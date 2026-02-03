/*
 * Copyright (C) 2023-2026 Ligero, Inc.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

#include <charconv>
#include <chrono>
#include <filesystem>
#include <fstream>
#include <sstream>
#include <unordered_set>

#include <transpiler.hpp>
#include <invoke.hpp>
#include <runtime.hpp>
#include <wgpu.hpp>

#include <util/portable_sample.hpp>
#include <util/boost/portable_binary_iarchive.hpp>
#include <zkp/common.hpp>
#include <zkp/finite_field_gmp.hpp>
#include <zkp/nonbatch_context.hpp>
#include <interpreter.hpp>

#include <boost/algorithm/hex.hpp>
#include <boost/iostreams/filtering_stream.hpp>
#include <boost/iostreams/filter/gzip.hpp>
#include <wabt/error-formatter.h>
#include <wabt/wast-parser.h>
#include <nlohmann/json.hpp>

using json = nlohmann::json;

using namespace wabt;
using namespace ligero;
using namespace ligero::vm;
namespace io = boost::iostreams;
namespace fs = std::filesystem;

using field_t = zkp::bn254_gmp;
using executor_t = webgpu_context;
using buffer_t = typename executor_t::buffer_type;

constexpr bool enable_RAM = false;

int main(int argc, const char *argv[]) {
    const std::string ligero_version_string =
        std::format("ligero-prover v{}.{}.{}+{}.{}",
                    LIGETRON_VERSION_MAJOR,
                    LIGETRON_VERSION_MINOR,
                    LIGETRON_VERSION_PATCH,
                    LIGETRON_GIT_BRANCH,
                    LIGETRON_GIT_COMMIT_HASH);
    std::cout << ligero_version_string << std::endl;
    
    std::vector<std::vector<u8>> input_args;
    std::string shader_path;
    std::string proof_name = "proof_data.gz";

    if (argc >= 3) {
        proof_name = argv[2];
    }

    if (argc < 2) {
        std::cerr << "Error: No JSON input provided" << std::endl;
        exit(EXIT_FAILURE);
    }
    
    std::string_view jstr = argv[1];
    json jconfig;

    try {
        jconfig = json::parse(jstr);
    }
    catch (json::exception& e) {
        std::cerr << e.what() << std::endl;
        exit(EXIT_FAILURE);
    }

    size_t k = params::default_row_size;
    size_t l = params::default_packing_size;
    size_t n = params::default_encoding_size;
    
    if (jconfig.contains("packing")) {
        uint64_t packing = jconfig["packing"];
        k = packing;
        l = k - params::sample_size;
        n = 4 * k;
    }
    std::cout << "packing: " << l << ", padding: " << k << ", encoding: " << n << std::endl;

    if (jconfig.contains("shader-path")) {
        shader_path = jconfig["shader-path"].template get<std::string>();
    }

    size_t gpu_threads = k;
    if (jconfig.contains("gpu-threads")) {
        gpu_threads = jconfig["gpu-threads"].template get<size_t>();
    }

    {
        const std::string arg0("Ligero");
        input_args.emplace_back((u8*)arg0.c_str(), (u8*)arg0.c_str() + arg0.size() + 1);
    }
    
    if (jconfig.contains("args")) {
        for (const auto& arg : jconfig["args"]) {
            std::cout << "args: " << arg.dump() << std::endl;
            
            if (arg.contains("i64")) {
                auto i = arg["i64"].template get<int64_t>();
                input_args.emplace_back((u8*)&i, (u8*)&i + sizeof(int64_t));
            }
            else if (arg.contains("str")) {
                auto str = arg["str"].template get<std::string>();
                input_args.emplace_back((u8*)str.c_str(), (u8*)str.c_str() + str.size() + 1);
            }
            else if (arg.contains("hex")) {
                std::vector<u8> hex_vec;
                auto hex_str = arg["hex"].template get<std::string>();
                
                // Remove leading "0x"
                if (hex_str.starts_with("0x")) {
                    hex_str = hex_str.substr(2);
                }
                
                if (hex_str.size() % 2 == 1) {
                    hex_str.insert(hex_str.begin(), '0');
                }
                boost::algorithm::unhex(hex_str.c_str(), std::back_inserter(hex_vec));
                input_args.emplace_back(std::move(hex_vec));
            }
            else {
                std::cerr << "Invalid args type: " << arg.dump() << std::endl;
                exit(-1);
            }
        }
    }

    std::unordered_set<int> indices_set;
    if (jconfig.contains("private-indices")) {
        indices_set = jconfig["private-indices"].template get<std::unordered_set<int>>();
    }

    fs::path program_name;
    if (jconfig.contains("program")) {
        program_name = jconfig["program"].template get<std::string>();
    }
    
    // Reading and parsing the wasm file
    // ------------------------------------------------------------
    std::unique_ptr<wabt::Module> wabt_module{ new wabt::Module{} };
    {
        std::vector<uint8_t> program_data;
        wabt::Result read_result = wabt::ReadFile(program_name.c_str(), &program_data);

        if (wabt::Failed(read_result)) {
            std::cerr << std::format("Error: Could not read from file \"{}\"",
                                     program_name.c_str())
                      << std::endl;
            exit(EXIT_FAILURE);
        }

        wabt::Features wabt_features;
        wabt::Result   parsing_result;
        wabt::Errors   parsing_errors;
        if (program_name.extension() == ".wat" || program_name.extension() == ".wast") {
            std::unique_ptr<wabt::WastLexer> lexer = wabt::WastLexer::CreateBufferLexer(
                program_name.c_str(),
                program_data.data(),
                program_data.size(),
                &parsing_errors);

            wabt::WastParseOptions parse_wast_options(wabt_features);
            parsing_result = wabt::ParseWatModule(lexer.get(),
                                                  &wabt_module,
                                                  &parsing_errors,
                                                  &parse_wast_options);
        }
        else {
            parsing_result = wabt::ReadBinaryIr(program_name.c_str(),
                                                program_data.data(),
                                                program_data.size(),
                                                wabt::ReadBinaryOptions{},
                                                &parsing_errors,
                                                wabt_module.get());
        }

        if (wabt::Failed(parsing_result)) {
            auto err_msg = wabt::FormatErrorsToString(parsing_errors,
                                                      wabt::Location::Type::Binary);
            std::cerr << std::format("wabt: {}", err_msg)
                      << std::format("Error: Failed to parse WASM module \"{}\"",
                                     program_name.c_str())
                      << std::endl;
            exit(EXIT_FAILURE);
        }
    }

    auto [omega_k, omega_2k, omega_4k] = field_t::generate_omegas(k, n);

    executor_t executor;
    executor.webgpu_init(gpu_threads, shader_path);
    executor.ntt_init(l, k, n,
                      field_t::modulus, field_t::barrett_factor,
                      omega_k, omega_2k, omega_4k);

    // ============================================================================
    // PROOF DESERIALIZATION
    // ============================================================================
    // The proof file (gzip compressed) contains:
    //   1. stage1_root    - 32-byte SHA256 Merkle root committed by prover
    //   2. sample_seed    - 32-byte seed for generating random sample indices
    //   3. encoded_code_limbs   - Code polynomial in NTT form (n × 8 u32 limbs)
    //   4. encoded_linear_limbs - Linear polynomial in NTT form (n × 8 u32 limbs)
    //   5. encoded_quad_limbs   - Quadratic polynomial in NTT form (n × 8 u32 limbs)
    //   6. decommit       - Merkle decommitment (sibling hashes for sampled leaves)
    //
    // Field elements are stored as 8 × u32 limbs (256 bits) in little-endian order.
    // The polynomials are in evaluation form (NTT'd), not coefficient form.
    // ============================================================================

    params::hasher::digest stage1_root;   // Prover's committed Merkle root
    params::hasher::digest sample_seed;   // Random seed for sampling (Fiat-Shamir)
    std::vector<uint32_t> encoded_code_limbs, encoded_linear_limbs, encoded_quad_limbs;
    zkp::merkle_tree<params::hasher>::decommitment decommit;  // Sibling hashes

    std::stringstream compressed_proof;
    io::filtering_istream proof_stream;
    std::unique_ptr<portable_binary_iarchive> archive_ptr;
    try {
        std::ifstream proof_file(proof_name, std::ios::in | std::ios::binary);

        if (!proof_file) {
            std::cerr << std::format("Error: Could not read from file \"{}\"", proof_name)
                      << std::endl;
            exit(EXIT_FAILURE);
        }

        compressed_proof << proof_file.rdbuf();
        proof_file.close();

        proof_stream.push(io::gzip_decompressor());
        proof_stream.push(compressed_proof);

        // Deserialize in order (Boost binary archive)
        archive_ptr = std::make_unique<portable_binary_iarchive>(proof_stream);
        *archive_ptr >> stage1_root           // 32 bytes
                     >> sample_seed           // 32 bytes
                     >> encoded_code_limbs    // n * 8 u32s
                     >> encoded_linear_limbs  // n * 8 u32s
                     >> encoded_quad_limbs    // n * 8 u32s
                     >> decommit;             // Merkle sibling hashes
        // Note: host_samplings is read by the verifier context from the archive
    }
    catch (const boost::archive::archive_exception& ex) {
        switch (ex.code) {
            case boost::archive::archive_exception::unsupported_version:
                std::cerr
                    << "Error: boost.archive: " << ex.what() << std::endl
                    << "It seems the proof was created with a newer version of Boost.Archive. \n"
                    << "Please update your Boost version to latest, or ask the file creator to use an older version." << std::endl;
                break;
            default:
                std::cerr << "Error: boost.archive: " << ex.what() << std::endl;
                break;
        }

        std::cerr << "Verification failed, exiting" << std::endl;
        exit(EXIT_FAILURE);
    }
    catch (const std::exception& ex) {
        std::cerr << "Error: " << ex.what() << std::endl;
        exit(EXIT_FAILURE);
    }

    std::cout << "=============== Start Verify ===============" << std::endl;

    auto vt = make_timer("Verify time");

    // Prepare random seed
    unsigned char seed[params::hasher::digest_size];
    std::copy(stage1_root.begin(), stage1_root.end(), seed);

    // Re-generate sample indexes
    zkp::hash_random_engine<params::hasher> engine(sample_seed);
    std::vector<size_t> indexes(n), sample_index;
    std::iota(indexes.begin(), indexes.end(), 0);
    portable_sample(indexes.begin(), indexes.end(),
                    std::back_inserter(sample_index),
                    params::sample_size,
                    engine);
    std::sort(sample_index.begin(), sample_index.end());
    
    auto vctx = std::make_unique<
        zkp::nonbatch_verifier_context<field_t,
                                       executor_t,
                                       zkp::verifier_random_policy,
                                       params::hasher,
                                       portable_binary_iarchive>>(executor,
                                                                  sample_index,
                                                                  *archive_ptr);
    vctx-> init_witness_random(seed, params::any_iv);

    try {
        run_program(*wabt_module, *vctx, input_args, indices_set);

        if (proof_stream.peek() != EOF) {
            std::cerr << "Error: proof size is bigger than it should be" << std::endl;
            std::cerr << "Verification failed, exiting" << std::endl;
            exit(EXIT_FAILURE);
        }
    }
    catch (const std::exception& e) {
        std::cout << "Error: " << e.what() << std::endl;
        std::cerr << "Verification failed, exiting" << std::endl;
        exit(EXIT_FAILURE);
    }

    vt.stop();

    auto leaf_digests = vctx->flush_digests();
    auto vs1_root = zkp::merkle_tree<params::hasher>::recommit(leaf_digests, decommit);

    // ============================================================================
    // STEP 3: Extract Verifier-Computed Values (from WASM execution)
    // ============================================================================
    // The verifier context (vctx) accumulated values while executing WASM:
    // - linear_sums: Running sums for linear constraint verification
    // - code/linear/quad buffers: Polynomial evaluations at sampled indices
    //
    // These are the "verifier's view" - computed by re-executing the program.
    // They will be compared against the prover's claimed values.
    // ----------------------------------------------------------------------------
    auto linear_sums = vctx->linear_sums();
    buffer_t vcode_buffer   = vctx->code();      // Verifier's code polynomial at sample points
    buffer_t vlinear_buffer = vctx->linear();    // Verifier's linear polynomial at sample points
    buffer_t vquad_buffer   = vctx->quadratic(); // Verifier's quadratic polynomial at sample points

    // Convert GPU buffers to CPU vectors of field elements (size = sample_size)
    mpz_vector vsample_code, vsample_linear, vsample_quad;

    auto vsample_code_limbs = executor.template copy_to_host<uint32_t>(vcode_buffer);
    vsample_code.import_limbs(vsample_code_limbs.data(),
                              vsample_code_limbs.size(),
                              sizeof(uint32_t),
                              field_t::num_u32_limbs);  // 8 limbs per BN254 element

    auto vsample_linear_limbs = executor.template copy_to_host<uint32_t>(vlinear_buffer);
    vsample_linear.import_limbs(vsample_linear_limbs.data(),
                                vsample_linear_limbs.size(),
                                sizeof(uint32_t),
                                field_t::num_u32_limbs);

    auto vsample_quad_limbs = executor.template copy_to_host<uint32_t>(vquad_buffer);
    vsample_quad.import_limbs(vsample_quad_limbs.data(),
                              vsample_quad_limbs.size(),
                              sizeof(uint32_t),
                              field_t::num_u32_limbs);

    // ============================================================================
    // STEP 4: Decode Prover's Encoded Polynomials via NTT Pipeline
    // ============================================================================
    // The prover sent polynomials in NTT (evaluation) form over n points.
    // We decode them using: INTT(n) -> fold(k) -> NTT(k)
    //
    // This transforms from n-point evaluations to k-point evaluations of the
    // underlying degree < k polynomial. The result is still in evaluation form,
    // NOT coefficient form.
    //
    // For valid RS encoding, positions [k..n] should be zero after decode.
    // ----------------------------------------------------------------------------

    // Allocate GPU buffers for prover's encoded polynomials (size = n elements)
    buffer_t device_code   = executor.make_codeword_buffer();
    buffer_t device_linear = executor.make_codeword_buffer();
    buffer_t device_quad   = executor.make_codeword_buffer();

    // Upload prover's encoded limbs from proof to GPU
    // Each buffer has n * 8 u32 limbs = n BN254 field elements
    executor.write_buffer(device_code,   encoded_code_limbs.data(),   encoded_code_limbs.size());
    executor.write_buffer(device_linear, encoded_linear_limbs.data(), encoded_linear_limbs.size());
    executor.write_buffer(device_quad,   encoded_quad_limbs.data(),   encoded_quad_limbs.size());

    // Bind NTT pipeline (sets up twiddle factors, etc.)
    auto bind_ntt_pc = executor.bind_ntt(device_code);
    auto bind_ntt_pl = executor.bind_ntt(device_linear);
    auto bind_ntt_pq = executor.bind_ntt(device_quad);

    // Decode: INTT(n) -> fold(k) -> NTT(k)
    // The result is k evaluations of the underlying polynomial.
    // After this: device_code[0..k] = decoded evaluations, device_code[k..n] should be ~0
    executor.decode_ntt_device(bind_ntt_pc);
    executor.decode_ntt_device(bind_ntt_pl);
    executor.decode_ntt_device(bind_ntt_pq);

    // Copy decoded polynomials back to CPU
    mpz_vector prover_code, prover_linear, prover_quad;

    {
        auto limbs = executor.template copy_to_host<uint32_t>(device_code);
        prover_code.import_limbs(limbs.data(),
                                 limbs.size(),
                                 sizeof(uint32_t),
                                 field_t::num_u32_limbs);
        // prover_code has n elements; we'll check prover_code[k..n] == 0 for valid RS encoding
    }
    {
        auto limbs = executor.template copy_to_host<uint32_t>(device_linear);
        prover_linear.import_limbs(limbs.data(),
                                   limbs.size(),
                                   sizeof(uint32_t),
                                   field_t::num_u32_limbs);
        prover_linear.resize(l);  // Only first l evaluations are meaningful
    }
    {
        auto limbs = executor.template copy_to_host<uint32_t>(device_quad);
        prover_quad.import_limbs(limbs.data(),
                                 limbs.size(),
                                 sizeof(uint32_t),
                                 field_t::num_u32_limbs);
        prover_quad.resize(l);    // Only first l evaluations are meaningful
    }

    // ============================================================================
    // STEP 5: Prepare Prover's Original Encoded Polynomials (for equality check)
    // ============================================================================
    // We also need the original encoded (NTT) form to compare against verifier's
    // sampled values. These are NOT decoded - they stay in evaluation form.
    // ----------------------------------------------------------------------------
    mpz_vector prover_encoded_codes, prover_encoded_linears, prover_encoded_quads;
    prover_encoded_codes.import_limbs(encoded_code_limbs.data(),
                                      encoded_code_limbs.size(),
                                      sizeof(uint32_t),
                                      field_t::num_u32_limbs);
    prover_encoded_linears.import_limbs(encoded_linear_limbs.data(),
                                        encoded_linear_limbs.size(),
                                        sizeof(uint32_t),
                                        field_t::num_u32_limbs);
    prover_encoded_quads.import_limbs(encoded_quad_limbs.data(),
                                      encoded_quad_limbs.size(),
                                      sizeof(uint32_t),
                                      field_t::num_u32_limbs);

    // ============================================================================
    // STEP 6: Verification Checks
    // ============================================================================
    std::cout << std::boolalpha;

    // CHECK 1: Merkle root - verifier's reconstructed root must match prover's
    bool valid_merkle = stage1_root == vs1_root;

    // CHECK 2: Code test - polynomial degree must be < k
    // After decode, positions [k..n] should all be zero (valid 4x Reed-Solomon encoding)
    bool valid_code   = std::all_of(prover_code.begin() + k, prover_code.end(),
                                  [](const auto& x) { return x == 0; });

    // CHECK 3: Linear test - verify Ax = b constraint satisfaction
    // Uses accumulated linear_sums from WASM execution
    bool valid_linear = zkp::validate_sum<field_t>(prover_linear, linear_sums);

    // CHECK 4: Quadratic test - all l coefficients must be zero
    // This checks the quadratic constraint Uz = 0
    bool valid_quad   = zkp::validate(prover_quad);

    std::cout << std::endl;
    std::cout << "Prover root  : ";
    zkp::show_hash(stage1_root);
    std::cout << "Verifier root: ";
    zkp::show_hash(vs1_root);
    std::cout << "Validating Merkle Tree Root:         "
              << valid_merkle   << std::endl;
    std::cout << "Validating Encoding Correctness:     "
              << valid_code   << std::endl;
    std::cout << "Validating Linear Constraints:       ";
    std::cout << valid_linear << " " << std::endl;
    std::cout << "Validating Quadratic Constraints:    ";
    std::cout << valid_quad << " " << std::endl;

    // CHECK 5: Column equality - prover's encoded values at sample indices
    // must match verifier's computed values at those same indices
    // This ensures the prover used the correct polynomial, not a different one
    // that happens to pass the degree/constraint tests
    bool code_equal = true, linear_equal = true, quad_equal = true;
    for (size_t i = 0; i < params::sample_size; i++) {
        // prover_encoded_*[sample_index[i]] is from the proof
        // vsample_*[i] is what the verifier computed by re-running WASM
        code_equal   &= prover_encoded_codes[sample_index[i]]   == vsample_code[i];
        linear_equal &= prover_encoded_linears[sample_index[i]] == vsample_linear[i];
        quad_equal   &= prover_encoded_quads[sample_index[i]]   == vsample_quad[i];
    }

    // FINAL: All checks must pass
    bool verify_result = valid_merkle &&
        valid_code && valid_linear && valid_quad &&
        code_equal && linear_equal && quad_equal;

    std::cout << "Validating Encoding Equality:        " << code_equal   << std::endl
              << "Validating Linear Equality:          " << linear_equal << std::endl
              << "Validating Quadratic Equality:       " << quad_equal   << std::endl
              << "-----------------------------------------" << std::endl
              << "Final Verify Result:                 " << verify_result << std::endl;
    
    // Dump golden file if requested (for Rust verifier testing)
    if (jconfig.contains("dump-golden")) {
        std::string golden_path = jconfig["dump-golden"].template get<std::string>();

        json golden;
        golden["proof_file"] = proof_name;
        golden["config"]["packing"] = l;
        golden["config"]["n"] = n;
        golden["config"]["k"] = k;
        golden["config"]["sample_size"] = params::sample_size;

        // Intermediate values (hex encoded)
        golden["intermediate_values"]["stage1_root"] = boost::algorithm::hex(
            std::string(stage1_root.begin(), stage1_root.end()));
        golden["intermediate_values"]["sample_seed"] = boost::algorithm::hex(
            std::string(sample_seed.begin(), sample_seed.end()));
        golden["intermediate_values"]["sample_indices"] = sample_index;
        golden["intermediate_values"]["vs1_root"] = boost::algorithm::hex(
            std::string(vs1_root.begin(), vs1_root.end()));

        // Leaf digests (hex encoded, one per sampled column)
        std::vector<std::string> leaf_digests_hex;
        for (const auto& digest : leaf_digests) {
            leaf_digests_hex.push_back(boost::algorithm::hex(
                std::string(reinterpret_cast<const char*>(digest.data), 32)));
        }
        golden["intermediate_values"]["leaf_digests"] = leaf_digests_hex;

        // Decoded polynomial evaluations (for NTT comparison)
        // NOTE: These are AFTER the full decode pipeline (INTT(n) → fold → NTT(k))
        // First 10 decoded evaluations of code polynomial (hex, big-endian)
        std::vector<std::string> decoded_code_first_10;
        for (size_t i = 0; i < std::min(size_t(10), prover_code.size()); i++) {
            decoded_code_first_10.push_back(prover_code[i].get_str(16));
        }
        golden["intermediate_values"]["decoded_code_first_10"] = decoded_code_first_10;

        // Also dump raw encoded values (before decode) for simple INTT comparison
        // First 10 encoded code values
        std::vector<std::string> encoded_code_first_10;
        for (size_t i = 0; i < std::min(size_t(10), prover_encoded_codes.size()); i++) {
            encoded_code_first_10.push_back(prover_encoded_codes[i].get_str(16));
        }
        golden["intermediate_values"]["encoded_code_first_10"] = encoded_code_first_10;

        // Decoded values around k boundary (k-5 to k+5) to verify degree check
        std::vector<std::string> decoded_code_around_k;
        for (size_t i = (k > 5 ? k - 5 : 0); i < std::min(k + 5, prover_code.size()); i++) {
            decoded_code_around_k.push_back(prover_code[i].get_str(16));
        }
        golden["intermediate_values"]["decoded_code_around_k"] = decoded_code_around_k;
        golden["intermediate_values"]["decoded_code_around_k_start_idx"] = (k > 5 ? k - 5 : 0);

        // First 10 decoded quad evaluations (should all be 0 for valid proof)
        std::vector<std::string> decoded_quad_first_10;
        for (size_t i = 0; i < std::min(size_t(10), prover_quad.size()); i++) {
            decoded_quad_first_10.push_back(prover_quad[i].get_str(16));
        }
        golden["intermediate_values"]["decoded_quad_first_10"] = decoded_quad_first_10;

        // =======================================================================
        // Extended NTT Pipeline Data (for isolated Rust testing)
        // =======================================================================

        // All encoded code values (input to decode pipeline)
        std::vector<std::string> encoded_code_all;
        for (size_t i = 0; i < prover_encoded_codes.size(); i++) {
            encoded_code_all.push_back(prover_encoded_codes[i].get_str(16));
        }
        golden["ntt_pipeline"]["encoded_code_all"] = encoded_code_all;

        // All decoded code values (output from decode pipeline)
        std::vector<std::string> decoded_code_all;
        for (size_t i = 0; i < prover_code.size(); i++) {
            decoded_code_all.push_back(prover_code[i].get_str(16));
        }
        golden["ntt_pipeline"]["decoded_code_all"] = decoded_code_all;

        // Parameters for the decode pipeline
        golden["ntt_pipeline"]["n"] = n;
        golden["ntt_pipeline"]["k"] = k;

        // Host samplings (sampled column values from proof)
        const auto& samplings = vctx->host_samplings();
        golden["host_samplings"]["limbs"] = samplings;
        golden["host_samplings"]["num_u32"] = samplings.size();
        golden["host_samplings"]["num_field_elements"] = samplings.size() / 8;
        golden["host_samplings"]["num_rows"] = (samplings.size() / 8) / params::sample_size;

        // Verification results
        golden["results"]["valid_merkle"] = valid_merkle;
        golden["results"]["valid_code"] = valid_code;
        golden["results"]["valid_linear"] = valid_linear;
        golden["results"]["valid_quad"] = valid_quad;
        golden["results"]["code_equal"] = code_equal;
        golden["results"]["linear_equal"] = linear_equal;
        golden["results"]["quad_equal"] = quad_equal;
        golden["results"]["final_result"] = verify_result;

        std::ofstream(golden_path) << golden.dump(2);
        std::cout << "Golden file written to: " << golden_path << std::endl;
    }

    show_timer();

#if defined(__EMSCRIPTEN__)
    // Since wasm remains loaded in memory after the "main" invocation,
    // timers are not cleaned up before the next invocation,
    // therefore we need to do it manually.
    clear_timers();
#endif

    return !verify_result;
}

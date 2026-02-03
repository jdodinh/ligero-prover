//! mDL Verification Circuit
//!
//! Arguments:
//!     [1]: <hex> mDL response file in CBOR format (private)
//!     [2]: <hex> "Obscured" version of the 'Argument 1' where the private data segments are "zeroed-out"
//!     [3]: <string> UTC time of verification (ISO 8601 date/time string)
//!     [4]: <hex> Session transcript hex data for device signature verification
//!     [5 - onwards]: <hex> CBOR encodings of the desired
//!                  { "elementIdentifier": <identifier name>,  "elementValue": <identifier value> } structures,
//!                  whose value we want to verify,
//!                  each prepended with one byte containing the Digest ID
//!                  of that element in that mDL response file.
//!
//! Note: Currently only supports EdDSA with Poseidon2 hash over the Babyjubjub curve (custom COSE algorithm tag -21).

use ligetron::babyjubjub::JubjubPoint;
use ligetron::bn254fr::Bn254Fr;
use ligetron::eddsa::EddsaSignature;
use ligetron::poseidon2::Poseidon2Context;
use ligetron::sha2::sha2_256;
use ligetron::*;

const TIME_LENGTH: usize = 20; // ISO 8601 date/time string (UTC)

const EDDSA_POSEIDON2_CUSTOM_TAG: u8 = 0x34;

fn find_subarray_positions(main_array: &[u8], sub_array: &[u8]) -> Vec<usize> {
    let mut positions: Vec<usize> = Vec::new();
    let main_len = main_array.len();
    let sub_len = sub_array.len();

    if sub_len > main_len {
        println_str(b"Subarray not found!");
        assert_one(0);
        return positions;
    }

    for i in 0..=(main_len - sub_len) {
        let mut found = true;
        for j in 0..sub_len {
            if main_array[i + j] != sub_array[j] {
                found = false;
                break;
            }
        }

        if found {
            positions.push(i);
        }
    }

    if positions.is_empty() {
        println_str(b"Subarray not found!");
        assert_one(0);
    }

    positions
}

fn find_first_sub(main_array: &[u8], sub_array: &[u8]) -> Option<usize> {
    let positions = find_subarray_positions(main_array, sub_array);
    if positions.is_empty() {
        return None;
    }
    Some(positions[0])
}

struct DecodedNum {
    value: usize,
    length: usize,
}

// Returns struct containing decoded CBOR's value and number of bytes it occupies
fn decode_cbor_num(major_type: u8, cbor_data: &[u8]) -> DecodedNum {
    let data_type = (cbor_data[0] & 0xE0) >> 5; // top 3 bits
    let additional_info = cbor_data[0] & 0x1F; // low 5 bits
    let mut result = DecodedNum {
        value: 0,
        length: 0,
    };

    if data_type != major_type {
        println_str(b"Data is not of the expected major type!");
        assert_one(0);
        return result;
    }

    if additional_info <= 23 {
        // Small integer directly encoded
        result.value = additional_info as usize;
        result.length = 1;
    } else if additional_info == 24 {
        result.value = cbor_data[1] as usize;
        result.length = 2;
    } else if additional_info == 25 {
        let value = ((cbor_data[1] as usize) << 8) | (cbor_data[2] as usize);
        result.value = value;
        result.length = 3;
    } else if additional_info == 26 {
        let value = ((cbor_data[1] as usize) << 24)
            | ((cbor_data[2] as usize) << 16)
            | ((cbor_data[3] as usize) << 8)
            | (cbor_data[4] as usize);
        result.value = value;
        result.length = 5;
    } else {
        println_str(b"Unsupported additional info!");
        assert_one(0);
    }
    result
}

struct Digest {
    position: usize,
    id: usize,
    data_length: usize,
    hash_in_mso: usize,
}

struct CborField<'a> {
    data: &'a [u8],
}

fn oblivious_ustr_equal(str1: &[u8], str2: &[u8], char_num: usize) -> usize {
    let mut matches: usize = 1;

    for i in 0..char_num {
        matches = oblivious_if(str1[i] == str2[i], matches as i32, 0) as usize;
    }
    matches
}

fn oblivious_str_compare(str1: &[u8], str2: &[u8], char_num: usize) -> i32 {
    let mut result: i32 = 0;

    for i in 0..char_num {
        result = oblivious_if(result == 0, (str1[i] as i32) - (str2[i] as i32), result);
    }
    result
}

fn filter_positions(positions: &[usize], start: usize, end: usize) -> Vec<usize> {
    let mut filtered_positions: Vec<usize> = Vec::new();
    for &pos in positions {
        if pos < start || pos > end {
            filtered_positions.push(pos);
        }
    }
    filtered_positions
}

// Converts byte array to its hex string representation (returns array of 2 + length*2 bytes)
fn bytes_to_hex(mdl_response: &[u8], position: usize, length: usize) -> Vec<u8> {
    let mut result: Vec<u8> = Vec::with_capacity(2 + length * 2);
    result.push(b'0');
    result.push(b'x');

    for i in 0..length {
        let value = mdl_response[position + i];

        let msb = (value >> 4) & 0xF;
        let msb_is_letter = msb > 9;

        let lsb = value & 0xF;
        let lsb_is_letter = lsb > 9;

        let final_val_m = if msb_is_letter { msb + 87 } else { msb + 48 };
        let final_val_l = if lsb_is_letter { lsb + 87 } else { lsb + 48 };

        result.push(final_val_m);
        result.push(final_val_l);
    }
    result
}

/// Helper to create Bn254Fr from a hex string (returns the string and Bn254Fr)
fn bn254fr_from_hex_str(hex_str: &[u8]) -> Bn254Fr {
    // Convert Vec<u8> of ASCII bytes to a &str for Bn254Fr::from_str
    let s = std::str::from_utf8(hex_str).expect("Invalid UTF-8 in hex string");
    Bn254Fr::from_str(s)
}

const SIG_SIGNATURE_HEADER: [u8; 18] = [
    0x84,
    0x6A,
    0x53,
    0x69,
    0x67,
    0x6E,
    0x61,
    0x74,
    0x75,
    0x72,
    0x65,
    0x31,
    0x43,
    0xA1,
    0x01,
    EDDSA_POSEIDON2_CUSTOM_TAG,
    0x40,
    0x59,
];

#[derive(PartialEq)]
enum SignatureType {
    IssuerSignature,
    DeviceSignature,
}

// Unified EdDSA signature verification function
fn verify_eddsa_signature(
    mdl_response: &[u8],
    signature_pos: usize,
    public_key_x_pos: usize,
    public_key_y_pos: usize,
    message_data: &[u8],
    _sig_type: SignatureType,
) {
    // Extract public key
    let hex_str_key_x = bytes_to_hex(mdl_response, public_key_x_pos, 32);
    let hex_str_key_y = bytes_to_hex(mdl_response, public_key_y_pos, 32);

    let mut key = JubjubPoint::new(
        bn254fr_from_hex_str(&hex_str_key_x),
        bn254fr_from_hex_str(&hex_str_key_y),
    );

    // Extract signature (skip CBOR header and get R.x, R.y, s)
    // Skip the CBOR header (5860) and extract the actual signature bytes
    let hex_str_sig_x = bytes_to_hex(mdl_response, signature_pos + 2, 32);
    let hex_str_sig_y = bytes_to_hex(mdl_response, signature_pos + 2 + 32, 32);
    let hex_str_sig_s = bytes_to_hex(mdl_response, signature_pos + 2 + 64, 32);

    let mut signature = EddsaSignature::new(
        JubjubPoint::new(
            bn254fr_from_hex_str(&hex_str_sig_x),
            bn254fr_from_hex_str(&hex_str_sig_y),
        ),
        bn254fr_from_hex_str(&hex_str_sig_s),
    );

    // Calculate message hash using Poseidon2
    let mut ctx = Poseidon2Context::new();
    ctx.digest_init();
    ctx.digest_update_bytes(message_data);
    let msg_hash = ctx.digest_final();

    // Create challenge hash: H(R.x, R.y, pubKey.x, pubKey.y, msg_hash)
    let mut ctx = Poseidon2Context::new();
    ctx.digest_init();
    ctx.digest_update(&signature.r.x);
    ctx.digest_update(&signature.r.y);
    ctx.digest_update(&key.x);
    ctx.digest_update(&key.y);
    ctx.digest_update(&msg_hash);
    let mut challenge_hash = ctx.digest_final();

    // Verify EdDSA signature
    EddsaSignature::verify(&mut signature, &mut key, &mut challenge_hash);
}

// Device signature validation wrapper
fn validate_device_signature(
    mdl_response: &[u8],
    device_signature_pos: usize,
    device_key_x: usize,
    device_key_y: usize,
    session_transcript: &[u8],
) {
    verify_eddsa_signature(
        mdl_response,
        device_signature_pos,
        device_key_x,
        device_key_y,
        session_transcript,
        SignatureType::DeviceSignature,
    );
}

// Issuer signature validation wrapper
fn validate_issuer_signature(
    mdl_response: &[u8],
    mso_pos: usize,
    mso_length: usize,
    key_x: usize,
    key_y: usize,
    cose_signature: usize,
) {
    // Create proper CBOR length encoding for the MSO data
    let mut cbor_length_bytes: Vec<u8> = Vec::new();
    if mso_length <= 23 {
        cbor_length_bytes.push(0x40 + mso_length as u8);
    } else if mso_length <= 0xFF {
        cbor_length_bytes.push(0x58);
        cbor_length_bytes.push(mso_length as u8);
    } else if mso_length <= 0xFFFF {
        cbor_length_bytes.push(0x59);
        cbor_length_bytes.push(((mso_length >> 8) & 0xFF) as u8);
        cbor_length_bytes.push((mso_length & 0xFF) as u8);
    } else {
        cbor_length_bytes.push(0x5A);
        cbor_length_bytes.push(((mso_length >> 24) & 0xFF) as u8);
        cbor_length_bytes.push(((mso_length >> 16) & 0xFF) as u8);
        cbor_length_bytes.push(((mso_length >> 8) & 0xFF) as u8);
        cbor_length_bytes.push((mso_length & 0xFF) as u8);
    }

    // Build the message buffer for issuer signature verification
    let mut buffer: Vec<u8> = Vec::with_capacity(mso_length + 18 + cbor_length_bytes.len());
    buffer.extend_from_slice(&SIG_SIGNATURE_HEADER);
    buffer.extend_from_slice(&cbor_length_bytes);

    for i in 0..mso_length {
        buffer.push(mdl_response[mso_pos + i]);
    }

    // Use unified signature verification
    verify_eddsa_signature(
        mdl_response,
        cose_signature,
        key_x,
        key_y,
        &buffer,
        SignatureType::IssuerSignature,
    );
}

fn parse_and_validate_mdl_response(
    mdl_response: &[u8],
    mdl_response_obscured: &[u8],
    _mdl_response_len: usize,
    validation_time: &[u8],
    session_transcript: &[u8],
    cbor_fields: &[CborField],
) {
    // MSO data extraction
    let issuer_auth_position = find_first_sub(mdl_response_obscured, b"issuerAuth").unwrap();

    let issuer_sign_algorithm_tag = mdl_response_obscured[issuer_auth_position + 14];
    if issuer_sign_algorithm_tag != EDDSA_POSEIDON2_CUSTOM_TAG {
        println_str(b"Issuer signing algorithm is not EDDSA with Poseidon2!");
        println_str(b"Other signing algorithms are not supported!");
        assert_one(0);
        return;
    }

    let crt_key_pos = issuer_auth_position + 16;
    let crt_key_dec = decode_cbor_num(0, &mdl_response_obscured[crt_key_pos..]);
    let crt_data_tag_pos = crt_key_pos + crt_key_dec.length;
    let crt_data_tag_dec = decode_cbor_num(2, &mdl_response_obscured[crt_data_tag_pos..]);
    let cert_start_pos = crt_data_tag_pos + crt_data_tag_dec.length; // Start of actual certificate data

    let mso_tag_pos = crt_data_tag_pos + crt_data_tag_dec.length + crt_data_tag_dec.value;
    let mso_tag_dec = decode_cbor_num(2, &mdl_response_obscured[mso_tag_pos..]);
    let mso_length = mso_tag_dec.value;
    let mso_start_pos = mso_tag_pos + mso_tag_dec.length;
    let cose_signature = mso_start_pos + mso_length;
    let mso_end_pos = cose_signature - 1;

    let digest_algorithm_offset =
        find_first_sub(&mdl_response_obscured[mso_start_pos..], b"digestAlgorithm").unwrap();
    let digest_algorithm_pos = mso_start_pos + digest_algorithm_offset + 16; // 15 chars + 1 CBOR header for value
    let is_sha256 = oblivious_str_compare(
        &mdl_response_obscured[digest_algorithm_pos..],
        b"SHA-256",
        7,
    );
    if is_sha256 != 0 {
        println_str(b"Digest algorithm is not SHA-256!");
        println_str(b"Other hash digest algorithms beside SHA-256 are not supported!");
        assert_one(0);
        return;
    }

    let value_digests_offset = find_first_sub(
        &mdl_response_obscured[digest_algorithm_pos..],
        b"valueDigests",
    )
    .unwrap();
    let value_digests_pos = digest_algorithm_pos + value_digests_offset + 12;

    // Device key extraction and signature extraction
    let device_key_positions = find_subarray_positions(mdl_response_obscured, b"deviceKey");
    let mut device_key_start: usize = 0;
    for i in 0..device_key_positions.len() - 1 {
        if device_key_positions[i] + 15 == device_key_positions[i + 1] {
            // The first one is "deviceKeyInfo", second one is "deviceKey"
            device_key_start = device_key_positions[i + 1];
            break;
        }
    }
    if device_key_start == 0 {
        println_str(b"Device key not found!");
        assert_one(0);
        return;
    }

    // Extract issuer keys from certificate-relative positions
    let issuer_key_x_pos = cert_start_pos + 224;
    let issuer_key_y_pos = issuer_key_x_pos + 32;

    // Signature validation using issuer keys
    validate_issuer_signature(
        mdl_response,
        mso_start_pos,
        mso_length,
        issuer_key_x_pos,
        issuer_key_y_pos,
        cose_signature,
    );

    // Extract device keys
    let device_key_x = device_key_start + 17;
    let device_key_y = device_key_start + 52;

    // Get date positions
    let valid_from_pos = device_key_y + 87;
    let valid_until_pos = valid_from_pos + 35;

    assert_one(
        (oblivious_str_compare(
            validation_time,
            &mdl_response[valid_from_pos..],
            TIME_LENGTH,
        ) > 0) as i32,
    );
    assert_one(
        (oblivious_str_compare(
            &mdl_response[valid_until_pos..],
            validation_time,
            TIME_LENGTH,
        ) > 0) as i32,
    );

    // DeviceSignature extraction
    let device_signed_len: usize = 109;
    let potential_signed_pos = find_subarray_positions(mdl_response_obscured, b"deviceSigned");
    let device_signed_start_pos =
        filter_positions(&potential_signed_pos, mso_start_pos, mso_end_pos)[0];
    let _device_signed_end_pos = device_signed_start_pos + device_signed_len;

    let signature_pos = find_first_sub(
        &mdl_response_obscured
            [device_signed_start_pos..device_signed_start_pos + device_signed_len],
        b"deviceSignature",
    )
    .unwrap();

    let device_sign_algorithm_tag =
        mdl_response_obscured[device_signed_start_pos + signature_pos + 19];
    if device_sign_algorithm_tag != EDDSA_POSEIDON2_CUSTOM_TAG {
        println_str(b"Device signing algorithm is not EDDSA with Poseidon2!");
        println_str(b"Other signing algorithms are not supported!");
        assert_one(0);
        return;
    }

    // Calculate device signature position
    let device_signature_pos = device_signed_start_pos + signature_pos + 22; // Skip to signature data

    // Validate device signature
    validate_device_signature(
        mdl_response,
        device_signature_pos,
        device_key_x,
        device_key_y,
        session_transcript,
    );

    // Digest positions and ID extraction
    let digest_id_title_pos = find_subarray_positions(mdl_response_obscured, b"digestID");
    // Filter out positions to exclude eventual random matches with data within the MSO and device signature
    let digest_id_title_pos = filter_positions(&digest_id_title_pos, mso_start_pos, mso_end_pos);

    let digest_tag_base: [u8; 2] = [0xD8, 0x18];
    let mut digests: Vec<Digest> = Vec::new();

    for i in 0..digest_id_title_pos.len() {
        let dig_id = decode_cbor_num(0, &mdl_response_obscured[digest_id_title_pos[i] + 8..]).value;
        let mut digest_pos = digest_id_title_pos[i] - 7;
        let seek_start = find_first_sub(
            &mdl_response_obscured[digest_pos..digest_pos + 3],
            &digest_tag_base,
        )
        .unwrap_or(0);
        digest_pos += seek_start;
        let data_len = decode_cbor_num(2, &mdl_response_obscured[digest_pos + 2..]).value;
        digests.push(Digest {
            position: digest_pos,
            id: dig_id,
            data_length: data_len,
            hash_in_mso: 0,
        });
    }

    // Start of the hashes map
    let hash_map_start_pos = value_digests_pos + 19;
    let hashes_tag_dec = decode_cbor_num(5, &mdl_response_obscured[hash_map_start_pos..]);
    let num_of_hashes = hashes_tag_dec.value;
    let hashes_start_pos = hash_map_start_pos + hashes_tag_dec.length;
    let digest_len: usize = 35; // 32 bytes + 3 header bytes

    // Iteration through all the hashes and mapping with found digest based on the ID
    for i in 0..num_of_hashes {
        let dig_id_dec = decode_cbor_num(
            0,
            &mdl_response_obscured[hashes_start_pos + i * digest_len..],
        );
        let dig_id = dig_id_dec.value;

        // Find proper digest and assign position
        for j in 0..digests.len() {
            if dig_id == digests[j].id {
                digests[j].hash_in_mso = hashes_start_pos + 2 + dig_id_dec.length + i * digest_len;
            }
        }
    }

    if digests.len() > num_of_hashes {
        println_str(b"Insufficient hash digests present in the file!");
        assert_one(0);
        return;
    }

    let mut data_matched: usize = 0;

    // Date and data hashes validation
    for i in 0..digests.len() {
        let mut total_data_length = digests[i].data_length + 4;
        // Check if the digest data is stored in three bytes
        if digests[i].data_length > 255 {
            total_data_length += 1;
        }

        let digest_hash =
            sha2_256(&mdl_response[digests[i].position..digests[i].position + total_data_length]);

        for j in 0..32 {
            assert_one((digest_hash[j] == mdl_response[digests[i].hash_in_mso + j]) as i32);
        }

        // Parse CBOR structure dynamically to find elementIdentifier position
        // digests[i].position points to D8 18 tag before the actual data
        let mut random_len_pos = digests[i].position + 22;

        // Skip digestID value
        if digests[i].id > 23 {
            random_len_pos += 1; // If digestID is 2 bytes
        }

        // Parse random field length dynamically from CBOR header
        let random_dec = decode_cbor_num(2, &mdl_response_obscured[random_len_pos..]);

        let element_name_pos = random_len_pos + random_dec.value + 19;

        for k in 0..cbor_fields.len() {
            let cbor_field = &cbor_fields[k];
            data_matched += oblivious_ustr_equal(
                &mdl_response[element_name_pos..],
                cbor_field.data,
                cbor_field.data.len(),
            );
        }
    }
    assert_one(data_matched as i32);
}

fn main() {
    let args = get_args();

    if args.len() < 6 {
        print_str(b"Argument error: Minimum number of arguments is 5");
        print_str(b"Usage: mdl_verification <mdl_response> <mdl_obscured> <time> <session_transcript> <cbor_fields...>");
        assert_one(0);
        return;
    }

    let mdl_response = args.get_as_bytes(1);
    let mdl_response_len = mdl_response.len();

    let mdl_response_obscured = args.get_as_bytes(2);
    let mdl_response_obscured_len = mdl_response_obscured.len();

    let validation_time = args.get_as_bytes(3);
    let validation_time_len = validation_time.len() - 1;

    let session_transcript = args.get_as_bytes(4);

    if mdl_response_len != mdl_response_obscured_len {
        println_str(
            b"Argument error: original and obscured MDL response must be of the same length!",
        );
        assert_one(0);
        return;
    }

    if validation_time_len != TIME_LENGTH || validation_time[TIME_LENGTH - 1] != b'Z' {
        println_str(b"Argument error: Wrong time/date format!");
        println_str(b"Time/date valid UTC time (with Z at the end)");
        assert_one(0);
        return;
    }

    let mut cbor_fields: Vec<CborField> = Vec::new();

    // Parse and check if the input CBOR fields are valid
    for i in 5..args.len() {
        let input_arg = args.get_as_bytes(i);
        let mut input_valid = input_arg[0] == 0xA2;
        input_valid &= input_arg[1] == 0x71;
        input_valid &= oblivious_ustr_equal(&input_arg[2..], b"elementIdentifier", 17) != 0;
        if !input_valid {
            println_str(b"Invalid CBOR field format!");
            assert_one(0);
            return;
        }
        cbor_fields.push(CborField {
            data: &input_arg[19..],
        }); // A2 || 71 || "elementIdentifier" = 19 bytes
    }

    parse_and_validate_mdl_response(
        mdl_response,
        mdl_response_obscured,
        mdl_response_len,
        validation_time,
        session_transcript,
        &cbor_fields,
    );
}


// // SPDX-License-Identifier: MIT

// pragma solidity ^0.8.0;

// /// @title Groth16 verifier template.
// /// @author Remco Bloemen
// /// @notice Supports verifying Groth16 proofs. Proofs can be in uncompressed
// /// (256 bytes) and compressed (128 bytes) format. A view function is provided
// /// to compress proofs.
// /// @notice See <https://2π.com/23/bn254-compression> for further explanation.
// contract PicoVmVerifier {

//     /// Some of the provided public input values are larger than the field modulus.
//     /// @dev Public input elements are not automatically reduced, as this is can be
//     /// a dangerous source of bugs.
//     error PublicInputNotInField();

//     /// The proof is invalid.
//     /// @dev This can mean that provided Groth16 proof points are not on their
//     /// curves, that pairing equation fails, or that the proof is not for the
//     /// provided public input.
//     error ProofInvalid();

//     // Addresses of precompiles
//     uint256 constant PRECOMPILE_MODEXP = 0x05;
//     uint256 constant PRECOMPILE_ADD = 0x06;
//     uint256 constant PRECOMPILE_MUL = 0x07;
//     uint256 constant PRECOMPILE_VERIFY = 0x08;

//     // Base field Fp order P and scalar field Fr order R.
//     // For BN254 these are computed as follows:
//     //     t = 4965661367192848881
//     //     P = 36⋅t⁴ + 36⋅t³ + 24⋅t² + 6⋅t + 1
//     //     R = 36⋅t⁴ + 36⋅t³ + 18⋅t² + 6⋅t + 1
//     uint256 constant P = 0x30644e72e131a029b85045b68181585d97816a916871ca8d3c208c16d87cfd47;
//     uint256 constant R = 0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000001;

//     uint256 constant MOD_R = 21888242871839275222246405745257275088548364400416034343698204186575808495617;

//     // Extension field Fp2 = Fp[i] / (i² + 1)
//     // Note: This is the complex extension field of Fp with i² = -1.
//     //       Values in Fp2 are represented as a pair of Fp elements (a₀, a₁) as a₀ + a₁⋅i.
//     // Note: The order of Fp2 elements is *opposite* that of the pairing contract, which
//     //       expects Fp2 elements in order (a₁, a₀). This is also the order in which
//     //       Fp2 elements are encoded in the public interface as this became convention.

//     // Constants in Fp
//     uint256 constant FRACTION_1_2_FP = 0x183227397098d014dc2822db40c0ac2ecbc0b548b438e5469e10460b6c3e7ea4;
//     uint256 constant FRACTION_27_82_FP = 0x2b149d40ceb8aaae81be18991be06ac3b5b4c5e559dbefa33267e6dc24a138e5;
//     uint256 constant FRACTION_3_82_FP = 0x2fcd3ac2a640a154eb23960892a85a68f031ca0c8344b23a577dcf1052b9e775;

//     // Exponents for inversions and square roots mod P
//     uint256 constant EXP_INVERSE_FP = 0x30644E72E131A029B85045B68181585D97816A916871CA8D3C208C16D87CFD45; // P - 2
//     uint256 constant EXP_SQRT_FP = 0xC19139CB84C680A6E14116DA060561765E05AA45A1C72A34F082305B61F3F52; // (P + 1) / 4;

//     // Groth16 alpha point in G1
//     uint256 constant ALPHA_X = 12466228198076905105755224006657941756607146595405451844521605798619441810186;
//     uint256 constant ALPHA_Y = 712526918512645576757662298939053999678330128243705406497671619263939745683;

//     // Groth16 beta point in G2 in powers of i
//     uint256 constant BETA_NEG_X_0 = 6589920211034276817640035068772162875169727598061885290418958805757521971979;
//     uint256 constant BETA_NEG_X_1 = 1701602543074268815129479797234342500256198664497258750040345698416225495484;
//     uint256 constant BETA_NEG_Y_0 = 9448557525190474513499859702917863867900386099948914619901462228871260591093;
//     uint256 constant BETA_NEG_Y_1 = 18242790104733248789058223253607063491520441244078025584360103711304549332126;

//     // Groth16 gamma point in G2 in powers of i
//     uint256 constant GAMMA_NEG_X_0 = 9266985912677105162367602238857156399124101940416631159812429530232026723639;
//     uint256 constant GAMMA_NEG_X_1 = 416264787545004896914316101576248203526410298204069383126972511176729697167;
//     uint256 constant GAMMA_NEG_Y_0 = 19030014286083919785101956240924142418582358580649813287328481698607578063361;
//     uint256 constant GAMMA_NEG_Y_1 = 17939445426976051831298860833809014005751881181814616804600461932545511710011;

//     // Groth16 delta point in G2 in powers of i
//     uint256 constant DELTA_NEG_X_0 = 9767613062680257792381589551480595284222373546251239179556211039289362276360;
//     uint256 constant DELTA_NEG_X_1 = 12728827779819191063140738409741217900911144433821086809266035940424429927884;
//     uint256 constant DELTA_NEG_Y_0 = 8708807645050862981441678682823427215835696674090770752586859062354340925098;
//     uint256 constant DELTA_NEG_Y_1 = 18016736593822738769338858816329912902000256687704609669001855711414409608628;

//     // Constant and public input points
//     uint256 constant CONSTANT_X = 11793932734324542011554606884130354422705755750040097242690973437897781220368;
//     uint256 constant CONSTANT_Y = 10146558032849280321325663432830491261975892276435624932585581309612616444372;
//     uint256 constant PUB_0_X = 20122043583654772286552204715385049139596972312729000636839308334037540614874;
//     uint256 constant PUB_0_Y = 12242689062403580094572081399489710262392149444651111615246552738192155978011;
//     uint256 constant PUB_1_X = 1321665823041660276386381667954449607883797855517222263012369853806841662027;
//     uint256 constant PUB_1_Y = 7802275470936064835268396674492134994569532931123909424307470485519130033128;

//     /// Compute the public input linear combination.
//     /// @notice Reverts with PublicInputNotInField if the input is not in the field.
//     /// @notice Computes the multi-scalar-multiplication of the public input
//     /// elements and the verification key including the constant term.
//     /// @param input The public inputs. These are elements of the scalar field Fr.
//     /// @return x The X coordinate of the resulting G1 point.
//     /// @return y The Y coordinate of the resulting G1 point.
//     function publicInputMSM(uint256[2] calldata input)
//     internal view returns (uint256 x, uint256 y) {
//         // Note: The ECMUL precompile does not reject unreduced values, so we check this.
//         // Note: Unrolling this loop does not cost much extra in code-size, the bulk of the
//         //       code-size is in the PUB_ constants.
//         // ECMUL has input (x, y, scalar) and output (x', y').
//         // ECADD has input (x1, y1, x2, y2) and output (x', y').
//         // We call them such that ecmul output is already in the second point
//         // argument to ECADD so we can have a tight loop.
//         bool success = true;
//         assembly ("memory-safe") {
//             let f := mload(0x40)
//             let g := add(f, 0x40)
//             let s
//             mstore(f, CONSTANT_X)
//             mstore(add(f, 0x20), CONSTANT_Y)
//             mstore(g, PUB_0_X)
//             mstore(add(g, 0x20), PUB_0_Y)
//             s :=  calldataload(input)
//             mstore(add(g, 0x40), s)
//             success := and(success, lt(s, R))
//             success := and(success, staticcall(gas(), PRECOMPILE_MUL, g, 0x60, g, 0x40))
//             success := and(success, staticcall(gas(), PRECOMPILE_ADD, f, 0x80, f, 0x40))
//             mstore(g, PUB_1_X)
//             mstore(add(g, 0x20), PUB_1_Y)
//             s :=  calldataload(add(input, 32))
//             mstore(add(g, 0x40), s)
//             success := and(success, lt(s, R))
//             success := and(success, staticcall(gas(), PRECOMPILE_MUL, g, 0x60, g, 0x40))
//             success := and(success, staticcall(gas(), PRECOMPILE_ADD, f, 0x80, f, 0x40))
//             x := mload(f)
//             y := mload(add(f, 0x20))
//         }
//         if (!success) {
//             // Either Public input not in field, or verification key invalid.
//             // We assume the contract is correctly generated, so the verification key is valid.
//             revert PublicInputNotInField();
//         }
//     }

//     /// Verify an uncompressed Groth16 proof.
//     /// @notice Reverts with InvalidProof if the proof is invalid or
//     /// with PublicInputNotInField the public input is not reduced.
//     /// @notice There is no return value. If the function does not revert, the
//     /// proof was successfully verified.
//     /// @param proof the points (A, B, C) in EIP-197 format matching the output
//     /// of compressProof.
//     /// @param input the public input field elements in the scalar field Fr.
//     /// Elements must be reduced.
//     function verifyProof(
//         uint256[8] calldata proof,
//         uint256[2] calldata input
//     ) public view {
//         (uint256 x, uint256 y) = publicInputMSM(input);

//         // Note: The precompile expects the F2 coefficients in big-endian order.
//         // Note: The pairing precompile rejects unreduced values, so we won't check that here.

//         bool success;
//         assembly ("memory-safe") {
//             let f := mload(0x40) // Free memory pointer.

//         // Copy points (A, B, C) to memory. They are already in correct encoding.
//         // This is pairing e(A, B) and G1 of e(C, -δ).
//             calldatacopy(f, proof, 0x100)

//         // Complete e(C, -δ) and write e(α, -β), e(L_pub, -γ) to memory.
//         // OPT: This could be better done using a single codecopy, but
//         //      Solidity (unlike standalone Yul) doesn't provide a way to
//         //      to do this.
//             mstore(add(f, 0x100), DELTA_NEG_X_1)
//             mstore(add(f, 0x120), DELTA_NEG_X_0)
//             mstore(add(f, 0x140), DELTA_NEG_Y_1)
//             mstore(add(f, 0x160), DELTA_NEG_Y_0)
//             mstore(add(f, 0x180), ALPHA_X)
//             mstore(add(f, 0x1a0), ALPHA_Y)
//             mstore(add(f, 0x1c0), BETA_NEG_X_1)
//             mstore(add(f, 0x1e0), BETA_NEG_X_0)
//             mstore(add(f, 0x200), BETA_NEG_Y_1)
//             mstore(add(f, 0x220), BETA_NEG_Y_0)
//             mstore(add(f, 0x240), x)
//             mstore(add(f, 0x260), y)
//             mstore(add(f, 0x280), GAMMA_NEG_X_1)
//             mstore(add(f, 0x2a0), GAMMA_NEG_X_0)
//             mstore(add(f, 0x2c0), GAMMA_NEG_Y_1)
//             mstore(add(f, 0x2e0), GAMMA_NEG_Y_0)

//         // Check pairing equation.
//             success := staticcall(gas(), PRECOMPILE_VERIFY, f, 0x300, f, 0x20)
//         // Also check returned value (both are either 1 or 0).
//             success := and(success, mload(f))
//         }
//         if (!success) {
//             // Either proof or verification key invalid.
//             // We assume the contract is correctly generated, so the verification key is valid.
//             revert ProofInvalid();
//         }
//     }
// }



pragma solidity ^0.8.0;

/// @title Groth16 verifier template.
/// @author Remco Bloemen
/// @notice Supports verifying Groth16 proofs. Proofs can be in uncompressed
/// (256 bytes) and compressed (128 bytes) format. A view function is provided
/// to compress proofs.
/// @notice See <https://2π.com/23/bn254-compression> for further explanation.
contract PicoVmVerifier {
    
    /// Some of the provided public input values are larger than the field modulus.
    /// @dev Public input elements are not automatically reduced, as this is can be
    /// a dangerous source of bugs.
    error PublicInputNotInField();

    /// The proof is invalid.
    /// @dev This can mean that provided Groth16 proof points are not on their
    /// curves, that pairing equation fails, or that the proof is not for the
    /// provided public input.
    error ProofInvalid();

    // Addresses of precompiles
    uint256 constant PRECOMPILE_MODEXP = 0x05;
    uint256 constant PRECOMPILE_ADD = 0x06;
    uint256 constant PRECOMPILE_MUL = 0x07;
    uint256 constant PRECOMPILE_VERIFY = 0x08;

    // Base field Fp order P and scalar field Fr order R.
    // For BN254 these are computed as follows:
    //     t = 4965661367192848881
    //     P = 36⋅t⁴ + 36⋅t³ + 24⋅t² + 6⋅t + 1
    //     R = 36⋅t⁴ + 36⋅t³ + 18⋅t² + 6⋅t + 1
    uint256 constant P = 0x30644e72e131a029b85045b68181585d97816a916871ca8d3c208c16d87cfd47;
    uint256 constant R = 0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000001;

	uint256 constant MOD_R = 21888242871839275222246405745257275088548364400416034343698204186575808495617;

    // Extension field Fp2 = Fp[i] / (i² + 1)
    // Note: This is the complex extension field of Fp with i² = -1.
    //       Values in Fp2 are represented as a pair of Fp elements (a₀, a₁) as a₀ + a₁⋅i.
    // Note: The order of Fp2 elements is *opposite* that of the pairing contract, which
    //       expects Fp2 elements in order (a₁, a₀). This is also the order in which
    //       Fp2 elements are encoded in the public interface as this became convention.

    // Constants in Fp
    uint256 constant FRACTION_1_2_FP = 0x183227397098d014dc2822db40c0ac2ecbc0b548b438e5469e10460b6c3e7ea4;
    uint256 constant FRACTION_27_82_FP = 0x2b149d40ceb8aaae81be18991be06ac3b5b4c5e559dbefa33267e6dc24a138e5;
    uint256 constant FRACTION_3_82_FP = 0x2fcd3ac2a640a154eb23960892a85a68f031ca0c8344b23a577dcf1052b9e775;

    // Exponents for inversions and square roots mod P
    uint256 constant EXP_INVERSE_FP = 0x30644E72E131A029B85045B68181585D97816A916871CA8D3C208C16D87CFD45; // P - 2
    uint256 constant EXP_SQRT_FP = 0xC19139CB84C680A6E14116DA060561765E05AA45A1C72A34F082305B61F3F52; // (P + 1) / 4;

    // Groth16 alpha point in G1
    uint256 constant ALPHA_X = 14314501919518882090394717447484555264755445938318850570259943576280036560234;
    uint256 constant ALPHA_Y = 3464648138172536097502275058139617482973938302385152608868192314471767203155;

    // Groth16 beta point in G2 in powers of i
    uint256 constant BETA_NEG_X_0 = 6301614410365648236477659703049115586741400600403941213592519892358054277196;
    uint256 constant BETA_NEG_X_1 = 20494049465257480578881509379970270683346221260359401500486806666098665786693;
    uint256 constant BETA_NEG_Y_0 = 7215779474301472713107354522254721291137546473301694130937778650984830543535;
    uint256 constant BETA_NEG_Y_1 = 11170495905233158288958972374631192425415327066545957805692740293707916865201;

    // Groth16 gamma point in G2 in powers of i
    uint256 constant GAMMA_NEG_X_0 = 16926401939035435925207271079315543750710841879979608148855549260327049702240;
    uint256 constant GAMMA_NEG_X_1 = 12182659355901135751088565947172305911060559604964753298951922014799099783845;
    uint256 constant GAMMA_NEG_Y_0 = 9504191999511692283011365386228822714468509627829428108854996030132542865283;
    uint256 constant GAMMA_NEG_Y_1 = 10685481643380945799692608326769918793248842567825873124661643766522511566027;

    // Groth16 delta point in G2 in powers of i
    uint256 constant DELTA_NEG_X_0 = 17220218489531966389123765014206042250472886587372271298287857884613421903458;
    uint256 constant DELTA_NEG_X_1 = 14470386200191635451083734293688353663320530189331692606027505192342131063606;
    uint256 constant DELTA_NEG_Y_0 = 249835958416057937657369124782138597129793828997693278059346796413817511310;
    uint256 constant DELTA_NEG_Y_1 = 18094254045222117580061947800403358159886540587730323476529053710742162001573;

    // Constant and public input points
    uint256 constant CONSTANT_X = 11953768251568857193273708165557972905717457689782869500776346259767863732152;
    uint256 constant CONSTANT_Y = 13649671507047934875131816057557786958595462521164403518772735569698015717712;
    uint256 constant PUB_0_X = 3037865058338468401680287148002468974167719491054672101844829814538172650363;
    uint256 constant PUB_0_Y = 3703487383378547499635789315071922056360893634369825434737745045599658494301;
    uint256 constant PUB_1_X = 13115434031104130463691295015179304261415426999834719184149693734255459768704;
    uint256 constant PUB_1_Y = 15583566577159823169254430240314541646708396225929938108480529258730392886474;

    /// Negation in Fp.
    /// @notice Returns a number x such that a + x = 0 in Fp.
    /// @notice The input does not need to be reduced.
    /// @param a the base
    /// @return x the result
    function negate(uint256 a) internal pure returns (uint256 x) {
        unchecked {
            x = (P - (a % P)) % P; // Modulo is cheaper than branching
        }
    }

    /// Exponentiation in Fp.
    /// @notice Returns a number x such that a ^ e = x in Fp.
    /// @notice The input does not need to be reduced.
    /// @param a the base
    /// @param e the exponent
    /// @return x the result
    function exp(uint256 a, uint256 e) internal view returns (uint256 x) {
        bool success;
        assembly ("memory-safe") {
            let f := mload(0x40)
            mstore(f, 0x20)
            mstore(add(f, 0x20), 0x20)
            mstore(add(f, 0x40), 0x20)
            mstore(add(f, 0x60), a)
            mstore(add(f, 0x80), e)
            mstore(add(f, 0xa0), P)
            success := staticcall(gas(), PRECOMPILE_MODEXP, f, 0xc0, f, 0x20)
            x := mload(f)
        }
        if (!success) {
            // Exponentiation failed.
            // Should not happen.
            revert ProofInvalid();
        } 
    }

    /// Invertsion in Fp.
    /// @notice Returns a number x such that a * x = 1 in Fp.
    /// @notice The input does not need to be reduced.
    /// @notice Reverts with ProofInvalid() if the inverse does not exist
    /// @param a the input
    /// @return x the solution
    function invert_Fp(uint256 a) internal view returns (uint256 x) {
        x = exp(a, EXP_INVERSE_FP);
        if (mulmod(a, x, P) != 1) {
            // Inverse does not exist.
            // Can only happen during G2 point decompression.
            revert ProofInvalid();
        }
    }

    /// Square root in Fp.
    /// @notice Returns a number x such that x * x = a in Fp.
    /// @notice Will revert with InvalidProof() if the input is not a square
    /// or not reduced.
    /// @param a the square
    /// @return x the solution
    function sqrt_Fp(uint256 a) internal view returns (uint256 x) {
        x = exp(a, EXP_SQRT_FP);
        if (mulmod(x, x, P) != a) {
            // Square root does not exist or a is not reduced.
            // Happens when G1 point is not on curve.
            revert ProofInvalid();
        }
    }

    /// Square test in Fp.
    /// @notice Returns wheter a number x exists such that x * x = a in Fp.
    /// @notice Will revert with InvalidProof() if the input is not a square
    /// or not reduced.
    /// @param a the square
    /// @return x the solution
    function isSquare_Fp(uint256 a) internal view returns (bool) {
        uint256 x = exp(a, EXP_SQRT_FP);
        return mulmod(x, x, P) == a;
    }

    /// Square root in Fp2.
    /// @notice Fp2 is the complex extension Fp[i]/(i^2 + 1). The input is
    /// a0 + a1 ⋅ i and the result is x0 + x1 ⋅ i.
    /// @notice Will revert with InvalidProof() if
    ///   * the input is not a square,
    ///   * the hint is incorrect, or
    ///   * the input coefficents are not reduced.
    /// @param a0 The real part of the input.
    /// @param a1 The imaginary part of the input.
    /// @param hint A hint which of two possible signs to pick in the equation.
    /// @return x0 The real part of the square root.
    /// @return x1 The imaginary part of the square root.
    function sqrt_Fp2(uint256 a0, uint256 a1, bool hint) internal view returns (uint256 x0, uint256 x1) {
        // If this square root reverts there is no solution in Fp2.
        uint256 d = sqrt_Fp(addmod(mulmod(a0, a0, P), mulmod(a1, a1, P), P));
        if (hint) {
            d = negate(d);
        }
        // If this square root reverts there is no solution in Fp2.
        x0 = sqrt_Fp(mulmod(addmod(a0, d, P), FRACTION_1_2_FP, P));
        x1 = mulmod(a1, invert_Fp(mulmod(x0, 2, P)), P);

        // Check result to make sure we found a root.
        // Note: this also fails if a0 or a1 is not reduced.
        if (a0 != addmod(mulmod(x0, x0, P), negate(mulmod(x1, x1, P)), P)
        ||  a1 != mulmod(2, mulmod(x0, x1, P), P)) {
            revert ProofInvalid();
        }
    }

    /// Compress a G1 point.
    /// @notice Reverts with InvalidProof if the coordinates are not reduced
    /// or if the point is not on the curve.
    /// @notice The point at infinity is encoded as (0,0) and compressed to 0.
    /// @param x The X coordinate in Fp.
    /// @param y The Y coordinate in Fp.
    /// @return c The compresed point (x with one signal bit).
    function compress_g1(uint256 x, uint256 y) internal view returns (uint256 c) {
        if (x >= P || y >= P) {
            // G1 point not in field.
            revert ProofInvalid();
        }
        if (x == 0 && y == 0) {
            // Point at infinity
            return 0;
        }
        
        // Note: sqrt_Fp reverts if there is no solution, i.e. the x coordinate is invalid.
        uint256 y_pos = sqrt_Fp(addmod(mulmod(mulmod(x, x, P), x, P), 3, P));
        if (y == y_pos) {
            return (x << 1) | 0;
        } else if (y == negate(y_pos)) {
            return (x << 1) | 1;
        } else {
            // G1 point not on curve.
            revert ProofInvalid();
        }
    }

    /// Decompress a G1 point.
    /// @notice Reverts with InvalidProof if the input does not represent a valid point.
    /// @notice The point at infinity is encoded as (0,0) and compressed to 0.
    /// @param c The compresed point (x with one signal bit).
    /// @return x The X coordinate in Fp.
    /// @return y The Y coordinate in Fp.
    function decompress_g1(uint256 c) internal view returns (uint256 x, uint256 y) {
        // Note that X = 0 is not on the curve since 0³ + 3 = 3 is not a square.
        // so we can use it to represent the point at infinity.
        if (c == 0) {
            // Point at infinity as encoded in EIP196 and EIP197.
            return (0, 0);
        }
        bool negate_point = c & 1 == 1;
        x = c >> 1;
        if (x >= P) {
            // G1 x coordinate not in field.
            revert ProofInvalid();
        }

        // Note: (x³ + 3) is irreducible in Fp, so it can not be zero and therefore
        //       y can not be zero.
        // Note: sqrt_Fp reverts if there is no solution, i.e. the point is not on the curve.
        y = sqrt_Fp(addmod(mulmod(mulmod(x, x, P), x, P), 3, P));
        if (negate_point) {
            y = negate(y);
        }
    }

    /// Compress a G2 point.
    /// @notice Reverts with InvalidProof if the coefficients are not reduced
    /// or if the point is not on the curve.
    /// @notice The G2 curve is defined over the complex extension Fp[i]/(i^2 + 1)
    /// with coordinates (x0 + x1 ⋅ i, y0 + y1 ⋅ i). 
    /// @notice The point at infinity is encoded as (0,0,0,0) and compressed to (0,0).
    /// @param x0 The real part of the X coordinate.
    /// @param x1 The imaginary poart of the X coordinate.
    /// @param y0 The real part of the Y coordinate.
    /// @param y1 The imaginary part of the Y coordinate.
    /// @return c0 The first half of the compresed point (x0 with two signal bits).
    /// @return c1 The second half of the compressed point (x1 unmodified).
    function compress_g2(uint256 x0, uint256 x1, uint256 y0, uint256 y1)
    internal view returns (uint256 c0, uint256 c1) {
        if (x0 >= P || x1 >= P || y0 >= P || y1 >= P) {
            // G2 point not in field.
            revert ProofInvalid();
        }
        if ((x0 | x1 | y0 | y1) == 0) {
            // Point at infinity
            return (0, 0);
        }

        // Compute y^2
        // Note: shadowing variables and scoping to avoid stack-to-deep.
        uint256 y0_pos;
        uint256 y1_pos;
        {
            uint256 n3ab = mulmod(mulmod(x0, x1, P), P-3, P);
            uint256 a_3 = mulmod(mulmod(x0, x0, P), x0, P);
            uint256 b_3 = mulmod(mulmod(x1, x1, P), x1, P);
            y0_pos = addmod(FRACTION_27_82_FP, addmod(a_3, mulmod(n3ab, x1, P), P), P);
            y1_pos = negate(addmod(FRACTION_3_82_FP,  addmod(b_3, mulmod(n3ab, x0, P), P), P));
        }

        // Determine hint bit
        // If this sqrt fails the x coordinate is not on the curve.
        bool hint;
        {
            uint256 d = sqrt_Fp(addmod(mulmod(y0_pos, y0_pos, P), mulmod(y1_pos, y1_pos, P), P));
            hint = !isSquare_Fp(mulmod(addmod(y0_pos, d, P), FRACTION_1_2_FP, P));
        }

        // Recover y
        (y0_pos, y1_pos) = sqrt_Fp2(y0_pos, y1_pos, hint);
        if (y0 == y0_pos && y1 == y1_pos) {
            c0 = (x0 << 2) | (hint ? 2  : 0) | 0;
            c1 = x1;
        } else if (y0 == negate(y0_pos) && y1 == negate(y1_pos)) {
            c0 = (x0 << 2) | (hint ? 2  : 0) | 1;
            c1 = x1;
        } else {
            // G1 point not on curve.
            revert ProofInvalid();
        }
    }

    /// Decompress a G2 point.
    /// @notice Reverts with InvalidProof if the input does not represent a valid point.
    /// @notice The G2 curve is defined over the complex extension Fp[i]/(i^2 + 1)
    /// with coordinates (x0 + x1 ⋅ i, y0 + y1 ⋅ i). 
    /// @notice The point at infinity is encoded as (0,0,0,0) and compressed to (0,0).
    /// @param c0 The first half of the compresed point (x0 with two signal bits).
    /// @param c1 The second half of the compressed point (x1 unmodified).
    /// @return x0 The real part of the X coordinate.
    /// @return x1 The imaginary poart of the X coordinate.
    /// @return y0 The real part of the Y coordinate.
    /// @return y1 The imaginary part of the Y coordinate.
    function decompress_g2(uint256 c0, uint256 c1)
    internal view returns (uint256 x0, uint256 x1, uint256 y0, uint256 y1) {
        // Note that X = (0, 0) is not on the curve since 0³ + 3/(9 + i) is not a square.
        // so we can use it to represent the point at infinity.
        if (c0 == 0 && c1 == 0) {
            // Point at infinity as encoded in EIP197.
            return (0, 0, 0, 0);
        }
        bool negate_point = c0 & 1 == 1;
        bool hint = c0 & 2 == 2;
        x0 = c0 >> 2;
        x1 = c1;
        if (x0 >= P || x1 >= P) {
            // G2 x0 or x1 coefficient not in field.
            revert ProofInvalid();
        }

        uint256 n3ab = mulmod(mulmod(x0, x1, P), P-3, P);
        uint256 a_3 = mulmod(mulmod(x0, x0, P), x0, P);
        uint256 b_3 = mulmod(mulmod(x1, x1, P), x1, P);

        y0 = addmod(FRACTION_27_82_FP, addmod(a_3, mulmod(n3ab, x1, P), P), P);
        y1 = negate(addmod(FRACTION_3_82_FP,  addmod(b_3, mulmod(n3ab, x0, P), P), P));

        // Note: sqrt_Fp2 reverts if there is no solution, i.e. the point is not on the curve.
        // Note: (X³ + 3/(9 + i)) is irreducible in Fp2, so y can not be zero.
        //       But y0 or y1 may still independently be zero.
        (y0, y1) = sqrt_Fp2(y0, y1, hint);
        if (negate_point) {
            y0 = negate(y0);
            y1 = negate(y1);
        }
    }

    /// Compute the public input linear combination.
    /// @notice Reverts with PublicInputNotInField if the input is not in the field.
    /// @notice Computes the multi-scalar-multiplication of the public input
    /// elements and the verification key including the constant term.
    /// @param input The public inputs. These are elements of the scalar field Fr.
    /// @return x The X coordinate of the resulting G1 point.
    /// @return y The Y coordinate of the resulting G1 point.
    function publicInputMSM(uint256[2] calldata input)
    internal view returns (uint256 x, uint256 y) {
        // Note: The ECMUL precompile does not reject unreduced values, so we check this.
        // Note: Unrolling this loop does not cost much extra in code-size, the bulk of the
        //       code-size is in the PUB_ constants.
        // ECMUL has input (x, y, scalar) and output (x', y').
        // ECADD has input (x1, y1, x2, y2) and output (x', y').
        // We call them such that ecmul output is already in the second point
        // argument to ECADD so we can have a tight loop.
        bool success = true;
        assembly ("memory-safe") {
            let f := mload(0x40)
            let g := add(f, 0x40)
            let s
            mstore(f, CONSTANT_X)
            mstore(add(f, 0x20), CONSTANT_Y)
            mstore(g, PUB_0_X)
            mstore(add(g, 0x20), PUB_0_Y)
            s :=  calldataload(input)
            mstore(add(g, 0x40), s)
            success := and(success, lt(s, R))
            success := and(success, staticcall(gas(), PRECOMPILE_MUL, g, 0x60, g, 0x40))
            success := and(success, staticcall(gas(), PRECOMPILE_ADD, f, 0x80, f, 0x40))
            mstore(g, PUB_1_X)
            mstore(add(g, 0x20), PUB_1_Y)
            s :=  calldataload(add(input, 32))
            mstore(add(g, 0x40), s)
            success := and(success, lt(s, R))
            success := and(success, staticcall(gas(), PRECOMPILE_MUL, g, 0x60, g, 0x40))
            success := and(success, staticcall(gas(), PRECOMPILE_ADD, f, 0x80, f, 0x40))
            x := mload(f)
            y := mload(add(f, 0x20))
        }
        if (!success) {
            // Either Public input not in field, or verification key invalid.
            // We assume the contract is correctly generated, so the verification key is valid.
            revert PublicInputNotInField();
        }
    }

    /// Compress a proof.
    /// @notice Will revert with InvalidProof if the curve points are invalid,
    /// but does not verify the proof itself.
    /// @param proof The uncompressed Groth16 proof. Elements are in the same order as for
    /// verifyProof. I.e. Groth16 points (A, B, C) encoded as in EIP-197.
    /// @return compressed The compressed proof. Elements are in the same order as for
    /// verifyCompressedProof. I.e. points (A, B, C) in compressed format.
    function compressProof(uint256[8] calldata proof)
    public view returns (uint256[4] memory compressed) {
        compressed[0] = compress_g1(proof[0], proof[1]);
        (compressed[2], compressed[1]) = compress_g2(proof[3], proof[2], proof[5], proof[4]);
        compressed[3] = compress_g1(proof[6], proof[7]);
    }

    /// Verify a Groth16 proof with compressed points.
    /// @notice Reverts with InvalidProof if the proof is invalid or
    /// with PublicInputNotInField the public input is not reduced.
    /// @notice There is no return value. If the function does not revert, the
    /// proof was successfully verified.
    /// @param compressedProof the points (A, B, C) in compressed format
    /// matching the output of compressProof.
    /// @param input the public input field elements in the scalar field Fr.
    /// Elements must be reduced.
    function verifyCompressedProof(
        uint256[4] calldata compressedProof,
        uint256[2] calldata input
    ) public view {
        (uint256 Ax, uint256 Ay) = decompress_g1(compressedProof[0]);
        (uint256 Bx0, uint256 Bx1, uint256 By0, uint256 By1) = decompress_g2(
                compressedProof[2], compressedProof[1]);
        (uint256 Cx, uint256 Cy) = decompress_g1(compressedProof[3]);
        (uint256 Lx, uint256 Ly) = publicInputMSM(input);

        // Verify the pairing
        // Note: The precompile expects the F2 coefficients in big-endian order.
        // Note: The pairing precompile rejects unreduced values, so we won't check that here.
        uint256[24] memory pairings;
        // e(A, B)
        pairings[ 0] = Ax;
        pairings[ 1] = Ay;
        pairings[ 2] = Bx1;
        pairings[ 3] = Bx0;
        pairings[ 4] = By1;
        pairings[ 5] = By0;
        // e(C, -δ)
        pairings[ 6] = Cx;
        pairings[ 7] = Cy;
        pairings[ 8] = DELTA_NEG_X_1;
        pairings[ 9] = DELTA_NEG_X_0;
        pairings[10] = DELTA_NEG_Y_1;
        pairings[11] = DELTA_NEG_Y_0;
        // e(α, -β)
        pairings[12] = ALPHA_X;
        pairings[13] = ALPHA_Y;
        pairings[14] = BETA_NEG_X_1;
        pairings[15] = BETA_NEG_X_0;
        pairings[16] = BETA_NEG_Y_1;
        pairings[17] = BETA_NEG_Y_0;
        // e(L_pub, -γ)
        pairings[18] = Lx;
        pairings[19] = Ly;
        pairings[20] = GAMMA_NEG_X_1;
        pairings[21] = GAMMA_NEG_X_0;
        pairings[22] = GAMMA_NEG_Y_1;
        pairings[23] = GAMMA_NEG_Y_0;

        // Check pairing equation.
        bool success;
        uint256[1] memory output;
        assembly ("memory-safe") {
            success := staticcall(gas(), PRECOMPILE_VERIFY, pairings, 0x300, output, 0x20)
        }
        if (!success || output[0] != 1) {
            // Either proof or verification key invalid.
            // We assume the contract is correctly generated, so the verification key is valid.
            revert ProofInvalid();
        }
    }

    /// Verify an uncompressed Groth16 proof.
    /// @notice Reverts with InvalidProof if the proof is invalid or
    /// with PublicInputNotInField the public input is not reduced.
    /// @notice There is no return value. If the function does not revert, the
    /// proof was successfully verified.
    /// @param proof the points (A, B, C) in EIP-197 format matching the output
    /// of compressProof.
    /// @param input the public input field elements in the scalar field Fr.
    /// Elements must be reduced.
    function verifyProof(
        uint256[8] calldata proof,
        uint256[2] calldata input
    ) public view {
        (uint256 x, uint256 y) = publicInputMSM(input);

        // Note: The precompile expects the F2 coefficients in big-endian order.
        // Note: The pairing precompile rejects unreduced values, so we won't check that here.
        
        bool success;
        assembly ("memory-safe") {
            let f := mload(0x40) // Free memory pointer.

            // Copy points (A, B, C) to memory. They are already in correct encoding.
            // This is pairing e(A, B) and G1 of e(C, -δ).
            calldatacopy(f, proof, 0x100)

            // Complete e(C, -δ) and write e(α, -β), e(L_pub, -γ) to memory.
            // OPT: This could be better done using a single codecopy, but
            //      Solidity (unlike standalone Yul) doesn't provide a way to
            //      to do this.
            mstore(add(f, 0x100), DELTA_NEG_X_1)
            mstore(add(f, 0x120), DELTA_NEG_X_0)
            mstore(add(f, 0x140), DELTA_NEG_Y_1)
            mstore(add(f, 0x160), DELTA_NEG_Y_0)
            mstore(add(f, 0x180), ALPHA_X)
            mstore(add(f, 0x1a0), ALPHA_Y)
            mstore(add(f, 0x1c0), BETA_NEG_X_1)
            mstore(add(f, 0x1e0), BETA_NEG_X_0)
            mstore(add(f, 0x200), BETA_NEG_Y_1)
            mstore(add(f, 0x220), BETA_NEG_Y_0)
            mstore(add(f, 0x240), x)
            mstore(add(f, 0x260), y)
            mstore(add(f, 0x280), GAMMA_NEG_X_1)
            mstore(add(f, 0x2a0), GAMMA_NEG_X_0)
            mstore(add(f, 0x2c0), GAMMA_NEG_Y_1)
            mstore(add(f, 0x2e0), GAMMA_NEG_Y_0)

            // Check pairing equation.
            success := staticcall(gas(), PRECOMPILE_VERIFY, f, 0x300, f, 0x20)
            // Also check returned value (both are either 1 or 0).
            success := and(success, mload(f))
        }
        if (!success) {
            // Either proof or verification key invalid.
            // We assume the contract is correctly generated, so the verification key is valid.
            revert ProofInvalid();
        }
    }
}

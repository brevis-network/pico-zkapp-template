// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import {IGroth16Verifier, PicoVerifier} from "../src/PicoVerifier.sol";
import {Fibonacci} from "../src/Fibonacci.sol";
import {Verifier} from "./dev/Groth16Verifier.sol";

/// The cheatcodes this test uses, declared here rather than taken from forge-std so the project has
/// nothing to install.
interface Vm {
    function readFile(string calldata path) external view returns (string memory);
    function parseJsonBytes32(string calldata json, string calldata key) external pure returns (bytes32);
    function parseJsonBytes(string calldata json, string calldata key) external pure returns (bytes memory);
    function parseJsonBytes32Array(string calldata json, string calldata key) external pure returns (bytes32[] memory);
    function expectRevert(bytes4 revertData) external;
}

/// Fibonacci over PicoVerifier and the test-key Groth16 verifier in `test/dev`, against the proof
/// `cargo pico prove --evm` made with the same keys (`test_data/inputs.json`, as written).
contract FibonacciTest {
    Vm internal constant vm = Vm(address(uint160(uint256(keccak256("hevm cheat code")))));

    PicoVerifier internal picoVerifier;
    Fibonacci internal fibonacci;

    bytes32 internal programId;
    bytes internal publicValues;
    uint256[12] internal proof;

    function setUp() public {
        string memory json = vm.readFile("test_data/inputs.json");
        programId = vm.parseJsonBytes32(json, ".riscvVKey");
        publicValues = vm.parseJsonBytes(json, ".publicValues");
        bytes32[] memory words = vm.parseJsonBytes32Array(json, ".proof");
        require(words.length == 12, "a proof is twelve words");
        for (uint256 i = 0; i < 12; i++) {
            proof[i] = uint256(words[i]);
        }

        picoVerifier = new PicoVerifier(IGroth16Verifier(address(new Verifier())));
        // The program id pins the one program whose proofs this contract accepts.
        fibonacci = new Fibonacci(address(picoVerifier), programId);
    }

    function test_valid_proof_returns_fib_10() public view {
        (uint32 n, uint32 a, uint32 b) = fibonacci.verifyFibonacciProof(publicValues, proof);
        require(n == 10, "n should be 10");
        require(a == 55, "a, F(10), should be 55");
        require(b == 89, "b, F(11), should be 89");
    }

    function test_zero_proof_is_refused() public {
        uint256[12] memory zero;
        vm.expectRevert(Verifier.ProofInvalid.selector);
        fibonacci.verifyFibonacciProof(publicValues, zero);
    }

    function test_changed_public_values_are_refused() public {
        bytes memory changed = publicValues;
        changed[changed.length - 1] ^= 0x01;
        vm.expectRevert(Verifier.ProofInvalid.selector);
        fibonacci.verifyFibonacciProof(changed, proof);
    }

    function test_wrong_program_id_is_refused() public {
        Fibonacci other = new Fibonacci(address(picoVerifier), programId ^ bytes32(uint256(1)));
        vm.expectRevert(Verifier.ProofInvalid.selector);
        other.verifyFibonacciProof(publicValues, proof);
    }
}

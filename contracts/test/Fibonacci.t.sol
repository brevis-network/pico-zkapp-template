// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import "forge-std/Test.sol";

import {PicoVerifier} from "../src/PicoVerifier.sol";
import {Fibonacci} from "../src/Fibonacci.sol";

contract FibonacciTest is Test {
    PicoVerifier public picoVerifier;
    Fibonacci public fibonacci;

    // Data required by Pico Proof Verification.
    bytes32 public fibonacciKey;
    uint256[8] public proof;
    bytes public publicValues;

    function setUp() public {
        // Read and parse the input data from the JSON file
        // The JSON file is produced by running the command: `cargo pico prove --evm --output`
        string memory filePath = "./test_data/input.json";
        string memory jsonContent = vm.readFile(filePath);

        fibonacciKey = abi.decode(
            vm.parseJson(jsonContent, ".riscvVKey"),
            (bytes32)
        );
        publicValues = abi.decode(
            vm.parseJson(jsonContent, ".publicValues"),
            (bytes)
        );
        bytes32[] memory proofBytes32 = abi.decode(
            vm.parseJson(jsonContent, ".proof"),
            (bytes32[])
        );

        for (uint256 i = 0; i < proofBytes32.length; i++) {
            proof[i] = uint256(proofBytes32[i]);
        }

        // Deploy contracts
        picoVerifier = new PicoVerifier();
        // The `fibonacciKey` serves as an identifier to distinguish between different zkApps.
        fibonacci = new Fibonacci(address(picoVerifier), fibonacciKey);
    }

    // Test that the Fibonacci proof verification passes with real proof data
    function testValidFibonacciProof() public view {
        (uint32 n, uint32 a, uint32 b) = fibonacci.verifyFibonacciProof(
            publicValues,
            proof
        );

        assertEq(n, 10, "The Fibonacci index (n) should be 10.");
        assertEq(a, 55, "The Fibonacci term n-1 (a) should be 55.");
        assertEq(b, 89, "The Fibonacci term n (b) should be 89.");
    }

    // This test is expected to fail (revert) when providing invalid proof
    function testInvalidFibonacciProof() public {
        vm.expectRevert();
        // Set up an invalid proof
        uint256[8] memory invalidProof = [uint256(0), 0, 0, 0, 0, 0, 0, 0];

        fibonacci.verifyFibonacciProof(publicValues, invalidProof);
    }
}

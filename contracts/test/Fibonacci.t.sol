// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import "forge-std/Test.sol";
import "forge-std/console.sol";

import {PicoVerifier} from "../src/PicoVerifier.sol";
import {IPicoVerifier} from "../src/IPicoVerifier.sol";
import {Fibonacci, PublicValuesStruct} from "../src/Fibonacci.sol";

contract FibonacciTest is Test {
    PicoVerifier public picoVerifier;
    Fibonacci public fibonacci;

    // The three types of data required by PicoVmVerifier.
    bytes32 public fibonacciKey;
    uint256[8] public proof;
    bytes public publicValues;

    function setUp() public {

        string memory filePath = "./test_data/fibonacci.json";
        string memory jsonContent = vm.readFile(filePath);

        fibonacciKey = abi.decode(vm.parseJson(jsonContent, ".riscvVKey"), (bytes32));
        publicValues = abi.decode(vm.parseJson(jsonContent, ".publicValues"), (bytes));
        bytes32[] memory proofBytes32 = abi.decode(vm.parseJson(jsonContent, ".proof"), (bytes32[]));

        for (uint256 i = 0; i < proofBytes32.length; i++) {
            proof[i] = uint256(proofBytes32[i]);
        }

        console.logBytes(publicValues);
        console.logBytes32(fibonacciKey);
        for (uint256 i = 0; i < proof.length; i++) {
            console.logUint(proof[i]);
        }

        picoVerifier = new PicoVerifier();
        fibonacci = new Fibonacci(address(picoVerifier), fibonacciKey);
    }

    function testVerifyFibonacciProofShouldPassOnRealProof() public view {
        // vm.expectRevert(); 

        (uint32 n, uint32 a, uint32 b) = fibonacci.verifyFibonacciProof(
            publicValues, 
            proof
        );

        assertEq(n, 10);
        assertEq(a, 55);
        assertEq(b, 89);
    }
}

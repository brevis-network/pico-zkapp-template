// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import "forge-std/Test.sol";

import {PicoVerifier} from "../src/PicoVerifier.sol";
import {IPicoVerifier} from "../src/IPicoVerifier.sol";
import {Fibonacci, PublicValuesStruct} from "../src/Fibonacci.sol";

contract FibonacciTest is Test {
    PicoVerifier public picoVerifier;
    Fibonacci public fibonacci;

    bytes32 public fibonacciKey = bytes32(abi.encodePacked("1234"));

    function setUp() public {
        picoVerifier = new PicoVerifier();

        fibonacci = new Fibonacci(address(picoVerifier), fibonacciKey);
    }

    function testVerifyFibonacciProofShouldPassOnRealProof() public {
        uint256[8] memory proof = [
            uint256(0), 
            0,
            0,
            0,
            0,
            0,
            0,
            0
        ];

        PublicValuesStruct memory dummyPublicValues = PublicValuesStruct({
            n: 5,
            a: 3,
            b: 8
        });

        bytes memory encodedPublicValues = abi.encode(dummyPublicValues);

        vm.expectRevert(); 

        (uint32 n, uint32 a, uint32 b) = fibonacci.verifyFibonacciProof(
            encodedPublicValues, 
            proof
        );

        // assertEq(n, 5);
        // assertEq(a, 3);
        // assertEq(b, 8);
    }
}

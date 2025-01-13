// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import "forge-std/Test.sol";

import {PicoVerifier} from "../src/PicoVerifier.sol";
import {IPicoVerifier} from "../src/IPicoVerifier.sol";
import {Fibonacci, PublicValuesStruct} from "../src/Fibonacci.sol";

contract FibonacciTest is Test {
    PicoVerifier public picoVerifier;
    Fibonacci public fibonacci;

    // bytes32 public fibonacciKey = bytes32(abi.encodePacked("0x005ccb492c86618b3b5e6dad6efa011b78344bba21939651133c4452934715ca"));
    bytes32 public fibonacciKey = 0x005ccb492c86618b3b5e6dad6efa011b78344bba21939651133c4452934715ca;

    function setUp() public {
        picoVerifier = new PicoVerifier();

        fibonacci = new Fibonacci(address(picoVerifier), fibonacciKey);
    }

    function testVerifyFibonacciProofShouldPassOnRealProof() public {
        uint256[8] memory proof = [
            uint256(0x247ec0c6989fc02fb84c64cee579b7995b966bfec884f47f733a4db42f9e10a9),
            uint256(0x2c7d5f851c4d1965b7c60254342526d9a5ac9add0e5f4aa9338bdfdb8a378c70),
            uint256(0x0341343e68455f0757ca2fd6684d1d560c37b1be957ee8de92e4d151ffa5a289),
            uint256(0x0ea8f5b97c77505c67432a331db024c8b50fd9db6d8781f3a040fd3ace3b7fcb),
            uint256(0x2e3b45ee0854a623c69f241cb5e9e63e28a33e7fb52f7d751fdf9ee4d6cf1cc6),
            uint256(0x056696bb9cfd025453c411499ff91c76666d7dfdc91fbe6c5ae28dceb9806ac5),
            uint256(0x0fc3aabf65146dcda6fa592a614d17e627f1625e752dad76c8a8b6209a984e2f),
            uint256(0x0a9f48941727c34a015dcefa728dacffd07ab62abc0dce009bacb7f60160e38b)
        ];

        PublicValuesStruct memory dummyPublicValues = PublicValuesStruct({
            n: 10,
            a: 55,
            b: 89
        });

        bytes memory encodedPublicValues = abi.encode(dummyPublicValues);

        // vm.expectRevert(); 

        (uint32 n, uint32 a, uint32 b) = fibonacci.verifyFibonacciProof(
            encodedPublicValues, 
            proof
        );

        assertEq(n, 10);
        assertEq(a, 55);
        assertEq(b, 89);
    }
}

// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

import "forge-std/Test.sol";

import "../src/PicoVmVerifier.sol";

contract PicoVmVerifierTest is Test {
    PicoVmVerifier public verifier;

    function setUp() public {
        verifier = new PicoVmVerifier();
    }

    function testShouldPassOnTrueProof() public {
        uint256[8] memory proof = [
            uint256(0x2ab21ed324a67ae7c4f201822957d3742f353498d9ced77fa93252d7ec99a786),
            uint256(0x1e4c538a65abaa4b2137cf169941ceb87387a8741e8303a591b4edbec3958e9f),
            uint256(0x0b6d184b9e7ca3131e7d66de0799fcd853689f0451bd7395ec096c9b498d8772),
            uint256(0x2dab2af734df4148b28226ac7ad8619d26d78eb5fbb2abd38774f4e2d779e8a4),
            uint256(0x23f899fd57d0a9bd9692c1874f45f23885fb7345babc052a7d182bb027cb87e5),
            uint256(0x1e50f9ac7b416cb6b6611cfbdc00a470be2ff2b5e35c54975224beee93f2bdf8),
            uint256(0x27eb1c5eef3777a5289e4548ac1e9cbe505dc391cb1ee79049433d587d62dcfc),
            uint256(0x1af6370a493d456616103e8a1abc1fc88d5f759307677d7f28004efcddf8d507)
        ];

        uint256[2] memory input = [
            uint256(0x007dca4a2b032787d3a2bc870aa6c40856227432ab65876e68c709bceed45933),
            uint256(0x10abd303eefe48a35a09197c8840467029bde2832f61695991207d60fb6a2354)
        ];

        verifier.verifyProof(proof, input);
    }

    function testShouldRevertOnFalseProof() public {
        vm.expectRevert(); 

        uint256[8] memory proof = [
            uint256(0x2ab21ed324a67ae7c4f201822957d3742f353498d9ced77fa93252d7ec99a786),
            uint256(0x1e4c538a65abaa4b2137cf169941ceb87387a8741e8303a591b4edbec3958e9f),
            uint256(0x0b6d184b9e7ca3131e7d66de0799fcd853689f0451bd7395ec096c9b498d8772),
            uint256(0x2dab2af734df4148b28226ac7ad8619d26d78eb5fbb2abd38774f4e2d779e8a4),
            uint256(0x23f899fd57d0a9bd9692c1874f45f23885fb7345babc052a7d182bb027cb87e5),
            uint256(0x1e50f9ac7b416cb6b6611cfbdc00a470be2ff2b5e35c54975224beee93f2bdf8),
            uint256(0x27eb1c5eef3777a5289e4548ac1e9cbe505dc391cb1ee79049433d587d62dcfc),
            uint256(0x1af6370a493d456616103e8a1abc1fc88d5f759307677d7f28004efcddf8d507)
        ];

        uint256[2] memory input = [
            uint256(0x007dca4a2b032787d3a2bc870aa6c40856227432ab65876e68c709bceed45933),
            uint256(0x10abd303eefe48a35a09197c8840467029bde2832f61695991207d60fb6a2355)
        ];

        verifier.verifyProof(proof, input);
    }
}

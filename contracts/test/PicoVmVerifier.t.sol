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
            uint256(0x247ec0c6989fc02fb84c64cee579b7995b966bfec884f47f733a4db42f9e10a9),
            uint256(0x2c7d5f851c4d1965b7c60254342526d9a5ac9add0e5f4aa9338bdfdb8a378c70),
            uint256(0x0341343e68455f0757ca2fd6684d1d560c37b1be957ee8de92e4d151ffa5a289),
            uint256(0x0ea8f5b97c77505c67432a331db024c8b50fd9db6d8781f3a040fd3ace3b7fcb),
            uint256(0x2e3b45ee0854a623c69f241cb5e9e63e28a33e7fb52f7d751fdf9ee4d6cf1cc6),
            uint256(0x056696bb9cfd025453c411499ff91c76666d7dfdc91fbe6c5ae28dceb9806ac5),
            uint256(0x0fc3aabf65146dcda6fa592a614d17e627f1625e752dad76c8a8b6209a984e2f),
            uint256(0x0a9f48941727c34a015dcefa728dacffd07ab62abc0dce009bacb7f60160e38b)
        ];

        uint256[2] memory input = [
            uint256(0x005ccb492c86618b3b5e6dad6efa011b78344bba21939651133c4452934715ca),
            uint256(0x1a92390fa6831fa70c4971165f98bf4eb80d48bd499b067b05c07a89d5b91ead)
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

        // Intentionally modify the last bit of the input to simulate an incorrect proof.
        uint256[2] memory input = [
            uint256(0x007dca4a2b032787d3a2bc870aa6c40856227432ab65876e68c709bceed45933),
            uint256(0x10abd303eefe48a35a09197c8840467029bde2832f61695991207d60fb6a2355)
        ];

        verifier.verifyProof(proof, input);
    }
}

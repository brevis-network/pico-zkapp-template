// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

/*
  Step 2: Read inputs and call the contract in a view-only way.
  - Reads contract addresses from ./script/addresses.json
  - Reads proof inputs from ./test_data/inputs.json
  - Performs a view call: fibonacci.verifyFibonacciProof(publicValues, proof)
  - No broadcast (eth_call), so no gas spent.
*/

import "forge-std/Script.sol";
import {PicoVerifier} from "../src/PicoVerifier.sol";
import {Fibonacci} from "../src/Fibonacci.sol";

interface IFibonacci {
    function verifyFibonacciProof(bytes calldata publicValues, uint256[8] calldata proof)
        external
        view
        returns (uint32 n, uint32 a, uint32 b);
}

contract VerifyOnly is Script {
    function run() external view {
        // 1) Load deployed addresses
        string memory addrPath = "./script/addresses.json";
        string memory addrJson = vm.readFile(addrPath);
        address fibonacciAddr = abi.decode(vm.parseJson(addrJson, ".fibonacci"), (address));

        // 2) Load proof inputs
        string memory inputPath = "./test_data/inputs.json";
        string memory inputJson = vm.readFile(inputPath);

        // (Optional) If you want to confirm the deployed key matches:
        // bytes32 riscvVKey = abi.decode(vm.parseJson(inputJson, ".riscvVKey"), (bytes32));

        bytes memory publicValues = abi.decode(vm.parseJson(inputJson, ".publicValues"), (bytes));
        bytes32[] memory proofBytes32 = abi.decode(vm.parseJson(inputJson, ".proof"), (bytes32[]));
        require(proofBytes32.length == 8, "proof must have 8 words");
        uint256[8] memory proof;
        for (uint256 i = 0; i < 8; i++) {
            proof[i] = uint256(proofBytes32[i]);
        }

        // 3) View call (no broadcast)
        (uint32 n, uint32 a, uint32 b) =
            IFibonacci(fibonacciAddr).verifyFibonacciProof(publicValues, proof);

        console2.log("verify ok -> n=%s a=%s b=%s", n, a, b);
    }
}

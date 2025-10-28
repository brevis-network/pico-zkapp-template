// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

/*
  Step 1: Deploy contracts only.
  - Broadcasts transactions using PRIVATE_KEY.
  - Writes deployed addresses to ./script/addresses.json for Step 2.
*/

import "forge-std/Script.sol";
import {PicoVerifier} from "../src/PicoVerifier.sol";
import {Fibonacci} from "../src/Fibonacci.sol";

contract DeployPicoFibo is Script {
    function run() external {
        // Use the real key from inputs.json (recommended)
        string memory inputJson = vm.readFile("./test_data/inputs.json");
        bytes32 realKey = abi.decode(vm.parseJson(inputJson, ".riscvVKey"), (bytes32));

        vm.startBroadcast();
        PicoVerifier picoVerifier = new PicoVerifier();
        Fibonacci fibonacci = new Fibonacci(address(picoVerifier), realKey);
        vm.stopBroadcast();

        console2.log("PicoVerifier:", address(picoVerifier));
        console2.log("Fibonacci:   ", address(fibonacci));

        // Persist addresses for Verify step
        string memory root = "deploy";
        vm.serializeAddress(root, "picoVerifier", address(picoVerifier));
        string memory json = vm.serializeAddress(root, "fibonacci", address(fibonacci));
        vm.writeJson(json, "./script/addresses.json");
    }
}

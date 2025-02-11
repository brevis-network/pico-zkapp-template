// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import {IPicoVerifier} from "./IPicoVerifier.sol";

struct PublicValuesStruct {
    uint32 n;
    uint32 a;
    uint32 b;
}

/// @title Fibonacci.
/// @author Brevis Network
/// @notice This contract implements a simple example of a fibonacci zkApp workflow
contract Fibonacci {
    /// @notice The address of the Pico verifier contract.
    address public verifier;

    /// @notice The verification key for the fibonacci riscv program.
    bytes32 public fibonacciVKey;

    constructor(address _verifier, bytes32 _fibonacciVKey) {
        verifier = _verifier;
        fibonacciVKey = _fibonacciVKey;
    }

    /// @notice The entrypoint for verifying the proof of a fibonacci program.
    /// @param _proof The proof.
    /// @param _publicValues The encoded public values, which can also be used for zkApp.
    function verifyFibonacciProof(
        bytes calldata _publicValues,
        uint256[8] calldata _proof
    ) public view returns (uint32, uint32, uint32) {
        // Constrain riscvVKey to be equal to fibonacciVKey.
        IPicoVerifier(verifier).verifyPicoProof(
            fibonacciVKey,
            _publicValues,
            _proof
        );
        PublicValuesStruct memory publicValues = abi.decode(
            _publicValues,
            (PublicValuesStruct)
        );
        return (publicValues.n, publicValues.a, publicValues.b);
    }
}

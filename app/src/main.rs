#![no_main]
pico_sdk::entrypoint!(main);

use rsp_client_executor::{
    executor::{EthClientExecutor, DESERIALZE_INPUTS},
    io::{CommittedHeader, EthClientExecutorInput},
    utils::profile_report,
};
use std::sync::Arc;

pub fn main() {
    let input = profile_report!(DESERIALZE_INPUTS, {
        let input = pico_sdk::io::read_vec();
        bincode::deserialize::<EthClientExecutorInput>(&input).unwrap()
    });

    let executor = EthClientExecutor::eth(
        Arc::new((&input.genesis).try_into().unwrap()),
        input.custom_beneficiary,
    );
    let header = executor.execute(input).expect("failed to execute client");

    pico_sdk::io::commit::<CommittedHeader>(&header.into());
}

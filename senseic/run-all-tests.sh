#!/bin/bash
cargo test --workspace
cd ./sir/sir-solidity-diff-tests/ && forge test --ffi
cd ..

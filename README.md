# Movable

A symbolic execution tool for [Move](https://github.com/libra/libra/tree/master/language), which is a smart contract language designed for [Diem](https://diem.com).

## Diem Setup

Clone [Diem](https://github.com/diem/diem) to the parent directory of Movable. The directory structure should look like:

```
|_ diem
|_ Movable
```

Diem repository should be checkout to tag `diem-framework-v1.2.0`. Other versions are untested.

## Usage

```sh
cargo run <BYTECODE_FILE> -f <FUNCTION_NAME>
```

## Roadmap

### Engine

- Transaction configuration
- Symbolic execution configuration

### Symbolic Chain State

- Start from states other than genesis
- Symbolic writeset
- Custom data store

### Symbolic VM

- Vector bound check (in plugin or not?)
- Native function modelling
- Stdlib test
- More benchmarks
- Docking with plugin system (intarith plugin running)
- Gas infrastructure
- Debug and log infrastructure

### Plugin System

- Single instruction listening support (intarith plugin added)
- Verification plugin support
# Movable

A symbolic execution tool for [Move](https://github.com/libra/libra/tree/master/language), which is a smart contract language designed for [Libra](https://libra.org).

## Libra Setup

Clone [Libra](https://github.com/libra/libra) to the parent directory of Movable. The directory structure should look like:

```
|_ libra
|_ Movable
```

Libra repository should be checkout to 4ed956c16f61dac52f40d413266d1ffd6fbb9b50. Other versions are untested.

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

- Constants support
- Generics support
- Vector support
- Native function modelling
- Stdlib test
- More benchmarks
- Docking with plugin system
- Gas infrastructure
- Debug and log infrastructure
- Code rewrite

### Plugin System

- Single instruction listening support
# Mitra Chess Engine

Mitra is a small, self-contained C++17 chess engine that speaks the Universal Chess Interface (UCI). It has no third-party runtime or library dependencies and can be used from a chess GUI that supports UCI.

## Build and test

Requirements: a C++17 compiler and pthread support (for example, `g++` on Linux/macOS).

```sh
make
make test
```

Or use CMake:

```sh
cmake -S . -B build -DCMAKE_BUILD_TYPE=Release
cmake --build build --config Release
```

The executable is `./mitra` (or `build/mitra` with CMake).

## Use

Start the UCI protocol:

```sh
./mitra
```

Useful commands in a UCI GUI or terminal:

```text
uci
isready
position startpos
go depth 8
```

Mitra also accepts FEN positions and move lists, standard UCI clock controls, `stop`, `ucinewgame`, and the `Hash` / `Clear Hash` options. For terminal testing:

```sh
./mitra --selftest
./mitra --perft 5
./mitra --bench 6
```

`go perft N` is available as a UCI-style debugging extension. `--perft` and `go perft` count legal move-tree nodes; they are not search commands.

## What's implemented

- Legal chess move generation, including castling, en passant, and all promotions
- Incremental Zobrist hashing and reversible make/unmake
- Iterative-deepening negamax with aspiration windows, principal-variation search, quiescence search, and a transposition table
- Move ordering, killer/history heuristics, late-move reductions, null-move pruning, and basic time management
- Material, piece-square, mobility, pawn-structure, passed-pawn, rook-file, bishop-pair, and king-safety evaluation
- UCI search runs asynchronously so `stop` and other UCI commands remain responsive

## Strength target

The goal is to grow this into an engine that can challenge a 2100 FIDE player. Elo is not something I can honestly guarantee from source inspection or a few tactical tests: it must be measured in a controlled match set against rated opponents with fixed hardware, time controls, and a sufficiently large sample. Mitra is a new hand-written engine, not a port of Stockfish, and should be treated as an experimental baseline until that testing and tuning is done. The included perft suite checks move-generation correctness; it is not an Elo claim.

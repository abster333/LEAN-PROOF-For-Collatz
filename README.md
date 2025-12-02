# Collatz CollatzProof

Lean 4 formalization work exploring the Collatz conjecture, focusing on cycles/loops and reverse trajectories. The repository also contains an informal write‑up of the ideas in prose form.

## Layout
- `CollatzProof/` – Lake project (Lean 4.2.0 + mathlib). Entry module is `CollatzProof.lean`, with the core development in `CollatzProof/Collatz.lean` and supporting lemmas about odd numbers modulo 6 in `CollatzProof/OddTypes.lean`.
- `Proof.md` – informal paper draft outlining the argument that nontrivial loops cannot exist.
- `tmp.lean` – scratchpad used during development (not part of the library).

## Prerequisites
- Lean `leanprover/lean4:v4.2.0` (pinned in `CollatzProof/lean-toolchain`)
- Lake (installed alongside Lean)
- Git for pulling mathlib (handled automatically by Lake)

## Getting Started
```bash
# from the repo root
cd CollatzProof
lake update   # fetch mathlib and other deps on first run
lake build    # compile the project
```

## Developing
- Open the project directory `CollatzProof/` in VS Code with the Lean 4 extension, or use `lake env lean` to load files in a terminal editor.
- The classical 1 → 4 → 2 → 1 cycle is formalized in `CollatzProof/Collatz.lean`, along with loop/trajectory definitions and reverse-step analysis. The congruence-based odd number partition lives in `CollatzProof/OddTypes.lean`.
- Contributions are welcome; keep proofs minimal and documented with brief comments when the strategy is not obvious.

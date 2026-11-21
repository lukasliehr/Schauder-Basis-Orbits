# Prompt 5 result

Date: 2026-11-19.

The original `MainResult` in `Showcase.lean` now has a complete Lean proof. The file keeps the original six definitions and theorem statement. The proof import loads `LeanCode/Main.lean`, and the proof of `MainResult` invokes the library theorem `SchauderBasisOrbits.mainResult`.

The proof library lives in `LeanCode/` and keeps the theorem namespace `SchauderBasisOrbits`. The project pins Lean 4.36.0 and Mathlib commit `1ddfaa9548e05b343be9248ae08b73c3425b446e`. It contains 105 library source files plus `Showcase.lean`. The implementation splits several of the blueprint's proposed files so their prerequisites can compile separately. Three subagents worked on the finite estimates, scalar packets, and spectral and product constructions.

The proof implements both directions. In the forward direction, the cyclic spectral realization gives a singleton-null probability measure. The finite row estimates support an unconditional scalar packet supply. The directional construction uses the response of the whitened row eigenbasis and checks cuts inside columns before centering and amplification. The residual and product estimates give the finite line extension via simultaneous graph averaging. Iteration and the positive limiting weight yield an ordered rational exponential basis, which is transported through the weight isometry and the cyclic intertwiner. The reverse implication uses the weak convergence of bounded Schauder basis vectors to exclude common eigenvectors.

The Lean implementation chooses each seed dimension before requesting the corresponding small scalar loss. It also proves the sharp skew arrow estimate using a two-dimensional top eigenspace and a vector in that eigenspace whose last coordinate is zero. The proof uses the paper's mathematics and pinned Mathlib, with the FLT Lean development excluded.

## Verification

- `lake build Showcase LeanCode` completed successfully.
- `#print axioms MainResult` and `#print axioms SchauderBasisOrbits.mainResult` returned exactly `[propext, Classical.choice, Quot.sound]`.
- Compared with the original, `Showcase.lean` has two changes. It adds `import LeanCode.Main` and replaces `sorry` with the proof.
- The current Lean sources contain no `sorry`, `admit`, or project axiom declarations.
- The Prompt 5 snapshot includes the pinned toolchain and dependency lockfile, both manuscripts and PDFs, the blueprint, and the complete current source. Earlier numbered snapshots retain their original contents. Local AGENTS, scripts, and build outputs are excluded.

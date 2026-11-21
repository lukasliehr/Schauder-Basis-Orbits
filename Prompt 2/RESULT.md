# Prompt 2 result

Date: 2026-11-18.

## Deliverable

Added `AUDIT.md`, a detailed source-level audit of the formalization of `thm:main`. It covers all named proof components, actual Mathlib support, missing project interfaces, representation hazards, alternatives, concrete proof reformulations, and an implementation order with acceptance checks.

## Main finding

Mathlib supplies the foundational mathematical frameworks, but a Mathlib-only implementation of the current proof still requires substantial project-specific auxiliary development. The main work is the finite weighted-family interface, sharp oblique-projection and row-splitting estimates, scalar and directional packet constructions, and ordered infinite assembly. This is an assessment of the present strategy, not a proof that no easier strategy exists.

The report identifies opportunities to reduce that development: use Mathlib's Schauder basis constructor, Gram positivity and Schur complement APIs, operator inverse convexity, character independence plus analytic accumulation, Lévy tightness, explicit fiber integrals, and finite Hilbert tuples.

A literal missing backslash before `quad` in `paper.tex` at line 653 is recorded for a subsequent correction. The mathematical paper and its compiled PDF were not changed by this audit.

## Sources and limits

The existing July Mathlib checkout was checked at commit `81a5d257c8e410db227a6665ed08f64fea08e997` with Lean `v4.32.0`. The primary availability assessment uses the downloaded upstream source at commit `1ddfaa9548e05b343be9248ae08b73c3425b446e` from 2026-11-18, with Lean `v4.36.0`.

The newer Mathlib source contains 8,725 Lean files. The audit includes 42 pinned source links, checked against the actual files and their expected anchor text. Absence findings are qualified as results not located by the searches and source inspection, rather than exhaustive nonexistence claims.

No project Lean source or proof probes were written. The project and the newer Mathlib source were not compiled; this is not kernel verification or an elaboration-compatibility test.

The user's follow-up excludes FLT Lean code. That implementation is not used, imported, copied into the repository, or recommended as a dependency. The follow-up is recorded under Prompt 2 and does not create another numbered snapshot.

## Validation and preservation

- All 42 Markdown source references have definitions and match actual source anchors at the pinned Mathlib revision.
- Key API namespaces, the reported typo location, and the source metadata were checked.
- `paper.tex`, `paper.pdf`, `Showcase.lean`, and the empty `README.md` remain byte-for-byte unchanged.
- The earlier `Prompt 1` snapshot is unchanged.
- `AGENTS.md` and `scripts/` remain local and excluded from the snapshot and GitHub.
- Downloaded library sources and research helpers remain outside the repository; no Mathlib source tree is included in the snapshot.
- `git diff --check` passed.

`AUDIT.md` SHA-256: `b1c17cf2ac8aa43f17b648f85ce5e155108b63a3d563de8832a9ab7be54da8a6`.

## Snapshot

`Prompt 2` contains the current project, including `AUDIT.md` and the existing compiled `paper.pdf`, together with the prompt and this result record. It excludes the earlier snapshot directory.

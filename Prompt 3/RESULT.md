# Prompt 3 result

Date: 2026-11-18.

## Deliverables

Added `refactored.tex`, a standalone mathematical manuscript based on `paper.tex` and the findings in `AUDIT.md`, and its compiled 35-page `refactored.pdf`.

The statement carrying the label `thm:main` is byte-for-byte identical to the corresponding statement in `paper.tex`. The refactored document retains the original theorem's assumptions and definitions, explains the change to Mathlib's inner-product convention, and preserves the quantitative weighted-basis conclusion used by the construction.

## Refactoring

The document contains 13 main sections and an appendix, with 8 definitions and 82 separately stated results with proofs: 74 lemmas, 6 propositions, and 2 theorems. The principal changes are:

- Explicit bounded character representatives, weighted measures, normalized product measures, and ordered prefix-bound predicates instead of optimal finite basis constants.
- Separate matrix lemmas for inverse quadratic forms, inverse compression and exhaustion, Gram stability, projection distances, adjoint norms, and oblique projections.
- A finite Hilbert-tuple formulation of the activated row calculation, with independent proofs of the skew-arrowhead estimate, two-Gram interpolation, and finite-rank two-projection decomposition.
- Separate scalar activation, copying, numerical, inverse, and prefix steps, followed by a full induction, finite Fejer smoothing, and exact gain tuning.
- A directional construction with uniform response estimates on a sequence of changing finite systems, explicit seed spectral bounds, completed- and partial-column estimates, centering, and amplification.
- An explicit order of choices for residual copies and one common tolerance for the product extension.
- Separate graph-averaging, frequency-separation, and relative-Gram transfer results.
- Explicit recurrent scheduling, compatible stage data, positive limiting weights, ordered limit lists, and passage of finite prefix inequalities to the limit.
- Character independence and the analytic accumulation-point argument using existing Mathlib results.
- An orbit-specific positive-integral construction of the scalar spectral measure, followed by Mathlib's characteristic-function tightness theorem and probability compactness.
- Separate equal-Gram extension, cyclic intertwining, exclusion of point masses, positive-weight isometry, and basis transport lemmas.

The manuscript states its foundational boundary explicitly. It is self-contained relative to the enumerated Mathlib foundations permitted in the preceding prompts; all specialized constructions needed by the main theorem have proofs in the manuscript. The appendix contains 28 pinned Mathlib source pointers and a crosswalk to the audit findings. The Mathlib revision is `1ddfaa9548e05b343be9248ae08b73c3425b446e`, with Lean `v4.36.0`.

The conventional expansion-only definition of Schauder basis is retained and its continuous-coordinate bridge is proved. The document explains that a future formalization against the supplied Mathlib basis type can use its existing fields and constructor directly.

## Validation

- Manual mathematical review of the refactored argument, with explicit checks of hypotheses, normalizations, parameter choices, and dependency order.
- All 82 stated results are associated with distinct, nonempty proofs; the graph of cited result dependencies is acyclic.
- All 94 labels are unique and every internal cross-reference resolves.
- The exact text of `thm:main` matches the original.
- The final `pdflatex` build has no warnings, undefined references, overfull boxes, or underfull boxes. The table of contents is stable.
- All 35 rendered pages were visually checked, including enlarged checks of dense mathematical pages. A section heading stranded at the bottom of a page was moved with its following material.
- All 28 pinned Mathlib file anchors were checked against the inspected source revision.
- Supplemental numerical checks passed for 120 complex information/projection-distance cases and 216 scalar parameter-step cases. These consistency checks are not mathematical proofs.

No Lean source or proof probes were written or modified, and no Lean verification is claimed. The project-specific lemmas remain future formalization work. No FLT Lean code was reused.

## Preservation and snapshot

`paper.tex`, `paper.pdf`, `AUDIT.md`, `Showcase.lean`, and the empty `README.md` are unchanged. The earlier Prompt 1 and Prompt 2 snapshots are unchanged. `AGENTS.md`, scripts, build intermediates, and downloaded libraries remain excluded from GitHub and snapshots.

Prompt 3 contains the complete current versioned project, including both manuscripts and PDFs, together with this prompt and result record. Earlier numbered folders are not nested inside it.

## Fingerprints

- `refactored.tex` SHA-256: `fb0609bfb4e763e689c3e351cd174b232227e4664826c6438bf7b0c48e2a87de`.
- `refactored.pdf` SHA-256: `f80976f54a55d4bd7e77264f20e71c040cd3ecffeecc2f3b825a7fe9a9e17efa`.

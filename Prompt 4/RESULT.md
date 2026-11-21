# Prompt 4 result

Date: 2026-11-18.

## Deliverable

Added `BLUEPRINT.md`, a formalization blueprint for the exact `MainResult` in `Showcase.lean`, based on `refactored.tex` and the preceding audit. It contains:

- Explicit representation conventions for raw functions, weighted L² spaces, matrices, ordered finite families, auxiliary coordinates, scalar data and construction states.
- 236 project definitions/lemma interfaces with direct dependencies, mathematical contracts, detailed proof strategies and proposed file placement.
- 27 Mathlib foundation groups, with 67 distinct source anchors checked at commit `1ddfaa9548e05b343be9248ae08b73c3425b446e`, using Lean `v4.36.0`.
- An incremental layout of 35 proposed Lean files, including the public entry point, with an acyclic import plan and implementation order.
- A complete JSON dependency manifest and a crosswalk accounting for all 90 manuscript definition/result labels. The two coefficient-space bridges are explicitly bypassed using the native Schauder-basis interface.
- A three-round independent audit record and final implementation acceptance criteria.

The blueprint explicitly includes the substantial project-specific work: infinite Hilbert-tuple adapters, the sharp row estimate, scalar packet induction, directional selection including internal cuts, normalized product and graph transfers, ordered limiting assembly, and the orbit-specific spectral probability construction. These are proposed proofs to implement, not claims that the specialized theorems already exist in Mathlib.

## Independent verification and revisions

Three different subagents audited successive complete candidates. Each later review began from scratch without consulting previous reports or revision logs.

The first audit required explicit finite-measure/integrability hypotheses, singleton-nullity in graph averaging, six definition-dependency edges, and relocation of scalar gain transport after its definition. These were corrected. The second found an empty-block counterexample to a generic joining contract with negative error allowance; the contract now states nonnegativity and proves its empty and zero-space cases. Additional interface clarifications made positivity premises and definition placement explicit and reused Mathlib's existing bundled L² pullback isometry.

The third independent audit returned **PASS**, with no required changes. It found no material false contract, missing substantial mathematical component, semantic dependency cycle, or missing path to the exact target. It reviewed the manuscript, quantitative estimates, normalization, partial prefixes, spectral route, native basis constructor and actual pinned Mathlib declarations.

After the passing audit, only the audit-record section was updated. Sections 1–9 were checked to remain byte-for-byte identical to the accepted candidate.

## Validation and limits

- All 263 graph vertices are reachable backwards from the exact public endpoint `GOAL03`.
- The node graph and derived 35-file import graph are acyclic.
- Every project ledger dependency list matches the JSON manifest, and all named node references in contracts and strategies are declared ancestors.
- All proposed nodes have a file assignment and a valid implementation order.
- All 67 cited source anchors match the inspected immutable Mathlib source.
- Markdown fences and identifiers were checked, and no generation markers or temporary-path links remain.
- The exact target hypotheses and literal orbit-basis vector equations are retained.

No Lean source or proof probe was written, modified or compiled. `Showcase.lean` retains its existing `sorry`; the blueprint has not been implemented or kernel-verified. No FLT Lean development was reused. No unresolved material blueprint dependency was identified by the final independent review.

## Preservation and snapshot

`paper.tex`, `paper.pdf`, `refactored.tex`, `refactored.pdf`, `AUDIT.md`, `Showcase.lean`, and the empty `README.md` are unchanged. Earlier Prompt 1–3 snapshots are unchanged. Since neither manuscript changed, their existing compiled PDFs are retained unchanged.

Prompt 4 contains the complete current versioned project, including both manuscripts, both PDFs and the new blueprint, plus this prompt and result record. Earlier numbered folders are not nested inside it. `AGENTS.md`, scripts, downloaded dependencies, audit scratch files and build intermediates remain excluded from GitHub and snapshots.

## Fingerprints

- Final `BLUEPRINT.md` SHA-256: `b1b8a505d2a68523175de56babad31222732831d4927008d00efd5d4fe1d5377`.
- Independently accepted candidate SHA-256: `988c2ac3316cdf6e3e7324b32250e4b1bff9bedb9bd461ca88cec42d01404c59`.
- Dependency manifest SHA-256: `e44518f31dcc80324185aa4d6d128a3ac3d6bccb436674b6064f80a0ba1b362e`.

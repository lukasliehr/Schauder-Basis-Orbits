# Prompt 1 result

Date: 2026-11-18.

## Changes

Expanded `paper.tex` to establish the specialized mathematical inputs needed for `thm:main`, using only the explicitly inventoried Mathlib results as unproved foundations. Appendix A lists the original cited and implicit dependencies, explains their replacements, identifies the Mathlib declarations and source revision, and checks correspondence with the supplied Lean statement.

The additions include:

- Continuity of basis coordinates from unique expansions, weak nullity of bounded Hilbert-space bases, and the bounded-prefix basis criterion.
- A proof of the scalar spectral-measure representation, the complex-density reduction for Fourier uniqueness, totality of rational exponentials, and independence under atomless measures.
- Finite Gram and projection estimates, inverse compression and averaging, a direct two-projection decomposition, and the real-skew arrowhead estimate.
- The scalar small-loss construction, its induction and polynomial smoothing, the directional construction and every within-column prefix bound, and residual replication.
- Direct graph averaging without invoking Wiener's lemma, transfer to rational frequencies, positivity of the limiting weight, the limiting basis construction, and the final unitary equivalence.

The finite scalar and directional constructions develop the method of Freeman, Liehr and Taylor, arXiv:2610.18709v2. The bibliography records this source; none of its propositions is left as an assumed proof input.

## Independent audit

A separate subagent read the full revised proof, checked the delicate matrix and limiting arguments, compared the target with `Showcase.lean`, and inspected the actual Mathlib declarations and their hypotheses. The audit identified a transcription error in the scalar induction budget: the condition must be `z_p <= Z_0 * 2^(-n-3)`, not two separate bounds. That condition was corrected and rechecked. The dense-span extension arguments were also made explicit using Cauchy sequences.

The audit found no unresolved substantive mathematical gap or specialized external dependency after these corrections. This conclusion is relative to the Mathlib foundations expressly permitted by the prompt and listed in Appendix A.2. It is a manual mathematical and source-level audit, not Lean formal verification.

Mathlib was inspected at clean commit `81a5d257c8e410db227a6665ed08f64fea08e997` of `leanprover-community/mathlib4`, with toolchain `leanprover/lean4:v4.32.0`. No absence claim is made about other revisions.

## Validation

- `pdflatex` completed successfully; the final document has 17 pages.
- The final compiler log has no warnings, undefined references, overfull boxes, or underfull boxes. All 29 labels are unique and all internal references resolve.
- All rendered pages were inspected for layout, with enlarged checks of dense mathematics and the dependency ledger.
- Supplemental numerical transcription checks passed for 240 real-skew arrowhead cases and 1,080 row-block cases. These checks do not replace the proofs.
- `Showcase.lean` is byte-for-byte identical to the file supplied by the user. No Lean source was written or modified, and no Lean compilation or formal proof check was performed. Its original `sorry` remains.
- `README.md` remains empty. `AGENTS.md` and `scripts/` remain local and are excluded from GitHub and this snapshot. The user's follow-up requested the compiled PDF in the repository: `paper.pdf` is included both at the root and in `Prompt 1`. Intermediate LaTeX output is kept outside the repository.

## Source fingerprints

- `paper.tex` SHA-256: `19adabb7335302326e820be695c104d1fee69b8674a11fac4abfdc828a070ec2`.
- `Showcase.lean` SHA-256: `355e6e01d67a1895baef0d5e4e62bf23e219725f4b2b864fff41cb3049bc44e5`.

## Snapshot

`Prompt 1` records the project source after this prompt, together with the prompt and this result record. Earlier setup commits were not assigned prompt numbers.

The PDF was recompiled and added as a follow-up to Prompt 1, without creating a new numbered snapshot. The root and snapshot PDFs are identical and compile from the unchanged audited TeX source.

# Prompt 2: Lean 4 formalization audit

Date: 2026-11-18. Target: `thm:main` in `paper.tex`, corresponding to `MainResult` in `Showcase.lean`.

## 1. Conclusion

**The proof is mathematically expressible using Mathlib's existing foundations, but it is not ready for a formalization that requires only a small amount of additional infrastructure.** The main obstacle is the large, reusable layer of finite weighted Fourier systems and quantitative projection estimates in the scalar and directional constructions. Those results have proofs in the paper; that does not mean that their definitions, intermediate interfaces, and proofs are already implemented in Mathlib.

There is no identified need to build a new general theory of Hilbert spaces, integration, Fourier transforms, probability measures, or finite-dimensional spectral theory. Nevertheless, a Mathlib-only implementation of this proof would require substantial project-specific development. Here, “substantial” means several interdependent modules of reusable definitions and lemmas, rather than a few local rewrites or isolated auxiliary facts. This is an assessment of this proof strategy, not a claim that no easier proof of the theorem can exist.

The difficult direction is **simple continuous spectrum implies the existence of an orbit Schauder basis**. The reverse direction is comparatively well supported: use Mathlib's Schauder basis coordinates, Hilbert duality, and a short weak-nullity argument.

The highest-priority work would be:

1. Establish a consistent interface for finite ordered families, their Gram matrices, and prefix bounds.
2. Formalize the sharp oblique-projection and row-splitting estimates. These are the main technical risk.
3. Formalize the scalar supply and directional construction using explicit finite product measures and finite character sums.
4. Connect the resulting ordered finite extensions to Mathlib's existing Schauder basis constructor.
5. Prove the spectral-measure and weighted-isometry adapters, reusing more of Mathlib than the paper currently does.

**User constraint:** the follow-up instruction excludes reuse of the FLT paper's Lean code. Accordingly, all implementation recommendations below use Mathlib and the mathematical arguments in `paper.tex`; the external FLT Lean implementation is not an allowed dependency or reuse route. This follow-up is part of Prompt 2.

## 2. Scope and evidence

The audited paper is the version committed in this repository at `6d4773cc7114791e641ab1317c3a3ba97adc7bb3`, with SHA-256 `19adabb7335302326e820be695c104d1fee69b8674a11fac4abfdc828a070ec2`. Its mathematical source is unchanged by this audit. References to paper line numbers below refer to this version.

Two Mathlib revisions were distinguished:

| Source | Revision | Lean toolchain | Role |
| --- | --- | --- | --- |
| Existing clean local checkout used in Prompt 1 | `81a5d257c8e410db227a6665ed08f64fea08e997`, 2026-07-13 | `v4.32.0` | Check the provenance of the paper's existing dependency inventory. |
| Upstream `master` checked for this audit | `1ddfaa9548e05b343be9248ae08b73c3425b446e`, 2026-11-18 | `v4.36.0` | Primary basis for the present availability assessment and source links. |

The newer revision was downloaded as a pinned source archive outside this repository. Its `Mathlib` directory contains 8,725 Lean source files. The archive SHA-256 is `8e0a186e1d76ddd16cfb649a445146da83259fa3e11ac924885be164e47e3d4a`. Upstream HEAD can change; all Mathlib links in this audit are pinned to the inspected revision.

The investigation combined whole-library name/comment searches with reading actual declarations, hypotheses, implementations, and neighboring APIs. Searches covered Bochner/positive-definite functions, spectral representations, Schauder bases, Gram matrices, matrix norms and order, Schur complements, Woodbury identities, inverse convexity, projection estimates, Fourier characters, Fejer kernels, weighted `Lp`, conditional expectation, analytic zeros, probability tightness, and infinite products. Results with similar names were checked for scope: finite-group character independence, orthogonal projections, `L1` density isometries, and finite-dimensional spectral theory are not automatically the results needed here.

“Not located” below means that a suitable packaged result was not found through these searches and source inspections. It is not an exhaustive mathematical nonexistence claim about the library. The assessment is source-level: no new Lean source, proof probes, or formalization were written, and neither the project nor the downloaded newer Mathlib was compiled. No claim of elaboration compatibility or kernel verification is made. The existing `sorry` in `Showcase.lean` remains.

The repository currently has a standalone `Showcase.lean`, but no `lakefile` or `lean-toolchain`. A subsequent implementation must explicitly choose and pin a toolchain/Mathlib pair. The July pin cited in the paper does not configure the project automatically.

## 3. What Mathlib actually supplies

Availability has three different meanings here: an ambient mathematical object can exist, a general supporting theorem can exist, and the exact construction used in the paper can exist. The first two are often available; the third frequently is not.

| Area | Verified Mathlib support | What still has to be supplied for this proof |
| --- | --- | --- |
| Schauder bases | `GeneralSchauderBasis`, `SchauderBasis`, continuous coordinates, `SchauderBasis.tendsto_proj`, `exists_norm_proj_le`; `SchauderBasis.RankOneDecomposition.basis` and `basis_coe`. [Definitions][BASIS], [constructor][BASISBUILD]. | A finite-prefix-bound adapter; weak nullity for the bounded basis; transport under the final isometry. No new general definition of Schauder basis is needed. |
| Finite Gram matrices | `Matrix.gram`, `star_dotProduct_gram_mulVec`, `posDef_gram_iff_linearIndependent`. [Source][GRAM]. | Ordered prefix bounds, centering, quotient/restriction bounds, normalization rules, and the projection-distance formulas in the form needed by the construction. |
| Matrix operator norms | The scoped `Matrix.Norms.L2Operator` instances, `Matrix.l2_opNorm_def`, `toEuclideanCLM`, and adjoint/product norm identities. [Source][L2NORM]. | Consistent use of this norm throughout. The default norm in `Analysis/Matrix/Normed.lean` is entrywise supremum, not the paper's Hilbert operator norm. [Default norm][ENTRYNORM]. |
| Positive matrix order and square roots | `MatrixOrder`, `Matrix.le_iff`, `isStrictlyPositive_iff_posDef`, continuous functional calculus, and `Matrix.PosSemidef.inv_sqrt`. [Source][MATRIXORDER]. | State every inverse's invertibility/strict-positivity hypotheses and consistently distinguish matrix order from scalar or entrywise order. |
| Schur complements and rank-one updates | `Matrix.PosDef.fromBlocks₁₁`, `Matrix.PosDef.fromBlocks₂₂`, block inverse formulas, and `Matrix.add_mul_mul_inv_eq_sub`. [Schur complements][SCHUR], [Woodbury][WOODBURY]. | Specialize these to the scalar gain, centered Gram matrix, and projection-information formulas; discharge the explicit `Invertible`/`IsUnit` hypotheses. The inspected Schur lemmas have a positive-definite pivot hypothesis and a positive-semidefinite block conclusion. |
| Inverse monotonicity and convexity | `CStarAlgebra.antitoneOn_ringInverse`, `CStarAlgebra.ringInverse_le_ringInverse`, and `CStarAlgebra.convexOn_ringInverse`. [Order][INVORDER], [convexity][INVCONVEX]. | Inverse compression and the integral averaging statement still need an adapter. A two-point operator-convexity theorem alone is not the paper's integral Jensen statement. |
| Hilbert decompositions | Orthogonal projections and `Submodule.orthogonalDecomposition` into `WithLp 2 (K × Kᗮ)`. [Source][PROD]. | The norm identity for a general oblique projection, the finite-rank two-projection decomposition, and the sharp row-splitting estimate. Orthogonal projection norm bounds do not prove these. |
| Operator norms from quadratic forms | `ContinuousLinearMap.norm_eq_iSup_rayleighQuotient` for symmetric maps. [Source][RAYLEIGH]. | The particular skew-arrowhead identity and its perturbation inequality, with real/complex scalar changes handled explicitly. |
| Circle and finite-torus characters | `AddCircle.span_fourierLp_closure_eq_top`, Fourier coefficients and orthogonality; `UnitAddTorus.mFourier` and its multiplication, conjugation, norm, and density results. [Circle][FOURIER1], [finite torus][FOURIERMULTI]. | A finite character-polynomial interface on `ℝ × T^d`, tracking rational real frequencies and auxiliary modes, plus the particular finite Fejer kernels. |
| Character polynomial algebra | `BoundedContinuousFunction.charAlgHom` and `charPoly` use `AddMonoidAlgebra`. [Source][CHARPOLY]. | Adapt or specialize finite-support evaluation to the mixed real/torus domain. This is useful infrastructure, not a ready-made scalar or directional supply theorem. |
| Exponential independence | `linearIndependent_monoidHom`, analytic identity/isolated-zero principles, and `exists_accPt_of_nullSingletonClass`. [Characters][CHARINDEP], [analyticity][ANALYTIC], [accumulation][ACCPOINT]. | Build the exponential characters and prove frequency injectivity; transfer pointwise independence to equality classes in `L2(ν)`. The finite-group `AddChar.linearIndependent` theorem is not directly applicable to `ℝ`. |
| Singleton-null measures | `MeasureTheory.NullSingletonClass` and `Set.Countable.measure_zero`. [Source][NULLPOINTS]. | Use these for the paper's stated meaning of “atomless.” Current `MeasureTheory.NoAtoms` concerns measurable atoms and is a different definition. [Source][NOATOMS]. |
| Fourier uniqueness and inversion | `MeasureTheory.Measure.ext_of_charFun`, `Continuous.fourierInv_fourier_eq`, `fourier_gaussian_pi`. [Uniqueness][CHARUNIQUE], [inversion][FOURIERINV], [Gaussian][GAUSSIAN]. | Complex-density uniqueness, parameter normalization, integrability obligations, and the actual spectral-measure construction. These theorems are not Bochner's representation theorem. |
| Probability compactness | `isTightMeasureSet_of_tendsto_charFun`, `isCompact_closure_of_isTightMeasureSet`, and weak convergence against bounded continuous complex functions. [Tightness][LEVY], [compactness][PROKHOROV], [weak convergence][WEAKPROB]. | Construct the approximating probabilities, recover a cluster probability's characteristic function, and then build the cyclic isometry. |
| Weighted measures and `L2` | `Measure.withDensity`, its absolute continuity and almost-everywhere rules, density integration, `memLp_two_iff_integrable_sq_norm`, and `L2.inner_def`. [Measure][DENSITY], [integration][DENSITYINT], [`L2`][L2]. | A complex-linear isometric equivalence for multiplication by `sqrt(w)` between two different `L2` measure spaces. The located `withDensitySMulLI` is an `L1`, real-linear result, not this equivalence. [Source][L1DENSITY]. |
| Pullback and conditional means | `Lp.compMeasurePreserving`; `MeasureTheory.condExpL2` with its contraction and projection properties. [Pullback][LPCOMP], [conditional expectation][CONDEXP]. | Prove the marginal identity for the explicitly weighted product, the concrete mean formula, the centered Gram identities, and additivity of the information operator for product copies. |
| Limits, products and integrals | Dominated convergence, Fubini, and `tprod_one_add_ne_zero_of_summable`. [DCT][DCT], [Fubini][FUBINI], [nonzero product][TPROD]. | Ordered stage assembly, a.e. summability, compatibility of changing weighted norms, and the final bounded-prefix construction. These are project lemmas using existing convergence theory. |

### Important representation decisions

1. **Inner products:** Mathlib is linear in the second argument. The paper is linear in the first, but its Gram entry `G_ij = ⟨v_j,v_i⟩paper` agrees with Mathlib's `Matrix.gram` entry `⟪v_i,v_j⟫`. Use that agreement; do not add an unnecessary transpose to the Gram matrix. Rewrite rank-one maps and mean vectors consistently. The paper's map `x ↦ ⟨x,v⟩paper v` becomes `x ↦ ⟪v,x⟫Mathlib v`.
2. **Norms and order:** use `EuclideanSpace`/continuous linear maps or the explicit `Matrix.Norms.L2Operator` scope for spectral estimates, and `MatrixOrder` or `PosSemidef` differences for Loewner inequalities. A plain `‖A‖` on a matrix is not a reliable specification of the intended norm.
3. **Orthogonal sums:** an ordinary product norm is a supremum norm. Use `WithLp 2`/`PiLp 2` for orthogonal sums. The block rotations in `rowsplit` and `joincopies` must be isometries for the Hilbert norm.
4. **Projections:** a basis prefix is generally an oblique idempotent, not a self-adjoint/orthogonal projection. `P_E` denotes an orthogonal projection; `P_k` denotes a coordinate prefix. Use distinct names and hypotheses. Replacing all prefix maps with `starProjection` changes the proof.
5. **Weights and equality classes:** retain ordinary measurable or continuous representatives for character-polynomial calculations, then map them into `Lp`. Weighted measures use `ℝ≥0∞` densities; track the conversion from a nonnegative real weight. Function equality, a.e. equality, and equality of `Lp` elements require different arguments.
6. **Dimension and order:** give finite families explicit ordered index sets, for example `Fin n`, and give auxiliary torus coordinates arbitrary finite types. Use disjoint sums/products of coordinate sets for new blocks, then flatten through explicit equivalences. An arbitrary enumeration of the final frequency set would not preserve a conditional Schauder basis; the append order is part of the theorem's construction.

## 4. Audit of each proof component

The workload descriptions concern formalization after choosing the representations above. “Large” identifies a substantial body of project work, not a defect in the mathematical argument.

| Paper component | Formalization assessment | Necessary decomposition or reformulation |
| --- | --- | --- |
| `basisfacts`, lines 64–104 | Manageable if specialized to the supplied Lean target. | Separate bounded Schauder bases being weakly null from the converse prefix criterion. The sequence-space completeness proof is unnecessary for a given Mathlib `SchauderBasis`, whose coordinates are already continuous. Use `exists_norm_proj_le`; construct the output through `RankOneDecomposition`. |
| `characters`, lines 106–138 | Moderate adaptation of existing analysis and algebra. | Separate integrability/continuity of the Fourier transform of an `L2` density, positive-measure uniqueness, rational-frequency density, and independence in `Lp`. Prefer the character-independence/analytic-accumulation route described below to iterated derivative and Vandermonde calculations. |
| `bochner`, lines 140–185 | A substantial standalone construction, but it can stay within existing integration and probability frameworks. | Name the triangular-window Fourier identity, positivity, Gaussian regularization, mass-one result, inversion, and limiting-measure existence. Index windows by `n+1`, so division by zero at `n=0` is absent. Use the existing Lévy tightness theorem rather than separately formalizing the sinc tail estimate. |
| `matrixfacts`, lines 197–251 | Too many distinct interfaces are combined in one lemma. | Separate Gram comparison; restriction; quotient/centering; angle concatenation; inverse variational formula; inverse compression; inverse averaging; oblique-projection norm identity; and Gram stability. The algebraic inverse identities have direct library support, while the sharp oblique and prefix statements need new lemmas. |
| `information`, lines 253–280 | A reusable project module is needed. | Define the base pullback, centered vectors, synthesis/mean maps, and their metrics. Prove marginal preservation, orthogonality, the full Gram decomposition, the normal-equation formula, the resolvent identity, and independent-block additivity separately. Restrict to the bounded functions actually used unless a general `L2` theorem is independently useful. |
| `rowsplit`, lines 300–399 | Highest technical risk. | Isolate the finite-rank two-projection decomposition; the two Gram matrices on each block; the synthesis/dual-analysis norm formula; the real-skew arrowhead identity; the block rotation/compression; and the endpoint cases. Preserve the exact error term `ε(H_jj−1)/4`; a dimension-dependent estimate would not close the later induction. |
| `joincopies`, lines 401–419 | Moderate once Hilbert block operators and oblique prefixes are established. | State the block operator explicitly and prove its norm bound as a lemma. Handle `P=0` and `P=I` separately before using equality of complementary projection norms. Specify that each prefix contains the whole initial subspace `V₀`. |
| `scalar`, lines 421–586 | Large project construction. | Split rare-set moments, inverse compression estimates, finite-exhaustion gain convergence, independent-copy parameters, the quantitative induction step, existence of arbitrarily small loss, Fejer smoothing, and exact-gain tuning. Bundle the inductive invariants, including the copy decomposition and each block's gain bound. |
| `scale`, lines 590–618 | Moderate finite arithmetic and order reasoning. | Give explicit grid stopping and crossing indices. Prove their existence and bounds before taking logarithms of ratios. Record positivity of the values appearing in those logarithms. Keep floors, ceilings, real powers, and natural indices separate. |
| `selective`, lines 620–792 | Large project construction with several changes of coordinates. | Separate scalar response bounds, the seed weight/moments, the two-dimensional eigensystem, scale choice, conditional means, projection eigenvalues, completed-column estimates, within-column estimates, centering, and amplification. Replace all unquantified asymptotic assertions by parameterized estimates or convergence statements on a chosen sequence. |
| `copies`, lines 806–860 | Moderate after the scalar and Gram interfaces exist. | State the unit-mean minimum-variance polynomial, conditional independence, the exact residual norm, independence of `α` from mass loss, the equicorrelation matrix, and the rank-one sum estimate as separate results. This makes the order of choices checkable. |
| `product`, lines 862–912 | Mostly composition once preceding modules are complete. | State a quantitative tolerance lemma for the finite sum of information operators, the small angle with `E`, and the strict distance reduction. Track pairwise distinct auxiliary modes in the construction data; this is stronger than merely distinct full characters. |
| `graph`, lines 915–947 | Moderate and well suited to the existing measure-theoretic APIs. | Separate finite-mode integer avoidance, the geometric-average formula, its a.e. limit, the double-integral identity, and extraction of one increasing subsequence for finitely many functions. A Wiener theorem is not required. |
| `stage`, lines 949–992 | Moderate after Gram stability and graph averaging. | Isolate normalization of `ν`, simultaneous entrywise Gram convergence, positivity of the limit, frequency avoidance, and selection of one index satisfying all estimates. Prove distance scaling by `m ν(ℝ)` explicitly. |
| `weighted`, lines 994–1038 | Large assembly layer, even though its analytic ingredients are standard. | Formalize the repeated rational schedule, an inductive state of ordered frequencies and weights, skipped stages, positivity of the limiting weight, compatibility of all finite prefixes, divergence of the list lengths, and construction of the final ordered sequence. Finish with Mathlib's basis constructor. |
| Main proof, lines 1040–1080 | Relatively short after the spectral and weighted-basis bridges. | Separate the reverse implication, the cyclic spectral isometry, its intertwining property, exclusion of point masses, the weighted `L2` isometry, and basis transport. The isometry from equal Gram data must be well defined without assuming independence before atomlessness has been proved. |

### Statements currently too compressed for a dependable Lean interface

The paper's named lemmas provide a useful dependency order, but several sentences contain entire supporting developments:

- **“The Gram matrices of the range vectors and their dual vectors are…”** requires explicit synthesis maps, coefficient spaces, dual vectors, and the relation between coordinate operators and the displayed matrices.
- **“As `Y` exhausts all characters…”** needs an increasing finite exhaustion, density in the relevant weighted Hilbert norm, and a theorem about convergence of inverse-compression quadratic forms. Entrywise convergence of fixed-size matrices does not establish this changing-dimension limit.
- **“Undoing the change to orthonormal row coordinates…”** needs a chosen invertible coordinate map, the congruence formula for the Gram matrix, and the inverse congruence formula. The matrix of the inverse metric transforms differently from the metric itself.
- **“For sufficiently small ε…”** in the directional construction simultaneously changes the scalar packet, its dimension, `L`, the response function, and the selected scale. There is no single fixed matrix-valued function of ε whose continuity may simply be invoked.
- **“Take independent copies”** means placing explicitly given finite character systems in disjoint coordinates and using a product density. The embeddings, integrability, marginal formula, and mode distinctions must be stated, not inferred from terminology.
- **“Pass the prefix bound to the limit”** refers to the same finite formal coefficient vectors evaluated under changing weights, not to a sequence of operators acting on one automatically identical `Lp` type.

These should become named mathematical intermediates before implementation. They are not solved by tactic selection.

## 5. Concrete changes that reduce the required infrastructure

### 5.1 Use Mathlib's basis interface from the outset

The supplied target already quantifies over a `SchauderBasis ℂ H`. For the reverse implication, use its continuous coordinate functionals and existing partial-sum convergence. Retain the paper's Hilbert-duality proof of weak nullity; there is no need to formalize the auxiliary Banach space of all convergent coefficient sequences merely to recover properties already present in the target's basis structure.

For the construction direction, build bounded prefix operators `P_n` with:

- `P_0=0`, range dimension `n`, and `P_n P_m=P_min(n,m)`;
- `P_n x → x` for every `x`;
- the actual desired exponential `e_n` nonzero and in the range of `P_(n+1)−P_n`.

These are exactly the inputs to `SchauderBasis.RankOneDecomposition.basis`. Its `basis_coe` theorem retains the specified vectors; it does not replace them by an unrelated Hilbert basis. [Constructor][BASISBUILD]. A separate transport lemma can send a basis through a linear isometry equivalence by composing its coordinates with the inverse. No new general Schauder theory is required, but the prefix-construction adapter is still real work.

### 5.2 Use a prefix-bound predicate rather than an exact finite basis constant

For a finite ordered family `v_0,…,v_(d−1)`, define the required assertion by

$$
  \left\|\sum_{i<k} c_i v_i\right\|
  \le K\left\|\sum_{i<d} c_i v_i\right\|
  \qquad(k\le d,\ c\in\mathbb C^d).
$$

For Gram matrix `G`, the equivalent statement is the Loewner inequality `D_kᴴ G D_k ≤ K² G`. This uses existing matrices and positivity, and avoids constructing a separate normed-space instance for every Gram metric or defining an optimal constant as a supremum. Prove comparison, restriction, centering, and concatenation directly for this predicate.

For the transfer step, use relative Gram inequalities

$$
 (1-\eta)G\le G_n\le(1+\eta)G,\qquad 0<\eta<1,
$$

to get a prefix bound multiplied by `sqrt((1+η)/(1−η))`. This is enough for a prescribed positive tolerance. It avoids a standalone continuity theorem for the *optimal* basis constant. Squared distance can still use its finite Schur-complement formula and `continuousAt_matrix_inv`, with invertibility proved first. [Matrix inverse continuity][INVERSECONT].

### 5.3 Replace the Vandermonde route by character independence and an accumulation point

A route using existing results is:

1. Regard `x ↦ exp(2πitx)` as a monoid homomorphism from `Multiplicative ℝ` to `ℂ`. Distinct frequencies give distinct homomorphisms; for unequal `s,t`, evaluating their ratio at `1/(2(s−t))` distinguishes them.
2. Apply `linearIndependent_monoidHom` to get pointwise linear independence. This theorem is for arbitrary suitable monoids; the finite-group-only additive-character result is not the right interface. [Source][CHARINDEP].
3. If a nonzero finite exponential sum vanished a.e. under a nonzero singleton-null measure, its zero set would have positive measure. Use `exists_accPt_of_nullSingletonClass` to obtain an accumulation point. Its separability hypothesis holds for a subset of the real line. [Source][ACCPOINT].
4. The sum is real analytic with complex values. Apply `AnalyticOnNhd.eqOn_zero_of_preconnected_of_frequently_eq_zero` on the real line to show that it vanishes everywhere, contradicting pointwise independence. [Source][ANALYTIC].

This avoids building a specialized iterated-derivative formula, a Vandermonde calculation, and an explicit countable coding of zeros. Analyticity of the exponential sum and the conversion from the accumulation-point statement to frequent vanishing still need ordinary bridging lemmas.

### 5.4 Specialize the spectral-measure construction to the orbit coefficient if useful

No directly applicable Bochner representation theorem was located in the inspected Mathlib revision. The paper's route is viable, but its general positive-definite-function statement is stronger than the application requires.

For `φ(t)=⟨U_t v,v⟩paper`, define the triangular-window density as in the paper. Positivity can be proved by the identity

$$
 q_T(x)=\frac1T\left\|\int_0^T e^{-2\pi ixs}U_s v\,ds\right\|^2.
$$

The orbit integral exists because of strong continuity on a compact interval. The norm-square identity uses Fubini and integration against continuous linear functionals; Mathlib has `integral_inner`. [Source][INTEGRALINNER]. This avoids a new general positive-definite-kernel framework and the positivity-via-Riemann-sums argument. The triangular-window change-of-variables identity remains an explicit lemma to prove.

Keep the Gaussian regularization and Fourier inversion, verifying `L1` hypotheses before using inversion. Represent the nonnegative density by a real-valued function, or prove that the complex Fourier expression is real before applying `ENNReal.ofReal`.

After obtaining probabilities with characteristic functions tending pointwise to the appropriately rescaled `φ`, invoke `MeasureTheory.isTightMeasureSet_of_tendsto_charFun`. It assumes continuity at zero and pointwise convergence, exactly the information available here. This removes the separate sinc tail-estimate development. [Source][LEVY]. Then use Prokhorov compactness and a cluster point, testing against bounded continuous characters. A filter/cluster-point proof avoids constructing an explicit subnet.

The theorem `ProbabilityMeasure.tendsto_of_tendsto_charFun` should **not** be used to conjure the limiting measure: its conclusion is convergence to an already supplied `μ₀`, and its hypothesis contains `charFun μ₀`. The tightness theorem plus compactness is the existence route.

### 5.5 Keep conditional means as explicit fiber integrals

The paper already made a useful choice by writing the mean as `M⁻¹ ∫ u(s,y)W(s,y) dy`. Keep this for the bounded character-polynomial functions used in the construction. Prove the constant-marginal identity first; then pull base functions into the weighted product space using the measure-preserving first-coordinate map and `Lp.compMeasurePreserving`. [Source][LPCOMP].

Mathlib has genuine conditional expectation in `L2`, so conditional expectation is not a missing foundational concept. [Source][CONDEXP]. Identifying that abstract object with this particular weighted fiber formula would introduce extra sub-sigma-algebra and a.e. bookkeeping. It is unnecessary if all required Gram and mean identities are proved directly by Fubini.

Put all information operators on the same explicitly declared base space. For spectral calculations, restrict to the finite-dimensional span containing the old family, the residual, and all mean vectors involved. The operators vanish on the orthogonal complement. This avoids pretending that a finite-dimensional diagonalization theorem applies directly to the whole infinite-dimensional `L2` space.

### 5.6 Avoid a general completed tensor-product development

Mathlib has an inner-product tensor product and bounded maps on it; it would be incorrect to report tensor products as entirely absent. However, adjoint results such as `TensorProduct.adjoint_mapL` explicitly require completeness of the relevant tensor spaces. [Source][TENSOR].

For the particular space written `ℂ^(d+1) ⊗ L2(T)` in `rowsplit`, use finite Hilbert-valued tuples, with squared norm equal to the sum of component squared norms. Define the action of the finite matrix and of multiplication by the indicator componentwise. Then the formula for the Gram operator and its inverse reduces to the two pointwise cases inside and outside the rare set.

The two-projection calculation can be restricted to the finite-dimensional invariant space `range(Π) + M_D(range(Π))`; on its orthogonal complement `Π=0`. Use `WithLp 2` decompositions and finite-dimensional spectral theory. This avoids developing a general theorem for two arbitrary infinite-rank projections, while still requiring the finite-rank decomposition and sharp norm calculation actually used.

### 5.7 Give scalar packets and their operations explicit contracts

An implementation needs a small number of coherent project definitions rather than repeatedly assembling unrelated existential witnesses. A scalar packet should carry:

- a finite auxiliary-coordinate type and an ordered finite list of distinct nonzero character modes;
- a measurable even weight, an explicit positive lower bound, and an upper bound of one;
- its mass and augmented/centered Gram data;
- gain and prefix-bound assertions;
- the two inverse estimates needed in the induction;
- when relevant, a decomposition into independent blocks and a bound on each block's gain.

Distinguish a measurable packet from a polynomial packet. The rare-set activation uses an indicator and is generally not a trigonometric polynomial. Polynomiality is obtained only after smoothing. Conversely, the later graph transfer needs finite Fourier support, not merely a bounded measurable weight.

Specify independent operations for rare-set activation, finite character truncation, independent replication, smoothing, and affine tuning. Each operation should return its new packet together with its parameter formulas. For the rare set, use an explicit symmetric arc in the circle and normalized Haar interval calculations; do not introduce a general theorem on divisibility of atomless measures just to choose this set.

The induction needs the gain-loss condition `z_p ≤ Z₀·2^(−n−3)` exactly as corrected in Prompt 1. Carry the fact that the present packet is assembled from independent small-gain blocks: the next augmented-prefix bound uses this stronger invariant, not just the total gain. Also give the positive-real and integer versions of `L=floor(Z/z)` separate names and prove `L≥1` before using finite copies.

### 5.8 Prove only the finite Fejer facts that the construction uses

No dedicated Fejer-kernel package was located in the scanned source. This does not force a general approximate-identity theory. Define the finite one-dimensional kernel directly by the squared norm of a geometric sum, normalize it, and use existing character orthogonality to prove:

1. positivity, evenness, and integral one;
2. finite Fourier support and the exact coefficient multiplier;
3. convergence of each fixed multiplier to one;
4. the finite-product version by Fubini;
5. the displayed diagonal-unitary averaging formula for each fixed Gram matrix.

This is enough for `scalar`. Neither uniform convergence of all Fourier series nor convergence of the weight in a stronger norm is needed. Matrix positivity under averaging can be proved by evaluating quadratic forms and integrating; inverse averaging can use the paper's variational argument. The existing operator-convexity theorem is immediately useful for the final two-point affine tuning, while an integral Jensen adapter would still need integrability and a uniform positive lower bound.

The inverse-convexity declaration assumes a `CStarAlgebra` with the stated order structures. Apply it to complex matrices with the Hilbert operator norm and the matching order; a real-matrix calculation needs an explicit change of scalars or the direct finite variational proof. Also identify its `Ring.inverse` with the chosen nonsingular matrix inverse under proved invertibility. The availability of the abstract theorem does not eliminate these type-level bridges.

### 5.9 Make the directional asymptotics uniform in the changing packet

For fixed target vector `e`, choose a sequence of scalar packets with losses `ε_n → 0`. Their sizes may change. The response functions are therefore `Φ_n`, each attached to its own finite matrix. State bounds such as `Φ_n(ε_n²) ≥ c`, `Φ_n(sqrt(ε_n)) ≤ sqrt(ε_n)`, and the ratio estimate uniformly in the packet. Do not assume that a chosen packet depends continuously on its loss.

Keep `e` and `κ` fixed while `L_n` grows. Prove explicit upper and lower bounds relating `R_n=1/γ_n` to `L_n`, and use them to establish the logarithmic hypothesis of `scale`. State the estimates for `m_n`, `Φ_*`, `λ_n`, the perpendicular leakage, and loss divided by `λ_n` separately. Then amplification by `ceil(σ/λ_n)` is a numerical lemma with proved `λ_n>0`.

Keep the within-column estimate as a separate theorem. A completed-column bound is insufficient for a Schauder basis. This is one of the reasons the directional construction cannot be replaced by a short invocation of an existing projection theorem.

The residual-copy choices also need their order stated explicitly: fix the residual coefficients and gain; compute `α` and the number of copies from their exact norm formula; only then choose the scalar mass losses. This prevents a circular dependence of the mass budget on the number of packets.

### 5.10 Keep the averaged graph argument and isolate its finite selections

The existing proof is preferable to importing a general Wiener theorem. It only needs the explicitly bounded geometric averages and dominated convergence on a product measure. `Set.Countable.measure_zero` supplies the null exceptional fibers once the measure is a `NullSingletonClass`. [Source][NULLPOINTS].

Useful standalone conclusions are:

- a finite set of nonzero integer linear forms admits the displayed integer direction avoiding their zeros;
- for nonzero integer slope `l` and `g ∈ L1(μ)`, the mean squared Fourier coefficients tend to zero;
- finitely many such mean-square limits yield one strictly increasing selection of indices;
- affine frequency functions with distinct nonzero slopes eventually avoid all old frequencies and each other.

Do not substitute Mathlib's Riemann–Lebesgue theorem here: the measure in the target may be singular, and lack of point masses does not justify pointwise Fourier decay. A mean-ergodic theorem exists, but using it would require additional multiplication-operator and fixed-space identifications; it does not obviously simplify this direct scalar-integral argument. [Existing mean-ergodic theorem][ERGODIC].

### 5.11 Assemble the limiting basis without identifying different `Lp` types

Store each stage's ordered rational frequency list and its weight as ordinary data. Express all stage estimates on finite formal linear combinations. During induction, a list either appends a block or remains unchanged, so distinguish the stage number from the number of basis vectors already selected.

Prove that the lists are compatible and their lengths tend to infinity. Define the final sequence using this compatibility, proving that each old list is literally an initial segment. This gives injective frequencies and preserves the prefix bounds. A mere countable enumeration of the union is not enough.

The a.e. positive-product argument can reuse `multipliable_one_add_of_summable` and `tprod_one_add_ne_zero_of_summable` with `f_n=V_n−1`. Positivity of finite products and their limit then gives a positive product; connect the unordered product's existence to the natural ordered partial products. [Source][TPROD]. Alternatively, retain the paper's elementary logarithm proof as one local lemma. The preceding a.e. summability and subsequent dominated convergence are required in either route.

Pass finite quadratic-form inequalities to the limiting weight using bounded representatives and `L1` convergence. Only after this passage should the final continuous prefix operators be constructed on `L2(wμ)`, followed by `RankOneDecomposition.basis`.

### 5.12 Treat the weighted isometry as a dedicated adapter

Prove the complex-linear isometric equivalence

$$
 L^2(w\mu)\longrightarrow L^2(\mu),\qquad F\longmapsto\sqrt w\,F,
$$

using density integration and the `MemLp` squared-norm characterization. Prove measurability and a.e. well-definedness, the norm identity, linearity, and surjectivity in separate steps. For the inverse, define division by `sqrt(w)` only on the positive set and choose any value on its null complement.

The limiting weight need not be bounded away from zero. Therefore `1/sqrt(w)` must not be assumed to be an `L∞` multiplier on `L2(μ)`. It is integrable in the required *weighted* squared norm, which is what makes the inverse well defined. The finite-packet equivalent-norm arguments do not automatically apply to this limiting weight.

For the cyclic spectral isometry, first descend equal Gram data to an isometry between the two algebraic spans and then use the existing dense extension machinery, such as `LinearEquiv.extendOfIsometry`. [Source][EXTEND]. Do not assume exponential independence at this point: the spectral measure is not known to be singleton-null until after the intertwining map has been constructed.

### 5.13 Specialize quantitative conclusions only where the main theorem permits it

`thm:main` requires existence of a Schauder basis, not a basis constant arbitrarily close to one. A formalization may first prove the weighted theorem for one fixed uniform bound, for example a bound below two, fixing `u=1/100` and summable error tolerances. This removes an outer parameter and some numerical generality.

It does not remove the need for controlled prefixes, arbitrarily small mass losses, selective capture, or a bound that survives all stages. Replacing the sharp intermediate estimates by arbitrary dimension-dependent constants would leave the infinite construction unsupported. Treat specialization as a reduction of parameter bookkeeping, not as a substitute for the central construction.

## 6. Missing interfaces and work that cannot be claimed as a library call

The following are the main missing or insufficiently packaged interfaces in the inspected Mathlib source. Their names here describe proposed results, not existing Lean declarations.

| Needed interface | Minimum content | Scope of development |
| --- | --- | --- |
| Finite ordered weighted family | Explicit representatives and frequencies, Gram matrices, prefix inequalities, normalization, restriction, and concatenation. | A substantial reusable project layer. Uses existing matrices, measures, and finite indexing. |
| Sharp oblique-projection calculus | `‖P‖²=1+‖P−P*‖²`, complementary projections, weighted row cuts, skew-arrowhead norm comparison, finite-rank two-projection decomposition. | The most demanding reusable linear-algebra module. Existing orthogonal projection and spectral APIs are supporting tools. |
| Finite inverse-exhaustion lemma | Convergence of a distinguished inverse-compression quadratic form along increasing dense finite spaces with a common coercive bound. | A genuine analytic bridge. Fixed-size matrix inverse continuity alone is insufficient. |
| Scalar packet engine | Activation, independent copies, invariant preservation, arbitrarily small loss, finite smoothing, and exact-gain tuning. | A large construction assembled from new project lemmas. |
| Directional packet engine | Seed moments and eigensystem, response selection, partial-column bounds, centering, and amplification. | A large construction with explicit quantitative interfaces. |
| Weighted product/mean interface | Marginal preservation, base pullback, centered Gram decomposition, information operator and conditional-copy addition. | Moderate to substantial reusable project work; a new disintegration theory is avoidable. |
| Ordered infinite assembly | Compatible finite lists, repeated targets, positive limiting weight, persistent prefixes, and basis construction. | Substantial assembly work, using existing convergence and Schauder infrastructure. |
| Spectral and weighted adapters | Orbit-specific scalar measure, equal-Gram span isometry, intertwining, point-mass exclusion, and weighted `L2` equivalence. | A separate sizeable module; it can avoid a general spectral theorem for unbounded generators. |

Several small definitions are unavoidable and reasonable: a mixed-domain character polynomial, a finite prefix-bound predicate, scalar-packet data, and an inductive extension state. Their *definitions* are not major foundational obstacles. The cost lies in the quantified interfaces and proofs connecting them.

### Alternatives investigated

| Alternative | Assessment |
| --- | --- |
| Use finite-dimensional spectral theory for every spectral assertion | Good for the finite matrices and finite-rank information operators. It does not supply the cyclic representation of an arbitrary strongly continuous unitary group. Restrict finite-rank calculations to an explicit finite-dimensional invariant space. |
| Use Gelfand duality or GNS as a replacement for the spectral-measure construction | These frameworks are present. [Gelfand duality][GELFAND], [GNS][GNS]. They do not directly produce the required probability on `ℝ` and intertwining with `e_t` from the given strongly continuous group. One would still need the relevant commutative algebra, identification of characters with real frequencies, a representation/multiplicity argument, and continuity/support bookkeeping. No evidence was found that this is a smaller Mathlib-only route. The inspected GNS file also explicitly lists a cyclic-vector construction as a TODO. |
| Use the circle Fourier basis directly | It supplies the auxiliary torus density facts. It does not give an exponential Schauder basis for an arbitrary singular probability on the real line, nor the required orbit basis in the original Hilbert space. |
| Apply Gram–Schmidt to the orbit | Linear combinations of orbit elements need not themselves be orbit elements. This changes the required conclusion and is not an acceptable shortcut. |
| Replace ordered prefix bounds by control of whole blocks | Insufficient. The chosen exponential sequence is generally conditional, and the proof must control cuts within a block. |
| Use general conditional expectation or a completed tensor-product framework everywhere | Available pieces exist, but the explicit product-integral and finite-tuple representations above are narrower and avoid unnecessary identifications. |
| Use scalar convexity for matrix inversion | Invalid without the operator-order statement. Mathlib supplies actual operator inverse convexity, which is the relevant theorem. Its integral version still needs a justified adapter. |
| Reuse the FLT Lean development | Excluded by the user's follow-up instruction. No part of this audit's proposed implementation depends on it. |

## 7. Specific corrections and precision requirements for the paper

These are recommendations for a subsequent edit; Prompt 2 requests an audit, so the TeX and its PDF were left unchanged.

1. **Fix a literal TeX typo at line 653.** The third inequality in `responsebounds` ends with `}quad(` rather than the command `}\quad(`. The intended spacing command has lost its backslash. This can compile while printing the letters `quad` as mathematical symbols. It should be corrected before using the display as a formal specification.
2. **State the meaning of positivity for complex expressions.** In the positive-definite-function and matrix statements, make explicit whether an expression is real and nonnegative or whether its real part is being compared. Lean's complex order is not a total ordered-field structure.
3. **Name the weighted Hilbert metrics on every matrix identity.** Reference-row Gram matrices, centered Gram matrices, normalized measures, and unnormalized measures coexist. Write the source and target of synthesis and coefficient-extraction maps, and make normalization factors explicit.
4. **Replace informal asymptotic comparisons with quantified bounds.** In particular, record the hypotheses and constants behind `R ≍ L`, `m=o(ε^(1/4))`, concentration of the small eigenspace, and the three limits for `λ`. Their dependence on fixed versus varying parameters matters.
5. **Give explicit ordered finite exhaustions and stage compatibility.** The rare-set exhaustion and the final frequency enumeration are different constructions. Neither should be represented by an unspecified enumeration when proving prefix properties.
6. **Keep all nonzero and endpoint cases visible.** These include `T>0`, positive scalar mass/gain, nonzero residual, nonempty old family, `D=0` for graph averaging, `P=0,I` for projections, `a₀=0` in row splitting, and skipped target stages. Most are handled in the prose but should become hypotheses or branches of the intermediate lemmas.
7. **Use the exact singleton-null assumption.** The paper defines atomlessness as vanishing on singletons. Current Mathlib's `NullSingletonClass` matches it directly; imposing `NoAtoms` everywhere would introduce an unnecessary equivalence proof and could accidentally change intermediate theorem hypotheses on more general spaces.
8. **Separate spectral-measure existence from spectral-measure uniqueness.** `ext_of_charFun` is a uniqueness theorem. It cannot replace `bochner`. Similarly, the convergence theorem with a specified limiting probability cannot be used before that probability exists.
9. **Make strictness margins explicit.** The final stage selection requires simultaneous strict inequalities. Record which constants are fixed, which limits have strict slack, and a single common index satisfying the finitely many conditions. Avoid re-selecting different indices for different Gram entries or frequency constraints.

The typo is a concrete source defect. The remaining items are statement/interface improvements for formalization, not newly established counterexamples to the mathematical argument.

## 8. Recommended implementation order and acceptance checks

| Stage | Deliverable | Acceptance check before proceeding |
| --- | --- | --- |
| 1 | Pin the toolchain; agree on inner-product, matrix-order, norm, weight, and finite-index conventions. | One finite Gram/prefix example and one weighted integral identity use the intended types and norms. This audit did not perform those Lean checks. |
| 2 | Basis and finite-family adapters. | The reverse implication of `MainResult`; a generic construction of a Mathlib Schauder basis from uniform ordered prefixes; transport through an isometry. |
| 3 | The difficult matrix module. | Prove the oblique projection identity, inverse compression/exhaustion, and the exact row-splitting bound with constants independent of dimension. This is the main feasibility checkpoint. |
| 4 | Scalar supply. | Build actual measurable packets, preserve the copy/gain invariants, obtain loss tending to zero, and turn them into polynomial packets with prescribed gain. |
| 5 | Directional and product extension. | Prove every within-column prefix estimate and the frequency-mode conditions, then obtain one product-space extension. |
| 6 | Graph transfer and infinite assembly. | Transfer one extension to distinct rational frequencies; construct a positive limiting weight; retain ordered prefix bounds and instantiate the existing basis constructor. |
| 7 | Spectral and weighted bridges; final theorem. | Construct the scalar measure and intertwiner, exclude point masses, prove the `sqrt(w)` equivalence, and obtain the exact `Showcase.lean` statement. |

A successful formalization of the foundational APIs alone would not discharge stages 3–6. Conversely, the absence of a prepackaged weighted-basis theorem does not indicate a need for new foundational mathematics: the paper provides the strategy, and the audit identifies where its derived arguments must become a project library.

**Final assessment:** proceed only with the expectation of a substantial Mathlib-only formalization project. The proposed reformulations reduce avoidable general infrastructure and clarify the interfaces, but the present audit does not establish that the whole proof can be formalized without substantial new auxiliary development. No claimed shortcut removes the scalar and directional construction while preserving the target theorem.

## 9. Pinned source references

Each Mathlib reference below points to an actual inspected source location at the November revision. These are evidence for available building blocks, not claims that the complete paper has already been formalized there.

[BASIS]: https://github.com/leanprover-community/mathlib4/blob/1ddfaa9548e05b343be9248ae08b73c3425b446e/Mathlib/Analysis/Normed/Module/Bases.lean#L104
[BASISBUILD]: https://github.com/leanprover-community/mathlib4/blob/1ddfaa9548e05b343be9248ae08b73c3425b446e/Mathlib/Analysis/Normed/Module/Bases.lean#L464
[GRAM]: https://github.com/leanprover-community/mathlib4/blob/1ddfaa9548e05b343be9248ae08b73c3425b446e/Mathlib/Analysis/InnerProductSpace/GramMatrix.lean#L40
[ENTRYNORM]: https://github.com/leanprover-community/mathlib4/blob/1ddfaa9548e05b343be9248ae08b73c3425b446e/Mathlib/Analysis/Matrix/Normed.lean#L84
[L2NORM]: https://github.com/leanprover-community/mathlib4/blob/1ddfaa9548e05b343be9248ae08b73c3425b446e/Mathlib/Analysis/CStarAlgebra/Matrix.lean#L195
[MATRIXORDER]: https://github.com/leanprover-community/mathlib4/blob/1ddfaa9548e05b343be9248ae08b73c3425b446e/Mathlib/Analysis/Matrix/Order.lean#L54
[SCHUR]: https://github.com/leanprover-community/mathlib4/blob/1ddfaa9548e05b343be9248ae08b73c3425b446e/Mathlib/LinearAlgebra/Matrix/PosDef.lean#L698
[WOODBURY]: https://github.com/leanprover-community/mathlib4/blob/1ddfaa9548e05b343be9248ae08b73c3425b446e/Mathlib/LinearAlgebra/Matrix/NonsingularInverse.lean#L616
[INVCONVEX]: https://github.com/leanprover-community/mathlib4/blob/1ddfaa9548e05b343be9248ae08b73c3425b446e/Mathlib/Analysis/SpecialFunctions/ContinuousFunctionalCalculus/Rpow/RingInverseOrder.lean#L36
[INVORDER]: https://github.com/leanprover-community/mathlib4/blob/1ddfaa9548e05b343be9248ae08b73c3425b446e/Mathlib/Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Order.lean#L413
[INVERSECONT]: https://github.com/leanprover-community/mathlib4/blob/1ddfaa9548e05b343be9248ae08b73c3425b446e/Mathlib/Topology/Instances/Matrix.lean#L246
[PROD]: https://github.com/leanprover-community/mathlib4/blob/1ddfaa9548e05b343be9248ae08b73c3425b446e/Mathlib/Analysis/InnerProductSpace/ProdL2.lean#L88
[EXTEND]: https://github.com/leanprover-community/mathlib4/blob/1ddfaa9548e05b343be9248ae08b73c3425b446e/Mathlib/Analysis/Normed/Operator/Extend.lean#L305
[FOURIER1]: https://github.com/leanprover-community/mathlib4/blob/1ddfaa9548e05b343be9248ae08b73c3425b446e/Mathlib/Analysis/Fourier/AddCircle.lean#L259
[FOURIERMULTI]: https://github.com/leanprover-community/mathlib4/blob/1ddfaa9548e05b343be9248ae08b73c3425b446e/Mathlib/Analysis/Fourier/AddCircleMulti.lean#L53
[CHARPOLY]: https://github.com/leanprover-community/mathlib4/blob/1ddfaa9548e05b343be9248ae08b73c3425b446e/Mathlib/Analysis/Fourier/BoundedContinuousFunctionChar.lean#L115
[CHARUNIQUE]: https://github.com/leanprover-community/mathlib4/blob/1ddfaa9548e05b343be9248ae08b73c3425b446e/Mathlib/MeasureTheory/Measure/CharacteristicFunction/Basic.lean#L256
[LEVY]: https://github.com/leanprover-community/mathlib4/blob/1ddfaa9548e05b343be9248ae08b73c3425b446e/Mathlib/MeasureTheory/Measure/LevyConvergence.lean#L43
[PROKHOROV]: https://github.com/leanprover-community/mathlib4/blob/1ddfaa9548e05b343be9248ae08b73c3425b446e/Mathlib/MeasureTheory/Measure/Prokhorov.lean#L553
[WEAKPROB]: https://github.com/leanprover-community/mathlib4/blob/1ddfaa9548e05b343be9248ae08b73c3425b446e/Mathlib/MeasureTheory/Measure/ProbabilityMeasure.lean#L374
[FOURIERINV]: https://github.com/leanprover-community/mathlib4/blob/1ddfaa9548e05b343be9248ae08b73c3425b446e/Mathlib/Analysis/Fourier/Inversion.lean#L175
[GAUSSIAN]: https://github.com/leanprover-community/mathlib4/blob/1ddfaa9548e05b343be9248ae08b73c3425b446e/Mathlib/Analysis/SpecialFunctions/Gaussian/FourierTransform.lean#L227
[NULLPOINTS]: https://github.com/leanprover-community/mathlib4/blob/1ddfaa9548e05b343be9248ae08b73c3425b446e/Mathlib/MeasureTheory/Measure/Typeclasses/NullSingletonClass.lean#L28
[ACCPOINT]: https://github.com/leanprover-community/mathlib4/blob/1ddfaa9548e05b343be9248ae08b73c3425b446e/Mathlib/MeasureTheory/Measure/Typeclasses/NullSingletonClass.lean#L88
[NOATOMS]: https://github.com/leanprover-community/mathlib4/blob/1ddfaa9548e05b343be9248ae08b73c3425b446e/Mathlib/MeasureTheory/Measure/Typeclasses/NoAtoms.lean#L93
[ANALYTIC]: https://github.com/leanprover-community/mathlib4/blob/1ddfaa9548e05b343be9248ae08b73c3425b446e/Mathlib/Analysis/Analytic/IsolatedZeros.lean#L210
[CHARINDEP]: https://github.com/leanprover-community/mathlib4/blob/1ddfaa9548e05b343be9248ae08b73c3425b446e/Mathlib/LinearAlgebra/LinearIndependent/Basic.lean#L516
[DENSITY]: https://github.com/leanprover-community/mathlib4/blob/1ddfaa9548e05b343be9248ae08b73c3425b446e/Mathlib/MeasureTheory/Measure/WithDensity.lean#L313
[DENSITYINT]: https://github.com/leanprover-community/mathlib4/blob/1ddfaa9548e05b343be9248ae08b73c3425b446e/Mathlib/MeasureTheory/Integral/Bochner/ContinuousLinearMap.lean#L251
[L2]: https://github.com/leanprover-community/mathlib4/blob/1ddfaa9548e05b343be9248ae08b73c3425b446e/Mathlib/MeasureTheory/Function/L2Space.lean#L45
[INTEGRALINNER]: https://github.com/leanprover-community/mathlib4/blob/1ddfaa9548e05b343be9248ae08b73c3425b446e/Mathlib/MeasureTheory/Function/L2Space.lean#L89
[LPCOMP]: https://github.com/leanprover-community/mathlib4/blob/1ddfaa9548e05b343be9248ae08b73c3425b446e/Mathlib/MeasureTheory/Function/LpSpace/Basic.lean#L642
[CONDEXP]: https://github.com/leanprover-community/mathlib4/blob/1ddfaa9548e05b343be9248ae08b73c3425b446e/Mathlib/MeasureTheory/Function/ConditionalExpectation/CondexpL2.lean#L67
[TPROD]: https://github.com/leanprover-community/mathlib4/blob/1ddfaa9548e05b343be9248ae08b73c3425b446e/Mathlib/Analysis/SpecialFunctions/Log/Summable.lean#L213
[DCT]: https://github.com/leanprover-community/mathlib4/blob/1ddfaa9548e05b343be9248ae08b73c3425b446e/Mathlib/MeasureTheory/Integral/DominatedConvergence.lean#L57
[FUBINI]: https://github.com/leanprover-community/mathlib4/blob/1ddfaa9548e05b343be9248ae08b73c3425b446e/Mathlib/MeasureTheory/Integral/Prod.lean#L443
[GNS]: https://github.com/leanprover-community/mathlib4/blob/1ddfaa9548e05b343be9248ae08b73c3425b446e/Mathlib/Analysis/CStarAlgebra/GelfandNaimarkSegal.lean#L30
[GELFAND]: https://github.com/leanprover-community/mathlib4/blob/1ddfaa9548e05b343be9248ae08b73c3425b446e/Mathlib/Analysis/CStarAlgebra/GelfandDuality.lean#L43
[ERGODIC]: https://github.com/leanprover-community/mathlib4/blob/1ddfaa9548e05b343be9248ae08b73c3425b446e/Mathlib/Analysis/InnerProductSpace/MeanErgodic.lean#L89
[TENSOR]: https://github.com/leanprover-community/mathlib4/blob/1ddfaa9548e05b343be9248ae08b73c3425b446e/Mathlib/Analysis/InnerProductSpace/TensorProduct.lean#L706
[RAYLEIGH]: https://github.com/leanprover-community/mathlib4/blob/1ddfaa9548e05b343be9248ae08b73c3425b446e/Mathlib/Analysis/InnerProductSpace/Rayleigh.lean#L120
[L1DENSITY]: https://github.com/leanprover-community/mathlib4/blob/1ddfaa9548e05b343be9248ae08b73c3425b446e/Mathlib/MeasureTheory/Function/L1Space/Integrable.lean#L887

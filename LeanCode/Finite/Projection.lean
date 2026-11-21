import LeanCode.Finite.Families

/-! Norm estimates for oblique prefix projections and joining centered blocks. -/

open Matrix ContinuousLinearMap Submodule
open scoped BigOperators InnerProductSpace InnerProduct ComplexOrder MatrixOrder Matrix.Norms.L2Operator
noncomputable section
namespace SchauderBasisOrbits

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

omit [CompleteSpace H] in
private theorem opNorm_le_of_sq_apply (A : H →L[𝕜] H) {r : ℝ} (hr : 0 ≤ r)
    (h : ∀ x : H, ‖A x‖ ^ 2 ≤ r * ‖x‖ ^ 2) : ‖A‖ ^ 2 ≤ r := by
  have hu : ‖A‖ ≤ Real.sqrt r := A.opNorm_le_bound (Real.sqrt_nonneg _) fun x ↦ by
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
    simpa only [mul_pow, Real.sq_sqrt hr] using h x
  simpa only [Real.sq_sqrt hr] using pow_le_pow_left₀ (norm_nonneg _) hu 2

/-- Norm formula for an oblique idempotent on a complete Hilbert space. -/
theorem norm_sq_idempotent_eq_one_add_skew_sq (P : H →L[𝕜] H) (hP : IsIdempotentElem P)
    (hP0 : P ≠ 0) : ‖P‖ ^ 2 = 1 + ‖P - P†‖ ^ 2 := by
  let E := P.range
  let _ : E.HasOrthogonalProjection := hP.hasOrthogonalProjection_range
  let Q := E.starProjection
  let A := P - Q
  have hQstar : star Q = Q := (isSelfAdjoint_starProjection E).star_eq
  have hQidem : Q * Q = Q := E.isIdempotentElem_starProjection.eq
  have hPQ : P * Q = Q := by
    ext x
    have hx : Q x ∈ P.range := E.starProjection_apply_mem x
    obtain ⟨y, hy⟩ := hx
    change P (Q x) = Q x
    rw [← hy]
    exact DFunLike.congr_fun hP.eq y
  have hQP : Q * P = P := by
    ext x
    exact Submodule.starProjection_eq_self_iff.mpr (show P x ∈ E from ⟨x, rfl⟩)
  have hAQ : A * Q = 0 := by
    change (P - Q) * Q = 0
    rw [sub_mul, hPQ, hQidem, sub_self]
  have hQA : Q * A = A := by
    change Q * (P - Q) = P - Q
    rw [mul_sub, hQP, hQidem]
  have hQAstar : Q * star A = 0 := by
    simpa only [star_mul, hQstar, star_zero] using congrArg star hAQ
  have hAstarQ : star A * Q = star A := by
    simpa only [star_mul, hQstar] using congrArg star hQA
  have normStar (L : H →L[𝕜] H) : ‖star L‖ = ‖L‖ := by
    rw [star_eq_adjoint, LinearIsometryEquiv.norm_map]
  have hPdecomp : P = Q + A := by dsimp [A]; abel
  have hPstar : star P = Q + star A := by rw [hPdecomp, star_add, hQstar]
  have hPstarQ (x : H) : (star P) (Q x) = Q x + (star A) x := by
    change ((star P) * Q) x = _
    rw [hPstar, add_mul, hQidem, hAstarQ, add_apply]
  have hQcontract (x : H) : ‖Q x‖ ≤ ‖x‖ := E.norm_starProjection_apply_le x
  have hPy (x : H) :
      ‖(star P) (Q x)‖ ^ 2 = ‖Q x‖ ^ 2 + ‖(star A) x‖ ^ 2 := by
    have h := E.norm_sq_eq_add_norm_sq_starProjection ((star P) (Q x))
    rw [Submodule.starProjection_orthogonal_val] at h
    change _ = ‖Q ((star P) (Q x))‖ ^ 2 + ‖(star P) (Q x) - Q ((star P) (Q x))‖ ^ 2 at h
    have hQPy : Q ((star P) (Q x)) = Q x := by
      rw [hPstarQ, map_add]
      change (Q * Q) x + (Q * star A) x = Q x
      simp only [hQidem, hQAstar, zero_apply, add_zero]
    have hDiff : (star P) (Q x) - Q ((star P) (Q x)) = (star A) x := by
      rw [hQPy, hPstarQ, add_sub_cancel_left]
    rw [hDiff, hQPy] at h
    exact h
  have hPge : 1 ≤ ‖P‖ := by
    obtain ⟨x, hx⟩ : ∃ x, P x ≠ 0 := by
      by_contra! h
      exact hP0 (ContinuousLinearMap.ext h)
    have hx' := P.le_opNorm (P x)
    have hPP : P (P x) = P x := DFunLike.congr_fun hP.eq x
    rw [hPP] at hx'
    exact le_of_mul_le_mul_right (by simpa only [one_mul] using hx') (norm_pos_iff.mpr hx)
  have hpSq : 0 ≤ ‖P‖ ^ 2 - 1 := by nlinarith
  have hSq (x : H) : ‖(star A) x‖ ^ 2 ≤ (‖P‖ ^ 2 - 1) * ‖x‖ ^ 2 := by
    have hb := pow_le_pow_left₀ (norm_nonneg _) ((star P).le_opNorm (Q x)) 2
    rw [hPy, mul_pow, normStar] at hb
    calc
      _ ≤ (‖P‖ ^ 2 - 1) * ‖Q x‖ ^ 2 := by linarith only [hb]
      _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hQcontract x) 2) hpSq
  have hlow : 1 + ‖A‖ ^ 2 ≤ ‖P‖ ^ 2 := by
    have h := opNorm_le_of_sq_apply (star A) hpSq hSq
    rw [normStar] at h
    linarith only [h]
  have hu : ‖P‖ ^ 2 ≤ 1 + ‖A‖ ^ 2 := by
    have h : ‖star P‖ ^ 2 ≤ 1 + ‖A‖ ^ 2 :=
      opNorm_le_of_sq_apply (star P) (r := 1 + ‖A‖ ^ 2) (by positivity) (fun x ↦ ?_)
    · simpa only [normStar] using h
    have he : (star P) x = (star P) (Q x) := by
      rw [hPstarQ, hPstar, add_apply]
    have hs : (star A) x = (star A) (Q x) := by
      change (star A) x = (star A * Q) x
      rw [hAstarQ]
    rw [he, hPy, hs]
    have hA := pow_le_pow_left₀ (norm_nonneg _) ((star A).le_opNorm (Q x)) 2
    rw [mul_pow, normStar] at hA
    calc
      _ ≤ (1 + ‖A‖ ^ 2) * ‖Q x‖ ^ 2 := by linarith only [hA]
      _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hQcontract x) 2) (by positivity)
  have hskew : P - P† = A - star A := by
    rw [← star_eq_adjoint, hPstar, hPdecomp]
    abel
  have hskewSq : ‖A - star A‖ ^ 2 = ‖A‖ ^ 2 := by
    have hlo : ‖A‖ ≤ ‖A - star A‖ := by
      apply A.opNorm_le_bound (norm_nonneg _) fun x ↦ ?_
      have ha : Q ((A - star A) x) = A x := by
        change (Q * (A - star A)) x = A x
        rw [mul_sub, hQA, hQAstar, sub_zero]
      rw [← ha]
      exact (hQcontract _).trans ((A - star A).le_opNorm x)
    have hhi := opNorm_le_of_sq_apply (A - star A) (sq_nonneg ‖A‖) fun x ↦ ?_
    · exact le_antisymm hhi (pow_le_pow_left₀ (norm_nonneg _) hlo 2)
    have hcomp : A x = A (x - Q x) := by
      rw [map_sub]
      change A x = A x - (A * Q) x
      rw [hAQ, zero_apply, sub_zero]
    have hco : (star A) x = (star A) (Q x) := by
      change (star A) x = (star A * Q) x
      rw [hAstarQ]
    have hx : Q ((A - star A) x) = A x := by
      change (Q * (A - star A)) x = A x
      rw [mul_sub, hQA, hQAstar, sub_zero]
    have hy : ((A - star A) x) - Q ((A - star A) x) = -(star A) x := by
      rw [hx, sub_apply]
      abel
    have hsum := E.norm_sq_eq_add_norm_sq_starProjection ((A - star A) x)
    rw [Submodule.starProjection_orthogonal_val] at hsum
    change _ = ‖Q ((A - star A) x)‖ ^ 2 + ‖(A - star A) x - Q ((A - star A) x)‖ ^ 2 at hsum
    rw [hy, hx, norm_neg] at hsum
    have hxsum := E.norm_sq_eq_add_norm_sq_starProjection x
    rw [Submodule.starProjection_orthogonal_val] at hxsum
    change ‖x‖ ^ 2 = ‖Q x‖ ^ 2 + ‖x - Q x‖ ^ 2 at hxsum
    rw [hsum, hcomp, hco, hxsum]
    have ha := pow_le_pow_left₀ (norm_nonneg _) (A.le_opNorm (x - Q x)) 2
    have hb := pow_le_pow_left₀ (norm_nonneg _) ((star A).le_opNorm (Q x)) 2
    rw [mul_pow] at ha
    rw [mul_pow, normStar] at hb
    linarith only [ha, hb]
  rw [hskew, hskewSq]
  exact le_antisymm hu hlow

theorem norm_one_sub_idempotent_le (P : H →L[𝕜] H) (hP : IsIdempotentElem P)
    {K : ℝ} (hK : 1 ≤ K) (h : ‖P‖ ≤ K) : ‖1 - P‖ ≤ K := by
  by_cases h0 : P = 0
  · rw [h0, sub_zero]
    exact (norm_id_le (𝕜 := 𝕜) (E := H)).trans hK
  by_cases h1 : 1 - P = 0
  · simp only [h1, norm_zero]
    linarith
  have hq : IsIdempotentElem (1 - P) := by
    unfold IsIdempotentElem
    rw [sub_mul, one_mul, mul_sub, mul_one, hP.eq, sub_self, sub_zero]
  have heq : (1 - P) - (1 - P)† = -(P - P†) := by
    simp only [← star_eq_adjoint, star_sub, star_one]
    abel
  have hbound : ‖1 - P‖ ^ 2 ≤ K ^ 2 := by
    rw [norm_sq_idempotent_eq_one_add_skew_sq _ hq h1, heq, norm_neg,
      ← norm_sq_idempotent_eq_one_add_skew_sq _ hP h0]
    exact pow_le_pow_left₀ (norm_nonneg _) h 2
  exact (sq_le_sq₀ (norm_nonneg _) (by linarith : 0 ≤ K)).mp hbound

/-- Scaled Young inequality for a difference of vectors. -/
theorem norm_sub_sq_le_weighted {E : Type*} [SeminormedAddCommGroup E] (x y : E)
    {h : ℝ} (hh : 0 < h) :
    ‖x - y‖ ^ 2 ≤ (1 + h) * ‖x‖ ^ 2 + (1 + h⁻¹) * ‖y‖ ^ 2 := by
  have ht := pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le x y) 2
  have hy : 2 * ‖x‖ * ‖y‖ ≤ h * ‖x‖ ^ 2 + h⁻¹ * ‖y‖ ^ 2 := by
    apply (le_of_mul_le_mul_left ?_ hh)
    rw [mul_add, ← mul_assoc h h⁻¹, mul_inv_cancel₀ hh.ne', one_mul]
    nlinarith only [sq_nonneg (h * ‖x‖ - ‖y‖)]
  calc
    _ ≤ (‖x‖ + ‖y‖) ^ 2 := ht
    _ ≤ _ := by linarith only [hy]

/-- Bound for the active two rows of the small-mean block joining estimate.
The nonnegative input energies come from an orthogonal partition of the input. -/
theorem join_small_mean_two_row_bound {E F : Type*}
    [SeminormedAddCommGroup E] [SeminormedAddCommGroup F] (a b : E) (p : F)
    {Q Z η EA EB : ℝ} (hZ : 0 ≤ Z) (hη : 0 ≤ η) (hQ : 1 + Z < Q)
    (hEA : 0 ≤ EA) (_hEB : 0 ≤ EB)
    (ha : ‖a‖ ^ 2 ≤ (1 + Z) * EA) (hb : ‖b‖ ^ 2 ≤ η * Q * EB)
    (hp : ‖p‖ ^ 2 ≤ Q * EB) :
    ‖a - b‖ ^ 2 + ‖p‖ ^ 2 ≤ (Q + Q ^ 2 * η / (Q - 1 - Z)) * (EA + EB) := by
  have hz : 0 < 1 + Z := by linarith
  have hden : 0 < Q - 1 - Z := by linarith
  let h := (Q - 1 - Z) / (1 + Z)
  have hh : 0 < h := div_pos hden hz
  have h0 : 0 ≤ 1 + h := by linarith
  have h1 : 0 ≤ 1 + h⁻¹ := by positivity
  have hconst : (1 + h) * (1 + Z) = Q := by
    dsimp [h]
    field_simp
    ring
  have hactive : (1 + h⁻¹) * (η * Q) = Q ^ 2 * η / (Q - 1 - Z) := by
    dsimp [h]
    rw [inv_div]
    field_simp
    ring
  have hf : ‖a - b‖ ^ 2 + ‖p‖ ^ 2 ≤ Q * EA + (Q + Q ^ 2 * η / (Q - 1 - Z)) * EB := calc
    _ ≤ (1 + h) * ‖a‖ ^ 2 + (1 + h⁻¹) * ‖b‖ ^ 2 + Q * EB :=
      add_le_add (norm_sub_sq_le_weighted a b hh) hp
    _ ≤ (1 + h) * ((1 + Z) * EA) + (1 + h⁻¹) * (η * Q * EB) + Q * EB :=
      add_le_add (add_le_add (mul_le_mul_of_nonneg_left ha h0)
        (mul_le_mul_of_nonneg_left hb h1)) le_rfl
    _ = _ := by rw [← mul_assoc, ← mul_assoc, hconst, hactive]; ring
  have hc : 0 ≤ Q ^ 2 * η / (Q - 1 - Z) := by positivity
  refine hf.trans ?_
  rw [mul_add]
  exact add_le_add (mul_le_mul_of_nonneg_right (by linarith only [hc]) hEA) le_rfl

section MetricCut

variable {𝕜 ι : Type*} [RCLike 𝕜] [Fintype ι] [DecidableEq ι]

theorem qform_eq_sqrt_mulVec_norm_sq {G : Matrix ι ι 𝕜} (hG : G.PosDef) (x : ι → 𝕜) :
    qform G x = ‖WithLp.toLp 2 (CFC.sqrt G *ᵥ x)‖ ^ 2 := by
  rw [← qform_conjTranspose_mul_self, (posDef_sqrt hG).isHermitian.eq, sqrt_mul_sqrt_of_posDef hG]

/-- A Gram norm estimate is an operator norm estimate in standard Euclidean coordinates. -/
theorem metric_opNorm_le_iff {G : Matrix ι ι 𝕜} (hG : G.PosDef)
    (D : Matrix ι ι 𝕜) {K : ℝ} (hK : 0 ≤ K) :
    opNorm (CFC.sqrt G * D * (CFC.sqrt G)⁻¹) ≤ K ↔
    ∀ x, qform G (D *ᵥ x) ≤ K ^ 2 * qform G x := by
  let A := CFC.sqrt G
  let f := Matrix.toEuclideanCLM (𝕜 := 𝕜) (n := ι) (A * D * A⁻¹)
  have hA := (Matrix.isUnit_iff_isUnit_det A).mp (posDef_sqrt hG).isUnit
  have hB (x : ι → 𝕜) : A *ᵥ (A⁻¹ *ᵥ x) = x := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hA, Matrix.one_mulVec]
  have hB' (x : ι → 𝕜) : A⁻¹ *ᵥ (A *ᵥ x) = x := by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hA, Matrix.one_mulVec]
  have happ (x : ι → 𝕜) : f (WithLp.toLp 2 x) = WithLp.toLp 2 (A *ᵥ (D *ᵥ (A⁻¹ *ᵥ x))) := by
    dsimp only [f]
    rw [Matrix.toEuclideanCLM_toLp, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  change ‖f‖ ≤ K ↔ _
  constructor
  · intro hf x
    have hi := (f.le_opNorm (WithLp.toLp 2 (A *ᵥ x))).trans
      (mul_le_mul_of_nonneg_right hf (norm_nonneg _))
    rw [happ, hB' x] at hi
    rw [qform_eq_sqrt_mulVec_norm_sq hG, qform_eq_sqrt_mulVec_norm_sq hG, ← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) hi 2
  · intro h
    apply f.opNorm_le_bound hK
    intro x
    obtain ⟨x, rfl⟩ := WithLp.toLp_surjective 2 x
    rw [happ]
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hK (norm_nonneg _))).mp
    have hi := h (A⁻¹ *ᵥ x)
    rw [qform_eq_sqrt_mulVec_norm_sq hG, qform_eq_sqrt_mulVec_norm_sq hG] at hi
    change ‖WithLp.toLp 2 (A *ᵥ (D *ᵥ (A⁻¹ *ᵥ x)))‖ ^ 2 ≤
      K ^ 2 * ‖WithLp.toLp 2 (A *ᵥ (A⁻¹ *ᵥ x))‖ ^ 2 at hi
    rw [hB, ← mul_pow] at hi
    exact hi

variable {n : ℕ}

theorem prefixMask_isIdempotent (k : ℕ) : IsIdempotentElem (prefixMask (n := n) 𝕜 k) := by
  unfold IsIdempotentElem prefixMask
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  by_cases hi : i.val < k <;> simp [hi]

/-- Bounding an ordered prefix also bounds the complementary cut in a positive Gram form. -/
theorem PB.complement_qform_le {G : Matrix (Fin n) (Fin n) 𝕜} {K : ℝ}
    (hG : G.PosDef) (hK : 1 ≤ K) (h : PB G K) {k : ℕ} (hk : k ≤ n) (x : Fin n → 𝕜) :
    qform G (x - truncCoeff k x) ≤ K ^ 2 * qform G x := by
  let D := prefixMask (n := n) 𝕜 k
  let A := CFC.sqrt G
  let C := A * D * A⁻¹
  let f := Matrix.toEuclideanCLM (𝕜 := 𝕜) (n := Fin n)
  have hA := (Matrix.isUnit_iff_isUnit_det A).mp (posDef_sqrt hG).isUnit
  have hA' : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul _ hA
  have hA'' : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv _ hA
  have hC : IsIdempotentElem C := by
    unfold IsIdempotentElem
    dsimp only [C]
    rw [show (A * D * A⁻¹) * (A * D * A⁻¹) = A * D * (A⁻¹ * A) * D * A⁻¹ by
      simp only [Matrix.mul_assoc], hA', Matrix.mul_one, Matrix.mul_assoc _ D D,
      (prefixMask_isIdempotent (n := n) (𝕜 := 𝕜) k).eq]
  have hf : IsIdempotentElem (f C) := by
    unfold IsIdempotentElem
    rw [← map_mul, hC.eq]
  have hnorm : ‖f C‖ ≤ K := (metric_opNorm_le_iff hG D h.1).mpr (fun c ↦ by
    rw [show D *ᵥ c = truncCoeff k c from prefixMask_mulVec k c]
    exact h.2 k hk c)
  have hc := norm_one_sub_idempotent_le (f C) hf hK hnorm
  have hcomp : A * (1 - D) * A⁻¹ = 1 - C := by
    change A * (1 - D) * A⁻¹ = 1 - A * D * A⁻¹
    rw [mul_sub, mul_one, sub_mul, hA'']
  have hm : opNorm (A * (1 - D) * A⁻¹) ≤ K := by
    change ‖f (A * (1 - D) * A⁻¹)‖ ≤ K
    rwa [hcomp, map_sub, map_one]
  have hp := ((metric_opNorm_le_iff hG (1 - D) h.1).mp hm) x
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, show D *ᵥ x = truncCoeff k x from prefixMask_mulVec k x] at hp
  exact hp

end MetricCut

/-- The constant component plus all omitted later-block means is one row of norm
at most sqrt(1+Z), from the summed gains of the later blocks. -/
theorem omitted_means_row_bound {σ : Type*} (later : Finset σ)
    (gain energy mean : σ → ℝ) (hg : ∀ i, 0 ≤ gain i) (he : ∀ i, 0 ≤ energy i)
    (hm : ∀ i ∈ later, mean i ^ 2 ≤ gain i * energy i) {Z γ : ℝ}
    (hZ : 0 ≤ Z) (hGain : (∑ i ∈ later, gain i) ≤ Z) :
    (γ - ∑ i ∈ later, mean i) ^ 2 ≤ (1 + Z) * (γ ^ 2 + ∑ i ∈ later, energy i) := by
  have hEach (i : σ) (hi : i ∈ later) : |mean i| ≤ √(gain i) * √(energy i) := by
    apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).mp
    rw [sq_abs, mul_pow, Real.sq_sqrt (hg i), Real.sq_sqrt (he i)]
    exact hm i hi
  let a := Real.sqrt Z
  let b := Real.sqrt (∑ i ∈ later, energy i)
  have hb : 0 ≤ ∑ i ∈ later, energy i := Finset.sum_nonneg fun i _ ↦ he i
  have ha2 : a ^ 2 = Z := Real.sq_sqrt hZ
  have hb2 : b ^ 2 = ∑ i ∈ later, energy i := Real.sq_sqrt hb
  have hall : |∑ i ∈ later, mean i| ≤ a * b := calc
    _ ≤ ∑ i ∈ later, |mean i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ later, √(gain i) * √(energy i) := Finset.sum_le_sum hEach
    _ ≤ √(∑ i ∈ later, gain i) * b := Real.sum_sqrt_mul_sqrt_le _ hg he
    _ ≤ a * b := mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hGain) (Real.sqrt_nonneg _)
  have hsub₀ : |γ - ∑ i ∈ later, mean i| ≤ |γ| + |∑ i ∈ later, mean i| := by
    simpa only [Real.norm_eq_abs] using norm_sub_le γ (∑ i ∈ later, mean i)
  have hsub : |γ - ∑ i ∈ later, mean i| ≤ |γ| + a * b :=
    hsub₀.trans (add_le_add le_rfl hall)
  calc
    _ = |γ - ∑ i ∈ later, mean i| ^ 2 := (sq_abs _).symm
    _ ≤ (|γ| + a * b) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hsub 2
    _ ≤ (1 + a ^ 2) * (|γ| ^ 2 + b ^ 2) := by nlinarith only [sq_nonneg (a * |γ| - b)]
    _ = _ := by rw [ha2, hb2, sq_abs]

/-- Real quadratic-form version of the small-mean block join with a one-dimensional head.
The centered energies of earlier blocks are copied unchanged. The constant component changes
by subtracting all later-block means and the mean of the active complementary cut.
Both the set of later blocks and the earlier energy may be empty/zero. -/
theorem join_small_mean_constant_bound {σ : Type*} (later : Finset σ)
    (gain energy mean : σ → ℝ) (hg : ∀ i, 0 ≤ gain i) (he : ∀ i, 0 ≤ energy i)
    (hm : ∀ i ∈ later, mean i ^ 2 ≤ gain i * energy i) {Q Z η γ early active kept comp : ℝ}
    (hZ : 0 ≤ Z) (hη : 0 ≤ η) (hQ : 1 + Z < Q)
    (hGain : (∑ i ∈ later, gain i) ≤ Z) (hEarly : 0 ≤ early) (hActive : 0 ≤ active)
    (hKept : 0 ≤ kept) (hCut : kept ≤ Q * active)
    (hComp : comp ^ 2 ≤ η * Q * active) :
    early + kept + (γ - (∑ i ∈ later, mean i) - comp) ^ 2 ≤
      (Q + Q ^ 2 * η / (Q - 1 - Z)) * (early + γ ^ 2 + (∑ i ∈ later, energy i) + active) := by
  let EA := γ ^ 2 + ∑ i ∈ later, energy i
  let a := γ - ∑ i ∈ later, mean i
  have hEA : 0 ≤ EA := add_nonneg (sq_nonneg _) (Finset.sum_nonneg fun i _ ↦ he i)
  have ha : ‖a‖ ^ 2 ≤ (1 + Z) * EA := by
    simp only [Real.norm_eq_abs, sq_abs]
    exact omitted_means_row_bound later gain energy mean hg he hm hZ hGain
  have hp : ‖Real.sqrt kept‖ ^ 2 ≤ Q * active := by
    rw [Real.norm_eq_abs, sq_abs, Real.sq_sqrt hKept]
    exact hCut
  have hcomp : ‖comp‖ ^ 2 ≤ η * Q * active := by
    simpa only [Real.norm_eq_abs, sq_abs] using hComp
  have h := join_small_mean_two_row_bound a comp (Real.sqrt kept) hZ hη hQ hEA hActive ha hcomp hp
  rw [Real.norm_eq_abs, sq_abs, Real.norm_eq_abs, sq_abs, Real.sq_sqrt hKept] at h
  let K := Q + Q ^ 2 * η / (Q - 1 - Z)
  have hK : 1 ≤ K := by
    have hd : 0 < Q - 1 - Z := by linarith
    have hz : 0 ≤ Q ^ 2 * η / (Q - 1 - Z) := by positivity
    dsimp only [K]
    linarith
  have hE : early ≤ K * early := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hK hEarly
  have hh := add_le_add hE h
  change early + ((a - comp) ^ 2 + kept) ≤ K * early + K * (EA + active) at hh
  have hleft : early + kept + (a - comp) ^ 2 = early + ((a - comp) ^ 2 + kept) := by ring
  have hright : K * (early + γ ^ 2 + (∑ i ∈ later, energy i) + active) =
      K * early + K * (EA + active) := by dsimp only [EA]; ring
  change early + kept + (a - comp) ^ 2 ≤ K * (early + γ ^ 2 + (∑ i ∈ later, energy i) + active)
  rwa [hleft, hright]

section TwoProjection

/-- Finite span carrying all the nontrivial interactions of the two projections. -/
def twoProjectionSpan (A : Submodule 𝕜 H) (D : H →L[𝕜] H) :=
  A ⊔ A.map D.toLinearMap

omit [CompleteSpace H] in
instance finiteDimensional_twoProjectionSpan (A : Submodule 𝕜 H) [FiniteDimensional 𝕜 A]
    (D : H →L[𝕜] H) : FiniteDimensional 𝕜 (twoProjectionSpan A D) := by
  unfold twoProjectionSpan
  infer_instance

omit [CompleteSpace H] in
theorem twoProjectionSpan_map_mem (A : Submodule 𝕜 H) {D : H →L[𝕜] H}
    (hD : IsIdempotentElem D) {x : H} (hx : x ∈ twoProjectionSpan A D) :
    D x ∈ twoProjectionSpan A D := by
  rw [twoProjectionSpan, Submodule.mem_sup] at hx ⊢
  obtain ⟨u, hu, v, ⟨w, hw, rfl⟩, rfl⟩ := hx
  have hadd : u + w ∈ A := A.add_mem hu hw
  refine ⟨0, A.zero_mem, D (u + w), ⟨u + w, hadd, rfl⟩, ?_⟩
  have hDD : D (D w) = D w := DFunLike.congr_fun hD.eq w
  simp [map_add, hDD]

theorem twoProjectionSpan_orthogonal_map_mem (A : Submodule 𝕜 H) {D : H →L[𝕜] H}
    (hD : IsIdempotentElem D) (hDA : D† = D) {x : H} (hx : x ∈ (twoProjectionSpan A D)ᗮ) :
    D x ∈ (twoProjectionSpan A D)ᗮ := by
  rw [Submodule.mem_orthogonal] at hx ⊢
  intro y hy
  rw [← adjoint_inner_left, hDA]
  exact hx _ (twoProjectionSpan_map_mem A hD hy)

omit [CompleteSpace H] in
theorem twoProjectionSpan_orthogonal_initial_zero (A : Submodule 𝕜 H) [A.HasOrthogonalProjection]
    (D : H →L[𝕜] H) {x : H} (hx : x ∈ (twoProjectionSpan A D)ᗮ) :
    A.starProjection x = 0 := by
  rw [Submodule.starProjection_apply_eq_zero_iff]
  exact Submodule.orthogonal_le (show A ≤ twoProjectionSpan A D from le_sup_left) hx

/-- The orthogonal remainder splits into simultaneous (zero, one) and (zero, zero) parts. -/
theorem twoProjectionSpan_remainder_decompose (A : Submodule 𝕜 H) [A.HasOrthogonalProjection]
    {D : H →L[𝕜] H} (hD : IsIdempotentElem D) (hDA : D† = D) {x : H}
    (hx : x ∈ (twoProjectionSpan A D)ᗮ) :
    ∃ u v : H, u ∈ (twoProjectionSpan A D)ᗮ ∧ v ∈ (twoProjectionSpan A D)ᗮ ∧
      A.starProjection u = 0 ∧ A.starProjection v = 0 ∧ D u = u ∧ D v = 0 ∧
      ⟪u, v⟫_𝕜 = 0 ∧ u + v = x := by
  have hu := twoProjectionSpan_orthogonal_map_mem A hD hDA hx
  have hv := (twoProjectionSpan A D)ᗮ.sub_mem hx hu
  have hDD : D (D x) = D x := DFunLike.congr_fun hD.eq x
  have hDZ : D (x - D x) = 0 := by rw [map_sub, hDD, sub_self]
  refine ⟨D x, x - D x, hu, hv, twoProjectionSpan_orthogonal_initial_zero A D hu,
    twoProjectionSpan_orthogonal_initial_zero A D hv, hDD, hDZ, ?_, ?_⟩
  · calc
      _ = ⟪x, (D†) (x - D x)⟫_𝕜 := (adjoint_inner_right D x _).symm
      _ = _ := by rw [hDA, hDZ, inner_zero_right]
  · abel

/-- Compression of the second projection to the range of the first. -/
def projectionCompression (A : Submodule 𝕜 H) [A.HasOrthogonalProjection]
    (D : H →L[𝕜] H) : A →L[𝕜] A :=
  A.orthogonalProjectionOnto ∘L D ∘L A.subtypeL

omit [CompleteSpace H] in
@[simp] theorem projectionCompression_apply (A : Submodule 𝕜 H) [A.HasOrthogonalProjection]
    (D : H →L[𝕜] H) (x : A) :
    ((projectionCompression A D x : A) : H) = A.starProjection (D (x : H)) := rfl

theorem projectionCompression_adjoint (A : Submodule 𝕜 H) [CompleteSpace A]
    {D : H →L[𝕜] H} (hDA : D† = D) :
    (projectionCompression A D)† = projectionCompression A D := by
  simp only [projectionCompression, adjoint_comp, A.adjoint_orthogonalProjectionOnto,
    A.adjoint_subtypeL, comp_assoc, hDA]

theorem projectionCompression_isSymmetric (A : Submodule 𝕜 H) [CompleteSpace A]
    {D : H →L[𝕜] H} (hDA : D† = D) : (projectionCompression A D).toLinearMap.IsSymmetric := by
  intro x y
  change ⟪projectionCompression A D x, y⟫_𝕜 = ⟪x, projectionCompression A D y⟫_𝕜
  rw [← adjoint_inner_right, projectionCompression_adjoint A hDA]

end TwoProjection

section EigenPlane

variable {ι : Type*}

theorem selfAdjoint_idempotent_norm_le_one (D : H →L[𝕜] H)
    (hD : IsIdempotentElem D) (hA : D† = D) : ‖D‖ ≤ 1 := by
  have h := norm_adjoint_comp D
  rw [hA] at h
  change ‖D * D‖ = ‖D‖ ^ 2 at h
  rw [hD.eq] at h
  nlinarith [norm_nonneg D]

omit [CompleteSpace H] in
theorem inner_against_starProjection (A : Submodule 𝕜 H) [A.HasOrthogonalProjection]
    {v : H} (hv : v ∈ A) (x : H) :
    ⟪v, A.starProjection x⟫_𝕜 = ⟪v, x⟫_𝕜 := by
  rw [← Submodule.inner_starProjection_left_eq_right, Submodule.starProjection_eq_self_iff.mpr hv]

/-- Component of a second projection off the first projection's eigenvector. -/
def projectionPlaneOff (D : H →L[𝕜] H) (x : H) (t : ℝ) : H :=
  D x - (t : 𝕜) • x

omit [CompleteSpace H] in
theorem projectionPlaneOff_initial_zero (A : Submodule 𝕜 H) [A.HasOrthogonalProjection]
    (D : H →L[𝕜] H) {x : H} (hx : x ∈ A) {t : ℝ}
    (hE : A.starProjection (D x) = (t : 𝕜) • x) :
    A.starProjection (projectionPlaneOff D x t) = 0 := by
  rw [projectionPlaneOff, map_sub, hE, map_smul, Submodule.starProjection_eq_self_iff.mpr hx, sub_self]

omit [CompleteSpace H] in
theorem projectionPlaneOff_apply (D : H →L[𝕜] H) (hD : IsIdempotentElem D) (x : H) (t : ℝ) :
    D (projectionPlaneOff D x t) =
      ((t * (1 - t) : ℝ) : 𝕜) • x + ((1 - t : ℝ) : 𝕜) • projectionPlaneOff D x t := by
  have hd : D (D x) = D x := DFunLike.congr_fun hD.eq x
  rw [projectionPlaneOff, map_sub, hd, map_smul, smul_sub, smul_smul, RCLike.ofReal_mul]
  have hs : (t : 𝕜) * ((1 - t : ℝ) : 𝕜) = ((1 - t : ℝ) : 𝕜) * (t : 𝕜) := mul_comm _ _
  rw [hs, add_sub_cancel]
  push_cast
  rw [sub_smul, one_smul]

section Ortho

variable (A : Submodule 𝕜 H) [A.HasOrthogonalProjection]
variable {D : H →L[𝕜] H} (hD : IsIdempotentElem D) (hDA : D† = D)
variable (v : ι → H) (hv : Orthonormal 𝕜 v) (t : ι → ℝ)
variable (hVmem : ∀ i, v i ∈ A) (hE : ∀ i, A.starProjection (D (v i)) = (t i : 𝕜) • v i)

include hVmem hE in
omit [CompleteSpace H] in
theorem inner_projection_eigen (i j : ι) : ⟪v i, D (v j)⟫_𝕜 = (t j : 𝕜) * ⟪v i, v j⟫_𝕜 := by
  rw [← inner_against_starProjection A (hVmem i), hE, inner_smul_right]

include hD hDA hVmem hv hE in
theorem projection_eigenvalue_bounds (i : ι) : 0 ≤ t i ∧ t i ≤ 1 := by
  have hDD : D (D (v i)) = D (v i) := DFunLike.congr_fun hD.eq (v i)
  have hInner : ⟪D (v i), D (v i)⟫_𝕜 = (t i : 𝕜) := calc
    _ = ⟪v i, D (v i)⟫_𝕜 := by rw [← adjoint_inner_right, hDA, hDD]
    _ = _ := by rw [inner_projection_eigen A v t hVmem hE, inner_self_eq_norm_sq_to_K, hv.1 i]
                simp
  have ht := congrArg RCLike.re hInner
  rw [inner_self_eq_norm_sq, RCLike.ofReal_re] at ht
  have hN : ‖D (v i)‖ ≤ 1 := calc
    _ ≤ ‖D‖ * ‖v i‖ := D.le_opNorm _
    _ ≤ 1 := by simpa only [hv.1 i, mul_one] using selfAdjoint_idempotent_norm_le_one D hD hDA
  exact ⟨ht ▸ sq_nonneg _, ht ▸ (by nlinarith [norm_nonneg (D (v i))] : ‖D (v i)‖ ^ 2 ≤ 1)⟩

include hVmem hE in
omit [CompleteSpace H] in
theorem inner_projectionPlaneOff_axis (i j : ι) :
    ⟪v i, projectionPlaneOff D (v j) (t j)⟫_𝕜 = 0 := by
  rw [projectionPlaneOff, inner_sub_right, inner_smul_right, inner_projection_eigen A v t hVmem hE, sub_self]

include hD hDA hVmem hE in
theorem inner_projectionPlaneOff (i j : ι) :
    ⟪projectionPlaneOff D (v i) (t i), projectionPlaneOff D (v j) (t j)⟫_𝕜 =
      ((t j * (1 - t j) : ℝ) : 𝕜) * ⟪v i, v j⟫_𝕜 := by
  have hi : ⟪v i, projectionPlaneOff D (v j) (t j)⟫_𝕜 = 0 :=
    inner_projectionPlaneOff_axis A v t hVmem hE i j
  have hj : ⟪D (v i), projectionPlaneOff D (v j) (t j)⟫_𝕜 =
      ⟪v i, D (projectionPlaneOff D (v j) (t j))⟫_𝕜 :=
    (adjoint_inner_right D (v i) _).symm.trans (by rw [hDA])
  calc
    _ = ⟪D (v i) - (t i : 𝕜) • v i, projectionPlaneOff D (v j) (t j)⟫_𝕜 := rfl
    _ = ⟪D (v i), projectionPlaneOff D (v j) (t j)⟫_𝕜 := by
      rw [inner_sub_left, inner_smul_left, hi, mul_zero, sub_zero]
    _ = _ := by
      rw [hj, projectionPlaneOff_apply D hD, inner_add_right, inner_smul_right, inner_smul_right,
        hi, mul_zero, add_zero]

include hD hDA hVmem hE hv in
theorem norm_sq_projectionPlaneOff (i : ι) :
    ‖projectionPlaneOff D (v i) (t i)‖ ^ 2 = t i * (1 - t i) := by
  have h := congrArg RCLike.re (inner_projectionPlaneOff A hD hDA v t hVmem hE i i)
  rw [inner_self_eq_norm_sq, inner_self_eq_norm_sq_to_K, hv.1 i] at h
  simpa using h

include hD hDA hVmem hE hv in
theorem projectionPlaneOff_zero_at_endpoint (i : ι) (hi : t i = 0 ∨ t i = 1) :
    projectionPlaneOff D (v i) (t i) = 0 := by
  apply norm_eq_zero.mp
  have h := norm_sq_projectionPlaneOff A hD hDA v hv t hVmem hE i
  rcases hi with hi | hi <;> simpa [hi] using h

end Ortho

end EigenPlane

section ColumnCut

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

private theorem norm_skew_le_sqrt {P : H →L[𝕜] H} (hP : IsIdempotentElem P) {K : ℝ}
    (hK : 1 ≤ K) (hPK : ‖P‖ ≤ K) : ‖P - P†‖ ≤ Real.sqrt (K ^ 2 - 1) := by
  have hnon : 0 ≤ K ^ 2 - 1 := by nlinarith
  apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
  rw [Real.sq_sqrt hnon]
  by_cases h0 : P = 0
  · simpa only [h0, map_zero, sub_self, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0)] using hnon
  · have hsq := norm_sq_idempotent_eq_one_add_skew_sq P hP h0
    have hle := pow_le_pow_left₀ (norm_nonneg _) hPK 2
    linarith only [hsq, hle]

/-- The norm of a prefix crossing two annihilating coordinate projections is controlled
by the sum of their skew parts, with no dimension-dependent loss. -/
theorem norm_sq_disjoint_idempotent_add_le (P R : H →L[𝕜] H)
    (hP : IsIdempotentElem P) (hR : IsIdempotentElem R) (hPR : P * R = 0) (hRP : R * P = 0)
    {K L : ℝ} (hK : 1 ≤ K) (hL : 1 ≤ L) (hPK : ‖P‖ ≤ K) (hRL : ‖R‖ ≤ L) :
    ‖P + R‖ ^ 2 ≤ 1 + (Real.sqrt (K ^ 2 - 1) + Real.sqrt (L ^ 2 - 1)) ^ 2 := by
  by_cases h0 : P + R = 0
  · rw [h0, norm_zero]
    norm_num
    positivity
  have hId : IsIdempotentElem (P + R) := by
    unfold IsIdempotentElem
    rw [add_mul, mul_add, mul_add, hP.eq, hR.eq, hPR, hRP, add_zero, zero_add]
  rw [norm_sq_idempotent_eq_one_add_skew_sq _ hId h0]
  have hskew : P + R - (P + R)† = (P - P†) + (R - R†) := by
    rw [map_add]
    abel
  rw [hskew]
  apply add_le_add le_rfl (pow_le_pow_left₀ (norm_nonneg _) ?_ 2)
  exact (norm_add_le _ _).trans (add_le_add (norm_skew_le_sqrt hP hK hPK)
    (norm_skew_le_sqrt hR hL hRL))

omit [CompleteSpace E] in
/-- A completed column prefix plus a cut inside the current column.
Insertion and extraction are measured in the relevant Hilbert metrics. -/
theorem norm_sq_partial_column_prefix_le (P : H →L[𝕜] H) (J : E →L[𝕜] H) (X : H →L[𝕜] E)
    (C : E →L[𝕜] E) (hP : IsIdempotentElem P) (hC : IsIdempotentElem C)
    (hXJ : X ∘L J = 1) (hPJ : P ∘L J = 0) (hXP : X ∘L P = 0)
    {Ks Kv ε : ℝ} (hKs : 1 ≤ Ks) (hKv : 1 ≤ Kv) (hε : 0 ≤ ε)
    (hPnorm : ‖P‖ ≤ Ks) (hJnorm : ‖J‖ ≤ 1) (hXnorm : ‖X‖ ≤ Real.sqrt (1 + 2 * ε))
    (hCnorm : ‖C‖ ≤ Kv) :
    ‖P + J ∘L C ∘L X‖ ^ 2 ≤
      1 + (Real.sqrt (Ks ^ 2 - 1) + Real.sqrt ((1 + 2 * ε) * Kv ^ 2 - 1)) ^ 2 := by
  let R := J ∘L C ∘L X
  have he : ∀ x, X (J x) = x := fun x ↦ DFunLike.congr_fun hXJ x
  have hCeq : ∀ x, C (C x) = C x := fun x ↦ DFunLike.congr_fun hC.eq x
  have hR : IsIdempotentElem R := by
    ext x
    change J (C (X (J (C (X x))))) = J (C (X x))
    rw [he, hCeq]
  have hPR : P * R = 0 := by
    ext x
    exact DFunLike.congr_fun hPJ (C (X x))
  have hRP : R * P = 0 := by
    ext x
    have ht : X (P x) = 0 := DFunLike.congr_fun hXP x
    change J (C (X (P x))) = 0
    simp [ht]
  let L := Real.sqrt (1 + 2 * ε) * Kv
  have hL : 1 ≤ L := by
    have hS : 1 ≤ Real.sqrt (1 + 2 * ε) := calc
      1 = Real.sqrt 1 := Real.sqrt_one.symm
      _ ≤ _ := Real.sqrt_le_sqrt (by linarith)
    calc
      1 = (1 : ℝ) * 1 := by ring
      _ ≤ Real.sqrt (1 + 2 * ε) * Kv :=
        mul_le_mul hS hKv zero_le_one (Real.sqrt_nonneg _)
  have hRL : ‖R‖ ≤ L := calc
    _ ≤ ‖J‖ * ‖C ∘L X‖ := J.opNorm_comp_le _
    _ ≤ ‖J‖ * (‖C‖ * ‖X‖) := mul_le_mul_of_nonneg_left (C.opNorm_comp_le X) (norm_nonneg _)
    _ ≤ 1 * (Kv * Real.sqrt (1 + 2 * ε)) :=
      mul_le_mul hJnorm (mul_le_mul hCnorm hXnorm (norm_nonneg _) (by linarith))
        (by positivity) zero_le_one
    _ = _ := by simp only [L, one_mul, mul_comm]
  have hLsq : L ^ 2 = (1 + 2 * ε) * Kv ^ 2 := by
    dsimp only [L]
    rw [mul_pow, Real.sq_sqrt (by linarith)]
  have hb := norm_sq_disjoint_idempotent_add_le P R hP hR hPR hRP hKs hL hPnorm hRL
  rw [hLsq] at hb
  exact hb

end ColumnCut

section ProjectionAxes

variable (A : Submodule 𝕜 H) [FiniteDimensional 𝕜 A] {D : H →L[𝕜] H}
variable (hDA : D† = D)

/-- Eigenbasis of the second projection compressed to the first finite range. -/
def projectionEigenbasis : OrthonormalBasis (Fin (Module.finrank 𝕜 A)) 𝕜 A :=
  (projectionCompression_isSymmetric A hDA).eigenvectorBasis rfl

def projectionEigenvalues : Fin (Module.finrank 𝕜 A) → ℝ :=
  (projectionCompression_isSymmetric A hDA).eigenvalues rfl

def projectionAxes : Fin (Module.finrank 𝕜 A) → H := fun i ↦ (projectionEigenbasis A hDA i : H)

theorem projectionAxes_orthonormal : Orthonormal 𝕜 (projectionAxes A hDA) :=
  (projectionEigenbasis A hDA).orthonormal.comp_linearIsometry A.subtypeₗᵢ

theorem projectionAxes_mem (i : Fin (Module.finrank 𝕜 A)) : projectionAxes A hDA i ∈ A :=
  (projectionEigenbasis A hDA i).property

theorem projectionAxes_span : span 𝕜 (Set.range (projectionAxes A hDA)) = A := by
  apply le_antisymm
  · exact span_le.mpr (by rintro _ ⟨i, rfl⟩; exact projectionAxes_mem A hDA i)
  · intro x hx
    have h := congrArg (fun a : A ↦ (a : H)) ((projectionEigenbasis A hDA).sum_repr ⟨x, hx⟩)
    change (↑(∑ i, (projectionEigenbasis A hDA).repr ⟨x, hx⟩ i • projectionEigenbasis A hDA i) : H) = x at h
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h
    rw [← h]
    apply Submodule.sum_mem
    intro i _
    apply Submodule.smul_mem
    exact subset_span ⟨i, rfl⟩

theorem projectionAxes_eigen (i : Fin (Module.finrank 𝕜 A)) :
    A.starProjection (D (projectionAxes A hDA i)) = (projectionEigenvalues A hDA i : 𝕜) • projectionAxes A hDA i := by
  have h := congrArg (fun a : A ↦ (a : H)) ((projectionCompression_isSymmetric A hDA).apply_eigenvectorBasis rfl i)
  exact h

section Span

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {A₀ : Submodule 𝕜 H} [FiniteDimensional 𝕜 A₀]

omit [CompleteSpace H] [Fintype ι] [DecidableEq ι] [FiniteDimensional 𝕜 ↥A₀] in
/-- The finite interaction space is spanned by the range axes and their second-projection images. -/
theorem twoProjectionSpan_eq_span_sum {v : ι → H} (hv : span 𝕜 (Set.range v) = A₀)
    (D : H →L[𝕜] H) :
    twoProjectionSpan A₀ D = span 𝕜 (Set.range (Sum.elim (D ∘ v) (fun i ↦ v i - D (v i)))) := by
  let F := span 𝕜 (Set.range (Sum.elim (D ∘ v) (fun i ↦ v i - D (v i))))
  have hvF (i : ι) : v i ∈ F := by
    have h₁ : D (v i) ∈ F := subset_span ⟨Sum.inl i, rfl⟩
    have h₂ : v i - D (v i) ∈ F := subset_span ⟨Sum.inr i, rfl⟩
    have hs := F.add_mem h₂ h₁
    simpa only [sub_add_cancel] using hs
  have hA : A₀ ≤ F := by
    rw [← hv]
    exact span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hvF i)
  apply le_antisymm
  · apply sup_le hA
    rw [← hv, Submodule.map_span]
    refine span_le.mpr ?_
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    exact subset_span ⟨Sum.inl i, rfl⟩
  · apply span_le.mpr
    rintro _ ⟨i | i, rfl⟩
    · exact (show A₀.map D.toLinearMap ≤ twoProjectionSpan A₀ D from le_sup_right)
        (show D (v i) ∈ A₀.map D.toLinearMap from
        ⟨v i, hv ▸ subset_span ⟨i, rfl⟩, rfl⟩)
    · have hvA : v i ∈ A₀ := hv ▸ subset_span ⟨i, rfl⟩
      exact (twoProjectionSpan A₀ D).sub_mem
        ((show A₀ ≤ twoProjectionSpan A₀ D from le_sup_left) hvA)
        ((show A₀.map D.toLinearMap ≤ twoProjectionSpan A₀ D from le_sup_right)
          (show D (v i) ∈ A₀.map D.toLinearMap from ⟨v i, hvA, rfl⟩))

omit [CompleteSpace H] [DecidableEq ι] [FiniteDimensional 𝕜 ↥A₀] in
/-- Split a finite interaction vector into the two generator families. -/
theorem exists_sum_twoProjectionSpan {v : ι → H} (hv : span 𝕜 (Set.range v) = A₀)
    {D : H →L[𝕜] H} {x : H} (hx : x ∈ twoProjectionSpan A₀ D) :
    ∃ c d : ι → 𝕜, (∑ i, (c i • D (v i) + d i • (v i - D (v i)))) = x := by
  rw [twoProjectionSpan_eq_span_sum hv D, ← Fintype.range_linearCombination] at hx
  obtain ⟨cd, hcd⟩ := hx
  change Fintype.linearCombination 𝕜 _ cd = _ at hcd
  rw [Fintype.linearCombination_apply, Fintype.sum_sum_type] at hcd
  refine ⟨cd ∘ Sum.inl, cd ∘ Sum.inr, ?_⟩
  simpa only [Function.comp_apply, Finset.sum_add_distrib, Sum.elim_inl, Sum.elim_inr] using hcd

end Span
end ProjectionAxes

theorem inner_D_apply_complement (D : H →L[𝕜] H)
    (hD : IsIdempotentElem D) (hDA : D† = D) (x y : H) :
    ⟪D x, y - D y⟫_𝕜 = 0 := by
  rw [← adjoint_inner_right, hDA, map_sub, show D (D y) = D y from DFunLike.congr_fun hD.eq y,
    sub_self, inner_zero_right]

theorem inner_D_both (D : H →L[𝕜] H)
    (hD : IsIdempotentElem D) (hDA : D† = D) (x y : H) :
    ⟪D x, D y⟫_𝕜 = ⟪x, D y⟫_𝕜 := by
  rw [← adjoint_inner_right, hDA, show D (D y) = D y from DFunLike.congr_fun hD.eq y]

theorem inner_complement_both (D : H →L[𝕜] H)
    (hD : IsIdempotentElem D) (hDA : D† = D) (x y : H) :
    ⟪x - D x, y - D y⟫_𝕜 = ⟪x, y⟫_𝕜 - ⟪x, D y⟫_𝕜 := by
  rw [inner_sub_left, inner_D_apply_complement D hD hDA, sub_zero, inner_sub_right]

/-- Normalized basis of the interaction plane in the second projection's range and kernel. -/
theorem twoProjection_D_basis (A : Submodule 𝕜 H) [A.HasOrthogonalProjection]
    {D : H →L[𝕜] H} (hD : IsIdempotentElem D) (hDA : D† = D) {v : H} (hv : v ∈ A)
    (hvone : ‖v‖ = 1) {t : ℝ} (ht : 0 < t) (ht' : t < 1)
    (he : A.starProjection (D v) = (t : 𝕜) • v) :
    ∃ u w : H, ‖u‖ = 1 ∧ ‖w‖ = 1 ∧ ⟪u, w⟫_𝕜 = 0 ∧ D u = u ∧ D w = 0 ∧
      D v = (Real.sqrt t : 𝕜) • u ∧ v - D v = (Real.sqrt (1 - t) : 𝕜) • w ∧
      A.starProjection u = (t : 𝕜) • u + (Real.sqrt (t * (1 - t)) : 𝕜) • w ∧
      A.starProjection w = (Real.sqrt (t * (1 - t)) : 𝕜) • u + ((1 - t : ℝ) : 𝕜) • w := by
  let a := Real.sqrt t
  let b := Real.sqrt (1 - t)
  let u := ((a⁻¹ : ℝ) : 𝕜) • D v
  let w := ((b⁻¹ : ℝ) : 𝕜) • (v - D v)
  have ha : 0 < a := Real.sqrt_pos.mpr ht
  have hb : 0 < b := Real.sqrt_pos.mpr (sub_pos.mpr ht')
  have haa : a * a = t := Real.mul_self_sqrt ht.le
  have hbb : b * b = 1 - t := Real.mul_self_sqrt (sub_nonneg.mpr ht'.le)
  have hcross : a * b = Real.sqrt (t * (1 - t)) := (Real.sqrt_mul ht.le _).symm
  have hPV : A.starProjection v = v := Submodule.starProjection_eq_self_iff.mpr hv
  have hinner : ⟪v, D v⟫_𝕜 = (t : 𝕜) := by
    rw [← inner_against_starProjection A hv, he, inner_smul_right, inner_self_eq_norm_sq_to_K, hvone]
    simp
  have hDnorm : ‖D v‖ = a := by
    have hh := congrArg RCLike.re ((inner_D_both D hD hDA v v).trans hinner)
    rw [inner_self_eq_norm_sq, RCLike.ofReal_re] at hh
    dsimp only [a]
    rw [← hh, Real.sqrt_sq (norm_nonneg _)]
  have hWnorm : ‖v - D v‖ = b := by
    have hh := congrArg RCLike.re (inner_complement_both D hD hDA v v)
    rw [inner_self_eq_norm_sq, map_sub, inner_self_eq_norm_sq, hvone, one_pow,
      hinner, RCLike.ofReal_re] at hh
    dsimp only [b]
    rw [← hh, Real.sqrt_sq (norm_nonneg _)]
  have hU : D v = (a : 𝕜) • u := by
    dsimp only [u]
    rw [smul_smul, ← RCLike.ofReal_mul, mul_inv_cancel₀ ha.ne', RCLike.ofReal_one, one_smul]
  have hW : v - D v = (b : 𝕜) • w := by
    dsimp only [w]
    rw [smul_smul, ← RCLike.ofReal_mul, mul_inv_cancel₀ hb.ne', RCLike.ofReal_one, one_smul]
  have hvrepr : v = (a : 𝕜) • u + (b : 𝕜) • w := by
    rw [← hU, ← hW]
    abel
  have hDD : D (D v) = D v := DFunLike.congr_fun hD.eq v
  have hUa : A.starProjection u = (a : 𝕜) • v := by
    dsimp only [u]
    rw [map_smul, he, smul_smul, ← RCLike.ofReal_mul, ← haa,
      ← mul_assoc, inv_mul_cancel₀ ha.ne', one_mul]
  have hWa : A.starProjection w = (b : 𝕜) • v := by
    dsimp only [w]
    have hsub : v - (t : 𝕜) • v = ((1 - t : ℝ) : 𝕜) • v := by
      rw [RCLike.ofReal_sub, RCLike.ofReal_one, sub_smul, one_smul]
    rw [map_smul, map_sub, hPV, he, hsub, smul_smul,
      ← RCLike.ofReal_mul, ← hbb, ← mul_assoc, inv_mul_cancel₀ hb.ne', one_mul]
  refine ⟨u, w, ?_, ?_, ?_, ?_, ?_, hU, hW, ?_, ?_⟩
  · dsimp only [u]
    rw [norm_smul, RCLike.norm_ofReal, abs_of_nonneg (inv_nonneg.mpr ha.le), hDnorm,
      inv_mul_cancel₀ ha.ne']
  · dsimp only [w]
    rw [norm_smul, RCLike.norm_ofReal, abs_of_nonneg (inv_nonneg.mpr hb.le), hWnorm,
      inv_mul_cancel₀ hb.ne']
  · simp only [u, w, inner_smul_left, inner_smul_right, inner_D_apply_complement D hD hDA,
      mul_zero]
  · simp only [u, map_smul, hDD]
  · simp only [w, map_smul, map_sub, hDD, sub_self, smul_zero]
  · calc
      _ = (a : 𝕜) • v := hUa
      _ = (a : 𝕜) • ((a : 𝕜) • u + (b : 𝕜) • w) := congrArg _ hvrepr
      _ = _ := by simp only [smul_add, smul_smul, ← RCLike.ofReal_mul, haa, hcross]
  · calc
      _ = (b : 𝕜) • v := hWa
      _ = (b : 𝕜) • ((a : 𝕜) • u + (b : 𝕜) • w) := congrArg _ hvrepr
      _ = _ := by simp only [smul_add, smul_smul, ← RCLike.ofReal_mul, hbb, mul_comm b a, hcross]

section FiberDecomposition

variable {ι : Type*}

omit [CompleteSpace H] in
theorem norm_sq_sum_of_orthogonal [Fintype ι] (v : ι → H)
    (hv : ∀ i j, i ≠ j → ⟪v i, v j⟫_𝕜 = 0) :
    ‖∑ i, v i‖ ^ 2 = ∑ i, ‖v i‖ ^ 2 := by
  classical
  calc
    _ = RCLike.re (∑ i, ∑ j, ⟪v i, v j⟫_𝕜) := by
      rw [← inner_self_eq_norm_sq (𝕜 := 𝕜), sum_inner]
      simp_rw [inner_sum]
    _ = _ := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_eq_single i, inner_self_eq_norm_sq]
      · exact fun j _ hij ↦ hv _ _ (Ne.symm hij)
      · simp

omit [CompleteSpace H] in
/-- Norm bound for a finite sum of orthogonal input and output components. -/
theorem norm_linearMap_sum_le_of_orthogonal [Fintype ι] (A : H →L[𝕜] H) (v : ι → H)
    (hin : ∀ i j, i ≠ j → ⟪v i, v j⟫_𝕜 = 0)
    (hout : ∀ i j, i ≠ j → ⟪A (v i), A (v j)⟫_𝕜 = 0)
    {K : ℝ} (hK : 0 ≤ K) (h : ∀ i, ‖A (v i)‖ ≤ K * ‖v i‖) :
    ‖A (∑ i, v i)‖ ≤ K * ‖∑ i, v i‖ := by
  rw [map_sum]
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hK (norm_nonneg _))).mp
  rw [mul_pow, norm_sq_sum_of_orthogonal v hin, norm_sq_sum_of_orthogonal _ hout, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (h i) 2

/-- One invariant interaction plane, allowing an endpoint eigenspace of dimension one. -/
def twoProjectionPlane (D : H →L[𝕜] H) (v : H) : Submodule 𝕜 H :=
  span 𝕜 {D v, v - D v}

omit [CompleteSpace H] in
theorem mem_twoProjectionPlane_iff (D : H →L[𝕜] H) (v x : H) :
    x ∈ twoProjectionPlane D v ↔ ∃ a b : 𝕜, a • D v + b • (v - D v) = x :=
  Submodule.mem_span_pair

omit [CompleteSpace H] in
theorem mem_twoProjectionPlane_axis (D : H →L[𝕜] H) (v : H) :
    v ∈ twoProjectionPlane D v := by
  refine (mem_twoProjectionPlane_iff D v v).mpr ⟨1, 1, ?_⟩
  simp only [one_smul]
  abel

omit [CompleteSpace H] in
theorem D_maps_twoProjectionPlane (D : H →L[𝕜] H) (hD : IsIdempotentElem D) (v : H) {x : H}
    (hx : x ∈ twoProjectionPlane D v) : D x ∈ twoProjectionPlane D v := by
  obtain ⟨a, b, rfl⟩ := (mem_twoProjectionPlane_iff D v x).mp hx
  have hd : D (D v) = D v := DFunLike.congr_fun hD.eq v
  rw [map_add, map_smul, map_smul, map_sub, hd, sub_self, smul_zero, add_zero]
  exact (twoProjectionPlane D v).smul_mem _ (subset_span (by simp))

omit [CompleteSpace H] in
theorem initial_maps_twoProjectionPlane (A : Submodule 𝕜 H) [A.HasOrthogonalProjection]
    (D : H →L[𝕜] H) {v : H} (hv : v ∈ A) {t : ℝ}
    (hE : A.starProjection (D v) = (t : 𝕜) • v) {x : H}
    (hx : x ∈ twoProjectionPlane D v) : A.starProjection x ∈ twoProjectionPlane D v := by
  obtain ⟨a, b, rfl⟩ := (mem_twoProjectionPlane_iff D v x).mp hx
  have hv' := mem_twoProjectionPlane_axis D v
  rw [map_add, map_smul, map_smul, map_sub, hE, Submodule.starProjection_eq_self_iff.mpr hv]
  exact (twoProjectionPlane D v).add_mem ((twoProjectionPlane D v).smul_mem _
    ((twoProjectionPlane D v).smul_mem _ hv')) ((twoProjectionPlane D v).smul_mem _
    ((twoProjectionPlane D v).sub_mem hv' ((twoProjectionPlane D v).smul_mem _ hv')))



theorem orthogonal_twoProjectionPlanes (A : Submodule 𝕜 H) [A.HasOrthogonalProjection]
    {D : H →L[𝕜] H} (hD : IsIdempotentElem D) (hDA : D† = D)
    (v : ι → H) (hv : Orthonormal 𝕜 v) (t : ι → ℝ)
    (hvA : ∀ i, v i ∈ A) (hE : ∀ i, A.starProjection (D (v i)) = (t i : 𝕜) • v i)
    {i j : ι} (hij : i ≠ j) {x y : H} (hx : x ∈ twoProjectionPlane D (v i))
    (hy : y ∈ twoProjectionPlane D (v j)) : ⟪x, y⟫_𝕜 = 0 := by
  obtain ⟨a, b, rfl⟩ := (mem_twoProjectionPlane_iff D (v i) x).mp hx
  obtain ⟨c, d, rfl⟩ := (mem_twoProjectionPlane_iff D (v j) y).mp hy
  have hAxis : ⟪v i, v j⟫_𝕜 = 0 := hv.2 hij
  have hAxis' : ⟪v i, D (v j)⟫_𝕜 = 0 := by
    rw [inner_projection_eigen A v t hvA hE, hAxis, mul_zero]
  have hCross : ⟪v i - D (v i), D (v j)⟫_𝕜 = 0 := by
    rw [← inner_conj_symm, inner_D_apply_complement D hD hDA, map_zero]
  simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
    inner_D_apply_complement D hD hDA, inner_D_both D hD hDA, inner_complement_both D hD hDA,
    hCross, hAxis', hAxis, mul_zero, sub_self, add_zero]

omit [CompleteSpace H] in
theorem twoProjectionPlane_le_span (A : Submodule 𝕜 H) (D : H →L[𝕜] H) {v : H} (hv : v ∈ A) :
    twoProjectionPlane D v ≤ twoProjectionSpan A D := by
  have hleft : A ≤ twoProjectionSpan A D := le_sup_left
  have hright : A.map D.toLinearMap ≤ twoProjectionSpan A D := le_sup_right
  have hD := hright (show D v ∈ A.map D.toLinearMap from ⟨v, hv, rfl⟩)
  apply span_le.mpr
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with hx | hx
  · rwa [hx]
  · rw [hx]
    exact (twoProjectionSpan A D).sub_mem (hleft hv) hD

/-- Exhaust the whole space by the finite interaction planes and two common eigenspaces. -/
theorem twoProjection_decompose (A : Submodule 𝕜 H) [FiniteDimensional 𝕜 A]
    (D : H →L[𝕜] H) (hD : IsIdempotentElem D) (hDA : D† = D) (x : H) :
    ∃ (f : Fin (Module.finrank 𝕜 A) → H) (u v : H),
      (∀ i, f i ∈ twoProjectionPlane D (projectionAxes A hDA i)) ∧
      u ∈ (twoProjectionSpan A D)ᗮ ∧ v ∈ (twoProjectionSpan A D)ᗮ ∧
      A.starProjection u = 0 ∧ A.starProjection v = 0 ∧ D u = u ∧ D v = 0 ∧
      ⟪u, v⟫_𝕜 = 0 ∧ (∑ i, f i) + u + v = x := by
  let K := twoProjectionSpan A D
  obtain ⟨c, d, hcd⟩ := exists_sum_twoProjectionSpan (projectionAxes_span A hDA)
    (K.starProjection_apply_mem x)
  obtain ⟨u, v, hu, hv, hup, hvp, hDu, hDv, huv, hre⟩ :=
    twoProjectionSpan_remainder_decompose A hD hDA (K.sub_starProjection_mem_orthogonal x)
  refine ⟨fun i ↦ c i • D (projectionAxes A hDA i) +
    d i • (projectionAxes A hDA i - D (projectionAxes A hDA i)), u, v, ?_, hu, hv,
    hup, hvp, hDu, hDv, huv, ?_⟩
  · intro i
    exact (mem_twoProjectionPlane_iff D _ _).mpr ⟨c i, d i, rfl⟩
  · rw [hcd, add_assoc, hre]
    abel

end FiberDecomposition

end SchauderBasisOrbits

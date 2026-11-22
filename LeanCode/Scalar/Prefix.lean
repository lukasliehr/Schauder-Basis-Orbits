module

public import LeanCode.Scalar.Data

@[expose] public section

open Matrix
open scoped MatrixOrder ComplexOrder

namespace SchauderBasisOrbits.Scalar

lemma truncCoeff_cons {𝕜 : Type*} [RCLike 𝕜] {n : ℕ} (k : ℕ) (t : 𝕜)
    (c : Fin n → 𝕜) :
    truncCoeff (k + 1) (Fin.cons t c : Fin (n + 1) → 𝕜) = Fin.cons t (truncCoeff k c) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [truncCoeff]
  · simp only [truncCoeff, Fin.cons_succ, Fin.val_succ, Nat.add_lt_add_iff_right]

lemma pb_complexify {n : ℕ} {B : Matrix (Fin n) (Fin n) ℝ} {K : ℝ}
    (h : PB B K) : PB (complexify B) K := by
  refine ⟨h.1, fun k hk c => ?_⟩
  have hre : (fun i => (truncCoeff k c i).re) =
      truncCoeff k (fun i => (c i).re) := by
    funext i
    by_cases hi : i.val < k <;> simp [truncCoeff, hi]
  have him : (fun i => (truncCoeff k c i).im) =
      truncCoeff k (fun i => (c i).im) := by
    funext i
    by_cases hi : i.val < k <;> simp [truncCoeff, hi]
  rw [qform_complexify, qform_complexify, hre, him, mul_add]
  exact add_le_add (h.2 k hk _) (h.2 k hk _)

lemma pb_of_complexify {n : ℕ} {B : Matrix (Fin n) (Fin n) ℝ} {K : ℝ}
    (h : PB (complexify B) K) : PB B K := by
  refine ⟨h.1, fun k hk c => ?_⟩
  have hh := h.2 k hk (fun i => (c i : ℂ))
  have htr : truncCoeff k (fun i => (c i : ℂ)) = fun i => (↑(truncCoeff (𝕜 := ℝ) k c i) : ℂ) := by
    funext i
    by_cases hi : i.val < k <;> simp [truncCoeff, hi]
  rw [htr, qform_complexify, qform_complexify] at hh
  simpa [qform] using hh

namespace Data

variable {r n : ℕ} (D : Data r n)

/-- Write the augmented quadratic form as the centered form plus the squared constant part. -/
lemma qform_gram_cons (t : ℝ) (c : Fin n → ℝ) :
    qform D.gram (Fin.cons t c) = qform D.centerGram c +
      D.mass * (t + (D.meanColumn ⬝ᵥ c) / D.mass) ^ 2 := by
  rw [qform, D.gram_mulVec_cons]
  simp only [RCLike.re_to_real, star_trivial, dotProduct, Fin.sum_univ_succ, Fin.cons_zero,
    Fin.cons_succ, mul_add, Finset.sum_add_distrib]
  simp only [qform, RCLike.re_to_real, star_trivial, D.centerGram_mulVec, dotProduct,
    mul_sub, Finset.sum_sub_distrib]
  have hsum (f : Fin n → ℝ) (a b : ℝ) :
      ∑ x, c x * (a * (f x * b)) = a * (∑ x, c x * f x) * b := by
    rw [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hsum]
  have hcomm : ∑ x, c x * D.meanColumn x = ∑ x, D.meanColumn x * c x := by
    exact Finset.sum_congr rfl (fun i hi => mul_comm _ _)
  have hcross : (∑ x, c x * (D.meanColumn x * t)) = (∑ x, c x * D.meanColumn x) * t := by
    simp only [← mul_assoc, Finset.sum_mul]
  rw [hcross, hcomm]
  field_simp [D.mass_pos.ne']
  ring

/-- A prefix bound on the augmented Gram implies the same bound on the centered Gram. -/
lemma centerGram_pb_of_gram_pb {K : ℝ} (h : PB D.gram K) : PB D.centerGram K := by
  refine ⟨h.1, fun k hk c => ?_⟩
  let t := -((D.meanColumn ⬝ᵥ c) / D.mass)
  have hpre := h.2 (k + 1) (Nat.succ_le_succ hk) (Fin.cons t c)
  rw [truncCoeff_cons, D.qform_gram_cons, D.qform_gram_cons] at hpre
  simp only [t, neg_add_cancel, zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero] at hpre
  have hres : 0 ≤ D.mass * (t + (D.meanColumn ⬝ᵥ truncCoeff k c) / D.mass) ^ 2 :=
    mul_nonneg D.mass_pos.le (sq_nonneg _)
  linarith

lemma centerLp_hPrefix_of_gram_pb {K : ℝ} (h : PB D.gram K) :
    HPrefix (𝕜 := ℂ) D.centerLp K := by
  rw [hPrefix_iff_pb, D.gram_centerLp]
  apply pb_complexify
  have h₀ := D.centerGram_pb_of_gram_pb h
  refine ⟨h₀.1, fun j hj c => ?_⟩
  simp only [normalizedGram, qform_smul]
  rw [mul_left_comm (K ^ 2)]
  exact mul_le_mul_of_nonneg_left (h₀.2 j hj c) (inv_nonneg.mpr D.mass_pos.le)

lemma augLp_hPrefix_of_gram_pb {K : ℝ} (h : PB D.gram K) :
    HPrefix (𝕜 := ℂ) D.augLp K := by
  rw [hPrefix_iff_pb, D.gram_augLp, ← D.complexify_gram]
  have h₀ := pb_complexify h
  refine ⟨h₀.1, fun j hj c => ?_⟩
  simp only [qform_smul]
  rw [mul_left_comm (K ^ 2)]
  exact mul_le_mul_of_nonneg_left (h₀.2 j hj c) (inv_nonneg.mpr D.mass_pos.le)


private lemma truncCoeff_one_eq_single (c : Fin (n + 1) → ℝ) :
    truncCoeff 1 c = Pi.single 0 (c 0) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [truncCoeff]
  · simp [truncCoeff]

private lemma qform_real_smul_vec (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (a : ℝ) (c : Fin (n + 1) → ℝ) :
    qform B (a • c) = a ^ 2 * qform B c := by
  simp only [qform, RCLike.re_to_real, star_trivial, Matrix.mulVec_smul, smul_dotProduct,
    dotProduct_smul, smul_eq_mul]
  ring

private lemma qform_trunc_one (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (c : Fin (n + 1) → ℝ) :
    qform B (truncCoeff 1 c) = B 0 0 * (c 0) ^ 2 := by
  rw [truncCoeff_one_eq_single]
  have h : (Pi.single 0 (c 0) : Fin (n + 1) → ℝ) = c 0 • Pi.single 0 1 := by
    funext i
    by_cases hi : i = 0 <;> simp [Pi.single_apply, hi]
  rw [h, qform_real_smul_vec]
  simp [qform, mul_comm]

lemma qform_firstCut (c : Fin (n + 1) → ℝ) :
    qform D.gram (truncCoeff 1 c) = D.mass * (c 0) ^ 2 := by
  rw [qform_trunc_one, D.gram_diag]

/-- Squared norm bound of the prefix consisting only of the constant vector. -/
lemma firstCut_qform_le (c : Fin (n + 1) → ℝ) :
    qform D.gram (truncCoeff 1 c) ≤ (1 + D.gain) * qform D.gram c := by
  by_cases hc : c = 0
  · rw [D.qform_firstCut, hc]
    simp [qform]
  have hq : 0 < qform D.gram c := qform_pos D.gram_posDef hc
  let v : Fin (n + 1) → ℝ := Pi.single 0 1
  let s := c 0 / qform D.gram c
  have hi := qform_inv_ge D.gram_posDef v (s • c)
  simp only [star_trivial, RCLike.re_to_real, dotProduct_smul, qform_real_smul_vec] at hi
  have hv : v ⬝ᵥ c = c 0 := by simp [v]
  have hv' : qform D.gram⁻¹ v = D.gram⁻¹ 0 0 := by
    simp [v, qform]
  rw [hv, hv', smul_eq_mul] at hi
  have hopt : 2 * (s * c 0) - s ^ 2 * qform D.gram c =
      (c 0) ^ 2 / qform D.gram c := by
    change 2 * (_ / _ * _) - (_ / _) ^ 2 * _ = _
    field_simp [hq.ne']
    ring
  rw [hopt] at hi
  have he := (div_le_iff₀ hq).mp hi
  rw [D.qform_firstCut, ← D.mass_mul_gram_inv_zero_zero]
  nlinarith only [mul_le_mul_of_nonneg_left he D.mass_pos.le]

/-- The first-prefix bound is attained at the inverse-Gram column for the constant. -/
lemma firstCut_bound_attained :
    ∃ c : Fin (n + 1) → ℝ, c ≠ 0 ∧
      qform D.gram (truncCoeff 1 c) = (1 + D.gain) * qform D.gram c := by
  let v : Fin (n + 1) → ℝ := Pi.single 0 1
  let c := D.gram⁻¹ *ᵥ v
  have h : D.gram *ᵥ c = v := by
    dsimp [c]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _
      ((Matrix.isUnit_iff_isUnit_det _).1 D.gram_posDef.isUnit), Matrix.one_mulVec]
  have hne : c ≠ 0 := by
    intro hc
    have hh := congrFun h 0
    rw [hc, Matrix.mulVec_zero] at hh
    simp [v] at hh
  have h0 : c 0 = D.gram⁻¹ 0 0 := by
    simp [c, v]
  have hq : qform D.gram c = c 0 := by
    simp [qform, h, v]
  refine ⟨c, hne, ?_⟩
  rw [D.qform_firstCut, hq, ← D.mass_mul_gram_inv_zero_zero, h0]
  ring

end Data

end SchauderBasisOrbits.Scalar

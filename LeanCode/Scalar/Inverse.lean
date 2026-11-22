module

public import LeanCode.Scalar.Copies
public import LeanCode.Scalar.ActivationGeometry

@[expose] public section

open Matrix
open scoped MatrixOrder ComplexOrder

namespace SchauderBasisOrbits.Scalar

namespace Data

variable {r n : ℕ} (D : Data r n)

lemma mass_qform_gram_inv_cons (s : ℝ) (c : Fin n → ℝ) :
    D.mass * qform D.gram⁻¹ (Fin.cons s c) =
      s ^ 2 + qform D.normalizedGram⁻¹ (c - s • D.normalizedMean) := by
  let b := D.meanColumn
  let y := c - (s / D.mass) • b
  let z := D.centerGram⁻¹ *ᵥ y
  have hy : c - s • D.normalizedMean = y := by
    simp [y, b, normalizedMean, div_eq_mul_inv, smul_smul]
  rw [hy]
  have hz : D.gram⁻¹ *ᵥ Fin.cons s c = Fin.cons ((s - b ⬝ᵥ z) / D.mass) z :=
    D.gram_inv_mulVec_cons s c
  simp only [qform, RCLike.re_to_real, star_trivial, hz]
  rw [show Fin.cons s c ⬝ᵥ Fin.cons ((s - b ⬝ᵥ z) / D.mass) z =
    s * ((s - b ⬝ᵥ z) / D.mass) + c ⬝ᵥ z by simp [dotProduct, Fin.sum_univ_succ]]
  rw [D.normalizedGram_inv, Matrix.smul_mulVec]
  change D.mass * (s * ((s - b ⬝ᵥ z) / D.mass) + c ⬝ᵥ z) =
    s ^ 2 + y ⬝ᵥ (D.mass • z)
  rw [dotProduct_smul]
  simp only [y, sub_dotProduct, smul_dotProduct, smul_eq_mul]
  field_simp [D.mass_pos.ne']
  ring

private lemma qform_one_cons (s : ℝ) (c : Fin n → ℝ) :
    qform (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (Fin.cons s c) =
      s ^ 2 + qform (1 : Matrix (Fin n) (Fin n) ℝ) c := by
  simp only [qform, RCLike.re_to_real, star_trivial, Matrix.one_mulVec, dotProduct,
    Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, pow_two]

/-- The scalar inverse estimate uses the centered inverse bound and the gain together. -/
lemma gram_inv_le_of_normalized_inverse_le {h : ℝ} (hh : 0 ≤ h)
    (hC : D.normalizedGram⁻¹ ≤ h • 1) :
    D.gram⁻¹ ≤ ((1 + D.gain + h) / D.mass) • 1 := by
  let C := D.normalizedGram⁻¹
  let R := CFC.sqrt C
  have hCpos := D.normalizedGram_posDef.inv
  have hR : Rᴴ = R := (CFC.sqrt_nonneg C).posSemidef.isHermitian
  have hRC : Rᴴ * R = C := by rw [hR, sqrt_mul_sqrt_of_posDef hCpos]
  have hqr (x : Fin n → ℝ) : qform C x = ‖WithLp.toLp 2 (R *ᵥ x)‖ ^ 2 := by
    rw [← hRC, qform_conjTranspose_mul_self]
  apply matrix_le_of_qform_le D.gram_posDef.inv.isHermitian
    (Matrix.isHermitian_one.smul (IsSelfAdjoint.all _))
  intro v
  let s := v 0
  let c := fun i : Fin n => v i.succ
  have hv : v = Fin.cons s c := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  rw [hv, qform_smul, qform_one_cons]
  have htr :
      qform C (c - s • D.normalizedMean) ≤
        (h + D.gain) * (s ^ 2 + qform (1 : Matrix (Fin n) (Fin n) ℝ) c) := by
    let x := WithLp.toLp 2 (R *ᵥ c)
    let y := WithLp.toLp 2 (R *ᵥ D.normalizedMean)
    have hu : ‖x‖ ^ 2 ≤ h * qform (1 : Matrix (Fin n) (Fin n) ℝ) c := by
      rw [← hqr]
      simpa only [qform_smul] using qform_mono hC c
    have hz : ‖y‖ ^ 2 = D.gain := by
      rw [← hqr]
      simp [gain, qform, C]
    have hx : ‖x‖ ≤ Real.sqrt h * ‖WithLp.toLp 2 c‖ := by
      apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
      rw [mul_pow, Real.sq_sqrt hh]
      simpa only [qform_one] using hu
    rw [hqr, Matrix.mulVec_sub, Matrix.mulVec_smul]
    change ‖x - s • y‖ ^ 2 ≤ _
    have hnorm : ‖x - s • y‖ ≤ Real.sqrt h * ‖WithLp.toLp 2 c‖ + |s| * ‖y‖ := by
      refine (norm_sub_le _ _).trans ?_
      rw [norm_smul, Real.norm_eq_abs]
      exact add_le_add hx le_rfl
    have hsq := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    rw [qform_one]
    refine hsq.trans ?_
    rw [← hz]
    have hS := Real.sq_sqrt hh
    have hp := congrArg (fun z : ℝ => z * ‖WithLp.toLp 2 c‖ ^ 2) hS
    have ha := congrArg (fun z : ℝ => z * ‖y‖ ^ 2) (sq_abs s)
    have hp' := congrArg (fun z : ℝ => z * |s| ^ 2) hS
    have ha' := congrArg (fun z : ℝ => z * h) (sq_abs s)
    nlinarith only [hp, hp', ha, ha', sq_nonneg (Real.sqrt h * |s| - ‖y‖ * ‖WithLp.toLp 2 c‖)]
  have hbase : 0 ≤ qform (1 : Matrix (Fin n) (Fin n) ℝ) c :=
    qform_nonneg Matrix.PosDef.one.posSemidef _
  have hbound : D.mass * qform D.gram⁻¹ (Fin.cons s c) ≤
      (1 + D.gain + h) * (s ^ 2 + qform (1 : Matrix (Fin n) (Fin n) ℝ) c) := by
    rw [D.mass_qform_gram_inv_cons]
    linarith only [htr, hbase]
  rw [div_mul_eq_mul_div, le_div_iff₀ D.mass_pos]
  simpa [mul_comm (qform D.gram⁻¹ _)] using hbound


/-- Cauchy--Schwarz for the mean functional in the centered Gram metric. -/
lemma normalizedMean_sq_le_gain (c : Fin n → ℝ) :
    (D.normalizedMean ⬝ᵥ c) ^ 2 ≤ D.gain * qform D.normalizedGram c := by
  by_cases hc : c = 0
  · simp [hc, qform]
  have hq : 0 < qform D.normalizedGram c := qform_pos D.normalizedGram_posDef hc
  let a := D.normalizedMean ⬝ᵥ c
  let t := a / qform D.normalizedGram c
  have hi := qform_inv_ge D.normalizedGram_posDef D.normalizedMean (t • c)
  have hscale :
      qform D.normalizedGram (t • c) = t ^ 2 * qform D.normalizedGram c := by
    simp only [qform, RCLike.re_to_real, star_trivial, Matrix.mulVec_smul, smul_dotProduct,
      dotProduct_smul, smul_eq_mul]
    ring
  rw [hscale] at hi
  simp only [RCLike.re_to_real, star_trivial, dotProduct_smul, smul_eq_mul] at hi
  change 2 * (t * a) - t ^ 2 * qform D.normalizedGram c ≤ D.gain at hi
  have ha : 2 * (t * a) - t ^ 2 * qform D.normalizedGram c = a ^ 2 / qform D.normalizedGram c := by
    dsimp [t]
    field_simp [hq.ne']
    ring
  rw [ha] at hi
  exact (div_le_iff₀ hq).mp hi

lemma qform_gram_cons_div_mass (s : ℝ) (c : Fin n → ℝ) :
    qform D.gram (Fin.cons s c) / D.mass =
      (s + D.normalizedMean ⬝ᵥ c) ^ 2 + qform D.normalizedGram c := by
  rw [D.qform_gram_cons, normalizedMean, normalizedGram, qform_smul, smul_dotProduct, smul_eq_mul]
  field_simp [D.mass_pos.ne']
  ring

end Data


private lemma inv_smul_of_posDef {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M : Matrix ι ι ℝ} (hM : M.PosDef) {c : ℝ} (hc : 0 < c) :
    (c • M)⁻¹ = c⁻¹ • M⁻¹ := by
  let u : ℝˣ := Units.mk0 c hc.ne'
  have h := Matrix.inv_smul' (A := M) u ((Matrix.isUnit_iff_isUnit_det _).1 hM.isUnit)
  simpa [u, Units.smul_def, Units.val_inv_eq_inv_val] using h

lemma Data.gram_inverse_norm_bound {r n : ℕ} (D : Data r n)
    (he : 0 < D.loss) (hfloor : D.loss ^ 2 • 1 ≤ D.gram) :
    opNorm D.gram⁻¹ ≤ 1 / D.loss ^ 2 := by
  have h := matrix_inv_le_inv (Matrix.PosDef.one.smul (sq_pos_of_pos he)) hfloor
  rw [inv_smul_of_posDef Matrix.PosDef.one (sq_pos_of_pos he), inv_one] at h
  exact (opNorm_psd_le_iff D.gram_posDef.inv.posSemidef).2 (by simpa only [one_div] using h)

lemma copies_normalized_inv_le {r n L : ℕ} (D : Data r n) (hL : 0 < L) {h : ℝ}
    (hD : D.centerGram⁻¹ ≤ h • 1) :
    (copies D L hL).normalizedGram⁻¹ ≤ (D.mass * h) • 1 := by
  let K := (copies D L hL).normalizedGram⁻¹
  have hK := (copies D L hL).normalizedGram_posDef.inv.isHermitian
  apply matrix_le_of_qform_le hK (Matrix.isHermitian_one.smul (IsSelfAdjoint.all _))
  intro x
  rw [copies_normalizedGram_inv, qform_blockCopies, qform_smul]
  rw [← blockCopies_one (n := n) L]
  rw [qform_blockCopies, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro b hb
  rw [D.normalizedGram_inv, qform_smul, mul_assoc]
  exact mul_le_mul_of_nonneg_left
    (by simpa only [qform_smul] using qform_mono hD (fun j => x (finProdFinEquiv (b, j))))
    D.mass_pos.le

/-- The copied activated system preserves the inverse diagonal estimate. -/
lemma copied_activation_inverse_diagonal {r n m L : ℕ} (D : Data r n)
    {p C : ℝ} (A : ActivationSet p) (hp : 0 ≤ p) (hC : 0 ≤ C)
    (hmax : ∀ j : Fin (n + 1), D.gram⁻¹ j j - 1 ≤ C)
    (hpC : p * C ≤ D.loss / 100)
    (Y : Fin (m + 1) → ℤ) (hY₀ : Y 0 = 0) (hY : Function.Injective Y)
    (hL : 0 < L) (he' : 0 < (copies (activate D A Y hY₀ hY) L hL).loss)
    (he'small : (copies (activate D A Y hY₀ hY) L hL).loss ≤ 1 / 400)
    (he_le : D.loss ≤ 12 * (copies (activate D A Y hY₀ hY) L hL).loss)
    (k : Fin (L * activatedCount n m)) :
    (copies (activate D A Y hY₀ hY) L hL).gram⁻¹ k.succ k.succ ≤
      1 + 2 * (copies (activate D A Y hY₀ hY) L hL).loss := by
  let E := activate D A Y hY₀ hY
  let F := copies E L hL
  obtain ⟨⟨b, j⟩, rfl⟩ :=
    (finProdFinEquiv : Fin L × Fin (activatedCount n m) ≃ Fin (L * activatedCount n m)).surjective k
  rw [copies_gram_inv_diagonal]
  have hd := activate_centerGram_inv_diagonal_le D A Y hp hY₀ hY j
  change E.centerGram⁻¹ j j ≤ _ at hd
  have hi : E.mass * E.centerGram⁻¹ j j ≤ E.mass * (1 + p * C) := by
    apply mul_le_mul_of_nonneg_left _ E.mass_pos.le
    exact hd.trans (add_le_add_right (mul_le_mul_of_nonneg_left (hmax _) hp) _)
  have hFM : 1 - F.loss = F.mass := by simp [Data.loss]
  have h := inverse_diagonal_step_arithmetic he' he'small he_le hpC E.mass_le_one
    (by positivity : 0 ≤ 1 + p * C) hi
  rwa [hFM] at h

/-- The copied activated system preserves the loss-squared lower Gram bound. -/
lemma copied_activation_gram_floor {r n m L : ℕ} (D : Data r n)
    {p Z₀ : ℝ} (A : ActivationSet p)
    (he : 0 < D.loss) (hesmall : D.loss ≤ 1 / 400) (hfloor : D.loss ^ 2 • 1 ≤ D.gram)
    (Y : Fin (m + 1) → ℤ) (hY₀ : Y 0 = 0) (hY : Function.Injective Y) (hL : 0 < L)
    (he' : 0 < (copies (activate D A Y hY₀ hY) L hL).loss)
    (hdec : (copies (activate D A Y hY₀ hY) L hL).loss ≤ D.loss - 3 * D.loss ^ 2 / 4)
    (hZ : (copies (activate D A Y hY₀ hY) L hL).gain ≤ Z₀)
    (hZ₀ : Z₀ ≤ (1 / 400 : ℝ) ^ 2 / 3) :
    (copies (activate D A Y hY₀ hY) L hL).loss ^ 2 • 1 ≤
      (copies (activate D A Y hY₀ hY) L hL).gram := by
  let E := activate D A Y hY₀ hY
  let F := copies E L hL
  let h := opNorm D.gram⁻¹
  have hh : 0 ≤ h := norm_nonneg _
  have hC₁ := activate_centerGram_inverse_le_opNorm D A Y hY₀ hY
  have hC₂ := copies_normalized_inv_le E hL hC₁
  have hC := F.gram_inv_le_of_normalized_inverse_le (mul_nonneg E.mass_pos.le hh) hC₂
  have hFM : 1 - F.loss = F.mass := by simp [Data.loss]
  have hnum := inverse_floor_step_arithmetic he he' hesmall hdec hZ₀
    (D.gram_inverse_norm_bound he hfloor)
  rw [hFM] at hnum
  have hcoef : (1 + F.gain + E.mass * h) / F.mass ≤ 1 / F.loss ^ 2 := by
    apply le_trans (b := (h + 1 + Z₀) / F.mass) _ hnum
    have hM := mul_le_mul_of_nonneg_right E.mass_le_one hh
    exact div_le_div_of_nonneg_right (by linarith only [hZ, hM]) F.mass_pos.le
  have hfloor' : F.gram⁻¹ ≤ (1 / F.loss ^ 2) • 1 := by
    refine hC.trans ?_
    apply matrix_le_of_qform_le (Matrix.isHermitian_one.smul (IsSelfAdjoint.all _))
      (Matrix.isHermitian_one.smul (IsSelfAdjoint.all _))
    intro x
    rw [qform_smul, qform_smul]
    exact mul_le_mul_of_nonneg_right hcoef (qform_nonneg Matrix.PosDef.one.posSemidef _)
  have hi := matrix_inv_le_inv F.gram_posDef.inv hfloor'
  rw [inv_smul_of_posDef Matrix.PosDef.one (by positivity : 0 < 1 / F.loss ^ 2), inv_one,
    Matrix.nonsing_inv_nonsing_inv _
      ((Matrix.isUnit_iff_isUnit_det _).1 F.gram_posDef.isUnit), inv_div, div_one] at hi
  exact hi

end SchauderBasisOrbits.Scalar

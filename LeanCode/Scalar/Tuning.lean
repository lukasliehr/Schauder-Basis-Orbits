import LeanCode.Scalar.MatrixMix
import LeanCode.Scalar.Prefix
import LeanCode.Fourier.TorusPolynomial

open MeasureTheory Complex Matrix
open scoped MatrixOrder ComplexOrder ComplexConjugate Topology

namespace SchauderBasisOrbits.Scalar

noncomputable local instance tuningCircleMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩

local instance tuningCircleProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure (@AddCircle.haarAddCircle 1 _))

variable {r n : ℕ} (P : PolynomialData r n)

/-- Affine tuning toward Haar measure keeps a polynomial positive and even. -/
noncomputable def tune (β : ℝ) (hβ : β ∈ Set.Icc 0 1) : PolynomialData r n where
  toData := {
    size_pos := P.size_pos
    w := fun x => β + (1 - β) * P.w x
    measurable_w := measurable_const.add (measurable_const.mul P.measurable_w)
    lower := P.lower
    lower_pos := P.lower_pos
    lower_le x := by
      have h₁ := mul_le_mul_of_nonneg_left P.toData.lower_le_one hβ.1
      have h₂ := mul_le_mul_of_nonneg_left (P.lower_le x) (sub_nonneg.mpr hβ.2)
      nlinarith only [h₁, h₂]
    le_one x := by
      have h := mul_le_mul_of_nonneg_left (P.le_one x) (sub_nonneg.mpr hβ.2)
      linarith
    even_w x := by rw [P.even_w]
    mode := P.mode
    mode_inj := P.mode_inj
    mode_ne_zero := P.mode_ne_zero
  }
  poly := (β : ℂ) • 1 + ((1 - β : ℝ) : ℂ) • P.poly
  eval_poly x := by
    simp only [evalTorusPoly_add, evalTorusPoly_smul, evalTorusPoly_one, P.eval_poly,
      mul_one, ofReal_add, ofReal_mul]

lemma tune_mass (β : ℝ) (hβ : β ∈ Set.Icc 0 1) :
    (tune P β hβ).toData.mass = β + (1 - β) * P.toData.mass := by
  change (∫ x, β + (1 - β) * P.w x) = _
  rw [integral_add (integrable_const _) (P.toData.integrable_w.const_mul _), integral_const_mul]
  simp [Data.mass]

lemma tune_loss (β : ℝ) (hβ : β ∈ Set.Icc 0 1) :
    (tune P β hβ).toData.loss = (1 - β) * P.toData.loss := by
  rw [Data.loss, tune_mass, Data.loss]
  ring

lemma tune_gram (β : ℝ) (hβ : β ∈ Set.Icc 0 1) :
    (tune P β hβ).toData.gram = gramMix P.toData.gram β := by
  let D := P.toData
  let E := (tune P β hβ).toData
  have hc : E.complexGram = (β : ℂ) • 1 + ((1 - β : ℝ) : ℂ) • D.complexGram := by
    rw [← charGram_one D.augMode_inj]
    ext i j
    let f (x : UnitAddTorus (Fin r)) :=
      conj (torusChar (D.augMode i) x) * torusChar (D.augMode j) x
    change (∫ x, (↑(β + (1 - β) * D.w x) : ℂ) * conj (torusChar (D.augMode i) x) *
      torusChar (D.augMode j) x) =
      (β : ℂ) * (∫ x, (1 : ℂ) * conj (torusChar (D.augMode i) x) * torusChar (D.augMode j) x) +
      ((1 - β : ℝ) : ℂ) * (∫ x, (D.w x : ℂ) * conj (torusChar (D.augMode i) x) *
        torusChar (D.augMode j) x)
    have hf : Integrable f :=
      Integrable.of_bound (((Complex.continuous_conj.comp (continuous_torusChar _)).mul
        (continuous_torusChar _)).measurable.aestronglyMeasurable) 1
        (Filter.Eventually.of_forall (fun x => by simp [f, norm_mul]))
    have hf' : Integrable (fun x => (D.w x : ℂ) * f x) := by
      have hh := charGram_integrable D.w D.measurable_w 1
        (fun x => by simpa [abs_of_nonneg (D.w_nonneg x)] using D.le_one x)
        (D.augMode i) (D.augMode j)
      simpa [f, mul_assoc] using hh
    simp only [one_mul, mul_assoc]
    rw [← integral_const_mul, ← integral_const_mul,
      ← integral_add (hf.const_mul _) (hf'.const_mul _)]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun x => by
      simp only [f, ofReal_add, ofReal_mul]
      ring)
  have hcc : complexify E.gram = complexify (gramMix D.gram β) := by
    rw [E.complexify_gram, hc, gramMix, ← D.complexify_gram]
    ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, complexify_apply, smul_eq_mul,
      ofReal_add, ofReal_mul, Matrix.one_apply, apply_ite, ofReal_one, ofReal_zero]
  ext i j
  have h := congrFun (congrFun hcc i) j
  exact Complex.ofReal_injective h

private lemma pb_one_of_one_le {K : ℝ} (hK : 1 ≤ K) :
    PB (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) K := by
  refine ⟨zero_le_one.trans hK, fun k hk c => ?_⟩
  rw [qform_one, qform_one, PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
  have hsum : ∑ i, ‖truncCoeff k c i‖ ^ 2 ≤ ∑ i, ‖c i‖ ^ 2 := by
    apply Finset.sum_le_sum
    intro i hi
    by_cases h : i.val < k <;> simp [truncCoeff, h, sq_nonneg]
  have hs : 1 ≤ K ^ 2 := by
    simpa using pow_le_pow_left₀ zero_le_one hK 2
  exact hsum.trans (le_mul_of_one_le_left (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) hs)

lemma tune_pb {K : ℝ} (hK : 1 ≤ K) (hPB : PB P.toData.gram K) {β : ℝ}
    (hβ : β ∈ Set.Icc 0 1) : PB (tune P β hβ).toData.gram K := by
  rw [tune_gram, gramMix]
  exact (pb_one_of_one_le (n := n) hK).add_smul hPB hβ.1 (sub_nonneg.mpr hβ.2)

lemma tune_floor {β : ℝ} (hβ : β ∈ Set.Icc 0 1)
    (h : P.toData.loss ^ 2 • 1 ≤ P.toData.gram) :
    (tune P β hβ).toData.loss ^ 2 • 1 ≤ (tune P β hβ).toData.gram := by
  rw [tune_loss, tune_gram]
  apply matrix_le_of_qform_le (Matrix.isHermitian_one.smul (IsSelfAdjoint.all _))
    (gramMix_posDef P.toData.gram_posDef hβ.1 hβ.2).isHermitian
  intro x
  rw [qform_smul, gramMix_qform]
  have hq := qform_mono h x
  rw [qform_smul] at hq
  have hs : (1 - β) ^ 2 ≤ 1 - β := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hβ.2) hβ.1]
  let b := qform (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) x
  have hb : 0 ≤ b := qform_nonneg Matrix.PosDef.one.posSemidef _
  rw [mul_pow]
  have hone : (1 - β) ^ 2 * P.toData.loss ^ 2 * b ≤ (1 - β) * P.toData.loss ^ 2 * b :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hs (sq_nonneg _)) hb
  change _ * b ≤ β * b + (1 - β) * qform P.toData.gram x
  have htwo := mul_le_mul_of_nonneg_left hq (sub_nonneg.mpr hβ.2)
  change (1 - β) * (P.toData.loss ^ 2 * b) ≤ _ at htwo
  linarith only [hone, htwo, mul_nonneg hβ.1 hb]

lemma tune_inverse_diagonal {β : ℝ} (hβ : β ∈ Set.Icc 0 1)
    (h : ∀ i : Fin n, P.toData.gram⁻¹ i.succ i.succ ≤ 1 + 2 * P.toData.loss)
    (i : Fin n) :
    (tune P β hβ).toData.gram⁻¹ i.succ i.succ ≤ 1 + 2 * (tune P β hβ).toData.loss := by
  rw [tune_loss, tune_gram]
  have hm := gramMix_inv_le_mix_inv P.toData.gram_posDef hβ.1 hβ.2
  have hd := Matrix.PosSemidef.diag_nonneg (Matrix.le_iff.mp hm) (i := i.succ)
  rw [Matrix.sub_apply, sub_nonneg] at hd
  refine hd.trans ?_
  have ho : gramMix P.toData.gram⁻¹ β i.succ i.succ = β + (1 - β) * P.toData.gram⁻¹ i.succ i.succ := by
    simp [gramMix]
  rw [ho]
  nlinarith only [mul_le_mul_of_nonneg_left (h i) (sub_nonneg.mpr hβ.2)]

/-- Gain formula extended to all parameters so that continuity can be used on the interval. -/
noncomputable def tuneGain (β : ℝ) : ℝ :=
  (β + (1 - β) * P.toData.mass) * (gramMix P.toData.gram β)⁻¹ 0 0 - 1

lemma tuneGain_eq (β : ℝ) (hβ : β ∈ Set.Icc 0 1) :
    tuneGain P β = (tune P β hβ).toData.gain := by
  unfold tuneGain
  rw [← tune_mass P β hβ, ← tune_gram P β hβ]
  rw [(tune P β hβ).toData.mass_mul_gram_inv_zero_zero]
  ring

lemma continuousOn_tuneGain : ContinuousOn (tuneGain P) (Set.Icc 0 1) := by
  intro β hβ
  have hcont : Continuous (gramMix P.toData.gram) := by unfold gramMix; fun_prop
  have hdet : (gramMix P.toData.gram β).det ≠ 0 :=
    isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp
      (gramMix_posDef P.toData.gram_posDef hβ.1 hβ.2).isUnit)
  have hinv : ContinuousAt Inv.inv (gramMix P.toData.gram β) :=
    continuousAt_matrix_inv _ (by simp only [Ring.inverse_eq_inv']; exact continuousAt_inv₀ hdet)
  have hentry : Continuous (fun B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ => B 0 0) :=
    (continuous_apply _).comp (continuous_apply _)
  have h := hentry.continuousAt.comp (hinv.comp hcont.continuousAt)
  have ht : Continuous (fun β : ℝ => β + (1 - β) * P.toData.mass) := by fun_prop
  exact ((ht.continuousAt.mul h).sub continuousAt_const).continuousWithinAt

theorem exists_tune_gain {z : ℝ} (hz : 0 < z) (hz' : z < P.toData.gain)
    (he : 0 < P.toData.loss) :
    ∃ β : ℝ, ∃ hβ : β ∈ Set.Icc 0 1, (tune P β hβ).toData.gain = z ∧
      0 < (tune P β hβ).toData.loss ∧ (tune P β hβ).toData.loss ≤ P.toData.loss := by
  have h₀ : tuneGain P 0 = P.toData.gain := by
    simp only [tuneGain, gramMix, zero_smul, sub_zero, one_smul, zero_add, one_mul]
    rw [P.toData.mass_mul_gram_inv_zero_zero]
    ring
  have h₁ : tuneGain P 1 = 0 := by simp [tuneGain, gramMix]
  have hz_mem : z ∈ Set.Icc (tuneGain P 1) (tuneGain P 0) := by
    rw [h₁, h₀]
    exact ⟨hz.le, hz'.le⟩
  obtain ⟨β, hβ, heq⟩ :=
    intermediate_value_Icc' (show (0 : ℝ) ≤ 1 by norm_num) (continuousOn_tuneGain P) hz_mem
  have hβ₁ : β < 1 := by
    refine lt_of_le_of_ne hβ.2 (fun ht => ?_)
    rw [ht, h₁] at heq
    linarith
  refine ⟨β, hβ, (tuneGain_eq P β hβ).symm.trans heq, ?_, ?_⟩
  · rw [tune_loss]
    exact mul_pos (sub_pos.mpr hβ₁) he
  · rw [tune_loss]
    exact mul_le_of_le_one_left he.le (sub_le_self _ hβ.1)

end SchauderBasisOrbits.Scalar

import LeanCode.Scalar.Data
import LeanCode.Scalar.Budgets

open MeasureTheory Matrix Complex
open scoped ComplexConjugate ComplexOrder MatrixOrder

namespace SchauderBasisOrbits.Scalar

noncomputable local instance initialCircleMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

local instance initialCircleProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure (@AddCircle.haarAddCircle 1 _))

private lemma integral_torusChar_zero {ι : Type*} [Fintype ι] {k : ι → ℤ} (hk : k ≠ 0) :
    ∫ x, torusChar k x = 0 := by
  let m : Fin 2 → ι → ℤ := fun i => if i = 0 then 0 else k
  have hm : Function.Injective m := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp_all [m, eq_comm]
  have h := congrFun (congrFun (charGram_one hm) 0) 1
  simpa [charGram, m, Matrix.one_apply] using h

/-- The mode one on the one-coordinate torus. -/
private def initialMode : Fin 1 → ℤ := fun _ => 1

private lemma initialMode_ne_zero : initialMode ≠ 0 := by
  intro h
  have hc := congrFun h 0
  norm_num [initialMode] at hc

private lemma initialMode_add_ne_zero : initialMode + initialMode ≠ 0 := by
  intro h
  have hc := congrFun h 0
  norm_num [initialMode] at hc

/-- The first scalar weight is `1-a+a cos(2πy)`, written as a character real part. -/
noncomputable def initialWeight (a : ℝ) (x : UnitAddTorus (Fin 1)) : ℝ :=
  1 - a + a * (torusChar initialMode x).re

private lemma initialWeight_bounds {a : ℝ} (ha : 0 ≤ a) (x : UnitAddTorus (Fin 1)) :
    1 - 2 * a ≤ initialWeight a x ∧ initialWeight a x ≤ 1 := by
  have h := Complex.abs_re_le_norm (torusChar initialMode x)
  rw [norm_torusChar, abs_le] at h
  exact ⟨by
    unfold initialWeight
    nlinarith [mul_le_mul_of_nonneg_left h.1 ha], by
    unfold initialWeight
    nlinarith [mul_le_mul_of_nonneg_left h.2 ha]⟩

/-- The initial scalar system, with one nonconstant character. -/
noncomputable def initialData (a : ℝ) (ha : 0 < a) (ha' : a ≤ 1 / 400) : Data 1 1 where
  size_pos := by decide
  w := initialWeight a
  measurable_w := by
    unfold initialWeight
    exact (continuous_const.add (continuous_const.mul
      (Complex.continuous_re.comp (continuous_torusChar initialMode)))).measurable
  lower := 1 - 2 * a
  lower_pos := by linarith
  lower_le x := (initialWeight_bounds ha.le x).1
  le_one x := (initialWeight_bounds ha.le x).2
  even_w x := by
    unfold initialWeight
    have hx := Data.torusChar_arg_neg initialMode x
    rw [hx, Complex.conj_re]
  mode := fun _ => initialMode
  mode_inj := fun _ _ _ => Subsingleton.elim _ _
  mode_ne_zero := fun _ => initialMode_ne_zero

lemma initialData_mass (a : ℝ) (ha : 0 < a) (ha' : a ≤ 1 / 400) :
    (initialData a ha ha').mass = 1 - a := by
  have hi : Integrable (torusChar initialMode) := by
    exact Integrable.of_bound (continuous_torusChar _).measurable.aestronglyMeasurable
      1 (Filter.Eventually.of_forall (fun x => (norm_torusChar _ x).le))
  have hir : Integrable (fun x => (torusChar initialMode x).re) := hi.re
  change (∫ x, 1 - a + a * (torusChar initialMode x).re) = _
  have hre : (∫ x, (torusChar initialMode x).re) = 0 := by
    have he := integral_re hi
    change (∫ x, (torusChar initialMode x).re) = (∫ x, torusChar initialMode x).re at he
    rw [he, integral_torusChar_zero initialMode_ne_zero, zero_re]
  rw [integral_add (integrable_const _) (hir.const_mul _), integral_const_mul, hre]
  simp

lemma initialData_loss (a : ℝ) (ha : 0 < a) (ha' : a ≤ 1 / 400) :
    (initialData a ha ha').loss = a := by
  rw [Data.loss, initialData_mass]
  ring

private lemma initialWeight_mul_character (a : ℝ) (x : UnitAddTorus (Fin 1)) :
    (initialWeight a x : ℂ) * torusChar initialMode x =
      ((1 - a : ℝ) : ℂ) * torusChar initialMode x +
      ((a / 2 : ℝ) : ℂ) * torusChar (initialMode + initialMode) x + ((a / 2 : ℝ) : ℂ) := by
  have hre (z : ℂ) : (z.re : ℂ) = (z + conj z) / 2 := by
    apply Complex.ext <;> simp
  have hun : conj (torusChar initialMode x) * torusChar initialMode x = 1 := by
    simp [Complex.conj_mul']
  change (↑(1 - a + a * (torusChar initialMode x).re) : ℂ) * _ = _
  push_cast
  rw [hre, torusChar_add]
  linear_combination (a : ℂ) / 2 * hun

lemma initialData_meanColumn (a : ℝ) (ha : 0 < a) (ha' : a ≤ 1 / 400) (i : Fin 1) :
    (initialData a ha ha').meanColumn i = a / 2 := by
  set D := initialData a ha ha'
  rw [← D.gram_zero_succ]
  have h (k : Fin 1 → ℤ) : Integrable (torusChar k) := by
    exact Integrable.of_bound (continuous_torusChar _).measurable.aestronglyMeasurable
      1 (Filter.Eventually.of_forall (fun x => (norm_torusChar _ x).le))
  have hmoment : (∫ x, (initialWeight a x : ℂ) * torusChar initialMode x) = (a / 2 : ℝ) := by
    have hi₁ : Integrable (fun x => ((1 - a : ℝ) : ℂ) * torusChar initialMode x) :=
      (h _).const_mul _
    have hi₂ : Integrable (fun x => ((a / 2 : ℝ) : ℂ) * torusChar (initialMode + initialMode) x) :=
      (h _).const_mul _
    have hi₁₂ : Integrable (fun x => ((1 - a : ℝ) : ℂ) * torusChar initialMode x +
      ((a / 2 : ℝ) : ℂ) * torusChar (initialMode + initialMode) x) := hi₁.add hi₂
    simp_rw [initialWeight_mul_character]
    rw [integral_add hi₁₂ (integrable_const _),
      integral_add hi₁ hi₂, integral_const_mul, integral_const_mul,
      integral_torusChar_zero initialMode_ne_zero, integral_torusChar_zero initialMode_add_ne_zero]
    simp
  have hg : D.complexGram 0 i.succ = ((a / 2 : ℝ) : ℂ) := by
    simp only [Data.complexGram, charGram, Matrix.of_apply, D.augMode_zero, D.augMode_succ,
      torusChar_zero, map_one, mul_one]
    exact hmoment
  change (D.complexGram 0 i.succ).re = _
  rw [hg, Complex.ofReal_re]

lemma initialData_floor (a : ℝ) (ha : 0 < a) (ha' : a ≤ 1 / 400) :
    a ^ 2 • 1 ≤ (initialData a ha ha').gram := by
  have h : a ^ 2 ≤ 1 - 2 * a := by
    nlinarith [mul_nonneg ha.le (sub_nonneg.mpr ha')]
  have hb : a ^ 2 • (1 : Matrix (Fin 2) (Fin 2) ℝ) ≤ (1 - 2 * a) • 1 := by
    apply matrix_le_of_qform_le
    · exact (Matrix.PosDef.one.smul (sq_pos_of_pos ha)).isHermitian
    · exact (Matrix.PosDef.one.smul (show 0 < 1 - 2 * a by linarith)).isHermitian
    · intro x
      simp only [qform_smul]
      exact mul_le_mul_of_nonneg_right h (qform_nonneg Matrix.PosDef.one.posSemidef _)
  exact hb.trans (initialData a ha ha').gram_bounds.1


private noncomputable def initialCenterEntry (a : ℝ) : ℝ :=
  (1 - a) - (1 - a)⁻¹ * ((a / 2) * (a / 2))

lemma initialData_centerGram (a : ℝ) (ha : 0 < a) (ha' : a ≤ 1 / 400) :
    (initialData a ha ha').centerGram = Matrix.diagonal (fun _ => initialCenterEntry a) := by
  ext i j
  have hij : i = j := Subsingleton.elim _ _
  subst j
  simp [Data.centerGram, Data.tailGram, Data.gram_diag, initialData_mass,
    Matrix.vecMulVec_apply, initialData_meanColumn, initialCenterEntry]

lemma initialData_centerGram_inv (a : ℝ) (ha : 0 < a) (ha' : a ≤ 1 / 400) :
    (initialData a ha ha').centerGram⁻¹ = Matrix.diagonal (fun _ => (initialCenterEntry a)⁻¹) := by
  have hpos := (initialData a ha ha').centerGram_posDef.diag_pos (i := (0 : Fin 1))
  rw [initialData_centerGram, Matrix.diagonal_apply_eq] at hpos
  apply Matrix.inv_eq_left_inv
  rw [initialData_centerGram, Matrix.diagonal_mul_diagonal]
  ext i j
  simp [Matrix.one_apply, Matrix.diagonal, hpos.ne']

lemma initialData_gain (a : ℝ) (ha : 0 < a) (ha' : a ≤ 1 / 400) :
    (initialData a ha ha').gain = initialGain a := by
  have hne : 1 - a ≠ 0 := by linarith
  have hd : (4 - 8 * a + 3 * a ^ 2) ≠ 0 := by nlinarith [sq_nonneg a]
  have hentry : initialCenterEntry a = (4 - 8 * a + 3 * a ^ 2) / (4 * (1 - a)) := by
    unfold initialCenterEntry
    field_simp
    ring
  rw [Data.gain_eq_centerGram_inv, initialData_mass, initialData_centerGram_inv]
  simp only [initialData_meanColumn, dotProduct, Fin.sum_univ_one, Matrix.mulVec_diagonal]
  rw [hentry]
  unfold initialGain
  field_simp
  ring

lemma initialData_inverse_diagonal (a : ℝ) (ha : 0 < a) (ha' : a ≤ 1 / 400) (i : Fin 1) :
    ((initialData a ha ha').gram⁻¹) i.succ i.succ ≤ 1 + 2 * a := by
  rw [Data.gram_inv_succ_succ, initialData_centerGram_inv, Matrix.diagonal_apply_eq]
  have hapos : 0 < 1 - a := by linarith
  have hnum : 0 < 1 - 2 * a + 3 * a ^ 2 / 4 := by nlinarith [sq_nonneg a]
  have heq : initialCenterEntry a = (1 - 2 * a + 3 * a ^ 2 / 4) / (1 - a) := by
    unfold initialCenterEntry
    field_simp [hapos.ne']
    ring
  rw [heq, inv_div, div_le_iff₀ hnum]
  have hq : a ^ 2 ≤ a / 400 := by nlinarith [mul_nonneg ha.le (sub_nonneg.mpr ha')]
  have hc : 0 ≤ a * a ^ 2 := by positivity
  nlinarith only [hq, hc, ha]

lemma initialData_centered_prefix (a : ℝ) (ha : 0 < a) (ha' : a ≤ 1 / 400) :
    HPrefix (𝕜 := ℂ) (initialData a ha ha').centerLp 1 := by
  refine ⟨zero_le_one, fun k hk c => ?_⟩
  have hk' : k = 0 ∨ k = 1 := by omega
  rcases hk' with rfl | rfl
  · simp [synth, truncCoeff]
  · rw [truncCoeff_eq_self _ (le_refl 1), one_mul]

end SchauderBasisOrbits.Scalar

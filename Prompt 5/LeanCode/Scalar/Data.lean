module

public import LeanCode.Measure.Weights
public import LeanCode.Finite.Families
public import Mathlib

@[expose] public section

open MeasureTheory Complex Matrix
open scoped ENNReal ComplexConjugate ComplexOrder MatrixOrder InnerProductSpace

namespace SchauderBasisOrbits.Scalar

noncomputable local instance dataCircleMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

local instance dataCircleProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure (@AddCircle.haarAddCircle 1 _))

local instance dataCircleHaar : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure (@AddCircle.haarAddCircle 1 _))

local instance dataCircleNegInvariant : (volume : Measure UnitAddCircle).IsNegInvariant := by
  apply Measure.IsAddHaarMeasure.isNegInvariant_of_regular

/-- An ordered finite nonconstant character family with an even and strictly positive weight. -/
structure Data (r n : ℕ) where
  size_pos : 0 < n
  w : UnitAddTorus (Fin r) → ℝ
  measurable_w : Measurable w
  lower : ℝ
  lower_pos : 0 < lower
  lower_le : ∀ y, lower ≤ w y
  le_one : ∀ y, w y ≤ 1
  even_w : ∀ y, w (-y) = w y
  mode : Fin n → Fin r → ℤ
  mode_inj : Function.Injective mode
  mode_ne_zero : ∀ i, mode i ≠ 0

/-- Scalar data with a finite character expansion of its weight. -/
structure PolynomialData (r n : ℕ) extends Data r n where
  poly : TorusPoly (Fin r)
  eval_poly : ∀ x, evalTorusPoly poly x = (w x : ℂ)

namespace Data

variable {r n : ℕ} (D : Data r n)

lemma w_nonneg (y : UnitAddTorus (Fin r)) : 0 ≤ D.w y :=
  D.lower_pos.le.trans (D.lower_le y)

lemma lower_le_one : D.lower ≤ 1 := (D.lower_le 0).trans (D.le_one 0)

/-- The augmented order starts with the trivial character. -/
def augMode (i : Fin (n + 1)) : Fin r → ℤ :=
  Fin.cases 0 D.mode i

@[simp] lemma augMode_zero : D.augMode 0 = 0 := rfl

@[simp] lemma augMode_succ (i : Fin n) : D.augMode i.succ = D.mode i := rfl

lemma augMode_inj : Function.Injective D.augMode := by
  intro i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
  · simp
  · simp only [augMode_zero, augMode_succ]
    exact fun h => (D.mode_ne_zero j h.symm).elim
  · simp only [augMode_zero, augMode_succ]
    exact fun h => (D.mode_ne_zero i h).elim
  · simpa only [augMode_succ, Fin.succ_inj] using D.mode_inj.eq_iff.mp

noncomputable def mass : ℝ := ∫ y, D.w y

noncomputable def loss : ℝ := 1 - D.mass

lemma integrable_w : Integrable D.w := by
  apply Integrable.of_bound D.measurable_w.aestronglyMeasurable 1
  exact Filter.Eventually.of_forall (fun y => by simpa [Real.norm_eq_abs, abs_of_nonneg (D.w_nonneg y)] using D.le_one y)

lemma lower_le_mass : D.lower ≤ D.mass := by
  simpa [mass] using integral_mono (integrable_const D.lower) D.integrable_w D.lower_le

lemma mass_le_one : D.mass ≤ 1 := by
  simpa [mass] using integral_mono D.integrable_w (integrable_const (1 : ℝ)) D.le_one

lemma mass_pos : 0 < D.mass := D.lower_pos.trans_le D.lower_le_mass

lemma loss_nonneg : 0 ≤ D.loss := sub_nonneg.mpr D.mass_le_one

lemma loss_lt_one : D.loss < 1 := by unfold loss; linarith [D.mass_pos]

end Data

section WeightedGram

variable {ι α : Type*} [Fintype ι]

/-- Weighted pairings of characters, expressed over the reference Haar probability. -/
noncomputable def charGram (w : UnitAddTorus ι → ℝ) (mode : α → ι → ℤ) : Matrix α α ℂ :=
  Matrix.of (fun i j => ∫ y, (w y : ℂ) * conj (torusChar (mode i) y) * torusChar (mode j) y)

lemma charGram_integrable (w : UnitAddTorus ι → ℝ) (hw : Measurable w)
    (C : ℝ) (hwC : ∀ y, |w y| ≤ C) (k l : ι → ℤ) :
    Integrable (fun y => (w y : ℂ) * conj (torusChar k y) * torusChar l y) := by
  apply Integrable.of_bound ?_ C (Filter.Eventually.of_forall (fun y => ?_))
  · exact (((Complex.continuous_ofReal.measurable.comp hw).mul
      (Complex.continuous_conj.measurable.comp (continuous_torusChar k).measurable)).mul
      (continuous_torusChar l).measurable).aestronglyMeasurable
  · simpa only [norm_mul, Complex.norm_conj, norm_torusChar, mul_one, Complex.norm_real,
      Real.norm_eq_abs] using hwC y

private lemma charGram_sub (w v : UnitAddTorus ι → ℝ)
    (hw : Measurable w) (hv : Measurable v)
    (C D : ℝ) (hwC : ∀ y, |w y| ≤ C) (hvD : ∀ y, |v y| ≤ D) (mode : α → ι → ℤ) :
    charGram (fun y => w y - v y) mode = charGram w mode - charGram v mode := by
  ext i j
  simp only [charGram, Matrix.of_apply, Matrix.sub_apply, Complex.ofReal_sub, sub_mul]
  exact integral_sub (charGram_integrable w hw C hwC _ _)
    (charGram_integrable v hv D hvD _ _)

lemma charGram_one {mode : α → ι → ℤ} (hm : Function.Injective mode)
    [DecidableEq α] : charGram (fun _ => 1) mode = 1 := by
  calc
    _ = Matrix.gram ℂ (UnitAddTorus.mFourierLp 2 ∘ mode) := by
      ext i j
      simp only [Matrix.gram_apply, Function.comp_apply, charGram, Matrix.of_apply, ofReal_one,
        one_mul, L2.inner_def]
      apply integral_congr_ae
      filter_upwards [UnitAddTorus.coeFn_mFourierLp 2 (mode i),
        UnitAddTorus.coeFn_mFourierLp 2 (mode j)] with x hi hj
      rw [hi, hj, RCLike.inner_apply']
    _ = 1 := Matrix.gram_eq_one_iff_orthonormal.mpr (UnitAddTorus.orthonormal_mFourier.comp mode hm)

private lemma charGram_const {mode : α → ι → ℤ} (hm : Function.Injective mode)
    [DecidableEq α] (c : ℝ) : charGram (fun _ => c) mode = (c : ℂ) • 1 := by
  rw [← charGram_one hm]
  ext i j
  simp only [charGram, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, ofReal_one, one_mul]
  rw [← integral_const_mul]
  simp only [mul_assoc]

private lemma charGram_eq_gram_sqrt {w : UnitAddTorus ι → ℝ} (hw : Measurable w)
    (hw₀ : ∀ y, 0 ≤ w y) (hw₁ : ∀ y, w y ≤ 1) (mode : α → ι → ℤ) :
    charGram w mode = Matrix.gram ℂ (fun i => lift₂ volume
      (fun y => (Real.sqrt (w y) : ℂ) * torusChar (mode i) y)
      ((Complex.continuous_ofReal.measurable.comp (Real.continuous_sqrt.measurable.comp hw)).mul
        (continuous_torusChar _).measurable)
      1 (fun y => by
        rw [norm_mul, norm_torusChar, mul_one, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (Real.sqrt_nonneg _)]
        simpa using Real.sqrt_le_sqrt (hw₁ y))) := by
  ext i j
  rw [Matrix.gram_apply, L2.inner_def]
  symm
  apply integral_congr_ae
  filter_upwards [ae_lift₂ volume _ _ _ _, ae_lift₂ volume _ _ _ _] with y hi hj
  rw [hi, hj]
  simp only [RCLike.inner_apply', map_mul, conj_ofReal]
  have h : ((Real.sqrt (w y) : ℝ) : ℂ) * ((Real.sqrt (w y) : ℝ) : ℂ) = (w y : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hw₀ y)]
  linear_combination (conj (torusChar (mode i) y) * torusChar (mode j) y) * h

lemma charGram_posSemidef {w : UnitAddTorus ι → ℝ} (hw : Measurable w)
    (hw₀ : ∀ y, 0 ≤ w y) (hw₁ : ∀ y, w y ≤ 1) (mode : α → ι → ℤ) :
    (charGram w mode).PosSemidef := by
  rw [charGram_eq_gram_sqrt hw hw₀ hw₁ mode]
  exact Matrix.posSemidef_gram _ _

end WeightedGram

namespace Data

variable {r n : ℕ} (D : Data r n)

noncomputable def complexGram : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  charGram D.w D.augMode

lemma complexGram_bounds : (D.lower : ℂ) • 1 ≤ D.complexGram ∧ D.complexGram ≤ 1 := by
  constructor
  · rw [Matrix.le_iff, complexGram, ← charGram_const D.augMode_inj]
    rw [← charGram_sub D.w (fun _ => D.lower) D.measurable_w measurable_const 1 1
      (fun y => by simpa [abs_of_nonneg (D.w_nonneg y)] using D.le_one y)
      (fun _ => by simpa [abs_of_nonneg D.lower_pos.le] using D.lower_le_one)]
    exact charGram_posSemidef (D.measurable_w.sub measurable_const)
      (fun y => sub_nonneg.mpr (D.lower_le y)) (fun y => by
        change D.w y - D.lower ≤ 1
        linarith [D.le_one y, D.lower_pos])
      D.augMode
  · rw [Matrix.le_iff, complexGram, ← charGram_one D.augMode_inj]
    rw [← charGram_sub (fun _ => 1) D.w measurable_const D.measurable_w 1 1
      (by intro y; norm_num)
      (fun y => by simpa [abs_of_nonneg (D.w_nonneg y)] using D.le_one y)]
    exact charGram_posSemidef (measurable_const.sub D.measurable_w)
      (fun y => sub_nonneg.mpr (D.le_one y)) (fun y => by
        change 1 - D.w y ≤ 1
        linarith [D.w_nonneg y]) D.augMode

lemma complexGram_posDef : D.complexGram.PosDef := by
  have hlo : (D.complexGram - (D.lower : ℂ) • 1).PosSemidef :=
    Matrix.le_iff.mp D.complexGram_bounds.1
  have hbase : ((D.lower : ℂ) • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)).PosDef := by
    exact Matrix.PosDef.one.smul (α := ℝ) D.lower_pos
  simpa using Matrix.PosDef.posSemidef_add hlo hbase

lemma complexGram_diag (i : Fin (n + 1)) : D.complexGram i i = (D.mass : ℂ) := by
  unfold complexGram charGram mass
  rw [← integral_complex_ofReal]
  apply integral_congr_ae
  refine Filter.Eventually.of_forall (fun y => ?_)
  simp only [mul_assoc, Complex.conj_mul', norm_torusChar, one_pow, ofReal_one, mul_one]

lemma torusChar_arg_neg {ι : Type*} [Fintype ι] (k : ι → ℤ) (y : UnitAddTorus ι) :
    torusChar k (-y) = conj (torusChar k y) := by
  rw [← torusChar_neg]
  simp only [torusChar, UnitAddTorus.mFourier, ContinuousMap.coe_mk, Pi.neg_apply,
    fourier_apply, zsmul_neg, neg_zsmul]

/-- Inverting all coordinates preserves Haar measure and conjugates the pairing. -/
lemma complexGram_conj (i j : Fin (n + 1)) :
    conj (D.complexGram i j) = D.complexGram i j := by
  change conj (∫ y, (D.w y : ℂ) * conj (torusChar (D.augMode i) y) *
    torusChar (D.augMode j) y) = _
  rw [← integral_conj]
  let f : UnitAddTorus (Fin r) → ℂ := fun y =>
    (D.w y : ℂ) * conj (torusChar (D.augMode i) y) * torusChar (D.augMode j) y
  change (∫ y, conj (f y)) = ∫ y, f y
  rw [← integral_neg_eq_self f volume]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun y => by
    simp only [f, map_mul, conj_ofReal, D.even_w, torusChar_arg_neg])

/-- The real augmented Gram matrix, available because the weight is even. -/
noncomputable def gram : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  D.complexGram.map Complex.re

lemma complexify_gram : complexify D.gram = D.complexGram := by
  ext i j
  exact Complex.conj_eq_iff_re.mp (D.complexGram_conj i j)

lemma gram_isHermitian : D.gram.IsHermitian := by
  have h := D.complexGram_posDef.isHermitian
  refine Matrix.ext (fun i j => ?_)
  change (D.complexGram j i).re = (D.complexGram i j).re
  have hij := congrFun (congrFun h.eq i) j
  simpa only [Matrix.conjTranspose_apply, Complex.star_def, Complex.conj_re] using congrArg Complex.re hij

private lemma qform_complexify_real {k : Type*} [Fintype k] (A : Matrix k k ℝ) (c : k → ℝ) :
    qform (complexify A) (fun i => (c i : ℂ)) = qform A c := by
  rw [qform_complexify]
  simp [qform]

lemma gram_posDef : D.gram.PosDef := by
  refine posDef_of_qform_pos D.gram_isHermitian (fun x hx => ?_)
  have hxc : (fun i => (x i : ℂ)) ≠ 0 := by
    intro hc
    apply hx
    funext i
    simpa using congrArg Complex.re (congrFun hc i)
  rw [← qform_complexify_real, D.complexify_gram]
  exact qform_pos D.complexGram_posDef hxc

lemma gram_bounds : D.lower • 1 ≤ D.gram ∧ D.gram ≤ 1 := by
  have h_one : complexify (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) = 1 := by
    ext i j
    simp [Matrix.one_apply, apply_ite]
  have h_lower : complexify (D.lower • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)) =
      (D.lower : ℂ) • 1 := by
    ext i j
    simp only [complexify_apply, Matrix.smul_apply, smul_eq_mul, ofReal_mul]
    rw [← complexify_apply, h_one]
  constructor
  · refine matrix_le_of_qform_le ((Matrix.PosDef.one.smul D.lower_pos).isHermitian)
      D.gram_isHermitian (fun x => ?_)
    rw [← qform_complexify_real (D.lower • 1), ← qform_complexify_real D.gram,
      h_lower, D.complexify_gram]
    exact qform_mono D.complexGram_bounds.1 _
  · refine matrix_le_of_qform_le D.gram_isHermitian Matrix.isHermitian_one (fun x => ?_)
    rw [← qform_complexify_real D.gram, ← qform_complexify_real 1, D.complexify_gram, h_one]
    exact qform_mono D.complexGram_bounds.2 _

lemma gram_diag (i : Fin (n + 1)) : D.gram i i = D.mass := by
  simp [gram, D.complexGram_diag]


/-- Unnormalized mean column of the nonconstant characters. -/
noncomputable def meanColumn : Fin n → ℝ := fun i => D.gram i.succ 0

/-- Unnormalized Gram matrix of the nonconstant characters. -/
noncomputable def tailGram : Matrix (Fin n) (Fin n) ℝ :=
  D.gram.submatrix Fin.succ Fin.succ

/-- Unnormalized Gram matrix after orthogonal projection off constants. -/
noncomputable def centerGram : Matrix (Fin n) (Fin n) ℝ :=
  D.tailGram - D.mass⁻¹ • Matrix.vecMulVec D.meanColumn D.meanColumn

/-- Centered Gram matrix in the normalized weighted space. -/
noncomputable def normalizedGram : Matrix (Fin n) (Fin n) ℝ :=
  D.mass⁻¹ • D.centerGram

/-- Column of means in the normalized weighted space. -/
noncomputable def normalizedMean : Fin n → ℝ := D.mass⁻¹ • D.meanColumn

/-- Gain, the squared norm of the map taking a centered combination to its uncentered mean. -/
noncomputable def gain : ℝ := D.normalizedMean ⬝ᵥ (D.normalizedGram⁻¹ *ᵥ D.normalizedMean)

lemma gram_zero_succ (i : Fin n) : D.gram 0 i.succ = D.meanColumn i := by
  simpa [meanColumn] using congrFun (congrFun D.gram_isHermitian.eq i.succ) 0

lemma gram_mulVec_cons (s : ℝ) (c : Fin n → ℝ) :
    D.gram *ᵥ Fin.cons s c =
      Fin.cons (D.mass * s + D.meanColumn ⬝ᵥ c)
        (fun i => D.meanColumn i * s + (D.tailGram *ᵥ c) i) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, D.gram_diag, D.gram_zero_succ]
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, meanColumn, tailGram]

lemma centerGram_mulVec (c : Fin n → ℝ) :
    D.centerGram *ᵥ c = fun i =>
      (D.tailGram *ᵥ c) i - D.mass⁻¹ * (D.meanColumn i * (D.meanColumn ⬝ᵥ c)) := by
  funext i
  simp only [centerGram, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.vecMulVec_mulVec,
    Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rfl

lemma tailGram_posDef : D.tailGram.PosDef := D.gram_posDef.submatrix (Fin.succ_injective n)

lemma centerGram_isHermitian : D.centerGram.IsHermitian := by
  unfold centerGram
  refine D.tailGram_posDef.isHermitian.sub ?_
  ext i j
  simp [Matrix.vecMulVec, mul_comm (D.meanColumn i) (D.meanColumn j)]

lemma centerGram_posDef : D.centerGram.PosDef := by
  refine posDef_of_qform_pos D.centerGram_isHermitian (fun c hc => ?_)
  let s : ℝ := -((D.meanColumn ⬝ᵥ c) / D.mass)
  have hcons : (Fin.cons (α := fun _ => ℝ) s c : Fin (n + 1) → ℝ) ≠ 0 := by
    intro h
    apply hc
    funext j
    exact congrFun h j.succ
  have hvec : D.gram *ᵥ Fin.cons s c = Fin.cons 0 (D.centerGram *ᵥ c) := by
    rw [D.gram_mulVec_cons]
    have hzero : D.mass * s + D.meanColumn ⬝ᵥ c = 0 := by
      dsimp [s]
      field_simp [D.mass_pos.ne']
      ring
    rw [hzero, D.centerGram_mulVec]
    congr 1
    funext i
    dsimp [s]
    ring
  have hpos := qform_pos D.gram_posDef hcons
  simpa only [qform, RCLike.re_to_real, star_trivial, hvec, dotProduct, Fin.sum_univ_succ,
    Fin.cons_zero, Fin.cons_succ, mul_zero, zero_add] using hpos

lemma normalizedGram_posDef : D.normalizedGram.PosDef :=
  D.centerGram_posDef.smul (inv_pos.mpr D.mass_pos)

lemma normalizedGram_inv : D.normalizedGram⁻¹ = D.mass • D.centerGram⁻¹ := by
  let u : ℝˣ := Units.mk0 D.mass⁻¹ (inv_ne_zero D.mass_pos.ne')
  have h := Matrix.inv_smul' (A := D.centerGram) u
    ((Matrix.isUnit_iff_isUnit_det _).1 D.centerGram_posDef.isUnit)
  simpa [u, normalizedGram, Units.smul_def, Units.val_inv_eq_inv_val] using h

lemma gain_nonneg : 0 ≤ D.gain := by
  simpa only [gain, qform, RCLike.re_to_real, star_trivial] using
    qform_nonneg D.normalizedGram_posDef.inv.posSemidef D.normalizedMean

/-- The inverse augmented Gram action, expressed through the centered matrix. -/
lemma gram_inv_mulVec_cons (t : ℝ) (y : Fin n → ℝ) :
    let c := D.centerGram⁻¹ *ᵥ (y - (t / D.mass) • D.meanColumn)
    D.gram⁻¹ *ᵥ Fin.cons t y =
      Fin.cons ((t - D.meanColumn ⬝ᵥ c) / D.mass) c := by
  let c := D.centerGram⁻¹ *ᵥ (y - (t / D.mass) • D.meanColumn)
  change D.gram⁻¹ *ᵥ Fin.cons t y = Fin.cons ((t - D.meanColumn ⬝ᵥ c) / D.mass) c
  have h₁ : D.centerGram * D.centerGram⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 D.centerGram_posDef.isUnit)
  have h₂ : D.centerGram *ᵥ c = y - (t / D.mass) • D.meanColumn := by
    dsimp [c]
    rw [Matrix.mulVec_mulVec, h₁, Matrix.one_mulVec]
  have hm : D.mass ≠ 0 := D.mass_pos.ne'
  apply D.gram_posDef.mulVec_injective
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _
    ((Matrix.isUnit_iff_isUnit_det _).1 D.gram_posDef.isUnit), Matrix.one_mulVec, D.gram_mulVec_cons]
  symm
  have hs : D.mass * ((t - D.meanColumn ⬝ᵥ c) / D.mass) + D.meanColumn ⬝ᵥ c = t := by
    field_simp
    ring
  rw [hs]
  congr 1
  funext i
  have hi := congrFun h₂ i
  simp only [D.centerGram_mulVec, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hi
  rw [← sub_add_cancel ((D.tailGram *ᵥ c) i)
    (D.mass⁻¹ * (D.meanColumn i * (D.meanColumn ⬝ᵥ c))), hi]
  ring

/-- The nonconstant block of the augmented inverse is the centered inverse, without a
mass factor. -/
lemma gram_inv_succ_succ (i j : Fin n) :
    D.gram⁻¹ i.succ j.succ = D.centerGram⁻¹ i j := by
  have h := congrFun (D.gram_inv_mulVec_cons 0 (Pi.single j 1)) i.succ
  have hc : Fin.cons (α := fun _ => ℝ) 0 (Pi.single j (1 : ℝ)) = Pi.single j.succ 1 := by
    funext k
    refine Fin.cases ?_ (fun l => ?_) k
    · simp
    · simp [Pi.single_apply, Fin.succ_inj]
  simpa only [hc, Matrix.mulVec_single_one, Matrix.col_apply, Fin.cons_succ, zero_div,
    zero_smul, sub_zero] using h

lemma gain_eq_centerGram_inv :
    D.gain = D.mass⁻¹ * (D.meanColumn ⬝ᵥ (D.centerGram⁻¹ *ᵥ D.meanColumn)) := by
  rw [gain, D.normalizedGram_inv, normalizedMean, Matrix.smul_mulVec, Matrix.mulVec_smul,
    smul_smul, mul_inv_cancel₀ D.mass_pos.ne', one_smul, smul_dotProduct, smul_eq_mul]

/-- The top-left entry of the inverse augmented Gram records the gain. -/
lemma mass_mul_gram_inv_zero_zero : D.mass * D.gram⁻¹ 0 0 = 1 + D.gain := by
  have h := congrFun (D.gram_inv_mulVec_cons 1 0) 0
  have hc : Fin.cons (α := fun _ => ℝ) 1 (0 : Fin n → ℝ) = Pi.single 0 1 := by
    funext k
    refine Fin.cases ?_ (fun l => ?_) k <;> simp
  simp only [hc, Matrix.mulVec_single_one, Matrix.col_apply, Fin.cons_zero, one_div, zero_sub,
    Matrix.mulVec_neg, Matrix.mulVec_smul, dotProduct_neg, dotProduct_smul, smul_eq_mul] at h
  rw [h, D.gain_eq_centerGram_inv]
  field_simp [D.mass_pos.ne']
  ring


/-- Unnormalized weighted Haar measure for the scalar system. -/
noncomputable def measure : Measure (UnitAddTorus (Fin r)) :=
  weightedMeasure volume D.w

instance finite_measure : IsFiniteMeasure D.measure :=
  finite_weightedMeasure volume (Filter.Eventually.of_forall D.le_one)

/-- Normalize by the strictly positive mass, keeping the reference Haar measure explicit. -/
noncomputable def normalizedMeasure : Measure (UnitAddTorus (Fin r)) :=
  (ENNReal.ofReal D.mass⁻¹) • D.measure

instance finite_normalizedMeasure : IsFiniteMeasure D.normalizedMeasure := by
  constructor
  rw [normalizedMeasure, smul_apply, smul_eq_mul]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top D.measure _)

lemma integral_normalizedMeasure {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : UnitAddTorus (Fin r) → E) :
    (∫ y, f y ∂D.normalizedMeasure) = D.mass⁻¹ • ∫ y, D.w y • f y := by
  unfold normalizedMeasure
  rw [integral_smul_measure, ENNReal.toReal_ofReal (inv_nonneg.mpr D.mass_pos.le)]
  rw [measure, integral_weightedMeasure volume D.measurable_w
    (Filter.Eventually.of_forall D.w_nonneg)]

/-- Augmented scalar family in the normalized weighted Hilbert space. -/
noncomputable def augLp (i : Fin (n + 1)) : Lp ℂ 2 D.normalizedMeasure :=
  lift₂ D.normalizedMeasure (torusChar (D.augMode i)) (continuous_torusChar _).measurable
    1 (fun y => (norm_torusChar _ y).le)

lemma inner_augLp (i j : Fin (n + 1)) :
    ⟪D.augLp i, D.augLp j⟫_ℂ = (D.gram i j : ℂ) / (D.mass : ℂ) := by
  rw [augLp, augLp, inner_lift₂, D.integral_normalizedMeasure, Complex.real_smul]
  have h : (∫ y, D.w y • (conj (torusChar (D.augMode i) y) * torusChar (D.augMode j) y)) =
      D.complexGram i j := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun y => by
      show D.w y • _ = (D.w y : ℂ) * _ * _
      rw [Complex.real_smul, mul_assoc])
  rw [h, ← D.complexify_gram, complexify_apply, ofReal_inv, div_eq_mul_inv, mul_comm]

lemma inner_augLp_zero_zero : ⟪D.augLp 0, D.augLp 0⟫_ℂ = 1 := by
  rw [D.inner_augLp, D.gram_diag, div_self]
  exact_mod_cast D.mass_pos.ne'

lemma norm_augLp_zero : ‖D.augLp 0‖ = 1 := by
  have h := congrArg Complex.re D.inner_augLp_zero_zero
  simp only [← RCLike.re_to_complex, inner_self_eq_norm_sq_to_K] at h
  change (↑‖D.augLp 0‖ ^ 2 : ℂ).re = (1 : ℂ).re at h
  rw [← ofReal_pow, ofReal_re, one_re] at h
  nlinarith [norm_nonneg (D.augLp 0)]

lemma inner_augLp_zero_succ (i : Fin n) :
    ⟪D.augLp 0, D.augLp i.succ⟫_ℂ = (D.normalizedMean i : ℂ) := by
  rw [D.inner_augLp, D.gram_zero_succ, normalizedMean]
  simp only [Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul, Complex.ofReal_inv, div_eq_mul_inv]
  rw [mul_comm]

lemma inner_augLp_succ_zero (i : Fin n) :
    ⟪D.augLp i.succ, D.augLp 0⟫_ℂ = (D.normalizedMean i : ℂ) := by
  rw [← inner_conj_symm, D.inner_augLp_zero_succ, Complex.conj_ofReal]

/-- Nonconstant scalar vectors after subtracting their normalized means. -/
noncomputable def centerLp (i : Fin n) : Lp ℂ 2 D.normalizedMeasure :=
  D.augLp i.succ - (D.normalizedMean i : ℂ) • D.augLp 0

lemma inner_constant_center (i : Fin n) : ⟪D.augLp 0, D.centerLp i⟫_ℂ = 0 := by
  rw [centerLp, inner_sub_right, inner_smul_right, D.inner_augLp_zero_succ,
    D.inner_augLp_zero_zero, mul_one, sub_self]

lemma normalizedGram_apply (i j : Fin n) :
    D.normalizedGram i j = D.gram i.succ j.succ / D.mass -
      D.normalizedMean i * D.normalizedMean j := by
  simp only [normalizedGram, centerGram, tailGram, Matrix.smul_apply, Matrix.sub_apply,
    smul_eq_mul, submatrix_apply, Matrix.vecMulVec_apply, normalizedMean, Pi.smul_apply]
  rw [div_eq_mul_inv]
  ring

lemma gram_centerLp : Matrix.gram ℂ D.centerLp = complexify D.normalizedGram := by
  ext i j
  simp only [Matrix.gram_apply, complexify_apply, D.normalizedGram_apply, ofReal_sub,
    ofReal_div, ofReal_mul, centerLp, inner_sub_left, inner_sub_right, inner_smul_left,
    inner_smul_right, D.inner_augLp_zero_succ, D.inner_augLp_succ_zero, D.inner_augLp_zero_zero,
    Complex.conj_ofReal]
  rw [D.inner_augLp]
  ring

lemma centerLp_linearIndependent : LinearIndependent ℂ D.centerLp := by
  apply Matrix.posDef_gram_iff_linearIndependent.mp
  rw [D.gram_centerLp]
  exact posDef_complexify D.normalizedGram_posDef

lemma gram_augLp : Matrix.gram ℂ D.augLp = D.mass⁻¹ • D.complexGram := by
  ext i j
  simp only [Matrix.gram_apply, Matrix.smul_apply, Complex.real_smul, D.inner_augLp,
    ← D.complexify_gram, complexify_apply, div_eq_mul_inv, Complex.ofReal_inv]
  rw [mul_comm]

lemma augLp_linearIndependent : LinearIndependent ℂ D.augLp := by
  apply Matrix.posDef_gram_iff_linearIndependent.mp
  rw [D.gram_augLp]
  exact D.complexGram_posDef.smul (inv_pos.mpr D.mass_pos)

lemma qform_centerLp_synth (c : Fin n → ℝ) :
    ‖synth D.centerLp (fun i => (c i : ℂ))‖ ^ 2 = qform D.normalizedGram c := by
  rw [← qform_gram, D.gram_centerLp, qform_complexify_real]

lemma inner_constant_tail_synth (c : Fin n → ℝ) :
    ⟪D.augLp 0, synth (fun i => D.augLp i.succ) (fun i => (c i : ℂ))⟫_ℂ =
      ((D.normalizedMean ⬝ᵥ c : ℝ) : ℂ) := by
  simp only [synth, inner_sum, inner_smul_right, D.inner_augLp_zero_succ, dotProduct, ofReal_sum,
    ofReal_mul]
  congr 1
  funext i
  ring

/-- The explicitly constructed real coefficients with mean one and variance reciprocal to gain. -/
lemma exists_mean_one_variance_inv_gain (hg : 0 < D.gain) :
    ∃ c : Fin n → ℝ, D.normalizedMean ⬝ᵥ c = 1 ∧ qform D.normalizedGram c = 1 / D.gain := by
  let c₀ := D.normalizedGram⁻¹ *ᵥ D.normalizedMean
  let c := D.gain⁻¹ • c₀
  have hC : D.normalizedGram *ᵥ c₀ = D.normalizedMean := by
    dsimp [c₀]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _
      ((Matrix.isUnit_iff_isUnit_det _).1 D.normalizedGram_posDef.isUnit), Matrix.one_mulVec]
  have hZ : D.normalizedMean ⬝ᵥ c₀ = D.gain := rfl
  refine ⟨c, ?_, ?_⟩
  · change D.normalizedMean ⬝ᵥ (D.gain⁻¹ • c₀) = _
    rw [dotProduct_smul, hZ]
    exact inv_mul_cancel₀ hg.ne'
  · simp only [qform, RCLike.re_to_real, star_trivial, c, Matrix.mulVec_smul, hC,
      smul_dotProduct, dotProduct_smul, smul_eq_mul]
    rw [dotProduct_comm c₀ D.normalizedMean, hZ]
    field_simp [hg.ne']

end Data

end SchauderBasisOrbits.Scalar

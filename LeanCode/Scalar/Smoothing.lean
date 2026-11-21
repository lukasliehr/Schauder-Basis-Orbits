import LeanCode.Scalar.Fejer
import LeanCode.Scalar.MatrixMix
import LeanCode.Scalar.Prefix

open Filter MeasureTheory Complex Matrix
open scoped ComplexConjugate ComplexOrder MatrixOrder InnerProductSpace Topology ENNReal

namespace SchauderBasisOrbits.Scalar

noncomputable local instance smoothingCircleMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩

local instance smoothingCircleProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure (@AddCircle.haarAddCircle 1 _))

local instance smoothingCircleHaar : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure (@AddCircle.haarAddCircle 1 _))

local instance smoothingCircleNegInvariant : (volume : Measure UnitAddCircle).IsNegInvariant := by
  apply Measure.IsAddHaarMeasure.isNegInvariant_of_regular

variable {r n : ℕ} (D : Data r n) (N : ℕ)

private abbrev T := UnitAddTorus (Fin r)

private lemma integral_sub_arg {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : UnitAddTorus ι → E) (x : UnitAddTorus ι) :
    (∫ y, g (x - y)) = ∫ y, g y := by
  simp only [sub_eq_add_neg]
  rw [integral_neg_eq_self (fun y => g (x + y)) volume, integral_add_left_eq_self]

private lemma integral_sub_right_arg {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : UnitAddTorus ι → E) (x : UnitAddTorus ι) :
    (∫ y, g (y - x)) = ∫ y, g y := by
  simp only [sub_eq_add_neg]
  rw [integral_add_right_eq_self]

private lemma continuous_fejerTorus (N : ℕ) : Continuous (fejerTorus (ι := Fin r) N) := by
  have h : fejerTorus (ι := Fin r) N = fun x => (evalTorusPoly (fejerTorusPoly (Fin r) N) x).re := by
    funext x
    rw [eval_fejerTorusPoly, ofReal_re]
  rw [h]
  exact Complex.continuous_re.comp (continuous_evalTorusPoly _)

private noncomputable def kernelBound (r N : ℕ) : ℝ :=
  ∑ k ∈ (fejerTorusPoly (Fin r) N).coeff.support, ‖(fejerTorusPoly (Fin r) N).coeff k‖

private lemma norm_fejerTorus_le (x : T (r := r)) : ‖fejerTorus N x‖ ≤ kernelBound r N := by
  simpa only [eval_fejerTorusPoly, Complex.norm_real, kernelBound] using
    norm_evalTorusPoly_le (fejerTorusPoly (Fin r) N) x

private lemma integrable_fejerTorus (N : ℕ) : Integrable (fejerTorus (ι := Fin r) N) :=
  Integrable.of_bound (continuous_fejerTorus N).measurable.aestronglyMeasurable (kernelBound r N)
    (Filter.Eventually.of_forall (norm_fejerTorus_le N))

/-- Probability averaging by the finite torus Fejér kernel. -/
noncomputable def smoothWeight (x : T (r := r)) : ℝ :=
  ∫ y, D.w y * fejerTorus N (x - y)

lemma smoothWeight_alt (x : T (r := r)) :
    smoothWeight D N x = ∫ y, fejerTorus N y * D.w (x - y) := by
  rw [← integral_sub_arg (fun y => fejerTorus N y * D.w (x - y)) x]
  simp [smoothWeight, sub_sub_cancel, mul_comm]

lemma smoothWeight_bounds (x : T (r := r)) :
    D.lower ≤ smoothWeight D N x ∧ smoothWeight D N x ≤ 1 := by
  have hi : Integrable (fun y => fejerTorus N y * D.w (x - y)) := by
    apply Integrable.of_bound ((continuous_fejerTorus N).measurable.mul
      (D.measurable_w.comp (measurable_const.sub measurable_id))).aestronglyMeasurable
      (kernelBound r N)
    refine Filter.Eventually.of_forall (fun y => ?_)
    change ‖fejerTorus N y * D.w (x - y)‖ ≤ _
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (fejerTorus_nonneg N y), Real.norm_eq_abs,
      abs_of_nonneg (D.w_nonneg (x - y))]
    have h := mul_le_mul_of_nonneg_left (D.le_one (x - y)) (fejerTorus_nonneg N y)
    rw [mul_one] at h
    exact h.trans (by simpa [Real.norm_eq_abs, abs_of_nonneg (fejerTorus_nonneg N y)] using norm_fejerTorus_le N y)
  rw [smoothWeight_alt]
  constructor
  · have hl := integral_mono ((integrable_fejerTorus N).const_mul D.lower) hi (fun y => by
      dsimp only
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left (D.lower_le (x - y)) (fejerTorus_nonneg N y))
    rwa [integral_const_mul, integral_fejerTorus, mul_one] at hl
  · have hu := integral_mono hi (integrable_fejerTorus N) (fun y => by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left (D.le_one (x - y)) (fejerTorus_nonneg N y))
    rwa [integral_fejerTorus] at hu

lemma smoothWeight_even (x : T (r := r)) : smoothWeight D N (-x) = smoothWeight D N x := by
  unfold smoothWeight
  rw [← integral_neg_eq_self (fun y => D.w y * fejerTorus N (-x - y)) volume]
  have h (y : T (r := r)) : -x - -y = -(x - y) := by abel
  simp only [D.even_w, h, fejerTorus_even]

private noncomputable def smoothPoly : TorusPoly (Fin r) :=
  let p := fejerTorusPoly (Fin r) N
  ∑ k ∈ p.coeff.support, AddMonoidAlgebra.single k
    (p.coeff k * ∫ y, (D.w y : ℂ) * conj (torusChar k y))

lemma eval_smoothPoly (x : T (r := r)) : evalTorusPoly (smoothPoly D N) x = (smoothWeight D N x : ℂ) := by
  classical
  let p := fejerTorusPoly (Fin r) N
  let g (k : Fin r → ℤ) (y : T (r := r)) :=
    p.coeff k * ((D.w y : ℂ) * conj (torusChar k y)) * torusChar k x
  have hi (k : Fin r → ℤ) : Integrable (g k) := by
    have hw := charGram_integrable D.w D.measurable_w 1
      (fun y => by simpa [abs_of_nonneg (D.w_nonneg y)] using D.le_one y) k 0
    have h : Integrable (fun y => (D.w y : ℂ) * conj (torusChar k y)) := by simpa using hw
    exact (h.const_mul _).mul_const _
  have he (y : T (r := r)) :
      (D.w y : ℂ) * (fejerTorus N (x - y) : ℂ) = ∑ k ∈ p.coeff.support, g k y := by
    rw [← eval_fejerTorusPoly, evalTorusPoly, Finsupp.sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    rw [sub_eq_add_neg, torusChar_add_arg, torusChar_neg_arg]
    dsimp [p, g]
    ring
  rw [smoothWeight, ← integral_complex_ofReal]
  simp_rw [Complex.ofReal_mul, he]
  rw [integral_finsetSum _ (fun k hk => hi k)]
  simp only [smoothPoly, evalTorusPoly_sum, evalTorusPoly_single]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [g, integral_mul_const, integral_const_mul, p]

lemma continuous_smoothWeight : Continuous (smoothWeight D N) := by
  have h : smoothWeight D N = fun x => (evalTorusPoly (smoothPoly D N) x).re := by
    funext x
    rw [eval_smoothPoly, ofReal_re]
  rw [h]
  exact Complex.continuous_re.comp (continuous_evalTorusPoly _)

/-- The smoothed datum keeps the modes and the pointwise positive lower bound. -/
noncomputable def smoothData : PolynomialData r n where
  toData := {
    size_pos := D.size_pos
    w := smoothWeight D N
    measurable_w := (continuous_smoothWeight D N).measurable
    lower := D.lower
    lower_pos := D.lower_pos
    lower_le x := (smoothWeight_bounds D N x).1
    le_one x := (smoothWeight_bounds D N x).2
    even_w := smoothWeight_even D N
    mode := D.mode
    mode_inj := D.mode_inj
    mode_ne_zero := D.mode_ne_zero
  }
  poly := smoothPoly D N
  eval_poly := eval_smoothPoly D N

private lemma integrable_smoothing_pair :
    Integrable (fun z : T (r := r) × T (r := r) => D.w z.2 * fejerTorus N (z.1 - z.2))
      ((volume : Measure (T (r := r))).prod volume) := by
  apply Integrable.of_bound ((D.measurable_w.comp measurable_snd).mul
    ((continuous_fejerTorus N).measurable.comp (measurable_fst.sub measurable_snd))).aestronglyMeasurable
    (kernelBound r N)
  refine Filter.Eventually.of_forall (fun z => ?_)
  change ‖D.w z.2 * fejerTorus N (z.1 - z.2)‖ ≤ _
  rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (D.w_nonneg z.2)]
  have h := mul_le_mul_of_nonneg_right (D.le_one z.2) (norm_nonneg (fejerTorus N (z.1 - z.2)))
  rw [one_mul] at h
  exact h.trans (norm_fejerTorus_le N (z.1 - z.2))

lemma smoothData_mass : (smoothData D N).toData.mass = D.mass := by
  change (∫ x, ∫ y, D.w y * fejerTorus N (x - y)) = _
  let f (x y : T (r := r)) := D.w y * fejerTorus N (x - y)
  have h := integral_integral_swap (f := f) (integrable_smoothing_pair D N)
  change (∫ x, ∫ y, f x y) = _
  rw [h]
  unfold f
  simp_rw [integral_const_mul, integral_sub_right_arg, integral_fejerTorus, mul_one, Data.mass]


private lemma integral_kernel_shift_char (k : Fin r → ℤ) (y : T (r := r)) :
    (∫ x, (fejerTorus N (x - y) : ℂ) * torusChar k x) =
      (∫ x, (fejerTorus N x : ℂ) * torusChar k x) * torusChar k y := by
  have hpoint (x : T (r := r)) : torusChar k x = torusChar k (x - y) * torusChar k y := by
    rw [← torusChar_add_arg, sub_add_cancel]
  simp_rw [show ∀ x : T (r := r), (fejerTorus N (x - y) : ℂ) * torusChar k x =
    ((fejerTorus N (x - y) : ℂ) * torusChar k (x - y)) * torusChar k y from
    fun x => by nth_rw 1 [hpoint x]; ring]
  rw [integral_mul_const]
  have hh := integral_sub_right_arg (fun x : T (r := r) => (fejerTorus N x : ℂ) * torusChar k x) y
  rw [hh]

/-- A Fourier moment after smoothing is the old moment times the kernel multiplier. -/
lemma smoothWeight_fourier (k : Fin r → ℤ) :
    (∫ x, (smoothWeight D N x : ℂ) * torusChar k x) =
      (∫ y, (D.w y : ℂ) * torusChar k y) *
        ∫ z, (fejerTorus N z : ℂ) * torusChar k z := by
  let f (x y : T (r := r)) : ℂ :=
    (D.w y : ℂ) * (fejerTorus N (x - y) : ℂ) * torusChar k x
  have hf : Integrable (Function.uncurry f) ((volume : Measure (T (r := r))).prod volume) := by
    have hw : Measurable (fun y : T (r := r) => (D.w y : ℂ)) :=
      Complex.continuous_ofReal.measurable.comp D.measurable_w
    have hK : Measurable (fun y : T (r := r) => (fejerTorus N y : ℂ)) :=
      Complex.continuous_ofReal.measurable.comp (continuous_fejerTorus N).measurable
    apply Integrable.of_bound (((hw.comp measurable_snd).mul (hK.comp
      (measurable_fst.sub measurable_snd))).mul
      ((continuous_torusChar k).measurable.comp measurable_fst)).aestronglyMeasurable (kernelBound r N)
    refine Filter.Eventually.of_forall (fun z => ?_)
    change ‖(D.w z.2 : ℂ) * (fejerTorus N (z.1 - z.2) : ℂ) * torusChar k z.1‖ ≤ _
    rw [norm_mul, norm_torusChar, mul_one, norm_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs (D.w z.2), abs_of_nonneg (D.w_nonneg z.2)]
    have h := mul_le_mul_of_nonneg_right (D.le_one z.2) (norm_nonneg (fejerTorus N (z.1 - z.2)))
    rw [one_mul] at h
    exact h.trans (norm_fejerTorus_le N (z.1 - z.2))
  have hi (x : T (r := r)) : (smoothWeight D N x : ℂ) * torusChar k x = ∫ y, f x y := by
    rw [smoothWeight, ← integral_complex_ofReal, ← integral_mul_const]
    simp [f, Complex.ofReal_mul]
  simp_rw [hi]
  rw [integral_integral_swap hf]
  have hj (y : T (r := r)) : (∫ x, f x y) =
      (D.w y : ℂ) * torusChar k y * ∫ z, (fejerTorus N z : ℂ) * torusChar k z := by
    simp only [f, mul_assoc, integral_const_mul, integral_kernel_shift_char]
    ring
  simp_rw [hj]
  rw [integral_mul_const]

lemma complexGram_eq_moment (i j : Fin (n + 1)) :
    D.complexGram i j = ∫ y, (D.w y : ℂ) * torusChar (D.augMode j - D.augMode i) y := by
  unfold Data.complexGram charGram
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun y => by
    simp only [Matrix.of_apply, sub_eq_add_neg, torusChar_add, torusChar_neg]
    ring)

lemma smoothData_complexGram (i j : Fin (n + 1)) :
    (smoothData D N).toData.complexGram i j =
      D.complexGram i j * ∫ z, (fejerTorus N z : ℂ) *
        (conj (torusChar (D.augMode i) z) * torusChar (D.augMode j) z) := by
  rw [complexGram_eq_moment]
  change (∫ x, (smoothWeight D N x : ℂ) * torusChar (D.augMode j - D.augMode i) x) = _
  rw [smoothWeight_fourier D N, complexGram_eq_moment]
  have h (z : T (r := r)) : torusChar (D.augMode j - D.augMode i) z =
      conj (torusChar (D.augMode i) z) * torusChar (D.augMode j) z := by
    simp [sub_eq_add_neg, torusChar_add, torusChar_neg, mul_comm]
  simp_rw [h]

lemma smoothData_complexGram_tendsto (i j : Fin (n + 1)) :
    Tendsto (fun N => (smoothData D N).toData.complexGram i j) atTop (𝓝 (D.complexGram i j)) := by
  let k := D.augMode j - D.augMode i
  have h (m : ℕ) : (smoothData D m).toData.complexGram i j =
      D.complexGram i j * (↑(∏ a, fejerMultiplier m ((-k) a)) : ℂ) := by
    rw [complexGram_eq_moment]
    change (∫ x, (smoothWeight D m x : ℂ) * torusChar k x) = _
    rw [smoothWeight_fourier, ← complexGram_eq_moment D i j]
    have hk (x : T (r := r)) : torusChar k x = conj (torusChar (-k) x) := by
      rw [← torusChar_neg, neg_neg]
    simp_rw [hk, fejerTorus_moment]
  simp_rw [h]
  have hK := (Complex.continuous_ofReal.tendsto 1).comp (fejerTorus_multiplier_tendsto (-k))
  simpa using tendsto_const_nhds.mul hK


private noncomputable def phaseCoeffs (z : T (r := r)) (c : Fin (n + 1) → ℂ) :
    Fin (n + 1) → ℂ := fun i => torusChar (D.augMode i) z * c i

private lemma phaseCoeffs_trunc (z : T (r := r)) (c : Fin (n + 1) → ℂ) (j : ℕ) :
    phaseCoeffs D z (truncCoeff j c) = truncCoeff j (phaseCoeffs D z c) := by
  funext i
  by_cases hi : i.val < j <;> simp [phaseCoeffs, truncCoeff, hi]

private lemma phaseCoeffs_qform_one (z : T (r := r)) (c : Fin (n + 1) → ℂ) :
    qform (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (phaseCoeffs D z c) = qform 1 c := by
  rw [qform_one, qform_one, PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
  simp [phaseCoeffs, norm_mul]

private lemma integrable_kernel_form (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (c : Fin (n + 1) → ℂ) :
    Integrable (fun z => fejerTorus N z * qform B (phaseCoeffs D z c)) := by
  have ht (i : Fin (n + 1)) : Continuous (fun z => phaseCoeffs D z c i) :=
    (continuous_torusChar _).mul_const _
  let f (z : T (r := r)) := star (phaseCoeffs D z c) ⬝ᵥ (B *ᵥ phaseCoeffs D z c)
  have hcont : Continuous f := by
    unfold f
    simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Complex.star_def]
    exact continuous_finsetSum _ fun i _ =>
      (continuous_conj.comp (ht i)).mul
        (continuous_finsetSum _ fun j _ => (ht j).const_mul _)
  have h := (continuous_fejerTorus N).mul (Complex.continuous_re.comp hcont)
  exact h.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- The smoothed quadratic form is a probability average of phase rotations of the old form. -/
lemma smoothData_qform (c : Fin (n + 1) → ℂ) :
    qform (smoothData D N).toData.complexGram c =
      ∫ z, fejerTorus N z * qform D.complexGram (phaseCoeffs D z c) := by
  let f (i j : Fin (n + 1)) (z : T (r := r)) : ℂ :=
    conj (c i) * D.complexGram i j * c j *
      ((fejerTorus N z : ℂ) * (conj (torusChar (D.augMode i) z) * torusChar (D.augMode j) z))
  have hterm (i j : Fin (n + 1)) : Continuous (f i j) := by
    apply Continuous.const_mul
    exact (Complex.continuous_ofReal.comp (continuous_fejerTorus N)).mul
      ((Complex.continuous_conj.comp (continuous_torusChar _)).mul (continuous_torusChar _))
  have hi (i j : Fin (n + 1)) : Integrable (f i j) :=
    (hterm i j).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hpt (z : T (r := r)) : (∑ i, ∑ j, f i j z).re =
      fejerTorus N z * qform D.complexGram (phaseCoeffs D z c) := by
    unfold qform
    change RCLike.re (∑ i, ∑ j, f i j z) = _
    rw [← RCLike.re_ofReal_mul]
    congr 1
    simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Complex.star_def, phaseCoeffs, map_mul,
      Finset.mul_sum, f]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ac_rfl
  have hsum : Integrable (fun z => ∑ i, ∑ j, f i j z) :=
    integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hi i j))
  simp_rw [← hpt]
  change qform (smoothData D N).toData.complexGram c =
    ∫ z, RCLike.re (∑ i, ∑ j, f i j z)
  rw [integral_re hsum, integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hi i j))]
  simp_rw [integral_finsetSum _ (fun j _ => hi _ j)]
  simp only [qform, RCLike.re_to_complex]
  congr 1
  simp only [f, integral_const_mul, dotProduct, Matrix.mulVec, Pi.star_apply, Complex.star_def,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hI
  apply Finset.sum_congr rfl
  intro j hJ
  rw [smoothData_complexGram]
  ring

private lemma integral_fejerTorus_mul_const (a : ℝ) :
    (∫ z : T (r := r), fejerTorus N z * a) = a := by
  rw [integral_mul_const, integral_fejerTorus, one_mul]

lemma smoothData_pb {K : ℝ} (h : PB D.gram K) : PB (smoothData D N).toData.gram K := by
  apply pb_of_complexify
  rw [(smoothData D N).toData.complexify_gram]
  have hc := pb_complexify h
  rw [D.complexify_gram] at hc
  refine ⟨hc.1, fun j hj c => ?_⟩
  rw [smoothData_qform, smoothData_qform, ← integral_const_mul]
  apply integral_mono (integrable_kernel_form D N _ _)
    ((integrable_kernel_form D N _ _).const_mul _)
  intro z
  change fejerTorus N z * qform D.complexGram (phaseCoeffs D z (truncCoeff j c)) ≤
    K ^ 2 * (fejerTorus N z * qform D.complexGram (phaseCoeffs D z c))
  rw [phaseCoeffs_trunc, mul_left_comm (K ^ 2)]
  exact mul_le_mul_of_nonneg_left (hc.2 j hj _) (fejerTorus_nonneg _ _)

lemma smoothData_floor {a : ℝ} (h : a • 1 ≤ D.gram) :
    a • 1 ≤ (smoothData D N).toData.gram := by
  apply complexify_le_iff.mp
  rw [complexify_smul, complexify_one, (smoothData D N).toData.complexify_gram]
  have hc := complexify_le_iff.mpr h
  rw [complexify_smul, complexify_one, D.complexify_gram] at hc
  apply matrix_le_of_qform_le (Matrix.isHermitian_one.smul (IsSelfAdjoint.all _))
    (smoothData D N).toData.complexGram_posDef.isHermitian
  intro c
  rw [smoothData_qform, qform_smul, ← integral_fejerTorus_mul_const (r := r) N (a * qform 1 c)]
  apply integral_mono ((integrable_fejerTorus (r := r) N).mul_const _)
    (integrable_kernel_form D N _ _)
  intro z
  have hq := qform_mono hc (phaseCoeffs D z c)
  rw [qform_smul, phaseCoeffs_qform_one] at hq
  exact mul_le_mul_of_nonneg_left hq (fejerTorus_nonneg _ _)


private lemma phaseCoeffs_pairing (z : T (r := r)) (u v : Fin (n + 1) → ℂ) :
    star (phaseCoeffs D z u) ⬝ᵥ phaseCoeffs D z v = star u ⬝ᵥ v := by
  simp only [dotProduct, Pi.star_apply, Complex.star_def, phaseCoeffs, map_mul]
  apply Finset.sum_congr rfl
  intro i hi
  have h : conj (torusChar (D.augMode i) z) * torusChar (D.augMode i) z = 1 := by
    simp [Complex.conj_mul']
  linear_combination conj (u i) * v i * h

private lemma qform_scalar_shift (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (a : ℂ) (c : Fin (n + 1) → ℂ) :
    qform B (a • c) = ‖a‖ ^ 2 * qform B c := by
  simp only [qform, star_smul, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct,
    smul_eq_mul, ← mul_assoc, Complex.star_def]
  rw [Complex.mul_conj', ← Complex.ofReal_pow]
  change ((↑(‖a‖ ^ 2) : ℂ) * (star c ⬝ᵥ (B *ᵥ c))).re = _
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rfl

private lemma phaseCoeffs_qform_single (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (z : T (r := r)) (i : Fin (n + 1)) :
    qform B (phaseCoeffs D z (Pi.single i 1)) = qform B (Pi.single i 1) := by
  have h : phaseCoeffs D z (Pi.single i 1) =
      torusChar (D.augMode i) z • Pi.single i 1 := by
    funext j
    by_cases hj : j = i
    · subst j
      simp [phaseCoeffs]
    · simp [phaseCoeffs, Pi.single_apply, hj]
  rw [h, qform_scalar_shift, norm_torusChar, one_pow, one_mul]

/-- Convexity of the inverse on single-coordinate tests preserves every inverse diagonal. -/
lemma smoothData_inverse_diagonal_le (i : Fin (n + 1)) :
    (smoothData D N).toData.gram⁻¹ i i ≤ D.gram⁻¹ i i := by
  let E := (smoothData D N).toData
  let v : Fin (n + 1) → ℂ := Pi.single i 1
  let c := E.complexGram⁻¹ *ᵥ v
  have hvar : qform E.complexGram⁻¹ v =
      2 * RCLike.re (star v ⬝ᵥ c) - qform E.complexGram c :=
    (qform_inv_eq_optimum E.complexGram_posDef v).symm
  let a := 2 * RCLike.re (star v ⬝ᵥ c)
  have hz (z : T (r := r)) :
      a - qform D.complexGram (phaseCoeffs D z c) ≤ qform D.complexGram⁻¹ v := by
    have h := qform_inv_ge D.complexGram_posDef (phaseCoeffs D z v) (phaseCoeffs D z c)
    rwa [phaseCoeffs_pairing, phaseCoeffs_qform_single] at h
  have hleft : Integrable (fun z : T (r := r) => fejerTorus N z * a -
      fejerTorus N z * qform D.complexGram (phaseCoeffs D z c)) :=
    ((integrable_fejerTorus (r := r) N).mul_const _).sub (integrable_kernel_form D N _ _)
  have hi := integral_mono hleft ((integrable_fejerTorus (r := r) N).mul_const
      (qform D.complexGram⁻¹ v))
    (fun z => by
      rw [← mul_sub]
      exact mul_le_mul_of_nonneg_left (hz z) (fejerTorus_nonneg _ _))
  rw [integral_sub ((integrable_fejerTorus (r := r) N).mul_const _) (integrable_kernel_form D N _ _),
    integral_fejerTorus_mul_const, integral_fejerTorus_mul_const, ← smoothData_qform] at hi
  change 2 * RCLike.re (star v ⬝ᵥ c) - qform E.complexGram c ≤ _ at hi
  rw [← hvar, ← E.complexify_gram, ← D.complexify_gram,
    complexify_inv_of_posDef E.gram_posDef, complexify_inv_of_posDef D.gram_posDef] at hi
  simpa [qform, v] using hi

lemma smoothData_gram_tendsto :
    Tendsto (fun N => (smoothData D N).toData.gram) atTop (𝓝 D.gram) := by
  apply tendsto_pi_nhds.2
  intro i
  apply tendsto_pi_nhds.2
  intro j
  exact (Complex.continuous_re.tendsto _).comp (smoothData_complexGram_tendsto D i j)

lemma smoothData_gain_tendsto :
    Tendsto (fun N => (smoothData D N).toData.gain) atTop (𝓝 D.gain) := by
  have hdet : D.gram.det ≠ 0 :=
    isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).1 D.gram_posDef.isUnit)
  have hinv : ContinuousAt (fun B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ => B⁻¹) D.gram :=
    continuousAt_matrix_inv _ (by simp only [Ring.inverse_eq_inv']; exact continuousAt_inv₀ hdet)
  have ht := hinv.tendsto.comp (smoothData_gram_tendsto D)
  have hentry : Continuous (fun B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ => B 0 0) :=
    (continuous_apply _).comp (continuous_apply _)
  have h' := (hentry.tendsto D.gram⁻¹).comp ht
  have hg (N : ℕ) : (smoothData D N).toData.gain =
      D.mass * (smoothData D N).toData.gram⁻¹ 0 0 - 1 := by
    have h := (smoothData D N).toData.mass_mul_gram_inv_zero_zero
    rw [smoothData_mass] at h
    linarith only [h]
  simp_rw [hg]
  have hlim : D.mass * D.gram⁻¹ 0 0 - 1 = D.gain := by rw [D.mass_mul_gram_inv_zero_zero]; ring
  rw [← hlim]
  exact (tendsto_const_nhds.mul h').sub tendsto_const_nhds

end SchauderBasisOrbits.Scalar

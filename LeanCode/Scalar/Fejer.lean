import LeanCode.Scalar.Data
import LeanCode.Fourier.TorusPolynomial

open Filter MeasureTheory Matrix Complex
open scoped ComplexConjugate BigOperators InnerProductSpace ENNReal Topology

namespace SchauderBasisOrbits.Scalar

local notation "𝕋" => UnitAddCircle
local notation "μ𝕋" => (@AddCircle.haarAddCircle 1 _)

private lemma circleFourier_norm (k : ℤ) (x : 𝕋) : ‖fourier k x‖ = 1 := by
  rw [fourier_apply, Circle.norm_coe]

private lemma circleFourier_integrable (k : ℤ) : Integrable (fun x : 𝕋 => fourier k x) μ𝕋 :=
  Integrable.of_bound (fourier k).continuous.measurable.aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun x => (circleFourier_norm k x).le)

private lemma circleFourier_integral (k : ℤ) :
    (∫ x : 𝕋, fourier k x ∂μ𝕋) = if k = 0 then 1 else 0 := by
  have h := orthonormal_iff_ite.mp (@orthonormal_fourier 1 _) 0 k
  have he : ⟪@fourierLp 1 _ 2 _ 0, @fourierLp 1 _ 2 _ k⟫_ℂ =
      ∫ x : 𝕋, fourier k x ∂μ𝕋 := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [@coeFn_fourierLp 1 _ 2 _ 0, @coeFn_fourierLp 1 _ 2 _ k] with x h0 hk
    rw [h0, hk, RCLike.inner_apply', fourier_zero, map_one, one_mul]
  rw [← he, h]
  by_cases hk : k = 0
  · simp [hk]
  · rw [ite_eq_right (Ne.symm hk), ite_eq_right hk]

/-- A finite Fejér kernel written as the normalized square of a character sum. -/
noncomputable def fejer (N : ℕ) (x : 𝕋) : ℝ :=
  ‖∑ j ∈ Finset.Icc 0 (N : ℤ), fourier j x‖ ^ 2 / (N + 1 : ℝ)

lemma fejer_nonneg (N : ℕ) (x : 𝕋) : 0 ≤ fejer N x := by
  unfold fejer
  positivity

lemma continuous_fejer (N : ℕ) : Continuous (fejer N) := by
  unfold fejer
  have hs : Continuous (fun x : 𝕋 => ∑ j ∈ Finset.Icc 0 (N : ℤ), fourier j x) :=
    continuous_finsetSum _ fun j _ => (fourier j).continuous
  exact (hs.norm.pow 2).div_const _

lemma fejer_even (N : ℕ) (x : 𝕋) : fejer N (-x) = fejer N x := by
  have h (j : ℤ) : fourier j (-x) = conj (fourier j x) := by
    rw [← fourier_neg, fourier_apply, fourier_apply, zsmul_neg, neg_zsmul]
  simp [fejer, h, ← map_sum]

/-- The expanded kernel is a finite character polynomial indexed by Fourier-pair differences. -/
lemma ofReal_fejer (N : ℕ) (x : 𝕋) :
    (fejer N x : ℂ) =
      (∑ j ∈ Finset.Icc 0 (N : ℤ), ∑ k ∈ Finset.Icc 0 (N : ℤ),
        fourier (j - k) x) / (N + 1 : ℂ) := by
  simp only [fejer, Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_add,
    Complex.ofReal_natCast, Complex.ofReal_one, ← Complex.mul_conj']
  congr 1
  rw [map_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [sub_eq_add_neg, fourier_add, fourier_neg]

/-- The kernel's normalized Fourier-pair count. -/
noncomputable def fejerMultiplier (N : ℕ) (k : ℤ) : ℝ :=
  (∑ j ∈ Finset.Icc 0 (N : ℤ), ∑ i ∈ Finset.Icc 0 (N : ℤ),
    if j - i = k then (1 : ℝ) else 0) / (N + 1 : ℝ)

lemma fejer_moment (N : ℕ) (k : ℤ) :
    (∫ x : 𝕋, (fejer N x : ℂ) * conj (fourier k x) ∂μ𝕋) = (fejerMultiplier N k : ℂ) := by
  have hterm (i j : ℤ) (x : 𝕋) :
      fourier (j - i) x * conj (fourier k x) = fourier (j - i - k) x := by
    rw [sub_eq_add_neg (j - i), fourier_add, fourier_neg]
  have hf x : (fejer N x : ℂ) * conj (fourier k x) =
      (N + 1 : ℂ)⁻¹ * ∑ j ∈ Finset.Icc 0 (N : ℤ), ∑ i ∈ Finset.Icc 0 (N : ℤ),
        fourier (j - i - k) x := by
    rw [ofReal_fejer, div_eq_inv_mul, mul_assoc, Finset.sum_mul]
    simp_rw [Finset.sum_mul, hterm]
  simp_rw [hf]
  rw [integral_const_mul, integral_finsetSum]
  · simp_rw [integral_finsetSum _ (fun i _ => circleFourier_integrable (_ - i - k)),
      circleFourier_integral, sub_eq_zero]
    simp [fejerMultiplier, ofReal_sum, div_eq_inv_mul]
  · intro j hj
    exact integrable_finsetSum _ (fun i _ => circleFourier_integrable (j - i - k))

lemma fejerMultiplier_eq_count (N : ℕ) (k : ℤ) :
    fejerMultiplier N k =
      ((Finset.Icc (max 0 k) (min (N : ℤ) ((N : ℤ) + k))).card : ℝ) / (N + 1 : ℝ) := by
  unfold fejerMultiplier
  congr 1
  have hsum (j : ℤ) :
      (∑ i ∈ Finset.Icc 0 (N : ℤ), if j - i = k then (1 : ℝ) else 0) =
        if j - k ∈ Finset.Icc 0 (N : ℤ) then 1 else 0 := by
    simp_rw [show ∀ i : ℤ, j - i = k ↔ i = j - k from fun i => by omega]
    simp
  simp_rw [hsum, ← Finset.sum_filter]
  rw [Finset.sum_const, nsmul_eq_mul, mul_one]
  have hfilter : (Finset.Icc (0 : ℤ) (N : ℤ)).filter (fun j => j - k ∈ Finset.Icc 0 (N : ℤ)) =
      Finset.Icc (max 0 k) (min (N : ℤ) ((N : ℤ) + k)) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_Icc, max_le_iff, le_min_iff]
    omega
  rw [hfilter]

lemma fejerMultiplier_zero (N : ℕ) : fejerMultiplier N 0 = 1 := by
  rw [fejerMultiplier_eq_count]
  simp only [max_self, add_zero, min_self, Int.card_Icc]
  rw [show ((N : ℤ) + 1 - 0).toNat = N + 1 by omega]
  push_cast
  exact div_self (by positivity)

lemma integral_fejer (N : ℕ) : ∫ x : 𝕋, fejer N x ∂μ𝕋 = 1 := by
  have h := fejer_moment N 0
  rw [fejerMultiplier_zero] at h
  simp only [fourier_zero, map_one, mul_one, ofReal_one, integral_complex_ofReal] at h
  exact_mod_cast h


lemma fejerMultiplier_eq_truncated (N : ℕ) (k : ℤ) :
    fejerMultiplier N k = ((N + 1 - k.natAbs : ℕ) : ℝ) / (N + 1 : ℝ) := by
  rw [fejerMultiplier_eq_count, Int.card_Icc]
  congr 2
  cases k with
  | ofNat k =>
    have h₀ : 0 ≤ Int.ofNat k := Int.natCast_nonneg k
    rw [max_eq_right h₀, min_eq_left (by omega)]
    omega
  | negSucc k =>
    rw [max_eq_left (by omega), min_eq_right (by omega)]
    simp only [Int.natAbs_negSucc]
    omega

lemma fejerMultiplier_tendsto (k : ℤ) :
    Tendsto (fun N => fejerMultiplier N k) atTop (𝓝 1) := by
  have hden : Tendsto (fun N : ℕ => ((N : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp
      (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop)
  have ht : Tendsto (fun N : ℕ => 1 - (k.natAbs : ℝ) * ((N : ℝ) + 1)⁻¹) atTop (𝓝 1) := by
    convert (tendsto_const_nhds.sub (tendsto_const_nhds.mul hden)) using 1
    norm_num
  apply ht.congr'
  filter_upwards [eventually_ge_atTop k.natAbs] with N hN
  rw [fejerMultiplier_eq_truncated, Nat.cast_sub (by omega), Nat.cast_add, Nat.cast_one]
  field_simp

/-- The product Fejér kernel on a finite torus. -/
noncomputable def fejerTorus {ι : Type*} [Fintype ι] (N : ℕ) (x : UnitAddTorus ι) : ℝ :=
  ∏ i, fejer N (x i)

lemma fejerTorus_nonneg {ι : Type*} [Fintype ι] (N : ℕ) (x : UnitAddTorus ι) :
    0 ≤ fejerTorus N x :=
  Finset.prod_nonneg fun _ _ => fejer_nonneg _ _

lemma fejerTorus_even {ι : Type*} [Fintype ι] (N : ℕ) (x : UnitAddTorus ι) :
    fejerTorus N (-x) = fejerTorus N x := by
  simp only [fejerTorus, Pi.neg_apply, fejer_even]

noncomputable local instance fejerCircleMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

local instance fejerCircleProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure (@AddCircle.haarAddCircle 1 _))

lemma integral_fejerTorus {ι : Type*} [Fintype ι] (N : ℕ) :
    ∫ x : UnitAddTorus ι, fejerTorus N x = 1 := by
  unfold fejerTorus
  rw [integral_fintype_prod_volume_eq_prod]
  have h : (∫ x : 𝕋, fejer N x) = 1 := integral_fejer N
  simp [h]

/-- The polynomial witnessing the finite expansion of the product kernel. -/
noncomputable def fejerTorusPoly (ι : Type*) [Fintype ι] [DecidableEq ι] (N : ℕ) : TorusPoly ι :=
  ∏ i : ι, (N + 1 : ℂ)⁻¹ •
    ∑ j ∈ Finset.Icc (0 : ℤ) (N : ℤ), ∑ k ∈ Finset.Icc (0 : ℤ) (N : ℤ),
      AddMonoidAlgebra.single (Pi.single i (j - k)) 1

lemma eval_fejerTorusPoly {ι : Type*} [Fintype ι] [DecidableEq ι]
    (N : ℕ) (x : UnitAddTorus ι) :
    evalTorusPoly (fejerTorusPoly ι N) x = (fejerTorus N x : ℂ) := by
  simp only [fejerTorusPoly, fejerTorus, Complex.ofReal_prod, evalTorusPoly_prod, evalTorusPoly_smul,
    evalTorusPoly_sum, evalTorusPoly_single, one_mul, torusChar_single, ofReal_fejer,
    div_eq_inv_mul]

lemma fejerTorus_moment {ι : Type*} [Fintype ι] (N : ℕ) (k : ι → ℤ) :
    (∫ x : UnitAddTorus ι, (fejerTorus N x : ℂ) * conj (torusChar k x)) =
      ((∏ i, fejerMultiplier N (k i) : ℝ) : ℂ) := by
  simp only [fejerTorus, Complex.ofReal_prod, torusChar, UnitAddTorus.mFourier,
    ContinuousMap.coe_mk, map_prod, ← Finset.prod_mul_distrib]
  rw [integral_fintype_prod_volume_eq_prod (fun i (x : 𝕋) => (fejer N x : ℂ) * conj (fourier (k i) x))]
  apply Finset.prod_congr rfl
  intro i hi
  exact fejer_moment N (k i)

lemma fejerTorus_multiplier_tendsto {ι : Type*} [Fintype ι] (k : ι → ℤ) :
    Tendsto (fun N => ∏ i, fejerMultiplier N (k i)) atTop (𝓝 1) := by
  simpa using (tendsto_finsetProd Finset.univ
    (fun (i : ι) _ => fejerMultiplier_tendsto (k i)))

end SchauderBasisOrbits.Scalar

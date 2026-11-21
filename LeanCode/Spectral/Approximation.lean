import LeanCode.Target.Group
import LeanCode.Fourier.RealTotality
import LeanCode.Spectral.Triangle
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

open Complex MeasureTheory Set Filter
open scoped FourierTransform InnerProductSpace ComplexConjugate

namespace SchauderBasisOrbits

variable {H : Type*} [ComplexHilbertSpace H] {U : ℝ → UnitaryOperator H}

noncomputable def orbitCoefficient (U : ℝ → UnitaryOperator H) (v : H) (t : ℝ) : ℂ :=
  ⟪v, U t v⟫_ℂ

theorem continuous_orbitCoefficient (hU : IsStronglyContinuousGroup U) (v : H) :
    Continuous (orbitCoefficient U v) :=
  continuous_const.inner (continuous_orbit hU v)

theorem orbitCoefficient_zero (hU : IsStronglyContinuousGroup U) {v : H} (hv : ‖v‖ = 1) :
    orbitCoefficient U v 0 = 1 := by
  simp [orbitCoefficient, unitary_group_zero hU, inner_self_eq_norm_sq_to_K, hv]

theorem norm_orbitCoefficient_le_one {v : H} (hv : ‖v‖ = 1) (t : ℝ) :
    ‖orbitCoefficient U v t‖ ≤ 1 := by
  simpa [orbitCoefficient, unitary_group_norm, hv] using norm_inner_le_norm (𝕜 := ℂ) v (U t v)

theorem orbit_inner_eq_coefficient (hU : IsStronglyContinuousGroup U) (v : H) (s t : ℝ) :
    ⟪U s v, U t v⟫_ℂ = orbitCoefficient U v (t - s) := by
  rw [orbitCoefficient, ← unitary_group_inner s v (U (t - s) v), ← unitary_group_add hU]
  rw [show s + (t - s) = t by ring]

theorem orbitCoefficient_neg (hU : IsStronglyContinuousGroup U) (v : H) (t : ℝ) :
    orbitCoefficient U v (-t) = conj (orbitCoefficient U v t) := by
  rw [← zero_sub, ← orbit_inner_eq_coefficient hU, unitary_group_zero hU, orbitCoefficient,
    inner_conj_symm]

theorem fourier_eq_integral_realChar (f : ℝ → ℂ) (t : ℝ) :
    𝓕 f t = ∫ x, realChar (-t) x * f x := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [realChar, smul_eq_mul]
  rw [show -2 * Real.pi * x * t = 2 * Real.pi * (-t) * x by ring]

theorem fourierInv_eq_integral_realChar (f : ℝ → ℂ) (t : ℝ) :
    𝓕⁻ f t = ∫ x, realChar t x * f x := by
  rw [Real.fourierInv_eq_fourier_neg, fourier_eq_integral_realChar, neg_neg]

theorem fourier_gaussian_realChar {a : ℝ} (ha : 0 < a) (t : ℝ) :
    ∫ x, realChar (-t) x * (↑(Real.exp (-Real.pi * a * x ^ 2)) : ℂ) =
      ↑((Real.sqrt a)⁻¹ * Real.exp (-Real.pi / a * t ^ 2)) := by
  have h := congrFun (fourier_gaussian_pi (b := (a : ℂ)) (by simpa using ha)) t
  rw [fourier_eq_integral_realChar] at h
  simp only [← Complex.ofReal_pow, ← Complex.ofReal_mul, ← Complex.ofReal_neg,
    ← Complex.ofReal_exp, ← Complex.ofReal_div] at h
  have hhalf : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by norm_num
  rw [hhalf, ← Complex.ofReal_cpow ha.le, ← Real.sqrt_eq_rpow, one_div, ← Complex.ofReal_inv,
    ← Complex.ofReal_mul] at h
  exact h

/-- The triangular window with half-width T. -/
noncomputable def triangularWindow (T t : ℝ) : ℝ := max 0 (1 - |t| / T)

theorem continuous_triangularWindow (T : ℝ) : Continuous (triangularWindow T) :=
  continuous_const.max (continuous_const.sub (continuous_abs.div_const T))

theorem triangularWindow_nonneg (T t : ℝ) : 0 ≤ triangularWindow T t := le_max_left _ _

theorem triangularWindow_le_one {T : ℝ} (hT : 0 < T) (t : ℝ) :
    triangularWindow T t ≤ 1 := by
  refine max_le zero_le_one (sub_le_self _ ?_)
  exact div_nonneg (abs_nonneg t) hT.le

theorem triangularWindow_eq_zero {T t : ℝ} (hT : 0 < T) (ht : T ≤ |t|) :
    triangularWindow T t = 0 := by
  apply max_eq_left
  rw [sub_nonpos, le_div_iff₀ hT, one_mul]
  exact ht

@[simp] theorem triangularWindow_zero (T : ℝ) : triangularWindow T 0 = 1 := by
  simp [triangularWindow]

noncomputable def windowedCoefficient (U : ℝ → UnitaryOperator H) (v : H) (T t : ℝ) : ℂ :=
  (triangularWindow T t : ℂ) * orbitCoefficient U v t

theorem continuous_windowedCoefficient (hU : IsStronglyContinuousGroup U) (v : H) (T : ℝ) :
    Continuous (windowedCoefficient U v T) :=
  (Complex.continuous_ofReal.comp (continuous_triangularWindow T)).mul
    (continuous_orbitCoefficient hU v)

theorem hasCompactSupport_windowedCoefficient (v : H) {T : ℝ} (hT : 0 < T) :
    HasCompactSupport (windowedCoefficient U v T) := by
  apply HasCompactSupport.of_support_subset_isCompact isCompact_Icc
  intro t ht
  by_contra hout
  apply ht
  have habs : T ≤ |t| := by
    by_contra! habs
    exact hout ⟨(abs_lt.mp habs).1.le, (abs_lt.mp habs).2.le⟩
  simp [windowedCoefficient, triangularWindow_eq_zero hT habs]

theorem integrable_windowedCoefficient (hU : IsStronglyContinuousGroup U) (v : H) {T : ℝ}
    (hT : 0 < T) :
    Integrable (windowedCoefficient U v T) :=
  (continuous_windowedCoefficient hU v T).integrable_of_hasCompactSupport
    (hasCompactSupport_windowedCoefficient v hT)

noncomputable def orbitDensity (U : ℝ → UnitaryOperator H) (v : H) (T : ℝ) (x : ℝ) : ℂ :=
  𝓕 (windowedCoefficient U v T) x

theorem continuous_orbitDensity (hU : IsStronglyContinuousGroup U) (v : H) {T : ℝ} (hT : 0 < T) :
    Continuous (orbitDensity U v T) := by
  have heq : orbitDensity U v T = densityFourier volume (windowedCoefficient U v T) := by
    ext x
    exact fourier_eq_integral_realChar _ _
  rw [heq]
  exact continuous_densityFourier (integrable_windowedCoefficient hU v hT)

private theorem integral_inner_left {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → H} (hf : Integrable f μ) (y : H) :
    ⟪∫ x, f x ∂μ, y⟫_ℂ = ∫ x, ⟪f x, y⟫_ℂ ∂μ := by
  calc
    _ = conj (⟪y, ∫ x, f x ∂μ⟫_ℂ) := (inner_conj_symm _ _).symm
    _ = _ := by rw [← integral_inner hf, ← integral_conj]; simp_rw [inner_conj_symm]

private theorem realChar_diff_product (s t x : ℝ) :
    conj (realChar (-x) s) * realChar (-x) t = realChar (-x) (t - s) := by
  rw [← realChar_neg, neg_neg, sub_eq_add_neg, realChar_add_arg, mul_comm]
  congr 1
  rw [realChar, realChar, show 2 * Real.pi * x * s = 2 * Real.pi * (-x) * (-s) by ring]

private theorem scale_triangularWindow {T : ℝ} (hT : 0 < T) (t : ℝ) :
    T * triangularWindow T t = max 0 (T - |t|) := by
  unfold triangularWindow
  rw [mul_max_of_nonneg _ _ hT.le, mul_zero, mul_sub, mul_one]
  rw [mul_div_cancel₀ _ hT.ne']

theorem orbitDensity_eq_norm_sq (hU : IsStronglyContinuousGroup U) (v : H)
    {T : ℝ} (hT : 0 < T) (x : ℝ) :
    orbitDensity U v T x =
      ↑(T⁻¹ * ‖∫ s in Icc 0 T, realChar (-x) s • U s v‖ ^ 2) := by
  let F (s : ℝ) := realChar (-x) s • U s v
  have hi : IntegrableOn F (Icc 0 T) :=
    ((continuous_realChar (-x)).smul (continuous_orbit hU v)).continuousOn.integrableOn_compact
      isCompact_Icc
  let J : H := ∫ s in Icc 0 T, F s
  have hpair (s t : ℝ) :
      ⟪F s, F t⟫_ℂ = realChar (-x) (t - s) * orbitCoefficient U v (t - s) := by
    simp only [F, inner_smul_left, inner_smul_right, orbit_inner_eq_coefficient hU, ← mul_assoc]
    rw [mul_comm (realChar (-x) t), realChar_diff_product]
  have hJ :
      ⟪J, J⟫_ℂ = ∫ s in Icc 0 T, ∫ t in Icc 0 T,
        realChar (-x) (t - s) * orbitCoefficient U v (t - s) := by
    rw [show ⟪J, J⟫_ℂ = ⟪∫ s in Icc 0 T, F s, J⟫_ℂ from rfl, integral_inner_left hi J]
    simp_rw [J, ← integral_inner hi, hpair]
  rw [integral_square_difference T (g := fun t ↦ realChar (-x) t * orbitCoefficient U v t)
    ((continuous_realChar (-x)).mul (continuous_orbitCoefficient hU v)),
    inner_self_eq_norm_sq_to_K] at hJ
  change (↑‖J‖ : ℂ) ^ 2 = _ at hJ
  change orbitDensity U v T x = ((T⁻¹ * ‖J‖ ^ 2 : ℝ) : ℂ)
  rw [Complex.ofReal_mul, Complex.ofReal_pow, hJ]
  simp only [orbitDensity, fourier_eq_integral_realChar, ← integral_const_mul, windowedCoefficient]
  apply integral_congr_ae
  filter_upwards [] with t
  rw [← scale_triangularWindow hT t, Complex.ofReal_mul, Complex.ofReal_inv,
    show realChar (-x) t = realChar (-t) x by
      rw [realChar, realChar, show 2 * Real.pi * (-x) * t = 2 * Real.pi * (-t) * x by ring]]
  field_simp [Complex.ofReal_ne_zero.mpr hT.ne']

theorem orbitDensity_re_nonneg (hU : IsStronglyContinuousGroup U) (v : H) {T : ℝ}
    (hT : 0 < T) (x : ℝ) : 0 ≤ (orbitDensity U v T x).re := by
  rw [orbitDensity_eq_norm_sq hU v hT, Complex.ofReal_re]
  positivity

theorem ofReal_orbitDensity_re (hU : IsStronglyContinuousGroup U) (v : H) {T : ℝ}
    (hT : 0 < T) (x : ℝ) : ((orbitDensity U v T x).re : ℂ) = orbitDensity U v T x := by
  rw [orbitDensity_eq_norm_sq hU v hT, Complex.ofReal_re]

end SchauderBasisOrbits

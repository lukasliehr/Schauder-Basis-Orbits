import LeanCode.Spectral.Approximation
import Mathlib.Analysis.Fourier.Inversion

open Complex MeasureTheory Set Filter
open scoped FourierTransform ENNReal InnerProductSpace Topology

namespace SchauderBasisOrbits

private noncomputable def gauss (a x : ℝ) : ℝ := Real.exp (-Real.pi * a * x ^ 2)

private theorem integrable_gauss {a : ℝ} (ha : 0 < a) : Integrable (gauss a) := by
  change Integrable (fun x : ℝ ↦ Real.exp (-Real.pi * a * x ^ 2))
  simpa only [neg_mul] using integrable_exp_neg_mul_sq (mul_pos Real.pi_pos ha)

private theorem gaussian_regularized_fourier_mass {a : ℝ} (ha : 0 < a)
    {f : ℝ → ℂ} (hf : Integrable f) :
    (∫ x, (𝓕 f x) * (↑(gauss a x) : ℂ)) =
      ∫ t, f t * (↑((Real.sqrt a)⁻¹ * Real.exp (-Real.pi / a * t ^ 2)) : ℂ) := by
  have hflip : (innerₗ ℝ : ℝ →ₗ[ℝ] ℝ →ₗ[ℝ] ℝ).flip = innerₗ ℝ := by
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    change inner ℝ y x = inner ℝ x y
    exact real_inner_comm x y
  let g : ℝ → ℂ := fun x ↦ ↑(gauss a x)
  have hg : Integrable g := (integrable_gauss ha).ofReal
  have heq := VectorFourier.integral_fourierIntegral_smul_eq_flip
    (L := (innerₗ ℝ : ℝ →ₗ[ℝ] ℝ →ₗ[ℝ] ℝ)) (μ := volume) (ν := volume)
    Real.continuous_fourierChar (continuous_inner (𝕜 := ℝ)) hf hg
  rw [hflip] at heq
  change (∫ x, (𝓕 f x) * (↑(gauss a x) : ℂ)) =
    ∫ t, f t * (𝓕 (fun x ↦ (↑(gauss a x) : ℂ)) t) at heq
  rw [heq]
  apply integral_congr_ae
  filter_upwards [] with t
  congr 1
  rw [fourier_eq_integral_realChar]
  exact fourier_gaussian_realChar ha t

private theorem gauss_rescale {r : ℝ} (hr : 0 < r) (f : ℝ → ℂ) :
    (∫ t, f t * (↑((Real.sqrt (r ^ 2))⁻¹ * Real.exp (-Real.pi / r ^ 2 * t ^ 2)) : ℂ)) =
      ∫ x, f (r * x) * (↑(gauss 1 x) : ℂ) := by
  have h := Measure.integral_comp_mul_left (fun x : ℝ ↦
    f x * (↑(Real.exp (-Real.pi / r ^ 2 * x ^ 2)) : ℂ)) r
  have hx (x : ℝ) : -Real.pi / r ^ 2 * (r * x) ^ 2 = -Real.pi * 1 * x ^ 2 := by
    field_simp
  simp only [hx, abs_of_nonneg (inv_nonneg.mpr hr.le)] at h
  change _ = ∫ x, f (r * x) * (↑(Real.exp (-Real.pi * 1 * x ^ 2)) : ℂ)
  simp only [Real.sqrt_sq hr.le, Complex.ofReal_mul, Complex.real_smul] at h ⊢
  refine Eq.trans ?_ h.symm
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with x
  ring

private theorem integrable_fourier_of_nonneg {f : ℝ → ℂ} (hf : Integrable f)
    (hfc : Continuous f) (hf0 : f 0 = 1) (hbound : ∀ x, ‖f x‖ ≤ 1)
    (hQ : ∀ x, 0 ≤ (𝓕 f x).re)
    (hQR : ∀ x, ((𝓕 f x).re : ℂ) = 𝓕 f x) :
    Integrable (fun x ↦ (𝓕 f x).re) ∧ (∫ x, (𝓕 f x).re) = 1 := by
  let r : ℕ → ℝ := fun n ↦ 1 / ((n : ℝ) + 1)
  have hr (n : ℕ) : 0 < r n := by dsimp [r]; positivity
  have hrlim : Tendsto r atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hanti : Antitone r := by
    intro i j hij
    change 1 / ((j : ℝ) + 1) ≤ 1 / ((i : ℝ) + 1)
    exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hij 1)
  let q : ℝ → ℝ := fun x ↦ (𝓕 f x).re
  have hqc : Continuous q := by
    have hfourier : (𝓕 f) = densityFourier volume f := by
      funext t
      exact fourier_eq_integral_realChar f t
    exact Complex.continuous_re.comp (hfourier ▸ continuous_densityFourier hf)
  let qr (n : ℕ) (x : ℝ) := q x * gauss (r n ^ 2) x
  have hqrc (n : ℕ) : Continuous (qr n) := by
    apply hqc.mul
    unfold gauss
    fun_prop
  have hqri (n : ℕ) : Integrable (qr n) := by
    refine ((integrable_gauss (show 0 < r n ^ 2 from sq_pos_of_pos (hr n))).const_mul
      (∫ x, ‖f x‖)).mono' (hqrc n).aestronglyMeasurable ?_
    filter_upwards [] with x
    rw [show ‖qr n x‖ = q x * gauss (r n ^ 2) x from Real.norm_of_nonneg
      (mul_nonneg (hQ x) (Real.exp_pos _).le)]
    exact mul_le_mul_of_nonneg_right
      ((Complex.re_le_norm _).trans (Real.norm_fourier_le_integral_norm f x)) (Real.exp_pos _).le
  have hscaled :
      Tendsto (fun n ↦ ∫ x, f (r n * x) * (↑(gauss 1 x) : ℂ)) atTop (𝓝 1) := by
    have hlim : (∫ x, (↑(gauss 1 x) : ℂ)) = 1 := by
      rw [integral_complex_ofReal]
      have h : (∫ x, gauss 1 x) = 1 := by
        simpa [gauss, integral_gaussian, Real.pi_ne_zero] using integral_gaussian Real.pi
      simp [h]
    rw [← hlim]
    apply tendsto_integral_of_dominated_convergence (gauss 1)
    · intro n
      apply Continuous.aestronglyMeasurable
      exact (hfc.comp (continuous_const.mul continuous_id)).mul (Complex.continuous_ofReal.comp
        (by unfold gauss; fun_prop))
    · exact integrable_gauss zero_lt_one
    · intro n
      filter_upwards [] with x
      rw [norm_mul, Complex.norm_real,
        Real.norm_of_nonneg (show 0 ≤ gauss 1 x from (Real.exp_pos _).le)]
      exact mul_le_of_le_one_left (Real.exp_pos _).le (hbound _)
    · filter_upwards [] with x
      have hx : Tendsto (fun n ↦ r n * x) atTop (𝓝 0) := by simpa using hrlim.mul_const x
      simpa only [Function.comp_apply, hf0, one_mul] using
        ((hfc.continuousAt (x := 0)).tendsto.comp hx).mul_const
        (↑(gauss 1 x) : ℂ)
  have heq (n : ℕ) : Complex.ofReal (∫ x, qr n x) = ∫ x, f (r n * x) * (↑(gauss 1 x) : ℂ) := by
    rw [← gauss_rescale (hr n) f, ← gaussian_regularized_fourier_mass (sq_pos_of_pos (hr n)) hf,
      ← integral_complex_ofReal]
    apply integral_congr_ae
    filter_upwards [] with x
    simp only [qr, q, Complex.ofReal_mul, hQR]
  have hreal : Tendsto (fun n ↦ ∫ x, qr n x) atTop (𝓝 1) := by
    have hcomp := Complex.continuous_re.continuousAt.tendsto.comp hscaled
    apply hcomp.congr'
    filter_upwards [] with n
    simpa only [Function.comp_apply, Complex.ofReal_re] using
      (congrArg Complex.re (heq n)).symm
  let Q (n : ℕ) (x : ℝ) := ENNReal.ofReal (qr n x)
  have hmono : Monotone Q := by
    intro i j hij x
    apply ENNReal.ofReal_le_ofReal
    apply mul_le_mul_of_nonneg_left _ (hQ x)
    apply Real.exp_le_exp.mpr
    rw [show -Real.pi * r i ^ 2 * x ^ 2 = -(Real.pi * x ^ 2 * r i ^ 2) by ring,
      show -Real.pi * r j ^ 2 * x ^ 2 = -(Real.pi * x ^ 2 * r j ^ 2) by ring]
    exact neg_le_neg (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (hr j).le (hanti hij) 2) (by positivity))
  have hQlim (x : ℝ) : (⨆ n, Q n x) = ENNReal.ofReal (q x) := by
    apply tendsto_nhds_unique (tendsto_atTop_iSup (fun i j h ↦ hmono h x))
    apply (ENNReal.continuous_ofReal.continuousAt.tendsto.comp ?_)
    have hlim := ((hrlim.pow 2).const_mul (-Real.pi)).mul_const (x ^ 2)
    have h := ((Real.continuous_exp.continuousAt.tendsto.comp hlim).const_mul (q x))
    simpa [Q, gauss, qr] using h
  have hmass : (∫⁻ x, ENNReal.ofReal (q x)) = 1 := by
    have hconv : Tendsto (fun n ↦ ∫⁻ x, Q n x) atTop (𝓝 1) := by
      have h := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hreal
      rw [ENNReal.ofReal_one] at h
      apply h.congr'
      filter_upwards [] with n
      exact ofReal_integral_eq_lintegral_ofReal (hqri n)
        (Eventually.of_forall fun x ↦ mul_nonneg (hQ x) (Real.exp_pos _).le)
    calc
      _ = ∫⁻ x, ⨆ n, Q n x := by simp_rw [hQlim]
      _ = ⨆ n, ∫⁻ x, Q n x := lintegral_iSup (fun n ↦ (hqrc n).measurable.ennreal_ofReal) hmono
      _ = 1 := tendsto_nhds_unique
        (tendsto_atTop_iSup fun i j hij ↦ lintegral_mono (hmono hij)) hconv
  have hi : Integrable q := by
    refine ⟨hqc.aestronglyMeasurable, (hasFiniteIntegral_iff_norm _).mpr ?_⟩
    have he : (∫⁻ x, ENNReal.ofReal ‖q x‖) = ∫⁻ x, ENNReal.ofReal (q x) := by
      apply lintegral_congr
      intro x
      rw [Real.norm_of_nonneg (hQ x)]
    rw [he, hmass]
    exact ENNReal.one_lt_top
  refine ⟨hi, ?_⟩
  have he := ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall hQ)
  rw [hmass, ← ENNReal.ofReal_one] at he
  exact (ENNReal.ofReal_eq_ofReal_iff
    (integral_nonneg hQ) zero_le_one).mp he

variable {H : Type*} [ComplexHilbertSpace H] {U : ℝ → UnitaryOperator H}

theorem integrable_orbitDensity (hU : IsStronglyContinuousGroup U) {v : H} (hv : ‖v‖ = 1)
    {T : ℝ} (hT : 0 < T) :
    Integrable (fun x ↦ (orbitDensity U v T x).re) ∧ (∫ x, (orbitDensity U v T x).re) = 1 := by
  apply integrable_fourier_of_nonneg (integrable_windowedCoefficient hU v hT)
    (continuous_windowedCoefficient hU v T)
  · simp [windowedCoefficient, orbitCoefficient_zero hU hv]
  · intro t
    simp only [windowedCoefficient, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (triangularWindow_nonneg _ _)]
    exact (mul_le_mul_of_nonneg_right (triangularWindow_le_one hT _) (norm_nonneg _)).trans
      (by simpa using norm_orbitCoefficient_le_one hv t)
  · exact orbitDensity_re_nonneg hU v hT
  · exact ofReal_orbitDensity_re hU v hT

/-- Probability measure from the positive Fourier density of a triangular window. -/
noncomputable def orbitApproximant (hU : IsStronglyContinuousGroup U) {v : H}
    (hv : ‖v‖ = 1) {T : ℝ} (hT : 0 < T) : ProbabilityMeasure ℝ := by
  refine ⟨weightedMeasure volume (fun x ↦ (orbitDensity U v T x).re), ⟨?_⟩⟩
  rw [weightedMeasure, withDensity_apply _ .univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (integrable_orbitDensity hU hv hT).1
      (Eventually.of_forall (orbitDensity_re_nonneg hU v hT)),
    (integrable_orbitDensity hU hv hT).2, ENNReal.ofReal_one]

theorem integral_realChar_orbitApproximant (hU : IsStronglyContinuousGroup U) {v : H}
    (hv : ‖v‖ = 1) {T : ℝ} (hT : 0 < T) (t : ℝ) :
    (∫ x, realChar t x ∂(orbitApproximant hU hv hT).toMeasure) = windowedCoefficient U v T t := by
  have hc := continuous_orbitDensity hU v hT
  have hq : Integrable (orbitDensity U v T) := by
    refine (integrable_orbitDensity hU hv hT).1.ofReal.congr ?_
    exact Eventually.of_forall (ofReal_orbitDensity_re hU v hT)
  have hinv := congrFun ((continuous_windowedCoefficient hU v T).fourierInv_fourier_eq
    (integrable_windowedCoefficient hU v hT) hq) t
  rw [fourierInv_eq_integral_realChar] at hinv
  rw [← hinv]
  change (∫ x, realChar t x ∂weightedMeasure volume (fun x ↦ (orbitDensity U v T x).re)) = _
  have hm : Measurable (fun x ↦ ENNReal.ofReal (orbitDensity U v T x).re) :=
    (Complex.continuous_re.comp hc).measurable.ennreal_ofReal
  rw [weightedMeasure, integral_withDensity_eq_integral_toReal_smul hm
      (Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top) (realChar t)]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [ENNReal.toReal_ofReal (orbitDensity_re_nonneg hU v hT x), Complex.real_smul,
    ofReal_orbitDensity_re hU v hT x, mul_comm]
  rfl

end SchauderBasisOrbits

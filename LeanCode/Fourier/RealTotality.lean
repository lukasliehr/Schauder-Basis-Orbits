module

public import LeanCode.Measure.Weights
public import Mathlib

@[expose] public section

open MeasureTheory Filter Complex
open scoped ENNReal InnerProductSpace ComplexConjugate Topology

namespace SchauderBasisOrbits

/-- Conversion from the characteristic-function convention to the manuscript's characters. -/
theorem charFun_eq_integral_realChar (μ : Measure ℝ) (s : ℝ) :
    charFun μ s = ∫ x, realChar (s / (2 * Real.pi)) x ∂μ := by
  rw [charFun_apply_real]
  apply integral_congr_ae
  filter_upwards [] with x
  have hp : 2 * Real.pi ≠ 0 := by positivity
  have hs : 2 * Real.pi * (s / (2 * Real.pi)) = s := by field_simp
  simp [realChar, hs]

/-- The transform of an integrable complex density against real characters. -/
noncomputable def densityFourier (μ : Measure ℝ) (f : ℝ → ℂ) (t : ℝ) : ℂ :=
  ∫ x, realChar (-t) x * f x ∂μ

theorem integrable_realChar_mul {μ : Measure ℝ} {f : ℝ → ℂ} (hf : Integrable f μ) (t : ℝ) :
    Integrable (fun x ↦ realChar t x * f x) μ :=
  hf.bdd_mul (c := 1) (continuous_realChar t).aestronglyMeasurable (by simp)

theorem continuous_densityFourier {μ : Measure ℝ} {f : ℝ → ℂ} (hf : Integrable f μ) :
    Continuous (densityFourier μ f) := by
  apply continuous_of_dominated (bound := fun x ↦ ‖f x‖)
  · intro t
    exact (integrable_realChar_mul hf (-t)).aestronglyMeasurable
  · intro t
    exact Eventually.of_forall (fun x ↦ by simp)
  · exact hf.norm
  · exact Eventually.of_forall fun x ↦
      ((continuous_realChar_frequency x).comp continuous_neg).mul continuous_const

private theorem finiteMeasure_positiveDensity {μ : Measure ℝ} {f : ℝ → ℝ}
    (hf : Integrable f μ) : IsFiniteMeasure (weightedMeasure μ f) := by
  apply isFiniteMeasure_withDensity
  apply ne_top_of_le_ne_top ((hasFiniteIntegral_iff_norm f).1 hf.hasFiniteIntegral).ne
  apply lintegral_mono
  intro x
  exact ENNReal.ofReal_le_ofReal (by simp [Real.norm_eq_abs, le_abs_self])

private theorem real_density_ae_zero_of_transform {μ : Measure ℝ} [IsFiniteMeasure μ]
    {a : ℝ → ℝ} (ha : Integrable a μ) (h : ∀ t, densityFourier μ (fun x ↦ ↑(a x)) t = 0) :
    a =ᵐ[μ] 0 := by
  let μp := weightedMeasure μ a
  let μm := weightedMeasure μ (fun x ↦ -a x)
  let : IsFiniteMeasure μp := finiteMeasure_positiveDensity ha
  let : IsFiniteMeasure μm := finiteMeasure_positiveDensity ha.neg
  have hp (f : ℝ → ℝ) (hf : Integrable f μ) (t : ℝ) :
      ∫ x, realChar t x ∂weightedMeasure μ f =
        ∫ x, realChar t x * (↑(max (f x) 0) : ℂ) ∂μ := by
    unfold weightedMeasure
    rw [integral_withDensity_eq_integral_toReal_smul₀ hf.aemeasurable.ennreal_ofReal
      (Eventually.of_forall fun x ↦ ENNReal.ofReal_lt_top)]
    apply integral_congr_ae
    filter_upwards [] with x
    rw [ENNReal.toReal_ofReal']
    exact mul_comm _ _
  have heq : μp = μm := by
    apply Measure.ext_of_charFun
    funext s
    change charFun (weightedMeasure μ a) s = charFun (weightedMeasure μ (fun x ↦ -a x)) s
    rw [charFun_eq_integral_realChar, charFun_eq_integral_realChar, hp a ha,
      hp (fun x ↦ -a x) ha.neg]
    let t := s / (2 * Real.pi)
    change (∫ x, realChar t x * (↑(max (a x) 0) : ℂ) ∂μ) =
      ∫ x, realChar t x * (↑(max (-a x) 0) : ℂ) ∂μ
    have hpos (f : ℝ → ℝ) (hf : Integrable f μ) :
        Integrable (fun x ↦ max (f x) 0) μ := hf.sup (integrable_zero _ _ _)
    apply sub_eq_zero.mp
    have hposn : Integrable (fun x ↦ max (-a x) 0) μ := hpos (fun x ↦ -a x) ha.neg
    calc
      _ = ∫ x, realChar t x * (↑(max (a x) 0) : ℂ) -
          realChar t x * (↑(max (-a x) 0) : ℂ) ∂μ :=
        (integral_sub (integrable_realChar_mul (hpos a ha).ofReal t)
          (integrable_realChar_mul hposn.ofReal t)).symm
      _ = densityFourier μ (fun x ↦ ↑(a x)) (-t) := by
        unfold densityFourier
        apply integral_congr_ae
        filter_upwards [] with x
        rw [neg_neg, ← mul_sub, ← Complex.ofReal_sub]
        congr 2
        by_cases hx : 0 ≤ a x
        · simp [max_eq_left hx, max_eq_right (neg_nonpos.mpr hx)]
        · have hx' := le_of_lt (lt_of_not_ge hx)
          simp [max_eq_right hx', max_eq_left (neg_nonneg.mpr hx')]
      _ = 0 := h _
  have hd := (withDensity_eq_iff_of_sigmaFinite
    ha.aemeasurable.ennreal_ofReal ha.neg.aemeasurable.ennreal_ofReal).mp heq
  filter_upwards [hd] with x hx
  change ENNReal.ofReal (a x) = ENNReal.ofReal (-a x) at hx
  change a x = 0
  by_cases hax : 0 ≤ a x
  · rw [ENNReal.ofReal_eq_zero.mpr (neg_nonpos.mpr hax), ENNReal.ofReal_eq_zero] at hx
    linarith
  · have hl : a x ≤ 0 := le_of_lt (lt_of_not_ge hax)
    rw [ENNReal.ofReal_eq_zero.mpr hl, eq_comm, ENNReal.ofReal_eq_zero] at hx
    linarith

theorem ae_zero_of_densityFourier_zero {μ : Measure ℝ} [IsFiniteMeasure μ]
    {f : ℝ → ℂ} (hf : Integrable f μ) (h : ∀ t, densityFourier μ f t = 0) :
    f =ᵐ[μ] 0 := by
  have hconj (t : ℝ) : ∫ x, realChar (-t) x * conj (f x) ∂μ = 0 := by
    calc
      _ = ∫ x, conj (realChar t x * f x) ∂μ := by simp only [realChar_neg, map_mul]
      _ = conj (densityFourier μ f (-t)) := by rw [integral_conj, densityFourier, neg_neg]
      _ = 0 := by rw [h, map_zero]
  have hc (t : ℝ) : Integrable (fun x ↦ realChar (-t) x * conj (f x)) μ := by
    apply integrable_realChar_mul ?_ (-t)
    exact (Complex.conjCLE.toContinuousLinearEquiv.toContinuousLinearMap.integrable_comp hf)
  have hre : (fun x ↦ (f x).re) =ᵐ[μ] 0 := by
    apply real_density_ae_zero_of_transform hf.re
    intro t
    unfold densityFourier
    calc
      _ = (2 : ℂ)⁻¹ * ∫ x, realChar (-t) x * f x + realChar (-t) x * conj (f x) ∂μ := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards [] with x
        change realChar (-t) x * (↑(f x).re : ℂ) = _
        rw [← mul_add, Complex.add_conj]
        push_cast
        ring
      _ = 0 := by
        rw [integral_add (integrable_realChar_mul hf _) (hc _), hconj]
        change (2 : ℂ)⁻¹ * (densityFourier μ f t + 0) = 0
        simp [h]
  have him : (fun x ↦ (f x).im) =ᵐ[μ] 0 := by
    apply real_density_ae_zero_of_transform hf.im
    intro t
    unfold densityFourier
    calc
      _ = (2 * I : ℂ)⁻¹ * ∫ x, realChar (-t) x * f x - realChar (-t) x * conj (f x) ∂μ := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards [] with x
        change realChar (-t) x * (↑(f x).im : ℂ) = _
        rw [← mul_sub, Complex.sub_conj]
        have hn : (2 * I : ℂ) ≠ 0 := mul_ne_zero (by norm_num) Complex.I_ne_zero
        field_simp
        push_cast
        ring
      _ = 0 := by
        rw [integral_sub (integrable_realChar_mul hf _) (hc _), hconj]
        change (2 * I : ℂ)⁻¹ * (densityFourier μ f t - 0) = 0
        simp [h]
  filter_upwards [hre, him] with x hr hi
  exact Complex.ext hr hi

theorem inner_realCharLp_eq_densityFourier {μ : Measure ℝ} [IsFiniteMeasure μ] (t : ℝ)
    (f : Lp ℂ 2 μ) :
    ⟪realCharLp μ t, f⟫_ℂ = densityFourier μ f t := by
  rw [L2.inner_def, densityFourier]
  apply integral_congr_ae
  filter_upwards [ae_realCharLp μ t] with x hx
  rw [hx, realChar_neg]
  exact RCLike.inner_apply' _ _

/-- Rational-frequency exponentials are total for any finite Borel measure on the line. -/
theorem dense_span_rat_realCharLp (μ : Measure ℝ) [IsFiniteMeasure μ] :
    Dense (Submodule.span ℂ (Set.range fun q : ℚ ↦ realCharLp μ (q : ℝ)) :
      Set (Lp ℂ 2 μ)) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top, Submodule.topologicalClosure_eq_top_iff]
  apply le_antisymm ?_ bot_le
  intro f hf
  have hin : Integrable f μ := (Lp.memLp f).integrable (by norm_num)
  have hz (q : ℚ) : densityFourier μ f (q : ℝ) = 0 := by
    rw [← inner_realCharLp_eq_densityFourier]
    exact (Submodule.mem_orthogonal _ _).mp hf _ (Submodule.subset_span ⟨q, rfl⟩)
  have hd : DenseRange (fun q : ℚ ↦ (q : ℝ)) := Rat.denseRange_cast
  have hc := continuous_densityFourier hin
  have hs : IsClosed {t : ℝ | densityFourier μ f t = 0} := isClosed_eq hc continuous_const
  have hv (t : ℝ) : densityFourier μ f t = 0 :=
    closure_minimal (by rintro _ ⟨q, rfl⟩; exact hz q) hs (hd t)
  rw [Submodule.mem_bot]
  exact Lp.ext ((ae_zero_of_densityFourier_zero hin hv).trans (Lp.coeFn_zero ℂ 2 μ).symm)

theorem dense_span_realCharLp (μ : Measure ℝ) [IsFiniteMeasure μ] :
    Dense (Submodule.span ℂ (Set.range (realCharLp μ)) : Set (Lp ℂ 2 μ)) := by
  apply (dense_span_rat_realCharLp μ).mono
  exact Submodule.span_mono (by rintro _ ⟨q, rfl⟩; exact ⟨(q : ℝ), rfl⟩)

/-- A real character regarded as a monoid homomorphism on the additive source. -/
noncomputable def realCharHom (t : ℝ) : Multiplicative ℝ →* ℂ where
  toFun x := realChar t x.toAdd
  map_one' := realChar_at_zero t
  map_mul' x y := realChar_add_arg t x.toAdd y.toAdd

theorem injective_realChar : Function.Injective realChar := by
  intro s t h
  by_contra hn
  have hd : s - t ≠ 0 := sub_ne_zero.mpr hn
  let x : ℝ := 1 / (2 * (s - t))
  have hh : realChar (s - t) x = 1 := by
    rw [sub_eq_add_neg, realChar_add, realChar_neg, show realChar s x = realChar t x from congrFun h x]
    simpa using (Complex.mul_conj (realChar t x)).trans (by
      rw [Complex.normSq_eq_norm_sq, norm_realChar]; norm_num)
  have hx : 2 * Real.pi * (s - t) * x = Real.pi := by
    dsimp only [x]
    field_simp
  rw [realChar, hx, Complex.exp_pi_mul_I] at hh
  norm_num at hh

theorem linearIndependent_realChar {ι : Type*} {t : ι → ℝ} (ht : Function.Injective t) :
    LinearIndependent ℂ (fun i ↦ realChar (t i)) := by
  have hh : Function.Injective realCharHom := by
    intro s u he
    apply injective_realChar
    exact funext fun x ↦ DFunLike.congr_fun he (Multiplicative.ofAdd x)
  have hi := (linearIndependent_monoidHom (Multiplicative ℝ) ℂ).comp _ (hh.comp ht)
  exact hi.map' (LinearMap.funLeft ℂ ℂ (Multiplicative.ofAdd : ℝ → Multiplicative ℝ))
    (LinearMap.ker_eq_bot.mpr (fun _ _ h ↦ funext fun x ↦ congrFun h x.toAdd))

theorem analyticAt_realChar (t x : ℝ) : AnalyticAt ℝ (realChar t) x := by
  unfold realChar
  apply (analyticAt_cexp.restrictScalars (𝕜 := ℝ)).comp
  let A := (ContinuousLinearMap.id ℝ ℝ).smulRight ((↑(2 * Real.pi * t) : ℂ) * I)
  apply (A.analyticAt x).congr
  filter_upwards [] with y
  change y • ((↑(2 * Real.pi * t) : ℂ) * I) = _
  simp only [Complex.real_smul, Complex.ofReal_mul]
  ring

theorem linearIndependent_realCharLp {ι : Type*} [Fintype ι] {μ : Measure ℝ}
    [IsFiniteMeasure μ] [NullSingletonClass μ] (hμ : μ ≠ 0)
    {t : ι → ℝ} (ht : Function.Injective t) :
    LinearIndependent ℂ (fun i ↦ realCharLp μ (t i)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc
  let f (x : ℝ) := ∑ i, c i * realChar (t i) x
  have hfae : f =ᵐ[μ] 0 := by
    have hs := Lp.coeFn_fun_finsetSum Finset.univ (fun i ↦ c i • realCharLp μ (t i))
    rw [hc] at hs
    have hp : (fun x ↦ ∑ i, (c i • realCharLp μ (t i)) x) =ᵐ[μ] f := by
      have hsum := eventuallyEq_sum (s := Finset.univ) fun i _ ↦
        (Lp.coeFn_smul (c i) (realCharLp μ (t i))).trans
          ((ae_realCharLp μ (t i)).fun_comp (fun z ↦ c i * z))
      filter_upwards [hsum] with x hx
      simpa only [Finset.sum_apply, Function.comp_apply, f] using hx
    exact hp.symm.trans (hs.symm.trans (Lp.coeFn_zero ℂ 2 μ))
  have ha : AnalyticOnNhd ℝ f Set.univ := by
    intro x _
    exact Finset.analyticAt_fun_sum _ (fun i _ ↦ analyticAt_const.mul (analyticAt_realChar (t i) x))
  have hz : 0 < μ {x | f x = 0} := by
    have hs : MeasurableSet {x | f x = 0} := isClosed_eq
      (continuous_iff_continuousAt.mpr fun x ↦ (ha x (Set.mem_univ x)).continuousAt)
      continuous_const |>.measurableSet
    have hu := (ae_eq_univ_iff_measure_eq hs.nullMeasurableSet).mp
      (eventuallyEqSet_univ.mpr (show ∀ᵐ x ∂μ, x ∈ {x | f x = 0} by exact hfae))
    rw [hu]
    exact pos_iff_ne_zero.mpr (Measure.measure_univ_ne_zero.mpr hμ)
  obtain ⟨x, hx⟩ := exists_accPt_of_nullSingletonClass hz
  have hz' : f = 0 :=
    ha.eq_of_frequently_eq analyticOnNhd_const (accPt_iff_frequently_nhdsNE.mp hx)
  apply Fintype.linearIndependent_iff.mp (linearIndependent_realChar ht) c
  ext y
  simpa [f] using congrFun hz' y

end SchauderBasisOrbits

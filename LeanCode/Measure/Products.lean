import LeanCode.Measure.Weights
import Mathlib.MeasureTheory.Integral.Prod

open Filter MeasureTheory Set
open scoped ENNReal InnerProductSpace ComplexConjugate

namespace SchauderBasisOrbits

/-- A bounded positive weight with constant integral in the auxiliary variable. -/
structure FiberWeight (α : Type*) [MeasurableSpace α]
    {β : Type*} [MeasurableSpace β] (κ : Measure β) where
  weight : α × β → ℝ
  measurable_weight : Measurable weight
  weight_pos : ∀ p, 0 < weight p
  weight_le_one : ∀ p, weight p ≤ 1
  mass : ℝ
  mass_pos : 0 < mass
  fiber_mass : ∀ s, (∫ y, weight (s, y) ∂κ) = mass

namespace FiberWeight

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
variable {κ : Measure β} (W : FiberWeight α κ)

/-- The density after division by the common fiber mass. -/
noncomputable def density (p : α × β) : ℝ := W.weight p / W.mass

theorem measurable_density : Measurable W.density :=
  W.measurable_weight.div_const _

theorem density_pos (p : α × β) : 0 < W.density p :=
  div_pos (W.weight_pos p) W.mass_pos

theorem density_le_inv_mass (p : α × β) : W.density p ≤ W.mass⁻¹ :=
  calc
    _ ≤ 1 / W.mass := div_le_div_of_nonneg_right (W.weight_le_one p) W.mass_pos.le
    _ = _ := one_div _

noncomputable def normalizedMeasure (ρ : Measure α) : Measure (α × β) :=
  weightedMeasure (ρ.prod κ) W.density

theorem integral_density (s : α) : (∫ y, W.density (s, y) ∂κ) = 1 := by
  change (∫ y, W.weight (s, y) / W.mass ∂κ) = 1
  rw [integral_div, W.fiber_mass, div_self W.mass_pos.ne']

theorem lintegral_density [IsFiniteMeasure κ] (s : α) :
    (∫⁻ y, ENNReal.ofReal (W.density (s, y)) ∂κ) = 1 := by
  have hmeas : Measurable (fun y ↦ W.density (s, y)) :=
    W.measurable_density.comp (measurable_prodMk_left)
  have hi : Integrable (fun y ↦ W.density (s, y)) κ :=
    Integrable.of_bound hmeas.aestronglyMeasurable W.mass⁻¹ <| Eventually.of_forall fun y ↦ by
      rw [Real.norm_of_nonneg (W.density_pos (s, y)).le]
      exact W.density_le_inv_mass (s, y)
  rw [← ofReal_integral_eq_lintegral_ofReal hi
    (Eventually.of_forall fun y ↦ (W.density_pos (s, y)).le),
    W.integral_density, ENNReal.ofReal_one]

theorem measurePreserving_fst (ρ : Measure α) [IsFiniteMeasure κ] :
    MeasurePreserving Prod.fst (W.normalizedMeasure ρ) ρ := by
  refine ⟨measurable_fst, ?_⟩
  ext A hA
  rw [Measure.map_apply measurable_fst hA, normalizedMeasure, weightedMeasure,
    withDensity_apply _ (measurable_fst hA), ← lintegral_indicator (measurable_fst hA)]
  rw [lintegral_prod _ ((W.measurable_density.ennreal_ofReal.indicator
    (measurable_fst hA)).aemeasurable)]
  have hslice (s : α) :
      (∫⁻ y, (Prod.fst ⁻¹' A).indicator (fun p ↦ ENNReal.ofReal (W.density p)) (s, y) ∂κ) =
        A.indicator (fun _ ↦ 1) s := by
    by_cases hs : s ∈ A
    · have hm (y : β) : (s, y) ∈ Prod.fst ⁻¹' A := hs
      simp only [indicator_of_mem (hm _), indicator_of_mem hs, W.lintegral_density]
    · have hm (y : β) : (s, y) ∉ Prod.fst ⁻¹' A := hs
      simp only [indicator_of_notMem (hm _), indicator_of_notMem hs, lintegral_zero]
  simp_rw [hslice]
  rw [lintegral_indicator hA, setLIntegral_one]

instance normalizedMeasure_finite (ρ : Measure α) [IsFiniteMeasure κ] [IsFiniteMeasure ρ] :
    IsFiniteMeasure (W.normalizedMeasure ρ) := by
  refine ⟨?_⟩
  have h := congrArg (fun μ : Measure α ↦ μ Set.univ) (W.measurePreserving_fst ρ).map_eq
  rw [Measure.map_apply measurable_fst .univ, preimage_univ] at h
  rw [h]
  exact measure_lt_top ρ _

instance normalizedMeasure_probability (ρ : Measure α) [IsFiniteMeasure κ] [IsProbabilityMeasure ρ] :
    IsProbabilityMeasure (W.normalizedMeasure ρ) := by
  refine ⟨?_⟩
  have h := congrArg (fun μ : Measure α ↦ μ Set.univ) (W.measurePreserving_fst ρ).map_eq
  rw [Measure.map_apply measurable_fst .univ, preimage_univ] at h
  rw [h, measure_univ]

/-- Isometric pullback of the base L² space along the first projection. -/
noncomputable def pullback (ρ : Measure α) [IsFiniteMeasure κ] :
    Lp ℂ 2 ρ →ₗᵢ[ℂ] Lp ℂ 2 (W.normalizedMeasure ρ) :=
  Lp.compMeasurePreservingₗᵢ ℂ Prod.fst (W.measurePreserving_fst ρ)

theorem ae_pullback (ρ : Measure α) [IsFiniteMeasure κ] (f : Lp ℂ 2 ρ) :
    ⇑(W.pullback ρ f) =ᵐ[W.normalizedMeasure ρ] fun p ↦ f p.1 :=
  Lp.coeFn_compMeasurePreserving f (W.measurePreserving_fst ρ)

/-- Fiber average with the probability density in that fiber. -/
noncomputable def mean (u : α × β → ℂ) (s : α) : ℂ :=
  ∫ y, W.density (s, y) • u (s, y) ∂κ

/-- Subtract the fiber mean pointwise, retaining the raw representative. -/
noncomputable def center (u : α × β → ℂ) (p : α × β) : ℂ :=
  u p - W.mean u p.1

theorem measurable_mean [IsFiniteMeasure κ] {u : α × β → ℂ} (hu : Measurable u) :
    Measurable (W.mean u) :=
  (W.measurable_density.smul hu).stronglyMeasurable.integral_prod_right'.measurable

theorem measurable_center [IsFiniteMeasure κ] {u : α × β → ℂ} (hu : Measurable u) :
    Measurable (W.center u) := hu.sub ((W.measurable_mean hu).comp measurable_fst)

private theorem integrable_fiber_weighted [IsFiniteMeasure κ] {u : α × β → ℂ}
    (hu : Measurable u) {B : ℝ} (hB : ∀ p, ‖u p‖ ≤ B) (s : α) :
    Integrable (fun y ↦ W.density (s, y) • u (s, y)) κ := by
  refine Integrable.of_bound (((W.measurable_density.smul hu).comp
    measurable_prodMk_left).aestronglyMeasurable) (W.mass⁻¹ * B) ?_
  filter_upwards [] with y
  rw [norm_smul, Real.norm_of_nonneg (W.density_pos (s, y)).le]
  exact mul_le_mul (W.density_le_inv_mass (s, y)) (hB (s, y)) (norm_nonneg _)
    (inv_nonneg.mpr W.mass_pos.le)

theorem norm_mean_le [IsFiniteMeasure κ] {u : α × β → ℂ} (hu : Measurable u) {B : ℝ}
    (hB : ∀ p, ‖u p‖ ≤ B) (s : α) :
    ‖W.mean u s‖ ≤ B := by
  calc
    _ ≤ ∫ y, ‖W.density (s, y) • u (s, y)‖ ∂κ := norm_integral_le_integral_norm _
    _ ≤ ∫ y, W.density (s, y) * B ∂κ := by
      apply integral_mono (W.integrable_fiber_weighted hu hB s).norm
      · have hd : Integrable (fun y ↦ W.density (s, y)) κ :=
          Integrable.of_bound (W.measurable_density.comp measurable_prodMk_left).aestronglyMeasurable
            W.mass⁻¹ (Eventually.of_forall fun y ↦ by
              rw [Real.norm_of_nonneg (W.density_pos (s, y)).le]
              exact W.density_le_inv_mass (s, y))
        exact hd.mul_const B
      · intro y
        change ‖W.density (s, y) • u (s, y)‖ ≤ W.density (s, y) * B
        rw [norm_smul, Real.norm_of_nonneg (W.density_pos (s, y)).le]
        exact mul_le_mul_of_nonneg_left (hB (s, y)) (W.density_pos (s, y)).le
    _ = B := by rw [integral_mul_const, W.integral_density, one_mul]

theorem norm_center_le [IsFiniteMeasure κ] {u : α × β → ℂ} (hu : Measurable u)
    {B : ℝ} (hB : ∀ p, ‖u p‖ ≤ B) (p : α × β) :
    ‖W.center u p‖ ≤ 2 * B := by
  exact (norm_sub_le _ _).trans (by linarith [hB p, W.norm_mean_le hu hB p.1])

theorem mean_center_eq_zero [IsFiniteMeasure κ] {u : α × β → ℂ} (hu : Measurable u)
    {B : ℝ} (hB : ∀ p, ‖u p‖ ≤ B) (s : α) :
    W.mean (W.center u) s = 0 := by
  have hi := W.integrable_fiber_weighted hu hB s
  have hc : Integrable (fun y ↦ W.density (s, y) • W.mean u s) κ :=
    W.integrable_fiber_weighted (u := fun _ ↦ W.mean u s) measurable_const (fun _ ↦ le_rfl) s
  change (∫ y, W.density (s, y) • (u (s, y) - W.mean u s) ∂κ) = 0
  simp_rw [smul_sub]
  rw [integral_sub hi hc, integral_smul_const, W.integral_density, one_smul]
  exact sub_self _

theorem integral_normalizedMeasure (ρ : Measure α) {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : α × β → E) :
    (∫ p, f p ∂W.normalizedMeasure ρ) = ∫ p, W.density p • f p ∂(ρ.prod κ) :=
  integral_weightedMeasure _ W.measurable_density (Eventually.of_forall fun p ↦
    (W.density_pos p).le) f

private theorem integrable_density_mul_pairing (ρ : Measure α) [IsFiniteMeasure ρ]
    [IsFiniteMeasure κ] (f : Lp ℂ 2 ρ) {u : α × β → ℂ} (hu : Measurable u)
    {B : ℝ} (hB : ∀ p, ‖u p‖ ≤ B) :
    Integrable (fun p ↦ W.density p • (conj (f p.1) * u p)) (ρ.prod κ) := by
  have hf := (Lp.memLp f).integrable (by norm_num : 1 ≤ (2 : ℝ≥0∞))
  have hm := Complex.continuous_conj.comp_aestronglyMeasurable
    ((Lp.aestronglyMeasurable f).comp_fst (ν := κ))
  apply ((hf.norm.const_mul (W.mass⁻¹ * B)).comp_fst κ).mono'
    (W.measurable_density.aestronglyMeasurable.smul (hm.mul hu.aestronglyMeasurable))
  filter_upwards [] with p
  change ‖W.density p • (conj (f p.1) * u p)‖ ≤ W.mass⁻¹ * B * ‖f p.1‖
  rw [norm_smul, Real.norm_of_nonneg (W.density_pos p).le, norm_mul, Complex.norm_conj]
  calc
    _ ≤ W.mass⁻¹ * (‖f p.1‖ * ‖u p‖) :=
      mul_le_mul_of_nonneg_right (W.density_le_inv_mass p) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = (W.mass⁻¹ * ‖u p‖) * ‖f p.1‖ := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hB p) (inv_nonneg.mpr W.mass_pos.le)) (norm_nonneg _)

/-- Pairing a vector pulled back from the base tests only the fiber average. -/
theorem inner_pullback_lift₂ (ρ : Measure α) [IsFiniteMeasure ρ] [IsFiniteMeasure κ]
    (f : Lp ℂ 2 ρ) {u : α × β → ℂ} (hu : Measurable u) {B : ℝ}
    (hB : ∀ p, ‖u p‖ ≤ B) :
    ⟪W.pullback ρ f, lift₂ (W.normalizedMeasure ρ) u hu B hB⟫_ℂ =
      ⟪f, lift₂ ρ (W.mean u) (W.measurable_mean hu) B (W.norm_mean_le hu hB)⟫_ℂ := by
  rw [L2.inner_def, L2.inner_def]
  calc
    _ = ∫ p, conj (f p.1) * u p ∂W.normalizedMeasure ρ := by
      apply integral_congr_ae
      filter_upwards [W.ae_pullback ρ f, ae_lift₂ (W.normalizedMeasure ρ) u hu B hB] with p hp hq
      rw [hp, hq, RCLike.inner_apply']
    _ = ∫ s, conj (f s) * W.mean u s ∂ρ := by
      rw [W.integral_normalizedMeasure, integral_prod _ (W.integrable_density_mul_pairing ρ f hu hB)]
      apply integral_congr_ae
      filter_upwards [] with s
      rw [mean, ← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with y
      simp only [Complex.real_smul]
      ring
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [ae_lift₂ ρ (W.mean u) (W.measurable_mean hu) B (W.norm_mean_le hu hB)] with s hs
      rw [hs, RCLike.inner_apply']

theorem inner_pullback_center_eq_zero (ρ : Measure α) [IsFiniteMeasure ρ] [IsFiniteMeasure κ]
    (f : Lp ℂ 2 ρ) {u : α × β → ℂ} (hu : Measurable u) {B : ℝ} (hB : ∀ p, ‖u p‖ ≤ B) :
    ⟪W.pullback ρ f, lift₂ (W.normalizedMeasure ρ) (W.center u) (W.measurable_center hu)
      (2 * B) (W.norm_center_le hu hB)⟫_ℂ = 0 := by
  rw [inner_pullback_lift₂]
  suffices he : lift₂ ρ (W.mean (W.center u)) (W.measurable_mean (W.measurable_center hu))
      (2 * B) (W.norm_mean_le (W.measurable_center hu) (W.norm_center_le hu hB)) = 0 by
    rw [he, inner_zero_right]
  apply Lp.ext
  have hzero : W.mean (W.center u) =ᵐ[ρ] (0 : α → ℂ) :=
    Eventually.of_forall (W.mean_center_eq_zero hu hB)
  exact (ae_lift₂ _ _ _ _ _).trans
    (hzero.trans (Lp.coeFn_zero ℂ 2 ρ).symm)

theorem map_weightedMeasure_pullback {S T : Type*} [MeasurableSpace S] [MeasurableSpace T]
    {μ : Measure S} {ν : Measure T} {e : S → T} (he : MeasurePreserving e μ ν)
    {w : T → ℝ} (hw : Measurable w) :
    Measure.map e (weightedMeasure μ (w ∘ e)) = weightedMeasure ν w := by
  ext A hA
  rw [Measure.map_apply he.measurable hA, weightedMeasure, weightedMeasure,
    withDensity_apply _ hA, withDensity_apply _ (he.measurable hA)]
  have h := lintegral_map (μ := μ.restrict (e ⁻¹' A)) hw.ennreal_ofReal he.measurable
  rw [← Measure.restrict_map he.measurable hA, he.map_eq] at h
  exact h.symm

variable {γ δ : Type*} [MeasurableSpace γ] [MeasurableSpace δ]
variable {ν : Measure γ} {η : Measure δ}

/-- Substitute a measurable function in the base coordinate. -/
def pullBase (V : FiberWeight δ ν) (e : α → δ) (he : Measurable e) : FiberWeight α ν where
  weight p := V.weight (e p.1, p.2)
  measurable_weight := V.measurable_weight.comp ((he.comp measurable_fst).prodMk measurable_snd)
  weight_pos p := V.weight_pos _
  weight_le_one p := V.weight_le_one _
  mass := V.mass
  mass_pos := V.mass_pos
  fiber_mass s := V.fiber_mass (e s)

/-- Reindex the fiber using a measure-preserving measurable equivalence. -/
def pullFiber (e : γ ≃ᵐ β) (he : MeasurePreserving e ν κ) : FiberWeight α ν where
  weight p := W.weight (p.1, e p.2)
  measurable_weight := W.measurable_weight.comp (measurable_fst.prodMk (he.measurable.comp measurable_snd))
  weight_pos p := W.weight_pos _
  weight_le_one p := W.weight_le_one _
  mass := W.mass
  mass_pos := W.mass_pos
  fiber_mass s := (he.integral_comp e.measurableEmbedding (fun y ↦ W.weight (s, y))).trans (W.fiber_mass s)

set_option maxHeartbeats 900000 in
theorem measurePreserving_pullFiber (ρ : Measure α) [IsFiniteMeasure ν]
    (e : γ ≃ᵐ β) (he : MeasurePreserving e ν κ) :
    MeasurePreserving (MeasurableEquiv.prodCongr (MeasurableEquiv.refl α) e)
      ((W.pullFiber e he).normalizedMeasure ρ) (W.normalizedMeasure ρ) := by
  let f := MeasurableEquiv.prodCongr (MeasurableEquiv.refl α) e
  have hf : MeasurePreserving f (ρ.prod ν) (ρ.prod κ) := by
    refine ⟨f.measurable, ?_⟩
    change Measure.map (Prod.map id e) (ρ.prod ν) = ρ.prod κ
    rw [← Measure.map_prod_map ρ ν measurable_id he.measurable, Measure.map_id, he.map_eq]
  refine ⟨f.measurable, ?_⟩
  change Measure.map f (weightedMeasure (ρ.prod ν) (W.density ∘ f)) =
    weightedMeasure (ρ.prod κ) W.density
  exact map_weightedMeasure_pullback hf W.measurable_density

theorem mean_pullFiber (e : γ ≃ᵐ β) (he : MeasurePreserving e ν κ)
    (u : α × β → ℂ) (s : α) :
    (W.pullFiber e he).mean (fun p ↦ u (p.1, e p.2)) s = W.mean u s :=
  he.integral_comp e.measurableEmbedding (fun y ↦ W.density (s, y) • u (s, y))

/-- Flatten an extra constant-marginal weight over a previously weighted product. -/
noncomputable def nested (V : FiberWeight (α × β) ν)
    [IsFiniteMeasure κ] [IsFiniteMeasure ν] : FiberWeight α (κ.prod ν) where
  weight p := W.weight (p.1, p.2.1) * V.weight ((p.1, p.2.1), p.2.2)
  measurable_weight := (W.measurable_weight.comp
    (measurable_fst.prodMk (measurable_fst.comp measurable_snd))).mul
    (V.measurable_weight.comp MeasurableEquiv.prodAssoc.symm.measurable)
  weight_pos _ := mul_pos (W.weight_pos _) (V.weight_pos _)
  weight_le_one _ := (mul_le_mul_of_nonneg_right (W.weight_le_one _) (V.weight_pos _).le).trans
    (by simpa using V.weight_le_one _)
  mass := W.mass * V.mass
  mass_pos := mul_pos W.mass_pos V.mass_pos
  fiber_mass s := by
    let f : β × γ → ℝ := fun p ↦ W.weight (s, p.1) * V.weight ((s, p.1), p.2)
    have hm : Measurable f :=
      (W.measurable_weight.comp (measurable_const.prodMk measurable_fst)).mul
      (V.measurable_weight.comp ((measurable_const.prodMk measurable_fst).prodMk measurable_snd))
    have hi : Integrable f (κ.prod ν) := by
      refine Integrable.of_bound hm.aestronglyMeasurable 1 (Eventually.of_forall fun p ↦ ?_)
      change ‖W.weight (s, p.1) * V.weight ((s, p.1), p.2)‖ ≤ 1
      rw [Real.norm_of_nonneg (mul_nonneg (W.weight_pos _).le (V.weight_pos _).le)]
      exact (mul_le_mul_of_nonneg_right (W.weight_le_one _) (V.weight_pos _).le).trans
        (by simpa using V.weight_le_one ((s, p.1), p.2))
    change (∫ p, f p ∂κ.prod ν) = _
    rw [integral_prod _ hi]
    simp_rw [f, integral_const_mul, V.fiber_mass, integral_mul_const, W.fiber_mass]

theorem density_nested (V : FiberWeight (α × β) ν)
    [IsFiniteMeasure κ] [IsFiniteMeasure ν] (p : α × (β × γ)) :
    (W.nested V).density p = W.density (p.1, p.2.1) * V.density ((p.1, p.2.1), p.2.2) := by
  exact (div_mul_div_comm _ _ _ _).symm

theorem measurePreserving_nested (ρ : Measure α) (V : FiberWeight (α × β) ν)
    [IsFiniteMeasure κ] [IsFiniteMeasure ν] :
    MeasurePreserving MeasurableEquiv.prodAssoc (V.normalizedMeasure (W.normalizedMeasure ρ))
      ((W.nested V).normalizedMeasure ρ) := by
  refine ⟨MeasurableEquiv.prodAssoc.measurable, ?_⟩
  have he := measurePreserving_prodAssoc ρ κ ν
  have hp := map_weightedMeasure_pullback he (W.nested V).measurable_density
  have hm : Measurable (fun p : (α × β) × γ ↦ ENNReal.ofReal (W.density p.1)) :=
    W.measurable_density.ennreal_ofReal.comp measurable_fst
  have hEq : V.normalizedMeasure (W.normalizedMeasure ρ) =
      weightedMeasure ((ρ.prod κ).prod ν) ((W.nested V).density ∘ MeasurableEquiv.prodAssoc) := by
    rw [normalizedMeasure, normalizedMeasure, weightedMeasure, weightedMeasure,
      prod_withDensity_left W.measurable_density.ennreal_ofReal, ← withDensity_mul _ hm
        V.measurable_density.ennreal_ofReal, weightedMeasure]
    apply congrArg ((ρ.prod κ).prod ν).withDensity
    funext p
    simp only [Function.comp_apply, Pi.mul_apply, density_nested]
    exact (ENNReal.ofReal_mul (W.density_pos p.1).le).symm
  rw [hEq]
  exact hp

/-- Combine two fiber weights on disjoint groups of auxiliary coordinates. -/
noncomputable def prod (V : FiberWeight α ν) [IsFiniteMeasure κ] [IsFiniteMeasure ν] :
    FiberWeight α (κ.prod ν) := W.nested (V.pullBase Prod.fst measurable_fst)

theorem density_prod (V : FiberWeight α ν) [IsFiniteMeasure κ] [IsFiniteMeasure ν]
    (p : α × (β × γ)) :
    (W.prod V).density p = W.density (p.1, p.2.1) * V.density (p.1, p.2.2) :=
  W.density_nested (V.pullBase Prod.fst measurable_fst) p

theorem measurePreserving_prod_left (ρ : Measure α) (V : FiberWeight α ν)
    [IsFiniteMeasure κ] [IsFiniteMeasure ν] :
    MeasurePreserving (fun p : α × (β × γ) ↦ (p.1, p.2.1))
      ((W.prod V).normalizedMeasure ρ) (W.normalizedMeasure ρ) :=
  ((V.pullBase Prod.fst measurable_fst).measurePreserving_fst (W.normalizedMeasure ρ)).comp
    ((W.measurePreserving_nested ρ (V.pullBase Prod.fst measurable_fst)).symm
      MeasurableEquiv.prodAssoc)

theorem mass_le_one [IsProbabilityMeasure κ] (s : α) : W.mass ≤ 1 := by
  rw [← W.fiber_mass s]
  have hm := W.measurable_weight.comp (measurable_prodMk_left (x := s))
  have hi : Integrable (fun y ↦ W.weight (s, y)) κ :=
    Integrable.of_bound hm.aestronglyMeasurable 1 <|
      Eventually.of_forall fun y ↦ by
        rw [Real.norm_of_nonneg (W.weight_pos (s, y)).le]
        exact W.weight_le_one (s, y)
  calc
    _ ≤ ∫ y : β, (1 : ℝ) ∂κ := integral_mono hi (integrable_const _) fun y ↦ W.weight_le_one (s, y)
    _ = 1 := by simp

theorem prod_mass_loss_le (V : FiberWeight α ν) [IsProbabilityMeasure κ] [IsProbabilityMeasure ν]
    (s : α) : 1 - (W.prod V).mass ≤ (1 - W.mass) + (1 - V.mass) := by
  change 1 - W.mass * V.mass ≤ _
  nlinarith [mul_nonneg (sub_nonneg.mpr (W.mass_le_one s)) (sub_nonneg.mpr (V.mass_le_one s))]

/-- The probability measure in a single fiber after normalization. -/
noncomputable def fiberMeasure (s : α) : Measure β :=
  weightedMeasure κ (fun y ↦ W.density (s, y))

instance fiberMeasure_probability [IsFiniteMeasure κ] (s : α) :
    IsProbabilityMeasure (W.fiberMeasure s) where
  measure_univ := by
    rw [fiberMeasure, weightedMeasure, withDensity_apply _ .univ, Measure.restrict_univ]
    exact W.lintegral_density s

theorem mean_eq_integral_fiberMeasure (u : α × β → ℂ) (s : α) :
    W.mean u s = ∫ y, u (s, y) ∂W.fiberMeasure s :=
  (integral_weightedMeasure _ (W.measurable_density.comp measurable_prodMk_left)
    (Eventually.of_forall fun y ↦ (W.density_pos (s, y)).le) (fun y ↦ u (s, y))).symm

theorem fiberMeasure_prod (V : FiberWeight α ν) [IsFiniteMeasure κ] [IsFiniteMeasure ν] (s : α) :
    (W.prod V).fiberMeasure s = (W.fiberMeasure s).prod (V.fiberMeasure s) := by
  unfold fiberMeasure weightedMeasure
  have h₁ : Measurable (fun y ↦ ENNReal.ofReal (W.density (s, y))) :=
    W.measurable_density.ennreal_ofReal.comp measurable_prodMk_left
  have h₂ : Measurable (fun z ↦ ENNReal.ofReal (V.density (s, z))) :=
    V.measurable_density.ennreal_ofReal.comp measurable_prodMk_left
  rw [prod_withDensity h₁ h₂]
  apply congrArg (κ.prod ν).withDensity
  funext p
  change ENNReal.ofReal ((W.prod V).density (s, p)) = _
  rw [density_prod, ENNReal.ofReal_mul (W.density_pos _).le]

theorem mean_prod_separated (V : FiberWeight α ν) [IsFiniteMeasure κ] [IsFiniteMeasure ν]
    (u : α × β → ℂ) (v : α × γ → ℂ) (s : α) :
    (W.prod V).mean (fun p ↦ u (p.1, p.2.1) * v (p.1, p.2.2)) s =
      W.mean u s * V.mean v s := by
  rw [mean_eq_integral_fiberMeasure, fiberMeasure_prod, W.mean_eq_integral_fiberMeasure,
    V.mean_eq_integral_fiberMeasure]
  exact integral_prod_mul (fun y ↦ u (s, y)) (fun z ↦ v (s, z))

theorem mean_prod_left (V : FiberWeight α ν) [IsFiniteMeasure κ] [IsFiniteMeasure ν]
    (u : α × β → ℂ) (s : α) :
    (W.prod V).mean (fun p ↦ u (p.1, p.2.1)) s = W.mean u s := by
  rw [mean_eq_integral_fiberMeasure, fiberMeasure_prod, W.mean_eq_integral_fiberMeasure]
  simpa only [probReal_univ, one_smul] using
    (integral_fun_fst (μ := W.fiberMeasure s) (ν := V.fiberMeasure s) (fun y ↦ u (s, y)))

theorem mean_prod_right (V : FiberWeight α ν) [IsFiniteMeasure κ] [IsFiniteMeasure ν]
    (v : α × γ → ℂ) (s : α) :
    (W.prod V).mean (fun p ↦ v (p.1, p.2.2)) s = V.mean v s := by
  rw [mean_eq_integral_fiberMeasure, fiberMeasure_prod, V.mean_eq_integral_fiberMeasure]
  simpa only [probReal_univ, one_smul] using
    (integral_fun_snd (μ := W.fiberMeasure s) (ν := V.fiberMeasure s) (fun z ↦ v (s, z)))

theorem mean_conj (u : α × β → ℂ) (s : α) :
    W.mean (fun p ↦ conj (u p)) s = conj (W.mean u s) := by
  simp only [mean_eq_integral_fiberMeasure, integral_conj]

theorem integral_normalizedMeasure_eq_mean (ρ : Measure α) [IsFiniteMeasure ρ] [IsFiniteMeasure κ]
    {u : α × β → ℂ} (hu : Measurable u) {B : ℝ} (hB : ∀ p, ‖u p‖ ≤ B) :
    (∫ p, u p ∂W.normalizedMeasure ρ) = ∫ s, W.mean u s ∂ρ := by
  rw [W.integral_normalizedMeasure]
  have hi : Integrable (fun p ↦ W.density p • u p) (ρ.prod κ) := by
    refine Integrable.of_bound (W.measurable_density.smul hu).aestronglyMeasurable (W.mass⁻¹ * B)
      (Eventually.of_forall fun p ↦ ?_)
    rw [norm_smul, Real.norm_of_nonneg (W.density_pos p).le]
    exact mul_le_mul (W.density_le_inv_mass p) (hB p) (norm_nonneg _) (inv_nonneg.mpr W.mass_pos.le)
  exact integral_prod _ hi

theorem integral_cross_center_prod_eq_zero (ρ : Measure α) [IsFiniteMeasure ρ]
    (V : FiberWeight α ν) [IsFiniteMeasure κ] [IsFiniteMeasure ν]
    {u : α × β → ℂ} {v : α × γ → ℂ} (hu : Measurable u) (hv : Measurable v)
    {B D : ℝ} (hB : ∀ p, ‖u p‖ ≤ B) (hD : ∀ p, ‖v p‖ ≤ D) :
    ∫ p, conj (W.center u (p.1, p.2.1)) * V.center v (p.1, p.2.2) ∂(W.prod V).normalizedMeasure ρ =
      0 := by
  have hm : Measurable
      (fun p : α × (β × γ) ↦ conj (W.center u (p.1, p.2.1)) * V.center v (p.1, p.2.2)) :=
    (Complex.continuous_conj.measurable.comp ((W.measurable_center hu).comp
      (measurable_fst.prodMk (measurable_fst.comp measurable_snd)))).mul
      ((V.measurable_center hv).comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd)))
  rw [(W.prod V).integral_normalizedMeasure_eq_mean ρ hm (B := (2 * B) * (2 * D))]
  · calc
      _ = ∫ _ : α, (0 : ℂ) ∂ρ := by
        apply integral_congr_ae
        filter_upwards [] with s
        rw [W.mean_prod_separated V (fun p ↦ conj (W.center u p)) (V.center v),
          V.mean_center_eq_zero hv hD, mul_zero]
      _ = 0 := integral_zero α ℂ
  · intro p
    rw [norm_mul, Complex.norm_conj]
    have hB' := W.norm_center_le hu hB (p.1, p.2.1)
    have hD' := V.norm_center_le hv hD (p.1, p.2.2)
    exact mul_le_mul hB' hD' (norm_nonneg _) ((norm_nonneg _).trans hB')

end FiberWeight

end SchauderBasisOrbits

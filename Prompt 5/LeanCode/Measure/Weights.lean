module

public import LeanCode.Fourier.Characters
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Measure.WithDensity

@[expose] public section

open Filter MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate

namespace SchauderBasisOrbits

variable {α : Type*} [MeasurableSpace α]

/-- Multiply a measure by a nonnegative real density, using its positive part. -/
noncomputable def weightedMeasure (μ : Measure α) (w : α → ℝ) : Measure α :=
  μ.withDensity (fun x => ENNReal.ofReal (w x))

/-- Lift a bounded measurable representative under a finite measure into L². -/
noncomputable def lift₂ (μ : Measure α) [IsFiniteMeasure μ]
    (f : α → ℂ) (hf : Measurable f) (B : ℝ) (hB : ∀ x, ‖f x‖ ≤ B) :
    Lp ℂ 2 μ :=
  (MemLp.of_bound hf.aestronglyMeasurable B (Filter.Eventually.of_forall hB)).toLp f

theorem ae_lift₂ (μ : Measure α) [IsFiniteMeasure μ]
    (f : α → ℂ) (hf : Measurable f) (B : ℝ) (hB : ∀ x, ‖f x‖ ≤ B) :
    ⇑(lift₂ μ f hf B hB) =ᵐ[μ] f :=
  MemLp.coeFn_toLp _

/-- The L² class represented by the real character of frequency `t`. -/
noncomputable def realCharLp (μ : Measure ℝ) [IsFiniteMeasure μ] (t : ℝ) : Lp ℂ 2 μ :=
  lift₂ μ (realChar t) (continuous_realChar t).measurable 1 (fun x => (norm_realChar t x).le)

theorem ae_realCharLp (μ : Measure ℝ) [IsFiniteMeasure μ] (t : ℝ) :
    ⇑(realCharLp μ t) =ᵐ[μ] realChar t :=
  ae_lift₂ μ _ _ _ _

/-- Bounded densities preserve finiteness of the reference measure. -/
theorem finite_weightedMeasure (μ : Measure α) [IsFiniteMeasure μ] {w : α → ℝ}
    (h₁ : ∀ᵐ x ∂μ, w x ≤ 1) : IsFiniteMeasure (weightedMeasure μ w) := by
  refine ⟨?_⟩
  rw [weightedMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  apply lt_of_le_of_lt (lintegral_mono_ae (g := fun _ => 1) ?_) _
  · filter_upwards [h₁] with x hx
    simpa using ENNReal.ofReal_le_ofReal hx
  · simpa using measure_lt_top μ Set.univ

/-- A positive measurable density preserves the almost-everywhere filter. -/
theorem ae_weightedMeasure (μ : Measure α) {w : α → ℝ} (hw : Measurable w)
    (hpos : ∀ᵐ x ∂μ, 0 < w x) : ae (weightedMeasure μ w) = ae μ := by
  ext s
  change (∀ᵐ x ∂weightedMeasure μ w, x ∈ s) ↔ ∀ᵐ x ∂μ, x ∈ s
  rw [weightedMeasure, ae_withDensity_iff hw.ennreal_ofReal]
  constructor
  · intro h
    filter_upwards [h, hpos] with x hx hp
    exact hx (ne_of_gt (ENNReal.ofReal_pos.mpr hp))
  · exact fun h => h.mono fun _ hx _ => hx

/-- Integration against the density as an ordinary real scalar multiplication. -/
theorem integral_weightedMeasure (μ : Measure α) {w : α → ℝ} (hw : Measurable w)
    (hn : ∀ᵐ x ∂μ, 0 ≤ w x) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : α → E) :
    ∫ x, f x ∂weightedMeasure μ w = ∫ x, w x • f x ∂μ := by
  rw [weightedMeasure, integral_withDensity_eq_integral_toReal_smul hw.ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) f]
  apply integral_congr_ae
  filter_upwards [hn] with x hx
  rw [ENNReal.toReal_ofReal hx]

theorem inner_lift₂ (μ : Measure α) [IsFiniteMeasure μ] {f g : α → ℂ}
    (hf : Measurable f) (hg : Measurable g) {Bf Bg : ℝ}
    (hBf : ∀ x, ‖f x‖ ≤ Bf) (hBg : ∀ x, ‖g x‖ ≤ Bg) :
    ⟪lift₂ μ f hf Bf hBf, lift₂ μ g hg Bg hBg⟫_ℂ = ∫ x, conj (f x) * g x ∂μ := by
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [ae_lift₂ μ f hf Bf hBf, ae_lift₂ μ g hg Bg hBg] with x hx hy
  simp [hx, hy, Complex.inner, mul_comm]

theorem inner_realCharLp (μ : Measure ℝ) [IsFiniteMeasure μ] (s t : ℝ) :
    ⟪realCharLp μ s, realCharLp μ t⟫_ℂ = ∫ x, realChar (t - s) x ∂μ := by
  rw [realCharLp, realCharLp, inner_lift₂]
  congr with x
  rw [← realChar_neg, ← realChar_add, neg_add_eq_sub]

theorem norm_sq_L2_integral (μ : Measure α) (f : Lp ℂ 2 μ) :
    ‖f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂μ := by
  calc
    ‖f‖ ^ 2 = RCLike.re ⟪f, f⟫_ℂ := (inner_self_eq_norm_sq f).symm
    _ = ∫ x, RCLike.re ⟪f x, f x⟫_ℂ ∂μ := by
      rw [L2.inner_def, integral_re (L2.integrable_inner (𝕜 := ℂ) f f)]
    _ = _ := integral_congr_ae (Eventually.of_forall fun x => inner_self_eq_norm_sq (f x))

end SchauderBasisOrbits

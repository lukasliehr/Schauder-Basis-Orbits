module

public import LeanCode.Measure.Weights
public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.Tactic

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace

namespace SchauderBasisOrbits

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {w : α → ℝ}

/-- Scaling a complex representative by the square root of a positive density
moves it from the weighted L² space to the original L² space. -/
theorem memLp_sqrt_weighted_iff (hw : Measurable w) (hp : ∀ᵐ x ∂μ, 0 < w x)
    {f : α → ℂ} (hf : AEStronglyMeasurable f μ) :
    MemLp (fun x => Real.sqrt (w x) • f x) 2 μ ↔ MemLp f 2 (weightedMeasure μ w) := by
  have hf' : AEStronglyMeasurable f (weightedMeasure μ w) := by
    obtain ⟨g, hg, hfg⟩ := hf
    exact ⟨g, hg, by rw [EventuallyEq, ae_weightedMeasure μ hw hp]; exact hfg⟩
  have hs : AEStronglyMeasurable (fun x => Real.sqrt (w x) • f x) μ :=
    (hw.sqrt.aestronglyMeasurable).smul hf
  rw [memLp_two_iff_integrable_sq_norm hs, memLp_two_iff_integrable_sq_norm hf', weightedMeasure,
    integrable_withDensity_iff hw.ennreal_ofReal (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  apply integrable_congr
  filter_upwards [hp] with x hx
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow,
    Real.sq_sqrt hx.le, ENNReal.toReal_ofReal hx.le, mul_comm]

theorem weighted_mem_sqrt (hw : Measurable w) (hp : ∀ᵐ x ∂μ, 0 < w x)
    (f : Lp ℂ 2 (weightedMeasure μ w)) :
    MemLp (fun x => Real.sqrt (w x) • f x) 2 μ := by
  have hf : AEStronglyMeasurable (⇑f) μ := by
    obtain ⟨g, hg, hfg⟩ := Lp.aestronglyMeasurable f
    exact ⟨g, hg, by rw [EventuallyEq, ← ae_weightedMeasure μ hw hp]; exact hfg⟩
  exact (memLp_sqrt_weighted_iff hw hp hf).mpr (Lp.memLp f)

noncomputable def weightedToBaseFun (hw : Measurable w) (hp : ∀ᵐ x ∂μ, 0 < w x)
    (f : Lp ℂ 2 (weightedMeasure μ w)) : Lp ℂ 2 μ :=
  (weighted_mem_sqrt hw hp f).toLp _

private theorem ae_weightedToBaseFun (hw : Measurable w) (hp : ∀ᵐ x ∂μ, 0 < w x)
    (f : Lp ℂ 2 (weightedMeasure μ w)) :
    ⇑(weightedToBaseFun hw hp f) =ᵐ[μ] fun x => Real.sqrt (w x) • f x :=
  MemLp.coeFn_toLp _

private theorem eventually_of_weighted (hw : Measurable w) (hp : ∀ᵐ x ∂μ, 0 < w x)
    {p : α → Prop} (h : ∀ᵐ x ∂weightedMeasure μ w, p x) : ∀ᵐ x ∂μ, p x := by
  rwa [ae_weightedMeasure μ hw hp] at h

noncomputable def weightedToBaseLinear (hw : Measurable w) (hp : ∀ᵐ x ∂μ, 0 < w x) :
    Lp ℂ 2 (weightedMeasure μ w) →ₗ[ℂ] Lp ℂ 2 μ where
  toFun := weightedToBaseFun hw hp
  map_add' f g := by
    apply Lp.ext
    filter_upwards [ae_weightedToBaseFun hw hp (f + g),
      ae_weightedToBaseFun hw hp f, ae_weightedToBaseFun hw hp g,
      eventually_of_weighted hw hp (Lp.coeFn_add f g),
      Lp.coeFn_add (weightedToBaseFun hw hp f) (weightedToBaseFun hw hp g)]
      with x h₁ h₂ h₃ h₄ h₅
    rw [h₁, h₄, h₅]
    change Real.sqrt (w x) • (f x + g x) = weightedToBaseFun hw hp f x + weightedToBaseFun hw hp g x
    rw [h₂, h₃, smul_add]
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [ae_weightedToBaseFun hw hp (c • f), ae_weightedToBaseFun hw hp f,
      eventually_of_weighted hw hp (Lp.coeFn_smul c f),
      Lp.coeFn_smul c (weightedToBaseFun hw hp f)] with x h₁ h₂ h₃ h₄
    change weightedToBaseFun hw hp (c • f) x = ((c • weightedToBaseFun hw hp f)) x
    rw [h₁, h₃, h₄]
    change Real.sqrt (w x) • (c • f x) = c • weightedToBaseFun hw hp f x
    rw [h₂, smul_comm]

theorem weightedToBase_inner (hw : Measurable w) (hp : ∀ᵐ x ∂μ, 0 < w x)
    (f g : Lp ℂ 2 (weightedMeasure μ w)) :
    ⟪weightedToBaseLinear hw hp f, weightedToBaseLinear hw hp g⟫_ℂ = ⟪f, g⟫_ℂ := by
  change ⟪weightedToBaseFun hw hp f, weightedToBaseFun hw hp g⟫_ℂ = _
  rw [L2.inner_def, L2.inner_def, integral_weightedMeasure μ hw (hp.mono fun _ h => h.le)]
  apply integral_congr_ae
  filter_upwards [ae_weightedToBaseFun hw hp f, ae_weightedToBaseFun hw hp g, hp]
    with x hf hg hx
  rw [hf, hg]
  conv_lhs =>
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ) _ (f x),
      RCLike.real_smul_eq_coe_smul (K := ℂ) _ (g x), inner_smul_real_left,
      inner_smul_real_right, smul_smul, ← pow_two, Real.sq_sqrt hx.le]

theorem weightedToBase_surjective (hw : Measurable w) (hp : ∀ᵐ x ∂μ, 0 < w x) :
    Function.Surjective (weightedToBaseFun hw hp) := by
  intro g
  let f : α → ℂ := fun x => (Real.sqrt (w x))⁻¹ • g x
  have hf : AEStronglyMeasurable f μ := hw.sqrt.inv.aestronglyMeasurable.smul (Lp.aestronglyMeasurable g)
  have hmul : (fun x => Real.sqrt (w x) • f x) =ᵐ[μ] g := by
    filter_upwards [hp] with x hx
    simp [f, (Real.sqrt_pos.2 hx).ne']
  have hfLp := (memLp_sqrt_weighted_iff hw hp hf).mp ((Lp.memLp g).ae_eq hmul.symm)
  refine ⟨hfLp.toLp f, Lp.ext ?_⟩
  filter_upwards [ae_weightedToBaseFun hw hp (hfLp.toLp f),
    eventually_of_weighted hw hp hfLp.coeFn_toLp, hmul] with x h₁ h₂ h₃
  rw [h₁, h₂, h₃]

/-- The surjective isometry from weighted to unweighted L² given by multiplication
by the square root of the density. The inverse may be an unbounded multiplier. -/
noncomputable def weightedL2Equiv (hw : Measurable w) (hp : ∀ᵐ x ∂μ, 0 < w x) :
    Lp ℂ 2 (weightedMeasure μ w) ≃ₗᵢ[ℂ] Lp ℂ 2 μ :=
  LinearIsometryEquiv.ofSurjective
    ((weightedToBaseLinear hw hp).isometryOfInner (weightedToBase_inner hw hp))
    (weightedToBase_surjective hw hp)

theorem ae_weightedL2Equiv (hw : Measurable w) (hp : ∀ᵐ x ∂μ, 0 < w x)
    (f : Lp ℂ 2 (weightedMeasure μ w)) :
    ⇑(weightedL2Equiv hw hp f) =ᵐ[μ] fun x => Real.sqrt (w x) • f x :=
  ae_weightedToBaseFun hw hp f

end SchauderBasisOrbits

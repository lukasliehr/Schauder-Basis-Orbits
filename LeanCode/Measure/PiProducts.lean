import LeanCode.Measure.Products
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Probability.Independence.Integration

open MeasureTheory Set Filter
open scoped BigOperators ENNReal

noncomputable section

namespace SchauderBasisOrbits

theorem measurePreserving_curry_const
    (ι κ K : Type*) [Fintype ι] [Fintype κ] [MeasurableSpace K]
    (ν : Measure K) [IsFiniteMeasure ν] :
    MeasurePreserving (MeasurableEquiv.curry ι κ K)
      (Measure.pi fun _ : ι × κ ↦ ν)
      (Measure.pi fun _ : ι ↦ Measure.pi fun _ : κ ↦ ν) := by
  let e := MeasurableEquiv.curry ι κ K
  have he : MeasurePreserving e.symm (Measure.pi fun _ : ι ↦ Measure.pi fun _ : κ ↦ ν)
      (Measure.pi fun _ : ι × κ ↦ ν) := by
    refine ⟨e.symm.measurable, (Measure.pi_eq fun s hs ↦ ?_).symm⟩
    have hp : e.symm ⁻¹' Set.univ.pi s = Set.univ.pi (fun i ↦ Set.univ.pi fun j ↦ s (i, j)) := by
      ext x
      simp [e, MeasurableEquiv.coe_curry_symm, Set.mem_pi, Function.uncurry, Prod.forall]
    rw [MeasurableEquiv.map_apply, hp, Measure.pi_pi]
    simp_rw [Measure.pi_pi]
    exact (Fintype.prod_prod_type (fun p : ι × κ ↦ ν (s p))).symm
  exact he.symm e.symm

theorem measurePreserving_piCurry_const
    (ι K : Type*) [Fintype ι] [MeasurableSpace K]
    (κ : ι → Type*) [∀ i, Fintype (κ i)] (ν : Measure K) [IsFiniteMeasure ν] :
    MeasurePreserving (MeasurableEquiv.piCurry (fun (_i : ι) (_k : κ _i) ↦ K))
      (Measure.pi fun _ : (Σ i, κ i) ↦ ν)
      (Measure.pi fun i : ι ↦ Measure.pi fun _ : κ i ↦ ν) := by
  let e := MeasurableEquiv.piCurry (fun (i : ι) (_ : κ i) ↦ K)
  have he : MeasurePreserving e.symm (Measure.pi fun i : ι ↦ Measure.pi fun _ : κ i ↦ ν)
      (Measure.pi fun _ : (Σ i, κ i) ↦ ν) := by
    refine ⟨e.symm.measurable, (Measure.pi_eq fun s _ ↦ ?_).symm⟩
    have hp : e.symm ⁻¹' Set.univ.pi s = Set.univ.pi (fun i ↦ Set.univ.pi fun j ↦ s ⟨i, j⟩) := by
      ext x
      simp [e, MeasurableEquiv.coe_piCurry_symm, Set.mem_pi, Sigma.uncurry, Sigma.forall]
    rw [MeasurableEquiv.map_apply, hp, Measure.pi_pi]
    simp_rw [Measure.pi_pi]
    exact (Fintype.prod_sigma (fun p : Σ i, κ i ↦ ν (s p))).symm
  exact he.symm e.symm


namespace FiberWeight

variable {ι α : Type*} [Fintype ι] [MeasurableSpace α]
variable {β : ι → Type*} [∀ i, MeasurableSpace (β i)] {κ : (i : ι) → Measure (β i)}
variable [∀ i, IsFiniteMeasure (κ i)] (W : ∀ i, FiberWeight α (κ i))

/-- Independent multiplication of finitely many constant-marginal fiber weights. -/
def pi : FiberWeight α (Measure.pi κ) where
  weight p := ∏ i, (W i).weight (p.1, p.2 i)
  measurable_weight := Finset.measurable_fun_prod _ fun i _ ↦
    (W i).measurable_weight.comp (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd))
  weight_pos _ := Finset.prod_pos fun i _ ↦ (W i).weight_pos _
  weight_le_one _ := Finset.prod_le_one₀ (fun i _ ↦ (W i).weight_pos _ |>.le)
    (fun i _ ↦ (W i).weight_le_one _)
  mass := ∏ i, (W i).mass
  mass_pos := Finset.prod_pos fun i _ ↦ (W i).mass_pos
  fiber_mass s := by
    rw [integral_fintype_prod_eq_prod (fun i y ↦ (W i).weight (s, y))]
    simp only [fiber_mass]

theorem density_pi (p : α × ((i : ι) → β i)) :
    (FiberWeight.pi W).density p = ∏ i, (W i).density (p.1, p.2 i) :=
  (Finset.prod_div_distrib ..).symm

theorem pi_mass_loss_le [∀ i, IsProbabilityMeasure (κ i)] (s : α) :
    1 - (FiberWeight.pi W).mass ≤ ∑ i, (1 - (W i).mass) := by
  classical
  change 1 - ∏ i, (W i).mass ≤ ∑ i, (1 - (W i).mass)
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty => simp
  | insert i I hi hind =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    have hprod : ∏ j ∈ I, (W j).mass ≤ 1 :=
      Finset.prod_le_one₀ (fun j _ ↦ (W j).mass_pos.le) (fun j _ ↦ (W j).mass_le_one s)
    nlinarith [mul_nonneg (sub_nonneg.mpr ((W i).mass_le_one s)) (sub_nonneg.mpr hprod)]

theorem mean_pi_separated (u : (i : ι) → α × (β i) → ℂ) (s : α) :
    (FiberWeight.pi W).mean (fun p ↦ ∏ i, u i (p.1, p.2 i)) s = ∏ i, (W i).mean (u i) s := by
  unfold mean
  simp only [density_pi, Complex.real_smul, Complex.ofReal_prod, ← Finset.prod_mul_distrib]
  exact integral_fintype_prod_eq_prod (fun i y ↦ (↑((W i).density (s, y)) : ℂ) * u i (s, y))

theorem fiberMeasure_pi (s : α) :
    (FiberWeight.pi W).fiberMeasure s = Measure.pi (fun i ↦ (W i).fiberMeasure s) := by
  refine (Measure.pi_eq fun A hA ↦ ?_).symm
  simp only [fiberMeasure, weightedMeasure, withDensity_apply _ (MeasurableSet.univ_pi hA)]
  rw [Measure.restrict_pi_pi]
  simp only [density_pi]
  have hi (i : ι) : Integrable (fun y ↦ (W i).density (s, y)) ((κ i).restrict (A i)) := by
    refine Integrable.of_bound ((W i).measurable_density.comp
      measurable_prodMk_left).aestronglyMeasurable (W i).mass⁻¹ (Eventually.of_forall fun y ↦ ?_)
    rw [Real.norm_of_nonneg ((W i).density_pos (s, y)).le]
    exact (W i).density_le_inv_mass (s, y)
  have hp := Integrable.fintype_prod_dep hi
  have hnn : ∀ x : (i : ι) → β i, 0 ≤ ∏ i, (W i).density (s, x i) :=
    fun x ↦ Finset.prod_nonneg fun i _ ↦ ((W i).density_pos (s, x i)).le
  rw [← ofReal_integral_eq_lintegral_ofReal hp (Eventually.of_forall hnn),
    integral_fintype_prod_eq_prod (fun i y ↦ (W i).density (s, y)), ENNReal.ofReal_prod_of_nonneg]
  · apply Finset.prod_congr rfl
    intro i _
    rw [withDensity_apply _ (hA i), ofReal_integral_eq_lintegral_ofReal (hi i)
      (Eventually.of_forall fun y ↦ ((W i).density_pos (s, y)).le)]
  · intro i _
    exact integral_nonneg fun y ↦ ((W i).density_pos (s, y)).le

theorem mean_pi_coordinate (i : ι) {u : α × β i → ℂ} (hu : Measurable u) (s : α) :
    (FiberWeight.pi W).mean (fun p ↦ u (p.1, p.2 i)) s = (W i).mean u s := by
  rw [mean_eq_integral_fiberMeasure, fiberMeasure_pi, mean_eq_integral_fiberMeasure]
  have hmeas : Measurable (fun y ↦ u (s, y)) := hu.comp measurable_prodMk_left
  have he := MeasureTheory.measurePreserving_eval (fun j ↦ (W j).fiberMeasure s) i
  rw [← integral_map (measurable_pi_apply i).aemeasurable hmeas.aestronglyMeasurable, he.map_eq]

theorem mean_pi_two_coordinates {i j : ι} (hij : i ≠ j)
    {u : α × β i → ℂ} {v : α × β j → ℂ} (hu : Measurable u) (hv : Measurable v) (s : α) :
    (FiberWeight.pi W).mean (fun p ↦ u (p.1, p.2 i) * v (p.1, p.2 j)) s =
      (W i).mean u s * (W j).mean v s := by
  let μ (k : ι) := (W k).fiberMeasure s
  letI (k : ι) : IsProbabilityMeasure (μ k) := inferInstanceAs (IsProbabilityMeasure ((W k).fiberMeasure s))
  let f (y : β i) := u (s, y)
  let g (y : β j) := v (s, y)
  have hf : Measurable f := hu.comp measurable_prodMk_left
  have hg : Measurable g := hv.comp measurable_prodMk_left
  have hi := (ProbabilityTheory.iIndepFun_pi (X := fun k ↦ (id : β k → β k)) (μ := μ)
    (fun _ ↦ aemeasurable_id)).indepFun hij
  have hfg := hi.comp hf hg
  have h := hfg.integral_fun_mul_eq_mul_integral
    ((hf.comp (measurable_pi_apply i)).aestronglyMeasurable (μ := Measure.pi μ))
    ((hg.comp (measurable_pi_apply j)).aestronglyMeasurable (μ := Measure.pi μ))
  change (∫ y, f (y i) * g (y j) ∂(Measure.pi μ)) =
    (∫ y, f (y i) ∂(Measure.pi μ)) * ∫ y, g (y j) ∂(Measure.pi μ) at h
  rw [mean_eq_integral_fiberMeasure, fiberMeasure_pi]
  change (∫ y, f (y i) * g (y j) ∂(Measure.pi μ)) = _
  rw [h, ← fiberMeasure_pi, ← mean_eq_integral_fiberMeasure (FiberWeight.pi W)
      (fun p ↦ u (p.1, p.2 i)), ← mean_eq_integral_fiberMeasure (FiberWeight.pi W)
      (fun p ↦ v (p.1, p.2 j)), mean_pi_coordinate W i hu, mean_pi_coordinate W j hv]

end FiberWeight

end SchauderBasisOrbits

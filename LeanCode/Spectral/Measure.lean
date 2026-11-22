module

public import LeanCode.Spectral.DensityMass
public import Mathlib.MeasureTheory.Measure.LevyConvergence

@[expose] public section

open MeasureTheory Set Filter
open scoped Topology InnerProductSpace

namespace SchauderBasisOrbits

variable {H : Type*} [ComplexHilbertSpace H] {U : ℝ → UnitaryOperator H}

private theorem tendsto_triangularWindow (t : ℝ) :
    Tendsto (fun n : ℕ ↦ triangularWindow ((n : ℝ) + 1) t) atTop (𝓝 1) := by
  have h : Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hs : Tendsto (fun n : ℕ ↦ 1 - |t| * (1 / ((n : ℝ) + 1))) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub (h.const_mul |t|)
  have hm := (tendsto_const_nhds (x := (0 : ℝ))).max hs
  rw [max_eq_right zero_le_one] at hm
  simpa only [triangularWindow, one_div, div_eq_mul_inv, one_mul] using hm

private theorem tendsto_windowedCoefficient (v : H) (t : ℝ) :
    Tendsto (fun n : ℕ ↦ windowedCoefficient U v ((n : ℝ) + 1) t) atTop
      (𝓝 (orbitCoefficient U v t)) := by
  simpa only [windowedCoefficient, Function.comp_apply, Complex.ofReal_one, one_mul] using
    ((Complex.continuous_ofReal.continuousAt.tendsto.comp
      (tendsto_triangularWindow t)).mul_const (orbitCoefficient U v t))

private noncomputable def boundedRealChar (t : ℝ) : BoundedContinuousFunction ℝ ℂ :=
  BoundedContinuousFunction.mkOfBound ⟨realChar t, continuous_realChar t⟩ 2 <| by
    intro x y
    change dist (realChar t x) (realChar t y) ≤ 2
    simpa only [dist_eq_norm, norm_realChar, one_add_one_eq_two] using
      norm_sub_le (realChar t x) (realChar t y)

private theorem continuous_integral_realChar (t : ℝ) :
    Continuous (fun μ : ProbabilityMeasure ℝ ↦ ∫ x, realChar t x ∂μ.toMeasure) := by
  refine continuous_iff_continuousAt.mpr fun μ ↦ ?_
  exact (ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ).mp
    (tendsto_id : Tendsto id (𝓝 μ) (𝓝 μ)) (boundedRealChar t)

/-- The spectral probability measure of a unit vector for the strongly continuous group. -/
theorem orbit_spectral_probability (hU : IsStronglyContinuousGroup U) {v : H} (hv : ‖v‖ = 1) :
    ∃ μ : ProbabilityMeasure ℝ,
      ∀ t, (∫ x, realChar t x ∂μ.toMeasure) = orbitCoefficient U v t := by
  let a (n : ℕ) : ProbabilityMeasure ℝ :=
    orbitApproximant hU hv (show 0 < (n : ℝ) + 1 by positivity)
  have ha (t : ℝ) :
      Tendsto (fun n ↦ ∫ x, realChar t x ∂(a n).toMeasure) atTop (𝓝 (orbitCoefficient U v t)) := by
    refine (tendsto_windowedCoefficient (U := U) v t).congr' ?_
    filter_upwards [] with n
    exact (integral_realChar_orbitApproximant hU hv (by positivity) t).symm
  have hcf (s : ℝ) : Tendsto (fun n ↦ charFun (a n).toMeasure s) atTop
      (𝓝 (orbitCoefficient U v (s / (2 * Real.pi)))) := by
    simpa only [charFun_eq_integral_realChar] using ha (s / (2 * Real.pi))
  have hcont : Continuous (fun s ↦ orbitCoefficient U v (s / (2 * Real.pi))) :=
    (continuous_orbitCoefficient hU v).comp (continuous_id.div_const _)
  have htight : IsTightMeasureSet (Set.range fun n ↦ (a n).toMeasure) :=
    isTightMeasureSet_of_tendsto_charFun hcont.continuousAt hcf
  have heq : {((m : ProbabilityMeasure ℝ) : Measure ℝ) | m ∈ Set.range a} =
      Set.range (fun n ↦ (a n).toMeasure) := by
    ext m
    constructor
    · rintro ⟨_, ⟨n, rfl⟩, rfl⟩
      exact ⟨n, rfl⟩
    · rintro ⟨n, rfl⟩
      exact ⟨a n, ⟨n, rfl⟩, rfl⟩
  have hcomp : IsCompact (closure (Set.range a)) :=
    isCompact_closure_of_isTightMeasureSet (heq ▸ htight)
  have hprincipal : Filter.map a atTop ≤ 𝓟 (closure (Set.range a)) := by
    rw [le_principal_iff]
    change ∀ᶠ n : ℕ in atTop, a n ∈ closure (Set.range a)
    exact Eventually.of_forall (fun n ↦ subset_closure ⟨n, rfl⟩)
  obtain ⟨μ, -, hμ⟩ := hcomp.exists_clusterPt hprincipal
  refine ⟨μ, fun t ↦ ?_⟩
  let J := fun m : ProbabilityMeasure ℝ ↦ ∫ x, realChar t x ∂m.toMeasure
  have hJ : ClusterPt (J μ) (𝓝 (orbitCoefficient U v t)) := by
    have hle : Filter.map J (Filter.map a atTop) ≤ 𝓝 (orbitCoefficient U v t) := by
      rw [Filter.map_map]
      exact ha t
    exact (hμ.map (continuous_integral_realChar t).continuousAt tendsto_map).mono hle
  by_contra hn
  exact (clusterPt_iff_not_disjoint.mp hJ) (disjoint_nhds_nhds.mpr hn)

end SchauderBasisOrbits

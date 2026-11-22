module

public import LeanCode.Target.Definitions

@[expose] public section

namespace SchauderBasisOrbits

open Function Submodule
open scoped InnerProductSpace Pointwise

variable {H : Type*} [ComplexHilbertSpace H] {U : ℝ → UnitaryOperator H}

theorem unitary_group_add (hU : IsStronglyContinuousGroup U) (s t : ℝ) (x : H) :
    U (s + t) x = U s (U t x) :=
  hU.1 s t x

theorem unitary_group_zero (hU : IsStronglyContinuousGroup U) (x : H) :
    U 0 x = x := by
  apply (U 0).injective
  simpa only [add_zero] using (hU.1 0 0 x).symm

theorem unitary_group_neg (hU : IsStronglyContinuousGroup U) (t : ℝ) :
    U (-t) = (U t).symm := by
  ext x
  apply (U t).injective
  rw [← hU.1, add_neg_cancel, unitary_group_zero hU, LinearIsometryEquiv.apply_symm_apply]

theorem unitary_group_commute (hU : IsStronglyContinuousGroup U) (s t : ℝ) (x : H) :
    U s (U t x) = U t (U s x) := by
  rw [← hU.1, ← hU.1, add_comm]

theorem continuous_orbit (hU : IsStronglyContinuousGroup U) (x : H) :
    Continuous (fun t : ℝ ↦ U t x) := hU.2 x

theorem unitary_group_norm (t : ℝ) (x : H) : ‖U t x‖ = ‖x‖ :=
  (U t).norm_map x

theorem unitary_group_inner (t : ℝ) (x y : H) : ⟪U t x, U t y⟫_ℂ = ⟪x, y⟫_ℂ :=
  (U t).inner_map_map x y

theorem IsCyclicVector.smul_of_ne_zero {v : H} (hv : IsCyclicVector U v) {a : ℂ}
    (ha : a ≠ 0) : IsCyclicVector U (a • v) := by
  have horbit : {U t (a • v) | t : ℝ} = a • {U t v | t : ℝ} := by
    ext x
    constructor
    · rintro ⟨t, rfl⟩
      rw [map_smul]
      exact Set.smul_mem_smul_set ⟨t, rfl⟩
    · rintro ⟨y, ⟨t, rfl⟩, rfl⟩
      exact ⟨t, map_smul (U t) a v⟩
  unfold IsCyclicVector at hv ⊢
  simpa only [horbit, span_smul_eq_of_isUnit _ a (isUnit_iff_ne_zero.mpr ha)] using hv

theorem cyclic_unit_vector (hH : ¬ FiniteDimensional ℂ H) {v : H} (hv : IsCyclicVector U v) :
    ∃ w, IsCyclicVector U w ∧ ‖w‖ = 1 := by
  have hv0 : v ≠ 0 := by
    intro eq
    subst v
    have hspan : span ℂ {U t (0 : H) | t : ℝ} = ⊥ := by
      rw [show {U t (0 : H) | t : ℝ} = {0} by ext x; simp, span_zero_singleton]
    rw [IsCyclicVector, hspan] at hv
    have hz : ∀ x : H, x = 0 := by
      intro x
      have hx := hv x
      simpa only [Submodule.bot_coe, closure_singleton, Set.mem_singleton_iff] using hx
    let : Subsingleton H := ⟨fun x y ↦ (hz x).trans (hz y).symm⟩
    exact hH inferInstance
  let a : ℂ := (↑‖v‖)⁻¹
  have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv0
  have ha : a ≠ 0 := inv_ne_zero (Complex.ofReal_ne_zero.mpr hn)
  refine ⟨a • v, IsCyclicVector.smul_of_ne_zero hv ha, ?_⟩
  simp [a, norm_smul, Complex.norm_real, hn]

end SchauderBasisOrbits

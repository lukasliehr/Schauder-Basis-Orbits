import LeanCode.Target.Group
import LeanCode.Basis.Criterion

open Filter Function Submodule
open scoped Topology InnerProductSpace

namespace SchauderBasisOrbits

variable {H : Type*} [ComplexHilbertSpace H] {U : ℝ → UnitaryOperator H}

/-- The reverse implication of the main theorem. -/
theorem orbit_basis_implies_simple_spectrum (hU : IsStronglyContinuousGroup U)
    {g : H} {t : ℕ → ℝ} {b : SchauderBasis ℂ H} (hb : ∀ n, b n = U (t n) g) :
    HasSimpleContinuousSpectrum U := by
  have hd := dense_span_schauderBasis b
  refine ⟨⟨g, hd.mono (span_mono ?_)⟩, ?_⟩
  · rintro _ ⟨n, rfl⟩
    exact ⟨t n, (hb n).symm⟩
  · rintro ⟨w, hw, heig⟩
    have ht := (continuous_norm.tendsto (0 : ℂ)).comp
      (tendsto_inner_schauderBasis b (C := ‖g‖)
        (fun n => (hb n ▸ (U (t n)).norm_map g).le) w)
    have hc (n : ℕ) : ‖⟪w, b n⟫_ℂ‖ = ‖⟪w, g⟫_ℂ‖ := by
      obtain ⟨c, hc⟩ := mem_span_singleton.mp (heig (-t n))
      have hnorm : ‖c‖ = 1 := by
        have h := congrArg norm hc
        rw [norm_smul, (U (-t n)).norm_map, ← one_mul ‖w‖] at h
        exact mul_right_cancel₀ (norm_ne_zero_iff.mpr hw) (by simpa using h)
      have hflip : ⟪w, (U (t n)) g⟫_ℂ = ⟪(U (-t n)) w, g⟫_ℂ := by
        rw [unitary_group_neg hU]
        calc
          _ = ⟪(U (t n)) ((U (t n)).symm w), (U (t n)) g⟫_ℂ := by simp
          _ = _ := (U (t n)).inner_map_map _ _
      rw [hb n, hflip, ← hc, inner_smul_left, norm_mul, RCLike.norm_conj, hnorm, one_mul]
    have hzero : ‖⟪w, g⟫_ℂ‖ = 0 := by
      apply (tendsto_const_nhds_iff (l := (atTop : Filter ℕ))).mp
      simpa only [Function.comp_def, hc, norm_zero] using ht
    have hortho : w ∈ (span ℂ (Set.range b))ᗮ := by
      rw [Submodule.mem_orthogonal']
      intro x hx
      induction hx using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨n, rfl⟩ := hy
        exact norm_eq_zero.mp ((hc n).trans hzero)
      | zero => exact inner_zero_right _
      | add x y _ _ hx hy => simp [inner_add_right, hx, hy]
      | smul c x _ hx => simp [inner_smul_right, hx]
    exact hw (hd.eq_zero_of_mem_orthogonal hortho)

end SchauderBasisOrbits

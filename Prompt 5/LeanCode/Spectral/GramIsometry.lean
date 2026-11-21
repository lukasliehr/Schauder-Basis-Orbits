import LeanCode.Target.Definitions

open Function Submodule
open scoped InnerProductSpace

namespace SchauderBasisOrbits

variable {E F : Type*} [ComplexHilbertSpace E] [ComplexHilbertSpace F]
variable {ι : Type*} {f : ι → E} {g : ι → F}

theorem norm_linearCombination_eq_of_inner_eq
    (h : ∀ i j, ⟪f i, f j⟫_ℂ = ⟪g i, g j⟫_ℂ) (c : ι →₀ ℂ) :
    ‖Finsupp.linearCombination ℂ f c‖ = ‖Finsupp.linearCombination ℂ g c‖ := by
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), norm_eq_sqrt_re_inner (𝕜 := ℂ)]
  simp_rw [Finsupp.linearCombination_apply, Finsupp.sum_inner, Finsupp.inner_sum,
    inner_smul_left, inner_smul_right, h]

/-- Families with equal Gram kernels define the same isometry on their dense spans. -/
theorem exists_isometry_of_gram_eq
    (h : ∀ i j, ⟪f i, f j⟫_ℂ = ⟪g i, g j⟫_ℂ)
    (hf : Dense (span ℂ (Set.range f) : Set E)) (hg : Dense (span ℂ (Set.range g) : Set F)) :
    ∃ A : E ≃ₗᵢ[ℂ] F, ∀ i, A (f i) = g i := by
  classical
  let a := Finsupp.linearCombination ℂ f
  let b := Finsupp.linearCombination ℂ g
  have hnorm (c : ι →₀ ℂ) : ‖a c‖ = ‖b c‖ :=
    norm_linearCombination_eq_of_inner_eq h c
  have hker : LinearMap.ker a = LinearMap.ker b := by
    ext c
    rw [LinearMap.mem_ker, LinearMap.mem_ker, ← norm_eq_zero, hnorm, norm_eq_zero]
  let B : LinearMap.range a ≃ₗ[ℂ] LinearMap.range b :=
    a.quotKerEquivRange.symm.trans
      ((Submodule.quotEquivOfEq _ _ hker).trans b.quotKerEquivRange)
  have hB (c : ι →₀ ℂ) (hc : a c ∈ LinearMap.range a) :
      (B ⟨a c, hc⟩ : F) = b c := by
    simp [B, LinearMap.quotKerEquivRange_symm_apply_image, Submodule.mkQ_apply]
  have hBa (x : LinearMap.range a) : ‖(LinearMap.range b).subtype (B x)‖ =
      ‖(LinearMap.range a).subtype x‖ := by
    change ‖(B x : F)‖ = ‖(x : E)‖
    obtain ⟨c, hc⟩ := x.property
    have hmem : a c ∈ LinearMap.range a := ⟨c, rfl⟩
    rw [show x = ⟨a c, hmem⟩ from Subtype.ext hc.symm]
    exact (congrArg norm (hB c hmem)).trans (hnorm c).symm
  have hfa : DenseRange (LinearMap.range a).subtype := by
    change Dense (Set.range (Subtype.val : LinearMap.range a → E))
    rw [Subtype.range_coe, show LinearMap.range a = span ℂ (Set.range f) from
      Finsupp.range_linearCombination ℂ (v := f)]
    exact hf
  have hgb : DenseRange (LinearMap.range b).subtype := by
    change Dense (Set.range (Subtype.val : LinearMap.range b → F))
    rw [Subtype.range_coe, show LinearMap.range b = span ℂ (Set.range g) from
      Finsupp.range_linearCombination ℂ (v := g)]
    exact hg
  let A := B.extendOfIsometry (LinearMap.range a).subtype (LinearMap.range b).subtype
    hfa hgb hBa
  refine ⟨A, fun i ↦ ?_⟩
  let c : ι →₀ ℂ := Finsupp.single i 1
  have ha : a c = f i := by simp [a, c]
  have hb : b c = g i := by simp [b, c]
  rw [← ha, ← hb]
  let x : LinearMap.range a := ⟨a c, ⟨c, rfl⟩⟩
  change A ((LinearMap.range a).subtype x) = b c
  exact (B.extendOfIsometry_eq _ _ hfa hgb hBa x).trans (hB c _)

end SchauderBasisOrbits

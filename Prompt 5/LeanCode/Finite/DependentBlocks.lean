import LeanCode.Finite.BlockPrefixes

open scoped BigOperators InnerProductSpace

noncomputable section

namespace SchauderBasisOrbits

/-- Pack the blocks in their original lexicographic order, even when their sizes differ. -/
def orderedDependentBlocks {m : ℕ} {n : Fin m → ℕ} {E : Type*}
    (v : (i : Fin m) → Fin (n i) → E) : Fin (∑ i, n i) → E :=
  fun k ↦ v (finSigmaFinEquiv.symm k).1 (finSigmaFinEquiv.symm k).2

@[simp] theorem orderedDependentBlocks_apply {m : ℕ} {n : Fin m → ℕ} {E : Type*}
    (v : (i : Fin m) → Fin (n i) → E) (i : Fin m) (j : Fin (n i)) :
    orderedDependentBlocks v (finSigmaFinEquiv ⟨i, j⟩) = v i j := by
  exact congrArg (fun p : Σ i, Fin (n i) ↦ v p.1 p.2)
    (finSigmaFinEquiv.symm_apply_apply ⟨i, j⟩)

theorem synth_orderedDependentBlocks {m : ℕ} {n : Fin m → ℕ} {𝕜 E : Type*} [RCLike 𝕜]
    [AddCommMonoid E] [Module 𝕜 E]
    (v : (i : Fin m) → Fin (n i) → E) (c : Fin (∑ i, n i) → 𝕜) :
    synth (orderedDependentBlocks v) c =
      ∑ i, synth (v i) (fun j ↦ c (finSigmaFinEquiv ⟨i, j⟩)) := by
  unfold synth
  calc
    _ = ∑ ij : Σ i, Fin (n i),
        c (finSigmaFinEquiv ij) • orderedDependentBlocks v (finSigmaFinEquiv ij) :=
      (Fintype.sum_equiv finSigmaFinEquiv _ _ (fun _ ↦ rfl)).symm
    _ = _ := by
      rw [Fintype.sum_sigma]
      simp only [orderedDependentBlocks_apply]

section Hilbert

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable {m : ℕ} {n : Fin m → ℕ}

theorem norm_sq_synth_orderedDependentBlocks (v : (i : Fin m) → Fin (n i) → E)
    (horth : ∀ i j, i ≠ j → ∀ k l, ⟪v i k, v j l⟫_𝕜 = 0) (c : Fin (∑ i, n i) → 𝕜) :
    ‖synth (orderedDependentBlocks v) c‖ ^ 2 =
      ∑ i, ‖synth (v i) (fun j ↦ c (finSigmaFinEquiv ⟨i, j⟩))‖ ^ 2 := by
  rw [synth_orderedDependentBlocks]
  apply norm_sq_sum_of_orthogonal (𝕜 := 𝕜)
  intro i j hij
  simp [synth, sum_inner, inner_sum, inner_smul_left, inner_smul_right, horth i j hij]

theorem hPrefix_orderedDependentBlocks (v : (i : Fin m) → Fin (n i) → E) {K : ℝ}
    (hK : 0 ≤ K)
    (horth : ∀ i j, i ≠ j → ∀ k l, ⟪v i k, v j l⟫_𝕜 = 0)
    (hprefix : ∀ i, HPrefix (𝕜 := 𝕜) (v i) K) :
    HPrefix (𝕜 := 𝕜) (orderedDependentBlocks v) K := by
  refine ⟨hK, fun k _ c ↦ ?_⟩
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hK (norm_nonneg _))).mp
  rw [mul_pow, norm_sq_synth_orderedDependentBlocks v horth, norm_sq_synth_orderedDependentBlocks v horth,
    Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  let p := ∑ j : Fin i.val, n (Fin.castLE i.2.le j)
  let l := min (n i) (k - p)
  have hl : l ≤ n i := min_le_left _ _
  have hEq (j : Fin (n i)) :
      truncCoeff k c (finSigmaFinEquiv ⟨i, j⟩) =
        truncCoeff l (fun s ↦ c (finSigmaFinEquiv ⟨i, s⟩)) j := by
    have hiff : (finSigmaFinEquiv ⟨i, j⟩).val < k ↔ j.val < l := by
      rw [finSigmaFinEquiv_apply]
      change p + j.val < k ↔ j.val < l
      dsimp only [l]
      rw [lt_min_iff, and_iff_right j.isLt]
      omega
    simp only [truncCoeff, hiff]
  simp_rw [hEq]
  rw [← mul_pow]
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hK (norm_nonneg _))).mpr
    ((hprefix i).2 l hl _)

theorem linearIndependent_orderedDependentBlocks (v : (i : Fin m) → Fin (n i) → E)
    (horth : ∀ i j, i ≠ j → ∀ k l, ⟪v i k, v j l⟫_𝕜 = 0)
    (hli : ∀ i, LinearIndependent 𝕜 (v i)) : LinearIndependent 𝕜 (orderedDependentBlocks v) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc r
  change synth (orderedDependentBlocks v) c = 0 at hc
  have hz := norm_sq_synth_orderedDependentBlocks v horth c
  rw [hc, norm_zero, zero_pow (by decide : 2 ≠ 0)] at hz
  obtain ⟨⟨i, j⟩, rfl⟩ := finSigmaFinEquiv.surjective r
  have hzr : ‖synth (v i) (fun j ↦ c (finSigmaFinEquiv ⟨i, j⟩))‖ ^ 2 = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun k _ ↦ sq_nonneg _)).mp hz.symm i (Finset.mem_univ i)
  have hsi : synth (v i) (fun j ↦ c (finSigmaFinEquiv ⟨i, j⟩)) = 0 := by
    have hnorm : ‖synth (v i) (fun j ↦ c (finSigmaFinEquiv ⟨i, j⟩))‖ = 0 := by nlinarith
    exact norm_eq_zero.mp hnorm
  exact (Fintype.linearIndependent_iff.mp (hli i)) _ hsi j

end Hilbert

end SchauderBasisOrbits

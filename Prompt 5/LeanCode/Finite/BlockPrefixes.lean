module

public import LeanCode.Finite.Families

@[expose] public section

open MeasureTheory
open scoped BigOperators InnerProductSpace

noncomputable section

namespace SchauderBasisOrbits

/-- The equal-size block concatenation in lexicographic order. -/
def orderedBlocks {m n : ℕ} {E : Type*} (v : Fin m → Fin n → E) : Fin (m * n) → E :=
  fun k ↦ v (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2

@[simp] theorem orderedBlocks_apply {m n : ℕ} {E : Type*} (v : Fin m → Fin n → E)
    (i : Fin m) (j : Fin n) : orderedBlocks v (finProdFinEquiv (i, j)) = v i j := by
  simp [orderedBlocks]

theorem synth_orderedBlocks {m n : ℕ} {𝕜 E : Type*} [RCLike 𝕜]
    [AddCommMonoid E] [Module 𝕜 E] (v : Fin m → Fin n → E) (c : Fin (m * n) → 𝕜) :
    synth (orderedBlocks v) c =
      ∑ i, synth (v i) (fun j ↦ c (finProdFinEquiv (i, j))) := by
  unfold synth
  calc
    _ = ∑ ij : Fin m × Fin n, c (finProdFinEquiv ij) • orderedBlocks v (finProdFinEquiv ij) :=
      (Fintype.sum_equiv finProdFinEquiv _ _ (fun _ ↦ rfl)).symm
    _ = _ := by
      rw [Fintype.sum_prod_type]
      simp only [orderedBlocks_apply]

section Hilbert

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable {m n : ℕ}

theorem norm_sq_sum_of_orthogonal {ι : Type*} [Fintype ι] (v : ι → E)
    (h : ∀ i j, i ≠ j → ⟪v i, v j⟫_𝕜 = 0) : ‖∑ i, v i‖ ^ 2 = ∑ i, ‖v i‖ ^ 2 := by
  classical
  have heq : ⟪∑ i, v i, ∑ i, v i⟫_𝕜 = ∑ i, ⟪v i, v i⟫_𝕜 := by
    simp only [sum_inner, inner_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_eq_single i]
    · intro j _ hij
      exact h j i hij
    · simp
  rw [← inner_self_eq_norm_sq (𝕜 := 𝕜) (∑ i, v i), heq]
  change RCLike.reLm (∑ i, ⟪v i, v i⟫_𝕜) = _
  rw [map_sum]
  exact Finset.sum_congr rfl fun i _ ↦ inner_self_eq_norm_sq (𝕜 := 𝕜) (v i)

theorem inner_synth_blocks_eq_zero (v : Fin m → Fin n → E)
    (horth : ∀ i j, i ≠ j → ∀ k l, ⟪v i k, v j l⟫_𝕜 = 0)
    {i j : Fin m} (hij : i ≠ j) (c d : Fin n → 𝕜) :
    ⟪synth (v i) c, synth (v j) d⟫_𝕜 = 0 := by
  simp [synth, sum_inner, inner_sum, inner_smul_left, inner_smul_right, horth i j hij]

theorem norm_sq_synth_orderedBlocks (v : Fin m → Fin n → E)
    (horth : ∀ i j, i ≠ j → ∀ k l, ⟪v i k, v j l⟫_𝕜 = 0) (c : Fin (m * n) → 𝕜) :
    ‖synth (orderedBlocks v) c‖ ^ 2 =
      ∑ i, ‖synth (v i) (fun j ↦ c (finProdFinEquiv (i, j)))‖ ^ 2 := by
  rw [synth_orderedBlocks]
  exact norm_sq_sum_of_orthogonal _ (fun i j hij ↦ inner_synth_blocks_eq_zero v horth hij _ _)

theorem hPrefix_orderedBlocks (v : Fin m → Fin n → E) {K : ℝ} (hK : 0 ≤ K)
    (horth : ∀ i j, i ≠ j → ∀ k l, ⟪v i k, v j l⟫_𝕜 = 0)
    (hprefix : ∀ i, HPrefix (𝕜 := 𝕜) (v i) K) :
    HPrefix (𝕜 := 𝕜) (orderedBlocks v) K := by
  refine ⟨hK, fun k _ c ↦ ?_⟩
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hK (norm_nonneg _))).mp
  rw [mul_pow, norm_sq_synth_orderedBlocks v horth, norm_sq_synth_orderedBlocks v horth,
    Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  let l := min n (k - n * i.val)
  have hl : l ≤ n := min_le_left _ _
  have hEq (j : Fin n) :
      truncCoeff k c (finProdFinEquiv (i, j)) =
        truncCoeff l (fun s ↦ c (finProdFinEquiv (i, s))) j := by
    have hiff : j.val + n * i.val < k ↔ j.val < l := by
      dsimp [l]
      rw [lt_min_iff, and_iff_right j.isLt]
      omega
    change (if j.val + n * i.val < k then c (finProdFinEquiv (i, j)) else 0) =
      (if j.val < l then c (finProdFinEquiv (i, j)) else 0)
    simp only [hiff]
  simp_rw [hEq]
  rw [← mul_pow]
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hK (norm_nonneg _))).mpr
    ((hprefix i).2 l hl _)

theorem linearIndependent_orderedBlocks (v : Fin m → Fin n → E)
    (horth : ∀ i j, i ≠ j → ∀ k l, ⟪v i k, v j l⟫_𝕜 = 0)
    (hli : ∀ i, LinearIndependent 𝕜 (v i)) : LinearIndependent 𝕜 (orderedBlocks v) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc r
  change synth (orderedBlocks v) c = 0 at hc
  have hz := norm_sq_synth_orderedBlocks v horth c
  rw [hc, norm_zero, zero_pow (by decide : 2 ≠ 0)] at hz
  let i := (finProdFinEquiv.symm r).1
  let j := (finProdFinEquiv.symm r).2
  have hzr : ‖synth (v i) (fun j ↦ c (finProdFinEquiv (i, j)))‖ ^ 2 = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun k _ ↦ sq_nonneg _)).mp hz.symm i (Finset.mem_univ i)
  have hsi : synth (v i) (fun j ↦ c (finProdFinEquiv (i, j))) = 0 := by
    have hnorm : ‖synth (v i) (fun j ↦ c (finProdFinEquiv (i, j)))‖ = 0 := by
      nlinarith
    exact norm_eq_zero.mp hnorm
  have h := (Fintype.linearIndependent_iff.mp (hli i)) _ hsi j
  have hr : finProdFinEquiv (i, j) = r := finProdFinEquiv.apply_symm_apply r
  simpa [hr] using h

end Hilbert

local postfix:1024 "†" => ContinuousLinearMap.adjoint

theorem synthCLM_adjoint_coordinate {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] {N : ℕ} (v : Fin N → E) (x : E) (i : Fin N) :
    ((synthCLM (𝕜 := ℂ) v)† x) i = ⟪v i, x⟫_ℂ := by
  rw [← show ⟪EuclideanSpace.single i (1 : ℂ), (synthCLM (𝕜 := ℂ) v)† x⟫_ℂ =
      ((synthCLM (𝕜 := ℂ) v)† x) i by simp [EuclideanSpace.inner_single_left],
    ContinuousLinearMap.adjoint_inner_right, synthCLM_apply]
  change ⟪synth v (Pi.single i (1 : ℂ)), x⟫_ℂ = _
  rw [synth_single, one_smul]

theorem clmGram_synthCLM_eq_gram {m : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] (v : Fin m → E) :
    clmGram (synthCLM v) = Matrix.gram ℂ v := by
  let e := Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin m)
  apply e.injective
  change e (clmGram (synthCLM v)) = e (Matrix.gram ℂ v)
  rw [show e (clmGram (synthCLM v)) = ((synthCLM v)† ∘L synthCLM v) from
    toEuclideanCLM_clmGram _]
  apply ContinuousLinearMap.ext
  intro c
  apply WithLp.ofLp_injective
  funext i
  change ((synthCLM (𝕜 := ℂ) v)† (synthCLM v c)) i = WithLp.ofLp (e (Matrix.gram ℂ v) c) i
  rw [synthCLM_adjoint_coordinate, synthCLM_apply, synth, inner_sum, Matrix.ofLp_toEuclideanCLM]
  simp only [inner_smul_right, Matrix.mulVec, dotProduct, Matrix.gram_apply]
  exact Finset.sum_congr rfl fun j _ ↦ mul_comm _ _

end SchauderBasisOrbits

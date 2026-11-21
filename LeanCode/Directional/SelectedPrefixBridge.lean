import LeanCode.Directional.SelectedPrefixData
import LeanCode.Directional.Amplification
import LeanCode.Finite.ColumnCuts
import LeanCode.Finite.PartialColumn

open Filter Function MeasureTheory Matrix
open scoped BigOperators InnerProductSpace MatrixOrder ComplexOrder

noncomputable section

namespace SchauderBasisOrbits.DirectionalInput

variable {ι : Type*} [Fintype ι]
variable {ρ : Measure (Base ι)} [IsProbabilityMeasure ρ] (D : DirectionalInput ρ)
variable {L r n : ℕ} {m : ℝ} (hm : 0 < m) (hm' : m ≤ ((1 : ℝ) / 2) ^ L)
variable (S : Scalar.Data r n)

local notation "q" => (D.d + L)
local notation "Ω" => (D.rowReferenceGram L)
local notation "H" => (columnTensorGram (D.rowSeedGram L hm hm') Ω S.complexGram)

theorem selectedTail_of_partialColumnBounds {K : ℝ} (hK : 1 ≤ K)
    (hH : (H).PosDef)
    (hPart : ∀ (k : Fin (n + 1)) l, l ≤ q → ∀ c : Fin (n + 1) × Fin q → ℂ,
      qform H (partialColumnMask ℂ (n + 1) q k l *ᵥ c) ≤ K ^ 2 * qform H c) :
    Injective (D.selectedTailSynthesis hm hm' S).centered ∧
      PB (D.selectedTailSynthesis hm hm' S).centeredGram K := by
  let s := ((D.seedFiber L hm hm').selected S).mass⁻¹
  let e : Fin ((n + 1) * q) ≃ Fin (n + 1) × Fin q := finProdFinEquiv.symm
  have hs : 0 < s := inv_pos.mpr (((D.seedFiber L hm hm').selected S).mass_pos)
  have hgram : Matrix.gram ℂ (D.selectedAugmented hm hm' S) = (s • H).submatrix e e :=
    D.selectedAugmented_gram_tensor hm hm' S
  have hPD : (Matrix.gram ℂ (D.selectedAugmented hm hm' S)).PosDef := by
    rw [hgram]
    exact (hH.smul hs).submatrix e.injective
  have hinj := D.selectedTail_centered_injective hm hm' S
    (Matrix.posDef_gram_iff_linearIndependent.mp hPD)
  refine ⟨hinj, D.selectedTail_centered_pb_of_gram hm hm' S (zero_le_one.trans hK) ?_⟩
  have hq : 0 < q := by have := D.d_pos; omega
  have hdiag (k : Fin (n + 1)) (l : ℕ) (hl : l ≤ q) (c : Fin (n + 1) × Fin q → ℂ) :
      qform H ((completedColumnMask ℂ (Fin q) (n + 1) k.val + incompleteColumnMask ℂ k l) *ᵥ c)
        ≤ K ^ 2 * qform H c := by
    rw [incompleteColumnMask_eq_embedding]
    exact hPart k l hl c
  have hpb : PB (Matrix.gram ℂ (D.selectedAugmented hm hm' S)) K := by
    rw [hgram]
    exact pb_submatrix_of_column_qform (zero_le_one.trans hK) hs.le
      (columnCutMask_qform_le hq hH.posSemidef hK hdiag)
  intro k hk c
  apply hpb.2 (q + k) _ c
  rw [Nat.succ_mul]
  omega

/-- The matrix partial-column estimates imply the centered prefix bound in the original order. -/
theorem selectedTail_of_columnMetrics {Ks : ℝ} (hKs : 1 ≤ Ks)
    (hH : (H).PosDef) (hΩ : (Ω).PosDef)
    (hFull : ∀ k : Fin (n + 1),
      completedColumnMask ℂ (Fin q) (n + 1) k.val * H *
        completedColumnMask ℂ (Fin q) (n + 1) k.val ≤ Ks ^ 2 • H)
    (hInsert : ∀ k : Fin (n + 1),
      (columnEmbedding ℂ (Fin q) k)ᴴ * H * columnEmbedding ℂ (Fin q) k ≤ Ω)
    (hExtract : ∀ k : Fin (n + 1),
      (columnEmbedding ℂ (Fin q) k)ᴴ * H⁻¹ * columnEmbedding ℂ (Fin q) k ≤ (1 + 2 * S.loss) • Ω⁻¹) :
    Injective (D.selectedTailSynthesis hm hm' S).centered ∧
      PB (D.selectedTailSynthesis hm hm' S).centeredGram
        (Real.sqrt (selectedPrefixSq Ks D.K S.loss)) := by
  have hq : 0 < q := by have := D.d_pos; omega
  let : Nonempty (Fin q) := ⟨⟨0, hq⟩⟩
  let K := Real.sqrt (selectedPrefixSq Ks D.K S.loss)
  have hbase : 1 ≤ selectedPrefixSq Ks D.K S.loss := by
    unfold selectedPrefixSq
    exact le_add_of_nonneg_right (sq_nonneg _)
  have hKsqr : 0 ≤ selectedPrefixSq Ks D.K S.loss := zero_le_one.trans hbase
  apply D.selectedTail_of_partialColumnBounds hm hm' S
    (K := K) ((sq_le_sq₀ zero_le_one (Real.sqrt_nonneg _)).mp (by
      change (1 : ℝ) ^ 2 ≤ (Real.sqrt (selectedPrefixSq Ks D.K S.loss)) ^ 2
      rw [Real.sq_sqrt hKsqr, one_pow]
      exact hbase)) hH
  intro k l hl c
  have h := partialColumn_qform_le hH hΩ k l hl hKs D.K_ge_one S.loss_nonneg
    (D.rowReferenceGram_pb L) (hFull k) (hInsert k) (hExtract k) c
  change _ ≤ (Real.sqrt (selectedPrefixSq Ks D.K S.loss)) ^ 2 * qform H c
  rw [Real.sq_sqrt hKsqr]
  exact h

end SchauderBasisOrbits.DirectionalInput

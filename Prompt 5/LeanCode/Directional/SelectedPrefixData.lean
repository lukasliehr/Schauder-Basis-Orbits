import LeanCode.Directional.RowMetric
import LeanCode.Directional.Amplification
import LeanCode.Finite.ActivatedRowCut
import LeanCode.Finite.PartialColumn
import LeanCode.Finite.ColumnCuts
import LeanCode.Directional.RowReference
import LeanCode.Directional.SelectedCentering
import LeanCode.Finite.ColumnMatrix
import LeanCode.Scalar.SupplyContract

open Filter Function MeasureTheory Submodule Matrix
open scoped ENNReal BigOperators ComplexConjugate InnerProductSpace MatrixOrder ComplexOrder

namespace SchauderBasisOrbits.DirectionalInput

noncomputable section

variable {ι : Type*} [Fintype ι]
variable {ρ : Measure (Base ι)} [IsProbabilityMeasure ρ] (D : DirectionalInput ρ)

theorem rowReferenceGram_pb (L : ℕ) : PB (D.rowReferenceGram L) D.K := by
  let a (i : Fin D.d) := D.rowLp (Fin.castAdd L i)
  let b (i : Fin L) := D.rowLp (Fin.natAdd D.d i)
  have hA : Matrix.gram ℂ a = Matrix.gram ℂ (productFamily ρ D.frequencies) := by
    ext i j
    change Matrix.gram ℂ (D.rowLp (L := L)) (Fin.castAdd L i) (Fin.castAdd L j) = _
    rw [D.gram_rowLp, D.rowReferenceGram_base_base, Matrix.gram_apply]
  have hB : Matrix.gram ℂ b = 1 := by
    classical
    ext i j
    change Matrix.gram ℂ (D.rowLp (L := L)) (Fin.natAdd D.d i) (Fin.natAdd D.d j) = _
    rw [D.gram_rowLp, D.rowReferenceGram_phase_phase, Matrix.one_apply]
  have hpA : HPrefix (𝕜 := ℂ) a D.K :=
    (hPrefix_iff_pb a _).mpr (hA ▸ (hPrefix_iff_pb _ _).mp D.prefix_bound)
  have hpB : HPrefix (𝕜 := ℂ) b D.K :=
    (hPrefix_iff_pb b _).mpr (hB ▸ PB.one D.K_ge_one)
  have hcross (i : Fin D.d) (j : Fin L) : ⟪a i, b j⟫_ℂ = 0 := by
    change Matrix.gram ℂ (D.rowLp (L := L)) (Fin.castAdd L i) (Fin.natAdd D.d j) = _
    rw [D.gram_rowLp, D.rowReferenceGram_base_phase]
  have hOrth (x : Lp ℂ 2 (rowMeasure (ρ := ρ) L)) (hx : x ∈ span ℂ (Set.range a))
      (y : Lp ℂ 2 (rowMeasure (ρ := ρ) L)) (hy : y ∈ span ℂ (Set.range b)) : ⟪x, y⟫_ℂ = 0 := by
    obtain ⟨u, rfl⟩ := (mem_span_range_iff_exists_fun ℂ).mp hx
    obtain ⟨v, rfl⟩ := (mem_span_range_iff_exists_fun ℂ).mp hy
    simp [sum_inner, inner_sum, inner_smul_left, inner_smul_right, hcross]
  have hp := append_small_angle_hPrefix a b hpA hpB (β := 0) le_rfl zero_lt_one
    (fun x hx y hy => by simp [hOrth x hx y hy])
  have heq : Fin.append a b = D.rowLp := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp [a, b]
  rw [heq] at hp
  have hp' : HPrefix (𝕜 := ℂ) (D.rowLp (L := L)) D.K := by
    simpa only [max_self, zero_add, add_zero, sub_zero, div_one, Real.sqrt_one, mul_one] using hp
  rw [← D.gram_rowLp, ← hPrefix_iff_pb]
  exact hp'

theorem selectedLp_gram_tensor {L r n : ℕ} {m : ℝ} (hm : 0 < m)
    (hm' : m ≤ ((1 : ℝ) / 2) ^ L) (S : Scalar.Data r n) :
    Matrix.gram ℂ (D.selectedLp hm hm' S) =
      ((D.seedFiber L hm hm').selected S).mass⁻¹ •
        columnTensorGram (D.rowSeedGram L hm hm') (D.rowReferenceGram L) S.complexGram := by
  ext ⟨k, i⟩ ⟨l, j⟩
  rw [D.selectedGram_formula hm hm' S]
  simp only [Matrix.smul_apply, columnTensorGram, Matrix.add_apply, Matrix.kronecker_apply,
    Matrix.one_apply, Matrix.sub_apply, Complex.real_smul, Complex.ofReal_inv]
  ring

theorem selectedAugmented_gram_tensor {L r n : ℕ} {m : ℝ} (hm : 0 < m)
    (hm' : m ≤ ((1 : ℝ) / 2) ^ L) (S : Scalar.Data r n) :
    let e : Fin ((n + 1) * (D.d + L)) ≃ Fin (n + 1) × Fin (D.d + L) := finProdFinEquiv.symm
    Matrix.gram ℂ (D.selectedAugmented hm hm' S) =
      (((D.seedFiber L hm hm').selected S).mass⁻¹ •
        columnTensorGram (D.rowSeedGram L hm hm') (D.rowReferenceGram L) S.complexGram).submatrix e e := by
  rw [← D.selectedLp_gram_tensor hm hm' S]
  rfl

set_option maxHeartbeats 1000000 in
/-- Positivity and every post-head prefix bound for the selected scalar packet.
Only the inverse diagonals from nonconstant scalar columns are needed. -/
theorem selected_packet_prefix_certificates {L : ℕ} {m δ z Ks : ℝ} (hm : 0 < m)
    (hm' : m ≤ ((1 : ℝ) / 2) ^ L) (S : Scalar.GoodScalar δ z) (hKs : 1 < Ks)
    (hKsδ : Scalar.commonBound δ < Ks) :
    LinearIndependent ℂ (D.selectedAugmented hm hm' S.data.toData) ∧
      PB (D.selectedTailSynthesis hm hm' S.data.toData).centeredGram
        (Real.sqrt (selectedPrefixSq Ks D.K S.data.toData.loss)) := by
  let S₀ := S.data.toData
  let n := S.length
  let q := D.d + L
  let ε := S₀.loss
  let W := (D.seedFiber L hm hm').selected S₀
  let B := S₀.complexGram
  let A := D.rowSeedGram L hm hm'
  let Ω := D.rowReferenceGram L
  let H := columnTensorGram A Ω B
  let R := selectedPrefixSq Ks D.K ε
  have hq : 0 < q := by
    have hd := D.d_pos
    dsimp only [q]
    omega
  let _ : Nonempty (Fin q) := ⟨⟨0, hq⟩⟩
  have hA : A.PosDef := D.rowSeedGram_posDef hm hm'
  have hΩ : Ω.PosDef := D.rowReferenceGram_posDef L
  have hAO : A ≤ Ω := (D.rowSeedGram_relative hm hm').2
  have hB : B.PosDef := S₀.complexGram_posDef
  have hPB₀ : PB B (Scalar.commonBound δ) := by
    change PB S₀.complexGram _
    rw [← S₀.complexify_gram]
    exact S.augmented_pb.complexify
  have hPB : PB B Ks := by
    refine ⟨hPB₀.1.trans hKsδ.le, fun k hk c ↦ (hPB₀.2 k hk c).trans ?_⟩
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hPB₀.1 hKsδ.le 2)
      (qform_nonneg hB.posSemidef c)
  obtain ⟨hH, hFull⟩ := columnTensorGram_completed_prefix hA hΩ hAO hB hKs.le hPB
  have hR : 1 ≤ R := by
    dsimp only [R, selectedPrefixSq]
    linarith only [sq_nonneg (Real.sqrt (Ks ^ 2 - 1) + Real.sqrt ((1 + 2 * ε) * D.K ^ 2 - 1))]
  have hR₀ : 0 ≤ R := zero_le_one.trans hR
  have hInv (j : Fin n) : RCLike.re (B⁻¹ j.succ j.succ) ≤ 1 + 2 * ε := by
    dsimp only [B, ε]
    rw [← S₀.complexify_gram, ← complexify_inv_eq S₀.gram_posDef.isUnit, complexify_apply]
    exact S.inverse_diagonal j
  refine ⟨D.selectedAugmented_independent_of_posDef hm hm' S₀ ?_, ?_⟩
  · rw [D.selectedLp_gram_tensor]
    exact hH.smul (inv_pos.mpr W.mass_pos)
  · apply D.selectedTail_centered_pb_of_gram hm hm' S₀ (Real.sqrt_nonneg R)
    intro k hk c
    let cut := q + k
    change k ≤ n * q at hk
    have hcut : cut ≤ (n + 1) * q := by
      change q + k ≤ (n + 1) * q
      rw [Nat.succ_mul]
      omega
    have hCut (u : Fin (n + 1) × Fin q → ℂ) :
        qform H (columnCutMask ℂ (n + 1) q cut *ᵥ u) ≤ R * qform H u := by
      rcases lt_or_eq_of_le hcut with hlt | heq
      · let j : Fin (n + 1) := ⟨cut / q, (Nat.div_lt_iff_lt_mul hq).mpr hlt⟩
        let l := cut % q
        have hl : l ≤ q := (Nat.mod_lt _ hq).le
        have hidx : cut = q * j.val + l := (Nat.div_add_mod cut q).symm
        have hj₀ : 1 ≤ j.val := (Nat.le_div_iff_mul_le hq).mpr (by simp [cut])
        obtain ⟨j', hj'⟩ : ∃ j' : Fin n, j'.succ = j := by
          have hJ := j.isLt
          refine ⟨⟨j.val - 1, by omega⟩, Fin.ext ?_⟩
          dsimp
          omega
        have hInv' : RCLike.re (B⁻¹ j j) ≤ 1 + 2 * ε := hj' ▸ hInv j'
        have hInsert := columnTensorGram_column_le hA.isHermitian hΩ.isHermitian hAO j
          S₀.mass_le_one (S₀.complexGram_diag j)
        have hExtract := columnTensorGram_inv_column_le hA hΩ hAO hB j
          (by linarith only [S₀.loss_nonneg] : 1 ≤ 1 + 2 * ε) hInv'
        rw [hidx, columnCutMask_column j hl, incompleteColumnMask_eq_embedding]
        change qform H (partialColumnMask ℂ (n + 1) q j l *ᵥ u) ≤ _
        exact partialColumn_qform_le hH hΩ j l hl hKs.le D.K_ge_one S₀.loss_nonneg
          (D.rowReferenceGram_pb L) (hFull j.val j.isLt.le) hInsert hExtract u
      · rw [heq, columnCutMask_full, Matrix.one_mulVec]
        exact le_mul_of_one_le_left (qform_nonneg hH.posSemidef _) hR
    rw [D.selectedAugmented_gram_tensor hm hm' S₀]
    simp only [qform_submatrix_equiv, Equiv.symm_symm, qform_smul, Real.sq_sqrt hR₀]
    rw [← columnCutMask_mulVec_flat]
    change W.mass⁻¹ * qform H (columnCutMask ℂ (n + 1) q cut *ᵥ (c ∘ finProdFinEquiv)) ≤
      R * (W.mass⁻¹ * qform H (c ∘ finProdFinEquiv))
    rw [mul_left_comm R W.mass⁻¹]
    exact mul_le_mul_of_nonneg_left (hCut _) (inv_nonneg.mpr W.mass_pos.le)

end

end SchauderBasisOrbits.DirectionalInput

import LeanCode.Directional.RowMoments

open Filter Function MeasureTheory Submodule Matrix
open scoped ENNReal BigOperators ComplexConjugate InnerProductSpace MatrixOrder ComplexOrder

namespace SchauderBasisOrbits.DirectionalInput

noncomputable section

variable {ι : Type*} [Fintype ι]
variable {ρ : Measure (Base ι)} [IsProbabilityMeasure ρ] (D : DirectionalInput ρ)

def rowMeasure (L : ℕ) : Measure (RowPoint ι L) := ρ.prod (torusHaar (Fin L))

instance (L : ℕ) : IsProbabilityMeasure (rowMeasure (ρ := ρ) L) :=
  inferInstanceAs (IsProbabilityMeasure (ρ.prod (torusHaar (Fin L))))

def rowLp {L : ℕ} (i : Fin (D.d + L)) : Lp ℂ 2 (rowMeasure (ρ := ρ) L) :=
  lift₂ _ (D.rawRow i) (D.measurable_rawRow i) 1 (fun p => (D.norm_rawRow i p).le)

theorem gram_rowLp {L : ℕ} : Matrix.gram ℂ (D.rowLp (L := L)) = D.rowReferenceGram L := by
  ext i j
  rw [Matrix.gram_apply, rowLp, rowLp, inner_lift₂]
  rfl

private theorem integral_phaseChar {L : ℕ} (i : Fin L) :
    ∫ y : UnitAddTorus (Fin L), fourier 1 (y i) ∂torusHaar (Fin L) = 0 := by
  have h (y : UnitAddTorus (Fin L)) :
      fourier 1 (y i) = torusChar (Pi.single i (1 : ℤ)) y :=
    (UnitAddTorus.mFourier_single y i).symm
  simp_rw [h]
  rw [integral_torusChar, ite_eq_right]
  intro hc
  have hh := congrFun hc i
  simpa using hh

private theorem integral_pair_phaseChar {L : ℕ} (i j : Fin L) :
    ∫ y : UnitAddTorus (Fin L), conj (fourier 1 (y i)) * fourier 1 (y j) ∂torusHaar (Fin L) =
      if i = j then 1 else 0 := by
  classical
  have hf (k : Fin L) (y : UnitAddTorus (Fin L)) :
      fourier 1 (y k) = torusChar (Pi.single k (1 : ℤ)) y :=
    (UnitAddTorus.mFourier_single y k).symm
  simp_rw [hf, ← torusChar_neg, ← torusChar_add]
  rw [integral_torusChar]
  have heq : -Pi.single i (1 : ℤ) + Pi.single j 1 = (0 : Fin L → ℤ) ↔ i = j := by
    rw [neg_add_eq_zero]
    constructor
    · intro h
      by_contra hn
      simpa [Pi.single_eq_of_ne hn] using congrFun h i
    · rintro rfl
      rfl
  simp only [heq]

theorem rowReferenceGram_base_base {L : ℕ} (i j : Fin D.d) :
    D.rowReferenceGram L (Fin.castAdd L i) (Fin.castAdd L j) =
      ⟪productFamily ρ D.frequencies i, productFamily ρ D.frequencies j⟫_ℂ := by
  rw [productFamily, productFamily, inner_lift₂, rowReferenceGram]
  have hfun (p : RowPoint ι L) :
      conj (D.rawRow (Fin.castAdd L i) p) * D.rawRow (Fin.castAdd L j) p =
        (conj (mixedChar (D.frequencies i) p.1) * mixedChar (D.frequencies j) p.1) * (1 : ℂ) := by
    simp [rawRow]
  rw [integral_congr_ae (Eventually.of_forall hfun),
    integral_prod_mul (fun p => conj (mixedChar (D.frequencies i) p) * mixedChar (D.frequencies j) p)
      (fun _ : UnitAddTorus (Fin L) => (1 : ℂ))]
  simp

theorem rowReferenceGram_base_phase {L : ℕ} (i : Fin D.d) (j : Fin L) :
    D.rowReferenceGram L (Fin.castAdd L i) (Fin.natAdd D.d j) = 0 := by
  rw [rowReferenceGram]
  have hfun (p : RowPoint ι L) :
      conj (D.rawRow (Fin.castAdd L i) p) * D.rawRow (Fin.natAdd D.d j) p =
        conj (mixedChar (D.frequencies i) p.1) * fourier 1 (p.2 j) := by
    simp [rawRow, phaseRow]
  rw [integral_congr_ae (Eventually.of_forall hfun),
    integral_prod_mul (fun p => conj (mixedChar (D.frequencies i) p)) (fun y : UnitAddTorus (Fin L) => fourier 1 (y j)),
    integral_phaseChar, mul_zero]

theorem rowReferenceGram_phase_phase {L : ℕ} (i j : Fin L) :
    D.rowReferenceGram L (Fin.natAdd D.d i) (Fin.natAdd D.d j) = if i = j then 1 else 0 := by
  classical
  rw [rowReferenceGram]
  have hfun (p : RowPoint ι L) :
      conj (D.rawRow (Fin.natAdd D.d i) p) * D.rawRow (Fin.natAdd D.d j) p =
        (1 : ℂ) * (conj (fourier 1 (p.2 i)) * fourier 1 (p.2 j)) := by
    simp [rawRow, phaseRow]
  rw [integral_congr_ae (Eventually.of_forall hfun),
    integral_prod_mul (fun _ : Base ι => (1 : ℂ)) (fun y : UnitAddTorus (Fin L) => conj (fourier 1 (y i)) * fourier 1 (y j)),
    integral_pair_phaseChar]
  simp

theorem rowReferenceGram_fromBlocks (L : ℕ) :
    (D.rowReferenceGram L).submatrix (finSumFinEquiv : Fin D.d ⊕ Fin L ≃ Fin (D.d + L))
      (finSumFinEquiv : Fin D.d ⊕ Fin L ≃ Fin (D.d + L)) =
      Matrix.fromBlocks (Matrix.gram ℂ (productFamily ρ D.frequencies)) 0 0 1 := by
  classical
  ext i j
  rcases i with i | i <;> rcases j with j | j
  · simpa [Matrix.gram_apply] using D.rowReferenceGram_base_base (L := L) i j
  · simpa using D.rowReferenceGram_base_phase (L := L) i j
  · have hHerm := (D.gram_rowLp (L := L)) ▸ Matrix.isHermitian_gram ℂ (D.rowLp (L := L))
    have hh := hHerm.apply (Fin.natAdd D.d i) (Fin.castAdd L j)
    simpa [D.rowReferenceGram_base_phase] using hh.symm
  · simpa [Matrix.one_apply] using D.rowReferenceGram_phase_phase (L := L) i j

theorem rowReferenceGram_posDef (L : ℕ) : (D.rowReferenceGram L).PosDef := by
  let G := Matrix.gram ℂ (productFamily ρ D.frequencies)
  have hG : G.PosDef := Matrix.posDef_gram_iff_linearIndependent.mpr D.independent
  have hI : (1 : Matrix (Fin L) (Fin L) ℂ).PosDef := Matrix.PosDef.one
  have hB : (Matrix.fromBlocks G (0 : Matrix (Fin D.d) (Fin L) ℂ) 0 1).PosDef := by
    apply posDef_of_qform_pos
    · change (Matrix.fromBlocks G (0 : Matrix (Fin D.d) (Fin L) ℂ) 0 1)ᴴ =
        Matrix.fromBlocks G 0 0 1
      rw [Matrix.fromBlocks_conjTranspose, hG.isHermitian.eq, conjTranspose_one, conjTranspose_zero, conjTranspose_zero]
    · intro x hx
      rw [qform_fromBlocks_diagonal]
      by_cases h : x ∘ Sum.inl = 0
      · have hR : x ∘ Sum.inr ≠ 0 := by
          intro h'
          apply hx
          funext i
          cases i with
          | inl i => exact congrFun h i
          | inr i => exact congrFun h' i
        exact add_pos_of_nonneg_of_pos (qform_nonneg hG.posSemidef _) (qform_pos hI hR)
      · exact add_pos_of_pos_of_nonneg (qform_pos hG h) (qform_nonneg hI.posSemidef _)
  dsimp [G] at hB
  rw [← D.rowReferenceGram_fromBlocks] at hB
  let e : Fin D.d ⊕ Fin L ≃ Fin (D.d + L) := finSumFinEquiv
  have h := hB.submatrix (e := e.symm) e.symm.injective
  convert h using 1
  ext i j
  simp [e, Matrix.submatrix]

end

end SchauderBasisOrbits.DirectionalInput

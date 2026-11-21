import LeanCode.Directional.RowMetric

open Filter Function MeasureTheory Submodule Matrix
open scoped ENNReal BigOperators ComplexConjugate InnerProductSpace MatrixOrder ComplexOrder

namespace SchauderBasisOrbits.DirectionalInput

noncomputable section

variable {ι : Type*} [Fintype ι]
variable {ρ : Measure (Base ι)} [IsProbabilityMeasure ρ] (D : DirectionalInput ρ)

def oldRowCoeffs (L : ℕ) (c : Fin D.d → ℂ) : Fin (D.d + L) → ℂ :=
  Fin.append c 0

def phaseOnes (L : ℕ) : Fin (D.d + L) → ℂ :=
  Fin.append 0 (fun _ : Fin L => 1)

theorem rowReferenceGram_phase_base {L : ℕ} (i : Fin L) (j : Fin D.d) :
    D.rowReferenceGram L (Fin.natAdd D.d i) (Fin.castAdd L j) = 0 := by
  have H := (D.gram_rowLp (L := L)) ▸ Matrix.isHermitian_gram ℂ (D.rowLp (L := L))
  rw [← H.apply (Fin.natAdd D.d i) (Fin.castAdd L j), D.rowReferenceGram_base_phase, star_zero]

theorem rowSeedGram_phase_base {L : ℕ} {m : ℝ} (hm : 0 < m)
    (hm' : m ≤ ((1 : ℝ) / 2) ^ L) (i : Fin L) (j : Fin D.d) :
    D.rowSeedGram L hm hm' (Fin.natAdd D.d i) (Fin.castAdd L j) =
      (m : ℂ) * ((D.seedScale : ℂ) *
        ⟪synth (productFamily ρ D.frequencies) D.coeff, productFamily ρ D.frequencies j⟫_ℂ) := by
  have H := (D.rowSeedGram_qform_and_hermitian hm hm').1
  rw [← H.apply (Fin.natAdd D.d i) (Fin.castAdd L j), D.rowSeedGram_base_phase hm hm']
  simp only [RCLike.star_def, map_mul, Complex.conj_ofReal, inner_conj_symm]

theorem refGram_oldRowCoeffs {L : ℕ} (c : Fin D.d → ℂ) :
    D.rowReferenceGram L *ᵥ D.oldRowCoeffs L c =
      Fin.append (fun i => ⟪productFamily ρ D.frequencies i, synth (productFamily ρ D.frequencies) c⟫_ℂ)
        (0 : Fin L → ℂ) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_add, oldRowCoeffs,
    Fin.append_left, Fin.append_right, Pi.zero_apply, mul_zero, Finset.sum_const_zero, add_zero]
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · simp only [Fin.append_left, D.rowReferenceGram_base_base, synth, inner_sum, inner_smul_right]
    exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
  · simp only [Fin.append_right, Pi.zero_apply, D.rowReferenceGram_phase_base, zero_mul, Finset.sum_const_zero]

theorem refGram_phaseOnes (L : ℕ) :
    D.rowReferenceGram L *ᵥ D.phaseOnes L = D.phaseOnes L := by
  classical
  funext i
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_add, phaseOnes,
    Fin.append_left, Fin.append_right, Pi.zero_apply, mul_zero, mul_one, Finset.sum_const_zero, zero_add]
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · simp only [Fin.append_left, Pi.zero_apply, D.rowReferenceGram_base_phase, Finset.sum_const_zero]
  · simp only [Fin.append_right, D.rowReferenceGram_phase_phase, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

/-- The action on the old coordinate subspace: the phase component is exactly
the pairing with the seed direction. -/
theorem seedGram_oldRowCoeffs {L : ℕ} {m : ℝ} (hm : 0 < m)
    (hm' : m ≤ ((1 : ℝ) / 2) ^ L) (c : Fin D.d → ℂ) :
    D.rowSeedGram L hm hm' *ᵥ D.oldRowCoeffs L c =
      (m : ℂ) • (D.rowReferenceGram L *ᵥ D.oldRowCoeffs L c +
        ((D.seedScale : ℂ) * ⟪synth (productFamily ρ D.frequencies) D.coeff,
          synth (productFamily ρ D.frequencies) c⟫_ℂ) • D.phaseOnes L) := by
  rw [D.refGram_oldRowCoeffs]
  funext i
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_add, oldRowCoeffs, Fin.append_left, Fin.append_right,
    Pi.zero_apply, mul_zero, Finset.sum_const_zero, add_zero, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · simp only [Fin.append_left, phaseOnes, Pi.zero_apply, mul_zero, add_zero,
      D.rowSeedGram_base_base hm hm', synth, inner_sum, inner_smul_right, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun _ _ => by ring)
  · simp only [Fin.append_right, phaseOnes, Pi.zero_apply, mul_one, zero_add,
      D.rowSeedGram_phase_base hm hm', synth, inner_sum, inner_smul_right, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun _ _ => by ring)

theorem seedGram_phaseOnes {L : ℕ} {m : ℝ} (hm : 0 < m)
    (hm' : m ≤ ((1 : ℝ) / 2) ^ L) :
    D.rowSeedGram L hm hm' *ᵥ D.phaseOnes L =
      (m : ℂ) • (((L : ℂ) * (D.seedScale : ℂ)) •
        (D.rowReferenceGram L *ᵥ D.oldRowCoeffs L D.coeff) +
        ((1 - D.seedTheta + (L : ℝ) * D.seedTheta : ℝ) : ℂ) • D.phaseOnes L) := by
  classical
  rw [D.refGram_oldRowCoeffs]
  funext i
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_add, phaseOnes,
    Fin.append_left, Fin.append_right, Pi.zero_apply, mul_zero, mul_one,
    Finset.sum_const_zero, zero_add, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · simp only [Fin.append_left, Pi.zero_apply, mul_zero, add_zero,
      D.rowSeedGram_base_phase hm hm', Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    ring
  · simp only [Fin.append_right, Pi.zero_apply, mul_zero, mul_one, zero_add,
      D.rowSeedGram_phase_phase hm hm', ← Finset.mul_sum]
    congr 1
    have he (j : Fin L) :
        (if i = j then 1 else (D.seedTheta : ℂ)) =
          (if i = j then 1 - (D.seedTheta : ℂ) else 0) + (D.seedTheta : ℂ) := by
      split <;> simp
    simp only [he, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ,
      ite_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    ring

end

end SchauderBasisOrbits.DirectionalInput

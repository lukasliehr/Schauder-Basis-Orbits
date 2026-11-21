import LeanCode.Directional.ProjectionResponse

open Matrix
open scoped MatrixOrder ComplexOrder ComplexConjugate BigOperators

namespace SchauderBasisOrbits

noncomputable section

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

theorem blockDiagonal_mulVec_apply (A : κ → Matrix ι ι ℂ) (x : ι × κ → ℂ)
    (i : ι) (k : κ) :
    (Matrix.blockDiagonal A *ᵥ x) (i, k) = (A k *ᵥ fun j => x (j, k)) i := by
  unfold Matrix.mulVec dotProduct
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro j _
  simp [Matrix.blockDiagonal_apply', Finset.sum_ite_eq, ite_mul]

theorem qform_blockDiagonal (A : κ → Matrix ι ι ℂ) (x : ι × κ → ℂ) :
    qform (Matrix.blockDiagonal A) x = ∑ k, qform (A k) (fun i => x (i, k)) := by
  simp only [qform, dotProduct]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  simp only [Pi.star_apply, blockDiagonal_mulVec_apply, map_sum]

theorem inv_blockDiagonal_of_posDef (A : κ → Matrix ι ι ℂ)
    (hA : ∀ k, (A k).PosDef) :
    (Matrix.blockDiagonal A)⁻¹ = Matrix.blockDiagonal (fun k => (A k)⁻¹) := by
  apply Matrix.inv_eq_left_inv
  rw [← Matrix.blockDiagonal_mul]
  have hEq : (fun k => (A k)⁻¹) * A = 1 := by
    funext k
    exact Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 (hA k).isUnit)
  change Matrix.blockDiagonal ((fun k => (A k)⁻¹) * A) = 1
  rw [hEq, Matrix.blockDiagonal_one]

theorem inv_real_smul_of_isUnit (A : Matrix ι ι ℂ) {s : ℝ} (hs : s ≠ 0) (hA : IsUnit A) :
    (s • A)⁻¹ = s⁻¹ • A⁻¹ := by
  apply Matrix.inv_eq_left_inv
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hs, one_smul,
    Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 hA)]

theorem blockDiagonal_isUnit_of_posDef (A : κ → Matrix ι ι ℂ)
    (hA : ∀ k, (A k).PosDef) : IsUnit (Matrix.blockDiagonal A) := by
  refine ⟨⟨Matrix.blockDiagonal A, Matrix.blockDiagonal (fun k => (A k)⁻¹), ?_, ?_⟩, rfl⟩
  · rw [← Matrix.blockDiagonal_mul]
    have hp : (fun k => A k * (A k)⁻¹) = 1 := by
      funext k
      exact Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (hA k).isUnit)
    rw [hp, Matrix.blockDiagonal_one]
  · rw [← Matrix.blockDiagonal_mul]
    have hp : (fun k => (A k)⁻¹ * A k) = 1 := by
      funext k
      exact Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 (hA k).isUnit)
    rw [hp, Matrix.blockDiagonal_one]

theorem isUnit_real_smul_matrix (A : Matrix ι ι ℂ) {s : ℝ} (hs : s ≠ 0) (hA : IsUnit A) :
    IsUnit (s • A) := by
  refine ⟨⟨s • A, s⁻¹ • A⁻¹, ?_, ?_⟩, rfl⟩
  · rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ hs, one_smul,
      Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hA)]
  · rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hs, one_smul,
      Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 hA)]

/-- The normalized projection quadratic form is the sum of the independent
scalar responses in the orthonormal row eigencoordinates. -/
theorem normalized_selected_block_response {r n : ℕ} (S : Scalar.Data r n)
    {M : ℝ} (hM : 0 < M) (β : κ → ℝ) (hβ : ∀ k, 0 ≤ β k ∧ β k ≤ 1) (c : κ → ℂ) :
    let A (i : κ) := complexify (Scalar.gramMix S.tailGram (β i))
    qform ((M⁻¹ : ℝ) • Matrix.blockDiagonal A)⁻¹
      (fun ji : Fin n × κ =>
        ((M⁻¹ : ℝ) : ℂ) * (((1 - β ji.2 : ℝ) : ℂ) * c ji.2 * (S.meanColumn ji.1 : ℂ))) =
      M⁻¹ * ∑ i, ‖c i‖ ^ 2 * S.response (β i) := by
  let A (i : κ) := complexify (Scalar.gramMix S.tailGram (β i))
  have hA (i : κ) : (A i).PosDef :=
    posDef_complexify (Scalar.gramMix_posDef S.tailGram_posDef (hβ i).1 (hβ i).2)
  change qform ((M⁻¹ : ℝ) • Matrix.blockDiagonal A)⁻¹ _ = _
  rw [inv_real_smul_of_isUnit _ (inv_ne_zero hM.ne') (blockDiagonal_isUnit_of_posDef A hA),
    inv_inv, qform_smul, inv_blockDiagonal_of_posDef A hA]
  let b (ji : Fin n × κ) := (((1 - β ji.2 : ℝ) : ℂ) * c ji.2 * (S.meanColumn ji.1 : ℂ))
  change M * qform (Matrix.blockDiagonal (fun i => (A i)⁻¹)) (((M⁻¹ : ℝ) : ℂ) • b) = _
  rw [complex_qform_smul_vec, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr hM.le),
    qform_blockDiagonal]
  simp only [b, A, scalar_block_response S (hβ _).1 (hβ _).2]
  field_simp

end

end SchauderBasisOrbits

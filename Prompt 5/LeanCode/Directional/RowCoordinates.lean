import LeanCode.Directional.SeedAction
import LeanCode.Directional.SeedSpectralWeights

open Filter Function MeasureTheory Submodule Matrix
open scoped ENNReal BigOperators ComplexConjugate InnerProductSpace MatrixOrder ComplexOrder

namespace SchauderBasisOrbits

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem qform_diag_real (β : ι → ℝ) (x : ι → ℂ) :
    qform (Matrix.diagonal (fun i => (β i : ℂ))) x = ∑ i, β i * ‖x i‖ ^ 2 := by
  simp only [qform, Matrix.mulVec_diagonal, dotProduct, map_sum, Pi.star_apply]
  apply Finset.sum_congr rfl
  intro i _
  have h : star (x i) * ((β i : ℂ) * x i) = (β i : ℂ) * ((‖x i‖ : ℂ) ^ 2) := by
    rw [← Complex.mul_conj']
    change conj (x i) * ((β i : ℂ) * x i) = _
    ring
  rw [h, ← Complex.ofReal_pow, ← Complex.ofReal_mul]
  rfl

/-- Coefficient coordinates in a basis orthonormal for the reference Gram. -/
def rowCoords (Ω E : Matrix ι ι ℂ) (x : ι → ℂ) : ι → ℂ :=
  Eᴴ *ᵥ (Ω *ᵥ x)

theorem rowCoords_reconstruct {Ω E : Matrix ι ι ℂ} (hE : IsUnit E) (hΩ : Eᴴ * Ω * E = 1) (x : ι → ℂ) :
    E *ᵥ rowCoords Ω E x = x := by
  have hl : Eᴴ * Ω = E⁻¹ := Matrix.inv_eq_left_inv hΩ |> Eq.symm
  rw [rowCoords, Matrix.mulVec_mulVec x Eᴴ Ω, hl, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _
    ((Matrix.isUnit_iff_isUnit_det _).1 hE), Matrix.one_mulVec]

theorem rowCoords_action {Ω E A : Matrix ι ι ℂ} (hE : IsUnit E) (hΩ : Eᴴ * Ω * E = 1)
    (β : ι → ℝ) (hA : Eᴴ * A * E = Matrix.diagonal (fun i => (β i : ℂ))) (x : ι → ℂ) :
    Eᴴ *ᵥ (A *ᵥ x) = Matrix.diagonal (fun i => (β i : ℂ)) *ᵥ rowCoords Ω E x := by
  rw [← hA, ← Matrix.mulVec_mulVec, rowCoords_reconstruct hE hΩ, ← Matrix.mulVec_mulVec]

theorem rowCoords_pairing {Ω E A : Matrix ι ι ℂ} (hE : IsUnit E) (hΩ : Eᴴ * Ω * E = 1)
    (β : ι → ℝ) (hA : Eᴴ * A * E = Matrix.diagonal (fun i => (β i : ℂ))) (x : ι → ℂ) (i : ι) :
    (Eᴴ *ᵥ ((Ω - A) *ᵥ x)) i = ((1 - β i : ℝ) : ℂ) * rowCoords Ω E x i := by
  rw [Matrix.sub_mulVec, Matrix.mulVec_sub, rowCoords_action hE hΩ β hA, Pi.sub_apply,
    Matrix.mulVec_diagonal, Complex.ofReal_sub, Complex.ofReal_one, sub_mul, one_mul]
  rfl

theorem rowCoords_qform {Ω E A : Matrix ι ι ℂ} (hE : IsUnit E) (hΩ : Eᴴ * Ω * E = 1)
    (β : ι → ℝ) (hA : Eᴴ * A * E = Matrix.diagonal (fun i => (β i : ℂ))) (x : ι → ℂ) :
    qform A x = ∑ i, β i * ‖rowCoords Ω E x i‖ ^ 2 := by
  rw [← qform_diag_real, ← hA, qform_conjTranspose_mul, rowCoords_reconstruct hE hΩ]

theorem rowCoords_norm_sq {Ω E : Matrix ι ι ℂ} (hE : IsUnit E) (hΩ : Eᴴ * Ω * E = 1)
    (x : ι → ℂ) :
    qform Ω x = ∑ i, ‖rowCoords Ω E x i‖ ^ 2 := by
  have hI : (1 : Matrix ι ι ℂ) = Matrix.diagonal (fun _ => ((1 : ℝ) : ℂ)) := by simp
  simpa only [one_mul] using rowCoords_qform hE hΩ (fun _ => 1) (hΩ.trans hI) x

end

end SchauderBasisOrbits

import LeanCode.Directional.Response
import LeanCode.Measure.Information

open Matrix Submodule ContinuousLinearMap
open scoped InnerProductSpace ComplexOrder MatrixOrder ComplexConjugate BigOperators

namespace SchauderBasisOrbits

noncomputable section

theorem complex_qform_smul_vec {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (x : ι → ℂ) (c : ℂ) :
    qform A (c • x) = ‖c‖ ^ 2 * qform A x := by
  rw [qform_eq_re_inner, qform_eq_re_inner]
  change RCLike.re ⟪c • WithLp.toLp 2 x,
    Matrix.toEuclideanCLM (𝕜 := ℂ) A (c • WithLp.toLp 2 x)⟫_ℂ = _
  rw [map_smul, inner_smul_left, inner_smul_right]
  change Complex.re (conj c * (c * _)) = _
  rw [← mul_assoc, mul_comm (conj c) c, Complex.mul_conj']
  simp only [← Complex.ofReal_pow, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero]
  rfl

theorem complex_qform_real_coefficients {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (x : ι → ℝ) :
    qform (complexify A) (fun i => (x i : ℂ)) = qform A x := by
  rw [qform_complexify]
  simp [qform]

/-- Projection response of one scalar block with a complex pairing coefficient. -/
theorem scalar_block_response {r n : ℕ} (S : Scalar.Data r n) {β : ℝ}
    (hβ : 0 ≤ β) (hβ₁ : β ≤ 1) (c : ℂ) :
    qform (complexify (Scalar.gramMix S.tailGram β))⁻¹
      (fun i => ((1 - β : ℝ) : ℂ) * c * (S.meanColumn i : ℂ)) =
        ‖c‖ ^ 2 * S.response β := by
  have hmix := Scalar.gramMix_posDef S.tailGram_posDef hβ hβ₁
  rw [Scalar.complexify_inv_of_posDef hmix]
  change qform (complexify (Scalar.gramMix S.tailGram β)⁻¹)
    ((((1 - β : ℝ) : ℂ) * c) • (fun i => (S.meanColumn i : ℂ))) = _
  rw [complex_qform_smul_vec, complex_qform_real_coefficients, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (sub_nonneg.mpr hβ₁), Scalar.Data.response]
  ring

section OrthogonalProjection

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type*} [Fintype ι]

theorem starProjection_iSup_of_orthogonal (F : ι → Submodule ℂ H)
    [∀ i, (F i).HasOrthogonalProjection] [(⨆ i, F i).HasOrthogonalProjection]
    (hF : ∀ i j, i ≠ j → F i ≤ (F j)ᗮ) (x : H) :
    (⨆ i, F i).starProjection x = ∑ i, (F i).starProjection x := by
  classical
  let S := ⨆ i, F i
  let p := ∑ i, (F i).starProjection x
  have hp : p ∈ S := Submodule.sum_mem _ fun i _ =>
    (le_iSup F i : F i ≤ S) ((F i).starProjection_apply_mem x)
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero hp ?_
  have hk : ∀ i, F i ≤ ((innerSL ℂ (x - p)).toLinearMap).ker := by
    intro i z hz
    change ⟪x - p, z⟫_ℂ = 0
    rw [inner_sub_left, sub_eq_zero, show p = ∑ i, (F i).starProjection x from rfl, sum_inner]
    symm
    rw [Finset.sum_eq_single i]
    · rw [(F i).inner_starProjection_left_eq_right, (F i).starProjection_eq_self_iff.mpr hz]
    · intro j _ hji
      exact ((F i).mem_orthogonal' _).mp
        (hF j i hji ((F j).starProjection_apply_mem x)) z hz
    · simp
  intro z hz
  exact (iSup_le hk) hz

theorem norm_sq_sum_orthogonal (x : ι → H)
    (h : ∀ i j, i ≠ j → ⟪x i, x j⟫_ℂ = 0) :
    ‖∑ i, x i‖ ^ 2 = ∑ i, ‖x i‖ ^ 2 := by
  classical
  calc
    _ = RCLike.re ⟪∑ i, x i, ∑ i, x i⟫_ℂ := (inner_self_eq_norm_sq _).symm
    _ = ∑ i, ‖x i‖ ^ 2 := by
      simp only [sum_inner, map_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [inner_sum, Finset.sum_eq_single i]
      · exact inner_self_eq_norm_sq _
      · intro j _ hji
        exact h i j hji.symm
      · simp

theorem norm_sq_starProjection_iSup_of_orthogonal (F : ι → Submodule ℂ H)
    [∀ i, (F i).HasOrthogonalProjection] [(⨆ i, F i).HasOrthogonalProjection]
    (hF : ∀ i j, i ≠ j → F i ≤ (F j)ᗮ) (x : H) :
    ‖(⨆ i, F i).starProjection x‖ ^ 2 = ∑ i, ‖(F i).starProjection x‖ ^ 2 := by
  rw [starProjection_iSup_of_orthogonal F hF]
  apply norm_sq_sum_orthogonal
  intro i j hij
  exact ((F j).mem_orthogonal' _).mp (hF i j hij ((F i).starProjection_apply_mem x))
    _ ((F j).starProjection_apply_mem x)

end OrthogonalProjection

section CaptureInversion

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem information_of_capture_sum {J P Q : H →L[ℂ] H} (hJ : J.IsPositive)
    (hP : P * P = P) (hQ : Q * Q = Q) (hPQ : P * Q = 0) (hQP : Q * P = 0)
    {s t : ℝ} (hs : s ≠ 1) (ht : t ≠ 1)
    (hC : informationCapture J = s • P + t • Q) :
    J = (s / (1 - s)) • P + (t / (1 - t)) • Q := by
  let C := s • P + t • Q
  let K := (s / (1 - s)) • P + (t / (1 - t)) • Q
  have hU := isUnit_one_add_positive hJ
  have hInv : 1 - C = Ring.inverse (1 + J) := by
    rw [← show informationCapture J = C from hC, informationCapture_eq_one_sub_inverse hJ]
    abel
  have hLeft : (1 - C) * J = C := by
    rw [hInv, ← show informationCapture J = C from hC,
      informationCapture_eq_one_sub_inverse hJ]
    have h := Ring.inverse_mul_cancel (1 + J) hU
    rw [mul_add, mul_one] at h
    exact eq_sub_iff_add_eq.mpr (by simpa only [add_comm] using h)
  have hRight : (1 - C) * K = C := by
    dsimp [C, K]
    rw [sub_mul, one_mul]
    simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, hP, hQ, hPQ, hQP,
      smul_zero, zero_add, add_zero, smul_smul]
    rw [add_sub_add_comm, ← sub_smul, ← sub_smul]
    congr 1 <;> (congr 1 <;> field_simp [sub_ne_zero.mpr hs.symm, sub_ne_zero.mpr ht.symm] <;> ring)
  have heq : Ring.inverse (1 + J) * J = Ring.inverse (1 + J) * K := by
    rw [← hInv, hLeft, hRight]
  have h := congrArg (fun T : H →L[ℂ] H => (1 + J) * T) heq
  simpa only [← mul_assoc, Ring.mul_inverse_cancel _ hU, one_mul] using h

end CaptureInversion

end

end SchauderBasisOrbits

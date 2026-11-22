module

public import LeanCode.Finite.Matrix

@[expose] public section

open Matrix
open scoped MatrixOrder ComplexOrder

namespace SchauderBasisOrbits.Scalar

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The matrix which replaces a fraction `β` of the weight by Haar measure. -/
noncomputable def gramMix (B : Matrix ι ι ℝ) (β : ℝ) : Matrix ι ι ℝ :=
  β • 1 + (1 - β) • B

omit [Fintype ι] in
lemma gramMix_posDef {B : Matrix ι ι ℝ} (hB : B.PosDef)
    {β : ℝ} (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1) : (gramMix B β).PosDef := by
  rcases hβ₁.eq_or_lt with rfl | hβ₁
  · simpa [gramMix] using (Matrix.PosDef.one : (1 : Matrix ι ι ℝ).PosDef)
  · exact Matrix.PosDef.posSemidef_add
      (Matrix.PosSemidef.one.smul hβ₀) (hB.smul (sub_pos.mpr hβ₁))

omit [Fintype ι] in
lemma gramMix_mono {B : Matrix ι ι ℝ} (hB : B ≤ 1)
    {x y : ℝ} (hxy : x ≤ y) : gramMix B x ≤ gramMix B y := by
  rw [Matrix.le_iff]
  have heq : gramMix B y - gramMix B x = (y - x) • (1 - B) := by
    unfold gramMix
    module
  rw [heq]
  exact (Matrix.le_iff.mp hB).smul (sub_nonneg.mpr hxy)

lemma gramMix_qform (B : Matrix ι ι ℝ) (β : ℝ) (x : ι → ℝ) :
    qform (gramMix B β) x = β * qform (1 : Matrix ι ι ℝ) x +
      (1 - β) * qform B x := by
  simp [gramMix]

/-- Inversion of a positive convex combination is bounded by the same combination of the
inverses. This is the special two-point averaging inequality needed for affine tuning. -/
lemma gramMix_inv_le_mix_inv {B : Matrix ι ι ℝ} (hB : B.PosDef)
    {β : ℝ} (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1) :
    (gramMix B β)⁻¹ ≤ gramMix B⁻¹ β := by
  have hM := gramMix_posDef hB hβ₀ hβ₁
  have hM' := gramMix_posDef hB.inv hβ₀ hβ₁
  apply matrix_le_of_qform_le hM.inv.isHermitian hM'.isHermitian
  intro v
  let c := (gramMix B β)⁻¹ *ᵥ v
  have h₁ := qform_inv_ge Matrix.PosDef.one v c
  have hB' := qform_inv_ge hB v c
  rw [show ((1 : Matrix ι ι ℝ)⁻¹) = 1 by simp] at h₁
  have ho : qform (gramMix B β)⁻¹ v =
      2 * RCLike.re (star v ⬝ᵥ c) - qform (gramMix B β) c :=
    (qform_inv_eq_optimum hM v).symm
  rw [ho, gramMix_qform, gramMix_qform]
  linarith only [mul_le_mul_of_nonneg_left h₁ hβ₀,
    mul_le_mul_of_nonneg_left hB' (sub_nonneg.mpr hβ₁)]

lemma complexify_inv_of_posDef {ι : Type*} [Fintype ι] [DecidableEq ι]
    {B : Matrix ι ι ℝ} (hB : B.PosDef) :
    (complexify B)⁻¹ = complexify (B⁻¹) := by
  apply Matrix.inv_eq_left_inv
  rw [← complexify_mul, Matrix.nonsing_inv_mul _
    ((Matrix.isUnit_iff_isUnit_det _).1 hB.isUnit), complexify_one]

end SchauderBasisOrbits.Scalar

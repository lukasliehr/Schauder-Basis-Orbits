import LeanCode.Fourier.Characters
import Mathlib.Algebra.MonoidAlgebra.MapDomain

open scoped ComplexConjugate

namespace SchauderBasisOrbits

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- Evaluation of a torus Fourier polynomial at a point. -/
noncomputable def torusEvalHom (x : UnitAddTorus ι) : TorusPoly ι →ₐ[ℂ] ℂ :=
  AddMonoidAlgebra.lift ℂ ℂ (ι → ℤ)
    { toFun := fun k => torusChar k.toAdd x
      map_one' := torusChar_zero x
      map_mul' := fun k l => torusChar_add k.toAdd l.toAdd x }

theorem torusEvalHom_apply (p : TorusPoly ι) (x : UnitAddTorus ι) :
    torusEvalHom x p = evalTorusPoly p x := by
  simp [torusEvalHom, AddMonoidAlgebra.lift_apply', evalTorusPoly]

@[simp] theorem evalTorusPoly_one (x : UnitAddTorus ι) : evalTorusPoly 1 x = 1 := by
  rw [← torusEvalHom_apply, map_one]

@[simp] theorem evalTorusPoly_add (p q : TorusPoly ι) (x : UnitAddTorus ι) :
    evalTorusPoly (p + q) x = evalTorusPoly p x + evalTorusPoly q x := by
  simp only [← torusEvalHom_apply, map_add]

@[simp] theorem evalTorusPoly_mul (p q : TorusPoly ι) (x : UnitAddTorus ι) :
    evalTorusPoly (p * q) x = evalTorusPoly p x * evalTorusPoly q x := by
  simp only [← torusEvalHom_apply, map_mul]

@[simp] theorem evalTorusPoly_smul (z : ℂ) (p : TorusPoly ι) (x : UnitAddTorus ι) :
    evalTorusPoly (z • p) x = z * evalTorusPoly p x := by
  simp only [← torusEvalHom_apply, map_smul, smul_eq_mul]

@[simp] theorem evalTorusPoly_single (k : ι → ℤ) (c : ℂ) (x : UnitAddTorus ι) :
    evalTorusPoly (AddMonoidAlgebra.single k c) x = c * torusChar k x := by
  rw [evalTorusPoly, AddMonoidAlgebra.coeff_single, Finsupp.sum_single_index (zero_mul _)]

@[simp] theorem evalTorusPoly_sum {α : Type*} (s : Finset α) (p : α → TorusPoly ι) (x : UnitAddTorus ι) :
    evalTorusPoly (∑ i ∈ s, p i) x = ∑ i ∈ s, evalTorusPoly (p i) x := by
  simp only [← torusEvalHom_apply, map_sum]

@[simp] theorem evalTorusPoly_prod {α : Type*} (s : Finset α) (p : α → TorusPoly ι) (x : UnitAddTorus ι) :
    evalTorusPoly (∏ i ∈ s, p i) x = ∏ i ∈ s, evalTorusPoly (p i) x := by
  simp only [← torusEvalHom_apply, map_prod]

theorem continuous_evalTorusPoly (p : TorusPoly ι) : Continuous (evalTorusPoly p) := by
  apply continuous_finsetSum
  intro k hk
  exact continuous_const.mul (continuous_torusChar k)

theorem norm_evalTorusPoly_le (p : TorusPoly ι) (x : UnitAddTorus ι) :
    ‖evalTorusPoly p x‖ ≤ ∑ k ∈ p.coeff.support, ‖p.coeff k‖ := by
  unfold evalTorusPoly Finsupp.sum
  calc
    _ ≤ ∑ k ∈ p.coeff.support, ‖p.coeff k * torusChar k x‖ := norm_sum_le ..
    _ = _ := by simp

theorem torusChar_add_arg (k : ι → ℤ) (x y : UnitAddTorus ι) :
    torusChar k (x + y) = torusChar k x * torusChar k y := by
  simp only [torusChar, UnitAddTorus.mFourier, ContinuousMap.coe_mk, Pi.add_apply, fourier_apply,
    zsmul_add, AddCircle.toCircle_add, Circle.coe_mul, Finset.prod_mul_distrib]

theorem torusChar_neg_arg (k : ι → ℤ) (x : UnitAddTorus ι) :
    torusChar k (-x) = conj (torusChar k x) := by
  rw [← torusChar_neg]
  simp only [torusChar, UnitAddTorus.mFourier, ContinuousMap.coe_mk, Pi.neg_apply,
    fourier_apply, zsmul_neg, neg_zsmul]

theorem torusChar_single [DecidableEq ι] (i : ι) (k : ℤ) (x : UnitAddTorus ι) :
    torusChar (Pi.single i k) x = fourier k (x i) := by
  simp only [torusChar, UnitAddTorus.mFourier, ContinuousMap.coe_mk]
  rw [Finset.prod_eq_single i]
  · simp
  · intro j hj hji
    simp [Pi.single_apply, hji]
  · simp

end SchauderBasisOrbits

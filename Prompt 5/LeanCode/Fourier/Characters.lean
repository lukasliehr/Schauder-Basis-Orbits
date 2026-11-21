import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

open scoped BigOperators ComplexConjugate
open Complex

namespace SchauderBasisOrbits

/-- The real character of frequency `t` at `x`, in the manuscript's convention. -/
noncomputable def realChar (t x : ℝ) : ℂ :=
  Complex.exp ((↑(2 * Real.pi * t * x) : ℂ) * Complex.I)

@[simp] theorem realChar_zero (x : ℝ) : realChar 0 x = 1 := by
  simp [realChar]

@[simp] theorem realChar_at_zero (t : ℝ) : realChar t 0 = 1 := by
  simp [realChar]

theorem realChar_add (t s x : ℝ) :
    realChar (t + s) x = realChar t x * realChar s x := by
  simp only [realChar, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem realChar_add_arg (t x y : ℝ) :
    realChar t (x + y) = realChar t x * realChar t y := by
  simp only [realChar, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem realChar_neg (t x : ℝ) : realChar (-t) x = conj (realChar t x) := by
  rw [realChar, realChar, ← Complex.exp_conj]
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  congr 1
  push_cast
  ring

@[simp] theorem norm_realChar (t x : ℝ) : ‖realChar t x‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

theorem continuous_realChar (t : ℝ) : Continuous (realChar t) := by
  unfold realChar
  fun_prop

theorem continuous_realChar_frequency (x : ℝ) : Continuous (fun t => realChar t x) := by
  unfold realChar
  fun_prop

variable {ι : Type*} [Fintype ι]

/-- The product character on a finite unit torus. -/
noncomputable abbrev torusChar (k : ι → ℤ) (x : UnitAddTorus ι) : ℂ :=
  UnitAddTorus.mFourier k x

@[simp] theorem torusChar_zero (x : UnitAddTorus ι) : torusChar 0 x = 1 := by
  simp [torusChar, UnitAddTorus.mFourier_zero]

theorem torusChar_add (k l : ι → ℤ) (x : UnitAddTorus ι) :
    torusChar (k + l) x = torusChar k x * torusChar l x :=
  UnitAddTorus.mFourier_add

theorem torusChar_neg (k : ι → ℤ) (x : UnitAddTorus ι) :
    torusChar (-k) x = conj (torusChar k x) :=
  UnitAddTorus.mFourier_neg

@[simp] theorem norm_torusChar (k : ι → ℤ) (x : UnitAddTorus ι) : ‖torusChar k x‖ = 1 := by
  simp only [torusChar, UnitAddTorus.mFourier, ContinuousMap.coe_mk, norm_prod,
    fourier_apply, Circle.norm_coe, Finset.prod_const_one]

theorem continuous_torusChar (k : ι → ℤ) : Continuous (torusChar k) :=
  (UnitAddTorus.mFourier k).continuous

/-- A rational real frequency and an integer auxiliary mode. -/
abbrev MixedFreq (ι : Type*) := ℚ × (ι → ℤ)

noncomputable def mixedChar (b : MixedFreq ι) (z : ℝ × UnitAddTorus ι) : ℂ :=
  realChar b.1 z.1 * torusChar b.2 z.2

@[simp] theorem norm_mixedChar (b : MixedFreq ι) (z : ℝ × UnitAddTorus ι) :
    ‖mixedChar b z‖ = 1 := by simp [mixedChar]

theorem continuous_mixedChar (b : MixedFreq ι) : Continuous (mixedChar b) :=
  ((continuous_realChar b.1).comp continuous_fst).mul
    ((continuous_torusChar b.2).comp continuous_snd)

/-- A finite Fourier polynomial on the auxiliary torus. -/
abbrev TorusPoly (ι : Type*) := AddMonoidAlgebra ℂ (ι → ℤ)

/-- A finite Fourier polynomial with rational frequencies on the real line. -/
abbrev RealPoly := AddMonoidAlgebra ℂ ℚ

/-- A finite Fourier polynomial on the line and auxiliary torus. -/
abbrev MixedPoly (ι : Type*) := AddMonoidAlgebra ℂ (MixedFreq ι)

noncomputable def evalTorusPoly (p : TorusPoly ι) (x : UnitAddTorus ι) : ℂ :=
  p.coeff.sum fun k c => c * torusChar k x

noncomputable def evalRealPoly (p : RealPoly) (x : ℝ) : ℂ :=
  p.coeff.sum fun k c => c * realChar k x

noncomputable def evalMixedPoly (p : MixedPoly ι) (x : ℝ × UnitAddTorus ι) : ℂ :=
  p.coeff.sum fun k c => c * mixedChar k x

@[simp] theorem mixedChar_zero (z : ℝ × UnitAddTorus ι) : mixedChar 0 z = 1 := by
  simp [mixedChar]

theorem mixedChar_add (a b : MixedFreq ι) (z : ℝ × UnitAddTorus ι) :
    mixedChar (a + b) z = mixedChar a z * mixedChar b z := by
  simp only [mixedChar, Prod.fst_add, Prod.snd_add, Rat.cast_add, realChar_add, torusChar_add]
  ring

theorem mixedChar_neg (b : MixedFreq ι) (z : ℝ × UnitAddTorus ι) :
    mixedChar (-b) z = conj (mixedChar b z) := by
  simp [mixedChar, realChar_neg, torusChar_neg]

/-- Pointwise evaluation of finite Fourier polynomials respects their algebra operations. -/
noncomputable def mixedEvalHom (z : ℝ × UnitAddTorus ι) : MixedPoly ι →ₐ[ℂ] ℂ :=
  AddMonoidAlgebra.lift ℂ ℂ (MixedFreq ι)
    { toFun := fun k => mixedChar k.toAdd z
      map_one' := mixedChar_zero z
      map_mul' := fun k l => mixedChar_add k.toAdd l.toAdd z }

theorem mixedEvalHom_apply (p : MixedPoly ι) (z : ℝ × UnitAddTorus ι) :
    mixedEvalHom z p = evalMixedPoly p z := by
  simp [mixedEvalHom, AddMonoidAlgebra.lift_apply', evalMixedPoly]

@[simp] theorem evalMixedPoly_one (z : ℝ × UnitAddTorus ι) : evalMixedPoly 1 z = 1 := by
  rw [← mixedEvalHom_apply, map_one]

@[simp] theorem evalMixedPoly_add (p q : MixedPoly ι) (z : ℝ × UnitAddTorus ι) :
    evalMixedPoly (p + q) z = evalMixedPoly p z + evalMixedPoly q z := by
  simp only [← mixedEvalHom_apply, map_add]

@[simp] theorem evalMixedPoly_sub (p q : MixedPoly ι) (z : ℝ × UnitAddTorus ι) :
    evalMixedPoly (p - q) z = evalMixedPoly p z - evalMixedPoly q z := by
  simp only [← mixedEvalHom_apply, map_sub]

@[simp] theorem evalMixedPoly_mul (p q : MixedPoly ι) (z : ℝ × UnitAddTorus ι) :
    evalMixedPoly (p * q) z = evalMixedPoly p z * evalMixedPoly q z := by
  simp only [← mixedEvalHom_apply, map_mul]

@[simp] theorem evalMixedPoly_single (b : MixedFreq ι) (c : ℂ) (z : ℝ × UnitAddTorus ι) :
    evalMixedPoly (AddMonoidAlgebra.single b c) z = c * mixedChar b z := by
  rw [evalMixedPoly, AddMonoidAlgebra.coeff_single, Finsupp.sum_single_index (zero_mul _)]

/-- Conjugate coefficients and negate all frequencies. -/
noncomputable def conjMixedPoly (p : MixedPoly ι) : MixedPoly ι :=
  AddMonoidAlgebra.ofCoeff ((p.coeff.mapRange (starRingEnd ℂ) (map_zero _)).mapDomain fun k => -k)

@[simp] theorem evalMixedPoly_conj (p : MixedPoly ι) (z : ℝ × UnitAddTorus ι) :
    evalMixedPoly (conjMixedPoly p) z = conj (evalMixedPoly p z) := by
  rw [evalMixedPoly, conjMixedPoly, AddMonoidAlgebra.coeff_ofCoeff,
    Finsupp.sum_mapDomain_index (h := fun b (c : ℂ) => c * mixedChar b z)
      (fun _ => zero_mul _) (fun _ _ _ => add_mul ..),
    Finsupp.sum_mapRange_index (fun _ => zero_mul _), evalMixedPoly, map_finsuppSum]
  apply Finsupp.sum_congr
  intro b _
  rw [mixedChar_neg, map_mul]

theorem continuous_evalMixedPoly (p : MixedPoly ι) : Continuous (evalMixedPoly p) := by
  apply continuous_finsetSum
  intro b _
  exact continuous_const.mul (continuous_mixedChar b)

theorem evalMixedPoly_bound (p : MixedPoly ι) (z : ℝ × UnitAddTorus ι) :
    ‖evalMixedPoly p z‖ ≤ ∑ b ∈ p.coeff.support, ‖p.coeff b‖ := by
  unfold evalMixedPoly Finsupp.sum
  calc
    _ ≤ ∑ b ∈ p.coeff.support, ‖p.coeff b * mixedChar b z‖ := norm_sum_le ..
    _ = _ := by simp

end SchauderBasisOrbits

import LeanCode.Construction.ResidualTensor

open Filter MeasureTheory Complex
open scoped BigOperators InnerProductSpace ComplexConjugate

noncomputable section

namespace SchauderBasisOrbits

abbrev ResidualCopyIndex (A : List ℚ) (N : ℕ) := Fin N × Fin (A.length + 1)

abbrev ResidualHelperSpace {r n : ℕ} (P : Scalar.Data r n) (ρ : Measure ℝ)
    (A : List ℚ) (N : ℕ) :=
  Lp ℂ 2 ((P.copiesFiberWeight (ResidualCopyIndex A N)).normalizedMeasure ρ)

variable {ρ : Measure ℝ} [IsFiniteMeasure ρ] {A : List ℚ} {q : ℚ}
variable {r n N : ℕ} (P : Scalar.Data r n)
variable (R : RationalResidualData ρ A q)

/-- The old residual normalized in its own Hilbert space. -/
def rationalResidualUnit (ρ : Measure ℝ) [IsFiniteMeasure ρ] (A : List ℚ) (q : ℚ) :
    Lp ℂ 2 ρ :=
  (‖rationalResidual ρ A q‖⁻¹ : ℝ) • rationalResidual ρ A q

theorem norm_rationalResidualUnit (h : rationalResidual ρ A q ≠ 0) :
    ‖rationalResidualUnit ρ A q‖ = 1 := by
  rw [rationalResidualUnit, norm_smul,
    Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)), inv_mul_cancel₀ (norm_ne_zero_iff.mpr h)]

theorem norm_smul_rationalResidualUnit (h : rationalResidual ρ A q ≠ 0) :
    ‖rationalResidual ρ A q‖ • rationalResidualUnit ρ A q = rationalResidual ρ A q := by
  rw [rationalResidualUnit, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr h), one_smul]

theorem rationalResidualUnit_orthogonal (A : List ℚ) (q : ℚ) :
    rationalResidualUnit ρ A q ∈ (rationalOldSpan ρ A)ᗮ := by
  change ((‖rationalResidual ρ A q‖⁻¹ : ℝ) : ℂ) • rationalResidual ρ A q ∈ _
  exact Submodule.smul_mem _ _ (rationalResidual_mem_orthogonal ρ A q)

def residualHelperFamily (i : Fin N) :
    Fin ((A.length + 1) * n) → ResidualHelperSpace P ρ A N :=
  orderedBlocks fun (j : Fin (A.length + 1)) (k : Fin n) ↦
    P.copyTensor ρ (i, j) (residualFrequencies A q j : ℝ) (PacketRep.char (P.mode k))

def residualHelperFreqs (i : Fin N) :
    Fin ((A.length + 1) * n) → MixedFreq (ResidualCopyIndex A N × Fin r) :=
  orderedBlocks fun (j : Fin (A.length + 1)) (k : Fin n) ↦
    (residualFrequencies A q j, extendBlockMode (i, j) (P.mode k))

theorem residualHelperFreqs_nonzero (i : Fin N) (k : Fin ((A.length + 1) * n)) :
    (residualHelperFreqs P (A := A) (q := q) i k).2 ≠ 0 :=
  extendBlockMode_ne_zero _ (P.mode_ne_zero _)

theorem residualHelperFreqs_injective (i : Fin N) :
    Function.Injective (fun k ↦ (residualHelperFreqs P (A := A) (q := q) i k).2) := by
  intro k l he
  let j := (finProdFinEquiv.symm k).1
  let j' := (finProdFinEquiv.symm l).1
  let s := (finProdFinEquiv.symm k).2
  let s' := (finProdFinEquiv.symm l).2
  change extendBlockMode (i, j) (P.mode s) = extendBlockMode (i, j') (P.mode s') at he
  have hje : j = j' := by
    by_contra hne
    exact (extendBlockMode_ne_of_ne (fun h ↦ hne (congrArg Prod.snd h)) (P.mode_ne_zero s)) he
  have hs : s = s' := P.mode_inj <| extendBlockMode_injective _ (by simpa only [hje] using he)
  apply finProdFinEquiv.symm.injective
  exact Prod.ext hje hs

theorem ae_residualHelperFamily (i : Fin N) (k : Fin ((A.length + 1) * n)) :
    ⇑(residualHelperFamily P (ρ := ρ) (A := A) (q := q) i k) =ᵐ[
      (P.copiesFiberWeight (ResidualCopyIndex A N)).normalizedMeasure ρ]
      mixedChar (residualHelperFreqs P (A := A) (q := q) i k) := by
  let j := (finProdFinEquiv.symm k).1
  let s := (finProdFinEquiv.symm k).2
  exact (P.ae_copyTensor ρ (i, j) (residualFrequencies A q j : ℝ) (PacketRep.char (P.mode s))).mono
    (fun x hx ↦ by
      change (P.copyTensor ρ (i, j) (residualFrequencies A q j : ℝ)
        (PacketRep.char (P.mode s))) x =
          mixedChar (residualFrequencies A q j, extendBlockMode (i, j) (P.mode s)) x
      rw [hx, Scalar.Data.copyTensorRaw, mixedChar, torusChar_extendBlockMode]
      rfl)

def residualNoise (i : Fin N) (g : PacketRep r) : ResidualHelperSpace P ρ A N :=
  ∑ j, R.coefficient j • P.copyTensor ρ (i, j) (residualFrequencies A q j : ℝ) g

theorem inner_pullback_residualNoise_eq_zero (i : Fin N) {g : PacketRep r} (hg : g.mean P = 0)
    (f : Lp ℂ 2 ρ) :
    ⟪(P.copiesFiberWeight (ResidualCopyIndex A N)).pullback ρ f, residualNoise P R i g⟫_ℂ = 0 := by
  simp only [residualNoise, inner_sum, inner_smul_right, P.inner_pullback_copyTensor_eq_zero ρ _ _ g hg,
    mul_zero, Finset.sum_const_zero]

theorem inner_residualNoise_distinct {i j : Fin N} (hij : i ≠ j)
    {g : PacketRep r} (hg : g.mean P = 0) :
    ⟪residualNoise P R i g, residualNoise P R j g⟫_ℂ = 0 := by
  unfold residualNoise
  rw [sum_inner]
  apply Finset.sum_eq_zero
  intro a _
  rw [inner_smul_left, inner_sum]
  apply mul_eq_zero_of_right
  apply Finset.sum_eq_zero
  intro b _
  rw [inner_smul_right, P.inner_copyTensor_eq_zero_of_ne ρ
    (fun h ↦ hij (congrArg Prod.fst h)) _ _ _ _ (Or.inl hg), mul_zero]

theorem norm_sq_residualNoise [IsProbabilityMeasure ρ] (i : Fin N)
    {g : PacketRep r} (hg : g.mean P = 0) {variance : ℝ}
    (hv : (∫ y, ‖g y‖ ^ 2 ∂P.normalizedMeasure) = variance) :
    ‖residualNoise P R i g‖ ^ 2 = R.coefficientEnergy * variance := by
  unfold residualNoise
  rw [norm_sq_sum_of_orthogonal (𝕜 := ℂ)]
  · simp only [norm_smul, mul_pow, P.norm_sq_copyTensor, hv, RationalResidualData.coefficientEnergy,
      Finset.sum_mul]
  · intro k l hne
    rw [inner_smul_left, inner_smul_right,
      P.inner_copyTensor_eq_zero_of_ne ρ (fun h ↦ hne (congrArg Prod.snd h)) _ _ _ _ (Or.inl hg)]
    simp

def residualHelperDirection (i : Fin N) (g : PacketRep r) (z : ℝ) :
    ResidualHelperSpace P ρ A N :=
  residualDirection ‖rationalResidual ρ A q‖ (R.coefficientEnergy * (1 / z))
    ((P.copiesFiberWeight (ResidualCopyIndex A N)).pullback ρ (rationalResidualUnit ρ A q))
    (residualNoise P R i (g.subConst 1))

theorem residualHelperDirection_norm [IsProbabilityMeasure ρ] {z : ℝ} (hz : 0 < z)
    (hr : rationalResidual ρ A q ≠ 0) (i : Fin N) {g : PacketRep r} (hg : g.mean P = 1)
    (hv : (∫ y, ‖g.subConst 1 y‖ ^ 2 ∂P.normalizedMeasure) = 1 / z) :
    ‖residualHelperDirection P R i g z‖ = 1 := by
  unfold residualHelperDirection
  have hmean : (g.subConst 1).mean P = 0 := by rw [P.packetRep_mean_subConst, hg, sub_self]
  refine norm_residualDirection _ _ _ _
    (add_pos_of_nonneg_of_pos (sq_nonneg _) (mul_pos (lt_of_lt_of_le zero_lt_one R.coefficientEnergy_ge_one)
      (one_div_pos.mpr hz))) ?_ ?_ ?_
  · rw [LinearIsometry.norm_map, norm_rationalResidualUnit hr]
  · exact inner_pullback_residualNoise_eq_zero P R i hmean _
  · exact norm_sq_residualNoise P R i hmean hv

theorem residualHelperDirection_pairwise {z : ℝ}
    (hr : rationalResidual ρ A q ≠ 0) {i j : Fin N} (hij : i ≠ j)
    {g : PacketRep r} (hg : g.mean P = 1) :
    ⟪residualHelperDirection P R i g z, residualHelperDirection P R j g z⟫_ℂ =
      (↑((residualCopyParameter ‖rationalResidual ρ A q‖ z R.coefficientEnergy) ^ 2) : ℂ) := by
  have hm : (g.subConst 1).mean P = 0 := by rw [P.packetRep_mean_subConst, hg, sub_self]
  unfold residualHelperDirection residualCopyParameter
  rw [inner_residualDirection_distinct _ _ _ _ _
    (by rw [LinearIsometry.norm_map, norm_rationalResidualUnit hr])
    (inner_pullback_residualNoise_eq_zero P R i hm _)
    (inner_pullback_residualNoise_eq_zero P R j hm _) (inner_residualNoise_distinct P R hij hm),
    one_div, mul_comm (R.coefficientEnergy)]

theorem inner_residualHelperDirection_pullback {z : ℝ} (i : Fin N)
    {g : PacketRep r} (hg : g.mean P = 1) (f : Lp ℂ 2 ρ) :
    ⟪residualHelperDirection P R i g z, (P.copiesFiberWeight (ResidualCopyIndex A N)).pullback ρ f⟫_ℂ =
      (↑(residualCopyParameter ‖rationalResidual ρ A q‖ z R.coefficientEnergy) : ℂ) *
        ⟪rationalResidualUnit ρ A q, f⟫_ℂ := by
  have hm : (g.subConst 1).mean P = 0 := by rw [P.packetRep_mean_subConst, hg, sub_self]
  unfold residualHelperDirection residualCopyParameter
  rw [inner_residualDirection_base _ _ _ _ _ (by
      rw [← inner_conj_symm, inner_pullback_residualNoise_eq_zero P R i hm f, map_zero]),
    LinearIsometry.inner_map_map, one_div, mul_comm R.coefficientEnergy]

theorem residualHelperDirection_eq_sum (hr : rationalResidual ρ A q ≠ 0)
    (i : Fin N) (c : Fin n → ℝ) (z : ℝ) :
    residualHelperDirection P R i (PacketRep.scalarCombination P c) z =
      ((Real.sqrt (‖rationalResidual ρ A q‖ ^ 2 + R.coefficientEnergy * (1 / z)))⁻¹ : ℝ) •
        ∑ j, R.coefficient j •
          P.copyTensor ρ (i, j) (residualFrequencies A q j : ℝ) (PacketRep.scalarCombination P c) := by
  let W := P.copiesFiberWeight (ResidualCopyIndex A N)
  have hbase : ‖rationalResidual ρ A q‖ • W.pullback ρ (rationalResidualUnit ρ A q) =
      W.pullback ρ (rationalResidual ρ A q) := by
    change (‖rationalResidual ρ A q‖ : ℂ) • W.pullback ρ (rationalResidualUnit ρ A q) = _
    rw [← map_smul]
    exact congrArg (W.pullback ρ) (norm_smul_rationalResidualUnit hr)
  unfold residualHelperDirection residualDirection
  change _ • (‖rationalResidual ρ A q‖ • W.pullback ρ (rationalResidualUnit ρ A q) + _) = _
  rw [hbase]
  congr 1
  have hr' : W.pullback ρ (rationalResidual ρ A q) =
      ∑ j, R.coefficient j • W.pullback ρ (residualAugmentedFamily ρ A q j) := by
    rw [← R.synth_eq, synth, map_sum]
    simp only [map_smul]
  rw [hr', residualNoise, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [← smul_add, P.copyTensor_decompose ρ (i, j) (residualFrequencies A q j : ℝ)
    (PacketRep.scalarCombination P c) 1, one_smul]
  congr 1
  apply add_comm

theorem residualHelperDirection_mem_span (hr : rationalResidual ρ A q ≠ 0)
    (i : Fin N) (c : Fin n → ℝ) (z : ℝ) :
    residualHelperDirection P R i (PacketRep.scalarCombination P c) z ∈
      Submodule.span ℂ (Set.range (residualHelperFamily P (ρ := ρ) (A := A) (q := q) i)) := by
  rw [residualHelperDirection_eq_sum P R hr]
  change (↑((Real.sqrt (‖rationalResidual ρ A q‖ ^ 2 + R.coefficientEnergy * (1 / z)))⁻¹) : ℂ) •
    (∑ j, R.coefficient j • P.copyTensor ρ (i, j) (residualFrequencies A q j : ℝ)
      (PacketRep.scalarCombination P c)) ∈ _
  apply Submodule.smul_mem
  apply Submodule.sum_mem
  intro j _
  apply Submodule.smul_mem
  rw [P.copyTensor_scalarCombination ρ]
  unfold synth
  apply Submodule.sum_mem
  intro k _
  apply Submodule.smul_mem
  apply Submodule.subset_span
  refine ⟨finProdFinEquiv (j, k), ?_⟩
  exact orderedBlocks_apply _ j k

end SchauderBasisOrbits

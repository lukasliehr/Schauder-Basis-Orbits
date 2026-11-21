import LeanCode.Construction.ResidualBounds
import LeanCode.Directional.Seed

open MeasureTheory Filter Submodule Complex Function
open scoped BigOperators InnerProductSpace

noncomputable section

namespace SchauderBasisOrbits

namespace Scalar.Data

variable {ρ : Measure ℝ} [IsProbabilityMeasure ρ] {A : List ℚ} {q : ℚ}
variable {r n N : ℕ} (P : Data r n)

theorem residualHelperFamily_independent (i : Fin N) :
    LinearIndependent ℂ (residualHelperFamily P (ρ := ρ) (A := A) (q := q) i) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc j
  let C := WithLp.toLp 2 c
  let S := residualHelperSynthesis P (ρ := ρ) (A := A) (q := q) i
  have h : S.full C = 0 := by
    rw [show S.full = _ from residualHelperSynthesis_full P i, synthCLM_apply]
    exact hc
  have he := S.full_injective (residualHelperSynthesis_centered_injective P i)
    (h.trans S.full.map_zero.symm)
  exact congrArg (fun c : EuclideanSpace ℂ (Fin ((A.length + 1) * n)) ↦ c j) he

theorem productFamily_residualHelperFreqs (i : Fin N) :
    productFamily ((P.copiesFiberWeight (ResidualCopyIndex A N)).normalizedMeasure ρ)
      (residualHelperFreqs P (A := A) (q := q) i) =
    residualHelperFamily P (ρ := ρ) (A := A) (q := q) i := by
  funext j
  apply Lp.ext
  exact (ae_lift₂ _ _ _ _ _).trans (ae_residualHelperFamily P i j).symm

theorem exists_residual_directionalInput (R : RationalResidualData ρ A q)
    (hr : rationalResidual ρ A q ≠ 0) (i : Fin N) (c : Fin n → ℝ) {z K : ℝ}
    (hNorm : ‖residualHelperDirection P R i (PacketRep.scalarCombination P c) z‖ = 1)
    (hPrefix : HPrefix (𝕜 := ℂ) (residualHelperFamily P (ρ := ρ) (A := A) (q := q) i) K) :
    ∃ V : DirectionalInput ((P.copiesFiberWeight (ResidualCopyIndex A N)).normalizedMeasure ρ),
      V.K = K ∧
      synth (productFamily _ V.frequencies) V.coeff =
        residualHelperDirection P R i (PacketRep.scalarCombination P c) z ∧
        Function.Injective (fun k ↦ (V.frequencies k).2) := by
  have hPos : 0 < (A.length + 1) * n := Nat.mul_pos (Nat.succ_pos _) P.size_pos
  have hInd := P.residualHelperFamily_independent (ρ := ρ) (A := A) (q := q) i
  let j : Fin ((A.length + 1) * n) := ⟨0, hPos⟩
  have hK : 1 ≤ K := hPrefix.one_le_of_nonzero (hInd.ne_zero j)
  have hmem := residualHelperDirection_mem_span P R hr i c z
  obtain ⟨b, hb⟩ := (mem_span_range_iff_exists_fun ℂ).mp hmem
  have hvec : synth
      (productFamily ((P.copiesFiberWeight (ResidualCopyIndex A N)).normalizedMeasure ρ)
        (residualHelperFreqs P (A := A) (q := q) i)) b =
      residualHelperDirection P R i (PacketRep.scalarCombination P c) z := by
    rw [P.productFamily_residualHelperFreqs i]
    exact hb
  let hprod := P.productFamily_residualHelperFreqs (ρ := ρ) (A := A) (q := q) i
  exact ⟨⟨_, hPos, residualHelperFreqs P (A := A) (q := q) i,
    hprod.symm ▸ hInd, K, hK,
    hprod.symm ▸ hPrefix, b, by rw [hvec]; exact hNorm⟩, rfl, hvec,
    residualHelperFreqs_injective P (A := A) (q := q) i⟩

end Scalar.Data

/-- A normalized residual product with a finite family of certified unit helper directions. -/
structure ResidualLift (ρ : Measure ℝ) [IsProbabilityMeasure ρ]
    (A : List ℚ) (q : ℚ) (u lossBudget : ℝ) where
  dim : ℕ
  count : ℕ
  count_pos : 0 < count
  weight : FiberWeight ℝ (torusHaar (ResidualCopyIndex A count × Fin dim))
  poly : MixedPoly (ResidualCopyIndex A count × Fin dim)
  eval_poly : ∀ p, evalMixedPoly poly p = (weight.weight p : ℂ)
  lower : ℝ
  lower_pos : 0 < lower
  lower_le : ∀ p, lower ≤ weight.weight p
  loss_lt : 1 - weight.mass < lossBudget
  directions : Fin count → DirectionalInput (weight.normalizedMeasure ρ)
  directional_bound : ∀ i, (directions i).K ≤ Real.sqrt ((1 + u) ^ 3)
  direction_modes_injective : ∀ i, Function.Injective (fun k ↦ ((directions i).frequencies k).2)

namespace ResidualLift

variable {ρ : Measure ℝ} [IsProbabilityMeasure ρ] {A : List ℚ} {q : ℚ} {u lossBudget : ℝ}
variable (D : ResidualLift ρ A q u lossBudget)

def helper (i : Fin D.count) : Lp ℂ 2 (D.weight.normalizedMeasure ρ) :=
  synth (productFamily _ (D.directions i).frequencies) (D.directions i).coeff

def information : Lp ℂ 2 (D.weight.normalizedMeasure ρ) →L[ℂ]
    Lp ℂ 2 (D.weight.normalizedMeasure ρ) :=
  residualInformation u D.helper

def target : Lp ℂ 2 (D.weight.normalizedMeasure ρ) :=
  D.weight.pullback ρ (rationalResidualUnit ρ A q)

end ResidualLift

structure ResidualLiftCertificate {ρ : Measure ℝ} [IsProbabilityMeasure ρ]
    {A : List ℚ} {q : ℚ} {u lossBudget : ℝ} (D : ResidualLift ρ A q u lossBudget) : Prop where
  norm_lt : ‖D.information‖ < 2 * u
  old_zero (f : Lp ℂ 2 ρ) (hf : f ∈ rationalOldSpan ρ A) :
    D.information (D.weight.pullback ρ f) = 0
  capture : u / (1 + 2 * u) ≤ Complex.re ⟪D.target, informationCapture D.information D.target⟫_ℂ

theorem exists_residualLift (ρ : Measure ℝ) [IsProbabilityMeasure ρ] [NullSingletonClass ρ]
    {A : List ℚ} (hA : A.Nodup) {q : ℚ} (hq : q ∉ A) {u lossBudget : ℝ}
    (hu : 0 < u) (hu₁ : u ≤ 1) (hBudget : 0 < lossBudget)
    (supply : ∀ z, 0 < z → z < Scalar.gainCap u / 2 → ∀ η, 0 < η →
      ∃ s : Scalar.GoodScalar u z, s.data.toData.loss < η) :
    ∃ L : ResidualLift ρ A q u lossBudget, ResidualLiftCertificate L := by
  have hρ : ρ ≠ 0 := by
    intro h
    have he : ρ Set.univ = 1 := measure_univ
    rw [h] at he
    simp at he
  have hr := rationalResidual_ne_zero ρ hρ hA hq
  obtain ⟨R⟩ := exists_rationalResidualData ρ A q
  let G := Matrix.gram ℂ (residualAugmentedFamily ρ A q)
  have hcap : 0 < Scalar.gainCap u / 2 := by
    have hh : 0 < Scalar.initialLoss u := by unfold Scalar.initialLoss; positivity
    linarith [(Scalar.gainCap_bounds hu hu₁).1, sq_pos_of_pos hh]
  obtain ⟨z, hz, hzcap, hzg⟩ := exists_residual_gain hu hcap (norm_nonneg _ :
    0 ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin (A.length + 1)) G‖)
  let a := residualCopyParameter ‖rationalResidual ρ A q‖ z R.coefficientEnergy
  obtain ⟨ha, ha₁⟩ := residualCopyParameter_bounds (norm_pos_iff.mpr hr) hz
    (zero_lt_one.trans_le R.coefficientEnergy_ge_one)
  let N := residualCopyCount a
  have hNdata : 0 < N ∧ 1 ≤ (N : ℝ) * a ^ 2 ∧ ((N : ℝ) - 1) * a ^ 2 < 1 :=
    residualCopyCount_bounds ha
  have hden : 0 < (N : ℝ) * (A.length + 1 : ℝ) := by
    exact mul_pos (by exact_mod_cast hNdata.1) (by positivity)
  let η := lossBudget / ((N : ℝ) * (A.length + 1 : ℝ))
  obtain ⟨s, hs⟩ := supply z hz hzcap η (div_pos hBudget hden)
  let P := s.data.toData
  let ι := ResidualCopyIndex A N
  let W := P.copiesFiberWeight ι
  obtain ⟨c, hcMean, hcVar⟩ := P.exists_packetFunction_mean_one_variance hz s.gain_eq
  let g := PacketRep.scalarCombination P c
  have hg : g.mean P = 1 := hcMean
  have hvar : (∫ y, ‖g.subConst 1 y‖ ^ 2 ∂P.normalizedMeasure) = 1 / z := hcVar
  have hNorm (i : Fin N) : ‖residualHelperDirection P R i g z‖ = 1 :=
    residualHelperDirection_norm P R hz hr i hg hvar
  have hGain :
      P.gain * opNorm (Matrix.gram ℂ (residualAugmentedFamily ρ A q)) ≤ u :=
    (show z * opNorm G < u from hzg).le.trans_eq (by rfl) |> fun h ↦ s.gain_eq.symm ▸ h
  have hBound : Real.sqrt (1 + u) * Scalar.commonBound u ≤ Real.sqrt ((1 + u) ^ 3) := by
    calc
      _ ≤ Real.sqrt (1 + u) * (1 + u) :=
        mul_le_mul_of_nonneg_left (Scalar.commonBound_lt_one_add hu).le (Real.sqrt_nonneg _)
      _ = _ := by
        rw [show (1 + u) ^ 3 = (1 + u) * (1 + u) ^ 2 by ring,
          Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  have hPrefix (i : Fin N) :
      HPrefix (𝕜 := ℂ) (residualHelperFamily P (ρ := ρ) (A := A) (q := q) i)
        (Real.sqrt ((1 + u) ^ 3)) :=
    (residualHelperFamily_hPrefix P i s.centered_hPrefix hGain).mono hBound
  choose V hVBound hVVector hVMode using fun i : Fin N ↦
    P.exists_residual_directionalInput R hr i c (hNorm i) (hPrefix i)
  have hMass : 1 - W.mass < lossBudget := by
    refine (P.copiesFiberWeight_loss_le ι).trans_lt ?_
    have hCard : (Fintype.card ι : ℝ) = (N : ℝ) * (A.length + 1 : ℝ) := by
      simp [ι, ResidualCopyIndex]
    rw [hCard, mul_comm]
    have h := (lt_div_iff₀ hden).mp hs
    exact h
  let L : ResidualLift ρ A q u lossBudget :=
    ⟨s.dim, N, hNdata.1, W, s.data.copiesPolynomial ι, s.data.eval_copiesPolynomial ι,
      P.lower ^ Fintype.card ι, pow_pos P.lower_pos _, P.copiesFiberWeight_lower ι, hMass, V,
      (fun i ↦ (hVBound i).le), hVMode⟩
  have hV (i : Fin L.count) : L.helper i = residualHelperDirection P R i g z :=
    hVVector i
  have hVNorm (i : Fin L.count) : ‖L.helper i‖ = 1 := (congrArg norm (hV i)).trans (hNorm i)
  have hVPairs (i j : Fin L.count) (hij : i ≠ j) :
      ⟪L.helper i, L.helper j⟫_ℂ = (a ^ 2 : ℝ) := by
    rw [hV i, hV j]
    exact residualHelperDirection_pairwise P R hr hij hg
  refine ⟨L, ⟨?_, ?_, ?_⟩⟩
  · exact norm_residualInformation_lt_two_mul hu ha.le ha₁.le L.helper hVNorm hVPairs hNdata.2.2
  · intro f hf
    apply residualInformation_eq_zero_of_orthogonal
    intro i
    rw [hV i]
    change ⟪residualHelperDirection P R i g z, W.pullback ρ f⟫_ℂ = 0
    rw [inner_residualHelperDirection_pullback P R i hg f,
      (Submodule.mem_orthogonal' _ _).mp (rationalResidualUnit_orthogonal A q) f hf, mul_zero]
  · apply residualInformation_capture_lower hu ha L.helper hVNorm hVPairs hNdata.2.2 hNdata.2.1
    intro i
    rw [hV i]
    change ⟪residualHelperDirection P R i g z, W.pullback ρ (rationalResidualUnit ρ A q)⟫_ℂ = _
    rw [inner_residualHelperDirection_pullback P R i hg, inner_self_eq_norm_sq_to_K,
      norm_rationalResidualUnit hr]
    simp

end SchauderBasisOrbits

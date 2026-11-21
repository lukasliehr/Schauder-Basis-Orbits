import LeanCode.Construction.ProductPackets

open MeasureTheory Filter
open scoped BigOperators InnerProductSpace

noncomputable section

namespace SchauderBasisOrbits

private theorem selectedPrefixSq_add_lt_product {u Kv η : ℝ} (hu : 0 < u) (huSmall : u ≤ 1 / 100)
    (hKv : 1 ≤ Kv) (hKv' : Kv ≤ Real.sqrt ((1 + u) ^ 3))
    (hη : η < (14 - (Real.sqrt 3 + 2) ^ 2) * u) :
    selectedPrefixSq (1 + u) Kv 0 + η < 1 + 14 * u := by
  have hsq : Kv ^ 2 ≤ (1 + u) ^ 3 := by
    have h := (sq_le_sq₀ (zero_le_one.trans hKv) (Real.sqrt_nonneg _)).mpr hKv'
    rwa [Real.sq_sqrt (by positivity)] at h
  have hA : (1 + u) ^ 2 - 1 ≤ 3 * u := by
    nlinarith [mul_le_mul_of_nonneg_left huSmall hu.le]
  have hB : Kv ^ 2 - 1 ≤ 4 * u := by
    have hsmall := mul_le_mul_of_nonneg_left huSmall hu.le
    have hsmall' := mul_le_mul_of_nonneg_left huSmall (sq_nonneg u)
    nlinarith only [hsq, hsmall, hsmall', hu.le]
  have hAs := Real.sqrt_le_sqrt hA
  have hBs := Real.sqrt_le_sqrt hB
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3)] at hAs
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4), show Real.sqrt 4 = 2 by
    calc
      Real.sqrt 4 = Real.sqrt ((2 : ℝ) ^ 2) := by norm_num
      _ = _ := Real.sqrt_sq (by norm_num)] at hBs
  have hsum :
      Real.sqrt ((1 + u) ^ 2 - 1) + Real.sqrt (Kv ^ 2 - 1) ≤ (Real.sqrt 3 + 2) * Real.sqrt u := by
    rw [add_mul]
    exact add_le_add hAs hBs
  have hss := (sq_le_sq₀ (by positivity) (by positivity)).mpr hsum
  rw [mul_pow, Real.sq_sqrt hu.le] at hss
  unfold selectedPrefixSq
  simp only [mul_zero, add_zero, one_mul]
  nlinarith only [hss, hη]

namespace ProductPackets

variable {ρ : Measure ℝ} [IsProbabilityMeasure ρ] {A : List ℚ} {q : ℚ} {u lossBudget η : ℝ}
variable {R : ResidualLift ρ A q u lossBudget} (P : ProductPackets R η)

theorem centered_pb (hu : 0 < u) (huSmall : u ≤ 1 / 100)
    (hη : η < (14 - (Real.sqrt 3 + 2) ^ 2) * u) :
    PB (flatSynthesis P).centeredGram (Real.sqrt (1 + 14 * u)) := by
  rw [flatSynthesis, CenteredSynthesis.mapTarget_centeredGram]
  apply FiberFamily.combine_centered_pb _ _ _ _ (Real.sqrt_nonneg _)
  intro i
  rw [rawFamilies_synthesis]
  have h := (P i).centered_pb
  have hlt := selectedPrefixSq_add_lt_product hu huSmall (R.directions i).K_ge_one
    (R.directional_bound i) hη
  have hK := Real.sqrt_le_sqrt hlt.le
  unfold CenteredSynthesis.centeredGram at h ⊢
  rw [← rawFamilies_synthesis, FiberFamily.synthesis_centered, clmGram_synthCLM_eq_gram,
    ← hPrefix_iff_pb]
  rw [← rawFamilies_synthesis, FiberFamily.synthesis_centered, clmGram_synthCLM_eq_gram,
    ← hPrefix_iff_pb] at h
  exact h.mono hK

theorem loss_lt_of_budget_add {δ : ℝ} (h : lossBudget + (R.count : ℝ) * η ≤ δ) :
    1 - (flatWeight P).mass < δ := by
  have hW : ∑ i, (1 - (P i).W.mass) ≤ (R.count : ℝ) * η := by
    calc
      _ ≤ ∑ _i : Fin R.count, η := Finset.sum_le_sum (fun i _ ↦ by linarith [(P i).mass_gt])
      _ = _ := by simp [nsmul_eq_mul]
  refine (flatWeight_loss_le P).trans_lt ?_
  linarith [R.loss_lt]

end ProductPackets

/-- Assemble a product extension from the scalar and directional supplies. -/
theorem normalizedProductExtension_of_supplies {ρ : Measure ℝ} [IsProbabilityMeasure ρ]
    [NullSingletonClass ρ]
    (scalarSupply : ∀ δ, 0 < δ → δ ≤ 1 → ∀ z, 0 < z → z < Scalar.gainCap δ / 2 →
      ∀ η, 0 < η → ∃ s : Scalar.GoodScalar δ z, s.data.toData.loss < η)
    (directionalSupply : ∀ (ι : Type) [Fintype ι]
      (m : Measure (ℝ × UnitAddTorus ι)) [IsProbabilityMeasure m], DirectionalSupply m) :
    NormalizedProductExtensionSupply ρ := by
  intro u hu huSmall A q K δ τ _ hA hq hδ hτ hK
  obtain ⟨R, hR⟩ := exists_residualLift ρ hA hq hu (huSmall.trans (by norm_num))
    (show 0 < δ / 2 by positivity) (scalarSupply u hu (huSmall.trans (by norm_num)))
  let K₀ := max K (linePrefixFloor u)
  have hK₀ : 0 < K₀ := by
    exact (show 0 < linePrefixFloor u by unfold linePrefixFloor; positivity).trans_le (le_max_right _ _)
  obtain ⟨η, hη, hηu, hηCap, hηMass, hηAngle, hηSmall⟩ :=
    exists_product_tolerance R.count_pos hK₀ hτ hδ hu
  have hExists (i : Fin R.count) : Nonempty (DirectionalOutput (R.directions i) (1 + u) u η) :=
    directionalSupply R.Coordinates (R.weight.normalizedMeasure ρ) (R.directions i) (1 + u) u η
      (by linarith) hu hη
  let P : ProductPackets R η := fun i ↦ Classical.choice (hExists i)
  have hnonneg : 0 ≤ (R.count : ℝ) * η := by positivity
  have hAngleBounds := angleLimit_bounds hK₀ hτ
  have hAngle := (sq_lt_sq₀ (Real.sqrt_nonneg ((R.count : ℝ) * η)) hAngleBounds.1.le).mp
    ((Real.sq_sqrt hnonneg).trans_lt hηAngle)
  have hAngle₁ := hAngle.trans hAngleBounds.2
  have hSlack := angleLimit_slack hK₀ hτ (Real.sqrt_nonneg ((R.count : ℝ) * η)) hAngle
  let S : ProductSelection R K δ τ :=
    ⟨P.dim, ∑ i, (P i).n, P.size_pos, P.freq, P.freq_aux_nonzero, P.freq_aux_injective,
      P.graphWeight, P.flatWeight, rfl, P.loss_lt_of_budget_add (by linarith [hηMass]),
      P.flatSynthesis, P.flatSynthesis_full, P.flatSynthesis_lift_base,
      P.flat_centered_injective, P.centered_pb hu huSmall hηSmall,
      (R.count : ℝ) * η, hηu, hηCap, P.information_error, hAngle₁, hSlack⟩
  exact assemble_normalizedProductLineData hA hq hu hK R hR S

end SchauderBasisOrbits

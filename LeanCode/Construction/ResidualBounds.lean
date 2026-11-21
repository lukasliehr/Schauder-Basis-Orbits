import LeanCode.Construction.ResidualHelpers
import LeanCode.Scalar.SupplyContract

open Matrix MeasureTheory Filter ContinuousLinearMap Complex
open scoped BigOperators InnerProductSpace ComplexConjugate

noncomputable section

namespace SchauderBasisOrbits

local postfix:1024 "†" => ContinuousLinearMap.adjoint

namespace Scalar.Data

variable {r n : ℕ} (P : Data r n)

def centerCharRep (k : Fin n) : PacketRep r :=
  (PacketRep.char (P.mode k)).subConst (P.normalizedMean k : ℂ)

theorem centerCharRep_mean_zero (k : Fin n) : (P.centerCharRep k).mean P = 0 := by
  rw [centerCharRep, packetRep_mean_subConst]
  change (∫ y, torusChar (P.mode k) y ∂P.normalizedMeasure) - (P.normalizedMean k : ℂ) = 0
  rw [integral_torusChar_normalized, sub_self]

theorem inner_copyTensor_centerCharRep {ι : Type*} [Fintype ι] (ρ : Measure ℝ)
    [IsProbabilityMeasure ρ] (i : ι) (t : ℝ) (j k : Fin n) :
    ⟪P.copyTensor ρ i t (P.centerCharRep j), P.copyTensor ρ i t (P.centerCharRep k)⟫_ℂ =
      ⟪P.centerLp j, P.centerLp k⟫_ℂ := by
  rw [P.inner_copyTensor_same_probability, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [P.ae_centerLp j, P.ae_centerLp k] with y hj hk
  rw [hj, hk, RCLike.inner_apply']
  rfl

end Scalar.Data

variable {ρ : Measure ℝ} [IsProbabilityMeasure ρ] {A : List ℚ} {q : ℚ}
variable {r n N : ℕ} (P : Scalar.Data r n)

def residualCenteredBlock (i : Fin N) (j : Fin (A.length + 1)) :
    Fin n → ResidualHelperSpace P ρ A N :=
  fun k ↦ P.copyTensor ρ (i, j) (residualFrequencies A q j : ℝ) (P.centerCharRep k)

def residualMeanBlock (j : Fin (A.length + 1)) : Fin n → Lp ℂ 2 ρ :=
  fun k ↦ (P.normalizedMean k : ℂ) • residualAugmentedFamily ρ A q j

theorem residualCenteredBlock_gram (i : Fin N) (j : Fin (A.length + 1)) :
    Matrix.gram ℂ (residualCenteredBlock P (ρ := ρ) (A := A) (q := q) i j) =
      Matrix.gram ℂ P.centerLp := by
  ext k l
  rw [Matrix.gram_apply, Matrix.gram_apply]
  exact P.inner_copyTensor_centerCharRep ρ (i, j) (residualFrequencies A q j : ℝ) k l

theorem residualCenteredBlock_orthogonal (i : Fin N) {j l : Fin (A.length + 1)} (h : j ≠ l)
    (k s : Fin n) :
    ⟪residualCenteredBlock P (ρ := ρ) (A := A) (q := q) i j k,
      residualCenteredBlock P (ρ := ρ) (A := A) (q := q) i l s⟫_ℂ = 0 :=
  P.inner_copyTensor_eq_zero_of_ne ρ (fun h' ↦ h (congrArg Prod.snd h')) _ _ _ _
    (Or.inl (P.centerCharRep_mean_zero k))

def residualHelperSynthesis (i : Fin N) :
    CenteredSynthesis (Lp ℂ 2 ρ) (ResidualHelperSpace P ρ A N) ((A.length + 1) * n) where
  pullback := (P.copiesFiberWeight (ResidualCopyIndex A N)).pullback ρ
  centered := synthCLM (orderedBlocks (residualCenteredBlock P (q := q) i))
  means := synthCLM (orderedBlocks (residualMeanBlock P (ρ := ρ) (q := q)))
  inner_eq_zero f c := by
    rw [synthCLM_apply, synth_orderedBlocks, inner_sum]
    apply Finset.sum_eq_zero
    intro j _
    rw [synth, inner_sum]
    apply Finset.sum_eq_zero
    intro k _
    rw [inner_smul_right, residualCenteredBlock, P.inner_pullback_copyTensor_eq_zero ρ _ _ _
      (P.centerCharRep_mean_zero k), mul_zero]

theorem residualHelperSynthesis_full (i : Fin N) :
    (residualHelperSynthesis P (ρ := ρ) (A := A) (q := q) i).full =
      synthCLM (residualHelperFamily P (ρ := ρ) (q := q) i) := by
  apply ContinuousLinearMap.ext
  intro c
  rw [CenteredSynthesis.full_apply]
  simp only [residualHelperSynthesis, synthCLM_apply, synth_orderedBlocks, residualHelperFamily,
    map_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  simp only [synth, map_sum, map_smul, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  rw [← smul_add, residualCenteredBlock, residualMeanBlock, map_smul, residualAugmentedFamily,
    Scalar.Data.centerCharRep, ← P.copyTensor_decompose]

theorem residualHelperSynthesis_centered_injective (i : Fin N) :
    Function.Injective (residualHelperSynthesis P (ρ := ρ) (A := A) (q := q) i).centered := by
  have hli : ∀ j, LinearIndependent ℂ (residualCenteredBlock P (ρ := ρ) (A := A) (q := q) i j) := by
    intro j
    apply Matrix.posDef_gram_iff_linearIndependent.mp
    rw [residualCenteredBlock_gram]
    exact Matrix.posDef_gram_iff_linearIndependent.mpr P.centerLp_linearIndependent
  have hLI := linearIndependent_orderedBlocks _
    (fun j l h ↦ residualCenteredBlock_orthogonal P (ρ := ρ) (A := A) (q := q) i h) hli
  change Function.Injective (synthCLM (𝕜 := ℂ) _)
  intro c d h
  rw [synthCLM_apply, synthCLM_apply] at h
  apply WithLp.ofLp_injective
  exact funext fun k ↦ hLI.eq_coords_of_eq h k

theorem residualHelperSynthesis_centered_pb (i : Fin N) {K : ℝ}
    (h : HPrefix (𝕜 := ℂ) P.centerLp K) :
    PB (residualHelperSynthesis P (ρ := ρ) (A := A) (q := q) i).centeredGram K := by
  change PB (clmGram (synthCLM _)) K
  rw [clmGram_synthCLM_eq_gram, ← hPrefix_iff_pb]
  apply hPrefix_orderedBlocks _ h.1
  · intro j l hn
    exact residualCenteredBlock_orthogonal P (ρ := ρ) (q := q) i hn
  · intro j
    rw [hPrefix_iff_pb, residualCenteredBlock_gram, ← hPrefix_iff_pb]
    exact h

theorem residualHelperSynthesis_information_eq (i : Fin N) :
    (residualHelperSynthesis P (ρ := ρ) (A := A) (q := q) i).information =
      residualInformation P.gain (residualAugmentedFamily ρ A q) := by
  let S := residualHelperSynthesis P (ρ := ρ) (A := A) (q := q) i
  let C := P.normalizedGram
  let a := P.normalizedMean
  let b := C⁻¹ *ᵥ a
  have hb : C *ᵥ b = a := by
    dsimp only [b]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _
      ((Matrix.isUnit_iff_isUnit_det _).mp P.normalizedGram_posDef.isUnit), Matrix.one_mulVec]
  let φ := residualAugmentedFamily ρ A q
  apply ContinuousLinearMap.ext
  intro x
  let t := fun j ↦ ⟪φ j, x⟫_ℂ
  let c : EuclideanSpace ℂ (Fin ((A.length + 1) * n)) :=
    WithLp.toLp 2 (orderedBlocks (fun j k ↦ (b k : ℂ) * t j))
  have hc (j : Fin (A.length + 1)) (k : Fin n) :
      c (finProdFinEquiv (j, k)) = (b k : ℂ) * t j :=
    orderedBlocks_apply (fun j k ↦ (b k : ℂ) * t j) j k
  have hc_eq : (S.centered†) (S.centered c) = (S.means†) x := by
    apply WithLp.ofLp_injective
    funext l
    obtain ⟨⟨j, k⟩, rfl⟩ := finProdFinEquiv.surjective l
    change ((synthCLM (𝕜 := ℂ) (orderedBlocks (residualCenteredBlock P (q := q) i)))†
        (synthCLM (orderedBlocks (residualCenteredBlock P (q := q) i)) c))
        (finProdFinEquiv (j, k)) =
      ((synthCLM (𝕜 := ℂ) (orderedBlocks (residualMeanBlock P (ρ := ρ) (q := q))))† x)
        (finProdFinEquiv (j, k))
    rw [synthCLM_adjoint_coordinate, synthCLM_adjoint_coordinate, orderedBlocks_apply,
      orderedBlocks_apply, synthCLM_apply, synth_orderedBlocks, inner_sum]
    rw [Finset.sum_eq_single j]
    · rw [synth, inner_sum, residualMeanBlock, inner_smul_left, Complex.conj_ofReal]
      simp_rw [inner_smul_right, hc]
      have hinner (l : Fin n) :
          ⟪residualCenteredBlock P (ρ := ρ) (q := q) i j k,
            residualCenteredBlock P (ρ := ρ) (q := q) i j l⟫_ℂ = (C k l : ℂ) := by
        rw [← Matrix.gram_apply, residualCenteredBlock_gram, P.gram_centerLp, complexify_apply]
      simp_rw [hinner]
      have hh : (∑ l, (b l : ℂ) * t j * (C k l : ℂ)) =
          (((C *ᵥ b) k : ℝ) : ℂ) * t j := by
        simp only [Matrix.mulVec, dotProduct, Complex.ofReal_sum, Complex.ofReal_mul, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro l _
        ring
      rw [hh, hb]
    · intro l _ hlj
      rw [synth, inner_sum]
      apply Finset.sum_eq_zero
      intro h _
      rw [inner_smul_right, residualCenteredBlock_orthogonal P i (Ne.symm hlj), mul_zero]
    · simp
  have hcinv : S.centeredInverse ((S.means†) x) = c :=
    (congrArg S.centeredInverse hc_eq).symm.trans
      (S.centeredInverse_left (residualHelperSynthesis_centered_injective P i) c)
  change S.information x = _
  rw [CenteredSynthesis.information_apply, hcinv, residualInformation_apply]
  change synthCLM (orderedBlocks (residualMeanBlock P (ρ := ρ) (q := q))) c =
    P.gain • ∑ j, t j • φ j
  rw [synthCLM_apply, synth_orderedBlocks, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [synth, hc, residualMeanBlock, smul_smul]
  rw [← Finset.sum_smul]
  have hcoef : (∑ l, (b l : ℂ) * t j * (a l : ℂ)) =
      (P.gain : ℂ) * t j := by
    change (∑ l, (b l : ℂ) * t j * (a l : ℂ)) = (↑(a ⬝ᵥ b) : ℂ) * t j
    rw [dotProduct, Complex.ofReal_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro l _
    push_cast
    ring
  rw [hcoef]
  change _ = (P.gain : ℂ) • t j • residualAugmentedFamily ρ A q j
  rw [smul_smul]

theorem norm_residualHelperSynthesis_information (i : Fin N) :
    ‖(residualHelperSynthesis P (ρ := ρ) (A := A) (q := q) i).information‖ =
      P.gain * opNorm (Matrix.gram ℂ (residualAugmentedFamily ρ A q)) := by
  rw [residualHelperSynthesis_information_eq, residualInformation]
  let X := synthCLM (𝕜 := ℂ) (residualAugmentedFamily ρ A q)
  change ‖(P.gain : ℂ) • (X ∘L X†)‖ = _
  rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg P.gain_nonneg,
    norm_comp_adjoint_eq_norm_adjoint_comp]
  congr 1
  change ‖(synthCLM _ : _ →L[ℂ] Lp ℂ 2 ρ)† ∘L synthCLM _‖ = _
  rw [← toEuclideanCLM_clmGram, opNorm_square_eq, clmGram_synthCLM_eq_gram]

theorem residualHelperFamily_hPrefix (i : Fin N) {K u : ℝ}
    (hC : HPrefix (𝕜 := ℂ) P.centerLp K)
    (hgain : P.gain * opNorm (Matrix.gram ℂ (residualAugmentedFamily ρ A q)) ≤ u) :
    HPrefix (𝕜 := ℂ) (residualHelperFamily P (ρ := ρ) (A := A) (q := q) i)
      (Real.sqrt (1 + u) * K) := by
  let S := residualHelperSynthesis P (ρ := ρ) (A := A) (q := q) i
  have hu : ‖S.information‖ ≤ u := (norm_residualHelperSynthesis_information P i).le.trans hgain
  have hpb := S.fullGram_prefix (residualHelperSynthesis_centered_injective P i) hu
    (residualHelperSynthesis_centered_pb P i hC)
  unfold CenteredSynthesis.fullGram at hpb
  rw [show S.full = _ from residualHelperSynthesis_full P i, clmGram_synthCLM_eq_gram] at hpb
  exact (hPrefix_iff_pb _ _).mpr hpb

end SchauderBasisOrbits

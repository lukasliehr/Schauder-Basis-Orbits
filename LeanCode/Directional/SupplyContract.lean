module

public import LeanCode.Directional.Seed
public import LeanCode.Directional.Amplification
public import LeanCode.Measure.Information

@[expose] public section

open Function MeasureTheory Submodule
open scoped ENNReal

namespace SchauderBasisOrbits

noncomputable section

variable {ι : Type*} [Fintype ι] {r : ℕ}

/-- Evaluation on a base and a fresh auxiliary block, using disjoint coordinates. -/
def directionalRaw (k : MixedFreq (ι ⊕ Fin r))
    (p : (ℝ × UnitAddTorus ι) × UnitAddTorus (Fin r)) : ℂ :=
  mixedChar k (p.1.1, Sum.elim p.1.2 p.2)

theorem measurable_directionalRaw (k : MixedFreq (ι ⊕ Fin r)) :
    Measurable (directionalRaw k) := by
  apply (continuous_mixedChar k).measurable.comp
  apply measurable_fst.fst.prodMk
  apply measurable_pi_lambda
  intro i
  cases i with
  | inl i => exact (measurable_pi_apply i).comp measurable_fst.snd
  | inr i => exact (measurable_pi_apply i).comp measurable_snd

theorem norm_directionalRaw (k : MixedFreq (ι ⊕ Fin r))
    (p : (ℝ × UnitAddTorus ι) × UnitAddTorus (Fin r)) :
    ‖directionalRaw k p‖ = 1 := norm_mixedChar _ _

def directionalSynthesis (ρ : Measure (ℝ × UnitAddTorus ι)) [IsFiniteMeasure ρ]
    (W : FiberWeight (ℝ × UnitAddTorus ι) (torusHaar (Fin r)))
    {n : ℕ} (freq : Fin n → MixedFreq (ι ⊕ Fin r)) :
    CenteredSynthesis (Lp ℂ 2 ρ) (Lp ℂ 2 (W.normalizedMeasure ρ)) n :=
  W.synthesis ρ (fun i => directionalRaw (freq i)) (fun i => measurable_directionalRaw _)
    (fun _ => 1) (fun i p => (norm_directionalRaw (freq i) p).le)

/-- The common data of a selected family and of its amplified copies. -/
structure DirectionalFamily {ρ : Measure (ℝ × UnitAddTorus ι)} [IsFiniteMeasure ρ]
    (D : DirectionalInput ρ) where
  r : ℕ
  n : ℕ
  nonempty_family : 0 < n
  W : FiberWeight (ℝ × UnitAddTorus ι) (torusHaar (Fin r))
  lower : ℝ
  lower_pos : 0 < lower
  lower_le : ∀ p, lower ≤ W.weight p
  poly : MixedPoly (ι ⊕ Fin r)
  eval_poly : ∀ p, evalMixedPoly poly (p.1.1, Sum.elim p.1.2 p.2) = (W.weight p : ℂ)
  freq : Fin n → MixedFreq (ι ⊕ Fin r)
  fresh_ne_zero : ∀ i, (fun k => (freq i).2 (Sum.inr k)) ≠ 0
  aux_injective : Injective (fun i => (D.frequencies i).2) → Injective (fun i => (freq i).2)
  real_frequency : ∀ i, (freq i).1 = 0 ∨ ∃ j, (freq i).1 = (D.frequencies j).1
  means_range : (directionalSynthesis ρ W freq).means.toLinearMap.range ≤
    span ℂ (Set.range (productFamily ρ D.frequencies))
  centered_injective : Injective (directionalSynthesis ρ W freq).centered

/-- The selected family before amplification, with its rank-one information
and a bounded leakage term. -/
structure SelectedPacket {ρ : Measure (ℝ × UnitAddTorus ι)} [IsFiniteMeasure ρ]
    (D : DirectionalInput ρ) (Ks ε : ℝ) extends DirectionalFamily D where
  gain : ℝ
  gain_pos : 0 < gain
  leak : ℝ
  leak_nonneg : 0 ≤ leak
  leakOp : Lp ℂ 2 ρ →L[ℂ] Lp ℂ 2 ρ
  leakOp_norm : ‖leakOp‖ ≤ 1
  centered_pb : PB (directionalSynthesis ρ W freq).centeredGram
    (Real.sqrt (selectedPrefixSq Ks D.K ε))
  information_eq :
    (directionalSynthesis ρ W freq).information =
      gain • InnerProductSpace.rankOne ℂ (synth (productFamily ρ D.frequencies) D.coeff)
        (synth (productFamily ρ D.frequencies) D.coeff) + leak • leakOp

/-- Certified output of directional selection and amplification on a fixed base. -/
structure DirectionalOutput {ρ : Measure (ℝ × UnitAddTorus ι)} [IsFiniteMeasure ρ]
    (D : DirectionalInput ρ) (Ks σ η : ℝ) extends DirectionalFamily D where
  mass_gt : 1 - η < W.mass
  centered_pb : PB (directionalSynthesis ρ W freq).centeredGram
    (Real.sqrt (selectedPrefixSq Ks D.K 0 + η))
  information_error :
    ‖(directionalSynthesis ρ W freq).information -
      σ • InnerProductSpace.rankOne ℂ (synth (productFamily ρ D.frequencies) D.coeff)
        (synth (productFamily ρ D.frequencies) D.coeff)‖ < η

/-- The directional extension property on the base probability ρ. -/
def DirectionalSupply (ρ : Measure (ℝ × UnitAddTorus ι)) [IsProbabilityMeasure ρ] : Prop :=
  ∀ (D : DirectionalInput ρ) (Ks σ η : ℝ), 1 < Ks → 0 < σ → 0 < η →
    Nonempty (DirectionalOutput D Ks σ η)

end

end SchauderBasisOrbits

import LeanCode.Basis.Criterion
import LeanCode.Construction.LineFamilies
import LeanCode.Construction.LimitWeights
import LeanCode.Construction.Schedule
import Mathlib

open Filter Function MeasureTheory Submodule
open scoped ENNReal Topology BigOperators

namespace SchauderBasisOrbits
noncomputable section

def linePrefixFloor (u : ℝ) : ℝ := 1 + 10 * u

def lineContraction (u : ℝ) : ℝ := 1 - (u / (1 + 2 * u)) / 4

theorem lineContraction_bounds {u : ℝ} (hu : 0 < u) :
    0 < lineContraction u ∧ lineContraction u < 1 := by
  have hden : 0 < 1 + 2 * u := by positivity
  have hlow : 0 < u / (1 + 2 * u) := div_pos hu hden
  have hupp : u / (1 + 2 * u) < 1 := (div_lt_iff₀ hden).mpr (by linarith)
  unfold lineContraction
  constructor <;> linarith

def stageU (ε : ℝ) : ℝ := min 1 ε / 100

theorem stageU_bounds {ε : ℝ} (hε : 0 < ε) :
    0 < stageU ε ∧ stageU ε ≤ 1 / 100 ∧ 10 * stageU ε < ε := by
  unfold stageU
  have hp : 0 < min 1 ε := lt_min (by norm_num) hε
  have h₁ : min (1 : ℝ) ε ≤ 1 := min_le_left ..
  have hε' : min (1 : ℝ) ε ≤ ε := min_le_right ..
  refine ⟨by positivity, by linarith, by linarith⟩

def stageLoss (n : ℕ) : ℝ := ((1 : ℝ) / 2) ^ (n + 1)

def stageSlack (ε : ℝ) (n : ℕ) : ℝ := (ε - 10 * stageU ε) / 4 * ((1 : ℝ) / 2) ^ n

def stagePrefixBound (ε : ℝ) (n : ℕ) : ℝ :=
  linePrefixFloor (stageU ε) + ∑ j ∈ Finset.range n, stageSlack ε j

theorem stageLoss_pos (n : ℕ) : 0 < stageLoss n := by unfold stageLoss; positivity

theorem summable_stageLoss : Summable stageLoss := by
  convert summable_geometric_two.mul_left (1 / 2) using 1
  funext n
  exact (pow_succ _ _).trans (mul_comm _ _)

theorem stageSlack_pos {ε : ℝ} (hε : 0 < ε) (n : ℕ) : 0 < stageSlack ε n := by
  have := sub_pos.mpr (stageU_bounds hε).2.2
  unfold stageSlack
  positivity

theorem linePrefixFloor_le_stage {ε : ℝ} (hε : 0 < ε) (n : ℕ) :
    linePrefixFloor (stageU ε) ≤ stagePrefixBound ε n :=
  le_add_of_nonneg_right (Finset.sum_nonneg fun j _ => (stageSlack_pos hε j).le)

theorem stagePrefixBound_succ (ε : ℝ) (n : ℕ) :
    stagePrefixBound ε (n + 1) = stagePrefixBound ε n + stageSlack ε n := by
  simp [stagePrefixBound, Finset.sum_range_succ, add_assoc]

theorem stagePrefixBound_le {ε : ℝ} (hε : 0 < ε) (n : ℕ) : stagePrefixBound ε n ≤ 1 + ε := by
  have hsum : HasSum (stageSlack ε) ((ε - 10 * stageU ε) / 4 * 2) :=
    hasSum_geometric_two.mul_left _
  have hle := hsum.summable.sum_le_tsum (Finset.range n) (fun j _ => (stageSlack_pos hε j).le)
  rw [hsum.tsum_eq] at hle
  unfold stagePrefixBound linePrefixFloor
  linarith [(stageU_bounds hε).2.2]

/-- Output of one finite line extension. The appended block is strictly nonempty. -/
structure LineStepData (μ : Measure ℝ) [IsFiniteMeasure μ] (u : ℝ)
    (v : LineWeight) (a : List ℚ) (q : ℚ) (K δ τ : ℝ) where
  V : LineWeight
  aNext : List ℚ
  nodup : aNext.Nodup
  prefix_le : a <+: aNext
  length_lt : a.length < aNext.length
  loss_lt : (∫ x, 1 - V x ∂μ) < δ
  prefix_bound : HPrefix (𝕜 := ℂ) (realFamily ((v.mul V).measure μ) aNext)
    (max K (linePrefixFloor u) + τ)
  contraction : lineDistanceSq μ (v.mul V) aNext q ≤
    lineContraction u * lineDistanceSq μ v a q

/-- The finite line extension proposition used at each non-skipped stage. -/
def LineExtensionSupply (μ : Measure ℝ) [IsFiniteMeasure μ] : Prop :=
  ∀ (u : ℝ), 0 < u → u ≤ 1 / 100 → ∀ (v : LineWeight) (a : List ℚ) (q : ℚ) (K δ τ : ℝ),
    a ≠ [] → a.Nodup → q ∉ a → 0 < δ → 0 < τ →
    HPrefix (𝕜 := ℂ) (realFamily (v.measure μ) a) K →
    Nonempty (LineStepData μ u v a q K δ τ)

structure ExtensionState (μ : Measure ℝ) [IsFiniteMeasure μ] (ε : ℝ) (n : ℕ) where
  v : LineWeight
  a : List ℚ
  nonempty_a : a ≠ []
  nodup : a.Nodup
  prefix_bound : HPrefix (𝕜 := ℂ) (realFamily (v.measure μ) a) (stagePrefixBound ε n)

structure ExtensionSuccessor {μ : Measure ℝ} [IsFiniteMeasure μ] {ε : ℝ} {n : ℕ}
    (s : ExtensionState μ ε n) where
  next : ExtensionState μ ε (n + 1)
  V : LineWeight
  next_eq : next.v = s.v.mul V
  prefix_le : s.a <+: next.a
  length_lt_if_absent : rationalSchedule n ∉ s.a → s.a.length < next.a.length
  loss_lt : (∫ x, 1 - V x ∂μ) < stageLoss n
  contraction : lineDistanceSq μ next.v next.a (rationalSchedule n) ≤
    lineContraction (stageU ε) * lineDistanceSq μ s.v s.a (rationalSchedule n)

@[simp] theorem LineWeight.mul_one (v : LineWeight) : v.mul LineWeight.one = v := by
  cases v
  simp [LineWeight.mul, LineWeight.one]

noncomputable def initialExtensionState (μ : Measure ℝ) [IsFiniteMeasure μ]
    {ε : ℝ} (hε : 0 < ε) : ExtensionState μ ε 0 where
  v := .one
  a := [0]
  nonempty_a := by simp
  nodup := by simp
  prefix_bound := by
    have hK : 1 ≤ stagePrefixBound ε 0 := by
      have h := linePrefixFloor_le_stage hε 0
      unfold linePrefixFloor at h
      linarith [(stageU_bounds hε).1]
    refine ⟨by linarith, fun k hk c => ?_⟩
    change k ≤ 1 at hk
    have hh : k = 0 ∨ k = 1 := by omega
    rcases hh with rfl | rfl
    · simp only [truncCoeff_zero, synth_zero, norm_zero]
      exact mul_nonneg (by linarith) (norm_nonneg _)
    · rw [truncCoeff_eq_self c (by simp)]
      exact le_mul_of_one_le_left (norm_nonneg _) hK

theorem extensionState_has_successor {μ : Measure ℝ} [IsFiniteMeasure μ] {ε : ℝ}
    (hε : 0 < ε) (supply : LineExtensionSupply μ) {n : ℕ} (s : ExtensionState μ ε n) :
    Nonempty (ExtensionSuccessor s) := by
  classical
  let q := rationalSchedule n
  by_cases hq : q ∈ s.a
  · have hprefix := s.prefix_bound.mono (show stagePrefixBound ε n ≤ stagePrefixBound ε (n + 1) from
      by rw [stagePrefixBound_succ]; linarith [stageSlack_pos hε n])
    refine ⟨⟨⟨s.v, s.a, s.nonempty_a, s.nodup, hprefix⟩, .one, (s.v.mul_one).symm,
      List.prefix_rfl, fun h => False.elim (h hq), ?_, ?_⟩⟩
    · simpa [LineWeight.one] using stageLoss_pos n
    · simp [lineDistanceSq_eq_zero_of_mem μ s.v hq, q]
  · obtain ⟨d⟩ := supply (stageU ε) (stageU_bounds hε).1 (stageU_bounds hε).2.1
      s.v s.a q (stagePrefixBound ε n) (stageLoss n) (stageSlack ε n)
      s.nonempty_a s.nodup hq (stageLoss_pos _) (stageSlack_pos hε _) s.prefix_bound
    refine ⟨⟨⟨s.v.mul d.V, d.aNext, ?_, d.nodup, ?_⟩, d.V, rfl,
      d.prefix_le, fun _ => d.length_lt, d.loss_lt, d.contraction⟩⟩
    · intro h
      have hlen := d.length_lt
      rw [h] at hlen
      simp at hlen
    · rw [stagePrefixBound_succ]
      simpa only [max_eq_left (linePrefixFloor_le_stage hε n)] using d.prefix_bound

/-- Recursively choose compatible states from the finite extension proposition. -/
noncomputable def extensionTrajectory {μ : Measure ℝ} [IsFiniteMeasure μ] {ε : ℝ}
    (hε : 0 < ε) (supply : LineExtensionSupply μ) : (n : ℕ) → ExtensionState μ ε n
  | 0 => initialExtensionState μ hε
  | n + 1 => (Classical.choice (extensionState_has_successor hε supply (extensionTrajectory hε supply n))).next

noncomputable def extensionTrajectoryStep {μ : Measure ℝ} [IsFiniteMeasure μ] {ε : ℝ}
    (hε : 0 < ε) (supply : LineExtensionSupply μ) (n : ℕ) :
    ExtensionSuccessor (extensionTrajectory hε supply n) :=
  Classical.choice (extensionState_has_successor hε supply _)

end

end SchauderBasisOrbits

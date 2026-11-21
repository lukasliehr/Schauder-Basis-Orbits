import LeanCode.Construction.Iteration
import LeanCode.Construction.OrderedLimit

open Filter Function MeasureTheory Submodule
open scoped ENNReal Topology BigOperators

namespace SchauderBasisOrbits

noncomputable section

variable {μ : Measure ℝ} [IsFiniteMeasure μ] {ε : ℝ}
    (hε : 0 < ε) (supply : LineExtensionSupply μ)

local notation "states" => extensionTrajectory hε supply
local notation "steps" => extensionTrajectoryStep hε supply

private theorem trajectory_prefix_succ (n : ℕ) : (states n).a <+: (states (n + 1)).a :=
  (steps n).prefix_le

theorem trajectory_prefix {n m : ℕ} (h : n ≤ m) : (states n).a <+: (states m).a := by
  induction h with
  | refl => exact List.prefix_rfl
  | step _ ih => exact ih.trans (trajectory_prefix_succ hε supply _)

theorem trajectory_unbounded (i : ℕ) : ∃ n, i < (states n).a.length := by
  induction i with
  | zero => exact ⟨0, by simp [extensionTrajectory, initialExtensionState]⟩
  | succ i ih =>
    obtain ⟨n, hn⟩ := ih
    obtain ⟨q, hq⟩ := (states n).a.finite_toSet.exists_notMem
    obtain ⟨j, hj, hvisit⟩ := exists_rationalSchedule_ge q n
    have hpre := trajectory_prefix hε supply hj
    by_cases hlen : (states n).a.length < (states j).a.length
    · exact ⟨j, by omega⟩
    have heq : (states n).a = (states j).a :=
      hpre.eq_of_length (le_antisymm hpre.length_le (by omega))
    have habs : rationalSchedule j ∉ (states j).a := by rw [hvisit, ← heq]; exact hq
    have hgrow : (states j).a.length < (states (j + 1)).a.length :=
      (steps j).length_lt_if_absent habs
    exact ⟨j + 1, (Nat.succ_le_of_lt (hn.trans_le hpre.length_le)).trans_lt hgrow⟩

private def trajectoryMultipliers (n : ℕ) (x : ℝ) : ℝ := (steps n).V x

private theorem trajectory_weight_eq (n : ℕ) (x : ℝ) :
    (states n).v x = stageWeight (trajectoryMultipliers hε supply) n x := by
  induction n with
  | zero => simp [extensionTrajectory, initialExtensionState, LineWeight.one, stageWeight]
  | succ n ih =>
    have heq : (states (n + 1)).v = (states n).v.mul (steps n).V := (steps n).next_eq
    rw [heq, stageWeight, Finset.prod_range_succ]
    change (states n).v x * (steps n).V x = stageWeight (trajectoryMultipliers hε supply) n x * (steps n).V x
    rw [ih]

/-- Positive representative of the limiting weight of the constructed states. -/
def trajectoryLimitWeight : LineWeight :=
  ⟨positiveLimitWeight (trajectoryMultipliers hε supply),
    measurable_positiveLimitWeight (fun n => (steps n).V.measurable_toFun),
    fun x => (positiveLimitWeight_bounds (fun n x => (steps n).V.positive x) x).1,
    fun x => (positiveLimitWeight_bounds (fun n x => (steps n).V.positive x) x).2⟩

private theorem ae_trajectoryProduct_pos :
    ∀ᵐ x ∂μ, 0 < limitWeight (trajectoryMultipliers hε supply) x :=
  ae_limitWeight_pos μ (fun n => (steps n).V.measurable_toFun) (fun n => (steps n).V.positive)
    (fun n => (steps n).V.le_one) summable_stageLoss (fun n => (steps n).loss_lt.le)

private theorem trajectoryLimitWeight_le (n : ℕ) :
    (trajectoryLimitWeight hε supply : ℝ → ℝ) ≤ᵐ[μ] ((states n).v : ℝ → ℝ) := by
  filter_upwards [ae_positiveLimitWeight_le_stageWeight (fun n x => (steps n).V.positive x)
    (ae_trajectoryProduct_pos hε supply) n] with x hx
  rw [trajectory_weight_eq hε supply]
  exact hx

private theorem trajectoryWeights_tendsto :
    ∀ᵐ x ∂μ, Tendsto (fun n => (states n).v x) atTop (𝓝 (trajectoryLimitWeight hε supply x)) := by
  filter_upwards [ae_positiveLimitWeight_eq (ae_trajectoryProduct_pos hε supply)] with x hx
  simp_rw [trajectory_weight_eq hε supply]
  change Tendsto _ _ (𝓝 (positiveLimitWeight (trajectoryMultipliers hε supply) x))
  rw [hx]
  exact stageWeight_tendsto (fun n x => (steps n).V.positive x) (fun n x => (steps n).V.le_one x) x

private theorem stageDistance_bound (q : ℚ) (n : ℕ) :
    lineDistanceSq μ (states n).v (states n).a q ≤
      lineContraction (stageU ε) ^ visitCount q n *
        lineDistanceSq μ (states 0).v (states 0).a q := by
  induction n with
  | zero => simp [visitCount]
  | succ n ih =>
    have hθ := (lineContraction_bounds (stageU_bounds hε).1).1
    rw [visitCount_succ]
    by_cases hq : rationalSchedule n = q
    · have ht : lineDistanceSq μ (states (n + 1)).v (states (n + 1)).a q ≤
          lineContraction (stageU ε) * lineDistanceSq μ (states n).v (states n).a q := by
        rw [← hq]
        exact (steps n).contraction
      calc
        _ ≤ lineContraction (stageU ε) *
            (lineContraction (stageU ε) ^ visitCount q n *
              lineDistanceSq μ (states 0).v (states 0).a q) :=
          ht.trans (mul_le_mul_of_nonneg_left ih hθ.le)
        _ = _ := by rw [ite_eq_left hq, pow_succ]; ring
    · have hmono := lineDistanceSq_mono μ (trajectory_prefix_succ hε supply n)
          (v := (states n).v) (w := (states (n + 1)).v) (by
            have heq : (states (n + 1)).v = (states n).v.mul (steps n).V := (steps n).next_eq
            rw [heq]
            exact Eventually.of_forall fun x =>
              mul_le_of_le_one_right ((states n).v.positive x).le ((steps n).V.le_one x)) q
      simpa only [ite_eq_right hq, add_zero] using hmono.trans ih

private theorem finalDistance_tendsto (q : ℚ) :
    Tendsto (fun n => lineDistanceSq μ (trajectoryLimitWeight hε supply) (states n).a q)
      atTop (𝓝 0) := by
  have hθ := lineContraction_bounds (stageU_bounds hε).1
  have ht := ((tendsto_pow_atTop_nhds_zero_of_lt_one hθ.1.le hθ.2).comp
    (tendsto_visitCount q)).mul_const (lineDistanceSq μ (states 0).v (states 0).a q)
  refine squeeze_zero (fun _ => lineDistanceSq_nonneg ..) (fun n => ?_)
    (by simpa only [zero_mul] using ht)
  exact (lineDistanceSq_mono μ List.prefix_rfl (trajectoryLimitWeight_le hε supply n) q).trans
    (stageDistance_bound hε supply q n)

private def finalFrequency : ℕ → ℚ :=
  orderedListLimit (fun n => (states n).a) (trajectory_unbounded hε supply)

private theorem finalFrequency_eq (n : ℕ) (i : Fin (states n).a.length) :
    finalFrequency hε supply i = (states n).a.get i :=
  orderedListLimit_eq _ _ (fun _ _ h => trajectory_prefix hε supply h) n i i.isLt

private theorem injective_finalFrequency : Injective (finalFrequency hε supply) :=
  orderedListLimit_injective _ _ (fun _ _ h => trajectory_prefix hε supply h) (fun n => (states n).nodup)

private theorem hPrefix_realFamily_of_prefix {ν : Measure ℝ} [IsFiniteMeasure ν]
    {a b : List ℚ} (hpre : a <+: b) {K : ℝ}
    (hK : HPrefix (𝕜 := ℂ) (realFamily ν b) K) :
    HPrefix (𝕜 := ℂ) (realFamily ν a) K := by
  let e : Fin a.length ↪ Fin b.length := Fin.castLEEmb hpre.length_le
  have he : StrictMono e := fun _ _ h => h
  have heq : realFamily ν a = (realFamily ν b) ∘ e := by
    funext i
    change realCharLp ν (a[i.val] : ℝ) = realCharLp ν (b[i.val]'(i.isLt.trans_le hpre.length_le) : ℝ)
    rw [hpre.getElem i.isLt]
  rw [heq]
  exact hK.restrict e he

private theorem finalPrefix_bound (n : ℕ) :
    HPrefix (𝕜 := ℂ) (realFamily ((trajectoryLimitWeight hε supply).measure μ) (states n).a) (1 + ε) := by
  apply hPrefix_of_weight_limit μ (fun m => (states m).v) _ (trajectoryWeights_tendsto hε supply)
  filter_upwards [eventually_ge_atTop n] with m hm
  exact hPrefix_realFamily_of_prefix (trajectory_prefix hε supply hm)
    ((states m).prefix_bound.mono (stagePrefixBound_le hε m))

private theorem dense_span_finalFrequency :
    Dense (span ℂ (Set.range (fun n => realCharLp ((trajectoryLimitWeight hε supply).measure μ)
      (finalFrequency hε supply n : ℝ))) : Set (Lp ℂ 2 ((trajectoryLimitWeight hε supply).measure μ))) := by
  let ν := (trajectoryLimitWeight hε supply).measure μ
  let S := span ℂ (Set.range (fun n => realCharLp ν (finalFrequency hε supply n : ℝ)))
  apply Submodule.dense_iff_topologicalClosure_eq_top.mpr
  have hsub : span ℂ (Set.range (fun q : ℚ => realCharLp ν (q : ℝ))) ≤ S.topologicalClosure := by
    apply span_le.mpr
    rintro _ ⟨q, rfl⟩
    let f := realCharLp ν (q : ℝ)
    have hle (n : ℕ) : Metric.infDist f (S : Set _) ^ 2 ≤
        lineDistanceSq μ (trajectoryLimitWeight hε supply) (states n).a q := by
      let E := span ℂ (Set.range (realFamily ν (states n).a))
      have hES : E ≤ S := by
        apply span_le.mpr
        rintro _ ⟨i, rfl⟩
        apply subset_span
        refine ⟨i.val, ?_⟩
        change realCharLp ν (finalFrequency hε supply i : ℝ) =
          realCharLp ν ((states n).a.get i : ℝ)
        rw [finalFrequency_eq hε supply n i]
      exact pow_le_pow_left₀ Metric.infDist_nonneg
        (Metric.infDist_le_infDist_of_subset hES ⟨0, E.zero_mem⟩) 2
    have hz := le_of_tendsto_of_tendsto' tendsto_const_nhds (finalDistance_tendsto hε supply q) hle
    have hzero : Metric.infDist f (S : Set _) = 0 := by nlinarith [sq_nonneg (Metric.infDist f (S : Set _))]
    change f ∈ closure (S : Set _)
    exact (Metric.mem_closure_iff_infDist_zero ⟨0, S.zero_mem⟩).mpr hzero
  apply top_unique
  rw [← Submodule.dense_iff_topologicalClosure_eq_top.mp (dense_span_rat_realCharLp ν)]
  exact Submodule.topologicalClosure_minimal _ hsub S.isClosed_topologicalClosure

include hε supply in
/-- Given the finite extension proposition, the ordered iteration produces a basis
of rational characters in a positively weighted L² space. -/
theorem weighted_exponential_basis_of_lineExtension [NullSingletonClass μ] (hμ : μ ≠ 0) :
    ∃ (w : LineWeight) (t : ℕ → ℚ), Injective t ∧
      ∃ b : SchauderBasis ℂ (Lp ℂ 2 (w.measure μ)),
        ∀ n, b n = realCharLp (w.measure μ) (t n : ℝ) := by
  let w := trajectoryLimitWeight hε supply
  let t := finalFrequency hε supply
  let f (n : ℕ) := realCharLp (w.measure μ) (t n : ℝ)
  have ht : Injective t := injective_finalFrequency hε supply
  have hlin : LinearIndependent ℂ f := by
    apply linearIndependent_of_initial
    intro n
    exact linearIndependent_realCharLp (w.measure_ne_zero hμ)
      (Rat.cast_injective.comp (ht.comp (Fin.val_injective : Injective (Fin.val : Fin n → ℕ))))
  have hpb : OrderedPrefixBound f (1 + ε) := by
    apply orderedPrefixBound_of_initial
    intro n
    obtain ⟨m, hm⟩ := trajectory_unbounded hε supply n
    let e : Fin n ↪ Fin (states m).a.length := Fin.castLEEmb hm.le
    have he : StrictMono e := fun _ _ h => h
    have heq : (fun i : Fin n => f i.val) = realFamily (w.measure μ) (states m).a ∘ e := by
      funext i
      change realCharLp (w.measure μ) (t i.val : ℝ) =
        realCharLp (w.measure μ) ((states m).a.get (e i) : ℝ)
      rw [show t i.val = (states m).a.get (e i) from finalFrequency_eq hε supply m (e i)]
    rw [heq]
    exact (finalPrefix_bound hε supply m).restrict e he
  obtain ⟨b, hb⟩ := basis_of_orderedPrefixBound hlin (dense_span_finalFrequency hε supply) hpb
  exact ⟨w, t, ht, b, hb⟩

end

end SchauderBasisOrbits

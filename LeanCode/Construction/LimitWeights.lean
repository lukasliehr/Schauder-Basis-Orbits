module

public import Mathlib

@[expose] public section

open Filter MeasureTheory
open scoped ENNReal Topology BigOperators

namespace SchauderBasisOrbits

variable {α : Type*} [MeasurableSpace α]

/-- Product of the first `n` stage multipliers. -/
def stageWeight (V : ℕ → α → ℝ) (n : ℕ) (x : α) : ℝ :=
  ∏ j ∈ Finset.range n, V j x

omit [MeasurableSpace α] in
theorem stageWeight_pos {V : ℕ → α → ℝ} (hV : ∀ n x, 0 < V n x) (n : ℕ) (x : α) :
    0 < stageWeight V n x :=
  Finset.prod_pos fun _ _ => hV _ _

omit [MeasurableSpace α] in
theorem stageWeight_antitone {V : ℕ → α → ℝ} (hV : ∀ n x, 0 < V n x)
    (h₁ : ∀ n x, V n x ≤ 1) (x : α) :
    Antitone (fun n => stageWeight V n x) := by
  apply antitone_nat_of_succ_le
  intro n
  rw [stageWeight, Finset.prod_range_succ]
  exact mul_le_of_le_one_right (stageWeight_pos hV n x).le (h₁ n x)

theorem measurable_stageWeight {V : ℕ → α → ℝ} (hV : ∀ n, Measurable (V n)) (n : ℕ) :
    Measurable (stageWeight V n) := by
  unfold stageWeight
  exact Finset.measurable_prod _ (fun i _ => hV i)

/-- The decreasing limit of the products, before modification on a null set. -/
noncomputable def limitWeight (V : ℕ → α → ℝ) (x : α) : ℝ :=
  ⨅ n, stageWeight V n x

omit [MeasurableSpace α] in
private theorem stageWeight_bddBelow {V : ℕ → α → ℝ} (hV : ∀ n x, 0 < V n x) (x : α) :
    BddBelow (Set.range (fun n => stageWeight V n x)) :=
  ⟨0, by rintro _ ⟨n, rfl⟩; exact (stageWeight_pos hV n x).le⟩

theorem measurable_limitWeight {V : ℕ → α → ℝ} (hV : ∀ n, Measurable (V n)) :
    Measurable (limitWeight V) := Measurable.iInf (measurable_stageWeight hV)

omit [MeasurableSpace α] in
theorem limitWeight_le_stageWeight {V : ℕ → α → ℝ} (hV : ∀ n x, 0 < V n x) (n : ℕ) (x : α) :
    limitWeight V x ≤ stageWeight V n x := ciInf_le (stageWeight_bddBelow hV x) n

omit [MeasurableSpace α] in
theorem limitWeight_nonneg {V : ℕ → α → ℝ} (hV : ∀ n x, 0 < V n x) (x : α) :
    0 ≤ limitWeight V x := le_ciInf fun n => (stageWeight_pos hV n x).le

omit [MeasurableSpace α] in
theorem stageWeight_tendsto {V : ℕ → α → ℝ} (hV : ∀ n x, 0 < V n x)
    (h₁ : ∀ n x, V n x ≤ 1) (x : α) :
    Tendsto (fun n => stageWeight V n x) atTop (𝓝 (limitWeight V x)) :=
  tendsto_atTop_ciInf (stageWeight_antitone hV h₁ x) (stageWeight_bddBelow hV x)

/-- If the losses of positive stage multipliers have a summable integral bound,
their decreasing product is positive almost everywhere. -/
theorem ae_limitWeight_pos (μ : Measure α) [IsFiniteMeasure μ] {V : ℕ → α → ℝ}
    (hV : ∀ n, Measurable (V n)) (hp : ∀ n x, 0 < V n x)
    (h₁ : ∀ n x, V n x ≤ 1) {δ : ℕ → ℝ} (hδ : Summable δ)
    (hloss : ∀ n, (∫ x, 1 - V n x ∂μ) ≤ δ n) :
    ∀ᵐ x ∂μ, 0 < limitWeight V x := by
  let loss : ℕ → α → ℝ≥0∞ := fun n x => ENNReal.ofReal (1 - V n x)
  have hm (n : ℕ) : Measurable (loss n) :=
    (measurable_const.sub (hV n)).ennreal_ofReal
  have hi (n : ℕ) : Integrable (fun x => 1 - V n x) μ :=
    (MemLp.of_bound ((measurable_const.sub (hV n)).aestronglyMeasurable) 1
      (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr (h₁ n x))]
        linarith [hp n x]) : MemLp (fun x => 1 - V n x) 1 μ).integrable le_rfl
  have hbound : (∫⁻ x, ∑' n, loss n x ∂μ) ≤ ∑' n, ENNReal.ofReal (δ n) := by
    rw [lintegral_tsum fun n => (hm n).aemeasurable]
    apply tsum_le_tsum
    intro n
    change (∫⁻ x, ENNReal.ofReal (1 - V n x) ∂μ) ≤ ENNReal.ofReal (δ n)
    rw [
      ← ofReal_integral_eq_lintegral_ofReal (hi n) (Eventually.of_forall fun x => sub_nonneg.mpr (h₁ n x))]
    exact ENNReal.ofReal_le_ofReal (hloss n)
  have hfinite := ae_lt_top (Measurable.tsum hm) ((hbound.trans_lt hδ.tsum_ofReal_lt_top).ne)
  filter_upwards [hfinite] with x hx
  have hs : Summable (fun n => ‖V n x - 1‖) := by
    have h := ENNReal.summable_toReal hx.ne
    convert h using 1
    funext n
    rw [Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr (h₁ n x)), show loss n x = ENNReal.ofReal (1 - V n x) from rfl,
      ENNReal.toReal_ofReal (sub_nonneg.mpr (h₁ n x))]
    ring
  have heq : (fun n => 1 + (V n x - 1)) = fun n => V n x := by
    funext n
    ring
  have hnz := tprod_one_add_ne_zero_of_summable
    (f := fun n => V n x - 1) (fun n => by rw [congrFun heq]; exact (hp n x).ne') hs
  rw [heq] at hnz
  have hprod := (multipliable_one_add_of_summable hs)
  rw [heq] at hprod
  have hlim := tendsto_nhds_unique (stageWeight_tendsto hp h₁ x) hprod.hasProd.tendsto_prod_nat
  exact lt_of_le_of_ne (limitWeight_nonneg hp x) ((hlim ▸ hnz).symm)

/-- A strictly positive representative of the limiting weight. -/
noncomputable def positiveLimitWeight (V : ℕ → α → ℝ) (x : α) : ℝ :=
  if 0 < limitWeight V x then limitWeight V x else 1

theorem measurable_positiveLimitWeight {V : ℕ → α → ℝ} (hV : ∀ n, Measurable (V n)) :
    Measurable (positiveLimitWeight V) :=
  (measurable_limitWeight hV).ite (measurableSet_lt measurable_const (measurable_limitWeight hV))
    measurable_const

omit [MeasurableSpace α] in
theorem positiveLimitWeight_bounds {V : ℕ → α → ℝ} (hp : ∀ n x, 0 < V n x) (x : α) :
    0 < positiveLimitWeight V x ∧ positiveLimitWeight V x ≤ 1 := by
  have h := limitWeight_le_stageWeight hp 0 x
  simp [stageWeight] at h
  by_cases hx : 0 < limitWeight V x <;> simp [positiveLimitWeight, hx, h]

theorem ae_positiveLimitWeight_eq {μ : Measure α} {V : ℕ → α → ℝ}
    (hp : ∀ᵐ x ∂μ, 0 < limitWeight V x) :
    positiveLimitWeight V =ᵐ[μ] limitWeight V :=
  hp.mono fun _ hx => ite_eq_left hx

theorem ae_positiveLimitWeight_le_stageWeight {μ : Measure α} {V : ℕ → α → ℝ}
    (hp : ∀ n x, 0 < V n x) (hae : ∀ᵐ x ∂μ, 0 < limitWeight V x) (n : ℕ) :
    positiveLimitWeight V ≤ᵐ[μ] stageWeight V n :=
  (ae_positiveLimitWeight_eq hae).mono fun x hx => hx.le.trans (limitWeight_le_stageWeight hp n x)

end SchauderBasisOrbits

module

public import Mathlib

@[expose] public section

open Filter Function
open scoped Topology

namespace SchauderBasisOrbits

/-- A surjective enumeration of rational frequencies. -/
def enumerateRational (n : ℕ) : ℚ := (Encodable.decode (α := ℚ) n).getD 0

@[simp] theorem enumerateRational_encode (q : ℚ) :
    enumerateRational (Encodable.encode q) = q := by
  simp [enumerateRational]

/-- The start of round `m`. This round visits indices 0 through m of the enumeration. -/
def roundStart : ℕ → ℕ
  | 0 => 0
  | m + 1 => roundStart m + (m + 1)

@[simp] theorem roundStart_zero : roundStart 0 = 0 := rfl

@[simp] theorem roundStart_succ (m : ℕ) : roundStart (m + 1) = roundStart m + (m + 1) := rfl

theorem le_roundStart (m : ℕ) : m ≤ roundStart m := by
  induction m with
  | zero => simp
  | succ m ih => rw [roundStart_succ]; omega

theorem strictMono_roundStart : StrictMono roundStart :=
  strictMono_nat_of_lt_succ fun n => by rw [roundStart_succ]; omega

theorem exists_round (n : ℕ) : ∃ m, n < roundStart (m + 1) :=
  ⟨n, lt_of_lt_of_le (Nat.lt_succ_self n) (le_roundStart _)⟩

/-- The round containing visit `n`. -/
noncomputable def roundAt (n : ℕ) : ℕ := Nat.find (exists_round n)

theorem roundAt_spec (n : ℕ) : roundStart (roundAt n) ≤ n ∧ n < roundStart (roundAt n + 1) := by
  refine ⟨?_, Nat.find_spec (exists_round n)⟩
  cases h : roundAt n with
  | zero => simp
  | succ m =>
    rw [← not_lt, ← Nat.succ_eq_add_one]
    exact Nat.find_min (exists_round n) (by change m < roundAt n; rw [h]; omega)

theorem roundAt_eq_of_bounds {n m : ℕ} (h₀ : roundStart m ≤ n)
    (h₁ : n < roundStart (m + 1)) : roundAt n = m := by
  have hle : roundAt n ≤ m := Nat.find_min' (exists_round n) h₁
  apply le_antisymm hle
  by_contra h
  have hh : roundAt n + 1 ≤ m := by omega
  exact (not_lt_of_ge h₀) ((roundAt_spec n).2.trans_le (strictMono_roundStart.monotone hh))

/-- The recurrent schedule obtained by concatenating the rounds of increasing length. -/
noncomputable def rationalSchedule (n : ℕ) : ℚ := enumerateRational (n - roundStart (roundAt n))

theorem rationalSchedule_round {m i : ℕ} (hi : i ≤ m) :
    rationalSchedule (roundStart m + i) = enumerateRational i := by
  have hm : roundAt (roundStart m + i) = m := roundAt_eq_of_bounds (by omega)
    (by rw [roundStart_succ]; omega)
  simp [rationalSchedule, hm]

theorem exists_rationalSchedule_ge (q : ℚ) (N : ℕ) :
    ∃ j ≥ N, rationalSchedule j = q := by
  let i := Encodable.encode q
  let m := max N i
  refine ⟨roundStart m + i, ?_, ?_⟩
  · exact le_trans (le_max_left ..) (le_trans (le_roundStart m) (Nat.le_add_right ..))
  · rw [rationalSchedule_round (le_max_right ..), show i = Encodable.encode q from rfl,
      enumerateRational_encode]

/-- Number of visits to `q` strictly before stage `n`. -/
noncomputable def visitCount (q : ℚ) (n : ℕ) : ℕ :=
  ((Finset.range n).filter (fun j => rationalSchedule j = q)).card

theorem visitCount_mono (q : ℚ) : Monotone (visitCount q) := by
  intro n m hnm
  exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.range_mono hnm))

theorem visitCount_succ (q : ℚ) (n : ℕ) :
    visitCount q (n + 1) = visitCount q n + if rationalSchedule n = q then 1 else 0 := by
  unfold visitCount
  rw [Finset.range_add_one, Finset.filter_insert]
  by_cases h : rationalSchedule n = q
  · simp only [h, ite_true]
    apply Finset.card_insert_of_notMem
    simp
  · simp [h]

theorem tendsto_visitCount (q : ℚ) : Tendsto (visitCount q) atTop atTop := by
  have hc : ∀ k, ∃ n, k ≤ visitCount q n := by
    intro k
    induction k with
    | zero => exact ⟨0, Nat.zero_le _⟩
    | succ k ih =>
      obtain ⟨N, hN⟩ := ih
      obtain ⟨j, hj, hq⟩ := exists_rationalSchedule_ge q N
      refine ⟨j + 1, ?_⟩
      simp only [visitCount_succ, hq, ite_true]
      exact Nat.add_le_add_right (hN.trans (visitCount_mono q hj)) 1
  refine tendsto_atTop.2 fun k => ?_
  obtain ⟨n, hn⟩ := hc k
  filter_upwards [eventually_ge_atTop n] with m hm
  exact hn.trans (visitCount_mono q hm)

end SchauderBasisOrbits

module

public import Mathlib

@[expose] public section

open Function

namespace SchauderBasisOrbits

variable {α : Type*} (a : ℕ → List α)

/-- Obtain the entry of a compatible list sequence from any list long enough to contain it. -/
noncomputable def orderedListLimit (h : ∀ i, ∃ n, i < (a n).length) (i : ℕ) : α :=
  (a (Classical.choose (h i))).get ⟨i, Classical.choose_spec (h i)⟩

theorem orderedListLimit_eq (h : ∀ i, ∃ n, i < (a n).length)
    (hpre : ∀ n m, n ≤ m → a n <+: a m) (n i : ℕ) (hi : i < (a n).length) :
    orderedListLimit a h i = (a n)[i] := by
  let m := Classical.choose (h i)
  have hm : i < (a m).length := Classical.choose_spec (h i)
  change (a m)[i] = (a n)[i]
  exact ((hpre m (max m n) (le_max_left ..)).getElem hm).trans
    ((hpre n (max m n) (le_max_right ..)).getElem hi).symm

theorem orderedListLimit_injective (h : ∀ i, ∃ n, i < (a n).length)
    (hpre : ∀ n m, n ≤ m → a n <+: a m) (hnodup : ∀ n, (a n).Nodup) :
    Injective (orderedListLimit a h) := by
  intro i j hij
  obtain ⟨n, hn⟩ := h (max i j)
  have hi : i < (a n).length := (le_max_left i j).trans_lt hn
  have hj : j < (a n).length := (le_max_right i j).trans_lt hn
  rw [orderedListLimit_eq a h hpre n i hi, orderedListLimit_eq a h hpre n j hj] at hij
  exact (List.getElem_inj (hnodup n)).mp hij

end SchauderBasisOrbits

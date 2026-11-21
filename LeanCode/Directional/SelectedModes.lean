import LeanCode.Directional.SelectedGram

open Filter Function MeasureTheory
open scoped ENNReal

namespace SchauderBasisOrbits.DirectionalInput

noncomputable section

variable {ι : Type*} [Fintype ι]
variable {ρ : Measure (ℝ × UnitAddTorus ι)} [IsFiniteMeasure ρ] (D : DirectionalInput ρ)

def rowFrequency {L : ℕ} : Fin (D.d + L) → MixedFreq (ι ⊕ Fin L) :=
  Fin.append
    (fun i => padMixedFreq Function.Embedding.inl (D.frequencies i))
    (fun i => padMixedFreq Function.Embedding.inr (0, Pi.single i 1))

theorem rowFrequency_real {L : ℕ} (i : Fin (D.d + L)) :
    (D.rowFrequency i).1 = 0 ∨ ∃ j, (D.rowFrequency i).1 = (D.frequencies j).1 := by
  refine Fin.addCases (fun j => Or.inr ⟨j, ?_⟩) (fun j => Or.inl ?_) i <;>
    simp [rowFrequency, padMixedFreq]

theorem rowFrequency_aux_injective {L : ℕ}
    (hφ : Injective fun i => (D.frequencies i).2) :
    Injective (fun i : Fin (D.d + L) => (D.rowFrequency i).2) := by
  intro i j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;>
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j
  · intro h
    simp only [rowFrequency, Fin.append_left, padMixedFreq] at h
    rw [hφ ((padMode_injective _) h)]
  · intro h
    have hm := congrFun h (Sum.inr j)
    have hnot : (Sum.inr j : ι ⊕ Fin L) ∉ Set.range (Function.Embedding.inl : ι ↪ ι ⊕ Fin L) := by simp
    simp only [rowFrequency, Fin.append_left, Fin.append_right, padMixedFreq] at hm
    rw [padMode_off _ _ hnot, padMode_inr, Pi.single_eq_same] at hm
    norm_num at hm
  · intro h
    have hm := congrFun h (Sum.inr i)
    have hnot : (Sum.inr i : ι ⊕ Fin L) ∉ Set.range (Function.Embedding.inl : ι ↪ ι ⊕ Fin L) := by simp
    simp only [rowFrequency, Fin.append_left, Fin.append_right, padMixedFreq] at hm
    rw [padMode_off _ _ hnot, padMode_inr, Pi.single_eq_same] at hm
    norm_num at hm
  · intro h
    simp only [rowFrequency, Fin.append_right, padMixedFreq] at h
    have hh := padMode_injective _ h
    have he : i = j := by
      by_contra hne
      have hzero := congrFun hh i
      rw [Pi.single_eq_same, Pi.single_eq_of_ne hne] at hzero
      norm_num at hzero
    rw [he]

/-- The ordered nonconstant columns, with explicit auxiliary coordinate blocks. -/
def selectedFrequency {L r n : ℕ} (S : Scalar.Data r n)
    (ji : Fin n × Fin (D.d + L)) : MixedFreq ((ι ⊕ Fin L) ⊕ Fin r) :=
  padMixedFreq Function.Embedding.inl (D.rowFrequency ji.2) +
    padMixedFreq Function.Embedding.inr (0, S.mode ji.1)

theorem selectedFrequency_scalar {L r n : ℕ} (S : Scalar.Data r n)
    (ji : Fin n × Fin (D.d + L)) (k : Fin r) :
    (D.selectedFrequency S ji).2 (Sum.inr k) = S.mode ji.1 k := by
  have hnot : (Sum.inr k : (ι ⊕ Fin L) ⊕ Fin r) ∉
      Set.range (Function.Embedding.inl : (ι ⊕ Fin L) ↪ (ι ⊕ Fin L) ⊕ Fin r) := by simp
  simp only [selectedFrequency, Prod.snd_add, padMixedFreq, Pi.add_apply]
  rw [padMode_off _ _ hnot, padMode_inr, zero_add]

theorem selectedFrequency_row {L r n : ℕ} (S : Scalar.Data r n)
    (ji : Fin n × Fin (D.d + L)) (k : ι ⊕ Fin L) :
    (D.selectedFrequency S ji).2 (Sum.inl k) = (D.rowFrequency ji.2).2 k := by
  have hnot : (Sum.inl k : (ι ⊕ Fin L) ⊕ Fin r) ∉
      Set.range (Function.Embedding.inr : Fin r ↪ (ι ⊕ Fin L) ⊕ Fin r) := by simp
  simp only [selectedFrequency, Prod.snd_add, padMixedFreq, Pi.add_apply]
  rw [padMode_off _ _ hnot, padMode_inl, add_zero]

theorem selectedFrequency_real {L r n : ℕ} (S : Scalar.Data r n)
    (ji : Fin n × Fin (D.d + L)) :
    (D.selectedFrequency S ji).1 = 0 ∨ ∃ j, (D.selectedFrequency S ji).1 = (D.frequencies j).1 := by
  simp only [selectedFrequency, Prod.fst_add, padMixedFreq, add_zero]
  exact D.rowFrequency_real ji.2

theorem selectedFrequency_fresh {L r n : ℕ} (S : Scalar.Data r n)
    (ji : Fin n × Fin (D.d + L)) :
    (fun k => (D.selectedFrequency S ji).2 (Sum.inr k)) ≠ 0 := by
  simp only [D.selectedFrequency_scalar]
  exact S.mode_ne_zero ji.1

theorem selectedFrequency_aux_injective {L r n : ℕ} (S : Scalar.Data r n)
    (hφ : Injective fun i => (D.frequencies i).2) :
    Injective (fun ji : Fin n × Fin (D.d + L) => (D.selectedFrequency S ji).2) := by
  intro p q hpq
  apply Prod.ext
  · apply S.mode_inj
    funext i
    simpa only [D.selectedFrequency_scalar] using congrFun hpq (Sum.inr i)
  · apply D.rowFrequency_aux_injective hφ
    funext i
    simpa only [D.selectedFrequency_row] using congrFun hpq (Sum.inl i)

theorem eval_rowFrequency {L : ℕ} (i : Fin (D.d + L)) (z : ℝ × UnitAddTorus (ι ⊕ Fin L)) :
    mixedChar (D.rowFrequency i) z = D.rawRow i ((z.1, z.2 ∘ Sum.inl), z.2 ∘ Sum.inr) := by
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp only [rowFrequency, rawRow, Fin.append_left, mixedChar_padMixedFreq]
    rfl
  · rw [rowFrequency, Fin.append_right, mixedChar_padMixedFreq, rawRow, Fin.append_right, phaseRow]
    simp [mixedChar, torusChar, UnitAddTorus.mFourier_single]

theorem eval_selectedFrequency {L r n : ℕ} (S : Scalar.Data r n)
    (ji : Fin n × Fin (D.d + L)) (z : ℝ × UnitAddTorus ((ι ⊕ Fin L) ⊕ Fin r)) :
    mixedChar (D.selectedFrequency S ji) z =
      D.rawSelected S (ji.1.succ, ji.2)
        ((z.1, fun i => z.2 (Sum.inl (Sum.inl i))),
          (fun i => z.2 (Sum.inl (Sum.inr i)), fun i => z.2 (Sum.inr i))) := by
  simp only [selectedFrequency, mixedChar_add, mixedChar_padMixedFreq, D.eval_rowFrequency,
    rawSelected, Scalar.Data.augMode_succ]
  have h : mixedChar (0, S.mode ji.1) (z.1, z.2 ∘ Sum.inr) = torusChar (S.mode ji.1) (z.2 ∘ Sum.inr) := by
    simp [mixedChar]
  rw [show (⇑(Function.Embedding.inr : Fin r ↪ (ι ⊕ Fin L) ⊕ Fin r)) = Sum.inr from rfl, h]
  rfl

end

end SchauderBasisOrbits.DirectionalInput

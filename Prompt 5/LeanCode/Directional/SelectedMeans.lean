import LeanCode.Directional.RowMoments

open Filter Function MeasureTheory Submodule
open scoped ENNReal BigOperators ComplexConjugate InnerProductSpace

namespace SchauderBasisOrbits.DirectionalInput

noncomputable section

variable {ι : Type*} [Fintype ι]
variable {ρ : Measure (Base ι)} [IsFiniteMeasure ρ] (D : DirectionalInput ρ)

def scalarMoment {r n : ℕ} (S : Scalar.Data r n) (k : Fin n) : ℂ :=
  ∫ y, (S.w y : ℂ) * torusChar (S.mode k) y ∂torusHaar (Fin r)

theorem scalarMoment_eq {r n : ℕ} (S : Scalar.Data r n) (k : Fin n) :
    scalarMoment S k = (S.meanColumn k : ℂ) := by
  have h := congrFun (congrFun S.complexify_gram (0 : Fin (n + 1))) k.succ
  change (S.gram 0 k.succ : ℂ) = S.complexGram 0 k.succ at h
  rw [S.gram_zero_succ] at h
  rw [h, Scalar.Data.complexGram, Scalar.charGram, Matrix.of_apply,
    S.augMode_zero, S.augMode_succ]
  simp [scalarMoment]

set_option maxHeartbeats 1000000 in
theorem selected_mean_rawRow {L r n : ℕ} {m : ℝ} (hm : 0 < m)
    (hm' : m ≤ ((1 : ℝ) / 2) ^ L) (S : Scalar.Data r n) (k : Fin n)
    (i : Fin (D.d + L)) (s : Base ι) :
    (((D.seedFiber L hm hm').selected S).mass : ℂ) *
      ((D.seedFiber L hm hm').selected S).mean (D.rawSelected S (k.succ, i)) s =
        ((∫ y, D.rawRow i (s, y) ∂torusHaar (Fin L)) -
          (m : ℂ) * (D.seedFiber L hm hm').mean (D.rawRow i) s) * scalarMoment S k := by
  let U := D.seedFiber L hm hm'
  let W := U.selected S
  let a (y : UnitAddTorus (Fin L)) := D.rawRow i (s, y)
  let b := torusChar (S.mode k)
  have ha : Integrable a (torusHaar (Fin L)) :=
    Integrable.of_bound ((D.measurable_rawRow i).comp measurable_prodMk_left).aestronglyMeasurable 1
      (Eventually.of_forall fun y => (D.norm_rawRow i (s, y)).le)
  have hb : Integrable b (torusHaar (Fin r)) := integrable_torusChar _
  have hU : Measurable (fun y => U.weight (s, y)) := U.measurable_weight.comp measurable_prodMk_left
  have hZero : (∫ y, b y ∂torusHaar (Fin r)) = 0 := by
    simp only [b, integral_torusChar, ite_eq_right (S.mode_ne_zero k)]
  change (W.mass : ℂ) * W.mean (D.rawSelected S (k.succ, i)) s = _
  rw [← W.integral_weight_eq_mass_mean]
  have hEq (p : UnitAddTorus (Fin L) × UnitAddTorus (Fin r)) :
      (W.weight (s, p) : ℂ) * D.rawSelected S (k.succ, i) (s, p) =
        ((S.w p.2 + (1 - S.w p.2) * U.weight (s, p.1) : ℝ) : ℂ) * a p.1 * b p.2 := by
    simp only [rawSelected, S.augMode_succ]
    change (W.weight (s, p) : ℂ) * (a p.1 * b p.2) = (W.weight (s, p) : ℂ) * a p.1 * b p.2
    exact (mul_assoc _ _ _).symm
  rw [integral_congr_ae (Eventually.of_forall hEq)]
  rw [integral_selected_pairing ha hb hU S.measurable_w
    (fun y => ⟨(U.weight_pos (s, y)).le, U.weight_le_one (s, y)⟩)
    (fun y => ⟨S.w_nonneg y, S.le_one y⟩),
    hZero, mul_zero, zero_add,
    show (∫ y, (U.weight (s, y) : ℂ) * a y ∂torusHaar (Fin L)) =
      (m : ℂ) * U.mean (D.rawRow i) s from U.integral_weight_eq_mass_mean _ s]
  rfl

theorem selected_mean_base {L r n : ℕ} {m : ℝ} (hm : 0 < m)
    (hm' : m ≤ ((1 : ℝ) / 2) ^ L) (S : Scalar.Data r n) (k : Fin n)
    (i : Fin D.d) (s : Base ι) :
    (((D.seedFiber L hm hm').selected S).mass : ℂ) *
      ((D.seedFiber L hm hm').selected S).mean (D.rawSelected S (k.succ, Fin.castAdd L i)) s =
        (1 - (m : ℂ)) * (S.meanColumn k : ℂ) * mixedChar (D.frequencies i) s := by
  rw [D.selected_mean_rawRow hm hm' S k, scalarMoment_eq]
  have he : D.rawRow (Fin.castAdd L i) =
      (fun p : RowPoint ι L => mixedChar (D.frequencies i) p.1) := by
    funext p
    simp [rawRow]
  rw [he]
  rw [(D.seedFiber L hm hm').mean_fst (fun x : Base ι => mixedChar (D.frequencies i) x) s]
  change ((∫ _ : UnitAddTorus (Fin L), mixedChar (D.frequencies i) s ∂torusHaar (Fin L)) -
    (m : ℂ) * mixedChar (D.frequencies i) s) * (S.meanColumn k : ℂ) = _
  simp only [integral_const, probReal_univ, one_smul]
  ring

theorem selected_mean_phase {L r n : ℕ} {m : ℝ} (hm : 0 < m)
    (hm' : m ≤ ((1 : ℝ) / 2) ^ L) (S : Scalar.Data r n) (k : Fin n)
    (i : Fin L) (s : Base ι) :
    (((D.seedFiber L hm hm').selected S).mass : ℂ) *
      ((D.seedFiber L hm hm').selected S).mean (D.rawSelected S (k.succ, Fin.natAdd D.d i)) s =
        - (m : ℂ) * (S.meanColumn k : ℂ) * D.amplitude s := by
  rw [D.selected_mean_rawRow hm hm' S k, scalarMoment_eq]
  have he : D.rawRow (Fin.natAdd D.d i) = phaseRow (ι := ι) i := by
    funext p
    simp [rawRow]
  rw [he, D.seedFiber_mean_phase hm hm']
  have h (y : UnitAddTorus (Fin L)) : phaseRow (ι := ι) i (s, y) = torusChar (Pi.single i 1) y :=
    (UnitAddTorus.mFourier_single y i).symm
  simp_rw [h]
  rw [integral_torusChar, ite_eq_right]
  · ring
  · intro hz
    have hbad := congrFun hz i
    simpa using hbad

end

end SchauderBasisOrbits.DirectionalInput

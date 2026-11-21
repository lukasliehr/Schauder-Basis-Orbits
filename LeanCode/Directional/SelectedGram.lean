import LeanCode.Directional.SelectedWeight

open Filter Function MeasureTheory
open scoped ENNReal BigOperators ComplexConjugate InnerProductSpace

namespace SchauderBasisOrbits.DirectionalInput

noncomputable section

variable {ι : Type*} [Fintype ι]
variable {ρ : Measure (ℝ × UnitAddTorus ι)} [IsFiniteMeasure ρ] (D : DirectionalInput ρ)

abbrev Base (ι : Type*) := ℝ × UnitAddTorus ι
abbrev RowPoint (ι : Type*) (L : ℕ) := Base ι × UnitAddTorus (Fin L)
abbrev SelectedPoint (ι : Type*) (L r : ℕ) :=
  Base ι × (UnitAddTorus (Fin L) × UnitAddTorus (Fin r))

/-- Keep the original helper rows first, followed by the phase rows. -/
def rawRow {L : ℕ} (i : Fin (D.d + L)) (p : RowPoint ι L) : ℂ :=
  Fin.append (fun j : Fin D.d => mixedChar (D.frequencies j) p.1)
    (fun j : Fin L => phaseRow j p) i

theorem measurable_rawRow {L : ℕ} (i : Fin (D.d + L)) : Measurable (D.rawRow i) := by
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · have heq : D.rawRow (Fin.castAdd L j) =
        (fun p : RowPoint ι L => mixedChar (D.frequencies j) p.1) := by
      funext p
      simp [rawRow]
    rw [heq]
    exact (continuous_mixedChar (D.frequencies j)).measurable.comp measurable_fst
  · have heq : D.rawRow (Fin.natAdd D.d j) = phaseRow (ι := ι) j := by
      funext p
      simp [rawRow, phaseRow]
    rw [heq]
    exact ((fourier 1).continuous.comp ((continuous_apply j).comp
      (continuous_snd : Continuous (Prod.snd : RowPoint ι L → UnitAddTorus (Fin L))))).measurable

theorem norm_rawRow {L : ℕ} (i : Fin (D.d + L)) (p : RowPoint ι L) : ‖D.rawRow i p‖ = 1 := by
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp [rawRow]
  · simp [rawRow, phaseRow, fourier_apply]

def rawSelected {L r n : ℕ} (S : Scalar.Data r n)
    (ji : Fin (n + 1) × Fin (D.d + L)) (p : SelectedPoint ι L r) : ℂ :=
  D.rawRow ji.2 (p.1, p.2.1) * torusChar (S.augMode ji.1) p.2.2

theorem measurable_rawSelected {L r n : ℕ} (S : Scalar.Data r n)
    (ji : Fin (n + 1) × Fin (D.d + L)) : Measurable (D.rawSelected S ji) :=
  ((D.measurable_rawRow ji.2).comp (measurable_fst.prodMk measurable_snd.fst)).mul
    ((continuous_torusChar _).measurable.comp measurable_snd.snd)

theorem norm_rawSelected {L r n : ℕ} (S : Scalar.Data r n)
    (ji : Fin (n + 1) × Fin (D.d + L)) (p : SelectedPoint ι L r) :
    ‖D.rawSelected S ji p‖ = 1 := by
  rw [rawSelected, norm_mul, D.norm_rawRow, norm_torusChar, mul_one]

def rowReferenceGram (L : ℕ) : Matrix (Fin (D.d + L)) (Fin (D.d + L)) ℂ :=
  fun i j => ∫ p, conj (D.rawRow i p) * D.rawRow j p ∂ρ.prod (torusHaar (Fin L))

def rowSeedGram (L : ℕ) {m : ℝ} (hm : 0 < m) (hm' : m ≤ ((1 : ℝ) / 2) ^ L) :
    Matrix (Fin (D.d + L)) (Fin (D.d + L)) ℂ :=
  fun i j => ∫ p, ((D.seedFiber L hm hm').weight p : ℂ) *
    (conj (D.rawRow i p) * D.rawRow j p) ∂ρ.prod (torusHaar (Fin L))

def selectedLp {L r n : ℕ} {m : ℝ} (hm : 0 < m) (hm' : m ≤ ((1 : ℝ) / 2) ^ L)
    (S : Scalar.Data r n) (ji : Fin (n + 1) × Fin (D.d + L)) :
    Lp ℂ 2 (((D.seedFiber L hm hm').selected S).normalizedMeasure ρ) :=
  lift₂ _ (D.rawSelected S ji) (D.measurable_rawSelected S ji) 1
    (fun p => (D.norm_rawSelected S ji p).le)

private theorem scalar_reference_pairing {r n : ℕ} (S : Scalar.Data r n) (i j : Fin (n + 1)) :
    (∫ y, conj (torusChar (S.augMode i) y) * torusChar (S.augMode j) y ∂torusHaar (Fin r)) =
      if i = j then 1 else 0 := by
  simp_rw [← torusChar_neg, ← torusChar_add]
  rw [integral_torusChar]
  have h : -S.augMode i + S.augMode j = 0 ↔ i = j := by
    rw [neg_add_eq_zero, S.augMode_inj.eq_iff]
  simp [h]

private theorem scalar_weighted_pairing {r n : ℕ} (S : Scalar.Data r n) (i j : Fin (n + 1)) :
    (∫ y, (S.w y : ℂ) * (conj (torusChar (S.augMode i) y) * torusChar (S.augMode j) y)
      ∂torusHaar (Fin r)) = S.complexGram i j := by
  simp only [Scalar.Data.complexGram, Scalar.charGram, Matrix.of_apply, mul_assoc]

/-- The selected Gram in row and column coordinates before any row eigenspace
change. The two reference measures and the canonic normalization are explicit. -/
theorem selectedGram_formula {L r n : ℕ} {m : ℝ} (hm : 0 < m)
    (hm' : m ≤ ((1 : ℝ) / 2) ^ L) (S : Scalar.Data r n)
    (k l : Fin (n + 1)) (i j : Fin (D.d + L)) :
    Matrix.gram ℂ (D.selectedLp hm hm' S) (k, i) (l, j) =
      (((D.seedFiber L hm hm').selected S).mass : ℂ)⁻¹ *
       (D.rowSeedGram L hm hm' i j * (if k = l then 1 else 0) +
        (D.rowReferenceGram L i j - D.rowSeedGram L hm hm' i j) * S.complexGram k l) := by
  let U := D.seedFiber L hm hm'
  let W := U.selected S
  let f (p : RowPoint ι L) := conj (D.rawRow i p) * D.rawRow j p
  let g (y : UnitAddTorus (Fin r)) := conj (torusChar (S.augMode k) y) * torusChar (S.augMode l) y
  have hf : Integrable f (ρ.prod (torusHaar (Fin L))) :=
    Integrable.of_bound ((Complex.continuous_conj.measurable.comp (D.measurable_rawRow i)).mul
      (D.measurable_rawRow j)).aestronglyMeasurable 1 (Eventually.of_forall fun p => by
        simp [f, D.norm_rawRow])
  have hg : Integrable g (torusHaar (Fin r)) :=
    Integrable.of_bound ((Complex.continuous_conj.measurable.comp (continuous_torusChar _).measurable).mul
      (continuous_torusChar _).measurable).aestronglyMeasurable 1 (Eventually.of_forall fun y => by simp [g])
  rw [Matrix.gram_apply, selectedLp, selectedLp, inner_lift₂]
  rw [W.integral_normalizedMeasure ρ]
  let F (p : SelectedPoint ι L r) : ℂ :=
    (W.weight p : ℂ) * f (p.1, p.2.1) * g p.2.2
  have hD (p : SelectedPoint ι L r) :
      W.density p • (conj (D.rawSelected S (k, i) p) * D.rawSelected S (l, j) p) =
        (↑W.mass : ℂ)⁻¹ * F p := by
    rw [FiberWeight.density, Complex.real_smul]
    dsimp [F, rawSelected, f, g]
    push_cast
    rw [map_mul]
    ring
  rw [integral_congr_ae (Eventually.of_forall hD), integral_const_mul]
  have hassoc := measurePreserving_prodAssoc ρ (torusHaar (Fin L)) (torusHaar (Fin r))
  rw [← hassoc.integral_comp' F]
  change (↑W.mass : ℂ)⁻¹ *
      (∫ p, ((S.w p.2 + (1 - S.w p.2) * U.weight p.1 : ℝ) : ℂ) * f p.1 * g p.2
        ∂(ρ.prod (torusHaar (Fin L))).prod (torusHaar (Fin r))) = _
  rw [integral_selected_pairing hf hg U.measurable_weight S.measurable_w
    (fun p => ⟨(U.weight_pos p).le, U.weight_le_one p⟩) (fun y => ⟨S.w_nonneg y, S.le_one y⟩),
    show (∫ y, g y ∂torusHaar (Fin r)) = _ from scalar_reference_pairing S k l,
    show (∫ y, (S.w y : ℂ) * g y ∂torusHaar (Fin r)) = _ from scalar_weighted_pairing S k l]
  rfl

end

end SchauderBasisOrbits.DirectionalInput

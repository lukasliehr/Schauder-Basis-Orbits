module

public import LeanCode.Directional.Seed
public import LeanCode.Scalar.Data
public import LeanCode.Measure.PiProducts

@[expose] public section

open Filter Function MeasureTheory
open scoped ENNReal BigOperators ComplexConjugate

namespace SchauderBasisOrbits

noncomputable section

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {ν : Measure Y} [IsProbabilityMeasure ν] {r n : ℕ}

namespace FiberWeight

/-- Blend the scalar weight with the seed, retaining a constant fiber mass. -/
def selected (U : FiberWeight X ν) (S : Scalar.Data r n) :
    FiberWeight X (ν.prod (torusHaar (Fin r))) where
  weight := fun z => S.w z.2.2 + (1 - S.w z.2.2) * U.weight (z.1, z.2.1)
  measurable_weight := by
    have hs : Measurable (fun z : X × (Y × UnitAddTorus (Fin r)) => S.w z.2.2) :=
      S.measurable_w.comp measurable_snd.snd
    have hu : Measurable (fun z : X × (Y × UnitAddTorus (Fin r)) => U.weight (z.1, z.2.1)) :=
      U.measurable_weight.comp (measurable_fst.prodMk measurable_snd.fst)
    exact hs.add ((measurable_const.sub hs).mul hu)
  weight_pos z :=
    add_pos_of_pos_of_nonneg (S.lower_pos.trans_le (S.lower_le z.2.2))
      (mul_nonneg (sub_nonneg.mpr (S.le_one _)) (U.weight_pos _).le)
  weight_le_one z := by
    have hh := mul_le_of_le_one_right (sub_nonneg.mpr (S.le_one z.2.2))
      (U.weight_le_one (z.1, z.2.1))
    linarith
  mass := S.mass + (1 - S.mass) * U.mass
  mass_pos := add_pos_of_pos_of_nonneg S.mass_pos
    (mul_nonneg (sub_nonneg.mpr S.mass_le_one) U.mass_pos.le)
  fiber_mass x := by
    have hU : Integrable (fun y => U.weight (x, y)) ν :=
      Integrable.of_bound (U.measurable_weight.comp measurable_prodMk_left).aestronglyMeasurable 1
        (Eventually.of_forall fun y => by
          rw [Real.norm_of_nonneg (U.weight_pos _).le]
          exact U.weight_le_one _)
    have hS : Integrable S.w (torusHaar (Fin r)) := S.integrable_w
    have hSc : Integrable (fun z => 1 - S.w z) (torusHaar (Fin r)) :=
      (integrable_const (1 : ℝ)).sub hS
    have hI := (integrable_const (μ := ν) (1 : ℝ)).mul_prod hS
    have hJ := hU.mul_prod hSc
    have hEq (z : Y × UnitAddTorus (Fin r)) :
        S.w z.2 + (1 - S.w z.2) * U.weight (x, z.1) =
        (1 : ℝ) * S.w z.2 + U.weight (x, z.1) * (1 - S.w z.2) := by ring
    rw [integral_congr_ae (Eventually.of_forall hEq), integral_add hI hJ,
      integral_prod_mul (fun _ => (1 : ℝ)) S.w,
      integral_prod_mul (fun y => U.weight (x, y)) (fun z => 1 - S.w z),
      U.fiber_mass, integral_sub (integrable_const (1 : ℝ)) hS]
    change (∫ _ : Y, (1 : ℝ) ∂ν) * S.mass +
      U.mass * ((∫ _ : UnitAddTorus (Fin r), (1 : ℝ) ∂torusHaar (Fin r)) - S.mass) = _
    simp [mul_comm U.mass]

theorem selected_mass (U : FiberWeight X ν) (S : Scalar.Data r n) :
    (U.selected S).mass = 1 - (1 - U.mass) * S.loss := by
  change S.mass + (1 - S.mass) * U.mass = 1 - (1 - U.mass) * (1 - S.mass)
  ring

theorem selected_lower (U : FiberWeight X ν) (S : Scalar.Data r n)
    (z : X × (Y × UnitAddTorus (Fin r))) :
    S.lower ≤ (U.selected S).weight z :=
  (S.lower_le _).trans (le_add_of_nonneg_right
    (mul_nonneg (sub_nonneg.mpr (S.le_one _)) (U.weight_pos _).le))

end FiberWeight

/-- The unnormalized selected pairings factor into one reference and one seed
pairing on rows, and one reference and one weighted pairing on columns. -/
theorem integral_selected_pairing {μ : Measure X} [IsFiniteMeasure μ]
    {κ : Measure Y} [IsFiniteMeasure κ]
    {a : X → ℂ} {b : Y → ℂ} {e : X → ℝ} {w : Y → ℝ}
    (ha : Integrable a μ) (hb : Integrable b κ)
    (he : Measurable e) (hw : Measurable w) (heB : ∀ x, 0 ≤ e x ∧ e x ≤ 1)
    (hwB : ∀ y, 0 ≤ w y ∧ w y ≤ 1) :
    ∫ z, ((w z.2 + (1 - w z.2) * e z.1 : ℝ) : ℂ) * a z.1 * b z.2 ∂μ.prod κ =
      (∫ x, (e x : ℂ) * a x ∂μ) * (∫ y, b y ∂κ) +
      ((∫ x, a x ∂μ) - ∫ x, (e x : ℂ) * a x ∂μ) * (∫ y, (w y : ℂ) * b y ∂κ) := by
  have hEA : Integrable (fun x => (e x : ℂ) * a x) μ :=
    ha.bdd_mul he.complex_ofReal.aestronglyMeasurable (Eventually.of_forall fun x => by
      rw [Complex.norm_real, Real.norm_of_nonneg (heB x).1]
      exact (heB x).2)
  have hWB : Integrable (fun y => (w y : ℂ) * b y) κ :=
    hb.bdd_mul hw.complex_ofReal.aestronglyMeasurable (Eventually.of_forall fun y => by
      rw [Complex.norm_real, Real.norm_of_nonneg (hwB y).1]
      exact (hwB y).2)
  have hEq (z : X × Y) : ((w z.2 + (1 - w z.2) * e z.1 : ℝ) : ℂ) * a z.1 * b z.2 =
      ((e z.1 : ℂ) * a z.1) * b z.2 +
        (a z.1 - (e z.1 : ℂ) * a z.1) * ((w z.2 : ℂ) * b z.2) := by
    push_cast
    ring
  have hA : Integrable (fun x => a x - (e x : ℂ) * a x) μ := ha.sub hEA
  rw [integral_congr_ae (Eventually.of_forall hEq),
    integral_add (hEA.mul_prod hb) (hA.mul_prod hWB),
    integral_prod_mul (fun x => (e x : ℂ) * a x) b,
    integral_prod_mul (fun x => a x - (e x : ℂ) * a x) (fun y => (w y : ℂ) * b y),
    integral_sub ha hEA]

namespace DirectionalInput

variable {ι : Type*} [Fintype ι]
variable {ρ : Measure (ℝ × UnitAddTorus ι)} [IsFiniteMeasure ρ] (D : DirectionalInput ρ)

/-- Polynomial realization of the selected weight on the old, phase and scalar coordinates. -/
def selectedPoly (L : ℕ) (m : ℝ) (S : Scalar.PolynomialData r n) :
    MixedPoly ((ι ⊕ Fin L) ⊕ Fin r) :=
  let w := padMixedPoly Function.Embedding.inr (torusPolyAsMixed S.poly)
  let b := padMixedPoly Function.Embedding.inl (D.seedPoly L m)
  w + (1 - w) * b

theorem eval_selectedPoly (L : ℕ) {m : ℝ} (hm : 0 < m) (hm' : m ≤ ((1 : ℝ)/2)^L)
    (S : Scalar.PolynomialData r n) (z : ℝ × UnitAddTorus ((ι ⊕ Fin L) ⊕ Fin r)) :
    evalMixedPoly (D.selectedPoly L m S) z =
      ((D.seedFiber L hm hm').selected S.toData).weight
        ((z.1, fun i => z.2 (Sum.inl (Sum.inl i))),
          (fun i => z.2 (Sum.inl (Sum.inr i)), fun i => z.2 (Sum.inr i))) := by
  simp only [selectedPoly, evalMixedPoly_add, evalMixedPoly_sub, evalMixedPoly_mul,
    evalMixedPoly_one, eval_padMixedPoly, eval_torusPolyAsMixed, eval_seedPoly, S.eval_poly]
  change _ = (↑(S.w _ + (1 - S.w _) * seedAt m (D.amplitude _) _) : ℂ)
  push_cast
  rfl

end DirectionalInput

end

end SchauderBasisOrbits

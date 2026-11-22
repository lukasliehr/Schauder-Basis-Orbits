module

public import LeanCode.Construction.LineStep
public import LeanCode.Fourier.Coordinates
public import LeanCode.Measure.Products

@[expose] public section

open Filter MeasureTheory Function
open scoped ENNReal Topology BigOperators ComplexConjugate

namespace SchauderBasisOrbits

noncomputable section

variable {ι : Type*} [Fintype ι]

/-- A finite ordered character system and an actual polynomial unit direction. -/
structure DirectionalInput (ρ : Measure (ℝ × UnitAddTorus ι)) [IsFiniteMeasure ρ] where
  d : ℕ
  d_pos : 0 < d
  frequencies : Fin d → MixedFreq ι
  independent : LinearIndependent ℂ (productFamily ρ frequencies)
  K : ℝ
  K_ge_one : 1 ≤ K
  prefix_bound : HPrefix (𝕜 := ℂ) (productFamily ρ frequencies) K
  coeff : Fin d → ℂ
  unit_direction : ‖synth (productFamily ρ frequencies) coeff‖ = 1

namespace DirectionalInput

variable {ρ : Measure (ℝ × UnitAddTorus ι)} [IsFiniteMeasure ρ] (D : DirectionalInput ρ)

def direction (z : ℝ × UnitAddTorus ι) : ℂ :=
  synth (fun i => mixedChar (D.frequencies i) z) D.coeff

def directionPoly : MixedPoly ι := ∑ i, AddMonoidAlgebra.single (D.frequencies i) (D.coeff i)

theorem eval_directionPoly (z : ℝ × UnitAddTorus ι) :
    evalMixedPoly D.directionPoly z = D.direction z := by
  rw [← mixedEvalHom_apply, directionPoly, map_sum]
  simp only [mixedEvalHom_apply, evalMixedPoly_single, direction, synth, smul_eq_mul]

theorem continuous_direction : Continuous D.direction := by
  rw [show D.direction = evalMixedPoly D.directionPoly from funext (fun z => (D.eval_directionPoly z).symm)]
  exact continuous_evalMixedPoly D.directionPoly

def coeffBound : ℝ := max 1 (∑ i, ‖D.coeff i‖)

theorem norm_direction_le (z : ℝ × UnitAddTorus ι) : ‖D.direction z‖ ≤ D.coeffBound := by
  unfold direction synth coeffBound
  calc
    _ ≤ ∑ i, ‖D.coeff i • mixedChar (D.frequencies i) z‖ := norm_sum_le ..
    _ ≤ _ := by simp

def seedScale : ℝ := (4 * D.coeffBound)⁻¹

theorem seedScale_pos : 0 < D.seedScale := by
  have h : 1 ≤ D.coeffBound := le_max_left ..
  unfold seedScale
  positivity

theorem seedScale_le : D.seedScale ≤ 1 / 4 := by
  unfold seedScale
  have h : 1 ≤ D.coeffBound := le_max_left ..
  rw [one_div]
  exact (inv_le_inv₀ (by linarith : 0 < 4 * D.coeffBound) (by norm_num : (0 : ℝ) < 4)).2 (by linarith)

def seedTheta : ℝ := D.seedScale ^ 2

theorem seedTheta_bounds : 0 < D.seedTheta ∧ D.seedTheta ≤ 1 / 16 := by
  unfold seedTheta
  exact ⟨sq_pos_of_pos D.seedScale_pos,
    (pow_le_pow_left₀ D.seedScale_pos.le D.seedScale_le 2).trans_eq (by norm_num)⟩

def amplitude (z : ℝ × UnitAddTorus ι) : ℂ := (D.seedScale : ℂ) * D.direction z

theorem norm_amplitude_le (z : ℝ × UnitAddTorus ι) : ‖D.amplitude z‖ ≤ 1 / 4 := by
  have hb : 0 < D.coeffBound := lt_of_lt_of_le zero_lt_one (le_max_left ..)
  rw [amplitude, norm_mul, Complex.norm_real, Real.norm_of_nonneg D.seedScale_pos.le]
  refine (mul_le_mul_of_nonneg_left (D.norm_direction_le z) D.seedScale_pos.le).trans_eq ?_
  unfold seedScale
  field_simp

end DirectionalInput

/-- The one-coordinate factor of the seed. -/
def phaseFactor (s : ℂ) (y : UnitAddCircle) : ℝ :=
  1 + 2 * (s * conj (fourier 1 y)).re

theorem continuous_phaseFactor (s : ℂ) : Continuous (phaseFactor s) := by
  unfold phaseFactor
  exact continuous_const.add (continuous_const.mul
    (Complex.continuous_re.comp (continuous_const.mul (Complex.continuous_conj.comp (fourier 1).continuous))))

theorem phaseFactor_bounds {s : ℂ} (hs : ‖s‖ ≤ 1 / 4) (y : UnitAddCircle) :
    1 / 2 ≤ phaseFactor s y ∧ phaseFactor s y ≤ 3 / 2 := by
  have hnorm : ‖s * conj (fourier 1 y)‖ = ‖s‖ := by
    rw [norm_mul, Complex.norm_conj, fourier_apply, Circle.norm_coe, mul_one]
  have h := abs_le.mp ((Complex.abs_re_le_norm _).trans (hnorm ▸ hs))
  unfold phaseFactor
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

theorem ofReal_phaseFactor (s : ℂ) (y : UnitAddCircle) :
    (phaseFactor s y : ℂ) = 1 + s * fourier (-1) y + conj s * fourier 1 y := by
  rw [phaseFactor, Complex.ofReal_add, Complex.ofReal_one, ← Complex.add_conj, map_mul, fourier_neg]
  simp only [starRingEnd_apply, star_star]
  ring

private theorem integral_circle_character (k : ℤ) :
    ∫ y : UnitAddCircle, fourier k y ∂AddCircle.haarAddCircle = if k = 0 then 1 else 0 := by
  let : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
  have ho : Orthonormal ℂ (fourierLp (T := 1) 2) := orthonormal_fourier
  have h := orthonormal_iff_ite.mp ho (0 : ℤ) k
  rw [ContinuousMap.inner_toLp] at h
  simpa only [fourier_zero, map_one, mul_one, eq_comm] using h

private theorem integrable_circle_character (k : ℤ) :
    Integrable (fourier k : UnitAddCircle → ℂ) AddCircle.haarAddCircle :=
  Integrable.of_bound (fourier k).continuous.aestronglyMeasurable 1
    (Eventually.of_forall fun y => by rw [fourier_apply, Circle.norm_coe])

theorem phaseFactor_fourier (s : ℂ) (k : ℤ) :
    ∫ y, (phaseFactor s y : ℂ) * fourier k y ∂AddCircle.haarAddCircle =
      (if k = 0 then 1 else 0) + s * (if k - 1 = 0 then 1 else 0) +
        conj s * (if k + 1 = 0 then 1 else 0) := by
  have h (y : UnitAddCircle) : (phaseFactor s y : ℂ) * fourier k y =
      fourier k y + s * fourier (k - 1) y + conj s * fourier (k + 1) y := by
    rw [ofReal_phaseFactor, add_mul, add_mul, one_mul, mul_assoc, mul_assoc, ← fourier_add,
      ← fourier_add, sub_eq_add_neg, add_comm (-1), add_comm 1]
  have h₀ : Integrable (fun y : UnitAddCircle => fourier k y) AddCircle.haarAddCircle :=
    integrable_circle_character k
  have h₁ : Integrable (fun y : UnitAddCircle => s * fourier (k - 1) y) AddCircle.haarAddCircle :=
    (integrable_circle_character (k - 1)).const_mul s
  have h₂ : Integrable (fun y : UnitAddCircle => conj s * fourier (k + 1) y) AddCircle.haarAddCircle :=
    (integrable_circle_character (k + 1)).const_mul (conj s)
  rw [integral_congr_ae (Eventually.of_forall h)]
  rw [integral_add (f := fun y => fourier k y + s * fourier (k - 1) y) (h₀.add h₁) h₂,
    integral_add h₀ h₁, integral_const_mul, integral_const_mul,
    integral_circle_character, integral_circle_character, integral_circle_character]

/-- The product seed at a fixed base point. -/
def seedAt {L : ℕ} (m : ℝ) (s : ℂ) (y : UnitAddTorus (Fin L)) : ℝ :=
  m * ∏ i, phaseFactor s (y i)

theorem seedAt_bounds {L : ℕ} {m : ℝ} (hm : 0 < m) (hm' : m ≤ ((1 : ℝ)/2) ^ L)
    {s : ℂ} (hs : ‖s‖ ≤ 1 / 4) (y : UnitAddTorus (Fin L)) :
    0 < seedAt m s y ∧ seedAt m s y ≤ 1 := by
  have hp (i : Fin L) : 0 < phaseFactor s (y i) := by linarith [(phaseFactor_bounds hs (y i)).1]
  have hfac (i : Fin L) : phaseFactor s (y i) ≤ 2 := by linarith [(phaseFactor_bounds hs (y i)).2]
  refine ⟨mul_pos hm (Finset.prod_pos fun i _ => hp i), ?_⟩
  have hup : (∏ i, phaseFactor s (y i)) ≤ (2 : ℝ) ^ L := by
    calc
      _ ≤ ∏ _ : Fin L, (2 : ℝ) :=
        Finset.prod_le_prod₀ (fun i _ => (hp i).le) (fun i _ => hfac i)
      _ = _ := by simp
  calc
    _ ≤ m * (2 : ℝ) ^ L := mul_le_mul_of_nonneg_left hup hm.le
    _ ≤ ((1 : ℝ)/2) ^ L * (2 : ℝ) ^ L := mul_le_mul_of_nonneg_right hm' (by positivity)
    _ = _ := by rw [← mul_pow]; norm_num

theorem integral_seedAt_fourier {L : ℕ} (m : ℝ) (s : ℂ) (k : Fin L → ℤ) :
    ∫ y, (seedAt m s y : ℂ) * torusChar k y ∂torusHaar (Fin L) =
      (m : ℂ) * ∏ i, ((if k i = 0 then 1 else 0) + s * (if k i - 1 = 0 then 1 else 0) +
        conj s * (if k i + 1 = 0 then 1 else 0)) := by
  have hf (y : UnitAddTorus (Fin L)) :
      (seedAt m s y : ℂ) * torusChar k y =
        (m : ℂ) * ∏ i, (phaseFactor s (y i) : ℂ) * fourier (k i) (y i) := by
    simp only [seedAt, torusChar, UnitAddTorus.mFourier, ContinuousMap.coe_mk,
      Complex.ofReal_mul, Complex.ofReal_prod, mul_assoc, Finset.prod_mul_distrib]
  rw [integral_congr_ae (Eventually.of_forall hf), integral_const_mul]
  change (m : ℂ) * (∫ y, ∏ i, (phaseFactor s (y i) : ℂ) * fourier (k i) (y i)
    ∂Measure.pi (fun _ : Fin L => AddCircle.haarAddCircle)) = _
  rw [integral_fintype_prod_eq_prod (μ := fun _ : Fin L => AddCircle.haarAddCircle)
    (fun i (y : UnitAddCircle) => (phaseFactor s y : ℂ) * fourier (k i) y)]
  simp only [phaseFactor_fourier]

theorem integral_seedAt {L : ℕ} (m : ℝ) (s : ℂ) :
    ∫ y, seedAt (L := L) m s y ∂torusHaar (Fin L) = m := by
  have h := integral_seedAt_fourier m s (0 : Fin L → ℤ)
  simp only [torusChar_zero, mul_one, Pi.zero_apply] at h
  norm_num at h
  exact_mod_cast h

theorem integral_seedAt_phase {L : ℕ} (m : ℝ) (s : ℂ) (i : Fin L) :
    ∫ y, (seedAt (L := L) m s y : ℂ) * fourier 1 (y i) ∂torusHaar (Fin L) = (m : ℂ) * s := by
  have h (y : UnitAddTorus (Fin L)) :
      fourier 1 (y i) = torusChar (Pi.single i (1 : ℤ)) y :=
    (UnitAddTorus.mFourier_single y i).symm
  simp_rw [h]
  rw [integral_seedAt_fourier]
  congr 1
  rw [Finset.prod_eq_single i]
  · norm_num [Pi.single_eq_same]
  · intro j _ hji
    norm_num [Pi.single_eq_of_ne hji]
  · simp

theorem seedAt_lower {L : ℕ} {m : ℝ} (hm : 0 ≤ m) {s : ℂ} (hs : ‖s‖ ≤ 1 / 4)
    (y : UnitAddTorus (Fin L)) :
    m * ((1 : ℝ) / 2) ^ L ≤ seedAt m s y := by
  unfold seedAt
  apply mul_le_mul_of_nonneg_left _ hm
  calc
    _ = ∏ _ : Fin L, ((1 : ℝ) / 2) := by simp
    _ ≤ _ := Finset.prod_le_prod₀ (fun _ _ => by norm_num)
      (fun i _ => (phaseFactor_bounds hs (y i)).1)

theorem integral_seedAt_phase_pair {L : ℕ} (m : ℝ) (s : ℂ) {i j : Fin L} (hij : i ≠ j) :
    ∫ y, (seedAt (L := L) m s y : ℂ) * (conj (fourier 1 (y i)) * fourier 1 (y j))
      ∂torusHaar (Fin L) = (m : ℂ) * (conj s * s) := by
  let k : Fin L → ℤ := -Pi.single i (1 : ℤ) + Pi.single j (1 : ℤ)
  have h (y : UnitAddTorus (Fin L)) : conj (fourier 1 (y i)) * fourier 1 (y j) = torusChar k y := by
    simp only [k, torusChar_add, torusChar_neg, torusChar, UnitAddTorus.mFourier_single]
  simp_rw [h]
  rw [integral_seedAt_fourier]
  congr 1
  let D : Finset (Fin L) := {i, j}
  rw [← Finset.prod_subset (Finset.subset_univ D)]
  · rw [Finset.prod_pair hij]
    have hi : k i = -1 := by simp [k, Pi.single_apply, hij]
    have hj : k j = 1 := by simp [k, Pi.single_apply, hij.symm]
    norm_num [hi, hj]
  · intro l _ hl
    have hli : l ≠ i := fun he => hl (by simp [D, he])
    have hlj : l ≠ j := fun he => hl (by simp [D, he])
    have hkl : k l = 0 := by simp [k, Pi.single_apply, hli, hlj]
    norm_num [hkl]

namespace DirectionalInput

variable {ρ : Measure (ℝ × UnitAddTorus ι)} [IsFiniteMeasure ρ] (D : DirectionalInput ρ)

/-- The product seed as a weight with a constant phase integral. -/
def seedFiber {m : ℝ} (L : ℕ) (hm : 0 < m) (hm' : m ≤ ((1 : ℝ) / 2) ^ L) :
    FiberWeight (ℝ × UnitAddTorus ι) (torusHaar (Fin L)) where
  weight := fun z => seedAt m (D.amplitude z.1) z.2
  measurable_weight := by
    have ha : Continuous D.amplitude := continuous_const.mul D.continuous_direction
    unfold seedAt phaseFactor
    apply Measurable.const_mul
    apply Finset.measurable_prod
    intro i _
    exact ((continuous_const.add (continuous_const.mul (Complex.continuous_re.comp
      ((ha.comp continuous_fst).mul (Complex.continuous_conj.comp
        ((fourier 1).continuous.comp ((continuous_apply i).comp continuous_snd)))))))
          : Continuous _).measurable
  weight_pos z := (seedAt_bounds hm hm' (D.norm_amplitude_le z.1) z.2).1
  weight_le_one z := (seedAt_bounds hm hm' (D.norm_amplitude_le z.1) z.2).2
  mass := m
  mass_pos := hm
  fiber_mass z := integral_seedAt m (D.amplitude z)

/-- The phase coordinate function. -/
def phaseRow {L : ℕ} (i : Fin L) (z : (ℝ × UnitAddTorus ι) × UnitAddTorus (Fin L)) : ℂ :=
  fourier 1 (z.2 i)

theorem seedFiber_mean_phase {m : ℝ} {L : ℕ} (hm : 0 < m)
    (hm' : m ≤ ((1 : ℝ) / 2) ^ L) (i : Fin L) (z : ℝ × UnitAddTorus ι) :
    (D.seedFiber L hm hm').mean (phaseRow (ι := ι) i) z = D.amplitude z := by
  have he (y : UnitAddTorus (Fin L)) :
      (D.seedFiber L hm hm').density (z, y) • phaseRow (ι := ι) i (z, y) =
        (m : ℂ)⁻¹ * ((seedAt m (D.amplitude z) y : ℂ) * fourier 1 (y i)) := by
    rw [FiberWeight.density, Complex.real_smul]
    dsimp [seedFiber, phaseRow]
    push_cast
    ring
  rw [FiberWeight.mean, integral_congr_ae (Eventually.of_forall he), integral_const_mul,
    integral_seedAt_phase, ← mul_assoc, inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hm.ne'), one_mul]

theorem seedFiber_mean_phase_pair {m : ℝ} {L : ℕ} (hm : 0 < m)
    (hm' : m ≤ ((1 : ℝ) / 2) ^ L) {i j : Fin L} (hij : i ≠ j) (z : ℝ × UnitAddTorus ι) :
    (D.seedFiber L hm hm').mean
      (fun p => conj (phaseRow (ι := ι) i p) * phaseRow (ι := ι) j p) z =
        conj (D.amplitude z) * D.amplitude z := by
  have he (y : UnitAddTorus (Fin L)) :
      (D.seedFiber L hm hm').density (z, y) •
        (conj (phaseRow (ι := ι) i (z, y)) * phaseRow (ι := ι) j (z, y)) =
        (m : ℂ)⁻¹ * ((seedAt m (D.amplitude z) y : ℂ) * (conj (fourier 1 (y i)) * fourier 1 (y j))) := by
    rw [FiberWeight.density, Complex.real_smul]
    dsimp [seedFiber, phaseRow]
    push_cast
    ring
  rw [FiberWeight.mean, integral_congr_ae (Eventually.of_forall he), integral_const_mul,
    integral_seedAt_phase_pair m (D.amplitude z) hij, ← mul_assoc,
    inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hm.ne'), one_mul]

/-- Polynomial for the seed, on the disjoint union of old and phase coordinates. -/
def seedPoly (L : ℕ) (m : ℝ) : MixedPoly (ι ⊕ Fin L) :=
  let amp := AddMonoidAlgebra.single 0 (D.seedScale : ℂ) *
    padMixedPoly (Function.Embedding.inl : ι ↪ ι ⊕ Fin L) D.directionPoly
  let phase (i : Fin L) : MixedPoly (ι ⊕ Fin L) :=
    AddMonoidAlgebra.single
      (padMixedFreq (Function.Embedding.inr : Fin L ↪ ι ⊕ Fin L) (0, Pi.single i 1)) 1
  AddMonoidAlgebra.single 0 (m : ℂ) *
    ∏ i : Fin L, (1 + amp * conjMixedPoly (phase i) + conjMixedPoly amp * phase i)

theorem eval_seedPoly {L : ℕ} (m : ℝ) (z : ℝ × UnitAddTorus (ι ⊕ Fin L)) :
    evalMixedPoly (D.seedPoly L m) z =
      (seedAt m (D.amplitude (z.1, z.2 ∘ Sum.inl)) (z.2 ∘ Sum.inr) : ℂ) := by
  rw [← mixedEvalHom_apply, seedPoly, map_mul, map_prod]
  simp only [mixedEvalHom_apply, evalMixedPoly_one, evalMixedPoly_add, evalMixedPoly_mul,
    evalMixedPoly_conj, evalMixedPoly_single, mixedChar_zero, mul_one,
    mixedChar_padMixedFreq, eval_padMixedPoly, eval_directionPoly]
  unfold seedAt
  push_cast
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  have hp : mixedChar (0, Pi.single i (1 : ℤ)) (z.1, z.2 ∘ Sum.inr) =
      fourier 1 (z.2 (Sum.inr i)) := by
    simp [mixedChar, torusChar, UnitAddTorus.mFourier_single]
  simp only [one_mul, show (⇑(Function.Embedding.inl : ι ↪ ι ⊕ Fin L)) = Sum.inl from rfl,
    show (⇑(Function.Embedding.inr : Fin L ↪ ι ⊕ Fin L)) = Sum.inr from rfl]
  rw [hp, ofReal_phaseFactor, fourier_neg]
  rfl

end DirectionalInput

end

end SchauderBasisOrbits

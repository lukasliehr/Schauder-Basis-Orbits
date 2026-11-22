module

public import LeanCode.Scalar.Data
public import LeanCode.Scalar.Budgets

@[expose] public section

open MeasureTheory Matrix Complex
open scoped ENNReal ComplexConjugate ComplexOrder MatrixOrder

namespace SchauderBasisOrbits.Scalar

local notation "𝕋" => UnitAddCircle

lemma haar_closedBall_eq {p : ℝ} (hp : p ≤ 1) :
    (@AddCircle.haarAddCircle 1 _) (Metric.closedBall 0 (p / 2)) = ENNReal.ofReal p := by
  have h := AddCircle.volume_closedBall (T := 1) (x := 0) (p / 2)
  rw [AddCircle.volume_eq_smul_haarAddCircle] at h
  simpa [show 2 * (p / 2) = p by ring, min_eq_right hp] using h

noncomputable local instance activationCircleMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

local instance activationCircleProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure (@AddCircle.haarAddCircle 1 _))

/-- A symmetric measurable activation set, with prescribed measure. -/
structure ActivationSet (p : ℝ) where
  carrier : Set 𝕋
  measurable_carrier : MeasurableSet carrier
  neg_mem : ∀ y, -y ∈ carrier ↔ y ∈ carrier
  measure_carrier : (volume : Measure 𝕋) carrier = ENNReal.ofReal p

/-- The closed ball of radius `p/2` realizes the symmetric rare arc. -/
noncomputable def rareArc {p : ℝ} (hp : p ≤ 1) : ActivationSet p where
  carrier := Metric.closedBall 0 (p / 2)
  measurable_carrier := measurableSet_closedBall
  neg_mem y := by simp [Metric.mem_closedBall, dist_zero_right]
  measure_carrier := haar_closedBall_eq hp

variable {r n : ℕ} (D : Data r n) {p : ℝ} (A : ActivationSet p)

/-- Activate the old weight only on the chosen rare set in the last coordinate. -/
noncomputable def activatedWeight (x : UnitAddTorus (Fin (r + 1))) : ℝ := by
  classical
  exact if x (Fin.last r) ∈ A.carrier then D.w (fun i => x i.castSucc) else 1

lemma measurable_activatedWeight : Measurable (activatedWeight D A) := by
  classical
  unfold activatedWeight
  have hcoord (j : Fin (r + 1)) : Measurable (fun x : UnitAddTorus (Fin (r + 1)) => x j) :=
    measurable_pi_apply j
  apply Measurable.ite (A.measurable_carrier.preimage (hcoord (Fin.last r)))
  · apply D.measurable_w.comp
    exact Measurable.of_eval (fun i => hcoord i.castSucc)
  · exact measurable_const

lemma lower_le_activatedWeight (x : UnitAddTorus (Fin (r + 1))) :
    D.lower ≤ activatedWeight D A x := by
  classical
  unfold activatedWeight
  split_ifs
  · exact D.lower_le _
  · exact D.lower_le_one

lemma activatedWeight_le_one (x : UnitAddTorus (Fin (r + 1))) :
    activatedWeight D A x ≤ 1 := by
  classical
  unfold activatedWeight
  split_ifs
  · exact D.le_one _
  · exact le_rfl

lemma activatedWeight_even (x : UnitAddTorus (Fin (r + 1))) :
    activatedWeight D A (-x) = activatedWeight D A x := by
  classical
  simp [activatedWeight, A.neg_mem, ← Pi.neg_def, D.even_w]

/-- One row of the activated family, with the old modes in their original coordinates. -/
def activationMode (row : Fin (n + 1)) (l : ℤ) : Fin (r + 1) → ℤ :=
  Fin.lastCases l (D.augMode row)

@[simp] lemma activationMode_last (row : Fin (n + 1)) (l : ℤ) :
    activationMode D row l (Fin.last r) = l := Fin.lastCases_last

@[simp] lemma activationMode_castSucc (row : Fin (n + 1)) (l : ℤ) (i : Fin r) :
    activationMode D row l i.castSucc = D.augMode row i := Fin.lastCases_castSucc _

lemma activationMode_inj : Function.Injective (fun q : Fin (n + 1) × ℤ =>
    activationMode D q.1 q.2) := by
  intro x y h
  apply Prod.ext
  · apply D.augMode_inj
    funext i
    simpa using congrFun h i.castSucc
  · simpa using congrFun h (Fin.last r)

@[simp] lemma activationMode_zero : activationMode D 0 0 = 0 := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp


lemma torusChar_activationMode (row : Fin (n + 1)) (l : ℤ)
    (x : UnitAddTorus (Fin (r + 1))) :
    torusChar (activationMode D row l) x =
      torusChar (D.augMode row) (fun i => x i.castSucc) * fourier l (x (Fin.last r)) := by
  simp only [torusChar, UnitAddTorus.mFourier, ContinuousMap.coe_mk, Fin.prod_univ_castSucc,
    activationMode_last, activationMode_castSucc]

/-- Number of nonconstant modes after activation by `m+1` distinct auxiliary modes. -/
def activatedCount (n m : ℕ) : ℕ := (n + 1) * (m + 1) - 1

lemma activatedCount_succ (n m : ℕ) : activatedCount n m + 1 = (n + 1) * (m + 1) := by
  unfold activatedCount
  exact Nat.sub_add_cancel (Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _))

/-- Decode the row-major augmented order. -/
def activationIndex (n m : ℕ) : Fin (activatedCount n m + 1) ≃ Fin (n + 1) × Fin (m + 1) :=
  (finCongr (activatedCount_succ n m)).trans finProdFinEquiv.symm

@[simp] lemma activationIndex_zero (n m : ℕ) : activationIndex n m 0 = (0, 0) := by
  apply finProdFinEquiv.injective
  simp [activationIndex, Fin.ext_iff]

variable {m : ℕ} (Y : Fin (m + 1) → ℤ)

/-- The augmented mode at a position of the new row-major family. -/
def activationList (i : Fin (activatedCount n m + 1)) : Fin (r + 1) → ℤ :=
  activationMode D (activationIndex n m i).1 (Y (activationIndex n m i).2)

lemma activationList_zero (hY₀ : Y 0 = 0) : activationList D Y 0 = 0 := by
  simp [activationList, hY₀]

lemma activationList_inj (hY : Function.Injective Y) : Function.Injective (activationList D Y) := by
  intro i j hij
  have h : ((activationIndex n m i).1, Y (activationIndex n m i).2) =
      ((activationIndex n m j).1, Y (activationIndex n m j).2) :=
    activationMode_inj D hij
  apply (activationIndex n m).injective
  have h₁ := congrArg (fun q : Fin (n + 1) × ℤ => q.1) h
  have h₂ := congrArg (fun q : Fin (n + 1) × ℤ => q.2) h
  exact Prod.ext h₁ (hY h₂)

/-- Extend a scalar system by one rare-activation variable and finitely many auxiliary modes. -/
noncomputable def activate (hY₀ : Y 0 = 0) (hY : Function.Injective Y) :
    Data (r + 1) (activatedCount n m) where
  size_pos := by
    have h := Nat.le_mul_of_pos_right (n := n + 1) (m := m + 1) (by positivity)
    have hin := D.size_pos
    unfold activatedCount
    omega
  w := activatedWeight D A
  measurable_w := measurable_activatedWeight D A
  lower := D.lower
  lower_pos := D.lower_pos
  lower_le := lower_le_activatedWeight D A
  le_one := activatedWeight_le_one D A
  even_w := activatedWeight_even D A
  mode := fun i => activationList D Y i.succ
  mode_inj := fun i j h => Fin.succ_injective _ (activationList_inj D Y hY h)
  mode_ne_zero := fun i h => by
    have h' := activationList_inj D Y hY (h.trans (activationList_zero D Y hY₀).symm)
    exact Fin.succ_ne_zero i h'

lemma activate_augMode (hY₀ : Y 0 = 0) (hY : Function.Injective Y)
    (i : Fin (activatedCount n m + 1)) :
    (activate D A Y hY₀ hY).augMode i = activationList D Y i := by
  refine Fin.cases ?_ (fun j => ?_) i
  · exact (activationList_zero D Y hY₀).symm
  · rfl


/-- In the activated datum, the mass is `1 - p * loss`. -/
lemma activate_mass (hp : 0 ≤ p) (hY₀ : Y 0 = 0) (hY : Function.Injective Y) :
    (activate D A Y hY₀ hY).mass = 1 - p * D.loss := by
  classical
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (r + 1) => 𝕋) (Fin.last r)
  let f : 𝕋 × UnitAddTorus (Fin r) → ℝ := fun q => if q.1 ∈ A.carrier then D.w q.2 else 1
  have hpres : MeasurePreserving e (volume : Measure (UnitAddTorus (Fin (r + 1))))
      ((volume : Measure 𝕋).prod volume) :=
    volume_preserving_piFinSuccAbove _ _
  have hf : Integrable f ((volume : Measure 𝕋).prod volume) := by
    apply Integrable.of_bound ?_ 1 (Filter.Eventually.of_forall fun q => ?_)
    · exact (Measurable.ite (A.measurable_carrier.preimage measurable_fst)
        (D.measurable_w.comp measurable_snd) measurable_const).aestronglyMeasurable
    · dsimp [f]
      split_ifs with h
      · simpa [Real.norm_eq_abs, abs_of_nonneg (D.w_nonneg q.2)] using D.le_one q.2
      · norm_num
  have hsplit (x : UnitAddTorus (Fin (r + 1))) : f (e x) = activatedWeight D A x := by
    have he : e x = (x (Fin.last r), fun i => x i.castSucc) := by
      simp [e, MeasurableEquiv.piFinSuccAbove]
      rfl
    rw [he]
    rfl
  change (∫ x, activatedWeight D A x) = _
  simp_rw [← hsplit]
  rw [hpres.integral_comp', integral_prod f hf]
  have hfiber (y : 𝕋) : (∫ x, f (y, x)) = if y ∈ A.carrier then D.mass else 1 := by
    by_cases h : y ∈ A.carrier <;> simp [f, h, Data.mass]
  simp_rw [hfiber]
  change (∫ y, A.carrier.piecewise (fun _ => D.mass) (fun _ => 1) y) = _
  rw [integral_piecewise A.measurable_carrier integrableOn_const integrableOn_const,
    setIntegral_const, setIntegral_const, probReal_compl_eq_one_sub A.measurable_carrier]
  have hp' : (volume : Measure 𝕋).real A.carrier = p := by
    rw [Measure.real, A.measure_carrier, ENNReal.toReal_ofReal hp]
  rw [hp', Data.loss]
  simp only [smul_eq_mul, mul_one]
  ring


noncomputable def activationGramEntry (i j : Fin (n + 1)) (y : 𝕋) : ℂ := by
  classical
  exact if y ∈ A.carrier then D.complexGram i j else (1 : Matrix _ _ ℂ) i j

/-- Integrating out the old coordinates gives either its original weighted Gram entry
or its reference Haar Gram entry, according to the new coordinate's activation. -/
lemma activate_complexGram (hY₀ : Y 0 = 0) (hY : Function.Injective Y)
    (i j : Fin (activatedCount n m + 1)) :
    (activate D A Y hY₀ hY).complexGram i j =
      ∫ y : 𝕋,
        activationGramEntry D A (activationIndex n m i).1 (activationIndex n m j).1 y *
        (conj (fourier (Y (activationIndex n m i).2) y) *
          fourier (Y (activationIndex n m j).2) y) := by
  classical
  let i₀ := (activationIndex n m i).1
  let j₀ := (activationIndex n m j).1
  let k := Y (activationIndex n m i).2
  let l := Y (activationIndex n m j).2
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (r + 1) => 𝕋) (Fin.last r)
  let w' : 𝕋 × UnitAddTorus (Fin r) → ℝ := fun q => if q.1 ∈ A.carrier then D.w q.2 else 1
  let f : 𝕋 × UnitAddTorus (Fin r) → ℂ := fun q =>
    ((w' q : ℝ) : ℂ) * conj (torusChar (D.augMode i₀) q.2) *
      torusChar (D.augMode j₀) q.2 * (conj (fourier k q.1) * fourier l q.1)
  have hpres : MeasurePreserving e (volume : Measure (UnitAddTorus (Fin (r + 1))))
      ((volume : Measure 𝕋).prod volume) :=
    volume_preserving_piFinSuccAbove _ _
  have hmeas : Measurable w' :=
    Measurable.ite (A.measurable_carrier.preimage measurable_fst)
      (D.measurable_w.comp measurable_snd) measurable_const
  have hfourier (ν : ℤ) : Measurable (fun y : 𝕋 => fourier ν y) :=
    (fourier ν).continuous.measurable
  have hnorm (ν : ℤ) (y : 𝕋) : ‖fourier ν y‖ = 1 := by
    rw [fourier_apply, Circle.norm_coe]
  have hf : Integrable f ((volume : Measure 𝕋).prod volume) := by
    apply Integrable.of_bound ?_ 1 (Filter.Eventually.of_forall fun q => ?_)
    · have hw : Measurable (fun q => (w' q : ℂ)) := Complex.continuous_ofReal.measurable.comp hmeas
      have hi := (continuous_torusChar (D.augMode i₀)).measurable.comp
        (measurable_snd : Measurable fun q : 𝕋 × UnitAddTorus (Fin r) => q.2)
      have hj := (continuous_torusChar (D.augMode j₀)).measurable.comp
        (measurable_snd : Measurable fun q : 𝕋 × UnitAddTorus (Fin r) => q.2)
      have hk := (hfourier k).comp (measurable_fst : Measurable fun q : 𝕋 × UnitAddTorus (Fin r) => q.1)
      have hl := (hfourier l).comp (measurable_fst : Measurable fun q : 𝕋 × UnitAddTorus (Fin r) => q.1)
      exact ((((hw.mul (Complex.continuous_conj.measurable.comp hi)).mul hj).mul
        ((Complex.continuous_conj.measurable.comp hk).mul hl))).aestronglyMeasurable
    · simp only [f, norm_mul, Complex.norm_real, Complex.norm_conj, norm_torusChar, hnorm,
        mul_one, Real.norm_eq_abs, w']
      split_ifs
      · simpa [abs_of_nonneg (D.w_nonneg q.2)] using D.le_one q.2
      · norm_num
  unfold Data.complexGram at ⊢
  simp only [charGram, Matrix.of_apply, activate_augMode, activationList, torusChar_activationMode]
  change (∫ x, _ ) = _
  have hsplit (x : UnitAddTorus (Fin (r + 1))) :
      f (e x) = (activatedWeight D A x : ℂ) *
        conj (torusChar (D.augMode i₀) (fun a => x a.castSucc) * fourier k (x (Fin.last r))) *
        (torusChar (D.augMode j₀) (fun a => x a.castSucc) * fourier l (x (Fin.last r))) := by
    have he : e x = (x (Fin.last r), fun a => x a.castSucc) := by
      simp [e, MeasurableEquiv.piFinSuccAbove]
      rfl
    rw [he]
    simp only [f, w', activatedWeight, map_mul]
    ring
  change (∫ x, (activatedWeight D A x : ℂ) *
        conj (torusChar (D.augMode i₀) (fun a => x a.castSucc) * fourier k (x (Fin.last r))) *
        (torusChar (D.augMode j₀) (fun a => x a.castSucc) * fourier l (x (Fin.last r)))) = _
  simp_rw [← hsplit]
  rw [hpres.integral_comp', integral_prod f hf]
  apply integral_congr_ae
  refine Filter.Eventually.of_forall (fun y => ?_)
  by_cases hy : y ∈ A.carrier
  · simp only [f, w', activationGramEntry, if_pos hy, integral_mul_const]
    rfl
  · simp only [f, w', activationGramEntry, if_neg hy, integral_mul_const]
    have hu := congrFun (congrFun (charGram_one D.augMode_inj) i₀) j₀
    simp only [charGram, Matrix.of_apply] at hu
    rw [hu]

end SchauderBasisOrbits.Scalar

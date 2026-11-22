module

public import LeanCode.Scalar.Data
public import LeanCode.Scalar.MatrixMix

@[expose] public section

open Matrix MeasureTheory Complex
open scoped MatrixOrder ComplexOrder ComplexConjugate InnerProductSpace ENNReal

namespace SchauderBasisOrbits.Scalar

namespace Data

variable {r n : ℕ} (D : Data r n)

lemma tailGram_le_one : D.tailGram ≤ 1 := by
  have h : (1 - D.gram).PosSemidef := Matrix.le_iff.mp D.gram_bounds.2
  have hsub := h.submatrix (Fin.succ : Fin n → Fin (n + 1))
  rw [Matrix.le_iff]
  convert hsub using 1
  ext i j
  simp [tailGram, Matrix.one_apply]

/-- Scalar response for a mixture with the Haar Gram. -/
noncomputable def response (β : ℝ) : ℝ :=
  (1 - β) ^ 2 * qform (gramMix D.tailGram β)⁻¹ D.meanColumn

lemma response_nonneg {β : ℝ} (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1) :
    0 ≤ D.response β :=
  mul_nonneg (sq_nonneg _)
    (qform_nonneg (gramMix_posDef D.tailGram_posDef hβ₀ hβ₁).inv.posSemidef _)

lemma response_antitoneOn : AntitoneOn D.response (Set.Icc 0 1) := by
  intro x hx y hy hxy
  have hxyM := gramMix_mono D.tailGram_le_one hxy
  have hxM := gramMix_posDef D.tailGram_posDef hx.1 hx.2
  have hyM := gramMix_posDef D.tailGram_posDef hy.1 hy.2
  unfold response
  exact mul_le_mul (pow_le_pow_left₀ (sub_nonneg.mpr hy.2) (sub_le_sub_left hxy _) 2)
    (qform_mono (matrix_inv_le_inv hxM hxyM) _)
    (qform_nonneg hyM.inv.posSemidef _) (sq_nonneg _)

lemma response_zero : D.response 0 = D.mass * D.gain / (1 + D.gain) := by
  let c := D.centerGram⁻¹ *ᵥ D.meanColumn
  have hA : D.centerGram *ᵥ c = D.meanColumn := by
    dsimp [c]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _
      ((Matrix.isUnit_iff_isUnit_det _).1 D.centerGram_posDef.isUnit), Matrix.one_mulVec]
  have hZ : D.gain = D.mass⁻¹ * (D.meanColumn ⬝ᵥ c) := D.gain_eq_centerGram_inv
  have hG : D.tailGram *ᵥ c = (1 + D.gain) • D.meanColumn := by
    funext i
    have hi := congrFun hA i
    simp only [D.centerGram_mulVec, Pi.smul_apply, smul_eq_mul] at hi ⊢
    rw [hZ]
    linarith only [hi, show (1 + D.mass⁻¹ * (D.meanColumn ⬝ᵥ c)) * D.meanColumn i =
      D.meanColumn i + D.mass⁻¹ * (D.meanColumn i * (D.meanColumn ⬝ᵥ c)) by ring]
  have hNZ : 1 + D.gain ≠ 0 := by linarith [D.gain_nonneg]
  have hGc : D.tailGram⁻¹ *ᵥ D.meanColumn = (1 + D.gain)⁻¹ • c := by
    apply D.tailGram_posDef.mulVec_injective
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _
      ((Matrix.isUnit_iff_isUnit_det _).1 D.tailGram_posDef.isUnit), Matrix.one_mulVec,
      Matrix.mulVec_smul, hG, smul_smul, inv_mul_cancel₀ hNZ, one_smul]
  simp only [response, sub_zero, one_pow, one_mul, gramMix, zero_smul, one_smul, zero_add,
    qform, RCLike.re_to_real, star_trivial, hGc, dotProduct_smul, smul_eq_mul, hZ]
  have hNZ' : 1 + D.mass⁻¹ * (D.meanColumn ⬝ᵥ c) ≠ 0 := hZ ▸ hNZ
  field_simp [D.mass_pos.ne', hNZ']


lemma gramMix_mulVec_cons (β s : ℝ) (c : Fin n → ℝ) :
    gramMix D.gram β *ᵥ Fin.cons s c =
      Fin.cons ((β + (1 - β) * D.mass) * s + (1 - β) * (D.meanColumn ⬝ᵥ c))
        (fun i => (1 - β) * (D.meanColumn i * s) + (gramMix D.tailGram β *ᵥ c) i) := by
  have h₀ : gramMix D.gram β *ᵥ Fin.cons s c =
      β • (Fin.cons s c : Fin (n + 1) → ℝ) + (1 - β) • (D.gram *ᵥ Fin.cons s c) := by
    simp only [gramMix, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
  have h₁ : gramMix D.tailGram β *ᵥ c = β • c + (1 - β) • (D.tailGram *ᵥ c) := by
    simp only [gramMix, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
  rw [h₀, h₁, D.gram_mulVec_cons]
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [Fin.cons_zero, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  · simp only [Fin.cons_succ, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring

/-- The response is strictly smaller than the mixture's mass, by a Schur complement test. -/
lemma response_lt_mix_mass {β : ℝ} (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1) :
    D.response β < 1 - (1 - β) * D.loss := by
  let q := (gramMix D.tailGram β)⁻¹ *ᵥ D.meanColumn
  let c := -(1 - β) • q
  let v : Fin (n + 1) → ℝ := Fin.cons 1 c
  have hq : gramMix D.tailGram β *ᵥ q = D.meanColumn := by
    rw [show q = (gramMix D.tailGram β)⁻¹ *ᵥ D.meanColumn from rfl, Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1
        (gramMix_posDef D.tailGram_posDef hβ₀ hβ₁).isUnit), Matrix.one_mulVec]
  have hc : gramMix D.tailGram β *ᵥ c = -(1 - β) • D.meanColumn := by
    dsimp [c]
    rw [Matrix.mulVec_smul, hq]
  have hv : v ≠ 0 := by
    intro h
    have hh := congrFun h 0
    simp [v] at hh
  have hval : gramMix D.gram β *ᵥ v =
      Fin.cons (β + (1 - β) * D.mass - D.response β) (0 : Fin n → ℝ) := by
    rw [show v = Fin.cons 1 c from rfl, D.gramMix_mulVec_cons, hc]
    congr 1
    · simp only [mul_one, c, dotProduct_smul, smul_eq_mul, response, qform, RCLike.re_to_real,
        star_trivial, q]
      ring
    · funext i
      simp only [mul_one, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      ring
  have hpos := qform_pos (gramMix_posDef D.gram_posDef hβ₀ hβ₁) hv
  rw [qform, hval] at hpos
  simp only [RCLike.re_to_real, star_trivial, dotProduct, Fin.sum_univ_succ, Fin.cons_zero,
    Fin.cons_succ, Pi.zero_apply, mul_zero, Finset.sum_const_zero, add_zero, v, one_mul] at hpos
  unfold loss
  nlinarith only [hpos]

/-- Enlarging a mixing parameter by `R` loses at most the factor `4R` in response,
as long as the enlarged parameter stays below one half. -/
lemma response_ratio {β R : ℝ} (hβ : 0 ≤ β) (hR : 1 ≤ R) (hRb : R * β ≤ 1 / 2) :
    D.response β / (4 * R) ≤ D.response (R * β) := by
  have hR₀ : 0 < R := by linarith
  have hb : β ≤ R * β := by nlinarith [mul_nonneg hβ (sub_nonneg.mpr hR)]
  have hb₁ : β ≤ 1 := by linarith
  have hRb₀ : 0 ≤ R * β := by positivity
  have hRb₁ : R * β ≤ 1 := by linarith
  have hM : gramMix D.tailGram (R * β) ≤ R • gramMix D.tailGram β := by
    rw [Matrix.le_iff]
    have heq : R • gramMix D.tailGram β - gramMix D.tailGram (R * β) =
        (R - 1) • D.tailGram := by
      unfold gramMix
      module
    rw [heq]
    exact D.tailGram_posDef.posSemidef.smul (sub_nonneg.mpr hR)
  have hInv := matrix_inv_le_inv (gramMix_posDef D.tailGram_posDef hRb₀ hRb₁) hM
  have hI : (R • gramMix D.tailGram β)⁻¹ = R⁻¹ • (gramMix D.tailGram β)⁻¹ := by
    let u : ℝˣ := Units.mk0 R hR₀.ne'
    have h := Matrix.inv_smul' (A := gramMix D.tailGram β) u
      ((Matrix.isUnit_iff_isUnit_det _).1 (gramMix_posDef D.tailGram_posDef hβ hb₁).isUnit)
    simpa [u, Units.smul_def, Units.val_inv_eq_inv_val] using h
  rw [hI] at hInv
  have hq := qform_mono hInv D.meanColumn
  rw [qform_smul] at hq
  have hfactor : (1 - β) ^ 2 / 4 ≤ (1 - R * β) ^ 2 := by
    have hl : (1 - β) / 2 ≤ 1 - R * β := by linarith
    have hs := pow_le_pow_left₀ (show 0 ≤ (1 - β) / 2 by linarith) hl 2
    nlinarith only [hs]
  have hq₀ := qform_nonneg (gramMix_posDef D.tailGram_posDef hβ hb₁).inv.posSemidef D.meanColumn
  rw [response, response]
  calc
    _ = ((1 - β) ^ 2 / 4) * (R⁻¹ * qform (gramMix D.tailGram β)⁻¹ D.meanColumn) := by ring
    _ ≤ (1 - R * β) ^ 2 * qform (gramMix D.tailGram (R * β))⁻¹ D.meanColumn :=
      mul_le_mul hfactor hq (mul_nonneg (inv_nonneg.mpr hR₀.le) hq₀) (sq_nonneg _)


noncomputable local instance responseCircleMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩

local instance responseCircleProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure (@AddCircle.haarAddCircle 1 _))

/-- The finite Fourier coefficients of the defect lose at most its total mass. -/
lemma meanColumn_qform_one_le_loss :
    qform (1 : Matrix (Fin n) (Fin n) ℝ) D.meanColumn ≤ D.loss := by
  let defect (y : UnitAddTorus (Fin r)) : ℝ := 1 - D.w y
  have hdmeas : Measurable defect := measurable_const.sub D.measurable_w
  have hd₀ (y : UnitAddTorus (Fin r)) : 0 ≤ defect y := sub_nonneg.mpr (D.le_one y)
  have hd₁ (y : UnitAddTorus (Fin r)) : defect y ≤ 1 := by dsimp [defect]; linarith [D.w_nonneg y]
  have hd_bound (y : UnitAddTorus (Fin r)) : ‖(defect y : ℂ)‖ ≤ 1 := by
    simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hd₀ y)] using hd₁ y
  let d := lift₂ volume (fun y => (defect y : ℂ)) (Complex.continuous_ofReal.measurable.comp hdmeas)
    1 hd_bound
  let v (i : Fin n) := UnitAddTorus.mFourierLp 2 (D.mode i)
  have hv : Orthonormal ℂ v := UnitAddTorus.orthonormal_mFourier.comp D.mode D.mode_inj
  have hcoeff (i : Fin n) : ⟪v i, d⟫_ℂ = -(D.meanColumn i : ℂ) := by
    have htriv := congrFun (congrFun (charGram_one D.augMode_inj) i.succ) 0
    simp only [charGram, Matrix.of_apply, Data.augMode_succ, Data.augMode_zero,
      Matrix.one_apply, Fin.succ_ne_zero, ite_false, torusChar_zero, ofReal_one, one_mul, mul_one] at htriv
    have hweighted : (∫ y, (D.w y : ℂ) * conj (torusChar (D.mode i) y)) =
        (D.meanColumn i : ℂ) := by
      rw [Data.meanColumn, ← complexify_apply, D.complexify_gram]
      simp [Data.complexGram, charGram]
    have hi := charGram_integrable (fun _ : UnitAddTorus (Fin r) => 1) measurable_const 1
      (by intro y; norm_num) (D.mode i) 0
    have hi' := charGram_integrable D.w D.measurable_w 1
      (fun y => by simpa [abs_of_nonneg (D.w_nonneg y)] using D.le_one y) (D.mode i) 0
    calc
      _ = ∫ y, conj (torusChar (D.mode i) y) * (defect y : ℂ) := by
        rw [L2.inner_def]
        apply integral_congr_ae
        filter_upwards [UnitAddTorus.coeFn_mFourierLp 2 (D.mode i),
          ae_lift₂ volume (fun y => (defect y : ℂ)) (Complex.continuous_ofReal.measurable.comp hdmeas)
            1 hd_bound] with y hy hd
        change ⟪(UnitAddTorus.mFourierLp 2 (D.mode i)) y,
          lift₂ volume _ _ 1 hd_bound y⟫_ℂ = _
        rw [hy, hd, RCLike.inner_apply']
      _ = (∫ y, conj (torusChar (D.mode i) y)) -
          (∫ y, (D.w y : ℂ) * conj (torusChar (D.mode i) y)) := by
        have hpointwise (y : UnitAddTorus (Fin r)) : conj (torusChar (D.mode i) y) * (defect y : ℂ) =
            conj (torusChar (D.mode i) y) - (D.w y : ℂ) * conj (torusChar (D.mode i) y) := by
          simp only [defect, Complex.ofReal_sub, Complex.ofReal_one]
          ring
        simp_rw [hpointwise]
        exact integral_sub (by simpa using hi) (by simpa using hi')
      _ = _ := by rw [htriv, hweighted, zero_sub]
  have hdf : ‖d‖ ^ 2 = ∫ y, defect y ^ 2 := by
    have hh : ⟪d, d⟫_ℂ = (↑(∫ y, defect y ^ 2) : ℂ) := by
      dsimp [d]
      rw [inner_lift₂, ← integral_complex_ofReal]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun y => by
        simp only [conj_ofReal, ← Complex.ofReal_mul, pow_two])
    have hr := congrArg RCLike.re hh
    rw [inner_self_eq_norm_sq] at hr
    exact hr
  have hbound : (∫ y, defect y ^ 2) ≤ D.loss := by
    have hdi : Integrable defect :=
      Integrable.of_bound hdmeas.aestronglyMeasurable 1
        (Filter.Eventually.of_forall (fun y => by
          simpa [Real.norm_eq_abs, abs_of_nonneg (hd₀ y)] using hd₁ y))
    have hdi' : Integrable (fun y => defect y ^ 2) :=
      Integrable.of_bound (hdmeas.pow_const 2).aestronglyMeasurable 1
        (Filter.Eventually.of_forall (fun y => by
          rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
          nlinarith [mul_le_mul_of_nonneg_left (hd₁ y) (hd₀ y)]))
    have hdif : (∫ y, defect y) = D.loss := by
      rw [show (∫ y, defect y) = ∫ y, (1 : ℝ) - D.w y from rfl,
        integral_sub (integrable_const _) D.integrable_w]
      simp [Data.loss, Data.mass]
    rw [← hdif]
    exact integral_mono hdi' hdi (fun y => by nlinarith [mul_le_mul_of_nonneg_left (hd₁ y) (hd₀ y)])
  have hB := hv.sum_inner_products_le (s := Finset.univ) d
  rw [hdf] at hB
  simp only [hcoeff, norm_neg, Complex.norm_real, Real.norm_eq_abs, sq_abs] at hB
  simp only [qform, RCLike.re_to_real, star_trivial, Matrix.one_mulVec, dotProduct, ← pow_two]
  exact hB.trans hbound

private lemma inverse_smul_pos {k : Type*} [Fintype k] [DecidableEq k] {B : Matrix k k ℝ}
    (hB : B.PosDef) {a : ℝ} (ha : 0 < a) : (a • B)⁻¹ = a⁻¹ • B⁻¹ := by
  let u : ℝˣ := Units.mk0 a ha.ne'
  have h := Matrix.inv_smul' (A := B) u ((Matrix.isUnit_iff_isUnit_det _).1 hB.isUnit)
  simpa [u, Units.smul_def, Units.val_inv_eq_inv_val] using h

/-- RP04's upper response endpoint, using the Haar Fourier bound on the defect. -/
lemma response_sqrt_loss_le (he : 0 < D.loss) :
    D.response (Real.sqrt D.loss) ≤ Real.sqrt D.loss := by
  let β := Real.sqrt D.loss
  have hβ : 0 < β := Real.sqrt_pos.mpr he
  have hβ_sq : β ^ 2 = D.loss := Real.sq_sqrt he.le
  have hβ₁ : β < 1 := by
    dsimp [β]
    calc
      _ < Real.sqrt 1 := Real.sqrt_lt_sqrt he.le D.loss_lt_one
      _ = 1 := Real.sqrt_one
  have hM : β • (1 : Matrix (Fin n) (Fin n) ℝ) ≤ gramMix D.tailGram β := by
    rw [Matrix.le_iff, gramMix, add_sub_cancel_left]
    exact D.tailGram_posDef.posSemidef.smul (sub_nonneg.mpr hβ₁.le)
  have hInv := matrix_inv_le_inv (Matrix.PosDef.one.smul hβ) hM
  rw [inverse_smul_pos Matrix.PosDef.one hβ, inv_one] at hInv
  have hq := qform_mono hInv D.meanColumn
  rw [qform_smul] at hq
  have hb := D.meanColumn_qform_one_le_loss
  have hu : qform ((gramMix D.tailGram β)⁻¹) D.meanColumn ≤ β := by
    refine hq.trans ((mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hβ.le)).trans ?_)
    rw [← hβ_sq, pow_two, ← mul_assoc, inv_mul_cancel₀ hβ.ne', one_mul]
  change (1 - β) ^ 2 * qform (gramMix D.tailGram β)⁻¹ D.meanColumn ≤ β
  refine (mul_le_mul_of_nonneg_left hu (sq_nonneg _)).trans ?_
  have hs : (1 - β) ^ 2 ≤ 1 := by
    simpa using pow_le_pow_left₀ (sub_nonneg.mpr hβ₁.le) (show 1 - β ≤ 1 by linarith) 2
  simpa using mul_le_mul_of_nonneg_right hs hβ.le

/-- RP04's lower response endpoint needs only the old Gram floor and the scalar gain. -/
lemma gain_div_eight_le_response_loss_sq (he : D.loss ≤ 1 / 2)
    (hfloor : (D.loss ^ 2) • 1 ≤ D.gram) :
    D.gain / (8 * (1 + D.gain)) ≤ D.response (D.loss ^ 2) := by
  let e := D.loss
  have he₀ : 0 ≤ e := D.loss_nonneg
  have he₂ : e ^ 2 ≤ 1 / 4 := by
    have h := pow_le_pow_left₀ he₀ he 2
    norm_num at h
    exact h
  have ht : (e ^ 2) • 1 ≤ D.tailGram := by
    have h := (Matrix.le_iff.mp hfloor).submatrix (Fin.succ : Fin n → Fin (n + 1))
    rw [Matrix.le_iff]
    convert h using 1
    ext i j
    simp [tailGram, Matrix.one_apply, e]
  have hle : gramMix D.tailGram (e ^ 2) ≤ (2 : ℝ) • D.tailGram := by
    rw [Matrix.le_iff]
    have hd : (2 : ℝ) • D.tailGram - gramMix D.tailGram (e ^ 2) =
        (D.tailGram - e ^ 2 • 1) + e ^ 2 • D.tailGram := by
      unfold gramMix
      module
    rw [hd]
    exact (Matrix.le_iff.mp ht).add (D.tailGram_posDef.posSemidef.smul (sq_nonneg e))
  have hM := gramMix_posDef D.tailGram_posDef (sq_nonneg e) (by linarith : e ^ 2 ≤ 1)
  have hi := matrix_inv_le_inv hM hle
  rw [inverse_smul_pos D.tailGram_posDef (by norm_num : 0 < (2 : ℝ))] at hi
  have hq := qform_mono hi D.meanColumn
  rw [qform_smul] at hq
  have hq₀ := qform_nonneg D.tailGram_posDef.inv.posSemidef D.meanColumn
  have hz : qform D.tailGram⁻¹ D.meanColumn = D.mass * D.gain / (1 + D.gain) := by
    simpa [response, gramMix] using D.response_zero
  have hm : 1 / 2 ≤ D.mass := by unfold Data.loss at he; linarith
  have hsf : 1 / 2 ≤ (1 - e ^ 2) ^ 2 := by
    have h := pow_le_pow_left₀ (by norm_num : 0 ≤ (3 / 4 : ℝ))
      (show 3 / 4 ≤ 1 - e ^ 2 by linarith) 2
    norm_num at h
    linarith
  have hg : 0 ≤ D.gain / (1 + D.gain) := by positivity [D.gain_nonneg]
  have hmass : (1 / 2) * (D.gain / (1 + D.gain)) ≤ qform D.tailGram⁻¹ D.meanColumn := by
    rw [hz, mul_div_assoc]
    exact mul_le_mul_of_nonneg_right hm hg
  change D.gain / (8 * (1 + D.gain)) ≤ (1 - e ^ 2) ^ 2 *
    qform (gramMix D.tailGram (e ^ 2))⁻¹ D.meanColumn
  have hn : 0 ≤ qform (gramMix D.tailGram (e ^ 2))⁻¹ D.meanColumn :=
    qform_nonneg hM.inv.posSemidef _
  calc
    _ = (1 / 2) * ((2 : ℝ)⁻¹ * ((1 / 2) * (D.gain / (1 + D.gain)))) := by
      rw [div_mul_eq_div_div]
      ring
    _ ≤ (1 - e ^ 2) ^ 2 * qform (gramMix D.tailGram (e ^ 2))⁻¹ D.meanColumn :=
      mul_le_mul hsf ((mul_le_mul_of_nonneg_left hmass (by norm_num)).trans hq)
        (by positivity) (sq_nonneg _)

end Data


/-- Choose a geometric-grid step with a substantial response drop while its previous
response stays strictly above the square-root threshold. -/
theorem exists_response_scale {e R : ℝ} {Φ : ℝ → ℝ}
    (he : 0 < e) (he₁ : e < 1) (hR : 2 ≤ R)
    (hlog : 8 * Real.log (4 * R) ≤ Real.log (1 / e))
    (hmono : AntitoneOn Φ (Set.Icc 0 1))
    (hl : e ^ (1 / 4 : ℝ) < Φ (e ^ 2))
    (hu : Φ (Real.sqrt e) ≤ Real.sqrt e)
    (hr : ∀ {β}, 0 ≤ β → R * β ≤ 1 / 2 → Φ β / (4 * R) ≤ Φ (R * β)) :
    ∃ m, m ∈ Set.Icc (e ^ 2 * R) (R * Real.sqrt e) ∧
      Real.sqrt e < Φ (m / R) ∧ Φ (m / R) ≤ e ^ (1 / 4 : ℝ) ∧
      Φ m ≤ R ^ (-(1 / 16 : ℝ)) * Φ (m / R) := by
  let L := Real.log (1 / e)
  let s := Real.sqrt e
  let q := e ^ (1 / 4 : ℝ)
  let x (k : ℕ) := e ^ 2 * R ^ k
  have hR₀ : 0 < R := by linarith
  have hR₁ : 1 < R := by linarith
  have hRlog := Real.log_pos hR₁
  have hs : 0 < s := Real.sqrt_pos.mpr he
  have hq : 0 < q := Real.rpow_pos_of_pos he _
  have hE : Real.log e = -L := by simp [L, one_div, Real.log_inv]
  have hS : Real.log s = -L / 2 := by rw [show s = Real.sqrt e from rfl, Real.log_sqrt he.le, hE]
  have hQ : Real.log q = -L / 4 := by
    dsimp [q]
    rw [Real.log_rpow he, hE]
    ring
  have hL : 0 < L := by linarith only [hE, Real.log_neg he he₁]
  have hlogR4 : 0 < Real.log (4 * R) := Real.log_pos (by linarith)
  have hlogR_le : Real.log R ≤ Real.log (4 * R) :=
    (Real.log_le_log_iff hR₀ (by positivity)).mpr (by linarith)
  have hRsmall : R * s ≤ 1 / 2 := by
    have hh : 4 * R * s ≤ 1 := by
      apply (Real.log_le_log_iff (by positivity) zero_lt_one).1
      rw [Real.log_mul (by positivity) hs.ne', Real.log_one, hS]
      linarith
    linarith
  have hqratio : s ≤ q / (4 * R) := by
    apply (Real.log_le_log_iff hs (by positivity)).1
    rw [hS, Real.log_div hq.ne' (by positivity), hQ]
    linarith
  have hsq : s ≤ q := hqratio.trans (by
    apply div_le_self hq.le
    linarith)
  have hq1 : q ≤ 1 := by
    apply (Real.log_le_log_iff hq zero_lt_one).1
    rw [hQ, Real.log_one]
    linarith
  have hs1 : s ≤ 1 := hsq.trans hq1
  have hxpos (k : ℕ) : 0 < x k := by dsimp [x]; positivity
  have hxmono : Monotone x := fun i j hij =>
    mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hR₁.le hij) (sq_nonneg e)
  have hxstep (k : ℕ) : x (k + 1) = R * x k := by dsimp [x]; rw [pow_succ]; ring
  have hxlog (k : ℕ) : Real.log (x k) = -2 * L + (k : ℝ) * Real.log R := by
    dsimp [x]
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow, hE]
    norm_num
  have hxs : x 0 < s := by
    apply (Real.log_lt_log_iff (hxpos _) hs).1
    rw [hxlog, hS]
    norm_num
    linarith
  have hx_ex : ∃ k : ℕ, s ≤ x k := by
    obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (s / e ^ 2) hR₁
    refine ⟨k, ?_⟩
    have ht : 0 < e ^ 2 := by positivity
    have h := (div_lt_iff₀ ht).mp hk
    exact (by simpa [x, mul_comm] using h : s < x k).le
  let K := Nat.find hx_ex
  have hK : s ≤ x K := Nat.find_spec hx_ex
  have hKplus : x K ≤ R * s ∧ (K : ℝ) ≤ (3 * L) / (2 * Real.log R) + 1 := by
    have hK₀ : K ≠ 0 := fun h => (not_le_of_gt hxs) (by simpa [h] using hK)
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hK₀
    have hprev : x k < s := lt_of_not_ge (Nat.find_min hx_ex (by omega : k < K))
    have hprevlog := (Real.log_lt_log_iff (hxpos k) hs).2 hprev
    rw [hxlog, hS] at hprevlog
    refine ⟨?_, ?_⟩
    · rw [hk, hxstep]
      exact mul_le_mul_of_nonneg_left hprev.le hR₀.le
    · rw [hk, Nat.cast_succ, add_le_add_iff_right, le_div_iff₀ (by positivity)]
      nlinarith only [hprevlog]
  have hx₁ (k : ℕ) (hk : k ≤ K) : x k ≤ 1 / 2 :=
    (hxmono hk).trans (hKplus.1.trans hRsmall)
  have hxmem (k : ℕ) (hk : k ≤ K) : x k ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨(hxpos k).le, (hx₁ k hk).trans (by norm_num)⟩
  have hφK : Φ (x K) ≤ s :=
    (hmono ⟨hs.le, hs1⟩ (hxmem K le_rfl) hK).trans hu
  have ha_ex : ∃ k, Φ (x k) ≤ q := ⟨K, hφK.trans hsq⟩
  have hb_ex : ∃ k, Φ (x k) ≤ s := ⟨K, hφK⟩
  let a := Nat.find ha_ex
  let b := Nat.find hb_ex
  have haK : a ≤ K := Nat.find_min' ha_ex (hφK.trans hsq)
  have hbK : b ≤ K := Nat.find_min' hb_ex hφK
  have haq : Φ (x a) ≤ q := Nat.find_spec ha_ex
  have hbs : Φ (x b) ≤ s := Nat.find_spec hb_ex
  have ha_ne : a ≠ 0 := by
    intro h
    have h' : Φ (e ^ 2) ≤ q := by simpa [h, x] using haq
    exact (not_lt_of_ge h') hl
  have has : q / (4 * R) < Φ (x a) := by
    obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero ha_ne
    have hj' : a = j + 1 := hj
    have hjφ : q < Φ (x j) :=
      lt_of_not_ge (Nat.find_min ha_ex (by omega : j < a))
    have haux : R * x j ≤ 1 / 2 := by
      rw [← hxstep, ← hj']
      exact hx₁ a haK
    rw [hj', hxstep]
    exact (div_lt_div_of_pos_right hjφ (by positivity)).trans_le (hr (hxpos j).le haux)
  have ha_s : s < Φ (x a) := hqratio.trans_lt has
  have hab : a < b := by
    by_contra! h
    exact (not_le_of_gt ha_s) ((hmono (hxmem b hbK) (hxmem a haK) (hxmono h)).trans hbs)
  let c : ℝ := R ^ (-(1 / 16 : ℝ))
  have hc : 0 < c := Real.rpow_pos_of_pos hR₀ _
  have hdrop : ∃ j : ℕ, a < j ∧ j ≤ b ∧ Φ (x j) ≤ c * Φ (x (j - 1)) := by
    by_contra! hdrop
    have hiter (j : ℕ) (hj : a + j ≤ b) : c ^ j * Φ (x a) ≤ Φ (x (a + j)) := by
      induction j with
      | zero => simp
      | succ j ih =>
        have h₁ : a < a + (j + 1) := by omega
        have h₂ := hdrop (a + (j + 1)) h₁ hj
        rw [show a + (j + 1) - 1 = a + j by omega] at h₂
        rw [pow_succ]
        exact (by
          rw [mul_right_comm, mul_comm (c ^ j * Φ (x a)) c]
          exact mul_le_mul_of_nonneg_left (ih (by omega)) hc.le :
            c ^ j * c * Φ (x a) ≤ c * Φ (x (a + j))).trans h₂.le
    have hb_lower := hiter (b - a) (by omega)
    rw [Nat.add_sub_of_le hab.le] at hb_lower
    have hbpos : 0 < Φ (x b) :=
      (mul_pos (pow_pos hc _) (hs.trans ha_s)).trans_le hb_lower
    have hlogb := (Real.log_le_log_iff hbpos hs).2 hbs
    have hloga := (Real.log_lt_log_iff (by positivity : 0 < q / (4 * R)) (hs.trans ha_s)).2 has
    have hlogab := (Real.log_le_log_iff (mul_pos (pow_pos hc _) (hs.trans ha_s)) hbpos).2 hb_lower
    rw [Real.log_mul (pow_ne_zero _ hc.ne') (hs.trans ha_s).ne', Real.log_pow,
      show Real.log c = -(1 / 16 : ℝ) * Real.log R from Real.log_rpow hR₀ _] at hlogab
    rw [hS] at hlogb
    rw [Real.log_div hq.ne' (by positivity), hQ] at hloga
    have hB : ((b - a : ℕ) : ℝ) ≤ (K : ℝ) := by
      exact_mod_cast (Nat.sub_le b a).trans hbK
    have hKlog := (le_div_iff₀ (show 0 < 2 * Real.log R by positivity)).mp
      (show (K : ℝ) - 1 ≤ 3 * L / (2 * Real.log R) by linarith [hKplus.2])
    nlinarith only [hlogb, hloga, hlogab, mul_le_mul_of_nonneg_right hB hRlog.le, hKlog,
      hlogR_le, hlogR4, hlog]
  obtain ⟨j, haj, hjb, hjφ⟩ := hdrop
  have hj₀ : 0 < j := by omega
  have hjK := hjb.trans hbK
  have hprev : j - 1 < b := by omega
  have hxf : x j / R = x (j - 1) := by
    nth_rw 1 [← Nat.sub_add_cancel (show 1 ≤ j by omega), hxstep]
    field_simp [hR₀.ne']
  refine ⟨x j, ⟨?_, (hxmono hjK).trans hKplus.1⟩, ?_, ?_, ?_⟩
  · have h := hxmono (show 1 ≤ j by omega)
    simpa [x] using h
  · rw [hxf]
    exact lt_of_not_ge (Nat.find_min hb_ex hprev)
  · rw [hxf]
    exact (hmono (hxmem a haK) (hxmem _ (by omega)) (hxmono (by omega))).trans haq
  · simpa only [hxf, c] using hjφ

end SchauderBasisOrbits.Scalar

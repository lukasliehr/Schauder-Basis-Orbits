module

public import LeanCode.Construction.ResidualGeometry
public import LeanCode.Measure.PiProducts
public import LeanCode.Fourier.Coordinates
public import LeanCode.Scalar.Data

@[expose] public section

open MeasureTheory Filter Matrix
open scoped BigOperators InnerProductSpace ComplexConjugate

noncomputable section

namespace SchauderBasisOrbits

namespace Scalar.Data

variable {r n : ℕ} (D : Data r n)

def fiberWeight (α : Type*) [MeasurableSpace α] : FiberWeight α (torusHaar (Fin r)) where
  weight p := D.w p.2
  measurable_weight := D.measurable_w.comp measurable_snd
  weight_pos y := D.lower_pos.trans_le (D.lower_le y.2)
  weight_le_one y := D.le_one y.2
  mass := D.mass
  mass_pos := D.mass_pos
  fiber_mass _ := rfl

theorem mean_fiberWeight_const {α : Type*} [MeasurableSpace α]
    (u : UnitAddTorus (Fin r) → ℂ) (s : α) :
    (D.fiberWeight α).mean (fun p ↦ u p.2) s = ∫ y, u y ∂D.normalizedMeasure := by
  rw [D.integral_normalizedMeasure, ← integral_smul]
  apply integral_congr_ae
  filter_upwards [] with y
  change (D.w y / D.mass) • u y = D.mass⁻¹ • D.w y • u y
  rw [smul_smul, div_eq_inv_mul]

/-- A linear combination of the nonconstant characters in a scalar packet. -/
def packetFunction (c : Fin n → ℝ) (y : UnitAddTorus (Fin r)) : ℂ :=
  ∑ i, (c i : ℂ) • torusChar (D.mode i) y

theorem continuous_packetFunction (c : Fin n → ℝ) : Continuous (D.packetFunction c) := by
  unfold packetFunction
  exact continuous_finsetSum _ fun i _ ↦ continuous_const.mul (continuous_torusChar _)

theorem norm_packetFunction_le (c : Fin n → ℝ) (y : UnitAddTorus (Fin r)) :
    ‖D.packetFunction c y‖ ≤ ∑ i, ‖c i‖ := by
  unfold packetFunction
  calc
    _ ≤ ∑ i, ‖(c i : ℂ) • torusChar (D.mode i) y‖ := norm_sum_le ..
    _ = _ := by simp

private theorem ae_augLp_zero :
    ⇑(D.augLp 0) =ᵐ[D.normalizedMeasure] (1 : UnitAddTorus (Fin r) → ℂ) := by
  refine (ae_lift₂ _ _ _ _ _).trans (Eventually.of_forall fun y ↦ ?_)
  simp [augMode]

private theorem ae_augLp_succ (i : Fin n) :
    ⇑(D.augLp i.succ) =ᵐ[D.normalizedMeasure] torusChar (D.mode i) := by
  refine (ae_lift₂ _ _ _ _ _).trans (Eventually.of_forall fun _ ↦ ?_)
  simp [augMode]

theorem integral_torusChar_normalized (i : Fin n) :
    (∫ y, torusChar (D.mode i) y ∂D.normalizedMeasure) = (D.normalizedMean i : ℂ) := by
  rw [← D.inner_augLp_zero_succ, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [D.ae_augLp_zero, D.ae_augLp_succ i] with y hz hs
  rw [hz, hs, RCLike.inner_apply']
  simp

theorem ae_centerLp (i : Fin n) :
    ⇑(D.centerLp i) =ᵐ[D.normalizedMeasure]
      fun y ↦ torusChar (D.mode i) y - (D.normalizedMean i : ℂ) := by
  unfold centerLp
  filter_upwards [Lp.coeFn_sub (D.augLp i.succ) ((D.normalizedMean i : ℂ) • D.augLp 0),
    Lp.coeFn_smul (D.normalizedMean i : ℂ) (D.augLp 0), D.ae_augLp_zero, D.ae_augLp_succ i]
    with y hsub hsmul hz hs
  simp only [hsub, Pi.sub_apply, hsmul, Pi.smul_apply, smul_eq_mul, hz, hs, Pi.one_apply, mul_one]

theorem integral_packetFunction (c : Fin n → ℝ) :
    (∫ y, D.packetFunction c y ∂D.normalizedMeasure) = ((D.normalizedMean ⬝ᵥ c : ℝ) : ℂ) := by
  unfold packetFunction
  rw [integral_finsetSum]
  · simp only [smul_eq_mul, integral_const_mul, D.integral_torusChar_normalized,
      dotProduct, Complex.ofReal_sum, Complex.ofReal_mul]
    exact Finset.sum_congr rfl fun i _ ↦ mul_comm _ _
  · intro i _
    exact (Integrable.of_bound (continuous_torusChar (D.mode i)).aestronglyMeasurable 1
      (Eventually.of_forall fun y ↦ (norm_torusChar _ y).le)).const_mul _

private theorem ae_synth_centerLp (c : Fin n → ℝ) :
    ⇑(synth D.centerLp (fun i ↦ (c i : ℂ))) =ᵐ[D.normalizedMeasure]
      fun y ↦ ∑ i, (c i : ℂ) • (torusChar (D.mode i) y - (D.normalizedMean i : ℂ)) := by
  unfold synth
  refine (Lp.coeFn_fun_finsetSum Finset.univ (fun i ↦ (c i : ℂ) • D.centerLp i)).trans ?_
  have h (i : Fin n) : ⇑((c i : ℂ) • D.centerLp i : Lp ℂ 2 D.normalizedMeasure)
      =ᵐ[D.normalizedMeasure]
      fun y ↦ (c i : ℂ) • (torusChar (D.mode i) y - (D.normalizedMean i : ℂ)) :=
    (Lp.coeFn_smul _ _).trans ((D.ae_centerLp i).mono fun y hy ↦
      congrArg (fun z : ℂ ↦ (c i : ℂ) • z) hy)
  filter_upwards [(Finset.eventually_all Finset.univ).mpr (fun i _ ↦ h i)] with y hy
  exact Finset.sum_congr rfl hy

theorem integral_packetFunction_variance (c : Fin n → ℝ) :
    (∫ y, ‖D.packetFunction c y - ((D.normalizedMean ⬝ᵥ c : ℝ) : ℂ)‖ ^ 2
      ∂D.normalizedMeasure) = qform D.normalizedGram c := by
  let g := synth D.centerLp (fun i ↦ (c i : ℂ))
  rw [← D.qform_centerLp_synth c, ← inner_self_eq_norm_sq (𝕜 := ℂ), L2.inner_def,
    ← integral_re (L2.integrable_inner (𝕜 := ℂ) g g)]
  apply integral_congr_ae
  filter_upwards [D.ae_synth_centerLp c] with y hy
  change _ = RCLike.re ⟪g y, g y⟫_ℂ
  rw [inner_self_eq_norm_sq]
  have hs : g y = D.packetFunction c y - ((D.normalizedMean ⬝ᵥ c : ℝ) : ℂ) := by
    rw [show g y = _ from hy]
    simp only [smul_eq_mul, mul_sub, Finset.sum_sub_distrib, packetFunction,
      dotProduct, Complex.ofReal_sum, Complex.ofReal_mul]
    congr 1
    exact Finset.sum_congr rfl fun i _ ↦ mul_comm (c i : ℂ) (D.normalizedMean i : ℂ)
  rw [hs]

theorem exists_packetFunction_mean_one_variance {z : ℝ} (hz : 0 < z) (hD : D.gain = z) :
    ∃ c : Fin n → ℝ,
      (∫ y, D.packetFunction c y ∂D.normalizedMeasure) = 1 ∧
      (∫ y, ‖D.packetFunction c y - 1‖ ^ 2 ∂D.normalizedMeasure) = 1 / z := by
  obtain ⟨c, hmean, hvar⟩ := D.exists_mean_one_variance_inv_gain (by rwa [hD])
  refine ⟨c, ?_, ?_⟩
  · rw [D.integral_packetFunction, hmean, Complex.ofReal_one]
  · convert D.integral_packetFunction_variance c using 2 <;> simp [hmean, hvar, hD]

end Scalar.Data

theorem exists_residual_gain {u c Nrm : ℝ} (hu : 0 < u) (hc : 0 < c) (hN : 0 ≤ Nrm) :
    ∃ z, 0 < z ∧ z < c ∧ z * Nrm < u := by
  have hp : 0 < 1 + Nrm := by positivity
  let m := min c (u / (1 + Nrm))
  have hpos : 0 < m := lt_min hc (div_pos hu hp)
  refine ⟨m / 2, by positivity, ?_, ?_⟩
  · exact (half_lt_self hpos).trans_le (min_le_left ..)
  · have h := (half_lt_self hpos).trans_le (min_le_right c (u / (1 + Nrm)))
    have h' := (lt_div_iff₀ hp).mp h
    calc
      _ ≤ (m / 2) * (1 + Nrm) := by gcongr; linarith
      _ < _ := h'

section TorusCopies

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]


/-- Include one block of coordinates in the product of coordinate sets. -/
def blockEmbedding (i : ι) : κ ↪ ι × κ :=
  ⟨fun j ↦ (i, j), fun _ _ h ↦ congrArg Prod.snd h⟩

def extendBlockMode (i : ι) (k : κ → ℤ) : ι × κ → ℤ :=
  padMode (blockEmbedding i) k

theorem extendBlockMode_ne_zero (i : ι) {k : κ → ℤ} (hk : k ≠ 0) :
    extendBlockMode i k ≠ 0 := by
  intro h
  apply hk
  funext j
  simpa [extendBlockMode] using congrFun h (blockEmbedding i j)

theorem extendBlockMode_injective (i : ι) : Function.Injective (extendBlockMode (κ := κ) i) :=
  padMode_injective (blockEmbedding i)

theorem extendBlockMode_ne_of_ne {i j : ι} (hij : i ≠ j) {k l : κ → ℤ}
    (hk : k ≠ 0) : extendBlockMode i k ≠ extendBlockMode j l := by
  intro h
  apply hk
  funext x
  have hx := congrFun h (blockEmbedding i x)
  rw [extendBlockMode, extendBlockMode, padMode_at, padMode_off] at hx
  · exact hx
  · rintro ⟨y, hy⟩
    exact hij (congrArg Prod.fst hy).symm

theorem torusChar_extendBlockMode (i : ι) (k : κ → ℤ) (x : UnitAddTorus (ι × κ)) :
    torusChar (extendBlockMode i k) x = torusChar k (fun j ↦ x (i, j)) :=
  torusChar_padMode (blockEmbedding i) k x

/-- Lift a scalar torus polynomial to a zero-real-frequency polynomial on one block. -/
def liftBlockPoly (i : ι) (p : TorusPoly κ) : MixedPoly (ι × κ) :=
  AddMonoidAlgebra.ofCoeff (p.coeff.mapDomain fun k ↦ (0, extendBlockMode i k))

theorem eval_liftBlockPoly (i : ι) (p : TorusPoly κ) (x : ℝ × UnitAddTorus (ι × κ)) :
    evalMixedPoly (liftBlockPoly i p) x = evalTorusPoly p (fun j ↦ x.2 (i, j)) := by
  rw [evalMixedPoly, liftBlockPoly, AddMonoidAlgebra.coeff_ofCoeff,
    Finsupp.sum_mapDomain_index (h := fun b (c : ℂ) ↦ c * mixedChar b x)
      (fun _ ↦ zero_mul _) (fun _ _ _ ↦ add_mul ..), evalTorusPoly]
  apply Finsupp.sum_congr
  intro k _
  simp [mixedChar, torusChar_extendBlockMode]

end TorusCopies

namespace Scalar.Data

variable {r n : ℕ} (D : Data r n)
variable (ι : Type*) [Fintype ι]

/-- The product weight for copies of one scalar packet, on a single flat torus. -/
def copiesFiberWeight : FiberWeight ℝ (torusHaar (ι × Fin r)) :=
  (FiberWeight.pi (fun _ : ι ↦ D.fiberWeight ℝ)).pullFiber
    (MeasurableEquiv.curry ι (Fin r) UnitAddCircle)
    (measurePreserving_curry_const ι (Fin r) UnitAddCircle AddCircle.haarAddCircle)

theorem copiesFiberWeight_apply (p : ℝ × UnitAddTorus (ι × Fin r)) :
    (D.copiesFiberWeight ι).weight p = ∏ i : ι, D.w (fun j ↦ p.2 (i, j)) := rfl

theorem copiesFiberWeight_lower (p : ℝ × UnitAddTorus (ι × Fin r)) :
    D.lower ^ Fintype.card ι ≤ (D.copiesFiberWeight ι).weight p := by
  rw [copiesFiberWeight_apply, ← Finset.card_univ, ← Finset.prod_const]
  exact Finset.prod_le_prod₀ (fun _ _ ↦ D.lower_pos.le) (fun _ _ ↦ D.lower_le _)

theorem copiesFiberWeight_mass :
    (D.copiesFiberWeight ι).mass = D.mass ^ Fintype.card ι := by
  change ∏ _i : ι, D.mass = _
  rw [Finset.prod_const, Finset.card_univ]

theorem copiesFiberWeight_loss_le :
    1 - (D.copiesFiberWeight ι).mass ≤ (Fintype.card ι : ℝ) * D.loss := by
  have h := FiberWeight.pi_mass_loss_le (fun _ : ι ↦ D.fiberWeight ℝ) (0 : ℝ)
  change 1 - (D.copiesFiberWeight ι).mass ≤ _ at h
  simpa only [fiberWeight, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, loss] using h

theorem mean_copies_coordinate (i : ι) {u : ℝ × UnitAddTorus (Fin r) → ℂ}
    (hu : Measurable u) (s : ℝ) :
    (D.copiesFiberWeight ι).mean (fun p ↦ u (p.1, fun j ↦ p.2 (i, j))) s =
      (D.fiberWeight ℝ).mean u s := by
  calc
    _ = (FiberWeight.pi (fun _ : ι ↦ D.fiberWeight ℝ)).mean (fun p ↦ u (p.1, p.2 i)) s :=
      FiberWeight.mean_pullFiber _ _ _ _ _
    _ = _ := FiberWeight.mean_pi_coordinate _ i hu s

theorem mean_copies_two_coordinates {i j : ι} (hij : i ≠ j)
    {u v : ℝ × UnitAddTorus (Fin r) → ℂ} (hu : Measurable u) (hv : Measurable v) (s : ℝ) :
    (D.copiesFiberWeight ι).mean (fun p ↦ u (p.1, fun k ↦ p.2 (i, k)) *
      v (p.1, fun k ↦ p.2 (j, k))) s =
      (D.fiberWeight ℝ).mean u s * (D.fiberWeight ℝ).mean v s := by
  calc
    _ = (FiberWeight.pi (fun _ : ι ↦ D.fiberWeight ℝ)).mean
        (fun p ↦ u (p.1, p.2 i) * v (p.1, p.2 j)) s :=
      FiberWeight.mean_pullFiber _ _ _ _ _
    _ = _ := FiberWeight.mean_pi_two_coordinates _ hij hu hv s

end Scalar.Data

namespace Scalar.PolynomialData

variable {r n : ℕ} (D : PolynomialData r n)
variable (ι : Type*) [Fintype ι] [DecidableEq ι]

def copiesPolynomial : MixedPoly (ι × Fin r) := ∏ i : ι, liftBlockPoly i D.poly

theorem eval_copiesPolynomial (p : ℝ × UnitAddTorus (ι × Fin r)) :
    evalMixedPoly (D.copiesPolynomial ι) p = ((D.toData.copiesFiberWeight ι).weight p : ℂ) := by
  rw [← mixedEvalHom_apply, copiesPolynomial, map_prod]
  simp only [mixedEvalHom_apply,
    eval_liftBlockPoly, D.eval_poly, Scalar.Data.copiesFiberWeight_apply, Complex.ofReal_prod]

end Scalar.PolynomialData

end SchauderBasisOrbits

module

public import LeanCode.Construction.ResidualCopies
public import LeanCode.Finite.BlockPrefixes

@[expose] public section

open MeasureTheory Filter Complex
open scoped InnerProductSpace BigOperators ComplexConjugate

noncomputable section

namespace SchauderBasisOrbits

/-- An actual bounded measurable representative on one scalar packet torus. -/
structure PacketRep (r : ℕ) where
  toFun : UnitAddTorus (Fin r) → ℂ
  measurable_toFun : Measurable toFun
  bound : ℝ
  norm_le : ∀ y, ‖toFun y‖ ≤ bound

instance {r : ℕ} : CoeFun (PacketRep r) (fun _ ↦ UnitAddTorus (Fin r) → ℂ) :=
  ⟨PacketRep.toFun⟩

namespace PacketRep

variable {r n : ℕ}

def char (k : Fin r → ℤ) : PacketRep r where
  toFun := torusChar k
  measurable_toFun := (continuous_torusChar k).measurable
  bound := 1
  norm_le _ := (norm_torusChar _ _).le

def scalarCombination (D : Scalar.Data r n) (c : Fin n → ℝ) : PacketRep r where
  toFun := D.packetFunction c
  measurable_toFun := (D.continuous_packetFunction c).measurable
  bound := ∑ j, ‖c j‖
  norm_le := D.norm_packetFunction_le c

def subConst (g : PacketRep r) (m : ℂ) : PacketRep r where
  toFun y := g y - m
  measurable_toFun := g.measurable_toFun.sub measurable_const
  bound := g.bound + ‖m‖
  norm_le y := (norm_sub_le _ _).trans (add_le_add (g.norm_le y) le_rfl)

theorem norm_subConst (g : PacketRep r) (m : ℂ) (y : UnitAddTorus (Fin r)) :
    ‖g.subConst m y‖ ≤ g.bound + ‖m‖ := (g.subConst m).norm_le y

def mean (D : Scalar.Data r n) (g : PacketRep r) : ℂ :=
  ∫ y, g y ∂D.normalizedMeasure

end PacketRep

namespace Scalar.Data

variable {r n : ℕ} (D : Data r n)

theorem mean_fiberWeight_separated (a : ℝ → ℂ) (g : UnitAddTorus (Fin r) → ℂ) (s : ℝ) :
    (D.fiberWeight ℝ).mean (fun p ↦ a p.1 * g p.2) s =
      a s * ∫ y, g y ∂D.normalizedMeasure := by
  rw [← D.mean_fiberWeight_const g s, FiberWeight.mean, FiberWeight.mean, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with y
  simp only [Complex.real_smul]
  ring

variable {ι : Type*} [Fintype ι]

/-- A scalar packet representative in a single auxiliary block, multiplied by a real character. -/
def copyTensorRaw (i : ι) (t : ℝ) (g : PacketRep r) (p : ℝ × UnitAddTorus (ι × Fin r)) : ℂ :=
  realChar t p.1 * g (fun j ↦ p.2 (i, j))

theorem measurable_copyTensorRaw (i : ι) (t : ℝ) (g : PacketRep r) :
    Measurable (copyTensorRaw i t g) := by
  exact ((continuous_realChar t).measurable.comp measurable_fst).mul
    (g.measurable_toFun.comp (measurable_pi_iff.mpr fun j ↦ (measurable_pi_apply (i, j)).comp measurable_snd))

theorem norm_copyTensorRaw_le (i : ι) (t : ℝ) (g : PacketRep r)
    (p : ℝ × UnitAddTorus (ι × Fin r)) : ‖copyTensorRaw i t g p‖ ≤ g.bound := by
  simpa [copyTensorRaw] using g.norm_le (fun j ↦ p.2 (i, j))

variable (ρ : Measure ℝ) [IsFiniteMeasure ρ]

def copyTensor (i : ι) (t : ℝ) (g : PacketRep r) :
    Lp ℂ 2 ((D.copiesFiberWeight ι).normalizedMeasure ρ) :=
  lift₂ _ (copyTensorRaw i t g) (measurable_copyTensorRaw i t g) g.bound
    (norm_copyTensorRaw_le i t g)

theorem ae_copyTensor (i : ι) (t : ℝ) (g : PacketRep r) :
    ⇑(D.copyTensor ρ i t g) =ᵐ[(D.copiesFiberWeight ι).normalizedMeasure ρ] copyTensorRaw i t g :=
  ae_lift₂ _ _ _ _ _

theorem mean_copyTensorRaw (i : ι) (t : ℝ) (g : PacketRep r) (s : ℝ) :
    (D.copiesFiberWeight ι).mean (copyTensorRaw i t g) s = realChar t s * g.mean D := by
  change (D.copiesFiberWeight ι).mean (fun p ↦ realChar t p.1 * g (fun j ↦ p.2 (i, j))) s = _
  calc
    _ = (D.fiberWeight ℝ).mean (fun p ↦ realChar t p.1 * g p.2) s :=
      D.mean_copies_coordinate ι i (((continuous_realChar t).measurable.comp measurable_fst).mul
        (g.measurable_toFun.comp measurable_snd)) s
    _ = _ := D.mean_fiberWeight_separated _ g s

theorem inner_copyTensor_same (i : ι) (t : ℝ) (g h : PacketRep r) :
    ⟪D.copyTensor ρ i t g, D.copyTensor ρ i t h⟫_ℂ =
      (∫ _ : ℝ, ∫ y, conj (g y) * h y ∂D.normalizedMeasure ∂ρ) := by
  simp only [copyTensor, inner_lift₂]
  have he (p : ℝ × UnitAddTorus (ι × Fin r)) :
      conj (copyTensorRaw i t g p) * copyTensorRaw i t h p =
        conj (g (fun j ↦ p.2 (i, j))) * h (fun j ↦ p.2 (i, j)) := by
    have hs : conj (realChar t p.1) * realChar t p.1 = 1 := by
      rw [← realChar_neg, ← realChar_add, neg_add_cancel, realChar_zero]
    simp only [copyTensorRaw, map_mul]
    calc
      _ = (conj (realChar t p.1) * realChar t p.1) *
          (conj (g (fun j ↦ p.2 (i, j))) * h (fun j ↦ p.2 (i, j))) := by ring
      _ = _ := by rw [hs, one_mul]
  simp_rw [he]
  let F : ℝ × UnitAddTorus (Fin r) → ℂ := fun z ↦ conj (g z.2) * h z.2
  let W := D.copiesFiberWeight ι
  have hf : Measurable F :=
    (Complex.continuous_conj.measurable.comp (g.measurable_toFun.comp measurable_snd)).mul
      (h.measurable_toFun.comp measurable_snd)
  change (∫ p : ℝ × UnitAddTorus (ι × Fin r), F (p.1, fun j ↦ p.2 (i, j)) ∂W.normalizedMeasure ρ) = _
  have hm : Measurable (fun p : ℝ × UnitAddTorus (ι × Fin r) ↦ F (p.1, fun j ↦ p.2 (i, j))) :=
    hf.comp (measurable_fst.prodMk (measurable_pi_iff.mpr
      fun j ↦ (measurable_pi_apply (i, j)).comp measurable_snd))
  rw [W.integral_normalizedMeasure_eq_mean ρ hm (B := g.bound * h.bound)]
  · apply integral_congr_ae
    filter_upwards [] with x
    rw [D.mean_copies_coordinate ι i hf]
    exact D.mean_fiberWeight_const (fun y ↦ conj (g y) * h y) x
  · intro p
    change ‖conj (g (fun j ↦ p.2 (i, j))) * h (fun j ↦ p.2 (i, j))‖ ≤ _
    rw [norm_mul, norm_conj]
    have hg := g.norm_le (fun j ↦ p.2 (i, j))
    exact mul_le_mul hg (h.norm_le _) (norm_nonneg _) ((norm_nonneg _).trans hg)

theorem inner_copyTensor_same_probability [IsProbabilityMeasure ρ]
    (i : ι) (t : ℝ) (g h : PacketRep r) :
    ⟪D.copyTensor ρ i t g, D.copyTensor ρ i t h⟫_ℂ =
      ∫ y, conj (g y) * h y ∂D.normalizedMeasure := by
  rw [D.inner_copyTensor_same, integral_const, probReal_univ, one_smul]

theorem inner_copyTensor_eq_zero_of_ne {i j : ι} (hij : i ≠ j)
    (t s : ℝ) (g h : PacketRep r) (hmean : g.mean D = 0 ∨ h.mean D = 0) :
    ⟪D.copyTensor ρ i t g, D.copyTensor ρ j s h⟫_ℂ = 0 := by
  rw [copyTensor, copyTensor, inner_lift₂]
  let W := D.copiesFiberWeight ι
  let u : ℝ × UnitAddTorus (Fin r) → ℂ := fun p ↦ realChar t p.1 * g p.2
  let v : ℝ × UnitAddTorus (Fin r) → ℂ := fun p ↦ realChar s p.1 * h p.2
  have hu : Measurable u := ((continuous_realChar t).measurable.comp measurable_fst).mul
    (g.measurable_toFun.comp measurable_snd)
  have hv : Measurable v := ((continuous_realChar s).measurable.comp measurable_fst).mul
    (h.measurable_toFun.comp measurable_snd)
  have hu' : Measurable (fun p ↦ conj (u p)) := Complex.continuous_conj.measurable.comp hu
  have hm : Measurable (fun p ↦ conj (copyTensorRaw i t g p) * copyTensorRaw j s h p) :=
    (Complex.continuous_conj.measurable.comp (measurable_copyTensorRaw i t g)).mul
      (measurable_copyTensorRaw j s h)
  rw [W.integral_normalizedMeasure_eq_mean ρ hm (B := g.bound * h.bound)]
  · calc
      _ = ∫ _ : ℝ, (0 : ℂ) ∂ρ := by
        apply integral_congr_ae
        filter_upwards [] with x
        change (D.copiesFiberWeight ι).mean (fun p ↦ conj (u (p.1, fun k ↦ p.2 (i, k))) *
          v (p.1, fun k ↦ p.2 (j, k))) x = 0
        rw [D.mean_copies_two_coordinates ι hij hu' hv,
          FiberWeight.mean_conj, show u = (fun p ↦ realChar t p.1 * g p.2) from rfl,
          show v = (fun p ↦ realChar s p.1 * h p.2) from rfl,
          D.mean_fiberWeight_separated, D.mean_fiberWeight_separated]
        change conj (realChar t x * g.mean D) * (realChar s x * h.mean D) = 0
        rcases hmean with hm | hm <;> simp [hm]
      _ = _ := integral_zero ℝ ℂ
  · intro p
    change ‖conj (copyTensorRaw i t g p) * copyTensorRaw j s h p‖ ≤ _
    rw [norm_mul, norm_conj]
    exact mul_le_mul (norm_copyTensorRaw_le i t g p) (norm_copyTensorRaw_le j s h p)
      (norm_nonneg _) ((norm_nonneg _).trans (norm_copyTensorRaw_le i t g p))

theorem inner_pullback_copyTensor_eq_zero (i : ι) (t : ℝ) (g : PacketRep r)
    (hmean : g.mean D = 0) (f : Lp ℂ 2 ρ) :
    ⟪(D.copiesFiberWeight ι).pullback ρ f, D.copyTensor ρ i t g⟫_ℂ = 0 := by
  rw [copyTensor, FiberWeight.inner_pullback_lift₂]
  suffices hm : lift₂ ρ ((D.copiesFiberWeight ι).mean (copyTensorRaw i t g))
      ((D.copiesFiberWeight ι).measurable_mean (measurable_copyTensorRaw i t g))
      g.bound ((D.copiesFiberWeight ι).norm_mean_le (measurable_copyTensorRaw i t g)
        (norm_copyTensorRaw_le i t g)) = 0 by rw [hm, inner_zero_right]
  apply Lp.ext
  refine (ae_lift₂ _ _ _ _ _).trans ?_
  refine EventuallyEq.trans ?_ (Lp.coeFn_zero ℂ 2 ρ).symm
  filter_upwards [] with x
  rw [D.mean_copyTensorRaw, hmean, mul_zero, Pi.zero_apply]

theorem ae_pullback_realChar (t : ℝ) :
    ⇑((D.copiesFiberWeight ι).pullback ρ (realCharLp ρ t)) =ᵐ[
      (D.copiesFiberWeight ι).normalizedMeasure ρ] fun p ↦ realChar t p.1 := by
  refine ((D.copiesFiberWeight ι).ae_pullback ρ (realCharLp ρ t)).trans ?_
  exact ((D.copiesFiberWeight ι).measurePreserving_fst ρ).quasiMeasurePreserving.ae_eq_comp
    (ae_realCharLp ρ t)

theorem copyTensor_decompose (i : ι) (t : ℝ) (g : PacketRep r) (m : ℂ) :
    D.copyTensor ρ i t g = D.copyTensor ρ i t (g.subConst m) +
      m • (D.copiesFiberWeight ι).pullback ρ (realCharLp ρ t) := by
  let p := D.copyTensor ρ i t (g.subConst m)
  let b := (D.copiesFiberWeight ι).pullback ρ (realCharLp ρ t)
  apply Lp.ext
  filter_upwards [D.ae_copyTensor ρ i t g, D.ae_copyTensor ρ i t (g.subConst m),
    D.ae_pullback_realChar ρ t (ι := ι), Lp.coeFn_add p (m • b), Lp.coeFn_smul m b]
    with x h₁ h₂ h₃ h₄ h₅
  change (D.copyTensor ρ i t g) x = (p + m • b) x
  simp only [h₁, h₄, Pi.add_apply, h₅, Pi.smul_apply, smul_eq_mul]
  change copyTensorRaw i t g x = (D.copyTensor ρ i t (g.subConst m)) x +
    m * ((D.copiesFiberWeight ι).pullback ρ (realCharLp ρ t)) x
  rw [h₂, h₃]
  simp only [copyTensorRaw, PacketRep.subConst, PacketRep.toFun]
  ring

theorem copyTensor_scalarCombination (i : ι) (t : ℝ) (c : Fin n → ℝ) :
    D.copyTensor ρ i t (PacketRep.scalarCombination D c) =
      synth (fun k ↦ D.copyTensor ρ i t (PacketRep.char (D.mode k))) (fun k ↦ (c k : ℂ)) := by
  classical
  let f := fun k : Fin n ↦ D.copyTensor ρ i t (PacketRep.char (D.mode k))
  apply Lp.ext
  refine (D.ae_copyTensor ρ i t (PacketRep.scalarCombination D c)).trans ?_
  refine Filter.EventuallyEq.symm ?_
  unfold synth
  refine (Lp.coeFn_fun_finsetSum Finset.univ (fun k ↦ (c k : ℂ) • f k)).trans ?_
  have hf (k : Fin n) : ⇑((c k : ℂ) • f k) =ᵐ[(D.copiesFiberWeight ι).normalizedMeasure ρ]
      fun p ↦ (c k : ℂ) * copyTensorRaw i t (PacketRep.char (D.mode k)) p :=
    (Lp.coeFn_smul _ _).trans ((D.ae_copyTensor ρ i t (PacketRep.char (D.mode k))).mono
      fun x hx ↦ congrArg (fun z : ℂ ↦ (c k : ℂ) * z) hx)
  filter_upwards [(Finset.eventually_all Finset.univ).mpr (fun k _ ↦ hf k)] with x hx
  simp only [copyTensorRaw, PacketRep.scalarCombination, PacketRep.toFun, packetFunction, smul_eq_mul,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [hx k hk]
  simp only [copyTensorRaw, PacketRep.char, PacketRep.toFun]
  ring

theorem norm_sq_copyTensor [IsProbabilityMeasure ρ] (i : ι) (t : ℝ) (g : PacketRep r) :
    ‖D.copyTensor ρ i t g‖ ^ 2 = ∫ y, ‖g y‖ ^ 2 ∂D.normalizedMeasure := by
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ), D.inner_copyTensor_same_probability ρ]
  have heq : (∫ y, conj (g y) * g y ∂D.normalizedMeasure) =
     ∫ y, (↑(‖g y‖ ^ 2) : ℂ) ∂D.normalizedMeasure := by
    apply integral_congr_ae
    filter_upwards [] with y
    rw [← RCLike.inner_apply', inner_self_eq_norm_sq_to_K, Complex.ofReal_pow]
    rfl
  rw [heq, integral_complex_ofReal]
  exact Complex.ofReal_re _

theorem integral_const_normalized (m : ℂ) :
    (∫ _y : UnitAddTorus (Fin r), m ∂D.normalizedMeasure) = m := by
  rw [D.integral_normalizedMeasure, integral_smul_const]
  change D.mass⁻¹ • D.mass • m = _
  rw [smul_smul, inv_mul_cancel₀ D.mass_pos.ne', one_smul]

theorem packetRep_mean_subConst (g : PacketRep r) (m : ℂ) :
    (g.subConst m).mean D = g.mean D - m := by
  unfold PacketRep.mean
  rw [show (g.subConst m : UnitAddTorus (Fin r) → ℂ) = fun y ↦ g y - m from rfl]
  rw [integral_sub (Integrable.of_bound g.measurable_toFun.aestronglyMeasurable g.bound
    (Eventually.of_forall g.norm_le)) (integrable_const _), D.integral_const_normalized]


end Scalar.Data

end SchauderBasisOrbits

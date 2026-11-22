module

public import LeanCode.Scalar.Initial
public import LeanCode.Scalar.Inverse
public import LeanCode.Scalar.ActivationExhaustion
public import LeanCode.Scalar.Joining

@[expose] public section

open Filter Matrix
open scoped Topology MatrixOrder ComplexOrder

namespace SchauderBasisOrbits.Scalar

/-- The bounds carried by one stage. Instead of keeping the block partition after an
update, we retain its resulting augmented prefix certificate. -/
structure Stage (δ : ℝ) (n : ℕ) where
  dim : ℕ
  length : ℕ
  data : Data dim length
  eta : ℝ
  U : ℝ
  V : ℝ
  eta_nonneg : 0 ≤ eta
  eta_le : eta ≤ etaBound (gainCap δ) n
  U_nonneg : 0 ≤ U
  V_nonneg : 0 ≤ V
  U_le : U ≤ ∑ j ∈ Finset.range n, etaBound (gainCap δ) j
  V_le : V ≤ 4 * (initialLoss δ - data.loss) / 3
  loss_pos : 0 < data.loss
  loss_le : data.loss ≤ initialLoss δ
  gain_le : data.gain ≤ gainCap δ
  gain_error : gainCap δ - data.gain ≤ gainCap δ * (1 - (1 / 2) ^ n) / 4
  gram_floor : data.loss ^ 2 • 1 ≤ data.gram
  inverse_diagonal : ∀ i : Fin length, data.gram⁻¹ i.succ i.succ ≤ 1 + 2 * data.loss
  centered_pb : PB data.centerGram (Real.sqrt (budgetQ δ U V))
  augmented_pb : PB data.gram (Real.sqrt (budgetQ δ U V + 20 * eta / δ))

namespace Stage

variable {δ : ℝ} {n : ℕ} (S : Stage δ n)

lemma gain_lower (hδ : 0 < δ) (hδ₁ : δ ≤ 1) : 3 * gainCap δ / 4 ≤ S.data.gain := by
  have hpos : 0 ≤ gainCap δ := (by positivity : 0 ≤ initialLoss δ ^ 2 / 4).trans
    (gainCap_bounds hδ hδ₁).1
  have hge := S.gain_error
  nlinarith only [hge, show 0 ≤ gainCap δ * (1 / 2 : ℝ) ^ n by positivity]

lemma gain_pos (hδ : 0 < δ) (hδ₁ : δ ≤ 1) : 0 < S.data.gain := by
  have hcap : 0 < gainCap δ := by
    apply lt_of_lt_of_le _ (gainCap_bounds hδ hδ₁).1
    unfold initialLoss
    positivity
  linarith [S.gain_lower hδ hδ₁]

lemma budget_bounds (hδ : 0 < δ) (hδ₁ : δ ≤ 1) :
    let Q := budgetQ δ S.U S.V
    1 + δ / 4 ≤ Q ∧ Q ≤ 1 + δ / 4 + 30 * gainCap δ / δ + 2 * initialLoss δ / 3 ∧
      Q < 1 + δ / 2 ∧ δ / 8 < Q - 1 - S.data.gain ∧
      Q ^ 2 / (Q - 1 - S.data.gain) < 20 / δ := by
  have hcap := gainCap_bounds hδ hδ₁
  have hcap₀ : 0 ≤ gainCap δ := (by positivity : 0 ≤ initialLoss δ ^ 2 / 4).trans hcap.1
  have hV : S.V ≤ 4 * initialLoss δ / 3 := by linarith [S.V_le, S.loss_pos]
  exact induction_budget_bounds hδ hδ₁ hcap₀ hcap.2 S.gain_le S.U_nonneg
    (S.U_le.trans (sum_etaBound_le hcap₀ n)) S.V_nonneg hV

private lemma amplifying_square_le (D : Data S.dim S.length) {K K' : ℝ}
    (h : PB D.gram K) (hKK' : K ≤ K') : PB D.gram K' := by
  refine ⟨h.1.trans hKK', fun j hj c => (h.2 j hj c).trans ?_⟩
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ h.1 hKK' 2)
    (qform_nonneg D.gram_posDef.posSemidef _)

lemma common_augmented_pb (hδ : 0 < δ) (hδ₁ : δ ≤ 1) :
    PB S.data.gram (commonBound δ) := by
  have hcap := gainCap_bounds hδ hδ₁
  have hcap₀ : 0 ≤ gainCap δ := (by positivity : 0 ≤ initialLoss δ ^ 2 / 4).trans hcap.1
  have he := S.eta_le.trans (etaBound_le hcap₀ n)
  have hη : 20 * S.eta / δ ≤ δ / 24000 := by
    rw [div_le_iff₀ hδ]
    unfold initialLoss at hcap
    nlinarith only [he, hcap.2]
  apply S.amplifying_square_le S.data S.augmented_pb
  unfold commonBound
  exact Real.sqrt_le_sqrt (by linarith [S.budget_bounds hδ hδ₁ |>.2.2.1, hη])

end Stage

/-- Stage zero with the explicit initial weight and one nonconstant mode. -/
noncomputable def initialStage (δ : ℝ) (hδ : 0 < δ) (hδ₁ : δ ≤ 1) : Stage δ 0 := by
  let a := initialLoss δ
  have ha : 0 < a := by dsimp [a, initialLoss]; positivity
  have ha₁ : a ≤ 1 / 400 := by dsimp [a, initialLoss]; linarith
  let D := initialData a ha ha₁
  have hDloss : D.loss = a := initialData_loss a ha ha₁
  have hDgain : D.gain = gainCap δ := initialData_gain a ha ha₁
  have hg := D.gain_nonneg
  rw [hDgain] at hg
  refine {
    dim := 1, length := 1, data := D, eta := gainCap δ, U := 0, V := 0
    eta_nonneg := hg, eta_le := le_rfl, U_nonneg := le_rfl, V_nonneg := le_rfl
    U_le := by simp
    V_le := by simp [hDloss, a]
    loss_pos := by simpa [hDloss] using ha
    loss_le := by simp [hDloss, a]
    gain_le := by rw [hDgain]
    gain_error := by rw [hDgain, sub_self, pow_zero, sub_self, mul_zero, zero_div]
    gram_floor := by rw [hDloss]; exact initialData_floor a ha ha₁
    inverse_diagonal := by simpa only [hDloss] using initialData_inverse_diagonal a ha ha₁
    centered_pb := ?_
    augmented_pb := ?_
  }
  · let Q := budgetQ δ 0 0
    have hQ : 1 ≤ Q := by dsimp [Q, budgetQ]; simp; positivity
    refine ⟨Real.sqrt_nonneg _, fun k hk c => ?_⟩
    rw [Real.sq_sqrt (by linarith : 0 ≤ Q)]
    have hk' : k = 0 ∨ k = 1 := by omega
    rcases hk' with rfl | rfl
    · rw [truncCoeff_zero, show qform D.centerGram 0 = 0 by simp [qform]]
      exact mul_nonneg (by linarith) (qform_nonneg D.centerGram_posDef.posSemidef _)
    · rw [truncCoeff_full]
      exact le_mul_of_one_le_left (qform_nonneg D.centerGram_posDef.posSemidef _) hQ
  · let J := budgetQ δ 0 0 + 20 * gainCap δ / δ
    have hJ : 1 + D.gain ≤ J := by
      rw [hDgain]
      dsimp [J, budgetQ]
      have h := (le_div_iff₀ hδ).mpr
        (show gainCap δ * δ ≤ 20 * gainCap δ by nlinarith [mul_nonneg hg (sub_nonneg.mpr hδ₁)])
      simp
      linarith
    have hJ₀ : 1 ≤ J := by linarith [D.gain_nonneg]
    refine ⟨Real.sqrt_nonneg _, fun k hk c => ?_⟩
    rw [Real.sq_sqrt (by linarith : 0 ≤ J)]
    have hk' : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hk' with rfl | rfl | rfl
    · rw [truncCoeff_zero, show qform D.gram 0 = 0 by simp [qform]]
      exact mul_nonneg (by linarith) (qform_nonneg D.gram_posDef.posSemidef _)
    · exact (D.firstCut_qform_le c).trans
        (mul_le_mul_of_nonneg_right hJ (qform_nonneg D.gram_posDef.posSemidef _))
    · rw [truncCoeff_full]
      exact le_mul_of_one_le_left (qform_nonneg D.gram_posDef.posSemidef _) hJ₀

/-- The output state of one step together with the verified quantitative loss improvement. -/
abbrev Successor {δ : ℝ} {n : ℕ} (s : Stage δ n) :=
  {t : Stage δ (n + 1) //
    t.data.loss ≤ s.data.loss - 3 * s.data.loss ^ 2 / 4}

/-- Iterating a closed step yields genuinely vanishing losses, with varying finite dimensions. -/
theorem stage_supply_of_step {δ : ℝ} (hδ : 0 < δ) (hδ₁ : δ ≤ 1)
    (step : ∀ n (s : Stage δ n), Nonempty (Successor s)) :
    ∃ S : ∀ n, Stage δ n, Tendsto (fun n => (S n).data.loss) atTop (𝓝 0) := by
  classical
  let S : ∀ n, Stage δ n := fun n =>
    Nat.rec (initialStage δ hδ hδ₁) (fun k s => (Classical.choice (step k s)).val) n
  refine ⟨S, tendsto_zero_of_loss_recurrence (fun n => (S n).loss_pos.le) ?_⟩
  intro n
  exact (Classical.choice (step n (S n))).property


/-- The precise activation-prefix interface used by the scalar induction. The row-zero
bound is kept separate from the common bound on old nonconstant rows. -/
def ActivationPrefixEstimate : Prop :=
  ∀ {r d : ℕ} (D : Data r d) {p : ℝ} (A : ActivationSet p) (N : ℕ)
    {Q : ℝ}, 1 ≤ Q → PB D.gram (Real.sqrt Q) →
    (∀ i : Fin d, D.gram⁻¹ i.succ i.succ ≤ 1 + 2 * D.loss) →
    1 + D.gain + D.loss / 4 * (D.gram⁻¹ 0 0 - 1) ≤ Q →
    PB (activateCutoff D A N).centerGram (Real.sqrt (Q + D.loss ^ 2 / 2))

private lemma normalizedGram_pb_of_center {r n : ℕ} (D : Data r n) {K : ℝ}
    (h : PB D.centerGram K) : PB D.normalizedGram K := by
  refine ⟨h.1, fun k hk c => ?_⟩
  simp only [Data.normalizedGram, qform_smul]
  rw [mul_left_comm (K ^ 2)]
  exact mul_le_mul_of_nonneg_left (h.2 k hk c) (inv_nonneg.mpr D.mass_pos.le)

private lemma raw_prefix_augment_bound {r d : ℕ} (D : Data r d) {s t : ℝ} (hst : s ≤ t)
    (h : PB D.gram (Real.sqrt s)) : PB D.gram (Real.sqrt t) := by
  refine ⟨Real.sqrt_nonneg _, fun j hj c => (h.2 j hj c).trans ?_⟩
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (Real.sqrt_nonneg _) (Real.sqrt_le_sqrt hst) 2)
    (qform_nonneg D.gram_posDef.posSemidef _)

private lemma zero_inv_sub_one_eq {r n : ℕ} (D : Data r n) :
    D.gram⁻¹ 0 0 - 1 = (D.gain + D.loss) / (1 - D.loss) := by
  have h : D.gram⁻¹ 0 0 = (1 + D.gain) / D.mass := by
    apply (eq_div_iff D.mass_pos.ne').2
    rw [mul_comm, D.mass_mul_gram_inv_zero_zero]
  rw [h, Data.loss, sub_sub_cancel]
  field_simp [D.mass_pos.ne']
  ring

private lemma exists_inverse_diagonal_excess {r d : ℕ} (D : Data r d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i : Fin (d + 1), D.gram⁻¹ i i - 1 ≤ C := by
  obtain ⟨j, hj⟩ := Finite.exists_max (fun i : Fin (d + 1) => D.gram⁻¹ i i - 1)
  exact ⟨max 0 (D.gram⁻¹ j j - 1), le_max_left _ _,
    fun i => (hj i).trans (le_max_right _ _)⟩

/-- The scalar successor with numerical, inverse, and copy budgets discharged. -/
theorem stage_step_of_activation_prefix (hAct : ActivationPrefixEstimate)
    {δ : ℝ} (hδ : 0 < δ) (hδ₁ : δ ≤ 1) {n : ℕ} (S : Stage δ n) :
    Nonempty (Successor S) := by
  let D := S.data
  let a := initialLoss δ
  let Z₀ := gainCap δ
  let e := D.loss
  let Z := D.gain
  let Q := budgetQ δ S.U S.V
  have ha : 0 < a := by dsimp [a, initialLoss]; positivity
  have ha₁ : a ≤ 1 / 400 := by dsimp [a, initialLoss]; linarith
  have he := S.loss_pos
  have hea := S.loss_le
  have hZcap := gainCap_bounds hδ hδ₁
  have hZ₁ := S.gain_lower hδ hδ₁
  have hZ₀ : 0 < Z₀ := (by positivity : 0 < a ^ 2 / 4).trans_le hZcap.1
  have hZ : 0 < Z := S.gain_pos hδ hδ₁
  have hZsmall : Z₀ ≤ (1 / 400 : ℝ) ^ 2 / 3 := hZcap.2.trans
    (div_le_div_of_nonneg_right (pow_le_pow_left₀ ha.le ha₁ 2) (by norm_num))
  have hZlow : 3 * a ^ 2 / 16 ≤ Z := by linarith only [show a ^ 2 / 4 ≤ Z₀ from hZcap.1,
    show 3 * Z₀ / 4 ≤ Z from hZ₁]
  let cap := etaBound Z₀ (n + 1)
  have hcap : 0 < cap := by simp only [cap, etaBound]; positivity
  obtain ⟨C, hC, hmax⟩ := exists_inverse_diagonal_excess D
  obtain ⟨p, hp, hp₁, hp₂, hpC, hzp, hzp'⟩ :=
    exists_activation_parameter he D.loss_lt_one hZ hC hcap
  let A := rareArc (show p ≤ 1 by linarith)
  obtain ⟨N, hz₁, hz₂⟩ := exists_activateCutoff_gain D A hp.le hzp
    (show 0 < D.loss / 4 by positivity)
  let E := activateCutoff D A N
  let z := E.gain
  have hz_le : z ≤ cap := hz₂.trans hzp'
  have hcap₁ : cap ≤ Z₀ / 8 := by
    simp only [cap, etaBound]
    exact div_le_div_of_nonneg_right
      (mul_le_of_le_one_right hZ₀.le (by apply pow_le_one₀ <;> norm_num)) (by norm_num)
  let L := ⌊Z / z⌋₊
  have hnumbers := activation_copy_bounds (a := a) (Z₀ := Z₀) he hea ha₁ hZlow hZ₁
    hp hp₁ hp₂ hz₁ hz₂ (hz_le.trans hcap₁)
  have hL : 0 < L := hnumbers.1
  let F := copies E L hL
  have hFgain : F.gain = (L : ℝ) * z := copies_gain E L hL
  have hFloss : F.loss = 1 - (1 - p * D.loss) ^ L := by
    rw [Data.loss, copies_mass, show E.mass = 1 - p * D.loss from
      activate_mass D A (fourierCutoffNumbering N) hp.le (fourierCutoffNumbering_zero N)
        (fourierCutoffNumbering_injective N)]
  have he₁ : D.loss / 12 ≤ F.loss := by rw [hFloss]; exact hnumbers.2.2.2.2.2.1
  have hdec : F.loss ≤ D.loss - 3 * D.loss ^ 2 / 4 := by
    rw [hFloss]
    exact hnumbers.2.2.2.2.2.2
  have hepos : 0 < F.loss := lt_of_lt_of_le (by positivity) he₁
  have heupper : F.loss ≤ D.loss := hdec.trans (by nlinarith [sq_nonneg D.loss])
  have hea' : F.loss ≤ a := heupper.trans hea
  have hgain : F.gain ≤ Z := by
    rw [hFgain]
    exact sub_nonneg.mp hnumbers.2.1
  have hgainloss : Z - F.gain ≤ cap := by
    rw [hFgain]
    exact hnumbers.2.2.1.le.trans hz_le
  let U' := S.U + S.eta
  let V' := S.V + D.loss ^ 2
  let Q' := budgetQ δ U' V'
  have hU' : U' ≤ ∑ j ∈ Finset.range (n + 1), etaBound Z₀ j := by
    rw [Finset.sum_range_succ]
    exact add_le_add S.U_le S.eta_le
  have hV' : V' ≤ 4 * (a - F.loss) / 3 := loss_budget_step S.V_le hdec
  have hU'₀ : 0 ≤ U' := add_nonneg S.U_nonneg S.eta_nonneg
  have hV'₀ : 0 ≤ V' := add_nonneg S.V_nonneg (sq_nonneg _)
  have hQ' : 1 + δ / 4 ≤ Q' ∧ Q' ≤ 1 + δ / 4 + 30 * Z₀ / δ + 2 * a / 3 ∧
      Q' < 1 + δ / 2 ∧ δ / 8 < Q' - 1 - F.gain ∧ Q' ^ 2 / (Q' - 1 - F.gain) < 20 / δ :=
    induction_budget_bounds hδ hδ₁ hZ₀.le hZcap.2 (hgain.trans S.gain_le)
      hU'₀ (hU'.trans (sum_etaBound_le hZ₀.le _)) hV'₀
      (hV'.trans (by change 4 * (a - F.loss) / 3 ≤ 4 * a / 3; linarith only [hepos]))
  have hQ₁ : 1 + δ / 4 ≤ Q := (S.budget_bounds hδ hδ₁).1
  have hrow0 : 1 + D.gain + D.loss / 4 * (D.gram⁻¹ 0 0 - 1) ≤ Q + 20 * S.eta / δ := by
    rw [zero_inv_sub_one_eq]
    have hf : D.loss / 4 * ((D.gain + D.loss) / (1 - D.loss)) =
        D.loss * (D.gain + D.loss) / (4 * (1 - D.loss)) := by rw [div_mul_eq_div_div]; ring
    rw [hf]
    have h := first_row_step_arithmetic he.le hea ha₁ D.gain_nonneg (S.gain_le.trans hZcap.2)
    have haδ : a ^ 2 ≤ δ / 4 := by
      dsimp [a, initialLoss]
      nlinarith [mul_nonneg hδ.le (sub_nonneg.mpr hδ₁)]
    have hη : 0 ≤ 20 * S.eta / δ := by positivity [S.eta_nonneg]
    linarith only [h, hQ₁, haδ, hη]
  have hQe : Q + 20 * S.eta / δ + D.loss ^ 2 / 2 = Q' := by
    dsimp [Q, Q', U', V', budgetQ]
    ring
  have hEPB : PB E.centerGram (Real.sqrt Q') := by
    rw [← hQe]
    have hQ₀ : 1 ≤ Q + 20 * S.eta / δ := by
      linarith only [hQ₁, hδ, show 0 ≤ 20 * S.eta / δ by positivity [S.eta_nonneg]]
    exact hAct D A N hQ₀ S.augmented_pb S.inverse_diagonal hrow0
  have hjoin := copies_augmented_pb E hL
    (show 1 + (L : ℝ) * E.gain < Q' by rw [← hFgain]; linarith only [hQ'.2.2.2.1, hδ])
    (normalizedGram_pb_of_center E hEPB)
  have hFaug : PB F.gram (Real.sqrt (Q' + 20 * z / δ)) := by
    apply raw_prefix_augment_bound F _ hjoin
    change Q' + Q' ^ 2 * z / (Q' - 1 - (L : ℝ) * z) ≤ Q' + 20 * z / δ
    rw [← hFgain]
    have h := mul_le_mul_of_nonneg_right hQ'.2.2.2.2.le E.gain_nonneg
    change (Q' ^ 2 / (Q' - 1 - F.gain)) * z ≤ 20 / δ * z at h
    linarith only [h, show Q' ^ 2 * z / (Q' - 1 - F.gain) =
      (Q' ^ 2 / (Q' - 1 - F.gain)) * z by ring,
      show 20 * z / δ = 20 / δ * z by ring]
  let next : Stage δ (n + 1) := {
    dim := L * (S.dim + 1)
    length := L * activatedCount S.length (2 * N)
    data := F
    eta := z
    U := U'
    V := V'
    eta_nonneg := E.gain_nonneg
    eta_le := hz_le
    U_nonneg := hU'₀
    V_nonneg := hV'₀
    U_le := hU'
    V_le := hV'
    loss_pos := hepos
    loss_le := hea'
    gain_le := hgain.trans S.gain_le
    gain_error := gain_budget_step S.gain_error hgainloss
    gram_floor := copied_activation_gram_floor D A he (hea.trans ha₁) S.gram_floor
      (fourierCutoffNumbering N) (fourierCutoffNumbering_zero N)
      (fourierCutoffNumbering_injective N) hL hepos hdec (hgain.trans S.gain_le) hZsmall
    inverse_diagonal := copied_activation_inverse_diagonal D A hp.le hC hmax hpC
      (fourierCutoffNumbering N) (fourierCutoffNumbering_zero N)
      (fourierCutoffNumbering_injective N) hL hepos (hea'.trans ha₁)
      (by change D.loss ≤ 12 * F.loss; linarith only [he₁])
    centered_pb := copies_centerGram_pb E L hL hEPB
    augmented_pb := hFaug
  }
  exact ⟨⟨next, hdec⟩⟩

end SchauderBasisOrbits.Scalar

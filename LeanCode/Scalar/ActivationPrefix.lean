module

public import LeanCode.Scalar.Induction
public import LeanCode.Finite.ActivatedRowCut

@[expose] public section

open Matrix MeasureTheory ContinuousLinearMap Submodule
open scoped ENNReal MatrixOrder ComplexOrder InnerProductSpace InnerProduct

namespace SchauderBasisOrbits.Scalar

local notation "μ𝕋" => (@AddCircle.haarAddCircle 1 _)

variable {r n m : ℕ} (D : Data r n) {p : ℝ} (A : ActivationSet p)
variable (Y : Fin (m + 1) → ℤ)

/-- Span of the first auxiliary modes used by a cut inside a row. -/
noncomputable def activationFiberSpan (l : ℕ) : Submodule ℂ (CircleL₂ 1) :=
  span ℂ (Set.range (fun i : {i : Fin (m + 1) // i.val < l} =>
    @fourierLp 1 _ 2 _ (Y i.val)))

noncomputable instance finiteDimensional_activationFiberSpan (l : ℕ) :
    FiniteDimensional ℂ (activationFiberSpan Y l) := by
  unfold activationFiberSpan
  exact FiniteDimensional.span_of_finite _ (Set.finite_range _)

lemma activationFiberSpan_projection (hY : Function.Injective Y)
    (l : ℕ) (i : Fin (m + 1)) :
    (activationFiberSpan Y l).starProjection (@fourierLp 1 _ 2 _ (Y i)) =
      if i.val < l then @fourierLp 1 _ 2 _ (Y i) else 0 := by
  by_cases hi : i.val < l
  · rw [if_pos hi]
    exact starProjection_eq_self_iff.mpr (subset_span ⟨⟨i, hi⟩, rfl⟩)
  · rw [if_neg hi, starProjection_apply]
    rw [orthogonalProjectionOnto_apply_of_mem_orthogonal, Submodule.coe_zero]
    apply (Submodule.mem_orthogonal _ _).2
    intro x hx
    have horth : ∀ j : {j : Fin (m + 1) // j.val < l},
        ⟪@fourierLp 1 _ 2 _ (Y j.val), @fourierLp 1 _ 2 _ (Y i)⟫_ℂ = 0 := by
      intro j
      have hne : Y j.val ≠ Y i := fun h => hi (hY h ▸ j.property)
      exact (orthonormal_iff_ite.mp (@orthonormal_fourier 1 _) _ _).trans (if_neg hne)
    change x ∈ span ℂ (Set.range _) at hx
    refine Submodule.span_induction (p := fun z _ => ⟪z, @fourierLp 1 _ 2 _ (Y i)⟫_ℂ = 0)
      ?_ ?_ ?_ ?_ hx
    · rintro _ ⟨j, rfl⟩
      exact horth j
    · simp
    · intro u v hu hv h₁ h₂
      rw [inner_add_left, h₁, h₂, add_zero]
    · intro c u hu h₁
      rw [inner_smul_left, h₁, mul_zero]

lemma activationIndex_val (i : Fin (activatedCount n m + 1)) :
    (activationIndex n m i).2.val + (m + 1) * (activationIndex n m i).1.val = i.val := by
  exact congrArg Fin.val (finProdFinEquiv.apply_symm_apply (finCongr (activatedCount_succ n m) i))

private lemma activationRefColumn_rowCut (hY : Function.Injective Y)
    (j : Fin (n + 1)) {l : ℕ} (hl : l < m + 1)
    (i : Fin (activatedCount n m + 1)) :
    HilbertTuple.rowCut j (activationFiberSpan Y l).starProjection (activationRefColumn Y i) =
      if i.val < (m + 1) * j.val + l then activationRefColumn Y i else 0 := by
  let s := (activationIndex n m i).1
  let t := (activationIndex n m i).2
  have hidx : t.val + (m + 1) * s.val = i.val := activationIndex_val i
  have hcol : activationRefColumn Y i =
      PiLp.single 2 s (@fourierLp 1 _ 2 _ (Y t)) := rfl
  rw [hcol]
  ext x
  by_cases hx : x = s
  · subst x
    simp only [HilbertTuple.rowCut_apply, PiLp.single_apply, ite_true, activationFiberSpan_projection Y hY]
    by_cases hs : s < j
    · have hmul : (m + 1) * (s.val + 1) ≤ (m + 1) * j.val :=
        Nat.mul_le_mul_left _ hs
      rw [Nat.mul_succ] at hmul
      have hc : i.val < (m + 1) * j.val + l := by omega
      rw [if_pos hs, if_pos hc]
      simp
    · by_cases he : s = j
      · have hc : i.val < (m + 1) * j.val + l ↔ t.val < l := by
          have hh := congrArg (fun a : Fin (n + 1) => (m + 1) * a.val) he
          omega
        rw [if_neg hs, if_pos he]
        by_cases ht : t.val < l <;> simp [hc, ht]
      · have hsj : j < s := lt_of_le_of_ne (le_of_not_gt hs) (Ne.symm he)
        have hmul : (m + 1) * (j.val + 1) ≤ (m + 1) * s.val :=
          Nat.mul_le_mul_left _ hsj
        rw [Nat.mul_succ] at hmul
        have hc : ¬ i.val < (m + 1) * j.val + l := by omega
        simp [hs, he, hc]
  · by_cases hcut : i.val < (m + 1) * j.val + l <;>
      simp [HilbertTuple.rowCut_apply, PiLp.single_apply, hx, hcut]

lemma activationRefIsometry_rowCut (hY : Function.Injective Y)
    (j : Fin (n + 1)) {l : ℕ} (hl : l < m + 1)
    (c : Fin (activatedCount n m + 1) → ℂ) :
    HilbertTuple.rowCut j (activationFiberSpan Y l).starProjection
      (activationRefIsometry Y hY (WithLp.toLp 2 c)) =
    activationRefIsometry Y hY (WithLp.toLp 2 (truncCoeff ((m + 1) * j.val + l) c)) := by
  change HilbertTuple.rowCut j (activationFiberSpan Y l).starProjection
    (synthCLM (activationRefColumn Y) (WithLp.toLp 2 c)) =
      synthCLM (activationRefColumn Y) (WithLp.toLp 2 (truncCoeff ((m + 1) * j.val + l) c))
  simp only [synthCLM_apply, WithLp.ofLp_toLp, synth, map_sum, map_smul,
    activationRefColumn_rowCut Y hY j hl]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases h : i.val < (m + 1) * j.val + l <;> simp [truncCoeff, h]

lemma Data.gramPrefixNormSq_first_le (D : Data r n) :
    gramPrefixNormSq D.gram 1 ≤ 1 + D.gain := by
  unfold gramPrefixNormSq
  apply max_le (by linarith [D.gain_nonneg])
  have hG : 0 ≤ 1 + D.gain := by linarith [D.gain_nonneg]
  have hnorm := (metric_opNorm_le_iff D.gram_posDef (prefixMask ℝ 1)
    (Real.sqrt_nonneg (1 + D.gain))).mpr (fun c => by
      rw [prefixMask_mulVec, Real.sq_sqrt hG]
      exact D.firstCut_qform_le c)
  exact (pow_le_pow_left₀ (norm_nonneg _) hnorm 2).trans_eq (Real.sq_sqrt hG)

lemma Data.gramPrefixNormSq_zero (D : Data r n) :
    gramPrefixNormSq D.gram 0 = 1 := by
  have h : prefixMask (n := n + 1) ℝ 0 = 0 := by
    ext i j
    simp [prefixMask]
  simp [gramPrefixNormSq, h, opNorm]


/-- The coordinate cut on the ambient tuple, conjugated into the standard Hilbert norm. -/
noncomputable def activationCutOperator (j : Fin (n + 1)) (l : ℕ) :
    HilbertTuple (Fin (n + 1)) (CircleL₂ 1) →L[ℂ]
      HilbertTuple (Fin (n + 1)) (CircleL₂ 1) :=
  (activationEquiv D A).toContinuousLinearMap ∘L
    (HilbertTuple.rowCut j (activationFiberSpan Y l).starProjection ∘L
      (activationEquiv D A).symm.toContinuousLinearMap)

lemma activate_qform_cut_le (hY₀ : Y 0 = 0) (hY : Function.Injective Y)
    (j : Fin (n + 1)) {l : ℕ} (hl : l < m + 1) (c : Fin (activatedCount n m + 1) → ℂ) :
    qform (activate D A Y hY₀ hY).complexGram (truncCoeff ((m + 1) * j.val + l) c) ≤
      ‖activationCutOperator D A Y j l‖ ^ 2 *
        qform (activate D A Y hY₀ hY).complexGram c := by
  rw [activate_complexGram_eq_clmGram, qform_clmGram, qform_clmGram]
  let S := activationEquiv D A
  let U := activationRefIsometry (n := n) Y hY
  let x := S (U (WithLp.toLp 2 c))
  let Q := activationCutOperator D A Y j l
  change ‖S (U (WithLp.toLp 2 (truncCoeff ((m + 1) * j.val + l) c)))‖ ^ 2 ≤
    ‖Q‖ ^ 2 * ‖x‖ ^ 2
  have hcut : Q x = S (U (WithLp.toLp 2 (truncCoeff ((m + 1) * j.val + l) c))) := by
    change S (HilbertTuple.rowCut j (activationFiberSpan Y l).starProjection (S.symm (S (U (WithLp.toLp 2 c))))) = _
    rw [S.symm_apply_apply]
    exact congrArg S (activationRefIsometry_rowCut Y hY j hl c)
  rw [← hcut, ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (Q.le_opNorm _) 2

/-- The tuple norm estimates suffice for the finite scalar activation used in the induction. -/
theorem activate_prefix_of_row_bounds (hY₀ : Y 0 = 0) (hY : Function.Injective Y)
    {Q : ℝ} (hQ : 1 ≤ Q) (hPB : PB D.gram (Real.sqrt Q))
    (hinv : ∀ i : Fin n, D.gram⁻¹ i.succ i.succ ≤ 1 + 2 * D.loss)
    (hhead : 1 + D.gain + D.loss / 4 * (D.gram⁻¹ 0 0 - 1) ≤ Q)
    (hRow : ∀ (j : Fin (n + 1)) (l : ℕ), l < m + 1 →
      ‖activationCutOperator D A Y j l‖ ^ 2 ≤
        max (gramPrefixNormSq D.gram j.val) (gramPrefixNormSq D.gram (j.val + 1)) +
          (1 - D.gram j j) * (D.gram⁻¹ j j - 1) / 4) :
    PB (activate D A Y hY₀ hY).centerGram (Real.sqrt (Q + D.loss ^ 2 / 2)) := by
  let F := activate D A Y hY₀ hY
  apply F.centerGram_pb_of_gram_pb
  apply pb_of_complexify
  rw [F.complexify_gram]
  refine ⟨Real.sqrt_nonneg _, fun k hk c => ?_⟩
  have hQ₀ : 0 ≤ Q := zero_le_one.trans hQ
  have hQ' : 0 ≤ Q + D.loss ^ 2 / 2 := by positivity
  rw [Real.sq_sqrt hQ']
  by_cases hkfull : k = activatedCount n m + 1
  · rw [hkfull, truncCoeff_full]
    exact le_mul_of_one_le_left (qform_nonneg F.complexGram_posDef.posSemidef _)
      (by linarith [sq_nonneg D.loss])
  have hklt : k < (n + 1) * (m + 1) := by
    rw [← activatedCount_succ]
    exact lt_of_le_of_ne hk hkfull
  let j : Fin (n + 1) := ⟨k / (m + 1), by
    apply (Nat.div_lt_iff_lt_mul (by omega)).mpr
    simpa only [Nat.mul_comm] using hklt⟩
  let l := k % (m + 1)
  have hl : l < m + 1 := Nat.mod_lt _ (by omega)
  have hkm : (m + 1) * j.val + l = k := by
    simpa [j, l, add_comm] using Nat.mod_add_div k (m + 1)
  have hq := activate_qform_cut_le D A Y hY₀ hY j hl c
  rw [hkm] at hq
  refine hq.trans (mul_le_mul_of_nonneg_right ?_ (qform_nonneg F.complexGram_posDef.posSemidef _))
  have hRow' := hRow j l hl
  rw [D.gram_diag] at hRow'
  change ‖activationCutOperator D A Y j l‖ ^ 2 ≤ _ +
    D.loss * (D.gram⁻¹ j j - 1) / 4 at hRow'
  refine hRow'.trans ?_
  refine Fin.cases ?_ (fun i => ?_) j
  · simp only [Fin.val_zero, zero_add, D.gramPrefixNormSq_zero]
    have hmax : max 1 (gramPrefixNormSq D.gram 1) ≤ 1 + D.gain :=
      max_le (by linarith [D.gain_nonneg]) D.gramPrefixNormSq_first_le
    linarith only [hmax, hhead, sq_nonneg D.loss]
  · have hK : 1 ≤ Real.sqrt Q := by
      simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hQ
    have hmax : max (gramPrefixNormSq D.gram i.succ.val)
        (gramPrefixNormSq D.gram (i.succ.val + 1)) ≤ Q := by
      apply max_le <;> rw [← Real.sq_sqrt hQ₀]
      · exact gramPrefixNormSq_le_of_pb D.gram_posDef hK hPB (by omega)
      · exact gramPrefixNormSq_le_of_pb D.gram_posDef hK hPB (by omega)
    have hi := mul_le_mul_of_nonneg_left (sub_le_sub_right (hinv i) 1) D.loss_nonneg
    nlinarith only [hmax, hi]


private lemma activationEquiv_eq_complexified_gram :
    activationEquiv D A =
      HilbertTuple.activatedSqrtEquiv (complexify D.gram) (posDef_complexify D.gram_posDef)
        (lpIndicatorProjection μ𝕋 A.measurable_carrier)
        (lpIndicatorProjection_idempotent μ𝕋 A.measurable_carrier) := by
  let B := {M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ // M.PosDef}
  have h : (⟨complexify D.gram, posDef_complexify D.gram_posDef⟩ : B) =
      ⟨D.complexGram, D.complexGram_posDef⟩ := Subtype.ext D.complexify_gram
  exact (congrArg (fun M : B => HilbertTuple.activatedSqrtEquiv M.val M.property
    (lpIndicatorProjection μ𝕋 A.measurable_carrier)
    (lpIndicatorProjection_idempotent μ𝕋 A.measurable_carrier)) h).symm

/-- The activation-prefix lemma in the exact form consumed by the scalar induction. -/
theorem activationPrefixEstimate : ActivationPrefixEstimate := by
  intro r d D p A N Q hQ hPB hinv hhead
  unfold activateCutoff
  apply activate_prefix_of_row_bounds D A (fourierCutoffNumbering N)
    (fourierCutoffNumbering_zero N) (fourierCutoffNumbering_injective N) hQ hPB hinv hhead
  intro j l hl
  unfold activationCutOperator
  rw [activationEquiv_eq_complexified_gram]
  exact HilbertTuple.opNorm_activated_rowCut_sq_le D.gram D.gram_posDef D.gram_bounds.2
    (lpIndicatorProjection μ𝕋 A.measurable_carrier)
    (lpIndicatorProjection_idempotent μ𝕋 A.measurable_carrier)
    (lpIndicatorProjection_adjoint μ𝕋 A.measurable_carrier)
    (activationFiberSpan (fourierCutoffNumbering N) l) j

end SchauderBasisOrbits.Scalar

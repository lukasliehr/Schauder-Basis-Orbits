import LeanCode.Directional.SelectedMeans
import LeanCode.Directional.SelectedModes
import LeanCode.Measure.Information
import LeanCode.Finite.BlockPrefixes

open Filter Function MeasureTheory Matrix Submodule
open scoped ENNReal ComplexOrder InnerProductSpace InnerProduct

namespace SchauderBasisOrbits.DirectionalInput

noncomputable section

variable {ι : Type*} [Fintype ι]
variable {ρ : Measure (Base ι)} [IsFiniteMeasure ρ] (D : DirectionalInput ρ)
variable {L r n : ℕ} {m : ℝ} (hm : 0 < m) (hm' : m ≤ ((1 : ℝ) / 2) ^ L)
variable (S : Scalar.Data r n)

local notation "W" => (FiberWeight.selected (DirectionalInput.seedFiber D L hm hm') S)
local notation "q" => (D.d + L)

/-- The augmented selected family in column-first order. -/
def selectedAugmented :
    Fin ((n + 1) * q) → Lp ℂ 2 ((W).normalizedMeasure ρ) :=
  D.selectedLp hm hm' S ∘ (finProdFinEquiv : Fin (n + 1) × Fin q ≃ Fin ((n + 1) * q)).symm

/-- The helper part of the constant scalar column. -/
def selectedHead :
    Fin D.d → Lp ℂ 2 ((W).normalizedMeasure ρ) :=
  fun i => D.selectedLp hm hm' S (0, Fin.castAdd L i)

/-- The nonconstant columns; their order is kept exactly in the projection argument. -/
def selectedTail :
    Fin (n * q) → Lp ℂ 2 ((W).normalizedMeasure ρ) :=
  fun i =>
    let j := (finProdFinEquiv : Fin n × Fin q ≃ Fin (n * q)).symm i
    D.selectedLp hm hm' S (j.1.succ, j.2)

/-- Delete the phase part of the constant column, keeping the old row order. -/
def selectedReduction (L n : ℕ) :
    Fin (D.d + n * (D.d + L)) ↪ Fin ((n + 1) * (D.d + L)) where
  toFun i :=
    ⟨if i.val < D.d then i.val else i.val + L, by
      rw [Nat.succ_mul]
      split_ifs <;> omega⟩
  inj' := by
    intro i j h
    apply Fin.ext
    have hval := congrArg Fin.val h
    change (if i.val < D.d then i.val else i.val + L) =
      (if j.val < D.d then j.val else j.val + L) at hval
    split at hval <;> split at hval <;> omega

lemma selectedReduction_cut (k : ℕ)
    (i : Fin (D.d + n * (D.d + L))) :
    (D.selectedReduction L n i).val < D.d + L + k ↔ i.val < D.d + k := by
  change (if i.val < D.d then i.val else i.val + L) < D.d + L + k ↔ _
  split <;> omega

lemma selectedAugmented_reduced :
    D.selectedAugmented hm hm' S ∘ D.selectedReduction L n =
      Fin.append (D.selectedHead hm hm' S) (D.selectedTail hm hm' S) := by
  funext i
  refine Fin.addCases (fun a => ?_) (fun b => ?_) i
  · simp only [Function.comp_apply, selectedAugmented, selectedHead, Fin.append_left]
    have h : D.selectedReduction L n (Fin.castAdd (n * q) a) =
        finProdFinEquiv (0, Fin.castAdd L a) := by
      apply Fin.ext
      change (if a.val < D.d then a.val else a.val + L) = a.val + q * (0 : Fin (n + 1)).val
      simp [a.isLt]
    rw [h, Equiv.symm_apply_apply]
  · let p := (finProdFinEquiv : Fin n × Fin q ≃ Fin (n * q)).symm b
    simp only [Function.comp_apply, selectedAugmented, selectedTail, Fin.append_right]
    have hp := congrArg Fin.val
      ((finProdFinEquiv : Fin n × Fin q ≃ Fin (n * q)).apply_symm_apply b)
    change p.2.val + q * p.1.val = b.val at hp
    have h : D.selectedReduction L n (Fin.natAdd D.d b) =
        finProdFinEquiv (p.1.succ, p.2) := by
      apply Fin.ext
      change (if D.d + b.val < D.d then D.d + b.val else D.d + b.val + L) =
        p.2.val + q * (p.1.val + 1)
      rw [if_neg (by omega), Nat.mul_succ]
      omega
    rw [h, Equiv.symm_apply_apply]

lemma selectedReduced_independent
    (hIndep : LinearIndependent ℂ (D.selectedAugmented hm hm' S)) :
    LinearIndependent ℂ (Fin.append (D.selectedHead hm hm' S) (D.selectedTail hm hm' S)) := by
  rw [← D.selectedAugmented_reduced hm hm' S]
  exact hIndep.comp _ (D.selectedReduction L n).injective

lemma selectedReduced_postHead_bounds {K : ℝ}
    (hCut : ∀ k ≤ n * q, ∀ c : Fin ((n + 1) * q) → ℂ,
        ‖synth (D.selectedAugmented hm hm' S) (truncCoeff (q + k) c)‖ ≤
          K * ‖synth (D.selectedAugmented hm hm' S) c‖)
    (k : ℕ) (hk : k ≤ n * q) (c : Fin (D.d + n * q) → ℂ) :
    ‖synth (Fin.append (D.selectedHead hm hm' S) (D.selectedTail hm hm' S))
      (truncCoeff (D.d + k) c)‖ ≤
      K * ‖synth (Fin.append (D.selectedHead hm hm' S) (D.selectedTail hm hm' S)) c‖ := by
  rw [← D.selectedAugmented_reduced hm hm' S]
  exact prefix_cut_restrict _ (D.selectedReduction L n) (hCut k hk)
    (D.selectedReduction_cut k) c


def rawSelectedTail (i : Fin (n * q)) : SelectedPoint ι L r → ℂ :=
  let ji := (finProdFinEquiv : Fin n × Fin q ≃ Fin (n * q)).symm i
  D.rawSelected S (ji.1.succ, ji.2)

lemma measurable_rawSelectedTail (i : Fin (n * q)) : Measurable (D.rawSelectedTail S i) :=
  D.measurable_rawSelected S _

lemma norm_rawSelectedTail (i : Fin (n * q)) (p : SelectedPoint ι L r) :
    ‖D.rawSelectedTail S i p‖ = 1 := D.norm_rawSelected S _ _

def selectedTailSynthesis : CenteredSynthesis (Lp ℂ 2 ρ) (Lp ℂ 2 ((W).normalizedMeasure ρ)) (n * q) :=
  (W).synthesis ρ (D.rawSelectedTail S) (D.measurable_rawSelectedTail S) (fun _ => 1)
    (fun i p => (D.norm_rawSelectedTail S i p).le)

private def selectedTailMeanVector (i : Fin (n * q)) : Lp ℂ 2 ρ :=
  lift₂ ρ ((W).mean (D.rawSelectedTail S i)) ((W).measurable_mean (D.measurable_rawSelectedTail S i))
    1 ((W).norm_mean_le (D.measurable_rawSelectedTail S i) (fun p => (D.norm_rawSelectedTail S i p).le))

private def selectedTailCenterVector (i : Fin (n * q)) : Lp ℂ 2 ((W).normalizedMeasure ρ) :=
  lift₂ _ ((W).center (D.rawSelectedTail S i)) ((W).measurable_center (D.measurable_rawSelectedTail S i))
    (2 * 1) ((W).norm_center_le (D.measurable_rawSelectedTail S i) (fun p => (D.norm_rawSelectedTail S i p).le))

lemma selectedHead_eq_pullback (i : Fin D.d) :
    D.selectedHead hm hm' S i = (W).pullback ρ (productFamily ρ D.frequencies i) := by
  let u := productFamily ρ D.frequencies i
  have hu := ae_lift₂ ρ (mixedChar (D.frequencies i)) (continuous_mixedChar _).measurable 1
    (fun p => (norm_mixedChar _ p).le)
  have hcomp := ((W).measurePreserving_fst ρ).quasiMeasurePreserving.ae_eq_comp hu
  apply Lp.ext
  filter_upwards [ae_lift₂ ((W).normalizedMeasure ρ) (D.rawSelected S (0, Fin.castAdd L i))
      (D.measurable_rawSelected S _) 1 (fun p => (D.norm_rawSelected S _ p).le),
    (W).ae_pullback ρ u, hcomp] with p hp hpb hcomp'
  change D.selectedLp hm hm' S (0, Fin.castAdd L i) p = (W).pullback ρ u p
  change D.selectedLp hm hm' S (0, Fin.castAdd L i) p = _ at hp
  rw [hp, hpb]
  change D.rawSelected S (0, Fin.castAdd L i) p = u p.1
  rw [show u p.1 = mixedChar (D.frequencies i) p.1 from hcomp']
  simp [rawSelected, rawRow]

private lemma selectedTailMeanVector_mem (i : Fin (n * q)) :
    D.selectedTailMeanVector hm hm' S i ∈ span ℂ (Set.range (productFamily ρ D.frequencies)) := by
  let V := span ℂ (Set.range (productFamily ρ D.frequencies))
  let M : ℂ := ((W).mass : ℂ)
  have hM : M ≠ 0 := by
    dsimp [M]
    exact_mod_cast (W).mass_pos.ne'
  obtain ⟨⟨k, j⟩, rfl⟩ := (finProdFinEquiv : Fin n × Fin q ≃ Fin (n * q)).surjective i
  let U := D.selectedTailMeanVector hm hm' S (finProdFinEquiv (k, j))
  have hU : ⇑U =ᵐ[ρ] (W).mean (D.rawSelected S (k.succ, j)) := by
    change _ =ᵐ[ρ] _
    unfold U selectedTailMeanVector
    apply (ae_lift₂ ρ _ _ _ _).trans
    exact Eventually.of_forall (fun p => by simp [rawSelectedTail])
  let e := synth (productFamily ρ D.frequencies) D.coeff
  have he : e ∈ V := by
    unfold e synth
    exact Submodule.sum_mem _ (fun i _ => smul_mem V _ (subset_span (Set.mem_range_self i)))
  change U ∈ V
  revert U hU
  refine Fin.addCases (fun a => ?_) (fun b => ?_) j
  · intro U hU
    let t : ℂ := M⁻¹ * ((1 - (m : ℂ)) * (S.meanColumn k : ℂ))
    have hu := ae_lift₂ ρ (mixedChar (D.frequencies a)) (continuous_mixedChar _).measurable 1
      (fun p => (norm_mixedChar _ p).le)
    have hEq : U = t • productFamily ρ D.frequencies a := by
      apply Lp.ext
      filter_upwards [hU, hu, Lp.coeFn_smul t (productFamily ρ D.frequencies a)] with p h₁ h₂ h₃
      rw [h₁, h₃]
      change (W).mean (D.rawSelected S (k.succ, Fin.castAdd L a)) p =
        t * productFamily ρ D.frequencies a p
      rw [show productFamily ρ D.frequencies a p = mixedChar (D.frequencies a) p from h₂]
      have h := congrArg (fun z : ℂ => M⁻¹ * z) (D.selected_mean_base hm hm' S k a p)
      change M⁻¹ * (M * (W).mean (D.rawSelected S (k.succ, Fin.castAdd L a)) p) = _ at h
      simpa only [← mul_assoc, inv_mul_cancel₀ hM, one_mul, t] using h
    rw [hEq]
    exact smul_mem V _ (subset_span (Set.mem_range_self a))
  · intro U hU
    let t : ℂ := M⁻¹ * (-(m : ℂ) * (S.meanColumn k : ℂ)) * (D.seedScale : ℂ)
    have hEq : U = t • e := by
      apply Lp.ext
      filter_upwards [hU, D.ae_direction, Lp.coeFn_smul t e] with p h₁ h₂ h₃
      rw [h₁, h₃]
      change (W).mean (D.rawSelected S (k.succ, Fin.natAdd D.d b)) p =
        t * e p
      rw [show e p = D.direction p from h₂]
      have h := congrArg (fun z : ℂ => M⁻¹ * z) (D.selected_mean_phase hm hm' S k b p)
      change M⁻¹ * (M * (W).mean (D.rawSelected S (k.succ, Fin.natAdd D.d b)) p) = _ at h
      rw [← mul_assoc, inv_mul_cancel₀ hM, one_mul] at h
      rw [h]
      simp [amplitude, t, mul_assoc]
    rw [hEq]
    exact smul_mem V _ he

lemma selectedTail_means_range :
    (D.selectedTailSynthesis hm hm' S).means.toLinearMap.range ≤
      span ℂ (Set.range (productFamily ρ D.frequencies)) := by
  rintro _ ⟨c, rfl⟩
  change synthCLM (D.selectedTailMeanVector hm hm' S) c ∈ _
  rw [synthCLM_apply, synth]
  apply Submodule.sum_mem
  intro i hi
  exact smul_mem _ _ (D.selectedTailMeanVector_mem hm hm' S i)

private lemma pullback_mem_span_selectedHead {z : Lp ℂ 2 ρ}
    (hz : z ∈ span ℂ (Set.range (productFamily ρ D.frequencies))) :
    (W).pullback ρ z ∈ span ℂ (Set.range (D.selectedHead hm hm' S)) := by
  let V := span ℂ (Set.range (D.selectedHead hm hm' S))
  have h : span ℂ (Set.range (productFamily ρ D.frequencies)) ≤
      V.comap ((W).pullback ρ).toLinearMap := by
    apply span_le.mpr
    rintro _ ⟨i, rfl⟩
    change (W).pullback ρ (productFamily ρ D.frequencies i) ∈ V
    rw [← D.selectedHead_eq_pullback hm hm' S i]
    exact subset_span (Set.mem_range_self i)
  exact h hz

private lemma selectedTailCenterVector_orthogonal (i : Fin (n * q)) :
    D.selectedTailCenterVector hm hm' S i ∈ (span ℂ (Set.range (D.selectedHead hm hm' S)))ᗮ := by
  apply (Submodule.mem_orthogonal _ _).2
  intro y hy
  refine Submodule.span_induction (p := fun y _ =>
    ⟪y, D.selectedTailCenterVector hm hm' S i⟫_ℂ = 0) ?_ ?_ ?_ ?_ hy
  · rintro _ ⟨j, rfl⟩
    rw [D.selectedHead_eq_pullback hm hm' S j]
    exact (W).inner_pullback_center_eq_zero ρ (productFamily ρ D.frequencies j)
      (D.measurable_rawSelectedTail S i) (fun p => (D.norm_rawSelectedTail S i p).le)
  · simp
  · intro a b ha hb h₁ h₂
    rw [inner_add_left, h₁, h₂, add_zero]
  · intro c a ha h₁
    rw [inner_smul_left, h₁, mul_zero]

/-- For these columns, projection off the retained constant helper span is precisely centering. -/
lemma selectedTail_offHead_eq :
    (offHead (𝕜 := ℂ) (D.selectedHead hm hm' S)) ∘ D.selectedTail hm hm' S =
      D.selectedTailCenterVector hm hm' S := by
  funext i
  have ht := (W).lift₂_eq_center_add_pullback ρ (D.measurable_rawSelectedTail S i)
    (fun p => (D.norm_rawSelectedTail S i p).le)
  change D.selectedTail hm hm' S i = D.selectedTailCenterVector hm hm' S i +
    (W).pullback ρ (D.selectedTailMeanVector hm hm' S i) at ht
  change (offHead (𝕜 := ℂ) (D.selectedHead hm hm' S)) (D.selectedTail hm hm' S i) =
    D.selectedTailCenterVector hm hm' S i
  rw [ht, map_add, offHead_eq_zero_of_mem_span _ (D.pullback_mem_span_selectedHead hm hm' S
    (D.selectedTailMeanVector_mem hm hm' S i)), add_zero]
  apply starProjection_eq_self_iff.mpr
  exact D.selectedTailCenterVector_orthogonal hm hm' S i

lemma selectedTail_centered_injective
    (hIndep : LinearIndependent ℂ (D.selectedAugmented hm hm' S)) :
    Injective (D.selectedTailSynthesis hm hm' S).centered := by
  have h := append_independent_offHead (𝕜 := ℂ) (D.selectedHead hm hm' S) (D.selectedTail hm hm' S)
    (D.selectedReduced_independent hm hm' S hIndep)
  rw [D.selectedTail_offHead_eq hm hm' S] at h
  change Injective (synthCLM (D.selectedTailCenterVector hm hm' S))
  intro a b hab
  simp only [synthCLM_apply] at hab
  exact WithLp.ofLp_injective 2 (funext (h.eq_coords_of_eq hab))

/-- SC09: no estimate of a prefix inside the constant column is required. -/
lemma selectedTail_centered_pb {K : ℝ} (hK : 0 ≤ K)
    (hCut : ∀ k ≤ n * q, ∀ c : Fin ((n + 1) * q) → ℂ,
      ‖synth (D.selectedAugmented hm hm' S) (truncCoeff (q + k) c)‖ ≤
        K * ‖synth (D.selectedAugmented hm hm' S) c‖) :
    PB (D.selectedTailSynthesis hm hm' S).centeredGram K := by
  have h := hPrefix_offHead (𝕜 := ℂ) (D.selectedHead hm hm' S) (D.selectedTail hm hm' S) hK
    (D.selectedReduced_postHead_bounds hm hm' S hCut)
  rw [D.selectedTail_offHead_eq hm hm' S] at h
  change PB (clmGram (synthCLM (D.selectedTailCenterVector hm hm' S))) K
  rw [clmGram_synthCLM_eq_gram]
  exact (hPrefix_iff_pb _ _).mp h


lemma selectedAugmented_independent_of_posDef
    (h : (Matrix.gram ℂ (D.selectedLp hm hm' S)).PosDef) :
    LinearIndependent ℂ (D.selectedAugmented hm hm' S) :=
  (Matrix.posDef_gram_iff_linearIndependent.mp h).comp _
    (finProdFinEquiv : Fin (n + 1) × Fin q ≃ Fin ((n + 1) * q)).symm.injective

lemma selectedTail_centered_pb_of_gram {K : ℝ} (hK : 0 ≤ K)
    (hCut : ∀ k ≤ n * q, ∀ c : Fin ((n + 1) * q) → ℂ,
      qform (Matrix.gram ℂ (D.selectedAugmented hm hm' S)) (truncCoeff (q + k) c) ≤
        K ^ 2 * qform (Matrix.gram ℂ (D.selectedAugmented hm hm' S)) c) :
    PB (D.selectedTailSynthesis hm hm' S).centeredGram K := by
  apply D.selectedTail_centered_pb hm hm' S hK
  intro k hk c
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hK (norm_nonneg _))).1
  rw [mul_pow, ← qform_gram, ← qform_gram]
  exact hCut k hk c

end

end SchauderBasisOrbits.DirectionalInput

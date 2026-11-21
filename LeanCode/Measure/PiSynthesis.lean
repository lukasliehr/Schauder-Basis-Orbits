import LeanCode.Measure.PiProducts
import LeanCode.Measure.Information
import LeanCode.Finite.DependentBlocks

open MeasureTheory Filter Matrix ContinuousLinearMap
open scoped BigOperators InnerProductSpace ComplexConjugate

noncomputable section

namespace SchauderBasisOrbits

local postfix:1024 "†" => ContinuousLinearMap.adjoint

/-- Raw representatives for a finite family of functions of modulus at most one. -/
structure FiberFamily (α β : Type*) [MeasurableSpace α] [MeasurableSpace β] (n : ℕ) where
  value : Fin n → α × β → ℂ
  measurable (k : Fin n) : Measurable (value k)
  norm_le (k : Fin n) (p : α × β) : ‖value k p‖ ≤ 1

namespace FiberFamily

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {n : ℕ}
variable {κ : Measure β} [IsFiniteMeasure κ]
variable (U : FiberFamily α β n) (W : FiberWeight α κ) (ρ : Measure α) [IsFiniteMeasure ρ]

def centerVector (k : Fin n) : Lp ℂ 2 (W.normalizedMeasure ρ) :=
  lift₂ _ (W.center (U.value k)) (W.measurable_center (U.measurable k))
    (2 * 1) (W.norm_center_le (U.measurable k) (U.norm_le k))

def meanVector (k : Fin n) : Lp ℂ 2 ρ :=
  lift₂ ρ (W.mean (U.value k)) (W.measurable_mean (U.measurable k))
    1 (W.norm_mean_le (U.measurable k) (U.norm_le k))

def synthesis : CenteredSynthesis (Lp ℂ 2 ρ) (Lp ℂ 2 (W.normalizedMeasure ρ)) n :=
  W.synthesis ρ U.value U.measurable (fun _ ↦ 1) U.norm_le

theorem synthesis_centered :
    (U.synthesis W ρ).centered = synthCLM (U.centerVector W ρ) := rfl

theorem synthesis_means :
    (U.synthesis W ρ).means = synthCLM (U.meanVector W ρ) := rfl

end FiberFamily

namespace FiberFamily

variable {m : ℕ} {n : Fin m → ℕ} {α : Type*} [MeasurableSpace α]
variable {β : Fin m → Type*} [∀ i, MeasurableSpace (β i)]
variable (U : (i : Fin m) → FiberFamily α (β i) (n i))

/-- Concatenate the families, each evaluated on its own fiber coordinates. -/
def combine : FiberFamily α ((i : Fin m) → β i) (∑ i, n i) where
  value := orderedDependentBlocks (fun i k p ↦ (U i).value k (p.1, p.2 i))
  measurable l := by
    obtain ⟨⟨i, k⟩, rfl⟩ := finSigmaFinEquiv.surjective l
    rw [orderedDependentBlocks_apply]
    exact ((U i).measurable k).comp (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd))
  norm_le l p := by
    obtain ⟨⟨i, k⟩, rfl⟩ := finSigmaFinEquiv.surjective l
    rw [orderedDependentBlocks_apply]
    exact (U i).norm_le k (p.1, p.2 i)

variable {κ : (i : Fin m) → Measure (β i)} [∀ i, IsFiniteMeasure (κ i)]
variable (W : (i : Fin m) → FiberWeight α (κ i))
variable (ρ : Measure α) [IsFiniteMeasure ρ]

theorem combine_value (i : Fin m) (k : Fin (n i)) :
    (combine U).value (finSigmaFinEquiv ⟨i, k⟩) = fun p ↦ (U i).value k (p.1, p.2 i) :=
  orderedDependentBlocks_apply (fun i k (p : α × ((i : Fin m) → β i)) ↦
    (U i).value k (p.1, p.2 i)) i k

theorem mean_combine (i : Fin m) (k : Fin (n i)) (s : α) :
    (FiberWeight.pi W).mean ((combine U).value (finSigmaFinEquiv ⟨i, k⟩)) s =
      (W i).mean ((U i).value k) s := by
  rw [combine_value]
  exact FiberWeight.mean_pi_coordinate W i ((U i).measurable k) s

theorem center_combine (i : Fin m) (k : Fin (n i)) (p : α × ((i : Fin m) → β i)) :
    (FiberWeight.pi W).center ((combine U).value (finSigmaFinEquiv ⟨i, k⟩)) p =
      (W i).center ((U i).value k) (p.1, p.2 i) := by
  unfold FiberWeight.center
  rw [mean_combine, combine_value]

theorem meanVector_combine (i : Fin m) (k : Fin (n i)) :
    (combine U).meanVector (FiberWeight.pi W) ρ (finSigmaFinEquiv ⟨i, k⟩) =
      (U i).meanVector (W i) ρ k := by
  apply Lp.ext
  refine (ae_lift₂ _ _ _ _ _).trans ?_
  refine Filter.EventuallyEq.trans ?_ (ae_lift₂ ρ _ _ _ _).symm
  exact Eventually.of_forall (mean_combine U W i k)

private theorem norm_center_le_two (i : Fin m) (k : Fin (n i)) (p : α × β i) :
    ‖(W i).center ((U i).value k) p‖ ≤ 2 := by
  simpa only [mul_one] using (W i).norm_center_le ((U i).measurable k) ((U i).norm_le k) p

theorem inner_centerVector_combine_same (i : Fin m) (k l : Fin (n i)) :
    ⟪(combine U).centerVector (FiberWeight.pi W) ρ (finSigmaFinEquiv ⟨i, k⟩),
      (combine U).centerVector (FiberWeight.pi W) ρ (finSigmaFinEquiv ⟨i, l⟩)⟫_ℂ =
    ⟪(U i).centerVector (W i) ρ k, (U i).centerVector (W i) ρ l⟫_ℂ := by
  simp only [centerVector, inner_lift₂, center_combine]
  let f : α × β i → ℂ :=
    fun p ↦ conj ((W i).center ((U i).value k) p) * (W i).center ((U i).value l) p
  have hf : Measurable f :=
    (Complex.continuous_conj.measurable.comp ((W i).measurable_center ((U i).measurable k))).mul
      ((W i).measurable_center ((U i).measurable l))
  have hB : ∀ p, ‖f p‖ ≤ 2 * 2 := by
    intro p
    change ‖conj _ * _‖ ≤ _
    rw [norm_mul, Complex.norm_conj]
    exact mul_le_mul (norm_center_le_two U W i k p) (norm_center_le_two U W i l p)
      (norm_nonneg _) (by norm_num)
  have hg : Measurable (fun p : α × ((i : Fin m) → β i) ↦ f (p.1, p.2 i)) :=
    hf.comp (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd))
  change (∫ p : α × ((i : Fin m) → β i), f (p.1, p.2 i) ∂(FiberWeight.pi W).normalizedMeasure ρ) =
    ∫ p, f p ∂(W i).normalizedMeasure ρ
  rw [(FiberWeight.pi W).integral_normalizedMeasure_eq_mean ρ hg (fun p ↦ hB (p.1, p.2 i)),
    (W i).integral_normalizedMeasure_eq_mean ρ hf hB]
  apply integral_congr_ae
  exact Eventually.of_forall (FiberWeight.mean_pi_coordinate W i hf)

theorem inner_centerVector_combine_distinct {i j : Fin m} (hij : i ≠ j)
    (k : Fin (n i)) (l : Fin (n j)) :
    ⟪(combine U).centerVector (FiberWeight.pi W) ρ (finSigmaFinEquiv ⟨i, k⟩),
      (combine U).centerVector (FiberWeight.pi W) ρ (finSigmaFinEquiv ⟨j, l⟩)⟫_ℂ = 0 := by
  simp only [centerVector, inner_lift₂, center_combine]
  let f : α × β i → ℂ := fun p ↦ conj ((W i).center ((U i).value k) p)
  let g := (W j).center ((U j).value l)
  have hf : Measurable f :=
    Complex.continuous_conj.measurable.comp ((W i).measurable_center ((U i).measurable k))
  have hg : Measurable g := (W j).measurable_center ((U j).measurable l)
  have hfg : Measurable (fun p : α × ((i : Fin m) → β i) ↦ f (p.1, p.2 i) * g (p.1, p.2 j)) :=
    (hf.comp (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd))).mul
      (hg.comp (measurable_fst.prodMk ((measurable_pi_apply j).comp measurable_snd)))
  change (∫ p : α × ((i : Fin m) → β i), f (p.1, p.2 i) * g (p.1, p.2 j)
    ∂(FiberWeight.pi W).normalizedMeasure ρ) = 0
  rw [(FiberWeight.pi W).integral_normalizedMeasure_eq_mean ρ hfg (B := 2 * 2)]
  · calc
      _ = ∫ _ : α, (0 : ℂ) ∂ρ := by
        apply integral_congr_ae
        filter_upwards [] with x
        rw [FiberWeight.mean_pi_two_coordinates W hij hf hg, show g = _ from rfl,
          (W j).mean_center_eq_zero ((U j).measurable l) ((U j).norm_le l), mul_zero]
      _ = _ := integral_zero α ℂ
  · intro p
    change ‖conj _ * _‖ ≤ _
    rw [norm_mul, Complex.norm_conj]
    exact mul_le_mul (norm_center_le_two U W i k _) (norm_center_le_two U W j l _)
      (norm_nonneg _) (by norm_num)

/-- The centered copy of a given input family in the combined Hilbert space. -/
def copiedCenter (i : Fin m) (k : Fin (n i)) : Lp ℂ 2 ((FiberWeight.pi W).normalizedMeasure ρ) :=
  (combine U).centerVector (FiberWeight.pi W) ρ (finSigmaFinEquiv ⟨i, k⟩)

theorem combine_synthesis_centered :
    ((combine U).synthesis (FiberWeight.pi W) ρ).centered =
      synthCLM (orderedDependentBlocks (copiedCenter U W ρ)) := by
  rw [synthesis_centered]
  congr 1
  funext k
  obtain ⟨⟨i, l⟩, rfl⟩ := finSigmaFinEquiv.surjective k
  rw [orderedDependentBlocks_apply]
  rfl

theorem combine_synthesis_means :
    ((combine U).synthesis (FiberWeight.pi W) ρ).means =
      synthCLM (orderedDependentBlocks (fun i ↦ (U i).meanVector (W i) ρ)) := by
  rw [synthesis_means]
  congr 1
  funext k
  obtain ⟨⟨i, l⟩, rfl⟩ := finSigmaFinEquiv.surjective k
  rw [orderedDependentBlocks_apply]
  exact meanVector_combine U W ρ i l

theorem gram_copiedCenter (i : Fin m) :
    Matrix.gram ℂ (copiedCenter U W ρ i) = Matrix.gram ℂ ((U i).centerVector (W i) ρ) := by
  ext k l
  rw [Matrix.gram_apply, Matrix.gram_apply]
  exact inner_centerVector_combine_same U W ρ i k l

private theorem injective_synthCLM_iff_independent {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] {d : ℕ} (v : Fin d → E) :
    Function.Injective (synthCLM (𝕜 := ℂ) v) ↔ LinearIndependent ℂ v := by
  constructor
  · intro h
    rw [linearIndependent_iff_synth_eq_zero]
    intro c hc
    let C := WithLp.toLp 2 c
    have hc' : synthCLM v C = 0 := by rw [synthCLM_apply]; exact hc
    exact congrArg WithLp.ofLp (h (hc'.trans ((synthCLM v).map_zero).symm))
  · intro h c d he
    rw [synthCLM_apply, synthCLM_apply] at he
    exact WithLp.ofLp_injective 2 (funext (h.eq_coords_of_eq he))

theorem combine_centered_injective
    (h : ∀ i, Function.Injective ((U i).synthesis (W i) ρ).centered) :
    Function.Injective ((combine U).synthesis (FiberWeight.pi W) ρ).centered := by
  rw [combine_synthesis_centered, injective_synthCLM_iff_independent]
  apply linearIndependent_orderedDependentBlocks _
  · exact fun i j hij k l ↦ inner_centerVector_combine_distinct U W ρ hij k l
  · intro i
    rw [← Matrix.posDef_gram_iff_linearIndependent, gram_copiedCenter,
      Matrix.posDef_gram_iff_linearIndependent, ← injective_synthCLM_iff_independent]
    exact h i

theorem combine_centered_pb (K : ℝ) (hK : 0 ≤ K)
    (h : ∀ i, PB ((U i).synthesis (W i) ρ).centeredGram K) :
    PB ((combine U).synthesis (FiberWeight.pi W) ρ).centeredGram K := by
  unfold CenteredSynthesis.centeredGram
  rw [combine_synthesis_centered, clmGram_synthCLM_eq_gram, ← hPrefix_iff_pb]
  apply hPrefix_orderedDependentBlocks _ hK
  · exact fun i j hij k l ↦ inner_centerVector_combine_distinct U W ρ hij k l
  · intro i
    rw [hPrefix_iff_pb, gram_copiedCenter, ← clmGram_synthCLM_eq_gram]
    exact h i

theorem combine_information_eq_sum
    (h : ∀ i, Function.Injective ((U i).synthesis (W i) ρ).centered) :
    ((combine U).synthesis (FiberWeight.pi W) ρ).information =
      ∑ i, ((U i).synthesis (W i) ρ).information := by
  let S := (combine U).synthesis (FiberWeight.pi W) ρ
  let D := fun i ↦ (U i).synthesis (W i) ρ
  apply ContinuousLinearMap.ext
  intro x
  let c := fun i ↦ (D i).centeredInverse (((D i).means†) x)
  let C : EuclideanSpace ℂ (Fin (∑ i, n i)) :=
    WithLp.toLp 2 (orderedDependentBlocks (fun i j ↦ c i j))
  have hC (i : Fin m) :
      (fun j ↦ C (finSigmaFinEquiv ⟨i, j⟩)) = WithLp.ofLp (c i) :=
    funext fun j ↦ orderedDependentBlocks_apply (fun i j ↦ c i j) i j
  have hsys : (S.centered†) (S.centered C) = (S.means†) x := by
    apply WithLp.ofLp_injective
    funext k
    obtain ⟨⟨i, j⟩, rfl⟩ := finSigmaFinEquiv.surjective k
    change (((combine U).synthesis (FiberWeight.pi W) ρ).centered†
      (((combine U).synthesis (FiberWeight.pi W) ρ).centered C)) (finSigmaFinEquiv ⟨i, j⟩) =
      (((combine U).synthesis (FiberWeight.pi W) ρ).means† x) (finSigmaFinEquiv ⟨i, j⟩)
    rw [combine_synthesis_centered, combine_synthesis_means,
      synthCLM_adjoint_coordinate, synthCLM_adjoint_coordinate,
      orderedDependentBlocks_apply, orderedDependentBlocks_apply,
      synthCLM_apply, synth_orderedDependentBlocks, inner_sum]
    let f (k : Fin m) := ⟪copiedCenter U W ρ i j, synth (copiedCenter U W ρ k)
      (fun l ↦ C (finSigmaFinEquiv ⟨k, l⟩))⟫_ℂ
    change (∑ k, f k) = _
    have hf : (∑ k, f k) = f i := by
      apply Finset.sum_eq_single i
      · intro i' _ hne
        unfold f
        rw [synth, inner_sum]
        apply Finset.sum_eq_zero
        intro l _
        rw [inner_smul_right, show ⟪copiedCenter U W ρ i j, copiedCenter U W ρ i' l⟫_ℂ = 0 from
          inner_centerVector_combine_distinct U W ρ (Ne.symm hne) j l, mul_zero]
      · simp
    rw [hf]
    dsimp only [f]
    rw [hC i, synth, inner_sum]
    ·
      simp_rw [inner_smul_right]
      have hsame (k : Fin (n i)) :
          ⟪copiedCenter U W ρ i j, copiedCenter U W ρ i k⟫_ℂ =
            ⟪(U i).centerVector (W i) ρ j, (U i).centerVector (W i) ρ k⟫_ℂ :=
        inner_centerVector_combine_same U W ρ i j k
      simp_rw [hsame]
      have hcal := congrArg (fun v : EuclideanSpace ℂ (Fin (n i)) ↦ v j)
        ((D i).centeredInverse_right (h i) (((D i).means†) x))
      change ((D i).centered† ((D i).centered (c i))) j = ((D i).means† x) j at hcal
      dsimp only [D] at hcal
      rw [synthesis_centered, synthesis_means, synthCLM_adjoint_coordinate,
        synthCLM_adjoint_coordinate, synthCLM_apply, synth, inner_sum] at hcal
      simpa only [inner_smul_right] using hcal
  have hInv : S.centeredInverse ((S.means†) x) = C :=
    (congrArg S.centeredInverse hsys).symm.trans (S.centeredInverse_left (combine_centered_injective U W ρ h) C)
  change S.information x = (∑ i, (D i).information) x
  rw [CenteredSynthesis.information_apply, hInv, ContinuousLinearMap.sum_apply]
  change ((combine U).synthesis (FiberWeight.pi W) ρ).means C =
    ∑ i, (D i).information x
  rw [combine_synthesis_means, synthCLM_apply, synth_orderedDependentBlocks]
  apply Finset.sum_congr rfl
  intro i _
  rw [hC i, ← synthCLM_apply, show synthCLM ((U i).meanVector (W i) ρ) = (D i).means from rfl,
    CenteredSynthesis.information_apply]

theorem combine_means_range (V : Submodule ℂ (Lp ℂ 2 ρ))
    (h : ∀ i, LinearMap.range ((U i).synthesis (W i) ρ).means.toLinearMap ≤ V) :
    LinearMap.range ((combine U).synthesis (FiberWeight.pi W) ρ).means.toLinearMap ≤ V := by
  rintro _ ⟨c, rfl⟩
  change ((combine U).synthesis (FiberWeight.pi W) ρ).means c ∈ V
  rw [combine_synthesis_means, synthCLM_apply, synth_orderedDependentBlocks]
  apply Submodule.sum_mem
  intro i _
  apply h i
  refine ⟨WithLp.toLp 2 (fun j ↦ WithLp.ofLp c (finSigmaFinEquiv ⟨i, j⟩)), ?_⟩
  change ((U i).synthesis (W i) ρ).means _ = _
  rw [synthesis_means, synthCLM_apply, WithLp.ofLp_toLp]

end FiberFamily

end SchauderBasisOrbits

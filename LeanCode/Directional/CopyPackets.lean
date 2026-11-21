import LeanCode.Directional.SupplyContract
import LeanCode.Fourier.Coordinates
import LeanCode.Measure.PiProducts
import LeanCode.Scalar.Copies

open Filter Function MeasureTheory Submodule
open scoped ENNReal BigOperators Topology

namespace SchauderBasisOrbits

noncomputable section

variable {ι : Type*} [Fintype ι] {r : ℕ} (N : ℕ)

/-- Place one copy's new coordinate block in the flat copied torus. -/
def directionalCopyEmbedding (b : Fin N) : Fin r ↪ Fin (N * r) where
  toFun := fun j => finProdFinEquiv (b, j)
  inj' := fun i j h => congrArg Prod.snd (finProdFinEquiv.injective h)

lemma directionalCopyEmbedding_disjoint {b c : Fin N} (h : b ≠ c) (j : Fin r) :
    directionalCopyEmbedding N b j ∉ Set.range (directionalCopyEmbedding N c) := by
  rintro ⟨k, hk⟩
  apply h
  exact (congrArg Prod.fst (finProdFinEquiv.injective hk)).symm

/-- Base coordinates are shared, whereas fresh coordinates are specific to one copy. -/
def directionalCopyEmbeddingWithBase (b : Fin N) : (ι ⊕ Fin r) ↪ (ι ⊕ Fin (N * r)) :=
  (Function.Embedding.refl ι).sumMap (directionalCopyEmbedding N b)

@[simp] lemma directionalCopyEmbeddingWithBase_inl (b : Fin N) (i : ι) :
    directionalCopyEmbeddingWithBase N b (Sum.inl i : ι ⊕ Fin r) = Sum.inl i := rfl

@[simp] lemma directionalCopyEmbeddingWithBase_inr (b : Fin N) (j : Fin r) :
    (directionalCopyEmbeddingWithBase (ι := ι) N b) (Sum.inr j) =
      Sum.inr (directionalCopyEmbedding N b j) := rfl

lemma directionalRaw_copy (b : Fin N) (k : MixedFreq (ι ⊕ Fin r))
    (p : (ℝ × UnitAddTorus ι) × UnitAddTorus (Fin (N * r))) :
    directionalRaw (padMixedFreq (directionalCopyEmbeddingWithBase N b) k) p =
      directionalRaw k (p.1, Scalar.copyPoint N p.2 b) := by
  unfold directionalRaw
  rw [mixedChar_padMixedFreq]
  congr 2
  funext j
  cases j <;> rfl

variable {α : Type*} [MeasurableSpace α]

/-- The normalized product weight on a flat fresh torus. -/
def directionalCopyWeight (W : FiberWeight α (torusHaar (Fin r))) :
    FiberWeight α (torusHaar (Fin (N * r))) :=
  (FiberWeight.pi (fun _ : Fin N => W)).pullFiber
    (Scalar.copyPointEquiv (r := r) N) (Scalar.measurePreserving_copyPointEquiv (r := r) N)

theorem directionalCopyWeight_apply (W : FiberWeight α (torusHaar (Fin r)))
    (p : α × UnitAddTorus (Fin (N * r))) :
    (directionalCopyWeight N W).weight p = ∏ b : Fin N, W.weight (p.1, Scalar.copyPoint N p.2 b) := by
  simp only [directionalCopyWeight, FiberWeight.pullFiber, FiberWeight.pi,
    Scalar.copyPointEquiv_apply]

theorem directionalCopyWeight_mass (W : FiberWeight α (torusHaar (Fin r))) :
    (directionalCopyWeight N W).mass = W.mass ^ N := by
  change ∏ _ : Fin N, W.mass = _
  simp

theorem directionalCopyWeight_lower (W : FiberWeight α (torusHaar (Fin r))) {lower : ℝ}
    (hlower₀ : 0 ≤ lower) (hlower : ∀ s, lower ≤ W.weight s)
    (p : α × UnitAddTorus (Fin (N * r))) :
    lower ^ N ≤ (directionalCopyWeight N W).weight p := by
  rw [directionalCopyWeight_apply]
  calc
    lower ^ N = ∏ _ : Fin N, lower := by simp
    _ ≤ _ := Finset.prod_le_prod₀ (fun _ _ => hlower₀) (fun b _ => hlower _)

/-- Copy the polynomial into disjoint fresh blocks over the unchanged base. -/
def directionalCopyPoly (p : MixedPoly (ι ⊕ Fin r)) : MixedPoly (ι ⊕ Fin (N * r)) :=
  ∏ b : Fin N, padMixedPoly (directionalCopyEmbeddingWithBase N b) p

theorem eval_directionalCopyPoly (poly : MixedPoly (ι ⊕ Fin r))
    (W : FiberWeight (ℝ × UnitAddTorus ι) (torusHaar (Fin r)))
    (hpoly : ∀ p, evalMixedPoly poly (p.1.1, Sum.elim p.1.2 p.2) = (W.weight p : ℂ))
    (p : (ℝ × UnitAddTorus ι) × UnitAddTorus (Fin (N * r))) :
    evalMixedPoly (directionalCopyPoly N poly) (p.1.1, Sum.elim p.1.2 p.2) =
      ((directionalCopyWeight N W).weight p : ℂ) := by
  rw [directionalCopyWeight_apply, Complex.ofReal_prod]
  simp only [directionalCopyPoly, ← mixedEvalHom_apply, map_prod]
  apply Finset.prod_congr rfl
  intro b hb
  rw [mixedEvalHom_apply, eval_padMixedPoly]
  have hs : (Sum.elim p.1.2 p.2) ∘ directionalCopyEmbeddingWithBase N b =
      Sum.elim p.1.2 (Scalar.copyPoint N p.2 b) := by
    funext j
    cases j <;> rfl
  rw [hs]
  exact hpoly (p.1, Scalar.copyPoint N p.2 b)

variable {ρ : Measure (ℝ × UnitAddTorus ι)} [IsFiniteMeasure ρ]
variable {D : DirectionalInput ρ} (P : DirectionalFamily D)

/-- Concatenate the copied frequency families in copy-first order. -/
def directionalCopyFrequencies (i : Fin (N * P.n)) : MixedFreq (ι ⊕ Fin (N * P.r)) :=
  let x := (finProdFinEquiv : Fin N × Fin P.n ≃ Fin (N * P.n)).symm i
  padMixedFreq (directionalCopyEmbeddingWithBase N x.1) (P.freq x.2)

@[simp] lemma directionalCopyFrequencies_apply (b : Fin N) (i : Fin P.n) :
    directionalCopyFrequencies N P (finProdFinEquiv (b, i)) =
      padMixedFreq (directionalCopyEmbeddingWithBase N b) (P.freq i) := by
  rw [directionalCopyFrequencies, Equiv.symm_apply_apply]

lemma directionalCopyFrequencies_fresh (i : Fin (N * P.n)) :
    (fun j => (directionalCopyFrequencies N P i).2 (Sum.inr j)) ≠ 0 := by
  obtain ⟨⟨b, k⟩, rfl⟩ := (finProdFinEquiv : Fin N × Fin P.n ≃ Fin (N * P.n)).surjective i
  intro h
  apply P.fresh_ne_zero k
  funext j
  have hh := congrFun h (directionalCopyEmbedding N b j)
  simpa only [directionalCopyFrequencies_apply, padMixedFreq,
    ← directionalCopyEmbeddingWithBase_inr, padMode_at, Pi.zero_apply] using hh

lemma directionalCopyFrequencies_aux_injective (hD : Injective (fun j => (D.frequencies j).2)) :
    Injective (fun i => (directionalCopyFrequencies N P i).2) := by
  intro i j hij
  obtain ⟨⟨b, k⟩, rfl⟩ := (finProdFinEquiv : Fin N × Fin P.n ≃ Fin (N * P.n)).surjective i
  obtain ⟨⟨c, l⟩, rfl⟩ := (finProdFinEquiv : Fin N × Fin P.n ≃ Fin (N * P.n)).surjective j
  have h' : padMode (directionalCopyEmbeddingWithBase N b) (P.freq k).2 =
      padMode (directionalCopyEmbeddingWithBase N c) (P.freq l).2 := by
    simpa only [directionalCopyFrequencies_apply, padMixedFreq] using hij
  have hbc : b = c := by
    by_contra! hbc
    apply P.fresh_ne_zero k
    funext x
    have hnot : Sum.inr (directionalCopyEmbedding N b x) ∉
        Set.range (directionalCopyEmbeddingWithBase (ι := ι) N c) := by
      rintro ⟨sum, hs⟩
      cases sum with
      | inl z => simp at hs
      | inr z =>
        apply directionalCopyEmbedding_disjoint N hbc x
        exact ⟨z, Sum.inr.inj hs⟩
    have hu := congrFun h' (directionalCopyEmbeddingWithBase (ι := ι) N b (Sum.inr x))
    rw [padMode_at, directionalCopyEmbeddingWithBase_inr, padMode_off _ _ hnot] at hu
    exact hu
  subst c
  have hkl := P.aux_injective hD (padMode_injective _ h')
  rw [hkl]

lemma directionalCopyFrequencies_real (i : Fin (N * P.n)) :
    (directionalCopyFrequencies N P i).1 = 0 ∨
      ∃ j, (directionalCopyFrequencies N P i).1 = (D.frequencies j).1 := by
  obtain ⟨⟨b, k⟩, rfl⟩ := (finProdFinEquiv : Fin N × Fin P.n ≃ Fin (N * P.n)).surjective i
  simpa only [directionalCopyFrequencies_apply, padMixedFreq] using P.real_frequency k

end

end SchauderBasisOrbits

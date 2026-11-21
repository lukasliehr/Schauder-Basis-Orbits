import LeanCode.Fourier.Graph

open MeasureTheory Function
open scoped BigOperators

namespace SchauderBasisOrbits

noncomputable section

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- Coordinate change preserving product Haar probability. -/
def torusReindex (e : κ ≃ ι) : UnitAddTorus κ ≃ᵐ UnitAddTorus ι :=
  MeasurableEquiv.piCongrLeft (fun _ => UnitAddCircle) e

theorem measurePreserving_torusReindex (e : κ ≃ ι) :
    MeasurePreserving (torusReindex e) (torusHaar κ) (torusHaar ι) :=
  measurePreserving_piCongrLeft (fun _ : ι => AddCircle.haarAddCircle) e

/-- The measurable equivalence that splits two disjoint coordinate sets. -/
def torusSplit : UnitAddTorus (ι ⊕ κ) ≃ᵐ UnitAddTorus ι × UnitAddTorus κ :=
  MeasurableEquiv.sumPiEquivProdPi (fun _ => UnitAddCircle)

theorem measurePreserving_torusSplit :
    MeasurePreserving (torusSplit (ι := ι) (κ := κ)) (torusHaar (ι ⊕ κ))
      ((torusHaar ι).prod (torusHaar κ)) :=
  measurePreserving_sumPiEquivProdPi (fun _ : ι ⊕ κ => AddCircle.haarAddCircle)

/-- Extend a mode vector by zero on the omitted coordinates. -/
def padMode (e : ι ↪ κ) (k : ι → ℤ) : κ → ℤ :=
  Function.extend e k 0

omit [Fintype ι] [Fintype κ] in
@[simp] theorem padMode_at (e : ι ↪ κ) (k : ι → ℤ) (i : ι) :
    padMode e k (e i) = k i :=
  e.injective.extend_apply _ _ _

omit [Fintype ι] [Fintype κ] in
theorem padMode_off (e : ι ↪ κ) (k : ι → ℤ) {j : κ} (hj : j ∉ Set.range e) :
    padMode e k j = 0 :=
  Function.extend_apply' _ _ _ hj

omit [Fintype ι] [Fintype κ] in
theorem padMode_injective (e : ι ↪ κ) : Injective (padMode e) := by
  intro k l h
  funext i
  simpa only [padMode_at] using congrFun h (e i)

omit [Fintype ι] [Fintype κ] in
@[simp] theorem padMode_inl (k : ι → ℤ) (i : ι) :
    padMode (Function.Embedding.inl : ι ↪ ι ⊕ κ) k (Sum.inl i) = k i :=
  padMode_at _ k i

omit [Fintype ι] [Fintype κ] in
@[simp] theorem padMode_inr (k : κ → ℤ) (i : κ) :
    padMode (Function.Embedding.inr : κ ↪ ι ⊕ κ) k (Sum.inr i) = k i :=
  padMode_at _ k i

theorem torusChar_padMode (e : ι ↪ κ) (k : ι → ℤ) (y : UnitAddTorus κ) :
    torusChar (padMode e k) y = torusChar k (y ∘ e) := by
  classical
  simp only [torusChar, UnitAddTorus.mFourier, ContinuousMap.coe_mk]
  rw [← Finset.prod_subset (Finset.subset_univ ((Finset.univ : Finset ι).image e))]
  · rw [Finset.prod_image e.injective.injOn]
    exact Finset.prod_congr rfl (fun i _ => by rw [padMode_at]; rfl)
  · intro j _ hj
    rw [padMode_off e k (fun ⟨i, hi⟩ => hj (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hi⟩)),
      fourier_zero]

def padMixedFreq (e : ι ↪ κ) (k : MixedFreq ι) : MixedFreq κ :=
  (k.1, padMode e k.2)

theorem mixedChar_padMixedFreq (e : ι ↪ κ) (k : MixedFreq ι) (z : ℝ × UnitAddTorus κ) :
    mixedChar (padMixedFreq e k) z = mixedChar k (z.1, z.2 ∘ e) := by
  simp [padMixedFreq, mixedChar, torusChar_padMode]

def padMixedPoly (e : ι ↪ κ) (p : MixedPoly ι) : MixedPoly κ :=
  AddMonoidAlgebra.ofCoeff (p.coeff.mapDomain (padMixedFreq e))

theorem eval_padMixedPoly (e : ι ↪ κ) (p : MixedPoly ι) (z : ℝ × UnitAddTorus κ) :
    evalMixedPoly (padMixedPoly e p) z = evalMixedPoly p (z.1, z.2 ∘ e) := by
  rw [evalMixedPoly, padMixedPoly, AddMonoidAlgebra.coeff_ofCoeff,
    Finsupp.sum_mapDomain_index (h := fun (b : MixedFreq κ) (c : ℂ) => c * mixedChar b z)
      (fun _ => zero_mul _) (fun _ _ _ => add_mul ..)]
  simp only [evalMixedPoly, mixedChar_padMixedFreq]

/-- View an auxiliary Fourier polynomial as a mixed polynomial with zero real frequency. -/
def torusPolyAsMixed (p : TorusPoly ι) : MixedPoly ι :=
  AddMonoidAlgebra.ofCoeff (p.coeff.mapDomain fun k => (0, k))

theorem eval_torusPolyAsMixed (p : TorusPoly ι) (z : ℝ × UnitAddTorus ι) :
    evalMixedPoly (torusPolyAsMixed p) z = evalTorusPoly p z.2 := by
  rw [evalMixedPoly, torusPolyAsMixed, AddMonoidAlgebra.coeff_ofCoeff,
    Finsupp.sum_mapDomain_index (h := fun (b : MixedFreq ι) (c : ℂ) => c * mixedChar b z)
      (fun _ => zero_mul _) (fun _ _ _ => add_mul ..)]
  simp [evalTorusPoly, mixedChar]

theorem torusReindex_apply (e : κ ≃ ι) (y : UnitAddTorus κ) :
    torusReindex e y = y ∘ e.symm := by
  funext i
  obtain ⟨j, rfl⟩ := e.surjective i
  rw [torusReindex, MeasurableEquiv.piCongrLeft_apply_apply]
  simp

def reindexMixedPoly (e : κ ≃ ι) (p : MixedPoly ι) : MixedPoly κ :=
  padMixedPoly e.symm.toEmbedding p

theorem eval_reindexMixedPoly (e : κ ≃ ι) (p : MixedPoly ι) (z : ℝ × UnitAddTorus κ) :
    evalMixedPoly (reindexMixedPoly e p) z = evalMixedPoly p (z.1, torusReindex e z.2) :=
  by rw [torusReindex_apply]; exact eval_padMixedPoly e.symm.toEmbedding p z


end

end SchauderBasisOrbits

import LeanCode.Directional.RowCoordinates
import LeanCode.Finite.ColumnMatrix
import LeanCode.Directional.SelectedPairing
import LeanCode.Directional.BlockResponse

open Filter Function MeasureTheory Submodule Matrix ContinuousLinearMap
open scoped ENNReal BigOperators ComplexConjugate InnerProductSpace MatrixOrder ComplexOrder

namespace SchauderBasisOrbits

noncomputable section

section FiniteSynthesis

variable {I : Type*} [Fintype I] [DecidableEq I]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def finiteSynthesis (v : I → H) : EuclideanSpace ℂ I →L[ℂ] H :=
  LinearMap.toContinuousLinearMap
    ((Fintype.linearCombination ℂ v).comp (WithLp.linearEquiv 2 ℂ _).toLinearMap)

theorem finiteSynthesis_apply (v : I → H) (c : EuclideanSpace ℂ I) :
    finiteSynthesis v c = ∑ i, c i • v i := by
  simp [finiteSynthesis, Fintype.linearCombination_apply]

theorem range_finiteSynthesis (v : I → H) :
    (finiteSynthesis v).toLinearMap.range = span ℂ (Set.range v) := by
  ext x
  rw [mem_span_range_iff_exists_fun ℂ]
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨WithLp.ofLp c, (finiteSynthesis_apply v c).symm⟩
  · rintro ⟨c, rfl⟩
    exact ⟨WithLp.toLp 2 c, finiteSynthesis_apply v _⟩

theorem finiteSynthesis_adjoint_coordinate (v : I → H) (x : H) (i : I) :
    ((finiteSynthesis v).adjoint x) i = ⟪v i, x⟫_ℂ := by
  rw [← show ⟪EuclideanSpace.single i (1 : ℂ), (finiteSynthesis v).adjoint x⟫_ℂ =
        ((finiteSynthesis v).adjoint x) i by simp [EuclideanSpace.inner_single_left],
    adjoint_inner_right, finiteSynthesis_apply]
  simp

theorem clmGram_finiteSynthesis (v : I → H) : clmGram (finiteSynthesis v) = Matrix.gram ℂ v := by
  let e := Matrix.toEuclideanCLM (𝕜 := ℂ) (n := I)
  apply e.injective
  change e (clmGram (finiteSynthesis v)) = e (Matrix.gram ℂ v)
  rw [toEuclideanCLM_clmGram]
  apply ContinuousLinearMap.ext
  intro c
  apply WithLp.ofLp_injective
  funext i
  change ((finiteSynthesis v).adjoint (finiteSynthesis v c)) i =
    WithLp.ofLp (e (Matrix.gram ℂ v) c) i
  rw [finiteSynthesis_adjoint_coordinate, finiteSynthesis_apply, inner_sum, Matrix.ofLp_toEuclideanCLM]
  simp only [inner_smul_right, Matrix.mulVec, dotProduct, Matrix.gram_apply]
  exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)

def familyChange (v : I → H) (P : Matrix I I ℂ) (j : I) :=
  ∑ i, P i j • v i

theorem gram_familyChange (v : I → H) (P : Matrix I I ℂ) :
    Matrix.gram ℂ (familyChange v P) = Pᴴ * Matrix.gram ℂ v * P := by
  rw [Matrix.mul_assoc]
  ext i j
  simp only [Matrix.gram_apply, familyChange, sum_inner, inner_sum, inner_smul_left, inner_smul_right,
    Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.mul_sum, RCLike.star_def]
  conv_lhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem familyChange_mul (v : I → H) (P Q : Matrix I I ℂ) :
    familyChange (familyChange v P) Q = familyChange v (P * Q) := by
  funext j
  simp only [familyChange, Finset.smul_sum, Matrix.mul_apply, Finset.sum_smul, smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  rw [mul_comm]

theorem span_familyChange (v : I → H) (P : Matrix I I ℂ) (hP : IsUnit P) :
    span ℂ (Set.range (familyChange v P)) = span ℂ (Set.range v) := by
  have hle (Q : Matrix I I ℂ) (w : I → H) :
      span ℂ (Set.range (familyChange w Q)) ≤ span ℂ (Set.range w) := by
    apply span_le.mpr
    rintro _ ⟨j, rfl⟩
    exact Submodule.sum_mem _ (fun i _ => smul_mem _ _ (subset_span ⟨i, rfl⟩))
  apply le_antisymm (hle P v)
  have h := hle P⁻¹ (familyChange v P)
  rw [familyChange_mul, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hP)] at h
  have hOne : familyChange v 1 = v := by
    funext j
    simp [familyChange, Matrix.one_apply, ite_smul]
  rwa [hOne] at h

end FiniteSynthesis

section MatrixChange

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

theorem isUnit_columnTensorChange (E : Matrix I I ℂ) (hE : IsUnit E) :
    IsUnit (columnTensorChange E (σ := J)) := by
  refine ⟨⟨columnTensorChange E, columnTensorChange E⁻¹, ?_, ?_⟩, rfl⟩
  · simp only [columnTensorChange, ← Matrix.mul_kronecker_mul, Matrix.one_mul,
      Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hE), Matrix.one_kronecker_one]
  · simp only [columnTensorChange, ← Matrix.mul_kronecker_mul, Matrix.one_mul,
      Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 hE), Matrix.one_kronecker_one]

end MatrixChange

namespace DirectionalInput

variable {ι : Type*} [Fintype ι]
variable {ρ : Measure (Base ι)} [IsProbabilityMeasure ρ] (D : DirectionalInput ρ)
variable {L r n : ℕ} {m : ℝ} (hm : 0 < m) (hm' : m ≤ ((1 : ℝ) / 2) ^ L)
variable (S : Scalar.Data r n)

local notation "W" => FiberWeight.selected (D.seedFiber L hm hm') S
local notation "Ω" => D.rowReferenceGram L
local notation "A" => D.rowSeedGram L hm hm'
local notation "I" => Fin (D.d + L)

def tailColumns (ji : Fin n × I) := D.selectedColumnLp hm hm' S ji.1 ji.2

theorem tailColumns_gram :
    Matrix.gram ℂ (D.tailColumns hm hm' S) =
      (W).mass⁻¹ • columnTensorGram A Ω (complexify S.tailGram) := by
  ext ⟨k, i⟩ ⟨l, j⟩
  change Matrix.gram ℂ (D.selectedLp hm hm' S) (k.succ, i) (l.succ, j) = _
  rw [D.selectedGram_formula hm hm' S]
  have hB : S.complexGram k.succ l.succ = complexify S.tailGram k l := by
    rw [← S.complexify_gram]
    rfl
  simp only [hB, Fin.succ_inj, Matrix.smul_apply, columnTensorGram, Matrix.add_apply,
    Matrix.kronecker_apply, Matrix.one_apply, Complex.real_smul, Complex.ofReal_inv,
    Matrix.sub_apply]
  ring

def whitenedTailColumns (E : Matrix I I ℂ) (ki : Fin n × I) :=
  familyChange (D.tailColumns hm hm' S) (columnTensorChange E) ki

theorem whitenedTailColumns_gram (E : Matrix I I ℂ) (β : I → ℝ)
    (hΩ : Eᴴ * Ω * E = 1) (hA : Eᴴ * A * E = Matrix.diagonal (fun i => (β i : ℂ))) :
    Matrix.gram ℂ (D.whitenedTailColumns hm hm' S E) =
      (W).mass⁻¹ • Matrix.blockDiagonal (fun i => complexify (Scalar.gramMix S.tailGram (β i))) := by
  change Matrix.gram ℂ (familyChange (D.tailColumns hm hm' S) (columnTensorChange E)) = _
  rw [gram_familyChange, D.tailColumns_gram hm hm' S, Matrix.mul_smul, Matrix.smul_mul,
    columnTensorGram_congruence, hΩ, hA]
  have hDiag :
      columnTensorGram (Matrix.diagonal (fun i => (β i : ℂ))) (1 : Matrix I I ℂ) (complexify S.tailGram) =
        Matrix.blockDiagonal (fun i => β i • (1 : Matrix (Fin n) (Fin n) ℂ) +
          (1 - β i) • complexify S.tailGram) :=
    columnTensorGram_diagonal (complexify S.tailGram) β
  rw [hDiag]
  congr 2
  funext j
  ext k l
  simp only [Scalar.gramMix, complexify_apply, Matrix.add_apply, Matrix.smul_apply,
    RCLike.real_smul_eq_coe_mul, Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_sub,
    Complex.ofReal_one, Matrix.one_apply]
  split <;> simp

theorem whitened_pair_old_synth (E : Matrix I I ℂ) (β : I → ℝ) (hE : IsUnit E)
    (hΩ : Eᴴ * Ω * E = 1) (hA : Eᴴ * A * E = Matrix.diagonal (fun i => (β i : ℂ)))
    (ki : Fin n × I) (a : Fin D.d → ℂ) :
    ⟪D.whitenedTailColumns hm hm' S E ki,
      (W).pullback ρ (synth (productFamily ρ D.frequencies) a)⟫_ℂ =
      (((W).mass⁻¹ : ℝ) : ℂ) * (((1 - β ki.2 : ℝ) : ℂ) * rowCoords Ω E (D.oldRowCoeffs L a) ki.2 *
        (S.meanColumn ki.1 : ℂ)) := by
  rcases ki with ⟨k, i⟩
  apply mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr (W).mass_pos.ne')
  rw [Complex.ofReal_inv, ← mul_assoc, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr (W).mass_pos.ne'), one_mul]
  rw [← rowCoords_pairing hE hΩ β hA (D.oldRowCoeffs L a) i]
  have hWhite : D.whitenedTailColumns hm hm' S E (k, i) =
      ∑ j, E j i • D.selectedColumnLp hm hm' S k j := by
    unfold whitenedTailColumns familyChange
    rw [Fintype.sum_prod_type, Finset.sum_eq_single_of_mem k (Finset.mem_univ _)]
    · simp [columnTensorChange, Matrix.kronecker_apply, Matrix.one_apply, tailColumns]
    · intro a ha hne
      simp [columnTensorChange, Matrix.kronecker_apply, Matrix.one_apply, hne]
  rw [hWhite, sum_inner, Finset.mul_sum]
  conv_rhs => rw [Matrix.mulVec, dotProduct, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  have h := D.selected_pair_old_synth hm hm' S k j a
  change ((W).mass : ℂ) * ⟪D.selectedColumnLp hm hm' S k j,
    (W).pullback ρ (synth (productFamily ρ D.frequencies) a)⟫_ℂ = _ at h
  rw [inner_smul_left, mul_left_comm, h, Matrix.conjTranspose_apply]
  simp only [RCLike.star_def, oldRowCoeffs]
  ring

theorem whitenedTailColumns_independent (E : Matrix I I ℂ) (β : I → ℝ)
    (hβ : ∀ j, 0 ≤ β j ∧ β j ≤ 1)
    (hΩ : Eᴴ * Ω * E = 1) (hA : Eᴴ * A * E = Matrix.diagonal (fun i => (β i : ℂ))) :
    LinearIndependent ℂ (D.whitenedTailColumns hm hm' S E) := by
  rw [← Matrix.det_gram_ne_zero_iff_linearIndependent,
    ← isUnit_iff_ne_zero, ← Matrix.isUnit_iff_isUnit_det, D.whitenedTailColumns_gram hm hm' S E β hΩ hA]
  apply isUnit_real_smul_matrix _ (inv_ne_zero (W).mass_pos.ne')
  exact blockDiagonal_isUnit_of_posDef _ (fun i =>
    posDef_complexify (Scalar.gramMix_posDef S.tailGram_posDef (hβ i).1 (hβ i).2))

/-- The capture of an old combination by all nonconstant columns is the
sum of the scalar responses, divided by the selected mass. -/
theorem selected_projection_response (E : Matrix I I ℂ) (β : I → ℝ) (hE : IsUnit E)
    (hβ : ∀ j, 0 ≤ β j ∧ β j ≤ 1)
    (hΩ : Eᴴ * Ω * E = 1) (hA : Eᴴ * A * E = Matrix.diagonal (fun i => (β i : ℂ)))
    (a : Fin D.d → ℂ) :
    haveI : FiniteDimensional ℂ (span ℂ (Set.range (D.tailColumns hm hm' S))) :=
      Module.Finite.span_of_finite ℂ (Set.finite_range _)
    ‖(span ℂ (Set.range (D.tailColumns hm hm' S))).starProjection
      ((W).pullback ρ (synth (productFamily ρ D.frequencies) a))‖ ^ 2 =
      (W).mass⁻¹ * ∑ i, ‖rowCoords Ω E (D.oldRowCoeffs L a) i‖ ^ 2 * S.response (β i) := by
  let V := D.whitenedTailColumns hm hm' S E
  let X := finiteSynthesis V
  have hLin : LinearIndependent ℂ V := D.whitenedTailColumns_independent hm hm' S E β hβ hΩ hA
  have hX : Injective X := by
    change Injective ((Fintype.linearCombination ℂ V) ∘ (WithLp.linearEquiv 2 ℂ _))
    exact (linearIndependent_iff_injective_fintypeLinearCombination.mp hLin).comp (WithLp.linearEquiv 2 ℂ _).injective
  have hRange : X.toLinearMap.range = span ℂ (Set.range (D.tailColumns hm hm' S)) :=
    (range_finiteSynthesis V).trans
      (span_familyChange (D.tailColumns hm hm' S) (columnTensorChange E)
        (isUnit_columnTensorChange E hE))
  let y := (W).pullback ρ (synth (productFamily ρ D.frequencies) a)
  have hp := norm_starProjection_range_sq X hX y
  rw [clmGram_finiteSynthesis, D.whitenedTailColumns_gram hm hm' S E β hΩ hA] at hp
  have hg :
      WithLp.ofLp (X.adjoint y) = fun ji =>
        (((W).mass⁻¹ : ℝ) : ℂ) * (((1 - β ji.2 : ℝ) : ℂ) *
          rowCoords Ω E (D.oldRowCoeffs L a) ji.2 * (S.meanColumn ji.1 : ℂ)) := by
    funext ji
    rw [finiteSynthesis_adjoint_coordinate, D.whitened_pair_old_synth hm hm' S E β hE hΩ hA]
  rw [hg, normalized_selected_block_response S (W).mass_pos β hβ] at hp
  simpa only [hRange] using hp

end DirectionalInput

end

end SchauderBasisOrbits

import LeanCode.Directional.RowCoordinates

open Filter Function MeasureTheory Submodule Matrix
open scoped ENNReal BigOperators ComplexConjugate InnerProductSpace MatrixOrder ComplexOrder

namespace SchauderBasisOrbits.DirectionalInput

noncomputable section

variable {ι : Type*} [Fintype ι]
variable {ρ : Measure (Base ι)} [IsProbabilityMeasure ρ] (D : DirectionalInput ρ)

def baseSynthesis (a : Fin D.d → ℂ) : Lp ℂ 2 ρ :=
  synth (productFamily ρ D.frequencies) a

theorem refGram_qform_oldRowCoeffs {L : ℕ} (a : Fin D.d → ℂ) :
    qform (D.rowReferenceGram L) (D.oldRowCoeffs L a) = ‖D.baseSynthesis a‖ ^ 2 := by
  rw [qform, D.refGram_oldRowCoeffs, dotProduct, Fin.sum_univ_add]
  simp only [Pi.star_apply, oldRowCoeffs, Fin.append_left, Fin.append_right, Pi.zero_apply,
    mul_zero, Finset.sum_const_zero, add_zero]
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ), baseSynthesis]
  congr 1
  rw [synth, sum_inner]
  simp only [inner_smul_left, RCLike.star_def]

theorem seedGram_qform_oldRowCoeffs {L : ℕ} {m : ℝ} (hm : 0 < m)
    (hm' : m ≤ ((1 : ℝ) / 2) ^ L) (a : Fin D.d → ℂ) :
    qform (D.rowSeedGram L hm hm') (D.oldRowCoeffs L a) = m * ‖D.baseSynthesis a‖ ^ 2 := by
  rw [← D.refGram_qform_oldRowCoeffs (L := L), qform, qform, D.seedGram_oldRowCoeffs hm hm',
    dotProduct_smul, dotProduct_add, dotProduct_smul]
  have hz : star (D.oldRowCoeffs L a) ⬝ᵥ D.phaseOnes L = 0 := by
    rw [dotProduct, Fin.sum_univ_add]
    simp [oldRowCoeffs, phaseOnes]
  simp only [hz, smul_eq_mul, mul_zero, add_zero]
  change Complex.re ((m : ℂ) * (star (D.oldRowCoeffs L a) ⬝ᵥ
    D.rowReferenceGram L *ᵥ D.oldRowCoeffs L a)) = _
  simp [Complex.mul_re]

theorem oldRowCoeffs_add (L : ℕ) (a b : Fin D.d → ℂ) :
    D.oldRowCoeffs L (a + b) = D.oldRowCoeffs L a + D.oldRowCoeffs L b := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp [oldRowCoeffs]

theorem oldRowCoeffs_smul (L : ℕ) (c : ℂ) (a : Fin D.d → ℂ) :
    D.oldRowCoeffs L (c • a) = c • D.oldRowCoeffs L a := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp [oldRowCoeffs]

theorem baseSynthesis_sub (a b : Fin D.d → ℂ) :
    D.baseSynthesis (a - b) = D.baseSynthesis a - D.baseSynthesis b := by
  change synth _ (a - b) = synth _ a - synth _ b
  simp [synth, sub_smul, Finset.sum_sub_distrib]

theorem baseSynthesis_smul (c : ℂ) (a : Fin D.d → ℂ) :
    D.baseSynthesis (c • a) = c • D.baseSynthesis a := by
  change synth _ (c • a) = c • synth _ a
  simp [synth, Finset.smul_sum, smul_smul]

section Eigenspace

variable {L : ℕ} {m : ℝ} (hm : 0 < m) (hm' : m ≤ ((1 : ℝ) / 2) ^ L)
variable (E : Matrix (Fin (D.d + L)) (Fin (D.d + L)) ℂ) (β : Fin (D.d + L) → ℝ)
variable (hE : IsUnit E) (hΩ : Eᴴ * D.rowReferenceGram L * E = 1)
variable (hA : Eᴴ * D.rowSeedGram L hm hm' * E = Matrix.diagonal (fun i => (β i : ℂ)))

local notation "Ω" => D.rowReferenceGram L
local notation "A" => D.rowSeedGram L hm hm'
local notation "e₀" => D.oldRowCoeffs L D.coeff
local notation "z₀" => D.phaseOnes L
local notation "coord" => rowCoords Ω E

include hm hm' hE hΩ hA

theorem seed_eigenspace_base_action (a : Fin D.d → ℂ) (i : Fin (D.d + L)) :
    (β i : ℂ) * coord (D.oldRowCoeffs L a) i =
      (m : ℂ) * (coord (D.oldRowCoeffs L a) i +
        ((D.seedScale : ℂ) * ⟪D.baseSynthesis D.coeff, D.baseSynthesis a⟫_ℂ) * coord z₀ i) := by
  have h := congrFun (rowCoords_action hE hΩ β hA (D.oldRowCoeffs L a)) i
  rw [Matrix.mulVec_diagonal, D.seedGram_oldRowCoeffs hm hm' a, Matrix.mulVec_smul,
    Matrix.mulVec_add, Matrix.mulVec_smul, ← D.refGram_phaseOnes L] at h
  exact h.symm

theorem seed_eigenspace_phase_action (i : Fin (D.d + L)) :
    (β i : ℂ) * coord z₀ i =
      (m : ℂ) * (((L * D.seedScale : ℝ) : ℂ) * coord e₀ i +
        ((1 - D.seedTheta + L * D.seedTheta : ℝ) : ℂ) * coord z₀ i) := by
  have h := congrFun (rowCoords_action hE hΩ β hA z₀) i
  rw [Matrix.mulVec_diagonal, D.seedGram_phaseOnes hm hm', Matrix.mulVec_smul,
    Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul] at h
  have hZ : Eᴴ *ᵥ z₀ = coord z₀ := by rw [rowCoords, D.refGram_phaseOnes]
  rw [hZ] at h
  simpa only [rowCoords, Complex.ofReal_mul, Complex.ofReal_natCast, Pi.smul_apply, Pi.add_apply, smul_eq_mul] using h.symm

theorem seed_eigenspace_perp_support (a : Fin D.d → ℂ)
    (ha : ⟪D.baseSynthesis D.coeff, D.baseSynthesis a⟫_ℂ = 0) (i : Fin (D.d + L)) :
    coord (D.oldRowCoeffs L a) i = 0 ∨ β i = m := by
  have h := D.seed_eigenspace_base_action hm hm' E β hE hΩ hA a i
  rw [ha, mul_zero, zero_mul, add_zero] at h
  rcases mul_eq_zero.mp (by rw [sub_mul, h, sub_self] :
      ((β i : ℂ) - (m : ℂ)) * coord (D.oldRowCoeffs L a) i = 0) with hm | hz
  · exact Or.inr (Complex.ofReal_inj.mp (sub_eq_zero.mp hm))
  · exact Or.inl hz

theorem seed_eigenspace_direction_support (hL : 1 ≤ L) (i : Fin (D.d + L)) :
    coord e₀ i = 0 ∨ β i = m * seedSmallEigenvalue D.seedTheta L ∨
      β i = m * seedLargeEigenvalue D.seedTheta L := by
  have h := D.seed_eigenspace_base_action hm hm' E β hE hΩ hA D.coeff i
  have he : ‖D.baseSynthesis D.coeff‖ = 1 := D.unit_direction
  rw [inner_self_eq_norm_sq_to_K, he] at h
  norm_num at h
  exact seed_plane_support D.seedScale_pos hm (by exact_mod_cast hL) h
    (D.seed_eigenspace_phase_action hm hm' E β hE hΩ hA i)

theorem seed_eigenspace_direction_response (hL : 1 ≤ L) (Φ : ℝ → ℝ) :
    ∑ i, Φ (β i) * ‖coord e₀ i‖ ^ 2 =
      seedDirectionFraction D.seedTheta L * Φ (m * seedSmallEigenvalue D.seedTheta L) +
      (1 - seedDirectionFraction D.seedTheta L) * Φ (m * seedLargeEigenvalue D.seedTheta L) := by
  have hθ := D.seedTheta_bounds
  have hunit : ‖D.baseSynthesis D.coeff‖ = 1 := D.unit_direction
  apply seed_direction_response hθ.1 (by linarith [hθ.2]) (by exact_mod_cast hL) hm β _
    (D.seed_eigenspace_direction_support hm hm' E β hE hΩ hA hL)
  · rw [← rowCoords_norm_sq hE hΩ, D.refGram_qform_oldRowCoeffs, hunit, one_pow]
  · rw [← rowCoords_qform hE hΩ β hA, D.seedGram_qform_oldRowCoeffs hm hm', hunit, one_pow, mul_one]

/-- The scalar response on the whole old span splits into the selected
direction and its orthogonal complement. -/
theorem old_span_response (hL : 1 ≤ L) (Φ : ℝ → ℝ) (a : Fin D.d → ℂ) :
    ∑ i, ‖coord (D.oldRowCoeffs L a) i‖ ^ 2 * Φ (β i) =
      Φ m * ‖D.baseSynthesis a -
        ⟪D.baseSynthesis D.coeff, D.baseSynthesis a⟫_ℂ • D.baseSynthesis D.coeff‖ ^ 2 +
      (seedDirectionFraction D.seedTheta L * Φ (m * seedSmallEigenvalue D.seedTheta L) +
        (1 - seedDirectionFraction D.seedTheta L) * Φ (m * seedLargeEigenvalue D.seedTheta L)) *
        ‖⟪D.baseSynthesis D.coeff, D.baseSynthesis a⟫_ℂ‖ ^ 2 := by
  let I := Fin (D.d + L)
  let e := D.baseSynthesis D.coeff
  let x := D.baseSynthesis a
  let s := ⟪e, x⟫_ℂ
  let b := a - s • D.coeff
  let v := coord e₀
  let w := coord (D.oldRowCoeffs L b)
  have hsplit : a = s • D.coeff + b := by simp [b, add_sub_cancel]
  have hperp : D.baseSynthesis b = x - s • e := by
    dsimp [b, x, e]
    rw [D.baseSynthesis_sub, D.baseSynthesis_smul]
  have hUnit : ‖e‖ = 1 := D.unit_direction
  have ho : ⟪e, D.baseSynthesis b⟫_ℂ = 0 := by
    rw [hperp, inner_sub_right, inner_smul_right, inner_self_eq_norm_sq_to_K, hUnit]
    norm_num [s]
  have hv (i : I) := D.seed_eigenspace_direction_support hm hm' E β hE hΩ hA hL i
  have hw (i : I) := D.seed_eigenspace_perp_support hm hm' E β hE hΩ hA b ho i
  have hdisj (i : I) : v i = 0 ∨ w i = 0 := by
    rcases hw i with h | h
    · exact Or.inr h
    · rcases hv i with h' | h' | h'
      · exact Or.inl h'
      · have hh := seed_eigenvalues_order D.seedTheta_bounds.1 (by linarith [D.seedTheta_bounds.2])
          (show 1 ≤ (L : ℝ) by exact_mod_cast hL)
        exact ((mul_lt_mul_of_pos_left hh.2.1 hm).ne (by simpa [h] using h'.symm)).elim
      · have hh := seed_eigenvalues_order D.seedTheta_bounds.1 (by linarith [D.seedTheta_bounds.2])
          (show 1 ≤ (L : ℝ) by exact_mod_cast hL)
        exact ((mul_lt_mul_of_pos_left hh.2.2 hm).ne (by simpa [h] using h')).elim
  have hCE : coord (D.oldRowCoeffs L a) = s • v + w := by
    conv_lhs => rw [hsplit]
    simp only [D.oldRowCoeffs_add, D.oldRowCoeffs_smul, rowCoords, Matrix.mulVec_add, Matrix.mulVec_smul]
    rfl
  rw [hCE]
  have hNorm (i : I) : ‖(s • v + w) i‖ ^ 2 = ‖s‖ ^ 2 * ‖v i‖ ^ 2 + ‖w i‖ ^ 2 := by
    rcases hdisj i with h | h
    · simp [h]
    · simp [h, norm_mul, mul_pow]
  have heR := D.seed_eigenspace_direction_response hm hm' E β hE hΩ hA hL Φ
  have hPerpR := seed_perp_response β w hw Φ
  have hwNorm : ∑ i, ‖w i‖ ^ 2 = ‖x - s • e‖ ^ 2 := by
    change (∑ i, ‖coord (D.oldRowCoeffs L b) i‖ ^ 2) = _
    rw [← rowCoords_norm_sq hE hΩ, D.refGram_qform_oldRowCoeffs, hperp]
  calc
    _ = (Φ m * ∑ i, ‖w i‖ ^ 2) +
      ‖s‖ ^ 2 * ∑ i, Φ (β i) * ‖v i‖ ^ 2 := by
      rw [← hPerpR, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [hNorm]
      ring
    _ = _ := by
      rw [hwNorm, show (∑ i, Φ (β i) * ‖v i‖ ^ 2) = _ from heR]
      change _ = Φ m * ‖x - s • e‖ ^ 2 + _ * ‖s‖ ^ 2
      ring

end Eigenspace

end

end SchauderBasisOrbits.DirectionalInput

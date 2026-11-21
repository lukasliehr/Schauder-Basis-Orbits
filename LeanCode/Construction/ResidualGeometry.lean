import LeanCode.Construction.Residual
import LeanCode.Measure.Information
import LeanCode.Finite.BlockPrefixes

open MeasureTheory ContinuousLinearMap InnerProductSpace
open scoped InnerProductSpace ComplexConjugate ComplexOrder

noncomputable section

namespace SchauderBasisOrbits

local postfix:1024 "†" => ContinuousLinearMap.adjoint

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {N : ℕ}

/-- Finite information operator of the helper directions with a common gain. -/
def residualInformation (u : ℝ) (v : Fin N → E) : E →L[ℂ] E :=
  u • (synthCLM v ∘L (synthCLM v)†)

theorem residualInformation_positive {u : ℝ} (hu : 0 ≤ u) (v : Fin N → E) :
    (residualInformation u v).IsPositive := by
  have h := (ContinuousLinearMap.isPositive_self_comp_adjoint (synthCLM (𝕜 := ℂ) v)).smul_of_nonneg
    ((RCLike.ofReal_nonneg (K := ℂ)).mpr hu)
  simpa only [residualInformation, ← Complex.coe_algebraMap, algebraMap_smul] using h

theorem residualInformation_apply (u : ℝ) (v : Fin N → E) (x : E) :
    residualInformation u v x = u • ∑ i, ⟪v i, x⟫_ℂ • v i := by
  simp only [residualInformation, smul_apply, comp_apply, synthCLM_apply, synth]
  exact congrArg (u • ·) (Finset.sum_congr rfl fun i _ ↦
    congrArg (fun z : ℂ ↦ z • v i) (synthCLM_adjoint_coordinate v x i))

theorem residualInformation_eq_zero_of_orthogonal (u : ℝ) (v : Fin N → E) {x : E}
    (hx : ∀ i, ⟪v i, x⟫_ℂ = 0) : residualInformation u v x = 0 := by
  simp [residualInformation_apply, hx]

private def allOnes : EuclideanSpace ℂ (Fin N) := WithLp.toLp 2 (fun _ ↦ 1)

private theorem allOnes_norm_sq : ‖(allOnes : EuclideanSpace ℂ (Fin N))‖ ^ 2 = (N : ℝ) := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [allOnes]

private theorem inner_allOnes (c : EuclideanSpace ℂ (Fin N)) :
    ⟪allOnes, c⟫_ℂ = ∑ i, c i := by
  simp [PiLp.inner_apply, allOnes]

private theorem equicorrelated_synthGram (v : Fin N → E) {a : ℝ}
    (hv : ∀ i, ‖v i‖ = 1) (hc : ∀ i j, i ≠ j → ⟪v i, v j⟫_ℂ = (a ^ 2 : ℝ)) :
    (synthCLM v)† ∘L synthCLM v =
      (1 - a ^ 2) • (1 : EuclideanSpace ℂ (Fin N) →L[ℂ] EuclideanSpace ℂ (Fin N)) +
      (a ^ 2 : ℝ) • rankOne ℂ allOnes allOnes := by
  apply ContinuousLinearMap.ext
  intro c
  apply WithLp.ofLp_injective
  funext i
  have hGram (j : Fin N) :
      ⟪v i, v j⟫_ℂ = (if i = j then ((1 - a ^ 2 : ℝ) : ℂ) else 0) + (↑(a ^ 2) : ℂ) := by
    by_cases hIJ : i = j
    · subst j
      simp only [inner_self_eq_norm_sq_to_K, hv, Complex.ofReal_one, one_pow, if_pos rfl]
      push_cast
      ring
    · simp [hIJ, hc i j hIJ]
  change ((synthCLM (𝕜 := ℂ) v)† (synthCLM v c)) i =
    (↑(1 - a ^ 2 : ℝ) : ℂ) * c i + (↑(a ^ 2) : ℂ) * (⟪allOnes, c⟫_ℂ * allOnes i)
  rw [synthCLM_adjoint_coordinate, synthCLM_apply, synth, inner_sum]
  simp only [inner_smul_right, hGram, mul_add, Finset.sum_add_distrib, inner_allOnes,
    show (allOnes : EuclideanSpace ℂ (Fin N)) i = 1 from rfl, mul_one]
  rw [← Finset.sum_mul]
  have hs : (∑ j : Fin N, c j * (if i = j then ((1 - a ^ 2 : ℝ) : ℂ) else 0)) =
      c i * ((1 - a ^ 2 : ℝ) : ℂ) := by
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      simp [Ne.symm hji]
    · simp
  rw [hs]
  ring

private def equicorrelationEigenvalue (N : ℕ) (a : ℝ) : ℝ := 1 + ((N : ℝ) - 1) * a ^ 2

theorem norm_residualInformation_le (u : ℝ) (hu : 0 ≤ u) (v : Fin N → E)
    {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) (hv : ∀ i, ‖v i‖ = 1)
    (hc : ∀ i j, i ≠ j → ⟪v i, v j⟫_ℂ = (a ^ 2 : ℝ)) :
    ‖residualInformation u v‖ ≤ u * equicorrelationEigenvalue N a := by
  unfold residualInformation
  rw [norm_smul, Real.norm_of_nonneg hu, norm_comp_adjoint, ← norm_adjoint_comp]
  apply mul_le_mul_of_nonneg_left _ hu
  rw [equicorrelated_synthGram v hv hc]
  refine (norm_add_le _ _).trans ?_
  have hnonneg : 0 ≤ 1 - a ^ 2 := by nlinarith
  rw [norm_smul, norm_smul, Real.norm_of_nonneg hnonneg, Real.norm_of_nonneg (sq_nonneg a),
    norm_rankOne, ← sq, allOnes_norm_sq]
  calc
    _ ≤ (1 - a ^ 2) * 1 + a ^ 2 * (N : ℝ) := by
      exact add_le_add (mul_le_mul_of_nonneg_left (ContinuousLinearMap.norm_id_le :
        ‖(1 : EuclideanSpace ℂ (Fin N) →L[ℂ] EuclideanSpace ℂ (Fin N))‖ ≤ 1) hnonneg) le_rfl
    _ = _ := by unfold equicorrelationEigenvalue; ring

theorem norm_residualInformation_lt_two_mul {u a : ℝ} (hu : 0 < u) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (v : Fin N → E) (hv : ∀ i, ‖v i‖ = 1)
    (hc : ∀ i j, i ≠ j → ⟪v i, v j⟫_ℂ = (a ^ 2 : ℝ))
    (hNa : ((N : ℝ) - 1) * a ^ 2 < 1) : ‖residualInformation u v‖ < 2 * u := by
  apply (norm_residualInformation_le u hu.le v ha ha1 hv hc).trans_lt
  rw [mul_comm 2]
  apply mul_lt_mul_of_pos_left _ hu
  unfold equicorrelationEigenvalue
  linarith

private theorem synthGram_allOnes (v : Fin N → E) {a : ℝ}
    (hv : ∀ i, ‖v i‖ = 1) (hc : ∀ i j, i ≠ j → ⟪v i, v j⟫_ℂ = (a ^ 2 : ℝ)) :
    ((synthCLM (𝕜 := ℂ) v)† ∘L synthCLM v) allOnes =
      equicorrelationEigenvalue N a • allOnes := by
  rw [equicorrelated_synthGram v hv hc, add_apply, smul_apply, smul_apply, rankOne_apply]
  have h : ⟪(allOnes : EuclideanSpace ℂ (Fin N)), allOnes⟫_ℂ = ((N : ℝ) : ℂ) := by
    rw [inner_allOnes]
    simp [allOnes]
  rw [h]
  change (1 - a ^ 2) • (allOnes : EuclideanSpace ℂ (Fin N)) +
    a ^ 2 • (N : ℝ) • (allOnes : EuclideanSpace ℂ (Fin N)) =
    equicorrelationEigenvalue N a • (allOnes : EuclideanSpace ℂ (Fin N))
  rw [smul_smul, ← add_smul]
  congr 1
  unfold equicorrelationEigenvalue
  ring

theorem residualInformation_capture_lower {u a : ℝ} (hu : 0 < u) (ha : 0 < a)
    (v : Fin N → E) (hv : ∀ i, ‖v i‖ = 1)
    (hc : ∀ i j, i ≠ j → ⟪v i, v j⟫_ℂ = (a ^ 2 : ℝ))
    (hNa : ((N : ℝ) - 1) * a ^ 2 < 1) (hNlower : 1 ≤ (N : ℝ) * a ^ 2)
    (e : E) (he : ∀ i, ⟪v i, e⟫_ℂ = (a : ℂ)) :
    u / (1 + 2 * u) ≤ Complex.re ⟪e, informationCapture (residualInformation u v) e⟫_ℂ := by
  let X := synthCLM (𝕜 := ℂ) v
  let y := X allOnes
  let J := residualInformation u v
  let ell := equicorrelationEigenvalue N a
  let b := u * a / (1 + u * ell)
  have hN : 1 ≤ (N : ℝ) := by
    by_contra! hn
    norm_cast at hn
    have h0 : N = 0 := by omega
    simp [h0] at hNlower
    linarith
  have hell : 0 < ell := by
    dsimp [ell, equicorrelationEigenvalue]
    have : 0 ≤ ((N : ℝ) - 1) * a ^ 2 := mul_nonneg (sub_nonneg.mpr hN) (sq_nonneg a)
    linarith
  have hell2 : ell < 2 := by dsimp [ell, equicorrelationEigenvalue]; linarith
  have hbden : 0 < 1 + u * ell := by positivity
  have hXe : (X†) e = a • allOnes := by
    apply WithLp.ofLp_injective
    funext i
    change ((synthCLM (𝕜 := ℂ) v)† e) i = (a : ℂ) * 1
    rw [synthCLM_adjoint_coordinate, he, mul_one]
  have hJe : J e = (u * a) • y := by
    change u • X ((X†) e) = _
    rw [hXe, ContinuousLinearMap.map_smul_of_tower, smul_smul]
  have hJy : J y = (u * ell) • y := by
    change u • X (((X†) ∘L X) allOnes) = _
    rw [show (((X†) ∘L X) allOnes) = ell • allOnes from synthGram_allOnes v hv hc,
      ContinuousLinearMap.map_smul_of_tower, smul_smul]
  have hJpos : J.IsPositive := residualInformation_positive hu.le v
  let A : E →L[ℂ] E := 1 + J
  have hAunit : IsUnit A := isUnit_one_add_positive hJpos
  have hAinv := Ring.mul_inverse_cancel A hAunit
  have hAcap : A * informationCapture J = J := by
    rw [informationCapture_eq_one_sub_inverse hJpos, mul_sub, mul_one, hAinv]
    change 1 + J - 1 = J
    abel
  have hAby : A (b • y) = J e := by
    rw [ContinuousLinearMap.map_smul_of_tower]
    change b • (y + J y) = J e
    rw [hJy, hJe]
    nth_rewrite 1 [← one_smul ℝ y]
    rw [← add_smul, smul_smul]
    have heq : b * (1 + u * ell) = u * a := div_mul_cancel₀ _ hbden.ne'
    exact congrArg (· • y) heq
  have hcap : informationCapture J e = b • y :=
    (ContinuousLinearMap.isUnit_iff_bijective.mp hAunit).1
      ((DFunLike.congr_fun hAcap e).trans hAby.symm)
  have hPair : ⟪e, y⟫_ℂ = ((N : ℝ) * a : ℝ) := by
    change ⟪e, X allOnes⟫_ℂ = _
    rw [← adjoint_inner_left, hXe]
    change ⟪(a : ℂ) • (allOnes : EuclideanSpace ℂ (Fin N)), allOnes⟫_ℂ = _
    rw [inner_smul_left]
    have h : ⟪(allOnes : EuclideanSpace ℂ (Fin N)), allOnes⟫_ℂ = ((N : ℝ) : ℂ) := by
      rw [inner_allOnes]
      simp [allOnes]
    simp only [Complex.conj_ofReal, h, Complex.ofReal_mul]
    ring
  change u / (1 + 2 * u) ≤ Complex.re ⟪e, informationCapture J e⟫_ℂ
  rw [hcap]
  change _ ≤ Complex.re ⟪e, (b : ℂ) • y⟫_ℂ
  rw [inner_smul_right, hPair]
  change u / (1 + 2 * u) ≤ Complex.re ((↑b : ℂ) * ↑((N : ℝ) * a))
  rw [← Complex.ofReal_mul, Complex.ofReal_re]
  have hb : b * ((N : ℝ) * a) = u * ((N : ℝ) * a ^ 2) / (1 + u * ell) := by
    dsimp [b]
    ring
  rw [hb]
  calc
    _ ≤ u / (1 + u * ell) := by
      apply div_le_div_of_nonneg_left hu.le hbden
      have hm := mul_le_mul_of_nonneg_left hell2.le hu.le
      linarith only [hm]
    _ ≤ _ := div_le_div_of_nonneg_right (by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hNlower hu.le) hbden.le

/-- Normalize a sum of the base residual and one centered copy of the residual noise. -/
def residualDirection (d variance : ℝ) (e noise : E) : E :=
  ((Real.sqrt (d ^ 2 + variance))⁻¹ : ℝ) • (d • e + noise)

theorem inner_residualDirection_base (d variance : ℝ) (e noise x : E)
    (h : ⟪noise, x⟫_ℂ = 0) :
    ⟪residualDirection d variance e noise, x⟫_ℂ =
      (↑(d / Real.sqrt (d ^ 2 + variance)) : ℂ) * ⟪e, x⟫_ℂ := by
  unfold residualDirection
  change ⟪(↑((Real.sqrt (d ^ 2 + variance))⁻¹) : ℂ) • ((d : ℂ) • e + noise), x⟫_ℂ = _
  rw [inner_smul_left, inner_add_left, inner_smul_left, h, add_zero,
    Complex.conj_ofReal, Complex.conj_ofReal]
  push_cast
  ring

theorem inner_residualDirection_pair (d variance : ℝ) (e ξ ξ' : E)
    (he : ‖e‖ = 1) (hξ : ⟪e, ξ⟫_ℂ = 0) (hξ' : ⟪e, ξ'⟫_ℂ = 0) :
    ⟪residualDirection d variance e ξ, residualDirection d variance e ξ'⟫_ℂ =
      ((↑(Real.sqrt (d ^ 2 + variance)) : ℂ)⁻¹) ^ 2 *
        ((↑(d ^ 2) : ℂ) + ⟪ξ, ξ'⟫_ℂ) := by
  have hξconj : ⟪ξ, e⟫_ℂ = 0 := by rw [← inner_conj_symm, hξ, map_zero]
  let q := (Real.sqrt (d ^ 2 + variance))⁻¹
  change ⟪(q : ℂ) • ((d : ℂ) • e + ξ), (q : ℂ) • ((d : ℂ) • e + ξ')⟫_ℂ = _
  simp only [inner_smul_left, inner_smul_right, inner_add_left, inner_add_right,
    Complex.conj_ofReal, hξ', hξconj, he, inner_self_eq_norm_sq_to_K,
    Complex.ofReal_one, one_pow, mul_zero, add_zero, zero_add, mul_one]
  dsimp only [q]
  push_cast
  ring

theorem norm_residualDirection (d variance : ℝ) (e noise : E)
    (hpos : 0 < d ^ 2 + variance) (he : ‖e‖ = 1)
    (horth : ⟪e, noise⟫_ℂ = 0) (hv : ‖noise‖ ^ 2 = variance) :
    ‖residualDirection d variance e noise‖ = 1 := by
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), inner_residualDirection_pair _ _ _ _ _ he horth horth,
    inner_self_eq_norm_sq_to_K]
  have hs := Real.sq_sqrt hpos.le
  have hh : ((↑(Real.sqrt (d ^ 2 + variance)) : ℂ)⁻¹) ^ 2 *
      ((↑(d ^ 2) : ℂ) + (↑‖noise‖ : ℂ) ^ 2) = 1 := by
    rw [← Complex.ofReal_pow, hv, ← Complex.ofReal_add, ← Complex.ofReal_inv, ← Complex.ofReal_pow,
      ← Complex.ofReal_mul, inv_pow, hs, inv_mul_cancel₀ hpos.ne', Complex.ofReal_one]
  change Real.sqrt (Complex.re (((↑(Real.sqrt (d ^ 2 + variance)) : ℂ)⁻¹) ^ 2 *
    ((↑(d ^ 2) : ℂ) + (↑‖noise‖ : ℂ) ^ 2))) = 1
  rw [hh]
  simp

theorem inner_residualDirection_distinct (d variance : ℝ) (e ξ ξ' : E)
    (he : ‖e‖ = 1) (hξ : ⟪e, ξ⟫_ℂ = 0) (hξ' : ⟪e, ξ'⟫_ℂ = 0)
    (hcross : ⟪ξ, ξ'⟫_ℂ = 0) :
    ⟪residualDirection d variance e ξ, residualDirection d variance e ξ'⟫_ℂ =
      (↑((d / Real.sqrt (d ^ 2 + variance)) ^ 2) : ℂ) := by
  rw [inner_residualDirection_pair d variance e ξ ξ' he hξ hξ', hcross, add_zero]
  push_cast
  rw [div_eq_mul_inv, mul_pow, mul_comm]

end SchauderBasisOrbits

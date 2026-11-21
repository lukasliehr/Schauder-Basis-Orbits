import LeanCode.Measure.Products
import LeanCode.Finite.Families
import Mathlib.Analysis.InnerProductSpace.Positive

open MeasureTheory Filter Submodule ContinuousLinearMap
open scoped InnerProductSpace ComplexConjugate NNReal ComplexOrder MatrixOrder
local postfix:1024 "†" => ContinuousLinearMap.adjoint

noncomputable section

namespace SchauderBasisOrbits

section Capture

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

private theorem one_add_norm_inner_lower {J : E →L[ℂ] E} (hJ : J.IsPositive) (x : E) :
    ‖x‖ ^ 2 * ((1 : ℝ≥0) : ℝ) ≤ ‖⟪((1 + J) : E →L[ℂ] E) x, x⟫_ℂ‖ := by
  calc
    _ ≤ Complex.re ⟪((1 + J) : E →L[ℂ] E) x, x⟫_ℂ := by
      change ‖x‖ ^ 2 * ((1 : ℝ≥0) : ℝ) ≤ Complex.re ⟪x + J x, x⟫_ℂ
      simp only [inner_add_left, Complex.add_re, NNReal.coe_one, mul_one]
      have h : Complex.re ⟪x, x⟫_ℂ = ‖x‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) x
      rw [h]
      exact le_add_of_nonneg_right (hJ.re_inner_nonneg_left x)
    _ ≤ _ := Complex.re_le_norm _

theorem isUnit_one_add_positive {J : E →L[ℂ] E} (hJ : J.IsPositive) :
    IsUnit (1 + J) :=
  ContinuousLinearMap.isUnit_of_forall_le_norm_inner_map _ (c := 1) one_pos
    (one_add_norm_inner_lower hJ)

theorem norm_inverse_one_add_positive_le_one {J : E →L[ℂ] E} (hJ : J.IsPositive) :
    ‖Ring.inverse (1 + J)‖ ≤ 1 := by
  let A : E →L[ℂ] E := 1 + J
  have hanti : AntilipschitzWith 1 A := by
    simpa only [inv_one] using ContinuousLinearMap.antilipschitz_of_forall_le_inner_map
      A (c := 1) one_pos (one_add_norm_inner_lower hJ)
  have hunit : IsUnit A := isUnit_one_add_positive hJ
  have hmul := Ring.mul_inverse_cancel A hunit
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x ↦ ?_
  have h := hanti.le_mul_dist (Ring.inverse A x) 0
  have hx : A (Ring.inverse A x) = x := DFunLike.congr_fun hmul x
  simpa only [dist_zero_right, map_zero, NNReal.coe_one, one_mul, hx] using h

/-- Information captured by projecting onto a finite coupled family. -/
def informationCapture (J : E →L[ℂ] E) : E →L[ℂ] E :=
  J * Ring.inverse (1 + J)

theorem informationCapture_eq_one_sub_inverse {J : E →L[ℂ] E} (hJ : J.IsPositive) :
    informationCapture J = 1 - Ring.inverse (1 + J) := by
  rw [informationCapture]
  have h := Ring.mul_inverse_cancel (1 + J) (isUnit_one_add_positive hJ)
  rw [add_mul, one_mul] at h
  exact eq_sub_iff_add_eq.mpr (by simpa only [add_comm] using h)

theorem informationCapture_resolvent {J J' : E →L[ℂ] E}
    (hJ : J.IsPositive) (hJ' : J'.IsPositive) :
    informationCapture J - informationCapture J' =
      Ring.inverse (1 + J) * (J - J') * Ring.inverse (1 + J') := by
  rw [informationCapture_eq_one_sub_inverse hJ, informationCapture_eq_one_sub_inverse hJ']
  rw [show J - J' = (1 + J) - (1 + J') by abel, mul_sub, sub_mul,
    Ring.inverse_mul_cancel _ (isUnit_one_add_positive hJ), one_mul,
    mul_assoc (Ring.inverse (1 + J)) (1 + J'),
    Ring.mul_inverse_cancel _ (isUnit_one_add_positive hJ'), mul_one]
  abel

theorem norm_informationCapture_sub_le {J J' : E →L[ℂ] E}
    (hJ : J.IsPositive) (hJ' : J'.IsPositive) :
    ‖informationCapture J - informationCapture J'‖ ≤ ‖J - J'‖ := by
  rw [informationCapture_resolvent hJ hJ']
  refine (norm_mul_le _ _).trans ?_
  calc
    _ ≤ (‖Ring.inverse (1 + J)‖ * ‖J - J'‖) * ‖Ring.inverse (1 + J')‖ :=
      mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
    _ ≤ (1 * ‖J - J'‖) * 1 :=
      mul_le_mul (mul_le_mul_of_nonneg_right (norm_inverse_one_add_positive_le_one hJ) (norm_nonneg _))
        (norm_inverse_one_add_positive_le_one hJ') (norm_nonneg _) (by positivity)
    _ = _ := by simp

end Capture

section FiniteGeometry

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem starProjection_map_linearIsometry (L : E →ₗᵢ[ℂ] F)
    (S : Submodule ℂ E) [FiniteDimensional ℂ S] (x : E) :
    (S.map L.toLinearMap).starProjection (L x) = L (S.starProjection x) := by
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · exact ⟨S.starProjection x, S.starProjection_apply_mem x, rfl⟩
  · rintro _ ⟨y, hy, rfl⟩
    change ⟪L x - L (S.starProjection x), L y⟫_ℂ = 0
    rw [← map_sub, L.inner_map_map]
    exact (Submodule.mem_orthogonal' S _).mp (S.sub_starProjection_mem_orthogonal x) y hy

end FiniteGeometry

/-- A finite synthesis split into an orthogonal centered component and a base component. -/
structure CenteredSynthesis (E F : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] (n : ℕ) where
  pullback : E →ₗᵢ[ℂ] F
  centered : EuclideanSpace ℂ (Fin n) →L[ℂ] F
  means : EuclideanSpace ℂ (Fin n) →L[ℂ] E
  inner_eq_zero (x : E) (c : EuclideanSpace ℂ (Fin n)) :
    ⟪pullback x, centered c⟫_ℂ = 0

namespace CenteredSynthesis

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable {n : ℕ} (D : CenteredSynthesis E F n)

/-- Synthesis of the original uncentered family. -/
def full : EuclideanSpace ℂ (Fin n) →L[ℂ] F :=
  D.centered + D.pullback.toContinuousLinearMap.comp D.means

@[simp] theorem full_apply (c : EuclideanSpace ℂ (Fin n)) :
    D.full c = D.centered c + D.pullback (D.means c) := rfl

@[simp] theorem full_adjoint_pullback (x : E) : (D.full†) (D.pullback x) = (D.means†) x := by
  apply ext_inner_left ℂ
  intro c
  rw [adjoint_inner_right, adjoint_inner_right, full_apply, inner_add_left,
    D.pullback.inner_map_map, ← inner_conj_symm (D.centered c) (D.pullback x),
    D.inner_eq_zero, map_zero, zero_add]

theorem full_gram_comp :
    D.full† ∘L D.full = D.centered† ∘L D.centered + D.means† ∘L D.means := by
  apply ContinuousLinearMap.ext
  intro c
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
  apply ext_inner_left ℂ
  intro v
  rw [inner_add_right, adjoint_inner_right, adjoint_inner_right, adjoint_inner_right,
    full_apply, full_apply, inner_add_left, inner_add_right, inner_add_right,
    D.inner_eq_zero, D.pullback.inner_map_map,
    ← inner_conj_symm (D.centered v) (D.pullback (D.means c)), D.inner_eq_zero, map_zero]
  ring

def centeredGram : Matrix (Fin n) (Fin n) ℂ := clmGram D.centered

def fullGram : Matrix (Fin n) (Fin n) ℂ := clmGram D.full

theorem centeredGram_posDef (hD : Function.Injective D.centered) : D.centeredGram.PosDef :=
  clmGram_posDef D.centered hD

theorem full_injective (hD : Function.Injective D.centered) : Function.Injective D.full := by
  apply LinearMap.ker_eq_bot.mp
  rw [Submodule.eq_bot_iff]
  intro c hc
  change D.full c = 0 at hc
  have he := D.full_gram_comp
  have hq := DFunLike.congr_fun he c
  change (D.full†) (D.full c) = (D.centered†) (D.centered c) + (D.means†) (D.means c) at hq
  rw [hc, map_zero] at hq
  have hlo := congrArg (fun v ↦ Complex.re ⟪c, v⟫_ℂ) hq
  simp only [inner_zero_right, Complex.zero_re, inner_add_right, Complex.add_re,
    adjoint_inner_right] at hlo
  change 0 = RCLike.re ⟪D.centered c, D.centered c⟫_ℂ +
    RCLike.re ⟪D.means c, D.means c⟫_ℂ at hlo
  rw [inner_self_eq_norm_sq, inner_self_eq_norm_sq] at hlo
  have hzero : ‖D.centered c‖ = 0 := by
    nlinarith [sq_nonneg ‖D.centered c‖, sq_nonneg ‖D.means c‖]
  exact hD ((norm_eq_zero.mp hzero).trans D.centered.map_zero.symm)

def centeredInverse : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n) :=
  Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) D.centeredGram⁻¹

def fullInverse : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n) :=
  Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) D.fullGram⁻¹

theorem centeredInverse_left (hD : Function.Injective D.centered)
    (c : EuclideanSpace ℂ (Fin n)) :
    D.centeredInverse ((D.centered†) (D.centered c)) = c := by
  have hdet := (Matrix.isUnit_iff_isUnit_det _).mp (D.centeredGram_posDef hD).isUnit
  have h := congrArg (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n))
    (Matrix.nonsing_inv_mul D.centeredGram hdet)
  rw [map_mul, map_one] at h
  change D.centeredInverse * Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) (clmGram D.centered) = 1 at h
  rw [toEuclideanCLM_clmGram] at h
  exact DFunLike.congr_fun h c

theorem centeredInverse_right (hD : Function.Injective D.centered)
    (c : EuclideanSpace ℂ (Fin n)) :
    (D.centered†) (D.centered (D.centeredInverse c)) = c :=
  clmGram_inv_apply_cancel D.centered hD c

theorem centeredInverse_adjoint (hD : Function.Injective D.centered) :
    D.centeredInverse† = D.centeredInverse := by
  change star D.centeredInverse = D.centeredInverse
  unfold centeredInverse
  rw [← map_star, show star D.centeredGram⁻¹ = D.centeredGram⁻¹ from
    (D.centeredGram_posDef hD).inv.isHermitian]

theorem centeredInverse_positive (hD : Function.Injective D.centered) :
    D.centeredInverse.IsPositive := by
  have h := (ContinuousLinearMap.isPositive_adjoint_comp_self D.centered).conj_adjoint
    D.centeredInverse
  have he : D.centeredInverse ∘L (D.centered† ∘L D.centered) ∘L D.centeredInverse† =
      D.centeredInverse := by
    rw [D.centeredInverse_adjoint hD]
    apply ContinuousLinearMap.ext
    intro c
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.comp_apply, D.centeredInverse_right hD]
  rwa [he] at h

/-- The finite-rank information operator on the reference base space. -/
def information : E →L[ℂ] E := D.means ∘L D.centeredInverse ∘L D.means†

@[simp] theorem information_apply (x : E) :
    D.information x = D.means (D.centeredInverse ((D.means†) x)) := rfl

theorem information_positive (hD : Function.Injective D.centered) :
    D.information.IsPositive :=
  (D.centeredInverse_positive hD).conj_adjoint D.means

theorem information_mem_range (x : E) : D.information x ∈ LinearMap.range D.means.toLinearMap :=
  ⟨D.centeredInverse ((D.means†) x), rfl⟩

theorem information_apply_of_mem_orthogonal {x : E}
    (hx : x ∈ (LinearMap.range D.means.toLinearMap)ᗮ) : D.information x = 0 := by
  have hz : (D.means†) x = 0 := by
    apply ext_inner_left ℂ
    intro c
    rw [adjoint_inner_right, inner_zero_right]
    exact (Submodule.mem_orthogonal _ _).mp hx _ ⟨c, rfl⟩
  simp [hz]

theorem informationCapture_apply_eq (hD : Function.Injective D.centered) (x : E) :
    informationCapture D.information x = D.means (D.fullInverse ((D.means†) x)) := by
  let b := D.fullInverse ((D.means†) x)
  have hgb : (D.full†) (D.full b) = (D.means†) x :=
    clmGram_inv_apply_cancel D.full (D.full_injective hD) _
  have hsum : (D.centered†) (D.centered b) + (D.means†) (D.means b) = (D.means†) x :=
    (DFunLike.congr_fun (D.full_gram_comp) b).symm.trans hgb
  let A : E →L[ℂ] E := 1 + D.information
  have hresp : A (D.means b) = D.information x := by
    change D.means b + D.means (D.centeredInverse ((D.means†) (D.means b))) =
      D.means (D.centeredInverse ((D.means†) x))
    calc
      _ = D.means (D.centeredInverse ((D.centered†) (D.centered b)) +
          D.centeredInverse ((D.means†) (D.means b))) := by
        rw [map_add, D.centeredInverse_left hD]
      _ = _ := by rw [← map_add, hsum]
  have hh : A (x - D.means b) = x := by
    rw [map_sub, hresp]
    change x + D.information x - D.information x = x
    exact add_sub_cancel_right _ _
  have hunit := isUnit_one_add_positive (D.information_positive hD)
  have hinv := DFunLike.congr_fun (Ring.inverse_mul_cancel A hunit) (x - D.means b)
  change (Ring.inverse A) (A (x - D.means b)) = x - D.means b at hinv
  rw [hh] at hinv
  rw [informationCapture_eq_one_sub_inverse (D.information_positive hD)]
  change x - (Ring.inverse A) x = D.means b
  rw [hinv]
  abel

theorem starProjection_full_sq (hD : Function.Injective D.centered) (x : E) :
    haveI : FiniteDimensional ℂ (LinearMap.range D.full.toLinearMap) :=
      Module.Finite.range D.full.toLinearMap
    ‖(LinearMap.range D.full.toLinearMap).starProjection (D.pullback x)‖ ^ 2 =
      Complex.re ⟪x, informationCapture D.information x⟫_ℂ := by
  let _ : FiniteDimensional ℂ (LinearMap.range D.full.toLinearMap) :=
    Module.Finite.range D.full.toLinearMap
  let V := LinearMap.range D.full.toLinearMap
  calc
    _ = RCLike.re ⟪D.pullback x, V.starProjection (D.pullback x)⟫_ℂ := by
      rw [← V.inner_starProjection_left_eq_right]
      exact (V.re_inner_starProjection_eq_normSq _).symm
    _ = _ := by
      change Complex.re ⟪D.pullback x, V.starProjection (D.pullback x)⟫_ℂ = _
      rw [starProjection_range_eq_gram D.full (D.full_injective hD), D.full_adjoint_pullback,
        ← show D.fullInverse = Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) (clmGram D.full)⁻¹ from rfl,
        D.full_apply, inner_add_right, D.inner_eq_zero, zero_add, D.pullback.inner_map_map,
        D.informationCapture_apply_eq hD]


theorem fullGram_eq : D.fullGram = D.centeredGram + clmGram D.means := by
  apply (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n)).injective
  change Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) D.fullGram =
    Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) (D.centeredGram + clmGram D.means)
  simp only [fullGram, centeredGram, map_add, toEuclideanCLM_clmGram]
  exact D.full_gram_comp

theorem norm_means_sq_le_information (hD : Function.Injective D.centered)
    (c : EuclideanSpace ℂ (Fin n)) :
    ‖D.means c‖ ^ 2 ≤ ‖D.information‖ * ‖D.centered c‖ ^ 2 := by
  let e := Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n)
  let R := CFC.sqrt D.centeredGram
  let S := e R
  let I := e R⁻¹
  have hC := D.centeredGram_posDef hD
  have hR : R.PosDef := posDef_sqrt hC
  have hRR : R * R = D.centeredGram := sqrt_mul_sqrt_of_posDef hC
  have hSadj : S† = S := by
    change star (e R) = e R
    rw [← map_star, show star R = R from hR.isHermitian]
  have hIadj : I† = I := by
    change star (e R⁻¹) = e R⁻¹
    rw [← map_star, show star R⁻¹ = R⁻¹ from hR.inv.isHermitian]
  have hIS : I * S = 1 := by
    change e R⁻¹ * e R = 1
    rw [← map_mul, Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hR.isUnit),
      map_one]
  have hII : I * I = D.centeredInverse := by
    change e R⁻¹ * e R⁻¹ = e D.centeredGram⁻¹
    rw [← map_mul, ← Matrix.mul_inv_rev, hRR]
  have hSS : S * S = D.centered† ∘L D.centered := by
    change e R * e R = _
    rw [← map_mul, hRR, centeredGram, toEuclideanCLM_clmGram]
  have hSsq : ‖S c‖ ^ 2 = ‖D.centered c‖ ^ 2 := by
    have hc : (S†) (S c) = (D.centered†) (D.centered c) := by
      rw [hSadj]
      exact DFunLike.congr_fun hSS c
    calc
      _ = RCLike.re ⟪c, (S†) (S c)⟫_ℂ := by rw [adjoint_inner_right, inner_self_eq_norm_sq]
      _ = _ := by rw [hc, adjoint_inner_right, inner_self_eq_norm_sq]
  let T := D.means ∘L I
  have hJ : T ∘L T† = D.information := by
    dsimp only [T]
    rw [adjoint_comp, hIadj]
    apply ContinuousLinearMap.ext
    intro x
    change D.means ((I * I) ((D.means†) x)) = D.information x
    rw [hII, information_apply]
  have hnorm : ‖T‖ ^ 2 = ‖D.information‖ := by rw [← hJ, norm_comp_adjoint]
  have hT := T.le_opNorm (S c)
  have heq : T (S c) = D.means c :=
    congrArg D.means (DFunLike.congr_fun hIS c)
  rw [heq] at hT
  calc
    _ ≤ (‖T‖ * ‖S c‖) ^ 2 := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr hT
    _ = _ := by rw [mul_pow, hnorm, hSsq]

theorem fullGram_bounds (hD : Function.Injective D.centered) {a : ℝ}
    (ha : ‖D.information‖ ≤ a) :
    D.centeredGram ≤ D.fullGram ∧ D.fullGram ≤ (1 + a) • D.centeredGram := by
  have hG : D.fullGram.IsHermitian := clmGram_isHermitian D.full
  have hC : D.centeredGram.IsHermitian := clmGram_isHermitian D.centered
  refine ⟨matrix_le_of_qform_le hC hG fun c ↦ ?_,
    matrix_le_of_qform_le hG (hC.smul (IsSelfAdjoint.all _)) fun c ↦ ?_⟩
  · rw [fullGram_eq, qform_add, qform_clmGram]
    exact le_add_of_nonneg_right (sq_nonneg _)
  · rw [fullGram_eq, qform_add, qform_smul, centeredGram,
      qform_clmGram, qform_clmGram, add_mul, one_mul]
    exact add_le_add (le_refl _) ((D.norm_means_sq_le_information hD _).trans
      (mul_le_mul_of_nonneg_right ha (sq_nonneg _)))

theorem fullGram_prefix (hD : Function.Injective D.centered) {a K : ℝ}
    (ha : ‖D.information‖ ≤ a) (hK : PB D.centeredGram K) :
    PB D.fullGram (Real.sqrt (1 + a) * K) := by
  obtain ⟨hl, hu⟩ := D.fullGram_bounds hD ha
  have ha0 := (norm_nonneg _).trans ha
  simpa only [div_one] using hK.relative zero_lt_one (le_add_of_nonneg_right ha0)
    (by simpa only [one_smul] using hl) hu


section Transport

variable {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
variable (L : F →ₗᵢ[ℂ] G)

/-- Transport the target Hilbert space without changing the base or any coefficients. -/
def mapTarget : CenteredSynthesis E G n where
  pullback := L.comp D.pullback
  centered := L.toContinuousLinearMap ∘L D.centered
  means := D.means
  inner_eq_zero x c := by
    change ⟪L (D.pullback x), L (D.centered c)⟫_ℂ = 0
    rw [L.inner_map_map]
    exact D.inner_eq_zero x c

theorem mapTarget_full : (D.mapTarget L).full = L.toContinuousLinearMap ∘L D.full := by
  apply ContinuousLinearMap.ext
  intro c
  change L (D.centered c) + L (D.pullback (D.means c)) =
    L (D.centered c + D.pullback (D.means c))
  exact (map_add L _ _).symm

theorem mapTarget_centeredGram : (D.mapTarget L).centeredGram = D.centeredGram := by
  let e := Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n)
  apply e.injective
  change e (clmGram (L.toContinuousLinearMap ∘L D.centered)) = e (clmGram D.centered)
  rw [show e (clmGram (L.toContinuousLinearMap ∘L D.centered)) =
      (L.toContinuousLinearMap ∘L D.centered)† ∘L (L.toContinuousLinearMap ∘L D.centered) from
    toEuclideanCLM_clmGram _, show e (clmGram D.centered) = D.centered† ∘L D.centered from
    toEuclideanCLM_clmGram _, adjoint_comp]
  apply ContinuousLinearMap.ext
  intro c
  change (D.centered†) ((L.toContinuousLinearMap†) (L (D.centered c))) =
    (D.centered†) (D.centered c)
  exact congrArg (D.centered†) (DFunLike.congr_fun (L.adjoint_comp_self) (D.centered c))

theorem mapTarget_centered_injective (hD : Function.Injective D.centered) :
    Function.Injective (D.mapTarget L).centered :=
  L.injective.comp hD

theorem mapTarget_information : (D.mapTarget L).information = D.information := by
  unfold information centeredInverse
  rw [mapTarget_centeredGram]
  rfl

end Transport


end CenteredSynthesis

namespace FiberWeight

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
variable {κ : Measure β} [IsFiniteMeasure κ] (W : FiberWeight α κ)
variable (ρ : Measure α) [IsFiniteMeasure ρ]

theorem lift₂_eq_center_add_pullback {u : α × β → ℂ} (hu : Measurable u)
    {B : ℝ} (hB : ∀ p, ‖u p‖ ≤ B) :
    lift₂ (W.normalizedMeasure ρ) u hu B hB =
      lift₂ (W.normalizedMeasure ρ) (W.center u) (W.measurable_center hu)
        (2 * B) (W.norm_center_le hu hB) +
      W.pullback ρ (lift₂ ρ (W.mean u) (W.measurable_mean hu) B (W.norm_mean_le hu hB)) := by
  let p := lift₂ (W.normalizedMeasure ρ) (W.center u) (W.measurable_center hu)
        (2 * B) (W.norm_center_le hu hB)
  let m := lift₂ ρ (W.mean u) (W.measurable_mean hu) B (W.norm_mean_le hu hB)
  have hcomp := (W.measurePreserving_fst ρ).quasiMeasurePreserving.ae_eq_comp
    (ae_lift₂ ρ (W.mean u) (W.measurable_mean hu) B (W.norm_mean_le hu hB))
  apply Lp.ext
  filter_upwards [ae_lift₂ (W.normalizedMeasure ρ) u hu B hB, Lp.coeFn_add p (W.pullback ρ m),
    ae_lift₂ (W.normalizedMeasure ρ) (W.center u) (W.measurable_center hu)
      (2 * B) (W.norm_center_le hu hB), W.ae_pullback ρ m, hcomp] with x hx hsum hp hm hc
  simp only [Pi.add_apply] at hsum
  simp only [Function.comp_apply] at hc
  change (m : α → ℂ) x.1 = _ at hc
  change (lift₂ (W.normalizedMeasure ρ) u hu B hB) x = (p + W.pullback ρ m) x
  rw [hx, hsum, show p x = W.center u x from hp, hm, hc, center, sub_add_cancel]

/-- The centered and mean synthesis operators of a finite raw family. -/
def synthesis {n : ℕ} (u : Fin n → α × β → ℂ) (hu : ∀ i, Measurable (u i))
    (B : Fin n → ℝ) (hB : ∀ i p, ‖u i p‖ ≤ B i) :
    CenteredSynthesis (Lp ℂ 2 ρ) (Lp ℂ 2 (W.normalizedMeasure ρ)) n where
  pullback := W.pullback ρ
  centered := synthCLM (fun i ↦ lift₂ (W.normalizedMeasure ρ) (W.center (u i))
    (W.measurable_center (hu i)) (2 * B i) (W.norm_center_le (hu i) (hB i)))
  means := synthCLM (fun i ↦ lift₂ ρ (W.mean (u i)) (W.measurable_mean (hu i))
    (B i) (W.norm_mean_le (hu i) (hB i)))
  inner_eq_zero x c := by
    rw [synthCLM_apply, synth, inner_sum]
    apply Finset.sum_eq_zero
    intro i _
    rw [inner_smul_right, W.inner_pullback_center_eq_zero ρ x (hu i) (hB i), mul_zero]

theorem synthesis_full {n : ℕ} (u : Fin n → α × β → ℂ) (hu : ∀ i, Measurable (u i))
    (B : Fin n → ℝ) (hB : ∀ i p, ‖u i p‖ ≤ B i) :
    (W.synthesis ρ u hu B hB).full = synthCLM (fun i ↦
      lift₂ (W.normalizedMeasure ρ) (u i) (hu i) (B i) (hB i)) := by
  apply ContinuousLinearMap.ext
  intro c
  simp only [CenteredSynthesis.full_apply, synthesis, synthCLM_apply, synth, map_sum, map_smul]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← smul_add, ← W.lift₂_eq_center_add_pullback ρ (hu i) (hB i)]

end FiberWeight

end SchauderBasisOrbits

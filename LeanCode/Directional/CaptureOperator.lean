module

public import LeanCode.Directional.ProjectionResponse

@[expose] public section

open Submodule ContinuousLinearMap InnerProductSpace
open scoped InnerProductSpace ComplexConjugate

noncomputable section

namespace SchauderBasisOrbits

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private theorem selfAdjoint_eq_of_re_inner_eq {F G : H →L[ℂ] H}
    (hF : IsSelfAdjoint F) (hG : IsSelfAdjoint G)
    (h : ∀ x, Complex.re ⟪x, F x⟫_ℂ = Complex.re ⟪x, G x⟫_ℂ) : F = G := by
  apply ContinuousLinearMap.coe_injective
  apply (ext_inner_map F.toLinearMap G.toLinearMap).mp
  intro x
  change ⟪F x, x⟫_ℂ = ⟪G x, x⟫_ℂ
  apply Complex.ext
  · exact ((inner_re_symm (𝕜 := ℂ) (F x) x).trans (h x)).trans
      (inner_re_symm (𝕜 := ℂ) (G x) x).symm
  · have hfi : (⟪F x, x⟫_ℂ).im = 0 := by
      have heq : conj ⟪F x, x⟫_ℂ = ⟪F x, x⟫_ℂ := by
        rw [inner_conj_symm]
        exact ((isSelfAdjoint_iff_isSymmetric.mp hF) x x).symm
      have hi := congrArg Complex.im heq
      simp only [Complex.conj_im] at hi
      linarith
    have hgi : (⟪G x, x⟫_ℂ).im = 0 := by
      have heq : conj ⟪G x, x⟫_ℂ = ⟪G x, x⟫_ℂ := by
        rw [inner_conj_symm]
        exact ((isSelfAdjoint_iff_isSymmetric.mp hG) x x).symm
      have hi := congrArg Complex.im heq
      simp only [Complex.conj_im] at hi
      linarith
    rw [hfi, hgi]

private theorem inner_projected_of_supported (V : Submodule ℂ H) [V.HasOrthogonalProjection]
    (A : H →L[ℂ] H) (hRange : ∀ x, A x ∈ V) (hVanish : ∀ x ∈ Vᗮ, A x = 0) (x : H) :
    ⟪x, A x⟫_ℂ = ⟪V.starProjection x, A (V.starProjection x)⟫_ℂ := by
  have hx := V.sub_starProjection_mem_orthogonal x
  have hA := hVanish _ hx
  rw [map_sub, sub_eq_zero] at hA
  have ho := (V.mem_orthogonal' _).mp hx (A x) (hRange x)
  rw [inner_sub_left, sub_eq_zero] at ho
  exact ho.trans (congrArg (fun y ↦ ⟪V.starProjection x, y⟫_ℂ) hA)

private theorem capture_zero_from_zero {J : H →L[ℂ] H} (hJ : J.IsPositive) {x : H}
    (hx : J x = 0) : informationCapture J x = 0 := by
  have h := DFunLike.congr_fun (Ring.inverse_mul_cancel (1 + J) (isUnit_one_add_positive hJ)) x
  change Ring.inverse (1 + J) (((1 + J) : H →L[ℂ] H) x) = x at h
  have hh : ((1 + J) : H →L[ℂ] H) x = x := by change x + J x = x; rw [hx, add_zero]
  rw [hh] at h
  rw [informationCapture_eq_one_sub_inverse hJ]
  change x - Ring.inverse (1 + J) x = 0
  rw [h, sub_self]

/-- Identify the capture operator from its quadratic form on its supporting subspace. -/
theorem informationCapture_eq_projected_sum (V : Submodule ℂ H) [V.HasOrthogonalProjection]
    {e : H} (he : ‖e‖ = 1) (heV : e ∈ V) {J : H →L[ℂ] H} (hJ : J.IsPositive)
    (hRange : ∀ x, J x ∈ V) {s t : ℝ}
    (hQuad : ∀ x ∈ V, Complex.re ⟪x, informationCapture J x⟫_ℂ =
      s * ‖x - rankOne ℂ e e x‖ ^ 2 + t * ‖rankOne ℂ e e x‖ ^ 2) :
    informationCapture J = s • (V.starProjection - rankOne ℂ e e) + t • rankOne ℂ e e := by
  let U := ℂ ∙ e
  have hUV : U ≤ V := (Submodule.span_singleton_le_iff_mem e V).mpr heV
  let Q := U.starProjection
  have hQ : rankOne ℂ e e = Q := rankOne_unit_eq_starProjection e he
  let T := s • (V.starProjection - Q) + t • Q
  rw [hQ]
  change informationCapture J = T
  have hpV : IsSelfAdjoint V.starProjection :=
    isSelfAdjoint_iff_isSymmetric.mpr V.starProjection_isSymmetric
  have hpQ : IsSelfAdjoint Q :=
    isSelfAdjoint_iff_isSymmetric.mpr U.starProjection_isSymmetric
  have hT : IsSelfAdjoint T := by
    change star (s • (V.starProjection - Q) + t • Q) =
      s • (V.starProjection - Q) + t • Q
    simp only [star_add, star_sub, star_smul, star_trivial, hpV.star_eq, hpQ.star_eq]
  have hC : IsSelfAdjoint (informationCapture J) := by
    rw [informationCapture_eq_one_sub_inverse hJ]
    exact (IsSelfAdjoint.one _).sub (((IsSelfAdjoint.one _).add hJ.isSelfAdjoint).ringInverse)
  have hCran (x : H) : informationCapture J x ∈ V := hRange _
  have hTran (x : H) : T x ∈ V := by
    change (s : ℂ) • (V.starProjection x - Q x) + (t : ℂ) • Q x ∈ V
    have hx := hUV (U.starProjection_apply_mem x)
    exact V.add_mem (V.smul_mem _ (V.sub_mem (V.starProjection_apply_mem x) hx)) (V.smul_mem _ hx)
  have hJzero (x : H) (hx : x ∈ Vᗮ) : J x = 0 := by
    apply ext_inner_left ℂ
    intro y
    have hs : ⟪J y, x⟫_ℂ = ⟪y, J x⟫_ℂ := hJ.isSymmetric y x
    rw [inner_zero_right, ← hs]
    exact (V.mem_orthogonal x).mp hx (J y) (hRange y)
  have hCzero (x : H) (hx : x ∈ Vᗮ) : informationCapture J x = 0 :=
    capture_zero_from_zero hJ (hJzero x hx)
  have hTzero (x : H) (hx : x ∈ Vᗮ) : T x = 0 := by
    have hv := V.starProjection_apply_eq_zero_iff.mpr hx
    have hq : Q x = 0 := U.starProjection_apply_eq_zero_iff.mpr (Submodule.orthogonal_le hUV hx)
    change s • (V.starProjection x - Q x) + t • Q x = 0
    rw [hv, hq, sub_zero, smul_zero, smul_zero, add_zero]
  have hTform (x : H) (hx : x ∈ V) :
      Complex.re ⟪x, T x⟫_ℂ = s * ‖x - Q x‖ ^ 2 + t * ‖Q x‖ ^ 2 := by
    have hQform : Complex.re ⟪x, Q x⟫_ℂ = ‖Q x‖ ^ 2 := by
      have h := U.re_inner_starProjection_eq_normSq x
      rw [U.inner_starProjection_left_eq_right] at h
      exact h
    have hsplit := U.norm_sq_eq_add_norm_sq_starProjection x
    rw [U.starProjection_orthogonal', ContinuousLinearMap.sub_apply] at hsplit
    change ‖x‖ ^ 2 = ‖Q x‖ ^ 2 + ‖x - Q x‖ ^ 2 at hsplit
    change Complex.re ⟪x, (s : ℂ) • (V.starProjection x - Q x) + (t : ℂ) • Q x⟫_ℂ = _
    rw [V.starProjection_eq_self_iff.mpr hx, inner_add_right, inner_smul_right, inner_smul_right,
      inner_sub_right]
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      sub_zero, Complex.sub_re, hQform]
    have hx' : Complex.re ⟪x, x⟫_ℂ = ‖x‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) x
    rw [hx', hsplit]
    ring
  apply selfAdjoint_eq_of_re_inner_eq hC hT
  intro x
  rw [inner_projected_of_supported V (informationCapture J) hCran hCzero,
    inner_projected_of_supported V T hTran hTzero, hQuad _ (V.starProjection_apply_mem x),
    hTform _ (V.starProjection_apply_mem x), hQ]

theorem norm_starProjection_sub_rankOne_le_one (V : Submodule ℂ H) [V.HasOrthogonalProjection]
    {e : H} (he : ‖e‖ = 1) (heV : e ∈ V) :
    ‖V.starProjection - rankOne ℂ e e‖ ≤ 1 := by
  let U := ℂ ∙ e
  have hUV : U ≤ V := (Submodule.span_singleton_le_iff_mem e V).mpr heV
  have hSub : V.starProjection - U.starProjection = Uᗮ.starProjection * V.starProjection := by
    rw [U.starProjection_orthogonal', sub_mul, one_mul]
    change V.starProjection - U.starProjection =
      V.starProjection - U.starProjection ∘L V.starProjection
    rw [Submodule.starProjection_comp_starProjection_of_le hUV]
  rw [rankOne_unit_eq_starProjection e he, hSub]
  refine (norm_mul_le _ _).trans ?_
  simpa only [one_mul] using mul_le_mul Uᗮ.starProjection_norm_le V.starProjection_norm_le (norm_nonneg _) zero_le_one

theorem information_eq_projected_sum (V : Submodule ℂ H) [V.HasOrthogonalProjection]
    {e : H} (he : ‖e‖ = 1) (heV : e ∈ V) {J : H →L[ℂ] H} (hJ : J.IsPositive)
    (hRange : ∀ x, J x ∈ V) {s t : ℝ} (hs : s ≠ 1) (ht : t ≠ 1)
    (hQuad : ∀ x ∈ V, Complex.re ⟪x, informationCapture J x⟫_ℂ =
      s * ‖x - rankOne ℂ e e x‖ ^ 2 + t * ‖rankOne ℂ e e x‖ ^ 2) :
    J = (s / (1 - s)) • (V.starProjection - rankOne ℂ e e) +
      (t / (1 - t)) • rankOne ℂ e e := by
  let U := ℂ ∙ e
  have hUV : U ≤ V := (Submodule.span_singleton_le_iff_mem e V).mpr heV
  let Q := U.starProjection
  have hQ : rankOne ℂ e e = Q := rankOne_unit_eq_starProjection e he
  have hp : V.starProjection * V.starProjection = V.starProjection := by
    change V.starProjection ∘L V.starProjection = V.starProjection
    exact Submodule.starProjection_comp_starProjection_of_le le_rfl
  have hq : Q * Q = Q := by
    change U.starProjection ∘L U.starProjection = U.starProjection
    exact Submodule.starProjection_comp_starProjection_of_le le_rfl
  have hqv : Q * V.starProjection = Q := Submodule.starProjection_comp_starProjection_of_le hUV
  have hvq : V.starProjection * Q = Q := by
    apply ContinuousLinearMap.ext
    intro x
    change V.starProjection (Q x) = Q x
    exact V.starProjection_eq_self_iff.mpr (hUV (U.starProjection_apply_mem x))
  have hp' : (V.starProjection - Q) * (V.starProjection - Q) = V.starProjection - Q := by
    rw [sub_mul, mul_sub, mul_sub, hp, hvq, hqv, hq, sub_self, sub_zero]
  have hpq : (V.starProjection - Q) * Q = 0 := by rw [sub_mul, hvq, hq, sub_self]
  have hqp : Q * (V.starProjection - Q) = 0 := by rw [mul_sub, hqv, hq, sub_self]
  rw [hQ]
  exact information_of_capture_sum hJ hp' hq hpq hqp hs ht
    ((informationCapture_eq_projected_sum V he heV hJ hRange hQuad).trans
      (by rw [hQ]))

end SchauderBasisOrbits

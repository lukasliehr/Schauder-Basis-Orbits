module

public import LeanCode.Directional.SelectedGram

@[expose] public section

open Filter Function MeasureTheory Submodule
open scoped ENNReal BigOperators ComplexConjugate InnerProductSpace MatrixOrder ComplexOrder

namespace SchauderBasisOrbits

noncomputable section

theorem FiberWeight.integral_weight_eq_mass_mean
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {ν : Measure Y}
    (W : FiberWeight X ν) (f : X × Y → ℂ) (s : X) :
    ∫ y, (W.weight (s, y) : ℂ) * f (s, y) ∂ν = (W.mass : ℂ) * W.mean f s := by
  rw [FiberWeight.mean, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with y
  rw [FiberWeight.density, Complex.real_smul]
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr W.mass_pos.ne']

theorem FiberWeight.mean_fst {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {ν : Measure Y} (W : FiberWeight X ν) (f : X → ℂ) (s : X) :
    W.mean (fun p => f p.1) s = f s := by
  change (∫ y, W.density (s, y) • f s ∂ν) = _
  rw [integral_smul_const, W.integral_density, one_smul]

theorem FiberWeight.mean_mul_fst {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {ν : Measure Y} (W : FiberWeight X ν) (f : X → ℂ) (g : X × Y → ℂ) (s : X) :
    W.mean (fun p => f p.1 * g p) s = f s * W.mean g s := by
  rw [FiberWeight.mean, FiberWeight.mean, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with y
  simp only [Complex.real_smul]
  ring

theorem FiberWeight.mean_const {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {ν : Measure Y} (W : FiberWeight X ν) (c : ℂ) (s : X) :
    W.mean (fun _ => c) s = c := W.mean_fst (fun _ => c) s

namespace DirectionalInput

variable {ι : Type*} [Fintype ι]
variable {ρ : Measure (Base ι)} [IsFiniteMeasure ρ] (D : DirectionalInput ρ)

theorem ae_direction :
    ⇑(synth (productFamily ρ D.frequencies) D.coeff) =ᵐ[ρ] D.direction := by
  classical
  unfold DirectionalInput.direction synth
  refine (Lp.coeFn_fun_finsetSum Finset.univ (fun i => D.coeff i • productFamily ρ D.frequencies i)).trans ?_
  have h (i : Fin D.d) :
      ⇑(D.coeff i • productFamily ρ D.frequencies i : Lp ℂ 2 ρ) =ᵐ[ρ]
        (fun x => D.coeff i • mixedChar (D.frequencies i) x) :=
    (Lp.coeFn_smul _ _).trans ((ae_lift₂ ρ _ _ _ _).mono fun _ hx =>
      congrArg (fun z : ℂ => D.coeff i • z) hx)
  filter_upwards [(Finset.eventually_all Finset.univ).mpr (fun i _ => h i)] with x hx
  exact Finset.sum_congr rfl hx

theorem integral_norm_direction_sq : ∫ x, ‖D.direction x‖ ^ 2 ∂ρ = 1 := by
  let e := synth (productFamily ρ D.frequencies) D.coeff
  have h : ‖e‖ ^ 2 = ∫ x, ‖e x‖ ^ 2 ∂ρ := by
    calc
      _ = RCLike.re ⟪e,e⟫_ℂ := (inner_self_eq_norm_sq e).symm
      _ = ∫ x, RCLike.re ⟪e x, e x⟫_ℂ ∂ρ := by
        rw [L2.inner_def, integral_re (L2.integrable_inner (𝕜 := ℂ) e e)]
      _ = _ := integral_congr_ae (Eventually.of_forall fun x => inner_self_eq_norm_sq (e x))
  have hEq : (∫ x, ‖e x‖ ^ 2 ∂ρ) = ∫ x, ‖D.direction x‖ ^ 2 ∂ρ :=
    integral_congr_ae (D.ae_direction.mono (fun x hx => congrArg (fun z : ℂ => ‖z‖ ^ 2) hx))
  rw [← hEq, ← h, show ‖e‖ = 1 from D.unit_direction]
  norm_num

set_option maxHeartbeats 1500000 in
private theorem rowSeedGram_as_mean {L : ℕ} {m : ℝ} (hm : 0 < m)
    (hm' : m ≤ ((1 : ℝ) / 2) ^ L) (i j : Fin (D.d + L)) :
    D.rowSeedGram L hm hm' i j =
      (m : ℂ) * ∫ x, (D.seedFiber L hm hm').mean (fun p => conj (D.rawRow i p) * D.rawRow j p) x ∂ρ := by
  let W := D.seedFiber L hm hm'
  let G (p : RowPoint ι L) := conj (D.rawRow i p) * D.rawRow j p
  have hG : Measurable G :=
    (Complex.continuous_conj.measurable.comp (D.measurable_rawRow i)).mul (D.measurable_rawRow j)
  let f (p : RowPoint ι L) := (W.weight p : ℂ) * G p
  have hint : Integrable f (ρ.prod (torusHaar (Fin L))) := by
    apply Integrable.of_bound (W.measurable_weight.complex_ofReal.mul hG).aestronglyMeasurable 1
    refine Eventually.of_forall fun p => ?_
    change ‖(W.weight p : ℂ) * (conj (D.rawRow i p) * D.rawRow j p)‖ ≤ 1
    simp only [norm_mul, Complex.norm_conj, D.norm_rawRow, mul_one, Complex.norm_real,
      Real.norm_of_nonneg (W.weight_pos p).le]
    exact W.weight_le_one p
  change (∫ p, f p ∂ρ.prod (torusHaar (Fin L))) = (m : ℂ) * ∫ x, W.mean G x ∂ρ
  calc
    _ = ∫ x, ∫ y, f (x, y) ∂torusHaar (Fin L) ∂ρ := integral_prod f hint
    _ = ∫ x, (m : ℂ) * W.mean G x ∂ρ :=
      integral_congr_ae (Eventually.of_forall fun x => W.integral_weight_eq_mass_mean G x)
    _ = _ := integral_const_mul _ _

set_option maxHeartbeats 1500000 in
theorem rowSeedGram_base_base {L : ℕ} {m : ℝ} (hm : 0 < m)
    (hm' : m ≤ ((1 : ℝ) / 2) ^ L) (i j : Fin D.d) :
    D.rowSeedGram L hm hm' (Fin.castAdd L i) (Fin.castAdd L j) =
      (m : ℂ) * ⟪productFamily ρ D.frequencies i, productFamily ρ D.frequencies j⟫_ℂ := by
  rw [rowSeedGram_as_mean, productFamily, productFamily, inner_lift₂]
  have hfun : (fun p : RowPoint ι L =>
      conj (D.rawRow (Fin.castAdd L i) p) * D.rawRow (Fin.castAdd L j) p) =
      (fun p => conj (mixedChar (D.frequencies i) p.1) * mixedChar (D.frequencies j) p.1) := by
    funext p
    simp [rawRow]
  rw [hfun]
  have h (x : Base ι) : (D.seedFiber L hm hm').mean
      (fun p => conj (mixedChar (D.frequencies i) p.1) * mixedChar (D.frequencies j) p.1) x =
      conj (mixedChar (D.frequencies i) x) * mixedChar (D.frequencies j) x :=
    (D.seedFiber L hm hm').mean_fst
      (fun p : Base ι => conj (mixedChar (D.frequencies i) p) * mixedChar (D.frequencies j) p) x
  simp_rw [h]

set_option maxHeartbeats 1500000 in
theorem rowSeedGram_base_phase {L : ℕ} {m : ℝ} (hm : 0 < m)
    (hm' : m ≤ ((1 : ℝ) / 2) ^ L) (i : Fin D.d) (j : Fin L) :
    D.rowSeedGram L hm hm' (Fin.castAdd L i) (Fin.natAdd D.d j) =
      (m : ℂ) * ((D.seedScale : ℂ) *
        ⟪productFamily ρ D.frequencies i, synth (productFamily ρ D.frequencies) D.coeff⟫_ℂ) := by
  rw [rowSeedGram_as_mean]
  have hfun : (fun p : RowPoint ι L =>
      conj (D.rawRow (Fin.castAdd L i) p) * D.rawRow (Fin.natAdd D.d j) p) =
      (fun p => conj (mixedChar (D.frequencies i) p.1) * phaseRow j p) := by
    funext p
    simp [rawRow]
  rw [hfun]
  have heq (x : Base ι) :
      (D.seedFiber L hm hm').mean
        (fun p : RowPoint ι L => conj (mixedChar (D.frequencies i) p.1) * phaseRow j p) x =
        conj (mixedChar (D.frequencies i) x) * D.amplitude x := by
    calc
      _ = conj (mixedChar (D.frequencies i) x) *
        (D.seedFiber L hm hm').mean (phaseRow j) x :=
        (D.seedFiber L hm hm').mean_mul_fst (fun p => conj (mixedChar (D.frequencies i) p)) (phaseRow j) x
      _ = _ := by rw [D.seedFiber_mean_phase hm hm']
  simp only [heq]
  rw [L2.inner_def]
  apply congrArg (fun a : ℂ => (m : ℂ) * a)
  rw [← integral_const_mul (D.seedScale : ℂ)]
  apply integral_congr_ae
  filter_upwards [ae_lift₂ ρ (mixedChar (D.frequencies i)) (continuous_mixedChar _).measurable
    1 (fun x => (norm_mixedChar _ x).le), D.ae_direction] with x hi hx
  rw [RCLike.inner_apply']
  change conj (mixedChar (D.frequencies i) x) * D.amplitude x =
    (D.seedScale : ℂ) * (conj (productFamily ρ D.frequencies i x) *
      synth (productFamily ρ D.frequencies) D.coeff x)
  change productFamily ρ D.frequencies i x = _ at hi
  rw [hi, hx, amplitude]
  ring

theorem rowSeedGram_phase_phase {L : ℕ} {m : ℝ} (hm : 0 < m)
    (hm' : m ≤ ((1 : ℝ) / 2) ^ L) [IsProbabilityMeasure ρ] (i j : Fin L) :
    D.rowSeedGram L hm hm' (Fin.natAdd D.d i) (Fin.natAdd D.d j) =
      (m : ℂ) * (if i = j then 1 else (D.seedTheta : ℂ)) := by
  classical
  rw [rowSeedGram_as_mean]
  congr 1
  have hfun : (fun p : RowPoint ι L => conj (D.rawRow (Fin.natAdd D.d i) p) *
      D.rawRow (Fin.natAdd D.d j) p) = (fun p => conj (phaseRow i p) * phaseRow j p) := by
    funext p
    simp [rawRow]
  rw [hfun]
  by_cases hij : i = j
  · subst j
    have h₁ : (fun p : RowPoint ι L => conj (phaseRow i p) * phaseRow i p) = fun _ => 1 := by
      funext p
      rw [mul_comm, Complex.mul_conj', phaseRow, fourier_apply, Circle.norm_coe]
      norm_num
    simp [h₁, FiberWeight.mean_const]
  · simp only [ite_eq_right hij, D.seedFiber_mean_phase_pair hm hm' hij]
    have he (x : Base ι) : conj (D.amplitude x) * D.amplitude x =
        (D.seedTheta : ℂ) * ((‖D.direction x‖ : ℂ) ^ 2) := by
      rw [amplitude, map_mul, Complex.conj_ofReal, seedTheta, Complex.ofReal_pow]
      calc
        _ = (D.seedScale : ℂ) ^ 2 * (D.direction x * conj (D.direction x)) := by ring
        _ = _ := by rw [Complex.mul_conj']
    simp_rw [he]
    rw [integral_const_mul]
    simp_rw [← Complex.ofReal_pow, integral_complex_ofReal, D.integral_norm_direction_sq, Complex.ofReal_one, mul_one]

end DirectionalInput

end

end SchauderBasisOrbits

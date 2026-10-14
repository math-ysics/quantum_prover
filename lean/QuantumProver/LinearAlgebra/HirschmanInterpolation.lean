import Mathlib
import QuantumProver.LinearAlgebra.SBTProbabilityWeight
import QuantumProver.LinearAlgebra.HirschmanRadialLimit
import QuantumProver.LinearAlgebra.HirschmanBoundaryChange

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace QuantumProver.HirschmanInterpolation

def beta (θ t : ℝ) : ℝ :=
  Real.sin (Real.pi * θ) /
    (2 * θ * (Real.cosh (Real.pi * t) + Real.cos (Real.pi * θ)))

theorem sin_pi_mul_pos {θ : ℝ} (hθ : θ ∈ Ioo (0 : ℝ) 1) :
    0 < Real.sin (Real.pi * θ) := by
  apply Real.sin_pos_of_pos_of_lt_pi
  · exact mul_pos Real.pi_pos hθ.1
  · nlinarith [Real.pi_pos, hθ.2]

theorem cos_pi_mul_gt_neg_one {θ : ℝ} (hθ : θ ∈ Ioo (0 : ℝ) 1) :
    -1 < Real.cos (Real.pi * θ) := by
  have h := Real.cos_lt_cos_of_nonneg_of_le_pi
    (mul_nonneg Real.pi_pos.le hθ.1.le) (le_refl Real.pi)
    (show Real.pi * θ < Real.pi by nlinarith [Real.pi_pos, hθ.2])
  simpa using h

theorem beta_denominator_pos {θ : ℝ} (hθ : θ ∈ Ioo (0 : ℝ) 1) (t : ℝ) :
    0 < Real.cosh (Real.pi * t) + Real.cos (Real.pi * θ) := by
  have hc := cos_pi_mul_gt_neg_one hθ
  have hh := Real.one_le_cosh (Real.pi * t)
  linarith

theorem beta_pos {θ : ℝ} (hθ : θ ∈ Ioo (0 : ℝ) 1) (t : ℝ) : 0 < beta θ t := by
  exact div_pos (sin_pi_mul_pos hθ)
    (mul_pos (mul_pos (by norm_num) hθ.1) (beta_denominator_pos hθ t))

theorem beta_nonneg {θ : ℝ} (hθ : θ ∈ Ioo (0 : ℝ) 1) (t : ℝ) :
    0 ≤ beta θ t := (beta_pos hθ t).le

@[simp] theorem beta_neg (θ t : ℝ) : beta θ (-t) = beta θ t := by
  simp [beta]

theorem continuous_beta {θ : ℝ} (hθ : θ ∈ Ioo (0 : ℝ) 1) : Continuous (beta θ) := by
  unfold beta
  apply Continuous.div continuous_const
  · fun_prop
  · intro t
    exact (mul_pos (mul_pos (by norm_num) hθ.1) (beta_denominator_pos hθ t)).ne'

theorem beta_exp_denominator_pos {θ : ℝ} (hθ : θ ∈ Ioo (0 : ℝ) 1) (t : ℝ) :
    0 < Real.exp (Real.pi * t) ^ 2 +
      2 * Real.cos (Real.pi * θ) * Real.exp (Real.pi * t) + 1 := by
  have hs := sin_pi_mul_pos hθ
  have ht := Real.sin_sq_add_cos_sq (Real.pi * θ)
  nlinarith [sq_nonneg (Real.exp (Real.pi * t) + Real.cos (Real.pi * θ)), sq_pos_of_pos hs]

theorem beta_eq_exp {θ : ℝ} (hθ : θ ∈ Ioo (0 : ℝ) 1) (t : ℝ) :
    beta θ t = Real.sin (Real.pi * θ) * Real.exp (Real.pi * t) /
      (θ * (Real.exp (Real.pi * t) ^ 2 +
        2 * Real.cos (Real.pi * θ) * Real.exp (Real.pi * t) + 1)) := by
  have he := (Real.exp_pos (Real.pi * t)).ne'
  have hd := (beta_denominator_pos hθ t).ne'
  have hq := (beta_exp_denominator_pos hθ t).ne'
  rw [beta, Real.cosh_eq, Real.exp_neg]
  field_simp [he, hθ.1.ne', hd, hq]
  ring

def betaPrimitive (θ t : ℝ) : ℝ :=
  Real.arctan ((Real.exp (Real.pi * t) + Real.cos (Real.pi * θ)) /
    Real.sin (Real.pi * θ)) / (Real.pi * θ)

theorem hasDerivAt_betaPrimitive {θ : ℝ} (hθ : θ ∈ Ioo (0 : ℝ) 1) (t : ℝ) :
    HasDerivAt (betaPrimitive θ) (beta θ t) t := by
  have he : HasDerivAt (fun x : ℝ => Real.exp (Real.pi * x))
      (Real.exp (Real.pi * t) * Real.pi) t := by
    simpa only [id_eq, mul_one] using ((hasDerivAt_id t).const_mul Real.pi).exp
  have hs := (sin_pi_mul_pos hθ).ne'
  have hq := (beta_exp_denominator_pos hθ t).ne'
  have hd : 1 + ((Real.exp (Real.pi * t) + Real.cos (Real.pi * θ)) /
      Real.sin (Real.pi * θ)) ^ 2 =
      (Real.exp (Real.pi * t) ^ 2 +
        2 * Real.cos (Real.pi * θ) * Real.exp (Real.pi * t) + 1) /
          Real.sin (Real.pi * θ) ^ 2 := by
    field_simp [hs]
    nlinarith [Real.sin_sq_add_cos_sq (Real.pi * θ)]
  convert (((he.add_const (Real.cos (Real.pi * θ))).div_const
    (Real.sin (Real.pi * θ))).arctan.div_const (Real.pi * θ)) using 1
  · rfl
  · rw [hd, beta_eq_exp hθ]
    field_simp [hs, hq, hθ.1.ne', Real.pi_ne_zero]

theorem arctan_cos_div_sin {θ : ℝ} (hθ : θ ∈ Ioo (0 : ℝ) 1) :
    Real.arctan (Real.cos (Real.pi * θ) / Real.sin (Real.pi * θ)) =
      Real.pi / 2 - Real.pi * θ := by
  apply Real.arctan_eq_of_tan_eq
  · simp only [Real.tan_eq_sin_div_cos, Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub]
  · constructor <;> nlinarith [Real.pi_pos, hθ.1, hθ.2]

theorem tendsto_betaPrimitive_atBot {θ : ℝ} (hθ : θ ∈ Ioo (0 : ℝ) 1) :
    Tendsto (betaPrimitive θ) atBot
      (𝓝 ((Real.pi / 2 - Real.pi * θ) / (Real.pi * θ))) := by
  have he : Tendsto (fun t : ℝ => Real.exp (Real.pi * t)) atBot (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (Tendsto.const_mul_atBot Real.pi_pos tendsto_id)
  have hd := (he.add_const (Real.cos (Real.pi * θ))).div_const
    (Real.sin (Real.pi * θ))
  have ha := (Real.continuous_arctan.tendsto _).comp hd
  convert ha.div_const (Real.pi * θ) using 1
  · rfl
  · simp only [zero_add, arctan_cos_div_sin hθ]

theorem tendsto_betaPrimitive_atTop {θ : ℝ} (hθ : θ ∈ Ioo (0 : ℝ) 1) :
    Tendsto (betaPrimitive θ) atTop (𝓝 ((Real.pi / 2) / (Real.pi * θ))) := by
  have he : Tendsto (fun t : ℝ => Real.exp (Real.pi * t)) atTop atTop :=
    Real.tendsto_exp_atTop.comp (Tendsto.const_mul_atTop Real.pi_pos tendsto_id)
  have ha : Tendsto (fun t : ℝ => Real.exp (Real.pi * t) + Real.cos (Real.pi * θ))
      atTop atTop := he.atTop_add tendsto_const_nhds
  have hd := ha.atTop_div_const (sin_pi_mul_pos hθ)
  convert ((Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp hd).div_const
    (Real.pi * θ) using 1
  rfl

theorem integrableOn_beta_Ioi {θ : ℝ} (hθ : θ ∈ Ioo (0 : ℝ) 1) :
    IntegrableOn (beta θ) (Ioi (0 : ℝ)) volume := by
  exact integrableOn_Ioi_deriv_of_nonneg'
    (fun t _ => hasDerivAt_betaPrimitive hθ t)
    (fun t _ => beta_nonneg hθ t) (tendsto_betaPrimitive_atTop hθ)

theorem integrable_beta {θ : ℝ} (hθ : θ ∈ Ioo (0 : ℝ) 1) :
    Integrable (beta θ) volume := by
  have htop := integrableOn_beta_Ioi hθ
  have hset : (fun x : ℝ => -x) ⁻¹' Ioi (0 : ℝ) = Iio (0 : ℝ) := by
    ext x
    simp
  have hbotOpen : IntegrableOn (beta θ) (Iio (0 : ℝ)) volume := by
    have h := (MeasurePreserving.integrableOn_comp_preimage
      (Measure.measurePreserving_neg volume) (Homeomorph.neg ℝ).measurableEmbedding).2 htop
    simpa only [hset, Function.comp_def, beta_neg] using h
  have hbot : IntegrableOn (beta θ) (Iic (0 : ℝ)) volume :=
    (integrableOn_Iic_iff_integrableOn_Iio (f := beta θ) (b := (0 : ℝ))
      (μ := volume) (by finiteness)).mpr hbotOpen
  simpa only [Iic_union_Ioi, integrableOn_univ] using hbot.union htop

theorem integral_beta_eq_one {θ : ℝ} (hθ : θ ∈ Ioo (0 : ℝ) 1) :
    (∫ t : ℝ, beta θ t ∂volume) = 1 := by
  have h := integral_of_hasDerivAt_of_tendsto (hasDerivAt_betaPrimitive hθ)
    (integrable_beta hθ) (tendsto_betaPrimitive_atBot hθ) (tendsto_betaPrimitive_atTop hθ)
  convert h using 1
  field_simp [Real.pi_ne_zero, hθ.1.ne']
  ring

theorem beta_eq_sin_div (θ t : ℝ) :
    beta θ t = (Real.sin (Real.pi * θ) / θ) /
      (2 * (Real.cosh (Real.pi * t) + Real.cos (Real.pi * θ))) := by
  rw [div_div]
  unfold beta
  congr 1
  ring

theorem tendsto_beta_at_zero (t : ℝ) :
    Tendsto (fun θ : ℝ => beta θ t) (𝓝[≠] 0)
      (𝓝 (SBTProbabilityWeight.beta0 t)) := by
  have hs : HasDerivAt (fun θ : ℝ => Real.sin (Real.pi * θ)) Real.pi 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).const_mul Real.pi).sin
  have hsl : Tendsto (fun θ : ℝ => Real.sin (Real.pi * θ) / θ)
      (𝓝[≠] 0) (𝓝 Real.pi) := by
    simpa only [zero_add, mul_zero, Real.sin_zero, sub_zero,
      smul_eq_mul, div_eq_mul_inv, mul_comm] using hs.tendsto_slope_zero
  have hd : Tendsto (fun θ : ℝ => 2 *
      (Real.cosh (Real.pi * t) + Real.cos (Real.pi * θ)))
      (𝓝[≠] 0) (𝓝 (2 * (Real.cosh (Real.pi * t) + 1))) := by
    have hc : Continuous (fun θ : ℝ => 2 *
        (Real.cosh (Real.pi * t) + Real.cos (Real.pi * θ))) := by fun_prop
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  simp_rw [beta_eq_sin_div]
  convert hsl.div hd (by positivity) using 1
  first | rfl | simp only [SBTProbabilityWeight.beta0, add_comm]

theorem beta_le_two_mul_beta0 {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1 / 2) (t : ℝ) :
    beta θ t ≤ 2 * SBTProbabilityWeight.beta0 t := by
  have hθ : θ ∈ Ioo (0 : ℝ) 1 := ⟨hθ0, by linarith⟩
  have hc : 0 ≤ Real.cos (Real.pi * θ) := by
    apply Real.cos_nonneg_of_mem_Icc
    constructor <;> nlinarith [Real.pi_pos]
  have hs : Real.sin (Real.pi * θ) / θ ≤ Real.pi := by
    apply (div_le_iff₀ hθ0).mpr
    simpa only [mul_comm] using Real.sin_le (mul_nonneg Real.pi_pos.le hθ0.le)
  have hh := Real.one_le_cosh (Real.pi * t)
  rw [beta_eq_sin_div]
  calc
    _ ≤ Real.pi / (2 * (Real.cosh (Real.pi * t) + Real.cos (Real.pi * θ))) := by
      exact div_le_div_of_nonneg_right hs (by positivity)
    _ ≤ Real.pi / (1 + Real.cosh (Real.pi * t)) := by
      gcongr
      linarith
    _ = 2 * SBTProbabilityWeight.beta0 t := by
      unfold SBTProbabilityWeight.beta0
      field_simp

theorem tendsto_integral_beta_mul_at_zero (f : ℝ → ℝ)
    (hf : AEStronglyMeasurable f volume) {C : ℝ}
    (hbound : ∀ t : ℝ, ‖f t‖ ≤ C) :
    Tendsto (fun θ : ℝ => ∫ t : ℝ, beta θ t * f t ∂volume) (𝓝[>] 0)
      (𝓝 (∫ t : ℝ, SBTProbabilityWeight.beta0 t * f t ∂volume)) := by
  have hsmall : ∀ᶠ θ : ℝ in 𝓝[>] 0, θ ∈ Ioo (0 : ℝ) (1 / 2) :=
    Ioo_mem_nhdsGT (by norm_num)
  apply tendsto_integral_filter_of_dominated_convergence
    (fun t => 2 * SBTProbabilityWeight.beta0 t * C)
  · filter_upwards [hsmall] with θ hθ
    exact (continuous_beta ⟨hθ.1, by linarith [hθ.2]⟩).aestronglyMeasurable.mul hf
  · filter_upwards [hsmall] with θ hθ
    apply Eventually.of_forall
    intro t
    rw [norm_mul, Real.norm_eq_abs, abs_of_pos (beta_pos ⟨hθ.1, by linarith [hθ.2]⟩ t)]
    exact mul_le_mul (beta_le_two_mul_beta0 hθ.1 hθ.2.le t) (hbound t)
      (norm_nonneg _) (mul_nonneg (by norm_num) (SBTProbabilityWeight.beta0_nonneg t))
  · simpa only [mul_comm, mul_left_comm, mul_assoc] using
      SBTProbabilityWeight.integrable_beta0.mul_const (2 * C)
  · apply Eventually.of_forall
    intro t
    exact ((tendsto_beta_at_zero t).mono_left (nhdsGT_le_nhdsNE 0)).mul_const (f t)

theorem norm_log_le_of_bounds {m M x : ℝ} (hm : 0 < m) (hx0 : m ≤ x) (hx1 : x ≤ M) :
    ‖Real.log x‖ ≤ max |Real.log m| |Real.log M| := by
  rw [Real.norm_eq_abs]
  apply abs_le.mpr
  constructor
  · exact ((neg_le_neg (le_max_left _ _)).trans (neg_abs_le _)).trans
      (Real.log_le_log hm hx0)
  · exact (Real.log_le_log (hm.trans_le hx0) hx1).trans
      ((le_abs_self _).trans (le_max_right _ _))

theorem integrable_beta_mul_log_majorant {θ : ℝ} (hθ : θ ∈ Ioo (0 : ℝ) 1)
    (M : ℝ → ℝ) (hM : Continuous M) {m B : ℝ} (hm : 0 < m)
    (hlo : ∀ t, m ≤ M t) (hhi : ∀ t, M t ≤ B) :
    Integrable (fun t => beta θ t * Real.log (M t)) volume := by
  have hc : Continuous (fun t => Real.log (M t)) := hM.log
    (fun t => (hm.trans_le (hlo t)).ne')
  exact (integrable_beta hθ).mul_bdd hc.aestronglyMeasurable
    (Eventually.of_forall (fun t => norm_log_le_of_bounds hm (hlo t) (hhi t)))

theorem tendsto_integral_beta_mul_log_majorant (M : ℝ → ℝ) (hM : Continuous M)
    {m B : ℝ} (hm : 0 < m) (hlo : ∀ t, m ≤ M t) (hhi : ∀ t, M t ≤ B) :
    Tendsto (fun θ : ℝ => ∫ t : ℝ, beta θ t * Real.log (M t) ∂volume) (𝓝[>] 0)
      (𝓝 (∫ t : ℝ, SBTProbabilityWeight.beta0 t * Real.log (M t) ∂volume)) := by
  have hc : Continuous (fun t => Real.log (M t)) := hM.log
    (fun t => (hm.trans_le (hlo t)).ne')
  exact tendsto_integral_beta_mul_at_zero _ hc.aestronglyMeasurable
    (fun t => norm_log_le_of_bounds hm (hlo t) (hhi t))

theorem log_norm_le_circleAverage {f : ℂ → ℂ} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall c R)) (hc : f c ≠ 0) :
    Real.log ‖f c‖ ≤ Real.circleAverage (fun z => Real.log ‖f z‖) c R := by
  have hf' : AnalyticOnNhd ℂ f (Metric.closedBall c |R|) := by
    simpa only [abs_of_pos hR] using hf
  rw [hf'.circleAverage_log_norm hR.ne' hc]
  apply le_add_of_nonneg_left
  apply finsum_nonneg
  intro z
  by_cases hz : z ∈ Metric.closedBall c |R|
  · by_cases hzc : z = c
    · subst z
      simp
    · apply mul_nonneg
      · exact_mod_cast MeromorphicOn.AnalyticOnNhd.divisor_nonneg hf' z
      · apply Real.log_nonneg
        rw [← div_eq_mul_inv]
        have hd : 0 < ‖c - z‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hzc))
        apply (one_le_div hd).mpr
        simpa only [Metric.mem_closedBall, dist_eq_norm', abs_of_pos hR] using hz
  · simp only [Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hz,
      Int.cast_zero, zero_mul, le_refl]

theorem log_norm_le_circleAverage_log_max_one {f : ℂ → ℂ} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall c R)) (hc : f c ≠ 0) :
    Real.log ‖f c‖ ≤ Real.circleAverage (fun z => Real.log (max 1 ‖f z‖)) c R := by
  have hf' : AnalyticOnNhd ℂ f (Metric.closedBall c |R|) := by
    simpa only [abs_of_pos hR] using hf
  have hg : ContinuousOn (fun z => Real.log (max 1 ‖f z‖)) (Metric.closedBall c |R|) :=
    (continuousOn_const.sup hf'.continuousOn.norm).log
      (fun _ _ => (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_left _ _)).ne')
  apply (log_norm_le_circleAverage hR hf hc).trans
  apply Real.circleAverage_mono
    ((hf'.mono Metric.sphere_subset_closedBall).meromorphicOn.circleIntegrable_log_norm)
    ((hg.mono Metric.sphere_subset_closedBall).circleIntegrable')
  intro z _
  by_cases hz : f z = 0
  · simp [hz]
  · exact Real.log_le_log (norm_pos_iff.mpr hz) (le_max_right _ _)

def leftKernel (θ t : ℝ) : ℝ := (1 - θ) * beta (1 - θ) t

def rightKernel (θ t : ℝ) : ℝ := θ * beta θ t

theorem one_sub_mem_Ioo {θ : ℝ} (hθ : θ ∈ Ioo (0 : ℝ) 1) :
    1 - θ ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hθ.2], by linarith [hθ.1]⟩

theorem rightKernel_eq {θ : ℝ} (hθ : θ ∈ Ioo (0 : ℝ) 1) (t : ℝ) :
    rightKernel θ t = Real.sin (Real.pi * θ) /
      (2 * (Real.cosh (Real.pi * t) + Real.cos (Real.pi * θ))) := by
  unfold rightKernel beta
  field_simp [hθ.1.ne', (beta_denominator_pos hθ t).ne']

theorem leftKernel_eq {θ : ℝ} (hθ : θ ∈ Ioo (0 : ℝ) 1) (t : ℝ) :
    leftKernel θ t = Real.sin (Real.pi * θ) /
      (2 * (Real.cosh (Real.pi * t) - Real.cos (Real.pi * θ))) := by
  have hθ' := one_sub_mem_Ioo hθ
  have ha : Real.pi * (1 - θ) = Real.pi - Real.pi * θ := by ring
  change rightKernel (1 - θ) t = _
  rw [rightKernel_eq hθ' t, ha, Real.sin_pi_sub, Real.cos_pi_sub]
  rfl

theorem integrable_leftKernel {θ : ℝ} (hθ : θ ∈ Ioo (0 : ℝ) 1) :
    Integrable (leftKernel θ) volume := (integrable_beta (one_sub_mem_Ioo hθ)).const_mul _

theorem integrable_rightKernel {θ : ℝ} (hθ : θ ∈ Ioo (0 : ℝ) 1) :
    Integrable (rightKernel θ) volume := (integrable_beta hθ).const_mul _

theorem integral_leftKernel {θ : ℝ} (hθ : θ ∈ Ioo (0 : ℝ) 1) :
    (∫ t : ℝ, leftKernel θ t ∂volume) = 1 - θ := by
  simp only [leftKernel, integral_const_mul, integral_beta_eq_one (one_sub_mem_Ioo hθ), mul_one]

theorem integral_rightKernel {θ : ℝ} (hθ : θ ∈ Ioo (0 : ℝ) 1) :
    (∫ t : ℝ, rightKernel θ t ∂volume) = θ := by
  simp only [rightKernel, integral_const_mul, integral_beta_eq_one hθ, mul_one]

theorem integral_leftKernel_add_rightKernel {θ : ℝ} (hθ : θ ∈ Ioo (0 : ℝ) 1) :
    (∫ t : ℝ, leftKernel θ t + rightKernel θ t ∂volume) = 1 := by
  rw [integral_add (integrable_leftKernel hθ) (integrable_rightKernel hθ),
    integral_leftKernel hθ, integral_rightKernel hθ]
  ring

def upperHalfPlaneMap (θ : ℝ) (w : ℂ) : ℂ :=
  (Real.cos (Real.pi * θ) : ℂ) +
    Complex.I * (Real.sin (Real.pi * θ) : ℂ) * ((1 + w) / (1 - w))

def stripDiskMap (θ : ℝ) (w : ℂ) : ℂ :=
  (-Complex.I) * Complex.log (upperHalfPlaneMap θ w) / (Real.pi : ℂ)

theorem one_sub_ne_zero_of_norm_lt_one {w : ℂ} (hw : ‖w‖ < 1) : 1 - w ≠ 0 := by
  intro h
  have hw1 : w = 1 := (sub_eq_zero.mp h).symm
  rw [hw1, norm_one] at hw
  exact (lt_irrefl (1 : ℝ)) hw

theorem upperHalfPlaneMap_im (θ : ℝ) (w : ℂ) :
    (upperHalfPlaneMap θ w).im = Real.sin (Real.pi * θ) *
      (1 - ‖w‖ ^ 2) / ‖1 - w‖ ^ 2 := by
  simp only [upperHalfPlaneMap, Complex.add_im, Complex.ofReal_im,
    Complex.mul_im, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
    zero_mul, mul_zero, one_mul, zero_add, sub_zero, zero_sub,
    Complex.div_re, Complex.add_re, Complex.sub_re, Complex.sub_im,
    Complex.one_re, Complex.one_im]
  simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
    Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im]
  ring

theorem upperHalfPlaneMap_im_pos {θ : ℝ} (hθ : θ ∈ Ioo (0 : ℝ) 1)
    {w : ℂ} (hw : ‖w‖ < 1) : 0 < (upperHalfPlaneMap θ w).im := by
  rw [upperHalfPlaneMap_im]
  apply div_pos
  · apply mul_pos (sin_pi_mul_pos hθ)
    nlinarith [norm_nonneg w]
  · exact sq_pos_of_pos (norm_pos_iff.mpr (one_sub_ne_zero_of_norm_lt_one hw))

theorem stripDiskMap_re (θ : ℝ) (w : ℂ) :
    (stripDiskMap θ w).re = (upperHalfPlaneMap θ w).arg / Real.pi := by
  simp only [stripDiskMap, Complex.div_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im,
    Complex.log_im, Complex.normSq_ofReal, zero_mul, mul_zero,
    zero_sub, neg_neg, neg_mul, one_mul]
  field_simp [Real.pi_ne_zero]
  simp only [add_zero]

theorem stripDiskMap_mem_verticalStrip {θ : ℝ} (hθ : θ ∈ Ioo (0 : ℝ) 1)
    {w : ℂ} (hw : ‖w‖ < 1) :
    stripDiskMap θ w ∈ Complex.HadamardThreeLines.verticalStrip 0 1 := by
  have hi := upperHalfPlaneMap_im_pos hθ hw
  have ha0 : 0 < (upperHalfPlaneMap θ w).arg := by
    apply lt_of_le_of_ne (Complex.arg_nonneg_iff.mpr hi.le)
    intro ha
    exact hi.ne' (Complex.arg_eq_zero_iff.mp ha.symm).2
  have ha1 : (upperHalfPlaneMap θ w).arg < Real.pi :=
    Complex.arg_lt_pi_iff.mpr (Or.inr hi.ne')
  change 0 < (stripDiskMap θ w).re ∧ (stripDiskMap θ w).re < 1
  rw [stripDiskMap_re]
  exact ⟨div_pos ha0 Real.pi_pos, (div_lt_one Real.pi_pos).mpr ha1⟩

theorem differentiableOn_stripDiskMap {θ : ℝ} (hθ : θ ∈ Ioo (0 : ℝ) 1) :
    DifferentiableOn ℂ (stripDiskMap θ) (Metric.ball (0 : ℂ) 1) := by
  intro w hw
  have hw' : ‖w‖ < 1 := by simpa only [Metric.mem_ball, dist_zero_right] using hw
  have hne := one_sub_ne_zero_of_norm_lt_one hw'
  have hU : DifferentiableAt ℂ (upperHalfPlaneMap θ) w := by
    unfold upperHalfPlaneMap
    fun_prop (disch := exact hne)
  have hslit : upperHalfPlaneMap θ w ∈ Complex.slitPlane :=
    Complex.mem_slitPlane_iff.mpr (Or.inr (upperHalfPlaneMap_im_pos hθ hw').ne')
  exact (((Complex.differentiableAt_log hslit).comp w hU).const_mul (-Complex.I)).div_const
    (Real.pi : ℂ) |>.differentiableWithinAt

theorem stripDiskMap_zero {θ : ℝ} (hθ : θ ∈ Ioo (0 : ℝ) 1) :
    stripDiskMap θ 0 = (θ : ℂ) := by
  have hU : upperHalfPlaneMap θ 0 = Complex.exp ((Real.pi * θ : ℝ) * Complex.I) := by
    rw [Complex.exp_mul_I]
    simp only [upperHalfPlaneMap, add_zero, sub_zero, div_one, mul_one,
      Complex.ofReal_cos, Complex.ofReal_sin]
    ring
  have hlog : Complex.log (upperHalfPlaneMap θ 0) = (Real.pi * θ : ℝ) * Complex.I := by
    rw [hU]
    apply Complex.log_exp
    · simp only [Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re,
        Complex.I_re, Complex.I_im, mul_zero, mul_one]
      nlinarith [Real.pi_pos, hθ.1]
    · simp only [Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re,
        Complex.I_re, Complex.I_im, mul_zero, mul_one]
      nlinarith [Real.pi_pos, hθ.2]
  rw [stripDiskMap, hlog]
  have hm : (-Complex.I) * ((Real.pi * θ : ℝ) * Complex.I) = (Real.pi * θ : ℝ) := by
    ring_nf
    rw [Complex.I_sq]
    ring
  rw [hm]
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr Real.pi_ne_zero]

theorem stripDiskMap_im (θ : ℝ) (w : ℂ) :
    (stripDiskMap θ w).im = -Real.log ‖upperHalfPlaneMap θ w‖ / Real.pi := by
  simp only [stripDiskMap, Complex.div_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
    Complex.I_re, Complex.I_im, Complex.log_re, Complex.normSq_ofReal,
    zero_mul, mul_zero, zero_add, zero_sub, neg_mul, one_mul]
  field_simp [Real.pi_ne_zero]
  ring

theorem upperHalfPlaneMap_injOn {θ : ℝ} (hθ : θ ∈ Ioo (0 : ℝ) 1) :
    InjOn (upperHalfPlaneMap θ) {1}ᶜ := by
  intro w hw v hv h
  have hw' : 1 - w ≠ 0 := sub_ne_zero.mpr (by simpa using Ne.symm hw)
  have hv' : 1 - v ≠ 0 := sub_ne_zero.mpr (by simpa using Ne.symm hv)
  have ha : Complex.I * (Real.sin (Real.pi * θ) : ℂ) ≠ 0 :=
    mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr (sin_pi_mul_pos hθ).ne')
  unfold upperHalfPlaneMap at h
  have hd := (div_eq_div_iff hw' hv').mp (mul_left_cancel₀ ha (add_left_cancel h))
  have h2 : (2 : ℂ) * w = 2 * v := by linear_combination hd
  exact mul_left_cancel₀ (by norm_num : (2 : ℂ) ≠ 0) h2

theorem upperHalfPlaneMap_boundary_im (θ : ℝ) {w : ℂ} (hw : ‖w‖ = 1) :
    (upperHalfPlaneMap θ w).im = 0 := by
  rw [upperHalfPlaneMap_im, hw]
  simp

theorem stripDiskMap_boundary_re (θ : ℝ) {w : ℂ} (hw : ‖w‖ = 1)
    (hne : upperHalfPlaneMap θ w ≠ 0) :
    (stripDiskMap θ w).re = 0 ∨ (stripDiskMap θ w).re = 1 := by
  have hi := upperHalfPlaneMap_boundary_im θ hw
  have hr : (upperHalfPlaneMap θ w).re ≠ 0 := by
    intro h
    exact hne (Complex.ext (by simpa using h) (by simpa using hi))
  rcases lt_or_gt_of_ne hr with hr | hr
  · right
    rw [stripDiskMap_re, Complex.arg_eq_pi_iff.mpr ⟨hr, hi⟩, div_self Real.pi_ne_zero]
  · left
    rw [stripDiskMap_re, Complex.arg_eq_zero_iff.mpr ⟨hr.le, hi⟩, zero_div]

theorem stripDiskMap_boundary_mem_verticalClosedStrip (θ : ℝ) {w : ℂ}
    (hw : ‖w‖ = 1) (hne : upperHalfPlaneMap θ w ≠ 0) :
    stripDiskMap θ w ∈ Complex.HadamardThreeLines.verticalClosedStrip 0 1 := by
  change 0 ≤ (stripDiskMap θ w).re ∧ (stripDiskMap θ w).re ≤ 1
  rcases stripDiskMap_boundary_re θ hw hne with h | h <;> simp [h]

theorem tendsto_stripDiskMap_radial {θ : ℝ} (hθ : θ ∈ Ioo (0 : ℝ) 1)
    {w : ℂ} (hw : ‖w‖ = 1) (hw1 : w ≠ 1) (hU0 : upperHalfPlaneMap θ w ≠ 0) :
    Tendsto (fun r : ℝ => stripDiskMap θ ((r : ℂ) * w)) (𝓝[<] 1)
      (𝓝 (stripDiskMap θ w)) := by
  have hd : 1 - w ≠ 0 := sub_ne_zero.mpr hw1.symm
  have hU : ContinuousAt (upperHalfPlaneMap θ) w := by
    unfold upperHalfPlaneMap
    fun_prop (disch := exact hd)
  have hr : Tendsto (fun r : ℝ => (r : ℂ) * w) (𝓝[<] 1) (𝓝 w) := by
    simpa using (Complex.continuous_ofReal.mul_const w).tendsto 1 |>.mono_left nhdsWithin_le_nhds
  have hUt : Tendsto (fun r : ℝ => upperHalfPlaneMap θ ((r : ℂ) * w))
      (𝓝[<] 1) (𝓝 (upperHalfPlaneMap θ w)) := hU.tendsto.comp hr
  have hi := upperHalfPlaneMap_boundary_im θ hw
  have hre : (upperHalfPlaneMap θ w).re ≠ 0 := by
    intro h
    exact hU0 (Complex.ext (by simpa using h) (by simpa using hi))
  have hL : Tendsto (fun r : ℝ => Complex.log (upperHalfPlaneMap θ ((r : ℂ) * w)))
      (𝓝[<] 1) (𝓝 (Complex.log (upperHalfPlaneMap θ w))) := by
    rcases lt_or_gt_of_ne hre with hre | hre
    · apply (Complex.continuousWithinAt_log_of_re_neg_of_im_zero hre hi).tendsto.comp
      apply tendsto_nhdsWithin_iff.mpr
      refine ⟨hUt, ?_⟩
      filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)] with r hr
      apply (upperHalfPlaneMap_im_pos hθ _).le
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, hw, mul_one, abs_of_pos hr.1]
      exact hr.2
    · exact (Complex.differentiableAt_log
        (Complex.mem_slitPlane_iff.mpr (Or.inl hre))).continuousAt.tendsto.comp hUt
  simpa only [stripDiskMap] using (hL.const_mul (-Complex.I)).div_const (Real.pi : ℂ)

theorem countable_upperHalfPlaneMap_zero {θ : ℝ} (hθ : θ ∈ Ioo (0 : ℝ) 1) :
    {w : ℂ | upperHalfPlaneMap θ w = 0}.Countable := by
  have hs : {w : ℂ | upperHalfPlaneMap θ w = 0 ∧ w ≠ 1}.Subsingleton := by
    intro w hw v hv
    apply upperHalfPlaneMap_injOn hθ
    · simpa using hw.2
    · simpa using hv.2
    · exact hw.1.trans hv.1.symm
  apply (hs.countable.insert 1).mono
  intro w hw
  by_cases hw1 : w = 1
  · simp only [hw1, mem_insert_iff, true_or]
  · exact mem_insert_of_mem 1 ⟨hw, hw1⟩

theorem ae_good_circle_boundary {θ : ℝ} (hθ : θ ∈ Ioo (0 : ℝ) 1)
    (μ : Measure ℝ) [NullSingletonClass μ] :
    ∀ᵐ t : ℝ ∂μ, circleMap 0 1 t ≠ 1 ∧ upperHalfPlaneMap θ (circleMap 0 1 t) ≠ 0 := by
  let bad : Set ℂ := {1} ∪ {w | upperHalfPlaneMap θ w = 0}
  have hc : bad.Countable := (countable_singleton 1).union (countable_upperHalfPlaneMap_zero hθ)
  have hz : μ (circleMap 0 1 ⁻¹' bad) = 0 :=
    (hc.preimage_circleMap 0 (by norm_num)).measure_zero μ
  have he : ∀ᵐ t : ℝ ∂μ, t ∉ circleMap 0 1 ⁻¹' bad := compl_mem_ae_iff.mpr hz
  filter_upwards [he] with t ht
  simpa only [bad, mem_preimage, mem_union, mem_singleton_iff, mem_ofPred_eq, not_or] using ht

theorem ae_tendsto_stripDiskMap_circle {θ : ℝ} (hθ : θ ∈ Ioo (0 : ℝ) 1)
    (μ : Measure ℝ) [NullSingletonClass μ] :
    ∀ᵐ t : ℝ ∂μ, Tendsto (fun r : ℝ => stripDiskMap θ (circleMap 0 r t))
      (𝓝[<] 1) (𝓝 (stripDiskMap θ (circleMap 0 1 t))) := by
  filter_upwards [ae_good_circle_boundary hθ μ] with t ht
  simpa only [circleMap_zero, Complex.ofReal_one, one_mul] using
    tendsto_stripDiskMap_radial hθ (by simp) ht.1 ht.2

theorem ae_stripDiskMap_circle_mem_verticalClosedStrip {θ : ℝ}
    (hθ : θ ∈ Ioo (0 : ℝ) 1) (μ : Measure ℝ) [NullSingletonClass μ] :
    ∀ᵐ t : ℝ ∂μ, stripDiskMap θ (circleMap 0 1 t) ∈
      Complex.HadamardThreeLines.verticalClosedStrip 0 1 := by
  filter_upwards [ae_good_circle_boundary hθ μ] with t ht
  exact stripDiskMap_boundary_mem_verticalClosedStrip θ (by simp) ht.2

theorem continuousOn_closedStrip {g : ℂ → ℂ}
    (hg : DiffContOnCl ℂ g (Complex.HadamardThreeLines.verticalStrip 0 1)) :
    ContinuousOn g (Complex.HadamardThreeLines.verticalClosedStrip 0 1) := by
  simpa only [Complex.HadamardThreeLines.verticalStrip,
    Complex.HadamardThreeLines.verticalClosedStrip, Complex.closure_preimage_re,
    closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)] using hg.continuousOn

theorem differentiableOn_stripDiskMap_comp {θ : ℝ} (hθ : θ ∈ Ioo (0 : ℝ) 1)
    {g : ℂ → ℂ}
    (hg : DiffContOnCl ℂ g (Complex.HadamardThreeLines.verticalStrip 0 1)) :
    DifferentiableOn ℂ (fun w => g (stripDiskMap θ w)) (Metric.ball (0 : ℂ) 1) := by
  apply hg.differentiableOn.comp (differentiableOn_stripDiskMap hθ)
  intro w hw
  exact stripDiskMap_mem_verticalStrip hθ
    (by simpa only [Metric.mem_ball, dist_zero_right] using hw)

theorem analyticOnNhd_stripDiskMap_comp_closedBall {θ R : ℝ}
    (hθ : θ ∈ Ioo (0 : ℝ) 1) (hR : R < 1) {g : ℂ → ℂ}
    (hg : DiffContOnCl ℂ g (Complex.HadamardThreeLines.verticalStrip 0 1)) :
    AnalyticOnNhd ℂ (fun w => g (stripDiskMap θ w)) (Metric.closedBall (0 : ℂ) R) := by
  apply ((differentiableOn_stripDiskMap_comp hθ hg).analyticOnNhd Metric.isOpen_ball).mono
  intro w hw
  simp only [Metric.mem_closedBall, dist_zero_right] at hw
  exact Metric.mem_ball.mpr (by simpa only [dist_zero_right] using hw.trans_lt hR)

theorem tendsto_stripDiskMap_comp_radial {θ : ℝ} (hθ : θ ∈ Ioo (0 : ℝ) 1)
    {g : ℂ → ℂ}
    (hg : DiffContOnCl ℂ g (Complex.HadamardThreeLines.verticalStrip 0 1))
    {w : ℂ} (hw : ‖w‖ = 1) (hw1 : w ≠ 1) (hU0 : upperHalfPlaneMap θ w ≠ 0) :
    Tendsto (fun r : ℝ => g (stripDiskMap θ ((r : ℂ) * w))) (𝓝[<] 1)
      (𝓝 (g (stripDiskMap θ w))) := by
  apply ((continuousOn_closedStrip hg) _
    (stripDiskMap_boundary_mem_verticalClosedStrip θ hw hU0)).tendsto.comp
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨tendsto_stripDiskMap_radial hθ hw hw1 hU0, ?_⟩
  filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)] with r hr
  have hn : ‖(r : ℂ) * w‖ < 1 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, hw, mul_one, abs_of_pos hr.1]
    exact hr.2
  have hm := stripDiskMap_mem_verticalStrip hθ hn
  exact ⟨hm.1.le, hm.2.le⟩

theorem ae_tendsto_stripDiskMap_comp_circle {θ : ℝ} (hθ : θ ∈ Ioo (0 : ℝ) 1)
    {g : ℂ → ℂ}
    (hg : DiffContOnCl ℂ g (Complex.HadamardThreeLines.verticalStrip 0 1))
    (μ : Measure ℝ) [NullSingletonClass μ] :
    ∀ᵐ t : ℝ ∂μ, Tendsto (fun r : ℝ => g (stripDiskMap θ (circleMap 0 r t)))
      (𝓝[<] 1) (𝓝 (g (stripDiskMap θ (circleMap 0 1 t)))) := by
  filter_upwards [ae_good_circle_boundary hθ μ] with t ht
  simpa only [circleMap_zero, Complex.ofReal_one, one_mul] using
    tendsto_stripDiskMap_comp_radial hθ hg (by simp) ht.1 ht.2

theorem log_norm_le_boundary_circleAverage_clipped {θ : ℝ}
    (hθ : θ ∈ Ioo (0 : ℝ) 1) {g : ℂ → ℂ}
    (hg : DiffContOnCl ℂ g (Complex.HadamardThreeLines.verticalStrip 0 1))
    (hB : BddAbove ((norm ∘ g) '' Complex.HadamardThreeLines.verticalClosedStrip 0 1))
    (hne : g (θ : ℂ) ≠ 0) :
    Real.log ‖g (θ : ℂ)‖ ≤ Real.circleAverage
      (fun w => Real.log (max 1 ‖g (stripDiskMap θ w)‖)) 0 1 := by
  obtain ⟨B, hbound⟩ := hB
  have hbound' : ∀ w : ℂ, ‖w‖ < 1 → ‖g (stripDiskMap θ w)‖ ≤ B := by
    intro w hw
    have hm := stripDiskMap_mem_verticalStrip hθ hw
    exact hbound ⟨stripDiskMap θ w, ⟨hm.1.le, hm.2.le⟩, rfl⟩
  have ht := HirschmanRadialLimit.tendsto_circleAverage_clippedLog
    (k := fun w => g (stripDiskMap θ w))
    (differentiableOn_stripDiskMap_comp hθ hg).continuousOn hbound'
    (ae_tendsto_stripDiskMap_comp_circle hθ hg
      (volume.restrict (Icc (0 : ℝ) (2 * Real.pi))))
  apply ge_of_tendsto ht
  filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)] with r hr
  have hJ := log_norm_le_circleAverage_log_max_one hr.1
    (analyticOnNhd_stripDiskMap_comp_closedBall hθ hr.2 hg)
    (by simpa only [stripDiskMap_zero hθ] using hne)
  simpa only [stripDiskMap_zero hθ] using hJ

theorem stripDiskMap_circle_eq_stripBoundaryValue (θ u : ℝ) :
    stripDiskMap θ (circleMap 0 1 u) = HirschmanBoundaryChange.stripBoundaryValue θ u := by
  simp only [stripDiskMap, upperHalfPlaneMap, circleMap_zero,
    Complex.ofReal_one, one_mul, HirschmanBoundaryChange.stripBoundaryValue,
    HirschmanBoundaryChange.upperBoundaryValue]

theorem stripDiskMap_leftAngle {θ : ℝ} (hθ : θ ∈ Ioo (0 : ℝ) 1) (t : ℝ) :
    stripDiskMap θ (circleMap 0 1 (HirschmanBoundaryChange.leftAngle θ t)) =
      Complex.I * (t : ℂ) := by
  rw [stripDiskMap_circle_eq_stripBoundaryValue,
    HirschmanBoundaryChange.stripBoundaryValue_leftAngle hθ t]

theorem stripDiskMap_rightAngle {θ : ℝ} (hθ : θ ∈ Ioo (0 : ℝ) 1) (t : ℝ) :
    stripDiskMap θ (circleMap 0 1 (HirschmanBoundaryChange.rightAngle θ t)) =
      1 + Complex.I * (t : ℂ) := by
  rw [stripDiskMap_circle_eq_stripBoundaryValue,
    HirschmanBoundaryChange.stripBoundaryValue_rightAngle hθ t]

theorem leftKernel_eq_rawLeftKernel {θ : ℝ} (hθ : θ ∈ Ioo (0 : ℝ) 1) (t : ℝ) :
    leftKernel θ t = HirschmanBoundaryChange.rawLeftKernel θ t := leftKernel_eq hθ t

theorem rightKernel_eq_rawRightKernel {θ : ℝ} (hθ : θ ∈ Ioo (0 : ℝ) 1) (t : ℝ) :
    rightKernel θ t = HirschmanBoundaryChange.rawRightKernel θ t := rightKernel_eq hθ t

theorem circleAverage_stripDiskMap_eq {θ : ℝ} (hθ : θ ∈ Ioo (0 : ℝ) 1)
    (h : ℂ → ℝ)
    (hI : IntegrableOn (fun u => h (stripDiskMap θ (circleMap 0 1 u)))
      (Icc (0 : ℝ) (2 * Real.pi))) :
    Real.circleAverage (fun w => h (stripDiskMap θ w)) 0 1 =
      (∫ t : ℝ, leftKernel θ t * h (Complex.I * (t : ℂ))) +
      (∫ t : ℝ, rightKernel θ t * h (1 + Complex.I * (t : ℂ))) := by
  let F : ℝ → ℝ := fun u => h (stripDiskMap θ (circleMap 0 1 u))
  have ha0 : 0 ≤ 2 * Real.pi * θ := mul_nonneg (by positivity) hθ.1.le
  have ha1 : 2 * Real.pi * θ ≤ 2 * Real.pi := by nlinarith [Real.pi_pos, hθ.2]
  have hr : IntervalIntegrable F volume 0 (2 * Real.pi * θ) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le ha0).mpr
      (hI.mono_set (fun _ hu => ⟨hu.1, hu.2.trans ha1⟩))
  have hl : IntervalIntegrable F volume (2 * Real.pi * θ) (2 * Real.pi) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le ha1).mpr
      (hI.mono_set (fun _ hu => ⟨ha0.trans hu.1, hu.2⟩))
  have hright : (∫ u in (0 : ℝ)..(2 * Real.pi * θ), F u) =
      (2 * Real.pi) * ∫ t : ℝ, rightKernel θ t * h (1 + Complex.I * (t : ℂ)) := by
    rw [intervalIntegral.integral_of_le ha0, integral_Ioc_eq_integral_Ioo,
      HirschmanBoundaryChange.integral_rightAngle_substitution hθ F]
    simp only [F, stripDiskMap_rightAngle hθ, ← rightKernel_eq_rawRightKernel hθ,
      mul_assoc, integral_const_mul]
  have hleft : (∫ u in (2 * Real.pi * θ)..(2 * Real.pi), F u) =
      (2 * Real.pi) * ∫ t : ℝ, leftKernel θ t * h (Complex.I * (t : ℂ)) := by
    rw [intervalIntegral.integral_of_le ha1, integral_Ioc_eq_integral_Ioo,
      HirschmanBoundaryChange.integral_leftAngle_substitution hθ F]
    simp only [F, stripDiskMap_leftAngle hθ, ← leftKernel_eq_rawLeftKernel hθ,
      mul_assoc, integral_const_mul]
  rw [Real.circleAverage_def, smul_eq_mul,
    ← intervalIntegral.integral_add_adjacent_intervals hr hl, hright, hleft]
  field_simp [Real.pi_ne_zero]
  ring

theorem integrable_boundary_circle_clipped {θ : ℝ} (hθ : θ ∈ Ioo (0 : ℝ) 1)
    {g : ℂ → ℂ}
    (hg : DiffContOnCl ℂ g (Complex.HadamardThreeLines.verticalStrip 0 1))
    (hB : BddAbove ((norm ∘ g) '' Complex.HadamardThreeLines.verticalClosedStrip 0 1)) :
    IntegrableOn (fun u => Real.log (max 1 ‖g (stripDiskMap θ (circleMap 0 1 u))‖))
      (Icc (0 : ℝ) (2 * Real.pi)) := by
  obtain ⟨B, hbound⟩ := hB
  have hbound' : ∀ w : ℂ, ‖w‖ < 1 → ‖g (stripDiskMap θ w)‖ ≤ B := by
    intro w hw
    have hm := stripDiskMap_mem_verticalStrip hθ hw
    exact hbound ⟨stripDiskMap θ w, ⟨hm.1.le, hm.2.le⟩, rfl⟩
  simpa only [HirschmanRadialLimit.clippedLog] using
    HirschmanRadialLimit.boundary_clippedLog_integrable
      (k := fun w => g (stripDiskMap θ w))
      (differentiableOn_stripDiskMap_comp hθ hg).continuousOn hbound'
      (ae_tendsto_stripDiskMap_comp_circle hθ hg
        (volume.restrict (Icc (0 : ℝ) (2 * Real.pi))))

theorem integrable_boundary_kernels_of_circle {θ : ℝ} (hθ : θ ∈ Ioo (0 : ℝ) 1)
    (h : ℂ → ℝ)
    (hI : IntegrableOn (fun u => h (stripDiskMap θ (circleMap 0 1 u)))
      (Icc (0 : ℝ) (2 * Real.pi))) :
    Integrable (fun t : ℝ => leftKernel θ t * h (Complex.I * (t : ℂ))) ∧
      Integrable (fun t : ℝ => rightKernel θ t * h (1 + Complex.I * (t : ℂ))) := by
  have ha0 : 0 ≤ 2 * Real.pi * θ := mul_nonneg (by positivity) hθ.1.le
  have ha1 : 2 * Real.pi * θ ≤ 2 * Real.pi := by nlinarith [Real.pi_pos, hθ.2]
  have hC : (2 * Real.pi) ≠ 0 := mul_ne_zero (by norm_num) Real.pi_ne_zero
  constructor
  · have hi := (HirschmanBoundaryChange.integrable_leftAngle_substitution hθ
        (fun u => h (stripDiskMap θ (circleMap 0 1 u)))).mp
      (hI.mono_set (fun _ hu => ⟨ha0.trans hu.1.le, hu.2.le⟩))
    simp only [stripDiskMap_leftAngle hθ, ← leftKernel_eq_rawLeftKernel hθ,
      mul_assoc] at hi
    simpa only [← mul_assoc, inv_mul_cancel₀ hC, one_mul] using hi.const_mul ((2 * Real.pi)⁻¹)
  · have hi := (HirschmanBoundaryChange.integrable_rightAngle_substitution hθ
        (fun u => h (stripDiskMap θ (circleMap 0 1 u)))).mp
      (hI.mono_set (fun _ hu => ⟨hu.1.le, hu.2.le.trans ha1⟩))
    simp only [stripDiskMap_rightAngle hθ, ← rightKernel_eq_rawRightKernel hθ,
      mul_assoc] at hi
    simpa only [← mul_assoc, inv_mul_cancel₀ hC, one_mul] using hi.const_mul ((2 * Real.pi)⁻¹)

theorem clipped_log_div_le_log_majorant {z : ℂ} {δ M : ℝ}
    (hδ : 0 < δ) (hδM : δ ≤ M) (hz : ‖z‖ ≤ M) :
    Real.log (max 1 ‖z / (δ : ℂ)‖) ≤ Real.log M - Real.log δ := by
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδ]
  calc
    Real.log (max 1 (‖z‖ / δ)) ≤ Real.log (M / δ) := by
      apply Real.log_le_log (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
      exact max_le ((one_le_div hδ).mpr hδM) (div_le_div_of_nonneg_right hz hδ.le)
    _ = Real.log M - Real.log δ := Real.log_div (hδ.trans_le hδM).ne' hδ.ne'

theorem hirschman_strip_majorant {θ : ℝ} (hθ : θ ∈ Ioo (0 : ℝ) 1)
    {g : ℂ → ℂ}
    (hg : DiffContOnCl ℂ g (Complex.HadamardThreeLines.verticalStrip 0 1))
    (hB : BddAbove ((norm ∘ g) '' Complex.HadamardThreeLines.verticalClosedStrip 0 1))
    (hne : g (θ : ℂ) ≠ 0) (M0 M1 : ℝ → ℝ) (hM0 : Continuous M0) (hM1 : Continuous M1)
    {m0 m1 B0 B1 : ℝ} (hm0 : 0 < m0) (hm1 : 0 < m1)
    (hlo0 : ∀ t, m0 ≤ M0 t) (hhi0 : ∀ t, M0 t ≤ B0)
    (hlo1 : ∀ t, m1 ≤ M1 t) (hhi1 : ∀ t, M1 t ≤ B1)
    (hboundary0 : ∀ t : ℝ, ‖g (Complex.I * (t : ℂ))‖ ≤ M0 t)
    (hboundary1 : ∀ t : ℝ, ‖g (1 + Complex.I * (t : ℂ))‖ ≤ M1 t) :
    Real.log ‖g (θ : ℂ)‖ ≤
      (1 - θ) * (∫ t : ℝ, beta (1 - θ) t * Real.log (M0 t) ∂volume) +
      θ * (∫ t : ℝ, beta θ t * Real.log (M1 t) ∂volume) := by
  let δ : ℝ := min m0 m1
  have hδ : 0 < δ := lt_min hm0 hm1
  have hδ0 : δ ≤ m0 := min_le_left _ _
  have hδ1 : δ ≤ m1 := min_le_right _ _
  let f : ℂ → ℂ := fun z => g z / (δ : ℂ)
  have hf : DiffContOnCl ℂ f (Complex.HadamardThreeLines.verticalStrip 0 1) :=
    ⟨hg.differentiableOn.div_const _, hg.continuousOn.div_const _⟩
  have hfB : BddAbove ((norm ∘ f) '' Complex.HadamardThreeLines.verticalClosedStrip 0 1) := by
    obtain ⟨B, hbound⟩ := hB
    refine ⟨B / δ, ?_⟩
    rintro y ⟨z, hz, rfl⟩
    dsimp [f, Function.comp_def]
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδ]
    exact div_le_div_of_nonneg_right (hbound ⟨z, hz, rfl⟩) hδ.le
  have hfne : f (θ : ℂ) ≠ 0 := div_ne_zero hne (Complex.ofReal_ne_zero.mpr hδ.ne')
  have hcircle := integrable_boundary_circle_clipped hθ hf hfB
  have hkernel := integrable_boundary_kernels_of_circle hθ
    (fun z => Real.log (max 1 ‖f z‖)) hcircle
  have hsubmean := log_norm_le_boundary_circleAverage_clipped hθ hf hfB hfne
  rw [circleAverage_stripDiskMap_eq hθ (fun z => Real.log (max 1 ‖f z‖)) hcircle] at hsubmean
  have hlog0 : Integrable (fun t : ℝ => leftKernel θ t * Real.log (M0 t)) := by
    simpa only [leftKernel, mul_assoc] using
      (integrable_beta_mul_log_majorant (one_sub_mem_Ioo hθ) M0 hM0 hm0 hlo0 hhi0).const_mul (1 - θ)
  have hlog1 : Integrable (fun t : ℝ => rightKernel θ t * Real.log (M1 t)) := by
    simpa only [rightKernel, mul_assoc] using
      (integrable_beta_mul_log_majorant hθ M1 hM1 hm1 hlo1 hhi1).const_mul θ
  have hshift0 : Integrable (fun t : ℝ => leftKernel θ t * (Real.log (M0 t) - Real.log δ)) := by
    convert hlog0.sub ((integrable_leftKernel hθ).mul_const (Real.log δ)) using 1
    ext t
    simp only [Pi.sub_apply, mul_sub]
  have hshift1 : Integrable (fun t : ℝ => rightKernel θ t * (Real.log (M1 t) - Real.log δ)) := by
    convert hlog1.sub ((integrable_rightKernel hθ).mul_const (Real.log δ)) using 1
    ext t
    simp only [Pi.sub_apply, mul_sub]
  have hle0 := integral_mono hkernel.1 hshift0 (fun t =>
    mul_le_mul_of_nonneg_left
      (clipped_log_div_le_log_majorant hδ (hδ0.trans (hlo0 t)) (hboundary0 t))
      (by rw [leftKernel_eq_rawLeftKernel hθ]; exact (HirschmanBoundaryChange.rawLeftKernel_pos hθ t).le))
  have hle1 := integral_mono hkernel.2 hshift1 (fun t =>
    mul_le_mul_of_nonneg_left
      (clipped_log_div_le_log_majorant hδ (hδ1.trans (hlo1 t)) (hboundary1 t))
      (by rw [rightKernel_eq_rawRightKernel hθ]; exact (HirschmanBoundaryChange.rawRightKernel_pos hθ t).le))
  have hfinal := hsubmean.trans (add_le_add hle0 hle1)
  have hlog : Real.log ‖f (θ : ℂ)‖ = Real.log ‖g (θ : ℂ)‖ - Real.log δ := by
    dsimp [f]
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδ,
      Real.log_div (norm_ne_zero_iff.mpr hne) hδ.ne']
  have hint0 : (∫ t : ℝ, leftKernel θ t * (Real.log (M0 t) - Real.log δ)) =
      (1 - θ) * (∫ t : ℝ, beta (1 - θ) t * Real.log (M0 t)) - (1 - θ) * Real.log δ := by
    simp_rw [mul_sub]
    rw [integral_sub hlog0 ((integrable_leftKernel hθ).mul_const (Real.log δ)),
      integral_mul_const, integral_leftKernel hθ]
    simp only [leftKernel, mul_assoc, integral_const_mul]
  have hint1 : (∫ t : ℝ, rightKernel θ t * (Real.log (M1 t) - Real.log δ)) =
      θ * (∫ t : ℝ, beta θ t * Real.log (M1 t)) - θ * Real.log δ := by
    simp_rw [mul_sub]
    rw [integral_sub hlog1 ((integrable_rightKernel hθ).mul_const (Real.log δ)),
      integral_mul_const, integral_rightKernel hθ]
    simp only [rightKernel, mul_assoc, integral_const_mul]
  rw [hlog, hint0, hint1] at hfinal
  nlinarith [hfinal]

end QuantumProver.HirschmanInterpolation

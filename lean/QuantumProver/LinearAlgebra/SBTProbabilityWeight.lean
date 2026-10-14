import Mathlib

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace QuantumProver.SBTProbabilityWeight

def beta0 (t : ℝ) : ℝ := Real.pi / (2 * (1 + Real.cosh (Real.pi * t)))

theorem beta0_pos (t : ℝ) : 0 < beta0 t := by
  unfold beta0
  apply div_pos Real.pi_pos
  apply mul_pos (by norm_num)
  have h := Real.cosh_pos (Real.pi * t)
  linarith

theorem beta0_nonneg (t : ℝ) : 0 ≤ beta0 t := (beta0_pos t).le

@[simp] theorem beta0_neg (t : ℝ) : beta0 (-t) = beta0 t := by
  simp [beta0]

theorem continuous_beta0 : Continuous beta0 := by
  unfold beta0
  apply Continuous.div continuous_const
  · fun_prop
  · intro t
    have h := Real.cosh_pos (Real.pi * t)
    positivity

theorem beta0_eq_exp (t : ℝ) :
    beta0 t = Real.pi * Real.exp (Real.pi * t) /
      (1 + Real.exp (Real.pi * t)) ^ 2 := by
  rw [beta0, Real.cosh_eq, Real.exp_neg]
  have he : Real.exp (Real.pi * t) ≠ 0 := (Real.exp_pos _).ne'
  have hd : 1 + Real.exp (Real.pi * t) ≠ 0 := by positivity
  field_simp [he, hd]
  ring

def beta0Primitive (t : ℝ) : ℝ :=
  Real.exp (Real.pi * t) / (1 + Real.exp (Real.pi * t))

theorem beta0Primitive_eq_one_sub_inv (t : ℝ) :
    beta0Primitive t = 1 - (1 + Real.exp (Real.pi * t))⁻¹ := by
  have hd : 1 + Real.exp (Real.pi * t) ≠ 0 := by positivity
  unfold beta0Primitive
  field_simp [hd]
  ring

set_option backward.isDefEq.respectTransparency false in
theorem hasDerivAt_beta0Primitive (t : ℝ) :
    HasDerivAt beta0Primitive (beta0 t) t := by
  have he : HasDerivAt (fun x : ℝ => Real.exp (Real.pi * x))
      (Real.exp (Real.pi * t) * Real.pi) t := by
    simpa only [id_eq, mul_one] using ((hasDerivAt_id t).const_mul Real.pi).exp
  have hd : 1 + Real.exp (Real.pi * t) ≠ 0 := by positivity
  convert he.div ((hasDerivAt_const t (1 : ℝ)).add he) hd using 1
  · rfl
  · dsimp only [Pi.add_apply]
    rw [beta0_eq_exp]
    field_simp [hd]
    ring

theorem tendsto_beta0Primitive_atBot : Tendsto beta0Primitive atBot (𝓝 0) := by
  have he : Tendsto (fun t : ℝ => Real.exp (Real.pi * t)) atBot (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (Filter.Tendsto.const_mul_atBot Real.pi_pos tendsto_id)
  have ho : Tendsto (fun _ : ℝ => (1 : ℝ)) atBot (𝓝 1) := tendsto_const_nhds
  convert he.div (ho.add he) (by norm_num : (1 : ℝ) + 0 ≠ 0) using 1 <;>
    first | rfl | norm_num

theorem tendsto_beta0Primitive_atTop : Tendsto beta0Primitive atTop (𝓝 1) := by
  have he : Tendsto (fun t : ℝ => Real.exp (Real.pi * t)) atTop atTop :=
    Real.tendsto_exp_atTop.comp (Filter.Tendsto.const_mul_atTop Real.pi_pos tendsto_id)
  have ho : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have hd : Tendsto (fun t : ℝ => 1 + Real.exp (Real.pi * t)) atTop atTop := by
    simpa only [add_comm] using he.atTop_add ho
  have hi : Tendsto (fun t : ℝ => (1 + Real.exp (Real.pi * t))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hd
  simpa only [← beta0Primitive_eq_one_sub_inv, sub_zero] using ho.sub hi

theorem integrableOn_beta0_Ioi : IntegrableOn beta0 (Ioi (0 : ℝ)) volume := by
  exact integrableOn_Ioi_deriv_of_nonneg'
    (fun t _ => hasDerivAt_beta0Primitive t)
    (fun t _ => beta0_nonneg t) tendsto_beta0Primitive_atTop

theorem integrable_beta0 : Integrable beta0 volume := by
  have htop := integrableOn_beta0_Ioi
  have hset : (fun x : ℝ => -x) ⁻¹' Ioi (0 : ℝ) = Iio (0 : ℝ) := by
    ext x
    simp
  have hbotOpen : IntegrableOn beta0 (Iio (0 : ℝ)) volume := by
    have h := (MeasurePreserving.integrableOn_comp_preimage
      (Measure.measurePreserving_neg volume) (Homeomorph.neg ℝ).measurableEmbedding).2 htop
    simpa only [hset, Function.comp_def, beta0_neg] using h
  have hbot : IntegrableOn beta0 (Iic (0 : ℝ)) volume :=
    (integrableOn_Iic_iff_integrableOn_Iio (f := beta0) (b := (0 : ℝ))
      (μ := volume) (by finiteness)).mpr hbotOpen
  have h := hbot.union htop
  simpa only [Iic_union_Ioi, integrableOn_univ] using h

theorem integral_beta0_eq_one : (∫ t : ℝ, beta0 t ∂volume) = 1 := by
  simpa only [sub_zero] using integral_of_hasDerivAt_of_tendsto
    hasDerivAt_beta0Primitive integrable_beta0
    tendsto_beta0Primitive_atBot tendsto_beta0Primitive_atTop

def beta0Density (t : ℝ) : ℝ≥0∞ := ENNReal.ofReal (beta0 t)

theorem measurable_beta0Density : Measurable beta0Density :=
  continuous_beta0.measurable.ennreal_ofReal

@[simp] theorem beta0Density_toReal (t : ℝ) : (beta0Density t).toReal = beta0 t :=
  ENNReal.toReal_ofReal (beta0_nonneg t)

theorem beta0Density_lt_top (t : ℝ) : beta0Density t < ∞ := by
  simp [beta0Density]

theorem lintegral_beta0Density_eq_one : (∫⁻ t : ℝ, beta0Density t ∂volume) = 1 := by
  change (∫⁻ t : ℝ, ENNReal.ofReal (beta0 t) ∂volume) = 1
  rw [← ofReal_integral_eq_lintegral_ofReal integrable_beta0
    (Eventually.of_forall beta0_nonneg), integral_beta0_eq_one]
  norm_num

def beta0Probability : Measure ℝ := volume.withDensity beta0Density

theorem beta0Probability_eq_withDensity :
    beta0Probability = volume.withDensity (fun t => ENNReal.ofReal (beta0 t)) := rfl

instance beta0Probability_isProbabilityMeasure : IsProbabilityMeasure beta0Probability where
  measure_univ := by
    rw [beta0Probability, withDensity_apply _ MeasurableSet.univ,
      Measure.restrict_univ, lintegral_beta0Density_eq_one]

theorem beta0Probability_apply {s : Set ℝ} (hs : MeasurableSet s) :
    beta0Probability s = ∫⁻ t in s, ENNReal.ofReal (beta0 t) ∂volume := by
  exact withDensity_apply beta0Density hs

section Bochner

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem integrable_beta0Probability_iff (f : ℝ → F) :
    Integrable f beta0Probability ↔ Integrable (fun t => beta0 t • f t) volume := by
  simpa only [beta0Probability, beta0Density_toReal] using
    (integrable_withDensity_iff_integrable_smul' (μ := volume)
      measurable_beta0Density (Eventually.of_forall beta0Density_lt_top) (g := f))

theorem integral_beta0Probability (f : ℝ → F) :
    (∫ t : ℝ, f t ∂beta0Probability) = ∫ t : ℝ, beta0 t • f t ∂volume := by
  simpa only [beta0Probability, beta0Density_toReal] using
    (integral_withDensity_eq_integral_toReal_smul (μ := volume)
      measurable_beta0Density (Eventually.of_forall beta0Density_lt_top) f)

end Bochner

theorem integral_beta0Probability_real (f : ℝ → ℝ) :
    (∫ t : ℝ, f t ∂beta0Probability) = ∫ t : ℝ, beta0 t * f t ∂volume := by
  simpa only [smul_eq_mul] using integral_beta0Probability f

end QuantumProver.SBTProbabilityWeight

import Mathlib

noncomputable section

open Complex Filter MeasureTheory Metric Set
open scoped Topology

namespace QuantumProver.HirschmanRadialLimit

def clippedLog (z : ℂ) : ℝ := Real.log (max 1 ‖z‖)

theorem continuous_clippedLog : Continuous clippedLog := by
  apply Continuous.log (continuous_const.max continuous_norm)
  intro z
  exact ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_left 1 ‖z‖))

theorem clippedLog_nonnegative (z : ℂ) : 0 ≤ clippedLog z := by
  exact Real.log_nonneg (le_max_left 1 ‖z‖)

theorem norm_clippedLog_le {z : ℂ} {C : ℝ} (hz : ‖z‖ ≤ C) :
    ‖clippedLog z‖ ≤ Real.log (max 1 C) := by
  rw [Real.norm_of_nonneg (clippedLog_nonnegative z)]
  exact Real.log_le_log
    (lt_of_lt_of_le zero_lt_one (le_max_left 1 ‖z‖))
    (max_le_max le_rfl hz)

theorem circleMap_mem_unitDisk {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) (t : ℝ) :
    circleMap 0 r t ∈ ball (0 : ℂ) 1 := by
  simpa only [mem_ball, dist_zero_right, norm_circleMap_zero, abs_of_pos hr.1]
    using hr.2

theorem continuous_radial_clippedLog {f : ℂ → ℂ}
    (hf : ContinuousOn f (ball (0 : ℂ) 1)) {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) :
    Continuous (fun t : ℝ => clippedLog (f (circleMap 0 r t))) := by
  exact continuous_clippedLog.comp
    (hf.comp_continuous (continuous_circleMap 0 r) (circleMap_mem_unitDisk hr))

theorem circleAverage_eq_normalized_Icc_integral (h : ℂ → ℝ) (r : ℝ) :
    Real.circleAverage h 0 r =
      (2 * Real.pi)⁻¹ * ∫ t in Icc (0 : ℝ) (2 * Real.pi), h (circleMap 0 r t) := by
  rw [Real.circleAverage_def, smul_eq_mul,
    intervalIntegral.integral_of_le (by positivity), ← integral_Icc_eq_integral_Ioc]

theorem boundary_clippedLog_aestronglyMeasurable {f k : ℂ → ℂ}
    (hf : ContinuousOn f (ball (0 : ℂ) 1))
    (hlim : ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) (2 * Real.pi))),
      Tendsto (fun r : ℝ => f (circleMap 0 r t)) (𝓝[<] 1)
        (𝓝 (k (circleMap 0 1 t)))) :
    AEStronglyMeasurable (fun t : ℝ => clippedLog (k (circleMap 0 1 t)))
      (volume.restrict (Icc (0 : ℝ) (2 * Real.pi))) := by
  let F : ℝ → ℝ → ℝ := fun r t =>
    if r ∈ Ioo (0 : ℝ) 1 then clippedLog (f (circleMap 0 r t)) else 0
  have hF : ∀ r, AEStronglyMeasurable (F r)
      (volume.restrict (Icc (0 : ℝ) (2 * Real.pi))) := by
    intro r
    by_cases hr : r ∈ Ioo (0 : ℝ) 1
    · simpa only [F, ite_eq_left hr] using
        (continuous_radial_clippedLog hf hr).aestronglyMeasurable
    · simpa only [F, ite_eq_right hr] using
        (aestronglyMeasurable_const : AEStronglyMeasurable (fun _ : ℝ => (0 : ℝ))
          (volume.restrict (Icc (0 : ℝ) (2 * Real.pi))))
  apply aestronglyMeasurable_of_tendsto_ae (𝓝[<] (1 : ℝ)) hF
  filter_upwards [hlim] with t ht
  apply ((continuous_clippedLog.tendsto _).comp ht).congr'
  filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with r hr
  simp only [F, ite_eq_left hr, Function.comp_apply]

theorem boundary_clippedLog_integrable {f k : ℂ → ℂ} {C : ℝ}
    (hf : ContinuousOn f (ball (0 : ℂ) 1))
    (hbound : ∀ z : ℂ, ‖z‖ < 1 → ‖f z‖ ≤ C)
    (hlim : ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) (2 * Real.pi))),
      Tendsto (fun r : ℝ => f (circleMap 0 r t)) (𝓝[<] 1)
        (𝓝 (k (circleMap 0 1 t)))) :
    IntegrableOn (fun t : ℝ => clippedLog (k (circleMap 0 1 t)))
      (Icc (0 : ℝ) (2 * Real.pi)) := by
  have hConst : IntegrableOn (fun _ : ℝ => Real.log (max 1 C))
      (Icc (0 : ℝ) (2 * Real.pi)) := integrableOn_const isCompact_Icc.measure_ne_top
  apply hConst.mono' (boundary_clippedLog_aestronglyMeasurable hf hlim)
  filter_upwards [hlim] with t ht
  apply norm_clippedLog_le
  apply le_of_tendsto ht.norm
  filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with r hr
  apply hbound
  simpa only [norm_circleMap_zero, abs_of_pos hr.1] using hr.2

theorem tendsto_circleAverage_clippedLog {f k : ℂ → ℂ} {C : ℝ}
    (hf : ContinuousOn f (ball (0 : ℂ) 1))
    (hbound : ∀ z : ℂ, ‖z‖ < 1 → ‖f z‖ ≤ C)
    (hlim : ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) (2 * Real.pi))),
      Tendsto (fun r : ℝ => f (circleMap 0 r t)) (𝓝[<] 1)
        (𝓝 (k (circleMap 0 1 t)))) :
    Tendsto (fun r : ℝ => Real.circleAverage (fun z => Real.log (max 1 ‖f z‖)) 0 r)
      (𝓝[<] 1)
      (𝓝 (Real.circleAverage (fun z => Real.log (max 1 ‖k z‖)) 0 1)) := by
  have hmeas : ∀ᶠ r in 𝓝[<] (1 : ℝ),
      AEStronglyMeasurable (fun t : ℝ => clippedLog (f (circleMap 0 r t)))
        (volume.restrict (Icc (0 : ℝ) (2 * Real.pi))) := by
    filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with r hr
    exact (continuous_radial_clippedLog hf hr).aestronglyMeasurable
  have hnorm : ∀ᶠ r in 𝓝[<] (1 : ℝ),
      ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) (2 * Real.pi))),
        ‖clippedLog (f (circleMap 0 r t))‖ ≤ Real.log (max 1 C) := by
    filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with r hr
    exact Eventually.of_forall fun t => norm_clippedLog_le
      (hbound _ (by simpa only [norm_circleMap_zero, abs_of_pos hr.1] using hr.2))
  have hConst : Integrable (fun _ : ℝ => Real.log (max 1 C))
      (volume.restrict (Icc (0 : ℝ) (2 * Real.pi))) :=
    integrableOn_const isCompact_Icc.measure_ne_top
  have hpoint : ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) (2 * Real.pi))),
      Tendsto (fun r : ℝ => clippedLog (f (circleMap 0 r t))) (𝓝[<] 1)
        (𝓝 (clippedLog (k (circleMap 0 1 t)))) := by
    filter_upwards [hlim] with t ht
    exact (continuous_clippedLog.tendsto _).comp ht
  have hint := tendsto_integral_filter_of_dominated_convergence
    (fun _ : ℝ => Real.log (max 1 C)) hmeas hnorm hConst hpoint
  simpa only [circleAverage_eq_normalized_Icc_integral, clippedLog]
    using hint.const_mul ((2 * Real.pi)⁻¹)

end QuantumProver.HirschmanRadialLimit

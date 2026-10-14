import QuantumProver.InformationTheory.FinitePR.SphereGeometry
import Mathlib

/-! Identical actual chart/prior declarations extracted by agreement from A Main37.
Only an acyclic ownership move: no alternate sphere prior is substituted. -/

namespace FinitePR.Sphere

open MeasureTheory Set
open scoped unitInterval
def uniformHeight (u : I) : Height :=
  ⟨2 * (u : ℝ) - 1, by
    constructor <;> linarith [u.property.1, u.property.2]⟩

theorem continuous_uniformHeight : Continuous uniformHeight := by
  exact ((continuous_const.mul continuous_subtype_val).sub continuous_const).subtype_mk _

noncomputable def uniformChart (p : I × I) : Height × ℝ :=
  (uniformHeight p.1, -Real.pi + 2 * Real.pi * (p.2 : ℝ))

theorem continuous_uniformChart : Continuous uniformChart := by
  exact (continuous_uniformHeight.comp continuous_fst).prodMk (by fun_prop)

noncomputable def uniformSphereSample (p : I × I) : Direction :=
  parameterDirection (uniformChart p)

theorem continuous_uniformSphereSample : Continuous uniformSphereSample :=
  continuous_parameterDirection.comp continuous_uniformChart

/-- The explicit normalized height-longitude probability law on the sphere. -/
noncomputable def uniformSpherePrior : ProbabilityMeasure Direction :=
  ProbabilityMeasure.map
    (⟨(volume : Measure I).prod (volume : Measure I), inferInstance⟩ :
      ProbabilityMeasure (I × I)) uniformSphereSample

theorem integral_uniformHeight (g : ℝ → ℝ) :
    (∫ u : I, g (2 * (u : ℝ) - 1)) =
      (1 / 2 : ℝ) * ∫ h in (-1 : ℝ)..1, g h := by
  rw [unitInterval.volume_def, integral_subtype_comap measurableSet_Icc
      (fun u : ℝ => g (2 * u - 1)),
    integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (a := (0 : ℝ)) (b := 1) (by norm_num)]
  simpa only [sub_eq_add_neg, mul_zero, zero_add, mul_one, smul_eq_mul,
    one_div, show (2 : ℝ) + -1 = 1 by norm_num] using
    (intervalIntegral.integral_comp_mul_add (a := (0 : ℝ)) (b := 1)
      (c := (2 : ℝ)) g (by norm_num) (-1))

/-- Exact axial distribution of the concrete pushforward, with its normalization factor. -/
theorem uniformSpherePrior_integral_height (g : ℝ → ℝ) (hg : Continuous g) :
    (∫ t : Direction, g (t.1 2) ∂(uniformSpherePrior : Measure Direction)) =
      (1 / 2 : ℝ) * ∫ h in (-1 : ℝ)..1, g h := by
  rw [show (uniformSpherePrior : Measure Direction) =
      ((volume : Measure I).prod (volume : Measure I)).map uniformSphereSample from rfl]
  have htest : Continuous (fun t : Direction => g (t.1 2)) :=
    hg.comp ((continuous_apply (2 : Fin 3)).comp continuous_subtype_val)
  rw [integral_map continuous_uniformSphereSample.measurable.aemeasurable
    htest.aestronglyMeasurable]
  change (∫ p : I × I, g (2 * (p.1 : ℝ) - 1)
    ∂(volume : Measure I).prod (volume : Measure I)) = _
  rw [integral_fun_fst (fun u : I => g (2 * (u : ℝ) - 1))]
  simpa using integral_uniformHeight g

theorem integral_positivePart_height :
    (∫ h in (-1 : ℝ)..1, max h 0) = (1 / 2 : ℝ) := by
  have hc : Continuous (fun h : ℝ => max h 0) := continuous_id.max continuous_const
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable (-1) 0) (hc.intervalIntegrable 0 1)]
  have hl : (∫ h in (-1 : ℝ)..0, max h 0) = 0 := by
    calc
      _ = ∫ h in (-1 : ℝ)..0, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro h hh
        rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 0)] at hh
        exact max_eq_right hh.2
      _ = 0 := by simp
  have hr : (∫ h in (0 : ℝ)..1, max h 0) = (1 / 2 : ℝ) := by
    calc
      _ = ∫ h in (0 : ℝ)..1, h := by
        apply intervalIntegral.integral_congr
        intro h hh
        rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hh
        exact max_eq_left hh.1
      _ = 1 / 2 := by norm_num [integral_id]
  rw [hl, hr, zero_add]

theorem uniformSpherePrior_positivePart_height :
    (∫ t : Direction, max (t.1 2) 0 ∂(uniformSpherePrior : Measure Direction)) =
      (1 / 4 : ℝ) := by
  have hh := uniformSpherePrior_integral_height (fun h : ℝ => max h 0)
    (continuous_id.max continuous_const)
  rw [integral_positivePart_height] at hh
  norm_num at hh ⊢
  exact hh

end FinitePR.Sphere

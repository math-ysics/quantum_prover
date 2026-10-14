import QuantumProver.InformationTheory.FinitePR.SphereSteeringLaw
import Mathlib

/-! Exact transport from the proved axial moments. The only geometric input is
the stated orthogonal map equality for the same actual chart prior. Main proves
that input; this module does not assume a replacement prior or moment theorem. -/

namespace FinitePR.Sphere.Transport

open MeasureTheory Set
open scoped BigOperators unitInterval

abbrev Space := EuclideanSpace ℝ (Fin 3)
abbrev Orthogonal := Space ≃ₗᵢ[ℝ] Space

noncomputable def action (A : Orthogonal) (t : Direction) : Direction :=
  ⟨WithLp.ofLp (A (WithLp.toLp 2 t.1)), by
    have hn : ‖A (directionVector t)‖ = 1 :=
      (A.norm_map _).trans (norm_directionVector t)
    have hs := congrArg (fun r : ℝ => r ^ 2) hn
    simpa only [EuclideanSpace.real_norm_sq_eq, one_pow, directionVector] using hs⟩

lemma continuous_action (A : Orthogonal) : Continuous (action A) :=
  (((PiLp.continuous_ofLp 2 (fun _ : Fin 3 => ℝ)).comp
    (A.continuous.comp (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)))).comp
      continuous_subtype_val).subtype_mk _

noncomputable def axis : Direction := ⟨![0, 0, 1], by norm_num [Fin.sum_univ_three]⟩

lemma blochDot_axis (t : Direction) : blochDot axis t = t.1 2 := by
  simp [blochDot, axis, Fin.sum_univ_three]

lemma directionVector_action (A : Orthogonal) (t : Direction) :
    directionVector (action A t) = A (directionVector t) := rfl

lemma action_apply_symm (A : Orthogonal) (t : Direction) :
    action A (action A.symm t) = t := by
  apply Subtype.ext
  change WithLp.ofLp (A (A.symm (directionVector t))) = t.1
  rw [A.apply_symm_apply]
  rfl

lemma inner_directionVector (v t : Direction) :
    inner ℝ (directionVector v) (directionVector t) = blochDot v t := by
  simp [blochDot, PiLp.inner_apply, directionVector, Fin.sum_univ_three]
  ring

lemma blochDot_action (A : Orthogonal) (v t : Direction) :
    blochDot (action A v) (action A t) = blochDot v t := by
  rw [← inner_directionVector, directionVector_action, directionVector_action,
    A.inner_map_map, inner_directionVector]

/-- A real Householder reflection actually moves every unit direction to the axis. -/
theorem exists_axis_isometry (b : Direction) :
    ∃ A : Orthogonal, A (directionVector b) = directionVector axis := by
  refine ⟨(ℝ ∙ (directionVector b - directionVector axis))ᗮ.reflection, ?_⟩
  exact Submodule.reflection_sub (by rw [norm_directionVector, norm_directionVector])

lemma action_axis_of_vector (A : Orthogonal) (b : Direction)
    (hA : A (directionVector b) = directionVector axis) : action A b = axis := by
  apply Subtype.ext
  change WithLp.ofLp (A (directionVector b)) = axis.1
  rw [hA]
  rfl

lemma height_action (A : Orthogonal) (b t : Direction)
    (hA : A (directionVector b) = directionVector axis) :
    (action A t).1 2 = blochDot b t := by
  have he := blochDot_action A b t
  rw [action_axis_of_vector A b hA, blochDot_axis] at he
  exact he

lemma projection_action_symm (A : Orthogonal) (b t : Direction)
    (hA : A (directionVector b) = directionVector axis) :
    blochDot b (action A.symm t) = t.1 2 := by
  have he := height_action A b (action A.symm t) hA
  rw [action_apply_symm] at he
  exact he.symm

noncomputable def signedVector (b t : Direction) : Space :=
  Real.sign (blochDot b t) • directionVector t

lemma measurable_directionVector : Measurable directionVector :=
  ((PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).comp continuous_subtype_val).measurable

lemma measurable_signedVector (b : Direction) : Measurable (signedVector b) :=
  (measurable_realSign.comp (measurable_blochDot b)).smul measurable_directionVector

lemma integrable_signedVector (b : Direction) :
    Integrable (signedVector b) (uniformSpherePrior : Measure Direction) := by
  apply (integrable_const (1 : ℝ)).mono' (measurable_signedVector b).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun t => by
    change ‖Real.sign (blochDot b t) • directionVector t‖ ≤ 1
    simpa [norm_smul, norm_directionVector, Real.norm_eq_abs] using
      realSign_abs_le_one (blochDot b t)

lemma axial_vector_integral :
    (∫ t, signedVector axis t ∂(uniformSpherePrior : Measure Direction)) =
      (1 / 2 : ℝ) • directionVector axis := by
  ext i
  have he := (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) i).integral_comp_comm
    (integrable_signedVector axis)
  change (∫ t, Real.sign (blochDot axis t) * t.1 i
    ∂(uniformSpherePrior : Measure Direction)) =
      (∫ t, signedVector axis t ∂(uniformSpherePrior : Measure Direction)) i at he
  rw [← he]
  simp_rw [blochDot_axis]
  rw [axial_signed_moment]
  fin_cases i <;> norm_num [directionVector, axis, PiLp.smul_apply]

lemma vector_integral_invariant (A : Orthogonal)
    (hmap : (uniformSpherePrior : Measure Direction).map (action A) =
      (uniformSpherePrior : Measure Direction)) (f : Direction → Space) (hf : Measurable f) :
    (∫ t, f (action A t) ∂(uniformSpherePrior : Measure Direction)) =
      ∫ t, f t ∂(uniformSpherePrior : Measure Direction) := by
  have he := integral_map (μ := (uniformSpherePrior : Measure Direction))
    (continuous_action A).measurable.aemeasurable hf.aestronglyMeasurable
  rw [hmap] at he
  exact he.symm

/-- The geometric premise is exactly the family of actual-prior map equalities. -/
theorem signed_vector_moment
    (hinv : ∀ A : Orthogonal, (uniformSpherePrior : Measure Direction).map (action A) =
      (uniformSpherePrior : Measure Direction)) (b : Direction) :
    (∫ t, signedVector b t ∂(uniformSpherePrior : Measure Direction)) =
      (1 / 2 : ℝ) • directionVector b := by
  obtain ⟨A, hA⟩ := exists_axis_isometry b
  have he : (fun t => signedVector b (action A.symm t)) =
      fun t => A.symm (signedVector axis t) := by
    funext t
    unfold signedVector
    rw [projection_action_symm A b t hA, blochDot_axis, directionVector_action]
    exact (A.symm.map_smul (Real.sign (t.1 2)) (directionVector t)).symm
  have haxis : A.symm (directionVector axis) = directionVector b := by
    rw [← hA, A.symm_apply_apply]
  calc
    (∫ t, signedVector b t ∂(uniformSpherePrior : Measure Direction)) =
        ∫ t, signedVector b (action A.symm t)
          ∂(uniformSpherePrior : Measure Direction) :=
      (vector_integral_invariant A.symm (hinv A.symm) _ (measurable_signedVector b)).symm
    _ = ∫ t, A.symm (signedVector axis t)
        ∂(uniformSpherePrior : Measure Direction) := by rw [he]
    _ = A.symm (∫ t, signedVector axis t
        ∂(uniformSpherePrior : Measure Direction)) :=
      A.symm.toLinearIsometry.integral_comp_comm _
    _ = (1 / 2 : ℝ) • directionVector b := by
      rw [axial_vector_integral, A.symm.map_smul, haxis]

theorem signed_coordinate_moment
    (hinv : ∀ A : Orthogonal, (uniformSpherePrior : Measure Direction).map (action A) =
      (uniformSpherePrior : Measure Direction)) (b : Direction) (i : Fin 3) :
    (∫ t, t.1 i * Real.sign (blochDot b t)
      ∂(uniformSpherePrior : Measure Direction)) = b.1 i / 2 := by
  have he := (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) i).integral_comp_comm
    (integrable_signedVector b)
  rw [signed_vector_moment hinv b] at he
  change (∫ t, Real.sign (blochDot b t) * t.1 i
      ∂(uniformSpherePrior : Measure Direction)) = (1 / 2 : ℝ) * b.1 i at he
  simpa only [mul_comm, div_eq_mul_inv, one_div, one_mul] using he

theorem projection_zero_null
    (hinv : ∀ A : Orthogonal, (uniformSpherePrior : Measure Direction).map (action A) =
      (uniformSpherePrior : Measure Direction)) (b : Direction) :
    (uniformSpherePrior : Measure Direction) {t | blochDot b t = 0} = 0 := by
  obtain ⟨A, hA⟩ := exists_axis_isometry b
  have he := congrArg (fun μ : Measure Direction => μ {t | t.1 2 = 0}) (hinv A)
  rw [Measure.map_apply (continuous_action A).measurable
    (measurableSet_eq_fun (measurable_coordinate 2) measurable_const),
    uniformSpherePrior_height_zero] at he
  have hset : action A ⁻¹' {t : Direction | t.1 2 = 0} = {t | blochDot b t = 0} := by
    ext t
    simp only [mem_preimage, mem_setOf_eq, height_action A b t hA]
  rw [hset] at he
  exact he

theorem abs_projection_integral
    (hinv : ∀ A : Orthogonal, (uniformSpherePrior : Measure Direction).map (action A) =
      (uniformSpherePrior : Measure Direction)) (v : Direction) :
    (∫ t, |blochDot v t| ∂(uniformSpherePrior : Measure Direction)) = (1 / 2 : ℝ) := by
  obtain ⟨A, hA⟩ := exists_axis_isometry v
  have haxis : (∫ t, |t.1 2| ∂(uniformSpherePrior : Measure Direction)) = (1 / 2 : ℝ) := by
    simpa only [realSign_mul_self] using integral_height_sign_height
  calc
    (∫ t, |blochDot v t| ∂(uniformSpherePrior : Measure Direction)) =
        ∫ t, |(action A t).1 2| ∂(uniformSpherePrior : Measure Direction) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun t => congrArg abs (height_action A v t hA).symm
    _ = ∫ t, |t.1 2| ∂(uniformSpherePrior : Measure Direction) :=
      integral_invariant (action A) ⟨(continuous_action A).measurable, hinv A⟩ _
        (measurable_coordinate 2).abs
    _ = 1 / 2 := haxis

theorem sign_halfmass
    (hinv : ∀ A : Orthogonal, (uniformSpherePrior : Measure Direction).map (action A) =
      (uniformSpherePrior : Measure Direction)) (b : Direction)
    (outcome : ℝ) (houtcome : outcome = 1 ∨ outcome = -1) :
    (uniformSpherePrior : Measure Direction).real {t | Real.sign (blochDot b t) = outcome} =
      (1 / 2 : ℝ) := by
  obtain ⟨A, hA⟩ := exists_axis_isometry b
  have he := congrArg (fun μ : Measure Direction => μ {t | Real.sign (t.1 2) = outcome})
    (hinv A)
  have hmeas : MeasurableSet {t : Direction | Real.sign (t.1 2) = outcome} :=
    measurableSet_eq_fun
      (show Measurable (fun t : Direction => Real.sign (t.1 2)) from
        measurable_realSign.comp (measurable_coordinate 2)) measurable_const
  rw [Measure.map_apply (continuous_action A).measurable hmeas] at he
  have hset : action A ⁻¹' {t : Direction | Real.sign (t.1 2) = outcome} =
      {t | Real.sign (blochDot b t) = outcome} := by
    ext t
    simp only [mem_preimage, mem_setOf_eq, height_action A b t hA]
  rw [hset] at he
  rw [measureReal_def, he]
  exact axial_sign_halfmass outcome houtcome

/-- All analytic steering inputs are derived from the explicit invariance family. -/
theorem steering_test_law
    (hinv : ∀ A : Orthogonal, (uniformSpherePrior : Measure Direction).map (action A) =
      (uniformSpherePrior : Measure Direction)) (v b : Direction)
    (outcome : ℝ) (houtcome : outcome = 1 ∨ outcome = -1) :
    (∫ t, (if Real.sign (blochDot b t) = outcome
      then 4 * max (blochDot v t) 0 else 0)
        ∂(uniformSpherePrior : Measure Direction)) =
      (1 + outcome * blochDot v b) / 2 :=
  steering_test_law_of_projection_moments v b outcome houtcome
    (abs_projection_integral hinv v) (signed_coordinate_moment hinv b)
    (projection_zero_null hinv b)

theorem steering_test_law_positive_tie
    (hinv : ∀ A : Orthogonal, (uniformSpherePrior : Measure Direction).map (action A) =
      (uniformSpherePrior : Measure Direction)) (v b : Direction)
    (outcome : ℝ) (houtcome : outcome = 1 ∨ outcome = -1) :
    (∫ t, (if positiveTieSign (blochDot b t) = outcome
      then 4 * max (blochDot v t) 0 else 0)
        ∂(uniformSpherePrior : Measure Direction)) =
      (1 + outcome * blochDot v b) / 2 :=
  FinitePR.Sphere.steering_test_law_positive_tie v b outcome houtcome
    (abs_projection_integral hinv v) (signed_coordinate_moment hinv b)
    (projection_zero_null hinv b)

end FinitePR.Sphere.Transport

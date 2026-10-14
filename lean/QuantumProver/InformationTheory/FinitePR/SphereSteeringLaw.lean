import QuantumProver.InformationTheory.FinitePR.SphereSignIntegrals
import Mathlib

/-! Algebraic steering law for the actual prior. The absolute projection,
rotated signed coordinate moments, and rotated zero-set nullity are explicit
inputs to the final theorem; none is declared as an axiom. -/

namespace FinitePR.Sphere

open MeasureTheory Set
open scoped BigOperators unitInterval

lemma measurable_blochDot (v : Direction) : Measurable (blochDot v) := by
  unfold blochDot
  exact Finset.measurable_sum Finset.univ fun i _ =>
    measurable_const.mul (measurable_coordinate i)

lemma blochDot_antipodal (v t : Direction) :
    blochDot v (antipodalDirection t) = -blochDot v t := by
  simp [blochDot, antipodalDirection, Fin.sum_univ_three]

lemma blochDot_abs_le_one (v t : Direction) : |blochDot v t| ≤ 1 := by
  have he : blochDot v t = inner ℝ (directionVector v) (directionVector t) := by
    simp [blochDot, PiLp.inner_apply, Real.inner_apply, directionVector,
      Fin.sum_univ_three]
    ring
  rw [he]
  simpa [norm_directionVector] using
    abs_real_inner_le_norm (directionVector v) (directionVector t)

lemma realSign_abs_le_one (r : ℝ) : |Real.sign r| ≤ 1 := by
  rcases Real.sign_apply_eq r with h | h | h <;> rw [h] <;> norm_num

lemma integrable_blochDot (v : Direction) :
    Integrable (blochDot v) (uniformSpherePrior : Measure Direction) :=
  integrable_bounded _ (measurable_blochDot v) 1 (blochDot_abs_le_one v)

lemma integrable_abs_blochDot (v : Direction) :
    Integrable (fun t => |blochDot v t|) (uniformSpherePrior : Measure Direction) := by
  apply integrable_bounded _ (measurable_blochDot v).abs 1
  intro t
  simpa only [abs_abs] using blochDot_abs_le_one v t

lemma integrable_blochDot_sign (v b : Direction) :
    Integrable (fun t => blochDot v t * Real.sign (blochDot b t))
      (uniformSpherePrior : Measure Direction) := by
  apply integrable_bounded _
    ((measurable_blochDot v).mul (measurable_realSign.comp (measurable_blochDot b))) 1
  intro t
  change |blochDot v t * Real.sign (blochDot b t)| ≤ 1
  rw [abs_mul]
  simpa using mul_le_mul (blochDot_abs_le_one v t)
    (realSign_abs_le_one (blochDot b t)) (abs_nonneg _) zero_le_one

lemma integrable_abs_blochDot_sign (v b : Direction) :
    Integrable (fun t => |blochDot v t| * Real.sign (blochDot b t))
      (uniformSpherePrior : Measure Direction) := by
  apply integrable_bounded _
    ((measurable_blochDot v).abs.mul
      (measurable_realSign.comp (measurable_blochDot b))) 1
  intro t
  change |(|blochDot v t| * Real.sign (blochDot b t))| ≤ 1
  rw [abs_mul, abs_abs]
  simpa using mul_le_mul (blochDot_abs_le_one v t)
    (realSign_abs_le_one (blochDot b t)) (abs_nonneg _) zero_le_one

/-- Linear projections have mean zero under the actual antipodal prior. -/
theorem integral_blochDot (v : Direction) :
    (∫ t, blochDot v t ∂(uniformSpherePrior : Measure Direction)) = 0 :=
  integral_antipodal_odd _ (measurable_blochDot v) (blochDot_antipodal v)

/-- Even absolute projection times an odd sign also has mean zero. -/
theorem integral_abs_blochDot_sign (v b : Direction) :
    (∫ t, |blochDot v t| * Real.sign (blochDot b t)
      ∂(uniformSpherePrior : Measure Direction)) = 0 := by
  apply integral_antipodal_odd _
    ((measurable_blochDot v).abs.mul
      (measurable_realSign.comp (measurable_blochDot b)))
  intro t
  change |blochDot v (antipodalDirection t)| * Real.sign (blochDot b (antipodalDirection t)) =
    -(|blochDot v t| * Real.sign (blochDot b t))
  rw [blochDot_antipodal, blochDot_antipodal, abs_neg, Real.sign_neg]
  ring

lemma integral_blochDot_sign_of_coordinates (v b : Direction)
    (hmom : ∀ i : Fin 3,
      (∫ t, t.1 i * Real.sign (blochDot b t)
        ∂(uniformSpherePrior : Measure Direction)) = b.1 i / 2) :
    (∫ t, blochDot v t * Real.sign (blochDot b t)
      ∂(uniformSpherePrior : Measure Direction)) = blochDot v b / 2 := by
  have hint (i : Fin 3) :
      Integrable (fun t : Direction => t.1 i * Real.sign (blochDot b t))
        (uniformSpherePrior : Measure Direction) := by
    apply integrable_bounded _
      ((measurable_coordinate i).mul
        (measurable_realSign.comp (measurable_blochDot b))) 1
    intro t
    change |t.1 i * Real.sign (blochDot b t)| ≤ 1
    rw [abs_mul]
    simpa using mul_le_mul (coordinate_abs_le_one t i)
      (realSign_abs_le_one (blochDot b t)) (abs_nonneg _) zero_le_one
  calc
    (∫ t, blochDot v t * Real.sign (blochDot b t)
      ∂(uniformSpherePrior : Measure Direction)) =
        ∫ t, ∑ i, v.1 i * (t.1 i * Real.sign (blochDot b t))
          ∂(uniformSpherePrior : Measure Direction) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun t => by
        simp [blochDot, Fin.sum_univ_three]
        ring
    _ = ∑ i, v.1 i * (∫ t, t.1 i * Real.sign (blochDot b t)
        ∂(uniformSpherePrior : Measure Direction)) := by
      rw [integral_finsetSum]
      · simp only [integral_const_mul]
      · intro i _
        exact (hint i).const_mul (v.1 i)
    _ = blochDot v b / 2 := by
      have hs : (∑ i, v.1 i * (∫ t, t.1 i * Real.sign (blochDot b t)
          ∂(uniformSpherePrior : Measure Direction))) = ∑ i, v.1 i * (b.1 i / 2) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [hmom i]
      rw [hs]
      simp only [blochDot, Fin.sum_univ_three]
      ring

lemma steering_indicator_algebra (a z outcome : ℝ)
    (hz : z ≠ 0) (houtcome : outcome = 1 ∨ outcome = -1) :
    (if Real.sign z = outcome then 4 * max a 0 else 0) =
      |a| + a + outcome * (|a| * Real.sign z) +
        outcome * (a * Real.sign z) := by
  have hmax : 2 * max a 0 = |a| + a := by
    by_cases ha : 0 ≤ a
    · rw [max_eq_left ha, abs_of_nonneg ha]
      ring
    · have ha' : a ≤ 0 := (lt_of_not_ge ha).le
      rw [max_eq_right ha', abs_of_nonpos ha']
      ring
  rcases houtcome with rfl | rfl <;>
    rcases Real.sign_apply_eq_of_ne_zero z hz with hs | hs <;>
    rw [hs] <;> norm_num <;> nlinarith [hmax]

/-- The exact steering test law follows from the listed projection facts on the
same concrete prior. The projection and rotated-moment inputs remain visible. -/
theorem steering_test_law_of_projection_moments (v b : Direction)
    (outcome : ℝ) (houtcome : outcome = 1 ∨ outcome = -1)
    (habs : (∫ t, |blochDot v t|
      ∂(uniformSpherePrior : Measure Direction)) = (1 / 2 : ℝ))
    (hmom : ∀ i : Fin 3,
      (∫ t, t.1 i * Real.sign (blochDot b t)
        ∂(uniformSpherePrior : Measure Direction)) = b.1 i / 2)
    (hzero : (uniformSpherePrior : Measure Direction) {t | blochDot b t = 0} = 0) :
    (∫ t, (if Real.sign (blochDot b t) = outcome
      then 4 * max (blochDot v t) 0 else 0)
        ∂(uniformSpherePrior : Measure Direction)) =
      (1 + outcome * blochDot v b) / 2 := by
  have hne : ∀ᵐ t ∂(uniformSpherePrior : Measure Direction), blochDot b t ≠ 0 := by
    rw [ae_iff]
    simpa only [not_not] using hzero
  have hintAbs := integrable_abs_blochDot v
  have hintDot := integrable_blochDot v
  have hintAbsSign := (integrable_abs_blochDot_sign v b).const_mul outcome
  have hintDotSign := (integrable_blochDot_sign v b).const_mul outcome
  calc
    (∫ t, (if Real.sign (blochDot b t) = outcome
      then 4 * max (blochDot v t) 0 else 0)
        ∂(uniformSpherePrior : Measure Direction)) =
        ∫ t, |blochDot v t| + blochDot v t +
          outcome * (|blochDot v t| * Real.sign (blochDot b t)) +
          outcome * (blochDot v t * Real.sign (blochDot b t))
            ∂(uniformSpherePrior : Measure Direction) := by
      apply integral_congr_ae
      filter_upwards [hne] with t ht
      exact steering_indicator_algebra _ _ _ ht houtcome
    _ = ((∫ t, |blochDot v t| ∂(uniformSpherePrior : Measure Direction)) +
        (∫ t, blochDot v t ∂(uniformSpherePrior : Measure Direction))) +
        outcome * (∫ t, |blochDot v t| * Real.sign (blochDot b t)
          ∂(uniformSpherePrior : Measure Direction)) +
        outcome * (∫ t, blochDot v t * Real.sign (blochDot b t)
          ∂(uniformSpherePrior : Measure Direction)) := by
      rw [integral_add
        (f := fun t => |blochDot v t| + blochDot v t +
          outcome * (|blochDot v t| * Real.sign (blochDot b t)))
        (g := fun t => outcome * (blochDot v t * Real.sign (blochDot b t)))
        ((hintAbs.add hintDot).add hintAbsSign) hintDotSign,
        integral_add (f := fun t => |blochDot v t| + blochDot v t)
          (g := fun t => outcome * (|blochDot v t| * Real.sign (blochDot b t)))
          (hintAbs.add hintDot) hintAbsSign,
        integral_add hintAbs hintDot, integral_const_mul, integral_const_mul]
    _ = (1 + outcome * blochDot v b) / 2 := by
      rw [habs, integral_blochDot, integral_abs_blochDot_sign,
        integral_blochDot_sign_of_coordinates v b hmom]
      ring

noncomputable def positiveTieSign (r : ℝ) : ℝ := if 0 ≤ r then 1 else -1

lemma positiveTieSign_eq_realSign {r : ℝ} (hr : r ≠ 0) :
    positiveTieSign r = Real.sign r := by
  rcases hr.lt_or_gt with hn | hp
  · rw [positiveTieSign, if_neg (not_le_of_gt hn), Real.sign_of_neg hn]
  · rw [positiveTieSign, if_pos hp.le, Real.sign_of_pos hp]

/-- The exact same law permits assigning a positive outcome at ties, because
the actual zero-set nullity is a visible hypothesis. -/
theorem steering_test_law_positive_tie (v b : Direction)
    (outcome : ℝ) (houtcome : outcome = 1 ∨ outcome = -1)
    (habs : (∫ t, |blochDot v t|
      ∂(uniformSpherePrior : Measure Direction)) = (1 / 2 : ℝ))
    (hmom : ∀ i : Fin 3,
      (∫ t, t.1 i * Real.sign (blochDot b t)
        ∂(uniformSpherePrior : Measure Direction)) = b.1 i / 2)
    (hzero : (uniformSpherePrior : Measure Direction) {t | blochDot b t = 0} = 0) :
    (∫ t, (if positiveTieSign (blochDot b t) = outcome
      then 4 * max (blochDot v t) 0 else 0)
        ∂(uniformSpherePrior : Measure Direction)) =
      (1 + outcome * blochDot v b) / 2 := by
  have hne : ∀ᵐ t ∂(uniformSpherePrior : Measure Direction), blochDot b t ≠ 0 := by
    rw [ae_iff]
    simpa only [not_not] using hzero
  have he : (∫ t, (if positiveTieSign (blochDot b t) = outcome
      then 4 * max (blochDot v t) 0 else 0)
        ∂(uniformSpherePrior : Measure Direction)) =
      ∫ t, (if Real.sign (blochDot b t) = outcome
        then 4 * max (blochDot v t) 0 else 0)
          ∂(uniformSpherePrior : Measure Direction) := by
    apply integral_congr_ae
    filter_upwards [hne] with t ht
    rw [positiveTieSign_eq_realSign ht]
  rw [he]
  exact steering_test_law_of_projection_moments v b outcome houtcome habs hmom hzero

end FinitePR.Sphere

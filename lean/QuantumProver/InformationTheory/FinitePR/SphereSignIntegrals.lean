import QuantumProver.InformationTheory.FinitePR.SpherePrior
import QuantumProver.InformationTheory.FinitePR.LongitudeHalfShift
import Mathlib

/-! Actual antipodal symmetry and axial sign integrals for the sphere-chart prior.
No arbitrary rotational invariance or projection identity is assumed here. -/

namespace FinitePR.Sphere

open MeasureTheory Set
open scoped BigOperators unitInterval

noncomputable def antipodalDirection (t : Direction) : Direction :=
  ⟨fun i => -t.1 i, by simpa using t.property⟩

noncomputable def axialHalfTurn (t : Direction) : Direction :=
  ⟨![-t.1 0, -t.1 1, t.1 2], by
    simpa [Fin.sum_univ_three] using t.property⟩

lemma continuous_antipodalDirection : Continuous antipodalDirection := by
  apply Continuous.subtype_mk
  exact continuous_pi fun i => ((continuous_apply i).comp continuous_subtype_val).neg

lemma continuous_axialHalfTurn : Continuous axialHalfTurn := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  fin_cases i
  · exact ((continuous_apply (0 : Fin 3)).comp continuous_subtype_val).neg
  · exact ((continuous_apply (1 : Fin 3)).comp continuous_subtype_val).neg
  · change Continuous (fun t : Direction => t.1 2)
    exact (continuous_apply (2 : Fin 3)).comp continuous_subtype_val

lemma radius_uniformHeight_symm (u : I) :
    radius (uniformHeight (unitInterval.symm u)) = radius (uniformHeight u) := by
  dsimp [radius, uniformHeight, unitInterval.symm]
  congr 1
  ring

lemma uniformSphereSample_antipodal (p : I × I) :
    uniformSphereSample (unitInterval.symm p.1, longitudeHalfShift p.2) =
      antipodalDirection (uniformSphereSample p) := by
  apply Subtype.ext
  funext i
  fin_cases i
  · change radius (uniformHeight (unitInterval.symm p.1)) *
      Real.cos (-Real.pi + 2 * Real.pi * (longitudeHalfShift p.2 : ℝ)) =
      -(radius (uniformHeight p.1) * Real.cos (-Real.pi + 2 * Real.pi * (p.2 : ℝ)))
    rw [radius_uniformHeight_symm, cos_longitudeHalfShift]
    ring
  · change radius (uniformHeight (unitInterval.symm p.1)) *
      Real.sin (-Real.pi + 2 * Real.pi * (longitudeHalfShift p.2 : ℝ)) =
      -(radius (uniformHeight p.1) * Real.sin (-Real.pi + 2 * Real.pi * (p.2 : ℝ)))
    rw [radius_uniformHeight_symm, sin_longitudeHalfShift]
    ring
  · change 2 * (unitInterval.symm p.1 : ℝ) - 1 = -(2 * (p.1 : ℝ) - 1)
    simp only [unitInterval.symm]
    ring

lemma uniformSphereSample_axialHalfTurn (p : I × I) :
    uniformSphereSample (p.1, longitudeHalfShift p.2) =
      axialHalfTurn (uniformSphereSample p) := by
  apply Subtype.ext
  funext i
  fin_cases i
  · change radius (uniformHeight p.1) *
      Real.cos (-Real.pi + 2 * Real.pi * (longitudeHalfShift p.2 : ℝ)) =
      -(radius (uniformHeight p.1) * Real.cos (-Real.pi + 2 * Real.pi * (p.2 : ℝ)))
    rw [cos_longitudeHalfShift]
    ring
  · change radius (uniformHeight p.1) *
      Real.sin (-Real.pi + 2 * Real.pi * (longitudeHalfShift p.2 : ℝ)) =
      -(radius (uniformHeight p.1) * Real.sin (-Real.pi + 2 * Real.pi * (p.2 : ℝ)))
    rw [sin_longitudeHalfShift]
    ring
  · rfl

/-- Actual antipodal invariance of the exact chart pushforward. -/
theorem prior_antipodal : MeasurePreserving antipodalDirection
    (uniformSpherePrior : Measure Direction) (uniformSpherePrior : Measure Direction) := by
  have hsample : MeasurePreserving uniformSphereSample
      ((volume : Measure I).prod (volume : Measure I))
      (uniformSpherePrior : Measure Direction) :=
    ⟨continuous_uniformSphereSample.measurable, rfl⟩
  exact hsample.of_semiconj
    (unitInterval.measurePreserving_symm.prod measurePreserving_longitudeHalfShift)
    uniformSphereSample_antipodal continuous_antipodalDirection.measurable

/-- The explicit longitude half-turn also preserves the actual prior. -/
theorem prior_axialHalfTurn : MeasurePreserving axialHalfTurn
    (uniformSpherePrior : Measure Direction) (uniformSpherePrior : Measure Direction) := by
  have hsample : MeasurePreserving uniformSphereSample
      ((volume : Measure I).prod (volume : Measure I))
      (uniformSpherePrior : Measure Direction) :=
    ⟨continuous_uniformSphereSample.measurable, rfl⟩
  exact hsample.of_semiconj
    ((MeasurePreserving.id (volume : Measure I)).prod measurePreserving_longitudeHalfShift)
    uniformSphereSample_axialHalfTurn continuous_axialHalfTurn.measurable

lemma measurable_realSign : Measurable Real.sign := by
  unfold Real.sign
  exact Measurable.ite measurableSet_Iio measurable_const
    (Measurable.ite measurableSet_Ioi measurable_const measurable_const)

lemma measurable_coordinate (i : Fin 3) : Measurable (fun t : Direction => t.1 i) :=
  ((continuous_apply i).comp continuous_subtype_val).measurable

noncomputable def midpoint : I := ⟨(1 / 2 : ℝ), by constructor <;> norm_num⟩

theorem uniformSpherePrior_height_zero :
    (uniformSpherePrior : Measure Direction) {t | t.1 2 = 0} = 0 := by
  change (((volume : Measure I).prod (volume : Measure I)).map uniformSphereSample)
    {t : Direction | t.1 2 = 0} = 0
  rw [Measure.map_apply continuous_uniformSphereSample.measurable
    (measurableSet_eq_fun (measurable_coordinate 2) measurable_const)]
  have he : uniformSphereSample ⁻¹' {t : Direction | t.1 2 = 0} =
      ({midpoint} ×ˢ (univ : Set I)) := by
    ext p
    change (2 * (p.1 : ℝ) - 1 = 0) ↔ (p.1 = midpoint ∧ True)
    simp only [and_true]
    constructor
    · intro hp
      apply Subtype.ext
      change (p.1 : ℝ) = 1 / 2
      linarith
    · intro hp
      rw [hp]
      norm_num [midpoint]
  rw [he, Measure.prod_prod]
  simp

theorem uniformSpherePrior_height_pos :
    (uniformSpherePrior : Measure Direction) {t | 0 < t.1 2} =
      ENNReal.ofReal (1 / 2 : ℝ) := by
  change (((volume : Measure I).prod (volume : Measure I)).map uniformSphereSample)
    {t : Direction | 0 < t.1 2} = _
  rw [Measure.map_apply continuous_uniformSphereSample.measurable
    (measurableSet_lt measurable_const (measurable_coordinate 2))]
  have he : uniformSphereSample ⁻¹' {t : Direction | 0 < t.1 2} =
      (Ioi midpoint ×ˢ (univ : Set I)) := by
    ext p
    change (0 < 2 * (p.1 : ℝ) - 1) ↔ ((1 / 2 : ℝ) < (p.1 : ℝ) ∧ True)
    simp only [and_true]
    constructor <;> intro hp <;> linarith
  rw [he, Measure.prod_prod, unitInterval.volume_Ioi]
  norm_num [midpoint]

theorem uniformSpherePrior_height_neg :
    (uniformSpherePrior : Measure Direction) {t | t.1 2 < 0} =
      ENNReal.ofReal (1 / 2 : ℝ) := by
  change (((volume : Measure I).prod (volume : Measure I)).map uniformSphereSample)
    {t : Direction | t.1 2 < 0} = _
  rw [Measure.map_apply continuous_uniformSphereSample.measurable
    (measurableSet_lt (measurable_coordinate 2) measurable_const)]
  have he : uniformSphereSample ⁻¹' {t : Direction | t.1 2 < 0} =
      (Iio midpoint ×ˢ (univ : Set I)) := by
    ext p
    change (2 * (p.1 : ℝ) - 1 < 0) ↔ ((p.1 : ℝ) < (1 / 2 : ℝ) ∧ True)
    simp only [and_true]
    constructor <;> intro hp <;> linarith
  rw [he, Measure.prod_prod, unitInterval.volume_Iio]
  norm_num [midpoint]

lemma integral_invariant (R : Direction → Direction)
    (hR : MeasurePreserving R (uniformSpherePrior : Measure Direction)
      (uniformSpherePrior : Measure Direction)) (f : Direction → ℝ) (hf : Measurable f) :
    (∫ t, f (R t) ∂(uniformSpherePrior : Measure Direction)) =
      ∫ t, f t ∂(uniformSpherePrior : Measure Direction) := by
  have hi := integral_map (μ := (uniformSpherePrior : Measure Direction))
    hR.measurable.aemeasurable hf.aestronglyMeasurable
  rw [hR.map_eq] at hi
  exact hi.symm

lemma integral_zero_of_neg (R : Direction → Direction)
    (hR : MeasurePreserving R (uniformSpherePrior : Measure Direction)
      (uniformSpherePrior : Measure Direction)) (f : Direction → ℝ) (hf : Measurable f)
    (hneg : ∀ t, f (R t) = -f t) : (∫ t, f t ∂(uniformSpherePrior : Measure Direction)) = 0 := by
  have hi := integral_invariant R hR f hf
  have he : (fun t => f (R t)) = fun t => -f t := funext hneg
  rw [he, integral_neg] at hi
  linarith

theorem integral_antipodal_odd (f : Direction → ℝ) (hf : Measurable f)
    (hodd : ∀ t, f (antipodalDirection t) = -f t) :
    (∫ t, f t ∂(uniformSpherePrior : Measure Direction)) = 0 :=
  integral_zero_of_neg antipodalDirection prior_antipodal f hf hodd

lemma coordinate_abs_le_one (t : Direction) (i : Fin 3) : |t.1 i| ≤ 1 := by
  have hs : (t.1 i) ^ 2 ≤ ∑ j, (t.1 j) ^ 2 :=
    Finset.single_le_sum (fun j _ => sq_nonneg (t.1 j)) (Finset.mem_univ i)
  rw [t.property] at hs
  exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩

lemma integrable_bounded (f : Direction → ℝ) (hf : Measurable f)
    (C : ℝ) (hbound : ∀ t, |f t| ≤ C) :
    Integrable f (uniformSpherePrior : Measure Direction) := by
  apply (integrable_const C).mono' hf.aestronglyMeasurable
  exact Filter.Eventually.of_forall fun t => by
    simpa only [Real.norm_eq_abs] using hbound t

lemma realSign_mul_self (r : ℝ) : Real.sign r * r = |r| := by
  rcases lt_trichotomy r 0 with hr | hr | hr
  · rw [Real.sign_of_neg hr, abs_of_neg hr]
    ring
  · subst r
    simp
  · rw [Real.sign_of_pos hr, abs_of_pos hr, one_mul]

lemma positivePart_bound {r : ℝ} (hr : |r| ≤ 1) : |max r 0| ≤ 1 := by
  rw [abs_of_nonneg (le_max_right r 0)]
  exact max_le ((le_abs_self r).trans hr) zero_le_one

lemma abs_positiveParts (r : ℝ) : |r| = max r 0 + max (-r) 0 := by
  by_cases hr : 0 ≤ r
  · rw [abs_of_nonneg hr, max_eq_left hr, max_eq_right (neg_nonpos.mpr hr), add_zero]
  · have hr' : r ≤ 0 := (lt_of_not_ge hr).le
    rw [abs_of_nonpos hr', max_eq_right hr', max_eq_left (neg_nonneg.mpr hr'), zero_add]

theorem integral_height_sign :
    (∫ t, Real.sign (t.1 2) ∂(uniformSpherePrior : Measure Direction)) = 0 := by
  apply integral_antipodal_odd _ (measurable_realSign.comp (measurable_coordinate 2))
  intro t
  exact Real.sign_neg

theorem integral_height_sign_height :
    (∫ t, Real.sign (t.1 2) * t.1 2 ∂(uniformSpherePrior : Measure Direction)) =
      (1 / 2 : ℝ) := by
  have hposm : Measurable (fun t : Direction => max (t.1 2) 0) :=
    (measurable_coordinate 2).max measurable_const
  have hnegm : Measurable (fun t : Direction => max (-t.1 2) 0) :=
    (measurable_coordinate 2).neg.max measurable_const
  have hpos := integrable_bounded (fun t : Direction => max (t.1 2) 0) hposm 1
    (fun t => positivePart_bound (coordinate_abs_le_one t 2))
  have hneg := integrable_bounded (fun t : Direction => max (-t.1 2) 0) hnegm 1
    (fun t => positivePart_bound (by simpa using coordinate_abs_le_one t 2))
  have he : (∫ t, max (-t.1 2) 0 ∂(uniformSpherePrior : Measure Direction)) =
      ∫ t, max (t.1 2) 0 ∂(uniformSpherePrior : Measure Direction) :=
    integral_invariant antipodalDirection prior_antipodal _ hposm
  calc
    (∫ t, Real.sign (t.1 2) * t.1 2 ∂(uniformSpherePrior : Measure Direction)) =
        ∫ t, |t.1 2| ∂(uniformSpherePrior : Measure Direction) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun t => realSign_mul_self (t.1 2)
    _ = ∫ t, max (t.1 2) 0 + max (-t.1 2) 0 ∂(uniformSpherePrior : Measure Direction) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun t => abs_positiveParts (t.1 2)
    _ = (∫ t, max (t.1 2) 0 ∂(uniformSpherePrior : Measure Direction)) +
        ∫ t, max (-t.1 2) 0 ∂(uniformSpherePrior : Measure Direction) := integral_add hpos hneg
    _ = 1 / 2 := by rw [he, uniformSpherePrior_positivePart_height]; norm_num

theorem integral_height_sign_transverse (i : Fin 3) (hi : i ≠ 2) :
    (∫ t, Real.sign (t.1 2) * t.1 i ∂(uniformSpherePrior : Measure Direction)) = 0 := by
  apply integral_zero_of_neg axialHalfTurn prior_axialHalfTurn _
    ((measurable_realSign.comp (measurable_coordinate 2)).mul (measurable_coordinate i))
  intro t
  fin_cases i
  · change Real.sign (t.1 2) * (-t.1 0) = -(Real.sign (t.1 2) * t.1 0)
    ring
  · change Real.sign (t.1 2) * (-t.1 1) = -(Real.sign (t.1 2) * t.1 1)
    ring
  · exact (hi rfl).elim

theorem axial_signed_moment (i : Fin 3) :
    (∫ t, Real.sign (t.1 2) * t.1 i ∂(uniformSpherePrior : Measure Direction)) =
      if i = 2 then (1 / 2 : ℝ) else 0 := by
  by_cases hi : i = 2
  · subst i
    simpa using integral_height_sign_height
  · simpa [hi] using integral_height_sign_transverse i hi

lemma realSign_eq_one_iff (r : ℝ) : Real.sign r = 1 ↔ 0 < r := by
  rcases lt_trichotomy r 0 with hn | rfl | hp
  · norm_num [Real.sign_of_neg hn, hn.not_gt]
  · norm_num
  · simp [Real.sign_of_pos hp, hp]

lemma realSign_eq_neg_one_iff (r : ℝ) : Real.sign r = -1 ↔ r < 0 := by
  rcases lt_trichotomy r 0 with hn | rfl | hp
  · simp [Real.sign_of_neg hn, hn]
  · norm_num
  · norm_num [Real.sign_of_pos hp, not_lt_of_ge hp.le]

/-- Both actual axial sign outcomes have probability one half; zero is null. -/
theorem axial_sign_halfmass (outcome : ℝ) (houtcome : outcome = 1 ∨ outcome = -1) :
    (uniformSpherePrior : Measure Direction).real {t | Real.sign (t.1 2) = outcome} =
      (1 / 2 : ℝ) := by
  rcases houtcome with rfl | rfl
  · have he : {t : Direction | Real.sign (t.1 2) = 1} = {t | 0 < t.1 2} := by
      ext t
      exact realSign_eq_one_iff (t.1 2)
    rw [he, measureReal_def, uniformSpherePrior_height_pos]
    norm_num
  · have he : {t : Direction | Real.sign (t.1 2) = -1} = {t | t.1 2 < 0} := by
      ext t
      exact realSign_eq_neg_one_iff (t.1 2)
    rw [he, measureReal_def, uniformSpherePrior_height_neg]
    norm_num

end FinitePR.Sphere

import QuantumProver.InformationTheory.FinitePR.SphereSignIntegrals
import QuantumProver.InformationTheory.FinitePR.Lemmas
import Mathlib

/-! Exact deterministic pair symmetrization on the actual chart prior.
Exceptional sign planes are represented by explicit a.e. flip hypotheses.
The density need only be integrable and a.e. even; no fairness is assumed. -/

namespace FinitePR.Sphere.Symmetrization

open MeasureTheory Set
open scoped BigOperators unitInterval

lemma bit_add_one_twice (u : Bit) : (u + 1) + 1 = u := by
  simp only [add_assoc, ZModModule.add_self, add_zero]

lemma bit_add_one_eq_iff (u a : Bit) : u + 1 = a ↔ u = a + 1 := by
  constructor
  · intro h
    have he := congrArg (fun z : Bit => z + 1) h
    simpa only [bit_add_one_twice] using he
  · intro h
    rw [h, bit_add_one_twice]

lemma bit_ne_add_one (u : Bit) : u ≠ u + 1 := by
  intro h
  have he : u + 0 = u + 1 := by simpa only [add_zero] using h
  exact zero_ne_one (add_left_cancel he)

lemma bit_add_one_ne (u : Bit) : u + 1 ≠ u := Ne.symm (bit_ne_add_one u)

lemma bit_eq_or_add_one (u a : Bit) : u = a ∨ u = a + 1 := by
  rcases bit_cases (u - a) with h | h
  · exact Or.inl (sub_eq_zero.mp h)
  · right
    simpa only [add_comm] using sub_eq_iff_eq_add.mp h

lemma pair_indicator_add_flip (u v a b : Bit) (r : ℝ) :
    (if u = a ∧ v = b then r else 0) +
      (if u = a + 1 ∧ v = b + 1 then r else 0) =
        if a + b = u + v then r else 0 := by
  classical
  rcases bit_eq_or_add_one u a with hu | hu <;>
    rcases bit_eq_or_add_one v b with hv | hv
  · rw [hu, hv]
    simp [bit_ne_add_one]
  · rw [hu, hv]
    have hp : a + b ≠ a + (b + 1) := by
      intro h
      exact bit_ne_add_one b (add_left_cancel h)
    simp [bit_ne_add_one, bit_add_one_ne, hp]
  · rw [hu, hv]
    have hp : a + b ≠ (a + 1) + b := by
      intro h
      exact bit_ne_add_one a (add_right_cancel h)
    simp [bit_ne_add_one, bit_add_one_ne, hp]
  · rw [hu, hv]
    have hp : (a + 1) + (b + 1) = a + b := by
      calc
        (a + 1) + (b + 1) = a + b + (1 + 1) := by ring
        _ = a + b := by simp only [ZModModule.add_self, add_zero]
    simp [bit_add_one_ne, hp]

noncomputable def pairDensity (f : Direction → ℝ) (d e : Direction → Bit)
    (a b : Bit) (t : Direction) : ℝ := if d t = a ∧ e t = b then f t else 0

lemma pairSet_measurable (d e : Direction → Bit) (hd : Measurable d) (he : Measurable e)
    (a b : Bit) : MeasurableSet {t | d t = a ∧ e t = b} :=
  (measurableSet_eq_fun hd measurable_const).inter
    (measurableSet_eq_fun he measurable_const)

lemma integrable_pairDensity (f : Direction → ℝ)
    (hf : Integrable f (uniformSpherePrior : Measure Direction))
    (d e : Direction → Bit) (hd : Measurable d) (he : Measurable e) (a b : Bit) :
    Integrable (pairDensity f d e a b) (uniformSpherePrior : Measure Direction) := by
  classical
  have heq : ({t | d t = a ∧ e t = b}.indicator f) = pairDensity f d e a b := by
    funext t
    rw [Set.indicator_apply]
    rfl
  rw [← heq]
  exact hf.indicator (pairSet_measurable d e hd he a b)

lemma pair_integral_eq_flipped (f : Direction → ℝ)
    (hf : Integrable f (uniformSpherePrior : Measure Direction))
    (heven : ∀ᵐ t ∂(uniformSpherePrior : Measure Direction),
      f (antipodalDirection t) = f t)
    (d e : Direction → Bit) (hd : Measurable d) (he : Measurable e)
    (hdflip : ∀ᵐ t ∂(uniformSpherePrior : Measure Direction),
      d (antipodalDirection t) = d t + 1)
    (heflip : ∀ᵐ t ∂(uniformSpherePrior : Measure Direction),
      e (antipodalDirection t) = e t + 1) (a b : Bit) :
    (∫ t, pairDensity f d e a b t ∂(uniformSpherePrior : Measure Direction)) =
      ∫ t, pairDensity f d e (a + 1) (b + 1) t
        ∂(uniformSpherePrior : Measure Direction) := by
  have hint := integrable_pairDensity f hf d e hd he a b
  have hmeas : AEStronglyMeasurable (pairDensity f d e a b)
      ((uniformSpherePrior : Measure Direction).map antipodalDirection) := by
    rw [prior_antipodal.map_eq]
    exact hint.aestronglyMeasurable
  have hi := integral_map (μ := (uniformSpherePrior : Measure Direction))
    prior_antipodal.measurable.aemeasurable hmeas
  rw [prior_antipodal.map_eq] at hi
  calc
    (∫ t, pairDensity f d e a b t ∂(uniformSpherePrior : Measure Direction)) =
        ∫ t, pairDensity f d e a b (antipodalDirection t)
          ∂(uniformSpherePrior : Measure Direction) := hi
    _ = ∫ t, pairDensity f d e (a + 1) (b + 1) t
        ∂(uniformSpherePrior : Measure Direction) := by
      apply integral_congr_ae
      filter_upwards [heven, hdflip, heflip] with t ht hdt het
      unfold pairDensity
      rw [ht, hdt, het]
      simp only [bit_add_one_eq_iff]

/-- Exact joint-pair law, including a.e. density evenness and sign flips. -/
theorem deterministic_pair_eq_half_parity_of_ae_even (f : Direction → ℝ)
    (hf : Integrable f (uniformSpherePrior : Measure Direction))
    (heven : ∀ᵐ t ∂(uniformSpherePrior : Measure Direction),
      f (antipodalDirection t) = f t)
    (d e : Direction → Bit) (hd : Measurable d) (he : Measurable e)
    (hdflip : ∀ᵐ t ∂(uniformSpherePrior : Measure Direction),
      d (antipodalDirection t) = d t + 1)
    (heflip : ∀ᵐ t ∂(uniformSpherePrior : Measure Direction),
      e (antipodalDirection t) = e t + 1) (a b : Bit) :
    (∫ t, (if d t = a ∧ e t = b then f t else 0)
      ∂(uniformSpherePrior : Measure Direction)) =
      (1 / 2 : ℝ) * ∫ t, (if a + b = d t + e t then f t else 0)
        ∂(uniformSpherePrior : Measure Direction) := by
  have hflip := pair_integral_eq_flipped f hf heven d e hd he hdflip heflip a b
  have hsum : (∫ t, (if a + b = d t + e t then f t else 0)
      ∂(uniformSpherePrior : Measure Direction)) =
      (∫ t, pairDensity f d e a b t ∂(uniformSpherePrior : Measure Direction)) +
      ∫ t, pairDensity f d e (a + 1) (b + 1) t
        ∂(uniformSpherePrior : Measure Direction) := by
    calc
      _ = ∫ t, pairDensity f d e a b t + pairDensity f d e (a + 1) (b + 1) t
          ∂(uniformSpherePrior : Measure Direction) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun t =>
          (pair_indicator_add_flip (d t) (e t) a b (f t)).symm
      _ = _ := integral_add (integrable_pairDensity f hf d e hd he a b)
        (integrable_pairDensity f hf d e hd he (a + 1) (b + 1))
  change (∫ t, pairDensity f d e a b t ∂(uniformSpherePrior : Measure Direction)) = _
  rw [← hflip] at hsum
  linarith

/-- Pointwise evenness wrapper, matching the actual residual density interface. -/
theorem deterministic_pair_eq_half_parity (f : Direction → ℝ)
    (hf : Integrable f (uniformSpherePrior : Measure Direction))
    (heven : ∀ t, f (antipodalDirection t) = f t)
    (d e : Direction → Bit) (hd : Measurable d) (he : Measurable e)
    (hdflip : ∀ᵐ t ∂(uniformSpherePrior : Measure Direction),
      d (antipodalDirection t) = d t + 1)
    (heflip : ∀ᵐ t ∂(uniformSpherePrior : Measure Direction),
      e (antipodalDirection t) = e t + 1) (a b : Bit) :
    (∫ t, (if d t = a ∧ e t = b then f t else 0)
      ∂(uniformSpherePrior : Measure Direction)) =
      (1 / 2 : ℝ) * ∫ t, (if a + b = d t + e t then f t else 0)
        ∂(uniformSpherePrior : Measure Direction) :=
  deterministic_pair_eq_half_parity_of_ae_even f hf (Filter.Eventually.of_forall heven)
    d e hd he hdflip heflip a b

/-- The same equality as an integral of the literal fair parity-mask kernel. -/
theorem deterministic_pair_eq_fair_parity_integral (f : Direction → ℝ)
    (hf : Integrable f (uniformSpherePrior : Measure Direction))
    (heven : ∀ t, f (antipodalDirection t) = f t)
    (d e : Direction → Bit) (hd : Measurable d) (he : Measurable e)
    (hdflip : ∀ᵐ t ∂(uniformSpherePrior : Measure Direction),
      d (antipodalDirection t) = d t + 1)
    (heflip : ∀ᵐ t ∂(uniformSpherePrior : Measure Direction),
      e (antipodalDirection t) = e t + 1) (a b : Bit) :
    (∫ t, (if d t = a ∧ e t = b then f t else 0)
      ∂(uniformSpherePrior : Measure Direction)) =
      ∫ t, (if a + b = d t + e t then (1 / 2 : ℝ) else 0) * f t
        ∂(uniformSpherePrior : Measure Direction) := by
  rw [deterministic_pair_eq_half_parity f hf heven d e hd he hdflip heflip a b,
    ← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun t => by
    change (1 / 2 : ℝ) * (if a + b = d t + e t then f t else 0) =
      (if a + b = d t + e t then (1 / 2 : ℝ) else 0) * f t
    split_ifs <;> simp

end FinitePR.Sphere.Symmetrization

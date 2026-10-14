import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section
open scoped BigOperators

namespace QuantumProver.DepolarizingSquashedEntanglement.BCYThreeRegions

variable {J : Type*} [Fintype J]

def upperMass (n : ℝ) (w x y : J → ℝ) (t : ℝ) : ℝ := by
  classical
  exact ∑ j, if Real.exp (n * t) * y j ≤ x j then w j * x j else 0

theorem upperMass_nonneg (n : ℝ) (w x y : J → ℝ) (t : ℝ)
    (hw : ∀ j, 0 ≤ w j) (hx : ∀ j, 0 ≤ x j) :
    0 ≤ upperMass n w x y t := by
  classical
  apply Finset.sum_nonneg
  intro j _
  split_ifs <;> first | exact mul_nonneg (hw j) (hx j) | exact le_rfl

theorem upperMass_le_one (n : ℝ) (w x y : J → ℝ) (t : ℝ)
    (hw : ∀ j, 0 ≤ w j) (hx : ∀ j, 0 ≤ x j)
    (hmass : ∑ j, w j * x j = 1) : upperMass n w x y t ≤ 1 := by
  classical
  rw [← hmass]
  apply Finset.sum_le_sum
  intro j _
  split_ifs <;> first | exact le_rfl | exact mul_nonneg (hw j) (hx j)

theorem upperMass_antitone (n : ℝ) (w x y : J → ℝ) (hn : 0 ≤ n)
    (hw : ∀ j, 0 ≤ w j) (hx : ∀ j, 0 ≤ x j) (hy : ∀ j, 0 ≤ y j) :
    Antitone (upperMass n w x y) := by
  classical
  intro lower upper horder
  apply Finset.sum_le_sum
  intro j _
  have hmono : Real.exp (n * lower) * y j ≤ Real.exp (n * upper) * y j :=
    mul_le_mul_of_nonneg_right
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left horder hn)) (hy j)
  by_cases hu : Real.exp (n * upper) * y j ≤ x j
  · simp only [hu, hmono.trans hu, ite_true]
    exact le_rfl
  · simp only [hu, ite_false]
    split_ifs <;> first | exact mul_nonneg (hw j) (hx j) | exact le_rfl

theorem three_region_pointwise_bound {n kappa lower upper x y : ℝ}
    (hn : 1 ≤ n) (horder : lower ≤ upper) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hy : Real.exp (-2 * n * kappa) ≤ y) :
    x * (Real.log x - Real.log y) / n ≤
      lower * x + (upper - lower) *
        (if Real.exp (n * lower) * y ≤ x then x else 0) +
      (2 * kappa - upper) * (if Real.exp (n * upper) * y ≤ x then x else 0) := by
  classical
  by_cases hxz : x = 0
  · simp only [hxz, zero_mul, zero_div, mul_zero, ite_self, add_zero, le_refl]
  · have hx : 0 < x := lt_of_le_of_ne hx0 (Ne.symm hxz)
    have hy0 : 0 < y := (Real.exp_pos _).trans_le hy
    have hn0 : 0 < n := zero_lt_one.trans_le hn
    have hlogy : -2 * n * kappa ≤ Real.log y :=
      (Real.le_log_iff_exp_le hy0).mpr hy
    have hlogx : Real.log x ≤ 0 := Real.log_nonpos hx0 hx1
    have hcap : (Real.log x - Real.log y) / n ≤ 2 * kappa := by
      apply (div_le_iff₀ hn0).mpr
      nlinarith
    have hlt (t : ℝ) (ht : ¬ Real.exp (n * t) * y ≤ x) :
        (Real.log x - Real.log y) / n ≤ t := by
      have h := Real.log_lt_log hx (lt_of_not_ge ht)
      rw [Real.log_mul (Real.exp_pos _).ne' hy0.ne', Real.log_exp] at h
      apply (div_le_iff₀ hn0).mpr
      linarith
    by_cases hu : Real.exp (n * upper) * y ≤ x
    · have hl : Real.exp (n * lower) * y ≤ x :=
        (mul_le_mul_of_nonneg_right
          (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left horder hn0.le)) hy0.le).trans hu
      simp only [hu, hl, ite_true]
      calc
        _ = x * ((Real.log x - Real.log y) / n) := by ring
        _ ≤ x * (2 * kappa) := mul_le_mul_of_nonneg_left hcap hx0
        _ = _ := by ring
    · by_cases hl : Real.exp (n * lower) * y ≤ x
      · simp only [hu, hl, ite_true, ite_false, mul_zero, add_zero]
        calc
          _ = x * ((Real.log x - Real.log y) / n) := by ring
          _ ≤ x * upper := mul_le_mul_of_nonneg_left (hlt upper hu) hx0
          _ = _ := by ring
      · simp only [hu, hl, ite_false, mul_zero, add_zero]
        calc
          _ = x * ((Real.log x - Real.log y) / n) := by ring
          _ ≤ x * lower := mul_le_mul_of_nonneg_left (hlt lower hl) hx0
          _ = _ := by ring

theorem sum_weighted_threshold_scale (n : ℝ) (w x y : J → ℝ) (t c : ℝ) :
    (∑ j, w j * (c * (if Real.exp (n * t) * y j ≤ x j then x j else 0))) =
      c * upperMass n w x y t := by
  classical
  rw [upperMass, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> ring

theorem weighted_log_div_le_three_regions (n kappa lower upper : ℝ)
    (w x y : J → ℝ) (hn : 1 ≤ n) (horder : lower ≤ upper)
    (hw : ∀ j, 0 ≤ w j) (hx0 : ∀ j, 0 ≤ x j) (hx1 : ∀ j, x j ≤ 1)
    (hy : ∀ j, Real.exp (-2 * n * kappa) ≤ y j)
    (hmass : ∑ j, w j * x j = 1) :
    (∑ j, w j * x j * (Real.log (x j) - Real.log (y j))) / n ≤
      lower + (upper - lower) * upperMass n w x y lower +
        (2 * kappa - upper) * upperMass n w x y upper := by
  classical
  calc
    _ = ∑ j, w j * (x j * (Real.log (x j) - Real.log (y j)) / n) := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ ≤ ∑ j, w j * (lower * x j + (upper - lower) *
        (if Real.exp (n * lower) * y j ≤ x j then x j else 0) +
        (2 * kappa - upper) * (if Real.exp (n * upper) * y j ≤ x j then x j else 0)) := by
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_left
        (three_region_pointwise_bound hn horder (hx0 j) (hx1 j) (hy j)) (hw j)
    _ = _ := by
      simp only [mul_add, Finset.sum_add_distrib]
      rw [sum_weighted_threshold_scale, sum_weighted_threshold_scale]
      have hc : (∑ j, w j * (lower * x j)) = lower := by
        calc
          _ = lower * ∑ j, w j * x j := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j _
            ring
          _ = lower := by rw [hmass, mul_one]
      rw [hc]

theorem log_div_le_three_regions (n kappa lower upper : ℝ) (x y : J → ℝ)
    (hn : 1 ≤ n) (horder : lower ≤ upper)
    (hx0 : ∀ j, 0 ≤ x j) (hx1 : ∀ j, x j ≤ 1)
    (hy : ∀ j, Real.exp (-2 * n * kappa) ≤ y j) (hmass : ∑ j, x j = 1) :
    (∑ j, x j * (Real.log (x j) - Real.log (y j))) / n ≤
      lower + (upper - lower) * upperMass n (fun _ => 1) x y lower +
        (2 * kappa - upper) * upperMass n (fun _ => 1) x y upper := by
  simpa only [one_mul] using weighted_log_div_le_three_regions n kappa lower upper
    (fun _ => 1) x y hn horder (fun _ => zero_le_one) hx0 hx1 hy
    (by simpa only [one_mul] using hmass)

def epsilon0 (epsilon eta Rprime Re : ℝ) : ℝ :=
  (epsilon - eta) / (1 - epsilon) * (Rprime - Re)

theorem epsilon0_nonneg {epsilon eta Rprime Re : ℝ}
    (he : epsilon < 1) (heta : eta ≤ epsilon) (hR : Re ≤ Rprime) :
    0 ≤ epsilon0 epsilon eta Rprime Re :=
  mul_nonneg (div_nonneg (sub_nonneg.mpr heta) (sub_pos.mpr he).le) (sub_nonneg.mpr hR)

theorem epsilon0_rate_identity {epsilon eta Rprime Re : ℝ} (he : epsilon ≠ 1) :
    Re + (1 - epsilon) * (Rprime + epsilon0 epsilon eta Rprime Re - Re) =
      Re + (1 - eta) * (Rprime - Re) := by
  unfold epsilon0
  field_simp [sub_ne_zero.mpr (Ne.symm he)]
  ring

end QuantumProver.DepolarizingSquashedEntanglement.BCYThreeRegions

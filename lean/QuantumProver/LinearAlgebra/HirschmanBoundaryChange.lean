import Mathlib

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace QuantumProver.HirschmanBoundaryChange

def boundaryAngle (θ x : ℝ) : ℝ :=
  Real.pi + 2 * Real.arctan
    ((x - Real.cos (Real.pi * θ)) / Real.sin (Real.pi * θ))

def leftAngle (θ t : ℝ) : ℝ := boundaryAngle θ (Real.exp (-Real.pi * t))

def rightAngle (θ t : ℝ) : ℝ := boundaryAngle θ (-Real.exp (-Real.pi * t))

def rawLeftKernel (θ t : ℝ) : ℝ :=
  Real.sin (Real.pi * θ) /
    (2 * (Real.cosh (Real.pi * t) - Real.cos (Real.pi * θ)))

def rawRightKernel (θ t : ℝ) : ℝ :=
  Real.sin (Real.pi * θ) /
    (2 * (Real.cosh (Real.pi * t) + Real.cos (Real.pi * θ)))

def upperBoundaryValue (θ u : ℝ) : ℂ :=
  (Real.cos (Real.pi * θ) : ℂ) +
    Complex.I * (Real.sin (Real.pi * θ) : ℂ) *
      ((1 + Complex.exp ((u : ℂ) * Complex.I)) /
        (1 - Complex.exp ((u : ℂ) * Complex.I)))

def stripBoundaryValue (θ u : ℝ) : ℂ :=
  (-Complex.I) * Complex.log (upperBoundaryValue θ u) / (Real.pi : ℂ)

theorem sin_pi_mul_pos {θ : ℝ} (hθ : θ ∈ Ioo (0 : ℝ) 1) :
    0 < Real.sin (Real.pi * θ) := by
  apply Real.sin_pos_of_pos_of_lt_pi
  · exact mul_pos Real.pi_pos hθ.1
  · nlinarith [Real.pi_pos, hθ.2]

theorem boundaryAngle_mem (θ x : ℝ) :
    boundaryAngle θ x ∈ Ioo (0 : ℝ) (2 * Real.pi) := by
  have h := Real.arctan_mem_Ioo
    ((x - Real.cos (Real.pi * θ)) / Real.sin (Real.pi * θ))
  unfold boundaryAngle
  constructor <;> linarith [h.1, h.2]

theorem strictMono_boundaryAngle {θ : ℝ} (hθ : θ ∈ Ioo (0 : ℝ) 1) :
    StrictMono (boundaryAngle θ) := by
  intro x y hxy
  have hdiv :
      (x - Real.cos (Real.pi * θ)) / Real.sin (Real.pi * θ) <
        (y - Real.cos (Real.pi * θ)) / Real.sin (Real.pi * θ) :=
    (div_lt_div_iff_of_pos_right (sin_pi_mul_pos hθ)).mpr (sub_lt_sub_right hxy _)
  have ha := Real.arctan_strictMono hdiv
  unfold boundaryAngle
  linarith

theorem arctan_cos_div_sin {θ : ℝ} (hθ : θ ∈ Ioo (0 : ℝ) 1) :
    Real.arctan (Real.cos (Real.pi * θ) / Real.sin (Real.pi * θ)) =
      Real.pi / 2 - Real.pi * θ := by
  apply Real.arctan_eq_of_tan_eq
  · simp only [Real.tan_eq_sin_div_cos, Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub]
  · constructor <;> nlinarith [Real.pi_pos, hθ.1, hθ.2]

theorem boundaryAngle_zero {θ : ℝ} (hθ : θ ∈ Ioo (0 : ℝ) 1) :
    boundaryAngle θ 0 = 2 * Real.pi * θ := by
  rw [boundaryAngle, zero_sub, neg_div, Real.arctan_neg, arctan_cos_div_sin hθ]
  ring

theorem range_boundaryAngle {θ : ℝ} (hθ : θ ∈ Ioo (0 : ℝ) 1) :
    range (boundaryAngle θ) = Ioo (0 : ℝ) (2 * Real.pi) := by
  ext u
  constructor
  · rintro ⟨x, rfl⟩
    exact boundaryAngle_mem θ x
  · intro hu
    have hv : (u - Real.pi) / 2 ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
      constructor <;> linarith [hu.1, hu.2]
    rw [← Real.range_arctan] at hv
    obtain ⟨v, hv⟩ := hv
    refine ⟨Real.cos (Real.pi * θ) + Real.sin (Real.pi * θ) * v, ?_⟩
    have hs := (sin_pi_mul_pos hθ).ne'
    have he :
        (Real.cos (Real.pi * θ) + Real.sin (Real.pi * θ) * v -
          Real.cos (Real.pi * θ)) / Real.sin (Real.pi * θ) = v := by
      field_simp [hs]
      ring
    rw [boundaryAngle, he, hv]
    ring

theorem rightAngle_eq (θ t : ℝ) :
    rightAngle θ t = Real.pi - 2 * Real.arctan
      ((Real.exp (-Real.pi * t) + Real.cos (Real.pi * θ)) /
        Real.sin (Real.pi * θ)) := by
  unfold rightAngle boundaryAngle
  rw [show -Real.exp (-Real.pi * t) - Real.cos (Real.pi * θ) =
      -(Real.exp (-Real.pi * t) + Real.cos (Real.pi * θ)) by ring,
    neg_div, Real.arctan_neg]
  ring

theorem strictAnti_leftAngle {θ : ℝ} (hθ : θ ∈ Ioo (0 : ℝ) 1) :
    StrictAnti (leftAngle θ) := by
  intro x y hxy
  apply strictMono_boundaryAngle hθ
  apply Real.exp_lt_exp.mpr
  nlinarith [Real.pi_pos]

theorem strictMono_rightAngle {θ : ℝ} (hθ : θ ∈ Ioo (0 : ℝ) 1) :
    StrictMono (rightAngle θ) := by
  intro x y hxy
  apply strictMono_boundaryAngle hθ
  apply neg_lt_neg
  apply Real.exp_lt_exp.mpr
  nlinarith [Real.pi_pos]

theorem exp_neg_pi_log (x : ℝ) (hx : 0 < x) :
    Real.exp (-Real.pi * (-Real.log x / Real.pi)) = x := by
  have he : -Real.pi * (-Real.log x / Real.pi) = Real.log x := by
    field_simp [Real.pi_ne_zero]
  rw [he, Real.exp_log hx]

theorem range_leftAngle {θ : ℝ} (hθ : θ ∈ Ioo (0 : ℝ) 1) :
    range (leftAngle θ) = Ioo (2 * Real.pi * θ) (2 * Real.pi) := by
  ext u
  constructor
  · rintro ⟨t, rfl⟩
    constructor
    · rw [← boundaryAngle_zero hθ]
      exact strictMono_boundaryAngle hθ (Real.exp_pos _)
    · exact (boundaryAngle_mem θ _).2
  · intro hu
    have hθ0 : 0 < 2 * Real.pi * θ :=
      mul_pos (mul_pos (by norm_num) Real.pi_pos) hθ.1
    have hwhole : u ∈ range (boundaryAngle θ) := by
      rw [range_boundaryAngle hθ]
      exact ⟨hθ0.trans hu.1, hu.2⟩
    obtain ⟨x, hx⟩ := hwhole
    have hx0 : 0 < x := (strictMono_boundaryAngle hθ).lt_iff_lt.mp (by
      rw [boundaryAngle_zero hθ, hx]
      exact hu.1)
    refine ⟨-Real.log x / Real.pi, ?_⟩
    rw [leftAngle, exp_neg_pi_log x hx0, hx]

theorem range_rightAngle {θ : ℝ} (hθ : θ ∈ Ioo (0 : ℝ) 1) :
    range (rightAngle θ) = Ioo (0 : ℝ) (2 * Real.pi * θ) := by
  ext u
  constructor
  · rintro ⟨t, rfl⟩
    constructor
    · exact (boundaryAngle_mem θ _).1
    · rw [← boundaryAngle_zero hθ]
      exact strictMono_boundaryAngle hθ (neg_neg_of_pos (Real.exp_pos _))
  · intro hu
    have hθ1 : 2 * Real.pi * θ < 2 * Real.pi := by nlinarith [Real.pi_pos, hθ.2]
    have hwhole : u ∈ range (boundaryAngle θ) := by
      rw [range_boundaryAngle hθ]
      exact ⟨hu.1, hu.2.trans hθ1⟩
    obtain ⟨x, hx⟩ := hwhole
    have hx0 : x < 0 := (strictMono_boundaryAngle hθ).lt_iff_lt.mp (by
      rw [boundaryAngle_zero hθ, hx]
      exact hu.2)
    refine ⟨-Real.log (-x) / Real.pi, ?_⟩
    rw [rightAngle, exp_neg_pi_log (-x) (neg_pos.mpr hx0), neg_neg, hx]

theorem exp_two_arctan_mul_I (y : ℝ) :
    Complex.exp (2 * (Real.arctan y : ℂ) * Complex.I) =
      (1 + (y : ℂ) * Complex.I) / (1 - (y : ℂ) * Complex.I) := by
  have hplus : (1 : ℂ) + (y : ℂ) * Complex.I ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    norm_num [Complex.mul_re] at hr
  have hminus : (1 : ℂ) - (y : ℂ) * Complex.I ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    norm_num [Complex.mul_re] at hr
  rw [Complex.ofReal_arctan, Complex.arctan]
  have he :
      2 * (-Complex.I / 2 * Complex.log
        ((1 + (y : ℂ) * Complex.I) / (1 - (y : ℂ) * Complex.I))) * Complex.I =
        Complex.log ((1 + (y : ℂ) * Complex.I) / (1 - (y : ℂ) * Complex.I)) := by
    calc
      _ = -(Complex.I * Complex.I) * Complex.log
          ((1 + (y : ℂ) * Complex.I) / (1 - (y : ℂ) * Complex.I)) := by ring
      _ = _ := by simp
  rw [he, Complex.exp_log (div_ne_zero hplus hminus)]

theorem exp_boundaryAngle (θ x : ℝ) :
    Complex.exp ((boundaryAngle θ x : ℂ) * Complex.I) =
      -((1 + (((x - Real.cos (Real.pi * θ)) / Real.sin (Real.pi * θ) : ℝ) : ℂ) *
          Complex.I) /
        (1 - (((x - Real.cos (Real.pi * θ)) / Real.sin (Real.pi * θ) : ℝ) : ℂ) *
          Complex.I)) := by
  rw [boundaryAngle, Complex.ofReal_add, Complex.ofReal_mul]
  norm_num only [Complex.ofReal_ofNat]
  rw [add_mul, Complex.exp_add, Complex.exp_pi_mul_I, exp_two_arctan_mul_I]
  ring

theorem one_sub_exp_boundaryAngle_ne_zero (θ x : ℝ) :
    (1 : ℂ) - Complex.exp ((boundaryAngle θ x : ℂ) * Complex.I) ≠ 0 := by
  let y : ℝ := (x - Real.cos (Real.pi * θ)) / Real.sin (Real.pi * θ)
  have hminus : (1 : ℂ) - (y : ℂ) * Complex.I ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    norm_num [Complex.mul_re] at hr
  have he : (1 : ℂ) - Complex.exp ((boundaryAngle θ x : ℂ) * Complex.I) =
      2 / (1 - (y : ℂ) * Complex.I) := by
    rw [exp_boundaryAngle]
    change 1 - -((1 + (y : ℂ) * Complex.I) / (1 - (y : ℂ) * Complex.I)) = _
    field_simp [hminus]
    ring
  rw [he]
  exact div_ne_zero (by norm_num) hminus

theorem upperBoundaryValue_boundaryAngle {θ : ℝ} (hθ : θ ∈ Ioo (0 : ℝ) 1)
    (x : ℝ) : upperBoundaryValue θ (boundaryAngle θ x) = (x : ℂ) := by
  let y : ℝ := (x - Real.cos (Real.pi * θ)) / Real.sin (Real.pi * θ)
  have hminus : (1 : ℂ) - (y : ℂ) * Complex.I ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    norm_num [Complex.mul_re] at hr
  have hratio :
      (1 + Complex.exp ((boundaryAngle θ x : ℂ) * Complex.I)) /
        (1 - Complex.exp ((boundaryAngle θ x : ℂ) * Complex.I)) =
          -(y : ℂ) * Complex.I := by
    apply (div_eq_iff (one_sub_exp_boundaryAngle_ne_zero θ x)).mpr
    rw [exp_boundaryAngle]
    change 1 + -((1 + (y : ℂ) * Complex.I) / (1 - (y : ℂ) * Complex.I)) =
      -(y : ℂ) * Complex.I *
        (1 - -((1 + (y : ℂ) * Complex.I) / (1 - (y : ℂ) * Complex.I)))
    field_simp [hminus]
    ring
  have hy : Real.cos (Real.pi * θ) + Real.sin (Real.pi * θ) * y = x := by
    dsimp [y]
    field_simp [(sin_pi_mul_pos hθ).ne']
    ring
  have hm : Complex.I * (Real.sin (Real.pi * θ) : ℂ) * (-(y : ℂ) * Complex.I) =
      ((Real.sin (Real.pi * θ) * y : ℝ) : ℂ) := by
    rw [Complex.ofReal_mul]
    calc
      _ = -(Complex.I * Complex.I) *
          ((Real.sin (Real.pi * θ) : ℂ) * (y : ℂ)) := by ring
      _ = _ := by simp
  rw [upperBoundaryValue, hratio, hm, ← Complex.ofReal_add, hy]

theorem upperBoundaryValue_leftAngle {θ : ℝ} (hθ : θ ∈ Ioo (0 : ℝ) 1) (t : ℝ) :
    upperBoundaryValue θ (leftAngle θ t) = (Real.exp (-Real.pi * t) : ℂ) :=
  upperBoundaryValue_boundaryAngle hθ _

theorem upperBoundaryValue_rightAngle {θ : ℝ} (hθ : θ ∈ Ioo (0 : ℝ) 1) (t : ℝ) :
    upperBoundaryValue θ (rightAngle θ t) = -(Real.exp (-Real.pi * t) : ℂ) := by
  simpa only [rightAngle, Complex.ofReal_neg] using
    upperBoundaryValue_boundaryAngle hθ (-Real.exp (-Real.pi * t))

theorem stripBoundaryValue_leftAngle {θ : ℝ} (hθ : θ ∈ Ioo (0 : ℝ) 1) (t : ℝ) :
    stripBoundaryValue θ (leftAngle θ t) = Complex.I * (t : ℂ) := by
  rw [stripBoundaryValue, upperBoundaryValue_leftAngle hθ t,
    ← Complex.ofReal_log (Real.exp_pos _).le, Real.log_exp]
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr Real.pi_ne_zero]

theorem stripBoundaryValue_rightAngle {θ : ℝ} (hθ : θ ∈ Ioo (0 : ℝ) 1) (t : ℝ) :
    stripBoundaryValue θ (rightAngle θ t) = 1 + Complex.I * (t : ℂ) := by
  have hlog : Complex.log (-(Real.exp (-Real.pi * t) : ℂ)) =
      ((-Real.pi * t : ℝ) : ℂ) + (Real.pi : ℂ) * Complex.I := by
    rw [show -(Real.exp (-Real.pi * t) : ℂ) =
        (Real.exp (-Real.pi * t) : ℂ) * (-1) by ring,
      Complex.log_ofReal_mul (Real.exp_pos _) (show (-1 : ℂ) ≠ 0 by norm_num),
      Real.log_exp, Complex.log_neg_one]
  rw [stripBoundaryValue, upperBoundaryValue_rightAngle hθ t, hlog]
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr Real.pi_ne_zero]
  ring_nf
  simp only [Complex.I_sq]
  ring

theorem cos_pi_mul_lt_one {θ : ℝ} (hθ : θ ∈ Ioo (0 : ℝ) 1) :
    Real.cos (Real.pi * θ) < 1 := by
  have h := Real.cos_lt_cos_of_nonneg_of_le_pi (show (0 : ℝ) ≤ 0 by rfl)
    (show Real.pi * θ ≤ Real.pi by nlinarith [Real.pi_pos, hθ.2])
    (mul_pos Real.pi_pos hθ.1)
  simpa using h

theorem cos_pi_mul_gt_neg_one {θ : ℝ} (hθ : θ ∈ Ioo (0 : ℝ) 1) :
    -1 < Real.cos (Real.pi * θ) := by
  have h := Real.cos_lt_cos_of_nonneg_of_le_pi
    (mul_nonneg Real.pi_pos.le hθ.1.le) (le_refl Real.pi)
    (show Real.pi * θ < Real.pi by nlinarith [Real.pi_pos, hθ.2])
  simpa using h

theorem rawLeftKernel_den_pos {θ : ℝ} (hθ : θ ∈ Ioo (0 : ℝ) 1) (t : ℝ) :
    0 < Real.cosh (Real.pi * t) - Real.cos (Real.pi * θ) := by
  have hc := cos_pi_mul_lt_one hθ
  have hh := Real.one_le_cosh (Real.pi * t)
  linarith

theorem rawRightKernel_den_pos {θ : ℝ} (hθ : θ ∈ Ioo (0 : ℝ) 1) (t : ℝ) :
    0 < Real.cosh (Real.pi * t) + Real.cos (Real.pi * θ) := by
  have hc := cos_pi_mul_gt_neg_one hθ
  have hh := Real.one_le_cosh (Real.pi * t)
  linarith

theorem rawLeftKernel_pos {θ : ℝ} (hθ : θ ∈ Ioo (0 : ℝ) 1) (t : ℝ) :
    0 < rawLeftKernel θ t :=
  div_pos (sin_pi_mul_pos hθ) (mul_pos (by norm_num) (rawLeftKernel_den_pos hθ t))

theorem rawRightKernel_pos {θ : ℝ} (hθ : θ ∈ Ioo (0 : ℝ) 1) (t : ℝ) :
    0 < rawRightKernel θ t :=
  div_pos (sin_pi_mul_pos hθ) (mul_pos (by norm_num) (rawRightKernel_den_pos hθ t))

@[simp] theorem rawLeftKernel_neg (θ t : ℝ) :
    rawLeftKernel θ (-t) = rawLeftKernel θ t := by simp [rawLeftKernel]

@[simp] theorem rawRightKernel_neg (θ t : ℝ) :
    rawRightKernel θ (-t) = rawRightKernel θ t := by simp [rawRightKernel]

theorem rawLeftKernel_exp_den_pos {θ : ℝ} (hθ : θ ∈ Ioo (0 : ℝ) 1) (t : ℝ) :
    0 < Real.exp (Real.pi * t) ^ 2 -
      2 * Real.cos (Real.pi * θ) * Real.exp (Real.pi * t) + 1 := by
  have hs := sin_pi_mul_pos hθ
  nlinarith [sq_nonneg (Real.exp (Real.pi * t) - Real.cos (Real.pi * θ)),
    sq_pos_of_pos hs, Real.sin_sq_add_cos_sq (Real.pi * θ)]

theorem rawRightKernel_exp_den_pos {θ : ℝ} (hθ : θ ∈ Ioo (0 : ℝ) 1) (t : ℝ) :
    0 < Real.exp (Real.pi * t) ^ 2 +
      2 * Real.cos (Real.pi * θ) * Real.exp (Real.pi * t) + 1 := by
  have hs := sin_pi_mul_pos hθ
  nlinarith [sq_nonneg (Real.exp (Real.pi * t) + Real.cos (Real.pi * θ)),
    sq_pos_of_pos hs, Real.sin_sq_add_cos_sq (Real.pi * θ)]

theorem rawLeftKernel_eq_exp {θ : ℝ} (hθ : θ ∈ Ioo (0 : ℝ) 1) (t : ℝ) :
    rawLeftKernel θ t = Real.sin (Real.pi * θ) * Real.exp (Real.pi * t) /
      (Real.exp (Real.pi * t) ^ 2 -
        2 * Real.cos (Real.pi * θ) * Real.exp (Real.pi * t) + 1) := by
  have he := (Real.exp_pos (Real.pi * t)).ne'
  have hd := (rawLeftKernel_den_pos hθ t).ne'
  have hq := (rawLeftKernel_exp_den_pos hθ t).ne'
  rw [rawLeftKernel, Real.cosh_eq, Real.exp_neg]
  field_simp [he, hd, hq]
  ring

theorem rawRightKernel_eq_exp {θ : ℝ} (hθ : θ ∈ Ioo (0 : ℝ) 1) (t : ℝ) :
    rawRightKernel θ t = Real.sin (Real.pi * θ) * Real.exp (Real.pi * t) /
      (Real.exp (Real.pi * t) ^ 2 +
        2 * Real.cos (Real.pi * θ) * Real.exp (Real.pi * t) + 1) := by
  have he := (Real.exp_pos (Real.pi * t)).ne'
  have hd := (rawRightKernel_den_pos hθ t).ne'
  have hq := (rawRightKernel_exp_den_pos hθ t).ne'
  rw [rawRightKernel, Real.cosh_eq, Real.exp_neg]
  field_simp [he, hd, hq]
  ring

theorem rawLeftKernel_eq_exp_neg {θ : ℝ} (hθ : θ ∈ Ioo (0 : ℝ) 1) (t : ℝ) :
    rawLeftKernel θ t = Real.sin (Real.pi * θ) * Real.exp (-Real.pi * t) /
      (Real.exp (-Real.pi * t) ^ 2 -
        2 * Real.cos (Real.pi * θ) * Real.exp (-Real.pi * t) + 1) := by
  rw [← rawLeftKernel_neg θ t, rawLeftKernel_eq_exp hθ (-t)]
  simp only [mul_neg, neg_mul]

theorem rawRightKernel_eq_exp_neg {θ : ℝ} (hθ : θ ∈ Ioo (0 : ℝ) 1) (t : ℝ) :
    rawRightKernel θ t = Real.sin (Real.pi * θ) * Real.exp (-Real.pi * t) /
      (Real.exp (-Real.pi * t) ^ 2 +
        2 * Real.cos (Real.pi * θ) * Real.exp (-Real.pi * t) + 1) := by
  rw [← rawRightKernel_neg θ t, rawRightKernel_eq_exp hθ (-t)]
  simp only [mul_neg, neg_mul]

theorem hasDerivAt_boundaryAngle {θ : ℝ} (hθ : θ ∈ Ioo (0 : ℝ) 1) (x : ℝ) :
    HasDerivAt (boundaryAngle θ)
      (2 * Real.sin (Real.pi * θ) /
        ((x - Real.cos (Real.pi * θ)) ^ 2 + Real.sin (Real.pi * θ) ^ 2)) x := by
  have hs := (sin_pi_mul_pos hθ).ne'
  have hq : ((x - Real.cos (Real.pi * θ)) ^ 2 + Real.sin (Real.pi * θ) ^ 2) ≠ 0 := by
    have hp := sq_pos_of_pos (sin_pi_mul_pos hθ)
    nlinarith [sq_nonneg (x - Real.cos (Real.pi * θ))]
  have hr : (1 + ((x - Real.cos (Real.pi * θ)) / Real.sin (Real.pi * θ)) ^ 2) ≠ 0 := by
    positivity
  have h := (((((hasDerivAt_id x).sub_const (Real.cos (Real.pi * θ))).div_const
    (Real.sin (Real.pi * θ))).arctan.const_mul 2).const_add Real.pi)
  change HasDerivAt (fun y : ℝ => Real.pi + 2 * Real.arctan
    ((y - Real.cos (Real.pi * θ)) / Real.sin (Real.pi * θ))) _ x
  convert h using 1
  · rfl
  · simp only [id_eq]
    field_simp [hs, hq, hr]
    ring

theorem hasDerivAt_exp_neg_pi (t : ℝ) :
    HasDerivAt (fun x : ℝ => Real.exp (-Real.pi * x))
      (Real.exp (-Real.pi * t) * (-Real.pi)) t := by
  simpa only [id_eq, mul_one] using ((hasDerivAt_id t).const_mul (-Real.pi)).exp

theorem hasDerivAt_leftAngle {θ : ℝ} (hθ : θ ∈ Ioo (0 : ℝ) 1) (t : ℝ) :
    HasDerivAt (leftAngle θ) (-(2 * Real.pi * rawLeftKernel θ t)) t := by
  have h := (hasDerivAt_boundaryAngle hθ (Real.exp (-Real.pi * t))).comp t
    (hasDerivAt_exp_neg_pi t)
  have hq :
      (Real.exp (-Real.pi * t) - Real.cos (Real.pi * θ)) ^ 2 +
          Real.sin (Real.pi * θ) ^ 2 = Real.exp (-Real.pi * t) ^ 2 -
            2 * Real.cos (Real.pi * θ) * Real.exp (-Real.pi * t) + 1 := by
    nlinarith [Real.sin_sq_add_cos_sq (Real.pi * θ)]
  change HasDerivAt (fun x : ℝ => boundaryAngle θ (Real.exp (-Real.pi * x))) _ t
  convert h using 1
  · rfl
  · rw [hq, rawLeftKernel_eq_exp_neg hθ t]
    ring

theorem hasDerivAt_rightAngle {θ : ℝ} (hθ : θ ∈ Ioo (0 : ℝ) 1) (t : ℝ) :
    HasDerivAt (rightAngle θ) (2 * Real.pi * rawRightKernel θ t) t := by
  have h := (hasDerivAt_boundaryAngle hθ (-Real.exp (-Real.pi * t))).comp t
    (hasDerivAt_exp_neg_pi t).neg
  have hq :
      (-Real.exp (-Real.pi * t) - Real.cos (Real.pi * θ)) ^ 2 +
          Real.sin (Real.pi * θ) ^ 2 = Real.exp (-Real.pi * t) ^ 2 +
            2 * Real.cos (Real.pi * θ) * Real.exp (-Real.pi * t) + 1 := by
    nlinarith [Real.sin_sq_add_cos_sq (Real.pi * θ)]
  change HasDerivAt (fun x : ℝ => boundaryAngle θ (-Real.exp (-Real.pi * x))) _ t
  convert h using 1
  · rfl
  · rw [hq, rawRightKernel_eq_exp_neg hθ t]
    ring

theorem abs_two_pi_rawLeftKernel {θ : ℝ} (hθ : θ ∈ Ioo (0 : ℝ) 1) (t : ℝ) :
    |2 * Real.pi * rawLeftKernel θ t| = 2 * Real.pi * rawLeftKernel θ t :=
  abs_of_pos (mul_pos (mul_pos (by norm_num) Real.pi_pos) (rawLeftKernel_pos hθ t))

theorem abs_two_pi_rawRightKernel {θ : ℝ} (hθ : θ ∈ Ioo (0 : ℝ) 1) (t : ℝ) :
    |2 * Real.pi * rawRightKernel θ t| = 2 * Real.pi * rawRightKernel θ t :=
  abs_of_pos (mul_pos (mul_pos (by norm_num) Real.pi_pos) (rawRightKernel_pos hθ t))

theorem integral_leftAngle_substitution {θ : ℝ} (hθ : θ ∈ Ioo (0 : ℝ) 1) (g : ℝ → ℝ) :
    (∫ u in Ioo (2 * Real.pi * θ) (2 * Real.pi), g u ∂volume) =
      ∫ t : ℝ, 2 * Real.pi * rawLeftKernel θ t * g (leftAngle θ t) ∂volume := by
  have h := integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ
    (fun t (_ : t ∈ (univ : Set ℝ)) => (hasDerivAt_leftAngle hθ t).hasDerivWithinAt)
    (strictAnti_leftAngle hθ).injective.injOn g
  simpa only [image_univ, range_leftAngle hθ, Measure.restrict_univ, abs_neg,
    abs_two_pi_rawLeftKernel hθ, smul_eq_mul] using h

theorem integral_rightAngle_substitution {θ : ℝ} (hθ : θ ∈ Ioo (0 : ℝ) 1) (g : ℝ → ℝ) :
    (∫ u in Ioo (0 : ℝ) (2 * Real.pi * θ), g u ∂volume) =
      ∫ t : ℝ, 2 * Real.pi * rawRightKernel θ t * g (rightAngle θ t) ∂volume := by
  have h := integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ
    (fun t (_ : t ∈ (univ : Set ℝ)) => (hasDerivAt_rightAngle hθ t).hasDerivWithinAt)
    (strictMono_rightAngle hθ).injective.injOn g
  simpa only [image_univ, range_rightAngle hθ, Measure.restrict_univ,
    abs_two_pi_rawRightKernel hθ, smul_eq_mul] using h

theorem integrable_leftAngle_substitution {θ : ℝ} (hθ : θ ∈ Ioo (0 : ℝ) 1)
    (g : ℝ → ℝ) :
    IntegrableOn g (Ioo (2 * Real.pi * θ) (2 * Real.pi)) volume ↔
      Integrable (fun t : ℝ => 2 * Real.pi * rawLeftKernel θ t * g (leftAngle θ t)) volume := by
  have h := integrableOn_image_iff_integrableOn_abs_deriv_smul MeasurableSet.univ
    (fun t (_ : t ∈ (univ : Set ℝ)) => (hasDerivAt_leftAngle hθ t).hasDerivWithinAt)
    (strictAnti_leftAngle hθ).injective.injOn g
  simpa only [image_univ, range_leftAngle hθ, integrableOn_univ, abs_neg,
    abs_two_pi_rawLeftKernel hθ, smul_eq_mul] using h

theorem integrable_rightAngle_substitution {θ : ℝ} (hθ : θ ∈ Ioo (0 : ℝ) 1)
    (g : ℝ → ℝ) :
    IntegrableOn g (Ioo (0 : ℝ) (2 * Real.pi * θ)) volume ↔
      Integrable (fun t : ℝ => 2 * Real.pi * rawRightKernel θ t * g (rightAngle θ t)) volume := by
  have h := integrableOn_image_iff_integrableOn_abs_deriv_smul MeasurableSet.univ
    (fun t (_ : t ∈ (univ : Set ℝ)) => (hasDerivAt_rightAngle hθ t).hasDerivWithinAt)
    (strictMono_rightAngle hθ).injective.injOn g
  simpa only [image_univ, range_rightAngle hθ, integrableOn_univ,
    abs_two_pi_rawRightKernel hθ, smul_eq_mul] using h

end QuantumProver.HirschmanBoundaryChange

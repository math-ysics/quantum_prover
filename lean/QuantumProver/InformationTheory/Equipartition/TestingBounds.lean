import QuantumProver.InformationTheory.Equipartition.Definitions
import QuantumProver.InformationTheory.Equipartition.RenyiBounds
import QuantumProver.InformationTheory.Equipartition.UniversalEntropyBounds

noncomputable section

open scoped BigOperators Matrix Kronecker
open scoped Topology
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Filter

namespace QuantumProver.Equipartition.FiniteModel

theorem weighted_square_le_remainder {x t t₀ J : ℝ}
    (ht : 0 ≤ t) (ht₀ : 0 < t₀) (ht3 : t ≤ t₀ / 3)
    (hJ : 0 ≤ J) (hxJ : x ≤ J) :
    x ^ 2 * Real.exp (t * |x|) ≤
      (2 * Real.exp (2 * t₀ * J / 3) / t₀ ^ 2) * expRemainder (t₀ * x) := by
  have hexp : t * |x| ≤ 2 * t₀ * J / 3 - t₀ * x / 3 := by
    by_cases hx : 0 ≤ x
    · rw [abs_of_nonneg hx]
      have htx := mul_le_mul_of_nonneg_right ht3 hx
      have hjx := mul_le_mul_of_nonneg_left hxJ ht₀.le
      nlinarith
    · have hx' : x ≤ 0 := le_of_lt (lt_of_not_ge hx)
      rw [abs_of_nonpos hx']
      have htx := mul_le_mul_of_nonneg_right ht3 (neg_nonneg.mpr hx')
      have hprod := mul_nonneg ht₀.le hJ
      nlinarith
  have hk : 0 ≤ 2 * Real.exp (2 * t₀ * J / 3) / t₀ ^ 2 := by positivity
  calc
    x ^ 2 * Real.exp (t * |x|) ≤
        x ^ 2 * Real.exp (2 * t₀ * J / 3 - t₀ * x / 3) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) (sq_nonneg x)
    _ = (2 * Real.exp (2 * t₀ * J / 3) / t₀ ^ 2) *
        ((t₀ * x) ^ 2 / 2 * Real.exp (-(t₀ * x) / 3)) := by
      rw [show 2 * t₀ * J / 3 - t₀ * x / 3 =
        2 * t₀ * J / 3 + (-(t₀ * x) / 3) by ring, Real.exp_add]
      field_simp [ht₀.ne'] <;> ring
    _ ≤ (2 * Real.exp (2 * t₀ * J / 3) / t₀ ^ 2) * expRemainder (t₀ * x) :=
      mul_le_mul_of_nonneg_left (expRemainder_sharp_lower _) hk

namespace FiniteLaw

variable {ι : Type*} [Fintype ι] (L : FiniteLaw ι)

theorem expect_expRemainder (X : ι → ℝ) (t₀ : ℝ) :
    L.expect (fun i => expRemainder (t₀ * X i)) =
      L.expect (fun i => Real.exp (-t₀ * X i)) - 1 + t₀ * L.mean X := by
  simp only [expRemainder, neg_mul]
  rw [L.expect_add, L.expect_sub, L.expect_const, L.expect_smul]
  rfl

theorem truncated_weightedSecondMoment_le (X : ι → ℝ) {t t₀ J : ℝ}
    (ht : 0 ≤ t) (ht₀ : 0 < t₀) (ht3 : t ≤ t₀ / 3) (hJ : 0 ≤ J) :
    L.expect (fun i => if X i ≤ J then (X i) ^ 2 * Real.exp (t * |X i|) else 0) ≤
      (2 * Real.exp (2 * t₀ * J / 3) / t₀ ^ 2) *
        (L.expect (fun i => Real.exp (-t₀ * X i)) - 1 + t₀ * L.mean X) := by
  classical
  rw [← L.expect_expRemainder, ← L.expect_smul]
  apply L.expect_mono
  intro i
  by_cases hx : X i ≤ J
  · rw [if_pos hx]
    exact weighted_square_le_remainder ht ht₀ ht3 hJ hx
  · rw [if_neg hx]
    exact mul_nonneg (by positivity) (expRemainder_nonneg _)

theorem laplace_taylor_upper (X : ι → ℝ) {t : ℝ} (ht : 0 ≤ t) :
    L.expect (fun i => Real.exp (-t * X i)) ≤
      1 - t * L.mean X + t ^ 2 / 2 * L.weightedSecondMoment X 0 t := by
  calc
    L.expect (fun i => Real.exp (-t * X i)) ≤
        L.expect (fun i => 1 + (-t) * X i +
          (t ^ 2 / 2) * ((X i) ^ 2 * Real.exp (t * |X i|))) := by
      apply L.expect_mono
      intro i
      convert exp_taylor_upper (-t * X i) using 1 <;>
        (try simp only [abs_mul, abs_neg, abs_of_nonneg ht]) <;> ring
    _ = 1 - t * L.mean X + t ^ 2 / 2 * L.weightedSecondMoment X 0 t := by
      rw [L.expect_add, L.expect_add, L.expect_const, L.expect_smul, L.expect_smul]
      simp only [weightedSecondMoment, sub_zero, mean]
      ring

theorem positive_laplace_taylor_upper (X : ι → ℝ) {t : ℝ} (ht : 0 ≤ t) :
    L.expect (fun i => Real.exp (t * X i)) ≤
      1 + t * L.mean X + t ^ 2 / 2 * L.weightedSecondMoment X 0 t := by
  calc
    L.expect (fun i => Real.exp (t * X i)) ≤
        L.expect (fun i => 1 + t * X i +
          (t ^ 2 / 2) * ((X i) ^ 2 * Real.exp (t * |X i|))) := by
      apply L.expect_mono
      intro i
      convert exp_taylor_upper (t * X i) using 1 <;>
        (try simp only [abs_mul, abs_of_nonneg ht]) <;> ring
    _ = 1 + t * L.mean X + t ^ 2 / 2 * L.weightedSecondMoment X 0 t := by
      rw [L.expect_add, L.expect_add, L.expect_const, L.expect_smul, L.expect_smul]
      simp only [weightedSecondMoment, sub_zero, mean]

end FiniteLaw

theorem retained_mean_coefficient_nonpos {t t₀ H : ℝ}
    (ht : 0 ≤ t) (ht₀ : 0 < t₀) (ht8 : t ≤ t₀ / 8) (hH : H ≤ 2) :
    -t + H * t ^ 2 / t₀ ≤ 0 := by
  have hHt : H * t ≤ t₀ := by
    have hm := mul_le_mul_of_nonneg_right hH ht
    linarith
  have hm := mul_le_mul_of_nonneg_right hHt ht
  have hdiv : H * t ^ 2 / t₀ ≤ t :=
    (div_le_iff₀ ht₀).mpr (by nlinarith)
  linarith

namespace FiniteLaw

variable {ι : Type*} [Fintype ι] (L : FiniteLaw ι)

theorem laplace_of_mean_dependent_curvature (X : ι → ℝ) {t t₀ H A F : ℝ}
    (ht : 0 ≤ t) (ht₀ : 0 < t₀) (ht8 : t ≤ t₀ / 8) (hH : H ≤ 2)
    (hs : 0 ≤ L.mean X)
    (hw : L.weightedSecondMoment X 0 t ≤
      2 * H * (A + L.mean X / t₀) + F) :
    L.expect (fun i => Real.exp (-t * X i)) ≤ 1 + t ^ 2 * (H * A + F / 2) := by
  have hc := retained_mean_coefficient_nonpos ht ht₀ ht8 hH
  calc
    L.expect (fun i => Real.exp (-t * X i)) ≤
        1 - t * L.mean X + t ^ 2 / 2 * L.weightedSecondMoment X 0 t :=
      L.laplace_taylor_upper X ht
    _ ≤ 1 - t * L.mean X + t ^ 2 / 2 *
        (2 * H * (A + L.mean X / t₀) + F) := by
      have hb : t ^ 2 / 2 * L.weightedSecondMoment X 0 t ≤
          t ^ 2 / 2 * (2 * H * (A + L.mean X / t₀) + F) :=
        mul_le_mul_of_nonneg_left hw (by positivity)
      linarith
    _ = 1 + t ^ 2 * (H * A + F / 2) +
        (-t + H * t ^ 2 / t₀) * L.mean X := by ring
    _ ≤ 1 + t ^ 2 * (H * A + F / 2) := by
      exact add_le_of_nonpos_right (mul_nonpos_of_nonpos_of_nonneg hc hs)

end FiniteLaw

theorem endpoint_curvature_factor_bound {L a e : ℝ}
    (hL : 1 ≤ L) (ha : 0 ≤ a) (haL : a ≤ 1 / (100 * L))
    (he : 0 ≤ e) (heL : e ≤ 2 / (75 * L)) :
    Real.exp e * (1 + 2 * a) ≤ 1 + 1 / (4 * L) := by
  have hLp : 0 < L := by linarith
  have hehalf : e ≤ 1 / 2 := by
    have hbound : 2 / (75 * L) ≤ (1 / 2 : ℝ) := by
      apply (div_le_iff₀ (by positivity : 0 < 75 * L)).mpr
      linarith
    exact heL.trans hbound
  have hquad : 2 * e ^ 2 ≤ e := by
    nlinarith [mul_nonneg he (show 0 ≤ 1 - 2 * e by linarith)]
  have hsmall := exp_sub_one_small he (hehalf.trans (by norm_num))
  have he' : Real.exp e ≤ 1 + 4 / (75 * L) := by
    have he2 : 2 * e ≤ 4 / (75 * L) := by
      calc
        2 * e ≤ 2 * (2 / (75 * L)) := mul_le_mul_of_nonneg_left heL (by norm_num)
        _ = _ := by ring
    nlinarith
  have ha' : 1 + 2 * a ≤ 1 + 1 / (50 * L) := by
    have hid : 2 * (1 / (100 * L)) = 1 / (50 * L) := by ring
    rw [← hid]
    linarith
  have hid : (1 + 1 / (4 * L)) -
      (1 + 4 / (75 * L)) * (1 + 1 / (50 * L)) =
        (2650 * L - 16) / (15000 * L ^ 2) := by
    field_simp
    ring
  have hpoly : (1 + 4 / (75 * L)) * (1 + 1 / (50 * L)) ≤
      1 + 1 / (4 * L) := by
    apply sub_nonneg.mp
    rw [hid]
    apply div_nonneg
    · linarith
    · positivity
  calc
    Real.exp e * (1 + 2 * a) ≤
        (1 + 4 / (75 * L)) * (1 + 1 / (50 * L)) :=
      mul_le_mul he' ha' (by linarith) (by positivity)
    _ ≤ 1 + 1 / (4 * L) := hpoly

theorem half_square_le_exp {u : ℝ} (hu : 0 ≤ u) : u ^ 2 / 2 ≤ Real.exp u := by
  have he : 1 ≤ Real.exp (u / 3) := Real.one_le_exp_iff.mpr (by positivity)
  have hs := expRemainder_sharp_lower (-u)
  simp only [neg_sq, neg_neg] at hs
  calc
    u ^ 2 / 2 ≤ u ^ 2 / 2 * Real.exp (u / 3) := by
      simpa using mul_le_mul_of_nonneg_left he (by positivity : 0 ≤ u ^ 2 / 2)
    _ ≤ expRemainder (-u) := hs
    _ ≤ Real.exp u := by simp only [expRemainder, neg_neg]; linarith

theorem positive_tail_pointwise {β t J x : ℝ} (hβ : 0 < β)
    (ht : t ≤ β / 8) (hJ : 0 ≤ J) (hx : J ≤ x) :
    x ^ 2 * Real.exp (t * x) ≤
      (128 / β ^ 2) * Real.exp (-(3 * β * J / 4)) * Real.exp (β * x) := by
  have hx0 : 0 ≤ x := hJ.trans hx
  have hsq : x ^ 2 ≤ (128 / β ^ 2) * Real.exp (β * x / 8) := by
    have he := half_square_le_exp (show 0 ≤ β * x / 8 by positivity)
    have hm := mul_le_mul_of_nonneg_left he (by positivity : 0 ≤ 128 / β ^ 2)
    have hid : (128 / β ^ 2) * ((β * x / 8) ^ 2 / 2) = x ^ 2 := by
      field_simp [hβ.ne']
      ring
    rw [hid] at hm
    exact hm
  have harg : β * x / 8 + t * x ≤ -(3 * β * J / 4) + β * x := by
    have ht' := mul_le_mul_of_nonneg_right ht hx0
    have hx' := mul_le_mul_of_nonneg_left hx hβ.le
    nlinarith
  calc
    x ^ 2 * Real.exp (t * x) ≤
        ((128 / β ^ 2) * Real.exp (β * x / 8)) * Real.exp (t * x) :=
      mul_le_mul_of_nonneg_right hsq (Real.exp_pos _).le
    _ = (128 / β ^ 2) * Real.exp (β * x / 8 + t * x) := by
      rw [mul_assoc, ← Real.exp_add]
    _ ≤ (128 / β ^ 2) * Real.exp (-(3 * β * J / 4) + β * x) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr harg) (by positivity)
    _ = (128 / β ^ 2) * Real.exp (-(3 * β * J / 4)) * Real.exp (β * x) := by
      rw [Real.exp_add]
      ring

namespace FiniteLaw

variable {ι : Type*} [Fintype ι] (L : FiniteLaw ι)

theorem positive_tail_weightedSecondMoment_le (X : ι → ℝ) {β t J : ℝ}
    (hβ : 0 < β) (ht : t ≤ β / 8) (hJ : 0 ≤ J) :
    L.expect (fun i => if J < X i then (X i) ^ 2 * Real.exp (t * |X i|) else 0) ≤
      ((128 / β ^ 2) * Real.exp (-(3 * β * J / 4))) *
        L.expect (fun i => Real.exp (β * X i)) := by
  classical
  rw [← L.expect_smul]
  apply L.expect_mono
  intro i
  by_cases hx : J < X i
  · rw [if_pos hx, abs_of_nonneg (hJ.trans hx.le)]
    exact positive_tail_pointwise hβ ht hJ hx.le
  · rw [if_neg hx]
    positivity

theorem weightedSecondMoment_split (X : ι → ℝ) (t J : ℝ) :
    L.weightedSecondMoment X 0 t =
      L.expect (fun i => if X i ≤ J then (X i) ^ 2 * Real.exp (t * |X i|) else 0) +
        L.expect (fun i => if J < X i then (X i) ^ 2 * Real.exp (t * |X i|) else 0) := by
  classical
  rw [← L.expect_add]
  unfold weightedSecondMoment
  congr 1
  funext i
  by_cases hx : X i ≤ J
  · simp [hx, not_lt.mpr hx]
  · simp [hx, lt_of_not_ge hx]

theorem weightedSecondMoment_le_curvature_and_tail (X : ι → ℝ)
    {t t₀ β J : ℝ} (ht : 0 ≤ t) (ht₀ : 0 < t₀)
    (ht3 : t ≤ t₀ / 3) (hβ : 0 < β) (htβ : t ≤ β / 8) (hJ : 0 ≤ J) :
    L.weightedSecondMoment X 0 t ≤
      (2 * Real.exp (2 * t₀ * J / 3) / t₀ ^ 2) *
        (L.expect (fun i => Real.exp (-t₀ * X i)) - 1 + t₀ * L.mean X) +
        ((128 / β ^ 2) * Real.exp (-(3 * β * J / 4))) *
          L.expect (fun i => Real.exp (β * X i)) := by
  rw [L.weightedSecondMoment_split X t J]
  exact add_le_add (L.truncated_weightedSecondMoment_le X ht ht₀ ht3 hJ)
    (L.positive_tail_weightedSecondMoment_le X hβ htβ hJ)

theorem exp_mean_le_expect_exp (X : ι → ℝ) :
    Real.exp (L.mean X) ≤ L.expect (fun i => Real.exp (X i)) := by
  calc
    Real.exp (L.mean X) =
        L.expect (fun i => Real.exp (L.mean X) * (1 + (X i - L.mean X))) := by
      rw [L.expect_smul, L.expect_add, L.expect_const, L.expect_centered]
      simp
    _ ≤ L.expect (fun i => Real.exp (X i)) := by
      apply L.expect_mono
      intro i
      have ht := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (X i - L.mean X))
        (Real.exp_pos (L.mean X)).le
      rw [← Real.exp_add] at ht
      convert ht using 1 <;> congr 1 <;> ring

end FiniteLaw

theorem logarithmic_cube_slack {L l H : ℝ}
    (hL : 8 ≤ L) (hl : 0 ≤ l) (hlL : l ≤ L - 2)
    (hH : H ≤ 1 + 1 / (4 * L)) :
    H * l ^ 3 ≤ L ^ 3 - 2 * L ^ 2 := by
  have hLp : 0 < L := by linarith
  have hid : (1 + 1 / (4 * L)) * (L - 2) ^ 3 =
      L ^ 3 - (23 / 4 : ℝ) * L ^ 2 + (21 / 2 : ℝ) * L - 5 - 2 / L := by
    field_simp
    ring
  have hs : (8 : ℝ) * L ≤ L ^ 2 := by
    nlinarith [mul_nonneg hLp.le (show 0 ≤ L - 8 by linarith)]
  have hpoly : (1 + 1 / (4 * L)) * (L - 2) ^ 3 ≤ L ^ 3 - 2 * L ^ 2 := by
    rw [hid]
    have hdiv : 0 ≤ 2 / L := by positivity
    nlinarith
  calc
    H * l ^ 3 ≤ (1 + 1 / (4 * L)) * l ^ 3 :=
      mul_le_mul_of_nonneg_right hH (pow_nonneg hl _)
    _ ≤ (1 + 1 / (4 * L)) * (L - 2) ^ 3 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hl hlL 3) (by positivity)
    _ ≤ L ^ 3 - 2 * L ^ 2 := hpoly

theorem logarithmic_coefficient_closure {L l H M K₀ : ℝ}
    (hL : 8 ≤ L) (hl : 0 ≤ l) (hlL : l ≤ L - 2)
    (hH : H ≤ 1 + 1 / (4 * L)) (hM : 0 ≤ M) (hK : K₀ ≤ 2 * M) :
    H * M * l ^ 3 + K₀ * L ^ 2 ≤ M * L ^ 3 := by
  have hc := mul_le_mul_of_nonneg_left (logarithmic_cube_slack hL hl hlL hH) hM
  have hk := mul_le_mul_of_nonneg_right hK (sq_nonneg L)
  nlinarith

theorem weighted_normalized_log_lower {p q S w : ℝ}
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hS : 0 < S) (hw : 0 ≤ w)
    (hs : q = 0 → p * w = 0) :
    p * w - (q / S) * w ≤
      (p * w) * (Real.log p - Real.log q + Real.log S) := by
  by_cases hp0 : p = 0
  · subst p
    simp only [zero_mul, zero_sub]
    exact neg_nonpos.mpr (mul_nonneg (div_nonneg hq hS.le) hw)
  by_cases hq0 : q = 0
  · have hpw := hs hq0
    simp [hq0, hpw]
  have hp' : 0 < p := lt_of_le_of_ne hp (Ne.symm hp0)
  have hq' : 0 < q := lt_of_le_of_ne hq (Ne.symm hq0)
  have hlog := Real.log_le_sub_one_of_pos
    (show 0 < q / (p * S) by positivity)
  rw [Real.log_div hq0 (mul_ne_zero hp0 hS.ne'),
    Real.log_mul hp0 hS.ne'] at hlog
  have hm := mul_le_mul_of_nonneg_left hlog (mul_nonneg hp hw)
  have hid : (p * w) * (q / (p * S) - 1) = (q / S) * w - p * w := by
    field_simp [hp0, hS.ne'] <;> ring
  rw [hid] at hm
  nlinarith

theorem real_complex_smul_matrix {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ℝ) (A : CMat ι) : (a : ℂ) • A = a • A := by
  ext i j
  change (a : ℂ) * A i j = a • A i j
  simp only [Algebra.smul_def]
  rfl

theorem supportLE_of_real_psd_domination {ι : Type*} [Fintype ι] [DecidableEq ι]
    {ρ σ : CMat ι} (hρ : ρ.PosSemidef) {a : ℝ}
    (hdom : LoewnerLE ρ (a • σ)) : SupportLE ρ σ := by
  apply supportLE_of_psd_domination hρ (a := (a : ℂ))
  simpa only [real_complex_smul_matrix] using hdom

section MatrixUnnormalizedEntropy

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem matrixRpow_smul (A : CMat ι) (hA : A.PosSemidef) (t : ℝ)
    {a : ℝ} (ha : 0 < a) :
    matrixRpow (a • A) t = Real.rpow a t • matrixRpow A t := by
  unfold matrixRpow
  simp only [Real.rpow_eq_pow]
  rw [← cfc_comp_smul (p := IsSelfAdjoint) a (fun x : ℝ => x ^ t) A
    ((A.finite_real_spectrum.image (fun x : ℝ => a • x)).continuousOn _) hA.1,
    ← cfc_smul (p := IsSelfAdjoint) (a ^ t) (fun x : ℝ => x ^ t) A
      (A.finite_real_spectrum.continuousOn _)]
  apply cfc_congr
  intro x hx
  exact Real.mul_rpow ha.le (spectrum_nonneg_of_nonneg hA.nonneg hx)

theorem inverse_half_scalar_shift_budget {p η : ℝ} (hp : 0 ≤ p) (hη : 0 ≤ η) :
    Real.rpow p (3 / 2 : ℝ) * Real.rpow (p + η) (-1 / 2 : ℝ) ≤ p := by
  by_cases hp0 : p = 0
  · simp [hp0, Real.zero_rpow (by norm_num : (3 / 2 : ℝ) ≠ 0)]
  have hp' : 0 < p := lt_of_le_of_ne hp (Ne.symm hp0)
  calc
    Real.rpow p (3 / 2 : ℝ) * Real.rpow (p + η) (-1 / 2 : ℝ) ≤
        Real.rpow p (3 / 2 : ℝ) * Real.rpow p (-1 / 2 : ℝ) :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos hp' (le_add_of_nonneg_right hη) (by norm_num))
        (Real.rpow_nonneg hp _)
    _ = p := by rw [Real.rpow_eq_pow, Real.rpow_eq_pow, ← Real.rpow_add hp']; norm_num

theorem matrixRpow_add_scalar (A : CMat ι) (hA : A.IsHermitian) (t ε : ℝ) :
    matrixRpow (A + ε • (1 : CMat ι)) t =
      cfc (fun x : ℝ => Real.rpow (x + ε) t) A := by
  have hshift : A + ε • (1 : CMat ι) = cfc (fun x : ℝ => x + ε) A := by
    rw [cfc_add_const (p := IsSelfAdjoint) ε (fun x : ℝ => x) A
      (A.finite_real_spectrum.continuousOn _) hA,
      cfc_id' (p := IsSelfAdjoint) ℝ A hA, Algebra.algebraMap_eq_smul_one]
  unfold matrixRpow
  rw [hshift, ← cfc_comp (p := IsSelfAdjoint) (fun x : ℝ => Real.rpow x t)
    (fun x : ℝ => x + ε) A hA
    ((A.finite_real_spectrum.image (fun x : ℝ => x + ε)).continuousOn _)
    (A.finite_real_spectrum.continuousOn _)]
  rfl

theorem matrixRpow_eq_cfc_rpow {A : CMat ι} (hA : A.PosSemidef) (α : ℝ) :
    matrixRpow A α = CFC.rpow A α := by
  unfold matrixRpow
  simpa only [Real.rpow_eq_pow, CFC.rpow_eq_pow] using
    (CFC.rpow_eq_cfc_real (y := α) hA.nonneg).symm

theorem trace_matrixRpow_scalar_shift_tendsto {A : CMat ι}
    (hA : A.PosSemidef) {α : ℝ} (hα : 0 ≤ α) (k : ℝ) :
    Tendsto (fun ε : ℝ =>
      (matrixRpow (A + (k * ε) • (1 : CMat ι)) α).trace.re)
      (𝓝 0) (𝓝 (matrixRpow A α).trace.re) := by
  have hshift (ε : ℝ) :
      (matrixRpow (A + (k * ε) • (1 : CMat ι)) α).trace.re =
        ∑ i, Real.rpow (hA.1.eigenvalues i + k * ε) α := by
    rw [matrixRpow_add_scalar A hA.1, Spectral.trace_cfc_eq_sum _ hA.1]
  have hbase : (matrixRpow A α).trace.re =
      ∑ i, Real.rpow (hA.1.eigenvalues i) α :=
    Spectral.trace_cfc_eq_sum _ hA.1
  simp_rw [hshift]
  rw [hbase]
  apply tendsto_finset_sum
  intro i hi
  have harg : Tendsto (fun ε : ℝ => hA.1.eigenvalues i + k * ε)
      (𝓝 0) (𝓝 (hA.1.eigenvalues i)) := by
    simpa only [mul_zero, add_zero, id_eq] using
      ((tendsto_const_nhds : Tendsto (fun _ : ℝ => hA.1.eigenvalues i)
        (𝓝 (0 : ℝ)) (𝓝 (hA.1.eigenvalues i))).add
          ((tendsto_id : Tendsto (fun ε : ℝ => ε) (𝓝 (0 : ℝ)) (𝓝 (0 : ℝ))).const_mul k))
  exact (Real.continuousAt_rpow_const (hA.1.eigenvalues i) α (Or.inr hα)).tendsto.comp harg

theorem trace_matrixRpow_subadd {A B : CMat ι}
    (hA : A.PosSemidef) (hB : B.PosSemidef) {α : ℝ}
    (hα₀ : 0 < α) (hα₁ : α < 1) :
    (matrixRpow (A + B) α).trace.re ≤
      (matrixRpow A α).trace.re + (matrixRpow B α).trace.re := by
  have hl := (trace_matrixRpow_scalar_shift_tendsto (hA.add hB) hα₀.le 2).mono_left
    (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from inf_le_left)
  have hr := ((trace_matrixRpow_scalar_shift_tendsto hA hα₀.le 1).add
    (trace_matrixRpow_scalar_shift_tendsto hB hα₀.le 1)).mono_left
      (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from inf_le_left)
  have hev : ∀ᶠ ε : ℝ in 𝓝[>] 0,
      (matrixRpow (A + B + (2 * ε) • (1 : CMat ι)) α).trace.re ≤
        (matrixRpow (A + ε • (1 : CMat ι)) α).trace.re +
          (matrixRpow (B + ε • (1 : CMat ι)) α).trace.re := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hAe : (A + ε • (1 : CMat ι)).PosDef :=
      Matrix.isStrictlyPositive_iff_posDef.mp
        (IsStrictlyPositive.nonneg_add hA.nonneg
          (IsStrictlyPositive.smul hε isStrictlyPositive_one))
    have hBe : (B + ε • (1 : CMat ι)).PosDef :=
      Matrix.isStrictlyPositive_iff_posDef.mp
        (IsStrictlyPositive.nonneg_add hB.nonneg
          (IsStrictlyPositive.smul hε isStrictlyPositive_one))
    have hsum : (A + ε • (1 : CMat ι)) + (B + ε • (1 : CMat ι)) =
        A + B + (2 * ε) • (1 : CMat ι) := by
      rw [show 2 * ε = ε + ε by ring, add_smul]
      abel
    have h := trace_rpow_subadd_faithful hAe hBe hα₀ hα₁
    rw [← matrixRpow_eq_cfc_rpow (hAe.posSemidef.add hBe.posSemidef),
      ← matrixRpow_eq_cfc_rpow hAe.posSemidef,
      ← matrixRpow_eq_cfc_rpow hBe.posSemidef, hsum] at h
    exact h
  simp only [one_mul] at hr
  exact le_of_tendsto_of_tendsto hl hr hev

theorem trace_matrixRpow_sum_le {κ : Type*} (s : Finset κ) (M : κ → CMat ι)
    (hM : ∀ j, (M j).PosSemidef) {α : ℝ} (hα₀ : 0 < α) (hα₁ : α < 1) :
    (matrixRpow (∑ j ∈ s, M j) α).trace.re ≤
      ∑ j ∈ s, (matrixRpow (M j) α).trace.re := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    rw [matrixRpow_eq_cfc_rpow Matrix.PosSemidef.zero,
      CFC.zero_rpow hα₀.ne']
    simp
  | @insert j s hjs ih =>
    rw [Finset.sum_insert hjs, Finset.sum_insert hjs]
    have hs : (∑ i ∈ s, M i).PosSemidef :=
      Matrix.posSemidef_sum s (fun i _ => hM i)
    exact (trace_matrixRpow_subadd (hM j) hs hα₀ hα₁).trans
      (add_le_add_right ih _)

theorem matrixRpow_unitary_conjugate (U : Matrix.unitaryGroup ι ℂ)
    {A : CMat ι} (hA : A.PosSemidef) (α : ℝ) :
    matrixRpow (Unitary.conjStarAlgAut ℝ (CMat ι) U A) α =
      Unitary.conjStarAlgAut ℝ (CMat ι) U (matrixRpow A α) := by
  have hUA : (Unitary.conjStarAlgAut ℝ (CMat ι) U A).PosSemidef := by
    change ((U : CMat ι) * A * (U : CMat ι)ᴴ).PosSemidef
    exact hA.mul_mul_conjTranspose_same (U : CMat ι)
  unfold matrixRpow
  exact (StarAlgHomClass.map_cfc
    (Unitary.conjStarAlgAut ℝ (CMat ι) U)
    (fun x : ℝ => Real.rpow x α) A
    (A.finite_real_spectrum.continuousOn _)
    (by
      change Continuous (fun X : CMat ι => (U : CMat ι) * X * (U : CMat ι)ᴴ)
      fun_prop) hA.1 hUA.1).symm

theorem trace_matrixRpow_unitary_conjugate (U : Matrix.unitaryGroup ι ℂ)
    {A : CMat ι} (hA : A.PosSemidef) (α : ℝ) :
    (matrixRpow (Unitary.conjStarAlgAut ℝ (CMat ι) U A) α).trace.re =
      (matrixRpow A α).trace.re := by
  rw [matrixRpow_unitary_conjugate U hA α, Spectral.trace_unitary_conjugate]

theorem trace_matrixRpow_unitary_average_le {κ : Type*} [Fintype κ] [Nonempty κ]
    (U : κ → Matrix.unitaryGroup ι ℂ) {A : CMat ι} (hA : A.PosSemidef)
    {α : ℝ} (hα₀ : 0 < α) (hα₁ : α < 1) :
    (matrixRpow ((Fintype.card κ : ℝ)⁻¹ •
      ∑ j, Unitary.conjStarAlgAut ℝ (CMat ι) (U j) A) α).trace.re ≤
      Real.rpow (Fintype.card κ : ℝ) (1 - α) * (matrixRpow A α).trace.re := by
  classical
  let v : ℝ := Fintype.card κ
  have hv : 0 < v := by dsimp [v]; exact_mod_cast Fintype.card_pos
  let M : κ → CMat ι := fun j => Unitary.conjStarAlgAut ℝ (CMat ι) (U j) A
  have hM (j : κ) : (M j).PosSemidef := by
    change ((U j : CMat ι) * A * (U j : CMat ι)ᴴ).PosSemidef
    exact hA.mul_mul_conjTranspose_same (U j : CMat ι)
  have hs : (∑ j, M j).PosSemidef :=
    Matrix.posSemidef_sum Finset.univ (fun j _ => hM j)
  have hsum : (matrixRpow (∑ j, M j) α).trace.re ≤
      v * (matrixRpow A α).trace.re := by
    calc
      _ ≤ ∑ j, (matrixRpow (M j) α).trace.re :=
        trace_matrixRpow_sum_le Finset.univ M hM hα₀ hα₁
      _ = v * (matrixRpow A α).trace.re := by
        simp only [M, trace_matrixRpow_unitary_conjugate _ hA α]
        simp [v, nsmul_eq_mul]
  have hcoef : Real.rpow v⁻¹ α * v = Real.rpow v (1 - α) := by
    simp only [Real.rpow_eq_pow]
    rw [← Real.rpow_neg_eq_inv_rpow v α]
    calc
      v ^ (-α) * v = v ^ (-α + 1) := by
        simpa only [Real.rpow_one] using (Real.rpow_add hv (-α) 1).symm
      _ = v ^ (1 - α) := by congr 1; ring
  change (matrixRpow (v⁻¹ • ∑ j, M j) α).trace.re ≤
    Real.rpow v (1 - α) * (matrixRpow A α).trace.re
  rw [matrixRpow_smul _ hs α (inv_pos.mpr hv), Matrix.trace_smul,
    Complex.smul_re, smul_eq_mul]
  calc
    _ ≤ Real.rpow v⁻¹ α * (v * (matrixRpow A α).trace.re) :=
      mul_le_mul_of_nonneg_left hsum (Real.rpow_nonneg (inv_nonneg.mpr hv.le) α)
    _ = _ := by rw [← mul_assoc, hcoef]

theorem trace_matrixRpow_pinching_le {κ : Type*} [Fintype κ] [Nonempty κ]
    [DecidableEq κ] (P : κ → CMat ι)
    (hP : ∀ i, (P i)ᴴ = P i)
    (hmul : ∀ i j, P i * P j = if i = j then P i else 0)
    (hsum : ∑ i, P i = 1) {A : CMat ι} (hA : A.PosSemidef)
    {α : ℝ} (hα₀ : 0 < α) (hα₁ : α < 1) :
    (matrixRpow (∑ i, P i * A * P i) α).trace.re ≤
      Real.rpow (Fintype.card κ : ℝ) (1 - α) * (matrixRpow A α).trace.re := by
  obtain ⟨U, hU⟩ := finite_pinching_unitary_average P hP hmul hsum A
  rw [hU]
  exact trace_matrixRpow_unitary_average_le U hA hα₀ hα₁

theorem pinching_matrix_sandwich_eq {κ : Type*} [Fintype κ]
    (P : κ → CMat ι) (S A : CMat ι) (hcomm : ∀ i, Commute S (P i)) :
    (∑ i, P i * (S * A * S) * P i) = S * (∑ i, P i * A * P i) * S := by
  simp only [Matrix.mul_sum, Matrix.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  calc
    P i * (S * A * S) * P i = (P i * S) * A * (S * P i) := by
      simp only [Matrix.mul_assoc]
    _ = (S * P i) * A * (P i * S) :=
      congrArg₂ (fun B C : CMat ι => B * A * C)
        (hcomm i).symm.eq (hcomm i).eq
    _ = S * (P i * A * P i) * S := by simp only [Matrix.mul_assoc]

theorem trace_matrixRpow_sandwich_pinching_le {κ : Type*} [Fintype κ]
    [Nonempty κ] [DecidableEq κ] (P : κ → CMat ι)
    (hP : ∀ i, (P i)ᴴ = P i)
    (hmul : ∀ i j, P i * P j = if i = j then P i else 0)
    (hsum : ∑ i, P i = 1) (S : CMat ι) (hS : S.IsHermitian)
    (hcomm : ∀ i, Commute S (P i)) {A : CMat ι} (hA : A.PosSemidef)
    {α : ℝ} (hα₀ : 0 < α) (hα₁ : α < 1) :
    (matrixRpow (S * (∑ i, P i * A * P i) * S) α).trace.re ≤
      Real.rpow (Fintype.card κ : ℝ) (1 - α) *
        (matrixRpow (S * A * S) α).trace.re := by
  have hSA : (S * A * S).PosSemidef := by
    simpa only [hS.eq] using hA.mul_mul_conjTranspose_same S
  have h := trace_matrixRpow_pinching_le P hP hmul hsum hSA hα₀ hα₁
  rw [pinching_matrix_sandwich_eq P S A hcomm] at h
  exact h

theorem sandwichedTrace_pinching_le {κ : Type*} [Fintype κ] [Nonempty κ]
    [DecidableEq κ] (P : κ → CMat ι)
    (hP : ∀ i, (P i)ᴴ = P i)
    (hmul : ∀ i j, P i * P j = if i = j then P i else 0)
    (hsum : ∑ i, P i = 1) {ρ σ : CMat ι} (hρ : ρ.PosSemidef)
    {α : ℝ} (hα₀ : 0 < α) (hα₁ : α < 1)
    (hcomm : ∀ i, Commute (matrixRpow σ ((1 - α) / (2 * α))) (P i)) :
    sandwichedTrace (∑ i, P i * ρ * P i) σ α ≤
      Real.rpow (Fintype.card κ : ℝ) (1 - α) * sandwichedTrace ρ σ α := by
  have hS : (matrixRpow σ ((1 - α) / (2 * α))).IsHermitian :=
    cfc_predicate (p := IsSelfAdjoint)
      (fun x : ℝ => Real.rpow x ((1 - α) / (2 * α))) σ
  exact trace_matrixRpow_sandwich_pinching_le P hP hmul hsum _ hS hcomm hρ hα₀ hα₁

theorem below_one_logTrace_pinching_bound {x y v α : ℝ}
    (hx : 0 < x) (hy : 0 < y) (hv : 0 < v) (hα : α < 1)
    (hbound : y ≤ Real.rpow v (1 - α) * x) :
    logTwo x / (α - 1) - logTwo v ≤ logTwo y / (α - 1) := by
  have hlog := Real.log_le_log hy hbound
  simp only [Real.rpow_eq_pow] at hlog
  rw [Real.log_mul (Real.rpow_pos_of_pos hv _).ne' hx.ne',
    Real.log_rpow hv] at hlog
  have hl : logTwo y ≤ (1 - α) * logTwo v + logTwo x := by
    calc
      logTwo y = Real.log y / Real.log 2 := rfl
      _ ≤ ((1 - α) * Real.log v + Real.log x) / Real.log 2 :=
        div_le_div_of_nonneg_right hlog (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
      _ = (1 - α) * logTwo v + logTwo x := by unfold logTwo; ring
  have hden : α - 1 < 0 := by linarith
  apply (le_div_iff_of_neg hden).mpr
  calc
    logTwo y ≤ (1 - α) * logTwo v + logTwo x := hl
    _ = (logTwo x / (α - 1) - logTwo v) * (α - 1) := by
      field_simp [hden.ne]
      ring

theorem sandwichedDivergence_pinching_lower {κ : Type*} [Fintype κ]
    [Nonempty κ] [DecidableEq κ] (P : κ → CMat ι)
    (hP : ∀ i, (P i)ᴴ = P i)
    (hmul : ∀ i j, P i * P j = if i = j then P i else 0)
    (hsum : ∑ i, P i = 1) {ρ σ : CMat ι} (hρ : ρ.PosSemidef)
    {α : ℝ} (hα₀ : 0 < α) (hα₁ : α < 1)
    (hcomm : ∀ i, Commute (matrixRpow σ ((1 - α) / (2 * α))) (P i))
    (htrace : 0 < sandwichedTrace ρ σ α)
    (hpinchedTrace : 0 < sandwichedTrace (∑ i, P i * ρ * P i) σ α) :
    sandwichedDivergence ρ σ α - (logTwo (Fintype.card κ : ℝ) : EReal) ≤
      sandwichedDivergence (∑ i, P i * ρ * P i) σ α := by
  have hb := sandwichedTrace_pinching_le P hP hmul hsum hρ hα₀ hα₁ hcomm
  have hl := below_one_logTrace_pinching_bound htrace hpinchedTrace
    (show (0 : ℝ) < Fintype.card κ by exact_mod_cast Fintype.card_pos) hα₁ hb
  have ho : sandwichedDivergence ρ σ α =
      ((logTwo (sandwichedTrace ρ σ α) / (α - 1) : ℝ) : EReal) := by
    simp [sandwichedDivergence, hα₁.ne, not_lt.mpr hα₁.le, htrace.ne']
    rw [← EReal.coe_one, ← EReal.coe_sub, ← EReal.coe_div]
  have hp : sandwichedDivergence (∑ i, P i * ρ * P i) σ α =
      ((logTwo (sandwichedTrace (∑ i, P i * ρ * P i) σ α) / (α - 1) : ℝ) : EReal) := by
    simp [sandwichedDivergence, hα₁.ne, not_lt.mpr hα₁.le, hpinchedTrace.ne']
    rw [← EReal.coe_one, ← EReal.coe_sub, ← EReal.coe_div]
  rw [ho, hp, ← EReal.coe_sub]
  exact EReal.coe_le_coe_iff.mpr hl

theorem inverse_half_trace_regularization_tendsto {ρ σ : CMat ι}
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) (hs : SupportLE ρ σ) :
    Tendsto
      (fun ε : ℝ => tracePair (matrixRpow ρ (3 / 2 : ℝ))
        (matrixRpow (σ + ε • (1 : CMat ι)) (-1 / 2 : ℝ)))
      (𝓝 0) (𝓝 (petzTrace ρ σ (3 / 2 : ℝ))) := by
  let U := Spectral.overlapUnitary hρ.1 hσ.1
  have hf (ε : ℝ) : tracePair (matrixRpow ρ (3 / 2 : ℝ))
      (matrixRpow (σ + ε • (1 : CMat ι)) (-1 / 2 : ℝ)) =
        ∑ i, ∑ j, Real.rpow (hρ.1.eigenvalues i) (3 / 2 : ℝ) *
          Real.rpow (hσ.1.eigenvalues j + ε) (-1 / 2 : ℝ) *
            Spectral.overlapWeight U i j := by
    rw [matrixRpow_add_scalar σ hσ.1]
    unfold tracePair matrixRpow
    exact Spectral.trace_cfc_mul_cfc_eq_overlap _ _ hρ.1 hσ.1
  have hp : petzTrace ρ σ (3 / 2 : ℝ) =
      ∑ i, ∑ j, Real.rpow (hρ.1.eigenvalues i) (3 / 2 : ℝ) *
        Real.rpow (hσ.1.eigenvalues j) (-1 / 2 : ℝ) *
          Spectral.overlapWeight U i j := by
    unfold petzTrace tracePair matrixRpow
    rw [Spectral.trace_cfc_mul_cfc_eq_overlap _ _ hρ.1 hσ.1]
    norm_num <;> rfl
  simp_rw [hf]
  rw [hp]
  apply tendsto_finset_sum
  intro i hi
  apply tendsto_finset_sum
  intro j hj
  by_cases hr : hρ.1.eigenvalues i = 0
  · simp [hr, Real.zero_rpow (by norm_num : (3 / 2 : ℝ) ≠ 0)]
  by_cases hq : hσ.1.eigenvalues j = 0
  · have hw := overlapWeight_zero_of_alternative_kernel hρ.1 hσ.1 hs i j hr hq
    change Spectral.overlapWeight U i j = 0 at hw
    rw [hw]
    simp only [mul_zero]
    exact tendsto_const_nhds
  have hshift : Tendsto (fun ε : ℝ => hσ.1.eigenvalues j + ε) (𝓝 0)
      (𝓝 (hσ.1.eigenvalues j)) := by
    simpa only [add_zero, id_eq] using
      ((tendsto_const_nhds : Tendsto (fun _ : ℝ => hσ.1.eigenvalues j)
          (𝓝 (0 : ℝ)) (𝓝 (hσ.1.eigenvalues j))).add
        (tendsto_id : Tendsto (fun ε : ℝ => ε) (𝓝 (0 : ℝ)) (𝓝 (0 : ℝ))))
  have hpow := (Real.continuousAt_rpow_const (hσ.1.eigenvalues j) (-1 / 2 : ℝ)
    (Or.inl hq)).tendsto.comp hshift
  exact (hpow.const_mul (Real.rpow (hρ.1.eigenvalues i) (3 / 2 : ℝ))).mul_const
    (Spectral.overlapWeight U i j)

theorem inverse_half_self_trace_le_one {ρ : CMat ι} (hρ : IsState ρ)
    {η : ℝ} (hη : 0 ≤ η) :
    tracePair (matrixRpow ρ (3 / 2 : ℝ))
      (matrixRpow (ρ + η • (1 : CMat ι)) (-1 / 2 : ℝ)) ≤ 1 := by
  rw [matrixRpow_add_scalar ρ hρ.1.1]
  unfold tracePair matrixRpow
  rw [← cfc_mul (p := IsSelfAdjoint) (fun x : ℝ => Real.rpow x (3 / 2 : ℝ))
    (fun x : ℝ => Real.rpow (x + η) (-1 / 2 : ℝ)) ρ
      (ρ.finite_real_spectrum.continuousOn _) (ρ.finite_real_spectrum.continuousOn _),
    Spectral.trace_cfc_eq_sum _ hρ.1.1]
  calc
    _ ≤ ∑ i, hρ.1.1.eigenvalues i := by
      apply Finset.sum_le_sum
      intro i hi
      exact inverse_half_scalar_shift_budget (hρ.1.eigenvalues_nonneg i) hη
    _ = 1 := by rw [← Spectral.trace_eq_sum_eigenvalues_re hρ.1.1, hρ.2]; rfl

theorem inverse_half_regularized_trace_le {ρ σ : CMat ι}
    (hρ : IsState ρ) (hσ : σ.PosSemidef) {a ε : ℝ} (ha : 0 < a) (hε : 0 < ε)
    (hdom : LoewnerLE ρ (a • σ)) :
    tracePair (matrixRpow ρ (3 / 2 : ℝ))
      (matrixRpow (σ + ε • (1 : CMat ι)) (-1 / 2 : ℝ)) ≤ Real.rpow a (1 / 2 : ℝ) := by
  have hη : 0 < a * ε := mul_pos ha hε
  have hrpos : (ρ + (a * ε) • (1 : CMat ι)).PosDef :=
    Matrix.isStrictlyPositive_iff_posDef.mp
      (IsStrictlyPositive.nonneg_add hρ.1.nonneg
        (IsStrictlyPositive.smul hη isStrictlyPositive_one))
  have hspos : (σ + ε • (1 : CMat ι)).PosSemidef :=
    hσ.add (Matrix.PosSemidef.one.smul hε.le)
  have hdomreg :
      (a • (σ + ε • (1 : CMat ι)) -
        (ρ + (a * ε) • (1 : CMat ι))).PosSemidef := by
    have hid : a • (σ + ε • (1 : CMat ι)) -
        (ρ + (a * ε) • (1 : CMat ι)) = a • σ - ρ := by
      rw [smul_add, smul_smul]
      abel
    rw [hid]
    exact hdom
  have hop := inverse_half_power_antitone hrpos hdomreg
  change (matrixRpow (ρ + (a * ε) • (1 : CMat ι)) (-1 / 2 : ℝ) -
    matrixRpow (a • (σ + ε • (1 : CMat ι))) (-1 / 2 : ℝ)).PosSemidef at hop
  rw [matrixRpow_smul _ hspos _ ha] at hop
  have hrpow : (matrixRpow ρ (3 / 2 : ℝ)).PosSemidef := by
    have hp := Matrix.nonneg_iff_posSemidef.mp
      (CFC.rpow_nonneg : 0 ≤ CFC.rpow ρ (3 / 2 : ℝ))
    rw [CFC.rpow_eq_cfc_real hρ.1.nonneg] at hp
    simpa only [matrixRpow, Real.rpow_eq_pow] using hp
  have ht := operator_trace_mul_nonneg hrpow hop
  simp only [Matrix.mul_sub, Matrix.mul_smul, Matrix.trace_sub, Matrix.trace_smul,
    Complex.sub_re, Complex.smul_re, smul_eq_mul] at ht
  have hinner : Real.rpow a (-1 / 2 : ℝ) *
      tracePair (matrixRpow ρ (3 / 2 : ℝ))
        (matrixRpow (σ + ε • (1 : CMat ι)) (-1 / 2 : ℝ)) ≤ 1 := by
    apply (show Real.rpow a (-1 / 2 : ℝ) *
        tracePair (matrixRpow ρ (3 / 2 : ℝ))
          (matrixRpow (σ + ε • (1 : CMat ι)) (-1 / 2 : ℝ)) ≤
        tracePair (matrixRpow ρ (3 / 2 : ℝ))
          (matrixRpow (ρ + (a * ε) • (1 : CMat ι)) (-1 / 2 : ℝ)) from
      sub_nonneg.mp ht).trans
    exact inverse_half_self_trace_le_one hρ hη.le
  have hc : Real.rpow a (1 / 2 : ℝ) * Real.rpow a (-1 / 2 : ℝ) = 1 := by
    simp only [Real.rpow_eq_pow]
    rw [← Real.rpow_add ha]
    norm_num
  have hm := mul_le_mul_of_nonneg_left (a := Real.rpow a (1 / 2 : ℝ)) hinner
    (show 0 ≤ Real.rpow a (1 / 2 : ℝ) from (Real.rpow_pos_of_pos ha _).le)
  simpa only [← mul_assoc, hc, one_mul, mul_one] using hm

theorem petzTrace_three_halves_le_of_domination {ρ σ : CMat ι}
    (hρ : IsState ρ) (hσ : σ.PosSemidef) {a : ℝ} (ha : 0 < a)
    (hdom : LoewnerLE ρ (a • σ)) :
    petzTrace ρ σ (3 / 2 : ℝ) ≤ Real.rpow a (1 / 2 : ℝ) := by
  have hs := supportLE_of_real_psd_domination hρ.1 hdom
  have hlim := (inverse_half_trace_regularization_tendsto hρ.1 hσ hs).mono_left
    (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from inf_le_left)
  have hev : ∀ᶠ ε : ℝ in 𝓝[>] 0,
      tracePair (matrixRpow ρ (3 / 2 : ℝ))
        (matrixRpow (σ + ε • (1 : CMat ι)) (-1 / 2 : ℝ)) ≤ Real.rpow a (1 / 2 : ℝ) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact inverse_half_regularized_trace_le hρ hσ ha hε hdom
  exact le_of_tendsto hlim hev

theorem nsLaw_positive_half_order_bound {ρ σ : CMat ι}
    (hρ : IsState ρ) (hσ : σ.PosSemidef) {a : ℝ} (ha : 0 < a)
    (hdom : LoewnerLE ρ (a • σ)) :
    (nsLaw ρ σ hρ hσ).expect
      (fun z => Real.exp ((Real.log 2 / 2) * nsLikelihood ρ σ z)) ≤
        Real.rpow a (1 / 2 : ℝ) := by
  have hs := supportLE_of_real_psd_domination hρ.1 hdom
  have heq : (nsLaw ρ σ hρ hσ).expect
      (fun z => Real.exp ((Real.log 2 / 2) * nsLikelihood ρ σ z)) =
        petzTrace ρ σ (3 / 2 : ℝ) := by
    calc
      _ = (nsLaw ρ σ hρ hσ).expect (fun z =>
          Real.exp (((3 / 2 : ℝ) - 1) * Real.log 2 * nsLikelihood ρ σ z)) := by
        congr 1
        funext z
        congr 1
        ring
      _ = _ := nsLaw_exp_eq_petzTrace ρ σ hρ hσ hs (by norm_num)
  rw [heq]
  exact petzTrace_three_halves_le_of_domination hρ hσ ha hdom

theorem umegakiReal_le_log_of_domination {ρ σ : CMat ι}
    (hρ : IsState ρ) (hσ : σ.PosSemidef) {a : ℝ} (ha : 0 < a)
    (hdom : LoewnerLE ρ (a • σ)) :
    umegakiReal ρ σ ≤ logTwo a := by
  let P := nsLaw ρ σ hρ hσ
  have hm : P.mean (fun z => (Real.log 2 / 2) * nsLikelihood ρ σ z) =
      (Real.log 2 / 2) * umegakiReal ρ σ := by
    unfold FiniteLaw.mean
    rw [P.expect_smul]
    exact congrArg (fun x : ℝ => (Real.log 2 / 2) * x)
      (nsLaw_mean_eq_umegakiReal ρ σ hρ hσ)
  have hj := P.exp_mean_le_expect_exp
    (fun z => (Real.log 2 / 2) * nsLikelihood ρ σ z)
  rw [hm] at hj
  have hh := nsLaw_positive_half_order_bound hρ hσ ha hdom
  have hl := Real.log_le_log (Real.exp_pos _) (hj.trans hh)
  rw [Real.log_exp, Real.rpow_eq_pow, Real.log_rpow ha] at hl
  unfold logTwo
  apply (le_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mpr
  nlinarith

theorem petzTrace_half_le_sqrt_trace {ρ σ : CMat ι}
    (hρ : IsState ρ) (hσ : σ.PosSemidef) :
    petzTrace ρ σ (1 / 2 : ℝ) ≤ Real.sqrt (Matrix.trace σ).re := by
  let U := Spectral.overlapUnitary hρ.1.1 hσ.1
  let f : ι × ι → ℝ := fun z => Real.sqrt (hρ.1.1.eigenvalues z.1) *
    Real.sqrt (Spectral.overlapWeight U z.1 z.2)
  let g : ι × ι → ℝ := fun z => Real.sqrt (hσ.1.eigenvalues z.2) *
    Real.sqrt (Spectral.overlapWeight U z.1 z.2)
  have hf (z : ι × ι) : f z ^ 2 = hρ.1.1.eigenvalues z.1 *
      Spectral.overlapWeight U z.1 z.2 := by
    dsimp [f]
    rw [mul_pow, Real.sq_sqrt (hρ.1.eigenvalues_nonneg z.1),
      Real.sq_sqrt (Spectral.overlapWeight_nonneg U z.1 z.2)]
  have hg (z : ι × ι) : g z ^ 2 = hσ.1.eigenvalues z.2 *
      Spectral.overlapWeight U z.1 z.2 := by
    dsimp [g]
    rw [mul_pow, Real.sq_sqrt (hσ.eigenvalues_nonneg z.2),
      Real.sq_sqrt (Spectral.overlapWeight_nonneg U z.1 z.2)]
  have hfg (z : ι × ι) : f z * g z =
      Real.sqrt (hρ.1.1.eigenvalues z.1) * Real.sqrt (hσ.1.eigenvalues z.2) *
        Spectral.overlapWeight U z.1 z.2 := by
    calc
      f z * g z =
          Real.sqrt (hρ.1.1.eigenvalues z.1) * Real.sqrt (hσ.1.eigenvalues z.2) *
            (Real.sqrt (Spectral.overlapWeight U z.1 z.2)) ^ 2 := by dsimp [f, g]; ring
      _ = _ := by rw [Real.sq_sqrt (Spectral.overlapWeight_nonneg U z.1 z.2)]
  have hfsum : ∑ z, f z ^ 2 = 1 := by
    calc
      _ = ∑ z, nsWeight ρ σ z := by
        apply Finset.sum_congr rfl
        rintro ⟨i, j⟩ hi
        rw [hf, nsWeight_eq_overlap hρ.1.1 hσ.1]
      _ = 1 := nsWeight_sum hρ hσ.1
  have hgsum : ∑ z, g z ^ 2 = (Matrix.trace σ).re := by
    simp_rw [hg]
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    simp_rw [← Finset.mul_sum, Spectral.overlapWeight_sum_col, mul_one]
    exact (Spectral.trace_eq_sum_eigenvalues_re hσ.1).symm
  have hp : petzTrace ρ σ (1 / 2 : ℝ) = ∑ z, f z * g z := by
    unfold petzTrace tracePair matrixRpow
    rw [Spectral.trace_cfc_mul_cfc_eq_overlap _ _ hρ.1.1 hσ.1]
    simp only [show (1 - (1 / 2 : ℝ)) = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow]
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    simpa only [U, Real.rpow_eq_pow, ← Real.sqrt_eq_rpow] using (hfg (i, j)).symm
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ f g
  change (∑ z, f z * g z) ^ 2 ≤ (∑ z, f z ^ 2) * ∑ z, g z ^ 2 at hcs
  rw [← hp, hfsum, hgsum, one_mul] at hcs
  have ht : 0 ≤ (Matrix.trace σ).re := (Complex.nonneg_iff.mp hσ.trace_nonneg).1
  nlinarith [Real.sqrt_nonneg (Matrix.trace σ).re, Real.sq_sqrt ht]

theorem nsLaw_negative_half_order_bound {ρ σ : CMat ι}
    (hρ : IsState ρ) (hσ : σ.PosSemidef) (hs : SupportLE ρ σ) :
    (nsLaw ρ σ hρ hσ).expect
      (fun z => Real.exp (-(Real.log 2 / 2) * nsLikelihood ρ σ z)) ≤
        Real.sqrt (Matrix.trace σ).re := by
  have heq : (nsLaw ρ σ hρ hσ).expect
      (fun z => Real.exp (-(Real.log 2 / 2) * nsLikelihood ρ σ z)) =
        petzTrace ρ σ (1 / 2 : ℝ) := by
    calc
      _ = (nsLaw ρ σ hρ hσ).expect (fun z =>
          Real.exp (((1 / 2 : ℝ) - 1) * Real.log 2 * nsLikelihood ρ σ z)) := by
        congr 1
        funext z
        congr 1
        ring
      _ = _ := nsLaw_exp_eq_petzTrace ρ σ hρ hσ hs (by norm_num)
  rw [heq]
  exact petzTrace_half_le_sqrt_trace hρ hσ

theorem alternative_trace_pos_of_domination {ρ σ : CMat ι}
    (hρ : IsState ρ) {a : ℝ} (ha : 0 < a) (hdom : LoewnerLE ρ (a • σ)) :
    0 < (Matrix.trace σ).re := by
  have hdom' : (a • σ - ρ).PosSemidef := hdom
  have ht := (Complex.nonneg_iff.mp hdom'.trace_nonneg).1
  simp only [LoewnerLE, Matrix.trace_sub, Matrix.trace_smul,
    Complex.sub_re, Complex.smul_re, hρ.2, Complex.one_re, smul_eq_mul] at ht
  nlinarith

theorem umegakiReal_ge_neg_log_trace {ρ σ : CMat ι}
    (hρ : IsState ρ) (hσ : σ.PosSemidef) (hs : SupportLE ρ σ)
    (htr : 0 < (Matrix.trace σ).re) :
    -logTwo (Matrix.trace σ).re ≤ umegakiReal ρ σ := by
  let S := (Matrix.trace σ).re
  let U := Spectral.overlapUnitary hρ.1.1 hσ.1
  let P := nsLaw ρ σ hρ hσ
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hsumq : (∑ z : ι × ι,
      (hσ.1.eigenvalues z.2 / S) * Spectral.overlapWeight U z.1 z.2) = 1 := by
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    simp_rw [← Finset.mul_sum, Spectral.overlapWeight_sum_col, mul_one]
    rw [← Finset.sum_div, ← Spectral.trace_eq_sum_eigenvalues_re hσ.1]
    exact div_self htr.ne'
  have hpoint (z : ι × ι) :
      P.weight z - (hσ.1.eigenvalues z.2 / S) * Spectral.overlapWeight U z.1 z.2 ≤
        P.weight z * (Real.log 2 * nsLikelihood ρ σ z + Real.log S) := by
    rcases z with ⟨i, j⟩
    have hz : hσ.1.eigenvalues j = 0 →
        hρ.1.1.eigenvalues i * Spectral.overlapWeight U i j = 0 := by
      intro hq0
      by_cases hr0 : hρ.1.1.eigenvalues i = 0
      · simp [hr0]
      · rw [overlapWeight_zero_of_alternative_kernel hρ.1.1 hσ.1 hs i j hr0 hq0]
        simp
    have hp := weighted_normalized_log_lower (hρ.1.eigenvalues_nonneg i)
      (hσ.eigenvalues_nonneg j) htr (Spectral.overlapWeight_nonneg U i j) hz
    change nsWeight ρ σ (i, j) -
      (hσ.1.eigenvalues j / S) * Spectral.overlapWeight U i j ≤
        nsWeight ρ σ (i, j) *
          (Real.log 2 * nsLikelihood ρ σ (i, j) + Real.log S)
    rw [nsWeight_eq_overlap hρ.1.1 hσ.1]
    simp only [nsLikelihood, spectrumValue_of_isHermitian hρ.1.1,
      spectrumValue_of_isHermitian hσ.1, logTwo]
    have hid : Real.log 2 *
        (Real.log (hρ.1.1.eigenvalues i) / Real.log 2 -
          Real.log (hσ.1.eigenvalues j) / Real.log 2) + Real.log S =
        Real.log (hρ.1.1.eigenvalues i) - Real.log (hσ.1.eigenvalues j) + Real.log S := by
      field_simp [hlog2.ne'] <;> ring
    rw [hid]
    exact hp
  have hpos : 0 ≤ P.expect
      (fun z => Real.log 2 * nsLikelihood ρ σ z + Real.log S) := by
    calc
      0 = (∑ z, P.weight z) - ∑ z : ι × ι,
          (hσ.1.eigenvalues z.2 / S) * Spectral.overlapWeight U z.1 z.2 := by
        rw [P.sum_weight, hsumq]
        ring
      _ = ∑ z : ι × ι, (P.weight z -
          (hσ.1.eigenvalues z.2 / S) * Spectral.overlapWeight U z.1 z.2) := by
        rw [Finset.sum_sub_distrib]
      _ ≤ P.expect (fun z => Real.log 2 * nsLikelihood ρ σ z + Real.log S) :=
        Finset.sum_le_sum fun z _ => hpoint z
  have hmean : P.expect (nsLikelihood ρ σ) = umegakiReal ρ σ :=
    nsLaw_mean_eq_umegakiReal ρ σ hρ hσ
  rw [P.expect_add, P.expect_smul, P.expect_const, hmean] at hpos
  unfold logTwo
  rw [← neg_div]
  apply (div_le_iff₀ hlog2).mpr
  dsimp [S] at hpos
  linarith

end MatrixUnnormalizedEntropy

theorem logTwo_two_rpow (x : ℝ) : logTwo (Real.rpow 2 x) = x := by
  unfold logTwo
  rw [Real.rpow_eq_pow, Real.log_rpow (by norm_num : (0 : ℝ) < 2)]
  field_simp [ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 2))]

theorem nsLaw_absolute_half_order_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    {ρ σ : CMat ι} (hρ : IsState ρ) (hσ : σ.PosSemidef) {a : ℝ}
    (ha : 0 < a) (hdom : LoewnerLE ρ (a • σ))
    (htrace : (Matrix.trace σ).re ≤ a) (c : ℝ) :
    (nsLaw ρ σ hρ hσ).expect (fun z =>
      Real.exp ((Real.log 2 / 2) * |nsLikelihood ρ σ z - c|)) ≤
        2 * Real.sqrt a * Real.exp ((Real.log 2 / 2) * |c|) := by
  let P := nsLaw ρ σ hρ hσ
  let β : ℝ := Real.log 2 / 2
  have hβ : 0 ≤ β := by dsimp [β]; positivity
  have hs := supportLE_of_real_psd_domination hρ.1 hdom
  have hpos : P.expect (fun z => Real.exp (β * nsLikelihood ρ σ z)) ≤
      Real.sqrt a := by
    simpa only [P, β, Real.sqrt_eq_rpow, Real.rpow_eq_pow] using
      nsLaw_positive_half_order_bound hρ hσ ha hdom
  have hneg : P.expect (fun z => Real.exp (-β * nsLikelihood ρ σ z)) ≤
      Real.sqrt a := (nsLaw_negative_half_order_bound hρ hσ hs).trans
        (Real.sqrt_le_sqrt htrace)
  have hshiftpos : P.expect (fun z => Real.exp (β * (nsLikelihood ρ σ z - c))) =
      Real.exp (-β * c) * P.expect (fun z => Real.exp (β * nsLikelihood ρ σ z)) := by
    have hid (z : ι × ι) : Real.exp (β * (nsLikelihood ρ σ z - c)) =
        Real.exp (-β * c) * Real.exp (β * nsLikelihood ρ σ z) := by
      rw [← Real.exp_add]
      congr 1
      ring
    simp_rw [hid]
    exact P.expect_smul _ _
  have hshiftneg : P.expect (fun z => Real.exp (-β * (nsLikelihood ρ σ z - c))) =
      Real.exp (β * c) * P.expect (fun z => Real.exp (-β * nsLikelihood ρ σ z)) := by
    have hid (z : ι × ι) : Real.exp (-β * (nsLikelihood ρ σ z - c)) =
        Real.exp (β * c) * Real.exp (-β * nsLikelihood ρ σ z) := by
      rw [← Real.exp_add]
      congr 1
      ring
    simp_rw [hid]
    exact P.expect_smul _ _
  have hexppos : Real.exp (β * c) ≤ Real.exp (β * |c|) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (le_abs_self c) hβ)
  have hexpneg : Real.exp (-β * c) ≤ Real.exp (β * |c|) := by
    apply Real.exp_le_exp.mpr
    have h := mul_le_mul_of_nonneg_left (neg_le_abs c) hβ
    nlinarith
  calc
    P.expect (fun z => Real.exp (β * |nsLikelihood ρ σ z - c|)) ≤
        P.expect (fun z => Real.exp (β * (nsLikelihood ρ σ z - c)) +
          Real.exp (-β * (nsLikelihood ρ σ z - c))) := by
      apply P.expect_mono
      intro z
      by_cases hz : 0 ≤ nsLikelihood ρ σ z - c
      · rw [abs_of_nonneg hz]
        exact le_add_of_nonneg_right (Real.exp_pos _).le
      · rw [abs_of_nonpos (le_of_lt (lt_of_not_ge hz))]
        have hid : β * -(nsLikelihood ρ σ z - c) =
            -β * (nsLikelihood ρ σ z - c) := by ring
        rw [hid]
        exact le_add_of_nonneg_left (Real.exp_pos _).le
    _ = Real.exp (-β * c) * P.expect (fun z => Real.exp (β * nsLikelihood ρ σ z)) +
        Real.exp (β * c) * P.expect (fun z => Real.exp (-β * nsLikelihood ρ σ z)) := by
      rw [P.expect_add, hshiftpos, hshiftneg]
    _ ≤ Real.exp (-β * c) * Real.sqrt a + Real.exp (β * c) * Real.sqrt a :=
      add_le_add (mul_le_mul_of_nonneg_left hpos (Real.exp_pos _).le)
        (mul_le_mul_of_nonneg_left hneg (Real.exp_pos _).le)
    _ ≤ Real.exp (β * |c|) * Real.sqrt a + Real.exp (β * |c|) * Real.sqrt a :=
      add_le_add (mul_le_mul_of_nonneg_right hexpneg (Real.sqrt_nonneg a))
        (mul_le_mul_of_nonneg_right hexppos (Real.sqrt_nonneg a))
    _ = 2 * Real.sqrt a * Real.exp (β * |c|) := by ring

theorem physical_family_entropy_bounds {d : ℕ} {F : QuantumFamilies d}
    (hF : PhysicalAssumptions F) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n, 0 < n → ∀ ρ ∈ F.null n,
      ∀ σ ∈ F.alternative n, SupportLE ρ σ ∧ 0 < (Matrix.trace σ).re ∧
        -(C * (n : ℝ)) ≤ umegakiReal ρ σ ∧ umegakiReal ρ σ ≤ C * (n : ℝ) := by
  obtain ⟨C, hC⟩ := hF.linear_growth
  have hpairs (n : ℕ) (hn : 0 < n) (ρ : QMat d n) (hρ : ρ ∈ F.null n)
      (σ : QMat d n) (hσ : σ ∈ F.alternative n) :
      SupportLE ρ σ ∧ 0 < (Matrix.trace σ).re ∧
        -(C * (n : ℝ)) ≤ umegakiReal ρ σ ∧ umegakiReal ρ σ ≤ C * (n : ℝ) := by
    have hr := hF.null_states n hn ρ hρ
    have hs := hF.alternative_positive n hn σ hσ
    obtain ⟨hdom, hlog⟩ := hC n hn ρ hρ σ hσ
    have ha : 0 < Real.rpow 2 (C * (n : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
    have hdomr : LoewnerLE ρ ((Real.rpow 2 (C * (n : ℝ))) • σ) := by
      simpa only [real_complex_smul_matrix] using hdom
    have hsupport := supportLE_of_psd_domination hr.1 hdom
    have htrace := alternative_trace_pos_of_domination hr ha hdomr
    refine ⟨hsupport, htrace, ?_, ?_⟩
    · exact (neg_le_neg hlog).trans
        (umegakiReal_ge_neg_log_trace hr hs hsupport htrace)
    · simpa only [logTwo_two_rpow] using
        umegakiReal_le_log_of_domination hr hs ha hdomr
  have hnonneg : 0 ≤ C := by
    obtain ⟨ρ, hρ⟩ := hF.null_nonempty 1 (by norm_num)
    obtain ⟨σ, hσ⟩ := hF.alternative_nonempty 1 (by norm_num)
    have hp := hpairs 1 (by norm_num) ρ hρ σ hσ
    norm_num at hp
    linarith [hp.2.2.1, hp.2.2.2]
  exact ⟨C, hnonneg, hpairs⟩

theorem absolute_weighted_square_le_exp {β t x : ℝ} (hβ : 0 < β)
    (ht : t ≤ β / 2) :
    x ^ 2 * Real.exp (t * |x|) ≤ (8 / β ^ 2) * Real.exp (β * |x|) := by
  have hsq : x ^ 2 ≤ (8 / β ^ 2) * Real.exp (β * |x| / 2) := by
    have h := half_square_le_exp (show 0 ≤ β * |x| / 2 by positivity)
    have hm := mul_le_mul_of_nonneg_left h (by positivity : 0 ≤ 8 / β ^ 2)
    have hid : (8 / β ^ 2) * ((β * |x| / 2) ^ 2 / 2) = x ^ 2 := by
      rw [div_pow, mul_pow, sq_abs]
      field_simp [hβ.ne']
      ring
    rw [hid] at hm
    exact hm
  calc
    x ^ 2 * Real.exp (t * |x|) ≤
        ((8 / β ^ 2) * Real.exp (β * |x| / 2)) * Real.exp (t * |x|) :=
      mul_le_mul_of_nonneg_right hsq (Real.exp_pos _).le
    _ = (8 / β ^ 2) * Real.exp (β * |x| / 2 + t * |x|) := by
      rw [Real.exp_add]
      ring
    _ ≤ (8 / β ^ 2) * Real.exp (β * |x|) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Real.exp_le_exp.mpr
      have h := mul_le_mul_of_nonneg_right ht (abs_nonneg x)
      nlinarith

theorem nsWeightedMoment_crude_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    {ρ σ : CMat ι} (hρ : IsState ρ) (hσ : σ.PosSemidef) {a : ℝ}
    (ha : 0 < a) (hdom : LoewnerLE ρ (a • σ))
    (htrace : (Matrix.trace σ).re ≤ a) (c : ℝ) {t : ℝ}
    (ht : t ≤ Real.log 2 / 4) :
    nsWeightedMoment ρ σ c t ≤
      (16 / (Real.log 2 / 2) ^ 2) * Real.sqrt a *
        Real.exp ((Real.log 2 / 2) * |c|) := by
  let P := nsLaw ρ σ hρ hσ
  let β : ℝ := Real.log 2 / 2
  have hβ : 0 < β := by dsimp [β]; positivity
  have ht' : t ≤ β / 2 := by dsimp [β]; linarith
  change P.expect (fun z => (nsLikelihood ρ σ z - c) ^ 2 *
    Real.exp (t * |nsLikelihood ρ σ z - c|)) ≤ _
  calc
    _ ≤ P.expect (fun z => (8 / β ^ 2) *
        Real.exp (β * |nsLikelihood ρ σ z - c|)) :=
      P.expect_mono fun z => absolute_weighted_square_le_exp hβ ht'
    _ = (8 / β ^ 2) * P.expect
        (fun z => Real.exp (β * |nsLikelihood ρ σ z - c|)) := P.expect_smul _ _
    _ ≤ (8 / β ^ 2) * (2 * Real.sqrt a * Real.exp (β * |c|)) :=
      mul_le_mul_of_nonneg_left
        (nsLaw_absolute_half_order_bound hρ hσ ha hdom htrace c) (by positivity)
    _ = _ := by dsimp [β]; ring

theorem nsPositiveExtremeTail_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    {ρ σ : CMat ι} (hρ : IsState ρ) (hσ : σ.PosSemidef)
    {C c t : ℝ} (hC : 0 ≤ C) (n : ℕ)
    (hdom : LoewnerLE ρ ((Real.rpow 2 (C * (n : ℝ))) • σ))
    (hc : -(C * (n : ℝ)) ≤ c) (ht : t ≤ Real.log 2 / 16) :
    nsExpectation ρ σ (fun z => if 4 * (C + 1) * (n : ℝ) < nsLikelihood ρ σ z - c
      then (nsLikelihood ρ σ z - c) ^ 2 * Real.exp (t * |nsLikelihood ρ σ z - c|)
      else 0) ≤ (128 / (Real.log 2 / 2) ^ 2) * Real.rpow 2 (-(n : ℝ)) := by
  classical
  let β : ℝ := Real.log 2 / 2
  let J : ℝ := 4 * (C + 1) * (n : ℝ)
  let a : ℝ := Real.rpow 2 (C * (n : ℝ))
  let P := nsLaw ρ σ hρ hσ
  have hβ : 0 < β := by dsimp [β]; positivity
  have hJ : 0 ≤ J := by dsimp [J]; positivity
  have ha : 0 < a := Real.rpow_pos_of_pos (by norm_num) _
  have hhalf : Real.rpow a (1 / 2 : ℝ) = Real.exp (β * C * (n : ℝ)) := by
    dsimp [a]
    rw [Real.rpow_def_of_pos (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _),
      Real.log_rpow (by norm_num : (0 : ℝ) < 2)]
    congr 1
    dsimp [β]
    ring
  have hcentered : P.expect (fun z => Real.exp (β * (nsLikelihood ρ σ z - c))) ≤
      Real.exp (2 * β * C * (n : ℝ)) := by
    have hid (z : ι × ι) : Real.exp (β * (nsLikelihood ρ σ z - c)) =
        Real.exp (-β * c) * Real.exp (β * nsLikelihood ρ σ z) := by
      rw [← Real.exp_add]
      congr 1
      ring
    simp_rw [hid]
    rw [P.expect_smul]
    calc
      _ ≤ Real.exp (-β * c) * Real.rpow a (1 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_left (nsLaw_positive_half_order_bound hρ hσ ha hdom)
          (Real.exp_pos _).le
      _ = Real.exp (-β * c + β * C * (n : ℝ)) := by rw [hhalf, Real.exp_add]
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        nlinarith [mul_le_mul_of_nonneg_left hc hβ.le]
  have htail := P.positive_tail_weightedSecondMoment_le
    (fun z => nsLikelihood ρ σ z - c) hβ
    (show t ≤ β / 8 by dsimp [β]; linarith) hJ
  change P.expect (fun z => if J < nsLikelihood ρ σ z - c
    then (nsLikelihood ρ σ z - c) ^ 2 * Real.exp (t * |nsLikelihood ρ σ z - c|)
    else 0) ≤ _
  have harg : -(3 * β * J / 4) + 2 * β * C * (n : ℝ) ≤ -Real.log 2 * (n : ℝ) := by
    have hprod := mul_nonneg hβ.le (mul_nonneg hC (Nat.cast_nonneg n))
    have hnprod := mul_nonneg hβ.le (Nat.cast_nonneg n)
    dsimp [β, J] at *
    nlinarith
  calc
    _ ≤ ((128 / β ^ 2) * Real.exp (-(3 * β * J / 4))) *
        P.expect (fun z => Real.exp (β * (nsLikelihood ρ σ z - c))) := htail
    _ ≤ ((128 / β ^ 2) * Real.exp (-(3 * β * J / 4))) *
        Real.exp (2 * β * C * (n : ℝ)) :=
      mul_le_mul_of_nonneg_left hcentered (by positivity)
    _ = (128 / β ^ 2) * Real.exp (-(3 * β * J / 4) + 2 * β * C * (n : ℝ)) := by
      rw [Real.exp_add]
      ring
    _ ≤ (128 / β ^ 2) * Real.exp (-Real.log 2 * (n : ℝ)) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr harg) (by positivity)
    _ = _ := by
      rw [Real.rpow_eq_pow, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
      dsimp [β]
      congr 2
      ring

theorem nsWeightedMoment_le_matrix_curvature {ι : Type*} [Fintype ι] [DecidableEq ι]
    {ρ σ : CMat ι} (hρ : IsState ρ) (hσ : σ.PosSemidef)
    {C c t t₀ : ℝ} (hC : 0 ≤ C) (n : ℕ)
    (hdom : LoewnerLE ρ ((Real.rpow 2 (C * (n : ℝ))) • σ))
    (hc : -(C * (n : ℝ)) ≤ c) (ht : 0 ≤ t) (ht₀ : 0 < t₀)
    (ht3 : t ≤ t₀ / 3) (htβ : t ≤ Real.log 2 / 16) :
    nsWeightedMoment ρ σ c t ≤
      (2 * Real.exp (8 * t₀ * (C + 1) * (n : ℝ) / 3) / t₀ ^ 2) *
        ((nsLaw ρ σ hρ hσ).expect
          (fun z => Real.exp (-t₀ * (nsLikelihood ρ σ z - c))) - 1 +
            t₀ * (umegakiReal ρ σ - c)) +
        (128 / (Real.log 2 / 2) ^ 2) * Real.rpow 2 (-(n : ℝ)) := by
  classical
  let P := nsLaw ρ σ hρ hσ
  let X : ι × ι → ℝ := fun z => nsLikelihood ρ σ z - c
  let J : ℝ := 4 * (C + 1) * (n : ℝ)
  have hJ : 0 ≤ J := by dsimp [J]; positivity
  have hmean : P.mean X = umegakiReal ρ σ - c := by
    change P.expect (fun z => nsLikelihood ρ σ z - c) = _
    rw [P.expect_sub, P.expect_const]
    exact congrArg (fun x : ℝ => x - c) (nsLaw_mean_eq_umegakiReal ρ σ hρ hσ)
  have hweighted : nsWeightedMoment ρ σ c t = P.weightedSecondMoment X 0 t := by
    simp only [nsWeightedMoment, nsExpectation, FiniteLaw.weightedSecondMoment,
      FiniteLaw.expect, X, P, nsLaw, sub_zero]
  rw [hweighted, P.weightedSecondMoment_split X t J]
  have hcentral := P.truncated_weightedSecondMoment_le X ht ht₀ ht3 hJ
  rw [hmean] at hcentral
  have hexp : 2 * t₀ * J / 3 = 8 * t₀ * (C + 1) * (n : ℝ) / 3 := by
    dsimp [J]
    ring
  rw [hexp] at hcentral
  have htail : P.expect (fun z => if J < X z then (X z) ^ 2 *
      Real.exp (t * |X z|) else 0) ≤
      (128 / (Real.log 2 / 2) ^ 2) * Real.rpow 2 (-(n : ℝ)) :=
    nsPositiveExtremeTail_bound hρ hσ hC n hdom hc htβ
  exact add_le_add hcentral htail

theorem nsWeightedMoment_le_laplace_budget {ι : Type*} [Fintype ι] [DecidableEq ι]
    {ρ σ : CMat ι} (hρ : IsState ρ) (hσ : σ.PosSemidef)
    {C c t t₀ a : ℝ} (hC : 0 ≤ C) (n : ℕ)
    (hdom : LoewnerLE ρ ((Real.rpow 2 (C * (n : ℝ))) • σ))
    (hc : -(C * (n : ℝ)) ≤ c) (ht : 0 ≤ t) (ht₀ : 0 < t₀)
    (ht3 : t ≤ t₀ / 3) (htβ : t ≤ Real.log 2 / 16)
    (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hlap : (nsLaw ρ σ hρ hσ).expect
      (fun z => Real.exp (-t₀ * (nsLikelihood ρ σ z - c))) ≤ Real.exp a) :
    nsWeightedMoment ρ σ c t ≤
      (2 * Real.exp (8 * t₀ * (C + 1) * (n : ℝ) / 3) / t₀ ^ 2) *
        (a * (1 + 2 * a) + t₀ * (umegakiReal ρ σ - c)) +
        (128 / (Real.log 2 / 2) ^ 2) * Real.rpow 2 (-(n : ℝ)) := by
  have he := exp_sub_one_small ha ha1
  have h := nsWeightedMoment_le_matrix_curvature hρ hσ hC n hdom hc ht ht₀ ht3 htβ
  refine h.trans ?_
  have hb : (nsLaw ρ σ hρ hσ).expect
      (fun z => Real.exp (-t₀ * (nsLikelihood ρ σ z - c))) - 1 +
        t₀ * (umegakiReal ρ σ - c) ≤ a * (1 + 2 * a) + t₀ * (umegakiReal ρ σ - c) := by
    linarith
  have hm : (2 * Real.exp (8 * t₀ * (C + 1) * (n : ℝ) / 3) / t₀ ^ 2) *
      ((nsLaw ρ σ hρ hσ).expect
        (fun z => Real.exp (-t₀ * (nsLikelihood ρ σ z - c))) - 1 +
          t₀ * (umegakiReal ρ σ - c)) ≤
      (2 * Real.exp (8 * t₀ * (C + 1) * (n : ℝ) / 3) / t₀ ^ 2) *
        (a * (1 + 2 * a) + t₀ * (umegakiReal ρ σ - c)) :=
    mul_le_mul_of_nonneg_left hb (by positivity)
  linarith

theorem blockLog_square_eventually_le_sqrt {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, (blockLog n) ^ 2 ≤ ε * Real.sqrt (n : ℝ) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlo := isLittleO_log_rpow_rpow_atTop (2 : ℝ)
    (by norm_num : (0 : ℝ) < 1 / 2)
  have hnat : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop
  have hbound := (hlo.comp_tendsto hnat).bound
    (show 0 < ε * (Real.log 2) ^ 2 / 2 by positivity)
  filter_upwards [hbound, eventually_ge_atTop (1 : ℕ)] with n hn hn1
  have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hn1r : 1 ≤ (n : ℝ) := by exact_mod_cast hn1
  have hshift : 0 ≤ (n : ℝ) + 1 := by positivity
  have hlogsq : Real.log ((n : ℝ) + 1) ^ 2 ≤
      (ε * (Real.log 2) ^ 2 / 2) * Real.sqrt ((n : ℝ) + 1) := by
    simpa only [Function.comp_apply, Real.rpow_two, Real.norm_eq_abs,
      abs_of_nonneg (sq_nonneg (Real.log ((n : ℝ) + 1))), ← Real.sqrt_eq_rpow,
      abs_of_nonneg (Real.sqrt_nonneg _)] using hn
  have hsqrt : Real.sqrt ((n : ℝ) + 1) ≤ 2 * Real.sqrt (n : ℝ) := by
    nlinarith [Real.sq_sqrt hn0, Real.sq_sqrt hshift,
      Real.sqrt_nonneg (n : ℝ), Real.sqrt_nonneg ((n : ℝ) + 1)]
  have hs := hlogsq.trans (mul_le_mul_of_nonneg_left hsqrt (by positivity))
  unfold blockLog logTwo
  rw [div_pow]
  apply (div_le_iff₀ (sq_pos_of_pos hlog2)).mpr
  nlinarith

theorem uniform_endpoint_smallness {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) :
    ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M → ∀ n : ℕ, M ^ 2 ≤ n →
      (A * blockLog n + (M : ℝ) * B * (blockLog n) ^ 2) / (n : ℝ) ≤
        (1 / 100 : ℝ) := by
  let ε : ℝ := 1 / (200 * (A + B + 1))
  have hε : 0 < ε := by dsimp [ε]; positivity
  obtain ⟨N, hN⟩ := eventually_atTop.1 (blockLog_square_eventually_le_sqrt hε)
  refine ⟨max N 1, ?_⟩
  intro M hM n hn
  have hM1 : 1 ≤ M := (le_max_right N 1).trans hM
  have hNM : N ≤ M := (le_max_left N 1).trans hM
  have hMn : M ≤ n := by nlinarith
  have hn1 : 1 ≤ n := hM1.trans hMn
  have hn1r : 1 ≤ (n : ℝ) := by exact_mod_cast hn1
  have hM0 : 0 ≤ (M : ℝ) := Nat.cast_nonneg M
  have hM2 : (M : ℝ) ^ 2 ≤ (n : ℝ) := by exact_mod_cast hn
  have hnsq := Real.sq_sqrt (Nat.cast_nonneg n : 0 ≤ (n : ℝ))
  have hMsqrt : (M : ℝ) ≤ Real.sqrt (n : ℝ) := by
    nlinarith [Real.sqrt_nonneg (n : ℝ)]
  have hsqrt1 : 1 ≤ Real.sqrt (n : ℝ) := by
    nlinarith [Real.sqrt_nonneg (n : ℝ)]
  have hsqrtn : Real.sqrt (n : ℝ) ≤ (n : ℝ) := by nlinarith
  have hprod : (M : ℝ) * Real.sqrt (n : ℝ) ≤ (n : ℝ) := by
    nlinarith [mul_le_mul_of_nonneg_right hMsqrt (Real.sqrt_nonneg (n : ℝ))]
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hL : 1 ≤ blockLog n := by
    unfold blockLog logTwo
    apply (le_div_iff₀ hlog2).mpr
    simpa only [one_mul] using
      Real.log_le_log (by norm_num : (0 : ℝ) < 2) (by linarith : 2 ≤ (n : ℝ) + 1)
  have hLL : blockLog n ≤ (blockLog n) ^ 2 := by nlinarith
  have hLn := hN n (hNM.trans hMn)
  have hcoeff : ε * (A + B) ≤ (1 / 100 : ℝ) := by
    dsimp [ε]
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (by positivity : 0 < 200 * (A + B + 1))).mpr
    nlinarith
  apply (div_le_iff₀ (by linarith : 0 < (n : ℝ))).mpr
  calc
    A * blockLog n + (M : ℝ) * B * (blockLog n) ^ 2 ≤
        (A + (M : ℝ) * B) * (blockLog n) ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_left hLL hA]
    _ ≤ (A + (M : ℝ) * B) * (ε * Real.sqrt (n : ℝ)) :=
      mul_le_mul_of_nonneg_left hLn (by positivity)
    _ = ε * (A * Real.sqrt (n : ℝ) + B * ((M : ℝ) * Real.sqrt (n : ℝ))) := by ring
    _ ≤ ε * (A * (n : ℝ) + B * (n : ℝ)) :=
      mul_le_mul_of_nonneg_left
        (add_le_add (mul_le_mul_of_nonneg_left hsqrtn hA)
          (mul_le_mul_of_nonneg_left hprod hB)) hε.le
    _ = (ε * (A + B)) * (n : ℝ) := by ring
    _ ≤ (1 / 100 : ℝ) * (n : ℝ) :=
      mul_le_mul_of_nonneg_right hcoeff (Nat.cast_nonneg n)

theorem blockLog_nonneg (n : ℕ) : 0 ≤ blockLog n := by
  unfold blockLog logTwo
  apply div_nonneg
  · exact Real.log_nonneg (le_add_of_nonneg_left (Nat.cast_nonneg n : 0 ≤ (n : ℝ)))
  · exact (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le

theorem blockLog_mono {m n : ℕ} (hmn : m ≤ n) : blockLog m ≤ blockLog n := by
  unfold blockLog logTwo
  apply (div_le_div_iff_of_pos_right (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mpr
  exact Real.log_le_log (by positivity : 0 < (m : ℝ) + 1)
    (by exact_mod_cast Nat.add_le_add_right hmn 1)

theorem blockLog_ge_one {n : ℕ} (hn : 1 ≤ n) : 1 ≤ blockLog n := by
  unfold blockLog logTwo
  apply (le_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mpr
  simpa only [one_mul] using Real.log_le_log
    (by norm_num : (0 : ℝ) < 2) (by exact_mod_cast Nat.add_le_add_right hn 1)

theorem shrunk_block_bounds {n : ℕ} (hn : 32 ≤ n) :
    0 < n / 16 ∧ n / 16 < n ∧ (n : ℝ) / 32 ≤ ((n / 16 : ℕ) : ℝ) ∧
      blockLog (n / 16) ≤ blockLog n - 2 := by
  have hm : 0 < n / 16 := by omega
  have hmn : n / 16 < n := by omega
  have h32 : n ≤ (n / 16) * 32 := by omega
  have h4 : 4 * (n / 16 + 1) ≤ n + 1 := by omega
  refine ⟨hm, hmn, ?_, ?_⟩
  · apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 32)).mpr
    exact_mod_cast h32
  · have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have h4r : 4 * (((n / 16 : ℕ) : ℝ) + 1) ≤ (n : ℝ) + 1 := by
      exact_mod_cast h4
    have hlog := Real.log_le_log
      (by positivity : 0 < 4 * (((n / 16 : ℕ) : ℝ) + 1)) h4r
    have hlog4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      norm_num
    rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0)
      (by positivity : (((n / 16 : ℕ) : ℝ) + 1) ≠ 0), hlog4] at hlog
    unfold blockLog logTwo
    apply (div_le_iff₀ hlog2).mpr
    have hid : (Real.log ((n : ℝ) + 1) / Real.log 2 - 2) * Real.log 2 =
        Real.log ((n : ℝ) + 1) - 2 * Real.log 2 := by
      field_simp [hlog2.ne'] <;> ring
    rw [hid]
    linarith

theorem shrunk_block_order_window {n : ℕ} (hn : 32 ≤ n) {ζ : ℝ} (hζ : 0 < ζ) :
    (ζ / ((n : ℝ) * blockLog n * Real.log 2)) *
      ((n / 16 : ℕ) : ℝ) * blockLog (n / 16) ≤ ζ / (16 * Real.log 2) := by
  have hb := shrunk_block_bounds hn
  have hn1 : 1 ≤ n := by omega
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hLpos : 0 < blockLog n := lt_of_lt_of_le zero_lt_one (blockLog_ge_one hn1)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hm : ((n / 16 : ℕ) : ℝ) ≤ (n : ℝ) / 16 := by
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 16)).mpr
    exact_mod_cast (show (n / 16) * 16 ≤ n by omega)
  have hLm : blockLog (n / 16) ≤ blockLog n := blockLog_mono hb.2.1.le
  have hproduct : ((n / 16 : ℕ) : ℝ) * blockLog (n / 16) ≤
      (n : ℝ) * blockLog n / 16 := by
    have h := mul_le_mul hm hLm (blockLog_nonneg _) (by positivity)
    nlinarith
  have hcoef : 0 ≤ ζ / ((n : ℝ) * blockLog n * Real.log 2) := by positivity
  calc
    _ = (ζ / ((n : ℝ) * blockLog n * Real.log 2)) *
        (((n / 16 : ℕ) : ℝ) * blockLog (n / 16)) := by ring
    _ ≤ (ζ / ((n : ℝ) * blockLog n * Real.log 2)) *
        ((n : ℝ) * blockLog n / 16) := mul_le_mul_of_nonneg_left hproduct hcoef
    _ = ζ / (16 * Real.log 2) := by
      field_simp [hnpos.ne', hLpos.ne', hlog2.ne'] <;> ring

theorem finite_baseline_absorbed {B M : ℝ} (hB : 0 ≤ B) (hM : 1 ≤ M)
    (hBM : 4 * B ^ 2 ≤ M) {n : ℕ} (hn : 1 ≤ n)
    (hnM : (n : ℝ) ≤ M ^ 2 + 1) :
    B * Real.rpow (n : ℝ) (1 / 4 : ℝ) * Real.rpow (blockLog n) (3 / 4 : ℝ) ≤
      M * (blockLog n) ^ 3 := by
  have hM0 : 0 ≤ M := (by norm_num : (0 : ℝ) ≤ 1).trans hM
  have hs := Real.sq_sqrt hM0
  have hpower : (2 * Real.sqrt M) ^ 4 = 16 * M ^ 2 := by
    calc
      _ = 16 * ((Real.sqrt M) ^ 2) ^ 2 := by ring
      _ = _ := by rw [hs]
  have hnPower : (n : ℝ) ≤ (2 * Real.sqrt M) ^ 4 := by
    rw [hpower]
    nlinarith
  have hquarter : Real.rpow (n : ℝ) (1 / 4 : ℝ) ≤ 2 * Real.sqrt M := by
    have h := Real.rpow_le_rpow (Nat.cast_nonneg n) hnPower
      (by norm_num : (0 : ℝ) ≤ 1 / 4)
    have hid : Real.rpow ((2 * Real.sqrt M) ^ 4) (1 / 4 : ℝ) =
        2 * Real.sqrt M := by
      simpa using Real.pow_rpow_inv_natCast (n := 4)
        (by positivity : 0 ≤ 2 * Real.sqrt M) (by norm_num : (4 : ℕ) ≠ 0)
    exact hid ▸ h
  have h2B : 2 * B ≤ Real.sqrt M := by
    nlinarith [Real.sqrt_nonneg M]
  have hbudget : B * Real.rpow (n : ℝ) (1 / 4 : ℝ) ≤ M := by
    have h1 := mul_le_mul_of_nonneg_left hquarter hB
    have h2 := mul_le_mul_of_nonneg_right h2B (Real.sqrt_nonneg M)
    nlinarith
  have hlog : Real.rpow (blockLog n) (3 / 4 : ℝ) ≤ (blockLog n) ^ 3 := by
    simpa only [Real.rpow_eq_pow, Real.rpow_natCast] using Real.rpow_le_rpow_of_exponent_le
      (blockLog_ge_one hn) (by norm_num : (3 / 4 : ℝ) ≤ (3 : ℕ))
  exact mul_le_mul hbudget hlog
    (Real.rpow_nonneg (blockLog_nonneg n) _) hM0

end QuantumProver.Equipartition.FiniteModel

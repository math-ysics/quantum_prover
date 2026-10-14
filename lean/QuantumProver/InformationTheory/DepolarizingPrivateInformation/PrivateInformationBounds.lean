import Mathlib

noncomputable section

namespace QuantumProver.DepolarizingPrivateInformation

def aScalar (p : ℝ) : ℝ := 1 - 3 * p / 4
def bScalar (p : ℝ) : ℝ := p / 4
def etaScalar (p : ℝ) : ℝ := 1 - p
def sScalar (p : ℝ) : ℝ := aScalar p + bScalar p
def tScalar (p : ℝ) : ℝ := aScalar p * bScalar p
def zScalar (u : ℝ) : ℝ := Real.sqrt (1 - u ^ 2)
def hScalar (p : ℝ) : ℝ := (aScalar p) ^ 2 + (bScalar p) ^ 2
def HScalar (p u : ℝ) : ℝ := hScalar p + 2 * tScalar p * zScalar u
def HCore (p z : ℝ) : ℝ := hScalar p + 2 * tScalar p * z
def cScalar (p : ℝ) : ℝ := 2 * Real.sqrt (tScalar p)
def RScalar (p u : ℝ) : ℝ := Real.sqrt (HScalar p u)
def ellScalar (p u : ℝ) : ℝ := Real.sqrt (tScalar p * (1 + u))
def xScalar (p u : ℝ) : ℝ := Real.sqrt (tScalar p * (1 + u) * HScalar p u)
def d0Scalar (p u : ℝ) : ℝ := tScalar p * (zScalar u + 1 + u)
def a0Scalar (p u : ℝ) : ℝ := (1 + u) * (sScalar p) ^ 2 - 4 * u * tScalar p
def b0Scalar (p u : ℝ) : ℝ :=
  2 * (zScalar u * hScalar p + 2 * tScalar p * (1 - u)) / HScalar p u
def rScalarSq (p u : ℝ) : ℝ := (etaScalar p) ^ 2 + 4 * u ^ 2 * tScalar p

def metricCross (p u : ℝ) : ℝ :=
  sScalar p / 4 + (1 - u) ^ 2 * tScalar p / rScalarSq p u *
    (u ^ 2 * sScalar p / (1 - u ^ 2) +
      2 * (etaScalar p) ^ 2 /
        (sScalar p + 2 * zScalar u * Real.sqrt (tScalar p)))

def metricLL (p u : ℝ) : ℝ :=
  8 * (tScalar p) ^ 2 * (a0Scalar p u + b0Scalar p u * xScalar p u) /
    (d0Scalar p u + xScalar p u) ^ 2

def metricKE (p u : ℝ) : ℝ :=
  metricLL p u + 8 * bScalar p * metricCross p u + 4 * (bScalar p) ^ 2 / (1 + u)

def metricKB (p u : ℝ) : ℝ :=
  (etaScalar p) ^ 2 / (1 + u * (etaScalar p) ^ 2)

def metricGap (p u : ℝ) : ℝ := metricKB p u - metricKE p u

def uBase : ℝ := 1 / 50
def uMiddle : ℝ := 201 / 10000
def uWide : ℝ := 21 / 1000

def PhysicalMetricRoot (p u : ℝ) : Prop :=
  89 / 300 < p ∧ p < 1 / 3 ∧ metricGap p u = 0

def bobAffinityScalar (η u v : ℝ) : ℝ :=
  (1 - u * η ^ 2) / 2 +
    Real.sqrt ((1 + u * η ^ 2) ^ 2 - 4 * v ^ 2 * η ^ 2) / 2

def finiteSignalRadius (δ : ℝ) : ℝ := Real.sqrt (3 * δ / (2 * 10 ^ 9))
def finiteAffinityMargin (δ : ℝ) : ℝ := 3 * δ ^ 2 / (4 * 10 ^ 9)
def finiteBlockCount (δ : ℝ) : ℕ :=
  2 * Nat.ceil (4096 / (finiteAffinityMargin δ) ^ 2)

def signalA07 : ℝ := 1 / 10 ^ 8
def blocksA07 : ℕ := 10 ^ 26
def finiteRateFloor (m : ℕ) : ℝ := (3 / 4 : ℝ) ^ m / (2 ^ 19 * (m : ℝ) ^ 16)

theorem uBase_pos : 0 < uBase := by norm_num [uBase]
theorem uWide_lt_quarter : uWide < 1 / 4 := by norm_num [uWide]
theorem uMiddle_sub_base : uMiddle - uBase = 1 / 10000 := by
  norm_num [uMiddle, uBase]
theorem uWide_sub_middle : uWide - uMiddle = 9 / 10000 := by
  norm_num [uWide, uMiddle]
theorem signalA07_pos : 0 < signalA07 := by norm_num [signalA07]
theorem blocksA07_pos : 0 < blocksA07 := by norm_num [blocksA07]

theorem scalar_weight_sum (p : ℝ) : aScalar p + 3 * bScalar p = 1 := by
  unfold aScalar bScalar
  ring

theorem scalar_eta_eq (p : ℝ) : aScalar p - bScalar p = etaScalar p := by
  unfold aScalar bScalar etaScalar
  ring

theorem bobAffinityScalar_gt_three_quarters {η u v : ℝ}
    (hη : |η| ≤ 1) (hu : 0 ≤ u) (hv : |v| ≤ 1 / 8) :
    3 / 4 < bobAffinityScalar η u v := by
  obtain ⟨hηl, hηu⟩ := abs_le.mp hη
  obtain ⟨hvl, hvu⟩ := abs_le.mp hv
  have hηp : 0 ≤ (1 - η) * (1 + η) := mul_nonneg (by linarith) (by linarith)
  have hηsq : η ^ 2 ≤ 1 := by nlinarith
  have hvp : 0 ≤ (1 / 8 - v) * (1 / 8 + v) :=
    mul_nonneg (by linarith) (by linarith)
  have hvsq : v ^ 2 ≤ 1 / 64 := by nlinarith
  have hvprod : v ^ 2 * η ^ 2 ≤ 1 / 64 := by
    calc
      v ^ 2 * η ^ 2 ≤ v ^ 2 * 1 := mul_le_mul_of_nonneg_left hηsq (sq_nonneg v)
      _ ≤ 1 / 64 := by simpa using hvsq
  have hw : 0 ≤ u * η ^ 2 := mul_nonneg hu (sq_nonneg η)
  have hrad : (1 / 2 + u * η ^ 2) ^ 2 <
      (1 + u * η ^ 2) ^ 2 - 4 * v ^ 2 * η ^ 2 := by nlinarith
  have hs := Real.lt_sqrt_of_sq_lt hrad
  unfold bobAffinityScalar
  linarith

theorem finiteSignalRadius_sq {δ : ℝ} (hδ : 0 ≤ δ) :
    (finiteSignalRadius δ) ^ 2 = 3 * δ / (2 * 10 ^ 9) := by
  unfold finiteSignalRadius
  rw [Real.sq_sqrt (by positivity)]

theorem finite_signal_margin_identity {δ : ℝ} (hδ : 0 ≤ δ) :
    δ * (finiteSignalRadius δ) ^ 2 - (10 ^ 9 / 3 : ℝ) *
      (finiteSignalRadius δ) ^ 4 = finiteAffinityMargin δ := by
  have hs := finiteSignalRadius_sq hδ
  rw [show (finiteSignalRadius δ) ^ 4 = ((finiteSignalRadius δ) ^ 2) ^ 2 by ring]
  rw [hs]
  unfold finiteAffinityMargin
  ring

theorem fixed_a07_remainder_gap {QE QB d : ℝ}
    (hd : 3 / 10 ^ 7 < d)
    (hrem : d * signalA07 ^ 2 - (10 ^ 9 / 3 : ℝ) * signalA07 ^ 4 ≤ QE - QB) :
    2 / 10 ^ 23 < QE - QB := by
  have hmul := mul_lt_mul_of_pos_right hd (sq_pos_of_pos signalA07_pos)
  have hfixed : (3 / 10 ^ 7 : ℝ) * signalA07 ^ 2 -
      (10 ^ 9 / 3 : ℝ) * signalA07 ^ 4 > 2 / 10 ^ 23 := by
    norm_num [signalA07]
  linarith

theorem finiteRateFloor_pos {m : ℕ} (hm : 0 < m) : 0 < finiteRateFloor m := by
  unfold finiteRateFloor
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  positivity

theorem unique_zero_in_open_interval {f : ℝ → ℝ} {lo hi : ℝ}
    (hlohi : lo < hi) (hc : ContinuousOn f (Set.Icc lo hi))
    (ha : StrictAntiOn f (Set.Ioo lo hi))
    (hl : 0 < f lo) (hh : f hi < 0) :
    ∃! p, p ∈ Set.Ioo lo hi ∧ f p = 0 := by
  obtain ⟨p, hp, hfp⟩ := intermediate_value_Ioo' hlohi.le hc (show
      (0 : ℝ) ∈ Set.Ioo (f hi) (f lo) from ⟨hh, hl⟩)
  refine ⟨p, ⟨hp, hfp⟩, ?_⟩
  intro q hq
  exact ha.injOn hq.1 hp (hq.2.trans hfp.symm)

theorem fourth_taylor_remainder_bound {f : ℝ → ℝ} {v C : ℝ}
    (hv : v ≠ 0) (hf : ContDiffOn ℝ 4 f (Set.uIcc 0 v))
    (hC : ∀ x ∈ Set.uIoo 0 v, |iteratedDeriv 4 f x| ≤ C) :
    |f v - taylorWithinEval f 3 (Set.uIcc 0 v) 0 v| ≤ C * |v| ^ 4 / 24 := by
  obtain ⟨x, hx, h⟩ := taylor_mean_remainder_lagrange_iteratedDeriv
    (n := 3) (x₀ := 0) (x := v) (Ne.symm hv) hf
  have h' : f v - taylorWithinEval f 3 (Set.uIcc 0 v) 0 v =
      iteratedDeriv 4 f x * v ^ 4 / 24 := by
    convert h using 1 <;> norm_num
  calc
    |f v - taylorWithinEval f 3 (Set.uIcc 0 v) 0 v| =
        |iteratedDeriv 4 f x| * |v| ^ 4 / 24 := by
      rw [h']
      simp [abs_div, abs_mul, abs_pow]
    _ ≤ C * |v| ^ 4 / 24 := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (hC x hx) (by positivity)) (by norm_num)

theorem quadratic_jet_fourth_remainder {f : ℝ → ℝ} {v C κ : ℝ}
    (hv : v ≠ 0) (hf : ContDiffOn ℝ 4 f (Set.uIcc 0 v))
    (hC : ∀ x ∈ Set.uIoo 0 v, |iteratedDeriv 4 f x| ≤ C)
    (hjet : taylorWithinEval f 3 (Set.uIcc 0 v) 0 v = 1 - κ * v ^ 2) :
    |f v - (1 - κ * v ^ 2)| ≤ C * |v| ^ 4 / 24 := by
  simpa only [hjet] using fourth_taylor_remainder_bound hv hf hC

theorem aScalar_pos {p : ℝ} (hp : p ≤ 1 / 3) : 0 < aScalar p := by
  unfold aScalar
  linarith

theorem bScalar_pos {p : ℝ} (hp : 0 < p) : 0 < bScalar p := by
  unfold bScalar
  linarith

theorem etaScalar_pos {p : ℝ} (hp : p ≤ 1 / 3) : 0 < etaScalar p := by
  unfold etaScalar
  linarith

theorem tScalar_pos {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1 / 3) :
    0 < tScalar p := by
  exact mul_pos (aScalar_pos hp1) (bScalar_pos hp0)

theorem zScalar_pos {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 4) :
    0 < zScalar u := by
  have hp : 0 < (1 - u) * (1 + u) := mul_pos (by linarith) (by linarith)
  unfold zScalar
  exact Real.sqrt_pos.mpr (by nlinarith)

theorem hScalar_pos {p : ℝ} (hp1 : p ≤ 1 / 3) : 0 < hScalar p := by
  have ha := sq_pos_of_pos (aScalar_pos hp1)
  unfold hScalar
  nlinarith [sq_nonneg (bScalar p)]

theorem HScalar_pos {p u : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1 / 3)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 4) : 0 < HScalar p u := by
  have hh := hScalar_pos hp1
  have ht := tScalar_pos hp0 hp1
  have hz := zScalar_pos hu0 hu1
  unfold HScalar
  positivity

theorem xScalar_pos {p u : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1 / 3)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 4) : 0 < xScalar p u := by
  have ht := tScalar_pos hp0 hp1
  have hH := HScalar_pos hp0 hp1 hu0 hu1
  unfold xScalar
  apply Real.sqrt_pos.mpr
  positivity

theorem physical_metric_denominators_pos {p u : ℝ}
    (hp0 : 0 < p) (hp1 : p ≤ 1 / 3) (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 4) :
    0 < 1 + u * (etaScalar p) ^ 2 ∧
    0 < 1 + u ∧ 0 < 1 - u ^ 2 ∧ 0 < rScalarSq p u ∧
    0 < HScalar p u ∧
    0 < sScalar p + 2 * zScalar u * Real.sqrt (tScalar p) ∧
    0 < (d0Scalar p u + xScalar p u) ^ 2 := by
  have ha := aScalar_pos hp1
  have hb := bScalar_pos hp0
  have he := etaScalar_pos hp1
  have ht := tScalar_pos hp0 hp1
  have hz := zScalar_pos hu0 hu1
  have hH := HScalar_pos hp0 hp1 hu0 hu1
  have hx := xScalar_pos hp0 hp1 hu0 hu1
  have hs : 0 < sScalar p := add_pos ha hb
  have h1 : 0 < 1 + u * (etaScalar p) ^ 2 := by positivity
  have h2 : 0 < 1 + u := by linarith
  have h3 : 0 < 1 - u ^ 2 := by
    have hh : 0 < (1 - u) * (1 + u) := mul_pos (by linarith) (by linarith)
    nlinarith
  have h4 : 0 < rScalarSq p u := by
    unfold rScalarSq
    positivity
  have h6 : 0 < sScalar p + 2 * zScalar u * Real.sqrt (tScalar p) := by positivity
  have hd : 0 < d0Scalar p u := by
    unfold d0Scalar
    positivity
  exact ⟨h1, h2, h3, h4, hH, h6, sq_pos_of_pos (add_pos hd hx)⟩

theorem zScalar_wide_table {u : ℝ} (hu : u ∈ Set.Icc (1 / 50) (21 / 1000)) :
    999779 / 10 ^ 6 < zScalar u ∧ zScalar u < 49989999 / 50000000 := by
  have hu0 : 0 ≤ u := by linarith [hu.1]
  have hpUpper : 0 ≤ (21 / 1000 - u) * (21 / 1000 + u) :=
    mul_nonneg (by linarith [hu.2]) (by linarith)
  have hpLower : 0 ≤ (u - 1 / 50) * (u + 1 / 50) :=
    mul_nonneg (by linarith [hu.1]) (by linarith)
  have hrad : 0 ≤ 1 - u ^ 2 := by nlinarith
  have hl : (999779 / 10 ^ 6 : ℝ) ^ 2 < 1 - (21 / 1000 : ℝ) ^ 2 := by norm_num
  have hh : 1 - (1 / 50 : ℝ) ^ 2 < (49989999 / 50000000 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold zScalar
    apply Real.lt_sqrt_of_sq_lt
    nlinarith
  · unfold zScalar
    apply (Real.sqrt_lt hrad (by norm_num : (0 : ℝ) ≤ 49989999 / 50000000)).mpr
    nlinarith

theorem xScalar_eq_ell_mul_R {p u : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1 / 3)
    (hu0 : 0 ≤ u) : xScalar p u = ellScalar p u * RScalar p u := by
  have ht := tScalar_pos hp0 hp1
  unfold xScalar ellScalar RScalar
  rw [Real.sqrt_mul (by positivity : 0 ≤ tScalar p * (1 + u))]

theorem tScalar_mono {p q : ℝ} (hpq : p ≤ q) (hq : q ≤ 2 / 3) :
    tScalar p ≤ tScalar q := by
  have hf : 0 ≤ (q - p) * (4 - 3 * (p + q)) :=
    mul_nonneg (by linarith) (by linarith)
  unfold tScalar aScalar bScalar
  nlinarith

def rectangleLow : ℝ := 89 / 300
def rectangleHigh : ℝ := rectangleLow + 1 / 5000

theorem rectangleHigh_lt_third : rectangleHigh < 1 / 3 := by
  norm_num [rectangleHigh, rectangleLow]

theorem cScalar_wide_table {p : ℝ}
    (hp : p ∈ Set.Icc rectangleLow rectangleHigh) :
    480269 / 10 ^ 6 < cScalar p ∧ cScalar p < 480386 / 10 ^ 6 := by
  have hp0 : 0 < p := by
    have hl : 0 < rectangleLow := by norm_num [rectangleLow]
    linarith [hp.1]
  have hp1 : p ≤ 1 / 3 := hp.2.trans rectangleHigh_lt_third.le
  have ht := tScalar_pos hp0 hp1
  have hl := tScalar_mono hp.1 (by linarith : p ≤ 2 / 3)
  have hh := tScalar_mono hp.2 (by
    norm_num [rectangleHigh, rectangleLow] : rectangleHigh ≤ 2 / 3)
  have hlfix : (480269 / 10 ^ 6 : ℝ) ^ 2 < 4 * tScalar rectangleLow := by
    norm_num [tScalar, aScalar, bScalar, rectangleLow]
  have hhfix : 4 * tScalar rectangleHigh < (480386 / 10 ^ 6 : ℝ) ^ 2 := by
    norm_num [tScalar, aScalar, bScalar, rectangleHigh, rectangleLow]
  have hs : (cScalar p) ^ 2 = 4 * tScalar p := by
    unfold cScalar
    nlinarith [Real.sq_sqrt ht.le]
  have hc : 0 ≤ cScalar p := by unfold cScalar; positivity
  constructor <;> nlinarith

theorem ellScalar_wide_table {p u : ℝ}
    (hp : p ∈ Set.Icc rectangleLow rectangleHigh)
    (hu : u ∈ Set.Icc (1 / 50) (21 / 1000)) :
    242523 / 10 ^ 6 < ellScalar p u ∧ ellScalar p u < 242711 / 10 ^ 6 := by
  have hp0 : 0 < p := by
    have hl : 0 < rectangleLow := by norm_num [rectangleLow]
    linarith [hp.1]
  have hp1 : p ≤ 1 / 3 := hp.2.trans rectangleHigh_lt_third.le
  have hu0 : 0 ≤ u := by linarith [hu.1]
  have ht := tScalar_pos hp0 hp1
  have htl := tScalar_mono hp.1 (by linarith : p ≤ 2 / 3)
  have hth := tScalar_mono hp.2 (by
    norm_num [rectangleHigh, rectangleLow] : rectangleHigh ≤ 2 / 3)
  have hlower : tScalar rectangleLow * (1 + 1 / 50) ≤ tScalar p * (1 + u) :=
    mul_le_mul htl (by linarith [hu.1]) (by norm_num) ht.le
  have hupper : tScalar p * (1 + u) ≤ tScalar rectangleHigh * (1 + 21 / 1000) :=
    mul_le_mul hth (by linarith [hu.2]) (by linarith)
      (by norm_num [tScalar, aScalar, bScalar, rectangleHigh, rectangleLow])
  have hlfix : (242523 / 10 ^ 6 : ℝ) ^ 2 <
      tScalar rectangleLow * (1 + 1 / 50) := by
    norm_num [tScalar, aScalar, bScalar, rectangleLow]
  have hhfix : tScalar rectangleHigh * (1 + 21 / 1000) <
      (242711 / 10 ^ 6 : ℝ) ^ 2 := by
    norm_num [tScalar, aScalar, bScalar, rectangleHigh, rectangleLow]
  have hrad : 0 ≤ tScalar p * (1 + u) := by positivity
  constructor
  · unfold ellScalar
    apply Real.lt_sqrt_of_sq_lt
    linarith
  · unfold ellScalar
    apply (Real.sqrt_lt hrad (by norm_num : (0 : ℝ) ≤ 242711 / 10 ^ 6)).mpr
    linarith

theorem HCore_identity (p z : ℝ) :
    HCore p z = (sScalar p) ^ 2 - 2 * tScalar p * (1 - z) := by
  unfold HCore hScalar sScalar tScalar
  ring

theorem HCore_antitone {p q z : ℝ} (hpq : p ≤ q) (hq : q ≤ 1 / 3)
    (hz : z ≤ 1) : HCore q z ≤ HCore p z := by
  have hs : sScalar q ≤ sScalar p := by
    unfold sScalar aScalar bScalar
    linarith
  have hsq : 0 ≤ sScalar q := by
    unfold sScalar aScalar bScalar
    linarith
  have hsp : 0 ≤ sScalar p := hsq.trans hs
  have hsq2 : (sScalar q) ^ 2 ≤ (sScalar p) ^ 2 := by
    have hh : 0 ≤ (sScalar p - sScalar q) * (sScalar p + sScalar q) :=
      mul_nonneg (sub_nonneg.mpr hs) (add_nonneg hsp hsq)
    nlinarith
  have ht := tScalar_mono hpq (by linarith : q ≤ 2 / 3)
  have htm := mul_le_mul_of_nonneg_right ht (sub_nonneg.mpr hz)
  rw [HCore_identity, HCore_identity]
  linarith

theorem HCore_mono_z {p z1 z2 : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1 / 3)
    (hz : z1 ≤ z2) : HCore p z1 ≤ HCore p z2 := by
  have ht := tScalar_pos hp0 hp1
  have hm := mul_le_mul_of_nonneg_left hz (show 0 ≤ 2 * tScalar p by positivity)
  unfold HCore
  linarith

theorem RScalar_wide_table {p u : ℝ}
    (hp : p ∈ Set.Icc rectangleLow rectangleHigh)
    (hu : u ∈ Set.Icc (1 / 50) (21 / 1000)) :
    851550 / 10 ^ 6 < RScalar p u ∧ RScalar p u < 851654 / 10 ^ 6 := by
  have hpl : 0 < rectangleLow := by norm_num [rectangleLow]
  have hph : 0 < rectangleHigh := by norm_num [rectangleHigh, rectangleLow]
  have hp0 : 0 < p := hpl.trans_le hp.1
  have hp1 : p ≤ 1 / 3 := hp.2.trans rectangleHigh_lt_third.le
  have hu0 : 0 ≤ u := by linarith [hu.1]
  have hu1 : u ≤ 1 / 4 := by linarith [hu.2]
  have hz := zScalar_wide_table hu
  have hz1 : zScalar u ≤ 1 := by
    unfold zScalar
    apply (Real.sqrt_le_left (by norm_num : (0 : ℝ) ≤ 1)).mpr
    nlinarith [sq_nonneg u]
  have hlow : HCore rectangleHigh (999779 / 10 ^ 6) ≤ HScalar p u := by
    calc
      HCore rectangleHigh (999779 / 10 ^ 6) ≤ HCore rectangleHigh (zScalar u) :=
        HCore_mono_z hph rectangleHigh_lt_third.le hz.1.le
      _ ≤ HCore p (zScalar u) := HCore_antitone hp.2 rectangleHigh_lt_third.le hz1
      _ = HScalar p u := rfl
  have hhigh : HScalar p u ≤ HCore rectangleLow (49989999 / 50000000) := by
    calc
      HScalar p u = HCore p (zScalar u) := rfl
      _ ≤ HCore rectangleLow (zScalar u) := HCore_antitone hp.1 hp1 hz1
      _ ≤ HCore rectangleLow (49989999 / 50000000) :=
        HCore_mono_z hpl (by norm_num [rectangleLow]) hz.2.le
  have hlfix : (851550 / 10 ^ 6 : ℝ) ^ 2 < HCore rectangleHigh (999779 / 10 ^ 6) := by
    norm_num [HCore, hScalar, tScalar, aScalar, bScalar, rectangleHigh, rectangleLow]
  have hhfix : HCore rectangleLow (49989999 / 50000000) < (851654 / 10 ^ 6 : ℝ) ^ 2 := by
    norm_num [HCore, hScalar, tScalar, aScalar, bScalar, rectangleLow]
  have hrad := HScalar_pos hp0 hp1 hu0 hu1
  constructor
  · unfold RScalar
    apply Real.lt_sqrt_of_sq_lt
    linarith
  · unfold RScalar
    apply (Real.sqrt_lt hrad.le (by norm_num : (0 : ℝ) ≤ 851654 / 10 ^ 6)).mpr
    linarith

end QuantumProver.DepolarizingPrivateInformation

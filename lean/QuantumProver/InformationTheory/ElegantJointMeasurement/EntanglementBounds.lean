import QuantumProver.InformationTheory.ElegantJointMeasurement.SquareProcess
import QuantumProver.InformationTheory.ElegantJointMeasurement.ResourceEntropy
import QuantumProver.InformationTheory.ElegantJointMeasurement.RankOneEffects
import QuantumProver.InformationTheory.ElegantJointMeasurement.ResourceCode
import QuantumProver.InformationTheory.ElegantJointMeasurement.ClosureJoin
import QuantumProver.InformationTheory.ElegantJointMeasurement.ProtocolEffects
import QuantumProver.InformationTheory.ElegantJointMeasurement.ProtocolEffectLimits
import QuantumProver.InformationTheory.ElegantJointMeasurement.TailReferencePurity
import QuantumProver.InformationTheory.ElegantJointMeasurement.Teleportation
import QuantumProver.InformationTheory.ElegantJointMeasurement.SchmidtResourceCode
import QuantumProver.InformationTheory.ElegantJointMeasurement.CompactProtocolEffects

namespace QuantumProver.ElegantJointMeasurement.Entropy

open scoped BigOperators

noncomputable section

theorem log_two_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)

theorem entropyBits_ge_minEntropy {ι : Type*} [Fintype ι]
    (p : ι → ℝ) (m : ℝ) (hm : 0 < m)
    (hnonneg : ∀ i, 0 ≤ p i) (hcap : ∀ i, p i ≤ m)
    (hsum : ∑ i, p i = 1) :
    -Real.log m / Real.log 2 ≤ entropyBits p := by
  have hterm : ∀ i, -(p i) * Real.log m ≤ Real.negMulLog (p i) := by
    intro i
    by_cases hi : p i = 0
    · simp [hi]
    · have hipos : 0 < p i := lt_of_le_of_ne (hnonneg i) (Ne.symm hi)
      have hlog : Real.log (p i) ≤ Real.log m := Real.log_le_log hipos (hcap i)
      unfold Real.negMulLog
      nlinarith [hnonneg i]
  have hsumterm : -Real.log m ≤ ∑ i, Real.negMulLog (p i) := by
    calc
      -Real.log m = ∑ i, -(p i) * Real.log m := by
        rw [← Finset.sum_mul, Finset.sum_neg_distrib, hsum]
        ring
      _ ≤ ∑ i, Real.negMulLog (p i) := Finset.sum_le_sum (fun i _ => hterm i)
  exact div_le_div_of_nonneg_right hsumterm log_two_pos.le

theorem entropyBits_ge_one_of_cap_half {ι : Type*} [Fintype ι]
    (p : ι → ℝ) (hnonneg : ∀ i, 0 ≤ p i)
    (hcap : ∀ i, p i ≤ (1 : ℝ) / 2) (hsum : ∑ i, p i = 1) :
    1 ≤ entropyBits p := by
  have h := entropyBits_ge_minEntropy p ((1 : ℝ) / 2) (by norm_num)
    hnonneg hcap hsum
  have hlog : Real.log ((1 : ℝ) / 2) = -Real.log 2 := by
    rw [Real.log_div (by norm_num) (by norm_num), Real.log_one]
    ring
  simpa [hlog, div_self (ne_of_gt log_two_pos)] using h

theorem entropyBits_split {ι : Type*} [Fintype ι]
    (x : ℝ) (μ : ι → ℝ) (hsum : ∑ i, μ i = 1) :
    entropyBits (splitWeights x μ) =
      binaryEntropyBits x + (1 - x) * entropyBits μ := by
  unfold entropyBits binaryEntropyBits
  rw [Fintype.sum_option]
  simp only [splitWeights, Real.negMulLog_mul]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum, hsum]
  rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  ring

theorem entropyBits_nonneg {ι : Type*} [Fintype ι]
    (p : ι → ℝ) (hnonneg : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) :
    0 ≤ entropyBits p := by
  classical
  have hcap : ∀ i, p i ≤ 1 := by
    intro i
    calc
      p i ≤ ∑ j, p j := Finset.single_le_sum (fun j _ => hnonneg j) (Finset.mem_univ i)
      _ = 1 := hsum
  unfold entropyBits
  exact div_nonneg (Finset.sum_nonneg fun i _ =>
    Real.negMulLog_nonneg (hnonneg i) (hcap i)) log_two_pos.le

theorem entropyBits_split_ge_binary {ι : Type*} [Fintype ι]
    (x : ℝ) (μ : ι → ℝ) (hx : x ≤ 1)
    (hnonneg : ∀ i, 0 ≤ μ i) (hsum : ∑ i, μ i = 1) :
    binaryEntropyBits x ≤ entropyBits (splitWeights x μ) := by
  rw [entropyBits_split x μ hsum]
  have h := mul_nonneg (sub_nonneg.mpr hx) (entropyBits_nonneg μ hnonneg hsum)
  linarith

theorem entry_sq_le_purity {ι : Type*} [Fintype ι]
    (p : ι → ℝ) (i : ι) : (p i) ^ 2 ≤ purity p := by
  classical
  exact Finset.single_le_sum (fun j _ => sq_nonneg (p j)) (Finset.mem_univ i)

theorem entry_le_sqrt_of_purity_le {ι : Type*} [Fintype ι]
    (p : ι → ℝ) (P : ℝ) (hP : 0 ≤ P)
    (hnonneg : ∀ i, 0 ≤ p i) (hpurity : purity p ≤ P) (i : ι) :
    p i ≤ Real.sqrt P := by
  have hsq : (p i) ^ 2 ≤ P := (entry_sq_le_purity p i).trans hpurity
  nlinarith [Real.sq_sqrt hP, Real.sqrt_nonneg P, hnonneg i]

theorem entropyBudget_lower_interval (x Htail : ℝ)
    (hxlo : (1 : ℝ) / 2 ≤ x) (hxhi : x ≤ (5 : ℝ) / 8)
    (hbinary : 1 - binaryEntropyBits x ≤ (3 : ℝ) / 4 * (2 * x - 1) ^ 2)
    (htail : (3 : ℝ) / 2 * ((2 * x - 1) / (2 * (1 - x))) ^ 2 ≤ Htail) :
    1 ≤ binaryEntropyBits x + (1 - x) * Htail := by
  have htpos : 0 < 1 - x := by linarith
  have htcap : 1 - x ≤ (1 : ℝ) / 2 := by linarith
  have hmul := mul_le_mul_of_nonneg_left htail htpos.le
  have hiden : (1 - x) * ((3 : ℝ) / 2 *
      ((2 * x - 1) / (2 * (1 - x))) ^ 2) =
      3 * (2 * x - 1) ^ 2 / (8 * (1 - x)) := by
    field_simp [ne_of_gt htpos]
    <;> ring
  rw [hiden] at hmul
  have hbound : (3 : ℝ) / 4 * (2 * x - 1) ^ 2 ≤
      3 * (2 * x - 1) ^ 2 / (8 * (1 - x)) := by
    apply (le_div_iff₀ (by positivity : 0 < 8 * (1 - x))).2
    nlinarith [sq_nonneg (2 * x - 1),
      mul_nonneg (sq_nonneg (2 * x - 1)) (sub_nonneg.mpr htcap)]
  linarith

theorem entropyBudget_upper_interval (x Htail : ℝ)
    (hxlo : (5 : ℝ) / 8 ≤ x) (hxhi : x ≤ (2 : ℝ) / 3)
    (hbinary : 1 - binaryEntropyBits x ≤ (3 : ℝ) / 4 * (2 * x - 1) ^ 2)
    (htail : (4 : ℝ) / 3 * ((2 * x - 1) / (2 * (1 - x))) ^ 2 ≤ Htail) :
    1 ≤ binaryEntropyBits x + (1 - x) * Htail := by
  have htpos : 0 < 1 - x := by linarith
  have htcap : 1 - x ≤ (3 : ℝ) / 8 := by linarith
  have hmul := mul_le_mul_of_nonneg_left htail htpos.le
  have hiden : (1 - x) * ((4 : ℝ) / 3 *
      ((2 * x - 1) / (2 * (1 - x))) ^ 2) =
      (2 * x - 1) ^ 2 / (3 * (1 - x)) := by
    field_simp [ne_of_gt htpos]
    <;> ring
  rw [hiden] at hmul
  have hbound : (3 : ℝ) / 4 * (2 * x - 1) ^ 2 ≤
      (2 * x - 1) ^ 2 / (3 * (1 - x)) := by
    apply (le_div_iff₀ (by positivity : 0 < 3 * (1 - x))).2
    nlinarith [sq_nonneg (2 * x - 1),
      mul_nonneg (sq_nonneg (2 * x - 1)) (sub_nonneg.mpr htcap)]
  linarith

theorem log_le_half_sub_inv (r : ℝ) (hr : 1 ≤ r) :
    Real.log r ≤ (r - r⁻¹) / 2 := by
  let f : ℝ → ℝ := fun y => (y - y⁻¹) / 2 - Real.log y
  have hderiv : ∀ y ∈ Set.Icc 1 r,
      HasDerivAt f ((y - 1) ^ 2 / (2 * y ^ 2)) y := by
    intro y hy
    have hypos : 0 < y := by linarith [hy.1]
    have h := (((hasDerivAt_id y).sub (hasDerivAt_inv hypos.ne')).div_const 2).sub
      (Real.hasDerivAt_log hypos.ne')
    convert h using 1
    · rfl
    · field_simp [hypos.ne']
      <;> ring
  have hmono : MonotoneOn f (Set.Icc 1 r) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 1 r)
      (fun y hy => (hderiv y hy).continuousAt.continuousWithinAt)
      (fun y hy => (hderiv y (interior_subset hy)).hasDerivWithinAt)
    intro y hy
    exact div_nonneg (sq_nonneg (y - 1)) (by positivity)
  have h := hmono (by exact ⟨le_rfl, hr⟩) (by exact ⟨hr, le_rfl⟩) hr
  simpa [f] using h

theorem log_odds_le_endpoint_curvature (x y : ℝ)
    (hx : x < 1) (hylo : (1 : ℝ) / 2 ≤ y) (hyhi : y ≤ x) :
    Real.log y - Real.log (1 - y) ≤ (y - (1 : ℝ) / 2) / (x * (1 - x)) := by
  have hypos : 0 < y := by linarith
  have htpos : 0 < 1 - y := by linarith
  have hxpos : 0 < x := hypos.trans_le hyhi
  have hxtpos : 0 < 1 - x := by linarith
  have hr : 1 ≤ y / (1 - y) := (le_div_iff₀ htpos).2 (by linarith)
  have hlog := log_le_half_sub_inv (y / (1 - y)) hr
  rw [Real.log_div hypos.ne' htpos.ne'] at hlog
  have hfrac : (y / (1 - y) - (y / (1 - y))⁻¹) / 2 =
      (y - (1 : ℝ) / 2) / (y * (1 - y)) := by
    field_simp [hypos.ne', htpos.ne']
    <;> ring
  rw [hfrac] at hlog
  apply hlog.trans
  apply (div_le_div_iff₀ (mul_pos hypos htpos) (mul_pos hxpos hxtpos)).2
  have hden : x * (1 - x) ≤ y * (1 - y) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hyhi) (by linarith : 0 ≤ x + y - 1)]
  exact mul_le_mul_of_nonneg_left hden (by linarith)

theorem binaryEntropy_deficit_le (x : ℝ)
    (hxlo : (1 : ℝ) / 2 ≤ x) (hxhi : x < 1) :
    1 - binaryEntropyBits x ≤ (2 * x - 1) ^ 2 / (8 * x * (1 - x) * Real.log 2) := by
  have hxpos : 0 < x := by linarith
  have htpos : 0 < 1 - x := by linarith
  let f : ℝ → ℝ := fun y => Real.binEntropy y +
    (y - (1 : ℝ) / 2) ^ 2 / (2 * x * (1 - x))
  let f' : ℝ → ℝ := fun y => Real.log (1 - y) - Real.log y +
    (y - (1 : ℝ) / 2) / (x * (1 - x))
  have hderiv : ∀ y ∈ Set.Icc ((1 : ℝ) / 2) x, HasDerivAt f (f' y) y := by
    intro y hy
    have hypos : 0 < y := by linarith [hy.1]
    have hyone : y ≠ 1 := by linarith [hy.2]
    have h := (Real.hasDerivAt_binEntropy hypos.ne' hyone).add
      (((hasDerivAt_id y).sub_const ((1 : ℝ) / 2)).pow 2 |>.div_const (2 * x * (1 - x)))
    convert h using 1
    · rfl
    · dsimp [f']
      norm_num
      field_simp [hxpos.ne', htpos.ne']
      <;> ring
  have hmono : MonotoneOn f (Set.Icc ((1 : ℝ) / 2) x) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc ((1 : ℝ) / 2) x)
      (fun y hy => (hderiv y hy).continuousAt.continuousWithinAt)
      (fun y hy => (hderiv y (interior_subset hy)).hasDerivWithinAt)
    intro y hy
    have hycc := interior_subset hy
    have h := log_odds_le_endpoint_curvature x y hxhi hycc.1 hycc.2
    dsimp [f']
    linarith
  have h := hmono ⟨le_rfl, hxlo⟩ ⟨hxlo, le_rfl⟩ hxlo
  have hhalf : Real.binEntropy ((1 : ℝ) / 2) = Real.log 2 := by
    simpa using Real.binEntropy_two_inv
  have hbound : Real.log 2 - Real.binEntropy x ≤
      (x - (1 : ℝ) / 2) ^ 2 / (2 * x * (1 - x)) := by
    dsimp [f] at h
    rw [hhalf] at h
    norm_num at h
    linarith
  unfold binaryEntropyBits
  have hfinal := div_le_div_of_nonneg_right hbound log_two_pos.le
  have hident : (Real.log 2 - Real.binEntropy x) / Real.log 2 =
      1 - Real.binEntropy x / Real.log 2 := by
    field_simp [log_two_pos.ne']
  rw [hident] at hfinal
  convert hfinal using 1
  field_simp [hxpos.ne', htpos.ne', log_two_pos.ne']
  <;> ring

theorem log_two_gt_two_thirds : (2 : ℝ) / 3 < Real.log 2 := by
  have h := Real.sum_range_le_log_div
    (show (0 : ℝ) ≤ (1 : ℝ) / 3 by norm_num)
    (show (1 : ℝ) / 3 < 1 by norm_num) 2
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem entropyBudget_lower_interval_proved_binary (x Htail : ℝ)
    (hxlo : (1 : ℝ) / 2 ≤ x) (hxhi : x ≤ (5 : ℝ) / 8)
    (htail : (3 : ℝ) / 2 * ((2 * x - 1) / (2 * (1 - x))) ^ 2 ≤ Htail) :
    1 ≤ binaryEntropyBits x + (1 - x) * Htail := by
  have hxpos : 0 < x := by linarith
  have htpos : 0 < 1 - x := by linarith
  have hbinary := binaryEntropy_deficit_le x hxlo (by linarith)
  have hfactor : 0 ≤ 3 * x * Real.log 2 - 1 := by
    nlinarith [log_two_gt_two_thirds,
      mul_nonneg (sub_nonneg.mpr hxlo) log_two_pos.le]
  have hbound : (2 * x - 1) ^ 2 / (8 * x * (1 - x) * Real.log 2) ≤
      3 * (2 * x - 1) ^ 2 / (8 * (1 - x)) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    nlinarith [mul_nonneg htpos.le (mul_nonneg (sq_nonneg (2 * x - 1)) hfactor)]
  have hmul := mul_le_mul_of_nonneg_left htail htpos.le
  have hiden : (1 - x) * ((3 : ℝ) / 2 *
      ((2 * x - 1) / (2 * (1 - x))) ^ 2) =
      3 * (2 * x - 1) ^ 2 / (8 * (1 - x)) := by
    field_simp [htpos.ne']
    <;> ring
  rw [hiden] at hmul
  linarith

theorem entropyBudget_upper_interval_proved_binary (x Htail : ℝ)
    (hxlo : (5 : ℝ) / 8 ≤ x) (hxhi : x ≤ (2 : ℝ) / 3)
    (htail : (4 : ℝ) / 3 * ((2 * x - 1) / (2 * (1 - x))) ^ 2 ≤ Htail) :
    1 ≤ binaryEntropyBits x + (1 - x) * Htail := by
  have hxpos : 0 < x := by linarith
  have htpos : 0 < 1 - x := by linarith
  have hbinary := binaryEntropy_deficit_le x (by linarith) (by linarith)
  have hfactor : 0 ≤ 8 * x * Real.log 2 - 3 := by
    nlinarith [log_two_gt_two_thirds,
      mul_nonneg (sub_nonneg.mpr hxlo) log_two_pos.le]
  have hbound : (2 * x - 1) ^ 2 / (8 * x * (1 - x) * Real.log 2) ≤
      (2 * x - 1) ^ 2 / (3 * (1 - x)) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    nlinarith [mul_nonneg htpos.le (mul_nonneg (sq_nonneg (2 * x - 1)) hfactor)]
  have hmul := mul_le_mul_of_nonneg_left htail htpos.le
  have hiden : (1 - x) * ((4 : ℝ) / 3 *
      ((2 * x - 1) / (2 * (1 - x))) ^ 2) =
      (2 * x - 1) ^ 2 / (3 * (1 - x)) := by
    field_simp [htpos.ne']
    <;> ring
  rw [hiden] at hmul
  linarith

theorem log_two_lt_seven_tenths : Real.log 2 < (7 : ℝ) / 10 := by
  have h := Real.log_div_le_sum_range_add
    (show (0 : ℝ) ≤ (1 : ℝ) / 3 by norm_num)
    (show (1 : ℝ) / 3 < 1 by norm_num) 3
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem binaryEntropy_lower_log (q : ℝ) (hqpos : 0 < q) (hqone : q < 1) :
    q * (-Real.log q + 1 - q) / Real.log 2 ≤ binaryEntropyBits q := by
  have htpos : 0 < 1 - q := by linarith
  have hlog := Real.log_le_sub_one_of_pos htpos
  have hmul := mul_le_mul_of_nonneg_left hlog htpos.le
  unfold binaryEntropyBits Real.binEntropy
  rw [Real.log_inv, Real.log_inv]
  apply div_le_div_of_nonneg_right _ log_two_pos.le
  nlinarith

theorem binaryEntropy_ge_six_mul (q : ℝ)
    (hqlo : 0 ≤ q) (hqhi : q ≤ (1 : ℝ) / 32) :
    6 * q ≤ binaryEntropyBits q := by
  by_cases hqzero : q = 0
  · simp [hqzero, binaryEntropyBits]
  have hqpos : 0 < q := lt_of_le_of_ne hqlo (Ne.symm hqzero)
  have hqone : q < 1 := by linarith
  have hlog := Real.log_le_log hqpos hqhi
  have hpow : Real.log ((1 : ℝ) / 32) = -5 * Real.log 2 := by
    have h := Real.log_pow (2 : ℝ) 5
    norm_num at h
    rw [Real.log_div (by norm_num) (by norm_num), Real.log_one]
    linarith
  rw [hpow] at hlog
  have hbound := binaryEntropy_lower_log q hqpos hqone
  have hlog2 : Real.log 2 ≤ (3 : ℝ) / 4 := by
    have h := log_le_half_sub_inv 2 (by norm_num)
    norm_num at h
    exact h
  have hnum : 6 * q * Real.log 2 ≤ q * (-Real.log q + 1 - q) := by
    have hgap : Real.log 2 ≤ 1 - q := by linarith
    nlinarith [mul_nonneg hqlo (sub_nonneg.mpr hgap),
      mul_nonneg hqlo (show 0 ≤ -Real.log q - 5 * Real.log 2 by linarith)]
  exact (le_div_iff₀ log_two_pos).2 hnum |>.trans hbound

theorem binaryEntropy_ge_quadratic_small (q : ℝ)
    (hqlo : 0 ≤ q) (hqhi : q ≤ (1 : ℝ) / 15) :
    (16 : ℝ) / 3 * q * (1 - q / 2) ≤ binaryEntropyBits q := by
  by_cases hqzero : q = 0
  · simp [hqzero, binaryEntropyBits]
  have hqpos : 0 < q := lt_of_le_of_ne hqlo (Ne.symm hqzero)
  have hqone : q < 1 := by linarith
  have h15 : (31 : ℝ) / 8 * Real.log 2 ≤ Real.log 15 := by
    have h := Real.log_lt_log (by positivity : (0 : ℝ) < 2 ^ 31)
      (by norm_num : (2 : ℝ) ^ 31 < 15 ^ 8)
    rw [Real.log_pow, Real.log_pow] at h
    norm_num at h
    linarith
  have hlog := Real.log_le_sub_one_of_pos (by positivity : 0 < 15 * q)
  rw [Real.log_mul (by norm_num) hqpos.ne'] at hlog
  have hqlog : (31 : ℝ) / 8 * Real.log 2 + 1 - 15 * q ≤ -Real.log q := by
    linarith
  have hcoef : (16 : ℝ) / 3 * (1 - q / 2) * Real.log 2 ≤
      (31 : ℝ) / 8 * Real.log 2 + 2 - 16 * q := by
    have hn : 0 ≤ (35 / 24 - 8 / 3 * q : ℝ) := by linarith
    nlinarith [log_two_lt_seven_tenths,
      mul_nonneg hn (show 0 ≤ (7 : ℝ) / 10 - Real.log 2 by linarith [log_two_lt_seven_tenths])]
  have hnum : ((16 : ℝ) / 3 * q * (1 - q / 2)) * Real.log 2 ≤
      q * (-Real.log q + 1 - q) := by
    nlinarith [mul_le_mul_of_nonneg_left hcoef hqlo,
      mul_le_mul_of_nonneg_left hqlog hqlo]
  exact (le_div_iff₀ log_two_pos).2 hnum |>.trans (binaryEntropy_lower_log q hqpos hqone)

theorem tailBinaryEntropy_lower (κ : ℝ) (hklo : 0 ≤ κ) (hkhi : κ ≤ (1 : ℝ) / 3) :
    (3 : ℝ) / 2 * κ ^ 2 ≤ binaryEntropyBits (1 - Real.sqrt (1 - κ ^ 2 / 2)) := by
  have hksq : κ ^ 2 ≤ (1 : ℝ) / 9 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hkhi) (by linarith : 0 ≤ (1 : ℝ) / 3 + κ)]
  have harg : 0 ≤ 1 - κ ^ 2 / 2 := by nlinarith
  have hs := Real.sq_sqrt harg
  have hspos := Real.sqrt_nonneg (1 - κ ^ 2 / 2)
  let q := 1 - Real.sqrt (1 - κ ^ 2 / 2)
  have hqlo : 0 ≤ q := by dsimp [q]; nlinarith [sq_nonneg κ]
  have hqhi : q ≤ (1 : ℝ) / 32 := by dsimp [q]; nlinarith
  have hid : κ ^ 2 = 4 * q * (1 - q / 2) := by dsimp [q]; nlinarith
  have h := binaryEntropy_ge_six_mul q hqlo hqhi
  dsimp [q] at h
  dsimp [q] at hid
  nlinarith [sq_nonneg (1 - Real.sqrt (1 - κ ^ 2 / 2))]

theorem tailBinaryEntropy_upper (κ : ℝ) (hklo : 0 ≤ κ) (hkhi : κ ≤ (1 : ℝ) / 2) :
    (4 : ℝ) / 3 * κ ^ 2 ≤ binaryEntropyBits (1 - Real.sqrt (1 - κ ^ 2 / 2)) := by
  have hksq : κ ^ 2 ≤ (1 : ℝ) / 4 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hkhi) (by linarith : 0 ≤ (1 : ℝ) / 2 + κ)]
  have harg : 0 ≤ 1 - κ ^ 2 / 2 := by nlinarith
  have hs := Real.sq_sqrt harg
  have hspos := Real.sqrt_nonneg (1 - κ ^ 2 / 2)
  let q := 1 - Real.sqrt (1 - κ ^ 2 / 2)
  have hqlo : 0 ≤ q := by dsimp [q]; nlinarith [sq_nonneg κ]
  have hqhi : q ≤ (1 : ℝ) / 15 := by dsimp [q]; nlinarith
  have hid : κ ^ 2 = 4 * q * (1 - q / 2) := by dsimp [q]; nlinarith
  have h := binaryEntropy_ge_quadratic_small q hqlo hqhi
  dsimp [q] at h
  dsimp [q] at hid
  nlinarith

theorem negMulLog_sum_le_sum {ι : Type*} (s : Finset ι) (p : ι → ℝ)
    (hnonneg : ∀ i ∈ s, 0 ≤ p i) :
    Real.negMulLog (∑ i ∈ s, p i) ≤ ∑ i ∈ s, Real.negMulLog (p i) := by
  classical
  have hterm : ∀ i ∈ s, -(p i) * Real.log (∑ j ∈ s, p j) ≤ Real.negMulLog (p i) := by
    intro i hi
    by_cases hpzero : p i = 0
    · simp [hpzero]
    have hppos : 0 < p i := lt_of_le_of_ne (hnonneg i hi) (Ne.symm hpzero)
    have hcap := Finset.single_le_sum hnonneg hi
    have hlog := Real.log_le_log hppos hcap
    unfold Real.negMulLog
    nlinarith [hnonneg i hi]
  calc
    Real.negMulLog (∑ i ∈ s, p i) = ∑ i ∈ s, -(p i) * Real.log (∑ j ∈ s, p j) := by
      unfold Real.negMulLog
      rw [← Finset.sum_mul, Finset.sum_neg_distrib]
    _ ≤ ∑ i ∈ s, Real.negMulLog (p i) := Finset.sum_le_sum hterm

theorem entropyBits_ge_binary_entry {ι : Type*} [Fintype ι]
    (p : ι → ℝ) (hnonneg : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) (i : ι) :
    binaryEntropyBits (p i) ≤ entropyBits p := by
  classical
  have hmass := Finset.sum_erase_add Finset.univ p (Finset.mem_univ i)
  have hrest : ∑ j ∈ Finset.univ.erase i, p j = 1 - p i := by
    rw [hsum] at hmass
    linarith
  have hgroup := negMulLog_sum_le_sum (Finset.univ.erase i) p (fun j _ => hnonneg j)
  rw [hrest] at hgroup
  have hent := Finset.sum_erase_add Finset.univ (fun j => Real.negMulLog (p j)) (Finset.mem_univ i)
  unfold binaryEntropyBits entropyBits
  apply div_le_div_of_nonneg_right _ log_two_pos.le
  rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  linarith

theorem entropyBits_ge_binary_sqrt_purity {ι : Type*} [Fintype ι]
    (p : ι → ℝ) (P : ℝ) (hPlo : 0 ≤ P) (hPhi : P ≤ 1)
    (hnonneg : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) (hpurity : purity p ≤ P) :
    binaryEntropyBits (1 - Real.sqrt P) ≤ entropyBits p := by
  classical
  by_cases hcap : ∀ i, p i ≤ (1 : ℝ) / 2
  · have hbits : binaryEntropyBits (1 - Real.sqrt P) ≤ 1 := by
      unfold binaryEntropyBits
      apply (div_le_iff₀ log_two_pos).2
      simpa using (Real.binEntropy_le_log_two (p := 1 - Real.sqrt P))
    exact hbits.trans (entropyBits_ge_one_of_cap_half p hnonneg hcap hsum)
  push_neg at hcap
  obtain ⟨i, hi⟩ := hcap
  have hentry := entry_le_sqrt_of_purity_le p P hPlo hnonneg hpurity i
  have hpone : p i ≤ 1 := by
    calc
      p i ≤ ∑ j, p j := Finset.single_le_sum (fun j _ => hnonneg j) (Finset.mem_univ i)
      _ = 1 := hsum
  have hsone : Real.sqrt P ≤ 1 := by
    nlinarith [Real.sq_sqrt hPlo, Real.sqrt_nonneg P]
  have hanti := Real.binEntropy_strictAntiOn.antitoneOn
    (show p i ∈ Set.Icc (2 : ℝ)⁻¹ 1 from ⟨by convert hi.le using 1 <;> norm_num, hpone⟩)
    (show Real.sqrt P ∈ Set.Icc (2 : ℝ)⁻¹ 1 from
      ⟨by convert hi.le.trans hentry using 1 <;> norm_num, hsone⟩)
    hentry
  have hbits : binaryEntropyBits (1 - Real.sqrt P) ≤ binaryEntropyBits (p i) := by
    unfold binaryEntropyBits
    rw [Real.binEntropy_one_sub]
    exact div_le_div_of_nonneg_right hanti log_two_pos.le
  exact hbits.trans (entropyBits_ge_binary_entry p hnonneg hsum i)

theorem entropyTail_lower {ι : Type*} [Fintype ι]
    (μ : ι → ℝ) (κ : ℝ) (hklo : 0 ≤ κ) (hkhi : κ ≤ (1 : ℝ) / 3)
    (hnonneg : ∀ i, 0 ≤ μ i) (hsum : ∑ i, μ i = 1)
    (hpurity : purity μ ≤ 1 - κ ^ 2 / 2) :
    (3 : ℝ) / 2 * κ ^ 2 ≤ entropyBits μ := by
  have hksq : κ ^ 2 ≤ (1 : ℝ) / 9 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hkhi) (by linarith : 0 ≤ (1 : ℝ) / 3 + κ)]
  exact (tailBinaryEntropy_lower κ hklo hkhi).trans
    (entropyBits_ge_binary_sqrt_purity μ (1 - κ ^ 2 / 2)
      (by nlinarith) (by nlinarith [sq_nonneg κ]) hnonneg hsum hpurity)

theorem entropyTail_upper {ι : Type*} [Fintype ι]
    (μ : ι → ℝ) (κ : ℝ) (hklo : 0 ≤ κ) (hkhi : κ ≤ (1 : ℝ) / 2)
    (hnonneg : ∀ i, 0 ≤ μ i) (hsum : ∑ i, μ i = 1)
    (hpurity : purity μ ≤ 1 - κ ^ 2 / 2) :
    (4 : ℝ) / 3 * κ ^ 2 ≤ entropyBits μ := by
  have hksq : κ ^ 2 ≤ (1 : ℝ) / 4 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hkhi) (by linarith : 0 ≤ (1 : ℝ) / 2 + κ)]
  exact (tailBinaryEntropy_upper κ hklo hkhi).trans
    (entropyBits_ge_binary_sqrt_purity μ (1 - κ ^ 2 / 2)
      (by nlinarith) (by nlinarith [sq_nonneg κ]) hnonneg hsum hpurity)

theorem entropyBits_ge_one_of_tail_necessary {ι : Type*} [Fintype ι]
    (x : ℝ) (μ : ι → ℝ) (hxlo : (1 : ℝ) / 2 ≤ x) (hxhi : x ≤ (2 : ℝ) / 3)
    (hnonneg : ∀ i, 0 ≤ μ i) (hsum : ∑ i, μ i = 1)
    (hnecessary : (2 * x - 1) ^ 2 ≤ 8 * (1 - x) ^ 2 * (1 - purity μ)) :
    1 ≤ entropyBits (splitWeights x μ) := by
  have htpos : 0 < 1 - x := by linarith
  let κ := (2 * x - 1) / (2 * (1 - x))
  have hklo : 0 ≤ κ := by dsimp [κ]; exact div_nonneg (by linarith) (by positivity)
  have hratio : κ ^ 2 / 2 = (2 * x - 1) ^ 2 / (8 * (1 - x) ^ 2) := by
    dsimp [κ]
    field_simp [htpos.ne']
    <;> ring
  have hpurity : purity μ ≤ 1 - κ ^ 2 / 2 := by
    have h : κ ^ 2 / 2 ≤ 1 - purity μ := by
      rw [hratio]
      exact (div_le_iff₀ (by positivity)).2 (by nlinarith [hnecessary])
    linarith
  rw [entropyBits_split x μ hsum]
  by_cases hxmid : x ≤ (5 : ℝ) / 8
  · have hkhi : κ ≤ (1 : ℝ) / 3 := by
      dsimp [κ]
      exact (div_le_iff₀ (by positivity)).2 (by linarith)
    exact entropyBudget_lower_interval_proved_binary x (entropyBits μ) hxlo hxmid
      (entropyTail_lower μ κ hklo hkhi hnonneg hsum hpurity)
  · have hkhi : κ ≤ (1 : ℝ) / 2 := by
      dsimp [κ]
      exact (div_le_iff₀ (by positivity)).2 (by linarith)
    exact entropyBudget_upper_interval_proved_binary x (entropyBits μ) (by linarith) hxhi
      (entropyTail_upper μ κ hklo hkhi hnonneg hsum hpurity)

end

end QuantumProver.ElegantJointMeasurement.Entropy

namespace QuantumProver.ElegantJointMeasurement.Overlap

open scoped BigOperators Matrix ComplexConjugate

noncomputable section

theorem two_term_cauchy (a b c d : ℂ) :
    Complex.normSq (a * c + b * d) ≤
      (Complex.normSq a + Complex.normSq b) * (Complex.normSq c + Complex.normSq d) := by
  have h := Complex.normSq_nonneg (a * conj d - b * conj c)
  have hid : (Complex.normSq a + Complex.normSq b) * (Complex.normSq c + Complex.normSq d) -
      Complex.normSq (a * c + b * d) = Complex.normSq (a * conj d - b * conj c) := by
    simp [Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
    <;> ring
  linarith

def tripletScale : ℝ := 1 / Real.sqrt 2

def tripletCoefficient (u v w : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  ((tripletScale : ℝ) : ℂ) • !![-(u : ℂ) + Complex.I * v, w; w, (u : ℂ) + Complex.I * v]

theorem tripletScale_sq : tripletScale ^ 2 = (1 : ℝ) / 2 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hn : Real.sqrt 2 ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
  unfold tripletScale
  field_simp [hn]
  nlinarith

theorem triplet_contraction_norm (u v w : ℝ) (hsphere : u ^ 2 + v ^ 2 + w ^ 2 = 1)
    (b0 b1 : ℂ) :
    Complex.normSq ((tripletScale : ℂ) *
      ((-(u : ℂ) + Complex.I * v) * conj b0 + w * conj b1)) +
    Complex.normSq ((tripletScale : ℂ) *
      (w * conj b0 + ((u : ℂ) + Complex.I * v) * conj b1)) =
      (1 : ℝ) / 2 * (Complex.normSq b0 + Complex.normSq b1) := by
  have hid :
      Complex.normSq ((-(u : ℂ) + Complex.I * v) * conj b0 + w * conj b1) +
      Complex.normSq (w * conj b0 + ((u : ℂ) + Complex.I * v) * conj b1) =
      (u ^ 2 + v ^ 2 + w ^ 2) * (Complex.normSq b0 + Complex.normSq b1) := by
    simp [Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
    <;> ring
  rw [Complex.normSq_mul, Complex.normSq_mul, Complex.normSq_ofReal]
  rw [← pow_two, ← mul_add, hid, hsphere, tripletScale_sq]
  ring

theorem triplet_product_overlap_le_half (u v w : ℝ)
    (hsphere : u ^ 2 + v ^ 2 + w ^ 2 = 1) (a b : Fin 2 → ℂ) :
    2 * Complex.normSq (∑ i : Fin 2, ∑ j : Fin 2,
      conj (tripletCoefficient u v w i j) * a i * b j) ≤
      (Complex.normSq (a 0) + Complex.normSq (a 1)) *
      (Complex.normSq (b 0) + Complex.normSq (b 1)) := by
  let c0 : ℂ := (tripletScale : ℂ) *
    ((-(u : ℂ) + Complex.I * v) * conj (b 0) + w * conj (b 1))
  let c1 : ℂ := (tripletScale : ℂ) *
    (w * conj (b 0) + ((u : ℂ) + Complex.I * v) * conj (b 1))
  have hnorm : Complex.normSq c0 + Complex.normSq c1 =
      (1 : ℝ) / 2 * (Complex.normSq (b 0) + Complex.normSq (b 1)) :=
    triplet_contraction_norm u v w hsphere (b 0) (b 1)
  have hcs := two_term_cauchy (conj c0) (conj c1) (a 0) (a 1)
  rw [Complex.normSq_conj, Complex.normSq_conj, hnorm] at hcs
  have hamp : (∑ i : Fin 2, ∑ j : Fin 2,
      conj (tripletCoefficient u v w i j) * a i * b j) = conj c0 * a 0 + conj c1 * a 1 := by
    simp [c0, c1, tripletCoefficient, Fin.sum_univ_two, Matrix.smul_apply]
    <;> ring
  rw [hamp]
  nlinarith

def coefficientInner (T E : Matrix (Fin 2) (Fin 2) ℂ) : ℂ :=
  ∑ i : Fin 2, ∑ j : Fin 2, conj (T i j) * E i j

def singletCoefficient : Matrix (Fin 2) (Fin 2) ℂ :=
  (tripletScale : ℂ) • !![0, 1; -1, 0]

def pauliDirection (u v w : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![w, (u : ℂ) - Complex.I * v; (u : ℂ) + Complex.I * v, -w]

def ejmDirectionCoefficient (u v w : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (1 / 2 : ℂ) • singletCoefficient + ((Real.sqrt 3 / 2 : ℝ) : ℂ) • tripletCoefficient u v w

theorem triplet_eq_pauli_singlet (u v w : ℝ) :
    tripletCoefficient u v w = pauliDirection u v w * singletCoefficient := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [tripletCoefficient, pauliDirection, singletCoefficient, Matrix.mul_apply,
      Fin.sum_univ_two] <;> ring

theorem ejmDirection_eq_pauli_singlet (u v w : ℝ) :
    ejmDirectionCoefficient u v w =
      ((1 / 2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) +
        ((Real.sqrt 3 / 2 : ℝ) : ℂ) • pauliDirection u v w) * singletCoefficient := by
  rw [ejmDirectionCoefficient, triplet_eq_pauli_singlet, Matrix.add_mul,
    Matrix.smul_mul, Matrix.smul_mul, Matrix.one_mul]

theorem coefficientInner_add (T E F : Matrix (Fin 2) (Fin 2) ℂ) :
    coefficientInner T (E + F) = coefficientInner T E + coefficientInner T F := by
  simp [coefficientInner, Fin.sum_univ_two]
  <;> ring

theorem coefficientInner_smul (T E : Matrix (Fin 2) (Fin 2) ℂ) (c : ℂ) :
    coefficientInner T (c • E) = c * coefficientInner T E := by
  simp [coefficientInner, Fin.sum_univ_two]
  <;> ring

theorem triplet_inner_self (u v w : ℝ) (hsphere : u ^ 2 + v ^ 2 + w ^ 2 = 1) :
    coefficientInner (tripletCoefficient u v w) (tripletCoefficient u v w) = 1 := by
  have hn : tripletScale ^ 2 * (u ^ 2 + v ^ 2 + w ^ 2) = (1 : ℝ) / 2 := by
    rw [hsphere, mul_one, tripletScale_sq]
  apply Complex.ext <;>
    simp [coefficientInner, tripletCoefficient, Fin.sum_univ_two, Complex.mul_re, Complex.mul_im] <;>
    nlinarith [hn]

theorem triplet_inner_singlet (u v w : ℝ) :
    coefficientInner (tripletCoefficient u v w) singletCoefficient = 0 := by
  simp [coefficientInner, tripletCoefficient, singletCoefficient, Fin.sum_univ_two]
  <;> ring

theorem triplet_inner_ejm (u v w : ℝ) (hsphere : u ^ 2 + v ^ 2 + w ^ 2 = 1) :
    coefficientInner (tripletCoefficient u v w) (ejmDirectionCoefficient u v w) =
      ((Real.sqrt 3 / 2 : ℝ) : ℂ) := by
  rw [ejmDirectionCoefficient, coefficientInner_add, coefficientInner_smul,
    coefficientInner_smul, triplet_inner_singlet, triplet_inner_self u v w hsphere]
  ring

theorem triplet_ejm_overlap_sq (u v w : ℝ) (hsphere : u ^ 2 + v ^ 2 + w ^ 2 = 1) :
    Complex.normSq (coefficientInner (tripletCoefficient u v w)
      (ejmDirectionCoefficient u v w)) = (3 : ℝ) / 4 := by
  rw [triplet_inner_ejm u v w hsphere, Complex.normSq_ofReal]
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]

def productKet (a b : Fin 2 → ℂ) : Fin 2 × Fin 2 → ℂ := fun q => a q.1 * b q.2

def ketEffect {δ : Type*} (v : δ → ℂ) : Matrix δ δ ℂ := fun i j => v i * conj (v j)

def coefficientVector (T : Matrix (Fin 2) (Fin 2) ℂ) : Fin 2 × Fin 2 → ℂ :=
  fun q => T q.1 q.2

def effectQuadratic {δ : Type*} [Fintype δ] (G : Matrix δ δ ℂ) (v : δ → ℂ) : ℝ :=
  (star v ⬝ᵥ (G *ᵥ v)).re

theorem trace_product_ket (a b : Fin 2 → ℂ) :
    (Matrix.trace (ketEffect (productKet a b))).re =
      (Complex.normSq (a 0) + Complex.normSq (a 1)) *
      (Complex.normSq (b 0) + Complex.normSq (b 1)) := by
  simp [Matrix.trace, Matrix.diag, ketEffect, productKet, Fintype.sum_prod_type,
    Fin.sum_univ_two, Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
  <;> ring

theorem product_ket_expectation (T : Matrix (Fin 2) (Fin 2) ℂ) (a b : Fin 2 → ℂ) :
    effectQuadratic (ketEffect (productKet a b)) (coefficientVector T) =
      Complex.normSq (coefficientInner T (fun i j => a i * b j)) := by
  simp [effectQuadratic, dotProduct, Matrix.mulVec, ketEffect, productKet,
    coefficientVector, coefficientInner, Fintype.sum_prod_type, Fin.sum_univ_two,
    Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
  <;> ring

theorem coefficient_ket_expectation (T E : Matrix (Fin 2) (Fin 2) ℂ) :
    effectQuadratic (ketEffect (coefficientVector E)) (coefficientVector T) =
      Complex.normSq (coefficientInner T E) := by
  simp [effectQuadratic, dotProduct, Matrix.mulVec, ketEffect,
    coefficientVector, coefficientInner, Fintype.sum_prod_type, Fin.sum_univ_two,
    Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
  <;> ring

theorem effectQuadratic_sum {δ ι : Type*} [Fintype δ] [Fintype ι]
    (G : ι → Matrix δ δ ℂ) (v : δ → ℂ) :
    effectQuadratic (∑ i, G i) v = ∑ i, effectQuadratic (G i) v := by
  simp [effectQuadratic, Matrix.sum_mulVec, dotProduct_sum]

theorem effectQuadratic_sub {δ : Type*} [Fintype δ]
    (G H : Matrix δ δ ℂ) (v : δ → ℂ) :
    effectQuadratic (G - H) v = effectQuadratic G v - effectQuadratic H v := by
  simp [effectQuadratic, Matrix.sub_mulVec, dotProduct_sub]

theorem effectQuadratic_smul_real {δ : Type*} [Fintype δ]
    (G : Matrix δ δ ℂ) (v : δ → ℂ) (x : ℝ) :
    effectQuadratic ((x : ℂ) • G) v = x * effectQuadratic G v := by
  simp [effectQuadratic, Matrix.smul_mulVec, dotProduct_smul, Complex.mul_re]

def separableEffect {ι : Type*} [Fintype ι]
    (a b : ι → Fin 2 → ℂ) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  ∑ i, ketEffect (productKet (a i) (b i))

theorem separable_triplet_trace_bound {ι : Type*} [Fintype ι]
    (a b : ι → Fin 2 → ℂ) (u v w : ℝ)
    (hsphere : u ^ 2 + v ^ 2 + w ^ 2 = 1) :
    2 * effectQuadratic (separableEffect a b)
      (coefficientVector (tripletCoefficient u v w)) ≤
      (Matrix.trace (separableEffect a b)).re := by
  classical
  have h (i : ι) :
      2 * effectQuadratic (ketEffect (productKet (a i) (b i)))
        (coefficientVector (tripletCoefficient u v w)) ≤
        (Matrix.trace (ketEffect (productKet (a i) (b i)))).re := by
    rw [product_ket_expectation, trace_product_ket]
    simpa [coefficientInner, mul_assoc] using
      triplet_product_overlap_le_half u v w hsphere (a i) (b i)
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => h i)
  simpa [separableEffect, effectQuadratic_sum, Matrix.trace_sum,
    Finset.mul_sum] using hs

open scoped ComplexOrder MatrixOrder

theorem effectQuadratic_nonneg {δ : Type*} [Fintype δ]
    (G : Matrix δ δ ℂ) (hG : G.PosSemidef) (v : δ → ℂ) :
    0 ≤ effectQuadratic G v :=
  (Complex.nonneg_iff.mp (hG.dotProduct_mulVec_nonneg v)).1

theorem ejm_dominated_triplet_expectation
    (G : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
    (x u v w : ℝ) (hsphere : u ^ 2 + v ^ 2 + w ^ 2 = 1)
    (hdom : (G - (x : ℂ) • ketEffect
      (coefficientVector (ejmDirectionCoefficient u v w))).PosSemidef) :
    x * (3 : ℝ) / 4 ≤ effectQuadratic G
      (coefficientVector (tripletCoefficient u v w)) := by
  have h := effectQuadratic_nonneg _ hdom
    (coefficientVector (tripletCoefficient u v w))
  rw [effectQuadratic_sub, effectQuadratic_smul_real,
    coefficient_ket_expectation, triplet_ejm_overlap_sq u v w hsphere] at h
  linarith

theorem separable_four_effect_cap {ι : Fin 4 → Type*} [∀ j, Fintype (ι j)]
    (a b : ∀ j, ι j → Fin 2 → ℂ) (u v w : Fin 4 → ℝ) (x : ℝ)
    (hsphere : ∀ j, u j ^ 2 + v j ^ 2 + w j ^ 2 = 1)
    (hcomplete : (∑ j, separableEffect (a j) (b j)) =
      (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ))
    (hdom : ∀ j, (separableEffect (a j) (b j) - (x : ℂ) • ketEffect
      (coefficientVector (ejmDirectionCoefficient (u j) (v j) (w j)))).PosSemidef) :
    x ≤ (2 : ℝ) / 3 := by
  classical
  have hj (j : Fin 4) :
      (3 : ℝ) / 2 * x ≤ (Matrix.trace (separableEffect (a j) (b j))).re := by
    have hl := ejm_dominated_triplet_expectation _ x (u j) (v j) (w j)
      (hsphere j) (hdom j)
    have hu := separable_triplet_trace_bound (a j) (b j) (u j) (v j) (w j)
      (hsphere j)
    linarith
  have hsum := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hj j)
  have htr : (∑ j, (Matrix.trace (separableEffect (a j) (b j))).re) = 4 := by
    calc
      _ = (Matrix.trace (∑ j, separableEffect (a j) (b j))).re := by simp
      _ = 4 := by rw [hcomplete]; norm_num
  rw [htr] at hsum
  norm_num at hsum
  linarith

open InnerProductSpace

def selectedSchmidtEffect {κ : Type*} [Fintype κ] (k : κ)
    (F : Matrix (QuantumProver.ElegantJointMeasurement.Augmented.Index κ) (QuantumProver.ElegantJointMeasurement.Augmented.Index κ) ℂ) :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  F.submatrix (fun q => ((q.1, k), (q.2, k))) (fun q => ((q.1, k), (q.2, k)))

theorem selectedSchmidtEffect_sum {κ ι : Type*} [Fintype κ] [Fintype ι]
    (k : κ) (F : ι → Matrix (QuantumProver.ElegantJointMeasurement.Augmented.Index κ) (QuantumProver.ElegantJointMeasurement.Augmented.Index κ) ℂ) :
    selectedSchmidtEffect k (∑ i, F i) = ∑ i, selectedSchmidtEffect k (F i) := by
  ext i j
  simp [selectedSchmidtEffect, Matrix.sum_apply]

theorem selectedSchmidtEffect_one {κ : Type*} [Fintype κ] [DecidableEq κ] (k : κ) :
    selectedSchmidtEffect k (1 : Matrix (QuantumProver.ElegantJointMeasurement.Augmented.Index κ) (QuantumProver.ElegantJointMeasurement.Augmented.Index κ) ℂ) = 1 := by
  ext i j
  simp [selectedSchmidtEffect, Matrix.one_apply, Prod.ext_iff]

theorem selectedSchmidtEffect_product {κ : Type*} [Fintype κ] [DecidableEq κ]
    (k : κ) (A B : Matrix (Fin 2) κ ℂ) :
    selectedSchmidtEffect k (QuantumProver.ElegantJointMeasurement.Augmented.effectMatrix (QuantumProver.ElegantJointMeasurement.ResourceCode.productKet A B)) =
      ketEffect (productKet (fun i => A i k) (fun j => B j k)) := by
  rfl

theorem selectedSchmidtEffect_sub {κ : Type*} [Fintype κ] (k : κ)
    (F G : Matrix (QuantumProver.ElegantJointMeasurement.Augmented.Index κ) (QuantumProver.ElegantJointMeasurement.Augmented.Index κ) ℂ) :
    selectedSchmidtEffect k (F - G) = selectedSchmidtEffect k F - selectedSchmidtEffect k G :=
  rfl

theorem effectMatrix_posSemidef {κ : Type*} [Fintype κ] [DecidableEq κ]
    (z : QuantumProver.ElegantJointMeasurement.Augmented.Ket κ) : (QuantumProver.ElegantJointMeasurement.Augmented.effectMatrix z).PosSemidef := by
  let f : QuantumProver.ElegantJointMeasurement.Augmented.Index κ → ℂ := fun q => z q
  have hf : star f = (fun q => conj (f q)) := by ext q; rfl
  have h := Matrix.posSemidef_vecMulVec_self_star f
  rw [hf] at h
  exact h

theorem selectedSchmidtEffect_code {κ : Type*} [Fintype κ] [DecidableEq κ]
    (β : κ → ℝ) (k : κ) (E : QuantumProver.ElegantJointMeasurement.ResourceCode.InputSpace (Fin 2) (Fin 2)) :
    selectedSchmidtEffect k (QuantumProver.ElegantJointMeasurement.Augmented.effectMatrix (QuantumProver.ElegantJointMeasurement.ResourceCode.codeContinuous β E)) =
      ((β k ^ 2 : ℝ) : ℂ) • ketEffect (fun q => E q) := by
  ext i j
  simp [selectedSchmidtEffect, QuantumProver.ElegantJointMeasurement.Augmented.effectMatrix, Matrix.vecMulVec_apply,
    QuantumProver.ElegantJointMeasurement.ResourceCode.codeContinuous_apply, QuantumProver.ElegantJointMeasurement.ResourceCode.codeLinear_apply,
    ketEffect, Complex.conj_ofReal, Matrix.smul_apply]
  push_cast
  ring

theorem code_effect_domination {κ : Type*} [Fintype κ] [DecidableEq κ]
    (β : κ → ℝ) (hβ : ∑ k, β k ^ 2 = 1)
    (F : Matrix (QuantumProver.ElegantJointMeasurement.Augmented.Index κ) (QuantumProver.ElegantJointMeasurement.Augmented.Index κ) ℂ)
    (hF : F.PosSemidef) (hupper : (1 - F).PosSemidef)
    (E : QuantumProver.ElegantJointMeasurement.ResourceCode.InputSpace (Fin 2) (Fin 2)) (hE : ‖E‖ = 1)
    (hcompression : (QuantumProver.ElegantJointMeasurement.ResourceCode.codeContinuous β).adjoint ∘L
      (QuantumProver.ElegantJointMeasurement.ClosureJoin.effectOperator F ∘L QuantumProver.ElegantJointMeasurement.ResourceCode.codeContinuous β) =
        rankOne ℂ E E) :
    (F - QuantumProver.ElegantJointMeasurement.Augmented.effectMatrix (QuantumProver.ElegantJointMeasurement.ResourceCode.codeContinuous β E)).PosSemidef := by
  have hfix := QuantumProver.ElegantJointMeasurement.ResourceCode.code_saturation β hβ
    (QuantumProver.ElegantJointMeasurement.ClosureJoin.effectOperator F) E hE
    ((QuantumProver.ElegantJointMeasurement.ClosureJoin.effectOperator_upper_iff F).mpr hupper) hcompression
  have hdom := QuantumProver.ElegantJointMeasurement.RankOne.positive_domination_of_fixed_unit
    (QuantumProver.ElegantJointMeasurement.ClosureJoin.effectOperator F) (QuantumProver.ElegantJointMeasurement.ResourceCode.codeContinuous β E)
    ((QuantumProver.ElegantJointMeasurement.ClosureJoin.effectOperator_positive_iff F).mpr hF)
    ((QuantumProver.ElegantJointMeasurement.ResourceCode.code_norm β hβ E).trans hE) hfix
  apply (QuantumProver.ElegantJointMeasurement.ClosureJoin.effectOperator_positive_iff _).mp
  rw [map_sub, QuantumProver.ElegantJointMeasurement.ClosureJoin.effectOperator_rankOne]
  exact hdom

theorem selectedSchmidtEffect_domination {κ : Type*} [Fintype κ] [DecidableEq κ]
    (β : κ → ℝ) (hβ : ∑ k, β k ^ 2 = 1) (k : κ)
    (F : Matrix (QuantumProver.ElegantJointMeasurement.Augmented.Index κ) (QuantumProver.ElegantJointMeasurement.Augmented.Index κ) ℂ)
    (hF : F.PosSemidef) (hupper : (1 - F).PosSemidef)
    (E : QuantumProver.ElegantJointMeasurement.ResourceCode.InputSpace (Fin 2) (Fin 2)) (hE : ‖E‖ = 1)
    (hcompression : (QuantumProver.ElegantJointMeasurement.ResourceCode.codeContinuous β).adjoint ∘L
      (QuantumProver.ElegantJointMeasurement.ClosureJoin.effectOperator F ∘L QuantumProver.ElegantJointMeasurement.ResourceCode.codeContinuous β) =
        rankOne ℂ E E) :
    (selectedSchmidtEffect k F - ((β k ^ 2 : ℝ) : ℂ) • ketEffect (fun q => E q)).PosSemidef := by
  have hdom := (code_effect_domination β hβ F hF hupper E hE hcompression).submatrix
    (fun q : Fin 2 × Fin 2 => ((q.1, k), (q.2, k)))
  change (selectedSchmidtEffect k
    (F - QuantumProver.ElegantJointMeasurement.Augmented.effectMatrix (QuantumProver.ElegantJointMeasurement.ResourceCode.codeContinuous β E))).PosSemidef at hdom
  rw [selectedSchmidtEffect_sub, selectedSchmidtEffect_code] at hdom
  exact hdom

theorem physical_four_effect_schmidt_cap {κ : Type*} [Fintype κ] [DecidableEq κ]
    {ι : Fin 4 → Type*} [∀ j, Fintype (ι j)]
    (β : κ → ℝ) (hβ : ∑ k, β k ^ 2 = 1) (k : κ)
    (A B : ∀ j, ι j → Matrix (Fin 2) κ ℂ) (u v w : Fin 4 → ℝ)
    (hsphere : ∀ j, u j ^ 2 + v j ^ 2 + w j ^ 2 = 1)
    (hcomplete : (∑ j, ∑ i, QuantumProver.ElegantJointMeasurement.Augmented.effectMatrix
      (QuantumProver.ElegantJointMeasurement.ResourceCode.productKet (A j i) (B j i))) =
        (1 : Matrix (QuantumProver.ElegantJointMeasurement.Augmented.Index κ) (QuantumProver.ElegantJointMeasurement.Augmented.Index κ) ℂ))
    (hcompression : ∀ j, (QuantumProver.ElegantJointMeasurement.ResourceCode.codeContinuous β).adjoint ∘L
      (QuantumProver.ElegantJointMeasurement.ClosureJoin.effectOperator (∑ i, QuantumProver.ElegantJointMeasurement.Augmented.effectMatrix
        (QuantumProver.ElegantJointMeasurement.ResourceCode.productKet (A j i) (B j i))) ∘L QuantumProver.ElegantJointMeasurement.ResourceCode.codeContinuous β) =
          rankOne ℂ (QuantumProver.ElegantJointMeasurement.ClosureJoin.directionKet (u j) (v j) (w j))
            (QuantumProver.ElegantJointMeasurement.ClosureJoin.directionKet (u j) (v j) (w j))) :
    β k ^ 2 ≤ (2 : ℝ) / 3 := by
  classical
  let F : Fin 4 → Matrix (QuantumProver.ElegantJointMeasurement.Augmented.Index κ) (QuantumProver.ElegantJointMeasurement.Augmented.Index κ) ℂ :=
    fun j => ∑ i, QuantumProver.ElegantJointMeasurement.Augmented.effectMatrix (QuantumProver.ElegantJointMeasurement.ResourceCode.productKet (A j i) (B j i))
  change (∑ j, F j) = 1 at hcomplete
  have hF (j : Fin 4) : (F j).PosSemidef := by
    apply Matrix.posSemidef_sum Finset.univ
    intro i _
    exact effectMatrix_posSemidef (QuantumProver.ElegantJointMeasurement.ResourceCode.productKet (A j i) (B j i))
  have hupper (j : Fin 4) : (1 - F j).PosSemidef := by
    have hpos := Matrix.posSemidef_sum (Finset.univ.erase j) (fun l _ => hF l)
    have heq : (∑ l ∈ Finset.univ.erase j, F l) = 1 - F j := by
      apply eq_sub_iff_add_eq.mpr
      rw [← hcomplete]
      exact Finset.sum_erase_add Finset.univ F (Finset.mem_univ j)
    rw [heq] at hpos
    exact hpos
  let a : ∀ j, ι j → Fin 2 → ℂ := fun j i q => A j i q k
  let b : ∀ j, ι j → Fin 2 → ℂ := fun j i q => B j i q k
  have hsel (j : Fin 4) : selectedSchmidtEffect k (F j) = separableEffect (a j) (b j) := by
    simp only [F, selectedSchmidtEffect_sum, selectedSchmidtEffect_product, separableEffect, a, b]
  have hcomplete' : (∑ j, separableEffect (a j) (b j)) = 1 := by
    calc
      _ = selectedSchmidtEffect k (∑ j, F j) := by rw [selectedSchmidtEffect_sum]; simp [hsel]
      _ = 1 := by rw [hcomplete, selectedSchmidtEffect_one]
  have hdom (j : Fin 4) : (separableEffect (a j) (b j) - ((β k ^ 2 : ℝ) : ℂ) •
      ketEffect (coefficientVector (ejmDirectionCoefficient (u j) (v j) (w j)))).PosSemidef := by
    have hnorm : ‖QuantumProver.ElegantJointMeasurement.ClosureJoin.directionKet (u j) (v j) (w j)‖ = 1 := by
      rw [QuantumProver.ElegantJointMeasurement.ClosureJoin.directionKet_eq_scaled_ejmKet]
      exact QuantumProver.ElegantJointMeasurement.ResourceCode.norm_ejmKet _ _ _
        (QuantumProver.ElegantJointMeasurement.ClosureJoin.scaled_direction_sphere _ _ _ (hsphere j))
    have h := selectedSchmidtEffect_domination β hβ k (F j) (hF j) (hupper j)
      (QuantumProver.ElegantJointMeasurement.ClosureJoin.directionKet (u j) (v j) (w j)) hnorm (hcompression j)
    rw [hsel] at h
    exact h
  exact separable_four_effect_cap a b u v w (β k ^ 2) hsphere hcomplete' hdom

end

end QuantumProver.ElegantJointMeasurement.Overlap

namespace QuantumProver.ElegantJointMeasurement.Operational

open scoped BigOperators ComplexConjugate
open InnerProductSpace
open QuantumProver.ElegantJointMeasurement.Concurrence QuantumProver.ElegantJointMeasurement.ProtocolEffects QuantumProver.ElegantJointMeasurement.Augmented

noncomputable section

set_option maxHeartbeats 600000

theorem schmidt_entropy_ge_one_of_cap_and_tail_cost
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (β : κ → ℝ) (hβ : ∑ k, β k ^ 2 = 1)
    (hcap : ∀ k, β k ^ 2 ≤ (2 : ℝ) / 3)
    (hcost : ∀ k, 0 < 1 - β k ^ 2 →
      |1 - 2 * β k ^ 2| ≤ 2 * (1 - β k ^ 2) * homogeneousBudget
        ((Real.sqrt (1 - β k ^ 2))⁻¹ • physicalReferenceInput (omittedCoefficient β k))) :
    1 ≤ QuantumProver.ElegantJointMeasurement.Entropy.entropyBits (fun k => β k ^ 2) := by
  classical
  by_cases hhalf : ∀ k, β k ^ 2 ≤ (1 : ℝ) / 2
  · exact QuantumProver.ElegantJointMeasurement.Entropy.entropyBits_ge_one_of_cap_half (fun k => β k ^ 2)
      (fun k => sq_nonneg (β k)) hhalf hβ
  · push Not at hhalf
    obtain ⟨k, hk⟩ := hhalf
    have ht : 0 < 1 - β k ^ 2 := by linarith [hcap k]
    have hnecessary := QuantumProver.ElegantJointMeasurement.TailReference.omitted_tail_quadratic_necessary β k
      (2 * (1 - β k ^ 2) * homogeneousBudget
        ((Real.sqrt (1 - β k ^ 2))⁻¹ • physicalReferenceInput (omittedCoefficient β k)))
      hβ ht (hcost k ht) le_rfl
    obtain ⟨hnonneg, hsum, _⟩ := QuantumProver.ElegantJointMeasurement.TailReference.normalized_omitted_weights β k hβ ht
    rw [QuantumProver.ElegantJointMeasurement.TailReference.squared_amplitude_entropy_eq_split β k hβ ht]
    exact QuantumProver.ElegantJointMeasurement.Entropy.entropyBits_ge_one_of_tail_necessary (β k ^ 2)
      (QuantumProver.ElegantJointMeasurement.TailReference.normalizedWeight (omittedCoefficient β k)) hk.le (hcap k)
      hnonneg hsum hnecessary

theorem schmidt_entropy_ge_one_of_tree_effect_limit_and_cap
    {κ : Type*} [Fintype κ] [DecidableEq κ] {m n : ℕ}
    {η : Type*} {l : Filter η} [l.NeBot]
    (β : κ → ℝ) (hβ : ∑ k, β k ^ 2 = 1)
    (hcap : ∀ k, β k ^ 2 ≤ (2 : ℝ) / 3)
    (u v w : Fin 4 → ℝ) (hsphere : ∀ j, u j ^ 2 + v j ^ 2 + w j ^ 2 = 1)
    (T : η → FiniteLocalKrausTree m n)
    (ea : Fin 2 × κ ≃ Fin m) (eb : Fin 2 × κ ≃ Fin n)
    (report : (a : η) → Fin (T a).terminalBraPairs.length → Fin 4)
    (F : Fin 4 → Matrix (Index κ) (Index κ) ℂ)
    (hlim : Filter.Tendsto (fun a j => groupedEffect (T a) ea eb (report a) j) l (nhds F))
    (hcompression : ∀ j, (QuantumProver.ElegantJointMeasurement.ResourceCode.codeContinuous β).adjoint ∘L
      (QuantumProver.ElegantJointMeasurement.ClosureJoin.effectOperator (F j) ∘L QuantumProver.ElegantJointMeasurement.ResourceCode.codeContinuous β) =
        rankOne ℂ (QuantumProver.ElegantJointMeasurement.ClosureJoin.directionKet (u j) (v j) (w j))
          (QuantumProver.ElegantJointMeasurement.ClosureJoin.directionKet (u j) (v j) (w j))) :
    1 ≤ QuantumProver.ElegantJointMeasurement.Entropy.entropyBits (fun k => β k ^ 2) := by
  apply schmidt_entropy_ge_one_of_cap_and_tail_cost β hβ hcap
  intro k ht
  exact unit_direction_ejm_necessary_of_tree_effect_limit β hβ k (β k ^ 2) rfl
    u v w hsphere (1 - β k ^ 2) ht T ea eb report F hlim hcompression

theorem schmidt_cap_of_finite_tree
    {κ : Type*} [Fintype κ] [DecidableEq κ] {m n : ℕ}
    (β : κ → ℝ) (hβ : ∑ k, β k ^ 2 = 1) (k : κ)
    (u v w : Fin 4 → ℝ) (hsphere : ∀ j, u j ^ 2 + v j ^ 2 + w j ^ 2 = 1)
    (T : FiniteLocalKrausTree m n)
    (ea : Fin 2 × κ ≃ Fin m) (eb : Fin 2 × κ ≃ Fin n)
    (report : Fin T.terminalBraPairs.length → Fin 4)
    (hcompression : ∀ j, (QuantumProver.ElegantJointMeasurement.ResourceCode.codeContinuous β).adjoint ∘L
      (QuantumProver.ElegantJointMeasurement.ClosureJoin.effectOperator (groupedEffect T ea eb report j) ∘L
        QuantumProver.ElegantJointMeasurement.ResourceCode.codeContinuous β) =
        rankOne ℂ (QuantumProver.ElegantJointMeasurement.ClosureJoin.directionKet (u j) (v j) (w j))
          (QuantumProver.ElegantJointMeasurement.ClosureJoin.directionKet (u j) (v j) (w j))) :
    β k ^ 2 ≤ (2 : ℝ) / 3 := by
  classical
  let A (j : Fin 4) (i : Fin T.terminalBraPairs.length) : Matrix (Fin 2) κ ℂ :=
    localMatrix (reportedPair T ea eb report j i).1
  let B (j : Fin 4) (i : Fin T.terminalBraPairs.length) : Matrix (Fin 2) κ ℂ :=
    localMatrix (reportedPair T ea eb report j i).2
  have hraw (j : Fin 4) : (∑ i, effectMatrix (QuantumProver.ElegantJointMeasurement.ResourceCode.productKet (A j i) (B j i))) =
      groupedEffect T ea eb report j := by
    have h := congrArg Prod.fst (groupedRecord_eq_raw_sum T ea eb β k report j)
    simpa only [Prod.fst_sum, augmentedMap, product, groupedRecord, A, B] using h
  apply QuantumProver.ElegantJointMeasurement.Overlap.physical_four_effect_schmidt_cap β hβ k A B u v w hsphere
  · simp_rw [hraw]
    exact groupedEffect_sum T ea eb report
  · intro j
    rw [hraw]
    exact hcompression j

theorem resource_entropy_ge_one_of_finite_tree
    {κ : Type*} [Fintype κ] [DecidableEq κ] {m n : ℕ}
    (β : κ → ℝ) (hβ : ∑ k, β k ^ 2 = 1)
    (u v w : Fin 4 → ℝ) (hsphere : ∀ j, u j ^ 2 + v j ^ 2 + w j ^ 2 = 1)
    (T : FiniteLocalKrausTree m n)
    (ea : Fin 2 × κ ≃ Fin m) (eb : Fin 2 × κ ≃ Fin n)
    (report : Fin T.terminalBraPairs.length → Fin 4)
    (hcompression : ∀ j, (QuantumProver.ElegantJointMeasurement.ResourceCode.codeContinuous β).adjoint ∘L
      (QuantumProver.ElegantJointMeasurement.ClosureJoin.effectOperator (groupedEffect T ea eb report j) ∘L
        QuantumProver.ElegantJointMeasurement.ResourceCode.codeContinuous β) =
        rankOne ℂ (QuantumProver.ElegantJointMeasurement.ClosureJoin.directionKet (u j) (v j) (w j))
          (QuantumProver.ElegantJointMeasurement.ClosureJoin.directionKet (u j) (v j) (w j))) :
    1 ≤ QuantumProver.ElegantJointMeasurement.TailReference.vonNeumannEntropyBits
      (QuantumProver.ElegantJointMeasurement.TailReference.resourceCoefficient β * (QuantumProver.ElegantJointMeasurement.TailReference.resourceCoefficient β).conjTranspose) := by
  rw [QuantumProver.ElegantJointMeasurement.TailReference.resource_left_vonNeumannEntropy_eq_entropyBits]
  apply schmidt_entropy_ge_one_of_tree_effect_limit_and_cap
    (l := (pure () : Filter Unit)) β hβ
    (fun k => schmidt_cap_of_finite_tree β hβ k u v w hsphere T ea eb report hcompression)
    u v w hsphere (fun _ : Unit => T) ea eb (fun _ => report)
    (fun j => groupedEffect T ea eb report j) tendsto_const_nhds hcompression

theorem schmidt_cap_of_tree_effect_limit
    {κ : Type*} [Fintype κ] [DecidableEq κ] {m n : ℕ}
    {η : Type*} {l : Filter η} [l.NeBot]
    (β : κ → ℝ) (hβ : ∑ k, β k ^ 2 = 1) (k : κ)
    (u v w : Fin 4 → ℝ) (hsphere : ∀ j, u j ^ 2 + v j ^ 2 + w j ^ 2 = 1)
    (T : η → FiniteLocalKrausTree m n)
    (ea : Fin 2 × κ ≃ Fin m) (eb : Fin 2 × κ ≃ Fin n)
    (report : (a : η) → Fin (T a).terminalBraPairs.length → Fin 4)
    (F : Fin 4 → Matrix (Index κ) (Index κ) ℂ)
    (hlim : Filter.Tendsto (fun a j => groupedEffect (T a) ea eb (report a) j) l (nhds F))
    (hcompression : ∀ j, (QuantumProver.ElegantJointMeasurement.ResourceCode.codeContinuous β).adjoint ∘L
      (QuantumProver.ElegantJointMeasurement.ClosureJoin.effectOperator (F j) ∘L QuantumProver.ElegantJointMeasurement.ResourceCode.codeContinuous β) =
        rankOne ℂ (QuantumProver.ElegantJointMeasurement.ClosureJoin.directionKet (u j) (v j) (w j))
          (QuantumProver.ElegantJointMeasurement.ClosureJoin.directionKet (u j) (v j) (w j))) :
    β k ^ 2 ≤ (2 : ℝ) / 3 := by
  classical
  obtain ⟨r, A, B, hraw, hcomplete⟩ :=
    QuantumProver.ElegantJointMeasurement.ProtocolEffectLimits.tree_effect_limit_raw_realization k T ea eb report F hlim
  apply QuantumProver.ElegantJointMeasurement.Overlap.physical_four_effect_schmidt_cap β hβ k A B u v w hsphere hcomplete
  intro j
  rw [hraw]
  exact hcompression j

theorem resource_entropy_ge_one_of_tree_effect_limit
    {κ : Type*} [Fintype κ] [DecidableEq κ] {m n : ℕ}
    {η : Type*} {l : Filter η} [l.NeBot]
    (β : κ → ℝ) (hβ : ∑ k, β k ^ 2 = 1)
    (u v w : Fin 4 → ℝ) (hsphere : ∀ j, u j ^ 2 + v j ^ 2 + w j ^ 2 = 1)
    (T : η → FiniteLocalKrausTree m n)
    (ea : Fin 2 × κ ≃ Fin m) (eb : Fin 2 × κ ≃ Fin n)
    (report : (a : η) → Fin (T a).terminalBraPairs.length → Fin 4)
    (F : Fin 4 → Matrix (Index κ) (Index κ) ℂ)
    (hlim : Filter.Tendsto (fun a j => groupedEffect (T a) ea eb (report a) j) l (nhds F))
    (hcompression : ∀ j, (QuantumProver.ElegantJointMeasurement.ResourceCode.codeContinuous β).adjoint ∘L
      (QuantumProver.ElegantJointMeasurement.ClosureJoin.effectOperator (F j) ∘L QuantumProver.ElegantJointMeasurement.ResourceCode.codeContinuous β) =
        rankOne ℂ (QuantumProver.ElegantJointMeasurement.ClosureJoin.directionKet (u j) (v j) (w j))
          (QuantumProver.ElegantJointMeasurement.ClosureJoin.directionKet (u j) (v j) (w j))) :
    1 ≤ QuantumProver.ElegantJointMeasurement.TailReference.vonNeumannEntropyBits
      (QuantumProver.ElegantJointMeasurement.TailReference.resourceCoefficient β * (QuantumProver.ElegantJointMeasurement.TailReference.resourceCoefficient β).conjTranspose) := by
  rw [QuantumProver.ElegantJointMeasurement.TailReference.resource_left_vonNeumannEntropy_eq_entropyBits]
  apply schmidt_entropy_ge_one_of_tree_effect_limit_and_cap β hβ
    (fun k => schmidt_cap_of_tree_effect_limit β hβ k u v w hsphere T ea eb report F hlim hcompression)
    u v w hsphere T ea eb report F hlim hcompression

theorem one_ebit_finite_locc_upper_bound : QuantumProver.ElegantJointMeasurement.Teleportation.OneEbitFiniteProtocolCertificate :=
  QuantumProver.ElegantJointMeasurement.Teleportation.one_ebit_finite_locc_protocol_certificate

end

end QuantumProver.ElegantJointMeasurement.Operational

namespace QuantumProver.ElegantJointMeasurement.GeneralResource

open scoped BigOperators ComplexConjugate Matrix
open InnerProductSpace QuantumProver.ElegantJointMeasurement.ResourceCode

noncomputable section

set_option maxHeartbeats 600000

variable {a b κ : Type*} [Fintype a] [Fintype b] [Fintype κ] [DecidableEq κ]

def codeLinear (Ψ : Matrix κ κ ℂ) : InputSpace a b →ₗ[ℂ] ExtendedSpace a b κ where
  toFun E := WithLp.toLp 2 (fun z => Ψ z.1.2 z.2.2 * E (z.1.1, z.2.1))
  map_add' E F := by
    ext z
    simp [mul_add]
  map_smul' c E := by
    ext z
    simp [mul_left_comm]

@[simp] theorem codeLinear_apply (Ψ : Matrix κ κ ℂ) (E : InputSpace a b)
    (i : a) (j : b) (k l : κ) :
    codeLinear Ψ E ((i, k), (j, l)) = Ψ k l * E (i, j) := rfl

def codeContinuous (Ψ : Matrix κ κ ℂ) : InputSpace a b →L[ℂ] ExtendedSpace a b κ :=
  (codeLinear Ψ).toContinuousLinearMap

@[simp] theorem codeContinuous_apply (Ψ : Matrix κ κ ℂ) (E : InputSpace a b) :
    codeContinuous Ψ E = codeLinear Ψ E := rfl

theorem resource_mass (Ψ : Matrix κ κ ℂ) :
    (Matrix.trace (Ψ * Ψᴴ)).re = QuantumProver.ElegantJointMeasurement.Concurrence.hsNormSq Ψ := by
  exact (QuantumProver.ElegantJointMeasurement.Concurrence.probability_gram_swap Ψ).trans
    (QuantumProver.ElegantJointMeasurement.Concurrence.probability_gram_eq_hsNormSq Ψ)

theorem code_norm_sq (Ψ : Matrix κ κ ℂ) (E : InputSpace a b) :
    ‖codeLinear Ψ E‖ ^ 2 = QuantumProver.ElegantJointMeasurement.Concurrence.hsNormSq Ψ * ‖E‖ ^ 2 := by
  calc
    ‖codeLinear Ψ E‖ ^ 2 =
        ∑ i : a, ∑ k : κ, ∑ j : b, ∑ l : κ,
          ‖Ψ k l‖ ^ 2 * ‖E (i, j)‖ ^ 2 := by
      simp [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type, norm_mul, mul_pow]
    _ = ∑ i : a, ∑ j : b, ∑ k : κ, ∑ l : κ,
          ‖Ψ k l‖ ^ 2 * ‖E (i, j)‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_comm]
    _ = ∑ i : a, ∑ j : b, QuantumProver.ElegantJointMeasurement.Concurrence.hsNormSq Ψ * ‖E (i, j)‖ ^ 2 := by
      simp only [QuantumProver.ElegantJointMeasurement.Concurrence.hsNormSq, Complex.normSq_eq_norm_sq, Finset.sum_mul]
    _ = QuantumProver.ElegantJointMeasurement.Concurrence.hsNormSq Ψ * ‖E‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
      simp only [Finset.mul_sum]

theorem code_norm (Ψ : Matrix κ κ ℂ) (hΨ : Matrix.trace (Ψ * Ψᴴ) = 1)
    (E : InputSpace a b) : ‖codeContinuous Ψ E‖ = ‖E‖ := by
  have hm : QuantumProver.ElegantJointMeasurement.Concurrence.hsNormSq Ψ = 1 := by rw [← resource_mass, hΨ]; rfl
  have h := code_norm_sq Ψ E
  rw [hm, one_mul] at h
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h

def contraction (Ψ : Matrix κ κ ℂ) (z : ExtendedSpace a b κ) : InputSpace a b :=
  WithLp.toLp 2 (fun ij => ∑ k, ∑ l, conj (Ψ k l) * z ((ij.1, k), (ij.2, l)))

@[simp] theorem contraction_apply (Ψ : Matrix κ κ ℂ) (z : ExtendedSpace a b κ)
    (i : a) (j : b) :
    contraction Ψ z (i, j) = ∑ k, ∑ l, conj (Ψ k l) * z ((i, k), (j, l)) := rfl

theorem code_inner_contraction (Ψ : Matrix κ κ ℂ) (E : InputSpace a b)
    (z : ExtendedSpace a b κ) :
    inner ℂ (codeContinuous Ψ E) z = inner ℂ E (contraction Ψ z) := by
  calc
    inner ℂ (codeContinuous Ψ E) z =
        ∑ i : a, ∑ k : κ, ∑ j : b, ∑ l : κ,
          conj (Ψ k l) * conj (E (i, j)) * z ((i, k), (j, l)) := by
      simp [PiLp.inner_apply, Fintype.sum_prod_type, mul_assoc, mul_left_comm, mul_comm]
    _ = ∑ i : a, ∑ j : b, ∑ k : κ, ∑ l : κ,
          conj (E (i, j)) * (conj (Ψ k l) * z ((i, k), (j, l))) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro k hk
      apply Finset.sum_congr rfl
      intro l hl
      ring
    _ = inner ℂ E (contraction Ψ z) := by
      simp [PiLp.inner_apply, Fintype.sum_prod_type, Finset.sum_mul, Finset.mul_sum,
        mul_assoc, mul_left_comm, mul_comm]

theorem code_adjoint_apply (Ψ : Matrix κ κ ℂ) (z : ExtendedSpace a b κ) :
    (codeContinuous Ψ).adjoint z = contraction Ψ z := by
  apply ext_inner_left ℂ
  intro E
  rw [ContinuousLinearMap.adjoint_inner_right]
  exact code_inner_contraction Ψ E z

theorem codeContinuous_diagonal (β : κ → ℝ) :
    (codeContinuous (a := a) (b := b) (QuantumProver.ElegantJointMeasurement.TailReference.resourceCoefficient β)) =
      QuantumProver.ElegantJointMeasurement.ResourceCode.codeContinuous β := by
  ext E z
  simp only [codeContinuous_apply, QuantumProver.ElegantJointMeasurement.ResourceCode.codeContinuous_apply]
  change QuantumProver.ElegantJointMeasurement.TailReference.resourceCoefficient β z.1.2 z.2.2 * E (z.1.1, z.2.1) = _
  simp [QuantumProver.ElegantJointMeasurement.TailReference.resourceCoefficient, Matrix.diagonal_apply, QuantumProver.ElegantJointMeasurement.ResourceCode.codeLinear]

def codeMatrix (Ψ : Matrix κ κ ℂ) : Matrix ((a × κ) × (b × κ)) (a × b) ℂ := by
  classical
  exact fun z q => if q = (z.1.1, z.2.1) then Ψ z.1.2 z.2.2 else 0

theorem codeMatrix_mulVec (Ψ : Matrix κ κ ℂ) (E : a × b → ℂ) :
    codeMatrix Ψ *ᵥ E = fun z => Ψ z.1.2 z.2.2 * E (z.1.1, z.2.1) := by
  classical
  ext z
  simp [codeMatrix, Matrix.mulVec, dotProduct, ite_mul]

theorem codeLinear_eq_toEuclideanLin [DecidableEq a] [DecidableEq b]
    (Ψ : Matrix κ κ ℂ) :
    codeLinear (a := a) (b := b) Ψ = Matrix.toEuclideanLin (codeMatrix Ψ) := by
  ext E z
  change Ψ z.1.2 z.2.2 * E (z.1.1, z.2.1) = (codeMatrix Ψ *ᵥ E.ofLp) z
  exact (congrFun (codeMatrix_mulVec Ψ E.ofLp) z).symm

theorem codeContinuous_eq_matrix [DecidableEq a] [DecidableEq b]
    (Ψ : Matrix κ κ ℂ) :
    codeContinuous (a := a) (b := b) Ψ =
      (Matrix.toEuclideanLin (codeMatrix Ψ)).toContinuousLinearMap := by
  unfold codeContinuous
  rw [codeLinear_eq_toEuclideanLin]

theorem encoded_density_apply (Ψ : Matrix κ κ ℂ) (ρ : Matrix (a × b) (a × b) ℂ)
    (z h : (a × κ) × (b × κ)) :
    (codeMatrix (a := a) (b := b) Ψ * ρ * (codeMatrix (a := a) (b := b) Ψ)ᴴ) z h =
      Ψ z.1.2 z.2.2 * conj (Ψ h.1.2 h.2.2) *
        ρ (z.1.1, z.2.1) (h.1.1, h.2.1) := by
  classical
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply, codeMatrix, mul_ite, ite_mul, apply_ite,
    mul_assoc, mul_left_comm, mul_comm]

theorem code_compression_matrix [DecidableEq a] [DecidableEq b]
    (Ψ : Matrix κ κ ℂ)
    (F : Matrix ((a × κ) × (b × κ)) ((a × κ) × (b × κ)) ℂ) :
    (codeContinuous Ψ).adjoint ∘L
      ((Matrix.toEuclideanLin F).toContinuousLinearMap ∘L codeContinuous Ψ) =
        (Matrix.toEuclideanLin ((codeMatrix (a := a) (b := b) Ψ)ᴴ * F *
          codeMatrix (a := a) (b := b) Ψ)).toContinuousLinearMap := by
  rw [codeContinuous_eq_matrix, ← LinearMap.adjoint_toContinuousLinearMap,
    ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
  ext E z
  change ((codeMatrix (a := a) (b := b) Ψ)ᴴ *ᵥ
    (F *ᵥ (codeMatrix (a := a) (b := b) Ψ *ᵥ E.ofLp))) z =
      (((codeMatrix (a := a) (b := b) Ψ)ᴴ * F *
        codeMatrix (a := a) (b := b) Ψ) *ᵥ E.ofLp) z
  simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]

theorem codeMatrix_localUnitary (U V : unitary (Matrix κ κ ℂ)) (Ψ : Matrix κ κ ℂ) :
    codeMatrix (a := Fin 2) (b := Fin 2) (QuantumProver.ElegantJointMeasurement.TailReference.localUnitaryCoefficient U V Ψ) =
      QuantumProver.ElegantJointMeasurement.TailReference.globalResourceUnitary U V * codeMatrix (a := Fin 2) (b := Fin 2) Ψ := by
  classical
  ext z q
  simp [codeMatrix, QuantumProver.ElegantJointMeasurement.TailReference.localUnitaryCoefficient,
    QuantumProver.ElegantJointMeasurement.TailReference.globalResourceUnitary, QuantumProver.ElegantJointMeasurement.TailReference.localPartyUnitary,
    Matrix.kronecker_apply, Matrix.one_apply, Matrix.mul_apply, Matrix.transpose_apply,
    Fintype.sum_prod_type, mul_ite, ite_mul, Finset.sum_mul, Finset.mul_sum,
    mul_assoc, mul_left_comm, mul_comm]
  split_ifs
  · rw [Finset.sum_comm]
  · rfl

theorem arbitrary_resource_entropy_ge_one_of_tree_effect_limit
    {m n : ℕ} {η : Type*} {l : Filter η} [l.NeBot]
    (Ψ : Matrix κ κ ℂ) (hΨ : Matrix.trace (Ψ * Ψᴴ) = 1)
    (u v w : Fin 4 → ℝ) (hsphere : ∀ j, u j ^ 2 + v j ^ 2 + w j ^ 2 = 1)
    (T : η → QuantumProver.ElegantJointMeasurement.Concurrence.FiniteLocalKrausTree m n)
    (ea : Fin 2 × κ ≃ Fin m) (eb : Fin 2 × κ ≃ Fin n)
    (report : (a : η) → Fin (T a).terminalBraPairs.length → Fin 4)
    (F : Fin 4 → Matrix (QuantumProver.ElegantJointMeasurement.Augmented.Index κ) (QuantumProver.ElegantJointMeasurement.Augmented.Index κ) ℂ)
    (hlim : Filter.Tendsto (fun a j => QuantumProver.ElegantJointMeasurement.ProtocolEffects.groupedEffect (T a) ea eb
      (report a) j) l (nhds F))
    (hcompression : ∀ j, (codeContinuous (a := Fin 2) (b := Fin 2) Ψ).adjoint ∘L
      (QuantumProver.ElegantJointMeasurement.ClosureJoin.effectOperator (F j) ∘L codeContinuous Ψ) =
        rankOne ℂ (QuantumProver.ElegantJointMeasurement.ClosureJoin.directionKet (u j) (v j) (w j))
          (QuantumProver.ElegantJointMeasurement.ClosureJoin.directionKet (u j) (v j) (w j))) :
    1 ≤ QuantumProver.ElegantJointMeasurement.TailReference.vonNeumannEntropyBits (Ψ * Ψᴴ) := by
  classical
  obtain ⟨β, U, V, _, hβ, hdecomp⟩ := QuantumProver.ElegantJointMeasurement.SchmidtResource.exists_squareSchmidtRepresentation Ψ hΨ
  have hΨUV : Ψ = QuantumProver.ElegantJointMeasurement.TailReference.localUnitaryCoefficient U V
      (QuantumProver.ElegantJointMeasurement.TailReference.resourceCoefficient β) := by
    rw [QuantumProver.ElegantJointMeasurement.TailReference.localUnitaryCoefficient,
      QuantumProver.ElegantJointMeasurement.TailReference.resourceCoefficient_eq_diagonal]
    exact hdecomp
  let P := QuantumProver.ElegantJointMeasurement.TailReference.globalResourceUnitary U V
  let Jβ := codeMatrix (a := Fin 2) (b := Fin 2) (QuantumProver.ElegantJointMeasurement.TailReference.resourceCoefficient β)
  let JΨ := codeMatrix (a := Fin 2) (b := Fin 2) Ψ
  have hJ : JΨ = P * Jβ := by
    dsimp [JΨ, P, Jβ]
    rw [hΨUV, codeMatrix_localUnitary]
  have hcompression' (j : Fin 4) : (QuantumProver.ElegantJointMeasurement.ResourceCode.codeContinuous β).adjoint ∘L
      (QuantumProver.ElegantJointMeasurement.ClosureJoin.effectOperator (Pᴴ * F j * P) ∘L QuantumProver.ElegantJointMeasurement.ResourceCode.codeContinuous β) =
        rankOne ℂ (QuantumProver.ElegantJointMeasurement.ClosureJoin.directionKet (u j) (v j) (w j))
          (QuantumProver.ElegantJointMeasurement.ClosureJoin.directionKet (u j) (v j) (w j)) := by
    have hc := hcompression j
    change (codeContinuous Ψ).adjoint ∘L
      ((Matrix.toEuclideanLin (F j)).toContinuousLinearMap ∘L codeContinuous Ψ) = _ at hc
    rw [code_compression_matrix] at hc
    change (Matrix.toEuclideanLin (JΨᴴ * F j * JΨ)).toContinuousLinearMap = _ at hc
    rw [← codeContinuous_diagonal β]
    change (codeContinuous (QuantumProver.ElegantJointMeasurement.TailReference.resourceCoefficient β)).adjoint ∘L
      ((Matrix.toEuclideanLin (Pᴴ * F j * P)).toContinuousLinearMap ∘L
        codeContinuous (QuantumProver.ElegantJointMeasurement.TailReference.resourceCoefficient β)) = _
    rw [code_compression_matrix]
    change (Matrix.toEuclideanLin (Jβᴴ * (Pᴴ * F j * P) * Jβ)).toContinuousLinearMap = _
    have heq : Jβᴴ * (Pᴴ * F j * P) * Jβ = JΨᴴ * F j * JΨ := by
      rw [hJ, Matrix.conjTranspose_mul]
      simp only [Matrix.mul_assoc]
    rw [heq]
    exact hc
  have hlow := QuantumProver.ElegantJointMeasurement.Operational.resource_entropy_ge_one_of_tree_effect_limit β hβ
    u v w hsphere
    (fun a => QuantumProver.ElegantJointMeasurement.TailReference.prependResourceUnitaries U V ea eb (T a)) ea eb
    (fun a => QuantumProver.ElegantJointMeasurement.TailReference.prependReport U V ea eb (T a) (report a))
    (fun j => Pᴴ * F j * P)
    (QuantumProver.ElegantJointMeasurement.TailReference.groupedEffect_limit_prependResourceUnitaries U V ea eb T report F hlim)
    hcompression'
  rw [QuantumProver.ElegantJointMeasurement.TailReference.resource_left_vonNeumannEntropy_eq_entropyBits] at hlow
  rw [hΨUV, QuantumProver.ElegantJointMeasurement.TailReference.localUnitary_resource_entropy]
  exact hlow

end

end QuantumProver.ElegantJointMeasurement.GeneralResource

namespace QuantumProver.ElegantJointMeasurement.FiniteTreeCostModel

open scoped BigOperators ComplexConjugate ComplexOrder Matrix Topology
open QuantumProver.ElegantJointMeasurement.GeneralResource

noncomputable section

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

theorem entropy_ge_one_of_density_channel_effect_closure
    {m n : ℕ} (Ψ : Matrix κ κ ℂ) (hΨ : Matrix.trace (Ψ * Ψᴴ) = 1)
    (ea : (Fin 2 × κ) ≃ Fin m) (eb : (Fin 2 × κ) ≃ Fin n)
    (F : Fin 4 → Matrix (QuantumProver.ElegantJointMeasurement.Augmented.Index κ) (QuantumProver.ElegantJointMeasurement.Augmented.Index κ) ℂ)
    (hF : F ∈ closure (QuantumProver.ElegantJointMeasurement.TailReference.finiteTreeEffectSet ea eb))
    (hChannel : ∀ ρ : Matrix QuantumProver.ElegantJointMeasurement.Teleportation.SystemIndex QuantumProver.ElegantJointMeasurement.Teleportation.SystemIndex ℂ,
      ρ.PosSemidef → Matrix.trace ρ = 1 →
      QuantumProver.ElegantJointMeasurement.Teleportation.Tomography.resourceMeasurementChannel
        (codeMatrix Ψ) F ρ = QuantumProver.ElegantJointMeasurement.Teleportation.physicalClassicalChannel ρ) :
    1 ≤ QuantumProver.ElegantJointMeasurement.TailReference.vonNeumannEntropyBits (Ψ * Ψᴴ) := by
  obtain ⟨T, report, hlim⟩ := QuantumProver.ElegantJointMeasurement.TailReference.finiteTreeEffectSet_closure_sequence ea eb F hF
  have hc := QuantumProver.ElegantJointMeasurement.Teleportation.Tomography.ejm_density_exactness_implies_compressed_effects
    (codeMatrix Ψ) F hChannel
  apply arbitrary_resource_entropy_ge_one_of_tree_effect_limit Ψ hΨ
    (fun j => QuantumProver.ElegantJointMeasurement.Teleportation.PhysicalUpper.unitDirection j 0)
    (fun j => QuantumProver.ElegantJointMeasurement.Teleportation.PhysicalUpper.unitDirection j 1)
    (fun j => QuantumProver.ElegantJointMeasurement.Teleportation.PhysicalUpper.unitDirection j 2)
    QuantumProver.ElegantJointMeasurement.Teleportation.PhysicalUpper.unitDirection_sphere T ea eb report F hlim
  intro j
  change (codeContinuous Ψ).adjoint ∘L
    ((Matrix.toEuclideanLin (F j)).toContinuousLinearMap ∘L codeContinuous Ψ) = _
  rw [code_compression_matrix, hc j, QuantumProver.ElegantJointMeasurement.Teleportation.PhysicalUpper.physicalEffect_operator]

theorem entropy_ge_one_of_density_channel_limit
    {m n : ℕ} (Ψ : Matrix κ κ ℂ) (hΨ : Matrix.trace (Ψ * Ψᴴ) = 1)
    (T : ℕ → QuantumProver.ElegantJointMeasurement.Concurrence.FiniteLocalKrausTree m n)
    (ea : (Fin 2 × κ) ≃ Fin m) (eb : (Fin 2 × κ) ≃ Fin n)
    (report : (a : ℕ) → Fin (T a).terminalBraPairs.length → Fin 4)
    (hChannel : ∀ ρ : Matrix QuantumProver.ElegantJointMeasurement.Teleportation.SystemIndex QuantumProver.ElegantJointMeasurement.Teleportation.SystemIndex ℂ,
      ρ.PosSemidef → Matrix.trace ρ = 1 →
      Filter.Tendsto (fun a => QuantumProver.ElegantJointMeasurement.Teleportation.Tomography.resourceMeasurementChannel
        (codeMatrix Ψ) (fun j => QuantumProver.ElegantJointMeasurement.ProtocolEffects.groupedEffect (T a) ea eb (report a) j) ρ)
        Filter.atTop (nhds (QuantumProver.ElegantJointMeasurement.Teleportation.physicalClassicalChannel ρ))) :
    1 ≤ QuantumProver.ElegantJointMeasurement.TailReference.vonNeumannEntropyBits (Ψ * Ψᴴ) := by
  classical
  have hne : Nonempty κ := by
    by_contra h
    haveI : IsEmpty κ := not_nonempty_iff.mp h
    simpa [Matrix.trace] using hΨ
  have hc := QuantumProver.ElegantJointMeasurement.Teleportation.Tomography.ejm_density_channel_tendsto_implies_compressed_effects
    Filter.atTop (codeMatrix Ψ)
    (fun a j => QuantumProver.ElegantJointMeasurement.ProtocolEffects.groupedEffect (T a) ea eb (report a) j) hChannel
  obtain ⟨F, φ, _, hlim, hcomp, _, _⟩ :=
    QuantumProver.ElegantJointMeasurement.CompactProtocolEffects.tree_effect_subsequence_of_compressed_limit
      (Classical.choice hne) T ea eb report (codeMatrix Ψ) QuantumProver.ElegantJointMeasurement.Teleportation.represented_physicalEffect hc
  apply arbitrary_resource_entropy_ge_one_of_tree_effect_limit Ψ hΨ
    (fun j => QuantumProver.ElegantJointMeasurement.Teleportation.PhysicalUpper.unitDirection j 0)
    (fun j => QuantumProver.ElegantJointMeasurement.Teleportation.PhysicalUpper.unitDirection j 1)
    (fun j => QuantumProver.ElegantJointMeasurement.Teleportation.PhysicalUpper.unitDirection j 2)
    QuantumProver.ElegantJointMeasurement.Teleportation.PhysicalUpper.unitDirection_sphere
    (fun a => T (φ a)) ea eb (fun a => report (φ a)) F hlim
  intro j
  change (codeContinuous Ψ).adjoint ∘L
    ((Matrix.toEuclideanLin (F j)).toContinuousLinearMap ∘L codeContinuous Ψ) = _
  rw [code_compression_matrix, hcomp j, QuantumProver.ElegantJointMeasurement.Teleportation.PhysicalUpper.physicalEffect_operator]

def ImplementsInFiniteTreeClosure (Ψ : Matrix κ κ ℂ) : Prop :=
  ∃ (m n : ℕ) (ea : (Fin 2 × κ) ≃ Fin m) (eb : (Fin 2 × κ) ≃ Fin n)
    (F : Fin 4 → Matrix (QuantumProver.ElegantJointMeasurement.Augmented.Index κ) (QuantumProver.ElegantJointMeasurement.Augmented.Index κ) ℂ),
    F ∈ closure (QuantumProver.ElegantJointMeasurement.TailReference.finiteTreeEffectSet ea eb) ∧
    ∀ ρ : Matrix QuantumProver.ElegantJointMeasurement.Teleportation.SystemIndex QuantumProver.ElegantJointMeasurement.Teleportation.SystemIndex ℂ,
      ρ.PosSemidef → Matrix.trace ρ = 1 →
      QuantumProver.ElegantJointMeasurement.Teleportation.Tomography.resourceMeasurementChannel (codeMatrix Ψ) F ρ =
        QuantumProver.ElegantJointMeasurement.Teleportation.physicalClassicalChannel ρ

theorem implementation_entropy_ge_one (Ψ : Matrix κ κ ℂ)
    (hΨ : Matrix.trace (Ψ * Ψᴴ) = 1) (h : ImplementsInFiniteTreeClosure Ψ) :
    1 ≤ QuantumProver.ElegantJointMeasurement.TailReference.vonNeumannEntropyBits (Ψ * Ψᴴ) := by
  obtain ⟨m, n, ea, eb, F, hF, hChannel⟩ := h
  exact entropy_ge_one_of_density_channel_effect_closure Ψ hΨ ea eb F hF hChannel

def finiteTreeClosureCostSet : Set ℝ :=
  {c | ∃ (r : ℕ) (_hr : 0 < r) (Ψ : Matrix (Fin r) (Fin r) ℂ),
    Matrix.trace (Ψ * Ψᴴ) = 1 ∧ ImplementsInFiniteTreeClosure Ψ ∧
      QuantumProver.ElegantJointMeasurement.TailReference.vonNeumannEntropyBits (Ψ * Ψᴴ) = c}

theorem finiteTreeClosureCostSet_lower {c : ℝ} (hc : c ∈ finiteTreeClosureCostSet) :
    1 ≤ c := by
  obtain ⟨r, _, Ψ, hΨ, h, he⟩ := hc
  rw [← he]
  exact implementation_entropy_ge_one Ψ hΨ h

theorem one_ebit_implements_in_finite_tree_closure :
    ImplementsInFiniteTreeClosure QuantumProver.ElegantJointMeasurement.Teleportation.resource := by
  let C := QuantumProver.ElegantJointMeasurement.Teleportation.PhysicalUpper.one_ebit_physical_upper_certificate
  have hJ : codeMatrix QuantumProver.ElegantJointMeasurement.Teleportation.resource =
      QuantumProver.ElegantJointMeasurement.Teleportation.PhysicalUpper.physicalEmbedding := by
    apply Matrix.toEuclideanLin.injective
    have hC : (Matrix.toEuclideanLin (codeMatrix QuantumProver.ElegantJointMeasurement.Teleportation.resource)).toContinuousLinearMap =
        (Matrix.toEuclideanLin QuantumProver.ElegantJointMeasurement.Teleportation.PhysicalUpper.physicalEmbedding).toContinuousLinearMap := by
      rw [← codeContinuous_eq_matrix, ← C.physical_resource, codeContinuous_diagonal]
      exact C.physical_resource_code
    exact congrArg ContinuousLinearMap.toLinearMap hC
  refine ⟨4, 4, QuantumProver.ElegantJointMeasurement.Teleportation.PhysicalUpper.alicePhysicalEquiv,
    QuantumProver.ElegantJointMeasurement.Teleportation.PhysicalUpper.bobPhysicalEquiv,
    (fun j => QuantumProver.ElegantJointMeasurement.ProtocolEffects.groupedEffect QuantumProver.ElegantJointMeasurement.Teleportation.oneEbitFiniteTree
      QuantumProver.ElegantJointMeasurement.Teleportation.PhysicalUpper.alicePhysicalEquiv
      QuantumProver.ElegantJointMeasurement.Teleportation.PhysicalUpper.bobPhysicalEquiv
      QuantumProver.ElegantJointMeasurement.Teleportation.PhysicalUpper.occurrenceReport j), ?_, ?_⟩
  · exact subset_closure (QuantumProver.ElegantJointMeasurement.TailReference.groupedEffect_mem_finiteTreeEffectSet
      QuantumProver.ElegantJointMeasurement.Teleportation.PhysicalUpper.alicePhysicalEquiv
      QuantumProver.ElegantJointMeasurement.Teleportation.PhysicalUpper.bobPhysicalEquiv QuantumProver.ElegantJointMeasurement.Teleportation.oneEbitFiniteTree
      QuantumProver.ElegantJointMeasurement.Teleportation.PhysicalUpper.occurrenceReport)
  · intro ρ hρ ht
    rw [hJ]
    exact C.density_shared_channel ρ hρ ht

theorem one_mem_finiteTreeClosureCostSet : (1 : ℝ) ∈ finiteTreeClosureCostSet := by
  let C := QuantumProver.ElegantJointMeasurement.Teleportation.PhysicalUpper.one_ebit_physical_upper_certificate
  exact ⟨2, by decide, QuantumProver.ElegantJointMeasurement.Teleportation.resource, C.alice_reduced_density.2,
    one_ebit_implements_in_finite_tree_closure, C.alice_reduced_entropy⟩

theorem finiteTreeClosure_cost_eq_one : sInf finiteTreeClosureCostSet = 1 := by
  apply le_antisymm
  · exact csInf_le ⟨1, fun _ hc => finiteTreeClosureCostSet_lower hc⟩ one_mem_finiteTreeClosureCostSet
  · exact le_csInf ⟨1, one_mem_finiteTreeClosureCostSet⟩ fun _ hc => finiteTreeClosureCostSet_lower hc

end

end QuantumProver.ElegantJointMeasurement.FiniteTreeCostModel

namespace QuantumProver.ElegantJointMeasurement.CountableCostModel

open scoped BigOperators ComplexConjugate ComplexOrder Matrix Topology
open QuantumProver.ElegantJointMeasurement.GeneralResource QuantumProver.ElegantJointMeasurement.TailReference.DiscreteProtocol

noncomputable section

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

def matrixResourceBorn {m n : ℕ}
    (ea : (Fin 2 × κ) ≃ Fin m) (eb : (Fin 2 × κ) ≃ Fin n)
    (P : CountableProtocol m n) (h : List ℕ) (j : Fin 4)
    (Ψ : Matrix κ κ ℂ)
    (ρ : Matrix QuantumProver.ElegantJointMeasurement.Teleportation.SystemIndex QuantumProver.ElegantJointMeasurement.Teleportation.SystemIndex ℂ) : ℂ :=
  ∑' w, Matrix.trace (QuantumProver.ElegantJointMeasurement.ProtocolEffects.pullbackEffect ea eb (terminalEffect P h w j) *
    (codeMatrix (a := Fin 2) (b := Fin 2) Ψ * ρ *
      (codeMatrix (a := Fin 2) (b := Fin 2) Ψ)ᴴ))

theorem matrixResourceBorn_eq_effect_trace {m n : ℕ}
    (ea : (Fin 2 × κ) ≃ Fin m) (eb : (Fin 2 × κ) ≃ Fin n)
    (P : CountableProtocol m n) (h : List ℕ) (j : Fin 4)
    (hs : Summable (fun w => terminalEffect P h w j))
    (Ψ : Matrix κ κ ℂ)
    (ρ : Matrix QuantumProver.ElegantJointMeasurement.Teleportation.SystemIndex QuantumProver.ElegantJointMeasurement.Teleportation.SystemIndex ℂ) :
    matrixResourceBorn ea eb P h j Ψ ρ =
      Matrix.trace (QuantumProver.ElegantJointMeasurement.ProtocolEffects.pullbackEffect ea eb (terminalEffects P h j) *
        (codeMatrix (a := Fin 2) (b := Fin 2) Ψ * ρ *
          (codeMatrix (a := Fin 2) (b := Fin 2) Ψ)ᴴ)) := by
  let f : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ →+ ℂ :=
    { toFun := fun E => Matrix.trace (QuantumProver.ElegantJointMeasurement.ProtocolEffects.pullbackEffect ea eb E *
        (codeMatrix (a := Fin 2) (b := Fin 2) Ψ * ρ *
          (codeMatrix (a := Fin 2) (b := Fin 2) Ψ)ᴴ))
      map_zero' := by simp
      map_add' := by intro E G; simp [Matrix.add_mul, Matrix.trace_add] }
  have hf : Continuous f := by
    change Continuous (fun E => Matrix.trace (QuantumProver.ElegantJointMeasurement.ProtocolEffects.pullbackEffect ea eb E *
      (codeMatrix (a := Fin 2) (b := Fin 2) Ψ * ρ *
        (codeMatrix (a := Fin 2) (b := Fin 2) Ψ)ᴴ)))
    unfold QuantumProver.ElegantJointMeasurement.ProtocolEffects.pullbackEffect
    fun_prop
  exact (hs.hasSum.map f hf).tsum_eq

def matrixSharedResourceChannel {m n : ℕ}
    (ea : (Fin 2 × κ) ≃ Fin m) (eb : (Fin 2 × κ) ≃ Fin n)
    (P : CountableProtocol m n) (h : List ℕ) (Ψ : Matrix κ κ ℂ)
    (ρ : Matrix QuantumProver.ElegantJointMeasurement.Teleportation.SystemIndex QuantumProver.ElegantJointMeasurement.Teleportation.SystemIndex ℂ) :
    Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) ℂ :=
  ∑ j, matrixResourceBorn ea eb P h j Ψ ρ • QuantumProver.ElegantJointMeasurement.Teleportation.Tomography.sharedProjector j

theorem matrixSharedResourceChannel_eq_effect_channel {m n : ℕ}
    (ea : (Fin 2 × κ) ≃ Fin m) (eb : (Fin 2 × κ) ≃ Fin n)
    (P : CountableProtocol m n) (h : List ℕ) (hP : GloballyDeterministic P h)
    (Ψ : Matrix κ κ ℂ)
    (ρ : Matrix QuantumProver.ElegantJointMeasurement.Teleportation.SystemIndex QuantumProver.ElegantJointMeasurement.Teleportation.SystemIndex ℂ) :
    matrixSharedResourceChannel ea eb P h Ψ ρ =
      QuantumProver.ElegantJointMeasurement.Teleportation.Tomography.resourceMeasurementChannel
        (codeMatrix (a := Fin 2) (b := Fin 2) Ψ)
        (fun j => QuantumProver.ElegantJointMeasurement.ProtocolEffects.pullbackEffect ea eb (terminalEffects P h j)) ρ := by
  simp only [matrixSharedResourceChannel,
    QuantumProver.ElegantJointMeasurement.Teleportation.Tomography.resourceMeasurementChannel]
  apply Finset.sum_congr rfl
  intro j hj
  rw [matrixResourceBorn_eq_effect_trace ea eb P h j (hP.1 j)]

theorem countable_protocol_entropy_ge_one {m n : ℕ}
    (Ψ : Matrix κ κ ℂ) (hΨ : Matrix.trace (Ψ * Ψᴴ) = 1)
    (ea : (Fin 2 × κ) ≃ Fin m) (eb : (Fin 2 × κ) ≃ Fin n)
    (P : CountableProtocol m n) (bA : Fin m) (bB : Fin n)
    (hP : GloballyDeterministic P [])
    (hChannel : ∀ ρ : Matrix QuantumProver.ElegantJointMeasurement.Teleportation.SystemIndex QuantumProver.ElegantJointMeasurement.Teleportation.SystemIndex ℂ,
      ρ.PosSemidef → Matrix.trace ρ = 1 →
      matrixSharedResourceChannel ea eb P [] Ψ ρ = QuantumProver.ElegantJointMeasurement.Teleportation.physicalClassicalChannel ρ) :
    1 ≤ QuantumProver.ElegantJointMeasurement.TailReference.vonNeumannEntropyBits (Ψ * Ψᴴ) := by
  apply QuantumProver.ElegantJointMeasurement.FiniteTreeCostModel.entropy_ge_one_of_density_channel_effect_closure Ψ hΨ ea eb
    (fun j => QuantumProver.ElegantJointMeasurement.ProtocolEffects.pullbackEffect ea eb (terminalEffects P [] j))
    (countableProtocol_mem_finiteTreeEffectSet_closure ea eb P bA bB 0 [] hP)
  intro ρ hρ ht
  rw [← matrixSharedResourceChannel_eq_effect_channel ea eb P [] hP]
  exact hChannel ρ hρ ht

end

end QuantumProver.ElegantJointMeasurement.CountableCostModel

namespace QuantumProver.ElegantJointMeasurement.HilbertFiniteCostModel

open scoped BigOperators ComplexConjugate ComplexOrder Matrix Topology
open QuantumProver.ElegantJointMeasurement.GeneralResource

noncomputable section

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

def matrixCodeMatrix {m n : ℕ}
    (ea : (Fin 2 × κ) ≃ Fin m) (eb : (Fin 2 × κ) ≃ Fin n)
    (Ψ : Matrix κ κ ℂ) :
    Matrix (Fin m × Fin n) QuantumProver.ElegantJointMeasurement.Teleportation.SystemIndex ℂ :=
  (codeMatrix (a := Fin 2) (b := Fin 2) Ψ).submatrix (ea.prodCongr eb).symm id

theorem groupedEffect_matrixCP {m n : ℕ}
    (ea : (Fin 2 × κ) ≃ Fin m) (eb : (Fin 2 × κ) ≃ Fin n)
    (T : QuantumProver.ElegantJointMeasurement.CP.FiniteLocalCPInstrumentTree m n)
    (labels : QuantumProver.ElegantJointMeasurement.CP.FiniteLocalCPInstrumentTree.LeafLabels T (Fin 4)) (j : Fin 4) :
    QuantumProver.ElegantJointMeasurement.ProtocolEffects.groupedEffect T.krausRefinement ea eb (T.terminalReport labels) j =
      QuantumProver.ElegantJointMeasurement.ProtocolEffects.pullbackEffect ea eb (T.matrixReportedEffect labels j) := by
  classical
  simp only [QuantumProver.ElegantJointMeasurement.ProtocolEffects.groupedEffect, QuantumProver.ElegantJointMeasurement.ProtocolEffects.outcomeSum,
    QuantumProver.ElegantJointMeasurement.CP.FiniteLocalCPInstrumentTree.matrixReportedEffect, map_sum,
    apply_ite, map_zero, QuantumProver.ElegantJointMeasurement.ProtocolEffects.physicalEffect_eq_pullback]

theorem matrix_finite_CP_entropy_ge_one {m n : ℕ}
    (Ψ : Matrix κ κ ℂ) (hΨ : Matrix.trace (Ψ * Ψᴴ) = 1)
    (ea : (Fin 2 × κ) ≃ Fin m) (eb : (Fin 2 × κ) ≃ Fin n)
    (T : QuantumProver.ElegantJointMeasurement.CP.FiniteLocalCPInstrumentTree m n)
    (labels : QuantumProver.ElegantJointMeasurement.CP.FiniteLocalCPInstrumentTree.LeafLabels T (Fin 4 × Fin 4))
    (hChannel : ∀ ρ : Matrix QuantumProver.ElegantJointMeasurement.Teleportation.SystemIndex QuantumProver.ElegantJointMeasurement.Teleportation.SystemIndex ℂ,
      ρ.PosSemidef → Matrix.trace ρ = 1 →
      QuantumProver.ElegantJointMeasurement.Teleportation.ClassicalOutputRepair.matrixPairedChannel T labels
        (matrixCodeMatrix ea eb Ψ * ρ * (matrixCodeMatrix ea eb Ψ)ᴴ) =
        QuantumProver.ElegantJointMeasurement.Teleportation.physicalClassicalChannel ρ) :
    1 ≤ QuantumProver.ElegantJointMeasurement.TailReference.vonNeumannEntropyBits (Ψ * Ψᴴ) := by
  classical
  let firstLabels := QuantumProver.ElegantJointMeasurement.Teleportation.ClassicalOutputRepair.mapLeafLabels Prod.fst T labels
  let F := fun j => QuantumProver.ElegantJointMeasurement.ProtocolEffects.groupedEffect T.krausRefinement ea eb
    (T.terminalReport firstLabels) j
  have hc := QuantumProver.ElegantJointMeasurement.Teleportation.ClassicalOutputRepair.matrix_coded_exactness_implies_fst_compression
    T labels (matrixCodeMatrix ea eb Ψ) QuantumProver.ElegantJointMeasurement.Teleportation.represented_physicalEffect
    (by intro ρ hρ ht
        simpa only [← QuantumProver.ElegantJointMeasurement.Teleportation.Tomography.physicalClassicalChannel_eq_measurement]
          using hChannel ρ hρ ht)
  apply arbitrary_resource_entropy_ge_one_of_tree_effect_limit (l := Filter.atTop) Ψ hΨ
    (fun j => QuantumProver.ElegantJointMeasurement.Teleportation.PhysicalUpper.unitDirection j 0)
    (fun j => QuantumProver.ElegantJointMeasurement.Teleportation.PhysicalUpper.unitDirection j 1)
    (fun j => QuantumProver.ElegantJointMeasurement.Teleportation.PhysicalUpper.unitDirection j 2)
    QuantumProver.ElegantJointMeasurement.Teleportation.PhysicalUpper.unitDirection_sphere
    (fun _ : ℕ => T.krausRefinement) ea eb (fun _ => T.terminalReport firstLabels)
    F tendsto_const_nhds
  intro j
  change (codeContinuous Ψ).adjoint ∘L
    ((Matrix.toEuclideanLin (F j)).toContinuousLinearMap ∘L codeContinuous Ψ) = _
  rw [code_compression_matrix]
  have hg : F j = QuantumProver.ElegantJointMeasurement.ProtocolEffects.pullbackEffect ea eb
      (T.matrixReportedEffect firstLabels j) := groupedEffect_matrixCP ea eb T firstLabels j
  rw [hg]
  change (Matrix.toEuclideanLin
    ((codeMatrix (a := Fin 2) (b := Fin 2) Ψ)ᴴ *
      (T.matrixReportedEffect firstLabels j).submatrix (ea.prodCongr eb) (ea.prodCongr eb) *
      codeMatrix (a := Fin 2) (b := Fin 2) Ψ)).toContinuousLinearMap = _
  rw [← QuantumProver.ElegantJointMeasurement.Teleportation.InitialBasisTransport.compression_reindex
    (ea.prodCongr eb) (codeMatrix (a := Fin 2) (b := Fin 2) Ψ)]
  change (Matrix.toEuclideanLin
    ((matrixCodeMatrix ea eb Ψ)ᴴ * T.matrixReportedEffect firstLabels j *
      matrixCodeMatrix ea eb Ψ)).toContinuousLinearMap = _
  rw [hc j, QuantumProver.ElegantJointMeasurement.Teleportation.PhysicalUpper.physicalEffect_operator]

theorem matrix_finite_CP_density_limit_entropy_ge_one {m n : ℕ}
    (Ψ : Matrix κ κ ℂ) (hΨ : Matrix.trace (Ψ * Ψᴴ) = 1)
    (ea : (Fin 2 × κ) ≃ Fin m) (eb : (Fin 2 × κ) ≃ Fin n)
    (T : ℕ → QuantumProver.ElegantJointMeasurement.CP.FiniteLocalCPInstrumentTree m n)
    (labels : ∀ a, QuantumProver.ElegantJointMeasurement.CP.FiniteLocalCPInstrumentTree.LeafLabels (T a) (Fin 4 × Fin 4))
    (hChannel : ∀ ρ : Matrix QuantumProver.ElegantJointMeasurement.Teleportation.SystemIndex QuantumProver.ElegantJointMeasurement.Teleportation.SystemIndex ℂ,
      ρ.PosSemidef → Matrix.trace ρ = 1 →
      Filter.Tendsto (fun a =>
        QuantumProver.ElegantJointMeasurement.Teleportation.ClassicalOutputRepair.matrixPairedChannel (T a) (labels a)
          (matrixCodeMatrix ea eb Ψ * ρ * (matrixCodeMatrix ea eb Ψ)ᴴ))
        Filter.atTop (nhds (QuantumProver.ElegantJointMeasurement.Teleportation.physicalClassicalChannel ρ))) :
    1 ≤ QuantumProver.ElegantJointMeasurement.TailReference.vonNeumannEntropyBits (Ψ * Ψᴴ) := by
  classical
  let firstLabels := fun a => QuantumProver.ElegantJointMeasurement.Teleportation.ClassicalOutputRepair.mapLeafLabels
    Prod.fst (T a) (labels a)
  let F := fun a j => QuantumProver.ElegantJointMeasurement.ProtocolEffects.pullbackEffect ea eb
    ((T a).matrixReportedEffect (firstLabels a) j)
  have hc := QuantumProver.ElegantJointMeasurement.Teleportation.InitialBasisTransport.matrix_paired_limit_implies_physical_compression
    Filter.atTop T labels (fun _ => ea.prodCongr eb)
    (fun _ => codeMatrix (a := Fin 2) (b := Fin 2) Ψ) QuantumProver.ElegantJointMeasurement.Teleportation.represented_physicalEffect
    (by intro ρ hρ ht
        simpa only [QuantumProver.ElegantJointMeasurement.Teleportation.InitialBasisTransport.matrixEmbedding,
          ← QuantumProver.ElegantJointMeasurement.Teleportation.Tomography.physicalClassicalChannel_eq_measurement,
          matrixCodeMatrix] using hChannel ρ hρ ht)
  have hF : ∀ j, Filter.Tendsto (fun a =>
      (codeMatrix (a := Fin 2) (b := Fin 2) Ψ)ᴴ * F a j *
        codeMatrix (a := Fin 2) (b := Fin 2) Ψ)
      Filter.atTop (nhds (QuantumProver.ElegantJointMeasurement.Teleportation.represented_physicalEffect j)) := hc
  have hphysical := (QuantumProver.ElegantJointMeasurement.Teleportation.Tomography.resourceChannel_tendsto_iff_compressed
    Filter.atTop (codeMatrix (a := Fin 2) (b := Fin 2) Ψ) F
    QuantumProver.ElegantJointMeasurement.Teleportation.represented_physicalEffect).mpr hF
  apply QuantumProver.ElegantJointMeasurement.FiniteTreeCostModel.entropy_ge_one_of_density_channel_limit Ψ hΨ
    (fun a => (T a).krausRefinement) ea eb (fun a => (T a).terminalReport (firstLabels a))
  intro ρ hρ ht
  simpa only [groupedEffect_matrixCP,
    QuantumProver.ElegantJointMeasurement.Teleportation.Tomography.physicalClassicalChannel_eq_measurement]
    using hphysical ρ hρ ht

def matrixDependentPairedChannel {m n : ℕ}
    (T : QuantumProver.ElegantJointMeasurement.CP.DependentOutputCPInstrumentTree m n)
    (labels : QuantumProver.ElegantJointMeasurement.CP.DependentOutputCPInstrumentTree.LeafLabels T (Fin 4 × Fin 4))
    (X : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) :
    Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) ℂ :=
  ∑ a : Fin 4, ∑ b : Fin 4, T.matrixReportedEvaluation labels (a, b) X •
    Matrix.single (a, b) (a, b) 1

theorem matrixDependentPairedChannel_eq_commonTree {m n : ℕ}
    (T : QuantumProver.ElegantJointMeasurement.CP.DependentOutputCPInstrumentTree m n)
    (labels : QuantumProver.ElegantJointMeasurement.CP.DependentOutputCPInstrumentTree.LeafLabels T (Fin 4 × Fin 4))
    (X : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) :
    matrixDependentPairedChannel T labels X =
      QuantumProver.ElegantJointMeasurement.Teleportation.ClassicalOutputRepair.matrixPairedChannel T.commonTree
        (T.commonLabels labels) X := by
  simp only [matrixDependentPairedChannel,
    QuantumProver.ElegantJointMeasurement.Teleportation.ClassicalOutputRepair.matrixPairedChannel,
    T.matrixReportedEvaluation_eq_commonTree]

theorem matrix_dependent_CP_entropy_ge_one {m n : ℕ}
    (Ψ : Matrix κ κ ℂ) (hΨ : Matrix.trace (Ψ * Ψᴴ) = 1)
    (ea : (Fin 2 × κ) ≃ Fin m) (eb : (Fin 2 × κ) ≃ Fin n)
    (T : QuantumProver.ElegantJointMeasurement.CP.DependentOutputCPInstrumentTree m n)
    (labels : QuantumProver.ElegantJointMeasurement.CP.DependentOutputCPInstrumentTree.LeafLabels T (Fin 4 × Fin 4))
    (hChannel : ∀ ρ : Matrix QuantumProver.ElegantJointMeasurement.Teleportation.SystemIndex QuantumProver.ElegantJointMeasurement.Teleportation.SystemIndex ℂ,
      ρ.PosSemidef → Matrix.trace ρ = 1 →
      matrixDependentPairedChannel T labels
        (matrixCodeMatrix ea eb Ψ * ρ * (matrixCodeMatrix ea eb Ψ)ᴴ) =
        QuantumProver.ElegantJointMeasurement.Teleportation.physicalClassicalChannel ρ) :
    1 ≤ QuantumProver.ElegantJointMeasurement.TailReference.vonNeumannEntropyBits (Ψ * Ψᴴ) := by
  apply matrix_finite_CP_entropy_ge_one Ψ hΨ ea eb T.commonTree (T.commonLabels labels)
  intro ρ hρ ht
  simpa only [matrixDependentPairedChannel_eq_commonTree] using hChannel ρ hρ ht

theorem matrix_dependent_CP_density_limit_entropy_ge_one {m n : ℕ}
    (Ψ : Matrix κ κ ℂ) (hΨ : Matrix.trace (Ψ * Ψᴴ) = 1)
    (ea : (Fin 2 × κ) ≃ Fin m) (eb : (Fin 2 × κ) ≃ Fin n)
    (T : ℕ → QuantumProver.ElegantJointMeasurement.CP.DependentOutputCPInstrumentTree m n)
    (labels : ∀ a, QuantumProver.ElegantJointMeasurement.CP.DependentOutputCPInstrumentTree.LeafLabels (T a) (Fin 4 × Fin 4))
    (hChannel : ∀ ρ : Matrix QuantumProver.ElegantJointMeasurement.Teleportation.SystemIndex QuantumProver.ElegantJointMeasurement.Teleportation.SystemIndex ℂ,
      ρ.PosSemidef → Matrix.trace ρ = 1 →
      Filter.Tendsto (fun a => matrixDependentPairedChannel (T a) (labels a)
        (matrixCodeMatrix ea eb Ψ * ρ * (matrixCodeMatrix ea eb Ψ)ᴴ))
        Filter.atTop (nhds (QuantumProver.ElegantJointMeasurement.Teleportation.physicalClassicalChannel ρ))) :
    1 ≤ QuantumProver.ElegantJointMeasurement.TailReference.vonNeumannEntropyBits (Ψ * Ψᴴ) := by
  apply matrix_finite_CP_density_limit_entropy_ge_one Ψ hΨ ea eb
    (fun a => (T a).commonTree) (fun a => (T a).commonLabels (labels a))
  intro ρ hρ ht
  simpa only [matrixDependentPairedChannel_eq_commonTree] using hChannel ρ hρ ht

end

end QuantumProver.ElegantJointMeasurement.HilbertFiniteCostModel

namespace QuantumProver.ElegantJointMeasurement.HilbertCountableCostModel

open scoped BigOperators ComplexConjugate ComplexOrder Matrix Topology
open QuantumProver.ElegantJointMeasurement.GeneralResource QuantumProver.ElegantJointMeasurement.HilbertFiniteCostModel
open QuantumProver.ElegantJointMeasurement.TailReference.DiscreteCPProtocol

noncomputable section

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

def matrixSharedResourceChannel {m n : ℕ}
    (ea : (Fin 2 × κ) ≃ Fin m) (eb : (Fin 2 × κ) ≃ Fin n)
    (P : MatrixProtocol m n) (h : List ℕ) (Ψ : Matrix κ κ ℂ)
    (ρ : Matrix QuantumProver.ElegantJointMeasurement.Teleportation.SystemIndex QuantumProver.ElegantJointMeasurement.Teleportation.SystemIndex ℂ) :
    Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) ℂ :=
  ∑ j, matrixReportedEvaluation P h j
    (matrixCodeMatrix ea eb Ψ * ρ * (matrixCodeMatrix ea eb Ψ)ᴴ) •
      QuantumProver.ElegantJointMeasurement.Teleportation.Tomography.sharedProjector j

theorem matrixSharedResourceChannel_eq_effect_channel {m n : ℕ}
    (ea : (Fin 2 × κ) ≃ Fin m) (eb : (Fin 2 × κ) ≃ Fin n)
    (P : MatrixProtocol m n) (h : List ℕ) (hP : GloballyDeterministic P h)
    (Ψ : Matrix κ κ ℂ)
    (ρ : Matrix QuantumProver.ElegantJointMeasurement.Teleportation.SystemIndex QuantumProver.ElegantJointMeasurement.Teleportation.SystemIndex ℂ) :
    matrixSharedResourceChannel ea eb P h Ψ ρ =
      QuantumProver.ElegantJointMeasurement.Teleportation.Tomography.resourceMeasurementChannel
        (codeMatrix (a := Fin 2) (b := Fin 2) Ψ)
        (fun j => QuantumProver.ElegantJointMeasurement.ProtocolEffects.pullbackEffect ea eb (terminalEffects P h j)) ρ := by
  simp only [matrixSharedResourceChannel,
    QuantumProver.ElegantJointMeasurement.Teleportation.Tomography.resourceMeasurementChannel]
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  rw [matrixReportedEvaluation_eq_trace P h j (hP.1 j)]
  exact QuantumProver.ElegantJointMeasurement.Teleportation.InitialBasisTransport.trace_resource_reindex
    (ea.prodCongr eb) (codeMatrix (a := Fin 2) (b := Fin 2) Ψ)
    (terminalEffects P h j) ρ

theorem exists_finite_tree_channel_approximation {m n : ℕ} [NeZero m] [NeZero n]
    (ea : (Fin 2 × κ) ≃ Fin m) (eb : (Fin 2 × κ) ≃ Fin n)
    (P : MatrixProtocol m n) (bA : Fin m) (bB : Fin n)
    (hP : GloballyDeterministic P []) (Ψ : Matrix κ κ ℂ) :
    ∃ (T : ℕ → QuantumProver.ElegantJointMeasurement.Concurrence.FiniteLocalKrausTree m n)
      (report : (a : ℕ) → Fin (T a).terminalBraPairs.length → Fin 4),
      ∀ ρ : Matrix QuantumProver.ElegantJointMeasurement.Teleportation.SystemIndex QuantumProver.ElegantJointMeasurement.Teleportation.SystemIndex ℂ,
        Filter.Tendsto (fun a => QuantumProver.ElegantJointMeasurement.Teleportation.Tomography.resourceMeasurementChannel
          (codeMatrix (a := Fin 2) (b := Fin 2) Ψ)
          (fun j => QuantumProver.ElegantJointMeasurement.ProtocolEffects.groupedEffect (T a) ea eb (report a) j) ρ)
          Filter.atTop (nhds (matrixSharedResourceChannel ea eb P [] Ψ ρ)) := by
  let F := fun j => QuantumProver.ElegantJointMeasurement.ProtocolEffects.pullbackEffect ea eb (terminalEffects P [] j)
  have hF : F ∈ closure (QuantumProver.ElegantJointMeasurement.TailReference.finiteTreeEffectSet ea eb) :=
    matrixProtocol_mem_finiteTreeEffectSet_closure ea eb P bA bB 0 hP
  obtain ⟨T, report, hlim⟩ :=
    QuantumProver.ElegantJointMeasurement.TailReference.finiteTreeEffectSet_closure_sequence ea eb F hF
  refine ⟨T, report, ?_⟩
  intro ρ
  rw [matrixSharedResourceChannel_eq_effect_channel ea eb P [] hP]
  have hc : Continuous (fun G : Fin 4 →
      Matrix (QuantumProver.ElegantJointMeasurement.Augmented.Index κ) (QuantumProver.ElegantJointMeasurement.Augmented.Index κ) ℂ =>
      QuantumProver.ElegantJointMeasurement.Teleportation.Tomography.resourceMeasurementChannel
        (codeMatrix (a := Fin 2) (b := Fin 2) Ψ) G ρ) := by
    unfold QuantumProver.ElegantJointMeasurement.Teleportation.Tomography.resourceMeasurementChannel
    fun_prop
  exact (hc.tendsto F).comp hlim

theorem matrix_countable_CP_entropy_ge_one {m n : ℕ} [NeZero m] [NeZero n]
    (Ψ : Matrix κ κ ℂ) (hΨ : Matrix.trace (Ψ * Ψᴴ) = 1)
    (ea : (Fin 2 × κ) ≃ Fin m) (eb : (Fin 2 × κ) ≃ Fin n)
    (P : MatrixProtocol m n) (bA : Fin m) (bB : Fin n)
    (hP : GloballyDeterministic P [])
    (hChannel : ∀ ρ : Matrix QuantumProver.ElegantJointMeasurement.Teleportation.SystemIndex QuantumProver.ElegantJointMeasurement.Teleportation.SystemIndex ℂ,
      ρ.PosSemidef → Matrix.trace ρ = 1 →
      matrixSharedResourceChannel ea eb P [] Ψ ρ =
        QuantumProver.ElegantJointMeasurement.Teleportation.physicalClassicalChannel ρ) :
    1 ≤ QuantumProver.ElegantJointMeasurement.TailReference.vonNeumannEntropyBits (Ψ * Ψᴴ) := by
  apply QuantumProver.ElegantJointMeasurement.FiniteTreeCostModel.entropy_ge_one_of_density_channel_effect_closure Ψ hΨ ea eb
    (fun j => QuantumProver.ElegantJointMeasurement.ProtocolEffects.pullbackEffect ea eb (terminalEffects P [] j))
    (matrixProtocol_mem_finiteTreeEffectSet_closure ea eb P bA bB 0 hP)
  intro ρ hρ ht
  rw [← matrixSharedResourceChannel_eq_effect_channel ea eb P [] hP]
  exact hChannel ρ hρ ht

end

end QuantumProver.ElegantJointMeasurement.HilbertCountableCostModel

namespace QuantumProver.ElegantJointMeasurement.PhysicalChannelCostModel

open scoped BigOperators ComplexConjugate ComplexOrder Matrix Topology
open QuantumProver.ElegantJointMeasurement.GeneralResource

noncomputable section

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

theorem normalized_code_gram (Ψ : Matrix κ κ ℂ)
    (hΨ : Matrix.trace (Ψ * Ψᴴ) = 1) :
    (codeMatrix (a := Fin 2) (b := Fin 2) Ψ)ᴴ * codeMatrix (a := Fin 2) (b := Fin 2) Ψ = 1 := by
  let J := codeMatrix (a := Fin 2) (b := Fin 2) Ψ
  have ho : (Matrix.toEuclideanLin
      (1 : Matrix (QuantumProver.ElegantJointMeasurement.Augmented.Index κ) (QuantumProver.ElegantJointMeasurement.Augmented.Index κ) ℂ)).toContinuousLinearMap =
      (1 : QuantumProver.ElegantJointMeasurement.ResourceCode.ExtendedSpace (Fin 2) (Fin 2) κ →L[ℂ]
        QuantumProver.ElegantJointMeasurement.ResourceCode.ExtendedSpace (Fin 2) (Fin 2) κ) := by
    ext E z
    change ((1 : Matrix (QuantumProver.ElegantJointMeasurement.Augmented.Index κ) (QuantumProver.ElegantJointMeasurement.Augmented.Index κ) ℂ) *ᵥ E.ofLp) z = E z
    simp
  have hi : (Matrix.toEuclideanLin
      (1 : Matrix QuantumProver.ElegantJointMeasurement.Teleportation.SystemIndex QuantumProver.ElegantJointMeasurement.Teleportation.SystemIndex ℂ)).toContinuousLinearMap =
      (1 : QuantumProver.ElegantJointMeasurement.ResourceCode.InputSpace (Fin 2) (Fin 2) →L[ℂ]
        QuantumProver.ElegantJointMeasurement.ResourceCode.InputSpace (Fin 2) (Fin 2)) := by
    ext E z
    change ((1 : Matrix QuantumProver.ElegantJointMeasurement.Teleportation.SystemIndex QuantumProver.ElegantJointMeasurement.Teleportation.SystemIndex ℂ) *ᵥ E.ofLp) z = E z
    simp
  have hcomp := code_compression_matrix (a := Fin 2) (b := Fin 2) Ψ
    (1 : Matrix (QuantumProver.ElegantJointMeasurement.Augmented.Index κ) (QuantumProver.ElegantJointMeasurement.Augmented.Index κ) ℂ)
  rw [ho, ContinuousLinearMap.one_def, ContinuousLinearMap.id_comp, Matrix.mul_one] at hcomp
  have hiso := (codeContinuous (a := Fin 2) (b := Fin 2) Ψ).norm_map_iff_adjoint_comp_self.mp
    (code_norm Ψ hΨ)
  have hmat : (Matrix.toEuclideanLin (Jᴴ * J)).toContinuousLinearMap =
      (Matrix.toEuclideanLin
        (1 : Matrix QuantumProver.ElegantJointMeasurement.Teleportation.SystemIndex QuantumProver.ElegantJointMeasurement.Teleportation.SystemIndex ℂ)).toContinuousLinearMap :=
    hcomp.symm.trans (hiso.trans hi.symm)
  apply Matrix.toEuclideanLin.injective
  exact congrArg ContinuousLinearMap.toLinearMap hmat

def resourceEncoding (Ψ : Matrix κ κ ℂ) :
    Matrix QuantumProver.ElegantJointMeasurement.Teleportation.SystemIndex QuantumProver.ElegantJointMeasurement.Teleportation.SystemIndex ℂ →ₗ[ℂ]
      Matrix (QuantumProver.ElegantJointMeasurement.Augmented.Index κ) (QuantumProver.ElegantJointMeasurement.Augmented.Index κ) ℂ :=
  QuantumProver.ElegantJointMeasurement.CP.krausMap (fun _ : Unit => codeMatrix (a := Fin 2) (b := Fin 2) Ψ)

omit [Fintype κ] [DecidableEq κ] in
theorem resourceEncoding_apply (Ψ : Matrix κ κ ℂ)
    (ρ : Matrix QuantumProver.ElegantJointMeasurement.Teleportation.SystemIndex QuantumProver.ElegantJointMeasurement.Teleportation.SystemIndex ℂ) :
    resourceEncoding Ψ ρ = codeMatrix (a := Fin 2) (b := Fin 2) Ψ * ρ * (codeMatrix (a := Fin 2) (b := Fin 2) Ψ)ᴴ := by
  simp [resourceEncoding, QuantumProver.ElegantJointMeasurement.CP.krausMap]

theorem resourceEncoding_completelyPositive (Ψ : Matrix κ κ ℂ) :
    QuantumProver.ElegantJointMeasurement.CP.CompletelyPositive (resourceEncoding Ψ) :=
  QuantumProver.ElegantJointMeasurement.CP.krausMap_completelyPositive _

theorem resourceEncoding_tracePreserving (Ψ : Matrix κ κ ℂ)
    (hΨ : Matrix.trace (Ψ * Ψᴴ) = 1)
    (ρ : Matrix QuantumProver.ElegantJointMeasurement.Teleportation.SystemIndex QuantumProver.ElegantJointMeasurement.Teleportation.SystemIndex ℂ) :
    Matrix.trace (resourceEncoding Ψ ρ) = Matrix.trace ρ := by
  rw [resourceEncoding_apply]
  calc
    _ = Matrix.trace ((codeMatrix (a := Fin 2) (b := Fin 2) Ψ)ᴴ * codeMatrix (a := Fin 2) (b := Fin 2) Ψ * ρ) := by
      simpa only [Matrix.mul_assoc] using
        (Matrix.trace_mul_cycle (codeMatrix (a := Fin 2) (b := Fin 2) Ψ) ρ (codeMatrix (a := Fin 2) (b := Fin 2) Ψ)ᴴ)
    _ = Matrix.trace ρ := by rw [normalized_code_gram Ψ hΨ, Matrix.one_mul]

theorem paired_channel_entropy_ge_one_of_first_effect_closure {m n : ℕ}
    (Ψ : Matrix κ κ ℂ) (hΨ : Matrix.trace (Ψ * Ψᴴ) = 1)
    (ea : (Fin 2 × κ) ≃ Fin m) (eb : (Fin 2 × κ) ≃ Fin n)
    (Γ : Matrix (QuantumProver.ElegantJointMeasurement.Augmented.Index κ) (QuantumProver.ElegantJointMeasurement.Augmented.Index κ) ℂ →ₗ[ℂ]
      QuantumProver.ElegantJointMeasurement.Teleportation.ClassicalOutputRepair.OutputMatrix)
    (hF : QuantumProver.ElegantJointMeasurement.Teleportation.ChannelFirstEffects.firstEffect Γ ∈
      closure (QuantumProver.ElegantJointMeasurement.TailReference.finiteTreeEffectSet ea eb))
    (hChannel : ∀ ρ : Matrix QuantumProver.ElegantJointMeasurement.Teleportation.SystemIndex QuantumProver.ElegantJointMeasurement.Teleportation.SystemIndex ℂ,
      ρ.PosSemidef → Matrix.trace ρ = 1 →
      Γ (resourceEncoding Ψ ρ) = QuantumProver.ElegantJointMeasurement.Teleportation.physicalClassicalChannel ρ) :
    1 ≤ QuantumProver.ElegantJointMeasurement.TailReference.vonNeumannEntropyBits (Ψ * Ψᴴ) := by
  have hc := QuantumProver.ElegantJointMeasurement.Teleportation.ChannelFirstEffects.coded_density_exactness_implies_firstEffect_compression
    Γ (codeMatrix (a := Fin 2) (b := Fin 2) Ψ) QuantumProver.ElegantJointMeasurement.Teleportation.represented_physicalEffect
    (by
      intro ρ hρ ht
      simpa only [resourceEncoding_apply,
        ← QuantumProver.ElegantJointMeasurement.Teleportation.Tomography.physicalClassicalChannel_eq_measurement]
        using hChannel ρ hρ ht)
  have hresource := (QuantumProver.ElegantJointMeasurement.Teleportation.Tomography.resourceChannel_exact_iff_compressed
    (codeMatrix (a := Fin 2) (b := Fin 2) Ψ)
    (QuantumProver.ElegantJointMeasurement.Teleportation.ChannelFirstEffects.firstEffect Γ)
    QuantumProver.ElegantJointMeasurement.Teleportation.represented_physicalEffect).mpr (funext hc)
  apply QuantumProver.ElegantJointMeasurement.FiniteTreeCostModel.entropy_ge_one_of_density_channel_effect_closure Ψ hΨ ea eb
    (QuantumProver.ElegantJointMeasurement.Teleportation.ChannelFirstEffects.firstEffect Γ) hF
  intro ρ hρ ht
  simpa only [← QuantumProver.ElegantJointMeasurement.Teleportation.Tomography.physicalClassicalChannel_eq_measurement]
    using hresource ρ hρ ht

end

end QuantumProver.ElegantJointMeasurement.PhysicalChannelCostModel

namespace QuantumProver.ElegantJointMeasurement.MixedLocalAncillaCostModel

open scoped BigOperators ComplexConjugate ComplexOrder Matrix Topology
open QuantumProver.ElegantJointMeasurement.GeneralResource QuantumProver.ElegantJointMeasurement.HilbertFiniteCostModel
open QuantumProver.ElegantJointMeasurement.Teleportation.MixedLocalAncillas

noncomputable section

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

theorem initial_dimensions_pos {m n : ℕ}
    (Ψ : Matrix κ κ ℂ) (hΨ : Matrix.trace (Ψ * Ψᴴ) = 1)
    (ea : (Fin 2 × κ) ≃ Fin m) (eb : (Fin 2 × κ) ≃ Fin n) :
    0 < m ∧ 0 < n := by
  classical
  have hκ : Nonempty κ := by
    by_contra h
    haveI : IsEmpty κ := not_nonempty_iff.mp h
    have hz : Matrix.trace (Ψ * Ψᴴ) = 0 := by simp [Matrix.trace]
    rw [hz] at hΨ
    exact zero_ne_one hΨ
  obtain ⟨k⟩ := hκ
  exact ⟨lt_of_le_of_lt (Nat.zero_le _) (ea ((0 : Fin 2), k)).isLt,
    lt_of_le_of_lt (Nat.zero_le _) (eb ((0 : Fin 2), k)).isLt⟩

theorem matrixDependentPairedChannel_prepend {m n da db : ℕ}
    (hm : 0 < m) (hn : 0 < n)
    (α : Matrix (Fin da) (Fin da) ℂ) (hα : α.PosSemidef) (tα : α.trace = 1)
    (β : Matrix (Fin db) (Fin db) ℂ) (hβ : β.PosSemidef) (tβ : β.trace = 1)
    (T : QuantumProver.ElegantJointMeasurement.CP.DependentOutputCPInstrumentTree (m * da) (n * db))
    (labels : QuantumProver.ElegantJointMeasurement.CP.DependentOutputCPInstrumentTree.LeafLabels T (Fin 4 × Fin 4))
    (X : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) :
    matrixDependentPairedChannel
      (prependLocalAncillas hm hn α hα tα β hβ tβ T)
      (prependLabels hm hn α hα tα β hβ tβ T labels) X =
      matrixDependentPairedChannel T labels (augmentedProductState α β X) := by
  simp only [matrixDependentPairedChannel, prepend_matrixReportedEvaluation]

theorem matrix_CP_mixed_local_ancillas_entropy_ge_one {m n da db : ℕ}
    (Ψ : Matrix κ κ ℂ) (hΨ : Matrix.trace (Ψ * Ψᴴ) = 1)
    (ea : (Fin 2 × κ) ≃ Fin m) (eb : (Fin 2 × κ) ≃ Fin n)
    (α : Matrix (Fin da) (Fin da) ℂ) (hα : α.PosSemidef) (tα : α.trace = 1)
    (β : Matrix (Fin db) (Fin db) ℂ) (hβ : β.PosSemidef) (tβ : β.trace = 1)
    (T : QuantumProver.ElegantJointMeasurement.CP.DependentOutputCPInstrumentTree (m * da) (n * db))
    (labels : QuantumProver.ElegantJointMeasurement.CP.DependentOutputCPInstrumentTree.LeafLabels T (Fin 4 × Fin 4))
    (hChannel : ∀ ρ : Matrix QuantumProver.ElegantJointMeasurement.Teleportation.SystemIndex QuantumProver.ElegantJointMeasurement.Teleportation.SystemIndex ℂ,
      ρ.PosSemidef → Matrix.trace ρ = 1 →
      matrixDependentPairedChannel T labels
        (augmentedProductState α β
          (matrixCodeMatrix ea eb Ψ * ρ * (matrixCodeMatrix ea eb Ψ)ᴴ)) =
        QuantumProver.ElegantJointMeasurement.Teleportation.physicalClassicalChannel ρ) :
    1 ≤ QuantumProver.ElegantJointMeasurement.TailReference.vonNeumannEntropyBits (Ψ * Ψᴴ) := by
  obtain ⟨hm, hn⟩ := initial_dimensions_pos Ψ hΨ ea eb
  apply matrix_dependent_CP_entropy_ge_one Ψ hΨ ea eb
    (prependLocalAncillas hm hn α hα tα β hβ tβ T)
    (prependLabels hm hn α hα tα β hβ tβ T labels)
  intro ρ hρ ht
  simpa only [matrixDependentPairedChannel_prepend] using hChannel ρ hρ ht

theorem matrix_CP_varying_mixed_local_ancillas_density_limit_entropy_ge_one {m n : ℕ}
    (Ψ : Matrix κ κ ℂ) (hΨ : Matrix.trace (Ψ * Ψᴴ) = 1)
    (ea : (Fin 2 × κ) ≃ Fin m) (eb : (Fin 2 × κ) ≃ Fin n)
    (da db : ℕ → ℕ)
    (α : ∀ r, Matrix (Fin (da r)) (Fin (da r)) ℂ)
    (hα : ∀ r, (α r).PosSemidef) (tα : ∀ r, (α r).trace = 1)
    (β : ∀ r, Matrix (Fin (db r)) (Fin (db r)) ℂ)
    (hβ : ∀ r, (β r).PosSemidef) (tβ : ∀ r, (β r).trace = 1)
    (T : ∀ r, QuantumProver.ElegantJointMeasurement.CP.DependentOutputCPInstrumentTree (m * da r) (n * db r))
    (labels : ∀ r, QuantumProver.ElegantJointMeasurement.CP.DependentOutputCPInstrumentTree.LeafLabels (T r) (Fin 4 × Fin 4))
    (hChannel : ∀ ρ : Matrix QuantumProver.ElegantJointMeasurement.Teleportation.SystemIndex QuantumProver.ElegantJointMeasurement.Teleportation.SystemIndex ℂ,
      ρ.PosSemidef → Matrix.trace ρ = 1 →
      Filter.Tendsto (fun r => matrixDependentPairedChannel (T r) (labels r)
        (augmentedProductState (α r) (β r)
          (matrixCodeMatrix ea eb Ψ * ρ * (matrixCodeMatrix ea eb Ψ)ᴴ)))
        Filter.atTop (nhds (QuantumProver.ElegantJointMeasurement.Teleportation.physicalClassicalChannel ρ))) :
    1 ≤ QuantumProver.ElegantJointMeasurement.TailReference.vonNeumannEntropyBits (Ψ * Ψᴴ) := by
  obtain ⟨hm, hn⟩ := initial_dimensions_pos Ψ hΨ ea eb
  apply matrix_dependent_CP_density_limit_entropy_ge_one Ψ hΨ ea eb
    (fun r => prependLocalAncillas hm hn (α r) (hα r) (tα r) (β r) (hβ r) (tβ r) (T r))
    (fun r => prependLabels hm hn (α r) (hα r) (tα r) (β r) (hβ r) (tβ r) (T r) (labels r))
  intro ρ hρ ht
  simpa only [matrixDependentPairedChannel_prepend] using hChannel ρ hρ ht

end

end QuantumProver.ElegantJointMeasurement.MixedLocalAncillaCostModel

namespace QuantumProver.ElegantJointMeasurement.HilbertVaryingCostModel

open scoped BigOperators ComplexConjugate ComplexOrder Matrix Topology
open QuantumProver.ElegantJointMeasurement.GeneralResource QuantumProver.ElegantJointMeasurement.HilbertFiniteCostModel
open QuantumProver.ElegantJointMeasurement.TailReference.VaryingProtocol

noncomputable section

variable {κ : Type*} [Fintype κ] [DecidableEq κ]
variable {S : ℕ → ℕ → Type*}

def matrixVaryingSharedResourceChannel {m n : ℕ}
    (ea : (Fin 2 × κ) ≃ Fin m) (eb : (Fin 2 × κ) ≃ Fin n)
    (P : MatrixMachine S) (z : S m n) (Ψ : Matrix κ κ ℂ)
    (ρ : Matrix QuantumProver.ElegantJointMeasurement.Teleportation.SystemIndex QuantumProver.ElegantJointMeasurement.Teleportation.SystemIndex ℂ) :
    Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) ℂ :=
  ∑ j, matrixReportedEvaluation P z j
    (matrixCodeMatrix ea eb Ψ * ρ * (matrixCodeMatrix ea eb Ψ)ᴴ) •
      QuantumProver.ElegantJointMeasurement.Teleportation.Tomography.sharedProjector j

theorem matrixVaryingSharedResourceChannel_eq_effect_channel {m n : ℕ}
    (ea : (Fin 2 × κ) ≃ Fin m) (eb : (Fin 2 × κ) ≃ Fin n)
    (P : MatrixMachine S) (z : S m n) (hP : GloballyDeterministic P z)
    (Ψ : Matrix κ κ ℂ)
    (ρ : Matrix QuantumProver.ElegantJointMeasurement.Teleportation.SystemIndex QuantumProver.ElegantJointMeasurement.Teleportation.SystemIndex ℂ) :
    matrixVaryingSharedResourceChannel ea eb P z Ψ ρ =
      QuantumProver.ElegantJointMeasurement.Teleportation.Tomography.resourceMeasurementChannel
        (codeMatrix (a := Fin 2) (b := Fin 2) Ψ)
        (fun j => QuantumProver.ElegantJointMeasurement.ProtocolEffects.pullbackEffect ea eb (terminalEffects P z j)) ρ := by
  simp only [matrixVaryingSharedResourceChannel,
    QuantumProver.ElegantJointMeasurement.Teleportation.Tomography.resourceMeasurementChannel]
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  rw [matrixReportedEvaluation_eq_trace P z j (hP.1 j)]
  exact QuantumProver.ElegantJointMeasurement.Teleportation.InitialBasisTransport.trace_resource_reindex
    (ea.prodCongr eb) (codeMatrix (a := Fin 2) (b := Fin 2) Ψ)
    (terminalEffects P z j) ρ

theorem exists_finite_tree_channel_approximation {m n : ℕ} [NeZero m] [NeZero n]
    (ea : (Fin 2 × κ) ≃ Fin m) (eb : (Fin 2 × κ) ≃ Fin n)
    (P : MatrixMachine S) (z : S m n) (bA : Fin m) (bB : Fin n)
    (hP : GloballyDeterministic P z) (Ψ : Matrix κ κ ℂ) :
    ∃ (T : ℕ → QuantumProver.ElegantJointMeasurement.Concurrence.FiniteLocalKrausTree m n)
      (report : (a : ℕ) → Fin (T a).terminalBraPairs.length → Fin 4),
      ∀ ρ : Matrix QuantumProver.ElegantJointMeasurement.Teleportation.SystemIndex QuantumProver.ElegantJointMeasurement.Teleportation.SystemIndex ℂ,
        Filter.Tendsto (fun a => QuantumProver.ElegantJointMeasurement.Teleportation.Tomography.resourceMeasurementChannel
          (codeMatrix (a := Fin 2) (b := Fin 2) Ψ)
          (fun j => QuantumProver.ElegantJointMeasurement.ProtocolEffects.groupedEffect (T a) ea eb (report a) j) ρ)
          Filter.atTop (nhds (matrixVaryingSharedResourceChannel ea eb P z Ψ ρ)) := by
  let F := fun j => QuantumProver.ElegantJointMeasurement.ProtocolEffects.pullbackEffect ea eb (terminalEffects P z j)
  have hF : F ∈ closure (QuantumProver.ElegantJointMeasurement.TailReference.finiteTreeEffectSet ea eb) :=
    varyingProtocol_mem_finiteTreeEffectSet_closure ea eb P z bA bB 0 hP
  obtain ⟨T, report, hlim⟩ :=
    QuantumProver.ElegantJointMeasurement.TailReference.finiteTreeEffectSet_closure_sequence ea eb F hF
  refine ⟨T, report, ?_⟩
  intro ρ
  rw [matrixVaryingSharedResourceChannel_eq_effect_channel ea eb P z hP]
  have hc : Continuous (fun G : Fin 4 →
      Matrix (QuantumProver.ElegantJointMeasurement.Augmented.Index κ) (QuantumProver.ElegantJointMeasurement.Augmented.Index κ) ℂ =>
      QuantumProver.ElegantJointMeasurement.Teleportation.Tomography.resourceMeasurementChannel
        (codeMatrix (a := Fin 2) (b := Fin 2) Ψ) G ρ) := by
    unfold QuantumProver.ElegantJointMeasurement.Teleportation.Tomography.resourceMeasurementChannel
    fun_prop
  exact (hc.tendsto F).comp hlim

theorem matrix_varying_workspace_countable_CP_entropy_ge_one {m n : ℕ} [NeZero m] [NeZero n]
    (Ψ : Matrix κ κ ℂ) (hΨ : Matrix.trace (Ψ * Ψᴴ) = 1)
    (ea : (Fin 2 × κ) ≃ Fin m) (eb : (Fin 2 × κ) ≃ Fin n)
    (P : MatrixMachine S) (z : S m n) (bA : Fin m) (bB : Fin n)
    (hP : GloballyDeterministic P z)
    (hChannel : ∀ ρ : Matrix QuantumProver.ElegantJointMeasurement.Teleportation.SystemIndex QuantumProver.ElegantJointMeasurement.Teleportation.SystemIndex ℂ,
      ρ.PosSemidef → Matrix.trace ρ = 1 →
      matrixVaryingSharedResourceChannel ea eb P z Ψ ρ =
        QuantumProver.ElegantJointMeasurement.Teleportation.physicalClassicalChannel ρ) :
    1 ≤ QuantumProver.ElegantJointMeasurement.TailReference.vonNeumannEntropyBits (Ψ * Ψᴴ) := by
  apply QuantumProver.ElegantJointMeasurement.FiniteTreeCostModel.entropy_ge_one_of_density_channel_effect_closure Ψ hΨ ea eb
    (fun j => QuantumProver.ElegantJointMeasurement.ProtocolEffects.pullbackEffect ea eb (terminalEffects P z j))
    (varyingProtocol_mem_finiteTreeEffectSet_closure ea eb P z bA bB 0 hP)
  intro ρ hρ ht
  rw [← matrixVaryingSharedResourceChannel_eq_effect_channel ea eb P z hP]
  exact hChannel ρ hρ ht

end

end QuantumProver.ElegantJointMeasurement.HilbertVaryingCostModel

namespace QuantumProver.ElegantJointMeasurement.EncodedResourceCostModel

open scoped BigOperators ComplexConjugate ComplexOrder Matrix Topology
open QuantumProver.ElegantJointMeasurement.GeneralResource QuantumProver.ElegantJointMeasurement.HilbertFiniteCostModel QuantumProver.ElegantJointMeasurement.HilbertVaryingCostModel
open QuantumProver.ElegantJointMeasurement.TailReference.VaryingProtocol

noncomputable section

variable {κ : Type*} [Fintype κ] [DecidableEq κ]
variable {S : ℕ → ℕ → Type*}

theorem matrixCodeMatrix_compression {m n : ℕ}
    (ea : (Fin 2 × κ) ≃ Fin m) (eb : (Fin 2 × κ) ≃ Fin n)
    (Ψ : Matrix κ κ ℂ) (F : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) :
    (matrixCodeMatrix ea eb Ψ)ᴴ * F * matrixCodeMatrix ea eb Ψ =
      (codeMatrix (a := Fin 2) (b := Fin 2) Ψ)ᴴ *
        QuantumProver.ElegantJointMeasurement.ProtocolEffects.pullbackEffect ea eb F * codeMatrix (a := Fin 2) (b := Fin 2) Ψ := by
  change ((codeMatrix (a := Fin 2) (b := Fin 2) Ψ).submatrix
      (ea.prodCongr eb).symm id)ᴴ * F *
      (codeMatrix (a := Fin 2) (b := Fin 2) Ψ).submatrix
        (ea.prodCongr eb).symm id =
    (codeMatrix (a := Fin 2) (b := Fin 2) Ψ)ᴴ *
      F.submatrix (ea.prodCongr eb) (ea.prodCongr eb) *
      codeMatrix (a := Fin 2) (b := Fin 2) Ψ
  exact QuantumProver.ElegantJointMeasurement.Teleportation.InitialBasisTransport.compression_reindex
    (ea.prodCongr eb) (codeMatrix (a := Fin 2) (b := Fin 2) Ψ) F

theorem matrixCodeMatrix_gram {m n : ℕ}
    (ea : (Fin 2 × κ) ≃ Fin m) (eb : (Fin 2 × κ) ≃ Fin n)
    (Ψ : Matrix κ κ ℂ) (hΨ : Matrix.trace (Ψ * Ψᴴ) = 1) :
    (matrixCodeMatrix ea eb Ψ)ᴴ * matrixCodeMatrix ea eb Ψ = 1 := by
  have h := matrixCodeMatrix_compression ea eb Ψ
    (1 : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ)
  simpa only [QuantumProver.ElegantJointMeasurement.ProtocolEffects.pullbackEffect_one, Matrix.mul_one,
    QuantumProver.ElegantJointMeasurement.PhysicalChannelCostModel.normalized_code_gram Ψ hΨ] using h

theorem matrixSharedResourceChannel_eq_effect_channel {m n : ℕ}
    (ea : (Fin 2 × κ) ≃ Fin m) (eb : (Fin 2 × κ) ≃ Fin n)
    (P : MatrixMachine S) (z : S m n) (Ψ : Matrix κ κ ℂ)
    (ρ : Matrix QuantumProver.ElegantJointMeasurement.Teleportation.SystemIndex QuantumProver.ElegantJointMeasurement.Teleportation.SystemIndex ℂ) :
    matrixVaryingSharedResourceChannel ea eb P z Ψ ρ =
      QuantumProver.ElegantJointMeasurement.Teleportation.Tomography.resourceMeasurementChannel
        (codeMatrix (a := Fin 2) (b := Fin 2) Ψ)
        (fun j => QuantumProver.ElegantJointMeasurement.ProtocolEffects.pullbackEffect ea eb (terminalEffects P z j)) ρ := by
  simp only [matrixVaryingSharedResourceChannel,
    QuantumProver.ElegantJointMeasurement.Teleportation.Tomography.resourceMeasurementChannel]
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  rw [matrixReportedEvaluation_eq_trace P z j (terminal_summable P z 0 j)]
  exact QuantumProver.ElegantJointMeasurement.Teleportation.InitialBasisTransport.trace_resource_reindex
    (ea.prodCongr eb) (codeMatrix (a := Fin 2) (b := Fin 2) Ψ)
    (terminalEffects P z j) ρ

theorem matrix_density_exactness_implies_compressed_effects {m n : ℕ}
    (ea : (Fin 2 × κ) ≃ Fin m) (eb : (Fin 2 × κ) ≃ Fin n)
    (P : MatrixMachine S) (z : S m n) (Ψ : Matrix κ κ ℂ)
    (hChannel : ∀ ρ : Matrix QuantumProver.ElegantJointMeasurement.Teleportation.SystemIndex QuantumProver.ElegantJointMeasurement.Teleportation.SystemIndex ℂ,
      ρ.PosSemidef → Matrix.trace ρ = 1 →
      matrixVaryingSharedResourceChannel ea eb P z Ψ ρ =
        QuantumProver.ElegantJointMeasurement.Teleportation.physicalClassicalChannel ρ) :
    ∀ j, (matrixCodeMatrix ea eb Ψ)ᴴ * terminalEffects P z j * matrixCodeMatrix ea eb Ψ =
      QuantumProver.ElegantJointMeasurement.Teleportation.represented_physicalEffect j := by
  have hc := QuantumProver.ElegantJointMeasurement.Teleportation.Tomography.ejm_density_exactness_implies_compressed_effects
    (codeMatrix (a := Fin 2) (b := Fin 2) Ψ)
    (fun j => QuantumProver.ElegantJointMeasurement.ProtocolEffects.pullbackEffect ea eb (terminalEffects P z j))
    (by
      intro ρ hρ ht
      rw [← matrixSharedResourceChannel_eq_effect_channel ea eb P z Ψ ρ]
      exact hChannel ρ hρ ht)
  intro j
  rw [matrixCodeMatrix_compression]
  exact hc j

theorem matrix_density_exactness_implies_code_completeness {m n : ℕ}
    (ea : (Fin 2 × κ) ≃ Fin m) (eb : (Fin 2 × κ) ≃ Fin n)
    (P : MatrixMachine S) (z : S m n)
    (Ψ : Matrix κ κ ℂ) (hΨ : Matrix.trace (Ψ * Ψᴴ) = 1)
    (hChannel : ∀ ρ : Matrix QuantumProver.ElegantJointMeasurement.Teleportation.SystemIndex QuantumProver.ElegantJointMeasurement.Teleportation.SystemIndex ℂ,
      ρ.PosSemidef → Matrix.trace ρ = 1 →
      matrixVaryingSharedResourceChannel ea eb P z Ψ ρ =
        QuantumProver.ElegantJointMeasurement.Teleportation.physicalClassicalChannel ρ) :
    (matrixCodeMatrix ea eb Ψ)ᴴ * (∑ j, terminalEffects P z j) * matrixCodeMatrix ea eb Ψ =
      (matrixCodeMatrix ea eb Ψ)ᴴ * matrixCodeMatrix ea eb Ψ := by
  have hc := matrix_density_exactness_implies_compressed_effects ea eb P z Ψ hChannel
  rw [Matrix.mul_sum, Matrix.sum_mul]
  simp_rw [hc]
  rw [QuantumProver.ElegantJointMeasurement.Teleportation.ejm_complete, matrixCodeMatrix_gram ea eb Ψ hΨ]

theorem matrix_varying_workspace_promised_code_entropy_ge_one {m n : ℕ}
    (Ψ : Matrix κ κ ℂ) (hΨ : Matrix.trace (Ψ * Ψᴴ) = 1)
    (ea : (Fin 2 × κ) ≃ Fin m) (eb : (Fin 2 × κ) ≃ Fin n)
    (P : MatrixMachine S) (z : S m n) (bA : Fin m) (bB : Fin n)
    (hChannel : ∀ ρ : Matrix QuantumProver.ElegantJointMeasurement.Teleportation.SystemIndex QuantumProver.ElegantJointMeasurement.Teleportation.SystemIndex ℂ,
      ρ.PosSemidef → Matrix.trace ρ = 1 →
      matrixVaryingSharedResourceChannel ea eb P z Ψ ρ =
        QuantumProver.ElegantJointMeasurement.Teleportation.physicalClassicalChannel ρ) :
    1 ≤ QuantumProver.ElegantJointMeasurement.TailReference.vonNeumannEntropyBits (Ψ * Ψᴴ) := by
  have hcode := matrix_density_exactness_implies_code_completeness ea eb P z Ψ hΨ hChannel
  obtain ⟨G, hGpositive, hGsum, hGclosure, hGcode⟩ :=
    exists_complete_closure_extension_on_code ea eb P z bA bB 0
      (matrixCodeMatrix ea eb Ψ) hcode
  have hc := matrix_density_exactness_implies_compressed_effects ea eb P z Ψ hChannel
  have hGc : ∀ j, (codeMatrix (a := Fin 2) (b := Fin 2) Ψ)ᴴ *
      QuantumProver.ElegantJointMeasurement.ProtocolEffects.pullbackEffect ea eb (G j) * codeMatrix (a := Fin 2) (b := Fin 2) Ψ =
        QuantumProver.ElegantJointMeasurement.Teleportation.represented_physicalEffect j := by
    intro j
    rw [← matrixCodeMatrix_compression]
    exact (hGcode j).trans (hc j)
  have hresource := (QuantumProver.ElegantJointMeasurement.Teleportation.Tomography.resourceChannel_exact_iff_compressed
    (codeMatrix (a := Fin 2) (b := Fin 2) Ψ)
    (fun j => QuantumProver.ElegantJointMeasurement.ProtocolEffects.pullbackEffect ea eb (G j))
    QuantumProver.ElegantJointMeasurement.Teleportation.represented_physicalEffect).mpr (funext hGc)
  apply QuantumProver.ElegantJointMeasurement.FiniteTreeCostModel.entropy_ge_one_of_density_channel_effect_closure Ψ hΨ ea eb
    (fun j => QuantumProver.ElegantJointMeasurement.ProtocolEffects.pullbackEffect ea eb (G j)) hGclosure
  intro ρ hρ ht
  simpa only [← QuantumProver.ElegantJointMeasurement.Teleportation.Tomography.physicalClassicalChannel_eq_measurement] using
    hresource ρ hρ ht

end
end QuantumProver.ElegantJointMeasurement.EncodedResourceCostModel

namespace QuantumProver.ElegantJointMeasurement.HilbertSquareCostModel

open scoped BigOperators ComplexConjugate ComplexOrder Matrix Topology
open QuantumProver.ElegantJointMeasurement.GeneralResource QuantumProver.ElegantJointMeasurement.HilbertFiniteCostModel

noncomputable section

universe u
variable {κ : Type*} [Fintype κ] [DecidableEq κ]
variable {R : Type u} [MeasurableSpace R] [StandardBorelSpace R] [Nonempty R]
variable {m n : ℕ} [NeZero m] [NeZero n]

def matrixCompletedResourceChannel
    (ea : (Fin 2 × κ) ≃ Fin m) (eb : (Fin 2 × κ) ≃ Fin n)
    (P : QuantumProver.ElegantJointMeasurement.HilbertSquareProcess.SquareProcess m n R)
    (J : QuantumProver.ElegantJointMeasurement.HilbertTranscriptPOVM.Transcript R → Fin 4) (Ψ : Matrix κ κ ℂ)
    (ρ : Matrix QuantumProver.ElegantJointMeasurement.Teleportation.SystemIndex QuantumProver.ElegantJointMeasurement.Teleportation.SystemIndex ℂ) :
    Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) ℂ :=
  QuantumProver.ElegantJointMeasurement.Teleportation.Tomography.resourceMeasurementChannel (matrixCodeMatrix ea eb Ψ)
    (fun j => P.cylinderPOVM.reportedEffect J j) ρ

theorem matrixCompletedResourceChannel_eq_physical
    (ea : (Fin 2 × κ) ≃ Fin m) (eb : (Fin 2 × κ) ≃ Fin n)
    (P : QuantumProver.ElegantJointMeasurement.HilbertSquareProcess.SquareProcess m n R)
    (J : QuantumProver.ElegantJointMeasurement.HilbertTranscriptPOVM.Transcript R → Fin 4) (Ψ : Matrix κ κ ℂ)
    (ρ : Matrix QuantumProver.ElegantJointMeasurement.Teleportation.SystemIndex QuantumProver.ElegantJointMeasurement.Teleportation.SystemIndex ℂ) :
    matrixCompletedResourceChannel ea eb P J Ψ ρ =
      QuantumProver.ElegantJointMeasurement.Teleportation.Tomography.resourceMeasurementChannel (codeMatrix Ψ)
        (fun j => QuantumProver.ElegantJointMeasurement.ProtocolEffects.pullbackEffect ea eb
          (P.cylinderPOVM.reportedEffect J j)) ρ := by
  change QuantumProver.ElegantJointMeasurement.Teleportation.Tomography.resourceMeasurementChannel
      ((codeMatrix (a := Fin 2) (b := Fin 2) Ψ).submatrix
        (ea.prodCongr eb).symm id)
      (fun j => P.cylinderPOVM.reportedEffect J j) ρ =
    QuantumProver.ElegantJointMeasurement.Teleportation.Tomography.resourceMeasurementChannel
      (codeMatrix (a := Fin 2) (b := Fin 2) Ψ)
      (fun j => (P.cylinderPOVM.reportedEffect J j).submatrix
        (ea.prodCongr eb) (ea.prodCongr eb)) ρ
  exact QuantumProver.ElegantJointMeasurement.Teleportation.InitialBasisTransport.resourceChannel_reindex
    (ea.prodCongr eb) (codeMatrix (a := Fin 2) (b := Fin 2) Ψ)
    (fun j => P.cylinderPOVM.reportedEffect J j) ρ

theorem completed_matrix_effects_mem_finiteTreeEffectSet_closure
    (ea : (Fin 2 × κ) ≃ Fin m) (eb : (Fin 2 × κ) ≃ Fin n)
    (P : QuantumProver.ElegantJointMeasurement.HilbertSquareProcess.SquareProcess m n R)
    (J : QuantumProver.ElegantJointMeasurement.HilbertTranscriptPOVM.Transcript R → Fin 4)
    (hJ : MeasureTheory.NullMeasurable J P.cylinderPOVM.faithfulMeasure) :
    (fun j => QuantumProver.ElegantJointMeasurement.ProtocolEffects.pullbackEffect ea eb
      (P.cylinderPOVM.reportedEffect J j)) ∈
      closure (QuantumProver.ElegantJointMeasurement.TailReference.finiteTreeEffectSet ea eb) := by
  obtain ⟨T, report, hlim⟩ := P.exists_actual_completed_report_finite_tree_sequence J hJ
  exact QuantumProver.ElegantJointMeasurement.TailReference.finiteTreeEffectSet_mem_closure_of_tendsto ea eb T report _
    (QuantumProver.ElegantJointMeasurement.CompactProtocolEffects.matrix_effect_sequence_pulled_back T report ea eb _ hlim)

theorem completed_matrix_square_entropy_ge_one
    (Ψ : Matrix κ κ ℂ) (hΨ : Matrix.trace (Ψ * Ψᴴ) = 1)
    (ea : (Fin 2 × κ) ≃ Fin m) (eb : (Fin 2 × κ) ≃ Fin n)
    (P : QuantumProver.ElegantJointMeasurement.HilbertSquareProcess.SquareProcess m n R)
    (J : QuantumProver.ElegantJointMeasurement.HilbertTranscriptPOVM.Transcript R → Fin 4)
    (hJ : MeasureTheory.NullMeasurable J P.cylinderPOVM.faithfulMeasure)
    (hChannel : ∀ ρ : Matrix QuantumProver.ElegantJointMeasurement.Teleportation.SystemIndex QuantumProver.ElegantJointMeasurement.Teleportation.SystemIndex ℂ,
      ρ.PosSemidef → Matrix.trace ρ = 1 →
      matrixCompletedResourceChannel ea eb P J Ψ ρ =
        QuantumProver.ElegantJointMeasurement.Teleportation.physicalClassicalChannel ρ) :
    1 ≤ QuantumProver.ElegantJointMeasurement.TailReference.vonNeumannEntropyBits (Ψ * Ψᴴ) := by
  apply QuantumProver.ElegantJointMeasurement.FiniteTreeCostModel.entropy_ge_one_of_density_channel_effect_closure
    Ψ hΨ ea eb (fun j => QuantumProver.ElegantJointMeasurement.ProtocolEffects.pullbackEffect ea eb
      (P.cylinderPOVM.reportedEffect J j))
    (completed_matrix_effects_mem_finiteTreeEffectSet_closure ea eb P J hJ)
  intro ρ hρ ht
  rw [← matrixCompletedResourceChannel_eq_physical ea eb P J Ψ ρ]
  exact hChannel ρ hρ ht

end
end QuantumProver.ElegantJointMeasurement.HilbertSquareCostModel

namespace QuantumProver.ElegantJointMeasurement.HilbertSquareCostModel

open scoped BigOperators ComplexConjugate ComplexOrder Matrix Topology
open QuantumProver.ElegantJointMeasurement.GeneralResource QuantumProver.ElegantJointMeasurement.HilbertFiniteCostModel

noncomputable section

universe u
variable {κ : Type*} [Fintype κ] [DecidableEq κ]
variable {R : Type u} [MeasurableSpace R] [StandardBorelSpace R] [Nonempty R]
variable {m n : ℕ} [NeZero m] [NeZero n]

theorem completed_matrix_square_density_limit_entropy_ge_one
    (Ψ : Matrix κ κ ℂ) (hΨ : Matrix.trace (Ψ * Ψᴴ) = 1)
    (ea : (Fin 2 × κ) ≃ Fin m) (eb : (Fin 2 × κ) ≃ Fin n)
    (P : ℕ → QuantumProver.ElegantJointMeasurement.HilbertSquareProcess.SquareProcess m n R)
    (J : ℕ → QuantumProver.ElegantJointMeasurement.HilbertTranscriptPOVM.Transcript R → Fin 4)
    (hJ : ∀ a, MeasureTheory.NullMeasurable (J a) (P a).cylinderPOVM.faithfulMeasure)
    (hChannel : ∀ ρ : Matrix QuantumProver.ElegantJointMeasurement.Teleportation.SystemIndex QuantumProver.ElegantJointMeasurement.Teleportation.SystemIndex ℂ,
      ρ.PosSemidef → Matrix.trace ρ = 1 →
      Filter.Tendsto (fun a => matrixCompletedResourceChannel ea eb (P a) (J a) Ψ ρ)
        Filter.atTop (nhds (QuantumProver.ElegantJointMeasurement.Teleportation.physicalClassicalChannel ρ))) :
    1 ≤ QuantumProver.ElegantJointMeasurement.TailReference.vonNeumannEntropyBits (Ψ * Ψᴴ) := by
  classical
  letI : NormedAddCommGroup
      (Fin 4 → Matrix (QuantumProver.ElegantJointMeasurement.Augmented.Index κ) (QuantumProver.ElegantJointMeasurement.Augmented.Index κ) ℂ) :=
    inferInstanceAs (NormedAddCommGroup
      (Fin 4 → QuantumProver.ElegantJointMeasurement.Augmented.Index κ → QuantumProver.ElegantJointMeasurement.Augmented.Index κ → ℂ))
  let F : ℕ → Fin 4 → Matrix (QuantumProver.ElegantJointMeasurement.Augmented.Index κ) (QuantumProver.ElegantJointMeasurement.Augmented.Index κ) ℂ :=
    fun a j => QuantumProver.ElegantJointMeasurement.ProtocolEffects.pullbackEffect ea eb
      ((P a).cylinderPOVM.reportedEffect (J a) j)
  have hF : ∀ a, F a ∈ closure (QuantumProver.ElegantJointMeasurement.TailReference.finiteTreeEffectSet ea eb) :=
    fun a => completed_matrix_effects_mem_finiteTreeEffectSet_closure ea eb (P a) (J a) (hJ a)
  have hApprox : ∀ a : ℕ, ∃ G ∈ QuantumProver.ElegantJointMeasurement.TailReference.finiteTreeEffectSet ea eb,
      dist (F a) G < 1 / ((a : ℝ) + 1) := by
    intro a
    exact Metric.mem_closure_iff.mp (hF a) _ (by positivity)
  choose G hG hdist using hApprox
  have hDelta : Filter.Tendsto (fun a => G a - F a) Filter.atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    apply squeeze_zero (fun _ => norm_nonneg _) _ tendsto_one_div_add_atTop_nhds_zero_nat
    intro a
    rw [← dist_eq_norm, dist_comm]
    exact (hdist a).le
  change ∀ a, ∃ (T : QuantumProver.ElegantJointMeasurement.Concurrence.FiniteLocalKrausTree m n)
    (report : Fin T.terminalBraPairs.length → Fin 4),
    G a = fun j => QuantumProver.ElegantJointMeasurement.ProtocolEffects.groupedEffect T ea eb report j at hG
  choose T report hEq using hG
  apply QuantumProver.ElegantJointMeasurement.FiniteTreeCostModel.entropy_ge_one_of_density_channel_limit Ψ hΨ T ea eb report
  intro ρ hρ ht
  let L : (Fin 4 → Matrix (QuantumProver.ElegantJointMeasurement.Augmented.Index κ) (QuantumProver.ElegantJointMeasurement.Augmented.Index κ) ℂ) →
      Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) ℂ :=
    fun H => QuantumProver.ElegantJointMeasurement.Teleportation.Tomography.resourceMeasurementChannel (codeMatrix Ψ) H ρ
  have hContinuous : Continuous L := by
    unfold L QuantumProver.ElegantJointMeasurement.Teleportation.Tomography.resourceMeasurementChannel
    fun_prop
  have hZero : L 0 = 0 := by
    simp [L, QuantumProver.ElegantJointMeasurement.Teleportation.Tomography.resourceMeasurementChannel]
  have hSub : ∀ A B, L (A - B) = L A - L B := by
    intro A B
    simp only [L, QuantumProver.ElegantJointMeasurement.Teleportation.Tomography.resourceMeasurementChannel,
      Pi.sub_apply, Matrix.sub_mul, Matrix.trace_sub, sub_smul, Finset.sum_sub_distrib]
  have hDifference : Filter.Tendsto (fun a => L (G a) - L (F a))
      Filter.atTop (nhds 0) := by
    have h := (hContinuous.tendsto 0).comp hDelta
    simpa only [Function.comp_def, hZero, hSub] using h
  have hPhysical : Filter.Tendsto (fun a => L (F a)) Filter.atTop
      (nhds (QuantumProver.ElegantJointMeasurement.Teleportation.physicalClassicalChannel ρ)) := by
    simpa only [matrixCompletedResourceChannel_eq_physical, L, F] using hChannel ρ hρ ht
  have hActual : Filter.Tendsto (fun a => L (G a)) Filter.atTop
      (nhds (QuantumProver.ElegantJointMeasurement.Teleportation.physicalClassicalChannel ρ)) := by
    simpa only [sub_add_cancel, zero_add] using hDifference.add hPhysical
  simpa only [hEq, L] using hActual

end
end QuantumProver.ElegantJointMeasurement.HilbertSquareCostModel

set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix
open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder

namespace QuantumProver.ElegantJointMeasurement.PreparedReports

open scoped NNReal

variable {I Q R S : Type*} [Fintype I] [Fintype Q]
  [DecidableEq I] [DecidableEq Q] [Nonempty Q]
  [MeasurableSpace R] [StandardBorelSpace R] [Nonempty R]
  [MeasurableSpace S] [StandardBorelSpace S] [Nonempty S]

open QuantumProver.ElegantJointMeasurement.HilbertTranscriptPOVM QuantumProver.ElegantJointMeasurement.ClosureJoin.RecordTransport

theorem trace_mul_psd_nonneg {X : Type*} [Fintype X] [DecidableEq X]
    (A B : Matrix X X ℂ) (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ (A * B).trace := by
  have hs : (CFC.sqrt B)ᴴ = CFC.sqrt B :=
    (CFC.sqrt_nonneg B).posSemidef.isHermitian
  have hT := hA.mul_mul_conjTranspose_same (CFC.sqrt B)
  have he : (CFC.sqrt B * A * (CFC.sqrt B)ᴴ).trace = (A * B).trace := by
    rw [hs, Matrix.trace_mul_cycle, CFC.sqrt_mul_sqrt_self B hB.nonneg,
      Matrix.trace_mul_comm]
  exact he ▸ hT.trace_nonneg

theorem trace_mul_psd_re_cast {X : Type*} [Fintype X] [DecidableEq X]
    (A B : Matrix X X ℂ) (hA : A.PosSemidef) (hB : B.PosSemidef) :
    (((A * B).trace.re : ℝ) : ℂ) = (A * B).trace := by
  apply Complex.ext
  · simp
  · simpa only [Complex.ofReal_im] using
      (Complex.nonneg_iff.mp (trace_mul_psd_nonneg A B hA hB)).2

def preparedRawReport (D : ConsistentCylinderPOVM R Q) (V : Matrix Q I ℂ)
    (J : Transcript R → Fin 4)
    (hJ : NullMeasurable J (D.fullBornMeasure (preparedReference V)
      (preparedReference_positive V))) : Transcript R → Fin 4 :=
  referenceRawReport D (preparedReference V) (preparedReference_positive V) J hJ

theorem preparedRawReport_measurable (D : ConsistentCylinderPOVM R Q)
    (V : Matrix Q I ℂ) (J : Transcript R → Fin 4)
    (hJ : NullMeasurable J (D.fullBornMeasure (preparedReference V)
      (preparedReference_positive V))) :
    Measurable (preparedRawReport D V J hJ) :=
  referenceRawReport_measurable D _ _ J hJ

theorem preparedRawReport_probability
    (C : ConsistentCylinderPOVM S Q) (D : ConsistentCylinderPOVM R Q)
    (g : S → R) (hg : Measurable g)
    (hC : ∀ n B, MeasurableSet B →
      C.effect n ((mapPrefixRecord g n) ⁻¹' B) = D.effect n B)
    (V : Matrix Q I ℂ) (J : Transcript R → Fin 4)
    (hJ : NullMeasurable J (D.fullBornMeasure (preparedReference V)
      (preparedReference_positive V)))
    (sigma : Matrix I I ℂ) (hs : sigma.PosSemidef) (ht : sigma.trace = 1)
    (j : Fin 4) :
    C.fullBornMeasure (V * sigma * Vᴴ) (hs.mul_mul_conjTranspose_same V)
        {omega | preparedRawReport D V J hJ (mapRecord g omega) = j} =
      D.fullBornMeasure (V * sigma * Vᴴ) (hs.mul_mul_conjTranspose_same V)
        {omega | J omega = j} := by
  classical
  letI : Nonempty I := by
    by_contra hn
    letI : IsEmpty I := not_nonempty_iff.mp hn
    have hz : sigma.trace = 0 := by simp [Matrix.trace]
    exact zero_ne_one (hz.symm.trans ht)
  let rho := V * sigma * Vᴴ
  have hr : rho.PosSemidef := hs.mul_mul_conjTranspose_same V
  let J0 := preparedRawReport D V J hJ
  have hm : Measurable J0 := preparedRawReport_measurable D V J hJ
  have hd : (((Fintype.card I : ℝ≥0) : ℂ) • preparedReference V - rho).PosSemidef := by
    simpa [rho] using prepared_density_cap V sigma hs ht
  have ha := referenceRawReport_ae_all_dominated D (Fintype.card I : ℝ≥0)
    (preparedReference V) rho (preparedReference_positive V) hr hd J hJ
  change J =ᵐ[D.fullBornMeasure rho hr] J0 at ha
  have hevent : D.fullBornMeasure rho hr {omega | J0 omega = j} =
      D.fullBornMeasure rho hr {omega | J omega = j} := by
    apply measure_congr
    filter_upwards [ha] with omega ho
    simp only [Set.mem_setOf_eq, ho]
  have hB : MeasurableSet {omega : Transcript R | J0 omega = j} :=
    measurableSet_eq_fun hm measurable_const
  change C.fullBornMeasure rho hr {omega | J0 (mapRecord g omega) = j} = _
  calc
    _ = D.fullBornMeasure rho hr {omega | J0 omega = j} := by
      rw [← fullBornMeasure_mapRecord C D g hg hC rho hr,
        Measure.map_apply (measurable_mapRecord g hg) hB]
      rfl
    _ = _ := hevent

theorem resource_channel_of_prepared_report
    (C : ConsistentCylinderPOVM S Q) (D : ConsistentCylinderPOVM R Q)
    (g : S → R) (hg : Measurable g)
    (hC : ∀ n B, MeasurableSet B →
      C.effect n ((mapPrefixRecord g n) ⁻¹' B) = D.effect n B)
    (V : Matrix Q I ℂ) (J : Transcript R → Fin 4)
    (hJ : NullMeasurable J (D.fullBornMeasure (preparedReference V)
      (preparedReference_positive V)))
    (E : Fin 4 → Matrix I I ℂ) (hE : ∀ j, (E j).PosSemidef)
    (hTarget : ∀ sigma : Matrix I I ℂ, ∀ hs : sigma.PosSemidef,
      sigma.trace = 1 → ∀ j,
        D.fullBornMeasure (V * sigma * Vᴴ) (hs.mul_mul_conjTranspose_same V)
          {omega | J omega = j} = ENNReal.ofReal ((E j * sigma).trace.re))
    (sigma : Matrix I I ℂ) (hs : sigma.PosSemidef) (ht : sigma.trace = 1) :
    QuantumProver.ElegantJointMeasurement.Teleportation.Tomography.resourceMeasurementChannel V
        (fun j => C.reportedEffect (preparedRawReport D V J hJ ∘ mapRecord g) j) sigma =
      QuantumProver.ElegantJointMeasurement.Teleportation.Tomography.measurementChannel E sigma := by
  let K := preparedRawReport D V J hJ ∘ mapRecord g
  have hm : Measurable K :=
    (preparedRawReport_measurable D V J hJ).comp (measurable_mapRecord g hg)
  have hr : (V * sigma * Vᴴ).PosSemidef := hs.mul_mul_conjTranspose_same V
  have hp (j : Fin 4) :
      ENNReal.ofReal ((C.reportedEffect K j * (V * sigma * Vᴴ)).trace.re) =
        ENNReal.ofReal ((E j * sigma).trace.re) := by
    have hprob := (preparedRawReport_probability C D g hg hC V J hJ sigma hs ht j).trans
      (hTarget sigma hs ht j)
    have hB : MeasurableSet {omega : Transcript S | K omega = j} :=
      measurableSet_eq_fun hm measurable_const
    change C.fullBornMeasure (V * sigma * Vᴴ) hr {omega | K omega = j} =
      ENNReal.ofReal ((E j * sigma).trace.re) at hprob
    rw [C.fullBornMeasure_apply _ hr _ hB,
      ← C.reportedEffect_eq_physical K hm j] at hprob
    exact hprob
  have htrace (j : Fin 4) : (C.reportedEffect K j * (V * sigma * Vᴴ)).trace =
      (E j * sigma).trace := by
    have hF := C.reportedEffect_positive K j
    have hnF := (Complex.nonneg_iff.mp
      (trace_mul_psd_nonneg _ _ hF hr)).1
    have hnE := (Complex.nonneg_iff.mp
      (trace_mul_psd_nonneg _ _ (hE j) hs)).1
    have hre := congrArg ENNReal.toReal (hp j)
    have he : (C.reportedEffect K j * (V * sigma * Vᴴ)).trace.re =
        (E j * sigma).trace.re := by
      simpa only [ENNReal.toReal_ofReal hnF, ENNReal.toReal_ofReal hnE] using hre
    rw [← trace_mul_psd_re_cast _ _ hF hr,
      ← trace_mul_psd_re_cast _ _ (hE j) hs]
    exact congrArg (fun t : ℝ => (t : ℂ)) he
  change QuantumProver.ElegantJointMeasurement.Teleportation.Tomography.resourceMeasurementChannel V
      (fun j => C.reportedEffect K j) sigma = _
  simp only [QuantumProver.ElegantJointMeasurement.Teleportation.Tomography.resourceMeasurementChannel,
    QuantumProver.ElegantJointMeasurement.Teleportation.Tomography.measurementChannel, htrace]

end QuantumProver.ElegantJointMeasurement.PreparedReports

namespace QuantumProver.ElegantJointMeasurement.HilbertSquareCostModel
open QuantumProver.ElegantJointMeasurement.GeneralResource QuantumProver.ElegantJointMeasurement.HilbertFiniteCostModel
open QuantumProver.ElegantJointMeasurement.HilbertTranscriptPOVM QuantumProver.ElegantJointMeasurement.ClosureJoin.RecordTransport QuantumProver.ElegantJointMeasurement.PreparedReports

variable {kappa : Type*} [Fintype kappa] [DecidableEq kappa]
variable {m n : ℕ} [NeZero m] [NeZero n]
variable {R S : Type*} [MeasurableSpace R] [MeasurableSpace S]
  [StandardBorelSpace R] [StandardBorelSpace S] [Nonempty R] [Nonempty S]

theorem physical_prepared_report_entropy_ge_one
    (Psi : Matrix kappa kappa ℂ) (hPsi : (Psi * Psiᴴ).trace = 1)
    (ea : (Fin 2 × kappa) ≃ Fin m) (eb : (Fin 2 × kappa) ≃ Fin n)
    (P : QuantumProver.ElegantJointMeasurement.HilbertSquareProcess.SquareProcess m n S)
    (D : ConsistentCylinderPOVM R (Fin m × Fin n))
    (g : S → R) (hg : Measurable g)
    (hCylinder : ∀ l B, MeasurableSet B →
      P.cylinderPOVM.effect l ((mapPrefixRecord g l) ⁻¹' B) = D.effect l B)
    (J : Transcript R → Fin 4)
    (hJ : NullMeasurable J (D.fullBornMeasure
      (preparedReference (matrixCodeMatrix ea eb Psi))
      (preparedReference_positive (matrixCodeMatrix ea eb Psi))))
    (hTarget : ∀ sigma : Matrix QuantumProver.ElegantJointMeasurement.Teleportation.SystemIndex QuantumProver.ElegantJointMeasurement.Teleportation.SystemIndex ℂ,
      ∀ hs : sigma.PosSemidef, sigma.trace = 1 → ∀ j,
        D.fullBornMeasure
          (matrixCodeMatrix ea eb Psi * sigma * (matrixCodeMatrix ea eb Psi)ᴴ)
          (hs.mul_mul_conjTranspose_same (matrixCodeMatrix ea eb Psi))
          {omega | J omega = j} =
            ENNReal.ofReal ((QuantumProver.ElegantJointMeasurement.Teleportation.represented_physicalEffect j * sigma).trace.re)) :
    1 ≤ QuantumProver.ElegantJointMeasurement.TailReference.vonNeumannEntropyBits (Psi * Psiᴴ) := by
  let V := matrixCodeMatrix ea eb Psi
  let K := preparedRawReport D V J hJ ∘ mapRecord g
  have hm : Measurable K :=
    (preparedRawReport_measurable D V J hJ).comp (measurable_mapRecord g hg)
  apply completed_matrix_square_entropy_ge_one Psi hPsi ea eb P K hm.nullMeasurable
  intro sigma hs ht
  have hE (j : Fin 4) : (QuantumProver.ElegantJointMeasurement.Teleportation.represented_physicalEffect j).PosSemidef := by
    have he : QuantumProver.ElegantJointMeasurement.Teleportation.represented_physicalEffect j = Matrix.vecMulVec
        (QuantumProver.ElegantJointMeasurement.Teleportation.flatten (QuantumProver.ElegantJointMeasurement.Teleportation.ejmCoefficient j))
        (star (QuantumProver.ElegantJointMeasurement.Teleportation.flatten (QuantumProver.ElegantJointMeasurement.Teleportation.ejmCoefficient j))) := by
      ext i k
      rfl
    rw [he]
    exact Matrix.posSemidef_vecMulVec_self_star _
  simpa only [matrixCompletedResourceChannel,
    QuantumProver.ElegantJointMeasurement.Teleportation.Tomography.physicalClassicalChannel_eq_measurement] using
      resource_channel_of_prepared_report P.cylinderPOVM D g hg hCylinder V J hJ
        QuantumProver.ElegantJointMeasurement.Teleportation.represented_physicalEffect hE hTarget sigma hs ht

end QuantumProver.ElegantJointMeasurement.HilbertSquareCostModel

set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix
open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder

namespace QuantumProver.ElegantJointMeasurement.HilbertSquareCostModel
open QuantumProver.ElegantJointMeasurement.GeneralResource QuantumProver.ElegantJointMeasurement.HilbertFiniteCostModel QuantumProver.ElegantJointMeasurement.HilbertTranscriptPOVM
open QuantumProver.ElegantJointMeasurement.ClosureJoin.RecordTransport QuantumProver.ElegantJointMeasurement.PreparedReports
open QuantumProver.ElegantJointMeasurement.HilbertSquareProcess.RawInstrumentProcess

variable {kappa : Type*} [Fintype kappa] [DecidableEq kappa]
variable {m n : Nat} [NeZero m] [NeZero n]
variable {R : Type*} [MeasurableSpace R] [StandardBorelSpace R] [Nonempty R]

theorem physical_matrix_instrument_entropy_ge_one
    (Psi : Matrix kappa kappa Complex) (hPsi : (Psi * Psiᴴ).trace = 1)
    (ea : (Fin 2 × kappa) ≃ Fin m) (eb : (Fin 2 × kappa) ≃ Fin n)
    (P : MatrixProcess m n R)
    (J : Transcript R → Fin 4)
    (hJ : NullMeasurable J (P.represented_physicalCylinderPOVM.fullBornMeasure
      (preparedReference (matrixCodeMatrix ea eb Psi))
      (preparedReference_positive (matrixCodeMatrix ea eb Psi))))
    (hTarget : ∀ sigma : Matrix QuantumProver.ElegantJointMeasurement.Teleportation.SystemIndex
        QuantumProver.ElegantJointMeasurement.Teleportation.SystemIndex Complex, ∀ hs : sigma.PosSemidef,
      sigma.trace = 1 → ∀ j,
        P.represented_physicalCylinderPOVM.fullBornMeasure
          (matrixCodeMatrix ea eb Psi * sigma * (matrixCodeMatrix ea eb Psi)ᴴ)
          (hs.mul_mul_conjTranspose_same (matrixCodeMatrix ea eb Psi))
          {omega | J omega = j} =
            ENNReal.ofReal ((QuantumProver.ElegantJointMeasurement.Teleportation.represented_physicalEffect j * sigma).trace.re)) :
    1 ≤ QuantumProver.ElegantJointMeasurement.TailReference.vonNeumannEntropyBits (Psi * Psiᴴ) := by
  let g : FineRecord m n R → R := Prod.fst
  have hg : Measurable g := measurable_fst
  have hCylinder : ∀ l B, MeasurableSet B →
      P.compiledSquare.cylinderPOVM.effect l ((mapPrefixRecord g l) ⁻¹' B) =
        P.represented_physicalCylinderPOVM.effect l B := by
    intro l B hB
    have hPrefix : mapPrefixRecord g l = coarseHistory (l + 1) := rfl
    change P.compiledSquare.cylinderEffect l ((mapPrefixRecord g l) ⁻¹' B) =
      P.represented_physicalCylinderEffect l B
    rw [hPrefix]
    exact (P.physicalCylinderEffect_eq_compiled l B hB).symm
  exact physical_prepared_report_entropy_ge_one Psi hPsi ea eb
    P.compiledSquare P.represented_physicalCylinderPOVM g hg hCylinder J hJ hTarget

end QuantumProver.ElegantJointMeasurement.HilbertSquareCostModel

set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix
open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder Topology

namespace QuantumProver.ElegantJointMeasurement.PreparedReports

variable {I Q R S : Type*} [Fintype I] [Fintype Q]
  [DecidableEq I] [DecidableEq Q] [Nonempty Q]
  [MeasurableSpace R] [StandardBorelSpace R] [Nonempty R]
  [MeasurableSpace S] [StandardBorelSpace S] [Nonempty S]

open QuantumProver.ElegantJointMeasurement.HilbertTranscriptPOVM QuantumProver.ElegantJointMeasurement.ClosureJoin.RecordTransport

def physicalReportDensityOutput (D : ConsistentCylinderPOVM R Q)
    (rho : Matrix Q Q ℂ) (hr : rho.PosSemidef) (J : Transcript R → Fin 4) :
    Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) ℂ :=
  ∑ j : Fin 4, (((D.fullBornMeasure rho hr {omega | J omega = j}).toReal : ℝ) : ℂ) •
    QuantumProver.ElegantJointMeasurement.Teleportation.Tomography.sharedProjector j

theorem resource_channel_eq_physical_report_output
    (C : ConsistentCylinderPOVM S Q) (D : ConsistentCylinderPOVM R Q)
    (g : S → R) (hg : Measurable g)
    (hC : ∀ n B, MeasurableSet B →
      C.effect n ((mapPrefixRecord g n) ⁻¹' B) = D.effect n B)
    (V : Matrix Q I ℂ) (J : Transcript R → Fin 4)
    (hJ : NullMeasurable J (D.fullBornMeasure (preparedReference V)
      (preparedReference_positive V)))
    (sigma : Matrix I I ℂ) (hs : sigma.PosSemidef) (ht : sigma.trace = 1) :
    QuantumProver.ElegantJointMeasurement.Teleportation.Tomography.resourceMeasurementChannel V
        (fun j => C.reportedEffect (preparedRawReport D V J hJ ∘ mapRecord g) j) sigma =
      physicalReportDensityOutput D (V * sigma * Vᴴ)
        (hs.mul_mul_conjTranspose_same V) J := by
  let rho := V * sigma * Vᴴ
  have hr : rho.PosSemidef := hs.mul_mul_conjTranspose_same V
  let K := preparedRawReport D V J hJ ∘ mapRecord g
  have hm : Measurable K :=
    (preparedRawReport_measurable D V J hJ).comp (measurable_mapRecord g hg)
  change (∑ j : Fin 4, (C.reportedEffect K j * rho).trace •
      QuantumProver.ElegantJointMeasurement.Teleportation.Tomography.sharedProjector j) =
    ∑ j : Fin 4, (((D.fullBornMeasure rho hr {omega | J omega = j}).toReal : ℝ) : ℂ) •
      QuantumProver.ElegantJointMeasurement.Teleportation.Tomography.sharedProjector j
  apply Finset.sum_congr rfl
  intro j _
  have hF := C.reportedEffect_positive K j
  have hn := (Complex.nonneg_iff.mp (trace_mul_psd_nonneg _ _ hF hr)).1
  have hp := preparedRawReport_probability C D g hg hC V J hJ sigma hs ht j
  have hB : MeasurableSet {omega : Transcript S | K omega = j} :=
    measurableSet_eq_fun hm measurable_const
  change C.fullBornMeasure rho hr {omega | K omega = j} =
    D.fullBornMeasure rho hr {omega | J omega = j} at hp
  rw [C.fullBornMeasure_apply _ hr _ hB,
    ← C.reportedEffect_eq_physical K hm j] at hp
  have hpR := congrArg ENNReal.toReal hp
  change (ENNReal.ofReal ((C.reportedEffect K j * rho).trace.re)).toReal =
    (D.fullBornMeasure rho hr {omega | J omega = j}).toReal at hpR
  have hRe : (C.reportedEffect K j * rho).trace.re =
      (D.fullBornMeasure rho hr {omega | J omega = j}).toReal := by
    simpa only [ENNReal.toReal_ofReal hn] using hpR
  rw [← trace_mul_psd_re_cast _ _ hF hr, hRe]

end QuantumProver.ElegantJointMeasurement.PreparedReports

namespace QuantumProver.ElegantJointMeasurement.HilbertSquareCostModel
open QuantumProver.ElegantJointMeasurement.GeneralResource QuantumProver.ElegantJointMeasurement.HilbertFiniteCostModel QuantumProver.ElegantJointMeasurement.HilbertTranscriptPOVM
open QuantumProver.ElegantJointMeasurement.ClosureJoin.RecordTransport QuantumProver.ElegantJointMeasurement.PreparedReports
open QuantumProver.ElegantJointMeasurement.HilbertSquareProcess.RawInstrumentProcess

variable {kappa : Type*} [Fintype kappa] [DecidableEq kappa]
variable {m n : Nat} [NeZero m] [NeZero n]
variable {R : Type*} [MeasurableSpace R] [StandardBorelSpace R] [Nonempty R]

def physicalMatrixResourceDensityOutput
    (ea : (Fin 2 × kappa) ≃ Fin m) (eb : (Fin 2 × kappa) ≃ Fin n)
    (P : MatrixProcess m n R) (J : Transcript R → Fin 4)
    (Psi : Matrix kappa kappa ℂ)
    (sigma : Matrix QuantumProver.ElegantJointMeasurement.Teleportation.SystemIndex QuantumProver.ElegantJointMeasurement.Teleportation.SystemIndex ℂ)
    (hs : sigma.PosSemidef) : Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) ℂ :=
  physicalReportDensityOutput P.represented_physicalCylinderPOVM
    (matrixCodeMatrix ea eb Psi * sigma * (matrixCodeMatrix ea eb Psi)ᴴ)
    (hs.mul_mul_conjTranspose_same (matrixCodeMatrix ea eb Psi)) J

theorem physical_cylinder_eq_compiled_pullback (P : MatrixProcess m n R) :
    ∀ l B, MeasurableSet B →
      P.compiledSquare.cylinderPOVM.effect l ((mapPrefixRecord (Prod.fst : FineRecord m n R → R) l) ⁻¹' B) =
        P.represented_physicalCylinderPOVM.effect l B := by
  intro l B hB
  have hPrefix : mapPrefixRecord (Prod.fst : FineRecord m n R → R) l =
      coarseHistory (l + 1) := rfl
  change P.compiledSquare.cylinderEffect l
    ((mapPrefixRecord (Prod.fst : FineRecord m n R → R) l) ⁻¹' B) =
      P.represented_physicalCylinderEffect l B
  rw [hPrefix]
  exact (P.physicalCylinderEffect_eq_compiled l B hB).symm

theorem physicalMatrixResourceDensityOutput_eq_compiled
    (ea : (Fin 2 × kappa) ≃ Fin m) (eb : (Fin 2 × kappa) ≃ Fin n)
    (P : MatrixProcess m n R) (J : Transcript R → Fin 4)
    (Psi : Matrix kappa kappa ℂ)
    (hJ : NullMeasurable J (P.represented_physicalCylinderPOVM.fullBornMeasure
      (preparedReference (matrixCodeMatrix ea eb Psi))
      (preparedReference_positive (matrixCodeMatrix ea eb Psi))))
    (sigma : Matrix QuantumProver.ElegantJointMeasurement.Teleportation.SystemIndex QuantumProver.ElegantJointMeasurement.Teleportation.SystemIndex ℂ)
    (hs : sigma.PosSemidef) (ht : sigma.trace = 1) :
    physicalMatrixResourceDensityOutput ea eb P J Psi sigma hs =
      matrixCompletedResourceChannel ea eb P.compiledSquare
        (preparedRawReport P.represented_physicalCylinderPOVM (matrixCodeMatrix ea eb Psi) J hJ ∘
          mapRecord (Prod.fst : FineRecord m n R → R)) Psi sigma := by
  exact (resource_channel_eq_physical_report_output P.compiledSquare.cylinderPOVM
    P.represented_physicalCylinderPOVM Prod.fst measurable_fst
    (physical_cylinder_eq_compiled_pullback P)
    (matrixCodeMatrix ea eb Psi) J hJ sigma hs ht).symm

theorem physical_matrix_instrument_density_limit_entropy_ge_one
    (Psi : Matrix kappa kappa ℂ) (hPsi : (Psi * Psiᴴ).trace = 1)
    (ea : (Fin 2 × kappa) ≃ Fin m) (eb : (Fin 2 × kappa) ≃ Fin n)
    (P : ℕ → MatrixProcess m n R) (J : ℕ → Transcript R → Fin 4)
    (hJ : ∀ a, NullMeasurable (J a) ((P a).represented_physicalCylinderPOVM.fullBornMeasure
      (preparedReference (matrixCodeMatrix ea eb Psi))
      (preparedReference_positive (matrixCodeMatrix ea eb Psi))))
    (hChannel : ∀ sigma : Matrix QuantumProver.ElegantJointMeasurement.Teleportation.SystemIndex QuantumProver.ElegantJointMeasurement.Teleportation.SystemIndex ℂ,
      ∀ hs : sigma.PosSemidef, sigma.trace = 1 →
      Filter.Tendsto (fun a => physicalMatrixResourceDensityOutput ea eb (P a) (J a)
        Psi sigma hs) Filter.atTop (nhds (QuantumProver.ElegantJointMeasurement.Teleportation.physicalClassicalChannel sigma))) :
    1 ≤ QuantumProver.ElegantJointMeasurement.TailReference.vonNeumannEntropyBits (Psi * Psiᴴ) := by
  let K : ℕ → Transcript (FineRecord m n R) → Fin 4 := fun a =>
    preparedRawReport (P a).represented_physicalCylinderPOVM (matrixCodeMatrix ea eb Psi)
      (J a) (hJ a) ∘ mapRecord (Prod.fst : FineRecord m n R → R)
  have hm (a : ℕ) : Measurable (K a) :=
    (preparedRawReport_measurable (P a).represented_physicalCylinderPOVM
      (matrixCodeMatrix ea eb Psi) (J a) (hJ a)).comp
      (measurable_mapRecord Prod.fst measurable_fst)
  apply completed_matrix_square_density_limit_entropy_ge_one Psi hPsi ea eb
    (fun a => (P a).compiledSquare) K (fun a => (hm a).nullMeasurable)
  intro sigma hs ht
  have he (a : ℕ) := physicalMatrixResourceDensityOutput_eq_compiled ea eb (P a)
    (J a) Psi (hJ a) sigma hs ht
  simpa only [he, K] using hChannel sigma hs ht

theorem physical_matrix_instrument_density_entropy_ge_one
    (Psi : Matrix kappa kappa ℂ) (hPsi : (Psi * Psiᴴ).trace = 1)
    (ea : (Fin 2 × kappa) ≃ Fin m) (eb : (Fin 2 × kappa) ≃ Fin n)
    (P : MatrixProcess m n R) (J : Transcript R → Fin 4)
    (hJ : NullMeasurable J (P.represented_physicalCylinderPOVM.fullBornMeasure
      (preparedReference (matrixCodeMatrix ea eb Psi))
      (preparedReference_positive (matrixCodeMatrix ea eb Psi))))
    (hChannel : ∀ sigma : Matrix QuantumProver.ElegantJointMeasurement.Teleportation.SystemIndex QuantumProver.ElegantJointMeasurement.Teleportation.SystemIndex ℂ,
      ∀ hs : sigma.PosSemidef, sigma.trace = 1 →
      physicalMatrixResourceDensityOutput ea eb P J Psi sigma hs =
        QuantumProver.ElegantJointMeasurement.Teleportation.physicalClassicalChannel sigma) :
    1 ≤ QuantumProver.ElegantJointMeasurement.TailReference.vonNeumannEntropyBits (Psi * Psiᴴ) := by
  apply physical_matrix_instrument_density_limit_entropy_ge_one Psi hPsi ea eb
    (fun _ => P) (fun _ => J) (fun _ => hJ)
  intro sigma hs ht
  simpa only [hChannel sigma hs ht] using
    (tendsto_const_nhds : Filter.Tendsto
      (fun _ : ℕ => QuantumProver.ElegantJointMeasurement.Teleportation.physicalClassicalChannel sigma)
      Filter.atTop (nhds (QuantumProver.ElegantJointMeasurement.Teleportation.physicalClassicalChannel sigma)))

end QuantumProver.ElegantJointMeasurement.HilbertSquareCostModel

namespace QuantumProver.ElegantJointMeasurement.HilbertSquareCostModel
open QuantumProver.ElegantJointMeasurement.GeneralResource QuantumProver.ElegantJointMeasurement.HilbertFiniteCostModel QuantumProver.ElegantJointMeasurement.HilbertTranscriptPOVM
open QuantumProver.ElegantJointMeasurement.ClosureJoin.RecordTransport QuantumProver.ElegantJointMeasurement.PreparedReports
open QuantumProver.ElegantJointMeasurement.HilbertSquareProcess.RawInstrumentProcess
open scoped Topology BigOperators

noncomputable section
variable {κ : Type*} [Fintype κ] [DecidableEq κ]
variable {m n : ℕ} [NeZero m] [NeZero n]
variable {R : ℕ → Type*} [∀ a, MeasurableSpace (R a)]
  [∀ a, StandardBorelSpace (R a)] [∀ a, Nonempty (R a)]

theorem completed_matrix_square_varying_records_density_limit_entropy_ge_one
    (Ψ : Matrix κ κ ℂ) (hΨ : (Ψ * Ψᴴ).trace = 1)
    (ea : (Fin 2 × κ) ≃ Fin m) (eb : (Fin 2 × κ) ≃ Fin n)
    (P : ∀ a : ℕ, QuantumProver.ElegantJointMeasurement.HilbertSquareProcess.SquareProcess m n (R a))
    (J : ∀ a : ℕ, Transcript (R a) → Fin 4)
    (hJ : ∀ a, NullMeasurable (J a) (P a).cylinderPOVM.faithfulMeasure)
    (hChannel : ∀ ρ : Matrix QuantumProver.ElegantJointMeasurement.Teleportation.SystemIndex QuantumProver.ElegantJointMeasurement.Teleportation.SystemIndex ℂ,
      ρ.PosSemidef → ρ.trace = 1 →
      Filter.Tendsto (fun a => matrixCompletedResourceChannel ea eb (P a) (J a) Ψ ρ)
        Filter.atTop (nhds (QuantumProver.ElegantJointMeasurement.Teleportation.physicalClassicalChannel ρ))) :
    1 ≤ QuantumProver.ElegantJointMeasurement.TailReference.vonNeumannEntropyBits (Ψ * Ψᴴ) := by
  classical
  letI : NormedAddCommGroup
      (Fin 4 → Matrix (QuantumProver.ElegantJointMeasurement.Augmented.Index κ) (QuantumProver.ElegantJointMeasurement.Augmented.Index κ) ℂ) :=
    inferInstanceAs (NormedAddCommGroup
      (Fin 4 → QuantumProver.ElegantJointMeasurement.Augmented.Index κ → QuantumProver.ElegantJointMeasurement.Augmented.Index κ → ℂ))
  let F : ℕ → Fin 4 → Matrix (QuantumProver.ElegantJointMeasurement.Augmented.Index κ) (QuantumProver.ElegantJointMeasurement.Augmented.Index κ) ℂ :=
    fun a j => QuantumProver.ElegantJointMeasurement.ProtocolEffects.pullbackEffect ea eb
      ((P a).cylinderPOVM.reportedEffect (J a) j)
  have hF : ∀ a, F a ∈ closure (QuantumProver.ElegantJointMeasurement.TailReference.finiteTreeEffectSet ea eb) :=
    fun a => completed_matrix_effects_mem_finiteTreeEffectSet_closure ea eb (P a) (J a) (hJ a)
  have hApprox : ∀ a : ℕ, ∃ G ∈ QuantumProver.ElegantJointMeasurement.TailReference.finiteTreeEffectSet ea eb,
      dist (F a) G < 1 / ((a : ℝ) + 1) := by
    intro a
    exact Metric.mem_closure_iff.mp (hF a) _ (by positivity)
  choose G hG hdist using hApprox
  have hDelta : Filter.Tendsto (fun a => G a - F a) Filter.atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    apply squeeze_zero (fun _ => norm_nonneg _) _ tendsto_one_div_add_atTop_nhds_zero_nat
    intro a
    rw [← dist_eq_norm, dist_comm]
    exact (hdist a).le
  change ∀ a, ∃ (T : QuantumProver.ElegantJointMeasurement.Concurrence.FiniteLocalKrausTree m n)
    (report : Fin T.terminalBraPairs.length → Fin 4),
    G a = fun j => QuantumProver.ElegantJointMeasurement.ProtocolEffects.groupedEffect T ea eb report j at hG
  choose T report hEq using hG
  apply QuantumProver.ElegantJointMeasurement.FiniteTreeCostModel.entropy_ge_one_of_density_channel_limit Ψ hΨ T ea eb report
  intro ρ hρ ht
  let L : (Fin 4 → Matrix (QuantumProver.ElegantJointMeasurement.Augmented.Index κ) (QuantumProver.ElegantJointMeasurement.Augmented.Index κ) ℂ) →
      Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) ℂ :=
    fun H => QuantumProver.ElegantJointMeasurement.Teleportation.Tomography.resourceMeasurementChannel (codeMatrix Ψ) H ρ
  have hContinuous : Continuous L := by
    unfold L QuantumProver.ElegantJointMeasurement.Teleportation.Tomography.resourceMeasurementChannel
    fun_prop
  have hZero : L 0 = 0 := by
    simp [L, QuantumProver.ElegantJointMeasurement.Teleportation.Tomography.resourceMeasurementChannel]
  have hSub : ∀ A B, L (A - B) = L A - L B := by
    intro A B
    simp only [L, QuantumProver.ElegantJointMeasurement.Teleportation.Tomography.resourceMeasurementChannel,
      Pi.sub_apply, Matrix.sub_mul, Matrix.trace_sub, sub_smul, Finset.sum_sub_distrib]
  have hDifference : Filter.Tendsto (fun a => L (G a) - L (F a))
      Filter.atTop (nhds 0) := by
    have h := (hContinuous.tendsto 0).comp hDelta
    simpa only [Function.comp_def, hZero, hSub] using h
  have hPhysical : Filter.Tendsto (fun a => L (F a)) Filter.atTop
      (nhds (QuantumProver.ElegantJointMeasurement.Teleportation.physicalClassicalChannel ρ)) := by
    simpa only [matrixCompletedResourceChannel_eq_physical, L, F] using hChannel ρ hρ ht
  have hActual : Filter.Tendsto (fun a => L (G a)) Filter.atTop
      (nhds (QuantumProver.ElegantJointMeasurement.Teleportation.physicalClassicalChannel ρ)) := by
    simpa only [sub_add_cancel, zero_add] using hDifference.add hPhysical
  simpa only [hEq, L] using hActual

theorem physical_matrix_instrument_varying_records_density_limit_entropy_ge_one
    (Ψ : Matrix κ κ ℂ) (hΨ : (Ψ * Ψᴴ).trace = 1)
    (ea : (Fin 2 × κ) ≃ Fin m) (eb : (Fin 2 × κ) ≃ Fin n)
    (P : ∀ a : ℕ, MatrixProcess m n (R a))
    (J : ∀ a : ℕ, Transcript (R a) → Fin 4)
    (hJ : ∀ a, NullMeasurable (J a) ((P a).represented_physicalCylinderPOVM.fullBornMeasure
      (preparedReference (matrixCodeMatrix ea eb Ψ))
      (preparedReference_positive (matrixCodeMatrix ea eb Ψ))))
    (hChannel : ∀ ρ : Matrix QuantumProver.ElegantJointMeasurement.Teleportation.SystemIndex QuantumProver.ElegantJointMeasurement.Teleportation.SystemIndex ℂ,
      ∀ hρ : ρ.PosSemidef, ρ.trace = 1 →
      Filter.Tendsto (fun a => physicalMatrixResourceDensityOutput ea eb (P a) (J a)
        Ψ ρ hρ) Filter.atTop (nhds (QuantumProver.ElegantJointMeasurement.Teleportation.physicalClassicalChannel ρ))) :
    1 ≤ QuantumProver.ElegantJointMeasurement.TailReference.vonNeumannEntropyBits (Ψ * Ψᴴ) := by
  let K : ∀ a : ℕ, Transcript (FineRecord m n (R a)) → Fin 4 := fun a =>
    preparedRawReport (P a).represented_physicalCylinderPOVM (matrixCodeMatrix ea eb Ψ)
      (J a) (hJ a) ∘ mapRecord (Prod.fst : FineRecord m n (R a) → R a)
  have hm (a : ℕ) : Measurable (K a) :=
    (preparedRawReport_measurable (P a).represented_physicalCylinderPOVM
      (matrixCodeMatrix ea eb Ψ) (J a) (hJ a)).comp
      (measurable_mapRecord Prod.fst measurable_fst)
  apply completed_matrix_square_varying_records_density_limit_entropy_ge_one Ψ hΨ ea eb
    (fun a => (P a).compiledSquare) K (fun a => (hm a).nullMeasurable)
  intro ρ hρ ht
  have he (a : ℕ) := physicalMatrixResourceDensityOutput_eq_compiled ea eb (P a)
    (J a) Ψ (hJ a) ρ hρ ht
  simpa only [he, K] using hChannel ρ hρ ht

end
end QuantumProver.ElegantJointMeasurement.HilbertSquareCostModel

namespace QuantumProver.ElegantJointMeasurement.HilbertSquareCostModel
open QuantumProver.ElegantJointMeasurement.HilbertFiniteCostModel QuantumProver.ElegantJointMeasurement.HilbertTranscriptPOVM
open QuantumProver.ElegantJointMeasurement.ClosureJoin.RecordTransport QuantumProver.ElegantJointMeasurement.SchmidtResource.SquarePadding
open QuantumProver.ElegantJointMeasurement.HilbertSquareProcess.RawInstrumentProcess

noncomputable section
variable {κ η : Type*} [Fintype κ] [DecidableEq κ] [Fintype η] [DecidableEq η]
variable {m n : ℕ} [NeZero m] [NeZero n]

section Exact
variable {R : Type*} [MeasurableSpace R] [StandardBorelSpace R] [Nonempty R]

theorem rectangular_physical_matrix_instrument_entropy_ge_one
    (Ψ : Matrix κ η ℂ) (hΨ : (Ψ * Ψᴴ).trace = 1)
    (ea : (Fin 2 × (κ ⊕ η)) ≃ Fin m) (eb : (Fin 2 × (κ ⊕ η)) ≃ Fin n)
    (P : MatrixProcess m n R) (J : Transcript R → Fin 4)
    (hJ : NullMeasurable J (P.represented_physicalCylinderPOVM.fullBornMeasure
      (preparedReference (matrixCodeMatrix ea eb (coefficient Ψ)))
      (preparedReference_positive (matrixCodeMatrix ea eb (coefficient Ψ)))))
    (hTarget : ∀ σ : Matrix QuantumProver.ElegantJointMeasurement.Teleportation.SystemIndex QuantumProver.ElegantJointMeasurement.Teleportation.SystemIndex ℂ,
      ∀ hσ : σ.PosSemidef, σ.trace = 1 → ∀ j,
        P.represented_physicalCylinderPOVM.fullBornMeasure
          (matrixCodeMatrix ea eb (coefficient Ψ) * σ *
            (matrixCodeMatrix ea eb (coefficient Ψ))ᴴ)
          (hσ.mul_mul_conjTranspose_same (matrixCodeMatrix ea eb (coefficient Ψ)))
          {ω | J ω = j} = ENNReal.ofReal ((QuantumProver.ElegantJointMeasurement.Teleportation.represented_physicalEffect j * σ).trace.re)) :
    1 ≤ QuantumProver.ElegantJointMeasurement.TailReference.vonNeumannEntropyBits (Ψ * Ψᴴ) := by
  have h := physical_matrix_instrument_entropy_ge_one (coefficient Ψ)
    (normalized_coefficient Ψ hΨ) ea eb P J hJ hTarget
  simpa only [coefficient_entropy] using h

end Exact

section Closure
variable {R : ℕ → Type*} [∀ a, MeasurableSpace (R a)]
  [∀ a, StandardBorelSpace (R a)] [∀ a, Nonempty (R a)]

theorem rectangular_physical_matrix_varying_records_density_limit_entropy_ge_one
    (Ψ : Matrix κ η ℂ) (hΨ : (Ψ * Ψᴴ).trace = 1)
    (ea : (Fin 2 × (κ ⊕ η)) ≃ Fin m) (eb : (Fin 2 × (κ ⊕ η)) ≃ Fin n)
    (P : ∀ a : ℕ, MatrixProcess m n (R a))
    (J : ∀ a : ℕ, Transcript (R a) → Fin 4)
    (hJ : ∀ a, NullMeasurable (J a) ((P a).represented_physicalCylinderPOVM.fullBornMeasure
      (preparedReference (matrixCodeMatrix ea eb (coefficient Ψ)))
      (preparedReference_positive (matrixCodeMatrix ea eb (coefficient Ψ)))))
    (hChannel : ∀ σ : Matrix QuantumProver.ElegantJointMeasurement.Teleportation.SystemIndex QuantumProver.ElegantJointMeasurement.Teleportation.SystemIndex ℂ,
      ∀ hσ : σ.PosSemidef, σ.trace = 1 →
      Filter.Tendsto (fun a => physicalMatrixResourceDensityOutput ea eb (P a) (J a)
        (coefficient Ψ) σ hσ) Filter.atTop (nhds (QuantumProver.ElegantJointMeasurement.Teleportation.physicalClassicalChannel σ))) :
    1 ≤ QuantumProver.ElegantJointMeasurement.TailReference.vonNeumannEntropyBits (Ψ * Ψᴴ) := by
  have h := physical_matrix_instrument_varying_records_density_limit_entropy_ge_one
    (coefficient Ψ) (normalized_coefficient Ψ hΨ) ea eb P J hJ hChannel
  simpa only [coefficient_entropy] using h

end Closure
end
end QuantumProver.ElegantJointMeasurement.HilbertSquareCostModel

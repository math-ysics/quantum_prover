import Mathlib

namespace QuantumProver.AmplitudeDamping.Scalar

open Finset Filter Topology

noncomputable section

def log2 (x : ℝ) : ℝ := Real.log x / Real.log 2

def binaryEntropyBits (x : ℝ) : ℝ := Real.binEntropy x / Real.log 2

def binaryDivergenceBits (p v : ℝ) : ℝ :=
  (-Real.binEntropy v - v * Real.log (1 - p) -
    (1 - v) * Real.log p) / Real.log 2

def binaryDivergenceNats (v z : ℝ) : ℝ :=
  -Real.binEntropy v - v * Real.log z - (1 - v) * Real.log (1 - z)

def typeObjective (p s u v : ℝ) : ℝ :=
  binaryEntropyBits (u * v) - u * binaryEntropyBits v -
    (u / s) * binaryDivergenceBits p v

def typeExponent (p s u v : ℝ) : ℝ :=
  s * Real.binEntropy (u * v) + (1 - s) * u * Real.binEntropy v +
    u * (v * Real.log (1 - p) + (1 - v) * Real.log p)

def binomialTerm (n k : ℕ) (z : ℝ) : ℝ :=
  (n.choose k : ℝ) * z ^ k * (1 - z) ^ (n - k)

def survivorTerm (n w r : ℕ) (p s : ℝ) : ℝ :=
  binomialTerm w r (1 - p) *
    ((n.choose r : ℝ) / (w.choose r : ℝ)) ^ s

def survivorMoment (n w : ℕ) (p s : ℝ) : ℝ :=
  ∑ r ∈ range (w + 1), survivorTerm n w r p s

def optimizingSurvivor (p s : ℝ) : ℝ :=
  1 - p ^ (1 / (1 - s))

def budgetNumerator (p s : ℝ) : ℝ :=
  Real.log (1 - p) - (1 - s) * Real.log (optimizingSurvivor p s)

def renyiLogWeight (p s : ℝ) : ℝ :=
  budgetNumerator p s / s

def scalarBudget (p s : ℝ) : ℝ :=
  log2 (1 + Real.exp (renyiLogWeight p s))

def zCapacityBound (p : ℝ) : ℝ :=
  log2 (1 + (1 - p) * p ^ (p / (1 - p)))

theorem log_two_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)

theorem typeExponent_eq (p s u v : ℝ) (hs : s ≠ 0) :
    typeExponent p s u v = s * Real.log 2 * typeObjective p s u v := by
  unfold typeExponent typeObjective binaryEntropyBits binaryDivergenceBits
  field_simp [hs, ne_of_gt log_two_pos]
  ring

theorem binomialTerm_nonneg (n k : ℕ) {z : ℝ}
    (hz0 : 0 ≤ z) (hz1 : z ≤ 1) : 0 ≤ binomialTerm n k z := by
  unfold binomialTerm
  positivity

theorem sum_binomialTerm (n : ℕ) (z : ℝ) :
    (∑ k ∈ range (n + 1), binomialTerm n k z) = 1 := by
  calc
    _ = (z + (1 - z)) ^ n := by
      rw [add_pow]
      apply sum_congr rfl
      intro k hk
      unfold binomialTerm
      ring
    _ = 1 := by simp

theorem binomialTerm_le_one (n k : ℕ) {z : ℝ}
    (hk : k ≤ n) (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    binomialTerm n k z ≤ 1 := by
  rw [← sum_binomialTerm n z]
  exact single_le_sum (fun i hi => binomialTerm_nonneg n i hz0 hz1)
    (mem_range.mpr (Nat.lt_succ_of_le hk))

theorem survivorMoment_zero (n : ℕ) (p s : ℝ) :
    survivorMoment n 0 p s = 1 := by
  simp [survivorMoment, survivorTerm, binomialTerm]

theorem typeObjective_zero_u (p s v : ℝ) : typeObjective p s 0 v = 0 := by
  simp [typeObjective, binaryEntropyBits]

theorem scalarBudget_nonneg (p s : ℝ) : 0 ≤ scalarBudget p s := by
  unfold scalarBudget log2
  exact div_nonneg (Real.log_nonneg (by linarith [Real.exp_pos (renyiLogWeight p s)]))
    log_two_pos.le

theorem log_choose_le_weighted_logs (n k : ℕ) {z : ℝ}
    (hk : k ≤ n) (hz0 : 0 < z) (hz1 : z < 1) :
    Real.log (n.choose k : ℝ) ≤
      -(k : ℝ) * Real.log z - (n - k : ℕ) * Real.log (1 - z) := by
  have hc : 0 < (n.choose k : ℝ) := by exact_mod_cast Nat.choose_pos hk
  have hz' : 0 < 1 - z := sub_pos.mpr hz1
  have ht : 0 < binomialTerm n k z := by
    unfold binomialTerm
    positivity
  have hl : Real.log (binomialTerm n k z) ≤ 0 := by
    simpa using Real.log_le_log ht (binomialTerm_le_one n k hk hz0.le hz1.le)
  rw [binomialTerm,
    Real.log_mul (mul_pos hc (pow_pos hz0 k)).ne' (pow_pos hz' (n - k)).ne',
    Real.log_mul hc.ne' (pow_pos hz0 k).ne', Real.log_pow, Real.log_pow] at hl
  linarith

theorem log_choose_le_entropy (n k : ℕ) (hk : k ≤ n) :
    Real.log (n.choose k : ℝ) ≤
      (n : ℝ) * Real.binEntropy ((k : ℝ) / n) := by
  by_cases hk0 : k = 0
  · simp [hk0]
  have hn : 0 < n := lt_of_lt_of_le (Nat.pos_of_ne_zero hk0) hk
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  by_cases hkn : k = n
  · simp [hkn, ne_of_gt hnR]
  have hklt : k < n := lt_of_le_of_ne hk hkn
  have hv0 : 0 < (k : ℝ) / n := div_pos (by exact_mod_cast Nat.pos_of_ne_zero hk0) hnR
  have hv1 : (k : ℝ) / n < 1 := (div_lt_one hnR).mpr (by exact_mod_cast hklt)
  have hcast : ((n - k : ℕ) : ℝ) = (n : ℝ) - k := Nat.cast_sub hk
  have he : (n : ℝ) * Real.binEntropy ((k : ℝ) / n) =
      -(k : ℝ) * Real.log ((k : ℝ) / n) -
        (n - k : ℕ) * Real.log (1 - (k : ℝ) / n) := by
    simp only [Real.binEntropy, Real.log_inv, hcast]
    field_simp [ne_of_gt hnR]
    ring
  rw [he]
  exact log_choose_le_weighted_logs n k hk hv0 hv1

theorem choose_le_exp_entropy (n k : ℕ) (hk : k ≤ n) :
    (n.choose k : ℝ) ≤
      Real.exp ((n : ℝ) * Real.binEntropy ((k : ℝ) / n)) :=
  Real.le_exp_of_log_le (log_choose_le_entropy n k hk)

theorem binaryDivergenceNats_nonneg {v z : ℝ} (hv0 : 0 ≤ v) (hv1 : v ≤ 1)
    (hz0 : 0 < z) (hz1 : z < 1) : 0 ≤ binaryDivergenceNats v z := by
  by_cases hvz : v = 0
  · simp only [binaryDivergenceNats, hvz, Real.binEntropy_zero, neg_zero,
      zero_mul, sub_zero, one_mul, sub_self]
    simpa only [zero_sub] using
      neg_nonneg.mpr (Real.log_nonpos (sub_nonneg.mpr hz1.le) (by linarith))
  by_cases hvo : v = 1
  · simp only [binaryDivergenceNats, hvo, Real.binEntropy_one, neg_zero,
      one_mul, sub_self, zero_mul, sub_zero]
    simpa only [zero_sub] using neg_nonneg.mpr (Real.log_nonpos hz0.le hz1.le)
  have hv : 0 < v := lt_of_le_of_ne hv0 (Ne.symm hvz)
  have hv' : 0 < 1 - v := sub_pos.mpr (lt_of_le_of_ne hv1 hvo)
  have hz' : 0 < 1 - z := sub_pos.mpr hz1
  have h0 := mul_le_mul_of_nonneg_left
    (Real.log_le_sub_one_of_pos (div_pos hz0 hv)) hv.le
  have h1 := mul_le_mul_of_nonneg_left
    (Real.log_le_sub_one_of_pos (div_pos hz' hv')) hv'.le
  rw [Real.log_div hz0.ne' hv.ne'] at h0
  rw [Real.log_div hz'.ne' hv'.ne'] at h1
  have hr0 : v * (z / v - 1) = z - v := by field_simp [hv.ne']
  have hr1 : (1 - v) * ((1 - z) / (1 - v) - 1) = v - z := by
    field_simp; ring
  rw [hr0] at h0
  rw [hr1] at h1
  simp only [binaryDivergenceNats, Real.binEntropy, Real.log_inv]
  linarith

theorem entropy_conjugate_le (a t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    Real.binEntropy t + t * a ≤ Real.log (1 + Real.exp a) := by
  let z := Real.exp a / (1 + Real.exp a)
  have hd : 0 < 1 + Real.exp a := by positivity
  have hz0 : 0 < z := div_pos (Real.exp_pos a) hd
  have hz1 : z < 1 := (div_lt_one hd).mpr (by linarith)
  have hzlog : Real.log z = a - Real.log (1 + Real.exp a) := by
    dsimp [z]
    rw [Real.log_div (Real.exp_pos a).ne' hd.ne', Real.log_exp]
  have hzsub : 1 - z = 1 / (1 + Real.exp a) := by
    dsimp [z]
    field_simp
    ring
  have hzlog' : Real.log (1 - z) = -Real.log (1 + Real.exp a) := by
    rw [hzsub, Real.log_div one_ne_zero hd.ne', Real.log_one, zero_sub]
  have h := binaryDivergenceNats_nonneg ht0 ht1 hz0 hz1
  unfold binaryDivergenceNats at h
  rw [hzlog, hzlog'] at h
  linarith

theorem optimizingSurvivor_zero (p : ℝ) : optimizingSurvivor p 0 = 1 - p := by
  simp [optimizingSurvivor]

theorem optimizingSurvivor_pos {p s : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hs1 : s < 1) : 0 < optimizingSurvivor p s := by
  unfold optimizingSurvivor
  exact sub_pos.mpr (Real.rpow_lt_one hp0.le hp1 (one_div_pos.mpr (sub_pos.mpr hs1)))

theorem optimizingSurvivor_lt_one {p s : ℝ} (hp0 : 0 < p) :
    optimizingSurvivor p s < 1 := by
  unfold optimizingSurvivor
  linarith [Real.rpow_pos_of_pos hp0 (1 / (1 - s))]

theorem log_damping_at_optimizer {p s : ℝ} (hp0 : 0 < p) (hs1 : s < 1) :
    Real.log p = (1 - s) * Real.log (1 - optimizingSurvivor p s) := by
  simp only [optimizingSurvivor, sub_sub_cancel]
  rw [Real.log_rpow hp0]
  field_simp [ne_of_gt (sub_pos.mpr hs1)]

theorem typeExponent_optimizer_identity {p s : ℝ} (hp0 : 0 < p)
    (hs0 : s ≠ 0) (hs1 : s < 1) (u v : ℝ) :
    typeExponent p s u v =
      s * (Real.binEntropy (u * v) + (u * v) * renyiLogWeight p s) -
        u * (1 - s) * binaryDivergenceNats v (optimizingSurvivor p s) := by
  unfold typeExponent renyiLogWeight budgetNumerator binaryDivergenceNats
  rw [log_damping_at_optimizer hp0 hs1]
  field_simp [hs0]
  ring

theorem typeExponent_le_closed {p s u v : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hs0 : 0 < s) (hs1 : s < 1) (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    typeExponent p s u v ≤ s * Real.log (1 + Real.exp (renyiLogWeight p s)) := by
  have hd := binaryDivergenceNats_nonneg hv0 hv1
    (optimizingSurvivor_pos hp0 hp1 hs1) (optimizingSurvivor_lt_one hp0)
  have hcost : 0 ≤ u * (1 - s) * binaryDivergenceNats v (optimizingSurvivor p s) :=
    mul_nonneg (mul_nonneg hu0 (sub_pos.mpr hs1).le) hd
  have ht0 : 0 ≤ u * v := mul_nonneg hu0 hv0
  have ht1 : u * v ≤ 1 := by nlinarith
  have hc := mul_le_mul_of_nonneg_left
    (entropy_conjugate_le (renyiLogWeight p s) (u * v) ht0 ht1) hs0.le
  rw [typeExponent_optimizer_identity hp0 hs0.ne' hs1]
  linarith

theorem typeObjective_le_scalarBudget {p s u v : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) (hs0 : 0 < s) (hs1 : s < 1)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    typeObjective p s u v ≤ scalarBudget p s := by
  have h := typeExponent_le_closed hp0 hp1 hs0 hs1 hu0 hu1 hv0 hv1
  rw [typeExponent_eq p s u v hs0.ne'] at h
  have he : s * Real.log (1 + Real.exp (renyiLogWeight p s)) =
      (s * Real.log 2) * scalarBudget p s := by
    unfold scalarBudget log2
    field_simp [ne_of_gt log_two_pos]
  rw [he] at h
  exact le_of_mul_le_mul_left h (mul_pos hs0 log_two_pos)

theorem budgetNumerator_zero (p : ℝ) : budgetNumerator p 0 = 0 := by
  simp [budgetNumerator, optimizingSurvivor_zero]

theorem hasDerivAt_budgetNumerator_zero {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    HasDerivAt (budgetNumerator p)
      (Real.log (1 - p) + (p / (1 - p)) * Real.log p) 0 := by
  have hden : HasDerivAt (fun s : ℝ => 1 - s) (-1) 0 := by
    exact (hasDerivAt_id (0 : ℝ)).const_sub (1 : ℝ)
  have hinv : HasDerivAt (fun s : ℝ => 1 / (1 - s)) 1 0 := by
    convert (hasDerivAt_const (0 : ℝ) (1 : ℝ)).div hden (by norm_num) using 1
    norm_num
  have hpow : HasDerivAt (fun s : ℝ => p ^ (1 / (1 - s)))
      (Real.log p * p) 0 := by
    simpa using hinv.const_rpow hp0
  have hv : HasDerivAt (optimizingSurvivor p) (-(Real.log p * p)) 0 := by
    exact hpow.const_sub (1 : ℝ)
  have hlog : HasDerivAt (fun s : ℝ => Real.log (optimizingSurvivor p s))
      (-(Real.log p * p) / (1 - p)) 0 := by
    simpa [optimizingSurvivor_zero] using
      hv.log (by simpa [optimizingSurvivor_zero] using (sub_pos.mpr hp1).ne')
  convert (hasDerivAt_const (0 : ℝ) (Real.log (1 - p))).sub (hden.mul hlog) using 1
  · rfl
  · simp only [optimizingSurvivor_zero, sub_zero, neg_mul, zero_sub]
    ring

theorem tendsto_renyiLogWeight_zero_right {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    Tendsto (renyiLogWeight p) (𝓝[>] (0 : ℝ))
      (𝓝 (Real.log (1 - p) + (p / (1 - p)) * Real.log p)) := by
  change Tendsto (fun s : ℝ => budgetNumerator p s / s) _ _
  simpa [renyiLogWeight, budgetNumerator_zero, smul_eq_mul, div_eq_mul_inv, mul_comm] using
    (hasDerivAt_budgetNumerator_zero hp0 hp1).tendsto_slope_zero_right

theorem scalarBudget_eq_closed {p s : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hs1 : s < 1) :
    scalarBudget p s =
      log2 (1 + ((1 - p) / (optimizingSurvivor p s) ^ (1 - s)) ^ (1 / s)) := by
  have hq : 0 < 1 - p := sub_pos.mpr hp1
  have hv : 0 < optimizingSurvivor p s := optimizingSurvivor_pos hp0 hp1 hs1
  have hvp : 0 < (optimizingSurvivor p s) ^ (1 - s) := Real.rpow_pos_of_pos hv _
  unfold scalarBudget renyiLogWeight budgetNumerator
  rw [Real.rpow_def_of_pos (div_pos hq hvp), Real.log_div hq.ne' hvp.ne',
    Real.log_rpow hv]
  congr 3
  ring

theorem tendsto_scalarBudget_zero_right {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    Tendsto (scalarBudget p) (𝓝[>] (0 : ℝ)) (𝓝 (zCapacityBound p)) := by
  have hc : Continuous (fun x : ℝ => log2 (1 + Real.exp x)) := by
    unfold log2
    exact ((continuous_const.add Real.continuous_exp).log
      (fun x => (by positivity : 0 < 1 + Real.exp x).ne')).div_const (Real.log 2)
  have he : Real.exp (Real.log (1 - p) + (p / (1 - p)) * Real.log p) =
      (1 - p) * p ^ (p / (1 - p)) := by
    rw [Real.exp_add, Real.exp_log (sub_pos.mpr hp1), Real.rpow_def_of_pos hp0]
    congr 2
    ring
  change Tendsto (fun s : ℝ => log2 (1 + Real.exp (renyiLogWeight p s))) _ _
  simpa [Function.comp_def, scalarBudget, zCapacityBound, he] using
    hc.continuousAt.tendsto.comp (tendsto_renyiLogWeight_zero_right hp0 hp1)

theorem survivorTerm_nonneg (n w r : ℕ) {p s : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : 0 ≤ survivorTerm n w r p s := by
  unfold survivorTerm
  exact mul_nonneg (binomialTerm_nonneg w r (sub_nonneg.mpr hp1) (by linarith))
    (Real.rpow_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) s)

theorem survivorMoment_pos (n w : ℕ) {p s : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    0 < survivorMoment n w p s := by
  have h0 : survivorTerm n w 0 p s = p ^ w := by
    simp [survivorTerm, binomialTerm]
  have hsum : survivorTerm n w 0 p s ≤ survivorMoment n w p s := by
    unfold survivorMoment
    exact single_le_sum (fun i hi => survivorTerm_nonneg n w i hp0.le hp1.le)
      (mem_range.mpr (Nat.zero_lt_succ w))
  rw [h0] at hsum
  exact (pow_pos hp0 w).trans_le hsum

theorem log_survivorTerm (n w r : ℕ) {p s : ℝ}
    (hrw : r ≤ w) (hwn : w ≤ n) (hp0 : 0 < p) (hp1 : p < 1) :
    Real.log (survivorTerm n w r p s) =
      s * Real.log (n.choose r : ℝ) + (1 - s) * Real.log (w.choose r : ℝ) +
        (r : ℝ) * Real.log (1 - p) + (w - r : ℕ) * Real.log p := by
  have hcn : 0 < (n.choose r : ℝ) := by exact_mod_cast Nat.choose_pos (hrw.trans hwn)
  have hcw : 0 < (w.choose r : ℝ) := by exact_mod_cast Nat.choose_pos hrw
  have hq : 0 < 1 - p := sub_pos.mpr hp1
  have hratio : 0 < (n.choose r : ℝ) / (w.choose r : ℝ) := div_pos hcn hcw
  have hprob : 0 < binomialTerm w r (1 - p) := by
    unfold binomialTerm
    simp only [sub_sub_cancel]
    positivity
  unfold survivorTerm
  rw [Real.log_mul hprob.ne' (Real.rpow_pos_of_pos hratio s).ne', Real.log_rpow hratio,
    Real.log_div hcn.ne' hcw.ne']
  unfold binomialTerm
  simp only [sub_sub_cancel]
  rw [Real.log_mul (mul_pos hcw (pow_pos hq r)).ne' (pow_pos hp0 (w - r)).ne',
    Real.log_mul hcw.ne' (pow_pos hq r).ne', Real.log_pow, Real.log_pow]
  ring

theorem survivorTerm_le_typeExponent (n w r : ℕ) {p s : ℝ}
    (hn : 0 < n) (hw : 0 < w) (hrw : r ≤ w) (hwn : w ≤ n)
    (hp0 : 0 < p) (hp1 : p < 1) (hs0 : 0 < s) (hs1 : s < 1) :
    survivorTerm n w r p s ≤
      Real.exp ((n : ℝ) * typeExponent p s ((w : ℝ) / n) ((r : ℝ) / w)) := by
  have h0 := mul_le_mul_of_nonneg_left (log_choose_le_entropy n r (hrw.trans hwn)) hs0.le
  have h1 := mul_le_mul_of_nonneg_left (log_choose_le_entropy w r hrw) (sub_pos.mpr hs1).le
  have hlog := log_survivorTerm n w r (s := s) hrw hwn hp0 hp1
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  have hwR : (w : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hw
  have hprod : (w : ℝ) / n * ((r : ℝ) / w) = (r : ℝ) / n := by
    field_simp [hnR, hwR]
  have he : (n : ℝ) * typeExponent p s ((w : ℝ) / n) ((r : ℝ) / w) =
      s * ((n : ℝ) * Real.binEntropy ((r : ℝ) / n)) +
        (1 - s) * ((w : ℝ) * Real.binEntropy ((r : ℝ) / w)) +
        (r : ℝ) * Real.log (1 - p) + (w - r : ℕ) * Real.log p := by
    unfold typeExponent
    rw [hprod, Nat.cast_sub hrw]
    field_simp [hnR, hwR]
    ring
  apply Real.le_exp_of_log_le
  rw [he, hlog]
  linarith

theorem survivorTerm_le_closed (n w r : ℕ) {p s : ℝ}
    (hn : 0 < n) (hw : 0 < w) (hrw : r ≤ w) (hwn : w ≤ n)
    (hp0 : 0 < p) (hp1 : p < 1) (hs0 : 0 < s) (hs1 : s < 1) :
    survivorTerm n w r p s ≤
      Real.exp ((n : ℝ) * s * Real.log 2 * scalarBudget p s) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hwR : 0 < (w : ℝ) := by exact_mod_cast hw
  have hu0 : 0 ≤ (w : ℝ) / n := (div_pos hwR hnR).le
  have hu1 : (w : ℝ) / n ≤ 1 := (div_le_one hnR).mpr (by exact_mod_cast hwn)
  have hv0 : 0 ≤ (r : ℝ) / w := div_nonneg (Nat.cast_nonneg _) hwR.le
  have hv1 : (r : ℝ) / w ≤ 1 := (div_le_one hwR).mpr (by exact_mod_cast hrw)
  have hb := mul_le_mul_of_nonneg_left
    (typeExponent_le_closed hp0 hp1 hs0 hs1 hu0 hu1 hv0 hv1) hnR.le
  have he : (n : ℝ) * (s * Real.log (1 + Real.exp (renyiLogWeight p s))) =
      (n : ℝ) * s * Real.log 2 * scalarBudget p s := by
    unfold scalarBudget log2
    field_simp [ne_of_gt log_two_pos]
  rw [he] at hb
  exact (survivorTerm_le_typeExponent n w r hn hw hrw hwn hp0 hp1 hs0 hs1).trans
    (Real.exp_le_exp.mpr hb)

theorem survivorMoment_le_closed (n w : ℕ) {p s : ℝ}
    (hn : 0 < n) (hwn : w ≤ n) (hp0 : 0 < p) (hp1 : p < 1)
    (hs0 : 0 < s) (hs1 : s < 1) :
    survivorMoment n w p s ≤
      ((n : ℝ) + 1) * Real.exp ((n : ℝ) * s * Real.log 2 * scalarBudget p s) := by
  by_cases hw0 : w = 0
  · rw [hw0, survivorMoment_zero]
    have hx : 0 ≤ (n : ℝ) * s * Real.log 2 * scalarBudget p s := by
      exact mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg n) hs0.le) log_two_pos.le)
        (scalarBudget_nonneg p s)
    have he : 1 ≤ Real.exp ((n : ℝ) * s * Real.log 2 * scalarBudget p s) :=
      Real.one_le_exp_iff.mpr hx
    have hnR : 1 ≤ (n : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) n]
    nlinarith
  have hw : 0 < w := Nat.pos_of_ne_zero hw0
  unfold survivorMoment
  calc
    _ ≤ ∑ r ∈ range (w + 1),
        Real.exp ((n : ℝ) * s * Real.log 2 * scalarBudget p s) := by
      apply sum_le_sum
      intro r hr
      exact survivorTerm_le_closed n w r hn hw (Nat.le_of_lt_succ (mem_range.mp hr))
        hwn hp0 hp1 hs0 hs1
    _ = ((w : ℝ) + 1) * Real.exp ((n : ℝ) * s * Real.log 2 * scalarBudget p s) := by
      simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.succ_le_succ hwn)
      (Real.exp_pos _).le

theorem log2Moment_div_le (n w : ℕ) {p s : ℝ}
    (hn : 0 < n) (hwn : w ≤ n) (hp0 : 0 < p) (hp1 : p < 1)
    (hs0 : 0 < s) (hs1 : s < 1) :
    log2 (survivorMoment n w p s) / s ≤
      (n : ℝ) * scalarBudget p s + log2 ((n : ℝ) + 1) / s := by
  have hm := survivorMoment_pos n w hp0 hp1 (s := s)
  have hl := Real.log_le_log hm (survivorMoment_le_closed n w hn hwn hp0 hp1 hs0 hs1)
  rw [Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_exp] at hl
  have hd := div_le_div_of_nonneg_right hl log_two_pos.le
  have he : (Real.log ((n : ℝ) + 1) + (n : ℝ) * s * Real.log 2 * scalarBudget p s) /
      Real.log 2 = log2 ((n : ℝ) + 1) + s * ((n : ℝ) * scalarBudget p s) := by
    unfold log2
    field_simp [ne_of_gt log_two_pos]
  rw [he] at hd
  apply (div_le_iff₀ hs0).mpr
  change log2 (survivorMoment n w p s) ≤ log2 ((n : ℝ) + 1) +
    s * ((n : ℝ) * scalarBudget p s) at hd
  have hr : ((n : ℝ) * scalarBudget p s + log2 ((n : ℝ) + 1) / s) * s =
      log2 ((n : ℝ) + 1) + s * ((n : ℝ) * scalarBudget p s) := by
    field_simp [hs0.ne']
    ring
  rw [hr]
  exact hd

theorem finiteTypeIncrement_le (n w : ℕ) {p s : ℝ}
    (hn : 0 < n) (hwn : w ≤ n) (hp0 : 0 < p) (hp1 : p < 1)
    (hs0 : 0 < s) (hs1 : s < 1) :
    ((1 + s) / s) * log2 ((n : ℝ) + 1) + log2 (survivorMoment n w p s) / s ≤
      (n : ℝ) * scalarBudget p s + ((2 + s) / s) * log2 ((n : ℝ) + 1) := by
  calc
    _ ≤ ((1 + s) / s) * log2 ((n : ℝ) + 1) +
        ((n : ℝ) * scalarBudget p s + log2 ((n : ℝ) + 1) / s) :=
      by linarith [log2Moment_div_le n w hn hwn hp0 hp1 hs0 hs1]
    _ = _ := by field_simp [hs0.ne']; ring

theorem scalarBudget_one {p : ℝ} (hp1 : p < 1) :
    scalarBudget p 1 = log2 (1 + (1 - p)) := by
  simp [scalarBudget, renyiLogWeight, budgetNumerator, Real.exp_log (sub_pos.mpr hp1)]

theorem survivorMoment_one_le (n w : ℕ) {p : ℝ} (hwn : w ≤ n)
    (hp0 : 0 < p) (hp1 : p < 1) :
    survivorMoment n w p 1 ≤ (1 + (1 - p)) ^ n := by
  have hq : 0 ≤ 1 - p := (sub_pos.mpr hp1).le
  have hterm : ∀ r ∈ range (w + 1),
      survivorTerm n w r p 1 ≤ (n.choose r : ℝ) * (1 - p) ^ r := by
    intro r hr
    have hrw : r ≤ w := Nat.le_of_lt_succ (mem_range.mp hr)
    have hc : (w.choose r : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.choose_pos hrw).ne'
    have he : survivorTerm n w r p 1 =
        (n.choose r : ℝ) * (1 - p) ^ r * p ^ (w - r) := by
      unfold survivorTerm binomialTerm
      simp only [Real.rpow_one, sub_sub_cancel]
      field_simp [hc]
    rw [he]
    exact mul_le_of_le_one_right (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hq _))
      (pow_le_one₀ hp0.le hp1.le)
  unfold survivorMoment
  calc
    _ ≤ ∑ r ∈ range (w + 1), (n.choose r : ℝ) * (1 - p) ^ r :=
      sum_le_sum hterm
    _ ≤ ∑ r ∈ range (n + 1), (n.choose r : ℝ) * (1 - p) ^ r := by
      exact sum_le_sum_of_subset_of_nonneg (range_mono (Nat.succ_le_succ hwn))
        (fun r hr hn => mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hq _))
    _ = (1 + (1 - p)) ^ n := by
      rw [add_comm 1 (1 - p), add_pow]
      apply sum_congr rfl
      intro r hr
      simp only [one_pow, mul_one]
      ring

theorem tendsto_typeOverhead_zero (s : ℝ) :
    Tendsto (fun n : ℕ => ((2 + s) / s) * log2 ((n : ℝ) + 1) / n)
      atTop (𝓝 0) := by
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ) / n) atTop (𝓝 0) := by
    simpa only [Function.comp_def, one_mul, pow_one, add_zero] using
      (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp
      (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)
  have hdiff := Real.tendsto_log_nat_add_one_sub_log.mul
    (tendsto_one_div_atTop_nhds_zero_nat :
      Tendsto (fun n : ℕ => (1 : ℝ) / n) atTop (𝓝 0))
  have hsum : Tendsto (fun n : ℕ => Real.log ((n : ℝ) + 1) / n) atTop (𝓝 0) := by
    convert hdiff.add hlog using 1
    · ext n
      ring
    · simp
  convert (hsum.div_const (Real.log 2)).const_mul ((2 + s) / s) using 1
  · ext n
    unfold log2
    ring
  · simp

end

end QuantumProver.AmplitudeDamping.Scalar

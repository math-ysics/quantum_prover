import Mathlib

namespace QuantumProver.SuperchannelDiscrimination

noncomputable def binaryRelativeEntropyBits (p q : ℝ) : ℝ :=
  (p * Real.log (p / q) + (1 - p) * Real.log ((1 - p) / (1 - q))) / Real.log 2

noncomputable def extendedBinaryRelativeEntropyBits (p q : ℝ) : EReal :=
  if q = 0 then (if p = 0 then 0 else ⊤)
  else if q = 1 then (if p = 1 then 0 else ⊤)
  else (binaryRelativeEntropyBits p q : EReal)

theorem weighted_log_quotient (a : ℝ) {b : ℝ} (hb : b ≠ 0) :
    a * Real.log (a / b) = a * Real.log a - a * Real.log b := by
  by_cases ha : a = 0
  · simp [ha]
  · rw [Real.log_div ha hb]
    ring

theorem binary_cross_entropy_identity {p q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    binaryRelativeEntropyBits p q =
      p * Real.logb 2 (1 / q) + (1 - p) * Real.logb 2 (1 / (1 - q)) -
        Real.binEntropy p / Real.log 2 := by
  have hq0' : q ≠ 0 := ne_of_gt hq0
  have hq1' : 1 - q ≠ 0 := ne_of_gt (sub_pos.mpr hq1)
  rw [binaryRelativeEntropyBits, weighted_log_quotient p hq0',
    weighted_log_quotient (1 - p) hq1']
  simp only [Real.logb, Real.binEntropy, one_div, Real.log_inv]
  ring

theorem binary_entropy_bits_le_one (p : ℝ) :
    Real.binEntropy p / Real.log 2 ≤ 1 := by
  apply (div_le_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mpr
  simpa using (Real.binEntropy_le_log_two (p := p))

theorem binary_relative_entropy_ge {p q : ℝ}
    (hp1 : p ≤ 1) (hq0 : 0 < q) (hq1 : q < 1) :
    p * Real.logb 2 (1 / q) - 1 ≤ binaryRelativeEntropyBits p q := by
  have hq : 0 < 1 - q := sub_pos.mpr hq1
  have hq_le : 1 - q ≤ 1 := by linarith
  have hlog : 0 ≤ Real.logb 2 (1 / (1 - q)) := by
    apply Real.logb_nonneg (by norm_num : (1 : ℝ) < 2)
    exact (le_div_iff₀ hq).mpr (by linarith)
  have hterm : 0 ≤ (1 - p) * Real.logb 2 (1 / (1 - q)) :=
    mul_nonneg (sub_nonneg.mpr hp1) hlog
  rw [binary_cross_entropy_identity hq0 hq1]
  linarith [binary_entropy_bits_le_one p]

theorem binary_relative_entropy_ge_of_typeI {p q ε : ℝ}
    (hp1 : p ≤ 1) (h_accept : 1 - ε ≤ p) (hq0 : 0 < q) (hq1 : q < 1) :
    (1 - ε) * Real.logb 2 (1 / q) - 1 ≤ binaryRelativeEntropyBits p q := by
  have hlog : 0 ≤ Real.logb 2 (1 / q) := by
    apply Real.logb_nonneg (by norm_num : (1 : ℝ) < 2)
    exact (le_div_iff₀ hq0).mpr (by linarith)
  have hmul := mul_le_mul_of_nonneg_right h_accept hlog
  exact (sub_le_sub_right hmul 1).trans (binary_relative_entropy_ge hp1 hq0 hq1)

theorem typeII_lower_bound_of_binary_bound {q ε B : ℝ} {n : ℕ}
    (hq0 : 0 < q) (hε : ε < 1)
    (h : (1 - ε) * Real.logb 2 (1 / q) - 1 ≤ (n : ℝ) * B) :
    (2 : ℝ) ^ (-((n : ℝ) * B + 1) / (1 - ε)) ≤ q := by
  have hεR : 0 < 1 - ε := sub_pos.mpr hε
  apply (Real.le_logb_iff_rpow_le (by norm_num : (1 : ℝ) < 2) hq0).mp
  apply (div_le_iff₀ hεR).mpr
  rw [one_div, Real.logb_inv] at h
  nlinarith

theorem typeII_lower_bound_of_divergence {p q ε B : ℝ} {n : ℕ}
    (hp1 : p ≤ 1) (h_accept : 1 - ε ≤ p) (hq0 : 0 < q) (hq1 : q < 1)
    (hε : ε < 1) (hD : binaryRelativeEntropyBits p q ≤ (n : ℝ) * B) :
    (2 : ℝ) ^ (-((n : ℝ) * B + 1) / (1 - ε)) ≤ q := by
  apply typeII_lower_bound_of_binary_bound hq0 hε
  exact (binary_relative_entropy_ge_of_typeI hp1 h_accept hq0 hq1).trans hD

theorem typeII_lower_bound_of_extended_divergence {p q ε B : ℝ} {n : ℕ}
    (hp1 : p ≤ 1) (h_accept : 1 - ε ≤ p) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hε : ε < 1) (hB : 0 ≤ B)
    (hD : extendedBinaryRelativeEntropyBits p q ≤ (((n : ℝ) * B : ℝ) : EReal)) :
    (2 : ℝ) ^ (-((n : ℝ) * B + 1) / (1 - ε)) ≤ q := by
  have hp_pos : 0 < p := (sub_pos.mpr hε).trans_le h_accept
  by_cases hqzero : q = 0
  · have htop : (⊤ : EReal) ≤ (((n : ℝ) * B : ℝ) : EReal) := by
      simpa [extendedBinaryRelativeEntropyBits, hqzero, ne_of_gt hp_pos] using hD
    exact (not_le_of_gt (EReal.coe_lt_top ((n : ℝ) * B)) htop).elim
  · have hq_pos : 0 < q := lt_of_le_of_ne hq0 (Ne.symm hqzero)
    by_cases hqone : q = 1
    · rw [hqone]
      apply Real.rpow_le_one_of_one_le_of_nonpos (by norm_num : (1 : ℝ) ≤ 2)
      have hNB : 0 ≤ (n : ℝ) * B := mul_nonneg (by positivity) hB
      exact div_nonpos_of_nonpos_of_nonneg (by linarith) (sub_pos.mpr hε).le
    · have hq_lt : q < 1 := lt_of_le_of_ne hq1 hqone
      have hD' : binaryRelativeEntropyBits p q ≤ (n : ℝ) * B := by
        apply EReal.coe_le_coe_iff.mp
        simpa [extendedBinaryRelativeEntropyBits, hqzero, hqone] using hD
      exact typeII_lower_bound_of_divergence hp1 h_accept hq_pos hq_lt hε hD'

end QuantumProver.SuperchannelDiscrimination

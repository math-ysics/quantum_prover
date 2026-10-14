import QuantumProver.InformationTheory.VisibleCompression.Definitions

/-!
# Scalar dependencies for the dimension-nine compression converse

This module proves the exact strict rate gap and the finite probability-weight
algebra.  The seed theorem has a per-seed support-score bound as an explicit
hypothesis; it does not claim to prove that bound for a quantum decoder.
-/

namespace VisibleCompression

open scoped BigOperators

theorem log2_two_pos : 0 < Real.log (2 : ℝ) :=
  Real.log_pos (by norm_num)

theorem decayD9_pos : 0 < decayD9 := by
  norm_num [decayD9]

theorem decayD9_lt_one : decayD9 < 1 := by
  norm_num [decayD9]

theorem log2_mul {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) :
    log2 (x * y) = log2 x + log2 y := by
  unfold log2
  rw [Real.log_mul hx hy]
  ring

theorem log2_pow (x : ℝ) (n : ℕ) : log2 (x ^ n) = (n : ℝ) * log2 x := by
  unfold log2
  rw [Real.log_pow]
  ring

theorem log2_rpow {x : ℝ} (hx : 0 < x) (r : ℝ) :
    log2 (Real.rpow x r) = r * log2 x := by
  unfold log2
  rw [Real.rpow_eq_pow, Real.log_rpow hx]
  ring

theorem log2_le_log2 {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) : log2 x ≤ log2 y :=
  div_le_div_of_nonneg_right (Real.log_le_log hx hxy) log2_two_pos.le

theorem log2_decayD9 : log2 decayD9 = -log2 (45 / 37) := by
  unfold decayD9 log2
  rw [show (37 / 45 : ℝ) = (45 / 37 : ℝ)⁻¹ by norm_num, Real.log_inv]
  ring

theorem min_le_sqrt_mul (d h : ℝ) (hd : 0 ≤ d) (hh : 0 ≤ h) :
    min d h ≤ Real.sqrt (d * h) := by
  apply Real.le_sqrt_of_sq_le
  rcases le_total d h with hdh | hhd
  · rw [min_eq_left hdh]
    nlinarith [mul_nonneg hd (sub_nonneg.mpr hdh)]
  · rw [min_eq_right hhd]
    nlinarith [mul_nonneg hh (sub_nonneg.mpr hhd)]

theorem sqrt_nine_pow (k : ℕ) : Real.sqrt ((9 : ℝ) ^ k) = (3 : ℝ) ^ k := by
  have hpow : (9 : ℝ) ^ k = ((3 : ℝ) ^ k) ^ 2 := by
    calc
      (9 : ℝ) ^ k = ((3 : ℝ) ^ 2) ^ k := by norm_num
      _ = ((3 : ℝ) ^ k) ^ 2 := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]
  rw [hpow, Real.sqrt_sq (pow_nonneg (by norm_num) k)]

theorem mul_sqrt_eq_rpow_three_halves {d : ℝ} (hd : 0 < d) :
    d * Real.sqrt d = Real.rpow d (3 / 2) := by
  calc
    d * Real.sqrt d = Real.rpow d 1 * Real.rpow d (1 / 2) := by
      simp only [Real.rpow_eq_pow, Real.rpow_one, ← Real.sqrt_eq_rpow]
    _ = Real.rpow d (1 + 1 / 2) := (Real.rpow_add hd 1 (1 / 2)).symm
    _ = Real.rpow d (3 / 2) := by norm_num

/-- Exact D9 interpolation term in the subset-moment scalar bound. -/
theorem d9_purity_interpolation (d : ℝ) (k : ℕ) (hd : 0 < d) :
    d * min d ((9 : ℝ) ^ k) ≤ Real.rpow d (3 / 2) * (3 : ℝ) ^ k := by
  calc
    d * min d ((9 : ℝ) ^ k) ≤ d * Real.sqrt (d * (9 : ℝ) ^ k) :=
      mul_le_mul_of_nonneg_left
        (min_le_sqrt_mul d ((9 : ℝ) ^ k) hd.le (pow_nonneg (by norm_num) k)) hd.le
    _ = (d * Real.sqrt d) * (3 : ℝ) ^ k := by
      rw [Real.sqrt_mul hd.le, sqrt_nine_pow]
      ring
    _ = Real.rpow d (3 / 2) * (3 : ℝ) ^ k := by
      rw [mul_sqrt_eq_rpow_three_halves hd]

theorem subset_product_expansion {I : Type*} [Fintype I] [DecidableEq I]
    (a b : ℝ) :
    (∑ T : Finset I, a ^ (Fintype.card I - T.card) * b ^ T.card) =
      (a + b) ^ Fintype.card I := by
  have h := Fintype.prod_add (fun _ : I => b) (fun _ : I => a)
  simp only [Finset.prod_const, Finset.card_univ, Finset.card_compl] at h
  simpa only [mul_comm, add_comm] using h.symm

theorem d9_subset_scalar_sum (n : ℕ) :
    (∑ T : Finset (Fin n),
      (71 / 90 : ℝ) ^ (n - T.card) * (1 / 90 : ℝ) ^ T.card * (3 : ℝ) ^ T.card) =
      decayD9 ^ n := by
  calc
    (∑ T : Finset (Fin n),
        (71 / 90 : ℝ) ^ (n - T.card) * (1 / 90 : ℝ) ^ T.card * (3 : ℝ) ^ T.card) =
        ∑ T : Finset (Fin n),
          (71 / 90 : ℝ) ^ (n - T.card) * ((1 / 90 : ℝ) * 3) ^ T.card := by
      apply Finset.sum_congr rfl
      intro T _
      rw [mul_pow]
      ring
    _ = ((71 / 90 : ℝ) + (1 / 90 : ℝ) * 3) ^ n := by
      simpa only [Fintype.card_fin] using
        (subset_product_expansion (I := Fin n) (71 / 90) ((1 / 90) * 3))
    _ = decayD9 ^ n := by norm_num [decayD9]

/-- The complete scalar subset estimate. The marginal Choi-purity premise
is separate from the iid operator moment identity. -/
theorem d9_subset_purity_sum_bound (d : ℝ) (n : ℕ)
    (purity : Finset (Fin n) → ℝ) (hd : 0 < d)
    (hpurity : ∀ T, purity T ≤ d * min d ((9 : ℝ) ^ T.card)) :
    (∑ T : Finset (Fin n),
      ((71 / 90 : ℝ) ^ (n - T.card) * (1 / 90 : ℝ) ^ T.card) * purity T) ≤
      Real.rpow d (3 / 2) * decayD9 ^ n := by
  calc
    (∑ T : Finset (Fin n),
        ((71 / 90 : ℝ) ^ (n - T.card) * (1 / 90 : ℝ) ^ T.card) * purity T) ≤
        ∑ T : Finset (Fin n),
          ((71 / 90 : ℝ) ^ (n - T.card) * (1 / 90 : ℝ) ^ T.card) *
            (Real.rpow d (3 / 2) * (3 : ℝ) ^ T.card) := by
      apply Finset.sum_le_sum
      intro T _
      apply mul_le_mul_of_nonneg_left
        ((hpurity T).trans (d9_purity_interpolation d T.card hd))
      positivity
    _ = Real.rpow d (3 / 2) *
        ∑ T : Finset (Fin n),
          (71 / 90 : ℝ) ^ (n - T.card) * (1 / 90 : ℝ) ^ T.card * (3 : ℝ) ^ T.card := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro T _
      ring
    _ = Real.rpow d (3 / 2) * decayD9 ^ n := by rw [d9_subset_scalar_sum]

theorem d9_gap_identity :
    lowerRateD9 - holevoD9 = (1 / 3 : ℝ) * log2 (12800 / 12321) := by
  have hlog : Real.log (12800 / 12321 : ℝ) =
      2 * Real.log (45 / 37 : ℝ) - 3 * Real.log (9 / 8 : ℝ) := by
    rw [show (12800 / 12321 : ℝ) = (45 / 37 : ℝ) ^ 2 / (9 / 8 : ℝ) ^ 3 by
      norm_num]
    rw [Real.log_div (by norm_num) (by norm_num), Real.log_pow, Real.log_pow]
    norm_num
  unfold lowerRateD9 holevoD9 log2
  rw [hlog]
  ring

theorem holevoD9_lt_lowerRateD9 : holevoD9 < lowerRateD9 := by
  have hnum : 0 < Real.log (12800 / 12321 : ℝ) :=
    Real.log_pos (by norm_num)
  have hgap : 0 < (1 / 3 : ℝ) * log2 (12800 / 12321) := by
    unfold log2
    exact mul_pos (by norm_num) (div_pos hnum log2_two_pos)
  have := d9_gap_identity
  linarith

/-- Squaring an arbitrary finite probability-weighted mean does not exceed
the same probability-weighted mean of the squares.  No support-size bound
or uniform-distribution assumption is used. -/
theorem weighted_average_sq_le_average_sq {S : Type*} [Fintype S]
    (q f : S → ℝ) (hq : ∀ s, 0 ≤ q s) (hqs : ∑ s, q s = 1) :
    (∑ s, q s * f s) ^ 2 ≤ ∑ s, q s * (f s) ^ 2 := by
  classical
  have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
    (r := fun s => q s * f s) (f := q) (g := fun s => q s * (f s) ^ 2)
    (fun s _ => hq s)
    (fun s _ => mul_nonneg (hq s) (sq_nonneg (f s)))
    (fun s _ => le_of_eq (by ring))
  simpa only [hqs, one_mul] using hcs

/-- A uniform scalar square bound survives an arbitrary finite shared seed. -/
theorem weighted_average_sq_le {S : Type*} [Fintype S]
    (q f : S → ℝ) (B : ℝ) (hq : ∀ s, 0 ≤ q s) (hqs : ∑ s, q s = 1)
    (hf : ∀ s, (f s) ^ 2 ≤ B) :
    (∑ s, q s * f s) ^ 2 ≤ B := by
  classical
  calc
    (∑ s, q s * f s) ^ 2 ≤ ∑ s, q s * (f s) ^ 2 :=
      weighted_average_sq_le_average_sq q f hq hqs
    _ ≤ ∑ s, q s * B := Finset.sum_le_sum fun s _ =>
      mul_le_mul_of_nonneg_left (hf s) (hq s)
    _ = (∑ s, q s) * B := (Finset.sum_mul _ _ _).symm
    _ = B := by rw [hqs, one_mul]

/-- This is the exact finite-seed scalar reduction in the proof.
The actual seed-averaged support score is bounded below by `1 - ε`;
the decoder-dependent square bound remains a visible hypothesis. -/
theorem finite_seed_strong_converse {S : Type*} [Fintype S]
    (q score : S → ℝ) (ε d : ℝ) (n : ℕ)
    (hq : ∀ s, 0 ≤ q s) (hqs : ∑ s, q s = 1)
    (hε : ε ≤ 1)
    (hscore : 1 - ε ≤ ∑ s, q s * score s)
    (hdecoder : ∀ s, (score s) ^ 2 ≤ Real.rpow d (3 / 2) * decayD9 ^ n) :
    (1 - ε) ^ 2 ≤ Real.rpow d (3 / 2) * decayD9 ^ n := by
  have havg := weighted_average_sq_le q score
    (Real.rpow d (3 / 2) * decayD9 ^ n) hq hqs hdecoder
  have hn : 0 ≤ 1 - ε := by linarith
  have hm : 0 ≤ ∑ s, q s * score s := le_trans hn hscore
  have hprod : 0 ≤ ((∑ s, q s * score s) - (1 - ε)) *
      ((∑ s, q s * score s) + (1 - ε)) :=
    mul_nonneg (sub_nonneg.mpr hscore) (add_nonneg hm hn)
  nlinarith

/-- Exact logarithmic consequence of the finite-code inequality.
The hypothesis `hbound` is the finite-code inequality. -/
theorem finite_code_log_balance (ε d : ℝ) (n : ℕ)
    (hε : ε < 1) (hd : 0 < d)
    (hbound : (1 - ε) ^ 2 ≤ Real.rpow d (3 / 2) * decayD9 ^ n) :
    (4 / 3 : ℝ) * log2 (1 - ε) + (n : ℝ) * lowerRateD9 ≤ log2 d := by
  have hleft : 0 < (1 - ε) ^ 2 := pow_pos (sub_pos.mpr hε) 2
  have hlog := log2_le_log2 hleft hbound
  rw [log2_pow, log2_mul (x := Real.rpow d (3 / 2)) (y := decayD9 ^ n)
    (Real.rpow_pos_of_pos hd _).ne'
    (pow_pos decayD9_pos n).ne', log2_rpow hd, log2_pow, log2_decayD9] at hlog
  unfold lowerRateD9
  norm_num at hlog
  nlinarith

theorem finite_code_rate_lower (ε d : ℝ) (n : ℕ)
    (hε : ε < 1) (hd : 0 < d) (hn : 0 < n)
    (hbound : (1 - ε) ^ 2 ≤ Real.rpow d (3 / 2) * decayD9 ^ n) :
    lowerRateD9 + ((4 / 3 : ℝ) * log2 (1 - ε)) / (n : ℝ) ≤
      log2 d / (n : ℝ) := by
  have hnreal : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  apply (le_div_iff₀ hnreal).mpr
  calc
    (lowerRateD9 + ((4 / 3 : ℝ) * log2 (1 - ε)) / (n : ℝ)) * (n : ℝ) =
        (4 / 3 : ℝ) * log2 (1 - ε) + (n : ℝ) * lowerRateD9 := by
      field_simp [hnreal.ne'] <;> ring
    _ ≤ log2 d := finite_code_log_balance ε d n hε hd hbound

/-- The finite-code logarithmic correction vanishes for vanishing block error. -/
theorem finite_code_correction_tendsto_zero (ε : ℕ → ℝ)
    (hε : Filter.Tendsto ε Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun n => ((4 / 3 : ℝ) * log2 (1 - ε n)) / (n : ℝ))
      Filter.atTop (nhds 0) := by
  have hone : Filter.Tendsto (fun n => 1 - ε n) Filter.atTop (nhds (1 : ℝ)) := by
    simpa using tendsto_const_nhds.sub hε
  have hlog : Filter.Tendsto (fun n => Real.log (1 - ε n))
      Filter.atTop (nhds 0) := by
    simpa only [Function.comp_def, Real.log_one] using
      (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp hone
  have hlog2 : Filter.Tendsto (fun n => log2 (1 - ε n)) Filter.atTop (nhds 0) := by
    simpa [log2] using hlog.div_const (Real.log 2)
  have hnum : Filter.Tendsto (fun n => (4 / 3 : ℝ) * log2 (1 - ε n))
      Filter.atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul hlog2
  exact hnum.div_atTop tendsto_natCast_atTop_atTop

end VisibleCompression

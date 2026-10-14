import Mathlib

set_option autoImplicit false

namespace QuantumProver.SuperchannelDiscrimination

open Filter
open scoped Topology

theorem divergence_telescopes {v : ℕ → ℝ} {B : ℝ}
    (h0 : v 0 ≤ 0) (hs : ∀ n, v (n + 1) ≤ v n + B) :
    ∀ n, v n ≤ (n : ℝ) * B := by
  intro n
  induction n with
  | zero => simpa using h0
  | succ n ih =>
      calc
        v (n + 1) ≤ v n + B := hs n
        _ ≤ (n : ℝ) * B + B := by linarith
        _ = ((n + 1 : ℕ) : ℝ) * B := by push_cast; ring

theorem divergence_telescopes_upto {v : ℕ → ℝ} {B : ℝ} {N : ℕ}
    (h0 : v 0 ≤ 0) (hs : ∀ k, k < N → v (k + 1) ≤ v k + B) :
    v N ≤ (N : ℝ) * B := by
  have h_prefix : ∀ m, m ≤ N → v m ≤ (m : ℝ) * B := by
    intro m
    induction m with
    | zero =>
        intro hm
        simpa using h0
    | succ m ih =>
        intro hm
        have hm_lt : m < N := Nat.lt_of_succ_le hm
        have hv : v m ≤ (m : ℝ) * B := ih (Nat.le_of_lt hm_lt)
        calc
          v (m + 1) ≤ v m + B := hs m hm_lt
          _ ≤ (m : ℝ) * B + B := by linarith
          _ = ((m + 1 : ℕ) : ℝ) * B := by push_cast; ring
  exact h_prefix N le_rfl

theorem normalized_rate_le {n : ℕ} {ε B L : ℝ}
    (hn : 0 < n) (hε : ε < 1)
    (h : (1 - ε) * L - 1 ≤ (n : ℝ) * B) :
    L / (n : ℝ) ≤ (B + 1 / (n : ℝ)) / (1 - ε) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnR
  have hεR : 0 < 1 - ε := sub_pos.mpr hε
  apply (le_div_iff₀ hεR).mpr
  rw [div_mul_eq_mul_div₀]
  apply (div_le_iff₀ hnR).mpr
  rw [add_mul, div_mul_cancel₀ 1 hn0]
  nlinarith

theorem rate_le_of_binary_bound {n : ℕ} {ε B rate : ℝ}
    (hn : 0 < n) (hε : ε < 1)
    (h : (1 - ε) * (n : ℝ) * rate - 1 ≤ (n : ℝ) * B) :
    rate ≤ (B + 1 / (n : ℝ)) / (1 - ε) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnR
  have h' : (1 - ε) * ((n : ℝ) * rate) - 1 ≤ (n : ℝ) * B := by
    nlinarith [h]
  simpa [mul_div_cancel_left₀ rate hn0] using normalized_rate_le hn hε h'

theorem converse_limsup_le {rate : ℕ → ℝ} {ε B : ℝ}
    (hε : ε < 1)
    (h_nonneg : ∀ᶠ n : ℕ in atTop, 0 ≤ rate n)
    (h_binary : ∀ᶠ n : ℕ in atTop,
      (1 - ε) * (n : ℝ) * rate n - 1 ≤ (n : ℝ) * B) :
    limsup rate atTop ≤ B / (1 - ε) := by
  have hlim : Tendsto (fun n : ℕ => (B + 1 / (n : ℝ)) / (1 - ε))
      atTop (𝓝 (B / (1 - ε))) := by
    convert (tendsto_const_nhds.add
      (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))).div_const (1 - ε) using 1 <;> simp
  have hle : ∀ᶠ n in atTop, rate n ≤ (B + 1 / (n : ℝ)) / (1 - ε) := by
    filter_upwards [h_binary, eventually_gt_atTop 0] with n hn hnpos
    exact rate_le_of_binary_bound hnpos hε hn
  have h_below : atTop.IsBoundedUnder (· ≥ ·) rate :=
    isBoundedUnder_of_eventually_ge h_nonneg
  exact (limsup_le_limsup hle h_below.isCobounded_flip hlim.isBoundedUnder_le).trans_eq
    hlim.limsup_eq

theorem converse_liminf_le {rate : ℕ → ℝ} {ε B : ℝ}
    (hε : ε < 1)
    (h_nonneg : ∀ᶠ n : ℕ in atTop, 0 ≤ rate n)
    (h_binary : ∀ᶠ n : ℕ in atTop,
      (1 - ε) * (n : ℝ) * rate n - 1 ≤ (n : ℝ) * B) :
    liminf rate atTop ≤ B / (1 - ε) := by
  have hlim : Tendsto (fun n : ℕ => (B + 1 / (n : ℝ)) / (1 - ε))
      atTop (𝓝 (B / (1 - ε))) := by
    convert (tendsto_const_nhds.add
      (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))).div_const (1 - ε) using 1 <;> simp
  have hle : ∀ᶠ n in atTop, rate n ≤ (B + 1 / (n : ℝ)) / (1 - ε) := by
    filter_upwards [h_binary, eventually_gt_atTop 0] with n hn hnpos
    exact rate_le_of_binary_bound hnpos hε hn
  have h_below : atTop.IsBoundedUnder (· ≥ ·) rate :=
    isBoundedUnder_of_eventually_ge h_nonneg
  have h_above : atTop.IsBoundedUnder (· ≤ ·) rate :=
    hlim.isBoundedUnder_le.mono_le hle
  exact (liminf_le_limsup h_above h_below).trans
    (converse_limsup_le hε h_nonneg h_binary)

end QuantumProver.SuperchannelDiscrimination

namespace QuantumProver.SuperchannelDiscrimination.WeakRateReduction

open Filter
open scoped Topology

def blockSize (N : ℕ) : ℕ := Nat.sqrt N
def blockCount (N : ℕ) : ℕ := N / blockSize N
def paddingSize (N : ℕ) : ℕ := N % blockSize N

theorem blockSize_eq_floor (N : ℕ) : blockSize N = ⌊Real.sqrt (N : ℝ)⌋₊ := by
  simp [blockSize]

theorem blockSize_pos {N : ℕ} (hN : 4 ≤ N) : 0 < blockSize N := by
  exact Nat.sqrt_pos.mpr (by omega)

theorem blockSize_real_bounds {N : ℕ} (hN : 4 ≤ N) :
    Real.sqrt (N : ℝ) / 2 ≤ (blockSize N : ℝ) ∧
      (blockSize N : ℝ) ≤ Real.sqrt (N : ℝ) := by
  have hm1 : (1 : ℝ) ≤ (blockSize N : ℝ) := by
    exact_mod_cast (blockSize_pos hN)
  have hupper : (blockSize N : ℝ) ≤ Real.sqrt (N : ℝ) := Real.nat_sqrt_le_real_sqrt
  have hlower : Real.sqrt (N : ℝ) < (blockSize N : ℝ) + 1 :=
    Real.real_sqrt_lt_nat_sqrt_succ
  exact ⟨by linarith, hupper⟩

theorem blockSize_le_blockCount {N : ℕ} (hN : 4 ≤ N) :
    blockSize N ≤ blockCount N := by
  apply (Nat.le_div_iff_mul_le (blockSize_pos hN)).mpr
  exact Nat.sqrt_le N

theorem blockCount_real_bounds {N : ℕ} (hN : 4 ≤ N) :
    Real.sqrt (N : ℝ) / 2 ≤ (blockCount N : ℝ) ∧
      (blockCount N : ℝ) ≤ 2 * Real.sqrt (N : ℝ) := by
  have hm := blockSize_real_bounds hN
  have hmk : (blockSize N : ℝ) ≤ (blockCount N : ℝ) := by
    exact_mod_cast blockSize_le_blockCount hN
  have hproduct : (blockCount N : ℝ) * (blockSize N : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast (Nat.div_mul_le_self N (blockSize N))
  have hspos : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < N))
  have hs2 := Real.sq_sqrt (Nat.cast_nonneg N)
  have hmul := mul_le_mul_of_nonneg_left hm.1 (Nat.cast_nonneg (blockCount N) : (0 : ℝ) ≤ _)
  constructor
  · exact hm.1.trans hmk
  · apply (mul_le_mul_iff_left₀ hspos).mp
    nlinarith

theorem block_padding_identity (N : ℕ) :
    blockSize N * blockCount N + paddingSize N = N := Nat.div_add_mod N (blockSize N)

theorem paddingSize_lt_blockSize {N : ℕ} (hN : 4 ≤ N) :
    paddingSize N < blockSize N := Nat.mod_lt N (blockSize_pos hN)

theorem paddingSize_real_le_sqrt {N : ℕ} (hN : 4 ≤ N) :
    (paddingSize N : ℝ) ≤ Real.sqrt (N : ℝ) := by
  have hpad : (paddingSize N : ℝ) < (blockSize N : ℝ) := by
    exact_mod_cast paddingSize_lt_blockSize hN
  exact hpad.le.trans (blockSize_real_bounds hN).2

theorem all_integer_rate_overhead {N : ℕ} (hN : 4 ≤ N) {a L c : ℝ}
    (haL : a ≤ L) (hc : 0 ≤ c) :
    (blockSize N : ℝ) * (blockCount N : ℝ) * a +
        2 * (blockCount N : ℝ) * c + (paddingSize N : ℝ) * L ≤
      (N : ℝ) * a + Real.sqrt (N : ℝ) * (L - a + 4 * c) := by
  have hidentity : (blockSize N : ℝ) * (blockCount N : ℝ) + (paddingSize N : ℝ) = N := by
    exact_mod_cast block_padding_identity N
  have hpad := mul_le_mul_of_nonneg_right (paddingSize_real_le_sqrt hN)
    (sub_nonneg.mpr haL)
  have hcount := mul_le_mul_of_nonneg_right (blockCount_real_bounds hN).2 hc
  have hidentitya := congrArg (fun t : ℝ => t * a) hidentity
  nlinarith

theorem eventually_all_integer_rate_absorption {a R L c : ℝ}
    (haR : a < R) (haL : a ≤ L) (hc : 0 ≤ c) :
    ∀ᶠ N : ℕ in atTop,
      (blockSize N : ℝ) * (blockCount N : ℝ) * a +
        2 * (blockCount N : ℝ) * c + (paddingSize N : ℝ) * L ≤ (N : ℝ) * R := by
  have hs : Tendsto (fun N : ℕ => Real.sqrt (N : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop 4,
    hs.eventually (eventually_ge_atTop ((L - a + 4 * c) / (R - a)))] with N hN hlarge
  have hmul : L - a + 4 * c ≤ Real.sqrt (N : ℝ) * (R - a) :=
    (div_le_iff₀ (sub_pos.mpr haR)).mp hlarge
  have hmul2 := mul_le_mul_of_nonneg_left hmul (Real.sqrt_nonneg (N : ℝ))
  have hs2 := Real.sq_sqrt (Nat.cast_nonneg N)
  exact (all_integer_rate_overhead hN haL hc).trans (by nlinarith)

noncomputable def descentTheta (b : ℝ) : ℝ := (1 + b) / 2
noncomputable def descentRate (r L b : ℝ) (j : ℕ) : ℝ := r + (descentTheta b) ^ j * (L - r)

theorem descentTheta_bounds {b : ℝ} (hb0 : 0 ≤ b) (hb1 : b < 1) :
    0 < descentTheta b ∧ b < descentTheta b ∧ descentTheta b < 1 := by
  unfold descentTheta
  constructor
  · linarith
  constructor <;> linarith

theorem descentRate_step_gap {r L b : ℝ} (hb0 : 0 ≤ b) (hb1 : b < 1) (hrL : r < L)
    (j : ℕ) :
    (1 - b) * r + b * descentRate r L b j < descentRate r L b (j + 1) := by
  have htheta := descentTheta_bounds hb0 hb1
  have hpos := mul_pos (mul_pos (sub_pos.mpr htheta.2.1) (pow_pos htheta.1 j)) (sub_pos.mpr hrL)
  have heq : descentRate r L b (j + 1) - ((1 - b) * r + b * descentRate r L b j) =
      (descentTheta b - b) * (descentTheta b) ^ j * (L - r) := by
    unfold descentRate
    rw [pow_succ]
    ring
  linarith

theorem descentRate_tendsto {r L b : ℝ} (hb0 : 0 ≤ b) (hb1 : b < 1) :
    Tendsto (descentRate r L b) atTop (𝓝 r) := by
  change Tendsto (fun j => r + (descentTheta b) ^ j * (L - r)) atTop (𝓝 r)
  have htheta := descentTheta_bounds hb0 hb1
  have hpow := tendsto_pow_atTop_nhds_zero_of_lt_one htheta.1.le htheta.2.2
  simpa only [zero_mul, add_zero] using
    tendsto_const_nhds.add (hpow.mul_const (L - r))

theorem exists_finite_descent {r R L b : ℝ} (hb0 : 0 ≤ b) (hb1 : b < 1) (hrR : r < R) :
    ∃ j : ℕ, descentRate r L b j < R :=
  ((descentRate_tendsto (r := r) (L := L) hb0 hb1).eventually (Iio_mem_nhds hrR)).exists

end QuantumProver.SuperchannelDiscrimination.WeakRateReduction

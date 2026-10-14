import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open Filter
open scoped Topology

namespace QuantumProver.QuantumRedistributionDimensions

def retainedRate (a c t : ℝ) : ℝ := max 0 (a / 2 - c * t)

def totalExponent (s t : ℝ) (n : ℕ) : ℕ :=
  Nat.ceil ((n : ℝ) * (s + t) / Real.log 2)

def retainedExponent (a c t : ℝ) (n : ℕ) : ℕ :=
  Nat.floor ((n : ℝ) * retainedRate a c t / Real.log 2)

def sentExponent (s a b c t : ℝ) (n : ℕ) : ℕ :=
  totalExponent s t n - retainedExponent a c t n - retainedExponent b c t n

def totalDimension (s t : ℝ) (n : ℕ) : ℕ := 2 ^ totalExponent s t n

def retainedDimension (a c t : ℝ) (n : ℕ) : ℕ := 2 ^ retainedExponent a c t n

def sentDimension (s a b c t : ℝ) (n : ℕ) : ℕ := 2 ^ sentExponent s a b c t n

def sentRate (s a b c t : ℝ) : ℝ :=
  s + t - retainedRate a c t - retainedRate b c t

theorem log_two_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)

theorem retainedRate_nonneg (a c t : ℝ) : 0 ≤ retainedRate a c t :=
  le_max_left _ _

theorem retainedRate_le_half {a c t : ℝ} (ha : 0 ≤ a)
    (hc : 0 ≤ c) (ht : 0 ≤ t) : retainedRate a c t ≤ a / 2 := by
  apply max_le
  · positivity
  · have := mul_nonneg hc ht
    linarith

theorem retainedRate_sum_le {s a b c t : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b ≤ 2 * s) (hc : 0 ≤ c) (ht : 0 ≤ t) :
    retainedRate a c t + retainedRate b c t ≤ s := by
  have h₁ := retainedRate_le_half ha hc ht
  have h₂ := retainedRate_le_half hb hc ht
  linarith

theorem totalDimension_pos (s t : ℝ) (n : ℕ) : 0 < totalDimension s t n :=
  pow_pos (by norm_num) _

theorem retainedDimension_pos (a c t : ℝ) (n : ℕ) :
    0 < retainedDimension a c t n := pow_pos (by norm_num) _

theorem sentDimension_pos (s a b c t : ℝ) (n : ℕ) :
    0 < sentDimension s a b c t n := pow_pos (by norm_num) _

theorem log_pow_two (k : ℕ) :
    Real.log ((2 ^ k : ℕ) : ℝ) = (k : ℝ) * Real.log 2 := by
  simp only [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]

theorem log_totalDimension_bounds {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (n : ℕ) :
    (n : ℝ) * (s + t) ≤ Real.log (totalDimension s t n : ℝ) ∧
    Real.log (totalDimension s t n : ℝ) < (n : ℝ) * (s + t) + Real.log 2 := by
  have hlo := Nat.le_ceil ((n : ℝ) * (s + t) / Real.log 2)
  have hhi := Nat.ceil_lt_add_one
    (show 0 ≤ (n : ℝ) * (s + t) / Real.log 2 by positivity)
  have hlo' := (div_le_iff₀ log_two_pos).mp hlo
  have hhi' := (lt_div_iff₀ log_two_pos).mp
    (show (Nat.ceil ((n : ℝ) * (s + t) / Real.log 2) : ℝ) <
      ((n : ℝ) * (s + t) + Real.log 2) / Real.log 2 by
      convert hhi using 1
      field_simp [ne_of_gt log_two_pos])
  rw [totalDimension, log_pow_two]
  exact ⟨hlo', hhi'⟩

theorem log_retainedDimension_bounds (a c t : ℝ) (n : ℕ) :
    (n : ℝ) * retainedRate a c t - Real.log 2 <
      Real.log (retainedDimension a c t n : ℝ) ∧
    Real.log (retainedDimension a c t n : ℝ) ≤ (n : ℝ) * retainedRate a c t := by
  have hlo := Nat.lt_floor_add_one ((n : ℝ) * retainedRate a c t / Real.log 2)
  have hhi := Nat.floor_le
    (show 0 ≤ (n : ℝ) * retainedRate a c t / Real.log 2 by
      exact div_nonneg (mul_nonneg (Nat.cast_nonneg n) (retainedRate_nonneg a c t))
        log_two_pos.le)
  have hlo' := (div_lt_iff₀ log_two_pos).mp hlo
  have hhi' := (le_div_iff₀ log_two_pos).mp hhi
  rw [retainedDimension, log_pow_two]
  constructor
  · dsimp [retainedExponent]
    linarith
  · exact hhi'

theorem retainedDimension_eq_one_of_nonpos {a c t : ℝ}
    (h : a / 2 - c * t ≤ 0) (n : ℕ) : retainedDimension a c t n = 1 := by
  simp [retainedDimension, retainedExponent, retainedRate, max_eq_left h]

theorem retainedDimension_singleton_or_threshold (a c t : ℝ) (n : ℕ) :
    retainedDimension a c t n = 1 ∨
      (0 < a / 2 - c * t ∧
        Real.log (retainedDimension a c t n : ℝ) ≤ (n : ℝ) * (a / 2 - c * t)) := by
  by_cases h : a / 2 - c * t ≤ 0
  · exact Or.inl (retainedDimension_eq_one_of_nonpos h n)
  · have hp : 0 < a / 2 - c * t := lt_of_not_ge h
    refine Or.inr ⟨hp, ?_⟩
    simpa only [retainedRate, max_eq_right hp.le] using
      (log_retainedDimension_bounds a c t n).2

theorem retainedExponents_le_total {s a b c t : ℝ}
    (hs : 0 ≤ s) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b ≤ 2 * s)
    (hc : 0 ≤ c) (ht : 0 ≤ t) (n : ℕ) :
    retainedExponent a c t n + retainedExponent b c t n ≤ totalExponent s t n := by
  have h₁ := (log_retainedDimension_bounds a c t n).2
  have h₂ := (log_retainedDimension_bounds b c t n).2
  have h₃ := (log_totalDimension_bounds hs ht n).1
  have hsum := retainedRate_sum_le ha hb hab hc ht
  have hmul := mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg n)
  rw [retainedDimension, log_pow_two] at h₁ h₂
  rw [totalDimension, log_pow_two] at h₃
  have hreal : (retainedExponent a c t n : ℝ) +
      (retainedExponent b c t n : ℝ) ≤ (totalExponent s t n : ℝ) := by
    nlinarith [log_two_pos, mul_nonneg (Nat.cast_nonneg n) ht]
  exact_mod_cast hreal

theorem totalDimension_eq_product {s a b c t : ℝ}
    (hs : 0 ≤ s) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b ≤ 2 * s)
    (hc : 0 ≤ c) (ht : 0 ≤ t) (n : ℕ) :
    totalDimension s t n = retainedDimension a c t n *
      retainedDimension b c t n * sentDimension s a b c t n := by
  have h := retainedExponents_le_total hs ha hb hab hc ht n
  unfold totalDimension retainedDimension sentDimension
  rw [← pow_add, ← pow_add]
  congr 1
  unfold sentExponent
  omega

def packingChart {s a b c t : ℝ}
    (hs : 0 ≤ s) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b ≤ 2 * s)
    (hc : 0 ≤ c) (ht : 0 ≤ t) (n : ℕ) :
    Fin (totalDimension s t n) ≃
      ((Fin (retainedDimension a c t n) × Fin (retainedDimension b c t n)) ×
        Fin (sentDimension s a b c t n)) :=
  Fintype.equivOfCardEq (by
    simp only [Fintype.card_fin, Fintype.card_prod]
    exact totalDimension_eq_product hs ha hb hab hc ht n)

theorem rank_le_totalDimension {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t)
    (n r : ℕ) (hr : (r : ℝ) ≤ Real.exp ((n : ℝ) * (s + t))) :
    r ≤ totalDimension s t n := by
  have hd : 0 < (totalDimension s t n : ℝ) := by
    exact_mod_cast totalDimension_pos s t n
  have hb := Real.exp_le_exp.mpr (log_totalDimension_bounds hs ht n).1
  rw [Real.exp_log hd] at hb
  exact_mod_cast hr.trans hb

def supportEmbedding {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t)
    (n r : ℕ) (hr : (r : ℝ) ≤ Real.exp ((n : ℝ) * (s + t))) :
    Fin r ↪ Fin (totalDimension s t n) :=
  Fin.castLEEmb (rank_le_totalDimension hs ht n r hr)

theorem log_sentDimension_eq {s a b c t : ℝ}
    (hs : 0 ≤ s) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b ≤ 2 * s)
    (hc : 0 ≤ c) (ht : 0 ≤ t) (n : ℕ) :
    Real.log (sentDimension s a b c t n : ℝ) =
      Real.log (totalDimension s t n : ℝ) -
        Real.log (retainedDimension a c t n : ℝ) -
        Real.log (retainedDimension b c t n : ℝ) := by
  have hsum := retainedExponents_le_total hs ha hb hab hc ht n
  have h₁ : retainedExponent a c t n ≤ totalExponent s t n := by omega
  have h₂ : retainedExponent b c t n ≤
      totalExponent s t n - retainedExponent a c t n := by omega
  simp only [sentDimension, totalDimension, retainedDimension, log_pow_two]
  rw [sentExponent, Nat.cast_sub h₂, Nat.cast_sub h₁]
  ring

theorem log_sentDimension_bounds {s a b c t : ℝ}
    (hs : 0 ≤ s) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b ≤ 2 * s)
    (hc : 0 ≤ c) (ht : 0 ≤ t) (n : ℕ) :
    (n : ℝ) * sentRate s a b c t ≤ Real.log (sentDimension s a b c t n : ℝ) ∧
      Real.log (sentDimension s a b c t n : ℝ) <
        (n : ℝ) * sentRate s a b c t + 3 * Real.log 2 := by
  rw [log_sentDimension_eq hs ha hb hab hc ht n]
  have h₀ := log_totalDimension_bounds hs ht n
  have h₁ := log_retainedDimension_bounds a c t n
  have h₂ := log_retainedDimension_bounds b c t n
  dsimp [sentRate]
  constructor <;> nlinarith

theorem tendsto_log_retainedDimension_rate (a c t : ℝ) :
    Tendsto (fun n : ℕ => Real.log (retainedDimension a c t n : ℝ) / (n : ℝ))
      atTop (𝓝 (retainedRate a c t)) := by
  have hnonneg : 0 ≤ retainedRate a c t / Real.log 2 :=
    div_nonneg (retainedRate_nonneg a c t) log_two_pos.le
  have h := (tendsto_nat_floor_mul_div_atTop hnonneg).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have h' := h.mul_const (Real.log 2)
  convert h' using 1
  · ext n
    simp only [retainedDimension, log_pow_two, retainedExponent, Function.comp_apply]
    rw [show (n : ℝ) * retainedRate a c t / Real.log 2 =
      (retainedRate a c t / Real.log 2) * (n : ℝ) by ring]
    ring
  · field_simp [ne_of_gt log_two_pos]

theorem tendsto_log_totalDimension_rate {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    Tendsto (fun n : ℕ => Real.log (totalDimension s t n : ℝ) / (n : ℝ))
      atTop (𝓝 (s + t)) := by
  have hnonneg : 0 ≤ (s + t) / Real.log 2 := div_nonneg (add_nonneg hs ht) log_two_pos.le
  have h := (tendsto_nat_ceil_mul_div_atTop hnonneg).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have h' := h.mul_const (Real.log 2)
  convert h' using 1
  · ext n
    simp only [totalDimension, log_pow_two, totalExponent, Function.comp_apply]
    rw [show (n : ℝ) * (s + t) / Real.log 2 =
      ((s + t) / Real.log 2) * (n : ℝ) by ring]
    ring
  · field_simp [ne_of_gt log_two_pos]

theorem tendsto_log_sentDimension_rate {s a b c t : ℝ}
    (hs : 0 ≤ s) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b ≤ 2 * s)
    (hc : 0 ≤ c) (ht : 0 ≤ t) :
    Tendsto (fun n : ℕ => Real.log (sentDimension s a b c t n : ℝ) / (n : ℝ))
      atTop (𝓝 (sentRate s a b c t)) := by
  have h := ((tendsto_log_totalDimension_rate hs ht).sub
    (tendsto_log_retainedDimension_rate a c t)).sub
    (tendsto_log_retainedDimension_rate b c t)
  unfold sentRate
  convert h using 1
  ext n
  rw [log_sentDimension_eq hs ha hb hab hc ht n]
  ring

theorem sentRate_nonneg {s a b c t : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b ≤ 2 * s)
    (hc : 0 ≤ c) (ht : 0 ≤ t) : 0 ≤ sentRate s a b c t := by
  have h := retainedRate_sum_le ha hb hab hc ht
  dsimp [sentRate]
  linarith

theorem sentRate_le (s a b c t : ℝ) :
    sentRate s a b c t ≤ s - (a + b) / 2 + (1 + 2 * c) * t := by
  have h₁ : a / 2 - c * t ≤ retainedRate a c t := le_max_right _ _
  have h₂ : b / 2 - c * t ≤ retainedRate b c t := le_max_right _ _
  dsimp [sentRate]
  linarith

theorem sentRate_four_le (s a b t : ℝ) :
    sentRate s a b 4 t ≤ s - (a + b) / 2 + 9 * t := by
  have h := sentRate_le s a b 4 t
  norm_num at h
  exact h

theorem exists_strict_margin {s a b c q : ℝ} (hc : 0 ≤ c)
    (hq : s - (a + b) / 2 < q) :
    ∃ t : ℝ, 0 < t ∧ sentRate s a b c t < q := by
  have hden : 0 < 1 + 2 * c := by linarith
  let t := (q - (s - (a + b) / 2)) / (2 * (1 + 2 * c))
  have ht : 0 < t := div_pos (sub_pos.mpr hq) (mul_pos (by norm_num) hden)
  refine ⟨t, ht, lt_of_le_of_lt (sentRate_le s a b c t) ?_⟩
  have hcancel : (1 + 2 * c) * t = (q - (s - (a + b) / 2)) / 2 := by
    dsimp [t]
    field_simp [ne_of_gt hden]
  rw [hcancel]
  linarith

theorem exists_strict_rate_packing {s a b c q : ℝ}
    (hs : 0 ≤ s) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b ≤ 2 * s)
    (hc : 0 ≤ c) (hq : s - (a + b) / 2 < q) :
    ∃ t : ℝ, 0 < t ∧ sentRate s a b c t < q ∧
      Tendsto (fun n : ℕ => Real.log (sentDimension s a b c t n : ℝ) / (n : ℝ))
        atTop (𝓝 (sentRate s a b c t)) ∧
      ∀ n : ℕ, totalDimension s t n = retainedDimension a c t n *
        retainedDimension b c t n * sentDimension s a b c t n := by
  obtain ⟨t, ht, hrate⟩ := exists_strict_margin hc hq
  exact ⟨t, ht, hrate, tendsto_log_sentDimension_rate hs ha hb hab hc ht.le,
    totalDimension_eq_product hs ha hb hab hc ht.le⟩

end QuantumProver.QuantumRedistributionDimensions

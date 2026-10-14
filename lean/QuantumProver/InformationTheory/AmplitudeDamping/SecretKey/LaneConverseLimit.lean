import QuantumProver.InformationTheory.AmplitudeDamping.SecretKey.PurificationBounds

set_option autoImplicit false
noncomputable section
open Filter Topology

namespace QuantumProver.AmplitudeDamping.SecretKey.LaneConverseLimit

theorem log2_le_of_pow_le_two_rpow {G e : ℝ} {n : ℕ}
    (hG : 0 < G) (hn : 0 < n) (h : G ^ n ≤ (2 : ℝ) ^ ((n : ℝ) * e)) :
    log2 G ≤ e := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hlog := Real.log_le_log (pow_pos hG n) h
  rw [Real.log_pow, Real.log_rpow (by norm_num : 0 < (2 : ℝ))] at hlog
  have hcancel : Real.log G ≤ e * Real.log 2 := by
    apply (mul_le_mul_iff_of_pos_left hnR).mp
    simpa only [mul_assoc] using hlog
  exact (div_le_iff₀ (Real.log_pos (by norm_num : 1 < (2 : ℝ)))).mpr hcancel

theorem le_two_rpow_of_log2_le {G e : ℝ} (hG : 0 < G) (h : log2 G ≤ e) :
    G ≤ (2 : ℝ) ^ e := by
  have hlog : Real.log G ≤ e * Real.log 2 :=
    (div_le_iff₀ (Real.log_pos (by norm_num : 1 < (2 : ℝ)))).mp h
  calc
    G = Real.exp (Real.log G) := (Real.exp_log hG).symm
    _ ≤ Real.exp (e * Real.log 2) := Real.exp_le_exp.mpr hlog
    _ = (2 : ℝ) ^ e := by
      rw [Real.rpow_def_of_pos (by norm_num : 0 < (2 : ℝ)), mul_comm]

theorem le_min_two_rpow_of_finite_powers {G a c : ℝ} (hG0 : 0 ≤ G) (hG1 : G ≤ 1)
    (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0))
    (hpow : ∀ n : ℕ, 0 < n → G ^ n ≤ (2 : ℝ) ^ ((n : ℝ) * (a + c * ε n))) :
    G ≤ min 1 ((2 : ℝ) ^ a) := by
  apply le_min hG1
  by_cases hG : 0 < G
  · have hlim : Tendsto (fun n : ℕ => a + c * ε n) atTop (𝓝 a) := by
      simpa only [mul_zero, add_zero] using tendsto_const_nhds.add (hε.const_mul c)
    have hlog : log2 G ≤ a := by
      apply le_of_tendsto_of_tendsto tendsto_const_nhds hlim
      filter_upwards [Filter.eventually_gt_atTop (0 : ℕ)] with n hn
      exact log2_le_of_pow_le_two_rpow hG hn (hpow n hn)
    exact le_two_rpow_of_log2_le hG hlog
  · have hz : G = 0 := le_antisymm (le_of_not_gt hG) hG0
    rw [hz]
    exact Real.rpow_nonneg (by norm_num) _

theorem strong_bound_of_finite_lane_overhead {G p k z : ℝ} {m d : ℕ}
    (hG0 : 0 ≤ G) (hG1 : G ≤ 1) (hz : 0 < z)
    (hpow : ∀ n : ℕ, 0 < n → G ^ n ≤ (2 : ℝ) ^
      (-z * ((n : ℝ) * log2 (d : ℝ) - (n : ℝ) * k - (m : ℝ) *
        ((n : ℝ) * channelBz p z + (2 / z) * log2 ((n : ℝ) + 1))))) :
    G ≤ min 1 ((2 : ℝ) ^ (-z * (log2 (d : ℝ) - k - (m : ℝ) * channelBz p z))) := by
  let ε := fun n : ℕ => (2 / z) * log2 ((n : ℝ) + 1) / n
  apply le_min_two_rpow_of_finite_powers hG0 hG1 ε
    (Scalar.tendsto_normalized_type_overhead_zero hz)
    (c := (m : ℝ) * z)
  intro n hn
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  have heq : -z * ((n : ℝ) * log2 (d : ℝ) - (n : ℝ) * k - (m : ℝ) *
      ((n : ℝ) * channelBz p z + (2 / z) * log2 ((n : ℝ) + 1))) =
    (n : ℝ) * (-z * (log2 (d : ℝ) - k - (m : ℝ) * channelBz p z) +
      ((m : ℝ) * z) * ε n) := by
    dsimp only [ε]
    field_simp [hnR, hz.ne']
    <;> ring
  rw [← heq]
  exact hpow n hn

theorem strong_bound_of_finite_block_powers {G p k z : ℝ} {m d : ℕ}
    (hG0 : 0 ≤ G) (hG1 : G ≤ 1) (hp0 : 0 < p) (hp1 : p < 1)
    (hz0 : 0 < z) (hz1 : z < 1)
    (hpow : ∀ n : ℕ, 0 < n → G ^ n ≤ (2 : ℝ) ^
      (-z * ((n : ℝ) * log2 (d : ℝ) - (n : ℝ) * k -
        (m : ℝ) * Scalar.normalizedBlockBudget n p z))) :
    G ≤ min 1 ((2 : ℝ) ^ (-z * (log2 (d : ℝ) - k - (m : ℝ) * channelBz p z))) := by
  apply strong_bound_of_finite_lane_overhead hG0 hG1 hz0
  intro n hn
  have hb := Scalar.normalizedBlockBudget_le n hn hp0 hp1 hz0 hz1
  have hs : 0 ≤ z * (m : ℝ) := mul_nonneg hz0.le (Nat.cast_nonneg m)
  have hm := mul_le_mul_of_nonneg_left hb hs
  have he : -z * ((n : ℝ) * log2 (d : ℝ) - (n : ℝ) * k -
      (m : ℝ) * Scalar.normalizedBlockBudget n p z) ≤
    -z * ((n : ℝ) * log2 (d : ℝ) - (n : ℝ) * k - (m : ℝ) *
      ((n : ℝ) * channelBz p z + (2 / z) * log2 ((n : ℝ) + 1))) := by
    nlinarith
  exact (hpow n hn).trans (Real.rpow_le_rpow_of_exponent_le (by norm_num : 1 ≤ (2 : ℝ)) he)

end QuantumProver.AmplitudeDamping.SecretKey.LaneConverseLimit

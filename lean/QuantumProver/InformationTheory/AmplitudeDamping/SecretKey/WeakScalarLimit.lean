import QuantumProver.InformationTheory.AmplitudeDamping.SecretKey.PurificationBounds

set_option autoImplicit false
noncomputable section
open Filter Topology

namespace QuantumProver.AmplitudeDamping.SecretKey.WeakScalarLimit

theorem tendsto_lane_overhead_zero {z : ℝ} (hz : 0 < z) :
    Tendsto
      (fun n : ℕ => (2 / z) * log2 ((n : ℝ) + 2) / ((n : ℝ) + 1))
      atTop (𝓝 0) := by
  have h := (Scalar.tendsto_normalized_type_overhead_zero hz).comp
    (Filter.tendsto_add_atTop_nat 1)
  convert h using 1
  ext n
  simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one, add_assoc,
    one_add_one_eq_two]

theorem weak_bound_of_finite_lane_overhead {L k p z : ℝ} {m : ℕ}
    (hz : 0 < z)
    (hbound : ∀ n : ℕ,
      ((n : ℝ) + 1) * L ≤ ((n : ℝ) + 1) * k + (m : ℝ) *
        (((n : ℝ) + 1) * channelBz p z + (2 / z) * log2 ((n : ℝ) + 2))) :
    L ≤ k + (m : ℝ) * channelBz p z := by
  have hlim : Tendsto
      (fun n : ℕ => k + (m : ℝ) * channelBz p z +
        (m : ℝ) * ((2 / z) * log2 ((n : ℝ) + 2) / ((n : ℝ) + 1)))
      atTop (𝓝 (k + (m : ℝ) * channelBz p z)) := by
    simpa only [mul_zero, add_zero] using
      tendsto_const_nhds.add ((tendsto_lane_overhead_zero hz).const_mul (m : ℝ))
  apply le_of_tendsto_of_tendsto tendsto_const_nhds hlim
  filter_upwards [] with n
  have hN : 0 < (n : ℝ) + 1 := by positivity
  apply (mul_le_mul_iff_of_pos_left hN).mp
  have heq : ((n : ℝ) + 1) *
      (k + (m : ℝ) * channelBz p z +
        (m : ℝ) * ((2 / z) * log2 ((n : ℝ) + 2) / ((n : ℝ) + 1))) =
      ((n : ℝ) + 1) * k + (m : ℝ) *
        (((n : ℝ) + 1) * channelBz p z + (2 / z) * log2 ((n : ℝ) + 2)) := by
    calc
      _ = ((n : ℝ) + 1) * k + (m : ℝ) *
          (((n : ℝ) + 1) * channelBz p z +
            ((n : ℝ) + 1) * ((2 / z) * log2 ((n : ℝ) + 2) / ((n : ℝ) + 1))) := by
        ring
      _ = _ := by rw [mul_div_cancel₀ _ hN.ne']
  rw [heq]
  exact hbound n

theorem weak_bound_of_all_positive_orders {L k p : ℝ} {m : ℕ}
    (hp0 : 0 < p) (hp1 : p < 1)
    (hbound : ∀ z : ℝ, 0 < z → z < 1 → L ≤ k + (m : ℝ) * channelBz p z) :
    L ≤ k + (m : ℝ) * channelCZ p := by
  have hlim : Tendsto (fun z : ℝ => k + (m : ℝ) * channelBz p z)
      (𝓝[>] (0 : ℝ)) (𝓝 (k + (m : ℝ) * channelCZ p)) :=
    tendsto_const_nhds.add ((Scalar.tendsto_channelBz_zero_right hp0 hp1).const_mul
      (m : ℝ))
  apply le_of_tendsto_of_tendsto tendsto_const_nhds hlim
  have hlt : ∀ᶠ z : ℝ in 𝓝[>] (0 : ℝ), z < 1 :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds
      (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [self_mem_nhdsWithin, hlt] with z hz0 hz1
  exact hbound z hz0 hz1

theorem weak_bound_of_finite_lane_overhead_all_orders {L k p : ℝ} {m : ℕ}
    (hp0 : 0 < p) (hp1 : p < 1)
    (hbound : ∀ z : ℝ, 0 < z → z < 1 → ∀ n : ℕ,
      ((n : ℝ) + 1) * L ≤ ((n : ℝ) + 1) * k + (m : ℝ) *
        (((n : ℝ) + 1) * channelBz p z + (2 / z) * log2 ((n : ℝ) + 2))) :
    L ≤ k + (m : ℝ) * channelCZ p := by
  apply weak_bound_of_all_positive_orders hp0 hp1
  intro z hz0 hz1
  exact weak_bound_of_finite_lane_overhead hz0 (hbound z hz0 hz1)

end QuantumProver.AmplitudeDamping.SecretKey.WeakScalarLimit

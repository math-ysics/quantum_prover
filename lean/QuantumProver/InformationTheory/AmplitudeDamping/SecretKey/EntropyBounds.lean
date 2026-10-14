import Mathlib

open scoped BigOperators

namespace QuantumProver.AmplitudeDamping.SecretKey.Scalar

variable {ι : Type*} [Fintype ι]

noncomputable def flagPowerCost (b μ : ι → ℝ) (α : ℝ) : ℝ :=
  ∑ i, μ i * (b i / μ i) ^ α

noncomputable def normalizedFlags (b : ι → ℝ) : ι → ℝ :=
  fun i ↦ b i / (∑ j, b j)

theorem normalizedFlags_nonneg (b : ι → ℝ)
    (hb : ∀ i, 0 ≤ b i) (hZ : 0 < ∑ i, b i) (i : ι) :
    0 ≤ normalizedFlags b i :=
  div_nonneg (hb i) hZ.le

theorem normalizedFlags_sum (b : ι → ℝ) (hZ : 0 < ∑ i, b i) :
    (∑ i, normalizedFlags b i) = 1 := by
  classical
  unfold normalizedFlags
  rw [← Finset.sum_div, div_self hZ.ne']

theorem normalizedFlags_support (b : ι → ℝ) (hZ : 0 < ∑ i, b i)
    (i : ι) (hi : normalizedFlags b i = 0) : b i = 0 := by
  unfold normalizedFlags at hi
  rcases (div_eq_zero_iff).mp hi with h | h
  · exact h
  · exact False.elim (hZ.ne' h)

theorem normalized_flag_power_lower_bound (b μ : ι → ℝ) (α : ℝ)
    (hb : ∀ i, 0 ≤ b i) (hμ : ∀ i, 0 ≤ μ i)
    (hμsum : ∑ i, μ i = 1)
    (hsupport : ∀ i, μ i = 0 → b i = 0) (hα : 1 ≤ α) :
    (∑ i, b i) ^ α ≤ flagPowerCost b μ α := by
  classical
  have hterm : ∀ i, μ i * (b i / μ i) = b i := by
    intro i
    by_cases hi : μ i = 0
    · simp [hi, hsupport i hi]
    · field_simp [hi]
  have hsum : (∑ i, μ i * (b i / μ i)) = ∑ i, b i :=
    Finset.sum_congr rfl (fun i _ ↦ hterm i)
  have hJ := (convexOn_rpow hα).map_sum_le
    (t := Finset.univ) (w := μ) (p := fun i ↦ b i / μ i)
    (fun i _ ↦ hμ i) hμsum
    (fun i _ ↦ show b i / μ i ∈ Set.Ici (0 : ℝ) from
      div_nonneg (hb i) (hμ i))
  simpa only [smul_eq_mul, hsum, flagPowerCost] using hJ

theorem flagPowerCost_normalizedFlags (b : ι → ℝ) (α : ℝ)
    (hZ : 0 < ∑ i, b i) :
    flagPowerCost b (normalizedFlags b) α = (∑ i, b i) ^ α := by
  classical
  have hterm : ∀ i,
      normalizedFlags b i * (b i / normalizedFlags b i) ^ α =
        (b i / (∑ j, b j)) * (∑ j, b j) ^ α := by
    intro i
    by_cases hi : b i = 0
    · simp [normalizedFlags, hi]
    · have hratio : b i / (b i / (∑ j, b j)) = ∑ j, b j := by
        field_simp [hi, hZ.ne']
      simpa only [normalizedFlags, hratio]
  unfold flagPowerCost
  calc
    (∑ i, normalizedFlags b i * (b i / normalizedFlags b i) ^ α) =
        ∑ i, (b i / (∑ j, b j)) * (∑ j, b j) ^ α :=
      Finset.sum_congr rfl (fun i _ ↦ hterm i)
    _ = (∑ i, b i / (∑ j, b j)) * (∑ j, b j) ^ α :=
      (Finset.sum_mul _ _ _).symm
    _ = (∑ j, b j) ^ α := by
      rw [← Finset.sum_div, div_self hZ.ne', one_mul]

theorem normalizedFlags_optimal (b μ : ι → ℝ) (α : ℝ)
    (hb : ∀ i, 0 ≤ b i) (hZ : 0 < ∑ i, b i)
    (hμ : ∀ i, 0 ≤ μ i) (hμsum : ∑ i, μ i = 1)
    (hsupport : ∀ i, μ i = 0 → b i = 0) (hα : 1 ≤ α) :
    flagPowerCost b (normalizedFlags b) α ≤ flagPowerCost b μ α := by
  rw [flagPowerCost_normalizedFlags b α hZ]
  exact normalized_flag_power_lower_bound b μ α hb hμ hμsum hsupport hα

theorem weighted_log_ratio_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 < y) :
    x * (Real.log y - Real.log x) ≤ y - x := by
  rcases eq_or_lt_of_le hx with rfl | hx
  · simpa using hy.le
  have h := mul_le_mul_of_nonneg_left
    (Real.log_le_sub_one_of_pos (div_pos hy hx)) hx.le
  rw [Real.log_div hy.ne' hx.ne'] at h
  have hcancel : x * (y / x) = y := by field_simp [hx.ne']
  nlinarith [hcancel]

theorem binary_entropy_cross_entropy_le {x r : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hr0 : 0 < r) (hr1 : r < 1) :
    Real.binEntropy x + x * Real.log r +
      (1 - x) * Real.log (1 - r) ≤ 0 := by
  have hfirst := weighted_log_ratio_le hx0 hr0
  have hsecond := weighted_log_ratio_le (sub_nonneg.mpr hx1) (sub_pos.mpr hr1)
  rw [Real.binEntropy, Real.log_inv, Real.log_inv]
  nlinarith [hfirst, hsecond]

theorem binary_entropy_conjugate {x A : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hA : 0 < A) :
    Real.binEntropy x + x * Real.log A ≤ Real.log (1 + A) := by
  have hsum : 0 < 1 + A := by positivity
  have hr0 : 0 < A / (1 + A) := div_pos hA hsum
  have hr1 : A / (1 + A) < 1 := (div_lt_one hsum).mpr (by linarith)
  have h := binary_entropy_cross_entropy_le hx0 hx1 hr0 hr1
  have hcomp : 1 - A / (1 + A) = 1 / (1 + A) := by
    field_simp [hsum.ne'] <;> ring
  have hlog : Real.log (1 - A / (1 + A)) = -Real.log (1 + A) := by
    rw [hcomp, Real.log_div one_ne_zero hsum.ne', Real.log_one]
    ring
  rw [Real.log_div hA.ne' hsum.ne', hlog] at h
  nlinarith [h]

theorem probability_power_sum_le_card [Nonempty ι] (a : ι → ℝ)
    (ha : ∀ i, 0 ≤ a i) (haSum : ∑ i, a i = 1) (β : ℝ)
    (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) :
    (∑ i, (a i) ^ β) ≤ (Fintype.card ι : ℝ) ^ (1 - β) := by
  classical
  let D : ℝ := Fintype.card ι
  have hD : 0 < D := by
    dsimp [D]
    exact_mod_cast (Fintype.card_pos (α := ι))
  have hweight : (∑ _i : ι, (1 / D : ℝ)) = 1 := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    change D * (1 / D) = 1
    field_simp [hD.ne']
  have hJ := (Real.concaveOn_rpow hβ0 hβ1).le_map_sum
    (t := Finset.univ) (w := fun _i : ι ↦ (1 / D : ℝ)) (p := a)
    (fun _i _ ↦ (div_pos zero_lt_one hD).le) hweight
    (fun i _ ↦ show a i ∈ Set.Ici (0 : ℝ) from ha i)
  have hJ' : (1 / D) * (∑ i, (a i) ^ β) ≤ (1 / D) ^ β := by
    simpa only [smul_eq_mul, ← Finset.mul_sum, haSum, mul_one] using hJ
  have hM := mul_le_mul_of_nonneg_left hJ' hD.le
  calc
    (∑ i, (a i) ^ β) = D * ((1 / D) * (∑ i, (a i) ^ β)) := by
      field_simp [hD.ne']
    _ ≤ D * (1 / D) ^ β := hM
    _ = D ^ (1 - β) := by
      rw [Real.div_rpow (by positivity : (0 : ℝ) ≤ 1) hD.le,
        Real.one_rpow, Real.rpow_sub hD, Real.rpow_one]
      ring

theorem probability_power_sum_pos (a : ι → ℝ)
    (ha : ∀ i, 0 ≤ a i) (haSum : ∑ i, a i = 1) (β : ℝ) :
    0 < ∑ i, (a i) ^ β := by
  classical
  have hex : ∃ i, 0 < a i := by
    by_contra! h
    have hnonpos : (∑ i, a i) ≤ 0 :=
      Finset.sum_nonpos (fun i _ ↦ h i)
    rw [haSum] at hnonpos
    linarith
  obtain ⟨i, hi⟩ := hex
  have hsingle : (a i) ^ β ≤ ∑ j, (a j) ^ β :=
    Finset.single_le_sum (fun j _ ↦ Real.rpow_nonneg (ha j) β) (Finset.mem_univ i)
  exact lt_of_lt_of_le (Real.rpow_pos_of_pos hi β) hsingle

theorem channel_flag_moment_pos (π c : ι → ℝ) (z : ℝ)
    (hπ : ∀ i, 0 ≤ π i) (hπsum : ∑ i, π i = 1) (hc : ∀ i, 0 < c i) :
    0 < ∑ i, π i * (c i) ^ z := by
  classical
  have hex : ∃ i, 0 < π i := by
    by_contra! h
    have hnonpos : (∑ i, π i) ≤ 0 := Finset.sum_nonpos (fun i _ ↦ h i)
    rw [hπsum] at hnonpos
    linarith
  obtain ⟨i, hi⟩ := hex
  have hsingle : π i * (c i) ^ z ≤ ∑ j, π j * (c j) ^ z :=
    Finset.single_le_sum (fun j _ ↦ mul_nonneg (hπ j) (Real.rpow_nonneg (hc j).le z))
      (Finset.mem_univ i)
  exact lt_of_lt_of_le (mul_pos hi (Real.rpow_pos_of_pos (hc i) z)) hsingle

theorem flagPowerCost_eq_renyiFactor (π c μ : ι → ℝ) (α z : ℝ)
    (hπ : ∀ i, 0 ≤ π i) (hc : ∀ i, 0 < c i) (hμ : ∀ i, 0 ≤ μ i)
    (hsupport : ∀ i, μ i = 0 → π i = 0)
    (hα : 1 < α) (hαz : α * z = α - 1) :
    flagPowerCost (fun i ↦ π i * (c i) ^ z) μ α =
      ∑ i, (π i) ^ α * (μ i) ^ (1 - α) * (c i) ^ (α - 1) := by
  classical
  unfold flagPowerCost
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hμ0 : μ i = 0
  · have hπ0 := hsupport i hμ0
    simp [hμ0, hπ0, Real.zero_rpow (by linarith : α ≠ 0)]
  have hμpos : 0 < μ i := lt_of_le_of_ne (hμ i) (Ne.symm hμ0)
  have hb : 0 ≤ π i * (c i) ^ z :=
    mul_nonneg (hπ i) (Real.rpow_nonneg (hc i).le z)
  have hpow : (π i * (c i) ^ z) ^ α = (π i) ^ α * (c i) ^ (α - 1) := by
    rw [Real.mul_rpow (hπ i) (Real.rpow_nonneg (hc i).le z),
      ← Real.rpow_mul (hc i).le, mul_comm z α, hαz]
  rw [Real.div_rpow hb hμpos.le, hpow,
    Real.rpow_sub hμpos, Real.rpow_one]
  ring

theorem optimized_renyi_flag_factor (π c : ι → ℝ) (α z : ℝ)
    (hπ : ∀ i, 0 ≤ π i) (hπsum : ∑ i, π i = 1) (hc : ∀ i, 0 < c i)
    (hα : 1 < α) (hαz : α * z = α - 1) :
    (∑ i, (π i) ^ α *
      (normalizedFlags (fun j ↦ π j * (c j) ^ z) i) ^ (1 - α) *
      (c i) ^ (α - 1)) = (∑ i, π i * (c i) ^ z) ^ α := by
  have hZ := channel_flag_moment_pos π c z hπ hπsum hc
  have hb : ∀ i, 0 ≤ π i * (c i) ^ z :=
    fun i ↦ mul_nonneg (hπ i) (Real.rpow_nonneg (hc i).le z)
  have hsupport : ∀ i, normalizedFlags (fun j ↦ π j * (c j) ^ z) i = 0 → π i = 0 := by
    intro i hi
    have h := normalizedFlags_support (fun j ↦ π j * (c j) ^ z) hZ i hi
    exact (mul_eq_zero.mp h).resolve_right (Real.rpow_pos_of_pos (hc i) z).ne'
  rw [← flagPowerCost_eq_renyiFactor π c _ α z hπ hc
    (normalizedFlags_nonneg _ hb hZ) hsupport hα hαz]
  exact flagPowerCost_normalizedFlags _ α hZ

theorem squared_budget_to_error_bound (G ε δ z budget : ℝ)
    (hε : 0 ≤ ε) (hδ : 0 ≤ δ)
    (hsecurity : (max (1 - ε - δ) 0) ^ 2 ≤ G)
    (hbudget : G ≤ min 1 ((2 : ℝ) ^ (-z * budget))) :
    1 - min 1 ((2 : ℝ) ^ (-(z / 2) * budget)) ≤ ε + δ := by
  let b : ℝ := (2 : ℝ) ^ (-(z / 2) * budget)
  have hb : 0 < b := Real.rpow_pos_of_pos (by norm_num) _
  have hexp : (2 : ℝ) ^ (-z * budget) = b ^ 2 := by
    calc
      (2 : ℝ) ^ (-z * budget) =
          (2 : ℝ) ^ ((-(z / 2) * budget) * (2 : ℝ)) := by congr 1; ring
      _ = ((2 : ℝ) ^ (-(z / 2) * budget)) ^ (2 : ℝ) :=
        Real.rpow_mul (by norm_num) _ _
      _ = b ^ 2 := Real.rpow_natCast b 2
  have hG : G ≤ b ^ 2 := by
    calc
      G ≤ min 1 ((2 : ℝ) ^ (-z * budget)) := hbudget
      _ ≤ (2 : ℝ) ^ (-z * budget) := min_le_right _ _
      _ = b ^ 2 := hexp
  change 1 - min 1 b ≤ ε + δ
  by_cases hsum : 1 ≤ ε + δ
  · have hmin : 0 ≤ min 1 b := le_min (by norm_num) hb.le
    linarith
  have ht0 : 0 ≤ 1 - ε - δ := by linarith
  rw [max_eq_left ht0] at hsecurity
  have ht : 1 - ε - δ ≤ b := by nlinarith [hsecurity, hG, hb]
  have ht1 : 1 - ε - δ ≤ 1 := by linarith
  have hmin := le_min ht1 ht
  linarith

end QuantumProver.AmplitudeDamping.SecretKey.Scalar

import QuantumProver.InformationTheory.Equipartition.TestingBounds
import QuantumProver.InformationTheory.Equipartition.PolarBounds

noncomputable section
open scoped Topology
open Filter
namespace QuantumProver.Equipartition.FiniteModel.EndpointModulus
open Testing

def inverseLog (δ : ℝ) : ℝ := logTwo (1 / δ)

def modulusBlock (κ δ : ℝ) : ℕ := Nat.floor (κ / (δ * inverseLog δ))

theorem inverseLog_ge_one {δ : ℝ} (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2) :
    1 ≤ inverseLog δ := by
  have hi : (2 : ℝ) ≤ 1 / δ := (le_div_iff₀ hδ).mpr (by linarith)
  have h := logTwo_mono_pos (by norm_num : (0 : ℝ) < 2) hi
  simpa only [inverseLog, logTwo, div_self (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'] using h

theorem tendsto_delta_inverseLog :
    Tendsto (fun δ : ℝ => δ * inverseLog δ) (𝓝[>] 0) (𝓝 0) := by
  have h := tendsto_log_mul_rpow_nhdsGT_zero (r := 1) (by norm_num)
  simp only [Real.rpow_one] at h
  have hh : Tendsto (fun δ : ℝ => -(Real.log δ * δ) / Real.log 2)
      (𝓝[>] 0) (𝓝 0) := by
    simpa only [neg_zero, zero_div] using h.neg.div_const (Real.log 2)
  convert hh using 1
  funext δ
  simp only [inverseLog, logTwo, one_div, Real.log_inv]
  ring

theorem modulusBlock_bounds {κ δ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2)
    (hx : 2 ≤ κ / (δ * inverseLog δ)) :
    0 < modulusBlock κ δ ∧
      κ / (2 * δ * inverseLog δ) ≤ (modulusBlock κ δ : ℝ) ∧
      (modulusBlock κ δ : ℝ) ≤ 1 / δ ∧
      blockLog (modulusBlock κ δ) ≤ 2 * inverseLog δ ∧
      δ * (modulusBlock κ δ : ℝ) * blockLog (modulusBlock κ δ) ≤ 2 * κ ∧
      1 / (modulusBlock κ δ : ℝ) ≤ 2 * δ * inverseLog δ / κ := by
  let L := inverseLog δ
  let x := κ / (δ * L)
  let m := modulusBlock κ δ
  have hL : 1 ≤ L := inverseLog_ge_one hδ hδhalf
  have hLp : 0 < L := by linarith
  have hxpos : 0 ≤ x := by dsimp [x]; positivity
  have hfloor : (m : ℝ) ≤ x := Nat.floor_le hxpos
  have hround : x < (m : ℝ) + 1 := Nat.lt_floor_add_one x
  have hx2 : 2 ≤ x := hx
  have hhalf : x / 2 ≤ (m : ℝ) := by linarith
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by linarith
  have hm : 0 < m := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hm1)
  have hlower : κ / (2 * δ * L) ≤ (m : ℝ) := by
    convert hhalf using 1 <;> dsimp [x] <;> ring
  have hxinv : x ≤ 1 / δ := by
    apply (div_le_div_iff₀ (mul_pos hδ hLp) hδ).mpr
    nlinarith
  have hminv : (m : ℝ) ≤ 1 / δ := hfloor.trans hxinv
  have hinv : 1 ≤ 1 / δ := (le_div_iff₀ hδ).mpr (by linarith)
  have hplus : (m : ℝ) + 1 ≤ 2 / δ := by
    calc
      _ ≤ 1 / δ + 1 / δ := add_le_add hminv hinv
      _ = _ := by ring
  have hlog : blockLog m ≤ 1 + L := by
    have hh := logTwo_mono_pos (by positivity : 0 < (m : ℝ) + 1) hplus
    have he : logTwo (2 / δ) = 1 + L := by
      rw [logTwo_div_pos (by norm_num : (0 : ℝ) < 2) hδ]
      dsimp [L, inverseLog]
      rw [logTwo_div_pos (by norm_num : (0 : ℝ) < 1) hδ]
      simp [logTwo, (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne']
      ring
    simpa only [blockLog, he] using hh
  have hlog2 : blockLog m ≤ 2 * L := by linarith
  have hbudget : δ * (m : ℝ) * L ≤ κ := by
    have hh := mul_le_mul_of_nonneg_left hfloor (mul_pos hδ hLp).le
    have he : δ * L * x = κ := by dsimp [x]; field_simp <;> ring
    rw [he] at hh
    nlinarith
  have hwindow : δ * (m : ℝ) * blockLog m ≤ 2 * κ := by
    have hh := mul_le_mul_of_nonneg_left hlog2 (by positivity : 0 ≤ δ * (m : ℝ))
    nlinarith
  have hmpos : 0 < (m : ℝ) := by exact_mod_cast hm
  have hinverse : 1 / (m : ℝ) ≤ 2 * δ * L / κ := by
    calc
      _ ≤ 1 / (κ / (2 * δ * L)) := one_div_le_one_div_of_le (by positivity) hlower
      _ = _ := by field_simp <;> ring
  exact ⟨hm, hlower, hminv, hlog2, hwindow, hinverse⟩

theorem modulusBlock_cost {κ δ G M : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2)
    (hx : 2 ≤ κ / (δ * inverseLog δ)) (hG : 0 ≤ G) (hM : 0 ≤ M) :
    G * blockLog (modulusBlock κ δ) / (modulusBlock κ δ : ℝ) +
      M * δ * (blockLog (modulusBlock κ δ)) ^ 3 ≤
        (4 * G / κ + 8 * M + 1) * δ * (inverseLog δ) ^ 3 := by
  let L := inverseLog δ
  let m := modulusBlock κ δ
  have hb := modulusBlock_bounds hκ hκ1 hδ hδhalf hx
  have hL : 1 ≤ L := inverseLog_ge_one hδ hδhalf
  have hL0 : 0 ≤ L := by linarith
  have hm : 0 < (m : ℝ) := by exact_mod_cast hb.1
  have hLs : L ^ 2 ≤ L ^ 3 := by nlinarith [mul_nonneg (sq_nonneg L) (by linarith : 0 ≤ L - 1)]
  have hfirst : G * blockLog m / (m : ℝ) ≤ (4 * G / κ) * δ * L ^ 3 := by
    calc
      _ = (G * blockLog m) * (1 / (m : ℝ)) := by ring
      _ ≤ (G * (2 * L)) * (2 * δ * L / κ) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hb.2.2.2.1 hG) hb.2.2.2.2.2
          (by positivity) (by positivity)
      _ = (4 * G / κ) * δ * L ^ 2 := by ring
      _ ≤ (4 * G / κ) * δ * L ^ 3 :=
        mul_le_mul_of_nonneg_left hLs (by positivity)
  have hsecond : M * δ * (blockLog m) ^ 3 ≤ (8 * M) * δ * L ^ 3 := by
    have hp := pow_le_pow_left₀ (blockLog_nonneg m) hb.2.2.2.1 3
    have hh := mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ M * δ)
    nlinarith
  calc
    _ ≤ (4 * G / κ) * δ * L ^ 3 + (8 * M) * δ * L ^ 3 := add_le_add hfirst hsecond
    _ = (4 * G / κ + 8 * M) * δ * L ^ 3 := by ring
    _ ≤ (4 * G / κ + 8 * M + 1) * δ * L ^ 3 := by
      nlinarith [mul_nonneg hδ.le (pow_nonneg hL0 3)]

theorem exists_uniform_modulus_schedule {c G M : ℝ} (hc : 0 < c)
    (hG : 0 ≤ G) (hM : 0 ≤ M) (N : ℕ) :
    ∃ κ K ε : ℝ, 0 < κ ∧ 0 < K ∧ 0 < ε ∧ ε ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ < ε →
        N ≤ modulusBlock κ δ ∧ 0 < modulusBlock κ δ ∧
          δ * (modulusBlock κ δ : ℝ) * blockLog (modulusBlock κ δ) ≤ c ∧
          G * blockLog (modulusBlock κ δ) / (modulusBlock κ δ : ℝ) +
            M * δ * (blockLog (modulusBlock κ δ)) ^ 3 ≤ K * δ * (inverseLog δ) ^ 3 := by
  let κ := min (c / 4) (1 / 4 : ℝ)
  have hκ : 0 < κ := lt_min (by positivity) (by norm_num)
  have hκ1 : κ ≤ 1 := (min_le_right _ _).trans (by norm_num)
  have hκc : 2 * κ ≤ c := by
    have hh : κ ≤ c / 4 := min_le_left _ _
    linarith
  let K := 4 * G / κ + 8 * M + 1
  have hK : 0 < K := by dsimp [K]; positivity
  have hthreshold : 0 < κ / (2 * ((N : ℝ) + 1)) := by positivity
  have he : ∀ᶠ δ : ℝ in 𝓝[>] 0,
      δ * inverseLog δ < κ / (2 * ((N : ℝ) + 1)) :=
    tendsto_delta_inverseLog.eventually (gt_mem_nhds hthreshold)
  obtain ⟨ε₀, hε₀, hsmall⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp he
  let ε := min ε₀ (1 / 2 : ℝ)
  have hε : 0 < ε := lt_min hε₀ (by norm_num)
  refine ⟨κ, K, ε, hκ, hK, hε, min_le_right _ _, ?_⟩
  intro δ hδ hδε
  have hδhalf : δ ≤ 1 / 2 := hδε.le.trans (min_le_right _ _)
  have hL : 0 < inverseLog δ := lt_of_lt_of_le zero_lt_one (inverseLog_ge_one hδ hδhalf)
  have hd : 0 < δ * inverseLog δ := mul_pos hδ hL
  have hs := hsmall ⟨hδ, hδε.trans_le (min_le_left _ _)⟩
  have hlarge : 2 * ((N : ℝ) + 1) < κ / (δ * inverseLog δ) := by
    apply (lt_div_iff₀ hd).mpr
    have hh := (lt_div_iff₀ (by positivity : 0 < 2 * ((N : ℝ) + 1))).mp hs
    nlinarith
  have hx : 2 ≤ κ / (δ * inverseLog δ) := by
    nlinarith [(Nat.cast_nonneg N : 0 ≤ (N : ℝ))]
  have hb := modulusBlock_bounds hκ hκ1 hδ hδhalf hx
  have hN : N ≤ modulusBlock κ δ := by
    change N ≤ Nat.floor (κ / (δ * inverseLog δ))
    apply (Nat.le_floor_iff (a := κ / (δ * inverseLog δ)) (by positivity)).mpr
    nlinarith [(Nat.cast_nonneg N : 0 ≤ (N : ℝ))]
  exact ⟨hN, hb.1, hb.2.2.2.2.1.trans hκc, modulusBlock_cost hκ hκ1 hδ hδhalf hx hG hM⟩

theorem scalar_modulus_of_narrow_block {c G M r : ℝ} (hc : 0 < c)
    (hG : 0 ≤ G) (hM : 0 ≤ M) (N : ℕ) (R : ℝ → ℝ)
    (hblock : ∀ δ : ℝ, 0 < δ → δ < 1 / 2 → ∀ n : ℕ,
      N ≤ n → 0 < n → δ * (n : ℝ) * blockLog n ≤ c →
        r - R δ ≤ G * blockLog n / (n : ℝ) + M * δ * (blockLog n) ^ 3) :
    ∃ K ε : ℝ, 0 < K ∧ 0 < ε ∧ ε ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ < ε → r - R δ ≤ K * δ * (inverseLog δ) ^ 3 := by
  obtain ⟨κ, K, ε, _, hK, hε, hεhalf, hs⟩ := exists_uniform_modulus_schedule hc hG hM N
  refine ⟨K, ε, hK, hε, hεhalf, ?_⟩
  intro δ hδ hδε
  have hb := hs δ hδ hδε
  exact (hblock δ hδ (hδε.trans_le hεhalf) _ hb.1 hb.2.1 hb.2.2.1).trans hb.2.2.2

end QuantumProver.Equipartition.FiniteModel.EndpointModulus

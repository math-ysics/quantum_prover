import QuantumProver.InformationTheory.Equipartition.EndpointPetzCoefficient
import QuantumProver.InformationTheory.Equipartition.EndpointModulus

noncomputable section
open scoped Topology ComplexOrder
open Filter
namespace QuantumProver.Equipartition.FiniteModel.FiniteStageBootstrap
open Testing EndpointModulus

def stageGamma (q : ℝ) : ℝ := 1 / (1 + q)

def stageScale (q δ : ℝ) : ℝ :=
  δ ^ (-stageGamma q) * (inverseLog δ) ^ (1 - stageGamma q)

def stageBlock (q δ : ℝ) : ℕ := Nat.floor (stageScale q δ)

def stageModulus (q δ : ℝ) : ℝ := δ ^ (stageGamma q) * (inverseLog δ) ^ (stageGamma q)

theorem stageGamma_bounds {q : ℝ} (hq : 0 < q) (hq1 : q ≤ 1) :
    1 / 2 ≤ stageGamma q ∧ 0 < stageGamma q ∧ stageGamma q < 1 ∧
      1 - stageGamma q > 0 ∧
      1 - stageGamma q * q = stageGamma q ∧
      q * (1 - stageGamma q) + (1 - q) = stageGamma q := by
  have hd : 0 < 1 + q := by linarith
  have he : stageGamma q * (1 + q) = 1 := by
    dsimp [stageGamma]
    exact div_mul_cancel₀ _ hd.ne'
  have hg : 0 < stageGamma q := by dsimp [stageGamma]; positivity
  have hg1 : stageGamma q < 1 := by
    dsimp [stageGamma]
    exact (div_lt_one hd).mpr (by linarith)
  refine ⟨?_, hg, hg1, by linarith, ?_, ?_⟩ <;> nlinarith

theorem delta_stageScale {q δ : ℝ} (hδ : 0 < δ) (hL : 0 < inverseLog δ) :
    δ * stageScale q δ = (δ * inverseLog δ) ^ (1 - stageGamma q) := by
  dsimp [stageScale]
  rw [Real.mul_rpow hδ.le hL.le]
  have he : δ * δ ^ (-stageGamma q) = δ ^ (1 - stageGamma q) := by
    rw [sub_eq_add_neg, Real.rpow_add hδ, Real.rpow_one]
  rw [← he]
  ring

theorem stageScale_modulus_identity {q δ : ℝ} (hδ : 0 < δ)
    (hL : 0 < inverseLog δ) :
    inverseLog δ / stageScale q δ = stageModulus q δ := by
  dsimp [stageScale, stageModulus]
  rw [Real.rpow_neg hδ.le]
  have he : (inverseLog δ) ^ (stageGamma q) *
      (inverseLog δ) ^ (1 - stageGamma q) = inverseLog δ := by
    rw [← Real.rpow_add hL, add_sub_cancel, Real.rpow_one]
  apply (div_eq_iff (by positivity :
    (δ ^ (stageGamma q))⁻¹ * (inverseLog δ) ^ (1 - stageGamma q) ≠ 0)).mpr
  calc
    _ = (δ ^ stageGamma q * (δ ^ stageGamma q)⁻¹) *
        ((inverseLog δ) ^ stageGamma q * (inverseLog δ) ^ (1 - stageGamma q)) := by
      rw [he, mul_inv_cancel₀ (Real.rpow_pos_of_pos hδ _).ne', one_mul]
    _ = _ := by ring

theorem stageBlock_bounds {q δ : ℝ} (hq : 0 < q) (hq1 : q ≤ 1)
    (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2) (hδL : δ * inverseLog δ ≤ 1)
    (hx : 2 ≤ stageScale q δ) :
    0 < stageBlock q δ ∧ stageScale q δ / 2 ≤ (stageBlock q δ : ℝ) ∧
      (stageBlock q δ : ℝ) ≤ stageScale q δ ∧
      (stageBlock q δ : ℝ) ≤ 1 / δ ∧
      blockLog (stageBlock q δ) ≤ 2 * inverseLog δ ∧
      δ * (stageBlock q δ : ℝ) ≤ (δ * inverseLog δ) ^ (1 - stageGamma q) := by
  let m := stageBlock q δ
  let x := stageScale q δ
  have hg := stageGamma_bounds hq hq1
  have hL : 1 ≤ inverseLog δ := inverseLog_ge_one hδ hδhalf
  have hLp : 0 < inverseLog δ := by linarith
  have hx0 : 0 ≤ x := by dsimp [x, stageScale]; positivity
  have hfloor : (m : ℝ) ≤ x := Nat.floor_le hx0
  have hround : x < (m : ℝ) + 1 := Nat.lt_floor_add_one x
  have hhalf : x / 2 ≤ (m : ℝ) := by change 2 ≤ x at hx; linarith
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by change 2 ≤ x at hx; linarith
  have hm : 0 < m := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hm1)
  have hdx : δ * x ≤ 1 := by
    rw [delta_stageScale hδ hLp]
    exact (Real.rpow_le_rpow (mul_nonneg hδ.le hLp.le) hδL hg.2.2.2.1.le).trans_eq
      (Real.one_rpow _)
  have hminv : (m : ℝ) ≤ 1 / δ := hfloor.trans ((le_div_iff₀ hδ).mpr (by nlinarith))
  have hinv : 1 ≤ 1 / δ := (le_div_iff₀ hδ).mpr (by linarith)
  have hplus : (m : ℝ) + 1 ≤ 2 / δ := by
    calc
      _ ≤ 1 / δ + 1 / δ := add_le_add hminv hinv
      _ = _ := by ring
  have hlog : blockLog m ≤ 1 + inverseLog δ := by
    have hh := logTwo_mono_pos (by positivity : 0 < (m : ℝ) + 1) hplus
    have he : logTwo (2 / δ) = 1 + inverseLog δ := by
      rw [logTwo_div_pos (by norm_num : (0 : ℝ) < 2) hδ]
      dsimp [inverseLog]
      rw [logTwo_div_pos (by norm_num : (0 : ℝ) < 1) hδ]
      simp [logTwo, (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne']
      ring
    simpa only [blockLog, he] using hh
  have hwindow : δ * (m : ℝ) ≤ (δ * inverseLog δ) ^ (1 - stageGamma q) := by
    rw [← delta_stageScale hδ hLp]
    exact mul_le_mul_of_nonneg_left hfloor hδ.le
  exact ⟨hm, hhalf, hfloor, hminv, by linarith, hwindow⟩

theorem stageScale_cost_identity {q δ : ℝ} (hq : 0 < q) (hq1 : q ≤ 1)
    (hδ : 0 < δ) (hL : 0 < inverseLog δ) :
    δ * (stageScale q δ) ^ q * (inverseLog δ) ^ (1 - q) = stageModulus q δ := by
  have hg := stageGamma_bounds hq hq1
  dsimp [stageScale, stageModulus]
  rw [Real.mul_rpow (Real.rpow_nonneg hδ.le _) (Real.rpow_nonneg hL.le _),
    ← Real.rpow_mul hδ.le, ← Real.rpow_mul hL.le]
  have heδ : δ * δ ^ (-stageGamma q * q) = δ ^ (stageGamma q) := by
    calc
      _ = δ ^ (1 : ℝ) * δ ^ (-stageGamma q * q) := by rw [Real.rpow_one]
      _ = δ ^ (1 + -stageGamma q * q) := (Real.rpow_add hδ _ _).symm
      _ = _ := by congr 1; nlinarith [hg.2.2.2.2.1]
  have heL : (inverseLog δ) ^ ((1 - stageGamma q) * q) *
      (inverseLog δ) ^ (1 - q) = (inverseLog δ) ^ (stageGamma q) := by
    rw [← Real.rpow_add hL]
    congr 1
    nlinarith [hg.2.2.2.2.2]
  calc
    _ = (δ * δ ^ (-stageGamma q * q)) *
        ((inverseLog δ) ^ ((1 - stageGamma q) * q) * (inverseLog δ) ^ (1 - q)) := by ring
    _ = _ := by rw [heδ, heL]

theorem stageBlock_cost {q δ G B : ℝ} (hq : 0 < q) (hq1 : q ≤ 1)
    (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2) (hδL : δ * inverseLog δ ≤ 1)
    (hx : 2 ≤ stageScale q δ) (hG : 0 ≤ G) (hB : 0 ≤ B) :
    G * blockLog (stageBlock q δ) / (stageBlock q δ : ℝ) +
      B * δ * (stageBlock q δ : ℝ) ^ q * (blockLog (stageBlock q δ)) ^ (1 - q) ≤
        (4 * G + B * 2 ^ (1 - q) + 1) * stageModulus q δ := by
  let m := stageBlock q δ
  let L := inverseLog δ
  let x := stageScale q δ
  have hb := stageBlock_bounds hq hq1 hδ hδhalf hδL hx
  have hL : 0 < L := lt_of_lt_of_le zero_lt_one (inverseLog_ge_one hδ hδhalf)
  have hm : 0 < (m : ℝ) := by exact_mod_cast hb.1
  have hxpos : 0 < x := by dsimp [x, stageScale]; positivity
  have hfirst : G * blockLog m / (m : ℝ) ≤ 4 * G * stageModulus q δ := by
    have hi : 1 / (m : ℝ) ≤ 2 / x := by
      calc
        _ ≤ 1 / (x / 2) := one_div_le_one_div_of_le (by positivity) hb.2.1
        _ = _ := by ring
    calc
      _ = (G * blockLog m) * (1 / (m : ℝ)) := by ring
      _ ≤ (G * (2 * L)) * (2 / x) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hb.2.2.2.2.1 hG) hi (by positivity) (by positivity)
      _ = 4 * G * (L / x) := by ring
      _ = _ := by rw [stageScale_modulus_identity hδ hL]
  have hp : (m : ℝ) ^ q ≤ x ^ q :=
    Real.rpow_le_rpow hm.le hb.2.2.1 hq.le
  have hlog : (blockLog m) ^ (1 - q) ≤ (2 * L) ^ (1 - q) :=
    Real.rpow_le_rpow (blockLog_nonneg m) hb.2.2.2.2.1 (by linarith)
  have hsecond : B * δ * (m : ℝ) ^ q * (blockLog m) ^ (1 - q) ≤
      (B * 2 ^ (1 - q)) * stageModulus q δ := by
    calc
      _ ≤ (B * δ * x ^ q) * (2 * L) ^ (1 - q) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hp (by positivity)) hlog
          (Real.rpow_nonneg (blockLog_nonneg m) _) (by positivity)
      _ = (B * 2 ^ (1 - q)) * (δ * x ^ q * L ^ (1 - q)) := by
        rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hL.le]
        ring
      _ = _ := by rw [stageScale_cost_identity hq hq1 hδ hL]
  have hmod : 0 ≤ stageModulus q δ := by dsimp [stageModulus]; positivity
  nlinarith

theorem tendsto_stageScale {q : ℝ} (hq : 0 < q) (hq1 : q ≤ 1) :
    Tendsto (stageScale q) (𝓝[>] 0) atTop := by
  have hg := stageGamma_bounds hq hq1
  have hpow := tendsto_rpow_neg_nhdsGT_zero (show -stageGamma q < 0 by linarith [hg.2.1])
  have hehalf : ∀ᶠ δ : ℝ in 𝓝[>] 0, δ < 1 / 2 :=
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2)).filter_mono nhdsWithin_le_nhds
  apply tendsto_atTop_mono' (𝓝[>] 0) _ hpow
  filter_upwards [self_mem_nhdsWithin, hehalf] with δ hδ hhalf
  have hL := inverseLog_ge_one hδ hhalf.le
  have hone := Real.one_le_rpow hL hg.2.2.2.1.le
  dsimp [stageScale]
  exact le_mul_of_one_le_right (Real.rpow_nonneg hδ.le _) hone

theorem tendsto_delta_stageScale {q : ℝ} (hq : 0 < q) (hq1 : q ≤ 1) :
    Tendsto (fun δ : ℝ => δ * stageScale q δ) (𝓝[>] 0) (𝓝 0) := by
  have hg := stageGamma_bounds hq hq1
  have hp : Tendsto (fun δ : ℝ => (δ * inverseLog δ) ^ (1 - stageGamma q))
      (𝓝[>] 0) (𝓝 0) := by
    have hh := ((Real.continuous_rpow_const hg.2.2.2.1.le).continuousAt
      (x := (0 : ℝ))).tendsto.comp tendsto_delta_inverseLog
    change Tendsto (fun δ : ℝ => (δ * inverseLog δ) ^ (1 - stageGamma q))
      (𝓝[>] 0) (𝓝 ((0 : ℝ) ^ (1 - stageGamma q))) at hh
    rwa [Real.zero_rpow hg.2.2.2.1.ne'] at hh
  have hehalf : ∀ᶠ δ : ℝ in 𝓝[>] 0, δ < 1 / 2 :=
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2)).filter_mono nhdsWithin_le_nhds
  apply hp.congr'
  filter_upwards [self_mem_nhdsWithin, hehalf] with δ hδ hhalf
  exact (delta_stageScale hδ (lt_of_lt_of_le zero_lt_one (inverseLog_ge_one hδ hhalf.le))).symm

theorem exists_uniform_stage_schedule {q c G B : ℝ} (hq : 0 < q) (hq1 : q ≤ 1)
    (hc : 0 < c) (hG : 0 ≤ G) (hB : 0 ≤ B) (N : ℕ) :
    ∃ K ε : ℝ, 0 < K ∧ 0 < ε ∧ ε ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ < ε → N ≤ stageBlock q δ ∧ 0 < stageBlock q δ ∧
        δ * (stageBlock q δ : ℝ) ≤ c ∧
        G * blockLog (stageBlock q δ) / (stageBlock q δ : ℝ) +
          B * δ * (stageBlock q δ : ℝ) ^ q * (blockLog (stageBlock q δ)) ^ (1 - q) ≤
            K * stageModulus q δ := by
  have heLarge : ∀ᶠ δ : ℝ in 𝓝[>] 0,
      2 * ((N : ℝ) + 1) ≤ stageScale q δ :=
    (tendsto_stageScale hq hq1).eventually_ge_atTop _
  have heWindow : ∀ᶠ δ : ℝ in 𝓝[>] 0, δ * stageScale q δ < c :=
    (tendsto_delta_stageScale hq hq1).eventually (gt_mem_nhds hc)
  have heLog : ∀ᶠ δ : ℝ in 𝓝[>] 0, δ * inverseLog δ < 1 :=
    tendsto_delta_inverseLog.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  obtain ⟨ε₀, hε₀, hs⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp
    (heLarge.and (heWindow.and heLog))
  let ε := min ε₀ (1 / 2 : ℝ)
  let K := 4 * G + B * 2 ^ (1 - q) + 1
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨K, ε, hK, lt_min hε₀ (by norm_num), min_le_right _ _, ?_⟩
  intro δ hδ hδε
  have hδhalf : δ ≤ 1 / 2 := hδε.le.trans (min_le_right _ _)
  have hh : 2 * ((N : ℝ) + 1) ≤ stageScale q δ ∧
      δ * stageScale q δ < c ∧ δ * inverseLog δ < 1 :=
    hs ⟨hδ, hδε.trans_le (min_le_left _ _)⟩
  have hx : 2 ≤ stageScale q δ := by nlinarith [hh.1, (Nat.cast_nonneg N : 0 ≤ (N : ℝ))]
  have hb := stageBlock_bounds hq hq1 hδ hδhalf hh.2.2.le hx
  have hN : N ≤ stageBlock q δ := by
    change N ≤ Nat.floor (stageScale q δ)
    apply (Nat.le_floor_iff (a := stageScale q δ) (by positivity [stageScale])).mpr
    nlinarith [hh.1, (Nat.cast_nonneg N : 0 ≤ (N : ℝ))]
  have hwindow : δ * (stageBlock q δ : ℝ) ≤ c :=
    (mul_le_mul_of_nonneg_left hb.2.2.1 hδ.le).trans hh.2.1.le
  exact ⟨hN, hb.1, hwindow, stageBlock_cost hq hq1 hδ hδhalf hh.2.2.le hx hG hB⟩

theorem scalar_stage_modulus {q c G B r : ℝ} (hq : 0 < q) (hq1 : q ≤ 1)
    (hc : 0 < c) (hG : 0 ≤ G) (hB : 0 ≤ B) (N : ℕ) (R : ℝ → ℝ)
    (hblock : ∀ δ : ℝ, 0 < δ → δ < 1 / 2 → ∀ m : ℕ, N ≤ m → 0 < m →
      δ * (m : ℝ) ≤ c → r - R δ ≤ G * blockLog m / (m : ℝ) +
        B * δ * (m : ℝ) ^ q * (blockLog m) ^ (1 - q)) :
    ∃ K ε : ℝ, 0 < K ∧ 0 < ε ∧ ε ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ < ε → r - R δ ≤ K * stageModulus q δ := by
  obtain ⟨K, ε, hK, hε, hhalf, hs⟩ := exists_uniform_stage_schedule hq hq1 hc hG hB N
  refine ⟨K, ε, hK, hε, hhalf, ?_⟩
  intro δ hδ hδε
  have hb := hs δ hδ hδε
  exact (hblock δ hδ (hδε.trans_le hhalf) _ hb.1 hb.2.1 hb.2.2.1).trans hb.2.2.2

theorem stageModulus_inverse_eight {q : ℝ} (hq : 0 < q) (hq1 : q ≤ 1)
    {n : ℕ} (hn : 1 ≤ n) :
    stageModulus q (1 / (8 * (n : ℝ))) ≤
      (n : ℝ) ^ (-stageGamma q) * (blockLog n) ^ (stageGamma q) := by
  let δ := 1 / (8 * (n : ℝ))
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hn1 : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδhalf : δ ≤ 1 / 2 := by
    dsimp [δ]
    apply (div_le_iff₀ (by positivity : 0 < 8 * (n : ℝ))).mpr
    nlinarith
  have hLδ : 0 < inverseLog δ := lt_of_lt_of_le zero_lt_one (inverseLog_ge_one hδ hδhalf)
  have hInv : 1 / δ = 8 * (n : ℝ) := by dsimp [δ]; field_simp [hnR.ne']
  have hEight : logTwo 8 = 3 := by
    unfold logTwo
    rw [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, Real.log_pow]
    norm_num
  have hL := blockLog_ge_one hn
  have hLbound : inverseLog δ ≤ 4 * blockLog n := by
    have hh := logTwo_mono_pos (by positivity : 0 < 8 * (n : ℝ))
      (show 8 * (n : ℝ) ≤ 8 * ((n : ℝ) + 1) by nlinarith)
    rw [logTwo_mul_pos (by norm_num : (0 : ℝ) < 8)
      (by positivity : 0 < (n : ℝ) + 1), hEight] at hh
    change logTwo (8 * (n : ℝ)) ≤ 3 + blockLog n at hh
    unfold inverseLog
    rw [hInv]
    linarith
  have hprod : δ * inverseLog δ ≤ blockLog n / (n : ℝ) := by
    have hh := mul_le_mul_of_nonneg_left hLbound hδ.le
    have hid : δ * (4 * blockLog n) = blockLog n / (2 * (n : ℝ)) := by
      dsimp [δ]
      field_simp [hnR.ne'] <;> ring
    rw [hid] at hh
    refine hh.trans ?_
    apply (div_le_div_iff₀ (by positivity : 0 < 2 * (n : ℝ)) hnR).mpr
    nlinarith [mul_nonneg (blockLog_nonneg n) hnR.le]
  have hg := stageGamma_bounds hq hq1
  have hp := Real.rpow_le_rpow (mul_nonneg hδ.le hLδ.le) hprod hg.2.1.le
  have hid : stageModulus q δ = (δ * inverseLog δ) ^ (stageGamma q) := by
    dsimp [stageModulus]
    rw [Real.mul_rpow hδ.le hLδ.le]
  rw [hid]
  refine hp.trans_eq ?_
  rw [Real.div_rpow (blockLog_nonneg n) hnR.le, Real.rpow_neg hnR.le]
  ring

def stageLengthPower (γ : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) ^ (2 - γ) * (blockLog n) ^ γ

def stageLaplaceBudget (A γ : ℝ) (n : ℕ) : ℝ :=
  A * (n : ℝ) ^ (-γ) * (blockLog n) ^ γ

def stageNSCoefficient (C A ζ : ℝ) : ℝ :=
  6 * Real.exp (8 * ζ * (C + 1) / 3) * A / ζ ^ 2 +
    2 * Real.exp (8 * ζ * (C + 1) / 3) / ζ + EndpointPetzCoefficient.tailConstant + 1

theorem stageLengthPower_ge_one {γ : ℝ} (hγ : 0 ≤ γ) (hγ1 : γ ≤ 1)
    {n : ℕ} (hn : 1 ≤ n) : 1 ≤ stageLengthPower γ n := by
  have hnR : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hLn := blockLog_ge_one hn
  have hfirst := Real.one_le_rpow hnR (show 0 ≤ 2 - γ by linarith)
  have hsecond := Real.one_le_rpow hLn hγ
  dsimp [stageLengthPower]
  nlinarith [mul_le_mul hfirst hsecond (by norm_num : (0 : ℝ) ≤ 1)
    (Real.rpow_nonneg (Nat.cast_nonneg n) (2 - γ))]

theorem stageLaplaceBudget_power_identity {A γ : ℝ} {n : ℕ} (hn : 0 < n) :
    (n : ℝ) ^ 2 * stageLaplaceBudget A γ n = A * stageLengthPower γ n := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hp : (n : ℝ) ^ (2 : ℕ) * (n : ℝ) ^ (-γ) = (n : ℝ) ^ (2 - γ) := by
    rw [← Real.rpow_two, ← Real.rpow_add hnR, sub_eq_add_neg]
  dsimp [stageLaplaceBudget, stageLengthPower]
  calc
    _ = A * ((n : ℝ) ^ (2 : ℕ) * (n : ℝ) ^ (-γ)) * (blockLog n) ^ γ := by ring
    _ = _ := by rw [hp]; ring

theorem stageLaplaceBudget_eventually_le_one {A γ : ℝ} (hA : 0 ≤ A) (hγ : 0 < γ) :
    ∀ᶠ n : ℕ in atTop, stageLaplaceBudget A γ n ≤ 1 := by
  let η : ℝ := (1 / (A + 1)) ^ (1 / γ)
  have hη : 0 < η := by dsimp [η]; positivity
  have hηpow : η ^ γ = 1 / (A + 1) := by
    dsimp [η]
    simpa only [one_div] using Real.rpow_inv_rpow (by positivity : 0 ≤ 1 / (A + 1)) hγ.ne'
  filter_upwards [blockLog_square_eventually_le_sqrt hη, eventually_ge_atTop (1 : ℕ)]
    with n hbound hn
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hn1 : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hL := blockLog_ge_one hn
  have hsqrt : Real.sqrt (n : ℝ) ≤ (n : ℝ) := by
    nlinarith [Real.sq_sqrt hnR.le, Real.sqrt_nonneg (n : ℝ)]
  have hratio : blockLog n / (n : ℝ) ≤ η := by
    apply (div_le_iff₀ hnR).mpr
    nlinarith [mul_le_mul_of_nonneg_left hsqrt hη.le]
  have hp := Real.rpow_le_rpow (div_nonneg (blockLog_nonneg n) hnR.le) hratio hγ.le
  have hid : stageLaplaceBudget A γ n = A * (blockLog n / (n : ℝ)) ^ γ := by
    dsimp [stageLaplaceBudget]
    rw [Real.div_rpow (blockLog_nonneg n) hnR.le, Real.rpow_neg hnR.le]
    ring
  rw [hηpow] at hp
  rw [hid]
  calc
    _ ≤ A * (1 / (A + 1)) := mul_le_mul_of_nonneg_left hp hA
    _ ≤ 1 := by
      simpa only [one_div, div_eq_mul_inv, one_mul] using
        (div_le_one (by positivity : 0 < A + 1)).mpr (show A ≤ A + 1 by linarith)

theorem matrix_stage_ns_moment {ι : Type*} [Fintype ι] [DecidableEq ι]
    {ρ σ : CMat ι} (hρ : IsState ρ) (hσ : σ.PosSemidef)
    {C A ζ γ center t : ℝ} (hC : 0 ≤ C) (hA : 0 ≤ A) (hζ : 0 < ζ)
    (hζSmall : ζ ≤ Real.log 2 / 8) (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    {n : ℕ} (hn : 1 ≤ n)
    (hdom : LoewnerLE ρ (Real.rpow 2 (C * (n : ℝ)) • σ))
    (hcenter : -(C * (n : ℝ)) ≤ center)
    (hmean : 0 ≤ umegakiReal ρ σ - center)
    (ht : 0 ≤ t) (ht3 : t ≤ (ζ / (n : ℝ)) / 3)
    (ha1 : stageLaplaceBudget A γ n ≤ 1)
    (hLap : (nsLaw ρ σ hρ hσ).expect
      (fun z => Real.exp (-(ζ / (n : ℝ)) * (nsLikelihood ρ σ z - center))) ≤
        Real.exp (stageLaplaceBudget A γ n)) :
    nsWeightedMoment ρ σ center t ≤ stageNSCoefficient C A ζ *
      ((n : ℝ) * (umegakiReal ρ σ - center) + stageLengthPower γ n) := by
  let a := stageLaplaceBudget A γ n
  let s := umegakiReal ρ σ - center
  let E := Real.exp (8 * ζ * (C + 1) / 3)
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hn1 : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have ht0 : 0 < ζ / (n : ℝ) := div_pos hζ hnR
  have hsmall : ζ / (n : ℝ) ≤ ζ := by
    apply (div_le_iff₀ hnR).mpr
    nlinarith
  have htBeta : t ≤ Real.log 2 / 16 := by linarith
  have hLn : 0 ≤ blockLog n := blockLog_nonneg n
  have ha : 0 ≤ a := by dsimp [a, stageLaplaceBudget]; positivity
  have hB := nsWeightedMoment_le_laplace_budget hρ hσ hC n hdom hcenter
    ht ht0 ht3 htBeta ha ha1 hLap
  have he : 8 * (ζ / (n : ℝ)) * (C + 1) * (n : ℝ) / 3 =
      8 * ζ * (C + 1) / 3 := by field_simp [hnR.ne'] <;> ring
  rw [he] at hB
  have hcurv : a * (1 + 2 * a) + (ζ / (n : ℝ)) * s ≤
      3 * a + (ζ / (n : ℝ)) * s := by
    have ha1' : a ≤ 1 := ha1
    nlinarith [mul_nonneg ha (by linarith : 0 ≤ 1 - a)]
  have hcoef : (2 * E / (ζ / (n : ℝ)) ^ 2) *
      (3 * a + (ζ / (n : ℝ)) * s) =
        (6 * E * A / ζ ^ 2) * stageLengthPower γ n + (2 * E / ζ) * (n : ℝ) * s := by
    have hid := stageLaplaceBudget_power_identity (A := A) (γ := γ) (by omega : 0 < n)
    have hsplit : (2 * E / (ζ / (n : ℝ)) ^ 2) *
        (3 * a + (ζ / (n : ℝ)) * s) =
      (6 * E / ζ ^ 2) * ((n : ℝ) ^ 2 * a) + (2 * E / ζ) * (n : ℝ) * s := by
      field_simp [hζ.ne', hnR.ne'] <;> ring
    rw [hsplit]
    change (n : ℝ) ^ 2 * a = A * stageLengthPower γ n at hid
    rw [hid]
    ring
  have hW := stageLengthPower_ge_one hγ.le hγ1 hn
  have htail : EndpointCurvature.matrixTailBudget n ≤
      EndpointPetzCoefficient.tailConstant * stageLengthPower γ n := by
    exact (EndpointPetzCoefficient.matrixTailBudget_le_constant n).trans
      (by simpa only [mul_one] using (mul_le_mul_of_nonneg_left hW
        (show 0 ≤ EndpointPetzCoefficient.tailConstant by
          unfold EndpointPetzCoefficient.tailConstant; positivity)))
  have hmain := mul_le_mul_of_nonneg_left hcurv
    (show 0 ≤ 2 * E / (ζ / (n : ℝ)) ^ 2 by positivity)
  rw [hcoef] at hmain
  have htotal := hB.trans (add_le_add hmain htail)
  have hW0 : 0 ≤ stageLengthPower γ n := by linarith
  have hs0 : 0 ≤ (n : ℝ) * s := mul_nonneg hnR.le hmean
  have hK1 : 0 ≤ 6 * E * A / ζ ^ 2 := by positivity
  have hK2 : 0 ≤ 2 * E / ζ := by positivity
  have hKtail : 0 ≤ EndpointPetzCoefficient.tailConstant := by
    unfold EndpointPetzCoefficient.tailConstant
    positivity
  dsimp [stageNSCoefficient]
  change nsWeightedMoment ρ σ center t ≤
    (6 * E * A / ζ ^ 2 + 2 * E / ζ + EndpointPetzCoefficient.tailConstant + 1) *
      ((n : ℝ) * s + stageLengthPower γ n)
  nlinarith [mul_nonneg hK1 hs0, mul_nonneg hK2 hW0,
    mul_nonneg hKtail hs0]

theorem stageNSCoefficient_pos {C A ζ : ℝ} (hA : 0 ≤ A) (hζ : 0 < ζ) :
    0 < stageNSCoefficient C A ζ := by
  unfold stageNSCoefficient EndpointPetzCoefficient.tailConstant
  positivity

def stagePetzCoefficient (C A ζ : ℝ) : ℝ := Real.log 2 * stageNSCoefficient C A ζ / 2

def stagePetzWindow (C A ζ : ℝ) : ℝ :=
  min (1 / 2) (min (ζ / (3 * Real.log 2)) (1 / (stageNSCoefficient C A ζ * Real.log 2)))

theorem stagePetz_constants {C A ζ : ℝ} (hA : 0 ≤ A) (hζ : 0 < ζ) :
    0 < stagePetzCoefficient C A ζ ∧ 0 < stagePetzWindow C A ζ ∧
      stagePetzWindow C A ζ ≤ 1 / 2 := by
  have hK := stageNSCoefficient_pos (C := C) hA hζ
  dsimp [stagePetzCoefficient, stagePetzWindow]
  exact ⟨by positivity, by positivity, min_le_left _ _⟩

private theorem ns_mean_center {ι : Type*} [Fintype ι] [DecidableEq ι]
    {ρ σ : CMat ι} (hρ : IsState ρ) (hσ : σ.PosSemidef) (center : ℝ) :
    (nsLaw ρ σ hρ hσ).mean (fun z => nsLikelihood ρ σ z - center) =
      umegakiReal ρ σ - center := by
  change (nsLaw ρ σ hρ hσ).expect (fun z => nsLikelihood ρ σ z - center) = _
  rw [FiniteLaw.expect_sub, FiniteLaw.expect_const]
  exact congrArg (fun x : ℝ => x - center) (nsLaw_mean_eq_umegakiReal ρ σ hρ hσ)

private theorem ns_secondMoment_center {ι : Type*} [Fintype ι] [DecidableEq ι]
    {ρ σ : CMat ι} (hρ : IsState ρ) (hσ : σ.PosSemidef) (center t : ℝ) :
    (nsLaw ρ σ hρ hσ).weightedSecondMoment (fun z => nsLikelihood ρ σ z - center) 0 t =
      nsWeightedMoment ρ σ center t := by
  simp only [nsWeightedMoment, nsExpectation, FiniteLaw.weightedSecondMoment,
    FiniteLaw.expect, nsLaw, sub_zero]

theorem matrix_stage_negative_laplace {ι : Type*} [Fintype ι] [DecidableEq ι]
    {ρ σ : CMat ι} (hρ : IsState ρ) (hσ : σ.PosSemidef)
    {K γ center t : ℝ} {n : ℕ} (hmean : 0 ≤ umegakiReal ρ σ - center)
    (ht : 0 ≤ t) (hwindow : t * K * (n : ℝ) ≤ 1)
    (hw : nsWeightedMoment ρ σ center t ≤
      K * ((n : ℝ) * (umegakiReal ρ σ - center) + stageLengthPower γ n)) :
    (nsLaw ρ σ hρ hσ).expect
      (fun z => Real.exp (-t * (nsLikelihood ρ σ z - center))) ≤
        Real.exp (t ^ 2 / 2 * K * stageLengthPower γ n) := by
  let P := nsLaw ρ σ hρ hσ
  let X := fun z => nsLikelihood ρ σ z - center
  let s := umegakiReal ρ σ - center
  have hm : P.mean X = s := ns_mean_center hρ hσ center
  have hww : P.weightedSecondMoment X 0 t ≤ K * ((n : ℝ) * s + stageLengthPower γ n) := by
    rw [ns_secondMoment_center]
    exact hw
  have hcoef : -t + t ^ 2 / 2 * K * (n : ℝ) ≤ 0 := by
    nlinarith [mul_le_mul_of_nonneg_left hwindow ht]
  have hTaylor := P.laplace_taylor_upper X ht
  rw [hm] at hTaylor
  have hbudget := mul_le_mul_of_nonneg_left hww (show 0 ≤ t ^ 2 / 2 by positivity)
  have hsurplus : (-t + t ^ 2 / 2 * K * (n : ℝ)) * s ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg hcoef hmean
  have hb : P.expect (fun z => Real.exp (-t * X z)) ≤
      1 + t ^ 2 / 2 * K * stageLengthPower γ n := by nlinarith
  exact hb.trans (by simpa only [add_comm] using
    Real.add_one_le_exp (t ^ 2 / 2 * K * stageLengthPower γ n))

theorem matrix_stage_positive_laplace {ι : Type*} [Fintype ι] [DecidableEq ι]
    {ρ σ : CMat ι} (hρ : IsState ρ) (hσ : σ.PosSemidef)
    {K γ center t : ℝ} {n : ℕ} (ht : 0 ≤ t)
    (hw : nsWeightedMoment ρ σ center t ≤
      K * ((n : ℝ) * (umegakiReal ρ σ - center) + stageLengthPower γ n)) :
    (nsLaw ρ σ hρ hσ).expect
      (fun z => Real.exp (t * (nsLikelihood ρ σ z - center))) ≤
        Real.exp (t * (umegakiReal ρ σ - center) + t ^ 2 / 2 * K *
          ((n : ℝ) * (umegakiReal ρ σ - center) + stageLengthPower γ n)) := by
  let P := nsLaw ρ σ hρ hσ
  let X := fun z => nsLikelihood ρ σ z - center
  have hm := ns_mean_center hρ hσ center
  have hTaylor := P.positive_laplace_taylor_upper X ht
  rw [hm] at hTaylor
  have hbudget := mul_le_mul_of_nonneg_left hw (show 0 ≤ t ^ 2 / 2 by positivity)
  rw [← ns_secondMoment_center hρ hσ center t] at hbudget
  have hb : P.expect (fun z => Real.exp (t * X z)) ≤ 1 +
      (t * (umegakiReal ρ σ - center) + t ^ 2 / 2 * K *
        ((n : ℝ) * (umegakiReal ρ σ - center) + stageLengthPower γ n)) := by nlinarith
  exact hb.trans (by simpa only [add_comm] using (Real.add_one_le_exp
    (t * (umegakiReal ρ σ - center) + t ^ 2 / 2 * K *
      ((n : ℝ) * (umegakiReal ρ σ - center) + stageLengthPower γ n))))

theorem matrix_stage_petz_bounds {ι : Type*} [Fintype ι] [DecidableEq ι]
    {ρ σ : CMat ι} (hρ : IsState ρ) (hσ : σ.PosSemidef)
    {C A ζ γ center δ : ℝ} (hC : 0 ≤ C) (hA : 0 ≤ A) (hζ : 0 < ζ)
    (hζSmall : ζ ≤ Real.log 2 / 8) (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    {n : ℕ} (hn : 1 ≤ n)
    (hdom : LoewnerLE ρ (Real.rpow 2 (C * (n : ℝ)) • σ))
    (hcenter : -(C * (n : ℝ)) ≤ center)
    (hmean : 0 ≤ umegakiReal ρ σ - center)
    (ha1 : stageLaplaceBudget A γ n ≤ 1)
    (hLap : (nsLaw ρ σ hρ hσ).expect
      (fun z => Real.exp (-(ζ / (n : ℝ)) * (nsLikelihood ρ σ z - center))) ≤
        Real.exp (stageLaplaceBudget A γ n))
    (hδ : 0 < δ) (hwindow : δ * (n : ℝ) ≤ stagePetzWindow C A ζ) :
    (((center - stagePetzCoefficient C A ζ * δ * stageLengthPower γ n : ℝ) : EReal) ≤
      petzDivergence ρ σ (1 - δ)) ∧
    (petzDivergence ρ σ (1 + δ) ≤
      ((umegakiReal ρ σ + stagePetzCoefficient C A ζ * δ *
        ((n : ℝ) * (umegakiReal ρ σ - center) + stageLengthPower γ n) : ℝ) : EReal)) := by
  let t := δ * Real.log 2
  let K := stageNSCoefficient C A ζ
  have hK : 0 < K := stageNSCoefficient_pos hA hζ
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hn1 : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have ht : 0 < t := by dsimp [t]; positivity
  have hwδ : δ * (n : ℝ) ≤ 1 / 2 := hwindow.trans (min_le_left _ _)
  have hδhalf : δ ≤ 1 / 2 := by nlinarith
  have ht3 : t ≤ (ζ / (n : ℝ)) / 3 := by
    have hwin := hwindow.trans ((min_le_right _ _).trans (min_le_left _ _))
    have hh := (le_div_iff₀ (by positivity : 0 < 3 * Real.log 2)).mp hwin
    rw [div_div]
    apply (le_div_iff₀ (by positivity : 0 < (n : ℝ) * 3)).mpr
    dsimp [t]
    nlinarith
  have htK : t * K * (n : ℝ) ≤ 1 := by
    have hwin := hwindow.trans ((min_le_right _ _).trans (min_le_right _ _))
    have hh := (le_div_iff₀ (by positivity : 0 < K * Real.log 2)).mp hwin
    dsimp [t]
    nlinarith
  have hw := matrix_stage_ns_moment hρ hσ hC hA hζ hζSmall hγ hγ1 hn hdom hcenter hmean
    ht.le ht3 ha1 hLap
  have hneg := matrix_stage_negative_laplace hρ hσ hmean ht.le htK hw
  have hpos := matrix_stage_positive_laplace hρ hσ ht.le hw
  have hs := supportLE_of_real_psd_domination hρ.1 hdom
  have horder : t / Real.log 2 = δ := by dsimp [t]; exact mul_div_cancel_right₀ _ hlog.ne'
  have ha : 0 < 1 - t / Real.log 2 := by rw [horder]; linarith
  have hl := EndpointCurvature.petz_lower_of_negative_laplace hρ hσ hs center ht ha hneg
  have hu := EndpointCurvature.petz_upper_of_positive_laplace hρ hσ hs center ht hpos
  have hlcost : (t ^ 2 / 2 * K * stageLengthPower γ n) / t =
      stagePetzCoefficient C A ζ * δ * stageLengthPower γ n := by
    dsimp [stagePetzCoefficient, t, K]
    field_simp [hδ.ne', hlog.ne'] <;> ring
  have hucost : (t * (umegakiReal ρ σ - center) + t ^ 2 / 2 * K *
      ((n : ℝ) * (umegakiReal ρ σ - center) + stageLengthPower γ n)) / t =
    (umegakiReal ρ σ - center) + stagePetzCoefficient C A ζ * δ *
      ((n : ℝ) * (umegakiReal ρ σ - center) + stageLengthPower γ n) := by
    dsimp [stagePetzCoefficient, t, K]
    field_simp [hδ.ne', hlog.ne'] <;> ring
  rw [horder, hlcost] at hl
  rw [horder, hucost] at hu
  refine ⟨hl, ?_⟩
  convert hu using 1 <;> congr 1 <;> ring

def stageLogCoefficient : ℝ := 1 / Real.log 2

theorem stageLengthPower_dominates_mean {γ : ℝ} (hγ : 0 ≤ γ) (hγ1 : γ ≤ 1)
    {n : ℕ} (hn : 1 ≤ n) :
    (n : ℝ) * blockLog n ≤ stageLogCoefficient * stageLengthPower γ n := by
  let D := stageLogCoefficient
  let L := blockLog n
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hL : 0 < L := lt_of_lt_of_le zero_lt_one (blockLog_ge_one hn)
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hD : 0 < D := by dsimp [D, stageLogCoefficient]; positivity
  have hD1 : 1 ≤ D := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    dsimp [D, stageLogCoefficient]
    apply (le_div_iff₀ hlog).mpr
    norm_num at hh ⊢
    exact hh
  have hLn : L ≤ D * (n : ℝ) := by
    have hh := Real.log_le_sub_one_of_pos (by positivity : 0 < (n : ℝ) + 1)
    have hh' : Real.log ((n : ℝ) + 1) ≤ (n : ℝ) := by simpa only [add_sub_cancel_right] using hh
    dsimp [L, blockLog, logTwo, D, stageLogCoefficient]
    simpa only [one_div, mul_comm, div_eq_mul_inv, one_mul] using div_le_div_of_nonneg_right hh' hlog.le
  have hp : L ^ (1 - γ) ≤ D * (n : ℝ) ^ (1 - γ) := by
    have hh := Real.rpow_le_rpow hL.le hLn (show 0 ≤ 1 - γ by linarith)
    rw [Real.mul_rpow hD.le hnR.le] at hh
    have hdpow : D ^ (1 - γ) ≤ D := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hD1
        (show 1 - γ ≤ 1 by linarith)
    exact hh.trans (mul_le_mul_of_nonneg_right hdpow (Real.rpow_nonneg hnR.le _))
  have hLid : L ^ γ * L ^ (1 - γ) = L := by
    rw [← Real.rpow_add hL, add_sub_cancel, Real.rpow_one]
  have hnid : (n : ℝ) * (n : ℝ) ^ (1 - γ) = (n : ℝ) ^ (2 - γ) := by
    calc
      _ = (n : ℝ) ^ (1 : ℝ) * (n : ℝ) ^ (1 - γ) := by rw [Real.rpow_one]
      _ = (n : ℝ) ^ (1 + (1 - γ)) := (Real.rpow_add hnR _ _).symm
      _ = _ := by congr 1; ring
  calc
    _ = (n : ℝ) * (L ^ γ * L ^ (1 - γ)) := by rw [hLid]
    _ ≤ (n : ℝ) * (L ^ γ * (D * (n : ℝ) ^ (1 - γ))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hp (Real.rpow_nonneg hL.le _)) hnR.le
    _ = D * ((n : ℝ) * (n : ℝ) ^ (1 - γ)) * L ^ γ := by ring
    _ = _ := by rw [hnid]; dsimp [D, L, stageLengthPower]; ring

theorem matrix_stage_petz_mean_bounded {ι : Type*} [Fintype ι] [DecidableEq ι]
    {ρ σ : CMat ι} (hρ : IsState ρ) (hσ : σ.PosSemidef)
    {C A G ζ γ center δ : ℝ} (hC : 0 ≤ C) (hA : 0 ≤ A) (hG : 0 ≤ G) (hζ : 0 < ζ)
    (hζSmall : ζ ≤ Real.log 2 / 8) (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    {n : ℕ} (hn : 1 ≤ n)
    (hdom : LoewnerLE ρ (Real.rpow 2 (C * (n : ℝ)) • σ))
    (hcenter : -(C * (n : ℝ)) ≤ center)
    (hmean : 0 ≤ umegakiReal ρ σ - center)
    (hmeanUpper : umegakiReal ρ σ - center ≤ G * blockLog n)
    (ha1 : stageLaplaceBudget A γ n ≤ 1)
    (hLap : (nsLaw ρ σ hρ hσ).expect
      (fun z => Real.exp (-(ζ / (n : ℝ)) * (nsLikelihood ρ σ z - center))) ≤
        Real.exp (stageLaplaceBudget A γ n))
    (hδ : 0 < δ) (hwindow : δ * (n : ℝ) ≤ stagePetzWindow C A ζ) :
    petzDivergence ρ σ (1 + δ) ≤
      ((center + G * blockLog n +
        (stagePetzCoefficient C A ζ * (1 + G * stageLogCoefficient)) *
          δ * stageLengthPower γ n : ℝ) : EReal) := by
  have hu := (matrix_stage_petz_bounds hρ hσ hC hA hζ hζSmall hγ hγ1 hn hdom hcenter hmean
    ha1 hLap hδ hwindow).2
  have hK : 0 ≤ stagePetzCoefficient C A ζ * δ :=
    mul_nonneg (stagePetz_constants (C := C) hA hζ).1.le hδ.le
  have hmeanN : (n : ℝ) * (umegakiReal ρ σ - center) ≤
      G * stageLogCoefficient * stageLengthPower γ n := by
    have hm := mul_le_mul_of_nonneg_left hmeanUpper (Nat.cast_nonneg n : 0 ≤ (n : ℝ))
    have hl := mul_le_mul_of_nonneg_left (stageLengthPower_dominates_mean hγ.le hγ1 hn) hG
    nlinarith
  have hcost := mul_le_mul_of_nonneg_left
    (add_le_add_right hmeanN (stageLengthPower γ n)) hK
  refine hu.trans (EReal.coe_le_coe ?_)
  nlinarith

def nextStage (q : ℝ) : ℝ := q / (1 + q)

theorem nextStage_eq_one_sub_gamma {q : ℝ} (hq : 0 < q) :
    nextStage q = 1 - stageGamma q := by
  dsimp [nextStage, stageGamma]
  field_simp [show 1 + q ≠ 0 by linarith] <;> ring

theorem stageLengthPower_nextStage {q : ℝ} (hq : 0 < q) (n : ℕ) :
    stageLengthPower (stageGamma q) n =
      (n : ℝ) ^ (1 + nextStage q) * (blockLog n) ^ (1 - nextStage q) := by
  rw [nextStage_eq_one_sub_gamma hq]
  dsimp [stageLengthPower]
  congr 2 <;> ring

theorem three_finite_stage_exponents :
    nextStage 1 = 1 / 2 ∧ nextStage (1 / 2) = 1 / 3 ∧ nextStage (1 / 3) = 1 / 4 := by
  norm_num [nextStage]

end QuantumProver.Equipartition.FiniteModel.FiniteStageBootstrap

import QuantumProver.InformationTheory.AmplitudeDamping.SecretKey.Definitions

noncomputable section

open Filter Set
open scoped Topology

namespace QuantumProver.AmplitudeDamping.SecretKey.WeakBinaryConjugate

def testValue (d : ℕ) (x lambda : ℝ) : ℝ :=
  lambda * x - log2 (1 + ((2 : ℝ) ^ lambda - 1) / (d : ℝ))

def testValues (d : ℕ) (x : ℝ) : Set ℝ :=
  {y | ∃ lambda : ℝ, 0 ≤ lambda ∧ y = testValue d x lambda}

private theorem dimension_pos {d : ℕ} (hd : 2 ≤ d) : 0 < (d : ℝ) := by
  exact_mod_cast (lt_of_lt_of_le (by decide : 0 < (2 : ℕ)) hd)

private theorem dimension_one_le {d : ℕ} (hd : 2 ≤ d) : 1 ≤ (d : ℝ) := by
  exact_mod_cast (le_trans (by decide : 1 ≤ (2 : ℕ)) hd)

private theorem log_two_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)

theorem testNormalizer_pos {d : ℕ} (hd : 2 ≤ d) (lambda : ℝ) :
    0 < 1 + ((2 : ℝ) ^ lambda - 1) / (d : ℝ) := by
  have hd0 := dimension_pos hd
  have hd1 := dimension_one_le hd
  have hp : 0 < (2 : ℝ) ^ lambda := Real.rpow_pos_of_pos (by norm_num) _
  have heq : 1 + ((2 : ℝ) ^ lambda - 1) / (d : ℝ) =
      ((d : ℝ) - 1 + (2 : ℝ) ^ lambda) / (d : ℝ) := by
    field_simp [hd0.ne']
    ring
  rw [heq]
  exact div_pos (by linarith) hd0

@[simp] theorem testValue_zero_parameter (d : ℕ) (x : ℝ) :
    testValue d x 0 = 0 := by simp [testValue, log2]

theorem zero_mem_testValues (d : ℕ) (x : ℝ) : 0 ∈ testValues d x := by
  exact ⟨0, le_rfl, (testValue_zero_parameter d x).symm⟩

theorem testValues_nonempty (d : ℕ) (x : ℝ) : (testValues d x).Nonempty :=
  ⟨0, zero_mem_testValues d x⟩

theorem testValue_le_log_dimension {d : ℕ} {x lambda : ℝ}
    (hd : 2 ≤ d) (hx : x ≤ 1) (hlambda : 0 ≤ lambda) :
    testValue d x lambda ≤ log2 (d : ℝ) := by
  have hd0 := dimension_pos hd
  have hd1 := dimension_one_le hd
  have hp : 0 < (2 : ℝ) ^ lambda := Real.rpow_pos_of_pos (by norm_num) _
  have hratio : (2 : ℝ) ^ lambda / (d : ℝ) ≤
      1 + ((2 : ℝ) ^ lambda - 1) / (d : ℝ) := by
    have heq : 1 + ((2 : ℝ) ^ lambda - 1) / (d : ℝ) =
        (2 : ℝ) ^ lambda / (d : ℝ) + ((d : ℝ) - 1) / (d : ℝ) := by
      field_simp [hd0.ne']
      ring
    rw [heq]
    exact le_add_of_nonneg_right (div_nonneg (by linarith) hd0.le)
  have hlog := Real.log_le_log (div_pos hp hd0) hratio
  rw [Real.log_div hp.ne' hd0.ne', Real.log_rpow (by norm_num : 0 < (2 : ℝ))] at hlog
  have hmul := mul_le_mul_of_nonneg_left hx hlambda
  have hmul' := mul_le_mul_of_nonneg_right hmul log_two_pos.le
  unfold testValue log2
  apply (le_div_iff₀ log_two_pos).mpr
  rw [sub_mul, div_mul_cancel₀ _ log_two_pos.ne']
  nlinarith

theorem testValues_bddAbove {d : ℕ} {x : ℝ} (hd : 2 ≤ d) (hx : x ≤ 1) :
    BddAbove (testValues d x) := by
  refine ⟨log2 (d : ℝ), ?_⟩
  rintro y ⟨lambda, hlambda, rfl⟩
  exact testValue_le_log_dimension hd hx hlambda

theorem sSup_testValues_nonneg {d : ℕ} {x : ℝ} (hd : 2 ≤ d) (hx : x ≤ 1) :
    0 ≤ sSup (testValues d x) :=
  le_csSup (testValues_bddAbove hd hx) (zero_mem_testValues d x)

theorem testValue_nonpos_of_le_threshold {d : ℕ} {x lambda : ℝ}
    (hd : 2 ≤ d) (hx : x ≤ 1 / (d : ℝ)) (hlambda : 0 ≤ lambda) :
    testValue d x lambda ≤ 0 := by
  have hd0 := dimension_pos hd
  have hd1 := dimension_one_le hd
  have hp : 0 < (2 : ℝ) ^ lambda := Real.rpow_pos_of_pos (by norm_num) _
  have hr0 : 0 ≤ 1 / (d : ℝ) := (one_div_pos.mpr hd0).le
  have hr1 : 1 / (d : ℝ) ≤ 1 := (div_le_one hd0).mpr hd1
  have hJ := strictConcaveOn_log_Ioi.concaveOn.2
    (show (1 : ℝ) ∈ Ioi 0 from by change (0 : ℝ) < 1; norm_num)
    (show (2 : ℝ) ^ lambda ∈ Ioi 0 from hp)
    (show 0 ≤ 1 - 1 / (d : ℝ) from sub_nonneg.mpr hr1) hr0
    (show (1 - 1 / (d : ℝ)) + 1 / (d : ℝ) = 1 by ring)
  have harg : (1 - 1 / (d : ℝ)) * 1 +
      (1 / (d : ℝ)) * (2 : ℝ) ^ lambda =
      1 + ((2 : ℝ) ^ lambda - 1) / (d : ℝ) := by ring
  simp only [smul_eq_mul, Real.log_one, mul_zero, zero_add, harg,
    Real.log_rpow (by norm_num : 0 < (2 : ℝ))] at hJ
  have hmul := mul_le_mul_of_nonneg_left hx hlambda
  have hmul' := mul_le_mul_of_nonneg_right hmul log_two_pos.le
  have hlog : lambda * x * Real.log 2 ≤
      Real.log (1 + ((2 : ℝ) ^ lambda - 1) / (d : ℝ)) := by
    nlinarith
  unfold testValue log2
  have := (le_div_iff₀ log_two_pos).mpr hlog
  linarith

theorem sSup_testValues_eq_zero_of_le_threshold {d : ℕ} {x : ℝ}
    (hd : 2 ≤ d) (hx : x ≤ 1 / (d : ℝ)) : sSup (testValues d x) = 0 := by
  have hx1 : x ≤ 1 := hx.trans ((div_le_one (dimension_pos hd)).mpr (dimension_one_le hd))
  apply le_antisymm
  · apply csSup_le (testValues_nonempty d x)
    rintro y ⟨lambda, hlambda, rfl⟩
    exact testValue_nonpos_of_le_threshold hd hx hlambda
  · exact sSup_testValues_nonneg hd hx1

@[simp] theorem sSup_testValues_zero {d : ℕ} (hd : 2 ≤ d) :
    sSup (testValues d 0) = 0 :=
  sSup_testValues_eq_zero_of_le_threshold hd (one_div_pos.mpr (dimension_pos hd)).le

theorem testValue_one_identity {d : ℕ} (hd : 2 ≤ d) (lambda : ℝ) :
    testValue d 1 lambda = log2 (d : ℝ) -
      log2 (1 + ((d : ℝ) - 1) * ((2 : ℝ) ^ lambda)⁻¹) := by
  have hd0 := dimension_pos hd
  have hd1 := dimension_one_le hd
  have hp : 0 < (2 : ℝ) ^ lambda := Real.rpow_pos_of_pos (by norm_num) _
  have hq : 0 < 1 + ((d : ℝ) - 1) * ((2 : ℝ) ^ lambda)⁻¹ := by
    have := mul_nonneg (sub_nonneg.mpr hd1) (inv_pos.mpr hp).le
    linarith
  have heq : 1 + ((2 : ℝ) ^ lambda - 1) / (d : ℝ) =
      ((2 : ℝ) ^ lambda / (d : ℝ)) *
        (1 + ((d : ℝ) - 1) * ((2 : ℝ) ^ lambda)⁻¹) := by
    field_simp [hd0.ne', hp.ne']
    ring
  unfold testValue log2
  rw [heq, Real.log_mul (div_pos hp hd0).ne' hq.ne',
    Real.log_div hp.ne' hd0.ne', Real.log_rpow (by norm_num : 0 < (2 : ℝ))]
  field_simp [log_two_pos.ne']
  ring

theorem testValue_one_tendsto {d : ℕ} (hd : 2 ≤ d) :
    Tendsto (testValue d 1) atTop (𝓝 (log2 (d : ℝ))) := by
  have hpow : Tendsto (fun lambda : ℝ => (2 : ℝ) ^ lambda) atTop atTop :=
    tendsto_rpow_atTop_of_base_gt_one 2 (by norm_num)
  have harg : Tendsto (fun lambda : ℝ =>
      1 + ((d : ℝ) - 1) * ((2 : ℝ) ^ lambda)⁻¹) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.add
      (tendsto_const_nhds.mul hpow.inv_tendsto_atTop)
  have hlog := (Real.continuousAt_log one_ne_zero).tendsto.comp harg
  have hlim : Tendsto (fun lambda : ℝ => log2 (d : ℝ) -
      log2 (1 + ((d : ℝ) - 1) * ((2 : ℝ) ^ lambda)⁻¹))
      atTop (𝓝 (log2 (d : ℝ))) := by
    simpa [log2] using tendsto_const_nhds.sub (hlog.div_const (Real.log 2))
  exact hlim.congr (fun lambda => (testValue_one_identity hd lambda).symm)

@[simp] theorem sSup_testValues_one {d : ℕ} (hd : 2 ≤ d) :
    sSup (testValues d 1) = log2 (d : ℝ) := by
  apply le_antisymm
  · apply csSup_le (testValues_nonempty d 1)
    rintro y ⟨lambda, hlambda, rfl⟩
    exact testValue_le_log_dimension hd le_rfl hlambda
  · apply le_of_tendsto (testValue_one_tendsto hd)
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with lambda hlambda
    exact le_csSup (testValues_bddAbove hd le_rfl) ⟨lambda, hlambda, rfl⟩

private theorem soft_nonpos_of_le_threshold {d : ℕ} {x : ℝ}
    (hd : 2 ≤ d) (hx0 : 0 ≤ x) (hx : x ≤ 1 / (d : ℝ)) :
    x * log2 (d : ℝ) - binaryEntropyBits x ≤ 0 := by
  rcases eq_or_lt_of_le hx0 with rfl | hx0
  · simp [binaryEntropyBits]
  have hd0 := dimension_pos hd
  have hx1 : x ≤ 1 := hx.trans ((div_le_one hd0).mpr (dimension_one_le hd))
  have hdx : (d : ℝ) * x ≤ 1 := by
    have := (le_div_iff₀ hd0).mp hx
    nlinarith
  have hlogdx := Real.log_nonpos (mul_nonneg hd0.le hx0.le) hdx
  rw [Real.log_mul hd0.ne' hx0.ne'] at hlogdx
  have hfirst := mul_nonpos_of_nonneg_of_nonpos hx0.le hlogdx
  have hsecond := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hx1)
    (Real.log_nonpos (sub_nonneg.mpr hx1) (by linarith : 1 - x ≤ 1))
  unfold log2 binaryEntropyBits
  rw [← mul_div_assoc, ← sub_div, div_le_iff₀ log_two_pos]
  simp only [zero_mul]
  rw [Real.binEntropy, Real.log_inv, Real.log_inv]
  nlinarith

private theorem rpow_two_log2 {a : ℝ} (ha : 0 < a) :
    (2 : ℝ) ^ log2 a = a := by
  rw [Real.rpow_def_of_pos (by norm_num : 0 < (2 : ℝ)), log2]
  have heq : Real.log 2 * (Real.log a / Real.log 2) = Real.log a := by
    field_simp [log_two_pos.ne']
  rw [heq, Real.exp_log ha]

theorem exists_soft_test_witness {d : ℕ} {x : ℝ}
    (hd : 2 ≤ d) (hx0 : 0 < x) (hx1 : x < 1)
    (hx : 1 / (d : ℝ) < x) :
    ∃ lambda : ℝ, 0 ≤ lambda ∧
      x * log2 (d : ℝ) - binaryEntropyBits x ≤ testValue d x lambda := by
  have hd0 := dimension_pos hd
  have hc : 0 < 1 - x := sub_pos.mpr hx1
  let a : ℝ := (d : ℝ) * x / (1 - x)
  have ha : 0 < a := div_pos (mul_pos hd0 hx0) hc
  have hdx : 1 < (d : ℝ) * x := by
    have := (div_lt_iff₀ hd0).mp hx
    nlinarith
  have ha1 : 1 ≤ a := (le_div_iff₀ hc).mpr (by nlinarith)
  refine ⟨log2 a, div_nonneg (Real.log_nonneg ha1) log_two_pos.le, ?_⟩
  have hpow := rpow_two_log2 ha
  have hnormeq : 1 + (a - 1) / (d : ℝ) = 1 / (1 - x) - 1 / (d : ℝ) := by
    dsimp [a]
    field_simp [hd0.ne', hc.ne']
    ring
  have hnormle : 1 + ((2 : ℝ) ^ log2 a - 1) / (d : ℝ) ≤ 1 / (1 - x) := by
    rw [hpow, hnormeq]
    linarith [one_div_pos.mpr hd0]
  have hlog := Real.log_le_log (testNormalizer_pos hd (log2 a)) hnormle
  rw [Real.log_div one_ne_zero hc.ne', Real.log_one] at hlog
  have hloga : Real.log a = Real.log (d : ℝ) + Real.log x - Real.log (1 - x) := by
    dsimp [a]
    rw [Real.log_div (mul_pos hd0 hx0).ne' hc.ne', Real.log_mul hd0.ne' hx0.ne']
  have hnats : x * Real.log (d : ℝ) - Real.binEntropy x ≤
      Real.log a * x - Real.log (1 + ((2 : ℝ) ^ log2 a - 1) / (d : ℝ)) := by
    rw [Real.binEntropy, Real.log_inv, Real.log_inv, hloga]
    nlinarith
  unfold testValue log2 binaryEntropyBits
  unfold log2 at hnats
  convert (div_le_div_iff_of_pos_right log_two_pos).mpr hnats using 1 <;> ring

theorem weak_binary_entropy_bound {d : ℕ} {x : ℝ}
    (hd : 2 ≤ d) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    x * log2 (d : ℝ) - binaryEntropyBits x ≤
      sSup {y : ℝ | ∃ lambda : ℝ, 0 ≤ lambda ∧
        y = lambda * x - log2 (1 + ((2 : ℝ) ^ lambda - 1) / (d : ℝ))} := by
  change x * log2 (d : ℝ) - binaryEntropyBits x ≤ sSup (testValues d x)
  by_cases hx : x ≤ 1 / (d : ℝ)
  · exact (soft_nonpos_of_le_threshold hd hx0 hx).trans (sSup_testValues_nonneg hd hx1)
  by_cases hxeq : x = 1
  · subst x
    simpa [binaryEntropyBits] using (sSup_testValues_one hd).ge
  have hxpos : 0 < x := (one_div_pos.mpr (dimension_pos hd)).trans (lt_of_not_ge hx)
  obtain ⟨lambda, hlambda, hbound⟩ :=
    exists_soft_test_witness hd hxpos (lt_of_le_of_ne hx1 hxeq) (lt_of_not_ge hx)
  exact hbound.trans (le_csSup (testValues_bddAbove hd hx1) ⟨lambda, hlambda, rfl⟩)

end QuantumProver.AmplitudeDamping.SecretKey.WeakBinaryConjugate

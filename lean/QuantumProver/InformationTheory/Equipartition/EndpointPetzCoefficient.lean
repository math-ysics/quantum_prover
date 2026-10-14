import QuantumProver.InformationTheory.Equipartition.EndpointCurvature

noncomputable section
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator
namespace QuantumProver.Equipartition.FiniteModel.EndpointPetzCoefficient
open EndpointCurvature FixedMInduction Testing

def tailConstant : ℝ := 128 / (Real.log 2 / 2) ^ 2

def negativeCoefficient (G zeta : ℝ) : ℝ :=
  2 * Real.log 2 * (32 * G / zeta) + Real.log 2 * tailConstant / 2

def positiveCoefficient (G zeta : ℝ) : ℝ :=
  negativeCoefficient G zeta + 2 * Real.log 2 * G / zeta

def pinchingCoefficient (d : ℕ) : ℝ :=
  2 * ((d : ℝ) ^ 2 + (d : ℝ)) * (logTwo ((d : ℝ) + 1) + 1)

theorem matrixTailBudget_le_constant (n : ℕ) : matrixTailBudget n ≤ tailConstant := by
  have hr := Real.rpow_le_one_of_one_le_of_nonpos (by norm_num : (1 : ℝ) ≤ 2)
    (neg_nonpos.mpr (Nat.cast_nonneg n : 0 ≤ (n : ℝ)))
  unfold matrixTailBudget tailConstant
  simpa only [Real.rpow_eq_pow, mul_one] using mul_le_mul_of_nonneg_left hr (by positivity :
    0 ≤ 128 / (Real.log 2 / 2) ^ 2)

theorem matrixTailBudget_le_log_budget {n : ℕ} (hn : 1 ≤ n) :
    matrixTailBudget n ≤ tailConstant * (n : ℝ) * (blockLog n) ^ 2 := by
  have hnr : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hL := blockLog_ge_one hn
  have hL2 : 1 ≤ (blockLog n) ^ 2 := by nlinarith
  have hprod : 1 ≤ (n : ℝ) * (blockLog n) ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hL2 (Nat.cast_nonneg n : 0 ≤ (n : ℝ))]
  have htail : 0 ≤ tailConstant := by unfold tailConstant; positivity
  have hh := mul_le_mul_of_nonneg_left hprod htail
  exact (matrixTailBudget_le_constant n).trans (by simpa only [mul_one, mul_assoc] using hh)

theorem pinchingOverhead_le_blockLog (d : ℕ) {n : ℕ} (hn : 1 ≤ n) :
    pinchingOverhead d n ≤ pinchingCoefficient d * blockLog n := by
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hd0 : 0 ≤ (d : ℝ) := Nat.cast_nonneg d
  have hnp : 0 < (n : ℝ) + (d : ℝ) := by linarith
  have harg : (n : ℝ) + (d : ℝ) ≤ ((d : ℝ) + 1) * ((n : ℝ) + 1) := by
    nlinarith [mul_nonneg (Nat.cast_nonneg n : 0 ≤ (n : ℝ)) hd0]
  have hl := logTwo_mono_pos hnp harg
  rw [logTwo_mul_pos (by positivity : 0 < (d : ℝ) + 1)
    (by positivity : 0 < (n : ℝ) + 1)] at hl
  have hdlog : 0 ≤ logTwo ((d : ℝ) + 1) := by
    unfold logTwo
    exact div_nonneg (Real.log_nonneg (by linarith)) (Real.log_pos (by norm_num)).le
  have hLn := blockLog_ge_one hn
  have hmul := mul_le_mul_of_nonneg_left hLn hdlog
  have hbound : logTwo ((n : ℝ) + (d : ℝ)) ≤
      (logTwo ((d : ℝ) + 1) + 1) * blockLog n := by
    change logTwo ((n : ℝ) + (d : ℝ)) ≤ _
    change logTwo ((n : ℝ) + (d : ℝ)) ≤ logTwo ((d : ℝ) + 1) + blockLog n at hl
    nlinarith
  unfold pinchingOverhead pinchingCoefficient
  have hcoef : 0 ≤ 2 * ((d : ℝ) ^ 2 + (d : ℝ)) := by positivity
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hbound hcoef

theorem time_in_narrow_window {n : ℕ} (hn : 1 ≤ n) {zeta delta : ℝ}
    (hwindow : delta * (n : ℝ) * blockLog n ≤ endpointWindow zeta) :
    delta * Real.log 2 ≤ narrowScale zeta n / 8 := by
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hLpos : 0 < blockLog n := lt_of_lt_of_le zero_lt_one (blockLog_ge_one hn)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hb : delta * (n : ℝ) * blockLog n * (8 * Real.log 2) ≤ zeta :=
    (le_div_iff₀ (by positivity : 0 < 8 * Real.log 2)).mp hwindow
  unfold narrowScale
  rw [div_div]
  apply (le_div_iff₀ (by positivity : 0 < (n : ℝ) * blockLog n * 8)).mpr
  convert hb using 1 <;> ring

theorem negative_cost_bound {G zeta delta H : ℝ} (hG : 0 ≤ G) (hzeta : 0 < zeta)
    (hdelta : 0 ≤ delta) (hH : H ≤ 2) (M : ℕ) {n : ℕ} (hn : 1 ≤ n) :
    (delta * Real.log 2) * (H * narrowMomentBudget G M zeta n + matrixTailBudget n / 2) ≤
      (delta * (n : ℝ)) *
        (H * (M : ℝ) * (blockLog (n / 16)) ^ 3 + negativeCoefficient G zeta * (blockLog n) ^ 2) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hL := blockLog_nonneg n
  have hx1 : delta * Real.log 2 * H * (32 * G / zeta) * (n : ℝ) * (blockLog n) ^ 2 ≤
      (delta * (n : ℝ)) * (2 * Real.log 2 * (32 * G / zeta) * (blockLog n) ^ 2) := by
    have h := mul_le_mul_of_nonneg_right hH (show
      0 ≤ delta * Real.log 2 * (32 * G / zeta) * (n : ℝ) * (blockLog n) ^ 2 by positivity)
    convert h using 1 <;> ring
  have hx2 : delta * Real.log 2 * matrixTailBudget n / 2 ≤
      (delta * (n : ℝ)) * (Real.log 2 * tailConstant / 2 * (blockLog n) ^ 2) := by
    have h := mul_le_mul_of_nonneg_left (matrixTailBudget_le_log_budget hn)
      (show 0 ≤ delta * Real.log 2 / 2 by positivity)
    convert h using 1 <;> ring
  calc
    _ = (delta * (n : ℝ)) * (H * (M : ℝ) * (blockLog (n / 16)) ^ 3) +
        delta * Real.log 2 * H * (32 * G / zeta) * (n : ℝ) * (blockLog n) ^ 2 +
        delta * Real.log 2 * matrixTailBudget n / 2 := by
      unfold narrowMomentBudget
      field_simp [hlog2.ne'] <;> ring
    _ ≤ (delta * (n : ℝ)) * (H * (M : ℝ) * (blockLog (n / 16)) ^ 3) +
        (delta * (n : ℝ)) * (2 * Real.log 2 * (32 * G / zeta) * (blockLog n) ^ 2) +
        (delta * (n : ℝ)) * (Real.log 2 * tailConstant / 2 * (blockLog n) ^ 2) :=
      add_le_add (add_le_add le_rfl hx1) hx2
    _ = _ := by unfold negativeCoefficient; ring

theorem positive_cost_bound {G zeta delta H s : ℝ} (hG : 0 ≤ G) (hzeta : 0 < zeta)
    (hdelta : 0 ≤ delta) (hH : H ≤ 2) (hs0 : 0 ≤ s)
    (M : ℕ) {n : ℕ} (hn : 1 ≤ n) (hs : s ≤ G * blockLog n) :
    (delta * Real.log 2) *
      (H * (narrowMomentBudget G M zeta n + ((n : ℝ) * blockLog n / zeta) * s) +
        matrixTailBudget n / 2) ≤
      (delta * (n : ℝ)) *
        (H * (M : ℝ) * (blockLog (n / 16)) ^ 3 + positiveCoefficient G zeta * (blockLog n) ^ 2) := by
  have hnegative := negative_cost_bound hG hzeta hdelta hH M hn
  have hmean := mul_le_mul hH hs hs0 (by norm_num : (0 : ℝ) ≤ 2)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hL := blockLog_nonneg n
  have hextra : (delta * Real.log 2) * H * ((n : ℝ) * blockLog n / zeta) * s ≤
      (delta * (n : ℝ)) * (2 * Real.log 2 * G / zeta * (blockLog n) ^ 2) := by
    have h := mul_le_mul_of_nonneg_left hmean (show
      0 ≤ (delta * Real.log 2) * ((n : ℝ) * blockLog n / zeta) by positivity)
    convert h using 1 <;> ring
  calc
    _ = (delta * Real.log 2) * (H * narrowMomentBudget G M zeta n + matrixTailBudget n / 2) +
        (delta * Real.log 2) * H * ((n : ℝ) * blockLog n / zeta) * s := by ring
    _ ≤ (delta * (n : ℝ)) *
        (H * (M : ℝ) * (blockLog (n / 16)) ^ 3 + negativeCoefficient G zeta * (blockLog n) ^ 2) +
        (delta * (n : ℝ)) * (2 * Real.log 2 * G / zeta * (blockLog n) ^ 2) :=
      add_le_add hnegative hextra
    _ = _ := by unfold positiveCoefficient; ring

theorem matrix_petz_lower_coefficient {ι : Type*} [Fintype ι] [DecidableEq ι]
    {ρ σ : CMat ι} (hρ : IsState ρ) (hσ : σ.PosSemidef)
    {C G zeta center delta : ℝ} (hC : 0 ≤ C) (hG : 0 ≤ G)
    (hzeta : 0 < zeta) (hzetaSmall : zeta ≤ Real.log 2 / 8)
    (M : ℕ) {n : ℕ} (hn : 32 ≤ n)
    (hdom : LoewnerLE ρ (Real.rpow 2 (C * (n : ℝ)) • σ))
    (hcenter : -(C * (n : ℝ)) ≤ center) (hmean : 0 ≤ umegakiReal ρ σ - center)
    (hdelta : 0 < delta) (hdelta1 : delta < 1)
    (hwindow : delta * (n : ℝ) * blockLog n ≤ endpointWindow zeta)
    (ha1 : narrowBlockBudget G M zeta n ≤ 1) (hH : narrowFactor C G M zeta n ≤ 2)
    (hLap : (nsLaw ρ σ hρ hσ).expect
      (fun z => Real.exp (-narrowScale zeta n * (nsLikelihood ρ σ z - center))) ≤
        Real.exp (narrowBlockBudget G M zeta n)) :
    ((center - (delta * (n : ℝ)) *
      (narrowFactor C G M zeta n * (M : ℝ) * (blockLog (n / 16)) ^ 3 +
        negativeCoefficient G zeta * (blockLog n) ^ 2) : ℝ) : EReal) ≤
      petzDivergence ρ σ (1 - delta) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have htime := time_in_narrow_window (by omega : 1 ≤ n) hwindow
  have halpha : 1 - (delta * Real.log 2) / Real.log 2 = 1 - delta := by
    field_simp [hlog2.ne'] <;> ring
  have hp := matrix_petz_narrow_lower hρ hσ hC hG hzeta hzetaSmall M hn hdom hcenter hmean
    (mul_pos hdelta hlog2) htime (by rw [halpha]; linarith) ha1 hH hLap
  rw [halpha] at hp
  have hc := negative_cost_bound hG hzeta hdelta.le hH M (by omega : 1 ≤ n)
  exact (EReal.coe_le_coe (by linarith :
    center - (delta * (n : ℝ)) *
      (narrowFactor C G M zeta n * (M : ℝ) * (blockLog (n / 16)) ^ 3 +
        negativeCoefficient G zeta * (blockLog n) ^ 2) ≤
      center - (delta * Real.log 2) *
        (narrowFactor C G M zeta n * narrowMomentBudget G M zeta n + matrixTailBudget n / 2))).trans hp

theorem matrix_petz_upper_coefficient {ι : Type*} [Fintype ι] [DecidableEq ι]
    {ρ σ : CMat ι} (hρ : IsState ρ) (hσ : σ.PosSemidef)
    {C G zeta center delta : ℝ} (hC : 0 ≤ C) (hG : 0 ≤ G)
    (hzeta : 0 < zeta) (hzetaSmall : zeta ≤ Real.log 2 / 8)
    (M : ℕ) {n : ℕ} (hn : 32 ≤ n)
    (hdom : LoewnerLE ρ (Real.rpow 2 (C * (n : ℝ)) • σ))
    (hcenter : -(C * (n : ℝ)) ≤ center)
    (hmean : 0 ≤ umegakiReal ρ σ - center)
    (hmeanUpper : umegakiReal ρ σ - center ≤ G * blockLog n)
    (hdelta : 0 < delta)
    (hwindow : delta * (n : ℝ) * blockLog n ≤ endpointWindow zeta)
    (ha1 : narrowBlockBudget G M zeta n ≤ 1) (hH : narrowFactor C G M zeta n ≤ 2)
    (hLap : (nsLaw ρ σ hρ hσ).expect
      (fun z => Real.exp (-narrowScale zeta n * (nsLikelihood ρ σ z - center))) ≤
        Real.exp (narrowBlockBudget G M zeta n)) :
    petzDivergence ρ σ (1 + delta) ≤
      ((center + G * blockLog n + (delta * (n : ℝ)) *
        (narrowFactor C G M zeta n * (M : ℝ) * (blockLog (n / 16)) ^ 3 +
          positiveCoefficient G zeta * (blockLog n) ^ 2) : ℝ) : EReal) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hscale := narrowScale_pos (by omega : 1 ≤ n) hzeta
  have htime := time_in_narrow_window (by omega : 1 ≤ n) hwindow
  have ht3 : delta * Real.log 2 ≤ narrowScale zeta n / 3 := by linarith
  have hp := matrix_petz_narrow_upper hρ hσ hC hG hzeta hzetaSmall M hn hdom hcenter hmean
    (mul_pos hdelta hlog2) ht3 ha1 hLap
  have halpha : 1 + (delta * Real.log 2) / Real.log 2 = 1 + delta := by
    field_simp [hlog2.ne'] <;> ring
  rw [halpha] at hp
  have hc := positive_cost_bound hG hzeta hdelta.le hH hmean M
    (by omega : 1 ≤ n) hmeanUpper
  refine hp.trans (EReal.coe_le_coe ?_)
  linarith

end QuantumProver.Equipartition.FiniteModel.EndpointPetzCoefficient

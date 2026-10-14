import QuantumProver.InformationTheory.SuperchannelDiscrimination.StrategyAssembly
import QuantumProver.InformationTheory.SuperchannelDiscrimination.ChannelChoiSupport

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace QuantumProver.SuperchannelDiscrimination.ChannelTestingPrimal

open Matrix KrausCompletion CPWrappers FlaggedStates TensorEntropy ChannelRegularization
open MatrixStrategyAssembly.MatrixBinaryTesting
open scoped BigOperators ComplexOrder MatrixOrder Matrix Kronecker

theorem positive_advantage_alternative_pos {p q t b : ℝ}
    (hq : 0 ≤ q) (ht : 0 ≤ t) (hpos : 0 < p - t * q)
    (hD : extendedBinaryRelativeEntropyBits p q ≤ (b : EReal)) : 0 < q := by
  by_contra hn
  have hq0 : q = 0 := le_antisymm (le_of_not_gt hn) hq
  have hp : p ≠ 0 := by rw [hq0, mul_zero, sub_zero] at hpos; exact ne_of_gt hpos
  have htop : (⊤ : EReal) ≤ (b : EReal) := by
    simpa [extendedBinaryRelativeEntropyBits, hq0, hp] using hD
  exact not_le_of_gt (EReal.coe_lt_top b) htop

theorem dyadic_advantage_le_of_binary_budget {p q B r : ℝ} {n : ℕ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hB : 0 ≤ B) (hn : 0 < n) (hr : 0 < r)
    (hD : extendedBinaryRelativeEntropyBits p q ≤ (((n : ℝ) * B : ℝ) : EReal)) :
    p - (2 : ℝ) ^ ((n : ℝ) * r) * q ≤ ((n : ℝ) * B + 1) / ((n : ℝ) * r) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hnr : 0 < (n : ℝ) * r := mul_pos hnR hr
  have ht : 0 < (2 : ℝ) ^ ((n : ℝ) * r) := Real.rpow_pos_of_pos (by norm_num) _
  have ht1 : 1 < (2 : ℝ) ^ ((n : ℝ) * r) :=
    Real.one_lt_rpow (by norm_num) hnr
  by_cases hpos : 0 < p - (2 : ℝ) ^ ((n : ℝ) * r) * q
  · have hqpos := positive_advantage_alternative_pos hq0 ht.le hpos hD
    have htq : (2 : ℝ) ^ ((n : ℝ) * r) * q < 1 := by linarith
    have hqlt : q < 1 := by
      nlinarith [mul_le_mul_of_nonneg_right ht1.le hq0]
    have hlog : (n : ℝ) * r ≤ Real.logb 2 (1 / q) := by
      apply (Real.le_logb_iff_rpow_le (by norm_num) (one_div_pos.mpr hqpos)).mpr
      apply (le_div_iff₀ hqpos).mpr
      exact htq.le
    have hfin : binaryRelativeEntropyBits p q ≤ (n : ℝ) * B := by
      apply EReal.coe_le_coe_iff.mp
      simpa [extendedBinaryRelativeEntropyBits, ne_of_gt hqpos, ne_of_lt hqlt] using hD
    have hbinary := (binary_relative_entropy_ge hp1 hqpos hqlt).trans hfin
    have hpbound : p ≤ ((n : ℝ) * B + 1) / ((n : ℝ) * r) := by
      apply (le_div_iff₀ hnr).mpr
      have hm := mul_le_mul_of_nonneg_left hlog hp0
      nlinarith
    exact (sub_le_self _ (mul_nonneg ht.le hq0)).trans hpbound
  · exact (le_of_not_gt hpos).trans (div_nonneg (by positivity) hnr.le)

theorem dyadic_advantage_le_one {p q r : ℝ} {n : ℕ}
    (hp1 : p ≤ 1) (hq0 : 0 ≤ q) :
    p - (2 : ℝ) ^ ((n : ℝ) * r) * q ≤ 1 :=
  (sub_le_self _ (mul_nonneg (Real.rpow_pos_of_pos (by norm_num) _).le hq0)).trans hp1

variable {I O : Type*} [Fintype I] [Fintype O] [DecidableEq I] [DecidableEq O]

def testingAdvantage (Φ Ψ : FiniteCPTP I O) (n : ℕ) (t : ℝ) : EReal :=
  ⨆ (k : ℕ) (ρ : Matrix (TensorIndex I n × Fin k) (TensorIndex I n × Fin k) ℂ)
    (_hρ : IsDensity ρ)
    (E : Matrix (TensorIndex O n × Fin k) (TensorIndex O n × Fin k) ℂ)
    (_hE : IsEffect E),
    ((acceptanceProbability (amplify (channelPower Φ n).map (Fin k) ρ) E -
      t * acceptanceProbability (amplify (channelPower Ψ n).map (Fin k) ρ) E : ℝ) : EReal)

theorem physical_dyadic_advantage_le (Φ Ψ : FiniteCPTP I O) [Nonempty I]
    {n : ℕ} (hn : 0 < n) {r B : ℝ} (hr : 0 < r)
    (hReg : regularizedRelativeEntropyBits Φ Ψ ≤ (B : EReal))
    (R : Type*) [Fintype R] [DecidableEq R]
    {ρ : Matrix (TensorIndex I n × R) (TensorIndex I n × R) ℂ}
    {E : Matrix (TensorIndex O n × R) (TensorIndex O n × R) ℂ}
    (hρ : IsDensity ρ) (hE : IsEffect E) :
    acceptanceProbability (amplify (channelPower Φ n).map R ρ) E -
      (2 : ℝ) ^ ((n : ℝ) * r) *
        acceptanceProbability (amplify (channelPower Ψ n).map R ρ) E ≤
      min 1 (((n : ℝ) * B + 1) / ((n : ℝ) * r)) := by
  have hp := acceptanceProbability_bounds (channelPower_reference_isDensity Φ n R hρ) hE
  have hq := acceptanceProbability_bounds (channelPower_reference_isDensity Ψ n R hρ) hE
  have hD := (binary_errors_entropy_dpi
    (channelPower_reference_isDensity Φ n R hρ)
    (channelPower_reference_isDensity Ψ n R hρ) hE).trans
      (channelPower_reference_entropy_le_real_bound Φ Ψ n R hρ hReg)
  have hB : 0 ≤ B := EReal.coe_nonneg.mp
    ((regularizedRelativeEntropyBits_nonneg Φ Ψ).trans hReg)
  exact le_min (dyadic_advantage_le_one hp.2 hq.1)
    (dyadic_advantage_le_of_binary_budget hp.1 hp.2 hq.1 hq.2 hB hn hr hD)

theorem testingAdvantage_dyadic_le (Φ Ψ : FiniteCPTP I O) [Nonempty I]
    {n : ℕ} (hn : 0 < n) {r B : ℝ} (hr : 0 < r)
    (hReg : regularizedRelativeEntropyBits Φ Ψ ≤ (B : EReal)) :
    testingAdvantage Φ Ψ n ((2 : ℝ) ^ ((n : ℝ) * r)) ≤
      ((min 1 (((n : ℝ) * B + 1) / ((n : ℝ) * r)) : ℝ) : EReal) := by
  refine iSup_le fun k => iSup_le fun ρ => iSup_le fun hρ =>
    iSup_le fun E => iSup_le fun hE => ?_
  exact EReal.coe_le_coe_iff.mpr
    (physical_dyadic_advantage_le Φ Ψ hn hr hReg (Fin k) hρ hE)

end QuantumProver.SuperchannelDiscrimination.ChannelTestingPrimal

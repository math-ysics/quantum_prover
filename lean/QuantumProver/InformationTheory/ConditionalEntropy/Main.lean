import QuantumProver.InformationTheory.ConditionalEntropy.JordanCoupling
import QuantumProver.InformationTheory.ConditionalEntropy.MixtureEntropy
import QuantumProver.InformationTheory.ConditionalEntropy.ConditionalRange

set_option autoImplicit false

noncomputable section

open Matrix
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator Topology

namespace QuantumProver.ConditionalEntropy

theorem binaryEntropy_continuous : Continuous binaryEntropy := by
  change Continuous (fun p : ℝ =>
    -(p * Real.log p + (1 - p) * Real.log (1 - p)) / Real.log 2)
  exact (Real.continuous_mul_log.add
    (Real.continuous_mul_log.comp (continuous_const.sub continuous_id))).neg.div_const _

theorem winterBound_tendsto_zero (A : Type*) [Fintype A] :
    Filter.Tendsto (winterBound A) (𝓝 (0 : ℝ)) (𝓝 (0 : ℝ)) := by
  have hNoise : ContinuousAt (fun epsilon : ℝ => epsilon / (1 + epsilon)) 0 :=
    continuousAt_id.div (continuousAt_const.add continuousAt_id) (by norm_num)
  have hEntropy : ContinuousAt
      (fun epsilon : ℝ => binaryEntropy (epsilon / (1 + epsilon))) 0 :=
    binaryEntropy_continuous.continuousAt.comp hNoise
  have hLinear : ContinuousAt (fun epsilon : ℝ => 2 * epsilon * logDimA A) 0 :=
    (continuousAt_const.mul continuousAt_id).mul continuousAt_const
  have hCost : ContinuousAt
      (fun epsilon : ℝ => (1 + epsilon) * binaryEntropy (epsilon / (1 + epsilon))) 0 :=
    (continuousAt_const.add continuousAt_id).mul hEntropy
  have hBound : ContinuousAt (winterBound A) 0 := hLinear.add hCost
  simpa only [winterBound_zero] using hBound.tendsto

theorem conditionalEntropy_continuity
    {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {R S : Matrix (A × B) (A × B) ℂ}
    (hR : IsDensity R) (hS : IsDensity S) {epsilon : ℝ}
    (hDistance : traceDistance R S ≤ epsilon) (hEpsilon : epsilon ≤ 1) :
    |conditionalEntropyBits R - conditionalEntropyBits S| ≤ winterBound A epsilon := by
  have hEpsilon0 : 0 ≤ epsilon := (traceDistance_nonneg R S).trans hDistance
  have hMatrixDistance : JordanCoupling.halfDistance R S ≤ epsilon := hDistance
  obtain ⟨W, TPlus, TMinus, _hW, hPlus, hMinus, hWS, hWR⟩ :=
    JordanCoupling.exists_common_density_coupling hR hS hMatrixDistance
  obtain ⟨_hBase0, _hBase1, hNoise0, _hNoiseLt1, _hSum, hBase⟩ :=
    JordanCoupling.coupling_weights hEpsilon0
  have hNoise1 : epsilon / (1 + epsilon) ≤ 1 :=
    (JordanCoupling.coupling_noise_le_half hEpsilon0 hEpsilon).trans (by norm_num)
  have hMixS : W = mix (epsilon / (1 + epsilon)) S TPlus := by
    simpa only [mix, hBase] using hWS
  have hMixR : W = mix (epsilon / (1 + epsilon)) R TMinus := by
    simpa only [mix, hBase] using hWR
  have hRLower := conditionalEntropy_mix_lower hR hMinus hNoise0 hNoise1
  have hRUpper := conditionalEntropy_mix_upper hR hMinus hNoise0 hNoise1
  have hSLower := conditionalEntropy_mix_lower hS hPlus hNoise0 hNoise1
  have hSUpper := conditionalEntropy_mix_upper hS hPlus hNoise0 hNoise1
  rw [← hMixR] at hRLower hRUpper
  rw [← hMixS] at hSLower hSUpper
  have hPlusRange := conditionalEntropy_bounds hPlus
  have hMinusRange := conditionalEntropy_bounds hMinus
  have hForward : conditionalEntropyBits R - conditionalEntropyBits S ≤
      winterBound A epsilon := by
    simpa only [winterBound] using
      winter_scalar_bound epsilon (logDimA A)
        (conditionalEntropyBits R) (conditionalEntropyBits S)
        (conditionalEntropyBits TMinus) (conditionalEntropyBits TPlus)
        (conditionalEntropyBits W) (binaryEntropy (epsilon / (1 + epsilon)))
        hEpsilon0 hRLower hSUpper hMinusRange.1 hPlusRange.2
  have hBackward : conditionalEntropyBits S - conditionalEntropyBits R ≤
      winterBound A epsilon := by
    simpa only [winterBound] using
      winter_scalar_bound epsilon (logDimA A)
        (conditionalEntropyBits S) (conditionalEntropyBits R)
        (conditionalEntropyBits TPlus) (conditionalEntropyBits TMinus)
        (conditionalEntropyBits W) (binaryEntropy (epsilon / (1 + epsilon)))
        hEpsilon0 hSLower hRUpper hPlusRange.1 hMinusRange.2
  exact abs_le.mpr ⟨by linarith, hForward⟩

theorem conditionalEntropy_eq_of_traceDistance_eq_zero
    {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {R S : Matrix (A × B) (A × B) ℂ}
    (hR : IsDensity R) (hS : IsDensity S) (hDistance : traceDistance R S = 0) :
    conditionalEntropyBits R = conditionalEntropyBits S := by
  have hBound := conditionalEntropy_continuity hR hS (le_of_eq hDistance) (by norm_num)
  have hAbs : |conditionalEntropyBits R - conditionalEntropyBits S| = 0 :=
    le_antisymm (by simpa only [winterBound_zero] using hBound) (abs_nonneg _)
  exact sub_eq_zero.mp (abs_eq_zero.mp hAbs)

def FiniteConditionalEntropyContinuity : Prop :=
  ∀ (dA dB : ℕ), 0 < dA → 0 < dB →
    ∀ (R S : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ),
      IsDensity R → IsDensity S → ∀ epsilon : ℝ,
        traceDistance R S ≤ epsilon → epsilon ≤ 1 →
          |conditionalEntropyBits R - conditionalEntropyBits S| ≤
            winterBound (Fin dA) epsilon

theorem winter_finite_conditionalEntropy_continuity :
    FiniteConditionalEntropyContinuity := by
  intro dA dB _hdA _hdB R S hR hS epsilon hDistance hEpsilon
  exact conditionalEntropy_continuity hR hS hDistance hEpsilon

end QuantumProver.ConditionalEntropy

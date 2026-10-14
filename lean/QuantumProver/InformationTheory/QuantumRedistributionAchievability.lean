import QuantumProver.InformationTheory.QuantumRedistributionTypicalRates
import QuantumProver.InformationTheory.QuantumRedistributionCarrierDecoupling
import QuantumProver.InformationTheory.QuantumRedistributionRealization
import QuantumProver.InformationTheory.QuantumRedistributionTargetWires

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 5000

noncomputable section

namespace QuantumProver.QuantumRedistributionAchievability

open Matrix Filter
open QuantumProver.QuantumEntropy QuantumProver.QuantumRedistributionEntropy
open QuantumProver.QuantumRedistributionSources QuantumProver.QuantumRedistributionTypicalRates
open QuantumProver.QuantumRedistributionDimensions QuantumProver.ConditionalTypicalSmoothing
open QuantumProver.QuantumTypicalProjectors QuantumProver.SuperchannelDiscrimination
open scoped Topology BigOperators ComplexOrder MatrixOrder Matrix Kronecker

variable {A B E C : Type*} [Fintype A] [Fintype B] [Fintype E] [Fintype C]
  [DecidableEq A] [DecidableEq B] [DecidableEq E] [DecidableEq C]

def senderAcceptance (ψ : PhysicalIndex A B E C → ℂ) (hψ : normSq ψ = 1)
    (t : ℝ) (n : ℕ) : ℝ :=
  (TensorEntropy.tensorPower (reducedB ψ) n * commonCarrier ψ hψ t n).trace.re

theorem commonCarrier_eq_matrix_typical (ψ : PhysicalIndex A B E C → ℂ)
    (hψ : normSq ψ = 1) (t : ℝ) (n : ℕ) :
    commonCarrier ψ hψ t n =
      typicalProjector (partialTraceRight_isDensity (reducedBE_isDensity ψ hψ)) t n := by
  exact senderTypical_eq_of_common_marginal (sourceBAC_isDensity ψ hψ)
    (reducedBE_isDensity ψ hψ) (sourceBAC_sender ψ) t n

theorem senderAcceptance_eq_typicalMass (ψ : PhysicalIndex A B E C → ℂ)
    (hψ : normSq ψ = 1) (t : ℝ) (n : ℕ) :
    senderAcceptance ψ hψ t n =
      typicalMass (partialTraceRight_isDensity (reducedBE_isDensity ψ hψ)) t n := by
  rw [senderAcceptance, commonCarrier_eq_matrix_typical]
  exact typicalProjector_acceptance _ _ _

theorem senderAcceptance_le_one (ψ : PhysicalIndex A B E C → ℂ)
    (hψ : normSq ψ = 1) (t : ℝ) (n : ℕ) : senderAcceptance ψ hψ t n ≤ 1 := by
  rw [senderAcceptance_eq_typicalMass]
  exact typicalMass_le_one _ _ _

theorem senderAcceptance_tendsto_one (ψ : PhysicalIndex A B E C → ℂ)
    (hψ : normSq ψ = 1) {t : ℝ} (ht : 0 < t) :
    Tendsto (senderAcceptance ψ hψ t) atTop (𝓝 1) := by
  have he : senderAcceptance ψ hψ t =
      typicalMass (partialTraceRight_isDensity (reducedBE_isDensity ψ hψ)) t :=
    funext (senderAcceptance_eq_typicalMass ψ hψ t)
  rw [he]
  exact typicalMass_tendsto_one _ ht

theorem senderAcceptance_eventually_pos (ψ : PhysicalIndex A B E C → ℂ)
    (hψ : normSq ψ = 1) {t : ℝ} (ht : 0 < t) :
    ∀ᶠ n : ℕ in atTop, 0 < senderAcceptance ψ hψ t n :=
  (senderAcceptance_tendsto_one ψ hψ ht).eventually (Ioi_mem_nhds (by norm_num))

def cropEnvelope (ψ : PhysicalIndex A B E C → ℂ) (hψ : normSq ψ = 1)
    (t : ℝ) (n : ℕ) : ℝ := 4 * Real.sqrt (1 - senderAcceptance ψ hψ t n)

def consumedProxyError (ψ : PhysicalIndex A B E C → ℂ) (hψ : normSq ψ = 1)
    (t : ℝ) (n : ℕ) : ℝ :=
  traceNorm (groupedPower (sourceBAC ψ) n - consumedProxy ψ hψ t n)

def generatedProxyError (ψ : PhysicalIndex A B E C → ℂ) (hψ : normSq ψ = 1)
    (t : ℝ) (n : ℕ) : ℝ :=
  traceNorm (groupedPower (sourceBAE ψ) n - generatedProxy ψ hψ t n)

theorem cropEnvelope_nonneg (ψ : PhysicalIndex A B E C → ℂ)
    (hψ : normSq ψ = 1) (t : ℝ) (n : ℕ) : 0 ≤ cropEnvelope ψ hψ t n := by
  exact mul_nonneg (by norm_num) (Real.sqrt_nonneg _)

theorem consumedProxyError_nonneg (ψ : PhysicalIndex A B E C → ℂ)
    (hψ : normSq ψ = 1) (t : ℝ) (n : ℕ) : 0 ≤ consumedProxyError ψ hψ t n :=
  EffectPerturbation.traceNorm_nonneg _

theorem generatedProxyError_nonneg (ψ : PhysicalIndex A B E C → ℂ)
    (hψ : normSq ψ = 1) (t : ℝ) (n : ℕ) : 0 ≤ generatedProxyError ψ hψ t n :=
  EffectPerturbation.traceNorm_nonneg _

theorem cropEnvelope_tendsto_zero (ψ : PhysicalIndex A B E C → ℂ)
    (hψ : normSq ψ = 1) {t : ℝ} (ht : 0 < t) :
    Tendsto (cropEnvelope ψ hψ t) atTop (𝓝 0) := by
  have h0 : Tendsto (fun n => 1 - senderAcceptance ψ hψ t n) atTop (𝓝 0) := by
    simpa only [sub_self] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub
        (senderAcceptance_tendsto_one ψ hψ ht)
  have hs := Real.continuous_sqrt.continuousAt.tendsto.comp h0
  change Tendsto (fun n => 4 * Real.sqrt (1 - senderAcceptance ψ hψ t n)) atTop (𝓝 0)
  simpa only [Function.comp_def, Real.sqrt_zero, mul_zero] using hs.const_mul 4

theorem consumedProxyError_tendsto_zero (ψ : PhysicalIndex A B E C → ℂ)
    (hψ : normSq ψ = 1) {t : ℝ} (ht : 0 < t) :
    Tendsto (consumedProxyError ψ hψ t) atTop (𝓝 0) :=
  iidProxy_error_tendsto_zero (sourceBAC_isDensity ψ hψ) ht

theorem generatedProxyError_tendsto_zero (ψ : PhysicalIndex A B E C → ℂ)
    (hψ : normSq ψ = 1) {t : ℝ} (ht : 0 < t) :
    Tendsto (generatedProxyError ψ hψ t) atTop (𝓝 0) :=
  iidProxy_error_tendsto_zero (sourceBAE_isDensity ψ hψ) ht

def consumedMarginalEnvelope (ψ : PhysicalIndex A B E C → ℂ) (hψ : normSq ψ = 1)
    (t : ℝ) (n : ℕ) : ℝ :=
  Real.sqrt (3 * consumedCost ψ hψ t n) +
    2 * (consumedProxyError ψ hψ t n + cropEnvelope ψ hψ t n) + cropEnvelope ψ hψ t n

def generatedMarginalEnvelope (ψ : PhysicalIndex A B E C → ℂ) (hψ : normSq ψ = 1)
    (t : ℝ) (n : ℕ) : ℝ :=
  Real.sqrt (3 * generatedCost ψ hψ t n) +
    2 * (generatedProxyError ψ hψ t n + cropEnvelope ψ hψ t n) + cropEnvelope ψ hψ t n

theorem consumedMarginalEnvelope_nonneg (ψ : PhysicalIndex A B E C → ℂ)
    (hψ : normSq ψ = 1) (t : ℝ) (n : ℕ) : 0 ≤ consumedMarginalEnvelope ψ hψ t n := by
  exact add_nonneg (add_nonneg (Real.sqrt_nonneg _)
    (mul_nonneg (by norm_num) (add_nonneg (consumedProxyError_nonneg ψ hψ t n)
      (cropEnvelope_nonneg ψ hψ t n)))) (cropEnvelope_nonneg ψ hψ t n)

theorem generatedMarginalEnvelope_nonneg (ψ : PhysicalIndex A B E C → ℂ)
    (hψ : normSq ψ = 1) (t : ℝ) (n : ℕ) : 0 ≤ generatedMarginalEnvelope ψ hψ t n := by
  exact add_nonneg (add_nonneg (Real.sqrt_nonneg _)
    (mul_nonneg (by norm_num) (add_nonneg (generatedProxyError_nonneg ψ hψ t n)
      (cropEnvelope_nonneg ψ hψ t n)))) (cropEnvelope_nonneg ψ hψ t n)

theorem consumedMarginalEnvelope_tendsto_zero (ψ : PhysicalIndex A B E C → ℂ)
    (hψ : normSq ψ = 1) {t : ℝ} (ht : 0 < t) :
    Tendsto (consumedMarginalEnvelope ψ hψ t) atTop (𝓝 0) := by
  have hc := Real.continuous_sqrt.continuousAt.tendsto.comp
    ((consumedCost_tendsto_zero ψ hψ ht).const_mul 3)
  have hp := consumedProxyError_tendsto_zero ψ hψ ht
  have hb := cropEnvelope_tendsto_zero ψ hψ ht
  change Tendsto (fun n => Real.sqrt (3 * consumedCost ψ hψ t n) +
    2 * (consumedProxyError ψ hψ t n + cropEnvelope ψ hψ t n) + cropEnvelope ψ hψ t n)
      atTop (𝓝 0)
  simpa only [Function.comp_def, mul_zero, Real.sqrt_zero,
    add_zero] using (hc.add ((hp.add hb).const_mul 2)).add hb

theorem generatedMarginalEnvelope_tendsto_zero (ψ : PhysicalIndex A B E C → ℂ)
    (hψ : normSq ψ = 1) {t : ℝ} (ht : 0 < t) :
    Tendsto (generatedMarginalEnvelope ψ hψ t) atTop (𝓝 0) := by
  have hc := Real.continuous_sqrt.continuousAt.tendsto.comp
    ((generatedCost_tendsto_zero ψ hψ ht).const_mul 3)
  have hp := generatedProxyError_tendsto_zero ψ hψ ht
  have hb := cropEnvelope_tendsto_zero ψ hψ ht
  change Tendsto (fun n => Real.sqrt (3 * generatedCost ψ hψ t n) +
    2 * (generatedProxyError ψ hψ t n + cropEnvelope ψ hψ t n) + cropEnvelope ψ hψ t n)
      atTop (𝓝 0)
  simpa only [Function.comp_def, mul_zero, Real.sqrt_zero,
    add_zero] using (hc.add ((hp.add hb).const_mul 2)).add hb

def recoveryEnvelope (ψ : PhysicalIndex A B E C → ℂ) (hψ : normSq ψ = 1)
    (t : ℝ) (n : ℕ) : ℝ := 2 * Real.sqrt (consumedMarginalEnvelope ψ hψ t n)

def sideEnvelope (ψ : PhysicalIndex A B E C → ℂ) (hψ : normSq ψ = 1)
    (t : ℝ) (n : ℕ) : ℝ :=
  Real.sqrt (consumedMarginalEnvelope ψ hψ t n) + generatedMarginalEnvelope ψ hψ t n / 2

theorem recoveryEnvelope_nonneg (ψ : PhysicalIndex A B E C → ℂ)
    (hψ : normSq ψ = 1) (t : ℝ) (n : ℕ) : 0 ≤ recoveryEnvelope ψ hψ t n :=
  mul_nonneg (by norm_num) (Real.sqrt_nonneg _)

theorem sideEnvelope_nonneg (ψ : PhysicalIndex A B E C → ℂ)
    (hψ : normSq ψ = 1) (t : ℝ) (n : ℕ) : 0 ≤ sideEnvelope ψ hψ t n :=
  add_nonneg (Real.sqrt_nonneg _) (div_nonneg (generatedMarginalEnvelope_nonneg ψ hψ t n)
    (by norm_num))

theorem recoveryEnvelope_tendsto_zero (ψ : PhysicalIndex A B E C → ℂ)
    (hψ : normSq ψ = 1) {t : ℝ} (ht : 0 < t) :
    Tendsto (recoveryEnvelope ψ hψ t) atTop (𝓝 0) := by
  have hs := Real.continuous_sqrt.continuousAt.tendsto.comp
    (consumedMarginalEnvelope_tendsto_zero ψ hψ ht)
  change Tendsto (fun n => 2 * Real.sqrt (consumedMarginalEnvelope ψ hψ t n)) atTop (𝓝 0)
  simpa only [Function.comp_def, Real.sqrt_zero, mul_zero] using hs.const_mul 2

theorem sideEnvelope_tendsto_zero (ψ : PhysicalIndex A B E C → ℂ)
    (hψ : normSq ψ = 1) {t : ℝ} (ht : 0 < t) :
    Tendsto (sideEnvelope ψ hψ t) atTop (𝓝 0) := by
  have hs := Real.continuous_sqrt.continuousAt.tendsto.comp
    (consumedMarginalEnvelope_tendsto_zero ψ hψ ht)
  have hg := (generatedMarginalEnvelope_tendsto_zero ψ hψ ht).div_const 2
  change Tendsto (fun n => Real.sqrt (consumedMarginalEnvelope ψ hψ t n) +
    generatedMarginalEnvelope ψ hψ t n / 2) atTop (𝓝 0)
  simpa only [Function.comp_def, Real.sqrt_zero, zero_div, add_zero] using hs.add hg

theorem exists_strict_physical_envelopes (ψ : PhysicalIndex A B E C → ℂ)
    (hψ : normSq ψ = 1) (q : ℝ) (hq : cmiNat ψ / 2 < q) :
    ∃ t : ℝ, 0 < t ∧
      sentRate (sentEntropyNat ψ) (consumedBudgetNat ψ) (generatedBudgetNat ψ) 4 t < q ∧
      Tendsto (recoveryEnvelope ψ hψ t) atTop (𝓝 0) ∧
      Tendsto (sideEnvelope ψ hψ t) atTop (𝓝 0) ∧
      Tendsto (fun n : ℕ => Real.log
        (sentDimension (sentEntropyNat ψ) (consumedBudgetNat ψ) (generatedBudgetNat ψ) 4 t n : ℝ) /
          (n : ℝ)) atTop
        (𝓝 (sentRate (sentEntropyNat ψ) (consumedBudgetNat ψ) (generatedBudgetNat ψ) 4 t)) := by
  obtain ⟨t, ht, hq', hr, _⟩ := exists_strict_pure_typical_data ψ hψ q hq
  exact ⟨t, ht, hq', recoveryEnvelope_tendsto_zero ψ hψ ht,
    sideEnvelope_tendsto_zero ψ hψ ht, hr⟩

def physicalPackingChart (ψ : PhysicalIndex A B E C → ℂ) (hψ : normSq ψ = 1)
    (t : ℝ) (ht : 0 ≤ t) (n : ℕ) :
    Fin (totalDimension (sentEntropyNat ψ) t n) ≃
      ((Fin (retainedDimension (consumedBudgetNat ψ) 4 t n) ×
        Fin (retainedDimension (generatedBudgetNat ψ) 4 t n)) ×
          Fin (sentDimension (sentEntropyNat ψ) (consumedBudgetNat ψ)
            (generatedBudgetNat ψ) 4 t n)) := by
  obtain ⟨hs, ha, hb, hab⟩ := scalar_packing_hypotheses ψ hψ
  exact packingChart hs ha hb hab (by norm_num : 0 ≤ (4 : ℝ)) ht n

theorem exists_strict_physical_threshold (ψ : PhysicalIndex A B E C → ℂ)
    (hψ : normSq ψ = 1) (q : ℝ) (hq : cmiNat ψ / 2 < q) :
    ∃ t : ℝ, 0 < t ∧
      sentRate (sentEntropyNat ψ) (consumedBudgetNat ψ) (generatedBudgetNat ψ) 4 t < q ∧
      ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        0 < senderAcceptance ψ hψ t n ∧
        (commonCarrier ψ hψ t n ⊗ₖ
          (1 : Matrix (TensorEntropy.TensorIndex (A × C) n)
            (TensorEntropy.TensorIndex (A × C) n) ℂ)) *
          consumedProxy ψ hψ t n = consumedProxy ψ hψ t n ∧
        (commonCarrier ψ hψ t n ⊗ₖ
          (1 : Matrix (TensorEntropy.TensorIndex (A × E) n)
            (TensorEntropy.TensorIndex (A × E) n) ℂ)) *
          generatedProxy ψ hψ t n = generatedProxy ψ hψ t n ∧
        recoveryEnvelope ψ hψ t n < ε ∧ sideEnvelope ψ hψ t n < ε ∧
        Real.log (sentDimension (sentEntropyNat ψ) (consumedBudgetNat ψ)
          (generatedBudgetNat ψ) 4 t n : ℝ) / (n : ℝ) < q := by
  obtain ⟨t, ht, hrate, hr, hs, hG⟩ := exists_strict_physical_envelopes ψ hψ q hq
  refine ⟨t, ht, hrate, ?_⟩
  intro ε hε
  have hevent : ∀ᶠ n : ℕ in atTop,
      0 < senderAcceptance ψ hψ t n ∧
      (commonCarrier ψ hψ t n ⊗ₖ
        (1 : Matrix (TensorEntropy.TensorIndex (A × C) n)
          (TensorEntropy.TensorIndex (A × C) n) ℂ)) *
        consumedProxy ψ hψ t n = consumedProxy ψ hψ t n ∧
      (commonCarrier ψ hψ t n ⊗ₖ
        (1 : Matrix (TensorEntropy.TensorIndex (A × E) n)
          (TensorEntropy.TensorIndex (A × E) n) ℂ)) *
        generatedProxy ψ hψ t n = generatedProxy ψ hψ t n ∧
      recoveryEnvelope ψ hψ t n < ε ∧ sideEnvelope ψ hψ t n < ε ∧
      Real.log (sentDimension (sentEntropyNat ψ) (consumedBudgetNat ψ)
        (generatedBudgetNat ψ) 4 t n : ℝ) / (n : ℝ) < q := by
    filter_upwards [senderAcceptance_eventually_pos ψ hψ ht,
      commonCarrier_support_eventually ψ hψ ht,
      hr.eventually (Iio_mem_nhds hε), hs.eventually (Iio_mem_nhds hε),
      hG.eventually (Iio_mem_nhds hrate)] with n ha hp hrn hsn hGn
    exact ⟨ha, hp.1, hp.2, hrn, hsn, hGn⟩
  exact Filter.eventually_atTop.mp hevent

section ActualCopies

open QuantumProver.DepolarizingSquashedEntanglement (Density)
open QuantumProver.DepolarizingSquashedEntanglement.BCYPurification
open QuantumProver.DepolarizingSquashedEntanglement.BCYRelativeEntropy

theorem canonical_cmi_eq_physical (ρ : Density (A × (B × E))) :
    cmiNat (sourceKet ρ) = QuantumProver.DepolarizingSquashedEntanglement.cmiNat (sourceMarginal ρ).matrix := by
  rw [cmiNat_eq_physical]
  have hm : reducedABE (sourceKet ρ) = (sourceMarginal ρ).matrix :=
    sourceKet_marginal ρ
  rw [hm]

def consumedCopyProxy (ρ : Density (A × (B × E))) (t : ℝ) (n : ℕ) :
    Matrix (CopyIndex B n × (CopyIndex A n × CopyIndex (A × (B × E)) n))
      (CopyIndex B n × (CopyIndex A n × CopyIndex (A × (B × E)) n)) ℂ :=
  Matrix.reindex (spectatorGrouping B A (A × (B × E)) n)
    (spectatorGrouping B A (A × (B × E)) n)
    (consumedProxy (sourceKet ρ) (sourceKet_normalized ρ) t n)

def generatedCopyProxy (ρ : Density (A × (B × E))) (t : ℝ) (n : ℕ) :
    Matrix (CopyIndex B n × (CopyIndex A n × CopyIndex E n))
      (CopyIndex B n × (CopyIndex A n × CopyIndex E n)) ℂ :=
  Matrix.reindex (spectatorGrouping B A E n) (spectatorGrouping B A E n)
    (generatedProxy (sourceKet ρ) (sourceKet_normalized ρ) t n)

theorem consumedCopyProxy_isDensity (ρ : Density (A × (B × E))) (t : ℝ) (n : ℕ) :
    FlaggedStates.IsDensity (consumedCopyProxy ρ t n) := by
  have hd := iidProxy_isDensity (sourceBAC_isDensity (sourceKet ρ) (sourceKet_normalized ρ)) t n
  exact ⟨hd.1.submatrix (spectatorGrouping B A (A × (B × E)) n).symm,
    (trace_reindex _ _).trans hd.2⟩

theorem generatedCopyProxy_isDensity (ρ : Density (A × (B × E))) (t : ℝ) (n : ℕ) :
    FlaggedStates.IsDensity (generatedCopyProxy ρ t n) := by
  have hd := iidProxy_isDensity (sourceBAE_isDensity (sourceKet ρ) (sourceKet_normalized ρ)) t n
  exact ⟨hd.1.submatrix (spectatorGrouping B A E n).symm, (trace_reindex _ _).trans hd.2⟩

theorem consumedCopyProxy_error (ρ : Density (A × (B × E))) (t : ℝ) (n : ℕ) :
    traceNorm (sourceBACCopies ρ n - consumedCopyProxy ρ t n) =
      consumedProxyError (sourceKet ρ) (sourceKet_normalized ρ) t n := by
  rw [sourceBACCopies_eq_groupedPower]
  change traceNorm (Matrix.reindex (spectatorGrouping B A (A × (B × E)) n)
    (spectatorGrouping B A (A × (B × E)) n)
    (groupedPower (sourceBAC (sourceKet ρ)) n -
      consumedProxy (sourceKet ρ) (sourceKet_normalized ρ) t n)) = _
  exact DiamondControl.nuclearNorm_submatrix_equiv
    (spectatorGrouping B A (A × (B × E)) n).symm _

theorem generatedCopyProxy_error (ρ : Density (A × (B × E))) (t : ℝ) (n : ℕ) :
    traceNorm (sourceBAECopies ρ n - generatedCopyProxy ρ t n) =
      generatedProxyError (sourceKet ρ) (sourceKet_normalized ρ) t n := by
  rw [sourceBAECopies_eq_groupedPower]
  change traceNorm (Matrix.reindex (spectatorGrouping B A E n) (spectatorGrouping B A E n)
    (groupedPower (sourceBAE (sourceKet ρ)) n -
      generatedProxy (sourceKet ρ) (sourceKet_normalized ρ) t n)) = _
  exact DiamondControl.nuclearNorm_submatrix_equiv (spectatorGrouping B A E n).symm _

theorem consumedCopyProxy_error_tendsto_zero (ρ : Density (A × (B × E)))
    {t : ℝ} (ht : 0 < t) :
    Tendsto (fun n => traceNorm (sourceBACCopies ρ n - consumedCopyProxy ρ t n))
      atTop (𝓝 0) := by
  simp_rw [consumedCopyProxy_error]
  exact consumedProxyError_tendsto_zero _ _ ht

theorem generatedCopyProxy_error_tendsto_zero (ρ : Density (A × (B × E)))
    {t : ℝ} (ht : 0 < t) :
    Tendsto (fun n => traceNorm (sourceBAECopies ρ n - generatedCopyProxy ρ t n))
      atTop (𝓝 0) := by
  simp_rw [generatedCopyProxy_error]
  exact generatedProxyError_tendsto_zero _ _ ht

theorem reindex_sender_support {X Y Z : Type*}
    [Fintype X] [Fintype Y] [Fintype Z]
    [DecidableEq X] [DecidableEq Y] [DecidableEq Z]
    (e : Y ≃ Z) (P : Matrix X X ℂ) (R : Matrix (X × Y) (X × Y) ℂ)
    (hs : (P ⊗ₖ (1 : Matrix Y Y ℂ)) * R = R) :
    (P ⊗ₖ (1 : Matrix Z Z ℂ)) *
      Matrix.reindex (Equiv.prodCongr (Equiv.refl X) e)
        (Equiv.prodCongr (Equiv.refl X) e) R =
      Matrix.reindex (Equiv.prodCongr (Equiv.refl X) e)
        (Equiv.prodCongr (Equiv.refl X) e) R := by
  let f := Equiv.prodCongr (Equiv.refl X) e
  have hP : Matrix.reindex f f (P ⊗ₖ (1 : Matrix Y Y ℂ)) =
      P ⊗ₖ (1 : Matrix Z Z ℂ) := by
    ext ⟨x,z⟩ ⟨x',z'⟩
    simp [f, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.kroneckerMap_apply,
      Matrix.one_apply]
  rw [← hP]
  change (Matrix.reindexRingEquiv ℂ f) (P ⊗ₖ (1 : Matrix Y Y ℂ)) *
    (Matrix.reindexRingEquiv ℂ f) R = (Matrix.reindexRingEquiv ℂ f) R
  rw [← (Matrix.reindexRingEquiv ℂ f).map_mul, hs]

theorem copyProxies_support_eventually (ρ : Density (A × (B × E)))
    {t : ℝ} (ht : 0 < t) :
    ∀ᶠ n : ℕ in atTop,
      (commonCarrier (sourceKet ρ) (sourceKet_normalized ρ) t n ⊗ₖ
        (1 : Matrix (CopyIndex A n × CopyIndex (A × (B × E)) n)
          (CopyIndex A n × CopyIndex (A × (B × E)) n) ℂ)) *
        consumedCopyProxy ρ t n = consumedCopyProxy ρ t n ∧
      (commonCarrier (sourceKet ρ) (sourceKet_normalized ρ) t n ⊗ₖ
        (1 : Matrix (CopyIndex A n × CopyIndex E n) (CopyIndex A n × CopyIndex E n) ℂ)) *
        generatedCopyProxy ρ t n = generatedCopyProxy ρ t n := by
  filter_upwards [commonCarrier_support_eventually (sourceKet ρ) (sourceKet_normalized ρ) ht]
    with n hn
  exact ⟨reindex_sender_support (powerGrouping A (A × (B × E)) n) _ _ hn.1,
    reindex_sender_support (powerGrouping A E n) _ _ hn.2⟩

theorem trace_square_reindex {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (e : I ≃ J) (R : Matrix I I ℂ) :
    (Matrix.reindex e e R * Matrix.reindex e e R).trace.re = (R * R).trace.re := by
  change ((Matrix.reindexRingEquiv ℂ e) R * (Matrix.reindexRingEquiv ℂ e) R).trace.re = _
  rw [← (Matrix.reindexRingEquiv ℂ e).map_mul]
  exact congrArg Complex.re (trace_reindex e (R * R))

theorem consumedCopyProxy_rank_purity (ρ : Density (A × (B × E))) (t : ℝ) (n : ℕ) :
    (Matrix.rank (partialTrace_left (consumedCopyProxy ρ t n)) : ℝ) *
      (consumedCopyProxy ρ t n * consumedCopyProxy ρ t n).trace.re =
        proxyRankPurity (sourceBAC_isDensity (sourceKet ρ) (sourceKet_normalized ρ)) t n := by
  unfold consumedCopyProxy proxyRankPurity consumedProxy
  rw [spectatorGrouping, partialTrace_left_reindex_spectator, Matrix.rank_reindex,
    trace_square_reindex]

theorem generatedCopyProxy_rank_purity (ρ : Density (A × (B × E))) (t : ℝ) (n : ℕ) :
    (Matrix.rank (partialTrace_left (generatedCopyProxy ρ t n)) : ℝ) *
      (generatedCopyProxy ρ t n * generatedCopyProxy ρ t n).trace.re =
        proxyRankPurity (sourceBAE_isDensity (sourceKet ρ) (sourceKet_normalized ρ)) t n := by
  unfold generatedCopyProxy proxyRankPurity generatedProxy
  rw [spectatorGrouping, partialTrace_left_reindex_spectator, Matrix.rank_reindex,
    trace_square_reindex]

end ActualCopies

section FiniteAssembly

open QuantumProver.DepolarizingSquashedEntanglement (IsNormalized pureDensity)
open QuantumProver.DepolarizingSquashedEntanglement.BCYRedistributionCode
open QuantumProver.DepolarizingSquashedEntanglement.BCYRedistributionResources
open QuantumProver.DepolarizingSquashedEntanglement.BCYNonlockability
open QuantumProver.QuantumRedistributionRealization
open QuantumProver.QuantumRedistributionTargetWires
open QuantumProver.QuantumRedistributionCarrierDecoupling
open QuantumProver.QuantumTypicalCarrier

variable {D F G K : Type*} [Fintype D] [Fintype F] [Fintype G] [Fintype K]
  [DecidableEq D] [DecidableEq F] [DecidableEq G] [DecidableEq K]

theorem rhoBAC_sourceCopies (ρ : QuantumProver.DepolarizingSquashedEntanglement.Density (A × (B × E))) (n : ℕ) :
    rhoBAC (QuantumProver.DepolarizingSquashedEntanglement.BCYPurification.sourceCopiesWireKet ρ n) = sourceBACCopies ρ n := by
  ext ⟨b,⟨a,c⟩⟩ ⟨b',⟨a',c'⟩⟩
  rfl

theorem rhoBAE_sourceCopies (ρ : QuantumProver.DepolarizingSquashedEntanglement.Density (A × (B × E))) (n : ℕ) :
    rhoBAE (QuantumProver.DepolarizingSquashedEntanglement.BCYPurification.sourceCopiesWireKet ρ n) = sourceBAECopies ρ n := by
  ext ⟨b,⟨a,e⟩⟩ ⟨b',⟨a',e'⟩⟩
  rfl

omit [Fintype A] [Fintype C] [DecidableEq A] [DecidableEq B] [DecidableEq E]
  [DecidableEq C] in
theorem rhoBAC_reference (v : (A × C) × (B × E) → ℂ) :
    partialTrace_left (rhoBAC v) = QuantumProver.DepolarizingSquashedEntanglement.partialTraceRight (pureDensity v) := by
  ext ⟨a,c⟩ ⟨a',c'⟩
  simp only [rhoBAC, sourceBACKet, partialTrace_left, QuantumProver.DepolarizingSquashedEntanglement.partialTraceRight,
    QuantumProver.WernerEndpoint.partialTraceLeft, pureDensity, QuantumProver.WernerEndpoint.pureDensity,
    QuantumProver.WernerEndpoint.crossDensity, Fintype.sum_prod_type]

omit [Fintype B] [DecidableEq A] [DecidableEq B] [DecidableEq E] [DecidableEq C] in
theorem senderMarginal_eq_rhoBAC (v : (A × C) × (B × E) → ℂ) :
    senderMarginal v = partialTrace_right (rhoBAC v) := by
  ext b b'
  change (∑ e : E, ∑ r : A × C, v (r,(b,e)) * star (v (r,(b',e)))) =
    ∑ r : A × C, ∑ e : E, v (r,(b,e)) * star (v (r,(b',e)))
  exact Finset.sum_comm

theorem senderMarginal_sourceCopies (ρ : QuantumProver.DepolarizingSquashedEntanglement.Density (A × (B × E))) (n : ℕ) :
    senderMarginal (QuantumProver.DepolarizingSquashedEntanglement.BCYPurification.sourceCopiesWireKet ρ n) =
      TensorEntropy.tensorPower (reducedB (QuantumProver.DepolarizingSquashedEntanglement.BCYPurification.sourceKet ρ)) n := by
  rw [senderMarginal_eq_rhoBAC, rhoBAC_sourceCopies, sourceBACCopies_sender]

theorem senderAction_eq_mulVec (M : Matrix K B ℂ) (v : (A × C) × (B × E) → ℂ) :
    senderAction M v = senderOperator (A × C) M E *ᵥ v := by
  ext ⟨r,⟨k,e⟩⟩
  exact (senderOperator_component M v r k e).symm

theorem traceNorm_sub_comm {I : Type*} [Fintype I] [DecidableEq I]
    (M N : Matrix I I ℂ) : traceNorm (M - N) = traceNorm (N - M) := by
  rw [show M - N = -(N - M) by abel]
  exact QuantumRedistributionRealization.traceNorm_neg _

theorem rhoBAC_traceNorm_sub_le (v w : (A × C) × (B × E) → ℂ) :
    traceNorm (rhoBAC v - rhoBAC w) ≤ traceNorm (pureDensity v - pureDensity w) := by
  have h := traceNorm_partialTraceRight_sub_le
    (pureDensity (sourceBACKet v)) (pureDensity (sourceBACKet w))
  change traceNorm (rhoBAC v - rhoBAC w) ≤ traceNorm
    (Matrix.reindex (sourceBACEquiv A C B E) (sourceBACEquiv A C B E)
      (pureDensity v - pureDensity w)) at h
  exact h.trans_eq (DiamondControl.nuclearNorm_submatrix_equiv
    (sourceBACEquiv A C B E).symm _)

theorem rhoBAE_traceNorm_sub_le (v w : (A × C) × (B × E) → ℂ) :
    traceNorm (rhoBAE v - rhoBAE w) ≤ traceNorm (pureDensity v - pureDensity w) := by
  have h := traceNorm_partialTraceRight_sub_le
    (pureDensity (sourceBAEKet v)) (pureDensity (sourceBAEKet w))
  change traceNorm (rhoBAE v - rhoBAE w) ≤ traceNorm
    (Matrix.reindex (sourceBAEEquiv A C B E) (sourceBAEEquiv A C B E)
      (pureDensity v - pureDensity w)) at h
  exact h.trans_eq (DiamondControl.nuclearNorm_submatrix_equiv
    (sourceBAEEquiv A C B E).symm _)

theorem local_sandwich_support {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y] (P : Matrix X X ℂ) (hP : PetzSmoothing.IsProjection P)
    (R : Matrix (X × Y) (X × Y) ℂ) (hR : R.IsHermitian)
    (hs : (P ⊗ₖ (1 : Matrix Y Y ℂ)) * R * (P ⊗ₖ (1 : Matrix Y Y ℂ))ᴴ = R) :
    carrierSupport P R := by
  apply carrierSupport_of_left hP.selfAdjoint hR
  let L := P ⊗ₖ (1 : Matrix Y Y ℂ)
  have hL : L * L = L := by
    dsimp only [L]
    rw [← Matrix.mul_kronecker_mul, hP.idempotent, Matrix.one_mul]
  change L * R = R
  calc
    L * R = L * (L * R * Lᴴ) := by rw [hs]
    _ = (L * L) * R * Lᴴ := by simp only [Matrix.mul_assoc]
    _ = R := by rw [hL, hs]

theorem senderPureCrop_marginals_supported (P : Matrix B B ℂ)
    (hP : PetzSmoothing.IsProjection P) (v : (A × C) × (B × E) → ℂ)
    (ht : 0 < (PetzSmoothing.cropMap (senderProjection (A × C) P E)
      (pureDensity v)).trace.re) :
    carrierSupport P (rhoBAC (normalizedPureCrop (senderProjection (A × C) P E) v)) ∧
    carrierSupport P (rhoBAE (normalizedPureCrop (senderProjection (A × C) P E) v)) := by
  let z := normalizedPureCrop (senderProjection (A × C) P E) v
  have hz : senderAction P z = z := by
    rw [senderAction_eq_mulVec]
    exact senderPureCrop_fixed P hP v ht
  have h1 : (P ⊗ₖ (1 : Matrix (A × C) (A × C) ℂ)) * rhoBAC z *
      (P ⊗ₖ (1 : Matrix (A × C) (A × C) ℂ))ᴴ = rhoBAC z := by
    rw [← rhoBAC_senderAction, hz]
  have h2 : (P ⊗ₖ (1 : Matrix (A × E) (A × E) ℂ)) * rhoBAE z *
      (P ⊗ₖ (1 : Matrix (A × E) (A × E) ℂ))ᴴ = rhoBAE z := by
    rw [← rhoBAE_senderAction, hz]
  exact ⟨local_sandwich_support P hP _ (rhoBAC_posSemidef z).isHermitian h1,
    local_sandwich_support P hP _ (rhoBAE_posSemidef z).isHermitian h2⟩

omit [DecidableEq F] [DecidableEq G] in
theorem codeFirstMarginalError_perturbation [Nonempty D]
    (v w : (A × C) × (B × E) → ℂ)
    (φ : ((A × C) × D) × ((E × F) × G) → ℂ) :
    codeFirstMarginalError v φ ≤ codeFirstMarginalError w φ +
      traceNorm (pureDensity v - pureDensity w) := by
  have htri := QuantumRedistributionRealization.traceNorm_triangle
    (QuantumProver.DepolarizingSquashedEntanglement.partialTraceRight (pureDensity v) ⊗ₖ (uniformDensity D).matrix)
    (QuantumProver.DepolarizingSquashedEntanglement.partialTraceRight (pureDensity w) ⊗ₖ (uniformDensity D).matrix)
    (QuantumProver.DepolarizingSquashedEntanglement.partialTraceRight (pureDensity φ))
  have happ := traceNorm_channel_sub_le (appendRightChannel (uniformDensity D))
    (QuantumProver.DepolarizingSquashedEntanglement.partialTraceRight (pureDensity v))
    (QuantumProver.DepolarizingSquashedEntanglement.partialTraceRight (pureDensity w))
  have hdis := traceNorm_partialTraceRight_sub_le (pureDensity v) (pureDensity w)
  change traceNorm (QuantumProver.DepolarizingSquashedEntanglement.partialTraceRight (pureDensity v) ⊗ₖ
    (uniformDensity D).matrix - QuantumProver.DepolarizingSquashedEntanglement.partialTraceRight (pureDensity w) ⊗ₖ
      (uniformDensity D).matrix) ≤
    traceNorm (QuantumProver.DepolarizingSquashedEntanglement.partialTraceRight (pureDensity v) -
      QuantumProver.DepolarizingSquashedEntanglement.partialTraceRight (pureDensity w)) at happ
  change codeFirstMarginalError v φ ≤
    traceNorm (QuantumProver.DepolarizingSquashedEntanglement.partialTraceRight (pureDensity v) ⊗ₖ (uniformDensity D).matrix -
      QuantumProver.DepolarizingSquashedEntanglement.partialTraceRight (pureDensity w) ⊗ₖ (uniformDensity D).matrix) +
      codeFirstMarginalError w φ at htri
  change traceNorm (QuantumProver.DepolarizingSquashedEntanglement.partialTraceRight (pureDensity v) -
    QuantumProver.DepolarizingSquashedEntanglement.partialTraceRight (pureDensity w)) ≤ traceNorm (pureDensity v - pureDensity w) at hdis
  linarith

theorem uniformDensity_matrix_complex {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I] :
    (uniformDensity I).matrix = ((Fintype.card I : ℂ)⁻¹) • (1 : Matrix I I ℂ) := by
  ext i j
  simp [uniformDensity, Complex.real_smul, Complex.ofReal_inv]

theorem codeReference_eq_physicalRef [Nonempty F]
    (v : (A × C) × (B × E) → ℂ) (hv : IsNormalized v) :
    (FiniteCode.reference (F := F) (codeSourceDensity v hv)).matrix =
      Matrix.reindex (retainedChart A E F) (retainedChart A E F)
        (carrierUniformReference F (rhoBAE v)) := by
  ext ⟨a,⟨e,f⟩⟩ ⟨a',⟨e',f'⟩⟩
  change (∑ b : B, ∑ c : C, v ((a,c),(b,e)) * star (v ((a',c),(b,e')))) *
      (uniformDensity F).matrix f f' =
    (((Fintype.card F : ℂ)⁻¹) • (1 : Matrix F F ℂ)) f f' *
      (∑ b : B, ∑ c : C, v ((a,c),(b,e)) * star (v ((a',c),(b,e'))))
  rw [← uniformDensity_matrix_complex]
  exact mul_comm _ _

theorem matrix_traceNorm_reindex {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (e : I ≃ J) (M : Matrix I I ℂ) :
    traceNorm (Matrix.reindex e e M) = traceNorm M :=
  DiamondControl.nuclearNorm_submatrix_equiv e.symm M

theorem uniform_left_difference_norm_le {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] [Nonempty I] (M N : Matrix J J ℂ) :
    traceNorm ((uniformDensity I).matrix ⊗ₖ M - (uniformDensity I).matrix ⊗ₖ N) ≤
      traceNorm (M - N) := by
  have h := traceNorm_channel_sub_le (appendRightChannel (uniformDensity I)) M N
  change traceNorm (M ⊗ₖ (uniformDensity I).matrix - N ⊗ₖ (uniformDensity I).matrix) ≤
    traceNorm (M - N) at h
  have he : Matrix.reindex (Equiv.prodComm J I) (Equiv.prodComm J I)
      (M ⊗ₖ (uniformDensity I).matrix - N ⊗ₖ (uniformDensity I).matrix) =
        (uniformDensity I).matrix ⊗ₖ M - (uniformDensity I).matrix ⊗ₖ N := by
    ext ⟨i,j⟩ ⟨i',j'⟩
    change M j j' * (uniformDensity I).matrix i i' - N j j' * (uniformDensity I).matrix i i' =
      (uniformDensity I).matrix i i' * M j j' - (uniformDensity I).matrix i i' * N j j'
    ring
  rw [← he, matrix_traceNorm_reindex]
  exact h

theorem carrierUniformReference_difference_norm_le {X Y I : Type*}
    [Fintype X] [Fintype Y] [Fintype I] [DecidableEq X] [DecidableEq Y]
    [DecidableEq I] [Nonempty I] (M N : Matrix (X × Y) (X × Y) ℂ) :
    traceNorm (carrierUniformReference I M - carrierUniformReference I N) ≤ traceNorm (M - N) := by
  unfold carrierUniformReference
  rw [← uniformDensity_matrix_complex]
  have h := uniform_left_difference_norm_le (I := I) (partialTrace_left M) (partialTrace_left N)
  have hp := QuantumProver.QuantumDecouplingRobust.partialTrace_left_traceNorm_le (M - N)
  have he : partialTrace_left (M - N) = partialTrace_left M - partialTrace_left N := by
    ext i j
    simp only [partialTrace_left, Matrix.sub_apply, Finset.sum_sub_distrib]
  change traceNorm (partialTrace_left (M - N)) ≤ traceNorm (M - N) at hp
  rw [he] at hp
  exact h.trans hp

theorem codeReference_difference_norm_le [Nonempty F]
    (v w : (A × C) × (B × E) → ℂ) (hv : IsNormalized v) (hw : IsNormalized w) :
    traceNorm ((FiniteCode.reference (F := F) (codeSourceDensity v hv)).matrix -
      (FiniteCode.reference (F := F) (codeSourceDensity w hw)).matrix) ≤
      traceNorm (pureDensity v - pureDensity w) := by
  rw [codeReference_eq_physicalRef, codeReference_eq_physicalRef]
  change traceNorm (Matrix.reindex (retainedChart A E F) (retainedChart A E F)
    (carrierUniformReference F (rhoBAE v) - carrierUniformReference F (rhoBAE w))) ≤ _
  rw [matrix_traceNorm_reindex]
  exact (carrierUniformReference_difference_norm_le (rhoBAE v) (rhoBAE w)).trans
    (rhoBAE_traceNorm_sub_le v w)

omit [DecidableEq D] [DecidableEq G] in
theorem codeRetainedTargetError_perturbation [Nonempty F]
    (v w : (A × C) × (B × E) → ℂ) (hv : IsNormalized v) (hw : IsNormalized w)
    (φ : ((A × C) × D) × ((E × F) × G) → ℂ) :
    codeRetainedTargetError v hv φ ≤ codeRetainedTargetError w hw φ +
      traceNorm (pureDensity v - pureDensity w) := by
  have ht := QuantumRedistributionRealization.traceNorm_triangle (codeTargetRetained φ)
    (FiniteCode.reference (F := F) (codeSourceDensity w hw)).matrix
    (FiniteCode.reference (F := F) (codeSourceDensity v hv)).matrix
  change codeRetainedTargetError v hv φ ≤ codeRetainedTargetError w hw φ +
    traceNorm ((FiniteCode.reference (F := F) (codeSourceDensity w hw)).matrix -
      (FiniteCode.reference (F := F) (codeSourceDensity v hv)).matrix) at ht
  have h := codeReference_difference_norm_le (F := F) w v hw hv
  rw [traceNorm_sub_comm (pureDensity w) (pureDensity v)] at h
  exact ht.trans (add_le_add_right h _)

omit [DecidableEq E] in
theorem compressed_target_first_error {d : ℕ} [Nonempty D]
    (p : Fin d ≃ ((D × F) × G)) (U : QuantumProver.UnitarySecondMoment.UGroup d)
    (V : Matrix B (Fin d) ℂ) (z : (A × C) × (B × E) → ℂ) :
    codeFirstMarginalError z (targetKet p U (senderAction Vᴴ z)) =
      traceNorm (carrierDecouplingError (chartD p) V (rhoBAC z) U) := by
  have href : QuantumProver.DepolarizingSquashedEntanglement.partialTraceRight (pureDensity z) ⊗ₖ (uniformDensity D).matrix =
      Matrix.reindex (Equiv.prodComm D (A × C)) (Equiv.prodComm D (A × C))
        (carrierUniformReference D (rhoBAC z)) := by
    rw [← rhoBAC_reference]
    unfold carrierUniformReference
    rw [← uniformDensity_matrix_complex]
    ext ⟨r,k⟩ ⟨s,l⟩
    exact mul_comm _ _
  have hρ : rhoBAC (senderAction Vᴴ z) = carrierCompression V (A × C) (rhoBAC z) :=
    by simpa only [carrierCompression, carrierLift, Matrix.conjTranspose_kronecker,
      Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_one] using rhoBAC_senderAction Vᴴ z
  have hm : QuantumProver.QuantumDecoupling.decoupledMarginal (chartD p)
      (rhoBAC (senderAction Vᴴ z)) U = carrierDecoupledMarginal (chartD p) V (rhoBAC z) U :=
    (congrArg (fun R => QuantumProver.QuantumDecoupling.decoupledMarginal (chartD p) R U) hρ).trans
      (carrierDecoupledMarginal_eq_compressed (chartD p) V (rhoBAC z) U).symm
  have htarget := (target_firstMarginal p U (senderAction Vᴴ z)).trans
    (congrArg (Matrix.reindex (Equiv.prodComm D (A × C)) (Equiv.prodComm D (A × C))) hm)
  change traceNorm (QuantumProver.DepolarizingSquashedEntanglement.partialTraceRight (pureDensity z) ⊗ₖ (uniformDensity D).matrix -
    QuantumProver.DepolarizingSquashedEntanglement.partialTraceRight (pureDensity (targetKet p U (senderAction Vᴴ z)))) = _
  calc
    _ = traceNorm (Matrix.reindex (Equiv.prodComm D (A × C)) (Equiv.prodComm D (A × C))
          (carrierUniformReference D (rhoBAC z)) -
        Matrix.reindex (Equiv.prodComm D (A × C)) (Equiv.prodComm D (A × C))
          (carrierDecoupledMarginal (chartD p) V (rhoBAC z) U)) :=
      congrArg₂ (fun M N => traceNorm (M - N)) href htarget
    _ = traceNorm (Matrix.reindex (Equiv.prodComm D (A × C)) (Equiv.prodComm D (A × C))
          (carrierUniformReference D (rhoBAC z) - carrierDecoupledMarginal (chartD p) V (rhoBAC z) U)) := rfl
    _ = traceNorm (carrierUniformReference D (rhoBAC z) - carrierDecoupledMarginal (chartD p) V (rhoBAC z) U) :=
      matrix_traceNorm_reindex _ _
    _ = _ := traceNorm_sub_comm _ _

theorem compressed_target_retained_error {d : ℕ} [Nonempty F]
    (p : Fin d ≃ ((D × F) × G)) (U : QuantumProver.UnitarySecondMoment.UGroup d)
    (V : Matrix B (Fin d) ℂ) (z : (A × C) × (B × E) → ℂ)
    (hz : IsNormalized z) :
    codeRetainedTargetError z hz (targetKet p U (senderAction Vᴴ z)) =
      traceNorm (carrierDecouplingError (chartF p) V (rhoBAE z) U) := by
  have hρ : rhoBAE (senderAction Vᴴ z) = carrierCompression V (A × E) (rhoBAE z) :=
    by simpa only [carrierCompression, carrierLift, Matrix.conjTranspose_kronecker,
      Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_one] using rhoBAE_senderAction Vᴴ z
  have hm : QuantumProver.QuantumDecoupling.decoupledMarginal (chartF p)
      (rhoBAE (senderAction Vᴴ z)) U = carrierDecoupledMarginal (chartF p) V (rhoBAE z) U :=
    (congrArg (fun R => QuantumProver.QuantumDecoupling.decoupledMarginal (chartF p) R U) hρ).trans
      (carrierDecoupledMarginal_eq_compressed (chartF p) V (rhoBAE z) U).symm
  have htarget := (target_retainedMarginal p U (senderAction Vᴴ z)).trans
    (congrArg (Matrix.reindex (retainedChart A E F) (retainedChart A E F)) hm)
  have href := codeReference_eq_physicalRef (F := F) z hz
  change traceNorm (retainedTarget p U (senderAction Vᴴ z) -
    (FiniteCode.reference (F := F) (codeSourceDensity z hz)).matrix) = _
  calc
    _ = traceNorm (Matrix.reindex (retainedChart A E F) (retainedChart A E F)
          (carrierDecoupledMarginal (chartF p) V (rhoBAE z) U) -
        Matrix.reindex (retainedChart A E F) (retainedChart A E F)
          (carrierUniformReference F (rhoBAE z))) :=
      congrArg₂ (fun M N => traceNorm (M - N)) htarget href
    _ = traceNorm (Matrix.reindex (retainedChart A E F) (retainedChart A E F)
          (carrierDecoupledMarginal (chartF p) V (rhoBAE z) U - carrierUniformReference F (rhoBAE z))) := rfl
    _ = _ := matrix_traceNorm_reindex _ _

def finiteCropEnvelope (P : Matrix B B ℂ) (v : (A × C) × (B × E) → ℂ) : ℝ :=
  4 * Real.sqrt (1 - (senderMarginal v * P).trace.re)

def finiteConsumedEnvelope (d : ℕ) (P : Matrix B B ℂ)
    (v : (A × C) × (B × E) → ℂ)
    (ν : Matrix (B × (A × C)) (B × (A × C)) ℂ) : ℝ :=
  Real.sqrt (3 * physicalCarrierDecouplingCost d D ν) +
    2 * (traceNorm (rhoBAC v - ν) + finiteCropEnvelope P v) + finiteCropEnvelope P v

def finiteGeneratedEnvelope (d : ℕ) (P : Matrix B B ℂ)
    (v : (A × C) × (B × E) → ℂ)
    (ν : Matrix (B × (A × E)) (B × (A × E)) ℂ) : ℝ :=
  Real.sqrt (3 * physicalCarrierDecouplingCost d F ν) +
    2 * (traceNorm (rhoBAE v - ν) + finiteCropEnvelope P v) + finiteCropEnvelope P v

theorem exists_finiteCode_from_supported_proxies {d : ℕ}
    [Nonempty B] [Nonempty E] [Nonempty D] [Nonempty F] [Nonempty G]
    (v : (A × C) × (B × E) → ℂ) (hv : IsNormalized v)
    (P : Matrix B B ℂ) (hP : PetzSmoothing.IsProjection P) (hrank : P.rank ≤ d)
    (p : Fin d ≃ ((D × F) × G))
    (ν₁ : Matrix (B × (A × C)) (B × (A × C)) ℂ)
    (ν₂ : Matrix (B × (A × E)) (B × (A × E)) ℂ)
    (hν₁ : ν₁.PosSemidef) (hν₂ : ν₂.PosSemidef)
    (hsν₁ : carrierSupport P ν₁) (hsν₂ : carrierSupport P ν₂)
    (ht : 0 < (PetzSmoothing.cropMap (senderProjection (A × C) P E) (pureDensity v)).trace.re) :
    ∃ code : FiniteCode B E D F G,
      code.recoveryError (codeSourceDensity v hv) ≤
        2 * Real.sqrt (finiteConsumedEnvelope (D := D) d P v ν₁) ∧
      code.sideError (codeSourceDensity v hv) ≤
        Real.sqrt (finiteConsumedEnvelope (D := D) d P v ν₁) +
          finiteGeneratedEnvelope (F := F) d P v ν₂ / 2 := by
  let z := normalizedPureCrop (senderProjection (A × C) P E) v
  let V := paddedCarrier P hP d hrank
  have hV : V * Vᴴ = P := paddedCarrier_projection P hP d hrank
  have hz : IsNormalized z := normalizedPureCrop_isNormalized _ v hv
  obtain ⟨hsρ₁, hsρ₂⟩ := senderPureCrop_marginals_supported P hP v ht
  have hdist : traceNorm (pureDensity v - pureDensity z) ≤ finiteCropEnvelope P v :=
    senderPureCrop_error P hP v hv
  have hclose₁ : traceNorm (rhoBAC z - ν₁) ≤
      traceNorm (rhoBAC v - ν₁) + finiteCropEnvelope P v := by
    have h := (rhoBAC_traceNorm_sub_le z v).trans
      ((traceNorm_sub_comm (pureDensity z) (pureDensity v)).le.trans hdist)
    have ht' := QuantumRedistributionRealization.traceNorm_triangle (rhoBAC z) (rhoBAC v) ν₁
    change traceNorm (rhoBAC z - ν₁) ≤ traceNorm (rhoBAC z - rhoBAC v) +
      traceNorm (rhoBAC v - ν₁) at ht'
    linarith
  have hclose₂ : traceNorm (rhoBAE z - ν₂) ≤
      traceNorm (rhoBAE v - ν₂) + finiteCropEnvelope P v := by
    have h := (rhoBAE_traceNorm_sub_le z v).trans
      ((traceNorm_sub_comm (pureDensity z) (pureDensity v)).le.trans hdist)
    have ht' := QuantumRedistributionRealization.traceNorm_triangle (rhoBAE z) (rhoBAE v) ν₂
    change traceNorm (rhoBAE z - ν₂) ≤ traceNorm (rhoBAE z - rhoBAE v) +
      traceNorm (rhoBAE v - ν₂) at ht'
    linarith
  obtain ⟨U, hU₁, hU₂⟩ := exists_common_carrier_decoupling_unitary
    (chartD p) (chartF p) hP hV (rhoBAC z) ν₁ (rhoBAE z) ν₂ hν₁ hν₂
    hsρ₁ hsν₁ hsρ₂ hsν₂ hclose₁ hclose₂
  change traceNorm (carrierDecouplingError (chartD p) V (rhoBAC z) U) ≤
    Real.sqrt (3 * physicalCarrierDecouplingCost d D ν₁) +
      2 * (traceNorm (rhoBAC v - ν₁) + finiteCropEnvelope P v) at hU₁
  change traceNorm (carrierDecouplingError (chartF p) V (rhoBAE z) U) ≤
    Real.sqrt (3 * physicalCarrierDecouplingCost d F ν₂) +
      2 * (traceNorm (rhoBAE v - ν₂) + finiteCropEnvelope P v) at hU₂
  let χ := senderAction Vᴴ z
  have hχ : IsNormalized χ := by
    change IsNormalized (senderAction Vᴴ z)
    rw [senderAction_eq_mulVec]
    exact senderCompressedCrop_isNormalized V P hP hV v hv ht
  let φ := targetKet p U χ
  have hφ : IsNormalized φ := targetKet_normalized p U χ hχ
  have hfirst : codeFirstMarginalError v φ ≤ finiteConsumedEnvelope (D := D) d P v ν₁ := by
    have ht' := codeFirstMarginalError_perturbation v z φ
    have he : codeFirstMarginalError z φ =
        traceNorm (carrierDecouplingError (chartD p) V (rhoBAC z) U) :=
      compressed_target_first_error p U V z
    rw [he] at ht'
    unfold finiteConsumedEnvelope
    linarith
  have hsecond : codeRetainedTargetError v hv φ ≤ finiteGeneratedEnvelope (F := F) d P v ν₂ := by
    have ht' := codeRetainedTargetError_perturbation v z hv hz φ
    have he : codeRetainedTargetError z hz φ =
        traceNorm (carrierDecouplingError (chartF p) V (rhoBAE z) U) :=
      compressed_target_retained_error p U V z hz
    rw [he] at ht'
    unfold finiteGeneratedEnvelope
    linarith
  obtain ⟨code, _, hrec, hside⟩ := exists_finiteCode_from_pure_target v hv φ hφ
  exact ⟨code, hrec.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hfirst) (by norm_num)),
    hside.trans (add_le_add (Real.sqrt_le_sqrt hfirst) (div_le_div_of_nonneg_right hsecond (by norm_num)))⟩

end FiniteAssembly

section PhysicalFamily

open QuantumProver.DepolarizingSquashedEntanglement (Density IsNormalized pureDensity)
open QuantumProver.DepolarizingSquashedEntanglement.BCYRelativeEntropy QuantumProver.DepolarizingSquashedEntanglement.BCYPurification
open QuantumProver.DepolarizingSquashedEntanglement.BCYRedistributionCode QuantumProver.DepolarizingSquashedEntanglement.BCYNonlockability
open QuantumProver.QuantumRedistributionRealization QuantumProver.QuantumRedistributionTargetWires
open QuantumProver.QuantumRedistributionCarrierDecoupling QuantumProver.QuantumTypicalCarrier

instance retainedRegister_nonempty (a c t : ℝ) (n : ℕ) :
    Nonempty (Fin (retainedDimension a c t n)) := ⟨⟨0, retainedDimension_pos a c t n⟩⟩

instance sentRegister_nonempty (s a b c t : ℝ) (n : ℕ) :
    Nonempty (Fin (sentDimension s a b c t n)) := ⟨⟨0, sentDimension_pos s a b c t n⟩⟩

abbrev InputRegister (ρ : Density (A × (B × E))) (t : ℝ) (n : ℕ) :=
  Fin (retainedDimension (consumedBudgetNat (sourceKet ρ)) 4 t n)

abbrev OutputRegister (ρ : Density (A × (B × E))) (t : ℝ) (n : ℕ) :=
  Fin (retainedDimension (generatedBudgetNat (sourceKet ρ)) 4 t n)

abbrev MessageRegister (ρ : Density (A × (B × E))) (t : ℝ) (n : ℕ) :=
  Fin (sentDimension (sentEntropyNat (sourceKet ρ)) (consumedBudgetNat (sourceKet ρ))
    (generatedBudgetNat (sourceKet ρ)) 4 t n)

abbrev CopyFiniteCode (ρ : Density (A × (B × E))) (t : ℝ) (n : ℕ) :=
  FiniteCode (CopyIndex B n) (CopyIndex E n)
    (InputRegister ρ t n) (OutputRegister ρ t n) (MessageRegister ρ t n)

theorem copyIndex_nonempty (X : Type*) [Nonempty X] (n : ℕ) : Nonempty (CopyIndex X n) := by
  induction n with
  | zero => exact ⟨PUnit.unit⟩
  | succ n hn => exact ⟨(Classical.choice hn, Classical.arbitrary X)⟩

theorem commonCarrier_isProjection (ψ : PhysicalIndex A B E C → ℂ)
    (hψ : normSq ψ = 1) (t : ℝ) (n : ℕ) :
    PetzSmoothing.IsProjection (commonCarrier ψ hψ t n) := by
  rw [commonCarrier_eq_matrix_typical]
  exact typicalProjector_isProjection _ _ _

theorem consumedCopy_cost_eq (ρ : Density (A × (B × E))) (t : ℝ) (n : ℕ) :
    physicalCarrierDecouplingCost (totalDimension (sentEntropyNat (sourceKet ρ)) t n)
      (InputRegister ρ t n) (consumedCopyProxy ρ t n) =
        consumedCost (sourceKet ρ) (sourceKet_normalized ρ) t n := by
  unfold physicalCarrierDecouplingCost consumedCost clippedCost InputRegister
  simp only [Fintype.card_fin]
  split_ifs
  · rfl
  · rw [mul_assoc, consumedCopyProxy_rank_purity]

theorem generatedCopy_cost_eq (ρ : Density (A × (B × E))) (t : ℝ) (n : ℕ) :
    physicalCarrierDecouplingCost (totalDimension (sentEntropyNat (sourceKet ρ)) t n)
      (OutputRegister ρ t n) (generatedCopyProxy ρ t n) =
        generatedCost (sourceKet ρ) (sourceKet_normalized ρ) t n := by
  unfold physicalCarrierDecouplingCost generatedCost clippedCost OutputRegister
  simp only [Fintype.card_fin]
  split_ifs
  · rfl
  · rw [mul_assoc, generatedCopyProxy_rank_purity]

theorem finiteCropEnvelope_copy_eq (ρ : Density (A × (B × E))) (t : ℝ) (n : ℕ) :
    finiteCropEnvelope (commonCarrier (sourceKet ρ) (sourceKet_normalized ρ) t n)
      (sourceCopiesWireKet ρ n) = cropEnvelope (sourceKet ρ) (sourceKet_normalized ρ) t n := by
  unfold finiteCropEnvelope cropEnvelope senderAcceptance
  rw [senderMarginal_sourceCopies]

theorem finiteConsumedEnvelope_copy_eq (ρ : Density (A × (B × E))) (t : ℝ) (n : ℕ) :
    finiteConsumedEnvelope (D := InputRegister ρ t n)
      (totalDimension (sentEntropyNat (sourceKet ρ)) t n)
      (commonCarrier (sourceKet ρ) (sourceKet_normalized ρ) t n)
      (sourceCopiesWireKet ρ n) (consumedCopyProxy ρ t n) =
        consumedMarginalEnvelope (sourceKet ρ) (sourceKet_normalized ρ) t n := by
  unfold finiteConsumedEnvelope consumedMarginalEnvelope
  rw [consumedCopy_cost_eq, rhoBAC_sourceCopies, consumedCopyProxy_error, finiteCropEnvelope_copy_eq]

theorem finiteGeneratedEnvelope_copy_eq (ρ : Density (A × (B × E))) (t : ℝ) (n : ℕ) :
    finiteGeneratedEnvelope (F := OutputRegister ρ t n)
      (totalDimension (sentEntropyNat (sourceKet ρ)) t n)
      (commonCarrier (sourceKet ρ) (sourceKet_normalized ρ) t n)
      (sourceCopiesWireKet ρ n) (generatedCopyProxy ρ t n) =
        generatedMarginalEnvelope (sourceKet ρ) (sourceKet_normalized ρ) t n := by
  unfold finiteGeneratedEnvelope generatedMarginalEnvelope
  rw [generatedCopy_cost_eq, rhoBAE_sourceCopies, generatedCopyProxy_error, finiteCropEnvelope_copy_eq]

def copyCropMass (ρ : Density (A × (B × E))) (t : ℝ) (n : ℕ) : ℝ := by
  classical
  exact (PetzSmoothing.cropMap
    (senderProjection (CopyIndex A n × CopyIndex (A × (B × E)) n)
      (commonCarrier (sourceKet ρ) (sourceKet_normalized ρ) t n) (CopyIndex E n))
    (pureDensity (sourceCopiesWireKet ρ n))).trace.re

theorem copy_crop_mass_eq_acceptance (ρ : Density (A × (B × E))) (t : ℝ) (n : ℕ) :
    copyCropMass ρ t n = senderAcceptance (sourceKet ρ) (sourceKet_normalized ρ) t n := by
  classical
  unfold copyCropMass
  have hP := commonCarrier_isProjection (sourceKet ρ) (sourceKet_normalized ρ) t n
  rw [PetzSmoothing.cropMap_trace (senderProjection_isProjection _ hP)]
  have he : (pureDensity (sourceCopiesWireKet ρ n) *
      senderProjection (CopyIndex A n × CopyIndex (A × (B × E)) n)
        (commonCarrier (sourceKet ρ) (sourceKet_normalized ρ) t n) (CopyIndex E n)).trace =
      (senderMarginal (sourceCopiesWireKet ρ n) *
        commonCarrier (sourceKet ρ) (sourceKet_normalized ρ) t n).trace :=
    senderProjection_acceptance _ _
  rw [he, senderMarginal_sourceCopies]
  rfl

theorem exists_eventual_copy_codes (ρ : Density (A × (B × E)))
    {t : ℝ} (ht : 0 < t) :
    ∀ᶠ n : ℕ in atTop, ∃ code : CopyFiniteCode ρ t n,
      code.recoveryError (tripleCopies ρ n) ≤ recoveryEnvelope (sourceKet ρ) (sourceKet_normalized ρ) t n ∧
      code.sideError (tripleCopies ρ n) ≤ sideEnvelope (sourceKet ρ) (sourceKet_normalized ρ) t n := by
  classical
  have hsource := sourcePurifier_nonempty ρ
  have : Nonempty B := hsource.map (fun x => x.2.1)
  have : Nonempty E := hsource.map (fun x => x.2.2)
  filter_upwards [senderAcceptance_eventually_pos (sourceKet ρ) (sourceKet_normalized ρ) ht,
    copyProxies_support_eventually ρ ht] with n hm hsupport
  have : Nonempty (CopyIndex B n) := copyIndex_nonempty B n
  have : Nonempty (CopyIndex E n) := copyIndex_nonempty E n
  let P := commonCarrier (sourceKet ρ) (sourceKet_normalized ρ) t n
  have hP : PetzSmoothing.IsProjection P := commonCarrier_isProjection _ _ _ _
  have hs₁ : carrierSupport P (consumedCopyProxy ρ t n) :=
    carrierSupport_of_left hP.selfAdjoint (consumedCopyProxy_isDensity ρ t n).1.isHermitian hsupport.1
  have hs₂ : carrierSupport P (generatedCopyProxy ρ t n) :=
    carrierSupport_of_left hP.selfAdjoint (generatedCopyProxy_isDensity ρ t n).1.isHermitian hsupport.2
  have hmass : 0 < (PetzSmoothing.cropMap
      (senderProjection (CopyIndex A n × CopyIndex (A × (B × E)) n) P (CopyIndex E n))
      (pureDensity (sourceCopiesWireKet ρ n))).trace.re := by
    change 0 < copyCropMass ρ t n
    rw [copy_crop_mass_eq_acceptance]
    exact hm
  obtain ⟨code, hrec, hside⟩ := exists_finiteCode_from_supported_proxies
    (sourceCopiesWireKet ρ n) (sourceCopiesWireKet_normalized ρ n) P hP
    (commonCarrier_rank_le (sourceKet ρ) (sourceKet_normalized ρ) ht.le n)
    (physicalPackingChart (sourceKet ρ) (sourceKet_normalized ρ) t ht.le n)
    (consumedCopyProxy ρ t n) (generatedCopyProxy ρ t n)
    (consumedCopyProxy_isDensity ρ t n).1 (generatedCopyProxy_isDensity ρ t n).1 hs₁ hs₂ hmass
  rw [codeSourceDensity_sourceCopiesWireKet, finiteConsumedEnvelope_copy_eq] at hrec
  rw [codeSourceDensity_sourceCopiesWireKet, finiteConsumedEnvelope_copy_eq,
    finiteGeneratedEnvelope_copy_eq] at hside
  exact ⟨code, hrec, hside⟩

theorem exists_strict_physical_code_family (ρ : Density (A × (B × E)))
    (q : ℝ) (hq : QuantumProver.DepolarizingSquashedEntanglement.cmiNat (sourceMarginal ρ).matrix / 2 < q) :
    ∃ t : ℝ, 0 < t ∧
      sentRate (sentEntropyNat (sourceKet ρ)) (consumedBudgetNat (sourceKet ρ))
        (generatedBudgetNat (sourceKet ρ)) 4 t < q ∧
      ∃ codes : (n : ℕ) → CopyFiniteCode ρ t n,
        Tendsto (fun n => (codes n).recoveryError (tripleCopies ρ n)) atTop (𝓝 0) ∧
        Tendsto (fun n => (codes n).sideError (tripleCopies ρ n)) atTop (𝓝 0) ∧
        Tendsto (fun n => (codes n).communicationCost / (n : ℝ)) atTop
          (𝓝 (sentRate (sentEntropyNat (sourceKet ρ)) (consumedBudgetNat (sourceKet ρ))
            (generatedBudgetNat (sourceKet ρ)) 4 t)) := by
  classical
  have hq' : cmiNat (sourceKet ρ) / 2 < q := by rwa [canonical_cmi_eq_physical]
  obtain ⟨t, ht, hrate, hr, hs, hG⟩ :=
    exists_strict_physical_envelopes (sourceKet ρ) (sourceKet_normalized ρ) q hq'
  have hsource := sourcePurifier_nonempty ρ
  have : Nonempty B := hsource.map (fun x => x.2.1)
  have : Nonempty E := hsource.map (fun x => x.2.2)
  let good := fun n (code : CopyFiniteCode ρ t n) =>
    code.recoveryError (tripleCopies ρ n) ≤ recoveryEnvelope (sourceKet ρ) (sourceKet_normalized ρ) t n ∧
      code.sideError (tripleCopies ρ n) ≤ sideEnvelope (sourceKet ρ) (sourceKet_normalized ρ) t n
  let fallback := fun n => @fallbackFiniteCode (CopyIndex B n) (CopyIndex E n)
    (InputRegister ρ t n) (OutputRegister ρ t n) (MessageRegister ρ t n)
    inferInstance inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance inferInstance inferInstance
    (copyIndex_nonempty B n) (copyIndex_nonempty E n) inferInstance inferInstance
  let codes : (n : ℕ) → CopyFiniteCode ρ t n := fun n =>
    if hex : ∃ code : CopyFiniteCode ρ t n, good n code then Classical.choose hex else fallback n
  have hg : ∀ᶠ n : ℕ in atTop, good n (codes n) := by
    filter_upwards [exists_eventual_copy_codes ρ ht] with n hn
    change ∃ code : CopyFiniteCode ρ t n, good n code at hn
    dsimp only [codes]
    rw [dite_eq_left hn]
    exact Classical.choose_spec hn
  have hrec0 : ∀ n : ℕ, 0 ≤ (codes n).recoveryError (tripleCopies ρ n) := by
    intro n
    change 0 ≤ traceNorm (((codes n).recovered (tripleCopies ρ n)).matrix - (tripleCopies ρ n).matrix) / 2
    exact div_nonneg (EffectPerturbation.traceNorm_nonneg _) (by norm_num)
  have hside0 : ∀ n : ℕ, 0 ≤ (codes n).sideError (tripleCopies ρ n) := by
    intro n
    change 0 ≤ traceNorm (((codes n).retained (tripleCopies ρ n)).matrix -
      (FiniteCode.reference (F := OutputRegister ρ t n) (tripleCopies ρ n)).matrix) / 2
    exact div_nonneg (EffectPerturbation.traceNorm_nonneg _) (by norm_num)
  refine ⟨t, ht, hrate, codes, ?_, ?_, ?_⟩
  · exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hr
      (Eventually.of_forall hrec0) (hg.mono (fun n hn => hn.1))
  · exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hs
      (Eventually.of_forall hside0) (hg.mono (fun n hn => hn.2))
  · simpa only [FiniteCode.communicationCost, Fintype.card_fin] using hG

def represented_physicalDensity (ψ : PhysicalIndex A B E C → ℂ) (hψ : normSq ψ = 1) :
    Density (A × (B × E)) :=
  densityReindex (sourceEquiv A B E).symm
    ⟨reducedABE ψ, (reducedABE_isDensity ψ hψ).1, (reducedABE_isDensity ψ hψ).2⟩

theorem sourceMarginal_physicalDensity (ψ : PhysicalIndex A B E C → ℂ)
    (hψ : normSq ψ = 1) : (sourceMarginal (represented_physicalDensity ψ hψ)).matrix = reducedABE ψ := by
  ext ⟨⟨a,b⟩,e⟩ ⟨⟨a',b'⟩,e'⟩
  rfl

theorem exists_strict_physical_pure_code_family (ψ : PhysicalIndex A B E C → ℂ)
    (hψ : normSq ψ = 1) (q : ℝ) (hq : cmiNat ψ / 2 < q) :
    ∃ t : ℝ, 0 < t ∧
      sentRate (sentEntropyNat (sourceKet (represented_physicalDensity ψ hψ)))
        (consumedBudgetNat (sourceKet (represented_physicalDensity ψ hψ)))
        (generatedBudgetNat (sourceKet (represented_physicalDensity ψ hψ))) 4 t < q ∧
      ∃ codes : (n : ℕ) → CopyFiniteCode (represented_physicalDensity ψ hψ) t n,
        Tendsto (fun n => (codes n).recoveryError (tripleCopies (represented_physicalDensity ψ hψ) n)) atTop (𝓝 0) ∧
        Tendsto (fun n => (codes n).sideError (tripleCopies (represented_physicalDensity ψ hψ) n)) atTop (𝓝 0) ∧
        Tendsto (fun n => (codes n).communicationCost / (n : ℝ)) atTop
          (𝓝 (sentRate (sentEntropyNat (sourceKet (represented_physicalDensity ψ hψ)))
            (consumedBudgetNat (sourceKet (represented_physicalDensity ψ hψ)))
            (generatedBudgetNat (sourceKet (represented_physicalDensity ψ hψ))) 4 t)) := by
  apply exists_strict_physical_code_family (represented_physicalDensity ψ hψ) q
  rwa [sourceMarginal_physicalDensity, ← cmiNat_eq_physical]

end PhysicalFamily

end QuantumProver.QuantumRedistributionAchievability

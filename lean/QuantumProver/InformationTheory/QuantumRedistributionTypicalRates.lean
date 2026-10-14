import QuantumProver.InformationTheory.ConditionalTypicalSmoothing
import QuantumProver.InformationTheory.QuantumRedistributionDimensions
import QuantumProver.InformationTheory.QuantumRedistributionEntropy
import QuantumProver.InformationTheory.QuantumRedistributionSources

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 5000

noncomputable section

namespace QuantumProver.QuantumRedistributionTypicalRates

open Matrix Filter
open QuantumProver.QuantumEntropy
open QuantumProver.SuperchannelDiscrimination
open PetzSmoothing
open QuantumProver.ConditionalTypicalSmoothing QuantumProver.QuantumTypicalProjectors
open QuantumProver.QuantumRedistributionDimensions
open scoped Topology BigOperators ComplexOrder MatrixOrder Matrix Kronecker

variable {X Y Z : Type*} [Fintype X] [DecidableEq X]
  [Fintype Y] [DecidableEq Y] [Fintype Z] [DecidableEq Z]

def conditionalNats (R : Matrix (X × Y) (X × Y) ℂ) : ℝ :=
  entropyNats R - entropyNats (partialTrace_left R)

def senderNats (R : Matrix (X × Y) (X × Y) ℂ) : ℝ :=
  entropyNats (partialTrace_right R)

def clippedCost (d k : ℕ) (u : ℝ) : ℝ :=
  if k = 1 then 0 else (k : ℝ) ^ 2 * u / (d : ℝ)

theorem clippedCost_singleton (d : ℕ) (u : ℝ) : clippedCost d 1 u = 0 := by
  simp [clippedCost]

theorem clippedCost_nonneg (d k : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    0 ≤ clippedCost d k u := by
  unfold clippedCost
  split_ifs
  · exact le_rfl
  · positivity

theorem clippedCost_eq_Haar_cost {d k j : ℕ} {u : ℝ}
    (hj : 0 < j) (hd : d = j * k) (hk : k ≠ 1) :
    clippedCost d k u = (d : ℝ) * u / (j : ℝ) ^ 2 := by
  have hj0 : (j : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hj
  by_cases hk0 : k = 0
  · subst k
    simp only [mul_zero] at hd
    subst d
    simp [clippedCost]
  · have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk0
    rw [clippedCost, if_neg hk, hd, Nat.cast_mul]
    field_simp
    <;> ring

theorem clippedCost_four_le_exp {s h t u : ℝ}
    (hs : 0 ≤ s) (ht : 0 ≤ t) (hu0 : 0 ≤ u) (n : ℕ)
    (hu : u ≤ Real.exp (-(n : ℝ) * (h - 3 * t))) :
    clippedCost (totalDimension s t n) (retainedDimension (s + h) 4 t n) u ≤
      Real.exp (-(6 : ℝ) * (n : ℝ) * t) := by
  by_cases hk : retainedDimension (s + h) 4 t n = 1
  · rw [clippedCost, if_pos hk]
    exact Real.exp_nonneg _
  · have hkpos : 0 < (retainedDimension (s + h) 4 t n : ℝ) := by
      exact_mod_cast retainedDimension_pos (s + h) 4 t n
    have hdpos : 0 < (totalDimension s t n : ℝ) := by
      exact_mod_cast totalDimension_pos s t n
    have hlogk : Real.log (retainedDimension (s + h) 4 t n : ℝ) ≤
        (n : ℝ) * ((s + h) / 2 - 4 * t) := by
      rcases retainedDimension_singleton_or_threshold (s + h) 4 t n with he | he
      · exact False.elim (hk he)
      · exact he.2
    have hkbound : (retainedDimension (s + h) 4 t n : ℝ) ≤
        Real.exp ((n : ℝ) * ((s + h) / 2 - 4 * t)) := by
      have he := Real.exp_le_exp.mpr hlogk
      rwa [Real.exp_log hkpos] at he
    have hk2 : (retainedDimension (s + h) 4 t n : ℝ) ^ 2 ≤
        Real.exp ((n : ℝ) * (s + h - 8 * t)) := by
      calc
        _ ≤ Real.exp ((n : ℝ) * ((s + h) / 2 - 4 * t)) *
            Real.exp ((n : ℝ) * ((s + h) / 2 - 4 * t)) := by
          rw [pow_two]
          exact mul_le_mul hkbound hkbound (Nat.cast_nonneg _) (Real.exp_nonneg _)
        _ = _ := by rw [← Real.exp_add]; congr 1; ring
    have hdbound : Real.exp ((n : ℝ) * (s + t)) ≤ (totalDimension s t n : ℝ) := by
      have he := Real.exp_le_exp.mpr (log_totalDimension_bounds hs ht n).1
      rwa [Real.exp_log hdpos] at he
    rw [clippedCost, if_neg hk]
    apply (div_le_iff₀ hdpos).mpr
    calc
      _ ≤ Real.exp ((n : ℝ) * (s + h - 8 * t)) *
          Real.exp (-(n : ℝ) * (h - 3 * t)) :=
        mul_le_mul hk2 hu hu0 (Real.exp_nonneg _)
      _ = Real.exp (-(6 : ℝ) * (n : ℝ) * t) *
          Real.exp ((n : ℝ) * (s + t)) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hdbound (Real.exp_nonneg _)

theorem six_margin_tendsto_zero {t : ℝ} (ht : 0 < t) :
    Tendsto (fun n : ℕ => Real.exp (-(6 : ℝ) * (n : ℝ) * t)) atTop (𝓝 0) := by
  have hn := (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)
  have hm := Filter.Tendsto.atTop_mul_const_of_neg
    (show -(6 : ℝ) * t < 0 by nlinarith) hn
  convert Real.tendsto_exp_atBot.comp hm using 1
  ext n
  simp only [Function.comp_apply]
  congr 1
  ring

theorem density_entropyNats_nonneg {J : Type*} [Fintype J] [DecidableEq J]
    {R : Matrix J J ℂ} (hR : IsDensity R) : 0 ≤ entropyNats R := by
  have h := (QuantumProver.ConditionalEntropy.ConditionalRange.entropyBits_bounds hR).1
  rw [entropyNats_eq_entropyBits_mul_log_two]
  exact mul_nonneg h (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le

def proxyRankPurity {R : Matrix (X × Y) (X × Y) ℂ}
    (hR : IsDensity R) (t : ℝ) (n : ℕ) : ℝ :=
  (Matrix.rank (partialTrace_left (iidProxy hR t n)) : ℝ) *
    (iidProxy hR t n * iidProxy hR t n).trace.re

def iidPackedCost {R : Matrix (X × Y) (X × Y) ℂ}
    (hR : IsDensity R) (t : ℝ) (n : ℕ) : ℝ :=
  clippedCost (totalDimension (senderNats R) t n)
    (retainedDimension (senderNats R + conditionalNats R) 4 t n)
    (proxyRankPurity hR t n)

theorem proxyRankPurity_nonneg {R : Matrix (X × Y) (X × Y) ℂ}
    (hR : IsDensity R) (t : ℝ) (n : ℕ) : 0 ≤ proxyRankPurity hR t n := by
  have hp := FlaggedStates.trace_mul_re_nonneg
    (iidProxy_isDensity hR t n).1 (iidProxy_isDensity hR t n).1
  exact mul_nonneg (Nat.cast_nonneg _) hp

theorem iidPackedCost_nonneg {R : Matrix (X × Y) (X × Y) ℂ}
    (hR : IsDensity R) (t : ℝ) (n : ℕ) : 0 ≤ iidPackedCost hR t n :=
  clippedCost_nonneg _ _ (proxyRankPurity_nonneg hR t n)

theorem iidPackedCost_eventual_le {R : Matrix (X × Y) (X × Y) ℂ}
    (hR : IsDensity R) {t : ℝ} (ht : 0 < t) :
    ∀ᶠ n : ℕ in atTop, iidPackedCost hR t n ≤
      Real.exp (-(6 : ℝ) * (n : ℝ) * t) := by
  filter_upwards [iidProxy_eventual_rank_purity hR ht] with n hn
  exact clippedCost_four_le_exp
    (density_entropyNats_nonneg (partialTraceRight_isDensity hR)) ht.le
    (proxyRankPurity_nonneg hR t n) n hn

theorem iidPackedCost_tendsto_zero {R : Matrix (X × Y) (X × Y) ℂ}
    (hR : IsDensity R) {t : ℝ} (ht : 0 < t) :
    Tendsto (iidPackedCost hR t) atTop (𝓝 0) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (six_margin_tendsto_zero ht) (Eventually.of_forall (iidPackedCost_nonneg hR t))
    (iidPackedCost_eventual_le hR ht)

theorem senderTypical_rank_le_packedDimension {R : Matrix (X × Y) (X × Y) ℂ}
    (hR : IsDensity R) {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    Matrix.rank (senderTypical hR t n) ≤ totalDimension (senderNats R) t n :=
  rank_le_totalDimension (density_entropyNats_nonneg (partialTraceRight_isDensity hR))
    ht n _ (typicalProjector_rank_le_exp (partialTraceRight_isDensity hR) t n)

theorem common_sender_two_proxy_limits
    {R : Matrix (X × Y) (X × Y) ℂ} {S : Matrix (X × Z) (X × Z) ℂ}
    (hR : IsDensity R) (hS : IsDensity S)
    (hcommon : partialTrace_right R = partialTrace_right S) {t : ℝ} (ht : 0 < t) :
    (∀ n, senderTypical hR t n = senderTypical hS t n) ∧
    (∀ n, IsDensity (iidProxy hR t n) ∧ IsDensity (iidProxy hS t n)) ∧
    Tendsto (fun n => traceNorm (groupedPower R n - iidProxy hR t n)) atTop (𝓝 0) ∧
    Tendsto (fun n => traceNorm (groupedPower S n - iidProxy hS t n)) atTop (𝓝 0) ∧
    Tendsto (iidPackedCost hR t) atTop (𝓝 0) ∧
    Tendsto (iidPackedCost hS t) atTop (𝓝 0) := by
  exact ⟨fun n => senderTypical_eq_of_common_marginal hR hS hcommon t n,
    fun n => ⟨iidProxy_isDensity hR t n, iidProxy_isDensity hS t n⟩,
    iidProxy_error_tendsto_zero hR ht, iidProxy_error_tendsto_zero hS ht,
    iidPackedCost_tendsto_zero hR ht, iidPackedCost_tendsto_zero hS ht⟩

open QuantumProver.QuantumRedistributionEntropy QuantumProver.QuantumRedistributionSources

variable {A B E C : Type*} [Fintype A] [DecidableEq A]
  [Fintype B] [DecidableEq B] [Fintype E] [DecidableEq E]
  [Fintype C] [DecidableEq C]

theorem sourceBAC_senderNats (ψ : PhysicalIndex A B E C → ℂ) :
    senderNats (sourceBAC ψ) = sentEntropyNat ψ := by
  rw [senderNats, sourceBAC_sender]
  rfl

theorem sourceBAE_senderNats (ψ : PhysicalIndex A B E C → ℂ) :
    senderNats (sourceBAE ψ) = sentEntropyNat ψ := by
  rw [senderNats, sourceBAE_sender]
  rfl

theorem sourceBAC_conditionalNats (ψ : PhysicalIndex A B E C → ℂ) :
    conditionalNats (sourceBAC ψ) = conditionalBACNat ψ :=
  sourceBAC_conditional_nats ψ

theorem sourceBAE_conditionalNats (ψ : PhysicalIndex A B E C → ℂ) :
    conditionalNats (sourceBAE ψ) = conditionalBAENat ψ :=
  sourceBAE_conditional_nats ψ

def consumedProxy (ψ : PhysicalIndex A B E C → ℂ) (hψ : normSq ψ = 1)
    (t : ℝ) (n : ℕ) := iidProxy (sourceBAC_isDensity ψ hψ) t n

def generatedProxy (ψ : PhysicalIndex A B E C → ℂ) (hψ : normSq ψ = 1)
    (t : ℝ) (n : ℕ) := iidProxy (sourceBAE_isDensity ψ hψ) t n

def commonCarrier (ψ : PhysicalIndex A B E C → ℂ) (hψ : normSq ψ = 1)
    (t : ℝ) (n : ℕ) := senderTypical (sourceBAC_isDensity ψ hψ) t n

def consumedCost (ψ : PhysicalIndex A B E C → ℂ) (hψ : normSq ψ = 1)
    (t : ℝ) (n : ℕ) : ℝ :=
  clippedCost (totalDimension (sentEntropyNat ψ) t n)
    (retainedDimension (consumedBudgetNat ψ) 4 t n)
    (proxyRankPurity (sourceBAC_isDensity ψ hψ) t n)

def generatedCost (ψ : PhysicalIndex A B E C → ℂ) (hψ : normSq ψ = 1)
    (t : ℝ) (n : ℕ) : ℝ :=
  clippedCost (totalDimension (sentEntropyNat ψ) t n)
    (retainedDimension (generatedBudgetNat ψ) 4 t n)
    (proxyRankPurity (sourceBAE_isDensity ψ hψ) t n)

theorem consumedCost_eq_iidPackedCost (ψ : PhysicalIndex A B E C → ℂ)
    (hψ : normSq ψ = 1) (t : ℝ) (n : ℕ) :
    consumedCost ψ hψ t n = iidPackedCost (sourceBAC_isDensity ψ hψ) t n := by
  unfold consumedCost iidPackedCost
  rw [sourceBAC_senderNats, sourceBAC_conditionalNats]
  rfl

theorem generatedCost_eq_iidPackedCost (ψ : PhysicalIndex A B E C → ℂ)
    (hψ : normSq ψ = 1) (t : ℝ) (n : ℕ) :
    generatedCost ψ hψ t n = iidPackedCost (sourceBAE_isDensity ψ hψ) t n := by
  unfold generatedCost iidPackedCost
  rw [sourceBAE_senderNats, sourceBAE_conditionalNats]
  rfl

theorem consumedCost_tendsto_zero (ψ : PhysicalIndex A B E C → ℂ)
    (hψ : normSq ψ = 1) {t : ℝ} (ht : 0 < t) :
    Tendsto (consumedCost ψ hψ t) atTop (𝓝 0) := by
  have he : consumedCost ψ hψ t = iidPackedCost (sourceBAC_isDensity ψ hψ) t :=
    funext (consumedCost_eq_iidPackedCost ψ hψ t)
  rw [he]
  exact iidPackedCost_tendsto_zero _ ht

theorem generatedCost_tendsto_zero (ψ : PhysicalIndex A B E C → ℂ)
    (hψ : normSq ψ = 1) {t : ℝ} (ht : 0 < t) :
    Tendsto (generatedCost ψ hψ t) atTop (𝓝 0) := by
  have he : generatedCost ψ hψ t = iidPackedCost (sourceBAE_isDensity ψ hψ) t :=
    funext (generatedCost_eq_iidPackedCost ψ hψ t)
  rw [he]
  exact iidPackedCost_tendsto_zero _ ht

theorem commonCarrier_eq_generated (ψ : PhysicalIndex A B E C → ℂ)
    (hψ : normSq ψ = 1) (t : ℝ) (n : ℕ) :
    commonCarrier ψ hψ t n = senderTypical (sourceBAE_isDensity ψ hψ) t n :=
  senderTypical_eq_of_common_marginal _ _ (source_sender_eq ψ) t n

theorem commonCarrier_rank_le (ψ : PhysicalIndex A B E C → ℂ)
    (hψ : normSq ψ = 1) {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    Matrix.rank (commonCarrier ψ hψ t n) ≤ totalDimension (sentEntropyNat ψ) t n := by
  simpa only [commonCarrier, sourceBAC_senderNats] using
    senderTypical_rank_le_packedDimension (sourceBAC_isDensity ψ hψ) ht n

theorem commonCarrier_support_eventually (ψ : PhysicalIndex A B E C → ℂ)
    (hψ : normSq ψ = 1) {t : ℝ} (ht : 0 < t) :
    ∀ᶠ n : ℕ in atTop,
      (commonCarrier ψ hψ t n ⊗ₖ
        (1 : Matrix (TensorEntropy.TensorIndex (A × C) n) (TensorEntropy.TensorIndex (A × C) n) ℂ)) *
        consumedProxy ψ hψ t n = consumedProxy ψ hψ t n ∧
      (commonCarrier ψ hψ t n ⊗ₖ
        (1 : Matrix (TensorEntropy.TensorIndex (A × E) n) (TensorEntropy.TensorIndex (A × E) n) ℂ)) *
        generatedProxy ψ hψ t n = generatedProxy ψ hψ t n := by
  filter_upwards [(conditional_typical_iid_smoothing (sourceBAC_isDensity ψ hψ) t ht).2.2.2,
    (conditional_typical_iid_smoothing (sourceBAE_isDensity ψ hψ) t ht).2.2.2] with n hAC hAE
  refine ⟨hAC.1, ?_⟩
  rw [commonCarrier_eq_generated]
  exact hAE.1

theorem actual_retained_singleton_or_threshold (ψ : PhysicalIndex A B E C → ℂ)
    (t : ℝ) (n : ℕ) :
    (retainedDimension (consumedBudgetNat ψ) 4 t n = 1 ∨
      (0 < consumedBudgetNat ψ / 2 - 4 * t ∧
        Real.log (retainedDimension (consumedBudgetNat ψ) 4 t n : ℝ) ≤
          (n : ℝ) * (consumedBudgetNat ψ / 2 - 4 * t))) ∧
    (retainedDimension (generatedBudgetNat ψ) 4 t n = 1 ∨
      (0 < generatedBudgetNat ψ / 2 - 4 * t ∧
        Real.log (retainedDimension (generatedBudgetNat ψ) 4 t n : ℝ) ≤
          (n : ℝ) * (generatedBudgetNat ψ / 2 - 4 * t))) :=
  ⟨retainedDimension_singleton_or_threshold _ _ _ _,
    retainedDimension_singleton_or_threshold _ _ _ _⟩

theorem exists_strict_pure_typical_data (ψ : PhysicalIndex A B E C → ℂ)
    (hψ : normSq ψ = 1) (q : ℝ) (hq : cmiNat ψ / 2 < q) :
    ∃ t : ℝ, 0 < t ∧
      sentRate (sentEntropyNat ψ) (consumedBudgetNat ψ) (generatedBudgetNat ψ) 4 t < q ∧
      Tendsto (fun n : ℕ => Real.log
        (sentDimension (sentEntropyNat ψ) (consumedBudgetNat ψ) (generatedBudgetNat ψ) 4 t n : ℝ) /
          (n : ℝ)) atTop
        (𝓝 (sentRate (sentEntropyNat ψ) (consumedBudgetNat ψ) (generatedBudgetNat ψ) 4 t)) ∧
      (∀ n, totalDimension (sentEntropyNat ψ) t n =
        retainedDimension (consumedBudgetNat ψ) 4 t n *
          retainedDimension (generatedBudgetNat ψ) 4 t n *
            sentDimension (sentEntropyNat ψ) (consumedBudgetNat ψ) (generatedBudgetNat ψ) 4 t n) ∧
      (∀ n, IsDensity (consumedProxy ψ hψ t n) ∧ IsDensity (generatedProxy ψ hψ t n)) ∧
      (∀ n, Matrix.rank (commonCarrier ψ hψ t n) ≤ totalDimension (sentEntropyNat ψ) t n) ∧
      Tendsto (fun n => traceNorm (groupedPower (sourceBAC ψ) n - consumedProxy ψ hψ t n))
        atTop (𝓝 0) ∧
      Tendsto (fun n => traceNorm (groupedPower (sourceBAE ψ) n - generatedProxy ψ hψ t n))
        atTop (𝓝 0) ∧
      Tendsto (consumedCost ψ hψ t) atTop (𝓝 0) ∧
      Tendsto (generatedCost ψ hψ t) atTop (𝓝 0) ∧
      (∀ᶠ n : ℕ in atTop,
        (commonCarrier ψ hψ t n ⊗ₖ
          (1 : Matrix (TensorEntropy.TensorIndex (A × C) n) (TensorEntropy.TensorIndex (A × C) n) ℂ)) *
          consumedProxy ψ hψ t n = consumedProxy ψ hψ t n ∧
        (commonCarrier ψ hψ t n ⊗ₖ
          (1 : Matrix (TensorEntropy.TensorIndex (A × E) n) (TensorEntropy.TensorIndex (A × E) n) ℂ)) *
          generatedProxy ψ hψ t n = generatedProxy ψ hψ t n) := by
  have hq' : sentEntropyNat ψ - (consumedBudgetNat ψ + generatedBudgetNat ψ) / 2 < q := by
    rw [half_cmi_eq_residual_entropy ψ]
    exact hq
  obtain ⟨t, ht, hrate⟩ := exists_strict_margin (by norm_num : 0 ≤ (4 : ℝ)) hq'
  obtain ⟨hs, ha, hb, hab⟩ := scalar_packing_hypotheses ψ hψ
  exact ⟨t, ht, hrate,
    tendsto_log_sentDimension_rate hs ha hb hab (by norm_num) ht.le,
    fun n => totalDimension_eq_product hs ha hb hab (by norm_num) ht.le n,
    fun n => ⟨iidProxy_isDensity _ _ _, iidProxy_isDensity _ _ _⟩,
    commonCarrier_rank_le ψ hψ ht.le,
    iidProxy_error_tendsto_zero _ ht, iidProxy_error_tendsto_zero _ ht,
    consumedCost_tendsto_zero ψ hψ ht, generatedCost_tendsto_zero ψ hψ ht,
    commonCarrier_support_eventually ψ hψ ht⟩

end QuantumProver.QuantumRedistributionTypicalRates

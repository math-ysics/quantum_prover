import QuantumProver.InformationTheory.SuperchannelDiscrimination.ChannelUniformFactory
import QuantumProver.InformationTheory.SuperchannelDiscrimination.ParallelPowerJoins
import QuantumProver.InformationTheory.SuperchannelDiscrimination.FlaggedTesting
import QuantumProver.InformationTheory.SuperchannelDiscrimination.ChannelEntropyChain
import QuantumProver.InformationTheory.SuperchannelDiscrimination.ChannelAmortization
import QuantumProver.InformationTheory.SuperchannelDiscrimination.SuperchannelReferenceTransport
import QuantumProver.InformationTheory.SuperchannelDiscrimination.ParallelAvailability

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option maxRecDepth 4000

noncomputable section
open Matrix Filter
open scoped BigOperators Topology ComplexOrder MatrixOrder Matrix Kronecker

namespace QuantumProver.SuperchannelDiscrimination.SuperchannelEntropyChain

open FlaggedStates TensorEntropy ChannelRegularization KrausCompletion CPWrappers
open MatrixStrategyAssembly.MatrixStrategies

theorem le_orderedSteinExponent_of_eventual_dyadic_tests {S : StrategyFamily}
    (T : ℕ → BinaryTest) (hmem : ∀ n, T n ∈ S n)
    (halpha : Tendsto (fun n => (T n).alpha) atTop (𝓝 0)) {r : ℝ}
    (hbeta : ∀ᶠ n : ℕ in atTop, (T n).beta ≤ (2 : ℝ) ^ (-(n : ℝ) * r)) :
    (r : EReal) ≤ orderedSteinExponent S := by
  apply le_orderedSteinExponent_of_eventual_tests
  intro epsilon hepsilon
  have ha := halpha.eventually (eventually_lt_nhds hepsilon.1)
  obtain ⟨N, hN⟩ := eventually_atTop.1 (ha.and hbeta)
  filter_upwards [eventually_ge_atTop N] with k hk
  obtain ⟨ha, hb⟩ := hN (k + 1) (by omega)
  refine ⟨T (k + 1), ⟨hmem _, ha.le⟩, ?_⟩
  have hexp : (T (k + 1)).beta ≤ Real.exp (-((k + 1 : ℕ) : ℝ) * (r * Real.log 2)) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)] at hb
    convert hb using 1 <;> congr 1 <;> ring
  simpa only [mul_div_cancel_right₀ r (ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 2)))] using
    QuantumSteinAchievability.testPositiveBlockRate_ge_of_beta_exp k hexp

theorem test_alpha_tendsto_of_perturbations (T U : ℕ → BinaryTest) (delta eta : ℕ → ℝ)
    (hU : Tendsto (fun n => (U n).alpha) atTop (𝓝 0))
    (hd : Tendsto delta atTop (𝓝 0)) (he : Tendsto eta atTop (𝓝 0))
    (hbound : ∀ᶠ n : ℕ in atTop, (T n).alpha ≤ (U n).alpha + delta n + eta n) :
    Tendsto (fun n => (T n).alpha) atTop (𝓝 0) := by
  exact squeeze_zero' (Eventually.of_forall fun n => (T n).alpha_nonneg) hbound
    (by simpa using (hU.add hd).add he)

theorem rate_transfer_of_unconditional_tests {S : StrategyFamily}
    (T : ℕ → BinaryTest) (hmem : ∀ n, T n ∈ S n)
    (halpha : Tendsto (fun n => (T n).alpha) atTop (𝓝 0)) {a b r : ℝ}
    (hbeta : ∀ᶠ n : ℕ in atTop, (T n).beta ≤ (2 : ℝ) ^ ((n : ℝ) * (a + b - r))) :
    ((r - a - b : ℝ) : EReal) ≤ orderedSteinExponent S := by
  apply le_orderedSteinExponent_of_eventual_dyadic_tests T hmem halpha
  filter_upwards [hbeta] with n hn
  convert hn using 1 <;> congr 1 <;> ring

theorem extended_chain_bound_of_strict_rates {D B : EReal} (c : ℝ)
    (h : ∀ r : ℝ, (r : EReal) < D → ((r - c : ℝ) : EReal) ≤ B) :
    D ≤ B + (c : EReal) := by
  by_contra hbad
  obtain ⟨r, hBr, hrD⟩ := EReal.lt_iff_exists_real_btwn.mp (lt_of_not_ge hbad)
  have hback := add_le_add_right (h r hrD) (c : EReal)
  rw [← EReal.coe_add, show c + (r - c) = r by ring] at hback
  have hback' : (r : EReal) ≤ B + (c : EReal) := by simpa only [add_comm] using hback
  exact (not_le_of_gt hBr hback').elim

theorem extended_chain_bound_of_strict_margins {D B : EReal} (d s : ℝ)
    (h : ∀ a b : ℝ, d < a → s < b → D ≤ B + ((a + b : ℝ) : EReal)) :
    D ≤ B + ((d + s : ℝ) : EReal) := by
  induction B using EReal.rec with
  | bot => simpa using h (d + 1) (s + 1) (by linarith) (by linarith)
  | top => simp
  | coe B =>
    by_contra hbad
    obtain ⟨r, hr0, hrD⟩ := EReal.lt_iff_exists_real_btwn.mp (lt_of_not_ge hbad)
    have hr : B + (d + s) < r := by exact_mod_cast hr0
    let e := (r - B - d - s) / 4
    have he : 0 < e := by dsimp [e]; linarith
    have hbound := h (d + e) (s + e) (by linarith) (by linarith)
    have hsmall : (B : EReal) + (((d + e) + (s + e) : ℝ) : EReal) < (r : EReal) := by
      rw [← EReal.coe_add]
      apply EReal.coe_lt_coe_iff.mpr
      dsimp [e]
      linarith
    exact (not_lt_of_ge hbound (hsmall.trans hrD)).elim

section BasisTransport

variable {I O J P R : Type*} [Fintype I] [Fintype O] [Fintype J] [Fintype P] [Fintype R]
  [DecidableEq I] [DecidableEq O] [DecidableEq J] [DecidableEq P] [DecidableEq R]

def reindexSlot (eI : I ≃ J) (eO : O ≃ P)
    (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) : Matrix J J ℂ →ₗ[ℂ] Matrix P P ℂ :=
  (reindexMap eO).comp (Φ.comp (reindexMap eI.symm))

theorem reindexSlot_apply_reindex (eI : I ≃ J) (eO : O ≃ P)
    (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) (A : Matrix I I ℂ) :
    reindexSlot eI eO Φ (reindexMap eI A) = reindexMap eO (Φ A) := by
  change reindexMap eO (Φ (reindexMap eI.symm (reindexMap eI A))) = _
  rw [MatrixParallelPowerJoins.reindexMap_cancel_matrix]

theorem reindexSlot_completelyPositive (eI : I ≃ J) (eO : O ≃ P)
    {Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ} (hΦ : CPTPKraus.CompletelyPositive Φ) :
    CPTPKraus.CompletelyPositive (reindexSlot eI eO Φ) :=
  completelyPositive_comp (completelyPositive_reindexMap eO)
    (completelyPositive_comp hΦ (completelyPositive_reindexMap eI.symm))

theorem reindexSlot_traceNonincreasing (eI : I ≃ J) (eO : O ≃ P)
    {Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ} (hΦ : CPTPKraus.TraceNonincreasing Φ) :
    CPTPKraus.TraceNonincreasing (reindexSlot eI eO Φ) := by
  intro A hA
  change (reindexMap eO (Φ (reindexMap eI.symm A))).trace ≤ A.trace
  rw [reindexMap_tracePreserving]
  exact (hΦ _ (completelyPositive_positive (completelyPositive_reindexMap eI.symm) hA)).trans_eq
    (reindexMap_tracePreserving eI.symm A)

theorem reindexSlot_cpDom (eI : I ≃ J) (eO : O ≃ P)
    {Φ Ψ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ} {c : ℝ} (h : CPTPKraus.CPDom Φ Ψ c) :
    CPTPKraus.CPDom (reindexSlot eI eO Φ) (reindexSlot eI eO Ψ) c :=
  cpDom_postcompose (cpDom_precompose h (completelyPositive_reindexMap eI.symm))
    (completelyPositive_reindexMap eO)

theorem reindexSlot_sub (eI : I ≃ J) (eO : O ≃ P)
    (Φ Ψ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) :
    reindexSlot eI eO (Φ - Ψ) = reindexSlot eI eO Φ - reindexSlot eI eO Ψ := by
  ext A p q
  rfl

theorem amplify_reindexSlot (eI : I ≃ J) (eO : O ≃ P)
    (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ)
    (A : Matrix (I × R) (I × R) ℂ) :
    amplifyMap (reindexSlot eI eO Φ) R
        (reindexMap (Equiv.prodCongr eI (Equiv.refl R)) A) =
      reindexMap (Equiv.prodCongr eO (Equiv.refl R)) (amplifyMap Φ R A) := by
  ext ⟨j, r⟩ ⟨k, s⟩
  change reindexSlot eI eO Φ
    (fun a b => reindexMap (Equiv.prodCongr eI (Equiv.refl R)) A (a, r) (b, s)) j k =
      Φ (fun a b => A (a, r) (b, s)) (eO.symm j) (eO.symm k)
  have hslice : (fun a b => reindexMap (Equiv.prodCongr eI (Equiv.refl R)) A (a, r) (b, s)) =
      reindexMap eI (fun a b => A (a, r) (b, s)) := rfl
  rw [hslice, reindexSlot_apply_reindex]
  rfl

theorem reindexSlot_diamondBudget_le (eI : I ≃ J) (eO : O ≃ P)
    (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) :
    DiamondControl.diamondBudget (reindexSlot eI eO Φ) ≤ DiamondControl.diamondBudget Φ := by
  rw [DiamondControl.diamondBudget_le_iff]
  intro k X hX
  let ei := Equiv.prodCongr eI (Equiv.refl (Fin k))
  let eo := Equiv.prodCongr eO (Equiv.refl (Fin k))
  let X' := reindexMap ei.symm X
  have hX' : DiamondControl.nuclearNorm X' ≤ 1 := by
    change DiamondControl.nuclearNorm (X.submatrix ei ei) ≤ 1
    rw [DiamondControl.nuclearNorm_submatrix_equiv]
    exact hX
  have houtput := amplify_reindexSlot (R := Fin k) eI eO Φ X'
  change amplifyMap (reindexSlot eI eO Φ) (Fin k) (reindexMap ei (reindexMap ei.symm X)) =
    reindexMap eo (amplifyMap Φ (Fin k) X') at houtput
  have hcancel : reindexMap ei (reindexMap ei.symm X) = X := by
    simpa only [Equiv.symm_symm] using MatrixParallelPowerJoins.reindexMap_cancel_matrix ei.symm X
  rw [hcancel] at houtput
  change (DiamondControl.nuclearNorm (amplifyMap (reindexSlot eI eO Φ) (Fin k) X) : EReal) ≤ _
  rw [houtput]
  change (DiamondControl.nuclearNorm ((amplifyMap Φ (Fin k) X').submatrix eo.symm eo.symm) : EReal) ≤ _
  rw [DiamondControl.nuclearNorm_submatrix_equiv]
  exact DiamondControl.unitBall_output_le_diamondBudget Φ k hX'

theorem reindex_traceNorm_difference (e : I ≃ J) (A B : Matrix I I ℂ) :
    EffectPerturbation.traceNorm (reindexMap e A - reindexMap e B) =
      EffectPerturbation.traceNorm (A - B) := by
  rw [← map_sub]
  change DiamondControl.nuclearNorm ((A - B).submatrix e.symm e.symm) = DiamondControl.nuclearNorm (A - B)
  exact DiamondControl.nuclearNorm_submatrix_equiv _ _

theorem reindex_state_order (e : I ≃ J) {A B : Matrix I I ℂ} {c : ℝ}
    (h : ((c : ℂ) • B - A).PosSemidef) :
    ((c : ℂ) • reindexMap e B - reindexMap e A).PosSemidef := h.submatrix e.symm

end BasisTransport

section MatrixFamilies

open MatrixParallelPowerJoins

variable {I O C D R₁ R₂ X Y : FiniteSystem}

theorem reindexSlot_groupedSidePower
    (Φ : FiniteCPTP (I.prod X).basis (O.prod Y).basis) (n : ℕ) :
    reindexSlot (repeatedPortsIndex I X n) (repeatedPortsIndex O Y n)
      (channelPower Φ n).map = (groupedSidePower Φ n).map := by
  apply LinearMap.ext
  intro A
  have h := MatrixFlaggedTesting.groupedSidePower_slot_intertwine Φ n
    (reindexMap (repeatedPortsIndex I X n).symm A)
  have hc : reindexMap (repeatedPortsIndex I X n)
      (reindexMap (repeatedPortsIndex I X n).symm A) = A := by
    simpa only [Equiv.symm_symm] using
      reindexMap_cancel_matrix (repeatedPortsIndex I X n).symm A
  rw [hc] at h
  exact h.symm

theorem exists_grouped_channel_uniform_approximation
    (Φ Ψ : FiniteCPTP (I.prod X).basis (O.prod Y).basis) {a : ℝ}
    (ha : regularizedRelativeEntropyBits Φ Ψ < (a : EReal)) :
    ∃ Λ : (n : ℕ) →
      Matrix ((I.tensorPower n).prod (X.tensorPower n)).basis
        ((I.tensorPower n).prod (X.tensorPower n)).basis ℂ →ₗ[ℂ]
      Matrix ((O.tensorPower n).prod (Y.tensorPower n)).basis
        ((O.tensorPower n).prod (Y.tensorPower n)).basis ℂ,
      ∃ errors : ℕ → ℝ, (∀ n, 0 ≤ errors n) ∧ Tendsto errors atTop (𝓝 0) ∧
        (∀ n, CPTPKraus.CompletelyPositive (Λ n) ∧ CPTPKraus.TraceNonincreasing (Λ n)) ∧
        ∀ᶠ n : ℕ in atTop,
          CPTPKraus.CPDom (Λ n) (groupedSidePower Ψ n).map ((2 : ℝ) ^ ((n : ℝ) * a)) ∧
            DiamondControl.diamondBudget ((groupedSidePower Φ n).map - Λ n) ≤
              ((errors n : ℝ) : EReal) := by
  obtain ⟨L, errors, he0, he, hL, hbound⟩ :=
    ChannelUniformFactory.exists_channel_uniform_approximation_tendsto Φ Ψ ha
  let Λ := fun n => reindexSlot (repeatedPortsIndex I X n) (repeatedPortsIndex O Y n) (L n)
  refine ⟨Λ, errors, he0, he, ?_, ?_⟩
  · intro n
    exact ⟨reindexSlot_completelyPositive _ _ (hL n).1,
      reindexSlot_traceNonincreasing _ _ (hL n).2⟩
  · filter_upwards [hbound] with n hn
    refine ⟨?_, ?_⟩
    · simpa only [reindexSlot_groupedSidePower] using
        reindexSlot_cpDom (repeatedPortsIndex I X n) (repeatedPortsIndex O Y n) hn.1
    · have h := (reindexSlot_diamondBudget_le
        (repeatedPortsIndex I X n) (repeatedPortsIndex O Y n)
          ((channelPower Φ n).map - L n)).trans hn.2
      simpa only [reindexSlot_sub, reindexSlot_groupedSidePower] using h

theorem exists_grouped_normalized_state_smoothing
    {ρ σ : Matrix (C.prod X).basis (C.prod X).basis ℂ}
    (hρ : IsDensity ρ) (hσ : IsDensity σ) (b : ℝ)
    (hb : relativeEntropyBits ρ σ < (b : EReal)) :
    ∃ ν : (n : ℕ) → Matrix ((C.tensorPower n).prod (X.tensorPower n)).basis
      ((C.tensorPower n).prod (X.tensorPower n)).basis ℂ,
      ∃ eta : ℕ → ℝ, (∀ n, 0 ≤ eta n) ∧ Tendsto eta atTop (𝓝 0) ∧
        (∀ n, IsDensity (ν n)) ∧
        (∀ n, EffectPerturbation.traceNorm
          (ν n - reindexMap (repeatedPortsIndex C X n) (tensorPower ρ n)) ≤ eta n) ∧
        ∀ᶠ n : ℕ in atTop,
          (((Real.rpow (2 : ℝ) ((n : ℝ) * b)) : ℂ) •
            reindexMap (repeatedPortsIndex C X n) (tensorPower σ n) - ν n).PosSemidef := by
  obtain ⟨ν₀, hν₀, he, hcap⟩ :=
    ChannelEntropyChain.normalized_state_smoothing_tail hρ hσ b hb
  let ν := fun n => reindexMap (repeatedPortsIndex C X n) (ν₀ n)
  let eta := fun n => EffectPerturbation.traceNorm (tensorPower ρ n - ν₀ n)
  refine ⟨ν, eta, (fun n => DiamondControl.nuclearNorm_nonneg _), he,
    (fun n => reindex_isDensity_matrix _ (hν₀ n)), ?_, ?_⟩
  · intro n
    change EffectPerturbation.traceNorm
      (reindexMap (repeatedPortsIndex C X n) (ν₀ n) -
        reindexMap (repeatedPortsIndex C X n) (tensorPower ρ n)) ≤ _
    rw [reindex_traceNorm_difference, ChannelEntropyChain.traceNorm_sub_comm]
  · filter_upwards [hcap] with n hn
    exact hn.submatrix (repeatedPortsIndex C X n).symm

theorem exists_grouped_iid_output_effects
    (Θ₁ : FiniteSuperchannel I.basis O.basis C.basis D.basis R₁.basis)
    (Θ₂ : FiniteSuperchannel I.basis O.basis C.basis D.basis R₂.basis)
    (Φ Ψ : FiniteCPTP (I.prod X).basis (O.prod Y).basis)
    {ρ σ : Matrix (C.prod X).basis (C.prod X).basis ℂ}
    (hρ : IsDensity ρ) (hσ : IsDensity σ) {r : ℝ}
    (hr : (r : EReal) < relativeEntropyBits
      (((extendSidePorts Θ₁ X Y).applyChannel Φ).map ρ)
      (((extendSidePorts Θ₂ X Y).applyChannel Ψ).map σ)) :
    ∃ Q : (n : ℕ) → Matrix ((D.tensorPower n).prod (Y.tensorPower n)).basis
      ((D.tensorPower n).prod (Y.tensorPower n)).basis ℂ,
      (∀ n, IsEffect (Q n)) ∧
      Tendsto (fun n => 1 - acceptanceProbability
        ((parallelChannel Θ₁ n (X.tensorPower n) (Y.tensorPower n)
          (groupedSidePower Φ n)).map
          (reindexMap (repeatedPortsIndex C X n) (tensorPower ρ n))) (Q n)) atTop (𝓝 0) ∧
      ∀ n, acceptanceProbability
        ((parallelChannel Θ₂ n (X.tensorPower n) (Y.tensorPower n)
          (groupedSidePower Ψ n)).map
          (reindexMap (repeatedPortsIndex C X n) (tensorPower σ n))) (Q n) ≤
            (2 : ℝ) ^ (-(n : ℝ) * r) := by
  let τ := ((extendSidePorts Θ₁ X Y).applyChannel Φ).map ρ
  let ω := ((extendSidePorts Θ₂ X Y).applyChannel Ψ).map σ
  have hτ : IsDensity τ := channel_density _ hρ.1 hρ.2
  have hω : IsDensity ω := channel_density _ hσ.1 hσ.2
  obtain ⟨Q₀, hQ₀, hα, hβ⟩ :=
    ChannelEntropyChain.iid_bits_effect_achievability_tail τ ω hτ hω hr
  let Q := fun n => reindexMap (repeatedPortsIndex D Y n) (Q₀ n)
  have hα' (n : ℕ) : 1 - acceptanceProbability
      ((parallelChannel Θ₁ n (X.tensorPower n) (Y.tensorPower n)
        (groupedSidePower Φ n)).map
          (reindexMap (repeatedPortsIndex C X n) (tensorPower ρ n))) (Q n) =
      acceptanceProbability (tensorPower τ n) (1 - Q₀ n) := by
    rw [groupedSidePower_tensor_output]
    change 1 - acceptanceProbability
      (reindexMap (repeatedPortsIndex D Y n) (tensorPower τ n))
      (reindexMap (repeatedPortsIndex D Y n) (Q₀ n)) = _
    rw [acceptanceProbability_reindex_matrix,
      QuantumSteinAchievability.acceptanceProbability_complement (tensorPower_isDensity hτ n)]
  refine ⟨Q, (fun n => reindex_isEffect_matrix _ (hQ₀ n)), ?_, ?_⟩
  · simpa only [hα'] using hα
  · intro n
    rw [groupedSidePower_tensor_output]
    exact (acceptanceProbability_reindex_matrix
      (repeatedPortsIndex D Y n) (tensorPower ω n) (Q₀ n)).le.trans (hβ n)

theorem exists_parallel_tests_of_strict_rates
    (Θ₁ : FiniteSuperchannel I.basis O.basis C.basis D.basis R₁.basis)
    (Θ₂ : FiniteSuperchannel I.basis O.basis C.basis D.basis R₂.basis)
    (Φ Ψ : FiniteCPTP (I.prod X).basis (O.prod Y).basis)
    {ρ σ : Matrix (C.prod X).basis (C.prod X).basis ℂ}
    (hρ : IsDensity ρ) (hσ : IsDensity σ) {a b r : ℝ}
    (ha : regularizedRelativeEntropyBits Φ Ψ < (a : EReal))
    (hb : relativeEntropyBits ρ σ < (b : EReal))
    (hr : (r : EReal) < relativeEntropyBits
      (((extendSidePorts Θ₁ X Y).applyChannel Φ).map ρ)
      (((extendSidePorts Θ₂ X Y).applyChannel Ψ).map σ)) :
    ∃ T : ℕ → BinaryTest,
      (∀ n, T n ∈ parallelStrategyFamily Θ₁ Θ₂ n) ∧
      Tendsto (fun n => (T n).alpha) atTop (𝓝 0) ∧
      ∀ᶠ n : ℕ in atTop, (T n).beta ≤ (2 : ℝ) ^ ((n : ℝ) * (a + b - r)) := by
  classical
  obtain ⟨Λ, errors, he0, he, hΛ, hΛbound⟩ :=
    exists_grouped_channel_uniform_approximation Φ Ψ ha
  obtain ⟨ν, eta, heta0, heta, hν, hνerror, hνcap⟩ :=
    exists_grouped_normalized_state_smoothing hρ hσ b hb
  obtain ⟨Q, hQ, hα, hβ⟩ := exists_grouped_iid_output_effects Θ₁ Θ₂ Φ Ψ hρ hσ hr
  let o₀ : (n : ℕ) → ((O.tensorPower n).prod (Y.tensorPower n)).basis :=
    fun n => Classical.choice inferInstance
  let T := fun n => MatrixFlaggedTesting.flaggedParallelTest Θ₁ Θ₂ n
    (Λ n) (o₀ n) (hΛ n).1 (hΛ n).2 (ν n) (Q n) (hν n) (hQ n)
  refine ⟨T, (fun n => MatrixFlaggedTesting.flaggedParallelTest_mem
    Θ₁ Θ₂ n (Λ n) (o₀ n) (hΛ n).1 (hΛ n).2 (ν n) (Q n) (hν n) (hQ n)), ?_, ?_⟩
  · have hbound : ∀ᶠ n : ℕ in atTop, (T n).alpha ≤
        1 - acceptanceProbability
          ((parallelChannel Θ₁ n (X.tensorPower n) (Y.tensorPower n)
            (groupedSidePower Φ n)).map
            (reindexMap (repeatedPortsIndex C X n) (tensorPower ρ n))) (Q n) +
          errors n + (1 / 2) * eta n := by
      filter_upwards [hΛbound] with n hn
      exact MatrixFlaggedTesting.flaggedParallelTest_alpha_le
        Θ₁ Θ₂ n (Λ n) (o₀ n) (hΛ n).1 (hΛ n).2 (hν n) (hQ n)
        (groupedSidePower Φ n)
        (reindex_isDensity_matrix _ (tensorPower_isDensity hρ n)) hn.2 (hνerror n)
    exact squeeze_zero' (Eventually.of_forall fun n => (T n).alpha_nonneg) hbound
      (by simpa only [add_zero, mul_zero] using (hα.add he).add (heta.const_mul (1 / 2)))
  · filter_upwards [hΛbound, hνcap] with n hn hcap
    have hu := MatrixFlaggedTesting.flaggedParallelTest_beta_le
      (X := X.tensorPower n) (Y := Y.tensorPower n)
      (ν := ν n) (σ := reindexMap (repeatedPortsIndex C X n) (tensorPower σ n)) (Q := Q n)
      Θ₁ Θ₂ n (Λ n) (o₀ n) (hΛ n).1 (hΛ n).2 (hν n) (hQ n)
      (groupedSidePower Ψ n) hn.1
      (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) ((n : ℝ) * b))
      (reindex_isDensity_matrix _ (tensorPower_isDensity hσ n)).1 hcap
    exact ChannelEntropyChain.dyadic_cap_test_bound n a b r hu (hβ n)

theorem superchannel_output_relativeEntropy_le_real_budget
    (Θ₁ : FiniteSuperchannel I.basis O.basis C.basis D.basis R₁.basis)
    (Θ₂ : FiniteSuperchannel I.basis O.basis C.basis D.basis R₂.basis)
    (Φ Ψ : FiniteCPTP (I.prod X).basis (O.prod Y).basis)
    {ρ σ : Matrix (C.prod X).basis (C.prod X).basis ℂ}
    (hρ : IsDensity ρ) (hσ : IsDensity σ) {budget inputBudget : ℝ}
    (hReg : regularizedRelativeEntropyBits Φ Ψ ≤ (budget : EReal))
    (hInput : relativeEntropyBits ρ σ ≤ (inputBudget : EReal)) :
    relativeEntropyBits
      (((extendSidePorts Θ₁ X Y).applyChannel Φ).map ρ)
      (((extendSidePorts Θ₂ X Y).applyChannel Ψ).map σ) ≤
        orderedSteinExponent (parallelStrategyFamily Θ₁ Θ₂) +
          (((budget + inputBudget : ℝ)) : EReal) := by
  apply extended_chain_bound_of_strict_margins budget inputBudget
  intro a b ha hb
  apply extended_chain_bound_of_strict_rates (a + b)
  intro r hr
  obtain ⟨T, hmem, hα, hβ⟩ := exists_parallel_tests_of_strict_rates Θ₁ Θ₂ Φ Ψ hρ hσ
    (hReg.trans_lt (EReal.coe_lt_coe_iff.mpr ha))
    (hInput.trans_lt (EReal.coe_lt_coe_iff.mpr hb)) hr
  have h := rate_transfer_of_unconditional_tests T hmem hα hβ
  convert h using 1 <;> congr 1 <;> ring

end MatrixFamilies

theorem regularizedRelativeEntropyBits_self_matrix
    {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    [Nonempty A] (Φ : FiniteCPTP A B) : regularizedRelativeEntropyBits Φ Φ = 0 := by
  apply le_antisymm
  · refine iSup_le fun n => ?_
    change (((((n + 1 : ℕ) : ℝ)⁻¹ : ℝ) : EReal) * powerValue Φ Φ (n + 1)) ≤ 0
    have hs : powerValue Φ Φ (n + 1) = 0 := stabilizedRelativeEntropyBits_self _
    rw [hs, mul_zero]
  · exact regularizedRelativeEntropyBits_nonneg Φ Φ

section ChannelChainAndNested

open MatrixParallelPowerJoins

variable {I O C D R₁ R₂ X Y : FiniteSystem}

theorem superchannel_reference_output_relativeEntropy_le_real_budget
    (Θ₁ : FiniteSuperchannel I.basis O.basis C.basis D.basis R₁.basis)
    (Θ₂ : FiniteSuperchannel I.basis O.basis C.basis D.basis R₂.basis)
    (Φ Ψ : FiniteCPTP (I.prod X).basis (O.prod Y).basis)
    {B budget : ℝ}
    (hB : orderedSteinExponent (parallelStrategyFamily Θ₁ Θ₂) ≤ (B : EReal))
    (hReg : regularizedRelativeEntropyBits Φ Ψ ≤ (budget : EReal))
    (k : ℕ) {ρ σ : Matrix ((C.prod X).basis × Fin k) ((C.prod X).basis × Fin k) ℂ}
    (hρ : IsDensity ρ) (hσ : IsDensity σ) (cost : ℝ)
    (hInput : relativeEntropyBits ρ σ ≤ (cost : EReal)) :
    relativeEntropyBits
      (CPTPKraus.amplify ((extendSidePorts Θ₁ X Y).applyChannel Φ).map (Fin k) ρ)
      (CPTPKraus.amplify ((extendSidePorts Θ₂ X Y).applyChannel Ψ).map (Fin k) σ) ≤
        (((B + budget + cost : ℝ)) : EReal) := by
  letI : Nonempty (Fin k) := (ChannelEntropyChain.density_nonempty hρ).map Prod.snd
  let T : FiniteSystem := ⟨Fin k, inferInstance, inferInstance, inferInstance⟩
  let ei := Equiv.prodAssoc C.basis X.basis T.basis
  let eo := Equiv.prodAssoc D.basis Y.basis T.basis
  let ρr := reindexMap ei ρ
  let σr := reindexMap ei σ
  let Φr := SuperchannelReferenceTransport.associatedReferenceChannel Φ T
  let Ψr := SuperchannelReferenceTransport.associatedReferenceChannel Ψ T
  have hρr : IsDensity ρr := MatrixParallelPowerJoins.reindex_isDensity_matrix ei hρ
  have hσr : IsDensity σr := MatrixParallelPowerJoins.reindex_isDensity_matrix ei hσ
  have hcost : relativeEntropyBits ρr σr ≤ (cost : EReal) := by
    change relativeEntropyBits (Matrix.reindex ei ei ρ) (Matrix.reindex ei ei σ) ≤ _
    rw [relativeEntropyBits_reindex ei hρ.1 hσ.1]
    exact hInput
  have hr : regularizedRelativeEntropyBits Φr Ψr ≤ (budget : EReal) :=
    (SuperchannelReferenceTransport.regularized_associatedReferenceChannel_le Φ Ψ T).trans hReg
  have h := superchannel_output_relativeEntropy_le_real_budget Θ₁ Θ₂ Φr Ψr hρr hσr hr hcost
  change relativeEntropyBits
    (((extendSidePorts Θ₁ (X.prod T) (Y.prod T)).applyChannel
      (SuperchannelReferenceTransport.associatedReferenceChannel Φ T)).map (reindexMap ei ρ))
    (((extendSidePorts Θ₂ (X.prod T) (Y.prod T)).applyChannel
      (SuperchannelReferenceTransport.associatedReferenceChannel Ψ T)).map (reindexMap ei σ)) ≤ _ at h
  rw [SuperchannelReferenceTransport.matrix_slot_reference_intertwine Θ₁ Φ T ρ,
    SuperchannelReferenceTransport.matrix_slot_reference_intertwine Θ₂ Ψ T σ] at h
  have hΦ : (CPTPKraus.amplify ((extendSidePorts Θ₁ X Y).applyChannel Φ).map (Fin k) ρ).PosSemidef :=
    (channel_density (amplifiedChannel ((extendSidePorts Θ₁ X Y).applyChannel Φ) (Fin k)) hρ.1 hρ.2).1
  have hΨ : (CPTPKraus.amplify ((extendSidePorts Θ₂ X Y).applyChannel Ψ).map (Fin k) σ).PosSemidef :=
    (channel_density (amplifiedChannel ((extendSidePorts Θ₂ X Y).applyChannel Ψ) (Fin k)) hσ.1 hσ.2).1
  change relativeEntropyBits
    (Matrix.reindex eo eo (CPTPKraus.amplify ((extendSidePorts Θ₁ X Y).applyChannel Φ).map (Fin k) ρ))
    (Matrix.reindex eo eo (CPTPKraus.amplify ((extendSidePorts Θ₂ X Y).applyChannel Ψ).map (Fin k) σ)) ≤ _ at h
  rw [relativeEntropyBits_reindex eo hΦ hΨ] at h
  have hb := h.trans (add_le_add hB le_rfl)
  simpa only [← EReal.coe_add, add_assoc] using hb

theorem superchannel_channel_relativeEntropy_le_real_budget
    (Θ₁ : FiniteSuperchannel I.basis O.basis C.basis D.basis R₁.basis)
    (Θ₂ : FiniteSuperchannel I.basis O.basis C.basis D.basis R₂.basis)
    (Φ Ψ : FiniteCPTP (I.prod X).basis (O.prod Y).basis) {B budget : ℝ}
    (hB : orderedSteinExponent (parallelStrategyFamily Θ₁ Θ₂) ≤ (B : EReal))
    (hReg : regularizedRelativeEntropyBits Φ Ψ ≤ (budget : EReal)) :
    regularizedRelativeEntropyBits
      ((extendSidePorts Θ₁ X Y).applyChannel Φ)
      ((extendSidePorts Θ₂ X Y).applyChannel Ψ) ≤ (((B + budget : ℝ)) : EReal) := by
  apply ChannelAmortization.regularized_le_of_reference_increment
  intro k ρ σ hρ hσ cost hInput
  exact superchannel_reference_output_relativeEntropy_le_real_budget
    Θ₁ Θ₂ Φ Ψ hB hReg k hρ hσ cost hInput

theorem nestedCircuit_regularized_relativeEntropy_le
    (Θ₁ : FiniteSuperchannel I.basis O.basis C.basis D.basis R₁.basis)
    (Θ₂ : FiniteSuperchannel I.basis O.basis C.basis D.basis R₂.basis) {B : ℝ}
    (hB : orderedSteinExponent (parallelStrategyFamily Θ₁ Θ₂) ≤ (B : EReal))
    {n : ℕ} (inner : NestedCircuit I O C D X Y n) :
    regularizedRelativeEntropyBits (inner.evaluate Θ₁) (inner.evaluate Θ₂) ≤
      (((n : ℝ) * B : ℝ) : EReal) := by
  induction inner with
  | known K =>
      simpa only [NestedCircuit.evaluate_known, Nat.cast_zero, zero_mul, EReal.coe_zero] using
        (regularizedRelativeEntropyBits_self_matrix K).le
  | knownWrap Γ inner ih =>
      exact (regularizedRelativeEntropyBits_superchannel_le
        (inner.evaluate Θ₁) (inner.evaluate Θ₂) Γ).trans ih
  | @testedUse X Y n inner ih =>
      have h := superchannel_channel_relativeEntropy_le_real_budget Θ₁ Θ₂
        (inner.evaluate Θ₁) (inner.evaluate Θ₂) hB ih
      have hs : B + (n : ℝ) * B = ((n + 1 : ℕ) : ℝ) * B := by push_cast; ring
      simpa only [NestedCircuit.evaluate_testedUse, hs] using h

theorem nestedCircuit_output_relativeEntropy_le
    (Θ₁ : FiniteSuperchannel I.basis O.basis C.basis D.basis R₁.basis)
    (Θ₂ : FiniteSuperchannel I.basis O.basis C.basis D.basis R₂.basis) {B : ℝ}
    (hB : orderedSteinExponent (parallelStrategyFamily Θ₁ Θ₂) ≤ (B : EReal))
    {n : ℕ} (inner : NestedCircuit I O C D X Y n)
    {ρ : Matrix X.basis X.basis ℂ} (hρ : IsDensity ρ) :
    relativeEntropyBits ((inner.evaluate Θ₁).map ρ) ((inner.evaluate Θ₂).map ρ) ≤
      (((n : ℝ) * B : ℝ) : EReal) := by
  have h := ChannelEntropyChain.channel_relativeEntropy_chain
    (inner.evaluate Θ₁) (inner.evaluate Θ₂) hρ hρ
  rw [relativeEntropyBits_self, add_zero] at h
  exact h.trans (nestedCircuit_regularized_relativeEntropy_le Θ₁ Θ₂ hB inner)

theorem nestedStrategyFamily_uniformBinaryConverse
    (Θ₁ : FiniteSuperchannel I.basis O.basis C.basis D.basis R₁.basis)
    (Θ₂ : FiniteSuperchannel I.basis O.basis C.basis D.basis R₂.basis) {B : ℝ}
    (hB : orderedSteinExponent (parallelStrategyFamily Θ₁ Θ₂) ≤ (B : EReal)) :
    UniformBinaryConverse (nestedStrategyFamily Θ₁ Θ₂) B := by
  intro n hn T hT
  rcases hT with ⟨X, Y, inner, ρ, E, hρ, hE, rfl⟩
  change extendedBinaryRelativeEntropyBits
    (1 - (1 - acceptanceProbability ((inner.evaluate Θ₁).map ρ) E))
    (acceptanceProbability ((inner.evaluate Θ₂).map ρ) E) ≤ _
  rw [sub_sub_cancel]
  exact (MatrixStrategyAssembly.MatrixBinaryTesting.binary_errors_entropy_dpi
    (inner.evaluate_density Θ₁ hρ) (inner.evaluate_density Θ₂ hρ) hE).trans
      (nestedCircuit_output_relativeEntropy_le Θ₁ Θ₂ hB inner hρ)

theorem matrix_nested_parallel_orderedSteinExponent_eq
    (Θ₁ : FiniteSuperchannel I.basis O.basis C.basis D.basis R₁.basis)
    (Θ₂ : FiniteSuperchannel I.basis O.basis C.basis D.basis R₂.basis) :
    orderedSteinExponent (nestedStrategyFamily Θ₁ Θ₂) =
      orderedSteinExponent (parallelStrategyFamily Θ₁ Θ₂) := by
  apply conditional_orderedSteinExponent_eq_all
    (MatrixParallelAvailability.matrix_parallel_hasAcceptAll Θ₁ Θ₂)
    (parallelStrategyFamily_subset_nested Θ₁ Θ₂)
  intro B hparallel
  exact nestedStrategyFamily_uniformBinaryConverse Θ₁ Θ₂ (by rw [hparallel])

end ChannelChainAndNested

end QuantumProver.SuperchannelDiscrimination.SuperchannelEntropyChain

import QuantumProver.InformationTheory.SuperchannelDiscrimination.TestingConsequences
import QuantumProver.InformationTheory.SuperchannelDiscrimination.CommonWrapperRegularization
import QuantumProver.InformationTheory.SuperchannelDiscrimination.ChannelUniformFactory

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
open Matrix Filter
open scoped BigOperators Topology ComplexOrder MatrixOrder Matrix Kronecker

namespace QuantumProver.SuperchannelDiscrimination.ChannelEntropyChain

open FlaggedStates TensorPinching TensorEntropy ChannelRegularization DiamondControl KrausCompletion

variable {I O R : Type*} [Fintype I] [Fintype O] [Fintype R]
  [DecidableEq I] [DecidableEq O] [DecidableEq R]

theorem density_nonempty {ρ : Matrix I I ℂ} (hρ : IsDensity ρ) : Nonempty I := by
  by_contra h
  letI : IsEmpty I := not_nonempty_iff.mp h
  have hz : ρ.trace = 0 := by simp [Matrix.trace]
  have hbad : (0 : ℂ) = 1 := hz.symm.trans hρ.2
  exact zero_ne_one hbad

def statePowerIndex (A : Type*) : (n : ℕ) → RecursiveRows A n ≃ TensorIndex A n
  | 0 => Equiv.refl PUnit
  | n + 1 => Equiv.prodCongr (statePowerIndex A n) (Equiv.refl A)

theorem state_tensorPower_transport (X : Matrix I I ℂ) (n : ℕ) :
    CPWrappers.reindexMap (statePowerIndex I n) (recursiveTensorPower X n) =
      TensorEntropy.tensorPower X n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change CPWrappers.reindexMap (statePowerIndex I n) (recursiveTensorPower X n) ⊗ₖ X =
        TensorEntropy.tensorPower X n ⊗ₖ X
      rw [ih]

theorem channelPower_tensor_input (Φ : FiniteCPTP I O)
    (X : Matrix I I ℂ) (n : ℕ) :
    (channelPower Φ n).map (TensorEntropy.tensorPower X n) =
      TensorEntropy.tensorPower (Φ.map X) n := by
  induction n with
  | zero =>
      ext i j
      cases i
      cases j
      simp [channelPower, TensorEntropy.tensorPower, CPWrappers.reindexChannel,
        CPWrappers.reindexMap, Matrix.reindex_apply, Matrix.one_apply]
  | succ n ih =>
      change (tensorChannel (channelPower Φ n) Φ).map
          (TensorEntropy.tensorPower X n ⊗ₖ X) =
        TensorEntropy.tensorPower (Φ.map X) n ⊗ₖ Φ.map X
      rw [tensorChannel_map_product, ih]

theorem traceNorm_reindex {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (e : A ≃ B) (X : Matrix A A ℂ) :
    EffectPerturbation.traceNorm (CPWrappers.reindexMap e X) =
      EffectPerturbation.traceNorm X :=
  nuclearNorm_submatrix_equiv e.symm X

theorem acceptance_reindex {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (e : A ≃ B) (X Q : Matrix A A ℂ) :
    acceptanceProbability (CPWrappers.reindexMap e X) (CPWrappers.reindexMap e Q) =
      acceptanceProbability X Q := by
  unfold acceptanceProbability
  have hmul : CPWrappers.reindexMap e X * CPWrappers.reindexMap e Q =
      CPWrappers.reindexMap e (X * Q) :=
    ((Matrix.reindexRingEquiv ℂ e).map_mul X Q).symm
  rw [hmul]
  exact congrArg Complex.re (CPWrappers.reindexMap_tracePreserving e (X * Q))

theorem reindex_isEffect {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (e : A ≃ B)
    {Q : Matrix A A ℂ} (hQ : IsEffect Q) : IsEffect (CPWrappers.reindexMap e Q) := by
  refine ⟨hQ.1.submatrix e.symm, ?_⟩
  have h := hQ.2.submatrix e.symm
  change ((1 : Matrix A A ℂ).submatrix e.symm e.symm - Q.submatrix e.symm e.symm).PosSemidef at h
  rw [Matrix.submatrix_one_equiv] at h
  exact h

theorem normalized_state_smoothing_tail {ρ σ : Matrix I I ℂ}
    (hρ : IsDensity ρ) (hσ : IsDensity σ) (b : ℝ)
    (hb : relativeEntropyBits ρ σ < (b : EReal)) :
    ∃ ν : (n : ℕ) → Matrix (TensorIndex I n) (TensorIndex I n) ℂ,
      (∀ n, IsDensity (ν n)) ∧
      Tendsto (fun n => EffectPerturbation.traceNorm (TensorEntropy.tensorPower ρ n - ν n))
        atTop (𝓝 0) ∧
      ∀ᶠ n : ℕ in atTop,
        (((2 : ℝ) ^ ((n : ℝ) * b)) • TensorEntropy.tensorPower σ n - ν n).PosSemidef := by
  obtain ⟨ν₀, hν₀, ht, hcap⟩ := Corollaries.normalized_state_smoothing hρ hσ b hb
  let ν := fun n => CPWrappers.reindexMap (statePowerIndex I n) (ν₀ n)
  have hnorm (n : ℕ) :
      EffectPerturbation.traceNorm (TensorEntropy.tensorPower ρ n - ν n) =
        EffectPerturbation.traceNorm (recursiveTensorPower ρ n - ν₀ n) := by
    rw [← state_tensorPower_transport]
    change EffectPerturbation.traceNorm
      (CPWrappers.reindexMap (statePowerIndex I n) (recursiveTensorPower ρ n) -
        CPWrappers.reindexMap (statePowerIndex I n) (ν₀ n)) = _
    rw [← map_sub, traceNorm_reindex]
  refine ⟨ν, (fun n => CPWrappers.channel_density
    (CPWrappers.reindexChannel (statePowerIndex I n)) (hν₀ n).1 (hν₀ n).2), ?_, ?_⟩
  · simpa only [hnorm] using ht
  · filter_upwards [hcap] with n hn
    have h := hn.submatrix (statePowerIndex I n).symm
    change (((2 : ℝ) ^ ((n : ℝ) * b)) •
      CPWrappers.reindexMap (statePowerIndex I n) (recursiveTensorPower σ n) - ν n).PosSemidef at h
    rwa [state_tensorPower_transport] at h

theorem iid_bits_effect_achievability_tail (ρ σ : Matrix I I ℂ)
    (hρ : IsDensity ρ) (hσ : IsDensity σ) {r : ℝ}
    (hr : (r : EReal) < relativeEntropyBits ρ σ) :
    ∃ Q : (n : ℕ) → Matrix (TensorIndex I n) (TensorIndex I n) ℂ,
      (∀ n, IsEffect (Q n)) ∧
      Tendsto (fun n => acceptanceProbability (TensorEntropy.tensorPower ρ n) (1 - Q n))
        atTop (𝓝 0) ∧
      ∀ n, acceptanceProbability (TensorEntropy.tensorPower σ n) (Q n) ≤
        (2 : ℝ) ^ (-(n : ℝ) * r) := by
  obtain ⟨Q₀, hQ₀, ht, hβ⟩ := Corollaries.iid_bits_effect_achievability ρ σ hρ hσ hr
  let Q := fun n => CPWrappers.reindexMap (statePowerIndex I n) (Q₀ n)
  have hcomp (n : ℕ) : 1 - Q n =
      CPWrappers.reindexMap (statePowerIndex I n) (1 - Q₀ n) := by
    rw [map_sub]
    change 1 - (Q₀ n).submatrix (statePowerIndex I n).symm (statePowerIndex I n).symm =
      (1 : Matrix (RecursiveRows I n) (RecursiveRows I n) ℂ).submatrix
        (statePowerIndex I n).symm (statePowerIndex I n).symm - _
    rw [Matrix.submatrix_one_equiv]
    rfl
  have halpha (n : ℕ) : acceptanceProbability (TensorEntropy.tensorPower ρ n) (1 - Q n) =
      acceptanceProbability (recursiveTensorPower ρ n) (1 - Q₀ n) := by
    rw [← state_tensorPower_transport, hcomp, acceptance_reindex]
  refine ⟨Q, (fun n => reindex_isEffect _ (hQ₀ n)), ?_, ?_⟩
  · simpa only [halpha] using ht
  · intro n
    rw [← state_tensorPower_transport]
    exact (acceptance_reindex (statePowerIndex I n) (recursiveTensorPower σ n) (Q₀ n)).le.trans (hβ n)

theorem density_map_difference_le_of_diamondBudget
    (Δ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) {δ : ℝ}
    (hδ : diamondBudget Δ ≤ (δ : EReal)) {ρ : Matrix I I ℂ} (hρ : IsDensity ρ) :
    EffectPerturbation.traceNorm (Δ ρ) ≤ δ := by
  let ei : (I × PUnit.{1}) ≃ I := Equiv.prodPUnit I
  let eo : (O × PUnit.{1}) ≃ O := Equiv.prodPUnit O
  have hX : nuclearNorm (ρ.submatrix ei ei) ≤ 1 := by
    rw [nuclearNorm_submatrix_equiv, nuclearNorm_of_density hρ]
  have h := unitBall_output_le_of_diamondBudget Δ PUnit.{1} hδ hX
  change nuclearNorm ((Δ ρ).submatrix eo eo) ≤ δ at h
  rw [nuclearNorm_submatrix_equiv] at h
  exact h

theorem cpDom_state_acceptance
    {Λ Ψ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ} {b c : ℝ}
    (hΛ : CPTPKraus.CompletelyPositive Λ) (hdom : CPTPKraus.CPDom Λ Ψ c)
    (hb : 0 ≤ b) {ν σ : Matrix I I ℂ} (hσ : σ.PosSemidef)
    (hcap : ((b : ℂ) • σ - ν).PosSemidef)
    {Q : Matrix O O ℂ} (hQ : IsEffect Q) :
    acceptanceProbability (Λ ν) Q ≤ (b * c) * acceptanceProbability (Ψ σ) Q := by
  exact CPWrappers.acceptance_le_of_outputOrder
    (CPWrappers.cpDom_state_outputOrder hΛ hdom hb hσ hcap) hQ.1

theorem approximation_acceptance_lower
    (Φ : FiniteCPTP I O)
    (Λ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ)
    (hΛ : CPTPKraus.CompletelyPositive Λ) {δ η : ℝ}
    (hδ : diamondBudget (Φ.map - Λ) ≤ (δ : EReal))
    {ν ρ : Matrix I I ℂ} (hν : IsDensity ν) (hρ : IsDensity ρ)
    (hη : EffectPerturbation.traceNorm (ν - ρ) ≤ η)
    {Q : Matrix O O ℂ} (hQ : IsEffect Q) :
    acceptanceProbability (Φ.map ρ) Q - δ - (1 / 2) * η ≤
      acceptanceProbability (Λ ν) Q := by
  have hd := density_map_difference_le_of_diamondBudget (Φ.map - Λ) hδ hν
  change EffectPerturbation.traceNorm (Φ.map ν - Λ ν) ≤ δ at hd
  have hd' : EffectPerturbation.traceNorm (Λ ν - Φ.map ν) ≤ δ := by
    rw [← neg_sub (Φ.map ν) (Λ ν), ← nuclearNorm_eq_traceNorm, nuclearNorm_neg]
    exact hd
  exact EffectPerturbation.acceptance_lower_bound_of_input_and_output_errors Φ.map
    (fun X hX => CPWrappers.completelyPositive_positive Φ.completelyPositive hX)
    Φ.tracePreserving hQ (CPWrappers.completelyPositive_positive hΛ hν.1).isHermitian
    hν hρ hd' hη

theorem dyadic_cap_test_bound (n : ℕ) (a b r : ℝ) {p q : ℝ}
    (hp : p ≤ ((2 : ℝ) ^ ((n : ℝ) * b) * (2 : ℝ) ^ ((n : ℝ) * a)) * q)
    (hq : q ≤ (2 : ℝ) ^ (-(n : ℝ) * r)) :
    p ≤ (2 : ℝ) ^ ((n : ℝ) * (a + b - r)) := by
  calc
    p ≤ ((2 : ℝ) ^ ((n : ℝ) * b) * (2 : ℝ) ^ ((n : ℝ) * a)) *
        (2 : ℝ) ^ (-(n : ℝ) * r) :=
      hp.trans (mul_le_mul_of_nonneg_left hq (by positivity))
    _ = _ := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
        ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      congr 1
      ring

theorem dyadic_strict_rate_tendsto_zero {a b r : ℝ} (hr : a + b < r) :
    Tendsto (fun n : ℕ => (2 : ℝ) ^ ((n : ℝ) * (a + b - r))) atTop (𝓝 0) := by
  have hq0 : 0 ≤ (2 : ℝ) ^ (a + b - r) := Real.rpow_nonneg (by norm_num) _
  have hq1 : (2 : ℝ) ^ (a + b - r) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have h := tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1
  convert h using 1
  funext n
  rw [← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2)]
  congr 1
  ring

theorem traceNorm_sub_comm (A B : Matrix I I ℂ) :
    EffectPerturbation.traceNorm (A - B) = EffectPerturbation.traceNorm (B - A) := by
  change nuclearNorm (A - B) = nuclearNorm (B - A)
  rw [← neg_sub B A, nuclearNorm_neg]

theorem channel_output_relativeEntropy_le_real_budget (Φ Ψ : FiniteCPTP I O)
    {ρ σ : Matrix I I ℂ} (hρ : IsDensity ρ) (hσ : IsDensity σ)
    {budget inputBudget : ℝ}
    (hReg : regularizedRelativeEntropyBits Φ Ψ ≤ (budget : EReal))
    (hInput : relativeEntropyBits ρ σ ≤ (inputBudget : EReal)) :
    relativeEntropyBits (Φ.map ρ) (Ψ.map σ) ≤ ((budget + inputBudget : ℝ) : EReal) := by
  letI : Nonempty I := density_nonempty hρ
  by_contra hbad
  obtain ⟨r, hsumr, hrD⟩ := EReal.exists_between_coe_real (lt_of_not_ge hbad)
  have hsumr' : budget + inputBudget < r := EReal.coe_lt_coe_iff.mp hsumr
  let margin := (r - (budget + inputBudget)) / 3
  let a := budget + margin
  let b := inputBudget + margin
  have hba : budget < a := by dsimp [a, margin]; linarith
  have hib : inputBudget < b := by dsimp [b, margin]; linarith
  have habr : a + b < r := by dsimp [a, b, margin]; linarith
  have ha : regularizedRelativeEntropyBits Φ Ψ < (a : EReal) :=
    hReg.trans_lt (EReal.coe_lt_coe_iff.mpr hba)
  have hb : relativeEntropyBits ρ σ < (b : EReal) :=
    hInput.trans_lt (EReal.coe_lt_coe_iff.mpr hib)
  obtain ⟨Λ, errors, herrors0, herrors, hΛ, hΛcap⟩ :=
    ChannelUniformFactory.exists_channel_uniform_approximation_tendsto Φ Ψ ha
  obtain ⟨ν, hν, hνerror, hνcap⟩ := normalized_state_smoothing_tail hρ hσ b hb
  have hτ : IsDensity (Φ.map ρ) := CPWrappers.channel_density Φ hρ.1 hρ.2
  have hω : IsDensity (Ψ.map σ) := CPWrappers.channel_density Ψ hσ.1 hσ.2
  obtain ⟨Q, hQ, hα, hβ⟩ := iid_bits_effect_achievability_tail (Φ.map ρ) (Ψ.map σ) hτ hω hrD
  have hlimit : Tendsto (fun n =>
      1 - acceptanceProbability (TensorEntropy.tensorPower (Φ.map ρ) n) (1 - Q n) -
        errors n - (1 / 2) * EffectPerturbation.traceNorm (TensorEntropy.tensorPower ρ n - ν n))
      atTop (𝓝 (1 : ℝ)) := by
    simpa only [sub_zero, mul_zero] using
      ((tendsto_const_nhds.sub hα).sub herrors).sub (hνerror.const_mul (1 / 2))
  have hupper := dyadic_strict_rate_tendsto_zero habr
  have horder : ∀ᶠ n : ℕ in atTop,
      1 - acceptanceProbability (TensorEntropy.tensorPower (Φ.map ρ) n) (1 - Q n) -
        errors n - (1 / 2) * EffectPerturbation.traceNorm (TensorEntropy.tensorPower ρ n - ν n) ≤
      (2 : ℝ) ^ ((n : ℝ) * (a + b - r)) := by
    filter_upwards [hΛcap, hνcap] with n hn hcap
    have heta : EffectPerturbation.traceNorm (ν n - TensorEntropy.tensorPower ρ n) ≤
        EffectPerturbation.traceNorm (TensorEntropy.tensorPower ρ n - ν n) :=
      (traceNorm_sub_comm _ _).le
    have hlower := approximation_acceptance_lower (channelPower Φ n) (Λ n) (hΛ n).1 hn.2
      (hν n) (tensorPower_isDensity hρ n) heta (hQ n)
    have hu := cpDom_state_acceptance (hΛ n).1 hn.1
      (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) ((n : ℝ) * b))
      (tensorPower_isDensity hσ n).1 hcap (hQ n)
    rw [channelPower_tensor_input] at hlower hu
    have hc := QuantumSteinAchievability.acceptanceProbability_complement
      (tensorPower_isDensity hτ n) (E := Q n)
    have hlower' :
        1 - acceptanceProbability (TensorEntropy.tensorPower (Φ.map ρ) n) (1 - Q n) -
          errors n - (1 / 2) * EffectPerturbation.traceNorm (TensorEntropy.tensorPower ρ n - ν n) ≤
        acceptanceProbability (Λ n (ν n)) (Q n) := by
      rw [hc]
      linarith
    exact hlower'.trans (dyadic_cap_test_bound n a b r hu (hβ n))
  have h10 : (1 : ℝ) ≤ 0 := le_of_tendsto_of_tendsto hlimit hupper horder
  norm_num at h10

theorem channel_relativeEntropy_chain (Φ Ψ : FiniteCPTP I O)
    {ρ σ : Matrix I I ℂ} (hρ : IsDensity ρ) (hσ : IsDensity σ) :
    relativeEntropyBits (Φ.map ρ) (Ψ.map σ) ≤
      regularizedRelativeEntropyBits Φ Ψ + relativeEntropyBits ρ σ := by
  letI : Nonempty I := density_nonempty hρ
  have hinb : relativeEntropyBits ρ σ ≠ ⊥ :=
    ne_of_gt (EReal.bot_lt_zero.trans_le (Klein.relativeEntropyBits_nonneg hρ hσ))
  cases hReg : regularizedRelativeEntropyBits Φ Ψ with
  | bot => exact False.elim ((regularizedRelativeEntropyBits_ne_bot Φ Ψ) hReg)
  | top => rw [EReal.top_add_of_ne_bot hinb]; exact le_top
  | coe budget =>
      cases hInput : relativeEntropyBits ρ σ with
      | bot => exact False.elim (hinb hInput)
      | top => rw [EReal.coe_add_top]; exact le_top
      | coe inputBudget =>
          have h := channel_output_relativeEntropy_le_real_budget Φ Ψ hρ hσ
            (by rw [hReg]) (by rw [hInput])
          simpa only [EReal.coe_add] using h

theorem channel_reference_relativeEntropy_chain (Φ Ψ : FiniteCPTP I O)
    (R : Type*) [Fintype R] [DecidableEq R]
    {ρ σ : Matrix (I × R) (I × R) ℂ} (hρ : IsDensity ρ) (hσ : IsDensity σ) :
    relativeEntropyBits (CPTPKraus.amplify Φ.map R ρ) (CPTPKraus.amplify Ψ.map R σ) ≤
      regularizedRelativeEntropyBits Φ Ψ + relativeEntropyBits ρ σ := by
  have h := channel_relativeEntropy_chain (CPWrappers.amplifiedChannel Φ R)
    (CPWrappers.amplifiedChannel Ψ R) hρ hσ
  exact h.trans (add_le_add (regularizedRelativeEntropyBits_amplified_le Φ Ψ) le_rfl)

end QuantumProver.SuperchannelDiscrimination.ChannelEntropyChain

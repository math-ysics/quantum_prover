import QuantumProver.InformationTheory.DepolarizingSquashedEntanglement.BCYCompositeTesting
import QuantumProver.InformationTheory.SuperchannelDiscrimination.QuantumSteinAchievability

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

noncomputable section
open Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator ENNReal NNReal

namespace QuantumProver.DepolarizingSquashedEntanglement.BCYTestingPrimitives

open BCYRelativeEntropy BCYCompositeTesting

variable {I J A B C D : Type*} [Fintype I] [Fintype J]
  [Fintype A] [Fintype B] [Fintype C] [Fintype D]
  [DecidableEq I] [DecidableEq J] [DecidableEq A] [DecidableEq B]
  [DecidableEq C] [DecidableEq D]

private theorem matrixCP (Phi : CPTP I J) :
    QuantumProver.SuperchannelDiscrimination.CPTPKraus.CompletelyPositive Phi.map :=
  (QuantumProver.SuperchannelDiscrimination.CPTPKraus.completelyPositive_iff_EJMCP _).mpr
    Phi.completelyPositive

def effectPullbackMatrix (Phi : CPTP I J) (T : QMatrix J) : QMatrix I :=
  ∑ q : I × J,
    (QuantumProver.SuperchannelDiscrimination.CPTPKraus.canonicalKraus Phi.map q)ᴴ * T *
      QuantumProver.SuperchannelDiscrimination.CPTPKraus.canonicalKraus Phi.map q

theorem effectPullbackMatrix_positive (Phi : CPTP I J) {T : QMatrix J}
    (hT : T.PosSemidef) : (effectPullbackMatrix Phi T).PosSemidef := by
  apply Matrix.posSemidef_sum Finset.univ
  intro q hq
  simpa only [Matrix.conjTranspose_conjTranspose] using
    hT.mul_mul_conjTranspose_same
      (QuantumProver.SuperchannelDiscrimination.CPTPKraus.canonicalKraus Phi.map q)ᴴ

theorem effectPullbackMatrix_complement (Phi : CPTP I J) (T : QMatrix J) :
    effectPullbackMatrix Phi (1 - T) = 1 - effectPullbackMatrix Phi T := by
  unfold effectPullbackMatrix
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Finset.sum_sub_distrib]
  rw [QuantumProver.SuperchannelDiscrimination.CPTPKraus.canonicalKraus_gram
    Phi.map (matrixCP Phi) Phi.tracePreserving]

def effectPullback (Phi : CPTP I J) (T : BinaryEffect J) : BinaryEffect I where
  matrix := effectPullbackMatrix Phi T.matrix
  positive := effectPullbackMatrix_positive Phi T.positive
  complement_positive := by
    rw [← effectPullbackMatrix_complement]
    exact effectPullbackMatrix_positive Phi T.complement_positive

theorem trace_effectPullbackMatrix (Phi : CPTP I J) (X : QMatrix I) (T : QMatrix J) :
    (X * effectPullbackMatrix Phi T).trace = (Phi.map X * T).trace := by
  rw [QuantumProver.SuperchannelDiscrimination.CPTPKraus.canonicalKraus_reconstruct
    Phi.map (matrixCP Phi) X]
  simp only [effectPullbackMatrix, Matrix.mul_sum, Matrix.sum_mul, Matrix.trace_sum]
  apply Finset.sum_congr rfl
  intro q hq
  let K := QuantumProver.SuperchannelDiscrimination.CPTPKraus.canonicalKraus Phi.map q
  change (X * (Kᴴ * T * K)).trace = (K * X * Kᴴ * T).trace
  calc
    (X * (Kᴴ * T * K)).trace = ((X * Kᴴ * T) * K).trace := by
      simp only [Matrix.mul_assoc]
    _ = (K * (X * Kᴴ * T)).trace := Matrix.trace_mul_comm _ _
    _ = (K * X * Kᴴ * T).trace := by simp only [Matrix.mul_assoc]

theorem acceptance_effectPullback (Phi : CPTP I J) (rho : Density I)
    (T : BinaryEffect J) :
    acceptance rho (effectPullback Phi T) = acceptance (Phi.onDensity rho) T := by
  exact congrArg Complex.re (trace_effectPullbackMatrix Phi rho.matrix T.matrix)

theorem singleAlternativeBeta_channel_le (Phi : CPTP (A × B) (C × D))
    (rho sigma : Density (A × B)) (epsilon : ℝ) :
    singleAlternativeBeta rho sigma epsilon ≤
      singleAlternativeBeta (Phi.onDensity rho) (Phi.onDensity sigma) epsilon := by
  apply le_iInf
  intro T
  let U : {U : BinaryEffect (A × B) // 1 - epsilon ≤ acceptance rho U} :=
    ⟨effectPullback Phi T.val, by rw [acceptance_effectPullback]; exact T.property⟩
  apply iInf_le_of_le U
  rw [show acceptance sigma U.val = acceptance (Phi.onDensity sigma) T.val from
    acceptance_effectPullback Phi sigma T.val]

theorem hypothesisTestingSingleNat_channel_mono (Phi : CPTP (A × B) (C × D))
    (rho sigma : Density (A × B)) (epsilon : ℝ) :
    hypothesisTestingSingleNat (Phi.onDensity rho) (Phi.onDensity sigma) epsilon ≤
      hypothesisTestingSingleNat rho sigma epsilon :=
  EReal.neg_le_neg_iff.mpr
    (ENNReal.log_monotone (singleAlternativeBeta_channel_le Phi rho sigma epsilon))

theorem acceptance_le_mul_of_alternative_le (sigmaStar sigmaRound : Density I)
    (T : BinaryEffect I) {c : ℝ} (horder : sigmaStar.matrix ≤ c • sigmaRound.matrix) :
    acceptance sigmaStar T ≤ c * acceptance sigmaRound T := by
  have h := QuantumProver.SuperchannelDiscrimination.FlaggedStates.trace_mul_re_nonneg
    (Matrix.le_iff.mp horder) T.positive
  simp only [Matrix.sub_mul, Matrix.smul_mul, Matrix.trace_sub, Matrix.trace_smul,
    Complex.sub_re, Complex.smul_re, smul_eq_mul] at h
  dsimp [acceptance]
  linarith

theorem singleAlternativeBetaReal_le_mul_of_alternative_le
    (rho sigmaStar sigmaRound : Density (A × B)) {epsilon c : ℝ}
    (hc : 0 ≤ c)
    (horder : sigmaStar.matrix ≤ c • sigmaRound.matrix) :
    singleAlternativeBetaReal rho sigmaStar epsilon ≤
      c * singleAlternativeBetaReal rho sigmaRound epsilon := by
  unfold singleAlternativeBetaReal
  rw [Real.mul_iInf_of_nonneg hc]
  apply ciInf_mono
  · exact ⟨0, by rintro x ⟨T, rfl⟩; exact (acceptance_bounds sigmaStar T.val).1⟩
  · intro T
    exact acceptance_le_mul_of_alternative_le sigmaStar sigmaRound T.val horder

theorem singleAlternativeBeta_le_mul_of_alternative_le
    (rho sigmaStar sigmaRound : Density (A × B)) {epsilon c : ℝ}
    (he : 0 ≤ epsilon) (hc : 0 ≤ c)
    (horder : sigmaStar.matrix ≤ c • sigmaRound.matrix) :
    singleAlternativeBeta rho sigmaStar epsilon ≤
      ENNReal.ofReal c * singleAlternativeBeta rho sigmaRound epsilon := by
  rw [singleAlternativeBeta_eq_ofReal rho sigmaStar he,
    singleAlternativeBeta_eq_ofReal rho sigmaRound he, ← ENNReal.ofReal_mul hc]
  exact ENNReal.ofReal_le_ofReal
    (singleAlternativeBetaReal_le_mul_of_alternative_le rho sigmaStar sigmaRound hc horder)

theorem hypothesisTestingSingleNat_le_add_log_of_alternative_le
    (rho sigmaStar sigmaRound : Density (A × B)) {epsilon c : ℝ}
    (he : 0 ≤ epsilon) (hc : 0 < c)
    (horder : sigmaStar.matrix ≤ c • sigmaRound.matrix) :
    hypothesisTestingSingleNat rho sigmaRound epsilon ≤
      hypothesisTestingSingleNat rho sigmaStar epsilon + (Real.log c : EReal) := by
  have h := EReal.neg_le_neg_iff.mpr (ENNReal.log_monotone
    (singleAlternativeBeta_le_mul_of_alternative_le rho sigmaStar sigmaRound he hc.le horder))
  rw [ENNReal.log_mul_add, ENNReal.log_ofReal_of_pos hc,
    EReal.neg_add (.inl (EReal.coe_ne_bot _)) (.inl (EReal.coe_ne_top _))] at h
  have hs : hypothesisTestingSingleNat rho sigmaRound epsilon - (Real.log c : EReal) ≤
      hypothesisTestingSingleNat rho sigmaStar epsilon := by
    simpa only [hypothesisTestingSingleNat, sub_eq_add_neg, add_comm] using h
  exact (EReal.sub_le_iff_le_add
    (.inl (EReal.coe_ne_bot _)) (.inl (EReal.coe_ne_top _))).mp hs

def nonnegativeIndicator (x : ℝ) : ℝ := if 0 ≤ x then 1 else 0

@[simp] theorem nonnegativeIndicator_zero : nonnegativeIndicator 0 = 1 := by
  simp [nonnegativeIndicator]

def nonnegativeSpectralTest (H : QMatrix I) : QMatrix I := cfc nonnegativeIndicator H

theorem nonnegativeSpectralTest_isEffect {H : QMatrix I} (hH : H.IsHermitian) :
    QuantumProver.SuperchannelDiscrimination.FlaggedStates.IsEffect (nonnegativeSpectralTest H) := by
  unfold nonnegativeSpectralTest
  rw [QuantumProver.SuperchannelDiscrimination.PetzTensorTail.cfc_spectralProjections _ hH]
  apply QuantumProver.SuperchannelDiscrimination.PetzTensorTail.spectralCombination_isEffect
    (QuantumProver.SuperchannelDiscrimination.SpectralPinching.spectralProjections_family hH)
  · intro i
    unfold nonnegativeIndicator
    split_ifs <;> norm_num
  · intro i
    unfold nonnegativeIndicator
    split_ifs <;> norm_num

theorem nonnegativeSpectralTest_product_posSemidef {H : QMatrix I}
    (hH : H.IsHermitian) : (H * nonnegativeSpectralTest H).PosSemidef := by
  have hprod : H * nonnegativeSpectralTest H =
      cfc (fun x : ℝ => x * nonnegativeIndicator x) H := by
    calc
      H * nonnegativeSpectralTest H =
          cfc (fun x : ℝ => x) H * cfc nonnegativeIndicator H := by
        rw [cfc_id' (p := IsSelfAdjoint) ℝ H hH]
        rfl
      _ = cfc (fun x : ℝ => x * nonnegativeIndicator x) H :=
        (cfc_mul (p := IsSelfAdjoint) (fun x : ℝ => x) nonnegativeIndicator H
          (H.finite_real_spectrum.continuousOn _) (H.finite_real_spectrum.continuousOn _)).symm
  rw [hprod]
  apply (show (0 : QMatrix I) ≤ cfc
    (fun x : ℝ => x * nonnegativeIndicator x) H from ?_).posSemidef
  apply cfc_nonneg (p := IsSelfAdjoint)
  intro x hx
  unfold nonnegativeIndicator
  split_ifs with hpos
  · simpa using hpos
  · simp

def neymanPearsonEffectGE (rho sigma : Density I) (n : ℕ) (a : ℝ) : BinaryEffect I where
  matrix := nonnegativeSpectralTest (rho.matrix - Real.exp ((n : ℝ) * a) • sigma.matrix)
  positive := (nonnegativeSpectralTest_isEffect
    (rho.positive.1.sub (sigma.positive.1.smul (IsSelfAdjoint.all _)))).1
  complement_positive := (nonnegativeSpectralTest_isEffect
    (rho.positive.1.sub (sigma.positive.1.smul (IsSelfAdjoint.all _)))).2

theorem neymanPearsonEffectGE_weighted_beta_le (rho sigma : Density I) (n : ℕ) (a : ℝ) :
    Real.exp ((n : ℝ) * a) * acceptance sigma (neymanPearsonEffectGE rho sigma n a) ≤
      acceptance rho (neymanPearsonEffectGE rho sigma n a) := by
  have hp := nonnegativeSpectralTest_product_posSemidef
    (rho.positive.1.sub (sigma.positive.1.smul (IsSelfAdjoint.all (Real.exp ((n : ℝ) * a)))))
  have h := (Complex.nonneg_iff.mp hp.trace_nonneg).1
  change 0 ≤ ((rho.matrix - Real.exp ((n : ℝ) * a) • sigma.matrix) *
    (neymanPearsonEffectGE rho sigma n a).matrix).trace.re at h
  simp only [Matrix.sub_mul, Matrix.smul_mul, Matrix.trace_sub, Matrix.trace_smul,
    Complex.sub_re, Complex.smul_re, smul_eq_mul] at h
  dsimp [acceptance]
  linarith

theorem neymanPearsonEffectGE_beta_le (rho sigma : Density I) (n : ℕ) (a : ℝ) :
    acceptance sigma (neymanPearsonEffectGE rho sigma n a) ≤ Real.exp (-(n : ℝ) * a) := by
  have h : acceptance sigma (neymanPearsonEffectGE rho sigma n a) ≤
      1 / Real.exp ((n : ℝ) * a) := by
    apply (le_div_iff₀ (Real.exp_pos _)).mpr
    rw [mul_comm]
    exact (neymanPearsonEffectGE_weighted_beta_le rho sigma n a).trans
      (acceptance_bounds rho _).2
  simpa only [one_div, ← Real.exp_neg, neg_mul] using h

def neymanPearsonEffectGT (rho sigma : Density I) (n : ℕ) (a : ℝ) : BinaryEffect I where
  matrix := QuantumProver.SuperchannelDiscrimination.PetzTensorTail.spectralUpperTail
    rho.matrix sigma.matrix (Real.exp ((n : ℝ) * a))
  positive := (QuantumProver.SuperchannelDiscrimination.QuantumSteinAchievability.neymanPearson_isEffect
    rho.positive.1 sigma.positive.1 _).1
  complement_positive :=
    (QuantumProver.SuperchannelDiscrimination.QuantumSteinAchievability.neymanPearson_isEffect
      rho.positive.1 sigma.positive.1 _).2

theorem neymanPearsonEffectGT_beta_le (rho sigma : Density I) (n : ℕ) (a : ℝ) :
    acceptance sigma (neymanPearsonEffectGT rho sigma n a) ≤ Real.exp (-(n : ℝ) * a) := by
  have h := QuantumProver.SuperchannelDiscrimination.QuantumSteinAchievability.neymanPearson_beta_le_inv
    (density_matrix rho) sigma.positive.1 (Real.exp_pos ((n : ℝ) * a))
  simpa only [acceptance, neymanPearsonEffectGT,
    QuantumProver.SuperchannelDiscrimination.FlaggedStates.acceptanceProbability,
    one_div, ← Real.exp_neg, neg_mul] using h

theorem singleAlternativeBeta_le_of_effect (rho sigma : Density (A × B))
    (T : BinaryEffect (A × B)) {epsilon : ℝ}
    (ha : 1 - epsilon ≤ acceptance rho T) :
    singleAlternativeBeta rho sigma epsilon ≤ ENNReal.ofReal (acceptance sigma T) :=
  iInf_le_of_le ⟨T, ha⟩ le_rfl

theorem hypothesisTestingSingleNat_ge_of_beta_bound (rho sigma : Density (A × B))
    (T : BinaryEffect (A × B)) {epsilon b : ℝ}
    (ha : 1 - epsilon ≤ acceptance rho T)
    (hb : acceptance sigma T ≤ Real.exp (-b)) :
    (b : EReal) ≤ hypothesisTestingSingleNat rho sigma epsilon := by
  have h := EReal.neg_le_neg_iff.mpr (ENNReal.log_monotone
    ((singleAlternativeBeta_le_of_effect rho sigma T ha).trans (ENNReal.ofReal_le_ofReal hb)))
  simpa only [hypothesisTestingSingleNat, ENNReal.log_ofReal_of_pos (Real.exp_pos _),
    Real.log_exp, ← EReal.coe_neg, neg_neg] using h

theorem hypothesisTestingSingleNat_ge_of_neymanPearsonGE
    (rho sigma : Density (A × B)) (n : ℕ) (a : ℝ) {epsilon : ℝ}
    (ha : 1 - epsilon ≤ acceptance rho (neymanPearsonEffectGE rho sigma n a)) :
    ((n : ℝ) * a : EReal) ≤ hypothesisTestingSingleNat rho sigma epsilon := by
  apply hypothesisTestingSingleNat_ge_of_beta_bound rho sigma
    (neymanPearsonEffectGE rho sigma n a) ha
  simpa only [neg_mul] using neymanPearsonEffectGE_beta_le rho sigma n a

end QuantumProver.DepolarizingSquashedEntanglement.BCYTestingPrimitives

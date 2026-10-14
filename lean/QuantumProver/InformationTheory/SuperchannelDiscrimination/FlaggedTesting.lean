import QuantumProver.InformationTheory.SuperchannelDiscrimination.ParallelPowerJoins
import QuantumProver.InformationTheory.SuperchannelDiscrimination.ChannelUniformFactory

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option maxRecDepth 4000
noncomputable section

namespace QuantumProver.SuperchannelDiscrimination.MatrixFlaggedTesting

open Matrix KrausCompletion CPWrappers FlaggedStates TensorEntropy ChannelRegularization
open MatrixStrategyAssembly MatrixStrategyAssembly.MatrixStrategies MatrixParallelPowerJoins
open scoped BigOperators ComplexOrder MatrixOrder Matrix Kronecker Topology

def flagSystem : FiniteSystem where
  basis := Fin 2
  finite := inferInstance
  decidableEq := inferInstance
  nonempty := inferInstance

def flaggedSideChannel {I O X Y : FiniteSystem}
    (Λ : Matrix (I.prod X).basis (I.prod X).basis ℂ →ₗ[ℂ]
      Matrix (O.prod Y).basis (O.prod Y).basis ℂ)
    (o₀ : (O.prod Y).basis) (hΛ : CPTPKraus.CompletelyPositive Λ)
    (hTNI : CPTPKraus.TraceNonincreasing Λ) :
    FiniteCPTP (I.prod (X.prod flagSystem)).basis (O.prod (Y.prod flagSystem)).basis :=
  composeChannel (reindexChannel (Equiv.prodAssoc O.basis Y.basis (Fin 2)))
    (composeChannel (flaggedInsertedChannel Λ o₀ hΛ hTNI)
      (reindexChannel (Equiv.prodAssoc I.basis X.basis (Fin 2)).symm))

theorem flaggedSideChannel_intertwine {I O C D R X Y : FiniteSystem}
    (Γ : FiniteSuperchannel I.basis O.basis C.basis D.basis R.basis)
    (Λ : Matrix (I.prod X).basis (I.prod X).basis ℂ →ₗ[ℂ]
      Matrix (O.prod Y).basis (O.prod Y).basis ℂ)
    (o₀ : (O.prod Y).basis) (hΛ : CPTPKraus.CompletelyPositive Λ)
    (hTNI : CPTPKraus.TraceNonincreasing Λ)
    (A : Matrix ((C.prod X).prod flagSystem).basis ((C.prod X).prod flagSystem).basis ℂ) :
    ((extendSidePorts Γ (X.prod flagSystem) (Y.prod flagSystem)).applyChannel
        (flaggedSideChannel Λ o₀ hΛ hTNI)).map
      (reindexMap (Equiv.prodAssoc C.basis X.basis (Fin 2)) A) =
    reindexMap (Equiv.prodAssoc D.basis Y.basis (Fin 2))
      (((extendFlagSuperchannel (extendSidePorts Γ X Y)).applyChannel
        (flaggedInsertedChannel Λ o₀ hΛ hTNI)).map A) := by
  ext ⟨d, ⟨y, f⟩⟩ ⟨e, ⟨z, g⟩⟩
  rfl

def flaggedParallelTest {I O C D R₁ R₂ X Y : FiniteSystem}
    (Θ₁ : FiniteSuperchannel I.basis O.basis C.basis D.basis R₁.basis)
    (Θ₂ : FiniteSuperchannel I.basis O.basis C.basis D.basis R₂.basis)
    (n : ℕ)
    (Λ : Matrix ((I.tensorPower n).prod X).basis ((I.tensorPower n).prod X).basis ℂ →ₗ[ℂ]
      Matrix ((O.tensorPower n).prod Y).basis ((O.tensorPower n).prod Y).basis ℂ)
    (o₀ : ((O.tensorPower n).prod Y).basis)
    (hΛ : CPTPKraus.CompletelyPositive Λ) (hTNI : CPTPKraus.TraceNonincreasing Λ)
    (ν : Matrix ((C.tensorPower n).prod X).basis ((C.tensorPower n).prod X).basis ℂ)
    (Q : Matrix ((D.tensorPower n).prod Y).basis ((D.tensorPower n).prod Y).basis ℂ)
    (hν : IsDensity ν) (hQ : IsEffect Q) : BinaryTest :=
  parallelBinaryTest Θ₁ Θ₂ n (X.prod flagSystem) (Y.prod flagSystem)
    (flaggedSideChannel Λ o₀ hΛ hTNI)
    (reindexMap (Equiv.prodAssoc (C.tensorPower n).basis X.basis (Fin 2))
      (MatrixStrategyAssembly.flagBlock ν 0))
    (reindexMap (Equiv.prodAssoc (D.tensorPower n).basis Y.basis (Fin 2))
      (MatrixStrategyAssembly.flagBlock Q 0))
    (reindex_isDensity_matrix _ (successFlag_isDensity hν))
    (reindex_isEffect_matrix _ (physicalFlag_success_isEffect hQ))

theorem flaggedParallelTest_mem {I O C D R₁ R₂ X Y : FiniteSystem}
    (Θ₁ : FiniteSuperchannel I.basis O.basis C.basis D.basis R₁.basis)
    (Θ₂ : FiniteSuperchannel I.basis O.basis C.basis D.basis R₂.basis)
    (n : ℕ)
    (Λ : Matrix ((I.tensorPower n).prod X).basis ((I.tensorPower n).prod X).basis ℂ →ₗ[ℂ]
      Matrix ((O.tensorPower n).prod Y).basis ((O.tensorPower n).prod Y).basis ℂ)
    (o₀ : ((O.tensorPower n).prod Y).basis)
    (hΛ : CPTPKraus.CompletelyPositive Λ) (hTNI : CPTPKraus.TraceNonincreasing Λ)
    (ν : Matrix ((C.tensorPower n).prod X).basis ((C.tensorPower n).prod X).basis ℂ)
    (Q : Matrix ((D.tensorPower n).prod Y).basis ((D.tensorPower n).prod Y).basis ℂ)
    (hν : IsDensity ν) (hQ : IsEffect Q) :
    flaggedParallelTest Θ₁ Θ₂ n Λ o₀ hΛ hTNI ν Q hν hQ ∈
      parallelStrategyFamily Θ₁ Θ₂ n :=
  parallel_binaryTest_mem _ _ _ _ _ _ _ _ _ _

theorem flaggedSideChannel_success_acceptance {I O C D R X Y : FiniteSystem}
    (Γ : FiniteSuperchannel I.basis O.basis C.basis D.basis R.basis)
    (Λ : Matrix (I.prod X).basis (I.prod X).basis ℂ →ₗ[ℂ]
      Matrix (O.prod Y).basis (O.prod Y).basis ℂ)
    (o₀ : (O.prod Y).basis) (hΛ : CPTPKraus.CompletelyPositive Λ)
    (hTNI : CPTPKraus.TraceNonincreasing Λ)
    (ν : Matrix (C.prod X).basis (C.prod X).basis ℂ)
    (Q : Matrix (D.prod Y).basis (D.prod Y).basis ℂ) :
    acceptanceProbability
      (((extendSidePorts Γ (X.prod flagSystem) (Y.prod flagSystem)).applyChannel
        (flaggedSideChannel Λ o₀ hΛ hTNI)).map
          (reindexMap (Equiv.prodAssoc C.basis X.basis (Fin 2))
            (MatrixStrategyAssembly.flagBlock ν 0)))
      (reindexMap (Equiv.prodAssoc D.basis Y.basis (Fin 2))
        (MatrixStrategyAssembly.flagBlock Q 0)) =
      acceptanceProbability ((extendSidePorts Γ X Y).applyLinear Λ ν) Q := by
  rw [flaggedSideChannel_intertwine]
  erw [acceptanceProbability_reindex_matrix]
  change acceptance
    (((extendFlagSuperchannel (extendSidePorts Γ X Y)).applyChannel
      (flaggedInsertedChannel Λ o₀ hΛ hTNI)).map (MatrixStrategyAssembly.flagBlock ν 0))
    (MatrixStrategyAssembly.flagBlock Q 0) = acceptance ((extendSidePorts Γ X Y).applyLinear Λ ν) Q
  rw [extendedFlaggedCompletion_success_acceptance, discardInputFlag_successFlag]

theorem flaggedParallelTest_alpha {I O C D R₁ R₂ X Y : FiniteSystem}
    (Θ₁ : FiniteSuperchannel I.basis O.basis C.basis D.basis R₁.basis)
    (Θ₂ : FiniteSuperchannel I.basis O.basis C.basis D.basis R₂.basis)
    (n : ℕ)
    (Λ : Matrix ((I.tensorPower n).prod X).basis ((I.tensorPower n).prod X).basis ℂ →ₗ[ℂ]
      Matrix ((O.tensorPower n).prod Y).basis ((O.tensorPower n).prod Y).basis ℂ)
    (o₀ : ((O.tensorPower n).prod Y).basis)
    (hΛ : CPTPKraus.CompletelyPositive Λ) (hTNI : CPTPKraus.TraceNonincreasing Λ)
    (ν : Matrix ((C.tensorPower n).prod X).basis ((C.tensorPower n).prod X).basis ℂ)
    (Q : Matrix ((D.tensorPower n).prod Y).basis ((D.tensorPower n).prod Y).basis ℂ)
    (hν : IsDensity ν) (hQ : IsEffect Q) :
    (flaggedParallelTest Θ₁ Θ₂ n Λ o₀ hΛ hTNI ν Q hν hQ).alpha =
      1 - acceptanceProbability ((extendSidePorts (parallelPower Θ₁ n) X Y).applyLinear Λ ν) Q := by
  change 1 - acceptanceProbability
    (((extendSidePorts (parallelPower Θ₁ n) (X.prod flagSystem) (Y.prod flagSystem)).applyChannel
      (flaggedSideChannel Λ o₀ hΛ hTNI)).map
        (reindexMap (Equiv.prodAssoc (C.tensorPower n).basis X.basis (Fin 2))
          (MatrixStrategyAssembly.flagBlock ν 0)))
    (reindexMap (Equiv.prodAssoc (D.tensorPower n).basis Y.basis (Fin 2))
      (MatrixStrategyAssembly.flagBlock Q 0)) = _
  rw [flaggedSideChannel_success_acceptance]

theorem flaggedParallelTest_beta {I O C D R₁ R₂ X Y : FiniteSystem}
    (Θ₁ : FiniteSuperchannel I.basis O.basis C.basis D.basis R₁.basis)
    (Θ₂ : FiniteSuperchannel I.basis O.basis C.basis D.basis R₂.basis)
    (n : ℕ)
    (Λ : Matrix ((I.tensorPower n).prod X).basis ((I.tensorPower n).prod X).basis ℂ →ₗ[ℂ]
      Matrix ((O.tensorPower n).prod Y).basis ((O.tensorPower n).prod Y).basis ℂ)
    (o₀ : ((O.tensorPower n).prod Y).basis)
    (hΛ : CPTPKraus.CompletelyPositive Λ) (hTNI : CPTPKraus.TraceNonincreasing Λ)
    (ν : Matrix ((C.tensorPower n).prod X).basis ((C.tensorPower n).prod X).basis ℂ)
    (Q : Matrix ((D.tensorPower n).prod Y).basis ((D.tensorPower n).prod Y).basis ℂ)
    (hν : IsDensity ν) (hQ : IsEffect Q) :
    (flaggedParallelTest Θ₁ Θ₂ n Λ o₀ hΛ hTNI ν Q hν hQ).beta =
      acceptanceProbability ((extendSidePorts (parallelPower Θ₂ n) X Y).applyLinear Λ ν) Q := by
  change acceptanceProbability
    (((extendSidePorts (parallelPower Θ₂ n) (X.prod flagSystem) (Y.prod flagSystem)).applyChannel
      (flaggedSideChannel Λ o₀ hΛ hTNI)).map
        (reindexMap (Equiv.prodAssoc (C.tensorPower n).basis X.basis (Fin 2))
          (MatrixStrategyAssembly.flagBlock ν 0)))
    (reindexMap (Equiv.prodAssoc (D.tensorPower n).basis Y.basis (Fin 2))
      (MatrixStrategyAssembly.flagBlock Q 0)) = _
  rw [flaggedSideChannel_success_acceptance]

section WrapperErrors

variable {I O C D R : Type*} [Fintype I] [Fintype O] [Fintype C] [Fintype D] [Fintype R]
  [DecidableEq I] [DecidableEq O] [DecidableEq C] [DecidableEq D] [DecidableEq R]

def rightReferencePre (Γ : FiniteSuperchannel I O C D R) : FiniteCPTP C (I × R) :=
  composeChannel (reindexChannel (Equiv.prodComm R I)) Γ.pre

def rightReferencePost (Γ : FiniteSuperchannel I O C D R) : FiniteCPTP (O × R) D :=
  composeChannel Γ.post (reindexChannel (Equiv.prodComm O R))

theorem superchannel_linear_error_le (Γ : FiniteSuperchannel I O C D R)
    (Φ Ψ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ)
    (hΦ : CPTPKraus.CompletelyPositive Φ) (hΨ : CPTPKraus.CompletelyPositive Ψ)
    {ν : Matrix C C ℂ} (hν : IsDensity ν) {δ : ℝ}
    (hδ : DiamondControl.diamondBudget (Φ - Ψ) ≤ (δ : EReal)) :
    EffectPerturbation.traceNorm (Γ.applyLinear Φ ν - Γ.applyLinear Ψ ν) ≤ δ := by
  change EffectPerturbation.traceNorm
    ((rightReferencePost Γ).map (amplifyMap Φ R ((rightReferencePre Γ).map ν)) -
      (rightReferencePost Γ).map (amplifyMap Ψ R ((rightReferencePre Γ).map ν))) ≤ δ
  exact DiamondControl.common_wrapper_output_error_le Φ Ψ R
    (rightReferencePre Γ).map (rightReferencePost Γ).map hΦ hΨ
    (fun A hA => completelyPositive_positive (rightReferencePre Γ).completelyPositive hA)
    (rightReferencePre Γ).tracePreserving
    (fun A hA => completelyPositive_positive (rightReferencePost Γ).completelyPositive hA)
    (rightReferencePost Γ).tracePreserving hδ hν

theorem superchannel_acceptance_lower_bound (Γ : FiniteSuperchannel I O C D R)
    (Λ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) (hΛ : CPTPKraus.CompletelyPositive Λ)
    (N : FiniteCPTP I O) {ν ρ : Matrix C C ℂ} (hν : IsDensity ν) (hρ : IsDensity ρ)
    {Q : Matrix D D ℂ} (hQ : IsEffect Q) {δ η : ℝ}
    (hδ : DiamondControl.diamondBudget (N.map - Λ) ≤ (δ : EReal))
    (hη : EffectPerturbation.traceNorm (ν - ρ) ≤ η) :
    acceptanceProbability ((Γ.applyChannel N).map ρ) Q - δ - (1 / 2) * η ≤
      acceptanceProbability (Γ.applyLinear Λ ν) Q := by
  have hflip : DiamondControl.diamondBudget (Λ - N.map) ≤ (δ : EReal) := by
    rw [DiamondControl.diamondBudget_difference_symm Λ N.map]
    exact hδ
  have herr := superchannel_linear_error_le Γ Λ N.map hΛ N.completelyPositive hν hflip
  exact EffectPerturbation.acceptance_lower_bound_of_input_and_output_errors
    (Γ.applyChannel N).map
    (fun A hA => completelyPositive_positive (Γ.applyChannel N).completelyPositive hA)
    (Γ.applyChannel N).tracePreserving hQ
    (completelyPositive_positive (superchannel_completelyPositive Γ hΛ) hν.1).isHermitian
    hν hρ herr hη

end WrapperErrors

section ParallelErrorBounds

variable {I O C D R₁ R₂ X Y : FiniteSystem}
  (Θ₁ : FiniteSuperchannel I.basis O.basis C.basis D.basis R₁.basis)
  (Θ₂ : FiniteSuperchannel I.basis O.basis C.basis D.basis R₂.basis)
  (n : ℕ)
  (Λ : Matrix ((I.tensorPower n).prod X).basis ((I.tensorPower n).prod X).basis ℂ →ₗ[ℂ]
    Matrix ((O.tensorPower n).prod Y).basis ((O.tensorPower n).prod Y).basis ℂ)
  (o₀ : ((O.tensorPower n).prod Y).basis)
  (hΛ : CPTPKraus.CompletelyPositive Λ) (hTNI : CPTPKraus.TraceNonincreasing Λ)
  {ν ρ σ : Matrix ((C.tensorPower n).prod X).basis ((C.tensorPower n).prod X).basis ℂ}
  {Q : Matrix ((D.tensorPower n).prod Y).basis ((D.tensorPower n).prod Y).basis ℂ}
  (hν : IsDensity ν) (hQ : IsEffect Q)

theorem flaggedParallelTest_alpha_le
    (N : FiniteCPTP ((I.tensorPower n).prod X).basis ((O.tensorPower n).prod Y).basis)
    (hρ : IsDensity ρ) {δ η : ℝ}
    (hδ : DiamondControl.diamondBudget (N.map - Λ) ≤ (δ : EReal))
    (hη : EffectPerturbation.traceNorm (ν - ρ) ≤ η) :
    (flaggedParallelTest Θ₁ Θ₂ n Λ o₀ hΛ hTNI ν Q hν hQ).alpha ≤
      1 - acceptanceProbability ((parallelChannel Θ₁ n X Y N).map ρ) Q + δ + (1 / 2) * η := by
  rw [flaggedParallelTest_alpha]
  have hb := superchannel_acceptance_lower_bound (extendSidePorts (parallelPower Θ₁ n) X Y)
    Λ hΛ N hν hρ hQ hδ hη
  change acceptanceProbability ((parallelChannel Θ₁ n X Y N).map ρ) Q - δ - (1 / 2) * η ≤
    acceptanceProbability ((extendSidePorts (parallelPower Θ₁ n) X Y).applyLinear Λ ν) Q at hb
  linarith

theorem flaggedParallelTest_beta_le
    (M : FiniteCPTP ((I.tensorPower n).prod X).basis ((O.tensorPower n).prod Y).basis)
    {b c : ℝ} (hdom : CPTPKraus.CPDom Λ M.map c) (hb : 0 ≤ b)
    (hσ : σ.PosSemidef) (horder : ((b : ℂ) • σ - ν).PosSemidef) :
    (flaggedParallelTest Θ₁ Θ₂ n Λ o₀ hΛ hTNI ν Q hν hQ).beta ≤
      (b * c) * acceptanceProbability ((parallelChannel Θ₂ n X Y M).map σ) Q := by
  rw [flaggedParallelTest_beta]
  exact cpDom_superchannel_state_acceptance (extendSidePorts (parallelPower Θ₂ n) X Y)
    hΛ hdom hb hσ horder hQ.1

theorem flaggedParallelTest_beta_le_dyadic
    (M : FiniteCPTP ((I.tensorPower n).prod X).basis ((O.tensorPower n).prod Y).basis)
    (a b r : ℝ)
    (hdom : CPTPKraus.CPDom Λ M.map ((2 : ℝ) ^ ((n : ℝ) * a)))
    (hσ : σ.PosSemidef)
    (horder : (((Real.rpow (2 : ℝ) ((n : ℝ) * b)) : ℂ) • σ - ν).PosSemidef)
    (hβ : acceptanceProbability ((parallelChannel Θ₂ n X Y M).map σ) Q ≤
      (2 : ℝ) ^ (-(n : ℝ) * r)) :
    (flaggedParallelTest Θ₁ Θ₂ n Λ o₀ hΛ hTNI ν Q hν hQ).beta ≤
      (2 : ℝ) ^ (-(n : ℝ) * (r - a - b)) := by
  have hc : (flaggedParallelTest Θ₁ Θ₂ n Λ o₀ hΛ hTNI ν Q hν hQ).beta ≤
      ((2 : ℝ) ^ ((n : ℝ) * b) * (2 : ℝ) ^ ((n : ℝ) * a)) *
        acceptanceProbability ((parallelChannel Θ₂ n X Y M).map σ) Q :=
    flaggedParallelTest_beta_le (X := X) (Y := Y) (ν := ν) (σ := σ) (Q := Q)
      (b := (2 : ℝ) ^ ((n : ℝ) * b)) (c := (2 : ℝ) ^ ((n : ℝ) * a))
      Θ₁ Θ₂ n Λ o₀ hΛ hTNI hν hQ M hdom
      (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _) hσ horder
  calc
    _ ≤ ((2 : ℝ) ^ ((n : ℝ) * b) * (2 : ℝ) ^ ((n : ℝ) * a)) *
        (2 : ℝ) ^ (-(n : ℝ) * r) :=
      hc.trans (mul_le_mul_of_nonneg_left hβ (by positivity))
    _ = _ := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
        ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      congr 1
      ring

end ParallelErrorBounds

theorem groupedSidePower_slot_matrix_intertwine {I O X Y : FiniteSystem}
    (Φ : FiniteCPTP (I.prod X).basis (O.prod Y).basis) (n : ℕ)
    (A : Matrix ((I.prod X).tensorPower n).basis ((I.prod X).tensorPower n).basis ℂ) :
    (groupedSidePower Φ n).map (reindexMap (matrixPowerPairIndex I X n) A) =
      reindexMap (matrixPowerPairIndex O Y n) ((matrixChannelPower Φ n).map A) := by
  induction n with
  | zero =>
      ext ⟨o, y⟩ ⟨p, z⟩
      cases o
      cases y
      cases p
      cases z
      rfl
  | succ n ih =>
      have hm : (groupedSidePower Φ (n + 1)).map.comp
          (reindexMap (matrixPowerPairIndex I X (n + 1))) =
        (reindexMap (matrixPowerPairIndex O Y (n + 1))).comp (matrixChannelPower Φ (n + 1)).map := by
        apply matrixMap_ext_units
        intro ⟨i, is⟩ ⟨j, js⟩
        have hs : Matrix.single (i, is) (j, js) (1 : ℂ) =
            Matrix.single i j 1 ⊗ₖ Matrix.single is js 1 := by
          rw [Matrix.single_kronecker_single, one_mul]
        simp only [LinearMap.comp_apply]
        rw [hs]
        change reindexMap (pairShuffle O.basis Y.basis (O.tensorPower n).basis (Y.tensorPower n).basis)
          ((productChannel Φ (groupedSidePower Φ n)).map
            (reindexMap (pairShuffle I.basis X.basis (I.tensorPower n).basis (X.tensorPower n).basis).symm
              (reindexMap (pairShuffle I.basis X.basis (I.tensorPower n).basis (X.tensorPower n).basis)
                (Matrix.single i j 1 ⊗ₖ reindexMap (matrixPowerPairIndex I X n) (Matrix.single is js 1))))) = _
        rw [reindexMap_cancel_matrix, productChannel_kronecker]
        erw [ih]
        have hp : (matrixChannelPower Φ (n + 1)).map
            (Matrix.single i j 1 ⊗ₖ Matrix.single is js 1) =
          Φ.map (Matrix.single i j 1) ⊗ₖ (matrixChannelPower Φ n).map (Matrix.single is js 1) :=
            productChannel_kronecker _ _ _ _
        rw [hp]
        rfl
      exact congrArg (fun F => F A) hm

theorem groupedSidePower_slot_intertwine {I O X Y : FiniteSystem}
    (Φ : FiniteCPTP (I.prod X).basis (O.prod Y).basis) (n : ℕ)
    (A : Matrix (TensorIndex (I.prod X).basis n) (TensorIndex (I.prod X).basis n) ℂ) :
    (groupedSidePower Φ n).map (reindexMap (repeatedPortsIndex I X n) A) =
      reindexMap (repeatedPortsIndex O Y n) ((channelPower Φ n).map A) := by
  change (groupedSidePower Φ n).map
    (reindexMap (matrixPowerPairIndex I X n) (reindexMap (frontTailIndex (I.prod X) n).symm A)) =
    reindexMap (matrixPowerPairIndex O Y n)
      (reindexMap (frontTailIndex (O.prod Y) n).symm ((channelPower Φ n).map A))
  rw [groupedSidePower_slot_matrix_intertwine]
  have ht := matrixChannelPower_intertwine Φ n (reindexMap (frontTailIndex (I.prod X) n).symm A)
  have hi : reindexMap (frontTailIndex (I.prod X) n)
      (reindexMap (frontTailIndex (I.prod X) n).symm A) = A := by
    ext i j
    simp [reindexMap, Matrix.reindex_apply, Matrix.submatrix_apply]
  rw [hi] at ht
  have ho := congrArg (reindexMap (frontTailIndex (O.prod Y) n).symm) ht
  erw [reindexMap_cancel_matrix] at ho
  exact congrArg (reindexMap (matrixPowerPairIndex O Y n)) ho

end QuantumProver.SuperchannelDiscrimination.MatrixFlaggedTesting

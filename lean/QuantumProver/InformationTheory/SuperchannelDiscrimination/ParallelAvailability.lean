import QuantumProver.InformationTheory.SuperchannelDiscrimination.ParallelStack
import QuantumProver.InformationTheory.SuperchannelDiscrimination.DiamondControl

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix Kronecker

namespace QuantumProver.SuperchannelDiscrimination.MatrixParallelAvailability

open FlaggedStates KrausCompletion CPWrappers
open MatrixStrategyAssembly.MatrixStrategies

variable {I O C D R₁ R₂ : FiniteSystem}

def basisResetChannel {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (b₀ : B) : FiniteCPTP A B where
  map := krausMap (resetKraus b₀ (1 : Matrix A A ℂ))
  completelyPositive r X hX := krausMap_completelyPositive _ (Fin r) hX
  tracePreserving X := krausAction_tracePreserving _
    (by rw [resetKraus_gram]; simp) X

theorem basisResetChannel_map {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (b₀ : B) (X : Matrix A A ℂ) :
    (basisResetChannel b₀).map X = X.trace • Matrix.single b₀ b₀ (1 : ℂ) := by
  change krausAction (resetKraus b₀ (1 : Matrix A A ℂ)) X = _
  rw [resetKraus_action]
  simp

theorem physicalBinaryTest_one {A B : FiniteSystem}
    (K₁ K₂ : FiniteCPTP A.basis B.basis)
    (ρ : Matrix A.basis A.basis ℂ) (hρ : IsDensity ρ) :
    physicalBinaryTest K₁ K₂ ρ 1 hρ
      ⟨Matrix.PosSemidef.one, by rw [sub_self]; exact Matrix.PosSemidef.zero⟩ = acceptAll := by
  unfold physicalBinaryTest acceptAll
  simp [acceptanceProbability, K₁.tracePreserving, K₂.tracePreserving, hρ.2]

theorem parallelBinaryTest_one
    (Θ₁ : FiniteSuperchannel I.basis O.basis C.basis D.basis R₁.basis)
    (Θ₂ : FiniteSuperchannel I.basis O.basis C.basis D.basis R₂.basis)
    (n : ℕ) (X Y : FiniteSystem)
    (K : FiniteCPTP ((I.tensorPower n).prod X).basis ((O.tensorPower n).prod Y).basis)
    (ρ : Matrix ((C.tensorPower n).prod X).basis ((C.tensorPower n).prod X).basis ℂ)
    (hρ : IsDensity ρ) :
    parallelBinaryTest Θ₁ Θ₂ n X Y K ρ 1 hρ
      ⟨Matrix.PosSemidef.one, by rw [sub_self]; exact Matrix.PosSemidef.zero⟩ = acceptAll :=
  physicalBinaryTest_one _ _ ρ hρ

theorem matrix_parallel_hasAcceptAll
    (Θ₁ : FiniteSuperchannel I.basis O.basis C.basis D.basis R₁.basis)
    (Θ₂ : FiniteSuperchannel I.basis O.basis C.basis D.basis R₂.basis) :
    HasAcceptAll (parallelStrategyFamily Θ₁ Θ₂) := by
  classical
  intro n
  let o₀ : ((O.tensorPower n).prod FiniteSystem.unit).basis := Classical.choice inferInstance
  let c₀ : ((C.tensorPower n).prod FiniteSystem.unit).basis := Classical.choice inferInstance
  let K : FiniteCPTP ((I.tensorPower n).prod FiniteSystem.unit).basis
      ((O.tensorPower n).prod FiniteSystem.unit).basis := basisResetChannel o₀
  let ρ : Matrix ((C.tensorPower n).prod FiniteSystem.unit).basis
      ((C.tensorPower n).prod FiniteSystem.unit).basis ℂ := Matrix.single c₀ c₀ 1
  have hρ : IsDensity ρ := ChannelRegularization.single_isDensity c₀
  have hE : IsEffect (1 : Matrix ((D.tensorPower n).prod FiniteSystem.unit).basis
      ((D.tensorPower n).prod FiniteSystem.unit).basis ℂ) :=
    ⟨Matrix.PosSemidef.one, by rw [sub_self]; exact Matrix.PosSemidef.zero⟩
  refine ⟨FiniteSystem.unit, FiniteSystem.unit, K, ρ, 1, hρ, hE, ?_⟩
  exact (parallelBinaryTest_one Θ₁ Θ₂ n FiniteSystem.unit FiniteSystem.unit K ρ hρ).symm

theorem matrix_parallel_orderedSteinExponent_nonneg
    (Θ₁ : FiniteSuperchannel I.basis O.basis C.basis D.basis R₁.basis)
    (Θ₂ : FiniteSuperchannel I.basis O.basis C.basis D.basis R₂.basis) :
    0 ≤ orderedSteinExponent (parallelStrategyFamily Θ₁ Θ₂) :=
  orderedSteinExponent_nonneg (matrix_parallel_hasAcceptAll Θ₁ Θ₂)

theorem matrix_parallel_orderedSteinExponent_ne_bot
    (Θ₁ : FiniteSuperchannel I.basis O.basis C.basis D.basis R₁.basis)
    (Θ₂ : FiniteSuperchannel I.basis O.basis C.basis D.basis R₂.basis) :
    orderedSteinExponent (parallelStrategyFamily Θ₁ Θ₂) ≠ ⊥ :=
  ne_of_gt (EReal.bot_lt_zero.trans_le (matrix_parallel_orderedSteinExponent_nonneg Θ₁ Θ₂))

end QuantumProver.SuperchannelDiscrimination.MatrixParallelAvailability

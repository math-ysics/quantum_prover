import QuantumProver.InformationTheory.WernerEndpoint.VariableStateProtocol
import QuantumProver.InformationTheory.WernerEndpoint.VariableReferenceMeasure

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

namespace QuantumProver.WernerEndpoint.MatrixVariableFiniteBaseProtocol

open OperationalEndpointCost MatrixVariableStateProtocol MeasureTheory Filter
open QuantumProver.SuperchannelDiscrimination
open scoped BigOperators ComplexOrder MatrixOrder Matrix Kronecker
  Matrix.Norms.L2Operator Topology

universe u

def GeneralRegular {c d : ℕ} : {a b height : ℕ} → Tree.{u} c d a b height → Prop
  | _, _, _, .finite _ _ => True
  | a, b, _, .alice _ mΩ μ p K child =>
      letI := mΩ
      Measurable (fun x => (⟨p x, (K x, channel (child x))⟩ : Sigma (AliceFiber c d a b))) ∧
        (∫ x, (K x).conjTranspose * K x ∂μ) = 1 ∧ ∀ x, GeneralRegular (child x)
  | a, b, _, .bob _ mΩ μ p K child =>
      letI := mΩ
      Measurable (fun x => (⟨p x, (K x, channel (child x))⟩ : Sigma (BobFiber c d a b))) ∧
        (∫ x, (K x).conjTranspose * K x ∂μ) = 1 ∧ ∀ x, GeneralRegular (child x)

@[simp] theorem generalRegular_finite {c d a b : ℕ} (height : ℕ)
    (T : MatrixCPProtocol.FiniteCPProtocol c d a b) :
    GeneralRegular (Tree.finite.{u} height T) := trivial

theorem regular_implies_generalRegular {c d a b height : ℕ}
    (T : Tree.{u} c d a b height) (hT : Regular T) : GeneralRegular T := by
  classical
  revert hT
  induction T with
  | finite height U =>
      intro _
      trivial
  | alice Ω mΩ μ p K child ih =>
      let := mΩ
      rintro ⟨_, hPacked, hComplete, hChild⟩
      exact ⟨hPacked, hComplete, fun x => ih x (hChild x)⟩
  | bob Ω mΩ μ p K child ih =>
      let := mΩ
      rintro ⟨_, hPacked, hComplete, hChild⟩
      exact ⟨hPacked, hComplete, fun x => ih x (hChild x)⟩

private theorem physical_alice_moments {Ω : Type*} [MeasurableSpace Ω]
    {c d a b : ℕ} (μ : Measure Ω) (p : Ω → ℕ)
    (K : ∀ x, Matrix (Fin (p x)) (Fin a) ℂ) (Φ : ∀ x, Channel c d (p x) b)
    (hPacked : Measurable (fun x => (⟨p x, (K x, Φ x)⟩ : Sigma (AliceFiber c d a b))))
    (hComplete : (∫ x, (K x).conjTranspose * K x ∂μ) = 1)
    (hCP : ∀ x, CPTPKraus.CompletelyPositive (Φ x).toLinearMap)
    (hTP : ∀ x, CPTPKraus.TracePreserving (Φ x).toLinearMap) :
    Integrable (fun x => (K x).conjTranspose * K x) μ ∧
      Integrable (fun x => (Φ x).comp (LocalChannelMoments.leftSandwichCLM (K x))) μ := by
  have hGram := MatrixVariableReferenceMeasure.integrable_gram_of_complete μ p K hComplete
  exact ⟨hGram, MatrixVariableReferenceMeasure.integrable_left_moment_of_cptp
    μ p K Φ hPacked hCP hTP hGram⟩

private theorem physical_bob_moments {Ω : Type*} [MeasurableSpace Ω]
    {c d a b : ℕ} (μ : Measure Ω) (p : Ω → ℕ)
    (K : ∀ x, Matrix (Fin (p x)) (Fin b) ℂ) (Φ : ∀ x, Channel c d a (p x))
    (hPacked : Measurable (fun x => (⟨p x, (K x, Φ x)⟩ : Sigma (BobFiber c d a b))))
    (hComplete : (∫ x, (K x).conjTranspose * K x ∂μ) = 1)
    (hCP : ∀ x, CPTPKraus.CompletelyPositive (Φ x).toLinearMap)
    (hTP : ∀ x, CPTPKraus.TracePreserving (Φ x).toLinearMap) :
    Integrable (fun x => (K x).conjTranspose * K x) μ ∧
      Integrable (fun x => (Φ x).comp (LocalChannelMoments.rightSandwichCLM (K x))) μ := by
  have hGram := MatrixVariableReferenceMeasure.integrable_gram_of_complete μ p K hComplete
  exact ⟨hGram, MatrixVariableReferenceMeasure.integrable_right_moment_of_cptp
    μ p K Φ hPacked hCP hTP hGram⟩

def toFiniteBase {c d : ℕ} : {a b height : ℕ} →
    Tree.{u} c d a b height → Tree.{u} c d a b height
  | _, _, _, .finite height T => .finite height T
  | _, _, _, .alice Ω mΩ μ p K child =>
      letI := mΩ
      .alice Ω mΩ (MatrixVariableReferenceMeasure.referenceMeasure μ p K) p
        (fun x => FiniteReferenceMeasure.rescaledKraus (K x))
        (fun x => toFiniteBase (child x))
  | _, _, _, .bob Ω mΩ μ p K child =>
      letI := mΩ
      .bob Ω mΩ (MatrixVariableReferenceMeasure.referenceMeasure μ p K) p
        (fun x => FiniteReferenceMeasure.rescaledKraus (K x))
        (fun x => toFiniteBase (child x))

@[simp] theorem toFiniteBase_finite {c d a b : ℕ} (height : ℕ)
    (T : MatrixCPProtocol.FiniteCPProtocol c d a b) :
    toFiniteBase (Tree.finite.{u} height T) = Tree.finite height T := rfl

theorem toFiniteBase_spec {c d a b height : ℕ}
    (T : Tree.{u} c d a b height) (hT : GeneralRegular T) (hc : 0 < c) (hd : 0 < d) :
    Regular (toFiniteBase T) ∧ channel (toFiniteBase T) = channel T ∧ IntegrableMoments T := by
  classical
  revert hT
  induction T with
  | finite height U =>
      intro _
      exact ⟨trivial, rfl, trivial⟩
  | @alice a b height Ω mΩ μ p K child ih =>
      let := mΩ
      intro hT
      rcases hT with ⟨hPacked, hComplete, hChild⟩
      have hIH := fun x => ih x (hChild x)
      have hChildPhysical (x : Ω) :
          CPTPKraus.CompletelyPositive (channel (child x)).toLinearMap ∧
            CPTPKraus.TracePreserving (channel (child x)).toLinearMap := by
        rw [← (hIH x).2.1]
        exact channel_cptp (toFiniteBase (child x)) (hIH x).1 hc hd
      obtain ⟨hGram, hMoment⟩ := physical_alice_moments μ p K (fun x => channel (child x))
        hPacked hComplete (fun x => (hChildPhysical x).1) (fun x => (hChildPhysical x).2)
      have hWeight : Measurable (fun x => FiniteReferenceMeasure.gramTraceWeight (K x)) := by
        exact (MatrixVariableReferenceMeasure.measurable_packedWeight
          a (fun r => Channel c d r b)).comp hPacked
      have hFinite := MatrixVariableReferenceMeasure.referenceMeasure_isFinite μ p K hGram hComplete
      have hRescaledComplete := MatrixVariableReferenceMeasure.rescaledGram_complete μ p K hWeight hComplete
      have hScaledPacked : Measurable (fun x =>
          (⟨p x, (FiniteReferenceMeasure.rescaledKraus (K x), channel (child x))⟩ :
            Sigma (AliceFiber c d a b))) :=
        (MatrixVariableReferenceMeasure.measurable_rescalePacked
          a (fun r => Channel c d r b)).comp hPacked
      have hConvertedPacked : Measurable (fun x =>
          (⟨p x, (FiniteReferenceMeasure.rescaledKraus (K x), channel (toFiniteBase (child x)))⟩ :
            Sigma (AliceFiber c d a b))) := by
        convert hScaledPacked using 1
        funext x
        rw [(hIH x).2.1]
      refine ⟨⟨hFinite, hConvertedPacked, hRescaledComplete, fun x => (hIH x).1⟩, ?_,
        ⟨hGram, hMoment, fun x => (hIH x).2.2⟩⟩
      change (∫ x, (channel (toFiniteBase (child x))).comp
          (LocalChannelMoments.leftSandwichCLM (FiniteReferenceMeasure.rescaledKraus (K x)))
          ∂MatrixVariableReferenceMeasure.referenceMeasure μ p K) =
        ∫ x, (channel (child x)).comp (LocalChannelMoments.leftSandwichCLM (K x)) ∂μ
      calc
        _ = ∫ x, (channel (child x)).comp
            (LocalChannelMoments.leftSandwichCLM (FiniteReferenceMeasure.rescaledKraus (K x)))
            ∂MatrixVariableReferenceMeasure.referenceMeasure μ p K := by
          apply integral_congr_ae
          exact Eventually.of_forall fun x => by
            dsimp only
            rw [(hIH x).2.1]
        _ = _ := MatrixVariableReferenceMeasure.integral_left_moment_rescaled
          μ p K (fun x => channel (child x)) hWeight
  | @bob a b height Ω mΩ μ p K child ih =>
      let := mΩ
      intro hT
      rcases hT with ⟨hPacked, hComplete, hChild⟩
      have hIH := fun x => ih x (hChild x)
      have hChildPhysical (x : Ω) :
          CPTPKraus.CompletelyPositive (channel (child x)).toLinearMap ∧
            CPTPKraus.TracePreserving (channel (child x)).toLinearMap := by
        rw [← (hIH x).2.1]
        exact channel_cptp (toFiniteBase (child x)) (hIH x).1 hc hd
      obtain ⟨hGram, hMoment⟩ := physical_bob_moments μ p K (fun x => channel (child x))
        hPacked hComplete (fun x => (hChildPhysical x).1) (fun x => (hChildPhysical x).2)
      have hWeight : Measurable (fun x => FiniteReferenceMeasure.gramTraceWeight (K x)) := by
        exact (MatrixVariableReferenceMeasure.measurable_packedWeight
          b (fun r => Channel c d a r)).comp hPacked
      have hFinite := MatrixVariableReferenceMeasure.referenceMeasure_isFinite μ p K hGram hComplete
      have hRescaledComplete := MatrixVariableReferenceMeasure.rescaledGram_complete μ p K hWeight hComplete
      have hScaledPacked : Measurable (fun x =>
          (⟨p x, (FiniteReferenceMeasure.rescaledKraus (K x), channel (child x))⟩ :
            Sigma (BobFiber c d a b))) :=
        (MatrixVariableReferenceMeasure.measurable_rescalePacked
          b (fun r => Channel c d a r)).comp hPacked
      have hConvertedPacked : Measurable (fun x =>
          (⟨p x, (FiniteReferenceMeasure.rescaledKraus (K x), channel (toFiniteBase (child x)))⟩ :
            Sigma (BobFiber c d a b))) := by
        convert hScaledPacked using 1
        funext x
        rw [(hIH x).2.1]
      refine ⟨⟨hFinite, hConvertedPacked, hRescaledComplete, fun x => (hIH x).1⟩, ?_,
        ⟨hGram, hMoment, fun x => (hIH x).2.2⟩⟩
      change (∫ x, (channel (toFiniteBase (child x))).comp
          (LocalChannelMoments.rightSandwichCLM (FiniteReferenceMeasure.rescaledKraus (K x)))
          ∂MatrixVariableReferenceMeasure.referenceMeasure μ p K) =
        ∫ x, (channel (child x)).comp (LocalChannelMoments.rightSandwichCLM (K x)) ∂μ
      calc
        _ = ∫ x, (channel (child x)).comp
            (LocalChannelMoments.rightSandwichCLM (FiniteReferenceMeasure.rescaledKraus (K x)))
            ∂MatrixVariableReferenceMeasure.referenceMeasure μ p K := by
          apply integral_congr_ae
          exact Eventually.of_forall fun x => by
            dsimp only
            rw [(hIH x).2.1]
        _ = _ := MatrixVariableReferenceMeasure.integral_right_moment_rescaled
          μ p K (fun x => channel (child x)) hWeight

theorem toFiniteBase_regular {c d a b height : ℕ}
    (T : Tree.{u} c d a b height) (hT : GeneralRegular T) (hc : 0 < c) (hd : 0 < d) :
    Regular (toFiniteBase T) := (toFiniteBase_spec T hT hc hd).1

theorem toFiniteBase_channel {c d a b height : ℕ}
    (T : Tree.{u} c d a b height) (hT : GeneralRegular T) (hc : 0 < c) (hd : 0 < d) :
    channel (toFiniteBase T) = channel T := (toFiniteBase_spec T hT hc hd).2.1

theorem integrableMoments_of_generalRegular {c d a b height : ℕ}
    (T : Tree.{u} c d a b height) (hT : GeneralRegular T) (hc : 0 < c) (hd : 0 < d) :
    IntegrableMoments T := (toFiniteBase_spec T hT hc hd).2.2

theorem channel_cptp_of_generalRegular {c d a b height : ℕ}
    (T : Tree.{u} c d a b height) (hT : GeneralRegular T) (hc : 0 < c) (hd : 0 < d) :
    CPTPKraus.CompletelyPositive (channel T).toLinearMap ∧
      CPTPKraus.TracePreserving (channel T).toLinearMap := by
  rw [← toFiniteBase_channel T hT hc hd]
  exact channel_cptp (toFiniteBase T) (toFiniteBase_regular T hT hc hd) hc hd

theorem exists_finiteProtocol_channel_approx_of_generalRegular {c d a b height : ℕ}
    (T : Tree.{u} c d a b height) (hT : GeneralRegular T) (hc : 0 < c) (hd : 0 < d)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ U : FiniteLocalProtocol c d a b, ‖MatrixContinuousStateProtocol.finiteChannel U - channel T‖ < ε := by
  obtain ⟨U, hU⟩ := exists_finiteProtocol_channel_approx
    (toFiniteBase T) (toFiniteBase_regular T hT hc hd) hc hd ε hε
  rw [toFiniteBase_channel T hT hc hd] at hU
  exact ⟨U, hU⟩

theorem exists_finiteProtocol_output_approx_of_generalRegular {c d a b height : ℕ}
    (T : Tree.{u} c d a b height) (hT : GeneralRegular T) (hc : 0 < c) (hd : 0 < d)
    (ρ : JointMatrix a b) (ε : ℝ) (hε : 0 < ε) :
    ∃ U : FiniteLocalProtocol c d a b, ‖U.apply ρ - channel T ρ‖ < ε := by
  obtain ⟨U, hU⟩ := exists_finiteProtocol_output_approx
    (toFiniteBase T) (toFiniteBase_regular T hT hc hd) hc hd ρ ε hε
  rw [toFiniteBase_channel T hT hc hd] at hU
  exact ⟨U, hU⟩

theorem channel_pureOutput_mem_outputClosure_of_generalRegular {c d a b height : ℕ}
    (T : Tree.{u} c d a b height) (hT : GeneralRegular T) (hc : 0 < c) (hd : 0 < d)
    (ψ : Fin a × Fin b → ℂ) :
    channel T (pureDensity ψ) ∈ EndpointProtocolClosure.outputClosure ψ := by
  have h := channel_pureOutput_mem_outputClosure
    (toFiniteBase T) (toFiniteBase_regular T hT hc hd) hc hd ψ
  rwa [toFiniteBase_channel T hT hc hd] at h

theorem channel_pureOutput_isDensity_of_generalRegular {c d a b height : ℕ}
    (T : Tree.{u} c d a b height) (hT : GeneralRegular T) (hc : 0 < c) (hd : 0 < d)
    (ψ : Fin a × Fin b → ℂ) (hψ : vectorNormSq ψ = 1) :
    (channel T (pureDensity ψ)).PosSemidef ∧ (channel T (pureDensity ψ)).trace = 1 := by
  have h := channel_pureOutput_isDensity
    (toFiniteBase T) (toFiniteBase_regular T hT hc hd) hc hd ψ hψ
  rwa [toFiniteBase_channel T hT hc hd] at h

end QuantumProver.WernerEndpoint.MatrixVariableFiniteBaseProtocol

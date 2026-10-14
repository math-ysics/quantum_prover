import QuantumProver.InformationTheory.ElegantJointMeasurement.NormalProcess

noncomputable section
set_option autoImplicit false

namespace QuantumProver.ElegantJointMeasurement.HilbertCommonPhysicalEventTensor

open QuantumProver.ElegantJointMeasurement.NormalProcess QuantumProver.ElegantJointMeasurement.NormalInstrumentAbsorption
open QuantumProver.ElegantJointMeasurement.NormalCompleteContraction (TraceNonincreasing)
open QuantumProver.MatrixNormalTensorExtension QuantumProver.MatrixNormalTensorInstrument
open QuantumProver.MatrixNormalRightTensor

private theorem extendLeft_congr (Φ Ψ : NormalOperation Workspace Workspace)
    (hΦCP : NormalCompletelyPositive Φ) (hΨCP : NormalCompletelyPositive Ψ)
    (hΦT : TraceNonincreasing Φ) (hΨT : TraceNonincreasing Ψ) (hΦΨ : Φ = Ψ) :
    extendLeft (G := Workspace) Φ hΦCP hΦT =
      extendLeft (G := Workspace) Ψ hΨCP hΨT := by
  cases hΦΨ
  rfl

private theorem extendRight_congr (Φ Ψ : NormalOperation Workspace Workspace)
    (hΦCP : NormalCompletelyPositive Φ) (hΨCP : NormalCompletelyPositive Ψ)
    (hΦT : TraceNonincreasing Φ) (hΨT : TraceNonincreasing Ψ) (hΦΨ : Φ = Ψ) :
    extendRight (G := Workspace) Φ hΦCP hΦT =
      extendRight (G := Workspace) Ψ hΨCP hΨT := by
  cases hΦΨ
  rfl

theorem left_event_transport {H K S T : Type*}
    [MeasurableSpace H] [MeasurableSpace K] [MeasurableSpace S] [MeasurableSpace T]
    (A : Instrument Workspace Workspace H S) (B : Instrument Workspace Workspace K T)
    (h : H) (k : K) (s : Set S) (t : Set T) (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hAB : A.operation h s = B.operation k t) :
    (tensorInstrument (G := Workspace) A).operation h s =
      (tensorInstrument (G := Workspace) B).operation k t := by
  rw [tensorInstrument_operation, tensorInstrument_operation,
    tensorOperation_of_measurable A h s hs, tensorOperation_of_measurable B k t ht]
  exact extendLeft_congr _ _ _ _ _ _ hAB

theorem right_event_transport {H K S T : Type*}
    [MeasurableSpace H] [MeasurableSpace K] [MeasurableSpace S] [MeasurableSpace T]
    (A : Instrument Workspace Workspace H S) (B : Instrument Workspace Workspace K T)
    (h : H) (k : K) (s : Set S) (t : Set T) (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hAB : A.operation h s = B.operation k t) :
    (rightTensorInstrument (G := Workspace) A).operation h s =
      (rightTensorInstrument (G := Workspace) B).operation k t := by
  rw [rightTensorInstrument_operation, rightTensorInstrument_operation,
    rightTensorOperation_of_measurable A h s hs,
    rightTensorOperation_of_measurable B k t ht]
  exact extendRight_congr _ _ _ _ _ _ hAB

end QuantumProver.ElegantJointMeasurement.HilbertCommonPhysicalEventTensor

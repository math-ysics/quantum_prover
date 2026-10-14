import QuantumProver.InformationTheory.ElegantJointMeasurement.NormalPhysicalTerminalAdmission
import QuantumProver.QuantumChannels.CommonPhysicalInstrument

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory Set Function
open scoped Classical

namespace QuantumProver.ElegantJointMeasurement.HilbertCommonPhysicalTerminalRealization

open QuantumProver.ElegantJointMeasurement.NormalInstrumentAbsorption QuantumProver.ElegantJointMeasurement.MeasurableNormalInstrument
open QuantumProver.ElegantJointMeasurement.SeparableHilbertEmbedding QuantumProver.ElegantJointMeasurement.NormalPhysicalTerminalAdmission
open QuantumProver.ElegantJointMeasurement.NormalProcess QuantumProver.ElegantJointMeasurement.HilbertSquareProcess
open QuantumProver.MatrixNormalSourceCompletion QuantumProver.MatrixCommonPhysicalInstrument

universe u v w

variable {H : Type u} [MeasurableSpace H] {K : Type v} [MeasurableSpace K]
  {Ω : Type w} [MeasurableSpace Ω] {c : ℕ}

def pullbackTerminalInstrument
    (L : Instrument CommonHilbert (FiniteOutput c) K Ω)
    (f : H → K) (hf : Measurable f) :
    Instrument CommonHilbert (FiniteOutput c) H Ω where
  operation h := L.operation (f h)
  empty h := L.empty (f h)
  countable_additivity h := L.countable_additivity (f h)
  completelyPositive h := L.completelyPositive (f h)
  measurable_coordinate s hs T x y := (L.measurable_coordinate s hs T x y).comp hf
  trace_preserving h := L.trace_preserving (f h)

@[simp] theorem pullbackTerminalInstrument_operation
    (L : Instrument CommonHilbert (FiniteOutput c) K Ω)
    (f : H → K) (hf : Measurable f) (h : H) (s : Set Ω) :
    (pullbackTerminalInstrument L f hf).operation h s = L.operation (f h) s := rfl

def rawTerminalInstrument
    (L : Instrument CommonHilbert (FiniteOutput c) K Ω)
    (f : H → K) (hf : Measurable f) :
    MatrixInstrument (commonFundamentalFamily (H := H))
      (finiteOutputFamily (H := H) c) Ω :=
  matrixInstrument (pullbackTerminalInstrument L f hf)
    (finiteOutputVector c) (finiteOutputVector_dense c)

@[simp] theorem rawTerminalInstrument_operation
    (L : Instrument CommonHilbert (FiniteOutput c) K Ω)
    (f : H → K) (hf : Measurable f) (h : H) (s : Set Ω) :
    (rawTerminalInstrument L f hf).operation h s = L.operation (f h) s :=
  matrixInstrument_operation (pullbackTerminalInstrument L f hf)
    (finiteOutputVector c) (finiteOutputVector_dense c) h s

theorem rawTerminalInstrument_fundamental_measurable
    (L : Instrument CommonHilbert (FiniteOutput c) K Ω)
    (f : H → K) (hf : Measurable f) (s : Set Ω) (hs : MeasurableSet s) :
    FundamentalCoefficientsMeasurable (commonFundamentalFamily (H := H))
      (finiteOutputFamily (H := H) c) (fun h => L.operation (f h) s) := by
  simpa only [rawTerminalInstrument_operation] using
    (rawTerminalInstrument L f hf).fundamental_measurable s hs

theorem rawTerminalInstrument_reference
    (L : Instrument CommonHilbert (FiniteOutput c) K Ω)
    (f : H → K) (hf : Measurable f) (h : H) (s : Set Ω)
    (I : Type) [Fintype I] [DecidableEq I] [Nonempty I]
    (T : QuantumProver.ElegantJointMeasurement.NuclearChoi.Nuclear (QuantumProver.ElegantJointMeasurement.HilbertChoi.BlockSpace I CommonHilbert)) :
    normalAmplification (R := I) ((rawTerminalInstrument L f hf).operation h s) T =
      normalAmplification (R := I) (L.operation (f h) s) T := by
  rw [rawTerminalInstrument_operation]

section NormalTerminal

variable {R : Type v} [MeasurableSpace R] {N d : ℕ}
  (Q : NormalTerminal R N c d) (f : H → History R N) (hf : Measurable f)

def rawTerminalAlice :
    MatrixInstrument (commonFundamentalFamily (H := H))
      (finiteOutputFamily (H := H) c) PUnit.{v+1} :=
  rawTerminalInstrument Q.alice f hf

def rawTerminalBob :
    MatrixInstrument (commonFundamentalFamily (H := H))
      (finiteOutputFamily (H := H) d) PUnit.{v+1} :=
  rawTerminalInstrument Q.bob f hf

@[simp] theorem rawTerminalAlice_operation (h : H) (s : Set PUnit.{v+1}) :
    (rawTerminalAlice Q f hf).operation h s = Q.alice.operation (f h) s :=
  rawTerminalInstrument_operation Q.alice f hf h s

@[simp] theorem rawTerminalBob_operation (h : H) (s : Set PUnit.{v+1}) :
    (rawTerminalBob Q f hf).operation h s = Q.bob.operation (f h) s :=
  rawTerminalInstrument_operation Q.bob f hf h s

end NormalTerminal
end QuantumProver.ElegantJointMeasurement.HilbertCommonPhysicalTerminalRealization

import QuantumProver.InformationTheory.ElegantJointMeasurement.NormalInstrumentAbsorption
import QuantumProver.InformationTheory.ElegantJointMeasurement.SeparableHilbertEmbedding
import QuantumProver.InformationTheory.ElegantJointMeasurement.SquareProcess

noncomputable section
set_option autoImplicit false
namespace QuantumProver.ElegantJointMeasurement.NormalProcess
open QuantumProver.ElegantJointMeasurement.HilbertSquareProcess QuantumProver.ElegantJointMeasurement.NormalCPInstruments
open QuantumProver.ElegantJointMeasurement.SeparableHilbertEmbedding
open scoped Matrix.Norms.L2Operator

abbrev Workspace := CommonHilbert
abbrev InputMatrix (d : ℕ) := Matrix (Fin d) (Fin d) ℂ
abbrev InputChannel (d : ℕ) := PhysicalOperation (Fin d) Workspace
abbrev FineRecord (R : Type*) := R × (ℕ × ℕ)

structure MatrixProcess (a b : ℕ) (R : Type*) [MeasurableSpace R] where
  initialAlice : EuclideanSpace ℂ (Fin a) →ₗᵢ[ℂ] Workspace
  initialBob : EuclideanSpace ℂ (Fin b) →ₗᵢ[ℂ] Workspace
  alice : (n : ℕ) →
    QuantumProver.ElegantJointMeasurement.NormalInstrumentAbsorption.Instrument Workspace Workspace (History R n) R
  bob : (n : ℕ) →
    QuantumProver.ElegantJointMeasurement.NormalInstrumentAbsorption.Instrument Workspace Workspace (History R n) R
  aliceTurn : (n : ℕ) → History R n → Bool
  turn_measurable : ∀ n, Measurable (aliceTurn n)

end QuantumProver.ElegantJointMeasurement.NormalProcess

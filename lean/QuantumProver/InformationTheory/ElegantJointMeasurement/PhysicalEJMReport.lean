import QuantumProver.InformationTheory.ElegantJointMeasurement.NormalCost
import QuantumProver.InformationTheory.ElegantJointMeasurement.CommonPhysicalChronology

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory Matrix Set Function Preorder
open scoped BigOperators Topology ComplexConjugate ComplexOrder MatrixOrder

namespace QuantumProver.ElegantJointMeasurement.PhysicalEJMReport

open QuantumProver.ElegantJointMeasurement.NormalProcess QuantumProver.ElegantJointMeasurement.HilbertSquareProcess
open QuantumProver.ElegantJointMeasurement.HilbertTranscriptPOVM QuantumProver.ElegantJointMeasurement.PhysicalTranscriptCoding
open QuantumProver.ElegantJointMeasurement.NormalRecordTransport QuantumProver.ElegantJointMeasurement.HilbertFiniteNormalRecordLift
open QuantumProver.ElegantJointMeasurement.HilbertFiniteEJMProtocol QuantumProver.ElegantJointMeasurement.NormalCost
open QuantumProver.ElegantJointMeasurement.HilbertFiniteCostModel
open QuantumProver.ElegantJointMeasurement.Teleportation QuantumProver.ElegantJointMeasurement.Teleportation.PhysicalUpper
open QuantumProver.WernerEndpoint.MatrixCommonPhysicalRealization
open QuantumProver.ElegantJointMeasurement.HilbertCommonPhysicalChronology

universe u

abbrev oneEbitRawProcess : MatrixProcess 4 4 (ULift.{u} ℕ) :=
  liftedOfProtocol oneEbitProtocol

abbrev PhysicalOneEbitOutcomes : ℕ → Type u :=
  constantOutcomes (ULift.{u} ℕ)

def physicalOneEbitTranscriptEquiv :
    PhysicalTranscript PhysicalOneEbitOutcomes.{u} ≃ᵐ Transcript (ULift.{u} ℕ) :=
  MeasurableEquiv.refl _

def physicalOneEbitReport
    (t : PhysicalTranscript PhysicalOneEbitOutcomes.{u}) : Fin 4 :=
  ejmLiftedPhysicalReport (physicalOneEbitTranscriptEquiv t)

theorem measurable_physicalOneEbitReport :
    Measurable physicalOneEbitReport.{u} :=
  measurable_ejmLiftedPhysicalReport.comp physicalOneEbitTranscriptEquiv.measurable

theorem physicalOneEbitReport_eq_physical
    (t : PhysicalTranscript PhysicalOneEbitOutcomes.{u}) :
    physicalOneEbitReport t = ejmLiftedPhysicalReport t := rfl

theorem physicalOneEbitReport_third_record
    (t : PhysicalTranscript PhysicalOneEbitOutcomes.{u}) :
    physicalOneEbitReport t = decodeEJMRecord ((t 2).down) := by
  change decodeEJMRecord
    (((appendHistory (R := ℕ) 2).symm
      ((QuantumProver.ElegantJointMeasurement.NormalRecordTransport.historyEquiv natLiftEquiv.{u} 3).symm
        (frestrictLe (π := fun _ => ULift.{u} ℕ) 2 t))).2) = _
  rfl

abbrev oneEbitChargedInput
    (ρ : Matrix SystemIndex SystemIndex ℂ) : JointInputMatrix 4 4 :=
  matrixCodeMatrix alicePhysicalEquiv bobPhysicalEquiv resource * ρ *
    (matrixCodeMatrix alicePhysicalEquiv bobPhysicalEquiv resource)ᴴ

theorem oneEbitChargedInput_eq_physical
    (ρ : Matrix SystemIndex SystemIndex ℂ) :
    oneEbitChargedInput ρ = matrixResourceEmbedding * ρ * matrixResourceEmbeddingᴴ := by
  simp only [oneEbitChargedInput, oneEbit_matrixCodeMatrix]

theorem oneEbitChargedInput_posSemidef
    (ρ : Matrix SystemIndex SystemIndex ℂ) (hρ : ρ.PosSemidef) :
    (oneEbitChargedInput ρ).PosSemidef :=
  hρ.mul_mul_conjTranspose_same
    (matrixCodeMatrix alicePhysicalEquiv bobPhysicalEquiv resource)

def physicalOneEbitBornMeasure
    (ρ : Matrix SystemIndex SystemIndex ℂ) (hρ : ρ.PosSemidef) :
    Measure (PhysicalTranscript PhysicalOneEbitOutcomes.{u}) :=
  constantPhysicalBornMeasure oneEbitRawProcess
    (oneEbitChargedInput ρ) (oneEbitChargedInput_posSemidef ρ hρ)

theorem physicalOneEbitBornMeasure_eq_literal
    (ρ : Matrix SystemIndex SystemIndex ℂ) (hρ : ρ.PosSemidef) :
    physicalOneEbitBornMeasure.{u} ρ hρ =
      QuantumProver.ElegantJointMeasurement.NormalPhysicalOperationalBridge.physicalBornMeasure
        (constantOutcomes (ULift.{u} ℕ)) (domains oneEbitRawProcess)
        (sourceFamily oneEbitRawProcess) (sourceFamily oneEbitRawProcess)
        (outputFamily oneEbitRawProcess true) (outputFamily oneEbitRawProcess false)
        (wiring oneEbitRawProcess true) (wiring oneEbitRawProcess false)
        (localFamily oneEbitRawProcess true) (localFamily oneEbitRawProcess false)
        oneEbitRawProcess.initialAlice oneEbitRawProcess.initialBob
        (oneEbitChargedInput ρ) (oneEbitChargedInput_posSemidef ρ hρ) := rfl

theorem physicalOneEbitBornMeasure_eq_physical
    (ρ : Matrix SystemIndex SystemIndex ℂ) (hρ : ρ.PosSemidef) :
    physicalOneEbitBornMeasure.{u} ρ hρ =
      oneEbitRawProcess.represented_physicalBornMeasure
        (oneEbitChargedInput ρ) (oneEbitChargedInput_posSemidef ρ hρ) :=
  constantPhysicalBornMeasure_eq_physical oneEbitRawProcess
    (oneEbitChargedInput ρ) (oneEbitChargedInput_posSemidef ρ hρ)

set_option maxRecDepth 4096 in

theorem oneEbit_physicalBorn_report
    (ρ : Matrix SystemIndex SystemIndex ℂ) (hρ : ρ.PosSemidef) (j : Fin 4) :
    physicalOneEbitBornMeasure.{u} ρ hρ {t | physicalOneEbitReport t = j} =
      ENNReal.ofReal ((Matrix.trace (represented_physicalEffect j * ρ)).re) := by
  rw [physicalOneEbitBornMeasure_eq_physical]
  simp only [physicalOneEbitReport_eq_physical, oneEbitChargedInput,
    oneEbit_matrixCodeMatrix]
  exact oneEbit_lifted_physicalBorn_report.{u} ρ hρ j

theorem oneEbit_physicalBorn_report_toReal
    (ρ : Matrix SystemIndex SystemIndex ℂ) (hρ : ρ.PosSemidef) (j : Fin 4) :
    (physicalOneEbitBornMeasure.{u} ρ hρ {t | physicalOneEbitReport t = j}).toReal =
      (Matrix.trace (represented_physicalEffect j * ρ)).re := by
  rw [oneEbit_physicalBorn_report ρ hρ j, ENNReal.toReal_ofReal]
  exact QuantumProver.ElegantJointMeasurement.HilbertTranscriptPOVM.MatrixProbe.bornScalar_nonneg
    ρ (represented_physicalEffect j) hρ (represented_physicalEffect_posSemidef j)

def physicalOneEbitSharedReport
    (ρ : Matrix SystemIndex SystemIndex ℂ) (hρ : ρ.PosSemidef) :
    Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) ℂ :=
  ∑ j : Fin 4,
    (((physicalOneEbitBornMeasure.{u} ρ hρ
      {t | physicalOneEbitReport t = j}).toReal : ℝ) : ℂ) •
        Tomography.sharedProjector j

theorem oneEbit_physicalSharedReport_output
    (ρ : Matrix SystemIndex SystemIndex ℂ) (hρ : ρ.PosSemidef) :
    physicalOneEbitSharedReport.{u} ρ hρ = physicalClassicalChannel ρ := by
  change _ = Tomography.measurementChannel represented_physicalEffect ρ
  apply Finset.sum_congr rfl
  intro j hj
  rw [oneEbit_physicalBorn_report_toReal ρ hρ j]
  rw [QuantumProver.ElegantJointMeasurement.PreparedReports.trace_mul_psd_re_cast
    _ _ (represented_physicalEffect_posSemidef j) hρ]

theorem physicalOneEbit_resource_normalized : (resource * resourceᴴ).trace = 1 :=
  oneEbit_resource_normalized

theorem physicalOneEbit_resource_entropy :
    QuantumProver.ElegantJointMeasurement.TailReference.vonNeumannEntropyBits (resource * resourceᴴ) = 1 :=
  oneEbit_resource_entropy

end QuantumProver.ElegantJointMeasurement.PhysicalEJMReport

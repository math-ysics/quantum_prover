import QuantumProver.InformationTheory.ElegantJointMeasurement.NormalPhysicalOperationalBridge
import QuantumProver.InformationTheory.ElegantJointMeasurement.NormalPhysicalEventChronology
import QuantumProver.InformationTheory.ElegantJointMeasurement.NormalPhysicalTerminalAdmission

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
open MeasureTheory ProbabilityTheory Set Filter Function InnerProductSpace TopologicalSpace Preorder
open scoped BigOperators Topology ComplexOrder Classical

namespace QuantumProver.ElegantJointMeasurement.NormalPhysicalOperationalBridge
open QuantumProver.ElegantJointMeasurement.NormalProcess QuantumProver.ElegantJointMeasurement.HilbertSquareProcess QuantumProver.ElegantJointMeasurement.HilbertRecordCoding
open QuantumProver.ElegantJointMeasurement.NormalPhysicalAdmission QuantumProver.ElegantJointMeasurement.HilbertChoi QuantumProver.ElegantJointMeasurement.NuclearChoi
open QuantumProver.ElegantJointMeasurement.NormalPhysicalTerminalAdmission
open QuantumProver.ElegantJointMeasurement.MeasurableNormalInstrument (MatrixInstrument)
open QuantumProver.ElegantJointMeasurement.NormalInstrumentAbsorption QuantumProver.ElegantJointMeasurement.NormalSandwich
open QuantumProver.ElegantJointMeasurement.SeparableHilbertEmbedding QuantumProver.ElegantJointMeasurement.MeasurableHilbertField
open QuantumProver.HilbertNuclearCompression QuantumProver.MatrixNuclearTensor
open QuantumProver.NuclearOperator (toOperator)
universe u v w

variable (Ω : ℕ → Type u) [∀ n, MeasurableSpace (Ω n)]
  [∀ n, StandardBorelSpace (Ω n)]

section PhysicalTerminalOutput

variable (D : PhysicalDomains Ω)
  {EA EB : (n : ℕ) → D.admissible n → Type v}
  [∀ n h, NormedAddCommGroup (EA n h)] [∀ n h, InnerProductSpace ℂ (EA n h)]
  [∀ n h, CompleteSpace (EA n h)]
  [∀ n h, NormedAddCommGroup (EB n h)] [∀ n h, InnerProductSpace ℂ (EB n h)]
  [∀ n h, CompleteSpace (EB n h)]
  (FA : (n : ℕ) → FundamentalFamily (EA n))
  (FB : (n : ℕ) → FundamentalFamily (EB n))
  {GA : (n : ℕ) → D.actingDomain n true × Ω n → Type w}
  {GB : (n : ℕ) → D.actingDomain n false × Ω n → Type w}
  [∀ n z, NormedAddCommGroup (GA n z)] [∀ n z, InnerProductSpace ℂ (GA n z)]
  [∀ n z, CompleteSpace (GA n z)]
  [∀ n z, NormedAddCommGroup (GB n z)] [∀ n z, InnerProductSpace ℂ (GB n z)]
  [∀ n z, CompleteSpace (GB n z)]
  (QA : (n : ℕ) → FundamentalFamily (GA n))
  (QB : (n : ℕ) → FundamentalFamily (GB n))
  (WA : PhysicalMemoryWiring Ω D true FA QA)
  (WB : PhysicalMemoryWiring Ω D false FB QB)
  (PA : PhysicalLocalFamily Ω D true FA QA)
  (PB : PhysicalLocalFamily Ω D false FB QB)
  {a b : ℕ} [NeZero a] [NeZero b]
  (JA : EuclideanSpace ℂ (Fin a) →ₗᵢ[ℂ] EA 0 D.initialHistory)
  (JB : EuclideanSpace ℂ (Fin b) →ₗᵢ[ℂ] EB 0 D.initialHistory)

local notation "N" => ofPhysicalFamilies Ω D FA FB QA QB WA WB PA PB JA JB
local notation "CA" n => IntrinsicFamily.family (selectedMemory Ω D true FA QA WA n)
local notation "CB" n => IntrinsicFamily.family (selectedMemory Ω D false FB QB WB n)

def decodePhysicalAdmissibleHistory (k : ℕ)
    (h : range (fun z : D.admissible k => encodeHistory Ω k z.val)) : D.admissible k :=
  (measurableEmbedding_encodeAdmissibleHistory Ω k (D.admissible k)
    (D.admissible_measurable k)).equivRange.symm h

@[simp] theorem decodePhysicalAdmissibleHistory_encode (k : ℕ) (h : D.admissible k)
    {hh : encodeHistory Ω k h.val ∈ range (fun z : D.admissible k => encodeHistory Ω k z.val)} :
    decodePhysicalAdmissibleHistory Ω D k ⟨encodeHistory Ω k h.val,hh⟩ = h :=
  (measurableEmbedding_encodeAdmissibleHistory Ω k (D.admissible k)
    (D.admissible_measurable k)).equivRange_symm_apply_mk h

def physicalInputDensity (k : ℕ) (X : JointInputMatrix a b) (h : D.admissible k) :
    Nuclear (Joint (EA k h) (EB k h)) :=
  chosenJointRecover Ω D FA FB QA QB WA WB k h
    (chargedDecode X (physicalState Ω D FA FB QA QB WA WB PA PB JA JB k
      (encodeHistory Ω k h.val)))

variable (k c d : ℕ)
  (TA : MatrixInstrument (FA k) (finiteOutputFamily (H := D.admissible k) c) PUnit.{u+1})
  (TB : MatrixInstrument (FB k) (finiteOutputFamily (H := D.admissible k) d) PUnit.{u+1})
  (hc : 0 < c) (hd : 0 < d)

local notation "Qterm" => ofPhysicalTerminal Ω D FA FB QA QB WA WB k c d TA TB hc hd

def physicalTerminalResponse (X : JointInputMatrix a b) (h : History (CommonRecord Ω) k) :
    Nuclear (TerminalWorkspace c d) :=
  if hh : h ∈ range (fun z : D.admissible k => encodeHistory Ω k z.val) then
    let z := decodePhysicalAdmissibleHistory Ω D k ⟨h,hh⟩
    physicalTerminalJointOperation Ω D FA FB k c d TA TB z
      (physicalInputDensity Ω D FA FB QA QB WA WB PA PB JA JB k X z)
  else 0

theorem physicalTerminalResponse_encoded (X : JointInputMatrix a b) (h : D.admissible k) :
    physicalTerminalResponse Ω D FA FB QA QB WA WB PA PB JA JB k c d TA TB X
      (encodeHistory Ω k h.val) =
      physicalTerminalJointOperation Ω D FA FB k c d TA TB h
        (physicalInputDensity Ω D FA FB QA QB WA WB PA PB JA JB k X h) := by
  rw [physicalTerminalResponse, dif_pos (mem_range_self h)]
  exact congrArg (fun z : D.admissible k =>
    physicalTerminalJointOperation Ω D FA FB k c d TA TB z
      (physicalInputDensity Ω D FA FB QA QB WA WB PA PB JA JB k X z))
    (decodePhysicalAdmissibleHistory_encode Ω D k h (hh := mem_range_self h))

theorem physicalTerminalResponse_eq_admitted_on_supported (X : JointInputMatrix a b)
    (h : D.admissible k)
    (hh : h ∈ physicallySupportedHistory Ω D FA FB QA QB WA WB PA PB JA JB k) :
    physicalTerminalResponse Ω D FA FB QA QB WA WB PA PB JA JB k c d TA TB X
      (encodeHistory Ω k h.val) =
      terminalJointOperation Qterm (encodeHistory Ω k h.val)
        ((N).represented_physicalInputDensity k X (encodeHistory Ω k h.val)) := by
  rw [physicalTerminalResponse_encoded, physicalInputDensity, physicalState_eq_admitted]
  have hInput := physicalInputDensity_supported_of_physicalState_supported (N) k
    (encodeHistory Ω k h.val) X (physicalJointProjection (CA k) (CB k) h)
    (physicalJointProjection_adjoint (CA k) (CB k) h) hh
  have hRet := physicalState_retraction (CA k) (CB k) h
    ((N).represented_physicalInputDensity k X (encodeHistory Ω k h.val)) hInput
  have hTerm := terminalJointOperation_on_physical_code Ω D FA FB QA QB WA WB k c d TA TB hc hd h
    (chosenJointRecover Ω D FA FB QA QB WA WB k h
      ((N).represented_physicalInputDensity k X (encodeHistory Ω k h.val)))
  rw [← chosenJointCode_eq_physicalJointCode Ω D FA FB QA QB WA WB k h] at hTerm
  change terminalJointOperation Qterm (encodeHistory Ω k h.val)
    (physicalStateCode (CA k) (CB k) h
      (physicalStateRecover (CA k) (CB k) h
        ((N).represented_physicalInputDensity k X (encodeHistory Ω k h.val)))) = _ at hTerm
  rw [hRet] at hTerm
  exact hTerm.symm

theorem physicalTerminalResponse_ae_eq_admitted (X : JointInputMatrix a b) :
    physicalTerminalResponse Ω D FA FB QA QB WA WB PA PB JA JB k c d TA TB X
      =ᵐ[(N).represented_physicalPrefixMeasure k]
        (fun h => terminalJointOperation Qterm h ((N).represented_physicalInputDensity k X h)) := by
  filter_upwards [physical_physicalPrefixMeasure_ae_supported
    Ω D FA FB QA QB WA WB PA PB JA JB k] with h hh
  rcases hh with ⟨z,hz,rfl⟩
  exact physicalTerminalResponse_eq_admitted_on_supported
    Ω D FA FB QA QB WA WB PA PB JA JB k c d TA TB hc hd X z hz

include hc hd in
theorem physicalTerminalResponse_integrable (X : JointInputMatrix a b) :
    Integrable (physicalTerminalResponse Ω D FA FB QA QB WA WB PA PB JA JB k c d TA TB X)
      (physicalPrefixMeasure Ω D FA FB QA QB WA WB PA PB JA JB k) := by
  rw [physicalPrefixMeasure_eq_admitted]
  exact ((N).physicalQuantumOutput_integrable k Qterm X).congr
    (physicalTerminalResponse_ae_eq_admitted Ω D FA FB QA QB WA WB PA PB JA JB k c d TA TB hc hd X).symm

def physicalPhysicalQuantumNuclearOutput (X : JointInputMatrix a b) : Nuclear (TerminalWorkspace c d) :=
  ∫ h, physicalTerminalResponse Ω D FA FB QA QB WA WB PA PB JA JB k c d TA TB X h
    ∂physicalPrefixMeasure Ω D FA FB QA QB WA WB PA PB JA JB k

def represented_physicalPhysicalQuantumOutput (X : JointInputMatrix a b) : JointInputMatrix c d :=
  finiteJointDecode c d
    (physicalPhysicalQuantumNuclearOutput Ω D FA FB QA QB WA WB PA PB JA JB k c d TA TB X)

theorem physicalPhysicalQuantumNuclearOutput_eq_admitted (X : JointInputMatrix a b) :
    physicalPhysicalQuantumNuclearOutput Ω D FA FB QA QB WA WB PA PB JA JB k c d TA TB X =
      (N).physicalQuantumNuclearOutput k Qterm X := by
  rw [physicalPhysicalQuantumNuclearOutput, physicalPrefixMeasure_eq_admitted]
  apply integral_congr_ae
  exact physicalTerminalResponse_ae_eq_admitted Ω D FA FB QA QB WA WB PA PB JA JB k c d TA TB hc hd X

theorem physicalPhysicalQuantumOutput_eq_admitted (X : JointInputMatrix a b) :
    represented_physicalPhysicalQuantumOutput Ω D FA FB QA QB WA WB PA PB JA JB k c d TA TB X =
      (N).represented_physicalQuantumOutput k Qterm X := by
  apply congrArg (finiteJointDecode c d)
  exact physicalPhysicalQuantumNuclearOutput_eq_admitted Ω D FA FB QA QB WA WB PA PB JA JB k c d TA TB hc hd X

end PhysicalTerminalOutput
end QuantumProver.ElegantJointMeasurement.NormalPhysicalOperationalBridge

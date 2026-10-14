import QuantumProver.QuantumChannels.PhysicalProtocolData
import QuantumProver.InformationTheory.WernerEndpoint.CommonPhysicalRealization
import QuantumProver.InformationTheory.ElegantJointMeasurement.CommonPhysicalChronology
import QuantumProver.InformationTheory.ElegantJointMeasurement.CommonPhysicalTerminalRealization
import QuantumProver.InformationTheory.ElegantJointMeasurement.NormalPhysicalOutputTransport
import QuantumProver.InformationTheory.ElegantJointMeasurement.FiniteNormalOperationalBridge

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w

open MeasureTheory Matrix Set Filter Function
open QuantumProver.ElegantJointMeasurement.NormalPhysicalAdmission QuantumProver.ElegantJointMeasurement.NormalPhysicalTerminalAdmission
open QuantumProver.ElegantJointMeasurement.NormalPhysicalOperationalBridge QuantumProver.ElegantJointMeasurement.NormalProcess QuantumProver.ElegantJointMeasurement.HilbertRecordCoding
open QuantumProver.ElegantJointMeasurement.HilbertSquareProcess QuantumProver.ElegantJointMeasurement.NuclearChoi QuantumProver.ElegantJointMeasurement.MeasurableNormalInstrument
open QuantumProver.ElegantJointMeasurement.HilbertCommonPhysicalChronology QuantumProver.ElegantJointMeasurement.HilbertCommonPhysicalTerminalRealization
open QuantumProver.ElegantJointMeasurement.HilbertFiniteNormalChronology QuantumProver.ElegantJointMeasurement.HilbertFiniteNormalRecordLift
open QuantumProver.ElegantJointMeasurement.HilbertFiniteNormalOperationalBridge
open QuantumProver.WernerEndpoint.MatrixCommonPhysicalRealization
open scoped BigOperators Topology ComplexOrder

namespace QuantumProver.ElegantJointMeasurement.PhysicalCost

local instance finiteComplete (q : ℕ) : CompleteSpace (EuclideanSpace ℂ (Fin q)) :=
  PiLp.completeSpace 2 (fun _ : Fin q => ℂ)

section PhysicalQuantumOutput
variable {a b N c d : ℕ} [NeZero a] [NeZero b]

def physicalQuantumOutput (P : PhysicalProtocol.{u,v,w} a b)
    (Q : PhysicalReadout P N c d) (X : JointInputMatrix a b) : JointInputMatrix c d :=
  represented_physicalPhysicalQuantumOutput P.Outcomes P.domains P.aliceSections P.bobSections
    P.aliceOutputSections P.bobOutputSections P.aliceWiring P.bobWiring
    P.aliceInstrument P.bobInstrument P.chargedAlice P.chargedBob N c d Q.alice Q.bob X

theorem physicalQuantumOutput_eq_matrix (P : PhysicalProtocol.{u,v,w} a b)
    (Q : PhysicalReadout P N c d) (hc : 0 < c) (hd : 0 < d)
    (X : JointInputMatrix a b) :
    physicalQuantumOutput P Q X = P.represented.represented_physicalQuantumOutput N (Q.represented hc hd) X :=
  physicalPhysicalQuantumOutput_eq_admitted P.Outcomes P.domains P.aliceSections P.bobSections
    P.aliceOutputSections P.bobOutputSections P.aliceWiring P.bobWiring
    P.aliceInstrument P.bobInstrument P.chargedAlice P.chargedBob
    N c d Q.alice Q.bob hc hd X

end PhysicalQuantumOutput

section CommonRealization
variable {R : Type u} [MeasurableSpace R] [StandardBorelSpace R]
variable {a b : ℕ} [NeZero a] [NeZero b]

def commonPhysicalProtocol (P : MatrixProcess a b R) : PhysicalProtocol.{u,0,0} a b :=
  packagePhysicalFamilies (constantOutcomes R) (domains P)
    (sourceFamily P) (sourceFamily P) (outputFamily P true) (outputFamily P false)
    (wiring P true) (wiring P false) (localFamily P true) (localFamily P false)
    P.initialAlice P.initialBob

theorem commonPhysicalProtocol_matrix (P : MatrixProcess a b R) :
    (commonPhysicalProtocol P).represented = realization P := rfl

def commonRawHistory (P : MatrixProcess a b R) (N : ℕ) :
    (domains P).admissible N → History R N := fun h => historyEquiv R N h.val

theorem measurable_commonRawHistory (P : MatrixProcess a b R) (N : ℕ) :
    Measurable (commonRawHistory P N) :=
  (historyEquiv R N).measurable.comp measurable_subtype_coe

def commonPhysicalReadout (P : MatrixProcess a b R) (N : ℕ)
    {c d : ℕ} (Q : NormalTerminal R N c d) : PhysicalReadout (commonPhysicalProtocol P) N c d where
  alice := rawTerminalAlice Q (commonRawHistory P N) (measurable_commonRawHistory P N)
  bob := rawTerminalBob Q (commonRawHistory P N) (measurable_commonRawHistory P N)

theorem commonPhysicalReadout_jointOperation (P : MatrixProcess a b R) (N : ℕ)
    {c d : ℕ} (Q : NormalTerminal R N c d) (h : (domains P).admissible N) :
    physicalTerminalJointOperation (constantOutcomes R) (domains P)
      (sourceFamily P) (sourceFamily P) N c d
      (commonPhysicalReadout P N Q).alice (commonPhysicalReadout P N Q).bob h =
        terminalJointOperation Q (commonRawHistory P N h) := by
  have hA := tensorOperation_congr_event (V := Workspace)
    (physicalTerminalLocal (commonPhysicalReadout P N Q).alice h) Q.alice
    () (commonRawHistory P N h) univ univ MeasurableSet.univ MeasurableSet.univ
    (rawTerminalAlice_operation Q (commonRawHistory P N)
      (measurable_commonRawHistory P N) h univ)
  have hB := rightTensorOperation_congr_event (V := EuclideanSpace ℂ (Fin c))
    (physicalTerminalLocal (commonPhysicalReadout P N Q).bob h) Q.bob
    () (commonRawHistory P N h) univ univ MeasurableSet.univ MeasurableSet.univ
    (rawTerminalBob_operation Q (commonRawHistory P N)
      (measurable_commonRawHistory P N) h univ)
  unfold physicalTerminalJointOperation terminalJointOperation
  rw [hA, hB]

theorem common_physicalQuantumOutput_eq_physical (P : MatrixProcess a b R) (N : ℕ)
    {c d : ℕ} (Q : NormalTerminal R N c d) (hc : 0 < c) (hd : 0 < d)
    (X : JointInputMatrix a b) :
    physicalQuantumOutput (commonPhysicalProtocol P) (commonPhysicalReadout P N Q) X =
      P.represented_physicalQuantumOutput N Q X := by
  let F := physicalTerminalResponse (constantOutcomes R) (domains P)
    (sourceFamily P) (sourceFamily P) (outputFamily P true) (outputFamily P false)
    (wiring P true) (wiring P false) (localFamily P true) (localFamily P false)
    P.initialAlice P.initialBob N c d
    (commonPhysicalReadout P N Q).alice (commonPhysicalReadout P N Q).bob X
  have hCode : MeasurableEmbedding (constantHistoryCoding P N) :=
    measurableEmbedding_constantHistoryCoding P N
  apply congrArg (finiteJointDecode c d)
  change (∫ h, F h ∂physicalPrefixMeasure (constantOutcomes R) (domains P)
    (sourceFamily P) (sourceFamily P) (outputFamily P true) (outputFamily P false)
    (wiring P true) (wiring P false) (localFamily P true) (localFamily P false)
    P.initialAlice P.initialBob N) = P.physicalQuantumNuclearOutput N Q X
  rw [← constant_physicalPrefixMeasure_map P N, hCode.integral_map]
  unfold MatrixProcess.physicalQuantumNuclearOutput
  apply integral_congr_ae
  filter_upwards [constant_physicalInputDensity_ae P N X] with h hh
  let z : (domains P).admissible N := ⟨(historyEquiv R N).symm h, mem_univ _⟩
  change F (encodeHistory (constantOutcomes R) N z.val) = _
  dsimp only [F]
  rw [physicalTerminalResponse_encoded, commonPhysicalReadout_jointOperation, hh]
  simp only [commonRawHistory, z, MeasurableEquiv.apply_symm_apply]

end CommonRealization

section FinitePhysicalWitness
variable {a b c d : ℕ} [NeZero a] [NeZero b]

def finitePhysicalProtocol (U : Protocol c d a b) : PhysicalProtocol.{u,0,0} a b :=
  commonPhysicalProtocol (liftedOfProtocol.{u} U)

def finitePhysicalReadout (U : Protocol c d a b) (N : ℕ) (hc : 0 < c) (hd : 0 < d) :
    PhysicalReadout (finitePhysicalProtocol.{u} U) N c d :=
  commonPhysicalReadout (liftedOfProtocol.{u} U) N
    (physicalLiftedFiniteNormalTerminal U N hc hd)

theorem finitePhysicalQuantumOutput_eq_apply (U : Protocol c d a b)
    (N : ℕ) (hN : depth U ≤ N) (hc : 0 < c) (hd : 0 < d) (X : JointInputMatrix a b) :
    physicalQuantumOutput (finitePhysicalProtocol.{u} U) (finitePhysicalReadout U N hc hd) X =
      U.apply X := by
  change physicalQuantumOutput (commonPhysicalProtocol (liftedOfProtocol.{u} U))
    (commonPhysicalReadout (liftedOfProtocol.{u} U) N
      (physicalLiftedFiniteNormalTerminal U N hc hd)) X = U.apply X
  exact (common_physicalQuantumOutput_eq_physical (liftedOfProtocol.{u} U) N
    (physicalLiftedFiniteNormalTerminal U N hc hd) hc hd X).trans
    (physicalQuantumOutput_liftedOfProtocol_eq_apply U N hN hc hd X)

theorem tendsto_finitePhysicalQuantumOutput (U : Protocol c d a b)
    (hc : 0 < c) (hd : 0 < d) (X : JointInputMatrix a b) :
    Tendsto (fun N => physicalQuantumOutput (finitePhysicalProtocol.{u} U)
      (finitePhysicalReadout U N hc hd) X) atTop (𝓝 (U.apply X)) := by
  have he : (fun N => physicalQuantumOutput (finitePhysicalProtocol.{u} U)
      (finitePhysicalReadout U N hc hd) X) =ᶠ[atTop] fun _ => U.apply X :=
    (eventually_ge_atTop (depth U)).mono fun N hN =>
      finitePhysicalQuantumOutput_eq_apply U N hN hc hd X
  exact tendsto_const_nhds.congr' he.symm

end FinitePhysicalWitness
end QuantumProver.ElegantJointMeasurement.PhysicalCost

import QuantumProver.InformationTheory.ElegantJointMeasurement.NormalProcess
import QuantumProver.InformationTheory.ElegantJointMeasurement.FiniteNormalRecordLift
import QuantumProver.InformationTheory.ElegantJointMeasurement.FiniteEJMProtocol

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open MeasureTheory Set Filter
open QuantumProver.ElegantJointMeasurement.NormalProcess QuantumProver.ElegantJointMeasurement.HilbertFiniteNormalChronology
open QuantumProver.ElegantJointMeasurement.HilbertFiniteNormalRecordLift QuantumProver.ElegantJointMeasurement.HilbertFiniteEJMProtocol
open QuantumProver.ElegantJointMeasurement.HilbertSquareProcess (History appendHistory)
open scoped BigOperators Topology Kronecker Matrix.Norms.L2Operator

namespace QuantumProver.ElegantJointMeasurement.HilbertFiniteNormalOperationalBridge

local instance finiteComplete (q : ℕ) : CompleteSpace (EuclideanSpace ℂ (Fin q)) :=
  PiLp.completeSpace 2 (fun _ : Fin q => ℂ)

variable {c d a b : ℕ} [NeZero a] [NeZero b]

theorem physicalJoint_eq_finiteJointChart :
    physicalJoint c d = finiteJointChart c d := rfl

theorem ofProtocol_initialJointOperation_eq_codedJoint (U : Protocol c d a b) :
    (ofProtocol U).initialJointOperation = codedJoint a b := by
  apply joint_matrix_clm_ext
  intro X Y
  rw [MatrixProcess.initialJointOperation_product, codedJoint_product]
  rfl

theorem ofProtocol_physicalStep_singleton (U : Protocol c d a b)
    (n : ℕ) (h : History ℕ n) (r : ℕ) :
    ((ofProtocol U).represented_physicalStepInstrument n).operation h {r} = rawStep U n h r := by
  change (if (ofProtocol U).aliceTurn n h = true then
    QuantumProver.MatrixNormalTensorInstrument.tensorOperation
      (G := Workspace) ((ofProtocol U).alice n) h {r} else
    QuantumProver.MatrixNormalRightTensor.rightTensorOperation
      (G := Workspace) ((ofProtocol U).bob n) h {r}) = rawStep U n h r
  rfl

def physicalFiniteNormalTerminal (U : Protocol c d a b) (n : ℕ)
    (hc : 0 < c) (hd : 0 < d) : NormalTerminal ℕ n c d where
  alice := terminalAlice U n hc
  bob := terminalBob U n hd

theorem physicalFiniteNormalTerminal_jointOperation (U : Protocol c d a b)
    (n : ℕ) (hc : 0 < c) (hd : 0 < d) (h : History ℕ n) :
    terminalJointOperation (physicalFiniteNormalTerminal U n hc hd) h =
      terminalOutput U n hc hd h := rfl

theorem physicalPrefixAction_ofProtocol_singleton (U : Protocol c d a b)
    (n : ℕ) (h : History ℕ n) (X : JointMatrix a b) :
    (ofProtocol U).represented_physicalPrefixAction n {h} X =
      rawPrefix U n h (codedJoint a b X) := by
  induction n with
  | zero =>
    cases h
    rw [MatrixProcess.physicalPrefixAction_zero_singleton,
      ofProtocol_initialJointOperation_eq_codedJoint]
    rfl
  | succ n ih =>
    obtain ⟨⟨h, r⟩, rfl⟩ := (appendHistory (R := ℕ) n).surjective h
    rw [MatrixProcess.physicalPrefixAction_singleton_successor,
      ofProtocol_physicalStep_singleton]
    simp only [rawPrefix, MeasurableEquiv.symm_apply_apply,
      ContinuousLinearMap.comp_apply, ih]

theorem physicalQuantumOutput_ofProtocol_eq_apply (U : Protocol c d a b)
    (n : ℕ) (hn : depth U ≤ n) (hc : 0 < c) (hd : 0 < d) (X : JointMatrix a b) :
    (ofProtocol U).represented_physicalQuantumOutput n (physicalFiniteNormalTerminal U n hc hd) X =
      U.apply X := by
  apply MatrixProcess.physicalQuantumOutput_eq_of_hasSum
  simpa only [physicalFiniteNormalTerminal_jointOperation,
    physicalPrefixAction_ofProtocol_singleton, ← physicalJoint_eq_finiteJointChart] using
    hasSum_terminal_rawPrefix_eq_apply U hc hd n hn X

theorem liftedOfProtocol_initialJointOperation_eq_codedJoint (U : Protocol c d a b) :
    (liftedOfProtocol.{u} U).initialJointOperation = codedJoint a b := by
  change (ofProtocol U).initialJointOperation = codedJoint a b
  exact ofProtocol_initialJointOperation_eq_codedJoint U

theorem liftedOfProtocol_physicalStep_singleton (U : Protocol c d a b)
    (n : ℕ) (h : History (ULift.{u} ℕ) n) (r : ULift.{u} ℕ) :
    ((liftedOfProtocol U).represented_physicalStepInstrument n).operation h {r} =
      liftedRawStep U n h r := by
  change (if (liftedOfProtocol U).aliceTurn n h = true then
    QuantumProver.MatrixNormalTensorInstrument.tensorOperation
      (G := Workspace) ((liftedOfProtocol U).alice n) h {r} else
    QuantumProver.MatrixNormalRightTensor.rightTensorOperation
      (G := Workspace) ((liftedOfProtocol U).bob n) h {r}) = liftedRawStep U n h r
  rfl

def physicalLiftedFiniteNormalTerminal (U : Protocol c d a b) (n : ℕ)
    (hc : 0 < c) (hd : 0 < d) : NormalTerminal (ULift.{u} ℕ) n c d where
  alice := QuantumProver.ElegantJointMeasurement.HilbertRecordCoding.pushforwardInstrument (liftedTerminalAlice U n hc)
    (fun _ : PUnit.{1} => (PUnit.unit : PUnit.{u+1})) measurable_const
  bob := QuantumProver.ElegantJointMeasurement.HilbertRecordCoding.pushforwardInstrument (liftedTerminalBob U n hd)
    (fun _ : PUnit.{1} => (PUnit.unit : PUnit.{u+1})) measurable_const

theorem physicalLiftedFiniteNormalTerminal_jointOperation (U : Protocol c d a b)
    (n : ℕ) (hc : 0 < c) (hd : 0 < d) (h : History (ULift.{u} ℕ) n) :
    terminalJointOperation (physicalLiftedFiniteNormalTerminal U n hc hd) h =
      liftedTerminalOutput U n hc hd h := rfl

theorem physicalPrefixAction_liftedOfProtocol_singleton (U : Protocol c d a b)
    (n : ℕ) (h : History (ULift.{u} ℕ) n) (X : JointMatrix a b) :
    (liftedOfProtocol U).represented_physicalPrefixAction n {h} X =
      liftedRawPrefix U n h (codedJoint a b X) := by
  induction n with
  | zero =>
    cases h
    rw [MatrixProcess.physicalPrefixAction_zero_singleton,
      liftedOfProtocol_initialJointOperation_eq_codedJoint]
    rfl
  | succ n ih =>
    obtain ⟨⟨h, r⟩, rfl⟩ := (appendHistory (R := ULift.{u} ℕ) n).surjective h
    rw [MatrixProcess.physicalPrefixAction_singleton_successor,
      liftedOfProtocol_physicalStep_singleton]
    simp only [liftedRawPrefix, MeasurableEquiv.symm_apply_apply,
      ContinuousLinearMap.comp_apply, ih]

theorem physicalQuantumOutput_liftedOfProtocol_eq_apply (U : Protocol c d a b)
    (n : ℕ) (hn : depth U ≤ n) (hc : 0 < c) (hd : 0 < d) (X : JointMatrix a b) :
    (liftedOfProtocol.{u} U).represented_physicalQuantumOutput n
      (physicalLiftedFiniteNormalTerminal U n hc hd) X = U.apply X := by
  apply MatrixProcess.physicalQuantumOutput_eq_of_hasSum
  simpa only [physicalLiftedFiniteNormalTerminal_jointOperation,
    physicalPrefixAction_liftedOfProtocol_singleton, ← physicalJoint_eq_finiteJointChart] using
    hasSum_lifted_terminal_rawPrefix_eq_apply U hc hd n hn X

theorem tendsto_physicalQuantumOutput_ofProtocol (U : Protocol c d a b)
    (hc : 0 < c) (hd : 0 < d) (X : JointMatrix a b) :
    Tendsto (fun n => (ofProtocol U).represented_physicalQuantumOutput n
      (physicalFiniteNormalTerminal U n hc hd) X) atTop (𝓝 (U.apply X)) := by
  have he : (fun n => (ofProtocol U).represented_physicalQuantumOutput n
      (physicalFiniteNormalTerminal U n hc hd) X) =ᶠ[atTop] fun _ => U.apply X :=
    (eventually_ge_atTop (depth U)).mono fun n hn =>
      physicalQuantumOutput_ofProtocol_eq_apply U n hn hc hd X
  exact tendsto_const_nhds.congr' he.symm

theorem tendsto_physicalQuantumOutput_liftedOfProtocol (U : Protocol c d a b)
    (hc : 0 < c) (hd : 0 < d) (X : JointMatrix a b) :
    Tendsto (fun n => (liftedOfProtocol.{u} U).represented_physicalQuantumOutput n
      (physicalLiftedFiniteNormalTerminal U n hc hd) X) atTop (𝓝 (U.apply X)) := by
  have he : (fun n => (liftedOfProtocol U).represented_physicalQuantumOutput n
      (physicalLiftedFiniteNormalTerminal U n hc hd) X) =ᶠ[atTop] fun _ => U.apply X :=
    (eventually_ge_atTop (depth U)).mono fun n hn =>
      physicalQuantumOutput_liftedOfProtocol_eq_apply U n hn hc hd X
  exact tendsto_const_nhds.congr' he.symm

open QuantumProver.ElegantJointMeasurement.Teleportation

theorem physicalQuantumOutput_oneEbitProtocol (n : ℕ) (hn : depth oneEbitProtocol ≤ n)
    (ρ : Matrix SystemIndex SystemIndex ℂ) :
    (ofProtocol oneEbitProtocol).represented_physicalQuantumOutput n
      (physicalFiniteNormalTerminal oneEbitProtocol n (by decide) (by decide))
      (matrixResourceEmbedding * ρ * matrixResourceEmbedding.conjTranspose) =
        physicalClassicalChannel ρ := by
  rw [physicalQuantumOutput_ofProtocol_eq_apply oneEbitProtocol n hn]
  exact oneEbitProtocol_physical_output ρ

theorem physicalQuantumOutput_liftedOneEbitProtocol (n : ℕ)
    (hn : depth oneEbitProtocol ≤ n) (ρ : Matrix SystemIndex SystemIndex ℂ) :
    (liftedOfProtocol.{u} oneEbitProtocol).represented_physicalQuantumOutput n
      (physicalLiftedFiniteNormalTerminal oneEbitProtocol n (by decide) (by decide))
      (matrixResourceEmbedding * ρ * matrixResourceEmbedding.conjTranspose) =
        physicalClassicalChannel ρ := by
  rw [physicalQuantumOutput_liftedOfProtocol_eq_apply oneEbitProtocol n hn]
  exact oneEbitProtocol_physical_output ρ

end QuantumProver.ElegantJointMeasurement.HilbertFiniteNormalOperationalBridge

import QuantumProver.InformationTheory.ElegantJointMeasurement.FiniteNormalChronology
import QuantumProver.QuantumChannels.NormalRecordTransport

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open MeasureTheory Set Function
open QuantumProver.ElegantJointMeasurement.HilbertSquareProcess (History appendHistory)
open QuantumProver.ElegantJointMeasurement.NormalProcess QuantumProver.ElegantJointMeasurement.NormalInstrumentAbsorption
open QuantumProver.ElegantJointMeasurement.SeparableHilbertEmbedding QuantumProver.ElegantJointMeasurement.NuclearChoi
open QuantumProver.ElegantJointMeasurement.NormalRecordTransport QuantumProver.ElegantJointMeasurement.HilbertFiniteNormalChronology
open QuantumProver.MatrixNormalTensorInstrument QuantumProver.MatrixNormalRightTensor
open scoped BigOperators Topology Matrix.Norms.L2Operator Classical

namespace QuantumProver.ElegantJointMeasurement.HilbertFiniteNormalRecordLift

local instance finiteComplete (a : ℕ) : CompleteSpace (EuclideanSpace ℂ (Fin a)) :=
  PiLp.completeSpace 2 (fun _ : Fin a => ℂ)

section TensorReindex

variable {E F G H K Ω Λ : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
  [MeasurableSpace H] [MeasurableSpace K]
  [MeasurableSpace Ω] [MeasurableSpace Λ]

theorem tensorOperation_rawInstrumentReindex (P : Instrument F E H Ω)
    (f : K → H) (hf : Measurable f) (e : Ω ≃ᵐ Λ)
    (h : K) (s : Set Λ) (hs : MeasurableSet s) :
    tensorOperation (G := G) (rawInstrumentReindex P f hf e) h s =
      tensorOperation (G := G) P (f h) (e ⁻¹' s) := by
  rw [tensorOperation_of_measurable _ _ _ hs,
    tensorOperation_of_measurable _ _ _ (hs.preimage e.measurable)]
  rfl

theorem rightTensorOperation_rawInstrumentReindex (P : Instrument F E H Ω)
    (f : K → H) (hf : Measurable f) (e : Ω ≃ᵐ Λ)
    (h : K) (s : Set Λ) (hs : MeasurableSet s) :
    rightTensorOperation (G := G) (rawInstrumentReindex P f hf e) h s =
      rightTensorOperation (G := G) P (f h) (e ⁻¹' s) := by
  unfold rightTensorOperation
  rw [tensorOperation_rawInstrumentReindex P f hf e h s hs]

end TensorReindex

variable {c d a b : ℕ}

def liftedOfProtocol (U : Protocol c d a b) : MatrixProcess a b (ULift.{u} ℕ) :=
  liftNatProcess (ofProtocol U)

@[simp] theorem liftedOfProtocol_initialAlice (U : Protocol c d a b) :
    (liftedOfProtocol.{u} U).initialAlice = finiteCode a := rfl

@[simp] theorem liftedOfProtocol_initialBob (U : Protocol c d a b) :
    (liftedOfProtocol.{u} U).initialBob = finiteCode b := rfl

theorem natLift_preimage_singleton (r : ℕ) :
    natLiftEquiv.{u} ⁻¹' {natLiftEquiv.{u} r} = {r} := by
  ext q
  simp only [mem_preimage, mem_singleton_iff, (natLiftEquiv.{u}).injective.eq_iff]

def liftedRawStep (U : Protocol c d a b) (n : ℕ)
    (h : History (ULift.{u} ℕ) n) (r : ULift.{u} ℕ) :
    JointNuclear →L[ℂ] JointNuclear :=
  if (liftedOfProtocol U).aliceTurn n h then
    tensorOperation (G := CommonHilbert) ((liftedOfProtocol U).alice n) h {r}
  else rightTensorOperation (G := CommonHilbert) ((liftedOfProtocol U).bob n) h {r}

theorem liftedRawStep_eq (U : Protocol c d a b) (n : ℕ)
    (h : History ℕ n) (r : ℕ) :
    liftedRawStep U n (historyEquiv natLiftEquiv.{u} n h) (natLiftEquiv.{u} r) =
      rawStep U n h r := by
  unfold liftedRawStep rawStep liftedOfProtocol liftNatProcess
  simp only [recordEquivProcess_aliceTurn, MeasurableEquiv.symm_apply_apply]
  split_ifs
  · change tensorOperation (G := CommonHilbert)
      (rawInstrumentReindex ((ofProtocol U).alice n) (historyEquiv natLiftEquiv.{u} n).symm
        (historyEquiv natLiftEquiv.{u} n).symm.measurable natLiftEquiv.{u})
      (historyEquiv natLiftEquiv.{u} n h) {natLiftEquiv.{u} r} = _
    rw [tensorOperation_rawInstrumentReindex _ _ _ _ _ _ (measurableSet_singleton _)]
    simp only [MeasurableEquiv.symm_apply_apply, natLift_preimage_singleton]
  · change rightTensorOperation (G := CommonHilbert)
      (rawInstrumentReindex ((ofProtocol U).bob n) (historyEquiv natLiftEquiv.{u} n).symm
        (historyEquiv natLiftEquiv.{u} n).symm.measurable natLiftEquiv.{u})
      (historyEquiv natLiftEquiv.{u} n h) {natLiftEquiv.{u} r} = _
    rw [rightTensorOperation_rawInstrumentReindex _ _ _ _ _ _ (measurableSet_singleton _)]
    simp only [MeasurableEquiv.symm_apply_apply, natLift_preimage_singleton]

def liftedRawPrefix (U : Protocol c d a b) :
    (n : ℕ) → History (ULift.{u} ℕ) n → JointNuclear →L[ℂ] JointNuclear
  | 0, _ => ContinuousLinearMap.id ℂ JointNuclear
  | n+1, h =>
      let q := (appendHistory n).symm h
      (liftedRawStep U n q.1 q.2).comp (liftedRawPrefix U n q.1)

theorem liftedRawPrefix_eq (U : Protocol c d a b) (n : ℕ) (h : History ℕ n) :
    liftedRawPrefix U n (historyEquiv natLiftEquiv.{u} n h) = rawPrefix U n h := by
  induction n with
  | zero => rfl
  | succ n ih =>
      let q := (appendHistory n).symm h
      have he : h = appendHistory n (q.1, q.2) := by
        exact ((appendHistory n).apply_symm_apply h).symm
      rw [he, historyEquiv_append]
      simp only [liftedRawPrefix, rawPrefix, MeasurableEquiv.symm_apply_apply]
      rw [liftedRawStep_eq.{u}, ih]

theorem liftedRawPrefix_eq_inverse (U : Protocol c d a b) (n : ℕ)
    (h : History (ULift.{u} ℕ) n) :
    liftedRawPrefix U n h = rawPrefix U n ((historyEquiv natLiftEquiv.{u} n).symm h) := by
  simpa only [MeasurableEquiv.apply_symm_apply] using
    liftedRawPrefix_eq.{u} U n ((historyEquiv natLiftEquiv.{u} n).symm h)

def liftedTerminalAlice (U : Protocol c d a b) (n : ℕ) (hc : 0 < c) :
    Instrument CommonHilbert (EuclideanSpace ℂ (Fin c))
      (History (ULift.{u} ℕ) n) PUnit.{1} :=
  rawInstrumentReindex (terminalAlice U n hc) (historyEquiv natLiftEquiv n).symm
    (historyEquiv natLiftEquiv n).symm.measurable (MeasurableEquiv.refl PUnit.{1})

def liftedTerminalBob (U : Protocol c d a b) (n : ℕ) (hd : 0 < d) :
    Instrument CommonHilbert (EuclideanSpace ℂ (Fin d))
      (History (ULift.{u} ℕ) n) PUnit.{1} :=
  rawInstrumentReindex (terminalBob U n hd) (historyEquiv natLiftEquiv n).symm
    (historyEquiv natLiftEquiv n).symm.measurable (MeasurableEquiv.refl PUnit.{1})

theorem liftedTerminalAlice_operation (U : Protocol c d a b) (n : ℕ) (hc : 0 < c)
    (h : History ℕ n) (s : Set PUnit.{1}) :
    (liftedTerminalAlice U n hc).operation (historyEquiv natLiftEquiv.{u} n h) s =
      (terminalAlice U n hc).operation h s := by
  simp only [liftedTerminalAlice, rawInstrumentReindex_operation,
    MeasurableEquiv.symm_apply_apply]
  rfl

theorem liftedTerminalBob_operation (U : Protocol c d a b) (n : ℕ) (hd : 0 < d)
    (h : History ℕ n) (s : Set PUnit.{1}) :
    (liftedTerminalBob U n hd).operation (historyEquiv natLiftEquiv.{u} n h) s =
      (terminalBob U n hd).operation h s := by
  simp only [liftedTerminalBob, rawInstrumentReindex_operation,
    MeasurableEquiv.symm_apply_apply]
  rfl

def liftedTerminalOutput (U : Protocol c d a b) (n : ℕ)
    (hc : 0 < c) (hd : 0 < d) (h : History (ULift.{u} ℕ) n) :
    JointNuclear →L[ℂ] FiniteJointNuclear c d :=
  (rightTensorOperation (G := EuclideanSpace ℂ (Fin c)) (liftedTerminalBob U n hd) h univ).comp
    (tensorOperation (G := CommonHilbert) (liftedTerminalAlice U n hc) h univ)

theorem liftedTerminalOutput_eq (U : Protocol c d a b) (n : ℕ)
    (hc : 0 < c) (hd : 0 < d) (h : History ℕ n) :
    liftedTerminalOutput U n hc hd (historyEquiv natLiftEquiv.{u} n h) =
      terminalOutput U n hc hd h := by
  unfold liftedTerminalOutput terminalOutput liftedTerminalAlice liftedTerminalBob
  rw [rightTensorOperation_rawInstrumentReindex _ _ _ _ _ _ MeasurableSet.univ,
    tensorOperation_rawInstrumentReindex _ _ _ _ _ _ MeasurableSet.univ]
  simp only [MeasurableEquiv.symm_apply_apply, preimage_univ]

theorem hasSum_lifted_terminal_rawPrefix_eq_apply (U : Protocol c d a b)
    (hc : 0 < c) (hd : 0 < d) (n : ℕ) (hn : depth U ≤ n) (X : JointMatrix a b) :
    HasSum (fun h : History (ULift.{u} ℕ) n => liftedTerminalOutput U n hc hd h
      (liftedRawPrefix U n h (codedJoint a b X))) (physicalJoint c d (U.apply X)) := by
  have hs := hasSum_terminal_rawPrefix_eq_apply U hc hd n hn X
  apply (historyEquiv natLiftEquiv.{u} n).toEquiv.hasSum_iff.mp
  simpa only [Function.comp_def, MeasurableEquiv.coe_toEquiv,
    liftedTerminalOutput_eq, liftedRawPrefix_eq] using hs

end QuantumProver.ElegantJointMeasurement.HilbertFiniteNormalRecordLift

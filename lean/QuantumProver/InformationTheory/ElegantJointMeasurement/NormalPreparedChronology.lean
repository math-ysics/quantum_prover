import QuantumProver.InformationTheory.ElegantJointMeasurement.CommonPhysicalTerminalRealization
import QuantumProver.QuantumChannels.NormalFreePreparationChronology

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory ProbabilityTheory Set Function InnerProductSpace
open scoped BigOperators Topology ComplexOrder Classical

namespace QuantumProver.ElegantJointMeasurement.NormalPreparedChronology

open QuantumProver.ElegantJointMeasurement.NormalProcess QuantumProver.ElegantJointMeasurement.HilbertSquareProcess QuantumProver.ElegantJointMeasurement.HilbertChoi
open QuantumProver.ElegantJointMeasurement.NuclearChoi QuantumProver.ElegantJointMeasurement.NormalInstrumentAbsorption
open QuantumProver.ElegantJointMeasurement.NormalInstrumentKraus QuantumProver.ElegantJointMeasurement.NormalCPInstruments
open QuantumProver.MatrixNormalStateKernel QuantumProver.MatrixNuclearKernelTransport
open QuantumProver.MatrixNuclearContinuationTransport
open QuantumProver.MatrixNormalFreePreparationChronology
open QuantumProver.ElegantJointMeasurement.HilbertCommonPhysicalTerminalRealization
open QuantumProver.NuclearOperator (toOperator)

universe u v

local instance stateNuclearMeasurable (a b : ℕ) :
    MeasurableSpace (Nuclear (PhysicalChoiWorkspace a b)) := borel _
local instance stateNuclearBorel (a b : ℕ) :
    BorelSpace (Nuclear (PhysicalChoiWorkspace a b)) := ⟨rfl⟩

section SeededChronology

variable {a b : ℕ} [NeZero a] [NeZero b]
  {R : Type u} [MeasurableSpace R] [StandardBorelSpace R]
  (P : MatrixProcess a b R)
  (L0 : MatrixProcess.PhysicalStateLayer (a := a) (b := b) (R := R) 0)

def seededStateLayers : (n : ℕ) →
    MatrixProcess.PhysicalStateLayer (a := a) (b := b) (R := R) n
  | 0 => L0
  | n+1 => (seededStateLayers n).successor P

def seededState (n : ℕ) : History R n → Nuclear (PhysicalChoiWorkspace a b) :=
  (seededStateLayers P L0 n).state

def seededBornKernel (n : ℕ) : Kernel (History R n) R :=
  (seededStateLayers P L0 n).kernel P

instance seededBornKernel_markov (n : ℕ) : IsMarkovKernel (seededBornKernel P L0 n) :=
  MatrixProcess.PhysicalStateLayer.isMarkovKernel_kernel P _

def seededPrefixMeasure : (n : ℕ) → Measure (History R n)
  | 0 => Measure.dirac PUnit.unit
  | n+1 => ((seededPrefixMeasure n) ⊗ₘ seededBornKernel P L0 n).map (appendHistory n)

instance seededPrefixMeasure_probability (n : ℕ) :
    IsProbabilityMeasure (seededPrefixMeasure P L0 n) := by
  induction n with
  | zero => change IsProbabilityMeasure (Measure.dirac PUnit.unit); infer_instance
  | succ n ih =>
      letI : IsProbabilityMeasure (seededPrefixMeasure P L0 n) := ih
      change IsProbabilityMeasure
        (((seededPrefixMeasure P L0 n) ⊗ₘ seededBornKernel P L0 n).map (appendHistory n))
      infer_instance

theorem stronglyMeasurable_seededState (n : ℕ) : StronglyMeasurable (seededState P L0 n) :=
  (seededStateLayers P L0 n).stronglyMeasurable_state

theorem seededState_positive (n : ℕ) (h : History R n) :
    (toOperator (seededState P L0 n h)).IsPositive :=
  (seededStateLayers P L0 n).positive h

theorem seededState_trace (n : ℕ) (h : History R n) :
    QuantumProver.HilbertNuclearTrace.trace (seededState P L0 n h) = 1 :=
  (seededStateLayers P L0 n).trace_one h

theorem seededState_norm (n : ℕ) (h : History R n) : ‖seededState P L0 n h‖ = 1 := by
  obtain ⟨I, basis, _⟩ := exists_hilbertBasis ℂ (PhysicalChoiWorkspace a b)
  rw [norm_positive_nuclear_eq_re_trace basis _ (seededState_positive P L0 n h),
    seededState_trace]
  rfl

theorem seededBornKernel_apply (n : ℕ) (h : History R n) (s : Set R)
    (hs : MeasurableSet s) :
    seededBornKernel P L0 n h s = ENNReal.ofReal
      (QuantumProver.HilbertNuclearTrace.trace
        ((P.represented_physicalReferenceInstrument n).operation h s (seededState P L0 n h))).re :=
  bornKernel_apply (P.represented_physicalReferenceInstrument n) (seededStateLayers P L0 n).state
    (seededStateLayers P L0 n).positive (seededStateLayers P L0 n).stronglyMeasurable_state
    (seededStateLayers P L0 n).trace_one h s hs

theorem seededState_successor (n : ℕ) (h : History R n) (r : R) :
    seededState P L0 (n+1) (appendHistory n (h,r)) =
      (seededStateLayers P L0 n).nextState P (h,r) :=
  MatrixProcess.PhysicalStateLayer.successor_append P (seededStateLayers P L0 n) h r

theorem seededState_successor_setIntegral (n : ℕ) (h : History R n)
    (s : Set R) (hs : MeasurableSet s) :
    (∫ r in s, seededState P L0 (n+1) (appendHistory n (h,r))
      ∂seededBornKernel P L0 n h) =
      (P.represented_physicalReferenceInstrument n).operation h s (seededState P L0 n h) := by
  calc
    (∫ r in s, seededState P L0 (n+1) (appendHistory n (h,r))
        ∂seededBornKernel P L0 n h) =
        ∫ r in s, (seededStateLayers P L0 n).nextState P (h,r)
          ∂seededBornKernel P L0 n h := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun r => seededState_successor P L0 n h r)
    _ = _ := (seededStateLayers P L0 n).nextState_setIntegral P h s hs

theorem seededState_integrable (n : ℕ) :
    Integrable (seededState P L0 n) (seededPrefixMeasure P L0 n) := by
  refine (integrable_const (1 : ℝ)).mono'
    (stronglyMeasurable_seededState P L0 n).aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall (fun h => (seededState_norm P L0 n h).le)

theorem seededState_append_integrable (n : ℕ) :
    Integrable (fun z : History R n × R => seededState P L0 (n+1) (appendHistory n z))
      ((seededPrefixMeasure P L0 n) ⊗ₘ seededBornKernel P L0 n) := by
  refine (integrable_const (1 : ℝ)).mono'
    ((stronglyMeasurable_seededState P L0 (n+1)).comp_measurable
      (appendHistory (R := R) n).measurable).aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall
    (fun z => (seededState_norm P L0 (n+1) (appendHistory n z)).le)

def seededPrefixVectorMeasure (n : ℕ) :
    VectorMeasure (History R n) (Nuclear (PhysicalChoiWorkspace a b)) :=
  (seededPrefixMeasure P L0 n).withDensityᵥ (seededState P L0 n)

theorem seededPrefixVectorMeasure_apply (n : ℕ) (s : Set (History R n))
    (hs : MeasurableSet s) :
    seededPrefixVectorMeasure P L0 n s =
      ∫ h in s, seededState P L0 n h ∂seededPrefixMeasure P L0 n :=
  withDensityᵥ_apply (seededState_integrable P L0 n) hs

theorem seededPrefixVectorMeasure_successorEvent (n : ℕ)
    (s : Set (History R n)) (t : Set R) (hs : MeasurableSet s) (ht : MeasurableSet t) :
    seededPrefixVectorMeasure P L0 (n+1) (MatrixProcess.successorEvent n s t) =
      ∫ h in s, (P.represented_physicalReferenceInstrument n).operation h t (seededState P L0 n h)
        ∂seededPrefixMeasure P L0 n := by
  rw [seededPrefixVectorMeasure_apply P L0 (n+1) _
    (MatrixProcess.measurableSet_successorEvent n s t hs ht)]
  change (∫ h in MatrixProcess.successorEvent n s t, seededState P L0 (n+1) h
    ∂(((seededPrefixMeasure P L0 n) ⊗ₘ seededBornKernel P L0 n).map (appendHistory n))) = _
  rw [setIntegral_map_equiv]
  have hp : (appendHistory (R := R) n) ⁻¹' MatrixProcess.successorEvent n s t = s ×ˢ t := by
    ext z
    simp only [MatrixProcess.successorEvent, Set.mem_preimage, MeasurableEquiv.symm_apply_apply]
  rw [hp, Measure.setIntegral_compProd hs ht (seededState_append_integrable P L0 n).integrableOn]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun h => seededState_successor_setIntegral P L0 n h t ht)

def seededInputDensity (n : ℕ) (X : JointInputMatrix a b) (h : History R n) :
    Nuclear JointWorkspace := chargedDecode X (seededState P L0 n h)

theorem seededInputDensity_integrable (n : ℕ) (X : JointInputMatrix a b) :
    Integrable (seededInputDensity P L0 n X) (seededPrefixMeasure P L0 n) :=
  (chargedDecode X).integrable_comp (seededState_integrable P L0 n)

def seededQuantumNuclearOutput {c d : ℕ} (N : ℕ) (Q : NormalTerminal R N c d)
    (X : JointInputMatrix a b) : Nuclear (TerminalWorkspace c d) :=
  ∫ h, terminalJointOperation Q h (seededInputDensity P L0 N X h)
    ∂seededPrefixMeasure P L0 N

def seededQuantumOutput {c d : ℕ} (N : ℕ) (Q : NormalTerminal R N c d)
    (X : JointInputMatrix a b) : JointInputMatrix c d :=
  finiteJointDecode c d (seededQuantumNuclearOutput P L0 N Q X)

theorem seededQuantumNuclearOutput_integrable {c d : ℕ} (N : ℕ)
    (Q : NormalTerminal R N c d) (X : JointInputMatrix a b) :
    Integrable (fun h => terminalJointOperation Q h (seededInputDensity P L0 N X h))
      (seededPrefixMeasure P L0 N) := by
  simpa only [id_eq] using
    integrable_continuation_field measurable_id (seededInputDensity_integrable P L0 N X)
      (terminalJointOperation Q) (stronglyMeasurable_terminalJointOperation Q)
      (terminalJointOperation_norm_le_one Q)

def seededPrefixAction (n : ℕ) (s : Set (History R n)) (X : JointInputMatrix a b) :
    Nuclear JointWorkspace := chargedDecode X (seededPrefixVectorMeasure P L0 n s)

theorem seededPrefixAction_apply (n : ℕ) (s : Set (History R n))
    (hs : MeasurableSet s) (X : JointInputMatrix a b) :
    seededPrefixAction P L0 n s X =
      ∫ h in s, seededInputDensity P L0 n X h ∂seededPrefixMeasure P L0 n := by
  rw [seededPrefixAction, seededPrefixVectorMeasure_apply P L0 n s hs]
  exact (chargedDecode X).integral_comp_comm (seededState_integrable P L0 n).restrict |>.symm

theorem seededPrefixAction_zero (X : JointInputMatrix a b) :
    seededPrefixAction P L0 0 univ X = chargedDecode X (L0.state PUnit.unit) := by
  rw [seededPrefixAction_apply P L0 0 univ MeasurableSet.univ X, setIntegral_univ]
  change (∫ h : History R 0, chargedDecode X (L0.state h) ∂Measure.dirac PUnit.unit) = _
  have he : L0.state = fun _ => L0.state PUnit.unit := by
    funext h
    exact congrArg L0.state (Subsingleton.elim h PUnit.unit)
  rw [he]
  simp

theorem seededPrefixAction_successorEvent (n : ℕ) (s : Set (History R n))
    (t : Set R) (hs : MeasurableSet s) (ht : MeasurableSet t) (X : JointInputMatrix a b) :
    seededPrefixAction P L0 (n+1) (MatrixProcess.successorEvent n s t) X =
      ∫ h in s, (P.represented_physicalStepInstrument n).operation h t (seededInputDensity P L0 n X h)
        ∂seededPrefixMeasure P L0 n := by
  rw [seededPrefixAction, seededPrefixVectorMeasure_successorEvent P L0 n s t hs ht]
  have hi : Integrable (fun h => (P.represented_physicalReferenceInstrument n).operation h t
      (seededState P L0 n h)) (seededPrefixMeasure P L0 n) := by
    simpa only [id_eq] using integrable_event_operation_field
      (P.represented_physicalReferenceInstrument n) measurable_id t ht (seededState_integrable P L0 n)
  rw [← (chargedDecode X).integral_comp_comm hi.restrict]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun h =>
    chargedDecode_normalAmplification ((P.represented_physicalStepInstrument n).operation h t)
      X (seededState P L0 n h))

theorem seededPrefixAction_trace_univ
    (hInitial : ∀ X : JointInputMatrix a b,
      QuantumProver.HilbertNuclearTrace.trace (chargedDecode X (L0.state PUnit.unit)) = X.trace)
    (n : ℕ) (X : JointInputMatrix a b) :
    QuantumProver.HilbertNuclearTrace.trace (seededPrefixAction P L0 n univ X) = X.trace := by
  induction n with
  | zero => rw [seededPrefixAction_zero]; exact hInitial X
  | succ n ih =>
      have hu : MatrixProcess.successorEvent (R := R) n univ univ = univ := by
        simp [MatrixProcess.successorEvent]
      rw [← hu, seededPrefixAction_successorEvent P L0 n univ univ
        MeasurableSet.univ MeasurableSet.univ X, setIntegral_univ]
      have hi : Integrable (fun h => (P.represented_physicalStepInstrument n).operation h univ
          (seededInputDensity P L0 n X h)) (seededPrefixMeasure P L0 n) := by
        simpa only [id_eq] using integrable_event_operation_field
          (P.represented_physicalStepInstrument n) measurable_id univ MeasurableSet.univ
          (seededInputDensity_integrable P L0 n X)
      rw [← (QuantumProver.HilbertNuclearTrace.trace (𝕜 := ℂ) (E := JointWorkspace)).integral_comp_comm hi]
      simp_rw [(P.represented_physicalStepInstrument n).trace_preserving]
      rw [(QuantumProver.HilbertNuclearTrace.trace (𝕜 := ℂ) (E := JointWorkspace)).integral_comp_comm
        (seededInputDensity_integrable P L0 n X)]
      rw [← setIntegral_univ, ← seededPrefixAction_apply P L0 n univ MeasurableSet.univ X]
      exact ih

end SeededChronology

section NormalizedTrace

variable {a b : ℕ}

theorem measure_eq_trace_setIntegral {A : Type*} [MeasurableSpace A]
    (μ : Measure A) [IsFiniteMeasure μ]
    (σ : A → Nuclear (PhysicalChoiWorkspace a b)) (hi : Integrable σ μ)
    (htrace : ∀ h, QuantumProver.HilbertNuclearTrace.trace (σ h) = 1)
    (s : Set A) :
    μ s = ENNReal.ofReal (QuantumProver.HilbertNuclearTrace.trace (∫ h in s, σ h ∂μ)).re := by
  have he : QuantumProver.HilbertNuclearTrace.trace (∫ h in s, σ h ∂μ) = ((μ s).toReal : ℂ) := by
    rw [← (QuantumProver.HilbertNuclearTrace.trace (𝕜 := ℂ)
      (E := PhysicalChoiWorkspace a b)).integral_comp_comm hi.restrict]
    simp [htrace, integral_const, Measure.real]
  rw [he]
  simpa only [Complex.ofReal_re] using (ENNReal.ofReal_toReal (measure_ne_top μ s)).symm

end NormalizedTrace

section TerminalPullback

variable {R : Type u} [MeasurableSpace R]

def pullbackShiftedTerminal {c d : ℕ} (n : ℕ)
    (Q : NormalTerminal (PreparationRecord R) (n+2) c d) : NormalTerminal R n c d where
  alice := pullbackTerminalInstrument Q.alice (padHistory n)
    (measurableEmbedding_padHistory n).measurable
  bob := pullbackTerminalInstrument Q.bob (padHistory n)
    (measurableEmbedding_padHistory n).measurable

theorem terminalJointOperation_pullbackShiftedTerminal {c d : ℕ} (n : ℕ)
    (Q : NormalTerminal (PreparationRecord R) (n+2) c d) (h : History R n) :
    terminalJointOperation (pullbackShiftedTerminal n Q) h =
      terminalJointOperation Q (padHistory n h) := rfl

end TerminalPullback

set_option maxHeartbeats 6000000

section PostTwoShift

variable {a b : ℕ} [NeZero a] [NeZero b]
  {R : Type u} [MeasurableSpace R] [StandardBorelSpace R]
  [StandardBorelSpace (PreparationRecord R)]
  (P : MatrixProcess a b R)
  (S : MatrixProcess a b (PreparationRecord R))
  (L0 : MatrixProcess.PhysicalStateLayer (a := a) (b := b) (R := R) 0)
  (hInitialMeasure : S.represented_physicalPrefixMeasure 2 = Measure.dirac preparationHistory)
  (hInitialState : S.represented_physicalState 2 preparationHistory = L0.state PUnit.unit)
  (hStep : ∀ n (h : History R n) (s : Set (PreparationRecord R)), MeasurableSet s →
    (S.represented_physicalReferenceInstrument (n+2)).operation (padHistory n h) s =
      (P.represented_physicalReferenceInstrument n).operation h (Sum.inr ⁻¹' s))

include hInitialMeasure hInitialState hStep

theorem seeded_prefix_setIntegral_shift (n : ℕ) (s : Set (History (PreparationRecord R) (n+2)))
    (hs : MeasurableSet s) :
    (∫ h in padHistory n ⁻¹' s, seededState P L0 n h ∂seededPrefixMeasure P L0 n) =
      ∫ h in s, S.represented_physicalState (n+2) h ∂S.represented_physicalPrefixMeasure (n+2) := by
  induction n with
  | zero =>
      rw [hInitialMeasure]
      change (∫ h : History R 0 in (fun _ => preparationHistory) ⁻¹' s,
        L0.state h ∂Measure.dirac PUnit.unit) = _
      have he : L0.state = fun _ => L0.state PUnit.unit := by
        funext h
        exact congrArg L0.state (Subsingleton.elim h PUnit.unit)
      rw [he, setIntegral_dirac' (S.stronglyMeasurable_physicalState 2) preparationHistory hs]
      by_cases hm : preparationHistory ∈ s
      · have hp : (fun _ : History R 0 => preparationHistory) ⁻¹' s = univ := by
          ext h; simp [hm]
        rw [hp, setIntegral_univ]
        simp [hm, hInitialState]
      · have hp : (fun _ : History R 0 => preparationHistory) ⁻¹' s = ∅ := by
          ext h; simp [hm]
        rw [hp, setIntegral_empty]
        simp [hm]
  | succ n ih =>
      letI : IsProbabilityMeasure (S.represented_physicalPrefixMeasure (n+2)) :=
        S.represented_physicalPrefixMeasure_probability (n+2)
      letI : IsMarkovKernel (S.represented_physicalBornKernel (n+2)) :=
        S.represented_physicalBornKernel_markov (n+2)
      have hset : ∀ t : Set (History (PreparationRecord R) (n+2)), MeasurableSet t →
          (∫ h in padHistory n ⁻¹' t, seededState P L0 n h ∂seededPrefixMeasure P L0 n) =
            ∫ h in t, S.represented_physicalState (n+2) h ∂S.represented_physicalPrefixMeasure (n+2) := by
        intro t ht
        exact ih t ht
      have he := setIntegral_kernel_transport (S.represented_physicalReferenceInstrument (n+2))
        (measurableEmbedding_padHistory n).measurable measurable_inr
        (seededState_integrable P L0 n) (S.represented_physicalState_integrable (n+2)) hset
        (seededBornKernel P L0 n) (S.represented_physicalBornKernel (n+2))
        (seededState_append_integrable P L0 n) (S.physicalState_append_integrable (n+2))
        (fun h t ht => by
          rw [seededState_successor_setIntegral P L0 n h (Sum.inr ⁻¹' t)
            (measurable_inr ht), hStep n h t ht])
        (fun h t ht => S.represented_physicalState_successor_setIntegral (n+2) h t ht)
      specialize he ((appendHistory (R := PreparationRecord R) (n+2)) ⁻¹' s)
        (hs.preimage (appendHistory (R := PreparationRecord R) (n+2)).measurable)
      change (∫ h in padHistory (n+1) ⁻¹' s, seededState P L0 (n+1) h
        ∂(((seededPrefixMeasure P L0 n) ⊗ₘ seededBornKernel P L0 n).map (appendHistory n))) =
          ∫ h in s, S.represented_physicalState (n+2+1) h
            ∂(((S.represented_physicalPrefixMeasure (n+2)) ⊗ₘ S.represented_physicalBornKernel (n+2)).map
              (appendHistory (n+2)))
      rw [setIntegral_map_equiv, setIntegral_map_equiv]
      have hc : (appendHistory (R := R) n) ⁻¹' (padHistory (n+1) ⁻¹' s) =
          Prod.map (padHistory n) (Sum.inr : R → PreparationRecord R) ⁻¹'
            ((appendHistory (R := PreparationRecord R) (n+2)) ⁻¹' s) := by
        ext z
        change padHistory (n+1) (appendHistory n z) ∈ s ↔
          appendHistory (n+2) (padHistory n z.1, Sum.inr z.2) ∈ s
        rw [padHistory_append]
      rw [hc]
      exact he

theorem seededPrefixMeasure_shift (n : ℕ) :
    S.represented_physicalPrefixMeasure (n+2) = (seededPrefixMeasure P L0 n).map (padHistory n) := by
  letI : IsProbabilityMeasure (S.represented_physicalPrefixMeasure (n+2)) :=
    S.represented_physicalPrefixMeasure_probability (n+2)
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply (measurableEmbedding_padHistory n).measurable hs,
    measure_eq_trace_setIntegral (S.represented_physicalPrefixMeasure (n+2))
      (S.represented_physicalState (n+2)) (S.represented_physicalState_integrable (n+2)) (S.physicalState_trace (n+2)) s,
    measure_eq_trace_setIntegral (seededPrefixMeasure P L0 n)
      (seededState P L0 n) (seededState_integrable P L0 n) (seededState_trace P L0 n)
      (padHistory n ⁻¹' s),
    seeded_prefix_setIntegral_shift P S L0 hInitialMeasure hInitialState hStep n s hs]

theorem seededState_shift_ae (n : ℕ) :
    seededState P L0 n =ᵐ[seededPrefixMeasure P L0 n]
      (fun h => S.represented_physicalState (n+2) (padHistory n h)) := by
  have hμ := seededPrefixMeasure_shift P S L0 hInitialMeasure hInitialState hStep n
  have hi : Integrable (fun h => S.represented_physicalState (n+2) (padHistory n h))
      (seededPrefixMeasure P L0 n) := by
    have ht := S.represented_physicalState_integrable (n+2)
    rw [hμ] at ht
    exact ht.comp_measurable (measurableEmbedding_padHistory n).measurable
  apply Integrable.ae_eq_of_forall_setIntegral_eq _ _ (seededState_integrable P L0 n) hi
  intro s hs _
  have he := seeded_prefix_setIntegral_shift P S L0 hInitialMeasure hInitialState hStep n
    (padHistory n '' s) ((measurableEmbedding_padHistory n).measurableSet_image' hs)
  rw [(measurableEmbedding_padHistory n).injective.preimage_image,
    hμ, (measurableEmbedding_padHistory n).setIntegral_map,
    (measurableEmbedding_padHistory n).injective.preimage_image] at he
  exact he

theorem seededPrefixAction_shift (n : ℕ) (s : Set (History R n))
    (hs : MeasurableSet s) (X : JointInputMatrix a b) :
    seededPrefixAction P L0 n s X = S.represented_physicalPrefixAction (n+2) (padHistory n '' s) X := by
  have he := seeded_prefix_setIntegral_shift P S L0 hInitialMeasure hInitialState hStep n
    (padHistory n '' s) ((measurableEmbedding_padHistory n).measurableSet_image' hs)
  rw [(measurableEmbedding_padHistory n).injective.preimage_image] at he
  change chargedDecode X (seededPrefixVectorMeasure P L0 n s) =
    chargedDecode X (S.represented_physicalPrefixVectorMeasure (n+2) (padHistory n '' s))
  rw [seededPrefixVectorMeasure_apply P L0 n s hs,
    S.represented_physicalPrefixVectorMeasure_apply (n+2) _
      ((measurableEmbedding_padHistory n).measurableSet_image' hs), he]

theorem seeded_continuation_shift {V : Type v} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [CompleteSpace V] (n : ℕ)
    (Ψ : History (PreparationRecord R) (n+2) →
      Nuclear (PhysicalChoiWorkspace a b) →L[ℂ] Nuclear V)
    (hΨ : ∀ T, StronglyMeasurable (fun h => Ψ h T))
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ h, ‖Ψ h‖ ≤ C) :
    (∫ h, Ψ (padHistory n h) (seededState P L0 n h) ∂seededPrefixMeasure P L0 n) =
      ∫ h, Ψ h (S.represented_physicalState (n+2) h) ∂S.represented_physicalPrefixMeasure (n+2) := by
  letI : IsProbabilityMeasure (S.represented_physicalPrefixMeasure (n+2)) :=
    S.represented_physicalPrefixMeasure_probability (n+2)
  exact integral_continuation_eq_of_preimage_setIntegral_eq
    (measurableEmbedding_padHistory n).measurable
    (seededState_integrable P L0 n) (S.represented_physicalState_integrable (n+2))
    (fun s hs => seeded_prefix_setIntegral_shift P S L0 hInitialMeasure hInitialState hStep n s hs)
    Ψ hΨ hC hbound

theorem seededQuantumNuclearOutput_shift {c d : ℕ} (n : ℕ)
    (Q : NormalTerminal (PreparationRecord R) (n+2) c d) (X : JointInputMatrix a b) :
    S.physicalQuantumNuclearOutput (n+2) Q X =
      seededQuantumNuclearOutput P L0 n (pullbackShiftedTerminal n Q) X := by
  let Ψ : History (PreparationRecord R) (n+2) →
      Nuclear (PhysicalChoiWorkspace a b) →L[ℂ] Nuclear (TerminalWorkspace c d) :=
    fun h => (terminalJointOperation Q h).comp (chargedDecode X)
  have hΨ (T : Nuclear (PhysicalChoiWorkspace a b)) : StronglyMeasurable (fun h => Ψ h T) :=
    stronglyMeasurable_terminalJointOperation Q (chargedDecode X T)
  have hbound (h : History (PreparationRecord R) (n+2)) : ‖Ψ h‖ ≤ ‖chargedDecode X‖ := by
    have hm := mul_le_mul_of_nonneg_right (terminalJointOperation_norm_le_one Q h)
      (norm_nonneg (chargedDecode X))
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (by simpa only [one_mul] using hm)
  have he := seeded_continuation_shift P S L0 hInitialMeasure hInitialState hStep n
    Ψ hΨ (norm_nonneg (chargedDecode X)) hbound
  change (∫ h, terminalJointOperation Q (padHistory n h) (seededInputDensity P L0 n X h)
      ∂seededPrefixMeasure P L0 n) = S.physicalQuantumNuclearOutput (n+2) Q X at he
  rw [← he]
  simp only [seededQuantumNuclearOutput, terminalJointOperation_pullbackShiftedTerminal]

theorem seededQuantumOutput_shift {c d : ℕ} (n : ℕ)
    (Q : NormalTerminal (PreparationRecord R) (n+2) c d) (X : JointInputMatrix a b) :
    S.represented_physicalQuantumOutput (n+2) Q X =
      seededQuantumOutput P L0 n (pullbackShiftedTerminal n Q) X :=
  congrArg (finiteJointDecode c d)
    (seededQuantumNuclearOutput_shift P S L0 hInitialMeasure hInitialState hStep n Q X)

end PostTwoShift
end QuantumProver.ElegantJointMeasurement.NormalPreparedChronology

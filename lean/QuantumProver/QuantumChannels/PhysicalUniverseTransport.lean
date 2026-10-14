import QuantumProver.QuantumChannels.PhysicalProtocolData
import QuantumProver.QuantumChannels.PhysicalUniverseHilbert
import QuantumProver.QuantumChannels.PhysicalUniverseInstruments
import QuantumProver.InformationTheory.ElegantJointMeasurement.NormalPhysicalBornTransport
import QuantumProver.InformationTheory.ElegantJointMeasurement.NormalPhysicalOutputTransport

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory Set Function InnerProductSpace
open QuantumProver.ElegantJointMeasurement.MeasurableHilbertField QuantumProver.ElegantJointMeasurement.MeasurableNormalInstrument
open QuantumProver.ElegantJointMeasurement.NormalProcess QuantumProver.ElegantJointMeasurement.NormalPhysicalAdmission
open QuantumProver.ElegantJointMeasurement.NormalPhysicalTerminalAdmission QuantumProver.ElegantJointMeasurement.NormalInstrumentAbsorption
open QuantumProver.ElegantJointMeasurement.HilbertRecordCoding QuantumProver.ElegantJointMeasurement.PhysicalTranscriptCoding QuantumProver.ElegantJointMeasurement.HilbertSquareProcess
open QuantumProver.ElegantJointMeasurement.NormalPhysicalOperationalBridge
open QuantumProver.MatrixNormalSourceCompletion QuantumProver.MatrixPhysicalUniverseHilbert
open QuantumProver.MatrixPhysicalUniverseInstruments QuantumProver.ElegantJointMeasurement.SeparableHilbertEmbedding
open scoped Topology Classical ComplexOrder

namespace QuantumProver.ElegantJointMeasurement.PhysicalCost

namespace PhysicalHilbert

def ulift.{r,v} (E : PhysicalHilbert.{v}) : PhysicalHilbert.{max v r} where
  carrier := ULift.{r} E
  normed := inferInstance
  innerProduct := inferInstance
  complete := inferInstance

end PhysicalHilbert

namespace PhysicalProtocol

def ulift.{r,s,u,v,w} {a b : ℕ} (P : PhysicalProtocol.{u,v,w} a b) : PhysicalProtocol.{u,max v r,max w s} a b where
  outcome := P.outcome
  domains := P.domains
  alice n h := PhysicalHilbert.ulift.{r} (P.alice n h)
  bob n h := PhysicalHilbert.ulift.{r} (P.bob n h)
  aliceSections n := uliftFamily.{r} (P.aliceSections n)
  bobSections n := uliftFamily.{r} (P.bobSections n)
  aliceOutput n z := PhysicalHilbert.ulift.{s} (P.aliceOutput n z)
  bobOutput n z := PhysicalHilbert.ulift.{s} (P.bobOutput n z)
  aliceOutputSections n := uliftFamily.{s} (P.aliceOutputSections n)
  bobOutputSections n := uliftFamily.{s} (P.bobOutputSections n)
  aliceWiring := uliftWiring.{r,s} P.Outcomes P.domains true
    P.aliceSections P.aliceOutputSections P.aliceWiring
  bobWiring := uliftWiring.{r,s} P.Outcomes P.domains false
    P.bobSections P.bobOutputSections P.bobWiring
  aliceInstrument := uliftPhysicalLocalFamily.{r,s} P.Outcomes P.domains true
    P.aliceSections P.aliceOutputSections P.aliceInstrument
  bobInstrument := uliftPhysicalLocalFamily.{r,s} P.Outcomes P.domains false
    P.bobSections P.bobOutputSections P.bobInstrument
  chargedAlice := (uliftUnitary.{r} (P.alice 0 P.domains.initialHistory)).toLinearIsometry.comp P.chargedAlice
  chargedBob := (uliftUnitary.{r} (P.bob 0 P.domains.initialHistory)).toLinearIsometry.comp P.chargedBob

end PhysicalProtocol

namespace PhysicalReadout

def ulift.{r,s,u,v,w} {a b N c d : ℕ} {P : PhysicalProtocol.{u,v,w} a b}
    (Q : PhysicalReadout P N c d) : PhysicalReadout P.ulift.{r,s} N c d where
  alice := uliftInputMatrixInstrument.{r} (P.aliceSections N) (finiteOutputFamily c) Q.alice
  bob := uliftInputMatrixInstrument.{r} (P.bobSections N) (finiteOutputFamily d) Q.bob

end PhysicalReadout
end QuantumProver.ElegantJointMeasurement.PhysicalCost

universe u v w r s

namespace QuantumProver.MatrixPhysicalUniverseTransport

section Extensionality

variable {H : Type u} [MeasurableSpace H]
  {E : H → Type v} {G : H → Type w}
  [∀ h, NormedAddCommGroup (E h)] [∀ h, InnerProductSpace ℂ (E h)]
  [∀ h, CompleteSpace (E h)]
  [∀ h, NormedAddCommGroup (G h)] [∀ h, InnerProductSpace ℂ (G h)]
  [∀ h, CompleteSpace (G h)]

omit [∀ h, CompleteSpace (E h)] in
theorem fundamentalFamily_eq_of_vector (F Q : FundamentalFamily E)
    (h : F.vector = Q.vector) : F = Q := by
  cases F
  cases Q
  cases h
  rfl

theorem instrument_eq_of_operation
    {X Y H Ω : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X]
    [CompleteSpace X] [NormedAddCommGroup Y] [InnerProductSpace ℂ Y]
    [CompleteSpace Y] [MeasurableSpace H] [MeasurableSpace Ω]
    (P Q : Instrument X Y H Ω) (h : P.operation = Q.operation) : P = Q := by
  cases P
  cases Q
  cases h
  rfl

theorem matrixProcess_eq_of_data
    {R : Type*} [MeasurableSpace R] {a b : ℕ}
    (P Q : MatrixProcess a b R)
    (hA : P.initialAlice = Q.initialAlice) (hB : P.initialBob = Q.initialBob)
    (hIA : P.alice = Q.alice) (hIB : P.bob = Q.bob)
    (hparty : P.aliceTurn = Q.aliceTurn) : P = Q := by
  cases P
  cases Q
  cases hA
  cases hB
  cases hIA
  cases hIB
  cases hparty
  rfl

theorem completeSourceInstrument_eq_of_code
    {Ω : Type*} [MeasurableSpace Ω] {F : FundamentalFamily E}
    {Q : FundamentalFamily G} (P : SourceInstrument F Ω) (L : SourceInstrument Q Ω)
    (hop : ∀ h t, sourceCodedOperation P h t = sourceCodedOperation L h t)
    (hproj : ∀ h, F.rangeProjection h = Q.rangeProjection h) :
    completeSourceInstrument P = completeSourceInstrument L := by
  apply instrument_eq_of_operation
  funext h t
  change sourceCodedOperation P h (Sum.inl ⁻¹' t) +
      (if Sum.inr () ∈ t then
        QuantumProver.ElegantJointMeasurement.NormalInstrumentCompletion.complementReset
          QuantumProver.ElegantJointMeasurement.NormalInstrumentCompletion.commonResetVector (F.rangeProjection h) else 0) =
    sourceCodedOperation L h (Sum.inl ⁻¹' t) +
      (if Sum.inr () ∈ t then
        QuantumProver.ElegantJointMeasurement.NormalInstrumentCompletion.complementReset
          QuantumProver.ElegantJointMeasurement.NormalInstrumentCompletion.commonResetVector (Q.rangeProjection h) else 0)
  rw [hop, hproj]

theorem completePhysicalTerminalLocal_eq_of_code
    {c : ℕ} {F : FundamentalFamily E} {Q : FundamentalFamily G}
    (P : MatrixInstrument F (finiteOutputFamily (H := H) c) PUnit.{u+1})
    (L : MatrixInstrument Q (finiteOutputFamily (H := H) c) PUnit.{u+1})
    (hc : 0 < c)
    (hop : ∀ h t, terminalSourceOperation P h t = terminalSourceOperation L h t)
    (hproj : ∀ h, F.rangeProjection h = Q.rangeProjection h) :
    completePhysicalTerminalLocal P hc = completePhysicalTerminalLocal L hc := by
  apply instrument_eq_of_operation
  funext h t
  change terminalSourceOperation P h (Sum.inl ⁻¹' (terminalCollapse ⁻¹' t)) +
      (if Sum.inr () ∈ terminalCollapse ⁻¹' t then
        QuantumProver.ElegantJointMeasurement.NormalInstrumentCompletion.complementReset
          (finiteResetVector hc) (F.rangeProjection h) else 0) =
    terminalSourceOperation L h (Sum.inl ⁻¹' (terminalCollapse ⁻¹' t)) +
      (if Sum.inr () ∈ terminalCollapse ⁻¹' t then
        QuantumProver.ElegantJointMeasurement.NormalInstrumentCompletion.complementReset
          (finiteResetVector hc) (Q.rangeProjection h) else 0)
  rw [hop, hproj]

end Extensionality

section ChronologicalTransport

variable (Ω : ℕ → Type u) [∀ n, MeasurableSpace (Ω n)]
  [∀ n, StandardBorelSpace (Ω n)] (D : PhysicalDomains Ω) (b : Bool)
  {E : (n : ℕ) → D.admissible n → Type v}
  [∀ n h, NormedAddCommGroup (E n h)] [∀ n h, InnerProductSpace ℂ (E n h)]
  [∀ n h, CompleteSpace (E n h)]
  (F : (n : ℕ) → FundamentalFamily (E n))
  {G : (n : ℕ) → D.actingDomain n b × Ω n → Type w}
  [∀ n z, NormedAddCommGroup (G n z)] [∀ n z, InnerProductSpace ℂ (G n z)]
  [∀ n z, CompleteSpace (G n z)]
  (Q : (n : ℕ) → FundamentalFamily (G n))
  (W : PhysicalMemoryWiring Ω D b F Q)

theorem selectedMemory_ulift_vector (n : ℕ) (h : D.admissible n) (i : ℕ) :
    (selectedMemory Ω D b (fun n => uliftFamily.{r} (F n)) (fun n => uliftFamily.{s} (Q n)) (uliftWiring.{r,s} Ω D b F Q W) n).family.vector h i =
      ULift.up ((selectedMemory Ω D b F Q W n).family.vector h i) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [selectedMemory, chooseNextMemory, glueFamily]
      split_ifs
      · simp only [actedNextFamily, transportFamily, outputOnSuccessor,
          pullbackFamily, uliftFamily_vector, uliftWiring_acted_apply_up]
      · simp only [idleNextFamily, transportFamily, pullbackFamily]
        rw [ih, uliftWiring_idle_apply_up]
      · rfl

theorem selectedMemory_ulift_family (n : ℕ) :
    (selectedMemory Ω D b (fun n => uliftFamily.{r} (F n)) (fun n => uliftFamily.{s} (Q n)) (uliftWiring.{r,s} Ω D b F Q W) n).family =
      uliftFamily.{r} (selectedMemory Ω D b F Q W n).family := by
  apply fundamentalFamily_eq_of_vector
  funext h i
  exact selectedMemory_ulift_vector Ω D b F Q W n h i

theorem selectedMemory_ulift_embedding (n : ℕ) (h : D.admissible n)
    (x : E n h) :
    (selectedMemory Ω D b (fun n => uliftFamily.{r} (F n)) (fun n => uliftFamily.{s} (Q n)) (uliftWiring.{r,s} Ω D b F Q W) n).family.embedding h (ULift.up x) =
      (selectedMemory Ω D b F Q W n).family.embedding h x := by
  rw [selectedMemory_ulift_family]
  exact uliftFamily_embedding _ h x

theorem selectedMemory_ulift_rangeProjection (n : ℕ) (h : D.admissible n) :
    (selectedMemory Ω D b (fun n => uliftFamily.{r} (F n)) (fun n => uliftFamily.{s} (Q n)) (uliftWiring.{r,s} Ω D b F Q W) n).family.rangeProjection h =
      (selectedMemory Ω D b F Q W n).family.rangeProjection h := by
  rw [selectedMemory_ulift_family]
  exact uliftFamily_rangeProjection _ h

theorem chosenActiveSource_ulift (n : ℕ) :
    chosenActiveSource Ω D b (fun n => uliftFamily.{r} (F n)) (fun n => uliftFamily.{s} (Q n)) (uliftWiring.{r,s} Ω D b F Q W) n =
      uliftFamily.{r} (chosenActiveSource Ω D b F Q W n) := by
  unfold chosenActiveSource
  rw [selectedMemory_ulift_family]
  exact (uliftFamily_pullback _ _ _).symm

variable (P : PhysicalLocalFamily Ω D b F Q)

theorem retargetedPhysicalInstrument_ulift_sourceCode
    (n : ℕ) (h : D.actingDomain n b) (t : Set (Ω n)) :
    sourceCodedOperation (retargetedPhysicalInstrument Ω D b (fun n => uliftFamily.{r} (F n)) (fun n => uliftFamily.{s} (Q n)) (uliftWiring.{r,s} Ω D b F Q W) (uliftPhysicalLocalFamily.{r,s} Ω D b F Q P) n).represented_physical h t =
      sourceCodedOperation (retargetedPhysicalInstrument Ω D b F Q W P n).represented_physical h t := by
  ext U
  change ((uliftPhysicalLocalFamily.{r,s} Ω D b F Q P).instrument n).represented_physical.operation h t
      (recoverNuclear ((chosenActiveSource Ω D b (fun n => uliftFamily.{r} (F n)) (fun n => uliftFamily.{s} (Q n)) (uliftWiring.{r,s} Ω D b F Q W) n).embedding h) U) =
    (P.instrument n).represented_physical.operation h t
      (recoverNuclear ((chosenActiveSource Ω D b F Q W n).embedding h) U)
  rw [uliftPhysicalLocalFamily_operation, chosenActiveSource_ulift,
    recoverNuclear_ulift_embedding]
  simp only [recover_padNuclear]

theorem admittedMemoryTurn_ulift (n : ℕ) :
    admittedMemoryTurn Ω D b (fun n => uliftFamily.{r} (F n)) (fun n => uliftFamily.{s} (Q n)) (uliftWiring.{r,s} Ω D b F Q W) (uliftPhysicalLocalFamily.{r,s} Ω D b F Q P) n =
      admittedMemoryTurn Ω D b F Q W P n := by
  have hproj : ∀ h : D.actingDomain n b,
      (chosenActiveSource Ω D b (fun n => uliftFamily.{r} (F n))
        (fun n => uliftFamily.{s} (Q n)) (uliftWiring.{r,s} Ω D b F Q W) n).rangeProjection h =
      (chosenActiveSource Ω D b F Q W n).rangeProjection h := by
    intro h
    change (selectedMemory Ω D b (fun n => uliftFamily.{r} (F n)) (fun n => uliftFamily.{s} (Q n)) (uliftWiring.{r,s} Ω D b F Q W) n).family.rangeProjection
      (D.actingHistory n b h) =
      (selectedMemory Ω D b F Q W n).family.rangeProjection (D.actingHistory n b h)
    exact selectedMemory_ulift_rangeProjection Ω D b F Q W n _
  have hcomplete :
      completeSourceInstrument
        (retargetedPhysicalInstrument Ω D b (fun n => uliftFamily.{r} (F n))
          (fun n => uliftFamily.{s} (Q n)) (uliftWiring.{r,s} Ω D b F Q W)
          (uliftPhysicalLocalFamily.{r,s} Ω D b F Q P) n).represented_physical =
      completeSourceInstrument (retargetedPhysicalInstrument Ω D b F Q W P n).represented_physical :=
    completeSourceInstrument_eq_of_code _ _
      (retargetedPhysicalInstrument_ulift_sourceCode Ω D b F Q W P n) hproj
  exact congrArg
    (fun I : Instrument CommonHilbert CommonHilbert (D.actingDomain n b) (Ω n ⊕ Unit) =>
      liftInstrumentAlongEmbedding I
        (fun h : D.actingDomain n b => encodeHistory Ω n h.val)
        (measurableEmbedding_encodeAdmissibleHistory Ω n (D.actingDomain n b)
          (D.measurableSet_actingDomain n b))
        (completedOutcome Ω n) (measurable_completedOutcome Ω n) (dummyRecord Ω)) hcomplete

theorem chargedInitialMemory_ulift {d : ℕ}
    (J : EuclideanSpace ℂ (Fin d) →ₗᵢ[ℂ] E 0 D.initialHistory) :
    chargedInitialMemory Ω D b (fun n => uliftFamily.{r} (F n)) (fun n => uliftFamily.{s} (Q n)) (uliftWiring.{r,s} Ω D b F Q W)
      ((uliftUnitary.{r} (E 0 D.initialHistory)).toLinearIsometry.comp J) =
      chargedInitialMemory Ω D b F Q W J := by
  apply LinearIsometry.ext
  intro x
  change (uliftFamily.{r} (F 0)).embedding D.initialHistory (ULift.up (J x)) =
    (F 0).embedding D.initialHistory (J x)
  exact uliftFamily_embedding _ _ _

end ChronologicalTransport

section TerminalTransport

variable (Ω : ℕ → Type u) [∀ n, MeasurableSpace (Ω n)]
  [∀ n, StandardBorelSpace (Ω n)] (D : PhysicalDomains Ω) (b : Bool)
  {E : (n : ℕ) → D.admissible n → Type v}
  [∀ n h, NormedAddCommGroup (E n h)] [∀ n h, InnerProductSpace ℂ (E n h)]
  [∀ n h, CompleteSpace (E n h)]
  (F : (n : ℕ) → FundamentalFamily (E n))
  {G : (n : ℕ) → D.actingDomain n b × Ω n → Type w}
  [∀ n z, NormedAddCommGroup (G n z)] [∀ n z, InnerProductSpace ℂ (G n z)]
  [∀ n z, CompleteSpace (G n z)]
  (Q : (n : ℕ) → FundamentalFamily (G n))
  (W : PhysicalMemoryWiring Ω D b F Q)
  (N c : ℕ)
  (T : MatrixInstrument (F N) (finiteOutputFamily (H := D.admissible N) c) PUnit.{u+1})

theorem retargetedTerminal_ulift_sourceCode (h : D.admissible N)
    (t : Set PUnit.{u+1}) :
    terminalSourceOperation
      (retargetTerminalSource ((fun n => uliftFamily.{r} (F n)) N) ((selectedMemory Ω D b (fun n => uliftFamily.{r} (F n)) (fun n => uliftFamily.{s} (Q n)) (uliftWiring.{r,s} Ω D b F Q W) N).family) c
        (uliftInputMatrixInstrument.{r} (F N) (finiteOutputFamily c) T)
        (selectedMemory Ω D b (fun n => uliftFamily.{r} (F n)) (fun n => uliftFamily.{s} (Q n)) (uliftWiring.{r,s} Ω D b F Q W) N).intrinsic) h t =
      terminalSourceOperation
        (retargetTerminalSource (F N) ((selectedMemory Ω D b F Q W N).family) c T
          (selectedMemory Ω D b F Q W N).intrinsic) h t := by
  ext U
  change (uliftInputMatrixInstrument.{r} (F N) (finiteOutputFamily c) T).operation h t
      (recoverNuclear (((selectedMemory Ω D b (fun n => uliftFamily.{r} (F n)) (fun n => uliftFamily.{s} (Q n)) (uliftWiring.{r,s} Ω D b F Q W) N).family).embedding h) U) =
    T.operation h t (recoverNuclear (((selectedMemory Ω D b F Q W N).family).embedding h) U)
  rw [uliftInputMatrixInstrument_operation, selectedMemory_ulift_family,
    recoverNuclear_ulift_embedding]
  simp only [recover_padNuclear]

theorem completeRetargetedTerminal_ulift (hc : 0 < c) :
    completePhysicalTerminalLocal
      (retargetTerminalSource ((fun n => uliftFamily.{r} (F n)) N) ((selectedMemory Ω D b (fun n => uliftFamily.{r} (F n)) (fun n => uliftFamily.{s} (Q n)) (uliftWiring.{r,s} Ω D b F Q W) N).family) c
        (uliftInputMatrixInstrument.{r} (F N) (finiteOutputFamily c) T)
        (selectedMemory Ω D b (fun n => uliftFamily.{r} (F n)) (fun n => uliftFamily.{s} (Q n)) (uliftWiring.{r,s} Ω D b F Q W) N).intrinsic) hc =
      completePhysicalTerminalLocal
        (retargetTerminalSource (F N) ((selectedMemory Ω D b F Q W N).family) c T
          (selectedMemory Ω D b F Q W N).intrinsic) hc := by
  apply completePhysicalTerminalLocal_eq_of_code
  · exact retargetedTerminal_ulift_sourceCode Ω D b F Q W N c T
  · exact selectedMemory_ulift_rangeProjection Ω D b F Q W N

end TerminalTransport
end QuantumProver.MatrixPhysicalUniverseTransport

namespace QuantumProver.ElegantJointMeasurement.PhysicalCost

open QuantumProver.MatrixPhysicalUniverseTransport

namespace PhysicalProtocol

variable {a b : ℕ}

@[simp] theorem ulift_Outcomes (P : PhysicalProtocol.{u,v,w} a b) :
    P.ulift.{r,s}.Outcomes = P.Outcomes := rfl

@[simp] theorem ulift_domains (P : PhysicalProtocol.{u,v,w} a b) :
    P.ulift.{r,s}.domains = P.domains := rfl

@[simp] theorem ulift_chargedAlice_apply (P : PhysicalProtocol.{u,v,w} a b)
    (x : EuclideanSpace ℂ (Fin a)) : P.ulift.{r,s}.chargedAlice x = ULift.up (P.chargedAlice x) := rfl

@[simp] theorem ulift_chargedBob_apply (P : PhysicalProtocol.{u,v,w} a b)
    (x : EuclideanSpace ℂ (Fin b)) : P.ulift.{r,s}.chargedBob x = ULift.up (P.chargedBob x) := rfl

@[simp] theorem matrix_ulift (P : PhysicalProtocol.{u,v,w} a b) :
    P.ulift.{r,s}.represented = P.represented := by
  apply matrixProcess_eq_of_data
  · exact chargedInitialMemory_ulift P.Outcomes P.domains true
      P.aliceSections P.aliceOutputSections P.aliceWiring P.chargedAlice
  · exact chargedInitialMemory_ulift P.Outcomes P.domains false
      P.bobSections P.bobOutputSections P.bobWiring P.chargedBob
  · funext n
    exact admittedMemoryTurn_ulift P.Outcomes P.domains true
      P.aliceSections P.aliceOutputSections P.aliceWiring P.aliceInstrument n
  · funext n
    exact admittedMemoryTurn_ulift P.Outcomes P.domains false
      P.bobSections P.bobOutputSections P.bobWiring P.bobInstrument n
  · rfl

end PhysicalProtocol

namespace PhysicalReadout

variable {a b N c d : ℕ} {P : PhysicalProtocol.{u,v,w} a b}

theorem alice_operation_ulift (Q : PhysicalReadout P N c d)
    (h : P.domains.admissible N) (t : Set PUnit.{u+1})
    (T : Nuc (P.alice N h)) :
    Q.ulift.{r,s}.alice.operation h t
      (padNuclear (uliftUnitary.{r} (P.alice N h)).toLinearIsometry T) =
      Q.alice.operation h t T := by
  change (uliftInputMatrixInstrument.{r} (P.aliceSections N) (finiteOutputFamily c) Q.alice).operation
    h t (padNuclear (uliftUnitary.{r} (P.alice N h)).toLinearIsometry T) = _
  rw [uliftInputMatrixInstrument_operation, recover_padNuclear]

theorem bob_operation_ulift (Q : PhysicalReadout P N c d)
    (h : P.domains.admissible N) (t : Set PUnit.{u+1})
    (T : Nuc (P.bob N h)) :
    Q.ulift.{r,s}.bob.operation h t
      (padNuclear (uliftUnitary.{r} (P.bob N h)).toLinearIsometry T) =
      Q.bob.operation h t T := by
  change (uliftInputMatrixInstrument.{r} (P.bobSections N) (finiteOutputFamily d) Q.bob).operation
    h t (padNuclear (uliftUnitary.{r} (P.bob N h)).toLinearIsometry T) = _
  rw [uliftInputMatrixInstrument_operation, recover_padNuclear]

@[simp] theorem matrix_ulift (Q : PhysicalReadout P N c d) (hc : 0 < c) (hd : 0 < d) :
    Q.ulift.{r,s}.represented hc hd = Q.represented hc hd := by
  have hA := completeRetargetedTerminal_ulift P.Outcomes P.domains true
    P.aliceSections P.aliceOutputSections P.aliceWiring N c Q.alice hc
  have hB := completeRetargetedTerminal_ulift P.Outcomes P.domains false
    P.bobSections P.bobOutputSections P.bobWiring N d Q.bob hd
  simp only [represented, ulift, PhysicalProtocol.ulift, ofPhysicalTerminal,
    retargetedTerminalAlice, retargetedTerminalBob] at hA hB ⊢
  rw [hA, hB]

theorem terminalInputAction_ulift (Q : PhysicalReadout P N c d)
    (hc : 0 < c) (hd : 0 < d)
    (h : History (CommonRecord P.Outcomes) N)
    (T : QuantumProver.ElegantJointMeasurement.NuclearChoi.Nuclear (JointWorkspace)) :
    terminalJointOperation (Q.ulift.{r,s}.represented hc hd) h T =
      terminalJointOperation (Q.represented hc hd) h T := by
  rw [matrix_ulift]

end PhysicalReadout

end QuantumProver.ElegantJointMeasurement.PhysicalCost

namespace QuantumProver.MatrixPhysicalUniverseTransport

open QuantumProver.ElegantJointMeasurement.PhysicalCost

section LiteralPhysicalLaws

variable {a b : ℕ} [NeZero a] [NeZero b]

def protocolBornMeasure (P : PhysicalProtocol.{u,v,w} a b)
    (X : JointInputMatrix a b) (hX : X.PosSemidef) : Measure (PhysicalTranscript P.Outcomes) :=
  physicalBornMeasure P.Outcomes P.domains P.aliceSections P.bobSections
    P.aliceOutputSections P.bobOutputSections P.aliceWiring P.bobWiring
    P.aliceInstrument P.bobInstrument P.chargedAlice P.chargedBob X hX

theorem protocolBornMeasure_ulift (P : PhysicalProtocol.{u,v,w} a b)
    (X : JointInputMatrix a b) (hX : X.PosSemidef) :
    protocolBornMeasure P.ulift.{r,s} X hX = protocolBornMeasure P X hX := by
  unfold protocolBornMeasure physicalBornMeasure
  rw [physicalCodedBornMeasure_eq_admitted, physicalCodedBornMeasure_eq_admitted]
  change (P.ulift.{r,s}.represented.represented_physicalBornMeasure X hX).comap (encodePhysicalTranscript P.Outcomes) =
    (P.represented.represented_physicalBornMeasure X hX).comap (encodePhysicalTranscript P.Outcomes)
  rw [PhysicalProtocol.matrix_ulift]

theorem protocolBornMeasure_ulift_event (P : PhysicalProtocol.{u,v,w} a b)
    (X : JointInputMatrix a b) (hX : X.PosSemidef) (t : Set (PhysicalTranscript P.Outcomes)) :
    protocolBornMeasure P.ulift.{r,s} X hX t = protocolBornMeasure P X hX t := by
  exact congrArg (fun μ : Measure (PhysicalTranscript P.Outcomes) => μ t)
    (protocolBornMeasure_ulift P X hX)

def protocolQuantumOutput (P : PhysicalProtocol.{u,v,w} a b)
    {N c d : ℕ} (Q : PhysicalReadout P N c d) (X : JointInputMatrix a b) : JointInputMatrix c d :=
  represented_physicalPhysicalQuantumOutput P.Outcomes P.domains P.aliceSections P.bobSections
    P.aliceOutputSections P.bobOutputSections P.aliceWiring P.bobWiring
    P.aliceInstrument P.bobInstrument P.chargedAlice P.chargedBob
    N c d Q.alice Q.bob X

theorem protocolQuantumOutput_ulift (P : PhysicalProtocol.{u,v,w} a b)
    {N c d : ℕ} (Q : PhysicalReadout P N c d) (hc : 0 < c) (hd : 0 < d)
    (X : JointInputMatrix a b) :
    protocolQuantumOutput P.ulift.{r,s} Q.ulift.{r,s} X = protocolQuantumOutput P Q X := by
  unfold protocolQuantumOutput
  rw [physicalPhysicalQuantumOutput_eq_admitted _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hc hd X,
    physicalPhysicalQuantumOutput_eq_admitted _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hc hd X]
  change P.ulift.{r,s}.represented.represented_physicalQuantumOutput N (Q.ulift.{r,s}.represented hc hd) X =
    P.represented.represented_physicalQuantumOutput N (Q.represented hc hd) X
  rw [PhysicalProtocol.matrix_ulift, PhysicalReadout.matrix_ulift]

end LiteralPhysicalLaws
end QuantumProver.MatrixPhysicalUniverseTransport

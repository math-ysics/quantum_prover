import QuantumProver.InformationTheory.ElegantJointMeasurement.NormalPhysicalAdmission
import QuantumProver.InformationTheory.ElegantJointMeasurement.NormalProcess

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory Set Function InnerProductSpace
open scoped BigOperators Topology Classical

namespace QuantumProver.ElegantJointMeasurement.NormalPhysicalTerminalAdmission

open QuantumProver.ElegantJointMeasurement.NormalProcess QuantumProver.ElegantJointMeasurement.HilbertRecordCoding QuantumProver.ElegantJointMeasurement.HilbertSquareProcess
open QuantumProver.ElegantJointMeasurement.MeasurableHilbertField QuantumProver.ElegantJointMeasurement.SeparableHilbertEmbedding
open QuantumProver.ElegantJointMeasurement.MeasurableNormalInstrument QuantumProver.ElegantJointMeasurement.NormalInstrumentAbsorption
open QuantumProver.ElegantJointMeasurement.NormalInstrumentCompletion QuantumProver.ElegantJointMeasurement.NormalSandwich
open QuantumProver.ElegantJointMeasurement.NuclearChoi QuantumProver.ElegantJointMeasurement.HilbertChoi
open QuantumProver.ElegantJointMeasurement.NormalPhysicalAdmission
open QuantumProver.MatrixNormalSourceCompletion QuantumProver.MatrixNuclearTensor
open QuantumProver.MatrixNormalTensorInstrument QuantumProver.MatrixNormalRightTensor
open QuantumProver.NuclearOperator (toOperator toOperator_injective)
open QuantumProver.HilbertNuclearCompression (compose)

universe u v w

abbrev FiniteOutput (c : ℕ) := EuclideanSpace ℂ (Fin c)

def finiteOutputVector (c n : ℕ) : FiniteOutput c :=
  if h : n < c then EuclideanSpace.basisFun (Fin c) ℂ ⟨n,h⟩ else 0

theorem finiteOutputVector_dense (c : ℕ) :
    (Submodule.span ℂ (range (finiteOutputVector c))).topologicalClosure = ⊤ := by
  have hi : range (EuclideanSpace.basisFun (Fin c) ℂ) ⊆
      range (finiteOutputVector c) := by
    rintro x ⟨i,rfl⟩
    exact ⟨i.val, by simp [finiteOutputVector, i.isLt]⟩
  have hs := Submodule.span_mono (R := ℂ) hi
  have hb : Submodule.span ℂ (range (EuclideanSpace.basisFun (Fin c) ℂ)) = ⊤ :=
    (EuclideanSpace.basisFun (Fin c) ℂ).toBasis.span_eq
  rw [hb] at hs
  have he : Submodule.span ℂ (range (finiteOutputVector c)) = ⊤ := top_le_iff.mp hs
  simp [he]

def finiteOutputFamily {H : Type*} [MeasurableSpace H] (c : ℕ) :
    FundamentalFamily (fun _ : H => FiniteOutput c) where
  vector _ := finiteOutputVector c
  pairingMeasurable _ _ := measurable_const
  dense _ := finiteOutputVector_dense c

def finiteOutputEmbedding (c : ℕ) : FiniteOutput c →ₗᵢ[ℂ] CommonHilbert :=
  QuantumProver.CountableGramSchmidt.coordinateEmbedding (finiteOutputVector c)
    (finiteOutputVector_dense c)

@[simp] theorem finiteOutputFamily_embedding {H : Type*} [MeasurableSpace H]
    (c : ℕ) (h : H) :
    (finiteOutputFamily (H := H) c).embedding h = finiteOutputEmbedding c := rfl

def finiteResetVector {c : ℕ} (hc : 0 < c) : FiniteOutput c :=
  EuclideanSpace.basisFun (Fin c) ℂ ⟨0,hc⟩

theorem norm_finiteResetVector {c : ℕ} (hc : 0 < c) : ‖finiteResetVector hc‖ = 1 :=
  (EuclideanSpace.basisFun (Fin c) ℂ).orthonormal.1 ⟨0,hc⟩

section PhysicalLocalTerminal

variable {H : Type u} [MeasurableSpace H] {E : H → Type v}
  [∀ h, NormedAddCommGroup (E h)] [∀ h, InnerProductSpace ℂ (E h)]
  [∀ h, CompleteSpace (E h)]

def retargetTerminalSource (F F' : FundamentalFamily E) (c : ℕ)
    (P : MatrixInstrument F (finiteOutputFamily (H := H) c) PUnit.{u+1})
    (hF' : ∀ i, F.IsMeasurableSection (fun h => F'.vector h i)) :
    MatrixInstrument F' (finiteOutputFamily (H := H) c) PUnit.{u+1} where
  operation := P.operation
  empty := P.empty
  countable_additivity := P.countable_additivity
  completelyPositive := P.completelyPositive
  trace_preserving := P.trace_preserving
  fundamental_measurable s hs i j k l :=
    measurable_operation_rankOne_coordinate F (finiteOutputFamily (H := H) c)
      (fun h => P.operation h s) (P.fundamental_measurable s hs)
      (fun h => F'.vector h i) (fun h => F'.vector h j) (hF' i) (hF' j) k l

@[simp] theorem retargetTerminalSource_operation (F F' : FundamentalFamily E) (c : ℕ)
    (P : MatrixInstrument F (finiteOutputFamily (H := H) c) PUnit.{u+1})
    (hF' : ∀ i, F.IsMeasurableSection (fun h => F'.vector h i))
    (h : H) (s : Set PUnit.{u+1}) :
    (retargetTerminalSource F F' c P hF').operation h s = P.operation h s := rfl

variable {F : FundamentalFamily E} {c : ℕ}
  (P : MatrixInstrument F (finiteOutputFamily (H := H) c) PUnit.{u+1})

def physicalTerminalLocal (h : H) : Instrument (E h) (FiniteOutput c) Unit PUnit.{u+1} where
  operation _ := P.operation h
  empty _ := P.empty h
  countable_additivity _ := P.countable_additivity h
  completelyPositive _ := P.completelyPositive h
  measurable_coordinate _ _ _ _ _ := measurable_const
  trace_preserving _ := P.trace_preserving h

@[simp] theorem physicalTerminalLocal_operation (h : H) (s : Set PUnit.{u+1}) :
    (physicalTerminalLocal P h).operation () s = P.operation h s := rfl

def terminalSourceOperation (h : H) (s : Set PUnit.{u+1}) :
    NormalOperation CommonHilbert (FiniteOutput c) :=
  (P.operation h s).comp (recoverNuclear (F.embedding h))

theorem terminalSourceOperation_on_physical (h : H) (s : Set PUnit.{u+1}) (T : Nuc (E h)) :
    terminalSourceOperation P h s (padNuclear (F.embedding h) T) = P.operation h s T := by
  simp only [terminalSourceOperation, ContinuousLinearMap.comp_apply, recover_padNuclear]

theorem stronglyMeasurable_terminalSourceOperation (s : Set PUnit.{u+1}) (hs : MeasurableSet s)
    (U : Nuc CommonHilbert) : StronglyMeasurable (fun h => terminalSourceOperation P h s U) := by
  have hm := P.stronglyMeasurable_codedOperation s hs U
  have hr := (recoverNuclear (finiteOutputEmbedding c)).continuous.comp_stronglyMeasurable hm
  have he : (fun h => recoverNuclear (finiteOutputEmbedding c) (P.codedOperation h s U)) =
      fun h => terminalSourceOperation P h s U := by
    funext h
    simp only [MatrixInstrument.codedOperation, encodedOperation,
      ContinuousLinearMap.comp_apply, finiteOutputFamily_embedding, recover_padNuclear,
      terminalSourceOperation]
  rw [he] at hr
  exact hr

theorem terminalSourceOperation_total_trace (h : H) (U : Nuc CommonHilbert) :
    QuantumProver.HilbertNuclearTrace.trace (terminalSourceOperation P h univ U) =
      QuantumProver.HilbertNuclearTrace.trace (sandwich (F.rangeProjection h) U) := by
  change QuantumProver.HilbertNuclearTrace.trace (P.operation h univ (recoverNuclear (F.embedding h) U)) = _
  rw [P.trace_preserving]
  rw [sandwich, inputProjection_adjoint]
  rw [← QuantumProver.ElegantJointMeasurement.MeasurableNuclearField.pad_recover_eq_projection, trace_padNuclear]

def terminalRangeInstrument : RangeInstrument CommonHilbert (FiniteOutput c) H PUnit.{u+1} where
  inputProjection := F.rangeProjection
  projection_adjoint := inputProjection_adjoint F
  projection_idempotent := inputProjection_idempotent F
  operation := terminalSourceOperation P
  empty h := by
    ext U
    simp only [terminalSourceOperation, ContinuousLinearMap.comp_apply, P.empty,
      ContinuousLinearMap.zero_apply]
  countable_additivity h s hs hd U := P.countable_additivity h s hs hd (recoverNuclear (F.embedding h) U)
  completelyPositive h s hs :=
    normalCompletelyPositive_comp _ _ (P.completelyPositive h s hs)
      (recoverNuclear_completelyPositive (F := F) h)
  measurable_coordinate s hs U x y := by
    let L : Nuc (FiniteOutput c) →L[ℂ] ℂ :=
      (innerSL ℂ x).comp ((ContinuousLinearMap.apply ℂ (FiniteOutput c) y).comp toOperator)
    exact (L.continuous.comp_stronglyMeasurable
      (stronglyMeasurable_terminalSourceOperation P s hs U)).measurable
  trace_on_range := terminalSourceOperation_total_trace P

def terminalCollapse : PUnit.{u+1} ⊕ Unit → PUnit.{u+1} := fun _ => PUnit.unit

theorem terminalCollapse_physical_preimage (s : Set PUnit.{u+1}) :
    Sum.inl ⁻¹' (terminalCollapse ⁻¹' s) = s := by
  ext x
  cases x
  rfl

def completePhysicalTerminalLocal (hc : 0 < c) :
    Instrument CommonHilbert (FiniteOutput c) H PUnit.{u+1} :=
  pushforwardInstrument ((terminalRangeInstrument P).complete
    (finiteResetVector hc) (norm_finiteResetVector hc)) terminalCollapse measurable_const

theorem completePhysicalTerminalLocal_on_physical (hc : 0 < c)
    (h : H) (s : Set PUnit.{u+1}) (T : Nuc (E h)) :
    (completePhysicalTerminalLocal P hc).operation h s (padNuclear (F.embedding h) T) =
      P.operation h s T := by
  change (terminalRangeInstrument P).completedOperation (finiteResetVector hc) h
    (terminalCollapse ⁻¹' s) (sandwich (F.embedding h).toContinuousLinearMap T) = _
  rw [RangeInstrument.completedOperation_supported_input (terminalRangeInstrument P)
    (finiteResetVector hc) h (terminalCollapse ⁻¹' s)
    (F.embedding h).toContinuousLinearMap (sourceProjection_embedding (F := F) h),
    terminalCollapse_physical_preimage]
  exact terminalSourceOperation_on_physical P h s T

end PhysicalLocalTerminal

section RectangularHistoryExtension

variable {X Y H K : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]
  [MeasurableSpace H] [MeasurableSpace K]

def finiteResetInstrument (φ : Y) (hφ : ‖φ‖ = 1) : Instrument X Y H PUnit.{u+1} where
  operation _ s := if PUnit.unit ∈ s then tracePrepare φ else 0
  empty _ := by simp
  countable_additivity _ s _ hd T := by
    have he (s : Set PUnit.{u+1}) :
        (if PUnit.unit ∈ s then (tracePrepare φ : NormalOperation X Y) else 0) T =
          if PUnit.unit ∈ s then tracePrepare φ T else 0 := by split_ifs <;> rfl
    convert dummy_hasSum PUnit.unit s hd (tracePrepare φ T) using 1
    · funext n
      exact he (s n)
    · exact he (⋃ n, s n)
  completelyPositive _ s _ := by
    split_ifs
    · exact normalCompletelyPositive_tracePrepare φ
    · exact normalCompletelyPositive_zero
  measurable_coordinate _ _ _ _ _ := measurable_const
  trace_preserving _ T := by
    simp only [mem_univ, ite_true]
    exact tracePrepare_trace_preserving φ hφ T

def liftRectangularTerminal (P : Instrument X Y H PUnit.{u+1}) (e : H → K)
    (he : MeasurableEmbedding e) (φ : Y) (hφ : ‖φ‖ = 1) : Instrument X Y K PUnit.{u+1} where
  operation k s := if hk : k ∈ range e then
      P.operation (he.equivRange.symm ⟨k,hk⟩) s
    else (finiteResetInstrument (X := X) (H := Unit) φ hφ).operation () s
  empty k := by split_ifs <;> simp [P.empty, finiteResetInstrument]
  countable_additivity k s hs hd T := by
    split_ifs with hk
    · exact P.countable_additivity (he.equivRange.symm ⟨k,hk⟩) s hs hd T
    · exact (finiteResetInstrument (X := X) (H := Unit) φ hφ).countable_additivity () s hs hd T
  completelyPositive k s hs := by
    split_ifs
    · exact P.completelyPositive _ s hs
    · exact (finiteResetInstrument (X := X) (H := Unit) φ hφ).completelyPositive () s hs
  measurable_coordinate s hs T x y := by
    have hm : Measurable (fun k : range e => inner ℂ x
        (toOperator (P.operation (he.equivRange.symm k) s T) y)) :=
      (P.measurable_coordinate s hs T x y).comp he.equivRange.symm.measurable
    have hm' : Measurable (fun _ : {k : K // k ∉ range e} => inner ℂ x
        (toOperator ((finiteResetInstrument (X := X) (H := Unit) φ hφ).operation () s T) y)) :=
      measurable_const
    convert hm.dite hm' he.measurableSet_range using 1
    funext k
    split_ifs <;> rfl
  trace_preserving k T := by
    split_ifs
    · exact P.trace_preserving _ T
    · exact (finiteResetInstrument (X := X) (H := Unit) φ hφ).trace_preserving () T

theorem liftRectangularTerminal_encoded (P : Instrument X Y H PUnit.{u+1}) (e : H → K)
    (he : MeasurableEmbedding e) (φ : Y) (hφ : ‖φ‖ = 1) (h : H) (s : Set PUnit.{u+1}) :
    (liftRectangularTerminal P e he φ hφ).operation (e h) s = P.operation h s := by
  simp only [liftRectangularTerminal, mem_range_self, ↓reduceDIte,
    he.equivRange_symm_apply_mk]

theorem liftRectangularTerminal_off_range (P : Instrument X Y H PUnit.{u+1}) (e : H → K)
    (he : MeasurableEmbedding e) (φ : Y) (hφ : ‖φ‖ = 1)
    (k : K) (hk : k ∉ range e) (s : Set PUnit.{u+1}) :
    (liftRectangularTerminal P e he φ hφ).operation k s =
      (finiteResetInstrument (X := X) (H := Unit) φ hφ).operation () s := by
  simp only [liftRectangularTerminal, dif_neg hk]

end RectangularHistoryExtension

section PhysicalTerminalFamily

variable (Ω : ℕ → Type u) [∀ n, MeasurableSpace (Ω n)]
  [∀ n, StandardBorelSpace (Ω n)] (D : PhysicalDomains Ω)
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
  (N c d : ℕ)
  (TA : MatrixInstrument (FA N) (finiteOutputFamily (H := D.admissible N) c) PUnit.{u+1})
  (TB : MatrixInstrument (FB N) (finiteOutputFamily (H := D.admissible N) d) PUnit.{u+1})

def retargetedTerminalAlice :
    MatrixInstrument (selectedMemory Ω D true FA QA WA N).family
      (finiteOutputFamily (H := D.admissible N) c) PUnit.{u+1} :=
  retargetTerminalSource (FA N) (selectedMemory Ω D true FA QA WA N).family c TA
    (selectedMemory Ω D true FA QA WA N).intrinsic

def retargetedTerminalBob :
    MatrixInstrument (selectedMemory Ω D false FB QB WB N).family
      (finiteOutputFamily (H := D.admissible N) d) PUnit.{u+1} :=
  retargetTerminalSource (FB N) (selectedMemory Ω D false FB QB WB N).family d TB
    (selectedMemory Ω D false FB QB WB N).intrinsic

def ofPhysicalTerminal (hc : 0 < c) (hd : 0 < d) : NormalTerminal (CommonRecord Ω) N c d where
  alice := liftRectangularTerminal
    (completePhysicalTerminalLocal (retargetedTerminalAlice Ω D FA QA WA N c TA) hc)
    (fun h : D.admissible N => encodeHistory Ω N h.val)
    (measurableEmbedding_encodeAdmissibleHistory Ω N (D.admissible N) (D.admissible_measurable N))
    (finiteResetVector hc) (norm_finiteResetVector hc)
  bob := liftRectangularTerminal
    (completePhysicalTerminalLocal (retargetedTerminalBob Ω D FB QB WB N d TB) hd)
    (fun h : D.admissible N => encodeHistory Ω N h.val)
    (measurableEmbedding_encodeAdmissibleHistory Ω N (D.admissible N) (D.admissible_measurable N))
    (finiteResetVector hd) (norm_finiteResetVector hd)

theorem ofPhysicalTerminal_alice_on_physical (hc : 0 < c) (hd : 0 < d)
    (h : D.admissible N) (s : Set PUnit.{u+1}) (T : Nuc (EA N h)) :
    (ofPhysicalTerminal Ω D FA FB QA QB WA WB N c d TA TB hc hd).alice.operation
      (encodeHistory Ω N h.val) s
      (padNuclear ((selectedMemory Ω D true FA QA WA N).family.embedding h) T) =
      TA.operation h s T := by
  change (liftRectangularTerminal _ _ _ _ _).operation _ s _ = _
  rw [liftRectangularTerminal_encoded]
  exact completePhysicalTerminalLocal_on_physical
    (retargetedTerminalAlice Ω D FA QA WA N c TA) hc h s T

theorem ofPhysicalTerminal_bob_on_physical (hc : 0 < c) (hd : 0 < d)
    (h : D.admissible N) (s : Set PUnit.{u+1}) (T : Nuc (EB N h)) :
    (ofPhysicalTerminal Ω D FA FB QA QB WA WB N c d TA TB hc hd).bob.operation
      (encodeHistory Ω N h.val) s
      (padNuclear ((selectedMemory Ω D false FB QB WB N).family.embedding h) T) =
      TB.operation h s T := by
  change (liftRectangularTerminal _ _ _ _ _).operation _ s _ = _
  rw [liftRectangularTerminal_encoded]
  exact completePhysicalTerminalLocal_on_physical
    (retargetedTerminalBob Ω D FB QB WB N d TB) hd h s T

def physicalTerminalJointOperation (h : D.admissible N) :
    Nuc (Joint (EA N h) (EB N h)) →L[ℂ] Nuc (TerminalWorkspace c d) :=
  (rightTensorOperation (F := EB N h) (E := FiniteOutput d) (G := FiniteOutput c)
    (physicalTerminalLocal TB h) () univ).comp
    (tensorOperation (F := EA N h) (E := FiniteOutput c) (G := EB N h)
      (physicalTerminalLocal TA h) () univ)

set_option maxHeartbeats 6000000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

theorem terminalJointOperation_physical_code_comp (hc : 0 < c) (hd : 0 < d)
    (h : D.admissible N) :
    (terminalJointOperation (ofPhysicalTerminal Ω D FA FB QA QB WA WB N c d TA TB hc hd)
      (encodeHistory Ω N h.val)).comp
      (physicalJointCode (X := EA N h) (X' := EB N h)
        (Y := CommonHilbert) (Y' := CommonHilbert)
        ((selectedMemory Ω D true FA QA WA N).family.embedding h)
        ((selectedMemory Ω D false FB QB WB N).family.embedding h)) =
      physicalTerminalJointOperation Ω D FA FB N c d TA TB h := by
  apply nuclear_joint_clm_ext_tensors (E := EA N h) (E' := EA N h) (F := EB N h) (F' := EB N h)
  intro T U
  simp only [ContinuousLinearMap.comp_apply, physicalJointCode_tensor]
  rw [terminalJointOperation_product,
    ofPhysicalTerminal_alice_on_physical Ω D FA FB QA QB WA WB N c d TA TB hc hd h univ T,
    ofPhysicalTerminal_bob_on_physical Ω D FA FB QA QB WA WB N c d TA TB hc hd h univ U]
  simp only [physicalTerminalJointOperation, ContinuousLinearMap.comp_apply]
  rw [tensorOperation_tensor (physicalTerminalLocal TA h) () univ MeasurableSet.univ T U,
    rightTensorOperation_tensor (physicalTerminalLocal TB h) () univ MeasurableSet.univ]
  rfl

theorem terminalJointOperation_on_physical_code (hc : 0 < c) (hd : 0 < d)
    (h : D.admissible N) (U : Nuc (Joint (EA N h) (EB N h))) :
    terminalJointOperation (ofPhysicalTerminal Ω D FA FB QA QB WA WB N c d TA TB hc hd)
      (encodeHistory Ω N h.val)
      (physicalJointCode (X := EA N h) (X' := EB N h)
        (Y := CommonHilbert) (Y' := CommonHilbert)
        ((selectedMemory Ω D true FA QA WA N).family.embedding h)
        ((selectedMemory Ω D false FB QB WB N).family.embedding h) U) =
      physicalTerminalJointOperation Ω D FA FB N c d TA TB h U := by
  exact congrArg (fun L => L U)
    (terminalJointOperation_physical_code_comp Ω D FA FB QA QB WA WB N c d TA TB hc hd h)

section FiniteReference

variable {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]
local instance terminalBlockComplete {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [CompleteSpace V] : CompleteSpace (BlockSpace I V) :=
  PiLp.completeSpace 2 (fun _ : I => V)

theorem terminalJointOperation_on_physical_code_reference (hc : 0 < c) (hd : 0 < d)
    (h : D.admissible N) (U : Nuc (BlockSpace I (Joint (EA N h) (EB N h)))) :
    normalAmplification (R := I)
      (terminalJointOperation (ofPhysicalTerminal Ω D FA FB QA QB WA WB N c d TA TB hc hd)
        (encodeHistory Ω N h.val))
      (normalAmplification (R := I)
        (physicalJointCode (X := EA N h) (X' := EB N h)
          (Y := CommonHilbert) (Y' := CommonHilbert)
          ((selectedMemory Ω D true FA QA WA N).family.embedding h)
          ((selectedMemory Ω D false FB QB WB N).family.embedding h)) U) =
      normalAmplification (R := I) (physicalTerminalJointOperation Ω D FA FB N c d TA TB h) U := by
  have he := congrArg (fun L => normalAmplification (R := I) L U)
    (terminalJointOperation_physical_code_comp Ω D FA FB QA QB WA WB N c d TA TB hc hd h)
  rw [normalAmplification_comp] at he
  exact he

end FiniteReference
end PhysicalTerminalFamily
end QuantumProver.ElegantJointMeasurement.NormalPhysicalTerminalAdmission

import QuantumProver.QuantumChannels.NormalSourceCompletion

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory Set Function InnerProductSpace
open scoped BigOperators Topology Classical

namespace QuantumProver.MatrixCommonPhysicalInstrument

open QuantumProver.ElegantJointMeasurement.SeparableHilbertEmbedding QuantumProver.ElegantJointMeasurement.MeasurableHilbertField
open QuantumProver.ElegantJointMeasurement.MeasurableNormalInstrument QuantumProver.ElegantJointMeasurement.NormalInstrumentAbsorption
open QuantumProver.ElegantJointMeasurement.NormalSandwich QuantumProver.ElegantJointMeasurement.HilbertChoi
open QuantumProver.ElegantJointMeasurement.NormalRecordedAbsorption QuantumProver.ElegantJointMeasurement.HilbertRecordedHilbertInstrument
open QuantumProver.MatrixNormalSourceCompletion
open QuantumProver.NuclearOperator (toOperator)
open QuantumProver.HilbertNuclearCompression (compose toOperator_compose)

theorem commonFrame_eq_commonBasis (n : ℕ) :
    QuantumProver.CountableGramSchmidt.frame commonBasis n = commonBasis n := by
  have hGS : InnerProductSpace.gramSchmidt ℂ commonBasis = commonBasis :=
    InnerProductSpace.gramSchmidt_of_orthogonal ℂ commonBasis.orthonormal.2
  simp [QuantumProver.CountableGramSchmidt.frame, InnerProductSpace.gramSchmidtNormed,
    hGS, commonBasis.orthonormal.1 n]

@[simp] theorem commonCoordinateEmbedding_apply_eq_self (x : CommonHilbert) :
    commonCoordinateEmbedding x = x := by
  apply lp.ext
  funext n
  change QuantumProver.CountableGramSchmidt.coordinateEmbedding commonBasis
    commonBasis.dense_span x n = x n
  rw [QuantumProver.CountableGramSchmidt.coordinateEmbedding_apply,
    commonFrame_eq_commonBasis, QuantumProver.CountableFrameProjection.commonBasis_inner]

theorem commonCoordinateEmbedding_eq_id :
    commonCoordinateEmbedding = (LinearIsometry.id : CommonHilbert →ₗᵢ[ℂ] CommonHilbert) := by
  apply LinearIsometry.ext
  exact commonCoordinateEmbedding_apply_eq_self

theorem commonCoordinateEmbedding_surjective :
    Function.Surjective commonCoordinateEmbedding :=
  fun x => ⟨x, commonCoordinateEmbedding_apply_eq_self x⟩

def commonCoordinateUnitary : CommonHilbert ≃ₗᵢ[ℂ] CommonHilbert :=
  LinearIsometryEquiv.ofSurjective commonCoordinateEmbedding commonCoordinateEmbedding_surjective

@[simp] theorem commonCoordinateUnitary_apply (x : CommonHilbert) :
    commonCoordinateUnitary x = commonCoordinateEmbedding x := rfl

theorem commonCoordinateEmbedding_clm_eq_id :
    commonCoordinateEmbedding.toContinuousLinearMap =
      ContinuousLinearMap.id ℂ CommonHilbert := by
  rw [commonCoordinateEmbedding_eq_id]
  rfl

theorem commonCoordinateEmbedding_unitary :
    commonCoordinateEmbedding.toContinuousLinearMap.comp
        commonCoordinateEmbedding.toContinuousLinearMap.adjoint =
      ContinuousLinearMap.id ℂ CommonHilbert ∧
    commonCoordinateEmbedding.toContinuousLinearMap.adjoint.comp
        commonCoordinateEmbedding.toContinuousLinearMap =
      ContinuousLinearMap.id ℂ CommonHilbert := by
  simp only [commonCoordinateEmbedding_clm_eq_id, ContinuousLinearMap.adjoint_id,
    ContinuousLinearMap.id_comp, and_self]

@[simp] theorem padNuclear_commonCoordinateEmbedding (T : Nuc CommonHilbert) :
    padNuclear commonCoordinateEmbedding T = T := by
  apply QuantumProver.NuclearOperator.toOperator_injective
  rw [toOperator_padNuclear, commonCoordinateEmbedding_clm_eq_id,
    ContinuousLinearMap.adjoint_id, ContinuousLinearMap.id_comp,
    ContinuousLinearMap.comp_id]

@[simp] theorem recoverNuclear_commonCoordinateEmbedding (T : Nuc CommonHilbert) :
    recoverNuclear commonCoordinateEmbedding T = T := by
  simpa only [padNuclear_commonCoordinateEmbedding] using
    recover_padNuclear commonCoordinateEmbedding T

variable {H Ω : Type*} [MeasurableSpace H] [MeasurableSpace Ω]

theorem commonFundamentalFamily_rangeProjection_eq_id (h : H) :
    (commonFundamentalFamily (H := H)).rangeProjection h =
      ContinuousLinearMap.id ℂ CommonHilbert := by
  change commonCoordinateEmbedding.toContinuousLinearMap.comp
    commonCoordinateEmbedding.toContinuousLinearMap.adjoint = _
  exact commonCoordinateEmbedding_unitary.1

variable {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]

def fixedFundamentalFamily (v : ℕ → Y)
    (hv : (Submodule.span ℂ (range v)).topologicalClosure = ⊤) :
    FundamentalFamily (fun _ : H => Y) where
  vector _ := v
  pairingMeasurable _ _ := measurable_const
  dense _ := hv

def matrixInstrument (P : Instrument CommonHilbert Y H Ω) (v : ℕ → Y)
    (hv : (Submodule.span ℂ (range v)).topologicalClosure = ⊤) :
    MatrixInstrument (commonFundamentalFamily (H := H))
      (fixedFundamentalFamily (H := H) v hv) Ω where
  operation h s := (P.operation h s).comp (padNuclear commonCoordinateEmbedding)
  empty h := by
    ext T
    simp only [ContinuousLinearMap.comp_apply, P.empty, ContinuousLinearMap.zero_apply]
  countable_additivity h s hs hd T :=
    P.countable_additivity h s hs hd (padNuclear commonCoordinateEmbedding T)
  completelyPositive h s hs :=
    normalCompletelyPositive_comp _ _ (P.completelyPositive h s hs)
      (by simpa only [padNuclear, sandwich] using
        normalCompletelyPositive_sandwich commonCoordinateEmbedding.toContinuousLinearMap)
  fundamental_measurable s hs := by
    intro i j k l
    exact P.measurable_coordinate s hs
      (padNuclear commonCoordinateEmbedding
        (QuantumProver.NuclearOperator.rankOne (innerSL ℂ (commonBasis i)) (commonBasis j)))
      (v k) (v l)
  trace_preserving h T := by
    change QuantumProver.HilbertNuclearTrace.trace
      (P.operation h univ (padNuclear commonCoordinateEmbedding T)) = _
    rw [P.trace_preserving, trace_padNuclear]

@[simp] theorem matrixInstrument_operation (P : Instrument CommonHilbert Y H Ω)
    (v : ℕ → Y) (hv : (Submodule.span ℂ (range v)).topologicalClosure = ⊤)
    (h : H) (s : Set Ω) :
    (matrixInstrument P v hv).operation h s = P.operation h s := by
  apply ContinuousLinearMap.ext
  intro T
  change P.operation h s (padNuclear commonCoordinateEmbedding T) = _
  rw [padNuclear_commonCoordinateEmbedding]

theorem stronglyMeasurable_matrixInstrument_operation [TopologicalSpace.SeparableSpace Y]
    (P : Instrument CommonHilbert Y H Ω) (v : ℕ → Y)
    (hv : (Submodule.span ℂ (range v)).topologicalClosure = ⊤)
    (s : Set Ω) (hs : MeasurableSet s) (T : Nuc CommonHilbert) :
    StronglyMeasurable (fun h => (matrixInstrument P v hv).operation h s T) := by
  simp only [matrixInstrument_operation]
  exact stronglyMeasurable_of_weak_coordinates _ (P.measurable_coordinate s hs T)

def sourceInstrument (P : Instrument CommonHilbert CommonHilbert H Ω) :
    SourceInstrument (commonFundamentalFamily (H := H)) Ω :=
  matrixInstrument P commonBasis commonBasis.dense_span

@[simp] theorem sourceInstrument_operation (P : Instrument CommonHilbert CommonHilbert H Ω)
    (h : H) (s : Set Ω) :
    (sourceInstrument P).operation h s = P.operation h s :=
  matrixInstrument_operation P commonBasis commonBasis.dense_span h s

@[simp] theorem sourceInstrument_operation_apply
    (P : Instrument CommonHilbert CommonHilbert H Ω) (h : H) (s : Set Ω)
    (T : Nuc CommonHilbert) : (sourceInstrument P).operation h s T = P.operation h s T := by
  rw [sourceInstrument_operation]

@[simp] theorem sourceCodedOperation_sourceInstrument
    (P : Instrument CommonHilbert CommonHilbert H Ω) (h : H) (s : Set Ω) :
    sourceCodedOperation (sourceInstrument P) h s = P.operation h s := by
  apply ContinuousLinearMap.ext
  intro T
  change (sourceInstrument P).operation h s (recoverNuclear commonCoordinateEmbedding T) = _
  rw [recoverNuclear_commonCoordinateEmbedding, sourceInstrument_operation]

theorem outputProjection_common_eq_id {J : Type} [Fintype J] [DecidableEq J]
    (h : H) (ω : Ω) :
    outputProjection (I := J) (commonFundamentalFamily (H := H × Ω)) h ω =
      ContinuousLinearMap.id ℂ (RecordedSpace J) := by
  change blockLift (R := J) ((commonFundamentalFamily (H := H × Ω)).rangeProjection (h, ω)) = _
  rw [commonFundamentalFamily_rangeProjection_eq_id]
  ext x i
  rfl

theorem controlledObservable_common_eq_self {J : Type} [Fintype J] [DecidableEq J]
    (h : H) (W : Ω → RecordedSpace J →L[ℂ] RecordedSpace J) :
    controlledObservable (commonFundamentalFamily (H := H × Ω)) h W = W := by
  funext ω
  simp only [controlledObservable, outputProjection_common_eq_id,
    ContinuousLinearMap.id_comp, ContinuousLinearMap.comp_id]

def recordedSourceInstrument (P : Instrument CommonHilbert CommonHilbert H Ω) :
    RecordedSourceInstrument (commonFundamentalFamily (H := H))
      (commonFundamentalFamily (H := H × Ω)) where
  represented_physical := sourceInstrument P
  controlled_output J _ _ _ h U hU W hW := by
    rw [controlledObservable_common_eq_self]

@[simp] theorem recordedSourceInstrument_physical
    (P : Instrument CommonHilbert CommonHilbert H Ω) :
    (recordedSourceInstrument P).represented_physical = sourceInstrument P := rfl

end QuantumProver.MatrixCommonPhysicalInstrument

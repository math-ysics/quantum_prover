import QuantumProver.QuantumChannels.PhysicalUniverseHilbert
import QuantumProver.InformationTheory.ElegantJointMeasurement.NormalPhysicalTerminalAdmission

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory Set Function InnerProductSpace
open scoped BigOperators Topology Classical

namespace QuantumProver.MatrixPhysicalUniverseInstruments

open QuantumProver.MatrixPhysicalUniverseHilbert
open QuantumProver.ElegantJointMeasurement.MeasurableHilbertField QuantumProver.ElegantJointMeasurement.SeparableHilbertEmbedding
open QuantumProver.ElegantJointMeasurement.MeasurableNormalInstrument QuantumProver.ElegantJointMeasurement.NormalInstrumentAbsorption
open QuantumProver.ElegantJointMeasurement.NormalPhysicalAdmission QuantumProver.ElegantJointMeasurement.NormalPhysicalTerminalAdmission
open QuantumProver.ElegantJointMeasurement.NormalInstrumentCompletion QuantumProver.ElegantJointMeasurement.NormalSandwich
open QuantumProver.ElegantJointMeasurement.NormalRecordedAbsorption QuantumProver.ElegantJointMeasurement.HilbertRecordedHilbertInstrument
open QuantumProver.ElegantJointMeasurement.HilbertChoi
open QuantumProver.MatrixNormalSourceCompletion
open QuantumProver.NuclearOperator (toOperator toOperator_injective)
open QuantumProver.HilbertNuclearCompression (compose toOperator_compose)

universe u v w x y z

section NuclearUnitary

variable {X : Type v} {Y : Type w} {Z : Type x}
  [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]
  [NormedAddCommGroup Z] [InnerProductSpace ℂ Z] [CompleteSpace Z]

theorem recoverNuclear_unitary (J : X ≃ₗᵢ[ℂ] Y) :
    recoverNuclear J.toLinearIsometry = padNuclear J.symm.toLinearIsometry := by
  have hJ : J.toLinearIsometry.toContinuousLinearMap.adjoint =
      J.symm.toLinearIsometry.toContinuousLinearMap := J.adjoint_eq_symm
  have hJs : J.symm.toLinearIsometry.toContinuousLinearMap.adjoint =
      J.toLinearIsometry.toContinuousLinearMap := J.symm.adjoint_eq_symm
  simp only [recoverNuclear, padNuclear, hJ, hJs]

theorem pad_recoverNuclear_unitary (J : X ≃ₗᵢ[ℂ] Y) (T : Nuc Y) :
    padNuclear J.toLinearIsometry (recoverNuclear J.toLinearIsometry T) = T := by
  rw [recoverNuclear_unitary]
  have h := recover_padNuclear J.symm.toLinearIsometry T
  rw [recoverNuclear_unitary J.symm] at h
  exact h

theorem trace_recoverNuclear_unitary (J : X ≃ₗᵢ[ℂ] Y) (T : Nuc Y) :
    QuantumProver.HilbertNuclearTrace.trace (recoverNuclear J.toLinearIsometry T) =
      QuantumProver.HilbertNuclearTrace.trace T := by
  rw [recoverNuclear_unitary]
  exact trace_padNuclear J.symm.toLinearIsometry T

theorem normalCompletelyPositive_recoverNuclear (J : X →ₗᵢ[ℂ] Y) :
    NormalCompletelyPositive (recoverNuclear J) := by
  simpa only [sandwich, recoverNuclear, ContinuousLinearMap.adjoint_adjoint] using
    normalCompletelyPositive_sandwich J.toContinuousLinearMap.adjoint

theorem recoverNuclear_comp (I : X →ₗᵢ[ℂ] Y) (J : Y →ₗᵢ[ℂ] Z)
    (T : Nuc Z) :
    recoverNuclear (J.comp I) T = recoverNuclear I (recoverNuclear J T) := by
  apply toOperator_injective
  have hc : (J.comp I).toContinuousLinearMap =
      J.toContinuousLinearMap.comp I.toContinuousLinearMap := rfl
  simp only [recoverNuclear, toOperator_compose, hc, ContinuousLinearMap.adjoint_comp]
  ext z
  rfl

theorem recoverNuclear_rankOne_unitary (J : X ≃ₗᵢ[ℂ] Y) (a b : X) :
    recoverNuclear J.toLinearIsometry
      (QuantumProver.NuclearOperator.rankOne (innerSL ℂ (J a)) (J b)) =
        QuantumProver.NuclearOperator.rankOne (innerSL ℂ a) b := by
  have ha : J.toLinearIsometry.toContinuousLinearMap.adjoint (J a) = a :=
    adjoint_embedding_apply J.toLinearIsometry a
  have hb : J.toLinearIsometry.toContinuousLinearMap.adjoint (J b) = b :=
    adjoint_embedding_apply J.toLinearIsometry b
  rw [recoverNuclear_rankOne, ha, hb]

theorem padNuclear_matrixElement (J : X →ₗᵢ[ℂ] Y) (T : Nuc X) (a b : X) :
    inner ℂ (J a) (toOperator (padNuclear J T) (J b)) =
      inner ℂ a (toOperator T b) := by
  rw [toOperator_padNuclear]
  simp only [ContinuousLinearMap.comp_apply, adjoint_embedding_apply,
    LinearIsometry.coe_toContinuousLinearMap, LinearIsometry.inner_map_map]

end NuclearUnitary

section FundamentalCodes

variable {H : Type u} [MeasurableSpace H]
  {E : H → Type v} {E' : H → Type w}
  [∀ h, NormedAddCommGroup (E h)] [∀ h, InnerProductSpace ℂ (E h)]
  [∀ h, CompleteSpace (E h)]
  [∀ h, NormedAddCommGroup (E' h)] [∀ h, InnerProductSpace ℂ (E' h)]
  [∀ h, CompleteSpace (E' h)]

theorem fundamentalFamily_ext (F Q : FundamentalFamily E)
    (hvector : F.vector = Q.vector) : F = Q := by
  cases F
  cases Q
  cases hvector
  rfl

theorem family_embedding_comp (F : FundamentalFamily E) (F' : FundamentalFamily E')
    (J : (h : H) → E h ≃ₗᵢ[ℂ] E' h)
    (hvector : ∀ h i, F'.vector h i = J h (F.vector h i)) (h : H) :
    (F'.embedding h).comp (J h).toLinearIsometry = F.embedding h := by
  apply DFunLike.ext
  intro a
  exact family_embedding_naturality F F' J hvector h a

theorem family_rangeProjection_transport (F : FundamentalFamily E)
    (F' : FundamentalFamily E') (J : (h : H) → E h ≃ₗᵢ[ℂ] E' h)
    (hvector : ∀ h i, F'.vector h i = J h (F.vector h i)) (h : H) :
    F'.rangeProjection h = F.rangeProjection h := by
  have hF : F' = transportFamily F J :=
    fundamentalFamily_ext _ _ (funext fun h => funext fun i => hvector h i)
  rw [hF]
  exact transportFamily_rangeProjection F J h

theorem recoverNuclear_family_transport (F : FundamentalFamily E)
    (F' : FundamentalFamily E') (J : (h : H) → E h ≃ₗᵢ[ℂ] E' h)
    (hvector : ∀ h i, F'.vector h i = J h (F.vector h i))
    (h : H) (T : Nuc CommonHilbert) :
    recoverNuclear (F'.embedding h) T =
      padNuclear (J h).toLinearIsometry (recoverNuclear (F.embedding h) T) := by
  calc
    _ = padNuclear (J h).toLinearIsometry
        (recoverNuclear (J h).toLinearIsometry (recoverNuclear (F'.embedding h) T)) :=
      (pad_recoverNuclear_unitary (J h) _).symm
    _ = _ := by
      rw [← recoverNuclear_comp, family_embedding_comp F F' J hvector h]

theorem padNuclear_family_transport (F : FundamentalFamily E)
    (F' : FundamentalFamily E') (J : (h : H) → E h ≃ₗᵢ[ℂ] E' h)
    (hvector : ∀ h i, F'.vector h i = J h (F.vector h i))
    (h : H) (T : Nuc (E h)) :
    padNuclear (F'.embedding h) (padNuclear (J h).toLinearIsometry T) =
      padNuclear (F.embedding h) T := by
  rw [← padNuclear_comp, family_embedding_comp F F' J hvector h]

end FundamentalCodes

section MatrixTransport

variable {H : Type u} [MeasurableSpace H] {Ω : Type y} [MeasurableSpace Ω]
  {E : H → Type v} {E' : H → Type w}
  {G : H → Type x} {G' : H → Type z}
  [∀ h, NormedAddCommGroup (E h)] [∀ h, InnerProductSpace ℂ (E h)]
  [∀ h, CompleteSpace (E h)]
  [∀ h, NormedAddCommGroup (E' h)] [∀ h, InnerProductSpace ℂ (E' h)]
  [∀ h, CompleteSpace (E' h)]
  [∀ h, NormedAddCommGroup (G h)] [∀ h, InnerProductSpace ℂ (G h)]
  [∀ h, CompleteSpace (G h)]
  [∀ h, NormedAddCommGroup (G' h)] [∀ h, InnerProductSpace ℂ (G' h)]
  [∀ h, CompleteSpace (G' h)]

def transportInputMatrixInstrument (F : FundamentalFamily E)
    (F' : FundamentalFamily E') (Q : FundamentalFamily G)
    (J : (h : H) → E h ≃ₗᵢ[ℂ] E' h)
    (hvector : ∀ h i, F'.vector h i = J h (F.vector h i))
    (P : MatrixInstrument F Q Ω) : MatrixInstrument F' Q Ω where
  operation h s := (P.operation h s).comp (recoverNuclear (J h).toLinearIsometry)
  empty h := by
    ext T
    simp only [ContinuousLinearMap.comp_apply, P.empty, ContinuousLinearMap.zero_apply]
  countable_additivity h s hs hd T :=
    P.countable_additivity h s hs hd (recoverNuclear (J h).toLinearIsometry T)
  completelyPositive h s hs := normalCompletelyPositive_comp _ _
    (P.completelyPositive h s hs) (normalCompletelyPositive_recoverNuclear _)
  fundamental_measurable s hs i j k l := by
    have he : (fun h => inner ℂ (Q.vector h k)
        (toOperator (((P.operation h s).comp (recoverNuclear (J h).toLinearIsometry))
          (QuantumProver.NuclearOperator.rankOne (innerSL ℂ (F'.vector h i))
            (F'.vector h j))) (Q.vector h l))) =
        fun h => inner ℂ (Q.vector h k)
          (toOperator (P.operation h s
            (QuantumProver.NuclearOperator.rankOne (innerSL ℂ (F.vector h i))
              (F.vector h j))) (Q.vector h l)) := by
      funext h
      rw [ContinuousLinearMap.comp_apply, hvector h i, hvector h j,
        recoverNuclear_rankOne_unitary]
    rw [he]
    exact P.fundamental_measurable s hs i j k l
  trace_preserving h T := by
    rw [ContinuousLinearMap.comp_apply, P.trace_preserving,
      trace_recoverNuclear_unitary]

@[simp] theorem transportInputMatrixInstrument_operation (F : FundamentalFamily E)
    (F' : FundamentalFamily E') (Q : FundamentalFamily G)
    (J : (h : H) → E h ≃ₗᵢ[ℂ] E' h)
    (hvector : ∀ h i, F'.vector h i = J h (F.vector h i))
    (P : MatrixInstrument F Q Ω) (h : H) (s : Set Ω) :
    (transportInputMatrixInstrument F F' Q J hvector P).operation h s =
      (P.operation h s).comp (recoverNuclear (J h).toLinearIsometry) := rfl

theorem transportInputMatrixInstrument_on_physical (F : FundamentalFamily E)
    (F' : FundamentalFamily E') (Q : FundamentalFamily G)
    (J : (h : H) → E h ≃ₗᵢ[ℂ] E' h)
    (hvector : ∀ h i, F'.vector h i = J h (F.vector h i))
    (P : MatrixInstrument F Q Ω) (h : H) (s : Set Ω) (T : Nuc (E h)) :
    (transportInputMatrixInstrument F F' Q J hvector P).operation h s
      (padNuclear (J h).toLinearIsometry T) = P.operation h s T := by
  simp only [transportInputMatrixInstrument_operation,
    ContinuousLinearMap.comp_apply, recover_padNuclear]

def transportMatrixInstrument (F : FundamentalFamily E)
    (F' : FundamentalFamily E') (Q : FundamentalFamily G)
    (Q' : FundamentalFamily G')
    (J : (h : H) → E h ≃ₗᵢ[ℂ] E' h)
    (K : (h : H) → G h ≃ₗᵢ[ℂ] G' h)
    (hF : ∀ h i, F'.vector h i = J h (F.vector h i))
    (hQ : ∀ h i, Q'.vector h i = K h (Q.vector h i))
    (P : MatrixInstrument F Q Ω) : MatrixInstrument F' Q' Ω where
  operation h s := (padNuclear (K h).toLinearIsometry).comp
    ((P.operation h s).comp (recoverNuclear (J h).toLinearIsometry))
  empty h := by
    ext T
    simp only [ContinuousLinearMap.comp_apply, P.empty,
      ContinuousLinearMap.zero_apply, map_zero]
  countable_additivity h s hs hd T :=
    (padNuclear (K h).toLinearIsometry).hasSum
      (P.countable_additivity h s hs hd (recoverNuclear (J h).toLinearIsometry T))
  completelyPositive h s hs := normalCompletelyPositive_comp _ _
    (normalCompletelyPositive_sandwich (K h).toLinearIsometry.toContinuousLinearMap)
    (normalCompletelyPositive_comp _ _ (P.completelyPositive h s hs)
      (normalCompletelyPositive_recoverNuclear _))
  fundamental_measurable s hs i j k l := by
    have he : (fun h => inner ℂ (Q'.vector h k)
        (toOperator (((padNuclear (K h).toLinearIsometry).comp
          ((P.operation h s).comp (recoverNuclear (J h).toLinearIsometry)))
            (QuantumProver.NuclearOperator.rankOne (innerSL ℂ (F'.vector h i))
              (F'.vector h j))) (Q'.vector h l))) =
        fun h => inner ℂ (Q.vector h k)
          (toOperator (P.operation h s
            (QuantumProver.NuclearOperator.rankOne (innerSL ℂ (F.vector h i))
              (F.vector h j))) (Q.vector h l)) := by
      funext h
      rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
        hF h i, hF h j, recoverNuclear_rankOne_unitary, hQ h k, hQ h l]
      exact padNuclear_matrixElement (K h).toLinearIsometry _ _ _
    rw [he]
    exact P.fundamental_measurable s hs i j k l
  trace_preserving h T := by
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
      trace_padNuclear, P.trace_preserving, trace_recoverNuclear_unitary]

@[simp] theorem transportMatrixInstrument_operation (F : FundamentalFamily E)
    (F' : FundamentalFamily E') (Q : FundamentalFamily G)
    (Q' : FundamentalFamily G')
    (J : (h : H) → E h ≃ₗᵢ[ℂ] E' h)
    (K : (h : H) → G h ≃ₗᵢ[ℂ] G' h)
    (hF : ∀ h i, F'.vector h i = J h (F.vector h i))
    (hQ : ∀ h i, Q'.vector h i = K h (Q.vector h i))
    (P : MatrixInstrument F Q Ω) (h : H) (s : Set Ω) (T : Nuc (E' h)) :
    (transportMatrixInstrument F F' Q Q' J K hF hQ P).operation h s T =
      padNuclear (K h).toLinearIsometry
        (P.operation h s (recoverNuclear (J h).toLinearIsometry T)) := rfl

theorem transportMatrixInstrument_on_physical (F : FundamentalFamily E)
    (F' : FundamentalFamily E') (Q : FundamentalFamily G)
    (Q' : FundamentalFamily G')
    (J : (h : H) → E h ≃ₗᵢ[ℂ] E' h)
    (K : (h : H) → G h ≃ₗᵢ[ℂ] G' h)
    (hF : ∀ h i, F'.vector h i = J h (F.vector h i))
    (hQ : ∀ h i, Q'.vector h i = K h (Q.vector h i))
    (P : MatrixInstrument F Q Ω) (h : H) (s : Set Ω) (T : Nuc (E h)) :
    (transportMatrixInstrument F F' Q Q' J K hF hQ P).operation h s
      (padNuclear (J h).toLinearIsometry T) =
        padNuclear (K h).toLinearIsometry (P.operation h s T) := by
  rw [transportMatrixInstrument_operation, recover_padNuclear]

theorem codedOperation_transportMatrixInstrument (F : FundamentalFamily E)
    (F' : FundamentalFamily E') (Q : FundamentalFamily G)
    (Q' : FundamentalFamily G')
    (J : (h : H) → E h ≃ₗᵢ[ℂ] E' h)
    (K : (h : H) → G h ≃ₗᵢ[ℂ] G' h)
    (hF : ∀ h i, F'.vector h i = J h (F.vector h i))
    (hQ : ∀ h i, Q'.vector h i = K h (Q.vector h i))
    (P : MatrixInstrument F Q Ω) (h : H) (s : Set Ω) :
    (transportMatrixInstrument F F' Q Q' J K hF hQ P).codedOperation h s =
      P.codedOperation h s := by
  ext T
  simp only [MatrixInstrument.codedOperation, encodedOperation,
    ContinuousLinearMap.comp_apply, transportMatrixInstrument_operation]
  rw [recoverNuclear_family_transport F F' J hF, recover_padNuclear,
    padNuclear_family_transport Q Q' K hQ]

end MatrixTransport

section SourceCodes

variable {H : Type u} [MeasurableSpace H] {Ω : Type y} [MeasurableSpace Ω]
  {E : H → Type v} {E' : H → Type w}
  [∀ h, NormedAddCommGroup (E h)] [∀ h, InnerProductSpace ℂ (E h)]
  [∀ h, CompleteSpace (E h)]
  [∀ h, NormedAddCommGroup (E' h)] [∀ h, InnerProductSpace ℂ (E' h)]
  [∀ h, CompleteSpace (E' h)]

theorem sourceCodedOperation_transportInput (F : FundamentalFamily E)
    (F' : FundamentalFamily E') (J : (h : H) → E h ≃ₗᵢ[ℂ] E' h)
    (hvector : ∀ h i, F'.vector h i = J h (F.vector h i))
    (P : SourceInstrument F Ω) (h : H) (s : Set Ω) :
    sourceCodedOperation
      (transportInputMatrixInstrument F F' (commonFundamentalFamily (H := H)) J hvector P)
        h s = sourceCodedOperation P h s := by
  ext T
  simp only [sourceCodedOperation, transportInputMatrixInstrument_operation,
    ContinuousLinearMap.comp_apply]
  rw [recoverNuclear_family_transport F F' J hvector, recover_padNuclear]

theorem normalInstrument_ext {X : Type v} {Y : Type w}
    [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]
    (P Q : Instrument X Y H Ω) (hoperation : P.operation = Q.operation) : P = Q := by
  cases P
  cases Q
  cases hoperation
  rfl

theorem completeSourceInstrument_transportInput (F : FundamentalFamily E)
    (F' : FundamentalFamily E') (J : (h : H) → E h ≃ₗᵢ[ℂ] E' h)
    (hvector : ∀ h i, F'.vector h i = J h (F.vector h i))
    (P : SourceInstrument F Ω) :
    completeSourceInstrument
      (transportInputMatrixInstrument F F' (commonFundamentalFamily (H := H)) J hvector P) =
        completeSourceInstrument P := by
  apply normalInstrument_ext
  funext h s
  change sourceCodedOperation
    (transportInputMatrixInstrument F F' (commonFundamentalFamily (H := H)) J hvector P)
      h (Sum.inl ⁻¹' s) +
        (if Sum.inr () ∈ s then complementReset commonResetVector (F'.rangeProjection h)
          else 0) =
    sourceCodedOperation P h (Sum.inl ⁻¹' s) +
      (if Sum.inr () ∈ s then complementReset commonResetVector (F.rangeProjection h)
        else 0)
  rw [sourceCodedOperation_transportInput, family_rangeProjection_transport F F' J hvector]

end SourceCodes

section RecordedSources

variable {H : Type u} [MeasurableSpace H] {Ω : Type y} [MeasurableSpace Ω]
  {E : H → Type v} {E' : H → Type w}
  [∀ h, NormedAddCommGroup (E h)] [∀ h, InnerProductSpace ℂ (E h)]
  [∀ h, CompleteSpace (E h)]
  [∀ h, NormedAddCommGroup (E' h)] [∀ h, InnerProductSpace ℂ (E' h)]
  [∀ h, CompleteSpace (E' h)]
  {G : H × Ω → Type x} {G' : H × Ω → Type z}
  [∀ z, NormedAddCommGroup (G z)] [∀ z, InnerProductSpace ℂ (G z)]
  [∀ z, CompleteSpace (G z)]
  [∀ z, NormedAddCommGroup (G' z)] [∀ z, InnerProductSpace ℂ (G' z)]
  [∀ z, CompleteSpace (G' z)]

variable {R : Type} [Fintype R] [DecidableEq R] [Nonempty R]

theorem normalResponse_transportInput (F : FundamentalFamily E)
    (F' : FundamentalFamily E') (J : (h : H) → E h ≃ₗᵢ[ℂ] E' h)
    (hvector : ∀ h i, F'.vector h i = J h (F.vector h i))
    (P : SourceInstrument F Ω) (h : H) (s : Set Ω) (U : Nuc (BlockSpace R (E' h))) :
    normalResponse
      (physicalInstrument (transportInputMatrixInstrument F F'
        (commonFundamentalFamily (H := H)) J hvector P) h) () U s =
      normalResponse (physicalInstrument P h) ()
        (normalAmplification (recoverNuclear (J h).toLinearIsometry) U) s := by
  change normalAmplification ((P.operation h s).comp
    (recoverNuclear (J h).toLinearIsometry)) U = _
  exact normalAmplification_comp _ _ U

theorem normalProbe_transportInput (F : FundamentalFamily E)
    (F' : FundamentalFamily E') (J : (h : H) → E h ≃ₗᵢ[ℂ] E' h)
    (hvector : ∀ h i, F'.vector h i = J h (F.vector h i))
    (P : SourceInstrument F Ω) (h : H)
    (U : Nuc (BlockSpace R (E' h))) (hU : (toOperator U).IsPositive)
    (a : RecordedSpace R) :
    normalProbe
      (physicalInstrument (transportInputMatrixInstrument F F'
        (commonFundamentalFamily (H := H)) J hvector P) h) () U hU a =
      normalProbe (physicalInstrument P h) ()
        (normalAmplification (recoverNuclear (J h).toLinearIsometry) U)
        (normalCompletelyPositive_recoverNuclear (J h).toLinearIsometry R U hU) a := by
  apply Measure.ext
  intro s hs
  rw [normalProbe_apply _ _ _ _ _ _ hs, normalProbe_apply _ _ _ _ _ _ hs,
    normalResponse_transportInput]

theorem normalRecordedExpectation_transportInput (F : FundamentalFamily E)
    (F' : FundamentalFamily E') (J : (h : H) → E h ≃ₗᵢ[ℂ] E' h)
    (hvector : ∀ h i, F'.vector h i = J h (F.vector h i))
    (P : SourceInstrument F Ω) (h : H)
    (U : Nuc (BlockSpace R (E' h))) (hU : (toOperator U).IsPositive)
    (W : Ω → RecordedSpace R →L[ℂ] RecordedSpace R) :
    normalRecordedExpectation
      (physicalInstrument (transportInputMatrixInstrument F F'
        (commonFundamentalFamily (H := H)) J hvector P) h) () U hU W =
      normalRecordedExpectation (physicalInstrument P h) ()
        (normalAmplification (recoverNuclear (J h).toLinearIsometry) U)
        (normalCompletelyPositive_recoverNuclear (J h).toLinearIsometry R U hU) W := by
  unfold normalRecordedExpectation
  have hp : (fun a => normalProbe
      (physicalInstrument (transportInputMatrixInstrument F F'
        (commonFundamentalFamily (H := H)) J hvector P) h) () U hU a) =
      fun a => normalProbe (physicalInstrument P h) ()
        (normalAmplification (recoverNuclear (J h).toLinearIsometry) U)
        (normalCompletelyPositive_recoverNuclear (J h).toLinearIsometry R U hU) a :=
    funext fun a => normalProbe_transportInput F F' J hvector P h U hU a
  rw [hp]

theorem controlledObservable_transport (Q : FundamentalFamily G)
    (Q' : FundamentalFamily G') (K : (z : H × Ω) → G z ≃ₗᵢ[ℂ] G' z)
    (hvector : ∀ z i, Q'.vector z i = K z (Q.vector z i))
    (h : H) (W : Ω → RecordedSpace R →L[ℂ] RecordedSpace R) :
    controlledObservable Q' h W = controlledObservable Q h W := by
  funext ω
  simp only [controlledObservable, outputProjection,
    family_rangeProjection_transport Q Q' K hvector]

def transportRecordedSourceInstrument (F : FundamentalFamily E)
    (F' : FundamentalFamily E') (Q : FundamentalFamily G) (Q' : FundamentalFamily G')
    (J : (h : H) → E h ≃ₗᵢ[ℂ] E' h)
    (K : (z : H × Ω) → G z ≃ₗᵢ[ℂ] G' z)
    (hF : ∀ h i, F'.vector h i = J h (F.vector h i))
    (hQ : ∀ z i, Q'.vector z i = K z (Q.vector z i))
    (P : RecordedSourceInstrument F Q) : RecordedSourceInstrument F' Q' where
  represented_physical := transportInputMatrixInstrument F F'
    (commonFundamentalFamily (H := H)) J hF P.represented_physical
  controlled_output R _ _ _ h U hU W hW := by
    rw [normalRecordedExpectation_transportInput,
      normalRecordedExpectation_transportInput,
      controlledObservable_transport Q Q' K hQ]
    exact P.controlled_output R h _
      (normalCompletelyPositive_recoverNuclear (J h).toLinearIsometry R U hU) W hW

end RecordedSources

section PhysicalTerminals

variable {H : Type u} [MeasurableSpace H] {E : H → Type v} {E' : H → Type w}
  [∀ h, NormedAddCommGroup (E h)] [∀ h, InnerProductSpace ℂ (E h)]
  [∀ h, CompleteSpace (E h)]
  [∀ h, NormedAddCommGroup (E' h)] [∀ h, InnerProductSpace ℂ (E' h)]
  [∀ h, CompleteSpace (E' h)]

theorem terminalSourceOperation_transportInput (F : FundamentalFamily E)
    (F' : FundamentalFamily E') (J : (h : H) → E h ≃ₗᵢ[ℂ] E' h)
    (hvector : ∀ h i, F'.vector h i = J h (F.vector h i)) (c : ℕ)
    (P : MatrixInstrument F (finiteOutputFamily (H := H) c) PUnit.{u+1})
    (h : H) (s : Set PUnit.{u+1}) :
    terminalSourceOperation
      (transportInputMatrixInstrument F F' (finiteOutputFamily (H := H) c) J hvector P) h s =
        terminalSourceOperation P h s := by
  ext T
  simp only [terminalSourceOperation, transportInputMatrixInstrument_operation,
    ContinuousLinearMap.comp_apply]
  rw [recoverNuclear_family_transport F F' J hvector, recover_padNuclear]

theorem completePhysicalTerminalLocal_transportInput (F : FundamentalFamily E)
    (F' : FundamentalFamily E') (J : (h : H) → E h ≃ₗᵢ[ℂ] E' h)
    (hvector : ∀ h i, F'.vector h i = J h (F.vector h i)) (c : ℕ)
    (P : MatrixInstrument F (finiteOutputFamily (H := H) c) PUnit.{u+1}) (hc : 0 < c) :
    completePhysicalTerminalLocal
      (transportInputMatrixInstrument F F' (finiteOutputFamily (H := H) c) J hvector P) hc =
        completePhysicalTerminalLocal P hc := by
  apply normalInstrument_ext
  funext h s
  change terminalSourceOperation
    (transportInputMatrixInstrument F F' (finiteOutputFamily (H := H) c) J hvector P)
      h (Sum.inl ⁻¹' (terminalCollapse ⁻¹' s)) +
        (if Sum.inr () ∈ terminalCollapse ⁻¹' s then
          complementReset (finiteResetVector hc) (F'.rangeProjection h) else 0) =
    terminalSourceOperation P h (Sum.inl ⁻¹' (terminalCollapse ⁻¹' s)) +
      (if Sum.inr () ∈ terminalCollapse ⁻¹' s then
        complementReset (finiteResetVector hc) (F.rangeProjection h) else 0)
  rw [terminalSourceOperation_transportInput, family_rangeProjection_transport F F' J hvector]

end PhysicalTerminals
end QuantumProver.MatrixPhysicalUniverseInstruments

namespace QuantumProver.MatrixPhysicalUniverseInstruments

open QuantumProver.MatrixPhysicalUniverseHilbert
open QuantumProver.ElegantJointMeasurement.MeasurableHilbertField QuantumProver.ElegantJointMeasurement.SeparableHilbertEmbedding
open QuantumProver.ElegantJointMeasurement.MeasurableNormalInstrument QuantumProver.ElegantJointMeasurement.NormalInstrumentAbsorption
open QuantumProver.ElegantJointMeasurement.NormalPhysicalAdmission QuantumProver.ElegantJointMeasurement.NormalPhysicalTerminalAdmission
open QuantumProver.ElegantJointMeasurement.NormalInstrumentCompletion QuantumProver.ElegantJointMeasurement.NormalSandwich
open QuantumProver.ElegantJointMeasurement.NormalRecordedAbsorption QuantumProver.ElegantJointMeasurement.HilbertRecordedHilbertInstrument
open QuantumProver.ElegantJointMeasurement.HilbertChoi
open QuantumProver.MatrixNormalSourceCompletion
open QuantumProver.NuclearOperator (toOperator toOperator_injective)

theorem recoverNuclear_ulift_embedding.{r,u,v}
    {H : Type u} [MeasurableSpace H] {E : H → Type v}
    [∀ h, NormedAddCommGroup (E h)] [∀ h, InnerProductSpace ℂ (E h)]
    [∀ h, CompleteSpace (E h)] (F : FundamentalFamily E)
    (h : H) (T : Nuc CommonHilbert) :
    recoverNuclear ((uliftFamily.{r} F).embedding h) T =
      padNuclear (uliftUnitary.{r} (E h)).toLinearIsometry
        (recoverNuclear (F.embedding h) T) :=
  recoverNuclear_family_transport F (uliftFamily.{r} F)
    (fun h => uliftUnitary.{r} (E h)) (fun _ _ => rfl) h T

theorem padNuclear_ulift_embedding.{r,u,v}
    {H : Type u} [MeasurableSpace H] {E : H → Type v}
    [∀ h, NormedAddCommGroup (E h)] [∀ h, InnerProductSpace ℂ (E h)]
    [∀ h, CompleteSpace (E h)] (F : FundamentalFamily E)
    (h : H) (T : Nuc (E h)) :
    padNuclear ((uliftFamily.{r} F).embedding h)
      (padNuclear (uliftUnitary.{r} (E h)).toLinearIsometry T) =
        padNuclear (F.embedding h) T :=
  padNuclear_family_transport F (uliftFamily.{r} F)
    (fun h => uliftUnitary.{r} (E h)) (fun _ _ => rfl) h T

def uliftInputMatrixInstrument.{r,u,v,w,x}
    {H : Type u} [MeasurableSpace H] {Ω : Type x} [MeasurableSpace Ω]
    {E : H → Type v} {G : H → Type w}
    [∀ h, NormedAddCommGroup (E h)] [∀ h, InnerProductSpace ℂ (E h)]
    [∀ h, CompleteSpace (E h)]
    [∀ h, NormedAddCommGroup (G h)] [∀ h, InnerProductSpace ℂ (G h)]
    [∀ h, CompleteSpace (G h)]
    (F : FundamentalFamily E) (Q : FundamentalFamily G) (P : MatrixInstrument F Q Ω) :
    MatrixInstrument (uliftFamily.{r} F) Q Ω :=
  transportInputMatrixInstrument F (uliftFamily.{r} F) Q
    (fun h => uliftUnitary.{r} (E h)) (fun _ _ => rfl) P

@[simp] theorem uliftInputMatrixInstrument_operation.{r,u,v,w,x}
    {H : Type u} [MeasurableSpace H] {Ω : Type x} [MeasurableSpace Ω]
    {E : H → Type v} {G : H → Type w}
    [∀ h, NormedAddCommGroup (E h)] [∀ h, InnerProductSpace ℂ (E h)]
    [∀ h, CompleteSpace (E h)]
    [∀ h, NormedAddCommGroup (G h)] [∀ h, InnerProductSpace ℂ (G h)]
    [∀ h, CompleteSpace (G h)]
    (F : FundamentalFamily E) (Q : FundamentalFamily G) (P : MatrixInstrument F Q Ω)
    (h : H) (s : Set Ω) (T : Nuc (ULift.{r} (E h))) :
    (uliftInputMatrixInstrument.{r} F Q P).operation h s T =
      P.operation h s (recoverNuclear (uliftUnitary.{r} (E h)).toLinearIsometry T) := rfl

def uliftMatrixInstrument.{r,s,u,v,w,x}
    {H : Type u} [MeasurableSpace H] {Ω : Type x} [MeasurableSpace Ω]
    {E : H → Type v} {G : H → Type w}
    [∀ h, NormedAddCommGroup (E h)] [∀ h, InnerProductSpace ℂ (E h)]
    [∀ h, CompleteSpace (E h)]
    [∀ h, NormedAddCommGroup (G h)] [∀ h, InnerProductSpace ℂ (G h)]
    [∀ h, CompleteSpace (G h)]
    (F : FundamentalFamily E) (Q : FundamentalFamily G) (P : MatrixInstrument F Q Ω) :
    MatrixInstrument (uliftFamily.{r} F) (uliftFamily.{s} Q) Ω :=
  transportMatrixInstrument F (uliftFamily.{r} F) Q (uliftFamily.{s} Q)
    (fun h => uliftUnitary.{r} (E h)) (fun h => uliftUnitary.{s} (G h))
    (fun _ _ => rfl) (fun _ _ => rfl) P

@[simp] theorem uliftMatrixInstrument_operation.{r,s,u,v,w,x}
    {H : Type u} [MeasurableSpace H] {Ω : Type x} [MeasurableSpace Ω]
    {E : H → Type v} {G : H → Type w}
    [∀ h, NormedAddCommGroup (E h)] [∀ h, InnerProductSpace ℂ (E h)]
    [∀ h, CompleteSpace (E h)]
    [∀ h, NormedAddCommGroup (G h)] [∀ h, InnerProductSpace ℂ (G h)]
    [∀ h, CompleteSpace (G h)]
    (F : FundamentalFamily E) (Q : FundamentalFamily G) (P : MatrixInstrument F Q Ω)
    (h : H) (s : Set Ω) (T : Nuc (ULift.{r} (E h))) :
    (uliftMatrixInstrument.{r,s} F Q P).operation h s T =
      padNuclear (uliftUnitary.{s} (G h)).toLinearIsometry
        (P.operation h s (recoverNuclear (uliftUnitary.{r} (E h)).toLinearIsometry T)) := rfl

theorem codedOperation_uliftMatrixInstrument.{r,s,u,v,w,x}
    {H : Type u} [MeasurableSpace H] {Ω : Type x} [MeasurableSpace Ω]
    {E : H → Type v} {G : H → Type w}
    [∀ h, NormedAddCommGroup (E h)] [∀ h, InnerProductSpace ℂ (E h)]
    [∀ h, CompleteSpace (E h)]
    [∀ h, NormedAddCommGroup (G h)] [∀ h, InnerProductSpace ℂ (G h)]
    [∀ h, CompleteSpace (G h)]
    (F : FundamentalFamily E) (Q : FundamentalFamily G) (P : MatrixInstrument F Q Ω)
    (h : H) (s : Set Ω) :
    (uliftMatrixInstrument.{r,s} F Q P).codedOperation h s = P.codedOperation h s :=
  codedOperation_transportMatrixInstrument F (uliftFamily.{r} F) Q (uliftFamily.{s} Q)
    (fun h => uliftUnitary.{r} (E h)) (fun h => uliftUnitary.{s} (G h))
    (fun _ _ => rfl) (fun _ _ => rfl) P h s

theorem sourceCodedOperation_uliftInput.{r,u,v,x}
    {H : Type u} [MeasurableSpace H] {Ω : Type x} [MeasurableSpace Ω]
    {E : H → Type v}
    [∀ h, NormedAddCommGroup (E h)] [∀ h, InnerProductSpace ℂ (E h)]
    [∀ h, CompleteSpace (E h)]
    (F : FundamentalFamily E) (P : SourceInstrument F Ω) (h : H) (s : Set Ω) :
    sourceCodedOperation (uliftInputMatrixInstrument.{r} F
      (commonFundamentalFamily (H := H)) P) h s = sourceCodedOperation P h s :=
  sourceCodedOperation_transportInput F (uliftFamily.{r} F)
    (fun h => uliftUnitary.{r} (E h)) (fun _ _ => rfl) P h s

theorem completeSourceInstrument_uliftInput.{r,u,v,x}
    {H : Type u} [MeasurableSpace H] {Ω : Type x} [MeasurableSpace Ω]
    {E : H → Type v}
    [∀ h, NormedAddCommGroup (E h)] [∀ h, InnerProductSpace ℂ (E h)]
    [∀ h, CompleteSpace (E h)]
    (F : FundamentalFamily E) (P : SourceInstrument F Ω) :
    completeSourceInstrument (uliftInputMatrixInstrument.{r} F
      (commonFundamentalFamily (H := H)) P) = completeSourceInstrument P :=
  completeSourceInstrument_transportInput F (uliftFamily.{r} F)
    (fun h => uliftUnitary.{r} (E h)) (fun _ _ => rfl) P

def uliftRecordedSourceInstrument.{r,s,u,v,w,x}
    {H : Type u} [MeasurableSpace H] {Ω : Type x} [MeasurableSpace Ω]
    {E : H → Type v} {G : H × Ω → Type w}
    [∀ h, NormedAddCommGroup (E h)] [∀ h, InnerProductSpace ℂ (E h)]
    [∀ h, CompleteSpace (E h)]
    [∀ z, NormedAddCommGroup (G z)] [∀ z, InnerProductSpace ℂ (G z)]
    [∀ z, CompleteSpace (G z)]
    (F : FundamentalFamily E) (Q : FundamentalFamily G) (P : RecordedSourceInstrument F Q) :
    RecordedSourceInstrument (uliftFamily.{r} F) (uliftFamily.{s} Q) :=
  transportRecordedSourceInstrument F (uliftFamily.{r} F) Q (uliftFamily.{s} Q)
    (fun h => uliftUnitary.{r} (E h)) (fun z => uliftUnitary.{s} (G z))
    (fun _ _ => rfl) (fun _ _ => rfl) P

@[simp] theorem uliftRecordedSourceInstrument_operation.{r,s,u,v,w,x}
    {H : Type u} [MeasurableSpace H] {Ω : Type x} [MeasurableSpace Ω]
    {E : H → Type v} {G : H × Ω → Type w}
    [∀ h, NormedAddCommGroup (E h)] [∀ h, InnerProductSpace ℂ (E h)]
    [∀ h, CompleteSpace (E h)]
    [∀ z, NormedAddCommGroup (G z)] [∀ z, InnerProductSpace ℂ (G z)]
    [∀ z, CompleteSpace (G z)]
    (F : FundamentalFamily E) (Q : FundamentalFamily G) (P : RecordedSourceInstrument F Q)
    (h : H) (s : Set Ω) (T : Nuc (ULift.{r} (E h))) :
    (uliftRecordedSourceInstrument.{r,s} F Q P).represented_physical.operation h s T =
      P.represented_physical.operation h s (recoverNuclear (uliftUnitary.{r} (E h)).toLinearIsometry T) := rfl

def uliftPhysicalLocalFamily.{r,s,u,v,w}
    (Ω : ℕ → Type u) [∀ n, MeasurableSpace (Ω n)] [∀ n, StandardBorelSpace (Ω n)]
    (D : PhysicalDomains Ω) (b : Bool)
    {E : (n : ℕ) → D.admissible n → Type v}
    [∀ n h, NormedAddCommGroup (E n h)] [∀ n h, InnerProductSpace ℂ (E n h)]
    [∀ n h, CompleteSpace (E n h)]
    (F : (n : ℕ) → FundamentalFamily (E n))
    {G : (n : ℕ) → D.actingDomain n b × Ω n → Type w}
    [∀ n z, NormedAddCommGroup (G n z)] [∀ n z, InnerProductSpace ℂ (G n z)]
    [∀ n z, CompleteSpace (G n z)]
    (Q : (n : ℕ) → FundamentalFamily (G n)) (P : PhysicalLocalFamily Ω D b F Q) :
    PhysicalLocalFamily Ω D b (fun n => uliftFamily.{r} (F n))
      (fun n => uliftFamily.{s} (Q n)) where
  instrument n := transportRecordedSourceInstrument
    (physicalActiveSource Ω D b F n)
    (physicalActiveSource Ω D b (fun n => uliftFamily.{r} (F n)) n)
    (Q n) (uliftFamily.{s} (Q n))
    (fun h => uliftUnitary.{r} (E n (D.actingHistory n b h)))
    (fun z => uliftUnitary.{s} (G n z)) (fun _ _ => rfl) (fun _ _ => rfl)
    (P.instrument n)
  off_graph n h := by
    ext T
    change (P.instrument n).represented_physical.operation h {x | (h,x) ∉ D.actingGraph n b}
      (recoverNuclear (uliftUnitary.{r} (E n (D.actingHistory n b h))).toLinearIsometry T) = 0
    rw [P.off_graph]
    rfl

@[simp] theorem uliftPhysicalLocalFamily_operation.{r,s,u,v,w}
    (Ω : ℕ → Type u) [∀ n, MeasurableSpace (Ω n)] [∀ n, StandardBorelSpace (Ω n)]
    (D : PhysicalDomains Ω) (b : Bool)
    {E : (n : ℕ) → D.admissible n → Type v}
    [∀ n h, NormedAddCommGroup (E n h)] [∀ n h, InnerProductSpace ℂ (E n h)]
    [∀ n h, CompleteSpace (E n h)]
    (F : (n : ℕ) → FundamentalFamily (E n))
    {G : (n : ℕ) → D.actingDomain n b × Ω n → Type w}
    [∀ n z, NormedAddCommGroup (G n z)] [∀ n z, InnerProductSpace ℂ (G n z)]
    [∀ n z, CompleteSpace (G n z)]
    (Q : (n : ℕ) → FundamentalFamily (G n)) (P : PhysicalLocalFamily Ω D b F Q)
    (n : ℕ) (h : D.actingDomain n b) (s : Set (Ω n))
    (T : Nuc (ULift.{r} (E n (D.actingHistory n b h)))) :
    ((uliftPhysicalLocalFamily.{r,s} Ω D b F Q P).instrument n).represented_physical.operation h s T =
      (P.instrument n).represented_physical.operation h s
        (recoverNuclear (uliftUnitary.{r} (E n (D.actingHistory n b h))).toLinearIsometry T) := rfl

theorem uliftPhysicalLocalFamily_on_physical.{r,s,u,v,w}
    (Ω : ℕ → Type u) [∀ n, MeasurableSpace (Ω n)] [∀ n, StandardBorelSpace (Ω n)]
    (D : PhysicalDomains Ω) (b : Bool)
    {E : (n : ℕ) → D.admissible n → Type v}
    [∀ n h, NormedAddCommGroup (E n h)] [∀ n h, InnerProductSpace ℂ (E n h)]
    [∀ n h, CompleteSpace (E n h)]
    (F : (n : ℕ) → FundamentalFamily (E n))
    {G : (n : ℕ) → D.actingDomain n b × Ω n → Type w}
    [∀ n z, NormedAddCommGroup (G n z)] [∀ n z, InnerProductSpace ℂ (G n z)]
    [∀ n z, CompleteSpace (G n z)]
    (Q : (n : ℕ) → FundamentalFamily (G n)) (P : PhysicalLocalFamily Ω D b F Q)
    (n : ℕ) (h : D.actingDomain n b) (s : Set (Ω n))
    (T : Nuc (E n (D.actingHistory n b h))) :
    ((uliftPhysicalLocalFamily.{r,s} Ω D b F Q P).instrument n).represented_physical.operation h s
      (padNuclear (uliftUnitary.{r} (E n (D.actingHistory n b h))).toLinearIsometry T) =
        (P.instrument n).represented_physical.operation h s T := by
  rw [uliftPhysicalLocalFamily_operation, recover_padNuclear]

theorem terminalSourceOperation_uliftInput.{r,u,v}
    {H : Type u} [MeasurableSpace H] {E : H → Type v}
    [∀ h, NormedAddCommGroup (E h)] [∀ h, InnerProductSpace ℂ (E h)]
    [∀ h, CompleteSpace (E h)] (F : FundamentalFamily E) (c : ℕ)
    (P : MatrixInstrument F (finiteOutputFamily (H := H) c) PUnit.{u+1})
    (h : H) (s : Set PUnit.{u+1}) :
    terminalSourceOperation (uliftInputMatrixInstrument.{r} F
      (finiteOutputFamily (H := H) c) P) h s = terminalSourceOperation P h s :=
  terminalSourceOperation_transportInput F (uliftFamily.{r} F)
    (fun h => uliftUnitary.{r} (E h)) (fun _ _ => rfl) c P h s

theorem completePhysicalTerminalLocal_uliftInput.{r,u,v}
    {H : Type u} [MeasurableSpace H] {E : H → Type v}
    [∀ h, NormedAddCommGroup (E h)] [∀ h, InnerProductSpace ℂ (E h)]
    [∀ h, CompleteSpace (E h)] (F : FundamentalFamily E) (c : ℕ)
    (P : MatrixInstrument F (finiteOutputFamily (H := H) c) PUnit.{u+1}) (hc : 0 < c) :
    completePhysicalTerminalLocal (uliftInputMatrixInstrument.{r} F
      (finiteOutputFamily (H := H) c) P) hc = completePhysicalTerminalLocal P hc :=
  completePhysicalTerminalLocal_transportInput F (uliftFamily.{r} F)
    (fun h => uliftUnitary.{r} (E h)) (fun _ _ => rfl) c P hc

end QuantumProver.MatrixPhysicalUniverseInstruments

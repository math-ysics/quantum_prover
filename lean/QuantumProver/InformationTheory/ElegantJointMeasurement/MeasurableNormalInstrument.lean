import QuantumProver.InformationTheory.ElegantJointMeasurement.MeasurableNuclearField
import QuantumProver.InformationTheory.ElegantJointMeasurement.NormalInstrumentAbsorption
import QuantumProver.InformationTheory.ElegantJointMeasurement.NormalSandwich
import QuantumProver.QuantumChannels.NuclearTensor

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section

open MeasureTheory Filter
open scoped BigOperators Topology Classical
open QuantumProver.ElegantJointMeasurement.MeasurableHilbertField QuantumProver.ElegantJointMeasurement.SeparableHilbertEmbedding
open QuantumProver.NuclearOperator (toOperator toOperator_injective)
open QuantumProver.HilbertNuclearCompression (compose toOperator_compose)
open QuantumProver.ElegantJointMeasurement.NormalInstrumentAbsorption (NormalOperation NormalCompletelyPositive)

namespace QuantumProver.ElegantJointMeasurement.MeasurableNormalInstrument

abbrev Nuclear (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [CompleteSpace V] := QuantumProver.ElegantJointMeasurement.MeasurableNuclearField.Nuclear V

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

def nuclearScalarForm (L : Nuclear V →L[ℂ] ℂ) : V →L⋆[ℂ] V →L[ℂ] ℂ :=
  (ContinuousLinearMap.compL ℂ V (Nuclear V) ℂ L).comp
    ((QuantumProver.MatrixNuclearTensor.rankOneCLM :
      (V →L[ℂ] ℂ) →L[ℂ] V →L[ℂ] Nuclear V).comp (innerSL ℂ))

def nuclearScalarOperator (L : Nuclear V →L[ℂ] ℂ) : V →L[ℂ] V :=
  (InnerProductSpace.continuousLinearMapOfBilin (nuclearScalarForm L)).adjoint

theorem nuclearScalarOperator_coefficient (L : Nuclear V →L[ℂ] ℂ) (x y : V) :
    inner ℂ x (nuclearScalarOperator L y) =
      L (QuantumProver.NuclearOperator.rankOne (innerSL ℂ x) y) := by
  rw [nuclearScalarOperator, ContinuousLinearMap.adjoint_inner_right,
    InnerProductSpace.continuousLinearMapOfBilin_apply]
  rfl

def nuclearMatrixElement (x y : V) : Nuclear V →L[ℂ] ℂ :=
  (innerSL ℂ x).comp ((ContinuousLinearMap.apply ℂ V y).comp toOperator)

@[simp] theorem nuclearMatrixElement_apply (x y : V) (T : Nuclear V) :
    nuclearMatrixElement x y T = inner ℂ x (toOperator T y) := rfl

universe u v w
variable {Z : Type u} [MeasurableSpace Z] {E : Z → Type v} {G : Z → Type w}
  [∀ z, NormedAddCommGroup (E z)] [∀ z, InnerProductSpace ℂ (E z)]
  [∀ z, CompleteSpace (E z)]
  [∀ z, NormedAddCommGroup (G z)] [∀ z, InnerProductSpace ℂ (G z)]
  [∀ z, CompleteSpace (G z)]

def FundamentalCoefficientsMeasurable (F : FundamentalFamily E) (H : FundamentalFamily G)
    (Φ : (z : Z) → NormalOperation (E z) (G z)) : Prop :=
  ∀ i j k l, Measurable (fun z => inner ℂ (H.vector z k)
    (toOperator (Φ z (QuantumProver.NuclearOperator.rankOne (innerSL ℂ (F.vector z i))
      (F.vector z j))) (H.vector z l)))

theorem measurable_operation_rankOne_coordinate (F : FundamentalFamily E)
    (H : FundamentalFamily G) (Φ : (z : Z) → NormalOperation (E z) (G z))
    (hΦ : FundamentalCoefficientsMeasurable F H Φ)
    (s t : (z : Z) → E z) (hs : F.IsMeasurableSection s) (ht : F.IsMeasurableSection t)
    (k l : ℕ) :
    Measurable (fun z => inner ℂ (H.vector z k)
      (toOperator (Φ z (QuantumProver.NuclearOperator.rankOne (innerSL ℂ (s z)) (t z)))
        (H.vector z l))) := by
  let A : (z : Z) → E z →L[ℂ] E z := fun z =>
    nuclearScalarOperator ((nuclearMatrixElement (H.vector z k) (H.vector z l)).comp (Φ z))
  have hA : QuantumProver.ElegantJointMeasurement.MeasurableHilbertOperator.CoefficientsMeasurable F F A := by
    intro i j
    have heq : (fun z => inner ℂ (F.vector z i) (A z (F.vector z j))) =
        (fun z => inner ℂ (H.vector z k)
          (toOperator (Φ z (QuantumProver.NuclearOperator.rankOne (innerSL ℂ (F.vector z i))
            (F.vector z j))) (H.vector z l))) := by
      funext z
      simp only [A, nuclearScalarOperator_coefficient, ContinuousLinearMap.comp_apply,
        nuclearMatrixElement_apply]
    rw [heq]
    exact hΦ i j k l
  have hm := QuantumProver.ElegantJointMeasurement.MeasurableHilbertOperator.measurable_matrix_element F F A hA t ht s hs
  have heq : (fun z => inner ℂ (s z) (A z (t z))) =
      (fun z => inner ℂ (H.vector z k)
        (toOperator (Φ z (QuantumProver.NuclearOperator.rankOne (innerSL ℂ (s z)) (t z)))
          (H.vector z l))) := by
    funext z
    simp only [A, nuclearScalarOperator_coefficient, ContinuousLinearMap.comp_apply,
      nuclearMatrixElement_apply]
  rw [heq] at hm
  exact hm

theorem coefficientsMeasurable_operation_rankOne (F : FundamentalFamily E)
    (H : FundamentalFamily G) (Φ : (z : Z) → NormalOperation (E z) (G z))
    (hΦ : FundamentalCoefficientsMeasurable F H Φ)
    (s t : (z : Z) → E z) (hs : F.IsMeasurableSection s) (ht : F.IsMeasurableSection t) :
    QuantumProver.ElegantJointMeasurement.MeasurableNuclearField.CoefficientsMeasurable H
      (fun z => Φ z (QuantumProver.NuclearOperator.rankOne (innerSL ℂ (s z)) (t z))) :=
  fun k l => measurable_operation_rankOne_coordinate F H Φ hΦ s t hs ht k l

theorem stronglyMeasurable_pad_operation_rankOne (F : FundamentalFamily E)
    (H : FundamentalFamily G) (Φ : (z : Z) → NormalOperation (E z) (G z))
    (hΦ : FundamentalCoefficientsMeasurable F H Φ)
    (s t : (z : Z) → E z) (hs : F.IsMeasurableSection s) (ht : F.IsMeasurableSection t) :
    StronglyMeasurable (fun z => padNuclear (H.embedding z)
      (Φ z (QuantumProver.NuclearOperator.rankOne (innerSL ℂ (s z)) (t z)))) :=
  QuantumProver.ElegantJointMeasurement.MeasurableNuclearField.stronglyMeasurable_padNuclearField H _
    (coefficientsMeasurable_operation_rankOne F H Φ hΦ s t hs ht)

def encodedOperation (F : FundamentalFamily E) (H : FundamentalFamily G)
    (Φ : (z : Z) → NormalOperation (E z) (G z)) (z : Z) :
    NormalOperation CommonHilbert CommonHilbert :=
  (padNuclear (H.embedding z)).comp ((Φ z).comp (recoverNuclear (F.embedding z)))

theorem recoverNuclear_rankOne {A B : Type*}
    [NormedAddCommGroup A] [InnerProductSpace ℂ A] [CompleteSpace A]
    [NormedAddCommGroup B] [InnerProductSpace ℂ B] [CompleteSpace B]
    (J : A →ₗᵢ[ℂ] B) (x y : B) :
    recoverNuclear J (QuantumProver.NuclearOperator.rankOne (innerSL ℂ x) y) =
      QuantumProver.NuclearOperator.rankOne (innerSL ℂ (J.toContinuousLinearMap.adjoint x))
        (J.toContinuousLinearMap.adjoint y) := by
  have hφ : (innerSL ℂ x).comp J.toContinuousLinearMap =
      innerSL ℂ (J.toContinuousLinearMap.adjoint x) := by
    ext a
    exact (J.toContinuousLinearMap.adjoint_inner_left a x).symm
  simp only [recoverNuclear, QuantumProver.HilbertNuclearCompression.compose_rankOne, hφ]

theorem embedding_adjoint_commonBasis (F : FundamentalFamily E) (z : Z) (n : ℕ) :
    (F.embedding z).toContinuousLinearMap.adjoint (commonBasis n) = F.frame n z :=
  QuantumProver.CountableFrameProjection.coordinateEmbedding_adjoint_commonBasis
    (F.vector z) (F.dense z) n

theorem stronglyMeasurable_encodedOperation_basisRankOne (F : FundamentalFamily E)
    (H : FundamentalFamily G) (Φ : (z : Z) → NormalOperation (E z) (G z))
    (hΦ : FundamentalCoefficientsMeasurable F H Φ) (i j : ℕ) :
    StronglyMeasurable (fun z => encodedOperation F H Φ z
      (QuantumProver.NuclearOperator.rankOne (innerSL ℂ (commonBasis j)) (commonBasis i))) := by
  have hm := stronglyMeasurable_pad_operation_rankOne F H Φ hΦ
    (F.frame j) (F.frame i) (F.frame_measurableSection j) (F.frame_measurableSection i)
  have heq : (fun z => encodedOperation F H Φ z
      (QuantumProver.NuclearOperator.rankOne (innerSL ℂ (commonBasis j)) (commonBasis i))) =
      (fun z => padNuclear (H.embedding z)
        (Φ z (QuantumProver.NuclearOperator.rankOne (innerSL ℂ (F.frame j z)) (F.frame i z)))) := by
    funext z
    simp only [encodedOperation, ContinuousLinearMap.comp_apply, recoverNuclear_rankOne,
      embedding_adjoint_commonBasis]
  rw [heq]
  exact hm

theorem stronglyMeasurable_encodedOperation_apply (F : FundamentalFamily E)
    (H : FundamentalFamily G) (Φ : (z : Z) → NormalOperation (E z) (G z))
    (hΦ : FundamentalCoefficientsMeasurable F H Φ) (U : Nuclear CommonHilbert) :
    StronglyMeasurable (fun z => encodedOperation F H Φ z U) := by
  have hm (n : ℕ) : StronglyMeasurable (fun z => encodedOperation F H Φ z
      (QuantumProver.HilbertNuclearCompression.compression commonBasis (Finset.range n) U)) := by
    have heq : (fun z => encodedOperation F H Φ z
        (QuantumProver.HilbertNuclearCompression.compression commonBasis (Finset.range n) U)) =
        (fun z => ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
          inner ℂ (commonBasis i) (toOperator U (commonBasis j)) •
            encodedOperation F H Φ z
              (QuantumProver.NuclearOperator.rankOne (innerSL ℂ (commonBasis j)) (commonBasis i))) := by
      funext z
      rw [QuantumProver.HilbertNuclearCompressionExpansion.compression_eq_coefficientCompression]
      simp only [QuantumProver.HilbertNuclearCompressionExpansion.coefficientCompression,
        map_sum, map_smul]
    rw [heq]
    apply Finset.stronglyMeasurable_fun_sum
    intro i hi
    apply Finset.stronglyMeasurable_fun_sum
    intro j hj
    exact (stronglyMeasurable_encodedOperation_basisRankOne F H Φ hΦ i j).const_smul
      (inner ℂ (commonBasis i) (toOperator U (commonBasis j)))
  apply stronglyMeasurable_of_tendsto (Filter.atTop : Filter ℕ) hm
  apply tendsto_pi_nhds.mpr
  intro z
  exact (encodedOperation F H Φ z).continuous.tendsto U |>.comp
    (QuantumProver.HilbertNuclearCompression.initial_compression_tendsto commonBasis U)

theorem stronglyMeasurable_encodedOperation_variable_apply (F : FundamentalFamily E)
    (H : FundamentalFamily G) (Φ : (z : Z) → NormalOperation (E z) (G z))
    (hΦ : FundamentalCoefficientsMeasurable F H Φ) (U : Z → Nuclear CommonHilbert)
    (hU : StronglyMeasurable U) :
    StronglyMeasurable (fun z => encodedOperation F H Φ z (U z)) :=
  QuantumProver.ElegantJointMeasurement.NormalInstrumentAbsorption.stronglyMeasurable_variable_apply _
    (stronglyMeasurable_encodedOperation_apply F H Φ hΦ) U hU

theorem stronglyMeasurable_pad_operation (F : FundamentalFamily E)
    (H : FundamentalFamily G) (Φ : (z : Z) → NormalOperation (E z) (G z))
    (hΦ : FundamentalCoefficientsMeasurable F H Φ) (T : (z : Z) → Nuclear (E z))
    (hT : QuantumProver.ElegantJointMeasurement.MeasurableNuclearField.CoefficientsMeasurable F T) :
    StronglyMeasurable (fun z => padNuclear (H.embedding z) (Φ z (T z))) := by
  have hm := stronglyMeasurable_encodedOperation_variable_apply F H Φ hΦ
    (QuantumProver.ElegantJointMeasurement.MeasurableNuclearField.padNuclearField F T)
    (QuantumProver.ElegantJointMeasurement.MeasurableNuclearField.stronglyMeasurable_padNuclearField F T hT)
  simpa only [encodedOperation, ContinuousLinearMap.comp_apply,
    QuantumProver.ElegantJointMeasurement.MeasurableNuclearField.padNuclearField, recover_padNuclear] using hm

theorem recover_encodedOperation_on_physical (F : FundamentalFamily E)
    (H : FundamentalFamily G) (Φ : (z : Z) → NormalOperation (E z) (G z))
    (z : Z) (T : Nuclear (E z)) :
    recoverNuclear (H.embedding z)
      (encodedOperation F H Φ z (padNuclear (F.embedding z) T)) = Φ z T := by
  simp only [encodedOperation, ContinuousLinearMap.comp_apply, recover_padNuclear]

theorem encodedOperation_output_supported (F : FundamentalFamily E)
    (H : FundamentalFamily G) (Φ : (z : Z) → NormalOperation (E z) (G z))
    (z : Z) (U : Nuclear CommonHilbert) :
    compose (H.rangeProjection z) (H.rangeProjection z) (encodedOperation F H Φ z U) =
      encodedOperation F H Φ z U := by
  exact QuantumProver.ElegantJointMeasurement.MeasurableNuclearField.padNuclearField_supported H
    (fun z => Φ z (recoverNuclear (F.embedding z) U)) z

theorem encodedOperation_trace (F : FundamentalFamily E)
    (H : FundamentalFamily G) (Φ : (z : Z) → NormalOperation (E z) (G z))
    (hTP : ∀ z (T : Nuclear (E z)), QuantumProver.HilbertNuclearTrace.trace (Φ z T) =
      QuantumProver.HilbertNuclearTrace.trace T) (z : Z) (U : Nuclear CommonHilbert) :
    QuantumProver.HilbertNuclearTrace.trace (encodedOperation F H Φ z U) =
      QuantumProver.HilbertNuclearTrace.trace
        (compose (F.rangeProjection z) (F.rangeProjection z) U) := by
  rw [encodedOperation, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    trace_padNuclear, hTP]
  rw [← QuantumProver.ElegantJointMeasurement.MeasurableNuclearField.pad_recover_eq_projection,
    trace_padNuclear]

theorem encodedOperation_normalCompletelyPositive (F : FundamentalFamily E)
    (H : FundamentalFamily G) (Φ : (z : Z) → NormalOperation (E z) (G z))
    (z : Z) (hΦ : NormalCompletelyPositive (Φ z)) :
    NormalCompletelyPositive (encodedOperation F H Φ z) := by
  have hOut : NormalCompletelyPositive (padNuclear (H.embedding z)) :=
    QuantumProver.ElegantJointMeasurement.NormalSandwich.normalCompletelyPositive_sandwich
      (H.embedding z).toContinuousLinearMap
  have hIn : NormalCompletelyPositive (recoverNuclear (F.embedding z)) := by
    simpa only [QuantumProver.ElegantJointMeasurement.NormalSandwich.sandwich, recoverNuclear,
      ContinuousLinearMap.adjoint_adjoint] using
      QuantumProver.ElegantJointMeasurement.NormalSandwich.normalCompletelyPositive_sandwich
        (F.embedding z).toContinuousLinearMap.adjoint
  exact QuantumProver.ElegantJointMeasurement.NormalSandwich.normalCompletelyPositive_comp _ _ hOut
    (QuantumProver.ElegantJointMeasurement.NormalSandwich.normalCompletelyPositive_comp _ _ hΦ hIn)

theorem inputProjection_adjoint (F : FundamentalFamily E) (z : Z) :
    (F.rangeProjection z).adjoint = F.rangeProjection z :=
  QuantumProver.CountableFrameProjection.rangeProjection_adjoint (F.vector z) (F.dense z)

theorem inputProjection_idempotent (F : FundamentalFamily E) (z : Z) :
    (F.rangeProjection z).comp (F.rangeProjection z) = F.rangeProjection z :=
  QuantumProver.CountableFrameProjection.rangeProjection_idempotent (F.vector z) (F.dense z)

theorem measurable_trace_input_projection (F : FundamentalFamily E)
    (U : Nuclear CommonHilbert) :
    Measurable (fun z => QuantumProver.HilbertNuclearTrace.trace
      (compose (F.rangeProjection z) (F.rangeProjection z) U)) := by
  have hm := (QuantumProver.HilbertNuclearTrace.trace (𝕜 := ℂ) (E := CommonHilbert)).continuous
    |>.comp_stronglyMeasurable
      (QuantumProver.ElegantJointMeasurement.MeasurableNuclearField.stronglyMeasurable_pad_recoverNuclearField F
        (fun _ => U) stronglyMeasurable_const)
  have heq : (fun z => QuantumProver.HilbertNuclearTrace.trace
      (QuantumProver.ElegantJointMeasurement.MeasurableNuclearField.padNuclearField F
        (QuantumProver.ElegantJointMeasurement.MeasurableNuclearField.recoverNuclearField F (fun _ => U)) z)) =
      (fun z => QuantumProver.HilbertNuclearTrace.trace
        (compose (F.rangeProjection z) (F.rangeProjection z) U)) := by
    funext z
    rw [QuantumProver.ElegantJointMeasurement.MeasurableNuclearField.padNuclearField,
      QuantumProver.ElegantJointMeasurement.MeasurableNuclearField.recoverNuclearField,
      QuantumProver.ElegantJointMeasurement.MeasurableNuclearField.pad_recover_eq_projection]
  rw [heq] at hm
  exact hm.measurable

structure MatrixInstrument (F : FundamentalFamily E) (H : FundamentalFamily G)
    (Ω : Type*) [MeasurableSpace Ω] where
  operation : (z : Z) → Set Ω → NormalOperation (E z) (G z)
  empty : ∀ z, operation z ∅ = 0
  countable_additivity : ∀ z (s : ℕ → Set Ω), (∀ n, MeasurableSet (s n)) →
    Pairwise (fun i j => Disjoint (s i) (s j)) → ∀ T : Nuclear (E z),
      HasSum (fun n => operation z (s n) T) (operation z (⋃ n, s n) T)
  completelyPositive : ∀ z s, MeasurableSet s → NormalCompletelyPositive (operation z s)
  fundamental_measurable : ∀ s, MeasurableSet s →
    FundamentalCoefficientsMeasurable F H (fun z => operation z s)
  trace_preserving : ∀ z (T : Nuclear (E z)),
    QuantumProver.HilbertNuclearTrace.trace (operation z Set.univ T) =
      QuantumProver.HilbertNuclearTrace.trace T

namespace MatrixInstrument
variable {Ω : Type*} [MeasurableSpace Ω]
  {F : FundamentalFamily E} {H : FundamentalFamily G}
  (P : MatrixInstrument F H Ω)

def codedOperation (z : Z) (s : Set Ω) : NormalOperation CommonHilbert CommonHilbert :=
  encodedOperation F H (fun z => P.operation z s) z

theorem codedOperation_empty (z : Z) : P.codedOperation z ∅ = 0 := by
  ext U
  simp only [codedOperation, encodedOperation, ContinuousLinearMap.comp_apply,
    P.empty, zero_apply, map_zero]

theorem codedOperation_countable_additivity (z : Z) (s : ℕ → Set Ω)
    (hs : ∀ n, MeasurableSet (s n)) (hd : Pairwise (fun i j => Disjoint (s i) (s j)))
    (U : Nuclear CommonHilbert) :
    HasSum (fun n => P.codedOperation z (s n) U) (P.codedOperation z (⋃ n, s n) U) := by
  have h := (padNuclear (H.embedding z)).hasSum
    (P.countable_additivity z s hs hd (recoverNuclear (F.embedding z) U))
  simpa only [codedOperation, encodedOperation, ContinuousLinearMap.comp_apply] using h

theorem codedOperation_completelyPositive (z : Z) (s : Set Ω) (hs : MeasurableSet s) :
    NormalCompletelyPositive (P.codedOperation z s) :=
  encodedOperation_normalCompletelyPositive F H _ z (P.completelyPositive z s hs)

theorem stronglyMeasurable_codedOperation (s : Set Ω) (hs : MeasurableSet s)
    (U : Nuclear CommonHilbert) : StronglyMeasurable (fun z => P.codedOperation z s U) :=
  stronglyMeasurable_encodedOperation_apply F H _ (P.fundamental_measurable s hs) U

theorem stronglyMeasurable_codedOperation_variable (s : Set Ω) (hs : MeasurableSet s)
    (U : Z → Nuclear CommonHilbert) (hU : StronglyMeasurable U) :
    StronglyMeasurable (fun z => P.codedOperation z s (U z)) :=
  stronglyMeasurable_encodedOperation_variable_apply F H _ (P.fundamental_measurable s hs) U hU

theorem codedOperation_recover_physical (z : Z) (s : Set Ω) (T : Nuclear (E z)) :
    recoverNuclear (H.embedding z)
      (P.codedOperation z s (padNuclear (F.embedding z) T)) = P.operation z s T :=
  recover_encodedOperation_on_physical F H _ z T

theorem codedOperation_output_supported (z : Z) (s : Set Ω) (U : Nuclear CommonHilbert) :
    compose (H.rangeProjection z) (H.rangeProjection z) (P.codedOperation z s U) =
      P.codedOperation z s U := encodedOperation_output_supported F H _ z U

theorem codedOperation_total_trace (z : Z) (U : Nuclear CommonHilbert) :
    QuantumProver.HilbertNuclearTrace.trace (P.codedOperation z Set.univ U) =
      QuantumProver.HilbertNuclearTrace.trace
        (compose (F.rangeProjection z) (F.rangeProjection z) U) :=
  encodedOperation_trace F H _ P.trace_preserving z U

end MatrixInstrument

end QuantumProver.ElegantJointMeasurement.MeasurableNormalInstrument

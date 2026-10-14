import QuantumProver.InformationTheory.ElegantJointMeasurement.MeasurableHilbertField

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section

open MeasureTheory
open QuantumProver.ElegantJointMeasurement.MeasurableHilbertField
open QuantumProver.ElegantJointMeasurement.SeparableHilbertEmbedding

namespace QuantumProver.ElegantJointMeasurement.MeasurableHilbertOperator

universe u v w
variable {Z : Type u} [MeasurableSpace Z]
  {E : Z → Type v} {G : Z → Type w}
  [∀ z, NormedAddCommGroup (E z)] [∀ z, InnerProductSpace ℂ (E z)]
  [∀ z, CompleteSpace (E z)]
  [∀ z, NormedAddCommGroup (G z)] [∀ z, InnerProductSpace ℂ (G z)]
  [∀ z, CompleteSpace (G z)]

def CoefficientsMeasurable (F : FundamentalFamily E) (H : FundamentalFamily G)
    (T : (z : Z) → E z →L[ℂ] G z) : Prop :=
  ∀ i j, Measurable (fun z => inner ℂ (H.vector z i) (T z (F.vector z j)))

theorem measurable_inner_sections (F : FundamentalFamily E)
    (s t : (z : Z) → E z) (hs : F.IsMeasurableSection s) (ht : F.IsMeasurableSection t) :
    Measurable (fun z => inner ℂ (s z) (t z)) := by
  have h : Measurable (fun z =>
      inner ℂ (F.embedding z (s z)) (F.embedding z (t z))) :=
    ((F.stronglyMeasurable_embedding_section s hs).inner
      (𝕜 := ℂ) (F.stronglyMeasurable_embedding_section t ht)).measurable
  simpa only [LinearIsometry.inner_map_map] using h

theorem adjoint_fundamental_isMeasurableSection
    (F : FundamentalFamily E) (H : FundamentalFamily G)
    (T : (z : Z) → E z →L[ℂ] G z) (hT : CoefficientsMeasurable F H T) (i : ℕ) :
    F.IsMeasurableSection (fun z => (T z).adjoint (H.vector z i)) := by
  intro j
  have h := continuous_star.measurable.comp (hT i j)
  convert h using 1
  funext z
  rw [ContinuousLinearMap.adjoint_inner_right]
  exact (inner_conj_symm _ _).symm

theorem apply_isMeasurableSection
    (F : FundamentalFamily E) (H : FundamentalFamily G)
    (T : (z : Z) → E z →L[ℂ] G z) (hT : CoefficientsMeasurable F H T)
    (s : (z : Z) → E z) (hs : F.IsMeasurableSection s) :
    H.IsMeasurableSection (fun z => T z (s z)) := by
  intro i
  have h := measurable_inner_sections F
    (fun z => (T z).adjoint (H.vector z i)) s
    (adjoint_fundamental_isMeasurableSection F H T hT i) hs
  simpa only [ContinuousLinearMap.adjoint_inner_left] using h

theorem stronglyMeasurable_encoded_apply
    (F : FundamentalFamily E) (H : FundamentalFamily G)
    (T : (z : Z) → E z →L[ℂ] G z) (hT : CoefficientsMeasurable F H T)
    (s : (z : Z) → E z) (hs : F.IsMeasurableSection s) :
    StronglyMeasurable (fun z => H.embedding z (T z (s z))) :=
  H.stronglyMeasurable_embedding_section _
    (apply_isMeasurableSection F H T hT s hs)

theorem measurable_norm_apply
    (F : FundamentalFamily E) (H : FundamentalFamily G)
    (T : (z : Z) → E z →L[ℂ] G z) (hT : CoefficientsMeasurable F H T)
    (s : (z : Z) → E z) (hs : F.IsMeasurableSection s) :
    Measurable (fun z => ‖T z (s z)‖) :=
  H.measurable_norm_section _ (apply_isMeasurableSection F H T hT s hs)

theorem measurable_matrix_element
    (F : FundamentalFamily E) (H : FundamentalFamily G)
    (T : (z : Z) → E z →L[ℂ] G z) (hT : CoefficientsMeasurable F H T)
    (s : (z : Z) → E z) (hs : F.IsMeasurableSection s)
    (t : (z : Z) → G z) (ht : H.IsMeasurableSection t) :
    Measurable (fun z => inner ℂ (t z) (T z (s z))) :=
  measurable_inner_sections H t _ ht (apply_isMeasurableSection F H T hT s hs)

theorem adjoint_coefficientsMeasurable
    (F : FundamentalFamily E) (H : FundamentalFamily G)
    (T : (z : Z) → E z →L[ℂ] G z) (hT : CoefficientsMeasurable F H T) :
    CoefficientsMeasurable H F (fun z => (T z).adjoint) :=
  fun i j => adjoint_fundamental_isMeasurableSection F H T hT j i

theorem adjoint_apply_isMeasurableSection
    (F : FundamentalFamily E) (H : FundamentalFamily G)
    (T : (z : Z) → E z →L[ℂ] G z) (hT : CoefficientsMeasurable F H T)
    (t : (z : Z) → G z) (ht : H.IsMeasurableSection t) :
    F.IsMeasurableSection (fun z => (T z).adjoint (t z)) :=
  apply_isMeasurableSection H F (fun z => (T z).adjoint)
    (adjoint_coefficientsMeasurable F H T hT) t ht

theorem stronglyMeasurable_encoded_adjoint_apply
    (F : FundamentalFamily E) (H : FundamentalFamily G)
    (T : (z : Z) → E z →L[ℂ] G z) (hT : CoefficientsMeasurable F H T)
    (t : (z : Z) → G z) (ht : H.IsMeasurableSection t) :
    StronglyMeasurable (fun z => F.embedding z ((T z).adjoint (t z))) :=
  F.stronglyMeasurable_embedding_section _
    (adjoint_apply_isMeasurableSection F H T hT t ht)

theorem coefficientsMeasurable_iff_preserves_sections
    (F : FundamentalFamily E) (H : FundamentalFamily G)
    (T : (z : Z) → E z →L[ℂ] G z) :
    CoefficientsMeasurable F H T ↔
      ∀ s : (z : Z) → E z, F.IsMeasurableSection s →
        H.IsMeasurableSection (fun z => T z (s z)) := by
  constructor
  · exact fun hT s hs => apply_isMeasurableSection F H T hT s hs
  · intro h i j
    exact h (fun z => F.vector z j) (F.fundamental_measurableSection j) i

theorem decode_isMeasurableSection (F : FundamentalFamily E)
    (u : Z → CommonHilbert) (hu : StronglyMeasurable u) :
    F.IsMeasurableSection (fun z => (F.embedding z).toContinuousLinearMap.adjoint (u z)) := by
  intro i
  have h : Measurable (fun z =>
      inner ℂ (F.embedding z (F.vector z i)) (u z)) :=
    ((F.stronglyMeasurable_embedding_section _
      (F.fundamental_measurableSection i)).inner (𝕜 := ℂ) hu).measurable
  simpa only [ContinuousLinearMap.adjoint_inner_right,
    LinearIsometry.coe_toContinuousLinearMap] using h

def encodedOperator (F : FundamentalFamily E) (H : FundamentalFamily G)
    (T : (z : Z) → E z →L[ℂ] G z) (z : Z) :
    CommonHilbert →L[ℂ] CommonHilbert :=
  (H.embedding z).toContinuousLinearMap.comp
    ((T z).comp (F.embedding z).toContinuousLinearMap.adjoint)

theorem encodedOperator_apply (F : FundamentalFamily E) (H : FundamentalFamily G)
    (T : (z : Z) → E z →L[ℂ] G z) (z : Z) (u : CommonHilbert) :
    encodedOperator F H T z u =
      H.embedding z (T z ((F.embedding z).toContinuousLinearMap.adjoint u)) := rfl

theorem encodedOperator_apply_embedding
    (F : FundamentalFamily E) (H : FundamentalFamily G)
    (T : (z : Z) → E z →L[ℂ] G z) (z : Z) (x : E z) :
    encodedOperator F H T z (F.embedding z x) = H.embedding z (T z x) := by
  rw [encodedOperator_apply, adjoint_embedding_apply]

theorem encodedOperator_adjoint
    (F : FundamentalFamily E) (H : FundamentalFamily G)
    (T : (z : Z) → E z →L[ℂ] G z) (z : Z) :
    (encodedOperator F H T z).adjoint =
      encodedOperator H F (fun z => (T z).adjoint) z := by
  simp only [encodedOperator, ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_adjoint, ContinuousLinearMap.comp_assoc]

theorem stronglyMeasurable_encodedOperator_apply
    (F : FundamentalFamily E) (H : FundamentalFamily G)
    (T : (z : Z) → E z →L[ℂ] G z) (hT : CoefficientsMeasurable F H T)
    (u : Z → CommonHilbert) (hu : StronglyMeasurable u) :
    StronglyMeasurable (fun z => encodedOperator F H T z (u z)) := by
  simpa only [encodedOperator_apply] using
    stronglyMeasurable_encoded_apply F H T hT
      (fun z => (F.embedding z).toContinuousLinearMap.adjoint (u z))
      (decode_isMeasurableSection F u hu)

theorem stronglyMeasurable_encodedOperator_apply_const
    (F : FundamentalFamily E) (H : FundamentalFamily G)
    (T : (z : Z) → E z →L[ℂ] G z) (hT : CoefficientsMeasurable F H T)
    (u : CommonHilbert) :
    StronglyMeasurable (fun z => encodedOperator F H T z u) :=
  stronglyMeasurable_encodedOperator_apply F H T hT (fun _ => u) stronglyMeasurable_const

theorem stronglyMeasurable_encodedOperator_adjoint_apply
    (F : FundamentalFamily E) (H : FundamentalFamily G)
    (T : (z : Z) → E z →L[ℂ] G z) (hT : CoefficientsMeasurable F H T)
    (u : Z → CommonHilbert) (hu : StronglyMeasurable u) :
    StronglyMeasurable (fun z => (encodedOperator F H T z).adjoint (u z)) := by
  simpa only [encodedOperator_adjoint] using
    stronglyMeasurable_encodedOperator_apply H F (fun z => (T z).adjoint)
      (adjoint_coefficientsMeasurable F H T hT) u hu

end QuantumProver.ElegantJointMeasurement.MeasurableHilbertOperator

import QuantumProver.InformationTheory.WernerEndpoint.ContinuousCPRepresentation
import QuantumProver.InformationTheory.WernerEndpoint.CPProtocol
import QuantumProver.InformationTheory.WernerEndpoint.MeasurableStateProtocol

set_option autoImplicit false
set_option maxHeartbeats 1200000

noncomputable section

namespace QuantumProver.WernerEndpoint.ContinuousCPProtocol

open MeasureTheory Matrix Filter
open OperationalEndpointCost MatrixContinuousStateProtocol LocalChannelMoments
open MatrixCPProtocol ContinuousCPRepresentation
open QuantumProver.SuperchannelDiscrimination.CPTPKraus
open scoped BigOperators ComplexOrder MatrixOrder Matrix Kronecker
  Matrix.Norms.L2Operator Topology

universe u
variable {Ω : Type u} [MeasurableSpace Ω]
variable {a b p c d height : ℕ}

abbrev JointMatrix (a b : ℕ) := Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ

def aliceReferenceCLM (Φ : LocalMap a p) : JointMatrix a b →L[ℂ] JointMatrix p b :=
  (QuantumProver.SuperchannelDiscrimination.CPWrappers.amplifyMap Φ (Fin b)).toContinuousLinearMap

def bobReferenceCLM (Φ : LocalMap b p) : JointMatrix a b →L[ℂ] JointMatrix a p :=
  (QuantumProver.SuperchannelDiscrimination.CPWrappers.amplifyLeftMap Φ (Fin a)).toContinuousLinearMap

@[simp] theorem aliceReferenceCLM_apply (Φ : LocalMap a p) (ρ : JointMatrix a b) :
    aliceReferenceCLM Φ ρ = aliceReferenceApply Φ ρ := rfl

@[simp] theorem bobReferenceCLM_apply (Φ : LocalMap b p) (ρ : JointMatrix a b) :
    bobReferenceCLM Φ ρ = bobReferenceApply Φ ρ := rfl

theorem refinedGram_complete_fin (μ : Measure Ω) [IsFiniteMeasure μ]
    (Φ : Ω → LocalMap a p)
    (hΦ : QuantumProver.ElegantJointMeasurement.ContinuousCPInstruments.CoordinateMeasurable Φ)
    (hCP : ∀ x, CompletelyPositive (Φ x))
    (hTotal : QuantumProver.ElegantJointMeasurement.ContinuousCPInstruments.MatrixTraceComplete μ Φ) :
    (∫ xq, (refinedKraus Φ xq).conjTranspose * refinedKraus Φ xq
      ∂refinedMeasure (I := Fin a) (O := Fin p) μ) = 1 := by
  classical
  by_cases hInput : Nonempty (Fin a)
  · let := hInput
    exact refinedGram_complete μ Φ hΦ hCP hTotal
  · let : IsEmpty (Fin a) := not_nonempty_iff.mp hInput
    ext i j
    exact isEmptyElim i

theorem aliceReferenceCLM_eq_refined_sum (Φ : Ω → LocalMap a p)
    (hCP : ∀ x, CompletelyPositive (Φ x)) (x : Ω) :
    aliceReferenceCLM (b := b) (Φ x) =
      ∑ q : Hidden (Fin a) (Fin p), leftSandwichCLM (refinedKraus Φ (x,q)) := by
  apply ContinuousLinearMap.ext
  intro ρ
  simpa only [_root_.sum_apply, leftSandwichCLM_apply,
    aliceReferenceCLM_apply, aliceReferenceApply] using
      referenceAction_eq_refined_sum Φ hCP x ρ

theorem bobReferenceCLM_eq_refined_sum (Φ : Ω → LocalMap b p)
    (hCP : ∀ x, CompletelyPositive (Φ x)) (x : Ω) :
    bobReferenceCLM (a := a) (Φ x) =
      ∑ q : Hidden (Fin b) (Fin p), rightSandwichCLM (refinedKraus Φ (x,q)) := by
  apply ContinuousLinearMap.ext
  intro ρ
  simp only [_root_.sum_apply, rightSandwichCLM_apply,
    bobReferenceCLM_apply, bobReferenceApply]
  rw [canonicalKraus_reconstruct_map (Φ x) (hCP x), QuantumProver.ElegantJointMeasurement.CP.amplification_krausMap]
  simp only [QuantumProver.ElegantJointMeasurement.CP.ancillaryKraus]
  exact ((Fintype.equivFin (Fin b × Fin p)).symm.sum_comp (fun q =>
    ((1 : Matrix (Fin a) (Fin a) ℂ) ⊗ₖ canonicalKraus (Φ x) q) * ρ *
      ((1 : Matrix (Fin a) (Fin a) ℂ) ⊗ₖ canonicalKraus (Φ x) q).conjTranspose)).symm

def aliceCPNode (μ : Measure Ω) (Φ : Ω → LocalMap a p)
    (child : Ω → Tree.{u} c d p b height) : Tree.{u} c d a b (height + 1) :=
  Tree.alice (Ω × Hidden (Fin a) (Fin p)) inferInstance
    (refinedMeasure (I := Fin a) (O := Fin p) μ) (refinedKraus Φ)
    (fun xq => child xq.1)

def bobCPNode (μ : Measure Ω) (Φ : Ω → LocalMap b p)
    (child : Ω → Tree.{u} c d a p height) : Tree.{u} c d a b (height + 1) :=
  Tree.bob (Ω × Hidden (Fin b) (Fin p)) inferInstance
    (refinedMeasure (I := Fin b) (O := Fin p) μ) (refinedKraus Φ)
    (fun xq => child xq.1)

theorem aliceCPNode_measurableWellFormed (μ : Measure Ω) [IsFiniteMeasure μ]
    (Φ : Ω → LocalMap a p)
    (hΦ : QuantumProver.ElegantJointMeasurement.ContinuousCPInstruments.CoordinateMeasurable Φ)
    (hCP : ∀ x, CompletelyPositive (Φ x))
    (hTotal : QuantumProver.ElegantJointMeasurement.ContinuousCPInstruments.MatrixTraceComplete μ Φ)
    (child : Ω → Tree.{u} c d p b height)
    (hChild : ∀ x, MatrixMeasurableStateProtocol.MeasurableWellFormed (child x))
    (hMeas : AEStronglyMeasurable (fun x => channel (child x)) μ) :
    MatrixMeasurableStateProtocol.MeasurableWellFormed (aliceCPNode μ Φ child) := by
  refine ⟨?_, refinedKraus_measurable Φ hΦ, refinedGram_complete_fin μ Φ hΦ hCP hTotal,
    fun xq => hChild xq.1, ?_⟩
  · unfold refinedMeasure
    infer_instance
  · exact hMeas.comp_fst

theorem bobCPNode_measurableWellFormed (μ : Measure Ω) [IsFiniteMeasure μ]
    (Φ : Ω → LocalMap b p)
    (hΦ : QuantumProver.ElegantJointMeasurement.ContinuousCPInstruments.CoordinateMeasurable Φ)
    (hCP : ∀ x, CompletelyPositive (Φ x))
    (hTotal : QuantumProver.ElegantJointMeasurement.ContinuousCPInstruments.MatrixTraceComplete μ Φ)
    (child : Ω → Tree.{u} c d a p height)
    (hChild : ∀ x, MatrixMeasurableStateProtocol.MeasurableWellFormed (child x))
    (hMeas : AEStronglyMeasurable (fun x => channel (child x)) μ) :
    MatrixMeasurableStateProtocol.MeasurableWellFormed (bobCPNode μ Φ child) := by
  refine ⟨?_, refinedKraus_measurable Φ hΦ, refinedGram_complete_fin μ Φ hΦ hCP hTotal,
    fun xq => hChild xq.1, ?_⟩
  · unfold refinedMeasure
    infer_instance
  · exact hMeas.comp_fst

private theorem aliceRefinedMoment_integrable (μ : Measure Ω) [IsFiniteMeasure μ]
    (Φ : Ω → LocalMap a p)
    (hΦ : QuantumProver.ElegantJointMeasurement.ContinuousCPInstruments.CoordinateMeasurable Φ)
    (hCP : ∀ x, CompletelyPositive (Φ x))
    (hTotal : QuantumProver.ElegantJointMeasurement.ContinuousCPInstruments.MatrixTraceComplete μ Φ)
    (child : Ω → Tree.{u} c d p b height)
    (hChild : ∀ x, MatrixMeasurableStateProtocol.MeasurableWellFormed (child x))
    (hMeas : AEStronglyMeasurable (fun x => channel (child x)) μ) :
    Integrable (fun xq => (channel (child xq.1)).comp
      (leftSandwichCLM (refinedKraus Φ xq)))
      (refinedMeasure (I := Fin a) (O := Fin p) μ) := by
  have hWF := MatrixMeasurableStateProtocol.measurableWellFormed_implies_wellFormed
    _ (aliceCPNode_measurableWellFormed μ Φ hΦ hCP hTotal child hChild hMeas)
  exact hWF.2.2.2.2.2

private theorem bobRefinedMoment_integrable (μ : Measure Ω) [IsFiniteMeasure μ]
    (Φ : Ω → LocalMap b p)
    (hΦ : QuantumProver.ElegantJointMeasurement.ContinuousCPInstruments.CoordinateMeasurable Φ)
    (hCP : ∀ x, CompletelyPositive (Φ x))
    (hTotal : QuantumProver.ElegantJointMeasurement.ContinuousCPInstruments.MatrixTraceComplete μ Φ)
    (child : Ω → Tree.{u} c d a p height)
    (hChild : ∀ x, MatrixMeasurableStateProtocol.MeasurableWellFormed (child x))
    (hMeas : AEStronglyMeasurable (fun x => channel (child x)) μ) :
    Integrable (fun xq => (channel (child xq.1)).comp
      (rightSandwichCLM (refinedKraus Φ xq)))
      (refinedMeasure (I := Fin b) (O := Fin p) μ) := by
  have hWF := MatrixMeasurableStateProtocol.measurableWellFormed_implies_wellFormed
    _ (bobCPNode_measurableWellFormed μ Φ hΦ hCP hTotal child hChild hMeas)
  exact hWF.2.2.2.2.2

private theorem aliceMoment_eq_refined_sum (Φ : Ω → LocalMap a p)
    (hCP : ∀ x, CompletelyPositive (Φ x)) (child : Ω → Tree.{u} c d p b height)
    (x : Ω) :
    (channel (child x)).comp (aliceReferenceCLM (Φ x)) =
      ∑ q : Hidden (Fin a) (Fin p), (channel (child x)).comp
        (leftSandwichCLM (refinedKraus Φ (x,q))) := by
  rw [aliceReferenceCLM_eq_refined_sum Φ hCP x]
  apply ContinuousLinearMap.ext
  intro ρ
  simp only [ContinuousLinearMap.comp_apply, _root_.sum_apply, map_sum]

private theorem bobMoment_eq_refined_sum (Φ : Ω → LocalMap b p)
    (hCP : ∀ x, CompletelyPositive (Φ x)) (child : Ω → Tree.{u} c d a p height)
    (x : Ω) :
    (channel (child x)).comp (bobReferenceCLM (Φ x)) =
      ∑ q : Hidden (Fin b) (Fin p), (channel (child x)).comp
        (rightSandwichCLM (refinedKraus Φ (x,q))) := by
  rw [bobReferenceCLM_eq_refined_sum Φ hCP x]
  apply ContinuousLinearMap.ext
  intro ρ
  simp only [ContinuousLinearMap.comp_apply, _root_.sum_apply, map_sum]

theorem aliceMoment_integrable (μ : Measure Ω) [IsFiniteMeasure μ]
    (Φ : Ω → LocalMap a p)
    (hΦ : QuantumProver.ElegantJointMeasurement.ContinuousCPInstruments.CoordinateMeasurable Φ)
    (hCP : ∀ x, CompletelyPositive (Φ x))
    (hTotal : QuantumProver.ElegantJointMeasurement.ContinuousCPInstruments.MatrixTraceComplete μ Φ)
    (child : Ω → Tree.{u} c d p b height)
    (hChild : ∀ x, MatrixMeasurableStateProtocol.MeasurableWellFormed (child x))
    (hMeas : AEStronglyMeasurable (fun x => channel (child x)) μ) :
    Integrable (fun x => (channel (child x)).comp (aliceReferenceCLM (Φ x))) μ := by
  have hMoment := aliceRefinedMoment_integrable μ Φ hΦ hCP hTotal child hChild hMeas
  unfold refinedMeasure at hMoment
  have hInner := Integrable.integral_prod_left (E := Channel c d a b) hMoment
  simpa only [integral_count, ← aliceMoment_eq_refined_sum Φ hCP child] using hInner

theorem bobMoment_integrable (μ : Measure Ω) [IsFiniteMeasure μ]
    (Φ : Ω → LocalMap b p)
    (hΦ : QuantumProver.ElegantJointMeasurement.ContinuousCPInstruments.CoordinateMeasurable Φ)
    (hCP : ∀ x, CompletelyPositive (Φ x))
    (hTotal : QuantumProver.ElegantJointMeasurement.ContinuousCPInstruments.MatrixTraceComplete μ Φ)
    (child : Ω → Tree.{u} c d a p height)
    (hChild : ∀ x, MatrixMeasurableStateProtocol.MeasurableWellFormed (child x))
    (hMeas : AEStronglyMeasurable (fun x => channel (child x)) μ) :
    Integrable (fun x => (channel (child x)).comp (bobReferenceCLM (Φ x))) μ := by
  have hMoment := bobRefinedMoment_integrable μ Φ hΦ hCP hTotal child hChild hMeas
  unfold refinedMeasure at hMoment
  have hInner := Integrable.integral_prod_left (E := Channel c d a b) hMoment
  simpa only [integral_count, ← bobMoment_eq_refined_sum Φ hCP child] using hInner

theorem aliceCPNode_channel (μ : Measure Ω) [IsFiniteMeasure μ]
    (Φ : Ω → LocalMap a p)
    (hΦ : QuantumProver.ElegantJointMeasurement.ContinuousCPInstruments.CoordinateMeasurable Φ)
    (hCP : ∀ x, CompletelyPositive (Φ x))
    (hTotal : QuantumProver.ElegantJointMeasurement.ContinuousCPInstruments.MatrixTraceComplete μ Φ)
    (child : Ω → Tree.{u} c d p b height)
    (hChild : ∀ x, MatrixMeasurableStateProtocol.MeasurableWellFormed (child x))
    (hMeas : AEStronglyMeasurable (fun x => channel (child x)) μ) :
    channel (aliceCPNode μ Φ child) =
      ∫ x, (channel (child x)).comp (aliceReferenceCLM (Φ x)) ∂μ := by
  change (∫ xq, (channel (child xq.1)).comp (leftSandwichCLM (refinedKraus Φ xq))
    ∂refinedMeasure (I := Fin a) (O := Fin p) μ) = _
  rw [refinedMeasure, integral_prod _
    (aliceRefinedMoment_integrable μ Φ hΦ hCP hTotal child hChild hMeas)]
  simp only [integral_count]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => (aliceMoment_eq_refined_sum Φ hCP child x).symm

theorem bobCPNode_channel (μ : Measure Ω) [IsFiniteMeasure μ]
    (Φ : Ω → LocalMap b p)
    (hΦ : QuantumProver.ElegantJointMeasurement.ContinuousCPInstruments.CoordinateMeasurable Φ)
    (hCP : ∀ x, CompletelyPositive (Φ x))
    (hTotal : QuantumProver.ElegantJointMeasurement.ContinuousCPInstruments.MatrixTraceComplete μ Φ)
    (child : Ω → Tree.{u} c d a p height)
    (hChild : ∀ x, MatrixMeasurableStateProtocol.MeasurableWellFormed (child x))
    (hMeas : AEStronglyMeasurable (fun x => channel (child x)) μ) :
    channel (bobCPNode μ Φ child) =
      ∫ x, (channel (child x)).comp (bobReferenceCLM (Φ x)) ∂μ := by
  change (∫ xq, (channel (child xq.1)).comp (rightSandwichCLM (refinedKraus Φ xq))
    ∂refinedMeasure (I := Fin b) (O := Fin p) μ) = _
  rw [refinedMeasure, integral_prod _
    (bobRefinedMoment_integrable μ Φ hΦ hCP hTotal child hChild hMeas)]
  simp only [integral_count]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => (bobMoment_eq_refined_sum Φ hCP child x).symm

theorem aliceCPNode_apply (μ : Measure Ω) [IsFiniteMeasure μ]
    (Φ : Ω → LocalMap a p)
    (hΦ : QuantumProver.ElegantJointMeasurement.ContinuousCPInstruments.CoordinateMeasurable Φ)
    (hCP : ∀ x, CompletelyPositive (Φ x))
    (hTotal : QuantumProver.ElegantJointMeasurement.ContinuousCPInstruments.MatrixTraceComplete μ Φ)
    (child : Ω → Tree.{u} c d p b height)
    (hChild : ∀ x, MatrixMeasurableStateProtocol.MeasurableWellFormed (child x))
    (hMeas : AEStronglyMeasurable (fun x => channel (child x)) μ) (ρ : JointMatrix a b) :
    channel (aliceCPNode μ Φ child) ρ =
      ∫ x, channel (child x) (aliceReferenceApply (Φ x) ρ) ∂μ := by
  rw [aliceCPNode_channel μ Φ hΦ hCP hTotal child hChild hMeas,
    ContinuousLinearMap.integral_apply (aliceMoment_integrable μ Φ hΦ hCP hTotal child hChild hMeas)]
  rfl

theorem bobCPNode_apply (μ : Measure Ω) [IsFiniteMeasure μ]
    (Φ : Ω → LocalMap b p)
    (hΦ : QuantumProver.ElegantJointMeasurement.ContinuousCPInstruments.CoordinateMeasurable Φ)
    (hCP : ∀ x, CompletelyPositive (Φ x))
    (hTotal : QuantumProver.ElegantJointMeasurement.ContinuousCPInstruments.MatrixTraceComplete μ Φ)
    (child : Ω → Tree.{u} c d a p height)
    (hChild : ∀ x, MatrixMeasurableStateProtocol.MeasurableWellFormed (child x))
    (hMeas : AEStronglyMeasurable (fun x => channel (child x)) μ) (ρ : JointMatrix a b) :
    channel (bobCPNode μ Φ child) ρ =
      ∫ x, channel (child x) (bobReferenceApply (Φ x) ρ) ∂μ := by
  rw [bobCPNode_channel μ Φ hΦ hCP hTotal child hChild hMeas,
    ContinuousLinearMap.integral_apply (bobMoment_integrable μ Φ hΦ hCP hTotal child hChild hMeas)]
  rfl

end QuantumProver.WernerEndpoint.ContinuousCPProtocol

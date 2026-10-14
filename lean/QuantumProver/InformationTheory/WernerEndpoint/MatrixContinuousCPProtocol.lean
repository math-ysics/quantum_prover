import QuantumProver.InformationTheory.WernerEndpoint.ContinuousCPProtocol

set_option autoImplicit false
set_option maxHeartbeats 1200000

noncomputable section

namespace QuantumProver.WernerEndpoint.MatrixContinuousCPProtocol

open MeasureTheory Filter OperationalEndpointCost
open MatrixCPProtocol (LocalMap FiniteCPProtocol)
open scoped BigOperators ComplexOrder MatrixOrder Matrix Kronecker
  Matrix.Norms.L2Operator Topology

universe u

abbrev JointMatrix (a b : ℕ) := Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ
abbrev Channel (c d a b : ℕ) := JointMatrix a b →L[ℂ] JointMatrix c d

def finiteCPChannel {c d a b : ℕ} (T : FiniteCPProtocol c d a b) : Channel c d a b :=
  ({ toFun := T.apply
     map_add' := by
       intro ρ σ
       simpa only [MatrixContinuousStateProtocol.finiteChannel_apply, T.represented_toMatrix_apply] using
         (MatrixContinuousStateProtocol.finiteChannel T.represented_toMatrix).map_add ρ σ
     map_smul' := by
       intro z ρ
       simpa only [MatrixContinuousStateProtocol.finiteChannel_apply, T.represented_toMatrix_apply,
         RingHom.id_apply] using
         (MatrixContinuousStateProtocol.finiteChannel T.represented_toMatrix).map_smul z ρ } :
      JointMatrix a b →ₗ[ℂ] JointMatrix c d).toContinuousLinearMap

@[simp] theorem finiteCPChannel_apply {c d a b : ℕ} (T : FiniteCPProtocol c d a b)
    (ρ : JointMatrix a b) : finiteCPChannel T ρ = T.apply ρ := rfl

theorem finiteCPChannel_eq_matrix {c d a b : ℕ} (T : FiniteCPProtocol c d a b) :
    finiteCPChannel T = MatrixContinuousStateProtocol.finiteChannel T.represented_toMatrix := by
  apply ContinuousLinearMap.ext
  intro ρ
  exact (T.represented_toMatrix_apply ρ).symm

inductive Tree (c d : ℕ) : (a b height : ℕ) → Type (u + 1) where
  | finite {a b : ℕ} (height : ℕ) (T : FiniteCPProtocol c d a b) : Tree c d a b height
  | alice {a b p height : ℕ} (Ω : Type u) (mΩ : MeasurableSpace Ω)
      (μ : @Measure Ω mΩ) (Φ : Ω → LocalMap a p)
      (child : Ω → Tree c d p b height) : Tree c d a b (height + 1)
  | bob {a b p height : ℕ} (Ω : Type u) (mΩ : MeasurableSpace Ω)
      (μ : @Measure Ω mΩ) (Φ : Ω → LocalMap b p)
      (child : Ω → Tree c d a p height) : Tree c d a b (height + 1)

def channel {c d : ℕ} : {a b height : ℕ} → Tree.{u} c d a b height → Channel c d a b
  | _, _, _, .finite _ T => finiteCPChannel T
  | _, _, _, .alice _ mΩ μ Φ child =>
      letI := mΩ
      ∫ x, (channel (child x)).comp (ContinuousCPProtocol.aliceReferenceCLM (Φ x)) ∂μ
  | _, _, _, .bob _ mΩ μ Φ child =>
      letI := mΩ
      ∫ x, (channel (child x)).comp (ContinuousCPProtocol.bobReferenceCLM (Φ x)) ∂μ

def Regular {c d : ℕ} : {a b height : ℕ} → Tree.{u} c d a b height → Prop
  | _, _, _, .finite _ _ => True
  | _, _, _, .alice _ mΩ μ Φ child =>
      letI := mΩ
      IsFiniteMeasure μ ∧ QuantumProver.ElegantJointMeasurement.ContinuousCPInstruments.CoordinateMeasurable Φ ∧
        (∀ x, QuantumProver.SuperchannelDiscrimination.CPTPKraus.CompletelyPositive (Φ x)) ∧
        QuantumProver.ElegantJointMeasurement.ContinuousCPInstruments.MatrixTraceComplete μ Φ ∧
        (∀ x, Regular (child x)) ∧ AEStronglyMeasurable (fun x => channel (child x)) μ
  | _, _, _, .bob _ mΩ μ Φ child =>
      letI := mΩ
      IsFiniteMeasure μ ∧ QuantumProver.ElegantJointMeasurement.ContinuousCPInstruments.CoordinateMeasurable Φ ∧
        (∀ x, QuantumProver.SuperchannelDiscrimination.CPTPKraus.CompletelyPositive (Φ x)) ∧
        QuantumProver.ElegantJointMeasurement.ContinuousCPInstruments.MatrixTraceComplete μ Φ ∧
        (∀ x, Regular (child x)) ∧ AEStronglyMeasurable (fun x => channel (child x)) μ

def IntegrableMoments {c d : ℕ} : {a b height : ℕ} → Tree.{u} c d a b height → Prop
  | _, _, _, .finite _ _ => True
  | _, _, _, .alice _ mΩ μ Φ child =>
      letI := mΩ
      Integrable (fun x => (channel (child x)).comp
        (ContinuousCPProtocol.aliceReferenceCLM (Φ x))) μ ∧
        ∀ x, IntegrableMoments (child x)
  | _, _, _, .bob _ mΩ μ Φ child =>
      letI := mΩ
      Integrable (fun x => (channel (child x)).comp
        (ContinuousCPProtocol.bobReferenceCLM (Φ x))) μ ∧
        ∀ x, IntegrableMoments (child x)

def represented_toMatrix {c d : ℕ} : {a b height : ℕ} → Tree.{u} c d a b height →
    MatrixContinuousStateProtocol.Tree.{u} c d a b height
  | _, _, _, .finite height T => .finite height T.represented_toMatrix
  | _, _, _, .alice _ mΩ μ Φ child =>
      letI := mΩ
      ContinuousCPProtocol.aliceCPNode μ Φ (fun x => represented_toMatrix (child x))
  | _, _, _, .bob _ mΩ μ Φ child =>
      letI := mΩ
      ContinuousCPProtocol.bobCPNode μ Φ (fun x => represented_toMatrix (child x))

@[simp] theorem regular_finite {c d a b : ℕ} (height : ℕ) (T : FiniteCPProtocol c d a b) :
    Regular (Tree.finite height T) := trivial

@[simp] theorem channel_finite {c d a b : ℕ} (height : ℕ) (T : FiniteCPProtocol c d a b) :
    channel (Tree.finite height T) = finiteCPChannel T := rfl

@[simp] theorem toMatrix_finite {c d a b : ℕ} (height : ℕ) (T : FiniteCPProtocol c d a b) :
    represented_toMatrix (Tree.finite height T) = .finite height T.represented_toMatrix := rfl

theorem toMatrix_spec {c d a b height : ℕ}
    (T : Tree.{u} c d a b height) (hT : Regular T) :
    MatrixMeasurableStateProtocol.MeasurableWellFormed (represented_toMatrix T) ∧
      MatrixContinuousStateProtocol.channel (represented_toMatrix T) = channel T ∧
      IntegrableMoments T := by
  classical
  revert hT
  induction T with
  | finite height U =>
      intro _
      exact ⟨trivial, (finiteCPChannel_eq_matrix U).symm, trivial⟩
  | @alice a b p height Ω mΩ μ Φ child ih =>
      let := mΩ
      intro hT
      rcases hT with ⟨hμ, hΦ, hCP, hTotal, hChild, hMeas⟩
      let := hμ
      have hIH := fun x => ih x (hChild x)
      have hMatrixMeas : AEStronglyMeasurable
          (fun x => MatrixContinuousStateProtocol.channel (represented_toMatrix (child x))) μ :=
        hMeas.congr (Filter.Eventually.of_forall (fun x => (hIH x).2.1.symm))
      have hMatrixRegular := ContinuousCPProtocol.aliceCPNode_measurableWellFormed
        μ Φ hΦ hCP hTotal (fun x => represented_toMatrix (child x))
        (fun x => (hIH x).1) hMatrixMeas
      have hPhysicalMoment : Integrable (fun x => (channel (child x)).comp
          (ContinuousCPProtocol.aliceReferenceCLM (Φ x))) μ := by
        have hMatrixMoment := ContinuousCPProtocol.aliceMoment_integrable
          μ Φ hΦ hCP hTotal (fun x => represented_toMatrix (child x))
          (fun x => (hIH x).1) hMatrixMeas
        apply hMatrixMoment.congr
        exact Filter.Eventually.of_forall (fun x => by
          dsimp only
          rw [(hIH x).2.1])
      refine ⟨hMatrixRegular, ?_, ⟨hPhysicalMoment, fun x => (hIH x).2.2⟩⟩
      change MatrixContinuousStateProtocol.channel
          (ContinuousCPProtocol.aliceCPNode μ Φ (fun x => represented_toMatrix (child x))) =
        ∫ x, (channel (child x)).comp (ContinuousCPProtocol.aliceReferenceCLM (Φ x)) ∂μ
      rw [ContinuousCPProtocol.aliceCPNode_channel μ Φ hΦ hCP hTotal
        (fun x => represented_toMatrix (child x)) (fun x => (hIH x).1) hMatrixMeas]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x => by
        dsimp only
        rw [(hIH x).2.1])
  | @bob a b p height Ω mΩ μ Φ child ih =>
      let := mΩ
      intro hT
      rcases hT with ⟨hμ, hΦ, hCP, hTotal, hChild, hMeas⟩
      let := hμ
      have hIH := fun x => ih x (hChild x)
      have hMatrixMeas : AEStronglyMeasurable
          (fun x => MatrixContinuousStateProtocol.channel (represented_toMatrix (child x))) μ :=
        hMeas.congr (Filter.Eventually.of_forall (fun x => (hIH x).2.1.symm))
      have hMatrixRegular := ContinuousCPProtocol.bobCPNode_measurableWellFormed
        μ Φ hΦ hCP hTotal (fun x => represented_toMatrix (child x))
        (fun x => (hIH x).1) hMatrixMeas
      have hPhysicalMoment : Integrable (fun x => (channel (child x)).comp
          (ContinuousCPProtocol.bobReferenceCLM (Φ x))) μ := by
        have hMatrixMoment := ContinuousCPProtocol.bobMoment_integrable
          μ Φ hΦ hCP hTotal (fun x => represented_toMatrix (child x))
          (fun x => (hIH x).1) hMatrixMeas
        apply hMatrixMoment.congr
        exact Filter.Eventually.of_forall (fun x => by
          dsimp only
          rw [(hIH x).2.1])
      refine ⟨hMatrixRegular, ?_, ⟨hPhysicalMoment, fun x => (hIH x).2.2⟩⟩
      change MatrixContinuousStateProtocol.channel
          (ContinuousCPProtocol.bobCPNode μ Φ (fun x => represented_toMatrix (child x))) =
        ∫ x, (channel (child x)).comp (ContinuousCPProtocol.bobReferenceCLM (Φ x)) ∂μ
      rw [ContinuousCPProtocol.bobCPNode_channel μ Φ hΦ hCP hTotal
        (fun x => represented_toMatrix (child x)) (fun x => (hIH x).1) hMatrixMeas]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x => by
        dsimp only
        rw [(hIH x).2.1])

theorem toMatrix_measurableWellFormed {c d a b height : ℕ}
    (T : Tree.{u} c d a b height) (hT : Regular T) :
    MatrixMeasurableStateProtocol.MeasurableWellFormed (represented_toMatrix T) := (toMatrix_spec T hT).1

theorem toMatrix_channel {c d a b height : ℕ}
    (T : Tree.{u} c d a b height) (hT : Regular T) :
    MatrixContinuousStateProtocol.channel (represented_toMatrix T) = channel T := (toMatrix_spec T hT).2.1

theorem integrableMoments_of_regular {c d a b height : ℕ}
    (T : Tree.{u} c d a b height) (hT : Regular T) : IntegrableMoments T :=
  (toMatrix_spec T hT).2.2

theorem represented_toMatrix_apply {c d a b height : ℕ}
    (T : Tree.{u} c d a b height) (hT : Regular T) (ρ : JointMatrix a b) :
    MatrixContinuousStateProtocol.channel (represented_toMatrix T) ρ = channel T ρ :=
  congrArg (fun L => L ρ) (toMatrix_channel T hT)

theorem exists_finiteProtocol_channel_approx {c d a b height : ℕ}
    (T : Tree.{u} c d a b height) (hT : Regular T) (epsilon : ℝ) (hEpsilon : 0 < epsilon) :
    ∃ U : FiniteLocalProtocol c d a b,
      ‖MatrixContinuousStateProtocol.finiteChannel U - channel T‖ < epsilon := by
  obtain ⟨U, hU⟩ := MatrixMeasurableStateProtocol.exists_finiteProtocol_channel_approx_of_measurable
    (represented_toMatrix T) (toMatrix_measurableWellFormed T hT) epsilon hEpsilon
  rw [toMatrix_channel T hT] at hU
  exact ⟨U, hU⟩

theorem exists_finiteProtocol_output_approx {c d a b height : ℕ}
    (T : Tree.{u} c d a b height) (hT : Regular T) (ρ : JointMatrix a b)
    (epsilon : ℝ) (hEpsilon : 0 < epsilon) :
    ∃ U : FiniteLocalProtocol c d a b, ‖U.apply ρ - channel T ρ‖ < epsilon := by
  obtain ⟨U, hU⟩ := MatrixMeasurableStateProtocol.exists_finiteProtocol_output_approx_of_measurable
    (represented_toMatrix T) (toMatrix_measurableWellFormed T hT) ρ epsilon hEpsilon
  rw [toMatrix_channel T hT] at hU
  exact ⟨U, hU⟩

theorem channel_pureOutput_mem_outputClosure {c d a b height : ℕ}
    (T : Tree.{u} c d a b height) (hT : Regular T) (ψ : Fin a × Fin b → ℂ) :
    channel T (pureDensity ψ) ∈ EndpointProtocolClosure.outputClosure ψ := by
  have h := MatrixMeasurableStateProtocol.channel_pureOutput_mem_outputClosure_of_measurable
    (represented_toMatrix T) (toMatrix_measurableWellFormed T hT) ψ
  rwa [toMatrix_channel T hT] at h

theorem channel_pureOutput_isDensity {c d a b height : ℕ}
    (T : Tree.{u} c d a b height) (hT : Regular T) (ψ : Fin a × Fin b → ℂ)
    (hψ : vectorNormSq ψ = 1) :
    (channel T (pureDensity ψ)).PosSemidef ∧ (channel T (pureDensity ψ)).trace = 1 := by
  have h := MatrixMeasurableStateProtocol.channel_pureOutput_isDensity_of_measurable
    (represented_toMatrix T) (toMatrix_measurableWellFormed T hT) ψ hψ
  rwa [toMatrix_channel T hT] at h

end QuantumProver.WernerEndpoint.MatrixContinuousCPProtocol

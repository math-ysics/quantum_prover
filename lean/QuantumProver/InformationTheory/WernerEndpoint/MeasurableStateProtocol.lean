import QuantumProver.InformationTheory.WernerEndpoint.ContinuousStateProtocol
import QuantumProver.InformationTheory.WernerEndpoint.ContinuousChannelIntegrability
import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 1200000

noncomputable section

namespace QuantumProver.WernerEndpoint.MatrixMeasurableStateProtocol

open OperationalEndpointCost MatrixContinuousStateProtocol MeasureTheory Filter
open scoped BigOperators ComplexOrder MatrixOrder Matrix Kronecker
  Matrix.Norms.L2Operator Topology

universe u

theorem integrable_gram_of_complete {Omega : Type*} [MeasurableSpace Omega]
    {a p : ℕ} (mu : Measure Omega) (K : Omega → Matrix (Fin p) (Fin a) ℂ)
    (hComplete : (∫ omega, (K omega).conjTranspose * K omega ∂mu) = 1) :
    Integrable (fun omega => (K omega).conjTranspose * K omega) mu := by
  classical
  by_cases hInput : Nonempty (Fin a)
  · let := hInput
    by_contra hNot
    have hZero := integral_undef hNot
    rw [hComplete] at hZero
    exact one_ne_zero hZero
  · let : IsEmpty (Fin a) := not_nonempty_iff.mp hInput
    have hZero : (fun omega => (K omega).conjTranspose * K omega) =
        (0 : Omega → Matrix (Fin a) (Fin a) ℂ) := by
      ext omega i j
      exact isEmptyElim i
    rw [hZero]
    exact integrable_zero Omega (Matrix (Fin a) (Fin a) ℂ) mu

theorem finiteChannel_norm_le_card {c d a b : ℕ} (T : FiniteLocalProtocol c d a b) :
    ‖finiteChannel T‖ ≤ (Fintype.card (Fin a × Fin b) : ℝ) := by
  apply ContinuousChannelIntegrability.norm_clm_le_card_of_complete_kraus
    (finiteChannel T) (FiniteLocalProtocol.leafKraus T) T.leafKraus_complete
  intro X
  simpa only [finiteChannel_apply,
    QuantumProver.SuperchannelDiscrimination.KrausCompletion.krausAction] using T.apply_eq_leafKraus X

theorem channel_norm_le_card {c d a b height : ℕ}
    (T : Tree.{u} c d a b height) (hT : WellFormed T) :
    ‖channel T‖ ≤ (Fintype.card (Fin a × Fin b) : ℝ) := by
  apply le_of_forall_pos_le_add
  intro epsilon hEpsilon
  obtain ⟨U, hU⟩ := exists_finiteProtocol_channel_approx T hT epsilon hEpsilon
  calc
    ‖channel T‖ = ‖finiteChannel U + (channel T - finiteChannel U)‖ := by
      congr 1
      abel
    _ ≤ ‖finiteChannel U‖ + ‖channel T - finiteChannel U‖ := norm_add_le _ _
    _ ≤ (Fintype.card (Fin a × Fin b) : ℝ) + epsilon :=
      add_le_add (finiteChannel_norm_le_card U)
        (le_of_lt (by simpa only [norm_sub_rev] using hU))

def MeasurableWellFormed {c d : ℕ} : {a b height : ℕ} → Tree.{u} c d a b height → Prop
  | _, _, _, .finite _ _ => True
  | _, _, _, .alice _ mOmega mu K child =>
      letI := mOmega
      IsFiniteMeasure mu ∧ Measurable K ∧
        (∫ omega, (K omega).conjTranspose * K omega ∂mu) = 1 ∧
        (∀ omega, MeasurableWellFormed (child omega)) ∧
        AEStronglyMeasurable (fun omega => channel (child omega)) mu
  | _, _, _, .bob _ mOmega mu K child =>
      letI := mOmega
      IsFiniteMeasure mu ∧ Measurable K ∧
        (∫ omega, (K omega).conjTranspose * K omega ∂mu) = 1 ∧
        (∀ omega, MeasurableWellFormed (child omega)) ∧
        AEStronglyMeasurable (fun omega => channel (child omega)) mu

@[simp] theorem measurableWellFormed_finite {c d a b : ℕ} (height : ℕ)
    (T : FiniteLocalProtocol c d a b) : MeasurableWellFormed (Tree.finite height T) := trivial

theorem measurableWellFormed_implies_wellFormed {c d a b height : ℕ}
    (T : Tree.{u} c d a b height) (hT : MeasurableWellFormed T) : WellFormed T := by
  classical
  revert hT
  induction T with
  | finite height U =>
      intro _
      exact wellFormed_finite height U
  | @alice a b p height Omega mOmega mu K child ih =>
      let := mOmega
      intro hT
      rcases hT with ⟨hMu, hK, hComplete, hChild, hMeas⟩
      let := hMu
      have hGram := integrable_gram_of_complete mu K hComplete
      have hChildWF : ∀ omega, WellFormed (child omega) :=
        fun omega => ih omega (hChild omega)
      have hBound : ∀ᵐ omega ∂mu, ‖channel (child omega)‖ ≤
          (Fintype.card (Fin p × Fin b) : ℝ) :=
        Filter.Eventually.of_forall (fun omega => channel_norm_le_card _ (hChildWF omega))
      have hMoment := ContinuousChannelIntegrability.integrable_left_channel_moment
        mu K (fun omega => channel (child omega)) hK hMeas hGram
        (Nat.cast_nonneg (Fintype.card (Fin p × Fin b))) hBound
      exact ⟨hMu, hK, hGram, hComplete, hChildWF, hMoment⟩
  | @bob a b p height Omega mOmega mu K child ih =>
      let := mOmega
      intro hT
      rcases hT with ⟨hMu, hK, hComplete, hChild, hMeas⟩
      let := hMu
      have hGram := integrable_gram_of_complete mu K hComplete
      have hChildWF : ∀ omega, WellFormed (child omega) :=
        fun omega => ih omega (hChild omega)
      have hBound : ∀ᵐ omega ∂mu, ‖channel (child omega)‖ ≤
          (Fintype.card (Fin a × Fin p) : ℝ) :=
        Filter.Eventually.of_forall (fun omega => channel_norm_le_card _ (hChildWF omega))
      have hMoment := ContinuousChannelIntegrability.integrable_right_channel_moment
        mu K (fun omega => channel (child omega)) hK hMeas hGram
        (Nat.cast_nonneg (Fintype.card (Fin a × Fin p))) hBound
      exact ⟨hMu, hK, hGram, hComplete, hChildWF, hMoment⟩

theorem exists_finiteProtocol_channel_approx_of_measurable {c d a b height : ℕ}
    (T : Tree.{u} c d a b height) (hT : MeasurableWellFormed T)
    (epsilon : ℝ) (hEpsilon : 0 < epsilon) :
    ∃ U : FiniteLocalProtocol c d a b, ‖finiteChannel U - channel T‖ < epsilon :=
  exists_finiteProtocol_channel_approx T
    (measurableWellFormed_implies_wellFormed T hT) epsilon hEpsilon

theorem exists_finiteProtocol_output_approx_of_measurable {c d a b height : ℕ}
    (T : Tree.{u} c d a b height) (hT : MeasurableWellFormed T)
    (rho : JointMatrix a b) (epsilon : ℝ) (hEpsilon : 0 < epsilon) :
    ∃ U : FiniteLocalProtocol c d a b, ‖U.apply rho - channel T rho‖ < epsilon :=
  exists_finiteProtocol_output_approx T
    (measurableWellFormed_implies_wellFormed T hT) rho epsilon hEpsilon

theorem channel_pureOutput_mem_outputClosure_of_measurable {c d a b height : ℕ}
    (T : Tree.{u} c d a b height) (hT : MeasurableWellFormed T)
    (psi : Fin a × Fin b → ℂ) :
    channel T (pureDensity psi) ∈ EndpointProtocolClosure.outputClosure psi :=
  channel_pureOutput_mem_outputClosure T (measurableWellFormed_implies_wellFormed T hT) psi

theorem channel_pureOutput_isDensity_of_measurable {c d a b height : ℕ}
    (T : Tree.{u} c d a b height) (hT : MeasurableWellFormed T)
    (psi : Fin a × Fin b → ℂ) (hPsi : vectorNormSq psi = 1) :
    (channel T (pureDensity psi)).PosSemidef ∧ (channel T (pureDensity psi)).trace = 1 :=
  channel_pureOutput_isDensity T (measurableWellFormed_implies_wellFormed T hT) psi hPsi

end QuantumProver.WernerEndpoint.MatrixMeasurableStateProtocol

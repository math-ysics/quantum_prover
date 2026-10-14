import QuantumProver.InformationTheory.WernerEndpoint.LocalChannelMoments
import QuantumProver.InformationTheory.WernerEndpoint.EndpointProtocolClosure
import QuantumProver.InformationTheory.WernerEndpoint.OperationalEndpointCost
import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 1200000

noncomputable section

namespace QuantumProver.WernerEndpoint.MatrixContinuousStateProtocol

open OperationalEndpointCost MeasureTheory Filter
open scoped BigOperators ComplexOrder MatrixOrder Matrix Kronecker
  Matrix.Norms.L2Operator Topology

abbrev JointMatrix (a b : ℕ) := Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ
abbrev Channel (c d a b : ℕ) := JointMatrix a b →L[ℂ] JointMatrix c d

def finiteChannel {c d a b : ℕ} (T : FiniteLocalProtocol c d a b) : Channel c d a b :=
  T.toLinearMap.toContinuousLinearMap

@[simp] theorem finiteChannel_apply {c d a b : ℕ}
    (T : FiniteLocalProtocol c d a b) (rho : JointMatrix a b) :
    finiteChannel T rho = T.apply rho := rfl

theorem exists_finite_child_replacement {c d a b p q h : ℕ}
    (D : Fin h → Channel p q a b) (Phi : Fin h → Channel c d p q)
    (hChild : ∀ i (eta : ℝ), 0 < eta →
      ∃ T : FiniteLocalProtocol c d p q, ‖finiteChannel T - Phi i‖ < eta)
    (epsilon : ℝ) (hEpsilon : 0 < epsilon) :
    ∃ T : Fin h → FiniteLocalProtocol c d p q,
      ‖(∑ i, (finiteChannel (T i)).comp (D i)) -
        (∑ i, (Phi i).comp (D i))‖ < epsilon := by
  classical
  let C : ℝ := ∑ i, ‖D i‖
  have hC : 0 ≤ C := Finset.sum_nonneg (fun i _ => norm_nonneg (D i))
  let eta : ℝ := epsilon / (C + 1)
  have hDen : 0 < C + 1 := by linarith
  have hEta : 0 < eta := div_pos hEpsilon hDen
  choose T hT using fun i : Fin h => hChild i eta hEta
  refine ⟨T, ?_⟩
  have hTerm (i : Fin h) :
      ‖(finiteChannel (T i) - Phi i).comp (D i)‖ ≤ eta * ‖D i‖ := by
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul_of_nonneg_right (le_of_lt (hT i)) (norm_nonneg _))
  have hDifference : (∑ i, (finiteChannel (T i)).comp (D i)) -
      (∑ i, (Phi i).comp (D i)) =
      ∑ i, (finiteChannel (T i) - Phi i).comp (D i) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    exact (ContinuousLinearMap.sub_comp _ _ _).symm
  rw [hDifference]
  calc
    ‖∑ i, (finiteChannel (T i) - Phi i).comp (D i)‖ ≤
        ∑ i, ‖(finiteChannel (T i) - Phi i).comp (D i)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i, eta * ‖D i‖ := Finset.sum_le_sum (fun i _ => hTerm i)
    _ = eta * C := by rw [← Finset.mul_sum]
    _ < eta * (C + 1) := mul_lt_mul_of_pos_left (by linarith) hEta
    _ = epsilon := by
      dsimp only [eta]
      exact div_mul_cancel₀ epsilon (ne_of_gt hDen)

universe u

inductive Tree (c d : ℕ) : (a b height : ℕ) → Type (u + 1) where
  | finite {a b : ℕ} (height : ℕ) (T : FiniteLocalProtocol c d a b) :
      Tree c d a b height
  | alice {a b p height : ℕ} (Omega : Type u) (mOmega : MeasurableSpace Omega)
      (mu : @Measure Omega mOmega) (K : Omega → Matrix (Fin p) (Fin a) ℂ)
      (child : Omega → Tree c d p b height) : Tree c d a b (height + 1)
  | bob {a b p height : ℕ} (Omega : Type u) (mOmega : MeasurableSpace Omega)
      (mu : @Measure Omega mOmega) (K : Omega → Matrix (Fin p) (Fin b) ℂ)
      (child : Omega → Tree c d a p height) : Tree c d a b (height + 1)

def channel {c d : ℕ} : {a b height : ℕ} → Tree.{u} c d a b height → Channel c d a b
  | _, _, _, .finite _ T => finiteChannel T
  | _, _, _, .alice _ mOmega mu K child =>
      letI := mOmega
      ∫ omega, (channel (child omega)).comp
        (LocalChannelMoments.leftSandwichCLM (K omega)) ∂mu
  | _, _, _, .bob _ mOmega mu K child =>
      letI := mOmega
      ∫ omega, (channel (child omega)).comp
        (LocalChannelMoments.rightSandwichCLM (K omega)) ∂mu

def WellFormed {c d : ℕ} : {a b height : ℕ} → Tree.{u} c d a b height → Prop
  | _, _, _, .finite _ _ => True
  | _, _, _, .alice _ mOmega mu K child =>
      letI := mOmega
      IsFiniteMeasure mu ∧ Measurable K ∧
        Integrable (fun omega => (K omega).conjTranspose * K omega) mu ∧
        (∫ omega, (K omega).conjTranspose * K omega ∂mu) = 1 ∧
        (∀ omega, WellFormed (child omega)) ∧
        Integrable (fun omega => (channel (child omega)).comp
          (LocalChannelMoments.leftSandwichCLM (K omega))) mu
  | _, _, _, .bob _ mOmega mu K child =>
      letI := mOmega
      IsFiniteMeasure mu ∧ Measurable K ∧
        Integrable (fun omega => (K omega).conjTranspose * K omega) mu ∧
        (∫ omega, (K omega).conjTranspose * K omega ∂mu) = 1 ∧
        (∀ omega, WellFormed (child omega)) ∧
        Integrable (fun omega => (channel (child omega)).comp
          (LocalChannelMoments.rightSandwichCLM (K omega))) mu

@[simp] theorem channel_finite {c d a b : ℕ} (height : ℕ)
    (T : FiniteLocalProtocol c d a b) : channel (Tree.finite height T) = finiteChannel T := rfl

@[simp] theorem wellFormed_finite {c d a b : ℕ} (height : ℕ)
    (T : FiniteLocalProtocol c d a b) : WellFormed (Tree.finite height T) := trivial

def finiteAliceNode {c d a b p h : ℕ}
    (K : Fin h → Matrix (Fin p) (Fin a) ℂ)
    (hK : ∑ i, (K i).conjTranspose * K i = 1)
    (child : Fin h → FiniteLocalProtocol c d p b) : FiniteLocalProtocol c d a b :=
  .alice (z := 1) (fun i _ => K i) (by simpa using hK) child

def finiteBobNode {c d a b p h : ℕ}
    (K : Fin h → Matrix (Fin p) (Fin b) ℂ)
    (hK : ∑ i, (K i).conjTranspose * K i = 1)
    (child : Fin h → FiniteLocalProtocol c d a p) : FiniteLocalProtocol c d a b :=
  .bob (z := 1) (fun i _ => K i) (by simpa using hK) child

theorem finiteAliceNode_channel {c d a b p h : ℕ}
    (K : Fin h → Matrix (Fin p) (Fin a) ℂ)
    (hK : ∑ i, (K i).conjTranspose * K i = 1)
    (child : Fin h → FiniteLocalProtocol c d p b) :
    finiteChannel (finiteAliceNode K hK child) =
      ∑ i, (finiteChannel (child i)).comp (LocalChannelMoments.leftSandwichCLM (K i)) := by
  ext rho : 1
  change (∑ i, (child i).apply (∑ _ : Fin 1,
      (K i ⊗ₖ (1 : Matrix (Fin b) (Fin b) ℂ)) * rho *
        (K i ⊗ₖ (1 : Matrix (Fin b) (Fin b) ℂ)).conjTranspose)) = _
  simp only [Fin.sum_univ_one, sum_apply,
    ContinuousLinearMap.comp_apply, finiteChannel_apply, LocalChannelMoments.leftSandwichCLM_apply]

theorem finiteBobNode_channel {c d a b p h : ℕ}
    (K : Fin h → Matrix (Fin p) (Fin b) ℂ)
    (hK : ∑ i, (K i).conjTranspose * K i = 1)
    (child : Fin h → FiniteLocalProtocol c d a p) :
    finiteChannel (finiteBobNode K hK child) =
      ∑ i, (finiteChannel (child i)).comp (LocalChannelMoments.rightSandwichCLM (K i)) := by
  ext rho : 1
  change (∑ i, (child i).apply (∑ _ : Fin 1,
      ((1 : Matrix (Fin a) (Fin a) ℂ) ⊗ₖ K i) * rho *
        ((1 : Matrix (Fin a) (Fin a) ℂ) ⊗ₖ K i).conjTranspose)) = _
  simp only [Fin.sum_univ_one, sum_apply,
    ContinuousLinearMap.comp_apply, finiteChannel_apply, LocalChannelMoments.rightSandwichCLM_apply]

theorem exists_output_approx_of_channel_approx {c d a b : ℕ} (Phi : Channel c d a b)
    (hApprox : ∀ eta : ℝ, 0 < eta → ∃ T : FiniteLocalProtocol c d a b,
      ‖finiteChannel T - Phi‖ < eta)
    (rho : JointMatrix a b) (epsilon : ℝ) (hEpsilon : 0 < epsilon) :
    ∃ T : FiniteLocalProtocol c d a b, ‖T.apply rho - Phi rho‖ < epsilon := by
  have hDen : 0 < ‖rho‖ + 1 := by positivity
  obtain ⟨T, hT⟩ := hApprox (epsilon / (‖rho‖ + 1)) (div_pos hEpsilon hDen)
  refine ⟨T, ?_⟩
  have hBound := ContinuousLinearMap.le_opNorm (finiteChannel T - Phi) rho
  change ‖T.apply rho - Phi rho‖ ≤ ‖finiteChannel T - Phi‖ * ‖rho‖ at hBound
  calc
    _ ≤ ‖finiteChannel T - Phi‖ * ‖rho‖ := hBound
    _ ≤ (epsilon / (‖rho‖ + 1)) * ‖rho‖ :=
      mul_le_mul_of_nonneg_right (le_of_lt hT) (norm_nonneg _)
    _ < (epsilon / (‖rho‖ + 1)) * (‖rho‖ + 1) :=
      mul_lt_mul_of_pos_left (by linarith) (div_pos hEpsilon hDen)
    _ = epsilon := div_mul_cancel₀ epsilon (ne_of_gt hDen)

theorem approximate_alice_with_finite_children {Omega : Type*} [MeasurableSpace Omega]
    {c d a b p : ℕ} (mu : Measure Omega) [IsFiniteMeasure mu]
    (K : Omega → Matrix (Fin p) (Fin a) ℂ) (Phi : Omega → Channel c d p b)
    (hGram : Integrable (fun omega => (K omega).conjTranspose * K omega) mu)
    (hMoment : Integrable (fun omega => (Phi omega).comp
      (LocalChannelMoments.leftSandwichCLM (K omega))) mu)
    (hComplete : (∫ omega, (K omega).conjTranspose * K omega ∂mu) = 1)
    (hChild : ∀ omega (eta : ℝ), 0 < eta →
      ∃ T : FiniteLocalProtocol c d p b, ‖finiteChannel T - Phi omega‖ < eta)
    (epsilon : ℝ) (hEpsilon : 0 < epsilon) :
    ∃ T : FiniteLocalProtocol c d a b,
      ‖finiteChannel T - (∫ omega, (Phi omega).comp
        (LocalChannelMoments.leftSandwichCLM (K omega)) ∂mu)‖ < epsilon := by
  classical
  obtain ⟨samples, Ks, point, hKs, _, hLimit⟩ :=
    LocalChannelMoments.exists_normalized_left_channel_quadrature_on
      mu K Phi hGram hMoment hComplete Set.univ
      (Filter.Eventually.of_forall (fun _ => Set.mem_univ _))
  have hClose := Metric.tendsto_nhds.mp hLimit (epsilon / 2) (half_pos hEpsilon)
  obtain ⟨k, hk⟩ := hClose.exists
  rw [dist_eq_norm] at hk
  obtain ⟨child, hChildError⟩ := exists_finite_child_replacement
    (fun i : Fin (samples k) => LocalChannelMoments.leftSandwichCLM (Ks k i))
    (fun i => Phi (point k i)) (fun i eta hEta => hChild (point k i) eta hEta)
    (epsilon / 2) (half_pos hEpsilon)
  refine ⟨finiteAliceNode (Ks k) (hKs k) child, ?_⟩
  rw [finiteAliceNode_channel]
  calc
    _ ≤ ‖(∑ i, (finiteChannel (child i)).comp
          (LocalChannelMoments.leftSandwichCLM (Ks k i))) -
        (∑ i, (Phi (point k i)).comp (LocalChannelMoments.leftSandwichCLM (Ks k i)))‖ +
      ‖(∑ i, (Phi (point k i)).comp (LocalChannelMoments.leftSandwichCLM (Ks k i))) -
        (∫ omega, (Phi omega).comp (LocalChannelMoments.leftSandwichCLM (K omega)) ∂mu)‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ < epsilon / 2 + epsilon / 2 := add_lt_add hChildError hk
    _ = epsilon := by ring

theorem approximate_bob_with_finite_children {Omega : Type*} [MeasurableSpace Omega]
    {c d a b p : ℕ} (mu : Measure Omega) [IsFiniteMeasure mu]
    (K : Omega → Matrix (Fin p) (Fin b) ℂ) (Phi : Omega → Channel c d a p)
    (hGram : Integrable (fun omega => (K omega).conjTranspose * K omega) mu)
    (hMoment : Integrable (fun omega => (Phi omega).comp
      (LocalChannelMoments.rightSandwichCLM (K omega))) mu)
    (hComplete : (∫ omega, (K omega).conjTranspose * K omega ∂mu) = 1)
    (hChild : ∀ omega (eta : ℝ), 0 < eta →
      ∃ T : FiniteLocalProtocol c d a p, ‖finiteChannel T - Phi omega‖ < eta)
    (epsilon : ℝ) (hEpsilon : 0 < epsilon) :
    ∃ T : FiniteLocalProtocol c d a b,
      ‖finiteChannel T - (∫ omega, (Phi omega).comp
        (LocalChannelMoments.rightSandwichCLM (K omega)) ∂mu)‖ < epsilon := by
  classical
  obtain ⟨samples, Ks, point, hKs, _, hLimit⟩ :=
    LocalChannelMoments.exists_normalized_right_channel_quadrature_on
      mu K Phi hGram hMoment hComplete Set.univ
      (Filter.Eventually.of_forall (fun _ => Set.mem_univ _))
  have hClose := Metric.tendsto_nhds.mp hLimit (epsilon / 2) (half_pos hEpsilon)
  obtain ⟨k, hk⟩ := hClose.exists
  rw [dist_eq_norm] at hk
  obtain ⟨child, hChildError⟩ := exists_finite_child_replacement
    (fun i : Fin (samples k) => LocalChannelMoments.rightSandwichCLM (Ks k i))
    (fun i => Phi (point k i)) (fun i eta hEta => hChild (point k i) eta hEta)
    (epsilon / 2) (half_pos hEpsilon)
  refine ⟨finiteBobNode (Ks k) (hKs k) child, ?_⟩
  rw [finiteBobNode_channel]
  calc
    _ ≤ ‖(∑ i, (finiteChannel (child i)).comp
          (LocalChannelMoments.rightSandwichCLM (Ks k i))) -
        (∑ i, (Phi (point k i)).comp (LocalChannelMoments.rightSandwichCLM (Ks k i)))‖ +
      ‖(∑ i, (Phi (point k i)).comp (LocalChannelMoments.rightSandwichCLM (Ks k i))) -
        (∫ omega, (Phi omega).comp (LocalChannelMoments.rightSandwichCLM (K omega)) ∂mu)‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ < epsilon / 2 + epsilon / 2 := add_lt_add hChildError hk
    _ = epsilon := by ring

theorem exists_finiteProtocol_channel_approx {c d a b height : ℕ}
    (T : Tree.{u} c d a b height) (hT : WellFormed T)
    (epsilon : ℝ) (hEpsilon : 0 < epsilon) :
    ∃ U : FiniteLocalProtocol c d a b, ‖finiteChannel U - channel T‖ < epsilon := by
  classical
  revert hT epsilon
  induction T with
  | finite height U =>
      intro _ epsilon hEpsilon
      exact ⟨U, by simpa only [channel_finite, sub_self, norm_zero] using hEpsilon⟩
  | @alice a b p height Omega mOmega mu K child ih =>
      let := mOmega
      intro hT epsilon hEpsilon
      rcases hT with ⟨hMu, _, hGram, hComplete, hChild, hMoment⟩
      let := hMu
      exact approximate_alice_with_finite_children mu K (fun omega => channel (child omega))
        hGram hMoment hComplete (fun omega eta hEta => ih omega (hChild omega) eta hEta)
        epsilon hEpsilon
  | @bob a b p height Omega mOmega mu K child ih =>
      let := mOmega
      intro hT epsilon hEpsilon
      rcases hT with ⟨hMu, _, hGram, hComplete, hChild, hMoment⟩
      let := hMu
      exact approximate_bob_with_finite_children mu K (fun omega => channel (child omega))
        hGram hMoment hComplete (fun omega eta hEta => ih omega (hChild omega) eta hEta)
        epsilon hEpsilon

theorem exists_finiteProtocol_output_approx {c d a b height : ℕ}
    (T : Tree.{u} c d a b height) (hT : WellFormed T)
    (rho : JointMatrix a b) (epsilon : ℝ) (hEpsilon : 0 < epsilon) :
    ∃ U : FiniteLocalProtocol c d a b, ‖U.apply rho - channel T rho‖ < epsilon :=
  exists_output_approx_of_channel_approx (channel T)
    (fun eta hEta => exists_finiteProtocol_channel_approx T hT eta hEta)
    rho epsilon hEpsilon

theorem channel_pureOutput_mem_outputClosure {c d a b height : ℕ}
    (T : Tree.{u} c d a b height) (hT : WellFormed T) (psi : Fin a × Fin b → ℂ) :
    channel T (pureDensity psi) ∈ EndpointProtocolClosure.outputClosure psi := by
  apply Metric.mem_closure_iff.mpr
  intro epsilon hEpsilon
  obtain ⟨U, hU⟩ := exists_finiteProtocol_output_approx T hT
    (pureDensity psi) epsilon hEpsilon
  refine ⟨U.apply (pureDensity psi), ⟨U, rfl⟩, ?_⟩
  simpa only [dist_eq_norm, norm_sub_rev] using hU

theorem channel_pureOutput_isDensity {c d a b height : ℕ}
    (T : Tree.{u} c d a b height) (hT : WellFormed T)
    (psi : Fin a × Fin b → ℂ) (hPsi : vectorNormSq psi = 1) :
    (channel T (pureDensity psi)).PosSemidef ∧
      (channel T (pureDensity psi)).trace = 1 :=
  EndpointProtocolClosure.outputClosure_isDensity psi hPsi
    (channel_pureOutput_mem_outputClosure T hT psi)

end QuantumProver.WernerEndpoint.MatrixContinuousStateProtocol

import QuantumProver.InformationTheory.WernerEndpoint.VariableFiniteBaseProtocol
import QuantumProver.InformationTheory.WernerEndpoint.ContinuousCPProtocol
import QuantumProver.InformationTheory.WernerEndpoint.StackedTraceout

set_option autoImplicit false
set_option maxHeartbeats 2000000

noncomputable section

namespace QuantumProver.WernerEndpoint.MatrixVariableCPDensityProtocol

open OperationalEndpointCost MeasureTheory Filter Matrix
open QuantumProver.SuperchannelDiscrimination
open scoped BigOperators ComplexOrder MatrixOrder Matrix Kronecker
  Matrix.Norms.L2Operator Topology

universe u

abbrev LocalMap (a p : ℕ) := Matrix (Fin a) (Fin a) ℂ →L[ℂ] Matrix (Fin p) (Fin p) ℂ
abbrev Channel (c d a b : ℕ) := MatrixVariableStateProtocol.Channel c d a b
abbrev Hidden (a p : ℕ) := Fin a × Fin p
abbrev StackedRows (a p : ℕ) := Fin p × Hidden a p
def stackedDimension (a p : ℕ) : ℕ := Fintype.card (StackedRows a p)
def stackedEquiv (a p : ℕ) : Fin (stackedDimension a p) ≃ StackedRows a p :=
  (Fintype.equivFin (StackedRows a p)).symm

def canonicalKraus {a p : ℕ} (Φ : LocalMap a p) (h : Hidden a p) :
    Matrix (Fin p) (Fin a) ℂ := CPTPKraus.canonicalKraus Φ.toLinearMap h

def stackedKraus {a p : ℕ} (Φ : LocalMap a p) :
    Matrix (Fin (stackedDimension a p)) (Fin a) ℂ :=
  fun r i => canonicalKraus Φ ((stackedEquiv a p r).2) ((stackedEquiv a p r).1) i

abbrev AliceFiber (c d a b p : ℕ) := LocalMap a p × Channel c d p b
abbrev BobFiber (c d a b p : ℕ) := LocalMap b p × Channel c d a p

inductive Tree (c d : ℕ) : (a b height : ℕ) → Type (u + 1) where
  | finite {a b : ℕ} (height : ℕ) (T : MatrixCPProtocol.FiniteCPProtocol c d a b) :
      Tree c d a b height
  | alice {a b height : ℕ} (Ω : Type u) (mΩ : MeasurableSpace Ω)
      (μ : @Measure Ω mΩ) (p : Ω → ℕ) (Φ : ∀ x, LocalMap a (p x))
      (child : ∀ x, Tree c d (p x) b height) : Tree c d a b (height + 1)
  | bob {a b height : ℕ} (Ω : Type u) (mΩ : MeasurableSpace Ω)
      (μ : @Measure Ω mΩ) (p : Ω → ℕ) (Φ : ∀ x, LocalMap b (p x))
      (child : ∀ x, Tree c d a (p x) height) : Tree c d a b (height + 1)

def channel {c d : ℕ} : {a b height : ℕ} → Tree.{u} c d a b height → Channel c d a b
  | _, _, _, .finite _ T => MatrixContinuousCPProtocol.finiteCPChannel T
  | _, _, _, .alice _ mΩ μ _ Φ child =>
      letI := mΩ
      ∫ x, (channel (child x)).comp (ContinuousCPProtocol.aliceReferenceCLM (Φ x).toLinearMap) ∂μ
  | _, _, _, .bob _ mΩ μ _ Φ child =>
      letI := mΩ
      ∫ x, (channel (child x)).comp (ContinuousCPProtocol.bobReferenceCLM (Φ x).toLinearMap) ∂μ

def Regular {c d : ℕ} : {a b height : ℕ} → Tree.{u} c d a b height → Prop
  | _, _, _, .finite _ _ => True
  | a, b, _, .alice _ mΩ μ p Φ child =>
      letI := mΩ
      Measurable (fun x => (⟨p x, (Φ x, channel (child x))⟩ : Sigma (AliceFiber c d a b))) ∧
        (∀ x, CPTPKraus.CompletelyPositive (Φ x).toLinearMap) ∧
        (∀ X, (∫ x, (Φ x X).trace ∂μ) = X.trace) ∧ ∀ x, Regular (child x)
  | a, b, _, .bob _ mΩ μ p Φ child =>
      letI := mΩ
      Measurable (fun x => (⟨p x, (Φ x, channel (child x))⟩ : Sigma (BobFiber c d a b))) ∧
        (∀ x, CPTPKraus.CompletelyPositive (Φ x).toLinearMap) ∧
        (∀ X, (∫ x, (Φ x X).trace ∂μ) = X.trace) ∧ ∀ x, Regular (child x)

theorem stackedKraus_gram {a p : ℕ} (Φ : LocalMap a p) :
    (stackedKraus Φ).conjTranspose * stackedKraus Φ =
      ∑ h : Hidden a p, (canonicalKraus Φ h).conjTranspose * canonicalKraus Φ h := by
  classical
  ext i j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.sum_apply, stackedKraus]
  rw [(stackedEquiv a p).sum_comp (fun r : StackedRows a p =>
    star (canonicalKraus Φ r.2 r.1 i) * canonicalKraus Φ r.2 r.1 j)]
  rw [Fintype.sum_prod_type]
  exact Finset.sum_comm

theorem matrix_trace_eq_stackedGram {a p : ℕ} (Φ : LocalMap a p)
    (hCP : CPTPKraus.CompletelyPositive Φ.toLinearMap) (X : Matrix (Fin a) (Fin a) ℂ) :
    (Φ X).trace = ((stackedKraus Φ).conjTranspose * stackedKraus Φ * X).trace := by
  rw [stackedKraus_gram]
  exact QuantumProver.ElegantJointMeasurement.ContinuousCPInstruments.matrix_trace_eq_canonicalGram
    (fun _ : Unit => Φ.toLinearMap)
    (fun _ => CPTPKraus.completelyPositive_to_EJMCP hCP) () X

theorem stackedGram_trace {a p : ℕ} (Φ : LocalMap a p)
    (hCP : CPTPKraus.CompletelyPositive Φ.toLinearMap) :
    ((stackedKraus Φ).conjTranspose * stackedKraus Φ).trace = (Φ 1).trace := by
  simpa only [Matrix.mul_one] using (matrix_trace_eq_stackedGram Φ hCP 1).symm

private theorem measurable_fiberElim {D : Type*} (F : D → Type*)
    [∀ d, MeasurableSpace (F d)] {E : Type*} [MeasurableSpace E]
    (f : Sigma F → E) (hf : ∀ d, Measurable (fun x : F d => f ⟨d, x⟩)) :
    Measurable f := by
  intro s hs
  change MeasurableSet[⨅ d, (inferInstance : MeasurableSpace (F d)).map (Sigma.mk d)]
    (f ⁻¹' s)
  rw [MeasurableSpace.measurableSet_iInf]
  intro d
  exact hf d hs

private theorem measurable_fiberMk {D : Type*} (F : D → Type*)
    [∀ d, MeasurableSpace (F d)] (d : D) : Measurable (Sigma.mk d : F d → Sigma F) := by
  intro s hs
  change MeasurableSet[⨅ e, (inferInstance : MeasurableSpace (F e)).map (Sigma.mk e)] s at hs
  rw [MeasurableSpace.measurableSet_iInf] at hs
  exact hs d

theorem measurable_stackedKraus (a p : ℕ) :
    Measurable (stackedKraus : LocalMap a p → Matrix (Fin (stackedDimension a p)) (Fin a) ℂ) := by
  have hCoord : QuantumProver.ElegantJointMeasurement.ContinuousCPInstruments.CoordinateMeasurable
      (fun Φ : LocalMap a p => Φ.toLinearMap) := by
    intro i j o r
    change Measurable (fun Φ : LocalMap a p => Φ (Matrix.single i j 1) o r)
    fun_prop
  refine Measurable.of_eval fun r => Measurable.of_eval fun i => ?_
  exact (measurable_pi_apply i).comp
    ((measurable_pi_apply ((stackedEquiv a p r).1)).comp
      (QuantumProver.ElegantJointMeasurement.ContinuousCPInstruments.measurable_canonicalKraus
        (fun Φ : LocalMap a p => Φ.toLinearMap) hCoord ((stackedEquiv a p r).2)))

theorem measurable_packedStackedGram (a : ℕ) (G : ℕ → Type*)
    [∀ p, MeasurableSpace (G p)] :
    Measurable (fun z : Sigma (fun p => LocalMap a p × G p) =>
      (stackedKraus z.2.1).conjTranspose * stackedKraus z.2.1) := by
  apply measurable_fiberElim
  intro p
  have hK : Measurable (fun z : LocalMap a p × G p => stackedKraus z.1) :=
    (measurable_stackedKraus a p).comp measurable_fst
  have hGram : Continuous (fun K : Matrix (Fin (stackedDimension a p)) (Fin a) ℂ => Kᴴ * K) := by
    fun_prop
  exact hGram.measurable.comp hK

section Aggregate

variable {Ω : Type*} [MeasurableSpace Ω] {a : ℕ}

theorem integrable_stackedGram (μ : Measure Ω) (p : Ω → ℕ)
    (Φ : ∀ x, LocalMap a (p x))
    (hGram : Measurable (fun x => (stackedKraus (Φ x)).conjTranspose * stackedKraus (Φ x)))
    (hCP : ∀ x, CPTPKraus.CompletelyPositive (Φ x).toLinearMap)
    (hTotal : ∀ X, (∫ x, (Φ x X).trace ∂μ) = X.trace) :
    Integrable (fun x => (stackedKraus (Φ x)).conjTranspose * stackedKraus (Φ x)) μ := by
  classical
  by_cases hInput : Nonempty (Fin a)
  · let := hInput
    have hTrace : Integrable (fun x => (Φ x 1).trace) μ := by
      by_contra h
      have ht := hTotal 1
      rw [integral_undef h] at ht
      have ha : 0 < a := by
        simpa only [Fintype.card_fin] using (Fintype.card_pos_iff.mpr hInput)
      have hn : (1 : Matrix (Fin a) (Fin a) ℂ).trace ≠ 0 := by simp [ne_of_gt ha]
      exact hn ht.symm
    have hm : Integrable (fun x => (Φ x 1).trace.re) μ := by
      simpa only [Complex.reCLM_apply] using Complex.reCLM.integrable_comp hTrace
    apply hm.mono' hGram.stronglyMeasurable.aestronglyMeasurable
    exact Eventually.of_forall fun x => by
      simpa only [stackedGram_trace (Φ x) (hCP x)] using
        QuantumProver.ElegantJointMeasurement.ContinuousCPInstruments.posSemidef_norm_le_trace _
          (Matrix.posSemidef_conjTranspose_mul_self (stackedKraus (Φ x)))
  · let : IsEmpty (Fin a) := not_nonempty_iff.mp hInput
    have hz : (fun x => (stackedKraus (Φ x)).conjTranspose * stackedKraus (Φ x)) =
        (0 : Ω → Matrix (Fin a) (Fin a) ℂ) := by
      ext x i j
      exact isEmptyElim i
    rw [hz]
    exact integrable_zero Ω (Matrix (Fin a) (Fin a) ℂ) μ

private def tracePairing (X : Matrix (Fin a) (Fin a) ℂ) :
    Matrix (Fin a) (Fin a) ℂ →L[ℂ] ℂ :=
  ({ toFun := fun G => (G * X).trace
     map_add' := by intro A B; simp [Matrix.add_mul, Matrix.trace_add]
     map_smul' := by intro z A; simp [Matrix.trace_smul] } :
    Matrix (Fin a) (Fin a) ℂ →ₗ[ℂ] ℂ).toContinuousLinearMap

theorem integral_stackedGram_eq_one (μ : Measure Ω) (p : Ω → ℕ)
    (Φ : ∀ x, LocalMap a (p x))
    (hGram : Measurable (fun x => (stackedKraus (Φ x)).conjTranspose * stackedKraus (Φ x)))
    (hCP : ∀ x, CPTPKraus.CompletelyPositive (Φ x).toLinearMap)
    (hTotal : ∀ X, (∫ x, (Φ x X).trace ∂μ) = X.trace) :
    (∫ x, (stackedKraus (Φ x)).conjTranspose * stackedKraus (Φ x) ∂μ) = 1 := by
  apply Matrix.ext_iff_trace_mul_right.mpr
  intro X
  have hcomm := (tracePairing X).integral_comp_comm (integrable_stackedGram μ p Φ hGram hCP hTotal)
  change (∫ x, ((stackedKraus (Φ x)).conjTranspose * stackedKraus (Φ x) * X).trace ∂μ) =
    ((∫ x, (stackedKraus (Φ x)).conjTranspose * stackedKraus (Φ x) ∂μ) * X).trace at hcomm
  have heq : (∫ x, ((stackedKraus (Φ x)).conjTranspose * stackedKraus (Φ x) * X).trace ∂μ) =
      (∫ x, (Φ x X).trace ∂μ) :=
    integral_congr_ae (Eventually.of_forall fun x => (matrix_trace_eq_stackedGram (Φ x) (hCP x) X).symm)
  simpa only [Matrix.one_mul] using hcomm.symm.trans (heq.trans (hTotal X))

end Aggregate

def discardKraus (a p : ℕ) (h : Hidden a p) :
    Matrix (Fin p) (Fin (stackedDimension a p)) ℂ :=
  MatrixStackedTraceout.selector (stackedEquiv a p) h

def aliceDiscardCLM (a p b : ℕ) : Channel p b (stackedDimension a p) b :=
  ∑ h : Hidden a p, LocalChannelMoments.leftSandwichCLM (discardKraus a p h)

def bobDiscardCLM (a b p : ℕ) : Channel a p a (stackedDimension b p) :=
  ∑ h : Hidden b p, LocalChannelMoments.rightSandwichCLM (discardKraus b p h)

private def hiddenLiftEquiv (a p : ℕ) : ULift.{u} (Hidden a p) ≃ Hidden a p where
  toFun := ULift.down
  invFun := ULift.up
  left_inv := by intro h; cases h; rfl
  right_inv := by intro h; rfl

def aliceDiscardChild {c d a b p height : ℕ}
    (child : MatrixVariableStateProtocol.Tree.{u} c d p b height) :
    MatrixVariableStateProtocol.Tree.{u} c d (stackedDimension a p) b (height + 1) :=
  MatrixVariableStateProtocol.Tree.alice (ULift.{u} (Hidden a p)) inferInstance Measure.count
    (fun _ => p) (fun h => discardKraus a p h.down) (fun _ => child)

def bobDiscardChild {c d a b p height : ℕ}
    (child : MatrixVariableStateProtocol.Tree.{u} c d a p height) :
    MatrixVariableStateProtocol.Tree.{u} c d a (stackedDimension b p) (height + 1) :=
  MatrixVariableStateProtocol.Tree.bob (ULift.{u} (Hidden b p)) inferInstance Measure.count
    (fun _ => p) (fun h => discardKraus b p h.down) (fun _ => child)

theorem aliceDiscardChild_generalRegular {c d a b p height : ℕ}
    (child : MatrixVariableStateProtocol.Tree.{u} c d p b height)
    (hChild : MatrixVariableFiniteBaseProtocol.GeneralRegular child) :
    MatrixVariableFiniteBaseProtocol.GeneralRegular (aliceDiscardChild (a := a) child) := by
  classical
  refine ⟨measurable_of_finite _, ?_, fun _ => hChild⟩
  change (∫ h : ULift.{u} (Hidden a p), (discardKraus a p h.down).conjTranspose *
    discardKraus a p h.down ∂Measure.count) = 1
  rw [integral_count]
  have hsum := (hiddenLiftEquiv.{u} a p).sum_comp (fun h : Hidden a p =>
    (discardKraus a p h).conjTranspose * discardKraus a p h)
  simp only [hiddenLiftEquiv, Equiv.coe_fn_mk] at hsum
  rw [hsum]
  exact MatrixStackedTraceout.selector_complete (stackedEquiv a p)

theorem bobDiscardChild_generalRegular {c d a b p height : ℕ}
    (child : MatrixVariableStateProtocol.Tree.{u} c d a p height)
    (hChild : MatrixVariableFiniteBaseProtocol.GeneralRegular child) :
    MatrixVariableFiniteBaseProtocol.GeneralRegular (bobDiscardChild (b := b) child) := by
  classical
  refine ⟨measurable_of_finite _, ?_, fun _ => hChild⟩
  change (∫ h : ULift.{u} (Hidden b p), (discardKraus b p h.down).conjTranspose *
    discardKraus b p h.down ∂Measure.count) = 1
  rw [integral_count]
  have hsum := (hiddenLiftEquiv.{u} b p).sum_comp (fun h : Hidden b p =>
    (discardKraus b p h).conjTranspose * discardKraus b p h)
  simp only [hiddenLiftEquiv, Equiv.coe_fn_mk] at hsum
  rw [hsum]
  exact MatrixStackedTraceout.selector_complete (stackedEquiv b p)

theorem aliceDiscardChild_channel {c d a b p height : ℕ}
    (child : MatrixVariableStateProtocol.Tree.{u} c d p b height) :
    MatrixVariableStateProtocol.channel (aliceDiscardChild (a := a) child) =
      (MatrixVariableStateProtocol.channel child).comp (aliceDiscardCLM a p b) := by
  classical
  change (∫ h : ULift.{u} (Hidden a p), (MatrixVariableStateProtocol.channel child).comp
    (LocalChannelMoments.leftSandwichCLM (discardKraus a p h.down)) ∂Measure.count) = _
  rw [integral_count]
  have hsum := (hiddenLiftEquiv.{u} a p).sum_comp (fun h : Hidden a p =>
    (MatrixVariableStateProtocol.channel child).comp
      (LocalChannelMoments.leftSandwichCLM (discardKraus a p h)))
  simp only [hiddenLiftEquiv, Equiv.coe_fn_mk] at hsum
  rw [hsum]
  apply ContinuousLinearMap.ext
  intro ρ
  simp only [aliceDiscardCLM, ContinuousLinearMap.comp_apply, _root_.sum_apply, map_sum]

theorem bobDiscardChild_channel {c d a b p height : ℕ}
    (child : MatrixVariableStateProtocol.Tree.{u} c d a p height) :
    MatrixVariableStateProtocol.channel (bobDiscardChild (b := b) child) =
      (MatrixVariableStateProtocol.channel child).comp (bobDiscardCLM a b p) := by
  classical
  change (∫ h : ULift.{u} (Hidden b p), (MatrixVariableStateProtocol.channel child).comp
    (LocalChannelMoments.rightSandwichCLM (discardKraus b p h.down)) ∂Measure.count) = _
  rw [integral_count]
  have hsum := (hiddenLiftEquiv.{u} b p).sum_comp (fun h : Hidden b p =>
    (MatrixVariableStateProtocol.channel child).comp
      (LocalChannelMoments.rightSandwichCLM (discardKraus b p h)))
  simp only [hiddenLiftEquiv, Equiv.coe_fn_mk] at hsum
  rw [hsum]
  apply ContinuousLinearMap.ext
  intro ρ
  simp only [bobDiscardCLM, ContinuousLinearMap.comp_apply, _root_.sum_apply, map_sum]

private theorem helper_leftSandwich_eq {a b p : ℕ} (K : Matrix (Fin p) (Fin a) ℂ) :
    MatrixStackedTraceout.leftSandwichCLM (Fin b) K = LocalChannelMoments.leftSandwichCLM K := by
  apply ContinuousLinearMap.ext
  intro ρ
  simp only [MatrixStackedTraceout.leftSandwichCLM, MatrixStackedTraceout.sandwichCLM_apply,
    LocalChannelMoments.leftSandwichCLM_apply]

private theorem helper_rightSandwich_eq {a b p : ℕ} (K : Matrix (Fin p) (Fin b) ℂ) :
    MatrixStackedTraceout.rightSandwichCLM (Fin a) K = LocalChannelMoments.rightSandwichCLM K := by
  apply ContinuousLinearMap.ext
  intro ρ
  simp only [MatrixStackedTraceout.rightSandwichCLM, MatrixStackedTraceout.sandwichCLM_apply,
    LocalChannelMoments.rightSandwichCLM_apply]

theorem aliceDiscardCLM_eq_finiteChannel (a p b : ℕ) :
    aliceDiscardCLM a p b = MatrixContinuousStateProtocol.finiteChannel
      (MatrixStackedTraceout.aliceTraceout (stackedEquiv a p) b) := by
  apply ContinuousLinearMap.ext
  intro ρ
  have h := MatrixStackedTraceout.aliceTraceout_apply (stackedEquiv a p) b ρ
  simpa only [aliceDiscardCLM, discardKraus, _root_.sum_apply, helper_leftSandwich_eq,
    MatrixContinuousStateProtocol.finiteChannel_apply] using h.symm

theorem bobDiscardCLM_eq_finiteChannel (a b p : ℕ) :
    bobDiscardCLM a b p = MatrixContinuousStateProtocol.finiteChannel
      (MatrixStackedTraceout.bobTraceout (stackedEquiv b p) a) := by
  apply ContinuousLinearMap.ext
  intro ρ
  have h := MatrixStackedTraceout.bobTraceout_apply (stackedEquiv b p) a ρ
  simpa only [bobDiscardCLM, discardKraus, _root_.sum_apply, helper_rightSandwich_eq,
    MatrixContinuousStateProtocol.finiteChannel_apply] using h.symm

theorem aliceDiscard_stack {a b p : ℕ} (Φ : LocalMap a p)
    (hCP : CPTPKraus.CompletelyPositive Φ.toLinearMap) :
    (aliceDiscardCLM a p b).comp (LocalChannelMoments.leftSandwichCLM (stackedKraus Φ)) =
      ContinuousCPProtocol.aliceReferenceCLM Φ.toLinearMap := by
  classical
  calc
    _ = ∑ h : Hidden a p, LocalChannelMoments.leftSandwichCLM (canonicalKraus Φ h) := by
      have h := MatrixStackedTraceout.left_selector_stack_channel (Fin b)
        (stackedEquiv a p) (canonicalKraus Φ)
      have hs : MatrixStackedTraceout.stack (stackedEquiv a p) (canonicalKraus Φ) = stackedKraus Φ := rfl
      rw [hs] at h
      simpa only [helper_leftSandwich_eq, aliceDiscardCLM, discardKraus] using h
    _ = _ := by
      rw [ContinuousCPProtocol.aliceReferenceCLM_eq_refined_sum
        (fun _ : Unit => Φ.toLinearMap) (fun _ => hCP) ()]
      exact ((Fintype.equivFin (Hidden a p)).symm.sum_comp (fun h =>
        LocalChannelMoments.leftSandwichCLM (canonicalKraus Φ h))).symm

theorem bobDiscard_stack {a b p : ℕ} (Φ : LocalMap b p)
    (hCP : CPTPKraus.CompletelyPositive Φ.toLinearMap) :
    (bobDiscardCLM a b p).comp (LocalChannelMoments.rightSandwichCLM (stackedKraus Φ)) =
      ContinuousCPProtocol.bobReferenceCLM Φ.toLinearMap := by
  classical
  calc
    _ = ∑ h : Hidden b p, LocalChannelMoments.rightSandwichCLM (canonicalKraus Φ h) := by
      have h := MatrixStackedTraceout.right_selector_stack_channel (Fin a)
        (stackedEquiv b p) (canonicalKraus Φ)
      have hs : MatrixStackedTraceout.stack (stackedEquiv b p) (canonicalKraus Φ) = stackedKraus Φ := rfl
      rw [hs] at h
      simpa only [helper_rightSandwich_eq, bobDiscardCLM, discardKraus] using h
    _ = _ := by
      rw [ContinuousCPProtocol.bobReferenceCLM_eq_refined_sum
        (fun _ : Unit => Φ.toLinearMap) (fun _ => hCP) ()]
      exact ((Fintype.equivFin (Hidden b p)).symm.sum_comp (fun h =>
        LocalChannelMoments.rightSandwichCLM (canonicalKraus Φ h))).symm

theorem measurable_packedAliceStack (c d a b : ℕ) :
    Measurable (fun z : Sigma (AliceFiber c d a b) =>
      (⟨stackedDimension a z.1, (stackedKraus z.2.1, z.2.2.comp (aliceDiscardCLM a z.1 b))⟩ :
        Sigma (MatrixVariableStateProtocol.AliceFiber c d a b))) := by
  apply measurable_fiberElim
  intro p
  apply (measurable_fiberMk (MatrixVariableStateProtocol.AliceFiber c d a b)
    (stackedDimension a p)).comp
  change Measurable (fun z : AliceFiber c d a b p =>
    (stackedKraus z.1, z.2.comp (aliceDiscardCLM a p b)))
  have hComp : Continuous (fun z : AliceFiber c d a b p => z.2.comp (aliceDiscardCLM a p b)) :=
    continuous_snd.clm_comp continuous_const
  exact ((measurable_stackedKraus a p).comp measurable_fst).prodMk hComp.measurable

theorem measurable_packedBobStack (c d a b : ℕ) :
    Measurable (fun z : Sigma (BobFiber c d a b) =>
      (⟨stackedDimension b z.1, (stackedKraus z.2.1, z.2.2.comp (bobDiscardCLM a b z.1))⟩ :
        Sigma (MatrixVariableStateProtocol.BobFiber c d a b))) := by
  apply measurable_fiberElim
  intro p
  apply (measurable_fiberMk (MatrixVariableStateProtocol.BobFiber c d a b)
    (stackedDimension b p)).comp
  change Measurable (fun z : BobFiber c d a b p =>
    (stackedKraus z.1, z.2.comp (bobDiscardCLM a b p)))
  have hComp : Continuous (fun z : BobFiber c d a b p => z.2.comp (bobDiscardCLM a b p)) :=
    continuous_snd.clm_comp continuous_const
  exact ((measurable_stackedKraus b p).comp measurable_fst).prodMk hComp.measurable

def matrixHeight : ℕ → ℕ
  | 0 => 0
  | h + 1 => matrixHeight h + 2

def toKraus {c d : ℕ} : {a b height : ℕ} → Tree.{u} c d a b height →
    MatrixVariableStateProtocol.Tree.{u} c d a b (matrixHeight height)
  | _, _, _, .finite height T => .finite (matrixHeight height) T
  | a, _, _, .alice Ω mΩ μ p Φ child =>
      letI := mΩ
      .alice Ω mΩ μ (fun x => stackedDimension a (p x))
        (fun x => stackedKraus (Φ x)) (fun x => aliceDiscardChild (a := a) (toKraus (child x)))
  | _, b, _, .bob Ω mΩ μ p Φ child =>
      letI := mΩ
      .bob Ω mΩ μ (fun x => stackedDimension b (p x))
        (fun x => stackedKraus (Φ x)) (fun x => bobDiscardChild (b := b) (toKraus (child x)))

def IntegrableMoments {c d : ℕ} : {a b height : ℕ} → Tree.{u} c d a b height → Prop
  | _, _, _, .finite _ _ => True
  | _, _, _, .alice _ mΩ μ _ Φ child =>
      letI := mΩ
      Integrable (fun x => (stackedKraus (Φ x)).conjTranspose * stackedKraus (Φ x)) μ ∧
        Integrable (fun x => (channel (child x)).comp
          (ContinuousCPProtocol.aliceReferenceCLM (Φ x).toLinearMap)) μ ∧
        ∀ x, IntegrableMoments (child x)
  | _, _, _, .bob _ mΩ μ _ Φ child =>
      letI := mΩ
      Integrable (fun x => (stackedKraus (Φ x)).conjTranspose * stackedKraus (Φ x)) μ ∧
        Integrable (fun x => (channel (child x)).comp
          (ContinuousCPProtocol.bobReferenceCLM (Φ x).toLinearMap)) μ ∧
        ∀ x, IntegrableMoments (child x)

theorem toKraus_spec {c d a b height : ℕ} (T : Tree.{u} c d a b height)
    (hT : Regular T) (hc : 0 < c) (hd : 0 < d) :
    MatrixVariableFiniteBaseProtocol.GeneralRegular (toKraus T) ∧
      MatrixVariableStateProtocol.channel (toKraus T) = channel T ∧ IntegrableMoments T := by
  classical
  revert hT
  induction T with
  | finite height U =>
      intro _
      exact ⟨trivial, rfl, trivial⟩
  | @alice a b height Ω mΩ μ p Φ child ih =>
      let := mΩ
      rintro ⟨hPacked, hCP, hTotal, hChild⟩
      have hIH := fun x => ih x (hChild x)
      have hGramMeas := (measurable_packedStackedGram a (fun r => Channel c d r b)).comp hPacked
      have hGram := integrable_stackedGram μ p Φ hGramMeas hCP hTotal
      have hComplete := integral_stackedGram_eq_one μ p Φ hGramMeas hCP hTotal
      have hStackPacked := (measurable_packedAliceStack c d a b).comp hPacked
      have hConvertedPacked : Measurable (fun x =>
          (⟨stackedDimension a (p x), (stackedKraus (Φ x),
            MatrixVariableStateProtocol.channel (aliceDiscardChild (a := a) (toKraus (child x))))⟩ :
            Sigma (MatrixVariableStateProtocol.AliceFiber c d a b))) := by
        convert hStackPacked using 1
        funext x
        rw [aliceDiscardChild_channel, (hIH x).2.1]
        rfl
      have hReg : MatrixVariableFiniteBaseProtocol.GeneralRegular
          (toKraus (Tree.alice Ω mΩ μ p Φ child)) :=
        ⟨hConvertedPacked, hComplete,
          fun x => aliceDiscardChild_generalRegular (toKraus (child x)) (hIH x).1⟩
      have hPoint (x : Ω) :
          (MatrixVariableStateProtocol.channel (aliceDiscardChild (a := a) (toKraus (child x)))).comp
              (LocalChannelMoments.leftSandwichCLM (stackedKraus (Φ x))) =
            (channel (child x)).comp (ContinuousCPProtocol.aliceReferenceCLM (Φ x).toLinearMap) := by
        rw [aliceDiscardChild_channel, (hIH x).2.1,
          ContinuousLinearMap.comp_assoc, aliceDiscard_stack (Φ x) (hCP x)]
      have hMatrixMoment : Integrable (fun x =>
          (MatrixVariableStateProtocol.channel (aliceDiscardChild (a := a) (toKraus (child x)))).comp
            (LocalChannelMoments.leftSandwichCLM (stackedKraus (Φ x)))) μ :=
        (MatrixVariableFiniteBaseProtocol.integrableMoments_of_generalRegular
          _ hReg hc hd).2.1
      have hPhysicalMoment : Integrable (fun x => (channel (child x)).comp
          (ContinuousCPProtocol.aliceReferenceCLM (Φ x).toLinearMap)) μ :=
        hMatrixMoment.congr (Eventually.of_forall hPoint)
      refine ⟨hReg, ?_, hGram, hPhysicalMoment, fun x => (hIH x).2.2⟩
      exact integral_congr_ae (Eventually.of_forall hPoint)
  | @bob a b height Ω mΩ μ p Φ child ih =>
      let := mΩ
      rintro ⟨hPacked, hCP, hTotal, hChild⟩
      have hIH := fun x => ih x (hChild x)
      have hGramMeas := (measurable_packedStackedGram b (fun r => Channel c d a r)).comp hPacked
      have hGram := integrable_stackedGram μ p Φ hGramMeas hCP hTotal
      have hComplete := integral_stackedGram_eq_one μ p Φ hGramMeas hCP hTotal
      have hStackPacked := (measurable_packedBobStack c d a b).comp hPacked
      have hConvertedPacked : Measurable (fun x =>
          (⟨stackedDimension b (p x), (stackedKraus (Φ x),
            MatrixVariableStateProtocol.channel (bobDiscardChild (b := b) (toKraus (child x))))⟩ :
            Sigma (MatrixVariableStateProtocol.BobFiber c d a b))) := by
        convert hStackPacked using 1
        funext x
        rw [bobDiscardChild_channel, (hIH x).2.1]
        rfl
      have hReg : MatrixVariableFiniteBaseProtocol.GeneralRegular
          (toKraus (Tree.bob Ω mΩ μ p Φ child)) :=
        ⟨hConvertedPacked, hComplete,
          fun x => bobDiscardChild_generalRegular (toKraus (child x)) (hIH x).1⟩
      have hPoint (x : Ω) :
          (MatrixVariableStateProtocol.channel (bobDiscardChild (b := b) (toKraus (child x)))).comp
              (LocalChannelMoments.rightSandwichCLM (stackedKraus (Φ x))) =
            (channel (child x)).comp (ContinuousCPProtocol.bobReferenceCLM (Φ x).toLinearMap) := by
        rw [bobDiscardChild_channel, (hIH x).2.1,
          ContinuousLinearMap.comp_assoc, bobDiscard_stack (Φ x) (hCP x)]
      have hMatrixMoment : Integrable (fun x =>
          (MatrixVariableStateProtocol.channel (bobDiscardChild (b := b) (toKraus (child x)))).comp
            (LocalChannelMoments.rightSandwichCLM (stackedKraus (Φ x)))) μ :=
        (MatrixVariableFiniteBaseProtocol.integrableMoments_of_generalRegular
          _ hReg hc hd).2.1
      have hPhysicalMoment : Integrable (fun x => (channel (child x)).comp
          (ContinuousCPProtocol.bobReferenceCLM (Φ x).toLinearMap)) μ :=
        hMatrixMoment.congr (Eventually.of_forall hPoint)
      refine ⟨hReg, ?_, hGram, hPhysicalMoment, fun x => (hIH x).2.2⟩
      exact integral_congr_ae (Eventually.of_forall hPoint)

theorem toKraus_generalRegular {c d a b height : ℕ} (T : Tree.{u} c d a b height)
    (hT : Regular T) (hc : 0 < c) (hd : 0 < d) :
    MatrixVariableFiniteBaseProtocol.GeneralRegular (toKraus T) := (toKraus_spec T hT hc hd).1

theorem toKraus_channel {c d a b height : ℕ} (T : Tree.{u} c d a b height)
    (hT : Regular T) (hc : 0 < c) (hd : 0 < d) :
    MatrixVariableStateProtocol.channel (toKraus T) = channel T := (toKraus_spec T hT hc hd).2.1

theorem integrableMoments_of_regular {c d a b height : ℕ} (T : Tree.{u} c d a b height)
    (hT : Regular T) (hc : 0 < c) (hd : 0 < d) :
    IntegrableMoments T := (toKraus_spec T hT hc hd).2.2

theorem channel_cptp {c d a b height : ℕ} (T : Tree.{u} c d a b height)
    (hT : Regular T) (hc : 0 < c) (hd : 0 < d) :
    CPTPKraus.CompletelyPositive (channel T).toLinearMap ∧
      CPTPKraus.TracePreserving (channel T).toLinearMap := by
  rw [← toKraus_channel T hT hc hd]
  exact MatrixVariableFiniteBaseProtocol.channel_cptp_of_generalRegular
    (toKraus T) (toKraus_generalRegular T hT hc hd) hc hd

theorem exists_finiteProtocol_channel_approx {c d a b height : ℕ}
    (T : Tree.{u} c d a b height) (hT : Regular T) (hc : 0 < c) (hd : 0 < d)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ U : FiniteLocalProtocol c d a b,
      ‖MatrixContinuousStateProtocol.finiteChannel U - channel T‖ < ε := by
  obtain ⟨U, hU⟩ := MatrixVariableFiniteBaseProtocol.exists_finiteProtocol_channel_approx_of_generalRegular
    (toKraus T) (toKraus_generalRegular T hT hc hd) hc hd ε hε
  rw [toKraus_channel T hT hc hd] at hU
  exact ⟨U, hU⟩

theorem exists_finiteProtocol_output_approx {c d a b height : ℕ}
    (T : Tree.{u} c d a b height) (hT : Regular T) (hc : 0 < c) (hd : 0 < d)
    (ρ : MatrixVariableStateProtocol.JointMatrix a b) (ε : ℝ) (hε : 0 < ε) :
    ∃ U : FiniteLocalProtocol c d a b, ‖U.apply ρ - channel T ρ‖ < ε := by
  obtain ⟨U, hU⟩ := MatrixVariableFiniteBaseProtocol.exists_finiteProtocol_output_approx_of_generalRegular
    (toKraus T) (toKraus_generalRegular T hT hc hd) hc hd ρ ε hε
  rw [toKraus_channel T hT hc hd] at hU
  exact ⟨U, hU⟩

theorem channel_pureOutput_mem_outputClosure {c d a b height : ℕ}
    (T : Tree.{u} c d a b height) (hT : Regular T) (hc : 0 < c) (hd : 0 < d)
    (ψ : Fin a × Fin b → ℂ) :
    channel T (pureDensity ψ) ∈ EndpointProtocolClosure.outputClosure ψ := by
  have hClosure := MatrixVariableFiniteBaseProtocol.channel_pureOutput_mem_outputClosure_of_generalRegular
    (toKraus T) (toKraus_generalRegular T hT hc hd) hc hd ψ
  rwa [toKraus_channel T hT hc hd] at hClosure

theorem channel_pureOutput_isDensity {c d a b height : ℕ}
    (T : Tree.{u} c d a b height) (hT : Regular T) (hc : 0 < c) (hd : 0 < d)
    (ψ : Fin a × Fin b → ℂ) (hNorm : vectorNormSq ψ = 1) :
    QuantumProver.QuantumEntropy.IsDensity (channel T (pureDensity ψ)) := by
  have hDensity := MatrixVariableFiniteBaseProtocol.channel_pureOutput_isDensity_of_generalRegular
    (toKraus T) (toKraus_generalRegular T hT hc hd) hc hd ψ hNorm
  rwa [toKraus_channel T hT hc hd] at hDensity

end QuantumProver.WernerEndpoint.MatrixVariableCPDensityProtocol

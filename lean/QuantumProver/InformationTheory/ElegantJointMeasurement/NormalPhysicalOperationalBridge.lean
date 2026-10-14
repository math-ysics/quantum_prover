import Mathlib
import QuantumProver.InformationTheory.ElegantJointMeasurement.NormalProcess
import QuantumProver.InformationTheory.ElegantJointMeasurement.MeasurableHilbertField
import QuantumProver.InformationTheory.ElegantJointMeasurement.NuclearFieldSupport
import QuantumProver.InformationTheory.ElegantJointMeasurement.NormalPhysicalAdmission
import QuantumProver.InformationTheory.ElegantJointMeasurement.NormalControlledSpectatorLift

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000

open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open TopologicalSpace QuantumProver.ElegantJointMeasurement.NuclearChoi
open scoped Topology ComplexOrder

namespace QuantumProver.ElegantJointMeasurement.NormalPhysicalOperationalBridge

open QuantumProver.ElegantJointMeasurement.NormalInstrumentAbsorption
open QuantumProver.HilbertNuclearCompression
open QuantumProver.MatrixNormalStateKernel
open QuantumProver.NuclearOperator (toOperator)

section PhysicalPosterior

variable {E H Ω : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [SeparableSpace E] [MeasurableSpace H] [MeasurableSpace Ω]
  [MeasurableSpace.CountableOrCountablyGenerated H Ω]

local instance nuclearMeasurable : MeasurableSpace (Nuclear E) := borel _
local instance nuclearBorel : BorelSpace (Nuclear E) := ⟨rfl⟩

theorem posterior_ae_eq_of_event_reconstruction
    (P : Instrument E E H Ω) (σ : H → Nuclear E)
    (hpos : ∀ h, (toOperator (σ h)).IsPositive)
    (hstrong : StronglyMeasurable σ)
    (htrace : ∀ h, QuantumProver.HilbertNuclearTrace.trace (σ h) = 1)
    (D : H × Ω → Nuclear E)
    (hDint : ∀ h, Integrable (fun ω => D (h,ω))
      (bornKernel P σ hpos hstrong htrace h))
    (hDset : ∀ h s, MeasurableSet s →
      (∫ ω in s, D (h,ω) ∂bornKernel P σ hpos hstrong htrace h) =
        P.operation h s (σ h)) (h : H) :
    (fun ω => posterior P σ hpos hstrong htrace (h,ω))
      =ᵐ[bornKernel P σ hpos hstrong htrace h] (fun ω => D (h,ω)) := by
  apply Integrable.ae_eq_of_forall_setIntegral_eq _ _
    (integrable_posterior P σ hpos hstrong htrace h) (hDint h)
  intro s hs _
  rw [setIntegral_posterior P σ hpos hstrong htrace h s hs, hDset h s hs]

theorem posterior_ae_supported_of_event_reconstruction
    (P : Instrument E E H Ω) (σ : H → Nuclear E)
    (hpos : ∀ h, (toOperator (σ h)).IsPositive)
    (hstrong : StronglyMeasurable σ)
    (htrace : ∀ h, QuantumProver.HilbertNuclearTrace.trace (σ h) = 1)
    (D : H × Ω → Nuclear E)
    (hDint : ∀ h, Integrable (fun ω => D (h,ω))
      (bornKernel P σ hpos hstrong htrace h))
    (hDset : ∀ h s, MeasurableSet s →
      (∫ ω in s, D (h,ω) ∂bornKernel P σ hpos hstrong htrace h) =
        P.operation h s (σ h))
    (Proj : H × Ω → E →L[ℂ] E)
    (hDsupport : ∀ z, compose (Proj z) (Proj z) (D z) = D z) (h : H) :
    ∀ᵐ ω ∂bornKernel P σ hpos hstrong htrace h,
      compose (Proj (h,ω)) (Proj (h,ω))
        (posterior P σ hpos hstrong htrace (h,ω)) =
        posterior P σ hpos hstrong htrace (h,ω) := by
  filter_upwards [posterior_ae_eq_of_event_reconstruction P σ hpos hstrong
    htrace D hDint hDset h] with ω hω
  rw [hω]
  exact hDsupport (h,ω)

theorem bornKernel_null_of_physical_event_zero
    (P : Instrument E E H Ω) (σ : H → Nuclear E)
    (hpos : ∀ h, (toOperator (σ h)).IsPositive)
    (hstrong : StronglyMeasurable σ)
    (htrace : ∀ h, QuantumProver.HilbertNuclearTrace.trace (σ h) = 1)
    (h : H) (s : Set Ω) (hs : MeasurableSet s)
    (hz : P.operation h s (σ h) = 0) :
    bornKernel P σ hpos hstrong htrace h s = 0 := by
  rw [bornKernel_apply P σ hpos hstrong htrace h s hs, hz]
  simp

end PhysicalPosterior

section ActualChronologicalDomain

open QuantumProver.ElegantJointMeasurement.NormalProcess QuantumProver.ElegantJointMeasurement.HilbertSquareProcess

variable {a b : ℕ} {R : Type*} [MeasurableSpace R] [StandardBorelSpace R]
  [NeZero a] [NeZero b] (P : MatrixProcess a b R)

theorem physicalPrefixMeasure_ae_admissible
    (S : (n : ℕ) → Set (History R n))
    (hS : ∀ n, MeasurableSet (S n))
    (hzero : PUnit.unit ∈ S 0)
    (hstep : ∀ n (h : History R n), h ∈ S n →
      P.represented_physicalBornKernel n h {r | appendHistory n (h,r) ∉ S (n+1)} = 0)
    (n : ℕ) : ∀ᵐ h ∂P.represented_physicalPrefixMeasure n, h ∈ S n := by
  induction n with
  | zero =>
      change ∀ᵐ h ∂Measure.dirac PUnit.unit, h ∈ S 0
      exact (ae_dirac_iff (hS 0)).mpr hzero
  | succ n ih =>
      change ∀ᵐ h ∂(((P.represented_physicalPrefixMeasure n) ⊗ₘ P.represented_physicalBornKernel n).map
        (appendHistory n)), h ∈ S (n+1)
      apply (ae_map_iff (appendHistory (R := R) n).measurable.aemeasurable (hS (n+1))).mpr
      apply Measure.ae_compProd_of_ae_ae
        ((hS (n+1)).preimage (appendHistory (R := R) n).measurable)
      filter_upwards [ih] with h hh
      exact ae_iff.mpr (hstep n h hh)

theorem physicalPrefixMeasure_admissible_compl_zero
    (S : (n : ℕ) → Set (History R n))
    (hS : ∀ n, MeasurableSet (S n))
    (hzero : PUnit.unit ∈ S 0)
    (hstep : ∀ n (h : History R n), h ∈ S n →
      P.represented_physicalBornKernel n h {r | appendHistory n (h,r) ∉ S (n+1)} = 0)
    (n : ℕ) : P.represented_physicalPrefixMeasure n (S n)ᶜ = 0 := by
  exact ae_iff.mp (physicalPrefixMeasure_ae_admissible P S hS hzero hstep n)

theorem physicalPrefixAction_admissible_compl_zero
    (S : (n : ℕ) → Set (History R n))
    (hS : ∀ n, MeasurableSet (S n))
    (hzero : PUnit.unit ∈ S 0)
    (hstep : ∀ n (h : History R n), h ∈ S n →
      P.represented_physicalBornKernel n h {r | appendHistory n (h,r) ∉ S (n+1)} = 0)
    (n : ℕ) (X : JointInputMatrix a b) :
    P.represented_physicalPrefixAction n (S n)ᶜ X = 0 := by
  rw [P.physicalPrefixAction_eq_physicalInputDensity n _ (hS n).compl X]
  have hz := physicalPrefixMeasure_admissible_compl_zero P S hS hzero hstep n
  simp only [Measure.restrict_eq_zero.mpr hz, integral_zero_measure]

end ActualChronologicalDomain

end QuantumProver.ElegantJointMeasurement.NormalPhysicalOperationalBridge

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000

open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open TopologicalSpace QuantumProver.ElegantJointMeasurement.NuclearChoi
open scoped Topology ComplexOrder

namespace QuantumProver.ElegantJointMeasurement.NormalPhysicalOperationalBridge

open QuantumProver.ElegantJointMeasurement.HilbertChoi QuantumProver.ElegantJointMeasurement.NuclearChoi
open QuantumProver.ElegantJointMeasurement.NormalInstrumentAbsorption QuantumProver.ElegantJointMeasurement.NormalSandwich
open QuantumProver.ElegantJointMeasurement.SeparableHilbertEmbedding QuantumProver.ElegantJointMeasurement.MeasurableHilbertField
open QuantumProver.HilbertNuclearCompression QuantumProver.MatrixNuclearTensor
open QuantumProver.NuclearOperator (toOperator toOperator_injective)

section SandwichComposition

variable {E F G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

theorem sandwich_comp_apply (J : F →L[ℂ] E) (K : G →L[ℂ] F) (U : Nuclear G) :
    sandwich J (sandwich K U) = sandwich (J.comp K) U := by
  apply toOperator_injective
  simp only [toOperator_sandwich, ContinuousLinearMap.adjoint_comp]
  ext x
  rfl

end SandwichComposition

section PhysicalPhysicalRetraction

variable {H : Type*} [MeasurableSpace H]
  {EA EB : H → Type*}
  [∀ h, NormedAddCommGroup (EA h)] [∀ h, InnerProductSpace ℂ (EA h)]
  [∀ h, CompleteSpace (EA h)]
  [∀ h, NormedAddCommGroup (EB h)] [∀ h, InnerProductSpace ℂ (EB h)]
  [∀ h, CompleteSpace (EB h)]
  (FA : FundamentalFamily EA) (FB : FundamentalFamily EB)

def physicalJointProjection (h : H) :
    Joint CommonHilbert CommonHilbert →L[ℂ] Joint CommonHilbert CommonHilbert :=
  tensorMap (FA.rangeProjection h) (FB.rangeProjection h)

def physicalStateCode (h : H) :
    Nuclear (Joint (EA h) (EB h)) →L[ℂ] Nuclear (Joint CommonHilbert CommonHilbert) :=
  sandwich (tensorMap (FA.embedding h).toContinuousLinearMap
    (FB.embedding h).toContinuousLinearMap)

def physicalStateRecover (h : H) :
    Nuclear (Joint CommonHilbert CommonHilbert) →L[ℂ] Nuclear (Joint (EA h) (EB h)) :=
  sandwich (tensorMap (FA.embedding h).toContinuousLinearMap
    (FB.embedding h).toContinuousLinearMap).adjoint

theorem physicalJointProjection_eq (h : H) :
    physicalJointProjection FA FB h =
      (tensorMap (FA.embedding h).toContinuousLinearMap
        (FB.embedding h).toContinuousLinearMap).comp
      (tensorMap (FA.embedding h).toContinuousLinearMap
        (FB.embedding h).toContinuousLinearMap).adjoint := by
  rw [tensorMap_adjoint]
  change tensorMap
    ((FA.embedding h).toContinuousLinearMap.comp
      (FA.embedding h).toContinuousLinearMap.adjoint)
    ((FB.embedding h).toContinuousLinearMap.comp
      (FB.embedding h).toContinuousLinearMap.adjoint) = _
  exact tensorMap_comp _ _ _ _

theorem physicalJointProjection_adjoint (h : H) :
    (physicalJointProjection FA FB h).adjoint = physicalJointProjection FA FB h := by
  rw [physicalJointProjection_eq]
  simp only [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint]

theorem physicalStateCode_completelyPositive (h : H) :
    NormalCompletelyPositive (physicalStateCode FA FB h) :=
  normalCompletelyPositive_sandwich _

theorem physicalStateRecover_completelyPositive (h : H) :
    NormalCompletelyPositive (physicalStateRecover FA FB h) :=
  normalCompletelyPositive_sandwich _

theorem physicalStateCode_recover (h : H)
    (U : Nuclear (Joint CommonHilbert CommonHilbert)) :
    physicalStateCode FA FB h (physicalStateRecover FA FB h U) =
      compose (physicalJointProjection FA FB h) (physicalJointProjection FA FB h) U := by
  let J : Joint (EA h) (EB h) →L[ℂ] Joint CommonHilbert CommonHilbert :=
    tensorMap (FA.embedding h).toContinuousLinearMap (FB.embedding h).toContinuousLinearMap
  change sandwich J (sandwich J.adjoint U) = _
  rw [sandwich_comp_apply]
  have hJ : J.comp J.adjoint = physicalJointProjection FA FB h :=
    (physicalJointProjection_eq FA FB h).symm
  rw [hJ]
  simp only [sandwich, physicalJointProjection_adjoint]

theorem physicalState_retraction (h : H)
    (U : Nuclear (Joint CommonHilbert CommonHilbert))
    (hU : compose (physicalJointProjection FA FB h) (physicalJointProjection FA FB h) U = U) :
    physicalStateCode FA FB h (physicalStateRecover FA FB h U) = U :=
  (physicalStateCode_recover FA FB h U).trans hU

variable {I : Type} [Fintype I] [DecidableEq I]

local instance physicalBlockComplete {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [CompleteSpace V] : CompleteSpace (BlockSpace I V) :=
  PiLp.completeSpace 2 (fun _ : I => V)

set_option maxHeartbeats 6000000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

theorem physicalStateCode_recover_amplified (h : H)
    (U : Nuclear (BlockSpace I (Joint CommonHilbert CommonHilbert))) :
    normalAmplification (E := Joint CommonHilbert CommonHilbert) (F := Joint (EA h) (EB h))
      (R := I) (physicalStateCode FA FB h)
      (normalAmplification (E := Joint (EA h) (EB h)) (F := Joint CommonHilbert CommonHilbert)
        (R := I) (physicalStateRecover FA FB h) U) =
      compose (blockLift (R := I) (physicalJointProjection FA FB h))
        (blockLift (R := I) (physicalJointProjection FA FB h)) U := by
  let code : NormalOperation (Joint (EA h) (EB h)) (Joint CommonHilbert CommonHilbert) :=
    physicalStateCode FA FB h
  let recover : NormalOperation (Joint CommonHilbert CommonHilbert) (Joint (EA h) (EB h)) :=
    physicalStateRecover FA FB h
  have he : code.comp recover =
      sandwich (physicalJointProjection FA FB h) := by
    apply ContinuousLinearMap.ext
    intro T
    change physicalStateCode FA FB h (physicalStateRecover FA FB h T) = _
    rw [physicalStateCode_recover]
    simp only [sandwich, physicalJointProjection_adjoint]
  change normalAmplification (R := I) code (normalAmplification (R := I) recover U) = _
  rw [← normalAmplification_comp code recover U, he, normalAmplification_sandwich,
    blockLift_adjoint, physicalJointProjection_adjoint]

set_option maxHeartbeats 1200000

theorem physicalState_retraction_amplified (h : H)
    (U : Nuclear (BlockSpace I (Joint CommonHilbert CommonHilbert)))
    (hU : compose (blockLift (R := I) (physicalJointProjection FA FB h))
      (blockLift (R := I) (physicalJointProjection FA FB h)) U = U) :
    normalAmplification (physicalStateCode FA FB h)
      (normalAmplification (physicalStateRecover FA FB h) U) = U :=
  (physicalStateCode_recover_amplified FA FB h U).trans hU

theorem physicalStateRecover_amplified_isPositive (h : H)
    (U : Nuclear (BlockSpace I (Joint CommonHilbert CommonHilbert)))
    (hU : (toOperator U).IsPositive) :
    (toOperator (normalAmplification (physicalStateRecover FA FB h) U)).IsPositive :=
  physicalStateRecover_completelyPositive FA FB h I U hU

end PhysicalPhysicalRetraction

section ConditionalPhysicalChronology

open QuantumProver.ElegantJointMeasurement.NormalProcess QuantumProver.ElegantJointMeasurement.HilbertSquareProcess

variable {a b : ℕ} {R : Type*} [MeasurableSpace R] [StandardBorelSpace R]
  [NeZero a] [NeZero b] (P : MatrixProcess a b R)

theorem physicalPrefixMeasure_ae_local_invariant
    (S : (n : ℕ) → Set (History R n))
    (hS : ∀ n, MeasurableSet (S n))
    (hzero : PUnit.unit ∈ S 0)
    (hstep : ∀ n (h : History R n), h ∈ S n →
      ∀ᵐ r ∂P.represented_physicalBornKernel n h, appendHistory n (h,r) ∈ S (n+1))
    (n : ℕ) : ∀ᵐ h ∂P.represented_physicalPrefixMeasure n, h ∈ S n := by
  induction n with
  | zero =>
      change ∀ᵐ h ∂Measure.dirac PUnit.unit, h ∈ S 0
      exact (ae_dirac_iff (hS 0)).mpr hzero
  | succ n ih =>
      change ∀ᵐ h ∂(((P.represented_physicalPrefixMeasure n) ⊗ₘ P.represented_physicalBornKernel n).map
        (appendHistory n)), h ∈ S (n+1)
      apply (ae_map_iff (appendHistory (R := R) n).measurable.aemeasurable (hS (n+1))).mpr
      apply Measure.ae_compProd_of_ae_ae
        ((hS (n+1)).preimage (appendHistory (R := R) n).measurable)
      filter_upwards [ih] with h hh
      exact hstep n h hh

theorem physicalInputDensity_supported_of_physicalState_supported
    (n : ℕ) (h : History R n) (X : JointInputMatrix a b)
    (Proj : JointWorkspace →L[ℂ] JointWorkspace) (hProj : Proj.adjoint = Proj)
    (hstate : compose (blockLift (R := Fin a × Fin b) Proj)
      (blockLift (R := Fin a × Fin b) Proj) (P.represented_physicalState n h) = P.represented_physicalState n h) :
    compose Proj Proj (P.represented_physicalInputDensity n X h) = P.represented_physicalInputDensity n X h := by
  have he : normalAmplification (sandwich Proj) (P.represented_physicalState n h) =
      P.represented_physicalState n h := by
    rw [normalAmplification_sandwich, blockLift_adjoint, hProj]
    exact hstate
  have hd := congrArg (chargedDecode X) he
  rw [chargedDecode_normalAmplification] at hd
  simpa only [sandwich, hProj, MatrixProcess.represented_physicalInputDensity] using hd

end ConditionalPhysicalChronology

end QuantumProver.ElegantJointMeasurement.NormalPhysicalOperationalBridge

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000

open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped BigOperators Topology ComplexOrder

namespace QuantumProver.ElegantJointMeasurement.NormalPhysicalOperationalBridge

open QuantumProver.ElegantJointMeasurement.HilbertChoi QuantumProver.ElegantJointMeasurement.NuclearChoi
open QuantumProver.ElegantJointMeasurement.NormalInstrumentAbsorption QuantumProver.ElegantJointMeasurement.NormalSandwich
open QuantumProver.ElegantJointMeasurement.SeparableHilbertEmbedding QuantumProver.ElegantJointMeasurement.MeasurableHilbertField
open QuantumProver.HilbertNuclearCompression QuantumProver.MatrixNuclearTensor
open QuantumProver.NuclearOperator (toOperator toOperator_injective)

section ProjectionAbsorption

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

theorem nuclear_support_of_projection_absorption (M C : V →L[ℂ] V)
    (hMC : M.comp C = C) (hCM : C.comp M = C) (U : Nuclear V)
    (hU : compose C C U = U) : compose M M U = U := by
  have hTo : C.comp ((toOperator U).comp C) = toOperator U := by
    simpa only [toOperator_compose, ContinuousLinearMap.comp_assoc] using
      congrArg toOperator hU
  apply toOperator_injective
  rw [toOperator_compose]
  change M.comp ((toOperator U).comp M) = toOperator U
  calc
    M.comp ((toOperator U).comp M) =
        M.comp ((C.comp ((toOperator U).comp C)).comp M) := by rw [hTo]
    _ = (M.comp C).comp ((toOperator U).comp (C.comp M)) := by ext x; rfl
    _ = C.comp ((toOperator U).comp C) := by rw [hMC, hCM]
    _ = toOperator U := hTo

end ProjectionAbsorption

section PhysicalProjectionField

variable {H : Type*} [MeasurableSpace H]
  {EA EB : H → Type*}
  [∀ h, NormedAddCommGroup (EA h)] [∀ h, InnerProductSpace ℂ (EA h)]
  [∀ h, CompleteSpace (EA h)]
  [∀ h, NormedAddCommGroup (EB h)] [∀ h, InnerProductSpace ℂ (EB h)]
  [∀ h, CompleteSpace (EB h)]
  (FA : FundamentalFamily EA) (FB : FundamentalFamily EB)

section FundamentalFiberSeparability

include FA

theorem fundamentalFamily_fiber_separable (h : H) : SeparableSpace (EA h) := by
  have hs : TopologicalSpace.IsSeparable
      (closure (Submodule.span ℂ (range (FA.vector h)) : Set (EA h))) :=
    ((Set.countable_range (FA.vector h)).isSeparable.span (R := ℂ)).closure
  have hc : closure (Submodule.span ℂ (range (FA.vector h)) : Set (EA h)) = univ := by
    rw [← Submodule.topologicalClosure_coe, FA.dense h, Submodule.top_coe]
  exact TopologicalSpace.isSeparable_univ_iff.mp (hc ▸ hs)

end FundamentalFiberSeparability

theorem physicalJointEmbedding_adjoint_comp (h : H) :
    (tensorMap (FA.embedding h).toContinuousLinearMap
      (FB.embedding h).toContinuousLinearMap).adjoint.comp
      (tensorMap (FA.embedding h).toContinuousLinearMap
        (FB.embedding h).toContinuousLinearMap) =
      ContinuousLinearMap.id ℂ (Joint (EA h) (EB h)) := by
  rw [tensorMap_adjoint, ← tensorMap_comp,
    (FA.embedding h).adjoint_comp_self, (FB.embedding h).adjoint_comp_self]
  change tensorMap (ContinuousLinearMap.id ℂ (EA h)) (ContinuousLinearMap.id ℂ (EB h)) = _
  exact tensorMap_id_id

theorem physicalJointProjection_idempotent (h : H) :
    (physicalJointProjection FA FB h).comp (physicalJointProjection FA FB h) =
      physicalJointProjection FA FB h := by
  rw [physicalJointProjection_eq]
  let J := tensorMap (FA.embedding h).toContinuousLinearMap
    (FB.embedding h).toContinuousLinearMap
  have he : ∀ y : Joint (EA h) (EB h), J.adjoint (J y) = y :=
    fun y => congrArg (fun L => L y) (physicalJointEmbedding_adjoint_comp FA FB h)
  ext x
  change J (J.adjoint (J (J.adjoint x))) = J (J.adjoint x)
  rw [he]

theorem physicalJointProjection_embedding (h : H) (x : Joint (EA h) (EB h)) :
    physicalJointProjection FA FB h
      (tensorMap (FA.embedding h).toContinuousLinearMap
        (FB.embedding h).toContinuousLinearMap x) =
      tensorMap (FA.embedding h).toContinuousLinearMap
        (FB.embedding h).toContinuousLinearMap x := by
  rw [physicalJointProjection_eq]
  have he := congrArg (fun L => L x) (physicalJointEmbedding_adjoint_comp FA FB h)
  exact congrArg (tensorMap (FA.embedding h).toContinuousLinearMap
    (FB.embedding h).toContinuousLinearMap) he

theorem physicalStateRecover_code (h : H) (U : Nuclear (Joint (EA h) (EB h))) :
    physicalStateRecover FA FB h (physicalStateCode FA FB h U) = U := by
  apply toOperator_injective
  rw [physicalStateRecover, physicalStateCode, toOperator_sandwich,
    toOperator_sandwich, ContinuousLinearMap.adjoint_adjoint]
  let J := tensorMap (FA.embedding h).toContinuousLinearMap
    (FB.embedding h).toContinuousLinearMap
  have he : ∀ y : Joint (EA h) (EB h), J.adjoint (J y) = y :=
    fun y => congrArg (fun L => L y) (physicalJointEmbedding_adjoint_comp FA FB h)
  ext x
  change J.adjoint (J (toOperator U (J.adjoint (J x)))) = toOperator U x
  rw [he, he]

theorem physicalStateCode_supported (h : H) (U : Nuclear (Joint (EA h) (EB h))) :
    compose (physicalJointProjection FA FB h) (physicalJointProjection FA FB h)
      (physicalStateCode FA FB h U) = physicalStateCode FA FB h U := by
  rw [← physicalStateCode_recover, physicalStateRecover_code]

theorem physicalStateCode_trace (h : H) (U : Nuclear (Joint (EA h) (EB h))) :
    QuantumProver.HilbertNuclearTrace.trace (physicalStateCode FA FB h U) =
      QuantumProver.HilbertNuclearTrace.trace U := by
  change QuantumProver.HilbertNuclearTrace.trace
    (compose (tensorMap (FA.embedding h).toContinuousLinearMap
      (FB.embedding h).toContinuousLinearMap)
      (tensorMap (FA.embedding h).toContinuousLinearMap
        (FB.embedding h).toContinuousLinearMap).adjoint U) = _
  rw [QuantumProver.ElegantJointMeasurement.NormalCPInstruments.trace_compose_cycle,
    physicalJointEmbedding_adjoint_comp, QuantumProver.MatrixNormalTensorExtension.compose_id_id_apply]

theorem physicalStateRecover_trace_of_supported (h : H)
    (U : Nuclear (Joint CommonHilbert CommonHilbert))
    (hU : compose (physicalJointProjection FA FB h) (physicalJointProjection FA FB h) U = U) :
    QuantumProver.HilbertNuclearTrace.trace (physicalStateRecover FA FB h U) =
      QuantumProver.HilbertNuclearTrace.trace U := by
  have ht := physicalStateCode_trace FA FB h (physicalStateRecover FA FB h U)
  rw [physicalState_retraction FA FB h U hU] at ht
  exact ht.symm

theorem continuous_tmulJoint :
    Continuous (fun p : CommonHilbert × CommonHilbert => tmulJoint p.1 p.2) :=
  (tmulJoint.continuous.comp continuous_fst).clm_apply continuous_snd

theorem stronglyMeasurable_physicalJointProjection_apply
    (x : Joint CommonHilbert CommonHilbert) :
    StronglyMeasurable (fun h => physicalJointProjection FA FB h x) := by
  apply QuantumProver.MatrixNormalTensorInstrument.stronglyMeasurable_apply_of_dense
    (range ((↑) : TensorProduct ℂ CommonHilbert CommonHilbert →
      Joint CommonHilbert CommonHilbert))
    UniformSpace.Completion.denseRange_coe
    (fun h => physicalJointProjection FA FB h) ?_ x
  rintro z ⟨w,rfl⟩
  induction w using TensorProduct.induction_on with
  | zero =>
      simpa only [UniformSpace.Completion.coe_zero, map_zero] using
        (stronglyMeasurable_const : StronglyMeasurable (fun _ : H =>
          (0 : Joint CommonHilbert CommonHilbert)))
  | tmul u v =>
      have hu := FA.stronglyMeasurable_rangeProjection_apply
        (fun _ : H => u) stronglyMeasurable_const
      have hv := FB.stronglyMeasurable_rangeProjection_apply
        (fun _ : H => v) stronglyMeasurable_const
      have hm := continuous_tmulJoint.comp_stronglyMeasurable (hu.prodMk hv)
      simpa only [physicalJointProjection, ← tmulJoint_apply, tensorMap_tmul] using hm
  | add u v hu hv =>
      convert hu.add hv using 1
      funext h
      simp only [UniformSpace.Completion.coe_add, map_add, Pi.add_apply]

theorem stronglyMeasurable_physicalJointProjection_variable
    (x : H → Joint CommonHilbert CommonHilbert) (hx : StronglyMeasurable x) :
    StronglyMeasurable (fun h => physicalJointProjection FA FB h (x h)) :=
  stronglyMeasurable_variable_apply (fun h => physicalJointProjection FA FB h)
    (stronglyMeasurable_physicalJointProjection_apply FA FB) x hx

theorem measurableSet_physicalState_supported
    (U : H → Nuclear (Joint CommonHilbert CommonHilbert))
    (hU : StronglyMeasurable U) :
    MeasurableSet {h | compose (physicalJointProjection FA FB h)
      (physicalJointProjection FA FB h) (U h) = U h} := by
  let : MeasurableSpace (Nuclear (Joint CommonHilbert CommonHilbert)) := borel _
  let : BorelSpace (Nuclear (Joint CommonHilbert CommonHilbert)) := ⟨rfl⟩
  have hsand := QuantumProver.ElegantJointMeasurement.NuclearFieldSupport.stronglyMeasurable_sandwich_variable
      (fun h => physicalJointProjection FA FB h)
      (physicalJointProjection_adjoint FA FB)
      (stronglyMeasurable_physicalJointProjection_apply FA FB) U hU
  have hm := measurableSet_eq_fun (hsand.sub hU).norm.measurable
    (measurable_const : Measurable (fun _ : H => (0 : ℝ)))
  simpa only [Pi.sub_apply, norm_eq_zero, sub_eq_zero] using hm

section Reference

variable {I : Type} [Fintype I] [DecidableEq I]
local instance supportBlockComplete {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [CompleteSpace V] : CompleteSpace (BlockSpace I V) :=
  PiLp.completeSpace 2 (fun _ : I => V)

theorem physicalState_reference_bob_supported (h : H)
    (U : Nuclear (BlockSpace I (Joint CommonHilbert CommonHilbert)))
    (hU : compose (blockLift (R := I) (physicalJointProjection FA FB h))
      (blockLift (R := I) (physicalJointProjection FA FB h)) U = U) :
    compose (blockLift (R := I)
      (tensorMap (ContinuousLinearMap.id ℂ CommonHilbert) (FB.rangeProjection h)))
      (blockLift (R := I)
        (tensorMap (ContinuousLinearMap.id ℂ CommonHilbert) (FB.rangeProjection h))) U = U := by
  have hB : (FB.rangeProjection h).comp (FB.rangeProjection h) = FB.rangeProjection h :=
    QuantumProver.CountableFrameProjection.rangeProjection_idempotent (FB.vector h) (FB.dense h)
  have hMC : (tensorMap (ContinuousLinearMap.id ℂ CommonHilbert) (FB.rangeProjection h)).comp
      (physicalJointProjection FA FB h) = physicalJointProjection FA FB h := by
    rw [physicalJointProjection, ← tensorMap_comp, ContinuousLinearMap.id_comp, hB]
  have hCM : (physicalJointProjection FA FB h).comp
      (tensorMap (ContinuousLinearMap.id ℂ CommonHilbert) (FB.rangeProjection h)) =
      physicalJointProjection FA FB h := by
    rw [physicalJointProjection, ← tensorMap_comp, ContinuousLinearMap.comp_id, hB]
  apply nuclear_support_of_projection_absorption _ _ _ _ U hU
  · ext x i
    exact congrArg (fun L => L (x i)) hMC
  · ext x i
    exact congrArg (fun L => L (x i)) hCM

theorem physicalState_reference_alice_supported (h : H)
    (U : Nuclear (BlockSpace I (Joint CommonHilbert CommonHilbert)))
    (hU : compose (blockLift (R := I) (physicalJointProjection FA FB h))
      (blockLift (R := I) (physicalJointProjection FA FB h)) U = U) :
    compose (blockLift (R := I)
      (tensorMap (FA.rangeProjection h) (ContinuousLinearMap.id ℂ CommonHilbert)))
      (blockLift (R := I)
        (tensorMap (FA.rangeProjection h) (ContinuousLinearMap.id ℂ CommonHilbert))) U = U := by
  have hA : (FA.rangeProjection h).comp (FA.rangeProjection h) = FA.rangeProjection h :=
    QuantumProver.CountableFrameProjection.rangeProjection_idempotent (FA.vector h) (FA.dense h)
  have hMC : (tensorMap (FA.rangeProjection h) (ContinuousLinearMap.id ℂ CommonHilbert)).comp
      (physicalJointProjection FA FB h) = physicalJointProjection FA FB h := by
    rw [physicalJointProjection, ← tensorMap_comp, ContinuousLinearMap.id_comp, hA]
  have hCM : (physicalJointProjection FA FB h).comp
      (tensorMap (FA.rangeProjection h) (ContinuousLinearMap.id ℂ CommonHilbert)) =
      physicalJointProjection FA FB h := by
    rw [physicalJointProjection, ← tensorMap_comp, ContinuousLinearMap.comp_id, hA]
  apply nuclear_support_of_projection_absorption _ _ _ _ U hU
  · ext x i
    exact congrArg (fun L => L (x i)) hMC
  · ext x i
    exact congrArg (fun L => L (x i)) hCM

theorem physicalStateCode_amplified_trace (h : H)
    (U : Nuclear (BlockSpace I (Joint (EA h) (EB h)))) :
    QuantumProver.HilbertNuclearTrace.trace (normalAmplification (physicalStateCode FA FB h) U) =
      QuantumProver.HilbertNuclearTrace.trace U :=
  QuantumProver.ElegantJointMeasurement.NormalCompleteContraction.trace_normalAmplification
    (physicalStateCode FA FB h) (physicalStateCode_trace FA FB h) U

theorem physicalStateRecover_amplified_trace_of_supported (h : H)
    (U : Nuclear (BlockSpace I (Joint CommonHilbert CommonHilbert)))
    (hU : compose (blockLift (R := I) (physicalJointProjection FA FB h))
      (blockLift (R := I) (physicalJointProjection FA FB h)) U = U) :
    QuantumProver.HilbertNuclearTrace.trace
      (normalAmplification (physicalStateRecover FA FB h) U) =
      QuantumProver.HilbertNuclearTrace.trace U := by
  have ht := physicalStateCode_amplified_trace FA FB h
    (normalAmplification (physicalStateRecover FA FB h) U)
  rw [physicalState_retraction_amplified FA FB h U hU] at ht
  exact ht.symm

theorem stronglyMeasurable_physicalJointProjection_block_apply
    (x : BlockSpace I (Joint CommonHilbert CommonHilbert)) :
    StronglyMeasurable (fun h => blockLift (R := I) (physicalJointProjection FA FB h) x) := by
  have he : (fun h => blockLift (R := I) (physicalJointProjection FA FB h) x) =
      (fun h => ∑ i : I, QuantumProver.ElegantJointMeasurement.HilbertChoi.insert i (physicalJointProjection FA FB h (x i))) := by
    funext h
    ext j
    simp only [blockLift_apply, WithLp.ofLp_sum, Finset.sum_apply, insert_apply_apply]
    simp
  rw [he]
  apply Finset.stronglyMeasurable_fun_sum
  intro i hi
  exact (QuantumProver.ElegantJointMeasurement.HilbertChoi.insert i).continuous.comp_stronglyMeasurable
    (stronglyMeasurable_physicalJointProjection_apply FA FB (x i))

theorem measurableSet_physicalState_reference_supported
    (U : H → Nuclear (BlockSpace I (Joint CommonHilbert CommonHilbert)))
    (hU : StronglyMeasurable U) :
    MeasurableSet {h | compose (blockLift (R := I) (physicalJointProjection FA FB h))
      (blockLift (R := I) (physicalJointProjection FA FB h)) (U h) = U h} := by
  let : MeasurableSpace (Nuclear (BlockSpace I (Joint CommonHilbert CommonHilbert))) := borel _
  let : BorelSpace (Nuclear (BlockSpace I (Joint CommonHilbert CommonHilbert))) := ⟨rfl⟩
  have hsand := QuantumProver.ElegantJointMeasurement.NuclearFieldSupport.stronglyMeasurable_sandwich_variable
      (fun h => blockLift (R := I) (physicalJointProjection FA FB h))
      (fun h => by rw [blockLift_adjoint, physicalJointProjection_adjoint])
      (stronglyMeasurable_physicalJointProjection_block_apply FA FB) U hU
  have hm := measurableSet_eq_fun (hsand.sub hU).norm.measurable
    (measurable_const : Measurable (fun _ : H => (0 : ℝ)))
  simpa only [Pi.sub_apply, norm_eq_zero, sub_eq_zero] using hm

end Reference
end PhysicalProjectionField

end QuantumProver.ElegantJointMeasurement.NormalPhysicalOperationalBridge

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000

open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped Topology ComplexOrder

namespace QuantumProver.ElegantJointMeasurement.NormalPhysicalOperationalBridge

open QuantumProver.ElegantJointMeasurement.NormalInstrumentAbsorption
open QuantumProver.MatrixNormalStateKernel
open QuantumProver.NuclearOperator (toOperator)

section OutcomeCoding

variable {E H K Ω Ξ : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [SeparableSpace E] [MeasurableSpace H] [MeasurableSpace K]
  [MeasurableSpace Ω] [MeasurableSpace Ξ]
  [MeasurableSpace.CountableOrCountablyGenerated H Ξ]
  [MeasurableSpace.CountableOrCountablyGenerated K Ω]

local instance localNuclearMeasurable : MeasurableSpace (Nuclear E) := borel _
local instance localNuclearBorel : BorelSpace (Nuclear E) := ⟨rfl⟩

variable
  (P : Instrument E E H Ξ) (σ : H → Nuclear E)
  (hpos : ∀ h, (toOperator (σ h)).IsPositive)
  (hstrong : StronglyMeasurable σ)
  (htrace : ∀ h, QuantumProver.HilbertNuclearTrace.trace (σ h) = 1)
  (Q : Instrument E E K Ω) (τ : K → Nuclear E)
  (hτpos : ∀ k, (toOperator (τ k)).IsPositive)
  (hτstrong : StronglyMeasurable τ)
  (hτtrace : ∀ k, QuantumProver.HilbertNuclearTrace.trace (τ k) = 1)
  (e : Ω → Ξ) (he : MeasurableEmbedding e) (h : H) (k : K)
  (hEvent : ∀ s, MeasurableSet s →
    P.operation h s (σ h) = Q.operation k (e ⁻¹' s) (τ k))

include he hEvent

theorem bornKernel_map_of_physical_events :
    bornKernel P σ hpos hstrong htrace h =
      (bornKernel Q τ hτpos hτstrong hτtrace k).map e := by
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply he.measurable hs,
    bornKernel_apply P σ hpos hstrong htrace h s hs,
    bornKernel_apply Q τ hτpos hτstrong hτtrace k (e ⁻¹' s) (he.measurable hs),
    hEvent s hs]

theorem posterior_ae_eq_after_outcomeCoding :
    (fun ω => posterior Q τ hτpos hτstrong hτtrace (k,ω))
      =ᵐ[bornKernel Q τ hτpos hτstrong hτtrace k]
        (fun ω => posterior P σ hpos hstrong htrace (h,e ω)) := by
  have hBorn := bornKernel_map_of_physical_events
    P σ hpos hstrong htrace Q τ hτpos hτstrong hτtrace e he h k hEvent
  have hInt : Integrable
      (fun ω => posterior P σ hpos hstrong htrace (h,e ω))
      (bornKernel Q τ hτpos hτstrong hτtrace k) := by
    have hi := integrable_posterior P σ hpos hstrong htrace h
    rw [hBorn] at hi
    exact hi.comp_measurable he.measurable
  apply Integrable.ae_eq_of_forall_setIntegral_eq _ _
    (integrable_posterior Q τ hτpos hτstrong hτtrace k) hInt
  intro s hs _
  have hsImage := he.measurableSet_image' hs
  have hAction : Q.operation k s (τ k) = P.operation h (e '' s) (σ h) := by
    have ha := hEvent (e '' s) hsImage
    rw [he.injective.preimage_image s] at ha
    exact ha.symm
  calc
    (∫ ω in s, posterior Q τ hτpos hτstrong hτtrace (k,ω)
        ∂bornKernel Q τ hτpos hτstrong hτtrace k) = Q.operation k s (τ k) :=
      setIntegral_posterior Q τ hτpos hτstrong hτtrace k s hs
    _ = P.operation h (e '' s) (σ h) := hAction
    _ = (∫ ξ in e '' s, posterior P σ hpos hstrong htrace (h,ξ)
        ∂bornKernel P σ hpos hstrong htrace h) :=
      (setIntegral_posterior P σ hpos hstrong htrace h (e '' s) hsImage).symm
    _ = (∫ ω in s, posterior P σ hpos hstrong htrace (h,e ω)
        ∂bornKernel Q τ hτpos hτstrong hτtrace k) := by
      rw [hBorn, he.setIntegral_map, he.injective.preimage_image s]

end OutcomeCoding

end QuantumProver.ElegantJointMeasurement.NormalPhysicalOperationalBridge

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000

open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped BigOperators Topology ComplexOrder

namespace QuantumProver.ElegantJointMeasurement.NormalPhysicalOperationalBridge

open QuantumProver.ElegantJointMeasurement.NormalProcess QuantumProver.ElegantJointMeasurement.HilbertSquareProcess
open QuantumProver.ElegantJointMeasurement.HilbertChoi QuantumProver.ElegantJointMeasurement.NuclearChoi QuantumProver.ElegantJointMeasurement.HilbertFiniteKrausPredual
open QuantumProver.ElegantJointMeasurement.NormalInstrumentAbsorption QuantumProver.ElegantJointMeasurement.NormalSandwich
open QuantumProver.ElegantJointMeasurement.SeparableHilbertEmbedding QuantumProver.ElegantJointMeasurement.MeasurableHilbertField
open QuantumProver.HilbertNuclearCompression QuantumProver.MatrixNuclearTensor
open QuantumProver.NuclearOperator (toOperator toOperator_injective)

section PhysicalInitialRange

variable {a b : ℕ} {R : Type*} [MeasurableSpace R] [StandardBorelSpace R]
  [NeZero a] [NeZero b] (P : MatrixProcess a b R)
  (Proj : JointWorkspace →L[ℂ] JointWorkspace)
  (hProj : Proj.adjoint = Proj)
  (hRange : Proj.comp P.initialJointMap = P.initialJointMap)

include hProj hRange

theorem initialJointOperation_supported (X : JointInputMatrix a b) :
    compose Proj Proj (P.initialJointOperation X) = P.initialJointOperation X := by
  have hLeft (x : EuclideanSpace ℂ (Fin a × Fin b)) :
      Proj (P.initialJointMap x) = P.initialJointMap x :=
    congrArg (fun L => L x) hRange
  have hRight : P.initialJointMap.adjoint.comp Proj = P.initialJointMap.adjoint := by
    rw [← hProj, ← ContinuousLinearMap.adjoint_comp, hRange]
  have hRightApply (x : JointWorkspace) :
      P.initialJointMap.adjoint (Proj x) = P.initialJointMap.adjoint x :=
    congrArg (fun L => L x) hRight
  apply toOperator_injective
  simp only [toOperator_compose, MatrixProcess.initialJointOperation,
    toOperator_finiteKrausOperation, Fintype.sum_unique]
  ext x
  simp only [ContinuousLinearMap.comp_apply]
  rw [hRightApply, hLeft]

theorem initialChoiState_supported :
    compose (blockLift (R := Fin a × Fin b) Proj)
      (blockLift (R := Fin a × Fin b) Proj) P.initialChoiState = P.initialChoiState := by
  have hOp : (sandwich Proj).comp P.initialJointOperation = P.initialJointOperation := by
    ext X
    change compose Proj Proj.adjoint (P.initialJointOperation X) = P.initialJointOperation X
    rw [hProj]
    exact initialJointOperation_supported P Proj hProj hRange X
  have hAmp : normalAmplification (R := Fin a × Fin b) (sandwich Proj)
      P.initialChoiState = P.initialChoiState := by
    rw [MatrixProcess.initialChoiState, map_smul, normalAmplification_nuclearChoi, hOp]
  rw [normalAmplification_sandwich, blockLift_adjoint, hProj] at hAmp
  exact hAmp

theorem physicalState_zero_supported :
    compose (blockLift (R := Fin a × Fin b) Proj)
      (blockLift (R := Fin a × Fin b) Proj) (P.represented_physicalState 0 PUnit.unit) =
      P.represented_physicalState 0 PUnit.unit := by
  change compose (blockLift (R := Fin a × Fin b) Proj)
    (blockLift (R := Fin a × Fin b) Proj) P.initialChoiState = P.initialChoiState
  exact initialChoiState_supported P Proj hProj hRange

end PhysicalInitialRange

end QuantumProver.ElegantJointMeasurement.NormalPhysicalOperationalBridge

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped BigOperators Topology ComplexOrder

namespace QuantumProver.ElegantJointMeasurement.NormalPhysicalOperationalBridge

open QuantumProver.ElegantJointMeasurement.NormalProcess QuantumProver.ElegantJointMeasurement.HilbertSquareProcess QuantumProver.ElegantJointMeasurement.HilbertRecordCoding
open QuantumProver.ElegantJointMeasurement.NormalPhysicalAdmission QuantumProver.ElegantJointMeasurement.HilbertChoi QuantumProver.ElegantJointMeasurement.NuclearChoi
open QuantumProver.ElegantJointMeasurement.NormalInstrumentAbsorption QuantumProver.ElegantJointMeasurement.NormalSandwich
open QuantumProver.ElegantJointMeasurement.SeparableHilbertEmbedding QuantumProver.ElegantJointMeasurement.MeasurableHilbertField
open QuantumProver.HilbertNuclearCompression QuantumProver.MatrixNuclearTensor
open QuantumProver.MatrixNormalTensorInstrument QuantumProver.MatrixNormalRightTensor
open QuantumProver.MatrixNormalSourceCompletion

universe u v w

variable (Ω : ℕ → Type u) [∀ n, MeasurableSpace (Ω n)]
  [∀ n, StandardBorelSpace (Ω n)]
  (D : PhysicalDomains Ω)
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
  (PA : PhysicalLocalFamily Ω D true FA QA)
  (PB : PhysicalLocalFamily Ω D false FB QB)
  {a b : ℕ} [NeZero a] [NeZero b]
  (JA : EuclideanSpace ℂ (Fin a) →ₗᵢ[ℂ] EA 0 D.initialHistory)
  (JB : EuclideanSpace ℂ (Fin b) →ₗᵢ[ℂ] EB 0 D.initialHistory)

local notation "N" => ofPhysicalFamilies Ω D FA FB QA QB WA WB PA PB JA JB

def chosenJointProjection (n : ℕ) (h : D.admissible n) :
    JointWorkspace →L[ℂ] JointWorkspace :=
  physicalJointProjection (selectedMemory Ω D true FA QA WA n).family
    (selectedMemory Ω D false FB QB WB n).family h

def chosenJointRecover (n : ℕ) (h : D.admissible n) :
    Nuclear JointWorkspace →L[ℂ] Nuclear (Joint (EA n h) (EB n h)) :=
  physicalStateRecover (selectedMemory Ω D true FA QA WA n).family
    (selectedMemory Ω D false FB QB WB n).family h

def chosenJointCode (n : ℕ) (h : D.admissible n) :
    Nuclear (Joint (EA n h) (EB n h)) →L[ℂ] Nuclear JointWorkspace :=
  physicalStateCode (selectedMemory Ω D true FA QA WA n).family
    (selectedMemory Ω D false FB QB WB n).family h

theorem chosenJointCode_eq_physicalJointCode (n : ℕ) (h : D.admissible n) :
    chosenJointCode Ω D FA FB QA QB WA WB n h =
      physicalJointCode
        ((selectedMemory Ω D true FA QA WA n).family.embedding h)
        ((selectedMemory Ω D false FB QB WB n).family.embedding h) := by
  simp only [chosenJointCode, physicalStateCode, sandwich, physicalJointCode, tensorMap_adjoint]

def physicalRawAliceJointEvent (n : ℕ) (h : D.actingDomain n true)
    (s : Set (CommonRecord Ω)) :
    Nuclear (Joint (EA n (D.actingHistory n true h))
      (EB n (D.actingHistory n true h))) →L[ℂ] Nuclear JointWorkspace :=
  (rightSourceCode (E := EB n) (V := CommonHilbert) Ω n (D.admissible n)
    (selectedMemory Ω D false FB QB WB n).family (D.actingHistory n true h)).comp
      (tensorOperation (F := EA n (D.actingHistory n true h)) (E := CommonHilbert)
        (G := EB n (D.actingHistory n true h))
        (physicalPhysicalMemoryTurn Ω D true FA QA PA n h) () (encodeOutcome Ω n ⁻¹' s))

def physicalRawBobJointEvent (n : ℕ) (h : D.actingDomain n false)
    (s : Set (CommonRecord Ω)) :
    Nuclear (Joint (EA n (D.actingHistory n false h))
      (EB n (D.actingHistory n false h))) →L[ℂ] Nuclear JointWorkspace :=
  (leftSourceCode (E := EA n) (V := CommonHilbert) Ω n (D.admissible n)
    (selectedMemory Ω D true FA QA WA n).family (D.actingHistory n false h)).comp
      (rightTensorOperation (F := EB n (D.actingHistory n false h)) (E := CommonHilbert)
        (G := EA n (D.actingHistory n false h))
        (physicalPhysicalMemoryTurn Ω D false FB QB PB n h) () (encodeOutcome Ω n ⁻¹' s))

theorem physical_initialJointMap :
    (N).initialJointMap =
      (tensorMap ((FA 0).embedding D.initialHistory).toContinuousLinearMap
        ((FB 0).embedding D.initialHistory).toContinuousLinearMap).comp
        ((tensorMap JA.toContinuousLinearMap JB.toContinuousLinearMap).comp
          (finiteTensorEmbedding (Fin a) (Fin b)).toContinuousLinearMap) := by
  change (tensorMap
    (((FA 0).embedding D.initialHistory).toContinuousLinearMap.comp JA.toContinuousLinearMap)
    (((FB 0).embedding D.initialHistory).toContinuousLinearMap.comp JB.toContinuousLinearMap)).comp
      (finiteTensorEmbedding (Fin a) (Fin b)).toContinuousLinearMap = _
  rw [tensorMap_comp]
  ext x
  rfl

theorem physical_initialJointMap_range :
    (chosenJointProjection Ω D FA FB QA QB WA WB 0 D.initialHistory).comp
      (N).initialJointMap = (N).initialJointMap := by
  rw [physical_initialJointMap]
  ext x
  exact physicalJointProjection_embedding (FA 0) (FB 0) D.initialHistory
    (tensorMap JA.toContinuousLinearMap JB.toContinuousLinearMap
      ((finiteTensorEmbedding (Fin a) (Fin b)).toContinuousLinearMap x))

theorem physical_physicalState_zero_supported :
    compose (blockLift (R := Fin a × Fin b)
      (chosenJointProjection Ω D FA FB QA QB WA WB 0 D.initialHistory))
      (blockLift (R := Fin a × Fin b)
        (chosenJointProjection Ω D FA FB QA QB WA WB 0 D.initialHistory))
      ((N).represented_physicalState 0 PUnit.unit) = (N).represented_physicalState 0 PUnit.unit := by
  apply physicalState_zero_supported N
    (chosenJointProjection Ω D FA FB QA QB WA WB 0 D.initialHistory)
  · exact physicalJointProjection_adjoint (FA 0) (FB 0) D.initialHistory
  · exact physical_initialJointMap_range Ω D FA FB QA QB WA WB PA PB JA JB

theorem physical_physicalStep_alice_event (n : ℕ) (h : D.actingDomain n true)
    (s : Set (CommonRecord Ω)) (hs : MeasurableSet s) (U : Nuclear JointWorkspace)
    (hU : compose (chosenJointProjection Ω D FA FB QA QB WA WB n (D.actingHistory n true h))
      (chosenJointProjection Ω D FA FB QA QB WA WB n (D.actingHistory n true h)) U = U) :
    ((N).represented_physicalStepInstrument n).operation (encodeHistory Ω n h.val) s U =
      physicalRawAliceJointEvent Ω D FA FB QA QB WB PA n h s
        (chosenJointRecover Ω D FA FB QA QB WA WB n (D.actingHistory n true h) U) := by
  have hp := ofPhysicalFamilies_party Ω D FA FB QA QB WA WB PA PB JA JB n
    (D.actingHistory n true h)
  rw [D.party_actingHistory n true h] at hp
  change (N).aliceTurn n (encodeHistory Ω n h.val) = true at hp
  change (if (N).aliceTurn n (encodeHistory Ω n h.val) = true then
    ((N).physicalAliceInstrument n).operation (encodeHistory Ω n h.val) s else
    ((N).physicalBobInstrument n).operation (encodeHistory Ω n h.val) s) U = _
  rw [if_pos hp]
  change tensorOperation (admittedMemoryTurn Ω D true FA QA WA PA n)
    (encodeHistory Ω n h.val) s U = _
  have hr := physicalState_retraction
    (selectedMemory Ω D true FA QA WA n).family
    (selectedMemory Ω D false FB QB WB n).family (D.actingHistory n true h) U hU
  simp only [physicalStateCode, sandwich, tensorMap_adjoint] at hr
  change physicalJointCode
    ((selectedMemory Ω D true FA QA WA n).family.embedding (D.actingHistory n true h))
    ((selectedMemory Ω D false FB QB WB n).family.embedding (D.actingHistory n true h))
    (chosenJointRecover Ω D FA FB QA QB WA WB n (D.actingHistory n true h) U) = U at hr
  have hi := congrArg (fun L => L
    (chosenJointRecover Ω D FA FB QA QB WA WB n (D.actingHistory n true h) U))
    (physicalAlice_joint_transition Ω D FA FB QA QB WA WB PA n h s hs)
  simp only [ContinuousLinearMap.comp_apply] at hi
  rw [hr] at hi
  exact hi

theorem physical_physicalStep_bob_event (n : ℕ) (h : D.actingDomain n false)
    (s : Set (CommonRecord Ω)) (hs : MeasurableSet s) (U : Nuclear JointWorkspace)
    (hU : compose (chosenJointProjection Ω D FA FB QA QB WA WB n (D.actingHistory n false h))
      (chosenJointProjection Ω D FA FB QA QB WA WB n (D.actingHistory n false h)) U = U) :
    ((N).represented_physicalStepInstrument n).operation (encodeHistory Ω n h.val) s U =
      physicalRawBobJointEvent Ω D FA FB QA QB WA PB n h s
        (chosenJointRecover Ω D FA FB QA QB WA WB n (D.actingHistory n false h) U) := by
  have hp := ofPhysicalFamilies_party Ω D FA FB QA QB WA WB PA PB JA JB n
    (D.actingHistory n false h)
  rw [D.party_actingHistory n false h] at hp
  change (N).aliceTurn n (encodeHistory Ω n h.val) = false at hp
  change (if (N).aliceTurn n (encodeHistory Ω n h.val) = true then
    ((N).physicalAliceInstrument n).operation (encodeHistory Ω n h.val) s else
    ((N).physicalBobInstrument n).operation (encodeHistory Ω n h.val) s) U = _
  rw [if_neg (by simp [hp])]
  change rightTensorOperation (admittedMemoryTurn Ω D false FB QB WB PB n)
    (encodeHistory Ω n h.val) s U = _
  have hr := physicalState_retraction
    (selectedMemory Ω D true FA QA WA n).family
    (selectedMemory Ω D false FB QB WB n).family (D.actingHistory n false h) U hU
  simp only [physicalStateCode, sandwich, tensorMap_adjoint] at hr
  change physicalJointCode
    ((selectedMemory Ω D true FA QA WA n).family.embedding (D.actingHistory n false h))
    ((selectedMemory Ω D false FB QB WB n).family.embedding (D.actingHistory n false h))
    (chosenJointRecover Ω D FA FB QA QB WA WB n (D.actingHistory n false h) U) = U at hr
  have hi := congrArg (fun L => L
    (chosenJointRecover Ω D FA FB QA QB WA WB n (D.actingHistory n false h) U))
    (physicalBob_joint_transition Ω D FA FB QA QB WA WB PB n h s hs)
  simp only [ContinuousLinearMap.comp_apply] at hi
  rw [hr] at hi
  exact hi

theorem physical_physicalReference_alice_event (n : ℕ) (h : D.actingDomain n true)
    (s : Set (CommonRecord Ω)) (hs : MeasurableSet s)
    (U : Nuclear (PhysicalChoiWorkspace a b))
    (hU : compose (blockLift (R := Fin a × Fin b)
      (chosenJointProjection Ω D FA FB QA QB WA WB n (D.actingHistory n true h)))
      (blockLift (R := Fin a × Fin b)
        (chosenJointProjection Ω D FA FB QA QB WA WB n (D.actingHistory n true h))) U = U) :
    ((N).represented_physicalReferenceInstrument n).operation (encodeHistory Ω n h.val) s U =
      normalAmplification (R := Fin a × Fin b)
        (physicalRawAliceJointEvent Ω D FA FB QA QB WB PA n h s)
        (normalAmplification (R := Fin a × Fin b)
          (chosenJointRecover Ω D FA FB QA QB WA WB n (D.actingHistory n true h)) U) := by
  have hp := ofPhysicalFamilies_party Ω D FA FB QA QB WA WB PA PB JA JB n
    (D.actingHistory n true h)
  rw [D.party_actingHistory n true h] at hp
  change (N).aliceTurn n (encodeHistory Ω n h.val) = true at hp
  change normalAmplification (R := Fin a × Fin b)
    (((N).represented_physicalStepInstrument n).operation (encodeHistory Ω n h.val) s) U = _
  change normalAmplification (R := Fin a × Fin b)
    (if (N).aliceTurn n (encodeHistory Ω n h.val) = true then
    ((N).physicalAliceInstrument n).operation (encodeHistory Ω n h.val) s else
    ((N).physicalBobInstrument n).operation (encodeHistory Ω n h.val) s) U = _
  rw [if_pos hp]
  change normalAmplification (R := Fin a × Fin b)
    (tensorOperation (admittedMemoryTurn Ω D true FA QA WA PA n)
      (encodeHistory Ω n h.val) s) U = _
  have hr := physicalState_retraction_amplified
    (selectedMemory Ω D true FA QA WA n).family
    (selectedMemory Ω D false FB QB WB n).family (D.actingHistory n true h) U hU
  simp only [physicalStateCode, sandwich, tensorMap_adjoint] at hr
  change normalAmplification (R := Fin a × Fin b) (physicalJointCode
    ((selectedMemory Ω D true FA QA WA n).family.embedding (D.actingHistory n true h))
    ((selectedMemory Ω D false FB QB WB n).family.embedding (D.actingHistory n true h)))
    (normalAmplification (R := Fin a × Fin b)
      (chosenJointRecover Ω D FA FB QA QB WA WB n (D.actingHistory n true h)) U) = U at hr
  have hi := congrArg (fun L => normalAmplification (R := Fin a × Fin b) L
    (normalAmplification (R := Fin a × Fin b)
      (chosenJointRecover Ω D FA FB QA QB WA WB n (D.actingHistory n true h)) U))
    (physicalAlice_joint_transition Ω D FA FB QA QB WA WB PA n h s hs)
  have hLeft : normalAmplification (R := Fin a × Fin b)
      ((tensorOperation (admittedMemoryTurn Ω D true FA QA WA PA n)
        (encodeHistory Ω n h.val) s).comp (physicalJointCode
          ((selectedMemory Ω D true FA QA WA n).family.embedding (D.actingHistory n true h))
          ((selectedMemory Ω D false FB QB WB n).family.embedding (D.actingHistory n true h))))
      (normalAmplification (R := Fin a × Fin b)
        (chosenJointRecover Ω D FA FB QA QB WA WB n (D.actingHistory n true h)) U) =
      normalAmplification (R := Fin a × Fin b)
        (tensorOperation (admittedMemoryTurn Ω D true FA QA WA PA n)
          (encodeHistory Ω n h.val) s) U := by
    rw [normalAmplification_comp, hr]
  exact hLeft.symm.trans hi

theorem physical_physicalReference_bob_event (n : ℕ) (h : D.actingDomain n false)
    (s : Set (CommonRecord Ω)) (hs : MeasurableSet s)
    (U : Nuclear (PhysicalChoiWorkspace a b))
    (hU : compose (blockLift (R := Fin a × Fin b)
      (chosenJointProjection Ω D FA FB QA QB WA WB n (D.actingHistory n false h)))
      (blockLift (R := Fin a × Fin b)
        (chosenJointProjection Ω D FA FB QA QB WA WB n (D.actingHistory n false h))) U = U) :
    ((N).represented_physicalReferenceInstrument n).operation (encodeHistory Ω n h.val) s U =
      normalAmplification (R := Fin a × Fin b)
        (physicalRawBobJointEvent Ω D FA FB QA QB WA PB n h s)
        (normalAmplification (R := Fin a × Fin b)
          (chosenJointRecover Ω D FA FB QA QB WA WB n (D.actingHistory n false h)) U) := by
  have hp := ofPhysicalFamilies_party Ω D FA FB QA QB WA WB PA PB JA JB n
    (D.actingHistory n false h)
  rw [D.party_actingHistory n false h] at hp
  change (N).aliceTurn n (encodeHistory Ω n h.val) = false at hp
  change normalAmplification (R := Fin a × Fin b)
    (((N).represented_physicalStepInstrument n).operation (encodeHistory Ω n h.val) s) U = _
  change normalAmplification (R := Fin a × Fin b)
    (if (N).aliceTurn n (encodeHistory Ω n h.val) = true then
    ((N).physicalAliceInstrument n).operation (encodeHistory Ω n h.val) s else
    ((N).physicalBobInstrument n).operation (encodeHistory Ω n h.val) s) U = _
  rw [if_neg (by simp [hp])]
  change normalAmplification (R := Fin a × Fin b)
    (rightTensorOperation (admittedMemoryTurn Ω D false FB QB WB PB n)
      (encodeHistory Ω n h.val) s) U = _
  have hr := physicalState_retraction_amplified
    (selectedMemory Ω D true FA QA WA n).family
    (selectedMemory Ω D false FB QB WB n).family (D.actingHistory n false h) U hU
  simp only [physicalStateCode, sandwich, tensorMap_adjoint] at hr
  change normalAmplification (R := Fin a × Fin b) (physicalJointCode
    ((selectedMemory Ω D true FA QA WA n).family.embedding (D.actingHistory n false h))
    ((selectedMemory Ω D false FB QB WB n).family.embedding (D.actingHistory n false h)))
    (normalAmplification (R := Fin a × Fin b)
      (chosenJointRecover Ω D FA FB QA QB WA WB n (D.actingHistory n false h)) U) = U at hr
  have hi := congrArg (fun L => normalAmplification (R := Fin a × Fin b) L
    (normalAmplification (R := Fin a × Fin b)
      (chosenJointRecover Ω D FA FB QA QB WA WB n (D.actingHistory n false h)) U))
    (physicalBob_joint_transition Ω D FA FB QA QB WA WB PB n h s hs)
  have hLeft : normalAmplification (R := Fin a × Fin b)
      ((rightTensorOperation (admittedMemoryTurn Ω D false FB QB WB PB n)
        (encodeHistory Ω n h.val) s).comp (physicalJointCode
          ((selectedMemory Ω D true FA QA WA n).family.embedding (D.actingHistory n false h))
          ((selectedMemory Ω D false FB QB WB n).family.embedding (D.actingHistory n false h))))
      (normalAmplification (R := Fin a × Fin b)
        (chosenJointRecover Ω D FA FB QA QB WA WB n (D.actingHistory n false h)) U) =
      normalAmplification (R := Fin a × Fin b)
        (rightTensorOperation (admittedMemoryTurn Ω D false FB QB WB PB n)
          (encodeHistory Ω n h.val) s) U := by
    rw [normalAmplification_comp, hr]
  exact hLeft.symm.trans hi

end QuantumProver.ElegantJointMeasurement.NormalPhysicalOperationalBridge

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000

open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped BigOperators Topology ComplexOrder

namespace QuantumProver.ElegantJointMeasurement.NormalPhysicalOperationalBridge

open QuantumProver.ElegantJointMeasurement.HilbertChoi QuantumProver.ElegantJointMeasurement.NuclearChoi QuantumProver.ElegantJointMeasurement.NormalProcess
open QuantumProver.ElegantJointMeasurement.NormalInstrumentAbsorption QuantumProver.ElegantJointMeasurement.NormalRecordedAbsorption
open QuantumProver.ElegantJointMeasurement.SeparableHilbertEmbedding QuantumProver.ElegantJointMeasurement.MeasurableHilbertField
open QuantumProver.ElegantJointMeasurement.NormalControlledSpectatorLift
open QuantumProver.HilbertNuclearCompression QuantumProver.MatrixNuclearTensor
open QuantumProver.MatrixNormalTensorInstrument QuantumProver.MatrixNormalRightTensor
open QuantumProver.MatrixNormalAmplifiedInstrument QuantumProver.MatrixNormalStateKernel
open QuantumProver.NuclearOperator (toOperator)

variable {H Ω V : Type*} [MeasurableSpace H] [MeasurableSpace Ω]
  [MeasurableSpace.CountableOrCountablyGenerated H Ω]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V] [SeparableSpace V]
  {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]
  {G : H × Ω → Type*}
  [∀ z, NormedAddCommGroup (G z)] [∀ z, InnerProductSpace ℂ (G z)]
  [∀ z, CompleteSpace (G z)]
  (Q : FundamentalFamily G) (P : RecordedNormalInstrument CommonHilbert Q)

local instance posteriorBlockComplete {W : Type*} [NormedAddCommGroup W]
    [InnerProductSpace ℂ W] [CompleteSpace W] : CompleteSpace (BlockSpace I W) :=
  PiLp.completeSpace 2 (fun _ : I => W)

local instance leftPosteriorJointSeparable : SeparableSpace (Joint CommonHilbert V) :=
  QuantumProver.ElegantJointMeasurement.NormalAncillaPreparation.separableSpace_joint

local instance rightPosteriorJointSeparable : SeparableSpace (Joint V CommonHilbert) :=
  QuantumProver.ElegantJointMeasurement.NormalAncillaPreparation.separableSpace_joint

local instance leftPosteriorSpaceSeparable : SeparableSpace (BlockSpace I (Joint CommonHilbert V)) := by
  change SeparableSpace (PiLp 2 (fun _ : I => Joint CommonHilbert V))
  infer_instance

local instance rightPosteriorSpaceSeparable : SeparableSpace (BlockSpace I (Joint V CommonHilbert)) := by
  change SeparableSpace (PiLp 2 (fun _ : I => Joint V CommonHilbert))
  infer_instance

def physicalLeftReferenceInstrument :
    Instrument (BlockSpace I (Joint CommonHilbert V))
      (BlockSpace I (Joint CommonHilbert V)) H Ω :=
  amplifiedInstrument I (tensorInstrument (G := V) P.represented_physical)

def physicalRightReferenceInstrument :
    Instrument (BlockSpace I (Joint V CommonHilbert))
      (BlockSpace I (Joint V CommonHilbert)) H Ω :=
  amplifiedInstrument I (rightTensorInstrument (G := V) P.represented_physical)

section LeftPosterior

variable (σ : H → Nuclear (BlockSpace I (Joint CommonHilbert V)))
  (hpos : ∀ h, (toOperator (σ h)).IsPositive)
  (hstrong : StronglyMeasurable σ)
  (htrace : ∀ h, QuantumProver.HilbertNuclearTrace.trace (σ h) = 1)
  (h : H) (R : V →L[ℂ] V) (hR : R.adjoint = R)
  (hRemote : compose (remoteLift (I := I) (E := CommonHilbert) R)
    (remoteLift (I := I) (E := CommonHilbert) R) (σ h) = σ h)

include hR hRemote

theorem physicalLeftPosterior_ae_supported :
    ∀ᵐ ω ∂bornKernel (physicalLeftReferenceInstrument (I := I) (V := V) Q P)
      σ hpos hstrong htrace h,
      compose (blockLift (R := I) (tensorMap (Q.rangeProjection (h,ω)) R))
        (blockLift (R := I) (tensorMap (Q.rangeProjection (h,ω)) R))
        (posterior (physicalLeftReferenceInstrument (I := I) (V := V) Q P)
          σ hpos hstrong htrace (h,ω)) =
        posterior (physicalLeftReferenceInstrument (I := I) (V := V) Q P)
          σ hpos hstrong htrace (h,ω) := by
  apply left_density_combined_supported Q P h R hR (σ h) (hpos h) hRemote
    (bornKernel (physicalLeftReferenceInstrument (I := I) (V := V) Q P)
      σ hpos hstrong htrace h)
    (fun ω => posterior (physicalLeftReferenceInstrument (I := I) (V := V) Q P)
      σ hpos hstrong htrace (h,ω))
  · exact integrable_posterior _ σ hpos hstrong htrace h
  · exact ae_of_all _ fun ω => posterior_isPositive _ σ hpos hstrong htrace h ω
  · intro s hs
    exact setIntegral_posterior _ σ hpos hstrong htrace h s hs

end LeftPosterior

section RightPosterior

variable (σ : H → Nuclear (BlockSpace I (Joint V CommonHilbert)))
  (hpos : ∀ h, (toOperator (σ h)).IsPositive)
  (hstrong : StronglyMeasurable σ)
  (htrace : ∀ h, QuantumProver.HilbertNuclearTrace.trace (σ h) = 1)
  (h : H) (R : V →L[ℂ] V) (hR : R.adjoint = R)
  (hRemote : compose (localLift (I := I) (V := CommonHilbert) R)
    (localLift (I := I) (V := CommonHilbert) R) (σ h) = σ h)

include hR hRemote

theorem physicalRightPosterior_ae_supported :
    ∀ᵐ ω ∂bornKernel (physicalRightReferenceInstrument (I := I) (V := V) Q P)
      σ hpos hstrong htrace h,
      compose (blockLift (R := I) (tensorMap R (Q.rangeProjection (h,ω))))
        (blockLift (R := I) (tensorMap R (Q.rangeProjection (h,ω))))
        (posterior (physicalRightReferenceInstrument (I := I) (V := V) Q P)
          σ hpos hstrong htrace (h,ω)) =
        posterior (physicalRightReferenceInstrument (I := I) (V := V) Q P)
          σ hpos hstrong htrace (h,ω) := by
  apply right_density_combined_supported Q P h R hR (σ h) (hpos h) hRemote
    (bornKernel (physicalRightReferenceInstrument (I := I) (V := V) Q P)
      σ hpos hstrong htrace h)
    (fun ω => posterior (physicalRightReferenceInstrument (I := I) (V := V) Q P)
      σ hpos hstrong htrace (h,ω))
  · exact integrable_posterior _ σ hpos hstrong htrace h
  · exact ae_of_all _ fun ω => posterior_isPositive _ σ hpos hstrong htrace h ω
  · intro s hs
    exact setIntegral_posterior _ σ hpos hstrong htrace h s hs

end RightPosterior

end QuantumProver.ElegantJointMeasurement.NormalPhysicalOperationalBridge

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000

open MeasureTheory ProbabilityTheory Set Filter Function InnerProductSpace TopologicalSpace
open scoped BigOperators Topology ComplexOrder

namespace QuantumProver.ElegantJointMeasurement.NormalPhysicalOperationalBridge

open QuantumProver.ElegantJointMeasurement.NormalProcess QuantumProver.ElegantJointMeasurement.HilbertSquareProcess QuantumProver.ElegantJointMeasurement.HilbertRecordCoding
open QuantumProver.ElegantJointMeasurement.NormalPhysicalAdmission QuantumProver.ElegantJointMeasurement.HilbertChoi QuantumProver.ElegantJointMeasurement.NuclearChoi
open QuantumProver.ElegantJointMeasurement.NormalInstrumentAbsorption QuantumProver.ElegantJointMeasurement.NormalSandwich
open QuantumProver.ElegantJointMeasurement.SeparableHilbertEmbedding QuantumProver.ElegantJointMeasurement.MeasurableHilbertField
open QuantumProver.HilbertNuclearCompression QuantumProver.MatrixNuclearTensor
open QuantumProver.MatrixNormalTensorInstrument QuantumProver.MatrixNormalRightTensor
open QuantumProver.MatrixNormalSourceCompletion QuantumProver.MatrixNormalStateKernel
open QuantumProver.NuclearOperator (toOperator)

section LiteralTensorEvent

variable {E F V H K X Y : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  [MeasurableSpace H] [MeasurableSpace K] [MeasurableSpace X] [MeasurableSpace Y]

theorem tensorOperation_congr_event (P : Instrument F E H X) (Q : Instrument F E K Y)
    (h : H) (k : K) (s : Set X) (t : Set Y)
    (hs : MeasurableSet s) (ht : MeasurableSet t)
    (he : P.operation h s = Q.operation k t) :
    tensorOperation (G := V) P h s = tensorOperation (G := V) Q k t := by
  apply nuclear_joint_clm_ext_tensors
  intro T U
  rw [tensorOperation_tensor P h s hs, tensorOperation_tensor Q k t ht, he]

theorem rightTensorOperation_congr_event (P : Instrument F E H X) (Q : Instrument F E K Y)
    (h : H) (k : K) (s : Set X) (t : Set Y)
    (hs : MeasurableSet s) (ht : MeasurableSet t)
    (he : P.operation h s = Q.operation k t) :
    rightTensorOperation (G := V) P h s = rightTensorOperation (G := V) Q k t := by
  apply nuclear_joint_clm_ext_tensors
  intro T U
  rw [rightTensorOperation_tensor P h s hs, rightTensorOperation_tensor Q k t ht, he]

theorem tensorOperation_zero_event (P : Instrument F E H X)
    (h : H) (s : Set X) (hs : MeasurableSet s) (he : P.operation h s = 0) :
    tensorOperation (G := V) P h s = 0 := by
  apply nuclear_joint_clm_ext_tensors
  intro T U
  rw [tensorOperation_tensor P h s hs, he]
  simp only [ContinuousLinearMap.zero_apply, map_zero]

theorem rightTensorOperation_zero_event (P : Instrument F E H X)
    (h : H) (s : Set X) (hs : MeasurableSet s) (he : P.operation h s = 0) :
    rightTensorOperation (G := V) P h s = 0 := by
  apply nuclear_joint_clm_ext_tensors
  intro T U
  rw [rightTensorOperation_tensor P h s hs, he]
  simp only [ContinuousLinearMap.zero_apply, map_zero]

end LiteralTensorEvent

universe u v w

variable (Ω : ℕ → Type u) [∀ n, MeasurableSpace (Ω n)]
  [∀ n, StandardBorelSpace (Ω n)]

theorem completedOutcome_injective (n : ℕ) : Injective (completedOutcome Ω n) := by
  intro z z' he
  cases z with
  | inl x =>
      cases z' with
      | inl y => exact congrArg Sum.inl (encodeOutcome_injective Ω n he)
      | inr y => simp [completedOutcome, encodeOutcome, dummyRecord] at he
  | inr x =>
      cases z' with
      | inl y => simp [completedOutcome, encodeOutcome, dummyRecord] at he
      | inr y => exact congrArg Sum.inr (Subsingleton.elim x y)

theorem measurableEmbedding_completedOutcome (n : ℕ) :
    MeasurableEmbedding (completedOutcome Ω n) := by
  classical
  refine ⟨completedOutcome_injective Ω n, measurable_completedOutcome Ω n, ?_⟩
  intro s hs
  have hImage : completedOutcome Ω n '' s =
      encodeOutcome Ω n '' (Sum.inl ⁻¹' s) ∪
        (if Sum.inr () ∈ s then {dummyRecord Ω} else ∅) := by
    ext r
    constructor
    · rintro ⟨ω,hω,rfl⟩
      cases ω with
      | inl x => exact Or.inl ⟨x,hω,rfl⟩
      | inr x =>
          cases x
          exact Or.inr (by simp only [if_pos hω, completedOutcome, mem_singleton_iff])
    · rintro (⟨x,hx,rfl⟩ | hr)
      · exact ⟨Sum.inl x,hx,rfl⟩
      · by_cases hd : Sum.inr () ∈ s
        · have he : r = dummyRecord Ω := by simpa only [if_pos hd,mem_singleton_iff] using hr
          exact ⟨Sum.inr (),hd,he.symm⟩
        · simp only [if_neg hd,mem_empty_iff_false] at hr
  rw [hImage]
  refine ((measurableEmbedding_encodeOutcome Ω n).measurableSet_image' (measurable_inl hs)).union ?_
  split
  · exact MeasurableSet.singleton _
  · exact MeasurableSet.empty

instance completedOutcome_countablyGenerated (n : ℕ) :
    MeasurableSpace.CountablyGenerated (Ω n ⊕ Unit) := by
  have hc := MeasurableSpace.CountablyGenerated.comap (completedOutcome Ω n)
  rw [(measurableEmbedding_completedOutcome Ω n).comap_eq] at hc
  exact hc

instance physicalAdmissible_standardBorel (D : PhysicalDomains Ω) (n : ℕ) :
    StandardBorelSpace (D.admissible n) := (D.admissible_measurable n).standardBorel

instance physicalActingDomain_standardBorel (D : PhysicalDomains Ω) (n : ℕ) (c : Bool) :
    StandardBorelSpace (D.actingDomain n c) := (D.measurableSet_actingDomain n c).standardBorel

section ConcretePhysicalInvariant

variable (D : PhysicalDomains Ω)
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
  (PA : PhysicalLocalFamily Ω D true FA QA)
  (PB : PhysicalLocalFamily Ω D false FB QB)
  {a b : ℕ} [NeZero a] [NeZero b]
  (JA : EuclideanSpace ℂ (Fin a) →ₗᵢ[ℂ] EA 0 D.initialHistory)
  (JB : EuclideanSpace ℂ (Fin b) →ₗᵢ[ℂ] EB 0 D.initialHistory)

local notation "N" => ofPhysicalFamilies Ω D FA FB QA QB WA WB PA PB JA JB
local notation "CA" n => IntrinsicFamily.family (selectedMemory Ω D true FA QA WA n)
local notation "CB" n => IntrinsicFamily.family (selectedMemory Ω D false FB QB WB n)

def physicallySupportedHistory (n : ℕ) : Set (D.admissible n) :=
  {h | compose (blockLift (R := Fin a × Fin b) (physicalJointProjection (CA n) (CB n) h))
    (blockLift (R := Fin a × Fin b) (physicalJointProjection (CA n) (CB n) h))
    ((N).represented_physicalState n (encodeHistory Ω n h.val)) =
      (N).represented_physicalState n (encodeHistory Ω n h.val)}

theorem measurableSet_physicallySupportedHistory (n : ℕ) :
    MeasurableSet (physicallySupportedHistory Ω D FA FB QA QB WA WB PA PB JA JB n) := by
  apply measurableSet_physicalState_reference_supported (CA n) (CB n)
  exact ((N).stronglyMeasurable_physicalState n).comp_measurable
    ((measurable_encodeHistory Ω n).comp measurable_subtype_coe)

def encodedPhysicallySupportedHistory (n : ℕ) : Set (History (CommonRecord Ω) n) :=
  (fun h : D.admissible n => encodeHistory Ω n h.val) ''
    physicallySupportedHistory Ω D FA FB QA QB WA WB PA PB JA JB n

theorem measurableSet_encodedPhysicallySupportedHistory (n : ℕ) :
    MeasurableSet (encodedPhysicallySupportedHistory Ω D FA FB QA QB WA WB PA PB JA JB n) :=
  (measurableEmbedding_encodeAdmissibleHistory Ω n (D.admissible n)
    (D.admissible_measurable n)).measurableSet_image'
      (measurableSet_physicallySupportedHistory Ω D FA FB QA QB WA WB PA PB JA JB n)

theorem encodedPhysicallySupportedHistory_zero :
    PUnit.unit ∈ encodedPhysicallySupportedHistory Ω D FA FB QA QB WA WB PA PB JA JB 0 := by
  refine ⟨D.initialHistory, ?_, rfl⟩
  exact physical_physicalState_zero_supported Ω D FA FB QA QB WA WB PA PB JA JB

def admittedActiveState (c : Bool) (n : ℕ) (h : D.actingDomain n c) :
    Nuclear (PhysicalChoiWorkspace a b) := (N).represented_physicalState n (encodeHistory Ω n h.val)

theorem admittedActiveState_positive (c : Bool) (n : ℕ) (h : D.actingDomain n c) :
    (toOperator (admittedActiveState Ω D FA FB QA QB WA WB PA PB JA JB c n h)).IsPositive :=
  (N).physicalState_isPositive n _

theorem stronglyMeasurable_admittedActiveState (c : Bool) (n : ℕ) :
    StronglyMeasurable (admittedActiveState Ω D FA FB QA QB WA WB PA PB JA JB c n) :=
  ((N).stronglyMeasurable_physicalState n).comp_measurable
    ((measurable_encodeHistory Ω n).comp measurable_subtype_coe)

theorem admittedActiveState_trace (c : Bool) (n : ℕ) (h : D.actingDomain n c) :
    QuantumProver.HilbertNuclearTrace.trace
      (admittedActiveState Ω D FA FB QA QB WA WB PA PB JA JB c n h) = 1 :=
  (N).physicalState_trace n _

def physicalAliceCompletedReferenceInstrument (n : ℕ) :
    Instrument (PhysicalChoiWorkspace a b) (PhysicalChoiWorkspace a b)
      (D.actingDomain n true) (Ω n ⊕ Unit) :=
  physicalLeftReferenceInstrument (I := Fin a × Fin b) (V := CommonHilbert)
    (taggedOutputFamily (QA n)) (admittedRecordedMemoryTurn Ω D true FA QA WA PA n)

def physicalBobCompletedReferenceInstrument (n : ℕ) :
    Instrument (PhysicalChoiWorkspace a b) (PhysicalChoiWorkspace a b)
      (D.actingDomain n false) (Ω n ⊕ Unit) :=
  physicalRightReferenceInstrument (I := Fin a × Fin b) (V := CommonHilbert)
    (taggedOutputFamily (QB n)) (admittedRecordedMemoryTurn Ω D false FB QB WB PB n)

theorem physicalAliceCompletedReferenceInstrument_event (n : ℕ)
    (h : D.actingDomain n true) (s : Set (CommonRecord Ω)) (hs : MeasurableSet s) :
    ((N).represented_physicalReferenceInstrument n).operation (encodeHistory Ω n h.val) s =
      (physicalAliceCompletedReferenceInstrument Ω D FA QA WA PA (a := a) (b := b) n).operation h
        (completedOutcome Ω n ⁻¹' s) := by
  have hp : (N).aliceTurn n (encodeHistory Ω n h.val) = true :=
    (ofPhysicalFamilies_party Ω D FA FB QA QB WA WB PA PB JA JB n
      (D.actingHistory n true h)).trans (D.party_actingHistory n true h)
  have hstep : ((N).represented_physicalStepInstrument n).operation (encodeHistory Ω n h.val) s =
      tensorOperation (G := CommonHilbert) (admittedMemoryTurn Ω D true FA QA WA PA n)
        (encodeHistory Ω n h.val) s := by
    change (if (N).aliceTurn n (encodeHistory Ω n h.val) = true then _ else _) = _
    rw [if_pos hp]
    rfl
  change normalAmplification (R := Fin a × Fin b)
      (((N).represented_physicalStepInstrument n).operation (encodeHistory Ω n h.val) s) =
    normalAmplification (R := Fin a × Fin b)
      (tensorOperation (G := CommonHilbert)
        (admittedRecordedMemoryTurn Ω D true FA QA WA PA n).represented_physical h
          (completedOutcome Ω n ⁻¹' s))
  rw [hstep]
  apply congrArg (normalAmplification (R := Fin a × Fin b))
  exact tensorOperation_congr_event _ _ _ _ _ _ hs
    ((measurable_completedOutcome Ω n) hs)
    (admittedMemoryTurn_recorded_encoded Ω D true FA QA WA PA n h s)

theorem physicalBobCompletedReferenceInstrument_event (n : ℕ)
    (h : D.actingDomain n false) (s : Set (CommonRecord Ω)) (hs : MeasurableSet s) :
    ((N).represented_physicalReferenceInstrument n).operation (encodeHistory Ω n h.val) s =
      (physicalBobCompletedReferenceInstrument Ω D FB QB WB PB (a := a) (b := b) n).operation h
        (completedOutcome Ω n ⁻¹' s) := by
  have hp : (N).aliceTurn n (encodeHistory Ω n h.val) = false :=
    (ofPhysicalFamilies_party Ω D FA FB QA QB WA WB PA PB JA JB n
      (D.actingHistory n false h)).trans (D.party_actingHistory n false h)
  have hstep : ((N).represented_physicalStepInstrument n).operation (encodeHistory Ω n h.val) s =
      rightTensorOperation (G := CommonHilbert) (admittedMemoryTurn Ω D false FB QB WB PB n)
        (encodeHistory Ω n h.val) s := by
    change (if (N).aliceTurn n (encodeHistory Ω n h.val) = true then _ else _) = _
    rw [hp]
    rfl
  change normalAmplification (R := Fin a × Fin b)
      (((N).represented_physicalStepInstrument n).operation (encodeHistory Ω n h.val) s) =
    normalAmplification (R := Fin a × Fin b)
      (rightTensorOperation (G := CommonHilbert)
        (admittedRecordedMemoryTurn Ω D false FB QB WB PB n).represented_physical h
          (completedOutcome Ω n ⁻¹' s))
  rw [hstep]
  apply congrArg (normalAmplification (R := Fin a × Fin b))
  exact rightTensorOperation_congr_event _ _ _ _ _ _ hs
    ((measurable_completedOutcome Ω n) hs)
    (admittedMemoryTurn_recorded_encoded Ω D false FB QB WB PB n h s)

local notation "σA" n => admittedActiveState Ω D FA FB QA QB WA WB PA PB JA JB true n
local notation "σB" n => admittedActiveState Ω D FA FB QA QB WA WB PA PB JA JB false n
local notation "posA" n => admittedActiveState_positive Ω D FA FB QA QB WA WB PA PB JA JB true n
local notation "posB" n => admittedActiveState_positive Ω D FA FB QA QB WA WB PA PB JA JB false n
local notation "strongA" n => stronglyMeasurable_admittedActiveState Ω D FA FB QA QB WA WB PA PB JA JB true n
local notation "strongB" n => stronglyMeasurable_admittedActiveState Ω D FA FB QA QB WA WB PA PB JA JB false n
local notation "traceA" n => admittedActiveState_trace Ω D FA FB QA QB WA WB PA PB JA JB true n
local notation "traceB" n => admittedActiveState_trace Ω D FA FB QA QB WA WB PA PB JA JB false n
local notation "LA" n => physicalAliceCompletedReferenceInstrument Ω D FA QA WA PA (a := a) (b := b) n
local notation "LB" n => physicalBobCompletedReferenceInstrument Ω D FB QB WB PB (a := a) (b := b) n

theorem physicalAliceCompletedReferenceInstrument_born_map (n : ℕ)
    (h : D.actingDomain n true) :
    (N).represented_physicalBornKernel n (encodeHistory Ω n h.val) =
      (bornKernel (LA n) (σA n) (posA n) (strongA n) (traceA n) h).map
        (completedOutcome Ω n) := by
  apply bornKernel_map_of_physical_events ((N).represented_physicalReferenceInstrument n)
    ((N).represented_physicalState n) ((N).physicalState_isPositive n) ((N).stronglyMeasurable_physicalState n)
    ((N).physicalState_trace n) (LA n) (σA n) (posA n) (strongA n) (traceA n)
    (completedOutcome Ω n) (measurableEmbedding_completedOutcome Ω n)
    (encodeHistory Ω n h.val) h
  intro s hs
  exact congrArg (fun L => L ((σA n) h))
    (physicalAliceCompletedReferenceInstrument_event Ω D FA FB QA QB WA WB PA PB JA JB n h s hs)

theorem physicalBobCompletedReferenceInstrument_born_map (n : ℕ)
    (h : D.actingDomain n false) :
    (N).represented_physicalBornKernel n (encodeHistory Ω n h.val) =
      (bornKernel (LB n) (σB n) (posB n) (strongB n) (traceB n) h).map
        (completedOutcome Ω n) := by
  apply bornKernel_map_of_physical_events ((N).represented_physicalReferenceInstrument n)
    ((N).represented_physicalState n) ((N).physicalState_isPositive n) ((N).stronglyMeasurable_physicalState n)
    ((N).physicalState_trace n) (LB n) (σB n) (posB n) (strongB n) (traceB n)
    (completedOutcome Ω n) (measurableEmbedding_completedOutcome Ω n)
    (encodeHistory Ω n h.val) h
  intro s hs
  exact congrArg (fun L => L ((σB n) h))
    (physicalBobCompletedReferenceInstrument_event Ω D FA FB QA QB WA WB PA PB JA JB n h s hs)

theorem physicalAliceCompletedReferenceInstrument_posterior_ae (n : ℕ)
    (h : D.actingDomain n true) :
    (fun ω => posterior (LA n) (σA n) (posA n) (strongA n) (traceA n) (h,ω))
      =ᵐ[bornKernel (LA n) (σA n) (posA n) (strongA n) (traceA n) h]
        (fun ω => (N).represented_physicalState (n+1)
          (appendHistory n (encodeHistory Ω n h.val,completedOutcome Ω n ω))) := by
  simp_rw [(N).physicalState_successor]
  apply posterior_ae_eq_after_outcomeCoding ((N).represented_physicalReferenceInstrument n)
    ((N).represented_physicalState n) ((N).physicalState_isPositive n) ((N).stronglyMeasurable_physicalState n)
    ((N).physicalState_trace n) (LA n) (σA n) (posA n) (strongA n) (traceA n)
    (completedOutcome Ω n) (measurableEmbedding_completedOutcome Ω n)
    (encodeHistory Ω n h.val) h
  intro s hs
  exact congrArg (fun L => L ((σA n) h))
    (physicalAliceCompletedReferenceInstrument_event Ω D FA FB QA QB WA WB PA PB JA JB n h s hs)

theorem physicalBobCompletedReferenceInstrument_posterior_ae (n : ℕ)
    (h : D.actingDomain n false) :
    (fun ω => posterior (LB n) (σB n) (posB n) (strongB n) (traceB n) (h,ω))
      =ᵐ[bornKernel (LB n) (σB n) (posB n) (strongB n) (traceB n) h]
        (fun ω => (N).represented_physicalState (n+1)
          (appendHistory n (encodeHistory Ω n h.val,completedOutcome Ω n ω))) := by
  simp_rw [(N).physicalState_successor]
  apply posterior_ae_eq_after_outcomeCoding ((N).represented_physicalReferenceInstrument n)
    ((N).represented_physicalState n) ((N).physicalState_isPositive n) ((N).stronglyMeasurable_physicalState n)
    ((N).physicalState_trace n) (LB n) (σB n) (posB n) (strongB n) (traceB n)
    (completedOutcome Ω n) (measurableEmbedding_completedOutcome Ω n)
    (encodeHistory Ω n h.val) h
  intro s hs
  exact congrArg (fun L => L ((σB n) h))
    (physicalBobCompletedReferenceInstrument_event Ω D FA FB QA QB WA WB PA PB JA JB n h s hs)

end ConcretePhysicalInvariant

end QuantumProver.ElegantJointMeasurement.NormalPhysicalOperationalBridge

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000

open MeasureTheory ProbabilityTheory Set Filter Function InnerProductSpace TopologicalSpace
open scoped BigOperators Topology ComplexOrder

namespace QuantumProver.ElegantJointMeasurement.NormalPhysicalOperationalBridge

open QuantumProver.ElegantJointMeasurement.NormalProcess QuantumProver.ElegantJointMeasurement.HilbertSquareProcess QuantumProver.ElegantJointMeasurement.HilbertRecordCoding
open QuantumProver.ElegantJointMeasurement.NormalPhysicalAdmission QuantumProver.ElegantJointMeasurement.HilbertChoi QuantumProver.ElegantJointMeasurement.NuclearChoi
open QuantumProver.ElegantJointMeasurement.NormalInstrumentAbsorption QuantumProver.ElegantJointMeasurement.NormalSandwich
open QuantumProver.ElegantJointMeasurement.MeasurableNormalInstrument
open QuantumProver.ElegantJointMeasurement.SeparableHilbertEmbedding QuantumProver.ElegantJointMeasurement.MeasurableHilbertField
open QuantumProver.ElegantJointMeasurement.NormalControlledSpectatorLift
open QuantumProver.HilbertNuclearCompression QuantumProver.MatrixNuclearTensor
open QuantumProver.MatrixNormalTensorInstrument QuantumProver.MatrixNormalRightTensor
open QuantumProver.MatrixNormalSourceCompletion QuantumProver.MatrixNormalStateKernel
open QuantumProver.NuclearOperator (toOperator)

universe u v w

variable (Ω : ℕ → Type u) [∀ n, MeasurableSpace (Ω n)]
  [∀ n, StandardBorelSpace (Ω n)]
  (D : PhysicalDomains Ω)
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
  (PA : PhysicalLocalFamily Ω D true FA QA)
  (PB : PhysicalLocalFamily Ω D false FB QB)
  {a b : ℕ} [NeZero a] [NeZero b]
  (JA : EuclideanSpace ℂ (Fin a) →ₗᵢ[ℂ] EA 0 D.initialHistory)
  (JB : EuclideanSpace ℂ (Fin b) →ₗᵢ[ℂ] EB 0 D.initialHistory)

local notation "N" => ofPhysicalFamilies Ω D FA FB QA QB WA WB PA PB JA JB
local notation "CA" n => IntrinsicFamily.family (selectedMemory Ω D true FA QA WA n)
local notation "CB" n => IntrinsicFamily.family (selectedMemory Ω D false FB QB WB n)
local notation "S" n => encodedPhysicallySupportedHistory Ω D FA FB QA QB WA WB PA PB JA JB n
local notation "σA" n => admittedActiveState Ω D FA FB QA QB WA WB PA PB JA JB true n
local notation "σB" n => admittedActiveState Ω D FA FB QA QB WA WB PA PB JA JB false n
local notation "posA" n => admittedActiveState_positive Ω D FA FB QA QB WA WB PA PB JA JB true n
local notation "posB" n => admittedActiveState_positive Ω D FA FB QA QB WA WB PA PB JA JB false n
local notation "strongA" n => stronglyMeasurable_admittedActiveState Ω D FA FB QA QB WA WB PA PB JA JB true n
local notation "strongB" n => stronglyMeasurable_admittedActiveState Ω D FA FB QA QB WA WB PA PB JA JB false n
local notation "traceA" n => admittedActiveState_trace Ω D FA FB QA QB WA WB PA PB JA JB true n
local notation "traceB" n => admittedActiveState_trace Ω D FA FB QA QB WA WB PA PB JA JB false n
local notation "LA" n => physicalAliceCompletedReferenceInstrument Ω D FA QA WA PA (a := a) (b := b) n
local notation "LB" n => physicalBobCompletedReferenceInstrument Ω D FB QB WB PB (a := a) (b := b) n

theorem physicalAlice_successor_ae_tagged_supported (n : ℕ) (h : D.actingDomain n true)
    (hh : D.actingHistory n true h ∈
      physicallySupportedHistory Ω D FA FB QA QB WA WB PA PB JA JB n) :
    ∀ᵐ ω ∂bornKernel (LA n) (σA n) (posA n) (strongA n) (traceA n) h,
      compose (blockLift (R := Fin a × Fin b)
        (tensorMap ((taggedOutputFamily (QA n)).rangeProjection (h,ω))
          ((CB n).rangeProjection (D.actingHistory n true h))))
        (blockLift (R := Fin a × Fin b)
          (tensorMap ((taggedOutputFamily (QA n)).rangeProjection (h,ω))
            ((CB n).rangeProjection (D.actingHistory n true h))))
        ((N).represented_physicalState (n+1) (appendHistory n (encodeHistory Ω n h.val,completedOutcome Ω n ω))) =
        (N).represented_physicalState (n+1) (appendHistory n (encodeHistory Ω n h.val,completedOutcome Ω n ω)) := by
  have hRemote := physicalState_reference_bob_supported (CA n) (CB n)
    (D.actingHistory n true h) ((σA n) h) hh
  have hR : ((CB n).rangeProjection (D.actingHistory n true h)).adjoint =
      (CB n).rangeProjection (D.actingHistory n true h) :=
    inputProjection_adjoint (CB n) _
  have hSupp := physicalLeftPosterior_ae_supported (I := Fin a × Fin b)
    (V := CommonHilbert) (taggedOutputFamily (QA n))
    (admittedRecordedMemoryTurn Ω D true FA QA WA PA n)
    (σA n) (posA n) (strongA n) (traceA n) h
    ((CB n).rangeProjection (D.actingHistory n true h)) hR hRemote
  have hEq := physicalAliceCompletedReferenceInstrument_posterior_ae
    Ω D FA FB QA QB WA WB PA PB JA JB n h
  simp only [physicalAliceCompletedReferenceInstrument] at hEq
  filter_upwards [hSupp, hEq] with ω hs he
  rw [he] at hs
  exact hs

theorem physicalBob_successor_ae_tagged_supported (n : ℕ) (h : D.actingDomain n false)
    (hh : D.actingHistory n false h ∈
      physicallySupportedHistory Ω D FA FB QA QB WA WB PA PB JA JB n) :
    ∀ᵐ ω ∂bornKernel (LB n) (σB n) (posB n) (strongB n) (traceB n) h,
      compose (blockLift (R := Fin a × Fin b)
        (tensorMap ((CA n).rangeProjection (D.actingHistory n false h))
          ((taggedOutputFamily (QB n)).rangeProjection (h,ω))))
        (blockLift (R := Fin a × Fin b)
          (tensorMap ((CA n).rangeProjection (D.actingHistory n false h))
            ((taggedOutputFamily (QB n)).rangeProjection (h,ω))))
        ((N).represented_physicalState (n+1) (appendHistory n (encodeHistory Ω n h.val,completedOutcome Ω n ω))) =
        (N).represented_physicalState (n+1) (appendHistory n (encodeHistory Ω n h.val,completedOutcome Ω n ω)) := by
  have hRemote := physicalState_reference_alice_supported (CA n) (CB n)
    (D.actingHistory n false h) ((σB n) h) hh
  have hR : ((CA n).rangeProjection (D.actingHistory n false h)).adjoint =
      (CA n).rangeProjection (D.actingHistory n false h) :=
    inputProjection_adjoint (CA n) _
  have hSupp := physicalRightPosterior_ae_supported (I := Fin a × Fin b)
    (V := CommonHilbert) (taggedOutputFamily (QB n))
    (admittedRecordedMemoryTurn Ω D false FB QB WB PB n)
    (σB n) (posB n) (strongB n) (traceB n) h
    ((CA n).rangeProjection (D.actingHistory n false h)) hR hRemote
  have hEq := physicalBobCompletedReferenceInstrument_posterior_ae
    Ω D FA FB QA QB WA WB PA PB JA JB n h
  simp only [physicalBobCompletedReferenceInstrument] at hEq
  filter_upwards [hSupp, hEq] with ω hs he
  rw [he] at hs
  exact hs

section GraphEvents

variable (n : ℕ) (c : Bool) (h : D.actingDomain n c)

def physicalBadEncodedOutcome : Set (CommonRecord Ω) :=
  {r | (h,r) ∉ encodedAdmissibleGraph Ω n (D.actingGraph n c)}

theorem measurableSet_physicalBadEncodedOutcome :
    MeasurableSet (physicalBadEncodedOutcome Ω D n c h) :=
  ((measurableSet_encodedAdmissibleGraph Ω n (D.actingGraph n c)
    (D.measurableSet_actingGraph n c)).preimage
      (measurable_const.prodMk measurable_id)).compl

theorem physicalBadEncodedOutcome_physical_preimage :
    encodeOutcome Ω n ⁻¹' physicalBadEncodedOutcome Ω D n c h =
      {x | (h,x) ∉ D.actingGraph n c} := by
  ext x
  have hp := congrArg (fun A => (h,x) ∈ A)
    (encodedAdmissibleGraph_preimage Ω n (D.actingGraph n c))
  exact Iff.of_eq (congrArg Not hp)

end GraphEvents

theorem physicalAlice_badOutcome_event_zero (n : ℕ) (h : D.actingDomain n true)
    (hh : D.actingHistory n true h ∈
      physicallySupportedHistory Ω D FA FB QA QB WA WB PA PB JA JB n) :
    ((N).represented_physicalReferenceInstrument n).operation (encodeHistory Ω n h.val)
      (physicalBadEncodedOutcome Ω D n true h) ((σA n) h) = 0 := by
  change ((N).represented_physicalReferenceInstrument n).operation (encodeHistory Ω n h.val)
    (physicalBadEncodedOutcome Ω D n true h)
      ((N).represented_physicalState n (encodeHistory Ω n (D.actingHistory n true h).val)) = 0
  rw [physical_physicalReference_alice_event Ω D FA FB QA QB WA WB PA PB JA JB n h
    _ (measurableSet_physicalBadEncodedOutcome Ω D n true h) _ hh]
  have hLocal : tensorOperation (G := EB n (D.actingHistory n true h))
      (physicalPhysicalMemoryTurn Ω D true FA QA PA n h) ()
      (encodeOutcome Ω n ⁻¹' physicalBadEncodedOutcome Ω D n true h) = 0 := by
    apply tensorOperation_zero_event
    · exact (measurable_encodeOutcome Ω n) (measurableSet_physicalBadEncodedOutcome Ω D n true h)
    · rw [physicalPhysicalMemoryTurn_operation,
        physicalBadEncodedOutcome_physical_preimage]
      exact PA.off_graph n h
  change normalAmplification (R := Fin a × Fin b)
    ((rightSourceCode Ω n (D.admissible n) (CB n) (D.actingHistory n true h)).comp
      (tensorOperation (G := EB n (D.actingHistory n true h))
        (physicalPhysicalMemoryTurn Ω D true FA QA PA n h) ()
        (encodeOutcome Ω n ⁻¹' physicalBadEncodedOutcome Ω D n true h))) _ = 0
  rw [hLocal, ContinuousLinearMap.comp_zero]
  simp only [normalAmplification_apply, ContinuousLinearMap.zero_apply,
    nuclearAssembly, map_zero, Finset.sum_const_zero]

theorem physicalBob_badOutcome_event_zero (n : ℕ) (h : D.actingDomain n false)
    (hh : D.actingHistory n false h ∈
      physicallySupportedHistory Ω D FA FB QA QB WA WB PA PB JA JB n) :
    ((N).represented_physicalReferenceInstrument n).operation (encodeHistory Ω n h.val)
      (physicalBadEncodedOutcome Ω D n false h) ((σB n) h) = 0 := by
  change ((N).represented_physicalReferenceInstrument n).operation (encodeHistory Ω n h.val)
    (physicalBadEncodedOutcome Ω D n false h)
      ((N).represented_physicalState n (encodeHistory Ω n (D.actingHistory n false h).val)) = 0
  rw [physical_physicalReference_bob_event Ω D FA FB QA QB WA WB PA PB JA JB n h
    _ (measurableSet_physicalBadEncodedOutcome Ω D n false h) _ hh]
  have hLocal : rightTensorOperation (G := EA n (D.actingHistory n false h))
      (physicalPhysicalMemoryTurn Ω D false FB QB PB n h) ()
      (encodeOutcome Ω n ⁻¹' physicalBadEncodedOutcome Ω D n false h) = 0 := by
    apply rightTensorOperation_zero_event
    · exact (measurable_encodeOutcome Ω n) (measurableSet_physicalBadEncodedOutcome Ω D n false h)
    · rw [physicalPhysicalMemoryTurn_operation,
        physicalBadEncodedOutcome_physical_preimage]
      exact PB.off_graph n h
  change normalAmplification (R := Fin a × Fin b)
    ((leftSourceCode Ω n (D.admissible n) (CA n) (D.actingHistory n false h)).comp
      (rightTensorOperation (G := EA n (D.actingHistory n false h))
        (physicalPhysicalMemoryTurn Ω D false FB QB PB n h) ()
        (encodeOutcome Ω n ⁻¹' physicalBadEncodedOutcome Ω D n false h))) _ = 0
  rw [hLocal, ContinuousLinearMap.comp_zero]
  simp only [normalAmplification_apply, ContinuousLinearMap.zero_apply,
    nuclearAssembly, map_zero, Finset.sum_const_zero]

theorem physicalAlice_graph_successor_supported (n : ℕ) (h : D.actingDomain n true)
    (x : Ω n) (hx : (h,x) ∈ D.actingGraph n true)
    (hs : compose (blockLift (R := Fin a × Fin b)
      (tensorMap ((QA n).rangeProjection (h,x))
        ((CB n).rangeProjection (D.actingHistory n true h))))
      (blockLift (R := Fin a × Fin b)
        (tensorMap ((QA n).rangeProjection (h,x))
          ((CB n).rangeProjection (D.actingHistory n true h))))
      ((N).represented_physicalState (n+1) (appendHistory n (encodeHistory Ω n h.val,encodeOutcome Ω n x))) =
      (N).represented_physicalState (n+1) (appendHistory n (encodeHistory Ω n h.val,encodeOutcome Ω n x))) :
    appendHistory n (encodeHistory Ω n h.val,encodeOutcome Ω n x) ∈ S (n+1) := by
  let z : D.actingGraph n true := ⟨(h,x),hx⟩
  let r : D.successorDomain n true := ⟨D.appendActingGraph n true z,mem_range_self z⟩
  have hDecode : D.decodeSuccessor n true r = z := D.decodeSuccessor_append n true z
  have hA : (CA (n+1)).rangeProjection r.val = (QA n).rangeProjection (h,x) := by
    rw [selectedMemory_acted_projection]
    change (QA n).rangeProjection (D.decodeSuccessor n true r).val = _
    rw [hDecode]
  have hB : (CB (n+1)).rangeProjection r.val =
      (CB n).rangeProjection (D.actingHistory n true h) := by
    rw [selectedMemory_idle_projection Ω D false FB QB WB n r]
    change (CB n).rangeProjection (D.actingHistory n true (D.decodeSuccessor n true r).val.1) = _
    rw [hDecode]
  refine ⟨r.val, ?_, rfl⟩
  change compose (blockLift (R := Fin a × Fin b) (physicalJointProjection (CA (n+1)) (CB (n+1)) r.val))
    (blockLift (R := Fin a × Fin b) (physicalJointProjection (CA (n+1)) (CB (n+1)) r.val))
    ((N).represented_physicalState (n+1) (encodeHistory Ω (n+1) r.val.val)) =
      (N).represented_physicalState (n+1) (encodeHistory Ω (n+1) r.val.val)
  rw [physicalJointProjection, hA, hB]
  exact hs

theorem physicalBob_graph_successor_supported (n : ℕ) (h : D.actingDomain n false)
    (x : Ω n) (hx : (h,x) ∈ D.actingGraph n false)
    (hs : compose (blockLift (R := Fin a × Fin b)
      (tensorMap ((CA n).rangeProjection (D.actingHistory n false h))
        ((QB n).rangeProjection (h,x))))
      (blockLift (R := Fin a × Fin b)
        (tensorMap ((CA n).rangeProjection (D.actingHistory n false h))
          ((QB n).rangeProjection (h,x))))
      ((N).represented_physicalState (n+1) (appendHistory n (encodeHistory Ω n h.val,encodeOutcome Ω n x))) =
      (N).represented_physicalState (n+1) (appendHistory n (encodeHistory Ω n h.val,encodeOutcome Ω n x))) :
    appendHistory n (encodeHistory Ω n h.val,encodeOutcome Ω n x) ∈ S (n+1) := by
  let z : D.actingGraph n false := ⟨(h,x),hx⟩
  let r : D.successorDomain n false := ⟨D.appendActingGraph n false z,mem_range_self z⟩
  have hDecode : D.decodeSuccessor n false r = z := D.decodeSuccessor_append n false z
  have hA : (CA (n+1)).rangeProjection r.val =
      (CA n).rangeProjection (D.actingHistory n false h) := by
    rw [selectedMemory_idle_projection Ω D true FA QA WA n r]
    change (CA n).rangeProjection (D.actingHistory n false (D.decodeSuccessor n false r).val.1) = _
    rw [hDecode]
  have hB : (CB (n+1)).rangeProjection r.val = (QB n).rangeProjection (h,x) := by
    rw [selectedMemory_acted_projection]
    change (QB n).rangeProjection (D.decodeSuccessor n false r).val = _
    rw [hDecode]
  refine ⟨r.val, ?_, rfl⟩
  change compose (blockLift (R := Fin a × Fin b) (physicalJointProjection (CA (n+1)) (CB (n+1)) r.val))
    (blockLift (R := Fin a × Fin b) (physicalJointProjection (CA (n+1)) (CB (n+1)) r.val))
    ((N).represented_physicalState (n+1) (encodeHistory Ω (n+1) r.val.val)) =
      (N).represented_physicalState (n+1) (encodeHistory Ω (n+1) r.val.val)
  rw [physicalJointProjection, hA, hB]
  exact hs

theorem physicalAlice_successor_ae_good (n : ℕ) (h : D.actingDomain n true)
    (hh : D.actingHistory n true h ∈
      physicallySupportedHistory Ω D FA FB QA QB WA WB PA PB JA JB n) :
    ∀ᵐ r ∂(N).represented_physicalBornKernel n (encodeHistory Ω n h.val),
      appendHistory n (encodeHistory Ω n h.val,r) ∈ S (n+1) := by
  have hBorn := physicalAliceCompletedReferenceInstrument_born_map
    Ω D FA FB QA QB WA WB PA PB JA JB n h
  have hz : (N).represented_physicalBornKernel n (encodeHistory Ω n h.val)
      (physicalBadEncodedOutcome Ω D n true h) = 0 := by
    rw [(N).physicalBornKernel_apply n _ _
      (measurableSet_physicalBadEncodedOutcome Ω D n true h)]
    have hZero := physicalAlice_badOutcome_event_zero Ω D FA FB QA QB WA WB PA PB JA JB n h hh
    simpa only [admittedActiveState, map_zero, Complex.zero_re, ENNReal.ofReal_zero] using
      congrArg (fun U : QuantumProver.ElegantJointMeasurement.NuclearChoi.Nuclear (PhysicalChoiWorkspace a b) =>
        ENNReal.ofReal (QuantumProver.HilbertNuclearTrace.trace U).re) hZero
  have hGraph : ∀ᵐ ω ∂bornKernel (LA n) (σA n) (posA n) (strongA n) (traceA n) h,
      (h,completedOutcome Ω n ω) ∈ encodedAdmissibleGraph Ω n (D.actingGraph n true) := by
    apply ae_iff.mpr
    rw [hBorn, Measure.map_apply (measurable_completedOutcome Ω n)
      (measurableSet_physicalBadEncodedOutcome Ω D n true h)] at hz
    exact hz
  rw [hBorn]
  apply (ae_map_iff (measurable_completedOutcome Ω n).aemeasurable
    ((measurableSet_encodedPhysicallySupportedHistory Ω D FA FB QA QB WA WB PA PB JA JB (n+1)).preimage
      ((appendHistory n).measurable.comp (measurable_const.prodMk measurable_id)))).mpr
  filter_upwards [hGraph, physicalAlice_successor_ae_tagged_supported
    Ω D FA FB QA QB WA WB PA PB JA JB n h hh] with ω hg hs
  rcases hg with ⟨⟨k,x⟩,hx,he⟩
  have hk : k = h := congrArg Prod.fst he
  subst k
  have hr : encodeOutcome Ω n x = completedOutcome Ω n ω := congrArg Prod.snd he
  have hω : ω = Sum.inl x := (completedOutcome_injective Ω n) hr.symm
  subst ω
  apply physicalAlice_graph_successor_supported Ω D FA FB QA QB WA WB PA PB JA JB n h x hx
  simpa only [completedOutcome, taggedOutputFamily_physical_projection] using hs

theorem physicalBob_successor_ae_good (n : ℕ) (h : D.actingDomain n false)
    (hh : D.actingHistory n false h ∈
      physicallySupportedHistory Ω D FA FB QA QB WA WB PA PB JA JB n) :
    ∀ᵐ r ∂(N).represented_physicalBornKernel n (encodeHistory Ω n h.val),
      appendHistory n (encodeHistory Ω n h.val,r) ∈ S (n+1) := by
  have hBorn := physicalBobCompletedReferenceInstrument_born_map
    Ω D FA FB QA QB WA WB PA PB JA JB n h
  have hz : (N).represented_physicalBornKernel n (encodeHistory Ω n h.val)
      (physicalBadEncodedOutcome Ω D n false h) = 0 := by
    rw [(N).physicalBornKernel_apply n _ _
      (measurableSet_physicalBadEncodedOutcome Ω D n false h)]
    have hZero := physicalBob_badOutcome_event_zero Ω D FA FB QA QB WA WB PA PB JA JB n h hh
    simpa only [admittedActiveState, map_zero, Complex.zero_re, ENNReal.ofReal_zero] using
      congrArg (fun U : QuantumProver.ElegantJointMeasurement.NuclearChoi.Nuclear (PhysicalChoiWorkspace a b) =>
        ENNReal.ofReal (QuantumProver.HilbertNuclearTrace.trace U).re) hZero
  have hGraph : ∀ᵐ ω ∂bornKernel (LB n) (σB n) (posB n) (strongB n) (traceB n) h,
      (h,completedOutcome Ω n ω) ∈ encodedAdmissibleGraph Ω n (D.actingGraph n false) := by
    apply ae_iff.mpr
    rw [hBorn, Measure.map_apply (measurable_completedOutcome Ω n)
      (measurableSet_physicalBadEncodedOutcome Ω D n false h)] at hz
    exact hz
  rw [hBorn]
  apply (ae_map_iff (measurable_completedOutcome Ω n).aemeasurable
    ((measurableSet_encodedPhysicallySupportedHistory Ω D FA FB QA QB WA WB PA PB JA JB (n+1)).preimage
      ((appendHistory n).measurable.comp (measurable_const.prodMk measurable_id)))).mpr
  filter_upwards [hGraph, physicalBob_successor_ae_tagged_supported
    Ω D FA FB QA QB WA WB PA PB JA JB n h hh] with ω hg hs
  rcases hg with ⟨⟨k,x⟩,hx,he⟩
  have hk : k = h := congrArg Prod.fst he
  subst k
  have hr : encodeOutcome Ω n x = completedOutcome Ω n ω := congrArg Prod.snd he
  have hω : ω = Sum.inl x := (completedOutcome_injective Ω n) hr.symm
  subst ω
  apply physicalBob_graph_successor_supported Ω D FA FB QA QB WA WB PA PB JA JB n h x hx
  simpa only [completedOutcome, taggedOutputFamily_physical_projection] using hs

theorem physical_physicalPrefixMeasure_ae_supported (n : ℕ) :
    ∀ᵐ h ∂(N).represented_physicalPrefixMeasure n, h ∈ S n := by
  apply physicalPrefixMeasure_ae_local_invariant N
    (encodedPhysicallySupportedHistory Ω D FA FB QA QB WA WB PA PB JA JB)
    (measurableSet_encodedPhysicallySupportedHistory Ω D FA FB QA QB WA WB PA PB JA JB)
    (encodedPhysicallySupportedHistory_zero Ω D FA FB QA QB WA WB PA PB JA JB)
  intro k h hh
  rcases hh with ⟨z,hz,rfl⟩
  cases hp : D.party k z with
  | false =>
      exact physicalBob_successor_ae_good Ω D FA FB QA QB WA WB PA PB JA JB k
        (D.actingPhysical k false z hp) hz
  | true =>
      exact physicalAlice_successor_ae_good Ω D FA FB QA QB WA WB PA PB JA JB k
        (D.actingPhysical k true z hp) hz

theorem physical_physicalPrefixAction_bad_zero (n : ℕ) (X : JointInputMatrix a b) :
    (N).represented_physicalPrefixAction n (S n)ᶜ X = 0 := by
  rw [(N).physicalPrefixAction_eq_physicalInputDensity n _
    (measurableSet_encodedPhysicallySupportedHistory Ω D FA FB QA QB WA WB PA PB JA JB n).compl X]
  have hz : (N).represented_physicalPrefixMeasure n (S n)ᶜ = 0 :=
    ae_iff.mp (physical_physicalPrefixMeasure_ae_supported Ω D FA FB QA QB WA WB PA PB JA JB n)
  simp only [Measure.restrict_eq_zero.mpr hz, integral_zero_measure]

end QuantumProver.ElegantJointMeasurement.NormalPhysicalOperationalBridge

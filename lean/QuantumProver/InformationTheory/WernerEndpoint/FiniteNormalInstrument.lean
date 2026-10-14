import QuantumProver.InformationTheory.ElegantJointMeasurement.NormalInstrumentCompletion
import QuantumProver.InformationTheory.ElegantJointMeasurement.HilbertRecovery

set_option autoImplicit false
set_option maxHeartbeats 1200000

noncomputable section

namespace QuantumProver.WernerEndpoint.MatrixFiniteNormalInstrument

open MeasureTheory Set Function InnerProductSpace
open QuantumProver.ElegantJointMeasurement.HilbertChoi QuantumProver.ElegantJointMeasurement.NuclearChoi
open QuantumProver.ElegantJointMeasurement.NormalInstrumentAbsorption QuantumProver.ElegantJointMeasurement.NormalSandwich
open QuantumProver.ElegantJointMeasurement.SeparableHilbertEmbedding QuantumProver.ElegantJointMeasurement.NormalInstrumentCompletion
open QuantumProver.ElegantJointMeasurement.HilbertRecovery
open QuantumProver.NuclearOperator (toOperator toOperator_injective)
open QuantumProver.HilbertNuclearCompression
open scoped BigOperators Topology ComplexOrder MatrixOrder Matrix.Norms.L2Operator Classical

abbrev FiniteSource (a : ℕ) := EuclideanSpace ℂ (Fin a)
abbrev FiniteNuclear (a : ℕ) := QuantumProver.ElegantJointMeasurement.NuclearChoi.Nuclear (FiniteSource a)

local instance finiteOutcomeMeasurable (h : ℕ) : MeasurableSpace (Fin h) := ⊤
local instance sourceComplete (a : ℕ) : CompleteSpace (FiniteSource a) :=
  PiLp.completeSpace 2 (fun _ : Fin a => ℂ)
local instance finiteNuclearDimensional (a : ℕ) : FiniteDimensional ℂ (FiniteNuclear a) :=
  FiniteDimensional.of_injective
    (toOperator (𝕜 := ℂ) (E := FiniteSource a) (F := FiniteSource a)).toLinearMap
    toOperator_injective
local instance finiteNuclearProper (a : ℕ) : ProperSpace (FiniteNuclear a) :=
  FiniteDimensional.proper ℂ (FiniteNuclear a)
local instance finiteNuclearMeasurable (a : ℕ) : MeasurableSpace (FiniteNuclear a) := borel _
local instance finiteNuclearBorel (a : ℕ) : BorelSpace (FiniteNuclear a) := ⟨rfl⟩
local instance finiteNormalMeasurable (a p : ℕ) :
    MeasurableSpace (NormalOperation (FiniteSource a) (FiniteSource p)) := borel _
local instance finiteNormalBorel (a p : ℕ) :
    BorelSpace (NormalOperation (FiniteSource a) (FiniteSource p)) := ⟨rfl⟩
local instance commonNuclearMeasurable : MeasurableSpace (Nuclear CommonHilbert) := borel _
local instance commonNuclearBorel : BorelSpace (Nuclear CommonHilbert) := ⟨rfl⟩
local instance commonSeparable : TopologicalSpace.SeparableSpace CommonHilbert := by
  have hs : TopologicalSpace.IsSeparable
      (closure (Submodule.span ℂ (Set.range commonBasis) : Set CommonHilbert)) :=
    ((Set.countable_range commonBasis).isSeparable.span (R := ℂ)).closure
  have hc : closure (Submodule.span ℂ (Set.range commonBasis) : Set CommonHilbert) = univ := by
    rw [← Submodule.topologicalClosure_coe, commonBasis.dense_span, Submodule.top_coe]
  exact TopologicalSpace.isSeparable_univ_iff.mp (hc ▸ hs)

def matrixCLM {a p : ℕ} (K : Matrix (Fin p) (Fin a) ℂ) :
    FiniteSource a →L[ℂ] FiniteSource p := K.toEuclideanLin.toContinuousLinearMap

@[simp] theorem matrixCLM_apply {a p : ℕ} (K : Matrix (Fin p) (Fin a) ℂ)
    (v : FiniteSource a) (i : Fin p) : matrixCLM K v i = (Matrix.mulVec K v) i := rfl

private def matrixCLMEquiv (a p : ℕ) : Matrix (Fin p) (Fin a) ℂ ≃ₗ[ℂ]
    (FiniteSource a →L[ℂ] FiniteSource p) :=
  Matrix.toEuclideanLin.trans LinearMap.toContinuousLinearMap

theorem continuous_matrixCLM (a p : ℕ) :
    Continuous (matrixCLM (a := a) (p := p)) :=
  (matrixCLMEquiv a p).toLinearMap.continuous_of_finiteDimensional

theorem matrixCLM_mul {a p q : ℕ}
    (A : Matrix (Fin q) (Fin p) ℂ) (B : Matrix (Fin p) (Fin a) ℂ) :
    matrixCLM (A * B) = matrixCLM A ∘L matrixCLM B := by
  ext v i
  change (Matrix.mulVec (A * B) v) i = (Matrix.mulVec A (Matrix.mulVec B v)) i
  rw [Matrix.mulVec_mulVec]

theorem matrixCLM_adjoint {a p : ℕ} (K : Matrix (Fin p) (Fin a) ℂ) :
    (matrixCLM K).adjoint = matrixCLM K.conjTranspose := by
  unfold matrixCLM
  rw [← LinearMap.adjoint_toContinuousLinearMap,
    ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]

@[simp] theorem matrixCLM_one (a : ℕ) :
    matrixCLM (1 : Matrix (Fin a) (Fin a) ℂ) = 1 := by
  ext v i
  simp only [matrixCLM_apply, Matrix.one_mulVec, one_apply_eq_self]

private theorem matrixCLM_square_eq (a : ℕ) (X : Matrix (Fin a) (Fin a) ℂ) :
    matrixCLM X = QuantumProver.ElegantJointMeasurement.HilbertPolar.matrixOperator X := by
  apply ContinuousLinearMap.coe_injective
  rfl

theorem sandwich_nuclearMatrix {a p : ℕ} (K : Matrix (Fin p) (Fin a) ℂ)
    (X : Matrix (Fin a) (Fin a) ℂ) :
    sandwich (matrixCLM K) (nuclearMatrix X) = nuclearMatrix (K * X * K.conjTranspose) := by
  apply toOperator_injective
  rw [toOperator_sandwich, toOperator_nuclearMatrix, toOperator_nuclearMatrix,
    ← matrixCLM_square_eq, ← matrixCLM_square_eq, matrixCLM_adjoint,
    ← matrixCLM_mul, ← matrixCLM_mul]
  rw [Matrix.mul_assoc]

def finiteBranch {a p h z : ℕ} (K : Fin h → Fin z → Matrix (Fin p) (Fin a) ℂ)
    (j : Fin h) : NormalOperation (FiniteSource a) (FiniteSource p) :=
  ∑ k, sandwich (matrixCLM (K j k))

def finiteEvent {a p h z : ℕ} (K : Fin h → Fin z → Matrix (Fin p) (Fin a) ℂ)
    (s : Set (Fin h)) : NormalOperation (FiniteSource a) (FiniteSource p) :=
  ∑ j, if j ∈ s then finiteBranch K j else 0

def matrixEvent {a p h z : ℕ} (K : Fin h → Fin z → Matrix (Fin p) (Fin a) ℂ)
    (s : Set (Fin h)) (X : Matrix (Fin a) (Fin a) ℂ) : Matrix (Fin p) (Fin p) ℂ :=
  ∑ j, if j ∈ s then ∑ k, K j k * X * (K j k).conjTranspose else 0

@[simp] theorem finiteEvent_apply {a p h z : ℕ}
    (K : Fin h → Fin z → Matrix (Fin p) (Fin a) ℂ)
    (s : Set (Fin h)) (T : FiniteNuclear a) :
    finiteEvent K s T = ∑ j, if j ∈ s then finiteBranch K j T else 0 := by
  simp only [finiteEvent, _root_.sum_apply]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j ∈ s <;> simp [hj]

theorem finiteEvent_nuclearMatrix {a p h z : ℕ}
    (K : Fin h → Fin z → Matrix (Fin p) (Fin a) ℂ)
    (s : Set (Fin h)) (X : Matrix (Fin a) (Fin a) ℂ) :
    finiteEvent K s (nuclearMatrix X) = nuclearMatrix (matrixEvent K s X) := by
  classical
  simp only [finiteEvent_apply, matrixEvent, map_sum, finiteBranch, _root_.sum_apply]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j ∈ s
  · simp only [ite_eq_left hj, map_sum]
    apply Finset.sum_congr rfl
    intro k _
    exact sandwich_nuclearMatrix (K j k) X
  · simp [hj]

private theorem normalCP_sum {a p : ℕ} {ι : Type*} (s : Finset ι)
    (Φ : ι → NormalOperation (FiniteSource a) (FiniteSource p))
    (hΦ : ∀ i, NormalCompletelyPositive (Φ i)) :
    NormalCompletelyPositive (∑ i ∈ s, Φ i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (normalCompletelyPositive_zero :
      NormalCompletelyPositive (0 : NormalOperation (FiniteSource a) (FiniteSource p)))
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact normalCompletelyPositive_add _ _ (hΦ i) ih

theorem finiteEvent_completelyPositive {a p h z : ℕ}
    (K : Fin h → Fin z → Matrix (Fin p) (Fin a) ℂ) (s : Set (Fin h)) :
    NormalCompletelyPositive (finiteEvent K s) := by
  classical
  unfold finiteEvent
  apply normalCP_sum
  intro j
  by_cases hj : j ∈ s
  · rw [ite_eq_left hj]
    apply normalCP_sum
    exact fun k => normalCompletelyPositive_sandwich _
  · rw [ite_eq_right hj]
    exact normalCompletelyPositive_zero

theorem finiteEvent_countable_additivity {a p h z : ℕ}
    (K : Fin h → Fin z → Matrix (Fin p) (Fin a) ℂ)
    (s : ℕ → Set (Fin h)) (hd : Pairwise (Disjoint on s)) (T : FiniteNuclear a) :
    HasSum (fun n => finiteEvent K (s n) T) (finiteEvent K (⋃ n, s n) T) := by
  classical
  have hs (u : Finset (Fin h)) :
      HasSum (fun n => ∑ j ∈ u, if j ∈ s n then finiteBranch K j T else 0)
        (∑ j ∈ u, if j ∈ ⋃ n, s n then finiteBranch K j T else 0) := by
    induction u using Finset.induction_on with
    | empty => simpa only [Finset.sum_empty] using
        (hasSum_zero : HasSum (fun _ : ℕ => (0 : FiniteNuclear p)) 0)
    | @insert j u hj ih =>
        simpa only [Finset.sum_insert hj] using
          (dummy_hasSum j s hd (finiteBranch K j T)).add ih
  simpa only [finiteEvent_apply] using hs Finset.univ

theorem matrixCLM_complete {a p h z : ℕ}
    (K : Fin h → Fin z → Matrix (Fin p) (Fin a) ℂ)
    (hK : ∑ j, ∑ k, (K j k).conjTranspose * K j k = 1) :
    ∑ j, ∑ k, (matrixCLM (K j k)).adjoint ∘L matrixCLM (K j k) = 1 := by
  calc
    _ = ∑ j, ∑ k, matrixCLM ((K j k).conjTranspose * K j k) := by
      simp only [matrixCLM_adjoint, matrixCLM_mul]
    _ = matrixCLM (∑ j, ∑ k, (K j k).conjTranspose * K j k) := by
      change (∑ j, ∑ k, matrixCLMEquiv a a ((K j k).conjTranspose * K j k)) =
        matrixCLMEquiv a a (∑ j, ∑ k, (K j k).conjTranspose * K j k)
      simp only [map_sum]
    _ = 1 := by rw [hK, matrixCLM_one]

private def tracePairing (a : ℕ) (T : FiniteNuclear a) :
    (FiniteSource a →L[ℂ] FiniteSource a) →L[ℂ] ℂ :=
  (QuantumProver.HilbertNuclearTrace.trace (𝕜 := ℂ) (E := FiniteSource a)).comp
    ((ContinuousLinearMap.apply ℂ (FiniteNuclear a) T).comp
      (rightCompose (ContinuousLinearMap.id ℂ (FiniteSource a))))

theorem finiteEvent_trace_preserving {a p h z : ℕ}
    (K : Fin h → Fin z → Matrix (Fin p) (Fin a) ℂ)
    (hK : ∑ j, ∑ k, (K j k).conjTranspose * K j k = 1) (T : FiniteNuclear a) :
    QuantumProver.HilbertNuclearTrace.trace (finiteEvent K univ T) =
      QuantumProver.HilbertNuclearTrace.trace T := by
  have ht (j : Fin h) (k : Fin z) :
      QuantumProver.HilbertNuclearTrace.trace (sandwich (matrixCLM (K j k)) T) =
        tracePairing a T ((matrixCLM (K j k)).adjoint ∘L matrixCLM (K j k)) := by
    rw [sandwich, QuantumProver.ElegantJointMeasurement.NormalCPInstruments.trace_compose_cycle]
    rfl
  simp only [finiteEvent_apply, mem_univ, ite_true, finiteBranch, _root_.sum_apply, map_sum]
  simp_rw [ht]
  change (∑ j, ∑ k, tracePairing a T ((matrixCLM (K j k)).adjoint ∘L matrixCLM (K j k))) = _
  calc
    _ = tracePairing a T (∑ j, ∑ k, (matrixCLM (K j k)).adjoint ∘L matrixCLM (K j k)) := by
      simp only [map_sum]
    _ = QuantumProver.HilbertNuclearTrace.trace T := by
      rw [matrixCLM_complete K hK]
      change QuantumProver.HilbertNuclearTrace.trace (compose (ContinuousLinearMap.id ℂ _) 1 T) = _
      congr 1
      apply toOperator_injective
      ext x
      simp [toOperator_compose]

section Histories
variable {Z : Type*} [MeasurableSpace Z]
variable {a p h z : ℕ}
variable (K : Z → Fin h → Fin z → Matrix (Fin p) (Fin a) ℂ)
    (hMeas : ∀ j k, Measurable (fun v => K v j k))

include hMeas in
theorem finiteEvent_measurable_apply (s : Set (Fin h)) (T : FiniteNuclear a) :
    Measurable (fun v => finiteEvent (K v) s T) := by
  classical
  simp only [finiteEvent_apply]
  apply Finset.measurable_sum
  intro j _
  by_cases hj : j ∈ s
  · simp only [ite_eq_left hj, finiteBranch, _root_.sum_apply]
    apply Finset.measurable_sum
    intro k _
    have hc : Continuous (fun A : Matrix (Fin p) (Fin a) ℂ => sandwich (matrixCLM A) T) := by
      change Continuous (fun A : Matrix (Fin p) (Fin a) ℂ =>
        (ContinuousLinearMap.apply ℂ (FiniteNuclear p) T) (nuclearSandwich (matrixCLM A)))
      exact (ContinuousLinearMap.apply ℂ (FiniteNuclear p) T).continuous.comp
        ((continuous_nuclearSandwich (I := Fin a) (E := FiniteSource p)).comp
          (continuous_matrixCLM a p))
    exact hc.measurable.comp (hMeas j k)
  · simp only [ite_eq_right hj]
    exact measurable_const

def finiteInstrument (hComplete : ∀ v, ∑ j, ∑ k, (K v j k).conjTranspose * K v j k = 1) :
    Instrument (FiniteSource a) (FiniteSource p) Z (Fin h) where
  operation v s := finiteEvent (K v) s
  empty v := by simp [finiteEvent]
  countable_additivity v s _ hd T := finiteEvent_countable_additivity (K v) s hd T
  completelyPositive v s _ := finiteEvent_completelyPositive (K v) s
  measurable_coordinate s _ T x y := by
    let L : FiniteNuclear p →L[ℂ] ℂ :=
      (innerSL ℂ x).comp ((ContinuousLinearMap.apply ℂ (FiniteSource p) y).comp toOperator)
    exact L.continuous.measurable.comp (finiteEvent_measurable_apply K hMeas s T)
  trace_preserving v T := finiteEvent_trace_preserving (K v) (hComplete v) T

def codeProjection (JA : FiniteSource a →ₗᵢ[ℂ] CommonHilbert) :
    CommonHilbert →L[ℂ] CommonHilbert :=
  JA.toContinuousLinearMap ∘L JA.toContinuousLinearMap.adjoint

private theorem codeProjection_adjoint (JA : FiniteSource a →ₗᵢ[ℂ] CommonHilbert) :
    (codeProjection JA).adjoint = codeProjection JA := by
  simp [codeProjection, ContinuousLinearMap.adjoint_comp]

private theorem codeProjection_idempotent (JA : FiniteSource a →ₗᵢ[ℂ] CommonHilbert) :
    codeProjection JA ∘L codeProjection JA = codeProjection JA := by
  calc
    _ = JA.toContinuousLinearMap ∘L
        (JA.toContinuousLinearMap.adjoint ∘L JA.toContinuousLinearMap) ∘L
          JA.toContinuousLinearMap.adjoint := by
      simp only [codeProjection, ContinuousLinearMap.comp_assoc]
    _ = codeProjection JA := by
      rw [JA.adjoint_comp_self]
      simp [codeProjection, ContinuousLinearMap.one_def]

private theorem pad_recover_eq_projection (JA : FiniteSource a →ₗᵢ[ℂ] CommonHilbert)
    (U : Nuclear CommonHilbert) :
    padNuclear JA (recoverNuclear JA U) = sandwich (codeProjection JA) U := by
  apply toOperator_injective
  ext x
  simp [padNuclear, recoverNuclear, codeProjection, toOperator_compose, toOperator_sandwich,
    ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.comp_apply]

def codedEvent (JA : FiniteSource a →ₗᵢ[ℂ] CommonHilbert)
    (JB : FiniteSource p →ₗᵢ[ℂ] CommonHilbert) (v : Z) (s : Set (Fin h)) :
    NormalOperation CommonHilbert CommonHilbert :=
  (padNuclear JB).comp ((finiteEvent (K v) s).comp (recoverNuclear JA))

def codedRangeInstrument (JA : FiniteSource a →ₗᵢ[ℂ] CommonHilbert)
    (JB : FiniteSource p →ₗᵢ[ℂ] CommonHilbert)
    (hComplete : ∀ v, ∑ j, ∑ k, (K v j k).conjTranspose * K v j k = 1) :
    RangeInstrument CommonHilbert CommonHilbert Z (Fin h) where
  inputProjection _ := codeProjection JA
  projection_adjoint _ := codeProjection_adjoint JA
  projection_idempotent _ := codeProjection_idempotent JA
  operation := codedEvent K JA JB
  empty v := by ext U; simp [codedEvent, finiteEvent]
  countable_additivity v s _ hd U := by
    simpa only [codedEvent, ContinuousLinearMap.comp_apply] using
      (finiteEvent_countable_additivity (K v) s hd (recoverNuclear JA U)).mapL (padNuclear JB)
  completelyPositive v s _ := by
    have hPad : padNuclear JB = sandwich JB.toContinuousLinearMap := rfl
    have hRec : recoverNuclear JA = sandwich JA.toContinuousLinearMap.adjoint := by
      simp only [recoverNuclear, sandwich, ContinuousLinearMap.adjoint_adjoint]
    rw [codedEvent, hPad, hRec]
    exact normalCompletelyPositive_comp _ _ (normalCompletelyPositive_sandwich _)
      (normalCompletelyPositive_comp _ _ (finiteEvent_completelyPositive (K v) s)
        (normalCompletelyPositive_sandwich _))
  measurable_coordinate s _ U x y := by
    let L : Nuclear CommonHilbert →L[ℂ] ℂ :=
      (innerSL ℂ x).comp ((ContinuousLinearMap.apply ℂ CommonHilbert y).comp toOperator)
    exact L.continuous.measurable.comp ((padNuclear JB).continuous.measurable.comp
      (finiteEvent_measurable_apply K hMeas s (recoverNuclear JA U)))
  trace_on_range v U := by
    change QuantumProver.HilbertNuclearTrace.trace
      (padNuclear JB (finiteEvent (K v) univ (recoverNuclear JA U))) = _
    rw [trace_padNuclear, finiteEvent_trace_preserving (K v) (hComplete v)]
    rw [← pad_recover_eq_projection]
    exact (trace_padNuclear JA (recoverNuclear JA U)).symm

def commonInstrument (JA : FiniteSource a →ₗᵢ[ℂ] CommonHilbert)
    (JB : FiniteSource p →ₗᵢ[ℂ] CommonHilbert)
    (hComplete : ∀ v, ∑ j, ∑ k, (K v j k).conjTranspose * K v j k = 1) :
    Instrument CommonHilbert CommonHilbert Z (Fin h ⊕ Unit) :=
  (codedRangeInstrument K hMeas JA JB hComplete).complete commonResetVector norm_commonResetVector

theorem commonInstrument_physical_event
    (JA : FiniteSource a →ₗᵢ[ℂ] CommonHilbert)
    (JB : FiniteSource p →ₗᵢ[ℂ] CommonHilbert)
    (hComplete : ∀ v, ∑ j, ∑ k, (K v j k).conjTranspose * K v j k = 1)
    (v : Z) (s : Set (Fin h)) (T : FiniteNuclear a) :
    (commonInstrument K hMeas JA JB hComplete).operation v (Sum.inl '' s) (padNuclear JA T) =
      padNuclear JB (finiteEvent (K v) s T) := by
  rw [commonInstrument, RangeInstrument.complete_operation,
    RangeInstrument.completedOperation_physical_event]
  simp only [codedRangeInstrument, codedEvent, ContinuousLinearMap.comp_apply, recover_padNuclear]

theorem commonInstrument_dummy_on_physical
    (JA : FiniteSource a →ₗᵢ[ℂ] CommonHilbert)
    (JB : FiniteSource p →ₗᵢ[ℂ] CommonHilbert)
    (hComplete : ∀ v, ∑ j, ∑ k, (K v j k).conjTranspose * K v j k = 1)
    (v : Z) (T : FiniteNuclear a) :
    (commonInstrument K hMeas JA JB hComplete).operation v {Sum.inr ()} (padNuclear JA T) = 0 := by
  rw [commonInstrument, RangeInstrument.complete_operation, RangeInstrument.completedOperation_dummy]
  have hPV : codeProjection JA ∘L JA.toContinuousLinearMap = JA.toContinuousLinearMap := by
    simp [codeProjection, ContinuousLinearMap.comp_assoc, JA.adjoint_comp_self,
      ContinuousLinearMap.one_def]
  exact complementReset_supported_input commonResetVector (codeProjection JA)
    JA.toContinuousLinearMap hPV T

theorem commonInstrument_all_events_on_physical
    (JA : FiniteSource a →ₗᵢ[ℂ] CommonHilbert)
    (JB : FiniteSource p →ₗᵢ[ℂ] CommonHilbert)
    (hComplete : ∀ v, ∑ j, ∑ k, (K v j k).conjTranspose * K v j k = 1)
    (v : Z) (s : Set (Fin h ⊕ Unit)) (T : FiniteNuclear a) :
    (commonInstrument K hMeas JA JB hComplete).operation v s (padNuclear JA T) =
      padNuclear JB (finiteEvent (K v) (Sum.inl ⁻¹' s) T) := by
  have hPV : codeProjection JA ∘L JA.toContinuousLinearMap = JA.toContinuousLinearMap := by
    simp [codeProjection, ContinuousLinearMap.comp_assoc, JA.adjoint_comp_self,
      ContinuousLinearMap.one_def]
  rw [commonInstrument, RangeInstrument.complete_operation]
  change (codedRangeInstrument K hMeas JA JB hComplete).completedOperation commonResetVector v s
    (sandwich JA.toContinuousLinearMap T) = _
  rw [RangeInstrument.completedOperation_supported_input _ commonResetVector v s
    JA.toContinuousLinearMap hPV T]
  change codedEvent K JA JB v (Sum.inl ⁻¹' s) (padNuclear JA T) = _
  simp only [codedEvent, ContinuousLinearMap.comp_apply, recover_padNuclear]

theorem commonInstrument_matrix_event
    (JA : FiniteSource a →ₗᵢ[ℂ] CommonHilbert)
    (JB : FiniteSource p →ₗᵢ[ℂ] CommonHilbert)
    (hComplete : ∀ v, ∑ j, ∑ k, (K v j k).conjTranspose * K v j k = 1)
    (v : Z) (s : Set (Fin h ⊕ Unit)) (X : Matrix (Fin a) (Fin a) ℂ) :
    (commonInstrument K hMeas JA JB hComplete).operation v s
      (padNuclear JA (nuclearMatrix X)) =
        padNuclear JB (nuclearMatrix (matrixEvent (K v) (Sum.inl ⁻¹' s) X)) := by
  rw [commonInstrument_all_events_on_physical K hMeas JA JB hComplete,
    finiteEvent_nuclearMatrix]

theorem commonInstrument_code_comp
    (JA : FiniteSource a →ₗᵢ[ℂ] CommonHilbert)
    (JB : FiniteSource p →ₗᵢ[ℂ] CommonHilbert)
    (hComplete : ∀ v, ∑ j, ∑ k, (K v j k).conjTranspose * K v j k = 1)
    (v : Z) (s : Set (Fin h ⊕ Unit)) :
    ((commonInstrument K hMeas JA JB hComplete).operation v s).comp (padNuclear JA) =
      (padNuclear JB).comp (finiteEvent (K v) (Sum.inl ⁻¹' s)) := by
  ext T
  exact commonInstrument_all_events_on_physical K hMeas JA JB hComplete v s T

theorem commonInstrument_finite_reference
    (JA : FiniteSource a →ₗᵢ[ℂ] CommonHilbert)
    (JB : FiniteSource p →ₗᵢ[ℂ] CommonHilbert)
    (hComplete : ∀ v, ∑ j, ∑ k, (K v j k).conjTranspose * K v j k = 1)
    (v : Z) (s : Set (Fin h ⊕ Unit))
    (R : Type) [Fintype R] [DecidableEq R]
    (T : Nuclear (BlockSpace R (FiniteSource a))) :
    normalAmplification ((commonInstrument K hMeas JA JB hComplete).operation v s)
      (normalAmplification (padNuclear JA) T) =
        normalAmplification (padNuclear JB)
          (normalAmplification (finiteEvent (K v) (Sum.inl ⁻¹' s)) T) := by
  rw [← normalAmplification_comp, ← normalAmplification_comp,
    commonInstrument_code_comp K hMeas JA JB hComplete]

end Histories
end QuantumProver.WernerEndpoint.MatrixFiniteNormalInstrument

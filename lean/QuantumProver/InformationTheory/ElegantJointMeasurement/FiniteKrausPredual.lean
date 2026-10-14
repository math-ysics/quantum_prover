import QuantumProver.InformationTheory.ElegantJointMeasurement.HilbertRecovery
import QuantumProver.InformationTheory.ElegantJointMeasurement.NormalCPInstruments
import QuantumProver.LinearAlgebra.HilbertNuclearCompression

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 200000

open MeasureTheory InnerProductSpace QuantumProver.ElegantJointMeasurement.HilbertPolar
open scoped BigOperators InnerProduct ComplexOrder MatrixOrder Topology Matrix.Norms.L2Operator

namespace QuantumProver.ElegantJointMeasurement.HilbertFiniteKrausPredual

open QuantumProver.ElegantJointMeasurement.HilbertRecovery QuantumProver.ElegantJointMeasurement.HilbertChoi QuantumProver.ElegantJointMeasurement.NormalCPInstruments
open QuantumProver.NuclearOperator (toOperator toOperator_injective)
open QuantumProver.HilbertNuclearCompression

variable {I Q : Type} [Fintype I] [DecidableEq I] [Fintype Q]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

local instance sourceComplete : CompleteSpace (Source I) :=
  PiLp.completeSpace 2 (fun _ : I => ℂ)
local instance channelNormedGroup :
    NormedAddCommGroup (NuclearChannel (I := I) (E := E)) := inferInstance
local instance channelNormedSpace :
    NormedSpace ℂ (NuclearChannel (I := I) (E := E)) := inferInstance
local instance operationNormedGroup :
    NormedAddCommGroup (PhysicalOperation I E) := inferInstance

def finiteKrausGram (K : Q → Source I →L[ℂ] E) : Source I →L[ℂ] Source I :=
  ∑ q, (K q).adjoint ∘L K q

def finiteKrausChannel (K : Q → Source I →L[ℂ] E) :
    NuclearChannel (I := I) (E := E) :=
  ∑ q, nuclearSandwich (K q)

theorem toOperator_finiteKrausChannel (K : Q → Source I →L[ℂ] E)
    (T : NuclearSource (I := I)) :
    toOperator (finiteKrausChannel K T) =
      ∑ q, K q ∘L toOperator T ∘L (K q).adjoint := by
  simp only [finiteKrausChannel, nuclearSandwich, sum_apply, map_sum, toOperator_compose]

theorem finiteKrausChannel_isPositive (K : Q → Source I →L[ℂ] E)
    (T : NuclearSource (I := I)) (hT : (toOperator T).IsPositive) :
    (toOperator (finiteKrausChannel K T)).IsPositive := by
  rw [toOperator_finiteKrausChannel]
  simpa using ContinuousLinearMap.isPositive_sum Finset.univ
    (fun q _ => hT.conj_adjoint (K q))

theorem trace_finiteKrausChannel (K : Q → Source I →L[ℂ] E)
    (T : NuclearSource (I := I)) :
    QuantumProver.HilbertNuclearTrace.trace (finiteKrausChannel K T) =
      QuantumProver.HilbertNuclearTrace.trace
        (compose (finiteKrausGram K) (ContinuousLinearMap.id ℂ (Source I)) T) := by
  have hsum : compose (ContinuousLinearMap.id ℂ (Source I))
      (finiteKrausGram K) T =
      ∑ q, compose (ContinuousLinearMap.id ℂ (Source I))
        ((K q).adjoint ∘L K q) T := by
    apply toOperator_injective
    simp only [finiteKrausGram, toOperator_compose, map_sum, ContinuousLinearMap.id_comp]
    ext x
    simp only [ContinuousLinearMap.comp_apply, sum_apply, map_sum]
  calc
    QuantumProver.HilbertNuclearTrace.trace (finiteKrausChannel K T) =
        ∑ q, QuantumProver.HilbertNuclearTrace.trace (compose (K q) (K q).adjoint T) := by
      simp only [finiteKrausChannel, nuclearSandwich, sum_apply, map_sum]
    _ = ∑ q, QuantumProver.HilbertNuclearTrace.trace
        (compose (ContinuousLinearMap.id ℂ (Source I)) ((K q).adjoint ∘L K q) T) := by
      apply Finset.sum_congr rfl
      intro q _
      exact trace_compose_cycle (K q) (K q).adjoint T
    _ = QuantumProver.HilbertNuclearTrace.trace
        (compose (ContinuousLinearMap.id ℂ (Source I)) (finiteKrausGram K) T) := by
      rw [← map_sum, ← hsum]
    _ = QuantumProver.HilbertNuclearTrace.trace
        (compose (finiteKrausGram K) (ContinuousLinearMap.id ℂ (Source I)) T) := by
      symm
      simpa only [ContinuousLinearMap.id_comp] using
        trace_compose_cycle (finiteKrausGram K) (ContinuousLinearMap.id ℂ (Source I)) T

def finiteKrausOperation (K : Q → Source I →L[ℂ] E) : PhysicalOperation I E :=
  (finiteKrausChannel K).comp (nuclearMatrix (I := I))

theorem toOperator_finiteKrausOperation (K : Q → Source I →L[ℂ] E)
    (X : Matrix I I ℂ) :
    toOperator (finiteKrausOperation K X) =
      ∑ q, K q ∘L QuantumProver.ElegantJointMeasurement.HilbertPolar.matrixOperator X ∘L (K q).adjoint := by
  simp only [finiteKrausOperation, ContinuousLinearMap.comp_apply,
    toOperator_finiteKrausChannel, toOperator_nuclearMatrix]

theorem trace_finiteKrausOperation (K : Q → Source I →L[ℂ] E)
    (X : Matrix I I ℂ) :
    QuantumProver.HilbertNuclearTrace.trace (finiteKrausOperation K X) =
      QuantumProver.HilbertNuclearTrace.trace
        (compose (finiteKrausGram K) (ContinuousLinearMap.id ℂ (Source I)) (nuclearMatrix X)) :=
  trace_finiteKrausChannel K (nuclearMatrix X)

theorem tracePreserving_finiteKrausOperation (K : Q → Source I →L[ℂ] E)
    (hK : ∑ q, (K q).adjoint ∘L K q = 1) (X : Matrix I I ℂ) :
    QuantumProver.HilbertNuclearTrace.trace (finiteKrausOperation K X) = Matrix.trace X := by
  have hGram : finiteKrausGram K = 1 := hK
  rw [trace_finiteKrausOperation, hGram]
  have h : compose (1 : Source I →L[ℂ] Source I)
      (ContinuousLinearMap.id ℂ (Source I)) (nuclearMatrix X) = nuclearMatrix X := by
    apply toOperator_injective
    simp only [toOperator_compose, ContinuousLinearMap.one_def,
      ContinuousLinearMap.id_comp, ContinuousLinearMap.comp_id]
  rw [h, trace_nuclearMatrix]

variable {R : Type} [Fintype R] [DecidableEq R]

def amplifiedFiniteKraus (K : Q → Source I →L[ℂ] E) :
    QuantumProver.ElegantJointMeasurement.NuclearChoi.Nuclear (BlockSpace R (Source I)) →L[ℂ]
      QuantumProver.ElegantJointMeasurement.NuclearChoi.Nuclear (BlockSpace R E) :=
  ∑ q, compose (blockLift (R := R) (K q)) (blockLift (R := R) (K q)).adjoint

theorem toOperator_amplifiedFiniteKraus (K : Q → Source I →L[ℂ] E)
    (T : QuantumProver.ElegantJointMeasurement.NuclearChoi.Nuclear (BlockSpace R (Source I))) :
    toOperator (amplifiedFiniteKraus K T) =
      ∑ q, blockLift (R := R) (K q) ∘L toOperator T ∘L (blockLift (R := R) (K q)).adjoint := by
  simp only [amplifiedFiniteKraus, sum_apply, map_sum, toOperator_compose]

theorem amplifiedFiniteKraus_isPositive (K : Q → Source I →L[ℂ] E)
    (T : QuantumProver.ElegantJointMeasurement.NuclearChoi.Nuclear (BlockSpace R (Source I))) (hT : (toOperator T).IsPositive) :
    (toOperator (amplifiedFiniteKraus K T)).IsPositive := by
  rw [toOperator_amplifiedFiniteKraus]
  simpa using ContinuousLinearMap.isPositive_sum Finset.univ
    (fun q _ => hT.conj_adjoint (blockLift (R := R) (K q)))

theorem amplifiedFiniteKraus_block (K : Q → Source I →L[ℂ] E)
    (T : QuantumProver.ElegantJointMeasurement.NuclearChoi.Nuclear (BlockSpace R (Source I))) (r s : R) :
    compose (PiLp.proj 2 (fun _ : R => E) r) (insert (E := E) s)
      (amplifiedFiniteKraus K T) =
      finiteKrausChannel K
        (compose (PiLp.proj 2 (fun _ : R => Source I) r) (insert (E := Source I) s) T) := by
  apply toOperator_injective
  rw [toOperator_compose, toOperator_amplifiedFiniteKraus, toOperator_finiteKrausChannel,
    toOperator_compose]
  ext x
  simp only [ContinuousLinearMap.comp_apply, sum_apply, map_sum]
  apply Finset.sum_congr rfl
  intro q _
  rw [blockLift_adjoint]
  change (blockLift (K q) (toOperator T (blockLift (K q).adjoint (insert s x)))) r = _
  rw [blockLift_apply]
  have harg : blockLift (R := R) (K q).adjoint (insert s x) =
      insert s ((K q).adjoint x) :=
    congrArg (fun L => L x) (blockLift_comp_insert (K q).adjoint s)
  rw [harg]
  rfl

theorem finiteKrausOperation_amplification (K : Q → Source I →L[ℂ] E)
    (X : Matrix (R × I) (R × I) ℂ) :
    toOperator (amplifiedFiniteKraus K (blockNuclearMatrix X)) =
      amplification (QuantumProver.ElegantJointMeasurement.NuclearChoi.operationOperator (finiteKrausOperation K).toLinearMap) X := by
  let A := toOperator (amplifiedFiniteKraus K (blockNuclearMatrix X))
  have hb (r s : R) :
      (PiLp.proj 2 (fun _ : R => E) r) ∘L A ∘L insert s =
        toOperator (finiteKrausOperation K (fun i j : I => X (r, i) (s, j))) := by
    change (PiLp.proj 2 (fun _ : R => E) r) ∘L
      toOperator (amplifiedFiniteKraus K (blockNuclearMatrix X)) ∘L insert s =
        toOperator (finiteKrausChannel K (nuclearMatrix (I := I) (fun i j : I => X (r, i) (s, j))))
    have h := congrArg (toOperator (𝕜 := ℂ) (E := E) (F := E))
      (amplifiedFiniteKraus_block K (blockNuclearMatrix X) r s)
    simpa only [toOperator_compose, blockNuclearMatrix_block] using h
  ext x r
  have hx : (∑ s : R, insert s (x s)) = x := by
    ext t
    simp [insert_apply_apply]
  change A x r = _
  calc
    A x r = ∑ s : R, A (insert s (x s)) r := by
      conv_lhs => rw [← hx, map_sum]
      simp only [WithLp.ofLp_sum, Finset.sum_apply]
    _ = ∑ s : R, toOperator (finiteKrausOperation K
        (fun i j : I => X (r, i) (s, j))) (x s) := by
      apply Finset.sum_congr rfl
      intro s _
      exact congrArg (fun L : E →L[ℂ] E => L (x s)) (hb r s)
    _ = _ := by
      rw [amplification, blockOperator_apply]
      apply Finset.sum_congr rfl
      intro s _
      let B : Matrix I I ℂ := fun i j => X (r, i) (s, j)
      change toOperator (finiteKrausOperation K B) (x s) = _
      rw [matrix_decomposition B]
      simp only [map_sum, map_smul, sum_apply, smul_apply,
        QuantumProver.ElegantJointMeasurement.NuclearChoi.operationOperator_apply, ContinuousLinearMap.coe_coe, B]

theorem completelyPositive_finiteKrausOperation (K : Q → Source I →L[ℂ] E) :
    CompletelyPositive (QuantumProver.ElegantJointMeasurement.NuclearChoi.operationOperator (finiteKrausOperation K).toLinearMap) := by
  intro R _ _ X hX
  rw [← finiteKrausOperation_amplification]
  exact amplifiedFiniteKraus_isPositive K _ (blockNuclearMatrix_isPositive X hX)

theorem continuous_finiteKrausChannel :
    Continuous (finiteKrausChannel (Q := Q) (I := I) (E := E)) := by
  apply continuous_finset_sum
  intro q _
  exact continuous_nuclearSandwich.comp (continuous_apply q)

theorem continuous_finiteKrausOperation :
    Continuous (finiteKrausOperation (Q := Q) (I := I) (E := E)) :=
  continuous_finiteKrausChannel.clm_comp continuous_const

local instance familyMeasurable : MeasurableSpace (Q → Source I →L[ℂ] E) := borel _
local instance familyBorel : BorelSpace (Q → Source I →L[ℂ] E) := ⟨rfl⟩
local instance operationMeasurable : MeasurableSpace (PhysicalOperation I E) := borel _
local instance operationBorel : BorelSpace (PhysicalOperation I E) := ⟨rfl⟩

theorem measurable_finiteKrausOperation :
    Measurable (finiteKrausOperation (Q := Q) (I := I) (E := E)) :=
  continuous_finiteKrausOperation.measurable

theorem stronglyMeasurable_finiteKrausOperation {α : Type*} [MeasurableSpace α]
    {K : α → Q → Source I →L[ℂ] E} (hK : StronglyMeasurable K) :
    StronglyMeasurable (fun a => finiteKrausOperation (K a)) :=
  continuous_finiteKrausOperation.comp_stronglyMeasurable hK

theorem stronglyMeasurable_finiteKrausOperation_apply {α : Type*} [MeasurableSpace α]
    {K : α → Q → Source I →L[ℂ] E} {X : α → Matrix I I ℂ}
    (hK : StronglyMeasurable K) (hX : StronglyMeasurable X) :
    StronglyMeasurable (fun a => finiteKrausOperation (K a) (X a)) := by
  let f : α → PhysicalOperation I E := fun a => finiteKrausOperation (K a)
  have hf : StronglyMeasurable f := stronglyMeasurable_finiteKrausOperation hK
  have hp : StronglyMeasurable (fun a => (f a, X a)) := hf.prodMk hX
  have hc : Continuous (fun p : PhysicalOperation I E × Matrix I I ℂ => p.1 p.2) :=
    (isBoundedBilinearMap_apply (𝕜 := ℂ) (E := Matrix I I ℂ)
      (F := QuantumProver.ElegantJointMeasurement.NuclearChoi.Nuclear E)).continuous
  change StronglyMeasurable (fun a => f a (X a))
  exact hc.comp_stronglyMeasurable hp

end QuantumProver.ElegantJointMeasurement.HilbertFiniteKrausPredual

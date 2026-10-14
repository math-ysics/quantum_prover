import QuantumProver.InformationTheory.WernerEndpoint.FiniteNormalInstrument

set_option autoImplicit false
set_option maxHeartbeats 1200000

noncomputable section

namespace QuantumProver.WernerEndpoint.MatrixFiniteNormalTerminal

open MeasureTheory Set Function InnerProductSpace
open QuantumProver.ElegantJointMeasurement.HilbertChoi QuantumProver.ElegantJointMeasurement.NuclearChoi
open QuantumProver.ElegantJointMeasurement.NormalInstrumentAbsorption QuantumProver.ElegantJointMeasurement.NormalSandwich
open QuantumProver.ElegantJointMeasurement.SeparableHilbertEmbedding QuantumProver.ElegantJointMeasurement.NormalInstrumentCompletion
open QuantumProver.ElegantJointMeasurement.HilbertRecovery QuantumProver.WernerEndpoint.MatrixFiniteNormalInstrument
open QuantumProver.NuclearOperator (toOperator toOperator_injective)
open QuantumProver.HilbertNuclearCompression
open scoped BigOperators Topology ComplexOrder MatrixOrder Matrix.Norms.L2Operator Classical

local instance finiteSourceComplete (a : ℕ) : CompleteSpace (FiniteSource a) :=
  PiLp.completeSpace 2 (fun _ : Fin a => ℂ)
local instance finiteSourceProper (a : ℕ) : ProperSpace (FiniteSource a) :=
  FiniteDimensional.proper ℂ (FiniteSource a)

variable {a c : ℕ}

def resetVector (hc : 0 < c) : FiniteSource c :=
  EuclideanSpace.basisFun (Fin c) ℂ ⟨0, hc⟩

theorem norm_resetVector (hc : 0 < c) : ‖resetVector hc‖ = 1 :=
  (EuclideanSpace.basisFun (Fin c) ℂ).orthonormal.1 ⟨0, hc⟩

theorem finiteIsometry_trace (L : Matrix (Fin c) (Fin a) ℂ)
    (hL : L.conjTranspose * L = 1) (T : FiniteNuclear a) :
    QuantumProver.HilbertNuclearTrace.trace (sandwich (matrixCLM L) T) =
      QuantumProver.HilbertNuclearTrace.trace T := by
  have hGram : (matrixCLM L).adjoint ∘L matrixCLM L = 1 := by
    rw [matrixCLM_adjoint, ← matrixCLM_mul, hL, matrixCLM_one]
  rw [sandwich, QuantumProver.ElegantJointMeasurement.NormalCPInstruments.trace_compose_cycle, hGram]
  congr 1
  apply toOperator_injective
  ext x
  simp only [toOperator_compose, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply, one_apply_eq_self]

theorem projection_comp_embedding (JA : FiniteSource a →ₗᵢ[ℂ] CommonHilbert) :
    codeProjection JA ∘L JA.toContinuousLinearMap = JA.toContinuousLinearMap := by
  simp [codeProjection, ContinuousLinearMap.comp_assoc, JA.adjoint_comp_self,
    ContinuousLinearMap.one_def]

private theorem pad_recover_projection (JA : FiniteSource a →ₗᵢ[ℂ] CommonHilbert)
    (U : Nuclear CommonHilbert) :
    padNuclear JA (recoverNuclear JA U) = sandwich (codeProjection JA) U := by
  apply toOperator_injective
  ext x
  simp [padNuclear, recoverNuclear, codeProjection, toOperator_compose,
    toOperator_sandwich, ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.comp_apply]

def branchOperation (JA : FiniteSource a →ₗᵢ[ℂ] CommonHilbert)
    (L : Matrix (Fin c) (Fin a) ℂ) : NormalOperation CommonHilbert (FiniteSource c) :=
  (sandwich (matrixCLM L)).comp (recoverNuclear JA)

def rangeOperation (JA : FiniteSource a →ₗᵢ[ℂ] CommonHilbert)
    (L : Matrix (Fin c) (Fin a) ℂ) (s : Set Unit) :
    NormalOperation CommonHilbert (FiniteSource c) :=
  if () ∈ s then branchOperation JA L else 0

@[simp] theorem rangeOperation_apply (JA : FiniteSource a →ₗᵢ[ℂ] CommonHilbert)
    (L : Matrix (Fin c) (Fin a) ℂ) (s : Set Unit) (U : Nuclear CommonHilbert) :
    rangeOperation JA L s U = if () ∈ s then branchOperation JA L U else 0 := by
  by_cases hs : () ∈ s <;> simp [rangeOperation, hs]

def rangeInstrument (JA : FiniteSource a →ₗᵢ[ℂ] CommonHilbert)
    (L : Matrix (Fin c) (Fin a) ℂ) (hL : L.conjTranspose * L = 1) :
    RangeInstrument CommonHilbert (FiniteSource c) Unit Unit where
  inputProjection _ := codeProjection JA
  projection_adjoint _ := by simp [codeProjection, ContinuousLinearMap.adjoint_comp]
  projection_idempotent _ := by
    calc
      _ = JA.toContinuousLinearMap ∘L
          (JA.toContinuousLinearMap.adjoint ∘L JA.toContinuousLinearMap) ∘L
            JA.toContinuousLinearMap.adjoint := by
        simp only [codeProjection, ContinuousLinearMap.comp_assoc]
      _ = codeProjection JA := by
        rw [JA.adjoint_comp_self]
        simp [codeProjection, ContinuousLinearMap.one_def]
  operation _ := rangeOperation JA L
  empty _ := by ext U; simp [rangeOperation]
  countable_additivity _ s _ hd U := by
    simpa only [rangeOperation_apply] using dummy_hasSum () s hd (branchOperation JA L U)
  completelyPositive _ s _ := by
    by_cases hs : () ∈ s
    · rw [rangeOperation, ite_eq_left hs]
      have hRec : recoverNuclear JA = sandwich JA.toContinuousLinearMap.adjoint := by
        simp only [recoverNuclear, sandwich, ContinuousLinearMap.adjoint_adjoint]
      rw [branchOperation, hRec]
      exact normalCompletelyPositive_comp _ _ (normalCompletelyPositive_sandwich _)
        (normalCompletelyPositive_sandwich _)
    · rw [rangeOperation, ite_eq_right hs]
      exact normalCompletelyPositive_zero
  measurable_coordinate _ _ _ _ _ := measurable_const
  trace_on_range _ U := by
    simp only [rangeOperation, mem_univ, ite_true, branchOperation,
      ContinuousLinearMap.comp_apply]
    rw [finiteIsometry_trace L hL, ← pad_recover_projection JA U]
    exact (trace_padNuclear JA (recoverNuclear JA U)).symm

def completedTerminal (hc : 0 < c) (JA : FiniteSource a →ₗᵢ[ℂ] CommonHilbert)
    (L : Matrix (Fin c) (Fin a) ℂ) (hL : L.conjTranspose * L = 1) :
    Instrument CommonHilbert (FiniteSource c) Unit (Unit ⊕ Unit) :=
  (rangeInstrument JA L hL).complete (resetVector hc) (norm_resetVector hc)

def collapse : Unit ⊕ Unit → Unit := fun _ => ()

def terminalInstrument (hc : 0 < c) (JA : FiniteSource a →ₗᵢ[ℂ] CommonHilbert)
    (L : Matrix (Fin c) (Fin a) ℂ) (hL : L.conjTranspose * L = 1) :
    Instrument CommonHilbert (FiniteSource c) Unit Unit where
  operation u s := (completedTerminal hc JA L hL).operation u (collapse ⁻¹' s)
  empty u := by simpa only [preimage_empty] using (completedTerminal hc JA L hL).empty u
  countable_additivity u s hs hd U := by
    simpa only [preimage_iUnion] using
      (completedTerminal hc JA L hL).countable_additivity u (fun n => collapse ⁻¹' s n)
        (fun n => measurable_const (hs n))
        (fun i j hij => (hd hij).preimage collapse) U
  completelyPositive u s hs :=
    (completedTerminal hc JA L hL).completelyPositive u _ (measurable_const hs)
  measurable_coordinate s hs U x y :=
    (completedTerminal hc JA L hL).measurable_coordinate _ (measurable_const hs) U x y
  trace_preserving u U := by
    simpa only [preimage_univ] using (completedTerminal hc JA L hL).trace_preserving u U

theorem terminalInstrument_univ_operation (hc : 0 < c)
    (JA : FiniteSource a →ₗᵢ[ℂ] CommonHilbert)
    (L : Matrix (Fin c) (Fin a) ℂ) (hL : L.conjTranspose * L = 1)
    (U : Nuclear CommonHilbert) :
    (terminalInstrument hc JA L hL).operation () univ U =
      branchOperation JA L U + complementReset (resetVector hc) (codeProjection JA) U := by
  simp only [terminalInstrument, preimage_univ, completedTerminal,
    RangeInstrument.complete_operation, RangeInstrument.completedOperation_apply,
    preimage_univ, mem_univ, ite_true, rangeInstrument, rangeOperation_apply]

theorem completedTerminal_on_code (hc : 0 < c)
    (JA : FiniteSource a →ₗᵢ[ℂ] CommonHilbert)
    (L : Matrix (Fin c) (Fin a) ℂ) (hL : L.conjTranspose * L = 1)
    (s : Set (Unit ⊕ Unit)) (T : FiniteNuclear a) :
    (completedTerminal hc JA L hL).operation () s (padNuclear JA T) =
      if Sum.inl () ∈ s then sandwich (matrixCLM L) T else 0 := by
  rw [completedTerminal, RangeInstrument.complete_operation]
  change (rangeInstrument JA L hL).completedOperation (resetVector hc) () s
    (sandwich JA.toContinuousLinearMap T) = _
  rw [RangeInstrument.completedOperation_supported_input _ (resetVector hc) () s
    JA.toContinuousLinearMap (projection_comp_embedding JA) T]
  change rangeOperation JA L (Sum.inl ⁻¹' s) (padNuclear JA T) = _
  simp only [rangeOperation_apply, mem_preimage, branchOperation,
    ContinuousLinearMap.comp_apply, recover_padNuclear]

theorem terminalInstrument_on_code (hc : 0 < c)
    (JA : FiniteSource a →ₗᵢ[ℂ] CommonHilbert)
    (L : Matrix (Fin c) (Fin a) ℂ) (hL : L.conjTranspose * L = 1)
    (s : Set Unit) (T : FiniteNuclear a) :
    (terminalInstrument hc JA L hL).operation () s (padNuclear JA T) =
      if () ∈ s then sandwich (matrixCLM L) T else 0 := by
  change (completedTerminal hc JA L hL).operation () (collapse ⁻¹' s) (padNuclear JA T) = _
  rw [completedTerminal_on_code]
  rfl

theorem terminalInstrument_univ_nuclear (hc : 0 < c)
    (JA : FiniteSource a →ₗᵢ[ℂ] CommonHilbert)
    (L : Matrix (Fin c) (Fin a) ℂ) (hL : L.conjTranspose * L = 1) (T : FiniteNuclear a) :
    (terminalInstrument hc JA L hL).operation () univ (padNuclear JA T) =
      sandwich (matrixCLM L) T := by
  simp only [terminalInstrument_on_code, mem_univ, ite_true]

theorem terminalInstrument_univ (hc : 0 < c)
    (JA : FiniteSource a →ₗᵢ[ℂ] CommonHilbert)
    (L : Matrix (Fin c) (Fin a) ℂ) (hL : L.conjTranspose * L = 1)
    (X : Matrix (Fin a) (Fin a) ℂ) :
    (terminalInstrument hc JA L hL).operation () univ (padNuclear JA (nuclearMatrix X)) =
      nuclearMatrix (L * X * L.conjTranspose) := by
  rw [terminalInstrument_univ_nuclear, sandwich_nuclearMatrix]

theorem terminalInstrument_singleton (hc : 0 < c)
    (JA : FiniteSource a →ₗᵢ[ℂ] CommonHilbert)
    (L : Matrix (Fin c) (Fin a) ℂ) (hL : L.conjTranspose * L = 1)
    (X : Matrix (Fin a) (Fin a) ℂ) :
    (terminalInstrument hc JA L hL).operation () {()} (padNuclear JA (nuclearMatrix X)) =
      nuclearMatrix (L * X * L.conjTranspose) := by
  rw [terminalInstrument_on_code]
  simp only [mem_singleton, ite_true, sandwich_nuclearMatrix]

theorem terminalInstrument_code_comp (hc : 0 < c)
    (JA : FiniteSource a →ₗᵢ[ℂ] CommonHilbert)
    (L : Matrix (Fin c) (Fin a) ℂ) (hL : L.conjTranspose * L = 1) :
    ((terminalInstrument hc JA L hL).operation () univ).comp (padNuclear JA) =
      sandwich (matrixCLM L) := by
  ext T
  exact terminalInstrument_univ_nuclear hc JA L hL T

theorem terminalInstrument_finite_reference (hc : 0 < c)
    (JA : FiniteSource a →ₗᵢ[ℂ] CommonHilbert)
    (L : Matrix (Fin c) (Fin a) ℂ) (hL : L.conjTranspose * L = 1)
    (R : Type) [Fintype R] [DecidableEq R]
    (T : Nuclear (BlockSpace R (FiniteSource a))) :
    normalAmplification ((terminalInstrument hc JA L hL).operation () univ)
      (normalAmplification (padNuclear JA) T) =
        normalAmplification (sandwich (matrixCLM L)) T := by
  rw [← normalAmplification_comp, terminalInstrument_code_comp]

end QuantumProver.WernerEndpoint.MatrixFiniteNormalTerminal

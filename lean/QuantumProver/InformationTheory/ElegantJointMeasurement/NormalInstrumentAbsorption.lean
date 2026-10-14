import Mathlib
import QuantumProver.InformationTheory.ElegantJointMeasurement.NormalCPInstruments
import QuantumProver.InformationTheory.ElegantJointMeasurement.SeparableHilbertEmbedding
import QuantumProver.LinearAlgebra.HilbertNuclearCompressionExpansion

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000

open MeasureTheory Set Filter Function InnerProductSpace
open scoped BigOperators Topology ComplexOrder Matrix.Norms.L2Operator

namespace QuantumProver.ElegantJointMeasurement.NormalInstrumentAbsorption

open QuantumProver.ElegantJointMeasurement.HilbertChoi QuantumProver.ElegantJointMeasurement.NuclearChoi QuantumProver.ElegantJointMeasurement.NormalCPInstruments
open QuantumProver.NuclearOperator (toOperator toOperator_injective)
open QuantumProver.HilbertNuclearCompression

local infixr:25 " →ₛ " => MeasureTheory.SimpleFunc

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable {R : Type} [Fintype R] [DecidableEq R]

abbrev NormalOperation (F E : Type*)
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] :=
  QuantumProver.ElegantJointMeasurement.NuclearChoi.Nuclear F →L[ℂ] QuantumProver.ElegantJointMeasurement.NuclearChoi.Nuclear E

def nuclearBlock (i j : R) : Nuclear (BlockSpace R E) →L[ℂ] Nuclear E :=
  compose (PiLp.proj 2 (fun _ : R => E) i) (QuantumProver.ElegantJointMeasurement.HilbertChoi.insert j)

def nuclearAssembly (A : R → R → Nuclear E) : Nuclear (BlockSpace R E) :=
  ∑ i, ∑ j, compose (QuantumProver.ElegantJointMeasurement.HilbertChoi.insert i) (PiLp.proj 2 (fun _ : R => E) j) (A i j)

theorem toOperator_nuclearBlock (i j : R) (T : Nuclear (BlockSpace R E)) :
    toOperator (nuclearBlock i j T) =
      (PiLp.proj 2 (fun _ : R => E) i) ∘L toOperator T ∘L QuantumProver.ElegantJointMeasurement.HilbertChoi.insert j :=
  toOperator_compose _ _ _

theorem toOperator_nuclearAssembly (A : R → R → Nuclear E) :
    toOperator (nuclearAssembly A) = blockOperator (fun i j => toOperator (A i j)) := by
  simp only [nuclearAssembly, map_sum, toOperator_compose]
  rfl

@[simp] theorem nuclearBlock_nuclearAssembly (A : R → R → Nuclear E) (i j : R) :
    nuclearBlock i j (nuclearAssembly A) = A i j := by
  apply toOperator_injective
  rw [toOperator_nuclearBlock, toOperator_nuclearAssembly]
  exact blockOperator_block _ _ _

theorem nuclearAssembly_nuclearBlock (T : Nuclear (BlockSpace R E)) :
    nuclearAssembly (fun i j => nuclearBlock i j T) = T := by
  apply toOperator_injective
  rw [toOperator_nuclearAssembly]
  ext x i
  rw [blockOperator_apply]
  simp only [toOperator_nuclearBlock, ContinuousLinearMap.comp_apply, PiLp.proj_apply]
  have hx : (∑ j : R, QuantumProver.ElegantJointMeasurement.HilbertChoi.insert j (x j)) = x := by
    ext j
    simp [insert_apply_apply]
  have he := congrArg (fun z => PiLp.proj (𝕜 := ℂ) 2 (fun _ : R => E) i (toOperator T z)) hx
  simpa only [map_sum, PiLp.proj_apply] using he

def normalAmplification (Φ : NormalOperation F E) :
    Nuclear (BlockSpace R F) →L[ℂ] Nuclear (BlockSpace R E) :=
  ∑ i, ∑ j,
    (compose (QuantumProver.ElegantJointMeasurement.HilbertChoi.insert (E := E) i) (PiLp.proj 2 (fun _ : R => E) j)).comp
      (Φ.comp (nuclearBlock (E := F) i j))

theorem normalAmplification_apply (Φ : NormalOperation F E)
    (T : Nuclear (BlockSpace R F)) :
    normalAmplification Φ T =
      nuclearAssembly (fun i j => Φ (nuclearBlock i j T)) := by
  simp [normalAmplification, nuclearAssembly]

def NormalCompletelyPositive (Φ : NormalOperation F E) : Prop :=
  ∀ (R : Type) [Fintype R] [DecidableEq R]
    (T : Nuclear (BlockSpace R F)), (toOperator T).IsPositive →
      (toOperator (normalAmplification Φ T)).IsPositive

variable {I : Type} [Fintype I] [DecidableEq I]

def finiteAmplification (ρ : PhysicalOperation I F)
    (X : Matrix (R × I) (R × I) ℂ) : Nuclear (BlockSpace R F) :=
  nuclearAssembly (fun r s => ∑ i, ∑ j, X (r,i) (s,j) • ρ (matrixUnit i j))

theorem toOperator_finiteAmplification (ρ : PhysicalOperation I F)
    (X : Matrix (R × I) (R × I) ℂ) :
    toOperator (finiteAmplification ρ X) =
      amplification (operationOperator ρ.toLinearMap) X := by
  rw [finiteAmplification, toOperator_nuclearAssembly]
  simp only [map_sum, map_smul]
  rfl

theorem normalAmplification_finiteAmplification (Φ : NormalOperation F E)
    (ρ : PhysicalOperation I F) (X : Matrix (R × I) (R × I) ℂ) :
    normalAmplification Φ (finiteAmplification ρ X) =
      finiteAmplification (Φ.comp ρ) X := by
  rw [normalAmplification_apply]
  simp only [finiteAmplification, nuclearBlock_nuclearAssembly, map_sum, map_smul,
    ContinuousLinearMap.comp_apply]

theorem completelyPositive_comp (Φ : NormalOperation F E)
    (hΦ : NormalCompletelyPositive Φ) (ρ : PhysicalOperation I F)
    (hρ : CompletelyPositive (operationOperator ρ.toLinearMap)) :
    CompletelyPositive (operationOperator (Φ.comp ρ).toLinearMap) := by
  intro R _ _ X hX
  rw [← toOperator_finiteAmplification, ← normalAmplification_finiteAmplification]
  exact hΦ R (finiteAmplification ρ X)
    (by rw [toOperator_finiteAmplification]; exact hρ R X hX)

variable {H Ω : Type*} [MeasurableSpace H] [MeasurableSpace Ω]

structure Instrument (F E H Ω : Type*)
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [MeasurableSpace H] [MeasurableSpace Ω] where
  operation : H → Set Ω → NormalOperation F E
  empty : ∀ h, operation h ∅ = 0
  countable_additivity : ∀ h (s : ℕ → Set Ω), (∀ n, MeasurableSet (s n)) →
    Pairwise (Disjoint on s) → ∀ T : Nuclear F,
      HasSum (fun n => operation h (s n) T) (operation h (⋃ n, s n) T)
  completelyPositive : ∀ h s, MeasurableSet s → NormalCompletelyPositive (operation h s)
  measurable_coordinate : ∀ s, MeasurableSet s → ∀ (T : Nuclear F) (x y : E),
    Measurable (fun h => inner ℂ x (toOperator (operation h s T) y))
  trace_preserving : ∀ h T,
    QuantumProver.HilbertNuclearTrace.trace (operation h univ T) =
      QuantumProver.HilbertNuclearTrace.trace T

local instance nuclearMeasurableE : MeasurableSpace (Nuclear E) := borel (Nuclear E)
local instance nuclearBorelE : BorelSpace (Nuclear E) := ⟨rfl⟩
local instance nuclearMeasurableF : MeasurableSpace (Nuclear F) := borel (Nuclear F)
local instance nuclearBorelF : BorelSpace (Nuclear F) := ⟨rfl⟩
local instance operationMeasurableE : MeasurableSpace (PhysicalOperation I E) :=
  borel (PhysicalOperation I E)
local instance operationBorelE : BorelSpace (PhysicalOperation I E) := ⟨rfl⟩
local instance operationPseudoMetricE : PseudoMetricSpace (PhysicalOperation I E) :=
  ContinuousLinearMap.toPseudoMetricSpace

theorem stronglyMeasurable_of_weak_coordinates [TopologicalSpace.SeparableSpace E]
    (T : H → Nuclear E)
    (hT : ∀ x y : E, Measurable (fun h => inner ℂ x (toOperator (T h) y))) :
    StronglyMeasurable T := by
  let J : E →ₗᵢ[ℂ] QuantumProver.ElegantJointMeasurement.SeparableHilbertEmbedding.CommonHilbert :=
    QuantumProver.ElegantJointMeasurement.SeparableHilbertEmbedding.separableEmbedding
  let V := J.toContinuousLinearMap
  have hp : StronglyMeasurable (fun h => QuantumProver.ElegantJointMeasurement.SeparableHilbertEmbedding.padNuclear J (T h)) := by
    apply QuantumProver.HilbertNuclearCompressionExpansion.stronglyMeasurable_of_coordinates
      QuantumProver.ElegantJointMeasurement.SeparableHilbertEmbedding.commonBasis
    intro i j
    simp only [QuantumProver.ElegantJointMeasurement.SeparableHilbertEmbedding.toOperator_padNuclear,
      ContinuousLinearMap.comp_apply]
    change Measurable (fun h => inner ℂ
      (QuantumProver.ElegantJointMeasurement.SeparableHilbertEmbedding.commonBasis i)
      (V (toOperator (T h) (V.adjoint (QuantumProver.ElegantJointMeasurement.SeparableHilbertEmbedding.commonBasis j)))))
    have he : (fun h => inner ℂ (QuantumProver.ElegantJointMeasurement.SeparableHilbertEmbedding.commonBasis i)
        (V (toOperator (T h) (V.adjoint (QuantumProver.ElegantJointMeasurement.SeparableHilbertEmbedding.commonBasis j))))) =
        (fun h => inner ℂ (V.adjoint (QuantumProver.ElegantJointMeasurement.SeparableHilbertEmbedding.commonBasis i))
          (toOperator (T h) (V.adjoint (QuantumProver.ElegantJointMeasurement.SeparableHilbertEmbedding.commonBasis j)))) := by
      funext h
      exact (V.adjoint_inner_left _ _).symm
    rw [he]
    exact hT _ _
  have hr := (QuantumProver.ElegantJointMeasurement.SeparableHilbertEmbedding.recoverNuclear J).continuous.comp_stronglyMeasurable hp
  simpa only [QuantumProver.ElegantJointMeasurement.SeparableHilbertEmbedding.recover_padNuclear] using hr

theorem stronglyMeasurable_variable_apply
    {A B : Type*} [NormedAddCommGroup A] [NormedSpace ℂ A]
    [NormedAddCommGroup B] [NormedSpace ℂ B]
    (L : H → A →L[ℂ] B)
    (hL : ∀ x : A, StronglyMeasurable (fun h => L h x))
    (X : H → A) (hX : StronglyMeasurable X) :
    StronglyMeasurable (fun h => L h (X h)) := by
  classical
  have hs (f : H →ₛ A) : StronglyMeasurable (fun h => L h (f h)) := by
    induction f using SimpleFunc.induction' with
    | const x => simpa only [SimpleFunc.coe_const, Function.const_apply] using hL x
    | @pcw f g s hm hf hg =>
      have he : (fun h => L h (f.piecewise s hm g h)) =
          Set.piecewise s (fun h => L h (f h)) (fun h => L h (g h)) := by
        funext h
        simp only [SimpleFunc.coe_piecewise, Set.piecewise]
        split_ifs <;> rfl
      rw [he]
      exact hf.piecewise hm hg
  apply stronglyMeasurable_of_tendsto (Filter.atTop : Filter ℕ)
    (fun n => hs (hX.approx n))
  apply tendsto_pi_nhds.mpr
  intro h
  exact (L h).continuous.tendsto (X h) |>.comp (hX.tendsto_approx h)

namespace Instrument

variable (P : Instrument F E H Ω)

theorem stronglyMeasurable_operation [TopologicalSpace.SeparableSpace E]
    (s : Set Ω) (hs : MeasurableSet s) (T : Nuclear F) :
    StronglyMeasurable (fun h => P.operation h s T) :=
  stronglyMeasurable_of_weak_coordinates _ (P.measurable_coordinate s hs T)

theorem stronglyMeasurable_operation_variable [TopologicalSpace.SeparableSpace E]
    (s : Set Ω) (hs : MeasurableSet s) (T : H → Nuclear F) (hT : StronglyMeasurable T) :
    StronglyMeasurable (fun h => P.operation h s (T h)) :=
  stronglyMeasurable_variable_apply _ (fun X => P.stronglyMeasurable_operation s hs X) T hT

end Instrument

def matrixEntry (i j : I) : Matrix I I ℂ →L[ℂ] ℂ :=
  (show Matrix I I ℂ →ₗ[ℂ] ℂ from
    { toFun := fun X => X i j
      map_add' := fun X Y => rfl
      map_smul' := fun c X => rfl }).toContinuousLinearMap

def operationFromUnits (A : I → I → Nuclear E) : PhysicalOperation I E :=
  ∑ i, ∑ j, ContinuousLinearMap.smulRightL ℂ (Matrix I I ℂ) (Nuclear E)
    (matrixEntry i j) (A i j)

theorem operationFromUnits_apply (A : I → I → Nuclear E) (X : Matrix I I ℂ) :
    operationFromUnits A X = ∑ i, ∑ j, X i j • A i j := by
  simp [operationFromUnits, matrixEntry]
  rfl

theorem operation_eq_operationFromUnits (Φ : PhysicalOperation I E) :
    Φ = operationFromUnits (fun i j => Φ (matrixUnit i j)) := by
  ext X
  rw [operationFromUnits_apply]
  conv_lhs => rw [matrix_decomposition X]
  simp only [map_sum, map_smul]

theorem stronglyMeasurable_operation_of_units (Φ : H → PhysicalOperation I E)
    (hΦ : ∀ i j, StronglyMeasurable (fun h => Φ h (matrixUnit i j))) :
    StronglyMeasurable Φ := by
  have he : Φ = fun h => operationFromUnits (fun i j => Φ h (matrixUnit i j)) :=
    funext fun h => operation_eq_operationFromUnits (Φ h)
  rw [he]
  unfold operationFromUnits
  apply Finset.stronglyMeasurable_fun_sum
  intro i hi
  apply Finset.stronglyMeasurable_fun_sum
  intro j hj
  exact (ContinuousLinearMap.smulRightL ℂ (Matrix I I ℂ) (Nuclear E)
    (matrixEntry i j)).continuous.comp_stronglyMeasurable (hΦ i j)

def absorbInstrument [TopologicalSpace.SeparableSpace E]
    (P : Instrument F E H Ω) (ρ : H → PhysicalOperation I F)
    (hρcp : ∀ h, CompletelyPositive (operationOperator (ρ h).toLinearMap))
    (hρmeas : ∀ X, StronglyMeasurable (fun h => ρ h X))
    (hρtrace : ∀ h X, QuantumProver.HilbertNuclearTrace.trace (ρ h X) = Matrix.trace X) :
    QuantumProver.ElegantJointMeasurement.NormalCPInstruments.Instrument I E H Ω where
  operation h s := (P.operation h s).comp (ρ h)
  empty h := by ext X; simp only [P.empty, ContinuousLinearMap.comp_apply, ContinuousLinearMap.zero_apply]
  countable_additivity h s hs hd X := P.countable_additivity h s hs hd (ρ h X)
  completelyPositive h s hs := completelyPositive_comp _ (P.completelyPositive h s hs) _ (hρcp h)
  measurable_operation s hs := by
    let A : H → PhysicalOperation I E := fun h => (P.operation h s).comp (ρ h)
    have hm : StronglyMeasurable A := stronglyMeasurable_operation_of_units A (fun i j =>
      P.stronglyMeasurable_operation_variable s hs _ (hρmeas (matrixUnit i j)))
    exact hm.measurable
  trace_preserving h X := by
    rw [ContinuousLinearMap.comp_apply, P.trace_preserving]
    exact hρtrace h X

@[simp] theorem absorbInstrument_operation [TopologicalSpace.SeparableSpace E]
    (P : Instrument F E H Ω) (ρ : H → PhysicalOperation I F)
    (hρcp : ∀ h, CompletelyPositive (operationOperator (ρ h).toLinearMap))
    (hρmeas : ∀ X, StronglyMeasurable (fun h => ρ h X))
    (hρtrace : ∀ h X, QuantumProver.HilbertNuclearTrace.trace (ρ h X) = Matrix.trace X)
    (h : H) (s : Set Ω) (X : Matrix I I ℂ) :
    (absorbInstrument P ρ hρcp hρmeas hρtrace).operation h s X =
      P.operation h s (ρ h X) := rfl

end QuantumProver.ElegantJointMeasurement.NormalInstrumentAbsorption

import QuantumProver.InformationTheory.ElegantJointMeasurement.NuclearChoi
import QuantumProver.LinearAlgebra.HilbertNuclearCompression

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000

open MeasureTheory ProbabilityTheory Set Filter Function
open scoped BigOperators InnerProduct ComplexOrder ENNReal Topology Matrix.Norms.L2Operator

namespace QuantumProver.ElegantJointMeasurement.NormalCPInstruments

open QuantumProver.ElegantJointMeasurement.HilbertChoi QuantumProver.ElegantJointMeasurement.NuclearChoi

variable {I : Type} [Fintype I] [DecidableEq I]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

abbrev PhysicalOperation (I : Type*) (E : Type*) [Fintype I] [DecidableEq I]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] :=
  Matrix I I ℂ →L[ℂ] Nuclear E

local instance nuclearMeasurable : MeasurableSpace (Nuclear E) := borel (Nuclear E)
local instance nuclearBorel : BorelSpace (Nuclear E) := ⟨rfl⟩
local instance operationMeasurable : MeasurableSpace (PhysicalOperation I E) :=
  borel (PhysicalOperation I E)
local instance operationBorel : BorelSpace (PhysicalOperation I E) := ⟨rfl⟩

theorem ofAtom_eq_rankOne (a : QuantumProver.NuclearOperator.Atom ℂ E E) :
    QuantumProver.NuclearOperator.ofAtom a = QuantumProver.NuclearOperator.rankOne a.1.1 a.2.1 := by
  apply QuantumProver.NuclearOperator.toOperator_injective
  simp only [QuantumProver.NuclearOperator.toOperator_ofAtom, QuantumProver.NuclearOperator.toOperator_rankOne, QuantumProver.NuclearOperator.atomOperator]

theorem trace_compose_cycle {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℂ F] [CompleteSpace F]
    (L : E →L[ℂ] F) (R : F →L[ℂ] E) (A : Nuclear E) :
    QuantumProver.HilbertNuclearTrace.trace (QuantumProver.HilbertNuclearCompression.compose L R A) =
      QuantumProver.HilbertNuclearTrace.trace (QuantumProver.HilbertNuclearCompression.compose (ContinuousLinearMap.id ℂ E) (R ∘L L) A) := by
  obtain ⟨c, rfl⟩ := QuantumProver.NuclearOperator.ofCoefficients_surjective A
  have hs := QuantumProver.NuclearOperator.hasSum_ofCoefficients c
  have hleft := hs.mapL ((QuantumProver.HilbertNuclearTrace.trace (𝕜 := ℂ) (E := F)).comp (QuantumProver.HilbertNuclearCompression.compose L R))
  have hright := hs.mapL ((QuantumProver.HilbertNuclearTrace.trace (𝕜 := ℂ) (E := E)).comp
    (QuantumProver.HilbertNuclearCompression.compose (ContinuousLinearMap.id ℂ E) (R ∘L L)))
  have heq : (fun a => QuantumProver.HilbertNuclearTrace.trace (QuantumProver.HilbertNuclearCompression.compose L R (c a • QuantumProver.NuclearOperator.ofAtom a))) =
      (fun a => QuantumProver.HilbertNuclearTrace.trace (QuantumProver.HilbertNuclearCompression.compose (ContinuousLinearMap.id ℂ E)
        (R ∘L L) (c a • QuantumProver.NuclearOperator.ofAtom a))) := by
    funext a
    simp only [map_smul, ofAtom_eq_rankOne, QuantumProver.HilbertNuclearCompression.compose_rankOne, QuantumProver.HilbertNuclearTrace.trace_rankOne]
    rfl
  exact (heq ▸ hleft).unique hright

theorem trace_block (i j : I) (A : Nuclear E) :
    QuantumProver.HilbertNuclearTrace.trace (QuantumProver.HilbertNuclearCompression.compose (QuantumProver.ElegantJointMeasurement.HilbertChoi.insert i) (PiLp.proj 2 (fun _ : I => E) j) A) =
      if i = j then QuantumProver.HilbertNuclearTrace.trace A else 0 := by
  rw [trace_compose_cycle]
  have hproj : (PiLp.proj 2 (fun _ : I => E) j) ∘L QuantumProver.ElegantJointMeasurement.HilbertChoi.insert i =
      if i = j then ContinuousLinearMap.id ℂ E else 0 := by
    ext x
    by_cases hij : i = j
    · subst j
      simp [insert_apply_apply]
    · simp [insert_apply_apply, hij, Ne.symm hij]
  rw [hproj]
  split_ifs with hij
  · congr 1
    apply QuantumProver.NuclearOperator.toOperator_injective
    simp
  · have hz : QuantumProver.HilbertNuclearCompression.compose (ContinuousLinearMap.id ℂ E) (0 : E →L[ℂ] E) A = 0 := by
      apply QuantumProver.NuclearOperator.toOperator_injective
      simp
    simp [hz]

def choiMap : PhysicalOperation I E →L[ℂ] Nuclear (BlockSpace I E) :=
  ∑ i, ∑ j, (QuantumProver.HilbertNuclearCompression.compose (QuantumProver.ElegantJointMeasurement.HilbertChoi.insert i) (PiLp.proj 2 (fun _ : I => E) j)).comp
    (ContinuousLinearMap.apply ℂ (Nuclear E) (matrixUnit i j))

def nuclearChoi (Φ : PhysicalOperation I E) : Nuclear (BlockSpace I E) := choiMap Φ

theorem nuclearChoi_eq (Φ : PhysicalOperation I E) :
    nuclearChoi Φ = ∑ i, ∑ j,
      QuantumProver.HilbertNuclearCompression.compose (QuantumProver.ElegantJointMeasurement.HilbertChoi.insert i) (PiLp.proj 2 (fun _ : I => E) j) (Φ (matrixUnit i j)) := by
  simp [nuclearChoi, choiMap]

theorem toOperator_nuclearChoi (Φ : PhysicalOperation I E) :
    QuantumProver.NuclearOperator.toOperator (nuclearChoi Φ) = choi (operationOperator Φ.toLinearMap) := by
  rw [nuclearChoi_eq]
  simp only [map_sum, QuantumProver.HilbertNuclearCompression.toOperator_compose]
  rfl

theorem nuclearChoi_isPositive (Φ : PhysicalOperation I E)
    (hΦ : CompletelyPositive (operationOperator Φ.toLinearMap)) :
    (QuantumProver.NuclearOperator.toOperator (nuclearChoi Φ)).IsPositive := by
  rw [toOperator_nuclearChoi]
  exact choi_isPositive _ hΦ

theorem sum_diagonal_matrixUnit : (∑ i : I, matrixUnit i i) = (1 : Matrix I I ℂ) := by
  ext i j
  simp [matrixUnit, Matrix.single, Matrix.one_apply, Matrix.sum_apply, ite_and]

theorem trace_nuclearChoi (Φ : PhysicalOperation I E) :
    QuantumProver.HilbertNuclearTrace.trace (nuclearChoi Φ) = QuantumProver.HilbertNuclearTrace.trace (Φ 1) := by
  rw [nuclearChoi_eq]
  simp only [map_sum, trace_block]
  calc
    (∑ i, ∑ j, if i = j then QuantumProver.HilbertNuclearTrace.trace (Φ (matrixUnit i j)) else 0) =
        ∑ i, QuantumProver.HilbertNuclearTrace.trace (Φ (matrixUnit i i)) := by simp
    _ = QuantumProver.HilbertNuclearTrace.trace (Φ (∑ i, matrixUnit i i)) := by simp only [map_sum]
    _ = QuantumProver.HilbertNuclearTrace.trace (Φ 1) := by rw [sum_diagonal_matrixUnit]

theorem re_trace_nonneg_of_positive (A : Nuclear E)
    (hA : (QuantumProver.NuclearOperator.toOperator A).IsPositive) : 0 ≤ (QuantumProver.HilbertNuclearTrace.trace A).re := by
  obtain ⟨ι, b, hb⟩ := exists_hilbertBasis ℂ E
  rw [← norm_positive_nuclear_eq_re_trace b A hA]
  exact norm_nonneg A

variable {H Ω : Type*} [MeasurableSpace H] [MeasurableSpace Ω]

structure Instrument (I : Type) (E H Ω : Type*) [Fintype I] [DecidableEq I]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [MeasurableSpace H] [MeasurableSpace Ω] where
  operation : H → Set Ω → PhysicalOperation I E
  empty : ∀ h, operation h ∅ = 0
  countable_additivity : ∀ h (s : ℕ → Set Ω), (∀ n, MeasurableSet (s n)) →
    Pairwise (Disjoint on s) → ∀ X : Matrix I I ℂ,
      HasSum (fun n => operation h (s n) X) (operation h (⋃ n, s n) X)
  completelyPositive : ∀ h s, MeasurableSet s →
    CompletelyPositive (operationOperator (operation h s).toLinearMap)
  measurable_operation : ∀ s, MeasurableSet s → Measurable (fun h => operation h s)
  trace_preserving : ∀ h X, QuantumProver.HilbertNuclearTrace.trace (operation h univ X) = Matrix.trace X

namespace Instrument

variable (P : Instrument I E H Ω)

def physicalChoi (h : H) (s : Set Ω) : Nuclear (BlockSpace I E) :=
  nuclearChoi (P.operation h s)

theorem physicalChoi_isPositive (h : H) (s : Set Ω) (hs : MeasurableSet s) :
    (QuantumProver.NuclearOperator.toOperator (P.physicalChoi h s)).IsPositive :=
  nuclearChoi_isPositive _ (P.completelyPositive h s hs)

@[simp] theorem physicalChoi_empty (h : H) : P.physicalChoi h ∅ = 0 := by
  simp [physicalChoi, nuclearChoi, P.empty]

theorem physicalChoi_hasSum (h : H) (s : ℕ → Set Ω)
    (hs : ∀ n, MeasurableSet (s n)) (hd : Pairwise (Disjoint on s)) :
    HasSum (fun n => P.physicalChoi h (s n)) (P.physicalChoi h (⋃ n, s n)) := by
  have hlocal (i j : I) :
      HasSum (fun n => QuantumProver.HilbertNuclearCompression.compose (QuantumProver.ElegantJointMeasurement.HilbertChoi.insert i)
        (PiLp.proj 2 (fun _ : I => E) j) (P.operation h (s n) (matrixUnit i j)))
        (QuantumProver.HilbertNuclearCompression.compose (QuantumProver.ElegantJointMeasurement.HilbertChoi.insert i)
          (PiLp.proj 2 (fun _ : I => E) j) (P.operation h (⋃ n, s n) (matrixUnit i j))) :=
    by
      let block : Nuclear E →L[ℂ] Nuclear (BlockSpace I E) :=
        QuantumProver.HilbertNuclearCompression.compose
          (QuantumProver.ElegantJointMeasurement.HilbertChoi.insert (E := E) i)
          (PiLp.proj 2 (fun _ : I => E) j)
      change HasSum (fun n => block (P.operation h (s n) (matrixUnit i j)))
        (block (P.operation h (⋃ n, s n) (matrixUnit i j)))
      exact block.hasSum (P.countable_additivity h s hs hd (matrixUnit i j))
  have hrow (i : I) :
      HasSum (fun n => ∑ j : I, QuantumProver.HilbertNuclearCompression.compose
        (QuantumProver.ElegantJointMeasurement.HilbertChoi.insert i) (PiLp.proj 2 (fun _ : I => E) j)
        (P.operation h (s n) (matrixUnit i j)))
        (∑ j : I, QuantumProver.HilbertNuclearCompression.compose
          (QuantumProver.ElegantJointMeasurement.HilbertChoi.insert i) (PiLp.proj 2 (fun _ : I => E) j)
          (P.operation h (⋃ n, s n) (matrixUnit i j))) :=
    hasSum_sum (s := Finset.univ) (fun j hj => hlocal i j)
  simp only [physicalChoi, nuclearChoi_eq]
  exact hasSum_sum (s := Finset.univ) (fun i hi => hrow i)

theorem measurable_physicalChoi (s : Set Ω) (hs : MeasurableSet s) :
    Measurable (fun h => P.physicalChoi h s) :=
  (choiMap.continuous.measurable).comp (P.measurable_operation s hs)

theorem trace_physicalChoi (h : H) (s : Set Ω) :
    QuantumProver.HilbertNuclearTrace.trace (P.physicalChoi h s) = QuantumProver.HilbertNuclearTrace.trace (P.operation h s 1) :=
  trace_nuclearChoi _

@[simp] theorem trace_physicalChoi_univ (h : H) :
    QuantumProver.HilbertNuclearTrace.trace (P.physicalChoi h univ) = (Fintype.card I : ℂ) := by
  rw [trace_physicalChoi, P.trace_preserving, Matrix.trace_one]

def referenceMass (h : H) (s : Set Ω) : ℝ :=
  (QuantumProver.HilbertNuclearTrace.trace (P.physicalChoi h s)).re / (Fintype.card I : ℝ)

theorem referenceMass_nonneg (h : H) (s : Set Ω) (hs : MeasurableSet s) :
    0 ≤ P.referenceMass h s :=
  div_nonneg (re_trace_nonneg_of_positive _ (P.physicalChoi_isPositive h s hs))
    (Nat.cast_nonneg _)

@[simp] theorem referenceMass_empty (h : H) : P.referenceMass h ∅ = 0 := by
  simp [referenceMass]

variable [Nonempty I]

@[simp] theorem referenceMass_univ (h : H) : P.referenceMass h univ = 1 := by
  simp [referenceMass, Fintype.card_ne_zero]

theorem referenceMass_hasSum (h : H) (s : ℕ → Set Ω)
    (hs : ∀ n, MeasurableSet (s n)) (hd : Pairwise (Disjoint on s)) :
    HasSum (fun n => P.referenceMass h (s n)) (P.referenceMass h (⋃ n, s n)) := by
  have ht := ((P.physicalChoi_hasSum h s hs hd).mapL
    (QuantumProver.HilbertNuclearTrace.trace (𝕜 := ℂ) (E := BlockSpace I E))).mapL Complex.reCLM
  exact ht.div_const (Fintype.card I : ℝ)

theorem measurable_referenceMass (s : Set Ω) (hs : MeasurableSet s) :
    Measurable (fun h => P.referenceMass h s) :=
  ((Complex.continuous_re.measurable).comp
    (QuantumProver.HilbertNuclearTrace.trace.continuous.measurable.comp (P.measurable_physicalChoi s hs))).div_const _

def referenceMeasure (h : H) : Measure Ω :=
  Measure.ofMeasurable (fun s hs => ENNReal.ofReal (P.referenceMass h s))
    (by simp) (by
      intro s hs hd
      have ht := P.referenceMass_hasSum h s hs hd
      rw [← ht.tsum_eq, ENNReal.ofReal_tsum_of_nonneg
        (fun n => P.referenceMass_nonneg h (s n) (hs n)) ht.summable])

theorem referenceMeasure_apply (h : H) (s : Set Ω) (hs : MeasurableSet s) :
    P.referenceMeasure h s = ENNReal.ofReal (P.referenceMass h s) :=
  Measure.ofMeasurable_apply _ hs

@[simp] theorem referenceMeasure_univ (h : H) : P.referenceMeasure h univ = 1 := by
  rw [referenceMeasure_apply _ _ _ MeasurableSet.univ, referenceMass_univ]
  simp

instance isProbabilityMeasure_referenceMeasure (h : H) :
    IsProbabilityMeasure (P.referenceMeasure h) := ⟨P.referenceMeasure_univ h⟩

def referenceKernel : Kernel H Ω where
  toFun := P.referenceMeasure
  measurable' := Measure.measurable_of_measurable_coe _ (fun s hs => by
    simp only [referenceMeasure_apply _ _ _ hs]
    exact ENNReal.continuous_ofReal.measurable.comp (P.measurable_referenceMass s hs))

@[simp] theorem referenceKernel_apply (h : H) : P.referenceKernel h = P.referenceMeasure h := rfl

instance isMarkovKernel_referenceKernel : IsMarkovKernel P.referenceKernel :=
  ⟨fun h => P.isProbabilityMeasure_referenceMeasure h⟩

theorem norm_physicalChoi_eq_reference (h : H) (s : Set Ω) (hs : MeasurableSet s) :
    ‖P.physicalChoi h s‖ = (Fintype.card I : ℝ) * (P.referenceKernel h s).toReal := by
  obtain ⟨ι, b, hb⟩ := exists_hilbertBasis ℂ (BlockSpace I E)
  rw [norm_positive_nuclear_eq_re_trace b _ (P.physicalChoi_isPositive h s hs),
    referenceKernel_apply, referenceMeasure_apply _ _ _ hs,
    ENNReal.toReal_ofReal (P.referenceMass_nonneg h s hs), referenceMass]
  exact (mul_div_cancel₀ _ (by exact_mod_cast Fintype.card_ne_zero (α := I))).symm

end Instrument
end QuantumProver.ElegantJointMeasurement.NormalCPInstruments

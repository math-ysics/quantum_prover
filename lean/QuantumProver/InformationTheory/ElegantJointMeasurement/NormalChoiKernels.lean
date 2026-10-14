import QuantumProver.InformationTheory.ElegantJointMeasurement.NormalCPInstruments
import QuantumProver.InformationTheory.ElegantJointMeasurement.ContinuousInstrumentRadonNikodym

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000

open MeasureTheory ProbabilityTheory Set Filter Function InnerProductSpace
open scoped BigOperators InnerProduct ComplexOrder ENNReal Topology Matrix.Norms.L2Operator

namespace QuantumProver.ElegantJointMeasurement.NormalChoiKernels

open QuantumProver.ElegantJointMeasurement.HilbertChoi QuantumProver.ElegantJointMeasurement.NuclearChoi QuantumProver.ElegantJointMeasurement.NormalCPInstruments
open QuantumProver.ElegantJointMeasurement.ContinuousInstrumentRadonNikodym

variable {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {H Ω : Type*} [MeasurableSpace H] [MeasurableSpace Ω]

local instance nuclearMeasurable : MeasurableSpace (Nuclear (BlockSpace I E)) :=
  borel (Nuclear (BlockSpace I E))
local instance nuclearBorel : BorelSpace (Nuclear (BlockSpace I E)) := ⟨rfl⟩

namespace Instrument

variable (P : QuantumProver.ElegantJointMeasurement.NormalCPInstruments.Instrument I E H Ω)

def scalarMeasure (q : Nuclear (BlockSpace I E) →L[ℝ] ℝ)
    (hq : ∀ h s, MeasurableSet s → 0 ≤ q (P.physicalChoi h s)) (h : H) : Measure Ω :=
  Measure.ofMeasurable (fun s hs => ENNReal.ofReal (q (P.physicalChoi h s)))
    (by simp) (by
      intro s hs hd
      have ht := q.hasSum (P.physicalChoi_hasSum h s hs hd)
      rw [← ht.tsum_eq, ENNReal.ofReal_tsum_of_nonneg
        (fun n => hq h (s n) (hs n)) ht.summable])

theorem scalarMeasure_apply (q : Nuclear (BlockSpace I E) →L[ℝ] ℝ)
    (hq : ∀ h s, MeasurableSet s → 0 ≤ q (P.physicalChoi h s))
    (h : H) (s : Set Ω) (hs : MeasurableSet s) :
    (scalarMeasure P) q hq h s = ENNReal.ofReal (q (P.physicalChoi h s)) :=
  Measure.ofMeasurable_apply _ hs

def scalarKernel (q : Nuclear (BlockSpace I E) →L[ℝ] ℝ)
    (hq : ∀ h s, MeasurableSet s → 0 ≤ q (P.physicalChoi h s)) : Kernel H Ω where
  toFun := (scalarMeasure P) q hq
  measurable' := Measure.measurable_of_measurable_coe _ (fun s hs => by
    simp only [scalarMeasure_apply _ _ _ _ _ hs]
    exact ENNReal.continuous_ofReal.measurable.comp
      (q.continuous.measurable.comp (P.measurable_physicalChoi s hs)))

theorem scalarKernel_apply (q : Nuclear (BlockSpace I E) →L[ℝ] ℝ)
    (hq : ∀ h s, MeasurableSet s → 0 ≤ q (P.physicalChoi h s))
    (h : H) (s : Set Ω) (hs : MeasurableSet s) :
    (scalarKernel P) q hq h s = ENNReal.ofReal (q (P.physicalChoi h s)) :=
  (scalarMeasure_apply P) q hq h s hs

end Instrument

def quadraticProbe (x : BlockSpace I E) : Nuclear (BlockSpace I E) →L[ℝ] ℝ :=
  let test : Nuclear (BlockSpace I E) →L[ℂ] ℂ :=
    ((innerSL ℂ x).comp (ContinuousLinearMap.apply ℂ (BlockSpace I E) x)).comp
      (QuantumProver.NuclearOperator.toOperator (𝕜 := ℂ) (E := BlockSpace I E)
        (F := BlockSpace I E))
  Complex.reCLM.comp (test.restrictScalars ℝ)

@[simp] theorem quadraticProbe_apply (x : BlockSpace I E) (A : Nuclear (BlockSpace I E)) :
    quadraticProbe x A = (inner ℂ x (QuantumProver.NuclearOperator.toOperator A x)).re := rfl

namespace Instrument

variable (P : QuantumProver.ElegantJointMeasurement.NormalCPInstruments.Instrument I E H Ω)

theorem quadraticProbe_nonneg (x : BlockSpace I E) (h : H) (s : Set Ω)
    (hs : MeasurableSet s) : 0 ≤ quadraticProbe x (P.physicalChoi h s) :=
  (P.physicalChoi_isPositive h s hs).re_inner_nonneg_right x

def physicalProbe (x : BlockSpace I E) : Kernel H Ω :=
  (scalarKernel P) (quadraticProbe x) ((quadraticProbe_nonneg P) x)

theorem physicalProbe_apply (x : BlockSpace I E) (h : H) (s : Set Ω)
    (hs : MeasurableSet s) : (physicalProbe P) x h s =
      ENNReal.ofReal (inner ℂ x (QuantumProver.NuclearOperator.toOperator (P.physicalChoi h s) x)).re :=
  (scalarKernel_apply P) _ _ h s hs

def diagonalKernel (b : HilbertBasis ℕ ℂ (BlockSpace I E)) (n : ℕ) : Kernel H Ω :=
  (physicalProbe P) (b n)

theorem diagonalKernel_tsum (b : HilbertBasis ℕ ℂ (BlockSpace I E))
    (h : H) (s : Set Ω) (hs : MeasurableSet s) :
    (∑' n, (diagonalKernel P) b n h s) =
      ENNReal.ofReal (Fintype.card I : ℝ) * P.referenceKernel h s := by
  have hd := (QuantumProver.HilbertNuclearTrace.hasSum_diagonal b (P.physicalChoi h s)).mapL
    Complex.reCLM
  change HasSum (fun n =>
    (inner ℂ (b n) (QuantumProver.NuclearOperator.toOperator (P.physicalChoi h s) (b n))).re)
    (QuantumProver.HilbertNuclearTrace.trace (P.physicalChoi h s)).re at hd
  have hn (n : ℕ) :
      0 ≤ (inner ℂ (b n) (QuantumProver.NuclearOperator.toOperator (P.physicalChoi h s) (b n))).re :=
    (P.physicalChoi_isPositive h s hs).re_inner_nonneg_right (b n)
  simp only [diagonalKernel, physicalProbe_apply _ _ _ _ hs]
  rw [← ENNReal.ofReal_tsum_of_nonneg hn hd.summable, hd.tsum_eq,
    P.referenceKernel_apply, P.referenceMeasure_apply h s hs,
    ← ENNReal.ofReal_mul (Nat.cast_nonneg (Fintype.card I))]
  congr 1
  rw [QuantumProver.ElegantJointMeasurement.NormalCPInstruments.Instrument.referenceMass]
  exact (mul_div_cancel₀ _ (by exact_mod_cast Fintype.card_ne_zero (α := I))).symm

def physicalBlockEffect (b : HilbertBasis ℕ ℂ (BlockSpace I E)) (n : ℕ)
    (h : H) (s : Set Ω) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => inner ℂ (b i.val)
    (QuantumProver.NuclearOperator.toOperator (P.physicalChoi h s) (b j.val))

theorem physicalBlockEffect_posSemidef (b : HilbertBasis ℕ ℂ (BlockSpace I E))
    (n : ℕ) (h : H) (s : Set Ω) (hs : MeasurableSet s) :
    ((physicalBlockEffect P) b n h s).PosSemidef := by
  let D : BlockSpace I E →L[ℂ] BlockSpace I E :=
    QuantumProver.NuclearOperator.toOperator (P.physicalChoi h s)
  have hD : D.IsPositive := P.physicalChoi_isPositive h s hs
  have heq : (physicalBlockEffect P) b n h s =
      Matrix.gram ℂ (fun i : Fin n => CFC.sqrt D (b i.val)) := by
    ext i j
    change inner ℂ (b i.val) (D (b j.val)) =
      inner ℂ (CFC.sqrt D (b i.val)) (CFC.sqrt D (b j.val))
    calc
      _ = inner ℂ (b i.val) ((CFC.sqrt D).adjoint (CFC.sqrt D (b j.val))) := by
        rw [sqrt_adjoint_eq]
        exact congrArg (fun A : BlockSpace I E →L[ℂ] BlockSpace I E =>
          inner ℂ (b i.val) (A (b j.val))) (sqrt_comp_sqrt D hD).symm
      _ = _ := (CFC.sqrt D).adjoint_inner_right _ _
  rw [heq]
  exact Matrix.posSemidef_gram ℂ _

def blockVector (b : HilbertBasis ℕ ℂ (BlockSpace I E)) (n : ℕ)
    (v : Fin n → ℂ) : BlockSpace I E := ∑ i, v i • b i.val

theorem quadratic_physicalBlockEffect (b : HilbertBasis ℕ ℂ (BlockSpace I E))
    (n : ℕ) (v : Fin n → ℂ) (h : H) (s : Set Ω) :
    quadratic v ((physicalBlockEffect P) b n h s) =
      quadraticProbe (blockVector b n v) (P.physicalChoi h s) := by
  change (dotProduct (star v) (Matrix.mulVec (physicalBlockEffect P b n h s) v)).re =
    (inner ℂ (blockVector b n v)
      (QuantumProver.NuclearOperator.toOperator (P.physicalChoi h s) (blockVector b n v))).re
  apply congrArg Complex.re
  simp only [physicalBlockEffect, blockVector, dotProduct, Matrix.mulVec,
    map_sum, map_smul, inner_sum, sum_inner, inner_smul_left,
    inner_smul_right, Pi.star_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro i hi
  simp only [starRingEnd_apply]
  ring

def finiteChoiKernel (b : HilbertBasis ℕ ℂ (BlockSpace I E)) (n : ℕ) :
    PositiveChoiKernel (H := H) (Ω := Ω) (Q := Fin n) where
  effect := (physicalBlockEffect P) b n
  positive := (physicalBlockEffect_posSemidef P) b n
  probe v := (physicalProbe P) (blockVector b n v)
  probe_apply := by
    intro v h s hs
    rw [(physicalProbe_apply P) _ h s hs, (quadratic_physicalBlockEffect P) b n v h s]
    rfl

@[simp] theorem blockVector_basisVector (b : HilbertBasis ℕ ℂ (BlockSpace I E))
    (n : ℕ) (i : Fin n) : blockVector b n (basisVector i) = b i.val := by
  simp [blockVector, basisVector, Pi.single_apply]

theorem finiteChoiKernel_probe_basisVector (b : HilbertBasis ℕ ℂ (BlockSpace I E))
    (n : ℕ) (i : Fin n) :
    ((finiteChoiKernel P) b n).probe (basisVector i) = (diagonalKernel P) b i.val := by
  change (physicalProbe P) (blockVector b n (basisVector i)) = (physicalProbe P) (b i.val)
  rw [blockVector_basisVector]

theorem finiteChoiKernel_coherent (b : HilbertBasis ℕ ℂ (BlockSpace I E))
    (n m : ℕ) (hnm : n ≤ m) (h : H) (s : Set Ω) (hs : MeasurableSet s)
    (i j : Fin n) :
    ((finiteChoiKernel P) b m).effect h s (Fin.castLE hnm i) (Fin.castLE hnm j) =
      ((finiteChoiKernel P) b n).effect h s i j := rfl

end Instrument
end QuantumProver.ElegantJointMeasurement.NormalChoiKernels

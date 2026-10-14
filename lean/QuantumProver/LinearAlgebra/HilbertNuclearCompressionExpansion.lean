import QuantumProver.LinearAlgebra.HilbertNuclearCompression
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex

set_option autoImplicit false
set_option maxHeartbeats 1200000

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology InnerProductSpace

namespace QuantumProver.HilbertNuclearCompressionExpansion
open NuclearOperator HilbertNuclearCompression HilbertFiniteCompression

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

def coefficientCompression (b : HilbertBasis ι ℂ E) (s : Finset ι)
    (F : ι → ι → ℂ) : Nuclear ℂ E E :=
  ∑ i ∈ s, ∑ j ∈ s, F i j • rankOne (innerSL ℂ (b j)) (b i)

theorem compression_eq_coefficientCompression (b : HilbertBasis ι ℂ E)
    (s : Finset ι) (T : Nuclear ℂ E E) :
    compression b s T = coefficientCompression b s
      (fun i j => inner ℂ (b i) (toOperator T (b j))) := by
  apply toOperator_injective
  ext x
  simp only [toOperator_compression, ContinuousLinearMap.comp_apply,
    finiteProjection_apply, coefficientCompression, map_sum, map_smul,
    toOperator_rankOne, sum_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, inner_sum, inner_smul_right,
    Finset.sum_smul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [mul_comm]

variable {P : Type*} [MeasurableSpace P]

theorem stronglyMeasurable_coefficientCompression (b : HilbertBasis ι ℂ E)
    (s : Finset ι) (F : P → ι → ι → ℂ) (hF : ∀ i j, Measurable (fun p => F p i j)) :
    StronglyMeasurable (fun p => coefficientCompression b s (F p)) := by
  unfold coefficientCompression
  apply Finset.stronglyMeasurable_fun_sum
  intro i hi
  apply Finset.stronglyMeasurable_fun_sum
  intro j hj
  exact (hF i j).stronglyMeasurable.smul_const _

theorem stronglyMeasurable_of_coordinates (b : HilbertBasis ℕ ℂ E)
    (T : P → Nuclear ℂ E E)
    (hT : ∀ i j, Measurable (fun p => inner ℂ (b i) (toOperator (T p) (b j)))) :
    StronglyMeasurable T := by
  apply stronglyMeasurable_of_tendsto (Filter.atTop : Filter ℕ)
    (fun n => stronglyMeasurable_coefficientCompression b (Finset.range n)
      (fun p i j => inner ℂ (b i) (toOperator (T p) (b j))) hT)
  apply tendsto_pi_nhds.mpr
  intro p
  simpa only [← compression_eq_coefficientCompression] using initial_compression_tendsto b (T p)

end QuantumProver.HilbertNuclearCompressionExpansion

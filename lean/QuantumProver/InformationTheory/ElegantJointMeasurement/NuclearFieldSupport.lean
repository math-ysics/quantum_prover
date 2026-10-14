import QuantumProver.InformationTheory.ElegantJointMeasurement.NuclearProjectionSupport
import QuantumProver.InformationTheory.ElegantJointMeasurement.NormalInstrumentAbsorption
import QuantumProver.LinearAlgebra.HilbertNuclearCompressionExpansion
import Mathlib.Topology.Sequences

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 200000

open MeasureTheory Filter Set InnerProductSpace
open scoped BigOperators Topology InnerProduct ComplexOrder

namespace QuantumProver.ElegantJointMeasurement.NuclearFieldSupport

open QuantumProver.NuclearOperator QuantumProver.HilbertNuclearCompression
open QuantumProver.HilbertNuclearCompressionExpansion
open QuantumProver.ElegantJointMeasurement.NuclearProjectionSupport

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {Ω : Type*} [MeasurableSpace Ω]

local instance nuclearNormedGroup : NormedAddCommGroup (Nuclear ℂ H H) := inferInstance
local instance nuclearNormedSpace : NormedSpace ℂ (Nuclear ℂ H H) := inferInstance
local instance rankOneMapNormedGroup : NormedAddCommGroup (H →L[ℂ] Nuclear ℂ H H) := inferInstance
local instance rankOneMapNormedSpace : NormedSpace ℂ (H →L[ℂ] Nuclear ℂ H H) := inferInstance

theorem continuous_nuclearRankOne :
    Continuous (fun p : H × H => rankOne (innerSL ℂ p.2) p.1) := by
  have haux (B : (H →L[ℂ] ℂ) →L[ℂ] H →L[ℂ] Nuclear ℂ H H) :
      Continuous (fun p : H × H => B (innerSL ℂ p.2) p.1) :=
    (B.continuous.comp ((innerSL ℂ).continuous.comp continuous_snd)).clm_apply continuous_fst
  have ht : Continuous (fun p : H × H =>
      QuantumProver.MatrixNuclearTensor.rankOneCLM (innerSL ℂ p.2) p.1) :=
    haux QuantumProver.MatrixNuclearTensor.rankOneCLM
  simpa only [QuantumProver.MatrixNuclearTensor.rankOneCLM_apply] using ht

theorem stronglyMeasurable_nuclearRankOne {x y : Ω → H}
    (hx : StronglyMeasurable x) (hy : StronglyMeasurable y) :
    StronglyMeasurable (fun ω => rankOne (innerSL ℂ (y ω)) (x ω)) := by
  have hxy : StronglyMeasurable (fun ω => (x ω, y ω)) := hx.prodMk hy
  exact Continuous.comp_stronglyMeasurable
    (g := fun p : H × H => rankOne (innerSL ℂ p.2) p.1)
    (f := fun ω : Ω => (x ω, y ω)) (continuous_nuclearRankOne (H := H)) hxy

theorem sandwich_rankOne (P : H →L[ℂ] H) (hAdj : P.adjoint = P) (x y : H) :
    compose P P (rankOne (innerSL ℂ y) x) = rankOne (innerSL ℂ (P y)) (P x) := by
  rw [compose_rankOne]
  have hφ : innerSL ℂ y ∘L P = innerSL ℂ (P y) := by
    ext z
    change inner ℂ y (P z) = inner ℂ (P y) z
    simpa only [hAdj] using (P.adjoint_inner_left z y).symm
  rw [hφ]

variable {ι : Type*}

theorem stronglyMeasurable_sandwich_compression
    (b : HilbertBasis ι ℂ H) (s : Finset ι) (T : Nuclear ℂ H H)
    (P : Ω → H →L[ℂ] H) (hAdj : ∀ ω, (P ω).adjoint = P ω)
    (hP : ∀ x : H, StronglyMeasurable (fun ω => P ω x)) :
    StronglyMeasurable (fun ω => compose (P ω) (P ω) (compression b s T)) := by
  classical
  have he : (fun ω => compose (P ω) (P ω) (compression b s T)) =
      (fun ω => ∑ i ∈ s, ∑ j ∈ s,
        inner ℂ (b i) (toOperator T (b j)) •
          rankOne (innerSL ℂ (P ω (b j))) (P ω (b i))) := by
    funext ω
    rw [compression_eq_coefficientCompression]
    simp only [coefficientCompression, map_sum, map_smul, sandwich_rankOne _ (hAdj ω)]
  rw [he]
  apply Finset.stronglyMeasurable_fun_sum
  intro i hi
  apply Finset.stronglyMeasurable_fun_sum
  intro j hj
  exact (stronglyMeasurable_nuclearRankOne (hP (b i)) (hP (b j))).const_smul
    (inner ℂ (b i) (toOperator T (b j)))

theorem stronglyMeasurable_sandwich_fixed
    (P : Ω → H →L[ℂ] H) (hAdj : ∀ ω, (P ω).adjoint = P ω)
    (hP : ∀ x : H, StronglyMeasurable (fun ω => P ω x)) (T : Nuclear ℂ H H) :
    StronglyMeasurable (fun ω => compose (P ω) (P ω) T) := by
  classical
  obtain ⟨κ, b, hb⟩ := exists_hilbertBasis ℂ H
  have ht : T ∈ closure (range (fun s : Finset κ => compression b s T)) :=
    mem_closure_of_tendsto (compression_tendsto b T)
      (Eventually.of_forall fun s => mem_range_self s)
  obtain ⟨A, hA, hAT⟩ := mem_closure_iff_seq_limit.mp ht
  choose s hs using hA
  have hseq : Tendsto (fun n : ℕ => compression b (s n) T) atTop (𝓝 T) := by
    have he : (fun n : ℕ => compression b (s n) T) = A := funext hs
    rw [he]
    exact hAT
  apply stronglyMeasurable_of_tendsto (atTop : Filter ℕ)
    (fun n => stronglyMeasurable_sandwich_compression b (s n) T P hAdj hP)
  apply tendsto_pi_nhds.mpr
  intro ω
  exact (compose (P ω) (P ω)).continuous.tendsto T |>.comp hseq

theorem stronglyMeasurable_sandwich_variable
    (P : Ω → H →L[ℂ] H) (hAdj : ∀ ω, (P ω).adjoint = P ω)
    (hP : ∀ x : H, StronglyMeasurable (fun ω => P ω x))
    (D : Ω → Nuclear ℂ H H) (hD : StronglyMeasurable D) :
    StronglyMeasurable (fun ω => compose (P ω) (P ω) (D ω)) :=
  QuantumProver.ElegantJointMeasurement.NormalInstrumentAbsorption.stronglyMeasurable_variable_apply
    (fun ω => compose (P ω) (P ω)) (stronglyMeasurable_sandwich_fixed P hAdj hP) D hD

def complementSandwich (P : H →L[ℂ] H) (U : Nuclear ℂ H H) : Nuclear ℂ H H :=
  compose (complement P) (complement P) U

def complementTrace (P : H →L[ℂ] H) (U : Nuclear ℂ H H) : ℝ :=
  (QuantumProver.HilbertNuclearTrace.trace (complementSandwich P U)).re

theorem complementTrace_nonneg (U : Nuclear ℂ H H) (P : H →L[ℂ] H)
    (hU : (toOperator U).IsPositive) (hAdj : P.adjoint = P) :
    0 ≤ complementTrace P U :=
  positive_nuclear_re_trace_nonneg _
    (nuclear_sandwich_isPositive U (complement P) hU (complement_adjoint P hAdj))

theorem complementTrace_le_norm (U : Nuclear ℂ H H) (P : H →L[ℂ] H)
    (hU : (toOperator U).IsPositive) (hAdj : P.adjoint = P) (hId : P.comp P = P) :
    complementTrace P U ≤ ‖U‖ := by
  change (QuantumProver.HilbertNuclearTrace.trace (compose (complement P) (complement P) U)).re ≤ ‖U‖
  rw [complement_trace_identity U P hId]
  exact (sub_le_self _ (positive_nuclear_re_trace_nonneg _
    (nuclear_sandwich_isPositive U P hU hAdj))).trans
      (QuantumProver.HilbertNuclearTrace.re_trace_le_norm U)

theorem norm_complementSandwich_le (U : Nuclear ℂ H H) (P : H →L[ℂ] H)
    (hU : (toOperator U).IsPositive) (hAdj : P.adjoint = P) (hId : P.comp P = P) :
    ‖complementSandwich P U‖ ≤ ‖U‖ := by
  obtain ⟨κ, b, hb⟩ := exists_hilbertBasis ℂ H
  have hp : (toOperator (complementSandwich P U)).IsPositive :=
    nuclear_sandwich_isPositive U (complement P) hU (complement_adjoint P hAdj)
  rw [QuantumProver.ElegantJointMeasurement.NuclearChoi.norm_positive_nuclear_eq_re_trace b _ hp]
  exact complementTrace_le_norm U P hU hAdj hId

theorem stronglyMeasurable_complementSandwich
    (P : Ω → H →L[ℂ] H) (hAdj : ∀ ω, (P ω).adjoint = P ω)
    (hP : ∀ x : H, StronglyMeasurable (fun ω => P ω x))
    (D : Ω → Nuclear ℂ H H) (hD : StronglyMeasurable D) :
    StronglyMeasurable (fun ω => complementSandwich (P ω) (D ω)) := by
  apply stronglyMeasurable_sandwich_variable (fun ω => complement (P ω))
    (fun ω => complement_adjoint _ (hAdj ω)) _ D hD
  intro x
  exact (stronglyMeasurable_const : StronglyMeasurable (fun _ : Ω => x)).sub (hP x)

theorem integrable_complementSandwich (μ : Measure Ω)
    (P : Ω → H →L[ℂ] H) (hAdj : ∀ ω, (P ω).adjoint = P ω)
    (hId : ∀ ω, (P ω).comp (P ω) = P ω)
    (hP : ∀ x : H, StronglyMeasurable (fun ω => P ω x))
    (D : Ω → Nuclear ℂ H H) (hD : StronglyMeasurable D) (hInt : Integrable D μ)
    (hPos : ∀ᵐ ω ∂μ, (toOperator (D ω)).IsPositive) :
    Integrable (fun ω => complementSandwich (P ω) (D ω)) μ := by
  refine hInt.mono (stronglyMeasurable_complementSandwich P hAdj hP D hD).aestronglyMeasurable ?_
  filter_upwards [hPos] with ω hω
  exact norm_complementSandwich_le (D ω) (P ω) hω (hAdj ω) (hId ω)

theorem integrable_complementTrace (μ : Measure Ω)
    (P : Ω → H →L[ℂ] H) (hAdj : ∀ ω, (P ω).adjoint = P ω)
    (hId : ∀ ω, (P ω).comp (P ω) = P ω)
    (hP : ∀ x : H, StronglyMeasurable (fun ω => P ω x))
    (D : Ω → Nuclear ℂ H H) (hD : StronglyMeasurable D) (hInt : Integrable D μ)
    (hPos : ∀ᵐ ω ∂μ, (toOperator (D ω)).IsPositive) :
    Integrable (fun ω => complementTrace (P ω) (D ω)) μ :=
  ((QuantumProver.HilbertNuclearTrace.trace (𝕜 := ℂ) (E := H)).integrable_comp
    (integrable_complementSandwich μ P hAdj hId hP D hD hInt hPos)).re

theorem ae_complementTrace_eq_zero_of_integral_eq_zero (μ : Measure Ω)
    (P : Ω → H →L[ℂ] H) (hAdj : ∀ ω, (P ω).adjoint = P ω)
    (hId : ∀ ω, (P ω).comp (P ω) = P ω)
    (hP : ∀ x : H, StronglyMeasurable (fun ω => P ω x))
    (D : Ω → Nuclear ℂ H H) (hD : StronglyMeasurable D) (hInt : Integrable D μ)
    (hPos : ∀ᵐ ω ∂μ, (toOperator (D ω)).IsPositive)
    (hZero : (∫ ω, complementTrace (P ω) (D ω) ∂μ) = 0) :
    (fun ω => complementTrace (P ω) (D ω)) =ᵐ[μ] 0 := by
  apply (integral_eq_zero_iff_of_nonneg_ae _
    (integrable_complementTrace μ P hAdj hId hP D hD hInt hPos)).mp hZero
  filter_upwards [hPos] with ω hω
  exact complementTrace_nonneg (D ω) (P ω) hω (hAdj ω)

theorem ae_projection_sandwich_eq_of_integral_complementTrace_eq_zero (μ : Measure Ω)
    (P : Ω → H →L[ℂ] H) (hAdj : ∀ ω, (P ω).adjoint = P ω)
    (hId : ∀ ω, (P ω).comp (P ω) = P ω)
    (hP : ∀ x : H, StronglyMeasurable (fun ω => P ω x))
    (D : Ω → Nuclear ℂ H H) (hD : StronglyMeasurable D) (hInt : Integrable D μ)
    (hPos : ∀ᵐ ω ∂μ, (toOperator (D ω)).IsPositive)
    (hZero : (∫ ω, complementTrace (P ω) (D ω) ∂μ) = 0) :
    ∀ᵐ ω ∂μ, compose (P ω) (P ω) (D ω) = D ω := by
  have hz := ae_complementTrace_eq_zero_of_integral_eq_zero μ P hAdj hId hP D hD hInt hPos hZero
  filter_upwards [hPos, hz] with ω hω hzero
  exact projection_sandwich_eq_of_re_complement_trace_eq_zero
    (D ω) (P ω) hω (hAdj ω) (hId ω) hzero

theorem ae_projection_sqrt_eq_of_integral_complementTrace_eq_zero (μ : Measure Ω)
    (P : Ω → H →L[ℂ] H) (hAdj : ∀ ω, (P ω).adjoint = P ω)
    (hId : ∀ ω, (P ω).comp (P ω) = P ω)
    (hP : ∀ x : H, StronglyMeasurable (fun ω => P ω x))
    (D : Ω → Nuclear ℂ H H) (hD : StronglyMeasurable D) (hInt : Integrable D μ)
    (hPos : ∀ᵐ ω ∂μ, (toOperator (D ω)).IsPositive)
    (hZero : (∫ ω, complementTrace (P ω) (D ω) ∂μ) = 0) :
    ∀ᵐ ω ∂μ, (P ω).comp (CFC.sqrt (toOperator (D ω))) = CFC.sqrt (toOperator (D ω)) := by
  have hz := ae_complementTrace_eq_zero_of_integral_eq_zero μ P hAdj hId hP D hD hInt hPos hZero
  filter_upwards [hPos, hz] with ω hω hzero
  exact projection_sqrt_eq_of_re_complement_trace_eq_zero (D ω) (P ω) hω (hAdj ω) hzero

theorem ae_sqrt_vectors_mem_projection_range (μ : Measure Ω)
    (P : Ω → H →L[ℂ] H) (hAdj : ∀ ω, (P ω).adjoint = P ω)
    (hId : ∀ ω, (P ω).comp (P ω) = P ω)
    (hP : ∀ x : H, StronglyMeasurable (fun ω => P ω x))
    (D : Ω → Nuclear ℂ H H) (hD : StronglyMeasurable D) (hInt : Integrable D μ)
    (hPos : ∀ᵐ ω ∂μ, (toOperator (D ω)).IsPositive)
    (hZero : (∫ ω, complementTrace (P ω) (D ω) ∂μ) = 0) :
    ∀ᵐ ω ∂μ, ∀ x : H, CFC.sqrt (toOperator (D ω)) x ∈ (P ω).toLinearMap.range := by
  filter_upwards [ae_projection_sqrt_eq_of_integral_complementTrace_eq_zero
    μ P hAdj hId hP D hD hInt hPos hZero] with ω hω
  intro x
  exact ⟨CFC.sqrt (toOperator (D ω)) x, congrArg (fun L : H →L[ℂ] H => L x) hω⟩

end QuantumProver.ElegantJointMeasurement.NuclearFieldSupport

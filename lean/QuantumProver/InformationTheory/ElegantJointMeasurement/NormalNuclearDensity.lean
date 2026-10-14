import QuantumProver.InformationTheory.ElegantJointMeasurement.NormalChoiRadonNikodym
import QuantumProver.InformationTheory.ElegantJointMeasurement.NuclearChoi
import QuantumProver.InformationTheory.ElegantJointMeasurement.NormalChoiKernels
import QuantumProver.LinearAlgebra.PositiveKernelOperator
import QuantumProver.LinearAlgebra.HilbertNuclearCompressionExpansion

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000

open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped BigOperators Topology ComplexOrder ENNReal

namespace QuantumProver.ElegantJointMeasurement.NormalNuclearDensity
open QuantumProver.ElegantJointMeasurement.NuclearChoi
open QuantumProver.PositiveKernelOperator

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

local instance nuclearMeasurable : MeasurableSpace (Nuclear E) := borel (Nuclear E)
local instance nuclearBorel : BorelSpace (Nuclear E) := ⟨rfl⟩

def nuclearOfPositiveKernel (b : HilbertBasis ℕ ℂ E) (F : ℕ → ℕ → ℂ)
    (hF : FinitePositive F) (hdiag : Summable (fun i => (F i i).re)) : Nuclear E :=
  positiveLift b (operator b F hF hdiag) (operator_isPositive b F hF hdiag)
    (operator_diagonal_summable_left b F hF hdiag)

theorem toOperator_nuclearOfPositiveKernel (b : HilbertBasis ℕ ℂ E)
    (F : ℕ → ℕ → ℂ) (hF : FinitePositive F)
    (hdiag : Summable (fun i => (F i i).re)) :
    QuantumProver.NuclearOperator.toOperator (nuclearOfPositiveKernel b F hF hdiag) =
      operator b F hF hdiag :=
  toOperator_positiveLift b _ _ _

theorem nuclearOfPositiveKernel_isPositive (b : HilbertBasis ℕ ℂ E)
    (F : ℕ → ℕ → ℂ) (hF : FinitePositive F)
    (hdiag : Summable (fun i => (F i i).re)) :
    (QuantumProver.NuclearOperator.toOperator (nuclearOfPositiveKernel b F hF hdiag)).IsPositive := by
  rw [toOperator_nuclearOfPositiveKernel]
  exact operator_isPositive b F hF hdiag

def nuclearCoefficient (b : HilbertBasis ℕ ℂ E) (i j : ℕ) : Nuclear E →L[ℂ] ℂ :=
  ((innerSL ℂ (b i)).comp (ContinuousLinearMap.apply ℂ E (b j))).comp
    (QuantumProver.NuclearOperator.toOperator (𝕜 := ℂ) (E := E) (F := E))

@[simp] theorem nuclearCoefficient_apply (b : HilbertBasis ℕ ℂ E) (i j : ℕ)
    (T : Nuclear E) :
    nuclearCoefficient b i j T = inner ℂ (b i) (QuantumProver.NuclearOperator.toOperator T (b j)) := rfl

theorem nuclearCoefficient_nuclearOfPositiveKernel (b : HilbertBasis ℕ ℂ E)
    (F : ℕ → ℕ → ℂ) (hF : FinitePositive F)
    (hdiag : Summable (fun i => (F i i).re)) (i j : ℕ) :
    nuclearCoefficient b i j (nuclearOfPositiveKernel b F hF hdiag) = F i j := by
  rw [nuclearCoefficient_apply, toOperator_nuclearOfPositiveKernel, operator_coefficient]

theorem nuclearCoefficient_ext (b : HilbertBasis ℕ ℂ E) {T S : Nuclear E}
    (h : ∀ i j, nuclearCoefficient b i j T = nuclearCoefficient b i j S) : T = S := by
  apply QuantumProver.NuclearOperator.toOperator_injective
  apply coefficient_ext b
  exact h

theorem norm_nuclearOfPositiveKernel (b : HilbertBasis ℕ ℂ E)
    (F : ℕ → ℕ → ℂ) (hF : FinitePositive F)
    (hdiag : Summable (fun i => (F i i).re)) :
    ‖nuclearOfPositiveKernel b F hF hdiag‖ = ∑' i, (F i i).re := by
  rw [nuclearOfPositiveKernel, norm_positiveLift_eq_diagonalTrace,
    operator_diagonalMass, diagonalMass]

variable {P : Type*} [MeasurableSpace P]

theorem stronglyMeasurable_nuclearOfPositiveKernel (b : HilbertBasis ℕ ℂ E)
    (F : P → ℕ → ℕ → ℂ) (hF : ∀ p, FinitePositive (F p))
    (hdiag : ∀ p, Summable (fun i => (F p i i).re))
    (hmeas : ∀ i j, Measurable (fun p => F p i j)) :
    StronglyMeasurable (fun p => nuclearOfPositiveKernel b (F p) (hF p) (hdiag p)) := by
  apply QuantumProver.HilbertNuclearCompressionExpansion.stronglyMeasurable_of_coordinates b
  intro i j
  simpa only [toOperator_nuclearOfPositiveKernel, operator_coefficient] using hmeas i j

theorem measurable_nuclearOfPositiveKernel (b : HilbertBasis ℕ ℂ E)
    (F : P → ℕ → ℕ → ℂ) (hF : ∀ p, FinitePositive (F p))
    (hdiag : ∀ p, Summable (fun i => (F p i i).re))
    (hmeas : ∀ i j, Measurable (fun p => F p i j)) :
    Measurable (fun p => nuclearOfPositiveKernel b (F p) (hF p) (hdiag p)) :=
  (stronglyMeasurable_nuclearOfPositiveKernel b F hF hdiag hmeas).measurable

theorem integrable_nuclearOfPositiveKernel (b : HilbertBasis ℕ ℂ E)
    (F : P → ℕ → ℕ → ℂ) (hF : ∀ p, FinitePositive (F p))
    (hdiag : ∀ p, Summable (fun i => (F p i i).re))
    (hmeas : ∀ i j, Measurable (fun p => F p i j))
    (d : ℝ) (hbound : ∀ p, (∑' i, (F p i i).re) ≤ d)
    (μ : Measure P) [IsFiniteMeasure μ] :
    Integrable (fun p => nuclearOfPositiveKernel b (F p) (hF p) (hdiag p)) μ := by
  refine ⟨(stronglyMeasurable_nuclearOfPositiveKernel b F hF hdiag hmeas).aestronglyMeasurable,
    HasFiniteIntegral.of_bounded (C := d) (ae_of_all μ fun p => ?_)⟩
  rw [norm_nuclearOfPositiveKernel]
  exact hbound p

theorem setIntegral_nuclearOfPositiveKernel (b : HilbertBasis ℕ ℂ E)
    (F : P → ℕ → ℕ → ℂ) (hF : ∀ p, FinitePositive (F p))
    (hdiag : ∀ p, Summable (fun i => (F p i i).re))
    (hmeas : ∀ i j, Measurable (fun p => F p i j))
    (d : ℝ) (hbound : ∀ p, (∑' i, (F p i i).re) ≤ d)
    (μ : Measure P) [IsFiniteMeasure μ] (s : Set P) (T : Nuclear E)
    (hcoord : ∀ i j, (∫ p in s, F p i j ∂μ) = nuclearCoefficient b i j T) :
    (∫ p in s, nuclearOfPositiveKernel b (F p) (hF p) (hdiag p) ∂μ) = T := by
  apply nuclearCoefficient_ext b
  intro i j
  rw [← (nuclearCoefficient b i j).integral_comp_comm
    (integrable_nuclearOfPositiveKernel b F hF hdiag hmeas d hbound μ).integrableOn]
  simp_rw [nuclearCoefficient_nuclearOfPositiveKernel]
  exact hcoord i j

variable {H Ω : Type*} [MeasurableSpace H] [MeasurableSpace Ω]
variable [MeasurableSpace.CountableOrCountablyGenerated H Ω]
open QuantumProver.ElegantJointMeasurement.ContinuousInstrumentRadonNikodym

theorem exists_joint_positive_nuclear_density
    (b : HilbertBasis ℕ ℂ E)
    (κ : ℕ → Kernel H Ω) (μ : Kernel H Ω) [IsMarkovKernel μ]
    (C : (n : ℕ) → PositiveChoiKernel (H := H) (Ω := Ω) (Q := Fin n))
    (d : ℝ) (hd : 0 ≤ d)
    (htrace : ∀ h (s : Set Ω), MeasurableSet s →
      (∑' i, κ i h s) = ENNReal.ofReal d * μ h s)
    (hdiag : ∀ n (i : Fin n), (C n).probe (basisVector i) = κ i.val)
    (hcoherent : ∀ n m (hnm : n ≤ m) h s, MeasurableSet s → ∀ i j : Fin n,
      (C m).effect h s (Fin.castLE hnm i) (Fin.castLE hnm j) = (C n).effect h s i j)
    (Γ : H → Set Ω → Nuclear E)
    (hΓ : ∀ n h (s : Set Ω), MeasurableSet s → ∀ i j : Fin n,
      (C n).effect h s i j = nuclearCoefficient b i.val j.val (Γ h s)) :
    ∃ D : H → Ω → Nuclear E,
      StronglyMeasurable (fun z : H × Ω => D z.1 z.2) ∧
      Measurable (fun z : H × Ω => D z.1 z.2) ∧
      (∀ h ω, (QuantumProver.NuclearOperator.toOperator (D h ω)).IsPositive) ∧
      (∀ h ω, ‖D h ω‖ ≤ d) ∧
      (∀ h, ∀ᵐ ω ∂μ h, ‖D h ω‖ = d) ∧
      (∀ h, Integrable (D h) (μ h)) ∧
      (∀ h (s : Set Ω), MeasurableSet s → (∫ ω in s, D h ω ∂μ h) = Γ h s) := by
  obtain ⟨F, hmeas, hpos, hsum, hbound, hmass, hint, hcoord⟩ :=
    QuantumProver.ElegantJointMeasurement.NormalChoiRadonNikodym.exists_joint_countable_positive_density
      κ μ C d hd htrace hdiag hcoherent
  let hp : ∀ z : H × Ω, FinitePositive (F z.1 z.2) := fun z n => hpos n z.1 z.2
  let hdg : ∀ z : H × Ω, Summable (fun i => (F z.1 z.2 i i).re) :=
    fun z => hsum z.1 z.2
  let D : H → Ω → Nuclear E := fun h ω =>
    nuclearOfPositiveKernel b (F h ω) (hp (h,ω)) (hdg (h,ω))
  refine ⟨D, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact stronglyMeasurable_nuclearOfPositiveKernel b
      (fun z : H × Ω => F z.1 z.2) hp hdg hmeas
  · exact measurable_nuclearOfPositiveKernel b
      (fun z : H × Ω => F z.1 z.2) hp hdg hmeas
  · intro h ω
    exact nuclearOfPositiveKernel_isPositive b _ _ _
  · intro h ω
    change ‖nuclearOfPositiveKernel b (F h ω) (hp (h,ω)) (hdg (h,ω))‖ ≤ d
    rw [norm_nuclearOfPositiveKernel]
    exact hbound h ω
  · intro h
    filter_upwards [hmass h] with ω hω
    change ‖nuclearOfPositiveKernel b (F h ω) (hp (h,ω)) (hdg (h,ω))‖ = d
    rw [norm_nuclearOfPositiveKernel]
    exact hω
  · intro h
    exact integrable_nuclearOfPositiveKernel b (F h)
      (fun ω => hp (h,ω)) (fun ω => hdg (h,ω))
      (fun i j => (hmeas i j).comp (measurable_const.prodMk measurable_id)) d (hbound h) (μ h)
  · intro h s hs
    apply setIntegral_nuclearOfPositiveKernel b (F h)
      (fun ω => hp (h,ω)) (fun ω => hdg (h,ω))
      (fun i j => (hmeas i j).comp (measurable_const.prodMk measurable_id)) d (hbound h) (μ h) s (Γ h s)
    intro i j
    let n := max i j + 1
    let ii : Fin n := ⟨i, Nat.lt_succ_of_le (Nat.le_max_left i j)⟩
    let jj : Fin n := ⟨j, Nat.lt_succ_of_le (Nat.le_max_right i j)⟩
    exact (hcoord n h s hs ii jj).trans (hΓ n h s hs ii jj)

variable {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]
open QuantumProver.ElegantJointMeasurement.HilbertChoi

theorem exists_physical_positive_nuclear_density
    (P : QuantumProver.ElegantJointMeasurement.NormalCPInstruments.Instrument I E H Ω)
    (b : HilbertBasis ℕ ℂ (BlockSpace I E)) :
    ∃ D : H → Ω → Nuclear (BlockSpace I E),
      StronglyMeasurable (fun z : H × Ω => D z.1 z.2) ∧
      Measurable (fun z : H × Ω => D z.1 z.2) ∧
      (∀ h ω, (QuantumProver.NuclearOperator.toOperator (D h ω)).IsPositive) ∧
      (∀ h ω, (QuantumProver.HilbertNuclearTrace.trace (D h ω)).re = ‖D h ω‖) ∧
      (∀ h ω, ‖D h ω‖ ≤ (Fintype.card I : ℝ)) ∧
      (∀ h, ∀ᵐ ω ∂P.referenceKernel h, ‖D h ω‖ = (Fintype.card I : ℝ)) ∧
      (∀ h, Integrable (D h) (P.referenceKernel h)) ∧
      (∀ h (s : Set Ω), MeasurableSet s →
        (∫ ω in s, D h ω ∂P.referenceKernel h) = P.physicalChoi h s) := by
  obtain ⟨D, hstrong, hmeas, hpos, hbound, hmass, hint, hset⟩ :=
    exists_joint_positive_nuclear_density b
      (QuantumProver.ElegantJointMeasurement.NormalChoiKernels.Instrument.diagonalKernel P b) P.referenceKernel
      (QuantumProver.ElegantJointMeasurement.NormalChoiKernels.Instrument.finiteChoiKernel P b)
      (Fintype.card I : ℝ) (Nat.cast_nonneg _)
      (QuantumProver.ElegantJointMeasurement.NormalChoiKernels.Instrument.diagonalKernel_tsum P b)
      (QuantumProver.ElegantJointMeasurement.NormalChoiKernels.Instrument.finiteChoiKernel_probe_basisVector P b)
      (QuantumProver.ElegantJointMeasurement.NormalChoiKernels.Instrument.finiteChoiKernel_coherent P b)
      P.physicalChoi (fun _ _ _ _ _ _ => rfl)
  refine ⟨D, hstrong, hmeas, hpos, ?_, hbound, hmass, hint, hset⟩
  intro h ω
  exact (norm_positive_nuclear_eq_re_trace b (D h ω) (hpos h ω)).symm

end QuantumProver.ElegantJointMeasurement.NormalNuclearDensity

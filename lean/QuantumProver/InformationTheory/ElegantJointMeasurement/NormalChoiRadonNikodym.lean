import Mathlib
import QuantumProver.InformationTheory.ElegantJointMeasurement.VariableFiberRadonNikodym
import QuantumProver.InformationTheory.ElegantJointMeasurement.InstrumentTestIntegral

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal BigOperators Topology

namespace QuantumProver.ElegantJointMeasurement.NormalChoiRadonNikodym

variable {H Ω : Type*} [MeasurableSpace H] [MeasurableSpace Ω]
variable [MeasurableSpace.CountableOrCountablyGenerated H Ω]
variable (κ : ℕ → Kernel H Ω) (μ : Kernel H Ω) [IsMarkovKernel μ]

def diagonalDensityE (n : ℕ) (h : H) (ω : Ω) : ℝ≥0∞ :=
  (κ n).rnDeriv μ h ω

def diagonalDensity (n : ℕ) (h : H) (ω : Ω) : ℝ :=
  (diagonalDensityE κ μ n h ω).toReal

theorem measurable_diagonalDensityE (n : ℕ) :
    Measurable (fun z : H × Ω => diagonalDensityE κ μ n z.1 z.2) :=
  (κ n).measurable_rnDeriv μ

theorem measurable_diagonalDensity (n : ℕ) :
    Measurable (fun z : H × Ω => diagonalDensity κ μ n z.1 z.2) :=
  (measurable_diagonalDensityE κ μ n).ennreal_toReal

theorem diagonalDensity_nonneg (n : ℕ) (h : H) (ω : Ω) :
    0 ≤ diagonalDensity κ μ n h ω := ENNReal.toReal_nonneg

theorem diagonal_isFinite (d : ℝ)
    (htrace : ∀ h (s : Set Ω), MeasurableSet s →
      (∑' n, κ n h s) = ENNReal.ofReal d * μ h s) (n : ℕ) :
    IsFiniteKernel (κ n) := by
  refine ⟨ENNReal.ofReal d, ENNReal.ofReal_lt_top, fun h => ?_⟩
  have ht : (∑' i, κ i h univ) = ENNReal.ofReal d := by
    simpa using htrace h univ MeasurableSet.univ
  rw [← ht]
  exact ENNReal.le_tsum (f := fun i => κ i h univ) n

theorem diagonal_absolutelyContinuous (d : ℝ)
    (htrace : ∀ h (s : Set Ω), MeasurableSet s →
      (∑' n, κ n h s) = ENNReal.ofReal d * μ h s) (n : ℕ) (h : H) :
    κ n h ≪ μ h := by
  refine Measure.AbsolutelyContinuous.mk fun s hs hzero => ?_
  have ht : (∑' i, κ i h s) = 0 := by rw [htrace h s hs, hzero, mul_zero]
  exact le_antisymm ((ENNReal.le_tsum n).trans_eq ht) bot_le

theorem integrable_diagonalDensity (d : ℝ)
    (htrace : ∀ h (s : Set Ω), MeasurableSet s →
      (∑' n, κ n h s) = ENNReal.ofReal d * μ h s) (n : ℕ) (h : H) :
    Integrable (diagonalDensity κ μ n h) (μ h) := by
  letI : IsFiniteKernel (κ n) := diagonal_isFinite κ μ d htrace n
  change Integrable (fun ω => ((κ n).rnDeriv μ h ω).toReal) (μ h)
  apply integrable_toReal_of_lintegral_ne_top
    ((measurable_diagonalDensityE κ μ n).of_uncurry_left.aemeasurable)
  rw [Kernel.lintegral_rnDeriv
    (diagonal_absolutelyContinuous κ μ d htrace n h)]
  exact measure_ne_top _ _

theorem setIntegral_diagonalDensity (d : ℝ)
    (htrace : ∀ h (s : Set Ω), MeasurableSet s →
      (∑' n, κ n h s) = ENNReal.ofReal d * μ h s) (n : ℕ) (h : H)
    (s : Set Ω) (hs : MeasurableSet s) :
    (∫ ω in s, diagonalDensity κ μ n h ω ∂μ h) = (κ n h s).toReal := by
  letI : IsFiniteKernel (κ n) := diagonal_isFinite κ μ d htrace n
  change (∫ ω in s, ((κ n).rnDeriv μ h ω).toReal ∂μ h) = _
  rw [integral_toReal
    ((measurable_diagonalDensityE κ μ n).of_uncurry_left.aemeasurable.restrict)
    (ae_restrict_of_ae (Kernel.rnDeriv_lt_top (κ n) μ))]
  rw [Kernel.setLIntegral_rnDeriv
    (diagonal_absolutelyContinuous κ μ d htrace n h) hs]

theorem ae_tsum_diagonalDensityE (d : ℝ)
    (htrace : ∀ h (s : Set Ω), MeasurableSet s →
      (∑' n, κ n h s) = ENNReal.ofReal d * μ h s) (h : H) :
    ∀ᵐ ω ∂μ h, (∑' n, diagonalDensityE κ μ n h ω) = ENNReal.ofReal d := by
  letI : ∀ n, IsFiniteKernel (κ n) := fun n => diagonal_isFinite κ μ d htrace n
  apply ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite
    (Measurable.ennreal_tsum fun n =>
      (measurable_diagonalDensityE κ μ n).of_uncurry_left) measurable_const
  intro s hs _
  rw [lintegral_tsum fun n =>
    (measurable_diagonalDensityE κ μ n).of_uncurry_left.aemeasurable.restrict]
  change (∑' n, ∫⁻ ω in s, (κ n).rnDeriv μ h ω ∂μ h) = _
  simp_rw [Kernel.setLIntegral_rnDeriv
    (diagonal_absolutelyContinuous κ μ d htrace _ h) hs]
  rw [htrace h s hs, lintegral_const, Measure.restrict_apply_univ]

def traceValid (d : ℝ) (z : H × Ω) : Prop :=
  (∑' n, diagonalDensityE κ μ n z.1 z.2) = ENNReal.ofReal d

theorem measurableSet_traceValid (d : ℝ) : MeasurableSet (traceValid κ μ d) :=
  measurableSet_eq_fun
    (Measurable.ennreal_tsum fun n => measurable_diagonalDensityE κ μ n) measurable_const

theorem traceValid_ae (d : ℝ)
    (htrace : ∀ h (s : Set Ω), MeasurableSet s →
      (∑' n, κ n h s) = ENNReal.ofReal d * μ h s) (h : H) :
    ∀ᵐ ω ∂μ h, traceValid κ μ d (h,ω) :=
  ae_tsum_diagonalDensityE κ μ d htrace h

theorem diagonalDensityE_ne_top_of_valid {d : ℝ} {z : H × Ω}
    (hz : traceValid κ μ d z) (n : ℕ) : diagonalDensityE κ μ n z.1 z.2 ≠ ∞ := by
  exact ne_of_lt ((ENNReal.le_tsum n).trans_lt (hz ▸ ENNReal.ofReal_lt_top))

theorem summable_diagonalDensity_of_valid {d : ℝ} {z : H × Ω}
    (hz : traceValid κ μ d z) : Summable (fun n => diagonalDensity κ μ n z.1 z.2) := by
  apply ENNReal.summable_toReal
  rw [show (∑' n, diagonalDensityE κ μ n z.1 z.2) = ENNReal.ofReal d from hz]
  exact ENNReal.ofReal_ne_top

theorem tsum_diagonalDensity_of_valid {d : ℝ} (hd : 0 ≤ d) {z : H × Ω}
    (hz : traceValid κ μ d z) : (∑' n, diagonalDensity κ μ n z.1 z.2) = d := by
  have he := congrArg ENNReal.toReal hz
  rw [ENNReal.tsum_toReal_eq (diagonalDensityE_ne_top_of_valid κ μ hz),
    ENNReal.toReal_ofReal hd] at he
  exact he

def patchedDiagonalDensity (d : ℝ) (n : ℕ) (z : H × Ω) : ℝ := by
  classical
  exact if traceValid κ μ d z then diagonalDensity κ μ n z.1 z.2 else 0

theorem measurable_patchedDiagonalDensity (d : ℝ) (n : ℕ) :
    Measurable (patchedDiagonalDensity κ μ d n) := by
  classical
  exact (measurable_diagonalDensity κ μ n).piecewise
    (measurableSet_traceValid κ μ d) measurable_const

theorem patchedDiagonalDensity_nonneg (d : ℝ) (n : ℕ) (z : H × Ω) :
    0 ≤ patchedDiagonalDensity κ μ d n z := by
  classical
  by_cases hz : traceValid κ μ d z
  · simpa [patchedDiagonalDensity, hz] using diagonalDensity_nonneg κ μ n z.1 z.2
  · simp [patchedDiagonalDensity, hz]

theorem patchedDiagonalDensity_ae_eq (d : ℝ)
    (htrace : ∀ h (s : Set Ω), MeasurableSet s →
      (∑' n, κ n h s) = ENNReal.ofReal d * μ h s) (n : ℕ) (h : H) :
    (fun ω => patchedDiagonalDensity κ μ d n (h,ω)) =ᵐ[μ h]
      diagonalDensity κ μ n h := by
  classical
  filter_upwards [traceValid_ae κ μ d htrace h] with ω hω
  simp [patchedDiagonalDensity, hω]

theorem summable_patchedDiagonalDensity (d : ℝ) (z : H × Ω) :
    Summable (fun n => patchedDiagonalDensity κ μ d n z) := by
  classical
  by_cases hz : traceValid κ μ d z
  · simpa [patchedDiagonalDensity, hz] using summable_diagonalDensity_of_valid κ μ hz
  · simp [patchedDiagonalDensity, hz]

def patchedTrace (d : ℝ) (z : H × Ω) : ℝ := by
  classical
  exact if traceValid κ μ d z then d else 0

theorem tsum_patchedDiagonalDensity (d : ℝ) (hd : 0 ≤ d) (z : H × Ω) :
    (∑' n, patchedDiagonalDensity κ μ d n z) = patchedTrace κ μ d z := by
  classical
  by_cases hz : traceValid κ μ d z
  · simpa [patchedDiagonalDensity, patchedTrace, hz] using tsum_diagonalDensity_of_valid κ μ hd hz
  · simp [patchedDiagonalDensity, patchedTrace, hz]

theorem integrable_patchedDiagonalDensity (d : ℝ)
    (htrace : ∀ h (s : Set Ω), MeasurableSet s →
      (∑' n, κ n h s) = ENNReal.ofReal d * μ h s) (n : ℕ) (h : H) :
    Integrable (fun ω => patchedDiagonalDensity κ μ d n (h,ω)) (μ h) :=
  (integrable_diagonalDensity κ μ d htrace n h).congr
    (patchedDiagonalDensity_ae_eq κ μ d htrace n h).symm

theorem setIntegral_patchedDiagonalDensity (d : ℝ)
    (htrace : ∀ h (s : Set Ω), MeasurableSet s →
      (∑' n, κ n h s) = ENNReal.ofReal d * μ h s) (n : ℕ) (h : H)
    (s : Set Ω) (hs : MeasurableSet s) :
    (∫ ω in s, patchedDiagonalDensity κ μ d n (h,ω) ∂μ h) = (κ n h s).toReal := by
  calc
    _ = ∫ ω in s, diagonalDensity κ μ n h ω ∂μ h :=
      integral_congr_ae (ae_restrict_of_ae (patchedDiagonalDensity_ae_eq κ μ d htrace n h))
    _ = _ := setIntegral_diagonalDensity κ μ d htrace n h s hs

end QuantumProver.ElegantJointMeasurement.NormalChoiRadonNikodym

namespace QuantumProver.ElegantJointMeasurement.NormalChoiRadonNikodym
open QuantumProver.ElegantJointMeasurement.ContinuousInstrumentRadonNikodym
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

section PositiveBlocks
variable {H Ω : Type*} [MeasurableSpace H] [MeasurableSpace Ω]
variable [MeasurableSpace.CountableOrCountablyGenerated H Ω]
variable (κ : ℕ → Kernel H Ω) (μ : Kernel H Ω) [IsMarkovKernel μ]
variable (C : (n : ℕ) → PositiveChoiKernel (H := H) (Ω := Ω) (Q := Fin n))

theorem block_trace_le_sum_diagonal
    (hdiag : ∀ n (i : Fin n), (C n).probe (basisVector i) = κ i.val)
    (n : ℕ) (h : H) (s : Set Ω) (hs : MeasurableSet s) :
    (C n).traceKernel h s ≤ ∑' i, κ i h s := by
  unfold PositiveChoiKernel.traceKernel
  simp only [Kernel.finsetSum_apply']
  simp_rw [hdiag n]
  simpa only [tsum_fintype] using
    ENNReal.tsum_comp_le_tsum_of_injective (Fin.val_injective (n := n)) (fun i => κ i h s)

theorem block_trace_real_le (d : ℝ) (hd : 0 ≤ d)
    (htrace : ∀ h (s : Set Ω), MeasurableSet s →
      (∑' i, κ i h s) = ENNReal.ofReal d * μ h s)
    (hdiag : ∀ n (i : Fin n), (C n).probe (basisVector i) = κ i.val)
    (n : ℕ) (h : H) : ((C n).effect h univ).trace.re ≤ d := by
  apply (ENNReal.ofReal_le_ofReal_iff hd).mp
  rw [← (C n).traceKernel_apply h univ MeasurableSet.univ]
  have hb := block_trace_le_sum_diagonal κ C hdiag n h univ MeasurableSet.univ
  rw [htrace h univ MeasurableSet.univ] at hb
  simpa using hb

theorem block_probe_isFinite (d : ℝ) (hd : 0 ≤ d)
    (htrace : ∀ h (s : Set Ω), MeasurableSet s →
      (∑' i, κ i h s) = ENNReal.ofReal d * μ h s)
    (hdiag : ∀ n (i : Fin n), (C n).probe (basisVector i) = κ i.val)
    (n : ℕ) (v : Fin n → ℂ) : IsFiniteKernel ((C n).probe v) :=
  (C n).probe_isFinite_of_trace_le d
    (block_trace_real_le κ μ C d hd htrace hdiag n) v

theorem block_probe_absolutelyContinuous (d : ℝ)
    (htrace : ∀ h (s : Set Ω), MeasurableSet s →
      (∑' i, κ i h s) = ENNReal.ofReal d * μ h s)
    (hdiag : ∀ n (i : Fin n), (C n).probe (basisVector i) = κ i.val)
    (n : ℕ) (v : Fin n → ℂ) (h : H) : (C n).probe v h ≪ μ h := by
  apply ((C n).probe_absolutelyContinuous_trace v h).trans
  refine Measure.AbsolutelyContinuous.mk fun s hs hzero => ?_
  have hb := block_trace_le_sum_diagonal κ C hdiag n h s hs
  rw [htrace h s hs, hzero, mul_zero] at hb
  exact le_antisymm hb bot_le

variable [∀ n (v : Fin n → ℂ), IsFiniteKernel ((C n).probe v)]

def blockDensity (n : ℕ) (h : H) (ω : Ω) : Matrix (Fin n) (Fin n) ℂ :=
  (C n).positiveRelativeDensity μ h ω

theorem measurable_blockDensity (n : ℕ) :
    Measurable (fun z : H × Ω => blockDensity μ C n z.1 z.2) :=
  (C n).measurable_positiveRelativeDensity μ

theorem blockDensity_positive (n : ℕ) (h : H) (ω : Ω) :
    (blockDensity μ C n h ω).PosSemidef :=
  (C n).positiveRelativeDensity_posSemidef μ h ω

theorem integrable_blockDensity (d : ℝ) (hd : 0 ≤ d)
    (htrace : ∀ h (s : Set Ω), MeasurableSet s →
      (∑' i, κ i h s) = ENNReal.ofReal d * μ h s)
    (hdiag : ∀ n (i : Fin n), (C n).probe (basisVector i) = κ i.val)
    (n : ℕ) (h : H) : Integrable (blockDensity μ C n h) (μ h) := by
  letI : ∀ v : Fin n → ℂ, IsFiniteKernel ((C n).probe v) :=
    block_probe_isFinite κ μ C d hd htrace hdiag n
  exact (C n).integrable_positiveRelativeDensity μ
    (block_probe_absolutelyContinuous κ μ C d htrace hdiag n) h

theorem setIntegral_blockDensity (d : ℝ) (hd : 0 ≤ d)
    (htrace : ∀ h (s : Set Ω), MeasurableSet s →
      (∑' i, κ i h s) = ENNReal.ofReal d * μ h s)
    (hdiag : ∀ n (i : Fin n), (C n).probe (basisVector i) = κ i.val)
    (n : ℕ) (h : H) (s : Set Ω) (hs : MeasurableSet s) :
    (∫ ω in s, blockDensity μ C n h ω ∂μ h) = (C n).effect h s := by
  letI : ∀ v : Fin n → ℂ, IsFiniteKernel ((C n).probe v) :=
    block_probe_isFinite κ μ C d hd htrace hdiag n
  exact (C n).setIntegral_positiveRelativeDensity μ
    (block_probe_absolutelyContinuous κ μ C d htrace hdiag n) h s hs

theorem integrable_blockEntry (d : ℝ) (hd : 0 ≤ d)
    (htrace : ∀ h (s : Set Ω), MeasurableSet s →
      (∑' i, κ i h s) = ENNReal.ofReal d * μ h s)
    (hdiag : ∀ n (i : Fin n), (C n).probe (basisVector i) = κ i.val)
    (n : ℕ) (h : H) (i j : Fin n) :
    Integrable (fun ω => blockDensity μ C n h ω i j) (μ h) :=
  QuantumProver.ElegantJointMeasurement.HilbertInstrumentTestIntegral.integrable_matrix_entry
    (integrable_blockDensity κ μ C d hd htrace hdiag n h) i j

theorem setIntegral_blockEntry (d : ℝ) (hd : 0 ≤ d)
    (htrace : ∀ h (s : Set Ω), MeasurableSet s →
      (∑' i, κ i h s) = ENNReal.ofReal d * μ h s)
    (hdiag : ∀ n (i : Fin n), (C n).probe (basisVector i) = κ i.val)
    (n : ℕ) (h : H) (s : Set Ω) (hs : MeasurableSet s) (i j : Fin n) :
    (∫ ω in s, blockDensity μ C n h ω i j ∂μ h) = (C n).effect h s i j := by
  rw [QuantumProver.ElegantJointMeasurement.HilbertInstrumentTestIntegral.integral_matrix_entry
    (integrable_blockDensity κ μ C d hd htrace hdiag n h).integrableOn i j,
    setIntegral_blockDensity κ μ C d hd htrace hdiag n h s hs]

theorem blockDensity_coherent_ae (d : ℝ) (hd : 0 ≤ d)
    (htrace : ∀ h (s : Set Ω), MeasurableSet s →
      (∑' i, κ i h s) = ENNReal.ofReal d * μ h s)
    (hdiag : ∀ n (i : Fin n), (C n).probe (basisVector i) = κ i.val)
    (hcoherent : ∀ n m (hnm : n ≤ m) h s, MeasurableSet s → ∀ i j : Fin n,
      (C m).effect h s (Fin.castLE hnm i) (Fin.castLE hnm j) = (C n).effect h s i j)
    (n m : ℕ) (hnm : n ≤ m) (h : H) (i j : Fin n) :
    ∀ᵐ ω ∂μ h,
      blockDensity μ C m h ω (Fin.castLE hnm i) (Fin.castLE hnm j) =
        blockDensity μ C n h ω i j := by
  apply Integrable.ae_eq_of_forall_setIntegral_eq _ _
    (integrable_blockEntry κ μ C d hd htrace hdiag m h _ _)
    (integrable_blockEntry κ μ C d hd htrace hdiag n h i j)
  intro s hs _
  rw [setIntegral_blockEntry κ μ C d hd htrace hdiag m h s hs,
    setIntegral_blockEntry κ μ C d hd htrace hdiag n h s hs]
  exact hcoherent n m hnm h s hs i j

theorem blockDensity_diagonal_ae (d : ℝ) (hd : 0 ≤ d)
    (htrace : ∀ h (s : Set Ω), MeasurableSet s →
      (∑' i, κ i h s) = ENNReal.ofReal d * μ h s)
    (hdiag : ∀ n (i : Fin n), (C n).probe (basisVector i) = κ i.val)
    (n : ℕ) (h : H) (i : Fin n) :
    ∀ᵐ ω ∂μ h, blockDensity μ C n h ω i i =
      (diagonalDensity κ μ i.val h ω : ℂ) := by
  apply Integrable.ae_eq_of_forall_setIntegral_eq _ _
    (integrable_blockEntry κ μ C d hd htrace hdiag n h i i)
    (integrable_diagonalDensity κ μ d htrace i.val h).ofReal
  intro s hs _
  rw [setIntegral_blockEntry κ μ C d hd htrace hdiag n h s hs i i]
  erw [integral_complex_ofReal, setIntegral_diagonalDensity κ μ d htrace i.val h s hs]
  have hp := congrArg (fun k : Kernel H Ω => k h s) (hdiag n i)
  rw [(C n).probe_apply _ h s hs, quadratic_basisVector] at hp
  have hnonneg : 0 ≤ (C n).effect h s i i := ((C n).positive h s hs).diag_nonneg
  have h0 := Complex.nonneg_iff.mp hnonneg
  rw [← hp, ENNReal.toReal_ofReal h0.1]
  apply Complex.ext <;> simp [h0.2]

def rawCoordinate (i j : ℕ) (z : H × Ω) : ℂ :=
  blockDensity μ C (max i j + 1) z.1 z.2
    ⟨i, Nat.lt_succ_of_le (Nat.le_max_left i j)⟩
    ⟨j, Nat.lt_succ_of_le (Nat.le_max_right i j)⟩

theorem measurable_rawCoordinate (i j : ℕ) : Measurable (rawCoordinate μ C i j) :=
  (measurable_pi_apply _).comp
    ((measurable_pi_apply _).comp (measurable_blockDensity μ C (max i j + 1)))

theorem integrable_rawCoordinate (d : ℝ) (hd : 0 ≤ d)
    (htrace : ∀ h (s : Set Ω), MeasurableSet s →
      (∑' i, κ i h s) = ENNReal.ofReal d * μ h s)
    (hdiag : ∀ n (i : Fin n), (C n).probe (basisVector i) = κ i.val)
    (i j : ℕ) (h : H) : Integrable (fun ω => rawCoordinate μ C i j (h,ω)) (μ h) :=
  integrable_blockEntry κ μ C d hd htrace hdiag _ h _ _

theorem rawCoordinate_eq_block_ae (d : ℝ) (hd : 0 ≤ d)
    (htrace : ∀ h (s : Set Ω), MeasurableSet s →
      (∑' i, κ i h s) = ENNReal.ofReal d * μ h s)
    (hdiag : ∀ n (i : Fin n), (C n).probe (basisVector i) = κ i.val)
    (hcoherent : ∀ n m (hnm : n ≤ m) h s, MeasurableSet s → ∀ i j : Fin n,
      (C m).effect h s (Fin.castLE hnm i) (Fin.castLE hnm j) = (C n).effect h s i j)
    (n : ℕ) (h : H) (i j : Fin n) :
    ∀ᵐ ω ∂μ h, rawCoordinate μ C i.val j.val (h,ω) = blockDensity μ C n h ω i j := by
  let m := max i.val j.val + 1
  have hmn : m ≤ n := by dsimp [m]; omega
  let im : Fin m := ⟨i.val, Nat.lt_succ_of_le (Nat.le_max_left i.val j.val)⟩
  let jm : Fin m := ⟨j.val, Nat.lt_succ_of_le (Nat.le_max_right i.val j.val)⟩
  have hi : Fin.castLE hmn im = i := Fin.ext rfl
  have hj : Fin.castLE hmn jm = j := Fin.ext rfl
  filter_upwards [blockDensity_coherent_ae κ μ C d hd htrace hdiag hcoherent m n hmn h im jm]
    with ω hω
  rw [hi, hj] at hω
  exact hω.symm

theorem rawCoordinate_diagonal_ae (d : ℝ) (hd : 0 ≤ d)
    (htrace : ∀ h (s : Set Ω), MeasurableSet s →
      (∑' i, κ i h s) = ENNReal.ofReal d * μ h s)
    (hdiag : ∀ n (i : Fin n), (C n).probe (basisVector i) = κ i.val)
    (i : ℕ) (h : H) :
    ∀ᵐ ω ∂μ h, rawCoordinate μ C i i (h,ω) = (diagonalDensity κ μ i h ω : ℂ) := by
  simpa only [rawCoordinate] using
    blockDensity_diagonal_ae κ μ C d hd htrace hdiag (max i i + 1) h
      ⟨i, Nat.lt_succ_of_le (Nat.le_max_left i i)⟩

end PositiveBlocks
end QuantumProver.ElegantJointMeasurement.NormalChoiRadonNikodym

namespace QuantumProver.ElegantJointMeasurement.NormalChoiRadonNikodym
open QuantumProver.ElegantJointMeasurement.ContinuousInstrumentRadonNikodym
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

section CountableAssembly
variable {H Ω : Type*} [MeasurableSpace H] [MeasurableSpace Ω]
variable [MeasurableSpace.CountableOrCountablyGenerated H Ω]
variable (κ : ℕ → Kernel H Ω) (μ : Kernel H Ω) [IsMarkovKernel μ]
variable (C : (n : ℕ) → PositiveChoiKernel (H := H) (Ω := Ω) (Q := Fin n))
variable [∀ n (v : Fin n → ℂ), IsFiniteKernel ((C n).probe v)]

def assemblyValid (d : ℝ) (z : H × Ω) : Prop :=
  traceValid κ μ d z ∧
    (∀ n (i j : Fin n), rawCoordinate μ C i.val j.val z = blockDensity μ C n z.1 z.2 i j) ∧
    (∀ i, rawCoordinate μ C i i z = (diagonalDensity κ μ i z.1 z.2 : ℂ))

theorem measurableSet_assemblyValid (d : ℝ) : MeasurableSet (assemblyValid κ μ C d) := by
  have hb : MeasurableSet {z : H × Ω | ∀ n (i j : Fin n),
      rawCoordinate μ C i.val j.val z = blockDensity μ C n z.1 z.2 i j} := by
    simp only [setOf_forall]
    refine MeasurableSet.iInter fun n => MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => ?_
    exact measurableSet_eq_fun (measurable_rawCoordinate μ C i.val j.val)
      ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp (measurable_blockDensity μ C n)))
  have hdg : MeasurableSet {z : H × Ω | ∀ i,
      rawCoordinate μ C i i z = (diagonalDensity κ μ i z.1 z.2 : ℂ)} := by
    simp only [setOf_forall]
    refine MeasurableSet.iInter fun i => ?_
    exact measurableSet_eq_fun (measurable_rawCoordinate μ C i i)
      ((measurable_diagonalDensity κ μ i).complex_ofReal)
  exact (measurableSet_traceValid κ μ d).inter (hb.inter hdg)

theorem assemblyValid_ae (d : ℝ) (hd : 0 ≤ d)
    (htrace : ∀ h (s : Set Ω), MeasurableSet s →
      (∑' i, κ i h s) = ENNReal.ofReal d * μ h s)
    (hdiag : ∀ n (i : Fin n), (C n).probe (basisVector i) = κ i.val)
    (hcoherent : ∀ n m (hnm : n ≤ m) h s, MeasurableSet s → ∀ i j : Fin n,
      (C m).effect h s (Fin.castLE hnm i) (Fin.castLE hnm j) = (C n).effect h s i j)
    (h : H) : ∀ᵐ ω ∂μ h, assemblyValid κ μ C d (h,ω) := by
  filter_upwards [traceValid_ae κ μ d htrace h,
    ae_all_iff.mpr (fun n => ae_all_iff.mpr (fun i => ae_all_iff.mpr (fun j =>
      rawCoordinate_eq_block_ae κ μ C d hd htrace hdiag hcoherent n h i j))),
    ae_all_iff.mpr (fun i => rawCoordinate_diagonal_ae κ μ C d hd htrace hdiag i h)]
    with ω ht hb hdg
  exact ⟨ht,hb,hdg⟩

def assembledCoordinate (d : ℝ) (i j : ℕ) (z : H × Ω) : ℂ := by
  classical
  exact if assemblyValid κ μ C d z then rawCoordinate μ C i j z else 0

theorem measurable_assembledCoordinate (d : ℝ) (i j : ℕ) :
    Measurable (assembledCoordinate κ μ C d i j) := by
  classical
  exact (measurable_rawCoordinate μ C i j).piecewise
    (measurableSet_assemblyValid κ μ C d) measurable_const

theorem assembledCoordinate_block_positive (d : ℝ) (n : ℕ) (z : H × Ω) :
    Matrix.PosSemidef (fun i j : Fin n => assembledCoordinate κ μ C d i.val j.val z) := by
  classical
  by_cases hz : assemblyValid κ μ C d z
  · have he : (fun i j : Fin n => assembledCoordinate κ μ C d i.val j.val z) =
        blockDensity μ C n z.1 z.2 := by
      funext i j
      simpa only [assembledCoordinate, if_pos hz] using hz.2.1 n i j
    rw [he]
    exact blockDensity_positive μ C n z.1 z.2
  · simp only [assembledCoordinate, if_neg hz]
    change (0 : Matrix (Fin n) (Fin n) ℂ).PosSemidef
    exact Matrix.PosSemidef.zero

theorem assembledCoordinate_hermitian (d : ℝ) (i j : ℕ) (z : H × Ω) :
    star (assembledCoordinate κ μ C d j i z) = assembledCoordinate κ μ C d i j z := by
  let n := max i j + 1
  let a : Fin n := ⟨i, Nat.lt_succ_of_le (Nat.le_max_left i j)⟩
  let b : Fin n := ⟨j, Nat.lt_succ_of_le (Nat.le_max_right i j)⟩
  exact (assembledCoordinate_block_positive κ μ C d n z).isHermitian.apply a b

theorem assembledCoordinate_diagonal_re_nonneg (d : ℝ) (i : ℕ) (z : H × Ω) :
    0 ≤ (assembledCoordinate κ μ C d i i z).re := by
  have hn := (assembledCoordinate_block_positive κ μ C d (i + 1) z).diag_nonneg
    (i := (⟨i, Nat.lt_succ_self i⟩ : Fin (i+1)))
  exact (Complex.nonneg_iff.mp hn).1

theorem assembledCoordinate_diagonal_of_valid {d : ℝ} {z : H × Ω}
    (hz : assemblyValid κ μ C d z) (i : ℕ) :
    (assembledCoordinate κ μ C d i i z).re = diagonalDensity κ μ i z.1 z.2 := by
  classical
  simp only [assembledCoordinate, if_pos hz]
  simpa only [Complex.ofReal_re] using congrArg Complex.re (hz.2.2 i)

theorem summable_assembledCoordinate_diagonal (d : ℝ) (z : H × Ω) :
    Summable (fun i => (assembledCoordinate κ μ C d i i z).re) := by
  classical
  by_cases hz : assemblyValid κ μ C d z
  · have he : (fun i => (assembledCoordinate κ μ C d i i z).re) =
        (fun i => diagonalDensity κ μ i z.1 z.2) :=
      funext (assembledCoordinate_diagonal_of_valid κ μ C hz)
    rw [he]
    exact summable_diagonalDensity_of_valid κ μ hz.1
  · simp only [assembledCoordinate, if_neg hz, Complex.zero_re]
    exact summable_zero

theorem tsum_assembledCoordinate_diagonal_of_valid {d : ℝ} (hd : 0 ≤ d) {z : H × Ω}
    (hz : assemblyValid κ μ C d z) :
    (∑' i, (assembledCoordinate κ μ C d i i z).re) = d := by
  simp_rw [assembledCoordinate_diagonal_of_valid κ μ C hz]
  exact tsum_diagonalDensity_of_valid κ μ hd hz.1

theorem tsum_assembledCoordinate_diagonal_le (d : ℝ) (hd : 0 ≤ d) (z : H × Ω) :
    (∑' i, (assembledCoordinate κ μ C d i i z).re) ≤ d := by
  classical
  by_cases hz : assemblyValid κ μ C d z
  · exact (tsum_assembledCoordinate_diagonal_of_valid κ μ C hd hz).le
  · simpa only [assembledCoordinate, if_neg hz, Complex.zero_re, tsum_zero] using hd

theorem assembledCoordinate_ae_eq_raw (d : ℝ) (hd : 0 ≤ d)
    (htrace : ∀ h (s : Set Ω), MeasurableSet s →
      (∑' i, κ i h s) = ENNReal.ofReal d * μ h s)
    (hdiag : ∀ n (i : Fin n), (C n).probe (basisVector i) = κ i.val)
    (hcoherent : ∀ n m (hnm : n ≤ m) h s, MeasurableSet s → ∀ i j : Fin n,
      (C m).effect h s (Fin.castLE hnm i) (Fin.castLE hnm j) = (C n).effect h s i j)
    (h : H) (i j : ℕ) :
    (fun ω => assembledCoordinate κ μ C d i j (h,ω)) =ᵐ[μ h]
      (fun ω => rawCoordinate μ C i j (h,ω)) := by
  classical
  filter_upwards [assemblyValid_ae κ μ C d hd htrace hdiag hcoherent h] with ω hω
  simp [assembledCoordinate, hω]

theorem integrable_assembledCoordinate (d : ℝ) (hd : 0 ≤ d)
    (htrace : ∀ h (s : Set Ω), MeasurableSet s →
      (∑' i, κ i h s) = ENNReal.ofReal d * μ h s)
    (hdiag : ∀ n (i : Fin n), (C n).probe (basisVector i) = κ i.val)
    (hcoherent : ∀ n m (hnm : n ≤ m) h s, MeasurableSet s → ∀ i j : Fin n,
      (C m).effect h s (Fin.castLE hnm i) (Fin.castLE hnm j) = (C n).effect h s i j)
    (h : H) (i j : ℕ) :
    Integrable (fun ω => assembledCoordinate κ μ C d i j (h,ω)) (μ h) :=
  (integrable_rawCoordinate κ μ C d hd htrace hdiag i j h).congr
    (assembledCoordinate_ae_eq_raw κ μ C d hd htrace hdiag hcoherent h i j).symm

theorem setIntegral_assembledCoordinate (d : ℝ) (hd : 0 ≤ d)
    (htrace : ∀ h (s : Set Ω), MeasurableSet s →
      (∑' i, κ i h s) = ENNReal.ofReal d * μ h s)
    (hdiag : ∀ n (i : Fin n), (C n).probe (basisVector i) = κ i.val)
    (hcoherent : ∀ n m (hnm : n ≤ m) h s, MeasurableSet s → ∀ i j : Fin n,
      (C m).effect h s (Fin.castLE hnm i) (Fin.castLE hnm j) = (C n).effect h s i j)
    (n : ℕ) (h : H) (s : Set Ω) (hs : MeasurableSet s) (i j : Fin n) :
    (∫ ω in s, assembledCoordinate κ μ C d i.val j.val (h,ω) ∂μ h) =
      (C n).effect h s i j := by
  have ha : (fun ω => assembledCoordinate κ μ C d i.val j.val (h,ω)) =ᵐ[μ h]
      (fun ω => blockDensity μ C n h ω i j) := by
    classical
    filter_upwards [assemblyValid_ae κ μ C d hd htrace hdiag hcoherent h] with ω hω
    simpa only [assembledCoordinate, if_pos hω] using hω.2.1 n i j
  rw [integral_congr_ae (ae_restrict_of_ae ha)]
  exact setIntegral_blockEntry κ μ C d hd htrace hdiag n h s hs i j

theorem ae_tsum_assembledCoordinate_diagonal (d : ℝ) (hd : 0 ≤ d)
    (htrace : ∀ h (s : Set Ω), MeasurableSet s →
      (∑' i, κ i h s) = ENNReal.ofReal d * μ h s)
    (hdiag : ∀ n (i : Fin n), (C n).probe (basisVector i) = κ i.val)
    (hcoherent : ∀ n m (hnm : n ≤ m) h s, MeasurableSet s → ∀ i j : Fin n,
      (C m).effect h s (Fin.castLE hnm i) (Fin.castLE hnm j) = (C n).effect h s i j)
    (h : H) : ∀ᵐ ω ∂μ h, (∑' i, (assembledCoordinate κ μ C d i i (h,ω)).re) = d := by
  filter_upwards [assemblyValid_ae κ μ C d hd htrace hdiag hcoherent h] with ω hω
  exact tsum_assembledCoordinate_diagonal_of_valid κ μ C hd hω

end CountableAssembly
end QuantumProver.ElegantJointMeasurement.NormalChoiRadonNikodym

namespace QuantumProver.ElegantJointMeasurement.NormalChoiRadonNikodym
open QuantumProver.ElegantJointMeasurement.ContinuousInstrumentRadonNikodym
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

variable {H Ω : Type*} [MeasurableSpace H] [MeasurableSpace Ω]
variable [MeasurableSpace.CountableOrCountablyGenerated H Ω]

theorem exists_joint_countable_positive_density
    (κ : ℕ → Kernel H Ω) (μ : Kernel H Ω) [IsMarkovKernel μ]
    (C : (n : ℕ) → PositiveChoiKernel (H := H) (Ω := Ω) (Q := Fin n))
    (d : ℝ) (hd : 0 ≤ d)
    (htrace : ∀ h (s : Set Ω), MeasurableSet s →
      (∑' i, κ i h s) = ENNReal.ofReal d * μ h s)
    (hdiag : ∀ n (i : Fin n), (C n).probe (basisVector i) = κ i.val)
    (hcoherent : ∀ n m (hnm : n ≤ m) h s, MeasurableSet s → ∀ i j : Fin n,
      (C m).effect h s (Fin.castLE hnm i) (Fin.castLE hnm j) = (C n).effect h s i j) :
    ∃ F : H → Ω → ℕ → ℕ → ℂ,
      (∀ i j, Measurable (fun z : H × Ω => F z.1 z.2 i j)) ∧
      (∀ n h ω, Matrix.PosSemidef (fun i j : Fin n => F h ω i.val j.val)) ∧
      (∀ h ω, Summable (fun i => (F h ω i i).re)) ∧
      (∀ h ω, (∑' i, (F h ω i i).re) ≤ d) ∧
      (∀ h, ∀ᵐ ω ∂μ h, (∑' i, (F h ω i i).re) = d) ∧
      (∀ i j h, Integrable (fun ω => F h ω i j) (μ h)) ∧
      (∀ n h (s : Set Ω), MeasurableSet s → ∀ i j : Fin n,
        (∫ ω in s, F h ω i.val j.val ∂μ h) = (C n).effect h s i j) := by
  letI : ∀ n (v : Fin n → ℂ), IsFiniteKernel ((C n).probe v) :=
    fun n v => block_probe_isFinite κ μ C d hd htrace hdiag n v
  let F : H → Ω → ℕ → ℕ → ℂ := fun h ω i j => assembledCoordinate κ μ C d i j (h,ω)
  refine ⟨F, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j
    exact measurable_assembledCoordinate κ μ C d i j
  · intro n h ω
    exact assembledCoordinate_block_positive κ μ C d n (h,ω)
  · intro h ω
    exact summable_assembledCoordinate_diagonal κ μ C d (h,ω)
  · intro h ω
    exact tsum_assembledCoordinate_diagonal_le κ μ C d hd (h,ω)
  · intro h
    exact ae_tsum_assembledCoordinate_diagonal κ μ C d hd htrace hdiag hcoherent h
  · intro i j h
    exact integrable_assembledCoordinate κ μ C d hd htrace hdiag hcoherent h i j
  · intro n h s hs i j
    exact setIntegral_assembledCoordinate κ μ C d hd htrace hdiag hcoherent n h s hs i j

end QuantumProver.ElegantJointMeasurement.NormalChoiRadonNikodym

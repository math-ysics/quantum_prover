import QuantumProver.InformationTheory.ElegantJointMeasurement.InstrumentTestIntegral
import QuantumProver.LinearAlgebra.HilbertNuclearCompressionExpansion
import QuantumProver.InformationTheory.ElegantJointMeasurement.NormalNuclearDensity

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory Filter Set InnerProductSpace
open scoped BigOperators Topology InnerProduct ComplexOrder

namespace QuantumProver.ElegantJointMeasurement.HilbertControlledNuclearTest

open QuantumProver.NuclearOperator QuantumProver.HilbertNuclearCompression
open QuantumProver.HilbertNuclearCompressionExpansion

variable {H Ω : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [MeasurableSpace Ω]

local instance nuclearNormedGroup : NormedAddCommGroup (Nuclear ℂ H H) := inferInstance
local instance nuclearNormedSpace : NormedSpace ℂ (Nuclear ℂ H H) := inferInstance

def nuclearEntry (x y : H) : Nuclear ℂ H H →L[ℂ] ℂ :=
  ((innerSL ℂ x).comp (ContinuousLinearMap.apply ℂ H y)).comp
    (toOperator (𝕜 := ℂ) (E := H) (F := H))

@[simp] theorem nuclearEntry_apply (x y : H) (T : Nuclear ℂ H H) :
    nuclearEntry x y T = inner ℂ x (toOperator T y) := rfl

def realProbe (v : H) : Nuclear ℂ H H →L[ℝ] ℝ :=
  Complex.reCLM.comp ((nuclearEntry v v).restrictScalars ℝ)

def complexProbe (v : H) : Nuclear ℂ H H →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp (realProbe v)

@[simp] theorem complexProbe_apply (v : H) (T : Nuclear ℂ H H) :
    complexProbe v T = ((inner ℂ v (toOperator T v)).re : ℂ) := rfl

theorem probe_polarization (T : Nuclear ℂ H H)
    (hT : (toOperator T).IsPositive) (x y : H) :
    (complexProbe (x + y) T - complexProbe (x - y) T -
        Complex.I * complexProbe (x + Complex.I • y) T +
        Complex.I * complexProbe (x - Complex.I • y) T) / 4 =
      inner ℂ x (toOperator T y) := by
  have hs := hT.isSymmetric
  have hp (z : H) : complexProbe z T = inner ℂ (toOperator T z) z := by
    change ((RCLike.re (inner ℂ z ((toOperator T).toLinearMap z)) : ℝ) : ℂ) = _
    exact (hs.coe_re_inner_self_apply z).trans (hs z z).symm
  simp only [hp]
  exact (inner_map_polarization' (toOperator T).toLinearMap x y).symm.trans
    (hs x y)

def rawPairTest (κ : H → Measure Ω) (w : Ω → ℂ) (x y : H) : ℂ :=
  ((∫ ω, w ω ∂κ (x + y)) - (∫ ω, w ω ∂κ (x - y)) -
      Complex.I * (∫ ω, w ω ∂κ (x + Complex.I • y)) +
      Complex.I * (∫ ω, w ω ∂κ (x - Complex.I • y))) / 4

def rawFiniteTest (b : HilbertBasis ℕ ℂ H) (κ : H → Measure Ω)
    (W : Ω → H →L[ℂ] H) (n : ℕ) : ℂ :=
  ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
    rawPairTest κ (fun ω => inner ℂ (b i) (W ω (b j))) (b j) (b i)

def densityTest (W : H →L[ℂ] H) (T : Nuclear ℂ H H) : ℂ :=
  QuantumProver.HilbertNuclearTrace.trace (compose W (ContinuousLinearMap.id ℂ H) T)

theorem norm_densityTest_le (W : H →L[ℂ] H) (T : Nuclear ℂ H H) :
    ‖densityTest W T‖ ≤ ‖W‖ * ‖T‖ := by
  refine (QuantumProver.HilbertNuclearTrace.norm_trace_apply_le _).trans
    ((norm_compose_apply_le W (ContinuousLinearMap.id ℂ H) T).trans ?_)
  calc
    (‖W‖ * ‖ContinuousLinearMap.id ℂ H‖) * ‖T‖ ≤ (‖W‖ * 1) * ‖T‖ :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le (norm_nonneg W))
        (norm_nonneg T)
    _ = ‖W‖ * ‖T‖ := by ring

theorem densityTest_compression_eq_sum (b : HilbertBasis ℕ ℂ H)
    (s : Finset ℕ) (W : H →L[ℂ] H) (T : Nuclear ℂ H H) :
    densityTest W (compression b s T) =
      ∑ i ∈ s, ∑ j ∈ s, inner ℂ (b i) (W (b j)) *
        inner ℂ (b j) (toOperator T (b i)) := by
  classical
  rw [compression_eq_coefficientCompression]
  simp only [densityTest, coefficientCompression, map_sum, map_smul,
    compose_rankOne, QuantumProver.HilbertNuclearTrace.trace_rankOne,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
    innerSL_apply_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  exact mul_comm _ _

omit [CompleteSpace H] in
theorem measurable_observable_entry (b : HilbertBasis ℕ ℂ H)
    (W : Ω → H →L[ℂ] H)
    (hW : ∀ x : H, StronglyMeasurable (fun ω => W ω x)) (i j : ℕ) :
    Measurable (fun ω => inner ℂ (b i) (W ω (b j))) :=
  ((innerSL ℂ (b i)).continuous.comp_stronglyMeasurable (hW (b j))).measurable

omit [CompleteSpace H] [MeasurableSpace Ω] in
theorem norm_observable_entry_le (b : HilbertBasis ℕ ℂ H)
    (W : Ω → H →L[ℂ] H) {C : ℝ} (hbound : ∀ ω, ‖W ω‖ ≤ C)
    (i j : ℕ) (ω : Ω) : ‖inner ℂ (b i) (W ω (b j))‖ ≤ C := by
  calc
    ‖inner ℂ (b i) (W ω (b j))‖ ≤ ‖b i‖ * ‖W ω (b j)‖ := norm_inner_le_norm _ _
    _ ≤ ‖b i‖ * (‖W ω‖ * ‖b j‖) :=
      mul_le_mul_of_nonneg_left ((W ω).le_opNorm (b j)) (norm_nonneg _)
    _ = ‖W ω‖ := by rw [b.orthonormal.norm_eq_one i, b.orthonormal.norm_eq_one j]; ring
    _ ≤ C := hbound ω

variable {μ : Measure Ω}

theorem complexProbe_setIntegral (Γ : Set Ω → Nuclear ℂ H H)
    (κ : H → Measure Ω) [∀ v, IsFiniteMeasure (κ v)] (D : Ω → Nuclear ℂ H H)
    (hD : Integrable D μ)
    (hset : ∀ s : Set Ω, MeasurableSet s → (∫ ω in s, D ω ∂μ) = Γ s)
    (hκ : ∀ v (s : Set Ω), MeasurableSet s →
      (κ v s).toReal = (inner ℂ v (toOperator (Γ s) v)).re)
    (v : H) (s : Set Ω) (hs : MeasurableSet s) :
    (∫ ω in s, complexProbe v (D ω) ∂μ) = ∫ _ω in s, (1 : ℂ) ∂κ v := by
  rw [(complexProbe v).integral_comp_comm hD.integrableOn, hset s hs]
  simp only [complexProbe_apply]
  rw [← hκ v s hs]
  simp [measureReal_def]

theorem integral_observable_probe_eq (Γ : Set Ω → Nuclear ℂ H H)
    (κ : H → Measure Ω) [∀ v, IsFiniteMeasure (κ v)] (D : Ω → Nuclear ℂ H H)
    (hD : Integrable D μ)
    (hset : ∀ s : Set Ω, MeasurableSet s → (∫ ω in s, D ω ∂μ) = Γ s)
    (hκ : ∀ v (s : Set Ω), MeasurableSet s →
      (κ v s).toReal = (inner ℂ v (toOperator (Γ s) v)).re)
    (w : Ω → ℂ) (hw : Measurable w) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ ω, ‖w ω‖ ≤ C) (v : H) :
    (∫ ω, w ω ∂κ v) = ∫ ω, w ω * complexProbe v (D ω) ∂μ := by
  symm
  simpa only [mul_one] using
    QuantumProver.ElegantJointMeasurement.HilbertInstrumentTestIntegral.integral_bounded_mul_eq_of_setIntegral_eq
      ((complexProbe v).integrable_comp hD) (integrable_const (1 : ℂ))
      (complexProbe_setIntegral Γ κ D hD hset hκ v) hw hC hbound

theorem rawPairTest_eq_densityPair (Γ : Set Ω → Nuclear ℂ H H)
    (κ : H → Measure Ω) [∀ v, IsFiniteMeasure (κ v)] (D : Ω → Nuclear ℂ H H)
    (hD : Integrable D μ) (hpos : ∀ᵐ ω ∂μ, (toOperator (D ω)).IsPositive)
    (hset : ∀ s : Set Ω, MeasurableSet s → (∫ ω in s, D ω ∂μ) = Γ s)
    (hκ : ∀ v (s : Set Ω), MeasurableSet s →
      (κ v s).toReal = (inner ℂ v (toOperator (Γ s) v)).re)
    (w : Ω → ℂ) (hw : Measurable w) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ ω, ‖w ω‖ ≤ C) (x y : H) :
    rawPairTest κ w x y = ∫ ω, w ω * inner ℂ x (toOperator (D ω) y) ∂μ := by
  have hint (v : H) : Integrable (fun ω => w ω * complexProbe v (D ω)) μ :=
    QuantumProver.ElegantJointMeasurement.HilbertInstrumentTestIntegral.integrable_bounded_mul
      ((complexProbe v).integrable_comp hD) hw hbound
  unfold rawPairTest
  simp only [integral_observable_probe_eq Γ κ D hD hset hκ w hw hC hbound]
  have hcombine :
      ((∫ ω, w ω * complexProbe (x + y) (D ω) ∂μ) -
          (∫ ω, w ω * complexProbe (x - y) (D ω) ∂μ) -
          Complex.I * (∫ ω, w ω * complexProbe (x + Complex.I • y) (D ω) ∂μ) +
          Complex.I * (∫ ω, w ω * complexProbe (x - Complex.I • y) (D ω) ∂μ)) / 4 =
        ∫ ω, w ω * ((complexProbe (x + y) (D ω) - complexProbe (x - y) (D ω) -
          Complex.I * complexProbe (x + Complex.I • y) (D ω) +
          Complex.I * complexProbe (x - Complex.I • y) (D ω)) / 4) ∂μ := by
    have heq : (fun ω => w ω * ((complexProbe (x + y) (D ω) - complexProbe (x - y) (D ω) -
          Complex.I * complexProbe (x + Complex.I • y) (D ω) +
          Complex.I * complexProbe (x - Complex.I • y) (D ω)) / 4)) =
        (fun ω => (w ω * complexProbe (x + y) (D ω) - w ω * complexProbe (x - y) (D ω) -
          Complex.I * (w ω * complexProbe (x + Complex.I • y) (D ω)) +
          Complex.I * (w ω * complexProbe (x - Complex.I • y) (D ω))) / 4) := by
      funext ω
      ring
    rw [heq, integral_div]
    apply congrArg (fun z : ℂ => z / 4)
    symm
    calc
      (∫ ω, w ω * complexProbe (x + y) (D ω) - w ω * complexProbe (x - y) (D ω) -
          Complex.I * (w ω * complexProbe (x + Complex.I • y) (D ω)) +
          Complex.I * (w ω * complexProbe (x - Complex.I • y) (D ω)) ∂μ) =
        (∫ ω, w ω * complexProbe (x + y) (D ω) - w ω * complexProbe (x - y) (D ω) -
          Complex.I * (w ω * complexProbe (x + Complex.I • y) (D ω)) ∂μ) +
          (∫ ω, Complex.I * (w ω * complexProbe (x - Complex.I • y) (D ω)) ∂μ) :=
        integral_add
          (((hint (x + y)).sub (hint (x - y))).sub
            ((hint (x + Complex.I • y)).const_mul Complex.I))
          ((hint (x - Complex.I • y)).const_mul Complex.I)
      _ = ((∫ ω, w ω * complexProbe (x + y) (D ω) -
          w ω * complexProbe (x - y) (D ω) ∂μ) -
          (∫ ω, Complex.I * (w ω * complexProbe (x + Complex.I • y) (D ω)) ∂μ)) +
          (∫ ω, Complex.I * (w ω * complexProbe (x - Complex.I • y) (D ω)) ∂μ) :=
        congrArg (fun z : ℂ => z +
          (∫ ω, Complex.I * (w ω * complexProbe (x - Complex.I • y) (D ω)) ∂μ))
          (integral_sub ((hint (x + y)).sub (hint (x - y)))
            ((hint (x + Complex.I • y)).const_mul Complex.I))
      _ = ((∫ ω, w ω * complexProbe (x + y) (D ω) ∂μ) -
          (∫ ω, w ω * complexProbe (x - y) (D ω) ∂μ) -
          Complex.I * (∫ ω, w ω * complexProbe (x + Complex.I • y) (D ω) ∂μ)) +
          Complex.I * (∫ ω, w ω * complexProbe (x - Complex.I • y) (D ω) ∂μ) := by
        rw [integral_const_mul, integral_const_mul]
        exact congrArg (fun z : ℂ => z -
          Complex.I * (∫ ω, w ω * complexProbe (x + Complex.I • y) (D ω) ∂μ) +
          Complex.I * (∫ ω, w ω * complexProbe (x - Complex.I • y) (D ω) ∂μ))
          (integral_sub (hint (x + y)) (hint (x - y)))
  rw [hcombine]
  apply integral_congr_ae
  filter_upwards [hpos] with ω hω
  rw [probe_polarization _ hω]

theorem integrable_compressed_densityTest (b : HilbertBasis ℕ ℂ H)
    (W : Ω → H →L[ℂ] H) (hW : ∀ x : H, StronglyMeasurable (fun ω => W ω x))
    {C : ℝ} (hbound : ∀ ω, ‖W ω‖ ≤ C)
    (D : Ω → Nuclear ℂ H H) (hD : Integrable D μ) (n : ℕ) :
    Integrable (fun ω => densityTest (W ω) (compression b (Finset.range n) (D ω))) μ := by
  simp only [densityTest_compression_eq_sum]
  apply integrable_finsetSum _
  intro i hi
  apply integrable_finsetSum _
  intro j hj
  exact QuantumProver.ElegantJointMeasurement.HilbertInstrumentTestIntegral.integrable_bounded_mul
    ((nuclearEntry (b j) (b i)).integrable_comp hD)
    (measurable_observable_entry b W hW i j) (norm_observable_entry_le b W hbound i j)

theorem rawFiniteTest_eq_densityTest (b : HilbertBasis ℕ ℂ H)
    (Γ : Set Ω → Nuclear ℂ H H) (κ : H → Measure Ω) [∀ v, IsFiniteMeasure (κ v)]
    (D : Ω → Nuclear ℂ H H) (hD : Integrable D μ)
    (hpos : ∀ᵐ ω ∂μ, (toOperator (D ω)).IsPositive)
    (hset : ∀ s : Set Ω, MeasurableSet s → (∫ ω in s, D ω ∂μ) = Γ s)
    (hκ : ∀ v (s : Set Ω), MeasurableSet s →
      (κ v s).toReal = (inner ℂ v (toOperator (Γ s) v)).re)
    (W : Ω → H →L[ℂ] H) (hW : ∀ x : H, StronglyMeasurable (fun ω => W ω x))
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ ω, ‖W ω‖ ≤ C) (n : ℕ) :
    rawFiniteTest b κ W n =
      ∫ ω, densityTest (W ω) (compression b (Finset.range n) (D ω)) ∂μ := by
  have hint (i j : ℕ) : Integrable (fun ω =>
      inner ℂ (b i) (W ω (b j)) * inner ℂ (b j) (toOperator (D ω) (b i))) μ :=
    QuantumProver.ElegantJointMeasurement.HilbertInstrumentTestIntegral.integrable_bounded_mul
      ((nuclearEntry (b j) (b i)).integrable_comp hD)
      (measurable_observable_entry b W hW i j) (norm_observable_entry_le b W hbound i j)
  simp only [rawFiniteTest, densityTest_compression_eq_sum]
  rw [integral_finsetSum _ (fun i hi => integrable_finsetSum _ (fun j hj => hint i j))]
  apply Finset.sum_congr rfl
  intro i hi
  rw [integral_finsetSum _ (fun j hj => hint i j)]
  apply Finset.sum_congr rfl
  intro j hj
  exact rawPairTest_eq_densityPair Γ κ D hD hpos hset hκ _
    (measurable_observable_entry b W hW i j) hC (norm_observable_entry_le b W hbound i j) _ _

theorem compressed_densityTest_tendsto (b : HilbertBasis ℕ ℂ H)
    (W : H →L[ℂ] H) (T : Nuclear ℂ H H) :
    Tendsto (fun n : ℕ => densityTest W (compression b (Finset.range n) T))
      atTop (𝓝 (densityTest W T)) :=
  ((QuantumProver.HilbertNuclearTrace.trace (𝕜 := ℂ) (E := H)).comp
    (compose W (ContinuousLinearMap.id ℂ H))).continuous.tendsto T |>.comp
      (initial_compression_tendsto b T)

theorem integrable_densityTest (b : HilbertBasis ℕ ℂ H)
    (W : Ω → H →L[ℂ] H) (hW : ∀ x : H, StronglyMeasurable (fun ω => W ω x))
    {C : ℝ} (hbound : ∀ ω, ‖W ω‖ ≤ C)
    (D : Ω → Nuclear ℂ H H) (hD : Integrable D μ) :
    Integrable (fun ω => densityTest (W ω) (D ω)) μ := by
  have hm : AEStronglyMeasurable (fun ω => densityTest (W ω) (D ω)) μ :=
    aestronglyMeasurable_of_tendsto_ae atTop
      (fun n => (integrable_compressed_densityTest b W hW hbound D hD n).aestronglyMeasurable)
      (ae_of_all _ (fun ω => compressed_densityTest_tendsto b (W ω) (D ω)))
  exact (hD.norm.const_mul C).mono' hm (ae_of_all _ fun ω =>
    (norm_densityTest_le (W ω) (D ω)).trans
      (mul_le_mul_of_nonneg_right (hbound ω) (norm_nonneg _)))

theorem rawFiniteTest_tendsto_densityTest (b : HilbertBasis ℕ ℂ H)
    (Γ : Set Ω → Nuclear ℂ H H) (κ : H → Measure Ω) [∀ v, IsFiniteMeasure (κ v)]
    (D : Ω → Nuclear ℂ H H) (hD : Integrable D μ)
    (hpos : ∀ᵐ ω ∂μ, (toOperator (D ω)).IsPositive)
    (hset : ∀ s : Set Ω, MeasurableSet s → (∫ ω in s, D ω ∂μ) = Γ s)
    (hκ : ∀ v (s : Set Ω), MeasurableSet s →
      (κ v s).toReal = (inner ℂ v (toOperator (Γ s) v)).re)
    (W : Ω → H →L[ℂ] H) (hW : ∀ x : H, StronglyMeasurable (fun ω => W ω x))
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ ω, ‖W ω‖ ≤ C) :
    Tendsto (rawFiniteTest b κ W) atTop (𝓝 (∫ ω, densityTest (W ω) (D ω) ∂μ)) := by
  have heq : rawFiniteTest b κ W = fun n =>
      ∫ ω, densityTest (W ω) (compression b (Finset.range n) (D ω)) ∂μ :=
    funext (rawFiniteTest_eq_densityTest b Γ κ D hD hpos hset hκ W hW hC hbound)
  rw [heq]
  apply tendsto_integral_of_dominated_convergence (fun ω => C * ‖D ω‖)
  · intro n
    exact (integrable_compressed_densityTest b W hW hbound D hD n).aestronglyMeasurable
  · exact hD.norm.const_mul C
  · intro n
    exact ae_of_all _ fun ω => (norm_densityTest_le _ _).trans
      ((mul_le_mul_of_nonneg_left (norm_compression_apply_le b (Finset.range n) (D ω))
        (norm_nonneg (W ω))).trans
        (mul_le_mul_of_nonneg_right (hbound ω) (norm_nonneg _)))
  · exact ae_of_all _ fun ω => compressed_densityTest_tendsto b (W ω) (D ω)

def controlledComplement (P : Ω → H →L[ℂ] H) (ω : Ω) : H →L[ℂ] H :=
  ContinuousLinearMap.id ℂ H - P ω

omit [CompleteSpace H] [MeasurableSpace Ω] in
theorem controlledComplement_idempotent (P : Ω → H →L[ℂ] H)
    (hId : ∀ ω, (P ω).comp (P ω) = P ω) (ω : Ω) :
    (controlledComplement P ω).comp (controlledComplement P ω) = controlledComplement P ω := by
  ext x
  have hx : P ω (P ω x) = P ω x := congrArg (fun L : H →L[ℂ] H => L x) (hId ω)
  simp only [controlledComplement, ContinuousLinearMap.comp_apply,
    sub_apply, ContinuousLinearMap.id_apply, map_sub, hx]
  abel

theorem trace_idempotent_sandwich (Q : H →L[ℂ] H) (hQ : Q.comp Q = Q)
    (T : Nuclear ℂ H H) :
    QuantumProver.HilbertNuclearTrace.trace (compose Q Q T) = densityTest Q T := by
  rw [QuantumProver.ElegantJointMeasurement.NormalCPInstruments.trace_compose_cycle, hQ]
  have hc : densityTest Q T = QuantumProver.HilbertNuclearTrace.trace
      (compose (ContinuousLinearMap.id ℂ H) Q T) := by
    simpa only [densityTest, ContinuousLinearMap.id_comp] using
      QuantumProver.ElegantJointMeasurement.NormalCPInstruments.trace_compose_cycle Q (ContinuousLinearMap.id ℂ H) T
  exact hc.symm

theorem complement_integral_eq_zero_of_raw_response_zero (b : HilbertBasis ℕ ℂ H)
    (Γ : Set Ω → Nuclear ℂ H H) (κ : H → Measure Ω) [∀ v, IsFiniteMeasure (κ v)]
    (D : Ω → Nuclear ℂ H H) (hD : Integrable D μ)
    (hpos : ∀ᵐ ω ∂μ, (toOperator (D ω)).IsPositive)
    (hset : ∀ s : Set Ω, MeasurableSet s → (∫ ω in s, D ω ∂μ) = Γ s)
    (hκ : ∀ v (s : Set Ω), MeasurableSet s →
      (κ v s).toReal = (inner ℂ v (toOperator (Γ s) v)).re)
    (P : Ω → H →L[ℂ] H) (hP : ∀ x : H, StronglyMeasurable (fun ω => P ω x))
    (hId : ∀ ω, (P ω).comp (P ω) = P ω)
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ ω, ‖controlledComplement P ω‖ ≤ C)
    (hraw : Tendsto (rawFiniteTest b κ (controlledComplement P)) atTop (𝓝 0)) :
    (∫ ω, (QuantumProver.HilbertNuclearTrace.trace
      (compose (controlledComplement P ω) (controlledComplement P ω) (D ω))).re ∂μ) = 0 := by
  have hW (x : H) : StronglyMeasurable (fun ω => controlledComplement P ω x) :=
    stronglyMeasurable_const.sub (hP x)
  have hlim := rawFiniteTest_tendsto_densityTest b Γ κ D hD hpos hset hκ
    (controlledComplement P) hW hC hbound
  have hzero : (∫ ω, densityTest (controlledComplement P ω) (D ω) ∂μ) = 0 :=
    tendsto_nhds_unique hlim hraw
  have heq (ω : Ω) : QuantumProver.HilbertNuclearTrace.trace
      (compose (controlledComplement P ω) (controlledComplement P ω) (D ω)) =
        densityTest (controlledComplement P ω) (D ω) :=
    trace_idempotent_sandwich _ (controlledComplement_idempotent P hId ω) _
  simp only [heq]
  change (∫ ω, RCLike.re (densityTest (controlledComplement P ω) (D ω)) ∂μ) = 0
  rw [integral_re (integrable_densityTest b (controlledComplement P) hW hbound D hD), hzero]
  rfl

section PhysicalInstrument

open QuantumProver.ElegantJointMeasurement.HilbertChoi

variable {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {Hist : Type*} [MeasurableSpace Hist]
variable [MeasurableSpace.CountableOrCountablyGenerated Hist Ω]

omit [MeasurableSpace.CountableOrCountablyGenerated Hist Ω] in

theorem physicalProbe_isFinite
    (P : QuantumProver.ElegantJointMeasurement.NormalCPInstruments.Instrument I E Hist Ω)
    (v : BlockSpace I E) (h : Hist) :
    IsFiniteMeasure (QuantumProver.ElegantJointMeasurement.NormalChoiKernels.Instrument.physicalProbe P v h) := by
  constructor
  rw [QuantumProver.ElegantJointMeasurement.NormalChoiKernels.Instrument.physicalProbe_apply P v h univ MeasurableSet.univ]
  exact ENNReal.ofReal_lt_top

theorem exists_physical_density_controlled_test
    (P : QuantumProver.ElegantJointMeasurement.NormalCPInstruments.Instrument I E Hist Ω)
    (b : HilbertBasis ℕ ℂ (BlockSpace I E)) (h : Hist) :
    ∃ D : Ω → Nuclear ℂ (BlockSpace I E) (BlockSpace I E),
      Integrable D (P.referenceKernel h) ∧
      (∀ ω, (toOperator (D ω)).IsPositive) ∧
      (∀ s : Set Ω, MeasurableSet s →
        (∫ ω in s, D ω ∂P.referenceKernel h) = P.physicalChoi h s) ∧
      ∀ (W : Ω → BlockSpace I E →L[ℂ] BlockSpace I E),
        (∀ x, StronglyMeasurable (fun ω => W ω x)) →
        ∀ C : ℝ, 0 ≤ C → (∀ ω, ‖W ω‖ ≤ C) →
        Tendsto (rawFiniteTest b
          (fun v => QuantumProver.ElegantJointMeasurement.NormalChoiKernels.Instrument.physicalProbe P v h) W)
          atTop (𝓝 (∫ ω, densityTest (W ω) (D ω) ∂P.referenceKernel h)) := by
  obtain ⟨D, hstrong, hmeas, hpos, htrace, hnorm, hmass, hint, hset⟩ :=
    QuantumProver.ElegantJointMeasurement.NormalNuclearDensity.exists_physical_positive_nuclear_density P b
  refine ⟨D h, hint h, hpos h, hset h, ?_⟩
  intro W hW C hC hbound
  haveI : ∀ v : BlockSpace I E,
      IsFiniteMeasure (QuantumProver.ElegantJointMeasurement.NormalChoiKernels.Instrument.physicalProbe P v h) :=
    fun v => physicalProbe_isFinite P v h
  apply rawFiniteTest_tendsto_densityTest b (P.physicalChoi h) _ (D h) (hint h)
    (ae_of_all _ (hpos h)) (hset h) ?_ W hW hC hbound
  intro v s hs
  rw [QuantumProver.ElegantJointMeasurement.NormalChoiKernels.Instrument.physicalProbe_apply P v h s hs]
  exact ENNReal.toReal_ofReal ((P.physicalChoi_isPositive h s hs).re_inner_nonneg_right v)

end PhysicalInstrument
end QuantumProver.ElegantJointMeasurement.HilbertControlledNuclearTest

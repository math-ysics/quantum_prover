import QuantumProver.InformationTheory.ElegantJointMeasurement.RecordedHilbertInstrument
import QuantumProver.InformationTheory.ElegantJointMeasurement.NormalRecordedAbsorption

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory ProbabilityTheory Filter Set InnerProductSpace
open scoped BigOperators Topology ComplexOrder Matrix.Norms.L2Operator

namespace QuantumProver.ElegantJointMeasurement.NormalRecordedConvergence

open QuantumProver.NuclearOperator
open QuantumProver.ElegantJointMeasurement.HilbertChoi QuantumProver.ElegantJointMeasurement.NuclearChoi
open QuantumProver.ElegantJointMeasurement.ContinuousInstrumentRadonNikodym

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
variable {Ω : Type*} [MeasurableSpace Ω]

local instance nuclearMeasurable : MeasurableSpace (Nuclear V) := borel (Nuclear V)
local instance nuclearBorel : BorelSpace (Nuclear V) := ⟨rfl⟩

def responseTraceMeasure (b : HilbertBasis ℕ ℂ V) (κ : V → Measure Ω) : Measure Ω :=
  Measure.sum (fun i : ℕ => κ (b i))

theorem responseTraceMeasure_apply (b : HilbertBasis ℕ ℂ V)
    (Γ : Set Ω → Nuclear V) (κ : V → Measure Ω)
    (hPos : ∀ s, MeasurableSet s → (toOperator (Γ s)).IsPositive)
    (hκ : ∀ v s, MeasurableSet s →
      κ v s = ENNReal.ofReal (inner ℂ v (toOperator (Γ s) v)).re)
    (s : Set Ω) (hs : MeasurableSet s) :
    responseTraceMeasure b κ s = ENNReal.ofReal (QuantumProver.HilbertNuclearTrace.trace (Γ s)).re := by
  have hd := (QuantumProver.HilbertNuclearTrace.hasSum_diagonal b (Γ s)).mapL Complex.reCLM
  change HasSum (fun i : ℕ => (inner ℂ (b i) (toOperator (Γ s) (b i))).re)
    (QuantumProver.HilbertNuclearTrace.trace (Γ s)).re at hd
  have hn (i : ℕ) : 0 ≤ (inner ℂ (b i) (toOperator (Γ s) (b i))).re :=
    (hPos s hs).re_inner_nonneg_right (b i)
  rw [responseTraceMeasure, Measure.sum_apply _ hs]
  simp_rw [hκ _ _ hs]
  rw [← ENNReal.ofReal_tsum_of_nonneg hn hd.summable, hd.tsum_eq]

def responseProbabilityMeasure (b : HilbertBasis ℕ ℂ V) (κ : V → Measure Ω)
    (d : ℝ) : Measure Ω := (ENNReal.ofReal d)⁻¹ • responseTraceMeasure b κ

theorem responseProbabilityMeasure_apply (b : HilbertBasis ℕ ℂ V)
    (κ : V → Measure Ω) (d : ℝ) (s : Set Ω) :
    responseProbabilityMeasure b κ d s =
      (ENNReal.ofReal d)⁻¹ * responseTraceMeasure b κ s := by
  rw [responseProbabilityMeasure, Measure.smul_apply, smul_eq_mul]

theorem responseProbabilityMeasure_isProbability (b : HilbertBasis ℕ ℂ V)
    (Γ : Set Ω → Nuclear V) (κ : V → Measure Ω)
    (hPos : ∀ s, MeasurableSet s → (toOperator (Γ s)).IsPositive)
    (hκ : ∀ v s, MeasurableSet s →
      κ v s = ENNReal.ofReal (inner ℂ v (toOperator (Γ s) v)).re)
    (d : ℝ) (hd : 0 < d) (hMass : (QuantumProver.HilbertNuclearTrace.trace (Γ univ)).re = d) :
    IsProbabilityMeasure (responseProbabilityMeasure b κ d) := by
  constructor
  rw [responseProbabilityMeasure_apply, responseTraceMeasure_apply b Γ κ hPos hκ _ MeasurableSet.univ,
    hMass]
  exact ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.mpr hd).ne' ENNReal.ofReal_ne_top

def responseBlock (b : HilbertBasis ℕ ℂ V) (Γ : Set Ω → Nuclear V) (n : ℕ)
    (s : Set Ω) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => inner ℂ (b i.val) (toOperator (Γ s) (b j.val))

theorem responseBlock_posSemidef (b : HilbertBasis ℕ ℂ V)
    (Γ : Set Ω → Nuclear V)
    (hPos : ∀ s, MeasurableSet s → (toOperator (Γ s)).IsPositive)
    (n : ℕ) (s : Set Ω) (hs : MeasurableSet s) :
    (responseBlock b Γ n s).PosSemidef := by
  let A : V →L[ℂ] V := toOperator (Γ s)
  have hA : A.IsPositive := hPos s hs
  have heq : responseBlock b Γ n s =
      Matrix.gram ℂ (fun i : Fin n => CFC.sqrt A (b i.val)) := by
    ext i j
    change inner ℂ (b i.val) (A (b j.val)) =
      inner ℂ (CFC.sqrt A (b i.val)) (CFC.sqrt A (b j.val))
    calc
      _ = inner ℂ (b i.val) ((CFC.sqrt A).adjoint (CFC.sqrt A (b j.val))) := by
        rw [sqrt_adjoint_eq]
        exact congrArg (fun L : V →L[ℂ] V => inner ℂ (b i.val) (L (b j.val)))
          (sqrt_comp_sqrt A hA).symm
      _ = _ := (CFC.sqrt A).adjoint_inner_right _ _
  rw [heq]
  exact Matrix.posSemidef_gram ℂ _

def responseVector (b : HilbertBasis ℕ ℂ V) (n : ℕ) (v : Fin n → ℂ) : V :=
  ∑ i, v i • b i.val

theorem quadratic_responseBlock (b : HilbertBasis ℕ ℂ V)
    (Γ : Set Ω → Nuclear V) (n : ℕ) (v : Fin n → ℂ) (s : Set Ω) :
    quadratic v (responseBlock b Γ n s) =
      (inner ℂ (responseVector b n v) (toOperator (Γ s) (responseVector b n v))).re := by
  change (dotProduct (star v) (Matrix.mulVec (responseBlock b Γ n s) v)).re = _
  apply congrArg Complex.re
  simp only [responseBlock, responseVector, dotProduct, Matrix.mulVec,
    map_sum, map_smul, inner_sum, sum_inner, inner_smul_left,
    inner_smul_right, Pi.star_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro i hi
  simp only [starRingEnd_apply]
  ring

@[simp] theorem responseVector_basisVector (b : HilbertBasis ℕ ℂ V)
    (n : ℕ) (i : Fin n) : responseVector b n (basisVector i) = b i.val := by
  simp [responseVector, basisVector, Pi.single_apply]

def responseFiniteKernel (b : HilbertBasis ℕ ℂ V)
    (Γ : Set Ω → Nuclear V) (κ : V → Measure Ω)
    (hPos : ∀ s, MeasurableSet s → (toOperator (Γ s)).IsPositive)
    (hκ : ∀ v s, MeasurableSet s →
      κ v s = ENNReal.ofReal (inner ℂ v (toOperator (Γ s) v)).re)
    (n : ℕ) : PositiveChoiKernel (H := Unit) (Ω := Ω) (Q := Fin n) where
  effect _ s := responseBlock b Γ n s
  positive _ s hs := responseBlock_posSemidef b Γ hPos n s hs
  probe v := Kernel.const Unit (κ (responseVector b n v))
  probe_apply := by
    intro v h s hs
    change κ (responseVector b n v) s = _
    rw [hκ _ _ hs, quadratic_responseBlock]

theorem exists_positive_response_nuclear_density (b : HilbertBasis ℕ ℂ V)
    (Γ : Set Ω → Nuclear V) (κ : V → Measure Ω)
    (hPos : ∀ s, MeasurableSet s → (toOperator (Γ s)).IsPositive)
    (hκ : ∀ v s, MeasurableSet s →
      κ v s = ENNReal.ofReal (inner ℂ v (toOperator (Γ s) v)).re)
    (d : ℝ) (hd : 0 < d) (hMass : (QuantumProver.HilbertNuclearTrace.trace (Γ univ)).re = d) :
    ∃ D : Ω → Nuclear V,
      StronglyMeasurable D ∧
      (∀ ω, (toOperator (D ω)).IsPositive) ∧
      (∀ ω, ‖D ω‖ ≤ d) ∧
      Integrable D (responseProbabilityMeasure b κ d) ∧
      (∀ s, MeasurableSet s →
        (∫ ω in s, D ω ∂responseProbabilityMeasure b κ d) = Γ s) := by
  let μ := responseProbabilityMeasure b κ d
  letI : IsProbabilityMeasure μ := responseProbabilityMeasure_isProbability b Γ κ hPos hκ d hd hMass
  let μK : Kernel Unit Ω := Kernel.const Unit μ
  let κK : ℕ → Kernel Unit Ω := fun i => Kernel.const Unit (κ (b i))
  let C : (n : ℕ) → PositiveChoiKernel (H := Unit) (Ω := Ω) (Q := Fin n) :=
    responseFiniteKernel b Γ κ hPos hκ
  have hTrace (h : Unit) (s : Set Ω) (hs : MeasurableSet s) :
      (∑' i, κK i h s) = ENNReal.ofReal d * μK h s := by
    change (∑' i, κ (b i) s) = ENNReal.ofReal d * μ s
    rw [← Measure.sum_apply _ hs]
    change responseTraceMeasure b κ s = _
    rw [responseProbabilityMeasure_apply, ← mul_assoc,
      ENNReal.mul_inv_cancel (ENNReal.ofReal_pos.mpr hd).ne' ENNReal.ofReal_ne_top, one_mul]
  have hDiag (n : ℕ) (i : Fin n) : (C n).probe (basisVector i) = κK i.val := by
    change Kernel.const Unit (κ (responseVector b n (basisVector i))) =
      Kernel.const Unit (κ (b i.val))
    rw [responseVector_basisVector]
  have hCoh (n m : ℕ) (hnm : n ≤ m) (h : Unit) (s : Set Ω) (hs : MeasurableSet s)
      (i j : Fin n) :
      (C m).effect h s (Fin.castLE hnm i) (Fin.castLE hnm j) = (C n).effect h s i j := rfl
  have hΓ (n : ℕ) (h : Unit) (s : Set Ω) (hs : MeasurableSet s) (i j : Fin n) :
      (C n).effect h s i j =
        QuantumProver.ElegantJointMeasurement.NormalNuclearDensity.nuclearCoefficient b i.val j.val (Γ s) := rfl
  obtain ⟨D, hStrong, hMeas, hPositive, hBound, hMassAE, hInt, hSet⟩ :=
    QuantumProver.ElegantJointMeasurement.NormalNuclearDensity.exists_joint_positive_nuclear_density b κK μK C d hd.le
      hTrace hDiag hCoh (fun _ => Γ) hΓ
  refine ⟨D (), ?_, hPositive (), hBound (), hInt (), ?_⟩
  · exact hStrong.comp_measurable
      ((measurable_const : Measurable (fun _ : Ω => ())).prodMk measurable_id)
  · exact hSet ()

section PhysicalNormalResponse

open QuantumProver.ElegantJointMeasurement.NormalRecordedAbsorption QuantumProver.ElegantJointMeasurement.NormalInstrumentAbsorption
open QuantumProver.ElegantJointMeasurement.SeparableHilbertEmbedding QuantumProver.ElegantJointMeasurement.HilbertRecordedHilbertInstrument

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {H : Type*} [MeasurableSpace H]
variable {J : Type} [Fintype J] [DecidableEq J] [Nonempty J]

theorem normalFiniteTest_eq_zero_of_re_trace_eq_zero
    (P : QuantumProver.ElegantJointMeasurement.NormalInstrumentAbsorption.Instrument E CommonHilbert H Ω)
    (h : H) (U : Nuclear (BlockSpace J E)) (hU : (toOperator U).IsPositive)
    (hTrace : (QuantumProver.HilbertNuclearTrace.trace U).re = 0)
    (W : Ω → RecordedSpace J →L[ℂ] RecordedSpace J) :
    QuantumProver.ElegantJointMeasurement.HilbertControlledNuclearTest.rawFiniteTest (commonBlockBasis (I := J))
      (fun v => normalProbe P h U hU v) W = fun _ : ℕ => (0 : ℂ) := by
  have hZero : U = 0 :=
    QuantumProver.ElegantJointMeasurement.NuclearProjectionSupport.positive_nuclear_eq_zero_of_re_trace_eq_zero U hU hTrace
  have hProbe (v : RecordedSpace J) : normalProbe P h U hU v = 0 := by
    apply Measure.ext
    intro s hs
    rw [normalProbe_apply P h U hU v s hs]
    simp [normalResponse, hZero]
  funext n
  simp [QuantumProver.ElegantJointMeasurement.HilbertControlledNuclearTest.rawFiniteTest,
    QuantumProver.ElegantJointMeasurement.HilbertControlledNuclearTest.rawPairTest, hProbe]

theorem exists_normalResponse_nuclear_density_of_pos_trace
    (P : QuantumProver.ElegantJointMeasurement.NormalInstrumentAbsorption.Instrument E CommonHilbert H Ω)
    (h : H) (U : Nuclear (BlockSpace J E)) (hU : (toOperator U).IsPositive)
    (hTrace : 0 < (QuantumProver.HilbertNuclearTrace.trace U).re) :
    ∃ D : Ω → Nuclear (RecordedSpace J),
      StronglyMeasurable D ∧
      (∀ ω, (toOperator (D ω)).IsPositive) ∧
      (∀ ω, ‖D ω‖ ≤ (QuantumProver.HilbertNuclearTrace.trace U).re) ∧
      Integrable D (responseProbabilityMeasure (commonBlockBasis (I := J))
        (fun v => normalProbe P h U hU v) (QuantumProver.HilbertNuclearTrace.trace U).re) ∧
      (∀ s, MeasurableSet s →
        (∫ ω in s, D ω ∂responseProbabilityMeasure (commonBlockBasis (I := J))
          (fun v => normalProbe P h U hU v) (QuantumProver.HilbertNuclearTrace.trace U).re) =
          normalResponse P h U s) := by
  apply exists_positive_response_nuclear_density (commonBlockBasis (I := J))
    (normalResponse P h U) (fun v => normalProbe P h U hU v)
    (normalResponse_isPositive P h U hU)
    (normalProbe_apply P h U hU) (QuantumProver.HilbertNuclearTrace.trace U).re hTrace
  exact congrArg Complex.re (normalResponse_trace_univ P h U)

theorem normalFiniteTest_tendsto_normalRecordedExpectation
    (P : QuantumProver.ElegantJointMeasurement.NormalInstrumentAbsorption.Instrument E CommonHilbert H Ω)
    (h : H) (U : Nuclear (BlockSpace J E)) (hU : (toOperator U).IsPositive)
    (W : Ω → RecordedSpace J →L[ℂ] RecordedSpace J) (hW : IsRecordedObservable W) :
    Tendsto (QuantumProver.ElegantJointMeasurement.HilbertControlledNuclearTest.rawFiniteTest (commonBlockBasis (I := J))
      (fun v => normalProbe P h U hU v) W) atTop
      (𝓝 (normalRecordedExpectation P h U hU W)) := by
  by_cases hz : (QuantumProver.HilbertNuclearTrace.trace U).re = 0
  · have hTest := normalFiniteTest_eq_zero_of_re_trace_eq_zero P h U hU hz W
    have ht : Tendsto (QuantumProver.ElegantJointMeasurement.HilbertControlledNuclearTest.rawFiniteTest (commonBlockBasis (I := J))
        (fun v => normalProbe P h U hU v) W) atTop (𝓝 (0 : ℂ)) := by
      rw [hTest]
      exact tendsto_const_nhds
    exact tendsto_nhds_limUnder ⟨_, ht⟩
  · have hd : 0 < (QuantumProver.HilbertNuclearTrace.trace U).re :=
      lt_of_le_of_ne (QuantumProver.ElegantJointMeasurement.NuclearProjectionSupport.positive_nuclear_re_trace_nonneg U hU)
        (Ne.symm hz)
    obtain ⟨D, hStrong, hPos, hBound, hInt, hSet⟩ :=
      exists_normalResponse_nuclear_density_of_pos_trace P h U hU hd
    have hProbe (v : RecordedSpace J) (s : Set Ω) (hs : MeasurableSet s) :
        (normalProbe P h U hU v s).toReal =
          (inner ℂ v (toOperator (normalResponse P h U s) v)).re := by
      rw [normalProbe_apply P h U hU v s hs]
      exact ENNReal.toReal_ofReal
        ((normalResponse_isPositive P h U hU s hs).re_inner_nonneg_right v)
    obtain ⟨hStrongW, C, hC, hNormW⟩ := hW
    have ht := QuantumProver.ElegantJointMeasurement.HilbertControlledNuclearTest.rawFiniteTest_tendsto_densityTest
      (commonBlockBasis (I := J)) (normalResponse P h U) (fun v => normalProbe P h U hU v)
      D hInt (ae_of_all _ hPos) hSet hProbe W hStrongW hC hNormW
    exact tendsto_nhds_limUnder ⟨_, ht⟩

end PhysicalNormalResponse

end QuantumProver.ElegantJointMeasurement.NormalRecordedConvergence

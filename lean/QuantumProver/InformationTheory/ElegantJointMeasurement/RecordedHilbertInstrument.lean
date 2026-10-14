import QuantumProver.InformationTheory.ElegantJointMeasurement.MeasurableNormalInstrument
import QuantumProver.InformationTheory.ElegantJointMeasurement.ControlledNuclearTest
import QuantumProver.InformationTheory.ElegantJointMeasurement.NuclearFieldSupport

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory Filter Set
open scoped BigOperators Topology ComplexOrder InnerProductSpace

namespace QuantumProver.ElegantJointMeasurement.HilbertRecordedHilbertInstrument

open QuantumProver.ElegantJointMeasurement.HilbertChoi QuantumProver.ElegantJointMeasurement.SeparableHilbertEmbedding
open QuantumProver.ElegantJointMeasurement.MeasurableHilbertField

universe u v w
variable {I : Type} [Fintype I] [DecidableEq I]
  {H : Type u} {Ω : Type v} [MeasurableSpace H] [MeasurableSpace Ω]
  {G : H × Ω → Type w}
  [∀ z, NormedAddCommGroup (G z)] [∀ z, InnerProductSpace ℂ (G z)]
  [∀ z, CompleteSpace (G z)]

def hilbertSqrt {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [CompleteSpace V] (D : V →L[ℂ] V) : V →L[ℂ] V := CFC.sqrt D

abbrev RecordedSpace (I : Type) [Fintype I] := BlockSpace I CommonHilbert

local instance recordedSpaceNormedGroup : NormedAddCommGroup (RecordedSpace I) := inferInstance
local instance recordedSpaceInnerProduct : InnerProductSpace ℂ (RecordedSpace I) := inferInstance
local instance recordedSpaceComplete : CompleteSpace (RecordedSpace I) := inferInstance
local instance recordedOperatorCStar : CStarAlgebra (RecordedSpace I →L[ℂ] RecordedSpace I) :=
  inferInstance

def outputProjection (F : FundamentalFamily G) (h : H) (ω : Ω) :
    RecordedSpace I →L[ℂ] RecordedSpace I :=
  blockLift (R := I) (F.rangeProjection (h, ω))

@[simp] theorem outputProjection_apply_coordinate (F : FundamentalFamily G)
    (h : H) (ω : Ω) (x : RecordedSpace I) (i : I) :
    outputProjection F h ω x i = F.rangeProjection (h, ω) (x i) := rfl

theorem outputProjection_adjoint (F : FundamentalFamily G) (h : H) (ω : Ω) :
    (outputProjection (I := I) F h ω).adjoint = outputProjection F h ω := by
  rw [outputProjection, blockLift_adjoint,
    QuantumProver.ElegantJointMeasurement.MeasurableNormalInstrument.inputProjection_adjoint]

theorem outputProjection_idempotent (F : FundamentalFamily G) (h : H) (ω : Ω) :
    (outputProjection (I := I) F h ω).comp (outputProjection F h ω) =
      outputProjection F h ω := by
  apply ContinuousLinearMap.ext
  intro x
  apply PiLp.ext
  intro i
  change F.rangeProjection (h, ω) (F.rangeProjection (h, ω) (x i)) =
    F.rangeProjection (h, ω) (x i)
  exact congrArg (fun L : CommonHilbert →L[ℂ] CommonHilbert => L (x i))
    (QuantumProver.ElegantJointMeasurement.MeasurableNormalInstrument.inputProjection_idempotent F (h, ω))

def outputComplement (F : FundamentalFamily G) (h : H) (ω : Ω) :
    RecordedSpace I →L[ℂ] RecordedSpace I :=
  ContinuousLinearMap.id ℂ (RecordedSpace I) - outputProjection F h ω

theorem outputComplement_adjoint (F : FundamentalFamily G) (h : H) (ω : Ω) :
    (outputComplement (I := I) F h ω).adjoint = outputComplement F h ω := by
  simp only [outputComplement, map_sub,
    ContinuousLinearMap.adjoint_id, outputProjection_adjoint]

theorem outputComplement_idempotent (F : FundamentalFamily G) (h : H) (ω : Ω) :
    (outputComplement (I := I) F h ω).comp (outputComplement F h ω) =
      outputComplement F h ω := by
  apply ContinuousLinearMap.ext
  intro x
  have hp := congrArg (fun L : RecordedSpace I →L[ℂ] RecordedSpace I => L x)
    (outputProjection_idempotent F h ω)
  simp only [ContinuousLinearMap.comp_apply] at hp
  simp only [outputComplement, ContinuousLinearMap.comp_apply,
    sub_apply, ContinuousLinearMap.id_apply, map_sub]
  rw [hp]
  abel

private theorem norm_projection_le_one {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [CompleteSpace V] (P : V →L[ℂ] V)
    (hAdj : P.adjoint = P) (hId : P.comp P = P) : ‖P‖ ≤ 1 := by
  have hSelf : IsSelfAdjoint P := by
    simpa only [IsSelfAdjoint, ContinuousLinearMap.star_eq_adjoint] using hAdj
  have hn := hSelf.norm_mul_self
  change ‖P.comp P‖ = ‖P‖ ^ 2 at hn
  rw [hId] at hn
  by_contra h
  have hlt : 1 < ‖P‖ := lt_of_not_ge h
  have hprod : 0 < ‖P‖ * (‖P‖ - 1) :=
    mul_pos (zero_lt_one.trans hlt) (sub_pos.mpr hlt)
  nlinarith

theorem norm_outputProjection_le_one (F : FundamentalFamily G) (h : H) (ω : Ω) :
    ‖outputProjection (I := I) F h ω‖ ≤ 1 :=
  norm_projection_le_one _ (outputProjection_adjoint F h ω)
    (outputProjection_idempotent F h ω)

theorem norm_outputComplement_le_one (F : FundamentalFamily G) (h : H) (ω : Ω) :
    ‖outputComplement (I := I) F h ω‖ ≤ 1 :=
  norm_projection_le_one _ (outputComplement_adjoint F h ω)
    (outputComplement_idempotent F h ω)

theorem stronglyMeasurable_outputProjection_apply (F : FundamentalFamily G)
    (h : H) (x : RecordedSpace I) :
    StronglyMeasurable (fun ω => outputProjection F h ω x) := by
  have hm : StronglyMeasurable (fun ω => ∑ i : I,
      insert i (F.rangeProjection (h, ω) (x i))) := by
    apply Finset.stronglyMeasurable_fun_sum
    intro i hi
    have hv := (F.stronglyMeasurable_rangeProjection_apply
      (fun _ : H × Ω => x i) stronglyMeasurable_const).comp_measurable
        ((measurable_const : Measurable (fun _ : Ω => h)).prodMk measurable_id)
    exact (QuantumProver.ElegantJointMeasurement.HilbertChoi.insert (E := CommonHilbert) i).continuous.comp_stronglyMeasurable hv
  have heq : (fun ω => ∑ i : I, insert i (F.rangeProjection (h, ω) (x i))) =
      (fun ω => outputProjection F h ω x) := by
    funext ω
    apply PiLp.ext
    intro i
    simp only [WithLp.ofLp_sum, Finset.sum_apply, insert_apply_apply,
      outputProjection_apply_coordinate]
    simp
  rw [heq] at hm
  exact hm

theorem stronglyMeasurable_outputProjection_variable_apply (F : FundamentalFamily G)
    (h : H) (x : Ω → RecordedSpace I) (hx : StronglyMeasurable x) :
    StronglyMeasurable (fun ω => outputProjection F h ω (x ω)) :=
  QuantumProver.ElegantJointMeasurement.NormalInstrumentAbsorption.stronglyMeasurable_variable_apply _
    (stronglyMeasurable_outputProjection_apply F h) x hx

theorem stronglyMeasurable_outputComplement_apply (F : FundamentalFamily G)
    (h : H) (x : RecordedSpace I) :
    StronglyMeasurable (fun ω => outputComplement F h ω x) := by
  have hm := (stronglyMeasurable_const : StronglyMeasurable (fun _ : Ω => x)).sub
    (stronglyMeasurable_outputProjection_apply F h x)
  have heq : ((fun _ : Ω => x) - fun ω => outputProjection F h ω x) =
      (fun ω => outputComplement F h ω x) := by
    funext ω
    rfl
  rw [heq] at hm
  exact hm

def IsRecordedObservable (W : Ω → RecordedSpace I →L[ℂ] RecordedSpace I) : Prop :=
  (∀ x, StronglyMeasurable (fun ω => W ω x)) ∧
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ω, ‖W ω‖ ≤ C

theorem outputProjection_isRecordedObservable (F : FundamentalFamily G) (h : H) :
    IsRecordedObservable (outputProjection (I := I) F h) :=
  ⟨stronglyMeasurable_outputProjection_apply F h,
    1, zero_le_one, norm_outputProjection_le_one F h⟩

theorem outputComplement_isRecordedObservable (F : FundamentalFamily G) (h : H) :
    IsRecordedObservable (outputComplement (I := I) F h) :=
  ⟨stronglyMeasurable_outputComplement_apply F h,
    1, zero_le_one, norm_outputComplement_le_one F h⟩

def controlledObservable (F : FundamentalFamily G) (h : H)
    (W : Ω → RecordedSpace I →L[ℂ] RecordedSpace I) :
    Ω → RecordedSpace I →L[ℂ] RecordedSpace I :=
  fun ω => (outputProjection F h ω).comp ((W ω).comp (outputProjection F h ω))

theorem controlledObservable_isRecordedObservable (F : FundamentalFamily G) (h : H)
    (W : Ω → RecordedSpace I →L[ℂ] RecordedSpace I) (hW : IsRecordedObservable W) :
    IsRecordedObservable (controlledObservable F h W) := by
  obtain ⟨hstrong, C, hC, hbound⟩ := hW
  constructor
  · intro x
    have hp := stronglyMeasurable_outputProjection_apply F h x
    have hw := QuantumProver.ElegantJointMeasurement.NormalInstrumentAbsorption.stronglyMeasurable_variable_apply
      W hstrong _ hp
    exact stronglyMeasurable_outputProjection_variable_apply F h _ hw
  · refine ⟨C, hC, fun ω => ?_⟩
    have hp := norm_outputProjection_le_one (I := I) F h ω
    have hinner : ‖(W ω).comp (outputProjection (I := I) F h ω)‖ ≤ C := by
      calc
        _ ≤ ‖W ω‖ * ‖outputProjection (I := I) F h ω‖ := ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ C * 1 := mul_le_mul (hbound ω) hp (norm_nonneg _) hC
        _ = C := mul_one C
    calc
      _ ≤ ‖outputProjection (I := I) F h ω‖ * ‖(W ω).comp (outputProjection (I := I) F h ω)‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * C := mul_le_mul hp hinner (norm_nonneg _) zero_le_one
      _ = C := one_mul C

theorem controlledObservable_complement_eq_zero (F : FundamentalFamily G) (h : H) :
    controlledObservable F h (outputComplement (I := I) F h) = fun _ => 0 := by
  funext ω
  apply ContinuousLinearMap.ext
  intro x
  have hp := congrArg (fun L : RecordedSpace I →L[ℂ] RecordedSpace I => L x)
    (outputProjection_idempotent F h ω)
  simp only [ContinuousLinearMap.comp_apply] at hp
  simp only [controlledObservable, ContinuousLinearMap.comp_apply,
    outputComplement, sub_apply, ContinuousLinearMap.id_apply, zero_apply]
  rw [hp, sub_self, map_zero]

theorem stronglyMeasurable_joint_outputProjection_apply (F : FundamentalFamily G)
    (x : RecordedSpace I) :
    StronglyMeasurable (fun z : H × Ω => outputProjection F z.1 z.2 x) := by
  have hm : StronglyMeasurable (fun z : H × Ω => ∑ i : I,
      QuantumProver.ElegantJointMeasurement.HilbertChoi.insert i (F.rangeProjection z (x i))) := by
    apply Finset.stronglyMeasurable_fun_sum
    intro i hi
    exact (QuantumProver.ElegantJointMeasurement.HilbertChoi.insert (E := CommonHilbert) i).continuous.comp_stronglyMeasurable
      (F.stronglyMeasurable_rangeProjection_apply (fun _ => x i) stronglyMeasurable_const)
  have heq : (fun z : H × Ω => ∑ i : I,
      QuantumProver.ElegantJointMeasurement.HilbertChoi.insert i (F.rangeProjection z (x i))) =
      (fun z => outputProjection F z.1 z.2 x) := by
    funext z
    apply PiLp.ext
    intro i
    simp only [WithLp.ofLp_sum, Finset.sum_apply, insert_apply_apply,
      outputProjection_apply_coordinate]
    simp
  rw [heq] at hm
  exact hm

theorem unvectorize_supported_of_outputProjection (F : FundamentalFamily G)
    (h : H) (ω : Ω) (v : RecordedSpace I)
    (hv : outputProjection F h ω v = v) :
    (F.rangeProjection (h, ω)).comp (unvectorize v) = unvectorize v := by
  have hcoord (i : I) : F.rangeProjection (h, ω) (v i) = v i :=
    congrArg (fun y : RecordedSpace I => y i) hv
  apply ContinuousLinearMap.ext
  intro x
  simp only [ContinuousLinearMap.comp_apply, unvectorize_apply, map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [hcoord]

theorem krausColumn_supported_of_sqrt_projection (F : FundamentalFamily G)
    (h : H) (ω : Ω)
    (D : QuantumProver.NuclearOperator.Nuclear ℂ (RecordedSpace I) (RecordedSpace I))
    (b : HilbertBasis ℕ ℂ (RecordedSpace I))
    (hD : (outputProjection F h ω).comp (hilbertSqrt (QuantumProver.NuclearOperator.toOperator D)) =
      hilbertSqrt (QuantumProver.NuclearOperator.toOperator D)) (l : ℕ) :
    (F.rangeProjection (h, ω)).comp
      (unvectorize (squareRootColumn b (QuantumProver.NuclearOperator.toOperator D) l)) =
      unvectorize (squareRootColumn b (QuantumProver.NuclearOperator.toOperator D) l) := by
  apply unvectorize_supported_of_outputProjection F h ω
  exact congrArg (fun L : RecordedSpace I →L[ℂ] RecordedSpace I => L (b l)) hD

section PhysicalRecordedInstrument

variable [Nonempty I]

abbrev PhysicalInstrument := QuantumProver.ElegantJointMeasurement.NormalCPInstruments.Instrument I CommonHilbert H Ω
abbrev RecordedNuclear := QuantumProver.NuclearOperator.Nuclear ℂ (RecordedSpace I) (RecordedSpace I)

def recordedExpectation (P : PhysicalInstrument (I := I) (H := H) (Ω := Ω))
    (h : H) (W : Ω → RecordedSpace I →L[ℂ] RecordedSpace I) : ℂ :=
  limUnder atTop (QuantumProver.ElegantJointMeasurement.HilbertControlledNuclearTest.rawFiniteTest (commonBlockBasis (I := I))
    (fun v => QuantumProver.ElegantJointMeasurement.NormalChoiKernels.Instrument.physicalProbe P v h) W)

theorem recordedExpectation_zero (P : PhysicalInstrument (I := I) (H := H) (Ω := Ω))
    (h : H) : recordedExpectation P h (fun _ => 0) = 0 := by
  have ht : Tendsto (QuantumProver.ElegantJointMeasurement.HilbertControlledNuclearTest.rawFiniteTest (commonBlockBasis (I := I))
      (fun v => QuantumProver.ElegantJointMeasurement.NormalChoiKernels.Instrument.physicalProbe P v h) (fun _ => 0))
      atTop (𝓝 (0 : ℂ)) := by
    have heq : QuantumProver.ElegantJointMeasurement.HilbertControlledNuclearTest.rawFiniteTest (commonBlockBasis (I := I))
        (fun v => QuantumProver.ElegantJointMeasurement.NormalChoiKernels.Instrument.physicalProbe P v h) (fun _ => 0) =
          (fun _ : ℕ => (0 : ℂ)) := by
      funext n
      simp [QuantumProver.ElegantJointMeasurement.HilbertControlledNuclearTest.rawFiniteTest,
        QuantumProver.ElegantJointMeasurement.HilbertControlledNuclearTest.rawPairTest]
    rw [heq]
    exact tendsto_const_nhds
  exact ht.limUnder_eq

structure RecordedInstrument (F : FundamentalFamily G) where
  represented_physical : PhysicalInstrument (I := I) (H := H) (Ω := Ω)
  controlled_output : ∀ (h : H) (W : Ω → RecordedSpace I →L[ℂ] RecordedSpace I),
    IsRecordedObservable W → recordedExpectation represented_physical h W =
      recordedExpectation represented_physical h (controlledObservable F h W)

variable [MeasurableSpace.CountableOrCountablyGenerated H Ω]

theorem physical_recorded_response_converges
    (P : PhysicalInstrument (I := I) (H := H) (Ω := Ω)) (h : H)
    (W : Ω → RecordedSpace I →L[ℂ] RecordedSpace I) (hW : IsRecordedObservable W) :
    Tendsto (QuantumProver.ElegantJointMeasurement.HilbertControlledNuclearTest.rawFiniteTest (commonBlockBasis (I := I))
      (fun v => QuantumProver.ElegantJointMeasurement.NormalChoiKernels.Instrument.physicalProbe P v h) W)
      atTop (𝓝 (recordedExpectation P h W)) := by
  obtain ⟨D, hInt, hPos, hSet, hTests⟩ :=
    QuantumProver.ElegantJointMeasurement.HilbertControlledNuclearTest.exists_physical_density_controlled_test P
      (commonBlockBasis (I := I)) h
  obtain ⟨hStrong, C, hC, hBound⟩ := hW
  exact tendsto_nhds_limUnder ⟨_, hTests W hStrong C hC hBound⟩

theorem physical_complement_response_eq_zero {F : FundamentalFamily G}
    (P : RecordedInstrument (I := I) F) (h : H) :
    recordedExpectation P.represented_physical h (outputComplement (I := I) F h) = 0 := by
  have heq := P.controlled_output h (outputComplement F h)
    (outputComplement_isRecordedObservable F h)
  rw [controlledObservable_complement_eq_zero, recordedExpectation_zero] at heq
  exact heq

theorem physical_complement_response_tendsto_zero {F : FundamentalFamily G}
    (P : RecordedInstrument (I := I) F) (h : H) :
    Tendsto (QuantumProver.ElegantJointMeasurement.HilbertControlledNuclearTest.rawFiniteTest (commonBlockBasis (I := I))
      (fun v => QuantumProver.ElegantJointMeasurement.NormalChoiKernels.Instrument.physicalProbe P.represented_physical v h)
      (outputComplement F h)) atTop (𝓝 0) := by
  have ht := physical_recorded_response_converges P.represented_physical h (outputComplement F h)
    (outputComplement_isRecordedObservable F h)
  rw [physical_complement_response_eq_zero P h] at ht
  exact ht

theorem physical_controlled_complement_integral_eq_zero {F : FundamentalFamily G}
    (P : RecordedInstrument (I := I) F) (h : H) (D : Ω → RecordedNuclear (I := I))
    (hInt : Integrable D (P.represented_physical.referenceKernel h))
    (hPos : ∀ᵐ ω ∂P.represented_physical.referenceKernel h,
      (QuantumProver.NuclearOperator.toOperator (D ω)).IsPositive)
    (hSet : ∀ s : Set Ω, MeasurableSet s →
      (∫ ω in s, D ω ∂P.represented_physical.referenceKernel h) = P.represented_physical.physicalChoi h s) :
    (∫ ω, QuantumProver.ElegantJointMeasurement.NuclearFieldSupport.complementTrace (outputProjection F h ω) (D ω)
      ∂P.represented_physical.referenceKernel h) = 0 := by
  haveI : ∀ v : RecordedSpace I,
      IsFiniteMeasure (QuantumProver.ElegantJointMeasurement.NormalChoiKernels.Instrument.physicalProbe P.represented_physical v h) :=
    fun v => QuantumProver.ElegantJointMeasurement.HilbertControlledNuclearTest.physicalProbe_isFinite P.represented_physical v h
  have hProbe (v : RecordedSpace I) (s : Set Ω) (hs : MeasurableSet s) :
      (QuantumProver.ElegantJointMeasurement.NormalChoiKernels.Instrument.physicalProbe P.represented_physical v h s).toReal =
        (inner ℂ v (QuantumProver.NuclearOperator.toOperator (P.represented_physical.physicalChoi h s) v)).re := by
    rw [QuantumProver.ElegantJointMeasurement.NormalChoiKernels.Instrument.physicalProbe_apply P.represented_physical v h s hs]
    have hp : 0 ≤
        (inner ℂ v (QuantumProver.NuclearOperator.toOperator (P.represented_physical.physicalChoi h s) v)).re :=
      (P.represented_physical.physicalChoi_isPositive h s hs).re_inner_nonneg_right v
    exact ENNReal.toReal_ofReal hp
  have hz := QuantumProver.ElegantJointMeasurement.HilbertControlledNuclearTest.complement_integral_eq_zero_of_raw_response_zero
    (commonBlockBasis (I := I)) (P.represented_physical.physicalChoi h)
    (fun v => QuantumProver.ElegantJointMeasurement.NormalChoiKernels.Instrument.physicalProbe P.represented_physical v h)
    D hInt hPos hSet hProbe (outputProjection F h)
    (stronglyMeasurable_outputProjection_apply F h) (outputProjection_idempotent F h)
    zero_le_one (norm_outputComplement_le_one F h)
    (physical_complement_response_tendsto_zero P h)
  exact hz

local instance recordedNuclearMeasurable : MeasurableSpace (RecordedNuclear (I := I)) :=
  borel (RecordedNuclear (I := I))
local instance recordedNuclearBorel : BorelSpace (RecordedNuclear (I := I)) := ⟨rfl⟩

theorem exists_physical_controlled_nuclear_density {F : FundamentalFamily G}
    (P : RecordedInstrument (I := I) F) :
    ∃ D : H → Ω → RecordedNuclear (I := I),
      StronglyMeasurable (fun z : H × Ω => D z.1 z.2) ∧
      (∀ h ω, (QuantumProver.NuclearOperator.toOperator (D h ω)).IsPositive) ∧
      (∀ h, Integrable (D h) (P.represented_physical.referenceKernel h)) ∧
      (∀ h (s : Set Ω), MeasurableSet s →
        (∫ ω in s, D h ω ∂P.represented_physical.referenceKernel h) = P.represented_physical.physicalChoi h s) ∧
      (∀ h, ∀ᵐ ω ∂P.represented_physical.referenceKernel h,
        QuantumProver.HilbertNuclearCompression.compose (outputProjection F h ω)
          (outputProjection F h ω) (D h ω) = D h ω ∧
        (outputProjection F h ω).comp (hilbertSqrt (QuantumProver.NuclearOperator.toOperator (D h ω))) =
          hilbertSqrt (QuantumProver.NuclearOperator.toOperator (D h ω)) ∧
        ∀ l : ℕ, (F.rangeProjection (h, ω)).comp
          (unvectorize (squareRootColumn (commonBlockBasis (I := I))
            (QuantumProver.NuclearOperator.toOperator (D h ω)) l)) =
          unvectorize (squareRootColumn (commonBlockBasis (I := I))
            (QuantumProver.NuclearOperator.toOperator (D h ω)) l)) := by
  obtain ⟨D, hStrong, hMeas, hPos, hTrace, hBound, hMass, hInt, hSet⟩ :=
    QuantumProver.ElegantJointMeasurement.NormalNuclearDensity.exists_physical_positive_nuclear_density P.represented_physical
      (commonBlockBasis (I := I))
  refine ⟨D, hStrong, hPos, hInt, hSet, ?_⟩
  intro h
  have hJoint : StronglyMeasurable (D h) := hStrong.comp_measurable
    ((measurable_const : Measurable (fun _ : Ω => h)).prodMk measurable_id)
  have hZero := physical_controlled_complement_integral_eq_zero P h (D h)
    (hInt h) (ae_of_all _ (hPos h)) (hSet h)
  have hSupport :=
    QuantumProver.ElegantJointMeasurement.NuclearFieldSupport.ae_projection_sandwich_eq_of_integral_complementTrace_eq_zero
      (P.represented_physical.referenceKernel h) (outputProjection F h)
      (outputProjection_adjoint F h) (outputProjection_idempotent F h)
      (stronglyMeasurable_outputProjection_apply F h) (D h) hJoint (hInt h)
      (ae_of_all _ (hPos h)) hZero
  have hSqrt :=
    QuantumProver.ElegantJointMeasurement.NuclearFieldSupport.ae_projection_sqrt_eq_of_integral_complementTrace_eq_zero
      (P.represented_physical.referenceKernel h) (outputProjection F h)
      (outputProjection_adjoint F h) (outputProjection_idempotent F h)
      (stronglyMeasurable_outputProjection_apply F h) (D h) hJoint (hInt h)
      (ae_of_all _ (hPos h)) hZero
  filter_upwards [hSupport, hSqrt] with ω hs hq
  exact ⟨hs, hq, fun l => krausColumn_supported_of_sqrt_projection F h ω (D h ω)
    (commonBlockBasis (I := I)) hq l⟩

def physicalDensity (F : FundamentalFamily G)
    (D : H → Ω → RecordedNuclear (I := I)) (h : H) (ω : Ω) : RecordedNuclear (I := I) :=
  QuantumProver.HilbertNuclearCompression.compose (outputProjection F h ω)
    (outputProjection F h ω) (D h ω)

theorem stronglyMeasurable_physicalDensity (F : FundamentalFamily G)
    (D : H → Ω → RecordedNuclear (I := I))
    (hD : StronglyMeasurable (fun z : H × Ω => D z.1 z.2)) :
    StronglyMeasurable (fun z : H × Ω => physicalDensity F D z.1 z.2) := by
  exact QuantumProver.ElegantJointMeasurement.NuclearFieldSupport.stronglyMeasurable_sandwich_variable
    (fun z : H × Ω => outputProjection F z.1 z.2)
    (fun z => outputProjection_adjoint F z.1 z.2)
    (stronglyMeasurable_joint_outputProjection_apply F)
    (fun z : H × Ω => D z.1 z.2) hD

theorem physicalDensity_isPositive (F : FundamentalFamily G)
    (D : H → Ω → RecordedNuclear (I := I))
    (hD : ∀ h ω, (QuantumProver.NuclearOperator.toOperator (D h ω)).IsPositive) (h : H) (ω : Ω) :
    (QuantumProver.NuclearOperator.toOperator (physicalDensity F D h ω)).IsPositive := by
  exact QuantumProver.ElegantJointMeasurement.NuclearProjectionSupport.nuclear_sandwich_isPositive
    (D h ω) (outputProjection F h ω) (hD h ω) (outputProjection_adjoint F h ω)

theorem norm_physicalDensity_le (F : FundamentalFamily G)
    (D : H → Ω → RecordedNuclear (I := I)) (h : H) (ω : Ω) :
    ‖physicalDensity F D h ω‖ ≤ ‖D h ω‖ := by
  have hp := norm_outputProjection_le_one (I := I) F h ω
  have hpp : ‖outputProjection (I := I) F h ω‖ * ‖outputProjection (I := I) F h ω‖ ≤ 1 :=
    mul_le_one₀ hp (norm_nonneg _) hp
  exact (QuantumProver.HilbertNuclearCompression.norm_compose_apply_le
    (outputProjection F h ω) (outputProjection F h ω) (D h ω)).trans
      (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hpp (norm_nonneg (D h ω)))

theorem physicalDensity_supported (F : FundamentalFamily G)
    (D : H → Ω → RecordedNuclear (I := I)) (h : H) (ω : Ω) :
    QuantumProver.HilbertNuclearCompression.compose (outputProjection F h ω)
      (outputProjection F h ω) (physicalDensity F D h ω) = physicalDensity F D h ω := by
  have hp (x : RecordedSpace I) :
      outputProjection F h ω (outputProjection F h ω x) = outputProjection F h ω x :=
    congrArg (fun L : RecordedSpace I →L[ℂ] RecordedSpace I => L x)
      (outputProjection_idempotent F h ω)
  apply QuantumProver.NuclearOperator.toOperator_injective
  ext x
  simp only [physicalDensity, QuantumProver.HilbertNuclearCompression.toOperator_compose,
    ContinuousLinearMap.comp_apply, hp]

theorem physicalDensity_sqrt_supported (F : FundamentalFamily G)
    (D : H → Ω → RecordedNuclear (I := I))
    (hD : ∀ h ω, (QuantumProver.NuclearOperator.toOperator (D h ω)).IsPositive) (h : H) (ω : Ω) :
    (outputProjection F h ω).comp
        (hilbertSqrt (QuantumProver.NuclearOperator.toOperator (physicalDensity F D h ω))) =
      hilbertSqrt (QuantumProver.NuclearOperator.toOperator (physicalDensity F D h ω)) := by
  apply QuantumProver.ElegantJointMeasurement.NuclearProjectionSupport.projection_sqrt_eq_of_re_trace_eq
    (physicalDensity F D h ω) (outputProjection F h ω)
    (physicalDensity_isPositive F D hD h ω) (outputProjection_adjoint F h ω)
    (outputProjection_idempotent F h ω)
  rw [physicalDensity_supported]

theorem exists_physical_pointwise_supported_nuclear_density {F : FundamentalFamily G}
    (P : RecordedInstrument (I := I) F) :
    ∃ D : H → Ω → RecordedNuclear (I := I),
      StronglyMeasurable (fun z : H × Ω => D z.1 z.2) ∧
      Measurable (fun z : H × Ω => D z.1 z.2) ∧
      (∀ h ω, (QuantumProver.NuclearOperator.toOperator (D h ω)).IsPositive) ∧
      (∀ h ω, (QuantumProver.HilbertNuclearTrace.trace (D h ω)).re = ‖D h ω‖) ∧
      (∀ h ω, ‖D h ω‖ ≤ (Fintype.card I : ℝ)) ∧
      (∀ h, ∀ᵐ ω ∂P.represented_physical.referenceKernel h, ‖D h ω‖ = (Fintype.card I : ℝ)) ∧
      (∀ h, Integrable (D h) (P.represented_physical.referenceKernel h)) ∧
      (∀ h (s : Set Ω), MeasurableSet s →
        (∫ ω in s, D h ω ∂P.represented_physical.referenceKernel h) = P.represented_physical.physicalChoi h s) ∧
      (∀ h ω, QuantumProver.HilbertNuclearCompression.compose (outputProjection F h ω)
        (outputProjection F h ω) (D h ω) = D h ω) ∧
      (∀ h ω, (outputProjection F h ω).comp (hilbertSqrt (QuantumProver.NuclearOperator.toOperator (D h ω))) =
        hilbertSqrt (QuantumProver.NuclearOperator.toOperator (D h ω))) ∧
      (∀ h ω l, (F.rangeProjection (h, ω)).comp
        (unvectorize (squareRootColumn (commonBlockBasis (I := I))
          (QuantumProver.NuclearOperator.toOperator (D h ω)) l)) =
        unvectorize (squareRootColumn (commonBlockBasis (I := I))
          (QuantumProver.NuclearOperator.toOperator (D h ω)) l)) := by
  obtain ⟨D, hStrong, hMeas, hPos, hTrace, hBound, hMass, hInt, hSet⟩ :=
    QuantumProver.ElegantJointMeasurement.NormalNuclearDensity.exists_physical_positive_nuclear_density P.represented_physical
      (commonBlockBasis (I := I))
  have hAE (h : H) : physicalDensity F D h =ᵐ[P.represented_physical.referenceKernel h] D h := by
    have hJoint : StronglyMeasurable (D h) := hStrong.comp_measurable
      ((measurable_const : Measurable (fun _ : Ω => h)).prodMk measurable_id)
    exact QuantumProver.ElegantJointMeasurement.NuclearFieldSupport.ae_projection_sandwich_eq_of_integral_complementTrace_eq_zero
      (P.represented_physical.referenceKernel h) (outputProjection F h)
      (outputProjection_adjoint F h) (outputProjection_idempotent F h)
      (stronglyMeasurable_outputProjection_apply F h) (D h) hJoint (hInt h)
      (ae_of_all _ (hPos h))
      (physical_controlled_complement_integral_eq_zero P h (D h)
        (hInt h) (ae_of_all _ (hPos h)) (hSet h))
  have hPhysStrong := stronglyMeasurable_physicalDensity F D hStrong
  refine ⟨physicalDensity F D, hPhysStrong, hPhysStrong.measurable,
    physicalDensity_isPositive F D hPos, ?_, ?_, ?_, ?_, ?_,
    physicalDensity_supported F D, physicalDensity_sqrt_supported F D hPos, ?_⟩
  · intro h ω
    exact (QuantumProver.ElegantJointMeasurement.NuclearChoi.norm_positive_nuclear_eq_re_trace
      (commonBlockBasis (I := I)) (physicalDensity F D h ω)
      (physicalDensity_isPositive F D hPos h ω)).symm
  · intro h ω
    exact (norm_physicalDensity_le F D h ω).trans (hBound h ω)
  · intro h
    filter_upwards [hAE h, hMass h] with ω heq hm
    rw [heq]
    exact hm
  · intro h
    exact (hInt h).congr (hAE h).symm
  · intro h s hs
    rw [integral_congr_ae (ae_restrict_of_ae (hAE h))]
    exact hSet h s hs
  · intro h ω l
    exact krausColumn_supported_of_sqrt_projection F h ω (physicalDensity F D h ω)
      (commonBlockBasis (I := I)) (physicalDensity_sqrt_supported F D hPos h ω) l

end PhysicalRecordedInstrument

end QuantumProver.ElegantJointMeasurement.HilbertRecordedHilbertInstrument

import Mathlib
import QuantumProver.InformationTheory.ElegantJointMeasurement.NormalInstrumentRealization
import QuantumProver.InformationTheory.ElegantJointMeasurement.FiniteKrausPredual
import QuantumProver.QuantumChannels.NuclearTraceDuality

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory ProbabilityTheory InnerProductSpace Set Filter
open scoped BigOperators Topology ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace QuantumProver.MatrixNormalStateKernel

open QuantumProver.ElegantJointMeasurement.HilbertChoi QuantumProver.ElegantJointMeasurement.NuclearChoi QuantumProver.ElegantJointMeasurement.NormalCPInstruments
open QuantumProver.NuclearOperator (toOperator toOperator_injective rankOne)
open QuantumProver.HilbertNuclearCompression

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

local instance nuclearMeasurable : MeasurableSpace (Nuclear E) := borel _
local instance nuclearBorel : BorelSpace (Nuclear E) := ⟨rfl⟩

def stateChannel (σ : Nuclear E) : PhysicalOperation (Fin 1) E :=
  (QuantumProver.ElegantJointMeasurement.NormalInstrumentAbsorption.matrixEntry (0 : Fin 1) (0 : Fin 1)).smulRight σ

@[simp] theorem stateChannel_apply (σ : Nuclear E) (X : Matrix (Fin 1) (Fin 1) ℂ) :
    stateChannel σ X = Matrix.trace X • σ := by
  simp [stateChannel, QuantumProver.ElegantJointMeasurement.NormalInstrumentAbsorption.matrixEntry, Matrix.trace, Matrix.diag]

def pureSourceVector (v : E) : BlockSpace (Fin 1) E :=
  WithLp.toLp 2 (fun _ : Fin 1 => v)

def pureSourceKraus (v : E) : EuclideanSpace ℂ (Fin 1) →L[ℂ] E :=
  unvectorize (pureSourceVector v)

theorem stateChannel_rankOne_eq_finiteKraus (v : E) :
    stateChannel (rankOne (innerSL ℂ v) v) =
      QuantumProver.ElegantJointMeasurement.HilbertFiniteKrausPredual.finiteKrausOperation (fun _ : Unit => pureSourceKraus v) := by
  ext X
  apply toOperator_injective
  rw [stateChannel_apply, map_smul, QuantumProver.NuclearOperator.toOperator_rankOne,
    QuantumProver.ElegantJointMeasurement.HilbertFiniteKrausPredual.toOperator_finiteKrausOperation]
  simp only [Fintype.sum_unique]
  ext x
  change Matrix.trace X • ((innerSL ℂ v) x • v) =
    pureSourceKraus v
      (QuantumProver.ElegantJointMeasurement.HilbertChoi.matrixOperator X ((pureSourceKraus v).adjoint x))
  simp [pureSourceKraus, unvectorize_apply, unvectorize_adjoint_apply,
    pureSourceVector, QuantumProver.ElegantJointMeasurement.HilbertChoi.matrixOperator_apply,
    Matrix.trace, Matrix.diag, smul_smul]

theorem stateChannel_rankOne_completelyPositive (v : E) :
    CompletelyPositive (operationOperator
      (stateChannel (rankOne (innerSL ℂ v) v)).toLinearMap) := by
  rw [stateChannel_rankOne_eq_finiteKraus]
  exact QuantumProver.ElegantJointMeasurement.HilbertFiniteKrausPredual.completelyPositive_finiteKrausOperation _

variable {R : Type} [Fintype R] [DecidableEq R]

def stateAmplificationMap (X : Matrix (R × Fin 1) (R × Fin 1) ℂ) :
    Nuclear E →L[ℂ] (BlockSpace R E →L[ℂ] BlockSpace R E) :=
  (QuantumProver.NuclearOperator.toOperator (𝕜 := ℂ)
    (E := BlockSpace R E) (F := BlockSpace R E)).comp
      (∑ r, ∑ s, X (r,0) (s,0) •
        compose (insert (E := E) r) (PiLp.proj 2 (fun _ : R => E) s))

theorem stateAmplificationMap_apply
    (X : Matrix (R × Fin 1) (R × Fin 1) ℂ) (σ : Nuclear E) :
    stateAmplificationMap X σ =
      amplification (operationOperator (stateChannel σ).toLinearMap) X := by
  ext x r
  simp [stateAmplificationMap, amplification, blockOperator_apply,
    operationOperator, stateChannel_apply, matrixUnit, Matrix.trace, Matrix.diag,
    toOperator_compose, ContinuousLinearMap.comp_apply, Pi.single_apply, apply_ite]

theorem stateChannel_completelyPositive (σ : Nuclear E)
    (hσ : (toOperator σ).IsPositive) :
    CompletelyPositive (operationOperator (stateChannel σ).toLinearMap) := by
  intro R _ _ X hX
  obtain ⟨L, b, hb⟩ := exists_hilbertBasis ℂ E
  have hd : Summable (fun l => (inner ℂ (toOperator σ (b l)) (b l)).re) := by
    have hs := ((QuantumProver.HilbertNuclearTrace.hasSum_diagonal b σ).mapL Complex.reCLM).summable
    convert hs using 1
    funext l
    exact inner_re_symm (𝕜 := ℂ) _ _
  have hs : HasSum (nuclearColumn b (toOperator σ)) σ := by
    have h := nuclearColumns_hasSum b (toOperator σ) hσ hd
    rw [positiveLift_eq_of_toOperator b (toOperator σ) hσ hd σ rfl] at h
    exact h
  rw [← stateAmplificationMap_apply]
  apply ContinuousLinearMap.nonneg_iff_isPositive.mp
  apply isClosed_Ici.mem_of_tendsto (hs.mapL (stateAmplificationMap X))
  filter_upwards [] with s
  change 0 ≤ ∑ l ∈ s, stateAmplificationMap X (nuclearColumn b (toOperator σ) l)
  apply Finset.sum_nonneg
  intro l hl
  apply ContinuousLinearMap.nonneg_iff_isPositive.mpr
  rw [stateAmplificationMap_apply]
  change (amplification (operationOperator
    (stateChannel (rankOne (innerSL ℂ (squareRootColumn b (toOperator σ) l))
      (squareRootColumn b (toOperator σ) l))).toLinearMap) X).IsPositive
  exact stateChannel_rankOne_completelyPositive _ R X hX

theorem stateChannel_trace (σ : Nuclear E)
    (hσ : QuantumProver.HilbertNuclearTrace.trace σ = 1) (X : Matrix (Fin 1) (Fin 1) ℂ) :
    QuantumProver.HilbertNuclearTrace.trace (stateChannel σ X) = Matrix.trace X := by
  simp [hσ]

variable {H Ω : Type*} [MeasurableSpace H] [MeasurableSpace Ω]

theorem stronglyMeasurable_stateChannel_apply (σ : H → Nuclear E)
    (hσ : StronglyMeasurable σ) (X : Matrix (Fin 1) (Fin 1) ℂ) :
    StronglyMeasurable (fun h => stateChannel (σ h) X) := by
  simpa only [stateChannel_apply] using hσ.fun_const_smul (Matrix.trace X)

variable [TopologicalSpace.SeparableSpace E]

def stateInstrument (P : QuantumProver.ElegantJointMeasurement.NormalInstrumentAbsorption.Instrument E E H Ω) (σ : H → Nuclear E)
    (hpos : ∀ h, (toOperator (σ h)).IsPositive) (hstrong : StronglyMeasurable σ)
    (htrace : ∀ h, QuantumProver.HilbertNuclearTrace.trace (σ h) = 1) :
    Instrument (Fin 1) E H Ω :=
  QuantumProver.ElegantJointMeasurement.NormalInstrumentAbsorption.absorbInstrument P (fun h => stateChannel (σ h))
    (fun h => stateChannel_completelyPositive (σ h) (hpos h))
    (fun X => stronglyMeasurable_stateChannel_apply σ hstrong X)
    (fun h X => stateChannel_trace (σ h) (htrace h) X)

@[simp] theorem stateInstrument_operation
    (P : QuantumProver.ElegantJointMeasurement.NormalInstrumentAbsorption.Instrument E E H Ω) (σ : H → Nuclear E)
    (hpos : ∀ h, (toOperator (σ h)).IsPositive) (hstrong : StronglyMeasurable σ)
    (htrace : ∀ h, QuantumProver.HilbertNuclearTrace.trace (σ h) = 1)
    (h : H) (s : Set Ω) (X : Matrix (Fin 1) (Fin 1) ℂ) :
    (stateInstrument P σ hpos hstrong htrace).operation h s X =
      Matrix.trace X • P.operation h s (σ h) := by
  simp [stateInstrument, QuantumProver.ElegantJointMeasurement.NormalInstrumentAbsorption.absorbInstrument_operation]

def bornKernel (P : QuantumProver.ElegantJointMeasurement.NormalInstrumentAbsorption.Instrument E E H Ω) (σ : H → Nuclear E)
    (hpos : ∀ h, (toOperator (σ h)).IsPositive) (hstrong : StronglyMeasurable σ)
    (htrace : ∀ h, QuantumProver.HilbertNuclearTrace.trace (σ h) = 1) : Kernel H Ω :=
  (stateInstrument P σ hpos hstrong htrace).referenceKernel

instance isMarkovKernel_bornKernel
    (P : QuantumProver.ElegantJointMeasurement.NormalInstrumentAbsorption.Instrument E E H Ω) (σ : H → Nuclear E)
    (hpos : ∀ h, (toOperator (σ h)).IsPositive) (hstrong : StronglyMeasurable σ)
    (htrace : ∀ h, QuantumProver.HilbertNuclearTrace.trace (σ h) = 1) :
    IsMarkovKernel (bornKernel P σ hpos hstrong htrace) :=
  Instrument.isMarkovKernel_referenceKernel _

theorem bornKernel_apply (P : QuantumProver.ElegantJointMeasurement.NormalInstrumentAbsorption.Instrument E E H Ω) (σ : H → Nuclear E)
    (hpos : ∀ h, (toOperator (σ h)).IsPositive) (hstrong : StronglyMeasurable σ)
    (htrace : ∀ h, QuantumProver.HilbertNuclearTrace.trace (σ h) = 1)
    (h : H) (s : Set Ω) (hs : MeasurableSet s) :
    bornKernel P σ hpos hstrong htrace h s =
      ENNReal.ofReal (QuantumProver.HilbertNuclearTrace.trace (P.operation h s (σ h))).re := by
  rw [bornKernel, Instrument.referenceKernel_apply,
    Instrument.referenceMeasure_apply _ h s hs]
  simp [Instrument.referenceMass, Instrument.trace_physicalChoi,
    stateInstrument_operation]

open QuantumProver.ElegantJointMeasurement.SeparableHilbertEmbedding QuantumProver.ElegantJointMeasurement.NormalInstrumentRealization
open QuantumProver.ElegantJointMeasurement.NormalInstrumentKraus

def singletonDecode : Nuclear (BlockSpace (Fin 1) E) →L[ℂ] Nuclear E :=
  nuclearDecode (1 : Matrix (Fin 1) (Fin 1) ℂ)

omit [TopologicalSpace.SeparableSpace E] in
theorem singletonDecode_eq :
    singletonDecode (E := E) =
      compose (PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin 1 => E) 0) (insert (E := E) 0) := by
  simp [singletonDecode, nuclearDecode]

omit [TopologicalSpace.SeparableSpace E] in
theorem singletonDecode_isPositive (A : Nuclear (BlockSpace (Fin 1) E))
    (hA : (toOperator A).IsPositive) :
    (toOperator (singletonDecode A)).IsPositive := by
  rw [singletonDecode_eq, toOperator_compose,
    ← QuantumProver.ElegantJointMeasurement.NormalCompleteContraction.insert_adjoint]
  simpa only [ContinuousLinearMap.adjoint_adjoint] using
    hA.conj_adjoint (insert (I := Fin 1) (E := E) 0).adjoint

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

def physicalRecovery (J : E →ₗᵢ[ℂ] F) :
    Nuclear (BlockSpace (Fin 1) F) →L[ℂ] Nuclear E :=
  singletonDecode.comp (blockPullback J)

omit [TopologicalSpace.SeparableSpace E] in
theorem physicalRecovery_isPositive (J : E →ₗᵢ[ℂ] F)
    (A : Nuclear (BlockSpace (Fin 1) F)) (hA : (toOperator A).IsPositive) :
    (toOperator (physicalRecovery J A)).IsPositive := by
  apply singletonDecode_isPositive
  unfold blockPullback
  erw [toOperator_compose, ← blockLift_adjoint]
  simpa only [ContinuousLinearMap.adjoint_adjoint] using
    hA.conj_adjoint (blockLift (R := Fin 1) J.toContinuousLinearMap).adjoint

omit [TopologicalSpace.SeparableSpace E] in
theorem physicalRecovery_physicalChoi (J : E →ₗᵢ[ℂ] F)
    (P : Instrument (Fin 1) E H Ω) (h : H) (s : Set Ω) :
    physicalRecovery J ((padInstrument J P).physicalChoi h s) =
      P.operation h s (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
  change nuclearDecode (1 : Matrix (Fin 1) (Fin 1) ℂ)
    (blockPullback (I := Fin 1) J _) = _
  rw [blockPullback_physicalChoi, nuclearDecode_physicalChoi]

variable [MeasurableSpace.CountableOrCountablyGenerated H Ω]

theorem exists_physical_positive_born_density
    (P : QuantumProver.ElegantJointMeasurement.NormalInstrumentAbsorption.Instrument E E H Ω) (σ : H → Nuclear E)
    (hpos : ∀ h, (toOperator (σ h)).IsPositive) (hstrong : StronglyMeasurable σ)
    (htrace : ∀ h, QuantumProver.HilbertNuclearTrace.trace (σ h) = 1) :
    ∃ D : H × Ω → Nuclear E,
      StronglyMeasurable D ∧
      (∀ h ω, (toOperator (D (h,ω))).IsPositive) ∧
      (∀ h, Integrable (fun ω => D (h,ω)) (bornKernel P σ hpos hstrong htrace h)) ∧
      (∀ h (s : Set Ω), MeasurableSet s →
        (∫ ω in s, D (h,ω) ∂bornKernel P σ hpos hstrong htrace h) =
          P.operation h s (σ h)) := by
  let Q := stateInstrument P σ hpos hstrong htrace
  let J := separableEmbedding (E := E)
  let Qpad := padInstrument J Q
  obtain ⟨D, hDstrong, hDmeas, hDpos, hDtrace, hDbound, hDmass, hDint, hDset⟩ :=
    QuantumProver.ElegantJointMeasurement.NormalNuclearDensity.exists_physical_positive_nuclear_density Qpad
      (commonBlockBasis (I := Fin 1))
  let R := physicalRecovery J
  have href : Qpad.referenceKernel = bornKernel P σ hpos hstrong htrace :=
    referenceKernel_padInstrument J Q
  refine ⟨fun z => R (D z.1 z.2),
    R.continuous.comp_stronglyMeasurable hDstrong,
    fun h ω => physicalRecovery_isPositive J _ (hDpos h ω), ?_, ?_⟩
  · intro h
    rw [← href]
    exact R.integrable_comp (hDint h)
  · intro h s hs
    rw [← href, R.integral_comp_comm ((hDint h).integrableOn), hDset h s hs]
    change physicalRecovery J ((padInstrument J Q).physicalChoi h s) = _
    rw [physicalRecovery_physicalChoi]
    simp [Q, stateInstrument_operation]

omit [MeasurableSpace.CountableOrCountablyGenerated H Ω] in

theorem born_density_trace_one_ae
    (P : QuantumProver.ElegantJointMeasurement.NormalInstrumentAbsorption.Instrument E E H Ω) (σ : H → Nuclear E)
    (hpos : ∀ h, (toOperator (σ h)).IsPositive) (hstrong : StronglyMeasurable σ)
    (htrace : ∀ h, QuantumProver.HilbertNuclearTrace.trace (σ h) = 1)
    (D : H × Ω → Nuclear E)
    (hDint : ∀ h, Integrable (fun ω => D (h,ω)) (bornKernel P σ hpos hstrong htrace h))
    (hDset : ∀ h (s : Set Ω), MeasurableSet s →
      (∫ ω in s, D (h,ω) ∂bornKernel P σ hpos hstrong htrace h) = P.operation h s (σ h))
    (h : H) :
    ∀ᵐ ω ∂bornKernel P σ hpos hstrong htrace h,
      QuantumProver.HilbertNuclearTrace.trace (D (h,ω)) = 1 := by
  let μ := bornKernel P σ hpos hstrong htrace h
  let t := QuantumProver.HilbertNuclearTrace.trace (𝕜 := ℂ) (E := E)
  have htint : Integrable (fun ω => t (D (h,ω))) μ := t.integrable_comp (hDint h)
  apply htint.ae_eq_of_forall_setIntegral_eq _ (fun _ => (1 : ℂ)) (integrable_const 1)
  intro s hs _hfinite
  rw [t.integral_comp_comm ((hDint h).integrableOn), hDset h s hs, setIntegral_const]
  have hreal : 0 ≤ t (P.operation h s (σ h)) := by
    apply QuantumProver.MatrixNuclearTraceDuality.trace_nonneg_of_isPositive
    have hp := (stateInstrument P σ hpos hstrong htrace).physicalChoi_isPositive h s hs
    have hp' := singletonDecode_isPositive _ hp
    rw [singletonDecode, nuclearDecode_physicalChoi] at hp'
    simpa [stateInstrument_operation] using hp'
  have hmass : μ s = ENNReal.ofReal (t (P.operation h s (σ h))).re :=
    bornKernel_apply P σ hpos hstrong htrace h s hs
  rw [Measure.real, hmass, ENNReal.toReal_ofReal (Complex.nonneg_iff.mp hreal).1]
  apply Complex.ext
  · simp
  · simpa using (Complex.nonneg_iff.mp hreal).2.symm

omit [MeasurableSpace.CountableOrCountablyGenerated H Ω] in

theorem born_density_exception_null
    (P : QuantumProver.ElegantJointMeasurement.NormalInstrumentAbsorption.Instrument E E H Ω) (σ : H → Nuclear E)
    (hpos : ∀ h, (toOperator (σ h)).IsPositive) (hstrong : StronglyMeasurable σ)
    (htrace : ∀ h, QuantumProver.HilbertNuclearTrace.trace (σ h) = 1)
    (D : H × Ω → Nuclear E)
    (hDint : ∀ h, Integrable (fun ω => D (h,ω)) (bornKernel P σ hpos hstrong htrace h))
    (hDset : ∀ h (s : Set Ω), MeasurableSet s →
      (∫ ω in s, D (h,ω) ∂bornKernel P σ hpos hstrong htrace h) = P.operation h s (σ h))
    (h : H) :
    bornKernel P σ hpos hstrong htrace h
      {ω | QuantumProver.HilbertNuclearTrace.trace (D (h,ω)) ≠ 1} = 0 :=
  ae_iff.mp (born_density_trace_one_ae P σ hpos hstrong htrace D hDint hDset h)

def normalizeBornDensity (σ : H → Nuclear E) (D : H × Ω → Nuclear E) :
    H × Ω → Nuclear E := by
  classical
  exact fun z => if QuantumProver.HilbertNuclearTrace.trace (D z) = 1 then D z else σ z.1

omit [TopologicalSpace.SeparableSpace E]
  [MeasurableSpace.CountableOrCountablyGenerated H Ω] in
theorem stronglyMeasurable_normalizeBornDensity
    (σ : H → Nuclear E) (hσ : StronglyMeasurable σ)
    (D : H × Ω → Nuclear E) (hD : StronglyMeasurable D) :
    StronglyMeasurable (normalizeBornDensity σ D) := by
  have hg : MeasurableSet {z : H × Ω | QuantumProver.HilbertNuclearTrace.trace (D z) = 1} :=
    measurableSet_eq_fun
      (QuantumProver.HilbertNuclearTrace.trace.continuous.measurable.comp hD.measurable) measurable_const
  exact hD.piecewise hg (hσ.comp_measurable measurable_fst)

omit [MeasurableSpace H] [MeasurableSpace Ω] [TopologicalSpace.SeparableSpace E]
  [MeasurableSpace.CountableOrCountablyGenerated H Ω] in
theorem normalizeBornDensity_isPositive
    (σ : H → Nuclear E) (hσ : ∀ h, (toOperator (σ h)).IsPositive)
    (D : H × Ω → Nuclear E) (hD : ∀ h ω, (toOperator (D (h,ω))).IsPositive)
    (h : H) (ω : Ω) :
    (toOperator (normalizeBornDensity σ D (h,ω))).IsPositive := by
  unfold normalizeBornDensity
  split_ifs
  · exact hD h ω
  · exact hσ h

omit [MeasurableSpace H] [MeasurableSpace Ω] [TopologicalSpace.SeparableSpace E]
  [MeasurableSpace.CountableOrCountablyGenerated H Ω] in
theorem normalizeBornDensity_trace
    (σ : H → Nuclear E) (hσ : ∀ h, QuantumProver.HilbertNuclearTrace.trace (σ h) = 1)
    (D : H × Ω → Nuclear E) (z : H × Ω) :
    QuantumProver.HilbertNuclearTrace.trace (normalizeBornDensity σ D z) = 1 := by
  unfold normalizeBornDensity
  split_ifs with hz
  · exact hz
  · exact hσ z.1

theorem exists_physical_born_normalized_posterior
    (P : QuantumProver.ElegantJointMeasurement.NormalInstrumentAbsorption.Instrument E E H Ω) (σ : H → Nuclear E)
    (hpos : ∀ h, (toOperator (σ h)).IsPositive) (hstrong : StronglyMeasurable σ)
    (htrace : ∀ h, QuantumProver.HilbertNuclearTrace.trace (σ h) = 1) :
    ∃ D : H × Ω → Nuclear E,
      StronglyMeasurable D ∧ Measurable D ∧
      (∀ h ω, (toOperator (D (h,ω))).IsPositive) ∧
      (∀ h ω, QuantumProver.HilbertNuclearTrace.trace (D (h,ω)) = 1) ∧
      (∀ h, Integrable (fun ω => D (h,ω)) (bornKernel P σ hpos hstrong htrace h)) ∧
      (∀ h (s : Set Ω), MeasurableSet s →
        (∫ ω in s, D (h,ω) ∂bornKernel P σ hpos hstrong htrace h) =
          P.operation h s (σ h)) := by
  obtain ⟨A, hAstrong, hApos, hAint, hAset⟩ :=
    exists_physical_positive_born_density P σ hpos hstrong htrace
  have hae (h : H) :
      (fun ω => normalizeBornDensity σ A (h,ω)) =ᵐ[bornKernel P σ hpos hstrong htrace h]
        (fun ω => A (h,ω)) := by
    filter_upwards [born_density_trace_one_ae P σ hpos hstrong htrace A
      hAint hAset h] with ω hω
    simp [normalizeBornDensity, hω]
  have hs := stronglyMeasurable_normalizeBornDensity σ hstrong A hAstrong
  refine ⟨normalizeBornDensity σ A, hs, hs.measurable,
    normalizeBornDensity_isPositive σ hpos A hApos,
    fun h ω => normalizeBornDensity_trace σ htrace A (h,ω), ?_, ?_⟩
  · intro h
    exact (hAint h).congr (hae h).symm
  · intro h s hs
    rw [integral_congr_ae (ae_restrict_of_ae (hae h))]
    exact hAset h s hs

def posterior
    (P : QuantumProver.ElegantJointMeasurement.NormalInstrumentAbsorption.Instrument E E H Ω) (σ : H → Nuclear E)
    (hpos : ∀ h, (toOperator (σ h)).IsPositive) (hstrong : StronglyMeasurable σ)
    (htrace : ∀ h, QuantumProver.HilbertNuclearTrace.trace (σ h) = 1) : H × Ω → Nuclear E :=
  Classical.choose (exists_physical_born_normalized_posterior P σ hpos hstrong htrace)

theorem stronglyMeasurable_posterior
    (P : QuantumProver.ElegantJointMeasurement.NormalInstrumentAbsorption.Instrument E E H Ω) (σ : H → Nuclear E)
    (hpos : ∀ h, (toOperator (σ h)).IsPositive) (hstrong : StronglyMeasurable σ)
    (htrace : ∀ h, QuantumProver.HilbertNuclearTrace.trace (σ h) = 1) :
    StronglyMeasurable (posterior P σ hpos hstrong htrace) :=
  (Classical.choose_spec (exists_physical_born_normalized_posterior P σ hpos hstrong htrace)).1

theorem measurable_posterior
    (P : QuantumProver.ElegantJointMeasurement.NormalInstrumentAbsorption.Instrument E E H Ω) (σ : H → Nuclear E)
    (hpos : ∀ h, (toOperator (σ h)).IsPositive) (hstrong : StronglyMeasurable σ)
    (htrace : ∀ h, QuantumProver.HilbertNuclearTrace.trace (σ h) = 1) :
    Measurable (posterior P σ hpos hstrong htrace) :=
  (stronglyMeasurable_posterior P σ hpos hstrong htrace).measurable

theorem posterior_isPositive
    (P : QuantumProver.ElegantJointMeasurement.NormalInstrumentAbsorption.Instrument E E H Ω) (σ : H → Nuclear E)
    (hpos : ∀ h, (toOperator (σ h)).IsPositive) (hstrong : StronglyMeasurable σ)
    (htrace : ∀ h, QuantumProver.HilbertNuclearTrace.trace (σ h) = 1) (h : H) (ω : Ω) :
    (toOperator (posterior P σ hpos hstrong htrace (h,ω))).IsPositive :=
  (Classical.choose_spec (exists_physical_born_normalized_posterior P σ hpos hstrong htrace)).2.2.1 h ω

theorem posterior_trace
    (P : QuantumProver.ElegantJointMeasurement.NormalInstrumentAbsorption.Instrument E E H Ω) (σ : H → Nuclear E)
    (hpos : ∀ h, (toOperator (σ h)).IsPositive) (hstrong : StronglyMeasurable σ)
    (htrace : ∀ h, QuantumProver.HilbertNuclearTrace.trace (σ h) = 1) (h : H) (ω : Ω) :
    QuantumProver.HilbertNuclearTrace.trace (posterior P σ hpos hstrong htrace (h,ω)) = 1 :=
  (Classical.choose_spec (exists_physical_born_normalized_posterior P σ hpos hstrong htrace)).2.2.2.1 h ω

theorem integrable_posterior
    (P : QuantumProver.ElegantJointMeasurement.NormalInstrumentAbsorption.Instrument E E H Ω) (σ : H → Nuclear E)
    (hpos : ∀ h, (toOperator (σ h)).IsPositive) (hstrong : StronglyMeasurable σ)
    (htrace : ∀ h, QuantumProver.HilbertNuclearTrace.trace (σ h) = 1) (h : H) :
    Integrable (fun ω => posterior P σ hpos hstrong htrace (h,ω))
      (bornKernel P σ hpos hstrong htrace h) :=
  (Classical.choose_spec (exists_physical_born_normalized_posterior P σ hpos hstrong htrace)).2.2.2.2.1 h

theorem setIntegral_posterior
    (P : QuantumProver.ElegantJointMeasurement.NormalInstrumentAbsorption.Instrument E E H Ω) (σ : H → Nuclear E)
    (hpos : ∀ h, (toOperator (σ h)).IsPositive) (hstrong : StronglyMeasurable σ)
    (htrace : ∀ h, QuantumProver.HilbertNuclearTrace.trace (σ h) = 1)
    (h : H) (s : Set Ω) (hs : MeasurableSet s) :
    (∫ ω in s, posterior P σ hpos hstrong htrace (h,ω)
      ∂bornKernel P σ hpos hstrong htrace h) = P.operation h s (σ h) :=
  (Classical.choose_spec (exists_physical_born_normalized_posterior P σ hpos hstrong htrace)).2.2.2.2.2 h s hs

end QuantumProver.MatrixNormalStateKernel

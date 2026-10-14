import QuantumProver.InformationTheory.ElegantJointMeasurement.NormalInstrumentAbsorption
import QuantumProver.InformationTheory.ElegantJointMeasurement.HilbertRecovery
import QuantumProver.InformationTheory.ElegantJointMeasurement.NormalInstrumentKraus
import QuantumProver.InformationTheory.ElegantJointMeasurement.SeparableHilbertEmbedding

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000

open MeasureTheory ProbabilityTheory InnerProductSpace Set Filter
open scoped BigOperators InnerProduct ComplexOrder Topology Matrix.Norms.L2Operator

namespace QuantumProver.ElegantJointMeasurement.NormalInstrumentRealization

open QuantumProver.ElegantJointMeasurement.HilbertChoi QuantumProver.ElegantJointMeasurement.NuclearChoi QuantumProver.ElegantJointMeasurement.NormalCPInstruments
open QuantumProver.ElegantJointMeasurement.SeparableHilbertEmbedding
open QuantumProver.NuclearOperator (toOperator toOperator_injective)
open QuantumProver.HilbertNuclearCompression

variable {I : Type} [Fintype I] [DecidableEq I]
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable {H Ω : Type*} [MeasurableSpace H] [MeasurableSpace Ω]

local instance nuclearMeasurableE : MeasurableSpace (Nuclear E) := borel _
local instance nuclearBorelE : BorelSpace (Nuclear E) := ⟨rfl⟩
local instance nuclearMeasurableF : MeasurableSpace (Nuclear F) := borel _
local instance nuclearBorelF : BorelSpace (Nuclear F) := ⟨rfl⟩
local instance operationMeasurableF : MeasurableSpace (PhysicalOperation I F) := borel _
local instance operationBorelF : BorelSpace (PhysicalOperation I F) := ⟨rfl⟩
local instance krausMeasurableF : MeasurableSpace (EuclideanSpace ℂ I →L[ℂ] F) := borel _
local instance krausBorelF : BorelSpace (EuclideanSpace ℂ I →L[ℂ] F) := ⟨rfl⟩

theorem stronglyMeasurable_finite_evaluation [TopologicalSpace.SeparableSpace F]
    (ρ : H → PhysicalOperation I F) (hρ : Measurable ρ) (X : Matrix I I ℂ) :
    StronglyMeasurable (fun h => ρ h X) := by
  apply QuantumProver.ElegantJointMeasurement.NormalInstrumentAbsorption.stronglyMeasurable_of_weak_coordinates
  intro x y
  let test : Nuclear F →L[ℂ] ℂ := (innerSL ℂ x).comp
    ((ContinuousLinearMap.apply ℂ F y).comp
      (QuantumProver.NuclearOperator.toOperator (𝕜 := ℂ) (E := F) (F := F)))
  let eval : PhysicalOperation I F →L[ℂ] Nuclear F :=
    ContinuousLinearMap.apply ℂ (Nuclear F) X
  exact (test.comp eval).continuous.measurable.comp hρ

def polarAbsorbedInstrument [TopologicalSpace.SeparableSpace E]
    [TopologicalSpace.SeparableSpace F]
    (P : QuantumProver.ElegantJointMeasurement.NormalInstrumentAbsorption.Instrument F E H Ω)
    (φ : F) (hφ : ‖φ‖ = 1) (K : H → EuclideanSpace ℂ I →L[ℂ] F) (hK : Measurable K) :
    Instrument I E H Ω :=
  QuantumProver.ElegantJointMeasurement.NormalInstrumentAbsorption.absorbInstrument P
    (fun h => QuantumProver.ElegantJointMeasurement.HilbertRecovery.matrixRecovery φ (K h))
    (fun h => QuantumProver.ElegantJointMeasurement.HilbertRecovery.matrixRecovery_completelyPositive φ (K h))
    (fun X => stronglyMeasurable_finite_evaluation _
      ((QuantumProver.ElegantJointMeasurement.HilbertRecovery.measurable_matrixRecovery φ).comp hK) X)
    (fun h X => QuantumProver.ElegantJointMeasurement.HilbertRecovery.trace_matrixRecovery φ hφ (K h) X)

@[simp] theorem polarAbsorbedInstrument_operation [TopologicalSpace.SeparableSpace E]
    [TopologicalSpace.SeparableSpace F]
    (P : QuantumProver.ElegantJointMeasurement.NormalInstrumentAbsorption.Instrument F E H Ω)
    (φ : F) (hφ : ‖φ‖ = 1) (K : H → EuclideanSpace ℂ I →L[ℂ] F) (hK : Measurable K)
    (h : H) (s : Set Ω) (X : Matrix I I ℂ) :
    (polarAbsorbedInstrument P φ hφ K hK).operation h s X =
      P.operation h s (QuantumProver.ElegantJointMeasurement.HilbertRecovery.matrixRecovery φ (K h) X) := rfl

theorem polarRecovery_square_matrix (φ : E) (K : EuclideanSpace ℂ I →L[ℂ] E)
    (X : Matrix I I ℂ) :
    QuantumProver.ElegantJointMeasurement.HilbertRecovery.nuclearRecovery φ K
      (compose (QuantumProver.ElegantJointMeasurement.HilbertPolar.positiveInput K) (QuantumProver.ElegantJointMeasurement.HilbertPolar.positiveInput K)
        (QuantumProver.ElegantJointMeasurement.HilbertRecovery.nuclearMatrix X)) =
      compose K K.adjoint (QuantumProver.ElegantJointMeasurement.HilbertRecovery.nuclearMatrix X) :=
  QuantumProver.ElegantJointMeasurement.HilbertRecovery.nuclearRecovery_square φ K _

end QuantumProver.ElegantJointMeasurement.NormalInstrumentRealization

namespace QuantumProver.ElegantJointMeasurement.NormalInstrumentRealization

open QuantumProver.ElegantJointMeasurement.HilbertChoi QuantumProver.ElegantJointMeasurement.NuclearChoi QuantumProver.ElegantJointMeasurement.NormalCPInstruments
open QuantumProver.ElegantJointMeasurement.SeparableHilbertEmbedding QuantumProver.ElegantJointMeasurement.NormalInstrumentKraus
open QuantumProver.NuclearOperator (toOperator toOperator_injective)
open QuantumProver.HilbertNuclearCompression

variable {I : Type} [Fintype I] [DecidableEq I]
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

def blockPullback (J : E →ₗᵢ[ℂ] F) : Nuclear (BlockSpace I F) →L[ℂ] Nuclear (BlockSpace I E) :=
  compose (blockLift J.toContinuousLinearMap.adjoint) (blockLift J.toContinuousLinearMap)

def pullbackVector (J : E →ₗᵢ[ℂ] F) : BlockSpace I F →L[ℂ] BlockSpace I E :=
  blockLift J.toContinuousLinearMap.adjoint

theorem unvectorize_pullbackVector (J : E →ₗᵢ[ℂ] F) (v : BlockSpace I F) :
    unvectorize (pullbackVector J v) = J.toContinuousLinearMap.adjoint ∘L unvectorize v := by
  ext x
  simp only [unvectorize_apply, ContinuousLinearMap.comp_apply, map_sum, map_smul]
  rfl

theorem blockPullback_rankOne (J : E →ₗᵢ[ℂ] F) (v : BlockSpace I F) :
    blockPullback J (QuantumProver.NuclearOperator.rankOne (innerSL ℂ v) v) =
      QuantumProver.NuclearOperator.rankOne (innerSL ℂ (pullbackVector J v)) (pullbackVector J v) := by
  have hφ : (innerSL ℂ v).comp (blockLift (R := I) J.toContinuousLinearMap) =
      innerSL ℂ (pullbackVector J v) := by
    ext x
    change inner ℂ v (blockLift J.toContinuousLinearMap x) =
      inner ℂ (blockLift J.toContinuousLinearMap.adjoint v) x
    rw [← blockLift_adjoint]
    exact (ContinuousLinearMap.adjoint_inner_left _ _ _).symm
  simp only [blockPullback, compose_rankOne, hφ, pullbackVector]

theorem blockPullback_pad_block (J : E →ₗᵢ[ℂ] F) (i j : I) (T : Nuclear E) :
    blockPullback J (compose (QuantumProver.ElegantJointMeasurement.HilbertChoi.insert (E := F) i)
      (PiLp.proj 2 (fun _ : I => F) j) (padNuclear J T)) =
      compose (QuantumProver.ElegantJointMeasurement.HilbertChoi.insert (E := E) i)
        (PiLp.proj 2 (fun _ : I => E) j) T := by
  apply toOperator_injective
  ext x r
  simp only [blockPullback, toOperator_compose, toOperator_padNuclear,
    ContinuousLinearMap.comp_apply, blockLift_apply, PiLp.proj_apply]
  by_cases hr : r = i
  · subst r
    simp only [insert_apply_apply, ite_true, LinearIsometry.coe_toContinuousLinearMap,
      adjoint_embedding_apply]
  · simp only [insert_apply_apply, hr, ite_false, map_zero]

variable {H Ω : Type*} [MeasurableSpace H] [MeasurableSpace Ω]

theorem blockPullback_physicalChoi (J : E →ₗᵢ[ℂ] F) (P : Instrument I E H Ω)
    (h : H) (s : Set Ω) :
    blockPullback J ((padInstrument J P).physicalChoi h s) = P.physicalChoi h s := by
  unfold Instrument.physicalChoi
  rw [nuclearChoi_eq, nuclearChoi_eq]
  simp only [map_sum, padInstrument_operation]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  exact blockPullback_pad_block J i j _

theorem nuclearDecode_rankOne (v : BlockSpace I E) (X : Matrix I I ℂ) :
    nuclearDecode X (QuantumProver.NuclearOperator.rankOne (innerSL ℂ v) v) = nuclearKrausAction v X := by
  apply toOperator_injective
  rw [toOperator_nuclearDecode, QuantumProver.NuclearOperator.toOperator_rankOne, ← rankOne_def,
    decode_rankOne, toOperator_nuclearKrausAction]

theorem inputGram_rankOne (v : BlockSpace I E) :
    inputGram (QuantumProver.NuclearOperator.rankOne (innerSL ℂ v) v) =
      Matrix.gram ℂ (fun i : I => v i) := by
  ext i j
  change QuantumProver.HilbertNuclearTrace.trace
    (compose (PiLp.proj 2 (fun _ : I => E) j) (QuantumProver.ElegantJointMeasurement.HilbertChoi.insert i)
      (QuantumProver.NuclearOperator.rankOne (innerSL ℂ v) v)) = _
  rw [compose_rankOne, QuantumProver.HilbertNuclearTrace.trace_rankOne]
  simp [ContinuousLinearMap.comp_apply, PiLp.inner_apply, Matrix.gram_apply]
  simp_rw [apply_ite]
  simp

theorem matrixOperator_gram_unvectorize (v : BlockSpace I E) :
    matrixOperator (Matrix.gram ℂ (fun i : I => v i)) =
      (unvectorize v).adjoint ∘L unvectorize v := by
  ext x i
  simp only [matrixOperator_apply, Matrix.gram_apply, ContinuousLinearMap.comp_apply,
    unvectorize_adjoint_apply, unvectorize_apply, inner_sum, inner_smul_right]
  exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)

theorem nuclearPositiveRankOne_smul (c : ℂ) (v : E) :
    QuantumProver.NuclearOperator.rankOne (innerSL ℂ (c • v)) (c • v) =
      (c * star c) • QuantumProver.NuclearOperator.rankOne (innerSL ℂ v) v := by
  apply toOperator_injective
  simp only [map_smul, QuantumProver.NuclearOperator.toOperator_rankOne]
  ext x
  simp only [ContinuousLinearMap.smulRight_apply, innerSL_apply_apply,
    inner_smul_left, smul_apply, smul_smul]
  congr 1
  simp only [mul_assoc, mul_comm, mul_left_comm, starRingEnd_apply]

theorem blockPullback_normalizedColumn (J : E →ₗᵢ[ℂ] F)
    (b : HilbertBasis ℕ ℂ (BlockSpace I F)) (A : Nuclear (BlockSpace I F)) (l : ℕ) :
    blockPullback J ((labelWeight l)⁻¹ • nuclearColumn b (toOperator A) l) =
      QuantumProver.NuclearOperator.rankOne
        (innerSL ℂ ((labelKrausScale l : ℂ) • pullbackVector J (squareRootColumn b (toOperator A) l)))
        ((labelKrausScale l : ℂ) • pullbackVector J (squareRootColumn b (toOperator A) l)) := by
  rw [ContinuousLinearMap.map_smul_of_tower, nuclearColumn, blockPullback_rankOne,
    nuclearPositiveRankOne_smul]
  have hc : (labelKrausScale l : ℂ) * star (labelKrausScale l : ℂ) =
      (((labelWeight l)⁻¹ : ℝ) : ℂ) := by
    have hs : star (labelKrausScale l : ℂ) = (labelKrausScale l : ℂ) :=
      Complex.conj_ofReal _
    rw [hs, ← Complex.ofReal_mul, ← pow_two, labelKrausScale_sq]
  rw [hc]
  exact RCLike.real_smul_eq_coe_smul (K := ℂ) (E := Nuclear (BlockSpace I E)) _ _

end QuantumProver.ElegantJointMeasurement.NormalInstrumentRealization

namespace QuantumProver.ElegantJointMeasurement.NormalInstrumentRealization

open QuantumProver.ElegantJointMeasurement.HilbertChoi QuantumProver.ElegantJointMeasurement.NuclearChoi QuantumProver.ElegantJointMeasurement.NormalCPInstruments
open QuantumProver.ElegantJointMeasurement.SeparableHilbertEmbedding QuantumProver.ElegantJointMeasurement.NormalInstrumentKraus
open QuantumProver.NuclearOperator (toOperator toOperator_injective)

variable {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [TopologicalSpace.SeparableSpace E]
variable {H Ω : Type*} [MeasurableSpace H] [MeasurableSpace Ω]
variable [MeasurableSpace.CountableOrCountablyGenerated H Ω]

local instance pulledBlockMeasurable : MeasurableSpace (BlockSpace I E) := borel _
local instance pulledBlockBorel : BorelSpace (BlockSpace I E) := ⟨rfl⟩
local instance pulledKrausMeasurable : MeasurableSpace (EuclideanSpace ℂ I →L[ℂ] E) := borel _
local instance pulledKrausBorel : BorelSpace (EuclideanSpace ℂ I →L[ℂ] E) := ⟨rfl⟩
local instance commonBlockMeasurable : MeasurableSpace (BlockSpace I CommonHilbert) := borel _
local instance commonBlockBorel : BorelSpace (BlockSpace I CommonHilbert) := ⟨rfl⟩
local instance commonBlockOperatorMeasurable :
    MeasurableSpace (BlockSpace I CommonHilbert →L[ℂ] BlockSpace I CommonHilbert) := borel _
local instance commonBlockOperatorBorel :
    BorelSpace (BlockSpace I CommonHilbert →L[ℂ] BlockSpace I CommonHilbert) := ⟨rfl⟩
local instance commonBlockNuclearMeasurable : MeasurableSpace (Nuclear (BlockSpace I CommonHilbert)) := borel _
local instance commonBlockNuclearBorel : BorelSpace (Nuclear (BlockSpace I CommonHilbert)) := ⟨rfl⟩

theorem exists_physical_separable_probability_kraus_representation
    (P : Instrument I E H Ω) :
    ∃ W : H → Ω × ℕ → BlockSpace I E,
      StronglyMeasurable (fun z : H × (Ω × ℕ) => W z.1 z.2) ∧
      Measurable (fun z : H × (Ω × ℕ) => unvectorize (W z.1 z.2)) ∧
      (∀ h X, Integrable (fun z : Ω × ℕ => nuclearKrausAction (W h z) X)
        (fineProbabilityKernel P h)) ∧
      (∀ h (s : Set Ω), MeasurableSet s → ∀ X,
        (∫ z : Ω × ℕ, nuclearKrausAction (W h z) X
          ∂((P.referenceKernel h).restrict s).prod labelProbability) = P.operation h s X) ∧
      (∀ h, Integrable (fun z : Ω × ℕ => Matrix.gram ℂ (fun i : I => W h z i))
        (fineProbabilityKernel P h)) ∧
      (∀ h, (∫ z : Ω × ℕ, Matrix.gram ℂ (fun i : I => W h z i)
        ∂fineProbabilityKernel P h) = (1 : Matrix I I ℂ)) := by
  let J : E →ₗᵢ[ℂ] CommonHilbert := separableEmbedding (E := E)
  let Ppad : Instrument I CommonHilbert H Ω := padInstrument J P
  let b : HilbertBasis ℕ ℂ (BlockSpace I CommonHilbert) := commonBlockBasis (I := I)
  haveI : SecondCountableTopology (BlockSpace I CommonHilbert) := secondCountable_block_of_basis b
  obtain ⟨D, hstrong, hmeas, hpos, htrace, hbound, hmass, hint, hset⟩ :=
    QuantumProver.ElegantJointMeasurement.NormalNuclearDensity.exists_physical_positive_nuclear_density Ppad b
  have hRef (h : H) : Ppad.referenceKernel h = P.referenceKernel h := by
    exact congrArg (fun κ : Kernel H Ω => κ h) (referenceKernel_padInstrument J P)
  have hd (h : H) : Measurable (D h) :=
    hmeas.comp (measurable_const.prodMk measurable_id)
  let N (h : H) : Ω × ℕ → Nuclear (BlockSpace I CommonHilbert) :=
    normalizeCountField (fineNuclearColumn b (D h))
  have hn (h : H) (μ : Measure Ω) (hμ : Integrable (D h) μ) :
      Integrable (N h) (μ.prod labelProbability) :=
    integrable_normalizeCountField _ (stronglyMeasurable_fineNuclearColumn b (D h) (hd h)) μ
      (integrable_fineNuclearColumn b (D h) (hd h) (hpos h) μ hμ)
  have hi (h : H) (μ : Measure Ω) [SFinite μ] (hμ : Integrable (D h) μ) :
      (∫ z, N h z ∂μ.prod labelProbability) = ∫ ω, D h ω ∂μ := by
    rw [integral_normalizeCountField _
      (stronglyMeasurable_fineNuclearColumn b (D h) (hd h)) μ
      (integrable_fineNuclearColumn b (D h) (hd h) (hpos h) μ hμ)]
    exact integral_fineNuclearColumn b (D h) (hd h) (hpos h) μ hμ
  have hintPhysical (h : H) : Integrable (D h) (P.referenceKernel h) := by
    simpa only [hRef h] using hint h
  let W (h : H) (z : Ω × ℕ) : BlockSpace I E :=
    (labelKrausScale z.2 : ℂ) • pullbackVector J (squareRootColumn b (toOperator (D h z.1)) z.2)
  let R : Nuclear (BlockSpace I CommonHilbert) →L[ℂ] Nuclear (BlockSpace I E) := blockPullback J
  have hRank (h : H) (z : Ω × ℕ) :
      R (N h z) = QuantumProver.NuclearOperator.rankOne (innerSL ℂ (W h z)) (W h z) :=
    blockPullback_normalizedColumn J b (D h z.1) z.2
  have hAction (h : H) (X : Matrix I I ℂ) :
      (fun z => (nuclearDecode (E := E) X).comp R (N h z)) =
        fun z => nuclearKrausAction (W h z) X := by
    funext z
    change nuclearDecode X (R (N h z)) = _
    rw [hRank, nuclearDecode_rankOne]
  have hGram (h : H) :
      (fun z => (inputGram (I := I) (E := E)).comp R (N h z)) =
        fun z => Matrix.gram ℂ (fun i : I => W h z i) := by
    funext z
    change inputGram (R (N h z)) = _
    rw [hRank, inputGram_rankOne]
  have hW : StronglyMeasurable (fun z : H × (Ω × ℕ) => W z.1 z.2) := by
    have ho : Measurable (fun z : H × Ω => toOperator (D z.1 z.2)) :=
      (QuantumProver.NuclearOperator.toOperator (𝕜 := ℂ) (E := BlockSpace I CommonHilbert)
        (F := BlockSpace I CommonHilbert)).continuous.measurable.comp hmeas
    have hm : Measurable (fun z : (H × Ω) × ℕ =>
        squareRootColumn b (toOperator (D z.1.1 z.1.2)) z.2) :=
      measurable_from_prod_countable_left (fun l => measurable_squareRootColumn b _ ho l)
    have hA : Measurable (fun z : H × (Ω × ℕ) => ((z.1,z.2.1),z.2.2)) :=
      (measurable_fst.prodMk (measurable_fst.comp measurable_snd)).prodMk
        (measurable_snd.comp measurable_snd)
    have hv : StronglyMeasurable (fun z : H × (Ω × ℕ) =>
        squareRootColumn b (toOperator (D z.1 z.2.1)) z.2.2) :=
      (hm.comp hA).stronglyMeasurable
    have hw : StronglyMeasurable (fun z : H × (Ω × ℕ) => (labelKrausScale z.2.2 : ℂ)) :=
      ((measurable_of_countable (fun l : ℕ => (labelKrausScale l : ℂ))).comp
        (measurable_snd.comp measurable_snd)).stronglyMeasurable
    exact hw.smul ((pullbackVector J).continuous.comp_stronglyMeasurable hv)
  refine ⟨W, hW, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [Function.comp_def, unvectorizeMap_apply] using
      (unvectorizeMap (I := I) (E := E)).continuous.measurable.comp hW.measurable
  · intro h X
    rw [fineProbabilityKernel_apply, ← hAction h X]
    exact ((nuclearDecode (E := E) X).comp R).integrable_comp
      (hn h (P.referenceKernel h) (hintPhysical h))
  · intro h s hs X
    rw [← hAction h X]
    rw [((nuclearDecode (E := E) X).comp R).integral_comp_comm
      (hn h ((P.referenceKernel h).restrict s) (hintPhysical h).integrableOn)]
    rw [hi h ((P.referenceKernel h).restrict s) (hintPhysical h).integrableOn]
    have hS : (∫ ω in s, D h ω ∂P.referenceKernel h) = Ppad.physicalChoi h s := by
      simpa only [hRef h] using hset h s hs
    rw [hS]
    change nuclearDecode X (blockPullback J ((padInstrument J P).physicalChoi h s)) = _
    rw [blockPullback_physicalChoi, nuclearDecode_physicalChoi]
  · intro h
    rw [fineProbabilityKernel_apply, ← hGram h]
    exact ((inputGram (I := I) (E := E)).comp R).integrable_comp
      (hn h (P.referenceKernel h) (hintPhysical h))
  · intro h
    rw [fineProbabilityKernel_apply, ← hGram h]
    rw [((inputGram (I := I) (E := E)).comp R).integral_comp_comm
      (hn h (P.referenceKernel h) (hintPhysical h))]
    rw [hi h (P.referenceKernel h) (hintPhysical h)]
    have hU : (∫ ω, D h ω ∂P.referenceKernel h) = Ppad.physicalChoi h Set.univ := by
      simpa only [hRef h, Measure.restrict_univ] using hset h Set.univ MeasurableSet.univ
    rw [hU]
    change inputGram (blockPullback J ((padInstrument J P).physicalChoi h Set.univ)) = _
    rw [blockPullback_physicalChoi, inputGram_physicalChoi_univ]

end QuantumProver.ElegantJointMeasurement.NormalInstrumentRealization

namespace QuantumProver.ElegantJointMeasurement.NormalInstrumentRealization

open QuantumProver.ElegantJointMeasurement.HilbertChoi QuantumProver.ElegantJointMeasurement.NuclearChoi QuantumProver.ElegantJointMeasurement.NormalCPInstruments
open QuantumProver.ElegantJointMeasurement.NormalInstrumentKraus
open QuantumProver.NuclearOperator (toOperator toOperator_injective)
open QuantumProver.HilbertNuclearCompression

variable {I : Type} [Fintype I] [DecidableEq I]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem matrixMatrixOperator_eq (X : Matrix I I ℂ) :
    matrixOperator X = QuantumProver.ElegantJointMeasurement.HilbertPolar.matrixOperator X := by
  ext x i
  rfl

theorem nuclearMatrix_sandwich (A X : Matrix I I ℂ) :
    QuantumProver.ElegantJointMeasurement.HilbertRecovery.nuclearMatrix (A * X * star A) =
      compose (QuantumProver.ElegantJointMeasurement.HilbertPolar.matrixOperator A)
        (QuantumProver.ElegantJointMeasurement.HilbertPolar.matrixOperator A).adjoint
        (QuantumProver.ElegantJointMeasurement.HilbertRecovery.nuclearMatrix X) := by
  apply toOperator_injective
  rw [QuantumProver.ElegantJointMeasurement.HilbertRecovery.toOperator_nuclearMatrix, toOperator_compose,
    QuantumProver.ElegantJointMeasurement.HilbertRecovery.toOperator_nuclearMatrix]
  change QuantumProver.ElegantJointMeasurement.HilbertPolar.matrixOperator (A * X * star A) =
    (QuantumProver.ElegantJointMeasurement.HilbertPolar.matrixOperator A * QuantumProver.ElegantJointMeasurement.HilbertPolar.matrixOperator X) *
      star (QuantumProver.ElegantJointMeasurement.HilbertPolar.matrixOperator A)
  simp only [map_mul, map_star]

theorem matrixRecovery_square_unvectorize (φ : E) (v : BlockSpace I E) (X : Matrix I I ℂ) :
    QuantumProver.ElegantJointMeasurement.HilbertRecovery.matrixRecovery φ (unvectorize v)
      (QuantumProver.ElegantJointMeasurement.HilbertPolar.positiveInputMatrix (unvectorize v) * X *
        star (QuantumProver.ElegantJointMeasurement.HilbertPolar.positiveInputMatrix (unvectorize v))) =
      nuclearKrausAction v X := by
  rw [QuantumProver.ElegantJointMeasurement.HilbertRecovery.matrixRecovery, ContinuousLinearMap.comp_apply,
    nuclearMatrix_sandwich, QuantumProver.ElegantJointMeasurement.HilbertPolar.matrixOperator_positiveInputMatrix,
    QuantumProver.ElegantJointMeasurement.HilbertPolar.positiveInput_selfAdjoint,
    QuantumProver.ElegantJointMeasurement.HilbertRecovery.nuclearRecovery_square]
  apply toOperator_injective
  rw [toOperator_compose, QuantumProver.ElegantJointMeasurement.HilbertRecovery.toOperator_nuclearMatrix,
    toOperator_nuclearKrausAction]
  simp only [krausAction, ContinuousLinearMap.comp_assoc, matrixMatrixOperator_eq]

theorem squareMatrix_gram_unvectorize (v : BlockSpace I E) :
    star (QuantumProver.ElegantJointMeasurement.HilbertPolar.positiveInputMatrix (unvectorize v)) *
      QuantumProver.ElegantJointMeasurement.HilbertPolar.positiveInputMatrix (unvectorize v) =
        Matrix.gram ℂ (fun i : I => v i) := by
  apply (QuantumProver.ElegantJointMeasurement.HilbertPolar.matrixOperator (I := I)).injective
  change QuantumProver.ElegantJointMeasurement.HilbertPolar.matrixOperator
      (star (QuantumProver.ElegantJointMeasurement.HilbertPolar.positiveInputMatrix (unvectorize v)) *
        QuantumProver.ElegantJointMeasurement.HilbertPolar.positiveInputMatrix (unvectorize v)) =
    QuantumProver.ElegantJointMeasurement.HilbertPolar.matrixOperator (Matrix.gram ℂ (fun i : I => v i))
  rw [map_mul, map_star, QuantumProver.ElegantJointMeasurement.HilbertPolar.matrixOperator_positiveInputMatrix]
  change (QuantumProver.ElegantJointMeasurement.HilbertPolar.positiveInput (unvectorize v)).adjoint ∘L
      QuantumProver.ElegantJointMeasurement.HilbertPolar.positiveInput (unvectorize v) = _
  rw [QuantumProver.ElegantJointMeasurement.HilbertPolar.positiveInput_selfAdjoint, QuantumProver.ElegantJointMeasurement.HilbertPolar.positiveInput_square]
  rw [← matrixMatrixOperator_eq, matrixOperator_gram_unvectorize]
  rfl

local instance squareKrausMeasurable : MeasurableSpace (EuclideanSpace ℂ I →L[ℂ] E) := borel _
local instance squareKrausBorel : BorelSpace (EuclideanSpace ℂ I →L[ℂ] E) := ⟨rfl⟩
local instance squareSourceMeasurable :
    MeasurableSpace (EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ I) := borel _
local instance squareSourceBorel :
    BorelSpace (EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ I) := ⟨rfl⟩
local instance squareMatrixMeasurable : MeasurableSpace (Matrix I I ℂ) := borel _
local instance squareMatrixBorel : BorelSpace (Matrix I I ℂ) := ⟨rfl⟩
local instance squareOperationMeasurable : MeasurableSpace (PhysicalOperation I E) := borel _
local instance squareOperationBorel : BorelSpace (PhysicalOperation I E) := ⟨rfl⟩

theorem measurable_positiveInputMatrix :
    Measurable (QuantumProver.ElegantJointMeasurement.HilbertPolar.positiveInputMatrix (I := I) (E := E)) := by
  have he (K : EuclideanSpace ℂ I →L[ℂ] E) :
      (QuantumProver.ElegantJointMeasurement.HilbertPolar.matrixOperator (I := I)).symm
        (QuantumProver.ElegantJointMeasurement.HilbertPolar.positiveInput K) = QuantumProver.ElegantJointMeasurement.HilbertPolar.positiveInputMatrix K := by
    rw [← QuantumProver.ElegantJointMeasurement.HilbertPolar.matrixOperator_positiveInputMatrix,
      (QuantumProver.ElegantJointMeasurement.HilbertPolar.matrixOperator (I := I)).symm_apply_apply]
  simpa only [Function.comp_def, he] using
    QuantumProver.ElegantJointMeasurement.HilbertPolar.continuous_matrixOperator_symm.measurable.comp
      (QuantumProver.ElegantJointMeasurement.HilbertPolar.measurable_positiveInput (I := I) (E := E))

variable [Nonempty I] [TopologicalSpace.SeparableSpace E]
variable {H Ω : Type*} [MeasurableSpace H] [MeasurableSpace Ω]
variable [MeasurableSpace.CountableOrCountablyGenerated H Ω]

theorem exists_physical_separable_probability_square_compilation_with_fallback
    (P : Instrument I E H Ω) (φ : E) (hφ : ∀ h : H, ‖φ‖ = 1) :
    ∃ W : H → Ω × ℕ → BlockSpace I E,
      Measurable (fun z : H × (Ω × ℕ) => unvectorize (W z.1 z.2)) ∧
      Measurable (fun z : H × (Ω × ℕ) =>
        QuantumProver.ElegantJointMeasurement.HilbertPolar.positiveInputMatrix (unvectorize (W z.1 z.2))) ∧
      Measurable (fun z : H × (Ω × ℕ) =>
        QuantumProver.ElegantJointMeasurement.HilbertRecovery.matrixRecovery φ (unvectorize (W z.1 z.2))) ∧
      (∀ h z, CompletelyPositive (operationOperator
        (QuantumProver.ElegantJointMeasurement.HilbertRecovery.matrixRecovery φ (unvectorize (W h z))).toLinearMap)) ∧
      (∀ h z X, QuantumProver.HilbertNuclearTrace.trace
        (QuantumProver.ElegantJointMeasurement.HilbertRecovery.matrixRecovery φ (unvectorize (W h z)) X) = Matrix.trace X) ∧
      (∀ h X, Integrable (fun z : Ω × ℕ =>
        QuantumProver.ElegantJointMeasurement.HilbertRecovery.matrixRecovery φ (unvectorize (W h z))
          (QuantumProver.ElegantJointMeasurement.HilbertPolar.positiveInputMatrix (unvectorize (W h z)) * X *
            star (QuantumProver.ElegantJointMeasurement.HilbertPolar.positiveInputMatrix (unvectorize (W h z)))))
        (fineProbabilityKernel P h)) ∧
      (∀ h (s : Set Ω), MeasurableSet s → ∀ X,
        (∫ z : Ω × ℕ,
          QuantumProver.ElegantJointMeasurement.HilbertRecovery.matrixRecovery φ (unvectorize (W h z))
            (QuantumProver.ElegantJointMeasurement.HilbertPolar.positiveInputMatrix (unvectorize (W h z)) * X *
              star (QuantumProver.ElegantJointMeasurement.HilbertPolar.positiveInputMatrix (unvectorize (W h z))))
          ∂((P.referenceKernel h).restrict s).prod labelProbability) = P.operation h s X) ∧
      (∀ h, Integrable (fun z : Ω × ℕ =>
        star (QuantumProver.ElegantJointMeasurement.HilbertPolar.positiveInputMatrix (unvectorize (W h z))) *
          QuantumProver.ElegantJointMeasurement.HilbertPolar.positiveInputMatrix (unvectorize (W h z)))
        (fineProbabilityKernel P h)) ∧
      (∀ h, (∫ z : Ω × ℕ,
        star (QuantumProver.ElegantJointMeasurement.HilbertPolar.positiveInputMatrix (unvectorize (W h z))) *
          QuantumProver.ElegantJointMeasurement.HilbertPolar.positiveInputMatrix (unvectorize (W h z))
        ∂fineProbabilityKernel P h) = (1 : Matrix I I ℂ)) := by
  obtain ⟨W, hstrong, hK, hAction, hSet, hGram, hComplete⟩ :=
    exists_physical_separable_probability_kraus_representation P
  refine ⟨W, hK, measurable_positiveInputMatrix.comp hK,
    (QuantumProver.ElegantJointMeasurement.HilbertRecovery.measurable_matrixRecovery φ).comp hK,
    (fun h z => QuantumProver.ElegantJointMeasurement.HilbertRecovery.matrixRecovery_completelyPositive φ _),
    (fun h z X => QuantumProver.ElegantJointMeasurement.HilbertRecovery.trace_matrixRecovery φ (hφ h) _ X), ?_, ?_, ?_, ?_⟩
  · intro h X
    simpa only [matrixRecovery_square_unvectorize] using hAction h X
  · intro h s hs X
    simpa only [matrixRecovery_square_unvectorize] using hSet h s hs X
  · intro h
    simpa only [squareMatrix_gram_unvectorize] using hGram h
  · intro h
    simpa only [squareMatrix_gram_unvectorize] using hComplete h

end QuantumProver.ElegantJointMeasurement.NormalInstrumentRealization

namespace QuantumProver.ElegantJointMeasurement.NormalInstrumentRealization

open QuantumProver.ElegantJointMeasurement.HilbertChoi QuantumProver.ElegantJointMeasurement.NuclearChoi QuantumProver.ElegantJointMeasurement.NormalCPInstruments
open QuantumProver.NuclearOperator (toOperator toOperator_injective)

variable {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {H Ω : Type*} [MeasurableSpace H] [MeasurableSpace Ω]

theorem exists_unit_output_of_history (P : Instrument I E H Ω) (h : H) :
    ∃ φ : E, ‖φ‖ = 1 := by
  have hE : Nontrivial E := by
    by_contra hn
    haveI : Subsingleton E := not_nontrivial_iff_subsingleton.mp hn
    have hz : P.operation h Set.univ (1 : Matrix I I ℂ) = 0 := by
      apply toOperator_injective
      ext x
      exact Subsingleton.elim _ _
    have ht := P.trace_preserving h (1 : Matrix I I ℂ)
    rw [hz, map_zero, Matrix.trace_one] at ht
    have hc : (0 : ℝ) = (Fintype.card I : ℝ) := by
      simpa only [Complex.zero_re, Complex.ofReal_re, Complex.natCast_re] using
        congrArg Complex.re ht
    exact (ne_of_gt (Nat.cast_pos.mpr Fintype.card_pos : (0 : ℝ) < Fintype.card I)) hc.symm
  haveI := hE
  obtain ⟨v, hv⟩ := exists_ne (0 : E)
  refine ⟨(‖v‖⁻¹ : ℝ) • v, ?_⟩
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg v))]
  exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)

theorem exists_history_unit_output (P : Instrument I E H Ω) :
    ∃ φ : E, ∀ h : H, ‖φ‖ = 1 := by
  by_cases hunit : ∃ φ : E, ‖φ‖ = 1
  · obtain ⟨φ, hφ⟩ := hunit
    exact ⟨φ, fun _ => hφ⟩
  · refine ⟨0, ?_⟩
    intro h
    exact False.elim (hunit (exists_unit_output_of_history P h))

end QuantumProver.ElegantJointMeasurement.NormalInstrumentRealization

namespace QuantumProver.ElegantJointMeasurement.NormalInstrumentRealization
open QuantumProver.ElegantJointMeasurement.HilbertChoi QuantumProver.ElegantJointMeasurement.NuclearChoi QuantumProver.ElegantJointMeasurement.NormalCPInstruments
open QuantumProver.ElegantJointMeasurement.NormalInstrumentKraus
variable {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [TopologicalSpace.SeparableSpace E]
variable {H Ω : Type*} [MeasurableSpace H] [MeasurableSpace Ω]
variable [MeasurableSpace.CountableOrCountablyGenerated H Ω]
local instance finalSquareKrausMeasurable : MeasurableSpace (EuclideanSpace ℂ I →L[ℂ] E) := borel _
local instance finalSquareKrausBorel : BorelSpace (EuclideanSpace ℂ I →L[ℂ] E) := ⟨rfl⟩
local instance finalSquareMatrixMeasurable : MeasurableSpace (Matrix I I ℂ) := borel _
local instance finalSquareMatrixBorel : BorelSpace (Matrix I I ℂ) := ⟨rfl⟩
local instance finalSquareOperationMeasurable : MeasurableSpace (PhysicalOperation I E) := borel _
local instance finalSquareOperationBorel : BorelSpace (PhysicalOperation I E) := ⟨rfl⟩

theorem exists_physical_separable_probability_square_compilation
    (P : Instrument I E H Ω) :
    ∃ φ : E,
    ∃ W : H → Ω × ℕ → BlockSpace I E,
      Measurable (fun z : H × (Ω × ℕ) => unvectorize (W z.1 z.2)) ∧
      Measurable (fun z : H × (Ω × ℕ) =>
        QuantumProver.ElegantJointMeasurement.HilbertPolar.positiveInputMatrix (unvectorize (W z.1 z.2))) ∧
      Measurable (fun z : H × (Ω × ℕ) =>
        QuantumProver.ElegantJointMeasurement.HilbertRecovery.matrixRecovery φ (unvectorize (W z.1 z.2))) ∧
      (∀ h z, CompletelyPositive (operationOperator
        (QuantumProver.ElegantJointMeasurement.HilbertRecovery.matrixRecovery φ (unvectorize (W h z))).toLinearMap)) ∧
      (∀ h z X, QuantumProver.HilbertNuclearTrace.trace
        (QuantumProver.ElegantJointMeasurement.HilbertRecovery.matrixRecovery φ (unvectorize (W h z)) X) = Matrix.trace X) ∧
      (∀ h X, Integrable (fun z : Ω × ℕ =>
        QuantumProver.ElegantJointMeasurement.HilbertRecovery.matrixRecovery φ (unvectorize (W h z))
          (QuantumProver.ElegantJointMeasurement.HilbertPolar.positiveInputMatrix (unvectorize (W h z)) * X *
            star (QuantumProver.ElegantJointMeasurement.HilbertPolar.positiveInputMatrix (unvectorize (W h z)))))
        (fineProbabilityKernel P h)) ∧
      (∀ h (s : Set Ω), MeasurableSet s → ∀ X,
        (∫ z : Ω × ℕ,
          QuantumProver.ElegantJointMeasurement.HilbertRecovery.matrixRecovery φ (unvectorize (W h z))
            (QuantumProver.ElegantJointMeasurement.HilbertPolar.positiveInputMatrix (unvectorize (W h z)) * X *
              star (QuantumProver.ElegantJointMeasurement.HilbertPolar.positiveInputMatrix (unvectorize (W h z))))
          ∂((P.referenceKernel h).restrict s).prod labelProbability) = P.operation h s X) ∧
      (∀ h, Integrable (fun z : Ω × ℕ =>
        star (QuantumProver.ElegantJointMeasurement.HilbertPolar.positiveInputMatrix (unvectorize (W h z))) *
          QuantumProver.ElegantJointMeasurement.HilbertPolar.positiveInputMatrix (unvectorize (W h z)))
        (fineProbabilityKernel P h)) ∧
      (∀ h, (∫ z : Ω × ℕ,
        star (QuantumProver.ElegantJointMeasurement.HilbertPolar.positiveInputMatrix (unvectorize (W h z))) *
          QuantumProver.ElegantJointMeasurement.HilbertPolar.positiveInputMatrix (unvectorize (W h z))
        ∂fineProbabilityKernel P h) = (1 : Matrix I I ℂ)) := by
  obtain ⟨φ, hφ⟩ := exists_history_unit_output P
  exact ⟨φ, exists_physical_separable_probability_square_compilation_with_fallback P φ hφ⟩

end QuantumProver.ElegantJointMeasurement.NormalInstrumentRealization

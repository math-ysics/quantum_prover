import QuantumProver.InformationTheory.ElegantJointMeasurement.NormalCPInstruments
import QuantumProver.InformationTheory.ElegantJointMeasurement.NormalNuclearDensity
import Mathlib.Probability.Distributions.Geometric

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000

open MeasureTheory ProbabilityTheory InnerProductSpace Filter
open scoped BigOperators InnerProduct ComplexOrder ENNReal Topology Matrix.Norms.L2Operator

namespace QuantumProver.ElegantJointMeasurement.NormalInstrumentKraus

open QuantumProver.ElegantJointMeasurement.HilbertChoi QuantumProver.ElegantJointMeasurement.NuclearChoi QuantumProver.ElegantJointMeasurement.NormalCPInstruments

variable {I : Type} [Fintype I] [DecidableEq I]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

def nuclearDecode (X : Matrix I I ℂ) : Nuclear (BlockSpace I E) →L[ℂ] Nuclear E :=
  ∑ i, ∑ j, X i j • QuantumProver.HilbertNuclearCompression.compose
    (PiLp.proj 2 (fun _ : I => E) i) (QuantumProver.ElegantJointMeasurement.HilbertChoi.insert (E := E) j)

theorem toOperator_nuclearDecode (X : Matrix I I ℂ) (A : Nuclear (BlockSpace I E)) :
    QuantumProver.NuclearOperator.toOperator (nuclearDecode X A) =
      decode X (QuantumProver.NuclearOperator.toOperator A) := by
  simp only [nuclearDecode, sum_apply, smul_apply,
    map_sum, map_smul, QuantumProver.HilbertNuclearCompression.toOperator_compose,
    decode, blockMap_apply]

theorem nuclearDecode_nuclearChoi (Φ : PhysicalOperation I E) (X : Matrix I I ℂ) :
    nuclearDecode X (nuclearChoi Φ) = Φ X := by
  apply QuantumProver.NuclearOperator.toOperator_injective
  rw [toOperator_nuclearDecode, toOperator_nuclearChoi, decode_choi]
  rfl

variable {H Ω : Type*} [MeasurableSpace H] [MeasurableSpace Ω]

theorem nuclearDecode_physicalChoi (P : Instrument I E H Ω)
    (h : H) (s : Set Ω) (X : Matrix I I ℂ) :
    nuclearDecode X (P.physicalChoi h s) = P.operation h s X :=
  nuclearDecode_nuclearChoi _ X

variable {L : Type*}

theorem summable_nuclear_diagonal (b : HilbertBasis L ℂ (BlockSpace I E))
    (A : Nuclear (BlockSpace I E)) :
    Summable (fun l =>
      (inner ℂ (QuantumProver.NuclearOperator.toOperator A (b l)) (b l)).re) := by
  have hs := ((QuantumProver.HilbertNuclearTrace.hasSum_diagonal b A).mapL Complex.reCLM).summable
  convert hs using 1
  funext l
  exact inner_re_symm (𝕜 := ℂ) _ _

theorem positiveNuclearColumns_hasSum (b : HilbertBasis L ℂ (BlockSpace I E))
    (A : Nuclear (BlockSpace I E)) (hA : (QuantumProver.NuclearOperator.toOperator A).IsPositive) :
    HasSum (nuclearColumn b (QuantumProver.NuclearOperator.toOperator A)) A := by
  have hs := nuclearColumns_hasSum b (QuantumProver.NuclearOperator.toOperator A) hA
    (summable_nuclear_diagonal b A)
  rw [positiveLift_eq_of_toOperator b _ hA (summable_nuclear_diagonal b A) A rfl] at hs
  exact hs

@[simp] theorem nuclearDecode_nuclearColumn
    (b : HilbertBasis L ℂ (BlockSpace I E)) (D : BlockSpace I E →L[ℂ] BlockSpace I E)
    (l : L) (X : Matrix I I ℂ) :
    nuclearDecode X (nuclearColumn b D l) = nuclearKrausAction (squareRootColumn b D l) X := by
  apply QuantumProver.NuclearOperator.toOperator_injective
  rw [toOperator_nuclearDecode, toOperator_nuclearColumn, decode_rankOne,
    toOperator_nuclearKrausAction]

def columnAction (b : HilbertBasis L ℂ (BlockSpace I E))
    (A : Nuclear (BlockSpace I E)) (l : L) (X : Matrix I I ℂ) : Nuclear E :=
  nuclearKrausAction (squareRootColumn b (QuantumProver.NuclearOperator.toOperator A) l) X

theorem columnAction_hasSum (b : HilbertBasis L ℂ (BlockSpace I E))
    (A : Nuclear (BlockSpace I E)) (hA : (QuantumProver.NuclearOperator.toOperator A).IsPositive)
    (X : Matrix I I ℂ) :
    HasSum (fun l => columnAction b A l X) (nuclearDecode X A) := by
  simpa only [nuclearDecode_nuclearColumn, columnAction] using
    (nuclearDecode X).hasSum (positiveNuclearColumns_hasSum b A hA)

theorem columnAction_summable_norm (b : HilbertBasis L ℂ (BlockSpace I E))
    (A : Nuclear (BlockSpace I E)) (hA : (QuantumProver.NuclearOperator.toOperator A).IsPositive)
    (X : Matrix I I ℂ) : Summable (fun l => ‖columnAction b A l X‖) := by
  have hm := (summable_nuclear_diagonal b A).mul_left (inputEntryMass X)
  refine Summable.of_nonneg_of_le (fun l => norm_nonneg _) (fun l => ?_) hm
  simpa only [columnAction, squareRootColumn_norm_sq b _ hA] using
    norm_nuclearKrausAction_le (squareRootColumn b (QuantumProver.NuclearOperator.toOperator A) l) X

local instance nuclearMeasurable : MeasurableSpace (Nuclear E) := borel (Nuclear E)
local instance nuclearBorel : BorelSpace (Nuclear E) := ⟨rfl⟩
local instance blockMeasurable : MeasurableSpace (BlockSpace I E) := borel (BlockSpace I E)
local instance blockBorel : BorelSpace (BlockSpace I E) := ⟨rfl⟩
local instance operatorMeasurable : MeasurableSpace (E →L[ℂ] E) := borel (E →L[ℂ] E)
local instance operatorBorel : BorelSpace (E →L[ℂ] E) := ⟨rfl⟩

variable {P : Type*} [MeasurableSpace P]

theorem measurable_columnAction (b : HilbertBasis L ℂ (BlockSpace I E))
    (D : P → Nuclear (BlockSpace I E)) (hD : Measurable D) (l : L) (X : Matrix I I ℂ) :
    Measurable (fun p => columnAction b (D p) l X) := by
  have ho : Measurable (fun p => QuantumProver.NuclearOperator.toOperator (D p)) :=
    (QuantumProver.NuclearOperator.toOperator (𝕜 := ℂ) (E := BlockSpace I E)
      (F := BlockSpace I E)).continuous.measurable.comp hD
  exact measurable_nuclearKrausColumnAction b _ ho l X

end QuantumProver.ElegantJointMeasurement.NormalInstrumentKraus

namespace QuantumProver.ElegantJointMeasurement.NormalInstrumentKraus

open QuantumProver.ElegantJointMeasurement.HilbertChoi QuantumProver.ElegantJointMeasurement.NuclearChoi QuantumProver.ElegantJointMeasurement.NormalCPInstruments

variable {I : Type} [Fintype I] [DecidableEq I]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {L : Type*}

def canonicalKraus (b : HilbertBasis L ℂ (BlockSpace I E))
    (A : Nuclear (BlockSpace I E)) (l : L) : EuclideanSpace ℂ I →L[ℂ] E :=
  unvectorize (squareRootColumn b (QuantumProver.NuclearOperator.toOperator A) l)

theorem toOperator_columnAction (b : HilbertBasis L ℂ (BlockSpace I E))
    (A : Nuclear (BlockSpace I E)) (l : L) (X : Matrix I I ℂ) :
    QuantumProver.NuclearOperator.toOperator (columnAction b A l X) =
      canonicalKraus b A l ∘L matrixOperator X ∘L (canonicalKraus b A l).adjoint := by
  rw [columnAction, toOperator_nuclearKrausAction]
  rfl

theorem nuclearDecode_matrixUnit (i j : I) (A : Nuclear (BlockSpace I E)) :
    nuclearDecode (matrixUnit i j) A = QuantumProver.HilbertNuclearCompression.compose
      (PiLp.proj 2 (fun _ : I => E) i) (QuantumProver.ElegantJointMeasurement.HilbertChoi.insert (E := E) j) A := by
  let S (p q : I) : Nuclear (BlockSpace I E) →L[ℂ] Nuclear E :=
    QuantumProver.HilbertNuclearCompression.compose (PiLp.proj 2 (fun _ : I => E) p)
      (QuantumProver.ElegantJointMeasurement.HilbertChoi.insert (E := E) q)
  have heq : nuclearDecode (E := E) (matrixUnit i j) = S i j := by
    change (∑ p, ∑ q, (if i = p ∧ j = q then (1 : ℂ) else 0) • S p q) = S i j
    have hz (p q : I) : (0 : ℂ) • S p q = 0 := by
      ext T
      simp only [smul_apply, zero_smul, ContinuousLinearMap.zero_apply]
    simp only [ite_smul, one_smul, hz, ite_and]
    simp
  exact congrArg (fun T : Nuclear (BlockSpace I E) →L[ℂ] Nuclear E => T A) heq

def inputGramEntry (i j : I) : Nuclear (BlockSpace I E) →L[ℂ] ℂ :=
  (QuantumProver.HilbertNuclearTrace.trace (𝕜 := ℂ) (E := E)).comp
    (QuantumProver.HilbertNuclearCompression.compose (PiLp.proj 2 (fun _ : I => E) j)
      (QuantumProver.ElegantJointMeasurement.HilbertChoi.insert (E := E) i))

def inputGram : Nuclear (BlockSpace I E) →L[ℂ] Matrix I I ℂ where
  toFun A i j := inputGramEntry i j A
  map_add' A B := by ext i j; exact (inputGramEntry i j).map_add A B
  map_smul' c A := by ext i j; exact (inputGramEntry i j).map_smul c A
  cont := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    exact (inputGramEntry i j).continuous

theorem inputGram_nuclearColumn (b : HilbertBasis L ℂ (BlockSpace I E))
    (D : BlockSpace I E →L[ℂ] BlockSpace I E) (l : L) :
    inputGram (nuclearColumn b D l) =
      Matrix.gram ℂ (fun i : I => squareRootColumn b D l i) := by
  ext i j
  change QuantumProver.HilbertNuclearTrace.trace
    (QuantumProver.HilbertNuclearCompression.compose (PiLp.proj 2 (fun _ : I => E) j)
      (QuantumProver.ElegantJointMeasurement.HilbertChoi.insert (E := E) i)
      (QuantumProver.NuclearOperator.rankOne (innerSL ℂ (squareRootColumn b D l))
        (squareRootColumn b D l))) = _
  rw [QuantumProver.HilbertNuclearCompression.compose_rankOne,
    QuantumProver.HilbertNuclearTrace.trace_rankOne]
  simp [ContinuousLinearMap.comp_apply, PiLp.inner_apply,
    QuantumProver.ElegantJointMeasurement.HilbertChoi.insert_apply_apply, Matrix.gram_apply]
  simp_rw [apply_ite]
  simp

def columnGram (b : HilbertBasis L ℂ (BlockSpace I E))
    (A : Nuclear (BlockSpace I E)) (l : L) : Matrix I I ℂ :=
  Matrix.gram ℂ (fun i : I => squareRootColumn b (QuantumProver.NuclearOperator.toOperator A) l i)

theorem matrixOperator_columnGram (b : HilbertBasis L ℂ (BlockSpace I E))
    (A : Nuclear (BlockSpace I E)) (l : L) :
    matrixOperator (columnGram b A l) =
      (canonicalKraus b A l).adjoint ∘L canonicalKraus b A l := by
  ext x i
  simp only [matrixOperator_apply, columnGram, Matrix.gram_apply,
    ContinuousLinearMap.comp_apply, canonicalKraus, unvectorize_adjoint_apply,
    unvectorize_apply, inner_sum, inner_smul_right]
  exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)

theorem columnGram_hasSum (b : HilbertBasis L ℂ (BlockSpace I E))
    (A : Nuclear (BlockSpace I E)) (hA : (QuantumProver.NuclearOperator.toOperator A).IsPositive) :
    HasSum (columnGram b A) (inputGram A) := by
  change HasSum (fun l => Matrix.gram ℂ
    (fun i : I => squareRootColumn b (QuantumProver.NuclearOperator.toOperator A) l i)) (inputGram A)
  simpa only [inputGram_nuclearColumn] using
    (inputGram (I := I) (E := E)).hasSum (positiveNuclearColumns_hasSum b A hA)

variable {H Ω : Type*} [MeasurableSpace H] [MeasurableSpace Ω]

theorem inputGram_physicalChoi_univ (P : Instrument I E H Ω) (h : H) :
    inputGram (P.physicalChoi h Set.univ) = (1 : Matrix I I ℂ) := by
  ext i j
  change QuantumProver.HilbertNuclearTrace.trace
    (QuantumProver.HilbertNuclearCompression.compose (PiLp.proj 2 (fun _ : I => E) j)
      (QuantumProver.ElegantJointMeasurement.HilbertChoi.insert (E := E) i) (P.physicalChoi h Set.univ)) = _
  rw [← nuclearDecode_matrixUnit, nuclearDecode_physicalChoi, P.trace_preserving]
  by_cases hij : i = j
  · subst j
    simp [matrixUnit]
  · simp only [matrixUnit, Matrix.one_apply, if_neg hij]
    exact Matrix.trace_single_eq_of_ne j i (1 : ℂ) (Ne.symm hij)

local instance nuclearMeasurable2 : MeasurableSpace (Nuclear E) := borel (Nuclear E)
local instance nuclearBorel2 : BorelSpace (Nuclear E) := ⟨rfl⟩
local instance blockMeasurable2 : MeasurableSpace (BlockSpace I E) := borel (BlockSpace I E)
local instance blockBorel2 : BorelSpace (BlockSpace I E) := ⟨rfl⟩
local instance blockOperatorMeasurable2 :
    MeasurableSpace (BlockSpace I E →L[ℂ] BlockSpace I E) := borel _
local instance blockOperatorBorel2 :
    BorelSpace (BlockSpace I E →L[ℂ] BlockSpace I E) := ⟨rfl⟩
local instance krausMeasurable : MeasurableSpace (EuclideanSpace ℂ I →L[ℂ] E) := borel _
local instance krausBorel : BorelSpace (EuclideanSpace ℂ I →L[ℂ] E) := ⟨rfl⟩

variable {P : Type*} [MeasurableSpace P]

theorem measurable_canonicalKraus (b : HilbertBasis L ℂ (BlockSpace I E))
    (D : P → Nuclear (BlockSpace I E)) (hD : Measurable D) (l : L) :
    Measurable (fun p => canonicalKraus b (D p) l) := by
  have ho : Measurable (fun p => QuantumProver.NuclearOperator.toOperator (D p)) :=
    (QuantumProver.NuclearOperator.toOperator (𝕜 := ℂ) (E := BlockSpace I E)
      (F := BlockSpace I E)).continuous.measurable.comp hD
  exact measurable_krausColumn b _ ho l

variable [Nonempty I] [MeasurableSpace.CountableOrCountablyGenerated H Ω]

theorem exists_physical_canonical_kraus_representation
    (P : Instrument I E H Ω) (b : HilbertBasis ℕ ℂ (BlockSpace I E)) :
    ∃ D : H → Ω → Nuclear (BlockSpace I E),
      Measurable (fun z : H × Ω => D z.1 z.2) ∧
      (∀ h ω, (QuantumProver.NuclearOperator.toOperator (D h ω)).IsPositive) ∧
      (∀ l, Measurable (fun z : H × Ω => canonicalKraus b (D z.1 z.2) l)) ∧
      (∀ l X, Measurable (fun z : H × Ω => columnAction b (D z.1 z.2) l X)) ∧
      (∀ h ω X, HasSum (fun l => columnAction b (D h ω) l X) (nuclearDecode X (D h ω))) ∧
      (∀ h ω X, Summable (fun l => ‖columnAction b (D h ω) l X‖)) ∧
      (∀ h X, Integrable (fun ω => ∑' l, columnAction b (D h ω) l X) (P.referenceKernel h)) ∧
      (∀ h (s : Set Ω), MeasurableSet s → ∀ X,
        (∫ ω in s, ∑' l, columnAction b (D h ω) l X ∂P.referenceKernel h) = P.operation h s X) ∧
      (∀ h, (∫ ω, ∑' l, columnGram b (D h ω) l ∂P.referenceKernel h) = (1 : Matrix I I ℂ)) := by
  obtain ⟨D, hstrong, hmeas, hpos, htrace, hbound, hmass, hint, hset⟩ :=
    QuantumProver.ElegantJointMeasurement.NormalNuclearDensity.exists_physical_positive_nuclear_density P b
  have hseries (h : H) (X : Matrix I I ℂ) :
      (fun ω => ∑' l, columnAction b (D h ω) l X) = fun ω => nuclearDecode X (D h ω) :=
    funext (fun ω => (columnAction_hasSum b (D h ω) (hpos h ω) X).tsum_eq)
  have hgram (h : H) : (fun ω => ∑' l, columnGram b (D h ω) l) =
      fun ω => inputGram (D h ω) :=
    funext (fun ω => (columnGram_hasSum b (D h ω) (hpos h ω)).tsum_eq)
  refine ⟨D, hmeas, hpos, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro l
    exact measurable_canonicalKraus b (fun z : H × Ω => D z.1 z.2) hmeas l
  · intro l X
    exact measurable_columnAction b (fun z : H × Ω => D z.1 z.2) hmeas l X
  · intro h ω X
    exact columnAction_hasSum b (D h ω) (hpos h ω) X
  · intro h ω X
    exact columnAction_summable_norm b (D h ω) (hpos h ω) X
  · intro h X
    rw [hseries h X]
    let DX : Nuclear (BlockSpace I E) →L[ℂ] Nuclear E := nuclearDecode (E := E) X
    exact DX.integrable_comp (hint h)
  · intro h s hs X
    rw [hseries h X]
    let DX : Nuclear (BlockSpace I E) →L[ℂ] Nuclear E := nuclearDecode (E := E) X
    change (∫ ω in s, DX (D h ω) ∂P.referenceKernel h) = _
    rw [DX.integral_comp_comm (hint h).integrableOn, hset h s hs]
    exact nuclearDecode_physicalChoi P h s X
  · intro h
    rw [hgram h]
    let G : Nuclear (BlockSpace I E) →L[ℂ] Matrix I I ℂ := inputGram (I := I) (E := E)
    change (∫ ω, G (D h ω) ∂P.referenceKernel h) = _
    rw [G.integral_comp_comm (hint h)]
    have hu : (∫ ω, D h ω ∂P.referenceKernel h) = P.physicalChoi h Set.univ := by
      simpa only [Measure.restrict_univ] using hset h Set.univ MeasurableSet.univ
    rw [hu]
    exact inputGram_physicalChoi_univ P h

end QuantumProver.ElegantJointMeasurement.NormalInstrumentKraus

namespace QuantumProver.ElegantJointMeasurement.NormalInstrumentKraus

open QuantumProver.ElegantJointMeasurement.HilbertChoi QuantumProver.ElegantJointMeasurement.NuclearChoi QuantumProver.ElegantJointMeasurement.NormalCPInstruments TopologicalSpace

variable {I : Type} [Fintype I] [DecidableEq I]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem secondCountable_block_of_basis (b : HilbertBasis ℕ ℂ (BlockSpace I E)) :
    SecondCountableTopology (BlockSpace I E) := by
  have hs : IsSeparable (closure (Submodule.span ℂ (Set.range b) : Set (BlockSpace I E))) :=
    ((Set.countable_range b).isSeparable.span (R := ℂ)).closure
  have hc : closure (Submodule.span ℂ (Set.range b) : Set (BlockSpace I E)) = Set.univ := by
    rw [← Submodule.topologicalClosure_coe, b.dense_span, Submodule.top_coe]
  haveI : SeparableSpace (BlockSpace I E) := isSeparable_univ_iff.mp (hc ▸ hs)
  infer_instance

theorem nuclearColumn_norm_hasSum (b : HilbertBasis ℕ ℂ (BlockSpace I E))
    (A : Nuclear (BlockSpace I E)) (hA : (QuantumProver.NuclearOperator.toOperator A).IsPositive) :
    HasSum (fun l => ‖nuclearColumn b (QuantumProver.NuclearOperator.toOperator A) l‖) ‖A‖ := by
  have hd := (QuantumProver.HilbertNuclearTrace.hasSum_diagonal b A).mapL Complex.reCLM
  change HasSum (fun l => (inner ℂ (b l) (QuantumProver.NuclearOperator.toOperator A (b l))).re)
    (QuantumProver.HilbertNuclearTrace.trace A).re at hd
  rw [← norm_positive_nuclear_eq_re_trace b A hA] at hd
  convert hd using 1
  funext l
  rw [norm_nuclearColumn b _ hA]
  exact inner_re_symm (𝕜 := ℂ) _ _

local instance nuclearMeasurableFine : MeasurableSpace (Nuclear E) := borel (Nuclear E)
local instance nuclearBorelFine : BorelSpace (Nuclear E) := ⟨rfl⟩
local instance blockMeasurableFine : MeasurableSpace (BlockSpace I E) := borel (BlockSpace I E)
local instance blockBorelFine : BorelSpace (BlockSpace I E) := ⟨rfl⟩
local instance blockOperatorMeasurableFine :
    MeasurableSpace (BlockSpace I E →L[ℂ] BlockSpace I E) := borel _
local instance blockOperatorBorelFine :
    BorelSpace (BlockSpace I E →L[ℂ] BlockSpace I E) := ⟨rfl⟩

variable {P : Type*} [MeasurableSpace P]

theorem stronglyMeasurable_nuclearColumn (b : HilbertBasis ℕ ℂ (BlockSpace I E))
    (D : P → Nuclear (BlockSpace I E)) (hD : Measurable D) (l : ℕ) :
    StronglyMeasurable (fun p => nuclearColumn b (QuantumProver.NuclearOperator.toOperator (D p)) l) := by
  haveI : SecondCountableTopology (BlockSpace I E) := secondCountable_block_of_basis b
  have ho : Measurable (fun p => QuantumProver.NuclearOperator.toOperator (D p)) :=
    (QuantumProver.NuclearOperator.toOperator (𝕜 := ℂ) (E := BlockSpace I E)
      (F := BlockSpace I E)).continuous.measurable.comp hD
  exact continuous_nuclearPositiveRankOne.comp_stronglyMeasurable
    (measurable_squareRootColumn b _ ho l).stronglyMeasurable

def fineNuclearColumn (b : HilbertBasis ℕ ℂ (BlockSpace I E))
    (D : P → Nuclear (BlockSpace I E)) (z : P × ℕ) : Nuclear (BlockSpace I E) :=
  nuclearColumn b (QuantumProver.NuclearOperator.toOperator (D z.1)) z.2

theorem stronglyMeasurable_fineNuclearColumn (b : HilbertBasis ℕ ℂ (BlockSpace I E))
    (D : P → Nuclear (BlockSpace I E)) (hD : Measurable D) :
    StronglyMeasurable (fineNuclearColumn b D) := by
  apply stronglyMeasurable_iff_measurable_separable.mpr
  constructor
  · exact measurable_from_prod_countable_left
      (fun l => (stronglyMeasurable_nuclearColumn b D hD l).measurable)
  · have heq : Set.range (fineNuclearColumn b D) =
        ⋃ l : ℕ, Set.range (fun p => nuclearColumn b (QuantumProver.NuclearOperator.toOperator (D p)) l) := by
      ext A
      simp only [Set.mem_range, Set.mem_iUnion]
      constructor
      · rintro ⟨⟨p,l⟩, rfl⟩
        exact ⟨l,p,rfl⟩
      · rintro ⟨l,p,rfl⟩
        exact ⟨(p,l),rfl⟩
    rw [heq]
    exact IsSeparable.iUnion (fun l =>
      (stronglyMeasurable_nuclearColumn b D hD l).isSeparable_range)

theorem integral_count_nuclearColumn_norm (b : HilbertBasis ℕ ℂ (BlockSpace I E))
    (A : Nuclear (BlockSpace I E)) (hA : (QuantumProver.NuclearOperator.toOperator A).IsPositive) :
    (∫ l, ‖nuclearColumn b (QuantumProver.NuclearOperator.toOperator A) l‖ ∂Measure.count) = ‖A‖ := by
  have hc : Integrable (nuclearColumn b (QuantumProver.NuclearOperator.toOperator A)) Measure.count :=
    integrable_count_iff.mpr (nuclearColumn_norm_hasSum b A hA).summable
  rw [integral_countable hc.norm]
  simpa only [measureReal_def, Measure.count_singleton, ENNReal.toReal_one, one_smul] using
    (nuclearColumn_norm_hasSum b A hA).tsum_eq

theorem integrable_fineNuclearColumn (b : HilbertBasis ℕ ℂ (BlockSpace I E))
    (D : P → Nuclear (BlockSpace I E)) (hD : Measurable D)
    (hpos : ∀ p, (QuantumProver.NuclearOperator.toOperator (D p)).IsPositive)
    (μ : Measure P) (hint : Integrable D μ) :
    Integrable (fineNuclearColumn b D) (μ.prod Measure.count) := by
  apply (integrable_prod_iff (stronglyMeasurable_fineNuclearColumn b D hD).aestronglyMeasurable).mpr
  constructor
  · exact Filter.Eventually.of_forall (fun p =>
      integrable_count_iff.mpr (nuclearColumn_norm_hasSum b (D p) (hpos p)).summable)
  · have heq : (fun p => ∫ l, ‖fineNuclearColumn b D (p,l)‖ ∂Measure.count) = fun p => ‖D p‖ :=
      funext (fun p => integral_count_nuclearColumn_norm b (D p) (hpos p))
    rw [heq]
    exact hint.norm

theorem integral_count_nuclearColumn (b : HilbertBasis ℕ ℂ (BlockSpace I E))
    (A : Nuclear (BlockSpace I E)) (hA : (QuantumProver.NuclearOperator.toOperator A).IsPositive) :
    (∫ l, nuclearColumn b (QuantumProver.NuclearOperator.toOperator A) l ∂Measure.count) = A := by
  have hc : Integrable (nuclearColumn b (QuantumProver.NuclearOperator.toOperator A)) Measure.count :=
    integrable_count_iff.mpr (nuclearColumn_norm_hasSum b A hA).summable
  rw [integral_countable hc]
  simpa only [measureReal_def, Measure.count_singleton, ENNReal.toReal_one, one_smul] using
    (positiveNuclearColumns_hasSum b A hA).tsum_eq

theorem integral_fineNuclearColumn (b : HilbertBasis ℕ ℂ (BlockSpace I E))
    (D : P → Nuclear (BlockSpace I E)) (hD : Measurable D)
    (hpos : ∀ p, (QuantumProver.NuclearOperator.toOperator (D p)).IsPositive)
    (μ : Measure P) [SFinite μ] (hint : Integrable D μ) :
    (∫ z, fineNuclearColumn b D z ∂(μ.prod Measure.count)) = ∫ p, D p ∂μ := by
  rw [integral_prod _ (integrable_fineNuclearColumn b D hD hpos μ hint)]
  congr 1
  funext p
  exact integral_count_nuclearColumn b (D p) (hpos p)

end QuantumProver.ElegantJointMeasurement.NormalInstrumentKraus

namespace QuantumProver.ElegantJointMeasurement.NormalInstrumentKraus

open QuantumProver.ElegantJointMeasurement.HilbertChoi QuantumProver.ElegantJointMeasurement.NuclearChoi QuantumProver.ElegantJointMeasurement.NormalCPInstruments

variable {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {H Ω : Type*} [MeasurableSpace H] [MeasurableSpace Ω]
variable [MeasurableSpace.CountableOrCountablyGenerated H Ω]

local instance nuclearMeasurableMatrixFine : MeasurableSpace (Nuclear E) := borel (Nuclear E)
local instance nuclearBorelMatrixFine : BorelSpace (Nuclear E) := ⟨rfl⟩
local instance blockMeasurableMatrixFine : MeasurableSpace (BlockSpace I E) := borel (BlockSpace I E)
local instance blockBorelMatrixFine : BorelSpace (BlockSpace I E) := ⟨rfl⟩
local instance blockOperatorMeasurableMatrixFine :
    MeasurableSpace (BlockSpace I E →L[ℂ] BlockSpace I E) := borel _
local instance blockOperatorBorelMatrixFine :
    BorelSpace (BlockSpace I E →L[ℂ] BlockSpace I E) := ⟨rfl⟩
local instance krausMeasurableMatrixFine : MeasurableSpace (EuclideanSpace ℂ I →L[ℂ] E) := borel _
local instance krausBorelMatrixFine : BorelSpace (EuclideanSpace ℂ I →L[ℂ] E) := ⟨rfl⟩

theorem exists_physical_fine_record_kraus_representation
    (P : Instrument I E H Ω) (b : HilbertBasis ℕ ℂ (BlockSpace I E)) :
    ∃ D : H → Ω → Nuclear (BlockSpace I E),
      Measurable (fun z : H × Ω => D z.1 z.2) ∧
      (∀ h ω, (QuantumProver.NuclearOperator.toOperator (D h ω)).IsPositive) ∧
      Measurable (fun z : H × (Ω × ℕ) => canonicalKraus b (D z.1 z.2.1) z.2.2) ∧
      (∀ h X, Integrable (fun z : Ω × ℕ => columnAction b (D h z.1) z.2 X)
        ((P.referenceKernel h).prod Measure.count)) ∧
      (∀ h (s : Set Ω), MeasurableSet s → ∀ X,
        (∫ z : Ω × ℕ, columnAction b (D h z.1) z.2 X
          ∂((P.referenceKernel h).restrict s).prod Measure.count) = P.operation h s X) ∧
      (∀ h, Integrable (fun z : Ω × ℕ => columnGram b (D h z.1) z.2)
        ((P.referenceKernel h).prod Measure.count)) ∧
      (∀ h, (∫ z : Ω × ℕ, columnGram b (D h z.1) z.2
        ∂(P.referenceKernel h).prod Measure.count) = (1 : Matrix I I ℂ)) := by
  obtain ⟨D, hstrong, hmeas, hpos, htrace, hbound, hmass, hint, hset⟩ :=
    QuantumProver.ElegantJointMeasurement.NormalNuclearDensity.exists_physical_positive_nuclear_density P b
  have hd (h : H) : Measurable (D h) :=
    hmeas.comp (measurable_const.prodMk measurable_id)
  refine ⟨D, hmeas, hpos, ?_, ?_, ?_, ?_, ?_⟩
  · have hm : Measurable (fun z : (H × Ω) × ℕ => canonicalKraus b (D z.1.1 z.1.2) z.2) :=
      measurable_from_prod_countable_left (fun l =>
        measurable_canonicalKraus b (fun z : H × Ω => D z.1 z.2) hmeas l)
    have hA : Measurable (fun z : H × (Ω × ℕ) => ((z.1,z.2.1),z.2.2)) :=
      (measurable_fst.prodMk (measurable_fst.comp measurable_snd)).prodMk
        (measurable_snd.comp measurable_snd)
    simpa only [Function.comp_def] using hm.comp hA
  · intro h X
    let DX : Nuclear (BlockSpace I E) →L[ℂ] Nuclear E := nuclearDecode (E := E) X
    have hf := integrable_fineNuclearColumn b (D h) (hd h) (hpos h) (P.referenceKernel h) (hint h)
    simpa only [DX, fineNuclearColumn, nuclearDecode_nuclearColumn, columnAction] using
      DX.integrable_comp hf
  · intro h s hs X
    let DX : Nuclear (BlockSpace I E) →L[ℂ] Nuclear E := nuclearDecode (E := E) X
    have hf := integrable_fineNuclearColumn b (D h) (hd h) (hpos h)
      ((P.referenceKernel h).restrict s) (hint h).integrableOn
    calc
      (∫ z : Ω × ℕ, columnAction b (D h z.1) z.2 X
          ∂((P.referenceKernel h).restrict s).prod Measure.count) =
          DX (∫ z, fineNuclearColumn b (D h) z
            ∂((P.referenceKernel h).restrict s).prod Measure.count) := by
        simpa only [DX, fineNuclearColumn, nuclearDecode_nuclearColumn, columnAction] using
          DX.integral_comp_comm hf
      _ = DX (∫ ω in s, D h ω ∂P.referenceKernel h) := by
        rw [integral_fineNuclearColumn b (D h) (hd h) (hpos h)
          ((P.referenceKernel h).restrict s) (hint h).integrableOn]
      _ = P.operation h s X := by
        rw [hset h s hs]
        exact nuclearDecode_physicalChoi P h s X
  · intro h
    let G : Nuclear (BlockSpace I E) →L[ℂ] Matrix I I ℂ := inputGram (I := I) (E := E)
    have hf := integrable_fineNuclearColumn b (D h) (hd h) (hpos h) (P.referenceKernel h) (hint h)
    simpa only [G, fineNuclearColumn, inputGram_nuclearColumn, columnGram] using
      G.integrable_comp hf
  · intro h
    let G : Nuclear (BlockSpace I E) →L[ℂ] Matrix I I ℂ := inputGram (I := I) (E := E)
    have hf := integrable_fineNuclearColumn b (D h) (hd h) (hpos h) (P.referenceKernel h) (hint h)
    have hG : (∫ z : Ω × ℕ, columnGram b (D h z.1) z.2 ∂(P.referenceKernel h).prod Measure.count) =
        G (∫ z, fineNuclearColumn b (D h) z ∂(P.referenceKernel h).prod Measure.count) := by
      simpa only [G, fineNuclearColumn, inputGram_nuclearColumn, columnGram] using
        G.integral_comp_comm hf
    rw [hG, integral_fineNuclearColumn b (D h) (hd h) (hpos h) (P.referenceKernel h) (hint h)]
    have hu : (∫ ω, D h ω ∂P.referenceKernel h) = P.physicalChoi h Set.univ := by
      simpa only [Measure.restrict_univ] using hset h Set.univ MeasurableSet.univ
    rw [hu]
    exact inputGram_physicalChoi_univ P h

end QuantumProver.ElegantJointMeasurement.NormalInstrumentKraus

namespace QuantumProver.ElegantJointMeasurement.NormalInstrumentKraus

def labelParameter : unitInterval := ⟨(1/2 : ℝ), by constructor <;> norm_num⟩

theorem labelParameter_ne_zero : labelParameter ≠ 0 := by
  intro h
  have he := congrArg (fun x : unitInterval => (x : ℝ)) h
  norm_num [labelParameter] at he

theorem labelParameter_ne_one : labelParameter ≠ 1 := by
  intro h
  have he := congrArg (fun x : unitInterval => (x : ℝ)) h
  norm_num [labelParameter] at he

def labelWeight (l : ℕ) : ℝ := (1 - (labelParameter : ℝ)) ^ l * labelParameter

theorem labelWeight_pos (l : ℕ) : 0 < labelWeight l :=
  ProbabilityTheory.geometricMeasure_pos labelParameter_ne_zero labelParameter_ne_one l

def labelProbability : Measure ℕ := ProbabilityTheory.geometricMeasure labelParameter

instance isProbabilityMeasure_labelProbability : IsProbabilityMeasure labelProbability :=
  ProbabilityTheory.isProbabilityMeasure_geometricMeasure

def normalizeCountField {P B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
    (f : P × ℕ → B) (z : P × ℕ) : B := (labelWeight z.2)⁻¹ • f z

section LabelTransport

variable {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]

theorem labelWeight_norm_inv_smul (l : ℕ) (x : B) :
    labelWeight l * ‖(labelWeight l)⁻¹ • x‖ = ‖x‖ := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (labelWeight_pos l)),
    ← mul_assoc, mul_inv_cancel₀ (ne_of_gt (labelWeight_pos l)), one_mul]

theorem integrable_label_inv_smul (f : ℕ → B)
    (hf : Integrable f Measure.count) :
    Integrable (fun l => (labelWeight l)⁻¹ • f l) labelProbability := by
  apply (ProbabilityTheory.integrable_geometricMeasure_iff labelParameter_ne_zero).mpr
  change Summable (fun l => labelWeight l * ‖(labelWeight l)⁻¹ • f l‖)
  simpa only [labelWeight_norm_inv_smul] using integrable_count_iff.mp hf

theorem integral_label_inv_smul [CompleteSpace B] (f : ℕ → B)
    (hf : Integrable f Measure.count) :
    (∫ l, (labelWeight l)⁻¹ • f l ∂labelProbability) = ∫ l, f l ∂Measure.count := by
  change (∫ l, (labelWeight l)⁻¹ • f l ∂ProbabilityTheory.geometricMeasure labelParameter) = _
  rw [ProbabilityTheory.integral_geometricMeasure' labelParameter_ne_zero
    (integrable_label_inv_smul f hf), integral_countable hf]
  change (∑' l, labelWeight l • ((labelWeight l)⁻¹ • f l)) = _
  simp only [smul_smul, mul_inv_cancel₀ (ne_of_gt (labelWeight_pos _)), one_smul,
    measureReal_def, Measure.count_singleton, ENNReal.toReal_one]

variable {P : Type*} [MeasurableSpace P]

theorem stronglyMeasurable_normalizeCountField (f : P × ℕ → B)
    (hf : StronglyMeasurable f) : StronglyMeasurable (normalizeCountField f) := by
  have hw : StronglyMeasurable (fun z : P × ℕ => (labelWeight z.2)⁻¹) :=
    ((measurable_of_countable (fun l : ℕ => (labelWeight l)⁻¹)).comp measurable_snd).stronglyMeasurable
  exact hw.smul hf

theorem integrable_normalizeCountField (f : P × ℕ → B) (hf : StronglyMeasurable f)
    (μ : Measure P) (hint : Integrable f (μ.prod Measure.count)) :
    Integrable (normalizeCountField f) (μ.prod labelProbability) := by
  have hc := (integrable_prod_iff hint.aestronglyMeasurable).mp hint
  apply (integrable_prod_iff
    (stronglyMeasurable_normalizeCountField f hf).aestronglyMeasurable).mpr
  constructor
  · filter_upwards [hc.1] with p hp
    exact integrable_label_inv_smul (fun l => f (p,l)) hp
  · have he : (fun p => ∫ l, ‖normalizeCountField f (p,l)‖ ∂labelProbability) =ᵐ[μ]
        (fun p => ∫ l, ‖f (p,l)‖ ∂Measure.count) := by
      filter_upwards [hc.1] with p hp
      have hn : (fun l => ‖normalizeCountField f (p,l)‖) =
          fun l => (labelWeight l)⁻¹ • ‖f (p,l)‖ := by
        funext l
        simp only [normalizeCountField, norm_smul, Real.norm_eq_abs,
          abs_of_pos (inv_pos.mpr (labelWeight_pos l)), smul_eq_mul]
      rw [hn]
      exact integral_label_inv_smul (fun l => ‖f (p,l)‖) hp.norm
    exact hc.2.congr he.symm

theorem integral_normalizeCountField [CompleteSpace B] (f : P × ℕ → B)
    (hf : StronglyMeasurable f) (μ : Measure P) [SFinite μ]
    (hint : Integrable f (μ.prod Measure.count)) :
    (∫ z, normalizeCountField f z ∂μ.prod labelProbability) = ∫ z, f z ∂μ.prod Measure.count := by
  rw [integral_prod _ (integrable_normalizeCountField f hf μ hint), integral_prod _ hint]
  apply integral_congr_ae
  have hc := (integrable_prod_iff hint.aestronglyMeasurable).mp hint
  filter_upwards [hc.1] with p hp
  exact integral_label_inv_smul (fun l => f (p,l)) hp

end LabelTransport

open QuantumProver.ElegantJointMeasurement.HilbertChoi QuantumProver.ElegantJointMeasurement.NuclearChoi QuantumProver.ElegantJointMeasurement.NormalCPInstruments

variable {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {H Ω : Type*} [MeasurableSpace H] [MeasurableSpace Ω]

def fineProbabilityKernel (P : Instrument I E H Ω) : Kernel H (Ω × ℕ) :=
  P.referenceKernel.prod (Kernel.const H labelProbability)

theorem fineProbabilityKernel_apply (P : Instrument I E H Ω) (h : H) :
    fineProbabilityKernel P h = (P.referenceKernel h).prod labelProbability := by
  rw [fineProbabilityKernel, Kernel.prod_apply, Kernel.const_apply]

instance isMarkovKernel_fineProbabilityKernel (P : Instrument I E H Ω) :
    IsMarkovKernel (fineProbabilityKernel P) := by
  unfold fineProbabilityKernel
  infer_instance

def labelKrausScale (l : ℕ) : ℝ := (Real.sqrt (labelWeight l))⁻¹

theorem labelKrausScale_sq (l : ℕ) : labelKrausScale l ^ 2 = (labelWeight l)⁻¹ := by
  rw [labelKrausScale, inv_pow, Real.sq_sqrt (le_of_lt (labelWeight_pos l))]

def normalizedKraus (b : HilbertBasis ℕ ℂ (BlockSpace I E))
    (A : Nuclear (BlockSpace I E)) (l : ℕ) : EuclideanSpace ℂ I →L[ℂ] E :=
  (labelKrausScale l : ℂ) • canonicalKraus b A l

def normalizedAction (b : HilbertBasis ℕ ℂ (BlockSpace I E))
    (A : Nuclear (BlockSpace I E)) (l : ℕ) (X : Matrix I I ℂ) : Nuclear E :=
  (labelWeight l)⁻¹ • columnAction b A l X

def normalizedGram (b : HilbertBasis ℕ ℂ (BlockSpace I E))
    (A : Nuclear (BlockSpace I E)) (l : ℕ) : Matrix I I ℂ :=
  (labelWeight l)⁻¹ • columnGram b A l

theorem toOperator_normalizedAction (b : HilbertBasis ℕ ℂ (BlockSpace I E))
    (A : Nuclear (BlockSpace I E)) (l : ℕ) (X : Matrix I I ℂ) :
    QuantumProver.NuclearOperator.toOperator (normalizedAction b A l X) =
      normalizedKraus b A l ∘L matrixOperator X ∘L (normalizedKraus b A l).adjoint := by
  have hr : QuantumProver.NuclearOperator.toOperator ((labelWeight l)⁻¹ • columnAction b A l X) =
      (labelWeight l)⁻¹ • QuantumProver.NuclearOperator.toOperator (columnAction b A l X) :=
    (QuantumProver.NuclearOperator.toOperator (𝕜 := ℂ) (E := E) (F := E)).map_smul_of_tower _ _
  have ha : (normalizedKraus b A l).adjoint =
      (labelKrausScale l : ℂ) • (canonicalKraus b A l).adjoint := by
    unfold normalizedKraus
    rw [map_smulₛₗ]
    congr 1
    exact Complex.conj_ofReal _
  rw [normalizedAction, hr, toOperator_columnAction, ha]
  simp only [normalizedKraus, ContinuousLinearMap.smul_comp,
    ContinuousLinearMap.comp_smul, smul_smul]
  rw [← Complex.ofReal_mul, ← pow_two, labelKrausScale_sq]
  ext x
  simp only [smul_apply]
  exact RCLike.real_smul_eq_coe_smul (K := ℂ) (E := E) _ _

theorem matrixOperator_normalizedGram (b : HilbertBasis ℕ ℂ (BlockSpace I E))
    (A : Nuclear (BlockSpace I E)) (l : ℕ) :
    matrixOperator (normalizedGram b A l) =
      (normalizedKraus b A l).adjoint ∘L normalizedKraus b A l := by
  have hm : matrixOperator (normalizedGram b A l) =
      (labelWeight l)⁻¹ • matrixOperator (columnGram b A l) := by
    ext x i
    simp only [normalizedGram, matrixOperator_apply, Matrix.smul_apply,
      smul_apply, PiLp.smul_apply, RCLike.real_smul_eq_coe_mul,
      Finset.mul_sum, mul_assoc]
  have ha : (normalizedKraus b A l).adjoint =
      (labelKrausScale l : ℂ) • (canonicalKraus b A l).adjoint := by
    unfold normalizedKraus
    rw [map_smulₛₗ]
    congr 1
    exact Complex.conj_ofReal _
  rw [hm, matrixOperator_columnGram]
  rw [ha]
  simp only [normalizedKraus, ContinuousLinearMap.smul_comp,
    ContinuousLinearMap.comp_smul, smul_smul]
  rw [← Complex.ofReal_mul, ← pow_two, labelKrausScale_sq]
  ext x i
  simp only [smul_apply, PiLp.smul_apply, RCLike.real_smul_eq_coe_mul, smul_eq_mul]
  rfl

end QuantumProver.ElegantJointMeasurement.NormalInstrumentKraus

namespace QuantumProver.ElegantJointMeasurement.NormalInstrumentKraus

open QuantumProver.ElegantJointMeasurement.HilbertChoi QuantumProver.ElegantJointMeasurement.NuclearChoi QuantumProver.ElegantJointMeasurement.NormalCPInstruments

variable {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {H Ω : Type*} [MeasurableSpace H] [MeasurableSpace Ω]
variable [MeasurableSpace.CountableOrCountablyGenerated H Ω]

local instance normalizedKrausMeasurable : MeasurableSpace (EuclideanSpace ℂ I →L[ℂ] E) := borel _
local instance normalizedKrausBorel : BorelSpace (EuclideanSpace ℂ I →L[ℂ] E) := ⟨rfl⟩
local instance normalizedNuclearMeasurable : MeasurableSpace (Nuclear E) := borel _
local instance normalizedNuclearBorel : BorelSpace (Nuclear E) := ⟨rfl⟩
local instance normalizedBlockNuclearMeasurable : MeasurableSpace (Nuclear (BlockSpace I E)) := borel _
local instance normalizedBlockNuclearBorel : BorelSpace (Nuclear (BlockSpace I E)) := ⟨rfl⟩

theorem exists_physical_probability_kraus_representation
    (P : Instrument I E H Ω) (b : HilbertBasis ℕ ℂ (BlockSpace I E)) :
    ∃ D : H → Ω → Nuclear (BlockSpace I E),
      Measurable (fun z : H × Ω => D z.1 z.2) ∧
      (∀ h ω, (QuantumProver.NuclearOperator.toOperator (D h ω)).IsPositive) ∧
      Measurable (fun z : H × (Ω × ℕ) => normalizedKraus b (D z.1 z.2.1) z.2.2) ∧
      (∀ h X, Integrable (fun z : Ω × ℕ => normalizedAction b (D h z.1) z.2 X)
        (fineProbabilityKernel P h)) ∧
      (∀ h (s : Set Ω), MeasurableSet s → ∀ X,
        (∫ z : Ω × ℕ, normalizedAction b (D h z.1) z.2 X
          ∂((P.referenceKernel h).restrict s).prod labelProbability) = P.operation h s X) ∧
      (∀ h, Integrable (fun z : Ω × ℕ => normalizedGram b (D h z.1) z.2)
        (fineProbabilityKernel P h)) ∧
      (∀ h, (∫ z : Ω × ℕ, normalizedGram b (D h z.1) z.2
        ∂fineProbabilityKernel P h) = (1 : Matrix I I ℂ)) := by
  obtain ⟨D, hstrong, hmeas, hpos, htrace, hbound, hmass, hint, hset⟩ :=
    QuantumProver.ElegantJointMeasurement.NormalNuclearDensity.exists_physical_positive_nuclear_density P b
  have hd (h : H) : Measurable (D h) :=
    hmeas.comp (measurable_const.prodMk measurable_id)
  have hn (h : H) (μ : Measure Ω) (hμ : Integrable (D h) μ) :
      Integrable (normalizeCountField (fineNuclearColumn b (D h))) (μ.prod labelProbability) :=
    integrable_normalizeCountField _ (stronglyMeasurable_fineNuclearColumn b (D h) (hd h)) μ
      (integrable_fineNuclearColumn b (D h) (hd h) (hpos h) μ hμ)
  have hi (h : H) (μ : Measure Ω) [SFinite μ] (hμ : Integrable (D h) μ) :
      (∫ z, normalizeCountField (fineNuclearColumn b (D h)) z ∂μ.prod labelProbability) =
        ∫ ω, D h ω ∂μ := by
    rw [integral_normalizeCountField _
      (stronglyMeasurable_fineNuclearColumn b (D h) (hd h)) μ
      (integrable_fineNuclearColumn b (D h) (hd h) (hpos h) μ hμ)]
    exact integral_fineNuclearColumn b (D h) (hd h) (hpos h) μ hμ
  refine ⟨D, hmeas, hpos, ?_, ?_, ?_, ?_, ?_⟩
  · have hk : Measurable (fun z : H × (Ω × ℕ) => canonicalKraus b (D z.1 z.2.1) z.2.2) := by
      have hm : Measurable (fun z : (H × Ω) × ℕ => canonicalKraus b (D z.1.1 z.1.2) z.2) :=
        measurable_from_prod_countable_left (fun l =>
          measurable_canonicalKraus b (fun z : H × Ω => D z.1 z.2) hmeas l)
      have hA : Measurable (fun z : H × (Ω × ℕ) => ((z.1,z.2.1),z.2.2)) :=
        (measurable_fst.prodMk (measurable_fst.comp measurable_snd)).prodMk
          (measurable_snd.comp measurable_snd)
      simpa only [Function.comp_def] using hm.comp hA
    have hw : Measurable (fun z : H × (Ω × ℕ) => (labelKrausScale z.2.2 : ℂ)) :=
      (measurable_of_countable (fun l : ℕ => (labelKrausScale l : ℂ))).comp
        (measurable_snd.comp measurable_snd)
    exact hw.smul hk
  · intro h X
    rw [fineProbabilityKernel_apply]
    let DX : Nuclear (BlockSpace I E) →L[ℂ] Nuclear E := nuclearDecode (E := E) X
    simpa only [DX, normalizeCountField, fineNuclearColumn, ContinuousLinearMap.map_smul_of_tower,
      nuclearDecode_nuclearColumn, columnAction, normalizedAction] using
      DX.integrable_comp (hn h (P.referenceKernel h) (hint h))
  · intro h s hs X
    let DX : Nuclear (BlockSpace I E) →L[ℂ] Nuclear E := nuclearDecode (E := E) X
    calc
      (∫ z : Ω × ℕ, normalizedAction b (D h z.1) z.2 X
          ∂((P.referenceKernel h).restrict s).prod labelProbability) =
          DX (∫ z, normalizeCountField (fineNuclearColumn b (D h)) z
            ∂((P.referenceKernel h).restrict s).prod labelProbability) := by
        simpa only [DX, normalizeCountField, fineNuclearColumn, ContinuousLinearMap.map_smul_of_tower,
          nuclearDecode_nuclearColumn, columnAction, normalizedAction] using
          DX.integral_comp_comm (hn h ((P.referenceKernel h).restrict s) (hint h).integrableOn)
      _ = DX (∫ ω in s, D h ω ∂P.referenceKernel h) := by
        rw [hi h ((P.referenceKernel h).restrict s) (hint h).integrableOn]
      _ = P.operation h s X := by
        rw [hset h s hs]
        exact nuclearDecode_physicalChoi P h s X
  · intro h
    rw [fineProbabilityKernel_apply]
    let G : Nuclear (BlockSpace I E) →L[ℂ] Matrix I I ℂ := inputGram (I := I) (E := E)
    simpa only [G, normalizeCountField, fineNuclearColumn, ContinuousLinearMap.map_smul_of_tower,
      inputGram_nuclearColumn, columnGram, normalizedGram] using
      G.integrable_comp (hn h (P.referenceKernel h) (hint h))
  · intro h
    rw [fineProbabilityKernel_apply]
    let G : Nuclear (BlockSpace I E) →L[ℂ] Matrix I I ℂ := inputGram (I := I) (E := E)
    have hG : (∫ z : Ω × ℕ, normalizedGram b (D h z.1) z.2 ∂(P.referenceKernel h).prod labelProbability) =
        G (∫ z, normalizeCountField (fineNuclearColumn b (D h)) z
          ∂(P.referenceKernel h).prod labelProbability) := by
      simpa only [G, normalizeCountField, fineNuclearColumn, ContinuousLinearMap.map_smul_of_tower,
        inputGram_nuclearColumn, columnGram, normalizedGram] using
        G.integral_comp_comm (hn h (P.referenceKernel h) (hint h))
    rw [hG, hi h (P.referenceKernel h) (hint h)]
    have hu : (∫ ω, D h ω ∂P.referenceKernel h) = P.physicalChoi h Set.univ := by
      simpa only [Measure.restrict_univ] using hset h Set.univ MeasurableSet.univ
    rw [hu]
    exact inputGram_physicalChoi_univ P h

end QuantumProver.ElegantJointMeasurement.NormalInstrumentKraus

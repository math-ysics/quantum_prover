import QuantumProver.QuantumChannels.NuclearTensor
import QuantumProver.InformationTheory.ElegantJointMeasurement.FiniteKrausPredual

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory InnerProductSpace
open scoped BigOperators InnerProduct ComplexOrder MatrixOrder Topology
  Matrix.Norms.L2Operator Kronecker

namespace QuantumProver.ElegantJointMeasurement.HilbertPendingTensor

open QuantumProver.ElegantJointMeasurement.HilbertPolar QuantumProver.ElegantJointMeasurement.HilbertRecovery QuantumProver.ElegantJointMeasurement.HilbertFiniteKrausPredual
open QuantumProver.ElegantJointMeasurement.NormalCPInstruments QuantumProver.ElegantJointMeasurement.HilbertChoi
open QuantumProver.MatrixNuclearTensor QuantumProver.HilbertNuclearCompression
open QuantumProver.NuclearOperator (toOperator toOperator_injective rankOne)

variable {I J Q R : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  [Fintype Q] [Fintype R]
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

local instance sourceComplete (K : Type) [Fintype K] : CompleteSpace (Source K) :=
  PiLp.completeSpace 2 (fun _ : K => ℂ)

def jointKraus (K : Q → Source I →L[ℂ] E) (L : R → Source J →L[ℂ] F) :
    Q × R → Source (I × J) →L[ℂ] Joint E F :=
  fun q => tensorMap (K q.1) (L q.2) ∘L
    (finiteTensorEmbedding I J).toContinuousLinearMap

omit [DecidableEq I] [DecidableEq J] in
@[simp] theorem jointKraus_basis
    (K : Q → Source I →L[ℂ] E) (L : R → Source J →L[ℂ] F)
    (q : Q × R) (i : I) (j : J) :
    jointKraus K L q (EuclideanSpace.basisFun (I × J) ℂ (i,j)) =
      tmulJoint (K q.1 (EuclideanSpace.basisFun I ℂ i))
        (L q.2 (EuclideanSpace.basisFun J ℂ j)) := by
  classical
  simp only [jointKraus, ContinuousLinearMap.comp_apply,
    LinearIsometry.coe_toContinuousLinearMap, EuclideanSpace.basisFun_apply]
  rw [finiteTensorEmbedding_single I J i j, tensorMap_tmul]

omit [DecidableEq I] [DecidableEq J] in
theorem tensorMap_finite_sums (A : Q → Source I →L[ℂ] Source I)
    (B : R → Source J →L[ℂ] Source J) :
    tensorMap (∑ q, A q) (∑ r, B r) = ∑ q, ∑ r, tensorMap (A q) (B r) := by
  classical
  calc
    _ = ∑ q, tensorMap (A q) (∑ r, B r) :=
      by simpa only [tensorMapLeft_apply] using
        (map_sum (tensorMapLeft (E := Source I) (E' := Source I) (∑ r, B r)) A Finset.univ)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro q _
      simpa only [tensorMapRight_apply] using
        (map_sum (tensorMapRight (F := Source J) (F' := Source J) (A q)) B Finset.univ)

omit [DecidableEq I] [DecidableEq J] [Fintype Q] [Fintype R] in
theorem jointKraus_gram_term
    (K : Q → Source I →L[ℂ] E) (L : R → Source J →L[ℂ] F) (q : Q × R) :
    (jointKraus K L q).adjoint ∘L jointKraus K L q =
      (finiteTensorEmbedding I J).toContinuousLinearMap.adjoint ∘L
        tensorMap ((K q.1).adjoint ∘L K q.1) ((L q.2).adjoint ∘L L q.2) ∘L
          (finiteTensorEmbedding I J).toContinuousLinearMap := by
  rw [jointKraus, ContinuousLinearMap.adjoint_comp, tensorMap_adjoint,
    tensorMap_comp]
  simp only [ContinuousLinearMap.comp_assoc]

theorem jointKraus_complete
    (K : Q → Source I →L[ℂ] E) (L : R → Source J →L[ℂ] F)
    (hK : ∑ q, (K q).adjoint ∘L K q = 1)
    (hL : ∑ r, (L r).adjoint ∘L L r = 1) :
    ∑ q, (jointKraus K L q).adjoint ∘L jointKraus K L q = 1 := by
  classical
  let U := (finiteTensorEmbedding I J).toContinuousLinearMap
  have hsum : (∑ q, (jointKraus K L q).adjoint ∘L jointKraus K L q) =
      U.adjoint ∘L (∑ q : Q × R,
        tensorMap ((K q.1).adjoint ∘L K q.1) ((L q.2).adjoint ∘L L q.2)) ∘L U := by
    simp only [jointKraus_gram_term]
    apply ContinuousLinearMap.ext
    intro x
    simp only [sum_apply, ContinuousLinearMap.comp_apply, map_sum, U]
  have hTensor : (∑ q : Q × R,
      tensorMap ((K q.1).adjoint ∘L K q.1) ((L q.2).adjoint ∘L L q.2)) =
      tensorMap (∑ q, (K q).adjoint ∘L K q) (∑ r, (L r).adjoint ∘L L r) := by
    simpa only [Fintype.sum_prod_type] using
      (tensorMap_finite_sums (I := I) (J := J)
        (fun q : Q => (K q).adjoint ∘L K q) (fun r : R => (L r).adjoint ∘L L r)).symm
  rw [hsum, hTensor, hK, hL]
  simpa only [ContinuousLinearMap.one_def, tensorMap_id_id,
    ContinuousLinearMap.comp_id, ContinuousLinearMap.id_comp, U] using
      (finiteTensorEmbedding I J).adjoint_comp_self

def jointOperation (K : Q → Source I →L[ℂ] E) (L : R → Source J →L[ℂ] F) :
    PhysicalOperation (I × J) (Joint E F) :=
  finiteKrausOperation (jointKraus K L)

omit [CompleteSpace E] [CompleteSpace F] in
theorem completelyPositive_jointOperation
    (K : Q → Source I →L[ℂ] E) (L : R → Source J →L[ℂ] F) :
    CompletelyPositive (QuantumProver.ElegantJointMeasurement.NuclearChoi.operationOperator (jointOperation K L).toLinearMap) :=
  completelyPositive_finiteKrausOperation (jointKraus K L)

theorem trace_jointOperation
    (K : Q → Source I →L[ℂ] E) (L : R → Source J →L[ℂ] F)
    (hK : ∑ q, (K q).adjoint ∘L K q = 1)
    (hL : ∑ r, (L r).adjoint ∘L L r = 1)
    (X : Matrix (I × J) (I × J) ℂ) :
    QuantumProver.HilbertNuclearTrace.trace (jointOperation K L X) = Matrix.trace X :=
  tracePreserving_finiteKrausOperation (jointKraus K L) (jointKraus_complete K L hK hL) X

omit [DecidableEq I] in
theorem sandwich_inner_rankOne (K : Source I →L[ℂ] E) (x y : Source I) :
    nuclearSandwich K (rankOne (innerSL ℂ x) y) =
      rankOne (innerSL ℂ (K x)) (K y) := by
  change compose K K.adjoint (rankOne (innerSL ℂ x) y) = _
  rw [compose_rankOne]
  congr 1
  ext z
  exact ContinuousLinearMap.adjoint_inner_right K x z

theorem nuclearSandwich_matrix_expansion (K : Source I →L[ℂ] E) (X : Matrix I I ℂ) :
    nuclearSandwich K (nuclearMatrix X) =
      ∑ i, ∑ j, X i j • rankOne (innerSL ℂ (K (EuclideanSpace.basisFun I ℂ j)))
        (K (EuclideanSpace.basisFun I ℂ i)) := by
  change nuclearSandwich K (∑ i, ∑ j, X i j •
      rankOne (innerSL ℂ (EuclideanSpace.basisFun I ℂ j))
        (EuclideanSpace.basisFun I ℂ i)) = _
  simp only [map_sum, map_smul, sandwich_inner_rankOne]

theorem jointKraus_product_sandwich
    (K : Q → Source I →L[ℂ] E) (L : R → Source J →L[ℂ] F)
    (q : Q × R) (X : Matrix I I ℂ) (Y : Matrix J J ℂ) :
    nuclearSandwich (jointKraus K L q) (nuclearMatrix (X ⊗ₖ Y)) =
      tensorNuclear (nuclearSandwich (K q.1) (nuclearMatrix X))
        (nuclearSandwich (L q.2) (nuclearMatrix Y)) := by
  classical
  rw [nuclearSandwich_matrix_expansion, nuclearSandwich_matrix_expansion,
    nuclearSandwich_matrix_expansion]
  simp only [Fintype.sum_prod_type, Matrix.kronecker_apply, jointKraus_basis,
    rankOne_tmul_innerSL, map_sum, map_smul,
    sum_apply, smul_apply, Finset.smul_sum, smul_smul]
  let f (i i' : I) (j j' : J) : QuantumProver.ElegantJointMeasurement.NuclearChoi.Nuclear (Joint E F) :=
    (X i i' * Y j j') • tensorNuclear
      (rankOne (innerSL ℂ (K q.1 (EuclideanSpace.basisFun I ℂ i')))
        (K q.1 (EuclideanSpace.basisFun I ℂ i)))
      (rankOne (innerSL ℂ (L q.2 (EuclideanSpace.basisFun J ℂ j')))
        (L q.2 (EuclideanSpace.basisFun J ℂ j)))
  calc
    _ = ∑ i, ∑ i', ∑ j, ∑ j', f i i' j j' := by
      change (∑ i, ∑ j, ∑ i', ∑ j', f i i' j j') = _
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = ∑ j, ∑ j', ∑ i, ∑ i', f i i' j j' := by
      have h : (∑ a : I × I, ∑ b : J × J, f a.1 a.2 b.1 b.2) =
          ∑ b : J × J, ∑ a : I × I, f a.1 a.2 b.1 b.2 := Finset.sum_comm
      simpa only [Fintype.sum_prod_type] using h
    _ = _ := by
      dsimp only [f]
      simp only [mul_comm]

theorem jointOperation_product
    (K : Q → Source I →L[ℂ] E) (L : R → Source J →L[ℂ] F)
    (X : Matrix I I ℂ) (Y : Matrix J J ℂ) :
    jointOperation K L (X ⊗ₖ Y) =
      tensorNuclear (finiteKrausOperation K X) (finiteKrausOperation L Y) := by
  classical
  simp only [jointOperation, finiteKrausOperation, finiteKrausChannel,
    ContinuousLinearMap.comp_apply, sum_apply,
    Fintype.sum_prod_type, jointKraus_product_sandwich, map_sum]
  rw [Finset.sum_comm]

def sourceFromColumns (v : I → E) : Source I →L[ℂ] E :=
  ∑ i, (innerSL ℂ (EuclideanSpace.basisFun I ℂ i)).smulRight (v i)

omit [DecidableEq I] [CompleteSpace E] in
theorem sourceFromColumns_map (K : Source I →L[ℂ] E) :
    sourceFromColumns (fun i => K (EuclideanSpace.basisFun I ℂ i)) = K := by
  classical
  ext x
  change (∑ i, (innerSL ℂ (EuclideanSpace.basisFun I ℂ i)).smulRight
      (K (EuclideanSpace.basisFun I ℂ i))) x = K x
  simp only [sum_apply, ContinuousLinearMap.smulRight_apply,
    innerSL_apply_apply]
  simp only [← map_smul]
  rw [← map_sum]
  exact congrArg K ((EuclideanSpace.basisFun I ℂ).sum_repr' x)

omit [DecidableEq I] [CompleteSpace E] in
theorem continuous_sourceFromColumns : Continuous (sourceFromColumns (I := I) (E := E)) := by
  classical
  apply continuous_finsetSum
  intro i _
  exact (ContinuousLinearMap.smulRightL ℂ (Source I) E
    (innerSL ℂ (EuclideanSpace.basisFun I ℂ i))).continuous.comp (continuous_apply i)

theorem continuous_sourceMap_of_basis {Z : Type*} [TopologicalSpace Z]
    (K : Z → Source I →L[ℂ] E)
    (hK : ∀ i, Continuous (fun z => K z (EuclideanSpace.basisFun I ℂ i))) : Continuous K := by
  have hcols : Continuous (fun z i => K z (EuclideanSpace.basisFun I ℂ i)) := continuous_pi hK
  have h := continuous_sourceFromColumns.comp hcols
  simpa only [Function.comp_def, sourceFromColumns_map] using h

theorem continuous_jointKraus :
    Continuous (fun p : (Q → Source I →L[ℂ] E) × (R → Source J →L[ℂ] F) =>
      jointKraus p.1 p.2) := by
  apply continuous_pi
  intro q
  apply continuous_sourceMap_of_basis
  rintro ⟨i,j⟩
  have hK : Continuous (fun p : (Q → Source I →L[ℂ] E) × (R → Source J →L[ℂ] F) =>
      p.1 q.1 (EuclideanSpace.basisFun I ℂ i)) := by fun_prop
  have hL : Continuous (fun p : (Q → Source I →L[ℂ] E) × (R → Source J →L[ℂ] F) =>
      p.2 q.2 (EuclideanSpace.basisFun J ℂ j)) := by fun_prop
  have h := (tmulJoint (E := E) (F := F)).continuous₂.comp (hK.prodMk hL)
  simpa only [Function.comp_def, Function.uncurry, jointKraus_basis] using h

theorem continuous_jointOperation :
    Continuous (fun p : (Q → Source I →L[ℂ] E) × (R → Source J →L[ℂ] F) =>
      jointOperation p.1 p.2) :=
  continuous_finiteKrausOperation.comp continuous_jointKraus

local instance jointDataMeasurable :
    MeasurableSpace ((Q → Source I →L[ℂ] E) × (R → Source J →L[ℂ] F)) := borel _
local instance jointDataBorel :
    BorelSpace ((Q → Source I →L[ℂ] E) × (R → Source J →L[ℂ] F)) := ⟨rfl⟩
local instance jointOperationMeasurable :
    MeasurableSpace (PhysicalOperation (I × J) (Joint E F)) := borel _
local instance jointOperationBorel :
    BorelSpace (PhysicalOperation (I × J) (Joint E F)) := ⟨rfl⟩

theorem measurable_jointOperation :
    Measurable (fun p : (Q → Source I →L[ℂ] E) × (R → Source J →L[ℂ] F) =>
      jointOperation p.1 p.2) := continuous_jointOperation.measurable

theorem stronglyMeasurable_sourceMap_of_basis {Z : Type*} [MeasurableSpace Z]
    (K : Z → Source I →L[ℂ] E)
    (hK : ∀ i, StronglyMeasurable (fun z => K z (EuclideanSpace.basisFun I ℂ i))) :
    StronglyMeasurable K := by
  classical
  have h : StronglyMeasurable (fun z => ∑ i,
      (innerSL ℂ (EuclideanSpace.basisFun I ℂ i)).smulRight
        (K z (EuclideanSpace.basisFun I ℂ i))) := by
    apply Finset.stronglyMeasurable_fun_sum
    intro i _
    exact (ContinuousLinearMap.smulRightL ℂ (Source I) E
      (innerSL ℂ (EuclideanSpace.basisFun I ℂ i))).continuous.comp_stronglyMeasurable (hK i)
  change StronglyMeasurable (fun z => sourceFromColumns
    (fun i => K z (EuclideanSpace.basisFun I ℂ i))) at h
  simpa only [sourceFromColumns_map] using h

theorem stronglyMeasurable_family_of_basis {Z : Type*} [MeasurableSpace Z]
    (K : Z → Q → Source I →L[ℂ] E)
    (hK : ∀ q i, StronglyMeasurable (fun z => K z q (EuclideanSpace.basisFun I ℂ i))) :
    StronglyMeasurable K := by
  classical
  have hq (q : Q) : StronglyMeasurable (fun z => K z q) :=
    stronglyMeasurable_sourceMap_of_basis (fun z => K z q) (hK q)
  have h : StronglyMeasurable (fun z => ∑ q : Q,
      ContinuousLinearMap.single ℂ (fun _ : Q => Source I →L[ℂ] E) q (K z q)) := by
    apply Finset.stronglyMeasurable_fun_sum
    intro q _
    exact (ContinuousLinearMap.single ℂ (fun _ : Q => Source I →L[ℂ] E) q).continuous.comp_stronglyMeasurable (hq q)
  convert h using 1
  funext z q
  simp only [Finset.sum_apply, ContinuousLinearMap.single_apply]
  simp

theorem stronglyMeasurable_jointKraus_of_basis {Z : Type*} [MeasurableSpace Z]
    (K : Z → Q → Source I →L[ℂ] E) (L : Z → R → Source J →L[ℂ] F)
    (hK : ∀ q i, StronglyMeasurable (fun z => K z q (EuclideanSpace.basisFun I ℂ i)))
    (hL : ∀ r j, StronglyMeasurable (fun z => L z r (EuclideanSpace.basisFun J ℂ j))) :
    StronglyMeasurable (fun z => jointKraus (K z) (L z)) := by
  have hK' : StronglyMeasurable K := stronglyMeasurable_family_of_basis (I := I) (Q := Q) (E := E) K hK
  have hL' : StronglyMeasurable L := stronglyMeasurable_family_of_basis (I := J) (Q := R) (E := F) L hL
  have hc : Continuous (fun p : (Q → Source I →L[ℂ] E) × (R → Source J →L[ℂ] F) =>
      jointKraus p.1 p.2) := continuous_jointKraus
  simpa only [Function.comp_def] using hc.comp_stronglyMeasurable (hK'.prodMk hL')

theorem stronglyMeasurable_jointOperation_of_basis {Z : Type*} [MeasurableSpace Z]
    (K : Z → Q → Source I →L[ℂ] E) (L : Z → R → Source J →L[ℂ] F)
    (hK : ∀ q i, StronglyMeasurable (fun z => K z q (EuclideanSpace.basisFun I ℂ i)))
    (hL : ∀ r j, StronglyMeasurable (fun z => L z r (EuclideanSpace.basisFun J ℂ j))) :
    StronglyMeasurable (fun z => jointOperation (K z) (L z)) := by
  have hK' : StronglyMeasurable K := stronglyMeasurable_family_of_basis (I := I) (Q := Q) (E := E) K hK
  have hL' : StronglyMeasurable L := stronglyMeasurable_family_of_basis (I := J) (Q := R) (E := F) L hL
  have hc : Continuous (fun p : (Q → Source I →L[ℂ] E) × (R → Source J →L[ℂ] F) =>
      jointOperation p.1 p.2) := continuous_jointOperation
  simpa only [Function.comp_def] using hc.comp_stronglyMeasurable (hK'.prodMk hL')

theorem stronglyMeasurable_jointOperation_apply_of_basis {Z : Type*} [MeasurableSpace Z]
    (K : Z → Q → Source I →L[ℂ] E) (L : Z → R → Source J →L[ℂ] F)
    (hK : ∀ q i, StronglyMeasurable (fun z => K z q (EuclideanSpace.basisFun I ℂ i)))
    (hL : ∀ r j, StronglyMeasurable (fun z => L z r (EuclideanSpace.basisFun J ℂ j)))
    (X : Z → Matrix (I × J) (I × J) ℂ) (hX : StronglyMeasurable X) :
    StronglyMeasurable (fun z => jointOperation (K z) (L z) (X z)) := by
  have hJ : StronglyMeasurable (fun z => jointKraus (K z) (L z)) :=
    stronglyMeasurable_jointKraus_of_basis K L hK hL
  exact stronglyMeasurable_finiteKrausOperation_apply
    (I := I × J) (Q := Q × R) (E := Joint E F) hJ hX

end QuantumProver.ElegantJointMeasurement.HilbertPendingTensor

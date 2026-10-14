import Mathlib

noncomputable section

open scoped BigOperators InnerProduct ComplexConjugate ComplexOrder
open InnerProductSpace ContinuousLinearMap

namespace QuantumProver.ElegantJointMeasurement.HilbertChoi

variable {I : Type} [Fintype I] [DecidableEq I]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

abbrev BlockSpace (I : Type*) (E : Type*) := PiLp 2 (fun _ : I => E)

def insert (i : I) : E →L[ℂ] BlockSpace I E :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : I => E)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.single ℂ (fun _ : I => E) i)

@[simp] theorem insert_apply (i : I) (x : E) :
    insert i x = PiLp.single 2 i x := rfl

@[simp] theorem insert_apply_apply (i j : I) (x : E) :
    insert i x j = if j = i then x else 0 := by
  by_cases h : j = i
  · subst j
    simp
  · simp only [if_neg h]
    change (Pi.single i x : I → E) j = 0
    simp [Pi.single_apply, h]

def blockOperator (B : I → I → (E →L[ℂ] E)) :
    BlockSpace I E →L[ℂ] BlockSpace I E :=
  ∑ i, ∑ j, (insert i).comp ((B i j).comp (PiLp.proj 2 (fun _ : I => E) j))

theorem blockOperator_apply (B : I → I → (E →L[ℂ] E))
    (x : BlockSpace I E) (i : I) :
    blockOperator B x i = ∑ j, B i j (x j) := by
  simp [blockOperator, Pi.single_apply]

@[simp] theorem blockOperator_block (B : I → I → (E →L[ℂ] E)) (i j : I) :
    (PiLp.proj 2 (fun _ : I => E) i).comp ((blockOperator B).comp (insert j)) =
      B i j := by
  ext x
  simp [blockOperator_apply, insert_apply_apply, apply_ite]

def matrixUnit (i j : I) : Matrix I I ℂ := Matrix.single i j 1

theorem matrix_decomposition (X : Matrix I I ℂ) :
    X = ∑ i, ∑ j, X i j • matrixUnit i j := by
  ext i j
  simp [matrixUnit, Matrix.single, Matrix.sum_apply, ite_and]

def choi (Φ : Matrix I I ℂ →ₗ[ℂ] (E →L[ℂ] E)) :
    BlockSpace I E →L[ℂ] BlockSpace I E :=
  blockOperator (fun i j => Φ (matrixUnit i j))

@[simp] theorem choi_block (Φ : Matrix I I ℂ →ₗ[ℂ] (E →L[ℂ] E)) (i j : I) :
    (PiLp.proj 2 (fun _ : I => E) i).comp ((choi Φ).comp (insert j)) =
      Φ (matrixUnit i j) := blockOperator_block _ _ _

theorem action_eq_choi_blocks (Φ : Matrix I I ℂ →ₗ[ℂ] (E →L[ℂ] E))
    (X : Matrix I I ℂ) :
    Φ X = ∑ i, ∑ j, X i j •
      (PiLp.proj 2 (fun _ : I => E) i).comp ((choi Φ).comp (insert j)) := by
  simp only [choi_block]
  conv_lhs => rw [matrix_decomposition X]
  simp only [map_sum, map_smul]

variable {R : Type} [Fintype R] [DecidableEq R]

def amplification (Φ : Matrix I I ℂ →ₗ[ℂ] (E →L[ℂ] E))
    (X : Matrix (R × I) (R × I) ℂ) :
    BlockSpace R E →L[ℂ] BlockSpace R E :=
  blockOperator (fun r s => ∑ i, ∑ j, X (r,i) (s,j) • Φ (matrixUnit i j))

def CompletelyPositive (Φ : Matrix I I ℂ →ₗ[ℂ] (E →L[ℂ] E)) : Prop :=
  ∀ (R : Type) [Fintype R] [DecidableEq R]
    (X : Matrix (R × I) (R × I) ℂ), X.PosSemidef → (amplification Φ X).IsPositive

def maximallyEntangled : I × I → ℂ := fun q => if q.1 = q.2 then 1 else 0

def entangledEffect : Matrix (I × I) (I × I) ℂ :=
  Matrix.vecMulVec (maximallyEntangled (I := I)) (star (maximallyEntangled (I := I)))

theorem entangledEffect_posSemidef : (entangledEffect (I := I)).PosSemidef :=
  Matrix.posSemidef_vecMulVec_self_star _

theorem amplification_entangled_eq_choi
    (Φ : Matrix I I ℂ →ₗ[ℂ] (E →L[ℂ] E)) :
    amplification Φ (entangledEffect (I := I)) = choi Φ := by
  change blockOperator (I := I) (E := E) _ = blockOperator (I := I) (E := E) _
  congr 1
  funext r s
  simp [entangledEffect, maximallyEntangled, Matrix.vecMulVec_apply]

theorem choi_isPositive (Φ : Matrix I I ℂ →ₗ[ℂ] (E →L[ℂ] E))
    (hΦ : CompletelyPositive Φ) : (choi Φ).IsPositive := by
  rw [← amplification_entangled_eq_choi]
  exact hΦ I _ entangledEffect_posSemidef

end QuantumProver.ElegantJointMeasurement.HilbertChoi

namespace QuantumProver.ElegantJointMeasurement.HilbertChoi

section HilbertColumns

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {L : Type*}

def squareRootColumn (b : HilbertBasis L ℂ E) (D : E →L[ℂ] E) (l : L) : E :=
  CFC.sqrt D (b l)

theorem sqrt_adjoint_eq (D : E →L[ℂ] E) :
    (CFC.sqrt D).adjoint = CFC.sqrt D := by
  exact (ContinuousLinearMap.nonneg_iff_isPositive.mp (CFC.sqrt_nonneg D)).isSelfAdjoint

theorem sqrt_comp_sqrt (D : E →L[ℂ] E) (hD : D.IsPositive) :
    (CFC.sqrt D).comp (CFC.sqrt D) = D := by
  exact CFC.sqrt_mul_sqrt_self D (ContinuousLinearMap.nonneg_iff_isPositive.mpr hD)

theorem squareRootColumn_norm_sq (b : HilbertBasis L ℂ E) (D : E →L[ℂ] E)
    (hD : D.IsPositive) (l : L) :
    ‖squareRootColumn b D l‖ ^ 2 = (inner ℂ (D (b l)) (b l)).re := by
  rw [squareRootColumn, ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_left,
    sqrt_adjoint_eq, sqrt_comp_sqrt D hD]
  rfl

theorem squareRootColumns_hasSum_apply (b : HilbertBasis L ℂ E) (D : E →L[ℂ] E)
    (hD : D.IsPositive) (x : E) :
    HasSum (fun l => rankOne ℂ (squareRootColumn b D l) (squareRootColumn b D l) x)
      (D x) := by
  have ht := (CFC.sqrt D).hasSum (b.hasSum_repr (CFC.sqrt D x))
  have hinner (l : L) : inner ℂ (squareRootColumn b D l) x =
      inner ℂ (b l) (CFC.sqrt D x) := by
    exact (ContinuousLinearMap.nonneg_iff_isPositive.mp (CFC.sqrt_nonneg D)).inner_left_eq_inner_right (b l) x
  have hDx : CFC.sqrt D (CFC.sqrt D x) = D x :=
    congrArg (fun T : E →L[ℂ] E => T x) (sqrt_comp_sqrt D hD)
  rw [hDx] at ht
  simp only [rankOne_apply, hinner]
  simpa only [squareRootColumn, HilbertBasis.repr_apply_apply, map_smul] using ht

theorem squareRootColumns_summable (b : HilbertBasis L ℂ E) (D : E →L[ℂ] E)
    (hD : D.IsPositive)
    (htrace : Summable (fun l => (inner ℂ (D (b l)) (b l)).re)) :
    Summable (fun l => rankOne ℂ (squareRootColumn b D l) (squareRootColumn b D l)) := by
  apply htrace.of_norm_bounded
  intro l
  rw [norm_rankOne, ← sq, squareRootColumn_norm_sq b D hD]

theorem squareRootColumns_hasSum (b : HilbertBasis L ℂ E) (D : E →L[ℂ] E)
    (hD : D.IsPositive)
    (htrace : Summable (fun l => (inner ℂ (D (b l)) (b l)).re)) :
    HasSum (fun l => rankOne ℂ (squareRootColumn b D l) (squareRootColumn b D l)) D := by
  have hs := squareRootColumns_summable b D hD htrace
  have heq : (∑' l, rankOne ℂ (squareRootColumn b D l) (squareRootColumn b D l)) = D := by
    ext x
    exact ((ContinuousLinearMap.apply ℂ E x).hasSum hs.hasSum).unique
      (squareRootColumns_hasSum_apply b D hD x)
  simpa only [heq] using hs.hasSum

end HilbertColumns
end QuantumProver.ElegantJointMeasurement.HilbertChoi

namespace QuantumProver.ElegantJointMeasurement.HilbertChoi

section Unvectorization

variable {I : Type} [Fintype I] [DecidableEq I]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

def unvectorize (v : BlockSpace I E) : EuclideanSpace ℂ I →L[ℂ] E :=
  ∑ i, (ContinuousLinearMap.toSpanSingleton ℂ (v i)).comp
    (PiLp.proj 2 (fun _ : I => ℂ) i)

theorem unvectorize_apply (v : BlockSpace I E) (x : EuclideanSpace ℂ I) :
    unvectorize v x = ∑ i, x i • v i := by
  simp [unvectorize]

@[simp] theorem unvectorize_single (v : BlockSpace I E) (i : I) :
    unvectorize v (EuclideanSpace.single i 1) = v i := by
  simp [unvectorize_apply, Pi.single_apply]

theorem unvectorize_adjoint_apply (v : BlockSpace I E) (x : E) (i : I) :
    (unvectorize v).adjoint x i = inner ℂ (v i) x := by
  have h := ContinuousLinearMap.adjoint_inner_right (unvectorize v)
    (EuclideanSpace.single i 1) x
  simpa [EuclideanSpace.inner_single_left] using h

def matrixOperator (X : Matrix I I ℂ) : EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ I :=
  (Matrix.toEuclideanLin X).toContinuousLinearMap

theorem matrixOperator_apply (X : Matrix I I ℂ) (x : EuclideanSpace ℂ I) (i : I) :
    matrixOperator X x i = ∑ j, X i j * x j := rfl

def krausAction (v : BlockSpace I E) (X : Matrix I I ℂ) : E →L[ℂ] E :=
  (unvectorize v).comp ((matrixOperator X).comp (unvectorize v).adjoint)

theorem krausAction_eq_rankOne_blocks (v : BlockSpace I E) (X : Matrix I I ℂ) :
    krausAction v X = ∑ i, ∑ j, X i j • rankOne ℂ (v i) (v j) := by
  ext x
  simp only [krausAction, comp_apply, unvectorize_apply, matrixOperator_apply,
    unvectorize_adjoint_apply, Finset.sum_smul, mul_smul, rankOne_apply,
    sum_apply, smul_apply]

def blockMap (i j : I) :
    (BlockSpace I E →L[ℂ] BlockSpace I E) →L[ℂ] (E →L[ℂ] E) :=
  (ContinuousLinearMap.compL ℂ E (BlockSpace I E) E (PiLp.proj 2 (fun _ : I => E) i)).comp
    ((ContinuousLinearMap.compL ℂ E (BlockSpace I E) (BlockSpace I E)).flip (insert j))

@[simp] theorem blockMap_apply (i j : I) (D : BlockSpace I E →L[ℂ] BlockSpace I E) :
    blockMap i j D =
      (PiLp.proj 2 (fun _ : I => E) i).comp (D.comp (insert j)) := rfl

@[simp] theorem blockMap_rankOne (i j : I) (v w : BlockSpace I E) :
    blockMap i j (rankOne ℂ v w) = rankOne ℂ (v i) (w j) := by
  ext x
  simp [blockMap_apply, rankOne_apply, PiLp.inner_apply, insert_apply_apply,
    Pi.single_apply, inner_smul_right, apply_ite]

def decode (X : Matrix I I ℂ) :
    (BlockSpace I E →L[ℂ] BlockSpace I E) →L[ℂ] (E →L[ℂ] E) :=
  ∑ i, ∑ j, X i j • blockMap i j

@[simp] theorem decode_choi (Φ : Matrix I I ℂ →ₗ[ℂ] (E →L[ℂ] E))
    (X : Matrix I I ℂ) : decode X (choi Φ) = Φ X := by
  simpa [decode] using (action_eq_choi_blocks Φ X).symm

@[simp] theorem decode_rankOne (X : Matrix I I ℂ) (v : BlockSpace I E) :
    decode X (rankOne ℂ v v) = krausAction v X := by
  rw [krausAction_eq_rankOne_blocks]
  simp only [decode, sum_apply, smul_apply, blockMap_rankOne]

theorem krausColumns_hasSum_action {L : Type*} (b : HilbertBasis L ℂ (BlockSpace I E))
    (Φ : Matrix I I ℂ →ₗ[ℂ] (E →L[ℂ] E))
    (hΦ : CompletelyPositive Φ)
    (htrace : Summable (fun l => (inner ℂ (choi Φ (b l)) (b l)).re))
    (X : Matrix I I ℂ) :
    HasSum (fun l => krausAction (squareRootColumn b (choi Φ) l) X) (Φ X) := by
  simpa using (decode X).hasSum
    (squareRootColumns_hasSum b (choi Φ) (choi_isPositive Φ hΦ) htrace)

end Unvectorization
end QuantumProver.ElegantJointMeasurement.HilbertChoi

namespace QuantumProver.ElegantJointMeasurement.HilbertChoi

section MeasurableColumns

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [MeasurableSpace E] [BorelSpace E]
variable [MeasurableSpace (E →L[ℂ] E)] [BorelSpace (E →L[ℂ] E)]
variable {P L : Type*} [MeasurableSpace P]

theorem measurable_squareRootColumn (b : HilbertBasis L ℂ E)
    (D : P → E →L[ℂ] E) (hD : Measurable D) (l : L) :
    Measurable (fun p => squareRootColumn b (D p) l) := by
  exact (ContinuousLinearMap.apply ℂ E (b l)).continuous.measurable.comp
    (CFC.measurable_sqrt.comp hD)

end MeasurableColumns
end QuantumProver.ElegantJointMeasurement.HilbertChoi

namespace QuantumProver.ElegantJointMeasurement.HilbertChoi

section ColumnBounds

variable {I : Type} [Fintype I] [DecidableEq I]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem krausAction_isPositive (v : BlockSpace I E) (X : Matrix I I ℂ)
    (hX : X.PosSemidef) : (krausAction v X).IsPositive := by
  have hM : (matrixOperator X).IsPositive :=
    (LinearMap.isPositive_toContinuousLinearMap_iff _).mpr
      (Matrix.isPositive_toEuclideanLin_iff.mpr hX)
  simpa only [krausAction, comp_assoc] using hM.conj_adjoint (unvectorize v)

def unvectorizeMap : BlockSpace I E →L[ℂ] (EuclideanSpace ℂ I →L[ℂ] E) :=
  ∑ i, (ContinuousLinearMap.smulRightL ℂ (EuclideanSpace ℂ I) E
    (PiLp.proj 2 (fun _ : I => ℂ) i)).comp (PiLp.proj 2 (fun _ : I => E) i)

@[simp] theorem unvectorizeMap_apply (v : BlockSpace I E) :
    unvectorizeMap v = unvectorize v := by
  ext x
  simp [unvectorizeMap, unvectorize_apply]

theorem norm_krausAction_le_column_mass (v : BlockSpace I E) (X : Matrix I I ℂ) :
    ‖krausAction v X‖ ≤ ‖decode (E := E) X‖ * ‖v‖ ^ 2 := by
  rw [← decode_rankOne]
  simpa only [norm_rankOne, sq] using
    (decode X).le_opNorm (rankOne ℂ v v)

theorem krausColumns_summable_norm_action {L : Type*}
    (b : HilbertBasis L ℂ (BlockSpace I E))
    (Φ : Matrix I I ℂ →ₗ[ℂ] (E →L[ℂ] E))
    (hΦ : CompletelyPositive Φ)
    (htrace : Summable (fun l => (inner ℂ (choi Φ (b l)) (b l)).re))
    (X : Matrix I I ℂ) :
    Summable (fun l => ‖krausAction (squareRootColumn b (choi Φ) l) X‖) := by
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) ?_
    (htrace.mul_left ‖decode (E := E) X‖)
  intro l
  calc
    ‖krausAction (squareRootColumn b (choi Φ) l) X‖
      ≤ ‖decode (E := E) X‖ * ‖squareRootColumn b (choi Φ) l‖ ^ 2 :=
        norm_krausAction_le_column_mass _ X
    _ = ‖decode (E := E) X‖ * (inner ℂ (choi Φ (b l)) (b l)).re := by
      rw [squareRootColumn_norm_sq b (choi Φ) (choi_isPositive Φ hΦ)]

end ColumnBounds

section MeasurableKraus

variable {I : Type} [Fintype I] [DecidableEq I]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [MeasurableSpace (BlockSpace I E)] [BorelSpace (BlockSpace I E)]
variable [MeasurableSpace (BlockSpace I E →L[ℂ] BlockSpace I E)]
variable [BorelSpace (BlockSpace I E →L[ℂ] BlockSpace I E)]
variable [MeasurableSpace (EuclideanSpace ℂ I →L[ℂ] E)]
variable [BorelSpace (EuclideanSpace ℂ I →L[ℂ] E)]
variable {P L : Type*} [MeasurableSpace P]

theorem measurable_krausColumn (b : HilbertBasis L ℂ (BlockSpace I E))
    (D : P → BlockSpace I E →L[ℂ] BlockSpace I E)
    (hD : Measurable D) (l : L) :
    Measurable (fun p => unvectorize (squareRootColumn b (D p) l)) := by
  simpa only [Function.comp_def, unvectorizeMap_apply] using
    (unvectorizeMap (I := I) (E := E)).continuous.measurable.comp
      (measurable_squareRootColumn b D hD l)

end MeasurableKraus
end QuantumProver.ElegantJointMeasurement.HilbertChoi

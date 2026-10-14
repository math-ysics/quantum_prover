import QuantumProver.InformationTheory.ElegantJointMeasurement.HilbertChoi
import QuantumProver.LinearAlgebra.NuclearOperator
import QuantumProver.LinearAlgebra.HilbertNuclearTrace

noncomputable section

open scoped BigOperators InnerProduct ComplexConjugate ComplexOrder
open InnerProductSpace ContinuousLinearMap
open QuantumProver.ElegantJointMeasurement.HilbertChoi

namespace QuantumProver.ElegantJointMeasurement.NuclearChoi

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {L : Type*}

abbrev Nuclear (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] := QuantumProver.NuclearOperator.Nuclear ℂ E E

def nuclearColumn (b : HilbertBasis L ℂ E) (D : E →L[ℂ] E) (l : L) : Nuclear E :=
  QuantumProver.NuclearOperator.rankOne (innerSL ℂ (squareRootColumn b D l))
    (squareRootColumn b D l)

@[simp] theorem toOperator_nuclearColumn (b : HilbertBasis L ℂ E)
    (D : E →L[ℂ] E) (l : L) :
    QuantumProver.NuclearOperator.toOperator (nuclearColumn b D l) =
      rankOne ℂ (squareRootColumn b D l) (squareRootColumn b D l) := by
  rw [nuclearColumn, QuantumProver.NuclearOperator.toOperator_rankOne]
  rfl

@[simp] theorem norm_nuclearColumn (b : HilbertBasis L ℂ E)
    (D : E →L[ℂ] E) (hD : D.IsPositive) (l : L) :
    ‖nuclearColumn b D l‖ = (inner ℂ (D (b l)) (b l)).re := by
  rw [nuclearColumn, QuantumProver.NuclearOperator.norm_rankOne, innerSL_apply_norm, ← sq,
    squareRootColumn_norm_sq b D hD]

theorem summable_column_cost (b : HilbertBasis L ℂ E) (D : E →L[ℂ] E)
    (hD : D.IsPositive)
    (htrace : Summable (fun l => (inner ℂ (D (b l)) (b l)).re)) :
    Summable (fun l => ‖innerSL ℂ (squareRootColumn b D l)‖ *
      ‖squareRootColumn b D l‖) := by
  simpa only [innerSL_apply_norm, ← sq, squareRootColumn_norm_sq b D hD] using htrace

def positiveLift (b : HilbertBasis L ℂ E) (D : E →L[ℂ] E) (hD : D.IsPositive)
    (htrace : Summable (fun l => (inner ℂ (D (b l)) (b l)).re)) : Nuclear E :=
  QuantumProver.NuclearOperator.ofSeries
    (fun l => innerSL ℂ (squareRootColumn b D l))
    (fun l => squareRootColumn b D l) (summable_column_cost b D hD htrace)

theorem nuclearColumns_hasSum (b : HilbertBasis L ℂ E) (D : E →L[ℂ] E)
    (hD : D.IsPositive)
    (htrace : Summable (fun l => (inner ℂ (D (b l)) (b l)).re)) :
    HasSum (nuclearColumn b D) (positiveLift b D hD htrace) :=
  QuantumProver.NuclearOperator.hasSum_rankOne _ _ (summable_column_cost b D hD htrace)

theorem toOperator_positiveLift (b : HilbertBasis L ℂ E) (D : E →L[ℂ] E)
    (hD : D.IsPositive)
    (htrace : Summable (fun l => (inner ℂ (D (b l)) (b l)).re)) :
    QuantumProver.NuclearOperator.toOperator (positiveLift b D hD htrace) = D := by
  have ht := (QuantumProver.NuclearOperator.toOperator (𝕜 := ℂ) (E := E) (F := E)).hasSum
    (nuclearColumns_hasSum b D hD htrace)
  have hh : HasSum
      (fun l => rankOne ℂ (squareRootColumn b D l) (squareRootColumn b D l))
      (QuantumProver.NuclearOperator.toOperator (positiveLift b D hD htrace)) := by
    simpa only [toOperator_nuclearColumn] using ht
  exact hh.unique (squareRootColumns_hasSum b D hD htrace)

theorem positiveLift_eq_of_toOperator (b : HilbertBasis L ℂ E) (D : E →L[ℂ] E)
    (hD : D.IsPositive)
    (htrace : Summable (fun l => (inner ℂ (D (b l)) (b l)).re))
    (T : Nuclear E) (hT : QuantumProver.NuclearOperator.toOperator T = D) :
    positiveLift b D hD htrace = T := by
  apply QuantumProver.NuclearOperator.toOperator_injective
  rw [toOperator_positiveLift, hT]

theorem norm_positiveLift_le_diagonalTrace (b : HilbertBasis L ℂ E)
    (D : E →L[ℂ] E) (hD : D.IsPositive)
    (htrace : Summable (fun l => (inner ℂ (D (b l)) (b l)).re)) :
    ‖positiveLift b D hD htrace‖ ≤ ∑' l, (inner ℂ (D (b l)) (b l)).re := by
  simpa only [positiveLift, innerSL_apply_norm, ← sq,
    squareRootColumn_norm_sq b D hD] using
      QuantumProver.NuclearOperator.norm_ofSeries_le _ _ (summable_column_cost b D hD htrace)

theorem tendsto_finite_nuclearColumns (b : HilbertBasis ℕ ℂ E)
    (D : E →L[ℂ] E) (hD : D.IsPositive)
    (htrace : Summable (fun l => (inner ℂ (D (b l)) (b l)).re)) :
    Filter.Tendsto (fun n => ∑ l ∈ Finset.range n, nuclearColumn b D l)
      Filter.atTop (nhds (positiveLift b D hD htrace)) :=
  (nuclearColumns_hasSum b D hD htrace).tendsto_sum_nat

end QuantumProver.ElegantJointMeasurement.NuclearChoi

namespace QuantumProver.ElegantJointMeasurement.NuclearChoi

section FiniteSourceAction

variable {I : Type} [Fintype I] [DecidableEq I]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

def nuclearKrausAction (v : BlockSpace I E) (X : Matrix I I ℂ) : Nuclear E :=
  ∑ i, ∑ j, X i j • QuantumProver.NuclearOperator.rankOne (innerSL ℂ (v j)) (v i)

@[simp] theorem toOperator_nuclearKrausAction (v : BlockSpace I E) (X : Matrix I I ℂ) :
    QuantumProver.NuclearOperator.toOperator (nuclearKrausAction v X) = krausAction v X := by
  rw [nuclearKrausAction, map_sum]
  simp only [map_sum, map_smul, QuantumProver.NuclearOperator.toOperator_rankOne,
    ← InnerProductSpace.rankOne_def, krausAction_eq_rankOne_blocks]

def inputEntryMass (X : Matrix I I ℂ) : ℝ := ∑ i, ∑ j, ‖X i j‖

theorem norm_nuclearKrausAction_le (v : BlockSpace I E) (X : Matrix I I ℂ) :
    ‖nuclearKrausAction v X‖ ≤ inputEntryMass X * ‖v‖ ^ 2 := by
  calc
    ‖nuclearKrausAction v X‖
        ≤ ∑ i, ∑ j, ‖X i j • QuantumProver.NuclearOperator.rankOne (innerSL ℂ (v j)) (v i)‖ := by
      unfold nuclearKrausAction
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i _ => norm_sum_le _ _))
    _ = ∑ i, ∑ j, ‖X i j‖ * (‖v j‖ * ‖v i‖) := by
      simp only [norm_smul, QuantumProver.NuclearOperator.norm_rankOne, innerSL_apply_norm]
    _ ≤ ∑ i, ∑ j, ‖X i j‖ * ‖v‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      rw [sq]
      exact mul_le_mul (PiLp.norm_apply_le v j) (PiLp.norm_apply_le v i)
        (norm_nonneg _) (norm_nonneg _)
    _ = inputEntryMass X * ‖v‖ ^ 2 := by
      simp only [inputEntryMass, Finset.sum_mul]

def operationOperator (Φ : Matrix I I ℂ →ₗ[ℂ] Nuclear E) :
    Matrix I I ℂ →ₗ[ℂ] (E →L[ℂ] E) :=
  (QuantumProver.NuclearOperator.toOperator (𝕜 := ℂ) (E := E) (F := E)).toLinearMap.comp Φ

@[simp] theorem operationOperator_apply (Φ : Matrix I I ℂ →ₗ[ℂ] Nuclear E)
    (X : Matrix I I ℂ) :
    operationOperator Φ X = QuantumProver.NuclearOperator.toOperator (Φ X) := rfl

theorem nuclearKrausColumns_summable {L : Type*}
    (b : HilbertBasis L ℂ (BlockSpace I E)) (Φ : Matrix I I ℂ →ₗ[ℂ] Nuclear E)
    (hΦ : CompletelyPositive (operationOperator Φ))
    (htrace : Summable (fun l =>
      (inner ℂ (choi (operationOperator Φ) (b l)) (b l)).re))
    (X : Matrix I I ℂ) :
    Summable (fun l => nuclearKrausAction
      (squareRootColumn b (choi (operationOperator Φ)) l) X) := by
  apply (htrace.mul_left (inputEntryMass X)).of_norm_bounded
  intro l
  calc
    ‖nuclearKrausAction (squareRootColumn b (choi (operationOperator Φ)) l) X‖
      ≤ inputEntryMass X * ‖squareRootColumn b (choi (operationOperator Φ)) l‖ ^ 2 :=
        norm_nuclearKrausAction_le _ X
    _ = inputEntryMass X *
        (inner ℂ (choi (operationOperator Φ) (b l)) (b l)).re := by
      rw [squareRootColumn_norm_sq b _ (choi_isPositive _ hΦ)]

theorem nuclearKrausColumns_hasSum_action {L : Type*}
    (b : HilbertBasis L ℂ (BlockSpace I E)) (Φ : Matrix I I ℂ →ₗ[ℂ] Nuclear E)
    (hΦ : CompletelyPositive (operationOperator Φ))
    (htrace : Summable (fun l =>
      (inner ℂ (choi (operationOperator Φ) (b l)) (b l)).re))
    (X : Matrix I I ℂ) :
    HasSum (fun l => nuclearKrausAction
      (squareRootColumn b (choi (operationOperator Φ)) l) X) (Φ X) := by
  have hs := nuclearKrausColumns_summable b Φ hΦ htrace X
  have ht := (QuantumProver.NuclearOperator.toOperator (𝕜 := ℂ) (E := E) (F := E)).hasSum hs.hasSum
  have hh : HasSum
      (fun l => krausAction (squareRootColumn b (choi (operationOperator Φ)) l) X)
      (QuantumProver.NuclearOperator.toOperator
        (∑' l, nuclearKrausAction (squareRootColumn b (choi (operationOperator Φ)) l) X)) := by
    simpa only [toOperator_nuclearKrausAction] using ht
  have heq : (∑' l, nuclearKrausAction
      (squareRootColumn b (choi (operationOperator Φ)) l) X) = Φ X := by
    apply QuantumProver.NuclearOperator.toOperator_injective
    exact hh.unique (krausColumns_hasSum_action b (operationOperator Φ) hΦ htrace X)
  simpa only [heq] using hs.hasSum

end FiniteSourceAction
end QuantumProver.ElegantJointMeasurement.NuclearChoi

namespace QuantumProver.ElegantJointMeasurement.NuclearChoi

section NuclearContinuity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

def rankOneLinear : (E →L[ℂ] ℂ) →ₗ[ℂ] E →ₗ[ℂ] Nuclear E where
  toFun φ :=
    { toFun := fun y => QuantumProver.NuclearOperator.rankOne φ y
      map_add' := by
        intro y z
        apply QuantumProver.NuclearOperator.toOperator_injective
        ext x
        simp [smul_add]
      map_smul' := by
        intro c y
        apply QuantumProver.NuclearOperator.toOperator_injective
        ext x
        simp [smul_smul, mul_comm] }
  map_add' := by
    intro φ ψ
    ext y
    apply QuantumProver.NuclearOperator.toOperator_injective
    ext x
    simp [add_smul]
  map_smul' := by
    intro c φ
    ext y
    apply QuantumProver.NuclearOperator.toOperator_injective
    ext x
    simp [smul_smul]

def rankOneBilinear : (E →L[ℂ] ℂ) →L[ℂ] E →L[ℂ] Nuclear E :=
  LinearMap.mkContinuous₂ rankOneLinear 1 (by
    intro φ y
    change ‖QuantumProver.NuclearOperator.rankOne φ y‖ ≤ 1 * ‖φ‖ * ‖y‖
    simpa only [one_mul] using QuantumProver.NuclearOperator.norm_rankOne_le φ y)

@[simp] theorem rankOneBilinear_apply (φ : E →L[ℂ] ℂ) (y : E) :
    rankOneBilinear φ y = QuantumProver.NuclearOperator.rankOne φ y := rfl

theorem continuous_nuclearPositiveRankOne :
    Continuous (fun v : E => QuantumProver.NuclearOperator.rankOne (innerSL ℂ v) v) := by
  change Continuous (fun v : E => rankOneBilinear (innerSL ℂ v) v)
  fun_prop

variable {I : Type} [Fintype I] [DecidableEq I]

theorem continuous_nuclearKrausAction (X : Matrix I I ℂ) :
    Continuous (fun v : BlockSpace I E => nuclearKrausAction v X) := by
  change Continuous (fun v : BlockSpace I E =>
    ∑ i, ∑ j, X i j • rankOneBilinear (innerSL ℂ (v j)) (v i))
  fun_prop

end NuclearContinuity

section MeasurableNuclearColumns

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [MeasurableSpace E] [BorelSpace E]
variable [MeasurableSpace (E →L[ℂ] E)] [BorelSpace (E →L[ℂ] E)]
variable [MeasurableSpace (Nuclear E)] [BorelSpace (Nuclear E)]
variable {P : Type*} [MeasurableSpace P]

theorem measurable_positiveLift [SecondCountableTopology E] (b : HilbertBasis ℕ ℂ E)
    (D : P → E →L[ℂ] E) (hD : Measurable D)
    (hpos : ∀ p, (D p).IsPositive)
    (htrace : ∀ p, Summable (fun l => (inner ℂ (D p (b l)) (b l)).re)) :
    Measurable (fun p => positiveLift b (D p) (hpos p) (htrace p)) := by
  have hc (l : ℕ) : MeasureTheory.StronglyMeasurable (fun p => nuclearColumn b (D p) l) :=
    continuous_nuclearPositiveRankOne.comp_stronglyMeasurable
      (measurable_squareRootColumn b D hD l).stronglyMeasurable
  apply measurable_of_tendsto_metrizable
    (f := fun n p => ∑ l ∈ Finset.range n, nuclearColumn b (D p) l)
  · intro n
    exact (Finset.stronglyMeasurable_fun_sum _ (fun l hl => hc l)).measurable
  · exact tendsto_pi_nhds.mpr (fun p => tendsto_finite_nuclearColumns b (D p) (hpos p) (htrace p))

end MeasurableNuclearColumns

section MeasurableNuclearActions

variable {I : Type} [Fintype I] [DecidableEq I]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [MeasurableSpace (BlockSpace I E)] [BorelSpace (BlockSpace I E)]
variable [MeasurableSpace (BlockSpace I E →L[ℂ] BlockSpace I E)]
variable [BorelSpace (BlockSpace I E →L[ℂ] BlockSpace I E)]
variable [MeasurableSpace (Nuclear E)] [BorelSpace (Nuclear E)]
variable {P L : Type*} [MeasurableSpace P]

theorem measurable_nuclearKrausColumnAction (b : HilbertBasis L ℂ (BlockSpace I E))
    (D : P → BlockSpace I E →L[ℂ] BlockSpace I E) (hD : Measurable D)
    (l : L) (X : Matrix I I ℂ) :
    Measurable (fun p => nuclearKrausAction (squareRootColumn b (D p) l) X) :=
  (continuous_nuclearKrausAction X).measurable.comp
    (measurable_squareRootColumn b D hD l)

end MeasurableNuclearActions
end QuantumProver.ElegantJointMeasurement.NuclearChoi

namespace QuantumProver.ElegantJointMeasurement.NuclearChoi

section PositiveTrace

variable {E L : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem re_trace_positiveLift (b : HilbertBasis L ℂ E) (D : E →L[ℂ] E)
    (hD : D.IsPositive)
    (htrace : Summable (fun l => (inner ℂ (D (b l)) (b l)).re)) :
    (QuantumProver.HilbertNuclearTrace.trace (positiveLift b D hD htrace)).re =
      ∑' l, (inner ℂ (D (b l)) (b l)).re := by
  change RCLike.re (QuantumProver.HilbertNuclearTrace.trace (positiveLift b D hD htrace)) = _
  rw [QuantumProver.HilbertNuclearTrace.re_trace_eq_tsum_re_diagonal b]
  apply tsum_congr
  intro l
  rw [toOperator_positiveLift]
  exact inner_re_symm (𝕜 := ℂ) _ _

theorem norm_positiveLift_eq_diagonalTrace (b : HilbertBasis L ℂ E)
    (D : E →L[ℂ] E) (hD : D.IsPositive)
    (htrace : Summable (fun l => (inner ℂ (D (b l)) (b l)).re)) :
    ‖positiveLift b D hD htrace‖ = ∑' l, (inner ℂ (D (b l)) (b l)).re := by
  apply le_antisymm (norm_positiveLift_le_diagonalTrace b D hD htrace)
  rw [← re_trace_positiveLift b D hD htrace]
  exact QuantumProver.HilbertNuclearTrace.re_trace_le_norm (𝕜 := ℂ) (E := E)
    (positiveLift b D hD htrace)

theorem norm_positive_nuclear_eq_re_trace (b : HilbertBasis L ℂ E)
    (T : Nuclear E) (hT : (QuantumProver.NuclearOperator.toOperator T).IsPositive) :
    ‖T‖ = (QuantumProver.HilbertNuclearTrace.trace T).re := by
  let D : E →L[ℂ] E := QuantumProver.NuclearOperator.toOperator T
  have hd0 : Summable (fun l => RCLike.re (inner ℂ (b l) (D (b l)))) :=
    ((QuantumProver.HilbertNuclearTrace.hasSum_diagonal b T).mapL RCLike.reCLM).summable
  have hd : Summable (fun l => (inner ℂ (D (b l)) (b l)).re) := by
    convert hd0 using 1
    funext l
    exact inner_re_symm (𝕜 := ℂ) _ _
  have heq : positiveLift b D hT hd = T :=
    positiveLift_eq_of_toOperator b D hT hd T rfl
  calc
    ‖T‖ = ‖positiveLift b D hT hd‖ := by rw [heq]
    _ = ∑' l, (inner ℂ (D (b l)) (b l)).re :=
      norm_positiveLift_eq_diagonalTrace b D hT hd
    _ = (QuantumProver.HilbertNuclearTrace.trace T).re := by
      rw [← re_trace_positiveLift b D hT hd, heq]

end PositiveTrace
end QuantumProver.ElegantJointMeasurement.NuclearChoi

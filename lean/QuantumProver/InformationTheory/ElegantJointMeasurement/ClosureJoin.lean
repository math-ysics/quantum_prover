import QuantumProver.InformationTheory.ElegantJointMeasurement.TranscriptPOVM
import QuantumProver.InformationTheory.ElegantJointMeasurement.AugmentedMoments

open scoped BigOperators ComplexConjugate ComplexOrder
open InnerProductSpace QuantumProver.ElegantJointMeasurement.Augmented

namespace QuantumProver.ElegantJointMeasurement.ClosureJoin

noncomputable section

set_option maxHeartbeats 400000

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

def effectOperator : Matrix (Index κ) (Index κ) ℂ →ₗ[ℂ] (Ket κ →L[ℂ] Ket κ) :=
  LinearMap.toContinuousLinearMap.toLinearMap.comp Matrix.toEuclideanLin.toLinearMap

theorem effectOperator_rankOne (z : Ket κ) :
    effectOperator (effectMatrix z) = rankOne ℂ z z := by
  unfold effectOperator
  simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    effectMatrix_eq_rankOne, LinearEquiv.apply_symm_apply]
  apply ContinuousLinearMap.coe_injective
  rfl

theorem effectOperator_one : effectOperator (1 : Matrix (Index κ) (Index κ) ℂ) =
    ContinuousLinearMap.id ℂ (Ket κ) := by
  unfold effectOperator
  simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    Matrix.toEuclideanLin, Matrix.toLpLin_one]
  apply ContinuousLinearMap.coe_injective
  rfl

theorem effectOperator_positive_iff (F : Matrix (Index κ) (Index κ) ℂ) :
    (effectOperator F).IsPositive ↔ F.PosSemidef := by
  change (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin F)).IsPositive ↔ F.PosSemidef
  rw [LinearMap.isPositive_toContinuousLinearMap_iff, Matrix.isPositive_toEuclideanLin_iff]

theorem effectOperator_upper_iff (F : Matrix (Index κ) (Index κ) ℂ) :
    (ContinuousLinearMap.id ℂ (Ket κ) - effectOperator F).IsPositive ↔
      (1 - F).PosSemidef := by
  rw [← effectOperator_one, ← map_sub, effectOperator_positive_iff]

def rawPair (w : ℝ) (p : Local κ × Local κ) : Local κ × Local κ :=
  (Real.sqrt w • p.1, p.2)

theorem rawPair_augmented (β : κ → ℝ) (k : κ) (w : ℝ)
    (hw : 0 ≤ w) (p : Local κ × Local κ) :
    augmentedMap β k (rawPair w p) = w • augmentedMap β k p := by
  simpa only [rawPair, one_smul, mul_one, Real.sq_sqrt hw] using
    augmentedMap_smul β k (Real.sqrt w) 1 p

theorem rawPair_effect (w : ℝ) (hw : 0 ≤ w) (p : Local κ × Local κ) :
    effectMatrix (product (rawPair w p)) = w • effectMatrix (product p) := by
  rw [rawPair]
  have hprod := product_smul (Real.sqrt w) 1 p
  simp only [one_smul, mul_one] at hprod
  rw [hprod, effectMatrix_smul, Real.sq_sqrt hw]

def pairTailCost (β : κ → ℝ) (k : κ) (p : Local κ × Local κ) : ℝ :=
  ‖(QuantumProver.ElegantJointMeasurement.ResourceCode.tailContraction β (localMatrix p.1) (localMatrix p.2) k).det‖

theorem rawPair_cost (β : κ → ℝ) (k : κ) (w : ℝ) (hw : 0 ≤ w)
    (p : Local κ × Local κ) :
    pairTailCost β k (rawPair w p) = w * pairTailCost β k p := by
  have h := congrArg Prod.snd (rawPair_augmented β k w hw p)
  change ‖(tailMatrix β k (product (rawPair w p))).det‖ =
    w * ‖(tailMatrix β k (product p)).det‖ at h
  simpa only [tailMatrix_product, pairTailCost] using h

theorem rawPair_effect_sum {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (p : ι → Local κ × Local κ) (hw : ∀ i, 0 ≤ w i)
    (F : Matrix (Index κ) (Index κ) ℂ)
    (hF : (∑ i, w i • effectMatrix (product (p i))) = F) :
    (∑ i, rankOne ℂ (product (rawPair (w i) (p i)))
      (product (rawPair (w i) (p i)))) = effectOperator F := by
  have hraw : (∑ i, effectMatrix (product (rawPair (w i) (p i)))) = F := by
    simpa only [rawPair_effect _ (hw _)] using hF
  calc
    (∑ i, rankOne ℂ (product (rawPair (w i) (p i)))
      (product (rawPair (w i) (p i)))) =
        ∑ i, effectOperator (effectMatrix (product (rawPair (w i) (p i)))) := by
          simp only [effectOperator_rankOne]
    _ = effectOperator (∑ i, effectMatrix (product (rawPair (w i) (p i)))) :=
      (map_sum effectOperator _ _).symm
    _ = effectOperator F := congrArg effectOperator hraw

theorem weighted_ejm_cost_lower {ι : Type*} [Fintype ι]
    (β : κ → ℝ) (hβ : ∑ k, β k ^ 2 = 1)
    (weights : ι → ℝ) (p : ι → Local κ × Local κ) (hw : ∀ i, 0 ≤ weights i)
    (F : Matrix (Index κ) (Index κ) ℂ)
    (hF : (∑ i, weights i • effectMatrix (product (p i))) = F)
    (u v w : ℝ) (hsphere : u ^ 2 + v ^ 2 + w ^ 2 = 3)
    (k : κ) (x : ℝ) (hx : β k ^ 2 = x)
    (hupper : (ContinuousLinearMap.id ℂ (Ket κ) - effectOperator F).IsPositive)
    (hcompression : (QuantumProver.ElegantJointMeasurement.ResourceCode.codeContinuous β).adjoint ∘L
      (effectOperator F ∘L QuantumProver.ElegantJointMeasurement.ResourceCode.codeContinuous β) =
        rankOne ℂ (QuantumProver.ElegantJointMeasurement.ResourceCode.ejmKet u v w) (QuantumProver.ElegantJointMeasurement.ResourceCode.ejmKet u v w)) :
    (1 / 4 : ℝ) * |1 - 2 * x| ≤ ∑ i, weights i * pairTailCost β k (p i) := by
  classical
  let A : ι → Matrix (Fin 2) κ ℂ := fun i => localMatrix (rawPair (weights i) (p i)).1
  let B : ι → Matrix (Fin 2) κ ℂ := fun i => localMatrix (rawPair (weights i) (p i)).2
  have hsum : (∑ i, rankOne ℂ (QuantumProver.ElegantJointMeasurement.ResourceCode.productKet (A i) (B i))
      (QuantumProver.ElegantJointMeasurement.ResourceCode.productKet (A i) (B i))) = effectOperator F :=
    rawPair_effect_sum weights p hw F hF
  have hlower := QuantumProver.ElegantJointMeasurement.ResourceCode.ejm_physical_tail_det_lower_bound
    Finset.univ β hβ A B u v w hsphere k x hx
    (by rw [hsum]; exact hupper) (by rw [hsum]; exact hcompression)
  calc
    (1 / 4 : ℝ) * |1 - 2 * x| ≤
        ∑ i, ‖(QuantumProver.ElegantJointMeasurement.ResourceCode.tailContraction β (A i) (B i) k).det‖ := hlower
    _ = ∑ i, weights i * pairTailCost β k (p i) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact rawPair_cost β k (weights i) (hw i) (p i)

theorem ejm_necessary_of_cost_representation
    (β : κ → ℝ) (hβ : ∑ k, β k ^ 2 = 1) (k : κ) (x C : ℝ) (hx : β k ^ 2 = x)
    (u v w : Fin 4 → ℝ) (hsphere : ∀ j, u j ^ 2 + v j ^ 2 + w j ^ 2 = 3)
    (F : Fin 4 → Matrix (Index κ) (Index κ) ℂ) (c : Fin 4 → ℝ)
    (hupper : ∀ j, (ContinuousLinearMap.id ℂ (Ket κ) - effectOperator (F j)).IsPositive)
    (hcompression : ∀ j, (QuantumProver.ElegantJointMeasurement.ResourceCode.codeContinuous β).adjoint ∘L
      (effectOperator (F j) ∘L QuantumProver.ElegantJointMeasurement.ResourceCode.codeContinuous β) =
        rankOne ℂ (QuantumProver.ElegantJointMeasurement.ResourceCode.ejmKet (u j) (v j) (w j))
          (QuantumProver.ElegantJointMeasurement.ResourceCode.ejmKet (u j) (v j) (w j)))
    (hrepresentation : ∀ j, ∃ (n : ℕ) (weights : Fin n → ℝ) (p : Fin n → Local κ × Local κ),
      (∀ i, 0 ≤ weights i) ∧
      (∑ i, weights i • effectMatrix (product (p i))) = F j ∧
      (∑ i, weights i * pairTailCost β k (p i)) = c j)
    (hcost : ∑ j, c j ≤ C) : |1 - 2 * x| ≤ C := by
  have hper : ∀ j, (1 / 4 : ℝ) * |1 - 2 * x| ≤ c j := by
    intro j
    obtain ⟨n, weights, p, hw, hF, hcosteq⟩ := hrepresentation j
    rw [← hcosteq]
    exact weighted_ejm_cost_lower β hβ weights p hw (F j) hF
      (u j) (v j) (w j) (hsphere j) k x hx (hupper j) (hcompression j)
  have hsum := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin 4))) => hper j)
  norm_num only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  linarith

theorem ejm_necessary_of_inherited_effect_limit {η : Type*} {l : Filter η} [l.NeBot]
    (β : κ → ℝ) (hβ : ∑ k, β k ^ 2 = 1) (k : κ) (x C : ℝ) (hx : β k ^ 2 = x)
    (u v w : Fin 4 → ℝ) (hsphere : ∀ j, u j ^ 2 + v j ^ 2 + w j ^ 2 = 3)
    (B : Fin 4 → ℝ) (f : η → Fin 4 → Augmented κ)
    (F : Fin 4 → Matrix (Index κ) (Index κ) ℂ)
    (hlim : Filter.Tendsto (fun t j => (f t j).1) l (nhds F))
    (hfinite : ∀ᶠ t in l, ∀ j, ∃ (n : ℕ) (p : Fin n → Local κ × Local κ),
      (∑ i, augmentedMap β k (p i)) = f t j)
    (htrace : ∀ᶠ t in l, ∀ j, effectMass (f t j).1 ≤ B j)
    (hcost : ∀ᶠ t in l, (∑ j, (f t j).2) ≤ C)
    (hupper : ∀ j, (ContinuousLinearMap.id ℂ (Ket κ) - effectOperator (F j)).IsPositive)
    (hcompression : ∀ j, (QuantumProver.ElegantJointMeasurement.ResourceCode.codeContinuous β).adjoint ∘L
      (effectOperator (F j) ∘L QuantumProver.ElegantJointMeasurement.ResourceCode.codeContinuous β) =
        rankOne ℂ (QuantumProver.ElegantJointMeasurement.ResourceCode.ejmKet (u j) (v j) (w j))
          (QuantumProver.ElegantJointMeasurement.ResourceCode.ejmKet (u j) (v j) (w j))) : |1 - 2 * x| ≤ C := by
  obtain ⟨c, hc0, hc, hrepr⟩ := finite_outcome_effect_limit_cost_representation
    β k B C f F hlim hfinite htrace hcost
  apply ejm_necessary_of_cost_representation β hβ k x C hx u v w hsphere F c hupper hcompression
    ?_ hc
  intro j
  obtain ⟨n, hn, weights, p, hw, hp, hsum, hF, hcosteq⟩ := hrepr j
  exact ⟨n, weights, p, hw, hF, hcosteq⟩

def directionTripletCoefficient (u v w : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  ((1 / Real.sqrt 2 : ℝ) : ℂ) •
    !![-(u : ℂ) + Complex.I * v, w; w, (u : ℂ) + Complex.I * v]

def directionEjmCoefficient (u v w : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (1 / 2 : ℂ) • QuantumProver.ElegantJointMeasurement.States.singletCoefficient +
    ((Real.sqrt 3 / 2 : ℝ) : ℂ) • directionTripletCoefficient u v w

theorem scaled_ejmCoefficient_eq_direction (u v w : ℝ) :
    QuantumProver.ElegantJointMeasurement.States.ejmCoefficient (Real.sqrt 3 * u) (Real.sqrt 3 * v) (Real.sqrt 3 * w) =
      directionEjmCoefficient u v w := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [QuantumProver.ElegantJointMeasurement.States.ejmCoefficient, QuantumProver.ElegantJointMeasurement.States.ejmNumerator, QuantumProver.ElegantJointMeasurement.States.amplitudeScale,
      QuantumProver.ElegantJointMeasurement.States.singletCoefficient, directionEjmCoefficient, directionTripletCoefficient,
      Matrix.smul_apply, div_eq_mul_inv, mul_inv_rev] <;> push_cast <;> ring

theorem scaled_direction_sphere (u v w : ℝ) (hsphere : u ^ 2 + v ^ 2 + w ^ 2 = 1) :
    (Real.sqrt 3 * u) ^ 2 + (Real.sqrt 3 * v) ^ 2 + (Real.sqrt 3 * w) ^ 2 = 3 := by
  have hs : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  simp only [mul_pow, hs]
  nlinarith [hsphere]

theorem coefficientMatrix_scaled_ejmKet (u v w : ℝ) :
    QuantumProver.ElegantJointMeasurement.ResourceCode.coefficientMatrix
      (QuantumProver.ElegantJointMeasurement.ResourceCode.ejmKet (Real.sqrt 3 * u) (Real.sqrt 3 * v) (Real.sqrt 3 * w)) =
        directionEjmCoefficient u v w := by
  rw [QuantumProver.ElegantJointMeasurement.ResourceCode.coefficientMatrix_ejmKet, scaled_ejmCoefficient_eq_direction]

def directionKet (u v w : ℝ) : QuantumProver.ElegantJointMeasurement.ResourceCode.InputSpace (Fin 2) (Fin 2) :=
  WithLp.toLp 2 (fun ij => directionEjmCoefficient u v w ij.1 ij.2)

theorem directionKet_eq_scaled_ejmKet (u v w : ℝ) :
    directionKet u v w =
      QuantumProver.ElegantJointMeasurement.ResourceCode.ejmKet (Real.sqrt 3 * u) (Real.sqrt 3 * v) (Real.sqrt 3 * w) := by
  ext ij
  exact (congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M ij.1 ij.2)
    (scaled_ejmCoefficient_eq_direction u v w)).symm

theorem unit_direction_ejm_necessary_of_inherited_effect_limit
    {η : Type*} {l : Filter η} [l.NeBot]
    (β : κ → ℝ) (hβ : ∑ k, β k ^ 2 = 1) (k : κ) (x C : ℝ) (hx : β k ^ 2 = x)
    (u v w : Fin 4 → ℝ) (hsphere : ∀ j, u j ^ 2 + v j ^ 2 + w j ^ 2 = 1)
    (B : Fin 4 → ℝ) (f : η → Fin 4 → Augmented κ)
    (F : Fin 4 → Matrix (Index κ) (Index κ) ℂ)
    (hlim : Filter.Tendsto (fun t j => (f t j).1) l (nhds F))
    (hfinite : ∀ᶠ t in l, ∀ j, ∃ (n : ℕ) (p : Fin n → Local κ × Local κ),
      (∑ i, augmentedMap β k (p i)) = f t j)
    (htrace : ∀ᶠ t in l, ∀ j, effectMass (f t j).1 ≤ B j)
    (hcost : ∀ᶠ t in l, (∑ j, (f t j).2) ≤ C)
    (hupper : ∀ j, (1 - F j).PosSemidef)
    (hcompression : ∀ j, (QuantumProver.ElegantJointMeasurement.ResourceCode.codeContinuous β).adjoint ∘L
      (effectOperator (F j) ∘L QuantumProver.ElegantJointMeasurement.ResourceCode.codeContinuous β) =
        rankOne ℂ (directionKet (u j) (v j) (w j)) (directionKet (u j) (v j) (w j))) :
    |1 - 2 * x| ≤ C := by
  apply ejm_necessary_of_inherited_effect_limit β hβ k x C hx
    (fun j => Real.sqrt 3 * u j) (fun j => Real.sqrt 3 * v j) (fun j => Real.sqrt 3 * w j)
    (fun j => scaled_direction_sphere (u j) (v j) (w j) (hsphere j))
    B f F hlim hfinite htrace hcost
  · exact fun j => (effectOperator_upper_iff (F j)).mpr (hupper j)
  · intro j
    simpa only [directionKet_eq_scaled_ejmKet] using hcompression j

end

end QuantumProver.ElegantJointMeasurement.ClosureJoin

noncomputable section
open MeasureTheory ProbabilityTheory Matrix Set Filter Function Preorder
open scoped NNReal ENNReal Topology BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace QuantumProver.ElegantJointMeasurement.ClosureJoin.RecordTransport

open QuantumProver.ElegantJointMeasurement.HilbertTranscriptPOVM

variable {R S Q : Type*} [MeasurableSpace R] [MeasurableSpace S]
  [StandardBorelSpace R] [StandardBorelSpace S] [Nonempty R] [Nonempty S]
  [Fintype Q] [DecidableEq Q]

def mapRecord (g : S → R) (ω : Transcript S) : Transcript R := fun n => g (ω n)

def mapPrefixRecord (g : S → R) (n : ℕ) (h : Prefix S n) : Prefix R n :=
  fun i => g (h i)

theorem measurable_mapRecord (g : S → R) (hg : Measurable g) :
    Measurable (mapRecord g) :=
  Measurable.of_eval fun n => hg.comp (measurable_pi_apply n)

theorem measurable_mapPrefixRecord (g : S → R) (hg : Measurable g) (n : ℕ) :
    Measurable (mapPrefixRecord g n) :=
  Measurable.of_eval fun i => hg.comp (measurable_pi_apply i)

def coarsenRecords (C : ConsistentCylinderPOVM S Q) (g : S → R)
    (hg : Measurable g) : ConsistentCylinderPOVM R Q where
  effect n B := C.effect n ((mapPrefixRecord g n) ⁻¹' B)
  empty n := by simpa only [Set.preimage_empty] using C.empty n
  positive n B hB := C.positive n _ ((measurable_mapPrefixRecord g hg n) hB)
  total n := by simpa only [Set.preimage_univ] using C.total n
  coordinate_additive n B hB hdisj i j := by
    have hd : Pairwise (fun k l => Disjoint
        ((mapPrefixRecord g n) ⁻¹' B k) ((mapPrefixRecord g n) ⁻¹' B l)) :=
      fun k l hkl => Set.disjoint_left.mpr fun x hxk hxl =>
        Set.disjoint_left.mp (hdisj hkl) hxk hxl
    simpa only [Set.preimage_iUnion] using C.coordinate_additive n
      (fun k => (mapPrefixRecord g n) ⁻¹' B k)
      (fun k => (measurable_mapPrefixRecord g hg n) (hB k)) hd i j
  consistent a b hab B hB := by
    change C.effect b ((frestrictLe₂ (π := fun _ => S) hab) ⁻¹'
      ((mapPrefixRecord g a) ⁻¹' B)) = _
    exact C.consistent a b hab _ ((measurable_mapPrefixRecord g hg a) hB)

theorem fullVectorMeasure_mapRecord
    (C : ConsistentCylinderPOVM S Q) (D : ConsistentCylinderPOVM R Q)
    (g : S → R) (hg : Measurable g)
    (hC : ∀ n B, MeasurableSet B →
      C.effect n ((mapPrefixRecord g n) ⁻¹' B) = D.effect n B) :
    C.fullVectorMeasure.map (mapRecord g) = D.fullVectorMeasure := by
  apply vectorMeasure_eq_of_prefix
  intro n B hB
  rw [VectorMeasure.map_apply _ (measurable_mapRecord g hg) ((measurable_frestrictLe n) hB)]
  change C.fullVectorMeasure ((frestrictLe (π := fun _ => S) n) ⁻¹'
    ((mapPrefixRecord g n) ⁻¹' B)) = _
  rw [C.fullVectorMeasure_prefix n _ ((measurable_mapPrefixRecord g hg n) hB),
    D.fullVectorMeasure_prefix n B hB, hC n B hB]

theorem fullBornMeasure_mapRecord
    (C : ConsistentCylinderPOVM S Q) (D : ConsistentCylinderPOVM R Q)
    (g : S → R) (hg : Measurable g)
    (hC : ∀ n B, MeasurableSet B →
      C.effect n ((mapPrefixRecord g n) ⁻¹' B) = D.effect n B)
    (ρ : Matrix Q Q ℂ) (hρ : ρ.PosSemidef) :
    (C.fullBornMeasure ρ hρ).map (mapRecord g) = D.fullBornMeasure ρ hρ := by
  ext B hB
  rw [Measure.map_apply (measurable_mapRecord g hg) hB,
    C.fullBornMeasure_apply ρ hρ _ ((measurable_mapRecord g hg) hB),
    D.fullBornMeasure_apply ρ hρ B hB]
  have he := congrArg (fun F : VectorMeasure (Transcript R) (Matrix Q Q ℂ) => F B)
    (fullVectorMeasure_mapRecord C D g hg hC)
  rw [VectorMeasure.map_apply _ (measurable_mapRecord g hg) hB] at he
  rw [he]

theorem faithfulMeasure_mapRecord [Nonempty Q]
    (C : ConsistentCylinderPOVM S Q) (D : ConsistentCylinderPOVM R Q)
    (g : S → R) (hg : Measurable g)
    (hC : ∀ n B, MeasurableSet B →
      C.effect n ((mapPrefixRecord g n) ⁻¹' B) = D.effect n B) :
    C.faithfulMeasure.map (mapRecord g) = D.faithfulMeasure := by
  rw [C.faithfulMeasure_eq_Born_faithfulInput,
    D.faithfulMeasure_eq_Born_faithfulInput]
  exact fullBornMeasure_mapRecord C D g hg hC _ ConsistentCylinderPOVM.faithfulInput_positive

theorem nullMeasurable_report_comp_mapRecord [Nonempty Q]
    (C : ConsistentCylinderPOVM S Q) (D : ConsistentCylinderPOVM R Q)
    (g : S → R) (hg : Measurable g)
    (hC : ∀ n B, MeasurableSet B →
      C.effect n ((mapPrefixRecord g n) ⁻¹' B) = D.effect n B)
    (J : Transcript R → Fin 4) (hJ : NullMeasurable J D.faithfulMeasure) :
    NullMeasurable (J ∘ mapRecord g) C.faithfulMeasure := by
  have hJ' : NullMeasurable J (C.faithfulMeasure.map (mapRecord g)) := by
    rw [faithfulMeasure_mapRecord C D g hg hC]
    exact hJ
  exact hJ'.comp_quasiMeasurePreserving
    ((measurable_mapRecord g hg).quasiMeasurePreserving C.faithfulMeasure)

theorem reportedEffect_congr_ae [Nonempty Q]
    (C : ConsistentCylinderPOVM S Q) (J L : Transcript S → Fin 4)
    (hJL : J =ᵐ[C.faithfulMeasure] L) (j : Fin 4) :
    C.reportedEffect J j = C.reportedEffect L j := by
  apply integral_congr_ae
  filter_upwards [hJL] with ω hω
  simp only [Set.indicator_apply, Set.mem_setOf_eq, hω]

theorem reportedEffect_mapRecord [Nonempty Q]
    (C : ConsistentCylinderPOVM S Q) (D : ConsistentCylinderPOVM R Q)
    (g : S → R) (hg : Measurable g)
    (hC : ∀ n B, MeasurableSet B →
      C.effect n ((mapPrefixRecord g n) ⁻¹' B) = D.effect n B)
    (J : Transcript R → Fin 4) (hJ : Measurable J) (j : Fin 4) :
    C.reportedEffect (J ∘ mapRecord g) j = D.reportedEffect J j := by
  rw [C.reportedEffect_eq_physical _ (hJ.comp (measurable_mapRecord g hg)) j,
    D.reportedEffect_eq_physical J hJ j]
  have he := congrArg (fun F : VectorMeasure (Transcript R) (Matrix Q Q ℂ) =>
      F {ω | J ω = j}) (fullVectorMeasure_mapRecord C D g hg hC)
  have hB : MeasurableSet {omega : Transcript R | J omega = j} := by
    exact measurableSet_eq_fun hJ measurable_const
  rw [VectorMeasure.map_apply _ (measurable_mapRecord g hg) hB] at he
  exact he

theorem completedReportedEffect_mapRecord [Nonempty Q]
    (C : ConsistentCylinderPOVM S Q) (D : ConsistentCylinderPOVM R Q)
    (g : S → R) (hg : Measurable g)
    (hC : ∀ n B, MeasurableSet B →
      C.effect n ((mapPrefixRecord g n) ⁻¹' B) = D.effect n B)
    (J : Transcript R → Fin 4) (hJ : NullMeasurable J D.faithfulMeasure) (j : Fin 4) :
    C.reportedEffect (J ∘ mapRecord g) j = D.reportedEffect J j := by
  let J₀ := D.rawReportVersion J hJ
  have hae : (J ∘ mapRecord g) =ᵐ[C.faithfulMeasure] (J₀ ∘ mapRecord g) := by
    have hae₀ : J =ᵐ[C.faithfulMeasure.map (mapRecord g)] J₀ := by
      rw [faithfulMeasure_mapRecord C D g hg hC]
      exact D.rawReportVersion_ae_eq J hJ
    exact ae_of_ae_map (measurable_mapRecord g hg).aemeasurable hae₀
  calc
    _ = C.reportedEffect (J₀ ∘ mapRecord g) j := reportedEffect_congr_ae C _ _ hae j
    _ = D.reportedEffect J₀ j := reportedEffect_mapRecord C D g hg hC J₀
      (D.measurable_rawReportVersion J hJ) j
    _ = _ := (D.reportedEffect_rawReportVersion J hJ j).symm

end QuantumProver.ElegantJointMeasurement.ClosureJoin.RecordTransport

end

noncomputable section
open MeasureTheory ProbabilityTheory Matrix Set Filter Function
open scoped NNReal ENNReal Topology BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace QuantumProver.ElegantJointMeasurement.ClosureJoin.RecordTransport
open QuantumProver.ElegantJointMeasurement.HilbertTranscriptPOVM QuantumProver.ElegantJointMeasurement.HilbertTranscriptPOVM.ConsistentCylinderPOVM

variable {R S Q I : Type*} [MeasurableSpace R] [MeasurableSpace S]
  [StandardBorelSpace R] [StandardBorelSpace S] [Nonempty R] [Nonempty S]
  [Fintype Q] [DecidableEq Q] [Fintype I] [DecidableEq I]

theorem density_one_sub_positive (sigma : Matrix I I ℂ)
    (hs : sigma.PosSemidef) (ht : sigma.trace = 1) : (1 - sigma).PosSemidef := by

  have hnorm : ‖sigma‖ = ‖fun i => (hs.isHermitian.eigenvalues i : ℂ)‖ := by
    conv_lhs => rw [hs.isHermitian.spectral_theorem, Unitary.conjStarAlgAut_apply]
    simp only [← Unitary.coe_star, CStarRing.norm_mul_coe_unitary,
      CStarRing.norm_coe_unitary_mul, Matrix.l2_opNorm_diagonal]
    rfl
  have htrace : sigma.trace.re = ∑ i, hs.isHermitian.eigenvalues i := by
    rw [hs.isHermitian.trace_eq_sum_eigenvalues]
    simp
  have hntrace : ‖sigma‖ ≤ sigma.trace.re := by
    rw [hnorm, htrace]
    apply (pi_norm_le_iff_of_nonneg
      (Finset.sum_nonneg (fun i _ => hs.eigenvalues_nonneg i))).mpr
    intro i
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hs.eigenvalues_nonneg i)]
    exact Finset.single_le_sum (fun k _ => hs.eigenvalues_nonneg k) (Finset.mem_univ i)
  have hn : ‖sigma‖ ≤ 1 := by
    simpa [ht] using hntrace
  exact Matrix.le_iff.mp ((CStarAlgebra.norm_le_one_iff_of_nonneg sigma hs.nonneg).mp hn)

def preparedReference (V : Matrix Q I ℂ) : Matrix Q Q ℂ :=
  V * faithfulInput (Q := I) * Vᴴ

theorem preparedReference_positive (V : Matrix Q I ℂ) :
    (preparedReference V).PosSemidef := faithfulInput_positive.mul_mul_conjTranspose_same V

theorem prepared_density_cap [Nonempty I] (V : Matrix Q I ℂ)
    (sigma : Matrix I I ℂ) (hs : sigma.PosSemidef) (ht : sigma.trace = 1) :
    ((Fintype.card I : ℂ) • preparedReference V - V * sigma * Vᴴ).PosSemidef := by
  have hc : (Fintype.card I : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hf : (Fintype.card I : ℂ) • faithfulInput (Q := I) = 1 := by
    rw [faithfulInput_eq_inverse_dim_smul, smul_smul, mul_inv_cancel₀ hc, one_smul]
  have he : (Fintype.card I : ℂ) • preparedReference V =
      V * (1 : Matrix I I ℂ) * Vᴴ := by
    calc
      _ = V * ((Fintype.card I : ℂ) • faithfulInput (Q := I)) * Vᴴ := by
        simp only [preparedReference, Matrix.mul_smul, Matrix.smul_mul]
      _ = _ := by rw [hf]
  rw [he, ← Matrix.sub_mul, ← Matrix.mul_sub]
  exact (density_one_sub_positive sigma hs ht).mul_mul_conjTranspose_same V

theorem bornMeasure_le_of_input_domination
    (D : ConsistentCylinderPOVM R Q) (c : ℝ≥0) (rho0 rho : Matrix Q Q ℂ)
    (h0 : rho0.PosSemidef) (hr : rho.PosSemidef)
    (hdom : ((c : ℂ) • rho0 - rho).PosSemidef) :
    D.fullBornMeasure rho hr ≤ c • D.fullBornMeasure rho0 h0 := by
  have he : rho + ((c : ℂ) • rho0 - rho) = (c : ℂ) • rho0 := by abel
  calc
    _ ≤ D.fullBornMeasure rho hr + D.fullBornMeasure ((c : ℂ) • rho0 - rho) hdom :=
      by
        apply Measure.le_iff.mpr
        intro B _
        rw [Measure.add_apply]
        exact le_add_of_nonneg_right bot_le
    _ = D.fullBornMeasure (rho + ((c : ℂ) • rho0 - rho)) (hr.add hdom) :=
      (D.fullBornMeasure_add rho ((c : ℂ) • rho0 - rho) hr hdom).symm
    _ = D.fullBornMeasure ((c : ℂ) • rho0) (h0.smul (complexWeight_nonneg c)) := by
      congr 1
    _ = _ := D.fullBornMeasure_smul c rho0 h0

theorem bornMeasure_absolutelyContinuous_of_input_domination
    (D : ConsistentCylinderPOVM R Q) (c : ℝ≥0) (rho0 rho : Matrix Q Q ℂ)
    (h0 : rho0.PosSemidef) (hr : rho.PosSemidef)
    (hdom : ((c : ℂ) • rho0 - rho).PosSemidef) :
    D.fullBornMeasure rho hr ≪ D.fullBornMeasure rho0 h0 := by
  apply Measure.absolutelyContinuous_of_le_smul (c := (c : ℝ≥0∞))
  exact bornMeasure_le_of_input_domination D c rho0 rho h0 hr hdom

def referenceRawReport (D : ConsistentCylinderPOVM R Q) (rho0 : Matrix Q Q ℂ)
    (h0 : rho0.PosSemidef) (J : Transcript R → Fin 4)
    (hJ : NullMeasurable J (D.fullBornMeasure rho0 h0)) : Transcript R → Fin 4 :=
  hJ.aemeasurable.mk J

theorem referenceRawReport_measurable (D : ConsistentCylinderPOVM R Q)
    (rho0 : Matrix Q Q ℂ) (h0 : rho0.PosSemidef) (J : Transcript R → Fin 4)
    (hJ : NullMeasurable J (D.fullBornMeasure rho0 h0)) :
    Measurable (referenceRawReport D rho0 h0 J hJ) := hJ.aemeasurable.measurable_mk

theorem referenceRawReport_ae_all_dominated (D : ConsistentCylinderPOVM R Q)
    (c : ℝ≥0) (rho0 rho : Matrix Q Q ℂ) (h0 : rho0.PosSemidef) (hr : rho.PosSemidef)
    (hdom : ((c : ℂ) • rho0 - rho).PosSemidef) (J : Transcript R → Fin 4)
    (hJ : NullMeasurable J (D.fullBornMeasure rho0 h0)) :
    J =ᵐ[D.fullBornMeasure rho hr] referenceRawReport D rho0 h0 J hJ :=
  (bornMeasure_absolutelyContinuous_of_input_domination D c rho0 rho h0 hr hdom).ae_eq
    hJ.aemeasurable.ae_eq_mk

theorem referenceCompletedReport_probability_mapRecord
    (C : ConsistentCylinderPOVM S Q) (D : ConsistentCylinderPOVM R Q)
    (g : S → R) (hg : Measurable g)
    (hC : ∀ n B, MeasurableSet B → C.effect n ((mapPrefixRecord g n) ⁻¹' B) = D.effect n B)
    (c : ℝ≥0) (rho0 rho : Matrix Q Q ℂ) (h0 : rho0.PosSemidef) (hr : rho.PosSemidef)
    (hdom : ((c : ℂ) • rho0 - rho).PosSemidef) (J : Transcript R → Fin 4)
    (hJ : NullMeasurable J (D.fullBornMeasure rho0 h0)) (j : Fin 4) :
    C.fullBornMeasure rho hr {omega | J (mapRecord g omega) = j} =
      D.fullBornMeasure rho hr {omega | J omega = j} := by
  let J0 := referenceRawReport D rho0 h0 J hJ
  have hm : Measurable J0 := referenceRawReport_measurable D rho0 h0 J hJ
  have ha := referenceRawReport_ae_all_dominated D c rho0 rho h0 hr hdom J hJ
  change J =ᵐ[D.fullBornMeasure rho hr] J0 at ha
  have hp : (J ∘ mapRecord g) =ᵐ[C.fullBornMeasure rho hr] (J0 ∘ mapRecord g) := by
    have hae : J =ᵐ[(C.fullBornMeasure rho hr).map (mapRecord g)] J0 := by
      rw [fullBornMeasure_mapRecord C D g hg hC rho hr]
      exact ha
    exact ae_of_ae_map (measurable_mapRecord g hg).aemeasurable hae
  have hl : C.fullBornMeasure rho hr {omega | J (mapRecord g omega) = j} =
      C.fullBornMeasure rho hr {omega | J0 (mapRecord g omega) = j} := by
    apply measure_congr
    filter_upwards [hp] with omega ho
    simp only [Set.mem_setOf_eq, Function.comp_apply] at ho ⊢
    rw [ho]
  have hr0 : D.fullBornMeasure rho hr {omega | J omega = j} =
      D.fullBornMeasure rho hr {omega | J0 omega = j} := by
    apply measure_congr
    filter_upwards [ha] with omega ho
    simp only [Set.mem_setOf_eq, ho]
  have hB : MeasurableSet {omega : Transcript R | J0 omega = j} :=
    measurableSet_eq_fun hm measurable_const
  rw [hl, hr0, ← fullBornMeasure_mapRecord C D g hg hC rho hr,
    Measure.map_apply (measurable_mapRecord g hg) hB]
  rfl

end QuantumProver.ElegantJointMeasurement.ClosureJoin.RecordTransport
end

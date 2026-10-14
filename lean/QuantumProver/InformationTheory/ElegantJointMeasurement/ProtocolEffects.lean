import Mathlib
import QuantumProver.InformationTheory.ElegantJointMeasurement.ClosureJoin
import QuantumProver.InformationTheory.ElegantJointMeasurement.IConcurrence

open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder
open InnerProductSpace QuantumProver.ElegantJointMeasurement.Augmented QuantumProver.ElegantJointMeasurement.Concurrence

namespace QuantumProver.ElegantJointMeasurement.ProtocolEffects

noncomputable section

set_option maxHeartbeats 600000

section Grouping

variable {ι M : Type*} [Fintype ι] [AddCommMonoid M]

def outcomeSum (report : ι → Fin 4) (g : ι → M) (j : Fin 4) : M :=
  ∑ i, if report i = j then g i else 0

theorem sum_outcomeSum (report : ι → Fin 4) (g : ι → M) :
    (∑ j, outcomeSum report g j) = ∑ i, g i := by
  unfold outcomeSum
  rw [Finset.sum_comm]
  simp [eq_comm]

theorem outcomeSum_add_complement (report : ι → Fin 4) (g : ι → M) (j : Fin 4) :
    outcomeSum report g j + (∑ i, if report i = j then 0 else g i) = ∑ i, g i := by
  unfold outcomeSum
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  split_ifs <;> simp

omit [Fintype ι] in
theorem sum_get_map (l : List ι) (g : ι → M) :
    (∑ i : Fin l.length, g (l.get i)) = (l.map g).sum := by
  rw [← List.sum_ofFn]
  change (List.ofFn (g ∘ l.get)).sum = (l.map g).sum
  rw [← List.map_ofFn, List.ofFn_get]

end Grouping

variable {κ : Type*} [Fintype κ] [DecidableEq κ]
variable {m n : ℕ}

def physicalPair (q : SystemBraPair m n)
    (ea : (Fin 2 × κ) ≃ Fin m) (eb : (Fin 2 × κ) ≃ Fin n) : Local κ × Local κ :=
  (WithLp.toLp 2 (fun z => conj (q.left (ea z))),
    WithLp.toLp 2 (fun z => conj (q.right (eb z))))

theorem physicalPair_left (q : SystemBraPair m n)
    (ea : (Fin 2 × κ) ≃ Fin m) (eb : (Fin 2 × κ) ≃ Fin n) :
    localMatrix (physicalPair q ea eb).1 = q.leftKetMatrix ea := rfl

theorem physicalPair_right (q : SystemBraPair m n)
    (ea : (Fin 2 × κ) ≃ Fin m) (eb : (Fin 2 × κ) ≃ Fin n) :
    localMatrix (physicalPair q ea eb).2 = q.rightKetMatrix eb := rfl

theorem physical_product_apply (q : SystemBraPair m n)
    (ea : (Fin 2 × κ) ≃ Fin m) (eb : (Fin 2 × κ) ≃ Fin n) (z : Index κ) :
    product (physicalPair q ea eb) z = conj (q.left (ea z.1) * q.right (eb z.2)) := by
  simp [product, QuantumProver.ElegantJointMeasurement.ResourceCode.productKet, localMatrix, physicalPair, map_mul]

def pullbackEffect (ea : (Fin 2 × κ) ≃ Fin m) (eb : (Fin 2 × κ) ≃ Fin n) :
    Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ →ₗ[ℂ] Matrix (Index κ) (Index κ) ℂ where
  toFun F := F.submatrix (ea.prodCongr eb) (ea.prodCongr eb)
  map_add' F G := rfl
  map_smul' r F := rfl

theorem pullbackEffect_one (ea : (Fin 2 × κ) ≃ Fin m) (eb : (Fin 2 × κ) ≃ Fin n) :
    pullbackEffect ea eb (1 : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) = 1 :=
  Matrix.submatrix_one_equiv (ea.prodCongr eb)

def physicalEffect (q : SystemBraPair m n)
    (ea : (Fin 2 × κ) ≃ Fin m) (eb : (Fin 2 × κ) ≃ Fin n) :
    Matrix (Index κ) (Index κ) ℂ := effectMatrix (product (physicalPair q ea eb))

theorem physicalEffect_eq_pullback (q : SystemBraPair m n)
    (ea : (Fin 2 × κ) ≃ Fin m) (eb : (Fin 2 × κ) ≃ Fin n) :
    physicalEffect q ea eb = pullbackEffect ea eb q.productEffect := by
  ext z h
  change product (physicalPair q ea eb) z * conj (product (physicalPair q ea eb) h) =
    q.productEffect (ea z.1, eb z.2) (ea h.1, eb h.2)
  rw [physical_product_apply, physical_product_apply, SystemBraPair.productEffect_apply]
  simp

theorem physicalEffect_rankOne (q : SystemBraPair m n)
    (ea : (Fin 2 × κ) ≃ Fin m) (eb : (Fin 2 × κ) ≃ Fin n) :
    QuantumProver.ElegantJointMeasurement.ClosureJoin.effectOperator (physicalEffect q ea eb) =
      rankOne ℂ (product (physicalPair q ea eb)) (product (physicalPair q ea eb)) :=
  QuantumProver.ElegantJointMeasurement.ClosureJoin.effectOperator_rankOne _

theorem physicalEffect_posSemidef (q : SystemBraPair m n)
    (ea : (Fin 2 × κ) ≃ Fin m) (eb : (Fin 2 × κ) ≃ Fin n) :
    (physicalEffect q ea eb).PosSemidef := by
  rw [physicalEffect_eq_pullback]
  exact q.productEffect_posSemidef.submatrix (ea.prodCongr eb)

theorem physicalPair_tailCost (q : SystemBraPair m n)
    (ea : (Fin 2 × κ) ≃ Fin m) (eb : (Fin 2 × κ) ≃ Fin n)
    (β : κ → ℝ) (k : κ) :
    QuantumProver.ElegantJointMeasurement.ClosureJoin.pairTailCost β k (physicalPair q ea eb) = q.tailCost ea eb β k := rfl

def braTailMatrix (q : SystemBraPair m n)
    (ea : (Fin 2 × κ) ≃ Fin m) (eb : (Fin 2 × κ) ≃ Fin n)
    (β : κ → ℝ) (k : κ) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => ∑ z ∈ Finset.univ.erase k,
    (β z : ℂ) * q.left (ea (i, z)) * q.right (eb (j, z))

theorem physical_tailMatrix_eq_conjugate (q : SystemBraPair m n)
    (ea : (Fin 2 × κ) ≃ Fin m) (eb : (Fin 2 × κ) ≃ Fin n)
    (β : κ → ℝ) (k : κ) :
    QuantumProver.ElegantJointMeasurement.ResourceCode.tailContraction β (localMatrix (physicalPair q ea eb).1)
      (localMatrix (physicalPair q ea eb).2) k = (braTailMatrix q ea eb β k).map conj := by
  ext i j
  rw [QuantumProver.ElegantJointMeasurement.ResourceCode.tailContraction_apply]
  simp [localMatrix, physicalPair, braTailMatrix, Matrix.map_apply, map_sum, map_mul]

theorem physicalPair_tailCost_eq_bra (q : SystemBraPair m n)
    (ea : (Fin 2 × κ) ≃ Fin m) (eb : (Fin 2 × κ) ≃ Fin n)
    (β : κ → ℝ) (k : κ) :
    QuantumProver.ElegantJointMeasurement.ClosureJoin.pairTailCost β k (physicalPair q ea eb) =
      ‖(braTailMatrix q ea eb β k).det‖ := by
  unfold QuantumProver.ElegantJointMeasurement.ClosureJoin.pairTailCost
  rw [physical_tailMatrix_eq_conjugate]
  have hdet := (starRingEnd ℂ).map_det (braTailMatrix q ea eb β k)
  change conj ((braTailMatrix q ea eb β k).det) =
    ((braTailMatrix q ea eb β k).map conj).det at hdet
  rw [← hdet]
  simp

theorem physicalPair_augmented (q : SystemBraPair m n)
    (ea : (Fin 2 × κ) ≃ Fin m) (eb : (Fin 2 × κ) ≃ Fin n)
    (β : κ → ℝ) (k : κ) :
    augmentedMap β k (physicalPair q ea eb) = (physicalEffect q ea eb, q.tailCost ea eb β k) := by
  apply Prod.ext
  · rfl
  · rw [augmentedMap, tailMatrix_product]
    exact physicalPair_tailCost q ea eb β k

def terminalPair (T : FiniteLocalKrausTree m n)
    (ea : (Fin 2 × κ) ≃ Fin m) (eb : (Fin 2 × κ) ≃ Fin n)
    (i : Fin T.terminalBraPairs.length) : Local κ × Local κ :=
  physicalPair (T.terminalBraPairs.get i) ea eb

def groupedEffect (T : FiniteLocalKrausTree m n)
    (ea : (Fin 2 × κ) ≃ Fin m) (eb : (Fin 2 × κ) ≃ Fin n)
    (report : Fin T.terminalBraPairs.length → Fin 4) (j : Fin 4) :
    Matrix (Index κ) (Index κ) ℂ :=
  outcomeSum report (fun i => physicalEffect (T.terminalBraPairs.get i) ea eb) j

def groupedCost (T : FiniteLocalKrausTree m n)
    (ea : (Fin 2 × κ) ≃ Fin m) (eb : (Fin 2 × κ) ≃ Fin n)
    (β : κ → ℝ) (k : κ) (report : Fin T.terminalBraPairs.length → Fin 4) (j : Fin 4) : ℝ :=
  outcomeSum report (fun i => (T.terminalBraPairs.get i).tailCost ea eb β k) j

def groupedRecord (T : FiniteLocalKrausTree m n)
    (ea : (Fin 2 × κ) ≃ Fin m) (eb : (Fin 2 × κ) ≃ Fin n)
    (β : κ → ℝ) (k : κ) (report : Fin T.terminalBraPairs.length → Fin 4) (j : Fin 4) : Augmented κ :=
  (groupedEffect T ea eb report j, groupedCost T ea eb β k report j)

theorem terminal_physical_effect_sum (T : FiniteLocalKrausTree m n)
    (ea : (Fin 2 × κ) ≃ Fin m) (eb : (Fin 2 × κ) ≃ Fin n) :
    (∑ i : Fin T.terminalBraPairs.length, physicalEffect (T.terminalBraPairs.get i) ea eb) = 1 := by
  simp_rw [physicalEffect_eq_pullback]
  rw [← map_sum, sum_get_map]
  change pullbackEffect ea eb T.terminalProductEffect = 1
  rw [T.terminalProductEffect_eq_one, pullbackEffect_one]

theorem groupedEffect_sum (T : FiniteLocalKrausTree m n)
    (ea : (Fin 2 × κ) ≃ Fin m) (eb : (Fin 2 × κ) ≃ Fin n)
    (report : Fin T.terminalBraPairs.length → Fin 4) :
    (∑ j, groupedEffect T ea eb report j) = 1 := by
  change (∑ j, outcomeSum report (fun i => physicalEffect (T.terminalBraPairs.get i) ea eb) j) = 1
  rw [sum_outcomeSum]
  exact terminal_physical_effect_sum T ea eb

theorem groupedEffect_posSemidef (T : FiniteLocalKrausTree m n)
    (ea : (Fin 2 × κ) ≃ Fin m) (eb : (Fin 2 × κ) ≃ Fin n)
    (report : Fin T.terminalBraPairs.length → Fin 4) (j : Fin 4) :
    (groupedEffect T ea eb report j).PosSemidef := by
  unfold groupedEffect outcomeSum
  apply Matrix.posSemidef_sum
  intro i hi
  split_ifs
  · exact physicalEffect_posSemidef _ ea eb
  · exact Matrix.PosSemidef.zero

theorem groupedEffect_upper (T : FiniteLocalKrausTree m n)
    (ea : (Fin 2 × κ) ≃ Fin m) (eb : (Fin 2 × κ) ≃ Fin n)
    (report : Fin T.terminalBraPairs.length → Fin 4) (j : Fin 4) :
    (1 - groupedEffect T ea eb report j).PosSemidef := by
  have hsplit := outcomeSum_add_complement report
    (fun i => physicalEffect (T.terminalBraPairs.get i) ea eb) j
  rw [terminal_physical_effect_sum T ea eb] at hsplit
  have heq : 1 - groupedEffect T ea eb report j =
      ∑ i, if report i = j then 0 else physicalEffect (T.terminalBraPairs.get i) ea eb := by
    change 1 - outcomeSum report (fun i => physicalEffect (T.terminalBraPairs.get i) ea eb) j = _
    rw [← hsplit]
    abel
  rw [heq]
  apply Matrix.posSemidef_sum
  intro i hi
  split_ifs
  · exact Matrix.PosSemidef.zero
  · exact physicalEffect_posSemidef _ ea eb

theorem groupedEffect_trace_le_dimension (T : FiniteLocalKrausTree m n)
    (ea : (Fin 2 × κ) ≃ Fin m) (eb : (Fin 2 × κ) ≃ Fin n)
    (report : Fin T.terminalBraPairs.length → Fin 4) (j : Fin 4) :
    effectMass (groupedEffect T ea eb report j) ≤ (Fintype.card (Index κ) : ℝ) := by
  have h := (groupedEffect_upper T ea eb report j).trace_nonneg
  have hre := (RCLike.nonneg_iff (K := ℂ)).mp h
  simp only [Matrix.trace_sub, Matrix.trace_one, Complex.sub_re, Complex.natCast_re] at hre
  exact sub_nonneg.mp hre.1

theorem groupedCost_sum (T : FiniteLocalKrausTree m n)
    (ea : (Fin 2 × κ) ≃ Fin m) (eb : (Fin 2 × κ) ≃ Fin n)
    (β : κ → ℝ) (k : κ) (report : Fin T.terminalBraPairs.length → Fin 4) :
    (∑ j, groupedCost T ea eb β k report j) =
      (T.terminalBraPairs.map fun q => q.tailCost ea eb β k).sum := by
  change (∑ j, outcomeSum report (fun i => (T.terminalBraPairs.get i).tailCost ea eb β k) j) = _
  rw [sum_outcomeSum]
  exact sum_get_map T.terminalBraPairs (fun q => q.tailCost ea eb β k)

def reportedPair (T : FiniteLocalKrausTree m n)
    (ea : (Fin 2 × κ) ≃ Fin m) (eb : (Fin 2 × κ) ≃ Fin n)
    (report : Fin T.terminalBraPairs.length → Fin 4) (j : Fin 4)
    (i : Fin T.terminalBraPairs.length) : Local κ × Local κ :=
  if report i = j then terminalPair T ea eb i else 0

theorem groupedRecord_eq_raw_sum (T : FiniteLocalKrausTree m n)
    (ea : (Fin 2 × κ) ≃ Fin m) (eb : (Fin 2 × κ) ≃ Fin n)
    (β : κ → ℝ) (k : κ) (report : Fin T.terminalBraPairs.length → Fin 4) (j : Fin 4) :
    (∑ i, augmentedMap β k (reportedPair T ea eb report j i)) = groupedRecord T ea eb β k report j := by
  have hzero : augmentedMap β k (0 : Local κ × Local κ) = 0 :=
    augmentedMap_zero_product β k (product_zero_left 0)
  calc
    (∑ i, augmentedMap β k (reportedPair T ea eb report j i)) =
        outcomeSum report (fun i => augmentedMap β k (terminalPair T ea eb i)) j := by
      unfold outcomeSum
      apply Finset.sum_congr rfl
      intro i hi
      simp only [reportedPair]
      split_ifs <;> simp_all
    _ = groupedRecord T ea eb β k report j := by
      apply Prod.ext <;>
        simp [outcomeSum, groupedRecord, groupedEffect, groupedCost, terminalPair,
          physicalPair_augmented, Prod.fst_sum, Prod.snd_sum, apply_ite]

theorem groupedRecord_finite_raw (T : FiniteLocalKrausTree m n)
    (ea : (Fin 2 × κ) ≃ Fin m) (eb : (Fin 2 × κ) ≃ Fin n)
    (β : κ → ℝ) (k : κ) (report : Fin T.terminalBraPairs.length → Fin 4) (j : Fin 4) :
    ∃ (r : ℕ) (p : Fin r → Local κ × Local κ),
      (∑ i, augmentedMap β k (p i)) = groupedRecord T ea eb β k report j :=
  ⟨T.terminalBraPairs.length, reportedPair T ea eb report j, groupedRecord_eq_raw_sum T ea eb β k report j⟩

theorem groupedRecord_total_cost_le (T : FiniteLocalKrausTree m n)
    (ea : (Fin 2 × κ) ≃ Fin m) (eb : (Fin 2 × κ) ≃ Fin n)
    (β : κ → ℝ) (k : κ) (t : ℝ) (ht : 0 < t)
    (report : Fin T.terminalBraPairs.length → Fin 4) :
    (∑ j, (groupedRecord T ea eb β k report j).2) ≤
      (2 * t) * homogeneousBudget
        ((Real.sqrt t)⁻¹ • physicalReferenceInput (omittedCoefficient β k)) := by
  change (∑ j, groupedCost T ea eb β k report j) ≤ _
  rw [groupedCost_sum]
  exact T.terminal_tail_cost_le ea eb β k t ht

theorem groupedRecord_closure_inputs (T : FiniteLocalKrausTree m n)
    (ea : (Fin 2 × κ) ≃ Fin m) (eb : (Fin 2 × κ) ≃ Fin n)
    (β : κ → ℝ) (k : κ) (t : ℝ) (ht : 0 < t)
    (report : Fin T.terminalBraPairs.length → Fin 4) :
    (∀ j, ∃ (r : ℕ) (p : Fin r → Local κ × Local κ),
      (∑ i, augmentedMap β k (p i)) = groupedRecord T ea eb β k report j) ∧
    (∀ j, effectMass (groupedRecord T ea eb β k report j).1 ≤ (Fintype.card (Index κ) : ℝ)) ∧
    (∑ j, (groupedRecord T ea eb β k report j).2) ≤
      (2 * t) * homogeneousBudget
        ((Real.sqrt t)⁻¹ • physicalReferenceInput (omittedCoefficient β k)) := by
  exact ⟨groupedRecord_finite_raw T ea eb β k report,
    groupedEffect_trace_le_dimension T ea eb report,
    groupedRecord_total_cost_le T ea eb β k t ht report⟩

theorem tree_effect_limit_upper {η : Type*} {l : Filter η} [l.NeBot]
    (T : η → FiniteLocalKrausTree m n)
    (ea : (Fin 2 × κ) ≃ Fin m) (eb : (Fin 2 × κ) ≃ Fin n)
    (report : (a : η) → Fin (T a).terminalBraPairs.length → Fin 4)
    (F : Fin 4 → Matrix (Index κ) (Index κ) ℂ)
    (hlim : Filter.Tendsto (fun a j => groupedEffect (T a) ea eb (report a) j) l (nhds F)) :
    ∀ j, (1 - F j).PosSemidef := by
  intro j
  have hj := (tendsto_pi_nhds.mp hlim) j
  apply Matrix.posSemidef_is_closed.mem_of_tendsto (tendsto_const_nhds.sub hj)
  exact Filter.Eventually.of_forall (fun a => groupedEffect_upper (T a) ea eb (report a) j)

theorem unit_direction_ejm_necessary_of_tree_effect_limit
    {η : Type*} {l : Filter η} [l.NeBot]
    (β : κ → ℝ) (hβ : ∑ k, β k ^ 2 = 1) (k : κ) (x : ℝ) (hx : β k ^ 2 = x)
    (u v w : Fin 4 → ℝ) (hsphere : ∀ j, u j ^ 2 + v j ^ 2 + w j ^ 2 = 1)
    (t : ℝ) (ht : 0 < t) (T : η → FiniteLocalKrausTree m n)
    (ea : (Fin 2 × κ) ≃ Fin m) (eb : (Fin 2 × κ) ≃ Fin n)
    (report : (a : η) → Fin (T a).terminalBraPairs.length → Fin 4)
    (F : Fin 4 → Matrix (Index κ) (Index κ) ℂ)
    (hlim : Filter.Tendsto (fun a j => groupedEffect (T a) ea eb (report a) j) l (nhds F))
    (hcompression : ∀ j, (QuantumProver.ElegantJointMeasurement.ResourceCode.codeContinuous β).adjoint ∘L
      (QuantumProver.ElegantJointMeasurement.ClosureJoin.effectOperator (F j) ∘L QuantumProver.ElegantJointMeasurement.ResourceCode.codeContinuous β) =
        rankOne ℂ (QuantumProver.ElegantJointMeasurement.ClosureJoin.directionKet (u j) (v j) (w j))
          (QuantumProver.ElegantJointMeasurement.ClosureJoin.directionKet (u j) (v j) (w j))) :
    |1 - 2 * x| ≤ (2 * t) * homogeneousBudget
      ((Real.sqrt t)⁻¹ • physicalReferenceInput (omittedCoefficient β k)) := by
  apply QuantumProver.ElegantJointMeasurement.ClosureJoin.unit_direction_ejm_necessary_of_inherited_effect_limit
    β hβ k x _ hx u v w hsphere (fun _ => (Fintype.card (Index κ) : ℝ))
    (fun a j => groupedRecord (T a) ea eb β k (report a) j) F hlim
  · exact Filter.Eventually.of_forall (fun a => groupedRecord_finite_raw (T a) ea eb β k (report a))
  · exact Filter.Eventually.of_forall (fun a => groupedEffect_trace_le_dimension (T a) ea eb (report a))
  · exact Filter.Eventually.of_forall (fun a => groupedRecord_total_cost_le (T a) ea eb β k t ht (report a))
  · exact tree_effect_limit_upper T ea eb report F hlim
  · exact hcompression

end

end QuantumProver.ElegantJointMeasurement.ProtocolEffects

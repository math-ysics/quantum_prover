import QuantumProver.InformationTheory.ElegantJointMeasurement.NormalCostIntegration
import QuantumProver.InformationTheory.ElegantJointMeasurement.FiniteNormalOperationalBridge
import QuantumProver.QuantumChannels.NormalFreePreparationChronology

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open MeasureTheory Matrix Set Filter Preorder
open QuantumProver.ElegantJointMeasurement.NormalProcess QuantumProver.ElegantJointMeasurement.HilbertTranscriptPOVM
open QuantumProver.ElegantJointMeasurement.HilbertSquareProcess (History appendHistory)
open QuantumProver.ElegantJointMeasurement.ClosureJoin.RecordTransport QuantumProver.ElegantJointMeasurement.PreparedReports QuantumProver.ElegantJointMeasurement.GeneralResource
open QuantumProver.ElegantJointMeasurement.HilbertSquareCostModel
open QuantumProver.ElegantJointMeasurement.HilbertFiniteCostModel
open scoped BigOperators Topology ComplexConjugate ComplexOrder MatrixOrder

namespace QuantumProver.ElegantJointMeasurement.NormalCost

local instance finiteComplete (q : ℕ) : CompleteSpace (EuclideanSpace ℂ (Fin q)) :=
  PiLp.completeSpace 2 (fun _ : Fin q => ℂ)

section PhysicalLaw
variable {R : Type*} [MeasurableSpace R] [StandardBorelSpace R]
variable {m n : ℕ} [NeZero m] [NeZero n]

theorem physical_cylinder_eq_compiled_pullback (P : MatrixProcess m n R) :
    ∀ N B, MeasurableSet B →
      (letI : Nonempty (FineRecord R) := P.fineRecord_nonempty;
       P.squareProcess.cylinderPOVM.effect N
         ((mapPrefixRecord (Prod.fst : FineRecord R → R) N) ⁻¹' B)) =
        P.represented_physicalCylinderPOVM.effect N B := by
  letI : Nonempty (FineRecord R) := P.fineRecord_nonempty
  intro N B hB
  change P.squareProcess.cylinderEffect N ((coarseHistory (N+1)) ⁻¹' B) =
    P.represented_physicalCylinderEffect N B
  exact (P.physicalCylinderEffect_eq_compiled N B hB).symm

end PhysicalLaw

section Resource
variable {κ : Type*} [Fintype κ] [DecidableEq κ]
variable {m n : ℕ} [NeZero m] [NeZero n]
variable {R : Type*} [MeasurableSpace R] [StandardBorelSpace R]

def physicalResourceDensityOutput
    (ea : (Fin 2 × κ) ≃ Fin m) (eb : (Fin 2 × κ) ≃ Fin n)
    (P : MatrixProcess m n R) (J : Transcript R → Fin 4) (Ψ : Matrix κ κ ℂ)
    (σ : Matrix QuantumProver.ElegantJointMeasurement.Teleportation.SystemIndex QuantumProver.ElegantJointMeasurement.Teleportation.SystemIndex ℂ)
    (hσ : σ.PosSemidef) : Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) ℂ :=
  ∑ j : Fin 4,
    (((P.represented_physicalBornMeasure
      (matrixCodeMatrix ea eb Ψ * σ * (matrixCodeMatrix ea eb Ψ)ᴴ)
      (hσ.mul_mul_conjTranspose_same (matrixCodeMatrix ea eb Ψ))
      {ω | J ω = j}).toReal : ℝ) : ℂ) • QuantumProver.ElegantJointMeasurement.Teleportation.Tomography.sharedProjector j

def preparedCompiledReport
    (ea : (Fin 2 × κ) ≃ Fin m) (eb : (Fin 2 × κ) ≃ Fin n)
    (P : MatrixProcess m n R) (J : Transcript R → Fin 4) (Ψ : Matrix κ κ ℂ)
    (hJ : NullMeasurable J (P.represented_physicalBornMeasure
      (preparedReference (matrixCodeMatrix ea eb Ψ))
      (preparedReference_positive (matrixCodeMatrix ea eb Ψ)))) :
    Transcript (FineRecord R) → Fin 4 := by
  letI : Nonempty R := P.record_nonempty
  letI : Nonempty (FineRecord R) := P.fineRecord_nonempty
  exact preparedRawReport P.represented_physicalCylinderPOVM (matrixCodeMatrix ea eb Ψ) J hJ ∘
    mapRecord (Prod.fst : FineRecord R → R)

theorem preparedCompiledReport_measurable
    (ea : (Fin 2 × κ) ≃ Fin m) (eb : (Fin 2 × κ) ≃ Fin n)
    (P : MatrixProcess m n R) (J : Transcript R → Fin 4) (Ψ : Matrix κ κ ℂ)
    (hJ : NullMeasurable J (P.represented_physicalBornMeasure
      (preparedReference (matrixCodeMatrix ea eb Ψ))
      (preparedReference_positive (matrixCodeMatrix ea eb Ψ)))) :
    Measurable (preparedCompiledReport ea eb P J Ψ hJ) := by
  letI : Nonempty R := P.record_nonempty
  letI : Nonempty (FineRecord R) := P.fineRecord_nonempty
  exact (preparedRawReport_measurable P.represented_physicalCylinderPOVM
    (matrixCodeMatrix ea eb Ψ) J hJ).comp (measurable_mapRecord Prod.fst measurable_fst)

theorem physicalResourceDensityOutput_eq_compiled
    (ea : (Fin 2 × κ) ≃ Fin m) (eb : (Fin 2 × κ) ≃ Fin n)
    (P : MatrixProcess m n R) (J : Transcript R → Fin 4) (Ψ : Matrix κ κ ℂ)
    (hJ : NullMeasurable J (P.represented_physicalBornMeasure
      (preparedReference (matrixCodeMatrix ea eb Ψ))
      (preparedReference_positive (matrixCodeMatrix ea eb Ψ))))
    (σ : Matrix QuantumProver.ElegantJointMeasurement.Teleportation.SystemIndex QuantumProver.ElegantJointMeasurement.Teleportation.SystemIndex ℂ)
    (hσ : σ.PosSemidef) (ht : σ.trace = 1) :
    physicalResourceDensityOutput ea eb P J Ψ σ hσ =
      (letI : Nonempty (FineRecord R) := P.fineRecord_nonempty;
       matrixCompletedResourceChannel ea eb P.squareProcess
         (preparedCompiledReport ea eb P J Ψ hJ) Ψ σ) := by
  letI : Nonempty R := P.record_nonempty
  letI : Nonempty (FineRecord R) := P.fineRecord_nonempty
  exact (resource_channel_eq_physical_report_output P.squareProcess.cylinderPOVM
    P.represented_physicalCylinderPOVM Prod.fst measurable_fst (physical_cylinder_eq_compiled_pullback P)
    (matrixCodeMatrix ea eb Ψ) J hJ σ hσ ht).symm

end Resource

section VaryingRecords
variable {κ : Type*} [Fintype κ] [DecidableEq κ]
variable {m n : ℕ} [NeZero m] [NeZero n]
variable {R : ℕ → Type*} [∀ k, MeasurableSpace (R k)] [∀ k, StandardBorelSpace (R k)]

theorem physical_normal_varying_records_density_limit_entropy_ge_one
    (Ψ : Matrix κ κ ℂ) (hΨ : (Ψ * Ψᴴ).trace = 1)
    (ea : (Fin 2 × κ) ≃ Fin m) (eb : (Fin 2 × κ) ≃ Fin n)
    (P : ∀ k : ℕ, MatrixProcess m n (R k))
    (J : ∀ k : ℕ, Transcript (R k) → Fin 4)
    (hJ : ∀ k, NullMeasurable (J k) ((P k).represented_physicalBornMeasure
      (preparedReference (matrixCodeMatrix ea eb Ψ))
      (preparedReference_positive (matrixCodeMatrix ea eb Ψ))))
    (hChannel : ∀ σ : Matrix QuantumProver.ElegantJointMeasurement.Teleportation.SystemIndex QuantumProver.ElegantJointMeasurement.Teleportation.SystemIndex ℂ,
      ∀ hσ : σ.PosSemidef, σ.trace = 1 →
      Tendsto (fun k => physicalResourceDensityOutput ea eb (P k) (J k) Ψ σ hσ)
        atTop (𝓝 (QuantumProver.ElegantJointMeasurement.Teleportation.physicalClassicalChannel σ))) :
    1 ≤ QuantumProver.ElegantJointMeasurement.TailReference.vonNeumannEntropyBits (Ψ * Ψᴴ) := by
  letI : ∀ k, Nonempty (R k) := fun k => (P k).record_nonempty
  letI : ∀ k, Nonempty (FineRecord (R k)) := fun k => (P k).fineRecord_nonempty
  let K := fun k => preparedCompiledReport ea eb (P k) (J k) Ψ (hJ k)
  have hm (k : ℕ) : Measurable (K k) :=
    preparedCompiledReport_measurable ea eb (P k) (J k) Ψ (hJ k)
  apply completed_matrix_square_varying_records_density_limit_entropy_ge_one
    Ψ hΨ ea eb (fun k => (P k).squareProcess) K (fun k => (hm k).nullMeasurable)
  intro σ hσ ht
  have he (k : ℕ) := physicalResourceDensityOutput_eq_compiled ea eb (P k) (J k)
    Ψ (hJ k) σ hσ ht
  simpa only [he, K] using hChannel σ hσ ht

end VaryingRecords

section Rectangular
variable {κ η : Type*} [Fintype κ] [DecidableEq κ] [Fintype η] [DecidableEq η]
variable {m n : ℕ} [NeZero m] [NeZero n]
variable {R : ℕ → Type*} [∀ k, MeasurableSpace (R k)] [∀ k, StandardBorelSpace (R k)]
open QuantumProver.ElegantJointMeasurement.SchmidtResource.SquarePadding

theorem rectangular_physical_normal_density_limit_entropy_ge_one
    (Ψ : Matrix κ η ℂ) (hΨ : (Ψ * Ψᴴ).trace = 1)
    (ea : (Fin 2 × (κ ⊕ η)) ≃ Fin m) (eb : (Fin 2 × (κ ⊕ η)) ≃ Fin n)
    (P : ∀ k : ℕ, MatrixProcess m n (R k))
    (J : ∀ k : ℕ, Transcript (R k) → Fin 4)
    (hJ : ∀ k, NullMeasurable (J k) ((P k).represented_physicalBornMeasure
      (preparedReference (matrixCodeMatrix ea eb (coefficient Ψ)))
      (preparedReference_positive (matrixCodeMatrix ea eb (coefficient Ψ)))))
    (hChannel : ∀ σ : Matrix QuantumProver.ElegantJointMeasurement.Teleportation.SystemIndex QuantumProver.ElegantJointMeasurement.Teleportation.SystemIndex ℂ,
      ∀ hσ : σ.PosSemidef, σ.trace = 1 →
      Tendsto (fun k => physicalResourceDensityOutput ea eb (P k) (J k) (coefficient Ψ) σ hσ)
        atTop (𝓝 (QuantumProver.ElegantJointMeasurement.Teleportation.physicalClassicalChannel σ))) :
    1 ≤ QuantumProver.ElegantJointMeasurement.TailReference.vonNeumannEntropyBits (Ψ * Ψᴴ) := by
  have h := physical_normal_varying_records_density_limit_entropy_ge_one
    (coefficient Ψ) (normalized_coefficient Ψ hΨ) ea eb P J hJ hChannel
  simpa only [coefficient_entropy] using h

end Rectangular
end QuantumProver.ElegantJointMeasurement.NormalCost

open QuantumProver.ElegantJointMeasurement.HilbertFiniteNormalChronology QuantumProver.ElegantJointMeasurement.HilbertFiniteNormalOperationalBridge
open QuantumProver.ElegantJointMeasurement.HilbertFiniteEJMProtocol QuantumProver.ElegantJointMeasurement.Teleportation
open scoped Matrix.Norms.L2Operator Kronecker Classical

namespace QuantumProver.ElegantJointMeasurement.NormalCost

section DiscretePrefix
variable {a b : ℕ} [NeZero a] [NeZero b]
variable {R : Type*} [MeasurableSpace R] [StandardBorelSpace R]
  [Countable R] [MeasurableSingletonClass R]

theorem hasSum_physicalPrefixAction_singletons_on_event (P : MatrixProcess a b R)
    (N : ℕ) (s : Set (History R N)) (hs : MeasurableSet s) (X : JointMatrix a b) :
    HasSum (fun h : History R N => if h ∈ s then P.represented_physicalPrefixAction N {h} X else 0)
      (P.represented_physicalPrefixAction N s X) := by
  letI := history_countable (R := R) N
  letI := history_measurableSingletonClass (R := R) N
  have hd : Pairwise (fun h k : History R N =>
      Disjoint (({h} : Set (History R N)) ∩ s) ({k} ∩ s)) := by
    intro h k hne
    exact (Set.disjoint_singleton.mpr hne).mono inter_subset_left inter_subset_left
  have he (h : History R N) :
      (∫ z in ({h} ∩ s), P.represented_physicalInputDensity N X z ∂P.represented_physicalPrefixMeasure N) =
        if h ∈ s then P.represented_physicalPrefixAction N {h} X else 0 := by
    by_cases hh : h ∈ s
    · rw [if_pos hh]
      have ht : ({h} : Set (History R N)) ∩ s = {h} := by ext z; aesop
      rw [ht, P.physicalPrefixAction_eq_physicalInputDensity N {h}
        (measurableSet_singleton h) X]
    · rw [if_neg hh]
      have ht : ({h} : Set (History R N)) ∩ s = ∅ := by ext z; aesop
      rw [ht, setIntegral_empty]
  have hu : (⋃ h : History R N, ({h} : Set (History R N)) ∩ s) = s := by
    ext z
    simp
  have ht := hasSum_integral_iUnion (fun h : History R N =>
    (measurableSet_singleton h).inter hs) hd (P.physicalInputDensity_integrable N X).integrableOn
  simpa only [hu, he, ← P.physicalPrefixAction_eq_physicalInputDensity N s hs X] using ht

end DiscretePrefix

def decodeEJMRecord (r : ℕ) : Fin 4 := ⟨(r-1) % 4, Nat.mod_lt _ (by decide)⟩

theorem decodeEJMRecord_visible (j : Fin 4) : decodeEJMRecord (j.val+1) = j := by
  apply Fin.ext
  simpa only [decodeEJMRecord, Nat.add_sub_cancel] using Nat.mod_eq_of_lt j.isLt

def ejmPrefixReport (h : History ℕ 3) : Fin 4 :=
  decodeEJMRecord ((appendHistory 2).symm h).2

def ejmPhysicalReport (ω : Transcript ℕ) : Fin 4 :=
  ejmPrefixReport (frestrictLe (π := fun _ => ℕ) 2 ω)

theorem measurable_ejmPrefixReport : Measurable ejmPrefixReport := by
  have hm : Measurable decodeEJMRecord := measurable_of_countable _
  exact hm.comp (measurable_snd.comp (appendHistory (R := ℕ) 2).symm.measurable)

theorem measurable_ejmPhysicalReport : Measurable ejmPhysicalReport :=
  measurable_ejmPrefixReport.comp (measurable_frestrictLe 2)

theorem oneEbitProtocol_depth : depth oneEbitProtocol = 3 := by
  simp [oneEbitProtocol, QuantumProver.ElegantJointMeasurement.HilbertFiniteEJMProtocol.bobCorrection, bobMeasurement,
    sharedTerminal, depth, Finset.sup_const (Finset.univ_nonempty (α := Fin 4)),
    Finset.sup_const (Finset.univ_nonempty (α := Fin 1))]

theorem finiteJointChart_trace (c d : ℕ) (X : JointMatrix c d) :
    QuantumProver.HilbertNuclearTrace.trace (finiteJointChart c d X) = Matrix.trace X := by
  exact QuantumProver.ElegantJointMeasurement.HilbertPendingTensor.trace_jointOperation
    (fun _ : Unit => ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin c)))
    (fun _ : Unit => ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin d)))
    (by simp; rfl) (by simp; rfl) X

theorem terminalOutput_rawPrefix_result {c d a b : ℕ} (U : Protocol c d a b)
    (N : ℕ) (hN : depth U ≤ N) (hc : 0 < c) (hd : 0 < d)
    (h : History ℕ N) (X : JointMatrix a b) :
    terminalOutput U N hc hd h (rawPrefix U N h (codedJoint a b X)) =
      physicalJoint c d (matrixState U X N h).result := by
  rw [terminalOutput_eq_state, rawPrefix_eq_matrixState, ← matrixState_toState U X N h]
  exact MatrixState.terminalPair_eval_of_depth_zero hc hd _ (by
    simpa only [matrixState_toState] using state_depth_zero U N hN h)

theorem oneEbit_two_turn_shape (h : History ℕ 2) (X : JointMatrix 4 4) :
    (∃ Y : JointMatrix 1 4, matrixState oneEbitProtocol X 2 h =
        MatrixState.active bobMeasurement Y) ∨
      matrixState oneEbitProtocol X 2 h = MatrixState.invalid := by
  obtain ⟨⟨h, r⟩, rfl⟩ := (appendHistory (R := ℕ) 1).surjective h
  obtain ⟨⟨h, q⟩, rfl⟩ := (appendHistory (R := ℕ) 0).surjective h
  cases h
  rw [matrixState_append, matrixState_append]
  cases q with
  | zero => exact Or.inr rfl
  | succ q =>
      by_cases hq : q < 4
      · cases r with
        | zero =>
            right
            simp only [matrixState, oneEbitProtocol, QuantumProver.ElegantJointMeasurement.HilbertFiniteEJMProtocol.bobCorrection,
              MatrixState.advance, dif_pos hq]
        | succ r =>
            by_cases hr : r < 1
            · left
              simp only [matrixState, oneEbitProtocol, QuantumProver.ElegantJointMeasurement.HilbertFiniteEJMProtocol.bobCorrection, MatrixState.advance,
                dif_pos hq, dif_pos hr]
              exact ⟨_, rfl⟩
            · right
              simp only [matrixState, oneEbitProtocol, QuantumProver.ElegantJointMeasurement.HilbertFiniteEJMProtocol.bobCorrection, MatrixState.advance,
                dif_pos hq, dif_neg hr]
      · right
        simp only [matrixState, oneEbitProtocol, MatrixState.advance, dif_neg hq]

theorem sharedProjector_diagonal_trace (i j : Fin 4) (z : ℂ) :
    (z • sharedLabelProjector j) (i,i) (i,i) =
      if j = i then Matrix.trace (z • sharedLabelProjector j) else 0 := by
  simp [sharedLabelProjector, Matrix.trace, Matrix.diag, Matrix.smul_apply,
    Fintype.sum_prod_type, eq_comm]

theorem oneEbit_result_report_diagonal (h : History ℕ 3) (X : JointMatrix 4 4)
    (j : Fin 4) :
    (matrixState oneEbitProtocol X 3 h).result (j,j) (j,j) =
      if ejmPrefixReport h = j then Matrix.trace ((matrixState oneEbitProtocol X 3 h).result)
        else 0 := by
  obtain ⟨⟨h, r⟩, rfl⟩ := (appendHistory (R := ℕ) 2).surjective h
  rw [matrixState_append]
  rcases oneEbit_two_turn_shape h X with ⟨Y, hY⟩ | hY
  · rw [hY]
    cases r with
    | zero => simp [bobMeasurement, MatrixState.advance, MatrixState.result, ejmPrefixReport]
    | succ r =>
        by_cases hr : r < 4
        · have hd : ejmPrefixReport (appendHistory 2 (h,r+1)) = (⟨r,hr⟩ : Fin 4) := by
            simpa only [ejmPrefixReport, MeasurableEquiv.symm_apply_apply] using
              decodeEJMRecord_visible (⟨r,hr⟩ : Fin 4)
          simp only [MatrixState.advance, bobMeasurement, dif_pos hr, MatrixState.result,
            sharedTerminal, QuantumProver.WernerEndpoint.OperationalEndpointCost.FiniteLocalProtocol.apply]
          let Z : JointMatrix 1 1 := bobMatrixEvent (fun j (_ : Fin 1) => bobFinBra j) {r+1} Y
          change (sharedColumn ⟨r,hr⟩ * Z * (sharedColumn ⟨r,hr⟩).conjTranspose) (j,j) (j,j) =
            if ejmPrefixReport (appendHistory 2 (h,r+1)) = j then
              Matrix.trace (sharedColumn ⟨r,hr⟩ * Z * (sharedColumn ⟨r,hr⟩).conjTranspose) else 0
          rw [sharedColumn_sandwich, hd]
          exact sharedProjector_diagonal_trace j ⟨r,hr⟩ _
        · simp [MatrixState.advance, bobMeasurement, hr, MatrixState.result]
  · simp [hY, MatrixState.advance, MatrixState.result]

end QuantumProver.ElegantJointMeasurement.NormalCost

namespace QuantumProver.ElegantJointMeasurement.NormalCost

theorem represented_physicalEffect_posSemidef (j : Fin 4) : (represented_physicalEffect j).PosSemidef := by
  change (Matrix.vecMulVec (flatten (ejmCoefficient j))
    (star (flatten (ejmCoefficient j)))).PosSemidef
  exact Matrix.posSemidef_vecMulVec_self_star _

theorem oneEbit_singleton_trace_result (h : History ℕ 3) (X : JointMatrix 4 4) :
    QuantumProver.HilbertNuclearTrace.trace
      ((ofProtocol oneEbitProtocol).represented_physicalPrefixAction 3 {h} X) =
        Matrix.trace ((matrixState oneEbitProtocol X 3 h).result) := by
  rw [physicalPrefixAction_ofProtocol_singleton]
  have hN : depth oneEbitProtocol ≤ 3 := by
    rw [oneEbitProtocol_depth]
  have ht0 := terminalJointOperation_trace
    (physicalFiniteNormalTerminal oneEbitProtocol 3 (by decide) (by decide)) h
    (rawPrefix oneEbitProtocol 3 h (codedJoint 4 4 X))
  have ht : QuantumProver.HilbertNuclearTrace.trace
      (terminalOutput oneEbitProtocol 3 (by decide) (by decide) h
        (rawPrefix oneEbitProtocol 3 h (codedJoint 4 4 X))) =
      QuantumProver.HilbertNuclearTrace.trace (rawPrefix oneEbitProtocol 3 h (codedJoint 4 4 X)) := by
    simpa only [physicalFiniteNormalTerminal_jointOperation] using ht0
  have hres := terminalOutput_rawPrefix_result oneEbitProtocol 3 hN
    (by decide) (by decide) h X
  calc
    _ = QuantumProver.HilbertNuclearTrace.trace
        (terminalOutput oneEbitProtocol 3 (by decide) (by decide) h
          (rawPrefix oneEbitProtocol 3 h (codedJoint 4 4 X))) := ht.symm
    _ = QuantumProver.HilbertNuclearTrace.trace
        (physicalJoint 4 4 (matrixState oneEbitProtocol X 3 h).result) :=
      congrArg QuantumProver.HilbertNuclearTrace.trace hres
    _ = _ := by rw [physicalJoint_eq_finiteJointChart, finiteJointChart_trace]

theorem oneEbit_report_prefix_trace (X : JointMatrix 4 4) (j : Fin 4) :
    QuantumProver.HilbertNuclearTrace.trace
      ((ofProtocol oneEbitProtocol).represented_physicalPrefixAction 3
        {h | ejmPrefixReport h = j} X) = (oneEbitProtocol.apply X) (j,j) (j,j) := by
  let s : Set (History ℕ 3) := {h | ejmPrefixReport h = j}
  have hs : MeasurableSet s := measurableSet_eq_fun measurable_ejmPrefixReport measurable_const
  have hz (h : History ℕ 3) (hh : h ∉ frontier oneEbitProtocol 3) :
      (if h ∈ s then (ofProtocol oneEbitProtocol).represented_physicalPrefixAction 3 {h} X else 0) = 0 := by
    by_cases hj : h ∈ s
    · rw [if_pos hj, physicalPrefixAction_ofProtocol_singleton,
        rawPrefix_zero_of_not_mem_frontier oneEbitProtocol X 3 h hh]
    · rw [if_neg hj]
  have hsum : HasSum
      (fun h : History ℕ 3 => if h ∈ s then
        (ofProtocol oneEbitProtocol).represented_physicalPrefixAction 3 {h} X else 0)
      (∑ h ∈ frontier oneEbitProtocol 3, if h ∈ s then
        (ofProtocol oneEbitProtocol).represented_physicalPrefixAction 3 {h} X else 0) :=
    hasSum_sum_of_ne_finset_zero (s := frontier oneEbitProtocol 3) hz
  have hactual : HasSum
      (fun h : History ℕ 3 => if h ∈ s then
        (ofProtocol oneEbitProtocol).represented_physicalPrefixAction 3 {h} X else 0)
      ((ofProtocol oneEbitProtocol).represented_physicalPrefixAction 3 s X) := by
    convert hasSum_physicalPrefixAction_singletons_on_event
      (ofProtocol oneEbitProtocol) 3 s hs X using 1
    funext h
    by_cases hj : h ∈ s <;> simp only [hj, ite_true, ite_false]
  have he := hactual.unique hsum
  change QuantumProver.HilbertNuclearTrace.trace
    ((ofProtocol oneEbitProtocol).represented_physicalPrefixAction 3 s X) = _
  rw [he, map_sum]
  calc
    _ = ∑ h ∈ frontier oneEbitProtocol 3,
        (matrixState oneEbitProtocol X 3 h).result (j,j) (j,j) := by
      apply Finset.sum_congr rfl
      intro h hh
      rw [oneEbit_result_report_diagonal]
      by_cases hj : h ∈ s
      · have hj' : ejmPrefixReport h = j := hj
        rw [if_pos hj, if_pos hj', oneEbit_singleton_trace_result]
      · have hj' : ejmPrefixReport h ≠ j := hj
        rw [if_neg hj, if_neg hj', map_zero]
    _ = (oneEbitProtocol.apply X) (j,j) (j,j) := by
      have he' := congrArg (fun Y : JointMatrix 4 4 => Y (j,j) (j,j))
        (sum_frontier_result oneEbitProtocol X 3)
      simpa only [Matrix.sum_apply] using he'

theorem represented_oneEbit_physicalBorn_report (ρ : Matrix SystemIndex SystemIndex ℂ)
    (hρ : ρ.PosSemidef) (j : Fin 4) :
    (ofProtocol oneEbitProtocol).represented_physicalBornMeasure
      (matrixResourceEmbedding * ρ * matrixResourceEmbeddingᴴ)
      (hρ.mul_mul_conjTranspose_same matrixResourceEmbedding)
      {ω | ejmPhysicalReport ω = j} =
        ENNReal.ofReal ((Matrix.trace (represented_physicalEffect j * ρ)).re) := by
  change (ofProtocol oneEbitProtocol).represented_physicalBornMeasure _ _
    ((frestrictLe (π := fun _ => ℕ) 2) ⁻¹' {h | ejmPrefixReport h = j}) = _
  rw [MatrixProcess.physicalBornMeasure_prefix _ _ _ _ _
      (measurableSet_eq_fun measurable_ejmPrefixReport measurable_const),
    oneEbit_report_prefix_trace, oneEbitProtocol_physical_output]
  change ENNReal.ofReal ((Tomography.measurementChannel represented_physicalEffect ρ (j,j) (j,j)).re) = _
  rw [Tomography.measurementChannel_entry]

theorem represented_oneEbit_physicalBorn_report_toReal (ρ : Matrix SystemIndex SystemIndex ℂ)
    (hρ : ρ.PosSemidef) (j : Fin 4) :
    ((ofProtocol oneEbitProtocol).represented_physicalBornMeasure
      (matrixResourceEmbedding * ρ * matrixResourceEmbeddingᴴ)
      (hρ.mul_mul_conjTranspose_same matrixResourceEmbedding)
      {ω | ejmPhysicalReport ω = j}).toReal = (Matrix.trace (represented_physicalEffect j * ρ)).re := by
  rw [represented_oneEbit_physicalBorn_report ρ hρ j, ENNReal.toReal_ofReal]
  exact QuantumProver.ElegantJointMeasurement.HilbertTranscriptPOVM.MatrixProbe.bornScalar_nonneg ρ (represented_physicalEffect j) hρ
    (represented_physicalEffect_posSemidef j)

theorem oneEbit_physical_report_density_output (ρ : Matrix SystemIndex SystemIndex ℂ)
    (hρ : ρ.PosSemidef) :
    (∑ j : Fin 4,
      ((((ofProtocol oneEbitProtocol).represented_physicalBornMeasure
        (matrixResourceEmbedding * ρ * matrixResourceEmbeddingᴴ)
        (hρ.mul_mul_conjTranspose_same matrixResourceEmbedding)
        {ω | ejmPhysicalReport ω = j}).toReal : ℝ) : ℂ) •
        Tomography.sharedProjector j) = physicalClassicalChannel ρ := by
  change _ = Tomography.measurementChannel represented_physicalEffect ρ
  apply Finset.sum_congr rfl
  intro j hj
  rw [represented_oneEbit_physicalBorn_report_toReal ρ hρ j]
  rw [QuantumProver.ElegantJointMeasurement.PreparedReports.trace_mul_psd_re_cast _ _ (represented_physicalEffect_posSemidef j) hρ]

open QuantumProver.ElegantJointMeasurement.NormalRecordTransport QuantumProver.ElegantJointMeasurement.HilbertFiniteNormalRecordLift

def ejmLiftedPrefixReport (h : History (ULift.{u} ℕ) 3) : Fin 4 :=
  ejmPrefixReport ((historyEquiv natLiftEquiv.{u} 3).symm h)

def ejmLiftedPhysicalReport (ω : Transcript (ULift.{u} ℕ)) : Fin 4 :=
  ejmLiftedPrefixReport (frestrictLe (π := fun _ => ULift.{u} ℕ) 2 ω)

theorem measurable_ejmLiftedPrefixReport : Measurable ejmLiftedPrefixReport.{u} :=
  measurable_ejmPrefixReport.comp (historyEquiv natLiftEquiv.{u} 3).symm.measurable

theorem measurable_ejmLiftedPhysicalReport : Measurable ejmLiftedPhysicalReport.{u} :=
  measurable_ejmLiftedPrefixReport.comp (measurable_frestrictLe 2)

theorem oneEbit_lifted_report_prefixAction (X : JointMatrix 4 4) (j : Fin 4) :
    (liftedOfProtocol.{u} oneEbitProtocol).represented_physicalPrefixAction 3
      {h | ejmLiftedPrefixReport h = j} X =
        (ofProtocol oneEbitProtocol).represented_physicalPrefixAction 3 {h | ejmPrefixReport h = j} X := by
  have hs := hasSum_physicalPrefixAction_singletons_on_event
    (ofProtocol oneEbitProtocol) 3 {h | ejmPrefixReport h = j}
    (measurableSet_eq_fun measurable_ejmPrefixReport measurable_const) X
  have he (h : History ℕ 3) :
      (if historyEquiv natLiftEquiv.{u} 3 h ∈ {h | ejmLiftedPrefixReport h = j} then
        (liftedOfProtocol oneEbitProtocol).represented_physicalPrefixAction 3
          {historyEquiv natLiftEquiv.{u} 3 h} X else 0) =
        if h ∈ {h | ejmPrefixReport h = j} then
          (ofProtocol oneEbitProtocol).represented_physicalPrefixAction 3 {h} X else 0 := by
    by_cases hj : ejmPrefixReport h = j
    · have hl : historyEquiv natLiftEquiv.{u} 3 h ∈ {h | ejmLiftedPrefixReport h = j} := by
        simpa only [Set.mem_setOf_eq, ejmLiftedPrefixReport,
          MeasurableEquiv.symm_apply_apply] using hj
      rw [if_pos hl, if_pos (show h ∈ {h | ejmPrefixReport h = j} from hj),
        physicalPrefixAction_liftedOfProtocol_singleton,
        liftedRawPrefix_eq, physicalPrefixAction_ofProtocol_singleton]
    · have hl : historyEquiv natLiftEquiv.{u} 3 h ∉ {h | ejmLiftedPrefixReport h = j} := by
        simpa only [Set.mem_setOf_eq, ejmLiftedPrefixReport,
          MeasurableEquiv.symm_apply_apply] using hj
      rw [if_neg hl, if_neg (show h ∉ {h | ejmPrefixReport h = j} from hj)]
  have hs' : HasSum (fun h : History (ULift.{u} ℕ) 3 =>
      if h ∈ {h | ejmLiftedPrefixReport h = j} then
        (liftedOfProtocol oneEbitProtocol).represented_physicalPrefixAction 3 {h} X else 0)
      ((ofProtocol oneEbitProtocol).represented_physicalPrefixAction 3 {h | ejmPrefixReport h = j} X) := by
    apply (historyEquiv natLiftEquiv.{u} 3).toEquiv.hasSum_iff.mp
    simp only [Function.comp_def, MeasurableEquiv.coe_toEquiv, he]
    convert hs using 1
    funext h
    by_cases hj : h ∈ {h | ejmPrefixReport h = j} <;> simp only [hj, ite_true, ite_false]
  have hactual : HasSum (fun h : History (ULift.{u} ℕ) 3 =>
      if h ∈ {h | ejmLiftedPrefixReport h = j} then
        (liftedOfProtocol oneEbitProtocol).represented_physicalPrefixAction 3 {h} X else 0)
      ((liftedOfProtocol oneEbitProtocol).represented_physicalPrefixAction 3
        {h | ejmLiftedPrefixReport h = j} X) := by
    convert hasSum_physicalPrefixAction_singletons_on_event
      (liftedOfProtocol oneEbitProtocol) 3 {h | ejmLiftedPrefixReport h = j}
      (measurableSet_eq_fun measurable_ejmLiftedPrefixReport measurable_const) X using 1
    funext h
    by_cases hj : h ∈ {h | ejmLiftedPrefixReport h = j} <;> simp only [hj, ite_true, ite_false]
  exact hactual.unique hs'

theorem oneEbit_lifted_physicalBorn_report (ρ : Matrix SystemIndex SystemIndex ℂ)
    (hρ : ρ.PosSemidef) (j : Fin 4) :
    (liftedOfProtocol.{u} oneEbitProtocol).represented_physicalBornMeasure
      (matrixResourceEmbedding * ρ * matrixResourceEmbeddingᴴ)
      (hρ.mul_mul_conjTranspose_same matrixResourceEmbedding)
      {ω | ejmLiftedPhysicalReport ω = j} =
        ENNReal.ofReal ((Matrix.trace (represented_physicalEffect j * ρ)).re) := by
  change (liftedOfProtocol oneEbitProtocol).represented_physicalBornMeasure _ _
    ((frestrictLe (π := fun _ => ULift.{u} ℕ) 2) ⁻¹' {h | ejmLiftedPrefixReport h = j}) = _
  rw [MatrixProcess.physicalBornMeasure_prefix _ _ _ _ _
      (measurableSet_eq_fun measurable_ejmLiftedPrefixReport measurable_const),
    oneEbit_lifted_report_prefixAction, oneEbit_report_prefix_trace,
    oneEbitProtocol_physical_output]
  change ENNReal.ofReal ((Tomography.measurementChannel represented_physicalEffect ρ (j,j) (j,j)).re) = _
  rw [Tomography.measurementChannel_entry]

end QuantumProver.ElegantJointMeasurement.NormalCost

namespace QuantumProver.ElegantJointMeasurement.NormalCost

open QuantumProver.ElegantJointMeasurement.Teleportation.PhysicalUpper
open QuantumProver.ElegantJointMeasurement.HilbertFiniteNormalRecordLift

theorem oneEbit_matrixCodeMatrix :
    matrixCodeMatrix alicePhysicalEquiv bobPhysicalEquiv resource = matrixResourceEmbedding := by
  let C := one_ebit_physical_upper_certificate
  have hCode : QuantumProver.ElegantJointMeasurement.GeneralResource.codeMatrix resource = physicalEmbedding := by
    apply Matrix.toEuclideanLin.injective
    have hC : (Matrix.toEuclideanLin (QuantumProver.ElegantJointMeasurement.GeneralResource.codeMatrix resource)).toContinuousLinearMap =
        (Matrix.toEuclideanLin physicalEmbedding).toContinuousLinearMap := by
      rw [← QuantumProver.ElegantJointMeasurement.GeneralResource.codeContinuous_eq_matrix, ← C.physical_resource,
        QuantumProver.ElegantJointMeasurement.GeneralResource.codeContinuous_diagonal]
      exact C.physical_resource_code
    exact congrArg ContinuousLinearMap.toLinearMap hC
  unfold matrixCodeMatrix
  rw [hCode]
  ext z q
  change matrixResourceEmbedding ((alicePhysicalEquiv.prodCongr bobPhysicalEquiv)
    ((alicePhysicalEquiv.prodCongr bobPhysicalEquiv).symm z)) q = _
  rw [Equiv.apply_symm_apply]

theorem oneEbit_resource_normalized : (resource * resourceᴴ).trace = 1 :=
  one_ebit_alice_reduced_density.2

theorem oneEbit_resource_entropy :
    QuantumProver.ElegantJointMeasurement.TailReference.vonNeumannEntropyBits (resource * resourceᴴ) = 1 :=
  one_ebit_alice_reduced_entropy

theorem oneEbit_lifted_physicalResourceDensityOutput
    (ρ : Matrix SystemIndex SystemIndex ℂ) (hρ : ρ.PosSemidef) :
    physicalResourceDensityOutput alicePhysicalEquiv bobPhysicalEquiv
      (liftedOfProtocol.{u} oneEbitProtocol) ejmLiftedPhysicalReport resource ρ hρ =
        physicalClassicalChannel ρ := by
  unfold physicalResourceDensityOutput
  simp only [oneEbit_matrixCodeMatrix]
  change _ = Tomography.measurementChannel represented_physicalEffect ρ
  apply Finset.sum_congr rfl
  intro j hj
  have hnon : 0 ≤ (Matrix.trace (represented_physicalEffect j * ρ)).re :=
    QuantumProver.ElegantJointMeasurement.HilbertTranscriptPOVM.MatrixProbe.bornScalar_nonneg
      ρ (represented_physicalEffect j) hρ (represented_physicalEffect_posSemidef j)
  rw [oneEbit_lifted_physicalBorn_report ρ hρ j,
    ENNReal.toReal_ofReal hnon,
    QuantumProver.ElegantJointMeasurement.PreparedReports.trace_mul_psd_re_cast _ _ (represented_physicalEffect_posSemidef j) hρ]

def ImplementsInPhysicalNormalExact {κ : Type} [Fintype κ] [DecidableEq κ]
    (Ψ : Matrix κ κ ℂ) : Prop :=
  ∃ (m n : ℕ) (ea : (Fin 2 × κ) ≃ Fin m) (eb : (Fin 2 × κ) ≃ Fin n)
    (hm : NeZero m) (hn : NeZero n),
    letI : NeZero m := hm
    letI : NeZero n := hn
    ∃ (R : Type u) (M : MeasurableSpace R),
      letI : MeasurableSpace R := M
      ∃ (S : StandardBorelSpace R),
        letI : StandardBorelSpace R := S
        ∃ (P : MatrixProcess m n R) (J : Transcript R → Fin 4),
          NullMeasurable J (P.represented_physicalBornMeasure
            (preparedReference (matrixCodeMatrix ea eb Ψ))
            (preparedReference_positive (matrixCodeMatrix ea eb Ψ))) ∧
          ∀ (σ : Matrix SystemIndex SystemIndex ℂ) (hσ : σ.PosSemidef), σ.trace = 1 →
            physicalResourceDensityOutput ea eb P J Ψ σ hσ = physicalClassicalChannel σ

def ImplementsInPhysicalNormalOperational {κ : Type} [Fintype κ] [DecidableEq κ]
    (Ψ : Matrix κ κ ℂ) : Prop :=
  ∃ (m n : ℕ) (ea : (Fin 2 × κ) ≃ Fin m) (eb : (Fin 2 × κ) ≃ Fin n)
    (hm : NeZero m) (hn : NeZero n),
    letI : NeZero m := hm
    letI : NeZero n := hn
    ∃ (R : ℕ → Type u) (M : ∀ k, MeasurableSpace (R k)),
      letI : ∀ k, MeasurableSpace (R k) := M
      ∃ (S : ∀ k, StandardBorelSpace (R k)),
        letI : ∀ k, StandardBorelSpace (R k) := S
        ∃ (P : ∀ k, MatrixProcess m n (R k)) (J : ∀ k, Transcript (R k) → Fin 4),
          (∀ k, NullMeasurable (J k) ((P k).represented_physicalBornMeasure
            (preparedReference (matrixCodeMatrix ea eb Ψ))
            (preparedReference_positive (matrixCodeMatrix ea eb Ψ)))) ∧
          ∀ (σ : Matrix SystemIndex SystemIndex ℂ) (hσ : σ.PosSemidef), σ.trace = 1 →
            Tendsto (fun k => physicalResourceDensityOutput ea eb (P k) (J k) Ψ σ hσ)
              atTop (𝓝 (physicalClassicalChannel σ))

theorem physicalNormal_exact_implies_operational {κ : Type} [Fintype κ] [DecidableEq κ]
    (Ψ : Matrix κ κ ℂ)
    (h : ImplementsInPhysicalNormalExact.{u} Ψ) : ImplementsInPhysicalNormalOperational.{u} Ψ := by
  rcases h with ⟨m,n,ea,eb,hm,hn,R,M,S,P,J,hJ,hC⟩
  letI : NeZero m := hm
  letI : NeZero n := hn
  letI : MeasurableSpace R := M
  letI : StandardBorelSpace R := S
  refine ⟨m,n,ea,eb,hm,hn,(fun _ => R),(fun _ => M),(fun _ => S),
    (fun _ => P),(fun _ => J),(fun _ => hJ),?_⟩
  intro σ hσ ht
  simpa only [hC σ hσ ht] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => physicalClassicalChannel σ) atTop
      (𝓝 (physicalClassicalChannel σ)))

theorem physicalNormal_operational_implementation_entropy_ge_one
    {κ : Type} [Fintype κ] [DecidableEq κ]
    (Ψ : Matrix κ κ ℂ) (hΨ : (Ψ * Ψᴴ).trace = 1)
    (h : ImplementsInPhysicalNormalOperational.{u} Ψ) :
    1 ≤ QuantumProver.ElegantJointMeasurement.TailReference.vonNeumannEntropyBits (Ψ * Ψᴴ) := by
  rcases h with ⟨m,n,ea,eb,hm,hn,R,M,S,P,J,hJ,hC⟩
  letI : NeZero m := hm
  letI : NeZero n := hn
  letI : ∀ k, MeasurableSpace (R k) := M
  letI : ∀ k, StandardBorelSpace (R k) := S
  exact physical_normal_varying_records_density_limit_entropy_ge_one Ψ hΨ ea eb P J hJ hC

theorem oneEbit_implements_in_physicalNormal_exact :
    ImplementsInPhysicalNormalExact.{u} resource := by
  refine ⟨4,4,alicePhysicalEquiv,bobPhysicalEquiv,inferInstance,inferInstance,
    ULift.{u} ℕ,inferInstance,inferInstance,liftedOfProtocol oneEbitProtocol,
    ejmLiftedPhysicalReport,?_,?_⟩
  · exact measurable_ejmLiftedPhysicalReport.nullMeasurable
  · intro σ hσ ht
    exact oneEbit_lifted_physicalResourceDensityOutput σ hσ

def physicalNormalExactCostSet : Set ℝ :=
  {c | ∃ (r : ℕ) (_hr : 0 < r) (Ψ : Matrix (Fin r) (Fin r) ℂ),
    (Ψ * Ψᴴ).trace = 1 ∧ ImplementsInPhysicalNormalExact.{u} Ψ ∧
      QuantumProver.ElegantJointMeasurement.TailReference.vonNeumannEntropyBits (Ψ * Ψᴴ) = c}

def physicalNormalOperationalCostSet : Set ℝ :=
  {c | ∃ (r : ℕ) (_hr : 0 < r) (Ψ : Matrix (Fin r) (Fin r) ℂ),
    (Ψ * Ψᴴ).trace = 1 ∧ ImplementsInPhysicalNormalOperational.{u} Ψ ∧
      QuantumProver.ElegantJointMeasurement.TailReference.vonNeumannEntropyBits (Ψ * Ψᴴ) = c}

theorem physicalNormalExactCostSet_subset_operational :
    physicalNormalExactCostSet.{u} ⊆ physicalNormalOperationalCostSet.{u} := by
  rintro c ⟨r,hr,Ψ,hΨ,hI,he⟩
  exact ⟨r,hr,Ψ,hΨ,physicalNormal_exact_implies_operational Ψ hI,he⟩

theorem physicalNormalOperationalCostSet_lower {c : ℝ}
    (hc : c ∈ physicalNormalOperationalCostSet.{u}) : 1 ≤ c := by
  rcases hc with ⟨r,hr,Ψ,hΨ,hI,he⟩
  rw [← he]
  exact physicalNormal_operational_implementation_entropy_ge_one Ψ hΨ hI

theorem physicalNormalExactCostSet_lower {c : ℝ}
    (hc : c ∈ physicalNormalExactCostSet.{u}) : 1 ≤ c :=
  physicalNormalOperationalCostSet_lower (physicalNormalExactCostSet_subset_operational hc)

theorem one_mem_physicalNormalExactCostSet : (1 : ℝ) ∈ physicalNormalExactCostSet.{u} :=
  ⟨2,by decide,resource,oneEbit_resource_normalized,
    oneEbit_implements_in_physicalNormal_exact,oneEbit_resource_entropy⟩

theorem one_mem_physicalNormalOperationalCostSet : (1 : ℝ) ∈ physicalNormalOperationalCostSet.{u} :=
  physicalNormalExactCostSet_subset_operational one_mem_physicalNormalExactCostSet

theorem physicalNormal_exact_cost_eq_one : sInf physicalNormalExactCostSet.{u} = 1 := by
  apply le_antisymm
  · exact csInf_le ⟨1,fun _ hc => physicalNormalExactCostSet_lower hc⟩ one_mem_physicalNormalExactCostSet
  · exact le_csInf ⟨1,one_mem_physicalNormalExactCostSet⟩ fun _ hc => physicalNormalExactCostSet_lower hc

theorem physicalNormal_operational_cost_eq_one : sInf physicalNormalOperationalCostSet.{u} = 1 := by
  apply le_antisymm
  · exact csInf_le ⟨1,fun _ hc => physicalNormalOperationalCostSet_lower hc⟩ one_mem_physicalNormalOperationalCostSet
  · exact le_csInf ⟨1,one_mem_physicalNormalOperationalCostSet⟩ fun _ hc => physicalNormalOperationalCostSet_lower hc

def physicalNormalPaddedExactCostSet : Set ℝ :=
  {c | ∃ (rA rB : ℕ) (_hrA : 0 < rA) (_hrB : 0 < rB)
      (Ψ : Matrix (Fin rA) (Fin rB) ℂ),
    (Ψ * Ψᴴ).trace = 1 ∧
      ImplementsInPhysicalNormalExact.{u} (QuantumProver.ElegantJointMeasurement.SchmidtResource.SquarePadding.coefficient Ψ) ∧
      QuantumProver.ElegantJointMeasurement.TailReference.vonNeumannEntropyBits (Ψ * Ψᴴ) = c}

def physicalNormalPaddedOperationalCostSet : Set ℝ :=
  {c | ∃ (rA rB : ℕ) (_hrA : 0 < rA) (_hrB : 0 < rB)
      (Ψ : Matrix (Fin rA) (Fin rB) ℂ),
    (Ψ * Ψᴴ).trace = 1 ∧
      ImplementsInPhysicalNormalOperational.{u} (QuantumProver.ElegantJointMeasurement.SchmidtResource.SquarePadding.coefficient Ψ) ∧
      QuantumProver.ElegantJointMeasurement.TailReference.vonNeumannEntropyBits (Ψ * Ψᴴ) = c}

theorem physicalNormalPaddedExactCostSet_subset_operational :
    physicalNormalPaddedExactCostSet.{u} ⊆ physicalNormalPaddedOperationalCostSet.{u} := by
  rintro c ⟨rA,rB,hrA,hrB,Ψ,hΨ,hI,he⟩
  exact ⟨rA,rB,hrA,hrB,Ψ,hΨ,physicalNormal_exact_implies_operational _ hI,he⟩

theorem physicalNormalPaddedOperationalCostSet_lower {c : ℝ}
    (hc : c ∈ physicalNormalPaddedOperationalCostSet.{u}) : 1 ≤ c := by
  rcases hc with ⟨rA,rB,hrA,hrB,Ψ,hΨ,hI,he⟩
  have h := physicalNormal_operational_implementation_entropy_ge_one
    (QuantumProver.ElegantJointMeasurement.SchmidtResource.SquarePadding.coefficient Ψ)
    (QuantumProver.ElegantJointMeasurement.SchmidtResource.SquarePadding.normalized_coefficient Ψ hΨ) hI
  simpa only [QuantumProver.ElegantJointMeasurement.SchmidtResource.SquarePadding.coefficient_entropy, he] using h

def physicalNormalAllFiniteExactCostSet : Set ℝ :=
  physicalNormalExactCostSet.{u} ∪ physicalNormalPaddedExactCostSet.{u}

def physicalNormalAllFiniteOperationalCostSet : Set ℝ :=
  physicalNormalOperationalCostSet.{u} ∪ physicalNormalPaddedOperationalCostSet.{u}

theorem physicalNormalAllFiniteExactCostSet_subset_operational :
    physicalNormalAllFiniteExactCostSet.{u} ⊆ physicalNormalAllFiniteOperationalCostSet.{u} :=
  Set.union_subset_union physicalNormalExactCostSet_subset_operational
    physicalNormalPaddedExactCostSet_subset_operational

theorem physicalNormalAllFiniteOperationalCostSet_lower {c : ℝ}
    (hc : c ∈ physicalNormalAllFiniteOperationalCostSet.{u}) : 1 ≤ c := by
  rcases hc with hc | hc
  · exact physicalNormalOperationalCostSet_lower hc
  · exact physicalNormalPaddedOperationalCostSet_lower hc

theorem physicalNormalAllFiniteExactCostSet_lower {c : ℝ}
    (hc : c ∈ physicalNormalAllFiniteExactCostSet.{u}) : 1 ≤ c :=
  physicalNormalAllFiniteOperationalCostSet_lower
    (physicalNormalAllFiniteExactCostSet_subset_operational hc)

theorem one_mem_physicalNormalAllFiniteExactCostSet :
    (1 : ℝ) ∈ physicalNormalAllFiniteExactCostSet.{u} :=
  Or.inl one_mem_physicalNormalExactCostSet

theorem one_mem_physicalNormalAllFiniteOperationalCostSet :
    (1 : ℝ) ∈ physicalNormalAllFiniteOperationalCostSet.{u} :=
  physicalNormalAllFiniteExactCostSet_subset_operational one_mem_physicalNormalAllFiniteExactCostSet

theorem physicalNormal_all_finite_exact_cost_eq_one :
    sInf physicalNormalAllFiniteExactCostSet.{u} = 1 := by
  apply le_antisymm
  · exact csInf_le ⟨1,fun _ hc => physicalNormalAllFiniteExactCostSet_lower hc⟩
      one_mem_physicalNormalAllFiniteExactCostSet
  · exact le_csInf ⟨1,one_mem_physicalNormalAllFiniteExactCostSet⟩
      fun _ hc => physicalNormalAllFiniteExactCostSet_lower hc

theorem physicalNormal_all_finite_operational_cost_eq_one :
    sInf physicalNormalAllFiniteOperationalCostSet.{u} = 1 := by
  apply le_antisymm
  · exact csInf_le ⟨1,fun _ hc => physicalNormalAllFiniteOperationalCostSet_lower hc⟩
      one_mem_physicalNormalAllFiniteOperationalCostSet
  · exact le_csInf ⟨1,one_mem_physicalNormalAllFiniteOperationalCostSet⟩
      fun _ hc => physicalNormalAllFiniteOperationalCostSet_lower hc

end QuantumProver.ElegantJointMeasurement.NormalCost

namespace QuantumProver.ElegantJointMeasurement.NormalCost

open QuantumProver.MatrixNormalFreePreparationChronology
open QuantumProver.ElegantJointMeasurement.NormalAncillaPreparation QuantumProver.ElegantJointMeasurement.NuclearChoi
open TopologicalSpace

section FreePreparation
variable {R : Type*} [MeasurableSpace R]
variable {a b : ℕ}
variable {FA FB : Type*}
  [NormedAddCommGroup FA] [InnerProductSpace ℂ FA] [CompleteSpace FA] [SeparableSpace FA]
  [NormedAddCommGroup FB] [InnerProductSpace ℂ FB] [CompleteSpace FB] [SeparableSpace FB]

def matrixRawFamilies (P : MatrixProcess a b R) : RawFamilies R where
  alice := P.alice
  bob := P.bob
  aliceTurn := P.aliceTurn
  turn_measurable := P.turn_measurable

def insertMixedMatrixProcess (P : MatrixProcess a b R) (τA : Nuclear FA) (τB : Nuclear FB)
    (hA : (QuantumProver.NuclearOperator.toOperator τA).IsPositive)
    (hB : (QuantumProver.NuclearOperator.toOperator τB).IsPositive)
    (hAT : QuantumProver.HilbertNuclearTrace.trace τA = 1)
    (hBT : QuantumProver.HilbertNuclearTrace.trace τB = 1) : MatrixProcess a b (PreparationRecord R) :=
  let F := insertMixedPreparation (matrixRawFamilies P) τA τB hA hB hAT hBT
  { initialAlice := P.initialAlice
    initialBob := P.initialBob
    alice := F.alice
    bob := F.bob
    aliceTurn := F.aliceTurn
    turn_measurable := F.turn_measurable }

theorem insertMixedMatrixProcess_initialAlice (P : MatrixProcess a b R)
    (τA : Nuclear FA) (τB : Nuclear FB) (hA : (QuantumProver.NuclearOperator.toOperator τA).IsPositive)
    (hB : (QuantumProver.NuclearOperator.toOperator τB).IsPositive)
    (hAT : QuantumProver.HilbertNuclearTrace.trace τA = 1)
    (hBT : QuantumProver.HilbertNuclearTrace.trace τB = 1) :
    (insertMixedMatrixProcess P τA τB hA hB hAT hBT).initialAlice = P.initialAlice := rfl

theorem insertMixedMatrixProcess_initialBob (P : MatrixProcess a b R)
    (τA : Nuclear FA) (τB : Nuclear FB) (hA : (QuantumProver.NuclearOperator.toOperator τA).IsPositive)
    (hB : (QuantumProver.NuclearOperator.toOperator τB).IsPositive)
    (hAT : QuantumProver.HilbertNuclearTrace.trace τA = 1)
    (hBT : QuantumProver.HilbertNuclearTrace.trace τB = 1) :
    (insertMixedMatrixProcess P τA τB hA hB hAT hBT).initialBob = P.initialBob := rfl

variable [StandardBorelSpace R] [NeZero a] [NeZero b]

private theorem preparationRecord_borelSpace [TopologicalSpace R] [BorelSpace R] :
    BorelSpace (PreparationRecord R) := by
  constructor
  apply le_antisymm
  · intro s hs
    have hl := (measurableSet_sum_iff.mp hs).1
    have hr := (measurableSet_sum_iff.mp hs).2
    letI : MeasurableSpace (PreparationRecord R) := borel (PreparationRecord R)
    letI : BorelSpace (PreparationRecord R) := ⟨rfl⟩
    have he : s = Sum.inl '' (Sum.inl ⁻¹' s) ∪ Sum.inr '' (Sum.inr ⁻¹' s) := by
      ext z
      constructor
      · intro hz
        cases z with
        | inl x => exact Or.inl (Set.mem_image_of_mem Sum.inl hz)
        | inr y => exact Or.inr (Set.mem_image_of_mem Sum.inr hz)
      · rintro (⟨x,hx,rfl⟩ | ⟨y,hy,rfl⟩)
        · exact hx
        · exact hy
    rw [he]
    exact (Topology.IsOpenEmbedding.inl.measurableEmbedding.measurableSet_image' hl).union
      (Topology.IsOpenEmbedding.inr.measurableEmbedding.measurableSet_image' hr)
  · apply MeasurableSpace.generateFrom_le
    intro s hs
    exact measurableSet_sum_iff.mpr
      ⟨(isOpen_sum_iff.mp hs).1.measurableSet, (isOpen_sum_iff.mp hs).2.measurableSet⟩

local instance preparationRecord_standardBorel : StandardBorelSpace (PreparationRecord R) := by
  letI := upgradeStandardBorel R
  letI : BorelSpace (PreparationRecord R) := preparationRecord_borelSpace
  infer_instance

theorem insertMixedMatrixProcess_initialJointOperation (P : MatrixProcess a b R)
    (τA : Nuclear FA) (τB : Nuclear FB) (hA : (QuantumProver.NuclearOperator.toOperator τA).IsPositive)
    (hB : (QuantumProver.NuclearOperator.toOperator τB).IsPositive)
    (hAT : QuantumProver.HilbertNuclearTrace.trace τA = 1)
    (hBT : QuantumProver.HilbertNuclearTrace.trace τB = 1) :
    (insertMixedMatrixProcess P τA τB hA hB hAT hBT).initialJointOperation =
      P.initialJointOperation := rfl

theorem insertMixedMatrixProcess_physicalStep (P : MatrixProcess a b R)
    (τA : Nuclear FA) (τB : Nuclear FB) (hA : (QuantumProver.NuclearOperator.toOperator τA).IsPositive)
    (hB : (QuantumProver.NuclearOperator.toOperator τB).IsPositive)
    (hAT : QuantumProver.HilbertNuclearTrace.trace τA = 1)
    (hBT : QuantumProver.HilbertNuclearTrace.trace τB = 1)
    (n : ℕ) (h : History R n) (s : Set R) (hs : MeasurableSet s) :
    ((insertMixedMatrixProcess P τA τB hA hB hAT hBT).represented_physicalStepInstrument (n+2)).operation
      (padHistory n h) (Sum.inr '' s) = (P.represented_physicalStepInstrument n).operation h s := by
  change rawEventAction (insertMixedPreparation (matrixRawFamilies P) τA τB hA hB hAT hBT)
    (n+2) (padHistory n h) (Sum.inr '' s) = rawEventAction (matrixRawFamilies P) n h s
  exact inserted_physical_joint_event (matrixRawFamilies P)
    (commonPreparation (E := QuantumProver.ElegantJointMeasurement.NormalProcess.Workspace) τA)
    (commonPreparation (E := QuantumProver.ElegantJointMeasurement.NormalProcess.Workspace) τB)
    (commonPreparation_completelyPositive τA hA) (commonPreparation_completelyPositive τB hB)
    (trace_commonPreparation τA hAT) (trace_commonPreparation τB hBT) n h s hs

theorem insertMixedMatrixProcess_preparation_singletons (P : MatrixProcess a b R)
    (τA : Nuclear FA) (τB : Nuclear FB) (hA : (QuantumProver.NuclearOperator.toOperator τA).IsPositive)
    (hB : (QuantumProver.NuclearOperator.toOperator τB).IsPositive)
    (hAT : QuantumProver.HilbertNuclearTrace.trace τA = 1)
    (hBT : QuantumProver.HilbertNuclearTrace.trace τB = 1)
    (W : Nuclear JointWorkspace) :
    ((insertMixedMatrixProcess P τA τB hA hB hAT hBT).represented_physicalStepInstrument 1).operation
      firstPreparationHistory {preparationTag}
      (((insertMixedMatrixProcess P τA τB hA hB hAT hBT).represented_physicalStepInstrument 0).operation
        PUnit.unit {preparationTag} W) = mixedJointPreparation τA τB hA hB hAT hBT W := by
  let F := insertMixedPreparation (matrixRawFamilies P) τA τB hA hB hAT hBT
  have h0 : rawEventAction F 0 PUnit.unit {preparationTag} =
      rawEventAction F 0 PUnit.unit univ := by
    simp only [F, insertMixedPreparation, rawEventAction, insertLocalPreparations, ite_true]
    rw [QuantumProver.MatrixNormalTensorInstrument.tensorOperation_of_measurable _ _ _
      measurableSet_preparationTag,
      QuantumProver.MatrixNormalTensorInstrument.tensorOperation_of_measurable _ _ _ MeasurableSet.univ]
    simp only [taggedSingleton_operation, mem_singleton_iff, mem_univ, ite_true]
  have h1 : rawEventAction F 1 firstPreparationHistory {preparationTag} =
      rawEventAction F 1 firstPreparationHistory univ := by
    simp only [F, insertMixedPreparation, rawEventAction, insertLocalPreparations,
      Bool.false_eq_true, ite_false]
    rw [QuantumProver.MatrixNormalRightTensor.rightTensorOperation_of_measurable _ _ _
      measurableSet_preparationTag,
      QuantumProver.MatrixNormalRightTensor.rightTensorOperation_of_measurable _ _ _ MeasurableSet.univ]
    simp only [secondPreparation_operation, mem_singleton_iff, mem_univ, ite_true]
  change rawEventAction F 1 firstPreparationHistory {preparationTag}
    (rawEventAction F 0 PUnit.unit {preparationTag} W) = _
  rw [h1, h0]
  exact mixed_preparation_all_input_action (matrixRawFamilies P) τA τB hA hB hAT hBT W

theorem insertMixedMatrixProcess_physicalPrefix_two (P : MatrixProcess a b R)
    (τA : Nuclear FA) (τB : Nuclear FB) (hA : (QuantumProver.NuclearOperator.toOperator τA).IsPositive)
    (hB : (QuantumProver.NuclearOperator.toOperator τB).IsPositive)
    (hAT : QuantumProver.HilbertNuclearTrace.trace τA = 1)
    (hBT : QuantumProver.HilbertNuclearTrace.trace τB = 1) (X : JointMatrix a b) :
    (insertMixedMatrixProcess P τA τB hA hB hAT hBT).represented_physicalPrefixAction 2 {preparationHistory} X =
      mixedJointPreparation τA τB hA hB hAT hBT (P.initialJointOperation X) := by
  change (insertMixedMatrixProcess P τA τB hA hB hAT hBT).represented_physicalPrefixAction 2
    {appendHistory 1 (appendHistory 0 (PUnit.unit, preparationTag), preparationTag)} X = _
  rw [MatrixProcess.physicalPrefixAction_singleton_successor,
    MatrixProcess.physicalPrefixAction_singleton_successor,
    MatrixProcess.physicalPrefixAction_zero_singleton,
    insertMixedMatrixProcess_initialJointOperation]
  exact insertMixedMatrixProcess_preparation_singletons P τA τB hA hB hAT hBT
    (P.initialJointOperation X)

end FreePreparation
end QuantumProver.ElegantJointMeasurement.NormalCost

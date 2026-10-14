import QuantumProver.InformationTheory.WernerEndpoint.FiniteNormalInstrument
import QuantumProver.InformationTheory.WernerEndpoint.OperationalEndpointCost
import QuantumProver.InformationTheory.ElegantJointMeasurement.RecordCoding
import QuantumProver.InformationTheory.ElegantJointMeasurement.NormalCostModels
import QuantumProver.InformationTheory.ElegantJointMeasurement.HilbertPendingTensor
import QuantumProver.QuantumChannels.NormalRightTensor
import QuantumProver.InformationTheory.WernerEndpoint.FiniteNormalTerminal

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory Set Function InnerProductSpace
open QuantumProver.ElegantJointMeasurement.SeparableHilbertEmbedding QuantumProver.ElegantJointMeasurement.NuclearChoi
open QuantumProver.ElegantJointMeasurement.NormalInstrumentAbsorption QuantumProver.ElegantJointMeasurement.HilbertRecovery
open QuantumProver.ElegantJointMeasurement.HilbertSquareProcess (History appendHistory)
open scoped BigOperators Topology ComplexOrder MatrixOrder Matrix Matrix.Norms.L2Operator Classical
  Kronecker

namespace QuantumProver.ElegantJointMeasurement.HilbertFiniteNormalChronology

abbrev Protocol := QuantumProver.WernerEndpoint.OperationalEndpointCost.FiniteLocalProtocol

local instance finiteOutcomeMeasurable (h : ℕ) : MeasurableSpace (Fin h) := ⊤
local instance finiteOutcomeSingletons (h : ℕ) : MeasurableSingletonClass (Fin h) :=
  ⟨fun _ => trivial⟩
local instance finiteComplete (a : ℕ) : CompleteSpace (EuclideanSpace ℂ (Fin a)) :=
  PiLp.completeSpace 2 (fun _ : Fin a => ℂ)
local instance sourceComplete (I : Type) [Fintype I] :
    CompleteSpace (EuclideanSpace ℂ I) := PiLp.completeSpace 2 (fun _ : I => ℂ)

def finiteCode (a : ℕ) : EuclideanSpace ℂ (Fin a) →ₗᵢ[ℂ] CommonHilbert :=
  separableEmbedding

def encodeFiniteOutcome (h : ℕ) : Fin h ⊕ Unit → ℕ
  | .inl j => j.val + 1
  | .inr _ => 0

theorem measurable_encodeFiniteOutcome (h : ℕ) : Measurable (encodeFiniteOutcome h) :=
  measurable_fun_sum (measurable_of_countable _) measurable_const

theorem encodeFiniteOutcome_injective (h : ℕ) : Injective (encodeFiniteOutcome h) := by
  intro x y hxy
  cases x with
  | inl i =>
      cases y with
      | inl j =>
          apply congrArg Sum.inl
          apply Fin.ext
          exact Nat.add_right_cancel hxy
      | inr u => simp [encodeFiniteOutcome] at hxy
  | inr u =>
      cases y with
      | inl j => simp [encodeFiniteOutcome] at hxy
      | inr v => cases u; cases v; rfl

theorem encodeFiniteOutcome_preimage_zero (h : ℕ) :
    encodeFiniteOutcome h ⁻¹' {0} = {Sum.inr ()} := by
  ext x
  cases x <;> simp [encodeFiniteOutcome]

theorem encodeFiniteOutcome_preimage_visible (h : ℕ) (j : Fin h) :
    encodeFiniteOutcome h ⁻¹' {j.val + 1} = {Sum.inl j} := by
  simpa only [Set.image_singleton, encodeFiniteOutcome] using
    (encodeFiniteOutcome_injective h).preimage_image ({Sum.inl j} : Set (Fin h ⊕ Unit))

section FiniteNode

variable {a p h z : ℕ}

def finiteNode (K : Fin h → Fin z → Matrix (Fin p) (Fin a) ℂ)
    (hK : ∑ j, ∑ k, (K j k).conjTranspose * K j k = 1) :
    Instrument CommonHilbert CommonHilbert Unit ℕ :=
  QuantumProver.ElegantJointMeasurement.HilbertRecordCoding.pushforwardInstrument
    (QuantumProver.WernerEndpoint.MatrixFiniteNormalInstrument.commonInstrument
      (fun _ : Unit => K) (fun _ _ => measurable_const)
      (finiteCode a) (finiteCode p) (fun _ => hK))
    (encodeFiniteOutcome h) (measurable_encodeFiniteOutcome h)

theorem finiteNode_all_events
    (K : Fin h → Fin z → Matrix (Fin p) (Fin a) ℂ)
    (hK : ∑ j, ∑ k, (K j k).conjTranspose * K j k = 1)
    (s : Set ℕ) (X : Matrix (Fin a) (Fin a) ℂ) :
    (finiteNode K hK).operation () s (padNuclear (finiteCode a) (nuclearMatrix X)) =
      padNuclear (finiteCode p) (nuclearMatrix
        (QuantumProver.WernerEndpoint.MatrixFiniteNormalInstrument.matrixEvent K
          {j | j.val + 1 ∈ s} X)) := by
  exact QuantumProver.WernerEndpoint.MatrixFiniteNormalInstrument.commonInstrument_matrix_event
    (fun _ : Unit => K) (fun _ _ => measurable_const) (finiteCode a) (finiteCode p)
    (fun _ => hK) () (encodeFiniteOutcome h ⁻¹' s) X

theorem finiteNode_zero_record
    (K : Fin h → Fin z → Matrix (Fin p) (Fin a) ℂ)
    (hK : ∑ j, ∑ k, (K j k).conjTranspose * K j k = 1)
    (T : QuantumProver.WernerEndpoint.MatrixFiniteNormalInstrument.FiniteNuclear a) :
    (finiteNode K hK).operation () {0} (padNuclear (finiteCode a) T) = 0 := by
  change (QuantumProver.WernerEndpoint.MatrixFiniteNormalInstrument.commonInstrument
    (fun _ : Unit => K) (fun _ _ => measurable_const)
    (finiteCode a) (finiteCode p) (fun _ => hK)).operation ()
      (encodeFiniteOutcome h ⁻¹' {0}) (padNuclear (finiteCode a) T) = 0
  rw [encodeFiniteOutcome_preimage_zero]
  exact QuantumProver.WernerEndpoint.MatrixFiniteNormalInstrument.commonInstrument_dummy_on_physical
    (fun _ : Unit => K) (fun _ _ => measurable_const)
    (finiteCode a) (finiteCode p) (fun _ => hK) () T

theorem finiteNode_visible_record
    (K : Fin h → Fin z → Matrix (Fin p) (Fin a) ℂ)
    (hK : ∑ j, ∑ k, (K j k).conjTranspose * K j k = 1)
    (j : Fin h) (X : Matrix (Fin a) (Fin a) ℂ) :
    (finiteNode K hK).operation () {j.val + 1}
      (padNuclear (finiteCode a) (nuclearMatrix X)) =
      padNuclear (finiteCode p) (nuclearMatrix
        (∑ k, K j k * X * (K j k).conjTranspose)) := by
  rw [finiteNode_all_events]
  congr 2
  simp [QuantumProver.WernerEndpoint.MatrixFiniteNormalInstrument.matrixEvent, Fin.val_inj]

end FiniteNode

inductive State (c d : ℕ) where
  | invalid : State c d
  | active {a b : ℕ} (T : Protocol c d a b) : State c d

namespace State

variable {c d : ℕ}

def advance : State c d → ℕ → State c d
  | .invalid, _ => .invalid
  | s@(.active (.terminal _ _ _ _)), 0 => s
  | .active (.terminal _ _ _ _), _ + 1 => .invalid
  | .active (.alice _ _ _), 0 => .invalid
  | @State.active _ _ _ _
      (@QuantumProver.WernerEndpoint.OperationalEndpointCost.FiniteLocalProtocol.alice _ _ _ _ _ h _ _K _hK next), r + 1 =>
      if hr : r < h then .active (next ⟨r, hr⟩) else .invalid
  | .active (.bob _ _ _), 0 => .invalid
  | @State.active _ _ _ _
      (@QuantumProver.WernerEndpoint.OperationalEndpointCost.FiniteLocalProtocol.bob _ _ _ _ _ h _ _K _hK next), r + 1 =>
      if hr : r < h then .active (next ⟨r, hr⟩) else .invalid

def aliceTurn : State c d → Bool
  | .active (.bob _ _ _) => false
  | _ => true

def aliceNode : State c d → Instrument CommonHilbert CommonHilbert Unit ℕ
  | .active (.alice K hK _) => finiteNode K hK
  | _ => QuantumProver.ElegantJointMeasurement.HilbertRecordCoding.dummyInstrument 0

def bobNode : State c d → Instrument CommonHilbert CommonHilbert Unit ℕ
  | .active (.bob K hK _) => finiteNode K hK
  | _ => QuantumProver.ElegantJointMeasurement.HilbertRecordCoding.dummyInstrument 0

end State

local instance historyCountable (n : ℕ) : Countable (History ℕ n) := by
  cases n <;> dsimp [QuantumProver.ElegantJointMeasurement.HilbertSquareProcess.History, QuantumProver.ElegantJointMeasurement.HilbertSquareProcess.Prefix] <;>
    infer_instance

local instance historySingletons (n : ℕ) : MeasurableSingletonClass (History ℕ n) := by
  cases n <;> dsimp [QuantumProver.ElegantJointMeasurement.HilbertSquareProcess.History, QuantumProver.ElegantJointMeasurement.HilbertSquareProcess.Prefix] <;>
    infer_instance

def state {c d a b : ℕ} (T : Protocol c d a b) : (n : ℕ) → History ℕ n → State c d
  | 0, _ => .active T
  | n + 1, h =>
      let q := (appendHistory n).symm h
      State.advance (state T n q.1) q.2

theorem state_append {c d a b : ℕ} (T : Protocol c d a b) (n : ℕ)
    (h : History ℕ n) (r : ℕ) :
    state T (n+1) (appendHistory n (h,r)) = State.advance (state T n h) r := by
  simp only [state, MeasurableEquiv.symm_apply_apply]

def instrumentFamily {c d a b : ℕ} (T : Protocol c d a b) (n : ℕ) (alice : Bool) :
    Instrument CommonHilbert CommonHilbert (History ℕ n) ℕ where
  operation h := (if alice then (state T n h).aliceNode else (state T n h).bobNode).operation ()
  empty h := by split_ifs <;> apply Instrument.empty
  countable_additivity h s hs hd U := by
    split_ifs <;> exact Instrument.countable_additivity _ () s hs hd U
  completelyPositive h s hs := by
    split_ifs <;> exact Instrument.completelyPositive _ () s hs
  measurable_coordinate s hs U x y := measurable_of_countable _
  trace_preserving h U := by
    split_ifs <;> exact Instrument.trace_preserving _ () U

theorem measurable_party {c d a b : ℕ} (T : Protocol c d a b) (n : ℕ) :
    Measurable (fun h : History ℕ n => (state T n h).aliceTurn) :=
  measurable_of_countable _

def ofProtocol {c d a b : ℕ} (T : Protocol c d a b) :
    QuantumProver.ElegantJointMeasurement.NormalProcess.MatrixProcess a b ℕ where
  initialAlice := finiteCode a
  initialBob := finiteCode b
  alice n := instrumentFamily T n true
  bob n := instrumentFamily T n false
  aliceTurn n h := (state T n h).aliceTurn
  turn_measurable := measurable_party T

@[simp] theorem ofProtocol_initialAlice {c d a b : ℕ} (T : Protocol c d a b) :
    (ofProtocol T).initialAlice = finiteCode a := rfl

@[simp] theorem ofProtocol_initialBob {c d a b : ℕ} (T : Protocol c d a b) :
    (ofProtocol T).initialBob = finiteCode b := rfl

def depth {c d a b : ℕ} : Protocol c d a b → ℕ
  | .terminal _ _ _ _ => 0
  | .alice _ _ next => 1 + Finset.univ.sup (fun j => depth (next j))
  | .bob _ _ next => 1 + Finset.univ.sup (fun j => depth (next j))

namespace State

def depth {c d : ℕ} : State c d → ℕ
  | .invalid => 0
  | .active T => QuantumProver.ElegantJointMeasurement.HilbertFiniteNormalChronology.depth T

theorem depth_advance {c d : ℕ} (s : State c d) (r : ℕ) :
    depth (advance s r) ≤ depth s - 1 := by
  cases s with
  | invalid => simp [advance, depth]
  | active T =>
      cases T with
      | terminal LA LB hLA hLB =>
          cases r <;> simp [advance, depth, QuantumProver.ElegantJointMeasurement.HilbertFiniteNormalChronology.depth]
      | alice K hK next =>
          cases r with
          | zero => simp [advance, depth, QuantumProver.ElegantJointMeasurement.HilbertFiniteNormalChronology.depth]
          | succ r =>
              simp only [advance]
              split_ifs with hr
              · simpa [depth, QuantumProver.ElegantJointMeasurement.HilbertFiniteNormalChronology.depth] using
                  (Finset.le_sup (f := fun j => QuantumProver.ElegantJointMeasurement.HilbertFiniteNormalChronology.depth (next j))
                    (Finset.mem_univ (⟨r, hr⟩)))
              · simp [depth, QuantumProver.ElegantJointMeasurement.HilbertFiniteNormalChronology.depth]
      | bob K hK next =>
          cases r with
          | zero => simp [advance, depth, QuantumProver.ElegantJointMeasurement.HilbertFiniteNormalChronology.depth]
          | succ r =>
              simp only [advance]
              split_ifs with hr
              · simpa [depth, QuantumProver.ElegantJointMeasurement.HilbertFiniteNormalChronology.depth] using
                  (Finset.le_sup (f := fun j => QuantumProver.ElegantJointMeasurement.HilbertFiniteNormalChronology.depth (next j))
                    (Finset.mem_univ (⟨r, hr⟩)))
              · simp [depth, QuantumProver.ElegantJointMeasurement.HilbertFiniteNormalChronology.depth]

end State

theorem state_depth_le {c d a b : ℕ} (T : Protocol c d a b) (n : ℕ)
    (h : History ℕ n) : (state T n h).depth ≤ depth T - n := by
  induction n with
  | zero => simp [state, State.depth]
  | succ n ih =>
      let q := (appendHistory n).symm h
      have hs := State.depth_advance (state T n q.1) q.2
      have hi := Nat.sub_le_sub_right (ih q.1) 1
      simpa only [state, q, Nat.sub_sub, Nat.add_comm n 1] using hs.trans hi

theorem state_depth_zero {c d a b : ℕ} (T : Protocol c d a b) (n : ℕ)
    (hn : depth T ≤ n) (h : History ℕ n) : (state T n h).depth = 0 := by
  have hs := state_depth_le T n h
  rw [Nat.sub_eq_zero_of_le hn] at hs
  exact Nat.eq_zero_of_le_zero hs

section JointEvents

open QuantumProver.ElegantJointMeasurement.HilbertChoi QuantumProver.ElegantJointMeasurement.HilbertPendingTensor QuantumProver.ElegantJointMeasurement.HilbertFiniteKrausPredual
open QuantumProver.MatrixNuclearTensor QuantumProver.HilbertNuclearCompression
open QuantumProver.MatrixNormalTensorInstrument QuantumProver.MatrixNormalRightTensor

abbrev JointMatrix (a b : ℕ) := Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ
abbrev JointNuclear := Nuclear (Joint CommonHilbert CommonHilbert)

def codedJoint (a b : ℕ) : JointMatrix a b →L[ℂ] JointNuclear :=
  jointOperation (fun _ : Unit => (finiteCode a).toContinuousLinearMap)
    (fun _ : Unit => (finiteCode b).toContinuousLinearMap)

theorem codedJoint_product {a b : ℕ}
    (X : Matrix (Fin a) (Fin a) ℂ) (Y : Matrix (Fin b) (Fin b) ℂ) :
    codedJoint a b (X ⊗ₖ Y) = tensorNuclear
      (E := CommonHilbert) (F := CommonHilbert) (E' := CommonHilbert) (F' := CommonHilbert)
      (padNuclear (finiteCode a) (nuclearMatrix X))
      (padNuclear (finiteCode b) (nuclearMatrix Y)) := by
  simpa only [codedJoint, finiteKrausOperation, finiteKrausChannel,
    ContinuousLinearMap.comp_apply, Fintype.sum_unique, nuclearSandwich, padNuclear] using
    jointOperation_product (fun _ : Unit => (finiteCode a).toContinuousLinearMap)
      (fun _ : Unit => (finiteCode b).toContinuousLinearMap) X Y

theorem joint_matrix_clm_ext {a b : ℕ} {Z : Type*}
    [NormedAddCommGroup Z] [NormedSpace ℂ Z]
    (A B : JointMatrix a b →L[ℂ] Z)
    (hAB : ∀ X : Matrix (Fin a) (Fin a) ℂ, ∀ Y : Matrix (Fin b) (Fin b) ℂ,
      A (X ⊗ₖ Y) = B (X ⊗ₖ Y)) : A = B := by
  apply ContinuousLinearMap.ext
  intro X
  conv_lhs => rw [matrix_decomposition X]
  conv_rhs => rw [matrix_decomposition X]
  simp only [map_sum, map_smul]
  apply Finset.sum_congr rfl
  rintro ⟨i,j⟩ _
  apply Finset.sum_congr rfl
  rintro ⟨k,l⟩ _
  congr 1
  have hu : matrixUnit (i,j) (k,l) = matrixUnit i k ⊗ₖ matrixUnit j l := by
    simp only [matrixUnit, Matrix.single_kronecker_single, one_mul]
  rw [hu, hAB]

def matrixSandwichLinear {a p : Type} [Fintype a] [Fintype p]
    (L : Matrix p a ℂ) : Matrix a a ℂ →ₗ[ℂ] Matrix p p ℂ where
  toFun X := L * X * L.conjTranspose
  map_add' X Y := by simp only [Matrix.mul_add, Matrix.add_mul]
  map_smul' z X := by simp only [Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply]

@[simp] theorem matrixSandwichLinear_clm_apply {a p : Type} [Fintype a] [Fintype p]
    (L : Matrix p a ℂ) (X : Matrix a a ℂ) :
    (matrixSandwichLinear L).toContinuousLinearMap X = L * X * L.conjTranspose := rfl

def aliceMatrixEvent {a p b h z : ℕ}
    (K : Fin h → Fin z → Matrix (Fin p) (Fin a) ℂ) (s : Set ℕ) :
    JointMatrix a b →L[ℂ] JointMatrix p b :=
  ∑ j, if j.val + 1 ∈ s then
    ∑ k, (matrixSandwichLinear (K j k ⊗ₖ (1 : Matrix (Fin b) (Fin b) ℂ))).toContinuousLinearMap
  else 0

def bobMatrixEvent {a b p h z : ℕ}
    (K : Fin h → Fin z → Matrix (Fin p) (Fin b) ℂ) (s : Set ℕ) :
    JointMatrix a b →L[ℂ] JointMatrix a p :=
  ∑ j, if j.val + 1 ∈ s then
    ∑ k, (matrixSandwichLinear ((1 : Matrix (Fin a) (Fin a) ℂ) ⊗ₖ K j k)).toContinuousLinearMap
  else 0

theorem aliceMatrixEvent_apply {a p b h z : ℕ}
    (K : Fin h → Fin z → Matrix (Fin p) (Fin a) ℂ) (s : Set ℕ) (X : JointMatrix a b) :
    aliceMatrixEvent K s X = ∑ j, if j.val+1 ∈ s then
      ∑ k, (K j k ⊗ₖ (1 : Matrix (Fin b) (Fin b) ℂ)) * X *
        (K j k ⊗ₖ (1 : Matrix (Fin b) (Fin b) ℂ)).conjTranspose else 0 := by
  unfold aliceMatrixEvent
  rw [sum_apply]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j.val+1 ∈ s
  · simp only [ite_eq_left hj, sum_apply, matrixSandwichLinear_clm_apply]
  · simp only [ite_eq_right hj, zero_apply]

theorem bobMatrixEvent_apply {a b p h z : ℕ}
    (K : Fin h → Fin z → Matrix (Fin p) (Fin b) ℂ) (s : Set ℕ) (X : JointMatrix a b) :
    bobMatrixEvent K s X = ∑ j, if j.val+1 ∈ s then
      ∑ k, ((1 : Matrix (Fin a) (Fin a) ℂ) ⊗ₖ K j k) * X *
        ((1 : Matrix (Fin a) (Fin a) ℂ) ⊗ₖ K j k).conjTranspose else 0 := by
  unfold bobMatrixEvent
  rw [sum_apply]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j.val+1 ∈ s
  · simp only [ite_eq_left hj, sum_apply, matrixSandwichLinear_clm_apply]
  · simp only [ite_eq_right hj, zero_apply]

theorem aliceMatrixEvent_product {a p b h z : ℕ}
    (K : Fin h → Fin z → Matrix (Fin p) (Fin a) ℂ) (s : Set ℕ)
    (X : Matrix (Fin a) (Fin a) ℂ) (Y : Matrix (Fin b) (Fin b) ℂ) :
    aliceMatrixEvent K s (X ⊗ₖ Y) =
      QuantumProver.WernerEndpoint.MatrixFiniteNormalInstrument.matrixEvent K {j | j.val+1 ∈ s} X ⊗ₖ Y := by
  rw [aliceMatrixEvent_apply]
  simp only [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
    ← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one]
  ext ⟨i,j⟩ ⟨k,l⟩
  simp only [QuantumProver.WernerEndpoint.MatrixFiniteNormalInstrument.matrixEvent,
    Matrix.kronecker_apply, Matrix.sum_apply, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j.val+1 ∈ s
  · simp [hj, Matrix.sum_apply, Finset.sum_mul]
  · simp [hj]

theorem bobMatrixEvent_product {a b p h z : ℕ}
    (K : Fin h → Fin z → Matrix (Fin p) (Fin b) ℂ) (s : Set ℕ)
    (X : Matrix (Fin a) (Fin a) ℂ) (Y : Matrix (Fin b) (Fin b) ℂ) :
    bobMatrixEvent K s (X ⊗ₖ Y) = X ⊗ₖ
      QuantumProver.WernerEndpoint.MatrixFiniteNormalInstrument.matrixEvent K {j | j.val+1 ∈ s} Y := by
  rw [bobMatrixEvent_apply]
  simp only [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
    ← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one]
  ext ⟨i,j⟩ ⟨k,l⟩
  simp only [QuantumProver.WernerEndpoint.MatrixFiniteNormalInstrument.matrixEvent,
    Matrix.kronecker_apply, Matrix.sum_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j.val+1 ∈ s
  · simp [hj, Matrix.sum_apply, Finset.mul_sum]
  · simp [hj]

theorem finiteNode_left_joint {a p b h z : ℕ}
    (K : Fin h → Fin z → Matrix (Fin p) (Fin a) ℂ)
    (hK : ∑ j, ∑ k, (K j k).conjTranspose * K j k = 1)
    (s : Set ℕ) (hs : MeasurableSet s) (X : JointMatrix a b) :
    tensorOperation (G := CommonHilbert) (finiteNode K hK) () s (codedJoint a b X) =
      codedJoint p b (aliceMatrixEvent K s X) := by
  have he := joint_matrix_clm_ext
    ((tensorOperation (G := CommonHilbert) (finiteNode K hK) () s).comp (codedJoint a b))
    ((codedJoint p b).comp (aliceMatrixEvent K s)) (by
      intro U V
      simp only [ContinuousLinearMap.comp_apply, codedJoint_product,
        tensorOperation_tensor _ _ _ hs, finiteNode_all_events, aliceMatrixEvent_product])
  exact congrArg (fun A : JointMatrix a b →L[ℂ] JointNuclear => A X) he

theorem finiteNode_right_joint {a b p h z : ℕ}
    (K : Fin h → Fin z → Matrix (Fin p) (Fin b) ℂ)
    (hK : ∑ j, ∑ k, (K j k).conjTranspose * K j k = 1)
    (s : Set ℕ) (hs : MeasurableSet s) (X : JointMatrix a b) :
    rightTensorOperation (G := CommonHilbert) (finiteNode K hK) () s (codedJoint a b X) =
      codedJoint a p (bobMatrixEvent K s X) := by
  have he := joint_matrix_clm_ext
    ((rightTensorOperation (G := CommonHilbert) (finiteNode K hK) () s).comp (codedJoint a b))
    ((codedJoint a p).comp (bobMatrixEvent K s)) (by
      intro U V
      simp only [ContinuousLinearMap.comp_apply, codedJoint_product,
        rightTensorOperation_tensor _ _ _ hs, finiteNode_all_events, bobMatrixEvent_product])
  exact congrArg (fun A : JointMatrix a b →L[ℂ] JointNuclear => A X) he

theorem aliceMatrixEvent_zero {a p b h z : ℕ}
    (K : Fin h → Fin z → Matrix (Fin p) (Fin a) ℂ) :
    aliceMatrixEvent (b := b) K {0} = 0 := by
  simp [aliceMatrixEvent]

theorem bobMatrixEvent_zero {a b p h z : ℕ}
    (K : Fin h → Fin z → Matrix (Fin p) (Fin b) ℂ) :
    bobMatrixEvent (a := a) K {0} = 0 := by
  simp [bobMatrixEvent]

theorem aliceMatrixEvent_outside {a p b h z : ℕ}
    (K : Fin h → Fin z → Matrix (Fin p) (Fin a) ℂ) (r : ℕ) (hr : h ≤ r) :
    aliceMatrixEvent (b := b) K {r+1} = 0 := by
  have hn (j : Fin h) : j.val ≠ r := by
    intro he
    have hh := j.isLt
    omega
  simp [aliceMatrixEvent, hn]

theorem bobMatrixEvent_outside {a b p h z : ℕ}
    (K : Fin h → Fin z → Matrix (Fin p) (Fin b) ℂ) (r : ℕ) (hr : h ≤ r) :
    bobMatrixEvent (a := a) K {r+1} = 0 := by
  have hn (j : Fin h) : j.val ≠ r := by
    intro he
    have hh := j.isLt
    omega
  simp [bobMatrixEvent, hn]

theorem tensor_dummy_record {a b : ℕ} (r : ℕ) (X : JointMatrix a b) :
    tensorOperation (G := CommonHilbert)
      (QuantumProver.ElegantJointMeasurement.HilbertRecordCoding.dummyInstrument (F := CommonHilbert) (H := Unit) 0)
        () {r} (codedJoint a b X) = if r = 0 then codedJoint a b X else 0 := by
  let P : Instrument CommonHilbert CommonHilbert Unit ℕ :=
    QuantumProver.ElegantJointMeasurement.HilbertRecordCoding.dummyInstrument 0
  have he : (tensorOperation (G := CommonHilbert) P () {r}).comp (codedJoint a b) =
      if r = 0 then codedJoint a b else 0 := by
    apply joint_matrix_clm_ext
    intro U V
    simp only [ContinuousLinearMap.comp_apply, codedJoint_product]
    rw [tensorOperation_tensor (E := CommonHilbert) (F := CommonHilbert) (G := CommonHilbert)
      P () {r} (measurableSet_singleton r)
      (padNuclear (finiteCode a) (nuclearMatrix U))
      (padNuclear (finiteCode b) (nuclearMatrix V))]
    by_cases hr : r = 0
    · subst r
      simp [P, QuantumProver.ElegantJointMeasurement.HilbertRecordCoding.dummyInstrument, codedJoint_product]
    · simp [P, QuantumProver.ElegantJointMeasurement.HilbertRecordCoding.dummyInstrument, hr, Ne.symm hr]
  have h := congrArg (fun A : JointMatrix a b →L[ℂ] JointNuclear => A X) he
  by_cases hr : r = 0 <;> simpa [hr, P] using h

def State.jointStep {c d : ℕ} (s : State c d) (r : ℕ) :
    JointNuclear →L[ℂ] JointNuclear :=
  if s.aliceTurn then tensorOperation (G := CommonHilbert) s.aliceNode () {r}
  else rightTensorOperation (G := CommonHilbert) s.bobNode () {r}

def rawStep {c d a b : ℕ} (T : Protocol c d a b) (n : ℕ) (h : History ℕ n) (r : ℕ) :
    JointNuclear →L[ℂ] JointNuclear :=
  if (ofProtocol T).aliceTurn n h then
    tensorOperation (G := CommonHilbert) ((ofProtocol T).alice n) h {r}
  else rightTensorOperation (G := CommonHilbert) ((ofProtocol T).bob n) h {r}

theorem rawStep_eq_state {c d a b : ℕ} (T : Protocol c d a b) (n : ℕ)
    (h : History ℕ n) (r : ℕ) : rawStep T n h r = (state T n h).jointStep r := by
  unfold rawStep State.jointStep
  change (if (state T n h).aliceTurn then _ else _) = _
  split_ifs with ht
  · rfl
  · rfl

def rawPrefix {c d a b : ℕ} (T : Protocol c d a b) :
    (n : ℕ) → History ℕ n → JointNuclear →L[ℂ] JointNuclear
  | 0, _ => ContinuousLinearMap.id ℂ JointNuclear
  | n+1, h =>
      let q := (appendHistory n).symm h
      (rawStep T n q.1 q.2).comp (rawPrefix T n q.1)

inductive MatrixState (c d : ℕ) where
  | invalid : MatrixState c d
  | active {a b : ℕ} (T : Protocol c d a b) (X : JointMatrix a b) : MatrixState c d

namespace MatrixState

variable {c d : ℕ}

def toState : MatrixState c d → State c d
  | .invalid => .invalid
  | .active T _ => .active T

def eval : MatrixState c d → JointNuclear
  | .invalid => 0
  | @MatrixState.active _ _ a b _ X => codedJoint a b X

def advance : MatrixState c d → ℕ → MatrixState c d
  | .invalid, _ => .invalid
  | s@(.active (.terminal _ _ _ _) _), 0 => s
  | .active (.terminal _ _ _ _) _, _+1 => .invalid
  | .active (.alice _ _ _) _, 0 => .invalid
  | @MatrixState.active _ _ _ _
      (@QuantumProver.WernerEndpoint.OperationalEndpointCost.FiniteLocalProtocol.alice _ _ _ _ _ h _ K _ next) X,
      r+1 => if hr : r < h then .active (next ⟨r,hr⟩) (aliceMatrixEvent K {r+1} X) else .invalid
  | .active (.bob _ _ _) _, 0 => .invalid
  | @MatrixState.active _ _ _ _
      (@QuantumProver.WernerEndpoint.OperationalEndpointCost.FiniteLocalProtocol.bob _ _ _ _ _ h _ K _ next) X,
      r+1 => if hr : r < h then .active (next ⟨r,hr⟩) (bobMatrixEvent K {r+1} X) else .invalid

theorem toState_advance (s : MatrixState c d) (r : ℕ) :
    (advance s r).toState = s.toState.advance r := by
  cases s with
  | invalid => rfl
  | @active a b T X =>
      cases T <;> cases r <;> simp [advance, toState, State.advance]
      all_goals split_ifs <;> rfl

theorem eval_advance (s : MatrixState c d) (r : ℕ) :
    (advance s r).eval = s.toState.jointStep r s.eval := by
  cases s with
  | invalid => simp [advance, toState, eval]
  | @active a b T X =>
      cases T with
      | terminal LA LB hLA hLB =>
          cases r <;> simp [advance, toState, eval, State.jointStep, State.aliceTurn,
            State.aliceNode, tensor_dummy_record]
      | @alice _a _b p h z K hK next =>
          cases r with
          | zero =>
              simpa [advance, toState, eval, State.jointStep, State.aliceTurn,
                State.aliceNode, aliceMatrixEvent_zero] using
                (finiteNode_left_joint (b := b) K hK {0} (measurableSet_singleton 0) X).symm
          | succ r =>
              by_cases hr : r < h
              · simpa [advance, hr, toState, eval, State.jointStep, State.aliceTurn,
                  State.aliceNode] using
                  (finiteNode_left_joint (b := b) K hK {r+1} (measurableSet_singleton (r+1)) X).symm
              · simpa [advance, hr, toState, eval, State.jointStep, State.aliceTurn,
                  State.aliceNode, aliceMatrixEvent_outside K r (Nat.le_of_not_gt hr)] using
                  (finiteNode_left_joint (b := b) K hK {r+1} (measurableSet_singleton (r+1)) X).symm
      | @bob _a _b p h z K hK next =>
          cases r with
          | zero =>
              simpa [advance, toState, eval, State.jointStep, State.aliceTurn,
                State.bobNode, bobMatrixEvent_zero] using
                (finiteNode_right_joint (a := a) K hK {0} (measurableSet_singleton 0) X).symm
          | succ r =>
              by_cases hr : r < h
              · simpa [advance, hr, toState, eval, State.jointStep, State.aliceTurn,
                  State.bobNode] using
                  (finiteNode_right_joint (a := a) K hK {r+1} (measurableSet_singleton (r+1)) X).symm
              · simpa [advance, hr, toState, eval, State.jointStep, State.aliceTurn,
                  State.bobNode, bobMatrixEvent_outside K r (Nat.le_of_not_gt hr)] using
                  (finiteNode_right_joint (a := a) K hK {r+1} (measurableSet_singleton (r+1)) X).symm

end MatrixState

def matrixState {c d a b : ℕ} (T : Protocol c d a b) (X : JointMatrix a b) :
    (n : ℕ) → History ℕ n → MatrixState c d
  | 0, _ => .active T X
  | n+1, h =>
      let q := (appendHistory n).symm h
      MatrixState.advance (matrixState T X n q.1) q.2

theorem matrixState_toState {c d a b : ℕ} (T : Protocol c d a b) (X : JointMatrix a b)
    (n : ℕ) (h : History ℕ n) : (matrixState T X n h).toState = state T n h := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [matrixState, state, MatrixState.toState_advance, ih]

theorem rawPrefix_eq_matrixState {c d a b : ℕ} (T : Protocol c d a b)
    (X : JointMatrix a b) (n : ℕ) (h : History ℕ n) :
    rawPrefix T n h (codedJoint a b X) = (matrixState T X n h).eval := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [rawPrefix, ContinuousLinearMap.comp_apply, matrixState,
        MatrixState.eval_advance, ih, matrixState_toState, rawStep_eq_state]

open QuantumProver.WernerEndpoint.MatrixFiniteNormalTerminal

def State.terminalAlice {c d : ℕ} (hc : 0 < c) :
    State c d → Instrument CommonHilbert (EuclideanSpace ℂ (Fin c)) Unit Unit
  | .active (.terminal LA _ hLA _) => terminalInstrument hc (finiteCode _) LA hLA
  | _ => terminalInstrument hc (finiteCode c) 1 (by simp)

def State.terminalBob {c d : ℕ} (hd : 0 < d) :
    State c d → Instrument CommonHilbert (EuclideanSpace ℂ (Fin d)) Unit Unit
  | .active (.terminal _ LB _ hLB) => terminalInstrument hd (finiteCode _) LB hLB
  | _ => terminalInstrument hd (finiteCode d) 1 (by simp)

def historySingletonInstrument {E H : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [MeasurableSpace H] [Countable H] [MeasurableSingletonClass H]
    (Q : H → Instrument CommonHilbert E Unit Unit) : Instrument CommonHilbert E H Unit where
  operation h := (Q h).operation ()
  empty h := (Q h).empty ()
  countable_additivity h := (Q h).countable_additivity ()
  completelyPositive h := (Q h).completelyPositive ()
  measurable_coordinate _s _hs _U _x _y := measurable_of_countable _
  trace_preserving h := (Q h).trace_preserving ()

def terminalAlice {c d a b : ℕ} (T : Protocol c d a b) (n : ℕ) (hc : 0 < c) :
    Instrument CommonHilbert (EuclideanSpace ℂ (Fin c)) (History ℕ n) PUnit.{1} :=
  QuantumProver.ElegantJointMeasurement.HilbertRecordCoding.pushforwardInstrument
    (historySingletonInstrument (fun h => (state T n h).terminalAlice hc))
    (fun _ : Unit => (PUnit.unit : PUnit.{1})) measurable_const

def terminalBob {c d a b : ℕ} (T : Protocol c d a b) (n : ℕ) (hd : 0 < d) :
    Instrument CommonHilbert (EuclideanSpace ℂ (Fin d)) (History ℕ n) PUnit.{1} :=
  QuantumProver.ElegantJointMeasurement.HilbertRecordCoding.pushforwardInstrument
    (historySingletonInstrument (fun h => (state T n h).terminalBob hd))
    (fun _ : Unit => (PUnit.unit : PUnit.{1})) measurable_const

abbrev FiniteJointNuclear (c d : ℕ) :=
  Nuclear (Joint (EuclideanSpace ℂ (Fin c)) (EuclideanSpace ℂ (Fin d)))

def physicalJoint (c d : ℕ) : JointMatrix c d →L[ℂ] FiniteJointNuclear c d :=
  jointOperation (fun _ : Unit => ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin c)))
    (fun _ : Unit => ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin d)))

theorem physicalJoint_product {c d : ℕ}
    (X : Matrix (Fin c) (Fin c) ℂ) (Y : Matrix (Fin d) (Fin d) ℂ) :
    physicalJoint c d (X ⊗ₖ Y) =
      tensorNuclear (E := EuclideanSpace ℂ (Fin c)) (F := EuclideanSpace ℂ (Fin d))
        (E' := EuclideanSpace ℂ (Fin c)) (F' := EuclideanSpace ℂ (Fin d))
        (nuclearMatrix X) (nuclearMatrix Y) := by
  have he := jointOperation_product
    (fun _ : Unit => ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin c)))
    (fun _ : Unit => ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin d))) X Y
  simpa [physicalJoint, finiteKrausOperation, finiteKrausChannel, nuclearSandwich,
    ContinuousLinearMap.adjoint_id, QuantumProver.MatrixNormalTensorExtension.compose_id_id_apply] using he

def State.terminalPair {c d : ℕ} (hc : 0 < c) (hd : 0 < d) (s : State c d) :
    JointNuclear →L[ℂ] FiniteJointNuclear c d :=
  (rightTensorOperation (G := EuclideanSpace ℂ (Fin c)) (s.terminalBob hd) () univ).comp
    (tensorOperation (G := CommonHilbert) (s.terminalAlice hc) () univ)

theorem terminalPair_on_terminal {c d a b : ℕ} (hc : 0 < c) (hd : 0 < d)
    (LA : Matrix (Fin c) (Fin a) ℂ) (LB : Matrix (Fin d) (Fin b) ℂ)
    (hLA : LA.conjTranspose * LA = 1) (hLB : LB.conjTranspose * LB = 1)
    (X : JointMatrix a b) :
    (State.active (.terminal LA LB hLA hLB)).terminalPair hc hd (codedJoint a b X) =
      physicalJoint c d ((LA ⊗ₖ LB) * X * (LA ⊗ₖ LB).conjTranspose) := by
  let A : JointMatrix a b →L[ℂ] FiniteJointNuclear c d :=
    ((State.active (.terminal LA LB hLA hLB)).terminalPair hc hd).comp (codedJoint a b)
  let B : JointMatrix a b →L[ℂ] FiniteJointNuclear c d :=
    (physicalJoint c d).comp (matrixSandwichLinear (LA ⊗ₖ LB)).toContinuousLinearMap
  have hp (U : Matrix (Fin a) (Fin a) ℂ) (V : Matrix (Fin b) (Fin b) ℂ) :
      A (U ⊗ₖ V) = B (U ⊗ₖ V) := by
    change rightTensorOperation (G := EuclideanSpace ℂ (Fin c))
      (terminalInstrument hd (finiteCode b) LB hLB) () univ
      (tensorOperation (G := CommonHilbert) (terminalInstrument hc (finiteCode a) LA hLA)
        () univ (codedJoint a b (U ⊗ₖ V))) =
        physicalJoint c d ((LA ⊗ₖ LB) * (U ⊗ₖ V) * (LA ⊗ₖ LB).conjTranspose)
    rw [codedJoint_product,
      tensorOperation_tensor (G := CommonHilbert)
        (terminalInstrument hc (finiteCode a) LA hLA) () univ MeasurableSet.univ
        (padNuclear (finiteCode a) (nuclearMatrix U)) (padNuclear (finiteCode b) (nuclearMatrix V)),
      rightTensorOperation_tensor (G := EuclideanSpace ℂ (Fin c))
        (terminalInstrument hd (finiteCode b) LB hLB) () univ MeasurableSet.univ
        ((terminalInstrument hc (finiteCode a) LA hLA).operation () univ
          (padNuclear (finiteCode a) (nuclearMatrix U)))
        (padNuclear (finiteCode b) (nuclearMatrix V))]
    calc
      _ = tensorNuclear
          (E := EuclideanSpace ℂ (Fin c)) (F := EuclideanSpace ℂ (Fin d))
          (E' := EuclideanSpace ℂ (Fin c)) (F' := EuclideanSpace ℂ (Fin d))
          (nuclearMatrix (LA * U * LA.conjTranspose))
          (nuclearMatrix (LB * V * LB.conjTranspose)) :=
        congrArg₂ (fun (M : Nuclear (EuclideanSpace ℂ (Fin c)))
          (N : Nuclear (EuclideanSpace ℂ (Fin d))) =>
          tensorNuclear (E := EuclideanSpace ℂ (Fin c)) (F := EuclideanSpace ℂ (Fin d))
            (E' := EuclideanSpace ℂ (Fin c)) (F' := EuclideanSpace ℂ (Fin d)) M N)
          (terminalInstrument_univ hc (finiteCode a) LA hLA U)
          (terminalInstrument_univ hd (finiteCode b) LB hLB V)
      _ = _ := by
        have hmat : (LA ⊗ₖ LB) * (U ⊗ₖ V) * (LA ⊗ₖ LB).conjTranspose =
            (LA * U * LA.conjTranspose) ⊗ₖ (LB * V * LB.conjTranspose) := by
          rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
            ← Matrix.mul_kronecker_mul]
        rw [hmat]
        exact (physicalJoint_product (LA * U * LA.conjTranspose) (LB * V * LB.conjTranspose)).symm
  have he : A = B := joint_matrix_clm_ext A B hp
  exact congrArg (fun A : JointMatrix a b →L[ℂ] FiniteJointNuclear c d => A X) he

theorem aliceMatrixEvent_visible {a p b h z : ℕ}
    (K : Fin h → Fin z → Matrix (Fin p) (Fin a) ℂ) (j : Fin h) (X : JointMatrix a b) :
    aliceMatrixEvent K {j.val+1} X =
      ∑ k, (K j k ⊗ₖ (1 : Matrix (Fin b) (Fin b) ℂ)) * X *
        (K j k ⊗ₖ (1 : Matrix (Fin b) (Fin b) ℂ)).conjTranspose := by
  rw [aliceMatrixEvent_apply]
  simp [Fin.val_inj]

theorem bobMatrixEvent_visible {a b p h z : ℕ}
    (K : Fin h → Fin z → Matrix (Fin p) (Fin b) ℂ) (j : Fin h) (X : JointMatrix a b) :
    bobMatrixEvent K {j.val+1} X =
      ∑ k, ((1 : Matrix (Fin a) (Fin a) ℂ) ⊗ₖ K j k) * X *
        ((1 : Matrix (Fin a) (Fin a) ℂ) ⊗ₖ K j k).conjTranspose := by
  rw [bobMatrixEvent_apply]
  simp [Fin.val_inj]

def State.records {c d : ℕ} : State c d → Finset ℕ
  | .invalid => {0}
  | .active (.terminal _ _ _ _) => {0}
  | @State.active _ _ _ _
      (@QuantumProver.WernerEndpoint.OperationalEndpointCost.FiniteLocalProtocol.alice _ _ _ _ _ h _ _ _ _) =>
      insert 0 (Finset.univ.image (fun j : Fin h => j.val+1))
  | @State.active _ _ _ _
      (@QuantumProver.WernerEndpoint.OperationalEndpointCost.FiniteLocalProtocol.bob _ _ _ _ _ h _ _ _ _) =>
      insert 0 (Finset.univ.image (fun j : Fin h => j.val+1))

namespace MatrixState

def result {c d : ℕ} : MatrixState c d → JointMatrix c d
  | .invalid => 0
  | .active T X => T.apply X

theorem result_sum_advance {c d : ℕ} (s : MatrixState c d) :
    ∑ r ∈ s.toState.records, (s.advance r).result = s.result := by
  cases s with
  | invalid => simp [toState, State.records, advance, result]
  | @active a b T X =>
      cases T with
      | terminal LA LB hLA hLB => simp [toState, State.records, advance, result]
      | @alice _a _b p h z K hK next =>
          have hz : 0 ∉ Finset.univ.image (fun j : Fin h => j.val+1) := by simp
          change (∑ r ∈ insert 0 (Finset.univ.image (fun j : Fin h => j.val+1)),
            (MatrixState.active (.alice K hK next) X |>.advance r).result) = _
          rw [Finset.sum_insert hz, Finset.sum_image]
          · simp [advance, result, aliceMatrixEvent_visible,
              QuantumProver.WernerEndpoint.OperationalEndpointCost.FiniteLocalProtocol.apply]
          · intro j _ k _ he
            exact Fin.ext (Nat.add_right_cancel he)
      | @bob _a _b p h z K hK next =>
          have hz : 0 ∉ Finset.univ.image (fun j : Fin h => j.val+1) := by simp
          change (∑ r ∈ insert 0 (Finset.univ.image (fun j : Fin h => j.val+1)),
            (MatrixState.active (.bob K hK next) X |>.advance r).result) = _
          rw [Finset.sum_insert hz, Finset.sum_image]
          · simp [advance, result, bobMatrixEvent_visible,
              QuantumProver.WernerEndpoint.OperationalEndpointCost.FiniteLocalProtocol.apply]
          · intro j _ k _ he
            exact Fin.ext (Nat.add_right_cancel he)

theorem advance_invalid_of_not_mem_records {c d : ℕ} (s : MatrixState c d) (r : ℕ)
    (hr : r ∉ s.toState.records) : s.advance r = .invalid := by
  cases s with
  | invalid => rfl
  | @active a b T X =>
      cases T with
      | terminal LA LB hLA hLB =>
          cases r with
          | zero => simp [toState, State.records] at hr
          | succ r => rfl
      | @alice _a _b p h z K hK next =>
          cases r with
          | zero => rfl
          | succ r =>
              have hn : ¬ r < h := by
                intro hh
                apply hr
                exact Finset.mem_insert_of_mem (Finset.mem_image.mpr
                  ⟨⟨r,hh⟩, Finset.mem_univ _, rfl⟩)
              simp [advance, hn]
      | @bob _a _b p h z K hK next =>
          cases r with
          | zero => rfl
          | succ r =>
              have hn : ¬ r < h := by
                intro hh
                apply hr
                exact Finset.mem_insert_of_mem (Finset.mem_image.mpr
                  ⟨⟨r,hh⟩, Finset.mem_univ _, rfl⟩)
              simp [advance, hn]

theorem terminalPair_eval_of_depth_zero {c d : ℕ} (hc : 0 < c) (hd : 0 < d)
    (s : MatrixState c d) (hs : s.toState.depth = 0) :
    s.toState.terminalPair hc hd s.eval = physicalJoint c d s.result := by
  cases s with
  | invalid => simp [toState, eval, result]
  | active T X =>
      cases T with
      | terminal LA LB hLA hLB => exact terminalPair_on_terminal hc hd LA LB hLA hLB X
      | alice K hK next => simp [toState, State.depth, depth] at hs
      | bob K hK next => simp [toState, State.depth, depth] at hs

end MatrixState

theorem matrixState_append {c d a b : ℕ} (T : Protocol c d a b) (X : JointMatrix a b)
    (n : ℕ) (h : History ℕ n) (r : ℕ) :
    matrixState T X (n+1) (appendHistory n (h,r)) = (matrixState T X n h).advance r := by
  simp only [matrixState, MeasurableEquiv.symm_apply_apply]

def frontier {c d a b : ℕ} (T : Protocol c d a b) : (n : ℕ) → Finset (History ℕ n)
  | 0 => {PUnit.unit}
  | n+1 => (frontier T n).biUnion (fun h =>
      ((state T n h).records).image (fun r => appendHistory n (h,r)))

theorem mem_frontier_append {c d a b : ℕ} (T : Protocol c d a b) (n : ℕ)
    (h : History ℕ n) (r : ℕ) :
    appendHistory n (h,r) ∈ frontier T (n+1) ↔
      h ∈ frontier T n ∧ r ∈ (state T n h).records := by
  simp only [frontier, Finset.mem_biUnion, Finset.mem_image]
  constructor
  · rintro ⟨u, hu, v, hv, he⟩
    have hp := (appendHistory n).injective he
    have hu' := congrArg Prod.fst hp
    have hv' := congrArg Prod.snd hp
    change u = h at hu'
    change v = r at hv'
    subst u
    subst v
    exact ⟨hu,hv⟩
  · rintro ⟨hh,hr⟩
    exact ⟨h,hh,r,hr,rfl⟩

theorem sum_frontier_succ {c d a b : ℕ} {Z : Type*} [AddCommMonoid Z]
    (T : Protocol c d a b) (n : ℕ) (f : History ℕ (n+1) → Z) :
    ∑ h ∈ frontier T (n+1), f h =
      ∑ h ∈ frontier T n, ∑ r ∈ (state T n h).records, f (appendHistory n (h,r)) := by
  rw [frontier, Finset.sum_biUnion]
  · apply Finset.sum_congr rfl
    intro h hh
    exact Finset.sum_image (fun r _ s _ he => congrArg Prod.snd ((appendHistory n).injective he))
  · intro h hh k hk hne
    apply Finset.disjoint_left.mpr
    intro z hz hzk
    obtain ⟨r,hr,he⟩ := Finset.mem_image.mp hz
    obtain ⟨s,hs,he'⟩ := Finset.mem_image.mp hzk
    exact hne (congrArg Prod.fst ((appendHistory n).injective (he.trans he'.symm)))

theorem sum_frontier_result {c d a b : ℕ} (T : Protocol c d a b) (X : JointMatrix a b)
    (n : ℕ) : ∑ h ∈ frontier T n, (matrixState T X n h).result = T.apply X := by
  induction n with
  | zero => simp [frontier, matrixState, MatrixState.result]
  | succ n ih =>
      rw [sum_frontier_succ]
      have he : (∑ h ∈ frontier T n, ∑ r ∈ (state T n h).records,
          (matrixState T X (n+1) (appendHistory n (h,r))).result) =
          ∑ h ∈ frontier T n, (matrixState T X n h).result := by
        apply Finset.sum_congr rfl
        intro h hh
        simp_rw [matrixState_append T X n h]
        rw [← matrixState_toState T X n h]
        exact MatrixState.result_sum_advance _
      exact he.trans ih

theorem rawPrefix_zero_of_not_mem_frontier {c d a b : ℕ} (T : Protocol c d a b)
    (X : JointMatrix a b) (n : ℕ) (h : History ℕ n) (hh : h ∉ frontier T n) :
    rawPrefix T n h (codedJoint a b X) = 0 := by
  induction n with
  | zero => exact False.elim (hh (by simp [frontier]))
  | succ n ih =>
      let q := (appendHistory n).symm h
      have he : appendHistory n (q.1,q.2) = h := (appendHistory n).apply_symm_apply h
      by_cases hq : q.1 ∈ frontier T n
      · have hr : q.2 ∉ (state T n q.1).records := by
          intro hr
          exact hh (he ▸ (mem_frontier_append T n q.1 q.2).mpr ⟨hq,hr⟩)
        rw [rawPrefix_eq_matrixState]
        simp only [matrixState]
        rw [MatrixState.advance_invalid_of_not_mem_records _ _ (by
          simpa only [matrixState_toState] using hr)]
        rfl
      · change rawStep T n q.1 q.2 (rawPrefix T n q.1 (codedJoint a b X)) = 0
        rw [ih q.1 hq, map_zero]

def terminalOutput {c d a b : ℕ} (T : Protocol c d a b) (n : ℕ)
    (hc : 0 < c) (hd : 0 < d) (h : History ℕ n) :
    JointNuclear →L[ℂ] FiniteJointNuclear c d :=
  (rightTensorOperation (G := EuclideanSpace ℂ (Fin c)) (terminalBob T n hd) h univ).comp
    (tensorOperation (G := CommonHilbert) (terminalAlice T n hc) h univ)

theorem terminalOutput_eq_state {c d a b : ℕ} (T : Protocol c d a b) (n : ℕ)
    (hc : 0 < c) (hd : 0 < d) (h : History ℕ n) :
    terminalOutput T n hc hd h = (state T n h).terminalPair hc hd := rfl

theorem sum_terminal_rawPrefix_eq_apply {c d a b : ℕ} (T : Protocol c d a b)
    (hc : 0 < c) (hd : 0 < d) (n : ℕ) (hn : depth T ≤ n) (X : JointMatrix a b) :
    ∑ h ∈ frontier T n, terminalOutput T n hc hd h (rawPrefix T n h (codedJoint a b X)) =
      physicalJoint c d (T.apply X) := by
  calc
    _ = ∑ h ∈ frontier T n, physicalJoint c d ((matrixState T X n h).result) := by
      apply Finset.sum_congr rfl
      intro h hh
      rw [terminalOutput_eq_state, rawPrefix_eq_matrixState, ← matrixState_toState T X n h]
      exact MatrixState.terminalPair_eval_of_depth_zero hc hd _ (by
        simpa only [matrixState_toState] using state_depth_zero T n hn h)
    _ = physicalJoint c d (∑ h ∈ frontier T n, (matrixState T X n h).result) := by rw [map_sum]
    _ = _ := by rw [sum_frontier_result]

theorem hasSum_terminal_rawPrefix_eq_apply {c d a b : ℕ} (T : Protocol c d a b)
    (hc : 0 < c) (hd : 0 < d) (n : ℕ) (hn : depth T ≤ n) (X : JointMatrix a b) :
    HasSum (fun h : History ℕ n => terminalOutput T n hc hd h
      (rawPrefix T n h (codedJoint a b X))) (physicalJoint c d (T.apply X)) := by
  have hz (h : History ℕ n) (hh : h ∉ frontier T n) :
      terminalOutput T n hc hd h (rawPrefix T n h (codedJoint a b X)) = 0 := by
    rw [rawPrefix_zero_of_not_mem_frontier T X n h hh, map_zero]
  have hs : HasSum (fun h : History ℕ n => terminalOutput T n hc hd h
      (rawPrefix T n h (codedJoint a b X)))
      (∑ h ∈ frontier T n, terminalOutput T n hc hd h (rawPrefix T n h (codedJoint a b X))) :=
    hasSum_sum_of_ne_finset_zero (s := frontier T n) hz
  rw [sum_terminal_rawPrefix_eq_apply T hc hd n hn X] at hs
  exact hs

end JointEvents

end QuantumProver.ElegantJointMeasurement.HilbertFiniteNormalChronology

import Mathlib
import QuantumProver.InformationTheory.ElegantJointMeasurement.IConcurrence
import QuantumProver.InformationTheory.ElegantJointMeasurement.ContinuousInstrumentQuadrature
import QuantumProver.InformationTheory.ElegantJointMeasurement.InstrumentNormalization

namespace QuantumProver.ElegantJointMeasurement.HilbertContinuousProtocol

open MeasureTheory Set Filter
open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder Matrix Kronecker
  Matrix.Norms.L2Operator Topology

noncomputable section

set_option maxHeartbeats 800000

universe u

abbrev LocalMatrix (a : ℕ) := Matrix (Fin a) (Fin a) ℂ
abbrev JointMatrix (a b : ℕ) := Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ

inductive Tree (a b : ℕ) : ℕ → Type (u + 1) where
  | leaf (height : ℕ) (report : Fin 4) : Tree a b height
  | alice {height : ℕ} (Ω : Type u) (mΩ : MeasurableSpace Ω)
      (μ : @Measure Ω mΩ) (K : Ω → LocalMatrix a)
      (child : Ω → Tree a b height) : Tree a b (height + 1)
  | bob {height : ℕ} (Ω : Type u) (mΩ : MeasurableSpace Ω)
      (μ : @Measure Ω mΩ) (K : Ω → LocalMatrix b)
      (child : Ω → Tree a b height) : Tree a b (height + 1)

def aliceSandwich {a b : ℕ} (K : LocalMatrix a) (E : JointMatrix a b) :
    JointMatrix a b :=
  (K ⊗ₖ (1 : LocalMatrix b))ᴴ * E * (K ⊗ₖ (1 : LocalMatrix b))

def bobSandwich {a b : ℕ} (K : LocalMatrix b) (E : JointMatrix a b) :
    JointMatrix a b :=
  ((1 : LocalMatrix a) ⊗ₖ K)ᴴ * E * ((1 : LocalMatrix a) ⊗ₖ K)

def reportedEffect {a b : ℕ} : {height : ℕ} → Tree.{u} a b height →
    Fin 4 → JointMatrix a b
  | _, .leaf _ report => fun j => if report = j then 1 else 0
  | _, .alice _Ω mΩ μ K child =>
      letI := mΩ
      fun j => ∫ ω, aliceSandwich (K ω) (reportedEffect (child ω) j) ∂μ
  | _, .bob _Ω mΩ μ K child =>
      letI := mΩ
      fun j => ∫ ω, bobSandwich (K ω) (reportedEffect (child ω) j) ∂μ

def WellFormed {a b : ℕ} : {height : ℕ} → Tree.{u} a b height → Prop
  | _, .leaf _ _ => True
  | _, .alice _Ω mΩ μ K child =>
      letI := mΩ
      IsFiniteMeasure μ ∧ Measurable K ∧
        Integrable (fun ω => (K ω)ᴴ * K ω) μ ∧
        (∫ ω, (K ω)ᴴ * K ω ∂μ) = 1 ∧
        (∀ ω, WellFormed (child ω)) ∧
        (∀ j, Measurable (fun ω => reportedEffect (child ω) j))
  | _, .bob _Ω mΩ μ K child =>
      letI := mΩ
      IsFiniteMeasure μ ∧ Measurable K ∧
        Integrable (fun ω => (K ω)ᴴ * K ω) μ ∧
        (∫ ω, (K ω)ᴴ * K ω ∂μ) = 1 ∧
        (∀ ω, WellFormed (child ω)) ∧
        (∀ j, Measurable (fun ω => reportedEffect (child ω) j))

@[simp] theorem reportedEffect_leaf (a b height : ℕ) (report j : Fin 4) :
    reportedEffect (Tree.leaf (a := a) (b := b) height report) j =
      if report = j then 1 else 0 := rfl

@[simp] theorem wellFormed_leaf (a b height : ℕ) (report : Fin 4) :
    WellFormed (Tree.leaf (a := a) (b := b) height report) := trivial

theorem sum_reportedEffect_leaf (a b height : ℕ) (report : Fin 4) :
    (∑ j, reportedEffect (Tree.leaf (a := a) (b := b) height report) j) = 1 := by
  simp [reportedEffect]

def leftTensorCLM (a b : ℕ) : LocalMatrix a →L[ℝ] JointMatrix a b :=
  ({ toFun := fun G => G ⊗ₖ (1 : LocalMatrix b)
     map_add' := by
       intro G H
       ext ⟨i, i'⟩ ⟨j, j'⟩
       simp only [Matrix.kronecker_apply, Matrix.add_apply, add_mul]
     map_smul' := by
       intro r G
       ext ⟨i, i'⟩ ⟨j, j'⟩
       simp only [Matrix.kronecker_apply, Matrix.smul_apply, smul_mul_assoc, RingHom.id_apply] } :
      LocalMatrix a →ₗ[ℝ] JointMatrix a b).toContinuousLinearMap

def rightTensorCLM (a b : ℕ) : LocalMatrix b →L[ℝ] JointMatrix a b :=
  ({ toFun := fun G => (1 : LocalMatrix a) ⊗ₖ G
     map_add' := by
       intro G H
       ext ⟨i, i'⟩ ⟨j, j'⟩
       simp only [Matrix.kronecker_apply, Matrix.add_apply, mul_add]
     map_smul' := by
       intro r G
       ext ⟨i, i'⟩ ⟨j, j'⟩
       simp only [Matrix.kronecker_apply, Matrix.smul_apply, mul_smul_comm, RingHom.id_apply] } :
      LocalMatrix b →ₗ[ℝ] JointMatrix a b).toContinuousLinearMap

@[simp] theorem leftTensorCLM_apply (a b : ℕ) (G : LocalMatrix a) :
    leftTensorCLM a b G = G ⊗ₖ (1 : LocalMatrix b) := rfl

@[simp] theorem rightTensorCLM_apply (a b : ℕ) (G : LocalMatrix b) :
    rightTensorCLM a b G = (1 : LocalMatrix a) ⊗ₖ G := rfl

theorem integrable_leftTensor {Ω : Type*} [MeasurableSpace Ω] {a b : ℕ}
    (μ : Measure Ω) (G : Ω → LocalMatrix a) (hG : Integrable G μ) :
    Integrable (fun ω => G ω ⊗ₖ (1 : LocalMatrix b)) μ :=
  (leftTensorCLM a b).integrable_comp hG

theorem integrable_rightTensor {Ω : Type*} [MeasurableSpace Ω] {a b : ℕ}
    (μ : Measure Ω) (G : Ω → LocalMatrix b) (hG : Integrable G μ) :
    Integrable (fun ω => (1 : LocalMatrix a) ⊗ₖ G ω) μ :=
  (rightTensorCLM a b).integrable_comp hG

theorem integral_leftTensor {Ω : Type*} [MeasurableSpace Ω] {a b : ℕ}
    (μ : Measure Ω) (G : Ω → LocalMatrix a) (hG : Integrable G μ) :
    (∫ ω, G ω ⊗ₖ (1 : LocalMatrix b) ∂μ) =
      (∫ ω, G ω ∂μ) ⊗ₖ (1 : LocalMatrix b) :=
  (leftTensorCLM a b).integral_comp_comm hG

theorem integral_rightTensor {Ω : Type*} [MeasurableSpace Ω] {a b : ℕ}
    (μ : Measure Ω) (G : Ω → LocalMatrix b) (hG : Integrable G μ) :
    (∫ ω, (1 : LocalMatrix a) ⊗ₖ G ω ∂μ) =
      (1 : LocalMatrix a) ⊗ₖ (∫ ω, G ω ∂μ) :=
  (rightTensorCLM a b).integral_comp_comm hG

@[simp] theorem aliceSandwich_one {a b : ℕ} (K : LocalMatrix a) :
    aliceSandwich K (1 : JointMatrix a b) =
      (Kᴴ * K) ⊗ₖ (1 : LocalMatrix b) := by
  simp only [aliceSandwich, Matrix.mul_one, Matrix.conjTranspose_kronecker,
    Matrix.conjTranspose_one]
  rw [← Matrix.mul_kronecker_mul, Matrix.one_mul]

@[simp] theorem bobSandwich_one {a b : ℕ} (K : LocalMatrix b) :
    bobSandwich K (1 : JointMatrix a b) =
      (1 : LocalMatrix a) ⊗ₖ (Kᴴ * K) := by
  simp only [bobSandwich, Matrix.mul_one, Matrix.conjTranspose_kronecker,
    Matrix.conjTranspose_one]
  rw [← Matrix.mul_kronecker_mul, Matrix.one_mul]

theorem sum_aliceSandwich {a b : ℕ} (K : LocalMatrix a)
    (E : Fin 4 → JointMatrix a b) :
    (∑ j, aliceSandwich K (E j)) = aliceSandwich K (∑ j, E j) := by
  simp only [aliceSandwich, Matrix.mul_sum, Matrix.sum_mul]

theorem sum_bobSandwich {a b : ℕ} (K : LocalMatrix b)
    (E : Fin 4 → JointMatrix a b) :
    (∑ j, bobSandwich K (E j)) = bobSandwich K (∑ j, E j) := by
  simp only [bobSandwich, Matrix.mul_sum, Matrix.sum_mul]

theorem integral_aliceSandwich_one {Ω : Type*} [MeasurableSpace Ω] {a b : ℕ}
    (μ : Measure Ω) (K : Ω → LocalMatrix a)
    (hG : Integrable (fun ω => (K ω)ᴴ * K ω) μ)
    (hcomplete : (∫ ω, (K ω)ᴴ * K ω ∂μ) = 1) :
    (∫ ω, aliceSandwich (K ω) (1 : JointMatrix a b) ∂μ) = 1 := by
  simp only [aliceSandwich_one]
  rw [integral_leftTensor μ _ hG, hcomplete]
  simp

theorem integral_bobSandwich_one {Ω : Type*} [MeasurableSpace Ω] {a b : ℕ}
    (μ : Measure Ω) (K : Ω → LocalMatrix b)
    (hG : Integrable (fun ω => (K ω)ᴴ * K ω) μ)
    (hcomplete : (∫ ω, (K ω)ᴴ * K ω ∂μ) = 1) :
    (∫ ω, bobSandwich (K ω) (1 : JointMatrix a b) ∂μ) = 1 := by
  simp only [bobSandwich_one]
  rw [integral_rightTensor μ _ hG, hcomplete]
  simp

theorem integrated_alicePOVM {Ω : Type*} [MeasurableSpace Ω] {a b : ℕ}
    (μ : Measure Ω) (K : Ω → LocalMatrix a) (E : Ω → Fin 4 → JointMatrix a b)
    (hK : Measurable K) (hE : ∀ j, Measurable (fun ω => E ω j))
    (hG : Integrable (fun ω => (K ω)ᴴ * K ω) μ)
    (hcomplete : (∫ ω, (K ω)ᴴ * K ω ∂μ) = 1)
    (hpos : ∀ ω j, (E ω j).PosSemidef) (hsum : ∀ ω, ∑ j, E ω j = 1) :
    (∀ j, (∫ ω, aliceSandwich (K ω) (E ω j) ∂μ).PosSemidef) ∧
      (∑ j, ∫ ω, aliceSandwich (K ω) (E ω j) ∂μ) = 1 := by
  have hle (ω : Ω) (j : Fin 4) : E ω j ≤ 1 := by
    simpa only [hsum ω] using Finset.single_le_sum
      (fun k (_ : k ∈ Finset.univ) => (hpos ω k).nonneg) (Finset.mem_univ j)
  have hInt := QuantumProver.ElegantJointMeasurement.InstrumentNormalization.integrable_leftConditionalEffects
    μ K E hK hE hG hpos hle
  have hIntj (j : Fin 4) : Integrable (fun ω => aliceSandwich (K ω) (E ω j)) μ := by
    simpa only [QuantumProver.ElegantJointMeasurement.InstrumentNormalization.leftConditionalEffects, aliceSandwich] using hInt.eval j
  constructor
  · intro j
    apply Matrix.nonneg_iff_posSemidef.mp
    apply integral_nonneg_of_ae
    exact Filter.Eventually.of_forall fun ω =>
      (QuantumProver.ElegantJointMeasurement.InstrumentNormalization.matrix_pullback_posSemidef
        (K ω ⊗ₖ (1 : LocalMatrix b)) (hpos ω j)).nonneg
  · calc
      _ = ∫ ω, ∑ j, aliceSandwich (K ω) (E ω j) ∂μ :=
        (integral_finsetSum Finset.univ (fun j _ => hIntj j)).symm
      _ = ∫ ω, aliceSandwich (K ω) (1 : JointMatrix a b) ∂μ := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun ω => by
          dsimp only
          rw [sum_aliceSandwich, hsum ω]
      _ = 1 := integral_aliceSandwich_one μ K hG hcomplete

theorem integrated_bobPOVM {Ω : Type*} [MeasurableSpace Ω] {a b : ℕ}
    (μ : Measure Ω) (K : Ω → LocalMatrix b) (E : Ω → Fin 4 → JointMatrix a b)
    (hK : Measurable K) (hE : ∀ j, Measurable (fun ω => E ω j))
    (hG : Integrable (fun ω => (K ω)ᴴ * K ω) μ)
    (hcomplete : (∫ ω, (K ω)ᴴ * K ω ∂μ) = 1)
    (hpos : ∀ ω j, (E ω j).PosSemidef) (hsum : ∀ ω, ∑ j, E ω j = 1) :
    (∀ j, (∫ ω, bobSandwich (K ω) (E ω j) ∂μ).PosSemidef) ∧
      (∑ j, ∫ ω, bobSandwich (K ω) (E ω j) ∂μ) = 1 := by
  have hle (ω : Ω) (j : Fin 4) : E ω j ≤ 1 := by
    simpa only [hsum ω] using Finset.single_le_sum
      (fun k (_ : k ∈ Finset.univ) => (hpos ω k).nonneg) (Finset.mem_univ j)
  have hInt := QuantumProver.ElegantJointMeasurement.InstrumentNormalization.integrable_rightConditionalEffects
    μ K E hK hE hG hpos hle
  have hIntj (j : Fin 4) : Integrable (fun ω => bobSandwich (K ω) (E ω j)) μ := by
    simpa only [QuantumProver.ElegantJointMeasurement.InstrumentNormalization.rightConditionalEffects, bobSandwich] using hInt.eval j
  constructor
  · intro j
    apply Matrix.nonneg_iff_posSemidef.mp
    apply integral_nonneg_of_ae
    exact Filter.Eventually.of_forall fun ω =>
      (QuantumProver.ElegantJointMeasurement.InstrumentNormalization.matrix_pullback_posSemidef
        ((1 : LocalMatrix a) ⊗ₖ K ω) (hpos ω j)).nonneg
  · calc
      _ = ∫ ω, ∑ j, bobSandwich (K ω) (E ω j) ∂μ :=
        (integral_finsetSum Finset.univ (fun j _ => hIntj j)).symm
      _ = ∫ ω, bobSandwich (K ω) (1 : JointMatrix a b) ∂μ := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun ω => by
          dsimp only
          rw [sum_bobSandwich, hsum ω]
      _ = 1 := integral_bobSandwich_one μ K hG hcomplete

theorem reportedEffect_povm {a b height : ℕ} (T : Tree.{u} a b height)
    (hT : WellFormed T) :
    (∀ j, (reportedEffect T j).PosSemidef) ∧ (∑ j, reportedEffect T j) = 1 := by
  revert hT
  induction T with
  | leaf height report =>
    intro _
    constructor
    · intro j
      simp only [reportedEffect]
      split_ifs
      · exact Matrix.PosSemidef.one
      · exact Matrix.PosSemidef.zero
    · exact sum_reportedEffect_leaf a b height report
  | @alice height Ω mΩ μ K child ih =>
    let := mΩ
    intro hT
    rcases hT with ⟨_, hK, hG, hcomplete, hchild, hE⟩
    exact integrated_alicePOVM μ K (fun ω j => reportedEffect (child ω) j)
      hK hE hG hcomplete (fun ω j => (ih ω (hchild ω)).1 j)
      (fun ω => (ih ω (hchild ω)).2)
  | @bob height Ω mΩ μ K child ih =>
    let := mΩ
    intro hT
    rcases hT with ⟨_, hK, hG, hcomplete, hchild, hE⟩
    exact integrated_bobPOVM μ K (fun ω j => reportedEffect (child ω) j)
      hK hE hG hcomplete (fun ω j => (ih ω (hchild ω)).1 j)
      (fun ω => (ih ω (hchild ω)).2)

theorem reportedEffect_bounds {a b height : ℕ} (T : Tree.{u} a b height)
    (hT : WellFormed T) (j : Fin 4) :
    (reportedEffect T j).PosSemidef ∧ reportedEffect T j ≤ 1 := by
  have h := reportedEffect_povm T hT
  refine ⟨h.1 j, ?_⟩
  simpa only [h.2] using Finset.single_le_sum
    (fun k (_ : k ∈ Finset.univ) => (h.1 k).nonneg) (Finset.mem_univ j)

theorem hermitian_norm_order_bounds {I : Type*} [Fintype I] [DecidableEq I]
    (D : Matrix I I ℂ) (eta : ℝ) (hD : D.IsHermitian) (hNorm : ‖D‖ ≤ eta) :
    (-eta) • (1 : Matrix I I ℂ) ≤ D ∧ D ≤ eta • 1 := by
  have hs : ‖D‖ • (1 : Matrix I I ℂ) ≤ eta • 1 :=
    smul_le_smul_of_nonneg_right hNorm Matrix.PosSemidef.one.nonneg
  have hU : D ≤ ‖D‖ • (1 : Matrix I I ℂ) := by
    simpa only [Algebra.algebraMap_eq_smul_one] using
      IsSelfAdjoint.le_algebraMap_norm_self D hD.isSelfAdjoint
  have hL : -(‖D‖ • (1 : Matrix I I ℂ)) ≤ D := by
    simpa only [Algebra.algebraMap_eq_smul_one] using
      IsSelfAdjoint.neg_algebraMap_norm_le_self D hD.isSelfAdjoint
  exact ⟨by simpa only [neg_smul] using (neg_le_neg hs).trans hL, hU.trans hs⟩

theorem aliceSandwich_weighted {a b : ℕ} (w : ℝ) (K : LocalMatrix a)
    (E : JointMatrix a b) (hw : 0 ≤ w) :
    aliceSandwich (QuantumProver.ElegantJointMeasurement.ContinuousInstrumentQuadrature.weightedKraus w K) E =
      w • aliceSandwich K E := by
  simp only [aliceSandwich, QuantumProver.ElegantJointMeasurement.ContinuousInstrumentQuadrature.weightedKraus,
    Matrix.smul_kronecker, Matrix.conjTranspose_smul, star_trivial,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul, Real.mul_self_sqrt hw]

theorem bobSandwich_weighted {a b : ℕ} (w : ℝ) (K : LocalMatrix b)
    (E : JointMatrix a b) (hw : 0 ≤ w) :
    bobSandwich (QuantumProver.ElegantJointMeasurement.ContinuousInstrumentQuadrature.weightedKraus w K) E =
      w • bobSandwich K E := by
  simp only [bobSandwich, QuantumProver.ElegantJointMeasurement.ContinuousInstrumentQuadrature.weightedKraus,
    Matrix.kronecker_smul, Matrix.conjTranspose_smul, star_trivial,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul, Real.mul_self_sqrt hw]

theorem normalized_alice_true_sum {a b : ℕ} {samples : ℕ → ℕ}
    (K : (k : ℕ) → Fin (samples k) → LocalMatrix a) (k : ℕ)
    (E : Fin (samples k) → JointMatrix a b) :
    QuantumProver.ElegantJointMeasurement.InstrumentNormalization.summedPullback
      (fun i => QuantumProver.ElegantJointMeasurement.InstrumentNormalization.normalizedKraus K k i ⊗ₖ (1 : LocalMatrix b)) E =
      (QuantumProver.ElegantJointMeasurement.InstrumentNormalization.localNormalizer K k)ᴴ *
        (∑ i, aliceSandwich (K k i) (E i)) *
        QuantumProver.ElegantJointMeasurement.InstrumentNormalization.localNormalizer K k := by
  classical
  unfold QuantumProver.ElegantJointMeasurement.InstrumentNormalization.summedPullback
  simp only [Matrix.mul_sum, Matrix.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  have heq : QuantumProver.ElegantJointMeasurement.InstrumentNormalization.normalizedKraus K k i ⊗ₖ (1 : LocalMatrix b) =
      (K k i ⊗ₖ (1 : LocalMatrix b)) *
        QuantumProver.ElegantJointMeasurement.InstrumentNormalization.localNormalizer K k := by
    change (K k i * QuantumProver.ElegantJointMeasurement.InstrumentNormalization.normalizer K k) ⊗ₖ (1 : LocalMatrix b) =
      (K k i ⊗ₖ (1 : LocalMatrix b)) *
        (QuantumProver.ElegantJointMeasurement.InstrumentNormalization.normalizer K k ⊗ₖ (1 : LocalMatrix b))
    rw [← Matrix.mul_kronecker_mul, Matrix.one_mul]
  rw [heq]
  exact QuantumProver.ElegantJointMeasurement.InstrumentNormalization.pullback_mul _ _ _

theorem normalized_bob_true_sum {a b : ℕ} {samples : ℕ → ℕ}
    (K : (k : ℕ) → Fin (samples k) → LocalMatrix b) (k : ℕ)
    (E : Fin (samples k) → JointMatrix a b) :
    QuantumProver.ElegantJointMeasurement.InstrumentNormalization.summedPullback
      (fun i => (1 : LocalMatrix a) ⊗ₖ QuantumProver.ElegantJointMeasurement.InstrumentNormalization.normalizedKraus K k i) E =
      (QuantumProver.ElegantJointMeasurement.InstrumentNormalization.rightLocalNormalizer K k)ᴴ *
        (∑ i, bobSandwich (K k i) (E i)) *
        QuantumProver.ElegantJointMeasurement.InstrumentNormalization.rightLocalNormalizer K k := by
  classical
  unfold QuantumProver.ElegantJointMeasurement.InstrumentNormalization.summedPullback
  simp only [Matrix.mul_sum, Matrix.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  have heq : (1 : LocalMatrix a) ⊗ₖ QuantumProver.ElegantJointMeasurement.InstrumentNormalization.normalizedKraus K k i =
      ((1 : LocalMatrix a) ⊗ₖ K k i) *
        QuantumProver.ElegantJointMeasurement.InstrumentNormalization.rightLocalNormalizer K k := by
    change (1 : LocalMatrix a) ⊗ₖ (K k i * QuantumProver.ElegantJointMeasurement.InstrumentNormalization.normalizer K k) =
      ((1 : LocalMatrix a) ⊗ₖ K k i) *
        ((1 : LocalMatrix a) ⊗ₖ QuantumProver.ElegantJointMeasurement.InstrumentNormalization.normalizer K k)
    rw [← Matrix.mul_kronecker_mul, Matrix.one_mul]
  rw [heq]
  exact QuantumProver.ElegantJointMeasurement.InstrumentNormalization.pullback_mul _ _ _

@[simp] theorem matrix_cp_leaf_effect (a b : ℕ) (report j : Fin 4) :
    (QuantumProver.ElegantJointMeasurement.CP.FiniteLocalCPInstrumentTree.leaf a b).matrixReportedEffect report j =
      if report = j then 1 else 0 := by
  symm
  apply QuantumProver.ElegantJointMeasurement.CP.FiniteLocalCPInstrumentTree.matrixReportedEffect_unique
  intro X
  simp only [QuantumProver.ElegantJointMeasurement.CP.FiniteLocalCPInstrumentTree.matrixReportedEvaluation]
  split_ifs <;> simp

theorem approximate_alice_with_finite_children {Ω : Type*} [MeasurableSpace Ω]
    {a b : ℕ} (μ : Measure Ω) [IsFiniteMeasure μ]
    (K : Ω → LocalMatrix a) (E : Ω → Fin 4 → JointMatrix a b)
    (hK : Measurable K) (hE : ∀ j, Measurable (fun ω => E ω j))
    (hGramInt : Integrable (fun ω => (K ω)ᴴ * K ω) μ)
    (hGramComplete : (∫ ω, (K ω)ᴴ * K ω ∂μ) = 1)
    (hPos : ∀ ω j, (E ω j).PosSemidef) (hLe : ∀ ω j, E ω j ≤ 1)
    (hChild : ∀ ω (eta : ℝ), 0 < eta →
      ∃ U : QuantumProver.ElegantJointMeasurement.CP.FiniteLocalCPInstrumentTree a b,
        ∃ labels : QuantumProver.ElegantJointMeasurement.CP.FiniteLocalCPInstrumentTree.LeafLabels U (Fin 4),
          ∀ j, ‖U.matrixReportedEffect labels j - E ω j‖ ≤ eta)
    (epsilon : ℝ) (hEpsilon : 0 < epsilon) :
    ∃ U : QuantumProver.ElegantJointMeasurement.CP.FiniteLocalCPInstrumentTree a b,
      ∃ labels : QuantumProver.ElegantJointMeasurement.CP.FiniteLocalCPInstrumentTree.LeafLabels U (Fin 4),
        ∀ j, ‖U.matrixReportedEffect labels j -
          (∫ ω, aliceSandwich (K ω) (E ω j) ∂μ)‖ ≤ epsilon := by
  classical
  let f := QuantumProver.ElegantJointMeasurement.InstrumentNormalization.leftConditionalEffects K E
  have hf : Integrable f μ :=
    QuantumProver.ElegantJointMeasurement.InstrumentNormalization.integrable_leftConditionalEffects μ K E
      hK hE hGramInt hPos hLe
  obtain ⟨samples, w, point, hw, _hmass, _hpoint, hG', hF'⟩ :=
    QuantumProver.ElegantJointMeasurement.ContinuousInstrumentQuadrature.exists_joint_sampled_kraus_quadrature_on
      μ K f (hGramInt.prodMk hf) Set.univ (Filter.Eventually.of_forall fun _ => Set.mem_univ _)
  let Ks : (k : ℕ) → Fin (samples k) → LocalMatrix a :=
    fun k i => QuantumProver.ElegantJointMeasurement.ContinuousInstrumentQuadrature.weightedKraus (w k i) (K (point k i))
  have hG : Tendsto (QuantumProver.ElegantJointMeasurement.InstrumentNormalization.gramTotal Ks) atTop (𝓝 1) := by
    change Tendsto (fun k => ∑ i, (Ks k i)ᴴ * Ks k i) atTop (𝓝 1)
    simpa only [Ks, hGramComplete] using hG'
  let H : Fin 4 → JointMatrix a b := fun j => ∫ ω, aliceSandwich (K ω) (E ω j) ∂μ
  let F : ℕ → Fin 4 → JointMatrix a b :=
    fun k j => ∑ i, aliceSandwich (Ks k i) (E (point k i) j)
  have hValues (k : ℕ) : F k = ∑ i, w k i • f (point k i) := by
    funext j
    simp only [F, Ks, Finset.sum_apply, Pi.smul_apply]
    apply Finset.sum_congr rfl
    intro i _
    exact aliceSandwich_weighted _ _ _ (hw k i)
  have hIntegral : (∫ ω, f ω ∂μ) = H := by
    funext j
    exact MeasureTheory.eval_integral (fun j => hf.eval j) j
  have hF : Tendsto F atTop (𝓝 H) := by
    rw [← hIntegral]
    exact hF'.congr' (Filter.Eventually.of_forall fun k => (hValues k).symm)
  let M : ℕ → Fin 4 → JointMatrix a b := fun k j =>
    (QuantumProver.ElegantJointMeasurement.InstrumentNormalization.localNormalizer Ks k)ᴴ * F k j *
      QuantumProver.ElegantJointMeasurement.InstrumentNormalization.localNormalizer Ks k
  have hM : Tendsto M atTop (𝓝 H) :=
    QuantumProver.ElegantJointMeasurement.InstrumentNormalization.normalized_local_effect_limit Ks hG F H hF
  have hClose : ∀ᶠ k in atTop, ∀ j, ‖M k j - H j‖ < epsilon / 2 := by
    have hC := Metric.tendsto_nhds.mp hM (epsilon / 2) (half_pos hEpsilon)
    filter_upwards [hC] with k hk j
    rw [dist_eq_norm] at hk
    exact (norm_le_pi_norm (M k - H) j).trans_lt hk
  obtain ⟨k, hPD, hk⟩ :=
    ((QuantumProver.ElegantJointMeasurement.InstrumentNormalization.eventually_gramTotal_posDef Ks hG).and hClose).exists
  choose U labels hU using fun i : Fin (samples k) =>
    hChild (point k i) (epsilon / 2) (half_pos hEpsilon)
  let P := QuantumProver.ElegantJointMeasurement.InstrumentNormalization.normalizedAliceNode Ks k hPD U
  let labelsP := QuantumProver.ElegantJointMeasurement.InstrumentNormalization.normalizedAliceLabels Ks k hPD U labels
  refine ⟨P, labelsP, ?_⟩
  intro j
  have hBounds (i : Fin (samples k)) :
      (-(epsilon / 2)) • (1 : JointMatrix a b) ≤
        E (point k i) j - (U i).matrixReportedEffect (labels i) j ∧
      E (point k i) j - (U i).matrixReportedEffect (labels i) j ≤ (epsilon / 2) • 1 := by
    have hD := (hPos (point k i) j).isHermitian.sub
      ((U i).matrixReportedEffect_posSemidef (labels i) j).isHermitian
    have hNorm : ‖E (point k i) j - (U i).matrixReportedEffect (labels i) j‖ ≤ epsilon / 2 := by
      simpa only [norm_sub_rev] using hU i j
    exact hermitian_norm_order_bounds _ (epsilon / 2) hD hNorm
  have hR := QuantumProver.ElegantJointMeasurement.InstrumentNormalization.normalizedLeftChildReplacement_bound
    Ks k hPD (fun i => E (point k i) j) U labels j (epsilon / 2)
    (le_of_lt (half_pos hEpsilon)) (fun i => (hPos (point k i) j).isHermitian)
    (fun i => (hBounds i).1) (fun i => (hBounds i).2)
  have hIdeal : QuantumProver.ElegantJointMeasurement.InstrumentNormalization.summedPullback
      (fun i => QuantumProver.ElegantJointMeasurement.InstrumentNormalization.normalizedKraus Ks k i ⊗ₖ (1 : LocalMatrix b))
      (fun i => E (point k i) j) = M k j := normalized_alice_true_sum Ks k _
  have hErr := hR.2
  change ‖QuantumProver.ElegantJointMeasurement.InstrumentNormalization.summedPullback
      (fun i => QuantumProver.ElegantJointMeasurement.InstrumentNormalization.normalizedKraus Ks k i ⊗ₖ (1 : LocalMatrix b))
      (fun i => E (point k i) j) - P.matrixReportedEffect labelsP j‖ ≤ epsilon / 2 at hErr
  rw [hIdeal] at hErr
  calc
    ‖P.matrixReportedEffect labelsP j - H j‖ ≤
        ‖P.matrixReportedEffect labelsP j - M k j‖ + ‖M k j - H j‖ := by
      simpa only [dist_eq_norm] using dist_triangle (P.matrixReportedEffect labelsP j) (M k j) (H j)
    _ ≤ epsilon / 2 + epsilon / 2 :=
      add_le_add (by simpa only [norm_sub_rev] using hErr) (le_of_lt (hk j))
    _ = epsilon := by ring

theorem approximate_bob_with_finite_children {Ω : Type*} [MeasurableSpace Ω]
    {a b : ℕ} (μ : Measure Ω) [IsFiniteMeasure μ]
    (K : Ω → LocalMatrix b) (E : Ω → Fin 4 → JointMatrix a b)
    (hK : Measurable K) (hE : ∀ j, Measurable (fun ω => E ω j))
    (hGramInt : Integrable (fun ω => (K ω)ᴴ * K ω) μ)
    (hGramComplete : (∫ ω, (K ω)ᴴ * K ω ∂μ) = 1)
    (hPos : ∀ ω j, (E ω j).PosSemidef) (hLe : ∀ ω j, E ω j ≤ 1)
    (hChild : ∀ ω (eta : ℝ), 0 < eta →
      ∃ U : QuantumProver.ElegantJointMeasurement.CP.FiniteLocalCPInstrumentTree a b,
        ∃ labels : QuantumProver.ElegantJointMeasurement.CP.FiniteLocalCPInstrumentTree.LeafLabels U (Fin 4),
          ∀ j, ‖U.matrixReportedEffect labels j - E ω j‖ ≤ eta)
    (epsilon : ℝ) (hEpsilon : 0 < epsilon) :
    ∃ U : QuantumProver.ElegantJointMeasurement.CP.FiniteLocalCPInstrumentTree a b,
      ∃ labels : QuantumProver.ElegantJointMeasurement.CP.FiniteLocalCPInstrumentTree.LeafLabels U (Fin 4),
        ∀ j, ‖U.matrixReportedEffect labels j -
          (∫ ω, bobSandwich (K ω) (E ω j) ∂μ)‖ ≤ epsilon := by
  classical
  let f := QuantumProver.ElegantJointMeasurement.InstrumentNormalization.rightConditionalEffects K E
  have hf : Integrable f μ :=
    QuantumProver.ElegantJointMeasurement.InstrumentNormalization.integrable_rightConditionalEffects μ K E
      hK hE hGramInt hPos hLe
  obtain ⟨samples, w, point, hw, _hmass, _hpoint, hG', hF'⟩ :=
    QuantumProver.ElegantJointMeasurement.ContinuousInstrumentQuadrature.exists_joint_sampled_kraus_quadrature_on
      μ K f (hGramInt.prodMk hf) Set.univ (Filter.Eventually.of_forall fun _ => Set.mem_univ _)
  let Ks : (k : ℕ) → Fin (samples k) → LocalMatrix b :=
    fun k i => QuantumProver.ElegantJointMeasurement.ContinuousInstrumentQuadrature.weightedKraus (w k i) (K (point k i))
  have hG : Tendsto (QuantumProver.ElegantJointMeasurement.InstrumentNormalization.gramTotal Ks) atTop (𝓝 1) := by
    change Tendsto (fun k => ∑ i, (Ks k i)ᴴ * Ks k i) atTop (𝓝 1)
    simpa only [Ks, hGramComplete] using hG'
  let H : Fin 4 → JointMatrix a b := fun j => ∫ ω, bobSandwich (K ω) (E ω j) ∂μ
  let F : ℕ → Fin 4 → JointMatrix a b :=
    fun k j => ∑ i, bobSandwich (Ks k i) (E (point k i) j)
  have hValues (k : ℕ) : F k = ∑ i, w k i • f (point k i) := by
    funext j
    simp only [F, Ks, Finset.sum_apply, Pi.smul_apply]
    apply Finset.sum_congr rfl
    intro i _
    exact bobSandwich_weighted _ _ _ (hw k i)
  have hIntegral : (∫ ω, f ω ∂μ) = H := by
    funext j
    exact MeasureTheory.eval_integral (fun j => hf.eval j) j
  have hF : Tendsto F atTop (𝓝 H) := by
    rw [← hIntegral]
    exact hF'.congr' (Filter.Eventually.of_forall fun k => (hValues k).symm)
  let M : ℕ → Fin 4 → JointMatrix a b := fun k j =>
    (QuantumProver.ElegantJointMeasurement.InstrumentNormalization.rightLocalNormalizer Ks k)ᴴ * F k j *
      QuantumProver.ElegantJointMeasurement.InstrumentNormalization.rightLocalNormalizer Ks k
  have hM : Tendsto M atTop (𝓝 H) :=
    QuantumProver.ElegantJointMeasurement.InstrumentNormalization.normalized_right_local_effect_limit Ks hG F H hF
  have hClose : ∀ᶠ k in atTop, ∀ j, ‖M k j - H j‖ < epsilon / 2 := by
    have hC := Metric.tendsto_nhds.mp hM (epsilon / 2) (half_pos hEpsilon)
    filter_upwards [hC] with k hk j
    rw [dist_eq_norm] at hk
    exact (norm_le_pi_norm (M k - H) j).trans_lt hk
  obtain ⟨k, hPD, hk⟩ :=
    ((QuantumProver.ElegantJointMeasurement.InstrumentNormalization.eventually_gramTotal_posDef Ks hG).and hClose).exists
  choose U labels hU using fun i : Fin (samples k) =>
    hChild (point k i) (epsilon / 2) (half_pos hEpsilon)
  let P := QuantumProver.ElegantJointMeasurement.InstrumentNormalization.normalizedBobNode Ks k hPD U
  let labelsP := QuantumProver.ElegantJointMeasurement.InstrumentNormalization.normalizedBobLabels Ks k hPD U labels
  refine ⟨P, labelsP, ?_⟩
  intro j
  have hBounds (i : Fin (samples k)) :
      (-(epsilon / 2)) • (1 : JointMatrix a b) ≤
        E (point k i) j - (U i).matrixReportedEffect (labels i) j ∧
      E (point k i) j - (U i).matrixReportedEffect (labels i) j ≤ (epsilon / 2) • 1 := by
    have hD := (hPos (point k i) j).isHermitian.sub
      ((U i).matrixReportedEffect_posSemidef (labels i) j).isHermitian
    have hNorm : ‖E (point k i) j - (U i).matrixReportedEffect (labels i) j‖ ≤ epsilon / 2 := by
      simpa only [norm_sub_rev] using hU i j
    exact hermitian_norm_order_bounds _ (epsilon / 2) hD hNorm
  have hR := QuantumProver.ElegantJointMeasurement.InstrumentNormalization.normalizedRightChildReplacement_bound
    Ks k hPD (fun i => E (point k i) j) U labels j (epsilon / 2)
    (le_of_lt (half_pos hEpsilon)) (fun i => (hPos (point k i) j).isHermitian)
    (fun i => (hBounds i).1) (fun i => (hBounds i).2)
  have hIdeal : QuantumProver.ElegantJointMeasurement.InstrumentNormalization.summedPullback
      (fun i => (1 : LocalMatrix a) ⊗ₖ QuantumProver.ElegantJointMeasurement.InstrumentNormalization.normalizedKraus Ks k i)
      (fun i => E (point k i) j) = M k j := normalized_bob_true_sum Ks k _
  have hErr := hR.2
  change ‖QuantumProver.ElegantJointMeasurement.InstrumentNormalization.summedPullback
      (fun i => (1 : LocalMatrix a) ⊗ₖ QuantumProver.ElegantJointMeasurement.InstrumentNormalization.normalizedKraus Ks k i)
      (fun i => E (point k i) j) - P.matrixReportedEffect labelsP j‖ ≤ epsilon / 2 at hErr
  rw [hIdeal] at hErr
  calc
    ‖P.matrixReportedEffect labelsP j - H j‖ ≤
        ‖P.matrixReportedEffect labelsP j - M k j‖ + ‖M k j - H j‖ := by
      simpa only [dist_eq_norm] using dist_triangle (P.matrixReportedEffect labelsP j) (M k j) (H j)
    _ ≤ epsilon / 2 + epsilon / 2 :=
      add_le_add (by simpa only [norm_sub_rev] using hErr) (le_of_lt (hk j))
    _ = epsilon := by ring

theorem exists_finiteCPTree_approx {a b height : ℕ} (T : Tree.{u} a b height)
    (hT : WellFormed T) (epsilon : ℝ) (hEpsilon : 0 < epsilon) :
    ∃ U : QuantumProver.ElegantJointMeasurement.CP.FiniteLocalCPInstrumentTree a b,
      ∃ labels : QuantumProver.ElegantJointMeasurement.CP.FiniteLocalCPInstrumentTree.LeafLabels U (Fin 4),
        ∀ j, ‖U.matrixReportedEffect labels j - reportedEffect T j‖ ≤ epsilon := by
  classical
  revert hT epsilon
  induction T with
  | leaf height report =>
    intro _ epsilon hEpsilon
    refine ⟨.leaf a b, report, ?_⟩
    intro j
    simp only [matrix_cp_leaf_effect, reportedEffect_leaf, sub_self, norm_zero]
    exact le_of_lt hEpsilon
  | @alice height Ω mΩ μ K child ih =>
    let := mΩ
    intro hT epsilon hEpsilon
    rcases hT with ⟨hμ, hK, hGramInt, hGramComplete, hChild, hE⟩
    let := hμ
    exact approximate_alice_with_finite_children μ K (fun ω j => reportedEffect (child ω) j)
      hK hE hGramInt hGramComplete
      (fun ω j => (reportedEffect_bounds (child ω) (hChild ω) j).1)
      (fun ω j => (reportedEffect_bounds (child ω) (hChild ω) j).2)
      (fun ω eta hEta => ih ω (hChild ω) eta hEta) epsilon hEpsilon
  | @bob height Ω mΩ μ K child ih =>
    let := mΩ
    intro hT epsilon hEpsilon
    rcases hT with ⟨hμ, hK, hGramInt, hGramComplete, hChild, hE⟩
    let := hμ
    exact approximate_bob_with_finite_children μ K (fun ω j => reportedEffect (child ω) j)
      hK hE hGramInt hGramComplete
      (fun ω j => (reportedEffect_bounds (child ω) (hChild ω) j).1)
      (fun ω j => (reportedEffect_bounds (child ω) (hChild ω) j).2)
      (fun ω eta hEta => ih ω (hChild ω) eta hEta) epsilon hEpsilon

def finiteKrausReportedEffect {a b : ℕ}
    (T : QuantumProver.ElegantJointMeasurement.Concurrence.FiniteLocalKrausTree a b)
    (report : Fin T.terminalBraPairs.length → Fin 4) (j : Fin 4) : JointMatrix a b :=
  ∑ i, if report i = j then (T.terminalBraPairs.get i).productEffect else 0

theorem exists_finiteKrausTree_approx {a b height : ℕ} (T : Tree.{u} a b height)
    (hT : WellFormed T) (epsilon : ℝ) (hEpsilon : 0 < epsilon) :
    ∃ U : QuantumProver.ElegantJointMeasurement.Concurrence.FiniteLocalKrausTree a b,
      ∃ report : Fin U.terminalBraPairs.length → Fin 4,
        (∑ j, finiteKrausReportedEffect U report j) = 1 ∧
        ∀ j, ‖finiteKrausReportedEffect U report j - reportedEffect T j‖ ≤ epsilon := by
  obtain ⟨U, labels, hU⟩ := exists_finiteCPTree_approx T hT epsilon hEpsilon
  refine ⟨U.krausRefinement, U.terminalReport labels, ?_, ?_⟩
  · exact U.sum_matrixReportedEffect labels
  · exact hU

theorem actual_finite_tree_approx {a b height : ℕ} (_ha : 0 < a) (_hb : 0 < b)
    (T : Tree.{u} a b height) (hT : WellFormed T)
    (epsilon : ℝ) (hEpsilon : 0 < epsilon) :
    ∃ U : QuantumProver.ElegantJointMeasurement.Concurrence.FiniteLocalKrausTree a b,
      ∃ report : Fin U.terminalBraPairs.length → Fin 4,
        (∑ j, finiteKrausReportedEffect U report j) = 1 ∧
        ∀ j, ‖Matrix.toEuclideanCLM (𝕜 := ℂ)
          (finiteKrausReportedEffect U report j - reportedEffect T j)‖ ≤ epsilon := by
  exact exists_finiteKrausTree_approx T hT epsilon hEpsilon

def finiteKrausReportedEffectSet (a b : ℕ) : Set (Fin 4 → JointMatrix a b) :=
  {F | ∃ U : QuantumProver.ElegantJointMeasurement.Concurrence.FiniteLocalKrausTree a b,
    ∃ report : Fin U.terminalBraPairs.length → Fin 4,
      F = finiteKrausReportedEffect U report}

theorem reportedEffect_mem_finiteKrausReportedEffectSet_closure
    {a b height : ℕ} (T : Tree.{u} a b height) (hT : WellFormed T) :
    reportedEffect T ∈ closure (finiteKrausReportedEffectSet a b) := by
  apply Metric.mem_closure_iff.mpr
  intro epsilon hEpsilon
  obtain ⟨U, report, _hSum, hU⟩ :=
    exists_finiteKrausTree_approx T hT (epsilon / 2) (half_pos hEpsilon)
  refine ⟨finiteKrausReportedEffect U report, ⟨U, report, rfl⟩, ?_⟩
  rw [dist_eq_norm]
  apply (pi_norm_lt_iff hEpsilon).mpr
  intro j
  simpa only [Pi.sub_apply, norm_sub_rev] using
    (hU j).trans_lt (half_lt_self hEpsilon)

theorem exists_finite_tree_sequence {a b height : ℕ} (T : Tree.{u} a b height)
    (hT : WellFormed T) :
    ∃ U : ℕ → QuantumProver.ElegantJointMeasurement.Concurrence.FiniteLocalKrausTree a b,
      ∃ report : (k : ℕ) → Fin (U k).terminalBraPairs.length → Fin 4,
        Tendsto (fun k => finiteKrausReportedEffect (U k) (report k))
          atTop (𝓝 (reportedEffect T)) := by
  obtain ⟨F, hF, hlim⟩ := mem_closure_iff_seq_limit.mp
    (reportedEffect_mem_finiteKrausReportedEffectSet_closure T hT)
  choose U report hEq using hF
  exact ⟨U, report, hlim.congr' (Filter.Eventually.of_forall fun k => hEq k)⟩

end

end QuantumProver.ElegantJointMeasurement.HilbertContinuousProtocol

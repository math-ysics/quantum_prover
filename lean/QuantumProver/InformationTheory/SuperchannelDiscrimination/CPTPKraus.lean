import Mathlib
import QuantumProver.InformationTheory.SuperchannelDiscrimination.Definitions
import QuantumProver.InformationTheory.ElegantJointMeasurement.IConcurrence

set_option autoImplicit false

noncomputable section

open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder Matrix Kronecker

namespace QuantumProver.SuperchannelDiscrimination.CPTPKraus

variable {I O : Type*} [Fintype I] [Fintype O]
  [DecidableEq I] [DecidableEq O]

def amplify (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ)
    (R : Type*) [Fintype R] (A : Matrix (I × R) (I × R) ℂ) :
    Matrix (O × R) (O × R) ℂ :=
  fun x y => Φ (fun i j => A (i, x.2) (j, y.2)) x.1 y.1

def CompletelyPositive (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) : Prop :=
  ∀ r (A : Matrix (I × Fin r) (I × Fin r) ℂ),
    A.PosSemidef → (amplify Φ (Fin r) A).PosSemidef

def TracePreserving (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) : Prop :=
  ∀ A : Matrix I I ℂ, (Φ A).trace = A.trace

theorem amplification_swap (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) (r : ℕ)
    (A : Matrix (Fin r × I) (Fin r × I) ℂ) :
    QuantumProver.ElegantJointMeasurement.CP.amplification Φ r A =
      (amplify Φ (Fin r)
        (A.submatrix (Equiv.prodComm I (Fin r)) (Equiv.prodComm I (Fin r)))).submatrix
          (Equiv.prodComm (Fin r) O) (Equiv.prodComm (Fin r) O) := by
  rfl

theorem amplify_swap (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) (r : ℕ)
    (A : Matrix (I × Fin r) (I × Fin r) ℂ) :
    amplify Φ (Fin r) A =
      (QuantumProver.ElegantJointMeasurement.CP.amplification Φ r
        (A.submatrix (Equiv.prodComm (Fin r) I) (Equiv.prodComm (Fin r) I))).submatrix
          (Equiv.prodComm O (Fin r)) (Equiv.prodComm O (Fin r)) := by
  rfl

theorem completelyPositive_to_EJMCP
    {Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ} (hΦ : CompletelyPositive Φ) :
    QuantumProver.ElegantJointMeasurement.CP.CompletelyPositive Φ := by
  intro r A hA
  rw [amplification_swap]
  exact (hΦ r _ (hA.submatrix (Equiv.prodComm I (Fin r)))).submatrix
    (Equiv.prodComm (Fin r) O)

theorem completelyPositive_iff_EJMCP
    (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) :
    CompletelyPositive Φ ↔ QuantumProver.ElegantJointMeasurement.CP.CompletelyPositive Φ := by
  refine ⟨completelyPositive_to_EJMCP, ?_⟩
  intro hΦ r A hA
  rw [amplify_swap]
  exact (hΦ r _ (hA.submatrix (Equiv.prodComm (Fin r) I))).submatrix
    (Equiv.prodComm O (Fin r))

def canonicalKraus (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) :
    I × O → Matrix O I ℂ := QuantumProver.ElegantJointMeasurement.CP.krausOperator Φ

theorem canonicalKraus_apply (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ)
    (q : I × O) (o : O) (i : I) :
    canonicalKraus Φ q o i = CFC.sqrt (QuantumProver.ElegantJointMeasurement.CP.choi Φ) (i, o) q := rfl

theorem canonicalKraus_reconstruct_map
    (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) (hΦ : CompletelyPositive Φ) :
    Φ = QuantumProver.ElegantJointMeasurement.CP.krausMap (canonicalKraus Φ) :=
  QuantumProver.ElegantJointMeasurement.CP.completelyPositive_eq_krausMap Φ (completelyPositive_to_EJMCP hΦ)

theorem canonicalKraus_reconstruct
    (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) (hΦ : CompletelyPositive Φ)
    (A : Matrix I I ℂ) :
    Φ A = ∑ q : I × O, canonicalKraus Φ q * A * (canonicalKraus Φ q)ᴴ :=
  QuantumProver.ElegantJointMeasurement.CP.completelyPositive_apply_eq_sum Φ (completelyPositive_to_EJMCP hΦ) A

theorem canonicalKraus_gram
    (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) (hΦ : CompletelyPositive Φ)
    (htrace : TracePreserving Φ) :
    ∑ q : I × O, (canonicalKraus Φ q)ᴴ * canonicalKraus Φ q = 1 := by
  apply (QuantumProver.ElegantJointMeasurement.CP.krausMap_trace_preserving_iff (canonicalKraus Φ)).mp
  intro A
  rw [← canonicalKraus_reconstruct_map Φ hΦ]
  exact htrace A

def stabilizedKraus (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ)
    (R : Type*) [Fintype R] [DecidableEq R] :
    I × O → Matrix (O × R) (I × R) ℂ :=
  fun q => canonicalKraus Φ q ⊗ₖ (1 : Matrix R R ℂ)

theorem stabilizedKraus_block
    (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ)
    (R : Type*) [Fintype R] [DecidableEq R]
    (q : I × O) (A : Matrix (I × R) (I × R) ℂ)
    (o p : O) (r s : R) :
    (stabilizedKraus Φ R q * A * (stabilizedKraus Φ R q)ᴴ) (o, r) (p, s) =
      (canonicalKraus Φ q * Matrix.of (fun i j => A (i, r) (j, s)) *
        (canonicalKraus Φ q)ᴴ) o p := by
  simp [stabilizedKraus, Matrix.mul_apply, Matrix.kronecker_apply,
    Matrix.one_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Fintype.sum_prod_type,
    apply_ite, mul_ite, ite_mul]

theorem canonicalKraus_amplify_reconstruct
    (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) (hΦ : CompletelyPositive Φ)
    (R : Type*) [Fintype R] [DecidableEq R]
    (A : Matrix (I × R) (I × R) ℂ) :
    amplify Φ R A = ∑ q : I × O,
      stabilizedKraus Φ R q * A * (stabilizedKraus Φ R q)ᴴ := by
  ext ⟨o, r⟩ ⟨p, s⟩
  change Φ (Matrix.of (fun i j => A (i, r) (j, s))) o p = _
  rw [canonicalKraus_reconstruct Φ hΦ]
  simp only [Matrix.sum_apply, stabilizedKraus_block]

theorem stabilizedKraus_gram
    (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ)
    (R : Type*) [Fintype R] [DecidableEq R] :
    (∑ q : I × O, (stabilizedKraus Φ R q)ᴴ * stabilizedKraus Φ R q) =
      (∑ q : I × O, (canonicalKraus Φ q)ᴴ * canonicalKraus Φ q) ⊗ₖ
        (1 : Matrix R R ℂ) := by
  simp only [stabilizedKraus, Matrix.conjTranspose_kronecker,
    Matrix.conjTranspose_one, ← Matrix.mul_kronecker_mul, Matrix.one_mul]
  ext i j
  simp [Matrix.sum_apply, Matrix.kronecker_apply, Finset.sum_mul]

theorem canonicalKraus_stabilized_gram
    (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) (hΦ : CompletelyPositive Φ)
    (htrace : TracePreserving Φ)
    (R : Type*) [Fintype R] [DecidableEq R] :
    ∑ q : I × O, (stabilizedKraus Φ R q)ᴴ * stabilizedKraus Φ R q = 1 := by
  rw [stabilizedKraus_gram, canonicalKraus_gram Φ hΦ htrace,
    Matrix.one_kronecker_one]

theorem amplify_posSemidef
    (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) (hΦ : CompletelyPositive Φ)
    (R : Type*) [Fintype R] [DecidableEq R]
    {A : Matrix (I × R) (I × R) ℂ} (hA : A.PosSemidef) :
    (amplify Φ R A).PosSemidef := by
  rw [canonicalKraus_amplify_reconstruct Φ hΦ]
  apply Matrix.nonneg_iff_posSemidef.mp
  exact Finset.sum_nonneg fun q _ =>
    (hA.mul_mul_conjTranspose_same (stabilizedKraus Φ R q)).nonneg

theorem amplify_tracePreserving
    (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) (hΦ : CompletelyPositive Φ)
    (htrace : TracePreserving Φ)
    (R : Type*) [Fintype R] [DecidableEq R]
    (A : Matrix (I × R) (I × R) ℂ) :
    (amplify Φ R A).trace = A.trace := by
  rw [canonicalKraus_amplify_reconstruct Φ hΦ]
  change (QuantumProver.ElegantJointMeasurement.CP.krausMap (stabilizedKraus Φ R) A).trace = A.trace
  rw [QuantumProver.ElegantJointMeasurement.CP.krausMap_trace, canonicalKraus_stabilized_gram Φ hΦ htrace,
    Matrix.one_mul]

theorem exists_complete_kraus
    (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) (hΦ : CompletelyPositive Φ)
    (htrace : TracePreserving Φ) :
    ∃ K : I × O → Matrix O I ℂ,
      (∑ q, (K q)ᴴ * K q = 1) ∧
      (∀ A : Matrix I I ℂ, Φ A = ∑ q, K q * A * (K q)ᴴ) :=
  ⟨canonicalKraus Φ, canonicalKraus_gram Φ hΦ htrace,
    canonicalKraus_reconstruct Φ hΦ⟩

theorem map_eq_zero_of_isEmpty_input [IsEmpty I]
    (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) : Φ = 0 := by
  apply LinearMap.ext
  intro A
  have hA : A = 0 := Subsingleton.elim _ _
  simp [hA]

theorem cptp_of_isEmpty_input [IsEmpty I]
    (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) :
    CompletelyPositive Φ ∧ TracePreserving Φ := by
  have hΦ := map_eq_zero_of_isEmpty_input Φ
  constructor
  · intro r A hA
    have hz : amplify Φ (Fin r) A = 0 := by
      rw [hΦ]
      ext x y
      rfl
    rw [hz]
    exact Matrix.PosSemidef.zero
  · intro A
    simp [hΦ, Matrix.trace_eq_zero_of_isEmpty]

theorem isEmpty_input_of_isEmpty_output [IsEmpty O]
    (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) (htrace : TracePreserving Φ) :
    IsEmpty I := by
  refine ⟨fun i => ?_⟩
  have h := htrace (Matrix.single i i 1)
  simp only [Matrix.trace_eq_zero_of_isEmpty, Matrix.trace_single_eq_same] at h
  exact zero_ne_one h

theorem not_tracePreserving_of_isEmpty_output [IsEmpty O] [Nonempty I]
    (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) : ¬ TracePreserving Φ := by
  intro htrace
  letI := isEmpty_input_of_isEmpty_output Φ htrace
  exact isEmptyElim (Classical.choice (inferInstance : Nonempty I))

end QuantumProver.SuperchannelDiscrimination.CPTPKraus

namespace QuantumProver.SuperchannelDiscrimination.CPTPKraus

variable {I O : Type*} [Fintype I] [Fintype O]
  [DecidableEq I] [DecidableEq O]

def TraceNonincreasing (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) : Prop :=
  ∀ A : Matrix I I ℂ, A.PosSemidef → (Φ A).trace ≤ A.trace

def canonicalGram (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) : Matrix I I ℂ :=
  ∑ q : I × O, (canonicalKraus Φ q)ᴴ * canonicalKraus Φ q

def canonicalResidual (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) : Matrix I I ℂ :=
  1 - canonicalGram Φ

theorem canonicalGram_posSemidef (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) :
    (canonicalGram Φ).PosSemidef := by
  apply Matrix.nonneg_iff_posSemidef.mp
  exact Finset.sum_nonneg fun q _ =>
    (Matrix.posSemidef_conjTranspose_mul_self (canonicalKraus Φ q)).nonneg

theorem canonicalKraus_trace
    (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) (hΦ : CompletelyPositive Φ)
    (A : Matrix I I ℂ) :
    (Φ A).trace = (canonicalGram Φ * A).trace := by
  calc
    (Φ A).trace = (QuantumProver.ElegantJointMeasurement.CP.krausMap (canonicalKraus Φ) A).trace :=
      congrArg (fun Ψ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ => (Ψ A).trace)
        (canonicalKraus_reconstruct_map Φ hΦ)
    _ = _ := QuantumProver.ElegantJointMeasurement.CP.krausMap_trace (canonicalKraus Φ) A

theorem canonicalResidual_trace
    (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) (hΦ : CompletelyPositive Φ)
    (A : Matrix I I ℂ) :
    (canonicalResidual Φ * A).trace = A.trace - (Φ A).trace := by
  rw [canonicalResidual, Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub,
    ← canonicalKraus_trace Φ hΦ]

theorem canonicalGram_eq_of_tracePairing
    (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) (hΦ : CompletelyPositive Φ)
    (H : Matrix I I ℂ)
    (htrace : ∀ A : Matrix I I ℂ, (Φ A).trace = (H * A).trace) :
    canonicalGram Φ = H := by
  apply Matrix.ext_iff_trace_mul_right.mpr
  intro A
  rw [← canonicalKraus_trace Φ hΦ]
  exact htrace A

theorem canonicalResidual_eq_of_tracePairing
    (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) (hΦ : CompletelyPositive Φ)
    (H : Matrix I I ℂ)
    (htrace : ∀ A : Matrix I I ℂ, (Φ A).trace = (H * A).trace) :
    canonicalResidual Φ = 1 - H := by
  rw [canonicalResidual, canonicalGram_eq_of_tracePairing Φ hΦ H htrace]

theorem canonicalResidual_trace_nonneg
    (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) (hΦ : CompletelyPositive Φ)
    (htrace : TraceNonincreasing Φ)
    {A : Matrix I I ℂ} (hA : A.PosSemidef) :
    0 ≤ (canonicalResidual Φ * A).trace := by
  rw [canonicalResidual_trace Φ hΦ]
  exact sub_nonneg.mpr (htrace A hA)

theorem canonical_success_failure_trace
    (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) (hΦ : CompletelyPositive Φ)
    (A : Matrix I I ℂ) :
    (Φ A).trace + (canonicalResidual Φ * A).trace = A.trace := by
  rw [canonicalResidual_trace Φ hΦ]
  abel

theorem canonicalResidual_posSemidef
    (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) (hΦ : CompletelyPositive Φ)
    (htrace : TraceNonincreasing Φ) : (canonicalResidual Φ).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    (Matrix.isHermitian_one.sub (canonicalGram_posSemidef Φ).isHermitian)
  intro x
  have h : 0 ≤ (canonicalResidual Φ * Matrix.vecMulVec x (star x)).trace := by
    rw [canonicalResidual, Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub,
      ← canonicalKraus_trace Φ hΦ]
    exact sub_nonneg.mpr (htrace _ (Matrix.posSemidef_vecMulVec_self_star x))
  rwa [Matrix.mul_vecMulVec, Matrix.trace_vecMulVec, dotProduct_comm] at h

theorem canonicalGram_le_one
    (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) (hΦ : CompletelyPositive Φ)
    (htrace : TraceNonincreasing Φ) : canonicalGram Φ ≤ 1 :=
  sub_nonneg.mp (canonicalResidual_posSemidef Φ hΦ htrace).nonneg

def canonicalRepairKraus (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) :
    I → Matrix Unit I ℂ :=
  fun i => Matrix.replicateRow Unit (fun j => CFC.sqrt (canonicalResidual Φ) i j)

theorem canonicalRepairKraus_factorGram
    (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) :
    (∑ i : I, (canonicalRepairKraus Φ i)ᴴ * canonicalRepairKraus Φ i) =
      (CFC.sqrt (canonicalResidual Φ))ᴴ * CFC.sqrt (canonicalResidual Φ) := by
  ext j k
  simp [canonicalRepairKraus, Matrix.sum_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.replicateRow]

theorem canonicalRepairKraus_gram
    (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) (hΦ : CompletelyPositive Φ)
    (htrace : TraceNonincreasing Φ) :
    (∑ i : I, (canonicalRepairKraus Φ i)ᴴ * canonicalRepairKraus Φ i) =
      canonicalResidual Φ := by
  have hs : (CFC.sqrt (canonicalResidual Φ)).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg _)
  rw [canonicalRepairKraus_factorGram, hs.isHermitian.eq,
    CFC.sqrt_mul_sqrt_self _ (canonicalResidual_posSemidef Φ hΦ htrace).nonneg]

theorem canonicalRepairKraus_action
    (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) (hΦ : CompletelyPositive Φ)
    (htrace : TraceNonincreasing Φ) (A : Matrix I I ℂ) :
    QuantumProver.ElegantJointMeasurement.CP.krausMap (canonicalRepairKraus Φ) A =
      (canonicalResidual Φ * A).trace • (1 : Matrix Unit Unit ℂ) := by
  have ht : (QuantumProver.ElegantJointMeasurement.CP.krausMap (canonicalRepairKraus Φ) A).trace =
      (canonicalResidual Φ * A).trace := by
    rw [QuantumProver.ElegantJointMeasurement.CP.krausMap_trace, canonicalRepairKraus_gram Φ hΦ htrace]
  ext u v
  cases u
  cases v
  simpa [Matrix.trace, Matrix.diag, Matrix.smul_apply, Matrix.one_apply] using ht

def canonicalCompletionKraus (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) :
    (I × O) ⊕ I → Matrix (O ⊕ Unit) I ℂ :=
  Sum.elim
    (fun q => Matrix.fromRows (canonicalKraus Φ q) (0 : Matrix Unit I ℂ))
    (fun i => Matrix.fromRows (0 : Matrix O I ℂ) (canonicalRepairKraus Φ i))

def canonicalCompletion (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) :
    Matrix I I ℂ →ₗ[ℂ] Matrix (O ⊕ Unit) (O ⊕ Unit) ℂ :=
  QuantumProver.ElegantJointMeasurement.CP.krausMap (canonicalCompletionKraus Φ)

theorem canonicalCompletionKraus_gram
    (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) (hΦ : CompletelyPositive Φ)
    (htrace : TraceNonincreasing Φ) :
    ∑ q : (I × O) ⊕ I,
      (canonicalCompletionKraus Φ q)ᴴ * canonicalCompletionKraus Φ q = 1 := by
  have hsplit :
      (∑ q : (I × O) ⊕ I,
        (canonicalCompletionKraus Φ q)ᴴ * canonicalCompletionKraus Φ q) =
      canonicalGram Φ + ∑ i : I,
        (canonicalRepairKraus Φ i)ᴴ * canonicalRepairKraus Φ i := by
    simp [canonicalCompletionKraus, canonicalGram, Fintype.sum_sum_type,
      Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose,
      Matrix.fromCols_mul_fromRows]
  rw [hsplit, canonicalRepairKraus_gram Φ hΦ htrace, canonicalResidual]
  abel

theorem canonicalCompletion_action
    (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) (hΦ : CompletelyPositive Φ)
    (htrace : TraceNonincreasing Φ) (A : Matrix I I ℂ) :
    canonicalCompletion Φ A =
      Matrix.fromBlocks (Φ A) (0 : Matrix O Unit ℂ) (0 : Matrix Unit O ℂ)
        ((canonicalResidual Φ * A).trace • (1 : Matrix Unit Unit ℂ)) := by
  calc
    canonicalCompletion Φ A =
        Matrix.fromBlocks (QuantumProver.ElegantJointMeasurement.CP.krausMap (canonicalKraus Φ) A)
          (0 : Matrix O Unit ℂ) (0 : Matrix Unit O ℂ)
          (QuantumProver.ElegantJointMeasurement.CP.krausMap (canonicalRepairKraus Φ) A) := by
      ext (o | u) (p | v) <;>
        simp [canonicalCompletion, QuantumProver.ElegantJointMeasurement.CP.krausMap, canonicalCompletionKraus,
          Matrix.sum_apply, Fintype.sum_sum_type,
          Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose,
          Matrix.fromRows_mul_fromCols]
    _ = _ := by
      rw [← canonicalKraus_reconstruct_map Φ hΦ, canonicalRepairKraus_action Φ hΦ htrace]

theorem canonicalCompletion_completelyPositive
    (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) :
    CompletelyPositive (canonicalCompletion Φ) :=
  (completelyPositive_iff_EJMCP _).mpr
    (QuantumProver.ElegantJointMeasurement.CP.krausMap_completelyPositive (canonicalCompletionKraus Φ))

theorem canonicalCompletion_tracePreserving
    (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) (hΦ : CompletelyPositive Φ)
    (htrace : TraceNonincreasing Φ) : TracePreserving (canonicalCompletion Φ) :=
  (QuantumProver.ElegantJointMeasurement.CP.krausMap_trace_preserving_iff (canonicalCompletionKraus Φ)).mpr
    (canonicalCompletionKraus_gram Φ hΦ htrace)

theorem tensorKraus_block
    (K : Matrix O I ℂ) (R : Type*) [Fintype R] [DecidableEq R]
    (A : Matrix (I × R) (I × R) ℂ) (o p : O) (r s : R) :
    ((K ⊗ₖ (1 : Matrix R R ℂ)) * A * (K ⊗ₖ (1 : Matrix R R ℂ))ᴴ)
        (o, r) (p, s) =
      (K * Matrix.of (fun i j => A (i, r) (j, s)) * Kᴴ) o p := by
  simp [Matrix.mul_apply, Matrix.kronecker_apply, Matrix.one_apply,
    Matrix.conjTranspose_apply, Matrix.of_apply, Fintype.sum_prod_type,
    apply_ite, mul_ite, ite_mul]

theorem amplify_krausMap_reconstruct {Q : Type*} [Fintype Q]
    (K : Q → Matrix O I ℂ) (R : Type*) [Fintype R] [DecidableEq R]
    (A : Matrix (I × R) (I × R) ℂ) :
    amplify (QuantumProver.ElegantJointMeasurement.CP.krausMap K) R A = ∑ q : Q,
      (K q ⊗ₖ (1 : Matrix R R ℂ)) * A * (K q ⊗ₖ (1 : Matrix R R ℂ))ᴴ := by
  ext ⟨o, r⟩ ⟨p, s⟩
  change (∑ q : Q, K q * Matrix.of (fun i j => A (i, r) (j, s)) * (K q)ᴴ) o p = _
  simp only [Matrix.sum_apply, tensorKraus_block]

theorem canonicalCompletion_amplify_reconstruct
    (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ)
    (R : Type*) [Fintype R] [DecidableEq R]
    (A : Matrix (I × R) (I × R) ℂ) :
    amplify (canonicalCompletion Φ) R A = ∑ q : (I × O) ⊕ I,
      (canonicalCompletionKraus Φ q ⊗ₖ (1 : Matrix R R ℂ)) * A *
        (canonicalCompletionKraus Φ q ⊗ₖ (1 : Matrix R R ℂ))ᴴ :=
  amplify_krausMap_reconstruct (canonicalCompletionKraus Φ) R A

theorem canonicalCompletion_amplify_gram
    (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) (hΦ : CompletelyPositive Φ)
    (htrace : TraceNonincreasing Φ)
    (R : Type*) [Fintype R] [DecidableEq R] :
    ∑ q : (I × O) ⊕ I,
      (canonicalCompletionKraus Φ q ⊗ₖ (1 : Matrix R R ℂ))ᴴ *
        (canonicalCompletionKraus Φ q ⊗ₖ (1 : Matrix R R ℂ)) = 1 :=
  QuantumProver.ElegantJointMeasurement.Concurrence.kronecker_left_complete (canonicalCompletionKraus Φ)
    (canonicalCompletionKraus_gram Φ hΦ htrace)

theorem canonicalCompletion_amplify_posSemidef
    (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ)
    (R : Type*) [Fintype R] [DecidableEq R]
    {A : Matrix (I × R) (I × R) ℂ} (hA : A.PosSemidef) :
    (amplify (canonicalCompletion Φ) R A).PosSemidef :=
  amplify_posSemidef _ (canonicalCompletion_completelyPositive Φ) R hA

theorem canonicalCompletion_amplify_tracePreserving
    (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) (hΦ : CompletelyPositive Φ)
    (htrace : TraceNonincreasing Φ)
    (R : Type*) [Fintype R] [DecidableEq R]
    (A : Matrix (I × R) (I × R) ℂ) :
    (amplify (canonicalCompletion Φ) R A).trace = A.trace :=
  amplify_tracePreserving _ (canonicalCompletion_completelyPositive Φ)
    (canonicalCompletion_tracePreserving Φ hΦ htrace) R A

theorem canonicalCompletion_amplify_success
    (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) (hΦ : CompletelyPositive Φ)
    (htrace : TraceNonincreasing Φ)
    (R : Type*) [Fintype R] (A : Matrix (I × R) (I × R) ℂ) :
    (amplify (canonicalCompletion Φ) R A).submatrix
      (fun x : O × R => (Sum.inl x.1, x.2))
      (fun x : O × R => (Sum.inl x.1, x.2)) = amplify Φ R A := by
  ext ⟨o, r⟩ ⟨p, s⟩
  change canonicalCompletion Φ (Matrix.of (fun i j => A (i, r) (j, s)))
    (Sum.inl o) (Sum.inl p) = _
  rw [canonicalCompletion_action Φ hΦ htrace]
  rfl

theorem canonicalCompletion_amplify_failure
    (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) (hΦ : CompletelyPositive Φ)
    (htrace : TraceNonincreasing Φ)
    (R : Type*) [Fintype R] (A : Matrix (I × R) (I × R) ℂ) :
    (amplify (canonicalCompletion Φ) R A).submatrix
      (fun r : R => (Sum.inr (), r)) (fun r : R => (Sum.inr (), r)) =
      Matrix.of (fun r s =>
        (canonicalResidual Φ * Matrix.of (fun i j => A (i, r) (j, s))).trace) := by
  ext r s
  change canonicalCompletion Φ (Matrix.of (fun i j => A (i, r) (j, s)))
    (Sum.inr ()) (Sum.inr ()) = _
  rw [canonicalCompletion_action Φ hΦ htrace]
  simp

theorem canonicalCompletion_amplify_cross
    (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) (hΦ : CompletelyPositive Φ)
    (htrace : TraceNonincreasing Φ)
    (R : Type*) [Fintype R] (A : Matrix (I × R) (I × R) ℂ) :
    (amplify (canonicalCompletion Φ) R A).submatrix
      (fun x : O × R => (Sum.inl x.1, x.2)) (fun r : R => (Sum.inr (), r)) = 0 ∧
    (amplify (canonicalCompletion Φ) R A).submatrix
      (fun r : R => (Sum.inr (), r)) (fun x : O × R => (Sum.inl x.1, x.2)) = 0 := by
  constructor
  · ext ⟨o, r⟩ s
    change canonicalCompletion Φ (Matrix.of (fun i j => A (i, r) (j, s)))
      (Sum.inl o) (Sum.inr ()) = 0
    rw [canonicalCompletion_action Φ hΦ htrace]
    rfl
  · ext r ⟨o, s⟩
    change canonicalCompletion Φ (Matrix.of (fun i j => A (i, r) (j, s)))
      (Sum.inr ()) (Sum.inl o) = 0
    rw [canonicalCompletion_action Φ hΦ htrace]
    rfl

theorem exists_flagged_cptp_completion
    (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) (hΦ : CompletelyPositive Φ)
    (htrace : TraceNonincreasing Φ) :
    ∃ Ψ : Matrix I I ℂ →ₗ[ℂ] Matrix (O ⊕ Unit) (O ⊕ Unit) ℂ,
      CompletelyPositive Ψ ∧ TracePreserving Ψ ∧
      (∀ A : Matrix I I ℂ,
        Ψ A = Matrix.fromBlocks (Φ A) (0 : Matrix O Unit ℂ) (0 : Matrix Unit O ℂ)
          ((canonicalResidual Φ * A).trace • (1 : Matrix Unit Unit ℂ))) :=
  ⟨canonicalCompletion Φ, canonicalCompletion_completelyPositive Φ,
    canonicalCompletion_tracePreserving Φ hΦ htrace,
    canonicalCompletion_action Φ hΦ htrace⟩

theorem map_eq_zero_of_isEmpty_output [IsEmpty O]
    (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) : Φ = 0 := by
  apply LinearMap.ext
  intro A
  exact Subsingleton.elim _ _

theorem canonicalGram_eq_zero_of_isEmpty_output [IsEmpty O]
    (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) : canonicalGram Φ = 0 := by
  simp [canonicalGram]

theorem cptni_of_isEmpty_output [IsEmpty O]
    (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) :
    CompletelyPositive Φ ∧ TraceNonincreasing Φ := by
  constructor
  · intro r A hA
    have hz : amplify Φ (Fin r) A = 0 := Subsingleton.elim _ _
    rw [hz]
    exact Matrix.PosSemidef.zero
  · intro A hA
    rw [map_eq_zero_of_isEmpty_output Φ]
    simpa using hA.trace_nonneg

theorem canonicalCompletion_action_of_isEmpty_output [IsEmpty O]
    (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) (A : Matrix I I ℂ) :
    canonicalCompletion Φ A =
      Matrix.fromBlocks (0 : Matrix O O ℂ) (0 : Matrix O Unit ℂ)
        (0 : Matrix Unit O ℂ) (A.trace • (1 : Matrix Unit Unit ℂ)) := by
  rw [canonicalCompletion_action Φ (cptni_of_isEmpty_output Φ).1
    (cptni_of_isEmpty_output Φ).2]
  rw [canonicalResidual, canonicalGram_eq_zero_of_isEmpty_output Φ,
    sub_zero, Matrix.one_mul]
  simp [map_eq_zero_of_isEmpty_output Φ]

theorem canonicalCompletion_eq_zero_of_isEmpty_input [IsEmpty I]
    (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) : canonicalCompletion Φ = 0 :=
  map_eq_zero_of_isEmpty_input _

end QuantumProver.SuperchannelDiscrimination.CPTPKraus

namespace QuantumProver.SuperchannelDiscrimination.CPTPKraus

variable {I O : Type*} [Fintype I] [Fintype O]
  [DecidableEq I] [DecidableEq O]

def choi (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) :
    Matrix (I × O) (I × O) ℂ := QuantumProver.ElegantJointMeasurement.CP.choi Φ

theorem choiFactor_mul_conjTranspose_of_posSemidef
    (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) (hJ : (choi Φ).PosSemidef) :
    QuantumProver.ElegantJointMeasurement.CP.choiFactor Φ * (QuantumProver.ElegantJointMeasurement.CP.choiFactor Φ)ᴴ = choi Φ := by
  have hs : (QuantumProver.ElegantJointMeasurement.CP.choiFactor Φ)ᴴ = QuantumProver.ElegantJointMeasurement.CP.choiFactor Φ :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (choi Φ))).isHermitian
  rw [hs, ← pow_two]
  exact CFC.sq_sqrt (choi Φ) hJ.nonneg

theorem canonicalKraus_matrix_unit_of_choi_posSemidef
    (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) (hJ : (choi Φ).PosSemidef) (i j : I) :
    QuantumProver.ElegantJointMeasurement.CP.krausMap (canonicalKraus Φ) (Matrix.single i j 1) =
      Φ (Matrix.single i j 1) := by
  ext o p
  change (∑ q : I × O, canonicalKraus Φ q * Matrix.single i j (1 : ℂ) *
    (canonicalKraus Φ q)ᴴ) o p = _
  simp only [Matrix.sum_apply, QuantumProver.ElegantJointMeasurement.CP.kraus_matrix_unit, canonicalKraus,
    QuantumProver.ElegantJointMeasurement.CP.krausOperator]
  change (QuantumProver.ElegantJointMeasurement.CP.choiFactor Φ * (QuantumProver.ElegantJointMeasurement.CP.choiFactor Φ)ᴴ) (i, o) (j, p) = choi Φ (i, o) (j, p)
  rw [choiFactor_mul_conjTranspose_of_posSemidef Φ hJ]

theorem canonicalKraus_reconstruct_map_of_choi_posSemidef
    (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) (hJ : (choi Φ).PosSemidef) :
    Φ = QuantumProver.ElegantJointMeasurement.CP.krausMap (canonicalKraus Φ) :=
  QuantumProver.ElegantJointMeasurement.CP.linearMap_eq_of_matrix_units Φ _
    (fun i j => (canonicalKraus_matrix_unit_of_choi_posSemidef Φ hJ i j).symm)

theorem choi_posSemidef_iff_completelyPositive
    (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) :
    (choi Φ).PosSemidef ↔ CompletelyPositive Φ := by
  constructor
  · intro hJ
    have heq := canonicalKraus_reconstruct_map_of_choi_posSemidef Φ hJ
    have hK : CompletelyPositive (QuantumProver.ElegantJointMeasurement.CP.krausMap (canonicalKraus Φ)) :=
      (completelyPositive_iff_EJMCP _).mpr (QuantumProver.ElegantJointMeasurement.CP.krausMap_completelyPositive _)
    exact Eq.mpr (congrArg CompletelyPositive heq) hK
  · intro hΦ
    exact QuantumProver.ElegantJointMeasurement.CP.choi_posSemidef Φ (completelyPositive_to_EJMCP hΦ)

theorem choi_difference (Φ Ψ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) (z : ℂ) :
    choi (z • Ψ - Φ) = z • choi Ψ - choi Φ := by
  ext x y
  rfl

def CPDom (Φ Ψ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) (c : ℝ) : Prop :=
  CompletelyPositive ((c : ℂ) • Ψ - Φ)

theorem choi_map_difference_posSemidef_iff_cpDom
    (Φ Ψ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) (c : ℝ) :
    (choi ((c : ℂ) • Ψ - Φ)).PosSemidef ↔ CPDom Φ Ψ c :=
  choi_posSemidef_iff_completelyPositive _

theorem choi_cp_order_iff
    (Φ Ψ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) (c : ℝ) :
    ((c : ℂ) • choi Ψ - choi Φ).PosSemidef ↔ CPDom Φ Ψ c := by
  rw [← choi_difference]
  exact choi_map_difference_posSemidef_iff_cpDom Φ Ψ c

def choiInputMarginal (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) : Matrix I I ℂ :=
  Matrix.of (fun i j => ∑ o : O, choi Φ (i, o) (j, o))

theorem canonicalGram_transpose_eq_choiInputMarginal
    (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) (hΦ : CompletelyPositive Φ) :
    (canonicalGram Φ)ᵀ = choiInputMarginal Φ := by
  ext i j
  change canonicalGram Φ j i = ∑ o : O, Φ (Matrix.single i j 1) o o
  calc
    canonicalGram Φ j i = (canonicalGram Φ * Matrix.single i j 1).trace := by
      simp [Matrix.trace_mul_single]
    _ = (Φ (Matrix.single i j 1)).trace := (canonicalKraus_trace Φ hΦ _).symm
    _ = _ := rfl

theorem canonicalResidual_transpose_eq_choiInputDefect
    (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) (hΦ : CompletelyPositive Φ) :
    (canonicalResidual Φ)ᵀ = 1 - choiInputMarginal Φ := by
  rw [canonicalResidual, Matrix.transpose_sub, Matrix.transpose_one,
    canonicalGram_transpose_eq_choiInputMarginal Φ hΦ]

theorem trace_pairing_nonneg {H A : Matrix I I ℂ}
    (hH : H.PosSemidef) (hA : A.PosSemidef) : 0 ≤ (H * A).trace := by
  have hs : (CFC.sqrt H).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg H)
  have ht : (CFC.sqrt H * A * (CFC.sqrt H)ᴴ).trace = (H * A).trace := by
    rw [Matrix.trace_mul_cycle, hs.isHermitian.eq, CFC.sqrt_mul_sqrt_self H hH.nonneg]
  have h := (hA.mul_mul_conjTranspose_same (CFC.sqrt H)).trace_nonneg
  rwa [ht] at h

theorem traceNonincreasing_of_canonicalResidual_posSemidef
    (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) (hΦ : CompletelyPositive Φ)
    (hH : (canonicalResidual Φ).PosSemidef) : TraceNonincreasing Φ := by
  intro A hA
  have h := trace_pairing_nonneg hH hA
  rw [canonicalResidual_trace Φ hΦ] at h
  exact sub_nonneg.mp h

theorem traceNonincreasing_iff_canonicalResidual_posSemidef
    (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) (hΦ : CompletelyPositive Φ) :
    TraceNonincreasing Φ ↔ (canonicalResidual Φ).PosSemidef :=
  ⟨canonicalResidual_posSemidef Φ hΦ,
    traceNonincreasing_of_canonicalResidual_posSemidef Φ hΦ⟩

theorem traceNonincreasing_iff_choiInputDefect_posSemidef
    (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) (hΦ : CompletelyPositive Φ) :
    TraceNonincreasing Φ ↔ (1 - choiInputMarginal Φ).PosSemidef := by
  constructor
  · intro htrace
    have h := (canonicalResidual_posSemidef Φ hΦ htrace).transpose
    rwa [canonicalResidual_transpose_eq_choiInputDefect Φ hΦ] at h
  · intro hM
    apply traceNonincreasing_of_canonicalResidual_posSemidef Φ hΦ
    apply Matrix.posSemidef_transpose_iff.mp
    rwa [canonicalResidual_transpose_eq_choiInputDefect Φ hΦ]

theorem traceNonincreasing_iff_choiInputMarginal_le_one
    (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) (hΦ : CompletelyPositive Φ) :
    TraceNonincreasing Φ ↔ choiInputMarginal Φ ≤ 1 := by
  rw [traceNonincreasing_iff_choiInputDefect_posSemidef Φ hΦ]
  constructor
  · intro h
    exact sub_nonneg.mp h.nonneg
  · intro h
    exact Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr h)

theorem choi_cptni_iff
    (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) :
    ((choi Φ).PosSemidef ∧ choiInputMarginal Φ ≤ 1) ↔
      (CompletelyPositive Φ ∧ TraceNonincreasing Φ) := by
  constructor
  · intro h
    have hΦ := (choi_posSemidef_iff_completelyPositive Φ).mp h.1
    exact ⟨hΦ, (traceNonincreasing_iff_choiInputMarginal_le_one Φ hΦ).mpr h.2⟩
  · intro h
    exact ⟨(choi_posSemidef_iff_completelyPositive Φ).mpr h.1,
      (traceNonincreasing_iff_choiInputMarginal_le_one Φ h.1).mp h.2⟩

theorem tracePreserving_iff_choiInputMarginal_eq_one
    (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) (hΦ : CompletelyPositive Φ) :
    TracePreserving Φ ↔ choiInputMarginal Φ = 1 := by
  constructor
  · intro htrace
    have hG : canonicalGram Φ = 1 := canonicalKraus_gram Φ hΦ htrace
    rw [← canonicalGram_transpose_eq_choiInputMarginal Φ hΦ, hG, Matrix.transpose_one]
  · intro hM
    have hG : canonicalGram Φ = 1 := by
      have h : (canonicalGram Φ)ᵀ = 1 := by
        rw [canonicalGram_transpose_eq_choiInputMarginal Φ hΦ]
        exact hM
      have ht := congrArg Matrix.transpose h
      simpa using ht
    intro A
    rw [canonicalKraus_trace Φ hΦ, hG, Matrix.one_mul]

theorem choi_cptp_iff
    (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) :
    ((choi Φ).PosSemidef ∧ choiInputMarginal Φ = 1) ↔
      (CompletelyPositive Φ ∧ TracePreserving Φ) := by
  constructor
  · intro h
    have hΦ := (choi_posSemidef_iff_completelyPositive Φ).mp h.1
    exact ⟨hΦ, (tracePreserving_iff_choiInputMarginal_eq_one Φ hΦ).mpr h.2⟩
  · intro h
    exact ⟨(choi_posSemidef_iff_completelyPositive Φ).mpr h.1,
      (tracePreserving_iff_choiInputMarginal_eq_one Φ h.1).mp h.2⟩

theorem choi_eq_zero_of_isEmpty_input [IsEmpty I]
    (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) : choi Φ = 0 :=
  Subsingleton.elim _ _

theorem choi_eq_zero_of_isEmpty_output [IsEmpty O]
    (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) : choi Φ = 0 :=
  Subsingleton.elim _ _

theorem choiInputMarginal_eq_zero_of_isEmpty_input [IsEmpty I]
    (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) : choiInputMarginal Φ = 0 :=
  Subsingleton.elim _ _

theorem choiInputMarginal_eq_zero_of_isEmpty_output [IsEmpty O]
    (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) : choiInputMarginal Φ = 0 := by
  ext i j
  simp [choiInputMarginal]

theorem choi_cptni_of_isEmpty_output [IsEmpty O]
    (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) :
    (choi Φ).PosSemidef ∧ choiInputMarginal Φ ≤ 1 :=
  (choi_cptni_iff Φ).mpr (cptni_of_isEmpty_output Φ)

theorem choi_cptp_of_isEmpty_input [IsEmpty I]
    (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) :
    (choi Φ).PosSemidef ∧ choiInputMarginal Φ = 1 :=
  (choi_cptp_iff Φ).mpr (cptp_of_isEmpty_input Φ)

theorem not_choi_cptp_of_isEmpty_output [IsEmpty O] [Nonempty I]
    (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) :
    ¬ ((choi Φ).PosSemidef ∧ choiInputMarginal Φ = 1) := by
  intro h
  exact not_tracePreserving_of_isEmpty_output Φ ((choi_cptp_iff Φ).mp h).2

end QuantumProver.SuperchannelDiscrimination.CPTPKraus

namespace QuantumProver.SuperchannelDiscrimination.CPTPKraus

variable {I O : Type*} [Fintype I] [Fintype O]
  [DecidableEq I] [DecidableEq O]

def fromChoi (J : Matrix (I × O) (I × O) ℂ) :
    Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ where
  toFun A := Matrix.of (fun o p => ∑ i : I, ∑ j : I, A i j * J (i, o) (j, p))
  map_add' A B := by
    ext o p
    change (∑ i : I, ∑ j : I, (A i j + B i j) * J (i, o) (j, p)) =
      (∑ i : I, ∑ j : I, A i j * J (i, o) (j, p)) +
        (∑ i : I, ∑ j : I, B i j * J (i, o) (j, p))
    simp only [add_mul, Finset.sum_add_distrib]
  map_smul' z A := by
    ext o p
    change (∑ i : I, ∑ j : I, (z * A i j) * J (i, o) (j, p)) =
      z * (∑ i : I, ∑ j : I, A i j * J (i, o) (j, p))
    simp only [mul_assoc, Finset.mul_sum]

theorem fromChoi_apply (J : Matrix (I × O) (I × O) ℂ)
    (A : Matrix I I ℂ) (o p : O) :
    fromChoi J A o p = ∑ i : I, ∑ j : I, A i j * J (i, o) (j, p) := rfl

theorem fromChoi_matrix_unit (J : Matrix (I × O) (I × O) ℂ) (i j : I) :
    fromChoi J (Matrix.single i j 1) = Matrix.of (fun o p => J (i, o) (j, p)) := by
  ext o p
  change (∑ a : I, ∑ b : I, Matrix.single i j (1 : ℂ) a b * J (a, o) (b, p)) = _
  simp [Matrix.single_apply, ite_and]

theorem choi_fromChoi (J : Matrix (I × O) (I × O) ℂ) :
    choi (fromChoi J) = J := by
  ext ⟨i, o⟩ ⟨j, p⟩
  change fromChoi J (Matrix.single i j 1) o p = J (i, o) (j, p)
  rw [fromChoi_matrix_unit]
  rfl

theorem fromChoi_choi (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) :
    fromChoi (choi Φ) = Φ := by
  apply QuantumProver.ElegantJointMeasurement.CP.linearMap_eq_of_matrix_units
  intro i j
  ext o p
  exact congrArg (fun M : Matrix (I × O) (I × O) ℂ => M (i, o) (j, p))
    (choi_fromChoi (choi Φ))

def choiMatrixInputMarginal (J : Matrix (I × O) (I × O) ℂ) : Matrix I I ℂ :=
  Matrix.of (fun i j => ∑ o : O, J (i, o) (j, o))

theorem choiInputMarginal_fromChoi (J : Matrix (I × O) (I × O) ℂ) :
    choiInputMarginal (fromChoi J) = choiMatrixInputMarginal J := by
  ext i j
  change (∑ o : O, choi (fromChoi J) (i, o) (j, o)) = ∑ o : O, J (i, o) (j, o)
  rw [choi_fromChoi]

theorem fromChoi_completelyPositive (J : Matrix (I × O) (I × O) ℂ)
    (hJ : J.PosSemidef) : CompletelyPositive (fromChoi J) := by
  apply (choi_posSemidef_iff_completelyPositive (fromChoi J)).mp
  rwa [choi_fromChoi]

theorem fromChoi_cptni_iff (J : Matrix (I × O) (I × O) ℂ) :
    (J.PosSemidef ∧ choiMatrixInputMarginal J ≤ 1) ↔
      (CompletelyPositive (fromChoi J) ∧ TraceNonincreasing (fromChoi J)) := by
  simpa only [choi_fromChoi, choiInputMarginal_fromChoi] using
    (choi_cptni_iff (fromChoi J))

theorem fromChoi_cptp_iff (J : Matrix (I × O) (I × O) ℂ) :
    (J.PosSemidef ∧ choiMatrixInputMarginal J = 1) ↔
      (CompletelyPositive (fromChoi J) ∧ TracePreserving (fromChoi J)) := by
  simpa only [choi_fromChoi, choiInputMarginal_fromChoi] using
    (choi_cptp_iff (fromChoi J))

theorem fromChoi_traceNonincreasing (J : Matrix (I × O) (I × O) ℂ)
    (hJ : J.PosSemidef) (hM : choiMatrixInputMarginal J ≤ 1) :
    TraceNonincreasing (fromChoi J) := ((fromChoi_cptni_iff J).mp ⟨hJ, hM⟩).2

theorem fromChoi_tracePreserving (J : Matrix (I × O) (I × O) ℂ)
    (hJ : J.PosSemidef) (hM : choiMatrixInputMarginal J = 1) :
    TracePreserving (fromChoi J) := ((fromChoi_cptp_iff J).mp ⟨hJ, hM⟩).2

theorem fromChoi_cp_order_iff (J : Matrix (I × O) (I × O) ℂ)
    (Ψ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) (c : ℝ) :
    ((c : ℂ) • choi Ψ - J).PosSemidef ↔ CPDom (fromChoi J) Ψ c := by
  simpa only [choi_fromChoi] using (choi_cp_order_iff (fromChoi J) Ψ c)

theorem exists_cptni_map_of_choi (J : Matrix (I × O) (I × O) ℂ)
    (hJ : J.PosSemidef) (hM : choiMatrixInputMarginal J ≤ 1) :
    ∃ Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ,
      choi Φ = J ∧ CompletelyPositive Φ ∧ TraceNonincreasing Φ :=
  ⟨fromChoi J, choi_fromChoi J, fromChoi_completelyPositive J hJ,
    fromChoi_traceNonincreasing J hJ hM⟩

theorem exists_cptp_map_of_choi (J : Matrix (I × O) (I × O) ℂ)
    (hJ : J.PosSemidef) (hM : choiMatrixInputMarginal J = 1) :
    ∃ Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ,
      choi Φ = J ∧ CompletelyPositive Φ ∧ TracePreserving Φ :=
  ⟨fromChoi J, choi_fromChoi J, fromChoi_completelyPositive J hJ,
    fromChoi_tracePreserving J hJ hM⟩

theorem exists_dominated_cptni_map_of_choi
    (J : Matrix (I × O) (I × O) ℂ)
    (Ψ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) (c : ℝ)
    (hJ : J.PosSemidef) (hM : choiMatrixInputMarginal J ≤ 1)
    (hcap : ((c : ℂ) • choi Ψ - J).PosSemidef) :
    ∃ Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ,
      choi Φ = J ∧ CompletelyPositive Φ ∧ TraceNonincreasing Φ ∧ CPDom Φ Ψ c :=
  ⟨fromChoi J, choi_fromChoi J, fromChoi_completelyPositive J hJ,
    fromChoi_traceNonincreasing J hJ hM, (fromChoi_cp_order_iff J Ψ c).mp hcap⟩

theorem fromChoi_canonicalKraus_apply (J : Matrix (I × O) (I × O) ℂ)
    (q : I × O) (o : O) (i : I) :
    canonicalKraus (fromChoi J) q o i = CFC.sqrt J (i, o) q := by
  rw [canonicalKraus_apply]
  change CFC.sqrt (choi (fromChoi J)) (i, o) q = CFC.sqrt J (i, o) q
  rw [choi_fromChoi]

theorem fromChoi_canonicalKraus_reconstruct (J : Matrix (I × O) (I × O) ℂ)
    (hJ : J.PosSemidef) (A : Matrix I I ℂ) :
    fromChoi J A = ∑ q : I × O,
      canonicalKraus (fromChoi J) q * A * (canonicalKraus (fromChoi J) q)ᴴ :=
  canonicalKraus_reconstruct _ (fromChoi_completelyPositive J hJ) A

theorem fromChoi_canonicalGram_le_one (J : Matrix (I × O) (I × O) ℂ)
    (hJ : J.PosSemidef) (hM : choiMatrixInputMarginal J ≤ 1) :
    canonicalGram (fromChoi J) ≤ 1 :=
  canonicalGram_le_one _ (fromChoi_completelyPositive J hJ)
    (fromChoi_traceNonincreasing J hJ hM)

theorem fromChoi_canonicalKraus_gram (J : Matrix (I × O) (I × O) ℂ)
    (hJ : J.PosSemidef) (hM : choiMatrixInputMarginal J = 1) :
    ∑ q : I × O,
      (canonicalKraus (fromChoi J) q)ᴴ * canonicalKraus (fromChoi J) q = 1 :=
  canonicalKraus_gram _ (fromChoi_completelyPositive J hJ)
    (fromChoi_tracePreserving J hJ hM)

theorem fromChoi_amplify_reconstruct (J : Matrix (I × O) (I × O) ℂ)
    (hJ : J.PosSemidef) (R : Type*) [Fintype R] [DecidableEq R]
    (A : Matrix (I × R) (I × R) ℂ) :
    amplify (fromChoi J) R A = ∑ q : I × O,
      stabilizedKraus (fromChoi J) R q * A * (stabilizedKraus (fromChoi J) R q)ᴴ :=
  canonicalKraus_amplify_reconstruct _ (fromChoi_completelyPositive J hJ) R A

theorem fromChoi_amplify_posSemidef (J : Matrix (I × O) (I × O) ℂ)
    (hJ : J.PosSemidef) (R : Type*) [Fintype R] [DecidableEq R]
    {A : Matrix (I × R) (I × R) ℂ} (hA : A.PosSemidef) :
    (amplify (fromChoi J) R A).PosSemidef :=
  amplify_posSemidef _ (fromChoi_completelyPositive J hJ) R hA

theorem amplify_traceNonincreasing
    (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) (htrace : TraceNonincreasing Φ)
    (R : Type*) [Fintype R] {A : Matrix (I × R) (I × R) ℂ}
    (hA : A.PosSemidef) : (amplify Φ R A).trace ≤ A.trace := by
  calc
    (amplify Φ R A).trace =
        ∑ r : R, (Φ (fun i j => A (i, r) (j, r))).trace := by
      simp only [amplify, Matrix.trace, Matrix.diag, Fintype.sum_prod_type]
      exact Finset.sum_comm
    _ ≤ ∑ r : R, Matrix.trace ((fun i j => A (i, r) (j, r)) : Matrix I I ℂ) := by
      exact Finset.sum_le_sum fun r _ => htrace _ (hA.submatrix (fun i : I => (i, r)))
    _ = A.trace := by
      simp only [Matrix.trace, Matrix.diag, Fintype.sum_prod_type]
      exact Finset.sum_comm

theorem fromChoi_amplify_traceNonincreasing (J : Matrix (I × O) (I × O) ℂ)
    (hJ : J.PosSemidef) (hM : choiMatrixInputMarginal J ≤ 1)
    (R : Type*) [Fintype R] {A : Matrix (I × R) (I × R) ℂ}
    (hA : A.PosSemidef) : (amplify (fromChoi J) R A).trace ≤ A.trace :=
  amplify_traceNonincreasing _ (fromChoi_traceNonincreasing J hJ hM) R hA

theorem fromChoi_amplify_tracePreserving (J : Matrix (I × O) (I × O) ℂ)
    (hJ : J.PosSemidef) (hM : choiMatrixInputMarginal J = 1)
    (R : Type*) [Fintype R] [DecidableEq R]
    (A : Matrix (I × R) (I × R) ℂ) :
    (amplify (fromChoi J) R A).trace = A.trace :=
  amplify_tracePreserving _ (fromChoi_completelyPositive J hJ)
    (fromChoi_tracePreserving J hJ hM) R A

theorem fromChoi_eq_zero_of_isEmpty_input [IsEmpty I]
    (J : Matrix (I × O) (I × O) ℂ) : fromChoi J = 0 :=
  map_eq_zero_of_isEmpty_input _

theorem fromChoi_eq_zero_of_isEmpty_output [IsEmpty O]
    (J : Matrix (I × O) (I × O) ℂ) : fromChoi J = 0 :=
  map_eq_zero_of_isEmpty_output _

theorem choiMatrixInputMarginal_eq_zero_of_isEmpty_input [IsEmpty I]
    (J : Matrix (I × O) (I × O) ℂ) : choiMatrixInputMarginal J = 0 :=
  Subsingleton.elim _ _

theorem choiMatrixInputMarginal_eq_zero_of_isEmpty_output [IsEmpty O]
    (J : Matrix (I × O) (I × O) ℂ) : choiMatrixInputMarginal J = 0 := by
  ext i j
  simp [choiMatrixInputMarginal]

end QuantumProver.SuperchannelDiscrimination.CPTPKraus

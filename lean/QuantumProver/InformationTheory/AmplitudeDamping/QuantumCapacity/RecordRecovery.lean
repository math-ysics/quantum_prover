import QuantumProver.InformationTheory.AmplitudeDamping.QuantumCapacity.RecordTypes

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder Matrix Kronecker

namespace QuantumProver.AmplitudeDamping.FiniteModel

section RecordedPhysicalCompleteness

variable (n : ℕ) (p : ℝ) (A B : Type*) [Fintype A] [Fintype B]
  [DecidableEq A] [DecidableEq B]

theorem recordCopyLabC_complete :
    (recordCopyLabC n A B)ᴴ * recordCopyLabC n A B = 1 := by
  simp only [recordCopyLabC, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
    ← Matrix.mul_kronecker_mul, recordCopyMemoryC_complete, Matrix.one_mul,
    Matrix.one_kronecker_one]

theorem recordedPhysicalKrausC_complete (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ∑ L, (recordedPhysicalKrausC n p A B L)ᴴ * recordedPhysicalKrausC n p A B L = 1 := by
  have hK : ∑ L, (tensorDampingKrausB n p L)ᴴ * tensorDampingKrausB n p L = 1 := by
    simpa only [physicalTensorKrausB_eq_damping] using physicalTensorKrausB_complete n p hp0 hp1
  simp only [recordedPhysicalKrausC, Matrix.conjTranspose_mul]
  calc
    _ = (recordCopyLabC n A B)ᴴ *
        (∑ L, (transferLabKrausC (A := A × Finset (Fin n)) (B := B)
          (tensorDampingKrausB n p) L)ᴴ *
          transferLabKrausC (A := A × Finset (Fin n)) (B := B)
            (tensorDampingKrausB n p) L) * recordCopyLabC n A B := by
      simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_assoc]
    _ = 1 := by rw [transferLabKrausC_complete _ hK, Matrix.mul_one, recordCopyLabC_complete]

theorem recordedOutputC_posSemidef
    {ρ : Matrix ((A × Finset (Fin n)) × B) ((A × Finset (Fin n)) × B) ℂ}
    (hρ : ρ.PosSemidef) : (recordedOutputC n p A B ρ).PosSemidef :=
  krausSumB_posSemidef _ hρ

theorem recordedOutputC_trace (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (ρ : Matrix ((A × Finset (Fin n)) × B) ((A × Finset (Fin n)) × B) ℂ) :
    (recordedOutputC n p A B ρ).trace = ρ.trace :=
  krausSumB_trace_preserving _ (recordedPhysicalKrausC_complete n p A B hp0 hp1) ρ

theorem recordedOutputC_isDensity (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {ρ : Matrix ((A × Finset (Fin n)) × B) ((A × Finset (Fin n)) × B) ℂ}
    (hρ : IsDensity ρ) : IsDensity (recordedOutputC n p A B ρ) :=
  ⟨krausSumB_posSemidef _ hρ.1,
    (krausSumB_trace_preserving _ (recordedPhysicalKrausC_complete n p A B hp0 hp1) ρ).trans hρ.2⟩

theorem recordWeightOutputC_family :
    QuantumProver.SuperchannelDiscrimination.Pinching.IsProjectionFamily
      (fun w : Fin (n + 1) => recordWeightOutputC n w.val A B) := by
  have hself (w : Fin (n + 1)) : (weightProjectionC n w.val)ᴴ =
      weightProjectionC n w.val := ((weightProjectionC_family n).selfAdjoint w).eq
  constructor
  · intro w
    change (recordWeightOutputC n w.val A B)ᴴ = recordWeightOutputC n w.val A B
    simp only [recordWeightOutputC, recordWeightMemoryC, Matrix.conjTranspose_kronecker,
      Matrix.conjTranspose_one, hself]
  · intro w
    simp only [recordWeightOutputC, recordWeightMemoryC, ← Matrix.mul_kronecker_mul,
      Matrix.one_mul, (weightProjectionC_family n).idempotent]
  · intro w v hwv
    simp only [recordWeightOutputC, recordWeightMemoryC, ← Matrix.mul_kronecker_mul,
      Matrix.one_mul, (weightProjectionC_family n).orthogonal w v hwv,
      Matrix.kronecker_zero, Matrix.zero_kronecker]
  · calc
      _ = ((1 : Matrix A A ℂ) ⊗ₖ
          (∑ w : Fin (n + 1), weightProjectionC n w.val)) ⊗ₖ
          (1 : Matrix (Finset (Fin n) × B) (Finset (Fin n) × B) ℂ) := by
        ext x y
        simp [Matrix.sum_apply, recordWeightOutputC, recordWeightMemoryC,
          Finset.mul_sum, Finset.sum_mul]
      _ = 1 := by rw [(weightProjectionC_family n).complete,
        Matrix.one_kronecker_one, Matrix.one_kronecker_one]

theorem recordWeightOutputC_complete :
    ∑ w : Fin (n + 1), (recordWeightOutputC n w.val A B)ᴴ *
      recordWeightOutputC n w.val A B = 1 := by
  have hgram (w : Fin (n + 1)) : (recordWeightOutputC n w.val A B)ᴴ *
      recordWeightOutputC n w.val A B = recordWeightOutputC n w.val A B := by
    rw [((recordWeightOutputC_family n A B).selfAdjoint w).eq,
      (recordWeightOutputC_family n A B).idempotent]
  simpa only [hgram] using (recordWeightOutputC_family n A B).complete

theorem pinchedRecordedOutputC_eq_pinchingMap
    (ρ : Matrix ((A × Finset (Fin n)) × B) ((A × Finset (Fin n)) × B) ℂ) :
    pinchedRecordedOutputC n p A B ρ =
      QuantumProver.SuperchannelDiscrimination.Pinching.pinchingMap
        (fun w : Fin (n + 1) => recordWeightOutputC n w.val A B)
        (recordedOutputC n p A B ρ) := rfl

theorem pinchedRecordedOutputC_isDensity (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {ρ : Matrix ((A × Finset (Fin n)) × B) ((A × Finset (Fin n)) × B) ℂ}
    (hρ : IsDensity ρ) : IsDensity (pinchedRecordedOutputC n p A B ρ) := by
  refine ⟨krausSumB_posSemidef _ (recordedOutputC_posSemidef n p A B hρ.1), ?_⟩
  rw [pinchedRecordedOutputC, krausSumB_trace_preserving _ (recordWeightOutputC_complete n A B),
    recordedOutputC_trace n p A B hp0 hp1, hρ.2]

end RecordedPhysicalCompleteness

section HonestRecordRecovery

variable (n : ℕ) (p : ℝ) (A B : Type*) [Fintype A] [Fintype B]
  [DecidableEq A] [DecidableEq B]

theorem recordCopyLabC_eq_basis : recordCopyLabC n A B =
    basisEmbeddingC (fun y : (A × Finset (Fin n)) × B => ((y.1, y.1.2), y.2)) := by
  rw [recordCopyLabC, recordCopyMemoryC, ← basisEmbeddingC_id, basisEmbeddingC_kronecker]
  rfl

theorem recordedPhysicalKrausC_entry (L U T S : Finset (Fin n))
    (a c : A) (b d : B) :
    recordedPhysicalKrausC n p A B L ((a, U), (T, b)) ((c, S), d) =
      tensorDampingKrausB n p L T S * (if a = c ∧ U = S ∧ b = d then 1 else 0) := by
  rw [recordedPhysicalKrausC, recordCopyLabC_eq_basis, basisEmbeddingC_mul_entry,
    transferLabKrausC_entry]
  simp only [Prod.mk.injEq, and_assoc]

theorem recordedPhysicalKrausC_eq_reference (L : Finset (Fin n)) :
    recordedPhysicalKrausC n p A B L =
      (referenceKrausB (fun _ : Unit =>
        ((1 : Matrix (Finset (Fin n)) (Finset (Fin n)) ℂ) ⊗ₖ physicalTensorKrausB n p L) *
          fullRecordCopyB n) (A × B) ()).submatrix
        (recordPortMemoryEquivB (Finset (Fin n)) A B)
        (inputPortMemoryEquivB (Finset (Fin n)) A B) := by
  ext ⟨⟨a, U⟩, ⟨T, b⟩⟩ ⟨⟨c, S⟩, d⟩
  rw [recordedPhysicalKrausC_entry]
  change tensorDampingKrausB n p L T S *
      (if a = c ∧ U = S ∧ b = d then 1 else 0) =
    (((1 : Matrix (Finset (Fin n)) (Finset (Fin n)) ℂ) ⊗ₖ
      physicalTensorKrausB n p L) * fullRecordCopyB n) (U, T) S *
      (1 : Matrix (A × B) (A × B) ℂ) (a, b) (c, d)
  rw [fullRecordCopyB_mul_entry]
  change _ = ((1 : Matrix (Finset (Fin n)) (Finset (Fin n)) ℂ) U S *
    physicalTensorKrausB n p L T S) *
      (1 : Matrix (A × B) (A × B) ℂ) (a, b) (c, d)
  rw [physicalTensorKrausB_eq_damping]
  by_cases ha : a = c <;> by_cases hU : U = S <;> by_cases hb : b = d <;>
    simp [Matrix.one_apply, ha, hU, hb]

theorem recordedPhysicalKrausC_corrected (z : Fin n → ZMod 3) (L : Finset (Fin n)) :
    fullRecordLabCorrectionB n A B z * recordedPhysicalKrausC n p A B L =
      transferLabKrausC (A := A) (B := B) (fullRecordRecoveredKrausB n p) (z, L) := by
  rw [fullRecordLabCorrectionB_eq_reference, recordedPhysicalKrausC_eq_reference,
    Matrix.submatrix_mul_equiv]
  unfold transferLabKrausC
  simp only [referenceKrausB, ← Matrix.mul_kronecker_mul, Matrix.one_mul,
    fullRecordRecoveredKrausB, fullRecordCorrectedKrausB,
    fullRecordPhysicalKrausB, Matrix.mul_assoc]

theorem recordedOutputC_recovery
    (ρ : Matrix ((A × Finset (Fin n)) × B) ((A × Finset (Fin n)) × B) ℂ) :
    krausSumB (fullRecordLabCorrectionB n A B) (recordedOutputC n p A B ρ) =
      krausSumB (transferLabKrausC (A := A) (B := B) (tensorDampingKrausB n p)) ρ := by
  unfold recordedOutputC
  rw [krausSumB_compose]
  have hfamily : (fun h : (Fin n → ZMod 3) × Finset (Fin n) =>
      fullRecordLabCorrectionB n A B h.1 * recordedPhysicalKrausC n p A B h.2) =
      transferLabKrausC (A := A) (B := B) (fullRecordRecoveredKrausB n p) := by
    funext h
    exact recordedPhysicalKrausC_corrected n p A B h.1 h.2
  rw [hfamily, transferLabOutputC_eq_reference, fullRecordRecoveredChannelB_reference_eq]
  have hphysical : physicalTensorKrausB n p = tensorDampingKrausB n p :=
    funext (physicalTensorKrausB_eq_damping n p)
  rw [hphysical]
  exact (transferLabOutputC_eq_reference _ ρ).symm

theorem recordedOutputC_matrix_recovery
    (ρ : Matrix ((A × Finset (Fin n)) × B) ((A × Finset (Fin n)) × B) ℂ) :
    (fullRecordRecoveryProtocolB p n A B).output
      ((recordedOutputC n p A B ρ).submatrix
        (recordedOutputEquivC n A B) (recordedOutputEquivC n A B)) =
      labTransferOutput (tensorDampingKrausB n p) ρ := by
  rw [recordedOutputEquivC, fullRecordRecoveryProtocolB_output_reindex, recordedOutputC_recovery]
  exact (labTransferOutput_eq_transferLabC _ ρ).symm

end HonestRecordRecovery

section ActualRecoveredComparator

theorem krausSumB_compose_completeC {I J O Z Y : Type*}
    [Fintype I] [Fintype J] [Fintype O] [Fintype Z] [Fintype Y]
    [DecidableEq I] [DecidableEq J] [DecidableEq O]
    (K : Z → Matrix O J ℂ) (M : Y → Matrix J I ℂ)
    (hK : ∑ z, (K z)ᴴ * K z = 1) (hM : ∑ y, (M y)ᴴ * M y = 1) :
    ∑ h : Z × Y, (K h.1 * M h.2)ᴴ * (K h.1 * M h.2) = 1 := by
  apply krausSumB_complete_of_trace
  intro ρ
  rw [← krausSumB_compose, krausSumB_trace_preserving _ hK,
    krausSumB_trace_preserving _ hM]

variable (n : ℕ) (p : ℝ) (A B : Type*) [Fintype A] [Fintype B]
  [DecidableEq A] [DecidableEq B]

theorem fullRecordLabCorrectionB_completeC :
    ∑ z, (fullRecordLabCorrectionB n A B z)ᴴ * fullRecordLabCorrectionB n A B z = 1 := by
  have hgram (z : Fin n → ZMod 3) :
      (fullRecordLabCorrectionB n A B z)ᴴ * fullRecordLabCorrectionB n A B z =
        ((fullRecordMemoryBraB n A z)ᴴ * fullRecordMemoryBraB n A z) ⊗ₖ
          (1 : Matrix (Finset (Fin n) × B) (Finset (Fin n) × B) ℂ) := by
    have hunit : ((1 : Matrix A A ℂ) ⊗ₖ
          (fullPhaseDiagonalB n z ⊗ₖ (1 : Matrix B B ℂ)))ᴴ *
        ((1 : Matrix A A ℂ) ⊗ₖ (fullPhaseDiagonalB n z ⊗ₖ (1 : Matrix B B ℂ))) = 1 := by
      simp only [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
        ← Matrix.mul_kronecker_mul, Matrix.one_mul, fullPhaseDiagonalB_conjTranspose_mul,
        Matrix.one_kronecker_one]
    unfold fullRecordLabCorrectionB
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc ((1 : Matrix A A ℂ) ⊗ₖ
      (fullPhaseDiagonalB n z ⊗ₖ (1 : Matrix B B ℂ)))ᴴ, hunit, Matrix.one_mul]
    simp only [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
      ← Matrix.mul_kronecker_mul, Matrix.one_mul]
  simp only [hgram]
  calc
    _ = (∑ z, (fullRecordMemoryBraB n A z)ᴴ * fullRecordMemoryBraB n A z) ⊗ₖ
        (1 : Matrix (Finset (Fin n) × B) (Finset (Fin n) × B) ℂ) := by
      ext x y
      simp [Matrix.sum_apply, Finset.sum_mul]
    _ = 1 := by rw [fullRecordMemoryBraB_complete, Matrix.one_kronecker_one]

def recoveredPhaseLabKrausC :
    ((Fin n → ZMod 3) × (Σ w : Fin (n + 1), survivorPhaseLabelB n w.val)) →
      Matrix (A × (Finset (Fin n) × B)) ((A × Finset (Fin n)) × B) ℂ :=
  fun z => fullRecordLabCorrectionB n A B z.1 * phaseRecordedKrausC n p A B z.2

theorem recoveredPhaseLabKrausC_complete (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ∑ z, (recoveredPhaseLabKrausC n p A B z)ᴴ * recoveredPhaseLabKrausC n p A B z = 1 :=
  krausSumB_compose_completeC _ _ (fullRecordLabCorrectionB_completeC n A B)
    (phaseRecordedKrausC_complete n p A B hp0 hp1)

theorem recoveredPhaseOutputC_eq_krausSum
    (σ : Matrix ((A × Finset (Fin n)) × B) ((A × Finset (Fin n)) × B) ℂ) :
    recoveredPhaseOutputC n p A B σ =
      (krausSumB (recoveredPhaseLabKrausC n p A B) σ).submatrix
        ((finiteIndexB A).prodCongr (finiteIndexB (Finset (Fin n) × B)))
        ((finiteIndexB A).prodCongr (finiteIndexB (Finset (Fin n) × B))) := by
  rw [recoveredPhaseOutputC, recordedOutputEquivC, fullRecordRecoveryProtocolB_output_reindex,
    phaseRecordedOutputC, krausSumB_compose]
  rfl

end ActualRecoveredComparator

end QuantumProver.AmplitudeDamping.FiniteModel

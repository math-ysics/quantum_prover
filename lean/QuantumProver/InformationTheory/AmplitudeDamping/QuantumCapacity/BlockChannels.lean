import QuantumProver.InformationTheory.AmplitudeDamping.QuantumCapacity.RecordRecovery

set_option autoImplicit false
set_option maxHeartbeats 1200000

noncomputable section
open Matrix
open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder Matrix Kronecker

namespace QuantumProver.AmplitudeDamping.FiniteModel

theorem krausSumB_matrix_chart {I O Z I' O' Z' : Type*}
    [Fintype I] [Fintype O] [Fintype Z] [Fintype I'] [Fintype O'] [Fintype Z']
    [DecidableEq I] [DecidableEq O] [DecidableEq I'] [DecidableEq O']
    (eI : I' ≃ I) (eO : O' ≃ O) (eZ : Z' ≃ Z)
    (K : Z → Matrix O I ℂ) (ρ : Matrix I' I' ℂ) :
    krausSumB (fun z => (K (eZ z)).submatrix eO eI) ρ =
      (krausSumB K (ρ.submatrix eI.symm eI.symm)).submatrix eO eO := by
  have hInput : (ρ.submatrix eI.symm eI.symm).submatrix eI eI = ρ := by
    ext x y
    simp
  have h := krausSumB_submatrix_equiv eI eO eZ K (ρ.submatrix eI.symm eI.symm)
  rwa [hInput] at h

theorem krausSumB_matrix_chart_complete {I O Z I' O' Z' : Type*}
    [Fintype I] [Fintype O] [Fintype Z] [Fintype I'] [Fintype O'] [Fintype Z']
    [DecidableEq I] [DecidableEq O] [DecidableEq I'] [DecidableEq O']
    (eI : I' ≃ I) (eO : O' ≃ O) (eZ : Z' ≃ Z)
    (K : Z → Matrix O I ℂ) (hK : ∑ z, (K z)ᴴ * K z = 1) :
    ∑ z, ((K (eZ z)).submatrix eO eI)ᴴ * (K (eZ z)).submatrix eO eI = 1 := by
  apply krausSumB_complete_of_trace
  intro ρ
  rw [krausSumB_matrix_chart, TensorPower.trace_submatrix_equiv,
    krausSumB_trace_preserving _ hK, TensorPower.trace_submatrix_equiv]

theorem sepPositive_matrix_chart_iff {A B A' B' : Type*}
    [Fintype A] [Fintype B] [Fintype A'] [Fintype B']
    (eA : A' ≃ A) (eB : B' ≃ B) (ρ : Matrix (A × B) (A × B) ℂ) :
    SepPositive (ρ.submatrix (eA.prodCongr eB) (eA.prodCongr eB)) ↔ SepPositive ρ := by
  constructor
  · intro h
    have hBack := h.submatrix_local_equiv eA.symm eB.symm
    have hCancel : (ρ.submatrix (eA.prodCongr eB) (eA.prodCongr eB)).submatrix
        (eA.symm.prodCongr eB.symm) (eA.symm.prodCongr eB.symm) = ρ := by
      ext ⟨a, b⟩ ⟨c, d⟩
      simp
    rwa [hCancel] at hBack
  · intro h
    exact h.submatrix_local_equiv eA eB

def matrixBlockInputAliceEquiv (n a : ℕ) :
    Fin (doubleDimB n a) ≃ (Fin a × Finset (Fin n)) :=
  (inputQubitWordEquivB n a).trans
    (((subsetQubitWordEquivB n).symm.prodCongr (Equiv.refl (Fin a))).trans
      (Equiv.prodComm (Finset (Fin n)) (Fin a)))

def matrixBlockOutputBobEquiv (n b : ℕ) :
    Fin (doubleDimB n b) ≃ (Finset (Fin n) × Fin b) :=
  (outputQubitWordEquivB n b).trans
    ((subsetQubitWordEquivB n).symm.prodCongr (Equiv.refl (Fin b)))

def matrixBlockInputEquiv (n a b : ℕ) :
    (Fin (doubleDimB n a) × Fin b) ≃ ((Fin a × Finset (Fin n)) × Fin b) :=
  (matrixBlockInputAliceEquiv n a).prodCongr (Equiv.refl (Fin b))

def matrixBlockOutputEquiv (n a b : ℕ) :
    (Fin a × Fin (doubleDimB n b)) ≃ (Fin a × (Finset (Fin n) × Fin b)) :=
  (Equiv.refl (Fin a)).prodCongr (matrixBlockOutputBobEquiv n b)

theorem matrixBlockInputEquiv_trans_port (n a b : ℕ) :
    (matrixBlockInputEquiv n a b).trans
      (inputPortMemoryEquivB (Finset (Fin n)) (Fin a) (Fin b)) =
        sequentialInputEquivB n a b := by
  apply Equiv.ext
  intro x
  rfl

theorem matrixBlockOutputEquiv_trans_port (n a b : ℕ) :
    (matrixBlockOutputEquiv n a b).trans
      (outputPortMemoryEquivB (Finset (Fin n)) (Fin a) (Fin b)) =
        sequentialOutputEquivB n a b := by
  apply Equiv.ext
  intro x
  rfl

def matrixPhysicalBlockKraus (n : ℕ) (p : ℝ) (a b : ℕ) (L : Finset (Fin n)) :
    Matrix (Fin a × Fin (doubleDimB n b)) (Fin (doubleDimB n a) × Fin b) ℂ :=
  (transferLabKrausC (A := Fin a) (B := Fin b) (tensorDampingKrausB n p) L).submatrix
    (matrixBlockOutputEquiv n a b) (matrixBlockInputEquiv n a b)

theorem sequentialCallsKrausB_eq_matrix_block (n : ℕ) (p : ℝ) (a b : ℕ)
    (L : Finset (Fin n)) :
    sequentialCallsKrausB p n a b (subsetQubitWordEquivB n L) =
      matrixPhysicalBlockKraus n p a b L := by
  have hPhysical : physicalTensorKrausB n p = tensorDampingKrausB n p :=
    funext (physicalTensorKrausB_eq_damping n p)
  rw [sequentialCallsKrausB_eq_physical, hPhysical]
  unfold matrixPhysicalBlockKraus transferLabKrausC
  rw [Matrix.submatrix_submatrix]
  change _ = (referenceKrausB (tensorDampingKrausB n p) (Fin a × Fin b) L).submatrix
    ((matrixBlockOutputEquiv n a b).trans
      (outputPortMemoryEquivB (Finset (Fin n)) (Fin a) (Fin b)))
    ((matrixBlockInputEquiv n a b).trans
      (inputPortMemoryEquivB (Finset (Fin n)) (Fin a) (Fin b)))
  rw [matrixBlockOutputEquiv_trans_port, matrixBlockInputEquiv_trans_port]

def matrixPhysicalBlockOutput (n : ℕ) (p : ℝ) (a b : ℕ)
    (ρ : BipartiteMatrix (doubleDimB n a) b) : BipartiteMatrix a (doubleDimB n b) :=
  krausSumB (matrixPhysicalBlockKraus n p a b) ρ

theorem matrixPhysicalBlockOutput_eq_raw (n : ℕ) (p : ℝ) (a b : ℕ)
    (ρ : BipartiteMatrix (doubleDimB n a) b) :
    matrixPhysicalBlockOutput n p a b ρ =
      (krausSumB (transferLabKrausC (A := Fin a) (B := Fin b) (tensorDampingKrausB n p))
        (ρ.submatrix (matrixBlockInputEquiv n a b).symm
          (matrixBlockInputEquiv n a b).symm)).submatrix
        (matrixBlockOutputEquiv n a b) (matrixBlockOutputEquiv n a b) :=
  krausSumB_matrix_chart _ _ (Equiv.refl _) _ ρ

theorem sequentialCallsKrausB_output_eq_matrix_block (n : ℕ) (p : ℝ) (a b : ℕ)
    (ρ : BipartiteMatrix (doubleDimB n a) b) :
    krausSumB (sequentialCallsKrausB p n a b) ρ = matrixPhysicalBlockOutput n p a b ρ := by
  have hFamily : sequentialCallsKrausB p n a b = fun h =>
      matrixPhysicalBlockKraus n p a b ((subsetQubitWordEquivB n).symm h) := by
    funext h
    simpa only [Equiv.apply_symm_apply] using sequentialCallsKrausB_eq_matrix_block n p a b
      ((subsetQubitWordEquivB n).symm h)
  rw [hFamily]
  unfold matrixPhysicalBlockOutput krausSumB
  exact (subsetQubitWordEquivB n).symm.sum_comp
    (fun L => matrixPhysicalBlockKraus n p a b L * ρ * (matrixPhysicalBlockKraus n p a b L)ᴴ)

theorem sequentialCallsProtocolB_output_eq_matrix_block (n : ℕ) (p : ℝ) (a b : ℕ)
    (ρ : BipartiteMatrix (doubleDimB n a) b) :
    (sequentialCallsProtocolB p n a b).output ρ = matrixPhysicalBlockOutput n p a b ρ := by
  rw [sequentialCallsProtocolB_output, sequentialCallsKrausB_output_eq_matrix_block]

theorem matrixPhysicalBlockKraus_complete (n : ℕ) (p : ℝ) (a b : ℕ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ∑ L, (matrixPhysicalBlockKraus n p a b L)ᴴ * matrixPhysicalBlockKraus n p a b L = 1 := by
  apply krausSumB_matrix_chart_complete _ _ (Equiv.refl _) _
  apply transferLabKrausC_complete
  simpa only [physicalTensorKrausB_eq_damping] using physicalTensorKrausB_complete n p hp0 hp1

theorem matrixPhysicalBlockOutput_trace (n : ℕ) (p : ℝ) (a b : ℕ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (ρ : BipartiteMatrix (doubleDimB n a) b) :
    (matrixPhysicalBlockOutput n p a b ρ).trace = ρ.trace :=
  krausSumB_trace_preserving _ (matrixPhysicalBlockKraus_complete n p a b hp0 hp1) ρ

theorem matrixPhysicalBlockOutput_posSemidef (n : ℕ) (p : ℝ) (a b : ℕ)
    {ρ : BipartiteMatrix (doubleDimB n a) b} (hρ : ρ.PosSemidef) :
    (matrixPhysicalBlockOutput n p a b ρ).PosSemidef := krausSumB_posSemidef _ hρ

abbrev MatrixPhaseBlockLabel (n : ℕ) :=
  (Fin n → ZMod 3) × (Σ w : Fin (n + 1), survivorPhaseLabelB n w.val)

def matrixPhaseBlockKraus (n : ℕ) (p : ℝ) (a b : ℕ)
    (z : Fin (Fintype.card (MatrixPhaseBlockLabel n))) :
    Matrix (Fin a × Fin (doubleDimB n b)) (Fin (doubleDimB n a) × Fin b) ℂ :=
  (recoveredPhaseLabKrausC n p (Fin a) (Fin b)
    (finiteIndexB (MatrixPhaseBlockLabel n) z)).submatrix
      (matrixBlockOutputEquiv n a b) (matrixBlockInputEquiv n a b)

def matrixPhaseBlockOutput (n : ℕ) (p : ℝ) (a b : ℕ)
    (σ : BipartiteMatrix (doubleDimB n a) b) : BipartiteMatrix a (doubleDimB n b) :=
  krausSumB (matrixPhaseBlockKraus n p a b) σ

theorem matrixPhaseBlockOutput_eq_raw (n : ℕ) (p : ℝ) (a b : ℕ)
    (σ : BipartiteMatrix (doubleDimB n a) b) :
    matrixPhaseBlockOutput n p a b σ =
      (krausSumB (recoveredPhaseLabKrausC n p (Fin a) (Fin b))
        (σ.submatrix (matrixBlockInputEquiv n a b).symm
          (matrixBlockInputEquiv n a b).symm)).submatrix
        (matrixBlockOutputEquiv n a b) (matrixBlockOutputEquiv n a b) :=
  krausSumB_matrix_chart _ _ (finiteIndexB (MatrixPhaseBlockLabel n)) _ σ

theorem matrixPhaseBlockKraus_complete (n : ℕ) (p : ℝ) (a b : ℕ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ∑ z, (matrixPhaseBlockKraus n p a b z)ᴴ * matrixPhaseBlockKraus n p a b z = 1 :=
  krausSumB_matrix_chart_complete _ _ (finiteIndexB (MatrixPhaseBlockLabel n)) _
    (recoveredPhaseLabKrausC_complete n p (Fin a) (Fin b) hp0 hp1)

theorem matrixPhaseBlockOutput_trace (n : ℕ) (p : ℝ) (a b : ℕ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (σ : BipartiteMatrix (doubleDimB n a) b) :
    (matrixPhaseBlockOutput n p a b σ).trace = σ.trace :=
  krausSumB_trace_preserving _ (matrixPhaseBlockKraus_complete n p a b hp0 hp1) σ

theorem matrixPhaseBlockOutput_posSemidef (n : ℕ) (p : ℝ) (a b : ℕ)
    {σ : BipartiteMatrix (doubleDimB n a) b} (hσ : σ.PosSemidef) :
    (matrixPhaseBlockOutput n p a b σ).PosSemidef := krausSumB_posSemidef _ hσ

theorem recoveredPhaseLabKrausC_output_sepPositive_matrix (n : ℕ) (p : ℝ)
    (A B : Type*) [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {σ : Matrix ((A × Finset (Fin n)) × B) ((A × Finset (Fin n)) × B) ℂ}
    (hσ : SepPositive σ) :
    SepPositive (krausSumB (recoveredPhaseLabKrausC n p A B) σ) := by
  have hPhase := (phaseRecordedOutputC_sepPositive n p A B hσ).submatrix_local_equiv
    (finiteIndexB (A × Finset (Fin n))) (finiteIndexB (Finset (Fin n) × B))
  have hRecovered : SepPositive (recoveredPhaseOutputC n p A B σ) := by
    unfold recoveredPhaseOutputC
    apply (fullRecordRecoveryProtocolB p n A B).output_sepPositive_of_calls_zero
      (fullRecordRecoveryProtocolB_calls p n A B)
    exact hPhase
  rw [recoveredPhaseOutputC_eq_krausSum] at hRecovered
  exact (sepPositive_matrix_chart_iff (finiteIndexB A)
    (finiteIndexB (Finset (Fin n) × B)) _).mp hRecovered

theorem matrixPhaseBlockOutput_sepPositive (n : ℕ) (p : ℝ) (a b : ℕ)
    {σ : BipartiteMatrix (doubleDimB n a) b} (hσ : SepPositive σ) :
    SepPositive (matrixPhaseBlockOutput n p a b σ) := by
  have hInput : SepPositive (σ.submatrix (matrixBlockInputEquiv n a b).symm
      (matrixBlockInputEquiv n a b).symm) := by
    exact hσ.submatrix_local_equiv (matrixBlockInputAliceEquiv n a).symm (Equiv.refl (Fin b))
  rw [matrixPhaseBlockOutput_eq_raw]
  exact SepPositive.submatrix_local_equiv
    (recoveredPhaseLabKrausC_output_sepPositive_matrix n p (Fin a) (Fin b) hInput)
    (Equiv.refl (Fin a)) (matrixBlockOutputBobEquiv n b)

theorem matrixPhaseBlockOutput_isDensity (n : ℕ) (p : ℝ) (a b : ℕ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {σ : BipartiteMatrix (doubleDimB n a) b} (hσ : IsDensity σ) :
    IsDensity (matrixPhaseBlockOutput n p a b σ) :=
  ⟨matrixPhaseBlockOutput_posSemidef n p a b hσ.1,
    (matrixPhaseBlockOutput_trace n p a b hp0 hp1 σ).trans hσ.2⟩

theorem matrixPhaseBlockOutput_isSeparable (n : ℕ) (p : ℝ) (a b : ℕ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {σ : BipartiteMatrix (doubleDimB n a) b} (hσ : IsSeparable (doubleDimB n a) b σ) :
    IsSeparable a (doubleDimB n b) (matrixPhaseBlockOutput n p a b σ) := by
  apply (matrixPhaseBlockOutput_sepPositive n p a b hσ.sepPositive).isSeparable
  rw [matrixPhaseBlockOutput_trace n p a b hp0 hp1, hσ.isDensity.2]

end QuantumProver.AmplitudeDamping.FiniteModel

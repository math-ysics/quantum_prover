import QuantumProver.InformationTheory.AmplitudeDamping.QuantumCapacity.BlockChannels
import QuantumProver.InformationTheory.AmplitudeDamping.QuantumCapacity.OptimizedRecordComparison

set_option autoImplicit false
set_option maxHeartbeats 1200000

noncomputable section
open Matrix
open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder Matrix Kronecker

namespace QuantumProver.AmplitudeDamping.FiniteModel

section RecoveredOptimizedComparator

variable (n : ℕ) (p z : ℝ) (A B : Type*) [Fintype A] [Fintype B]
  [DecidableEq A] [DecidableEq B]

def recoveredOptimizedPhaseLabKraus (γ : MatrixPhaseBlockLabel n) :
    Matrix (A × (Finset (Fin n) × B)) ((A × Finset (Fin n)) × B) ℂ :=
  fullRecordLabCorrectionB n A B γ.1 * optimizedPhaseRecordedKraus n p z A B γ.2

theorem recoveredOptimizedPhaseLabKraus_complete (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ∑ γ, (recoveredOptimizedPhaseLabKraus n p z A B γ)ᴴ *
      recoveredOptimizedPhaseLabKraus n p z A B γ = 1 :=
  krausSumB_compose_completeC _ _ (fullRecordLabCorrectionB_completeC n A B)
    (optimizedPhaseRecordedKraus_complete n p z A B hp0 hp1)

theorem recoveredOptimizedPhaseOutput_eq_krausSum
    (σ : Matrix ((A × Finset (Fin n)) × B) ((A × Finset (Fin n)) × B) ℂ) :
    recoveredOptimizedPhaseOutput n p z A B σ =
      (krausSumB (recoveredOptimizedPhaseLabKraus n p z A B) σ).submatrix
        ((finiteIndexB A).prodCongr (finiteIndexB (Finset (Fin n) × B)))
        ((finiteIndexB A).prodCongr (finiteIndexB (Finset (Fin n) × B))) := by
  rw [recoveredOptimizedPhaseOutput, recordedOutputEquivC,
    fullRecordRecoveryProtocolB_output_reindex, optimizedPhaseRecordedOutput, krausSumB_compose]
  rfl

theorem recoveredOptimizedPhaseLabKraus_output_sepPositive_matrix
    {σ : Matrix ((A × Finset (Fin n)) × B) ((A × Finset (Fin n)) × B) ℂ}
    (hσ : SepPositive σ) :
    SepPositive (krausSumB (recoveredOptimizedPhaseLabKraus n p z A B) σ) := by
  have hRecorded := (optimizedPhaseRecordedOutput_sepPositive n p z A B hσ).submatrix_local_equiv
    (finiteIndexB (A × Finset (Fin n))) (finiteIndexB (Finset (Fin n) × B))
  have hRecovered : SepPositive (recoveredOptimizedPhaseOutput n p z A B σ) := by
    unfold recoveredOptimizedPhaseOutput
    apply (fullRecordRecoveryProtocolB p n A B).output_sepPositive_of_calls_zero
      (fullRecordRecoveryProtocolB_calls p n A B)
    exact hRecorded
  rw [recoveredOptimizedPhaseOutput_eq_krausSum] at hRecovered
  exact (sepPositive_matrix_chart_iff (finiteIndexB A)
    (finiteIndexB (Finset (Fin n) × B)) _).mp hRecovered

end RecoveredOptimizedComparator

def matrixOptimizedBlockRecoveredOutputEquiv (n a b : ℕ) :
    (Fin a × Fin (doubleDimB n b)) ≃
      (Fin (Fintype.card (Fin a)) × Fin (Fintype.card (Finset (Fin n) × Fin b))) :=
  (matrixBlockOutputEquiv n a b).trans
    ((finiteIndexB (Fin a)).symm.prodCongr (finiteIndexB (Finset (Fin n) × Fin b)).symm)

def matrixOptimizedPhaseBlockKraus (n : ℕ) (p z : ℝ) (a b : ℕ)
    (γ : Fin (Fintype.card (MatrixPhaseBlockLabel n))) :
    Matrix (Fin a × Fin (doubleDimB n b)) (Fin (doubleDimB n a) × Fin b) ℂ :=
  (recoveredOptimizedPhaseLabKraus n p z (Fin a) (Fin b)
    (finiteIndexB (MatrixPhaseBlockLabel n) γ)).submatrix
      (matrixBlockOutputEquiv n a b) (matrixBlockInputEquiv n a b)

def matrixOptimizedPhaseBlockOutput (n : ℕ) (p z : ℝ) (a b : ℕ)
    (σ : BipartiteMatrix (doubleDimB n a) b) : BipartiteMatrix a (doubleDimB n b) :=
  krausSumB (matrixOptimizedPhaseBlockKraus n p z a b) σ

theorem matrixOptimizedPhaseBlockOutput_eq_labKrausSum (n : ℕ) (p z : ℝ) (a b : ℕ)
    (σ : BipartiteMatrix (doubleDimB n a) b) :
    matrixOptimizedPhaseBlockOutput n p z a b σ =
      (krausSumB (recoveredOptimizedPhaseLabKraus n p z (Fin a) (Fin b))
        (σ.submatrix (matrixBlockInputEquiv n a b).symm
          (matrixBlockInputEquiv n a b).symm)).submatrix
        (matrixBlockOutputEquiv n a b) (matrixBlockOutputEquiv n a b) :=
  krausSumB_matrix_chart _ _ (finiteIndexB (MatrixPhaseBlockLabel n)) _ σ

theorem matrixOptimizedPhaseBlockOutput_eq_raw (n : ℕ) (p z : ℝ) (a b : ℕ)
    (σ : BipartiteMatrix (doubleDimB n a) b) :
    matrixOptimizedPhaseBlockOutput n p z a b σ =
      (recoveredOptimizedPhaseOutput n p z (Fin a) (Fin b)
        (σ.submatrix (matrixBlockInputEquiv n a b).symm
          (matrixBlockInputEquiv n a b).symm)).submatrix
        (matrixOptimizedBlockRecoveredOutputEquiv n a b)
        (matrixOptimizedBlockRecoveredOutputEquiv n a b) := by
  rw [matrixOptimizedPhaseBlockOutput_eq_labKrausSum, recoveredOptimizedPhaseOutput_eq_krausSum]
  let eFinite := (finiteIndexB (Fin a)).prodCongr (finiteIndexB (Finset (Fin n) × Fin b))
  have hChart (x : Fin a × Fin (doubleDimB n b)) :
      eFinite (matrixOptimizedBlockRecoveredOutputEquiv n a b x) =
        matrixBlockOutputEquiv n a b x := by
    change eFinite (eFinite.symm (matrixBlockOutputEquiv n a b x)) = _
    exact eFinite.apply_symm_apply _
  ext x y
  change _ = krausSumB (recoveredOptimizedPhaseLabKraus n p z (Fin a) (Fin b))
    (σ.submatrix (matrixBlockInputEquiv n a b).symm (matrixBlockInputEquiv n a b).symm)
      (eFinite (matrixOptimizedBlockRecoveredOutputEquiv n a b x))
      (eFinite (matrixOptimizedBlockRecoveredOutputEquiv n a b y))
  simp only [Matrix.submatrix_apply, hChart]

theorem matrixOptimizedPhaseBlockKraus_complete (n : ℕ) (p z : ℝ) (a b : ℕ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ∑ γ, (matrixOptimizedPhaseBlockKraus n p z a b γ)ᴴ *
      matrixOptimizedPhaseBlockKraus n p z a b γ = 1 :=
  krausSumB_matrix_chart_complete _ _ (finiteIndexB (MatrixPhaseBlockLabel n)) _
    (recoveredOptimizedPhaseLabKraus_complete n p z (Fin a) (Fin b) hp0 hp1)

theorem matrixOptimizedPhaseBlockOutput_trace (n : ℕ) (p z : ℝ) (a b : ℕ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (σ : BipartiteMatrix (doubleDimB n a) b) :
    (matrixOptimizedPhaseBlockOutput n p z a b σ).trace = σ.trace :=
  krausSumB_trace_preserving _ (matrixOptimizedPhaseBlockKraus_complete n p z a b hp0 hp1) σ

theorem matrixOptimizedPhaseBlockOutput_posSemidef (n : ℕ) (p z : ℝ) (a b : ℕ)
    {σ : BipartiteMatrix (doubleDimB n a) b} (hσ : σ.PosSemidef) :
    (matrixOptimizedPhaseBlockOutput n p z a b σ).PosSemidef := krausSumB_posSemidef _ hσ

theorem matrixOptimizedPhaseBlockOutput_sepPositive (n : ℕ) (p z : ℝ) (a b : ℕ)
    {σ : BipartiteMatrix (doubleDimB n a) b} (hσ : SepPositive σ) :
    SepPositive (matrixOptimizedPhaseBlockOutput n p z a b σ) := by
  have hInput : SepPositive (σ.submatrix (matrixBlockInputEquiv n a b).symm
      (matrixBlockInputEquiv n a b).symm) := by
    exact hσ.submatrix_local_equiv (matrixBlockInputAliceEquiv n a).symm (Equiv.refl (Fin b))
  rw [matrixOptimizedPhaseBlockOutput_eq_labKrausSum]
  exact SepPositive.submatrix_local_equiv
    (recoveredOptimizedPhaseLabKraus_output_sepPositive_matrix n p z (Fin a) (Fin b) hInput)
    (Equiv.refl (Fin a)) (matrixBlockOutputBobEquiv n b)

theorem matrixOptimizedPhaseBlockOutput_isDensity (n : ℕ) (p z : ℝ) (a b : ℕ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {σ : BipartiteMatrix (doubleDimB n a) b} (hσ : IsDensity σ) :
    IsDensity (matrixOptimizedPhaseBlockOutput n p z a b σ) :=
  ⟨matrixOptimizedPhaseBlockOutput_posSemidef n p z a b hσ.1,
    (matrixOptimizedPhaseBlockOutput_trace n p z a b hp0 hp1 σ).trans hσ.2⟩

theorem matrixOptimizedPhaseBlockOutput_isSeparable (n : ℕ) (p z : ℝ) (a b : ℕ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {σ : BipartiteMatrix (doubleDimB n a) b} (hσ : IsSeparable (doubleDimB n a) b σ) :
    IsSeparable a (doubleDimB n b) (matrixOptimizedPhaseBlockOutput n p z a b σ) := by
  apply (matrixOptimizedPhaseBlockOutput_sepPositive n p z a b hσ.sepPositive).isSeparable
  rw [matrixOptimizedPhaseBlockOutput_trace n p z a b hp0 hp1, hσ.isDensity.2]

end QuantumProver.AmplitudeDamping.FiniteModel

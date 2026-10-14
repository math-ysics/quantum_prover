import QuantumProver.InformationTheory.AmplitudeDamping.QuantumCapacity.RecordTypes

set_option autoImplicit false
set_option maxHeartbeats 1200000

noncomputable section

open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder Matrix Kronecker

namespace QuantumProver.AmplitudeDamping.FiniteModel

section OptimizedSectorTransfer

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

theorem transferLabOptimizedPhase_sepPositive (n w : ℕ) (p z : ℝ)
    {σ : Matrix ((A × WeightBasisB n w) × B) ((A × WeightBasisB n w) × B) ℂ}
    (hσ : SepPositive σ) :
    SepPositive (krausSumB (transferLabKrausC (A := A) (B := B)
      (optimizedPhaseKrausB n w p z)) σ) := by
  have hfamily : transferLabKrausC (A := A) (B := B) (optimizedPhaseKrausB n w p z) =
      measurePrepareTransferKraus (A := A) (B := B)
        (weightedPhaseInputVectorB n w (optimizedPhaseLawB n w p z))
        (weightedPhaseOutputVectorB n w) := by
    funext j
    exact transferLabKrausC_rankOne _ _ j
  rw [hfamily]
  exact hσ.measurePrepareTransfer _ _

theorem transferLabOptimizedPhase_survivor_sum (n w : ℕ) (hwn : w ≤ n)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (z : ℝ)
    (σ : Matrix ((A × WeightBasisB n w) × B) ((A × WeightBasisB n w) × B) ℂ) :
    krausSumB (transferLabKrausC (A := A) (B := B) (optimizedPhaseKrausB n w p z)) σ =
      ∑ r : Fin (w + 1), optimizedPhaseLawB n w p z r •
        krausSumB (transferLabKrausC (A := A) (B := B)
          (measurePhaseKrausB n w r.val)) σ := by
  rw [transferLabOutputC_eq_reference,
    optimizedPhaseChannelB_reference_eq n w hwn p hp0 hp1 z]
  ext x y
  simp only [transferLabOutputC_eq_reference, Matrix.submatrix_apply,
    Matrix.sum_apply, Matrix.smul_apply]

theorem recordedPhaseBranch_sepPositive (n w r : ℕ)
    {σ : Matrix ((A × Finset (Fin n)) × B) ((A × Finset (Fin n)) × B) ℂ}
    (hσ : SepPositive σ) : SepPositive (recordedPhaseBranchC n w r A B σ) := by
  have hport : measurePhaseKrausB n w r = fun t => QuantumProver.AmplitudeDamping.SecretKey.KrausAlgebra.rankOneKraus
      (phaseInputVectorB n w t) (phaseOutputVectorB n r t) :=
    funext (measurePhaseKrausB_rankOne n w r)
  have hfamily : transferLabKrausC (A := A × Finset (Fin n)) (B := B)
      (measurePhaseKrausB n w r) =
      measurePrepareTransferKraus (A := A × Finset (Fin n)) (B := B)
        (phaseInputVectorB n w) (phaseOutputVectorB n r) := by
    rw [hport]
    funext t
    exact transferLabKrausC_rankOne _ _ t
  unfold recordedPhaseBranchC
  rw [hfamily]
  exact (typeCopyLabC_sepPositive n w A B hσ).measurePrepareTransfer _ _

end OptimizedSectorTransfer

section CompleteOptimizedRecord

variable (n : ℕ) (p z : ℝ) (A B : Type*) [Fintype A] [Fintype B]
  [DecidableEq A] [DecidableEq B]

def optimizedPhaseRecordedKraus : (Σ w : Fin (n + 1), survivorPhaseLabelB n w.val) →
    Matrix ((A × Finset (Fin n)) × (Finset (Fin n) × B))
      ((A × Finset (Fin n)) × B) ℂ :=
  fun j => transferLabKrausC (A := A × Finset (Fin n)) (B := B)
      (optimizedPhaseKrausB n j.1.val p z) j.2 * typeCopyLabC n j.1.val A B

theorem optimizedPhaseRecordedKraus_complete (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ∑ j, (optimizedPhaseRecordedKraus n p z A B j)ᴴ *
      optimizedPhaseRecordedKraus n p z A B j = 1 := by
  simp only [optimizedPhaseRecordedKraus, Fintype.sum_sigma, Matrix.conjTranspose_mul]
  calc
    _ = ∑ w : Fin (n + 1), (typeCopyLabC n w.val A B)ᴴ *
        (∑ j : survivorPhaseLabelB n w.val,
          (transferLabKrausC (A := A × Finset (Fin n)) (B := B)
            (optimizedPhaseKrausB n w.val p z) j)ᴴ *
          transferLabKrausC (A := A × Finset (Fin n)) (B := B)
            (optimizedPhaseKrausB n w.val p z) j) * typeCopyLabC n w.val A B := by
      apply Finset.sum_congr rfl
      intro w _
      simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_assoc]
    _ = 1 := by
      simp only [transferLabKrausC_complete _
        (optimizedPhaseKrausB_complete n _ (Nat.le_of_lt_succ (Fin.isLt _)) p hp0 hp1 z),
        Matrix.mul_one]
      exact typeCopyLabC_complete n A B

def optimizedPhaseRecordedOutput
    (σ : Matrix ((A × Finset (Fin n)) × B) ((A × Finset (Fin n)) × B) ℂ) :
    Matrix ((A × Finset (Fin n)) × (Finset (Fin n) × B))
      ((A × Finset (Fin n)) × (Finset (Fin n) × B)) ℂ :=
  krausSumB (optimizedPhaseRecordedKraus n p z A B) σ

theorem optimizedPhaseRecordedOutput_eq_sectors
    (σ : Matrix ((A × Finset (Fin n)) × B) ((A × Finset (Fin n)) × B) ℂ) :
    optimizedPhaseRecordedOutput n p z A B σ = ∑ w : Fin (n + 1),
      krausSumB (transferLabKrausC (A := A × Finset (Fin n)) (B := B)
        (optimizedPhaseKrausB n w.val p z))
        (typeCopyLabC n w.val A B * σ * (typeCopyLabC n w.val A B)ᴴ) := by
  unfold optimizedPhaseRecordedOutput
  simp only [krausSumB, optimizedPhaseRecordedKraus, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro w _
  change krausSumB (fun j => transferLabKrausC (A := A × Finset (Fin n)) (B := B)
        (optimizedPhaseKrausB n w.val p z) j * typeCopyLabC n w.val A B) σ =
      krausSumB (transferLabKrausC (A := A × Finset (Fin n)) (B := B)
        (optimizedPhaseKrausB n w.val p z))
        (typeCopyLabC n w.val A B * σ * (typeCopyLabC n w.val A B)ᴴ)
  exact krausSumB_rectangular_precompose _ _ σ

theorem optimizedPhaseRecordedOutput_survivor_sum (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (σ : Matrix ((A × Finset (Fin n)) × B) ((A × Finset (Fin n)) × B) ℂ) :
    optimizedPhaseRecordedOutput n p z A B σ = ∑ w : Fin (n + 1),
      ∑ r : Fin (w.val + 1), optimizedPhaseLawB n w.val p z r •
        recordedPhaseBranchC n w.val r.val A B σ := by
  rw [optimizedPhaseRecordedOutput_eq_sectors]
  apply Finset.sum_congr rfl
  intro w _
  exact transferLabOptimizedPhase_survivor_sum n w.val (Nat.le_of_lt_succ w.isLt)
    p hp0 hp1 z _

theorem optimizedPhaseRecordedOutput_trace (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (σ : Matrix ((A × Finset (Fin n)) × B) ((A × Finset (Fin n)) × B) ℂ) :
    (optimizedPhaseRecordedOutput n p z A B σ).trace = σ.trace :=
  krausSumB_trace_preserving _ (optimizedPhaseRecordedKraus_complete n p z A B hp0 hp1) σ

theorem optimizedPhaseRecordedOutput_posSemidef
    {σ : Matrix ((A × Finset (Fin n)) × B) ((A × Finset (Fin n)) × B) ℂ}
    (hσ : σ.PosSemidef) : (optimizedPhaseRecordedOutput n p z A B σ).PosSemidef :=
  krausSumB_posSemidef _ hσ

theorem optimizedPhaseRecordedOutput_isDensity (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {σ : Matrix ((A × Finset (Fin n)) × B) ((A × Finset (Fin n)) × B) ℂ}
    (hσ : IsDensity σ) : IsDensity (optimizedPhaseRecordedOutput n p z A B σ) :=
  ⟨optimizedPhaseRecordedOutput_posSemidef n p z A B hσ.1,
    (optimizedPhaseRecordedOutput_trace n p z A B hp0 hp1 σ).trans hσ.2⟩

theorem optimizedPhaseRecordedOutput_sepPositive
    {σ : Matrix ((A × Finset (Fin n)) × B) ((A × Finset (Fin n)) × B) ℂ}
    (hσ : SepPositive σ) : SepPositive (optimizedPhaseRecordedOutput n p z A B σ) := by
  rw [optimizedPhaseRecordedOutput_eq_sectors]
  apply SepPositive.sum
  intro w
  exact transferLabOptimizedPhase_sepPositive n w.val p z
    (typeCopyLabC_sepPositive n w.val A B hσ)

theorem optimizedPhaseRecordedOutput_isSeparable (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {σ : Matrix ((A × Finset (Fin n)) × B) ((A × Finset (Fin n)) × B) ℂ}
    (hσ : SepPositive σ) (htrace : σ.trace = 1) :
    IsSeparable (Fintype.card (A × Finset (Fin n))) (Fintype.card (Finset (Fin n) × B))
      ((optimizedPhaseRecordedOutput n p z A B σ).submatrix
        (recordedOutputEquivC n A B) (recordedOutputEquivC n A B)) := by
  apply ((optimizedPhaseRecordedOutput_sepPositive n p z A B hσ).submatrix_local_equiv
    (finiteIndexB (A × Finset (Fin n))) (finiteIndexB (Finset (Fin n) × B))).isSeparable
  rw [TensorPower.trace_submatrix_equiv, optimizedPhaseRecordedOutput_trace n p z A B hp0 hp1,
    htrace]

end CompleteOptimizedRecord

section UniformOptimizedFlags

def optimizedRecordedFlagLaw (n : ℕ) (p z : ℝ) (j : Fin (n + 1) × Fin (n + 1)) : ℝ :=
  if hr : j.2.val ≤ j.1.val then
    optimizedPhaseLawB n j.1.val p z ⟨j.2.val, Nat.lt_succ_of_le hr⟩ else 0

theorem optimizedRecordedFlagLaw_nonneg (n : ℕ) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (z : ℝ) (j : Fin (n + 1) × Fin (n + 1)) : 0 ≤ optimizedRecordedFlagLaw n p z j := by
  unfold optimizedRecordedFlagLaw
  split_ifs with hr
  · exact optimizedPhaseLawB_nonneg n j.1.val (Nat.le_of_lt_succ j.1.isLt)
      p hp0 hp1 z _
  · exact le_rfl

theorem optimizedRecordedFlagLaw_support (n : ℕ) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (z : ℝ) (j : Fin (n + 1) × Fin (n + 1))
    (hZero : optimizedRecordedFlagLaw n p z j = 0) : recordedFlagLawC n p j = 0 := by
  by_cases hr : j.2.val ≤ j.1.val
  · rw [optimizedRecordedFlagLaw, dite_eq_left hr] at hZero
    have h := optimizedPhaseLawB_support n j.1.val (Nat.le_of_lt_succ j.1.isLt)
      p hp0 hp1 z _ hZero
    simpa only [recordedFlagLawC, ite_eq_left hr, physicalPhaseLawB] using h
  · simp [recordedFlagLawC, hr]

theorem optimizedRecordedFlagLaw_sum {M : Type*} [AddCommMonoid M] [Module ℝ M]
    (n : ℕ) (p z : ℝ) (w : Fin (n + 1)) (F : ℕ → M) :
    (∑ r : Fin (n + 1), optimizedRecordedFlagLaw n p z (w, r) • F r.val) =
      ∑ r : Fin (w.val + 1), optimizedPhaseLawB n w.val p z r • F r.val := by
  let f : ℕ → M := fun r =>
    if hr : r ≤ w.val then optimizedPhaseLawB n w.val p z ⟨r, Nat.lt_succ_of_le hr⟩ • F r
    else 0
  have hLeft : (∑ r : Fin (n + 1), optimizedRecordedFlagLaw n p z (w, r) • F r.val) =
      ∑ r ∈ Finset.range (n + 1), f r := by
    rw [← Fin.sum_univ_eq_sum_range f (n + 1)]
    apply Finset.sum_congr rfl
    intro r _
    simp [optimizedRecordedFlagLaw, f, dite_smul]
  have hRight : (∑ r : Fin (w.val + 1), optimizedPhaseLawB n w.val p z r • F r.val) =
      ∑ r ∈ Finset.range (w.val + 1), f r := by
    rw [← Fin.sum_univ_eq_sum_range f (w.val + 1)]
    apply Finset.sum_congr rfl
    intro r _
    simp [f, Nat.le_of_lt_succ r.isLt]
  rw [hLeft, hRight]
  symm
  apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ (Nat.le_of_lt_succ w.isLt)))
  intro r _ hr
  have hwr : ¬ r ≤ w.val := by
    have h : ¬ r < w.val + 1 := by simpa only [Finset.mem_range] using hr
    omega
  simp [f, hwr]

theorem optimizedRecordedFlagLaw_sum_one (n : ℕ) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (z : ℝ) (w : Fin (n + 1)) : ∑ r : Fin (n + 1), optimizedRecordedFlagLaw n p z (w, r) = 1 := by
  have h := optimizedRecordedFlagLaw_sum n p z w (fun _ => (1 : ℝ))
  simpa only [smul_eq_mul, mul_one,
    optimizedPhaseLawB_sum n w.val (Nat.le_of_lt_succ w.isLt) p hp0 hp1 z] using h

end UniformOptimizedFlags

section OptimizedFlagRecovery

variable (n : ℕ) (p z : ℝ) (A B : Type*) [Fintype A] [Fintype B]
  [DecidableEq A] [DecidableEq B]

theorem optimizedPhaseRecordedOutput_uniform_sum (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (σ : Matrix ((A × Finset (Fin n)) × B) ((A × Finset (Fin n)) × B) ℂ) :
    optimizedPhaseRecordedOutput n p z A B σ = ∑ w : Fin (n + 1), ∑ r : Fin (n + 1),
      optimizedRecordedFlagLaw n p z (w, r) • recordedPhaseBranchC n w.val r.val A B σ := by
  rw [optimizedPhaseRecordedOutput_survivor_sum n p z A B hp0 hp1]
  apply Finset.sum_congr rfl
  intro w _
  exact (optimizedRecordedFlagLaw_sum n p z w
    (fun r => recordedPhaseBranchC n w.val r A B σ)).symm

def optimizedFlaggedPhaseOutput
    (σ : Matrix ((A × Finset (Fin n)) × B) ((A × Finset (Fin n)) × B) ℂ) :
    BipartiteMatrix ((n + 1) * Fintype.card (A × Finset (Fin n)))
      ((n + 1) * Fintype.card (Finset (Fin n) × B)) :=
  labFlagComparator (optimizedRecordedFlagLaw n p z) (fun j =>
    (recordedPhaseBranchC n j.1.val j.2.val A B σ).submatrix
      (recordedOutputEquivC n A B) (recordedOutputEquivC n A B))

theorem optimizedFlaggedPhaseOutput_erase (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (σ : Matrix ((A × Finset (Fin n)) × B) ((A × Finset (Fin n)) × B) ℂ) :
    (eraseLabFlagsProtocolC p (n + 1) (n + 1)
      (Fintype.card (A × Finset (Fin n))) (Fintype.card (Finset (Fin n) × B))).output
        (optimizedFlaggedPhaseOutput n p z A B σ) =
      (optimizedPhaseRecordedOutput n p z A B σ).submatrix
        (recordedOutputEquivC n A B) (recordedOutputEquivC n A B) := by
  rw [optimizedFlaggedPhaseOutput, eraseLabFlagsProtocolC_labFlagComparator,
    optimizedPhaseRecordedOutput_uniform_sum n p z A B hp0 hp1]
  ext x y
  simp only [Fintype.sum_prod_type, Matrix.sum_apply, Matrix.smul_apply,
    Matrix.submatrix_apply, Complex.coe_smul]

theorem optimizedFlaggedPhaseOutput_trace (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (σ : Matrix ((A × Finset (Fin n)) × B) ((A × Finset (Fin n)) × B) ℂ) :
    (optimizedFlaggedPhaseOutput n p z A B σ).trace = σ.trace := by
  calc
    _ = ((eraseLabFlagsProtocolC p (n + 1) (n + 1)
        (Fintype.card (A × Finset (Fin n))) (Fintype.card (Finset (Fin n) × B))).output
          (optimizedFlaggedPhaseOutput n p z A B σ)).trace :=
      (FiniteProtocol.output_trace hp0 hp1 _ _).symm
    _ = σ.trace := by rw [optimizedFlaggedPhaseOutput_erase n p z A B hp0 hp1,
        TensorPower.trace_submatrix_equiv, optimizedPhaseRecordedOutput_trace n p z A B hp0 hp1]

theorem optimizedFlaggedPhaseOutput_sepPositive (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {σ : Matrix ((A × Finset (Fin n)) × B) ((A × Finset (Fin n)) × B) ℂ}
    (hσ : SepPositive σ) : SepPositive (optimizedFlaggedPhaseOutput n p z A B σ) := by
  unfold optimizedFlaggedPhaseOutput labFlagComparator
  apply SepPositive.sum
  intro j
  apply SepPositive.smul _ (optimizedRecordedFlagLaw_nonneg n p hp0 hp1 z j)
  exact ((recordedPhaseBranch_sepPositive n j.1.val j.2.val hσ).submatrix_local_equiv
    (finiteIndexB (A × Finset (Fin n))) (finiteIndexB (Finset (Fin n) × B))).local_conjugation
      (appendFlagKraus j.1) (appendFlagKraus j.2)

theorem optimizedFlaggedPhaseOutput_isSeparable (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {σ : Matrix ((A × Finset (Fin n)) × B) ((A × Finset (Fin n)) × B) ℂ}
    (hσ : SepPositive σ) (htrace : σ.trace = 1) :
    IsSeparable ((n + 1) * Fintype.card (A × Finset (Fin n)))
      ((n + 1) * Fintype.card (Finset (Fin n) × B))
      (optimizedFlaggedPhaseOutput n p z A B σ) := by
  apply (optimizedFlaggedPhaseOutput_sepPositive n p z A B hp0 hp1 hσ).isSeparable
  rw [optimizedFlaggedPhaseOutput_trace n p z A B hp0 hp1, htrace]

def recoveredOptimizedPhaseOutput
    (σ : Matrix ((A × Finset (Fin n)) × B) ((A × Finset (Fin n)) × B) ℂ) :
    BipartiteMatrix (Fintype.card A) (Fintype.card (Finset (Fin n) × B)) :=
  (fullRecordRecoveryProtocolB p n A B).output
    ((optimizedPhaseRecordedOutput n p z A B σ).submatrix
      (recordedOutputEquivC n A B) (recordedOutputEquivC n A B))

theorem recoveredOptimizedPhaseOutput_trace (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (σ : Matrix ((A × Finset (Fin n)) × B) ((A × Finset (Fin n)) × B) ℂ) :
    (recoveredOptimizedPhaseOutput n p z A B σ).trace = σ.trace := by
  rw [recoveredOptimizedPhaseOutput, FiniteProtocol.output_trace hp0 hp1,
    TensorPower.trace_submatrix_equiv, optimizedPhaseRecordedOutput_trace n p z A B hp0 hp1]

theorem recoveredOptimizedPhaseOutput_isSeparable (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {σ : Matrix ((A × Finset (Fin n)) × B) ((A × Finset (Fin n)) × B) ℂ}
    (hσ : SepPositive σ) (htrace : σ.trace = 1) :
    IsSeparable (Fintype.card A) (Fintype.card (Finset (Fin n) × B))
      (recoveredOptimizedPhaseOutput n p z A B σ) :=
  (fullRecordRecoveryProtocolB p n A B).output_isSeparable_of_calls_zero hp0 hp1
    (fullRecordRecoveryProtocolB_calls p n A B)
    (optimizedPhaseRecordedOutput_isSeparable n p z A B hp0 hp1 hσ htrace)

theorem optimizedRecordPair_erase_recover (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (ρ σ : Matrix ((A × Finset (Fin n)) × B) ((A × Finset (Fin n)) × B) ℂ) :
    let erase := eraseLabFlagsProtocolC p (n + 1) (n + 1)
      (Fintype.card (A × Finset (Fin n))) (Fintype.card (Finset (Fin n) × B))
    let recover := fullRecordRecoveryProtocolB p n A B
    (recover.output (erase.output (flaggedRecordedOutputC n p A B ρ)) =
      recover.output ((pinchedRecordedOutputC n p A B ρ).submatrix
        (recordedOutputEquivC n A B) (recordedOutputEquivC n A B))) ∧
    (recover.output (erase.output (optimizedFlaggedPhaseOutput n p z A B σ)) =
      recoveredOptimizedPhaseOutput n p z A B σ) := by
  dsimp only
  constructor
  · rw [flaggedRecordedOutputC_erase n p A B hp0 hp1]
  · rw [optimizedFlaggedPhaseOutput_erase n p z A B hp0 hp1]
    rfl

end OptimizedFlagRecovery

end QuantumProver.AmplitudeDamping.FiniteModel

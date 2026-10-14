import QuantumProver.InformationTheory.AmplitudeDamping.QuantumCapacity.AdaptiveIteration
import QuantumProver.InformationTheory.AmplitudeDamping.QuantumCapacity.OptimizedRecordComparison
import QuantumProver.InformationTheory.AmplitudeDamping.QuantumCapacity.OptimizedSectorCharge
import QuantumProver.InformationTheory.AmplitudeDamping.QuantumCapacity.OptimizedComparisonTree

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix Kronecker

namespace QuantumProver.AmplitudeDamping.FiniteModel

def optimizedBlockOrderA (z : ℝ) : ℝ := 1 / (1 - z)

theorem optimizedBlockOrderA_gt_one {z : ℝ} (hz0 : 0 < z) (hz1 : z < 1) :
    1 < optimizedBlockOrderA z :=
  (lt_div_iff₀ (sub_pos.mpr hz1)).mpr (by linarith)

def optimizedBlockQFactorA (n : ℕ) (p z : ℝ) : ℝ :=
  ((n : ℝ) + 1) ^ optimizedBlockOrderA z * (typeMomentMaxA n p z) ^ optimizedBlockOrderA z

def optimizedBlockLogChargeA (n : ℕ) (p z : ℝ) : ℝ :=
  (logTwo ((n : ℝ) + 1) + logTwo (typeMomentMaxA n p z)) / z

theorem one_le_optimizedBlockQFactorA (n : ℕ) (p : ℝ) {z : ℝ}
    (hz0 : 0 < z) (hz1 : z < 1) : 1 ≤ optimizedBlockQFactorA n p z := by
  have hα := (optimizedBlockOrderA_gt_one hz0 hz1).le
  have hN : (1 : ℝ) ≤ (n : ℝ) + 1 := by
    have hn := Nat.cast_nonneg (α := ℝ) n
    linarith
  have hM := one_le_typeMomentMaxA n p z
  have hNr := Real.one_le_rpow hN (zero_le_one.trans hα)
  have hMr := Real.one_le_rpow hM (zero_le_one.trans hα)
  unfold optimizedBlockQFactorA
  nlinarith

theorem log_optimizedBlockQFactorA (n : ℕ) (p : ℝ) {z : ℝ}
    (hz0 : 0 < z) (hz1 : z < 1) :
    logTwo (optimizedBlockQFactorA n p z) / (optimizedBlockOrderA z - 1) =
      optimizedBlockLogChargeA n p z := by
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hm : 0 < typeMomentMaxA n p z := zero_lt_one.trans_le (one_le_typeMomentMaxA n p z)
  have hd : 1 - z ≠ 0 := (sub_pos.mpr hz1).ne'
  have hα1 : optimizedBlockOrderA z - 1 ≠ 0 := (sub_pos.mpr (optimizedBlockOrderA_gt_one hz0 hz1)).ne'
  have h2 : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  unfold optimizedBlockQFactorA optimizedBlockLogChargeA logTwo
  rw [Real.log_mul (Real.rpow_pos_of_pos hn _).ne' (Real.rpow_pos_of_pos hm _).ne',
    Real.log_rpow hn, Real.log_rpow hm]
  unfold optimizedBlockOrderA at *
  field_simp [hd, hz0.ne', hα1, h2]
  ring

theorem optimizedBlockLogChargeA_le (n : ℕ) {p z : ℝ}
    (hn : 0 < n) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hz0 : 0 < z) (hz1 : z < 1) :
    optimizedBlockLogChargeA n p z ≤ (n : ℝ) * converseBudget p z +
      (2 / z) * logTwo ((n : ℝ) + 1) := by
  have h := physicalBlockLogChargeA_le_full_parameters n hn hp0 hp1 hz0 hz1.le
  have hRel : optimizedBlockLogChargeA n p z =
      physicalBlockLogChargeA n p z - logTwo ((n : ℝ) + 1) := by
    unfold optimizedBlockLogChargeA physicalBlockLogChargeA
    field_simp [hz0.ne']
    ring
  have hC : ((2 + z) / z) * logTwo ((n : ℝ) + 1) - logTwo ((n : ℝ) + 1) =
      (2 / z) * logTwo ((n : ℝ) + 1) := by
    field_simp [hz0.ne']
    ring
  rw [hRel]
  linarith

theorem sum_uniform_survivorA (n w : ℕ) (hwn : w ≤ n) (f : ℕ → ℝ)
    (hf : ∀ r, w < r → f r = 0) :
    (∑ r : Fin (n + 1), f r.val) = ∑ r : Fin (w + 1), f r.val := by
  rw [Fin.sum_univ_eq_sum_range, Fin.sum_univ_eq_sum_range]
  symm
  apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ hwn))
  intro r _ hr
  apply hf r
  have h : ¬ r < w + 1 := by simpa only [Finset.mem_range] using hr
  omega

theorem survivorMoment_nonnegA (n w : ℕ) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (z : ℝ) :
    0 ≤ Scalar.survivorMoment n w p z := by
  unfold Scalar.survivorMoment
  apply Finset.sum_nonneg
  intro r _
  unfold Scalar.survivorTerm
  exact mul_nonneg (Scalar.binomialTerm_nonneg w r (sub_nonneg.mpr hp1) (by linarith))
    (Real.rpow_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) z)

section ActualOptimizedFlags

variable (n : ℕ) (p z : ℝ) (A B : Type*) [Fintype A] [Fintype B]
  [DecidableEq A] [DecidableEq B]

theorem optimized_uniform_sector_Q_leA_of_order (w : Fin (n + 1))
    (hA : 0 < Fintype.card A) (hB : 0 < Fintype.card B)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {α : ℝ} (hα : 1 < α) (hαz : α * z = α - 1)
    {ρ σ : Matrix ((A × WeightBasisB n w.val) × B) ((A × WeightBasisB n w.val) × B) ℂ}
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) (hs : SupportLE ρ σ) :
    (∑ r : Fin (n + 1), (recordedFlagLawC n p (w, r)) ^ α *
      (optimizedRecordedFlagLaw n p z (w, r)) ^ (1 - α) *
      sandwichedTrace (α)
        (labTransferOutput (lossKrausB n w.val r.val) ρ)
        (labTransferOutput (measurePhaseKrausB n w.val r.val) σ)) ≤
      (Scalar.survivorMoment n w.val p z) ^ α *
        sandwichedTrace (α) ρ σ := by
  have hwn : w.val ≤ n := Nat.le_of_lt_succ w.isLt
  let f : ℕ → ℝ := fun r => (physicalSurvivorProbabilityB p w.val r) ^ α *
    (if hr : r ≤ w.val then optimizedPhaseLawB n w.val p z ⟨r, Nat.lt_succ_of_le hr⟩ else 0) ^
      (1 - α) * sandwichedTrace (α)
        (labTransferOutput (lossKrausB n w.val r) ρ)
        (labTransferOutput (measurePhaseKrausB n w.val r) σ)
  have hCut : (∑ r : Fin (n + 1), f r.val) = ∑ r : Fin (w.val + 1), f r.val := by
    apply sum_uniform_survivorA n w.val hwn f
    intro r hr
    simp only [f, physicalSurvivorProbabilityB_zeroC p w.val r hr,
      Real.zero_rpow (by linarith : α ≠ 0), zero_mul]
  have h := fixedWeight_optimized_flagged_sandwichedTrace_le_of_order n w.val hwn hA hB
    hρ hσ hs hp0 hp1 hα hαz
  change sandwichedTrace (α)
    (labFlagComparator (fun j : Fin 1 × Fin (w.val + 1) => physicalPhaseLawB p w.val j.2)
      (fun j => labTransferOutput (lossKrausB n w.val j.2.val) ρ))
    (labFlagComparator (fun j : Fin 1 × Fin (w.val + 1) => optimizedPhaseLawB n w.val p z j.2)
      (fun j => labTransferOutput (measurePhaseKrausB n w.val j.2.val) σ)) ≤
    (Scalar.survivorMoment n w.val p z) ^ α *
      sandwichedTrace (α) ρ σ at h
  rw [labFlagComparator_sandwichedTrace_unequal
    (fun j : Fin 1 × Fin (w.val + 1) => physicalPhaseLawB p w.val j.2)
    (fun j : Fin 1 × Fin (w.val + 1) => optimizedPhaseLawB n w.val p z j.2)
    (fun j => labTransferOutput (lossKrausB n w.val j.2.val) ρ)
    (fun j => labTransferOutput (measurePhaseKrausB n w.val j.2.val) σ)
    (fun j => physicalPhaseLawB_nonneg p hp0 hp1 w.val j.2)
    (fun j => optimizedPhaseLawB_nonneg n w.val hwn p hp0 hp1 z j.2)
    (fun j => optimizedPhaseLawB_support n w.val hwn p hp0 hp1 z j.2)
    (fun _ => krausSumB_posSemidef _ hρ) (fun _ => krausSumB_posSemidef _ hσ) hα.le] at h
  have hLeft : (∑ r : Fin (n + 1), (recordedFlagLawC n p (w, r)) ^ α *
      (optimizedRecordedFlagLaw n p z (w, r)) ^ (1 - α) *
      sandwichedTrace (α)
        (labTransferOutput (lossKrausB n w.val r.val) ρ)
        (labTransferOutput (measurePhaseKrausB n w.val r.val) σ)) = ∑ r : Fin (n + 1), f r.val := by
    simp only [recordedFlagLawC_eq_physical, optimizedRecordedFlagLaw, f]
  rw [hLeft, hCut]
  simpa only [Fintype.sum_prod_type, Fin.sum_univ_one, physicalPhaseLawB,
    f, dite_eq_left (Nat.le_of_lt_succ (Fin.isLt _))] using h

theorem flaggedRecordedOutputC_optimized_sandwichedTrace_leA_of_order
    (hA : 0 < Fintype.card A) (hB : 0 < Fintype.card B)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {α : ℝ} (hα : 1 < α) (hαz : α * z = α - 1)
    {ρ σ : Matrix ((A × Finset (Fin n)) × B) ((A × Finset (Fin n)) × B) ℂ}
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) (hs : SupportLE ρ σ) :
    sandwichedTrace (α) (flaggedRecordedOutputC n p A B ρ)
      (optimizedFlaggedPhaseOutput n p z A B σ) ≤
        (typeMomentMaxA n p z) ^ α *
          sandwichedTrace (α) ρ σ := by
  let R := fun w : Fin (n + 1) => typeCopyLabC n w.val A B
  let ρw := fun w : Fin (n + 1) => R w * ρ * (R w)ᴴ
  let σw := fun w : Fin (n + 1) => R w * σ * (R w)ᴴ
  have hρw (w : Fin (n + 1)) : (ρw w).PosSemidef := hρ.mul_mul_conjTranspose_same (R w)
  have hσw (w : Fin (n + 1)) : (σw w).PosSemidef := hσ.mul_mul_conjTranspose_same (R w)
  have hsw (w : Fin (n + 1)) : SupportLE (ρw w) (σw w) :=
    supportLE_conjugationA (R w) hρ hσ hs
  have hA' : 0 < Fintype.card (A × Finset (Fin n)) := by
    rw [Fintype.card_prod]
    exact Nat.mul_pos hA Fintype.card_pos
  unfold flaggedRecordedOutputC optimizedFlaggedPhaseOutput
  simp_rw [recordedLossBranchC_fin_eq_labTransfer, recordedPhaseBranchC_fin_eq_labTransfer]
  rw [labFlagComparator_sandwichedTrace_unequal
    (recordedFlagLawC n p) (optimizedRecordedFlagLaw n p z)
    (fun j => labTransferOutput (lossKrausB n j.1.val j.2.val) (ρw j.1))
    (fun j => labTransferOutput (measurePhaseKrausB n j.1.val j.2.val) (σw j.1))
    (recordedFlagLawC_nonnegA n p hp0 hp1) (optimizedRecordedFlagLaw_nonneg n p hp0 hp1 z)
    (optimizedRecordedFlagLaw_support n p hp0 hp1 z)
    (fun j => krausSumB_posSemidef _ (hρw j.1))
    (fun j => krausSumB_posSemidef _ (hσw j.1)) hα.le]
  rw [Fintype.sum_prod_type]
  calc
    _ ≤ ∑ w : Fin (n + 1), (Scalar.survivorMoment n w.val p z) ^ α *
        sandwichedTrace (α) (ρw w) (σw w) := by
      apply Finset.sum_le_sum
      intro w _
      exact optimized_uniform_sector_Q_leA_of_order n p z (A × Finset (Fin n)) B w hA' hB
        hp0 hp1 (α := α) hα hαz (ρ := ρw w) (σ := σw w) (hρw w) (hσw w) (hsw w)
    _ ≤ ∑ w : Fin (n + 1), (typeMomentMaxA n p z) ^ α *
        sandwichedTrace (α) (ρw w) (σw w) := by
      apply Finset.sum_le_sum
      intro w _
      exact mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow (survivorMoment_nonnegA n w.val hp0 hp1 z)
          (survivorMoment_le_typeMomentMaxA n p z w) (zero_le_one.trans hα.le))
        (sandwichedTrace_nonneg (hρw w) α)
    _ = (typeMomentMaxA n p z) ^ α *
        (∑ w : Fin (n + 1), sandwichedTrace (α) (ρw w) (σw w)) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (sandwichedTrace_branch_sum_le R (typeCopyLabC_complete n A B) hρ hσ hs hα)
      (Real.rpow_nonneg (zero_le_one.trans (one_le_typeMomentMaxA n p z)) _)

theorem flaggedRecordedOutputC_optimized_sandwichedTrace_leA
    (hA : 0 < Fintype.card A) (hB : 0 < Fintype.card B)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hz0 : 0 < z) (hz1 : z < 1)
    {ρ σ : Matrix ((A × Finset (Fin n)) × B) ((A × Finset (Fin n)) × B) ℂ}
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) (hs : SupportLE ρ σ) :
    sandwichedTrace (optimizedBlockOrderA z) (flaggedRecordedOutputC n p A B ρ)
      (optimizedFlaggedPhaseOutput n p z A B σ) ≤
        (typeMomentMaxA n p z) ^ optimizedBlockOrderA z *
          sandwichedTrace (optimizedBlockOrderA z) ρ σ := by
  have hαz : optimizedBlockOrderA z * z = optimizedBlockOrderA z - 1 := by
    unfold optimizedBlockOrderA
    field_simp [(sub_pos.mpr hz1).ne']
    ring
  exact flaggedRecordedOutputC_optimized_sandwichedTrace_leA_of_order n p z A B hA hB
    hp0 hp1 (optimizedBlockOrderA_gt_one hz0 hz1) hαz hρ hσ hs

theorem optimizedFlaggedPhaseOutput_posSemidefA (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {σ : Matrix ((A × Finset (Fin n)) × B) ((A × Finset (Fin n)) × B) ℂ}
    (hσ : σ.PosSemidef) : (optimizedFlaggedPhaseOutput n p z A B σ).PosSemidef := by
  unfold optimizedFlaggedPhaseOutput
  apply labFlagComparator_posSemidefA _ _ (optimizedRecordedFlagLaw_nonneg n p hp0 hp1 z)
  intro j
  rw [recordedPhaseBranchC_fin_eq_labTransfer]
  exact krausSumB_posSemidef _ (hσ.mul_mul_conjTranspose_same _)

theorem flaggedRecordedOutputC_optimized_supportLEA (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {ρ σ : Matrix ((A × Finset (Fin n)) × B) ((A × Finset (Fin n)) × B) ℂ}
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) (hs : SupportLE ρ σ) :
    SupportLE (flaggedRecordedOutputC n p A B ρ) (optimizedFlaggedPhaseOutput n p z A B σ) := by
  unfold flaggedRecordedOutputC optimizedFlaggedPhaseOutput
  simp_rw [recordedLossBranchC_fin_eq_labTransfer, recordedPhaseBranchC_fin_eq_labTransfer]
  apply labFlagComparator_supportLE _ _ _ _
    (recordedFlagLawC_nonnegA n p hp0 hp1) (optimizedRecordedFlagLaw_nonneg n p hp0 hp1 z)
    (optimizedRecordedFlagLaw_support n p hp0 hp1 z)
  · intro j
    exact krausSumB_posSemidef _ (hρ.mul_mul_conjTranspose_same (typeCopyLabC n j.1.val A B))
  · intro j
    exact krausSumB_posSemidef _ (hσ.mul_mul_conjTranspose_same (typeCopyLabC n j.1.val A B))
  · intro j hj
    have hrw : j.2.val ≤ j.1.val := by
      by_contra h
      exact hj (by simp [recordedFlagLawC, h])
    have hrn : j.2.val ≤ n := Nat.le_of_lt_succ j.2.isLt
    let ρw := typeCopyLabC n j.1.val A B * ρ * (typeCopyLabC n j.1.val A B)ᴴ
    let σw := typeCopyLabC n j.1.val A B * σ * (typeCopyLabC n j.1.val A B)ᴴ
    have hρw : ρw.PosSemidef := hρ.mul_mul_conjTranspose_same _
    have hσw : σw.PosSemidef := hσ.mul_mul_conjTranspose_same _
    have hsN := labTransferOutput_supportLE (lossKrausB n j.1.val j.2.val)
      hρw hσw (supportLE_conjugationA _ hρ hσ hs)
    have hc := phaseComparisonConstantB_pos n j.1.val j.2.val hrw hrn
    have hN := krausSumB_posSemidef (labTransferKraus (lossKrausB n j.1.val j.2.val)) hσw
    have hS := krausSumB_posSemidef (labTransferKraus (measurePhaseKrausB n j.1.val j.2.val)) hσw
    have ho := supportLE_of_loewner hN (hS.smul hc.le)
      (labTransferOutput_loss_phase_domination n j.1.val j.2.val hrw hrn
        (A × Finset (Fin n)) B hσw)
    exact (supportLE_smul_comparison_iff
      (krausSumB_posSemidef (labTransferKraus (lossKrausB n j.1.val j.2.val)) hρw).1
      hS hc).mp (hsN.trans ho)

theorem pinchedRecordedOutputC_optimized_supportLEA (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {ρ σ : Matrix ((A × Finset (Fin n)) × B) ((A × Finset (Fin n)) × B) ℂ}
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) (hs : SupportLE ρ σ) :
    SupportLE (pinchedRecordedOutputC n p A B ρ) (optimizedPhaseRecordedOutput n p z A B σ) := by
  have h := (eraseLabFlagsProtocolC p (n + 1) (n + 1)
    (Fintype.card (A × Finset (Fin n))) (Fintype.card (Finset (Fin n) × B))).output_supportLE
    (flaggedRecordedOutputC_posSemidefA n p A B hp0 hp1 hρ)
    (optimizedFlaggedPhaseOutput_posSemidefA n p z A B hp0 hp1 hσ)
    (flaggedRecordedOutputC_optimized_supportLEA n p z A B hp0 hp1 hρ hσ hs)
  rw [flaggedRecordedOutputC_erase n p A B hp0 hp1,
    optimizedFlaggedPhaseOutput_erase n p z A B hp0 hp1] at h
  exact (SupportLE.submatrix_equiv_iff (recordedOutputEquivC n A B)).mp h

theorem pinchedRecordedOutputC_optimized_sandwichedTrace_leA
    (hA : 0 < Fintype.card A) (hB : 0 < Fintype.card B)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hz0 : 0 < z) (hz1 : z < 1)
    {ρ σ : Matrix ((A × Finset (Fin n)) × B) ((A × Finset (Fin n)) × B) ℂ}
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) (hs : SupportLE ρ σ) :
    sandwichedTrace (optimizedBlockOrderA z) (pinchedRecordedOutputC n p A B ρ)
      (optimizedPhaseRecordedOutput n p z A B σ) ≤
        (typeMomentMaxA n p z) ^ optimizedBlockOrderA z * sandwichedTrace (optimizedBlockOrderA z) ρ σ := by
  have hα := optimizedBlockOrderA_gt_one hz0 hz1
  have h := (eraseLabFlagsProtocolC p (n + 1) (n + 1)
    (Fintype.card (A × Finset (Fin n))) (Fintype.card (Finset (Fin n) × B))).sandwichedTrace_output_le
    hp0 hp1 (flaggedRecordedOutputC_posSemidefA n p A B hp0 hp1 hρ)
    (optimizedFlaggedPhaseOutput_posSemidefA n p z A B hp0 hp1 hσ)
    (flaggedRecordedOutputC_optimized_supportLEA n p z A B hp0 hp1 hρ hσ hs) hα
  have hpin : (pinchedRecordedOutputC n p A B ρ).PosSemidef :=
    krausSumB_posSemidef _ (recordedOutputC_posSemidef n p A B hρ)
  rw [flaggedRecordedOutputC_erase n p A B hp0 hp1,
    optimizedFlaggedPhaseOutput_erase n p z A B hp0 hp1,
    TensorPower.sandwichedTrace_submatrix_equiv hpin
      (optimizedPhaseRecordedOutput_posSemidef n p z A B hσ)] at h
  exact h.trans (flaggedRecordedOutputC_optimized_sandwichedTrace_leA n p z A B hA hB
    hp0 hp1 hz0 hz1 hρ hσ hs)

theorem recordedOutputC_optimized_supportLEA (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {ρ σ : Matrix ((A × Finset (Fin n)) × B) ((A × Finset (Fin n)) × B) ℂ}
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) (hs : SupportLE ρ σ) :
    SupportLE (recordedOutputC n p A B ρ) (optimizedPhaseRecordedOutput n p z A B σ) := by
  have hΩ := recordedOutputC_posSemidef n p A B hρ
  have hPΩ : (pinchedRecordedOutputC n p A B ρ).PosSemidef := krausSumB_posSemidef _ hΩ
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have horder := QuantumProver.SuperchannelDiscrimination.Pinching.le_card_smul_pinching
    (recordWeightOutputC_family n A B) hΩ
  rw [Fintype.card_fin, Nat.cast_add, Nat.cast_one,
    ← pinchedRecordedOutputC_eq_pinchingMap] at horder
  have hSP := supportLE_of_loewner hΩ (hPΩ.smul hn.le) horder
  have hΩP := (supportLE_smul_comparison_iff hΩ.1 hPΩ hn).mp hSP
  exact hΩP.trans (pinchedRecordedOutputC_optimized_supportLEA n p z A B hp0 hp1 hρ hσ hs)

theorem recordedOutputC_optimized_sandwichedTrace_leA
    (hA : 0 < Fintype.card A) (hB : 0 < Fintype.card B)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hz0 : 0 < z) (hz1 : z < 1)
    {ρ σ : Matrix ((A × Finset (Fin n)) × B) ((A × Finset (Fin n)) × B) ℂ}
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) (hs : SupportLE ρ σ) :
    sandwichedTrace (optimizedBlockOrderA z) (recordedOutputC n p A B ρ)
      (optimizedPhaseRecordedOutput n p z A B σ) ≤
        optimizedBlockQFactorA n p z * sandwichedTrace (optimizedBlockOrderA z) ρ σ := by
  have hα := optimizedBlockOrderA_gt_one hz0 hz1
  have hPin := sandwichedTrace_pinching_bound (recordWeightOutputC_family n A B)
    (recordedOutputC_posSemidef n p A B hρ) (optimizedPhaseRecordedOutput n p z A B σ) hα.le
  rw [Fintype.card_fin, Nat.cast_add, Nat.cast_one,
    ← pinchedRecordedOutputC_eq_pinchingMap] at hPin
  have hQ := mul_le_mul_of_nonneg_left
    (pinchedRecordedOutputC_optimized_sandwichedTrace_leA n p z A B hA hB hp0 hp1 hz0 hz1 hρ hσ hs)
    (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1) (optimizedBlockOrderA z))
  exact hPin.trans (hQ.trans_eq (by unfold optimizedBlockQFactorA; ring))

theorem physicalOutput_sandwichedTrace_recoveredOptimizedPhase_leA
    (hA : 0 < Fintype.card A) (hB : 0 < Fintype.card B)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hz0 : 0 < z) (hz1 : z < 1)
    {ρ σ : Matrix ((A × Finset (Fin n)) × B) ((A × Finset (Fin n)) × B) ℂ}
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) (hs : SupportLE ρ σ) :
    sandwichedTrace (optimizedBlockOrderA z) (labTransferOutput (tensorDampingKrausB n p) ρ)
      (recoveredOptimizedPhaseOutput n p z A B σ) ≤
        optimizedBlockQFactorA n p z * sandwichedTrace (optimizedBlockOrderA z) ρ σ := by
  have hΩ := recordedOutputC_posSemidef n p A B hρ
  have hκ := optimizedPhaseRecordedOutput_posSemidef n p z A B hσ
  have h := (fullRecordRecoveryProtocolB p n A B).sandwichedTrace_output_le hp0 hp1
    (hΩ.submatrix _) (hκ.submatrix _)
    ((recordedOutputC_optimized_supportLEA n p z A B hp0 hp1 hρ hσ hs).submatrix_equiv
      (recordedOutputEquivC n A B)) (optimizedBlockOrderA_gt_one hz0 hz1)
  rw [recordedOutputC_matrix_recovery, ← recoveredOptimizedPhaseOutput,
    TensorPower.sandwichedTrace_submatrix_equiv hΩ hκ] at h
  exact h.trans (recordedOutputC_optimized_sandwichedTrace_leA n p z A B hA hB hp0 hp1 hz0 hz1 hρ hσ hs)

theorem physicalOutput_supportLE_recoveredOptimizedA (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {ρ σ : Matrix ((A × Finset (Fin n)) × B) ((A × Finset (Fin n)) × B) ℂ}
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) (hs : SupportLE ρ σ) :
    SupportLE (labTransferOutput (tensorDampingKrausB n p) ρ)
      (recoveredOptimizedPhaseOutput n p z A B σ) := by
  have h := (fullRecordRecoveryProtocolB p n A B).output_supportLE
    ((recordedOutputC_posSemidef n p A B hρ).submatrix _)
    ((optimizedPhaseRecordedOutput_posSemidef n p z A B hσ).submatrix _)
    ((recordedOutputC_optimized_supportLEA n p z A B hp0 hp1 hρ hσ hs).submatrix_equiv
      (recordedOutputEquivC n A B))
  rwa [recordedOutputC_matrix_recovery, ← recoveredOptimizedPhaseOutput] at h

end ActualOptimizedFlags

theorem matrixPhysicalBlockOutput_supportLE_optimizedA (n : ℕ) (p z : ℝ) (a b : ℕ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {ρ σ : BipartiteMatrix (doubleDimB n a) b}
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) (hs : SupportLE ρ σ) :
    SupportLE (matrixPhysicalBlockOutput n p a b ρ)
      (matrixOptimizedPhaseBlockOutput n p z a b σ) := by
  let eI := matrixBlockInputEquiv n a b
  let eO := matrixBlockOutputEquiv n a b
  let eF := (finiteIndexB (Fin a)).prodCongr (finiteIndexB (Finset (Fin n) × Fin b))
  have h := physicalOutput_supportLE_recoveredOptimizedA n p z (Fin a) (Fin b) hp0 hp1
    (hρ.submatrix eI.symm) (hσ.submatrix eI.symm) (hs.submatrix_equiv eI.symm)
  rw [labTransferOutput_eq_transferLabC, recoveredOptimizedPhaseOutput_eq_krausSum] at h
  have hRaw := h.submatrix_equiv eF.symm
  have hCancel (M : Matrix (Fin a × (Finset (Fin n) × Fin b))
      (Fin a × (Finset (Fin n) × Fin b)) ℂ) :
      (M.submatrix eF eF).submatrix eF.symm eF.symm = M := by
    ext x y
    simp
  rw [hCancel, hCancel] at hRaw
  rw [matrixPhysicalBlockOutput_eq_raw, matrixOptimizedPhaseBlockOutput_eq_labKrausSum]
  exact hRaw.submatrix_equiv eO

theorem matrixPhysicalBlockOutput_sandwichedTrace_optimized_leA
    (n : ℕ) (p z : ℝ) (a b : ℕ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hz0 : 0 < z) (hz1 : z < 1)
    {ρ σ : BipartiteMatrix (doubleDimB n a) b}
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) (hs : SupportLE ρ σ) :
    sandwichedTrace (optimizedBlockOrderA z) (matrixPhysicalBlockOutput n p a b ρ)
      (matrixOptimizedPhaseBlockOutput n p z a b σ) ≤
      optimizedBlockQFactorA n p z * sandwichedTrace (optimizedBlockOrderA z) ρ σ := by
  have hα := optimizedBlockOrderA_gt_one hz0 hz1
  by_cases ha : 0 < a
  · by_cases hb : 0 < b
    · let eI := matrixBlockInputEquiv n a b
      have hρr := hρ.submatrix eI.symm
      have hσr := hσ.submatrix eI.symm
      have hN := krausSumB_posSemidef
        (transferLabKrausC (A := Fin a) (B := Fin b) (tensorDampingKrausB n p)) hρr
      have hT := krausSumB_posSemidef
        (recoveredOptimizedPhaseLabKraus n p z (Fin a) (Fin b)) hσr
      have h := physicalOutput_sandwichedTrace_recoveredOptimizedPhase_leA n p z (Fin a) (Fin b)
        (by simpa using ha) (by simpa using hb) hp0 hp1 hz0 hz1 hρr hσr
        (hs.submatrix_equiv eI.symm)
      rw [labTransferOutput_eq_transferLabC, recoveredOptimizedPhaseOutput_eq_krausSum,
        TensorPower.sandwichedTrace_submatrix_equiv hN hT,
        TensorPower.sandwichedTrace_submatrix_equiv hρ hσ] at h
      rw [matrixPhysicalBlockOutput_eq_raw, matrixOptimizedPhaseBlockOutput_eq_labKrausSum,
        TensorPower.sandwichedTrace_submatrix_equiv hN hT]
      exact h
    · have hb0 : b = 0 := Nat.eq_zero_of_not_pos hb
      subst b
      have hzero : ρ = 0 := by
        ext x y
        exact Fin.elim0 x.2
      rw [hzero]
      simp [matrixPhysicalBlockOutput, krausSumB, sandwichedTrace_zero_input _
        (by linarith : 0 < optimizedBlockOrderA z)]
  · have ha0 : a = 0 := Nat.eq_zero_of_not_pos ha
    subst a
    have hzero : ρ = 0 := by
      ext x y
      exact Fin.elim0 ((matrixBlockInputAliceEquiv n 0) x.1).1
    rw [hzero]
    simp [matrixPhysicalBlockOutput, krausSumB, sandwichedTrace_zero_input _
      (by linarith : 0 < optimizedBlockOrderA z)]

theorem FiniteBlockProtocolB.output_supportLE_optimizedA {p : ℝ} {n a b af bf : ℕ}
    (P : FiniteBlockProtocolB p n a b af bf) (z : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {ρ σ : BipartiteMatrix a b} (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef)
    (hs : SupportLE ρ σ) : SupportLE (P.output ρ) (P.optimizedPhaseOutput z σ) := by
  induction P with
  | done a b => exact hs
  | alice K next ih =>
    apply supportLE_sumA
    · intro j; exact (next j).output_posSemidefA (hρ.mul_mul_conjTranspose_same _)
    · intro j; exact (next j).optimizedPhaseOutput_posSemidef z (hσ.mul_mul_conjTranspose_same _)
    · intro j
      exact ih j (hρ.mul_mul_conjTranspose_same _) (hσ.mul_mul_conjTranspose_same _)
        (supportLE_conjugationA _ hρ hσ hs)
  | bob K next ih =>
    apply supportLE_sumA
    · intro j; exact (next j).output_posSemidefA (hρ.mul_mul_conjTranspose_same _)
    · intro j; exact (next j).optimizedPhaseOutput_posSemidef z (hσ.mul_mul_conjTranspose_same _)
    · intro j
      exact ih j (hρ.mul_mul_conjTranspose_same _) (hσ.mul_mul_conjTranspose_same _)
        (supportLE_conjugationA _ hρ hσ hs)
  | blockCall next ih =>
    rw [FiniteBlockProtocolB.output, FiniteBlockProtocolB.optimizedPhaseOutput,
      sequentialCallsKrausB_output_eq_matrix_block]
    exact ih (matrixPhysicalBlockOutput_posSemidef _ _ _ _ hρ)
      (matrixOptimizedPhaseBlockOutput_posSemidef _ _ _ _ _ hσ)
      (matrixPhysicalBlockOutput_supportLE_optimizedA _ _ _ _ _ hp0 hp1 hρ hσ hs)

theorem FiniteBlockProtocolB.sandwichedTrace_output_optimized_leA
    {p : ℝ} {n a b af bf : ℕ} (P : FiniteBlockProtocolB p n a b af bf)
    (z : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hz0 : 0 < z) (hz1 : z < 1)
    {ρ σ : BipartiteMatrix a b} (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef)
    (hs : SupportLE ρ σ) :
    sandwichedTrace (optimizedBlockOrderA z) (P.output ρ) (P.optimizedPhaseOutput z σ) ≤
      optimizedBlockQFactorA n p z ^ P.calls * sandwichedTrace (optimizedBlockOrderA z) ρ σ := by
  have hα := optimizedBlockOrderA_gt_one hz0 hz1
  have hF : 1 ≤ optimizedBlockQFactorA n p z := one_le_optimizedBlockQFactorA n p hz0 hz1
  have hF0 : 0 ≤ optimizedBlockQFactorA n p z := zero_le_one.trans hF
  induction P with
  | done a b => simp [FiniteBlockProtocolB.output, FiniteBlockProtocolB.optimizedPhaseOutput,
      FiniteBlockProtocolB.calls]
  | @alice a b ao af bf k K next ih =>
    let R := fun j => aliceOperator (b := b) (K.operator j)
    have hRρ (j : Fin k) := hρ.mul_mul_conjTranspose_same (R j)
    have hRσ (j : Fin k) := hσ.mul_mul_conjTranspose_same (R j)
    have hRs (j : Fin k) := supportLE_conjugationA (R j) hρ hσ hs
    have hBranch := sandwichedTrace_branch_sum_le R (aliceOperator_gram K) hρ hσ hs hα
    change sandwichedTrace (optimizedBlockOrderA z) (∑ j, (next j).output (R j * ρ * (R j)ᴴ))
      (∑ j, (next j).optimizedPhaseOutput z (R j * σ * (R j)ᴴ)) ≤ _
    calc
      _ ≤ ∑ j, sandwichedTrace (optimizedBlockOrderA z) ((next j).output (R j * ρ * (R j)ᴴ))
          ((next j).optimizedPhaseOutput z (R j * σ * (R j)ᴴ)) :=
        sandwichedTrace_sum_leA _ _
          (fun j => (next j).output_posSemidefA (hRρ j))
          (fun j => (next j).optimizedPhaseOutput_posSemidef z (hRσ j))
          (fun j => (next j).output_supportLE_optimizedA z hp0 hp1 (hRρ j) (hRσ j) (hRs j)) hα
      _ ≤ ∑ j, optimizedBlockQFactorA n p z ^ (Finset.univ.sup fun j => (next j).calls) *
          sandwichedTrace (optimizedBlockOrderA z) (R j * ρ * (R j)ᴴ) (R j * σ * (R j)ᴴ) := by
        apply Finset.sum_le_sum
        intro j hj
        exact (ih j (hRρ j) (hRσ j) (hRs j)).trans
          (mul_le_mul_of_nonneg_right
            (pow_le_pow_right₀ hF (Finset.le_sup (f := fun j => (next j).calls) hj))
            (sandwichedTrace_nonneg (hRρ j) (optimizedBlockOrderA z)))
      _ = optimizedBlockQFactorA n p z ^ (Finset.univ.sup fun j => (next j).calls) *
          (∑ j, sandwichedTrace (optimizedBlockOrderA z) (R j * ρ * (R j)ᴴ) (R j * σ * (R j)ᴴ)) :=
        (Finset.mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hBranch (pow_nonneg hF0 _)
  | @bob a b bo af bf k K next ih =>
    let R := fun j => bobOperator (a := a) (K.operator j)
    have hRρ (j : Fin k) := hρ.mul_mul_conjTranspose_same (R j)
    have hRσ (j : Fin k) := hσ.mul_mul_conjTranspose_same (R j)
    have hRs (j : Fin k) := supportLE_conjugationA (R j) hρ hσ hs
    have hBranch := sandwichedTrace_branch_sum_le R (bobOperator_gram K) hρ hσ hs hα
    change sandwichedTrace (optimizedBlockOrderA z) (∑ j, (next j).output (R j * ρ * (R j)ᴴ))
      (∑ j, (next j).optimizedPhaseOutput z (R j * σ * (R j)ᴴ)) ≤ _
    calc
      _ ≤ ∑ j, sandwichedTrace (optimizedBlockOrderA z) ((next j).output (R j * ρ * (R j)ᴴ))
          ((next j).optimizedPhaseOutput z (R j * σ * (R j)ᴴ)) :=
        sandwichedTrace_sum_leA _ _
          (fun j => (next j).output_posSemidefA (hRρ j))
          (fun j => (next j).optimizedPhaseOutput_posSemidef z (hRσ j))
          (fun j => (next j).output_supportLE_optimizedA z hp0 hp1 (hRρ j) (hRσ j) (hRs j)) hα
      _ ≤ ∑ j, optimizedBlockQFactorA n p z ^ (Finset.univ.sup fun j => (next j).calls) *
          sandwichedTrace (optimizedBlockOrderA z) (R j * ρ * (R j)ᴴ) (R j * σ * (R j)ᴴ) := by
        apply Finset.sum_le_sum
        intro j hj
        exact (ih j (hRρ j) (hRσ j) (hRs j)).trans
          (mul_le_mul_of_nonneg_right
            (pow_le_pow_right₀ hF (Finset.le_sup (f := fun j => (next j).calls) hj))
            (sandwichedTrace_nonneg (hRρ j) (optimizedBlockOrderA z)))
      _ = optimizedBlockQFactorA n p z ^ (Finset.univ.sup fun j => (next j).calls) *
          (∑ j, sandwichedTrace (optimizedBlockOrderA z) (R j * ρ * (R j)ᴴ) (R j * σ * (R j)ᴴ)) :=
        (Finset.mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hBranch (pow_nonneg hF0 _)
  | @blockCall a b af bf next ih =>
    rw [FiniteBlockProtocolB.output, FiniteBlockProtocolB.optimizedPhaseOutput,
      sequentialCallsKrausB_output_eq_matrix_block, FiniteBlockProtocolB.calls]
    calc
      _ ≤ optimizedBlockQFactorA n p z ^ next.calls *
          sandwichedTrace (optimizedBlockOrderA z) (matrixPhysicalBlockOutput n p a b ρ)
            (matrixOptimizedPhaseBlockOutput n p z a b σ) :=
        ih (matrixPhysicalBlockOutput_posSemidef _ _ _ _ hρ)
          (matrixOptimizedPhaseBlockOutput_posSemidef _ _ _ _ _ hσ)
          (matrixPhysicalBlockOutput_supportLE_optimizedA _ _ _ _ _ hp0 hp1 hρ hσ hs)
      _ ≤ optimizedBlockQFactorA n p z ^ next.calls *
          (optimizedBlockQFactorA n p z * sandwichedTrace (optimizedBlockOrderA z) ρ σ) :=
        mul_le_mul_of_nonneg_left
          (matrixPhysicalBlockOutput_sandwichedTrace_optimized_leA n p z a b hp0 hp1 hz0 hz1 hρ hσ hs)
          (pow_nonneg hF0 _)
      _ = _ := by rw [pow_succ]; ring

theorem optimizedBlockLogChargeA_nonneg (n : ℕ) (p : ℝ) {z : ℝ}
    (hz0 : 0 < z) (hz1 : z < 1) : 0 ≤ optimizedBlockLogChargeA n p z := by
  rw [← log_optimizedBlockQFactorA n p hz0 hz1]
  exact div_nonneg
    (div_nonneg (Real.log_nonneg (one_le_optimizedBlockQFactorA n p hz0 hz1))
      (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le)
    (sub_pos.mpr (optimizedBlockOrderA_gt_one hz0 hz1)).le

theorem FiniteBlockProtocolB.sandwichedDivergence_output_optimized_leA
    {p : ℝ} {n a b af bf : ℕ} (P : FiniteBlockProtocolB p n a b af bf)
    (z : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hz0 : 0 < z) (hz1 : z < 1)
    {ρ σ : BipartiteMatrix a b} (hρ : IsDensity ρ) (hσ : IsDensity σ) (hs : SupportLE ρ σ) :
    sandwichedDivergence (optimizedBlockOrderA z) (P.output ρ) (P.optimizedPhaseOutput z σ) ≤
      sandwichedDivergence (optimizedBlockOrderA z) ρ σ +
        (((P.calls : ℝ) * optimizedBlockLogChargeA n p z : ℝ) : EReal) := by
  have hα := optimizedBlockOrderA_gt_one hz0 hz1
  have hF : 0 < optimizedBlockQFactorA n p z :=
    zero_lt_one.trans_le (one_le_optimizedBlockQFactorA n p hz0 hz1)
  have h := sandwichedDivergence_le_of_Q_factorA hρ hσ
    ⟨P.output_posSemidefA hρ.1, (P.output_traceA hp0 hp1 ρ).trans hρ.2⟩
    (P.optimizedPhaseOutput_isDensity z hp0 hp1 hσ) hs
    (P.output_supportLE_optimizedA z hp0 hp1 hρ.1 hσ.1 hs) hα (pow_pos hF P.calls)
    (P.sandwichedTrace_output_optimized_leA z hp0 hp1 hz0 hz1 hρ.1 hσ.1 hs)
  have hlog : logTwo (optimizedBlockQFactorA n p z ^ P.calls) / (optimizedBlockOrderA z - 1) =
      (P.calls : ℝ) * optimizedBlockLogChargeA n p z := by
    calc
      _ = (P.calls : ℝ) * (logTwo (optimizedBlockQFactorA n p z) /
          (optimizedBlockOrderA z - 1)) := by
        unfold logTwo
        rw [Real.log_pow]
        ring
      _ = _ := by rw [log_optimizedBlockQFactorA n p hz0 hz1]
  rwa [hlog] at h

theorem FiniteBlockProtocolB.sandwichedEntanglement_output_optimized_le_of_leA
    {p : ℝ} {n a b af bf : ℕ} (P : FiniteBlockProtocolB p n a b af bf)
    (z : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hz0 : 0 < z) (hz1 : z < 1)
    {ρ : BipartiteMatrix a b} (hρ : IsDensity ρ) {e : ℝ}
    (hE : sandwichedEntanglement (optimizedBlockOrderA z) a b ρ ≤ (e : EReal)) :
    sandwichedEntanglement (optimizedBlockOrderA z) af bf (P.output ρ) ≤
      ((e + (P.calls : ℝ) * optimizedBlockLogChargeA n p z : ℝ) : EReal) := by
  apply EReal.le_of_forall_lt_iff_le.mp
  intro t ht
  have htR : e + (P.calls : ℝ) * optimizedBlockLogChargeA n p z < t :=
    EReal.coe_lt_coe_iff.mp ht
  let ε := t - (e + (P.calls : ℝ) * optimizedBlockLogChargeA n p z)
  have hε : 0 < ε := sub_pos.mpr htR
  have hElt : sandwichedEntanglement (optimizedBlockOrderA z) a b ρ < ((e + ε : ℝ) : EReal) :=
    hE.trans_lt (EReal.coe_lt_coe_iff.mpr (by linarith))
  obtain ⟨σ, hσ, hsep, hs, hD⟩ := exists_separable_comparison_divergence_lt ρ hElt
  calc
    _ ≤ sandwichedDivergence (optimizedBlockOrderA z) (P.output ρ) (P.optimizedPhaseOutput z σ) :=
      sandwichedEntanglement_le_comparison _ (P.optimizedPhaseOutput_isDensity z hp0 hp1 hσ)
        (P.optimizedPhaseOutput_isSeparable z hp0 hp1 hsep) (optimizedBlockOrderA z)
    _ ≤ sandwichedDivergence (optimizedBlockOrderA z) ρ σ +
        (((P.calls : ℝ) * optimizedBlockLogChargeA n p z : ℝ) : EReal) :=
      P.sandwichedDivergence_output_optimized_leA z hp0 hp1 hz0 hz1 hρ hσ hs
    _ ≤ ((e + ε : ℝ) : EReal) +
        (((P.calls : ℝ) * optimizedBlockLogChargeA n p z : ℝ) : EReal) :=
      _root_.add_le_add hD.le le_rfl
    _ = (t : EReal) := by
      rw [← EReal.coe_add]
      congr 1
      dsimp only [ε]
      ring

theorem FiniteBlockProtocolB.sandwichedEntanglement_output_optimized_le_of_calls_leA
    {p : ℝ} {n a b af bf m : ℕ} (P : FiniteBlockProtocolB p n a b af bf)
    (z : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hz0 : 0 < z) (hz1 : z < 1) (hP : P.calls ≤ m)
    {ρ : BipartiteMatrix a b} (hρ : IsDensity ρ) {e : ℝ}
    (hE : sandwichedEntanglement (optimizedBlockOrderA z) a b ρ ≤ (e : EReal)) :
    sandwichedEntanglement (optimizedBlockOrderA z) af bf (P.output ρ) ≤
      ((e + (m : ℝ) * optimizedBlockLogChargeA n p z : ℝ) : EReal) := by
  apply (P.sandwichedEntanglement_output_optimized_le_of_leA z hp0 hp1 hz0 hz1 hρ hE).trans
  apply EReal.coe_le_coe_iff.mpr
  exact _root_.add_le_add le_rfl
    (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hP) (optimizedBlockLogChargeA_nonneg n p hz0 hz1))

theorem FiniteBlockProtocolB.sandwichedEntanglement_output_optimized_le_uniformA
    {p : ℝ} {n a b af bf m : ℕ} (P : FiniteBlockProtocolB p n a b af bf)
    (z : ℝ) (hn : 0 < n) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hz0 : 0 < z) (hz1 : z < 1) (hP : P.calls ≤ m)
    {ρ : BipartiteMatrix a b} (hρ : IsDensity ρ) {e : ℝ}
    (hE : sandwichedEntanglement (optimizedBlockOrderA z) a b ρ ≤ (e : EReal)) :
    sandwichedEntanglement (optimizedBlockOrderA z) af bf (P.output ρ) ≤
      ((e + (m : ℝ) * ((n : ℝ) * converseBudget p z +
        (2 / z) * logTwo ((n : ℝ) + 1)) : ℝ) : EReal) := by
  apply (P.sandwichedEntanglement_output_optimized_le_of_calls_leA z hp0 hp1 hz0 hz1 hP hρ hE).trans
  apply EReal.coe_le_coe_iff.mpr
  exact _root_.add_le_add le_rfl (mul_le_mul_of_nonneg_left
    (optimizedBlockLogChargeA_le n hn hp0 hp1 hz0 hz1) (Nat.cast_nonneg m))

end QuantumProver.AmplitudeDamping.FiniteModel

import QuantumProver.InformationTheory.AmplitudeDamping.QuantumCapacity.BlockIncrement
import QuantumProver.InformationTheory.AmplitudeDamping.QuantumCapacity.ParallelScheduler
import QuantumProver.InformationTheory.AmplitudeDamping.QuantumCapacity.RecordRecovery

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix Kronecker

namespace QuantumProver.AmplitudeDamping.FiniteModel

section DependentBranchFlags

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  {H : J → Type*} [∀ j, Fintype (H j)] [∀ j, DecidableEq (H j)]

def branchStack (R : ∀ j, Matrix (H j) I ℂ) : Matrix (Σ j, H j) I ℂ :=
  fun x i => R x.1 x.2 i

def branchSelector (j : J) : Matrix (Σ j, H j) (Σ j, H j) ℂ :=
  Matrix.diagonal (fun x => if x.1 = j then 1 else 0)

def branchFlaggedKraus (R : ∀ j, Matrix (H j) I ℂ) (j : J) :
    Matrix (Σ j, H j) I ℂ :=
  fun x i => if x.1 = j then R x.1 x.2 i else 0

omit [Fintype I] [DecidableEq I] [Fintype J] [∀ j, Fintype (H j)]
  [∀ j, DecidableEq (H j)] in
theorem branchFlaggedKraus_apply (R : ∀ j, Matrix (H j) I ℂ)
    (j : J) (x : Σ j, H j) (i : I) :
    branchFlaggedKraus R j x i = if x.1 = j then R x.1 x.2 i else 0 := rfl

omit [DecidableEq I] [∀ j, Fintype (H j)] [∀ j, DecidableEq (H j)] in

theorem branchFlaggedOutput_eq_blockDiagonal' (R : ∀ j, Matrix (H j) I ℂ)
    (ρ : Matrix I I ℂ) :
    krausSumB (branchFlaggedKraus R) ρ =
      Matrix.blockDiagonal' (fun j => R j * ρ * (R j)ᴴ) := by
  ext ⟨j, x⟩ ⟨k, y⟩
  by_cases h : j = k
  · subst k
    rw [krausSumB, Matrix.sum_apply, Finset.sum_eq_single j]
    · simp [Matrix.mul_apply, Matrix.conjTranspose_apply, branchFlaggedKraus_apply,
        Matrix.blockDiagonal']
    · intro z _ hz
      simp [Matrix.mul_apply, Matrix.conjTranspose_apply, branchFlaggedKraus_apply,
        Ne.symm hz]
    · intro hj
      exact False.elim (hj (Finset.mem_univ j))
  · have hzero : (krausSumB (branchFlaggedKraus R) ρ) ⟨j, x⟩ ⟨k, y⟩ = 0 := by
      rw [krausSumB, Matrix.sum_apply]
      apply Finset.sum_eq_zero
      intro z _
      by_cases hjz : j = z
      · have hkz : k ≠ z := fun hkz => h (hjz.trans hkz.symm)
        simp [Matrix.mul_apply, Matrix.conjTranspose_apply, branchFlaggedKraus_apply,
          hkz]
      · simp [Matrix.mul_apply, Matrix.conjTranspose_apply, branchFlaggedKraus_apply,
          hjz]
    rw [hzero]
    simp [Matrix.blockDiagonal', h]

theorem branchFlaggedKraus_complete (R : ∀ j, Matrix (H j) I ℂ)
    (hR : ∑ j, (R j)ᴴ * R j = 1) :
    ∑ j, (branchFlaggedKraus R j)ᴴ * branchFlaggedKraus R j = 1 := by
  apply krausSumB_complete_of_trace
  intro ρ
  rw [branchFlaggedOutput_eq_blockDiagonal', Matrix.trace_blockDiagonal']
  calc
    _ = ∑ j, (((R j)ᴴ * R j) * ρ).trace := by
      apply Finset.sum_congr rfl
      intro j _
      exact Matrix.trace_mul_cycle _ _ _
    _ = ((∑ j, (R j)ᴴ * R j) * ρ).trace := by
      rw [Matrix.sum_mul, Matrix.trace_sum]
    _ = ρ.trace := by rw [hR, Matrix.one_mul]

theorem sandwichedTrace_branch_sum_le (R : ∀ j, Matrix (H j) I ℂ)
    (hR : ∑ j, (R j)ᴴ * R j = 1) {ρ σ : Matrix I I ℂ}
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) (hs : SupportLE ρ σ)
    {α : ℝ} (hα : 1 < α) :
    (∑ j, sandwichedTrace α (R j * ρ * (R j)ᴴ) (R j * σ * (R j)ᴴ)) ≤
      sandwichedTrace α ρ σ := by
  have h := sandwichedTrace_krausSumB_le (branchFlaggedKraus R)
    (branchFlaggedKraus_complete R hR) hρ hσ hs hα
  rw [branchFlaggedOutput_eq_blockDiagonal', branchFlaggedOutput_eq_blockDiagonal',
    FlagPower.sandwichedTrace_blockDiagonal'
      (fun j => hρ.mul_mul_conjTranspose_same (R j))
      (fun j => hσ.mul_mul_conjTranspose_same (R j)) α] at h
  exact h

end DependentBranchFlags

theorem pairMatrixB_eq_tensorOnLabCut {a b c d : ℕ}
    (ρ : BipartiteMatrix a b) (σ : BipartiteMatrix c d) :
    pairMatrixB ρ σ = tensorOnLabCut ρ σ := by
  ext x y
  rfl

theorem lanePowerMatrixB_isDensity {a b : ℕ} {ρ : BipartiteMatrix a b}
    (hρ : IsDensity ρ) (n : ℕ) : IsDensity (lanePowerMatrixB ρ n) := by
  induction n with
  | zero => exact hρ
  | succ n ih =>
      change IsDensity (pairMatrixB (lanePowerMatrixB ρ n) ρ)
      rw [pairMatrixB_eq_tensorOnLabCut]
      exact ih.tensorOnLabCut hρ

theorem lanePowerMatrixB_isSeparable {a b : ℕ} {ρ : BipartiteMatrix a b}
    (hρ : IsSeparable a b ρ) (n : ℕ) :
    IsSeparable (lanePowerDimB n a) (lanePowerDimB n b) (lanePowerMatrixB ρ n) := by
  induction n with
  | zero => exact hρ
  | succ n ih =>
      change IsSeparable _ _ (pairMatrixB (lanePowerMatrixB ρ n) ρ)
      rw [pairMatrixB_eq_tensorOnLabCut]
      exact ih.tensorOnLabCut hρ

theorem lanePowerMatrixB_entanglement_le {a b : ℕ} {ρ : BipartiteMatrix a b}
    (hρ : IsDensity ρ) {α e : ℝ} (hα : 1 < α)
    (hE : sandwichedEntanglement α a b ρ ≤ (e : EReal)) (n : ℕ) :
    sandwichedEntanglement α (lanePowerDimB n a) (lanePowerDimB n b)
      (lanePowerMatrixB ρ n) ≤ (((n + 1 : ℕ) : ℝ) * e : EReal) := by
  induction n with
  | zero =>
      simpa [lanePowerDimB, lanePowerMatrixB] using hE
  | succ n ih =>
      have ht := sandwichedEntanglement_tensor_le_of_le
        (lanePowerMatrixB_isDensity hρ n) hρ hα ih hE
      have he : ((n + 1 : ℕ) : ℝ) * e + e = ((n + 1 + 1 : ℕ) : ℝ) * e := by
        push_cast
        ring
      rw [he] at ht
      change sandwichedEntanglement α _ _ (pairMatrixB (lanePowerMatrixB ρ n) ρ) ≤ _
      rw [pairMatrixB_eq_tensorOnLabCut]
      exact ht

theorem lanePowerMatrixB_bellOverlap {d : ℕ} {ρ : BipartiteMatrix d d}
    (hρ : IsDensity ρ) (n : ℕ) :
    bellOverlap (lanePowerDimB n d) (lanePowerMatrixB ρ n) = bellOverlap d ρ ^ (n + 1) := by
  induction n with
  | zero => simp only [lanePowerDimB, lanePowerMatrixB, zero_add, pow_one]
  | succ n ih =>
      change bellOverlap (lanePowerDimB n d * d) (pairMatrixB (lanePowerMatrixB ρ n) ρ) = _
      rw [pairMatrixB_eq_tensorOnLabCut,
        bellOverlap_tensorOnLabCut (lanePowerMatrixB_isDensity hρ n).1 hρ.1, ih]
      exact (pow_succ (bellOverlap d ρ) (n + 1)).symm

theorem logTwo_lanePowerDimB (n d : ℕ) :
    logTwo (lanePowerDimB n d : ℝ) = ((n + 1 : ℕ) : ℝ) * logTwo (d : ℝ) := by
  rw [lanePowerDimB_eq_pow, Nat.cast_pow]
  unfold logTwo
  rw [Real.log_pow]
  ring

def typeMomentMaxA (n : ℕ) (p s : ℝ) : ℝ :=
  (Finset.univ : Finset (Fin (n + 1))).sup' Finset.univ_nonempty
    (fun w => Scalar.survivorMoment n w.val p s)

theorem survivorMoment_le_typeMomentMaxA (n : ℕ) (p s : ℝ) (w : Fin (n + 1)) :
    Scalar.survivorMoment n w.val p s ≤ typeMomentMaxA n p s := by
  unfold typeMomentMaxA
  exact Finset.le_sup' (fun w : Fin (n + 1) => Scalar.survivorMoment n w.val p s)
    (Finset.mem_univ w)

theorem one_le_typeMomentMaxA (n : ℕ) (p s : ℝ) :
    1 ≤ typeMomentMaxA n p s := by
  simpa only [Fin.val_zero, Scalar.survivorMoment_zero] using
    survivorMoment_le_typeMomentMaxA n p s (0 : Fin (n + 1))

theorem typeMomentMaxA_eq_some (n : ℕ) (p s : ℝ) :
    ∃ w : Fin (n + 1), typeMomentMaxA n p s = Scalar.survivorMoment n w.val p s := by
  obtain ⟨w, _, hw⟩ := Finset.exists_mem_eq_sup'
    (s := (Finset.univ : Finset (Fin (n + 1)))) Finset.univ_nonempty
    (fun w => Scalar.survivorMoment n w.val p s)
  exact ⟨w, hw⟩

theorem sandwichedTrace_type_branch_moment_le
    {I : Type*} [Fintype I] [DecidableEq I] (n : ℕ) (p : ℝ)
    {H : Fin (n + 1) → Type*} [∀ w, Fintype (H w)] [∀ w, DecidableEq (H w)]
    (R : ∀ w, Matrix (H w) I ℂ) (hR : ∑ w, (R w)ᴴ * R w = 1)
    {ρ σ : Matrix I I ℂ} (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef)
    (hs : SupportLE ρ σ) {α : ℝ} (hα : 1 < α) :
    (∑ w : Fin (n + 1), Scalar.survivorMoment n w.val p (α - 1) *
      sandwichedTrace α (R w * ρ * (R w)ᴴ) (R w * σ * (R w)ᴴ)) ≤
      typeMomentMaxA n p (α - 1) * sandwichedTrace α ρ σ := by
  calc
    _ ≤ ∑ w : Fin (n + 1), typeMomentMaxA n p (α - 1) *
        sandwichedTrace α (R w * ρ * (R w)ᴴ) (R w * σ * (R w)ᴴ) := by
      apply Finset.sum_le_sum
      intro w _
      exact mul_le_mul_of_nonneg_right
        (survivorMoment_le_typeMomentMaxA n p (α - 1) w)
        (sandwichedTrace_nonneg (hρ.mul_mul_conjTranspose_same (R w)) α)
    _ = typeMomentMaxA n p (α - 1) *
        ∑ w : Fin (n + 1), sandwichedTrace α (R w * ρ * (R w)ᴴ)
          (R w * σ * (R w)ᴴ) := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (sandwichedTrace_branch_sum_le R hR hρ hσ hs hα)
      ((zero_le_one : (0 : ℝ) ≤ 1).trans (one_le_typeMomentMaxA n p (α - 1)))

def physicalBlockLogChargeA (n : ℕ) (p s : ℝ) : ℝ :=
  ((1 + s) / s) * logTwo ((n : ℝ) + 1) + logTwo (typeMomentMaxA n p s) / s

theorem physicalBlockLogChargeA_le (n : ℕ) {p s : ℝ}
    (hn : 0 < n) (hp0 : 0 < p) (hp1 : p < 1) (hs0 : 0 < s) (hs1 : s ≤ 1) :
    physicalBlockLogChargeA n p s ≤ (n : ℝ) * converseBudget p s +
      ((2 + s) / s) * logTwo ((n : ℝ) + 1) := by
  obtain ⟨w, hw⟩ := typeMomentMaxA_eq_some n p s
  unfold physicalBlockLogChargeA
  rw [hw]
  exact finiteTypeIncrement_matrix_full_s n w.val hn
    (Nat.le_of_lt_succ w.isLt) hp0 hp1 hs0 hs1

theorem survivorMoment_parameter_zeroA (n w : ℕ) (s : ℝ) :
    Scalar.survivorMoment n w 0 s = (n.choose w : ℝ) ^ s := by
  unfold Scalar.survivorMoment
  rw [Finset.sum_eq_single w]
  · simp [Scalar.survivorTerm, Scalar.binomialTerm]
  · intro r hr hrw
    have hlt : r < w := lt_of_le_of_ne (Nat.le_of_lt_succ (Finset.mem_range.mp hr)) hrw
    have hsub : w - r ≠ 0 := (Nat.sub_pos_of_lt hlt).ne'
    simp [Scalar.survivorTerm, Scalar.binomialTerm, zero_pow hsub]
  · intro hw
    exact False.elim (hw (Finset.mem_range.mpr (Nat.lt_succ_self w)))

theorem survivorMoment_parameter_oneA (n w : ℕ) (s : ℝ) :
    Scalar.survivorMoment n w 1 s = 1 := by
  unfold Scalar.survivorMoment
  rw [Finset.sum_eq_single 0]
  · simp [Scalar.survivorTerm, Scalar.binomialTerm]
  · intro r _ hr0
    simp [Scalar.survivorTerm, Scalar.binomialTerm, zero_pow hr0]
  · intro hw
    exact False.elim (hw (Finset.mem_range.mpr (Nat.zero_lt_succ w)))

theorem logTwo_choose_leA (n w : ℕ) (hwn : w ≤ n) :
    logTwo (n.choose w : ℝ) ≤ (n : ℝ) := by
  have hc : (0 : ℝ) < n.choose w := Nat.cast_pos.mpr (Nat.choose_pos hwn)
  have hb : (n.choose w : ℝ) ≤ (2 : ℝ) ^ n := by
    exact_mod_cast Nat.choose_le_two_pow n w
  have hl := Real.log_le_log hc hb
  rw [Real.log_pow] at hl
  unfold logTwo
  exact (div_le_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mpr hl

theorem physicalBlockLogChargeA_le_parameter_zero (n : ℕ) {s : ℝ}
    (hs0 : 0 < s) :
    physicalBlockLogChargeA n 0 s ≤ (n : ℝ) * converseBudget 0 s +
      ((2 + s) / s) * logTwo ((n : ℝ) + 1) := by
  obtain ⟨w, hw⟩ := typeMomentMaxA_eq_some n 0 s
  have hc : (0 : ℝ) < n.choose w.val :=
    Nat.cast_pos.mpr (Nat.choose_pos (Nat.le_of_lt_succ w.isLt))
  have he : logTwo ((n.choose w.val : ℝ) ^ s) / s =
      logTwo (n.choose w.val : ℝ) := by
    unfold logTwo
    rw [Real.log_rpow hc]
    field_simp [hs0.ne', (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne']
  have hnlog : 0 ≤ logTwo ((n : ℝ) + 1) := by
    unfold logTwo
    have hnreal : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    exact div_nonneg (Real.log_nonneg (by linarith))
      (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
  have hcoeff : (1 + s) / s ≤ (2 + s) / s :=
    div_le_div_of_nonneg_right (by linarith) hs0.le
  unfold physicalBlockLogChargeA
  rw [hw, survivorMoment_parameter_zeroA, he]
  have hl := logTwo_choose_leA n w.val (Nat.le_of_lt_succ w.isLt)
  have hmul := mul_le_mul_of_nonneg_right hcoeff hnlog
  have hbudget : converseBudget 0 s = 1 := by simp [converseBudget]
  rw [hbudget, mul_one]
  linarith

theorem physicalBlockLogChargeA_le_parameter_one (n : ℕ) {s : ℝ}
    (hs0 : 0 < s) :
    physicalBlockLogChargeA n 1 s ≤ (n : ℝ) * converseBudget 1 s +
      ((2 + s) / s) * logTwo ((n : ℝ) + 1) := by
  obtain ⟨w, hw⟩ := typeMomentMaxA_eq_some n 1 s
  have hnlog : 0 ≤ logTwo ((n : ℝ) + 1) := by
    unfold logTwo
    have hnreal : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    exact div_nonneg (Real.log_nonneg (by linarith))
      (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
  have hcoeff : (1 + s) / s ≤ (2 + s) / s :=
    div_le_div_of_nonneg_right (by linarith) hs0.le
  unfold physicalBlockLogChargeA
  rw [hw, survivorMoment_parameter_oneA]
  simpa [converseBudget, logTwo] using mul_le_mul_of_nonneg_right hcoeff hnlog

theorem physicalBlockLogChargeA_le_full_parameters (n : ℕ) {p s : ℝ}
    (hn : 0 < n) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hs0 : 0 < s) (hs1 : s ≤ 1) :
    physicalBlockLogChargeA n p s ≤ (n : ℝ) * converseBudget p s +
      ((2 + s) / s) * logTwo ((n : ℝ) + 1) := by
  by_cases hzero : p = 0
  · subst p
    exact physicalBlockLogChargeA_le_parameter_zero n hs0
  by_cases hone : p = 1
  · subst p
    exact physicalBlockLogChargeA_le_parameter_one n hs0
  exact physicalBlockLogChargeA_le n hn (lt_of_le_of_ne hp0 (Ne.symm hzero))
    (lt_of_le_of_ne hp1 hone) hs0 hs1

theorem supportLE_conjugationA {I O : Type*} [Fintype I] [Fintype O]
    [DecidableEq I] [DecidableEq O] (R : Matrix O I ℂ) {ρ σ : Matrix I I ℂ}
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) (hs : SupportLE ρ σ) :
    SupportLE (R * ρ * Rᴴ) (R * σ * Rᴴ) := by
  simpa only [krausSumB, Fin.sum_univ_one] using
    QuantumProver.SandwichedDPI.supportLE_kraus_sum (fun _ : Fin 1 => R) hρ hσ hs

theorem FiniteProtocol.output_supportLE {p : ℝ} {a b af bf : ℕ}
    (P : FiniteProtocol p a b af bf) {ρ σ : BipartiteMatrix a b}
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) (hs : SupportLE ρ σ) :
    SupportLE (P.output ρ) (P.output σ) := by
  obtain ⟨k, K, hK⟩ := P.exists_output_kraus
  rw [hK ρ, hK σ]
  exact QuantumProver.SandwichedDPI.supportLE_kraus_sum K hρ hσ hs

theorem FiniteProtocol.sandwichedTrace_output_le {p : ℝ} {a b af bf : ℕ}
    (P : FiniteProtocol p a b af bf) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {ρ σ : BipartiteMatrix a b} (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef)
    (hs : SupportLE ρ σ) {α : ℝ} (hα : 1 < α) :
    sandwichedTrace α (P.output ρ) (P.output σ) ≤ sandwichedTrace α ρ σ := by
  obtain ⟨k, K, hK, hO⟩ := P.exists_complete_output_kraus hp0 hp1
  rw [hO ρ, hO σ]
  exact sandwichedTrace_krausSumB_le K hK hρ hσ hs hα

theorem labFlagComparator_posSemidefA {f g a b : ℕ}
    (t : Fin f × Fin g → ℝ) (ρ : Fin f × Fin g → BipartiteMatrix a b)
    (ht : ∀ z, 0 ≤ t z) (hρ : ∀ z, (ρ z).PosSemidef) :
    (labFlagComparator t ρ).PosSemidef := by
  unfold labFlagComparator
  apply Matrix.posSemidef_sum
  intro z _
  rw [Complex.coe_smul]
  exact ((hρ z).mul_mul_conjTranspose_same
    (appendFlagKraus z.1 ⊗ₖ appendFlagKraus z.2)).smul (ht z)

theorem physical_phase_moment_uniformA (n w : ℕ) (hwn : w ≤ n) (p s : ℝ) :
    (∑ r : Fin (n + 1), physicalSurvivorProbabilityB p w r.val *
      (phaseComparisonConstantB n w r.val) ^ s) = Scalar.survivorMoment n w p s := by
  rw [Fin.sum_univ_eq_sum_range (fun r : ℕ => physicalSurvivorProbabilityB p w r *
    (phaseComparisonConstantB n w r) ^ s) (n + 1)]
  change (∑ r ∈ Finset.range (n + 1), physicalSurvivorProbabilityB p w r •
    ((phaseComparisonConstantB n w r) ^ s)) = _
  rw [physicalSurvivorProbabilityB_sum_rangeC n w hwn p]
  simp only [smul_eq_mul, Scalar.survivorMoment, Scalar.survivorTerm,
    Scalar.binomialTerm, physicalSurvivorProbabilityB, phaseComparisonConstantB,
    sub_sub_cancel]

section ActualPhysicalFlags

variable (n : ℕ) (p : ℝ) (A B : Type*) [Fintype A] [Fintype B]
  [DecidableEq A] [DecidableEq B]

theorem recordedFlagLawC_nonnegA (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (z : Fin (n + 1) × Fin (n + 1)) : 0 ≤ recordedFlagLawC n p z := by
  rw [recordedFlagLawC_eq_physical]
  exact physicalSurvivorProbabilityB_nonneg p hp0 hp1 z.1.val z.2.val

theorem flaggedRecordedOutputC_sandwichedTrace_le
    (hA : 0 < Fintype.card A) (hB : 0 < Fintype.card B)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {ρ σ : Matrix ((A × Finset (Fin n)) × B) ((A × Finset (Fin n)) × B) ℂ}
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) (hs : SupportLE ρ σ)
    {α : ℝ} (hα : 1 < α) :
    sandwichedTrace α (flaggedRecordedOutputC n p A B ρ)
      (flaggedPhaseOutputC n p A B σ) ≤
        typeMomentMaxA n p (α - 1) * sandwichedTrace α ρ σ := by
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
  unfold flaggedRecordedOutputC flaggedPhaseOutputC
  simp_rw [recordedLossBranchC_fin_eq_labTransfer, recordedPhaseBranchC_fin_eq_labTransfer]
  rw [labFlagComparator_sandwichedTrace_same_weights
    (recordedFlagLawC n p)
    (fun z => labTransferOutput (lossKrausB n z.1.val z.2.val) (ρw z.1))
    (fun z => labTransferOutput (measurePhaseKrausB n z.1.val z.2.val) (σw z.1))
    (recordedFlagLawC_nonnegA n p hp0 hp1)
    (fun z => krausSumB_posSemidef _ (hρw z.1))
    (fun z => krausSumB_posSemidef _ (hσw z.1)) hα.le]
  simp_rw [recordedFlagLawC_eq_physical]
  rw [Fintype.sum_prod_type]
  calc
    _ ≤ ∑ w : Fin (n + 1), Scalar.survivorMoment n w.val p (α - 1) *
        sandwichedTrace α (ρw w) (σw w) := by
      apply Finset.sum_le_sum
      intro w _
      calc
        _ ≤ ∑ r : Fin (n + 1), physicalSurvivorProbabilityB p w.val r.val *
            ((phaseComparisonConstantB n w.val r.val) ^ (α - 1) *
              sandwichedTrace α (ρw w) (σw w)) := by
          apply Finset.sum_le_sum
          intro r _
          by_cases hrw : r.val ≤ w.val
          · exact mul_le_mul_of_nonneg_left
              (fixedWeight_sandwichedTrace_phase_le_input_of_posSemidef
                n w.val r.val hrw (Nat.le_of_lt_succ r.isLt) hA' hB
                (hρw w) (hσw w) (hsw w) hα)
              (physicalSurvivorProbabilityB_nonneg p hp0 hp1 w.val r.val)
          · rw [physicalSurvivorProbabilityB_zeroC p w.val r.val (by omega)]
            simp
        _ = _ := by
          simp only [← mul_assoc, ← Finset.sum_mul]
          rw [physical_phase_moment_uniformA n w.val (Nat.le_of_lt_succ w.isLt)]
    _ ≤ _ := sandwichedTrace_type_branch_moment_le n p R
      (typeCopyLabC_complete n A B) hρ hσ hs hα

theorem flaggedRecordedOutputC_supportLEA (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {ρ σ : Matrix ((A × Finset (Fin n)) × B) ((A × Finset (Fin n)) × B) ℂ}
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) (hs : SupportLE ρ σ) :
    SupportLE (flaggedRecordedOutputC n p A B ρ) (flaggedPhaseOutputC n p A B σ) := by
  unfold flaggedRecordedOutputC flaggedPhaseOutputC
  simp_rw [recordedLossBranchC_fin_eq_labTransfer, recordedPhaseBranchC_fin_eq_labTransfer]
  apply labFlagComparator_supportLE _ _ _ _
    (recordedFlagLawC_nonnegA n p hp0 hp1) (recordedFlagLawC_nonnegA n p hp0 hp1)
    (fun _ h => h)
  · intro z
    exact krausSumB_posSemidef _ (hρ.mul_mul_conjTranspose_same (typeCopyLabC n z.1.val A B))
  · intro z
    exact krausSumB_posSemidef _ (hσ.mul_mul_conjTranspose_same (typeCopyLabC n z.1.val A B))
  · intro z hz
    have hrw : z.2.val ≤ z.1.val := by
      by_contra h
      exact hz (by simp [recordedFlagLawC, h])
    have hrn : z.2.val ≤ n := Nat.le_of_lt_succ z.2.isLt
    let ρw := typeCopyLabC n z.1.val A B * ρ * (typeCopyLabC n z.1.val A B)ᴴ
    let σw := typeCopyLabC n z.1.val A B * σ * (typeCopyLabC n z.1.val A B)ᴴ
    have hρw : ρw.PosSemidef := hρ.mul_mul_conjTranspose_same _
    have hσw : σw.PosSemidef := hσ.mul_mul_conjTranspose_same _
    have hsN := labTransferOutput_supportLE (lossKrausB n z.1.val z.2.val)
      hρw hσw (supportLE_conjugationA _ hρ hσ hs)
    have hc := phaseComparisonConstantB_pos n z.1.val z.2.val hrw hrn
    have hN := krausSumB_posSemidef (labTransferKraus (lossKrausB n z.1.val z.2.val)) hσw
    have hS := krausSumB_posSemidef (labTransferKraus (measurePhaseKrausB n z.1.val z.2.val)) hσw
    have ho := supportLE_of_loewner hN (hS.smul hc.le)
      (labTransferOutput_loss_phase_domination n z.1.val z.2.val hrw hrn
        (A × Finset (Fin n)) B hσw)
    exact (supportLE_smul_comparison_iff
      (krausSumB_posSemidef (labTransferKraus (lossKrausB n z.1.val z.2.val)) hρw).1
      hS hc).mp (hsN.trans ho)

theorem pinchedRecordedOutputC_sandwichedTrace_le
    (hA : 0 < Fintype.card A) (hB : 0 < Fintype.card B)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {ρ σ : Matrix ((A × Finset (Fin n)) × B) ((A × Finset (Fin n)) × B) ℂ}
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) (hs : SupportLE ρ σ)
    {α : ℝ} (hα : 1 < α) :
    sandwichedTrace α (pinchedRecordedOutputC n p A B ρ)
      (phaseRecordedOutputC n p A B σ) ≤
        typeMomentMaxA n p (α - 1) * sandwichedTrace α ρ σ := by
  have hFρ : (flaggedRecordedOutputC n p A B ρ).PosSemidef := by
    unfold flaggedRecordedOutputC
    apply labFlagComparator_posSemidefA _ _ (recordedFlagLawC_nonnegA n p hp0 hp1)
    intro z
    rw [recordedLossBranchC_fin_eq_labTransfer]
    exact krausSumB_posSemidef _ (hρ.mul_mul_conjTranspose_same _)
  have hFσ : (flaggedPhaseOutputC n p A B σ).PosSemidef := by
    unfold flaggedPhaseOutputC
    apply labFlagComparator_posSemidefA _ _ (recordedFlagLawC_nonnegA n p hp0 hp1)
    intro z
    rw [recordedPhaseBranchC_fin_eq_labTransfer]
    exact krausSumB_posSemidef _ (hσ.mul_mul_conjTranspose_same _)
  have hD := (eraseLabFlagsProtocolC p (n + 1) (n + 1)
    (Fintype.card (A × Finset (Fin n))) (Fintype.card (Finset (Fin n) × B))).sandwichedTrace_output_le
      hp0 hp1 hFρ hFσ (flaggedRecordedOutputC_supportLEA n p A B hp0 hp1 hρ hσ hs) hα
  have hpin : (pinchedRecordedOutputC n p A B ρ).PosSemidef :=
    krausSumB_posSemidef _ (krausSumB_posSemidef _ hρ)
  rw [flaggedRecordedOutputC_erase n p A B hp0 hp1,
    flaggedPhaseOutputC_erase n p A B hp0 hp1,
    TensorPower.sandwichedTrace_submatrix_equiv
      hpin
      (phaseRecordedOutputC_posSemidef n p A B hσ)] at hD
  exact hD.trans (flaggedRecordedOutputC_sandwichedTrace_le n p A B hA hB hp0 hp1 hρ hσ hs hα)

end ActualPhysicalFlags

theorem sandwichedTrace_sum_leA {k a b : ℕ}
    (ρ σ : Fin k → BipartiteMatrix a b)
    (hρ : ∀ j, (ρ j).PosSemidef) (hσ : ∀ j, (σ j).PosSemidef)
    (hs : ∀ j, SupportLE (ρ j) (σ j)) {α : ℝ} (hα : 1 < α) :
    sandwichedTrace α (∑ j, ρ j) (∑ j, σ j) ≤
      ∑ j, sandwichedTrace α (ρ j) (σ j) := by
  let t := fun _ : Fin k × Fin 1 => (1 : ℝ)
  let R := fun z : Fin k × Fin 1 => ρ z.1
  let S := fun z : Fin k × Fin 1 => σ z.1
  have hR := labFlagComparator_posSemidefA t R (fun _ => zero_le_one) (fun z => hρ z.1)
  have hS := labFlagComparator_posSemidefA t S (fun _ => zero_le_one) (fun z => hσ z.1)
  have hRS := labFlagComparator_supportLE t t R S (fun _ => zero_le_one)
    (fun _ => zero_le_one) (fun _ h => h) (fun z => hρ z.1) (fun z => hσ z.1)
    (fun z _ => hs z.1)
  have h := (eraseLabFlagsProtocolC 0 k 1 a b).sandwichedTrace_output_le
    (by norm_num) (by norm_num) hR hS hRS hα
  rw [eraseLabFlagsProtocolC_labFlagComparator,
    eraseLabFlagsProtocolC_labFlagComparator,
    labFlagComparator_sandwichedTrace_same_weights t R S (fun _ => zero_le_one)
      (fun z => hρ z.1) (fun z => hσ z.1) hα.le] at h
  simpa only [t, R, S, Complex.ofReal_one, one_smul, one_mul,
    Fintype.sum_prod_type, Fin.sum_univ_one] using h

theorem supportLE_sumA {k a b : ℕ} (ρ σ : Fin k → BipartiteMatrix a b)
    (hρ : ∀ j, (ρ j).PosSemidef) (hσ : ∀ j, (σ j).PosSemidef)
    (hs : ∀ j, SupportLE (ρ j) (σ j)) : SupportLE (∑ j, ρ j) (∑ j, σ j) := by
  let t := fun _ : Fin k × Fin 1 => (1 : ℝ)
  let R := fun z : Fin k × Fin 1 => ρ z.1
  let S := fun z : Fin k × Fin 1 => σ z.1
  have hR := labFlagComparator_posSemidefA t R (fun _ => zero_le_one) (fun z => hρ z.1)
  have hS := labFlagComparator_posSemidefA t S (fun _ => zero_le_one) (fun z => hσ z.1)
  have hRS := labFlagComparator_supportLE t t R S (fun _ => zero_le_one)
    (fun _ => zero_le_one) (fun _ h => h) (fun z => hρ z.1) (fun z => hσ z.1)
    (fun z _ => hs z.1)
  have h := (eraseLabFlagsProtocolC 0 k 1 a b).output_supportLE hR hS hRS
  rw [eraseLabFlagsProtocolC_labFlagComparator, eraseLabFlagsProtocolC_labFlagComparator] at h
  simpa only [t, R, S, Complex.ofReal_one, one_smul,
    Fintype.sum_prod_type, Fin.sum_univ_one] using h

def physicalBlockQFactorA (n : ℕ) (p α : ℝ) : ℝ :=
  ((n : ℝ) + 1) ^ α * typeMomentMaxA n p (α - 1)

theorem one_le_physicalBlockQFactorA (n : ℕ) (p : ℝ) {α : ℝ} (hα : 0 ≤ α) :
    1 ≤ physicalBlockQFactorA n p α := by
  have hn : (1 : ℝ) ≤ (n : ℝ) + 1 := by
    have h := Nat.cast_nonneg (α := ℝ) n
    linarith
  have hp := Real.one_le_rpow hn hα
  have hm := one_le_typeMomentMaxA n p (α - 1)
  unfold physicalBlockQFactorA
  nlinarith

theorem log_physicalBlockQFactorA (n : ℕ) (p : ℝ) {α : ℝ} (_hα : 1 < α) :
    logTwo (physicalBlockQFactorA n p α) / (α - 1) =
      physicalBlockLogChargeA n p (α - 1) := by
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hm : 0 < typeMomentMaxA n p (α - 1) :=
    (zero_lt_one : (0 : ℝ) < 1).trans_le (one_le_typeMomentMaxA n p (α - 1))
  unfold physicalBlockQFactorA physicalBlockLogChargeA logTwo
  rw [Real.log_mul (Real.rpow_pos_of_pos hn α).ne' hm.ne', Real.log_rpow hn]
  ring

section FullPhysicalComparison

variable (n : ℕ) (p : ℝ) (A B : Type*) [Fintype A] [Fintype B]
  [DecidableEq A] [DecidableEq B]

theorem flaggedRecordedOutputC_posSemidefA (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {ρ : Matrix ((A × Finset (Fin n)) × B) ((A × Finset (Fin n)) × B) ℂ}
    (hρ : ρ.PosSemidef) : (flaggedRecordedOutputC n p A B ρ).PosSemidef := by
  unfold flaggedRecordedOutputC
  apply labFlagComparator_posSemidefA _ _ (recordedFlagLawC_nonnegA n p hp0 hp1)
  intro z
  rw [recordedLossBranchC_fin_eq_labTransfer]
  exact krausSumB_posSemidef _ (hρ.mul_mul_conjTranspose_same _)

theorem flaggedPhaseOutputC_posSemidefA (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {σ : Matrix ((A × Finset (Fin n)) × B) ((A × Finset (Fin n)) × B) ℂ}
    (hσ : σ.PosSemidef) : (flaggedPhaseOutputC n p A B σ).PosSemidef := by
  unfold flaggedPhaseOutputC
  apply labFlagComparator_posSemidefA _ _ (recordedFlagLawC_nonnegA n p hp0 hp1)
  intro z
  rw [recordedPhaseBranchC_fin_eq_labTransfer]
  exact krausSumB_posSemidef _ (hσ.mul_mul_conjTranspose_same _)

theorem pinchedRecordedOutputC_supportLEA (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {ρ σ : Matrix ((A × Finset (Fin n)) × B) ((A × Finset (Fin n)) × B) ℂ}
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) (hs : SupportLE ρ σ) :
    SupportLE (pinchedRecordedOutputC n p A B ρ) (phaseRecordedOutputC n p A B σ) := by
  have hD := (eraseLabFlagsProtocolC p (n + 1) (n + 1)
    (Fintype.card (A × Finset (Fin n))) (Fintype.card (Finset (Fin n) × B))).output_supportLE
      (flaggedRecordedOutputC_posSemidefA n p A B hp0 hp1 hρ)
      (flaggedPhaseOutputC_posSemidefA n p A B hp0 hp1 hσ)
      (flaggedRecordedOutputC_supportLEA n p A B hp0 hp1 hρ hσ hs)
  rw [flaggedRecordedOutputC_erase n p A B hp0 hp1,
    flaggedPhaseOutputC_erase n p A B hp0 hp1] at hD
  exact (SupportLE.submatrix_equiv_iff (recordedOutputEquivC n A B)).mp hD

end FullPhysicalComparison

section FullPhysicalComparison
variable (n : ℕ) (p : ℝ) (A B : Type*) [Fintype A] [Fintype B]
  [DecidableEq A] [DecidableEq B]

theorem recordedOutputC_supportLEA (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {ρ σ : Matrix ((A × Finset (Fin n)) × B) ((A × Finset (Fin n)) × B) ℂ}
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) (hs : SupportLE ρ σ) :
    SupportLE (recordedOutputC n p A B ρ) (phaseRecordedOutputC n p A B σ) := by
  have hΩ := recordedOutputC_posSemidef n p A B hρ
  have hPΩ : (pinchedRecordedOutputC n p A B ρ).PosSemidef := krausSumB_posSemidef _ hΩ
  have hn : (0 : ℝ) < n + 1 := by positivity
  have horder := QuantumProver.SuperchannelDiscrimination.Pinching.le_card_smul_pinching
    (recordWeightOutputC_family n A B) hΩ
  rw [Fintype.card_fin, Nat.cast_add, Nat.cast_one,
    ← pinchedRecordedOutputC_eq_pinchingMap] at horder
  have hSP := supportLE_of_loewner hΩ (hPΩ.smul hn.le) horder
  have hΩP := (supportLE_smul_comparison_iff hΩ.1 hPΩ hn).mp hSP
  exact hΩP.trans (pinchedRecordedOutputC_supportLEA n p A B hp0 hp1 hρ hσ hs)

theorem recordedOutputC_sandwichedTrace_le
    (hA : 0 < Fintype.card A) (hB : 0 < Fintype.card B)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {ρ σ : Matrix ((A × Finset (Fin n)) × B) ((A × Finset (Fin n)) × B) ℂ}
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) (hs : SupportLE ρ σ)
    {α : ℝ} (hα : 1 < α) :
    sandwichedTrace α (recordedOutputC n p A B ρ) (phaseRecordedOutputC n p A B σ) ≤
      physicalBlockQFactorA n p α * sandwichedTrace α ρ σ := by
  have hP := sandwichedTrace_pinching_bound (recordWeightOutputC_family n A B)
    (recordedOutputC_posSemidef n p A B hρ) (phaseRecordedOutputC n p A B σ) hα.le
  rw [Fintype.card_fin, Nat.cast_add, Nat.cast_one,
    ← pinchedRecordedOutputC_eq_pinchingMap] at hP
  have hQ := mul_le_mul_of_nonneg_left
    (pinchedRecordedOutputC_sandwichedTrace_le n p A B hA hB hp0 hp1 hρ hσ hs hα)
    (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1) α)
  exact hP.trans (hQ.trans_eq (by unfold physicalBlockQFactorA; ring))

theorem physicalOutput_sandwichedTrace_recoveredPhase_le
    (hA : 0 < Fintype.card A) (hB : 0 < Fintype.card B)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {ρ σ : Matrix ((A × Finset (Fin n)) × B) ((A × Finset (Fin n)) × B) ℂ}
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) (hs : SupportLE ρ σ)
    {α : ℝ} (hα : 1 < α) :
    sandwichedTrace α (labTransferOutput (tensorDampingKrausB n p) ρ)
      (recoveredPhaseOutputC n p A B σ) ≤
        physicalBlockQFactorA n p α * sandwichedTrace α ρ σ := by
  have hΩ := recordedOutputC_posSemidef n p A B hρ
  have hκ := phaseRecordedOutputC_posSemidef n p A B hσ
  have hD := (fullRecordRecoveryProtocolB p n A B).sandwichedTrace_output_le hp0 hp1
    (hΩ.submatrix _) (hκ.submatrix _)
    ((recordedOutputC_supportLEA n p A B hp0 hp1 hρ hσ hs).submatrix_equiv
      (recordedOutputEquivC n A B)) hα
  rw [recordedOutputC_matrix_recovery, ← recoveredPhaseOutputC,
    TensorPower.sandwichedTrace_submatrix_equiv hΩ hκ] at hD
  exact hD.trans (recordedOutputC_sandwichedTrace_le n p A B hA hB hp0 hp1 hρ hσ hs hα)

theorem physicalOutput_supportLE_recoveredPhaseA (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {ρ σ : Matrix ((A × Finset (Fin n)) × B) ((A × Finset (Fin n)) × B) ℂ}
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) (hs : SupportLE ρ σ) :
    SupportLE (labTransferOutput (tensorDampingKrausB n p) ρ)
      (recoveredPhaseOutputC n p A B σ) := by
  have hD := (fullRecordRecoveryProtocolB p n A B).output_supportLE
    ((recordedOutputC_posSemidef n p A B hρ).submatrix _)
    ((phaseRecordedOutputC_posSemidef n p A B hσ).submatrix _)
    ((recordedOutputC_supportLEA n p A B hp0 hp1 hρ hσ hs).submatrix_equiv
      (recordedOutputEquivC n A B))
  rw [recordedOutputC_matrix_recovery, ← recoveredPhaseOutputC] at hD
  exact hD

end FullPhysicalComparison

theorem sandwichedDivergence_le_of_Q_factorA
    {I O : Type*} [Fintype I] [Fintype O] [DecidableEq I] [DecidableEq O]
    {ρ σ : Matrix I I ℂ} {η τ : Matrix O O ℂ}
    (hρ : IsDensity ρ) (hσ : IsDensity σ) (hη : IsDensity η) (hτ : IsDensity τ)
    (hsIn : SupportLE ρ σ) (hsOut : SupportLE η τ) {α c : ℝ}
    (hα : 1 < α) (hc : 0 < c)
    (hQ : sandwichedTrace α η τ ≤ c * sandwichedTrace α ρ σ) :
    sandwichedDivergence α η τ ≤ sandwichedDivergence α ρ σ +
      ((logTwo c / (α - 1) : ℝ) : EReal) := by
  have hQi : 0 < sandwichedTrace α ρ σ :=
    (zero_lt_one : (0 : ℝ) < 1).trans_le (sandwichedTrace_ge_one hρ hσ hsIn hα)
  have hQo : 0 < sandwichedTrace α η τ :=
    (zero_lt_one : (0 : ℝ) < 1).trans_le (sandwichedTrace_ge_one hη hτ hsOut hα)
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hα1 : 0 < α - 1 := sub_pos.mpr hα
  have hl := Real.log_le_log hQo hQ
  rw [Real.log_mul hc.ne' hQi.ne'] at hl
  simp only [sandwichedDivergence, ite_eq_left hsIn, ite_eq_left hsOut,
    ← EReal.coe_add, EReal.coe_le_coe_iff]
  calc
    _ ≤ (Real.log c + Real.log (sandwichedTrace α ρ σ)) /
        ((α - 1) * Real.log 2) :=
      div_le_div_of_nonneg_right hl (mul_pos hα1 h2).le
    _ = _ := by
      unfold logTwo
      field_simp [hα1.ne', h2.ne']
      ring

section SupportedPhysicalCharge

variable (n : ℕ) (p : ℝ) (A B : Type*) [Fintype A] [Fintype B]
  [DecidableEq A] [DecidableEq B]

theorem physicalOutput_sandwichedDivergence_recoveredPhase_le
    (hA : 0 < Fintype.card A) (hB : 0 < Fintype.card B)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {ρ σ : Matrix ((A × Finset (Fin n)) × B) ((A × Finset (Fin n)) × B) ℂ}
    (hρ : IsDensity ρ) (hσ : SepPositive σ) (htrace : σ.trace = 1)
    (hs : SupportLE ρ σ) {α : ℝ} (hα : 1 < α) :
    sandwichedDivergence α (labTransferOutput (tensorDampingKrausB n p) ρ)
      (recoveredPhaseOutputC n p A B σ) ≤
        sandwichedDivergence α ρ σ + (physicalBlockLogChargeA n p (α - 1) : EReal) := by
  have hK : ∑ L, (tensorDampingKrausB n p L)ᴴ * tensorDampingKrausB n p L = 1 := by
    simpa only [physicalTensorKrausB_eq_damping] using physicalTensorKrausB_complete n p hp0 hp1
  have hN := labTransferOutput_isDensity (tensorDampingKrausB n p) hK hρ
  have hT := (recoveredPhaseOutputC_isSeparable n p A B hp0 hp1 hσ htrace).isDensity
  have hsOut := physicalOutput_supportLE_recoveredPhaseA n p A B hp0 hp1 hρ.1 hσ.posSemidef hs
  have hQ := physicalOutput_sandwichedTrace_recoveredPhase_le n p A B hA hB hp0 hp1
    hρ.1 hσ.posSemidef hs hα
  have hc : 0 < physicalBlockQFactorA n p α :=
    (zero_lt_one : (0 : ℝ) < 1).trans_le (one_le_physicalBlockQFactorA n p (by linarith))
  have hD := sandwichedDivergence_le_of_Q_factorA hρ ⟨hσ.posSemidef, htrace⟩
    hN hT hs hsOut hα hc hQ
  rw [log_physicalBlockQFactorA n p hα] at hD
  exact hD

end SupportedPhysicalCharge

end QuantumProver.AmplitudeDamping.FiniteModel

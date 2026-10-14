import QuantumProver.InformationTheory.DepolarizingSquashedEntanglement.BCYTesting
import QuantumProver.InformationTheory.DepolarizingSquashedEntanglement.BCYTensorRegularization

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators ComplexOrder Kronecker Topology

namespace QuantumProver.DepolarizingSquashedEntanglement.BCYCopyTesting

open BCYTesting BCYMeasurement BCYRelativeEntropy

variable {A B X Y : Type*} [Fintype A] [Fintype B] [Fintype X] [Fintype Y]
  [DecidableEq A] [DecidableEq B] [DecidableEq X] [DecidableEq Y]

def binaryOutcomeSet (s : Finset (X × Y)) (b : Bool) : Finset (X × Y) :=
  if b then s else Finset.univ \ s

def lastCopyDensity (n : ℕ) (ρ : Density (CopyIndex A (n + 1) × CopyIndex B (n + 1))) :
    Density ((A × CopyIndex A n) × (B × CopyIndex B n)) :=
  densityReindex (Equiv.prodCongr (Equiv.prodComm (CopyIndex A n) A)
    (Equiv.prodComm (CopyIndex B n) B)) ρ

theorem lastCopyDensity_isSeparable (n : ℕ)
    (ρ : Density (CopyIndex A (n + 1) × CopyIndex B (n + 1)))
    (hρ : IsSeparable ρ.matrix) : IsSeparable (lastCopyDensity n ρ).matrix :=
  isSeparable_reindex _ _ hρ

def copyHistoryWeight (M : OneWayPOVM A B X Y) (s : Finset (X × Y)) :
    (n : ℕ) → Density (CopyIndex A n × CopyIndex B n) → History n → ℝ
  | 0, _, _ => 1
  | n + 1, ρ, h =>
    let σ := lastCopyDensity n ρ
    let sb := binaryOutcomeSet s (h 0)
    let p := (companionApply M sb σ.matrix).trace.re
    if hp : 0 < p then
      p * copyHistoryWeight M s n (remainderDensity M sb σ hp) (Fin.tail h)
    else 0

@[simp] theorem copyHistoryWeight_cons (M : OneWayPOVM A B X Y) (s : Finset (X × Y))
    (n : ℕ) (ρ : Density (CopyIndex A (n + 1) × CopyIndex B (n + 1)))
    (b : Bool) (h : History n) :
    copyHistoryWeight M s (n + 1) ρ (Fin.cons b h) =
      if hp : 0 < (companionApply M (binaryOutcomeSet s b) (lastCopyDensity n ρ).matrix).trace.re then
        (companionApply M (binaryOutcomeSet s b) (lastCopyDensity n ρ).matrix).trace.re *
          copyHistoryWeight M s n
            (remainderDensity M (binaryOutcomeSet s b) (lastCopyDensity n ρ) hp) h
      else 0 := by
  simp only [copyHistoryWeight, Fin.cons_zero, Fin.tail_cons]

theorem copyHistoryWeight_nonneg (M : OneWayPOVM A B X Y) (s : Finset (X × Y))
    (n : ℕ) (ρ : Density (CopyIndex A n × CopyIndex B n)) (h : History n) :
    0 ≤ copyHistoryWeight M s n ρ h := by
  induction n with
  | zero => exact zero_le_one
  | succ n ih =>
    dsimp only [copyHistoryWeight]
    split
    · rename_i hp
      exact mul_nonneg hp.le (ih _ _)
    · exact le_refl _

theorem sum_histories_cons {n : ℕ} (f : History (n + 1) → ℝ) :
    ∑ h, f h = ∑ h : History n, (f (Fin.cons true h) + f (Fin.cons false h)) := by
  rw [← (Fin.consEquiv (fun _ : Fin (n + 1) => Bool)).sum_comp f,
    Fintype.sum_prod_type, Finset.sum_comm]
  simp only [Fintype.sum_bool]
  rfl

theorem copyHistoryWeight_cons_sum (M : OneWayPOVM A B X Y) (s : Finset (X × Y))
    (n : ℕ) (ρ : Density (CopyIndex A (n + 1) × CopyIndex B (n + 1)))
    (b : Bool)
    (ih : ∀ σ : Density (CopyIndex A n × CopyIndex B n),
      ∑ h : History n, copyHistoryWeight M s n σ h = 1) :
    ∑ h : History n, copyHistoryWeight M s (n + 1) ρ (Fin.cons b h) =
      (companionApply M (binaryOutcomeSet s b) (lastCopyDensity n ρ).matrix).trace.re := by
  let p := (companionApply M (binaryOutcomeSet s b) (lastCopyDensity n ρ).matrix).trace.re
  by_cases hp : 0 < p
  · have hp' : 0 < (companionApply M (binaryOutcomeSet s b) (lastCopyDensity n ρ).matrix).trace.re := hp
    simp only [copyHistoryWeight_cons, dif_pos hp']
    rw [← Finset.mul_sum, ih, mul_one]
  · have hp0 : p = 0 := le_antisymm (le_of_not_gt hp)
      (companionApply_probability_nonneg _ _ (lastCopyDensity n ρ).positive)
    have hp' : ¬0 < (companionApply M (binaryOutcomeSet s b) (lastCopyDensity n ρ).matrix).trace.re := hp
    simp only [copyHistoryWeight_cons, dif_neg hp', Finset.sum_const_zero]
    exact hp0.symm

theorem copyHistoryWeight_sum_one (M : OneWayPOVM A B X Y) (s : Finset (X × Y))
    (n : ℕ) (ρ : Density (CopyIndex A n × CopyIndex B n)) :
    ∑ h : History n, copyHistoryWeight M s n ρ h = 1 := by
  induction n with
  | zero => simp [copyHistoryWeight, History]
  | succ n ih =>
    rw [sum_histories_cons, Finset.sum_add_distrib,
      copyHistoryWeight_cons_sum M s n ρ true ih,
      copyHistoryWeight_cons_sum M s n ρ false ih]
    simp only [binaryOutcomeSet, Bool.false_eq_true, ite_true, ite_false]
    have hsum := congrArg Complex.re
      (companionApply_trace_complement_sum M s (lastCopyDensity n ρ).matrix)
    simpa only [Complex.add_re, (lastCopyDensity n ρ).trace_one, Complex.one_re] using hsum

@[simp] theorem successCount_cons {n : ℕ} (b : Bool) (h : History n) :
    successCount (Fin.cons b h) = (if b then 1 else 0) + successCount h := by
  simp only [successCount, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]

@[simp] theorem centeredCount_cons (a : ℝ) {n : ℕ} (b : Bool) (h : History n) :
    centeredCount a (Fin.cons b h) = centeredCount a h + ((if b then 1 else 0) - a) := by
  simp only [centeredCount, successCount_cons, Nat.cast_add, Nat.cast_one]
  ring

def copyMGF (M : OneWayPOVM A B X Y) (s : Finset (X × Y)) (a t : ℝ)
    (n : ℕ) (ρ : Density (CopyIndex A n × CopyIndex B n)) : ℝ :=
  ∑ h : History n, copyHistoryWeight M s n ρ h * Real.exp (t * centeredCount a h)

theorem copyMGF_cons_le (M : OneWayPOVM A B X Y) (s : Finset (X × Y))
    (a t : ℝ) (n : ℕ) (ρ : Density (CopyIndex A (n + 1) × CopyIndex B (n + 1)))
    (hρ : IsSeparable ρ.matrix) (b : Bool)
    (ih : ∀ σ : Density (CopyIndex A n × CopyIndex B n), IsSeparable σ.matrix →
      copyMGF M s a t n σ ≤ Real.exp ((n : ℝ) * t ^ 2 / 2)) :
    (∑ h : History n, copyHistoryWeight M s (n + 1) ρ (Fin.cons b h) *
      Real.exp (t * centeredCount a (Fin.cons b h))) ≤
      ((companionApply M (binaryOutcomeSet s b) (lastCopyDensity n ρ).matrix).trace.re *
        Real.exp (t * ((if b then 1 else 0) - a))) * Real.exp ((n : ℝ) * t ^ 2 / 2) := by
  let p := (companionApply M (binaryOutcomeSet s b) (lastCopyDensity n ρ).matrix).trace.re
  by_cases hp : 0 < p
  · have hp' : 0 < (companionApply M (binaryOutcomeSet s b) (lastCopyDensity n ρ).matrix).trace.re := hp
    simp only [copyHistoryWeight_cons, dif_pos hp', centeredCount_cons, mul_add, Real.exp_add]
    calc
      _ = (p * Real.exp (t * ((if b then 1 else 0) - a))) *
          copyMGF M s a t n (remainderDensity M (binaryOutcomeSet s b) (lastCopyDensity n ρ) hp') := by
        rw [copyMGF, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro h hh
        dsimp only [p]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (ih _ (remainderDensity_isSeparable M _ (lastCopyDensity n ρ)
          (lastCopyDensity_isSeparable n ρ hρ) hp'))
        (mul_nonneg hp.le (Real.exp_pos _).le)
  · have hp' : ¬0 < (companionApply M (binaryOutcomeSet s b) (lastCopyDensity n ρ).matrix).trace.re := hp
    have hp0 : p = 0 := le_antisymm (le_of_not_gt hp)
      (companionApply_probability_nonneg _ _ (lastCopyDensity n ρ).positive)
    simp only [copyHistoryWeight_cons, dif_neg hp', zero_mul, Finset.sum_const_zero]
    change 0 ≤ (p * _) * _
    rw [hp0, zero_mul, zero_mul]

theorem copyMGF_le_exp_of_separable (M : OneWayPOVM A B X Y) (s : Finset (X × Y))
    {a t : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (ht : 0 ≤ t)
    (hnull : ∀ σ : Density (A × B), IsSeparable σ.matrix →
      (coarseApply M s σ.matrix).trace.re ≤ a)
    (n : ℕ) (ρ : Density (CopyIndex A n × CopyIndex B n)) (hρ : IsSeparable ρ.matrix) :
    copyMGF M s a t n ρ ≤ Real.exp ((n : ℝ) * t ^ 2 / 2) := by
  induction n with
  | zero => simp [copyMGF, copyHistoryWeight, centeredCount, successCount, History]
  | succ n ih =>
    let σ := lastCopyDensity n ρ
    let q := (companionApply M s σ.matrix).trace.re
    let r := (companionApply M (Finset.univ \ s) σ.matrix).trace.re
    have hq0 : 0 ≤ q := companionApply_probability_nonneg M s σ.positive
    have hq : q ≤ a := by
      dsimp only [q]
      rw [companionApply_trace_eq_tested]
      exact hnull (testedDensity σ)
        (testedDensity_isSeparable σ (lastCopyDensity_isSeparable n ρ hρ))
    have hsum : q + r = 1 := by
      have hc := congrArg Complex.re (companionApply_trace_complement_sum M s σ.matrix)
      simpa only [Complex.add_re, σ.trace_one, Complex.one_re] using hc
    rw [copyMGF, sum_histories_cons, Finset.sum_add_distrib]
    calc
      _ ≤ (q * Real.exp (t * (1 - a))) * Real.exp ((n : ℝ) * t ^ 2 / 2) +
          (r * Real.exp (t * (-a))) * Real.exp ((n : ℝ) * t ^ 2 / 2) := by
        have hb1 := copyMGF_cons_le M s a t n ρ hρ true ih
        have hb0 := copyMGF_cons_le M s a t n ρ hρ false ih
        simpa only [binaryOutcomeSet, Bool.false_eq_true, ite_true, ite_false, zero_sub] using
          add_le_add hb1 hb0
      _ = Real.exp ((n : ℝ) * t ^ 2 / 2) * binaryMGF q a t := by
        have hr : r = 1 - q := by linarith
        rw [hr, binaryMGF]
        ring
      _ ≤ Real.exp ((n : ℝ) * t ^ 2 / 2) * Real.exp (t ^ 2 / 2) :=
        mul_le_mul_of_nonneg_left (binaryMGF_le_exp_half_sq hq0 hq ha0 ha1 ht)
          (Real.exp_pos _).le
      _ = Real.exp (((n + 1 : ℕ) : ℝ) * t ^ 2 / 2) := by
        rw [← Real.exp_add]
        congr 1
        push_cast
        ring

def copyTestProbability (M : OneWayPOVM A B X Y) (s : Finset (X × Y))
    (n : ℕ) (ρ : Density (CopyIndex A n × CopyIndex B n)) (P : History n → Prop) : ℝ := by
  classical
  exact ∑ h : History n, if P h then copyHistoryWeight M s n ρ h else 0

theorem copyTestProbability_mem_Icc (M : OneWayPOVM A B X Y) (s : Finset (X × Y))
    (n : ℕ) (ρ : Density (CopyIndex A n × CopyIndex B n)) (P : History n → Prop) :
    copyTestProbability M s n ρ P ∈ Set.Icc 0 1 := by
  classical
  constructor
  · unfold copyTestProbability
    apply Finset.sum_nonneg
    intro h hh
    split
    · exact copyHistoryWeight_nonneg M s n ρ h
    · exact le_refl _
  · rw [← copyHistoryWeight_sum_one M s n ρ]
    unfold copyTestProbability
    apply Finset.sum_le_sum
    intro h hh
    split
    · exact le_refl _
    · exact copyHistoryWeight_nonneg M s n ρ h

theorem copyTestProbability_le_exp_mul_copyMGF (M : OneWayPOVM A B X Y)
    (s : Finset (X × Y)) {a t threshold : ℝ} (ht : 0 ≤ t) (n : ℕ)
    (ρ : Density (CopyIndex A n × CopyIndex B n)) :
    copyTestProbability M s n ρ (fun h => threshold ≤ centeredCount a h) ≤
      Real.exp (-(t * threshold)) * copyMGF M s a t n ρ := by
  classical
  have hm : Real.exp (t * threshold) *
      copyTestProbability M s n ρ (fun h => threshold ≤ centeredCount a h) ≤
      copyMGF M s a t n ρ := by
    rw [copyTestProbability, Finset.mul_sum, copyMGF]
    apply Finset.sum_le_sum
    intro h hh
    by_cases he : threshold ≤ centeredCount a h
    · simp only [he, ite_true]
      rw [mul_comm (Real.exp (t * threshold))]
      exact mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left he ht))
        (copyHistoryWeight_nonneg M s n ρ h)
    · simp only [he, ite_false, mul_zero]
      exact mul_nonneg (copyHistoryWeight_nonneg M s n ρ h) (Real.exp_pos _).le
  calc
    _ = Real.exp (-(t * threshold)) * (Real.exp (t * threshold) *
        copyTestProbability M s n ρ (fun h => threshold ≤ centeredCount a h)) := by
      rw [← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_left hm (Real.exp_pos _).le

theorem copy_threshold_test_le_exp_of_separable (M : OneWayPOVM A B X Y)
    (s : Finset (X × Y)) {a gap : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hgap : 0 ≤ gap)
    (hnull : ∀ σ : Density (A × B), IsSeparable σ.matrix →
      (coarseApply M s σ.matrix).trace.re ≤ a)
    (n : ℕ) (ρ : Density (CopyIndex A n × CopyIndex B n)) (hρ : IsSeparable ρ.matrix) :
    copyTestProbability M s n ρ (thresholdTest a gap n) ≤
      Real.exp (-(n : ℝ) * gap ^ 2 / 2) := by
  calc
    _ ≤ Real.exp (-(gap * ((n : ℝ) * gap))) * copyMGF M s a gap n ρ :=
      copyTestProbability_le_exp_mul_copyMGF M s hgap n ρ
    _ ≤ Real.exp (-(gap * ((n : ℝ) * gap))) * Real.exp ((n : ℝ) * gap ^ 2 / 2) :=
      mul_le_mul_of_nonneg_left
        (copyMGF_le_exp_of_separable M s ha0 ha1 hgap hnull n ρ hρ) (Real.exp_pos _).le
    _ = Real.exp (-(n : ℝ) * gap ^ 2 / 2) := by
      rw [← Real.exp_add]
      congr 1
      ring

section ProductInput

variable {C D : Type*} [Fintype C] [Fintype D] [DecidableEq C] [DecidableEq D]

theorem fineKraus_companion_grouping (M : OneWayPOVM A B X Y) (z : X × Y) :
    (fineKraus (companionPOVM (C := C) (D := D) M) z).submatrix
      (companionGrouping (A := A) (B := B) (C := C) (D := D)) companionGrouping =
      fineKraus M z ⊗ₖ (1 : QMatrix (C × D)) := by
  rw [fineKraus_companion, ← Matrix.one_kronecker_one]
  ext u v
  simp only [Matrix.submatrix_apply, companionGrouping, Equiv.coe_fn_mk,
    fineKraus, Matrix.kroneckerMap_apply]
  ring

theorem bipartiteTensorDensity_grouping (ρ : Density (A × B)) (τ : Density (C × D)) :
    (bipartiteTensorDensity ρ τ).matrix.submatrix
      (companionGrouping (A := A) (B := B) (C := C) (D := D)) companionGrouping =
      ρ.matrix ⊗ₖ τ.matrix := by
  ext u v
  rfl

theorem companionApply_product_grouping (M : OneWayPOVM A B X Y)
    (s : Finset (X × Y)) (ρ : Density (A × B)) (τ : Density (C × D)) :
    (companionApply M s (bipartiteTensorDensity ρ τ).matrix).submatrix
      (companionGrouping (A := A) (B := B) (C := C) (D := D)) companionGrouping =
      coarseApply M s ρ.matrix ⊗ₖ τ.matrix := by
  let g := companionGrouping (A := A) (B := B) (C := C) (D := D)
  have hterm (z : X × Y) :
      (fineKraus (companionPOVM M) z * (bipartiteTensorDensity ρ τ).matrix *
        (fineKraus (companionPOVM M) z)ᴴ).submatrix g g =
      (fineKraus M z * ρ.matrix * (fineKraus M z)ᴴ) ⊗ₖ τ.matrix := by
    rw [← Matrix.submatrix_mul_equiv (e₂ := g),
      ← Matrix.submatrix_mul_equiv (e₂ := g),
      ← Matrix.conjTranspose_submatrix, fineKraus_companion_grouping,
      bipartiteTensorDensity_grouping, Matrix.conjTranspose_kronecker,
      Matrix.conjTranspose_one, ← Matrix.mul_kronecker_mul,
      ← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one]
  ext u v
  simp only [companionApply, coarseApply, Matrix.submatrix_apply,
    Matrix.kroneckerMap_apply, Matrix.sum_apply, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro z hz
  exact congrFun (congrFun (hterm z) u) v

theorem companionApply_product_trace (M : OneWayPOVM A B X Y)
    (s : Finset (X × Y)) (ρ : Density (A × B)) (τ : Density (C × D)) :
    (companionApply M s (bipartiteTensorDensity ρ τ).matrix).trace =
      (coarseApply M s ρ.matrix).trace := by
  let g := companionGrouping (A := A) (B := B) (C := C) (D := D)
  have hg (T : QMatrix ((A × C) × (B × D))) :
      (T.submatrix g g).trace = T.trace := g.sum_comp (fun i => T i i)
  rw [← hg, companionApply_product_grouping, Matrix.trace_kronecker,
    τ.trace_one, mul_one]

theorem remainderMarginal_companion_product (M : OneWayPOVM A B X Y)
    (s : Finset (X × Y)) (ρ : Density (A × B)) (τ : Density (C × D)) :
    remainderMarginal (companionApply M s (bipartiteTensorDensity ρ τ).matrix) =
      (coarseApply M s ρ.matrix).trace.re • τ.matrix := by
  rw [remainderMarginal_eq_partialTrace, companionApply_product_grouping]
  have hreal : ((coarseApply M s ρ.matrix).trace.re : ℂ) =
      (coarseApply M s ρ.matrix).trace := by
    have him := (Complex.nonneg_iff.mp (coarseApply_posSemidef M s ρ.positive).trace_nonneg).2
    apply Complex.ext <;> simp [him]
  ext u v
  simp only [partialTraceLeft, QuantumProver.WernerEndpoint.partialTraceRight,
    Matrix.kroneckerMap_apply, Matrix.trace, Matrix.diag,
    Matrix.smul_apply, Complex.real_smul]
  rw [← Finset.sum_mul]
  exact congrArg (fun z : ℂ => z * τ.matrix u v) hreal.symm

theorem remainderDensity_product (M : OneWayPOVM A B X Y)
    (s : Finset (X × Y)) (ρ : Density (A × B)) (τ : Density (C × D))
    (hp : 0 < (companionApply M s (bipartiteTensorDensity ρ τ).matrix).trace.re) :
    remainderDensity M s (bipartiteTensorDensity ρ τ) hp = τ := by
  apply density_ext
  change (remainderMarginal (companionApply M s (bipartiteTensorDensity ρ τ).matrix)).trace.re⁻¹ •
    remainderMarginal (companionApply M s (bipartiteTensorDensity ρ τ).matrix) = τ.matrix
  rw [remainderMarginal_trace, companionApply_product_trace,
    remainderMarginal_companion_product, smul_smul]
  have hp' : 0 < (coarseApply M s ρ.matrix).trace.re := by
    simpa only [companionApply_product_trace] using hp
  rw [inv_mul_cancel₀ hp'.ne', one_smul]

end ProductInput

theorem lastCopyDensity_tensorCopies (ρ : Density (A × B)) (n : ℕ) :
    lastCopyDensity n (tensorCopies ρ (n + 1)) =
      bipartiteTensorDensity ρ (tensorCopies ρ n) := by
  apply density_ext
  ext u v
  change (tensorCopies ρ n).matrix (u.1.2, u.2.2) (v.1.2, v.2.2) *
      ρ.matrix (u.1.1, u.2.1) (v.1.1, v.2.1) =
    ρ.matrix (u.1.1, u.2.1) (v.1.1, v.2.1) *
      (tensorCopies ρ n).matrix (u.1.2, u.2.2) (v.1.2, v.2.2)
  exact mul_comm _ _

theorem coarseApply_binary_trace (M : OneWayPOVM A B X Y) (s : Finset (X × Y))
    (ρ : Density (A × B)) (b : Bool) :
    (coarseApply M (binaryOutcomeSet s b) ρ.matrix).trace.re =
      binaryWeight (coarseApply M s ρ.matrix).trace.re b := by
  cases b with
  | false =>
    simp only [binaryOutcomeSet, Bool.false_eq_true, ite_false, binaryWeight]
    have hs := congrArg Complex.re (coarseApply_trace_complement_sum M s ρ.matrix)
    simp only [Complex.add_re, ρ.trace_one, Complex.one_re] at hs
    linarith
  | true => rfl

theorem historyWeight_iid_cons (b : ℝ) (n : ℕ) (z : Bool) (h : History n) :
    historyWeight (fun _ _ => b) (n + 1) (Fin.cons z h) =
      binaryWeight b z * historyWeight (fun _ _ => b) n h := by
  rw [historyWeight_iid, Fin.prod_univ_succ, historyWeight_iid]
  simp only [Fin.cons_zero, Fin.cons_succ]

theorem copyHistoryWeight_tensorCopies (M : OneWayPOVM A B X Y)
    (s : Finset (X × Y)) (ρ : Density (A × B)) (n : ℕ) (h : History n) :
    copyHistoryWeight M s n (tensorCopies ρ n) h =
      historyWeight (fun _ _ => (coarseApply M s ρ.matrix).trace.re) n h := by
  induction n with
  | zero => rfl
  | succ n ih =>
    let q := (coarseApply M s ρ.matrix).trace.re
    let z := h 0
    let σ := bipartiteTensorDensity ρ (tensorCopies ρ n)
    let p := (companionApply M (binaryOutcomeSet s z) σ.matrix).trace.re
    have hpq : p = binaryWeight q z := by
      dsimp only [p, σ, q]
      rw [companionApply_product_trace, coarseApply_binary_trace]
    rw [← Fin.cons_self_tail h, copyHistoryWeight_cons, lastCopyDensity_tensorCopies]
    by_cases hp : 0 < p
    · have hp' : 0 < (companionApply M (binaryOutcomeSet s (h 0))
        (bipartiteTensorDensity ρ (tensorCopies ρ n)).matrix).trace.re := hp
      simp only [dif_pos hp']
      rw [remainderDensity_product, ih, historyWeight_iid_cons]
      exact congrArg (fun r : ℝ => r * historyWeight (fun _ _ => q) n (Fin.tail h)) hpq
    · have hp' : ¬0 < (companionApply M (binaryOutcomeSet s (h 0))
        (bipartiteTensorDensity ρ (tensorCopies ρ n)).matrix).trace.re := hp
      have hp0 : p = 0 := le_antisymm (le_of_not_gt hp)
        (companionApply_probability_nonneg M _ σ.positive)
      simp only [dif_neg hp']
      rw [historyWeight_iid_cons, ← hpq, hp0, zero_mul]

theorem copyTestProbability_tensorCopies (M : OneWayPOVM A B X Y)
    (s : Finset (X × Y)) (ρ : Density (A × B)) (n : ℕ) (P : History n → Prop) :
    copyTestProbability M s n (tensorCopies ρ n) P =
      eventProbability (fun _ _ => (coarseApply M s ρ.matrix).trace.re) n P := by
  classical
  simp only [copyTestProbability, eventProbability, copyHistoryWeight_tensorCopies]

theorem copy_iid_rejection_le_exp (M : OneWayPOVM A B X Y) (s : Finset (X × Y))
    (ρ : Density (A × B)) {a δ : ℝ}
    (ha : a ≤ (coarseApply M s ρ.matrix).trace.re) (hδ : 0 ≤ δ) (n : ℕ) :
    copyTestProbability M s n (tensorCopies ρ n)
      (fun h => ¬thresholdTest a ((1 - δ) * ((coarseApply M s ρ.matrix).trace.re - a)) n h) ≤
      Real.exp (-(n : ℝ) * (δ * ((coarseApply M s ρ.matrix).trace.re - a)) ^ 2 / 2) := by
  rw [copyTestProbability_tensorCopies]
  exact iid_rejection_le_exp (coarseApply_probability_nonneg M s ρ.positive)
    (coarseApply_probability_le_one M s ρ) ha hδ n

theorem copy_iid_acceptance_tendsto_one (M : OneWayPOVM A B X Y)
    (s : Finset (X × Y)) (ρ : Density (A × B)) {a δ : ℝ}
    (ha : a < (coarseApply M s ρ.matrix).trace.re) (hδ : 0 < δ) :
    Filter.Tendsto (fun n : ℕ => copyTestProbability M s n (tensorCopies ρ n)
      (thresholdTest a ((1 - δ) * ((coarseApply M s ρ.matrix).trace.re - a)) n))
      Filter.atTop (𝓝 1) := by
  simp only [copyTestProbability_tensorCopies]
  exact iid_acceptance_tendsto_one (coarseApply_probability_nonneg M s ρ.positive)
    (coarseApply_probability_le_one M s ρ) ha hδ

end QuantumProver.DepolarizingSquashedEntanglement.BCYCopyTesting

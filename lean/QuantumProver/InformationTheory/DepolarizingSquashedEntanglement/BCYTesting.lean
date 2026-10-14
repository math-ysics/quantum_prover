import Mathlib
import QuantumProver.InformationTheory.DepolarizingSquashedEntanglement.Definitions
import QuantumProver.InformationTheory.DepolarizingSquashedEntanglement.BCYMeasurement

set_option autoImplicit false
noncomputable section

open scoped BigOperators Topology ComplexOrder

namespace QuantumProver.DepolarizingSquashedEntanglement.BCYTesting

abbrev History (n : ℕ) := Fin n → Bool

def binaryWeight (q : ℝ) (b : Bool) : ℝ := if b then q else 1 - q

def historyWeight (q : (n : ℕ) → History n → ℝ) : (n : ℕ) → History n → ℝ
  | 0, _ => 1
  | n + 1, h => historyWeight q n (Fin.init h) * binaryWeight (q n (Fin.init h)) (h (Fin.last n))

@[simp] theorem historyWeight_snoc (q : (n : ℕ) → History n → ℝ)
    (n : ℕ) (h : History n) (b : Bool) :
    historyWeight q (n + 1) (Fin.snoc h b) = historyWeight q n h * binaryWeight (q n h) b := by
  simp only [historyWeight, Fin.init_snoc, Fin.snoc_last]

theorem sum_histories_succ {n : ℕ} (f : History (n + 1) → ℝ) :
    ∑ h, f h = ∑ h : History n, (f (Fin.snoc h true) + f (Fin.snoc h false)) := by
  rw [← (Fin.snocEquiv (fun _ : Fin (n + 1) => Bool)).sum_comp f,
    Fintype.sum_prod_type, Finset.sum_comm]
  simp only [Fintype.sum_bool]
  rfl

theorem historyWeight_nonneg (q : (n : ℕ) → History n → ℝ)
    (hq : ∀ n h, q n h ∈ Set.Icc 0 1) (n : ℕ) (h : History n) :
    0 ≤ historyWeight q n h := by
  induction n with
  | zero => exact zero_le_one
  | succ n ih =>
    rw [historyWeight]
    apply mul_nonneg (ih _)
    unfold binaryWeight
    split
    · exact (hq n _).1
    · exact sub_nonneg.mpr (hq n _).2

theorem historyWeight_sum_one (q : (n : ℕ) → History n → ℝ) (n : ℕ) :
    ∑ h : History n, historyWeight q n h = 1 := by
  induction n with
  | zero => simp [historyWeight, History]
  | succ n ih =>
    rw [sum_histories_succ]
    calc
      _ = ∑ h : History n, historyWeight q n h := by
        apply Finset.sum_congr rfl
        intro h hh
        simp only [historyWeight_snoc, binaryWeight, Bool.false_eq_true, ite_true, ite_false]
        ring
      _ = 1 := ih

theorem conditional_success_probability (q : (n : ℕ) → History n → ℝ)
    (n : ℕ) (h : History n) (hh : 0 < historyWeight q n h) :
    historyWeight q (n + 1) (Fin.snoc h true) / historyWeight q n h = q n h := by
  simp only [historyWeight_snoc, binaryWeight, ite_true]
  exact mul_div_cancel_left₀ _ hh.ne'

def successCount {n : ℕ} (h : History n) : ℝ := ∑ i, if h i then 1 else 0

def centeredCount (a : ℝ) {n : ℕ} (h : History n) : ℝ := successCount h - (n : ℝ) * a

@[simp] theorem successCount_snoc {n : ℕ} (h : History n) (b : Bool) :
    successCount (Fin.snoc h b) = successCount h + (if b then 1 else 0) := by
  simp only [successCount, Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last]

@[simp] theorem centeredCount_snoc (a : ℝ) {n : ℕ} (h : History n) (b : Bool) :
    centeredCount a (Fin.snoc h b) = centeredCount a h + ((if b then 1 else 0) - a) := by
  simp only [centeredCount, successCount_snoc, Nat.cast_add, Nat.cast_one]
  ring

def binaryMGF (q a t : ℝ) : ℝ :=
  q * Real.exp (t * (1 - a)) + (1 - q) * Real.exp (t * (-a))

theorem binaryMGF_le_exp_half_sq {q a t : ℝ} (hq0 : 0 ≤ q) (hqa : q ≤ a)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (ht : 0 ≤ t) :
    binaryMGF q a t ≤ Real.exp (t ^ 2 / 2) := by
  have hq1 : q ≤ 1 := hqa.trans ha1
  have hx : |1 - a| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hy : |-a| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hxexp : Real.exp (t * (1 - a)) ≤ Real.cosh t + (1 - a) * Real.sinh t := by
    simpa only [mul_comm] using Real.exp_mul_le_cosh_add_mul_sinh hx t
  have hyexp : Real.exp (t * (-a)) ≤ Real.cosh t + (-a) * Real.sinh t := by
    simpa only [mul_comm] using Real.exp_mul_le_cosh_add_mul_sinh hy t
  calc
    binaryMGF q a t ≤ q * (Real.cosh t + (1 - a) * Real.sinh t) +
        (1 - q) * (Real.cosh t + (-a) * Real.sinh t) :=
      add_le_add (mul_le_mul_of_nonneg_left hxexp hq0)
        (mul_le_mul_of_nonneg_left hyexp (sub_nonneg.mpr hq1))
    _ = Real.cosh t + (q - a) * Real.sinh t := by ring
    _ ≤ Real.cosh t := add_le_of_nonpos_right
      (mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hqa) (Real.sinh_nonneg_iff.mpr ht))
    _ ≤ Real.exp (t ^ 2 / 2) := Real.cosh_le_exp_half_sq t

def historyMGF (q : (n : ℕ) → History n → ℝ) (a t : ℝ) (n : ℕ) : ℝ :=
  ∑ h : History n, historyWeight q n h * Real.exp (t * centeredCount a h)

theorem historyMGF_succ (q : (n : ℕ) → History n → ℝ) (a t : ℝ) (n : ℕ) :
    historyMGF q a t (n + 1) = ∑ h : History n,
      (historyWeight q n h * Real.exp (t * centeredCount a h)) * binaryMGF (q n h) a t := by
  rw [historyMGF, sum_histories_succ]
  apply Finset.sum_congr rfl
  intro h hh
  simp only [historyWeight_snoc, centeredCount_snoc, binaryWeight, Bool.false_eq_true, ite_true, ite_false,
    binaryMGF, mul_add, Real.exp_add]
  ring

theorem historyMGF_le_exp (q : (n : ℕ) → History n → ℝ)
    {a t : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hq : ∀ n h, q n h ∈ Set.Icc 0 a) (ht : 0 ≤ t) (n : ℕ) :
    historyMGF q a t n ≤ Real.exp ((n : ℝ) * t ^ 2 / 2) := by
  have hq01 : ∀ n h, q n h ∈ Set.Icc 0 1 := fun n h => ⟨(hq n h).1, (hq n h).2.trans ha1⟩
  induction n with
  | zero => simp [historyMGF, historyWeight, centeredCount, successCount, History]
  | succ n ih =>
    rw [historyMGF_succ]
    calc
      _ ≤ ∑ h : History n,
          (historyWeight q n h * Real.exp (t * centeredCount a h)) * Real.exp (t ^ 2 / 2) := by
        apply Finset.sum_le_sum
        intro h hh
        exact mul_le_mul_of_nonneg_left
          (binaryMGF_le_exp_half_sq (hq n h).1 (hq n h).2 ha0 ha1 ht)
          (mul_nonneg (historyWeight_nonneg q hq01 n h) (Real.exp_pos _).le)
      _ = historyMGF q a t n * Real.exp (t ^ 2 / 2) := (Finset.sum_mul _ _ _).symm
      _ ≤ Real.exp ((n : ℝ) * t ^ 2 / 2) * Real.exp (t ^ 2 / 2) :=
        mul_le_mul_of_nonneg_right ih (Real.exp_pos _).le
      _ = Real.exp (((n + 1 : ℕ) : ℝ) * t ^ 2 / 2) := by
        rw [← Real.exp_add]
        congr 1
        push_cast
        ring

def eventProbability (q : (n : ℕ) → History n → ℝ) (n : ℕ)
    (P : History n → Prop) : ℝ := by
  classical
  exact ∑ h : History n, if P h then historyWeight q n h else 0

def thresholdTest (a gap : ℝ) (n : ℕ) (h : History n) : Prop :=
  (n : ℝ) * gap ≤ centeredCount a h

theorem eventProbability_nonneg (q : (n : ℕ) → History n → ℝ)
    (hq : ∀ n h, q n h ∈ Set.Icc 0 1) (n : ℕ) (P : History n → Prop) :
    0 ≤ eventProbability q n P := by
  classical
  unfold eventProbability
  apply Finset.sum_nonneg
  intro h hh
  split
  · exact historyWeight_nonneg q hq n h
  · exact le_refl _

theorem eventProbability_le_one (q : (n : ℕ) → History n → ℝ)
    (hq : ∀ n h, q n h ∈ Set.Icc 0 1) (n : ℕ) (P : History n → Prop) :
    eventProbability q n P ≤ 1 := by
  classical
  unfold eventProbability
  rw [← historyWeight_sum_one q n]
  apply Finset.sum_le_sum
  intro h hh
  split
  · exact le_refl _
  · exact historyWeight_nonneg q hq n h

theorem eventProbability_le_exp_mul_historyMGF (q : (n : ℕ) → History n → ℝ)
    (hq : ∀ n h, q n h ∈ Set.Icc 0 1) {a t threshold : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    eventProbability q n (fun h => threshold ≤ centeredCount a h) ≤
      Real.exp (-(t * threshold)) * historyMGF q a t n := by
  classical
  have hmark : Real.exp (t * threshold) *
      eventProbability q n (fun h => threshold ≤ centeredCount a h) ≤ historyMGF q a t n := by
    rw [eventProbability, Finset.mul_sum, historyMGF]
    apply Finset.sum_le_sum
    intro h hh
    by_cases he : threshold ≤ centeredCount a h
    · simp only [he, ite_true]
      rw [mul_comm (Real.exp (t * threshold))]
      exact mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left he ht))
        (historyWeight_nonneg q hq n h)
    · simp only [he, ite_false, mul_zero]
      exact mul_nonneg (historyWeight_nonneg q hq n h) (Real.exp_pos _).le
  calc
    _ = Real.exp (-(t * threshold)) * (Real.exp (t * threshold) *
        eventProbability q n (fun h => threshold ≤ centeredCount a h)) := by
      rw [← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]
    _ ≤ Real.exp (-(t * threshold)) * historyMGF q a t n :=
      mul_le_mul_of_nonneg_left hmark (Real.exp_pos _).le

theorem finite_history_azuma (q : (n : ℕ) → History n → ℝ)
    {a gap : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hq : ∀ n h, q n h ∈ Set.Icc 0 a) (hgap : 0 ≤ gap) (n : ℕ) :
    eventProbability q n (thresholdTest a gap n) ≤
      Real.exp (-(n : ℝ) * gap ^ 2 / 2) := by
  have hq01 : ∀ n h, q n h ∈ Set.Icc 0 1 :=
    fun n h => ⟨(hq n h).1, (hq n h).2.trans ha1⟩
  calc
    _ ≤ Real.exp (-(gap * ((n : ℝ) * gap))) * historyMGF q a gap n :=
      eventProbability_le_exp_mul_historyMGF q hq01 hgap n
    _ ≤ Real.exp (-(gap * ((n : ℝ) * gap))) *
        Real.exp ((n : ℝ) * gap ^ 2 / 2) :=
      mul_le_mul_of_nonneg_left (historyMGF_le_exp q ha0 ha1 hq hgap n) (Real.exp_pos _).le
    _ = Real.exp (-(n : ℝ) * gap ^ 2 / 2) := by
      rw [← Real.exp_add]
      congr 1
      ring

theorem historyWeight_iid (b : ℝ) (n : ℕ) (h : History n) :
    historyWeight (fun _ _ => b) n h = ∏ i, binaryWeight b (h i) := by
  induction n with
  | zero => simp [historyWeight]
  | succ n ih =>
    rw [historyWeight, ih, Fin.prod_univ_castSucc]
    rfl

def flipHistory {n : ℕ} (h : History n) : History n := fun i => !(h i)

def flipHistoryEquiv (n : ℕ) : History n ≃ History n where
  toFun := flipHistory
  invFun := flipHistory
  left_inv h := by ext i; simp [flipHistory]
  right_inv h := by ext i; simp [flipHistory]

theorem successCount_flip {n : ℕ} (h : History n) :
    successCount (flipHistory h) = (n : ℝ) - successCount h := by
  calc
    _ = ∑ i : Fin n, (1 - (if h i then 1 else 0) : ℝ) := by
      apply Finset.sum_congr rfl
      intro i hi
      cases hb : h i <;> simp [flipHistory, hb]
    _ = (n : ℝ) - successCount h := by
      simp [Finset.sum_sub_distrib, successCount]

theorem binaryWeight_flip (b : ℝ) (z : Bool) :
    binaryWeight (1 - b) (!z) = binaryWeight b z := by
  cases z <;> simp [binaryWeight]

theorem historyWeight_iid_flip (b : ℝ) (n : ℕ) (h : History n) :
    historyWeight (fun _ _ => 1 - b) n (flipHistory h) =
      historyWeight (fun _ _ => b) n h := by
  simp only [historyWeight_iid, flipHistory, binaryWeight_flip]

theorem eventProbability_iid_flip (b : ℝ) (n : ℕ) (P : History n → Prop) :
    eventProbability (fun _ _ => 1 - b) n P =
      eventProbability (fun _ _ => b) n (fun h => P (flipHistory h)) := by
  classical
  unfold eventProbability
  rw [← (flipHistoryEquiv n).sum_comp
    (fun h => if P h then historyWeight (fun _ _ => 1 - b) n h else 0)]
  apply Finset.sum_congr rfl
  intro h hh
  change (if P (flipHistory h) then historyWeight (fun _ _ => 1 - b) n (flipHistory h) else 0) = _
  rw [historyWeight_iid_flip]

theorem eventProbability_mono (q : (n : ℕ) → History n → ℝ)
    (hq : ∀ n h, q n h ∈ Set.Icc 0 1) (n : ℕ) {P Q : History n → Prop}
    (hPQ : ∀ h, P h → Q h) : eventProbability q n P ≤ eventProbability q n Q := by
  classical
  unfold eventProbability
  apply Finset.sum_le_sum
  intro h hh
  by_cases hP : P h
  · simp only [hP, hPQ h hP, ite_true]
    exact le_refl _
  · simp only [hP, ite_false]
    split
    · exact historyWeight_nonneg q hq n h
    · exact le_refl _

theorem eventProbability_compl (q : (n : ℕ) → History n → ℝ)
    (n : ℕ) (P : History n → Prop) :
    eventProbability q n P + eventProbability q n (fun h => ¬P h) = 1 := by
  classical
  rw [eventProbability, eventProbability, ← Finset.sum_add_distrib,
    ← historyWeight_sum_one q n]
  apply Finset.sum_congr rfl
  intro h hh
  by_cases hp : P h <;> simp [hp]

theorem iid_rejection_le_exp {a b δ : ℝ} (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (hba : a ≤ b) (hδ : 0 ≤ δ) (n : ℕ) :
    eventProbability (fun _ _ => b) n
      (fun h => ¬thresholdTest a ((1 - δ) * (b - a)) n h) ≤
      Real.exp (-(n : ℝ) * (δ * (b - a)) ^ 2 / 2) := by
  have hq : ∀ m (h : History m), (fun _ _ => b) m h ∈ Set.Icc 0 1 :=
    fun _ _ => ⟨hb0, hb1⟩
  have hg : 0 ≤ δ * (b - a) := mul_nonneg hδ (sub_nonneg.mpr hba)
  calc
    _ ≤ eventProbability (fun _ _ => b) n
        (fun h => thresholdTest (1 - b) (δ * (b - a)) n (flipHistory h)) := by
      apply eventProbability_mono _ hq n
      intro h hh
      unfold thresholdTest centeredCount at hh ⊢
      rw [successCount_flip]
      push_neg at hh
      nlinarith
    _ = eventProbability (fun _ _ => 1 - b) n
        (thresholdTest (1 - b) (δ * (b - a)) n) :=
      (eventProbability_iid_flip b n _).symm
    _ ≤ Real.exp (-(n : ℝ) * (δ * (b - a)) ^ 2 / 2) :=
      finite_history_azuma _ (sub_nonneg.mpr hb1) (by linarith)
        (fun _ _ => ⟨sub_nonneg.mpr hb1, le_refl _⟩) hg n

theorem exp_quadratic_decay_tendsto {gap : ℝ} (hgap : 0 < gap) :
    Filter.Tendsto (fun n : ℕ => Real.exp (-(n : ℝ) * gap ^ 2 / 2))
      Filter.atTop (𝓝 0) := by
  have hc : 0 < gap ^ 2 / 2 := div_pos (sq_pos_of_pos hgap) (by norm_num)
  have hnat : Filter.Tendsto (fun n : ℕ => (n : ℝ)) Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop
  have ht : Filter.Tendsto (fun n : ℕ => (n : ℝ) * (gap ^ 2 / 2))
      Filter.atTop Filter.atTop :=
    hnat.atTop_mul_const hc
  convert Real.tendsto_exp_neg_atTop_nhds_zero.comp ht using 1
  ext n
  congr 1
  ring

theorem iid_rejection_tendsto_zero {a b δ : ℝ} (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (hba : a < b) (hδ : 0 < δ) :
    Filter.Tendsto (fun n : ℕ => eventProbability (fun _ _ => b) n
        (fun h => ¬thresholdTest a ((1 - δ) * (b - a)) n h))
      Filter.atTop (𝓝 0) := by
  exact squeeze_zero
    (fun n => eventProbability_nonneg _ (fun _ _ => ⟨hb0, hb1⟩) n _)
    (fun n => iid_rejection_le_exp hb0 hb1 hba.le hδ.le n)
    (exp_quadratic_decay_tendsto (mul_pos hδ (sub_pos.mpr hba)))

theorem iid_acceptance_tendsto_one {a b δ : ℝ} (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (hba : a < b) (hδ : 0 < δ) :
    Filter.Tendsto (fun n : ℕ => eventProbability (fun _ _ => b) n
        (thresholdTest a ((1 - δ) * (b - a)) n)) Filter.atTop (𝓝 1) := by
  have heq : (fun n : ℕ => eventProbability (fun _ _ => b) n
      (thresholdTest a ((1 - δ) * (b - a)) n)) =
      (fun n : ℕ => 1 - eventProbability (fun _ _ => b) n
        (fun h => ¬thresholdTest a ((1 - δ) * (b - a)) n h)) := by
    funext n
    have hc := eventProbability_compl (fun _ _ => b) n
      (thresholdTest a ((1 - δ) * (b - a)) n)
    linarith
  rw [heq]
  have hc : Filter.Tendsto (fun _ : ℕ => (1 : ℝ)) Filter.atTop (𝓝 1) :=
    tendsto_const_nhds
  simpa using hc.sub (iid_rejection_tendsto_zero hb0 hb1 hba hδ)

section MatrixHistories

open BCYMeasurement

variable {A B X Y : Type*} [Fintype A] [Fintype B] [Fintype X] [Fintype Y]
  [DecidableEq A] [DecidableEq B] [DecidableEq X] [DecidableEq Y]

structure AdaptiveOneWayExperiment (A B X Y : Type*)
    [Fintype A] [Fintype B] [Fintype X] [Fintype Y]
    [DecidableEq A] [DecidableEq B] [DecidableEq X] [DecidableEq Y] where
  measurement : (n : ℕ) → History n → OneWayPOVM A B X Y
  acceptFine : (n : ℕ) → History n → Finset (X × Y)

def outcomeSet (E : AdaptiveOneWayExperiment A B X Y) (n : ℕ)
    (h : History n) (b : Bool) : Finset (X × Y) :=
  if b then E.acceptFine n h else Finset.univ \ E.acceptFine n h

def historyState (E : AdaptiveOneWayExperiment A B X Y) (ρ : QMatrix (A × B)) :
    (n : ℕ) → History n → QMatrix (A × B)
  | 0, _ => ρ
  | n + 1, h => coarseApply (E.measurement n (Fin.init h))
      (outcomeSet E n (Fin.init h) (h (Fin.last n))) (historyState E ρ n (Fin.init h))

@[simp] theorem historyState_snoc (E : AdaptiveOneWayExperiment A B X Y)
    (ρ : QMatrix (A × B)) (n : ℕ) (h : History n) (b : Bool) :
    historyState E ρ (n + 1) (Fin.snoc h b) =
      coarseApply (E.measurement n h) (outcomeSet E n h b) (historyState E ρ n h) := by
  simp only [historyState, Fin.init_snoc, Fin.snoc_last]

theorem historyState_posSemidef (E : AdaptiveOneWayExperiment A B X Y)
    {ρ : QMatrix (A × B)} (hρ : ρ.PosSemidef) (n : ℕ) (h : History n) :
    (historyState E ρ n h).PosSemidef := by
  induction n with
  | zero => exact hρ
  | succ n ih => exact coarseApply_posSemidef _ _ (ih _)

theorem historyState_mem_cone (E : AdaptiveOneWayExperiment A B X Y)
    {ρ : QMatrix (A × B)} (hρ : ρ ∈ separableCone A B) (n : ℕ) (h : History n) :
    historyState E ρ n h ∈ separableCone A B := by
  induction n with
  | zero => exact hρ
  | succ n ih => exact coarseApply_mem_cone _ _ (ih _)

def conditionalBorn (E : AdaptiveOneWayExperiment A B X Y) (ρ : QMatrix (A × B))
    (n : ℕ) (h : History n) : ℝ := by
  classical
  exact if 0 < (historyState E ρ n h).trace.re then
    (coarseApply (E.measurement n h) (E.acceptFine n h) (historyState E ρ n h)).trace.re /
      (historyState E ρ n h).trace.re else 0

def historyDensity (E : AdaptiveOneWayExperiment A B X Y) (ρ : Density (A × B))
    (n : ℕ) (h : History n) (ht : 0 < (historyState E ρ.matrix n h).trace.re) :
    Density (A × B) :=
  normalizedDensity _ (historyState_posSemidef E ρ.positive n h) ht

theorem historyDensity_isSeparable (E : AdaptiveOneWayExperiment A B X Y)
    (ρ : Density (A × B)) (hρ : IsSeparable ρ.matrix) (n : ℕ) (h : History n)
    (ht : 0 < (historyState E ρ.matrix n h).trace.re) :
    IsSeparable (historyDensity E ρ n h ht).matrix :=
  normalize_cone_isSeparable (historyState_mem_cone E (isSeparable_mem_cone hρ) n h) ht

theorem conditionalBorn_eq_historyDensity (E : AdaptiveOneWayExperiment A B X Y)
    (ρ : Density (A × B)) (n : ℕ) (h : History n)
    (ht : 0 < (historyState E ρ.matrix n h).trace.re) :
    conditionalBorn E ρ.matrix n h =
      (coarseApply (E.measurement n h) (E.acceptFine n h) (historyDensity E ρ n h ht).matrix).trace.re := by
  rw [conditionalBorn, if_pos ht]
  exact (normalizedDensity_coarse_probability _ _ _ _ ht).symm

theorem conditionalBorn_mem_Icc (E : AdaptiveOneWayExperiment A B X Y)
    (ρ : Density (A × B)) (n : ℕ) (h : History n) :
    conditionalBorn E ρ.matrix n h ∈ Set.Icc 0 1 := by
  by_cases ht : 0 < (historyState E ρ.matrix n h).trace.re
  · rw [conditionalBorn_eq_historyDensity E ρ n h ht]
    exact ⟨coarseApply_probability_nonneg _ _ (historyDensity E ρ n h ht).positive,
      coarseApply_probability_le_one _ _ (historyDensity E ρ n h ht)⟩
  · simp only [conditionalBorn, if_neg ht]
    exact ⟨le_refl _, zero_le_one⟩

theorem historyWeight_conditionalBorn_eq_trace (E : AdaptiveOneWayExperiment A B X Y)
    (ρ : Density (A × B)) (n : ℕ) (h : History n) :
    historyWeight (conditionalBorn E ρ.matrix) n h = (historyState E ρ.matrix n h).trace.re := by
  induction n with
  | zero => simp [historyWeight, historyState, ρ.trace_one]
  | succ n ih =>
    rw [historyWeight, historyState, ih]
    let R := historyState E ρ.matrix n (Fin.init h)
    have hR : R.PosSemidef := historyState_posSemidef E ρ.positive n (Fin.init h)
    change R.trace.re * binaryWeight (conditionalBorn E ρ.matrix n (Fin.init h)) (h (Fin.last n)) =
      (coarseApply (E.measurement n (Fin.init h))
        (outcomeSet E n (Fin.init h) (h (Fin.last n))) R).trace.re
    by_cases ht : 0 < R.trace.re
    · have hqeq : conditionalBorn E ρ.matrix n (Fin.init h) =
          (coarseApply (E.measurement n (Fin.init h)) (E.acceptFine n (Fin.init h)) R).trace.re /
            R.trace.re := by
        change (if 0 < R.trace.re then _ else 0) = _
        exact if_pos ht
      have hmul : R.trace.re *
          ((coarseApply (E.measurement n (Fin.init h)) (E.acceptFine n (Fin.init h)) R).trace.re /
            R.trace.re) =
          (coarseApply (E.measurement n (Fin.init h)) (E.acceptFine n (Fin.init h)) R).trace.re := by
        field_simp
      cases hb : h (Fin.last n) <;>
        simp only [hb, outcomeSet, binaryWeight, Bool.false_eq_true, ite_true, ite_false, hqeq]
      · have hsum := congrArg Complex.re
          (coarseApply_trace_complement_sum (E.measurement n (Fin.init h))
            (E.acceptFine n (Fin.init h)) R)
        rw [Complex.add_re] at hsum
        nlinarith [hmul]
      · exact hmul
    · have hn := (Complex.nonneg_iff.mp hR.trace_nonneg).1
      have hz : R.trace.re = 0 := le_antisymm (le_of_not_gt ht) hn
      have hRzero : R = 0 := by
        apply hR.trace_eq_zero_iff.mp
        have him := (Complex.nonneg_iff.mp hR.trace_nonneg).2.symm
        apply Complex.ext <;> simp [hz, him]
      rw [hz, zero_mul, hRzero, coarseApply_zero]
      simp

def bornTestProbability (E : AdaptiveOneWayExperiment A B X Y) (ρ : Density (A × B))
    (n : ℕ) (P : History n → Prop) : ℝ := by
  classical
  exact ∑ h : History n, if P h then (historyState E ρ.matrix n h).trace.re else 0

theorem bornTestProbability_eq_eventProbability (E : AdaptiveOneWayExperiment A B X Y)
    (ρ : Density (A × B)) (n : ℕ) (P : History n → Prop) :
    bornTestProbability E ρ n P = eventProbability (conditionalBorn E ρ.matrix) n P := by
  classical
  unfold bornTestProbability eventProbability
  apply Finset.sum_congr rfl
  intro h hh
  rw [historyWeight_conditionalBorn_eq_trace]

theorem bornTestProbability_mem_Icc (E : AdaptiveOneWayExperiment A B X Y)
    (ρ : Density (A × B)) (n : ℕ) (P : History n → Prop) :
    bornTestProbability E ρ n P ∈ Set.Icc 0 1 := by
  rw [bornTestProbability_eq_eventProbability]
  exact ⟨eventProbability_nonneg _ (conditionalBorn_mem_Icc E ρ) n P,
    eventProbability_le_one _ (conditionalBorn_mem_Icc E ρ) n P⟩

theorem conditionalBorn_le_of_separable (E : AdaptiveOneWayExperiment A B X Y)
    (ρ : Density (A × B)) (hρ : IsSeparable ρ.matrix) {a : ℝ} (ha0 : 0 ≤ a)
    (hnull : ∀ n h (σ : Density (A × B)), IsSeparable σ.matrix →
      (coarseApply (E.measurement n h) (E.acceptFine n h) σ.matrix).trace.re ≤ a)
    (n : ℕ) (h : History n) : conditionalBorn E ρ.matrix n h ≤ a := by
  by_cases ht : 0 < (historyState E ρ.matrix n h).trace.re
  · rw [conditionalBorn_eq_historyDensity E ρ n h ht]
    exact hnull n h _ (historyDensity_isSeparable E ρ hρ n h ht)
  · simp only [conditionalBorn, if_neg ht]
    exact ha0

theorem born_threshold_test_le_exp_of_separable (E : AdaptiveOneWayExperiment A B X Y)
    (ρ : Density (A × B)) (hρ : IsSeparable ρ.matrix) {a gap : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hgap : 0 ≤ gap)
    (hnull : ∀ n h (σ : Density (A × B)), IsSeparable σ.matrix →
      (coarseApply (E.measurement n h) (E.acceptFine n h) σ.matrix).trace.re ≤ a)
    (n : ℕ) : bornTestProbability E ρ n (thresholdTest a gap n) ≤
      Real.exp (-(n : ℝ) * gap ^ 2 / 2) := by
  rw [bornTestProbability_eq_eventProbability]
  apply finite_history_azuma _ ha0 ha1 _ hgap n
  intro k h
  exact ⟨(conditionalBorn_mem_Icc E ρ k h).1,
    conditionalBorn_le_of_separable E ρ hρ ha0 hnull k h⟩

variable {C D : Type*} [Fintype C] [Fintype D] [DecidableEq C] [DecidableEq D]

def companionExperiment (E : AdaptiveOneWayExperiment A B X Y) :
    AdaptiveOneWayExperiment (A × C) (B × D) X Y where
  measurement n h := companionPOVM (E.measurement n h)
  acceptFine := E.acceptFine

theorem companion_born_threshold_test_le_exp_of_separable
    (E : AdaptiveOneWayExperiment A B X Y)
    (ρ : Density ((A × C) × (B × D))) (hρ : IsSeparable ρ.matrix) {a gap : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hgap : 0 ≤ gap)
    (hnull : ∀ n h (σ : Density (A × B)), IsSeparable σ.matrix →
      (coarseApply (E.measurement n h) (E.acceptFine n h) σ.matrix).trace.re ≤ a)
    (n : ℕ) :
    bornTestProbability (companionExperiment E) ρ n (thresholdTest a gap n) ≤
      Real.exp (-(n : ℝ) * gap ^ 2 / 2) := by
  apply born_threshold_test_le_exp_of_separable _ ρ hρ ha0 ha1 hgap
  intro k h σ hσ
  change (companionApply (E.measurement k h) (E.acceptFine k h) σ.matrix).trace.re ≤ a
  rw [companionApply_trace_eq_tested]
  exact hnull k h (testedDensity σ) (testedDensity_isSeparable σ hσ)

end MatrixHistories

end QuantumProver.DepolarizingSquashedEntanglement.BCYTesting

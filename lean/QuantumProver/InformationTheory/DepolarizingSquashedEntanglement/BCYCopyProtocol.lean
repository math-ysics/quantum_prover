import QuantumProver.InformationTheory.DepolarizingSquashedEntanglement.BCYCopyTesting
import QuantumProver.InformationTheory.DepolarizingSquashedEntanglement.BCYOneWaySeparation
import QuantumProver.InformationTheory.DepolarizingSquashedEntanglement.BCYAsymptoticComposition

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix
open scoped BigOperators ComplexOrder Kronecker Topology

namespace QuantumProver.DepolarizingSquashedEntanglement.BCYCopyProtocol

open BCYTesting BCYMeasurement BCYRelativeEntropy BCYCopyTesting BCYOneWaySeparation

variable {A B X Y : Type*} [Fintype A] [Fintype B] [Fintype X] [Fintype Y]
  [DecidableEq A] [DecidableEq B] [DecidableEq X] [DecidableEq Y]

private theorem sum_kronecker_product {S T U V : Type*} [Fintype U] [Fintype V]
    (f : U → QMatrix S) (g : V → QMatrix T) :
    (∑ u : U × V, f u.1 ⊗ₖ g u.2) = (∑ u, f u) ⊗ₖ (∑ v, g v) := by
  ext i j
  simp only [Matrix.sum_apply, Fintype.sum_prod_type, Matrix.kroneckerMap_apply,
    Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_comm

def copyPOVM (M : OneWayPOVM A B X Y) : (n : ℕ) →
    OneWayPOVM (CopyIndex A n) (CopyIndex B n) (CopyIndex X n) (CopyIndex Y n)
  | 0 => {
      alice := fun _ => 1
      alice_positive := fun _ => Matrix.PosSemidef.one
      alice_complete := by
        change (∑ _ : PUnit, (1 : QMatrix (CopyIndex A 0))) = 1
        simp
      bob := fun _ _ => 1
      bob_positive := fun _ _ => Matrix.PosSemidef.one
      bob_complete := fun _ => by
        change (∑ _ : PUnit, (1 : QMatrix (CopyIndex B 0))) = 1
        simp
    }
  | n + 1 => {
      alice := fun x => (copyPOVM M n).alice x.1 ⊗ₖ M.alice x.2
      alice_positive := fun x => ((copyPOVM M n).alice_positive x.1).kronecker (M.alice_positive x.2)
      alice_complete := by
        change (∑ x : CopyIndex X n × X, (copyPOVM M n).alice x.1 ⊗ₖ M.alice x.2) =
          (1 : QMatrix (CopyIndex A n × A))
        rw [sum_kronecker_product, (copyPOVM M n).alice_complete,
          M.alice_complete, Matrix.one_kronecker_one]
      bob := fun x y => (copyPOVM M n).bob x.1 y.1 ⊗ₖ M.bob x.2 y.2
      bob_positive := fun x y => ((copyPOVM M n).bob_positive x.1 y.1).kronecker (M.bob_positive x.2 y.2)
      bob_complete := fun x => by
        change (∑ y : CopyIndex Y n × Y, (copyPOVM M n).bob x.1 y.1 ⊗ₖ M.bob x.2 y.2) =
          (1 : QMatrix (CopyIndex B n × B))
        rw [sum_kronecker_product, (copyPOVM M n).bob_complete x.1,
          M.bob_complete x.2, Matrix.one_kronecker_one]
    }

def fineHistory (s : Finset (X × Y)) : (n : ℕ) → CopyIndex X n → CopyIndex Y n → History n
  | 0, _, _ => Fin.elim0
  | n + 1, x, y => Fin.cons (decide ((x.2, y.2) ∈ s)) (fineHistory s n x.1 y.1)

theorem copyPOVM_effect_succ (M : OneWayPOVM A B X Y) (n : ℕ)
    (x : CopyIndex X (n + 1)) (y : CopyIndex Y (n + 1)) :
    (copyPOVM M (n + 1)).alice x ⊗ₖ (copyPOVM M (n + 1)).bob x y =
      bipartiteTensorMatrix ((copyPOVM M n).alice x.1 ⊗ₖ (copyPOVM M n).bob x.1 y.1)
        (M.alice x.2 ⊗ₖ M.bob x.2 y.2) := by
  ext i j
  change (((copyPOVM M n).alice x.1 i.1.1 j.1.1 * M.alice x.2 i.1.2 j.1.2) *
    ((copyPOVM M n).bob x.1 y.1 i.2.1 j.2.1 * M.bob x.2 y.2 i.2.2 j.2.2)) =
    (((copyPOVM M n).alice x.1 i.1.1 j.1.1 * (copyPOVM M n).bob x.1 y.1 i.2.1 j.2.1) *
      (M.alice x.2 i.1.2 j.1.2 * M.bob x.2 y.2 i.2.2 j.2.2))
  ring

section BranchPairing

variable {C D : Type*} [Fintype C] [Fintype D] [DecidableEq C] [DecidableEq D]

theorem tensorMatrix_grouping (T : QMatrix (A × B)) (H : QMatrix (C × D)) :
    (bipartiteTensorMatrix T H).submatrix
      (companionGrouping (A := A) (B := B) (C := C) (D := D)) companionGrouping = T ⊗ₖ H := by
  ext u v
  rfl

theorem trace_grouping (R : QMatrix ((A × C) × (B × D))) :
    (R.submatrix (companionGrouping (A := A) (B := B) (C := C) (D := D))
      companionGrouping).trace = R.trace :=
  companionGrouping.sum_comp (fun i => R i i)

theorem remainder_trace_pairing (R : QMatrix ((A × C) × (B × D))) (H : QMatrix (C × D)) :
    (remainderMarginal R * H).trace =
      (R.submatrix (companionGrouping (A := A) (B := B) (C := C) (D := D))
        companionGrouping * ((1 : QMatrix (A × B)) ⊗ₖ H)).trace := by
  rw [remainderMarginal_eq_partialTrace]
  exact (QuantumProver.QuantumEntropy.partialTrace_left_mul_trace _ H).symm

private theorem fine_companion_trace_pairing (M : OneWayPOVM A B X Y)
    (z : X × Y) (R : QMatrix ((A × C) × (B × D))) (H : QMatrix (C × D)) :
    (((fineKraus (companionPOVM M) z * R * (fineKraus (companionPOVM M) z)ᴴ).submatrix
      (companionGrouping (A := A) (B := B) (C := C) (D := D)) companionGrouping) *
      ((1 : QMatrix (A × B)) ⊗ₖ H)).trace =
    (R.submatrix companionGrouping companionGrouping *
      ((M.alice z.1 ⊗ₖ M.bob z.1 z.2) ⊗ₖ H)).trace := by
  let g := companionGrouping (A := A) (B := B) (C := C) (D := D)
  let L := fineKraus M z ⊗ₖ (1 : QMatrix (C × D))
  rw [← Matrix.submatrix_mul_equiv (e₂ := g),
    ← Matrix.submatrix_mul_equiv (e₂ := g),
    ← Matrix.conjTranspose_submatrix, fineKraus_companion_grouping]
  have hcycle (S : QMatrix ((A × B) × (C × D))) :
      (L * S * Lᴴ * ((1 : QMatrix (A × B)) ⊗ₖ H)).trace =
      (S * (Lᴴ * ((1 : QMatrix (A × B)) ⊗ₖ H) * L)).trace := by
    simp only [Matrix.mul_assoc]
    rw [Matrix.trace_mul_comm L]
    simp only [Matrix.mul_assoc]
  rw [hcycle]
  dsimp only [L]
  rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
    ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    Matrix.mul_one, Matrix.one_mul, fineKraus_gram, Matrix.mul_one]

theorem companionApply_trace_pairing (M : OneWayPOVM A B X Y)
    (s : Finset (X × Y)) (R : QMatrix ((A × C) × (B × D))) (H : QMatrix (C × D)) :
    (remainderMarginal (companionApply M s R) * H).trace =
      (R * bipartiteTensorMatrix (acceptEffect M s) H).trace := by
  let g := companionGrouping (A := A) (B := B) (C := C) (D := D)
  rw [remainder_trace_pairing]
  have hright := trace_grouping (R * bipartiteTensorMatrix (acceptEffect M s) H)
  rw [← hright, ← Matrix.submatrix_mul_equiv (e₂ := g), tensorMatrix_grouping]
  have hsum : (companionApply M s R).submatrix g g =
      ∑ z ∈ s, (fineKraus (companionPOVM (C := C) (D := D) M) z * R *
        (fineKraus (companionPOVM (C := C) (D := D) M) z)ᴴ).submatrix g g := by
    ext u v
    simp only [companionApply, coarseApply, Matrix.submatrix_apply, Matrix.sum_apply]
  have htensor : acceptEffect M s ⊗ₖ H =
      ∑ z ∈ s, (M.alice z.1 ⊗ₖ M.bob z.1 z.2) ⊗ₖ H := by
    ext u v
    simp only [acceptEffect, Matrix.kroneckerMap_apply, Matrix.sum_apply, Finset.sum_mul]
  rw [hsum, Matrix.sum_mul, Matrix.trace_sum, htensor, Matrix.mul_sum, Matrix.trace_sum]
  apply Finset.sum_congr rfl
  intro z hz
  exact fine_companion_trace_pairing M z R H

end BranchPairing

def copyTensorMatrix (n : ℕ) (H : QMatrix (CopyIndex A n × CopyIndex B n))
    (T : QMatrix (A × B)) : QMatrix (CopyIndex A (n + 1) × CopyIndex B (n + 1)) :=
  bipartiteTensorMatrix H T

theorem lastCopyDensity_trace_pairing (n : ℕ)
    (ρ : Density (CopyIndex A (n + 1) × CopyIndex B (n + 1)))
    (H : QMatrix (CopyIndex A n × CopyIndex B n)) (T : QMatrix (A × B)) :
    ((lastCopyDensity n ρ).matrix * bipartiteTensorMatrix T H).trace =
      (ρ.matrix * copyTensorMatrix n H T).trace := by
  let e := Equiv.prodCongr (Equiv.prodComm (CopyIndex A n) A)
    (Equiv.prodComm (CopyIndex B n) B)
  have he : bipartiteTensorMatrix T H =
      Matrix.reindex e e (bipartiteTensorMatrix H T) := by
    ext u v
    change T (u.1.1,u.2.1) (v.1.1,v.2.1) * H (u.1.2,u.2.2) (v.1.2,v.2.2) =
      H (u.1.2,u.2.2) (v.1.2,v.2.2) * T (u.1.1,u.2.1) (v.1.1,v.2.1)
    exact mul_comm _ _
  change (Matrix.reindex e e ρ.matrix * bipartiteTensorMatrix T H).trace = _
  rw [he]
  change (ρ.matrix.submatrix e.symm e.symm *
    (bipartiteTensorMatrix H T).submatrix e.symm e.symm).trace = _
  exact (congrArg Matrix.trace (Matrix.submatrix_mul_equiv ρ.matrix
    (copyTensorMatrix n H T) e.symm e.symm e.symm)).trans
      (e.symm.sum_comp (fun i => (ρ.matrix * copyTensorMatrix n H T) i i))

def recordedEffect (M : OneWayPOVM A B X Y) (s : Finset (X × Y)) :
    (n : ℕ) → History n → QMatrix (CopyIndex A n × CopyIndex B n)
  | 0, _ => 1
  | n + 1, h => bipartiteTensorMatrix (recordedEffect M s n (Fin.tail h))
      (acceptEffect M (binaryOutcomeSet s (h 0)))

@[simp] theorem recordedEffect_cons (M : OneWayPOVM A B X Y)
    (s : Finset (X × Y)) (n : ℕ) (b : Bool) (h : History n) :
    recordedEffect M s (n + 1) (Fin.cons b h) =
      bipartiteTensorMatrix (recordedEffect M s n h) (acceptEffect M (binaryOutcomeSet s b)) := by
  simp only [recordedEffect, Fin.cons_zero, Fin.tail_cons]

theorem copyHistoryWeight_eq_recorded_trace (M : OneWayPOVM A B X Y)
    (s : Finset (X × Y)) (n : ℕ) (ρ : Density (CopyIndex A n × CopyIndex B n))
    (h : History n) : copyHistoryWeight M s n ρ h =
      (ρ.matrix * recordedEffect M s n h).trace.re := by
  induction n with
  | zero => simp only [copyHistoryWeight, recordedEffect, Matrix.mul_one, ρ.trace_one, Complex.one_re]
  | succ n ih =>
    let σ := lastCopyDensity n ρ
    let sb := binaryOutcomeSet s (h 0)
    let H := recordedEffect M s n (Fin.tail h)
    let p := (companionApply M sb σ.matrix).trace.re
    have hbridge : (remainderMarginal (companionApply M sb σ.matrix) * H).trace.re =
        (ρ.matrix * copyTensorMatrix n H (acceptEffect M sb)).trace.re := by
      rw [companionApply_trace_pairing]
      exact congrArg Complex.re (lastCopyDensity_trace_pairing n ρ H (acceptEffect M sb))
    rw [← Fin.cons_self_tail h, copyHistoryWeight_cons, recordedEffect_cons]
    by_cases hp : 0 < p
    · have hp' : 0 < (companionApply M (binaryOutcomeSet s (h 0))
        (lastCopyDensity n ρ).matrix).trace.re := hp
      rw [dite_eq_left hp', ih]
      calc
        _ = (remainderMarginal (companionApply M sb σ.matrix) * H).trace.re := by
          change p * (((remainderMarginal (companionApply M sb σ.matrix)).trace.re⁻¹ •
            remainderMarginal (companionApply M sb σ.matrix)) * H).trace.re = _
          rw [remainderMarginal_trace]
          change p * ((p⁻¹ • remainderMarginal (companionApply M sb σ.matrix)) * H).trace.re = _
          rw [Matrix.smul_mul, Matrix.trace_smul, Complex.smul_re, smul_eq_mul,
            ← mul_assoc, mul_inv_cancel₀ hp.ne', one_mul]
        _ = _ := hbridge
    · have hp' : ¬0 < (companionApply M (binaryOutcomeSet s (h 0))
        (lastCopyDensity n ρ).matrix).trace.re := hp
      have hp0 : p = 0 := le_antisymm (le_of_not_gt hp)
        (companionApply_probability_nonneg M sb σ.positive)
      have hr0 : companionApply M sb σ.matrix = 0 :=
        coarseApply_eq_zero_of_probability_zero (companionPOVM M) sb σ.positive hp0
      have hm0 : remainderMarginal
          (0 : QMatrix ((A × CopyIndex A n) × (B × CopyIndex B n))) =
          (0 : QMatrix (CopyIndex A n × CopyIndex B n)) := by
        ext i j
        simp only [remainderMarginal, Matrix.zero_apply, Finset.sum_const_zero]
      have hz : (remainderMarginal (companionApply M sb σ.matrix) * H).trace.re = 0 := by
        rw [hr0, hm0, Matrix.zero_mul, Matrix.trace_zero, Complex.zero_re]
      rw [dite_eq_right hp']
      exact hz.symm.trans hbridge

private theorem acceptEffect_eq_sum_ite (M : OneWayPOVM A B X Y) (s : Finset (X × Y)) :
    acceptEffect M s = ∑ x, ∑ y, if (x,y) ∈ s then M.alice x ⊗ₖ M.bob x y else 0 := by
  unfold acceptEffect
  simpa only [Fintype.sum_prod_type] using
    (Finset.sum_ite_mem_eq s (fun z : X × Y => M.alice z.1 ⊗ₖ M.bob z.1 z.2)).symm

private theorem acceptEffect_univ (M : OneWayPOVM A B X Y) :
    acceptEffect M Finset.univ = 1 := by
  simpa only [acceptEffect, Fintype.sum_prod_type] using c1_oneWay_effects_complete M

def historyFineSet (s : Finset (X × Y)) (n : ℕ) (h : History n) :
    Finset (CopyIndex X n × CopyIndex Y n) := by
  classical
  exact Finset.univ.filter (fun z => fineHistory s n z.1 z.2 = h)

theorem fineHistory_cons_eq (s : Finset (X × Y)) (n : ℕ)
    (x : CopyIndex X n) (y : CopyIndex Y n) (u : X) (v : Y) (b : Bool) (h : History n) :
    fineHistory s (n + 1) (x,u) (y,v) = Fin.cons b h ↔
      (u,v) ∈ binaryOutcomeSet s b ∧ fineHistory s n x y = h := by
  rw [fineHistory, Fin.cons_inj]
  cases b <;> simp [binaryOutcomeSet]

private theorem sum_ite_product_factor {U V S T : Type*}
    [Fintype U] [Fintype V] [Fintype S] [Fintype T]
    (P : U → V → Prop) (Q : S → T → Prop)
    [∀ u v, Decidable (P u v)] [∀ s t, Decidable (Q s t)]
    (f : U → V → ℂ) (g : S → T → ℂ) :
    (∑ u, ∑ s, ∑ v, ∑ t, if P u v ∧ Q s t then f u v * g s t else 0) =
      (∑ u, ∑ v, if P u v then f u v else 0) *
        (∑ s, ∑ t, if Q s t then g s t else 0) := by
  calc
    _ = ∑ u, ∑ v, ∑ s, ∑ t, if P u v ∧ Q s t then f u v * g s t else 0 := by
      apply Finset.sum_congr rfl
      intro u hu
      exact Finset.sum_comm
    _ = ∑ u, ∑ v, (if P u v then f u v else 0) *
        (∑ s, ∑ t, if Q s t then g s t else 0) := by
      apply Finset.sum_congr rfl
      intro u hu
      apply Finset.sum_congr rfl
      intro v hv
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s hs
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t ht
      by_cases hp : P u v <;> by_cases hq : Q s t <;> simp [hp,hq]
    _ = _ := by simp only [Finset.sum_mul]

@[simp] theorem mem_historyFineSet (s : Finset (X × Y)) (n : ℕ)
    (h : History n) (z : CopyIndex X n × CopyIndex Y n) :
    z ∈ historyFineSet s n h ↔ fineHistory s n z.1 z.2 = h := by
  classical
  simp only [historyFineSet, Finset.mem_filter, Finset.mem_univ, true_and]

theorem recordedEffect_eq_acceptEffect (M : OneWayPOVM A B X Y)
    (s : Finset (X × Y)) (n : ℕ) (h : History n) :
    recordedEffect M s n h = acceptEffect (copyPOVM M n) (historyFineSet s n h) := by
  classical
  induction n with
  | zero =>
    have hs : historyFineSet s 0 h = Finset.univ := by
      ext z
      simp only [mem_historyFineSet, Finset.mem_univ, iff_true]
      exact Subsingleton.elim _ _
    rw [hs, acceptEffect_univ]
    rfl
  | succ n ih =>
    rw [← Fin.cons_self_tail h, recordedEffect_cons, ih]
    ext i j
    let P (x : CopyIndex X n) (y : CopyIndex Y n) := fineHistory s n x y = Fin.tail h
    let Q (u : X) (v : Y) := (u,v) ∈ binaryOutcomeSet s (h 0)
    let f (x : CopyIndex X n) (y : CopyIndex Y n) :=
      ((copyPOVM M n).alice x ⊗ₖ (copyPOVM M n).bob x y)
        (i.1.1,i.2.1) (j.1.1,j.2.1)
    let g (u : X) (v : Y) := (M.alice u ⊗ₖ M.bob u v)
      (i.1.2,i.2.2) (j.1.2,j.2.2)
    have hr : acceptEffect (copyPOVM M (n + 1))
        (historyFineSet s (n + 1) (Fin.cons (h 0) (Fin.tail h))) i j =
        ∑ x : CopyIndex X n, ∑ u : X, ∑ y : CopyIndex Y n, ∑ v : Y,
          if P x y ∧ Q u v then f x y * g u v else 0 := by
      rw [acceptEffect_eq_sum_ite]
      simp only [Matrix.sum_apply, Matrix.ite_apply, Matrix.zero_apply]
      change (∑ x : CopyIndex X n × X, ∑ y : CopyIndex Y n × Y,
        if (x,y) ∈ historyFineSet s (n + 1) (Fin.cons (h 0) (Fin.tail h)) then
          ((copyPOVM M (n + 1)).alice x ⊗ₖ (copyPOVM M (n + 1)).bob x y) i j else 0) = _
      simp only [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro x hx
      apply Finset.sum_congr rfl
      intro u hu
      apply Finset.sum_congr rfl
      intro y hy
      apply Finset.sum_congr rfl
      intro v hv
      have hm : ((x,u),(y,v)) ∈ historyFineSet s (n + 1) (Fin.cons (h 0) (Fin.tail h)) ↔
          Q u v ∧ P x y :=
        (mem_historyFineSet s (n + 1) (Fin.cons (h 0) (Fin.tail h)) ((x,u),(y,v))).trans
          (fineHistory_cons_eq s n x y u v (h 0) (Fin.tail h))
      have he : ((copyPOVM M (n + 1)).alice (x,u) ⊗ₖ
          (copyPOVM M (n + 1)).bob (x,u) (y,v)) i j = f x y * g u v :=
        congrFun (congrFun (copyPOVM_effect_succ M n (x,u) (y,v)) i) j
      by_cases hp : P x y
      · by_cases hq : Q u v
        · have hmem := hm.mpr ⟨hq,hp⟩
          simpa only [hmem, hp, hq, and_self, ite_true] using he
        · have hmem : ¬((x,u),(y,v)) ∈ historyFineSet s (n + 1) (Fin.cons (h 0) (Fin.tail h)) :=
            fun hh => hq (hm.mp hh).1
          simp only [hmem, hp, hq, and_false, ite_false]
      · have hmem : ¬((x,u),(y,v)) ∈ historyFineSet s (n + 1) (Fin.cons (h 0) (Fin.tail h)) :=
          fun hh => hp (hm.mp hh).2
        simp only [hmem, hp, false_and, ite_false]
    rw [hr]
    change acceptEffect (copyPOVM M n) (historyFineSet s n (Fin.tail h))
        (i.1.1,i.2.1) (j.1.1,j.2.1) *
      acceptEffect M (binaryOutcomeSet s (h 0)) (i.1.2,i.2.2) (j.1.2,j.2.2) = _
    simpa only [acceptEffect_eq_sum_ite, Matrix.sum_apply, Matrix.ite_apply, Matrix.zero_apply,
      mem_historyFineSet, P, Q, f, g] using (sum_ite_product_factor P Q f g).symm

def testFineSet (s : Finset (X × Y)) (n : ℕ) (P : History n → Prop) :
    Finset (CopyIndex X n × CopyIndex Y n) := by
  classical
  exact Finset.univ.filter (fun z => P (fineHistory s n z.1 z.2))

private theorem sum_ite_fiberwise {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq J] (g : I → J) (w : I → ℝ) (P : J → Prop) [DecidablePred P] :
    (∑ h, if P h then ∑ i, if g i = h then w i else 0 else 0) =
      ∑ i, if P (g i) then w i else 0 := by
  calc
    _ = ∑ h, ∑ i, if P h ∧ g i = h then w i else 0 := by
      apply Finset.sum_congr rfl
      intro h hh
      by_cases hp : P h <;> simp [hp]
    _ = ∑ i, ∑ h, if P h ∧ g i = h then w i else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      have heq : (fun h => if P h ∧ g i = h then w i else 0) =
          (fun h => if h = g i then (if P h then w i else 0) else 0) := by
        funext h
        by_cases hh : g i = h
        · subst h
          simp
        · simp only [hh, Ne.symm hh, and_false, ite_false]
      rw [heq]
      simp

theorem coarse_copy_test_probability (M : OneWayPOVM A B X Y)
    (s : Finset (X × Y)) (n : ℕ) (ρ : Density (CopyIndex A n × CopyIndex B n))
    (P : History n → Prop) :
    (coarseApply (copyPOVM M n) (testFineSet s n P) ρ.matrix).trace.re =
      copyTestProbability M s n ρ P := by
  classical
  have hw (h : History n) : copyHistoryWeight M s n ρ h =
      ∑ z : CopyIndex X n × CopyIndex Y n,
        if fineHistory s n z.1 z.2 = h then oneWayOutcome (copyPOVM M n) ρ.matrix z.1 z.2 else 0 := by
    rw [copyHistoryWeight_eq_recorded_trace, recordedEffect_eq_acceptEffect]
    change acceptance ρ.matrix (acceptEffect (copyPOVM M n) (historyFineSet s n h)) = _
    rw [acceptance_eq_coarse_probability, coarseApply_probability, historyFineSet, Finset.sum_filter]
  rw [coarseApply_probability, testFineSet, Finset.sum_filter, copyTestProbability]
  simp_rw [hw]
  exact (sum_ite_fiberwise (fun z : CopyIndex X n × CopyIndex Y n => fineHistory s n z.1 z.2)
    (fun z => oneWayOutcome (copyPOVM M n) ρ.matrix z.1 z.2) P).symm

def matrixCopyTest (M : OneWayPOVM A B X Y) (s : Finset (X × Y))
    (n : ℕ) (P : History n → Prop) :
    BCYAsymptoticComposition.OneWayTest (CopyIndex A n) (CopyIndex B n) where
  firstCount := Fintype.card (CopyIndex X n)
  secondCount := Fintype.card (CopyIndex Y n)
  measurement := reindexPOVM (copyPOVM M n) (Fintype.equivFin _).symm (Fintype.equivFin _).symm
  accepted := (testFineSet s n P).map
    (((Fintype.equivFin (CopyIndex X n)).symm.prodCongr
      (Fintype.equivFin (CopyIndex Y n)).symm).symm.toEmbedding)

theorem matrixCopyTest_effect (M : OneWayPOVM A B X Y) (s : Finset (X × Y))
    (n : ℕ) (P : History n → Prop) :
    (matrixCopyTest M s n P).effectMatrix = acceptEffect (copyPOVM M n) (testFineSet s n P) := by
  rw [BCYAsymptoticComposition.OneWayTest.effectMatrix_eq_fine_sum]
  change acceptEffect (reindexPOVM (copyPOVM M n) (Fintype.equivFin _).symm
    (Fintype.equivFin _).symm) _ = _
  exact acceptEffect_reindex _ _ _ _

theorem matrixCopyTest_acceptance (M : OneWayPOVM A B X Y) (s : Finset (X × Y))
    (n : ℕ) (ρ : Density (CopyIndex A n × CopyIndex B n)) (P : History n → Prop) :
    BCYCompositeTesting.acceptance ρ (matrixCopyTest M s n P).toBinaryEffect =
      copyTestProbability M s n ρ P := by
  change acceptance ρ.matrix (matrixCopyTest M s n P).effectMatrix = _
  rw [matrixCopyTest_effect, acceptance_eq_coarse_probability]
  exact coarse_copy_test_probability M s n ρ P

open BCYAsymptoticComposition

theorem achievableOneWayRate_of_separator (M : OneWayPOVM A B X Y)
    (s : Finset (X × Y)) (ρ : Density (A × B)) {a δ : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hba : a < (coarseApply M s ρ.matrix).trace.re)
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hnull : ∀ σ : Density (A × B), IsSeparable σ.matrix →
      (coarseApply M s σ.matrix).trace.re ≤ a) :
    AchievableOneWayRate ρ
      ((((1 - δ) * ((coarseApply M s ρ.matrix).trace.re - a)) ^ 2 / 2 : ℝ) : EReal) := by
  let gap := (1 - δ) * ((coarseApply M s ρ.matrix).trace.re - a)
  let P : ∀ n, OneWayTest (CopyIndex A n) (CopyIndex B n) :=
    fun n => matrixCopyTest M s n (thresholdTest a gap n)
  apply achievableOneWayRate_of_uniform_separable_bound ρ (gap ^ 2 / 2) P
  · simpa only [P, matrixCopyTest_acceptance] using
      copy_iid_acceptance_tendsto_one M s ρ hba hδ0
  · intro n hn σ
    dsimp only [P]
    rw [matrixCopyTest_acceptance]
    exact (copy_threshold_test_le_exp_of_separable M s ha0 ha1
      (mul_nonneg (sub_nonneg.mpr hδ1) (sub_nonneg.mpr hba.le)) hnull n σ.val σ.property).trans_eq
        (by congr 1; ring)

theorem oneWayTestingRateNat_ge_of_lt_distance (ρ : Density (A × B)) {d : ℝ}
    (hd0 : 0 < d) (hd : d < separableOneWayDistance ρ) :
    ((d ^ 2 / 8 : ℝ) : EReal) ≤ oneWayTestingRateNat ρ := by
  obtain ⟨m,n,M,s,a,b,ha,hb,hnull,hgap,hba⟩ :=
    exists_oneWay_separator_of_lt_distance ρ hd0 hd
  have hδbound : ∀ δ ∈ Set.Ioo (0 : ℝ) 1,
      (((1 - δ) ^ 2 * d ^ 2 / 8 : ℝ) : EReal) ≤ oneWayTestingRateNat ρ := by
    intro δ hδ
    have hr := achievableOneWayRate_of_separator M s ρ ha.1 ha.2
      (by simpa only [← hb] using hba) hδ.1 hδ.2.le hnull
    have hm : (1 - δ) * d / 2 ≤ (1 - δ) * (b - a) := by
      have hh := mul_le_mul_of_nonneg_left hgap (sub_nonneg.mpr hδ.2.le)
      convert hh using 1 <;> ring
    have hu0 : 0 ≤ (1 - δ) * d / 2 :=
      div_nonneg (mul_nonneg (sub_nonneg.mpr hδ.2.le) hd0.le) (by norm_num)
    have hs := mul_self_le_mul_self hu0 hm
    have hreal : (1 - δ) ^ 2 * d ^ 2 / 8 ≤ ((1 - δ) * (b - a)) ^ 2 / 2 := by
      nlinarith [hs]
    have hrRate : ((((1 - δ) * ((coarseApply M s ρ.matrix).trace.re - a)) ^ 2 / 2 : ℝ) : EReal) ≤
        oneWayTestingRateNat ρ := by
      exact le_sSup hr
    have hr' : ((((1 - δ) * (b - a)) ^ 2 / 2 : ℝ) : EReal) ≤ oneWayTestingRateNat ρ := by
      simpa only [← hb] using hrRate
    exact (EReal.coe_le_coe_iff.mpr hreal).trans hr'
  have hcont : ContinuousAt (fun δ : ℝ => (1 - δ) ^ 2 * d ^ 2 / 8) 0 := by fun_prop
  have hlim : Filter.Tendsto (fun δ : ℝ => (((1 - δ) ^ 2 * d ^ 2 / 8 : ℝ) : EReal))
      (𝓝[>] 0) (𝓝 ((d ^ 2 / 8 : ℝ) : EReal)) := by
    apply EReal.tendsto_coe.mpr
    simpa using hcont.continuousWithinAt.tendsto
  apply le_of_tendsto hlim
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with δ hδ
  exact hδbound δ hδ

end QuantumProver.DepolarizingSquashedEntanglement.BCYCopyProtocol

import QuantumProver.InformationTheory.AmplitudeDamping.SecretKey.LaneHistoryTransport
import QuantumProver.InformationTheory.AmplitudeDamping.QuantumCapacity.ParallelLanes

set_option autoImplicit false

noncomputable section

open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix Kronecker

namespace QuantumProver.AmplitudeDamping.SecretKey.BlockLossHistory

open PhysicalProtocol PhysicalProtocol.FiniteKeyProtocol IndependentLanes
open QuantumProver.AmplitudeDamping.FiniteModel

def keyRelabel_B {i o : ℕ} (e : Fin o ≃ Fin i) :
    KrausChannel (Fin i) (Fin o) (Fin 1) where
  op := (relabelInstrumentB e).operator
  complete := (relabelInstrumentB e).complete

def sequentialThenKey_B (p : ℝ) : (n a b af bf : ℕ) →
    FiniteKeyProtocol p a (doubleDimB n b) af bf →
      FiniteKeyProtocol p (doubleDimB n a) b af bf
  | 0, _, _, _, _, Q => Q
  | n + 1, a, b, af, bf, Q =>
      .alice (keyRelabel_B (finCongr (doubleDimB_double n a)).symm) fun _ =>
        .call (sequentialThenKey_B p n a (2 * b) af bf Q)

theorem sequentialThenKey_toQuantum_B (p : ℝ) (n a b af bf : ℕ)
    (Q : FiniteKeyProtocol p a (doubleDimB n b) af bf) :
    toQuantum_B (sequentialThenKey_B p n a b af bf Q) =
      sequentialCallsThenB p n a b (toQuantum_B Q) := by
  induction n generalizing b with
  | zero => rfl
  | succ n ih =>
      simp only [sequentialThenKey_B, toQuantum_B, sequentialCallsThenB]
      congr 1
      funext z
      congr 1
      exact ih (2 * b) Q

theorem sequentialThenKey_calls_B (p : ℝ) (n a b af bf : ℕ)
    (Q : FiniteKeyProtocol p a (doubleDimB n b) af bf) :
    (sequentialThenKey_B p n a b af bf Q).calls = Q.calls + n := by
  rw [← toQuantum_calls_B, sequentialThenKey_toQuantum_B,
    sequentialCallsThenB_calls, toQuantum_calls_B]

def sequentialEnvironmentEquiv_B (p : ℝ) : (n a b af bf : ℕ) →
    (Q : FiniteKeyProtocol p a (doubleDimB n b) af bf) →
      (sequentialThenKey_B p n a b af bf Q).Environment ≃
        ((Fin n → Fin 2) × Q.Environment)
  | 0, _, _, _, _, Q =>
      { toFun := fun h => (Fin.elim0,h)
        invFun := fun h => h.2
        left_inv := fun _ => rfl
        right_inv := by
          intro h
          apply Prod.ext
          · funext z
            exact Fin.elim0 z
          · rfl }
  | n + 1, a, b, af, bf, Q =>
      let e := sequentialEnvironmentEquiv_B p n a (2 * b) af bf Q
      { toFun := fun h => (Fin.cons h.2.1 (e h.2.2).1, (e h.2.2).2)
        invFun := fun h => ⟨0, (h.1 0, e.symm (Fin.tail h.1,h.2))⟩
        left_inv := by
          intro h
          rcases h with ⟨z,l,t⟩
          have hz : z = 0 := Subsingleton.elim _ _
          subst z
          simp only [Fin.cons_zero, Fin.tail_cons, e.symm_apply_apply]
          rfl
        right_inv := by
          intro h
          simp only [e.apply_symm_apply, Fin.cons_self_tail] }

theorem sequentialThenKey_historyKraus_B (p : ℝ) (n a b af bf : ℕ)
    (Q : FiniteKeyProtocol p a (doubleDimB n b) af bf) :
    ∀ h, (sequentialThenKey_B p n a b af bf Q).historyKraus_B h =
      Q.historyKraus_B ((sequentialEnvironmentEquiv_B p n a b af bf Q h).2) *
        sequentialCallsKrausB p n a b
          ((sequentialEnvironmentEquiv_B p n a b af bf Q h).1) := by
  induction n generalizing b with
  | zero =>
      change FiniteKeyProtocol p a b af bf at Q
      intro h
      change Q.Environment at h
      change Q.historyKraus_B h = Q.historyKraus_B h *
        (1 : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ)
      rw [Matrix.mul_one]
  | succ n ih =>
      change FiniteKeyProtocol p a (doubleDimB n (2 * b)) af bf at Q
      intro h
      rcases h with ⟨z,l,t⟩
      have hz : z = 0 := Subsingleton.elim _ _
      subst z
      have he : (sequentialEnvironmentEquiv_B p (n + 1) a b af bf Q) ⟨0,(l,t)⟩ =
          (Fin.cons l ((sequentialEnvironmentEquiv_B p n a (2 * b) af bf Q) t).1,
            ((sequentialEnvironmentEquiv_B p n a (2 * b) af bf Q) t).2) := rfl
      change ((sequentialThenKey_B p n a (2 * b) af bf Q).historyKraus_B t *
        transferKraus p (doubleDimB n a) b l) *
          ((relabelInstrumentB (finCongr (doubleDimB_double n a)).symm).operator 0 ⊗ₖ
            (1 : Matrix (Fin b) (Fin b) ℂ)) = _
      rw [he, ih (2 * b) Q t]
      simp only [sequentialCallsKrausB, Fin.cons_zero, Fin.tail_cons,
        quantum_callOperator_eq_key_B, aliceOperator, Matrix.mul_assoc]
      rfl

theorem sequentialThenKey_publicHistory_eq_B (p : ℝ) (n a b af bf : ℕ)
    (Q : FiniteKeyProtocol p a (doubleDimB n b) af bf) :
    ∀ h h', (sequentialThenKey_B p n a b af bf Q).publicTranscript_B h =
        (sequentialThenKey_B p n a b af bf Q).publicTranscript_B h' ↔
      Q.publicTranscript_B ((sequentialEnvironmentEquiv_B p n a b af bf Q h).2) =
        Q.publicTranscript_B ((sequentialEnvironmentEquiv_B p n a b af bf Q h').2) := by
  induction n generalizing b with
  | zero => intro h h'; rfl
  | succ n ih =>
      change FiniteKeyProtocol p a (doubleDimB n (2 * b)) af bf at Q
      intro h h'
      rcases h with ⟨z,l,t⟩
      rcases h' with ⟨z',l',t'⟩
      have hz : z = 0 := Subsingleton.elim _ _
      have hz' : z' = 0 := Subsingleton.elim _ _
      subst z
      subst z'
      change (@Sigma.mk (Fin 1)
        (fun _ => (sequentialThenKey_B p n a (2 * b) af bf Q).comparisonPublicHistory_B)
        0 ((sequentialThenKey_B p n a (2 * b) af bf Q).publicTranscript_B t) =
        @Sigma.mk (Fin 1)
          (fun _ => (sequentialThenKey_B p n a (2 * b) af bf Q).comparisonPublicHistory_B)
          0 ((sequentialThenKey_B p n a (2 * b) af bf Q).publicTranscript_B t')) ↔ _
      constructor
      · intro h
        exact (ih (2 * b) Q t t').mp (eq_of_heq (Sigma.mk.inj_iff.mp h).2)
      · intro h
        exact congrArg (fun v => @Sigma.mk (Fin 1)
          (fun _ => (sequentialThenKey_B p n a (2 * b) af bf Q).comparisonPublicHistory_B)
          0 v) ((ih (2 * b) Q t t').mpr h)

theorem sequentialThenKey_fullOutput_B (p : ℝ) (n a b af bf : ℕ)
    (Q : FiniteKeyProtocol p a (doubleDimB n b) af bf)
    (ρ : PhysicalProtocol.BipartiteMatrix (doubleDimB n a) b)
    (x y : Fin af × Fin bf)
    (h h' : (sequentialThenKey_B p n a b af bf Q).Environment) :
    (sequentialThenKey_B p n a b af bf Q).fullOutput ρ (x,h) (y,h') =
      if Q.publicTranscript_B ((sequentialEnvironmentEquiv_B p n a b af bf Q h).2) =
        Q.publicTranscript_B ((sequentialEnvironmentEquiv_B p n a b af bf Q h').2) then
        ((Q.historyKraus_B ((sequentialEnvironmentEquiv_B p n a b af bf Q h).2) *
            sequentialCallsKrausB p n a b
              ((sequentialEnvironmentEquiv_B p n a b af bf Q h).1)) * ρ *
          (Q.historyKraus_B ((sequentialEnvironmentEquiv_B p n a b af bf Q h').2) *
            sequentialCallsKrausB p n a b
              ((sequentialEnvironmentEquiv_B p n a b af bf Q h').1))ᴴ) x y
      else 0 := by
  rw [fullOutput_historyKraus_apply_B]
  simp only [sequentialThenKey_publicHistory_eq_B, sequentialThenKey_historyKraus_B]

def oneFlagEquiv_B (T : Type*) : ((z : Fin 1) × T) ≃ T where
  toFun h := h.2
  invFun h := ⟨0,h⟩
  left_inv h := by
    rcases h with ⟨z,h⟩
    have hz : z = 0 := Subsingleton.elim _ _
    subst z
    rfl
  right_inv _ := rfl

theorem sigmaZero_eq_iff_B {T : Type*} (x y : T) :
    (@Sigma.mk (Fin 1) (fun _ => T) 0 x = @Sigma.mk (Fin 1) (fun _ => T) 0 y) ↔
      x = y := by
  constructor
  · intro h
    exact eq_of_heq (Sigma.mk.inj_iff.mp h).2
  · intro h
    exact congrArg (fun t => @Sigma.mk (Fin 1) (fun _ => T) 0 t) h

theorem aliceChart_public_eq_B {p : ℝ} {a b ao af bf : ℕ}
    (C : KrausChannel (Fin a) (Fin ao) (Fin 1))
    (Q : FiniteKeyProtocol p ao b af bf)
    (h h' : (FiniteKeyProtocol.alice C (fun _ => Q)).Environment) :
    (FiniteKeyProtocol.alice C (fun _ => Q)).publicTranscript_B h =
        (FiniteKeyProtocol.alice C (fun _ => Q)).publicTranscript_B h' ↔
      Q.publicTranscript_B h.2 = Q.publicTranscript_B h'.2 := by
  rcases h with ⟨z,t⟩
  rcases h' with ⟨z',t'⟩
  have hz : z = 0 := Subsingleton.elim _ _
  have hz' : z' = 0 := Subsingleton.elim _ _
  subst z
  subst z'
  exact sigmaZero_eq_iff_B _ _

theorem bobChart_public_eq_B {p : ℝ} {a b bo af bf : ℕ}
    (C : KrausChannel (Fin b) (Fin bo) (Fin 1))
    (Q : FiniteKeyProtocol p a bo af bf)
    (h h' : (FiniteKeyProtocol.bob C (fun _ => Q)).Environment) :
    (FiniteKeyProtocol.bob C (fun _ => Q)).publicTranscript_B h =
        (FiniteKeyProtocol.bob C (fun _ => Q)).publicTranscript_B h' ↔
      Q.publicTranscript_B h.2 = Q.publicTranscript_B h'.2 := by
  rcases h with ⟨z,t⟩
  rcases h' with ⟨z',t'⟩
  have hz : z = 0 := Subsingleton.elim _ _
  have hz' : z' = 0 := Subsingleton.elim _ _
  subst z
  subst z'
  exact sigmaZero_eq_iff_B _ _

def groupedBobRestore_B (p : ℝ) (n a b c d af bf : ℕ)
    (Q : FiniteKeyProtocol p (a * c) (doubleDimB n b * (2 * d)) af bf) :
    FiniteKeyProtocol p (a * c) (doubleDimB (n + 1) (b * d)) af bf :=
  .bob (keyRelabel_B (mergeOutputEquivB n b d).symm) fun _ => Q

def groupedThenKey_B (p : ℝ) (n a b c d af bf : ℕ)
    (Q : FiniteKeyProtocol p (a * c) (doubleDimB n b * (2 * d)) af bf) :
    FiniteKeyProtocol p (doubleDimB n a * (2 * c)) (b * d) af bf :=
  .alice (keyRelabel_B (mergeInputEquivB n a c)) fun _ =>
    sequentialThenKey_B p (n + 1) (a * c) (b * d) af bf
      (groupedBobRestore_B p n a b c d af bf Q)

def groupedEnvironmentEquiv_B (p : ℝ) (n a b c d af bf : ℕ)
    (Q : FiniteKeyProtocol p (a * c) (doubleDimB n b * (2 * d)) af bf) :
    (groupedThenKey_B p n a b c d af bf Q).Environment ≃
      ((Fin (n + 1) → Fin 2) × Q.Environment) :=
  (oneFlagEquiv_B _).trans
    ((sequentialEnvironmentEquiv_B p (n + 1) (a * c) (b * d) af bf
      (groupedBobRestore_B p n a b c d af bf Q)).trans
        ((Equiv.refl (Fin (n + 1) → Fin 2)).prodCongr (oneFlagEquiv_B Q.Environment)))

theorem groupedThenKey_calls_B (p : ℝ) (n a b c d af bf : ℕ)
    (Q : FiniteKeyProtocol p (a * c) (doubleDimB n b * (2 * d)) af bf) :
    (groupedThenKey_B p n a b c d af bf Q).calls = Q.calls + (n + 1) := by
  simp only [groupedThenKey_B, FiniteKeyProtocol.calls,
    Finset.univ_unique, Finset.sup_singleton, sequentialThenKey_calls_B,
    groupedBobRestore_B]

theorem groupedThenKey_historyKraus_B (p : ℝ) (n a b c d af bf : ℕ)
    (Q : FiniteKeyProtocol p (a * c) (doubleDimB n b * (2 * d)) af bf)
    (h : (groupedThenKey_B p n a b c d af bf Q).Environment) :
    (groupedThenKey_B p n a b c d af bf Q).historyKraus_B h =
      Q.historyKraus_B ((groupedEnvironmentEquiv_B p n a b c d af bf Q h).2) *
        mergeCallKrausB p n a b c d
          ((groupedEnvironmentEquiv_B p n a b c d af bf Q h).1) := by
  rcases h with ⟨z,t⟩
  have hz : z = 0 := Subsingleton.elim _ _
  subst z
  let R := groupedBobRestore_B p n a b c d af bf Q
  let e := sequentialEnvironmentEquiv_B p (n + 1) (a * c) (b * d) af bf R
  change (sequentialThenKey_B p (n + 1) (a * c) (b * d) af bf R).historyKraus_B t *
    ((relabelInstrumentB (mergeInputEquivB n a c)).operator 0 ⊗ₖ
      (1 : Matrix (Fin (b * d)) (Fin (b * d)) ℂ)) = _
  rw [sequentialThenKey_historyKraus_B]
  change ((Q.historyKraus_B (e t).2.2 *
    ((1 : Matrix (Fin (a * c)) (Fin (a * c)) ℂ) ⊗ₖ
      (relabelInstrumentB (mergeOutputEquivB n b d).symm).operator (e t).2.1)) *
    sequentialCallsKrausB p (n + 1) (a * c) (b * d) (e t).1) *
      ((relabelInstrumentB (mergeInputEquivB n a c)).operator 0 ⊗ₖ
        (1 : Matrix (Fin (b * d)) (Fin (b * d)) ℂ)) = _
  have hzB : (e t).2.1 = 0 := Subsingleton.elim _ _
  rw [hzB]
  have he : groupedEnvironmentEquiv_B p n a b c d af bf Q ⟨0,t⟩ =
      ((e t).1,(e t).2.2) := rfl
  rw [he]
  simp only [mergeCallKrausB, aliceOperator, bobOperator, Matrix.mul_assoc]

theorem groupedThenKey_publicHistory_eq_B (p : ℝ) (n a b c d af bf : ℕ)
    (Q : FiniteKeyProtocol p (a * c) (doubleDimB n b * (2 * d)) af bf)
    (h h' : (groupedThenKey_B p n a b c d af bf Q).Environment) :
    (groupedThenKey_B p n a b c d af bf Q).publicTranscript_B h =
        (groupedThenKey_B p n a b c d af bf Q).publicTranscript_B h' ↔
      Q.publicTranscript_B ((groupedEnvironmentEquiv_B p n a b c d af bf Q h).2) =
        Q.publicTranscript_B ((groupedEnvironmentEquiv_B p n a b c d af bf Q h').2) := by
  let R := groupedBobRestore_B p n a b c d af bf Q
  let T := sequentialThenKey_B p (n + 1) (a * c) (b * d) af bf R
  let e := sequentialEnvironmentEquiv_B p (n + 1) (a * c) (b * d) af bf R
  exact (aliceChart_public_eq_B (keyRelabel_B (mergeInputEquivB n a c)) T h h').trans
    ((sequentialThenKey_publicHistory_eq_B p (n + 1) (a * c) (b * d) af bf R
      h.2 h'.2).trans
        (bobChart_public_eq_B (keyRelabel_B (mergeOutputEquivB n b d).symm) Q
          (e h.2).2 (e h'.2).2))

theorem groupedThenKey_fullOutput_B (p : ℝ) (n a b c d af bf : ℕ)
    (Q : FiniteKeyProtocol p (a * c) (doubleDimB n b * (2 * d)) af bf)
    (ρ : PhysicalProtocol.BipartiteMatrix (doubleDimB n a * (2 * c)) (b * d))
    (x y : Fin af × Fin bf)
    (h h' : (groupedThenKey_B p n a b c d af bf Q).Environment) :
    (groupedThenKey_B p n a b c d af bf Q).fullOutput ρ (x,h) (y,h') =
      if Q.publicTranscript_B ((groupedEnvironmentEquiv_B p n a b c d af bf Q h).2) =
        Q.publicTranscript_B ((groupedEnvironmentEquiv_B p n a b c d af bf Q h').2) then
        ((Q.historyKraus_B ((groupedEnvironmentEquiv_B p n a b c d af bf Q h).2) *
          pairOperatorB
            (sequentialCallsKrausB p n a b
              (Fin.tail ((groupedEnvironmentEquiv_B p n a b c d af bf Q h).1)))
            (callOperator p c d ((groupedEnvironmentEquiv_B p n a b c d af bf Q h).1 0))) *
          ρ * (Q.historyKraus_B ((groupedEnvironmentEquiv_B p n a b c d af bf Q h').2) *
            pairOperatorB
              (sequentialCallsKrausB p n a b
                (Fin.tail ((groupedEnvironmentEquiv_B p n a b c d af bf Q h').1)))
              (callOperator p c d ((groupedEnvironmentEquiv_B p n a b c d af bf Q h').1 0)))ᴴ) x y
      else 0 := by
  rw [fullOutput_historyKraus_apply_B]
  simp only [groupedThenKey_publicHistory_eq_B, groupedThenKey_historyKraus_B,
    mergeCallKrausB_eq_pair]

theorem groupedThenKey_priorEve_apply_B {E : Type*}
    (p : ℝ) (n a b c d af bf : ℕ)
    (Q : FiniteKeyProtocol p (a * c) (doubleDimB n b * (2 * d)) af bf)
    (ρ : Matrix (((Fin (doubleDimB n a * (2 * c))) × Fin (b * d)) × E)
      (((Fin (doubleDimB n a * (2 * c))) × Fin (b * d)) × E) ℂ)
    (x y : Fin af × Fin bf)
    (h h' : (groupedThenKey_B p n a b c d af bf Q).Environment) (e e' : E) :
    PublicHistory.localPriorEveMatrix_B (groupedThenKey_B p n a b c d af bf Q) ρ
      (x,(h,e)) (y,(h',e')) =
      Q.fullOutput
        (mergeCallKrausB p n a b c d
          ((groupedEnvironmentEquiv_B p n a b c d af bf Q h).1) *
          Matrix.of (fun i j => ρ (i,e) (j,e')) *
          (mergeCallKrausB p n a b c d
            ((groupedEnvironmentEquiv_B p n a b c d af bf Q h').1))ᴴ)
        (x, (groupedEnvironmentEquiv_B p n a b c d af bf Q h).2)
        (y, (groupedEnvironmentEquiv_B p n a b c d af bf Q h').2) := by
  unfold PublicHistory.localPriorEveMatrix_B
  rw [fullOutput_historyKraus_apply_B, Q.fullOutput_historyKraus_apply_B]
  simp only [groupedThenKey_publicHistory_eq_B, groupedThenKey_historyKraus_B,
    Matrix.conjTranspose_mul, Matrix.mul_assoc]

theorem groupedThenKey_toQuantum_B (p : ℝ) (n a b c d af bf : ℕ)
    (Q : FiniteKeyProtocol p (a * c) (doubleDimB n b * (2 * d)) af bf) :
    toQuantum_B (groupedThenKey_B p n a b c d af bf Q) =
      .alice (relabelInstrumentB (mergeInputEquivB n a c)) (fun _ =>
        sequentialCallsThenB p (n + 1) (a * c) (b * d)
          (.bob (relabelInstrumentB (mergeOutputEquivB n b d).symm) (fun _ => toQuantum_B Q))) := by
  simp only [groupedThenKey_B, toQuantum_B, sequentialThenKey_toQuantum_B,
    groupedBobRestore_B, keyRelabel_B]

theorem toQuantum_fromQuantum_B {p : ℝ} {a b af bf : ℕ}
    (P : QuantumProver.AmplitudeDamping.FiniteModel.FiniteProtocol p a b af bf) :
    toQuantum_B (fromQuantum_B P) = P := by
  induction P with
  | done a b => rfl
  | alice C next ih =>
      change QuantumProver.AmplitudeDamping.FiniteModel.FiniteProtocol.alice C
        (fun z => toQuantum_B (fromQuantum_B (next z))) =
          QuantumProver.AmplitudeDamping.FiniteModel.FiniteProtocol.alice C next
      congr 1
      funext z
      exact ih z
  | bob C next ih =>
      change QuantumProver.AmplitudeDamping.FiniteModel.FiniteProtocol.bob C
        (fun z => toQuantum_B (fromQuantum_B (next z))) =
          QuantumProver.AmplitudeDamping.FiniteModel.FiniteProtocol.bob C next
      congr 1
      funext z
      exact ih z
  | call next ih =>
      change QuantumProver.AmplitudeDamping.FiniteModel.FiniteProtocol.call
        (toQuantum_B (fromQuantum_B next)) = _
      rw [ih]

theorem groupedThenKey_eq_actualBlockExpansion_B (p : ℝ) (n a b c d af bf : ℕ)
    (Q : FiniteBlockProtocolB p (n + 1) (a * c) (doubleDimB n b * (2 * d)) af bf) :
    groupedThenKey_B p n a b c d af bf (fromQuantum_B Q.represented_toMatrix) =
      fromQuantum_B (mergeBlockCallThenB p n a b c d Q).represented_toMatrix := by
  have ht : toQuantum_B (groupedThenKey_B p n a b c d af bf (fromQuantum_B Q.represented_toMatrix)) =
      toQuantum_B (fromQuantum_B (mergeBlockCallThenB p n a b c d Q).represented_toMatrix) := by
    rw [groupedThenKey_toQuantum_B, toQuantum_fromQuantum_B, toQuantum_fromQuantum_B]
    rfl
  have h := congrArg (fun T => fromQuantum_B T) ht
  simpa only [fromQuantum_toQuantum_B] using h

end QuantumProver.AmplitudeDamping.SecretKey.BlockLossHistory

import QuantumProver.InformationTheory.AmplitudeDamping.QuantumCapacity.ParallelSchedulerHistory
import QuantumProver.InformationTheory.AmplitudeDamping.SecretKey.BlockLossHistory

set_option autoImplicit false

noncomputable section

open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix Kronecker

namespace QuantumProver.AmplitudeDamping.SecretKey.LaneMergeHistory

open PhysicalProtocol PhysicalProtocol.FiniteKeyProtocol IndependentLanes BlockLossHistory
open QuantumProver.AmplitudeDamping.FiniteModel

theorem fromQuantum_sequential_B (p : ℝ) (n a b af bf : ℕ)
    (Q : FiniteProtocol p a (doubleDimB n b) af bf) :
    fromQuantum_B (sequentialCallsThenB p n a b Q) =
      sequentialThenKey_B p n a b af bf (fromQuantum_B Q) := by
  have h := congrArg (fun T => fromQuantum_B T)
    (sequentialThenKey_toQuantum_B p n a b af bf (fromQuantum_B Q))
  simpa only [fromQuantum_toQuantum_B, toQuantum_fromQuantum_B] using h.symm

def blockOneEnvironmentEquiv_B {p : ℝ} {a b af bf : ℕ}
    (P : FiniteProtocol p a b af bf) :
    (fromQuantum_B P.toBlockOneB.represented_toMatrix).Environment ≃
      (fromQuantum_B P).Environment :=
  match P with
  | .done _ _ => Equiv.refl _
  | .alice _ next => Equiv.sigmaCongrRight fun z => blockOneEnvironmentEquiv_B (next z)
  | .bob _ next => Equiv.sigmaCongrRight fun z => blockOneEnvironmentEquiv_B (next z)
  | @FiniteProtocol.call _ a₀ b₀ af₀ bf₀ next =>
      (sequentialEnvironmentEquiv_B p 1 a₀ b₀ af₀ bf₀
        (fromQuantum_B next.toBlockOneB.represented_toMatrix)).trans
          (scalarWordEquivB.symm.prodCongr (blockOneEnvironmentEquiv_B next))

def blockOnePublicEquiv_B {p : ℝ} {a b af bf : ℕ}
    (P : FiniteProtocol p a b af bf) :
    (fromQuantum_B P.toBlockOneB.represented_toMatrix).comparisonPublicHistory_B ≃
      (fromQuantum_B P).comparisonPublicHistory_B :=
  match P with
  | .done _ _ => Equiv.refl _
  | .alice _ next => Equiv.sigmaCongrRight fun z => blockOnePublicEquiv_B (next z)
  | .bob _ next => Equiv.sigmaCongrRight fun z => blockOnePublicEquiv_B (next z)
  | .call next =>
      (oneFlagEquiv_B _).trans (blockOnePublicEquiv_B next)

theorem blockOne_historyKraus_B {p : ℝ} {a b af bf : ℕ}
    (P : FiniteProtocol p a b af bf) :
    ∀ h, (fromQuantum_B P.toBlockOneB.represented_toMatrix).historyKraus_B h =
      (fromQuantum_B P).historyKraus_B (blockOneEnvironmentEquiv_B P h) := by
  induction P with
  | done a b => intro h; rfl
  | alice C next ih =>
      intro h
      change (fromQuantum_B (next h.1).toBlockOneB.represented_toMatrix).historyKraus_B h.2 *
          (C.operator h.1 ⊗ₖ (1 : Matrix (Fin _) (Fin _) ℂ)) =
        (fromQuantum_B (next h.1)).historyKraus_B
          (blockOneEnvironmentEquiv_B (next h.1) h.2) *
            (C.operator h.1 ⊗ₖ (1 : Matrix (Fin _) (Fin _) ℂ))
      rw [ih h.1 h.2]
  | bob C next ih =>
      intro h
      change (fromQuantum_B (next h.1).toBlockOneB.represented_toMatrix).historyKraus_B h.2 *
          ((1 : Matrix (Fin _) (Fin _) ℂ) ⊗ₖ C.operator h.1) =
        (fromQuantum_B (next h.1)).historyKraus_B
          (blockOneEnvironmentEquiv_B (next h.1) h.2) *
            ((1 : Matrix (Fin _) (Fin _) ℂ) ⊗ₖ C.operator h.1)
      rw [ih h.1 h.2]
  | @call a₀ b₀ af₀ bf₀ next ih =>
      intro h
      rcases h with ⟨z,l,t⟩
      have hz : z = 0 := Subsingleton.elim _ _
      subst z
      let C : KrausInstrument (2 * a₀) (2 * a₀) 1 :=
        relabelInstrumentB (finCongr (doubleDimB_double 0 a₀)).symm
      change ((fromQuantum_B next.toBlockOneB.represented_toMatrix).historyKraus_B t *
          transferKraus p a₀ b₀ l) *
          (C.operator 0 ⊗ₖ (1 : Matrix (Fin b₀) (Fin b₀) ℂ)) =
        (fromQuantum_B next).historyKraus_B (blockOneEnvironmentEquiv_B next t) *
          transferKraus p a₀ b₀ l
      rw [ih t]
      have hi : C.operator 0 =
          (1 : Matrix (Fin (2 * a₀)) (Fin (2 * a₀)) ℂ) := by
        ext x y
        have he : (finCongr (doubleDimB_double 0 a₀)).symm x = x := by
          apply Fin.ext
          rfl
        simp only [C,relabelInstrumentB,krausInstrumentOfEquivsB,Matrix.submatrix_apply,
          Equiv.refl_apply,Equiv.refl_symm]
        exact congrArg (fun u => (1 : Matrix (Fin (2 * a₀)) (Fin (2 * a₀)) ℂ) u y) he
      rw [hi,Matrix.one_kronecker_one,Matrix.mul_one]

theorem blockOne_publicTranscript_B {p : ℝ} {a b af bf : ℕ}
    (P : FiniteProtocol p a b af bf) :
    ∀ h, blockOnePublicEquiv_B P
        ((fromQuantum_B P.toBlockOneB.represented_toMatrix).publicTranscript_B h) =
      (fromQuantum_B P).publicTranscript_B (blockOneEnvironmentEquiv_B P h) := by
  induction P with
  | done a b => intro h; rfl
  | alice C next ih =>
      intro h
      change @Sigma.mk _ (fun z => (fromQuantum_B (next z)).comparisonPublicHistory_B) h.1
          (blockOnePublicEquiv_B (next h.1)
            ((fromQuantum_B (next h.1).toBlockOneB.represented_toMatrix).publicTranscript_B h.2)) =
        @Sigma.mk _ (fun z => (fromQuantum_B (next z)).comparisonPublicHistory_B) h.1
          ((fromQuantum_B (next h.1)).publicTranscript_B
          (blockOneEnvironmentEquiv_B (next h.1) h.2))
      rw [ih h.1 h.2]
  | bob C next ih =>
      intro h
      change @Sigma.mk _ (fun z => (fromQuantum_B (next z)).comparisonPublicHistory_B) h.1
          (blockOnePublicEquiv_B (next h.1)
            ((fromQuantum_B (next h.1).toBlockOneB.represented_toMatrix).publicTranscript_B h.2)) =
        @Sigma.mk _ (fun z => (fromQuantum_B (next z)).comparisonPublicHistory_B) h.1
          ((fromQuantum_B (next h.1)).publicTranscript_B
          (blockOneEnvironmentEquiv_B (next h.1) h.2))
      rw [ih h.1 h.2]
  | @call a₀ b₀ af₀ bf₀ next ih =>
      intro h
      change blockOnePublicEquiv_B next
        ((fromQuantum_B next.toBlockOneB.represented_toMatrix).publicTranscript_B h.2.2) =
          (fromQuantum_B next).publicTranscript_B (blockOneEnvironmentEquiv_B next h.2.2)
      exact ih h.2.2

theorem blockOne_publicHistory_eq_B {p : ℝ} {a b af bf : ℕ}
    (P : FiniteProtocol p a b af bf)
    (h h' : (fromQuantum_B P.toBlockOneB.represented_toMatrix).Environment) :
    (fromQuantum_B P.toBlockOneB.represented_toMatrix).publicTranscript_B h =
        (fromQuantum_B P.toBlockOneB.represented_toMatrix).publicTranscript_B h' ↔
      (fromQuantum_B P).publicTranscript_B (blockOneEnvironmentEquiv_B P h) =
        (fromQuantum_B P).publicTranscript_B (blockOneEnvironmentEquiv_B P h') := by
  rw [← blockOne_publicTranscript_B, ← blockOne_publicTranscript_B]
  exact (blockOnePublicEquiv_B P).injective.eq_iff.symm

theorem blockOne_fullOutput_B {p : ℝ} {a b af bf : ℕ}
    (P : FiniteProtocol p a b af bf) (ρ : PhysicalProtocol.BipartiteMatrix a b)
    (x y : Fin af × Fin bf)
    (h h' : (fromQuantum_B P.toBlockOneB.represented_toMatrix).Environment) :
    (fromQuantum_B P.toBlockOneB.represented_toMatrix).fullOutput ρ (x,h) (y,h') =
      (fromQuantum_B P).fullOutput ρ (x,blockOneEnvironmentEquiv_B P h)
        (y,blockOneEnvironmentEquiv_B P h') := by
  rw [fullOutput_historyKraus_apply_B, fullOutput_historyKraus_apply_B]
  simp only [blockOne_publicHistory_eq_B, blockOne_historyKraus_B]

theorem blockOne_priorEve_B {E : Type*} {p : ℝ} {a b af bf : ℕ}
    (P : FiniteProtocol p a b af bf)
    (ρ : Matrix ((Fin a × Fin b) × E) ((Fin a × Fin b) × E) ℂ)
    (x y : Fin af × Fin bf)
    (h h' : (fromQuantum_B P.toBlockOneB.represented_toMatrix).Environment) (e e' : E) :
    PublicHistory.localPriorEveMatrix_B (fromQuantum_B P.toBlockOneB.represented_toMatrix) ρ
        (x,(h,e)) (y,(h',e')) =
      PublicHistory.localPriorEveMatrix_B (fromQuantum_B P) ρ
        (x,(blockOneEnvironmentEquiv_B P h,e))
        (y,(blockOneEnvironmentEquiv_B P h',e')) := by
  exact blockOne_fullOutput_B P _ x y h h'

def sigmaLeftPairEquiv_B {Z : Type*} {A R : Z → Type*} {B : Type*}
    (e : ∀ z, R z ≃ (A z × B)) : ((z : Z) × R z) ≃ (((z : Z) × A z) × B) where
  toFun h := (⟨h.1,(e h.1 h.2).1⟩,(e h.1 h.2).2)
  invFun h := ⟨h.1.1,(e h.1.1).symm (h.1.2,h.2)⟩
  left_inv h := by
    rcases h with ⟨z,t⟩
    change Sigma.mk z ((e z).symm (e z t)) = Sigma.mk z t
    rw [(e z).symm_apply_apply]
  right_inv h := by
    rcases h with ⟨⟨z,t⟩,u⟩
    simp only [(e z).apply_symm_apply]

def sigmaRightPairEquiv_B {Z : Type*} {B R : Z → Type*} {A : Type*}
    (e : ∀ z, R z ≃ (A × B z)) : ((z : Z) × R z) ≃ (A × ((z : Z) × B z)) where
  toFun h := ((e h.1 h.2).1,⟨h.1,(e h.1 h.2).2⟩)
  invFun h := ⟨h.2.1,(e h.2.1).symm (h.1,h.2.2)⟩
  left_inv h := by
    rcases h with ⟨z,t⟩
    change Sigma.mk z ((e z).symm (e z t)) = Sigma.mk z t
    rw [(e z).symm_apply_apply]
  right_inv h := by
    rcases h with ⟨u,⟨z,t⟩⟩
    simp only [(e z).apply_symm_apply]

abbrev keyInstrument_B {i o k : ℕ} (K : KrausInstrument i o k) :
    KrausChannel (Fin i) (Fin o) (Fin k) :=
  { op := K.operator, complete := K.complete }

theorem aliceLeft_historyKraus_B {p : ℝ} {a b ao af bf c d cf df k : ℕ}
    (K : KrausInstrument a ao k)
    (P : Fin k → FiniteKeyProtocol p ao b af bf)
    (Q : FiniteKeyProtocol p c d cf df)
    (R : Fin k → FiniteKeyProtocol p (ao * c) (b * d) (af * cf) (bf * df))
    (e : ∀ z, (R z).Environment ≃ ((P z).Environment × Q.Environment))
    (hK : ∀ z t, (R z).historyKraus_B t =
      pairOperatorB ((P z).historyKraus_B (e z t).1) (Q.historyKraus_B (e z t).2))
    (z : Fin k) (t : (R z).Environment) :
    (FiniteKeyProtocol.alice (keyInstrument_B (tensorLeftInstrumentB K c)) R).historyKraus_B
        ⟨z,t⟩ =
      pairOperatorB
        ((FiniteKeyProtocol.alice (keyInstrument_B K) P).historyKraus_B ⟨z,(e z t).1⟩)
        (Q.historyKraus_B (e z t).2) := by
  change (R z).historyKraus_B t *
      aliceOperator (b := b * d) ((tensorLeftInstrumentB K c).operator z) =
    pairOperatorB ((P z).historyKraus_B (e z t).1 *
      aliceOperator (b := b) (K.operator z)) (Q.historyKraus_B (e z t).2)
  rw [hK z t, aliceOperator_tensorLeftB, pairOperatorB_mul, Matrix.mul_one]

theorem bobLeft_historyKraus_B {p : ℝ} {a b bo af bf c d cf df k : ℕ}
    (K : KrausInstrument b bo k)
    (P : Fin k → FiniteKeyProtocol p a bo af bf)
    (Q : FiniteKeyProtocol p c d cf df)
    (R : Fin k → FiniteKeyProtocol p (a * c) (bo * d) (af * cf) (bf * df))
    (e : ∀ z, (R z).Environment ≃ ((P z).Environment × Q.Environment))
    (hK : ∀ z t, (R z).historyKraus_B t =
      pairOperatorB ((P z).historyKraus_B (e z t).1) (Q.historyKraus_B (e z t).2))
    (z : Fin k) (t : (R z).Environment) :
    (FiniteKeyProtocol.bob (keyInstrument_B (tensorLeftInstrumentB K d)) R).historyKraus_B
        ⟨z,t⟩ =
      pairOperatorB
        ((FiniteKeyProtocol.bob (keyInstrument_B K) P).historyKraus_B ⟨z,(e z t).1⟩)
        (Q.historyKraus_B (e z t).2) := by
  change (R z).historyKraus_B t *
      bobOperator (a := a * c) ((tensorLeftInstrumentB K d).operator z) =
    pairOperatorB ((P z).historyKraus_B (e z t).1 *
      bobOperator (a := a) (K.operator z)) (Q.historyKraus_B (e z t).2)
  rw [hK z t, bobOperator_tensorLeftB, pairOperatorB_mul, Matrix.mul_one]

theorem aliceRight_historyKraus_B {p : ℝ} {a b af bf c d co cf df k : ℕ}
    (K : KrausInstrument c co k)
    (P : FiniteKeyProtocol p a b af bf)
    (Q : Fin k → FiniteKeyProtocol p co d cf df)
    (R : Fin k → FiniteKeyProtocol p (a * co) (b * d) (af * cf) (bf * df))
    (e : ∀ z, (R z).Environment ≃ (P.Environment × (Q z).Environment))
    (hK : ∀ z t, (R z).historyKraus_B t =
      pairOperatorB (P.historyKraus_B (e z t).1) ((Q z).historyKraus_B (e z t).2))
    (z : Fin k) (t : (R z).Environment) :
    (FiniteKeyProtocol.alice (keyInstrument_B (tensorRightInstrumentB K a)) R).historyKraus_B
        ⟨z,t⟩ =
      pairOperatorB (P.historyKraus_B (e z t).1)
        ((FiniteKeyProtocol.alice (keyInstrument_B K) Q).historyKraus_B ⟨z,(e z t).2⟩) := by
  change (R z).historyKraus_B t *
      aliceOperator (b := b * d) ((tensorRightInstrumentB K a).operator z) =
    pairOperatorB (P.historyKraus_B (e z t).1)
      ((Q z).historyKraus_B (e z t).2 * aliceOperator (b := d) (K.operator z))
  rw [hK z t, aliceOperator_tensorRightB, pairOperatorB_mul, Matrix.mul_one]

theorem bobRight_historyKraus_B {p : ℝ} {a b af bf c d do_ cf df k : ℕ}
    (K : KrausInstrument d do_ k)
    (P : FiniteKeyProtocol p a b af bf)
    (Q : Fin k → FiniteKeyProtocol p c do_ cf df)
    (R : Fin k → FiniteKeyProtocol p (a * c) (b * do_) (af * cf) (bf * df))
    (e : ∀ z, (R z).Environment ≃ (P.Environment × (Q z).Environment))
    (hK : ∀ z t, (R z).historyKraus_B t =
      pairOperatorB (P.historyKraus_B (e z t).1) ((Q z).historyKraus_B (e z t).2))
    (z : Fin k) (t : (R z).Environment) :
    (FiniteKeyProtocol.bob (keyInstrument_B (tensorRightInstrumentB K b)) R).historyKraus_B
        ⟨z,t⟩ =
      pairOperatorB (P.historyKraus_B (e z t).1)
        ((FiniteKeyProtocol.bob (keyInstrument_B K) Q).historyKraus_B ⟨z,(e z t).2⟩) := by
  change (R z).historyKraus_B t *
      bobOperator (a := a * c) ((tensorRightInstrumentB K b).operator z) =
    pairOperatorB (P.historyKraus_B (e z t).1)
      ((Q z).historyKraus_B (e z t).2 * bobOperator (a := c) (K.operator z))
  rw [hK z t, bobOperator_tensorRightB, pairOperatorB_mul, Matrix.mul_one]

def sequentialPublicEquiv_B (p : ℝ) : (n a b af bf : ℕ) →
    (Q : FiniteKeyProtocol p a (doubleDimB n b) af bf) →
      (sequentialThenKey_B p n a b af bf Q).comparisonPublicHistory_B ≃
        Q.comparisonPublicHistory_B
  | 0, _, _, _, _, _ => Equiv.refl _
  | n + 1, a, b, af, bf, Q =>
      (oneFlagEquiv_B _).trans (sequentialPublicEquiv_B p n a (2 * b) af bf Q)

theorem sequentialPublic_transcript_B (p : ℝ) (n a b af bf : ℕ)
    (Q : FiniteKeyProtocol p a (doubleDimB n b) af bf) :
    ∀ h, sequentialPublicEquiv_B p n a b af bf Q
        ((sequentialThenKey_B p n a b af bf Q).publicTranscript_B h) =
      Q.publicTranscript_B (sequentialEnvironmentEquiv_B p n a b af bf Q h).2 := by
  induction n generalizing b with
  | zero => intro h; rfl
  | succ n ih =>
      change FiniteKeyProtocol p a (doubleDimB n (2 * b)) af bf at Q
      intro h
      change sequentialPublicEquiv_B p n a (2 * b) af bf Q
          ((sequentialThenKey_B p n a (2 * b) af bf Q).publicTranscript_B h.2.2) =
        Q.publicTranscript_B (sequentialEnvironmentEquiv_B p n a (2 * b) af bf Q h.2.2).2
      exact ih (2 * b) Q h.2.2

def groupedPublicEquiv_B (p : ℝ) (n a b c d af bf : ℕ)
    (Q : FiniteKeyProtocol p (a * c) (doubleDimB n b * (2 * d)) af bf) :
    (groupedThenKey_B p n a b c d af bf Q).comparisonPublicHistory_B ≃
      Q.comparisonPublicHistory_B :=
  (oneFlagEquiv_B _).trans
    ((sequentialPublicEquiv_B p (n + 1) (a * c) (b * d) af bf
      (groupedBobRestore_B p n a b c d af bf Q)).trans (oneFlagEquiv_B _))

theorem groupedPublic_transcript_B (p : ℝ) (n a b c d af bf : ℕ)
    (Q : FiniteKeyProtocol p (a * c) (doubleDimB n b * (2 * d)) af bf)
    (h : (groupedThenKey_B p n a b c d af bf Q).Environment) :
    groupedPublicEquiv_B p n a b c d af bf Q
        ((groupedThenKey_B p n a b c d af bf Q).publicTranscript_B h) =
      Q.publicTranscript_B (groupedEnvironmentEquiv_B p n a b c d af bf Q h).2 := by
  let R := groupedBobRestore_B p n a b c d af bf Q
  let e := sequentialEnvironmentEquiv_B p (n + 1) (a * c) (b * d) af bf R
  have hs := sequentialPublic_transcript_B p (n + 1) (a * c) (b * d) af bf R h.2
  change (sequentialPublicEquiv_B p (n + 1) (a * c) (b * d) af bf R
      ((sequentialThenKey_B p (n + 1) (a * c) (b * d) af bf R).publicTranscript_B h.2)).2 =
    Q.publicTranscript_B (e h.2).2.2
  exact congrArg (fun v : R.comparisonPublicHistory_B => v.2) hs

def splitMergeEnvironmentEquiv_B {A B R : Type*} (n : ℕ) (e : R ≃ A × B) :
    ((Fin (n + 1) → Fin 2) × R) ≃ (((Fin n → Fin 2) × A) × (Fin 2 × B)) where
  toFun h := ((Fin.tail h.1,(e h.2).1),(h.1 0,(e h.2).2))
  invFun h := (Fin.cons h.2.1 h.1.1,e.symm (h.1.2,h.2.2))
  left_inv h := by simp only [Fin.cons_self_tail,e.symm_apply_apply]
  right_inv h := by simp only [Fin.cons_zero,Fin.tail_cons,e.apply_symm_apply]

def pairedKeyEnvironmentEquiv_B (p : ℝ) (n a b af bf c d cf df : ℕ)
    (P : FiniteKeyProtocol p a (doubleDimB n b) af bf)
    (Q : FiniteKeyProtocol p c (2 * d) cf df)
    (R : FiniteKeyProtocol p (a * c) (doubleDimB n b * (2 * d)) (af * cf) (bf * df))
    (e : R.Environment ≃ (P.Environment × Q.Environment)) :
    (groupedThenKey_B p n a b c d (af * cf) (bf * df) R).Environment ≃
      ((sequentialThenKey_B p n a b af bf P).Environment ×
        (FiniteKeyProtocol.call Q).Environment) :=
  (groupedEnvironmentEquiv_B p n a b c d (af * cf) (bf * df) R).trans
    ((splitMergeEnvironmentEquiv_B n e).trans
      ((sequentialEnvironmentEquiv_B p n a b af bf P).symm.prodCongr (Equiv.refl _)))

def pairedKeyPublicEquiv_B (p : ℝ) (n a b af bf c d cf df : ℕ)
    (P : FiniteKeyProtocol p a (doubleDimB n b) af bf)
    (Q : FiniteKeyProtocol p c (2 * d) cf df)
    (R : FiniteKeyProtocol p (a * c) (doubleDimB n b * (2 * d)) (af * cf) (bf * df))
    (e : R.comparisonPublicHistory_B ≃
      (P.comparisonPublicHistory_B × Q.comparisonPublicHistory_B)) :
    (groupedThenKey_B p n a b c d (af * cf) (bf * df) R).comparisonPublicHistory_B ≃
      ((sequentialThenKey_B p n a b af bf P).comparisonPublicHistory_B ×
        (FiniteKeyProtocol.call Q).comparisonPublicHistory_B) :=
  (groupedPublicEquiv_B p n a b c d (af * cf) (bf * df) R).trans
    (e.trans ((sequentialPublicEquiv_B p n a b af bf P).symm.prodCongr (Equiv.refl _)))

theorem pairedKey_historyKraus_B (p : ℝ) (n a b af bf c d cf df : ℕ)
    (P : FiniteKeyProtocol p a (doubleDimB n b) af bf)
    (Q : FiniteKeyProtocol p c (2 * d) cf df)
    (R : FiniteKeyProtocol p (a * c) (doubleDimB n b * (2 * d)) (af * cf) (bf * df))
    (e : R.Environment ≃ (P.Environment × Q.Environment))
    (hK : ∀ t, R.historyKraus_B t =
      pairOperatorB (P.historyKraus_B (e t).1) (Q.historyKraus_B (e t).2))
    (h : (groupedThenKey_B p n a b c d (af * cf) (bf * df) R).Environment) :
    (groupedThenKey_B p n a b c d (af * cf) (bf * df) R).historyKraus_B h =
      pairOperatorB
        ((sequentialThenKey_B p n a b af bf P).historyKraus_B
          (pairedKeyEnvironmentEquiv_B p n a b af bf c d cf df P Q R e h).1)
        ((FiniteKeyProtocol.call Q).historyKraus_B
          (pairedKeyEnvironmentEquiv_B p n a b af bf c d cf df P Q R e h).2) := by
  let f := groupedEnvironmentEquiv_B p n a b c d (af * cf) (bf * df) R
  let eP := sequentialEnvironmentEquiv_B p n a b af bf P
  have hs := sequentialThenKey_historyKraus_B p n a b af bf P
    (eP.symm (Fin.tail (f h).1,(e (f h).2).1))
  have hs' : (sequentialThenKey_B p n a b af bf P).historyKraus_B
      (eP.symm (Fin.tail (f h).1,(e (f h).2).1)) =
    P.historyKraus_B (e (f h).2).1 * sequentialCallsKrausB p n a b (Fin.tail (f h).1) := by
    simpa only [eP,eP.apply_symm_apply] using hs
  change (groupedThenKey_B p n a b c d (af * cf) (bf * df) R).historyKraus_B h =
    pairOperatorB
      ((sequentialThenKey_B p n a b af bf P).historyKraus_B
        (eP.symm (Fin.tail (f h).1,(e (f h).2).1)))
      (Q.historyKraus_B (e (f h).2).2 * transferKraus p c d ((f h).1 0))
  rw [hs',groupedThenKey_historyKraus_B,hK,mergeCallKrausB_eq_pair,
    pairOperatorB_mul,quantum_callOperator_eq_key_B]

theorem pairedKey_publicTranscript_B (p : ℝ) (n a b af bf c d cf df : ℕ)
    (P : FiniteKeyProtocol p a (doubleDimB n b) af bf)
    (Q : FiniteKeyProtocol p c (2 * d) cf df)
    (R : FiniteKeyProtocol p (a * c) (doubleDimB n b * (2 * d)) (af * cf) (bf * df))
    (eH : R.Environment ≃ (P.Environment × Q.Environment))
    (eT : R.comparisonPublicHistory_B ≃
      (P.comparisonPublicHistory_B × Q.comparisonPublicHistory_B))
    (hT : ∀ t, eT (R.publicTranscript_B t) =
      (P.publicTranscript_B (eH t).1,Q.publicTranscript_B (eH t).2))
    (h : (groupedThenKey_B p n a b c d (af * cf) (bf * df) R).Environment) :
    pairedKeyPublicEquiv_B p n a b af bf c d cf df P Q R eT
        ((groupedThenKey_B p n a b c d (af * cf) (bf * df) R).publicTranscript_B h) =
      ((sequentialThenKey_B p n a b af bf P).publicTranscript_B
        (pairedKeyEnvironmentEquiv_B p n a b af bf c d cf df P Q R eH h).1,
       (FiniteKeyProtocol.call Q).publicTranscript_B
        (pairedKeyEnvironmentEquiv_B p n a b af bf c d cf df P Q R eH h).2) := by
  let f := groupedEnvironmentEquiv_B p n a b c d (af * cf) (bf * df) R
  let eP := sequentialEnvironmentEquiv_B p n a b af bf P
  let tP := sequentialPublicEquiv_B p n a b af bf P
  change (tP.symm (eT (groupedPublicEquiv_B p n a b c d (af * cf) (bf * df) R
      ((groupedThenKey_B p n a b c d (af * cf) (bf * df) R).publicTranscript_B h))).1,
    (eT (groupedPublicEquiv_B p n a b c d (af * cf) (bf * df) R
      ((groupedThenKey_B p n a b c d (af * cf) (bf * df) R).publicTranscript_B h))).2) =
      ((sequentialThenKey_B p n a b af bf P).publicTranscript_B
        (eP.symm (Fin.tail (f h).1,(eH (f h).2).1)), Q.publicTranscript_B (eH (f h).2).2)
  rw [groupedPublic_transcript_B,hT]
  apply Prod.ext
  · have hs := sequentialPublic_transcript_B p n a b af bf P
      (eP.symm (Fin.tail (f h).1,(eH (f h).2).1))
    have ht := congrArg (fun u => tP.symm u) hs
    simpa only [eP,tP,tP.symm_apply_apply,eP.apply_symm_apply] using ht.symm
  · rfl

theorem fullOutput_pair_of_history_B {p : ℝ} {a b af bf c d cf df : ℕ}
    (P : FiniteKeyProtocol p a b af bf) (Q : FiniteKeyProtocol p c d cf df)
    (R : FiniteKeyProtocol p (a * c) (b * d) (af * cf) (bf * df))
    (eH : R.Environment ≃ (P.Environment × Q.Environment))
    (eT : R.comparisonPublicHistory_B ≃
      (P.comparisonPublicHistory_B × Q.comparisonPublicHistory_B))
    (hK : ∀ h, R.historyKraus_B h =
      pairOperatorB (P.historyKraus_B (eH h).1) (Q.historyKraus_B (eH h).2))
    (hT : ∀ h, eT (R.publicTranscript_B h) =
      (P.publicTranscript_B (eH h).1,Q.publicTranscript_B (eH h).2))
    (ρ : PhysicalProtocol.BipartiteMatrix a b) (σ : PhysicalProtocol.BipartiteMatrix c d)
    (x y : Fin (af * cf) × Fin (bf * df)) (h h' : R.Environment) :
    R.fullOutput (pairMatrixB ρ σ) (x,h) (y,h') =
      P.fullOutput ρ ((pairLabEquivB af bf cf df x).1,(eH h).1)
        ((pairLabEquivB af bf cf df y).1,(eH h').1) *
      Q.fullOutput σ ((pairLabEquivB af bf cf df x).2,(eH h).2)
        ((pairLabEquivB af bf cf df y).2,(eH h').2) := by
  have hpub : R.publicTranscript_B h = R.publicTranscript_B h' ↔
      P.publicTranscript_B (eH h).1 = P.publicTranscript_B (eH h').1 ∧
        Q.publicTranscript_B (eH h).2 = Q.publicTranscript_B (eH h').2 := by
    calc
      _ ↔ eT (R.publicTranscript_B h) = eT (R.publicTranscript_B h') :=
        eT.injective.eq_iff.symm
      _ ↔ _ := by rw [hT h,hT h',Prod.mk.injEq]
  rw [R.fullOutput_historyKraus_apply_B, P.fullOutput_historyKraus_apply_B,
    Q.fullOutput_historyKraus_apply_B]
  simp only [hpub, hK, pairMatrixB, pairOperatorB_conjTranspose, pairOperatorB_mul]
  by_cases hp : P.publicTranscript_B (eH h).1 = P.publicTranscript_B (eH h').1 <;>
    by_cases hq : Q.publicTranscript_B (eH h).2 = Q.publicTranscript_B (eH h').2 <;>
      simp [hp,hq,pairOperatorB,Matrix.submatrix_apply,Matrix.kronecker_apply]

def pairPriorEveInput_B {a b c d : ℕ} {E F : Type*}
    (ρ : Matrix ((Fin a × Fin b) × E) ((Fin a × Fin b) × E) ℂ)
    (σ : Matrix ((Fin c × Fin d) × F) ((Fin c × Fin d) × F) ℂ) :
    Matrix ((Fin (a * c) × Fin (b * d)) × (E × F))
      ((Fin (a * c) × Fin (b * d)) × (E × F)) ℂ :=
  Matrix.of fun x y =>
    ρ ((pairLabEquivB a b c d x.1).1,x.2.1)
      ((pairLabEquivB a b c d y.1).1,y.2.1) *
    σ ((pairLabEquivB a b c d x.1).2,x.2.2)
      ((pairLabEquivB a b c d y.1).2,y.2.2)

theorem priorEve_pair_of_history_B {E F : Type*} {p : ℝ}
    {a b af bf c d cf df : ℕ}
    (P : FiniteKeyProtocol p a b af bf) (Q : FiniteKeyProtocol p c d cf df)
    (R : FiniteKeyProtocol p (a * c) (b * d) (af * cf) (bf * df))
    (eH : R.Environment ≃ (P.Environment × Q.Environment))
    (eT : R.comparisonPublicHistory_B ≃
      (P.comparisonPublicHistory_B × Q.comparisonPublicHistory_B))
    (hK : ∀ h, R.historyKraus_B h =
      pairOperatorB (P.historyKraus_B (eH h).1) (Q.historyKraus_B (eH h).2))
    (hT : ∀ h, eT (R.publicTranscript_B h) =
      (P.publicTranscript_B (eH h).1,Q.publicTranscript_B (eH h).2))
    (ρ : Matrix ((Fin a × Fin b) × E) ((Fin a × Fin b) × E) ℂ)
    (σ : Matrix ((Fin c × Fin d) × F) ((Fin c × Fin d) × F) ℂ)
    (x y : Fin (af * cf) × Fin (bf * df)) (h h' : R.Environment)
    (e e' : E) (f f' : F) :
    PublicHistory.localPriorEveMatrix_B R (pairPriorEveInput_B ρ σ)
        (x,(h,(e,f))) (y,(h',(e',f'))) =
      PublicHistory.localPriorEveMatrix_B P ρ
        ((pairLabEquivB af bf cf df x).1,((eH h).1,e))
        ((pairLabEquivB af bf cf df y).1,((eH h').1,e')) *
      PublicHistory.localPriorEveMatrix_B Q σ
        ((pairLabEquivB af bf cf df x).2,((eH h).2,f))
        ((pairLabEquivB af bf cf df y).2,((eH h').2,f')) := by
  exact fullOutput_pair_of_history_B P Q R eH eT hK hT
    (Matrix.of fun i j => ρ (i,e) (j,e')) (Matrix.of fun i j => σ (i,f) (j,f')) x y h h'

theorem mergeScalar_matrix_history_B {p : ℝ} {n a b af bf c d cf df : ℕ}
    {P : FiniteBlockProtocolB p n a b af bf} {Q : FiniteProtocol p c d cf df}
    {R : FiniteBlockProtocolB p (n + 1) (a * c) (b * d) (af * cf) (bf * df)}
    (h : MergeScalarDerivationB p n P Q R) :
    ∃ eH : (blockExpansion_B R).Environment ≃
        ((blockExpansion_B P).Environment × (fromQuantum_B Q).Environment),
    ∃ eT : (blockExpansion_B R).comparisonPublicHistory_B ≃
        ((blockExpansion_B P).comparisonPublicHistory_B ×
          (fromQuantum_B Q).comparisonPublicHistory_B),
      (∀ t, (blockExpansion_B R).historyKraus_B t =
        pairOperatorB ((blockExpansion_B P).historyKraus_B (eH t).1)
          ((fromQuantum_B Q).historyKraus_B (eH t).2)) ∧
      (∀ t, eT ((blockExpansion_B R).publicTranscript_B t) =
        ((blockExpansion_B P).publicTranscript_B (eH t).1,
          (fromQuantum_B Q).publicTranscript_B (eH t).2)) := by
  induction h with
  | done a b c d =>
      let eU : Unit ≃ (Unit × Unit) :=
        { toFun := fun _ => ((),())
          invFun := fun _ => ()
          left_inv := fun _ => Subsingleton.elim _ _
          right_inv := fun _ => Subsingleton.elim _ _ }
      refine ⟨eU,eU,?_,?_⟩
      · intro t
        change (1 : PhysicalProtocol.BipartiteMatrix (a * c) (b * d)) =
          pairOperatorB (1 : PhysicalProtocol.BipartiteMatrix a b)
            (1 : PhysicalProtocol.BipartiteMatrix c d)
        simp [pairOperatorB,Matrix.one_kronecker_one,Matrix.submatrix_one_equiv]
      · intro t; rfl
  | aliceLeft K P Q R next ih =>
      choose eH eT hRest using ih
      refine ⟨sigmaLeftPairEquiv_B eH,sigmaLeftPairEquiv_B eT,?_,?_⟩
      · rintro ⟨z,t⟩
        exact aliceLeft_historyKraus_B K (fun z => blockExpansion_B (P z))
          (fromQuantum_B Q) (fun z => blockExpansion_B (R z)) eH
          (fun z => (hRest z).1) z t
      · rintro ⟨z,t⟩
        change
          (@Sigma.mk _ (fun z => (blockExpansion_B (P z)).comparisonPublicHistory_B) z
              (eT z ((blockExpansion_B (R z)).publicTranscript_B t)).1,
            (eT z ((blockExpansion_B (R z)).publicTranscript_B t)).2) =
          (@Sigma.mk _ (fun z => (blockExpansion_B (P z)).comparisonPublicHistory_B) z
              ((blockExpansion_B (P z)).publicTranscript_B (eH z t).1),
            (fromQuantum_B Q).publicTranscript_B (eH z t).2)
        rw [(hRest z).2 t]
  | bobLeft K P Q R next ih =>
      choose eH eT hRest using ih
      refine ⟨sigmaLeftPairEquiv_B eH,sigmaLeftPairEquiv_B eT,?_,?_⟩
      · rintro ⟨z,t⟩
        exact bobLeft_historyKraus_B K (fun z => blockExpansion_B (P z))
          (fromQuantum_B Q) (fun z => blockExpansion_B (R z)) eH
          (fun z => (hRest z).1) z t
      · rintro ⟨z,t⟩
        change
          (@Sigma.mk _ (fun z => (blockExpansion_B (P z)).comparisonPublicHistory_B) z
              (eT z ((blockExpansion_B (R z)).publicTranscript_B t)).1,
            (eT z ((blockExpansion_B (R z)).publicTranscript_B t)).2) =
          (@Sigma.mk _ (fun z => (blockExpansion_B (P z)).comparisonPublicHistory_B) z
              ((blockExpansion_B (P z)).publicTranscript_B (eH z t).1),
            (fromQuantum_B Q).publicTranscript_B (eH z t).2)
        rw [(hRest z).2 t]
  | aliceRight K P Q R next ih =>
      choose eH eT hRest using ih
      refine ⟨sigmaRightPairEquiv_B eH,sigmaRightPairEquiv_B eT,?_,?_⟩
      · rintro ⟨z,t⟩
        exact aliceRight_historyKraus_B K (blockExpansion_B P)
          (fun z => fromQuantum_B (Q z)) (fun z => blockExpansion_B (R z)) eH
          (fun z => (hRest z).1) z t
      · rintro ⟨z,t⟩
        change
          ((eT z ((blockExpansion_B (R z)).publicTranscript_B t)).1,
            @Sigma.mk _ (fun z => (fromQuantum_B (Q z)).comparisonPublicHistory_B) z
              (eT z ((blockExpansion_B (R z)).publicTranscript_B t)).2) =
          ((blockExpansion_B P).publicTranscript_B (eH z t).1,
            @Sigma.mk _ (fun z => (fromQuantum_B (Q z)).comparisonPublicHistory_B) z
              ((fromQuantum_B (Q z)).publicTranscript_B (eH z t).2))
        rw [(hRest z).2 t]
  | bobRight K P Q R next ih =>
      choose eH eT hRest using ih
      refine ⟨sigmaRightPairEquiv_B eH,sigmaRightPairEquiv_B eT,?_,?_⟩
      · rintro ⟨z,t⟩
        exact bobRight_historyKraus_B K (blockExpansion_B P)
          (fun z => fromQuantum_B (Q z)) (fun z => blockExpansion_B (R z)) eH
          (fun z => (hRest z).1) z t
      · rintro ⟨z,t⟩
        change
          ((eT z ((blockExpansion_B (R z)).publicTranscript_B t)).1,
            @Sigma.mk _ (fun z => (fromQuantum_B (Q z)).comparisonPublicHistory_B) z
              (eT z ((blockExpansion_B (R z)).publicTranscript_B t)).2) =
          ((blockExpansion_B P).publicTranscript_B (eH z t).1,
            @Sigma.mk _ (fun z => (fromQuantum_B (Q z)).comparisonPublicHistory_B) z
              ((fromQuantum_B (Q z)).publicTranscript_B (eH z t).2))
        rw [(hRest z).2 t]
  | @pairedCall a₀ b₀ af₀ bf₀ c₀ d₀ cf₀ df₀ P Q R next ih =>
      rcases ih with ⟨eH,eT,hK,hT⟩
      have hp : blockExpansion_B (FiniteBlockProtocolB.blockCall P) =
          sequentialThenKey_B p n a₀ b₀ af₀ bf₀ (blockExpansion_B P) :=
        fromQuantum_sequential_B p n a₀ b₀ af₀ bf₀ P.represented_toMatrix
      have hr : blockExpansion_B (mergeBlockCallThenB p n a₀ b₀ c₀ d₀ R) =
          groupedThenKey_B p n a₀ b₀ c₀ d₀ (af₀ * cf₀) (bf₀ * df₀) (blockExpansion_B R) :=
        (groupedThenKey_eq_actualBlockExpansion_B p n a₀ b₀ c₀ d₀
          (af₀ * cf₀) (bf₀ * df₀) R).symm
      rw [hr,hp]
      refine ⟨pairedKeyEnvironmentEquiv_B p n a₀ b₀ af₀ bf₀ c₀ d₀ cf₀ df₀
          (blockExpansion_B P) (fromQuantum_B Q) (blockExpansion_B R) eH,
        pairedKeyPublicEquiv_B p n a₀ b₀ af₀ bf₀ c₀ d₀ cf₀ df₀
          (blockExpansion_B P) (fromQuantum_B Q) (blockExpansion_B R) eT,?_,?_⟩
      · exact pairedKey_historyKraus_B p n a₀ b₀ af₀ bf₀ c₀ d₀ cf₀ df₀
          (blockExpansion_B P) (fromQuantum_B Q) (blockExpansion_B R) eH hK
      · exact pairedKey_publicTranscript_B p n a₀ b₀ af₀ bf₀ c₀ d₀ cf₀ df₀
          (blockExpansion_B P) (fromQuantum_B Q) (blockExpansion_B R) eH eT hT

theorem mergeScalar_priorEve_B {E F : Type*} {p : ℝ} {n a b af bf c d cf df : ℕ}
    {P : FiniteBlockProtocolB p n a b af bf} {Q : FiniteProtocol p c d cf df}
    {R : FiniteBlockProtocolB p (n + 1) (a * c) (b * d) (af * cf) (bf * df)}
    (h : MergeScalarDerivationB p n P Q R) :
    ∃ eH : (blockExpansion_B R).Environment ≃
        ((blockExpansion_B P).Environment × (fromQuantum_B Q).Environment),
    ∀ (ρ : Matrix ((Fin a × Fin b) × E) ((Fin a × Fin b) × E) ℂ)
      (σ : Matrix ((Fin c × Fin d) × F) ((Fin c × Fin d) × F) ℂ)
      (x y : Fin (af * cf) × Fin (bf * df))
      (t t' : (blockExpansion_B R).Environment) (e e' : E) (f f' : F),
      PublicHistory.localPriorEveMatrix_B (blockExpansion_B R) (pairPriorEveInput_B ρ σ)
          (x,(t,(e,f))) (y,(t',(e',f'))) =
        PublicHistory.localPriorEveMatrix_B (blockExpansion_B P) ρ
          ((pairLabEquivB af bf cf df x).1,((eH t).1,e))
          ((pairLabEquivB af bf cf df y).1,((eH t').1,e')) *
        PublicHistory.localPriorEveMatrix_B (fromQuantum_B Q) σ
          ((pairLabEquivB af bf cf df x).2,((eH t).2,f))
          ((pairLabEquivB af bf cf df y).2,((eH t').2,f')) := by
  rcases mergeScalar_matrix_history_B h with ⟨eH,eT,hK,hT⟩
  refine ⟨eH,?_⟩
  intro ρ σ x y t t' e e' f f'
  exact priorEve_pair_of_history_B (blockExpansion_B P) (fromQuantum_B Q)
    (blockExpansion_B R) eH eT hK hT ρ σ x y t t' e e' f f'

def addEmptyTuple_B (I : Type*) : I ≃ Register I 1 where
  toFun i := (i,PUnit.unit)
  invFun h := h.1
  left_inv _ := rfl
  right_inv h := by rcases h with ⟨i,u⟩; cases u; rfl

def laneHistoryKraus_B {p : ℝ} {a b af bf : ℕ} (P : FiniteProtocol p a b af bf) :
    (n : ℕ) → Register (fromQuantum_B P).Environment (n + 1) →
      Matrix (Fin (lanePowerDimB n af) × Fin (lanePowerDimB n bf))
        (Fin (lanePowerDimB n a) × Fin (lanePowerDimB n b)) ℂ
  | 0, h => (fromQuantum_B P).historyKraus_B h.1
  | n + 1, h => pairOperatorB (laneHistoryKraus_B P n h.2)
      ((fromQuantum_B P).historyKraus_B h.1)

def lanePublicTranscript_B {p : ℝ} {a b af bf : ℕ} (P : FiniteProtocol p a b af bf) :
    (n : ℕ) → Register (fromQuantum_B P).Environment (n + 1) →
      Register (fromQuantum_B P).comparisonPublicHistory_B (n + 1)
  | 0, h => ((fromQuantum_B P).publicTranscript_B h.1,PUnit.unit)
  | n + 1, h => ((fromQuantum_B P).publicTranscript_B h.1,lanePublicTranscript_B P n h.2)

theorem independentLanes_matrix_history_B {p : ℝ} {a b af bf n : ℕ}
    {P : FiniteProtocol p a b af bf}
    {R : FiniteBlockProtocolB p (n + 1) (lanePowerDimB n a) (lanePowerDimB n b)
      (lanePowerDimB n af) (lanePowerDimB n bf)}
    (h : IndependentLanesDerivationB p P n R) :
    ∃ eH : (blockExpansion_B R).Environment ≃ Register (fromQuantum_B P).Environment (n + 1),
    ∃ eT : (blockExpansion_B R).comparisonPublicHistory_B ≃
        Register (fromQuantum_B P).comparisonPublicHistory_B (n + 1),
      (∀ t, (blockExpansion_B R).historyKraus_B t = laneHistoryKraus_B P n (eH t)) ∧
      (∀ t, eT ((blockExpansion_B R).publicTranscript_B t) =
        lanePublicTranscript_B P n (eH t)) := by
  induction h with
  | one =>
      refine ⟨(blockOneEnvironmentEquiv_B P).trans (addEmptyTuple_B _),
        (blockOnePublicEquiv_B P).trans (addEmptyTuple_B _),?_,?_⟩
      · exact blockOne_historyKraus_B P
      · intro t
        change (blockOnePublicEquiv_B P
            ((fromQuantum_B P.toBlockOneB.represented_toMatrix).publicTranscript_B t),PUnit.unit) =
          ((fromQuantum_B P).publicTranscript_B (blockOneEnvironmentEquiv_B P t),PUnit.unit)
        exact congrArg (fun u => (u,PUnit.unit)) (blockOne_publicTranscript_B P t)
  | @append n R S previous merge ih =>
      rcases ih with ⟨eH,eT,hK,hT⟩
      rcases mergeScalar_matrix_history_B merge with ⟨eM,eMT,hMK,hMT⟩
      refine ⟨eM.trans ((eH.prodCongr (Equiv.refl _)).trans (Equiv.prodComm _ _)),
        eMT.trans ((eT.prodCongr (Equiv.refl _)).trans (Equiv.prodComm _ _)),?_,?_⟩
      · intro t
        change (blockExpansion_B S).historyKraus_B t =
          pairOperatorB (laneHistoryKraus_B P n (eH (eM t).1))
            ((fromQuantum_B P).historyKraus_B (eM t).2)
        exact (hMK t).trans (congrArg
          (fun M => pairOperatorB M ((fromQuantum_B P).historyKraus_B (eM t).2))
          (hK (eM t).1))
      · intro t
        change ((eMT ((blockExpansion_B S).publicTranscript_B t)).2,
            eT (eMT ((blockExpansion_B S).publicTranscript_B t)).1) =
          ((fromQuantum_B P).publicTranscript_B (eM t).2,
            lanePublicTranscript_B P n (eH (eM t).1))
        exact (congrArg (fun u => (u.2,eT u.1)) (hMT t)).trans
          (congrArg (fun u => ((fromQuantum_B P).publicTranscript_B (eM t).2,u))
            (hT (eM t).1))

@[reducible] def LaneEveRegister_B (E : Type*) : ℕ → Type _
  | 0 => E
  | n + 1 => LaneEveRegister_B E n × E

def lanePriorMatrix_B {a b : ℕ} {E : Type*}
    (ρ : Matrix ((Fin a × Fin b) × E) ((Fin a × Fin b) × E) ℂ) :
    (n : ℕ) → Matrix
      ((Fin (lanePowerDimB n a) × Fin (lanePowerDimB n b)) × LaneEveRegister_B E n)
      ((Fin (lanePowerDimB n a) × Fin (lanePowerDimB n b)) × LaneEveRegister_B E n) ℂ
  | 0 => ρ
  | n + 1 => pairPriorEveInput_B (lanePriorMatrix_B ρ n) ρ

def laneInputEquiv_B (a b : ℕ) (E : Type*) : (n : ℕ) →
    ((Fin (lanePowerDimB n a) × Fin (lanePowerDimB n b)) × LaneEveRegister_B E n) ≃
      Register ((Fin a × Fin b) × E) (n + 1)
  | 0 => addEmptyTuple_B _
  | n + 1 =>
      ((pairLabEquivB (lanePowerDimB n a) (lanePowerDimB n b) a b).prodCongr
        (Equiv.refl _)).trans
      ((Equiv.prodProdProdComm _ _ _ _).trans
      (((laneInputEquiv_B a b E n).prodCongr (Equiv.refl _)).trans
        (Equiv.prodComm _ _)))

theorem lanePriorMatrix_eq_tensor_B {a b : ℕ} {E : Type*}
    [Fintype E] [DecidableEq E]
    (ρ : Matrix ((Fin a × Fin b) × E) ((Fin a × Fin b) × E) ℂ) (n : ℕ) :
    lanePriorMatrix_B ρ n = (matrix ρ (n + 1)).submatrix
      (laneInputEquiv_B a b E n) (laneInputEquiv_B a b E n) := by
  induction n with
  | zero =>
      ext x y
      change ρ x y = ρ x y * (1 : Matrix PUnit PUnit ℂ) PUnit.unit PUnit.unit
      simp
  | succ n ih =>
      ext x y
      change lanePriorMatrix_B ρ n
          ((pairLabEquivB (lanePowerDimB n a) (lanePowerDimB n b) a b x.1).1,x.2.1)
          ((pairLabEquivB (lanePowerDimB n a) (lanePowerDimB n b) a b y.1).1,y.2.1) *
            ρ ((pairLabEquivB (lanePowerDimB n a) (lanePowerDimB n b) a b x.1).2,x.2.2)
              ((pairLabEquivB (lanePowerDimB n a) (lanePowerDimB n b) a b y.1).2,y.2.2) = _
      rw [ih]
      exact mul_comm _ _

def laneHistoryEveEquiv_B (H : Type*) (E : Type*) : (n : ℕ) →
    (Register H (n + 1) × LaneEveRegister_B E n) ≃ LaneEveRegister_B (H × E) n
  | 0 => (addEmptyTuple_B H).symm.prodCongr (Equiv.refl E)
  | n + 1 =>
      ((Equiv.prodComm H (Register H (n + 1))).prodCongr (Equiv.refl _)).trans
      ((Equiv.prodProdProdComm _ _ _ _).trans
        ((laneHistoryEveEquiv_B H E n).prodCongr (Equiv.refl _)))

theorem independentLanes_priorEve_B {E : Type*} {p : ℝ} {a b af bf n : ℕ}
    {P : FiniteProtocol p a b af bf}
    {R : FiniteBlockProtocolB p (n + 1) (lanePowerDimB n a) (lanePowerDimB n b)
      (lanePowerDimB n af) (lanePowerDimB n bf)}
    (h : IndependentLanesDerivationB p P n R) :
    ∃ eH : (blockExpansion_B R).Environment ≃ Register (fromQuantum_B P).Environment (n + 1),
    ∃ eT : (blockExpansion_B R).comparisonPublicHistory_B ≃
        Register (fromQuantum_B P).comparisonPublicHistory_B (n + 1),
      (∀ t, (blockExpansion_B R).historyKraus_B t = laneHistoryKraus_B P n (eH t)) ∧
      (∀ t, eT ((blockExpansion_B R).publicTranscript_B t) =
        lanePublicTranscript_B P n (eH t)) ∧
    ∀ (ρ : Matrix ((Fin a × Fin b) × E) ((Fin a × Fin b) × E) ℂ)
      (x y : Fin (lanePowerDimB n af) × Fin (lanePowerDimB n bf))
      (t t' : (blockExpansion_B R).Environment) (e e' : LaneEveRegister_B E n),
      PublicHistory.localPriorEveMatrix_B (blockExpansion_B R) (lanePriorMatrix_B ρ n)
          (x,(t,e)) (y,(t',e')) =
        lanePriorMatrix_B (PublicHistory.localPriorEveMatrix_B (fromQuantum_B P) ρ) n
          (x,laneHistoryEveEquiv_B (fromQuantum_B P).Environment E n (eH t,e))
          (y,laneHistoryEveEquiv_B (fromQuantum_B P).Environment E n (eH t',e')) := by
  induction h with
  | one =>
      refine ⟨(blockOneEnvironmentEquiv_B P).trans (addEmptyTuple_B _),
        (blockOnePublicEquiv_B P).trans (addEmptyTuple_B _),?_,?_,?_⟩
      · exact blockOne_historyKraus_B P
      · intro t
        exact congrArg (fun u => (u,PUnit.unit)) (blockOne_publicTranscript_B P t)
      · intro ρ x y t t' e e'
        exact blockOne_priorEve_B P ρ x y t t' e e'
  | @append n R S previous merge ih =>
      rcases ih with ⟨eH,eT,hK,hT,hO⟩
      rcases mergeScalar_matrix_history_B merge with ⟨eM,eMT,hMK,hMT⟩
      refine ⟨eM.trans ((eH.prodCongr (Equiv.refl _)).trans (Equiv.prodComm _ _)),
        eMT.trans ((eT.prodCongr (Equiv.refl _)).trans (Equiv.prodComm _ _)),?_,?_,?_⟩
      · intro t
        exact (hMK t).trans (congrArg
          (fun M => pairOperatorB M ((fromQuantum_B P).historyKraus_B (eM t).2))
          (hK (eM t).1))
      · intro t
        exact (congrArg (fun u => (u.2,eT u.1)) (hMT t)).trans
          (congrArg (fun u => ((fromQuantum_B P).publicTranscript_B (eM t).2,u))
            (hT (eM t).1))
      · intro ρ x y t t' e e'
        exact (priorEve_pair_of_history_B (blockExpansion_B R) (fromQuantum_B P)
        (blockExpansion_B S) eM eMT hMK hMT (lanePriorMatrix_B ρ n) ρ x y t t'
        e.1 e'.1 e.2 e'.2).trans
          (congrArg (fun v => v * PublicHistory.localPriorEveMatrix_B (fromQuantum_B P) ρ
            ((pairLabEquivB (lanePowerDimB n af) (lanePowerDimB n bf) af bf x).2,
              ((eM t).2,e.2))
            ((pairLabEquivB (lanePowerDimB n af) (lanePowerDimB n bf) af bf y).2,
              ((eM t').2,e'.2)))
            (hO ρ (pairLabEquivB (lanePowerDimB n af) (lanePowerDimB n bf) af bf x).1
              (pairLabEquivB (lanePowerDimB n af) (lanePowerDimB n bf) af bf y).1
              (eM t).1 (eM t').1 e.1 e'.1))

theorem independentLanes_calls_B {p : ℝ} {a b af bf n m : ℕ}
    {P : FiniteProtocol p a b af bf}
    {R : FiniteBlockProtocolB p (n + 1) (lanePowerDimB n a) (lanePowerDimB n b)
      (lanePowerDimB n af) (lanePowerDimB n bf)}
    (h : IndependentLanesDerivationB p P n R) (hP : P.UniformCallsB m) :
    R.calls ≤ m ∧ (blockExpansion_B R).calls ≤ (n + 1) * m := by
  have hR : R.calls ≤ m := (h.uniform hP).calls_le
  refine ⟨hR,?_⟩
  exact (blockExpansion_calls_le_B R).trans (Nat.mul_le_mul_left (n + 1) hR)

def laneOutputEveEquiv_B {p : ℝ} {a b af bf n : ℕ}
    {P : FiniteProtocol p a b af bf}
    {R : FiniteBlockProtocolB p (n + 1) (lanePowerDimB n a) (lanePowerDimB n b)
      (lanePowerDimB n af) (lanePowerDimB n bf)}
    (E : Type*)
    (eH : (blockExpansion_B R).Environment ≃ Register (fromQuantum_B P).Environment (n + 1)) :
    ((Fin (lanePowerDimB n af) × Fin (lanePowerDimB n bf)) ×
        ((blockExpansion_B R).Environment × LaneEveRegister_B E n)) ≃
      Register ((Fin af × Fin bf) × ((fromQuantum_B P).Environment × E)) (n + 1) :=
  ((Equiv.refl _).prodCongr
    ((eH.prodCongr (Equiv.refl _)).trans
      (laneHistoryEveEquiv_B (fromQuantum_B P).Environment E n))).trans
    (laneInputEquiv_B af bf ((fromQuantum_B P).Environment × E) n)

theorem independentLanes_priorEve_tensor_B {E : Type*} [Fintype E] [DecidableEq E]
    {p : ℝ} {a b af bf n : ℕ} {P : FiniteProtocol p a b af bf}
    {R : FiniteBlockProtocolB p (n + 1) (lanePowerDimB n a) (lanePowerDimB n b)
      (lanePowerDimB n af) (lanePowerDimB n bf)}
    (h : IndependentLanesDerivationB p P n R) :
    ∃ eH : (blockExpansion_B R).Environment ≃ Register (fromQuantum_B P).Environment (n + 1),
    ∃ eT : (blockExpansion_B R).comparisonPublicHistory_B ≃
        Register (fromQuantum_B P).comparisonPublicHistory_B (n + 1),
      (∀ t, (blockExpansion_B R).historyKraus_B t = laneHistoryKraus_B P n (eH t)) ∧
      (∀ t, eT ((blockExpansion_B R).publicTranscript_B t) =
        lanePublicTranscript_B P n (eH t)) ∧
    ∀ ρ : Matrix ((Fin a × Fin b) × E) ((Fin a × Fin b) × E) ℂ,
      PublicHistory.localPriorEveMatrix_B (blockExpansion_B R) (lanePriorMatrix_B ρ n) =
        (matrix (PublicHistory.localPriorEveMatrix_B (fromQuantum_B P) ρ) (n + 1)).submatrix
          (laneOutputEveEquiv_B E eH) (laneOutputEveEquiv_B E eH) := by
  rcases independentLanes_priorEve_B (E := E) h with ⟨eH,eT,hK,hT,hO⟩
  refine ⟨eH,eT,hK,hT,?_⟩
  intro ρ
  ext x y
  exact (hO ρ x.1 y.1 x.2.1 y.2.1 x.2.2 y.2.2).trans
    (congrArg (fun M => M
      (x.1,laneHistoryEveEquiv_B (fromQuantum_B P).Environment E n (eH x.2.1,x.2.2))
      (y.1,laneHistoryEveEquiv_B (fromQuantum_B P).Environment E n (eH y.2.1,y.2.2)))
      (lanePriorMatrix_eq_tensor_B
        (PublicHistory.localPriorEveMatrix_B (fromQuantum_B P) ρ) n))

theorem exists_uniformLanes_priorEve_B {E : Type*} [Fintype E] [DecidableEq E]
    {p : ℝ} {a b af bf m : ℕ} (P : FiniteProtocol p a b af bf)
    (hP : P.UniformCallsB m) (n : ℕ) :
    ∃ R : FiniteBlockProtocolB p (n + 1) (lanePowerDimB n a) (lanePowerDimB n b)
      (lanePowerDimB n af) (lanePowerDimB n bf),
      IndependentLanesDerivationB p P n R ∧ R.calls ≤ m ∧
        (blockExpansion_B R).calls ≤ (n + 1) * m ∧
    ∃ eH : (blockExpansion_B R).Environment ≃ Register (fromQuantum_B P).Environment (n + 1),
    ∃ eT : (blockExpansion_B R).comparisonPublicHistory_B ≃
        Register (fromQuantum_B P).comparisonPublicHistory_B (n + 1),
      (∀ t, (blockExpansion_B R).historyKraus_B t = laneHistoryKraus_B P n (eH t)) ∧
      (∀ t, eT ((blockExpansion_B R).publicTranscript_B t) =
        lanePublicTranscript_B P n (eH t)) ∧
    ∀ ρ : Matrix ((Fin a × Fin b) × E) ((Fin a × Fin b) × E) ℂ,
      PublicHistory.localPriorEveMatrix_B (blockExpansion_B R) (lanePriorMatrix_B ρ n) =
        (matrix (PublicHistory.localPriorEveMatrix_B (fromQuantum_B P) ρ) (n + 1)).submatrix
          (laneOutputEveEquiv_B E eH) (laneOutputEveEquiv_B E eH) := by
  rcases P.exists_uniform_lanes_with_derivationB hP n with ⟨R,hR,hRC,hRU,hRN,hRO⟩
  rcases independentLanes_calls_B hR hP with ⟨hC,hN⟩
  rcases independentLanes_priorEve_tensor_B (E := E) hR with ⟨eH,eT,hK,hT,hO⟩
  exact ⟨R,hR,hC,hN,eH,eT,hK,hT,hO⟩

end QuantumProver.AmplitudeDamping.SecretKey.LaneMergeHistory

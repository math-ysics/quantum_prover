import QuantumProver.InformationTheory.AmplitudeDamping.QuantumCapacity.IdlePaddingHistory
import QuantumProver.InformationTheory.AmplitudeDamping.SecretKey.LaneMergeHistory

set_option autoImplicit false

noncomputable section

attribute [local instance] Classical.propDecidable

open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix Kronecker

namespace QuantumProver.AmplitudeDamping.SecretKey.IdleEvePadding

open PhysicalProtocol PhysicalProtocol.FiniteKeyProtocol IndependentLanes LaneMergeHistory
open QuantumProver.AmplitudeDamping.FiniteModel

def dropIdleHistory_B {p : ℝ} {a b af bf : ℕ} (P : FiniteProtocol p a b af bf)
    (h : (fromQuantum_B (idleCallThenB p P)).Environment) :
    (fromQuantum_B P).Environment := h.2.2.2

def idleGroundHistory_B {p : ℝ} {a b af bf : ℕ} (P : FiniteProtocol p a b af bf)
    (h : (fromQuantum_B (idleCallThenB p P)).Environment) : Prop :=
  h.2.1 = 0 ∧ h.2.2.1 = 0

def groundIdleHistoryEmbedding_B {p : ℝ} {a b af bf : ℕ}
    (P : FiniteProtocol p a b af bf) :
    (fromQuantum_B P).Environment ↪ (fromQuantum_B (idleCallThenB p P)).Environment where
  toFun t := ⟨0,(0,⟨0,t⟩)⟩
  inj' := by
    intro t t' h
    exact congrArg (dropIdleHistory_B P) h

theorem groundIdleHistory_leftInverse_B {p : ℝ} {a b af bf : ℕ}
    (P : FiniteProtocol p a b af bf) :
    Function.LeftInverse (dropIdleHistory_B P) (groundIdleHistoryEmbedding_B P) :=
  fun _ => rfl

theorem groundIdleHistory_image_iff_B {p : ℝ} {a b af bf : ℕ}
    (P : FiniteProtocol p a b af bf)
    (h : (fromQuantum_B (idleCallThenB p P)).Environment) :
    groundIdleHistoryEmbedding_B P (dropIdleHistory_B P h) = h ↔ idleGroundHistory_B P h := by
  rcases h with ⟨u,z,⟨r,t⟩⟩
  have hu : u = 0 := Subsingleton.elim _ _
  subst u
  constructor
  · intro h
    exact ⟨(congrArg (fun v => v.2.1) h).symm,
      (congrArg (fun v => v.2.2.1) h).symm⟩
  · rintro ⟨rfl,rfl⟩
    rfl

theorem idleCall_historyKraus_B {p : ℝ} {a b af bf : ℕ}
    (P : FiniteProtocol p a b af bf)
    (h : (fromQuantum_B (idleCallThenB p P)).Environment) :
    (fromQuantum_B (idleCallThenB p P)).historyKraus_B h =
      if idleGroundHistory_B P h then
        (fromQuantum_B P).historyKraus_B (dropIdleHistory_B P h) else 0 := by
  rcases h with ⟨u,z,⟨r,t⟩⟩
  have hu : u = 0 := Subsingleton.elim _ _
  subst u
  change (((fromQuantum_B P).historyKraus_B t *
      ((1 : Matrix (Fin a) (Fin a) ℂ) ⊗ₖ (discardQubitInstrumentB b).operator r)) *
        transferKraus p a b z) *
          ((groundPrepareInstrumentB a).operator 0 ⊗ₖ (1 : Matrix (Fin b) (Fin b) ℂ)) =
    if idleGroundHistory_B P ⟨0,(z,⟨r,t⟩)⟩ then (fromQuantum_B P).historyKraus_B t else 0
  rw [← quantum_callOperator_eq_key_B]
  calc
    _ = (fromQuantum_B P).historyKraus_B t * idleCallKrausB p a b r z := by
      simp only [idleCallKrausB,bobOperator,aliceOperator,Matrix.mul_assoc]
    _ = _ := by
      rw [idleCallKrausB_eq_identity]
      by_cases hz : z = 0 <;> by_cases hr : r = 0 <;> simp [idleGroundHistory_B,hz,hr]

theorem idleCall_publicHistory_B {p : ℝ} {a b af bf : ℕ}
    (P : FiniteProtocol p a b af bf)
    (h h' : (fromQuantum_B (idleCallThenB p P)).Environment)
    (hh : idleGroundHistory_B P h) (hh' : idleGroundHistory_B P h') :
    (fromQuantum_B (idleCallThenB p P)).publicTranscript_B h =
        (fromQuantum_B (idleCallThenB p P)).publicTranscript_B h' ↔
      (fromQuantum_B P).publicTranscript_B (dropIdleHistory_B P h) =
        (fromQuantum_B P).publicTranscript_B (dropIdleHistory_B P h') := by
  have he := (groundIdleHistory_image_iff_B P h).mpr hh
  have he' := (groundIdleHistory_image_iff_B P h').mpr hh'
  rw [← he,← he']
  constructor
  · intro heq
    exact congrArg
      (fun t : (fromQuantum_B (idleCallThenB p P)).comparisonPublicHistory_B => t.2.2) heq
  · intro heq
    exact congrArg (fun t : (fromQuantum_B P).comparisonPublicHistory_B =>
      (⟨0,⟨0,t⟩⟩ : (fromQuantum_B (idleCallThenB p P)).comparisonPublicHistory_B)) heq

theorem idleCall_fullOutput_B {p : ℝ} {a b af bf : ℕ}
    (P : FiniteProtocol p a b af bf) (ρ : PhysicalProtocol.BipartiteMatrix a b)
    (x y : Fin af × Fin bf)
    (h h' : (fromQuantum_B (idleCallThenB p P)).Environment) :
    (fromQuantum_B (idleCallThenB p P)).fullOutput ρ (x,h) (y,h') =
      if idleGroundHistory_B P h ∧ idleGroundHistory_B P h' then
        (fromQuantum_B P).fullOutput ρ
          (x,dropIdleHistory_B P h) (y,dropIdleHistory_B P h') else 0 := by
  rw [fullOutput_historyKraus_apply_B, fullOutput_historyKraus_apply_B,
    idleCall_historyKraus_B,idleCall_historyKraus_B]
  by_cases hh : idleGroundHistory_B P h
  · by_cases hh' : idleGroundHistory_B P h'
    · simp only [if_pos hh,if_pos hh',if_pos (And.intro hh hh'),
        idleCall_publicHistory_B P h h' hh hh']
    · simp [hh,hh']
  · simp [hh]

theorem idleCall_priorEve_B {E : Type*} {p : ℝ} {a b af bf : ℕ}
    (P : FiniteProtocol p a b af bf)
    (ρ : Matrix ((Fin a × Fin b) × E) ((Fin a × Fin b) × E) ℂ)
    (x y : Fin af × Fin bf)
    (h h' : (fromQuantum_B (idleCallThenB p P)).Environment) (e e' : E) :
    PublicHistory.localPriorEveMatrix_B (fromQuantum_B (idleCallThenB p P)) ρ
        (x,(h,e)) (y,(h',e')) =
      if idleGroundHistory_B P h ∧ idleGroundHistory_B P h' then
        PublicHistory.localPriorEveMatrix_B (fromQuantum_B P) ρ
          (x,(dropIdleHistory_B P h,e)) (y,(dropIdleHistory_B P h',e')) else 0 :=
  idleCall_fullOutput_B P _ x y h h'

theorem sigma_same_eq_iff_B {Z : Type*} {A : Z → Type*} (z : Z) (x y : A z) :
    (Sigma.mk z x = Sigma.mk z y) ↔ x = y := by
  constructor
  · intro h
    exact eq_of_heq (Sigma.mk.inj_iff.mp h).2
  · intro h
    exact congrArg (Sigma.mk z) h

theorem idleCall_transport_history_B {p : ℝ} {a b af bf : ℕ}
    (P Q : FiniteProtocol p a b af bf)
    (f : (fromQuantum_B P).Environment → (fromQuantum_B Q).Environment)
    (g : (fromQuantum_B Q).Environment → (fromQuantum_B P).Environment)
    (hfg : Function.LeftInverse g f)
    (hK : ∀ t, (fromQuantum_B Q).historyKraus_B t =
      if f (g t) = t then (fromQuantum_B P).historyKraus_B (g t) else 0)
    (hT : ∀ t t', f (g t) = t → f (g t') = t' →
      ((fromQuantum_B Q).publicTranscript_B t = (fromQuantum_B Q).publicTranscript_B t' ↔
        (fromQuantum_B P).publicTranscript_B (g t) =
          (fromQuantum_B P).publicTranscript_B (g t'))) :
    ∃ F : (fromQuantum_B P).Environment → (fromQuantum_B (idleCallThenB p Q)).Environment,
    ∃ G : (fromQuantum_B (idleCallThenB p Q)).Environment → (fromQuantum_B P).Environment,
      Function.LeftInverse G F ∧
      (∀ t, (fromQuantum_B (idleCallThenB p Q)).historyKraus_B t =
        if F (G t) = t then (fromQuantum_B P).historyKraus_B (G t) else 0) ∧
      (∀ t t', F (G t) = t → F (G t') = t' →
        ((fromQuantum_B (idleCallThenB p Q)).publicTranscript_B t =
            (fromQuantum_B (idleCallThenB p Q)).publicTranscript_B t' ↔
          (fromQuantum_B P).publicTranscript_B (G t) =
            (fromQuantum_B P).publicTranscript_B (G t'))) := by
  let F := fun t => groundIdleHistoryEmbedding_B Q (f t)
  let G := fun t => g (dropIdleHistory_B Q t)
  have hground (t : (fromQuantum_B (idleCallThenB p Q)).Environment) :
      F (G t) = t ↔ idleGroundHistory_B Q t ∧
        f (g (dropIdleHistory_B Q t)) = dropIdleHistory_B Q t := by
    constructor
    · intro ht
      have hd : f (g (dropIdleHistory_B Q t)) = dropIdleHistory_B Q t :=
        congrArg (dropIdleHistory_B Q) ht
      have hg : groundIdleHistoryEmbedding_B Q (dropIdleHistory_B Q t) = t :=
        (congrArg (groundIdleHistoryEmbedding_B Q) hd).symm.trans ht
      exact ⟨(groundIdleHistory_image_iff_B Q t).mp hg,hd⟩
    · rintro ⟨hg,hd⟩
      exact (congrArg (groundIdleHistoryEmbedding_B Q) hd).trans
        ((groundIdleHistory_image_iff_B Q t).mpr hg)
  refine ⟨F,G,?_,?_,?_⟩
  · intro t
    exact hfg t
  · intro t
    rw [idleCall_historyKraus_B]
    have hk := hK (dropIdleHistory_B Q t)
    by_cases hg : idleGroundHistory_B Q t
    · by_cases hd : f (g (dropIdleHistory_B Q t)) = dropIdleHistory_B Q t
      · have hf := (hground t).mpr ⟨hg,hd⟩
        simpa only [if_pos hg,if_pos hd,if_pos hf] using hk
      · have hf : ¬ F (G t) = t := fun hf => hd ((hground t).mp hf).2
        simpa only [if_pos hg,if_neg hd,if_neg hf] using hk
    · have hf : ¬ F (G t) = t := fun hf => hg ((hground t).mp hf).1
      simp only [if_neg hg,if_neg hf]
  · intro t t' ht ht'
    rcases (hground t).mp ht with ⟨hg,hd⟩
    rcases (hground t').mp ht' with ⟨hg',hd'⟩
    exact (idleCall_publicHistory_B Q t t' hg hg').trans
      (hT (dropIdleHistory_B Q t) (dropIdleHistory_B Q t') hd hd')

theorem idleCalls_transport_history_B {p : ℝ} {a b af bf : ℕ}
    (P : FiniteProtocol p a b af bf) (n : ℕ) :
    ∃ f : (fromQuantum_B P).Environment → (fromQuantum_B (idleCallsThenB p n P)).Environment,
    ∃ g : (fromQuantum_B (idleCallsThenB p n P)).Environment → (fromQuantum_B P).Environment,
      Function.LeftInverse g f ∧
      (∀ t, (fromQuantum_B (idleCallsThenB p n P)).historyKraus_B t =
        if f (g t) = t then (fromQuantum_B P).historyKraus_B (g t) else 0) ∧
      (∀ t t', f (g t) = t → f (g t') = t' →
        ((fromQuantum_B (idleCallsThenB p n P)).publicTranscript_B t =
            (fromQuantum_B (idleCallsThenB p n P)).publicTranscript_B t' ↔
          (fromQuantum_B P).publicTranscript_B (g t) =
            (fromQuantum_B P).publicTranscript_B (g t'))) := by
  induction n with
  | zero =>
      refine ⟨id,id,fun _ => rfl,?_,?_⟩
      · intro t
        change (fromQuantum_B P).historyKraus_B t =
          if t = t then (fromQuantum_B P).historyKraus_B t else 0
        exact (if_pos rfl).symm
      · intro t t' _ _
        rfl
  | succ n ih =>
      rcases ih with ⟨f,g,hfg,hK,hT⟩
      exact idleCall_transport_history_B P (idleCallsThenB p n P) f g hfg hK hT

theorem padding_transport_history_B {p : ℝ} {a b af bf m : ℕ}
    {P Q : FiniteProtocol p a b af bf} (h : UniformPaddingDerivationB p m P Q) :
    ∃ f : (fromQuantum_B P).Environment → (fromQuantum_B Q).Environment,
    ∃ g : (fromQuantum_B Q).Environment → (fromQuantum_B P).Environment,
      Function.LeftInverse g f ∧
      (∀ t, (fromQuantum_B Q).historyKraus_B t =
        if f (g t) = t then (fromQuantum_B P).historyKraus_B (g t) else 0) ∧
      (∀ t t', f (g t) = t → f (g t') = t' →
        ((fromQuantum_B Q).publicTranscript_B t = (fromQuantum_B Q).publicTranscript_B t' ↔
          (fromQuantum_B P).publicTranscript_B (g t) =
            (fromQuantum_B P).publicTranscript_B (g t'))) := by
  induction h with
  | done a b m => exact idleCalls_transport_history_B (.done a b) m
  | @alice a b ao af bf k m K P Q next ih =>
      choose e d hed hK hT using ih
      let F : (fromQuantum_B (.alice K P)).Environment →
          (fromQuantum_B (.alice K Q)).Environment := fun t => ⟨t.1,e t.1 t.2⟩
      let G : (fromQuantum_B (.alice K Q)).Environment →
          (fromQuantum_B (.alice K P)).Environment := fun t => ⟨t.1,d t.1 t.2⟩
      have hA (z : Fin k) (t : (fromQuantum_B (Q z)).Environment) :
          F (G ⟨z,t⟩) = ⟨z,t⟩ ↔ e z (d z t) = t := sigma_same_eq_iff_B z _ _
      refine ⟨F,G,?_,?_,?_⟩
      · rintro ⟨z,t⟩
        exact congrArg (Sigma.mk z) (hed z t)
      · rintro ⟨z,t⟩
        change (fromQuantum_B (Q z)).historyKraus_B t *
            (K.operator z ⊗ₖ (1 : Matrix (Fin b) (Fin b) ℂ)) =
          if F (G ⟨z,t⟩) = ⟨z,t⟩ then
            (fromQuantum_B (P z)).historyKraus_B (d z t) *
              (K.operator z ⊗ₖ (1 : Matrix (Fin b) (Fin b) ℂ)) else 0
        by_cases ht : e z (d z t) = t
        · have hf := (hA z t).mpr ht
          simpa only [if_pos ht,if_pos hf] using congrArg
            (fun M => M * (K.operator z ⊗ₖ (1 : Matrix (Fin b) (Fin b) ℂ))) (hK z t)
        · have hf : ¬ F (G ⟨z,t⟩) = ⟨z,t⟩ := fun hf => ht ((hA z t).mp hf)
          simpa only [if_neg ht,if_neg hf,Matrix.zero_mul] using congrArg
            (fun M => M * (K.operator z ⊗ₖ (1 : Matrix (Fin b) (Fin b) ℂ))) (hK z t)
      · rintro ⟨z,t⟩ ⟨z',t'⟩ ht ht'
        have hs := (hA z t).mp ht
        have hs' := (hA z' t').mp ht'
        by_cases hz : z = z'
        · subst z'
          exact (sigma_same_eq_iff_B
            (A := fun j => (fromQuantum_B (Q j)).comparisonPublicHistory_B) z _ _).trans
            ((hT z t t' hs hs').trans (sigma_same_eq_iff_B
              (A := fun j => (fromQuantum_B (P j)).comparisonPublicHistory_B) z _ _).symm)
        · constructor
          · intro hx
            exact False.elim (hz (Sigma.mk.inj_iff.mp hx).1)
          · intro hx
            exact False.elim (hz (Sigma.mk.inj_iff.mp hx).1)
  | @bob a b bo af bf k m K P Q next ih =>
      choose e d hed hK hT using ih
      let F : (fromQuantum_B (.bob K P)).Environment →
          (fromQuantum_B (.bob K Q)).Environment := fun t => ⟨t.1,e t.1 t.2⟩
      let G : (fromQuantum_B (.bob K Q)).Environment →
          (fromQuantum_B (.bob K P)).Environment := fun t => ⟨t.1,d t.1 t.2⟩
      have hA (z : Fin k) (t : (fromQuantum_B (Q z)).Environment) :
          F (G ⟨z,t⟩) = ⟨z,t⟩ ↔ e z (d z t) = t := sigma_same_eq_iff_B z _ _
      refine ⟨F,G,?_,?_,?_⟩
      · rintro ⟨z,t⟩
        exact congrArg (Sigma.mk z) (hed z t)
      · rintro ⟨z,t⟩
        change (fromQuantum_B (Q z)).historyKraus_B t *
            ((1 : Matrix (Fin a) (Fin a) ℂ) ⊗ₖ K.operator z) =
          if F (G ⟨z,t⟩) = ⟨z,t⟩ then
            (fromQuantum_B (P z)).historyKraus_B (d z t) *
              ((1 : Matrix (Fin a) (Fin a) ℂ) ⊗ₖ K.operator z) else 0
        by_cases ht : e z (d z t) = t
        · have hf := (hA z t).mpr ht
          simpa only [if_pos ht,if_pos hf] using congrArg
            (fun M => M * ((1 : Matrix (Fin a) (Fin a) ℂ) ⊗ₖ K.operator z)) (hK z t)
        · have hf : ¬ F (G ⟨z,t⟩) = ⟨z,t⟩ := fun hf => ht ((hA z t).mp hf)
          simpa only [if_neg ht,if_neg hf,Matrix.zero_mul] using congrArg
            (fun M => M * ((1 : Matrix (Fin a) (Fin a) ℂ) ⊗ₖ K.operator z)) (hK z t)
      · rintro ⟨z,t⟩ ⟨z',t'⟩ ht ht'
        have hs := (hA z t).mp ht
        have hs' := (hA z' t').mp ht'
        by_cases hz : z = z'
        · subst z'
          exact (sigma_same_eq_iff_B
            (A := fun j => (fromQuantum_B (Q j)).comparisonPublicHistory_B) z _ _).trans
            ((hT z t t' hs hs').trans (sigma_same_eq_iff_B
              (A := fun j => (fromQuantum_B (P j)).comparisonPublicHistory_B) z _ _).symm)
        · constructor
          · intro hx
            exact False.elim (hz (Sigma.mk.inj_iff.mp hx).1)
          · intro hx
            exact False.elim (hz (Sigma.mk.inj_iff.mp hx).1)
  | call P Q next ih =>
      rcases ih with ⟨e,d,hed,hK,hT⟩
      let F : (fromQuantum_B (.call P)).Environment → (fromQuantum_B (.call Q)).Environment :=
        fun t => (t.1,e t.2)
      let G : (fromQuantum_B (.call Q)).Environment → (fromQuantum_B (.call P)).Environment :=
        fun t => (t.1,d t.2)
      have hA (z : Fin 2) (t : (fromQuantum_B Q).Environment) :
          F (G (z,t)) = (z,t) ↔ e (d t) = t := by
        constructor
        · intro hx
          exact congrArg Prod.snd hx
        · intro hx
          exact congrArg (fun u => (z,u)) hx
      refine ⟨F,G,?_,?_,?_⟩
      · rintro ⟨z,t⟩
        exact congrArg (fun u => (z,u)) (hed t)
      · rintro ⟨z,t⟩
        change (fromQuantum_B Q).historyKraus_B t * transferKraus p _ _ z =
          if F (G (z,t)) = (z,t) then
            (fromQuantum_B P).historyKraus_B (d t) * transferKraus p _ _ z else 0
        by_cases ht : e (d t) = t
        · have hf := (hA z t).mpr ht
          rw [if_pos hf]
          exact congrArg (fun M => M * transferKraus p _ _ z) ((hK t).trans (if_pos ht))
        · have hf : ¬ F (G (z,t)) = (z,t) := fun hf => ht ((hA z t).mp hf)
          rw [if_neg hf]
          exact (congrArg (fun M => M * transferKraus p _ _ z)
            ((hK t).trans (if_neg ht))).trans (Matrix.zero_mul _)
      · rintro ⟨z,t⟩ ⟨z',t'⟩ ht ht'
        exact hT t t' ((hA z t).mp ht) ((hA z' t').mp ht')

theorem padding_priorEve_entry_B {E : Type*} {p : ℝ} {a b af bf m : ℕ}
    {P Q : FiniteProtocol p a b af bf} (h : UniformPaddingDerivationB p m P Q) :
    ∃ f : (fromQuantum_B P).Environment → (fromQuantum_B Q).Environment,
    ∃ g : (fromQuantum_B Q).Environment → (fromQuantum_B P).Environment,
      Function.LeftInverse g f ∧
    ∀ (ρ : Matrix ((Fin a × Fin b) × E) ((Fin a × Fin b) × E) ℂ)
      (x y : Fin af × Fin bf) (t t' : (fromQuantum_B Q).Environment) (e e' : E),
      PublicHistory.localPriorEveMatrix_B (fromQuantum_B Q) ρ (x,(t,e)) (y,(t',e')) =
        if f (g t) = t ∧ f (g t') = t' then
          PublicHistory.localPriorEveMatrix_B (fromQuantum_B P) ρ
            (x,(g t,e)) (y,(g t',e')) else 0 := by
  rcases padding_transport_history_B h with ⟨f,g,hfg,hK,hT⟩
  refine ⟨f,g,hfg,?_⟩
  intro ρ x y t t' e e'
  change (fromQuantum_B Q).fullOutput _ (x,t) (y,t') =
    if f (g t) = t ∧ f (g t') = t' then (fromQuantum_B P).fullOutput _ (x,g t) (y,g t') else 0
  rw [fullOutput_historyKraus_apply_B,fullOutput_historyKraus_apply_B,hK t,hK t']
  by_cases ht : f (g t) = t
  · by_cases ht' : f (g t') = t'
    · simp only [if_pos ht,if_pos ht',if_pos (And.intro ht ht'),hT t t' ht ht']
    · simp [ht,ht']
  · simp [ht]

def historyWithOldEveEmbedding_B {A H J E : Type*} (f : H → J) : A × (H × E) → A × (J × E) :=
  fun x => (x.1,(f x.2.1,x.2.2))

theorem historyWithOldEve_leftInverse_B {A H J E : Type*}
    (f : H → J) (g : J → H) (hfg : Function.LeftInverse g f) :
    Function.LeftInverse (historyWithOldEveEmbedding_B (A := A) (E := E) g)
      (historyWithOldEveEmbedding_B f) := by
  intro x
  exact congrArg (fun t => (x.1,(t,x.2.2))) (hfg x.2.1)

theorem historyWithOldEve_image_iff_B {A H J E : Type*}
    (f : H → J) (g : J → H) (x : A × (J × E)) :
    historyWithOldEveEmbedding_B f (historyWithOldEveEmbedding_B g x) = x ↔ f (g x.2.1) = x.2.1 := by
  constructor
  · intro hx
    exact congrArg (fun t => t.2.1) hx
  · intro hx
    exact congrArg (fun t => (x.1,(t,x.2.2))) hx

theorem padding_priorEve_isometry_B {E : Type*} [Fintype E] [DecidableEq E]
    {p : ℝ} {a b af bf m : ℕ} {P Q : FiniteProtocol p a b af bf}
    (h : UniformPaddingDerivationB p m P Q) :
    ∃ f : (fromQuantum_B P).Environment → (fromQuantum_B Q).Environment,
    ∃ g : (fromQuantum_B Q).Environment → (fromQuantum_B P).Environment,
      Function.LeftInverse g f ∧
      let V := PublicHistory.basisEmbedding_B
        (historyWithOldEveEmbedding_B (A := Fin af × Fin bf) (E := E) f)
      Vᴴ * V = 1 ∧
      ∀ ρ : Matrix ((Fin a × Fin b) × E) ((Fin a × Fin b) × E) ℂ,
        PublicHistory.localPriorEveMatrix_B (fromQuantum_B Q) ρ =
          V * PublicHistory.localPriorEveMatrix_B (fromQuantum_B P) ρ * Vᴴ := by
  rcases padding_priorEve_entry_B (E := E) h with ⟨f,g,hfg,hO⟩
  refine ⟨f,g,hfg,?_,?_⟩
  · exact PublicHistory.basisEmbedding_gram_B _
      (historyWithOldEve_leftInverse_B (A := Fin af × Fin bf) (E := E) f g hfg).injective
  · intro ρ
    ext x y
    rw [PublicHistory.basisEmbedding_sandwich_apply_B _
      (historyWithOldEveEmbedding_B (A := Fin af × Fin bf) (E := E) g)
      (historyWithOldEve_leftInverse_B f g hfg)]
    simp only [historyWithOldEve_image_iff_B]
    exact hO ρ x.1 y.1 x.2.1 y.2.1 x.2.2 y.2.2

theorem padding_readout_entry_B {E K : Type*} [Fintype E] [DecidableEq E]
    [Fintype K] [DecidableEq K] {p : ℝ} {a b af bf m : ℕ}
    {P Q : FiniteProtocol p a b af bf} (h : UniformPaddingDerivationB p m P Q) :
    ∃ f : (fromQuantum_B P).Environment → (fromQuantum_B Q).Environment,
    ∃ g : (fromQuantum_B Q).Environment → (fromQuantum_B P).Environment,
      Function.LeftInverse g f ∧
    ∀ (label : Fin af × Fin bf → K)
      (ρ : Matrix ((Fin a × Fin b) × E) ((Fin a × Fin b) × E) ℂ)
      (k k' : K) (t t' : (fromQuantum_B Q).Environment) (e e' : E),
      ((basisReadoutChannel label).withRightMemory ((fromQuantum_B Q).Environment × E)).eval
          (PublicHistory.localPriorEveMatrix_B (fromQuantum_B Q) ρ) (k,(t,e)) (k',(t',e')) =
        if f (g t) = t ∧ f (g t') = t' then
          ((basisReadoutChannel label).withRightMemory ((fromQuantum_B P).Environment × E)).eval
            (PublicHistory.localPriorEveMatrix_B (fromQuantum_B P) ρ)
              (k,(g t,e)) (k',(g t',e')) else 0 := by
  rcases padding_priorEve_entry_B (E := E) h with ⟨f,g,hfg,hO⟩
  refine ⟨f,g,hfg,?_⟩
  intro label ρ k k' t t' e e'
  rw [PublicHistory.reference_basisReadout_apply_B,PublicHistory.reference_basisReadout_apply_B]
  simp_rw [hO]
  by_cases ht : f (g t) = t ∧ f (g t') = t'
  · simp only [if_pos ht]
  · simp only [if_neg ht,ite_self,Finset.sum_const_zero]

theorem padding_readout_isometry_B {E K : Type*} [Fintype E] [DecidableEq E]
    [Fintype K] [DecidableEq K] {p : ℝ} {a b af bf m : ℕ}
    {P Q : FiniteProtocol p a b af bf} (h : UniformPaddingDerivationB p m P Q) :
    ∃ f : (fromQuantum_B P).Environment → (fromQuantum_B Q).Environment,
    ∃ g : (fromQuantum_B Q).Environment → (fromQuantum_B P).Environment,
      Function.LeftInverse g f ∧
      let V := PublicHistory.basisEmbedding_B
        (historyWithOldEveEmbedding_B (A := K) (E := E) f)
      Vᴴ * V = 1 ∧
      ∀ (label : Fin af × Fin bf → K)
        (ρ : Matrix ((Fin a × Fin b) × E) ((Fin a × Fin b) × E) ℂ),
        ((basisReadoutChannel label).withRightMemory ((fromQuantum_B Q).Environment × E)).eval
            (PublicHistory.localPriorEveMatrix_B (fromQuantum_B Q) ρ) =
          V * ((basisReadoutChannel label).withRightMemory ((fromQuantum_B P).Environment × E)).eval
            (PublicHistory.localPriorEveMatrix_B (fromQuantum_B P) ρ) * Vᴴ := by
  rcases padding_readout_entry_B (E := E) (K := K) h with ⟨f,g,hfg,hO⟩
  refine ⟨f,g,hfg,?_,?_⟩
  · exact PublicHistory.basisEmbedding_gram_B _
      (historyWithOldEve_leftInverse_B (A := K) (E := E) f g hfg).injective
  · intro label ρ
    ext x y
    rw [PublicHistory.basisEmbedding_sandwich_apply_B _
      (historyWithOldEveEmbedding_B (A := K) (E := E) g)
      (historyWithOldEve_leftInverse_B f g hfg)]
    simp only [historyWithOldEve_image_iff_B]
    exact hO label ρ x.1 y.1 x.2.1 y.2.1 x.2.2 y.2.2

theorem exists_paddedLanes_physical_priorEve_B {E : Type*} [Fintype E] [DecidableEq E]
    {p : ℝ} {a b af bf : ℕ} (P : FiniteProtocol p a b af bf)
    (m : ℕ) (hP : P.calls ≤ m) (n : ℕ) :
    ∃ Q : FiniteProtocol p a b af bf,
      UniformPaddingDerivationB p m P Q ∧ Q.calls ≤ m ∧ Q.UniformCallsB m ∧
    ∃ f : (fromQuantum_B P).Environment → (fromQuantum_B Q).Environment,
    ∃ g : (fromQuantum_B Q).Environment → (fromQuantum_B P).Environment,
      Function.LeftInverse g f ∧
      let V := PublicHistory.basisEmbedding_B
        (historyWithOldEveEmbedding_B (A := Fin af × Fin bf) (E := E) f)
      Vᴴ * V = 1 ∧
      (∀ ρ : Matrix ((Fin a × Fin b) × E) ((Fin a × Fin b) × E) ℂ,
        PublicHistory.localPriorEveMatrix_B (fromQuantum_B Q) ρ =
          V * PublicHistory.localPriorEveMatrix_B (fromQuantum_B P) ρ * Vᴴ) ∧
    ∃ R : FiniteBlockProtocolB p (n + 1) (lanePowerDimB n a) (lanePowerDimB n b)
        (lanePowerDimB n af) (lanePowerDimB n bf),
      IndependentLanesDerivationB p Q n R ∧ R.calls ≤ m ∧
        (blockExpansion_B R).calls ≤ (n + 1) * m ∧
    ∃ eH : (blockExpansion_B R).Environment ≃ Register (fromQuantum_B Q).Environment (n + 1),
    ∃ eT : (blockExpansion_B R).comparisonPublicHistory_B ≃
        Register (fromQuantum_B Q).comparisonPublicHistory_B (n + 1),
      (∀ t, (blockExpansion_B R).historyKraus_B t = laneHistoryKraus_B Q n (eH t)) ∧
      (∀ t, eT ((blockExpansion_B R).publicTranscript_B t) =
        lanePublicTranscript_B Q n (eH t)) ∧
      ∀ ρ : Matrix ((Fin a × Fin b) × E) ((Fin a × Fin b) × E) ℂ,
        PublicHistory.localPriorEveMatrix_B (blockExpansion_B R) (lanePriorMatrix_B ρ n) =
          (matrix (V * PublicHistory.localPriorEveMatrix_B (fromQuantum_B P) ρ * Vᴴ)
            (n + 1)).submatrix (laneOutputEveEquiv_B E eH) (laneOutputEveEquiv_B E eH) := by
  rcases P.exists_uniform_padding_with_derivationB m hP with ⟨Q,hQ,hQC,hQU,hQO⟩
  rcases padding_priorEve_isometry_B (E := E) hQ with ⟨f,g,hfg,hV,hO⟩
  rcases exists_uniformLanes_priorEve_B (E := E) Q hQU n with
    ⟨R,hR,hRC,hRN,eH,eT,hK,hT,hRO⟩
  refine ⟨Q,hQ,hQC,hQU,f,g,hfg,hV,hO,R,hR,hRC,hRN,eH,eT,hK,hT,?_⟩
  intro ρ
  exact (hRO ρ).trans (congrArg
    (fun M => (matrix M (n + 1)).submatrix (laneOutputEveEquiv_B E eH) (laneOutputEveEquiv_B E eH))
    (hO ρ))

end QuantumProver.AmplitudeDamping.SecretKey.IdleEvePadding

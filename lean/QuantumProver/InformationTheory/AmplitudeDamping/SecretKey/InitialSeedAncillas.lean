import QuantumProver.InformationTheory.AmplitudeDamping.SecretKey.InitialSeedPreparation

set_option autoImplicit false

noncomputable section

open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix Kronecker

namespace QuantumProver.AmplitudeDamping.SecretKey.InitialSeedAncillas

open InitialSeed PhysicalProtocol PhysicalProtocol.FiniteKeyProtocol

theorem local_isometry_resource_le {a ao b : ℕ}
    (ρ : Density (Fin a × Fin b)) (V : Matrix (Fin ao) (Fin a) ℂ)
    (hV : Vᴴ * V = 1) {α : ℝ} (hα : 1 < α) :
    QuantumProver.AmplitudeDamping.FiniteModel.sandwichedEntanglement α ao b
      ((V ⊗ₖ (1 : Matrix (Fin b) (Fin b) ℂ)) * ρ.mat *
        (V ⊗ₖ (1 : Matrix (Fin b) (Fin b) ℂ))ᴴ) ≤
      QuantumProver.AmplitudeDamping.FiniteModel.sandwichedEntanglement α a b ρ.mat := by
  let W := V ⊗ₖ (1 : Matrix (Fin b) (Fin b) ℂ)
  have hW : Wᴴ * W = 1 := by
    dsimp only [W]
    rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
      ← Matrix.mul_kronecker_mul, hV, Matrix.one_mul, Matrix.one_kronecker_one]
  unfold QuantumProver.AmplitudeDamping.FiniteModel.sandwichedEntanglement
  apply le_sInf
  rintro q ⟨σ, ⟨hσ, hsep⟩, rfl⟩
  by_cases hs : QuantumProver.AmplitudeDamping.FiniteModel.SupportLE ρ.mat σ
  · rw [← sandwichedDivergence_isometry W hW ρ.positive hσ.1 hs hα]
    apply sInf_le
    refine ⟨W * σ * Wᴴ, ?_, rfl⟩
    exact ⟨⟨hσ.1.mul_mul_conjTranspose_same W,
      (trace_isometry W hW σ).trans hσ.2⟩,
        normalizedSeparable_local_isometry V hV hsep⟩
  · simp only [QuantumProver.AmplitudeDamping.FiniteModel.sandwichedDivergence, if_neg hs]
    exact le_top

def labelCopyMatrix {a c : ℕ} (label : Fin a → Fin c) :
    Matrix (Fin (c * a)) (Fin a) ℂ :=
  PublicHistory.basisEmbedding_B
    (fun x => (privateAliceLocalEquiv c a).symm (label x,x))

theorem labelCopyMatrix_isometry {a c : ℕ} (label : Fin a → Fin c) :
    (labelCopyMatrix label)ᴴ * labelCopyMatrix label = 1 := by
  apply PublicHistory.basisEmbedding_gram_B
  intro x y h
  exact congrArg Prod.snd ((privateAliceLocalEquiv c a).symm.injective h)

def labelCopyChannel {a c : ℕ} (label : Fin a → Fin c) :
    KrausChannel (Fin a) (Fin (c * a)) Unit where
  op _ := labelCopyMatrix label
  complete := by simpa only [Fintype.sum_unique] using labelCopyMatrix_isometry label

def privateLabelDensity {a b c : ℕ} (label : Fin a → Fin c)
    (ρ : Density (Fin a × Fin b)) : Density (Fin (c * a) × Fin b) :=
  ((labelCopyChannel label).withRightMemory (Fin b)).onDensity ρ

theorem privateLabelDensity_matrix {a b c : ℕ} (label : Fin a → Fin c)
    (ρ : Density (Fin a × Fin b)) :
    (privateLabelDensity label ρ).mat =
      (labelCopyMatrix label ⊗ₖ (1 : Matrix (Fin b) (Fin b) ℂ)) * ρ.mat *
        (labelCopyMatrix label ⊗ₖ (1 : Matrix (Fin b) (Fin b) ℂ))ᴴ := by
  simp only [privateLabelDensity, KrausChannel.onDensity, KrausChannel.eval,
    KrausChannel.withRightMemory, labelCopyChannel, Fintype.sum_unique]

theorem privateLabelDensity_resource_le {a b c : ℕ} (label : Fin a → Fin c)
    (ρ : Density (Fin a × Fin b)) {α : ℝ} (hα : 1 < α) :
    QuantumProver.AmplitudeDamping.FiniteModel.sandwichedEntanglement α (c * a) b
      (privateLabelDensity label ρ).mat ≤
        QuantumProver.AmplitudeDamping.FiniteModel.sandwichedEntanglement α a b ρ.mat := by
  rw [privateLabelDensity_matrix]
  exact local_isometry_resource_le ρ _ (labelCopyMatrix_isometry label) hα

def coherentSeedAncillas {d c e : ℕ} (a : ProbabilityLaw (Fin d))
    (ρA : Density (Fin c)) (ρB : Density (Fin e)) :
    Density (Fin (d * c) × Fin (d * e)) :=
  (a.coherentSeedDensity.tensor (ρA.tensor ρB)).relabel
    (QuantumProver.AmplitudeDamping.FiniteModel.tensorLabEquiv d d c e)

def copiedSeedAncillas {d c e : ℕ} (a : ProbabilityLaw (Fin d))
    (ρA : Density (Fin c)) (ρB : Density (Fin e)) :
    Density (Fin (d * c) × Fin (d * e)) :=
  (a.copiedDensity.tensor (ρA.tensor ρB)).relabel
    (QuantumProver.AmplitudeDamping.FiniteModel.tensorLabEquiv d d c e)

theorem coherentSeedAncillas_matrix {d c e : ℕ} (a : ProbabilityLaw (Fin d))
    (ρA : Density (Fin c)) (ρB : Density (Fin e)) :
    (coherentSeedAncillas a ρA ρB).mat =
      QuantumProver.AmplitudeDamping.FiniteModel.tensorOnLabCut a.coherentSeedMatrix (ρA.tensor ρB).mat := rfl

def retainedSeedAncillas {d c e : ℕ} (a : ProbabilityLaw (Fin d))
    (ρA : Density (Fin c)) (ρB : Density (Fin e)) :
    Density (Fin (d * (d * c)) × Fin (d * e)) :=
  privateLabelDensity (fun x : Fin (d * c) => (privateAliceLocalEquiv d c x).1)
    (coherentSeedAncillas a ρA ρB)

theorem retainedSeedAncillas_resource_le {d c e : ℕ} (a : ProbabilityLaw (Fin d))
    (ρA : Density (Fin c)) (ρB : Density (Fin e)) {z : ℝ} (hz : 0 < z) (hz1 : z < 1) :
    QuantumProver.AmplitudeDamping.FiniteModel.sandwichedEntanglement (1 / (1 - z))
      (d * (d * c)) (d * e) (retainedSeedAncillas a ρA ρB).mat ≤
        (a.renyiSeedCharge z : EReal) := by
  have hα : 1 < 1 / (1 - z) :=
    (lt_div_iff₀ (sub_pos.mpr hz1)).mpr (by linarith)
  apply (privateLabelDensity_resource_le _ _ hα).trans
  rw [coherentSeedAncillas_matrix]
  exact a.coherentSeed_entanglement_le_with_local_ancillas ρA ρB hz hz1

theorem retainedSeedAncillas_resource_le_bits {d c e : ℕ} [Nonempty (Fin d)]
    (a : ProbabilityLaw (Fin d)) (ρA : Density (Fin c)) (ρB : Density (Fin e))
    {z k : ℝ} (hz : 0 < z) (hz1 : z < 1) (hk : (d : ℝ) ≤ 2 ^ k) :
    QuantumProver.AmplitudeDamping.FiniteModel.sandwichedEntanglement (1 / (1 - z))
      (d * (d * c)) (d * e) (retainedSeedAncillas a ρA ρB).mat ≤ (k : EReal) := by
  apply (retainedSeedAncillas_resource_le a ρA ρB hz hz1).trans
  exact_mod_cast a.renyiSeedCharge_le_bits z k hz (by simpa using hk)

def privateBobJointEquiv (c a b : ℕ) :
    (Fin a × Fin (c * b)) ≃ (Fin c × (Fin a × Fin b)) where
  toFun x := ((privateAliceLocalEquiv c b x.2).1,
    (x.1, (privateAliceLocalEquiv c b x.2).2))
  invFun x := (x.2.1, (privateAliceLocalEquiv c b).symm (x.1,x.2.2))
  left_inv x := by simp only [Prod.mk.eta, Equiv.symm_apply_apply]
  right_inv x := by simp only [Equiv.apply_symm_apply]

theorem privateBobJointEquiv_apply (c a b : ℕ) (x : Fin a × Fin (c * b)) :
    privateBobJointEquiv c a b x = ((privateAliceLocalEquiv c b x.2).1,
      (x.1, (privateAliceLocalEquiv c b x.2).2)) := rfl

def privateBobCallChartEquiv (c b : ℕ) : Fin (2 * (c * b)) ≃ Fin (c * (2 * b)) :=
  (QuantumProver.AmplitudeDamping.FiniteModel.aliceSpectatorPortEquivB c b).trans
    (privateAliceLocalEquiv c (2 * b)).symm

def privateBobCallChart (c b : ℕ) :
    KrausChannel (Fin (2 * (c * b))) (Fin (c * (2 * b))) (Fin 1) where
  op _ := PublicHistory.basisEmbedding_B (privateBobCallChartEquiv c b)
  complete := by
    simpa only [Fin.sum_univ_one] using
      PublicHistory.basisEmbedding_gram_B (privateBobCallChartEquiv c b)
        (privateBobCallChartEquiv c b).injective

def withPrivateBob {p : ℝ} {a b af bf : ℕ} (c : ℕ)
    (P : FiniteKeyProtocol p a b af bf) : FiniteKeyProtocol p a (c * b) af (c * bf) :=
  match P with
  | .done a b => .done a (c * b)
  | .alice C next => .alice C fun z => withPrivateBob c (next z)
  | .bob C next => .bob (privateAliceInstrument c C) fun z => withPrivateBob c (next z)
  | .call (b := b₀) next => .call (.bob (privateBobCallChart c b₀)
      fun _ => withPrivateBob c next)

theorem withPrivateBob_calls {p : ℝ} {a b af bf : ℕ} (c : ℕ)
    (P : FiniteKeyProtocol p a b af bf) : (withPrivateBob c P).calls = P.calls := by
  induction P with
  | done a b => rfl
  | alice C next ih => simp only [withPrivateBob, calls, ih]
  | bob C next ih => simp only [withPrivateBob, calls, ih]
  | call next ih => simp [withPrivateBob, calls, ih]

def privateBobEnvironmentEquiv {p : ℝ} {a b af bf : ℕ} (c : ℕ)
    (P : FiniteKeyProtocol p a b af bf) : (withPrivateBob c P).Environment ≃ P.Environment :=
  match P with
  | .done _ _ => Equiv.refl Unit
  | .alice _ next => Equiv.sigmaCongrRight fun z => privateBobEnvironmentEquiv c (next z)
  | .bob _ next => Equiv.sigmaCongrRight fun z => privateBobEnvironmentEquiv c (next z)
  | .call next =>
      { toFun := fun h => (h.1, privateBobEnvironmentEquiv c next h.2.2)
        invFun := fun h => (h.1, ⟨0, (privateBobEnvironmentEquiv c next).symm h.2⟩)
        left_inv := by
          intro h
          rcases h with ⟨q,z,t⟩
          have hz : z = (0 : Fin 1) := Subsingleton.elim _ _
          subst z
          apply Prod.ext
          · rfl
          ·
            exact congrArg (fun u : (withPrivateBob c next).Environment =>
              (⟨0,u⟩ : (z : Fin 1) × (withPrivateBob c next).Environment))
                ((privateBobEnvironmentEquiv c next).symm_apply_apply t)
        right_inv := by
          intro h
          rcases h with ⟨q,t⟩
          change (q, privateBobEnvironmentEquiv c next
            ((privateBobEnvironmentEquiv c next).symm t)) = (q,t)
          rw [Equiv.apply_symm_apply] }

def privateBobPublicEquiv {p : ℝ} {a b af bf : ℕ} (c : ℕ)
    (P : FiniteKeyProtocol p a b af bf) :
    (withPrivateBob c P).comparisonPublicHistory_B ≃ P.comparisonPublicHistory_B :=
  match P with
  | .done _ _ => Equiv.refl Unit
  | .alice _ next => Equiv.sigmaCongrRight fun z => privateBobPublicEquiv c (next z)
  | .bob _ next => Equiv.sigmaCongrRight fun z => privateBobPublicEquiv c (next z)
  | .call next =>
      { toFun := fun h => privateBobPublicEquiv c next h.2
        invFun := fun h => ⟨0, (privateBobPublicEquiv c next).symm h⟩
        left_inv := by
          intro h
          rcases h with ⟨z,t⟩
          have hz : z = (0 : Fin 1) := Subsingleton.elim _ _
          subst z
          exact congrArg (fun u : (withPrivateBob c next).comparisonPublicHistory_B =>
            (⟨0,u⟩ : (z : Fin 1) × (withPrivateBob c next).comparisonPublicHistory_B))
              ((privateBobPublicEquiv c next).symm_apply_apply t)
        right_inv := by intro h; exact (privateBobPublicEquiv c next).apply_symm_apply h }

theorem privateBob_publicTranscript {p : ℝ} {a b af bf : ℕ} (c : ℕ)
    (P : FiniteKeyProtocol p a b af bf) : ∀ h,
    privateBobPublicEquiv c P ((withPrivateBob c P).publicTranscript_B h) =
      P.publicTranscript_B (privateBobEnvironmentEquiv c P h) := by
  induction P with
  | done a b => intro h; rfl
  | @alice a b ao af bf k C next ih =>
      intro h
      rcases h with ⟨z,t⟩
      change Sigma.mk (β := fun w : Fin k => (next w).comparisonPublicHistory_B) z
        (privateBobPublicEquiv c (next z) ((withPrivateBob c (next z)).publicTranscript_B t)) =
          Sigma.mk (β := fun w : Fin k => (next w).comparisonPublicHistory_B) z
            ((next z).publicTranscript_B (privateBobEnvironmentEquiv c (next z) t))
      rw [ih z t]
  | @bob a b bo af bf k C next ih =>
      intro h
      rcases h with ⟨z,t⟩
      change Sigma.mk (β := fun w : Fin k => (next w).comparisonPublicHistory_B) z
        (privateBobPublicEquiv c (next z) ((withPrivateBob c (next z)).publicTranscript_B t)) =
          Sigma.mk (β := fun w : Fin k => (next w).comparisonPublicHistory_B) z
            ((next z).publicTranscript_B (privateBobEnvironmentEquiv c (next z) t))
      rw [ih z t]
  | call next ih =>
      intro h
      rcases h with ⟨q,z,t⟩
      exact ih t

theorem privateBob_public_eq_iff {p : ℝ} {a b af bf : ℕ} (c : ℕ)
    (P : FiniteKeyProtocol p a b af bf) (h h' : (withPrivateBob c P).Environment) :
    (withPrivateBob c P).publicTranscript_B h = (withPrivateBob c P).publicTranscript_B h' ↔
      P.publicTranscript_B (privateBobEnvironmentEquiv c P h) =
        P.publicTranscript_B (privateBobEnvironmentEquiv c P h') := by
  rw [← (privateBobPublicEquiv c P).injective.eq_iff,
    privateBob_publicTranscript, privateBob_publicTranscript]

theorem privateBob_alice_step {a ao b k : ℕ} (c : ℕ)
    (C : KrausChannel (Fin a) (Fin ao) (Fin k)) (z : Fin k) :
    C.op z ⊗ₖ (1 : Matrix (Fin (c * b)) (Fin (c * b)) ℂ) =
      ((1 : Matrix (Fin c) (Fin c) ℂ) ⊗ₖ
        (C.op z ⊗ₖ (1 : Matrix (Fin b) (Fin b) ℂ))).submatrix
          (privateBobJointEquiv c ao b) (privateBobJointEquiv c a b) := by
  have hI : ((1 : Matrix (Fin c) (Fin c) ℂ) ⊗ₖ
      (1 : Matrix (Fin b) (Fin b) ℂ)).submatrix
        (privateAliceLocalEquiv c b) (privateAliceLocalEquiv c b) = 1 := by
    rw [Matrix.one_kronecker_one, Matrix.submatrix_one_equiv]
  rw [← hI]
  ext x y
  simp only [Matrix.submatrix_apply, Matrix.kroneckerMap_apply, privateBobJointEquiv_apply]
  ring

theorem privateBob_bob_step {a b bo k : ℕ} (c : ℕ)
    (C : KrausChannel (Fin b) (Fin bo) (Fin k)) (z : Fin k) :
    (1 : Matrix (Fin a) (Fin a) ℂ) ⊗ₖ (privateAliceInstrument c C).op z =
      ((1 : Matrix (Fin c) (Fin c) ℂ) ⊗ₖ
        ((1 : Matrix (Fin a) (Fin a) ℂ) ⊗ₖ C.op z)).submatrix
          (privateBobJointEquiv c a bo) (privateBobJointEquiv c a b) := by
  ext x y
  simp only [privateAliceInstrument, KrausChannel.relabel_B, KrausChannel.withMemory,
    Matrix.submatrix_apply, Matrix.kroneckerMap_apply, privateBobJointEquiv_apply]
  ring

theorem identity_tensor_basisEmbedding {R S A : Type*}
    [Fintype R] [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]
    (f : R → S) :
    (1 : Matrix A A ℂ) ⊗ₖ PublicHistory.basisEmbedding_B f =
      PublicHistory.basisEmbedding_B (fun x : A × R => (x.1,f x.2)) := by
  ext x y
  rcases x with ⟨a,s⟩
  rcases y with ⟨a',r⟩
  by_cases ha : a = a' <;>
    simp [PublicHistory.basisEmbedding_B, Matrix.kroneckerMap_apply,
      Matrix.one_apply, Prod.mk.injEq, ha]

theorem basisEmbedding_equiv_mul {R S T : Type*} [Fintype R] [DecidableEq S]
    (f : R ≃ S) (K : Matrix R T ℂ) :
    PublicHistory.basisEmbedding_B f * K = K.submatrix f.symm id := by
  ext s t
  classical
  have heq (j : R) : s = f j ↔ f.symm s = j := by
    constructor
    · intro h; rw [h, Equiv.symm_apply_apply]
    · intro h; rw [← h, Equiv.apply_symm_apply]
  simp [Matrix.mul_apply, PublicHistory.basisEmbedding_B, Matrix.submatrix_apply,
    heq, ite_mul]

theorem finProd_divNat {m n : ℕ} (x : Fin m) (y : Fin n) :
    (finProdFinEquiv (x,y)).divNat = x :=
  congrArg Prod.fst ((finProdFinEquiv : Fin m × Fin n ≃ Fin (m * n)).symm_apply_apply (x,y))

theorem finProd_modNat {m n : ℕ} (x : Fin m) (y : Fin n) :
    (finProdFinEquiv (x,y)).modNat = y :=
  congrArg Prod.snd ((finProdFinEquiv : Fin m × Fin n ≃ Fin (m * n)).symm_apply_apply (x,y))

theorem privateBob_call_step (p : ℝ) (c a b : ℕ) (z : Fin 2) :
    ((1 : Matrix (Fin a) (Fin a) ℂ) ⊗ₖ (privateBobCallChart c b).op 0) *
      transferKraus p a (c * b) z =
      ((1 : Matrix (Fin c) (Fin c) ℂ) ⊗ₖ transferKraus p a b z).submatrix
        (privateBobJointEquiv c a (2 * b)) (privateBobJointEquiv c (2 * a) b) := by
  simp only [privateBobCallChart]
  rw [identity_tensor_basisEmbedding]
  have he := basisEmbedding_equiv_mul
    ((Equiv.refl (Fin a)).prodCongr (privateBobCallChartEquiv c b))
    (transferKraus p a (c * b) z)
  have he' : PublicHistory.basisEmbedding_B
      (fun x : Fin a × Fin (2 * (c * b)) => (x.1, privateBobCallChartEquiv c b x.2)) *
        transferKraus p a (c * b) z =
      (transferKraus p a (c * b) z).submatrix
        ((Equiv.refl (Fin a)).prodCongr (privateBobCallChartEquiv c b)).symm id := by
    have hf : (⇑((Equiv.refl (Fin a)).prodCongr (privateBobCallChartEquiv c b))) =
        (fun x : Fin a × Fin (2 * (c * b)) =>
          (x.1, privateBobCallChartEquiv c b x.2)) := by
      funext x
      rfl
    rw [hf] at he
    exact he
  rw [he']
  ext x y
  rcases x with ⟨x,v⟩
  rcases y with ⟨u,w⟩
  obtain ⟨⟨r,v⟩, rfl⟩ := (privateAliceLocalEquiv c (2 * b)).symm.surjective v
  obtain ⟨⟨r',w⟩, rfl⟩ := (privateAliceLocalEquiv c b).symm.surjective w
  obtain ⟨⟨q,v⟩, rfl⟩ := (splitQubit b).symm.surjective v
  by_cases hR : r = r' <;> by_cases hA : x = (splitQubit a u).2 <;>
    by_cases hB : v = w <;>
    simp [transferKraus, privateBobCallChartEquiv, privateBobJointEquiv_apply,
      privateAliceLocalEquiv, QuantumProver.AmplitudeDamping.FiniteModel.aliceSpectatorPortEquivB,
      QuantumProver.AmplitudeDamping.FiniteModel.spectatorPortSwapEquivB,
      QuantumProver.AmplitudeDamping.FiniteModel.splitQubit, splitQubit, Matrix.submatrix_apply,
      Matrix.kroneckerMap_apply, Matrix.one_apply, Equiv.trans_apply, hR, hA, hB,
      Prod.mk.injEq, mul_ite, ite_mul, finProd_divNat, finProd_modNat]

theorem withPrivateBob_historyKraus {p : ℝ} {a b af bf : ℕ} (c : ℕ)
    (P : FiniteKeyProtocol p a b af bf) : ∀ h,
    (withPrivateBob c P).historyKraus_B h =
      ((1 : Matrix (Fin c) (Fin c) ℂ) ⊗ₖ
        P.historyKraus_B (privateBobEnvironmentEquiv c P h)).submatrix
          (privateBobJointEquiv c af bf) (privateBobJointEquiv c a b) := by
  induction P with
  | done a b =>
      intro h
      change 1 = ((1 : Matrix (Fin c) (Fin c) ℂ) ⊗ₖ
        (1 : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ)).submatrix _ _
      rw [Matrix.one_kronecker_one, Matrix.submatrix_one_equiv]
  | @alice a b ao af bf k C next ih =>
      intro h
      rcases h with ⟨z,t⟩
      change (withPrivateBob c (next z)).historyKraus_B t *
        (C.op z ⊗ₖ (1 : Matrix (Fin (c * b)) (Fin (c * b)) ℂ)) =
          ((1 : Matrix (Fin c) (Fin c) ℂ) ⊗ₖ
            ((next z).historyKraus_B (privateBobEnvironmentEquiv c (next z) t) *
              (C.op z ⊗ₖ (1 : Matrix (Fin b) (Fin b) ℂ)))).submatrix _ _
      rw [ih z t, privateBob_alice_step, Matrix.submatrix_mul_equiv,
        ← Matrix.mul_kronecker_mul, Matrix.one_mul]
  | @bob a b bo af bf k C next ih =>
      intro h
      rcases h with ⟨z,t⟩
      change (withPrivateBob c (next z)).historyKraus_B t *
        ((1 : Matrix (Fin a) (Fin a) ℂ) ⊗ₖ (privateAliceInstrument c C).op z) =
          ((1 : Matrix (Fin c) (Fin c) ℂ) ⊗ₖ
            ((next z).historyKraus_B (privateBobEnvironmentEquiv c (next z) t) *
              ((1 : Matrix (Fin a) (Fin a) ℂ) ⊗ₖ C.op z))).submatrix _ _
      rw [ih z t, privateBob_bob_step, Matrix.submatrix_mul_equiv,
        ← Matrix.mul_kronecker_mul, Matrix.one_mul]
  | @call a b af bf next ih =>
      intro h
      rcases h with ⟨z,u,t⟩
      change ((withPrivateBob c next).historyKraus_B t *
        ((1 : Matrix (Fin a) (Fin a) ℂ) ⊗ₖ (privateBobCallChart c b).op 0)) *
        transferKraus p a (c * b) z =
          ((1 : Matrix (Fin c) (Fin c) ℂ) ⊗ₖ
            (next.historyKraus_B (privateBobEnvironmentEquiv c next t) *
              transferKraus p a b z)).submatrix _ _
      rw [Matrix.mul_assoc, privateBob_call_step, ih t, Matrix.submatrix_mul_equiv,
        ← Matrix.mul_kronecker_mul, Matrix.one_mul]

variable {E : Type*} [Fintype E] [DecidableEq E]

theorem withPrivateBob_priorEve {p : ℝ} {a b af bf : ℕ} (c : ℕ)
    (P : FiniteKeyProtocol p a b af bf)
    (ρ : Matrix ((Fin c × (Fin a × Fin b)) × E)
      ((Fin c × (Fin a × Fin b)) × E) ℂ) :
    PublicHistory.localPriorEveMatrix_B (withPrivateBob c P)
      (ρ.submatrix ((privateBobJointEquiv c a b).prodCongr (Equiv.refl E))
        ((privateBobJointEquiv c a b).prodCongr (Equiv.refl E))) =
      (LaneHistoryTransport.fullOutputWithPrivateMemoryAndEve_B P ρ).submatrix
        ((privateBobJointEquiv c af bf).prodCongr
          ((privateBobEnvironmentEquiv c P).prodCongr (Equiv.refl E)))
        ((privateBobJointEquiv c af bf).prodCongr
          ((privateBobEnvironmentEquiv c P).prodCongr (Equiv.refl E))) :=
  LaneHistoryTransport.priorEve_privateMemory_transport_B P (withPrivateBob c P)
    (privateBobJointEquiv c a b) (privateBobJointEquiv c af bf)
    (privateBobEnvironmentEquiv c P) (withPrivateBob_historyKraus c P)
    (privateBob_public_eq_iff c P) ρ

def privateBobOutputEquiv {p : ℝ} {a b af bf : ℕ} (c : ℕ)
    (P : FiniteKeyProtocol p a b af bf) :
    ((Fin af × Fin (c * bf)) × ((withPrivateBob c P).Environment × E)) ≃
      (Fin c × ((Fin af × Fin bf) × (P.Environment × E))) :=
  (((privateBobJointEquiv c af bf).prodCongr
      ((privateBobEnvironmentEquiv c P).prodCongr (Equiv.refl E))).trans
    (Equiv.prodAssoc (Fin c) (Fin af × Fin bf) (P.Environment × E)))

def forgetPrivateBobOutput {p : ℝ} {a b af bf : ℕ} (c : ℕ)
    (P : FiniteKeyProtocol p a b af bf)
    (σ : Matrix ((Fin af × Fin (c * bf)) × ((withPrivateBob c P).Environment × E))
      ((Fin af × Fin (c * bf)) × ((withPrivateBob c P).Environment × E)) ℂ) :
    Matrix ((Fin af × Fin bf) × (P.Environment × E))
      ((Fin af × Fin bf) × (P.Environment × E)) ℂ :=
  partialTraceLeft (σ.submatrix (privateBobOutputEquiv (E := E) c P).symm
    (privateBobOutputEquiv (E := E) c P).symm)

theorem withPrivateBob_forget_same_Eve {p : ℝ} {a b af bf : ℕ} (c : ℕ)
    (P : FiniteKeyProtocol p a b af bf)
    (ρ : Matrix ((Fin c × (Fin a × Fin b)) × E)
      ((Fin c × (Fin a × Fin b)) × E) ℂ) :
    forgetPrivateBobOutput c P
      (PublicHistory.localPriorEveMatrix_B (withPrivateBob c P)
        (ρ.submatrix ((privateBobJointEquiv c a b).prodCongr (Equiv.refl E))
          ((privateBobJointEquiv c a b).prodCongr (Equiv.refl E)))) =
      PublicHistory.localPriorEveMatrix_B P (forgetPrivateAliceInput c a b ρ) := by
  rw [withPrivateBob_priorEve]
  have hin : forgetPrivateAliceInput c a b ρ =
      ∑ r : Fin c, Matrix.of (fun x y => ρ ((r,x.1),x.2) ((r,y.1),y.2)) := by
    ext x y
    simp only [forgetPrivateAliceInput, partialTraceLeft, Matrix.submatrix_apply,
      Equiv.prodAssoc_symm_apply, Matrix.sum_apply, Matrix.of_apply]
  rw [hin, localPriorEveMatrix_sum]
  ext x y
  simp only [forgetPrivateBobOutput, partialTraceLeft, Matrix.submatrix_apply,
    privateBobOutputEquiv, Equiv.symm_trans_apply, Equiv.prodAssoc_symm_apply,
    Equiv.prodCongr_apply, Equiv.prodCongr_symm, Equiv.apply_symm_apply,
    Equiv.refl_symm, Equiv.refl_apply, Prod.map_fst, Prod.map_snd,
    LaneHistoryTransport.fullOutputWithPrivateMemoryAndEve_B,
    Matrix.sum_apply, PublicHistory.localPriorEveMatrix_B, Matrix.of_apply]

theorem privateLabelDensity_apply {a b c : ℕ} (label : Fin a → Fin c)
    (ρ : Density (Fin a × Fin b)) (r : Fin c) (i : Fin a) (v : Fin b)
    (r' : Fin c) (j : Fin a) (w : Fin b) :
    (privateLabelDensity label ρ).mat
      ((privateAliceLocalEquiv c a).symm (r,i),v)
      ((privateAliceLocalEquiv c a).symm (r',j),w) =
        if r = label i ∧ r' = label j then ρ.mat (i,v) (j,w) else 0 := by
  rw [privateLabelDensity_matrix]
  dsimp only [labelCopyMatrix]
  rw [basisEmbedding_tensor_identity,
    PublicHistory.basisEmbedding_sandwich_apply_B
      (fun x : Fin a × Fin b =>
        ((privateAliceLocalEquiv c a).symm (label x.1,x.1),x.2))
      (fun x : Fin (c * a) × Fin b => ((privateAliceLocalEquiv c a x.1).2,x.2))
      (by intro x; simp only [Equiv.apply_symm_apply])]
  simp only [Equiv.apply_symm_apply, Prod.mk.injEq, and_true,
    Equiv.symm_apply_eq, Equiv.apply_symm_apply, eq_comm]

def labelDephasedMatrix {a b c : ℕ} (label : Fin a → Fin c)
    (ρ : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) :
    Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ :=
  fun x y => if label x.1 = label y.1 then ρ x y else 0

def privateLabelMemoryMatrix {a b c : ℕ} (label : Fin a → Fin c)
    (ρ : Density (Fin a × Fin b)) (ξ : Density E) :
    Matrix ((Fin c × (Fin a × Fin b)) × E)
      ((Fin c × (Fin a × Fin b)) × E) ℂ :=
  ((privateLabelDensity label ρ).tensor ξ).mat.submatrix
    ((privateAliceJointEquiv c a b).symm.prodCongr (Equiv.refl E))
    ((privateAliceJointEquiv c a b).symm.prodCongr (Equiv.refl E))

theorem privateLabelMemoryMatrix_matrix {a b c : ℕ} (label : Fin a → Fin c)
    (ρ : Density (Fin a × Fin b)) (ξ : Density E) :
    (privateLabelMemoryMatrix label ρ ξ).submatrix
      ((privateAliceJointEquiv c a b).prodCongr (Equiv.refl E))
      ((privateAliceJointEquiv c a b).prodCongr (Equiv.refl E)) =
        ((privateLabelDensity label ρ).tensor ξ).mat := by
  ext x y
  change ((privateLabelDensity label ρ).tensor ξ).mat
    (((privateAliceJointEquiv c a b).prodCongr (Equiv.refl E)).symm
      (((privateAliceJointEquiv c a b).prodCongr (Equiv.refl E)) x))
    (((privateAliceJointEquiv c a b).prodCongr (Equiv.refl E)).symm
      (((privateAliceJointEquiv c a b).prodCongr (Equiv.refl E)) y)) = _
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]

theorem privateLabelMemoryMatrix_forget {a b c : ℕ} (label : Fin a → Fin c)
    (ρ : Density (Fin a × Fin b)) (ξ : Density E) :
    forgetPrivateAliceInput c a b (privateLabelMemoryMatrix label ρ ξ) =
      labelDephasedMatrix label ρ.mat ⊗ₖ ξ.mat := by
  ext x y
  rcases x with ⟨⟨i,v⟩,e⟩
  rcases y with ⟨⟨j,w⟩,e'⟩
  change (∑ r : Fin c, (privateLabelDensity label ρ).mat
    ((privateAliceLocalEquiv c a).symm (r,i),v)
    ((privateAliceLocalEquiv c a).symm (r,j),w) * ξ.mat e e') = _
  simp only [privateLabelDensity_apply, ite_mul, zero_mul,
    Matrix.kroneckerMap_apply, labelDephasedMatrix]
  by_cases h : label i = label j
  · rw [← h]
    simp only [and_self, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  · have hn : ∀ r : Fin c, ¬(r = label i ∧ r = label j) :=
      fun r hr => h (hr.1.symm.trans hr.2)
    simp only [if_neg (hn _), Finset.sum_const_zero, if_neg h, zero_mul]

theorem coherentSeed_label_dephase {d : ℕ} (a : ProbabilityLaw (Fin d))
    (x y : Fin d × Fin d) :
    (if x.1 = y.1 then a.coherentSeedMatrix x y else 0) = a.copiedMatrix x y := by
  rcases x with ⟨i,v⟩
  rcases y with ⟨j,w⟩
  by_cases h : i = j
  · subst j
    simp only [if_true]
    by_cases hv : i = v
    · subst v
      by_cases hw : i = w
      · subst w
        simpa [ProbabilityLaw.copiedMatrix, Matrix.diagonal_apply] using
          a.coherentSeedMatrix_diagonal (i,i)
      · simp [ProbabilityLaw.coherentSeedMatrix, ProbabilityLaw.coherentSeedVector,
          ProbabilityLaw.copiedMatrix, Matrix.vecMulVec_apply,
          Matrix.diagonal_apply, hw, Prod.mk.injEq]
    · simp [ProbabilityLaw.coherentSeedMatrix, ProbabilityLaw.coherentSeedVector,
        ProbabilityLaw.copiedMatrix, Matrix.vecMulVec_apply,
        Matrix.diagonal_apply, hv, Prod.mk.injEq]
  · simp [ProbabilityLaw.copiedMatrix, Matrix.diagonal_apply, Prod.mk.injEq, h]

theorem coherentSeedAncillas_label_dephase {d c e : ℕ} (a : ProbabilityLaw (Fin d))
    (ρA : Density (Fin c)) (ρB : Density (Fin e)) :
    labelDephasedMatrix (fun x : Fin (d * c) => (privateAliceLocalEquiv d c x).1)
      (coherentSeedAncillas a ρA ρB).mat = (copiedSeedAncillas a ρA ρB).mat := by
  ext x y
  rcases x with ⟨x,v⟩
  rcases y with ⟨y,w⟩
  obtain ⟨⟨i,u⟩, rfl⟩ := (privateAliceLocalEquiv d c).symm.surjective x
  obtain ⟨⟨j,u'⟩, rfl⟩ := (privateAliceLocalEquiv d c).symm.surjective y
  obtain ⟨⟨v,t⟩, rfl⟩ := (privateAliceLocalEquiv d e).symm.surjective v
  obtain ⟨⟨w,t'⟩, rfl⟩ := (privateAliceLocalEquiv d e).symm.surjective w
  simp only [labelDephasedMatrix, coherentSeedAncillas, copiedSeedAncillas,
    Density.relabel, Density.tensor, Matrix.submatrix_apply, Matrix.kroneckerMap_apply,
    QuantumProver.AmplitudeDamping.FiniteModel.tensorLabEquiv, privateAliceLocalEquiv,
    Equiv.trans_apply, Equiv.prodCongr_apply, Equiv.prodProdProdComm_apply,
    Prod.map_fst, Prod.map_snd, Equiv.apply_symm_apply, Equiv.symm_symm,
    Equiv.symm_apply_apply]
  change (if i = j then a.coherentSeedMatrix (i,v) (j,w) *
    (ρA.mat u u' * ρB.mat t t') else 0) =
      a.copiedMatrix (i,v) (j,w) * (ρA.mat u u' * ρB.mat t t')
  by_cases h : i = j
  · have hs := coherentSeed_label_dephase a (i,v) (j,w)
    simp only [h, if_true] at hs ⊢
    rw [hs]
  · have hs := coherentSeed_label_dephase a (i,v) (j,w)
    simp only [h, if_false] at hs ⊢
    rw [← hs, zero_mul]

theorem retainedSeedAncillas_physical_protocol_same_Eve
    {p : ℝ} {d c e af bf : ℕ}
    (P : FiniteKeyProtocol p (d * c) (d * e) af bf)
    (a : ProbabilityLaw (Fin d)) (ρA : Density (Fin c)) (ρB : Density (Fin e))
    (ξ : Density E) :
    forgetPrivateAliceOutput d P
      (PublicHistory.localPriorEveMatrix_B (withPrivateAlice d P)
        ((retainedSeedAncillas a ρA ρB).tensor ξ).mat) =
      PublicHistory.localPriorEveMatrix_B P ((copiedSeedAncillas a ρA ρB).tensor ξ).mat := by
  change forgetPrivateAliceOutput d P
    (PublicHistory.localPriorEveMatrix_B (withPrivateAlice d P)
      ((privateLabelDensity _ (coherentSeedAncillas a ρA ρB)).tensor ξ).mat) = _
  rw [← privateLabelMemoryMatrix_matrix, withPrivateAlice_forget_same_Eve,
    privateLabelMemoryMatrix_forget, coherentSeedAncillas_label_dephase]
  rfl

section PureFactors

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

def factorVector (ρ : Density I) : I × I → ℂ :=
  fun x => star (CFC.sqrt ρ.mat x.1 x.2)

def factorMatrix (ρ : Density I) : Matrix (I × I) (I × I) ℂ :=
  Matrix.vecMulVec (factorVector ρ) (star (factorVector ρ))

theorem factorMatrix_active (ρ : Density I) : partialTraceLeft (factorMatrix ρ) = ρ.mat := by
  have hroot : (CFC.sqrt ρ.mat)ᴴ = CFC.sqrt ρ.mat :=
    (CFC.sqrt_nonneg ρ.mat).posSemidef.isHermitian
  have hgram : (CFC.sqrt ρ.mat)ᴴ * CFC.sqrt ρ.mat = ρ.mat := by
    rw [hroot, CFC.sqrt_mul_sqrt_self ρ.mat ρ.positive.nonneg]
  rw [← hgram]
  ext i j
  simp only [partialTraceLeft, factorMatrix, factorVector, Matrix.vecMulVec_apply,
    Pi.star_apply, star_star, Matrix.mul_apply, Matrix.conjTranspose_apply]

def factorDensity (ρ : Density I) : Density (I × I) where
  mat := factorMatrix ρ
  positive := Matrix.posSemidef_vecMulVec_self_star _
  normalized := by rw [← trace_partialTraceLeft, factorMatrix_active, ρ.normalized]

theorem factorDensity_active (ρ : Density I) : (factorDensity ρ).marginalRight = ρ := by
  apply Density.eq_of_mat_eq
  exact factorMatrix_active ρ

def factorPrivateDensity (ρ : Density I) : Density I where
  mat := partialTraceRight (factorDensity ρ).mat
  positive := partialTraceRight_posSemidef (factorDensity ρ).positive
  normalized := (trace_partialTraceRight _).trans (factorDensity ρ).normalized

def factorFinDensity {c : ℕ} (ρ : Density (Fin c)) : Density (Fin (c * c)) :=
  (factorDensity ρ).relabel (privateAliceLocalEquiv c c)

theorem outer_tensor (u : I → ℂ) (v : J → ℂ) :
    Matrix.vecMulVec u (star u) ⊗ₖ Matrix.vecMulVec v (star v) =
      Matrix.vecMulVec (fun x : I × J => u x.1 * v x.2)
        (star (fun x : I × J => u x.1 * v x.2)) := by
  ext x y
  simp only [Matrix.kroneckerMap_apply, Matrix.vecMulVec_apply, Pi.star_apply, star_mul]
  ring

theorem outer_relabel {K : Type*} (u : I → ℂ) (e : K ≃ I) :
    (Matrix.vecMulVec u (star u)).submatrix e e =
      Matrix.vecMulVec (fun x : K => u (e x)) (star (fun x : K => u (e x))) := rfl

end PureFactors

def jointHonestDensity {H R : Type*} [Fintype H] [Fintype R]
    (ρ : Density (H × R)) : Density H where
  mat := partialTraceRight ρ.mat
  positive := partialTraceRight_posSemidef ρ.positive
  normalized := (trace_partialTraceRight _).trans ρ.normalized

def pureFactorInputEquiv (d c e f : ℕ) :
    ((Fin (d * ((c * c) * f)) × Fin (d * (e * e))) × Fin f) ≃
      (((Fin d × Fin d) × ((Fin c × Fin c) × (Fin e × Fin e))) × (Fin f × Fin f)) where
  toFun x :=
    let u := privateAliceLocalEquiv d ((c * c) * f) x.1.1
    let v := privateAliceLocalEquiv (c * c) f u.2
    let w := privateAliceLocalEquiv d (e * e) x.1.2
    (((u.1,w.1),(privateAliceLocalEquiv c c v.1,privateAliceLocalEquiv e e w.2)),(v.2,x.2))
  invFun x :=
    (( (privateAliceLocalEquiv d ((c * c) * f)).symm
      (x.1.1.1,(privateAliceLocalEquiv (c * c) f).symm
        ((privateAliceLocalEquiv c c).symm x.1.2.1,x.2.1)),
      (privateAliceLocalEquiv d (e * e)).symm
        (x.1.1.2,(privateAliceLocalEquiv e e).symm x.1.2.2)),x.2.2)
  left_inv x := by simp only [Equiv.symm_apply_apply, Prod.mk.eta]
  right_inv x := by simp only [Equiv.apply_symm_apply, Prod.mk.eta]

theorem pureFactorInputEquiv_apply (d c e f : ℕ)
    (x : (Fin (d * ((c * c) * f)) × Fin (d * (e * e))) × Fin f) :
    pureFactorInputEquiv d c e f x =
      ((((privateAliceLocalEquiv d ((c * c) * f) x.1.1).1,
          (privateAliceLocalEquiv d (e * e) x.1.2).1),
        (privateAliceLocalEquiv c c
          (privateAliceLocalEquiv (c * c) f
            (privateAliceLocalEquiv d ((c * c) * f) x.1.1).2).1,
          privateAliceLocalEquiv e e (privateAliceLocalEquiv d (e * e) x.1.2).2)),
        ((privateAliceLocalEquiv (c * c) f
          (privateAliceLocalEquiv d ((c * c) * f) x.1.1).2).2,x.2)) := rfl

def pureFactorInput {d c e f : ℕ} (a : ProbabilityLaw (Fin d))
    (ρA : Density (Fin c)) (ρB : Density (Fin e)) (ξ : Density (Fin f)) :
    Density ((Fin (d * ((c * c) * f)) × Fin (d * (e * e))) × Fin f) :=
  ((a.coherentSeedDensity.tensor ((factorDensity ρA).tensor (factorDensity ρB))).tensor
    (factorDensity ξ)).relabel (pureFactorInputEquiv d c e f)

def pureFactorVector {d c e f : ℕ} (a : ProbabilityLaw (Fin d))
    (ρA : Density (Fin c)) (ρB : Density (Fin e)) (ξ : Density (Fin f)) :
    (Fin (d * ((c * c) * f)) × Fin (d * (e * e))) × Fin f → ℂ :=
  fun x =>
    let y := pureFactorInputEquiv d c e f x
    (a.coherentSeedVector y.1.1 *
      (factorVector ρA y.1.2.1 * factorVector ρB y.1.2.2)) * factorVector ξ y.2

theorem pureFactorInput_outer {d c e f : ℕ} (a : ProbabilityLaw (Fin d))
    (ρA : Density (Fin c)) (ρB : Density (Fin e)) (ξ : Density (Fin f)) :
    (pureFactorInput a ρA ρB ξ).mat =
      Matrix.vecMulVec (pureFactorVector a ρA ρB ξ) (star (pureFactorVector a ρA ρB ξ)) := by
  change ((a.coherentSeedMatrix ⊗ₖ (factorMatrix ρA ⊗ₖ factorMatrix ρB)) ⊗ₖ
    factorMatrix ξ).submatrix _ _ = _
  rw [ProbabilityLaw.coherentSeedMatrix, factorMatrix, factorMatrix, factorMatrix,
    outer_tensor, outer_tensor, outer_tensor, outer_relabel]
  rfl

theorem pureFactorInput_honest {d c e f : ℕ} (a : ProbabilityLaw (Fin d))
    (ρA : Density (Fin c)) (ρB : Density (Fin e)) (ξ : Density (Fin f)) :
    jointHonestDensity (pureFactorInput a ρA ρB ξ) =
      coherentSeedAncillas a
        (((factorFinDensity ρA).tensor (factorPrivateDensity ξ)).relabel
          (privateAliceLocalEquiv (c * c) f)) (factorFinDensity ρB) := by
  apply Density.eq_of_mat_eq
  ext x y
  rcases x with ⟨x,v⟩
  rcases y with ⟨y,w⟩
  obtain ⟨⟨i,u⟩,rfl⟩ := (privateAliceLocalEquiv d ((c * c) * f)).symm.surjective x
  obtain ⟨⟨j,u'⟩,rfl⟩ := (privateAliceLocalEquiv d ((c * c) * f)).symm.surjective y
  obtain ⟨⟨t,r⟩,rfl⟩ := (privateAliceLocalEquiv (c * c) f).symm.surjective u
  obtain ⟨⟨t',r'⟩,rfl⟩ := (privateAliceLocalEquiv (c * c) f).symm.surjective u'
  obtain ⟨⟨k,s⟩,rfl⟩ := (privateAliceLocalEquiv d (e * e)).symm.surjective v
  obtain ⟨⟨l,s'⟩,rfl⟩ := (privateAliceLocalEquiv d (e * e)).symm.surjective w
  simp only [jointHonestDensity, partialTraceRight, pureFactorInput, Density.relabel,
    Density.tensor, Matrix.submatrix_apply, Matrix.kroneckerMap_apply,
    pureFactorInputEquiv_apply, factorDensity, coherentSeedAncillas, factorFinDensity,
    factorPrivateDensity, QuantumProver.AmplitudeDamping.FiniteModel.tensorLabEquiv,
    privateAliceLocalEquiv, Equiv.trans_apply, Equiv.prodCongr_apply,
    Equiv.prodProdProdComm_apply, Prod.map_fst, Prod.map_snd, Equiv.symm_symm,
    Equiv.symm_apply_apply, Equiv.apply_symm_apply]
  rw [← Finset.mul_sum]
  ring

theorem pureFactorInput_resource_le {d c e f : ℕ} (a : ProbabilityLaw (Fin d))
    (ρA : Density (Fin c)) (ρB : Density (Fin e)) (ξ : Density (Fin f))
    {z : ℝ} (hz : 0 < z) (hz1 : z < 1) :
    QuantumProver.AmplitudeDamping.FiniteModel.sandwichedEntanglement (1 / (1 - z))
      (d * ((c * c) * f)) (d * (e * e))
        (jointHonestDensity (pureFactorInput a ρA ρB ξ)).mat ≤ (a.renyiSeedCharge z : EReal) := by
  rw [pureFactorInput_honest, coherentSeedAncillas_matrix]
  exact a.coherentSeed_entanglement_le_with_local_ancillas _ _ hz hz1

theorem coefficient_outer_trace {H R : Type*} [Fintype H] [Fintype R]
    (u : H × R → ℂ) :
    ((Matrix.of fun h r => star (u (h,r)))ᴴ * (Matrix.of fun h r => star (u (h,r)))).trace =
      (Matrix.vecMulVec u (star u)).trace := by
  have h : partialTraceLeft (Matrix.vecMulVec u (star u)) =
      (Matrix.of fun h r => star (u (h,r)))ᴴ * (Matrix.of fun h r => star (u (h,r))) := by
    ext r s
    simp only [partialTraceLeft, Matrix.vecMulVec_apply, Pi.star_apply,
      Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, star_star]
  rw [← h, trace_partialTraceLeft]

def pureFactorCoefficient {d c e f : ℕ} (a : ProbabilityLaw (Fin d))
    (ρA : Density (Fin c)) (ρB : Density (Fin e)) (ξ : Density (Fin f)) :
    Matrix (Fin (d * ((c * c) * f)) × Fin (d * (e * e))) (Fin f) ℂ :=
  Matrix.of fun h r => star (pureFactorVector a ρA ρB ξ (h,r))

theorem pureFactorCoefficient_normalized {d c e f : ℕ} (a : ProbabilityLaw (Fin d))
    (ρA : Density (Fin c)) (ρB : Density (Fin e)) (ξ : Density (Fin f)) :
    ((pureFactorCoefficient a ρA ρB ξ)ᴴ * pureFactorCoefficient a ρA ρB ξ).trace = 1 := by
  rw [pureFactorCoefficient, coefficient_outer_trace, ← pureFactorInput_outer]
  exact (pureFactorInput a ρA ρB ξ).normalized

theorem quantumSEP_local_relabel {a b ao bo : ℕ}
    (eA : Fin ao ≃ Fin a) (eB : Fin bo ≃ Fin b)
    {σ : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ}
    (hσ : QuantumProver.AmplitudeDamping.FiniteModel.IsSeparable a b σ) :
    QuantumProver.AmplitudeDamping.FiniteModel.IsSeparable ao bo
      (σ.submatrix (eA.prodCongr eB) (eA.prodCongr eB)) := by
  obtain ⟨k,t,X,Y,ht,hs,hXY,hσ⟩ := hσ
  refine ⟨k,t,(fun j => (X j).submatrix eA eA),
    (fun j => (Y j).submatrix eB eB),ht,hs,
      (fun j => ⟨(hXY j).1.submatrix_equiv eA, (hXY j).2.submatrix_equiv eB⟩), ?_⟩
  rw [hσ]
  ext x y
  simp only [Matrix.submatrix_apply, Matrix.sum_apply, Matrix.smul_apply,
    Matrix.kroneckerMap_apply, Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd]

theorem quantumResource_local_relabel_le {a b ao bo : ℕ}
    (eA : Fin ao ≃ Fin a) (eB : Fin bo ≃ Fin b) (ρ : Density (Fin a × Fin b)) (α : ℝ) :
    QuantumProver.AmplitudeDamping.FiniteModel.sandwichedEntanglement α ao bo
      (ρ.mat.submatrix (eA.prodCongr eB) (eA.prodCongr eB)) ≤
        QuantumProver.AmplitudeDamping.FiniteModel.sandwichedEntanglement α a b ρ.mat := by
  unfold QuantumProver.AmplitudeDamping.FiniteModel.sandwichedEntanglement
  apply le_sInf
  rintro q ⟨σ,⟨hσ,hsep⟩,rfl⟩
  rw [← QuantumProver.AmplitudeDamping.TensorPower.sandwichedDivergence_submatrix_equiv
    ρ.positive hσ.1 (eA.prodCongr eB) α]
  exact sInf_le ⟨σ.submatrix (eA.prodCongr eB) (eA.prodCongr eB),
    ⟨hσ.submatrix_equiv _, quantumSEP_local_relabel eA eB hsep⟩,rfl⟩

def privateFourChart {R T K A : Type*} : ((R × T) × (K × A)) ≃ (K × ((R × A) × T)) where
  toFun x := (x.2.1,((x.1.1,x.2.2),x.1.2))
  invFun x := ((x.2.1.1,x.2.2),(x.1,x.2.1.2))
  left_inv _ := rfl
  right_inv _ := rfl

def privateThreeChart {R K A : Type*} : (R × (K × A)) ≃ (K × (R × A)) where
  toFun x := (x.2.1,(x.1,x.2.2))
  invFun x := (x.2.1,(x.1,x.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

def privateFactorsAliceEquiv (d c f : ℕ) :
    Fin ((c * f) * (d * c)) ≃ Fin (d * ((c * c) * f)) :=
  ((((privateAliceLocalEquiv (c * f) (d * c)).trans
    ((privateAliceLocalEquiv c f).prodCongr (privateAliceLocalEquiv d c))).trans
      privateFourChart).trans
        ((Equiv.refl (Fin d)).prodCongr
          (((privateAliceLocalEquiv c c).symm.prodCongr (Equiv.refl (Fin f))).trans
            (privateAliceLocalEquiv (c * c) f).symm))).trans
              (privateAliceLocalEquiv d ((c * c) * f)).symm

def privateFactorsBobEquiv (d e : ℕ) : Fin (e * (d * e)) ≃ Fin (d * (e * e)) :=
  ((((privateAliceLocalEquiv e (d * e)).trans
    ((Equiv.refl (Fin e)).prodCongr (privateAliceLocalEquiv d e))).trans
      privateThreeChart).trans
        ((Equiv.refl (Fin d)).prodCongr (privateAliceLocalEquiv e e).symm)).trans
          (privateAliceLocalEquiv d (e * e)).symm

def matrixSeedLabel (d c f : ℕ) (x : Fin ((c * f) * (d * c))) : Fin d :=
  (privateAliceLocalEquiv d c (privateAliceLocalEquiv (c * f) (d * c) x).2).1

def pureFactorMatrixInput {d c e f : ℕ} (a : ProbabilityLaw (Fin d))
    (ρA : Density (Fin c)) (ρB : Density (Fin e)) (ξ : Density (Fin f)) :
    Density ((Fin ((c * f) * (d * c)) × Fin (e * (d * e))) × Fin f) :=
  (pureFactorInput a ρA ρB ξ).relabel
    (((privateFactorsAliceEquiv d c f).prodCongr (privateFactorsBobEquiv d e)).prodCongr
      (Equiv.refl (Fin f)))

def pureFactorMatrixVector {d c e f : ℕ} (a : ProbabilityLaw (Fin d))
    (ρA : Density (Fin c)) (ρB : Density (Fin e)) (ξ : Density (Fin f)) :
    (Fin ((c * f) * (d * c)) × Fin (e * (d * e))) × Fin f → ℂ :=
  fun x => pureFactorVector a ρA ρB ξ
    ((((privateFactorsAliceEquiv d c f).prodCongr (privateFactorsBobEquiv d e)).prodCongr
      (Equiv.refl (Fin f))) x)

theorem pureFactorMatrixInput_outer {d c e f : ℕ} (a : ProbabilityLaw (Fin d))
    (ρA : Density (Fin c)) (ρB : Density (Fin e)) (ξ : Density (Fin f)) :
    (pureFactorMatrixInput a ρA ρB ξ).mat =
      Matrix.vecMulVec (pureFactorMatrixVector a ρA ρB ξ)
        (star (pureFactorMatrixVector a ρA ρB ξ)) := by
  change (pureFactorInput a ρA ρB ξ).mat.submatrix _ _ = _
  rw [pureFactorInput_outer, outer_relabel]
  rfl

theorem jointHonestDensity_local_relabel {A B R : Type*}
    [Fintype A] [Fintype B] [Fintype R] [DecidableEq A] [DecidableEq B] [DecidableEq R]
    (e : B ≃ A) (ρ : Density (A × R)) :
    jointHonestDensity (ρ.relabel (e.prodCongr (Equiv.refl R))) =
      (jointHonestDensity ρ).relabel e := by
  apply Density.eq_of_mat_eq
  ext x y
  rfl

theorem pureFactorMatrixInput_resource_le {d c e f : ℕ} (a : ProbabilityLaw (Fin d))
    (ρA : Density (Fin c)) (ρB : Density (Fin e)) (ξ : Density (Fin f))
    {z : ℝ} (hz : 0 < z) (hz1 : z < 1) :
    QuantumProver.AmplitudeDamping.FiniteModel.sandwichedEntanglement (1 / (1 - z))
      ((c * f) * (d * c)) (e * (d * e))
        (jointHonestDensity (pureFactorMatrixInput a ρA ρB ξ)).mat ≤
          (a.renyiSeedCharge z : EReal) := by
  rw [pureFactorMatrixInput, jointHonestDensity_local_relabel]
  apply (quantumResource_local_relabel_le _ _ _ _).trans
  exact pureFactorInput_resource_le a ρA ρB ξ hz hz1

theorem partialTraceRight_withRightMemory {A B J R : Type*}
    [Fintype A] [Fintype B] [Fintype J] [Fintype R] [DecidableEq A] [DecidableEq B] [DecidableEq R]
    (C : KrausChannel A B J) (ρ : Matrix (A × R) (A × R) ℂ) :
    partialTraceRight ((C.withRightMemory R).eval ρ) = C.eval (partialTraceRight ρ) := by
  have hs : partialTraceRight ρ = ∑ r : R, Matrix.of (fun i j => ρ (i,r) (j,r)) := by
    ext i j
    simp only [partialTraceRight, Matrix.sum_apply, Matrix.of_apply]
  rw [hs, C.eval_finite_sum_B]
  ext i j
  simp only [partialTraceRight, Matrix.sum_apply, eval_withRightMemory_apply]
  rfl

def privateLabelJointDensity {a b c : ℕ} {R : Type*} [Fintype R] [DecidableEq R]
    (label : Fin a → Fin c) (ρ : Density ((Fin a × Fin b) × R)) :
    Density ((Fin (c * a) × Fin b) × R) :=
  (((labelCopyChannel label).withRightMemory (Fin b)).withRightMemory R).onDensity ρ

theorem privateLabelJointDensity_honest {a b c : ℕ} {R : Type*}
    [Fintype R] [DecidableEq R] (label : Fin a → Fin c)
    (ρ : Density ((Fin a × Fin b) × R)) :
    jointHonestDensity (privateLabelJointDensity label ρ) =
      privateLabelDensity label (jointHonestDensity ρ) := by
  apply Density.eq_of_mat_eq
  exact partialTraceRight_withRightMemory ((labelCopyChannel label).withRightMemory (Fin b)) ρ.mat

def seedPureMatrixInput {d c e f : ℕ} (a : ProbabilityLaw (Fin d))
    (ρA : Density (Fin c)) (ρB : Density (Fin e)) (ξ : Density (Fin f)) :
    Density ((Fin (d * ((c * f) * (d * c))) × Fin (e * (d * e))) × Fin f) :=
  privateLabelJointDensity (matrixSeedLabel d c f) (pureFactorMatrixInput a ρA ρB ξ)

theorem seedPureMatrixInput_resource_le {d c e f : ℕ} (a : ProbabilityLaw (Fin d))
    (ρA : Density (Fin c)) (ρB : Density (Fin e)) (ξ : Density (Fin f))
    {z : ℝ} (hz : 0 < z) (hz1 : z < 1) :
    QuantumProver.AmplitudeDamping.FiniteModel.sandwichedEntanglement (1 / (1 - z))
      (d * ((c * f) * (d * c))) (e * (d * e))
        (jointHonestDensity (seedPureMatrixInput a ρA ρB ξ)).mat ≤
          (a.renyiSeedCharge z : EReal) := by
  rw [seedPureMatrixInput, privateLabelJointDensity_honest]
  exact (privateLabelDensity_resource_le _ _
    ((lt_div_iff₀ (sub_pos.mpr hz1)).mpr (by linarith))).trans
      (pureFactorMatrixInput_resource_le a ρA ρB ξ hz hz1)

def seedPureMatrixVector {d c e f : ℕ} (a : ProbabilityLaw (Fin d))
    (ρA : Density (Fin c)) (ρB : Density (Fin e)) (ξ : Density (Fin f)) :
    (Fin (d * ((c * f) * (d * c))) × Fin (e * (d * e))) × Fin f → ℂ :=
  ((labelCopyMatrix (matrixSeedLabel d c f) ⊗ₖ
    (1 : Matrix (Fin (e * (d * e))) (Fin (e * (d * e))) ℂ)) ⊗ₖ
      (1 : Matrix (Fin f) (Fin f) ℂ)) *ᵥ pureFactorMatrixVector a ρA ρB ξ

theorem seedPureMatrixInput_outer {d c e f : ℕ} (a : ProbabilityLaw (Fin d))
    (ρA : Density (Fin c)) (ρB : Density (Fin e)) (ξ : Density (Fin f)) :
    (seedPureMatrixInput a ρA ρB ξ).mat =
      Matrix.vecMulVec (seedPureMatrixVector a ρA ρB ξ)
        (star (seedPureMatrixVector a ρA ρB ξ)) := by
  simp only [seedPureMatrixInput, privateLabelJointDensity, KrausChannel.onDensity,
    KrausChannel.eval, KrausChannel.withRightMemory, labelCopyChannel, Fintype.sum_unique]
  rw [pureFactorMatrixInput_outer, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul,
    ← Matrix.star_mulVec]
  rfl

def seedPureMatrixCoefficient {d c e f : ℕ} (a : ProbabilityLaw (Fin d))
    (ρA : Density (Fin c)) (ρB : Density (Fin e)) (ξ : Density (Fin f)) :
    Matrix (Fin (d * ((c * f) * (d * c))) × Fin (e * (d * e))) (Fin f) ℂ :=
  Matrix.of fun h r => star (seedPureMatrixVector a ρA ρB ξ (h,r))

theorem seedPureMatrixCoefficient_normalized {d c e f : ℕ} (a : ProbabilityLaw (Fin d))
    (ρA : Density (Fin c)) (ρB : Density (Fin e)) (ξ : Density (Fin f)) :
    ((seedPureMatrixCoefficient a ρA ρB ξ)ᴴ * seedPureMatrixCoefficient a ρA ρB ξ).trace = 1 := by
  rw [seedPureMatrixCoefficient, coefficient_outer_trace, ← seedPureMatrixInput_outer]
  exact (seedPureMatrixInput a ρA ρB ξ).normalized

theorem seedPureMatrixInput_coefficient {d c e f : ℕ} (a : ProbabilityLaw (Fin d))
    (ρA : Density (Fin c)) (ρB : Density (Fin e)) (ξ : Density (Fin f)) :
    (seedPureMatrixInput a ρA ρB ξ).mat =
      Matrix.vecMulVec
        (fun x => star (seedPureMatrixCoefficient a ρA ρB ξ x.1 x.2))
        (star (fun x => star (seedPureMatrixCoefficient a ρA ρB ξ x.1 x.2))) := by
  rw [seedPureMatrixInput_outer]
  ext x y
  simp only [Matrix.vecMulVec_apply, Pi.star_apply, seedPureMatrixCoefficient,
    Matrix.of_apply, star_star]

theorem seedPureMatrixInput_resource_le_bits {d c e f : ℕ} [Nonempty (Fin d)]
    (a : ProbabilityLaw (Fin d)) (ρA : Density (Fin c)) (ρB : Density (Fin e))
    (ξ : Density (Fin f)) {z k : ℝ} (hz : 0 < z) (hz1 : z < 1)
    (hk : (d : ℝ) ≤ 2 ^ k) :
    QuantumProver.AmplitudeDamping.FiniteModel.sandwichedEntanglement (1 / (1 - z))
      (d * ((c * f) * (d * c))) (e * (d * e))
        (jointHonestDensity (seedPureMatrixInput a ρA ρB ξ)).mat ≤ (k : EReal) := by
  apply (seedPureMatrixInput_resource_le a ρA ρB ξ hz hz1).trans
  exact_mod_cast a.renyiSeedCharge_le_bits z k hz (by simpa using hk)

def seedPureProtocol {p : ℝ} {d c e f af bf : ℕ}
    (P : FiniteKeyProtocol p (d * c) (d * e) af bf) :
    FiniteKeyProtocol p (d * ((c * f) * (d * c))) (e * (d * e))
      (d * ((c * f) * af)) (e * bf) :=
  withPrivateAlice d (withPrivateAlice (c * f) (withPrivateBob e P))

theorem seedPureProtocol_calls {p : ℝ} {d c e f af bf : ℕ}
    (P : FiniteKeyProtocol p (d * c) (d * e) af bf) : (seedPureProtocol (f := f) P).calls = P.calls := by
  simp only [seedPureProtocol, withPrivateAlice_calls, withPrivateBob_calls]

def forgetPrivateAliceMatrixInput (c a b : ℕ)
    (ρ : Matrix ((Fin (c * a) × Fin b) × E) ((Fin (c * a) × Fin b) × E) ℂ) :
    Matrix ((Fin a × Fin b) × E) ((Fin a × Fin b) × E) ℂ :=
  forgetPrivateAliceInput c a b
    (ρ.submatrix ((privateAliceJointEquiv c a b).symm.prodCongr (Equiv.refl E))
      ((privateAliceJointEquiv c a b).symm.prodCongr (Equiv.refl E)))

def forgetPrivateBobMatrixInput (c a b : ℕ)
    (ρ : Matrix ((Fin a × Fin (c * b)) × E) ((Fin a × Fin (c * b)) × E) ℂ) :
    Matrix ((Fin a × Fin b) × E) ((Fin a × Fin b) × E) ℂ :=
  forgetPrivateAliceInput c a b
    (ρ.submatrix ((privateBobJointEquiv c a b).symm.prodCongr (Equiv.refl E))
      ((privateBobJointEquiv c a b).symm.prodCongr (Equiv.refl E)))

theorem submatrix_inverse_cancel {I J : Type*} (M : Matrix I I ℂ) (e : I ≃ J) :
    (M.submatrix e.symm e.symm).submatrix e e = M := by
  ext x y
  simp only [Matrix.submatrix_apply, Equiv.symm_apply_apply]

theorem withPrivateAlice_forget_matrix {p : ℝ} {a b af bf : ℕ} (c : ℕ)
    (P : FiniteKeyProtocol p a b af bf)
    (ρ : Matrix ((Fin (c * a) × Fin b) × E) ((Fin (c * a) × Fin b) × E) ℂ) :
    forgetPrivateAliceOutput c P
      (PublicHistory.localPriorEveMatrix_B (withPrivateAlice c P) ρ) =
        PublicHistory.localPriorEveMatrix_B P (forgetPrivateAliceMatrixInput c a b ρ) := by
  have h := withPrivateAlice_forget_same_Eve c P
    (ρ.submatrix ((privateAliceJointEquiv c a b).prodCongr (Equiv.refl E)).symm
      ((privateAliceJointEquiv c a b).prodCongr (Equiv.refl E)).symm)
  rw [submatrix_inverse_cancel] at h
  exact h

theorem withPrivateBob_forget_matrix {p : ℝ} {a b af bf : ℕ} (c : ℕ)
    (P : FiniteKeyProtocol p a b af bf)
    (ρ : Matrix ((Fin a × Fin (c * b)) × E) ((Fin a × Fin (c * b)) × E) ℂ) :
    forgetPrivateBobOutput c P
      (PublicHistory.localPriorEveMatrix_B (withPrivateBob c P) ρ) =
        PublicHistory.localPriorEveMatrix_B P (forgetPrivateBobMatrixInput c a b ρ) := by
  have h := withPrivateBob_forget_same_Eve c P
    (ρ.submatrix ((privateBobJointEquiv c a b).prodCongr (Equiv.refl E)).symm
      ((privateBobJointEquiv c a b).prodCongr (Equiv.refl E)).symm)
  rw [submatrix_inverse_cancel] at h
  exact h

def jointLabelDephasedMatrix {a b c : ℕ} (label : Fin a → Fin c)
    (ρ : Matrix ((Fin a × Fin b) × E) ((Fin a × Fin b) × E) ℂ) :
    Matrix ((Fin a × Fin b) × E) ((Fin a × Fin b) × E) ℂ :=
  fun x y => if label x.1.1 = label y.1.1 then ρ x y else 0

theorem privateLabelJointDensity_apply {a b c : ℕ} (label : Fin a → Fin c)
    (ρ : Density ((Fin a × Fin b) × E)) (r r' : Fin c) (i j : Fin a)
    (v w : Fin b) (u u' : E) :
    (privateLabelJointDensity label ρ).mat
      (((privateAliceLocalEquiv c a).symm (r,i),v),u)
      (((privateAliceLocalEquiv c a).symm (r',j),w),u') =
        if r = label i ∧ r' = label j then ρ.mat ((i,v),u) ((j,w),u') else 0 := by
  simp only [privateLabelJointDensity, KrausChannel.onDensity, KrausChannel.eval,
    KrausChannel.withRightMemory, labelCopyChannel, Fintype.sum_unique]
  dsimp only [labelCopyMatrix]
  rw [basisEmbedding_tensor_identity, basisEmbedding_tensor_identity,
    PublicHistory.basisEmbedding_sandwich_apply_B
      (fun x : (Fin a × Fin b) × E =>
        (((privateAliceLocalEquiv c a).symm (label x.1.1,x.1.1),x.1.2),x.2))
      (fun x : (Fin (c * a) × Fin b) × E =>
        (((privateAliceLocalEquiv c a x.1.1).2,x.1.2),x.2))
      (by intro x; simp only [Equiv.apply_symm_apply])]
  simp only [Equiv.apply_symm_apply, Prod.mk.injEq, and_true,
    Equiv.symm_apply_eq, Equiv.apply_symm_apply, eq_comm]

theorem privateLabelJointDensity_forget {a b c : ℕ} (label : Fin a → Fin c)
    (ρ : Density ((Fin a × Fin b) × E)) :
    forgetPrivateAliceMatrixInput c a b (privateLabelJointDensity label ρ).mat =
      jointLabelDephasedMatrix label ρ.mat := by
  ext x y
  rcases x with ⟨⟨i,v⟩,u⟩
  rcases y with ⟨⟨j,w⟩,u'⟩
  change (∑ r : Fin c, (privateLabelJointDensity label ρ).mat
    (((privateAliceLocalEquiv c a).symm (r,i),v),u)
    (((privateAliceLocalEquiv c a).symm (r,j),w),u')) = _
  simp only [privateLabelJointDensity_apply, jointLabelDephasedMatrix]
  by_cases h : label i = label j
  · rw [← h]
    simp only [and_self, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  · have hn : ∀ r : Fin c, ¬(r = label i ∧ r = label j) :=
      fun r hr => h (hr.1.symm.trans hr.2)
    simp only [if_neg (hn _), Finset.sum_const_zero, if_neg h]

theorem privateFactorsAliceEquiv_chart (d c f : ℕ) (r : Fin c) (s : Fin f)
    (x : Fin (d * c)) :
    privateFactorsAliceEquiv d c f
      ((privateAliceLocalEquiv (c * f) (d * c)).symm
        ((privateAliceLocalEquiv c f).symm (r,s),x)) =
      (privateAliceLocalEquiv d ((c * c) * f)).symm
        ((privateAliceLocalEquiv d c x).1,
          (privateAliceLocalEquiv (c * c) f).symm
            ((privateAliceLocalEquiv c c).symm (r,(privateAliceLocalEquiv d c x).2),s)) := by
  simp [privateFactorsAliceEquiv, privateFourChart]

theorem privateFactorsBobEquiv_chart (d e : ℕ) (r : Fin e) (x : Fin (d * e)) :
    privateFactorsBobEquiv d e ((privateAliceLocalEquiv e (d * e)).symm (r,x)) =
      (privateAliceLocalEquiv d (e * e)).symm
        ((privateAliceLocalEquiv d e x).1,
          (privateAliceLocalEquiv e e).symm (r,(privateAliceLocalEquiv d e x).2)) := by
  simp [privateFactorsBobEquiv, privateThreeChart]

theorem pureFactorMatrixInput_apply {d c e f : ℕ} (a : ProbabilityLaw (Fin d))
    (ρA : Density (Fin c)) (ρB : Density (Fin e)) (ξ : Density (Fin f))
    (r r' : Fin c) (s s' : Fin f) (t t' : Fin e)
    (xA yA : Fin (d * c)) (xB yB : Fin (d * e)) (u u' : Fin f) :
    (pureFactorMatrixInput a ρA ρB ξ).mat
      (((privateAliceLocalEquiv (c * f) (d * c)).symm
          ((privateAliceLocalEquiv c f).symm (r,s),xA),
        (privateAliceLocalEquiv e (d * e)).symm (t,xB)),u)
      (((privateAliceLocalEquiv (c * f) (d * c)).symm
          ((privateAliceLocalEquiv c f).symm (r',s'),yA),
        (privateAliceLocalEquiv e (d * e)).symm (t',yB)),u') =
      a.coherentSeedMatrix
        ((privateAliceLocalEquiv d c xA).1,(privateAliceLocalEquiv d e xB).1)
        ((privateAliceLocalEquiv d c yA).1,(privateAliceLocalEquiv d e yB).1) *
      (factorMatrix ρA (r,(privateAliceLocalEquiv d c xA).2)
          (r',(privateAliceLocalEquiv d c yA).2) *
        factorMatrix ρB (t,(privateAliceLocalEquiv d e xB).2)
          (t',(privateAliceLocalEquiv d e yB).2)) * factorMatrix ξ (s,u) (s',u') := by
  simp only [pureFactorMatrixInput, Density.relabel, Matrix.submatrix_apply,
    Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd, Equiv.refl_apply,
    privateFactorsAliceEquiv_chart, privateFactorsBobEquiv_chart,
    pureFactorInput, Density.tensor, Matrix.kroneckerMap_apply, pureFactorInputEquiv_apply,
    Equiv.apply_symm_apply, factorDensity]
  rfl

theorem sum_private_product (c f : ℕ) (g : Fin (c * f) → ℂ) :
    (∑ r, g r) = ∑ r : Fin c, ∑ s : Fin f,
      g ((privateAliceLocalEquiv c f).symm (r,s)) := by
  rw [← (privateAliceLocalEquiv c f).symm.sum_comp g, Fintype.sum_prod_type]

theorem independent_three_sums {R S T : Type*} [Fintype R] [Fintype S] [Fintype T]
    (a : R → ℂ) (b : S → ℂ) (v : T → ℂ) (q : ℂ) :
    (∑ s : S, ∑ r : R, ∑ t : T, q * (a r * b s) * v t) =
      q * ((∑ r, a r) * (∑ s, b s)) * (∑ t, v t) := by
  have hi (s : S) : (∑ r : R, ∑ t : T, q * (a r * b s) * v t) =
      (q * (∑ r, a r) * b s) * (∑ t, v t) := by
    simp_rw [← Finset.mul_sum]
    calc
      (∑ r, q * (a r * b s) * (∑ t, v t)) =
          ∑ r, a r * (q * b s * (∑ t, v t)) := by
        apply Finset.sum_congr rfl
        intro r _
        ring
      _ = (∑ r, a r) * (q * b s * (∑ t, v t)) := by rw [← Finset.sum_mul]
      _ = _ := by ring
  simp_rw [hi]
  calc
    (∑ s, (q * (∑ r, a r) * b s) * (∑ t, v t)) =
        ∑ s, b s * (q * (∑ r, a r) * (∑ t, v t)) := by
      apply Finset.sum_congr rfl
      intro s _
      ring
    _ = (∑ s, b s) * (q * (∑ r, a r) * (∑ t, v t)) := by rw [← Finset.sum_mul]
    _ = _ := by ring

theorem seedPureMatrixInput_forget_physical {d c e f : ℕ} (a : ProbabilityLaw (Fin d))
    (ρA : Density (Fin c)) (ρB : Density (Fin e)) (ξ : Density (Fin f)) :
    forgetPrivateBobMatrixInput e (d * c) (d * e)
      (forgetPrivateAliceMatrixInput (c * f) (d * c) (e * (d * e))
        (forgetPrivateAliceMatrixInput d ((c * f) * (d * c)) (e * (d * e))
          (seedPureMatrixInput a ρA ρB ξ).mat)) =
      ((copiedSeedAncillas a ρA ρB).tensor ξ).mat := by
  rw [seedPureMatrixInput, privateLabelJointDensity_forget]
  ext x y
  rcases x with ⟨⟨xA,xB⟩,u⟩
  rcases y with ⟨⟨yA,yB⟩,u'⟩
  change (∑ t : Fin e, ∑ r : Fin (c * f),
    jointLabelDephasedMatrix (matrixSeedLabel d c f) (pureFactorMatrixInput a ρA ρB ξ).mat
      (((privateAliceLocalEquiv (c * f) (d * c)).symm (r,xA),
        (privateAliceLocalEquiv e (d * e)).symm (t,xB)),u)
      (((privateAliceLocalEquiv (c * f) (d * c)).symm (r,yA),
        (privateAliceLocalEquiv e (d * e)).symm (t,yB)),u')) = _
  simp_rw [sum_private_product, jointLabelDephasedMatrix, matrixSeedLabel,
    Equiv.apply_symm_apply, pureFactorMatrixInput_apply]
  change (∑ t : Fin e, ∑ r : Fin c, ∑ s : Fin f,
    if (privateAliceLocalEquiv d c xA).1 = (privateAliceLocalEquiv d c yA).1 then
      a.coherentSeedMatrix
        ((privateAliceLocalEquiv d c xA).1,(privateAliceLocalEquiv d e xB).1)
        ((privateAliceLocalEquiv d c yA).1,(privateAliceLocalEquiv d e yB).1) *
      (factorMatrix ρA (r,(privateAliceLocalEquiv d c xA).2)
        (r,(privateAliceLocalEquiv d c yA).2) *
       factorMatrix ρB (t,(privateAliceLocalEquiv d e xB).2)
        (t,(privateAliceLocalEquiv d e yB).2)) * factorMatrix ξ (s,u) (s,u') else 0) = _
  have hA := congrArg (fun M => M (privateAliceLocalEquiv d c xA).2
    (privateAliceLocalEquiv d c yA).2) (factorMatrix_active ρA)
  have hB := congrArg (fun M => M (privateAliceLocalEquiv d e xB).2
    (privateAliceLocalEquiv d e yB).2) (factorMatrix_active ρB)
  have hξ := congrArg (fun M => M u u') (factorMatrix_active ξ)
  have hs := coherentSeed_label_dephase a
    ((privateAliceLocalEquiv d c xA).1,(privateAliceLocalEquiv d e xB).1)
    ((privateAliceLocalEquiv d c yA).1,(privateAliceLocalEquiv d e yB).1)
  change (∑ r, factorMatrix ρA (r,_) (r,_)) = _ at hA
  change (∑ r, factorMatrix ρB (r,_) (r,_)) = _ at hB
  change (∑ r, factorMatrix ξ (r,u) (r,u')) = _ at hξ
  have hrhs : ((copiedSeedAncillas a ρA ρB).tensor ξ).mat ((xA,xB),u) ((yA,yB),u') =
      a.copiedMatrix
        ((privateAliceLocalEquiv d c xA).1,(privateAliceLocalEquiv d e xB).1)
        ((privateAliceLocalEquiv d c yA).1,(privateAliceLocalEquiv d e yB).1) *
      (ρA.mat (privateAliceLocalEquiv d c xA).2 (privateAliceLocalEquiv d c yA).2 *
        ρB.mat (privateAliceLocalEquiv d e xB).2 (privateAliceLocalEquiv d e yB).2) *
          ξ.mat u u' := by
    rfl
  rw [hrhs]
  by_cases h : (privateAliceLocalEquiv d c xA).1 = (privateAliceLocalEquiv d c yA).1
  · simp only [if_pos h] at hs ⊢
    rw [independent_three_sums, hA, hB, hξ, hs]
  · simp only [if_neg h] at hs ⊢
    rw [← hs]
    simp only [Finset.sum_const_zero, zero_mul]

theorem seedPureProtocol_physical_output {p : ℝ} {d c e f af bf : ℕ}
    (P : FiniteKeyProtocol p (d * c) (d * e) af bf)
    (a : ProbabilityLaw (Fin d)) (ρA : Density (Fin c)) (ρB : Density (Fin e))
    (ξ : Density (Fin f)) :
    forgetPrivateBobOutput e P
      (forgetPrivateAliceOutput (c * f) (withPrivateBob e P)
        (forgetPrivateAliceOutput d (withPrivateAlice (c * f) (withPrivateBob e P))
          (PublicHistory.localPriorEveMatrix_B (seedPureProtocol (f := f) P)
            (seedPureMatrixInput a ρA ρB ξ).mat))) =
      PublicHistory.localPriorEveMatrix_B P ((copiedSeedAncillas a ρA ρB).tensor ξ).mat := by
  dsimp only [seedPureProtocol]
  rw [withPrivateAlice_forget_matrix, withPrivateAlice_forget_matrix,
    withPrivateBob_forget_matrix, seedPureMatrixInput_forget_physical]

end QuantumProver.AmplitudeDamping.SecretKey.InitialSeedAncillas

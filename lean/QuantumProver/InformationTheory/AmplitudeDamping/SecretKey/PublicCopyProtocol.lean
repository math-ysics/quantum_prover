import QuantumProver.InformationTheory.AmplitudeDamping.SecretKey.LaneMergeHistory

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix Kronecker

namespace QuantumProver.AmplitudeDamping.SecretKey.MatrixPublicCopy

open QuantumProver.AmplitudeDamping.FiniteModel
open PublicHistory PhysicalProtocol PhysicalProtocol.FiniteKeyProtocol
open IndependentLanes BlockLossHistory

theorem sum_sigma_any_B {I : Type*} [Fintype I] {T : I → Type*}
    [∀ i, Fintype (T i)] {M : Type*} [AddCommMonoid M]
    (s : Fintype ((i : I) × T i)) (f : ((i : I) × T i) → M) :
    (@Finset.univ _ s).sum f = ∑ i, ∑ h, f ⟨i,h⟩ := by
  have hs : s = Sigma.instFintype := Subsingleton.elim _ _
  rw [hs]
  exact Fintype.sum_sigma f

theorem sum_prod_any_B {I T : Type*} [Fintype I] [Fintype T]
    {M : Type*} [AddCommMonoid M] (s : Fintype (I × T)) (f : I × T → M) :
    (@Finset.univ _ s).sum f = ∑ i, ∑ t, f (i,t) := by
  have hs : s = instFintypeProd I T := Subsingleton.elim _ _
  rw [hs]
  exact Fintype.sum_prod_type f

def embeddingMatrix_B {I O : Type*} [DecidableEq O] (f : I → O) :
    Matrix O I ℂ := fun o i => if o = f i then 1 else 0

theorem embeddingMatrix_complete_B {I O : Type*} [Fintype O]
    [DecidableEq I] [DecidableEq O] (f : I → O) (hf : Function.Injective f) :
    (embeddingMatrix_B f)ᴴ * embeddingMatrix_B f = 1 := by
  classical
  ext i j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, embeddingMatrix_B]
  rw [Finset.sum_eq_single (f i)]
  · by_cases h : i = j
    · subst j; simp
    · have hij : f i ≠ f j := fun h' => h (hf h')
      simp [h, hij, Matrix.one_apply]
  · intro o _ ho
    simp [ho]
  · simp

def isometryInstrument_B {i o : ℕ} (M : Matrix (Fin o) (Fin i) ℂ)
    (hM : Mᴴ * M = 1) : KrausInstrument i o 1 where
  operator := fun _ => M
  complete := by simpa only [Fintype.sum_unique] using hM

def postLocal_B {p : ℝ} {n af bf ag bg : ℕ}
    (M : Matrix (Fin ag) (Fin af) ℂ) (hM : Mᴴ * M = 1)
    (N : Matrix (Fin bg) (Fin bf) ℂ) (hN : Nᴴ * N = 1) :
    {a b : ℕ} → FiniteBlockProtocolB p n a b af bf →
      FiniteBlockProtocolB p n a b ag bg
  | _, _, .done _ _ =>
      .alice (isometryInstrument_B M hM) fun _ =>
        .bob (isometryInstrument_B N hN) fun _ => .done ag bg
  | _, _, .alice K next => .alice K fun j => postLocal_B M hM N hN (next j)
  | _, _, .bob K next => .bob K fun j => postLocal_B M hM N hN (next j)
  | _, _, .blockCall next => .blockCall (postLocal_B M hM N hN next)

theorem postLocal_calls_B {p : ℝ} {n a b af bf ag bg : ℕ}
    (P : FiniteBlockProtocolB p n a b af bf)
    (M : Matrix (Fin ag) (Fin af) ℂ) (hM : Mᴴ * M = 1)
    (N : Matrix (Fin bg) (Fin bf) ℂ) (hN : Nᴴ * N = 1) :
    (postLocal_B M hM N hN P).calls = P.calls := by
  induction P with
  | done a b => simp [postLocal_B, FiniteBlockProtocolB.calls]
  | alice K next ih => simp only [postLocal_B, FiniteBlockProtocolB.calls, ih]
  | bob K next ih => simp only [postLocal_B, FiniteBlockProtocolB.calls, ih]
  | blockCall next ih => simp only [postLocal_B, FiniteBlockProtocolB.calls, ih]

theorem postLocal_output_B {p : ℝ} {n a b af bf ag bg : ℕ}
    (P : FiniteBlockProtocolB p n a b af bf)
    (M : Matrix (Fin ag) (Fin af) ℂ) (hM : Mᴴ * M = 1)
    (N : Matrix (Fin bg) (Fin bf) ℂ) (hN : Nᴴ * N = 1) :
    ∀ ρ, (postLocal_B M hM N hN P).output ρ =
      (M ⊗ₖ N) * P.output ρ * (M ⊗ₖ N)ᴴ := by
  induction P with
  | done a b =>
      intro ρ
      simp only [postLocal_B, FiniteBlockProtocolB.output, isometryInstrument_B,
        Fintype.sum_unique, aliceOperator, bobOperator]
      have hp : ((1 : Matrix (Fin ag) (Fin ag) ℂ) ⊗ₖ N) *
          (M ⊗ₖ (1 : Matrix (Fin b) (Fin b) ℂ)) = M ⊗ₖ N := by
        rw [← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one]
      simpa only [Matrix.conjTranspose_mul, Matrix.mul_assoc] using
        congrArg (fun S => S * ρ * Sᴴ) hp
  | alice K next ih =>
      intro ρ
      simp only [postLocal_B, FiniteBlockProtocolB.output, ih,
        Matrix.mul_sum, Matrix.sum_mul]
  | bob K next ih =>
      intro ρ
      simp only [postLocal_B, FiniteBlockProtocolB.output, ih,
        Matrix.mul_sum, Matrix.sum_mul]
  | blockCall next ih => intro ρ; exact ih M hM N hN _

end QuantumProver.AmplitudeDamping.SecretKey.MatrixPublicCopy

namespace QuantumProver.AmplitudeDamping.FiniteModel.FiniteBlockProtocolB

open QuantumProver.AmplitudeDamping.SecretKey.MatrixPublicCopy QuantumProver.AmplitudeDamping.SecretKey.PublicHistory

def publicHistory_B {p : ℝ} {n a b af bf : ℕ}
    (R : FiniteBlockProtocolB p n a b af bf) : Type :=
  match R with
  | .done _ _ => Unit
  | .alice _ next => (j : _) × (next j).publicHistory_B
  | .bob _ next => (j : _) × (next j).publicHistory_B
  | .blockCall next => next.publicHistory_B

instance publicHistoryFintype_B {p : ℝ} {n a b af bf : ℕ}
    (R : FiniteBlockProtocolB p n a b af bf) : Fintype R.publicHistory_B :=
  match R with
  | .done _ _ => inferInstanceAs (Fintype Unit)
  | .alice (k := k) _ next =>
      letI : ∀ j, Fintype (next j).publicHistory_B := fun j => publicHistoryFintype_B (next j)
      inferInstanceAs (Fintype ((j : Fin k) × (next j).publicHistory_B))
  | .bob (k := k) _ next =>
      letI : ∀ j, Fintype (next j).publicHistory_B := fun j => publicHistoryFintype_B (next j)
      inferInstanceAs (Fintype ((j : Fin k) × (next j).publicHistory_B))
  | .blockCall next => publicHistoryFintype_B next

instance publicHistoryDecidableEq_B {p : ℝ} {n a b af bf : ℕ}
    (R : FiniteBlockProtocolB p n a b af bf) : DecidableEq R.publicHistory_B :=
  Classical.decEq _

attribute [reducible] publicHistory_B

def publicBranch_B {p : ℝ} {n a b af bf : ℕ}
    (R : FiniteBlockProtocolB p n a b af bf) :
    BipartiteMatrix a b → R.publicHistory_B → BipartiteMatrix af bf :=
  match R with
  | .done _ _ => fun ρ _ => ρ
  | .alice (b := b₀) K next => fun ρ h =>
      (next h.1).publicBranch_B
        (aliceOperator (b := b₀) (K.operator h.1) * ρ *
          (aliceOperator (b := b₀) (K.operator h.1))ᴴ) h.2
  | .bob (a := a₀) K next => fun ρ h =>
      (next h.1).publicBranch_B
        (bobOperator (a := a₀) (K.operator h.1) * ρ *
          (bobOperator (a := a₀) (K.operator h.1))ᴴ) h.2
  | .blockCall (a := a₀) (b := b₀) next => fun ρ h =>
      next.publicBranch_B (krausSumB (sequentialCallsKrausB p n a₀ b₀) ρ) h

end QuantumProver.AmplitudeDamping.FiniteModel.FiniteBlockProtocolB

namespace QuantumProver.AmplitudeDamping.SecretKey.MatrixPublicCopy

open QuantumProver.AmplitudeDamping.FiniteModel

variable {H G : Type*} [Fintype H] [Fintype G] [DecidableEq H] [DecidableEq G]

def matrixIndex_B (T : Type*) [Finite T] : Fin (Nat.card T) ≃ T := by
  letI := Fintype.ofFinite T
  exact (finCongr (Nat.card_eq_fintype_card)).trans (finiteIndexB T)

def flagMatrix_B (d : ℕ) (h : H) :
    Matrix (Fin (Nat.card (H × Fin d))) (Fin d) ℂ := by
  letI : DecidableEq H := Classical.decEq H
  exact (PublicHistory.attachFlag_B (A := Fin d) h).submatrix (matrixIndex_B _) id

theorem flagMatrix_complete_B (d : ℕ) (h : H) :
    (flagMatrix_B d h)ᴴ * flagMatrix_B d h = 1 := by
  letI : DecidableEq H := Classical.decEq H
  simp only [flagMatrix_B, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv,
    PublicHistory.attachFlag_complete_B, Matrix.submatrix_id_id]

def flagEmbeddingMatrix_B (d : ℕ) (f : H → G) :
    Matrix (Fin (Nat.card (G × Fin d))) (Fin (Nat.card (H × Fin d))) ℂ := by
  letI : DecidableEq G := Classical.decEq G
  exact (embeddingMatrix_B (fun x : H × Fin d => (f x.1, x.2))).submatrix
    (matrixIndex_B _) (matrixIndex_B _)

theorem flagEmbeddingMatrix_complete_B (d : ℕ) (f : H → G)
    (hf : Function.Injective f) :
    (flagEmbeddingMatrix_B d f)ᴴ * flagEmbeddingMatrix_B d f = 1 := by
  letI : DecidableEq H := Classical.decEq H
  letI : DecidableEq G := Classical.decEq G
  have hm : Function.Injective (fun x : H × Fin d => (f x.1, x.2)) := by
    intro x y h
    exact Prod.ext (hf (congrArg (fun z : G × Fin d => z.1) h))
      (congrArg (fun z : G × Fin d => z.2) h)
  simp only [flagEmbeddingMatrix_B, Matrix.conjTranspose_submatrix,
    Matrix.submatrix_mul_equiv, embeddingMatrix_complete_B _ hm,
    Matrix.submatrix_one_equiv]

theorem embeddingMatrix_attachFlag_B (d : ℕ) (f : H → G) (h : H) :
    embeddingMatrix_B (fun x : H × Fin d => (f x.1, x.2)) *
      PublicHistory.attachFlag_B (A := Fin d) h = PublicHistory.attachFlag_B (f h) := by
  classical
  ext ⟨g,a⟩ i
  by_cases hg : g = f h
  all_goals
  simp [embeddingMatrix_B, PublicHistory.attachFlag_B, Matrix.mul_apply,
    Matrix.one_apply, Fintype.sum_prod_type, ite_mul, mul_ite, eq_comm, hg]

theorem flagEmbeddingMatrix_flag_B (d : ℕ) (f : H → G) (h : H) :
    flagEmbeddingMatrix_B d f * flagMatrix_B d h = flagMatrix_B d (f h) := by
  letI : DecidableEq H := Classical.decEq H
  letI : DecidableEq G := Classical.decEq G
  rw [flagEmbeddingMatrix_B, flagMatrix_B, Matrix.submatrix_mul_equiv,
    embeddingMatrix_attachFlag_B]
  rfl

theorem embed_copy_sum_B (af bf : ℕ) (f : H → G)
    (σ : H → BipartiteMatrix af bf) :
    (flagEmbeddingMatrix_B af f ⊗ₖ flagEmbeddingMatrix_B bf f) *
        (∑ h, (flagMatrix_B af h ⊗ₖ flagMatrix_B bf h) * σ h *
          (flagMatrix_B af h ⊗ₖ flagMatrix_B bf h)ᴴ) *
      (flagEmbeddingMatrix_B af f ⊗ₖ flagEmbeddingMatrix_B bf f)ᴴ =
      ∑ h, (flagMatrix_B af (f h) ⊗ₖ flagMatrix_B bf (f h)) * σ h *
        (flagMatrix_B af (f h) ⊗ₖ flagMatrix_B bf (f h))ᴴ := by
  rw [Matrix.mul_sum, Matrix.sum_mul]
  apply Finset.sum_congr rfl
  intro h _
  have hp : (flagEmbeddingMatrix_B af f ⊗ₖ flagEmbeddingMatrix_B bf f) *
      (flagMatrix_B af h ⊗ₖ flagMatrix_B bf h) =
      flagMatrix_B af (f h) ⊗ₖ flagMatrix_B bf (f h) := by
    rw [← Matrix.mul_kronecker_mul, flagEmbeddingMatrix_flag_B, flagEmbeddingMatrix_flag_B]
  simpa only [Matrix.conjTranspose_mul, Matrix.mul_assoc] using
    congrArg (fun S => S * σ h * Sᴴ) hp

end QuantumProver.AmplitudeDamping.SecretKey.MatrixPublicCopy

namespace QuantumProver.AmplitudeDamping.FiniteModel.FiniteBlockProtocolB

open QuantumProver.AmplitudeDamping.SecretKey.MatrixPublicCopy

def copyPublic {p : ℝ} {n a b af bf : ℕ} (R : FiniteBlockProtocolB p n a b af bf) :
    FiniteBlockProtocolB p n a b
      (Nat.card (R.publicHistory_B × Fin af))
      (Nat.card (R.publicHistory_B × Fin bf)) :=
  match R with
  | .done a b =>
      postLocal_B (flagMatrix_B a (H := Unit) ()) (flagMatrix_complete_B a ())
        (flagMatrix_B b (H := Unit) ()) (flagMatrix_complete_B b ()) (.done a b)
  | .alice (af := af₀) (bf := bf₀) (k := k) K next =>
      .alice K fun j =>
        let f : (next j).publicHistory_B → ((z : Fin k) × (next z).publicHistory_B) :=
          fun h => ⟨j,h⟩
        let hf : Function.Injective f := fun _ _ h => eq_of_heq (Sigma.mk.inj_iff.mp h).2
        postLocal_B (flagEmbeddingMatrix_B af₀ f) (flagEmbeddingMatrix_complete_B af₀ f hf)
          (flagEmbeddingMatrix_B bf₀ f) (flagEmbeddingMatrix_complete_B bf₀ f hf)
          (next j).copyPublic
  | .bob (af := af₀) (bf := bf₀) (k := k) K next =>
      .bob K fun j =>
        let f : (next j).publicHistory_B → ((z : Fin k) × (next z).publicHistory_B) :=
          fun h => ⟨j,h⟩
        let hf : Function.Injective f := fun _ _ h => eq_of_heq (Sigma.mk.inj_iff.mp h).2
        postLocal_B (flagEmbeddingMatrix_B af₀ f) (flagEmbeddingMatrix_complete_B af₀ f hf)
          (flagEmbeddingMatrix_B bf₀ f) (flagEmbeddingMatrix_complete_B bf₀ f hf)
          (next j).copyPublic
  | .blockCall next => .blockCall next.copyPublic

theorem copyPublic_calls {p : ℝ} {n a b af bf : ℕ}
    (R : FiniteBlockProtocolB p n a b af bf) : R.copyPublic.calls = R.calls := by
  induction R with
  | done a b =>
      dsimp only [copyPublic, publicHistory_B, publicHistoryFintype_B]
      apply postLocal_calls_B
  | alice K next ih =>
      dsimp only [copyPublic, publicHistory_B, publicHistoryFintype_B, FiniteBlockProtocolB.calls]
      congr 1
      funext j
      rw [postLocal_calls_B]
      exact ih j
  | bob K next ih =>
      dsimp only [copyPublic, publicHistory_B, publicHistoryFintype_B, FiniteBlockProtocolB.calls]
      congr 1
      funext j
      rw [postLocal_calls_B]
      exact ih j
  | blockCall next ih => exact congrArg (fun x : ℕ => x + 1) ih

theorem copyPublic_scalar_calls_le {p : ℝ} {n a b af bf : ℕ}
    (R : FiniteBlockProtocolB p n a b af bf) : R.copyPublic.represented_toMatrix.calls ≤ n * R.calls := by
  simpa only [copyPublic_calls] using R.copyPublic.toMatrix_calls_le

def copiedMatrix_B {p : ℝ} {n a b af bf : ℕ}
    (R : FiniteBlockProtocolB p n a b af bf) (ρ : BipartiteMatrix a b) :
    BipartiteMatrix (Nat.card (R.publicHistory_B × Fin af))
      (Nat.card (R.publicHistory_B × Fin bf)) :=
  ∑ h, (flagMatrix_B af h ⊗ₖ flagMatrix_B bf h) * R.publicBranch_B ρ h *
    (flagMatrix_B af h ⊗ₖ flagMatrix_B bf h)ᴴ

theorem copyPublic_output {p : ℝ} {n a b af bf : ℕ}
    (R : FiniteBlockProtocolB p n a b af bf) :
    ∀ ρ, R.copyPublic.output ρ = R.copiedMatrix_B ρ := by
  induction R with
  | done a b =>
      intro ρ
      dsimp only [copyPublic, publicHistory_B, publicHistoryFintype_B]
      rw [postLocal_output_B]
      simp only [copiedMatrix_B, publicBranch_B, FiniteBlockProtocolB.output,
        Fintype.sum_unique]
      all_goals rfl
  | @alice a b ao af bf k K next ih =>
      intro ρ
      simp only [copyPublic, FiniteBlockProtocolB.output, postLocal_output_B, ih]
      unfold copiedMatrix_B
      dsimp only [publicHistory_B, publicBranch_B]
      rw [sum_sigma_any_B]
      apply Finset.sum_congr rfl
      intro j _
      exact embed_copy_sum_B af bf
        (fun h : (next j).publicHistory_B =>
          @Sigma.mk (Fin k) (fun z => (next z).publicHistory_B) j h) _
  | @bob a b bo af bf k K next ih =>
      intro ρ
      simp only [copyPublic, FiniteBlockProtocolB.output, postLocal_output_B, ih]
      unfold copiedMatrix_B
      dsimp only [publicHistory_B, publicBranch_B]
      rw [sum_sigma_any_B]
      apply Finset.sum_congr rfl
      intro j _
      exact embed_copy_sum_B af bf
        (fun h : (next j).publicHistory_B =>
          @Sigma.mk (Fin k) (fun z => (next z).publicHistory_B) j h) _
  | blockCall next ih => intro ρ; exact ih _

end QuantumProver.AmplitudeDamping.FiniteModel.FiniteBlockProtocolB

namespace QuantumProver.AmplitudeDamping.FiniteModel.FiniteBlockProtocolB

open QuantumProver.AmplitudeDamping.SecretKey.MatrixPublicCopy
open QuantumProver.AmplitudeDamping.SecretKey.IndependentLanes QuantumProver.AmplitudeDamping.SecretKey.BlockLossHistory QuantumProver.AmplitudeDamping.SecretKey.LaneMergeHistory

def privateHistory_B {p : ℝ} {n a b af bf : ℕ}
    (R : FiniteBlockProtocolB p n a b af bf) : Type :=
  match R with
  | .done _ _ => Unit
  | .alice _ next => (j : _) × (next j).privateHistory_B
  | .bob _ next => (j : _) × (next j).privateHistory_B
  | .blockCall next => (Fin n → Fin 2) × next.privateHistory_B

instance privateHistoryFintype_B {p : ℝ} {n a b af bf : ℕ}
    (R : FiniteBlockProtocolB p n a b af bf) : Fintype R.privateHistory_B :=
  match R with
  | .done _ _ => inferInstanceAs (Fintype Unit)
  | .alice (k := k) _ next =>
      letI : ∀ j, Fintype (next j).privateHistory_B := fun j => privateHistoryFintype_B (next j)
      inferInstanceAs (Fintype ((j : Fin k) × (next j).privateHistory_B))
  | .bob (k := k) _ next =>
      letI : ∀ j, Fintype (next j).privateHistory_B := fun j => privateHistoryFintype_B (next j)
      inferInstanceAs (Fintype ((j : Fin k) × (next j).privateHistory_B))
  | .blockCall next =>
      letI := privateHistoryFintype_B next
      inferInstanceAs (Fintype ((Fin n → Fin 2) × next.privateHistory_B))

instance privateHistoryDecidableEq_B {p : ℝ} {n a b af bf : ℕ}
    (R : FiniteBlockProtocolB p n a b af bf) : DecidableEq R.privateHistory_B :=
  Classical.decEq _

attribute [reducible] privateHistory_B

def publicTranscript_B {p : ℝ} {n a b af bf : ℕ}
    (R : FiniteBlockProtocolB p n a b af bf) : R.privateHistory_B → R.publicHistory_B :=
  match R with
  | .done _ _ => fun _ => ()
  | .alice _ next => fun h => ⟨h.1, (next h.1).publicTranscript_B h.2⟩
  | .bob _ next => fun h => ⟨h.1, (next h.1).publicTranscript_B h.2⟩
  | .blockCall next => fun h => next.publicTranscript_B h.2

def historyOperator_B {p : ℝ} {n a b af bf : ℕ}
    (R : FiniteBlockProtocolB p n a b af bf) :
    R.privateHistory_B → Matrix (Fin af × Fin bf) (Fin a × Fin b) ℂ :=
  match R with
  | .done _ _ => fun _ => 1
  | .alice (b := b₀) K next => fun h =>
      (next h.1).historyOperator_B h.2 * aliceOperator (b := b₀) (K.operator h.1)
  | .bob (a := a₀) K next => fun h =>
      (next h.1).historyOperator_B h.2 * bobOperator (a := a₀) (K.operator h.1)
  | .blockCall (a := a₀) (b := b₀) next => fun h =>
      next.historyOperator_B h.2 * sequentialCallsKrausB p n a₀ b₀ h.1

def recordedHistoryOperator_B {p : ℝ} {n a b af bf : ℕ}
    (R : FiniteBlockProtocolB p n a b af bf) (h : R.privateHistory_B) :
    Matrix (Fin (Nat.card (R.publicHistory_B × Fin af)) ×
      Fin (Nat.card (R.publicHistory_B × Fin bf))) (Fin a × Fin b) ℂ :=
  (flagMatrix_B af (R.publicTranscript_B h) ⊗ₖ flagMatrix_B bf (R.publicTranscript_B h)) *
    R.historyOperator_B h

theorem output_finite_sum_B {p : ℝ} {n a b af bf : ℕ}
    (R : FiniteBlockProtocolB p n a b af bf) {T : Type*} [Fintype T] :
    ∀ σ : T → BipartiteMatrix a b, R.output (∑ t, σ t) = ∑ t, R.output (σ t) := by
  induction R with
  | done a b => intro σ; rfl
  | alice K next ih =>
      intro σ
      simp only [FiniteBlockProtocolB.output, Matrix.mul_sum, Matrix.sum_mul, ih]
      exact Finset.sum_comm
  | bob K next ih =>
      intro σ
      simp only [FiniteBlockProtocolB.output, Matrix.mul_sum, Matrix.sum_mul, ih]
      exact Finset.sum_comm
  | blockCall next ih =>
      intro σ
      simp only [FiniteBlockProtocolB.output, krausSumB, Matrix.mul_sum, Matrix.sum_mul]
      rw [Finset.sum_comm]
      exact ih _

theorem copyPublic_output_history_B {p : ℝ} {n a b af bf : ℕ}
    (R : FiniteBlockProtocolB p n a b af bf) :
    ∀ ρ, R.copyPublic.output ρ =
      ∑ h, R.recordedHistoryOperator_B h * ρ * (R.recordedHistoryOperator_B h)ᴴ := by
  induction R with
  | done a b =>
      intro ρ
      rw [copyPublic, postLocal_output_B]
      simp [recordedHistoryOperator_B, publicTranscript_B, historyOperator_B,
        FiniteBlockProtocolB.output]
      all_goals rfl
  | @alice a b ao af bf k K next ih =>
      intro ρ
      simp only [copyPublic, FiniteBlockProtocolB.output, postLocal_output_B, ih]
      change _ = ∑ h : (j : Fin k) × (next j).privateHistory_B,
        (FiniteBlockProtocolB.alice K next).recordedHistoryOperator_B h * ρ *
          ((FiniteBlockProtocolB.alice K next).recordedHistoryOperator_B h)ᴴ
      rw [Fintype.sum_sigma]
      apply Finset.sum_congr rfl
      intro j _
      rw [Matrix.mul_sum, Matrix.sum_mul]
      apply Finset.sum_congr rfl
      intro h _
      let f : (next j).publicHistory_B → ((z : Fin k) × (next z).publicHistory_B) :=
        fun t => ⟨j,t⟩
      have hop : (flagEmbeddingMatrix_B af f ⊗ₖ flagEmbeddingMatrix_B bf f) *
          (next j).recordedHistoryOperator_B h * aliceOperator (b := b) (K.operator j) =
          (FiniteBlockProtocolB.alice K next).recordedHistoryOperator_B ⟨j,h⟩ := by
        simp only [recordedHistoryOperator_B, publicTranscript_B, historyOperator_B]
        rw [← Matrix.mul_assoc, ← Matrix.mul_kronecker_mul,
          flagEmbeddingMatrix_flag_B, flagEmbeddingMatrix_flag_B]
        simp only [Matrix.mul_assoc, f]
        all_goals rfl
      simpa only [Matrix.conjTranspose_mul, Matrix.mul_assoc] using
        congrArg (fun S => S * ρ * Sᴴ) hop
  | @bob a b bo af bf k K next ih =>
      intro ρ
      simp only [copyPublic, FiniteBlockProtocolB.output, postLocal_output_B, ih]
      change _ = ∑ h : (j : Fin k) × (next j).privateHistory_B,
        (FiniteBlockProtocolB.bob K next).recordedHistoryOperator_B h * ρ *
          ((FiniteBlockProtocolB.bob K next).recordedHistoryOperator_B h)ᴴ
      rw [Fintype.sum_sigma]
      apply Finset.sum_congr rfl
      intro j _
      rw [Matrix.mul_sum, Matrix.sum_mul]
      apply Finset.sum_congr rfl
      intro h _
      let f : (next j).publicHistory_B → ((z : Fin k) × (next z).publicHistory_B) :=
        fun t => ⟨j,t⟩
      have hop : (flagEmbeddingMatrix_B af f ⊗ₖ flagEmbeddingMatrix_B bf f) *
          (next j).recordedHistoryOperator_B h * bobOperator (a := a) (K.operator j) =
          (FiniteBlockProtocolB.bob K next).recordedHistoryOperator_B ⟨j,h⟩ := by
        simp only [recordedHistoryOperator_B, publicTranscript_B, historyOperator_B]
        rw [← Matrix.mul_assoc, ← Matrix.mul_kronecker_mul,
          flagEmbeddingMatrix_flag_B, flagEmbeddingMatrix_flag_B]
        simp only [Matrix.mul_assoc, f]
        all_goals rfl
      simpa only [Matrix.conjTranspose_mul, Matrix.mul_assoc] using
        congrArg (fun S => S * ρ * Sᴴ) hop
  | @blockCall a b af bf next ih =>
      intro ρ
      change next.copyPublic.output (krausSumB (sequentialCallsKrausB p n a b) ρ) = _
      rw [krausSumB, output_finite_sum_B]
      simp_rw [ih]
      simp only [privateHistory_B, recordedHistoryOperator_B,
        publicTranscript_B, historyOperator_B, Matrix.conjTranspose_mul, Matrix.mul_assoc]
      rw [sum_prod_any_B]
      all_goals rfl

end QuantumProver.AmplitudeDamping.FiniteModel.FiniteBlockProtocolB

namespace QuantumProver.AmplitudeDamping.SecretKey.MatrixPublicCopy

open QuantumProver.AmplitudeDamping.FiniteModel
open IndependentLanes BlockLossHistory LaneMergeHistory
open PhysicalProtocol PhysicalProtocol.FiniteKeyProtocol PublicHistory

def keyTree_B {p : ℝ} {n a b af bf : ℕ}
    (R : FiniteBlockProtocolB p n a b af bf) : FiniteKeyProtocol p a b af bf :=
  match R with
  | .done a b => .done a b
  | .alice K next => .alice { op := K.operator, complete := K.complete } fun j => keyTree_B (next j)
  | .bob K next => .bob { op := K.operator, complete := K.complete } fun j => keyTree_B (next j)
  | .blockCall (a := a₀) (b := b₀) next =>
      sequentialThenKey_B p n a₀ b₀ af bf (keyTree_B next)

attribute [reducible] keyTree_B

theorem keyTree_eq_blockExpansion_B {p : ℝ} {n a b af bf : ℕ}
    (R : FiniteBlockProtocolB p n a b af bf) : keyTree_B R = blockExpansion_B R := by
  induction R with
  | done a b => rfl
  | alice K next ih =>
      simp only [keyTree_B, blockExpansion_B, FiniteBlockProtocolB.represented_toMatrix, fromQuantum_B]
      congr 1
      funext j
      exact ih j
  | bob K next ih =>
      simp only [keyTree_B, blockExpansion_B, FiniteBlockProtocolB.represented_toMatrix, fromQuantum_B]
      congr 1
      funext j
      exact ih j
  | blockCall next ih =>
      simp only [keyTree_B, blockExpansion_B, FiniteBlockProtocolB.represented_toMatrix,
        fromQuantum_sequential_B]
      rw [ih]
      rfl

def keyPublicEquiv_B {p : ℝ} {n a b af bf : ℕ}
    (R : FiniteBlockProtocolB p n a b af bf) :
    (keyTree_B R).comparisonPublicHistory_B ≃ R.publicHistory_B :=
  match R with
  | .done _ _ => Equiv.refl _
  | .alice _ next => Equiv.sigmaCongrRight fun j => keyPublicEquiv_B (next j)
  | .bob _ next => Equiv.sigmaCongrRight fun j => keyPublicEquiv_B (next j)
  | .blockCall (a := a₀) (b := b₀) next =>
      (sequentialPublicEquiv_B p n a₀ b₀ af bf (keyTree_B next)).trans (keyPublicEquiv_B next)

def keyEnvironmentEquiv_B {p : ℝ} {n a b af bf : ℕ}
    (R : FiniteBlockProtocolB p n a b af bf) :
    (keyTree_B R).Environment ≃ R.privateHistory_B :=
  match R with
  | .done _ _ => Equiv.refl _
  | .alice _ next => Equiv.sigmaCongrRight fun j => keyEnvironmentEquiv_B (next j)
  | .bob _ next => Equiv.sigmaCongrRight fun j => keyEnvironmentEquiv_B (next j)
  | .blockCall (a := a₀) (b := b₀) next =>
      (sequentialEnvironmentEquiv_B p n a₀ b₀ af bf (keyTree_B next)).trans
        ((Equiv.refl (Fin n → Fin 2)).prodCongr (keyEnvironmentEquiv_B next))

theorem keyTree_historyOperator_B {p : ℝ} {n a b af bf : ℕ}
    (R : FiniteBlockProtocolB p n a b af bf) :
    ∀ h, (keyTree_B R).historyKraus_B h = R.historyOperator_B (keyEnvironmentEquiv_B R h) := by
  induction R with
  | done a b => intro h; rfl
  | alice K next ih =>
      intro h
      rcases h with ⟨j,t⟩
      change (keyTree_B (next j)).historyKraus_B t * aliceOperator (K.operator j) =
        (next j).historyOperator_B (keyEnvironmentEquiv_B (next j) t) * aliceOperator (K.operator j)
      rw [ih j]
  | bob K next ih =>
      intro h
      rcases h with ⟨j,t⟩
      change (keyTree_B (next j)).historyKraus_B t * bobOperator (K.operator j) =
        (next j).historyOperator_B (keyEnvironmentEquiv_B (next j) t) * bobOperator (K.operator j)
      rw [ih j]
  | @blockCall a b af bf next ih =>
      intro h
      change (sequentialThenKey_B p n a b af bf (keyTree_B next)).historyKraus_B h = _
      rw [sequentialThenKey_historyKraus_B]
      change (keyTree_B next).historyKraus_B
        (sequentialEnvironmentEquiv_B p n a b af bf (keyTree_B next) h).2 *
          sequentialCallsKrausB p n a b
            (sequentialEnvironmentEquiv_B p n a b af bf (keyTree_B next) h).1 = _
      rw [ih]
      rfl

theorem keyTree_publicTranscript_B {p : ℝ} {n a b af bf : ℕ}
    (R : FiniteBlockProtocolB p n a b af bf) :
    ∀ h, keyPublicEquiv_B R ((keyTree_B R).publicTranscript_B h) =
      R.publicTranscript_B (keyEnvironmentEquiv_B R h) := by
  induction R with
  | done a b => intro h; rfl
  | alice K next ih =>
      intro h
      rcases h with ⟨j,t⟩
      change @Sigma.mk _ (fun z => (next z).publicHistory_B) j
        (keyPublicEquiv_B (next j) ((keyTree_B (next j)).publicTranscript_B t)) =
        @Sigma.mk _ (fun z => (next z).publicHistory_B) j
          ((next j).publicTranscript_B (keyEnvironmentEquiv_B (next j) t))
      rw [ih j]
  | bob K next ih =>
      intro h
      rcases h with ⟨j,t⟩
      change @Sigma.mk _ (fun z => (next z).publicHistory_B) j
        (keyPublicEquiv_B (next j) ((keyTree_B (next j)).publicTranscript_B t)) =
        @Sigma.mk _ (fun z => (next z).publicHistory_B) j
          ((next j).publicTranscript_B (keyEnvironmentEquiv_B (next j) t))
      rw [ih j]
  | @blockCall a b af bf next ih =>
      intro h
      change keyPublicEquiv_B next (sequentialPublicEquiv_B p n a b af bf (keyTree_B next)
        ((sequentialThenKey_B p n a b af bf (keyTree_B next)).publicTranscript_B h)) = _
      rw [sequentialPublic_transcript_B, ih]
      rfl

def copiedLocalOutputEquiv_B {p : ℝ} {n a b af bf : ℕ}
    (R : FiniteBlockProtocolB p n a b af bf) (d : ℕ) :
    Fin (Nat.card (R.publicHistory_B × Fin d)) ≃
      ((keyTree_B R).comparisonPublicHistory_B × Fin d) :=
  (matrixIndex_B _).trans ((keyPublicEquiv_B R).symm.prodCongr (Equiv.refl (Fin d)))

def copiedOutputEquiv_B {p : ℝ} {n a b af bf : ℕ}
    (R : FiniteBlockProtocolB p n a b af bf) :
    (Fin (Nat.card (R.publicHistory_B × Fin af)) ×
      Fin (Nat.card (R.publicHistory_B × Fin bf))) ≃
      (((keyTree_B R).comparisonPublicHistory_B × Fin af) ×
        ((keyTree_B R).comparisonPublicHistory_B × Fin bf)) :=
  (copiedLocalOutputEquiv_B R af).prodCongr (copiedLocalOutputEquiv_B R bf)

theorem retainedWithPriorEve_honest_B {I O J E : Type*}
    [Fintype I] [Fintype O] [Fintype J] [Fintype E]
    [DecidableEq I] [DecidableEq E] (C : KrausChannel I O J)
    (ρ : Matrix (I × E) (I × E) ℂ) :
    partialTraceRight ((retainedWithPriorEveChannel_B (E := E) C).eval ρ) =
      C.eval (partialTraceRight ρ) := by
  have hrho : partialTraceRight ρ = ∑ e : E, Matrix.of (fun i j => ρ (i,e) (j,e)) := by
    ext i j
    simp only [partialTraceRight, Matrix.sum_apply, Matrix.of_apply]
  rw [hrho, KrausChannel.eval_finite_sum_B]
  ext o o'
  simp only [partialTraceRight, Matrix.sum_apply]
  change (∑ h : J × E,
    (retainedWithPriorEveChannel_B (E := E) C).eval ρ (o,h) (o',h)) =
      ∑ e : E, (C.eval (Matrix.of (fun i j => ρ (i,e) (j,e)))) o o'
  rw [Fintype.sum_prod_type]
  simp_rw [retainedWithPriorEve_eval_apply_B]
  simp only [KrausChannel.eval, Matrix.sum_apply]
  exact Finset.sum_comm

end QuantumProver.AmplitudeDamping.SecretKey.MatrixPublicCopy

namespace QuantumProver.AmplitudeDamping.SecretKey.MatrixPublicCopy

open QuantumProver.AmplitudeDamping.FiniteModel
open IndependentLanes PhysicalProtocol PhysicalProtocol.FiniteKeyProtocol PublicHistory

theorem sandwich_submatrix_rows_B {I O U : Type*} [Fintype I]
    (K : Matrix O I ℂ) (ρ : Matrix I I ℂ) (e : U → O) :
    (K * ρ * Kᴴ).submatrix e e =
      K.submatrix e id * ρ * (K.submatrix e id)ᴴ := by
  rw [Matrix.submatrix_mul _ _ e id e Function.bijective_id,
    Matrix.submatrix_mul _ _ e id id Function.bijective_id]
  simp only [Matrix.submatrix_id_id, Matrix.conjTranspose_submatrix]

theorem attachFlag_public_chart_B {p : ℝ} {n a b af bf : ℕ}
    (R : FiniteBlockProtocolB p n a b af bf) (d : ℕ)
    (h : (keyTree_B R).comparisonPublicHistory_B) :
    (attachFlag_B (A := Fin d) h).submatrix (copiedLocalOutputEquiv_B R d) id =
      flagMatrix_B d (keyPublicEquiv_B R h) := by
  classical
  ext i j
  simp only [copiedLocalOutputEquiv_B, flagMatrix_B, attachFlag_B,
    Matrix.submatrix_apply, Equiv.trans_apply, Equiv.prodCongr_apply,
    Prod.map, Equiv.refl_apply, Matrix.one_apply, id_eq]
  simp only [Equiv.symm_apply_eq]

theorem wholePublicCopiedOperator_chart_B {p : ℝ} {n a b af bf : ℕ}
    (R : FiniteBlockProtocolB p n a b af bf) (h : (keyTree_B R).Environment) :
    (wholePublicCopiedOperator_B (keyTree_B R) h).submatrix (copiedOutputEquiv_B R) id =
      R.recordedHistoryOperator_B (keyEnvironmentEquiv_B R h) := by
  have hf : (attachFlag_B (A := Fin af) ((keyTree_B R).publicTranscript_B h) ⊗ₖ
        attachFlag_B (A := Fin bf) ((keyTree_B R).publicTranscript_B h)).submatrix
      (copiedOutputEquiv_B R) id =
      flagMatrix_B af (keyPublicEquiv_B R ((keyTree_B R).publicTranscript_B h)) ⊗ₖ
        flagMatrix_B bf (keyPublicEquiv_B R ((keyTree_B R).publicTranscript_B h)) := by
    ext x y
    change ((attachFlag_B (A := Fin af) ((keyTree_B R).publicTranscript_B h)).submatrix
        (copiedLocalOutputEquiv_B R af) id) x.1 y.1 *
      ((attachFlag_B (A := Fin bf) ((keyTree_B R).publicTranscript_B h)).submatrix
        (copiedLocalOutputEquiv_B R bf) id) x.2 y.2 = _
    rw [attachFlag_public_chart_B, attachFlag_public_chart_B]
    rfl
  rw [wholePublicCopiedOperator_B,
    Matrix.submatrix_mul _ _ (copiedOutputEquiv_B R) id id Function.bijective_id]
  simp only [Matrix.submatrix_id_id]
  rw [hf, keyTree_historyOperator_B, keyTree_publicTranscript_B]
  rfl

theorem copyPublic_output_eq_physicalCopied_B {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {n a b af bf : ℕ} (R : FiniteBlockProtocolB p n a b af bf)
    (ρ : QuantumProver.AmplitudeDamping.FiniteModel.BipartiteMatrix a b) :
    R.copyPublic.output ρ =
      ((wholePublicCopiedChannel_B hp0 hp1 (keyTree_B R)).eval ρ).submatrix
        (copiedOutputEquiv_B R) (copiedOutputEquiv_B R) := by
  rw [R.copyPublic_output_history_B]
  calc
    _ = ∑ h : (keyTree_B R).Environment,
        R.recordedHistoryOperator_B (keyEnvironmentEquiv_B R h) * ρ *
          (R.recordedHistoryOperator_B (keyEnvironmentEquiv_B R h))ᴴ :=
      (keyEnvironmentEquiv_B R).sum_comp
        (fun h => R.recordedHistoryOperator_B h * ρ * (R.recordedHistoryOperator_B h)ᴴ) |>.symm
    _ = _ := by
      ext x y
      simp only [KrausChannel.eval, wholePublicCopiedChannel_B, Matrix.submatrix_apply,
        Matrix.sum_apply]
      apply Finset.sum_congr rfl
      intro h _
      have he := sandwich_submatrix_rows_B (wholePublicCopiedOperator_B (keyTree_B R) h)
        ρ (copiedOutputEquiv_B R)
      rw [wholePublicCopiedOperator_chart_B] at he
      exact (congrArg (fun A => A x y) he).symm

theorem exists_copyPublic_retained_honest_B {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {n a b af bf : ℕ} (R : FiniteBlockProtocolB p n a b af bf)
    {E : Type*} [Fintype E] [DecidableEq E] :
    ∃ eA : Fin (Nat.card (R.publicHistory_B × Fin af)) ≃
        ((blockExpansion_B R).comparisonPublicHistory_B × Fin af),
      ∃ eB : Fin (Nat.card (R.publicHistory_B × Fin bf)) ≃
        ((blockExpansion_B R).comparisonPublicHistory_B × Fin bf),
      ∀ ρ : Matrix ((Fin a × Fin b) × E) ((Fin a × Fin b) × E) ℂ,
        R.copyPublic.output (partialTraceRight ρ) =
          (partialTraceRight ((wholeRetainedChannelWithEve_B hp0 hp1
            (blockExpansion_B R) E).eval ρ)).submatrix
              (eA.prodCongr eB) (eA.prodCongr eB) := by
  rw [← keyTree_eq_blockExpansion_B R]
  refine ⟨copiedLocalOutputEquiv_B R af, copiedLocalOutputEquiv_B R bf, ?_⟩
  intro ρ
  rw [wholeRetainedChannelWithEve_B, retainedWithPriorEve_honest_B]
  exact copyPublic_output_eq_physicalCopied_B hp0 hp1 R (partialTraceRight ρ)

theorem postLocal_scalar_calls_B {p : ℝ} {n a b af bf ag bg : ℕ}
    (P : FiniteBlockProtocolB p n a b af bf)
    (M : Matrix (Fin ag) (Fin af) ℂ) (hM : Mᴴ * M = 1)
    (N : Matrix (Fin bg) (Fin bf) ℂ) (hN : Nᴴ * N = 1) :
    (postLocal_B M hM N hN P).represented_toMatrix.calls = P.represented_toMatrix.calls := by
  induction P with
  | done a b => simp [postLocal_B, FiniteBlockProtocolB.represented_toMatrix, FiniteProtocol.calls]
  | alice K next ih => simp only [postLocal_B, FiniteBlockProtocolB.represented_toMatrix, FiniteProtocol.calls, ih]
  | bob K next ih => simp only [postLocal_B, FiniteBlockProtocolB.represented_toMatrix, FiniteProtocol.calls, ih]
  | blockCall next ih =>
      simp only [postLocal_B, FiniteBlockProtocolB.represented_toMatrix, sequentialCallsThenB_calls, ih]

end QuantumProver.AmplitudeDamping.SecretKey.MatrixPublicCopy

namespace QuantumProver.AmplitudeDamping.FiniteModel.FiniteBlockProtocolB

open QuantumProver.AmplitudeDamping.SecretKey.MatrixPublicCopy

theorem copyPublic_scalar_calls_eq {p : ℝ} {n a b af bf : ℕ}
    (R : FiniteBlockProtocolB p n a b af bf) :
    R.copyPublic.represented_toMatrix.calls = R.represented_toMatrix.calls := by
  induction R with
  | done a b => simp only [copyPublic, postLocal_scalar_calls_B]
  | alice K next ih =>
      simp only [copyPublic, FiniteBlockProtocolB.represented_toMatrix, FiniteProtocol.calls,
        postLocal_scalar_calls_B, ih]
  | bob K next ih =>
      simp only [copyPublic, FiniteBlockProtocolB.represented_toMatrix, FiniteProtocol.calls,
        postLocal_scalar_calls_B, ih]
  | blockCall next ih =>
      simp only [copyPublic, FiniteBlockProtocolB.represented_toMatrix, sequentialCallsThenB_calls, ih]

end QuantumProver.AmplitudeDamping.FiniteModel.FiniteBlockProtocolB

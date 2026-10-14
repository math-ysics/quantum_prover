import QuantumProver.InformationTheory.AmplitudeDamping.SecretKey.LaneRetainedOutput
import QuantumProver.InformationTheory.AmplitudeDamping.SecretKey.PublicCopyProtocol
import QuantumProver.InformationTheory.AmplitudeDamping.SecretKey.PrivateTestResource

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix Kronecker

namespace QuantumProver.AmplitudeDamping.SecretKey.MatrixCoherentLaneOutput

open PublicHistory IndependentLanes PrivateTestResource

section Decoder

variable {I O : Type*} [Fintype I] [Fintype O]
  [DecidableEq I] [DecidableEq O]

theorem embedding_projector_apply_B (f : I → O) (g : O → I)
    (hgf : Function.LeftInverse g f) (x y : O) :
    (basisEmbedding_B f * (basisEmbedding_B f)ᴴ) x y =
      if x = y ∧ f (g x) = x then 1 else 0 := by
  have h := basisEmbedding_sandwich_apply_B f g hgf (1 : Matrix I I ℂ) x y
  rw [Matrix.mul_one] at h
  rw [h]
  by_cases hxy : x = y
  · subst y
    simp [Matrix.one_apply]
  · by_cases hx : f (g x) = x <;> by_cases hy : f (g y) = y
    · have hg : g x ≠ g y := fun h => hxy (hx.symm.trans ((congrArg f h).trans hy))
      simp [hx,hy,hxy,hg,Matrix.one_apply]
    · simp [hx,hy,hxy]
    · simp [hx,hy,hxy]
    · simp [hx,hy,hxy]

def decoderFailure_B (f : I → O) (g : O → I) (o : O) : Matrix I O ℂ :=
  fun i q => if f (g o) ≠ o ∧ i = g o ∧ q = o then 1 else 0

theorem decoderFailure_gram_apply_B (f : I → O) (g : O → I) (o x y : O) :
    ((decoderFailure_B f g o)ᴴ * decoderFailure_B f g o) x y =
      if x = o ∧ y = o ∧ f (g o) ≠ o then 1 else 0 := by
  classical
  change (∑ i : I, star (if f (g o) ≠ o ∧ i = g o ∧ x = o then (1 : ℂ) else 0) *
    (if f (g o) ≠ o ∧ i = g o ∧ y = o then (1 : ℂ) else 0)) = _
  by_cases ho : f (g o) = o <;> by_cases hx : x = o <;> by_cases hy : y = o <;>
    simp [hx,hy,ho,eq_comm]

def decoderOperator_B (f : I → O) (g : O → I) : Unit ⊕ O → Matrix I O ℂ
  | .inl _ => (basisEmbedding_B f)ᴴ
  | .inr o => decoderFailure_B f g o

theorem decoderOperator_complete_B (f : I → O) (g : O → I)
    (hgf : Function.LeftInverse g f) :
    (∑ z, (decoderOperator_B f g z)ᴴ * decoderOperator_B f g z) = 1 := by
  classical
  ext x y
  simp only [Matrix.sum_apply,Fintype.sum_sum_type,Fintype.sum_unique,
    decoderOperator_B,Matrix.conjTranspose_conjTranspose,
    embedding_projector_apply_B f g hgf,decoderFailure_gram_apply_B]
  by_cases hxy : x = y
  · subst y
    by_cases hx : f (g x) = x
    · simp [hx,Matrix.one_apply]
    · have hpred (o : O) : (x = o ∧ x = o ∧ f (g o) ≠ o) ↔ o = x := by
        constructor
        · intro h
          exact h.1.symm
        · intro h
          subst o
          exact ⟨rfl,rfl,hx⟩
      simp only [hpred]
      simp [hx]
  · have hbad (o : O) : ¬ (x = o ∧ y = o ∧ f (g o) ≠ o) := by
      rintro ⟨hx,hy,_⟩
      exact hxy (hx.trans hy.symm)
    simp [hxy,hbad,Matrix.one_apply]

def basisDecoderChannel_B (f : I → O) (g : O → I)
    (hgf : Function.LeftInverse g f) : KrausChannel O I (Unit ⊕ O) where
  op := decoderOperator_B f g
  complete := decoderOperator_complete_B f g hgf

theorem decoderOperator_embedding_B (f : I → O) (g : O → I)
    (hgf : Function.LeftInverse g f) (z : Unit ⊕ O) :
    decoderOperator_B f g z * basisEmbedding_B f =
      match z with
      | .inl _ => 1
      | .inr _ => 0 := by
  classical
  cases z with
  | inl u => exact basisEmbedding_gram_B f hgf.injective
  | inr o =>
    by_cases ho : f (g o) = o
    · ext i j
      change (∑ q : O, (if f (g o) ≠ o ∧ i = g o ∧ q = o then (1 : ℂ) else 0) *
        (if q = f j then (1 : ℂ) else 0)) = 0
      simp [ho]
    · have hneq (i : I) : o ≠ f i := by
        intro h
        apply ho
        rw [h,hgf i]
      ext i j
      change (∑ q : O, (if f (g o) ≠ o ∧ i = g o ∧ q = o then (1 : ℂ) else 0) *
        (if q = f j then (1 : ℂ) else 0)) = 0
      apply Finset.sum_eq_zero
      intro q _
      by_cases hq : q = o
      · subst q
        simp [hneq j]
      · simp [hq]

theorem basisDecoder_recovers_B (f : I → O) (g : O → I)
    (hgf : Function.LeftInverse g f) (M : Matrix I I ℂ) :
    (basisDecoderChannel_B f g hgf).eval
      (basisEmbedding_B f * M * (basisEmbedding_B f)ᴴ) = M := by
  change (∑ z, decoderOperator_B f g z *
    (basisEmbedding_B f * M * (basisEmbedding_B f)ᴴ) *
      (decoderOperator_B f g z)ᴴ) = M
  have hs (z : Unit ⊕ O) :
      decoderOperator_B f g z *
        (basisEmbedding_B f * M * (basisEmbedding_B f)ᴴ) *
          (decoderOperator_B f g z)ᴴ =
        (decoderOperator_B f g z * basisEmbedding_B f) * M *
          (decoderOperator_B f g z * basisEmbedding_B f)ᴴ := by
    simp only [Matrix.conjTranspose_mul,Matrix.mul_assoc]
  simp only [hs,decoderOperator_embedding_B f g hgf,Fintype.sum_sum_type,
    Fintype.sum_unique,Matrix.one_mul,Matrix.conjTranspose_one,Matrix.mul_one,
    Matrix.zero_mul,Matrix.conjTranspose_zero,Matrix.mul_zero,
    Finset.sum_const_zero,add_zero]

end Decoder

section LocalTensor

variable {A B A' B' J K : Type*}
  [Fintype A] [Fintype B] [Fintype A'] [Fintype B'] [Fintype J] [Fintype K]
  [DecidableEq A] [DecidableEq B] [DecidableEq A'] [DecidableEq B']

theorem tensorChannel_local_operator_B
    (C : KrausChannel A A' J) (D : KrausChannel B B' K) (N : ℕ)
    (z : Register (J × K) N) :
    (channel (C.tensorLanes_B D) N).op z =
      ((channel C N).op ((pairEquiv J K N z).1) ⊗ₖ
        (channel D N).op ((pairEquiv J K N z).2)).submatrix
          (pairEquiv A' B' N) (pairEquiv A B N) := by
  induction N with
  | zero =>
      ext x y
      cases x
      cases y
      change (1 : ℂ) = 1 * 1
      simp
  | succ N ih =>
      rcases z with ⟨⟨j,k⟩,zs⟩
      ext x y
      rcases x with ⟨⟨a',b'⟩,xs⟩
      rcases y with ⟨⟨a,b⟩,ys⟩
      simp only [channel,KrausChannel.tensorLanes_op_B,Matrix.kroneckerMap_apply,
        Matrix.submatrix_apply,pairEquiv,Equiv.trans_apply,Equiv.prodCongr_apply,
        Equiv.refl_apply,Equiv.prodProdProdComm_apply]
      simp only [Prod.map,Equiv.refl_apply]
      have ht := congrArg (fun M => M xs ys) (ih zs)
      simp only [Matrix.submatrix_apply,Matrix.kroneckerMap_apply] at ht
      rw [ht]
      ring

def localTensorChannel_B (C : KrausChannel A A' J) (D : KrausChannel B B' K)
    (N : ℕ) : KrausChannel (Register A N × Register B N)
      (Register A' N × Register B' N) (Register (J × K) N) :=
  (channel (C.tensorLanes_B D) N).relabel_B
    (pairEquiv A B N).symm (pairEquiv A' B' N).symm

theorem localTensorChannel_operator_B
    (C : KrausChannel A A' J) (D : KrausChannel B B' K) (N : ℕ)
    (z : Register (J × K) N) :
    (localTensorChannel_B C D N).op z =
      (channel C N).op ((pairEquiv J K N z).1) ⊗ₖ
        (channel D N).op ((pairEquiv J K N z).2) := by
  change ((channel (C.tensorLanes_B D) N).op z).submatrix
    (pairEquiv A' B' N).symm (pairEquiv A B N).symm = _
  rw [tensorChannel_local_operator_B]
  ext x y
  simp

theorem localTensorChannel_eval_B
    (C : KrausChannel A A' J) (D : KrausChannel B B' K) (N : ℕ)
    (M : Matrix (A × B) (A × B) ℂ) :
    (localTensorChannel_B C D N).eval
      ((matrix M N).submatrix (pairEquiv A B N).symm (pairEquiv A B N).symm) =
      (matrix ((C.tensorLanes_B D).eval M) N).submatrix
        (pairEquiv A' B' N).symm (pairEquiv A' B' N).symm := by
  rw [localTensorChannel_B,KrausChannel.relabel_eval_B]
  simp only [Equiv.symm_symm]
  have hcancel : ((matrix M N).submatrix
      (pairEquiv A B N).symm (pairEquiv A B N).symm).submatrix
        (pairEquiv A B N) (pairEquiv A B N) = matrix M N := by
    ext x y
    simp
  rw [hcancel,channel_eval]

theorem localTensorChannel_separable_B
    (C : KrausChannel A A' J) (D : KrausChannel B B' K) (N : ℕ)
    (sigma : Density (Register A N × Register B N)) (hs : IsSeparable sigma) :
    IsSeparable ((localTensorChannel_B C D N).onDensity sigma) := by
  change InSeparableCone (∑ z, (localTensorChannel_B C D N).op z * sigma.mat *
    ((localTensorChannel_B C D N).op z)ᴴ)
  apply separableCone_finite_sum_B
  intro z
  rw [localTensorChannel_operator_B]
  exact separableCone_local_product_B _ _ hs

end LocalTensor

section PhysicalPadding

open PhysicalProtocol PhysicalProtocol.FiniteKeyProtocol
open QuantumProver.AmplitudeDamping.FiniteModel IdleEvePadding MatrixPublicCopy

def publicHistorySection_B {p : ℝ} {a b af bf : ℕ}
    (P : FiniteKeyProtocol p a b af bf) :
    P.comparisonPublicHistory_B → P.Environment :=
  match P with
  | .done _ _ => fun _ => ()
  | .alice _ next => fun t => ⟨t.1, publicHistorySection_B (next t.1) t.2⟩
  | .bob _ next => fun t => ⟨t.1, publicHistorySection_B (next t.1) t.2⟩
  | .call next => fun t => (0,publicHistorySection_B next t)

theorem publicHistorySection_transcript_B {p : ℝ} {a b af bf : ℕ}
    (P : FiniteKeyProtocol p a b af bf) :
    ∀ t, P.publicTranscript_B (publicHistorySection_B P t) = t := by
  induction P with
  | done a b => intro t; cases t; rfl
  | alice K next ih =>
      rintro ⟨z,t⟩
      exact congrArg (Sigma.mk z) (ih z t)
  | bob K next ih =>
      rintro ⟨z,t⟩
      exact congrArg (Sigma.mk z) (ih z t)
  | call next ih => exact ih

theorem publicTransport_of_history_B {p : ℝ} {a b af bf : ℕ}
    (P Q : FiniteKeyProtocol p a b af bf)
    (f : P.Environment → Q.Environment) (g : Q.Environment → P.Environment)
    (hgf : Function.LeftInverse g f)
    (hT : ∀ t t', f (g t) = t → f (g t') = t' →
      (Q.publicTranscript_B t = Q.publicTranscript_B t' ↔
        P.publicTranscript_B (g t) = P.publicTranscript_B (g t'))) :
    ∃ j : P.comparisonPublicHistory_B → Q.comparisonPublicHistory_B,
    ∃ k : Q.comparisonPublicHistory_B → P.comparisonPublicHistory_B,
      Function.LeftInverse k j ∧
      ∀ h, Q.publicTranscript_B (f h) = j (P.publicTranscript_B h) := by
  classical
  have himage (h : P.Environment) : f (g (f h)) = f h := congrArg f (hgf h)
  have hpublic (h h' : P.Environment) :
      Q.publicTranscript_B (f h) = Q.publicTranscript_B (f h') ↔
        P.publicTranscript_B h = P.publicTranscript_B h' := by
    have heq := hT (f h) (f h') (himage h) (himage h')
    rw [hgf h,hgf h'] at heq
    exact heq
  let j : P.comparisonPublicHistory_B → Q.comparisonPublicHistory_B :=
    fun t => Q.publicTranscript_B (f (publicHistorySection_B P t))
  have hj : Function.Injective j := by
    intro t t' heq
    have ht := (hpublic (publicHistorySection_B P t)
      (publicHistorySection_B P t')).mp heq
    simpa only [publicHistorySection_transcript_B] using ht
  let k : Q.comparisonPublicHistory_B → P.comparisonPublicHistory_B := fun t =>
    if ht : ∃ u, j u = t then Classical.choose ht else
      P.publicTranscript_B (g (publicHistorySection_B Q t))
  refine ⟨j,k,?_,?_⟩
  · intro t
    have ht : ∃ u, j u = j t := ⟨t,rfl⟩
    change (if hx : ∃ u, j u = j t then Classical.choose hx else
      P.publicTranscript_B (g (publicHistorySection_B Q (j t)))) = t
    rw [dif_pos ht]
    exact hj (Classical.choose_spec ht)
  · intro h
    exact (hpublic h (publicHistorySection_B P (P.publicTranscript_B h))).mpr
      (publicHistorySection_transcript_B P _).symm

theorem padding_history_and_public_injection_B {p : ℝ} {a b af bf m : ℕ}
    {P Q : FiniteProtocol p a b af bf} (h : UniformPaddingDerivationB p m P Q) :
    ∃ f : (fromQuantum_B P).Environment → (fromQuantum_B Q).Environment,
    ∃ g : (fromQuantum_B Q).Environment → (fromQuantum_B P).Environment,
    ∃ j : (fromQuantum_B P).comparisonPublicHistory_B →
        (fromQuantum_B Q).comparisonPublicHistory_B,
    ∃ k : (fromQuantum_B Q).comparisonPublicHistory_B →
        (fromQuantum_B P).comparisonPublicHistory_B,
      Function.LeftInverse g f ∧ Function.LeftInverse k j ∧
      (∀ t, (fromQuantum_B Q).historyKraus_B t =
        if f (g t) = t then (fromQuantum_B P).historyKraus_B (g t) else 0) ∧
      (∀ t, (fromQuantum_B Q).publicTranscript_B (f t) =
        j ((fromQuantum_B P).publicTranscript_B t)) := by
  rcases padding_transport_history_B h with ⟨f,g,hgf,hK,hT⟩
  rcases publicTransport_of_history_B (fromQuantum_B P) (fromQuantum_B Q)
    f g hgf hT with ⟨j,k,hkj,hmap⟩
  exact ⟨f,g,j,k,hgf,hkj,hK,hmap⟩

theorem sum_ground_image_B {H G M : Type*} [Fintype H] [Fintype G]
    [AddCommMonoid M] (f : H → G) (g : G → H)
    (hgf : Function.LeftInverse g f) (a : H → M) :
    (∑ t : G, if f (g t) = t then a (g t) else 0) = ∑ h : H, a h := by
  classical
  rw [← Finset.sum_filter]
  symm
  apply Finset.sum_bij (fun h _ => f h)
  · intro h _
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,congrArg f (hgf h)⟩
  · intro h _ h' _ heq
    exact hgf.injective heq
  · intro t ht
    exact ⟨g t,Finset.mem_univ _,(Finset.mem_filter.mp ht).2⟩
  · intro h _
    rw [hgf]

def publicRawEmbedding_B {T U : Type*} [DecidableEq U]
    (j : T → U) (a : ℕ) : Matrix (U × Fin a) (T × Fin a) ℂ :=
  basisEmbedding_B (fun x => (j x.1,x.2))

theorem publicRawEmbedding_flag_B {T U : Type*} [Fintype T] [Fintype U]
    [DecidableEq T] [DecidableEq U] (j : T → U) (a : ℕ) (t : T) :
    publicRawEmbedding_B j a * attachFlag_B (A := Fin a) t =
      attachFlag_B (j t) :=
  embeddingMatrix_attachFlag_B a j t

theorem copiedOperator_ground_injection_B {p : ℝ} {a b af bf : ℕ}
    (P Q : FiniteKeyProtocol p a b af bf)
    (f : P.Environment → Q.Environment) (g : Q.Environment → P.Environment)
    (j : P.comparisonPublicHistory_B → Q.comparisonPublicHistory_B)
    (hK : ∀ t, Q.historyKraus_B t =
      if f (g t) = t then P.historyKraus_B (g t) else 0)
    (hT : ∀ t, Q.publicTranscript_B (f t) = j (P.publicTranscript_B t))
    (t : Q.Environment) :
    wholePublicCopiedOperator_B Q t =
      if f (g t) = t then
        (publicRawEmbedding_B j af ⊗ₖ publicRawEmbedding_B j bf) *
          wholePublicCopiedOperator_B P (g t) else 0 := by
  classical
  by_cases ht : f (g t) = t
  · have hpublic : Q.publicTranscript_B t = j (P.publicTranscript_B (g t)) :=
      (congrArg Q.publicTranscript_B ht).symm.trans (hT (g t))
    rw [if_pos ht,wholePublicCopiedOperator_B,hK t,if_pos ht,hpublic,
      wholePublicCopiedOperator_B]
    rw [← Matrix.mul_assoc,← Matrix.mul_kronecker_mul,
      publicRawEmbedding_flag_B,publicRawEmbedding_flag_B]
  · rw [if_neg ht,wholePublicCopiedOperator_B,hK t,if_neg ht,Matrix.mul_zero]

theorem copiedChannel_ground_injection_B {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {a b af bf : ℕ}
    (P Q : FiniteKeyProtocol p a b af bf)
    (f : P.Environment → Q.Environment) (g : Q.Environment → P.Environment)
    (j : P.comparisonPublicHistory_B → Q.comparisonPublicHistory_B)
    (hgf : Function.LeftInverse g f)
    (hK : ∀ t, Q.historyKraus_B t =
      if f (g t) = t then P.historyKraus_B (g t) else 0)
    (hT : ∀ t, Q.publicTranscript_B (f t) = j (P.publicTranscript_B t))
    (M : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) :
    (wholePublicCopiedChannel_B hp0 hp1 Q).eval M =
      (publicRawEmbedding_B j af ⊗ₖ publicRawEmbedding_B j bf) *
        (wholePublicCopiedChannel_B hp0 hp1 P).eval M *
          (publicRawEmbedding_B j af ⊗ₖ publicRawEmbedding_B j bf)ᴴ := by
  let V := publicRawEmbedding_B j af ⊗ₖ publicRawEmbedding_B j bf
  change (∑ t : Q.Environment, wholePublicCopiedOperator_B Q t * M *
    (wholePublicCopiedOperator_B Q t)ᴴ) =
      V * (∑ h : P.Environment, wholePublicCopiedOperator_B P h * M *
        (wholePublicCopiedOperator_B P h)ᴴ) * Vᴴ
  have hterm (t : Q.Environment) :
      wholePublicCopiedOperator_B Q t * M * (wholePublicCopiedOperator_B Q t)ᴴ =
      if f (g t) = t then V *
        (wholePublicCopiedOperator_B P (g t) * M *
          (wholePublicCopiedOperator_B P (g t))ᴴ) * Vᴴ else 0 := by
    rw [copiedOperator_ground_injection_B P Q f g j hK hT t]
    by_cases ht : f (g t) = t
    · simp only [V,if_pos ht,Matrix.conjTranspose_mul,Matrix.mul_assoc]
    · simp only [if_neg ht,Matrix.zero_mul,Matrix.conjTranspose_zero,
        Matrix.mul_zero]
  simp only [hterm]
  have hs := sum_ground_image_B f g hgf (fun h =>
    V * (wholePublicCopiedOperator_B P h * M * (wholePublicCopiedOperator_B P h)ᴴ) * Vᴴ)
  rw [hs]
  rw [Matrix.mul_sum,Matrix.sum_mul]

end PhysicalPadding

end QuantumProver.AmplitudeDamping.SecretKey.MatrixCoherentLaneOutput

namespace QuantumProver.AmplitudeDamping.SecretKey.MatrixCoherentLaneOutput

open Matrix Kronecker PublicHistory IndependentLanes PrivateTestResource
open PhysicalProtocol PhysicalProtocol.FiniteKeyProtocol PhysicalPurification
open QuantumProver.AmplitudeDamping.FiniteModel IdleEvePadding MatrixPublicCopy LaneRetainedOutput

section BilocalDecoder

variable {A B A' B' : Type*}
  [Fintype A] [Fintype B] [Fintype A'] [Fintype B']
  [DecidableEq A] [DecidableEq B] [DecidableEq A'] [DecidableEq B']

theorem bilocalDecoder_recovers_B (f : A → A') (g : A' → A)
    (hgf : Function.LeftInverse g f) (j : B → B') (k : B' → B)
    (hkj : Function.LeftInverse k j) (M : Matrix (A × B) (A × B) ℂ) :
    ((basisDecoderChannel_B f g hgf).tensorLanes_B
      (basisDecoderChannel_B j k hkj)).eval
        ((basisEmbedding_B f ⊗ₖ basisEmbedding_B j) * M *
          (basisEmbedding_B f ⊗ₖ basisEmbedding_B j)ᴴ) = M := by
  let C := (basisDecoderChannel_B f g hgf).tensorLanes_B
    (basisDecoderChannel_B j k hkj)
  let V := basisEmbedding_B f ⊗ₖ basisEmbedding_B j
  have hprod (z : Unit ⊕ A') (w : Unit ⊕ B') :
      C.op (z,w) * V =
        (match z with | .inl _ => (1 : Matrix A A ℂ) | .inr _ => 0) ⊗ₖ
        (match w with | .inl _ => (1 : Matrix B B ℂ) | .inr _ => 0) := by
    rw [KrausChannel.tensorLanes_op_B,← Matrix.mul_kronecker_mul]
    exact congrArg₂ (fun U W => U ⊗ₖ W)
      (decoderOperator_embedding_B f g hgf z) (decoderOperator_embedding_B j k hkj w)
  have hterm (z : Unit ⊕ A') (w : Unit ⊕ B') :
      C.op (z,w) * (V * M * Vᴴ) * (C.op (z,w))ᴴ =
        (C.op (z,w) * V) * M * (C.op (z,w) * V)ᴴ := by
    simp only [Matrix.conjTranspose_mul,Matrix.mul_assoc]
  change (∑ zw, C.op zw * (V * M * Vᴴ) * (C.op zw)ᴴ) = M
  simp only [Fintype.sum_prod_type,hterm,hprod,Fintype.sum_sum_type,
    Fintype.sum_unique,Matrix.zero_kronecker,Matrix.kronecker_zero,
    Matrix.one_kronecker_one,Matrix.one_mul,Matrix.conjTranspose_one,
    Matrix.mul_one,Matrix.zero_mul,Matrix.conjTranspose_zero,Matrix.mul_zero,
    Finset.sum_const_zero,add_zero]

end BilocalDecoder

def publicRawDecoder_B {T U : Type*} [Fintype T] [Fintype U]
    [DecidableEq T] [DecidableEq U] (j : T → U) (k : U → T)
    (hkj : Function.LeftInverse k j) (a : ℕ) :
    KrausChannel (U × Fin a) (T × Fin a) (Unit ⊕ (U × Fin a)) :=
  basisDecoderChannel_B (fun x => (j x.1,x.2)) (fun x => (k x.1,x.2))
    (fun x => Prod.ext (hkj x.1) rfl)

theorem padding_retained_honest_decode_B {E : Type*} [Fintype E] [DecidableEq E]
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {a b af bf m : ℕ}
    {P Q : FiniteProtocol p a b af bf} (h : UniformPaddingDerivationB p m P Q) :
    ∃ j : (fromQuantum_B P).comparisonPublicHistory_B →
        (fromQuantum_B Q).comparisonPublicHistory_B,
    ∃ k : (fromQuantum_B Q).comparisonPublicHistory_B →
        (fromQuantum_B P).comparisonPublicHistory_B,
    ∃ hkj : Function.LeftInverse k j,
    ∀ rho : Matrix ((Fin a × Fin b) × E) ((Fin a × Fin b) × E) ℂ,
      ((publicRawDecoder_B j k hkj af).tensorLanes_B
        (publicRawDecoder_B j k hkj bf)).eval
          (partialTraceRight ((wholeRetainedChannelWithEve_B hp0 hp1
            (fromQuantum_B Q) E).eval rho)) =
        partialTraceRight ((wholeRetainedChannelWithEve_B hp0 hp1
          (fromQuantum_B P) E).eval rho) := by
  rcases padding_history_and_public_injection_B h with ⟨f,g,j,k,hgf,hkj,hK,hT⟩
  refine ⟨j,k,hkj,?_⟩
  intro rho
  have hout : partialTraceRight ((wholeRetainedChannelWithEve_B hp0 hp1
        (fromQuantum_B Q) E).eval rho) =
      (publicRawEmbedding_B j af ⊗ₖ publicRawEmbedding_B j bf) *
        partialTraceRight ((wholeRetainedChannelWithEve_B hp0 hp1
          (fromQuantum_B P) E).eval rho) *
        (publicRawEmbedding_B j af ⊗ₖ publicRawEmbedding_B j bf)ᴴ := by
    simp only [wholeRetainedChannelWithEve_B,retainedWithPriorEve_honest_B]
    exact copiedChannel_ground_injection_B hp0 hp1 (fromQuantum_B P)
      (fromQuantum_B Q) f g j hgf hK hT (partialTraceRight rho)
  rw [hout]
  exact bilocalDecoder_recovers_B _ _ _ _ _ _ _

section LocalLift

variable {A B W : Type*} [Fintype A] [Fintype B] [Fintype W]
  [DecidableEq A] [DecidableEq B] [DecidableEq W] {d : ℕ}

def keyRecordLocalChannel_B (label : A → Fin d) :
    KrausChannel A (Fin d × A) Unit where
  op := fun _ => labelRecordingMatrix label
  complete := by
    simpa only [Fintype.sum_unique] using labelRecordingMatrix_isometry label

def privateLiftAliceChannel_B (label : A → Fin d) :
    KrausChannel A (Fin d × (A ⊕ W)) (Unit × Unit) :=
  ((paddingChannel (S := A) (E := W)).withMemory (Fin d)).compose
    (keyRecordLocalChannel_B label)

theorem privateLiftLocal_eval_B (labelA : A → Fin d) (labelB : B → Fin d)
    (M : Matrix (A × B) (A × B) ℂ) :
    ((privateLiftAliceChannel_B (W := W) labelA).tensorLanes_B
      (keyRecordLocalChannel_B labelB)).eval M =
      (keyPaddingChannel (d := d) (A := A) (B := B) (E := W)).eval
        ((keyRecordingChannel labelA labelB).eval M) := by
  simp only [KrausChannel.eval,Fintype.sum_prod_type,Fintype.sum_unique,
    KrausChannel.tensorLanes_op_B]
  let P := ((paddingChannel (S := A) (E := W)).withMemory (Fin d)).op ()
  let LA := labelRecordingMatrix labelA
  let LB := labelRecordingMatrix labelB
  change ((P * LA) ⊗ₖ LB) * M * ((P * LA) ⊗ₖ LB)ᴴ =
    (P ⊗ₖ (1 : Matrix (Fin d × B) (Fin d × B) ℂ)) *
      ((LA ⊗ₖ LB) * M * (LA ⊗ₖ LB)ᴴ) *
        (P ⊗ₖ (1 : Matrix (Fin d × B) (Fin d × B) ℂ))ᴴ
  have hp : (P ⊗ₖ (1 : Matrix (Fin d × B) (Fin d × B) ℂ)) *
      (LA ⊗ₖ LB) = (P * LA) ⊗ₖ LB := by
    rw [← Matrix.mul_kronecker_mul,Matrix.one_mul]
  simpa only [Matrix.conjTranspose_mul,Matrix.mul_assoc] using
    (congrArg (fun S => S * M * Sᴴ) hp).symm

end LocalLift

theorem physical_privateLift_honest_matrix_B {E : Type*} [Fintype E] [DecidableEq E]
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {a b af bf d : ℕ}
    (P : FiniteKeyProtocol p a b af bf) (labelA : Fin af → Fin d)
    (labelB : Fin bf → Fin d)
    (rho : Matrix ((Fin a × Fin b) × E) ((Fin a × Fin b) × E) ℂ) :
    ((privateLiftAliceChannel_B (W := P.Environment × E)
        (fun x : P.comparisonPublicHistory_B × Fin af => labelA x.2)).tensorLanes_B
      (keyRecordLocalChannel_B
        (fun x : P.comparisonPublicHistory_B × Fin bf => labelB x.2))).eval
          (partialTraceRight ((wholeRetainedChannelWithEve_B hp0 hp1 P E).eval rho)) =
        partialTraceRight ((P.retainedProtocolPrivateLiftChannel (E := E)
          hp0 hp1 labelA labelB).eval rho) := by
  rw [retainedProtocolPrivateLiftChannel,KrausChannel.eval_compose,
    KrausChannel.eval_compose,partialTraceRight_eval_withRightMemory,
    partialTraceRight_eval_withRightMemory]
  exact privateLiftLocal_eval_B _ _ _

end QuantumProver.AmplitudeDamping.SecretKey.MatrixCoherentLaneOutput

namespace QuantumProver.AmplitudeDamping.SecretKey.MatrixCoherentLaneOutput

open Matrix Kronecker PublicHistory IndependentLanes PrivateTestResource
open PhysicalProtocol PhysicalProtocol.FiniteKeyProtocol PhysicalPurification
open QuantumProver.AmplitudeDamping.FiniteModel IdleEvePadding MatrixPublicCopy LaneRetainedOutput
open LaneMergeHistory PrivateTest

section TensorComposition

variable {A B A' B' A'' B'' J K J' K' : Type*}
  [Fintype A] [Fintype B] [Fintype A'] [Fintype B'] [Fintype A''] [Fintype B'']
  [Fintype J] [Fintype K] [Fintype J'] [Fintype K']
  [DecidableEq A] [DecidableEq B] [DecidableEq A'] [DecidableEq B']
  [DecidableEq A''] [DecidableEq B'']

theorem tensor_compose_eval_B (C : KrausChannel A A' J) (D : KrausChannel B B' K)
    (C' : KrausChannel A' A'' J') (D' : KrausChannel B' B'' K')
    (M : Matrix (A × B) (A × B) ℂ) :
    ((C'.compose C).tensorLanes_B (D'.compose D)).eval M =
      (C'.tensorLanes_B D').eval ((C.tensorLanes_B D).eval M) := by
  rw [← KrausChannel.eval_compose]
  let e : ((J × J') × (K × K')) ≃ ((J × K) × (J' × K')) :=
    Equiv.prodProdProdComm _ _ _ _
  have hop (z : (J × J') × (K × K')) :
      ((C'.compose C).tensorLanes_B (D'.compose D)).op z =
        ((C'.tensorLanes_B D').compose (C.tensorLanes_B D)).op (e z) := by
    rcases z with ⟨⟨j,j'⟩,⟨k,k'⟩⟩
    rw [KrausChannel.tensorLanes_op_B]
    change (C'.op j' * C.op j) ⊗ₖ (D'.op k' * D.op k) =
      (C'.tensorLanes_B D').op (j',k') * (C.tensorLanes_B D).op (j,k)
    rw [KrausChannel.tensorLanes_op_B,KrausChannel.tensorLanes_op_B]
    exact Matrix.mul_kronecker_mul _ _ _ _
  exact Fintype.sum_equiv e _ _ (fun z =>
    congrArg (fun S => S * M * Sᴴ) (hop z))

end TensorComposition

abbrev PhysicalLiftAlice_B {p : ℝ} {a b af bf : ℕ}
    (P : FiniteKeyProtocol p a b af bf) (E : Type*) (d : ℕ) :=
  Fin d × ((P.comparisonPublicHistory_B × Fin af) ⊕ (P.Environment × E))

abbrev PhysicalLiftBob_B {p : ℝ} {a b af bf : ℕ}
    (P : FiniteKeyProtocol p a b af bf) (d : ℕ) :=
  Fin d × (P.comparisonPublicHistory_B × Fin bf)

abbrev DecodedAliceLabels_B {p : ℝ} {a b af bf : ℕ}
    (Q : FiniteKeyProtocol p a b af bf) :=
  (Unit ⊕ (Q.comparisonPublicHistory_B × Fin af)) × (Unit × Unit)

abbrev DecodedBobLabels_B {p : ℝ} {a b af bf : ℕ}
    (Q : FiniteKeyProtocol p a b af bf) :=
  (Unit ⊕ (Q.comparisonPublicHistory_B × Fin bf)) × Unit

section DecodedLift

variable {E : Type*} [Fintype E] [DecidableEq E] {p : ℝ} {a b af bf d : ℕ}

def decodedLiftAliceChannel_B (P Q : FiniteKeyProtocol p a b af bf)
    (j : P.comparisonPublicHistory_B → Q.comparisonPublicHistory_B)
    (k : Q.comparisonPublicHistory_B → P.comparisonPublicHistory_B)
    (hkj : Function.LeftInverse k j) (labelA : Fin af → Fin d) :
    KrausChannel (Q.comparisonPublicHistory_B × Fin af)
      (PhysicalLiftAlice_B P E d) (DecodedAliceLabels_B Q) :=
  (privateLiftAliceChannel_B (W := P.Environment × E)
    (fun x : P.comparisonPublicHistory_B × Fin af => labelA x.2)).compose
      (publicRawDecoder_B j k hkj af)

def decodedLiftBobChannel_B (P Q : FiniteKeyProtocol p a b af bf)
    (j : P.comparisonPublicHistory_B → Q.comparisonPublicHistory_B)
    (k : Q.comparisonPublicHistory_B → P.comparisonPublicHistory_B)
    (hkj : Function.LeftInverse k j) (labelB : Fin bf → Fin d) :
    KrausChannel (Q.comparisonPublicHistory_B × Fin bf)
      (PhysicalLiftBob_B P d) (DecodedBobLabels_B Q) :=
  (keyRecordLocalChannel_B
    (fun x : P.comparisonPublicHistory_B × Fin bf => labelB x.2)).compose
      (publicRawDecoder_B j k hkj bf)

def coherentLaneLocalChannel_B {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y] (P Q : FiniteKeyProtocol p a b af bf)
    (j : P.comparisonPublicHistory_B → Q.comparisonPublicHistory_B)
    (k : Q.comparisonPublicHistory_B → P.comparisonPublicHistory_B)
    (hkj : Function.LeftInverse k j) (labelA : Fin af → Fin d)
    (labelB : Fin bf → Fin d) (N : ℕ)
    (eA : X ≃ Register (Q.comparisonPublicHistory_B × Fin af) N)
    (eB : Y ≃ Register (Q.comparisonPublicHistory_B × Fin bf) N) :
    KrausChannel (X × Y)
      (Register (PhysicalLiftAlice_B P E d) N × Register (PhysicalLiftBob_B P d) N)
      (Register (DecodedAliceLabels_B Q × DecodedBobLabels_B Q) N) :=
  (localTensorChannel_B (decodedLiftAliceChannel_B (E := E) P Q j k hkj labelA)
    (decodedLiftBobChannel_B P Q j k hkj labelB) N).relabel_B
      (eA.prodCongr eB) (Equiv.refl _)

theorem coherentLaneLocalChannel_operator_B {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y] (P Q : FiniteKeyProtocol p a b af bf)
    (j : P.comparisonPublicHistory_B → Q.comparisonPublicHistory_B)
    (k : Q.comparisonPublicHistory_B → P.comparisonPublicHistory_B)
    (hkj : Function.LeftInverse k j) (labelA : Fin af → Fin d)
    (labelB : Fin bf → Fin d) (N : ℕ)
    (eA : X ≃ Register (Q.comparisonPublicHistory_B × Fin af) N)
    (eB : Y ≃ Register (Q.comparisonPublicHistory_B × Fin bf) N)
    (z : Register (DecodedAliceLabels_B Q × DecodedBobLabels_B Q) N) :
    (coherentLaneLocalChannel_B (E := E) P Q j k hkj labelA labelB N eA eB).op z =
      (((channel (decodedLiftAliceChannel_B (E := E) P Q j k hkj labelA) N).op
          ((pairEquiv (DecodedAliceLabels_B Q) (DecodedBobLabels_B Q) N) z).1).submatrix id eA) ⊗ₖ
      (((channel (decodedLiftBobChannel_B P Q j k hkj labelB) N).op
          ((pairEquiv (DecodedAliceLabels_B Q) (DecodedBobLabels_B Q) N) z).2).submatrix id eB) := by
  change ((localTensorChannel_B _ _ N).op z).submatrix (Equiv.refl _)
    (eA.prodCongr eB) = _
  rw [localTensorChannel_operator_B]
  ext x y
  rcases x with ⟨xa,xb⟩
  rcases y with ⟨ya,yb⟩
  rfl

theorem coherentLaneLocalChannel_resource_le_B {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y] (P Q : FiniteKeyProtocol p a b af bf)
    (j : P.comparisonPublicHistory_B → Q.comparisonPublicHistory_B)
    (k : Q.comparisonPublicHistory_B → P.comparisonPublicHistory_B)
    (hkj : Function.LeftInverse k j) (labelA : Fin af → Fin d)
    (labelB : Fin bf → Fin d) (N : ℕ)
    (eA : X ≃ Register (Q.comparisonPublicHistory_B × Fin af) N)
    (eB : Y ≃ Register (Q.comparisonPublicHistory_B × Fin bf) N)
    (rho : Density (X × Y)) {alpha : ℝ} (ha : 1 < alpha) :
    normalizedSEPEntanglement alpha
      ((coherentLaneLocalChannel_B (E := E) P Q j k hkj labelA labelB N eA eB).onDensity rho) ≤
      normalizedSEPEntanglement alpha rho := by
  let C := coherentLaneLocalChannel_B (E := E) P Q j k hkj labelA labelB N eA eB
  let KA := fun z : Register (DecodedAliceLabels_B Q × DecodedBobLabels_B Q) N =>
    (((channel (decodedLiftAliceChannel_B (E := E) P Q j k hkj labelA) N).op
      ((pairEquiv (DecodedAliceLabels_B Q) (DecodedBobLabels_B Q) N) z).1).submatrix id eA)
  let KB := fun z : Register (DecodedAliceLabels_B Q × DecodedBobLabels_B Q) N =>
    (((channel (decodedLiftBobChannel_B P Q j k hkj labelB) N).op
      ((pairEquiv (DecodedAliceLabels_B Q) (DecodedBobLabels_B Q) N) z).2).submatrix id eB)
  have hop (z) : C.op z = KA z ⊗ₖ KB z :=
    coherentLaneLocalChannel_operator_B P Q j k hkj labelA labelB N eA eB z
  have hc : ∑ z, (KA z ⊗ₖ KB z)ᴴ * (KA z ⊗ₖ KB z) = 1 := by
    simpa only [hop] using C.complete
  have hD : C.onDensity rho = (localProductChannel KA KB hc).onDensity rho := by
    apply Density.eq_of_mat_eq
    change (∑ z, C.op z * rho.mat * (C.op z)ᴴ) = _
    simp only [hop]
    rfl
  change normalizedSEPEntanglement alpha (C.onDensity rho) ≤ _
  rw [hD]
  exact normalizedSEPEntanglement_localProductChannel_le KA KB hc rho ha

end DecodedLift

def honestTensorDensity_B {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (rho : Density (A × B)) (N : ℕ) :
    Density (Register A N × Register B N) :=
  (IndependentLanes.density rho N).relabel (pairEquiv A B N).symm

theorem honestTensorDensity_mat_B {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (rho : Density (A × B)) (N : ℕ) :
    (honestTensorDensity_B rho N).mat =
      (matrix rho.mat N).submatrix (pairEquiv A B N).symm (pairEquiv A B N).symm := by
  simp only [honestTensorDensity_B,Density.relabel,IndependentLanes.density_mat]

def physicalPriorLaneDensity_B {E : Type*} [Fintype E] [DecidableEq E] {a b : ℕ}
    (rho : Density ((Fin a × Fin b) × E)) (n : ℕ) :
    Density ((Fin (lanePowerDimB n a) × Fin (lanePowerDimB n b)) × LaneEveRegister_B E n) :=
  (IndependentLanes.density rho (n+1)).relabel (laneInputEquiv_B a b E n)

theorem physicalPriorLaneDensity_mat_B {E : Type*} [Fintype E] [DecidableEq E] {a b : ℕ}
    (rho : Density ((Fin a × Fin b) × E)) (n : ℕ) :
    (physicalPriorLaneDensity_B rho n).mat = lanePriorMatrix_B rho.mat n := by
  simp only [physicalPriorLaneDensity_B,Density.relabel,IndependentLanes.density_mat]
  exact (lanePriorMatrix_eq_tensor_B rho.mat n).symm

theorem independentLanes_physical_privateLift_B {E : Type*} [Fintype E] [DecidableEq E]
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {a b af bf d m n : ℕ}
    {P Q : FiniteProtocol p a b af bf} (hPadding : UniformPaddingDerivationB p m P Q)
    {R : FiniteBlockProtocolB p (n+1) (lanePowerDimB n a) (lanePowerDimB n b)
      (lanePowerDimB n af) (lanePowerDimB n bf)}
    (hLanes : IndependentLanesDerivationB p Q n R)
    (labelA : Fin af → Fin d) (labelB : Fin bf → Fin d) :
    ∃ j : (fromQuantum_B P).comparisonPublicHistory_B → (fromQuantum_B Q).comparisonPublicHistory_B,
    ∃ k : (fromQuantum_B Q).comparisonPublicHistory_B → (fromQuantum_B P).comparisonPublicHistory_B,
    ∃ hkj : Function.LeftInverse k j,
    ∃ eT : (blockExpansion_B R).comparisonPublicHistory_B ≃
      Register (fromQuantum_B Q).comparisonPublicHistory_B (n+1),
    ∀ rho : Matrix ((Fin a × Fin b) × E) ((Fin a × Fin b) × E) ℂ,
      (coherentLaneLocalChannel_B (E := E) (fromQuantum_B P) (fromQuantum_B Q)
        j k hkj labelA labelB (n+1)
        (retainedLocalOutputEquiv_B af n eT) (retainedLocalOutputEquiv_B bf n eT)).eval
          (partialTraceRight ((wholeRetainedChannelWithEve_B hp0 hp1 (blockExpansion_B R)
            (LaneEveRegister_B E n)).eval (lanePriorMatrix_B rho n))) =
        (matrix (partialTraceRight (((fromQuantum_B P).retainedProtocolPrivateLiftChannel
          (E := E) hp0 hp1 labelA labelB).eval rho)) (n+1)).submatrix
            (pairEquiv (PhysicalLiftAlice_B (fromQuantum_B P) E d)
              (PhysicalLiftBob_B (fromQuantum_B P) d) (n+1)).symm
            (pairEquiv (PhysicalLiftAlice_B (fromQuantum_B P) E d)
              (PhysicalLiftBob_B (fromQuantum_B P) d) (n+1)).symm := by
  rcases padding_retained_honest_decode_B (E := E) hp0 hp1 hPadding with ⟨j,k,hkj,hDecode⟩
  rcases independentLanes_retained_honest_B (E := E) hp0 hp1 hLanes with
    ⟨eH,eT,hK,hT,hHonest⟩
  refine ⟨j,k,hkj,eT,?_⟩
  intro rho
  let A := decodedLiftAliceChannel_B (E := E) (fromQuantum_B P) (fromQuantum_B Q) j k hkj labelA
  let B := decodedLiftBobChannel_B (fromQuantum_B P) (fromQuantum_B Q) j k hkj labelB
  let M := partialTraceRight ((wholeRetainedChannelWithEve_B hp0 hp1 (fromQuantum_B Q) E).eval rho)
  have hsingle : (A.tensorLanes_B B).eval M =
      partialTraceRight (((fromQuantum_B P).retainedProtocolPrivateLiftChannel
        (E := E) hp0 hp1 labelA labelB).eval rho) := by
    dsimp only [A,B,decodedLiftAliceChannel_B,decodedLiftBobChannel_B,M]
    rw [tensor_compose_eval_B,hDecode rho]
    exact physical_privateLift_honest_matrix_B hp0 hp1 (fromQuantum_B P) labelA labelB rho
  rw [coherentLaneLocalChannel_B,KrausChannel.relabel_eval_B,hHonest rho]
  have hchart : ((matrix M (n+1)).submatrix
      (retainedHonestOutputEquiv_B af bf n eT) (retainedHonestOutputEquiv_B af bf n eT)).submatrix
        ((retainedLocalOutputEquiv_B af n eT).prodCongr
          (retainedLocalOutputEquiv_B bf n eT)).symm
        ((retainedLocalOutputEquiv_B af n eT).prodCongr
          (retainedLocalOutputEquiv_B bf n eT)).symm =
      (matrix M (n+1)).submatrix
        (pairEquiv ((fromQuantum_B Q).comparisonPublicHistory_B × Fin af)
          ((fromQuantum_B Q).comparisonPublicHistory_B × Fin bf) (n+1)).symm
        (pairEquiv ((fromQuantum_B Q).comparisonPublicHistory_B × Fin af)
          ((fromQuantum_B Q).comparisonPublicHistory_B × Fin bf) (n+1)).symm := by
    ext x y
    simp only [Matrix.submatrix_apply,retainedHonestOutputEquiv_B,
      Equiv.trans_apply,Equiv.apply_symm_apply]
  change (localTensorChannel_B A B (n+1)).eval
    (((matrix M (n+1)).submatrix (retainedHonestOutputEquiv_B af bf n eT)
      (retainedHonestOutputEquiv_B af bf n eT)).submatrix
      ((retainedLocalOutputEquiv_B af n eT).prodCongr (retainedLocalOutputEquiv_B bf n eT)).symm
      ((retainedLocalOutputEquiv_B af n eT).prodCongr (retainedLocalOutputEquiv_B bf n eT)).symm) = _
  rw [hchart,localTensorChannel_eval_B,hsingle]

end QuantumProver.AmplitudeDamping.SecretKey.MatrixCoherentLaneOutput

namespace QuantumProver.AmplitudeDamping.SecretKey.MatrixCoherentLaneOutput

open Matrix Kronecker PublicHistory IndependentLanes PrivateTestResource
open PhysicalProtocol PhysicalProtocol.FiniteKeyProtocol PhysicalPurification
open QuantumProver.AmplitudeDamping.FiniteModel IdleEvePadding MatrixPublicCopy LaneRetainedOutput
open LaneMergeHistory PrivateTest

theorem independentLanes_physical_privateLift_density_B {E : Type*} [Fintype E] [DecidableEq E]
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {a b af bf d m n : ℕ}
    {P Q : FiniteProtocol p a b af bf} (hPadding : UniformPaddingDerivationB p m P Q)
    {R : FiniteBlockProtocolB p (n+1) (lanePowerDimB n a) (lanePowerDimB n b)
      (lanePowerDimB n af) (lanePowerDimB n bf)}
    (hLanes : IndependentLanesDerivationB p Q n R)
    (labelA : Fin af → Fin d) (labelB : Fin bf → Fin d) :
    ∃ j : (fromQuantum_B P).comparisonPublicHistory_B → (fromQuantum_B Q).comparisonPublicHistory_B,
    ∃ k : (fromQuantum_B Q).comparisonPublicHistory_B → (fromQuantum_B P).comparisonPublicHistory_B,
    ∃ hkj : Function.LeftInverse k j,
    ∃ eT : (blockExpansion_B R).comparisonPublicHistory_B ≃
      Register (fromQuantum_B Q).comparisonPublicHistory_B (n+1),
    ∀ rho : Density ((Fin a × Fin b) × E),
      let C := coherentLaneLocalChannel_B (E := E) (fromQuantum_B P) (fromQuantum_B Q)
        j k hkj labelA labelB (n+1)
        (retainedLocalOutputEquiv_B af n eT) (retainedLocalOutputEquiv_B bf n eT)
      let rhoR := honestMarginal ((wholeRetainedChannelWithEve_B hp0 hp1 (blockExpansion_B R)
        (LaneEveRegister_B E n)).onDensity (physicalPriorLaneDensity_B rho n))
      let rhoHat := honestMarginal (((fromQuantum_B P).retainedProtocolPrivateLiftChannel
        (E := E) hp0 hp1 labelA labelB).onDensity rho)
      C.onDensity rhoR = honestTensorDensity_B rhoHat (n+1) ∧
      ∀ alpha : ℝ, 1 < alpha →
        normalizedSEPEntanglement alpha (honestTensorDensity_B rhoHat (n+1)) ≤
          normalizedSEPEntanglement alpha rhoR := by
  rcases independentLanes_physical_privateLift_B (E := E) hp0 hp1 hPadding hLanes
    labelA labelB with ⟨j,k,hkj,eT,hTensor⟩
  refine ⟨j,k,hkj,eT,?_⟩
  intro rho
  let C := coherentLaneLocalChannel_B (E := E) (fromQuantum_B P) (fromQuantum_B Q)
    j k hkj labelA labelB (n+1)
    (retainedLocalOutputEquiv_B af n eT) (retainedLocalOutputEquiv_B bf n eT)
  let rhoR := honestMarginal ((wholeRetainedChannelWithEve_B hp0 hp1 (blockExpansion_B R)
    (LaneEveRegister_B E n)).onDensity (physicalPriorLaneDensity_B rho n))
  let rhoHat := honestMarginal (((fromQuantum_B P).retainedProtocolPrivateLiftChannel
    (E := E) hp0 hp1 labelA labelB).onDensity rho)
  have hD : C.onDensity rhoR = honestTensorDensity_B rhoHat (n+1) := by
    apply Density.eq_of_mat_eq
    rw [honestTensorDensity_mat_B]
    change C.eval (partialTraceRight ((wholeRetainedChannelWithEve_B hp0 hp1 (blockExpansion_B R)
      (LaneEveRegister_B E n)).eval (physicalPriorLaneDensity_B rho n).mat)) = _
    rw [physicalPriorLaneDensity_mat_B]
    exact hTensor rho.mat
  refine ⟨hD,?_⟩
  intro alpha ha
  have hRes := coherentLaneLocalChannel_resource_le_B (E := E)
    (fromQuantum_B P) (fromQuantum_B Q) j k hkj labelA labelB (n+1)
    (retainedLocalOutputEquiv_B af n eT) (retainedLocalOutputEquiv_B bf n eT) rhoR ha
  rw [hD] at hRes
  convert hRes using 1
  congr 1

theorem exists_physical_coherent_lanes_B {E : Type*} [Fintype E] [DecidableEq E]
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {a b af bf d : ℕ}
    (P : FiniteProtocol p a b af bf) (m : ℕ) (hP : P.calls ≤ m) (n : ℕ)
    (labelA : Fin af → Fin d) (labelB : Fin bf → Fin d) :
    ∃ Q : FiniteProtocol p a b af bf,
      UniformPaddingDerivationB p m P Q ∧ Q.calls ≤ m ∧ Q.UniformCallsB m ∧
    ∃ R : FiniteBlockProtocolB p (n+1) (lanePowerDimB n a) (lanePowerDimB n b)
      (lanePowerDimB n af) (lanePowerDimB n bf),
      IndependentLanesDerivationB p Q n R ∧ R.calls ≤ m ∧
      (blockExpansion_B R).calls ≤ (n+1) * m ∧
    ∃ j : (fromQuantum_B P).comparisonPublicHistory_B → (fromQuantum_B Q).comparisonPublicHistory_B,
    ∃ k : (fromQuantum_B Q).comparisonPublicHistory_B → (fromQuantum_B P).comparisonPublicHistory_B,
    ∃ hkj : Function.LeftInverse k j,
    ∃ eT : (blockExpansion_B R).comparisonPublicHistory_B ≃
      Register (fromQuantum_B Q).comparisonPublicHistory_B (n+1),
    ∀ rho : Density ((Fin a × Fin b) × E),
      let C := coherentLaneLocalChannel_B (E := E) (fromQuantum_B P) (fromQuantum_B Q)
        j k hkj labelA labelB (n+1)
        (retainedLocalOutputEquiv_B af n eT) (retainedLocalOutputEquiv_B bf n eT)
      let rhoR := honestMarginal ((wholeRetainedChannelWithEve_B hp0 hp1 (blockExpansion_B R)
        (LaneEveRegister_B E n)).onDensity (physicalPriorLaneDensity_B rho n))
      let rhoHat := honestMarginal (((fromQuantum_B P).retainedProtocolPrivateLiftChannel
        (E := E) hp0 hp1 labelA labelB).onDensity rho)
      C.onDensity rhoR = honestTensorDensity_B rhoHat (n+1) ∧
      ∀ alpha : ℝ, 1 < alpha →
        normalizedSEPEntanglement alpha (honestTensorDensity_B rhoHat (n+1)) ≤
          normalizedSEPEntanglement alpha rhoR := by
  rcases P.exists_uniform_padding_with_derivationB m hP with ⟨Q,hPadding,hQC,hQU,hQO⟩
  rcases Q.exists_uniform_lanes_with_derivationB hQU n with ⟨R,hLanes,hRC,hRU,hRN,hRO⟩
  refine ⟨Q,hPadding,hQC,hQU,R,hLanes,hRC,?_,?_⟩
  · simpa only [blockExpansion_B,fromQuantum_calls_B] using hRN
  · exact independentLanes_physical_privateLift_density_B hp0 hp1 hPadding hLanes labelA labelB

end QuantumProver.AmplitudeDamping.SecretKey.MatrixCoherentLaneOutput

namespace QuantumProver.AmplitudeDamping.SecretKey.MatrixCoherentLaneOutput

open Matrix Kronecker PublicHistory IndependentLanes PrivateTestResource
open PhysicalProtocol PhysicalProtocol.FiniteKeyProtocol PhysicalPurification
open QuantumProver.AmplitudeDamping.FiniteModel IdleEvePadding MatrixPublicCopy LaneRetainedOutput
open LaneMergeHistory PrivateTest

section MatrixLocalChannels

variable {J K : Type*} [Fintype J] [Fintype K]

def channelInstrument_B {a af : ℕ} (C : KrausChannel (Fin a) (Fin af) J) :
    KrausInstrument a af (Fintype.card J) where
  operator := fun z => C.op (finiteIndexB J z)
  complete := by
    change (∑ z, (C.op (finiteIndexB J z))ᴴ * C.op (finiteIndexB J z)) = 1
    exact ((finiteIndexB J).sum_comp (fun j => (C.op j)ᴴ * C.op j)).trans C.complete

def postLocalChannels_B {p : ℝ} {n af bf ag bg : ℕ}
    (C : KrausChannel (Fin af) (Fin ag) J) (D : KrausChannel (Fin bf) (Fin bg) K) :
    {a b : ℕ} → FiniteBlockProtocolB p n a b af bf → FiniteBlockProtocolB p n a b ag bg
  | _, _, .done _ _ => .alice (channelInstrument_B C) fun _ =>
      .bob (channelInstrument_B D) fun _ => .done ag bg
  | _, _, .alice L next => .alice L fun j => postLocalChannels_B C D (next j)
  | _, _, .bob L next => .bob L fun j => postLocalChannels_B C D (next j)
  | _, _, .blockCall next => .blockCall (postLocalChannels_B C D next)

theorem postLocalChannels_calls_B {p : ℝ} {n a b af bf ag bg : ℕ}
    (P : FiniteBlockProtocolB p n a b af bf)
    (C : KrausChannel (Fin af) (Fin ag) J) (D : KrausChannel (Fin bf) (Fin bg) K) :
    (postLocalChannels_B C D P).calls = P.calls := by
  induction P with
  | done a b => simp [postLocalChannels_B,FiniteBlockProtocolB.calls]
  | alice L next ih => simp only [postLocalChannels_B,FiniteBlockProtocolB.calls,ih]
  | bob L next ih => simp only [postLocalChannels_B,FiniteBlockProtocolB.calls,ih]
  | blockCall next ih => simp only [postLocalChannels_B,FiniteBlockProtocolB.calls,ih]

theorem postLocalChannels_scalar_calls_B {p : ℝ} {n a b af bf ag bg : ℕ}
    (P : FiniteBlockProtocolB p n a b af bf)
    (C : KrausChannel (Fin af) (Fin ag) J) (D : KrausChannel (Fin bf) (Fin bg) K) :
    (postLocalChannels_B C D P).represented_toMatrix.calls = P.represented_toMatrix.calls := by
  induction P with
  | done a b => simp [postLocalChannels_B,FiniteBlockProtocolB.represented_toMatrix,FiniteProtocol.calls]
  | alice L next ih => simp only [postLocalChannels_B,FiniteBlockProtocolB.represented_toMatrix,FiniteProtocol.calls,ih]
  | bob L next ih => simp only [postLocalChannels_B,FiniteBlockProtocolB.represented_toMatrix,FiniteProtocol.calls,ih]
  | blockCall next ih =>
      simp only [postLocalChannels_B,FiniteBlockProtocolB.represented_toMatrix,sequentialCallsThenB_calls,ih]

theorem localSequence_eval_B {a b af bf : ℕ}
    (C : KrausChannel (Fin a) (Fin af) J) (D : KrausChannel (Fin b) (Fin bf) K)
    (rho : QuantumProver.AmplitudeDamping.FiniteModel.BipartiteMatrix a b) :
    (∑ u : Fin (Fintype.card J), ∑ v : Fin (Fintype.card K),
      bobOperator (a := af) (D.op (finiteIndexB K v)) *
        (aliceOperator (b := b) (C.op (finiteIndexB J u)) * rho *
          (aliceOperator (b := b) (C.op (finiteIndexB J u)))ᴴ) *
        (bobOperator (a := af) (D.op (finiteIndexB K v)))ᴴ) =
      (C.tensorLanes_B D).eval rho := by
  have hprod (u : Fin (Fintype.card J)) (v : Fin (Fintype.card K)) :
      bobOperator (a := af) (D.op (finiteIndexB K v)) *
        aliceOperator (b := b) (C.op (finiteIndexB J u)) =
      C.op (finiteIndexB J u) ⊗ₖ D.op (finiteIndexB K v) := by
    rw [bobOperator,aliceOperator,← Matrix.mul_kronecker_mul,Matrix.one_mul,Matrix.mul_one]
  have hterm (u : Fin (Fintype.card J)) (v : Fin (Fintype.card K)) :
      bobOperator (a := af) (D.op (finiteIndexB K v)) *
        (aliceOperator (b := b) (C.op (finiteIndexB J u)) * rho *
          (aliceOperator (b := b) (C.op (finiteIndexB J u)))ᴴ) *
        (bobOperator (a := af) (D.op (finiteIndexB K v)))ᴴ =
      (C.op (finiteIndexB J u) ⊗ₖ D.op (finiteIndexB K v)) * rho *
        (C.op (finiteIndexB J u) ⊗ₖ D.op (finiteIndexB K v))ᴴ := by
    simpa only [Matrix.conjTranspose_mul,Matrix.mul_assoc] using
      congrArg (fun S => S * rho * Sᴴ) (hprod u v)
  simp only [hterm]
  have hsum := Fintype.sum_equiv ((finiteIndexB J).prodCongr (finiteIndexB K))
    (fun z : Fin (Fintype.card J) × Fin (Fintype.card K) =>
      (C.op (finiteIndexB J z.1) ⊗ₖ D.op (finiteIndexB K z.2)) * rho *
        (C.op (finiteIndexB J z.1) ⊗ₖ D.op (finiteIndexB K z.2))ᴴ)
    (fun z : J × K => (C.op z.1 ⊗ₖ D.op z.2) * rho *
      (C.op z.1 ⊗ₖ D.op z.2)ᴴ) (by intro z; rfl)
  simpa only [Fintype.sum_prod_type,KrausChannel.eval,KrausChannel.tensorLanes_op_B] using hsum

theorem channel_eval_sum_B {I O Z T : Type*} [Fintype I] [Fintype O]
    [Fintype Z] [Fintype T] [DecidableEq I] (C : KrausChannel I O Z)
    (f : T → Matrix I I ℂ) : C.eval (∑ t, f t) = ∑ t, C.eval (f t) := by
  simp only [KrausChannel.eval,Matrix.mul_sum,Matrix.sum_mul]
  exact Finset.sum_comm

theorem postLocalChannels_output_B {p : ℝ} {n a b af bf ag bg : ℕ}
    (P : FiniteBlockProtocolB p n a b af bf)
    (C : KrausChannel (Fin af) (Fin ag) J) (D : KrausChannel (Fin bf) (Fin bg) K) :
    ∀ rho, (postLocalChannels_B C D P).output rho = (C.tensorLanes_B D).eval (P.output rho) := by
  induction P with
  | done a b =>
      intro rho
      simp only [postLocalChannels_B,FiniteBlockProtocolB.output,channelInstrument_B]
      exact localSequence_eval_B C D rho
  | alice L next ih =>
      intro rho
      simp only [postLocalChannels_B,FiniteBlockProtocolB.output,ih]
      exact (channel_eval_sum_B _ _).symm
  | bob L next ih =>
      intro rho
      simp only [postLocalChannels_B,FiniteBlockProtocolB.output,ih]
      exact (channel_eval_sum_B _ _).symm
  | blockCall next ih => intro rho; exact ih C D _

end MatrixLocalChannels

section LocalTensorIdentification

variable {A B A' B' J K : Type*}
  [Fintype A] [Fintype B] [Fintype A'] [Fintype B'] [Fintype J] [Fintype K]
  [DecidableEq A] [DecidableEq B] [DecidableEq A'] [DecidableEq B']

theorem localTensorChannel_eq_two_local_B (C : KrausChannel A A' J)
    (D : KrausChannel B B' K) (N : ℕ)
    (M : Matrix (Register A N × Register B N) (Register A N × Register B N) ℂ) :
    (localTensorChannel_B C D N).eval M =
      ((channel C N).tensorLanes_B (channel D N)).eval M := by
  change (∑ z, (localTensorChannel_B C D N).op z * M *
    ((localTensorChannel_B C D N).op z)ᴴ) = _
  exact Fintype.sum_equiv (pairEquiv J K N) _ _ (by
    intro z
    rw [localTensorChannel_operator_B,KrausChannel.tensorLanes_op_B])

theorem bilocal_relabel_eval_B {X Y X' Y' : Type*}
    [Fintype X] [Fintype Y] [Fintype X'] [Fintype Y']
    [DecidableEq X] [DecidableEq Y] [DecidableEq X'] [DecidableEq Y']
    (C : KrausChannel A A' J)
    (D : KrausChannel B B' K) (eA : X ≃ A) (eB : Y ≃ B)
    (eA' : X' ≃ A') (eB' : Y' ≃ B') (M : Matrix (X × Y) (X × Y) ℂ) :
    ((C.relabel_B eA eA').tensorLanes_B (D.relabel_B eB eB')).eval M =
      ((C.tensorLanes_B D).relabel_B (eA.prodCongr eB) (eA'.prodCongr eB')).eval M := by
  have hop (z : J × K) :
      ((C.relabel_B eA eA').tensorLanes_B (D.relabel_B eB eB')).op z =
      ((C.tensorLanes_B D).relabel_B (eA.prodCongr eB) (eA'.prodCongr eB')).op z := by
    rw [KrausChannel.tensorLanes_op_B]
    change (C.op z.1).submatrix eA' eA ⊗ₖ (D.op z.2).submatrix eB' eB =
      ((C.tensorLanes_B D).op z).submatrix (eA'.prodCongr eB') (eA.prodCongr eB)
    rw [KrausChannel.tensorLanes_op_B]
    ext x y
    rfl
  simp only [KrausChannel.eval,hop]

end LocalTensorIdentification

end QuantumProver.AmplitudeDamping.SecretKey.MatrixCoherentLaneOutput

namespace QuantumProver.AmplitudeDamping.SecretKey.MatrixCoherentLaneOutput

open Matrix Kronecker PublicHistory IndependentLanes PrivateTestResource
open PhysicalProtocol PhysicalProtocol.FiniteKeyProtocol PhysicalPurification
open QuantumProver.AmplitudeDamping.FiniteModel IdleEvePadding MatrixPublicCopy LaneRetainedOutput
open LaneMergeHistory PrivateTest

abbrev MatrixLiftAliceDim_B {p : ℝ} {a b af bf : ℕ}
    (P : FiniteKeyProtocol p a b af bf) (E : Type*) (d n : ℕ) :=
  Nat.card (Register (PhysicalLiftAlice_B P E d) (n+1))

abbrev MatrixLiftBobDim_B {p : ℝ} {a b af bf : ℕ}
    (P : FiniteKeyProtocol p a b af bf) (d n : ℕ) :=
  Nat.card (Register (PhysicalLiftBob_B P d) (n+1))

theorem independentLanes_matrix_physical_privateLift_B {E : Type*} [Fintype E] [DecidableEq E]
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {a b af bf d m n : ℕ}
    {P Q : FiniteProtocol p a b af bf} (hPadding : UniformPaddingDerivationB p m P Q)
    {R : FiniteBlockProtocolB p (n+1) (lanePowerDimB n a) (lanePowerDimB n b)
      (lanePowerDimB n af) (lanePowerDimB n bf)}
    (hLanes : IndependentLanesDerivationB p Q n R)
    (labelA : Fin af → Fin d) (labelB : Fin bf → Fin d) :
    ∃ S : FiniteBlockProtocolB p (n+1) (lanePowerDimB n a) (lanePowerDimB n b)
        (MatrixLiftAliceDim_B (fromQuantum_B P) E d n)
        (MatrixLiftBobDim_B (fromQuantum_B P) d n),
      S.calls = R.calls ∧ S.represented_toMatrix.calls = R.represented_toMatrix.calls ∧
      ∀ rho : Matrix ((Fin a × Fin b) × E) ((Fin a × Fin b) × E) ℂ,
        S.output (partialTraceRight (lanePriorMatrix_B rho n)) =
          ((matrix (partialTraceRight (((fromQuantum_B P).retainedProtocolPrivateLiftChannel
            (E := E) hp0 hp1 labelA labelB).eval rho)) (n+1)).submatrix
              (pairEquiv (PhysicalLiftAlice_B (fromQuantum_B P) E d)
                (PhysicalLiftBob_B (fromQuantum_B P) d) (n+1)).symm
              (pairEquiv (PhysicalLiftAlice_B (fromQuantum_B P) E d)
                (PhysicalLiftBob_B (fromQuantum_B P) d) (n+1)).symm).submatrix
            ((matrixIndex_B (Register (PhysicalLiftAlice_B (fromQuantum_B P) E d) (n+1))).prodCongr
              (matrixIndex_B (Register (PhysicalLiftBob_B (fromQuantum_B P) d) (n+1))))
            ((matrixIndex_B (Register (PhysicalLiftAlice_B (fromQuantum_B P) E d) (n+1))).prodCongr
              (matrixIndex_B (Register (PhysicalLiftBob_B (fromQuantum_B P) d) (n+1)))) := by
  rcases independentLanes_physical_privateLift_B (E := E) hp0 hp1 hPadding hLanes
    labelA labelB with ⟨j,k,hkj,eT,hTensor⟩
  letI : DecidableEq (Register (PhysicalLiftAlice_B (fromQuantum_B P) E d) (n+1)) :=
    registerDecidableEq (PhysicalLiftAlice_B (fromQuantum_B P) E d) (n+1)
  letI : DecidableEq (Register (PhysicalLiftBob_B (fromQuantum_B P) d) (n+1)) :=
    registerDecidableEq (PhysicalLiftBob_B (fromQuantum_B P) d) (n+1)
  rcases exists_copyPublic_retained_honest_B hp0 hp1 R (E := LaneEveRegister_B E n) with
    ⟨eCopyA,eCopyB,hCopy⟩
  let A := decodedLiftAliceChannel_B (E := E) (fromQuantum_B P) (fromQuantum_B Q) j k hkj labelA
  let B := decodedLiftBobChannel_B (fromQuantum_B P) (fromQuantum_B Q) j k hkj labelB
  let eA := eCopyA.trans (retainedLocalOutputEquiv_B af n eT)
  let eB := eCopyB.trans (retainedLocalOutputEquiv_B bf n eT)
  let eOA := matrixIndex_B (Register (PhysicalLiftAlice_B (fromQuantum_B P) E d) (n+1))
  let eOB := matrixIndex_B (Register (PhysicalLiftBob_B (fromQuantum_B P) d) (n+1))
  let CA := (channel A (n+1)).relabel_B eA eOA
  let CB := (channel B (n+1)).relabel_B eB eOB
  let S := postLocalChannels_B CA CB R.copyPublic
  refine ⟨S,?_,?_,?_⟩
  · rw [postLocalChannels_calls_B,FiniteBlockProtocolB.copyPublic_calls]
  · rw [postLocalChannels_scalar_calls_B,FiniteBlockProtocolB.copyPublic_scalar_calls_eq]
  · intro rho
    let M := partialTraceRight ((wholeRetainedChannelWithEve_B hp0 hp1 (blockExpansion_B R)
      (LaneEveRegister_B E n)).eval (lanePriorMatrix_B rho n))
    have hTarget : (localTensorChannel_B A B (n+1)).eval
        (M.submatrix ((retainedLocalOutputEquiv_B af n eT).prodCongr
          (retainedLocalOutputEquiv_B bf n eT)).symm
          ((retainedLocalOutputEquiv_B af n eT).prodCongr
            (retainedLocalOutputEquiv_B bf n eT)).symm) =
        (matrix (partialTraceRight (((fromQuantum_B P).retainedProtocolPrivateLiftChannel
          (E := E) hp0 hp1 labelA labelB).eval rho)) (n+1)).submatrix
            (pairEquiv (PhysicalLiftAlice_B (fromQuantum_B P) E d)
              (PhysicalLiftBob_B (fromQuantum_B P) d) (n+1)).symm
            (pairEquiv (PhysicalLiftAlice_B (fromQuantum_B P) E d)
              (PhysicalLiftBob_B (fromQuantum_B P) d) (n+1)).symm := by
      have h := hTensor rho
      rw [coherentLaneLocalChannel_B,KrausChannel.relabel_eval_B] at h
      simpa using h
    have hchart : (M.submatrix (eCopyA.prodCongr eCopyB) (eCopyA.prodCongr eCopyB)).submatrix
        (eA.prodCongr eB).symm (eA.prodCongr eB).symm =
      M.submatrix ((retainedLocalOutputEquiv_B af n eT).prodCongr
          (retainedLocalOutputEquiv_B bf n eT)).symm
        ((retainedLocalOutputEquiv_B af n eT).prodCongr
          (retainedLocalOutputEquiv_B bf n eT)).symm := by
      ext x y
      rcases x with ⟨xa,xb⟩
      rcases y with ⟨ya,yb⟩
      simp [eA,eB,Matrix.submatrix_apply,Equiv.prodCongr_apply,Equiv.trans_apply]
    change (postLocalChannels_B CA CB R.copyPublic).output
      (partialTraceRight (lanePriorMatrix_B rho n)) = _
    rw [postLocalChannels_output_B,hCopy (lanePriorMatrix_B rho n)]
    change (((channel A (n+1)).relabel_B eA eOA).tensorLanes_B
      ((channel B (n+1)).relabel_B eB eOB)).eval
        (M.submatrix (eCopyA.prodCongr eCopyB) (eCopyA.prodCongr eCopyB)) = _
    rw [bilocal_relabel_eval_B,KrausChannel.relabel_eval_B,hchart]
    have hTwo := localTensorChannel_eq_two_local_B A B (n+1)
      (M.submatrix ((retainedLocalOutputEquiv_B af n eT).prodCongr
        (retainedLocalOutputEquiv_B bf n eT)).symm
        ((retainedLocalOutputEquiv_B af n eT).prodCongr
          (retainedLocalOutputEquiv_B bf n eT)).symm)
    rw [← hTwo,hTarget]

theorem exists_matrix_physical_coherent_lanes_B {E : Type*} [Fintype E] [DecidableEq E]
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {a b af bf d : ℕ}
    (P : FiniteProtocol p a b af bf) (m : ℕ) (hP : P.calls ≤ m) (n : ℕ)
    (labelA : Fin af → Fin d) (labelB : Fin bf → Fin d) :
    ∃ Q : FiniteProtocol p a b af bf,
      UniformPaddingDerivationB p m P Q ∧ Q.calls ≤ m ∧ Q.UniformCallsB m ∧
    ∃ R : FiniteBlockProtocolB p (n+1) (lanePowerDimB n a) (lanePowerDimB n b)
      (lanePowerDimB n af) (lanePowerDimB n bf),
      IndependentLanesDerivationB p Q n R ∧ R.calls ≤ m ∧ (blockExpansion_B R).calls ≤ (n+1)*m ∧
    ∃ S : FiniteBlockProtocolB p (n+1) (lanePowerDimB n a) (lanePowerDimB n b)
        (MatrixLiftAliceDim_B (fromQuantum_B P) E d n)
        (MatrixLiftBobDim_B (fromQuantum_B P) d n),
      S.calls = R.calls ∧ S.represented_toMatrix.calls = R.represented_toMatrix.calls ∧
      S.calls ≤ m ∧ (blockExpansion_B S).calls ≤ (n+1)*m ∧
      ∀ rho : Matrix ((Fin a × Fin b) × E) ((Fin a × Fin b) × E) ℂ,
        S.output (partialTraceRight (lanePriorMatrix_B rho n)) =
          ((matrix (partialTraceRight (((fromQuantum_B P).retainedProtocolPrivateLiftChannel
            (E := E) hp0 hp1 labelA labelB).eval rho)) (n+1)).submatrix
              (pairEquiv (PhysicalLiftAlice_B (fromQuantum_B P) E d)
                (PhysicalLiftBob_B (fromQuantum_B P) d) (n+1)).symm
              (pairEquiv (PhysicalLiftAlice_B (fromQuantum_B P) E d)
                (PhysicalLiftBob_B (fromQuantum_B P) d) (n+1)).symm).submatrix
            ((matrixIndex_B (Register (PhysicalLiftAlice_B (fromQuantum_B P) E d) (n+1))).prodCongr
              (matrixIndex_B (Register (PhysicalLiftBob_B (fromQuantum_B P) d) (n+1))))
            ((matrixIndex_B (Register (PhysicalLiftAlice_B (fromQuantum_B P) E d) (n+1))).prodCongr
              (matrixIndex_B (Register (PhysicalLiftBob_B (fromQuantum_B P) d) (n+1)))) := by
  rcases P.exists_uniform_padding_with_derivationB m hP with ⟨Q,hPadding,hQC,hQU,hQO⟩
  rcases Q.exists_uniform_lanes_with_derivationB hQU n with ⟨R,hLanes,hRC,hRU,hRN,hRO⟩
  rcases independentLanes_matrix_physical_privateLift_B (E := E) hp0 hp1 hPadding hLanes labelA labelB with
    ⟨S,hSC,hSN,hSO⟩
  have hPhysical : (blockExpansion_B R).calls ≤ (n+1)*m := by
    simpa only [blockExpansion_B,fromQuantum_calls_B] using hRN
  refine ⟨Q,hPadding,hQC,hQU,R,hLanes,hRC,hPhysical,S,hSC,hSN,?_,?_,hSO⟩
  · simpa only [hSC] using hRC
  · simpa only [blockExpansion_B,fromQuantum_calls_B,hSN] using hPhysical

end QuantumProver.AmplitudeDamping.SecretKey.MatrixCoherentLaneOutput

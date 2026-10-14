import QuantumProver.InformationTheory.AmplitudeDamping.SecretKey.IdleEvePadding

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

attribute [local instance] Classical.propDecidable

open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix Kronecker

namespace QuantumProver.AmplitudeDamping.SecretKey.LaneRetainedOutput

open PhysicalProtocol PhysicalProtocol.FiniteKeyProtocol IndependentLanes PublicHistory
open LaneMergeHistory IdleEvePadding QuantumProver.AmplitudeDamping.FiniteModel

def copiedPairAliceEquiv_B {T U V : Type*} (eT : T ≃ U × V) (a c : ℕ) :
    (T × Fin (a * c)) ≃ ((U × Fin a) × (V × Fin c)) :=
  (eT.prodCongr (finProdFinEquiv : Fin a × Fin c ≃ Fin (a * c)).symm).trans
    (Equiv.prodProdProdComm _ _ _ _)

def copiedPairLabEquiv_B {T U V : Type*} (eT : T ≃ U × V) (a b c d : ℕ) :
    ((T × Fin (a * c)) × (T × Fin (b * d))) ≃
      (((U × Fin a) × (U × Fin b)) × ((V × Fin c) × (V × Fin d))) :=
  ((copiedPairAliceEquiv_B eT a c).prodCongr (copiedPairAliceEquiv_B eT b d)).trans
    (Equiv.prodProdProdComm _ _ _ _)

theorem wholeCopiedOperator_apply_B {p : ℝ} {a b af bf : ℕ}
    (P : FiniteKeyProtocol p a b af bf) (h : P.Environment)
    (x : (P.comparisonPublicHistory_B × Fin af) × (P.comparisonPublicHistory_B × Fin bf))
    (i : Fin a × Fin b) :
    wholePublicCopiedOperator_B P h x i =
      if x.1.1 = P.publicTranscript_B h ∧ x.2.1 = P.publicTranscript_B h then
        P.historyKraus_B h (x.1.2,x.2.2) i else 0 := by
  classical
  by_cases hA : x.1.1 = P.publicTranscript_B h <;>
    by_cases hB : x.2.1 = P.publicTranscript_B h <;>
      simp [wholePublicCopiedOperator_B,attachFlag_B,Matrix.mul_apply,
        Fintype.sum_prod_type,Matrix.kroneckerMap_apply,Matrix.one_apply,
        ite_mul,mul_ite,apply_ite,hA,hB]

theorem copiedPair_historyOperator_B {p : ℝ} {a b af bf c d cf df : ℕ}
    (P : FiniteKeyProtocol p a b af bf) (Q : FiniteKeyProtocol p c d cf df)
    (R : FiniteKeyProtocol p (a * c) (b * d) (af * cf) (bf * df))
    (eH : R.Environment ≃ P.Environment × Q.Environment)
    (eT : R.comparisonPublicHistory_B ≃ P.comparisonPublicHistory_B × Q.comparisonPublicHistory_B)
    (hK : ∀ h, R.historyKraus_B h =
      pairOperatorB (P.historyKraus_B (eH h).1) (Q.historyKraus_B (eH h).2))
    (hT : ∀ h, eT (R.publicTranscript_B h) =
      (P.publicTranscript_B (eH h).1,Q.publicTranscript_B (eH h).2)) (h : R.Environment) :
    wholePublicCopiedOperator_B R h =
      (wholePublicCopiedOperator_B P (eH h).1 ⊗ₖ wholePublicCopiedOperator_B Q (eH h).2).submatrix
        (copiedPairLabEquiv_B eT af bf cf df) (pairLabEquivB a b c d) := by
  ext x i
  rw [wholeCopiedOperator_apply_B]
  simp only [Matrix.submatrix_apply,Matrix.kroneckerMap_apply,wholeCopiedOperator_apply_B]
  have hpublic (j : R.comparisonPublicHistory_B) : j = R.publicTranscript_B h ↔
      (eT j).1 = P.publicTranscript_B (eH h).1 ∧
        (eT j).2 = Q.publicTranscript_B (eH h).2 := by
    calc
      _ ↔ eT j = eT (R.publicTranscript_B h) := eT.injective.eq_iff.symm
      _ ↔ _ := by rw [hT h,Prod.mk.injEq]
  simp only [hpublic x.1.1,hpublic x.2.1,hK h]
  by_cases hAP : (eT x.1.1).1 = P.publicTranscript_B (eH h).1 <;>
    by_cases hBP : (eT x.2.1).1 = P.publicTranscript_B (eH h).1 <;>
      by_cases hAQ : (eT x.1.1).2 = Q.publicTranscript_B (eH h).2 <;>
        by_cases hBQ : (eT x.2.1).2 = Q.publicTranscript_B (eH h).2 <;>
          simp [hAP,hBP,hAQ,hBQ,copiedPairLabEquiv_B,copiedPairAliceEquiv_B,
            pairOperatorB,pairLabEquivB,Matrix.kroneckerMap_apply]

theorem retainedPair_priorEve_B {E F : Type*} [Fintype E] [DecidableEq E]
    [Fintype F] [DecidableEq F] {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {a b af bf c d cf df : ℕ}
    (P : FiniteKeyProtocol p a b af bf) (Q : FiniteKeyProtocol p c d cf df)
    (R : FiniteKeyProtocol p (a * c) (b * d) (af * cf) (bf * df))
    (eH : R.Environment ≃ P.Environment × Q.Environment)
    (eT : R.comparisonPublicHistory_B ≃ P.comparisonPublicHistory_B × Q.comparisonPublicHistory_B)
    (hK : ∀ h, R.historyKraus_B h =
      pairOperatorB (P.historyKraus_B (eH h).1) (Q.historyKraus_B (eH h).2))
    (hT : ∀ h, eT (R.publicTranscript_B h) =
      (P.publicTranscript_B (eH h).1,Q.publicTranscript_B (eH h).2))
    (ρ : Matrix ((Fin a × Fin b) × E) ((Fin a × Fin b) × E) ℂ)
    (σ : Matrix ((Fin c × Fin d) × F) ((Fin c × Fin d) × F) ℂ)
    (x y : (R.comparisonPublicHistory_B × Fin (af * cf)) ×
      (R.comparisonPublicHistory_B × Fin (bf * df)))
    (h h' : R.Environment) (e e' : E) (f f' : F) :
    (wholeRetainedChannelWithEve_B hp0 hp1 R (E × F)).eval (pairPriorEveInput_B ρ σ)
        (x,(h,(e,f))) (y,(h',(e',f'))) =
      (wholeRetainedChannelWithEve_B hp0 hp1 P E).eval ρ
        ((copiedPairLabEquiv_B eT af bf cf df x).1,((eH h).1,e))
        ((copiedPairLabEquiv_B eT af bf cf df y).1,((eH h').1,e')) *
      (wholeRetainedChannelWithEve_B hp0 hp1 Q F).eval σ
        ((copiedPairLabEquiv_B eT af bf cf df x).2,((eH h).2,f))
        ((copiedPairLabEquiv_B eT af bf cf df y).2,((eH h').2,f')) := by
  simp only [wholeRetainedChannelWithEve_B,retainedWithPriorEve_eval_apply_B,
    wholePublicCopiedChannel_B]
  have hinput : Matrix.of (fun i j => pairPriorEveInput_B ρ σ (i,(e,f)) (j,(e',f'))) =
      ((Matrix.of fun i j => ρ (i,e) (j,e')) ⊗ₖ (Matrix.of fun i j => σ (i,f) (j,f'))).submatrix
        (pairLabEquivB a b c d) (pairLabEquivB a b c d) := rfl
  rw [copiedPair_historyOperator_B P Q R eH eT hK hT h,
    copiedPair_historyOperator_B P Q R eH eT hK hT h',hinput,
    Matrix.conjTranspose_submatrix,Matrix.submatrix_mul_equiv,Matrix.submatrix_mul_equiv,
    Matrix.conjTranspose_kronecker,← Matrix.mul_kronecker_mul,← Matrix.mul_kronecker_mul]
  rfl

theorem mergeScalar_retained_priorEve_B {E F : Type*} [Fintype E] [DecidableEq E]
    [Fintype F] [DecidableEq F] {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {n a b af bf c d cf df : ℕ}
    {P : FiniteBlockProtocolB p n a b af bf} {Q : FiniteProtocol p c d cf df}
    {R : FiniteBlockProtocolB p (n + 1) (a * c) (b * d) (af * cf) (bf * df)}
    (hR : MergeScalarDerivationB p n P Q R) :
    ∃ eH : (blockExpansion_B R).Environment ≃ (blockExpansion_B P).Environment × (fromQuantum_B Q).Environment,
    ∃ eT : (blockExpansion_B R).comparisonPublicHistory_B ≃
        (blockExpansion_B P).comparisonPublicHistory_B × (fromQuantum_B Q).comparisonPublicHistory_B,
    ∀ (ρ : Matrix ((Fin a × Fin b) × E) ((Fin a × Fin b) × E) ℂ)
      (σ : Matrix ((Fin c × Fin d) × F) ((Fin c × Fin d) × F) ℂ)
      (x y : ((blockExpansion_B R).comparisonPublicHistory_B × Fin (af * cf)) ×
        ((blockExpansion_B R).comparisonPublicHistory_B × Fin (bf * df)))
      (h h' : (blockExpansion_B R).Environment) (e e' : E) (f f' : F),
      (wholeRetainedChannelWithEve_B hp0 hp1 (blockExpansion_B R) (E × F)).eval
          (pairPriorEveInput_B ρ σ) (x,(h,(e,f))) (y,(h',(e',f'))) =
        (wholeRetainedChannelWithEve_B hp0 hp1 (blockExpansion_B P) E).eval ρ
          ((copiedPairLabEquiv_B eT af bf cf df x).1,((eH h).1,e))
          ((copiedPairLabEquiv_B eT af bf cf df y).1,((eH h').1,e')) *
        (wholeRetainedChannelWithEve_B hp0 hp1 (fromQuantum_B Q) F).eval σ
          ((copiedPairLabEquiv_B eT af bf cf df x).2,((eH h).2,f))
          ((copiedPairLabEquiv_B eT af bf cf df y).2,((eH h').2,f')) := by
  rcases mergeScalar_matrix_history_B hR with ⟨eH,eT,hK,hT⟩
  refine ⟨eH,eT,?_⟩
  intro ρ σ x y h h' e e' f f'
  exact retainedPair_priorEve_B hp0 hp1 (blockExpansion_B P) (fromQuantum_B Q)
    (blockExpansion_B R) eH eT hK hT ρ σ x y h h' e e' f f'

@[reducible] instance laneEveRegisterFintype_B (E : Type*) [Fintype E] :
    (n : ℕ) → Fintype (LaneEveRegister_B E n)
  | 0 => inferInstanceAs (Fintype E)
  | n + 1 =>
      letI := laneEveRegisterFintype_B E n
      inferInstanceAs (Fintype (LaneEveRegister_B E n × E))

@[reducible] instance laneEveRegisterDecidableEq_B (E : Type*) [DecidableEq E] :
    (n : ℕ) → DecidableEq (LaneEveRegister_B E n)
  | 0 => inferInstanceAs (DecidableEq E)
  | n + 1 =>
      letI := laneEveRegisterDecidableEq_B E n
      inferInstanceAs (DecidableEq (LaneEveRegister_B E n × E))

def laneLocalEquiv_B (a : ℕ) : (n : ℕ) → Fin (lanePowerDimB n a) ≃ Register (Fin a) (n + 1)
  | 0 => addEmptyTuple_B _
  | n + 1 =>
      (finProdFinEquiv : Fin (lanePowerDimB n a) × Fin a ≃ Fin (lanePowerDimB n a * a)).symm.trans
        (((laneLocalEquiv_B a n).prodCongr (Equiv.refl _)).trans (Equiv.prodComm _ _))

def laneEveTupleEquiv_B (E : Type*) : (n : ℕ) → LaneEveRegister_B E n ≃ Register E (n + 1)
  | 0 => addEmptyTuple_B _
  | n + 1 => ((laneEveTupleEquiv_B E n).prodCongr (Equiv.refl E)).trans (Equiv.prodComm _ _)

abbrev StandardRetained_B (T : Type*) (H : Type*) (E : Type*) (a b n : ℕ) :=
  ((Register T (n + 1) × Fin (lanePowerDimB n a)) ×
    (Register T (n + 1) × Fin (lanePowerDimB n b))) ×
      (Register H (n + 1) × LaneEveRegister_B E n)

def retainedCanonicalEquiv_B (T : Type*) (H : Type*) (E : Type*) (a b n : ℕ) :
    StandardRetained_B T H E a b n ≃
      Register (((T × Fin a) × (T × Fin b)) × (H × E)) (n + 1) :=
  let eA := ((Equiv.refl (Register T (n + 1))).prodCongr (laneLocalEquiv_B a n)).trans
    (pairEquiv T (Fin a) (n + 1)).symm
  let eB := ((Equiv.refl (Register T (n + 1))).prodCongr (laneLocalEquiv_B b n)).trans
    (pairEquiv T (Fin b) (n + 1)).symm
  let eE := (laneHistoryEveEquiv_B H E n).trans (laneEveTupleEquiv_B (H × E) n)
  (((eA.prodCongr eB).trans (pairEquiv (T × Fin a) (T × Fin b) (n + 1)).symm).prodCongr eE).trans
    (pairEquiv ((T × Fin a) × (T × Fin b)) (H × E) (n + 1)).symm

def retainedLaneMatrix_B {T H E : Type*} [Fintype T] [DecidableEq T]
    [Fintype H] [DecidableEq H] [Fintype E] [DecidableEq E] {a b : ℕ}
    (M : Matrix (((T × Fin a) × (T × Fin b)) × (H × E))
      (((T × Fin a) × (T × Fin b)) × (H × E)) ℂ) (n : ℕ) :
    Matrix (StandardRetained_B T H E a b n) (StandardRetained_B T H E a b n) ℂ :=
  (matrix M (n + 1)).submatrix (retainedCanonicalEquiv_B T H E a b n)
    (retainedCanonicalEquiv_B T H E a b n)

def retainedStandardEquiv_B {p : ℝ} {a b af bf n : ℕ}
    (R : FiniteKeyProtocol p (lanePowerDimB n a) (lanePowerDimB n b)
      (lanePowerDimB n af) (lanePowerDimB n bf))
    (T : Type*) (H : Type*) (E : Type*)
    (eH : R.Environment ≃ Register H (n + 1))
    (eT : R.comparisonPublicHistory_B ≃ Register T (n + 1)) :
    (((R.comparisonPublicHistory_B × Fin (lanePowerDimB n af)) ×
      (R.comparisonPublicHistory_B × Fin (lanePowerDimB n bf))) ×
        (R.Environment × LaneEveRegister_B E n)) ≃ StandardRetained_B T H E af bf n :=
  ((eT.prodCongr (Equiv.refl _)).prodCongr (eT.prodCongr (Equiv.refl _))).prodCongr
    (eH.prodCongr (Equiv.refl _))

theorem copiedOperator_relabel_B {p : ℝ} {a b af bf : ℕ}
    (P Q : FiniteKeyProtocol p a b af bf)
    (eH : Q.Environment ≃ P.Environment)
    (eT : Q.comparisonPublicHistory_B ≃ P.comparisonPublicHistory_B)
    (hK : ∀ h, Q.historyKraus_B h = P.historyKraus_B (eH h))
    (hT : ∀ h, eT (Q.publicTranscript_B h) = P.publicTranscript_B (eH h))
    (h : Q.Environment) :
    wholePublicCopiedOperator_B Q h =
      (wholePublicCopiedOperator_B P (eH h)).submatrix
        ((eT.prodCongr (Equiv.refl _)).prodCongr (eT.prodCongr (Equiv.refl _))) (Equiv.refl _) := by
  ext x i
  simp only [wholeCopiedOperator_apply_B,Matrix.submatrix_apply,
    Equiv.prodCongr_apply,Prod.map_fst,Prod.map_snd,Equiv.refl_apply]
  have hpublic (j : Q.comparisonPublicHistory_B) :
      j = Q.publicTranscript_B h ↔ eT j = P.publicTranscript_B (eH h) := by
    calc
      _ ↔ eT j = eT (Q.publicTranscript_B h) := eT.injective.eq_iff.symm
      _ ↔ _ := by rw [hT h]
  simp only [hpublic x.1.1,hpublic x.2.1,hK h]

theorem retained_relabel_priorEve_B {E : Type*} [Fintype E] [DecidableEq E]
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {a b af bf : ℕ}
    (P Q : FiniteKeyProtocol p a b af bf)
    (eH : Q.Environment ≃ P.Environment)
    (eT : Q.comparisonPublicHistory_B ≃ P.comparisonPublicHistory_B)
    (hK : ∀ h, Q.historyKraus_B h = P.historyKraus_B (eH h))
    (hT : ∀ h, eT (Q.publicTranscript_B h) = P.publicTranscript_B (eH h))
    (ρ : Matrix ((Fin a × Fin b) × E) ((Fin a × Fin b) × E) ℂ)
    (x y : (Q.comparisonPublicHistory_B × Fin af) × (Q.comparisonPublicHistory_B × Fin bf))
    (h h' : Q.Environment) (e e' : E) :
    (wholeRetainedChannelWithEve_B hp0 hp1 Q E).eval ρ (x,(h,e)) (y,(h',e')) =
      (wholeRetainedChannelWithEve_B hp0 hp1 P E).eval ρ
        (((eT.prodCongr (Equiv.refl _)).prodCongr (eT.prodCongr (Equiv.refl _))) x,(eH h,e))
        (((eT.prodCongr (Equiv.refl _)).prodCongr (eT.prodCongr (Equiv.refl _))) y,(eH h',e')) := by
  simp only [wholeRetainedChannelWithEve_B,retainedWithPriorEve_eval_apply_B,
    wholePublicCopiedChannel_B]
  rw [copiedOperator_relabel_B P Q eH eT hK hT h,copiedOperator_relabel_B P Q eH eT hK hT h']
  let eO := (eT.prodCongr (Equiv.refl (Fin af))).prodCongr (eT.prodCongr (Equiv.refl (Fin bf)))
  let eI := Equiv.refl (Fin a × Fin b)
  change ((wholePublicCopiedOperator_B P (eH h)).submatrix eO eI *
      (Matrix.of (fun i j => ρ (i,e) (j,e'))).submatrix eI eI *
        ((wholePublicCopiedOperator_B P (eH h')).submatrix eO eI)ᴴ) x y = _
  rw [Matrix.conjTranspose_submatrix,Matrix.submatrix_mul_equiv,Matrix.submatrix_mul_equiv]
  rfl

def retainedHead_B {T H E : Type*} {a b n : ℕ} (x : StandardRetained_B T H E a b (n + 1)) :
    ((T × Fin a) × (T × Fin b)) × (H × E) :=
  (((x.1.1.1.1,((finProdFinEquiv : Fin (lanePowerDimB n a) × Fin a ≃ Fin (lanePowerDimB n a * a)).symm x.1.1.2).2),
    (x.1.2.1.1,((finProdFinEquiv : Fin (lanePowerDimB n b) × Fin b ≃ Fin (lanePowerDimB n b * b)).symm x.1.2.2).2)),
      (x.2.1.1,x.2.2.2))

def retainedTail_B {T H E : Type*} {a b n : ℕ} (x : StandardRetained_B T H E a b (n + 1)) :
    StandardRetained_B T H E a b n :=
  (((x.1.1.1.2,((finProdFinEquiv : Fin (lanePowerDimB n a) × Fin a ≃ Fin (lanePowerDimB n a * a)).symm x.1.1.2).1),
    (x.1.2.1.2,((finProdFinEquiv : Fin (lanePowerDimB n b) × Fin b ≃ Fin (lanePowerDimB n b * b)).symm x.1.2.2).1)),
      (x.2.1.2,x.2.2.1))

theorem retainedLaneMatrix_zero_B {T H E : Type*} [Fintype T] [DecidableEq T]
    [Fintype H] [DecidableEq H] [Fintype E] [DecidableEq E] {a b : ℕ}
    (M : Matrix (((T × Fin a) × (T × Fin b)) × (H × E))
      (((T × Fin a) × (T × Fin b)) × (H × E)) ℂ)
    (x y : StandardRetained_B T H E a b 0) :
    retainedLaneMatrix_B M 0 x y =
      M (((x.1.1.1.1,x.1.1.2),(x.1.2.1.1,x.1.2.2)),(x.2.1.1,x.2.2))
        (((y.1.1.1.1,y.1.1.2),(y.1.2.1.1,y.1.2.2)),(y.2.1.1,y.2.2)) := by
  simp [retainedLaneMatrix_B,retainedCanonicalEquiv_B,laneLocalEquiv_B,
    laneHistoryEveEquiv_B,laneEveTupleEquiv_B,pairEquiv,matrix,addEmptyTuple_B,
    Matrix.kroneckerMap_apply,Equiv.prodCongr_apply,Prod.map_fst,Prod.map_snd,Equiv.refl_apply]
  all_goals rfl

theorem retainedLaneMatrix_succ_B {T H E : Type*} [Fintype T] [DecidableEq T]
    [Fintype H] [DecidableEq H] [Fintype E] [DecidableEq E] {a b : ℕ}
    (M : Matrix (((T × Fin a) × (T × Fin b)) × (H × E))
      (((T × Fin a) × (T × Fin b)) × (H × E)) ℂ) (n : ℕ)
    (x y : StandardRetained_B T H E a b (n + 1)) :
    retainedLaneMatrix_B M (n + 1) x y =
      retainedLaneMatrix_B M n (retainedTail_B x) (retainedTail_B y) *
        M (retainedHead_B x) (retainedHead_B y) := by
  change M (retainedHead_B x) (retainedHead_B y) *
    retainedLaneMatrix_B M n (retainedTail_B x) (retainedTail_B y) = _
  exact mul_comm _ _

theorem independentLanes_retained_priorEve_B {E : Type*} [Fintype E] [DecidableEq E]
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {a b af bf n : ℕ}
    {P : FiniteProtocol p a b af bf}
    {R : FiniteBlockProtocolB p (n + 1) (lanePowerDimB n a) (lanePowerDimB n b)
      (lanePowerDimB n af) (lanePowerDimB n bf)}
    (h : IndependentLanesDerivationB p P n R) :
    ∃ eH : (blockExpansion_B R).Environment ≃ Register (fromQuantum_B P).Environment (n + 1),
    ∃ eT : (blockExpansion_B R).comparisonPublicHistory_B ≃
        Register (fromQuantum_B P).comparisonPublicHistory_B (n + 1),
      (∀ t, (blockExpansion_B R).historyKraus_B t = laneHistoryKraus_B P n (eH t)) ∧
      (∀ t, eT ((blockExpansion_B R).publicTranscript_B t) = lanePublicTranscript_B P n (eH t)) ∧
    ∀ ρ : Matrix ((Fin a × Fin b) × E) ((Fin a × Fin b) × E) ℂ,
      (wholeRetainedChannelWithEve_B hp0 hp1 (blockExpansion_B R) (LaneEveRegister_B E n)).eval
          (lanePriorMatrix_B ρ n) =
        (retainedLaneMatrix_B ((wholeRetainedChannelWithEve_B hp0 hp1 (fromQuantum_B P) E).eval ρ) n).submatrix
          (retainedStandardEquiv_B (blockExpansion_B R)
            (fromQuantum_B P).comparisonPublicHistory_B (fromQuantum_B P).Environment E eH eT)
          (retainedStandardEquiv_B (blockExpansion_B R)
            (fromQuantum_B P).comparisonPublicHistory_B (fromQuantum_B P).Environment E eH eT) := by
  induction h with
  | one =>
      let eH0 := (blockOneEnvironmentEquiv_B P).trans (addEmptyTuple_B _)
      let eT0 := (blockOnePublicEquiv_B P).trans (addEmptyTuple_B _)
      refine ⟨eH0,eT0,?_,?_,?_⟩
      · exact blockOne_historyKraus_B P
      · intro t
        exact congrArg (fun u => (u,PUnit.unit)) (blockOne_publicTranscript_B P t)
      · intro ρ
        ext x y
        let Z := retainedStandardEquiv_B (a := a) (b := b) (af := af) (bf := bf) (n := 0)
          (blockExpansion_B P.toBlockOneB)
          (fromQuantum_B P).comparisonPublicHistory_B (fromQuantum_B P).Environment E eH0 eT0
        have hz := retainedLaneMatrix_zero_B
          ((wholeRetainedChannelWithEve_B hp0 hp1 (fromQuantum_B P) E).eval ρ) (Z x) (Z y)
        exact (retained_relabel_priorEve_B hp0 hp1 (fromQuantum_B P)
          (blockExpansion_B P.toBlockOneB) (blockOneEnvironmentEquiv_B P)
          (blockOnePublicEquiv_B P) (blockOne_historyKraus_B P) (blockOne_publicTranscript_B P)
          ρ x.1 y.1 x.2.1 y.2.1 x.2.2 y.2.2).trans
            hz.symm
  | @append n R S previous merge ih =>
      rcases ih with ⟨eH,eT,hK,hT,hO⟩
      rcases mergeScalar_matrix_history_B merge with ⟨eM,eMT,hMK,hMT⟩
      let eHC := eM.trans ((eH.prodCongr (Equiv.refl _)).trans (Equiv.prodComm _ _))
      let eTC := eMT.trans ((eT.prodCongr (Equiv.refl _)).trans (Equiv.prodComm _ _))
      refine ⟨eHC,eTC,?_,?_,?_⟩
      · intro t
        exact (hMK t).trans (congrArg
          (fun M => pairOperatorB M ((fromQuantum_B P).historyKraus_B (eM t).2)) (hK (eM t).1))
      · intro t
        exact (congrArg (fun u => (u.2,eT u.1)) (hMT t)).trans
          (congrArg (fun u => ((fromQuantum_B P).publicTranscript_B (eM t).2,u)) (hT (eM t).1))
      · intro ρ
        ext x y
        let Z := retainedStandardEquiv_B (blockExpansion_B S)
          (fromQuantum_B P).comparisonPublicHistory_B (fromQuantum_B P).Environment E eHC eTC
        have hs := retainedLaneMatrix_succ_B
          ((wholeRetainedChannelWithEve_B hp0 hp1 (fromQuantum_B P) E).eval ρ) n (Z x) (Z y)
        have hpair := retainedPair_priorEve_B hp0 hp1 (blockExpansion_B R) (fromQuantum_B P)
          (blockExpansion_B S) eM eMT hMK hMT (lanePriorMatrix_B ρ n) ρ x.1 y.1
          x.2.1 y.2.1 x.2.2.1 y.2.2.1 x.2.2.2 y.2.2.2
        have htail := congrArg (fun M => M
          ((copiedPairLabEquiv_B eMT (lanePowerDimB n af) (lanePowerDimB n bf) af bf x.1).1,
            ((eM x.2.1).1,x.2.2.1))
          ((copiedPairLabEquiv_B eMT (lanePowerDimB n af) (lanePowerDimB n bf) af bf y.1).1,
            ((eM y.2.1).1,y.2.2.1))) (hO ρ)
        exact hpair.trans ((congrArg (fun v => v *
          (wholeRetainedChannelWithEve_B hp0 hp1 (fromQuantum_B P) E).eval ρ
            ((copiedPairLabEquiv_B eMT (lanePowerDimB n af) (lanePowerDimB n bf) af bf x.1).2,
              ((eM x.2.1).2,x.2.2.2))
            ((copiedPairLabEquiv_B eMT (lanePowerDimB n af) (lanePowerDimB n bf) af bf y.1).2,
              ((eM y.2.1).2,y.2.2.2))) htail).trans
          hs.symm)

def retainedWholeEquiv_B {p : ℝ} {a b af bf n : ℕ}
    (R : FiniteKeyProtocol p (lanePowerDimB n a) (lanePowerDimB n b)
      (lanePowerDimB n af) (lanePowerDimB n bf))
    (T : Type*) (H : Type*) (E : Type*)
    (eH : R.Environment ≃ Register H (n + 1))
    (eT : R.comparisonPublicHistory_B ≃ Register T (n + 1)) :=
  (retainedStandardEquiv_B R T H E eH eT).trans
    (retainedCanonicalEquiv_B T H E af bf n)

theorem independentLanes_retained_tensor_B {E : Type*} [Fintype E] [DecidableEq E]
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {a b af bf n : ℕ}
    {P : FiniteProtocol p a b af bf}
    {R : FiniteBlockProtocolB p (n + 1) (lanePowerDimB n a) (lanePowerDimB n b)
      (lanePowerDimB n af) (lanePowerDimB n bf)}
    (h : IndependentLanesDerivationB p P n R) :
    ∃ eH : (blockExpansion_B R).Environment ≃ Register (fromQuantum_B P).Environment (n + 1),
    ∃ eT : (blockExpansion_B R).comparisonPublicHistory_B ≃
        Register (fromQuantum_B P).comparisonPublicHistory_B (n + 1),
      (∀ t, (blockExpansion_B R).historyKraus_B t = laneHistoryKraus_B P n (eH t)) ∧
      (∀ t, eT ((blockExpansion_B R).publicTranscript_B t) = lanePublicTranscript_B P n (eH t)) ∧
    ∀ ρ : Matrix ((Fin a × Fin b) × E) ((Fin a × Fin b) × E) ℂ,
      (wholeRetainedChannelWithEve_B hp0 hp1 (blockExpansion_B R) (LaneEveRegister_B E n)).eval
          (lanePriorMatrix_B ρ n) =
        (matrix ((wholeRetainedChannelWithEve_B hp0 hp1 (fromQuantum_B P) E).eval ρ) (n + 1)).submatrix
          (retainedWholeEquiv_B (blockExpansion_B R)
            (fromQuantum_B P).comparisonPublicHistory_B (fromQuantum_B P).Environment E eH eT)
          (retainedWholeEquiv_B (blockExpansion_B R)
            (fromQuantum_B P).comparisonPublicHistory_B (fromQuantum_B P).Environment E eH eT) := by
  rcases independentLanes_retained_priorEve_B hp0 hp1 (E := E) h with ⟨eH,eT,hK,hT,hO⟩
  exact ⟨eH,eT,hK,hT,hO⟩

theorem partialTraceRight_submatrix_prodEquiv_B {I J E F : Type*}
    [Fintype E] [Fintype F] (eI : J ≃ I) (eE : F ≃ E)
    (M : Matrix (I × E) (I × E) ℂ) :
    partialTraceRight (M.submatrix (eI.prodCongr eE) (eI.prodCongr eE)) =
      (partialTraceRight M).submatrix eI eI := by
  ext x y
  exact Fintype.sum_equiv eE _ _ (fun _ => rfl)

theorem partialTraceRight_tensor_B {I E : Type*} [Fintype I] [DecidableEq I]
    [Fintype E] [DecidableEq E] (M : Matrix (I × E) (I × E) ℂ) (n : ℕ) :
    partialTraceRight ((matrix M n).submatrix (pairEquiv I E n).symm (pairEquiv I E n).symm) =
      matrix (partialTraceRight M) n := by
  induction n with
  | zero =>
      ext x y
      cases x
      cases y
      simp [partialTraceRight,matrix,pairEquiv,Matrix.one_apply]
  | succ n ih =>
      ext x y
      simp only [partialTraceRight,Fintype.sum_prod_type]
      change (∑ e : E, ∑ es : Register E n,
        M (x.1,e) (y.1,e) *
          matrix M n ((pairEquiv I E n).symm (x.2,es)) ((pairEquiv I E n).symm (y.2,es))) =
        (∑ e : E, M (x.1,e) (y.1,e)) * matrix (partialTraceRight M) n x.2 y.2
      simp_rw [← Finset.mul_sum]
      rw [← Finset.sum_mul]
      exact congrArg (fun v => (∑ e : E, M (x.1,e) (y.1,e)) * v)
        (congrArg (fun N => N x.2 y.2) ih)

def retainedLocalOutputEquiv_B {T U : Type*} (a n : ℕ)
    (eT : T ≃ Register U (n + 1)) :
    (T × Fin (lanePowerDimB n a)) ≃ Register (U × Fin a) (n + 1) :=
  (eT.prodCongr (laneLocalEquiv_B a n)).trans (pairEquiv U (Fin a) (n + 1)).symm

def retainedHonestOutputEquiv_B {T U : Type*} (a b n : ℕ)
    (eT : T ≃ Register U (n + 1)) :
    ((T × Fin (lanePowerDimB n a)) × (T × Fin (lanePowerDimB n b))) ≃
      Register ((U × Fin a) × (U × Fin b)) (n + 1) :=
  ((retainedLocalOutputEquiv_B a n eT).prodCongr
    (retainedLocalOutputEquiv_B b n eT)).trans
      (pairEquiv (U × Fin a) (U × Fin b) (n + 1)).symm

def retainedEveOutputEquiv_B {H J E : Type*} (n : ℕ) (eH : J ≃ Register H (n + 1)) :
    (J × LaneEveRegister_B E n) ≃ Register (H × E) (n + 1) :=
  ((eH.prodCongr (Equiv.refl _)).trans (laneHistoryEveEquiv_B H E n)).trans
    (laneEveTupleEquiv_B (H × E) n)

theorem retained_tensor_honest_chart_B {p : ℝ} {a b af bf n : ℕ}
    (R : FiniteKeyProtocol p (lanePowerDimB n a) (lanePowerDimB n b)
      (lanePowerDimB n af) (lanePowerDimB n bf))
    {T H E : Type*} [Fintype T] [DecidableEq T] [Fintype H] [DecidableEq H]
    [Fintype E] [DecidableEq E]
    (eH : R.Environment ≃ Register H (n + 1))
    (eT : R.comparisonPublicHistory_B ≃ Register T (n + 1))
    (M : Matrix (((T × Fin af) × (T × Fin bf)) × (H × E))
      (((T × Fin af) × (T × Fin bf)) × (H × E)) ℂ) :
    partialTraceRight ((matrix M (n + 1)).submatrix (retainedWholeEquiv_B R T H E eH eT)
      (retainedWholeEquiv_B R T H E eH eT)) =
      (matrix (partialTraceRight M) (n + 1)).submatrix
        (retainedHonestOutputEquiv_B af bf n eT) (retainedHonestOutputEquiv_B af bf n eT) := by
  let Z := ((matrix M (n + 1)).submatrix
    (pairEquiv _ _ (n + 1)).symm (pairEquiv _ _ (n + 1)).symm)
  let eA := retainedHonestOutputEquiv_B af bf n eT
  let eE := retainedEveOutputEquiv_B (E := E) n eH
  change partialTraceRight (Z.submatrix (eA.prodCongr eE) (eA.prodCongr eE)) = _
  exact (partialTraceRight_submatrix_prodEquiv_B eA eE Z).trans
    (congrArg (fun N => N.submatrix eA eA) (partialTraceRight_tensor_B M (n + 1)))

theorem independentLanes_retained_honest_B {E : Type*} [Fintype E] [DecidableEq E]
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {a b af bf n : ℕ}
    {P : FiniteProtocol p a b af bf}
    {R : FiniteBlockProtocolB p (n + 1) (lanePowerDimB n a) (lanePowerDimB n b)
      (lanePowerDimB n af) (lanePowerDimB n bf)}
    (h : IndependentLanesDerivationB p P n R) :
    ∃ eH : (blockExpansion_B R).Environment ≃ Register (fromQuantum_B P).Environment (n + 1),
    ∃ eT : (blockExpansion_B R).comparisonPublicHistory_B ≃
        Register (fromQuantum_B P).comparisonPublicHistory_B (n + 1),
      (∀ t, (blockExpansion_B R).historyKraus_B t = laneHistoryKraus_B P n (eH t)) ∧
      (∀ t, eT ((blockExpansion_B R).publicTranscript_B t) = lanePublicTranscript_B P n (eH t)) ∧
    ∀ ρ : Matrix ((Fin a × Fin b) × E) ((Fin a × Fin b) × E) ℂ,
      partialTraceRight
        ((wholeRetainedChannelWithEve_B hp0 hp1 (blockExpansion_B R) (LaneEveRegister_B E n)).eval
          (lanePriorMatrix_B ρ n)) =
        (matrix (partialTraceRight
          ((wholeRetainedChannelWithEve_B hp0 hp1 (fromQuantum_B P) E).eval ρ)) (n + 1)).submatrix
            (retainedHonestOutputEquiv_B af bf n eT) (retainedHonestOutputEquiv_B af bf n eT) := by
  rcases independentLanes_retained_tensor_B hp0 hp1 (E := E) h with ⟨eH,eT,hK,hT,hO⟩
  refine ⟨eH,eT,hK,hT,?_⟩
  intro ρ
  exact (congrArg partialTraceRight (hO ρ)).trans
    (retained_tensor_honest_chart_B (blockExpansion_B R) eH eT
      ((wholeRetainedChannelWithEve_B hp0 hp1 (fromQuantum_B P) E).eval ρ))

theorem exists_uniformLanes_retained_B {E : Type*} [Fintype E] [DecidableEq E]
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {a b af bf m : ℕ}
    (P : FiniteProtocol p a b af bf) (hP : P.UniformCallsB m) (n : ℕ) :
    ∃ R : FiniteBlockProtocolB p (n + 1) (lanePowerDimB n a) (lanePowerDimB n b)
        (lanePowerDimB n af) (lanePowerDimB n bf),
      IndependentLanesDerivationB p P n R ∧ R.calls ≤ m ∧
        (blockExpansion_B R).calls ≤ (n + 1) * m ∧
    ∃ eH : (blockExpansion_B R).Environment ≃ Register (fromQuantum_B P).Environment (n + 1),
    ∃ eT : (blockExpansion_B R).comparisonPublicHistory_B ≃
        Register (fromQuantum_B P).comparisonPublicHistory_B (n + 1),
      (∀ t, (blockExpansion_B R).historyKraus_B t = laneHistoryKraus_B P n (eH t)) ∧
      (∀ t, eT ((blockExpansion_B R).publicTranscript_B t) = lanePublicTranscript_B P n (eH t)) ∧
    ∀ ρ : Matrix ((Fin a × Fin b) × E) ((Fin a × Fin b) × E) ℂ,
      ((wholeRetainedChannelWithEve_B hp0 hp1 (blockExpansion_B R) (LaneEveRegister_B E n)).eval
          (lanePriorMatrix_B ρ n) =
        (matrix ((wholeRetainedChannelWithEve_B hp0 hp1 (fromQuantum_B P) E).eval ρ) (n + 1)).submatrix
          (retainedWholeEquiv_B (blockExpansion_B R)
            (fromQuantum_B P).comparisonPublicHistory_B (fromQuantum_B P).Environment E eH eT)
          (retainedWholeEquiv_B (blockExpansion_B R)
            (fromQuantum_B P).comparisonPublicHistory_B (fromQuantum_B P).Environment E eH eT)) ∧
      partialTraceRight
        ((wholeRetainedChannelWithEve_B hp0 hp1 (blockExpansion_B R) (LaneEveRegister_B E n)).eval
          (lanePriorMatrix_B ρ n)) =
        (matrix (partialTraceRight
          ((wholeRetainedChannelWithEve_B hp0 hp1 (fromQuantum_B P) E).eval ρ)) (n + 1)).submatrix
            (retainedHonestOutputEquiv_B af bf n eT) (retainedHonestOutputEquiv_B af bf n eT) := by
  rcases P.exists_uniform_lanes_with_derivationB hP n with ⟨R,hR,hRC,hRU,hRN,hRO⟩
  rcases independentLanes_calls_B hR hP with ⟨hC,hN⟩
  rcases independentLanes_retained_tensor_B hp0 hp1 (E := E) hR with ⟨eH,eT,hK,hT,hO⟩
  refine ⟨R,hR,hC,hN,eH,eT,hK,hT,?_⟩
  intro ρ
  refine ⟨hO ρ,?_⟩
  exact (congrArg partialTraceRight (hO ρ)).trans
    (retained_tensor_honest_chart_B (blockExpansion_B R) eH eT
      ((wholeRetainedChannelWithEve_B hp0 hp1 (fromQuantum_B P) E).eval ρ))

theorem exists_paddedLanes_retained_B {E : Type*} [Fintype E] [DecidableEq E]
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {a b af bf : ℕ}
    (P : FiniteProtocol p a b af bf) (m : ℕ) (hP : P.calls ≤ m) (n : ℕ) :
    ∃ Q : FiniteProtocol p a b af bf,
      UniformPaddingDerivationB p m P Q ∧ Q.calls ≤ m ∧ Q.UniformCallsB m ∧
    ∃ R : FiniteBlockProtocolB p (n + 1) (lanePowerDimB n a) (lanePowerDimB n b)
        (lanePowerDimB n af) (lanePowerDimB n bf),
      IndependentLanesDerivationB p Q n R ∧ R.calls ≤ m ∧
        (blockExpansion_B R).calls ≤ (n + 1) * m ∧
    ∃ eH : (blockExpansion_B R).Environment ≃ Register (fromQuantum_B Q).Environment (n + 1),
    ∃ eT : (blockExpansion_B R).comparisonPublicHistory_B ≃
        Register (fromQuantum_B Q).comparisonPublicHistory_B (n + 1),
      (∀ t, (blockExpansion_B R).historyKraus_B t = laneHistoryKraus_B Q n (eH t)) ∧
      (∀ t, eT ((blockExpansion_B R).publicTranscript_B t) = lanePublicTranscript_B Q n (eH t)) ∧
    ∀ ρ : Matrix ((Fin a × Fin b) × E) ((Fin a × Fin b) × E) ℂ,
      ((wholeRetainedChannelWithEve_B hp0 hp1 (blockExpansion_B R) (LaneEveRegister_B E n)).eval
          (lanePriorMatrix_B ρ n) =
        (matrix ((wholeRetainedChannelWithEve_B hp0 hp1 (fromQuantum_B Q) E).eval ρ) (n + 1)).submatrix
          (retainedWholeEquiv_B (blockExpansion_B R)
            (fromQuantum_B Q).comparisonPublicHistory_B (fromQuantum_B Q).Environment E eH eT)
          (retainedWholeEquiv_B (blockExpansion_B R)
            (fromQuantum_B Q).comparisonPublicHistory_B (fromQuantum_B Q).Environment E eH eT)) ∧
      partialTraceRight
        ((wholeRetainedChannelWithEve_B hp0 hp1 (blockExpansion_B R) (LaneEveRegister_B E n)).eval
          (lanePriorMatrix_B ρ n)) =
        (matrix (partialTraceRight
          ((wholeRetainedChannelWithEve_B hp0 hp1 (fromQuantum_B Q) E).eval ρ)) (n + 1)).submatrix
            (retainedHonestOutputEquiv_B af bf n eT) (retainedHonestOutputEquiv_B af bf n eT) := by
  rcases P.exists_uniform_padding_with_derivationB m hP with ⟨Q,hQ,hQC,hQU,hQO⟩
  exact ⟨Q,hQ,hQC,hQU,exists_uniformLanes_retained_B hp0 hp1 (E := E) Q hQU n⟩

end QuantumProver.AmplitudeDamping.SecretKey.LaneRetainedOutput

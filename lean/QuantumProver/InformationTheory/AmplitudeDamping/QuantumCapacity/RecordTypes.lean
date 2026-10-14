import QuantumProver.InformationTheory.AmplitudeDamping.QuantumCapacity.BlockComparison

set_option autoImplicit false

noncomputable section

open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder Matrix Kronecker

namespace QuantumProver.AmplitudeDamping.FiniteModel

section BasisMatrices

variable {I O : Type*} [Fintype I] [Fintype O] [DecidableEq I] [DecidableEq O]

def basisEmbeddingC (f : I → O) : Matrix O I ℂ :=
  fun o i => if o = f i then 1 else 0

theorem basisEmbeddingC_complete (f : I → O) (hf : Function.Injective f) :
    (basisEmbeddingC f)ᴴ * basisEmbeddingC f = 1 := by
  ext i j
  rw [Matrix.mul_apply, Finset.sum_eq_single (f i)]
  · simp [basisEmbeddingC, Matrix.conjTranspose_apply, Matrix.one_apply, hf.eq_iff]
  · intro o _ hne
    simp [basisEmbeddingC, Matrix.conjTranspose_apply, hne]
  · intro h
    exact False.elim (h (Finset.mem_univ (f i)))

theorem basisEmbeddingC_mul_entry {J : Type*} (f : I → O)
    (M : Matrix J O ℂ) (j : J) (i : I) :
    (M * basisEmbeddingC f) j i = M j (f i) := by
  simp [Matrix.mul_apply, basisEmbeddingC, mul_ite]

theorem basisEmbeddingC_id : basisEmbeddingC (id : I → I) = 1 := by
  ext i j
  simp [basisEmbeddingC, Matrix.one_apply]

theorem basisEmbeddingC_compose {J : Type*} [Fintype J] [DecidableEq J]
    (f : O → J) (g : I → O) :
    basisEmbeddingC f * basisEmbeddingC g = basisEmbeddingC (f ∘ g) := by
  ext j i
  exact basisEmbeddingC_mul_entry g (basisEmbeddingC f) j i

theorem basisEmbeddingC_kronecker {J P : Type*} [Fintype J] [Fintype P]
    [DecidableEq J] [DecidableEq P] (f : I → O) (g : J → P) :
    basisEmbeddingC f ⊗ₖ basisEmbeddingC g =
      basisEmbeddingC (fun y : I × J => (f y.1, g y.2)) := by
  ext ⟨o, p⟩ ⟨i, j⟩
  by_cases ho : o = f i <;> by_cases hp : p = g j <;>
    simp [basisEmbeddingC, Matrix.kronecker_apply, ho, hp]

theorem diagonal_basisEmbeddingC (f : I → O) (d : O → ℂ) :
    Matrix.diagonal d * basisEmbeddingC f =
      basisEmbeddingC f * Matrix.diagonal (d ∘ f) := by
  ext o i
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal, basisEmbeddingC]
  by_cases h : o = f i
  · subst o
    simp
  · simp [h]

end BasisMatrices

def typeInclusionC (n w : ℕ) : Matrix (Finset (Fin n)) (WeightBasisB n w) ℂ :=
  basisEmbeddingC Subtype.val

theorem typeInclusionC_complete (n w : ℕ) :
    (typeInclusionC n w)ᴴ * typeInclusionC n w = 1 :=
  basisEmbeddingC_complete _ Subtype.val_injective

def weightProjectionC (n w : ℕ) : Matrix (Finset (Fin n)) (Finset (Fin n)) ℂ :=
  Matrix.diagonal (fun S => if S.card = w then 1 else 0)

theorem typeInclusionC_projection (n w : ℕ) :
    typeInclusionC n w * (typeInclusionC n w)ᴴ = weightProjectionC n w := by
  ext S T
  by_cases hS : S.card = w
  · let s : WeightBasisB n w := ⟨S, hS⟩
    rw [Matrix.mul_apply, Finset.sum_eq_single s]
    · by_cases hST : S = T
      · subst T
        simp [typeInclusionC, basisEmbeddingC, Matrix.conjTranspose_apply,
          weightProjectionC, Matrix.diagonal_apply, s, hS]
      · simp [typeInclusionC, basisEmbeddingC, Matrix.conjTranspose_apply,
          weightProjectionC, Matrix.diagonal_apply, s, hST, Ne.symm hST]
    · intro t _ hne
      have ht : S ≠ t.val := fun h => hne (Subtype.ext h.symm)
      simp [typeInclusionC, basisEmbeddingC, ht]
    · intro h
      exact False.elim (h (Finset.mem_univ s))
  · have ht : ∀ t : WeightBasisB n w, S ≠ t.val := by
      intro t h
      exact hS ((congrArg Finset.card h).trans t.property)
    simp [Matrix.mul_apply, typeInclusionC, basisEmbeddingC, ht,
      weightProjectionC, Matrix.diagonal_apply, hS]

def weightLabelC {n : ℕ} (S : Finset (Fin n)) : Fin (n + 1) :=
  ⟨S.card, Nat.lt_succ_of_le (S.card_le_univ.trans_eq (Fintype.card_fin n))⟩

theorem weightProjectionC_family (n : ℕ) :
    QuantumProver.SuperchannelDiscrimination.Pinching.IsProjectionFamily
      (fun w : Fin (n + 1) => weightProjectionC n w.val) := by
  constructor
  · intro w
    ext S T
    by_cases hST : S = T
    · subst T
      simp [weightProjectionC, Matrix.conjTranspose_apply, Matrix.diagonal_apply]
    · simp [weightProjectionC, Matrix.conjTranspose_apply, Matrix.diagonal_apply,
        hST, Ne.symm hST]
  · intro w
    rw [weightProjectionC, Matrix.diagonal_mul_diagonal]
    congr 1
    funext S
    split_ifs <;> simp
  · intro w v hwv
    rw [weightProjectionC, weightProjectionC, Matrix.diagonal_mul_diagonal]
    ext S T
    by_cases hS : S.card = w.val
    · have hv : S.card ≠ v.val := fun h => hwv (Fin.ext (hS.symm.trans h))
      have hvals : w.val ≠ v.val := fun h => hwv (Fin.ext h)
      simp [Matrix.diagonal_apply, hS, hv, hvals]
    · simp [Matrix.diagonal_apply, hS]
  · ext S T
    by_cases hST : S = T
    · subst T
      have hiff (w : Fin (n + 1)) : S.card = w.val ↔ weightLabelC S = w :=
        ⟨fun h => Fin.ext h, fun h => congrArg Fin.val h⟩
      simp [Matrix.sum_apply, weightProjectionC, Matrix.diagonal_apply,
        Matrix.one_apply, hiff]
    · simp [Matrix.sum_apply, weightProjectionC, Matrix.diagonal_apply, hST,
        Matrix.one_apply]

section OldMemories

variable (n w : ℕ) (A B : Type*) [Fintype A] [Fintype B]
  [DecidableEq A] [DecidableEq B]

def recordCopyMemoryC : Matrix ((A × Finset (Fin n)) × Finset (Fin n))
    (A × Finset (Fin n)) ℂ :=
  basisEmbeddingC (fun y => ((y.1, y.2), y.2))

theorem recordCopyMemoryC_complete :
    (recordCopyMemoryC n A)ᴴ * recordCopyMemoryC n A = 1 := by
  apply basisEmbeddingC_complete
  intro y z h
  exact congrArg Prod.fst h

def typeCopyMemoryC :
    Matrix ((A × Finset (Fin n)) × WeightBasisB n w) (A × Finset (Fin n)) ℂ :=
  basisEmbeddingC (fun y : A × WeightBasisB n w => ((y.1, y.2.val), y.2)) *
    ((1 : Matrix A A ℂ) ⊗ₖ typeInclusionC n w)ᴴ

theorem typeCopyMemoryC_gram :
    (typeCopyMemoryC n w A)ᴴ * typeCopyMemoryC n w A =
      (1 : Matrix A A ℂ) ⊗ₖ weightProjectionC n w := by
  have hf : Function.Injective
      (fun y : A × WeightBasisB n w => ((y.1, y.2.val), y.2)) := by
    intro y z h
    exact Prod.ext (congrArg (fun t : ((A × Finset (Fin n)) × WeightBasisB n w) =>
      t.1.1) h) (congrArg (fun t : ((A × Finset (Fin n)) × WeightBasisB n w) =>
      t.2) h)
  simp only [typeCopyMemoryC, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc (basisEmbeddingC _)ᴴ,
    basisEmbeddingC_complete _ hf, Matrix.one_mul,
    Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one, ← Matrix.mul_kronecker_mul,
    Matrix.one_mul, typeInclusionC_projection]

theorem typeCopyMemoryC_complete :
    (∑ w : Fin (n + 1), (typeCopyMemoryC n w.val A)ᴴ *
      typeCopyMemoryC n w.val A) = 1 := by
  simp only [typeCopyMemoryC_gram]
  have hp := (weightProjectionC_family n).complete
  calc
    _ = (1 : Matrix A A ℂ) ⊗ₖ (∑ w : Fin (n + 1), weightProjectionC n w.val) := by
      ext x y
      simp [Matrix.sum_apply, Matrix.kronecker_apply, Finset.mul_sum]
    _ = 1 := by rw [hp, Matrix.one_kronecker_one]

def typeCopyLabC : Matrix (((A × Finset (Fin n)) × WeightBasisB n w) × B)
    ((A × Finset (Fin n)) × B) ℂ :=
  typeCopyMemoryC n w A ⊗ₖ (1 : Matrix B B ℂ)

theorem typeCopyLabC_sepPositive
    {ρ : Matrix ((A × Finset (Fin n)) × B) ((A × Finset (Fin n)) × B) ℂ}
    (hρ : SepPositive ρ) :
    SepPositive (typeCopyLabC n w A B * ρ * (typeCopyLabC n w A B)ᴴ) :=
  hρ.local_conjugation (typeCopyMemoryC n w A) 1

def recordWeightMemoryC : Matrix (A × Finset (Fin n)) (A × Finset (Fin n)) ℂ :=
  (1 : Matrix A A ℂ) ⊗ₖ weightProjectionC n w

def recordWeightInstrumentC : KrausInstrument (Fintype.card (A × Finset (Fin n)))
    (Fintype.card (A × Finset (Fin n))) (n + 1) :=
  krausInstrumentOfEquivsB (finiteIndexB _) (finiteIndexB _) (Equiv.refl _)
    (fun w : Fin (n + 1) => recordWeightMemoryC n w.val A) (by
      have hw (w : Fin (n + 1)) : (weightProjectionC n w.val)ᴴ =
          weightProjectionC n w.val := ((weightProjectionC_family n).selfAdjoint w).eq
      simp only [recordWeightMemoryC, Matrix.conjTranspose_kronecker,
        Matrix.conjTranspose_one, ← Matrix.mul_kronecker_mul, Matrix.one_mul,
        hw,
        (weightProjectionC_family n).idempotent]
      calc
        _ = (1 : Matrix A A ℂ) ⊗ₖ
            (∑ w : Fin (n + 1), weightProjectionC n w.val) := by
          ext x y
          simp [Matrix.sum_apply, Matrix.kronecker_apply, Finset.mul_sum]
        _ = 1 := by rw [(weightProjectionC_family n).complete, Matrix.one_kronecker_one])

end OldMemories

section RecordedTransfer

variable (n w : ℕ) (A B : Type*) [Fintype A] [Fintype B]
  [DecidableEq A] [DecidableEq B]

def typePortEmbeddingC :
    Matrix ((A × Finset (Fin n)) × Finset (Fin n))
      ((A × Finset (Fin n)) × WeightBasisB n w) ℂ :=
  (1 : Matrix (A × Finset (Fin n)) (A × Finset (Fin n)) ℂ) ⊗ₖ typeInclusionC n w

def recordWeightBeforeC :
    Matrix ((A × Finset (Fin n)) × Finset (Fin n))
      ((A × Finset (Fin n)) × Finset (Fin n)) ℂ :=
  recordWeightMemoryC n w A ⊗ₖ (1 : Matrix (Finset (Fin n)) (Finset (Fin n)) ℂ)

theorem recordWeightBeforeC_diagonal : recordWeightBeforeC n w A =
    Matrix.diagonal (fun x => if x.1.2.card = w then (1 : ℂ) else 0) := by
  unfold recordWeightBeforeC recordWeightMemoryC weightProjectionC
  rw [← Matrix.diagonal_one (n := A), ← Matrix.diagonal_one (n := Finset (Fin n)),
    Matrix.diagonal_kronecker_diagonal, Matrix.diagonal_kronecker_diagonal]
  congr 1
  funext x
  simp

theorem recordWeightBeforeC_copy :
    recordWeightBeforeC n w A * recordCopyMemoryC n A =
      typePortEmbeddingC n w A * typeCopyMemoryC n w A := by
  let E := (1 : Matrix A A ℂ) ⊗ₖ typeInclusionC n w
  let F := basisEmbeddingC
    (fun y : A × WeightBasisB n w => ((y.1, y.2.val), y.2))
  have hfactor : typePortEmbeddingC n w A * F = recordCopyMemoryC n A * E := by
    simp only [typePortEmbeddingC, F, E, typeInclusionC,
      ← basisEmbeddingC_id, basisEmbeddingC_kronecker, basisEmbeddingC_compose,
      recordCopyMemoryC]
    rfl
  have hEE : E * Eᴴ = (1 : Matrix A A ℂ) ⊗ₖ weightProjectionC n w := by
    simp only [E, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
      ← Matrix.mul_kronecker_mul, Matrix.one_mul, typeInclusionC_projection]
  have hdiag : (1 : Matrix A A ℂ) ⊗ₖ weightProjectionC n w =
      Matrix.diagonal (fun x : A × Finset (Fin n) =>
        if x.2.card = w then (1 : ℂ) else 0) := by
    rw [← Matrix.diagonal_one (n := A), weightProjectionC,
      Matrix.diagonal_kronecker_diagonal]
    congr 1
    funext x
    simp
  calc
    _ = recordCopyMemoryC n A * ((1 : Matrix A A ℂ) ⊗ₖ weightProjectionC n w) := by
      rw [recordWeightBeforeC_diagonal, hdiag, recordCopyMemoryC,
        diagonal_basisEmbeddingC]
      rfl
    _ = (recordCopyMemoryC n A * E) * Eᴴ := by rw [Matrix.mul_assoc, hEE]
    _ = _ := by rw [← hfactor, Matrix.mul_assoc]; rfl

end RecordedTransfer

section LabMaps

variable {I O J Z A B : Type*} [Fintype I] [Fintype O] [Fintype J] [Fintype Z]
  [Fintype A] [Fintype B] [DecidableEq I] [DecidableEq O] [DecidableEq J]
  [DecidableEq A] [DecidableEq B]

def transferLabKrausC (K : Z → Matrix O I ℂ) (z : Z) :
    Matrix (A × (O × B)) ((A × I) × B) ℂ :=
  (referenceKrausB K (A × B) z).submatrix
    (outputPortMemoryEquivB O A B) (inputPortMemoryEquivB I A B)

theorem transferLabKrausC_entry (K : Z → Matrix O I ℂ) (z : Z)
    (x : A × (O × B)) (y : (A × I) × B) :
    transferLabKrausC K z x y = K z x.2.1 y.1.2 *
      (if x.1 = y.1.1 ∧ x.2.2 = y.2 then 1 else 0) := by
  simp [transferLabKrausC, referenceKrausB, Matrix.submatrix_apply,
    outputPortMemoryEquivB, inputPortMemoryEquivB, Matrix.kronecker_apply,
    Matrix.one_apply]

theorem labTransferOutput_eq_transferLabC (K : Z → Matrix O I ℂ)
    (ρ : Matrix ((A × I) × B) ((A × I) × B) ℂ) :
    labTransferOutput K ρ = (krausSumB (transferLabKrausC K) ρ).submatrix
      ((finiteIndexB A).prodCongr (finiteIndexB (O × B)))
      ((finiteIndexB A).prodCongr (finiteIndexB (O × B))) := by
  have hK : labTransferKraus (A := A) (B := B) K =
      fun z => (transferLabKrausC (A := A) (B := B) K z).submatrix
        ((finiteIndexB A).prodCongr (finiteIndexB (O × B))) id := rfl
  rw [labTransferOutput, hK]
  exact krausSumB_submatrix_equiv (Equiv.refl _) _ (Equiv.refl Z) _ ρ

theorem transferLabKrausC_port_precompose (K : Z → Matrix O I ℂ)
    (D : Matrix I J ℂ) (z : Z) :
    transferLabKrausC (A := A) (B := B) K z *
        (((1 : Matrix A A ℂ) ⊗ₖ D) ⊗ₖ (1 : Matrix B B ℂ)) =
      transferLabKrausC (A := A) (B := B) (fun t => K t * D) z := by
  ext ⟨a, o, b⟩ ⟨⟨c, j⟩, d⟩
  simp [Matrix.mul_apply, Fintype.sum_prod_type, transferLabKrausC_entry,
    Matrix.kronecker_apply, Matrix.one_apply, ite_and, mul_ite, ite_mul,
    Finset.mul_sum, Finset.sum_mul]

theorem transferLabKrausC_memory (K : Z → Matrix O I ℂ)
    (D : Matrix A A ℂ) (z : Z) :
    (D ⊗ₖ (1 : Matrix (O × B) (O × B) ℂ)) *
        transferLabKrausC (A := A) (B := B) K z =
      transferLabKrausC (A := A) (B := B) K z *
        ((D ⊗ₖ (1 : Matrix I I ℂ)) ⊗ₖ (1 : Matrix B B ℂ)) := by
  ext ⟨a, o, b⟩ ⟨⟨c, i⟩, d⟩
  simp [Matrix.mul_apply, Fintype.sum_prod_type, transferLabKrausC_entry,
    Matrix.kronecker_apply, Matrix.one_apply, ite_and, mul_ite, ite_mul,
    mul_comm]

end LabMaps

theorem krausSumB_rectangular_postcomposeC {I J O Z : Type*}
    [Fintype I] [Fintype J] [Fintype O] [Fintype Z]
    [DecidableEq I] [DecidableEq J] [DecidableEq O]
    (K : Z → Matrix J I ℂ) (D : Matrix O J ℂ) (ρ : Matrix I I ℂ) :
    krausSumB (fun z => D * K z) ρ = D * krausSumB K ρ * Dᴴ := by
  simp only [krausSumB, Matrix.conjTranspose_mul, Matrix.mul_sum, Matrix.sum_mul,
    Matrix.mul_assoc]

section PhysicalRecords

variable (n w : ℕ) (p : ℝ) (A B : Type*) [Fintype A] [Fintype B]
  [DecidableEq A] [DecidableEq B]

def recordCopyLabC : Matrix (((A × Finset (Fin n)) × Finset (Fin n)) × B)
    ((A × Finset (Fin n)) × B) ℂ :=
  recordCopyMemoryC n A ⊗ₖ (1 : Matrix B B ℂ)

def recordWeightOutputC :
    Matrix ((A × Finset (Fin n)) × (Finset (Fin n) × B))
      ((A × Finset (Fin n)) × (Finset (Fin n) × B)) ℂ :=
  recordWeightMemoryC n w A ⊗ₖ
    (1 : Matrix (Finset (Fin n) × B) (Finset (Fin n) × B) ℂ)

def recordedPhysicalKrausC (L : Finset (Fin n)) :
    Matrix ((A × Finset (Fin n)) × (Finset (Fin n) × B))
      ((A × Finset (Fin n)) × B) ℂ :=
  transferLabKrausC (A := A × Finset (Fin n)) (B := B)
    (tensorDampingKrausB n p) L * recordCopyLabC n A B

theorem tensorDampingKrausB_typeInclusionC (L : Finset (Fin n)) :
    tensorDampingKrausB n p L * typeInclusionC n w =
      tensorDampingSectorKrausB n w p L := by
  ext T S
  exact basisEmbeddingC_mul_entry Subtype.val (tensorDampingKrausB n p L) T S

theorem recordWeightOutputC_physical (L : Finset (Fin n)) :
    recordWeightOutputC n w A B * recordedPhysicalKrausC n p A B L =
      transferLabKrausC (A := A × Finset (Fin n)) (B := B)
        (tensorDampingSectorKrausB n w p) L * typeCopyLabC n w A B := by
  have hpre :
      ((recordWeightMemoryC n w A ⊗ₖ
        (1 : Matrix (Finset (Fin n)) (Finset (Fin n)) ℂ)) ⊗ₖ
          (1 : Matrix B B ℂ)) * recordCopyLabC n A B =
      (typePortEmbeddingC n w A ⊗ₖ (1 : Matrix B B ℂ)) * typeCopyLabC n w A B := by
    simp only [recordCopyLabC, typeCopyLabC, ← Matrix.mul_kronecker_mul, Matrix.one_mul]
    change (recordWeightBeforeC n w A * recordCopyMemoryC n A) ⊗ₖ
        (1 : Matrix B B ℂ) =
      (typePortEmbeddingC n w A * typeCopyMemoryC n w A) ⊗ₖ (1 : Matrix B B ℂ)
    rw [recordWeightBeforeC_copy]
  have hfamily : (fun L => tensorDampingKrausB n p L * typeInclusionC n w) =
      tensorDampingSectorKrausB n w p := by
    funext L
    exact tensorDampingKrausB_typeInclusionC n w p L
  unfold recordWeightOutputC recordedPhysicalKrausC
  have hmem := transferLabKrausC_memory (A := A × Finset (Fin n)) (B := B)
    (tensorDampingKrausB n p) (recordWeightMemoryC n w A) L
  calc
    _ = (transferLabKrausC (A := A × Finset (Fin n)) (B := B)
        (tensorDampingKrausB n p) L *
          ((recordWeightMemoryC n w A ⊗ₖ
            (1 : Matrix (Finset (Fin n)) (Finset (Fin n)) ℂ)) ⊗ₖ
              (1 : Matrix B B ℂ))) * recordCopyLabC n A B := by
      rw [← Matrix.mul_assoc]
      exact congrArg (fun M => M * recordCopyLabC n A B) hmem
    _ = transferLabKrausC (A := A × Finset (Fin n)) (B := B)
        (tensorDampingKrausB n p) L *
          ((typePortEmbeddingC n w A ⊗ₖ (1 : Matrix B B ℂ)) *
            typeCopyLabC n w A B) := by
      rw [Matrix.mul_assoc, hpre]
    _ = _ := by
      rw [← Matrix.mul_assoc]
      change (transferLabKrausC (A := A × Finset (Fin n)) (B := B)
          (tensorDampingKrausB n p) L *
            (((1 : Matrix (A × Finset (Fin n)) (A × Finset (Fin n)) ℂ) ⊗ₖ
              typeInclusionC n w) ⊗ₖ (1 : Matrix B B ℂ))) * typeCopyLabC n w A B = _
      rw [transferLabKrausC_port_precompose, hfamily]

def recordedOutputC (ρ : Matrix ((A × Finset (Fin n)) × B)
    ((A × Finset (Fin n)) × B) ℂ) :
    Matrix ((A × Finset (Fin n)) × (Finset (Fin n) × B))
      ((A × Finset (Fin n)) × (Finset (Fin n) × B)) ℂ :=
  krausSumB (recordedPhysicalKrausC n p A B) ρ

def pinchedRecordedOutputC (ρ : Matrix ((A × Finset (Fin n)) × B)
    ((A × Finset (Fin n)) × B) ℂ) :
    Matrix ((A × Finset (Fin n)) × (Finset (Fin n) × B))
      ((A × Finset (Fin n)) × (Finset (Fin n) × B)) ℂ :=
  krausSumB (fun w : Fin (n + 1) => recordWeightOutputC n w.val A B)
    (recordedOutputC n p A B ρ)

theorem pinchedRecordedOutputC_eq_sectors
    (ρ : Matrix ((A × Finset (Fin n)) × B) ((A × Finset (Fin n)) × B) ℂ) :
    pinchedRecordedOutputC n p A B ρ =
      ∑ w : Fin (n + 1), krausSumB
        (transferLabKrausC (A := A × Finset (Fin n)) (B := B)
          (tensorDampingSectorKrausB n w.val p))
        (typeCopyLabC n w.val A B * ρ * (typeCopyLabC n w.val A B)ᴴ) := by
  unfold pinchedRecordedOutputC recordedOutputC
  change (∑ w : Fin (n + 1), recordWeightOutputC n w.val A B *
      krausSumB (recordedPhysicalKrausC n p A B) ρ *
        (recordWeightOutputC n w.val A B)ᴴ) = _
  apply Finset.sum_congr rfl
  intro w _
  rw [← krausSumB_rectangular_postcomposeC]
  have hfamily : (fun L => recordWeightOutputC n w.val A B *
      recordedPhysicalKrausC n p A B L) =
      fun L => transferLabKrausC (A := A × Finset (Fin n)) (B := B)
        (tensorDampingSectorKrausB n w.val p) L * typeCopyLabC n w.val A B := by
    funext L
    exact recordWeightOutputC_physical n w.val p A B L
  rw [hfamily, krausSumB_rectangular_precompose]

end PhysicalRecords

section SectorSums

variable {I O Z A B : Type*} [Fintype I] [Fintype O] [Fintype Z]
  [Fintype A] [Fintype B] [DecidableEq I] [DecidableEq O]
  [DecidableEq A] [DecidableEq B]

theorem transferLabOutputC_eq_reference (K : Z → Matrix O I ℂ)
    (ρ : Matrix ((A × I) × B) ((A × I) × B) ℂ) :
    krausSumB (transferLabKrausC (A := A) (B := B) K) ρ =
      (krausSumB (referenceKrausB K (A × B))
        (ρ.submatrix (inputPortMemoryEquivB I A B).symm
          (inputPortMemoryEquivB I A B).symm)).submatrix
        (outputPortMemoryEquivB O A B) (outputPortMemoryEquivB O A B) := by
  unfold transferLabKrausC
  simpa only [Equiv.refl_apply, Matrix.submatrix_submatrix,
    Equiv.symm_comp_self, Matrix.submatrix_id_id] using
    krausSumB_submatrix_equiv (inputPortMemoryEquivB I A B)
      (outputPortMemoryEquivB O A B) (Equiv.refl Z) (referenceKrausB K (A × B))
      (ρ.submatrix (inputPortMemoryEquivB I A B).symm
        (inputPortMemoryEquivB I A B).symm)

theorem transferLabSectorC_survivor_sum (n w : ℕ) (p : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (ρ : Matrix ((A × WeightBasisB n w) × B) ((A × WeightBasisB n w) × B) ℂ) :
    krausSumB (transferLabKrausC (A := A) (B := B)
      (tensorDampingSectorKrausB n w p)) ρ =
      ∑ r ∈ Finset.range (w + 1), physicalSurvivorProbabilityB p w r •
        krausSumB (transferLabKrausC (A := A) (B := B) (lossKrausB n w r)) ρ := by
  rw [transferLabOutputC_eq_reference, tensorDampingSectorChannelB_reference_eq n w p hp0 hp1]
  ext x y
  simp only [transferLabOutputC_eq_reference, Matrix.submatrix_apply,
    Matrix.sum_apply, Matrix.smul_apply]

theorem pinchedRecordedOutputC_survivor_sum (n : ℕ) (p : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (ρ : Matrix ((A × Finset (Fin n)) × B) ((A × Finset (Fin n)) × B) ℂ) :
    pinchedRecordedOutputC n p A B ρ =
      ∑ w : Fin (n + 1), ∑ r ∈ Finset.range (w.val + 1),
        physicalSurvivorProbabilityB p w.val r •
          krausSumB (transferLabKrausC (A := A × Finset (Fin n)) (B := B)
            (lossKrausB n w.val r))
            (typeCopyLabC n w.val A B * ρ * (typeCopyLabC n w.val A B)ᴴ) := by
  rw [pinchedRecordedOutputC_eq_sectors]
  apply Finset.sum_congr rfl
  intro w _
  exact transferLabSectorC_survivor_sum n w.val p hp0 hp1 _

end SectorSums

section CompletePhaseComparator

variable {I O Z A B : Type*} [Fintype I] [Fintype O] [Fintype Z]
  [Fintype A] [Fintype B] [DecidableEq I] [DecidableEq O]
  [DecidableEq A] [DecidableEq B]

theorem transferLabKrausC_complete (K : Z → Matrix O I ℂ)
    (hK : ∑ z, (K z)ᴴ * K z = 1) :
    ∑ z, (transferLabKrausC (A := A) (B := B) K z)ᴴ *
      transferLabKrausC (A := A) (B := B) K z = 1 := by
  apply krausSumB_complete_of_trace
  intro ρ
  rw [transferLabOutputC_eq_reference, TensorPower.trace_submatrix_equiv,
    krausSumB_trace_preserving _ (referenceKrausB_complete K hK (A × B)),
    TensorPower.trace_submatrix_equiv]

theorem transferLabKrausC_rankOne (χ : Z → I → ℂ) (v : Z → O → ℂ) (z : Z) :
    transferLabKrausC (A := A) (B := B)
        (fun j => QuantumProver.AmplitudeDamping.SecretKey.KrausAlgebra.rankOneKraus (χ j) (v j)) z =
      measurePrepareTransferKraus (A := A) (B := B) χ v z :=
  (measurePrepareTransferKraus_eq_reference χ v z).symm

theorem transferLabPhysicalPhaseC_sepPositive (n w : ℕ) (p : ℝ)
    {σ : Matrix ((A × WeightBasisB n w) × B) ((A × WeightBasisB n w) × B) ℂ}
    (hσ : SepPositive σ) :
    SepPositive (krausSumB (transferLabKrausC (A := A) (B := B)
      (physicalPhaseKrausB n w p)) σ) := by
  have hfamily : transferLabKrausC (A := A) (B := B) (physicalPhaseKrausB n w p) =
      measurePrepareTransferKraus (A := A) (B := B)
        (weightedPhaseInputVectorB n w (physicalPhaseLawB p w))
        (weightedPhaseOutputVectorB n w) := by
    funext z
    exact transferLabKrausC_rankOne _ _ z
  rw [hfamily]
  exact hσ.measurePrepareTransfer _ _

theorem transferLabPhysicalPhaseC_survivor_sum (n w : ℕ) (p : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (σ : Matrix ((A × WeightBasisB n w) × B) ((A × WeightBasisB n w) × B) ℂ) :
    krausSumB (transferLabKrausC (A := A) (B := B) (physicalPhaseKrausB n w p)) σ =
      ∑ r : Fin (w + 1), physicalPhaseLawB p w r •
        krausSumB (transferLabKrausC (A := A) (B := B)
          (measurePhaseKrausB n w r.val)) σ := by
  rw [transferLabOutputC_eq_reference, physicalPhaseChannelB_reference_eq n w p hp0 hp1]
  ext x y
  simp only [transferLabOutputC_eq_reference, Matrix.submatrix_apply,
    Matrix.sum_apply, Matrix.smul_apply]

end CompletePhaseComparator

section RecordedPhaseChannel

variable (n : ℕ) (p : ℝ) (A B : Type*) [Fintype A] [Fintype B]
  [DecidableEq A] [DecidableEq B]

theorem typeCopyLabC_complete :
    (∑ w : Fin (n + 1), (typeCopyLabC n w.val A B)ᴴ * typeCopyLabC n w.val A B) = 1 := by
  simp only [typeCopyLabC, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
    ← Matrix.mul_kronecker_mul, Matrix.one_mul]
  calc
    _ = (∑ w : Fin (n + 1), (typeCopyMemoryC n w.val A)ᴴ *
        typeCopyMemoryC n w.val A) ⊗ₖ (1 : Matrix B B ℂ) := by
      ext x y
      simp [Matrix.sum_apply, Finset.sum_mul]
    _ = 1 := by rw [typeCopyMemoryC_complete, Matrix.one_kronecker_one]

def phaseRecordedKrausC : (Σ w : Fin (n + 1), survivorPhaseLabelB n w.val) →
    Matrix ((A × Finset (Fin n)) × (Finset (Fin n) × B))
      ((A × Finset (Fin n)) × B) ℂ :=
  fun z => transferLabKrausC (A := A × Finset (Fin n)) (B := B)
      (physicalPhaseKrausB n z.1.val p) z.2 * typeCopyLabC n z.1.val A B

theorem phaseRecordedKrausC_complete (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ∑ z, (phaseRecordedKrausC n p A B z)ᴴ * phaseRecordedKrausC n p A B z = 1 := by
  simp only [phaseRecordedKrausC, Fintype.sum_sigma, Matrix.conjTranspose_mul]
  calc
    _ = ∑ w : Fin (n + 1), (typeCopyLabC n w.val A B)ᴴ *
        (∑ j : survivorPhaseLabelB n w.val,
          (transferLabKrausC (A := A × Finset (Fin n)) (B := B)
            (physicalPhaseKrausB n w.val p) j)ᴴ *
          transferLabKrausC (A := A × Finset (Fin n)) (B := B)
            (physicalPhaseKrausB n w.val p) j) * typeCopyLabC n w.val A B := by
      apply Finset.sum_congr rfl
      intro w _
      simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_assoc]
    _ = 1 := by
      simp only [transferLabKrausC_complete _
        (physicalPhaseKrausB_complete n _ (Nat.le_of_lt_succ (Fin.isLt _)) p hp0 hp1),
        Matrix.mul_one]
      exact typeCopyLabC_complete n A B

def phaseRecordedOutputC (σ : Matrix ((A × Finset (Fin n)) × B)
    ((A × Finset (Fin n)) × B) ℂ) :
    Matrix ((A × Finset (Fin n)) × (Finset (Fin n) × B))
      ((A × Finset (Fin n)) × (Finset (Fin n) × B)) ℂ :=
  krausSumB (phaseRecordedKrausC n p A B) σ

theorem phaseRecordedOutputC_eq_sectors
    (σ : Matrix ((A × Finset (Fin n)) × B) ((A × Finset (Fin n)) × B) ℂ) :
    phaseRecordedOutputC n p A B σ = ∑ w : Fin (n + 1),
      krausSumB (transferLabKrausC (A := A × Finset (Fin n)) (B := B)
        (physicalPhaseKrausB n w.val p))
        (typeCopyLabC n w.val A B * σ * (typeCopyLabC n w.val A B)ᴴ) := by
  unfold phaseRecordedOutputC
  simp only [krausSumB, phaseRecordedKrausC, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro w _
  change krausSumB (fun j => transferLabKrausC (A := A × Finset (Fin n)) (B := B)
        (physicalPhaseKrausB n w.val p) j * typeCopyLabC n w.val A B) σ =
      krausSumB (transferLabKrausC (A := A × Finset (Fin n)) (B := B)
        (physicalPhaseKrausB n w.val p))
        (typeCopyLabC n w.val A B * σ * (typeCopyLabC n w.val A B)ᴴ)
  exact krausSumB_rectangular_precompose _ _ σ

theorem phaseRecordedOutputC_survivor_sum (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (σ : Matrix ((A × Finset (Fin n)) × B) ((A × Finset (Fin n)) × B) ℂ) :
    phaseRecordedOutputC n p A B σ = ∑ w : Fin (n + 1),
      ∑ r : Fin (w.val + 1), physicalPhaseLawB p w.val r •
        krausSumB (transferLabKrausC (A := A × Finset (Fin n)) (B := B)
          (measurePhaseKrausB n w.val r.val))
          (typeCopyLabC n w.val A B * σ * (typeCopyLabC n w.val A B)ᴴ) := by
  rw [phaseRecordedOutputC_eq_sectors]
  apply Finset.sum_congr rfl
  intro w _
  exact transferLabPhysicalPhaseC_survivor_sum n w.val p hp0 hp1 _

theorem phaseRecordedOutputC_trace (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (σ : Matrix ((A × Finset (Fin n)) × B) ((A × Finset (Fin n)) × B) ℂ) :
    (phaseRecordedOutputC n p A B σ).trace = σ.trace :=
  krausSumB_trace_preserving _ (phaseRecordedKrausC_complete n p A B hp0 hp1) σ

theorem phaseRecordedOutputC_posSemidef
    {σ : Matrix ((A × Finset (Fin n)) × B) ((A × Finset (Fin n)) × B) ℂ}
    (hσ : σ.PosSemidef) : (phaseRecordedOutputC n p A B σ).PosSemidef :=
  krausSumB_posSemidef _ hσ

theorem phaseRecordedOutputC_sepPositive
    {σ : Matrix ((A × Finset (Fin n)) × B) ((A × Finset (Fin n)) × B) ℂ}
    (hσ : SepPositive σ) : SepPositive (phaseRecordedOutputC n p A B σ) := by
  rw [phaseRecordedOutputC_eq_sectors]
  apply SepPositive.sum
  intro w
  exact transferLabPhysicalPhaseC_sepPositive n w.val p
    (typeCopyLabC_sepPositive n w.val A B hσ)

theorem phaseRecordedOutputC_isSeparable (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {σ : Matrix ((A × Finset (Fin n)) × B) ((A × Finset (Fin n)) × B) ℂ}
    (hσ : SepPositive σ) (htrace : σ.trace = 1) :
    IsSeparable (Fintype.card (A × Finset (Fin n))) (Fintype.card (Finset (Fin n) × B))
      ((phaseRecordedOutputC n p A B σ).submatrix
        ((finiteIndexB (A × Finset (Fin n))).prodCongr (finiteIndexB (Finset (Fin n) × B)))
        ((finiteIndexB (A × Finset (Fin n))).prodCongr (finiteIndexB (Finset (Fin n) × B)))) := by
  apply ((phaseRecordedOutputC_sepPositive n p A B hσ).submatrix_local_equiv
    (finiteIndexB (A × Finset (Fin n))) (finiteIndexB (Finset (Fin n) × B))).isSeparable
  rw [TensorPower.trace_submatrix_equiv, phaseRecordedOutputC_trace n p A B hp0 hp1, htrace]

end RecordedPhaseChannel

section UniformSurvivorFlags

theorem physicalSurvivorProbabilityB_zeroC (p : ℝ) (w r : ℕ) (hwr : w < r) :
    physicalSurvivorProbabilityB p w r = 0 := by
  simp [physicalSurvivorProbabilityB, Nat.choose_eq_zero_of_lt hwr]

def recordedFlagLawC (n : ℕ) (p : ℝ) (z : Fin (n + 1) × Fin (n + 1)) : ℝ :=
  if z.2.val ≤ z.1.val then physicalSurvivorProbabilityB p z.1.val z.2.val else 0

theorem recordedFlagLawC_eq_physical (n : ℕ) (p : ℝ) (z : Fin (n + 1) × Fin (n + 1)) :
    recordedFlagLawC n p z = physicalSurvivorProbabilityB p z.1.val z.2.val := by
  by_cases h : z.2.val ≤ z.1.val
  · simp [recordedFlagLawC, h]
  · rw [recordedFlagLawC, if_neg h, physicalSurvivorProbabilityB_zeroC p _ _ (by omega)]

theorem physicalSurvivorProbabilityB_sum_rangeC {M : Type*} [AddCommMonoid M] [Module ℝ M]
    (n w : ℕ) (hwn : w ≤ n) (p : ℝ) (F : ℕ → M) :
    (∑ r ∈ Finset.range (n + 1), physicalSurvivorProbabilityB p w r • F r) =
      ∑ r ∈ Finset.range (w + 1), physicalSurvivorProbabilityB p w r • F r := by
  symm
  apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ hwn))
  intro r _ hr
  have hwr : w < r := by
    have h : ¬ r < w + 1 := by simpa only [Finset.mem_range] using hr
    omega
  rw [physicalSurvivorProbabilityB_zeroC p w r hwr, zero_smul]

variable (n w r : ℕ) (A B : Type*) [Fintype A] [Fintype B]
  [DecidableEq A] [DecidableEq B]

def recordedLossBranchC
    (ρ : Matrix ((A × Finset (Fin n)) × B) ((A × Finset (Fin n)) × B) ℂ) :
    Matrix ((A × Finset (Fin n)) × (Finset (Fin n) × B))
      ((A × Finset (Fin n)) × (Finset (Fin n) × B)) ℂ :=
  krausSumB (transferLabKrausC (A := A × Finset (Fin n)) (B := B) (lossKrausB n w r))
    (typeCopyLabC n w A B * ρ * (typeCopyLabC n w A B)ᴴ)

def recordedPhaseBranchC
    (σ : Matrix ((A × Finset (Fin n)) × B) ((A × Finset (Fin n)) × B) ℂ) :
    Matrix ((A × Finset (Fin n)) × (Finset (Fin n) × B))
      ((A × Finset (Fin n)) × (Finset (Fin n) × B)) ℂ :=
  krausSumB (transferLabKrausC (A := A × Finset (Fin n)) (B := B)
    (measurePhaseKrausB n w r))
    (typeCopyLabC n w A B * σ * (typeCopyLabC n w A B)ᴴ)

theorem pinchedRecordedOutputC_uniform_sum (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (ρ : Matrix ((A × Finset (Fin n)) × B) ((A × Finset (Fin n)) × B) ℂ) :
    pinchedRecordedOutputC n p A B ρ = ∑ w : Fin (n + 1), ∑ r : Fin (n + 1),
      physicalSurvivorProbabilityB p w.val r.val • recordedLossBranchC n w.val r.val A B ρ := by
  rw [pinchedRecordedOutputC_survivor_sum n p hp0 hp1]
  apply Finset.sum_congr rfl
  intro w _
  rw [Fin.sum_univ_eq_sum_range (fun r : ℕ =>
      physicalSurvivorProbabilityB p w.val r • recordedLossBranchC n w.val r A B ρ) (n + 1),
    physicalSurvivorProbabilityB_sum_rangeC n w.val (Nat.le_of_lt_succ w.isLt)]
  rfl

theorem phaseRecordedOutputC_uniform_sum (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (σ : Matrix ((A × Finset (Fin n)) × B) ((A × Finset (Fin n)) × B) ℂ) :
    phaseRecordedOutputC n p A B σ = ∑ w : Fin (n + 1), ∑ r : Fin (n + 1),
      physicalSurvivorProbabilityB p w.val r.val • recordedPhaseBranchC n w.val r.val A B σ := by
  rw [phaseRecordedOutputC_survivor_sum n p A B hp0 hp1]
  apply Finset.sum_congr rfl
  intro w _
  change (∑ r : Fin (w.val + 1), physicalSurvivorProbabilityB p w.val r.val •
      recordedPhaseBranchC n w.val r.val A B σ) = _
  rw [Fin.sum_univ_eq_sum_range (fun r : ℕ =>
      physicalSurvivorProbabilityB p w.val r • recordedPhaseBranchC n w.val r A B σ) (w.val + 1),
    Fin.sum_univ_eq_sum_range (fun r : ℕ =>
      physicalSurvivorProbabilityB p w.val r • recordedPhaseBranchC n w.val r A B σ) (n + 1),
    physicalSurvivorProbabilityB_sum_rangeC n w.val (Nat.le_of_lt_succ w.isLt)]

end UniformSurvivorFlags

section ActualFlagErasure

theorem appendFlagKraus_crossC {f a : ℕ} (w v : Fin f) :
    (appendFlagKraus (a := a) w)ᴴ * appendFlagKraus (a := a) v =
      if w = v then (1 : Matrix (Fin a) (Fin a) ℂ) else 0 := by
  classical
  by_cases hwv : w = v
  · subst v
    rw [appendFlagKraus_complete, if_pos rfl]
  · ext i j
    let e : Fin (f * a) ≃ Fin f × Fin a := finProdFinEquiv.symm
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, appendFlagKraus]
    rw [e.sum_comp (fun x => star (if x.1 = w ∧ x.2 = i then (1 : ℂ) else 0) *
      (if x.1 = v ∧ x.2 = j then (1 : ℂ) else 0))]
    simp [Fintype.sum_prod_type, hwv, Ne.symm hwv, ite_and, mul_ite, ite_mul]

theorem eraseFlagKrausC_complete (f a : ℕ) :
    ∑ w : Fin f, appendFlagKraus (a := a) w * (appendFlagKraus (a := a) w)ᴴ = 1 := by
  classical
  let e : Fin (f * a) ≃ Fin f × Fin a := finProdFinEquiv.symm
  ext x y
  simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, appendFlagKraus]
  by_cases hf : (e x).1 = (e y).1
  · by_cases hi : (e x).2 = (e y).2
    · have hxy : x = y := e.injective (Prod.ext hf hi)
      subst y
      simp [e, Matrix.one_apply, ite_and, mul_ite, ite_mul]
    · have hxy : x ≠ y := fun h => hi (congrArg (fun t => (e t).2) h)
      simp [e, Matrix.one_apply, hxy, hf, hi, Ne.symm hi, ite_and, mul_ite, ite_mul]
      intro hd hm
      exact hxy (e.injective (Prod.ext hd.symm hm.symm))
  · have hxy : x ≠ y := fun h => hf (congrArg (fun t => (e t).1) h)
    simp [e, Matrix.one_apply, hxy, hf, Ne.symm hf, ite_and, mul_ite, ite_mul]
    intro hd hm
    exact hxy (e.injective (Prod.ext hd.symm hm.symm))

def eraseFlagInstrumentC (f a : ℕ) : KrausInstrument (f * a) a f where
  operator w := (appendFlagKraus (a := a) w)ᴴ
  complete := by
    simpa only [Matrix.conjTranspose_conjTranspose] using eraseFlagKrausC_complete f a

def eraseLabFlagsProtocolC (p : ℝ) (f g a b : ℕ) :
    FiniteProtocol p (f * a) (g * b) a b :=
  .alice (eraseFlagInstrumentC f a) fun _ =>
    .bob (eraseFlagInstrumentC g b) fun _ => .done a b

theorem eraseLabFlagsProtocolC_calls (p : ℝ) (f g a b : ℕ) :
    (eraseLabFlagsProtocolC p f g a b).calls = 0 := by
  simp [eraseLabFlagsProtocolC, FiniteProtocol.calls]

theorem eraseLabFlagsProtocolC_output (p : ℝ) {f g a b : ℕ}
    (ρ : BipartiteMatrix (f * a) (g * b)) :
    (eraseLabFlagsProtocolC p f g a b).output ρ =
      krausSumB (fun z : Fin f × Fin g =>
        (appendFlagKraus (a := a) z.1)ᴴ ⊗ₖ (appendFlagKraus (a := b) z.2)ᴴ) ρ := by
  simp only [eraseLabFlagsProtocolC, FiniteProtocol.output, krausSumB,
    Fintype.sum_prod_type, eraseFlagInstrumentC]
  apply Finset.sum_congr rfl
  intro w _
  apply Finset.sum_congr rfl
  intro r _
  have hprod : bobOperator (a := a) (appendFlagKraus (a := b) r)ᴴ *
      aliceOperator (b := g * b) (appendFlagKraus (a := a) w)ᴴ =
        (appendFlagKraus (a := a) w)ᴴ ⊗ₖ (appendFlagKraus (a := b) r)ᴴ := by
    simp only [bobOperator, aliceOperator, ← Matrix.mul_kronecker_mul,
      Matrix.mul_one, Matrix.one_mul]
  calc
    _ = (bobOperator (a := a) (appendFlagKraus (a := b) r)ᴴ *
          aliceOperator (b := g * b) (appendFlagKraus (a := a) w)ᴴ) * ρ *
        (bobOperator (a := a) (appendFlagKraus (a := b) r)ᴴ *
          aliceOperator (b := g * b) (appendFlagKraus (a := a) w)ᴴ)ᴴ := by
      simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = _ := by rw [hprod]

theorem eraseLabFlagsProtocolC_labFlagBlock (p : ℝ) {f g a b : ℕ}
    (w : Fin f) (r : Fin g) (ρ : BipartiteMatrix a b) :
    (eraseLabFlagsProtocolC p f g a b).output (labFlagBlock w r ρ) = ρ := by
  rw [eraseLabFlagsProtocolC_output]
  unfold krausSumB labFlagBlock
  have hprod (z : Fin f × Fin g) :
      ((appendFlagKraus (a := a) z.1)ᴴ ⊗ₖ (appendFlagKraus (a := b) z.2)ᴴ) *
        (appendFlagKraus (a := a) w ⊗ₖ appendFlagKraus (a := b) r) =
      if z = (w, r) then (1 : BipartiteMatrix a b) else 0 := by
    rw [← Matrix.mul_kronecker_mul, appendFlagKraus_crossC, appendFlagKraus_crossC]
    by_cases hw : z.1 = w <;> by_cases hr : z.2 = r <;>
      simp [hw, hr, Prod.ext_iff, Matrix.one_kronecker_one]
  have hterm (z : Fin f × Fin g) :
      ((appendFlagKraus (a := a) z.1)ᴴ ⊗ₖ (appendFlagKraus (a := b) z.2)ᴴ) *
          ((appendFlagKraus (a := a) w ⊗ₖ appendFlagKraus (a := b) r) * ρ *
            (appendFlagKraus (a := a) w ⊗ₖ appendFlagKraus (a := b) r)ᴴ) *
        ((appendFlagKraus (a := a) z.1)ᴴ ⊗ₖ (appendFlagKraus (a := b) z.2)ᴴ)ᴴ =
      if z = (w, r) then ρ else 0 := by
    calc
      _ = (((appendFlagKraus (a := a) z.1)ᴴ ⊗ₖ (appendFlagKraus (a := b) z.2)ᴴ) *
          (appendFlagKraus (a := a) w ⊗ₖ appendFlagKraus (a := b) r)) * ρ *
        (((appendFlagKraus (a := a) z.1)ᴴ ⊗ₖ (appendFlagKraus (a := b) z.2)ᴴ) *
          (appendFlagKraus (a := a) w ⊗ₖ appendFlagKraus (a := b) r))ᴴ := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by
        rw [hprod]
        by_cases h : z = (w, r) <;> simp [h]
  simp_rw [hterm]
  simp

theorem eraseLabFlagsProtocolC_labFlagComparator (p : ℝ) {f g a b : ℕ}
    (t : Fin f × Fin g → ℝ) (ρ : Fin f × Fin g → BipartiteMatrix a b) :
    (eraseLabFlagsProtocolC p f g a b).output (labFlagComparator t ρ) =
      ∑ z, (t z : ℂ) • ρ z := by
  change (eraseLabFlagsProtocolC p f g a b).outputLinearMap
      (∑ z, (t z : ℂ) • labFlagBlock z.1 z.2 (ρ z)) = _
  rw [map_sum]
  simp only [map_smul]
  apply Finset.sum_congr rfl
  intro z _
  exact congrArg (fun M => (t z : ℂ) • M)
    (eraseLabFlagsProtocolC_labFlagBlock p z.1 z.2 (ρ z))

end ActualFlagErasure

section PhysicalFlagJoins

variable (n : ℕ) (p : ℝ) (A B : Type*) [Fintype A] [Fintype B]
  [DecidableEq A] [DecidableEq B]

def recordedOutputEquivC :
    (Fin (Fintype.card (A × Finset (Fin n))) × Fin (Fintype.card (Finset (Fin n) × B))) ≃
      ((A × Finset (Fin n)) × (Finset (Fin n) × B)) :=
  (finiteIndexB (A × Finset (Fin n))).prodCongr (finiteIndexB (Finset (Fin n) × B))

theorem recordedLossBranchC_fin_eq_labTransfer (w r : ℕ)
    (ρ : Matrix ((A × Finset (Fin n)) × B) ((A × Finset (Fin n)) × B) ℂ) :
    (recordedLossBranchC n w r A B ρ).submatrix (recordedOutputEquivC n A B)
        (recordedOutputEquivC n A B) =
      labTransferOutput (lossKrausB n w r)
        (typeCopyLabC n w A B * ρ * (typeCopyLabC n w A B)ᴴ) :=
  (labTransferOutput_eq_transferLabC _ _).symm

theorem recordedPhaseBranchC_fin_eq_labTransfer (w r : ℕ)
    (σ : Matrix ((A × Finset (Fin n)) × B) ((A × Finset (Fin n)) × B) ℂ) :
    (recordedPhaseBranchC n w r A B σ).submatrix (recordedOutputEquivC n A B)
        (recordedOutputEquivC n A B) =
      labTransferOutput (measurePhaseKrausB n w r)
        (typeCopyLabC n w A B * σ * (typeCopyLabC n w A B)ᴴ) :=
  (labTransferOutput_eq_transferLabC _ _).symm

def flaggedRecordedOutputC
    (ρ : Matrix ((A × Finset (Fin n)) × B) ((A × Finset (Fin n)) × B) ℂ) :
    BipartiteMatrix ((n + 1) * Fintype.card (A × Finset (Fin n)))
      ((n + 1) * Fintype.card (Finset (Fin n) × B)) :=
  labFlagComparator (recordedFlagLawC n p) (fun z =>
    (recordedLossBranchC n z.1.val z.2.val A B ρ).submatrix
      (recordedOutputEquivC n A B) (recordedOutputEquivC n A B))

def flaggedPhaseOutputC
    (σ : Matrix ((A × Finset (Fin n)) × B) ((A × Finset (Fin n)) × B) ℂ) :
    BipartiteMatrix ((n + 1) * Fintype.card (A × Finset (Fin n)))
      ((n + 1) * Fintype.card (Finset (Fin n) × B)) :=
  labFlagComparator (recordedFlagLawC n p) (fun z =>
    (recordedPhaseBranchC n z.1.val z.2.val A B σ).submatrix
      (recordedOutputEquivC n A B) (recordedOutputEquivC n A B))

theorem flaggedRecordedOutputC_erase (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (ρ : Matrix ((A × Finset (Fin n)) × B) ((A × Finset (Fin n)) × B) ℂ) :
    (eraseLabFlagsProtocolC p (n + 1) (n + 1)
      (Fintype.card (A × Finset (Fin n))) (Fintype.card (Finset (Fin n) × B))).output
        (flaggedRecordedOutputC n p A B ρ) =
      (pinchedRecordedOutputC n p A B ρ).submatrix
        (recordedOutputEquivC n A B) (recordedOutputEquivC n A B) := by
  rw [flaggedRecordedOutputC, eraseLabFlagsProtocolC_labFlagComparator,
    pinchedRecordedOutputC_uniform_sum n A B p hp0 hp1]
  ext x y
  simp only [Fintype.sum_prod_type, Matrix.sum_apply, Matrix.smul_apply,
    Matrix.submatrix_apply, Complex.coe_smul, recordedFlagLawC_eq_physical]

theorem flaggedPhaseOutputC_erase (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (σ : Matrix ((A × Finset (Fin n)) × B) ((A × Finset (Fin n)) × B) ℂ) :
    (eraseLabFlagsProtocolC p (n + 1) (n + 1)
      (Fintype.card (A × Finset (Fin n))) (Fintype.card (Finset (Fin n) × B))).output
        (flaggedPhaseOutputC n p A B σ) =
      (phaseRecordedOutputC n p A B σ).submatrix
        (recordedOutputEquivC n A B) (recordedOutputEquivC n A B) := by
  rw [flaggedPhaseOutputC, eraseLabFlagsProtocolC_labFlagComparator,
    phaseRecordedOutputC_uniform_sum n A B p hp0 hp1]
  ext x y
  simp only [Fintype.sum_prod_type, Matrix.sum_apply, Matrix.smul_apply,
    Matrix.submatrix_apply, Complex.coe_smul, recordedFlagLawC_eq_physical]

def recoveredPhaseOutputC
    (σ : Matrix ((A × Finset (Fin n)) × B) ((A × Finset (Fin n)) × B) ℂ) :
    BipartiteMatrix (Fintype.card A) (Fintype.card (Finset (Fin n) × B)) :=
  (fullRecordRecoveryProtocolB p n A B).output
    ((phaseRecordedOutputC n p A B σ).submatrix
      (recordedOutputEquivC n A B) (recordedOutputEquivC n A B))

theorem recoveredPhaseOutputC_trace (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (σ : Matrix ((A × Finset (Fin n)) × B) ((A × Finset (Fin n)) × B) ℂ) :
    (recoveredPhaseOutputC n p A B σ).trace = σ.trace := by
  rw [recoveredPhaseOutputC, FiniteProtocol.output_trace hp0 hp1,
    TensorPower.trace_submatrix_equiv, phaseRecordedOutputC_trace n p A B hp0 hp1]

theorem recoveredPhaseOutputC_isSeparable (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {σ : Matrix ((A × Finset (Fin n)) × B) ((A × Finset (Fin n)) × B) ℂ}
    (hσ : SepPositive σ) (htrace : σ.trace = 1) :
    IsSeparable (Fintype.card A) (Fintype.card (Finset (Fin n) × B))
      (recoveredPhaseOutputC n p A B σ) :=
  (fullRecordRecoveryProtocolB p n A B).output_isSeparable_of_calls_zero hp0 hp1
    (fullRecordRecoveryProtocolB_calls p n A B)
    (phaseRecordedOutputC_isSeparable n p A B hp0 hp1 hσ htrace)

end PhysicalFlagJoins

end QuantumProver.AmplitudeDamping.FiniteModel

import QuantumProver.InformationTheory.AmplitudeDamping.QuantumCapacity.ComparisonInequalities

set_option autoImplicit false

noncomputable section

open scoped BigOperators ComplexConjugate ComplexOrder Matrix Kronecker

namespace QuantumProver.AmplitudeDamping.FiniteModel

def pairLabEquivB (a b c d : ℕ) :
    (Fin (a * c) × Fin (b * d)) ≃ ((Fin a × Fin b) × (Fin c × Fin d)) where
  toFun x :=
    ((((finProdFinEquiv : Fin a × Fin c ≃ Fin (a * c)).symm x.1).1,
      ((finProdFinEquiv : Fin b × Fin d ≃ Fin (b * d)).symm x.2).1),
     (((finProdFinEquiv : Fin a × Fin c ≃ Fin (a * c)).symm x.1).2,
      ((finProdFinEquiv : Fin b × Fin d ≃ Fin (b * d)).symm x.2).2))
  invFun x := (finProdFinEquiv (x.1.1, x.2.1), finProdFinEquiv (x.1.2, x.2.2))
  left_inv x := by
    apply Prod.ext
    · change (finProdFinEquiv : Fin a × Fin c ≃ Fin (a * c))
        (finProdFinEquiv.symm x.1) = x.1
      exact finProdFinEquiv.apply_symm_apply x.1
    · change (finProdFinEquiv : Fin b × Fin d ≃ Fin (b * d))
        (finProdFinEquiv.symm x.2) = x.2
      exact finProdFinEquiv.apply_symm_apply x.2
  right_inv x := by
    rcases x with ⟨⟨a₀, b₀⟩, ⟨c₀, d₀⟩⟩
    simp

theorem finProd_eq_iffB {a b : ℕ} (x y : Fin (a * b)) :
    x = y ↔
      ((finProdFinEquiv : Fin a × Fin b ≃ Fin (a * b)).symm x).1 =
        (finProdFinEquiv.symm y).1 ∧
      (finProdFinEquiv.symm x).2 = (finProdFinEquiv.symm y).2 := by
  constructor
  · intro h; subst y; exact ⟨rfl, rfl⟩
  · intro h
    exact (finProdFinEquiv : Fin a × Fin b ≃ Fin (a * b)).symm.injective
      (Prod.ext h.1 h.2)

def pairOperatorB {a b c d ao bo co do_ : ℕ}
    (K : Matrix (Fin ao × Fin bo) (Fin a × Fin b) ℂ)
    (L : Matrix (Fin co × Fin do_) (Fin c × Fin d) ℂ) :
    Matrix (Fin (ao * co) × Fin (bo * do_)) (Fin (a * c) × Fin (b * d)) ℂ :=
  (K ⊗ₖ L).submatrix (pairLabEquivB ao bo co do_) (pairLabEquivB a b c d)

def pairMatrixB {a b c d : ℕ} (ρ : BipartiteMatrix a b) (σ : BipartiteMatrix c d) :
    BipartiteMatrix (a * c) (b * d) := pairOperatorB ρ σ

theorem pairOperatorB_mul {a b c d ao bo co do_ ax bx cx dx : ℕ}
    (K : Matrix (Fin ao × Fin bo) (Fin a × Fin b) ℂ)
    (L : Matrix (Fin co × Fin do_) (Fin c × Fin d) ℂ)
    (M : Matrix (Fin ax × Fin bx) (Fin ao × Fin bo) ℂ)
    (N : Matrix (Fin cx × Fin dx) (Fin co × Fin do_) ℂ) :
    pairOperatorB M N * pairOperatorB K L = pairOperatorB (M * K) (N * L) := by
  simp only [pairOperatorB, Matrix.submatrix_mul_equiv, ← Matrix.mul_kronecker_mul]

theorem pairOperatorB_conjTranspose {a b c d ao bo co do_ : ℕ}
    (K : Matrix (Fin ao × Fin bo) (Fin a × Fin b) ℂ)
    (L : Matrix (Fin co × Fin do_) (Fin c × Fin d) ℂ) :
    (pairOperatorB K L)ᴴ = pairOperatorB Kᴴ Lᴴ := by
  simp only [pairOperatorB, Matrix.conjTranspose_submatrix, Matrix.conjTranspose_kronecker]

theorem pairMatrixB_action {a b c d ao bo co do_ : ℕ}
    (K : Matrix (Fin ao × Fin bo) (Fin a × Fin b) ℂ)
    (L : Matrix (Fin co × Fin do_) (Fin c × Fin d) ℂ)
    (ρ : BipartiteMatrix a b) (σ : BipartiteMatrix c d) :
    pairOperatorB K L * pairMatrixB ρ σ * (pairOperatorB K L)ᴴ =
      pairMatrixB (K * ρ * Kᴴ) (L * σ * Lᴴ) := by
  simp only [pairMatrixB, pairOperatorB_conjTranspose, pairOperatorB_mul]

theorem pairMatrixB_sum_left {a b c d : ℕ} {Z : Type*} [Fintype Z]
    (ρ : Z → BipartiteMatrix a b) (σ : BipartiteMatrix c d) :
    (∑ z, pairMatrixB (ρ z) σ) = pairMatrixB (∑ z, ρ z) σ := by
  ext x y
  simp [pairMatrixB, pairOperatorB, Matrix.sum_apply, Matrix.submatrix_apply,
    Matrix.kronecker_apply, Finset.sum_mul]

theorem pairMatrixB_sum_right {a b c d : ℕ} {Z : Type*} [Fintype Z]
    (ρ : BipartiteMatrix a b) (σ : Z → BipartiteMatrix c d) :
    (∑ z, pairMatrixB ρ (σ z)) = pairMatrixB ρ (∑ z, σ z) := by
  ext x y
  simp [pairMatrixB, pairOperatorB, Matrix.sum_apply, Matrix.submatrix_apply,
    Matrix.kronecker_apply, Finset.mul_sum]

theorem pairKrausSumB {a b c d ao bo co do_ : ℕ} {Z Y : Type*}
    [Fintype Z] [Fintype Y]
    (K : Z → Matrix (Fin ao × Fin bo) (Fin a × Fin b) ℂ)
    (L : Y → Matrix (Fin co × Fin do_) (Fin c × Fin d) ℂ)
    (ρ : BipartiteMatrix a b) (σ : BipartiteMatrix c d) :
    krausSumB (fun h : Z × Y => pairOperatorB (K h.1) (L h.2)) (pairMatrixB ρ σ) =
      pairMatrixB (krausSumB K ρ) (krausSumB L σ) := by
  simp only [krausSumB, Fintype.sum_prod_type, pairMatrixB_action,
    pairMatrixB_sum_left, pairMatrixB_sum_right]

def tensorLeftInstrumentB {i o k : ℕ} (K : KrausInstrument i o k) (m : ℕ) :
    KrausInstrument (i * m) (o * m) k :=
  krausInstrumentOfEquivsB
    (finProdFinEquiv : Fin i × Fin m ≃ Fin (i * m)).symm
    (finProdFinEquiv : Fin o × Fin m ≃ Fin (o * m)).symm
    (Equiv.refl (Fin k)) (fun z => K.operator z ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ))
    (referenceKrausB_complete K.operator K.complete (Fin m))

def tensorRightInstrumentB {i o k : ℕ} (K : KrausInstrument i o k) (m : ℕ) :
    KrausInstrument (m * i) (m * o) k :=
  krausInstrumentOfEquivsB
    (finProdFinEquiv : Fin m × Fin i ≃ Fin (m * i)).symm
    (finProdFinEquiv : Fin m × Fin o ≃ Fin (m * o)).symm
    (Equiv.refl (Fin k)) (fun z => (1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ K.operator z)
    (by rw [krausGramB_memory_left, K.complete, Matrix.one_kronecker_one])

theorem aliceOperator_tensorLeftB {a ao k b c d : ℕ} (K : KrausInstrument a ao k)
    (z : Fin k) :
    aliceOperator (b := b * d) ((tensorLeftInstrumentB K c).operator z) =
      pairOperatorB (aliceOperator (b := b) (K.operator z)) (1 : BipartiteMatrix c d) := by
  ext ⟨x, y⟩ ⟨u, v⟩
  by_cases h1 : y.divNat = v.divNat <;> by_cases h2 : y.modNat = v.modNat <;>
    by_cases h3 : x.modNat = u.modNat <;>
    simp [tensorLeftInstrumentB, krausInstrumentOfEquivsB, pairOperatorB,
    pairLabEquivB, aliceOperator, Matrix.kronecker_apply, Matrix.submatrix_apply,
    Matrix.one_apply, finProd_eq_iffB, Prod.mk.injEq, mul_ite, ite_mul,
    h1, h2, h3]

theorem aliceOperator_tensorRightB {a b c co k d : ℕ} (K : KrausInstrument c co k)
    (z : Fin k) :
    aliceOperator (b := b * d) ((tensorRightInstrumentB K a).operator z) =
      pairOperatorB (1 : BipartiteMatrix a b) (aliceOperator (b := d) (K.operator z)) := by
  ext ⟨x, y⟩ ⟨u, v⟩
  by_cases h1 : y.divNat = v.divNat <;> by_cases h2 : y.modNat = v.modNat <;>
    by_cases h3 : x.divNat = u.divNat <;>
    simp [tensorRightInstrumentB, krausInstrumentOfEquivsB, pairOperatorB,
    pairLabEquivB, aliceOperator, Matrix.kronecker_apply, Matrix.submatrix_apply,
    Matrix.one_apply, finProd_eq_iffB, Prod.mk.injEq, mul_ite, ite_mul,
    h1, h2, h3]

theorem bobOperator_tensorLeftB {a b bo k c d : ℕ} (K : KrausInstrument b bo k)
    (z : Fin k) :
    bobOperator (a := a * c) ((tensorLeftInstrumentB K d).operator z) =
      pairOperatorB (bobOperator (a := a) (K.operator z)) (1 : BipartiteMatrix c d) := by
  ext ⟨x, y⟩ ⟨u, v⟩
  by_cases h1 : x.divNat = u.divNat <;> by_cases h2 : x.modNat = u.modNat <;>
    by_cases h3 : y.modNat = v.modNat <;>
    simp [tensorLeftInstrumentB, krausInstrumentOfEquivsB, pairOperatorB,
    pairLabEquivB, bobOperator, Matrix.kronecker_apply, Matrix.submatrix_apply,
    Matrix.one_apply, finProd_eq_iffB, Prod.mk.injEq, mul_ite, ite_mul,
    h1, h2, h3]

theorem bobOperator_tensorRightB {a b c d do_ k : ℕ} (K : KrausInstrument d do_ k)
    (z : Fin k) :
    bobOperator (a := a * c) ((tensorRightInstrumentB K b).operator z) =
      pairOperatorB (1 : BipartiteMatrix a b) (bobOperator (a := c) (K.operator z)) := by
  ext ⟨x, y⟩ ⟨u, v⟩
  by_cases h1 : x.divNat = u.divNat <;> by_cases h2 : x.modNat = u.modNat <;>
    by_cases h3 : y.divNat = v.divNat <;>
    simp [tensorRightInstrumentB, krausInstrumentOfEquivsB, pairOperatorB,
    pairLabEquivB, bobOperator, Matrix.kronecker_apply, Matrix.submatrix_apply,
    Matrix.one_apply, finProd_eq_iffB, Prod.mk.injEq, mul_ite, ite_mul,
    h1, h2, h3]

theorem alice_tensorLeft_actionB {a ao k b c d : ℕ} (K : KrausInstrument a ao k)
    (z : Fin k) (ρ : BipartiteMatrix a b) (σ : BipartiteMatrix c d) :
    let A := aliceOperator (b := b * d) ((tensorLeftInstrumentB K c).operator z)
    A * pairMatrixB ρ σ * Aᴴ =
      pairMatrixB (aliceOperator (b := b) (K.operator z) * ρ *
        (aliceOperator (b := b) (K.operator z))ᴴ) σ := by
  dsimp only
  rw [aliceOperator_tensorLeftB, pairMatrixB_action]
  simp only [Matrix.one_mul, Matrix.conjTranspose_one, Matrix.mul_one]

theorem alice_tensorRight_actionB {a b c co k d : ℕ} (K : KrausInstrument c co k)
    (z : Fin k) (ρ : BipartiteMatrix a b) (σ : BipartiteMatrix c d) :
    let A := aliceOperator (b := b * d) ((tensorRightInstrumentB K a).operator z)
    A * pairMatrixB ρ σ * Aᴴ =
      pairMatrixB ρ (aliceOperator (b := d) (K.operator z) * σ *
        (aliceOperator (b := d) (K.operator z))ᴴ) := by
  dsimp only
  rw [aliceOperator_tensorRightB, pairMatrixB_action]
  simp only [Matrix.one_mul, Matrix.conjTranspose_one, Matrix.mul_one]

theorem bob_tensorLeft_actionB {a b bo k c d : ℕ} (K : KrausInstrument b bo k)
    (z : Fin k) (ρ : BipartiteMatrix a b) (σ : BipartiteMatrix c d) :
    let B := bobOperator (a := a * c) ((tensorLeftInstrumentB K d).operator z)
    B * pairMatrixB ρ σ * Bᴴ =
      pairMatrixB (bobOperator (a := a) (K.operator z) * ρ *
        (bobOperator (a := a) (K.operator z))ᴴ) σ := by
  dsimp only
  rw [bobOperator_tensorLeftB, pairMatrixB_action]
  simp only [Matrix.one_mul, Matrix.conjTranspose_one, Matrix.mul_one]

theorem bob_tensorRight_actionB {a b c d do_ k : ℕ} (K : KrausInstrument d do_ k)
    (z : Fin k) (ρ : BipartiteMatrix a b) (σ : BipartiteMatrix c d) :
    let B := bobOperator (a := a * c) ((tensorRightInstrumentB K b).operator z)
    B * pairMatrixB ρ σ * Bᴴ =
      pairMatrixB ρ (bobOperator (a := c) (K.operator z) * σ *
        (bobOperator (a := c) (K.operator z))ᴴ) := by
  dsimp only
  rw [bobOperator_tensorRightB, pairMatrixB_action]
  simp only [Matrix.one_mul, Matrix.conjTranspose_one, Matrix.mul_one]

def headTailMemoryEquivB (X Y A C : Type*) :
    ((X × Y) × (A × C)) ≃ ((Y × A) × (X × C)) where
  toFun x := ((x.1.2, x.2.1), (x.1.1, x.2.2))
  invFun x := ((x.2.1, x.1.1), (x.1.2, x.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

def mergeInputEquivB (n a c : ℕ) :
    Fin (doubleDimB (n + 1) (a * c)) ≃ Fin (doubleDimB n a * (2 * c)) :=
  (inputQubitWordEquivB (n + 1) (a * c)).trans
    ((((Fin.consEquiv (fun _ : Fin (n + 1) => Qubit)).symm.prodCongr
      (finProdFinEquiv : Fin a × Fin c ≃ Fin (a * c)).symm).trans
      ((headTailMemoryEquivB Qubit (Fin n → Qubit) (Fin a) (Fin c)).trans
        (((inputQubitWordEquivB n a).symm.prodCongr (splitQubit c).symm).trans
          (finProdFinEquiv : Fin (doubleDimB n a) × Fin (2 * c) ≃
            Fin (doubleDimB n a * (2 * c)))))))

def mergeOutputEquivB (n b d : ℕ) :
    Fin (doubleDimB (n + 1) (b * d)) ≃ Fin (doubleDimB n b * (2 * d)) :=
  (outputQubitWordEquivB (n + 1) (b * d)).trans
    ((((Fin.consEquiv (fun _ : Fin (n + 1) => Qubit)).symm.prodCongr
      (finProdFinEquiv : Fin b × Fin d ≃ Fin (b * d)).symm).trans
      ((headTailMemoryEquivB Qubit (Fin n → Qubit) (Fin b) (Fin d)).trans
        (((outputQubitWordEquivB n b).symm.prodCongr (splitQubit d).symm).trans
          (finProdFinEquiv : Fin (doubleDimB n b) × Fin (2 * d) ≃
            Fin (doubleDimB n b * (2 * d)))))))

theorem mergeInputEquivB_symm_chart (n a c : ℕ)
    (y : Fin (doubleDimB n a * (2 * c))) :
    inputQubitWordEquivB (n + 1) (a * c) ((mergeInputEquivB n a c).symm y) =
      (Fin.cons (splitQubit c (finProdFinEquiv.symm y).2).1
        (inputQubitWordEquivB n a (finProdFinEquiv.symm y).1).1,
       finProdFinEquiv ((inputQubitWordEquivB n a (finProdFinEquiv.symm y).1).2,
         (splitQubit c (finProdFinEquiv.symm y).2).2)) := by
  simp [mergeInputEquivB, headTailMemoryEquivB, Equiv.trans_apply,
    Equiv.symm_trans_apply, Fin.consEquiv]

theorem mergeOutputEquivB_symm_chart (n b d : ℕ)
    (x : Fin (doubleDimB n b * (2 * d))) :
    outputQubitWordEquivB (n + 1) (b * d) ((mergeOutputEquivB n b d).symm x) =
      (Fin.cons (splitQubit d (finProdFinEquiv.symm x).2).1
        (outputQubitWordEquivB n b (finProdFinEquiv.symm x).1).1,
       finProdFinEquiv ((outputQubitWordEquivB n b (finProdFinEquiv.symm x).1).2,
         (splitQubit d (finProdFinEquiv.symm x).2).2)) := by
  simp [mergeOutputEquivB, headTailMemoryEquivB, Equiv.trans_apply,
    Equiv.symm_trans_apply, Fin.consEquiv]

theorem bobRelabel_mulB {a i o : ℕ} {J : Type*} (e : Fin o ≃ Fin i)
    (M : Matrix (Fin a × Fin i) J ℂ) :
    bobOperator (a := a) ((relabelInstrumentB e).operator 0) * M =
      M.submatrix ((Equiv.refl (Fin a)).prodCongr e) id := by
  rw [bobRelabelOperatorB]
  simpa only [Equiv.refl_symm, Equiv.coe_refl, Function.id_comp] using
    Matrix.one_submatrix_mul ((Equiv.refl (Fin a)).prodCongr e)
      (Equiv.refl (Fin a × Fin i)) M

theorem aliceRelabel_rightMulB {i o b : ℕ} {J : Type*} (e : Fin o ≃ Fin i)
    (M : Matrix J (Fin o × Fin b) ℂ) :
    M * aliceOperator (b := b) ((relabelInstrumentB e).operator 0) =
      M.submatrix id (e.symm.prodCongr (Equiv.refl (Fin b))) := by
  rw [aliceRelabelOperatorB]
  simpa only [Equiv.prodCongr_symm, Equiv.refl_symm, Equiv.coe_refl,
    Function.comp_id] using
    Matrix.mul_submatrix_one (e.prodCongr (Equiv.refl (Fin b)))
      (Equiv.refl (Fin i × Fin b)) M

def mergeCallKrausB (p : ℝ) (n a b c d : ℕ) (h : Fin (n + 1) → Qubit) :
    Matrix (Fin (a * c) × Fin (doubleDimB n b * (2 * d)))
      (Fin (doubleDimB n a * (2 * c)) × Fin (b * d)) ℂ :=
  bobOperator (a := a * c)
      ((relabelInstrumentB (mergeOutputEquivB n b d).symm).operator 0) *
    sequentialCallsKrausB p (n + 1) (a * c) (b * d) h *
      aliceOperator (b := b * d)
        ((relabelInstrumentB (mergeInputEquivB n a c)).operator 0)

theorem mergeCallKrausB_eq_pair (p : ℝ) (n a b c d : ℕ)
    (h : Fin (n + 1) → Qubit) :
    mergeCallKrausB p n a b c d h =
      pairOperatorB (sequentialCallsKrausB p n a b (Fin.tail h))
        (callOperator p c d (h 0)) := by
  rw [mergeCallKrausB, bobRelabel_mulB, aliceRelabel_rightMulB]
  ext ⟨x, y⟩ ⟨u, v⟩
  simp only [Matrix.submatrix_apply, Function.comp_apply, Equiv.refl_apply,
    Equiv.prodCongr_apply, Equiv.symm_symm, id_eq]
  change sequentialCallsKrausB p (n + 1) (a * c) (b * d) h
    (x, (mergeOutputEquivB n b d).symm y)
    ((mergeInputEquivB n a c).symm u, v) = _
  rw [sequentialCallsKrausB_entry, mergeInputEquivB_symm_chart,
    mergeOutputEquivB_symm_chart]
  by_cases hA : x.divNat = (inputQubitWordEquivB n a u.divNat).2 <;>
    by_cases hC : x.modNat = (splitQubit c u.modNat).2 <;>
    by_cases hB : (outputQubitWordEquivB n b y.divNat).2 = v.divNat <;>
    by_cases hD : (splitQubit d y.modNat).2 = v.modNat <;>
    simp [pairOperatorB, pairLabEquivB, Matrix.submatrix_apply,
    Matrix.kronecker_apply, sequentialCallsKrausB_entry, callOperator,
    Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, Fin.tail,
    finProd_eq_iffB, mul_ite, ite_mul, hA, hC, hB, hD] <;> ring

def mergeBlockCallThenB (p : ℝ) (n a b c d : ℕ) {af bf : ℕ}
    (Q : FiniteBlockProtocolB p (n + 1) (a * c) (doubleDimB n b * (2 * d)) af bf) :
    FiniteBlockProtocolB p (n + 1) (doubleDimB n a * (2 * c)) (b * d) af bf :=
  .alice (relabelInstrumentB (mergeInputEquivB n a c)) fun _ =>
    .blockCall (.bob (relabelInstrumentB (mergeOutputEquivB n b d).symm) fun _ => Q)

theorem mergeBlockCallThenB_calls (p : ℝ) (n a b c d : ℕ) {af bf : ℕ}
    (Q : FiniteBlockProtocolB p (n + 1) (a * c) (doubleDimB n b * (2 * d)) af bf) :
    (mergeBlockCallThenB p n a b c d Q).calls = Q.calls + 1 := by
  simp [mergeBlockCallThenB, FiniteBlockProtocolB.calls, Finset.univ_unique]

theorem mergeBlockCallThenB_output (p : ℝ) (n a b c d : ℕ) {af bf : ℕ}
    (Q : FiniteBlockProtocolB p (n + 1) (a * c) (doubleDimB n b * (2 * d)) af bf)
    (ρ : BipartiteMatrix (doubleDimB n a * (2 * c)) (b * d)) :
    (mergeBlockCallThenB p n a b c d Q).output ρ =
      Q.output (krausSumB (mergeCallKrausB p n a b c d) ρ) := by
  simp only [mergeBlockCallThenB, FiniteBlockProtocolB.output, Fin.sum_univ_one]
  congr 1
  simp only [krausSumB, mergeCallKrausB, Matrix.mul_sum, Matrix.sum_mul,
    Matrix.conjTranspose_mul, Matrix.mul_assoc]

def mergeHistoryEquivB (n : ℕ) : ((Fin n → Qubit) × Qubit) ≃ (Fin (n + 1) → Qubit) :=
  (Equiv.prodComm (Fin n → Qubit) Qubit).trans
    (Fin.consEquiv (fun _ : Fin (n + 1) => Qubit))

theorem mergeBlockCallThenB_product_output (p : ℝ) (n a b c d : ℕ) {af bf : ℕ}
    (Q : FiniteBlockProtocolB p (n + 1) (a * c) (doubleDimB n b * (2 * d)) af bf)
    (ρ : BipartiteMatrix (doubleDimB n a) b) (σ : BipartiteMatrix (2 * c) d) :
    (mergeBlockCallThenB p n a b c d Q).output (pairMatrixB ρ σ) =
      Q.output (pairMatrixB (krausSumB (sequentialCallsKrausB p n a b) ρ)
        (krausSumB (callOperator p c d) σ)) := by
  rw [mergeBlockCallThenB_output]
  congr 1
  calc
    _ = krausSumB (fun h : (Fin n → Qubit) × Qubit =>
        mergeCallKrausB p n a b c d (mergeHistoryEquivB n h)) (pairMatrixB ρ σ) :=
      (krausSumB_outcome_equiv (mergeHistoryEquivB n) (mergeCallKrausB p n a b c d)
        (pairMatrixB ρ σ)).symm
    _ = krausSumB (fun h : (Fin n → Qubit) × Qubit =>
        pairOperatorB (sequentialCallsKrausB p n a b h.1) (callOperator p c d h.2))
        (pairMatrixB ρ σ) := by
      congr 1
      funext h
      simp [mergeCallKrausB_eq_pair, mergeHistoryEquivB, Fin.consEquiv]
    _ = _ := pairKrausSumB (sequentialCallsKrausB p n a b) (callOperator p c d) ρ σ

def spectatorPortSwapEquivB (c a : ℕ) :
    (Qubit × (Fin c × Fin a)) ≃ (Fin c × (Qubit × Fin a)) where
  toFun x := (x.2.1, (x.1, x.2.2))
  invFun x := (x.2.1, (x.1, x.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

def aliceSpectatorPortEquivB (c a : ℕ) :
    Fin (2 * (c * a)) ≃ (Fin c × Fin (2 * a)) :=
  (splitQubit (c * a)).trans
    (((Equiv.refl Qubit).prodCongr
      (finProdFinEquiv : Fin c × Fin a ≃ Fin (c * a)).symm).trans
      ((spectatorPortSwapEquivB c a).trans
        ((Equiv.refl (Fin c)).prodCongr (splitQubit a).symm)))

def aliceSpectatorInputEquivB (c a b : ℕ) :
    (Fin (2 * (c * a)) × Fin b) ≃ (Fin c × (Fin (2 * a) × Fin b)) :=
  ((aliceSpectatorPortEquivB c a).prodCongr (Equiv.refl (Fin b))).trans
    (Equiv.prodAssoc (Fin c) (Fin (2 * a)) (Fin b))

def aliceSpectatorOutputEquivB (c a b : ℕ) :
    (Fin (c * a) × Fin (2 * b)) ≃ (Fin c × (Fin a × Fin (2 * b))) :=
  (((finProdFinEquiv : Fin c × Fin a ≃ Fin (c * a)).symm).prodCongr
    (Equiv.refl (Fin (2 * b)))).trans (Equiv.prodAssoc (Fin c) (Fin a) (Fin (2 * b)))

theorem callOperator_aliceSpectatorB (p : ℝ) (c a b : ℕ) (z : Qubit) :
    callOperator p (c * a) b z =
      ((1 : Matrix (Fin c) (Fin c) ℂ) ⊗ₖ callOperator p a b z).submatrix
        (aliceSpectatorOutputEquivB c a b) (aliceSpectatorInputEquivB c a b) := by
  ext ⟨x, y⟩ ⟨u, v⟩
  by_cases hC : x.divNat = ((splitQubit (c * a) u).2).divNat <;>
    by_cases hA : x.modNat = ((splitQubit (c * a) u).2).modNat <;>
    by_cases hB : (splitQubit b y).2 = v <;>
    simp [callOperator, aliceSpectatorInputEquivB, aliceSpectatorOutputEquivB,
      aliceSpectatorPortEquivB, spectatorPortSwapEquivB,
      Matrix.submatrix_apply, Matrix.kronecker_apply, Matrix.one_apply,
      Equiv.trans_apply, finProd_eq_iffB, Prod.mk.injEq, mul_ite, ite_mul, hC, hA, hB]

def FiniteBlockProtocolB.UniformCallsB {p : ℝ} {n a b af bf : ℕ}
    (P : FiniteBlockProtocolB p n a b af bf) (m : ℕ) : Prop :=
  match P with
  | .done _ _ => m = 0
  | .alice _ next => ∀ z, (next z).UniformCallsB m
  | .bob _ next => ∀ z, (next z).UniformCallsB m
  | .blockCall next => ∃ k, m = k + 1 ∧ next.UniformCallsB k

def FiniteBlockProtocolB.heightB {p : ℝ} {n a b af bf : ℕ}
    (P : FiniteBlockProtocolB p n a b af bf) : ℕ :=
  match P with
  | .done _ _ => 0
  | .alice _ next => (Finset.univ.sup fun z => (next z).heightB) + 1
  | .bob _ next => (Finset.univ.sup fun z => (next z).heightB) + 1
  | .blockCall next => next.heightB + 1

def FiniteProtocol.heightB {p : ℝ} {a b af bf : ℕ}
    (P : FiniteProtocol p a b af bf) : ℕ :=
  match P with
  | .done _ _ => 0
  | .alice _ next => (Finset.univ.sup fun z => (next z).heightB) + 1
  | .bob _ next => (Finset.univ.sup fun z => (next z).heightB) + 1
  | .call next => next.heightB + 1

theorem mergeBlockCallThenB_uniform (p : ℝ) (n a b c d : ℕ) {af bf m : ℕ}
    {Q : FiniteBlockProtocolB p (n + 1) (a * c) (doubleDimB n b * (2 * d)) af bf}
    (hQ : Q.UniformCallsB m) :
    (mergeBlockCallThenB p n a b c d Q).UniformCallsB (m + 1) := by
  change ∀ _ : Fin 1, ∃ k, m + 1 = k + 1 ∧ ∀ _ : Fin 1, Q.UniformCallsB k
  intro _
  exact ⟨m, rfl, fun _ => hQ⟩

def scalarWordEquivB : Qubit ≃ (Fin 1 → Qubit) where
  toFun q := fun _ => q
  invFun h := h 0
  left_inv _ := rfl
  right_inv h := by
    funext i
    fin_cases i
    rfl

theorem sequentialCallsKrausB_one (p : ℝ) (a b : ℕ) (h : Fin 1 → Qubit) :
    sequentialCallsKrausB p 1 a b h = callOperator p a b (h 0) := by
  have hI (x : Fin (2 * a)) : inputQubitWordEquivB 1 a x =
      (fun _ : Fin 1 => (splitQubit a x).1, (splitQubit a x).2) := by
    apply Prod.ext
    · funext i
      fin_cases i
      apply Fin.ext
      rfl
    · apply Fin.ext
      rfl
  have hO (x : Fin (2 * b)) : outputQubitWordEquivB 1 b x =
      (fun _ : Fin 1 => (splitQubit b x).1, (splitQubit b x).2) := by
    apply Prod.ext
    · funext i
      fin_cases i
      rfl
    · rfl
  ext ⟨x, y⟩ ⟨u, v⟩
  rw [sequentialCallsKrausB_entry]
  simp only [hI, hO, Fin.prod_univ_one]
  rfl

theorem sequentialCallsKrausB_one_output (p : ℝ) (a b : ℕ)
    (ρ : BipartiteMatrix (2 * a) b) :
    krausSumB (sequentialCallsKrausB p 1 a b) ρ =
      krausSumB (callOperator p a b) ρ := by
  have hK : sequentialCallsKrausB p 1 a b =
      fun h : Fin 1 → Qubit => callOperator p a b (h 0) := by
    funext h
    exact sequentialCallsKrausB_one p a b h
  calc
    _ = krausSumB (fun h : Fin 1 → Qubit => callOperator p a b (h 0)) ρ :=
      congrArg (fun K : (Fin 1 → Qubit) →
        Matrix (Fin a × Fin (2 * b)) (Fin (2 * a) × Fin b) ℂ => krausSumB K ρ) hK
    _ = _ := by
      have hs := scalarWordEquivB.symm.sum_comp
        (fun q => callOperator p a b q * ρ * (callOperator p a b q)ᴴ)
      change (∑ h : Fin 1 → Qubit, callOperator p a b (h 0) * ρ *
        (callOperator p a b (h 0))ᴴ) = _ at hs
      exact hs

def FiniteProtocol.toBlockOneB {p : ℝ} {a b af bf : ℕ}
    (P : FiniteProtocol p a b af bf) : FiniteBlockProtocolB p 1 a b af bf :=
  match P with
  | .done a b => .done a b
  | .alice K next => .alice K fun z => (next z).toBlockOneB
  | .bob K next => .bob K fun z => (next z).toBlockOneB
  | .call next => .blockCall next.toBlockOneB

theorem FiniteProtocol.toBlockOneB_calls {p : ℝ} {a b af bf : ℕ}
    (P : FiniteProtocol p a b af bf) : P.toBlockOneB.calls = P.calls := by
  induction P with
  | done a b => rfl
  | alice K next ih =>
    simp only [FiniteProtocol.toBlockOneB, FiniteBlockProtocolB.calls, FiniteProtocol.calls, ih]
  | bob K next ih =>
    simp only [FiniteProtocol.toBlockOneB, FiniteBlockProtocolB.calls, FiniteProtocol.calls, ih]
  | call next ih =>
    change next.toBlockOneB.calls + 1 = next.calls + 1
    exact congrArg (fun x : ℕ => x + 1) ih

theorem FiniteProtocol.toBlockOneB_uniform {p : ℝ} {a b af bf m : ℕ}
    {P : FiniteProtocol p a b af bf} (hP : P.UniformCallsB m) :
    P.toBlockOneB.UniformCallsB m := by
  induction P generalizing m with
  | done a b => exact hP
  | alice K next ih => exact fun z => ih z (hP z)
  | bob K next ih => exact fun z => ih z (hP z)
  | call next ih =>
    rcases hP with ⟨k, hm, hk⟩
    exact ⟨k, hm, ih hk⟩

theorem FiniteProtocol.toBlockOneB_output {p : ℝ} {a b af bf : ℕ}
    (P : FiniteProtocol p a b af bf) :
    ∀ ρ, P.toBlockOneB.output ρ = P.output ρ := by
  induction P with
  | done a b => intro ρ; rfl
  | alice K next ih =>
    intro ρ
    simp only [FiniteProtocol.toBlockOneB, FiniteBlockProtocolB.output,
      FiniteProtocol.output, ih]
  | bob K next ih =>
    intro ρ
    simp only [FiniteProtocol.toBlockOneB, FiniteBlockProtocolB.output,
      FiniteProtocol.output, ih]
  | call next ih =>
    intro ρ
    change next.toBlockOneB.output (krausSumB (sequentialCallsKrausB p 1 _ _) ρ) =
      next.output (krausSumB (callOperator p _ _) ρ)
    calc
      _ = next.toBlockOneB.output (krausSumB (callOperator p _ _) ρ) :=
        congrArg next.toBlockOneB.output (sequentialCallsKrausB_one_output p _ _ ρ)
      _ = _ := ih _

end QuantumProver.AmplitudeDamping.FiniteModel

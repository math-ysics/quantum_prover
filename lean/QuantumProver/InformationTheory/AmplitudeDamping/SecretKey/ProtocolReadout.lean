import QuantumProver.LinearAlgebra.MatrixSqrt.Derivatives
import QuantumProver.InformationTheory.AmplitudeDamping.SecretKey.Definitions
import QuantumProver.InformationTheory.AmplitudeDamping.SecretKey.ScalarBounds
import QuantumProver.InformationTheory.AmplitudeDamping.SecretKey.PurificationBounds

noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix Kronecker

namespace QuantumProver.AmplitudeDamping.SecretKey

theorem physical_amplitudeDamping_preserves_trace {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    ((amplitudeDamping p hp0 hp1).eval ρ).trace = ρ.trace :=
  (amplitudeDamping p hp0 hp1).trace_eval ρ

namespace PhysicalProtocol

def transferInputEquiv (a b : ℕ) :
    (Fin (2 * a) × Fin b) ≃ ((Fin a × Fin b) × Fin 2) where
  toFun y := (((splitQubit a y.1).2, y.2), (splitQubit a y.1).1)
  invFun t := ((splitQubit a).symm (t.2, t.1.1), t.1.2)
  left_inv y := by simp
  right_inv t := by simp

def transferOutputEquiv (a b : ℕ) :
    (Fin a × Fin (2 * b)) ≃ ((Fin a × Fin b) × Fin 2) where
  toFun x := ((x.1, (splitQubit b x.2).2), (splitQubit b x.2).1)
  invFun t := (t.1.1, (splitQubit b).symm (t.2, t.1.2))
  left_inv x := by simp
  right_inv t := by simp

theorem transferKraus_eq_reindex (p : ℝ) (a b : ℕ) (z : Fin 2) :
    transferKraus p a b z =
      ((1 : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) ⊗ₖ
        amplitudeDampingKraus p z).submatrix
          (transferOutputEquiv a b) (transferInputEquiv a b) := by
  ext x y
  simp [transferKraus, transferOutputEquiv, transferInputEquiv,
    Matrix.kroneckerMap_apply, Matrix.one_apply, Prod.mk.injEq, mul_comm]

theorem transferKraus_complete {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (a b : ℕ) :
    ∑ z, (transferKraus p a b z)ᴴ * transferKraus p a b z = 1 := by
  have hg := ((amplitudeDamping p hp0 hp1).withMemory (Fin a × Fin b)).complete
  simp only [KrausChannel.withMemory, amplitudeDamping] at hg
  simp only [transferKraus_eq_reindex, Matrix.conjTranspose_submatrix,
    Matrix.submatrix_mul_equiv]
  have hs : (∑ z,
      (((1 : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) ⊗ₖ
          amplitudeDampingKraus p z)ᴴ *
        ((1 : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) ⊗ₖ
          amplitudeDampingKraus p z)).submatrix
          (transferInputEquiv a b) (transferInputEquiv a b)) =
      (∑ z,
        ((1 : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) ⊗ₖ
          amplitudeDampingKraus p z)ᴴ *
        ((1 : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) ⊗ₖ
          amplitudeDampingKraus p z)).submatrix
            (transferInputEquiv a b) (transferInputEquiv a b) := by
    ext x y
    simp
  rw [hs, hg, Matrix.submatrix_one_equiv]

def transferChannel (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (a b : ℕ) :
    KrausChannel (Fin (2 * a) × Fin b) (Fin a × Fin (2 * b)) (Fin 2) where
  op := transferKraus p a b
  complete := transferKraus_complete hp0 hp1 a b

end PhysicalProtocol

namespace MemoryMatrix

theorem trace_submatrix_equiv {I K : Type*} [Fintype I] [Fintype K]
    (e : K ≃ I) (M : Matrix I I ℂ) :
    (M.submatrix e e).trace = M.trace := by
  exact e.sum_comp (fun i => M i i)

theorem trace_publicBranches {K Z : Type*} {T : Z → Type*}
    [Fintype K] [Fintype Z] [∀ z, Fintype (T z)]
    (R : Matrix (K × Sigma T) (K × Sigma T) ℂ)
    (M : ∀ z, Matrix (K × T z) (K × T z) ℂ)
    (hdiag : ∀ (i : K) (z : Z) (t : T z),
      R (i, ⟨z, t⟩) (i, ⟨z, t⟩) = M z (i, t) (i, t)) :
    R.trace = ∑ z, (M z).trace := by
  change (∑ x : K × Sigma T, R x x) =
    ∑ z, ∑ x : K × T z, M z x x
  rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_sigma, hdiag]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z hz
  rw [Fintype.sum_prod_type]

theorem trace_quantumBranches {K Z T : Type*}
    [Fintype K] [Fintype Z] [Fintype T]
    (R : Matrix (K × (Z × T)) (K × (Z × T)) ℂ)
    (M : Z → Matrix (K × T) (K × T) ℂ)
    (hdiag : ∀ (i : K) (z : Z) (t : T),
      R (i, (z, t)) (i, (z, t)) = M z (i, t) (i, t)) :
    R.trace = ∑ z, (M z).trace := by
  change (∑ x : K × (Z × T), R x x) =
    ∑ z, ∑ x : K × T, M z x x
  rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type (α₁ := Z) (α₂ := T), hdiag]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z hz
  rw [Fintype.sum_prod_type]

theorem congruence_withRightMemory_apply {I O E : Type*}
    [Fintype I] [Fintype E] [DecidableEq E]
    (K : Matrix O I ℂ)
    (ρ : Matrix (I × E) (I × E) ℂ) (o o' : O) (e e' : E) :
    (((K ⊗ₖ (1 : Matrix E E ℂ)) * ρ *
      (K ⊗ₖ (1 : Matrix E E ℂ))ᴴ) (o, e) (o', e')) =
      (K * Matrix.of (fun i j => ρ (i, e) (j, e')) * Kᴴ) o o' := by
  classical
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.kroneckerMap_apply, Matrix.one_apply, Fintype.sum_prod_type,
    Finset.sum_mul, Finset.mul_sum, Matrix.of_apply,
    apply_ite, ite_mul, mul_ite, mul_assoc]

theorem jointCongruence_withRightMemory_apply {I O J E : Type*}
    [Fintype I] [Fintype O] [Fintype J] [Fintype E]
    [DecidableEq I] [DecidableEq E]
    (C : KrausChannel I O J)
    (ρ : Matrix (I × E) (I × E) ℂ)
    (o o' : O) (j j' : J) (e e' : E) :
    (((C.stinespring ⊗ₖ (1 : Matrix E E ℂ)) * ρ *
      (C.stinespring ⊗ₖ (1 : Matrix E E ℂ))ᴴ) ((o, j), e) ((o', j'), e')) =
      (C.op j * Matrix.of (fun i k => ρ (i, e) (k, e')) * (C.op j')ᴴ) o o' := by
  rw [congruence_withRightMemory_apply]
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply, KrausChannel.stinespring]

theorem blockDiagonal'_posSemidef {Z : Type*} {J : Z → Type*}
    [Fintype Z] [DecidableEq Z] [∀ z, Fintype (J z)]
    [∀ z, DecidableEq (J z)]
    (M : ∀ z, Matrix (J z) (J z) ℂ) (hM : ∀ z, (M z).PosSemidef) :
    (Matrix.blockDiagonal' M).PosSemidef := by
  let W := Matrix.blockDiagonal' fun z => CFC.sqrt (M z)
  have hsqrt (z : Z) : (CFC.sqrt (M z))ᴴ = CFC.sqrt (M z) :=
    IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg (M z))
  have hfactor : Matrix.blockDiagonal' M = W * Wᴴ := by
    dsimp [W]
    rw [Matrix.blockDiagonal'_conjTranspose, ← Matrix.blockDiagonal'_mul]
    congr 1
    funext z
    rw [hsqrt z, CFC.sqrt_mul_sqrt_self (M z) (hM z).nonneg]
  rw [hfactor]
  exact Matrix.posSemidef_self_mul_conjTranspose W

end MemoryMatrix

namespace PhysicalProtocol.FiniteKeyProtocol

theorem fullOutput_trace {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {a b af bf : ℕ} (P : PhysicalProtocol.FiniteKeyProtocol p a b af bf) :
    ∀ ρ : PhysicalProtocol.BipartiteMatrix a b,
      (P.fullOutput ρ).trace = ρ.trace := by
  induction P with
  | done a b =>
      intro ρ
      change (∑ x : (Fin a × Fin b) × Unit, ρ x.1 x.1) =
        ∑ x : Fin a × Fin b, ρ x x
      rw [Fintype.sum_prod_type]
      simp
  | @alice a b ao af bf k C next ih =>
      intro ρ
      have htrace : ((PhysicalProtocol.FiniteKeyProtocol.alice C next).fullOutput ρ).trace =
          ∑ z, ((next z).fullOutput
            ((C.op z ⊗ₖ (1 : Matrix (Fin b) (Fin b) ℂ)) * ρ *
              (C.op z ⊗ₖ (1 : Matrix (Fin b) (Fin b) ℂ))ᴴ)).trace := by
        apply MemoryMatrix.trace_publicBranches
        intro i z t
        simp [fullOutput]
      rw [htrace]
      simp_rw [ih]
      simpa [KrausChannel.eval, KrausChannel.withRightMemory] using
        (C.withRightMemory (Fin b)).trace_eval ρ
  | @bob a b bo af bf k C next ih =>
      intro ρ
      have htrace : ((PhysicalProtocol.FiniteKeyProtocol.bob C next).fullOutput ρ).trace =
          ∑ z, ((next z).fullOutput
            (((1 : Matrix (Fin a) (Fin a) ℂ) ⊗ₖ C.op z) * ρ *
              ((1 : Matrix (Fin a) (Fin a) ℂ) ⊗ₖ C.op z)ᴴ)).trace := by
        apply MemoryMatrix.trace_publicBranches
        intro i z t
        simp [fullOutput]
      rw [htrace]
      simp_rw [ih]
      simpa [KrausChannel.eval, KrausChannel.withMemory] using
        (C.withMemory (Fin a)).trace_eval ρ
  | @call a b af bf next ih =>
      intro ρ
      have htrace : ((PhysicalProtocol.FiniteKeyProtocol.call next).fullOutput ρ).trace =
          ∑ z, (next.fullOutput
            (PhysicalProtocol.transferKraus p a b z * ρ *
              (PhysicalProtocol.transferKraus p a b z)ᴴ)).trace := by
        apply MemoryMatrix.trace_quantumBranches
        intro i z t
        rfl
      rw [htrace]
      simp_rw [ih]
      simpa [KrausChannel.eval, PhysicalProtocol.transferChannel] using
        (PhysicalProtocol.transferChannel p hp0 hp1 a b).trace_eval ρ

theorem fullOutput_add {p : ℝ} {a b af bf : ℕ}
    (P : PhysicalProtocol.FiniteKeyProtocol p a b af bf)
    (ρ σ : PhysicalProtocol.BipartiteMatrix a b) :
    P.fullOutput (ρ + σ) = P.fullOutput ρ + P.fullOutput σ := by
  induction P with
  | done a b => rfl
  | alice C next ih =>
      ext x y
      rw [Matrix.add_apply]
      rcases x with ⟨x, ⟨z, t⟩⟩
      rcases y with ⟨y, ⟨z', u⟩⟩
      by_cases h : z = z'
      · subst z'
        simp [fullOutput, Matrix.add_apply,
          Matrix.mul_add, Matrix.add_mul, ih]
      · simp [fullOutput, Matrix.add_apply, h]
  | bob C next ih =>
      ext x y
      rw [Matrix.add_apply]
      rcases x with ⟨x, ⟨z, t⟩⟩
      rcases y with ⟨y, ⟨z', u⟩⟩
      by_cases h : z = z'
      · subst z'
        simp [fullOutput, Matrix.add_apply,
          Matrix.mul_add, Matrix.add_mul, ih]
      · simp [fullOutput, Matrix.add_apply, h]
  | call next ih =>
      ext x y
      simp only [fullOutput]
      rw [Matrix.mul_add, Matrix.add_mul, ih]
      rfl

theorem fullOutput_smul {p : ℝ} {a b af bf : ℕ}
    (P : PhysicalProtocol.FiniteKeyProtocol p a b af bf)
    (c : ℂ) (ρ : PhysicalProtocol.BipartiteMatrix a b) :
    P.fullOutput (c • ρ) = c • P.fullOutput ρ := by
  induction P with
  | done a b => rfl
  | alice C next ih =>
      ext x y
      rw [Matrix.smul_apply]
      rcases x with ⟨x, ⟨z, t⟩⟩
      rcases y with ⟨y, ⟨z', u⟩⟩
      by_cases h : z = z'
      · subst z'
        simp [fullOutput, Matrix.smul_apply,
          Matrix.mul_smul, Matrix.smul_mul, ih]
      · simp [fullOutput, Matrix.smul_apply, h]
  | bob C next ih =>
      ext x y
      rw [Matrix.smul_apply]
      rcases x with ⟨x, ⟨z, t⟩⟩
      rcases y with ⟨y, ⟨z', u⟩⟩
      by_cases h : z = z'
      · subst z'
        simp [fullOutput, Matrix.smul_apply,
          Matrix.mul_smul, Matrix.smul_mul, ih]
      · simp [fullOutput, Matrix.smul_apply, h]
  | call next ih =>
      ext x y
      simp only [fullOutput]
      rw [Matrix.mul_smul, Matrix.smul_mul, ih]
      rfl

def fullOutputLinearMap {p : ℝ} {a b af bf : ℕ}
    (P : PhysicalProtocol.FiniteKeyProtocol p a b af bf) :
    PhysicalProtocol.BipartiteMatrix a b →ₗ[ℂ]
      Matrix ((Fin af × Fin bf) × P.Environment)
        ((Fin af × Fin bf) × P.Environment) ℂ where
  toFun := P.fullOutput
  map_add' := P.fullOutput_add
  map_smul' := P.fullOutput_smul

def withPriorEve {p : ℝ} {a b af bf : ℕ}
    (P : PhysicalProtocol.FiniteKeyProtocol p a b af bf) (E : Type*)
    (ρ : Matrix ((Fin a × Fin b) × E) ((Fin a × Fin b) × E) ℂ) :
    Matrix (((Fin af × Fin bf) × P.Environment) × E)
      (((Fin af × Fin bf) × P.Environment) × E) ℂ :=
  fun x y => P.fullOutput (Matrix.of (fun i j => ρ (i, x.2) (j, y.2))) x.1 y.1

theorem withPriorEve_trace {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {a b af bf : ℕ} (P : PhysicalProtocol.FiniteKeyProtocol p a b af bf)
    (E : Type*) [Fintype E]
    (ρ : Matrix ((Fin a × Fin b) × E) ((Fin a × Fin b) × E) ℂ) :
    (P.withPriorEve E ρ).trace = ρ.trace := by
  calc
    (P.withPriorEve E ρ).trace =
        ∑ e, (P.fullOutput (fun i j => ρ (i, e) (j, e))).trace := by
      change (∑ x : ((Fin af × Fin bf) × P.Environment) × E,
        P.fullOutput (fun i j => ρ (i, x.2) (j, x.2)) x.1 x.1) =
        ∑ e, ∑ x : (Fin af × Fin bf) × P.Environment,
          P.fullOutput (fun i j => ρ (i, e) (j, e)) x x
      rw [Fintype.sum_prod_type]
      exact Finset.sum_comm
    _ = ∑ e, (Matrix.of (fun i j => ρ (i, e) (j, e)) :
          PhysicalProtocol.BipartiteMatrix a b).trace := by
      apply Finset.sum_congr rfl
      intro e he
      exact P.fullOutput_trace hp0 hp1 _
    _ = ρ.trace := by
      change (∑ e, ∑ i : Fin a × Fin b, ρ (i, e) (i, e)) =
        ∑ x : (Fin a × Fin b) × E, ρ x x
      rw [Fintype.sum_prod_type]
      exact Finset.sum_comm

theorem withPriorEve_posSemidef {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {a b af bf : ℕ} (P : PhysicalProtocol.FiniteKeyProtocol p a b af bf) :
    ∀ (E : Type*) [Fintype E] [DecidableEq E]
      (ρ : Matrix ((Fin a × Fin b) × E) ((Fin a × Fin b) × E) ℂ),
      ρ.PosSemidef → (P.withPriorEve E ρ).PosSemidef := by
  classical
  induction P with
  | done a b =>
      intro E _ _ ρ hρ
      exact hρ.submatrix (fun x : (((Fin a × Fin b) × Unit) × E) => (x.1.1, x.2))
  | @alice a b ao af bf k C next ih =>
      intro E _ _ ρ hρ
      let L (z : Fin k) := C.op z ⊗ₖ (1 : Matrix (Fin b) (Fin b) ℂ)
      let S (z : Fin k) := (L z ⊗ₖ (1 : Matrix E E ℂ)) * ρ *
        (L z ⊗ₖ (1 : Matrix E E ℂ))ᴴ
      let M (z : Fin k) := (next z).withPriorEve E (S z)
      have hM (z : Fin k) : (M z).PosSemidef :=
        ih z E (S z) (hρ.mul_mul_conjTranspose_same
          (L z ⊗ₖ (1 : Matrix E E ℂ)))
      let f : (((Fin af × Fin bf) ×
          (PhysicalProtocol.FiniteKeyProtocol.alice C next).Environment) × E) →
          Σ z : Fin k, (((Fin af × Fin bf) × (next z).Environment) × E) :=
        fun x => ⟨x.1.2.1, ((x.1.1, x.1.2.2), x.2)⟩
      have heq : (PhysicalProtocol.FiniteKeyProtocol.alice C next).withPriorEve E ρ =
          (Matrix.blockDiagonal' M).submatrix f f := by
        ext x y
        rcases x with ⟨⟨x, ⟨z, t⟩⟩, e⟩
        rcases y with ⟨⟨y, ⟨z', u⟩⟩, e'⟩
        by_cases h : z = z'
        · subst z'
          simp [f, M, S, L, withPriorEve, fullOutput, Matrix.submatrix_apply,
            MemoryMatrix.congruence_withRightMemory_apply] <;> rfl
        · simp [f, M, withPriorEve, fullOutput, Matrix.submatrix_apply,
            Matrix.blockDiagonal'_apply, h]
      rw [heq]
      exact (MemoryMatrix.blockDiagonal'_posSemidef M hM).submatrix f
  | @bob a b bo af bf k C next ih =>
      intro E _ _ ρ hρ
      let L (z : Fin k) := (1 : Matrix (Fin a) (Fin a) ℂ) ⊗ₖ C.op z
      let S (z : Fin k) := (L z ⊗ₖ (1 : Matrix E E ℂ)) * ρ *
        (L z ⊗ₖ (1 : Matrix E E ℂ))ᴴ
      let M (z : Fin k) := (next z).withPriorEve E (S z)
      have hM (z : Fin k) : (M z).PosSemidef :=
        ih z E (S z) (hρ.mul_mul_conjTranspose_same
          (L z ⊗ₖ (1 : Matrix E E ℂ)))
      let f : (((Fin af × Fin bf) ×
          (PhysicalProtocol.FiniteKeyProtocol.bob C next).Environment) × E) →
          Σ z : Fin k, (((Fin af × Fin bf) × (next z).Environment) × E) :=
        fun x => ⟨x.1.2.1, ((x.1.1, x.1.2.2), x.2)⟩
      have heq : (PhysicalProtocol.FiniteKeyProtocol.bob C next).withPriorEve E ρ =
          (Matrix.blockDiagonal' M).submatrix f f := by
        ext x y
        rcases x with ⟨⟨x, ⟨z, t⟩⟩, e⟩
        rcases y with ⟨⟨y, ⟨z', u⟩⟩, e'⟩
        by_cases h : z = z'
        · subst z'
          simp [f, M, S, L, withPriorEve, fullOutput, Matrix.submatrix_apply,
            MemoryMatrix.congruence_withRightMemory_apply] <;> rfl
        · simp [f, M, withPriorEve, fullOutput, Matrix.submatrix_apply,
            Matrix.blockDiagonal'_apply, h]
      rw [heq]
      exact (MemoryMatrix.blockDiagonal'_posSemidef M hM).submatrix f
  | @call a b af bf next ih =>
      intro E _ _ ρ hρ
      let C := PhysicalProtocol.transferChannel p hp0 hp1 a b
      let S := ((C.stinespring ⊗ₖ (1 : Matrix E E ℂ)) * ρ *
        (C.stinespring ⊗ₖ (1 : Matrix E E ℂ))ᴴ).submatrix
          (Equiv.prodAssoc (Fin a × Fin (2 * b)) (Fin 2) E).symm
          (Equiv.prodAssoc (Fin a × Fin (2 * b)) (Fin 2) E).symm
      have hS : S.PosSemidef :=
        (hρ.mul_mul_conjTranspose_same
          (C.stinespring ⊗ₖ (1 : Matrix E E ℂ))).submatrix _
      let f : (((Fin af × Fin bf) ×
          (PhysicalProtocol.FiniteKeyProtocol.call next).Environment) × E) →
          (((Fin af × Fin bf) × next.Environment) × (Fin 2 × E)) :=
        fun x => ((x.1.1, x.1.2.2), (x.1.2.1, x.2))
      have heq : (PhysicalProtocol.FiniteKeyProtocol.call next).withPriorEve E ρ =
          (next.withPriorEve (Fin 2 × E) S).submatrix f f := by
        ext x y
        rcases x with ⟨⟨x, ⟨z, t⟩⟩, e⟩
        rcases y with ⟨⟨y, ⟨z', u⟩⟩, e'⟩
        have hblock : Matrix.of (fun i j => S (i, (z, e)) (j, (z', e'))) =
            PhysicalProtocol.transferKraus p a b z *
              Matrix.of (fun i j => ρ (i, e) (j, e')) *
              (PhysicalProtocol.transferKraus p a b z')ᴴ := by
          ext i j
          change (((C.stinespring ⊗ₖ (1 : Matrix E E ℂ)) * ρ *
            (C.stinespring ⊗ₖ (1 : Matrix E E ℂ))ᴴ) ((i, z), e) ((j, z'), e')) =
              (PhysicalProtocol.transferKraus p a b z *
                Matrix.of (fun i j => ρ (i, e) (j, e')) *
                (PhysicalProtocol.transferKraus p a b z')ᴴ) i j
          simpa only [C, PhysicalProtocol.transferChannel] using
            MemoryMatrix.jointCongruence_withRightMemory_apply C ρ i j z z' e e'
        simp only [f, withPriorEve, fullOutput, Matrix.submatrix_apply]
        change next.fullOutput (PhysicalProtocol.transferKraus p a b z *
          Matrix.of (fun i j => ρ (i, e) (j, e')) *
          (PhysicalProtocol.transferKraus p a b z')ᴴ) (x, t) (y, u) =
            next.fullOutput (Matrix.of (fun i j =>
              S (i, (z, e)) (j, (z', e')))) (x, t) (y, u)
        rw [hblock]
      rw [heq]
      exact (ih (Fin 2 × E) S hS).submatrix f

def onDensityWithPriorEve {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {a b af bf : ℕ} (P : PhysicalProtocol.FiniteKeyProtocol p a b af bf)
    (E : Type*) [Fintype E] [DecidableEq E]
    (ρ : Density ((Fin a × Fin b) × E)) :
    Density (((Fin af × Fin bf) × P.Environment) × E) where
  mat := P.withPriorEve E ρ.mat
  positive := P.withPriorEve_posSemidef hp0 hp1 E ρ.mat ρ.positive
  normalized := (P.withPriorEve_trace hp0 hp1 E ρ.mat).trans ρ.normalized

def onDensityWholeEve {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {a b af bf : ℕ} (P : PhysicalProtocol.FiniteKeyProtocol p a b af bf)
    (E : Type*) [Fintype E] [DecidableEq E]
    (ρ : Density ((Fin a × Fin b) × E)) :
    Density ((Fin af × Fin bf) × (P.Environment × E)) where
  mat := (P.onDensityWithPriorEve hp0 hp1 E ρ).mat.submatrix
    (Equiv.prodAssoc (Fin af × Fin bf) P.Environment E).symm
    (Equiv.prodAssoc (Fin af × Fin bf) P.Environment E).symm
  positive := (P.onDensityWithPriorEve hp0 hp1 E ρ).positive.submatrix _
  normalized := (MemoryMatrix.trace_submatrix_equiv
    (Equiv.prodAssoc (Fin af × Fin bf) P.Environment E).symm
    (P.onDensityWithPriorEve hp0 hp1 E ρ).mat).trans
      (P.onDensityWithPriorEve hp0 hp1 E ρ).normalized

def finalKeyStateWithPriorEve {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {a b d af bf : ℕ}
    (P : PhysicalProtocol.FiniteKeyProtocol p a b (d * af) (d * bf))
    (E : Type*) [Fintype E] [DecidableEq E]
    (ρ : Density ((Fin a × Fin b) × E)) :
    Density ((Fin d × Fin d) × (P.Environment × E)) := by
  classical
  exact privateKeyReadout d af bf (P.onDensityWholeEve hp0 hp1 E ρ)

def finalKeyStateWithPriorEveLabels {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {a b d af bf : ℕ}
    (P : PhysicalProtocol.FiniteKeyProtocol p a b af bf)
    (labelA : Fin af → Fin d) (labelB : Fin bf → Fin d)
    (E : Type*) [Fintype E] [DecidableEq E]
    (ρ : Density ((Fin a × Fin b) × E)) :
    Density ((Fin d × Fin d) × (P.Environment × E)) := by
  classical
  exact ((basisReadoutChannel (fun i : Fin af × Fin bf =>
    (labelA i.1, labelB i.2))).withRightMemory (P.Environment × E)).onDensity
      (P.onDensityWholeEve hp0 hp1 E ρ)

end PhysicalProtocol.FiniteKeyProtocol

namespace PrivateTest

def productVector {A B : Type*} [Fintype A] [Fintype B]
    (x : EuclideanSpace ℂ A) (y : EuclideanSpace ℂ B) :
    EuclideanSpace ℂ (A × B) :=
  WithLp.toLp 2 (fun ab => x ab.1 * y ab.2)

theorem norm_productVector_sq {A B : Type*} [Fintype A] [Fintype B]
    (x : EuclideanSpace ℂ A) (y : EuclideanSpace ℂ B) :
    ‖productVector x y‖ ^ 2 = ‖x‖ ^ 2 * ‖y‖ ^ 2 := by
  simp only [EuclideanSpace.norm_sq_eq, productVector, PiLp.toLp_apply,
    norm_mul, mul_pow, Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum]
  rw [← Finset.sum_mul]

theorem norm_productVector {A B : Type*} [Fintype A] [Fintype B]
    (x : EuclideanSpace ℂ A) (y : EuclideanSpace ℂ B) :
    ‖productVector x y‖ = ‖x‖ * ‖y‖ := by
  have h := norm_productVector_sq x y
  have hp : 0 ≤ ‖x‖ * ‖y‖ := mul_nonneg (norm_nonneg x) (norm_nonneg y)
  nlinarith [norm_nonneg (productVector x y)]

def keyBlock {K A : Type*} [Fintype K] [Fintype A]
    (x : EuclideanSpace ℂ (K × A)) (i : K) : EuclideanSpace ℂ A :=
  WithLp.toLp 2 (fun a => x (i, a))

theorem sum_keyBlock_norm_sq {K A : Type*} [Fintype K] [Fintype A]
    (x : EuclideanSpace ℂ (K × A)) :
    (∑ i, ‖keyBlock x i‖ ^ 2) = ‖x‖ ^ 2 := by
  simp only [EuclideanSpace.norm_sq_eq, keyBlock, PiLp.toLp_apply,
    Fintype.sum_prod_type]

def twistedProductAmplitude {K A B : Type*}
    [Fintype K] [Fintype A] [Fintype B]
    (U : K → EuclideanSpace ℂ (A × B) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (A × B))
    (x : EuclideanSpace ℂ (K × A)) (y : EuclideanSpace ℂ (K × B)) :
    EuclideanSpace ℂ (A × B) :=
  ∑ i, U i (productVector (keyBlock x i) (keyBlock y i))

theorem twistedProductAmplitude_norm_sq_le {K A B : Type*}
    [Fintype K] [Fintype A] [Fintype B]
    (U : K → EuclideanSpace ℂ (A × B) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (A × B))
    (x : EuclideanSpace ℂ (K × A)) (y : EuclideanSpace ℂ (K × B)) :
    ‖twistedProductAmplitude U x y‖ ^ 2 ≤ ‖x‖ ^ 2 * ‖y‖ ^ 2 := by
  have ht : ‖twistedProductAmplitude U x y‖ ≤
      ∑ i, ‖keyBlock x i‖ * ‖keyBlock y i‖ := by
    simpa only [twistedProductAmplitude, LinearIsometryEquiv.norm_map,
      norm_productVector] using norm_sum_le Finset.univ
        (fun i => U i (productVector (keyBlock x i) (keyBlock y i)))
  have hc := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun i => ‖keyBlock x i‖) (fun i => ‖keyBlock y i‖)
  rw [sum_keyBlock_norm_sq x, sum_keyBlock_norm_sq y] at hc
  have hn : 0 ≤ ∑ i, ‖keyBlock x i‖ * ‖keyBlock y i‖ := by positivity
  nlinarith [norm_nonneg (twistedProductAmplitude U x y)]

def twistedPureProductPass {d : ℕ} {A B : Type*} [Fintype A] [Fintype B]
    (U : Fin d → EuclideanSpace ℂ (A × B) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (A × B))
    (x : EuclideanSpace ℂ (Fin d × A)) (y : EuclideanSpace ℂ (Fin d × B)) : ℝ :=
  ‖twistedProductAmplitude U x y‖ ^ 2 / (d : ℝ)

theorem twistedPureProductPass_le {d : ℕ} {A B : Type*}
    [Fintype A] [Fintype B]
    (U : Fin d → EuclideanSpace ℂ (A × B) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (A × B))
    (x : EuclideanSpace ℂ (Fin d × A)) (y : EuclideanSpace ℂ (Fin d × B))
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    twistedPureProductPass U x y ≤ 1 / (d : ℝ) := by
  have h := twistedProductAmplitude_norm_sq_le U x y
  rw [hx, hy] at h
  simp only [one_pow, one_mul] at h
  exact div_le_div_of_nonneg_right h (Nat.cast_nonneg d)

end PrivateTest

end QuantumProver.AmplitudeDamping.SecretKey

noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix Kronecker

namespace QuantumProver.AmplitudeDamping.SecretKey.PrivateTest

def keyDiagonalSlice {K A B : Type*} [Fintype K] [Fintype A] [Fintype B]
    (i : K) : EuclideanSpace ℂ ((K × A) × (K × B)) →ₗ[ℂ]
      EuclideanSpace ℂ (A × B) where
  toFun v := WithLp.toLp 2 (fun ab => v ((i, ab.1), (i, ab.2)))
  map_add' v w := by ext ab; rfl
  map_smul' c v := by ext ab; rfl

def privacyLinearMap {K A B : Type*} [Fintype K] [Fintype A] [Fintype B]
    (U : K → EuclideanSpace ℂ (A × B) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (A × B)) :
    EuclideanSpace ℂ ((K × A) × (K × B)) →ₗ[ℂ] EuclideanSpace ℂ (A × B) :=
  ∑ i, (U i).toLinearEquiv.toLinearMap.comp (keyDiagonalSlice i)

theorem privacyLinearMap_apply {K A B : Type*}
    [Fintype K] [Fintype A] [Fintype B]
    (U : K → EuclideanSpace ℂ (A × B) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (A × B))
    (v : EuclideanSpace ℂ ((K × A) × (K × B))) :
    privacyLinearMap U v = ∑ i, U i (keyDiagonalSlice i v) := by
  simp only [privacyLinearMap, LinearMap.sum_apply, LinearMap.comp_apply] <;> rfl

theorem sum_keyDiagonalSlice_norm_sq_le {K A B : Type*}
    [Fintype K] [Fintype A] [Fintype B]
    (v : EuclideanSpace ℂ ((K × A) × (K × B))) :
    (∑ i, ‖keyDiagonalSlice i v‖ ^ 2) ≤ ‖v‖ ^ 2 := by
  classical
  simp only [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
  change (∑ i, ∑ a, ∑ b, ‖v ((i, a), (i, b))‖ ^ 2) ≤
    ∑ i, ∑ a, ∑ j, ∑ b, ‖v ((i, a), (j, b))‖ ^ 2
  apply Finset.sum_le_sum
  intro i hi
  apply Finset.sum_le_sum
  intro a ha
  exact Finset.single_le_sum
    (f := fun j : K => ∑ b : B, ‖v ((i, a), (j, b))‖ ^ 2)
    (fun j hj => by positivity) (Finset.mem_univ i)

theorem privacyLinearMap_norm_sq_le {d : ℕ} {A B : Type*}
    [Fintype A] [Fintype B]
    (U : Fin d → EuclideanSpace ℂ (A × B) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (A × B))
    (v : EuclideanSpace ℂ (((Fin d) × A) × ((Fin d) × B))) :
    ‖privacyLinearMap U v‖ ^ 2 ≤ (d : ℝ) * ‖v‖ ^ 2 := by
  have ht : ‖privacyLinearMap U v‖ ≤ ∑ i, ‖keyDiagonalSlice i v‖ := by
    rw [privacyLinearMap_apply]
    simpa only [LinearIsometryEquiv.norm_map] using
      norm_sum_le Finset.univ (fun i => U i (keyDiagonalSlice i v))
  have hc := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun _ : Fin d => (1 : ℝ)) (fun i => ‖keyDiagonalSlice i v‖)
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one] at hc
  have hd := mul_le_mul_of_nonneg_left (sum_keyDiagonalSlice_norm_sq_le v)
    (Nat.cast_nonneg d : (0 : ℝ) ≤ d)
  have hn : 0 ≤ ∑ i : Fin d, ‖keyDiagonalSlice i v‖ := by positivity
  nlinarith [norm_nonneg (privacyLinearMap U v)]

theorem privacyLinearMap_product {K A B : Type*}
    [Fintype K] [Fintype A] [Fintype B]
    (U : K → EuclideanSpace ℂ (A × B) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (A × B))
    (x : EuclideanSpace ℂ (K × A)) (y : EuclideanSpace ℂ (K × B)) :
    privacyLinearMap U (productVector x y) = twistedProductAmplitude U x y := by
  simp only [privacyLinearMap, LinearMap.sum_apply, LinearMap.comp_apply]
  change (∑ i, U i (keyDiagonalSlice i (productVector x y))) =
    ∑ i, U i (productVector (keyBlock x i) (keyBlock y i))
  apply Finset.sum_congr rfl
  intro i hi
  congr 1

def privacyMatrix {K A B : Type*}
    [Fintype K] [Fintype A] [Fintype B]
    [DecidableEq K] [DecidableEq A] [DecidableEq B]
    (U : K → EuclideanSpace ℂ (A × B) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (A × B)) :
    Matrix (A × B) ((K × A) × (K × B)) ℂ :=
  Matrix.toEuclideanLin.symm (privacyLinearMap U)

theorem privacyMatrix_product {K A B : Type*}
    [Fintype K] [Fintype A] [Fintype B]
    [DecidableEq K] [DecidableEq A] [DecidableEq B]
    (U : K → EuclideanSpace ℂ (A × B) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (A × B))
    (x : EuclideanSpace ℂ (K × A)) (y : EuclideanSpace ℂ (K × B)) :
    (privacyMatrix U).toEuclideanLin (productVector x y) =
      twistedProductAmplitude U x y := by
  simpa only [privacyMatrix, LinearEquiv.apply_symm_apply] using
    privacyLinearMap_product U x y

theorem traceGram_re {I : Type*} [Fintype I] (v : I → ℂ) :
    (Matrix.vecMulVec v (star v)).trace.re = ∑ i, Complex.normSq (v i) := by
  simp [Matrix.trace, Matrix.diag, Matrix.vecMulVec_apply, Complex.mul_re,
    Complex.normSq_apply, pow_two]

theorem traceGram_norm {I : Type*} [Fintype I] (v : I → ℂ) :
    (Matrix.vecMulVec v (star v)).trace.re =
      ‖(WithLp.toLp 2 v : EuclideanSpace ℂ I)‖ ^ 2 := by
  simp only [traceGram_re, EuclideanSpace.norm_sq_eq, PiLp.toLp_apply,
    Complex.normSq_eq_norm_sq]

theorem congruence_Gram_trace {I O : Type*} [Fintype I] [Fintype O]
    [DecidableEq I] (W : Matrix O I ℂ) (v : I → ℂ) :
    (W * Matrix.vecMulVec v (star v) * Wᴴ).trace.re =
      ‖W.toEuclideanLin (WithLp.toLp 2 v)‖ ^ 2 := by
  rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, ← Matrix.star_mulVec]
  change (Matrix.vecMulVec (W *ᵥ v) (star (W *ᵥ v))).trace.re =
    ‖(WithLp.toLp 2 (W *ᵥ v) : EuclideanSpace ℂ O)‖ ^ 2
  exact traceGram_norm (W *ᵥ v)

def privacyAcceptance {d : ℕ} {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (U : Fin d → EuclideanSpace ℂ (A × B) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (A × B))
    (M : Matrix ((Fin d × A) × (Fin d × B))
      ((Fin d × A) × (Fin d × B)) ℂ) : ℝ :=
  (privacyMatrix U * M * (privacyMatrix U)ᴴ).trace.re / (d : ℝ)

theorem privacyAcceptance_sum {d : ℕ} {A B Z : Type*}
    [Fintype A] [Fintype B] [Fintype Z] [DecidableEq A] [DecidableEq B]
    (U : Fin d → EuclideanSpace ℂ (A × B) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (A × B))
    (M : Z → Matrix ((Fin d × A) × (Fin d × B))
      ((Fin d × A) × (Fin d × B)) ℂ) :
    privacyAcceptance U (∑ z, M z) = ∑ z, privacyAcceptance U (M z) := by
  simp [privacyAcceptance, Matrix.mul_sum, Matrix.sum_mul, Matrix.trace_sum,
    Complex.re_sum, Finset.sum_div]

theorem Gram_product_matrix {A B : Type*} [Fintype A] [Fintype B]
    (u : A → ℂ) (v : B → ℂ) :
    Matrix.vecMulVec u (star u) ⊗ₖ Matrix.vecMulVec v (star v) =
      Matrix.vecMulVec (fun x : A × B => u x.1 * v x.2)
        (star (fun x : A × B => u x.1 * v x.2)) := by
  ext x y
  simp [Matrix.kroneckerMap_apply, Matrix.vecMulVec_apply,
    mul_assoc, mul_comm, mul_left_comm]

theorem privacyAcceptance_Gram_product_le {d : ℕ} {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (U : Fin d → EuclideanSpace ℂ (A × B) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (A × B))
    (u : Fin d × A → ℂ) (v : Fin d × B → ℂ) :
    privacyAcceptance U (Matrix.vecMulVec u (star u) ⊗ₖ
      Matrix.vecMulVec v (star v)) ≤
        ‖(WithLp.toLp 2 u : EuclideanSpace ℂ (Fin d × A))‖ ^ 2 *
        ‖(WithLp.toLp 2 v : EuclideanSpace ℂ (Fin d × B))‖ ^ 2 / (d : ℝ) := by
  rw [Gram_product_matrix, privacyAcceptance, congruence_Gram_trace]
  change ‖(privacyMatrix U).toEuclideanLin
    (productVector (WithLp.toLp 2 u) (WithLp.toLp 2 v))‖ ^ 2 / (d : ℝ) ≤ _
  rw [privacyMatrix_product]
  exact div_le_div_of_nonneg_right
    (twistedProductAmplitude_norm_sq_le U (WithLp.toLp 2 u) (WithLp.toLp 2 v))
    (Nat.cast_nonneg d)

theorem privacyAcceptance_product_psd_le {d : ℕ} {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (U : Fin d → EuclideanSpace ℂ (A × B) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (A × B))
    {M : Matrix (Fin d × A) (Fin d × A) ℂ}
    {N : Matrix (Fin d × B) (Fin d × B) ℂ}
    (hM : M.PosSemidef) (hN : N.PosSemidef) :
    privacyAcceptance U (M ⊗ₖ N) ≤ M.trace.re * N.trace.re / (d : ℝ) := by
  obtain ⟨m, u, hu⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp hM
  obtain ⟨n, v, hv⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp hN
  have hnu : (∑ i : Fin m,
      ‖(WithLp.toLp 2 (u i) : EuclideanSpace ℂ (Fin d × A))‖ ^ 2) = M.trace.re := by
    rw [hu, Matrix.trace_sum, Complex.re_sum]
    simp only [traceGram_norm]
  have hnv : (∑ j : Fin n,
      ‖(WithLp.toLp 2 (v j) : EuclideanSpace ℂ (Fin d × B))‖ ^ 2) = N.trace.re := by
    rw [hv, Matrix.trace_sum, Complex.re_sum]
    simp only [traceGram_norm]
  have hp : M ⊗ₖ N = ∑ i : Fin m, ∑ j : Fin n,
      Matrix.vecMulVec (u i) (star (u i)) ⊗ₖ
        Matrix.vecMulVec (v j) (star (v j)) := by
    rw [hu, hv]
    ext x y
    simp [Matrix.sum_apply, Matrix.kroneckerMap_apply, Finset.mul_sum,
      Finset.sum_mul]
    exact Finset.sum_comm
  rw [hp, privacyAcceptance_sum]
  simp_rw [privacyAcceptance_sum]
  calc
    _ ≤ ∑ i : Fin m, ∑ j : Fin n,
        ‖(WithLp.toLp 2 (u i) : EuclideanSpace ℂ (Fin d × A))‖ ^ 2 *
        ‖(WithLp.toLp 2 (v j) : EuclideanSpace ℂ (Fin d × B))‖ ^ 2 / (d : ℝ) := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      exact privacyAcceptance_Gram_product_le U (u i) (v j)
    _ = M.trace.re * N.trace.re / (d : ℝ) := by
      simp only [← Finset.sum_div, ← Finset.mul_sum, ← Finset.sum_mul, hnu, hnv]

theorem psd_trace_kronecker_re {A B : Type*} [Fintype A] [Fintype B]
    {M : Matrix A A ℂ} {N : Matrix B B ℂ}
    (hM : M.PosSemidef) (hN : N.PosSemidef) :
    (M ⊗ₖ N).trace.re = M.trace.re * N.trace.re := by
  have hMi : M.trace.im = 0 := (Complex.nonneg_iff.mp hM.trace_nonneg).2.symm
  have hNi : N.trace.im = 0 := (Complex.nonneg_iff.mp hN.trace_nonneg).2.symm
  rw [Matrix.trace_kronecker, Complex.mul_re, hMi, hNi]
  ring

theorem privacyAcceptance_separableCone_le {d : ℕ} {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (U : Fin d → EuclideanSpace ℂ (A × B) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (A × B))
    {M : Matrix ((Fin d × A) × (Fin d × B))
      ((Fin d × A) × (Fin d × B)) ℂ} (hM : InSeparableCone M) :
    privacyAcceptance U M ≤ M.trace.re / (d : ℝ) := by
  obtain ⟨k, left, right, hl, hr, rfl⟩ := hM
  rw [privacyAcceptance_sum]
  have htrace : (∑ j : Fin k, left j ⊗ₖ right j).trace.re =
      ∑ j : Fin k, (left j).trace.re * (right j).trace.re := by
    rw [Matrix.trace_sum, Complex.re_sum]
    apply Finset.sum_congr rfl
    intro j hj
    exact psd_trace_kronecker_re (hl j) (hr j)
  rw [htrace, Finset.sum_div]
  apply Finset.sum_le_sum
  intro j hj
  exact privacyAcceptance_product_psd_le U (hl j) (hr j)

theorem privacyAcceptance_separable_le {d : ℕ} {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (U : Fin d → EuclideanSpace ℂ (A × B) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (A × B))
    (ρ : Density ((Fin d × A) × (Fin d × B))) (hρ : IsSeparable ρ) :
    privacyAcceptance U ρ.mat ≤ 1 / (d : ℝ) := by
  have h := privacyAcceptance_separableCone_le U hρ
  simpa only [ρ.normalized, Complex.one_re] using h

theorem privacyAcceptance_Gram_nonneg {d : ℕ} {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (U : Fin d → EuclideanSpace ℂ (A × B) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (A × B))
    (v : (Fin d × A) × (Fin d × B) → ℂ) :
    0 ≤ privacyAcceptance U (Matrix.vecMulVec v (star v)) := by
  rw [privacyAcceptance, congruence_Gram_trace]
  exact div_nonneg (sq_nonneg _) (Nat.cast_nonneg d)

theorem privacyAcceptance_Gram_le_trace {d : ℕ} {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (U : Fin d → EuclideanSpace ℂ (A × B) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (A × B))
    (hd : 0 < d) (v : (Fin d × A) × (Fin d × B) → ℂ) :
    privacyAcceptance U (Matrix.vecMulVec v (star v)) ≤
      (Matrix.vecMulVec v (star v)).trace.re := by
  rw [privacyAcceptance, congruence_Gram_trace, traceGram_norm]
  have hp : (privacyMatrix U).toEuclideanLin = privacyLinearMap U := by
    simp only [privacyMatrix, LinearEquiv.apply_symm_apply]
  rw [hp]
  apply (div_le_iff₀ (Nat.cast_pos.mpr hd : (0 : ℝ) < d)).2
  simpa only [mul_comm] using privacyLinearMap_norm_sq_le U (WithLp.toLp 2 v)

theorem privacyAcceptance_posSemidef_nonneg {d : ℕ} {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (U : Fin d → EuclideanSpace ℂ (A × B) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (A × B))
    {M : Matrix ((Fin d × A) × (Fin d × B))
      ((Fin d × A) × (Fin d × B)) ℂ} (hM : M.PosSemidef) :
    0 ≤ privacyAcceptance U M := by
  obtain ⟨n, v, rfl⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp hM
  rw [privacyAcceptance_sum]
  exact Finset.sum_nonneg fun j _ => privacyAcceptance_Gram_nonneg U (v j)

theorem privacyAcceptance_posSemidef_le_trace {d : ℕ} {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (U : Fin d → EuclideanSpace ℂ (A × B) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (A × B))
    (hd : 0 < d) {M : Matrix ((Fin d × A) × (Fin d × B))
      ((Fin d × A) × (Fin d × B)) ℂ} (hM : M.PosSemidef) :
    privacyAcceptance U M ≤ M.trace.re := by
  obtain ⟨n, v, rfl⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp hM
  rw [privacyAcceptance_sum, Matrix.trace_sum, Complex.re_sum]
  exact Finset.sum_le_sum fun j _ => privacyAcceptance_Gram_le_trace U hd (v j)

theorem privacyAcceptance_density_mem_Icc {d : ℕ} {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (U : Fin d → EuclideanSpace ℂ (A × B) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (A × B))
    (hd : 0 < d) (ρ : Density ((Fin d × A) × (Fin d × B))) :
    privacyAcceptance U ρ.mat ∈ Set.Icc (0 : ℝ) 1 := by
  refine ⟨privacyAcceptance_posSemidef_nonneg U ρ.positive, ?_⟩
  simpa only [ρ.normalized, Complex.one_re] using
    privacyAcceptance_posSemidef_le_trace U hd ρ.positive

def privacyEffect {d : ℕ} {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (U : Fin d → EuclideanSpace ℂ (A × B) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (A × B)) :
    Matrix ((Fin d × A) × (Fin d × B)) ((Fin d × A) × (Fin d × B)) ℂ :=
  (1 / (d : ℝ)) • ((privacyMatrix U)ᴴ * privacyMatrix U)

theorem privacyEffect_posSemidef {d : ℕ} {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (U : Fin d → EuclideanSpace ℂ (A × B) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (A × B)) :
    (privacyEffect U).PosSemidef :=
  (Matrix.posSemidef_conjTranspose_mul_self (privacyMatrix U)).smul
    (div_nonneg zero_le_one (Nat.cast_nonneg d) : (0 : ℝ) ≤ 1 / d)

theorem privacyEffect_trace {d : ℕ} {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (U : Fin d → EuclideanSpace ℂ (A × B) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (A × B))
    (M : Matrix ((Fin d × A) × (Fin d × B))
      ((Fin d × A) × (Fin d × B)) ℂ) :
    (privacyEffect U * M).trace.re = privacyAcceptance U M := by
  rw [privacyEffect, Matrix.smul_mul, Matrix.trace_smul, Complex.smul_re,
    Matrix.trace_mul_cycle, Matrix.trace_mul_cycle]
  simp only [privacyAcceptance, one_div, div_eq_mul_inv, mul_comm,
    mul_one, smul_eq_mul]

theorem trace_mul_Gram {I : Type*} [Fintype I]
    (M : Matrix I I ℂ) (v : I → ℂ) :
    (M * Matrix.vecMulVec v (star v)).trace = star v ⬝ᵥ (M *ᵥ v) := by
  rw [Matrix.mul_vecMulVec, Matrix.trace_vecMulVec, dotProduct_comm]

theorem privacyEffect_complement_posSemidef {d : ℕ} {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (U : Fin d → EuclideanSpace ℂ (A × B) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (A × B))
    (hd : 0 < d) : (1 - privacyEffect U).PosSemidef := by
  have hH : (1 - privacyEffect U).IsHermitian :=
    Matrix.isHermitian_one.sub (privacyEffect_posSemidef U).isHermitian
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hH
  intro v
  have hre : 0 ≤ (star v ⬝ᵥ ((1 - privacyEffect U) *ᵥ v)).re := by
    rw [← trace_mul_Gram, Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub,
      Complex.sub_re, privacyEffect_trace]
    exact sub_nonneg.mpr (privacyAcceptance_Gram_le_trace U hd v)
  have him : (star v ⬝ᵥ ((1 - privacyEffect U) *ᵥ v)).im = 0 := by
    have hs := congrArg Complex.im (hH.star_dotProduct_mulVec_comm v v)
    simp only [Complex.star_def, Complex.conj_im] at hs
    linarith
  exact Complex.nonneg_iff.mpr ⟨hre, him.symm⟩

def unitaryMatrix {S : Type*} [Fintype S] [DecidableEq S]
    (U : EuclideanSpace ℂ S ≃ₗᵢ[ℂ] EuclideanSpace ℂ S) : Matrix S S ℂ :=
  Matrix.toEuclideanLin.symm U.toLinearEquiv.toLinearMap

theorem unitaryMatrix_action {S : Type*} [Fintype S] [DecidableEq S]
    (U : EuclideanSpace ℂ S ≃ₗᵢ[ℂ] EuclideanSpace ℂ S)
    (v : EuclideanSpace ℂ S) : (unitaryMatrix U).toEuclideanLin v = U v := by
  simp only [unitaryMatrix, LinearEquiv.apply_symm_apply] <;> rfl

theorem unitaryMatrix_mem_unitary {S : Type*} [Fintype S] [DecidableEq S]
    (U : EuclideanSpace ℂ S ≃ₗᵢ[ℂ] EuclideanSpace ℂ S) :
    unitaryMatrix U ∈ Matrix.unitaryGroup S ℂ := by
  change U.toMatrix (EuclideanSpace.basisFun S ℂ).toBasis
    (EuclideanSpace.basisFun S ℂ).toBasis ∈ Matrix.unitaryGroup S ℂ
  exact U.toMatrix_mem_unitaryGroup (EuclideanSpace.basisFun S ℂ)
    (EuclideanSpace.basisFun S ℂ)

def privacyMatrixByEntries {d : ℕ} {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (U : Fin d → EuclideanSpace ℂ (A × B) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (A × B)) :
    Matrix (A × B) ((Fin d × A) × (Fin d × B)) ℂ :=
  Matrix.of fun s r =>
    if r.1.1 = r.2.1 then unitaryMatrix (U r.1.1) s (r.1.2, r.2.2) else 0

theorem privacyMatrixByEntries_toEuclideanLin {d : ℕ} {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (U : Fin d → EuclideanSpace ℂ (A × B) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (A × B)) :
    (privacyMatrixByEntries U).toEuclideanLin = privacyLinearMap U := by
  ext v s
  simp_rw [privacyLinearMap_apply, ← unitaryMatrix_action]
  simp [privacyMatrixByEntries, Matrix.toLpLin_apply, Matrix.of_apply,
    Matrix.mulVec, dotProduct, Fintype.sum_prod_type, keyDiagonalSlice,
    WithLp.ofLp_sum, Finset.sum_apply, ite_mul]

theorem privacyMatrix_eq_entries {d : ℕ} {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (U : Fin d → EuclideanSpace ℂ (A × B) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (A × B)) :
    privacyMatrix U = privacyMatrixByEntries U := by
  apply Matrix.toEuclideanLin.injective
  rw [privacyMatrixByEntries_toEuclideanLin]
  simp only [privacyMatrix, LinearEquiv.apply_symm_apply]

theorem privacyMatrix_mul_conjTranspose {d : ℕ} {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (U : Fin d → EuclideanSpace ℂ (A × B) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (A × B)) :
    privacyMatrix U * (privacyMatrix U)ᴴ =
      (d : ℂ) • (1 : Matrix (A × B) (A × B) ℂ) := by
  have hU (i : Fin d) : unitaryMatrix (U i) * (unitaryMatrix (U i))ᴴ = 1 :=
    Matrix.mem_unitaryGroup_iff.mp (unitaryMatrix_mem_unitary (U i))
  rw [privacyMatrix_eq_entries]
  ext s t
  have hs : (privacyMatrixByEntries U * (privacyMatrixByEntries U)ᴴ) s t =
      ∑ i : Fin d, (unitaryMatrix (U i) * (unitaryMatrix (U i))ᴴ) s t := by
    simp [privacyMatrixByEntries, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fintype.sum_prod_type, apply_ite, ite_mul, mul_ite]
  rw [hs]
  simp only [hU, Matrix.smul_apply, smul_eq_mul]
  simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

def twistedPrivateDensity {d : ℕ} {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (U : Fin d → EuclideanSpace ℂ (A × B) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (A × B))
    (hd : 0 < d) (ω : Density (A × B)) :
    Density ((Fin d × A) × (Fin d × B)) where
  mat := (1 / (d : ℝ)) • ((privacyMatrix U)ᴴ * ω.mat * privacyMatrix U)
  positive := (ω.positive.conjTranspose_mul_mul_same (privacyMatrix U)).smul
    (div_nonneg zero_le_one (Nat.cast_nonneg d) : (0 : ℝ) ≤ 1 / d)
  normalized := by
    rw [Matrix.trace_smul, Matrix.trace_mul_cycle,
      privacyMatrix_mul_conjTranspose, Matrix.smul_mul, Matrix.one_mul,
      Matrix.trace_smul, ω.normalized]
    have hdz : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
    simp [smul_eq_mul, Complex.real_smul, hdz]

theorem privacyAcceptance_twistedPrivateDensity {d : ℕ} {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (U : Fin d → EuclideanSpace ℂ (A × B) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (A × B))
    (hd : 0 < d) (ω : Density (A × B)) :
    privacyAcceptance U (twistedPrivateDensity U hd ω).mat = 1 := by
  let W := privacyMatrix U
  have hWW : W * Wᴴ = (d : ℂ) • (1 : Matrix (A × B) (A × B) ℂ) :=
    privacyMatrix_mul_conjTranspose U
  have hcong : W * (Wᴴ * ω.mat * W) * Wᴴ = (W * Wᴴ) * ω.mat * (W * Wᴴ) := by
    simp only [Matrix.mul_assoc]
  change ((W * ((1 / (d : ℝ)) • (Wᴴ * ω.mat * W)) * Wᴴ).trace.re / (d : ℝ)) = 1
  rw [Matrix.mul_smul, Matrix.smul_mul, hcong, hWW, Matrix.smul_mul,
    Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul,
    Matrix.trace_smul, Matrix.trace_smul, ω.normalized]
  have hdz : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
  simp [Complex.smul_re, smul_eq_mul, Complex.mul_re, Complex.mul_im] <;>
    field_simp [hdz]

def privateEmbeddingMatrix {d : ℕ} {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (U : Fin d → EuclideanSpace ℂ (A × B) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (A × B)) :
    Matrix ((Fin d × A) × (Fin d × B)) (A × B) ℂ :=
  ((Real.sqrt (d : ℝ))⁻¹ : ℂ) • (privacyMatrix U)ᴴ

theorem privateEmbeddingMatrix_isometry {d : ℕ} {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (U : Fin d → EuclideanSpace ℂ (A × B) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (A × B))
    (hd : 0 < d) : (privateEmbeddingMatrix U)ᴴ * privateEmbeddingMatrix U = 1 := by
  have hdp : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have hsq : (Real.sqrt (d : ℝ) : ℂ) * (Real.sqrt (d : ℝ) : ℂ) = (d : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hdp.le]
    norm_cast
  have hsz : (Real.sqrt (d : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr hdp).ne'
  have hscale : ((Real.sqrt (d : ℝ))⁻¹ : ℂ) *
      ((Real.sqrt (d : ℝ))⁻¹ : ℂ) * (d : ℂ) = 1 := by
    push_cast
    rw [← hsq]
    field_simp
  rw [privateEmbeddingMatrix, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_conjTranspose, Matrix.smul_mul, Matrix.mul_smul,
    privacyMatrix_mul_conjTranspose]
  simp [Complex.real_smul, smul_smul, ← mul_assoc, hscale]

def privateEmbeddingChannel {d : ℕ} {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (U : Fin d → EuclideanSpace ℂ (A × B) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (A × B))
    (hd : 0 < d) : KrausChannel (A × B) ((Fin d × A) × (Fin d × B)) (Fin 1) where
  op := fun _ => privateEmbeddingMatrix U
  complete := by simpa using privateEmbeddingMatrix_isometry U hd

def twistedPrivateDensityWithEve {d : ℕ} {A B E : Type*}
    [Fintype A] [Fintype B] [Fintype E]
    [DecidableEq A] [DecidableEq B] [DecidableEq E]
    (U : Fin d → EuclideanSpace ℂ (A × B) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (A × B))
    (hd : 0 < d) (ω : Density ((A × B) × E)) :
    Density (((Fin d × A) × (Fin d × B)) × E) :=
  ((privateEmbeddingChannel U hd).withRightMemory E).onDensity ω

theorem twistedPrivateDensityWithEve_marginal {d : ℕ} {A B E : Type*}
    [Fintype A] [Fintype B] [Fintype E]
    [DecidableEq A] [DecidableEq B] [DecidableEq E]
    (U : Fin d → EuclideanSpace ℂ (A × B) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (A × B))
    (hd : 0 < d) (ω : Density ((A × B) × E)) :
    partialTraceLeft (twistedPrivateDensityWithEve U hd ω).mat =
      partialTraceLeft ω.mat := by
  exact partialTraceLeft_eval_withRightMemory (privateEmbeddingChannel U hd) ω.mat

def twistedPrivateKeyStateWithEve {d : ℕ} {A B E : Type*}
    [Fintype A] [Fintype B] [Fintype E]
    [DecidableEq A] [DecidableEq B] [DecidableEq E]
    (U : Fin d → EuclideanSpace ℂ (A × B) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (A × B))
    (hd : 0 < d) (ω : Density ((A × B) × E)) :
    Density ((Fin d × Fin d) × E) :=
  ((basisReadoutChannel (fun r : (Fin d × A) × (Fin d × B) =>
    (r.1.1, r.2.1))).withRightMemory E).onDensity
      (twistedPrivateDensityWithEve U hd ω)

theorem twistedPrivateKeyStateWithEve_isCCQ {d : ℕ} {A B E : Type*}
    [Fintype A] [Fintype B] [Fintype E]
    [DecidableEq A] [DecidableEq B] [DecidableEq E]
    (U : Fin d → EuclideanSpace ℂ (A × B) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (A × B))
    (hd : 0 < d) (ω : Density ((A × B) × E)) :
    IsCCQ (twistedPrivateKeyStateWithEve U hd ω) :=
  privateLabelReadout_isCCQ (fun r : (Fin d × A) × (Fin d × B) =>
    (r.1.1, r.2.1)) (twistedPrivateDensityWithEve U hd ω)

theorem twistedPrivateKeyStateWithEve_marginal {d : ℕ} {A B E : Type*}
    [Fintype A] [Fintype B] [Fintype E]
    [DecidableEq A] [DecidableEq B] [DecidableEq E]
    (U : Fin d → EuclideanSpace ℂ (A × B) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (A × B))
    (hd : 0 < d) (ω : Density ((A × B) × E)) :
    partialTraceLeft (twistedPrivateKeyStateWithEve U hd ω).mat =
      partialTraceLeft ω.mat := by
  change partialTraceLeft (((basisReadoutChannel
    (fun r : (Fin d × A) × (Fin d × B) => (r.1.1, r.2.1))).withRightMemory E).eval
      (twistedPrivateDensityWithEve U hd ω).mat) = partialTraceLeft ω.mat
  rw [partialTraceLeft_eval_withRightMemory, twistedPrivateDensityWithEve_marginal]

end QuantumProver.AmplitudeDamping.SecretKey.PrivateTest

noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix Kronecker

namespace QuantumProver.AmplitudeDamping.SecretKey.PrivateTest

theorem privacyEffect_eq_embeddingRange {d : ℕ} {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (U : Fin d → EuclideanSpace ℂ (A × B) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (A × B)) :
    privacyEffect U = privateEmbeddingMatrix U * (privateEmbeddingMatrix U)ᴴ := by
  have hcoef : ((Real.sqrt (d : ℝ))⁻¹ : ℂ) *
      ((Real.sqrt (d : ℝ))⁻¹ : ℂ) = ((1 / (d : ℝ) : ℝ) : ℂ) := by
    have hr : (Real.sqrt (d : ℝ))⁻¹ * (Real.sqrt (d : ℝ))⁻¹ =
        1 / (d : ℝ) := by
      rw [← mul_inv, Real.mul_self_sqrt (Nat.cast_nonneg d), one_div]
    exact_mod_cast hr
  rw [privateEmbeddingMatrix, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_conjTranspose, Matrix.smul_mul, Matrix.mul_smul]
  ext r s
  simp [privacyEffect, Matrix.smul_apply, smul_smul, Complex.real_smul,
    ← mul_assoc, hcoef]

theorem rangeEffect_projection {S R : Type*} [Fintype S] [Fintype R]
    [DecidableEq S] (V : Matrix R S ℂ) (hV : Vᴴ * V = 1) :
    (V * Vᴴ) * (V * Vᴴ) = V * Vᴴ := by
  calc
    _ = V * (Vᴴ * V) * Vᴴ := by simp only [Matrix.mul_assoc]
    _ = V * Vᴴ := by rw [hV, Matrix.mul_one]

theorem rangeEffect_embedding_pass {S R : Type*} [Fintype S] [Fintype R]
    [DecidableEq S] (V : Matrix R S ℂ) (hV : Vᴴ * V = 1) (ω : Density S) :
    ((V * Vᴴ) * (V * ω.mat * Vᴴ)).trace.re = 1 := by
  have hm : (V * Vᴴ) * (V * ω.mat * Vᴴ) = V * (Vᴴ * V) * ω.mat * Vᴴ := by
    simp only [Matrix.mul_assoc]
  rw [hm, hV, Matrix.mul_one, Matrix.trace_mul_cycle, hV,
    Matrix.one_mul, ω.normalized, Complex.one_re]

theorem partialTraceRight_kronecker_one_mul {I E : Type*}
    [Fintype I] [Fintype E] [DecidableEq E]
    (P : Matrix I I ℂ) (ρ : Matrix (I × E) (I × E) ℂ) :
    partialTraceRight ((P ⊗ₖ (1 : Matrix E E ℂ)) * ρ) =
      P * partialTraceRight ρ := by
  ext i j
  simpa [partialTraceRight, Matrix.mul_apply, Fintype.sum_prod_type,
    Matrix.kroneckerMap_apply, Matrix.one_apply, Finset.mul_sum] using
    (Finset.sum_comm : (∑ e : E, ∑ k : I, P i k * ρ (k,e) (j,e)) =
      ∑ k : I, ∑ e : E, P i k * ρ (k,e) (j,e))

theorem trace_mul_kronecker_one {I E : Type*}
    [Fintype I] [Fintype E] [DecidableEq E]
    (P : Matrix I I ℂ) (ρ : Matrix (I × E) (I × E) ℂ) :
    ((P ⊗ₖ (1 : Matrix E E ℂ)) * ρ).trace =
      (P * partialTraceRight ρ).trace := by
  rw [← trace_partialTraceRight, partialTraceRight_kronecker_one_mul]

def honestMarginal {I E : Type*} [Fintype I] [Fintype E]
    (ρ : Density (I × E)) : Density I where
  mat := partialTraceRight ρ.mat
  positive := partialTraceRight_posSemidef ρ.positive
  normalized := (trace_partialTraceRight ρ.mat).trans ρ.normalized

theorem privacyEffect_projection {d : ℕ} {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (U : Fin d → EuclideanSpace ℂ (A × B) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (A × B))
    (hd : 0 < d) : privacyEffect U * privacyEffect U = privacyEffect U := by
  rw [privacyEffect_eq_embeddingRange]
  exact rangeEffect_projection _ (privateEmbeddingMatrix_isometry U hd)

def privacyEffectWithEve {d : ℕ} {A B E : Type*}
    [Fintype A] [Fintype B] [Fintype E]
    [DecidableEq A] [DecidableEq B] [DecidableEq E]
    (U : Fin d → EuclideanSpace ℂ (A × B) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (A × B)) :
    Matrix (((Fin d × A) × (Fin d × B)) × E)
      (((Fin d × A) × (Fin d × B)) × E) ℂ :=
  privacyEffect U ⊗ₖ (1 : Matrix E E ℂ)

theorem privacyEffectWithEve_posSemidef {d : ℕ} {A B E : Type*}
    [Fintype A] [Fintype B] [Fintype E]
    [DecidableEq A] [DecidableEq B] [DecidableEq E]
    (U : Fin d → EuclideanSpace ℂ (A × B) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (A × B)) :
    (privacyEffectWithEve (E := E) U).PosSemidef :=
  (privacyEffect_posSemidef U).kronecker Matrix.PosSemidef.one

theorem privacyEffectWithEve_complement_posSemidef {d : ℕ} {A B E : Type*}
    [Fintype A] [Fintype B] [Fintype E]
    [DecidableEq A] [DecidableEq B] [DecidableEq E]
    (U : Fin d → EuclideanSpace ℂ (A × B) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (A × B))
    (hd : 0 < d) : (1 - privacyEffectWithEve (E := E) U).PosSemidef := by
  have heq : 1 - privacyEffectWithEve (E := E) U =
      (1 - privacyEffect U) ⊗ₖ (1 : Matrix E E ℂ) := by
    ext x y
    rcases x with ⟨x,e⟩
    rcases y with ⟨y,f⟩
    by_cases h : e = f <;>
      simp [privacyEffectWithEve, Matrix.kroneckerMap_apply, Matrix.sub_apply,
        Matrix.one_apply, Prod.mk.injEq, h]
  rw [heq]
  exact (privacyEffect_complement_posSemidef U hd).kronecker Matrix.PosSemidef.one

theorem privacyEffectWithEve_projection {d : ℕ} {A B E : Type*}
    [Fintype A] [Fintype B] [Fintype E]
    [DecidableEq A] [DecidableEq B] [DecidableEq E]
    (U : Fin d → EuclideanSpace ℂ (A × B) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (A × B))
    (hd : 0 < d) : privacyEffectWithEve (E := E) U *
      privacyEffectWithEve (E := E) U = privacyEffectWithEve (E := E) U := by
  rw [privacyEffectWithEve, ← Matrix.mul_kronecker_mul,
    privacyEffect_projection U hd, Matrix.one_mul]

theorem privacyEffectWithEve_trace {d : ℕ} {A B E : Type*}
    [Fintype A] [Fintype B] [Fintype E]
    [DecidableEq A] [DecidableEq B] [DecidableEq E]
    (U : Fin d → EuclideanSpace ℂ (A × B) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (A × B))
    (ρ : Matrix (((Fin d × A) × (Fin d × B)) × E)
      (((Fin d × A) × (Fin d × B)) × E) ℂ) :
    (privacyEffectWithEve (E := E) U * ρ).trace.re =
      privacyAcceptance U (partialTraceRight ρ) := by
  rw [privacyEffectWithEve, trace_mul_kronecker_one, privacyEffect_trace]

theorem privacyEffectWithEve_density_mem_Icc {d : ℕ} {A B E : Type*}
    [Fintype A] [Fintype B] [Fintype E]
    [DecidableEq A] [DecidableEq B] [DecidableEq E]
    (U : Fin d → EuclideanSpace ℂ (A × B) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (A × B))
    (hd : 0 < d) (ρ : Density (((Fin d × A) × (Fin d × B)) × E)) :
    (privacyEffectWithEve (E := E) U * ρ.mat).trace.re ∈ Set.Icc (0 : ℝ) 1 := by
  rw [privacyEffectWithEve_trace]
  exact privacyAcceptance_density_mem_Icc U hd (honestMarginal ρ)

theorem privacyEffectWithEve_separable_marginal_le {d : ℕ} {A B E : Type*}
    [Fintype A] [Fintype B] [Fintype E]
    [DecidableEq A] [DecidableEq B] [DecidableEq E]
    (U : Fin d → EuclideanSpace ℂ (A × B) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (A × B))
    (ρ : Density (((Fin d × A) × (Fin d × B)) × E))
    (hsep : InSeparableCone (partialTraceRight ρ.mat)) :
    (privacyEffectWithEve (E := E) U * ρ.mat).trace.re ≤ 1 / (d : ℝ) := by
  rw [privacyEffectWithEve_trace]
  exact privacyAcceptance_separable_le U (honestMarginal ρ) hsep

theorem privacyEffectWithEve_twistedPrivate_support {d : ℕ} {A B E : Type*}
    [Fintype A] [Fintype B] [Fintype E]
    [DecidableEq A] [DecidableEq B] [DecidableEq E]
    (U : Fin d → EuclideanSpace ℂ (A × B) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (A × B))
    (hd : 0 < d) (ω : Density ((A × B) × E)) :
    privacyEffectWithEve (E := E) U * (twistedPrivateDensityWithEve U hd ω).mat =
      (twistedPrivateDensityWithEve U hd ω).mat := by
  let V := privateEmbeddingMatrix U ⊗ₖ (1 : Matrix E E ℂ)
  have hV : Vᴴ * V = 1 := by
    dsimp only [V]
    rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
      ← Matrix.mul_kronecker_mul, privateEmbeddingMatrix_isometry U hd,
      Matrix.one_mul, Matrix.one_kronecker_one]
  have hP : privacyEffectWithEve (E := E) U = V * Vᴴ := by
    dsimp only [V]
    rw [privacyEffectWithEve, privacyEffect_eq_embeddingRange,
      Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
      ← Matrix.mul_kronecker_mul, Matrix.one_mul]
  have hρ : (twistedPrivateDensityWithEve U hd ω).mat = V * ω.mat * Vᴴ := by
    simp [twistedPrivateDensityWithEve, KrausChannel.onDensity,
      KrausChannel.eval, KrausChannel.withRightMemory, privateEmbeddingChannel, V]
  rw [hP, hρ]
  calc
    _ = V * (Vᴴ * V) * ω.mat * Vᴴ := by simp only [Matrix.mul_assoc]
    _ = V * ω.mat * Vᴴ := by rw [hV, Matrix.mul_one]

theorem privacyEffectWithEve_twistedPrivate_pass {d : ℕ} {A B E : Type*}
    [Fintype A] [Fintype B] [Fintype E]
    [DecidableEq A] [DecidableEq B] [DecidableEq E]
    (U : Fin d → EuclideanSpace ℂ (A × B) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (A × B))
    (hd : 0 < d) (ω : Density ((A × B) × E)) :
    (privacyEffectWithEve (E := E) U *
      (twistedPrivateDensityWithEve U hd ω).mat).trace.re = 1 := by
  let V := privateEmbeddingMatrix U ⊗ₖ (1 : Matrix E E ℂ)
  have hV : Vᴴ * V = 1 := by
    dsimp only [V]
    rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
      ← Matrix.mul_kronecker_mul, privateEmbeddingMatrix_isometry U hd,
      Matrix.one_mul, Matrix.one_kronecker_one]
  have hP : privacyEffectWithEve (E := E) U = V * Vᴴ := by
    dsimp only [V]
    rw [privacyEffectWithEve, privacyEffect_eq_embeddingRange,
      Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
      ← Matrix.mul_kronecker_mul, Matrix.one_mul]
  rw [hP]
  simpa only [twistedPrivateDensityWithEve, KrausChannel.onDensity,
    KrausChannel.eval, KrausChannel.withRightMemory, privateEmbeddingChannel,
    Fin.sum_univ_one, V] using rangeEffect_embedding_pass V hV ω

end QuantumProver.AmplitudeDamping.SecretKey.PrivateTest

noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix Kronecker

namespace QuantumProver.AmplitudeDamping.SecretKey.PrivateTest

def keyInjection {d : ℕ} {A B : Type*} (i : Fin d) (s : A × B) :
    (Fin d × A) × (Fin d × B) := ((i,s.1),(i,s.2))

theorem submatrix_sandwich_rows {I R T : Type*} [Fintype I]
    (V : Matrix R I ℂ) (M : Matrix I I ℂ) (r : T → R) :
    (V * M * Vᴴ).submatrix r r =
      V.submatrix r id * M * (V.submatrix r id)ᴴ := by
  ext i j
  rfl

theorem privateEmbeddingMatrix_keyBlock {d : ℕ} {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (U : Fin d → EuclideanSpace ℂ (A × B) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (A × B))
    (i : Fin d) :
    (privateEmbeddingMatrix U).submatrix (keyInjection i) id =
      ((Real.sqrt (d : ℝ))⁻¹ : ℂ) • (unitaryMatrix (U i))ᴴ := by
  ext s t
  simp [privateEmbeddingMatrix, privacyMatrix_eq_entries,
    privacyMatrixByEntries, keyInjection, Matrix.submatrix_apply,
    Matrix.smul_apply, Matrix.conjTranspose_apply, Matrix.of_apply]

theorem privateEmbeddingMatrix_keyBlock_gram {d : ℕ} {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (U : Fin d → EuclideanSpace ℂ (A × B) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (A × B))
    (i : Fin d) :
    ((privateEmbeddingMatrix U).submatrix (keyInjection i) id)ᴴ *
      (privateEmbeddingMatrix U).submatrix (keyInjection i) id =
      ((1 / (d : ℝ) : ℝ) : ℂ) • (1 : Matrix (A × B) (A × B) ℂ) := by
  have hU : unitaryMatrix (U i) * (unitaryMatrix (U i))ᴴ = 1 :=
    Matrix.mem_unitaryGroup_iff.mp (unitaryMatrix_mem_unitary (U i))
  have hcoef : ((Real.sqrt (d : ℝ))⁻¹ : ℂ) *
      ((Real.sqrt (d : ℝ))⁻¹ : ℂ) = ((1 / (d : ℝ) : ℝ) : ℂ) := by
    have hr : (Real.sqrt (d : ℝ))⁻¹ * (Real.sqrt (d : ℝ))⁻¹ =
        1 / (d : ℝ) := by
      rw [← mul_inv, Real.mul_self_sqrt (Nat.cast_nonneg d), one_div]
    exact_mod_cast hr
  rw [privateEmbeddingMatrix_keyBlock, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_conjTranspose, Matrix.smul_mul, Matrix.mul_smul, hU]
  simp [Complex.real_smul, smul_smul, hcoef]

theorem privateEmbeddingMatrix_keyBlock_trace {d : ℕ} {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (U : Fin d → EuclideanSpace ℂ (A × B) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (A × B))
    (i : Fin d) (M : Matrix (A × B) (A × B) ℂ) :
    ((privateEmbeddingMatrix U * M * (privateEmbeddingMatrix U)ᴴ).submatrix
      (keyInjection i) (keyInjection i)).trace =
      ((1 / (d : ℝ) : ℝ) : ℂ) * M.trace := by
  rw [submatrix_sandwich_rows, Matrix.trace_mul_cycle,
    privateEmbeddingMatrix_keyBlock_gram, Matrix.smul_mul,
    Matrix.one_mul, Matrix.trace_smul]
  rfl

theorem privateEmbeddingMatrix_unmatched_row_zero {d : ℕ} {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (U : Fin d → EuclideanSpace ℂ (A × B) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (A × B))
    (r : (Fin d × A) × (Fin d × B)) (h : r.1.1 ≠ r.2.1) (s : A × B) :
    privateEmbeddingMatrix U r s = 0 := by
  simp [privateEmbeddingMatrix, privacyMatrix_eq_entries,
    privacyMatrixByEntries, Matrix.conjTranspose_apply, Matrix.of_apply, h]

theorem privateEmbeddingMatrix_unmatched_diagonal_zero {d : ℕ} {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (U : Fin d → EuclideanSpace ℂ (A × B) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (A × B))
    (M : Matrix (A × B) (A × B) ℂ)
    (r : (Fin d × A) × (Fin d × B)) (h : r.1.1 ≠ r.2.1) :
    (privateEmbeddingMatrix U * M * (privateEmbeddingMatrix U)ᴴ) r r = 0 := by
  have hrow (s : A × B) : (privateEmbeddingMatrix U * M) r s = 0 := by
    simp [Matrix.mul_apply, privateEmbeddingMatrix_unmatched_row_zero U r h]
  simp [Matrix.mul_apply, hrow]

theorem basisReadoutChannel_diagonal {I O : Type*}
    [Fintype I] [Fintype O] [DecidableEq I] [DecidableEq O]
    (label : I → O) (M : Matrix I I ℂ) (x : O) :
    ((basisReadoutChannel label).eval M) x x =
      ∑ i, if label i = x then M i i else 0 := by
  rw [basisReadoutChannel_eval]
  simp only [Matrix.sum_apply, Matrix.single_apply, and_self]

theorem privateEmbedding_readout_linear {d : ℕ} {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (U : Fin d → EuclideanSpace ℂ (A × B) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (A × B))
    (hd : 0 < d) (M : Matrix (A × B) (A × B) ℂ) :
    (basisReadoutChannel (fun r : (Fin d × A) × (Fin d × B) =>
      (r.1.1,r.2.1))).eval
      (privateEmbeddingMatrix U * M * (privateEmbeddingMatrix U)ᴴ) =
      M.trace • (uniformKeyLaw d hd).copiedMatrix := by
  ext x y
  by_cases hxy : x = y
  · subst y
    have hdiag : (basisReadoutChannel
        (fun r : (Fin d × A) × (Fin d × B) => (r.1.1,r.2.1))).eval
        (privateEmbeddingMatrix U * M * (privateEmbeddingMatrix U)ᴴ) x x =
        ∑ a : A, ∑ b : B,
          (privateEmbeddingMatrix U * M * (privateEmbeddingMatrix U)ᴴ)
            ((x.1,a),(x.2,b)) ((x.1,a),(x.2,b)) := by
      rw [basisReadoutChannel_diagonal]
      rcases x with ⟨i,j⟩
      simp only [Fintype.sum_prod_type, Prod.mk.injEq, ite_and]
      simp_rw [Finset.sum_ite_irrel]
      simp [Finset.sum_ite_irrel]
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.sum_comm]
      simp
    rw [hdiag]
    by_cases hx : x.1 = x.2
    · have htrace : (∑ a : A, ∑ b : B,
          (privateEmbeddingMatrix U * M * (privateEmbeddingMatrix U)ᴴ)
            ((x.1,a),(x.2,b)) ((x.1,a),(x.2,b))) =
          ((1 / (d : ℝ) : ℝ) : ℂ) * M.trace := by
        simpa [Matrix.trace, Matrix.diag, Matrix.submatrix_apply,
          keyInjection, Fintype.sum_prod_type, hx] using
          privateEmbeddingMatrix_keyBlock_trace U x.1 M
      rw [htrace]
      simp [ProbabilityLaw.copiedMatrix, uniformKeyLaw, Matrix.smul_apply,
        Matrix.diagonal_apply, hx, mul_comm]
    · have hz (a : A) (b : B) :
          (privateEmbeddingMatrix U * M * (privateEmbeddingMatrix U)ᴴ)
            ((x.1,a),(x.2,b)) ((x.1,a),(x.2,b)) = 0 :=
          privateEmbeddingMatrix_unmatched_diagonal_zero U M
            ((x.1,a),(x.2,b)) hx
      simp [hz,
        ProbabilityLaw.copiedMatrix, uniformKeyLaw, Matrix.smul_apply,
        Matrix.diagonal_apply, hx]
  · rw [basisReadoutChannel_offdiagonal _ _ x y hxy]
    simp [ProbabilityLaw.copiedMatrix, Matrix.smul_apply,
      Matrix.diagonal_apply, hxy]

theorem privateEmbeddingChannel_eval {d : ℕ} {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (U : Fin d → EuclideanSpace ℂ (A × B) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (A × B))
    (hd : 0 < d) (M : Matrix (A × B) (A × B) ℂ) :
    (privateEmbeddingChannel U hd).eval M =
      privateEmbeddingMatrix U * M * (privateEmbeddingMatrix U)ᴴ := by
  simp only [KrausChannel.eval, privateEmbeddingChannel, Fin.sum_univ_one]

theorem twistedPrivateKeyStateWithEve_ideal {d : ℕ} {A B E : Type*}
    [Fintype A] [Fintype B] [Fintype E]
    [DecidableEq A] [DecidableEq B] [DecidableEq E]
    (U : Fin d → EuclideanSpace ℂ (A × B) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (A × B))
    (hd : 0 < d) (ω : Density ((A × B) × E)) :
    twistedPrivateKeyStateWithEve U hd ω =
      idealKeyStateAgainst d hd ω.marginalRight := by
  apply Density.eq_of_mat_eq
  ext p q
  rcases p with ⟨x,e⟩
  rcases q with ⟨y,e'⟩
  change ((basisReadoutChannel
    (fun r : (Fin d × A) × (Fin d × B) => (r.1.1,r.2.1))).withRightMemory E).eval
      (((privateEmbeddingChannel U hd).withRightMemory E).eval ω.mat) (x,e) (y,e') =
    ((uniformKeyLaw d hd).copiedMatrix ⊗ₖ partialTraceLeft ω.mat) (x,e) (y,e')
  rw [eval_withRightMemory_apply]
  have hslice : (Matrix.of (fun r s =>
      (((privateEmbeddingChannel U hd).withRightMemory E).eval ω.mat)
        (r,e) (s,e'))) =
      (privateEmbeddingChannel U hd).eval
        (Matrix.of (fun a b => ω.mat (a,e) (b,e'))) := by
    ext r s
    exact eval_withRightMemory_apply (privateEmbeddingChannel U hd) ω.mat r s e e'
  change ((basisReadoutChannel
    (fun r : (Fin d × A) × (Fin d × B) => (r.1.1,r.2.1))).eval
      (Matrix.of (fun r s =>
        (((privateEmbeddingChannel U hd).withRightMemory E).eval ω.mat)
          (r,e) (s,e')))) x y = _
  rw [hslice]
  rw [privateEmbeddingChannel_eval, privateEmbedding_readout_linear U hd]
  simp [Matrix.smul_apply, smul_eq_mul, Matrix.kroneckerMap_apply,
    partialTraceLeft, Matrix.trace, Matrix.diag, Matrix.of_apply, mul_comm]

end QuantumProver.AmplitudeDamping.SecretKey.PrivateTest

noncomputable section
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace QuantumProver.AmplitudeDamping.SecretKey.PurificationOrbit

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]

theorem norm_eq_of_gram (f g : E →ₗ[ℂ] F)
    (hGram : f.adjoint.comp f = g.adjoint.comp g) (v : E) : ‖f v‖ = ‖g v‖ := by
  have hInner : inner ℂ (f v) (f v) = inner ℂ (g v) (g v) := by
    calc
      _ = inner ℂ v ((f.adjoint.comp f) v) :=
        (LinearMap.adjoint_inner_right f v (f v)).symm
      _ = inner ℂ v ((g.adjoint.comp g) v) := by rw [hGram]
      _ = _ := LinearMap.adjoint_inner_right g v (g v)
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), norm_eq_sqrt_re_inner (𝕜 := ℂ), hInner]

theorem ker_le_of_norm_eq (f g : E →ₗ[ℂ] F)
    (hNorm : ∀ v, ‖f v‖ = ‖g v‖) : f.ker ≤ g.ker := by
  intro v hv
  rw [LinearMap.mem_ker] at hv ⊢
  have h := hNorm v
  rw [hv, norm_zero] at h
  exact norm_eq_zero.mp h.symm

def rangeFactor (f g : E →ₗ[ℂ] F) (hKer : f.ker ≤ g.ker) : f.range →ₗ[ℂ] F :=
  (f.ker.liftQ g hKer).comp f.quotKerEquivRange.symm.toLinearMap

theorem rangeFactor_apply (f g : E →ₗ[ℂ] F) (hKer : f.ker ≤ g.ker) (v : E) :
    rangeFactor f g hKer (f.rangeRestrict v) = g v := by
  change f.ker.liftQ g hKer
    (f.quotKerEquivRange.symm ⟨f v, LinearMap.mem_range_self f v⟩) = g v
  rw [LinearMap.quotKerEquivRange_symm_apply_image]
  rfl

def rangeIsometry (f g : E →ₗ[ℂ] F) (hNorm : ∀ v, ‖f v‖ = ‖g v‖) :
    f.range →ₗᵢ[ℂ] F where
  toLinearMap := rangeFactor f g (ker_le_of_norm_eq f g hNorm)
  norm_map' u := by
    rcases u with ⟨u, hu⟩
    rcases hu with ⟨v, rfl⟩
    change ‖rangeFactor f g (ker_le_of_norm_eq f g hNorm) (f.rangeRestrict v)‖ = ‖f v‖
    rw [rangeFactor_apply]
    exact (hNorm v).symm

theorem rangeIsometry_apply (f g : E →ₗ[ℂ] F)
    (hNorm : ∀ v, ‖f v‖ = ‖g v‖) (v : E) :
    rangeIsometry f g hNorm (f.rangeRestrict v) = g v :=
  rangeFactor_apply f g (ker_le_of_norm_eq f g hNorm) v

theorem exists_shield_unitary_of_norm_eq (f g : E →ₗ[ℂ] F)
    (hNorm : ∀ v, ‖f v‖ = ‖g v‖) :
    ∃ U : F ≃ₗᵢ[ℂ] F, ∀ v : E, U (f v) = g v := by
  let L := rangeIsometry f g hNorm
  let V := L.extend
  have hSurj : Function.Surjective V :=
    LinearMap.injective_iff_surjective.mp V.injective
  let U := LinearIsometryEquiv.ofSurjective V hSurj
  refine ⟨U, ?_⟩
  intro v
  change V (f v) = g v
  calc
    _ = L (f.rangeRestrict v) := L.extend_apply (f.rangeRestrict v)
    _ = g v := rangeIsometry_apply f g hNorm v

theorem exists_shield_unitary_of_gram (f g : E →ₗ[ℂ] F)
    (hGram : f.adjoint.comp f = g.adjoint.comp g) :
    ∃ U : F ≃ₗᵢ[ℂ] F, ∀ v : E, U (f v) = g v :=
  exists_shield_unitary_of_norm_eq f g (norm_eq_of_gram f g hGram)

section Matrix

variable {S J : Type*} [Fintype S] [Fintype J] [DecidableEq S] [DecidableEq J]

theorem toEuclideanLin_mul (A : Matrix S S ℂ) (B : Matrix S J ℂ) :
    (A * B).toEuclideanLin = A.toEuclideanLin.comp B.toEuclideanLin := by
  change (A * B).toLin (EuclideanSpace.basisFun J ℂ).toBasis
      (EuclideanSpace.basisFun S ℂ).toBasis =
    (A.toLin (EuclideanSpace.basisFun S ℂ).toBasis
      (EuclideanSpace.basisFun S ℂ).toBasis).comp
    (B.toLin (EuclideanSpace.basisFun J ℂ).toBasis
      (EuclideanSpace.basisFun S ℂ).toBasis)
  exact Matrix.toLin_mul _ _ _ A B

theorem toEuclideanLin_gram (A : Matrix S J ℂ) :
    (Aᴴ * A).toEuclideanLin = A.toEuclideanLin.adjoint.comp A.toEuclideanLin := by
  rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
  exact Matrix.toLin_mul (EuclideanSpace.basisFun J ℂ).toBasis
    (EuclideanSpace.basisFun S ℂ).toBasis (EuclideanSpace.basisFun J ℂ).toBasis Aᴴ A

theorem exists_unitary_matrix_of_equal_gram (A B : Matrix S J ℂ)
    (hGram : Aᴴ * A = Bᴴ * B) :
    ∃ U : Matrix S S ℂ, U ∈ Matrix.unitaryGroup S ℂ ∧ U * A = B := by
  have hLin : A.toEuclideanLin.adjoint.comp A.toEuclideanLin =
      B.toEuclideanLin.adjoint.comp B.toEuclideanLin := by
    rw [← toEuclideanLin_gram, ← toEuclideanLin_gram, hGram]
  obtain ⟨W, hW⟩ := exists_shield_unitary_of_gram A.toEuclideanLin B.toEuclideanLin hLin
  refine ⟨PrivateTest.unitaryMatrix W, PrivateTest.unitaryMatrix_mem_unitary W, ?_⟩
  apply Matrix.toEuclideanLin.injective
  rw [toEuclideanLin_mul]
  apply LinearMap.ext
  intro v
  change (PrivateTest.unitaryMatrix W).toEuclideanLin (A.toEuclideanLin v) = B.toEuclideanLin v
  rw [PrivateTest.unitaryMatrix_action]
  exact hW v

end Matrix

section Polar

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem exists_unitary_polar (M : Matrix I I ℂ) :
    ∃ U : Matrix I I ℂ, U ∈ Matrix.unitaryGroup I ℂ ∧ U * M = CFC.abs M := by
  have hAbs : (CFC.abs M)ᴴ = CFC.abs M := (CFC.abs_nonneg M).posSemidef.isHermitian
  have hGram : Mᴴ * M = (CFC.abs M)ᴴ * CFC.abs M := by
    rw [hAbs]
    simpa only [star_eq_conjTranspose] using (CFC.abs_mul_abs M).symm
  exact exists_unitary_matrix_of_equal_gram M (CFC.abs M) hGram

theorem exists_unitary_traceNorm_attainer (M : Matrix I I ℂ) :
    ∃ U : Matrix I I ℂ, U ∈ Matrix.unitaryGroup I ℂ ∧
      (U * M).trace.re = traceNorm M := by
  obtain ⟨U, hU, hUM⟩ := exists_unitary_polar M
  exact ⟨U, hU, by rw [hUM]; rfl⟩

theorem re_trace_isometry_mul_le {S H : Matrix I I ℂ}
    (hS : Sᴴ * S = 1) (hH : H.PosSemidef) :
    (S * H).trace.re ≤ H.trace.re := by
  let R := CFC.sqrt H
  have hR : Rᴴ = R := (CFC.sqrt_nonneg H).posSemidef.isHermitian
  have hRR : R * R = H := CFC.sqrt_mul_sqrt_self H hH.nonneg
  have hHH : Hᴴ = H := hH.isHermitian
  have hExpand : (1 - S)ᴴ * (1 - S) = 1 + 1 - Sᴴ - S := by
    simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_one,
      Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hS]
    noncomm_ring
  let Z := (1 - S) * R
  have hGram : Zᴴ * Z = H + H - R * Sᴴ * R - R * S * R := by
    calc
      _ = R * ((1 - S)ᴴ * (1 - S)) * R := by
        simp only [Z, Matrix.conjTranspose_mul, hR, Matrix.mul_assoc]
      _ = _ := by
        rw [hExpand]
        simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_add,
          Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, hRR]
  have hCycle (A : Matrix I I ℂ) : (R * A * R).trace = (A * H).trace := by
    rw [Matrix.trace_mul_cycle, hRR, Matrix.trace_mul_comm]
  have hStar : (Sᴴ * H).trace.re = (S * H).trace.re := by
    have ht : (Sᴴ * H).trace = star (S * H).trace := by
      rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, hHH]
      exact Matrix.trace_mul_comm _ _
    rw [ht]
    simp
  have hp : 0 ≤ (Zᴴ * Z).trace.re :=
    (Complex.nonneg_iff.mp (Matrix.posSemidef_conjTranspose_mul_self Z).trace_nonneg).1
  rw [hGram, Matrix.trace_sub, Matrix.trace_sub, Matrix.trace_add,
    hCycle Sᴴ, hCycle S] at hp
  simp only [Complex.sub_re, Complex.add_re, hStar] at hp
  linarith

theorem re_trace_unitary_mul_le_traceNorm (M V : Matrix I I ℂ)
    (hV : V ∈ Matrix.unitaryGroup I ℂ) : (V * M).trace.re ≤ traceNorm M := by
  obtain ⟨U, hU, hUM⟩ := exists_unitary_polar M
  have hU1 : Uᴴ * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hU
  have hU2 : U * Uᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hU
  have hV1 : Vᴴ * V = 1 := Matrix.mem_unitaryGroup_iff'.mp hV
  have hM : M = Uᴴ * CFC.abs M := by
    rw [← hUM, ← Matrix.mul_assoc, hU1, Matrix.one_mul]
  have hS : (V * Uᴴ)ᴴ * (V * Uᴴ) = 1 := by
    calc
      _ = U * (Vᴴ * V) * Uᴴ := by
        simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
          Matrix.mul_assoc]
      _ = 1 := by rw [hV1, Matrix.mul_one, hU2]
  have hBound := re_trace_isometry_mul_le hS (CFC.abs_nonneg M).posSemidef
  change (V * M).trace.re ≤ (CFC.abs M).trace.re
  calc
    _ = (V * (Uᴴ * CFC.abs M)).trace.re :=
      congrArg (fun N : Matrix I I ℂ => (V * N).trace.re) hM
    _ ≤ _ := by simpa only [Matrix.mul_assoc] using hBound

end Polar
end QuantumProver.AmplitudeDamping.SecretKey.PurificationOrbit

noncomputable section
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace QuantumProver.AmplitudeDamping.SecretKey.MatrixTraceNorm

open QuantumProver.MatrixAnalysis.MatrixSqrt

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem traceNorm_nonneg (M : Matrix I I ℂ) : 0 ≤ traceNorm M :=
  (Complex.nonneg_iff.mp (CFC.abs_nonneg M).posSemidef.trace_nonneg).1

theorem hsNorm_isometry_mul (U X : Matrix I I ℂ) (hU : Uᴴ * U = 1) :
    hsNorm (U * X) = hsNorm X := by
  have hGram : (U * X)ᴴ * (U * X) = Xᴴ * X := by
    calc
      _ = Xᴴ * (Uᴴ * U) * X := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [hU, Matrix.mul_one]
  unfold hsNorm
  rw [hGram]

theorem traceNorm_mul_le_hs (X Y : Matrix I I ℂ) :
    traceNorm (X * Y) ≤ hsNorm X * hsNorm Y := by
  obtain ⟨U, hU, hTrace⟩ := PurificationOrbit.exists_unitary_traceNorm_attainer (X * Y)
  have hGram : Uᴴ * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hU
  calc
    _ = (U * (X * Y)).trace.re := hTrace.symm
    _ ≤ hsNorm (U * X) * hsNorm Y := by
      simpa only [Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc,
        hsNorm_conjTranspose] using hs_trace_pair_le (U * X)ᴴ Y
    _ = _ := by rw [hsNorm_isometry_mul U X hGram]

theorem purification_overlap_re_eq (A B U : Matrix I I ℂ) :
    ((U * A)ᴴ * B).trace.re = (U * (A * Bᴴ)).trace.re := by
  calc
    _ = ((Bᴴ * (U * A))ᴴ).trace.re := by
      simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
        Matrix.mul_assoc]
    _ = (Bᴴ * (U * A)).trace.re := by
      rw [Matrix.trace_conjTranspose]
      simp
    _ = _ := by rw [Matrix.trace_mul_comm Bᴴ (U * A), Matrix.mul_assoc]

theorem exists_purification_overlap_attainer (A B : Matrix I I ℂ) :
    ∃ U : Matrix I I ℂ, U ∈ Matrix.unitaryGroup I ℂ ∧
      (inner ℂ (hsVector (U * A)) (hsVector B)).re = traceNorm (A * Bᴴ) := by
  obtain ⟨U, hU, hTrace⟩ := PurificationOrbit.exists_unitary_traceNorm_attainer (A * Bᴴ)
  refine ⟨U, hU, ?_⟩
  rw [inner_hsVector, purification_overlap_re_eq, hTrace]

theorem purification_overlap_le (A B U : Matrix I I ℂ)
    (hU : U ∈ Matrix.unitaryGroup I ℂ) :
    (inner ℂ (hsVector (U * A)) (hsVector B)).re ≤ traceNorm (A * Bᴴ) := by
  rw [inner_hsVector, purification_overlap_re_eq]
  exact PurificationOrbit.re_trace_unitary_mul_le_traceNorm (A * Bᴴ) U hU

theorem exists_canonical_comparison_purification (rho sigma : Density I) :
    ∃ C : Matrix I I ℂ, Cᴴ * C = sigma.mat ∧ hsNorm C = 1 ∧
      (inner ℂ (hsVector (CFC.sqrt rho.mat)) (hsVector C)).re = rootFidelity rho sigma := by
  let A := CFC.sqrt rho.mat
  let B := CFC.sqrt sigma.mat
  have hB : Bᴴ = B := (CFC.sqrt_nonneg sigma.mat).posSemidef.isHermitian
  have hBB : B * B = sigma.mat := CFC.sqrt_mul_sqrt_self sigma.mat sigma.positive.nonneg
  obtain ⟨U, hU, hOverlap⟩ := exists_purification_overlap_attainer A B
  have hU2 : U * Uᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hU
  let C := Uᴴ * B
  have hGram : Cᴴ * C = sigma.mat := by
    calc
      _ = B * (U * Uᴴ) * B := by
        simp only [C, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
          hB, Matrix.mul_assoc]
      _ = _ := by rw [hU2, Matrix.mul_one, hBB]
  refine ⟨C, hGram, ?_, ?_⟩
  · simp only [hsNorm, hGram, sigma.normalized, Complex.one_re, Real.sqrt_one]
  · rw [inner_hsVector] at hOverlap ⊢
    have hTrace : (Aᴴ * C).trace = ((U * A)ᴴ * B).trace := by
      simp only [C, Matrix.conjTranspose_mul, Matrix.mul_assoc]
    change (Aᴴ * C).trace.re = traceNorm (A * B)
    rw [hTrace]
    simpa only [hB] using hOverlap

theorem sqrt_support {P S : Matrix I I ℂ} (hP : P.IsHermitian)
    (hS : S.PosSemidef) (hSupport : P * S = S) :
    P * CFC.sqrt S = CFC.sqrt S := by
  have hRoot : (CFC.sqrt S)ᴴ = CFC.sqrt S := (CFC.sqrt_nonneg S).posSemidef.isHermitian
  have hSquare : CFC.sqrt S * CFC.sqrt S = S := CFC.sqrt_mul_sqrt_self S hS.nonneg
  have hGram : ((1 - P) * CFC.sqrt S) * ((1 - P) * CFC.sqrt S)ᴴ = 0 := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_sub,
      Matrix.conjTranspose_one, hP.eq, hRoot]
    calc
      _ = (1 - P) * (CFC.sqrt S * CFC.sqrt S) * (1 - P) := by
        simp only [Matrix.mul_assoc]
      _ = (1 - P) * S * (1 - P) := by rw [hSquare]
      _ = 0 := by
        rw [Matrix.sub_mul, Matrix.one_mul, hSupport, sub_self, Matrix.zero_mul]
  have hZero : (1 - P) * CFC.sqrt S = 0 :=
    Matrix.trace_mul_conjTranspose_self_eq_zero_iff.mp (by rw [hGram]; simp)
  rw [Matrix.sub_mul, Matrix.one_mul] at hZero
  exact (sub_eq_zero.mp hZero).symm

theorem hsNorm_projected_sqrt_sq (P : Matrix I I ℂ) (hP : P.IsHermitian)
    (hProj : P * P = P) (rho : Density I) :
    hsNorm (CFC.sqrt rho.mat * P) ^ 2 = (P * rho.mat).trace.re := by
  have hRoot : (CFC.sqrt rho.mat)ᴴ = CFC.sqrt rho.mat :=
    (CFC.sqrt_nonneg rho.mat).posSemidef.isHermitian
  rw [hsNorm_sq, Matrix.conjTranspose_mul, hP.eq, hRoot]
  have hProduct : (P * CFC.sqrt rho.mat) * (CFC.sqrt rho.mat * P) =
      P * rho.mat * P := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (CFC.sqrt rho.mat),
      CFC.sqrt_mul_sqrt_self rho.mat rho.positive.nonneg]
    simp only [Matrix.mul_assoc]
  rw [hProduct, Matrix.trace_mul_cycle, hProj]

theorem squaredFidelity_le_projection (rho sigma : Density I)
    (P : Matrix I I ℂ) (hP : P.IsHermitian) (hProj : P * P = P)
    (hSupport : P * sigma.mat = sigma.mat) :
    squaredFidelity rho sigma ≤ (P * rho.mat).trace.re := by
  have hRootSupport := sqrt_support hP sigma.positive hSupport
  have hProduct : CFC.sqrt rho.mat * CFC.sqrt sigma.mat =
      (CFC.sqrt rho.mat * P) * CFC.sqrt sigma.mat := by
    rw [Matrix.mul_assoc, hRootSupport]
  have hBound : rootFidelity rho sigma ≤ hsNorm (CFC.sqrt rho.mat * P) := by
    rw [rootFidelity, hProduct]
    simpa only [hsNorm_sqrt_of_trace_one sigma.positive sigma.normalized, mul_one] using
      traceNorm_mul_le_hs (CFC.sqrt rho.mat * P) (CFC.sqrt sigma.mat)
  have hNonneg : 0 ≤ rootFidelity rho sigma := traceNorm_nonneg _
  have hNormNonneg := hsNorm_nonneg (CFC.sqrt rho.mat * P)
  rw [squaredFidelity, ← hsNorm_projected_sqrt_sq P hP hProj rho]
  nlinarith

theorem rootFidelity_mem_Icc (rho sigma : Density I) :
    rootFidelity rho sigma ∈ Set.Icc (0 : ℝ) 1 := by
  refine ⟨traceNorm_nonneg _, ?_⟩
  have h := traceNorm_mul_le_hs (CFC.sqrt rho.mat) (CFC.sqrt sigma.mat)
  simpa only [rootFidelity, hsNorm_sqrt_of_trace_one rho.positive rho.normalized,
    hsNorm_sqrt_of_trace_one sigma.positive sigma.normalized, one_mul] using h

theorem squaredFidelity_mem_Icc (rho sigma : Density I) :
    squaredFidelity rho sigma ∈ Set.Icc (0 : ℝ) 1 := by
  have h := rootFidelity_mem_Icc rho sigma
  constructor
  · exact sq_nonneg _
  · dsimp only [squaredFidelity]
    nlinarith [h.1, h.2]

theorem optimalWholeKeySquaredFidelity_mem_Icc {E : Type*}
    [Fintype E] [DecidableEq E] (d : ℕ) (hd : 0 < d)
    (rho : Density ((Fin d × Fin d) × E)) :
    optimalWholeKeySquaredFidelity d hd rho ∈ Set.Icc (0 : ℝ) 1 := by
  let vals := Set.range (fun xi : Density E => squaredFidelity rho (idealKeyStateAgainst d hd xi))
  have hUpper : ∀ y ∈ vals, y ≤ 1 := by
    intro y hy
    rcases hy with ⟨xi, rfl⟩
    exact (squaredFidelity_mem_Icc rho (idealKeyStateAgainst d hd xi)).2
  have hBdd : BddAbove vals := ⟨1, hUpper⟩
  have hNonempty : vals.Nonempty :=
    ⟨squaredFidelity rho (idealKeyStateAgainst d hd rho.marginalRight),
      ⟨rho.marginalRight, rfl⟩⟩
  change sSup vals ∈ Set.Icc (0 : ℝ) 1
  refine ⟨?_, csSup_le hNonempty hUpper⟩
  exact (sq_nonneg (rootFidelity rho (idealKeyStateAgainst d hd rho.marginalRight))).trans
    (le_csSup hBdd ⟨rho.marginalRight, rfl⟩)

section PrivateComparison

open PrivateTest

variable {d : ℕ} {A B E : Type*}
  [Fintype A] [Fintype B] [Fintype E]
  [DecidableEq A] [DecidableEq B] [DecidableEq E]

theorem squaredFidelity_twistedPrivate_le_privacyAcceptance
    (U : Fin d → EuclideanSpace ℂ (A × B) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (A × B))
    (hd : 0 < d)
    (rho : Density (((Fin d × A) × (Fin d × B)) × E))
    (omega : Density ((A × B) × E)) :
    squaredFidelity rho (twistedPrivateDensityWithEve U hd omega) ≤
      privacyAcceptance U (partialTraceRight rho.mat) := by
  have h := squaredFidelity_le_projection rho (twistedPrivateDensityWithEve U hd omega)
    (privacyEffectWithEve (E := E) U)
    (privacyEffectWithEve_posSemidef U).isHermitian
    (privacyEffectWithEve_projection U hd)
    (privacyEffectWithEve_twistedPrivate_support U hd omega)
  simpa only [privacyEffectWithEve_trace] using h

theorem squaredFidelity_twistedPrivate_separable_le
    (U : Fin d → EuclideanSpace ℂ (A × B) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (A × B))
    (hd : 0 < d)
    (rho : Density (((Fin d × A) × (Fin d × B)) × E))
    (omega : Density ((A × B) × E))
    (hsep : InSeparableCone (partialTraceRight rho.mat)) :
    squaredFidelity rho (twistedPrivateDensityWithEve U hd omega) ≤ 1 / (d : ℝ) := by
  exact (squaredFidelity_twistedPrivate_le_privacyAcceptance U hd rho omega).trans
    (privacyAcceptance_separable_le U (honestMarginal rho) hsep)

end PrivateComparison

end QuantumProver.AmplitudeDamping.SecretKey.MatrixTraceNorm

namespace QuantumProver.AmplitudeDamping.SecretKey.PhysicalPurification

open QuantumProver.MatrixAnalysis.MatrixSqrt

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {S E : Type*} [Fintype S] [Fintype E]
  [DecidableEq S] [DecidableEq E]

def vector (C : Matrix S E ℂ) : S × E → ℂ :=
  fun se => star (C se.1 se.2)

def pureMatrix (C : Matrix S E ℂ) : Matrix (S × E) (S × E) ℂ :=
  Matrix.vecMulVec (vector C) (star (vector C))

theorem pureMatrix_posSemidef (C : Matrix S E ℂ) :
    (pureMatrix C).PosSemidef := Matrix.posSemidef_vecMulVec_self_star _

theorem pureMatrix_Eve (C : Matrix S E ℂ) :
    partialTraceLeft (pureMatrix C) = Cᴴ * C := by
  ext e e'
  simp only [partialTraceLeft, pureMatrix, vector, Matrix.vecMulVec_apply,
    Pi.star_apply, star_star, Matrix.mul_apply, Matrix.conjTranspose_apply]

theorem trace_pureMatrix (C : Matrix S E ℂ) :
    (pureMatrix C).trace = (Cᴴ * C).trace := by
  rw [← trace_partialTraceLeft, pureMatrix_Eve]

def density (C : Matrix S E ℂ) (hC : (Cᴴ * C).trace = 1) : Density (S × E) where
  mat := pureMatrix C
  positive := pureMatrix_posSemidef C
  normalized := (trace_pureMatrix C).trans hC

theorem density_Eve (C : Matrix S E ℂ) (hC : (Cᴴ * C).trace = 1) :
    (density C hC).marginalRight.mat = Cᴴ * C := pureMatrix_Eve C

theorem inner_vector (C D : Matrix S E ℂ) :
    inner ℂ (WithLp.toLp 2 (vector C) : EuclideanSpace ℂ (S × E))
      (WithLp.toLp 2 (vector D)) = star ((Cᴴ * D).trace) := by
  simp only [PiLp.inner_apply, PiLp.toLp_apply, RCLike.inner_apply', vector,
    star_star, Fintype.sum_prod_type, Matrix.trace, Matrix.diag_apply,
    Matrix.mul_apply, Matrix.conjTranspose_apply, star_sum, star_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e he
  apply Finset.sum_congr rfl
  intro s hs
  simp [RCLike.star_def,mul_comm]

theorem inner_vector_re (C D : Matrix S E ℂ) :
    (inner ℂ (WithLp.toLp 2 (vector C) : EuclideanSpace ℂ (S × E))
      (WithLp.toLp 2 (vector D))).re = (Cᴴ * D).trace.re := by
  rw [inner_vector]
  simp

def shieldAction (U : Matrix S S ℂ) : Matrix (S × E) (S × E) ℂ :=
  U.map star ⊗ₖ (1 : Matrix E E ℂ)

theorem shieldAction_unitary (U : Matrix S S ℂ)
    (hU : U ∈ Matrix.unitaryGroup S ℂ) :
    shieldAction (E := E) U ∈ Matrix.unitaryGroup (S × E) ℂ := by
  exact Matrix.kronecker_mem_unitary (Matrix.map_star_mem_unitaryGroup_iff.mpr hU)
    (Matrix.mem_unitaryGroup_iff.mpr (by simp))

theorem shieldAction_vector (U : Matrix S S ℂ) (C : Matrix S E ℂ) :
    shieldAction U *ᵥ vector C = vector (U * C) := by
  ext se
  rcases se with ⟨s,e⟩
  simp only [shieldAction, vector, Matrix.mulVec, dotProduct,
    Matrix.kronecker_apply, Matrix.map_apply, Fintype.sum_prod_type,
    Matrix.one_apply, mul_ite, mul_one, mul_zero, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, Matrix.mul_apply,
    star_sum, star_mul]
  apply Finset.sum_congr rfl
  intro t ht
  change (∑ f : E, (if e = f then star (U s t) else 0) * star (C t f)) =
    star (C t e) * star (U s t)
  simp [mul_comm]

theorem shieldAction_pureMatrix (U : Matrix S S ℂ) (C : Matrix S E ℂ) :
    shieldAction U * pureMatrix C * (shieldAction U)ᴴ = pureMatrix (U * C) := by
  rw [pureMatrix, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul,
    ← Matrix.star_mulVec, shieldAction_vector]
  rfl

theorem exists_shieldAction_of_equal_Eve (C D : Matrix S E ℂ)
    (hEve : partialTraceLeft (pureMatrix C) = partialTraceLeft (pureMatrix D)) :
    ∃ U : Matrix S S ℂ, U ∈ Matrix.unitaryGroup S ℂ ∧
      shieldAction U * pureMatrix C * (shieldAction U)ᴴ = pureMatrix D := by
  rw [pureMatrix_Eve, pureMatrix_Eve] at hEve
  obtain ⟨U,hU,hUD⟩ := PurificationOrbit.exists_unitary_matrix_of_equal_gram C D hEve
  exact ⟨U,hU,by rw [shieldAction_pureMatrix,hUD]⟩

def padActual (C : Matrix S E ℂ) : Matrix (S ⊕ E) E ℂ :=
  Matrix.fromRows C 0

def padCanonical (C : Matrix E E ℂ) : Matrix (S ⊕ E) E ℂ :=
  Matrix.fromRows 0 C

theorem padActual_gram (C D : Matrix S E ℂ) :
    (padActual C)ᴴ * padActual D = Cᴴ * D := by
  ext e e'
  simp [padActual, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fintype.sum_sum_type]

theorem padCanonical_gram (C D : Matrix E E ℂ) :
    (padCanonical (S := S) C)ᴴ * padCanonical (S := S) D = Cᴴ * D := by
  ext e e'
  simp [padCanonical, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fintype.sum_sum_type]

def paddingMatrix : Matrix (S ⊕ E) S ℂ :=
  Matrix.of fun t s => if t = Sum.inl s then 1 else 0

theorem paddingMatrix_isometry :
    (paddingMatrix (S := S) (E := E))ᴴ * paddingMatrix (S := S) (E := E) = 1 := by
  ext s t
  simp [paddingMatrix, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fintype.sum_sum_type, Matrix.one_apply,eq_comm]

theorem paddingMatrix_coeff (C : Matrix S E ℂ) :
    paddingMatrix (S := S) (E := E) * C = padActual C := by
  ext se e
  cases se with
  | inl s => simp [paddingMatrix,padActual,Matrix.mul_apply]
  | inr e' => simp [paddingMatrix,padActual,Matrix.mul_apply]

def paddingChannel : KrausChannel S (S ⊕ E) Unit where
  op := fun _ => paddingMatrix
  complete := by simp only [Fintype.sum_unique]; exact paddingMatrix_isometry

theorem exists_canonical_comparison_psd (R : Matrix E E ℂ) (hR : R.PosSemidef)
    (xi : Density E) :
    ∃ D : Matrix E E ℂ, Dᴴ * D = xi.mat ∧
      ((CFC.sqrt R)ᴴ * D).trace.re = traceNorm (CFC.sqrt R * CFC.sqrt xi.mat) := by
  let A := CFC.sqrt R
  let B := CFC.sqrt xi.mat
  have hB : Bᴴ = B := (CFC.sqrt_nonneg xi.mat).posSemidef.isHermitian
  have hBB : B * B = xi.mat := CFC.sqrt_mul_sqrt_self xi.mat xi.positive.nonneg
  obtain ⟨U,hU,hOverlap⟩ := MatrixTraceNorm.exists_purification_overlap_attainer A B
  have hU2 : U * Uᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hU
  let D := Uᴴ * B
  refine ⟨D,?_,?_⟩
  · calc
      _ = B * (U * Uᴴ) * B := by
        simp only [D,Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose,
          hB,Matrix.mul_assoc]
      _ = xi.mat := by rw [hU2,Matrix.mul_one,hBB]
  · rw [inner_hsVector] at hOverlap
    change (Aᴴ * D).trace.re = traceNorm (A * B)
    have hTrace : Aᴴ * D = (U * A)ᴴ * B := by
      simp only [D,Matrix.conjTranspose_mul,Matrix.mul_assoc]
    rw [hTrace]
    simpa only [hB] using hOverlap

theorem exists_padded_comparison (C : Matrix S E ℂ) (xi : Density E) :
    ∃ D : Matrix (S ⊕ E) E ℂ, Dᴴ * D = xi.mat ∧
      (inner ℂ (WithLp.toLp 2 (vector (padActual C)) :
          EuclideanSpace ℂ ((S ⊕ E) × E)) (WithLp.toLp 2 (vector D))).re =
        traceNorm (CFC.sqrt (Cᴴ * C) * CFC.sqrt xi.mat) := by
  let R := Cᴴ * C
  have hR : R.PosSemidef := Matrix.posSemidef_conjTranspose_mul_self C
  let A := padCanonical (S := S) (CFC.sqrt R)
  have hRoot : (CFC.sqrt R)ᴴ = CFC.sqrt R :=
    (CFC.sqrt_nonneg R).posSemidef.isHermitian
  have hA : Aᴴ * A = R := by
    rw [padCanonical_gram,hRoot,CFC.sqrt_mul_sqrt_self R hR.nonneg]
  have hGram : Aᴴ * A = (padActual C)ᴴ * padActual C := by
    rw [hA,padActual_gram]
  obtain ⟨U,hU,hUA⟩ := PurificationOrbit.exists_unitary_matrix_of_equal_gram
    A (padActual C) hGram
  obtain ⟨D,hD,hOverlap⟩ := exists_canonical_comparison_psd R hR xi
  let B := padCanonical (S := S) D
  let W := U * B
  have hU1 : Uᴴ * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hU
  have hCancel (X Y : Matrix (S ⊕ E) E ℂ) :
      (U * X)ᴴ * (U * Y) = Xᴴ * Y := by
    calc
      _ = Xᴴ * (Uᴴ * U) * Y := by
        simp only [Matrix.conjTranspose_mul,Matrix.mul_assoc]
      _ = _ := by rw [hU1,Matrix.mul_one]
  refine ⟨W,?_,?_⟩
  · rw [hCancel B B,padCanonical_gram,hD]
  · rw [inner_vector_re,← hUA,hCancel A B,padCanonical_gram]
    exact hOverlap

theorem padded_comparison_density (C : Matrix S E ℂ) (xi : Density E) :
    ∃ D : Matrix (S ⊕ E) E ℂ, ∃ hD : (Dᴴ * D).trace = 1,
      (density D hD).marginalRight.mat = xi.mat ∧
      (inner ℂ (WithLp.toLp 2 (vector (padActual C)) :
          EuclideanSpace ℂ ((S ⊕ E) × E)) (WithLp.toLp 2 (vector D))).re =
        traceNorm (CFC.sqrt (Cᴴ * C) * CFC.sqrt xi.mat) := by
  obtain ⟨D,hD,hOverlap⟩ := exists_padded_comparison C xi
  have hTrace : (Dᴴ * D).trace = 1 := by rw [hD,xi.normalized]
  exact ⟨D,hTrace,(density_Eve D hTrace).trans hD,hOverlap⟩

end QuantumProver.AmplitudeDamping.SecretKey.PhysicalPurification

namespace QuantumProver.AmplitudeDamping.SecretKey.PhysicalPurification

variable {A B E : Type*} [Fintype A] [Fintype B] [Fintype E]
  [DecidableEq A] [DecidableEq B] [DecidableEq E]

def padAliceActual (C : Matrix (A × B) E ℂ) : Matrix ((A ⊕ E) × B) E ℂ :=
  fun ab e => Sum.elim (fun a => C (a,ab.2) e) (fun _ => 0) ab.1

def padAliceCanonical (b0 : B) (C : Matrix E E ℂ) :
    Matrix ((A ⊕ E) × B) E ℂ :=
  Matrix.of fun ab e => Sum.elim (fun _ => 0)
    (fun f => if ab.2 = b0 then C f e else 0) ab.1

theorem padAliceActual_gram (C D : Matrix (A × B) E ℂ) :
    (padAliceActual C)ᴴ * padAliceActual D = Cᴴ * D := by
  ext e e'
  simp [padAliceActual,Matrix.mul_apply,Matrix.conjTranspose_apply,
    Fintype.sum_prod_type,Fintype.sum_sum_type]

theorem padAliceCanonical_gram (b0 : B) (C D : Matrix E E ℂ) :
    (padAliceCanonical (A := A) b0 C)ᴴ * padAliceCanonical (A := A) b0 D = Cᴴ * D := by
  ext e e'
  simp [padAliceCanonical,Matrix.mul_apply,Matrix.conjTranspose_apply,
    Fintype.sum_prod_type,Fintype.sum_sum_type]

def alicePaddingChannel : KrausChannel (A × B) ((A ⊕ E) × B) Unit :=
  (paddingChannel (S := A) (E := E)).withRightMemory B

theorem alicePaddingChannel_coeff (C : Matrix (A × B) E ℂ) :
    (alicePaddingChannel (A := A) (B := B) (E := E)).op () * C = padAliceActual C := by
  ext ab e
  rcases ab with ⟨a,b⟩
  cases a with
  | inl a =>
    simp [alicePaddingChannel,KrausChannel.withRightMemory,paddingChannel,
      paddingMatrix,padAliceActual,Matrix.mul_apply,Matrix.kronecker_apply,
      Fintype.sum_prod_type,Matrix.one_apply]
  | inr f =>
    simp [alicePaddingChannel,KrausChannel.withRightMemory,paddingChannel,
      paddingMatrix,padAliceActual,Matrix.mul_apply,Matrix.kronecker_apply,
      Fintype.sum_prod_type,Matrix.one_apply]

theorem exists_Alice_padded_comparison (b0 : B)
    (C : Matrix (A × B) E ℂ) (xi : Density E) :
    ∃ D : Matrix ((A ⊕ E) × B) E ℂ, Dᴴ * D = xi.mat ∧
      (inner ℂ (WithLp.toLp 2 (vector (padAliceActual C)) :
          EuclideanSpace ℂ (((A ⊕ E) × B) × E)) (WithLp.toLp 2 (vector D))).re =
        traceNorm (CFC.sqrt (Cᴴ * C) * CFC.sqrt xi.mat) := by
  let R := Cᴴ * C
  have hR : R.PosSemidef := Matrix.posSemidef_conjTranspose_mul_self C
  let V := padAliceCanonical (A := A) b0 (CFC.sqrt R)
  have hRoot : (CFC.sqrt R)ᴴ = CFC.sqrt R :=
    (CFC.sqrt_nonneg R).posSemidef.isHermitian
  have hV : Vᴴ * V = R := by
    dsimp only [V]
    rw [padAliceCanonical_gram,hRoot,CFC.sqrt_mul_sqrt_self R hR.nonneg]
  have hGram : Vᴴ * V = (padAliceActual C)ᴴ * padAliceActual C := by
    rw [hV,padAliceActual_gram]
  obtain ⟨U,hU,hUV⟩ := PurificationOrbit.exists_unitary_matrix_of_equal_gram
    V (padAliceActual C) hGram
  obtain ⟨D,hD,hOverlap⟩ := exists_canonical_comparison_psd R hR xi
  let W := padAliceCanonical (A := A) b0 D
  let Z := U * W
  have hU1 : Uᴴ * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hU
  have hCancel (X Y : Matrix ((A ⊕ E) × B) E ℂ) :
      (U * X)ᴴ * (U * Y) = Xᴴ * Y := by
    calc
      _ = Xᴴ * (Uᴴ * U) * Y := by
        simp only [Matrix.conjTranspose_mul,Matrix.mul_assoc]
      _ = _ := by rw [hU1,Matrix.mul_one]
  refine ⟨Z,?_,?_⟩
  · change (U * W)ᴴ * (U * W) = xi.mat
    rw [hCancel W W]
    dsimp only [W]
    rw [padAliceCanonical_gram,hD]
  · rw [inner_vector_re,← hUV]
    change ((U * V)ᴴ * (U * W)).trace.re = _
    rw [hCancel V W]
    dsimp only [V,W]
    rw [padAliceCanonical_gram]
    exact hOverlap

end QuantumProver.AmplitudeDamping.SecretKey.PhysicalPurification

namespace QuantumProver.AmplitudeDamping.SecretKey.PhysicalPurification

variable {d : ℕ} {A B E : Type*} [Fintype A] [Fintype B] [Fintype E]
  [DecidableEq A] [DecidableEq B] [DecidableEq E]

def keyCoefficient
    (C : Matrix ((Fin d × A) × (Fin d × B)) E ℂ)
    (k : Fin d × Fin d) : Matrix (A × B) E ℂ :=
  fun ab e => C ((k.1,ab.1),(k.2,ab.2)) e

def readoutKeyState (C : Matrix ((Fin d × A) × (Fin d × B)) E ℂ)
    (hC : (Cᴴ * C).trace = 1) : Density ((Fin d × Fin d) × E) :=
  ((basisReadoutChannel (fun r : (Fin d × A) × (Fin d × B) =>
    (r.1.1,r.2.1))).withRightMemory E).onDensity (density C hC)

theorem readoutKeyState_isCCQ
    (C : Matrix ((Fin d × A) × (Fin d × B)) E ℂ)
    (hC : (Cᴴ * C).trace = 1) : IsCCQ (readoutKeyState C hC) :=
  privateLabelReadout_isCCQ _ (density C hC)

theorem readoutKeyState_block
    (C : Matrix ((Fin d × A) × (Fin d × B)) E ℂ)
    (hC : (Cᴴ * C).trace = 1) (k : Fin d × Fin d) :
    classicalKeyBlock (readoutKeyState C hC) k =
      (keyCoefficient C k)ᴴ * keyCoefficient C k := by
  rcases k with ⟨i,j⟩
  ext e e'
  change (((basisReadoutChannel (fun r : (Fin d × A) × (Fin d × B) =>
      (r.1.1,r.2.1))).withRightMemory E).eval (pureMatrix C))
      ((i,j),e) ((i,j),e') = ((keyCoefficient C (i,j))ᴴ * keyCoefficient C (i,j)) e e'
  rw [eval_withRightMemory_apply]
  change ((basisReadoutChannel (fun r : (Fin d × A) × (Fin d × B) =>
      (r.1.1,r.2.1))).eval (Matrix.of fun r s => pureMatrix C (r,e) (s,e'))) (i,j) (i,j) = _
  rw [PrivateTest.basisReadoutChannel_diagonal]
  simp [pureMatrix,vector,keyCoefficient,Matrix.vecMulVec_apply,
    Matrix.mul_apply,Matrix.conjTranspose_apply,Fintype.sum_prod_type,
    Prod.mk.injEq,ite_and,Finset.sum_ite_irrel]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq,Finset.sum_ite_eq',Finset.mem_univ,ite_true]

theorem rootFidelity_readoutKeyState
    (C : Matrix ((Fin d × A) × (Fin d × B)) E ℂ)
    (hC : (Cᴴ * C).trace = 1) (hd : 0 < d) (xi : Density E) :
    rootFidelity (readoutKeyState C hC) (idealKeyStateAgainst d hd xi) =
      (1 / Real.sqrt (d : ℝ)) * ∑ i : Fin d,
        traceNorm (CFC.sqrt ((keyCoefficient C (i,i))ᴴ * keyCoefficient C (i,i)) *
          CFC.sqrt xi.mat) := by
  rw [rootFidelity_isCCQ_ideal_directSum d hd _ (readoutKeyState_isCCQ C hC) xi]
  simp_rw [readoutKeyState_block]

theorem squaredFidelity_readoutKeyState
    (C : Matrix ((Fin d × A) × (Fin d × B)) E ℂ)
    (hC : (Cᴴ * C).trace = 1) (hd : 0 < d) (xi : Density E) :
    squaredFidelity (readoutKeyState C hC) (idealKeyStateAgainst d hd xi) =
      (1 / (d : ℝ)) * (∑ i : Fin d,
        traceNorm (CFC.sqrt ((keyCoefficient C (i,i))ᴴ * keyCoefficient C (i,i)) *
          CFC.sqrt xi.mat)) ^ 2 := by
  rw [squaredFidelity_isCCQ_ideal_directSum d hd _ (readoutKeyState_isCCQ C hC) xi]
  simp_rw [readoutKeyState_block]

end QuantumProver.AmplitudeDamping.SecretKey.PhysicalPurification

namespace QuantumProver.AmplitudeDamping.SecretKey.PhysicalPurification

variable {S E : Type*} [Fintype S] [Fintype E]
  [DecidableEq S] [DecidableEq E]

theorem norm_vector_sq (C : Matrix S E ℂ) :
    ‖(WithLp.toLp 2 (vector C) : EuclideanSpace ℂ (S × E))‖ ^ 2 =
      (Cᴴ * C).trace.re := by
  calc
    _ = (pureMatrix C).trace.re := (PrivateTest.traceGram_norm (vector C)).symm
    _ = _ := congrArg Complex.re (trace_pureMatrix C)

theorem exists_euclidean_unitary_of_equal_gram (C D : Matrix S E ℂ)
    (hGram : Cᴴ * C = Dᴴ * D) :
    ∃ U : EuclideanSpace ℂ S ≃ₗᵢ[ℂ] EuclideanSpace ℂ S,
      PrivateTest.unitaryMatrix U * C = D := by
  have hLin : C.toEuclideanLin.adjoint.comp C.toEuclideanLin =
      D.toEuclideanLin.adjoint.comp D.toEuclideanLin := by
    rw [← PurificationOrbit.toEuclideanLin_gram,← PurificationOrbit.toEuclideanLin_gram,hGram]
  obtain ⟨U,hU⟩ := PurificationOrbit.exists_shield_unitary_of_gram
    C.toEuclideanLin D.toEuclideanLin hLin
  refine ⟨U,?_⟩
  apply Matrix.toEuclideanLin.injective
  rw [PurificationOrbit.toEuclideanLin_mul]
  apply LinearMap.ext
  intro v
  change (PrivateTest.unitaryMatrix U).toEuclideanLin (C.toEuclideanLin v) =
    D.toEuclideanLin v
  rw [PrivateTest.unitaryMatrix_action]
  exact hU v

theorem exists_euclidean_unitary_of_matrix (V : Matrix S S ℂ)
    (hV : V ∈ Matrix.unitaryGroup S ℂ) :
    ∃ U : EuclideanSpace ℂ S ≃ₗᵢ[ℂ] EuclideanSpace ℂ S,
      PrivateTest.unitaryMatrix U = V := by
  have hV1 : Vᴴ * V = 1 := Matrix.mem_unitaryGroup_iff'.mp hV
  have hGram : (1 : Matrix S S ℂ)ᴴ * 1 = Vᴴ * V := by simp [hV1]
  obtain ⟨U,hU⟩ := exists_euclidean_unitary_of_equal_gram (1 : Matrix S S ℂ) V hGram
  exact ⟨U,by simpa only [Matrix.mul_one] using hU⟩

theorem exists_common_shield_unitaries {K : Type*} (k0 : K)
    (D : K → Matrix S E ℂ) (xi : Density E)
    (hGram : ∀ k, (D k)ᴴ * D k = xi.mat) :
    ∃ U : K → EuclideanSpace ℂ S ≃ₗᵢ[ℂ] EuclideanSpace ℂ S,
      ∀ k, PrivateTest.unitaryMatrix (U k) * D k0 = D k := by
  have hSame (k : K) : (D k0)ᴴ * D k0 = (D k)ᴴ * D k := by rw [hGram,hGram]
  choose U hU using fun k => exists_euclidean_unitary_of_equal_gram (D k0) (D k) (hSame k)
  exact ⟨U,hU⟩

variable {d : ℕ} {A B : Type*} [Fintype A] [Fintype B]
  [DecidableEq A] [DecidableEq B]

theorem exists_Alice_padded_key_comparisons (b0 : B)
    (C : Matrix ((Fin d × A) × (Fin d × B)) E ℂ) (xi : Density E) :
    ∃ D : Fin d → Matrix ((A ⊕ E) × B) E ℂ,
      ∀ i, (D i)ᴴ * D i = xi.mat ∧
        (inner ℂ (WithLp.toLp 2 (vector (padAliceActual (keyCoefficient C (i,i)))) :
            EuclideanSpace ℂ (((A ⊕ E) × B) × E))
          (WithLp.toLp 2 (vector (D i)))).re =
          traceNorm (CFC.sqrt ((keyCoefficient C (i,i))ᴴ * keyCoefficient C (i,i)) *
            CFC.sqrt xi.mat) := by
  choose D hD using fun i => exists_Alice_padded_comparison b0 (keyCoefficient C (i,i)) xi
  exact ⟨D,hD⟩

end QuantumProver.AmplitudeDamping.SecretKey.PhysicalPurification

namespace QuantumProver.AmplitudeDamping.SecretKey.PrivateTest

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem pure_overlap_sq_le_projection (P : Matrix I I ℂ)
    (hP : P.IsHermitian) (hProj : P * P = P)
    (v w : I → ℂ)
    (hW : ‖(WithLp.toLp 2 w : EuclideanSpace ℂ I)‖ = 1)
    (hSupport : P *ᵥ w = w) :
    (inner ℂ (WithLp.toLp 2 v : EuclideanSpace ℂ I) (WithLp.toLp 2 w)).re ^ 2 ≤
      (P * Matrix.vecMulVec v (star v)).trace.re := by
  let V : EuclideanSpace ℂ I := WithLp.toLp 2 v
  let W : EuclideanSpace ℂ I := WithLp.toLp 2 w
  let L := P.toEuclideanLin
  have hAdj : L.adjoint = L := by
    change P.toEuclideanLin.adjoint = P.toEuclideanLin
    rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint,hP.eq]
  have hLW : L W = W := by
    change WithLp.toLp 2 (P *ᵥ w) = WithLp.toLp 2 w
    rw [hSupport]
  have hOverlap : inner ℂ (L V) W = inner ℂ V W := by
    calc
      _ = inner ℂ V (L.adjoint W) :=
        (LinearMap.adjoint_inner_right L V W).symm
      _ = _ := by rw [hAdj,hLW]
  have hCauchy : |(inner ℂ V W).re| ≤ ‖L V‖ := by
    rw [← hOverlap]
    calc
      _ ≤ ‖inner ℂ (L V) W‖ := Complex.abs_re_le_norm _
      _ ≤ ‖L V‖ * ‖W‖ := norm_inner_le_norm (L V) W
      _ = ‖L V‖ := by rw [hW,mul_one]
  have hTrace : (P * Matrix.vecMulVec v (star v)).trace.re = ‖L V‖ ^ 2 := by
    have hGram := congruence_Gram_trace P v
    have hCycle : (P * Matrix.vecMulVec v (star v) * Pᴴ).trace =
        (P * Matrix.vecMulVec v (star v)).trace := by
      rw [Matrix.trace_mul_cycle,hP.eq,hProj]
    rw [hCycle] at hGram
    exact hGram
  rw [hTrace]
  change (inner ℂ V W).re ^ 2 ≤ ‖L V‖ ^ 2
  have hAbs : |(inner ℂ V W).re| ^ 2 = (inner ℂ V W).re ^ 2 := sq_abs _
  nlinarith [abs_nonneg (inner ℂ V W).re,norm_nonneg (L V)]

end QuantumProver.AmplitudeDamping.SecretKey.PrivateTest

namespace QuantumProver.AmplitudeDamping.SecretKey.PhysicalPurification

variable {d : ℕ} {A B E : Type*} [Fintype A] [Fintype B] [Fintype E]
  [DecidableEq A] [DecidableEq B] [DecidableEq E]

def padAliceKeyCoefficient
    (C : Matrix ((Fin d × A) × (Fin d × B)) E ℂ) :
    Matrix ((Fin d × (A ⊕ E)) × (Fin d × B)) E ℂ :=
  Matrix.of fun r e => Sum.elim
    (fun a => C ((r.1.1,a),r.2) e) (fun _ => 0) r.1.2

def keyPaddingChannel : KrausChannel ((Fin d × A) × (Fin d × B))
    ((Fin d × (A ⊕ E)) × (Fin d × B)) Unit :=
  ((paddingChannel (S := A) (E := E)).withMemory (Fin d)).withRightMemory (Fin d × B)

theorem keyPaddingChannel_coeff
    (C : Matrix ((Fin d × A) × (Fin d × B)) E ℂ) :
    (keyPaddingChannel (d := d) (A := A) (B := B) (E := E)).op () * C =
      padAliceKeyCoefficient C := by
  ext r e
  rcases r with ⟨⟨i,a⟩,⟨j,b⟩⟩
  cases a with
  | inl a =>
    simp [keyPaddingChannel,KrausChannel.withMemory,KrausChannel.withRightMemory,
      paddingChannel,paddingMatrix,padAliceKeyCoefficient,Matrix.mul_apply,
      Matrix.kronecker_apply,Fintype.sum_prod_type,Matrix.one_apply]
  | inr f =>
    simp [keyPaddingChannel,KrausChannel.withMemory,KrausChannel.withRightMemory,
      paddingChannel,paddingMatrix,padAliceKeyCoefficient,Matrix.mul_apply,
      Matrix.kronecker_apply,Fintype.sum_prod_type,Matrix.one_apply]

theorem padAliceKeyCoefficient_gram
    (C : Matrix ((Fin d × A) × (Fin d × B)) E ℂ) :
    (padAliceKeyCoefficient C)ᴴ * padAliceKeyCoefficient C = Cᴴ * C := by
  let K := (keyPaddingChannel (d := d) (A := A) (B := B) (E := E)).op ()
  have hK : Kᴴ * K = 1 := by
    simpa only [Fintype.sum_unique] using
      (keyPaddingChannel (d := d) (A := A) (B := B) (E := E)).complete
  rw [← keyPaddingChannel_coeff]
  change (K * C)ᴴ * (K * C) = Cᴴ * C
  calc
    _ = Cᴴ * (Kᴴ * K) * C := by
      simp only [Matrix.conjTranspose_mul,Matrix.mul_assoc]
    _ = _ := by rw [hK,Matrix.mul_one]

theorem padAliceKeyCoefficient_branch
    (C : Matrix ((Fin d × A) × (Fin d × B)) E ℂ) (k : Fin d × Fin d) :
    keyCoefficient (padAliceKeyCoefficient C) k = padAliceActual (keyCoefficient C k) := by
  ext ab e
  rcases ab with ⟨a,b⟩
  cases a <;> rfl

theorem readoutKeyState_padAlice
    (C : Matrix ((Fin d × A) × (Fin d × B)) E ℂ)
    (hC : (Cᴴ * C).trace = 1) :
    readoutKeyState (padAliceKeyCoefficient C)
      (by rw [padAliceKeyCoefficient_gram,hC]) = readoutKeyState C hC := by
  have hCp : ((padAliceKeyCoefficient C)ᴴ * padAliceKeyCoefficient C).trace = 1 := by
    rw [padAliceKeyCoefficient_gram,hC]
  apply Density.eq_of_mat_eq
  ext x y
  rcases x with ⟨k,e⟩
  rcases y with ⟨k',e'⟩
  by_cases hk : k = k'
  · subst k'
    change (classicalKeyBlock (readoutKeyState (padAliceKeyCoefficient C) hCp) k) e e' =
      (classicalKeyBlock (readoutKeyState C hC) k) e e'
    rw [readoutKeyState_block,readoutKeyState_block,padAliceKeyCoefficient_branch,
      padAliceActual_gram]
  · rw [readoutKeyState_isCCQ _ _ k k' e e' hk,
      readoutKeyState_isCCQ _ _ k k' e e' hk]

end QuantumProver.AmplitudeDamping.SecretKey.PhysicalPurification

namespace QuantumProver.AmplitudeDamping.SecretKey.PhysicalPurification

variable {S T E : Type*} [Fintype S] [Fintype T] [Fintype E]
  [DecidableEq S] [DecidableEq T] [DecidableEq E]

theorem map_star_mul {R : Type*} (L : Matrix S T ℂ) (M : Matrix T R ℂ) :
    (L * M).map star = L.map star * M.map star := by
  ext s r
  simp only [Matrix.map_apply,Matrix.mul_apply,star_sum,star_mul]
  apply Finset.sum_congr rfl
  intro t ht
  exact mul_comm _ _

theorem pureMatrix_honest (C : Matrix S E ℂ) :
    partialTraceRight (pureMatrix C) = C.map star * (C.map star)ᴴ := by
  ext s t
  simp [partialTraceRight,pureMatrix,vector,Matrix.vecMulVec_apply,
    Matrix.mul_apply,Matrix.conjTranspose_apply,Matrix.map_apply]

variable {d : ℕ} {A B : Type*} [Fintype A] [Fintype B]
  [DecidableEq A] [DecidableEq B]

theorem privacyAcceptance_pureMatrix
    (U : Fin d → EuclideanSpace ℂ (A × B) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (A × B))
    (C : Matrix ((Fin d × A) × (Fin d × B)) E ℂ) :
    PrivateTest.privacyAcceptance U (partialTraceRight (pureMatrix C)) =
      ‖(WithLp.toLp 2 (vector ((PrivateTest.privacyMatrix U).map star * C)) :
        EuclideanSpace ℂ ((A × B) × E))‖ ^ 2 / (d : ℝ) := by
  let P := PrivateTest.privacyMatrix U
  let F := P.map star * C
  have hF : F.map star = P * C.map star := by
    ext s e
    simp [F,Matrix.map_apply,Matrix.mul_apply,star_sum,star_mul,mul_comm]
  have hMat : P * partialTraceRight (pureMatrix C) * Pᴴ =
      partialTraceRight (pureMatrix F) := by
    rw [pureMatrix_honest,pureMatrix_honest,hF]
    simp only [Matrix.conjTranspose_mul,Matrix.mul_assoc]
  change (P * partialTraceRight (pureMatrix C) * Pᴴ).trace.re / (d : ℝ) =
    ‖(WithLp.toLp 2 (vector F) : EuclideanSpace ℂ ((A × B) × E))‖ ^ 2 / (d : ℝ)
  rw [hMat,trace_partialTraceRight,trace_pureMatrix,← norm_vector_sq]

theorem privacyCoefficient_branches
    (U : Fin d → EuclideanSpace ℂ (A × B) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (A × B))
    (C : Matrix ((Fin d × A) × (Fin d × B)) E ℂ) :
    (PrivateTest.privacyMatrix U).map star * C =
      ∑ i : Fin d, (PrivateTest.unitaryMatrix (U i)).map star * keyCoefficient C (i,i) := by
  ext ab e
  rw [PrivateTest.privacyMatrix_eq_entries]
  simp [PrivateTest.privacyMatrixByEntries,Matrix.map_apply,Matrix.mul_apply,
    Matrix.sum_apply,Fintype.sum_prod_type,keyCoefficient,apply_ite,ite_mul]

theorem exists_private_test_of_whole_Eve_candidate (b0 : B)
    (C : Matrix ((Fin d × A) × (Fin d × B)) E ℂ)
    (hC : (Cᴴ * C).trace = 1) (hd : 0 < d) (xi : Density E) :
    ∃ V : Fin d → EuclideanSpace ℂ ((A ⊕ E) × B) ≃ₗᵢ[ℂ]
        EuclideanSpace ℂ ((A ⊕ E) × B),
      squaredFidelity (readoutKeyState C hC) (idealKeyStateAgainst d hd xi) ≤
        PrivateTest.privacyAcceptance V
          (partialTraceRight (pureMatrix (padAliceKeyCoefficient C))) := by
  obtain ⟨D,hD⟩ := exists_Alice_padded_key_comparisons b0 C xi
  let i0 : Fin d := ⟨0,hd⟩
  obtain ⟨U,hU⟩ := exists_common_shield_unitaries i0 D xi (fun i => (hD i).1)
  have hTrans (i : Fin d) : (PrivateTest.unitaryMatrix (U i))ᵀ ∈
      Matrix.unitaryGroup ((A ⊕ E) × B) ℂ :=
    Matrix.transpose_mem_unitaryGroup_iff.mpr (PrivateTest.unitaryMatrix_mem_unitary (U i))
  choose V hV using fun i => exists_euclidean_unitary_of_matrix
    (PrivateTest.unitaryMatrix (U i))ᵀ (hTrans i)
  let Cp := padAliceKeyCoefficient C
  let F := (PrivateTest.privacyMatrix V).map star * Cp
  let f : Fin d → ℝ := fun i =>
    traceNorm (CFC.sqrt ((keyCoefficient C (i,i))ᴴ * keyCoefficient C (i,i)) *
      CFC.sqrt xi.mat)
  have hVD (i : Fin d) : ((PrivateTest.unitaryMatrix (V i)).map star)ᴴ * D i0 = D i := by
    rw [hV]
    have hTranspose : ((PrivateTest.unitaryMatrix (U i))ᵀ.map star)ᴴ =
        PrivateTest.unitaryMatrix (U i) := by
      ext s t
      simp [Matrix.conjTranspose_apply,Matrix.map_apply]
    rw [hTranspose]
    exact hU i
  have hBranch (i : Fin d) :
      (((PrivateTest.unitaryMatrix (V i)).map star * keyCoefficient Cp (i,i))ᴴ *
        D i0).trace.re = f i := by
    rw [Matrix.conjTranspose_mul,Matrix.mul_assoc,hVD]
    dsimp [Cp]
    rw [padAliceKeyCoefficient_branch]
    rw [← inner_vector_re]
    exact (hD i).2
  have hOverlap : (Fᴴ * D i0).trace.re = ∑ i : Fin d, f i := by
    have hFSum : F = ∑ i : Fin d,
        (PrivateTest.unitaryMatrix (V i)).map star * keyCoefficient Cp (i,i) :=
      privacyCoefficient_branches V Cp
    rw [hFSum]
    simp only [Matrix.conjTranspose_sum,Matrix.sum_mul,Matrix.trace_sum,Complex.re_sum]
    exact Finset.sum_congr rfl (fun i hi => hBranch i)
  have hWsq : ‖(WithLp.toLp 2 (vector (D i0)) :
      EuclideanSpace ℂ (((A ⊕ E) × B) × E))‖ ^ 2 = 1 := by
    rw [norm_vector_sq,(hD i0).1,xi.normalized]
    norm_num
  have hW : ‖(WithLp.toLp 2 (vector (D i0)) :
      EuclideanSpace ℂ (((A ⊕ E) × B) × E))‖ = 1 := by
    have hNonneg := norm_nonneg (WithLp.toLp 2 (vector (D i0)) :
      EuclideanSpace ℂ (((A ⊕ E) × B) × E))
    nlinarith
  have hCauchy : |∑ i : Fin d, f i| ≤
      ‖(WithLp.toLp 2 (vector F) : EuclideanSpace ℂ (((A ⊕ E) × B) × E))‖ := by
    rw [← hOverlap,← inner_vector_re]
    calc
      _ ≤ ‖inner ℂ (WithLp.toLp 2 (vector F) :
          EuclideanSpace ℂ (((A ⊕ E) × B) × E)) (WithLp.toLp 2 (vector (D i0)))‖ :=
        Complex.abs_re_le_norm _
      _ ≤ ‖(WithLp.toLp 2 (vector F) :
            EuclideanSpace ℂ (((A ⊕ E) × B) × E))‖ *
          ‖(WithLp.toLp 2 (vector (D i0)) :
            EuclideanSpace ℂ (((A ⊕ E) × B) × E))‖ := norm_inner_le_norm _ _
      _ = _ := by rw [hW,mul_one]
  have hSq : (∑ i : Fin d, f i) ^ 2 ≤
      ‖(WithLp.toLp 2 (vector F) : EuclideanSpace ℂ (((A ⊕ E) × B) × E))‖ ^ 2 := by
    have hNN := norm_nonneg (WithLp.toLp 2 (vector F) :
      EuclideanSpace ℂ (((A ⊕ E) × B) × E))
    nlinarith [abs_nonneg (∑ i : Fin d, f i),sq_abs (∑ i : Fin d, f i)]
  refine ⟨V,?_⟩
  rw [squaredFidelity_readoutKeyState,privacyAcceptance_pureMatrix]
  change (1 / (d : ℝ)) * (∑ i : Fin d, f i) ^ 2 ≤
    ‖(WithLp.toLp 2 (vector F) : EuclideanSpace ℂ (((A ⊕ E) × B) × E))‖ ^ 2 / (d : ℝ)
  calc
    _ = (∑ i : Fin d, f i) ^ 2 / (d : ℝ) := by ring
    _ ≤ _ := div_le_div_of_nonneg_right hSq (Nat.cast_nonneg d : (0 : ℝ) ≤ d)

end QuantumProver.AmplitudeDamping.SecretKey.PhysicalPurification

namespace QuantumProver.AmplitudeDamping.SecretKey.PhysicalPurification

variable {I S E : Type*} [Fintype I] [Fintype S] [Fintype E]
  [DecidableEq I] [DecidableEq S] [DecidableEq E]

def coefficientOfVector (v : S × E → ℂ) : Matrix S E ℂ :=
  Matrix.of fun s e => star (v (s,e))

theorem vector_coefficientOfVector (v : S × E → ℂ) :
    vector (coefficientOfVector v) = v := by
  funext x
  simp [coefficientOfVector,vector]

def pureOutputCoefficient (C : KrausChannel I (S × E) Unit) (v : I → ℂ) :
    Matrix S E ℂ := coefficientOfVector (C.op () *ᵥ v)

theorem pureOutputCoefficient_matrix (C : KrausChannel I (S × E) Unit) (v : I → ℂ) :
    pureMatrix (pureOutputCoefficient C v) = C.eval (Matrix.vecMulVec v (star v)) := by
  simp only [pureOutputCoefficient,pureMatrix,vector_coefficientOfVector,KrausChannel.eval,
    Fintype.sum_unique,Matrix.mul_vecMulVec,Matrix.vecMulVec_mul,← Matrix.star_mulVec]

theorem pureOutputCoefficient_normalized (C : KrausChannel I (S × E) Unit) (v : I → ℂ)
    (hv : (Matrix.vecMulVec v (star v)).trace = 1) :
    ((pureOutputCoefficient C v)ᴴ * pureOutputCoefficient C v).trace = 1 := by
  rw [← trace_pureMatrix,pureOutputCoefficient_matrix,C.trace_eval,hv]

variable {d : ℕ} {A B : Type*} [Fintype A] [Fintype B]
  [DecidableEq A] [DecidableEq B]

def labelRecordingMatrix (label : A → Fin d) : Matrix (Fin d × A) A ℂ :=
  Matrix.of fun ka a => if ka.2 = a then if ka.1 = label a then 1 else 0 else 0

theorem labelRecordingMatrix_isometry (label : A → Fin d) :
    (labelRecordingMatrix label)ᴴ * labelRecordingMatrix label = 1 := by
  ext a b
  by_cases hab : a = b
  · subst b
    simp [labelRecordingMatrix,Matrix.mul_apply,Matrix.conjTranspose_apply,
      Fintype.sum_prod_type,Matrix.one_apply,apply_ite,ite_mul,mul_ite,eq_comm]
  · simp [labelRecordingMatrix,Matrix.mul_apply,Matrix.conjTranspose_apply,
      Fintype.sum_prod_type,Matrix.one_apply,apply_ite,ite_mul,mul_ite,eq_comm,hab]

def keyRecordingChannel (labelA : A → Fin d) (labelB : B → Fin d) :
    KrausChannel (A × B) ((Fin d × A) × (Fin d × B)) Unit where
  op := fun _ => labelRecordingMatrix labelA ⊗ₖ labelRecordingMatrix labelB
  complete := by
    simp only [Fintype.sum_unique,Matrix.conjTranspose_kronecker,
      ← Matrix.mul_kronecker_mul,labelRecordingMatrix_isometry,Matrix.one_kronecker_one]

def keyRecordedCoefficient (labelA : A → Fin d) (labelB : B → Fin d)
    (C : Matrix (A × B) E ℂ) : Matrix ((Fin d × A) × (Fin d × B)) E ℂ :=
  Matrix.of fun r e => if r.1.1 = labelA r.1.2 ∧ r.2.1 = labelB r.2.2
    then C (r.1.2,r.2.2) e else 0

theorem keyRecordingChannel_coeff (labelA : A → Fin d) (labelB : B → Fin d)
    (C : Matrix (A × B) E ℂ) :
    (keyRecordingChannel labelA labelB).op () * C = keyRecordedCoefficient labelA labelB C := by
  ext r e
  rcases r with ⟨⟨i,a⟩,⟨j,b⟩⟩
  by_cases hi : i = labelA a <;> by_cases hj : j = labelB b <;>
    simp [keyRecordingChannel,labelRecordingMatrix,keyRecordedCoefficient,
      Matrix.mul_apply,Matrix.kronecker_apply,Fintype.sum_prod_type,ite_and,
      apply_ite,ite_mul,mul_ite,hi,hj]

theorem keyRecordedCoefficient_gram (labelA : A → Fin d) (labelB : B → Fin d)
    (C : Matrix (A × B) E ℂ) :
    (keyRecordedCoefficient labelA labelB C)ᴴ * keyRecordedCoefficient labelA labelB C =
      Cᴴ * C := by
  let K := (keyRecordingChannel labelA labelB).op ()
  have hK : Kᴴ * K = 1 := by
    simpa only [Fintype.sum_unique] using (keyRecordingChannel labelA labelB).complete
  rw [← keyRecordingChannel_coeff]
  change (K * C)ᴴ * (K * C) = Cᴴ * C
  calc
    _ = Cᴴ * (Kᴴ * K) * C := by
      simp only [Matrix.conjTranspose_mul,Matrix.mul_assoc]
    _ = _ := by rw [hK,Matrix.mul_one]

theorem readoutKeyState_keyRecorded (labelA : A → Fin d) (labelB : B → Fin d)
    (C : Matrix (A × B) E ℂ) (hC : (Cᴴ * C).trace = 1) :
    readoutKeyState (keyRecordedCoefficient labelA labelB C)
      (by rw [keyRecordedCoefficient_gram,hC]) =
      ((basisReadoutChannel (fun ab : A × B => (labelA ab.1,labelB ab.2))).withRightMemory E).onDensity
        (density C hC) := by
  have hCp : ((keyRecordedCoefficient labelA labelB C)ᴴ *
      keyRecordedCoefficient labelA labelB C).trace = 1 := by
    rw [keyRecordedCoefficient_gram,hC]
  apply Density.eq_of_mat_eq
  ext x y
  rcases x with ⟨k,e⟩
  rcases y with ⟨k',e'⟩
  by_cases hk : k = k'
  · subst k'
    change (classicalKeyBlock (readoutKeyState (keyRecordedCoefficient labelA labelB C) hCp) k) e e' =
      (((basisReadoutChannel (fun ab : A × B => (labelA ab.1,labelB ab.2))).withRightMemory E).eval
        (pureMatrix C)) (k,e) (k,e')
    rw [readoutKeyState_block,PublicHistory.reference_basisReadout_apply_B,Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro ab hab
    rcases ab with ⟨a,b⟩
    by_cases ha : k.1 = labelA a <;> by_cases hb : k.2 = labelB b <;>
      simp [keyCoefficient,keyRecordedCoefficient,pureMatrix,vector,Matrix.vecMulVec_apply,
        Matrix.conjTranspose_apply,Prod.ext_iff,ha,hb]
  · rw [readoutKeyState_isCCQ _ _ k k' e e' hk]
    change 0 = (((basisReadoutChannel (fun ab : A × B =>
      (labelA ab.1,labelB ab.2))).withRightMemory E).eval (pureMatrix C)) (k,e) (k',e')
    rw [PublicHistory.reference_basisReadout_apply_B]
    symm
    apply Finset.sum_eq_zero
    intro ab hab
    have hNo : ¬ (k = (labelA ab.1,labelB ab.2) ∧ k' = (labelA ab.1,labelB ab.2)) := by
      rintro ⟨h,h'⟩
      exact hk (h.trans h'.symm)
    simp only [hNo,ite_false]

theorem nonempty_B_of_normalized_keyCoefficient
    (C : Matrix ((Fin d × A) × (Fin d × B)) E ℂ) (hC : (Cᴴ * C).trace = 1) :
    Nonempty B := by
  by_contra hB
  haveI : IsEmpty B := not_nonempty_iff.mp hB
  have hZero : C = 0 := by
    ext x e
    exact isEmptyElim x.2.2
  rw [hZero] at hC
  norm_num at hC

theorem exists_private_test_of_whole_Eve_candidate_normalized
    (C : Matrix ((Fin d × A) × (Fin d × B)) E ℂ)
    (hC : (Cᴴ * C).trace = 1) (hd : 0 < d) (xi : Density E) :
    ∃ V : Fin d → EuclideanSpace ℂ ((A ⊕ E) × B) ≃ₗᵢ[ℂ]
        EuclideanSpace ℂ ((A ⊕ E) × B),
      squaredFidelity (readoutKeyState C hC) (idealKeyStateAgainst d hd xi) ≤
        PrivateTest.privacyAcceptance V
          (partialTraceRight (pureMatrix (padAliceKeyCoefficient C))) := by
  letI : Nonempty B := nonempty_B_of_normalized_keyCoefficient C hC
  exact exists_private_test_of_whole_Eve_candidate (Classical.choice inferInstance) C hC hd xi

end QuantumProver.AmplitudeDamping.SecretKey.PhysicalPurification

namespace QuantumProver.AmplitudeDamping.SecretKey.PhysicalProtocol.FiniteKeyProtocol

open PhysicalPurification PublicHistory

variable {p : ℝ} {a b af bf d : ℕ} {E : Type*}
  [Fintype E] [DecidableEq E]

def retainedProtocolCoefficient (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (P : FiniteKeyProtocol p a b af bf) (C : Matrix (Fin a × Fin b) E ℂ) :
    Matrix ((P.comparisonPublicHistory_B × Fin af) ×
      (P.comparisonPublicHistory_B × Fin bf)) (P.Environment × E) ℂ :=
  pureOutputCoefficient (wholeRetainedChannelWithEve_B hp0 hp1 P E) (vector C)

theorem retainedProtocolCoefficient_matrix (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (P : FiniteKeyProtocol p a b af bf) (C : Matrix (Fin a × Fin b) E ℂ) :
    pureMatrix (P.retainedProtocolCoefficient hp0 hp1 C) =
      (wholeRetainedChannelWithEve_B hp0 hp1 P E).eval (pureMatrix C) :=
  pureOutputCoefficient_matrix _ _

theorem retainedProtocolCoefficient_normalized (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (P : FiniteKeyProtocol p a b af bf) (C : Matrix (Fin a × Fin b) E ℂ)
    (hC : (Cᴴ * C).trace = 1) :
    ((P.retainedProtocolCoefficient hp0 hp1 C)ᴴ *
      P.retainedProtocolCoefficient hp0 hp1 C).trace = 1 := by
  apply pureOutputCoefficient_normalized
  change (pureMatrix C).trace = 1
  rw [trace_pureMatrix,hC]

def retainedProtocolKeyCoefficient (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (P : FiniteKeyProtocol p a b af bf)
    (labelA : Fin af → Fin d) (labelB : Fin bf → Fin d)
    (C : Matrix (Fin a × Fin b) E ℂ) :
    Matrix ((Fin d × (P.comparisonPublicHistory_B × Fin af)) ×
      (Fin d × (P.comparisonPublicHistory_B × Fin bf))) (P.Environment × E) ℂ :=
  keyRecordedCoefficient (fun x => labelA x.2) (fun x => labelB x.2)
    (P.retainedProtocolCoefficient hp0 hp1 C)

theorem retainedProtocolKeyCoefficient_normalized (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (P : FiniteKeyProtocol p a b af bf)
    (labelA : Fin af → Fin d) (labelB : Fin bf → Fin d)
    (C : Matrix (Fin a × Fin b) E ℂ) (hC : (Cᴴ * C).trace = 1) :
    ((P.retainedProtocolKeyCoefficient hp0 hp1 labelA labelB C)ᴴ *
      P.retainedProtocolKeyCoefficient hp0 hp1 labelA labelB C).trace = 1 := by
  rw [retainedProtocolKeyCoefficient,keyRecordedCoefficient_gram]
  exact P.retainedProtocolCoefficient_normalized hp0 hp1 C hC

theorem retainedProtocolKey_readout (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (P : FiniteKeyProtocol p a b af bf)
    (labelA : Fin af → Fin d) (labelB : Fin bf → Fin d)
    (C : Matrix (Fin a × Fin b) E ℂ) (hC : (Cᴴ * C).trace = 1) :
    readoutKeyState (P.retainedProtocolKeyCoefficient hp0 hp1 labelA labelB C)
      (P.retainedProtocolKeyCoefficient_normalized hp0 hp1 labelA labelB C hC) =
      P.finalKeyStateWithPriorEveLabels hp0 hp1 labelA labelB E (density C hC) := by
  have hRet := P.retainedProtocolCoefficient_normalized hp0 hp1 C hC
  have hRecord := readoutKeyState_keyRecorded
    (fun x : P.comparisonPublicHistory_B × Fin af => labelA x.2)
    (fun x : P.comparisonPublicHistory_B × Fin bf => labelB x.2)
    (P.retainedProtocolCoefficient hp0 hp1 C) hRet
  calc
    _ = ((basisReadoutChannel (fun x :
      (P.comparisonPublicHistory_B × Fin af) × (P.comparisonPublicHistory_B × Fin bf) =>
        (labelA x.1.2,labelB x.2.2))).withRightMemory (P.Environment × E)).onDensity
      (density (P.retainedProtocolCoefficient hp0 hp1 C) hRet) := hRecord
    _ = _ := by
      apply Density.eq_of_mat_eq
      change ((basisReadoutChannel (fun x :
          (P.comparisonPublicHistory_B × Fin af) × (P.comparisonPublicHistory_B × Fin bf) =>
            (labelA x.1.2,labelB x.2.2))).withRightMemory (P.Environment × E)).eval
          (pureMatrix (P.retainedProtocolCoefficient hp0 hp1 C)) =
        ((basisReadoutChannel (fun x : Fin af × Fin bf =>
          (labelA x.1,labelB x.2))).withRightMemory (P.Environment × E)).eval
          (localPriorEveMatrix_B P (pureMatrix C))
      rw [retainedProtocolCoefficient_matrix]
      exact wholeRetainedChannelWithEve_readout_B hp0 hp1 P
        (fun x : Fin af × Fin bf => (labelA x.1,labelB x.2)) (pureMatrix C)

theorem exists_private_test_of_protocol_candidate (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (P : FiniteKeyProtocol p a b af bf)
    (labelA : Fin af → Fin d) (labelB : Fin bf → Fin d)
    (C : Matrix (Fin a × Fin b) E ℂ) (hC : (Cᴴ * C).trace = 1)
    (hd : 0 < d) (xi : Density (P.Environment × E)) :
    ∃ V : Fin d →
        EuclideanSpace ℂ (((P.comparisonPublicHistory_B × Fin af) ⊕ (P.Environment × E)) ×
          (P.comparisonPublicHistory_B × Fin bf)) ≃ₗᵢ[ℂ]
        EuclideanSpace ℂ (((P.comparisonPublicHistory_B × Fin af) ⊕ (P.Environment × E)) ×
          (P.comparisonPublicHistory_B × Fin bf)),
      squaredFidelity
        (P.finalKeyStateWithPriorEveLabels hp0 hp1 labelA labelB E (density C hC))
        (idealKeyStateAgainst d hd xi) ≤
      PrivateTest.privacyAcceptance V (partialTraceRight (pureMatrix
        (padAliceKeyCoefficient (P.retainedProtocolKeyCoefficient hp0 hp1 labelA labelB C)))) := by
  obtain ⟨V,hV⟩ := exists_private_test_of_whole_Eve_candidate_normalized
    (P.retainedProtocolKeyCoefficient hp0 hp1 labelA labelB C)
    (P.retainedProtocolKeyCoefficient_normalized hp0 hp1 labelA labelB C hC) hd xi
  refine ⟨V,?_⟩
  rw [P.retainedProtocolKey_readout hp0 hp1 labelA labelB C hC] at hV
  exact hV

end QuantumProver.AmplitudeDamping.SecretKey.PhysicalProtocol.FiniteKeyProtocol

namespace QuantumProver.AmplitudeDamping.SecretKey.PhysicalPurification

variable {S T E : Type*} [Fintype S] [Fintype T] [Fintype E]
  [DecidableEq S] [DecidableEq T] [DecidableEq E]

theorem rectangular_action_vector (K : Matrix T S ℂ) (C : Matrix S E ℂ) :
    (K ⊗ₖ (1 : Matrix E E ℂ)) *ᵥ vector C = vector (K.map star * C) := by
  ext te
  rcases te with ⟨t,e⟩
  simp only [vector,Matrix.mulVec,dotProduct,Matrix.kronecker_apply,
    Matrix.map_apply,Fintype.sum_prod_type,Matrix.one_apply,mul_ite,mul_one,
    mul_zero,zero_mul,Finset.sum_ite_eq',Finset.mem_univ,if_true,
    Matrix.mul_apply,star_sum,star_mul,star_star]
  apply Finset.sum_congr rfl
  intro s hs
  change (∑ f : E, (if e = f then K t s else 0) * star (C s f)) =
    star (C s e) * K t s
  simp [mul_comm]

theorem rectangular_action_pureMatrix (K : Matrix T S ℂ) (C : Matrix S E ℂ) :
    (K ⊗ₖ (1 : Matrix E E ℂ)) * pureMatrix C *
      (K ⊗ₖ (1 : Matrix E E ℂ))ᴴ = pureMatrix (K.map star * C) := by
  rw [pureMatrix,Matrix.mul_vecMulVec,Matrix.vecMulVec_mul,
    ← Matrix.star_mulVec,rectangular_action_vector]
  rfl

theorem eval_singleOperator_pureMatrix (K : KrausChannel S T Unit) (C : Matrix S E ℂ) :
    (K.withRightMemory E).eval (pureMatrix C) = pureMatrix ((K.op ()).map star * C) := by
  simp only [KrausChannel.eval,KrausChannel.withRightMemory,Fintype.sum_unique]
  exact rectangular_action_pureMatrix (K.op ()) C

variable {d : ℕ} {A B : Type*} [Fintype A] [Fintype B]
  [DecidableEq A] [DecidableEq B]

theorem keyRecordingChannel_map_star (labelA : A → Fin d) (labelB : B → Fin d) :
    ((keyRecordingChannel labelA labelB).op ()).map star =
      (keyRecordingChannel labelA labelB).op () := by
  ext x y
  simp only [keyRecordingChannel,Matrix.map_apply,Matrix.kroneckerMap_apply,
    labelRecordingMatrix,Matrix.of_apply]
  split_ifs <;> simp

theorem eval_keyRecordingChannel_pureMatrix (labelA : A → Fin d) (labelB : B → Fin d)
    (C : Matrix (A × B) E ℂ) :
    ((keyRecordingChannel labelA labelB).withRightMemory E).eval (pureMatrix C) =
      pureMatrix (keyRecordedCoefficient labelA labelB C) := by
  rw [eval_singleOperator_pureMatrix,keyRecordingChannel_map_star,keyRecordingChannel_coeff]

theorem keyPaddingChannel_map_star :
    ((keyPaddingChannel (d := d) (A := A) (B := B) (E := E)).op ()).map star =
      (keyPaddingChannel (d := d) (A := A) (B := B) (E := E)).op () := by
  ext x y
  simp only [keyPaddingChannel,KrausChannel.withMemory,KrausChannel.withRightMemory,
    paddingChannel,paddingMatrix,Matrix.map_apply,Matrix.kroneckerMap_apply,
    Matrix.one_apply,Matrix.of_apply]
  split_ifs <;> simp

theorem eval_keyPaddingChannel_pureMatrix
    (C : Matrix ((Fin d × A) × (Fin d × B)) E ℂ) :
    ((keyPaddingChannel (d := d) (A := A) (B := B) (E := E)).withRightMemory E).eval
      (pureMatrix C) = pureMatrix (padAliceKeyCoefficient C) := by
  rw [eval_singleOperator_pureMatrix,keyPaddingChannel_map_star,keyPaddingChannel_coeff]

end QuantumProver.AmplitudeDamping.SecretKey.PhysicalPurification

namespace QuantumProver.AmplitudeDamping.SecretKey.PhysicalProtocol.FiniteKeyProtocol

open PhysicalPurification PublicHistory

variable {p : ℝ} {a b af bf d : ℕ} {E : Type*}
  [Fintype E] [DecidableEq E]

def retainedProtocolPrivateLiftChannel (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (P : FiniteKeyProtocol p a b af bf)
    (labelA : Fin af → Fin d) (labelB : Fin bf → Fin d) :
    KrausChannel ((Fin a × Fin b) × E)
      (((Fin d × ((P.comparisonPublicHistory_B × Fin af) ⊕ (P.Environment × E))) ×
        (Fin d × (P.comparisonPublicHistory_B × Fin bf))) × (P.Environment × E))
      ((Unit × Unit) × Unit) :=
  ((keyPaddingChannel (d := d) (A := P.comparisonPublicHistory_B × Fin af)
      (B := P.comparisonPublicHistory_B × Fin bf) (E := P.Environment × E)).withRightMemory
    (P.Environment × E)).compose
    (((keyRecordingChannel
      (fun x : P.comparisonPublicHistory_B × Fin af => labelA x.2)
      (fun x : P.comparisonPublicHistory_B × Fin bf => labelB x.2)).withRightMemory
      (P.Environment × E)).compose
        (wholeRetainedChannelWithEve_B hp0 hp1 P E))

theorem retainedProtocolPrivateLiftChannel_matrix (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (P : FiniteKeyProtocol p a b af bf)
    (labelA : Fin af → Fin d) (labelB : Fin bf → Fin d)
    (C : Matrix (Fin a × Fin b) E ℂ) :
    (P.retainedProtocolPrivateLiftChannel (E := E) hp0 hp1 labelA labelB).eval (pureMatrix C) =
      pureMatrix (padAliceKeyCoefficient
        (P.retainedProtocolKeyCoefficient hp0 hp1 labelA labelB C)) := by
  rw [retainedProtocolPrivateLiftChannel,KrausChannel.eval_compose,KrausChannel.eval_compose,
    ← retainedProtocolCoefficient_matrix,eval_keyRecordingChannel_pureMatrix,
    eval_keyPaddingChannel_pureMatrix]
  rfl

theorem exists_private_test_of_protocol_candidate_channel (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (P : FiniteKeyProtocol p a b af bf)
    (labelA : Fin af → Fin d) (labelB : Fin bf → Fin d)
    (C : Matrix (Fin a × Fin b) E ℂ) (hC : (Cᴴ * C).trace = 1)
    (hd : 0 < d) (xi : Density (P.Environment × E)) :
    ∃ V : Fin d →
        EuclideanSpace ℂ (((P.comparisonPublicHistory_B × Fin af) ⊕ (P.Environment × E)) ×
          (P.comparisonPublicHistory_B × Fin bf)) ≃ₗᵢ[ℂ]
        EuclideanSpace ℂ (((P.comparisonPublicHistory_B × Fin af) ⊕ (P.Environment × E)) ×
          (P.comparisonPublicHistory_B × Fin bf)),
      squaredFidelity
        (P.finalKeyStateWithPriorEveLabels hp0 hp1 labelA labelB E (density C hC))
        (idealKeyStateAgainst d hd xi) ≤
      PrivateTest.privacyAcceptance V
        (PrivateTest.honestMarginal
          ((P.retainedProtocolPrivateLiftChannel (E := E) hp0 hp1 labelA labelB).onDensity
            (density C hC))).mat := by
  obtain ⟨V,hV⟩ := P.exists_private_test_of_protocol_candidate
    hp0 hp1 labelA labelB C hC hd xi
  refine ⟨V,?_⟩
  change squaredFidelity
    (P.finalKeyStateWithPriorEveLabels hp0 hp1 labelA labelB E (density C hC))
    (idealKeyStateAgainst d hd xi) ≤
    PrivateTest.privacyAcceptance V (partialTraceRight
      ((P.retainedProtocolPrivateLiftChannel (E := E) hp0 hp1 labelA labelB).eval (pureMatrix C)))
  rw [retainedProtocolPrivateLiftChannel_matrix]
  exact hV

end QuantumProver.AmplitudeDamping.SecretKey.PhysicalProtocol.FiniteKeyProtocol

namespace QuantumProver.AmplitudeDamping.SecretKey.PrivateTest

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

def measurementRow (b : J) (S : Matrix I I ℂ) (i : I) : Matrix J I ℂ :=
  Matrix.of fun a j => if a = b then S i j else 0

theorem measurementRow_gram (b : J) (S : Matrix I I ℂ) :
    (∑ i : I, (measurementRow b S i)ᴴ * measurementRow b S i) = Sᴴ * S := by
  ext j k
  simp [measurementRow,Matrix.sum_apply,Matrix.mul_apply,Matrix.conjTranspose_apply,mul_ite]

theorem measurementRow_born (b : J) (S X : Matrix I I ℂ) :
    (∑ i : I, measurementRow b S i * X * (measurementRow b S i)ᴴ) =
      (S * X * Sᴴ).trace • Matrix.single b b (1 : ℂ) := by
  ext a c
  by_cases ha : a = b <;> by_cases hc : c = b
  · subst a
    subst c
    simp [measurementRow,Matrix.sum_apply,Matrix.mul_apply,Matrix.conjTranspose_apply,
      Matrix.trace,Matrix.diag,Finset.sum_mul,Matrix.smul_apply]
  · simp [measurementRow,ha,hc,Ne.symm hc,Matrix.sum_apply,Matrix.mul_apply,
      Matrix.conjTranspose_apply,Matrix.smul_apply]
  · simp [measurementRow,ha,hc,Ne.symm ha,Matrix.sum_apply,Matrix.mul_apply,
      Matrix.conjTranspose_apply,Matrix.smul_apply]
  · simp [measurementRow,ha,hc,Ne.symm ha,Ne.symm hc,Matrix.sum_apply,Matrix.mul_apply,
      Matrix.conjTranspose_apply,Matrix.smul_apply]

def finiteMeasurementKraus (M : J → Matrix I I ℂ) (q : J × I) : Matrix J I ℂ :=
  measurementRow q.1 (CFC.sqrt (M q.1)) q.2

theorem measurement_sqrt_gram {M : Matrix I I ℂ} (hM : M.PosSemidef) :
    (CFC.sqrt M)ᴴ * CFC.sqrt M = M := by
  have hS : (CFC.sqrt M)ᴴ = CFC.sqrt M := (CFC.sqrt_nonneg M).posSemidef.isHermitian
  rw [hS,CFC.sqrt_mul_sqrt_self M hM.nonneg]

theorem measurement_sqrt_trace {M : Matrix I I ℂ} (hM : M.PosSemidef)
    (X : Matrix I I ℂ) :
    (CFC.sqrt M * X * (CFC.sqrt M)ᴴ).trace = (M * X).trace := by
  rw [Matrix.trace_mul_cycle,measurement_sqrt_gram hM]

def finiteMeasurementChannel (M : J → Matrix I I ℂ)
    (hM : ∀ b, (M b).PosSemidef) (hSum : ∑ b, M b = 1) :
    KrausChannel I J (J × I) where
  op := finiteMeasurementKraus M
  complete := by
    simp only [Fintype.sum_prod_type,finiteMeasurementKraus,measurementRow_gram,
      measurement_sqrt_gram (hM _),hSum]

theorem finiteMeasurementChannel_eval (M : J → Matrix I I ℂ)
    (hM : ∀ b, (M b).PosSemidef) (hSum : ∑ b, M b = 1)
    (X : Matrix I I ℂ) :
    (finiteMeasurementChannel M hM hSum).eval X =
      Matrix.diagonal (fun b => (M b * X).trace) := by
  simp only [KrausChannel.eval,finiteMeasurementChannel,Fintype.sum_prod_type,
    finiteMeasurementKraus,measurementRow_born,measurement_sqrt_trace (hM _)]
  ext a c
  by_cases hac : a = c
  · subst c
    simp [Matrix.sum_apply,Matrix.smul_apply,Matrix.diagonal_apply,Matrix.single_apply,eq_comm]
  · have hNo (b : J) : ¬ (b = a ∧ b = c) := by
      rintro ⟨ha,hc⟩
      exact hac (ha.symm.trans hc)
    simp [Matrix.sum_apply,Matrix.smul_apply,Matrix.diagonal_apply,Matrix.single_apply,hac,hNo]

variable {d : ℕ} {A B : Type*} [Fintype A] [Fintype B]
  [DecidableEq A] [DecidableEq B]

def privacyBinaryEffect
    (U : Fin d → EuclideanSpace ℂ (A × B) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (A × B))
    (b : Fin 2) : Matrix ((Fin d × A) × (Fin d × B))
      ((Fin d × A) × (Fin d × B)) ℂ :=
  if b = 0 then privacyEffect U else 1 - privacyEffect U

theorem privacyBinaryEffect_positive
    (U : Fin d → EuclideanSpace ℂ (A × B) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (A × B))
    (hd : 0 < d) (b : Fin 2) : (privacyBinaryEffect U b).PosSemidef := by
  unfold privacyBinaryEffect
  split_ifs
  · exact privacyEffect_posSemidef U
  · exact privacyEffect_complement_posSemidef U hd

theorem privacyBinaryEffect_sum
    (U : Fin d → EuclideanSpace ℂ (A × B) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (A × B)) :
    ∑ b : Fin 2, privacyBinaryEffect U b = 1 := by
  simp only [Fin.sum_univ_two,privacyBinaryEffect,if_pos rfl]
  norm_num

def privacyBinaryChannel
    (U : Fin d → EuclideanSpace ℂ (A × B) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (A × B)) (hd : 0 < d) :
    KrausChannel ((Fin d × A) × (Fin d × B)) (Fin 2)
      (Fin 2 × ((Fin d × A) × (Fin d × B))) :=
  finiteMeasurementChannel (privacyBinaryEffect U)
    (privacyBinaryEffect_positive U hd) (privacyBinaryEffect_sum U)

theorem privacyBinaryChannel_eval
    (U : Fin d → EuclideanSpace ℂ (A × B) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (A × B))
    (hd : 0 < d)
    (X : Matrix ((Fin d × A) × (Fin d × B))
      ((Fin d × A) × (Fin d × B)) ℂ) :
    (privacyBinaryChannel U hd).eval X = Matrix.diagonal (fun b : Fin 2 =>
      if b = 0 then (privacyEffect U * X).trace else X.trace - (privacyEffect U * X).trace) := by
  rw [privacyBinaryChannel,finiteMeasurementChannel_eval]
  congr 1
  funext b
  by_cases hb : b = 0
  · simp [privacyBinaryEffect,hb]
  · simp [privacyBinaryEffect,hb,Matrix.sub_mul,Matrix.one_mul,Matrix.trace_sub]

theorem privacyBinaryChannel_pass
    (U : Fin d → EuclideanSpace ℂ (A × B) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (A × B))
    (hd : 0 < d)
    (X : Matrix ((Fin d × A) × (Fin d × B))
      ((Fin d × A) × (Fin d × B)) ℂ) :
    ((privacyBinaryChannel U hd).eval X 0 0).re = privacyAcceptance U X := by
  rw [privacyBinaryChannel_eval]
  simp only [Matrix.diagonal_apply_eq,if_pos rfl]
  exact privacyEffect_trace U X

theorem privacyBinaryChannel_separable_pass_le
    (U : Fin d → EuclideanSpace ℂ (A × B) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (A × B))
    (hd : 0 < d)
    (rho : Density ((Fin d × A) × (Fin d × B))) (hSep : IsSeparable rho) :
    (((privacyBinaryChannel U hd).onDensity rho).mat 0 0).re ≤ 1 / (d : ℝ) := by
  rw [show ((privacyBinaryChannel U hd).onDensity rho).mat =
    (privacyBinaryChannel U hd).eval rho.mat from rfl,privacyBinaryChannel_pass]
  exact privacyAcceptance_separable_le U rho hSep

end QuantumProver.AmplitudeDamping.SecretKey.PrivateTest

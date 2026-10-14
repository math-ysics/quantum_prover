import Mathlib

noncomputable section

open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix Kronecker

namespace QuantumProver.AmplitudeDamping.SecretKey

def log2 (x : ℝ) : ℝ := Real.log x / Real.log 2

def binaryEntropyBits (x : ℝ) : ℝ := Real.binEntropy x / Real.log 2

def channelCZ (p : ℝ) : ℝ :=
  log2 (1 + (1 - p) * p ^ (p / (1 - p)))

def channelBz (p z : ℝ) : ℝ :=
  log2 (1 + ((1 - p) / (1 - p ^ (1 / (1 - z))) ^ (1 - z)) ^ (1 / z))

structure Density (I : Type*) [Fintype I] where
  mat : Matrix I I ℂ
  positive : mat.PosSemidef
  normalized : mat.trace = 1

structure ProbabilityLaw (J : Type*) [Fintype J] where
  weight : J → ℝ
  nonnegative : ∀ j, 0 ≤ weight j
  normalized : ∑ j, weight j = 1

def partialTraceRight {I E : Type*} [Fintype E]
    (ρ : Matrix (I × E) (I × E) ℂ) : Matrix I I ℂ :=
  fun i k => ∑ e, ρ (i, e) (k, e)

theorem partialTraceRight_posSemidef {I E : Type*} [Fintype E]
    {ρ : Matrix (I × E) (I × E) ℂ} (hρ : ρ.PosSemidef) :
    (partialTraceRight ρ).PosSemidef := by
  have hsum : partialTraceRight ρ =
      ∑ e, ρ.submatrix (fun i => (i, e)) (fun i => (i, e)) := by
    ext i k
    simp only [partialTraceRight, Matrix.sum_apply, Matrix.submatrix_apply]
  rw [hsum]
  apply Matrix.posSemidef_sum
  intro e he
  exact hρ.submatrix (fun i => (i, e))

theorem trace_partialTraceRight {I E : Type*} [Fintype I] [Fintype E]
    (ρ : Matrix (I × E) (I × E) ℂ) : (partialTraceRight ρ).trace = ρ.trace := by
  simp [partialTraceRight, Matrix.trace, Fintype.sum_prod_type]

def partialTraceLeft {I E : Type*} [Fintype I]
    (ρ : Matrix (I × E) (I × E) ℂ) : Matrix E E ℂ :=
  fun e e' => ∑ i, ρ (i, e) (i, e')

theorem partialTraceLeft_posSemidef {I E : Type*} [Fintype I]
    {ρ : Matrix (I × E) (I × E) ℂ} (hρ : ρ.PosSemidef) :
    (partialTraceLeft ρ).PosSemidef := by
  have hsum : partialTraceLeft ρ =
      ∑ i, ρ.submatrix (fun e => (i, e)) (fun e => (i, e)) := by
    ext e e'
    simp only [partialTraceLeft, Matrix.sum_apply, Matrix.submatrix_apply]
  rw [hsum]
  apply Matrix.posSemidef_sum
  intro i hi
  exact hρ.submatrix (fun e => (i, e))

theorem trace_partialTraceLeft {I E : Type*} [Fintype I] [Fintype E]
    (ρ : Matrix (I × E) (I × E) ℂ) : (partialTraceLeft ρ).trace = ρ.trace := by
  simp only [partialTraceLeft, Matrix.trace, Matrix.diag, Fintype.sum_prod_type]
  exact Finset.sum_comm

namespace Density

def tensor {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A]
    [DecidableEq B] (ρ : Density A) (σ : Density B) : Density (A × B) where
  mat := ρ.mat ⊗ₖ σ.mat
  positive := ρ.positive.kronecker σ.positive
  normalized := by rw [Matrix.trace_kronecker, ρ.normalized, σ.normalized, one_mul]

def marginalRight {A E : Type*} [Fintype A] [Fintype E]
    (ρ : Density (A × E)) : Density E where
  mat := partialTraceLeft ρ.mat
  positive := partialTraceLeft_posSemidef ρ.positive
  normalized := (trace_partialTraceLeft ρ.mat).trans ρ.normalized

end Density

def traceNorm {I : Type*} [Fintype I] [DecidableEq I]
    (M : Matrix I I ℂ) : ℝ := (CFC.abs M).trace.re

def rootFidelity {I : Type*} [Fintype I] [DecidableEq I]
    (ρ σ : Density I) : ℝ := traceNorm (CFC.sqrt ρ.mat * CFC.sqrt σ.mat)

def squaredFidelity {I : Type*} [Fintype I] [DecidableEq I]
    (ρ σ : Density I) : ℝ := (rootFidelity ρ σ) ^ 2

structure KrausChannel (I O J : Type*) [Fintype I] [Fintype O] [Fintype J]
    [DecidableEq I] where
  op : J → Matrix O I ℂ
  complete : ∑ j, (op j)ᴴ * op j = 1

namespace KrausChannel

variable {I O J : Type*} [Fintype I] [Fintype O] [Fintype J] [DecidableEq I]

def eval (C : KrausChannel I O J) (ρ : Matrix I I ℂ) : Matrix O O ℂ :=
  ∑ j, C.op j * ρ * (C.op j)ᴴ

theorem eval_posSemidef (C : KrausChannel I O J) {ρ : Matrix I I ℂ}
    (hρ : ρ.PosSemidef) : (C.eval ρ).PosSemidef := by
  apply Matrix.posSemidef_sum
  intro j hj
  exact hρ.mul_mul_conjTranspose_same (C.op j)

theorem trace_eval (C : KrausChannel I O J) (ρ : Matrix I I ℂ) :
    (C.eval ρ).trace = ρ.trace := by
  calc
    (C.eval ρ).trace = ∑ j, (C.op j * ρ * (C.op j)ᴴ).trace := by
      simp [eval]
    _ = ∑ j, ((C.op j)ᴴ * C.op j * ρ).trace := by
      apply Finset.sum_congr rfl
      intro j hj
      exact Matrix.trace_mul_cycle _ _ _
    _ = ((∑ j, (C.op j)ᴴ * C.op j) * ρ).trace := by
      rw [Matrix.sum_mul]
      simp
    _ = ρ.trace := by rw [C.complete, Matrix.one_mul]

def onDensity (C : KrausChannel I O J) (ρ : Density I) : Density O where
  mat := C.eval ρ.mat
  positive := C.eval_posSemidef ρ.positive
  normalized := (C.trace_eval ρ.mat).trans ρ.normalized

def stinespring (C : KrausChannel I O J) : Matrix (O × J) I ℂ :=
  fun oj i => C.op oj.2 oj.1 i

theorem stinespring_isometry (C : KrausChannel I O J) :
    C.stinespringᴴ * C.stinespring = 1 := by
  ext i k
  change (∑ oj : O × J, star (C.op oj.2 oj.1 i) * C.op oj.2 oj.1 k) =
    (1 : Matrix I I ℂ) i k
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  have h := congrArg (fun M : Matrix I I ℂ => M i k) C.complete
  simpa only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply] using h

def jointOutput (C : KrausChannel I O J) (ρ : Matrix I I ℂ) :
    Matrix (O × J) (O × J) ℂ := C.stinespring * ρ * C.stinespringᴴ

theorem jointOutput_posSemidef (C : KrausChannel I O J) {ρ : Matrix I I ℂ}
    (hρ : ρ.PosSemidef) : (C.jointOutput ρ).PosSemidef :=
  hρ.mul_mul_conjTranspose_same C.stinespring

theorem trace_jointOutput (C : KrausChannel I O J) (ρ : Matrix I I ℂ) :
    (C.jointOutput ρ).trace = ρ.trace := by
  rw [jointOutput, Matrix.trace_mul_cycle, C.stinespring_isometry, Matrix.one_mul]

theorem partialTrace_jointOutput (C : KrausChannel I O J) (ρ : Matrix I I ℂ) :
    partialTraceRight (C.jointOutput ρ) = C.eval ρ := by
  ext o o'
  simp [partialTraceRight, jointOutput, stinespring, eval, Matrix.sum_apply,
    Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul, Finset.mul_sum]

def withMemory (C : KrausChannel I O J) (A : Type*) [Fintype A]
    [DecidableEq A] : KrausChannel (A × I) (A × O) J where
  op j := (1 : Matrix A A ℂ) ⊗ₖ C.op j
  complete := by
    simp_rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
      ← Matrix.mul_kronecker_mul, Matrix.one_mul]
    have hsum : (∑ j, (1 : Matrix A A ℂ) ⊗ₖ ((C.op j)ᴴ * C.op j)) =
        (1 : Matrix A A ℂ) ⊗ₖ (∑ j, (C.op j)ᴴ * C.op j) := by
      ext x y
      simp only [Matrix.kroneckerMap_apply, Matrix.sum_apply, Finset.mul_sum]
    rw [hsum, C.complete, Matrix.one_kronecker_one]

theorem eval_withMemory_posSemidef (C : KrausChannel I O J) (A : Type*)
    [Fintype A] [DecidableEq A] {ρ : Matrix (A × I) (A × I) ℂ}
    (hρ : ρ.PosSemidef) : ((C.withMemory A).eval ρ).PosSemidef :=
  (C.withMemory A).eval_posSemidef hρ

theorem trace_eval_withMemory (C : KrausChannel I O J) (A : Type*)
    [Fintype A] [DecidableEq A] (ρ : Matrix (A × I) (A × I) ℂ) :
    ((C.withMemory A).eval ρ).trace = ρ.trace :=
  (C.withMemory A).trace_eval ρ

def withRightMemory (C : KrausChannel I O J) (B : Type*) [Fintype B]
    [DecidableEq B] : KrausChannel (I × B) (O × B) J where
  op j := C.op j ⊗ₖ (1 : Matrix B B ℂ)
  complete := by
    simp_rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
      ← Matrix.mul_kronecker_mul, Matrix.one_mul]
    have hsum : (∑ j, ((C.op j)ᴴ * C.op j) ⊗ₖ (1 : Matrix B B ℂ)) =
        (∑ j, (C.op j)ᴴ * C.op j) ⊗ₖ (1 : Matrix B B ℂ) := by
      ext x y
      simp only [Matrix.kroneckerMap_apply, Matrix.sum_apply, Finset.sum_mul]
    rw [hsum, C.complete, Matrix.one_kronecker_one]

def compose {P L : Type*} [Fintype P] [Fintype L] [DecidableEq O]
    (D : KrausChannel O P L) (C : KrausChannel I O J) :
    KrausChannel I P (J × L) where
  op jl := D.op jl.2 * C.op jl.1
  complete := by
    rw [Fintype.sum_prod_type]
    simp_rw [Matrix.conjTranspose_mul]
    calc
      (∑ j, ∑ l, ((C.op j)ᴴ * (D.op l)ᴴ) * (D.op l * C.op j)) =
          ∑ j, (C.op j)ᴴ * (∑ l, (D.op l)ᴴ * D.op l) * C.op j := by
        apply Finset.sum_congr rfl
        intro j hj
        simp [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_assoc]
      _ = ∑ j, (C.op j)ᴴ * C.op j := by
        rw [D.complete]
        simp
      _ = 1 := C.complete

theorem eval_compose {P L : Type*} [Fintype P] [Fintype L] [DecidableEq O]
    (D : KrausChannel O P L) (C : KrausChannel I O J)
    (ρ : Matrix I I ℂ) : (D.compose C).eval ρ = D.eval (C.eval ρ) := by
  simp only [eval, compose, Fintype.sum_prod_type, Matrix.conjTranspose_mul]
  simp_rw [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_assoc]
  exact Finset.sum_comm

end KrausChannel

def basisReadoutChannel {I O : Type*} [Fintype I] [Fintype O]
    [DecidableEq I] [DecidableEq O] (label : I → O) : KrausChannel I O I where
  op i := Matrix.single (label i) i 1
  complete := by
    simp [Matrix.sum_single_one]

theorem basisReadoutChannel_eval {I O : Type*} [Fintype I] [Fintype O]
    [DecidableEq I] [DecidableEq O] (label : I → O) (ρ : Matrix I I ℂ) :
    (basisReadoutChannel label).eval ρ =
      ∑ i, Matrix.single (label i) (label i) (ρ i i) := by
  simp [KrausChannel.eval, basisReadoutChannel]

def splitKeyRegister (d a : ℕ) : Fin (d * a) ≃ Fin d × Fin a :=
  (finProdFinEquiv : Fin d × Fin a ≃ Fin (d * a)).symm

def keyLabels (d a b : ℕ) (i : Fin (d * a) × Fin (d * b)) : Fin d × Fin d :=
  ((splitKeyRegister d a i.1).1, (splitKeyRegister d b i.2).1)

theorem keyReadoutKraus_local (d a b : ℕ) (i : Fin (d * a) × Fin (d * b)) :
    (basisReadoutChannel (keyLabels d a b)).op i =
      Matrix.single (splitKeyRegister d a i.1).1 i.1 (1 : ℂ) ⊗ₖ
        Matrix.single (splitKeyRegister d b i.2).1 i.2 (1 : ℂ) := by
  simp [basisReadoutChannel, keyLabels, Matrix.single_kronecker_single]

def privateKeyReadout {E : Type*} [Fintype E] [DecidableEq E]
    (d a b : ℕ) (ρ : Density ((Fin (d * a) × Fin (d * b)) × E)) :
    Density ((Fin d × Fin d) × E) :=
  ((basisReadoutChannel (keyLabels d a b)).withRightMemory E).onDensity ρ

namespace ProbabilityLaw

variable {J : Type*} [Fintype J] [DecidableEq J]

def copiedMatrix (a : ProbabilityLaw J) : Matrix (J × J) (J × J) ℂ :=
  Matrix.diagonal fun ij => if ij.1 = ij.2 then (a.weight ij.1 : ℂ) else 0

theorem copiedMatrix_posSemidef (a : ProbabilityLaw J) :
    a.copiedMatrix.PosSemidef := by
  apply Matrix.PosSemidef.diagonal
  intro ij
  dsimp
  split_ifs
  · exact_mod_cast a.nonnegative ij.1
  · exact le_refl 0

theorem copiedMatrix_trace (a : ProbabilityLaw J) :
    a.copiedMatrix.trace = 1 := by
  simp only [copiedMatrix, Matrix.trace_diagonal, Fintype.sum_prod_type]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  exact_mod_cast a.normalized

def copiedDensity (a : ProbabilityLaw J) : Density (J × J) where
  mat := a.copiedMatrix
  positive := a.copiedMatrix_posSemidef
  normalized := a.copiedMatrix_trace

def entropyBits (a : ProbabilityLaw J) : ℝ :=
  (∑ j, Real.negMulLog (a.weight j)) / Real.log 2

def coherentSeedVector (a : ProbabilityLaw J) : J × J → ℂ :=
  fun ij => if ij.1 = ij.2 then (Real.sqrt (a.weight ij.1) : ℂ) else 0

def coherentSeedMatrix (a : ProbabilityLaw J) : Matrix (J × J) (J × J) ℂ :=
  Matrix.vecMulVec a.coherentSeedVector (star a.coherentSeedVector)

theorem coherentSeedMatrix_posSemidef (a : ProbabilityLaw J) :
    a.coherentSeedMatrix.PosSemidef :=
  Matrix.posSemidef_vecMulVec_self_star a.coherentSeedVector

theorem coherentSeedMatrix_trace (a : ProbabilityLaw J) :
    a.coherentSeedMatrix.trace = 1 := by
  have hsqrt (j : J) : (Real.sqrt (a.weight j) : ℂ) *
      (Real.sqrt (a.weight j) : ℂ) = (a.weight j : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (a.nonnegative j)]
  have htrace : a.coherentSeedMatrix.trace = ∑ j, (a.weight j : ℂ) := by
    simp [coherentSeedMatrix, coherentSeedVector, Matrix.trace_vecMulVec,
      dotProduct, Fintype.sum_prod_type, hsqrt]
  rw [htrace]
  exact_mod_cast a.normalized

def coherentSeedDensity (a : ProbabilityLaw J) : Density (J × J) where
  mat := a.coherentSeedMatrix
  positive := a.coherentSeedMatrix_posSemidef
  normalized := a.coherentSeedMatrix_trace

def renyiSeedCharge (a : ProbabilityLaw J) (z : ℝ) : ℝ :=
  ((1 + z) / z) * log2 (∑ j, (a.weight j) ^ (1 / (1 + z)))

end ProbabilityLaw

def uniformKeyLaw (d : ℕ) (hd : 0 < d) : ProbabilityLaw (Fin d) where
  weight _ := 1 / (d : ℝ)
  nonnegative _ := one_div_nonneg.mpr (Nat.cast_nonneg d)
  normalized := by
    have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd)
    simp [Finset.sum_const, nsmul_eq_mul, hd']

def idealWholeKeyState {E : Type*} [Fintype E] [DecidableEq E]
    (d : ℕ) (hd : 0 < d) (ρ : Density ((Fin d × Fin d) × E)) :
    Density ((Fin d × Fin d) × E) :=
  ((uniformKeyLaw d hd).copiedDensity).tensor ρ.marginalRight

def wholeKeySquaredFidelity {E : Type*} [Fintype E] [DecidableEq E]
    (d : ℕ) (hd : 0 < d) (ρ : Density ((Fin d × Fin d) × E)) : ℝ :=
  squaredFidelity ρ (idealWholeKeyState d hd ρ)

def idealKeyStateAgainst {E : Type*} [Fintype E] [DecidableEq E]
    (d : ℕ) (hd : 0 < d) (ξ : Density E) :
    Density ((Fin d × Fin d) × E) :=
  ((uniformKeyLaw d hd).copiedDensity).tensor ξ

def optimalWholeKeySquaredFidelity {E : Type*} [Fintype E] [DecidableEq E]
    (d : ℕ) (hd : 0 < d) (ρ : Density ((Fin d × Fin d) × E)) : ℝ :=
  sSup (Set.range fun ξ : Density E => squaredFidelity ρ (idealKeyStateAgainst d hd ξ))

def IsCCQ {E : Type*} [Fintype E] {d : ℕ}
    (ρ : Density ((Fin d × Fin d) × E)) : Prop :=
  ∀ (x y : Fin d × Fin d) (e e' : E), x ≠ y → ρ.mat (x, e) (y, e') = 0

def InSeparableCone {A B : Type*} [Fintype A] [Fintype B]
    (σ : Matrix (A × B) (A × B) ℂ) : Prop :=
  ∃ (k : ℕ) (left : Fin k → Matrix A A ℂ)
    (right : Fin k → Matrix B B ℂ),
    (∀ j, (left j).PosSemidef) ∧ (∀ j, (right j).PosSemidef) ∧
    σ = ∑ j, left j ⊗ₖ right j

def IsSeparable {A B : Type*} [Fintype A] [Fintype B]
    (σ : Density (A × B)) : Prop := InSeparableCone σ.mat

theorem product_mem_separableCone {A B : Type*} [Fintype A] [Fintype B]
    {x : Matrix A A ℂ} {y : Matrix B B ℂ}
    (hx : x.PosSemidef) (hy : y.PosSemidef) : InSeparableCone (x ⊗ₖ y) := by
  refine ⟨1, (fun _ => x), (fun _ => y), (fun _ => hx), (fun _ => hy), ?_⟩
  simp

theorem separableCone_posSemidef {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] {σ : Matrix (A × B) (A × B) ℂ}
    (hσ : InSeparableCone σ) : σ.PosSemidef := by
  obtain ⟨k, left, right, hleft, hright, rfl⟩ := hσ
  apply Matrix.posSemidef_sum
  intro j hj
  exact (hleft j).kronecker (hright j)

def noJumpKraus (p : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1, 0; 0, (Real.sqrt (1 - p) : ℂ)]

def jumpKraus (p : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, (Real.sqrt p : ℂ); 0, 0]

def amplitudeDampingKraus (p : ℝ) : Fin 2 → Matrix (Fin 2) (Fin 2) ℂ :=
  ![noJumpKraus p, jumpKraus p]

theorem amplitudeDamping_complete {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ∑ j, (amplitudeDampingKraus p j)ᴴ * amplitudeDampingKraus p j = 1 := by
  have hsqp : (Real.sqrt p : ℂ) * (Real.sqrt p : ℂ) = (p : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hp0]
  have hsqq : (Real.sqrt (1 - p) : ℂ) * (Real.sqrt (1 - p) : ℂ) =
      ((1 - p : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (sub_nonneg.mpr hp1)]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [amplitudeDampingKraus, noJumpKraus, jumpKraus, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Fin.sum_univ_two, hsqp, hsqq]

def amplitudeDamping (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    KrausChannel (Fin 2) (Fin 2) (Fin 2) where
  op := amplitudeDampingKraus p
  complete := amplitudeDamping_complete hp0 hp1

namespace PhysicalProtocol

abbrev BipartiteMatrix (a b : ℕ) :=
  Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ

def splitQubit (a : ℕ) : Fin (2 * a) ≃ Fin 2 × Fin a :=
  (finProdFinEquiv : Fin 2 × Fin a ≃ Fin (2 * a)).symm

def transferKraus (p : ℝ) (a b : ℕ) (z : Fin 2) :
    Matrix (Fin a × Fin (2 * b)) (Fin (2 * a) × Fin b) ℂ :=
  fun x y =>
    amplitudeDampingKraus p z (splitQubit b x.2).1 (splitQubit a y.1).1 *
      if x.1 = (splitQubit a y.1).2 ∧ (splitQubit b x.2).2 = y.2
      then 1 else 0

inductive FiniteKeyProtocol (p : ℝ) : ℕ → ℕ → ℕ → ℕ → Type
  | done (a b : ℕ) : FiniteKeyProtocol p a b a b
  | alice {a b ao af bf k : ℕ}
      (C : KrausChannel (Fin a) (Fin ao) (Fin k))
      (next : Fin k → FiniteKeyProtocol p ao b af bf) :
      FiniteKeyProtocol p a b af bf
  | bob {a b bo af bf k : ℕ}
      (C : KrausChannel (Fin b) (Fin bo) (Fin k))
      (next : Fin k → FiniteKeyProtocol p a bo af bf) :
      FiniteKeyProtocol p a b af bf
  | call {a b af bf : ℕ} (next : FiniteKeyProtocol p a (2 * b) af bf) :
      FiniteKeyProtocol p (2 * a) b af bf

namespace FiniteKeyProtocol

def calls {p : ℝ} {a b af bf : ℕ} (P : FiniteKeyProtocol p a b af bf) : ℕ :=
  match P with
  | .done _ _ => 0
  | .alice _ next => Finset.univ.sup fun z => (next z).calls
  | .bob _ next => Finset.univ.sup fun z => (next z).calls
  | .call next => next.calls + 1

def Environment {p : ℝ} {a b af bf : ℕ}
    (P : FiniteKeyProtocol p a b af bf) : Type :=
  match P with
  | .done _ _ => Unit
  | .alice _ next => (z : _) × (next z).Environment
  | .bob _ next => (z : _) × (next z).Environment
  | .call next => Fin 2 × next.Environment

instance environmentFintype {p : ℝ} {a b af bf : ℕ}
    (P : FiniteKeyProtocol p a b af bf) : Fintype P.Environment :=
  match P with
  | .done _ _ => inferInstanceAs (Fintype Unit)
  | .alice (k := k) _ next =>
      letI : ∀ z, Fintype (next z).Environment := fun z => environmentFintype (next z)
      inferInstanceAs (Fintype ((z : Fin k) × (next z).Environment))
  | .bob (k := k) _ next =>
      letI : ∀ z, Fintype (next z).Environment := fun z => environmentFintype (next z)
      inferInstanceAs (Fintype ((z : Fin k) × (next z).Environment))
  | .call next =>
      letI := environmentFintype next
      inferInstanceAs (Fintype (Fin 2 × next.Environment))

def fullOutput {p : ℝ} {a b af bf : ℕ} (P : FiniteKeyProtocol p a b af bf)
    (ρ : BipartiteMatrix a b) :
    Matrix ((Fin af × Fin bf) × P.Environment)
      ((Fin af × Fin bf) × P.Environment) ℂ :=
  match P with
  | .done _ _ => fun x y => ρ x.1 y.1
  | .alice (b := b₀) C next => fun x y =>
      if h : x.2.1 = y.2.1 then
        (next x.2.1).fullOutput
          ((C.op x.2.1 ⊗ₖ (1 : Matrix (Fin b₀) (Fin b₀) ℂ)) * ρ *
            (C.op x.2.1 ⊗ₖ (1 : Matrix (Fin b₀) (Fin b₀) ℂ))ᴴ)
          (x.1, x.2.2) (y.1, h.symm ▸ y.2.2)
      else 0
  | .bob (a := a₀) C next => fun x y =>
      if h : x.2.1 = y.2.1 then
        (next x.2.1).fullOutput
          (((1 : Matrix (Fin a₀) (Fin a₀) ℂ) ⊗ₖ C.op x.2.1) * ρ *
            ((1 : Matrix (Fin a₀) (Fin a₀) ℂ) ⊗ₖ C.op x.2.1)ᴴ)
          (x.1, x.2.2) (y.1, h.symm ▸ y.2.2)
      else 0
  | .call (a := a₀) (b := b₀) next => fun x y =>
      next.fullOutput
        (transferKraus p a₀ b₀ x.2.1 * ρ * (transferKraus p a₀ b₀ y.2.1)ᴴ)
        (x.1, x.2.2) (y.1, y.2.2)

end FiniteKeyProtocol
end PhysicalProtocol

end QuantumProver.AmplitudeDamping.SecretKey

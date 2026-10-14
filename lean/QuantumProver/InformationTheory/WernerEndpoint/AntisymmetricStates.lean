import Mathlib

noncomputable section

namespace QuantumProver.WernerEndpoint

open scoped BigOperators ComplexOrder Matrix Kronecker

def crossDensity {I : Type*} (u v : I → ℂ) : Matrix I I ℂ :=
  fun i j => u i * star (v j)

def pureDensity {I : Type*} (u : I → ℂ) : Matrix I I ℂ := crossDensity u u

def purity {I : Type*} [Fintype I] (ρ : Matrix I I ℂ) : ℝ :=
  (Matrix.trace (ρ * ρ)).re

def vectorNormSq {I : Type*} [Fintype I] (u : I → ℂ) : ℝ :=
  ∑ i, Complex.normSq (u i)

def tensorVector {I : Type*} (u v : I → ℂ) : I × I → ℂ :=
  fun ij => u ij.1 * v ij.2

theorem pureDensity_posSemidef {I : Type*} [Fintype I] (u : I → ℂ) :
    (pureDensity u).PosSemidef :=
  Matrix.posSemidef_vecMulVec_self_star u

theorem pureDensity_trace {I : Type*} [Fintype I] (u : I → ℂ) :
    Matrix.trace (pureDensity u) = (vectorNormSq u : ℂ) := by
  simp [pureDensity, crossDensity, Matrix.trace, vectorNormSq, Complex.mul_conj]

theorem sandwich_crossDensity {I O : Type*} [Fintype I]
    (V : Matrix O I ℂ) (u v : I → ℂ) :
    V * crossDensity u v * V.conjTranspose =
      crossDensity (V.mulVec u) (V.mulVec v) := by
  change V * Matrix.vecMulVec u (star v) * V.conjTranspose =
    Matrix.vecMulVec (V.mulVec u) (star (V.mulVec v))
  rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul]
  congr 1
  ext o
  simp [Matrix.vecMul, Matrix.mulVec, dotProduct, star_sum, star_mul, mul_comm]

def partialTraceLeft {B E : Type*} [Fintype E]
    (ρ : Matrix (B × E) (B × E) ℂ) : Matrix B B ℂ :=
  fun b c => ∑ e, ρ (b, e) (c, e)

def partialTraceRight {B E : Type*} [Fintype B]
    (ρ : Matrix (B × E) (B × E) ℂ) : Matrix E E ℂ :=
  fun e f => ∑ b, ρ (b, e) (b, f)

theorem partialTraceLeft_trace {B E : Type*} [Fintype B] [Fintype E]
    (ρ : Matrix (B × E) (B × E) ℂ) :
    Matrix.trace (partialTraceLeft ρ) = Matrix.trace ρ := by
  simp [Matrix.trace, partialTraceLeft, Fintype.sum_prod_type]

theorem partialTraceRight_trace {B E : Type*} [Fintype B] [Fintype E]
    (ρ : Matrix (B × E) (B × E) ℂ) :
    Matrix.trace (partialTraceRight ρ) = Matrix.trace ρ := by
  simp only [Matrix.trace, Matrix.diag, partialTraceRight, Fintype.sum_prod_type]
  exact Finset.sum_comm

theorem partialTraceLeft_posSemidef {B E : Type*} [Fintype B] [Fintype E]
    (ρ : Matrix (B × E) (B × E) ℂ) (hρ : ρ.PosSemidef) :
    (partialTraceLeft ρ).PosSemidef := by
  have hp := Matrix.posSemidef_sum (Finset.univ : Finset E)
    (fun e _ => hρ.submatrix (fun b : B => (b, e)))
  have heq : partialTraceLeft ρ = ∑ e, ρ.submatrix (fun b : B => (b, e))
      (fun b : B => (b, e)) := by
    ext b c
    simp [partialTraceLeft, Matrix.submatrix_apply, Matrix.sum_apply]
  rw [heq]
  simpa using hp

theorem partialTraceRight_posSemidef {B E : Type*} [Fintype B] [Fintype E]
    (ρ : Matrix (B × E) (B × E) ℂ) (hρ : ρ.PosSemidef) :
    (partialTraceRight ρ).PosSemidef := by
  have hp := Matrix.posSemidef_sum (Finset.univ : Finset B)
    (fun b _ => hρ.submatrix (fun e : E => (b, e)))
  have heq : partialTraceRight ρ = ∑ b, ρ.submatrix (fun e : E => (b, e))
      (fun e : E => (b, e)) := by
    ext e f
    simp [partialTraceRight, Matrix.submatrix_apply, Matrix.sum_apply]
  rw [heq]
  simpa using hp

def crossLeft {B E : Type*} [Fintype E] (U W : Matrix B E ℂ) : Matrix B B ℂ :=
  fun b c => ∑ e, U b e * star (W c e)

def crossRight {B E : Type*} [Fintype B] (U W : Matrix B E ℂ) : Matrix E E ℂ :=
  fun e f => ∑ b, U b e * star (W b f)

def reducedLeft {B E : Type*} [Fintype E] (U : Matrix B E ℂ) : Matrix B B ℂ :=
  crossLeft U U

def reducedRight {B E : Type*} [Fintype B] (U : Matrix B E ℂ) : Matrix E E ℂ :=
  crossRight U U

structure Stinespring (Y B E : Type*) [Fintype Y] [Fintype B] [Fintype E]
    [DecidableEq Y] where
  coeff : Matrix (B × E) Y ℂ
  gram_eq_one : coeff.conjTranspose * coeff = 1

namespace Stinespring

variable {Y B E : Type*} [Fintype Y] [Fintype B] [Fintype E] [DecidableEq Y]

def amplitudes (N : Stinespring Y B E) (u : Y → ℂ) : Matrix B E ℂ :=
  fun b e => ∑ y, N.coeff (b, e) y * u y

theorem amplitudes_add (N : Stinespring Y B E) (u v : Y → ℂ) :
    N.amplitudes (u + v) = N.amplitudes u + N.amplitudes v := by
  ext b e
  simp [amplitudes, mul_add, Finset.sum_add_distrib]

theorem amplitudes_smul (N : Stinespring Y B E) (z : ℂ) (u : Y → ℂ) :
    N.amplitudes (z • u) = z • N.amplitudes u := by
  ext b e
  simp [amplitudes, Finset.mul_sum, mul_left_comm]

def apply (N : Stinespring Y B E) (ρ : Matrix Y Y ℂ) : Matrix B B ℂ :=
  partialTraceLeft (N.coeff * ρ * N.coeff.conjTranspose)

def complement (N : Stinespring Y B E) (ρ : Matrix Y Y ℂ) : Matrix E E ℂ :=
  partialTraceRight (N.coeff * ρ * N.coeff.conjTranspose)

theorem apply_trace (N : Stinespring Y B E) (ρ : Matrix Y Y ℂ) :
    Matrix.trace (N.apply ρ) = Matrix.trace ρ := by
  rw [apply, partialTraceLeft_trace, Matrix.trace_mul_cycle, N.gram_eq_one, Matrix.one_mul]

theorem complement_trace (N : Stinespring Y B E) (ρ : Matrix Y Y ℂ) :
    Matrix.trace (N.complement ρ) = Matrix.trace ρ := by
  rw [complement, partialTraceRight_trace, Matrix.trace_mul_cycle,
    N.gram_eq_one, Matrix.one_mul]

theorem apply_posSemidef (N : Stinespring Y B E) (ρ : Matrix Y Y ℂ)
    (hρ : ρ.PosSemidef) : (N.apply ρ).PosSemidef :=
  partialTraceLeft_posSemidef _ (hρ.mul_mul_conjTranspose_same N.coeff)

theorem complement_posSemidef (N : Stinespring Y B E) (ρ : Matrix Y Y ℂ)
    (hρ : ρ.PosSemidef) : (N.complement ρ).PosSemidef :=
  partialTraceRight_posSemidef _ (hρ.mul_mul_conjTranspose_same N.coeff)

theorem apply_crossDensity (N : Stinespring Y B E) (u v : Y → ℂ) :
    N.apply (crossDensity u v) = crossLeft (N.amplitudes u) (N.amplitudes v) := by
  rw [apply, sandwich_crossDensity]
  rfl

theorem complement_crossDensity (N : Stinespring Y B E) (u v : Y → ℂ) :
    N.complement (crossDensity u v) = crossRight (N.amplitudes u) (N.amplitudes v) := by
  rw [complement, sandwich_crossDensity]
  rfl

theorem apply_pureDensity (N : Stinespring Y B E) (u : Y → ℂ) :
    N.apply (pureDensity u) = reducedLeft (N.amplitudes u) :=
  apply_crossDensity N u u

theorem complement_pureDensity (N : Stinespring Y B E) (u : Y → ℂ) :
    N.complement (pureDensity u) = reducedRight (N.amplitudes u) :=
  complement_crossDensity N u u

theorem amplitudes_normSq (N : Stinespring Y B E) (u : Y → ℂ) :
    vectorNormSq (fun be : B × E => N.amplitudes u be.1 be.2) = vectorNormSq u := by
  have ht := congrArg Complex.re (N.apply_trace (pureDensity u))
  rw [apply_pureDensity] at ht
  have hl : reducedLeft (N.amplitudes u) =
      partialTraceLeft (pureDensity (fun be : B × E => N.amplitudes u be.1 be.2)) := by
    ext b c
    rfl
  rw [hl, partialTraceLeft_trace, pureDensity_trace, pureDensity_trace] at ht
  simpa using ht

def referenceCoeff (N : Stinespring Y B E) (R : Type*) [Fintype R] [DecidableEq R] :
    Matrix ((R × B) × E) (R × Y) ℂ :=
  fun rbe ry => if rbe.1.1 = ry.1 then N.coeff (rbe.1.2, rbe.2) ry.2 else 0

theorem referenceCoeff_isometry (N : Stinespring Y B E) (R : Type*)
    [Fintype R] [DecidableEq R] :
    (N.referenceCoeff R).conjTranspose * N.referenceCoeff R =
      (1 : Matrix (R × Y) (R × Y) ℂ) := by
  ext ⟨r, y⟩ ⟨s, z⟩
  by_cases hrs : r = s
  · subst s
    have hg := congrArg (fun M : Matrix Y Y ℂ => M y z) N.gram_eq_one
    simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, referenceCoeff,
      Fintype.sum_prod_type, apply_ite, mul_ite, ite_mul, Matrix.one_apply] using hg
  · simp [Matrix.mul_apply, Matrix.conjTranspose_apply, referenceCoeff,
      Fintype.sum_prod_type, apply_ite, mul_ite, ite_mul, hrs, Ne.symm hrs]

def withReference (N : Stinespring Y B E) (R : Type*) [Fintype R] [DecidableEq R] :
    Stinespring (R × Y) (R × B) E :=
  ⟨N.referenceCoeff R, N.referenceCoeff_isometry R⟩

def amplify (N : Stinespring Y B E) {R : Type*} [Fintype R] [DecidableEq R]
    (ρ : Matrix (R × Y) (R × Y) ℂ) : Matrix (R × B) (R × B) ℂ :=
  (N.withReference R).apply ρ

theorem amplify_block (N : Stinespring Y B E) {R : Type*} [Fintype R] [DecidableEq R]
    (ρ : Matrix (R × Y) (R × Y) ℂ) (r s : R) (b c : B) :
    N.amplify ρ (r, b) (s, c) = N.apply (fun y z => ρ (r, y) (s, z)) b c := by
  simp [amplify, withReference, apply, partialTraceLeft, Matrix.mul_apply,
    Matrix.conjTranspose_apply, referenceCoeff, Fintype.sum_prod_type,
    apply_ite, mul_ite, ite_mul]
  rfl

theorem apply_completelyPositive (N : Stinespring Y B E) {R : Type*}
    [Fintype R] [DecidableEq R] (ρ : Matrix (R × Y) (R × Y) ℂ)
    (hρ : ρ.PosSemidef) : (N.amplify ρ).PosSemidef :=
  (N.withReference R).apply_posSemidef ρ hρ

theorem amplify_trace (N : Stinespring Y B E) {R : Type*}
    [Fintype R] [DecidableEq R] (ρ : Matrix (R × Y) (R × Y) ℂ) :
    Matrix.trace (N.amplify ρ) = Matrix.trace ρ :=
  (N.withReference R).apply_trace ρ

def columnAmplitude (N : Stinespring Y B E) (y : Y) : Matrix B E ℂ :=
  fun b e => N.coeff (b, e) y

def replicaKernel (N : Stinespring Y B E) : Matrix (Y × Y) (Y × Y) ℂ :=
  fun ij kl => Matrix.trace
    (crossLeft (N.columnAmplitude kl.1) (N.columnAmplitude ij.1) *
     crossLeft (N.columnAmplitude kl.2) (N.columnAmplitude ij.2))

def replicaComplementKernel (N : Stinespring Y B E) : Matrix (Y × Y) (Y × Y) ℂ :=
  fun ij kl => Matrix.trace
    (crossRight (N.columnAmplitude kl.1) (N.columnAmplitude ij.1) *
     crossRight (N.columnAmplitude kl.2) (N.columnAmplitude ij.2))

theorem apply_crossDensity_columns (N : Stinespring Y B E) (u v : Y → ℂ) :
    N.apply (crossDensity u v) = ∑ i, ∑ j, (u i * star (v j)) •
      crossLeft (N.columnAmplitude i) (N.columnAmplitude j) := by
  rw [apply_crossDensity]
  ext b c
  simp only [crossLeft, amplitudes, columnAmplitude, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul, star_sum, star_mul]
  simp only [Finset.sum_mul]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro e he
  ring

theorem replicaKernel_pair (N : Stinespring Y B E) (u v w z : Y → ℂ) :
    dotProduct (star (tensorVector u v)) (N.replicaKernel.mulVec (tensorVector w z)) =
      Matrix.trace (N.apply (crossDensity w u) * N.apply (crossDensity z v)) := by
  rw [apply_crossDensity_columns, apply_crossDensity_columns]
  simp only [Finset.sum_mul, Finset.mul_sum, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, Matrix.trace_sum, Matrix.trace_smul, smul_eq_mul]
  simp only [dotProduct, Matrix.mulVec, tensorVector, replicaKernel, Pi.star_apply,
    Fintype.sum_prod_type, star_mul, Finset.mul_sum]
  conv_lhs =>
    rw [Finset.sum_comm]
    enter [2, j]
    rw [Finset.sum_comm]
    enter [2, k]
    rw [Finset.sum_comm]
  conv_lhs =>
    rw [Finset.sum_comm]
    enter [2, k]
    rw [Finset.sum_comm]
  conv_lhs =>
    rw [Finset.sum_comm]
    enter [2, l]
    rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro l hl
  ring

variable {X A F : Type*} [Fintype X] [Fintype A] [Fintype F] [DecidableEq X]

def tensorCoeff (M : Stinespring X A F) (N : Stinespring Y B E) :
    Matrix ((A × B) × (F × E)) (X × Y) ℂ :=
  fun outenv xy => M.coeff (outenv.1.1, outenv.2.1) xy.1 *
    N.coeff (outenv.1.2, outenv.2.2) xy.2

theorem tensorCoeff_gram (M : Stinespring X A F) (N : Stinespring Y B E) :
    (tensorCoeff M N).conjTranspose * tensorCoeff M N =
      (M.coeff.conjTranspose * M.coeff) ⊗ₖ (N.coeff.conjTranspose * N.coeff) := by
  ext ⟨x, y⟩ ⟨z, w⟩
  simp only [tensorCoeff, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.kroneckerMap_apply, Fintype.sum_prod_type, star_mul]
  simp only [Finset.sum_mul]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro f hf
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro e he
  ring

def tensor (M : Stinespring X A F) (N : Stinespring Y B E) :
    Stinespring (X × Y) (A × B) (F × E) where
  coeff := tensorCoeff M N
  gram_eq_one := by
    rw [tensorCoeff_gram, M.gram_eq_one, N.gram_eq_one, Matrix.one_kronecker_one]

theorem tensor_amplitudes (M : Stinespring X A F) (N : Stinespring Y B E)
    (Ψ : X × Y → ℂ) (ab : A × B) (fe : F × E) :
    (M.tensor N).amplitudes Ψ ab fe =
      ∑ x, ∑ y, M.coeff (ab.1, fe.1) x * N.coeff (ab.2, fe.2) y * Ψ (x, y) := by
  simp [tensor, tensorCoeff, amplitudes, Fintype.sum_prod_type]

theorem tensor_columnAmplitude (M : Stinespring X A F) (N : Stinespring Y B E)
    (xy : X × Y) :
    (M.tensor N).columnAmplitude xy = M.columnAmplitude xy.1 ⊗ₖ N.columnAmplitude xy.2 := by
  ext ab fe
  rfl

end Stinespring

abbrev Edge (d : ℕ) := {p : Fin d × Fin d // p.1 < p.2}

def wedgeScale : ℂ := ((Real.sqrt 2)⁻¹ : ℝ)

def wedgeInclusion (d : ℕ) : Matrix (Fin d × Fin d) (Edge d) ℂ :=
  fun ab e => wedgeScale *
    ((if ab.1 = e.val.1 ∧ ab.2 = e.val.2 then 1 else 0) -
     (if ab.1 = e.val.2 ∧ ab.2 = e.val.1 then 1 else 0))

def antisymmetricChannel (d : ℕ) (ρ : Matrix (Edge d) (Edge d) ℂ) :
    Matrix (Fin d) (Fin d) ℂ :=
  partialTraceLeft (wedgeInclusion d * ρ * (wedgeInclusion d).conjTranspose)

def antisymmetricComplement (d : ℕ) (ρ : Matrix (Edge d) (Edge d) ℂ) :
    Matrix (Fin d) (Fin d) ℂ :=
  partialTraceRight (wedgeInclusion d * ρ * (wedgeInclusion d).conjTranspose)

abbrev Quad (d : ℕ) := (Fin d × Fin d) × (Fin d × Fin d)

def quadSwap12 {d : ℕ} (q : Quad d) : Quad d := ((q.1.2, q.1.1), q.2)
def quadSwap34 {d : ℕ} (q : Quad d) : Quad d := (q.1, (q.2.2, q.2.1))
def quadSwap13 {d : ℕ} (q : Quad d) : Quad d := ((q.2.1, q.1.2), (q.1.1, q.2.2))
def quadSwap14 {d : ℕ} (q : Quad d) : Quad d := ((q.2.2, q.1.2), (q.2.1, q.1.1))
def quadSwap23 {d : ℕ} (q : Quad d) : Quad d := ((q.1.1, q.2.1), (q.1.2, q.2.2))
def quadSwap24 {d : ℕ} (q : Quad d) : Quad d := ((q.1.1, q.2.2), (q.2.1, q.1.2))
def quadPairSwap {d : ℕ} (q : Quad d) : Quad d := (q.2, q.1)

def quadPermMatrix (d : ℕ) (f : Quad d → Quad d) : Matrix (Quad d) (Quad d) ℂ :=
  fun q r => if r = f q then 1 else 0

def quadS12 (d : ℕ) := quadPermMatrix d quadSwap12
def quadS34 (d : ℕ) := quadPermMatrix d quadSwap34
def quadS13 (d : ℕ) := quadPermMatrix d quadSwap13
def quadS14 (d : ℕ) := quadPermMatrix d quadSwap14
def quadS23 (d : ℕ) := quadPermMatrix d quadSwap23
def quadS24 (d : ℕ) := quadPermMatrix d quadSwap24
def quadPairExchange (d : ℕ) := quadPermMatrix d quadPairSwap

def pairAntisymmetrizer (d : ℕ) : Matrix (Quad d) (Quad d) ℂ :=
  (1 / 4 : ℂ) • (1 - quadS12 d - quadS34 d + quadS12 d * quadS34 d)

def sixCosetOperator (d : ℕ) : Matrix (Quad d) (Quad d) ℂ :=
  1 + quadPairExchange d - quadS13 d - quadS14 d - quadS23 d - quadS24 d

def fourAntisymmetrizer (d : ℕ) : Matrix (Quad d) (Quad d) ℂ :=
  (1 / 6 : ℂ) • (sixCosetOperator d * pairAntisymmetrizer d)

def FullyAntisymmetricQuad (d : ℕ) (w : Quad d → ℂ) : Prop :=
  (∀ q, w (quadSwap12 q) = -w q) ∧ (∀ q, w (quadSwap34 q) = -w q) ∧
  (∀ q, w (quadSwap13 q) = -w q) ∧ (∀ q, w (quadSwap14 q) = -w q) ∧
  (∀ q, w (quadSwap23 q) = -w q) ∧ (∀ q, w (quadSwap24 q) = -w q)

def pairWedgeInclusion (d : ℕ) : Matrix (Quad d) (Edge d × Edge d) ℂ :=
  wedgeInclusion d ⊗ₖ wedgeInclusion d

abbrev FourSet (d : ℕ) := {S : Finset (Fin d) // S.card = 4}

def fourSetEdge {d : ℕ} (S : FourSet d) (i j : Fin 4) (hij : i < j) : Edge d :=
  ⟨((S.val.orderEmbOfFin S.property) i, (S.val.orderEmbOfFin S.property) j),
    (S.val.orderEmbOfFin S.property).strictMono hij⟩

def fourFormOmega {d : ℕ} (S : FourSet d) : Edge d × Edge d → ℂ :=
  let ab := fourSetEdge S 0 1 (by decide)
  let ac := fourSetEdge S 0 2 (by decide)
  let ad := fourSetEdge S 0 3 (by decide)
  let bc := fourSetEdge S 1 2 (by decide)
  let bd := fourSetEdge S 1 3 (by decide)
  let cd := fourSetEdge S 2 3 (by decide)
  Pi.single (ab, cd) 1 + Pi.single (cd, ab) 1 -
    Pi.single (ac, bd) 1 - Pi.single (bd, ac) 1 +
    Pi.single (ad, bc) 1 + Pi.single (bc, ad) 1

def fourFormMatrix {d : ℕ} (S : FourSet d) : Matrix (Edge d) (Edge d) ℂ :=
  fun e f => fourFormOmega S (e, f)

def omittedFourSet (t : Fin 5) : FourSet 5 :=
  ⟨Finset.univ.erase t, by simp⟩

def d5FourFormOmega (t : Fin 5) := fourFormOmega (omittedFourSet t)
def d5FourFormMatrix (t : Fin 5) := fourFormMatrix (omittedFourSet t)

@[simp] theorem wedgeScale_star : star wedgeScale = wedgeScale := by
  simp [wedgeScale]

@[simp] theorem wedgeScale_conj : (starRingEnd ℂ) wedgeScale = wedgeScale := by
  simp [wedgeScale]

theorem endpointConj_ite (P : Prop) [Decidable P] (x y : ℂ) :
    (starRingEnd ℂ) (if P then x else y) =
      if P then (starRingEnd ℂ) x else (starRingEnd ℂ) y := by
  split_ifs <;> rfl

theorem wedgeScale_square : wedgeScale * wedgeScale = (1 : ℂ) / 2 := by
  have hr : (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ = (1 : ℝ) / 2 := by
    rw [← mul_inv, ← pow_two, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  simpa [wedgeScale] using congrArg (fun x : ℝ => (x : ℂ)) hr

theorem wedgeInclusion_swap (d : ℕ) (a b : Fin d) (e : Edge d) :
    wedgeInclusion d (b, a) e = -wedgeInclusion d (a, b) e := by
  simp only [wedgeInclusion, and_comm]
  ring

theorem wedgeInclusion_isometry (d : ℕ) :
    (wedgeInclusion d).conjTranspose * wedgeInclusion d =
      (1 : Matrix (Edge d) (Edge d) ℂ) := by
  ext e f
  have he : e.val.1 ≠ e.val.2 := ne_of_lt e.property
  have hf : f.val.1 ≠ f.val.2 := ne_of_lt f.property
  have hrev : ¬(e.val.1 = f.val.2 ∧ e.val.2 = f.val.1) := by
    rintro ⟨h₁, h₂⟩
    have hh := e.property
    rw [h₁, h₂] at hh
    exact (not_lt_of_ge f.property.le) hh
  by_cases hef : e = f
  · subst f
    norm_num [Matrix.mul_apply, Matrix.conjTranspose_apply, wedgeInclusion,
      Fintype.sum_prod_type, endpointConj_ite, map_mul, map_sub, mul_sub, sub_mul,
      Finset.sum_sub_distrib, mul_ite, ite_mul, ite_and, he, Ne.symm he,
      wedgeScale_square]
  · have hval : ¬(e.val.1 = f.val.1 ∧ e.val.2 = f.val.2) := by
      rintro ⟨h₁, h₂⟩
      exact hef (Subtype.ext (Prod.ext h₁ h₂))
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, wedgeInclusion,
      Fintype.sum_prod_type, endpointConj_ite, mul_sub, sub_mul,
      Finset.sum_sub_distrib, mul_ite, ite_mul, ite_and, hef,
      eq_comm, wedgeScale_square]
    all_goals split_ifs <;> simp_all

def antisymmetricStinespring (d : ℕ) : Stinespring (Edge d) (Fin d) (Fin d) :=
  ⟨wedgeInclusion d, wedgeInclusion_isometry d⟩

def wedgeProjector (d : ℕ) : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  wedgeInclusion d * (wedgeInclusion d).conjTranspose

theorem wedgeProjector_posSemidef (d : ℕ) : (wedgeProjector d).PosSemidef :=
  Matrix.posSemidef_self_mul_conjTranspose _

theorem wedgeProjector_idempotent (d : ℕ) :
    wedgeProjector d * wedgeProjector d = wedgeProjector d := by
  unfold wedgeProjector
  calc
    _ = wedgeInclusion d * ((wedgeInclusion d).conjTranspose * wedgeInclusion d) *
        (wedgeInclusion d).conjTranspose := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [wedgeInclusion_isometry, Matrix.mul_one]

theorem wedgeProjector_trace (d : ℕ) :
    Matrix.trace (wedgeProjector d) = (Fintype.card (Edge d) : ℂ) := by
  rw [wedgeProjector, Matrix.trace_mul_comm, wedgeInclusion_isometry]
  simp

theorem wedgeInclusion_forward_entry (d : ℕ) (a b : Fin d) (hab : a < b)
    (e : Edge d) :
    wedgeInclusion d (a, b) e = if e = ⟨(a, b), hab⟩ then wedgeScale else 0 := by
  have hrev : ¬(a = e.val.2 ∧ b = e.val.1) := by
    rintro ⟨h₁, h₂⟩
    have hh := hab
    rw [h₁, h₂] at hh
    exact (not_lt_of_ge e.property.le) hh
  by_cases he : e = ⟨(a, b), hab⟩
  · subst e
    simp [wedgeInclusion, ne_of_lt hab, Ne.symm (ne_of_lt hab)]
  · have hpos : ¬(a = e.val.1 ∧ b = e.val.2) := by
      rintro ⟨h₁, h₂⟩
      exact he (Subtype.ext (Prod.ext h₁.symm h₂.symm))
    simp [wedgeInclusion, hpos, hrev, he]

theorem wedgeInclusion_diagonal (d : ℕ) (a : Fin d) (e : Edge d) :
    wedgeInclusion d (a, a) e = 0 := by
  simp [wedgeInclusion, and_comm]

theorem wedgeInclusion_mulVec_forward (d : ℕ) (a b : Fin d) (hab : a < b)
    (u : Edge d → ℂ) :
    (wedgeInclusion d).mulVec u (a, b) = wedgeScale * u ⟨(a, b), hab⟩ := by
  simp [Matrix.mulVec, dotProduct, wedgeInclusion_forward_entry d a b hab, ite_mul]

theorem wedgeInclusion_mulVec_swap (d : ℕ) (a b : Fin d) (u : Edge d → ℂ) :
    (wedgeInclusion d).mulVec u (b, a) = -(wedgeInclusion d).mulVec u (a, b) := by
  simp only [Matrix.mulVec, dotProduct]
  simp_rw [wedgeInclusion_swap d a b, neg_mul]
  simp

theorem wedgeAdjoint_mulVec (d : ℕ) (x : Fin d × Fin d → ℂ) (e : Edge d) :
    (wedgeInclusion d).conjTranspose.mulVec x e =
      wedgeScale * (x e.val - x (e.val.2, e.val.1)) := by
  simp [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, wedgeInclusion,
    Fintype.sum_prod_type, endpointConj_ite,
    mul_sub, sub_mul, Finset.sum_sub_distrib, mul_ite, ite_mul, ite_and]

theorem wedgeProjector_mulVec (d : ℕ) (x : Fin d × Fin d → ℂ) :
    (wedgeProjector d).mulVec x =
      fun ab => (1 / 2 : ℂ) * (x ab - x (ab.2, ab.1)) := by
  ext ⟨a, b⟩
  rw [wedgeProjector, ← Matrix.mulVec_mulVec]
  by_cases hab : a < b
  · rw [wedgeInclusion_mulVec_forward d a b hab, wedgeAdjoint_mulVec]
    rw [← mul_assoc, wedgeScale_square]
  · by_cases hba : b < a
    · rw [wedgeInclusion_mulVec_swap d b a,
        wedgeInclusion_mulVec_forward d b a hba, wedgeAdjoint_mulVec]
      calc
        _ = (wedgeScale * wedgeScale) * (x (a, b) - x (b, a)) := by ring
        _ = _ := by rw [wedgeScale_square]
    · have heq : a = b := le_antisymm (not_lt.mp hba) (not_lt.mp hab)
      subst b
      simp [Matrix.mulVec, dotProduct, wedgeInclusion_diagonal]

def physicalSwap (d : ℕ) : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  fun ab cd => if (ab.2, ab.1) = cd then 1 else 0

theorem wedgeProjector_eq_antisymmetrizer (d : ℕ) :
    wedgeProjector d = (1 / 2 : ℂ) • (1 - physicalSwap d) := by
  ext ⟨a, b⟩ ⟨c, f⟩
  have hh := congrFun (wedgeProjector_mulVec d (Pi.single (c, f) 1)) (a, b)
  simpa [Matrix.mulVec_single_one, Matrix.col, Pi.single_apply, physicalSwap,
    Matrix.one_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul, eq_comm] using hh

def replicaSwap (Y : Type*) [DecidableEq Y] : Matrix (Y × Y) (Y × Y) ℂ :=
  fun ij kl => if ij = (kl.2, kl.1) then 1 else 0

theorem quadPermMatrix_mulVec (d : ℕ) (f : Quad d → Quad d)
    (w : Quad d → ℂ) (q : Quad d) :
    (quadPermMatrix d f).mulVec w q = w (f q) := by
  simp [quadPermMatrix, Matrix.mulVec, dotProduct, ite_mul]

theorem pairAntisymmetrizer_mulVec (d : ℕ) (w : Quad d → ℂ) (q : Quad d) :
    (pairAntisymmetrizer d).mulVec w q = (1 / 4 : ℂ) *
      (w q - w (quadSwap12 q) - w (quadSwap34 q) +
        w (quadSwap34 (quadSwap12 q))) := by
  simp only [pairAntisymmetrizer, Matrix.smul_mulVec, Matrix.add_mulVec,
    Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec,
    quadS12, quadS34, quadPermMatrix_mulVec, Pi.smul_apply, Pi.add_apply,
    Pi.sub_apply, smul_eq_mul]

theorem sixCosetOperator_mulVec (d : ℕ) (w : Quad d → ℂ) (q : Quad d) :
    (sixCosetOperator d).mulVec w q = w q + w (quadPairSwap q) -
      w (quadSwap13 q) - w (quadSwap14 q) - w (quadSwap23 q) - w (quadSwap24 q) := by
  simp only [sixCosetOperator, Matrix.add_mulVec, Matrix.sub_mulVec,
    Matrix.one_mulVec, quadPairExchange, quadS13, quadS14, quadS23, quadS24,
    quadPermMatrix_mulVec, Pi.add_apply, Pi.sub_apply]

theorem fourAntisymmetrizer_mulVec (d : ℕ) (w : Quad d → ℂ) (q : Quad d) :
    (fourAntisymmetrizer d).mulVec w q = (1 / 6 : ℂ) *
      ((pairAntisymmetrizer d).mulVec w q +
       (pairAntisymmetrizer d).mulVec w (quadPairSwap q) -
       (pairAntisymmetrizer d).mulVec w (quadSwap13 q) -
       (pairAntisymmetrizer d).mulVec w (quadSwap14 q) -
       (pairAntisymmetrizer d).mulVec w (quadSwap23 q) -
       (pairAntisymmetrizer d).mulVec w (quadSwap24 q)) := by
  simp only [fourAntisymmetrizer, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec,
    sixCosetOperator_mulVec, Pi.smul_apply, smul_eq_mul]

theorem fourAntisymmetrizer_fully_antisymmetric (d : ℕ) (w : Quad d → ℂ) :
    FullyAntisymmetricQuad d ((fourAntisymmetrizer d).mulVec w) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro q <;>
    simp only [fourAntisymmetrizer_mulVec, pairAntisymmetrizer_mulVec,
      quadSwap12, quadSwap34, quadSwap13, quadSwap14, quadSwap23, quadSwap24,
      quadPairSwap] <;> ring

theorem pairAntisymmetrizer_fixes (d : ℕ) (w : Quad d → ℂ)
    (h12 : ∀ q, w (quadSwap12 q) = -w q)
    (h34 : ∀ q, w (quadSwap34 q) = -w q) :
    (pairAntisymmetrizer d).mulVec w = w := by
  ext q
  rw [pairAntisymmetrizer_mulVec, h12, h34, h34, h12]
  ring

theorem fourAntisymmetrizer_fixes (d : ℕ) (w : Quad d → ℂ)
    (hw : FullyAntisymmetricQuad d w) :
    (fourAntisymmetrizer d).mulVec w = w := by
  rcases hw with ⟨h12, h34, h13, h14, h23, h24⟩
  have hp := pairAntisymmetrizer_fixes d w h12 h34
  have hpair (q : Quad d) : w (quadPairSwap q) = w q := by
    have h := h13 (quadSwap24 q)
    change w (quadPairSwap q) = -w (quadSwap24 q) at h
    simpa only [h24, neg_neg] using h
  ext q
  rw [fourAntisymmetrizer_mulVec]
  simp only [hp, hpair, h13, h14, h23, h24]
  ring

theorem fourAntisymmetrizer_idempotent (d : ℕ) :
    fourAntisymmetrizer d * fourAntisymmetrizer d = fourAntisymmetrizer d := by
  apply Matrix.ext_iff_mulVec.mpr
  intro w
  rw [← Matrix.mulVec_mulVec]
  exact fourAntisymmetrizer_fixes d _ (fourAntisymmetrizer_fully_antisymmetric d w)

theorem quadPermMatrix_mul (d : ℕ) (f g : Quad d → Quad d) :
    quadPermMatrix d f * quadPermMatrix d g = quadPermMatrix d (g ∘ f) := by
  apply Matrix.ext_iff_mulVec.mpr
  intro w
  ext q
  simp only [← Matrix.mulVec_mulVec, quadPermMatrix_mulVec, Function.comp_apply]

theorem quadPermMatrix_hermitian (d : ℕ) (f : Quad d → Quad d)
    (hf : Function.Involutive f) :
    (quadPermMatrix d f).conjTranspose = quadPermMatrix d f := by
  ext q r
  have heq : q = f r ↔ r = f q := by
    constructor <;> intro h
    · simpa only [hf r] using (congrArg f h).symm
    · simpa only [hf q] using (congrArg f h).symm
  simp [Matrix.conjTranspose_apply, quadPermMatrix, endpointConj_ite, heq]

@[simp] theorem quadS12_hermitian (d : ℕ) : (quadS12 d).conjTranspose = quadS12 d :=
  quadPermMatrix_hermitian d _ (by intro q; rfl)
@[simp] theorem quadS34_hermitian (d : ℕ) : (quadS34 d).conjTranspose = quadS34 d :=
  quadPermMatrix_hermitian d _ (by intro q; rfl)
@[simp] theorem quadS13_hermitian (d : ℕ) : (quadS13 d).conjTranspose = quadS13 d :=
  quadPermMatrix_hermitian d _ (by intro q; rfl)
@[simp] theorem quadS14_hermitian (d : ℕ) : (quadS14 d).conjTranspose = quadS14 d :=
  quadPermMatrix_hermitian d _ (by intro q; rfl)
@[simp] theorem quadS23_hermitian (d : ℕ) : (quadS23 d).conjTranspose = quadS23 d :=
  quadPermMatrix_hermitian d _ (by intro q; rfl)
@[simp] theorem quadS24_hermitian (d : ℕ) : (quadS24 d).conjTranspose = quadS24 d :=
  quadPermMatrix_hermitian d _ (by intro q; rfl)
@[simp] theorem quadPairExchange_hermitian (d : ℕ) :
    (quadPairExchange d).conjTranspose = quadPairExchange d :=
  quadPermMatrix_hermitian d _ (by intro q; rfl)

theorem quadS12_commute_quadS34 (d : ℕ) : quadS12 d * quadS34 d = quadS34 d * quadS12 d := by
  simp only [quadS12, quadS34, quadPermMatrix_mul]
  rfl

theorem pairAntisymmetrizer_hermitian (d : ℕ) :
    (pairAntisymmetrizer d).conjTranspose = pairAntisymmetrizer d := by
  simp only [pairAntisymmetrizer, Matrix.conjTranspose_smul, Matrix.conjTranspose_add,
    Matrix.conjTranspose_sub, Matrix.conjTranspose_one, Matrix.conjTranspose_mul,
    quadS12_hermitian, quadS34_hermitian, ← quadS12_commute_quadS34]
  norm_num

theorem sixCosetOperator_hermitian (d : ℕ) :
    (sixCosetOperator d).conjTranspose = sixCosetOperator d := by
  simp [sixCosetOperator]

theorem sixCosetOperator_commute_pair (d : ℕ) :
    sixCosetOperator d * pairAntisymmetrizer d =
      pairAntisymmetrizer d * sixCosetOperator d := by
  apply Matrix.ext_iff_mulVec.mpr
  intro w
  ext q
  simp only [← Matrix.mulVec_mulVec, sixCosetOperator_mulVec, pairAntisymmetrizer_mulVec,
    quadSwap12, quadSwap34, quadSwap13, quadSwap14, quadSwap23, quadSwap24,
    quadPairSwap]
  ring

theorem fourAntisymmetrizer_hermitian (d : ℕ) :
    (fourAntisymmetrizer d).conjTranspose = fourAntisymmetrizer d := by
  simp only [fourAntisymmetrizer, Matrix.conjTranspose_smul, Matrix.conjTranspose_mul,
    pairAntisymmetrizer_hermitian, sixCosetOperator_hermitian,
    ← sixCosetOperator_commute_pair]
  norm_num

theorem pairWedgeInclusion_isometry (d : ℕ) :
    (pairWedgeInclusion d).conjTranspose * pairWedgeInclusion d = 1 := by
  simp only [pairWedgeInclusion, Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
    wedgeInclusion_isometry, Matrix.one_kronecker_one]

theorem pairWedgeInclusion_projector (d : ℕ) :
    pairWedgeInclusion d * (pairWedgeInclusion d).conjTranspose = pairAntisymmetrizer d := by
  simp only [pairWedgeInclusion, Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul]
  change wedgeProjector d ⊗ₖ wedgeProjector d = _
  rw [wedgeProjector_eq_antisymmetrizer]
  have h12 : physicalSwap d ⊗ₖ (1 : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) =
      quadS12 d := by
    ext q r
    simp [Matrix.kroneckerMap_apply, physicalSwap, quadS12, quadPermMatrix,
      quadSwap12, Matrix.one_apply, Prod.ext_iff, eq_comm, ite_mul, mul_ite]
    split_ifs <;> simp_all
  have h34 : (1 : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) ⊗ₖ physicalSwap d =
      quadS34 d := by
    ext q r
    simp [Matrix.kroneckerMap_apply, physicalSwap, quadS34, quadPermMatrix,
      quadSwap34, Matrix.one_apply, Prod.ext_iff, eq_comm, ite_mul, mul_ite]
    split_ifs <;> simp_all
  have h1234 : physicalSwap d ⊗ₖ physicalSwap d = quadS12 d * quadS34 d := by
    rw [← h12, ← h34, ← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul]
  have ht : (1 - physicalSwap d) ⊗ₖ (1 - physicalSwap d) =
      (1 - quadS12 d - quadS34 d + quadS12 d * quadS34 d) := by
    rw [← h1234, ← h12, ← h34,
      ← Matrix.one_kronecker_one (m := Fin d × Fin d) (n := Fin d × Fin d) (α := ℂ)]
    ext q r
    simp only [Matrix.kroneckerMap_apply, Matrix.sub_apply, Matrix.add_apply]
    ring
  rw [Matrix.smul_kronecker, Matrix.kronecker_smul, smul_smul, ht]
  norm_num [pairAntisymmetrizer]

theorem quadPermMatrix_mul_matrix {Y : Type*} (d : ℕ) (f : Quad d → Quad d)
    (M : Matrix (Quad d) Y ℂ) (q : Quad d) (y : Y) :
    (quadPermMatrix d f * M) q y = M (f q) y := by
  simp [quadPermMatrix, Matrix.mul_apply, ite_mul]

theorem quadS12_pairWedge (d : ℕ) :
    quadS12 d * pairWedgeInclusion d = -pairWedgeInclusion d := by
  ext q ij
  simp only [quadS12, quadPermMatrix_mul_matrix, pairWedgeInclusion,
    Matrix.kroneckerMap_apply, quadSwap12, Matrix.neg_apply]
  rw [wedgeInclusion_swap d q.1.1 q.1.2 ij.1, neg_mul]

theorem quadS34_pairWedge (d : ℕ) :
    quadS34 d * pairWedgeInclusion d = -pairWedgeInclusion d := by
  ext q ij
  simp only [quadS34, quadPermMatrix_mul_matrix, pairWedgeInclusion,
    Matrix.kroneckerMap_apply, quadSwap34, Matrix.neg_apply]
  rw [wedgeInclusion_swap d q.2.1 q.2.2 ij.2, mul_neg]

theorem pairAntisymmetrizer_pairWedge (d : ℕ) :
    pairAntisymmetrizer d * pairWedgeInclusion d = pairWedgeInclusion d := by
  rw [← pairWedgeInclusion_projector, Matrix.mul_assoc, pairWedgeInclusion_isometry,
    Matrix.mul_one]

theorem quadS13_conjugate12 (d : ℕ) :
    quadS12 d * quadS13 d * quadS12 d = quadS23 d := by
  simp only [quadS12, quadS13, quadS23, quadPermMatrix_mul]
  rfl

theorem quadS13_conjugate34 (d : ℕ) :
    quadS34 d * quadS13 d * quadS34 d = quadS14 d := by
  simp only [quadS34, quadS13, quadS14, quadPermMatrix_mul]
  rfl

theorem quadS23_conjugate34 (d : ℕ) :
    quadS34 d * quadS23 d * quadS34 d = quadS24 d := by
  simp only [quadS34, quadS23, quadS24, quadPermMatrix_mul]
  rfl

theorem pairWedge_adjoint_quadS12 (d : ℕ) :
    (pairWedgeInclusion d).conjTranspose * quadS12 d =
      -(pairWedgeInclusion d).conjTranspose := by
  have h := congrArg Matrix.conjTranspose (quadS12_pairWedge d)
  simpa only [Matrix.conjTranspose_mul, quadS12_hermitian, Matrix.conjTranspose_neg] using h

theorem pairWedge_adjoint_quadS34 (d : ℕ) :
    (pairWedgeInclusion d).conjTranspose * quadS34 d =
      -(pairWedgeInclusion d).conjTranspose := by
  have h := congrArg Matrix.conjTranspose (quadS34_pairWedge d)
  simpa only [Matrix.conjTranspose_mul, quadS34_hermitian, Matrix.conjTranspose_neg] using h

theorem compressed_crossSwap_eq (d : ℕ) :
    let J := pairWedgeInclusion d
    J.conjTranspose * quadS14 d * J = J.conjTranspose * quadS13 d * J ∧
    J.conjTranspose * quadS23 d * J = J.conjTranspose * quadS13 d * J ∧
    J.conjTranspose * quadS24 d * J = J.conjTranspose * quadS13 d * J := by
  dsimp only
  have h23 : (pairWedgeInclusion d).conjTranspose * quadS23 d * pairWedgeInclusion d =
      (pairWedgeInclusion d).conjTranspose * quadS13 d * pairWedgeInclusion d := by
    rw [← quadS13_conjugate12, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      pairWedge_adjoint_quadS12, Matrix.neg_mul, Matrix.mul_assoc,
      quadS12_pairWedge, Matrix.mul_neg, Matrix.neg_mul, neg_neg]
  have h14 : (pairWedgeInclusion d).conjTranspose * quadS14 d * pairWedgeInclusion d =
      (pairWedgeInclusion d).conjTranspose * quadS13 d * pairWedgeInclusion d := by
    rw [← quadS13_conjugate34, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      pairWedge_adjoint_quadS34, Matrix.neg_mul, Matrix.mul_assoc,
      quadS34_pairWedge, Matrix.mul_neg, Matrix.neg_mul, neg_neg]
  refine ⟨h14, h23, ?_⟩
  rw [← quadS23_conjugate34, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    pairWedge_adjoint_quadS34, Matrix.neg_mul, Matrix.mul_assoc,
    quadS34_pairWedge, Matrix.mul_neg, Matrix.neg_mul, neg_neg, h23]

theorem quadPairExchange_pairWedge (d : ℕ) :
    quadPairExchange d * pairWedgeInclusion d =
      pairWedgeInclusion d * replicaSwap (Edge d) := by
  ext q ⟨i, j⟩
  simp only [quadPairExchange, quadPermMatrix_mul_matrix]
  simp only [Matrix.mul_apply, replicaSwap, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp only [pairWedgeInclusion, Matrix.kroneckerMap_apply, quadPairSwap]
  ring

theorem compressed_pairExchange (d : ℕ) :
    (pairWedgeInclusion d).conjTranspose * quadPairExchange d * pairWedgeInclusion d =
      replicaSwap (Edge d) := by
  rw [Matrix.mul_assoc, quadPairExchange_pairWedge, ← Matrix.mul_assoc,
    pairWedgeInclusion_isometry, Matrix.one_mul]

theorem pairAntisymmetrizer_fourAntisymmetrizer (d : ℕ) :
    pairAntisymmetrizer d * fourAntisymmetrizer d = fourAntisymmetrizer d := by
  apply Matrix.ext_iff_mulVec.mpr
  intro w
  rw [← Matrix.mulVec_mulVec]
  have hw := fourAntisymmetrizer_fully_antisymmetric d w
  exact pairAntisymmetrizer_fixes d _ hw.1 hw.2.1

theorem fourAntisymmetrizer_pairAntisymmetrizer (d : ℕ) :
    fourAntisymmetrizer d * pairAntisymmetrizer d = fourAntisymmetrizer d := by
  have h := congrArg Matrix.conjTranspose (pairAntisymmetrizer_fourAntisymmetrizer d)
  simpa only [Matrix.conjTranspose_mul, pairAntisymmetrizer_hermitian,
    fourAntisymmetrizer_hermitian] using h

theorem fourAntisymmetrizer_posSemidef (d : ℕ) : (fourAntisymmetrizer d).PosSemidef := by
  have h := Matrix.posSemidef_conjTranspose_mul_self (fourAntisymmetrizer d)
  simpa only [fourAntisymmetrizer_hermitian, fourAntisymmetrizer_idempotent] using h

def exteriorReplicaProjector (d : ℕ) : Matrix (Edge d × Edge d) (Edge d × Edge d) ℂ :=
  (pairWedgeInclusion d).conjTranspose * fourAntisymmetrizer d * pairWedgeInclusion d

theorem exteriorReplicaProjector_hermitian (d : ℕ) :
    (exteriorReplicaProjector d).conjTranspose = exteriorReplicaProjector d := by
  simp only [exteriorReplicaProjector, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    fourAntisymmetrizer_hermitian, Matrix.mul_assoc]

theorem exteriorReplicaProjector_idempotent (d : ℕ) :
    exteriorReplicaProjector d * exteriorReplicaProjector d = exteriorReplicaProjector d := by
  change ((pairWedgeInclusion d).conjTranspose * fourAntisymmetrizer d * pairWedgeInclusion d) *
      ((pairWedgeInclusion d).conjTranspose * fourAntisymmetrizer d * pairWedgeInclusion d) = _
  calc
    _ = (pairWedgeInclusion d).conjTranspose *
        (fourAntisymmetrizer d * (pairWedgeInclusion d * (pairWedgeInclusion d).conjTranspose) *
         fourAntisymmetrizer d) * pairWedgeInclusion d := by simp only [Matrix.mul_assoc]
    _ = exteriorReplicaProjector d := by
      rw [pairWedgeInclusion_projector, fourAntisymmetrizer_pairAntisymmetrizer,
        fourAntisymmetrizer_idempotent]
      rfl

theorem exteriorReplicaProjector_posSemidef (d : ℕ) : (exteriorReplicaProjector d).PosSemidef := by
  exact (fourAntisymmetrizer_posSemidef d).conjTranspose_mul_mul_same _

theorem endpointIndicator_and (P Q : Prop) [Decidable P] [Decidable Q] :
    (if P ∧ Q then (1 : ℂ) else 0) =
      (if P then (1 : ℂ) else 0) * (if Q then (1 : ℂ) else 0) := by
  by_cases hP : P <;> by_cases hQ : Q <;> simp [hP, hQ]

theorem fourFormOmega_physical_coset {d : ℕ} (S : FourSet d) :
    (sixCosetOperator d).mulVec
      ((pairWedgeInclusion d).col
        (fourSetEdge S 0 1 (by decide), fourSetEdge S 2 3 (by decide))) =
      (pairWedgeInclusion d).mulVec (fourFormOmega S) := by
  ext q
  simp only [sixCosetOperator_mulVec, fourFormOmega, Matrix.mulVec_add,
    Matrix.mulVec_sub, Matrix.mulVec_single_one, Matrix.col, Matrix.transpose_apply, Pi.add_apply,
    Pi.sub_apply, pairWedgeInclusion, Matrix.kroneckerMap_apply, fourSetEdge,
    quadPairSwap, quadSwap13, quadSwap14, quadSwap23, quadSwap24,
    wedgeInclusion, endpointIndicator_and]
  ring

theorem fourFormOmega_physical_projection {d : ℕ} (S : FourSet d) :
    (fourAntisymmetrizer d).mulVec
      ((pairWedgeInclusion d).col
        (fourSetEdge S 0 1 (by decide), fourSetEdge S 2 3 (by decide))) =
      (1 / 6 : ℂ) • (pairWedgeInclusion d).mulVec (fourFormOmega S) := by
  have hp : (pairAntisymmetrizer d).mulVec
      ((pairWedgeInclusion d).col
        (fourSetEdge S 0 1 (by decide), fourSetEdge S 2 3 (by decide))) =
      (pairWedgeInclusion d).col
        (fourSetEdge S 0 1 (by decide), fourSetEdge S 2 3 (by decide)) := by
    rw [← Matrix.mulVec_single_one, Matrix.mulVec_mulVec, pairAntisymmetrizer_pairWedge,
      Matrix.mulVec_single_one]
  rw [fourAntisymmetrizer, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec, hp,
    fourFormOmega_physical_coset]

theorem exteriorReplicaProjector_fourFormOmega {d : ℕ} (S : FourSet d) :
    (exteriorReplicaProjector d).mulVec (fourFormOmega S) = fourFormOmega S := by
  have h := congrArg (fun w => (fourAntisymmetrizer d).mulVec w)
    (fourFormOmega_physical_projection S)
  rw [Matrix.mulVec_mulVec, fourAntisymmetrizer_idempotent,
    fourFormOmega_physical_projection, Matrix.mulVec_smul] at h
  have hfix : (fourAntisymmetrizer d).mulVec
      ((pairWedgeInclusion d).mulVec (fourFormOmega S)) =
      (pairWedgeInclusion d).mulVec (fourFormOmega S) := by
    have h' := congrArg (fun w => (6 : ℂ) • w) h
    norm_num [smul_smul] at h'
    simpa only [← Matrix.mulVec_mulVec] using h'.symm
  simp only [exteriorReplicaProjector, ← Matrix.mulVec_mulVec, hfix]
  rw [Matrix.mulVec_mulVec, pairWedgeInclusion_isometry, Matrix.one_mulVec]

theorem replicaSwap_mulVec {Y : Type*} [Fintype Y] [DecidableEq Y]
    (w : Y × Y → ℂ) (ij : Y × Y) :
    (replicaSwap Y).mulVec w ij = w (ij.2, ij.1) := by
  have heq (kl : Y × Y) : ij = (kl.2, kl.1) ↔ kl = (ij.2, ij.1) := by
    simp [Prod.ext_iff, eq_comm, and_comm]
  simp [replicaSwap, Matrix.mulVec, dotProduct, heq, ite_mul]

theorem single_replica_swap {Y : Type*} [DecidableEq Y]
    (a b : Y) (x : ℂ) (ij : Y × Y) :
    (Pi.single (a, b) x : Y × Y → ℂ) (ij.2, ij.1) =
      (Pi.single (b, a) x : Y × Y → ℂ) ij := by
  by_cases ha : a = ij.2 <;> by_cases hb : b = ij.1 <;>
    simp [Pi.single_apply, Prod.ext_iff, ha, hb, eq_comm]

theorem fourFormOmega_replicaSwap {d : ℕ} (S : FourSet d) :
    (replicaSwap (Edge d)).mulVec (fourFormOmega S) = fourFormOmega S := by
  ext ij
  rw [replicaSwap_mulVec]
  simp only [fourFormOmega, Pi.add_apply, Pi.sub_apply, single_replica_swap]
  abel

theorem fourAntisymmetrizer_trace (d : ℕ) :
    Matrix.trace (fourAntisymmetrizer d) =
      ((d : ℂ) ^ 4 - 6 * (d : ℂ) ^ 3 + 11 * (d : ℂ) ^ 2 - 6 * (d : ℂ)) / 24 := by
  have hd (q : Quad d) : fourAntisymmetrizer d q q =
      (fourAntisymmetrizer d).mulVec (Pi.single q 1) q := by
    simp [Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite]
  simp only [Matrix.trace, Matrix.diag, hd, fourAntisymmetrizer_mulVec,
    pairAntisymmetrizer_mulVec, Pi.single_apply, quadSwap12, quadSwap34,
    quadSwap13, quadSwap14, quadSwap23, quadSwap24, quadPairSwap]
  norm_num [Fintype.sum_prod_type, Prod.ext_iff, ite_and, eq_comm,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_mul,
    mul_add, mul_sub, add_mul, sub_mul, mul_ite, ite_mul]
  ring

theorem exteriorReplicaProjector_trace (d : ℕ) :
    Matrix.trace (exteriorReplicaProjector d) =
      ((d : ℂ) ^ 4 - 6 * (d : ℂ) ^ 3 + 11 * (d : ℂ) ^ 2 - 6 * (d : ℂ)) / 24 := by
  calc
    _ = Matrix.trace ((pairWedgeInclusion d * (pairWedgeInclusion d).conjTranspose) *
        fourAntisymmetrizer d) := by
      simpa only [exteriorReplicaProjector, Matrix.mul_assoc] using
        Matrix.trace_mul_comm ((pairWedgeInclusion d).conjTranspose * fourAntisymmetrizer d)
          (pairWedgeInclusion d)
    _ = _ := by
      rw [pairWedgeInclusion_projector, pairAntisymmetrizer_fourAntisymmetrizer,
        fourAntisymmetrizer_trace]

theorem exteriorReplicaProjector_trace_d5 : Matrix.trace (exteriorReplicaProjector 5) = 5 := by
  norm_num [exteriorReplicaProjector_trace]

theorem exteriorReplicaProjector_trace_d4 : Matrix.trace (exteriorReplicaProjector 4) = 1 := by
  norm_num [exteriorReplicaProjector_trace]

theorem orthogonalProjector_eq_six_scaled_columns {R K : Type*}
    [Fintype R] [Fintype K] [DecidableEq K]
    (P : Matrix R R ℂ) (M : Matrix R K ℂ)
    (hP : P.conjTranspose = P) (hP2 : P * P = P) (hPM : P * M = M)
    (hGram : M.conjTranspose * M = (6 : ℂ) • (1 : Matrix K K ℂ))
    (htrace : Matrix.trace P = (Fintype.card K : ℂ)) :
    P = (1 / 6 : ℂ) • (M * M.conjTranspose) := by
  let Q : Matrix R R ℂ := (1 / 6 : ℂ) • (M * M.conjTranspose)
  have hQ : Q.conjTranspose = Q := by
    simp only [Q, Matrix.conjTranspose_smul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose]
    norm_num
  have hMM : (M * M.conjTranspose) * (M * M.conjTranspose) =
      (6 : ℂ) • (M * M.conjTranspose) := by
    calc
      _ = M * (M.conjTranspose * M) * M.conjTranspose := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hGram]; simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
  have hQ2 : Q * Q = Q := by
    simp only [Q, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hMM]
    norm_num [smul_smul]
  have hPQ : P * Q = Q := by
    simp only [Q, Matrix.mul_smul, ← Matrix.mul_assoc, hPM]
  have hQP : Q * P = Q := by
    have h := congrArg Matrix.conjTranspose hPQ
    simpa only [Matrix.conjTranspose_mul, hP, hQ] using h
  have htQ : Matrix.trace Q = (Fintype.card K : ℂ) := by
    change Matrix.trace ((1 / 6 : ℂ) • (M * M.conjTranspose)) = _
    rw [Matrix.trace_smul, Matrix.trace_mul_comm, hGram, Matrix.trace_smul,
      Matrix.trace_one]
    ring
  have hD : (P - Q).conjTranspose * (P - Q) = P - Q := by
    rw [Matrix.conjTranspose_sub, hP, hQ]
    calc
      _ = P * P - P * Q - Q * P + Q * Q := by noncomm_ring
      _ = P - Q := by rw [hP2, hPQ, hQP, hQ2]; abel
  have hz : P - Q = 0 := Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp (by
    rw [hD, Matrix.trace_sub, htrace, htQ, sub_self])
  exact sub_eq_zero.mp hz

def symmetricReplicaProjector (X : Type*) [DecidableEq X] : Matrix (X × X) (X × X) ℂ :=
  (1 / 2 : ℂ) • (1 + replicaSwap X)

def positiveReplicaProjector (d : ℕ) : Matrix (Edge d × Edge d) (Edge d × Edge d) ℂ :=
  symmetricReplicaProjector (Edge d) - exteriorReplicaProjector d

def replicaSectorContraction {X Y B E : Type*} [Fintype X] [Fintype Y]
    [Fintype B] [Fintype E] [DecidableEq Y]
    (N : Stinespring Y B E) (A : Matrix Y X ℂ) (P : Matrix (X × X) (X × X) ℂ) : ℝ :=
  (Matrix.trace (N.replicaKernel * (A ⊗ₖ A) * P.transpose *
    (A ⊗ₖ A).conjTranspose)).re

def replicaSectorMass {X Y : Type*} [Fintype X] [Fintype Y]
    (A : Matrix Y X ℂ) (P : Matrix (X × X) (X × X) ℂ) : ℝ :=
  (Matrix.trace ((A ⊗ₖ A) * P.transpose * (A ⊗ₖ A).conjTranspose)).re

theorem matrix_vectorNormSq_scalar {I : Type*} [Fintype I] (u : I → ℂ) (z : ℂ) :
    vectorNormSq (z • u) = Complex.normSq z * vectorNormSq u := by
  simp [vectorNormSq, Pi.smul_apply, smul_eq_mul, Complex.normSq_mul, Finset.mul_sum]

theorem matrix_vectorNormSq_nonneg {I : Type*} [Fintype I] (v : I → ℂ) :
    0 ≤ vectorNormSq v :=
  Finset.sum_nonneg (fun i _ => Complex.normSq_nonneg _)

theorem matrix_vectorNormSq_eq_zero {I : Type*} [Fintype I] (v : I → ℂ)
    (h : vectorNormSq v = 0) : v = 0 := by
  funext i
  have hi := Finset.single_le_sum (fun j _ => Complex.normSq_nonneg (v j))
    (Finset.mem_univ i)
  change Complex.normSq (v i) ≤ vectorNormSq v at hi
  rw [h] at hi
  exact Complex.normSq_eq_zero.mp (le_antisymm hi (Complex.normSq_nonneg _))

theorem matrix_pureDensity_scalar {I : Type*} (v : I → ℂ) (z : ℂ) :
    pureDensity (z • v) = (Complex.normSq z : ℂ) • pureDensity v := by
  have hz : z * star z = (Complex.normSq z : ℂ) := by
    simpa only [Complex.star_def] using Complex.mul_conj z
  ext i j
  simp only [pureDensity, crossDensity, Pi.smul_apply, Matrix.smul_apply,
    smul_eq_mul, star_mul, ← hz]
  ring

theorem matrix_purity_real_scalar {I : Type*} [Fintype I]
    (R : Matrix I I ℂ) (t : ℝ) :
    purity ((t : ℂ) • R) = t ^ 2 * purity R := by
  unfold purity
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.trace_smul,
    smul_eq_mul, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, zero_mul, sub_zero]
  ring

namespace Stinespring

variable {Y B E : Type*} [Fintype Y] [Fintype B] [Fintype E] [DecidableEq Y]

theorem apply_scalar (N : Stinespring Y B E) (ρ : Matrix Y Y ℂ) (z : ℂ) :
    N.apply (z • ρ) = z • N.apply ρ := by
  unfold apply
  rw [Matrix.mul_smul, Matrix.smul_mul]
  ext b c
  simp [partialTraceLeft, Matrix.smul_apply, Finset.mul_sum]

theorem pure_purity_scalar (N : Stinespring Y B E) (v : Y → ℂ) (z : ℂ) :
    purity (N.apply (pureDensity (z • v))) =
      (Complex.normSq z) ^ 2 * purity (N.apply (pureDensity v)) := by
  rw [matrix_pureDensity_scalar, N.apply_scalar, matrix_purity_real_scalar]

theorem pure_purity_homogeneous (N : Stinespring Y B E) (β : ℝ)
    (hbound : ∀ v : Y → ℂ, vectorNormSq v = 1 → purity (N.apply (pureDensity v)) ≤ β)
    (v : Y → ℂ) :
    purity (N.apply (pureDensity v)) ≤ β * (vectorNormSq v) ^ 2 := by
  have hm := matrix_vectorNormSq_nonneg v
  by_cases hz : vectorNormSq v = 0
  · have hv := matrix_vectorNormSq_eq_zero v hz
    rw [hv]
    have hρ : pureDensity (0 : Y → ℂ) = 0 := by
      ext i j
      simp [pureDensity, crossDensity]
    have hN : N.apply (0 : Matrix Y Y ℂ) = 0 := by
      simpa using N.apply_scalar (0 : Matrix Y Y ℂ) 0
    rw [hρ, hN]
    simp [purity, vectorNormSq]
  · have hpos : 0 < vectorNormSq v := lt_of_le_of_ne hm (Ne.symm hz)
    let z : ℂ := ((Real.sqrt (vectorNormSq v))⁻¹ : ℝ)
    have hscale : Complex.normSq z = (vectorNormSq v)⁻¹ := by
      simp only [z, Complex.normSq_ofReal, ← sq, inv_pow]
      rw [Real.sq_sqrt hm]
    have hu : vectorNormSq (z • v) = 1 := by
      rw [matrix_vectorNormSq_scalar, hscale, inv_mul_cancel₀ hz]
    have hb := hbound (z • v) hu
    rw [N.pure_purity_scalar, hscale] at hb
    have hdiv : purity (N.apply (pureDensity v)) / (vectorNormSq v) ^ 2 ≤ β := by
      simpa only [inv_pow, div_eq_mul_inv, mul_comm] using hb
    exact (div_le_iff₀ (sq_pos_of_pos hpos)).mp hdiv

end Stinespring

end QuantumProver.WernerEndpoint

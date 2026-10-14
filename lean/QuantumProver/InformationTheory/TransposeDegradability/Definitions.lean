import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Bilinear
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Register finite matrix semantics for transpose degradability

The environment basis is `Fin 2`. Channels are complex-linear maps on the
entire matrix algebra. Complete positivity quantifies all finite ancillary
spaces, and trace preservation quantifies all complex matrices.
-/

noncomputable section

namespace TransposeDegradability

open Matrix
open scoped ComplexOrder

abbrev Qubit := Fin 2

variable {I J K R C : Type}

/-- Trace the second tensor factor, with no normalization. -/
def partialTraceRight [Fintype J]
    (X : Matrix (I × J) (I × J) ℂ) : Matrix I I ℂ :=
  fun i i' => ∑ j, X (i, j) (i', j)

/-- Trace the first tensor factor, with no normalization. -/
def partialTraceLeft [Fintype I]
    (X : Matrix (I × J) (I × J) ℂ) : Matrix J J ℂ :=
  fun j j' => ∑ i, X (i, j) (i, j')

/-- Fixed-basis partial transpose of only the second tensor factor. -/
def partialTransposeRight (X : Matrix (I × J) (I × J) ℂ) :
    Matrix (I × J) (I × J) ℂ :=
  fun p q => X (p.1, q.2) (q.1, p.2)

@[simp] theorem partialTransposeRight_apply
    (X : Matrix (I × J) (I × J) ℂ) (i i' : I) (j j' : J) :
    partialTransposeRight X (i, j) (i', j') = X (i, j') (i', j) := rfl

@[simp] theorem partialTransposeRight_diagonal_block
    (X : Matrix (I × J) (I × J) ℂ) (i i' : I) (j : J) :
    partialTransposeRight X (i, j) (i', j) = X (i, j) (i', j) := rfl

@[simp] theorem partialTransposeRight_involutive
    (X : Matrix (I × J) (I × J) ℂ) :
    partialTransposeRight (partialTransposeRight X) = X := by
  ext p q
  rfl

def partialTraceRightLinear [Fintype J] :
    Matrix (I × J) (I × J) ℂ →ₗ[ℂ] Matrix I I ℂ where
  toFun := partialTraceRight
  map_add' X Y := by
    ext i i'
    simp [partialTraceRight, Finset.sum_add_distrib]
  map_smul' z X := by
    ext i i'
    simp [partialTraceRight, Finset.mul_sum]

def partialTraceLeftLinear [Fintype I] :
    Matrix (I × J) (I × J) ℂ →ₗ[ℂ] Matrix J J ℂ where
  toFun := partialTraceLeft
  map_add' X Y := by
    ext j j'
    simp [partialTraceLeft, Finset.sum_add_distrib]
  map_smul' z X := by
    ext j j'
    simp [partialTraceLeft, Finset.mul_sum]

def transposeLinear : Matrix I I ℂ →ₗ[ℂ] Matrix I I ℂ where
  toFun := Matrix.transpose
  map_add' _X _Y := rfl
  map_smul' _z _X := rfl

@[simp] theorem transposeLinear_apply (X : Matrix I I ℂ) :
    transposeLinear X = Xᵀ := rfl

/-- The reference index is unchanged and the two qubit indices are exchanged. -/
def swapQubitsIndex (p : (R × Qubit) × Qubit) : (R × Qubit) × Qubit :=
  ((p.1.1, p.2), p.1.2)

@[simp] theorem swapQubitsIndex_involutive (p : (R × Qubit) × Qubit) :
    swapQubitsIndex (swapQubitsIndex p) = p := by
  rcases p with ⟨⟨r, q⟩, q'⟩
  rfl

/-- Bosonic support: every row is fixed by the swap on the two qubits.
For a Hermitian matrix, this implies the corresponding column identity. -/
def Bosonic (X : Matrix ((R × Qubit) × Qubit) ((R × Qubit) × Qubit) ℂ) : Prop :=
  ∀ p q, X (swapQubitsIndex p) q = X p q

def firstMarginal
    (X : Matrix ((R × Qubit) × Qubit) ((R × Qubit) × Qubit) ℂ) :
    Matrix (R × Qubit) (R × Qubit) ℂ := partialTraceRight X

/-- Trace the middle factor in a reference/qubit/qubit tensor product. -/
def partialTraceMiddle [Fintype I]
    (X : Matrix ((R × I) × J) ((R × I) × J) ℂ) :
    Matrix (R × J) (R × J) ℂ :=
  fun p q => ∑ e : I, X ((p.1, e), p.2) ((q.1, e), q.2)

def secondMarginal
    (X : Matrix ((R × Qubit) × Qubit) ((R × Qubit) × Qubit) ℂ) :
    Matrix (R × Qubit) (R × Qubit) ℂ := partialTraceMiddle X

/-- Literal row-block order `00=A, 01=B, 10=G, 11=D`. -/
def qubitFactor (A B G D : Matrix R C ℂ) : Matrix ((R × Qubit) × Qubit) C ℂ :=
  fun p c => if p.1.2 = 0 then (if p.2 = 0 then A p.1.1 c else B p.1.1 c)
    else (if p.2 = 0 then G p.1.1 c else D p.1.1 c)

@[simp] theorem qubitFactor_00 (A B G D : Matrix R C ℂ) (r : R) (c : C) :
    qubitFactor A B G D ((r, 0), 0) c = A r c := by simp [qubitFactor]

@[simp] theorem qubitFactor_01 (A B G D : Matrix R C ℂ) (r : R) (c : C) :
    qubitFactor A B G D ((r, 0), 1) c = B r c := by simp [qubitFactor]

@[simp] theorem qubitFactor_10 (A B G D : Matrix R C ℂ) (r : R) (c : C) :
    qubitFactor A B G D ((r, 1), 0) c = G r c := by simp [qubitFactor]

@[simp] theorem qubitFactor_11 (A B G D : Matrix R C ℂ) (r : R) (c : C) :
    qubitFactor A B G D ((r, 1), 1) c = D r c := by simp [qubitFactor]

/-- A positive bosonic joint matrix with both marginals equal to the input. -/
def HasBosonicSelfExtension [Fintype R]
    (ρ : Matrix (R × Qubit) (R × Qubit) ℂ) : Prop :=
  ∃ σ : Matrix ((R × Qubit) × Qubit) ((R × Qubit) × Qubit) ℂ,
    σ.PosSemidef ∧ Bosonic σ ∧ firstMarginal σ = ρ ∧ secondMarginal σ = ρ

/-- Blockwise `id_K ⊗ φ`, defined on all complex matrices. -/
def amplify (φ : Matrix I I ℂ →ₗ[ℂ] Matrix J J ℂ) (K : Type)
    (X : Matrix (K × I) (K × I) ℂ) : Matrix (K × J) (K × J) ℂ :=
  fun p q => φ (fun i i' => X (p.1, i) (q.1, i')) p.2 q.2

/-- Register complete positivity, for every finite ancillary Hilbert space. -/
def CompletelyPositive [Fintype I] [Fintype J]
    (φ : Matrix I I ℂ →ₗ[ℂ] Matrix J J ℂ) : Prop :=
  ∀ (K : Type) [Fintype K] (X : Matrix (K × I) (K × I) ℂ),
    X.PosSemidef → (amplify φ K X).PosSemidef

/-- Trace preservation on the whole complex matrix algebra. -/
def TracePreserving [Fintype I] [Fintype J]
    (φ : Matrix I I ℂ →ₗ[ℂ] Matrix J J ℂ) : Prop :=
  ∀ X, Matrix.trace (φ X) = Matrix.trace X

def CPTP [Fintype I] [Fintype J]
    (φ : Matrix I I ℂ →ₗ[ℂ] Matrix J J ℂ) : Prop :=
  CompletelyPositive φ ∧ TracePreserving φ

theorem partialTraceRight_amplify_of_tracePreserving [Fintype I] [Fintype J]
    (φ : Matrix I I ℂ →ₗ[ℂ] Matrix J J ℂ) (hφ : TracePreserving φ)
    (X : Matrix (K × I) (K × I) ℂ) :
    partialTraceRight (amplify φ K X) = partialTraceRight X := by
  ext k k'
  exact hφ (fun i i' => X (k, i) (k', i'))

set_option backward.isDefEq.respectTransparency false in
theorem partialTraceMiddle_amplify [Fintype K]
    (φ : Matrix I I ℂ →ₗ[ℂ] Matrix J J ℂ)
    (X : Matrix ((R × K) × I) ((R × K) × I) ℂ) :
    partialTraceMiddle (amplify φ (R × K) X) =
      amplify φ R (partialTraceMiddle X) := by
  ext p q
  have hb : (fun i i' => ∑ k : K, X ((p.1, k), i) ((q.1, k), i') : Matrix I I ℂ) =
      ∑ k : K, (fun i i' => X ((p.1, k), i) ((q.1, k), i') : Matrix I I ℂ) := by
    ext i i'
    simp
  simp only [partialTraceMiddle, amplify]
  rw [hb]
  have hm : φ (∑ k : K,
      (fun i i' => X ((p.1, k), i) ((q.1, k), i') : Matrix I I ℂ)) =
      ∑ k : K, φ (fun i i' => X ((p.1, k), i) ((q.1, k), i') : Matrix I I ℂ) :=
    map_sum φ _ _
  simpa only [Matrix.sum_apply] using
    (congrArg (fun M : Matrix J J ℂ => M p.2 q.2) hm).symm

/-- The pure matrix associated with a rectangular purification. -/
def purificationState (Z : Matrix R J ℂ) : Matrix (R × J) (R × J) ℂ :=
  Matrix.vecMulVec (fun p => Z p.1 p.2) (star (fun p => Z p.1 p.2))

@[simp] theorem purificationState_apply (Z : Matrix R J ℂ) (r r' : R) (j j' : J) :
    purificationState Z (r, j) (r', j') = Z r j * star (Z r' j') := rfl

theorem purificationState_posSemidef [Fintype R] [Fintype J] (Z : Matrix R J ℂ) :
    (purificationState Z).PosSemidef :=
  Matrix.posSemidef_vecMulVec_self_star _

@[simp] theorem partialTraceRight_purificationState [Fintype J] (Z : Matrix R J ℂ) :
    partialTraceRight (purificationState Z) = Z * Zᴴ := by
  ext r r'
  simp [partialTraceRight, Matrix.mul_apply, Matrix.conjTranspose_apply]

/-- Unnormalized input Choi matrix in the fixed matrix-unit basis. -/
def choi [DecidableEq I] (φ : Matrix I I ℂ →ₗ[ℂ] Matrix J J ℂ) :
    Matrix (I × J) (I × J) ℂ :=
  fun p q => φ (Matrix.single p.1 q.1 1) p.2 q.2

@[simp] theorem choi_apply [DecidableEq I]
    (φ : Matrix I I ℂ →ₗ[ℂ] Matrix J J ℂ) (i i' : I) (j j' : J) :
    choi φ (i, j) (i', j') = φ (Matrix.single i i' 1) j j' := rfl

theorem choi_injective [Fintype I] [DecidableEq I]
    {φ ψ : Matrix I I ℂ →ₗ[ℂ] Matrix J J ℂ} (h : choi φ = choi ψ) : φ = ψ := by
  apply Matrix.ext_linearMap
  intro i i'
  apply LinearMap.ext
  intro z
  have hb : φ (Matrix.single i i' 1) = ψ (Matrix.single i i' 1) := by
    ext j j'
    exact congrArg (fun X : Matrix (I × J) (I × J) ℂ => X (i, j) (i', j')) h
  have hz : Matrix.single i i' z = z • Matrix.single i i' (1 : ℂ) := by
    simp [Matrix.smul_single]
  change φ (Matrix.single i i' z) = ψ (Matrix.single i i' z)
  rw [hz, map_smul, map_smul, hb]

@[simp] theorem choi_comp [DecidableEq I]
    (φ : Matrix I I ℂ →ₗ[ℂ] Matrix J J ℂ)
    (ψ : Matrix J J ℂ →ₗ[ℂ] Matrix K K ℂ) :
    choi (ψ.comp φ) = amplify ψ I (choi φ) := by
  ext p q
  rfl

@[simp] theorem choi_transpose_comp [DecidableEq I]
    (φ : Matrix I I ℂ →ₗ[ℂ] Matrix J J ℂ) :
    choi (transposeLinear.comp φ) = partialTransposeRight (choi φ) := by
  ext p q
  rfl

/-- Register rectangular conjugation; the adjoint acts on the output index. -/
def sandwichLinear [Fintype I] [Fintype J] (V : Matrix J I ℂ) :
    Matrix I I ℂ →ₗ[ℂ] Matrix J J ℂ where
  toFun X := V * X * Vᴴ
  map_add' X Y := by simp [Matrix.mul_add, Matrix.add_mul]
  map_smul' z X := by simp [Matrix.mul_smul, Matrix.smul_mul]

@[simp] theorem sandwichLinear_apply [Fintype I] [Fintype J]
    (V : Matrix J I ℂ) (X : Matrix I I ℂ) :
    sandwichLinear V X = V * X * Vᴴ := rfl

def stinespringOutput [Fintype I] [Fintype J] [Fintype K]
    (V : Matrix (J × K) I ℂ) : Matrix I I ℂ →ₗ[ℂ] Matrix J J ℂ :=
  partialTraceRightLinear.comp (sandwichLinear V)

def stinespringComplement [Fintype I] [Fintype J] [Fintype K]
    (V : Matrix (J × K) I ℂ) : Matrix I I ℂ →ₗ[ℂ] Matrix K K ℂ :=
  partialTraceLeftLinear.comp (sandwichLinear V)

@[simp] theorem stinespringOutput_apply [Fintype I] [Fintype J] [Fintype K]
    (V : Matrix (J × K) I ℂ) (X : Matrix I I ℂ) :
    stinespringOutput V X = partialTraceRight (V * X * Vᴴ) := rfl

@[simp] theorem stinespringComplement_apply [Fintype I] [Fintype J] [Fintype K]
    (V : Matrix (J × K) I ℂ) (X : Matrix I I ℂ) :
    stinespringComplement V X = partialTraceLeft (V * X * Vᴴ) := rfl

/-- Raw, unnormalized purification in reference/environment/output order. -/
def purificationMatrix (V : Matrix (J × K) I ℂ) : Matrix (I × K) J ℂ :=
  fun p b => V (b, p.2) p.1

theorem purificationMatrix_gram [Fintype I] [Fintype J] [Fintype K] [DecidableEq I]
    (V : Matrix (J × K) I ℂ) :
    (purificationMatrix V)ᴴ * purificationMatrix V = (stinespringOutput V 1)ᵀ := by
  ext b b'
  simp only [purificationMatrix, stinespringOutput_apply, Matrix.mul_one,
    partialTraceRight, Matrix.transpose_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  apply Finset.sum_congr rfl
  intro i _
  exact mul_comm _ _

def IsStinespringIsometry [Fintype I] [Fintype J] [Fintype K] [DecidableEq I]
    (V : Matrix (J × K) I ℂ) : Prop := Vᴴ * V = 1

/-- Full actual output and environment support, as strict quadratic positivity. -/
def SupportMinimal [Fintype I] [Fintype J] [Fintype K] [DecidableEq I]
    (V : Matrix (J × K) I ℂ) : Prop :=
  (stinespringOutput V 1).PosDef ∧ (stinespringComplement V 1).PosDef

theorem purificationMatrix_gram_posDef [Fintype I] [Fintype J] [Fintype K]
    [DecidableEq I] {V : Matrix (J × K) I ℂ} (hV : SupportMinimal V) :
    ((purificationMatrix V)ᴴ * purificationMatrix V).PosDef := by
  rw [purificationMatrix_gram]
  exact hV.1.transpose

def TransposeDegradable [Fintype I] [Fintype J]
    (V : Matrix (J × Qubit) I ℂ) : Prop :=
  ∃ D : Matrix J J ℂ →ₗ[ℂ] Matrix Qubit Qubit ℂ,
    CPTP D ∧ ∀ X, D (stinespringOutput V X) = (stinespringComplement V X)ᵀ

def OrdinaryDegradable [Fintype I] [Fintype J]
    (V : Matrix (J × Qubit) I ℂ) : Prop :=
  ∃ D : Matrix J J ℂ →ₗ[ℂ] Matrix Qubit Qubit ℂ,
    CPTP D ∧ ∀ X, D (stinespringOutput V X) = stinespringComplement V X

def StrictlyTransposeDegradable [Fintype I] [Fintype J]
    (V : Matrix (J × Qubit) I ℂ) : Prop :=
  TransposeDegradable V ∧ ¬ OrdinaryDegradable V

end TransposeDegradability

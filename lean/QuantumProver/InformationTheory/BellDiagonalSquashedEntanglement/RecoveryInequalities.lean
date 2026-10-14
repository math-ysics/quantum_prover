import Mathlib

set_option autoImplicit false

noncomputable section

open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder Matrix
  Matrix.Norms.L2Operator

namespace QuantumProver.BellDiagonalSquashedEntanglement.Geometry

variable {I E : Type*} [Fintype I] [Fintype E]
  [DecidableEq I] [DecidableEq E]

def pureMatrix (v : I → ℂ) : Matrix I I ℂ :=
  Matrix.vecMulVec v (star v)

theorem pureMatrix_posSemidef (v : I → ℂ) :
    (pureMatrix v).PosSemidef :=
  Matrix.posSemidef_vecMulVec_self_star v

theorem pureMatrix_trace (v : I → ℂ) :
    (pureMatrix v).trace = v ⬝ᵥ star v := by
  exact Matrix.trace_vecMulVec v (star v)

def traceRight (A : Matrix (I × E) (I × E) ℂ) : Matrix I I ℂ :=
  fun i j => ∑ e : E, A (i, e) (j, e)

theorem trace_traceRight (A : Matrix (I × E) (I × E) ℂ) :
    (traceRight A).trace = A.trace := by
  simp [traceRight, Matrix.trace, Matrix.diag, Fintype.sum_prod_type]

def columns (v : I × E → ℂ) : Matrix I E ℂ :=
  fun i e => v (i, e)

theorem traceRight_pureMatrix (v : I × E → ℂ) :
    traceRight (pureMatrix v) = columns v * (columns v)ᴴ := by
  ext i j
  simp [traceRight, pureMatrix, columns, Matrix.vecMulVec_apply,
    Matrix.mul_apply, Matrix.conjTranspose_apply]

def sqrtColumns (A : Matrix I I ℂ) : I × I → ℂ :=
  fun p => CFC.sqrt A p.1 p.2

theorem columns_sqrtColumns (A : Matrix I I ℂ) :
    columns (sqrtColumns A) = CFC.sqrt A := rfl

theorem traceRight_pureMatrix_sqrtColumns
    (A : Matrix I I ℂ) (hA : A.PosSemidef) :
    traceRight (pureMatrix (sqrtColumns A)) = A := by
  rw [traceRight_pureMatrix, columns_sqrtColumns]
  have hsqrt : (CFC.sqrt A).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)
  have hs : (CFC.sqrt A)ᴴ = CFC.sqrt A := hsqrt.isHermitian.eq
  rw [hs]
  exact CFC.sqrt_mul_sqrt_self A hA.nonneg

theorem pureMatrix_sqrtColumns_trace
    (A : Matrix I I ℂ) (hA : A.PosSemidef) :
    (pureMatrix (sqrtColumns A)).trace = A.trace := by
  rw [← trace_traceRight, traceRight_pureMatrix_sqrtColumns A hA]

theorem canonicalPurification_isDensity
    (A : Matrix I I ℂ) (hA : A.PosSemidef) (htrace : A.trace = 1) :
    (pureMatrix (sqrtColumns A)).PosSemidef ∧
      (pureMatrix (sqrtColumns A)).trace = 1 ∧
      traceRight (pureMatrix (sqrtColumns A)) = A := by
  exact ⟨pureMatrix_posSemidef _,
    (pureMatrix_sqrtColumns_trace A hA).trans htrace,
    traceRight_pureMatrix_sqrtColumns A hA⟩

end QuantumProver.BellDiagonalSquashedEntanglement.Geometry

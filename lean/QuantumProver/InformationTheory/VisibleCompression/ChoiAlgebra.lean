import Mathlib

/-!
# The unnormalized Choi-purity contraction, in matrix entries

The channel images `K i j` are arbitrary matrices.  Complete positivity is
not needed for this algebraic identity.  Thus the two-copy contraction is
the square trace of the ordinary Choi matrix, with no partial transpose
and no normalized-Choi factor.
-/

namespace VisibleCompression

open scoped BigOperators

/-- Entry form of the unnormalized Choi matrix for matrix-unit images `K`. -/
def choiOfMatrixUnits {I O R : Type*} (K : I → I → Matrix O O R) :
    Matrix (I × O) (I × O) R :=
  fun ia jb => K ia.1 jb.1 ia.2 jb.2

/-- The contraction in Eq. (N) of the dimension-nine proof is exactly
the ordinary Choi purity.  This is a finite symbolic sum, not enumeration. -/
theorem trace_choi_square {I O R : Type*} [Fintype I] [Fintype O]
    [CommSemiring R] (K : I → I → Matrix O O R) :
    Matrix.trace (choiOfMatrixUnits K * choiOfMatrixUnits K) =
      ∑ i, ∑ j, Matrix.trace (K i j * K j i) := by
  classical
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Fintype.sum_prod_type,
    choiOfMatrixUnits]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]

end VisibleCompression

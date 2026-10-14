import QuantumProver.InformationTheory.VisibleCompression.Definitions
import QuantumProver.InformationTheory.VisibleCompression.ChoiAlgebra
import QuantumProver.InformationTheory.VisibleCompression.BlockQuadratic

/-!
# Choi positivity and normalization from an actual CPTP decoder

The completely-positive and trace-preserving hypotheses here are exactly
the operational channel fields in `Definitions`.  No research bound is an
assumption.  The input-output dimensions may be arbitrary finite dimensions.
-/

noncomputable section

namespace VisibleCompression

open scoped BigOperators ComplexOrder

variable {B : Type*} [Fintype B] {d : ℕ}

/-- Unnormalized Choi matrix, with the reference before the output. -/
def channelChoi (Φ : CPTP (Fin d) B) : Matrix (Fin d × B) (Fin d × B) ℂ :=
  choiOfMatrixUnits (fun i j => Φ.map (Matrix.single i j 1))

/-- Coefficients of the unnormalized maximally entangled input vector. -/
def deltaVector (d : ℕ) : Fin d × Fin d → ℂ :=
  fun ia => if ia.1 = ia.2 then 1 else 0

def entangledInput (d : ℕ) : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  Matrix.vecMulVec (deltaVector d) (star (deltaVector d))

theorem entangledInput_posSemidef (d : ℕ) : (entangledInput d).PosSemidef :=
  Matrix.posSemidef_vecMulVec_self_star (deltaVector d)

theorem entangledInput_block (i j : Fin d) :
    (fun a b => entangledInput d (i, a) (j, b)) = Matrix.single i j 1 := by
  ext a b
  by_cases hia : i = a <;> by_cases hjb : j = b <;>
    simp [entangledInput, deltaVector, Matrix.vecMulVec_apply,
      Matrix.single_apply, hia, hjb]

theorem amplify_entangledInput_eq_channelChoi (Φ : CPTP (Fin d) B) :
    amplify Φ.map d (entangledInput d) = channelChoi Φ := by
  ext ia jb
  simp only [amplify, channelChoi, choiOfMatrixUnits, entangledInput_block]

/-- Complete positivity of the physical decoder proves Choi positivity. -/
theorem channelChoi_posSemidef (Φ : CPTP (Fin d) B) :
    (channelChoi Φ).PosSemidef := by
  have hcp := Φ.completelyPositive d (entangledInput d) (entangledInput_posSemidef d)
  rw [amplify_entangledInput_eq_channelChoi] at hcp
  exact hcp

/-- Tracing the output of the unnormalized Choi matrix gives the identity. -/
theorem channelChoi_output_marginal (Φ : CPTP (Fin d) B) (i j : Fin d) :
    ∑ b, channelChoi Φ (i, b) (j, b) = (1 : Matrix (Fin d) (Fin d) ℂ) i j := by
  change (Φ.map (Matrix.single i j 1)).trace = _
  rw [Φ.tracePreserving]
  by_cases hij : i = j
  · subst j
    simp
  · rw [Matrix.trace_single_eq_of_ne i j (1 : ℂ) hij]
    simp [Matrix.one_apply, hij]

theorem channelChoi_trace (Φ : CPTP (Fin d) B) :
    (channelChoi Φ).trace = (d : ℂ) := by
  simp only [Matrix.trace, Matrix.diag, Fintype.sum_prod_type]
  simp_rw [channelChoi_output_marginal]
  simp

theorem channelChoi_sum_outputBlocks [DecidableEq B] (Φ : CPTP (Fin d) B) :
    ∑ b, outputBlock (channelChoi Φ) b = (1 : Matrix (Fin d) (Fin d) ℂ) := by
  ext i j
  simp only [Matrix.sum_apply, outputBlock, Matrix.submatrix_apply]
  exact channelChoi_output_marginal Φ i j

theorem channelChoi_eigenvalues_le_output_dimension [DecidableEq B]
    (Φ : CPTP (Fin d) B) (i : Fin d × B) :
    (channelChoi_posSemidef Φ).isHermitian.eigenvalues i ≤ (Fintype.card B : ℝ) :=
  eigenvalues_le_card_output (channelChoi Φ) (channelChoi_posSemidef Φ)
    (channelChoi_sum_outputBlocks Φ) i

/-- The genuine output-dimension half of the channel-purity estimate,
expressed spectrally so that no imports of the downstream main theorem
are needed. -/
theorem channelChoi_sum_eigenvalues_sq_le_dimensions [DecidableEq B]
    (Φ : CPTP (Fin d) B) :
    (∑ i, (channelChoi_posSemidef Φ).isHermitian.eigenvalues i ^ 2) ≤
      (Fintype.card B : ℝ) * (d : ℝ) := by
  have h := sum_eigenvalues_sq_le_output_card_mul_trace (channelChoi Φ)
    (channelChoi_posSemidef Φ) (channelChoi_sum_outputBlocks Φ)
  rw [channelChoi_trace] at h
  simpa using h

/-- Exact channel version of the contraction identity. -/
theorem channelChoi_trace_square (Φ : CPTP (Fin d) B) :
    (channelChoi Φ * channelChoi Φ).trace =
      ∑ i, ∑ j, (Φ.map (Matrix.single i j 1) * Φ.map (Matrix.single j i 1)).trace :=
  trace_choi_square _

end VisibleCompression

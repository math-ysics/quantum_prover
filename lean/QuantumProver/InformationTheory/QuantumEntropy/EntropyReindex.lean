import QuantumProver.InformationTheory.QuantumEntropy.Definitions
import QuantumProver.InformationTheory.QuantumEntropy.TensorReindex

set_option autoImplicit false

noncomputable section

open Matrix
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace QuantumProver.QuantumEntropy

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

def reindexStarAlgHom (e : I ≃ J) : Matrix I I ℂ →⋆ₐ[ℝ] Matrix J J ℂ :=
  { (Matrix.reindexAlgEquiv ℝ ℂ e).toAlgHom with
    map_star' := by
      intro X
      ext i j
      rfl }

theorem reindexStarAlgHom_continuous (e : I ≃ J) :
    Continuous (reindexStarAlgHom e) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  change Continuous (fun X : Matrix I I ℂ => X (e.symm i) (e.symm j))
  fun_prop

theorem cfc_reindex (e : I ≃ J) (f : ℝ → ℝ) {X : Matrix I I ℂ}
    (hX : X.IsHermitian) :
    cfc f (Matrix.reindex e e X) = Matrix.reindex e e (cfc f X) := by
  exact ((reindexStarAlgHom e).map_cfc f X (X.finite_real_spectrum.continuousOn _)
    (reindexStarAlgHom_continuous e) hX (hX.submatrix e.symm)).symm

theorem entropyBits_reindex (e : I ≃ J) {X : Matrix I I ℂ}
    (hX : X.IsHermitian) :
    entropyBits (Matrix.reindex e e X) = entropyBits X := by
  change QuantumProver.SuperchannelDiscrimination.FlaggedStates.entropyBits
      (Matrix.reindex e e X) =
    QuantumProver.SuperchannelDiscrimination.FlaggedStates.entropyBits X
  rw [QuantumProver.SuperchannelDiscrimination.FlaggedStates.entropyBits,
    cfc_reindex e _ hX, trace_reindex]
  rfl

theorem entropyNats_reindex (e : I ≃ J) {X : Matrix I I ℂ}
    (hX : X.IsHermitian) :
    entropyNats (Matrix.reindex e e X) = entropyNats X := by
  calc
    entropyNats (Matrix.reindex e e X) =
        entropyBits (Matrix.reindex e e X) * Real.log 2 :=
      entropyNats_eq_entropyBits_mul_log_two _
    _ = entropyBits X * Real.log 2 :=
      congrArg (fun h : ℝ => h * Real.log 2) (entropyBits_reindex e hX)
    _ = entropyNats X := (entropyNats_eq_entropyBits_mul_log_two X).symm

end QuantumProver.QuantumEntropy

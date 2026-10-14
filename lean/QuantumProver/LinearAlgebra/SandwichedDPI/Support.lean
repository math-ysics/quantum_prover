import Mathlib
import QuantumProver.InformationTheory.AmplitudeDamping.QuantumCapacity.Definitions
import QuantumProver.InformationTheory.QuantumEntropy.PartialTraceKraus

set_option autoImplicit false

noncomputable section

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace QuantumProver.SandwichedDPI

open QuantumProver.AmplitudeDamping.FiniteModel
open QuantumProver.SuperchannelDiscrimination.KrausCompletion

variable {I O Z : Type*} [Fintype I] [DecidableEq I]

private theorem range_mulVecLin_le_iff {ρ σ : Matrix I I ℂ} :
    LinearMap.range ρ.mulVecLin ≤ LinearMap.range σ.mulVecLin ↔
      LinearMap.range ρ.toEuclideanLin ≤ LinearMap.range σ.toEuclideanLin := by
  constructor
  · intro h y hy
    obtain ⟨x, hx⟩ := hy
    have hx' : ρ.mulVecLin (WithLp.ofLp x) = WithLp.ofLp y :=
      congrArg (fun v : EuclideanSpace ℂ I => WithLp.ofLp v) hx
    obtain ⟨w, hw⟩ := h ⟨WithLp.ofLp x, hx'⟩
    refine ⟨WithLp.toLp 2 w, ?_⟩
    apply WithLp.ofLp_injective 2
    exact hw
  · intro h y hy
    obtain ⟨x, hx⟩ := hy
    have hx' : ρ.toEuclideanLin (WithLp.toLp 2 x) = WithLp.toLp 2 y :=
      congrArg (WithLp.toLp 2) hx
    obtain ⟨w, hw⟩ := h ⟨WithLp.toLp 2 x, hx'⟩
    refine ⟨WithLp.ofLp w, ?_⟩
    exact congrArg (fun v : EuclideanSpace ℂ I => WithLp.ofLp v) hw

private theorem ker_toEuclideanLin_le_iff {ρ σ : Matrix I I ℂ} :
    LinearMap.ker σ.toEuclideanLin ≤ LinearMap.ker ρ.toEuclideanLin ↔
      LinearMap.ker σ.mulVecLin ≤ LinearMap.ker ρ.mulVecLin := by
  constructor
  · intro h x hx
    have hx' : σ.toEuclideanLin (WithLp.toLp 2 x) = 0 :=
      congrArg (WithLp.toLp 2) hx
    have hy : ρ.toEuclideanLin (WithLp.toLp 2 x) = 0 := h hx'
    exact congrArg (fun v : EuclideanSpace ℂ I => WithLp.ofLp v) hy
  · intro h x hx
    have hx' : σ.mulVecLin (WithLp.ofLp x) = 0 :=
      congrArg (fun v : EuclideanSpace ℂ I => WithLp.ofLp v) hx
    have hy : ρ.mulVecLin (WithLp.ofLp x) = 0 := h hx'
    apply WithLp.ofLp_injective 2
    exact hy

theorem supportLE_iff_ker_le {ρ σ : Matrix I I ℂ}
    (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) :
    SupportLE ρ σ ↔ LinearMap.ker σ.mulVecLin ≤ LinearMap.ker ρ.mulVecLin := by
  have hρadj : ρ.toEuclideanLin.adjoint = ρ.toEuclideanLin :=
    (Matrix.isSymmetric_toEuclideanLin_iff.mpr hρ).adjoint_eq
  have hσadj : σ.toEuclideanLin.adjoint = σ.toEuclideanLin :=
    (Matrix.isSymmetric_toEuclideanLin_iff.mpr hσ).adjoint_eq
  unfold SupportLE
  rw [range_mulVecLin_le_iff, ← Submodule.orthogonal_le_orthogonal_iff,
    LinearMap.orthogonal_range, LinearMap.orthogonal_range, hρadj, hσadj]
  exact ker_toEuclideanLin_le_iff

theorem supportLE_iff_kernel {ρ σ : Matrix I I ℂ}
    (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) :
    SupportLE ρ σ ↔ ∀ x : I → ℂ, σ *ᵥ x = 0 → ρ *ᵥ x = 0 := by
  rw [supportLE_iff_ker_le hρ hσ]
  rfl

variable [Fintype O] [DecidableEq O] [Fintype Z]

theorem supportLE_krausAction (K : Z → Matrix O I ℂ) {ρ σ : Matrix I I ℂ}
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) (hSupport : SupportLE ρ σ) :
    SupportLE (krausAction K ρ) (krausAction K σ) := by
  classical
  apply (supportLE_iff_kernel (krausAction_posSemidef K hρ).1
    (krausAction_posSemidef K hσ).1).mpr
  intro x hx
  have hkernel := (supportLE_iff_kernel hρ.1 hσ.1).mp hSupport
  have hterm (z : Z) : ρ *ᵥ ((K z)ᴴ *ᵥ x) = 0 :=
    hkernel _ (QuantumProver.QuantumEntropy.kraus_lift_kernel K hσ x hx z)
  change (∑ z, K z * ρ * (K z)ᴴ) *ᵥ x = 0
  simp only [Matrix.sum_mulVec, ← Matrix.mulVec_mulVec, hterm,
    Matrix.mulVec_zero, Finset.sum_const_zero]

theorem supportLE_kraus_sum (K : Z → Matrix O I ℂ) {ρ σ : Matrix I I ℂ}
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) (hSupport : SupportLE ρ σ) :
    SupportLE (∑ z, K z * ρ * (K z)ᴴ) (∑ z, K z * σ * (K z)ᴴ) :=
  supportLE_krausAction K hρ hσ hSupport

end QuantumProver.SandwichedDPI

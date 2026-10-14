import Mathlib

set_option autoImplicit false

noncomputable section

open Matrix
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace QuantumProver.MatrixAnalysis.MatrixSqrt

abbrev Mat (I : Type*) := Matrix I I ℂ

abbrev Herm (I : Type*) [Fintype I] [DecidableEq I] :=
  (selfAdjoint.submodule ℝ (Mat I))

variable {I : Type*} [Fintype I] [DecidableEq I]

def positiveCone : Set (Herm I) := {A | (A : Mat I).PosDef}

def spectralFloor (m : ℝ) (A : Mat I) : Prop := (A - m • 1).PosSemidef

def rootFloor (a : ℝ) (A : Mat I) : Prop := (CFC.sqrt A - a • 1).PosSemidef

def sqrtHerm (A : Herm I) : Herm I :=
  ⟨CFC.sqrt (A : Mat I), (CFC.sqrt_nonneg (A : Mat I)).posSemidef.isHermitian.isSelfAdjoint⟩

def hsNorm (X : Mat I) : ℝ := Real.sqrt (Xᴴ * X).trace.re

theorem hsNorm_nonneg (X : Mat I) : 0 ≤ hsNorm X := Real.sqrt_nonneg _

theorem hsNorm_sqrt_of_trace_one {A : Mat I} (hA : A.PosSemidef)
    (hTrace : A.trace = 1) : hsNorm (CFC.sqrt A) = 1 := by
  have hS : (CFC.sqrt A)ᴴ = CFC.sqrt A := (CFC.sqrt_nonneg A).posSemidef.isHermitian
  simp only [hsNorm, hS, CFC.sqrt_mul_sqrt_self A hA.nonneg, hTrace,
    Complex.one_re, Real.sqrt_one]

def sylvester (S X : Mat I) : Mat I := S * X + X * S

def sylvesterLinear (S : Mat I) : Mat I →ₗ[ℂ] Mat I where
  toFun := sylvester S
  map_add' X Y := by simp only [sylvester, mul_add, add_mul]; abel
  map_smul' z X := by simp only [sylvester, Matrix.mul_smul, Matrix.smul_mul, smul_add, RingHom.id_apply]

def sylvesterCLM (S : Mat I) : Mat I →L[ℂ] Mat I :=
  { sylvesterLinear S with
    cont := by
      change Continuous (fun X : Mat I => S * X + X * S)
      fun_prop }

theorem sylvester_injective_of_spectral (S U : Mat I) (lam : I → ℝ)
    (hLam : ∀ i, 0 < lam i) (hU1 : Uᴴ * U = 1) (hU2 : U * Uᴴ = 1)
    (hS : S = U * Matrix.diagonal (fun i => (lam i : ℂ)) * Uᴴ) :
    Function.Injective (sylvester S) := by
  suffices hZero : ∀ X : Mat I, sylvester S X = 0 → X = 0 by
    intro X Y hXY
    have hDifference : sylvester S (X - Y) = 0 := by
      unfold sylvester at hXY ⊢
      simp only [mul_sub, sub_mul]
      calc
        _ = (S * X + X * S) - (S * Y + Y * S) := by abel
        _ = 0 := sub_eq_zero.mpr hXY
    exact sub_eq_zero.mp (hZero (X - Y) hDifference)
  intro X hX
  let D : Mat I := Matrix.diagonal (fun i => (lam i : ℂ))
  let Y : Mat I := Uᴴ * X * U
  have hLeft : Uᴴ * (S * X) * U = D * Y := by
    rw [hS]
    calc
      _ = (Uᴴ * U) * D * (Uᴴ * X * U) := by dsimp only [D]; noncomm_ring
      _ = D * Y := by rw [hU1]; simp only [one_mul, Y]
  have hRight : Uᴴ * (X * S) * U = Y * D := by
    rw [hS]
    calc
      _ = (Uᴴ * X * U) * D * (Uᴴ * U) := by dsimp only [D]; noncomm_ring
      _ = Y * D := by rw [hU1]; simp only [mul_one, Y]
  have hDiagonal : D * Y + Y * D = 0 := by
    rw [← hLeft, ← hRight, ← add_mul, ← mul_add]
    change Uᴴ * sylvester S X * U = 0
    rw [hX]
    simp
  have hY : Y = 0 := by
    ext i j
    have hEntry := congrArg (fun M : Mat I => M i j) hDiagonal
    simp only [D, Matrix.add_apply, Matrix.diagonal_mul, Matrix.mul_diagonal,
      Matrix.zero_apply] at hEntry
    have hSum : ((lam i + lam j : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (ne_of_gt (add_pos (hLam i) (hLam j)))
    have hProduct : ((lam i + lam j : ℝ) : ℂ) * Y i j = 0 := by
      push_cast
      linear_combination hEntry
    exact (mul_eq_zero.mp hProduct).resolve_left hSum
  have hRecover : U * Y * Uᴴ = X := by
    calc
      _ = (U * Uᴴ) * X * (U * Uᴴ) := by dsimp only [Y]; noncomm_ring
      _ = X := by rw [hU2]; simp
  rw [hY] at hRecover
  simpa using hRecover.symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem sylvester_injective {S : Mat I} (hS : S.PosDef) :
    Function.Injective (sylvester S) := by
  let U : Mat I := hS.1.eigenvectorUnitary
  apply sylvester_injective_of_spectral S U hS.1.eigenvalues hS.eigenvalues_pos
  · simpa only [U, star_eq_conjTranspose] using Unitary.coe_star_mul_self hS.1.eigenvectorUnitary
  · simpa only [U, Unitary.coe_star, star_eq_conjTranspose] using Unitary.coe_mul_star_self hS.1.eigenvectorUnitary
  · change S = (hS.1.eigenvectorUnitary : Matrix I I ℂ) *
      Matrix.diagonal (fun i => (hS.1.eigenvalues i : ℂ)) *
      (hS.1.eigenvectorUnitary : Matrix I I ℂ)ᴴ
    simpa [Mat, Unitary.conjStarAlgAut_apply, star_eq_conjTranspose, Function.comp_def]
      using hS.1.spectral_theorem

theorem sylvesterLinear_bijective {S : Mat I} (hS : S.PosDef) :
    Function.Bijective (sylvesterLinear S) := by
  have hInjective : Function.Injective (sylvesterLinear S) := sylvester_injective hS
  exact ⟨hInjective, LinearMap.injective_iff_surjective.mp hInjective⟩

def sylvesterEquiv (S : Mat I) (hS : S.PosDef) : Mat I ≃L[ℂ] Mat I :=
  (LinearEquiv.ofBijective (sylvesterLinear S) (sylvesterLinear_bijective hS)).toContinuousLinearEquiv

theorem sylvesterEquiv_apply (S : Mat I) (hS : S.PosDef) (X : Mat I) :
    sylvesterEquiv S hS X = sylvester S X := rfl

theorem sylvester_inverse_equation (S : Mat I) (hS : S.PosDef) (H : Mat I) :
    sylvester S ((sylvesterEquiv S hS).symm H) = H :=
  (sylvesterEquiv S hS).apply_symm_apply H

theorem sylvester_solution_unique (S : Mat I) (hS : S.PosDef) (H X : Mat I)
    (hX : sylvester S X = H) : X = (sylvesterEquiv S hS).symm H :=
  (sylvester_injective hS) (hX.trans (sylvester_inverse_equation S hS H).symm)

theorem sqrt_posDef {A : Mat I} (hA : A.PosDef) : (CFC.sqrt A).PosDef := by
  apply Matrix.isStrictlyPositive_iff_posDef.mp
  have hUnit : IsUnit (CFC.sqrt A) :=
    (CFC.isUnit_sqrt_iff A hA.posSemidef.nonneg).mpr hA.isUnit
  exact hUnit.isStrictlyPositive (CFC.sqrt_nonneg A)

end QuantumProver.MatrixAnalysis.MatrixSqrt

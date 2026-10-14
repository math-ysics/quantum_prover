import Mathlib
import QuantumProver.InformationTheory.SuperchannelDiscrimination.TensorPinching

set_option autoImplicit false

noncomputable section
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker Matrix

namespace QuantumProver.SuperchannelDiscrimination.SpectralPinching

variable {I : Type*} [Fintype I] [DecidableEq I]

def coordinateProjection (i : I) : Matrix I I ℂ := Matrix.diagonal (Pi.single i 1)

theorem coordinateProjection_family :
    Pinching.IsProjectionFamily (coordinateProjection (I := I)) := by
  constructor
  · intro i
    apply Matrix.isHermitian_diagonal_iff.mpr
    intro j
    simp [Pi.single_apply, isSelfAdjoint_iff]
  · intro i
    simp only [coordinateProjection, Matrix.diagonal_mul_diagonal]
    congr 1
    funext j
    by_cases h : j = i <;> simp [h]
  · intro i j hij
    simp only [coordinateProjection, Matrix.diagonal_mul_diagonal]
    ext x y
    by_cases hxi : x = i
    · subst x
      simp [Matrix.diagonal_apply, Pi.single_apply, hij]
    · simp [Matrix.diagonal_apply, Pi.single_apply, hxi]
  · ext x y
    by_cases hxy : x = y
    · subst y
      simp [coordinateProjection, Matrix.sum_apply, Pi.single_apply]
    · simp [coordinateProjection, Matrix.sum_apply, hxy]

theorem coordinateProjection_combination (a : I → ℂ) :
    Pinching.spectralCombination coordinateProjection a = Matrix.diagonal a := by
  ext x y
  by_cases hxy : x = y
  · subst y
    simp [Pinching.spectralCombination, coordinateProjection, Matrix.sum_apply,
      Matrix.smul_apply, Pi.single_apply]
  · simp [Pinching.spectralCombination, coordinateProjection, Matrix.sum_apply,
      Matrix.smul_apply, hxy]

def unitaryProjection (U : Matrix.unitaryGroup I ℂ) (i : I) : Matrix I I ℂ :=
  Unitary.conjStarAlgAut ℂ (Matrix I I ℂ) U (coordinateProjection i)

theorem unitaryProjection_family (U : Matrix.unitaryGroup I ℂ) :
    Pinching.IsProjectionFamily (unitaryProjection U) := by
  let F := Unitary.conjStarAlgAut ℂ (Matrix I I ℂ) U
  have hP := coordinateProjection_family (I := I)
  constructor
  · intro i
    change star (F (coordinateProjection i)) = F (coordinateProjection i)
    rw [← map_star]
    change F ((coordinateProjection i)ᴴ) = F (coordinateProjection i)
    rw [(hP.selfAdjoint i).eq]
  · intro i
    change F (coordinateProjection i) * F (coordinateProjection i) = F (coordinateProjection i)
    rw [← map_mul, hP.idempotent]
  · intro i j hij
    change F (coordinateProjection i) * F (coordinateProjection j) = 0
    rw [← map_mul, hP.orthogonal i j hij, map_zero]
  · change (∑ i, F (coordinateProjection i)) = 1
    rw [← map_sum, hP.complete, map_one]

theorem unitaryProjection_combination (U : Matrix.unitaryGroup I ℂ) (a : I → ℂ) :
    Pinching.spectralCombination (unitaryProjection U) a =
      Unitary.conjStarAlgAut ℂ (Matrix I I ℂ) U (Matrix.diagonal a) := by
  rw [← coordinateProjection_combination a]
  simp [Pinching.spectralCombination, unitaryProjection, map_sum, map_smul]

def spectralProjections {σ : Matrix I I ℂ} (hσ : σ.IsHermitian) : I → Matrix I I ℂ :=
  unitaryProjection hσ.eigenvectorUnitary

theorem spectralProjections_family {σ : Matrix I I ℂ} (hσ : σ.IsHermitian) :
    Pinching.IsProjectionFamily (spectralProjections hσ) :=
  unitaryProjection_family hσ.eigenvectorUnitary

theorem spectralProjections_reconstruction {σ : Matrix I I ℂ} (hσ : σ.IsHermitian) :
    Pinching.spectralCombination (spectralProjections hσ)
      (fun i => (hσ.eigenvalues i : ℂ)) = σ := by
  rw [spectralProjections, unitaryProjection_combination]
  exact hσ.spectral_theorem.symm

theorem spectralProjections_weights_nonneg {σ : Matrix I I ℂ}
    (hσ : σ.PosSemidef) (i : I) : 0 ≤ hσ.1.eigenvalues i :=
  hσ.eigenvalues_nonneg i

def comparatorPinching {σ : Matrix I I ℂ} (hσ : σ.PosSemidef) (r : ℕ) :
    Matrix (TensorPinching.TensorRows I r) (TensorPinching.TensorRows I r) ℂ →ₗ[ℂ]
      Matrix (TensorPinching.TensorRows I r) (TensorPinching.TensorRows I r) ℂ :=
  TensorPinching.occupancyPinching (spectralProjections hσ.1) r

def recursiveComparatorPinching {σ : Matrix I I ℂ} (hσ : σ.PosSemidef) (r : ℕ) :
    Matrix (TensorPinching.RecursiveRows I r) (TensorPinching.RecursiveRows I r) ℂ →ₗ[ℂ]
      Matrix (TensorPinching.RecursiveRows I r) (TensorPinching.RecursiveRows I r) ℂ :=
  TensorPinching.recursiveOccupancyPinching (spectralProjections hσ.1) r

theorem comparatorPower_occupancy_decomposition {σ : Matrix I I ℂ}
    (hσ : σ.PosSemidef) (r : ℕ) :
    TensorPinching.tensorPower σ r =
      Pinching.spectralCombination
        (TensorPinching.occupancyProjections (spectralProjections hσ.1) r)
        (TensorPinching.typeWeight (fun i => (hσ.1.eigenvalues i : ℂ))) := by
  calc
    TensorPinching.tensorPower σ r = TensorPinching.tensorPower
        (Pinching.spectralCombination (spectralProjections hσ.1)
          (fun i => (hσ.1.eigenvalues i : ℂ))) r :=
      congrArg (fun A => TensorPinching.tensorPower A r)
        (spectralProjections_reconstruction hσ.1).symm
    _ = _ := TensorPinching.tensorPower_occupancy_decomposition _ _ r

theorem recursiveComparatorPower_occupancy_decomposition {σ : Matrix I I ℂ}
    (hσ : σ.PosSemidef) (r : ℕ) :
    TensorPinching.recursiveTensorPower σ r =
      Pinching.spectralCombination
        (TensorPinching.recursiveOccupancyProjections (spectralProjections hσ.1) r)
        (TensorPinching.typeWeight (fun i => (hσ.1.eigenvalues i : ℂ))) := by
  calc
    TensorPinching.recursiveTensorPower σ r = TensorPinching.recursiveTensorPower
        (Pinching.spectralCombination (spectralProjections hσ.1)
          (fun i => (hσ.1.eigenvalues i : ℂ))) r :=
      congrArg (fun A => TensorPinching.recursiveTensorPower A r)
        (spectralProjections_reconstruction hσ.1).symm
    _ = _ := TensorPinching.recursiveTensorPower_occupancy_decomposition _ _ r

theorem comparatorPinching_domination {σ : Matrix I I ℂ}
    (hσ : σ.PosSemidef) (r : ℕ)
    {X : Matrix (TensorPinching.TensorRows I r) (TensorPinching.TensorRows I r) ℂ}
    (hX : X.PosSemidef) :
    (((((r + 1) ^ Fintype.card I : ℕ) : ℝ) • comparatorPinching hσ r X) - X).PosSemidef :=
  TensorPinching.occupancyPinching_domination (spectralProjections_family hσ.1) r hX

theorem comparatorPinching_domination_allReferences {σ : Matrix I I ℂ}
    (hσ : σ.PosSemidef) (r : ℕ) (R : Type*) [Fintype R] [DecidableEq R]
    {X : Matrix (TensorPinching.TensorRows I r × R) (TensorPinching.TensorRows I r × R) ℂ}
    (hX : X.PosSemidef) :
    (((((r + 1) ^ Fintype.card I : ℕ) : ℝ) •
      DiamondControl.amplifyMap (comparatorPinching hσ r) R X) - X).PosSemidef :=
  TensorPinching.occupancyPinching_domination_allReferences (spectralProjections_family hσ.1) r R hX

theorem comparatorPinching_fixes_comparator {σ : Matrix I I ℂ}
    (hσ : σ.PosSemidef) (r : ℕ) :
    comparatorPinching hσ r (TensorPinching.tensorPower σ r) = TensorPinching.tensorPower σ r := by
  have h := TensorPinching.occupancyPinching_fixes_comparator (spectralProjections_family hσ.1)
    (fun i => (hσ.1.eigenvalues i : ℂ)) r
  simpa only [spectralProjections_reconstruction, comparatorPinching] using h

theorem comparatorPinching_commutes_comparator {σ : Matrix I I ℂ}
    (hσ : σ.PosSemidef) (r : ℕ)
    (X : Matrix (TensorPinching.TensorRows I r) (TensorPinching.TensorRows I r) ℂ) :
    Commute (comparatorPinching hσ r X) (TensorPinching.tensorPower σ r) := by
  have h := TensorPinching.occupancyPinching_commutes_comparator (spectralProjections_family hσ.1)
    (fun i => (hσ.1.eigenvalues i : ℂ)) r X
  simpa only [spectralProjections_reconstruction, comparatorPinching] using h

theorem comparatorPinching_CPTP {σ : Matrix I I ℂ} (hσ : σ.PosSemidef) (r : ℕ) :
    DiamondControl.CompletelyPositive (comparatorPinching hσ r) ∧
      ∀ X, (comparatorPinching hσ r X).trace = X.trace :=
  ⟨TensorPinching.occupancyPinching_completelyPositive _ r,
    TensorPinching.occupancyPinching_tracePreserving (spectralProjections_family hσ.1) r⟩

theorem recursiveComparatorPinching_domination {σ : Matrix I I ℂ}
    (hσ : σ.PosSemidef) (r : ℕ)
    {X : Matrix (TensorPinching.RecursiveRows I r) (TensorPinching.RecursiveRows I r) ℂ}
    (hX : X.PosSemidef) :
    (((((r + 1) ^ Fintype.card I : ℕ) : ℝ) • recursiveComparatorPinching hσ r X) - X).PosSemidef :=
  TensorPinching.recursiveOccupancyPinching_domination (spectralProjections_family hσ.1) r hX

theorem recursiveComparatorPinching_domination_allReferences {σ : Matrix I I ℂ}
    (hσ : σ.PosSemidef) (r : ℕ) (R : Type*) [Fintype R] [DecidableEq R]
    {X : Matrix (TensorPinching.RecursiveRows I r × R) (TensorPinching.RecursiveRows I r × R) ℂ}
    (hX : X.PosSemidef) :
    (((((r + 1) ^ Fintype.card I : ℕ) : ℝ) •
      DiamondControl.amplifyMap (recursiveComparatorPinching hσ r) R X) - X).PosSemidef :=
  TensorPinching.recursiveOccupancyPinching_domination_allReferences
    (spectralProjections_family hσ.1) r R hX

theorem recursiveComparatorPinching_fixes_comparator {σ : Matrix I I ℂ}
    (hσ : σ.PosSemidef) (r : ℕ) :
    recursiveComparatorPinching hσ r (TensorPinching.recursiveTensorPower σ r) =
      TensorPinching.recursiveTensorPower σ r := by
  have h := TensorPinching.recursiveOccupancyPinching_fixes_comparator
    (spectralProjections_family hσ.1) (fun i => (hσ.1.eigenvalues i : ℂ)) r
  simpa only [spectralProjections_reconstruction, recursiveComparatorPinching] using h

theorem recursiveComparatorPinching_commutes_comparator {σ : Matrix I I ℂ}
    (hσ : σ.PosSemidef) (r : ℕ)
    (X : Matrix (TensorPinching.RecursiveRows I r) (TensorPinching.RecursiveRows I r) ℂ) :
    Commute (recursiveComparatorPinching hσ r X) (TensorPinching.recursiveTensorPower σ r) := by
  have h := TensorPinching.recursiveOccupancyPinching_commutes_comparator
    (spectralProjections_family hσ.1) (fun i => (hσ.1.eigenvalues i : ℂ)) r X
  simpa only [spectralProjections_reconstruction, recursiveComparatorPinching] using h

theorem recursiveComparatorPinching_CPTP {σ : Matrix I I ℂ} (hσ : σ.PosSemidef) (r : ℕ) :
    DiamondControl.CompletelyPositive (recursiveComparatorPinching hσ r) ∧
      ∀ X, (recursiveComparatorPinching hσ r X).trace = X.trace :=
  TensorPinching.recursiveOccupancyPinching_CPTP (spectralProjections_family hσ.1) r

end QuantumProver.SuperchannelDiscrimination.SpectralPinching

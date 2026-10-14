import QuantumProver.InformationTheory.SuperchannelDiscrimination.FlaggedStates

set_option autoImplicit false

noncomputable section

open Matrix
open QuantumProver.SuperchannelDiscrimination.FlaggedStates
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker Matrix

namespace QuantumProver.QuantumEntropy

variable {I J A B C : Type*} [Fintype I] [Fintype J]
  [Fintype A] [Fintype B] [Fintype C]
  [DecidableEq I] [DecidableEq J] [DecidableEq A] [DecidableEq B] [DecidableEq C]

def reassoc (R : Matrix ((A × B) × C) ((A × B) × C) ℂ) :
    Matrix (A × (B × C)) (A × (B × C)) ℂ :=
  Matrix.reindex (Equiv.prodAssoc A B C) (Equiv.prodAssoc A B C) R

def unreassoc (R : Matrix (A × (B × C)) (A × (B × C)) ℂ) :
    Matrix ((A × B) × C) ((A × B) × C) ℂ :=
  Matrix.reindex (Equiv.prodAssoc A B C).symm (Equiv.prodAssoc A B C).symm R

@[simp] theorem reassoc_apply (R : Matrix ((A × B) × C) ((A × B) × C) ℂ)
    (a a' : A) (b b' : B) (c c' : C) :
    reassoc R (a, (b, c)) (a', (b', c')) = R ((a, b), c) ((a', b'), c') := rfl

@[simp] theorem unreassoc_apply (R : Matrix (A × (B × C)) (A × (B × C)) ℂ)
    (a a' : A) (b b' : B) (c c' : C) :
    unreassoc R ((a, b), c) ((a', b'), c') = R (a, (b, c)) (a', (b', c')) := rfl

@[simp] theorem reassoc_unreassoc (R : Matrix (A × (B × C)) (A × (B × C)) ℂ) :
    reassoc (unreassoc R) = R := by ext i j; rfl

@[simp] theorem unreassoc_reassoc (R : Matrix ((A × B) × C) ((A × B) × C) ℂ) :
    unreassoc (reassoc R) = R := by ext i j; rfl

theorem trace_reindex (e : I ≃ J) (R : Matrix I I ℂ) :
    (Matrix.reindex e e R).trace = R.trace := by
  change (∑ j : J, R (e.symm j) (e.symm j)) = ∑ i : I, R i i
  exact Equiv.sum_comp e.symm (fun i => R i i)

theorem reindex_posSemidef (e : I ≃ J) {R : Matrix I I ℂ} (hR : R.PosSemidef) :
    (Matrix.reindex e e R).PosSemidef := hR.submatrix e.symm

theorem hasSupportIn_reindex (e : I ≃ J) {R S : Matrix I I ℂ}
    (hs : HasSupportIn R S) :
    HasSupportIn (Matrix.reindex e e R) (Matrix.reindex e e S) := by
  intro v hv
  have hSv : S *ᵥ (v ∘ e) = 0 := by
    have h := hv
    change S.submatrix e.symm e.symm *ᵥ v = 0 at h
    rw [Matrix.submatrix_mulVec_equiv, Equiv.symm_symm] at h
    funext i
    have hi := congrFun h (e i)
    simpa only [Function.comp_apply, Equiv.symm_apply_apply, Pi.zero_apply] using hi
  change R.submatrix e.symm e.symm *ᵥ v = 0
  rw [Matrix.submatrix_mulVec_equiv, Equiv.symm_symm, hs (v ∘ e) hSv]
  rfl

@[simp] theorem trace_reassoc (R : Matrix ((A × B) × C) ((A × B) × C) ℂ) :
    (reassoc R).trace = R.trace := trace_reindex (Equiv.prodAssoc A B C) R

@[simp] theorem trace_unreassoc (R : Matrix (A × (B × C)) (A × (B × C)) ℂ) :
    (unreassoc R).trace = R.trace := trace_reindex (Equiv.prodAssoc A B C).symm R

theorem reassoc_posSemidef {R : Matrix ((A × B) × C) ((A × B) × C) ℂ}
    (hR : R.PosSemidef) : (reassoc R).PosSemidef :=
  reindex_posSemidef (Equiv.prodAssoc A B C) hR

theorem unreassoc_posSemidef {R : Matrix (A × (B × C)) (A × (B × C)) ℂ}
    (hR : R.PosSemidef) : (unreassoc R).PosSemidef :=
  reindex_posSemidef (Equiv.prodAssoc A B C).symm hR

theorem reassoc_kronecker (X : Matrix A A ℂ) (Y : Matrix B B ℂ) (Z : Matrix C C ℂ) :
    reassoc ((X ⊗ₖ Y) ⊗ₖ Z) = X ⊗ₖ (Y ⊗ₖ Z) :=
  Matrix.kronecker_assoc X Y Z

theorem unreassoc_kronecker (X : Matrix A A ℂ) (Y : Matrix B B ℂ) (Z : Matrix C C ℂ) :
    unreassoc (X ⊗ₖ (Y ⊗ₖ Z)) = (X ⊗ₖ Y) ⊗ₖ Z := by
  rw [← reassoc_kronecker, unreassoc_reassoc]

end QuantumProver.QuantumEntropy

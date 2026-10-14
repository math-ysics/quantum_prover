import QuantumProver.InformationTheory.DepolarizingSquashedEntanglement.BCYRelativeEntropy

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

noncomputable section

open Matrix Set Filter
open scoped Topology BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker

namespace QuantumProver.DepolarizingSquashedEntanglement.BCYRelativeEntropy

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

theorem tensorCopies_succ_apply (ρ : Density (A × B)) (n : ℕ)
    (a a' : CopyIndex A n) (b b' : CopyIndex B n) (i i' : A) (j j' : B) :
    (tensorCopies ρ (n + 1)).matrix ((a,i),(b,j)) ((a',i'),(b',j')) =
      (tensorCopies ρ n).matrix (a,b) (a',b') * ρ.matrix (i,j) (i',j') := rfl

theorem tensorCopies_zero_apply (ρ : Density (A × B))
    (a a' : CopyIndex A 0) (b b' : CopyIndex B 0) :
    (tensorCopies ρ 0).matrix (a,b) (a',b') = 1 := by
  cases a
  cases a'
  cases b
  cases b'
  rfl

theorem tensorCopies_succ (ρ : Density (A × B)) (n : ℕ) :
    tensorCopies ρ (n + 1) = bipartiteTensorDensity (tensorCopies ρ n) ρ := by
  apply density_ext
  ext i j
  rfl

theorem tensorCopies_zero (ρ : Density (A × B)) :
    tensorCopies ρ 0 = productDensity
      (matrixTensorPowerDensity (leftMarginal ρ) 0)
      (matrixTensorPowerDensity (rightMarginal ρ) 0) := by
  apply density_ext
  ext i j
  rcases i with ⟨a,b⟩
  rcases j with ⟨a',b'⟩
  cases a
  cases a'
  cases b
  cases b'
  change (1 : ℂ) = 1 * 1
  exact (one_mul _).symm

def copyConcat (A : Type*) (m : ℕ) : (n : ℕ) →
    CopyIndex A (m + n) ≃ CopyIndex A m × CopyIndex A n
  | 0 => {
      toFun := fun x => (x, PUnit.unit)
      invFun := Prod.fst
      left_inv := by intro x; rfl
      right_inv := by rintro ⟨x,y⟩; cases y; rfl }
  | n + 1 => (Equiv.prodCongr (copyConcat A m n) (Equiv.refl A)).trans
      (Equiv.prodAssoc (CopyIndex A m) (CopyIndex A n) A)

theorem tensorCopies_add_apply (ρ : Density (A × B)) (m n : ℕ) :
    ∀ (x x' : CopyIndex A m) (u u' : CopyIndex A n)
      (y y' : CopyIndex B m) (v v' : CopyIndex B n),
    (tensorCopies ρ (m + n)).matrix
        ((copyConcat A m n).symm (x,u), (copyConcat B m n).symm (y,v))
        ((copyConcat A m n).symm (x',u'), (copyConcat B m n).symm (y',v')) =
      (tensorCopies ρ m).matrix (x,y) (x',y') *
        (tensorCopies ρ n).matrix (u,v) (u',v') := by
  induction n with
  | zero =>
      intro x x' u u' y y' v v'
      cases u
      cases u'
      cases v
      cases v'
      change (tensorCopies ρ m).matrix (x,y) (x',y') =
        (tensorCopies ρ m).matrix (x,y) (x',y') *
          (tensorCopies ρ 0).matrix (PUnit.unit,PUnit.unit) (PUnit.unit,PUnit.unit)
      rw [tensorCopies_zero_apply, mul_one]
  | succ n ih =>
      intro x x' u u' y y' v v'
      rcases u with ⟨u,i⟩
      rcases u' with ⟨u',i'⟩
      rcases v with ⟨v,j⟩
      rcases v' with ⟨v',j'⟩
      change (tensorCopies ρ (m + n)).matrix
          ((copyConcat A m n).symm (x,u), (copyConcat B m n).symm (y,v))
          ((copyConcat A m n).symm (x',u'), (copyConcat B m n).symm (y',v')) *
            ρ.matrix (i,j) (i',j') =
        (tensorCopies ρ m).matrix (x,y) (x',y') *
          ((tensorCopies ρ n).matrix (u,v) (u',v') * ρ.matrix (i,j) (i',j'))
      rw [ih]
      exact mul_assoc _ _ _

theorem tensorCopies_add (ρ : Density (A × B)) (m n : ℕ) :
    tensorCopies ρ (m + n) =
      densityReindex (Equiv.prodCongr (copyConcat A m n).symm (copyConcat B m n).symm)
        (bipartiteTensorDensity (tensorCopies ρ m) (tensorCopies ρ n)) := by
  apply density_ext
  ext i j
  change (tensorCopies ρ (m + n)).matrix i j =
    (tensorCopies ρ m).matrix
      (((copyConcat A m n) i.1).1, ((copyConcat B m n) i.2).1)
      (((copyConcat A m n) j.1).1, ((copyConcat B m n) j.2).1) *
    (tensorCopies ρ n).matrix
      (((copyConcat A m n) i.1).2, ((copyConcat B m n) i.2).2)
      (((copyConcat A m n) j.1).2, ((copyConcat B m n) j.2).2)
  have h := tensorCopies_add_apply ρ m n
    ((copyConcat A m n i.1).1) ((copyConcat A m n j.1).1)
    ((copyConcat A m n i.1).2) ((copyConcat A m n j.1).2)
    ((copyConcat B m n i.2).1) ((copyConcat B m n j.2).1)
    ((copyConcat B m n i.2).2) ((copyConcat B m n j.2).2)
  simpa using h

theorem tensorCopies_separable (ρ : Density (A × B)) (hρ : IsSeparable ρ.matrix)
    (n : ℕ) : IsSeparable (tensorCopies ρ n).matrix := by
  induction n with
  | zero =>
      rw [tensorCopies_zero]
      exact productDensity_separable _ _
  | succ n ih =>
      rw [tensorCopies_succ]
      exact bipartiteTensorMatrix_separable ih hρ

def tensorEntanglementSequence (ρ : Density (A × B)) (n : ℕ) : ℝ :=
  relativeEntropyEntanglementReal (tensorCopies ρ n)

theorem tensorEntanglementSequence_nonneg (ρ : Density (A × B)) (n : ℕ) :
    0 ≤ tensorEntanglementSequence ρ n :=
  relativeEntropyEntanglementReal_nonneg _

theorem tensorEntanglementSequence_zero (ρ : Density (A × B)) :
    tensorEntanglementSequence ρ 0 = 0 := by
  unfold tensorEntanglementSequence relativeEntropyEntanglementReal
  rw [relativeEntropyEntanglementNat_eq_zero_of_separable _
    (by rw [tensorCopies_zero]; exact productDensity_separable _ _)]
  rfl

theorem tensorEntanglementSequence_one (ρ : Density (A × B)) :
    tensorEntanglementSequence ρ 1 = relativeEntropyEntanglementReal ρ := by
  have hd : densityReindex
      (Equiv.prodCongr (Equiv.punitProd A) (Equiv.punitProd B)) (tensorCopies ρ 1) = ρ := by
    apply density_ext
    ext i j
    change (1 : ℂ) * ρ.matrix i j = ρ.matrix i j
    exact one_mul _
  have h := relativeEntropyEntanglementReal_reindex
    (Equiv.punitProd A) (Equiv.punitProd B) (tensorCopies ρ 1)
  exact h.symm.trans (congrArg (fun σ : Density (A × B) =>
    relativeEntropyEntanglementReal σ) hd)

theorem tensorEntanglementSequence_subadditive (ρ : Density (A × B)) :
    Subadditive (tensorEntanglementSequence ρ) := by
  intro m n
  unfold tensorEntanglementSequence
  rw [tensorCopies_add, relativeEntropyEntanglementReal_reindex]
  exact relativeEntropyEntanglementReal_tensor_subadditive _ _

theorem tensorEntanglementSequence_rates_bddBelow (ρ : Density (A × B)) :
    BddBelow (range (fun n : ℕ => tensorEntanglementSequence ρ n / (n : ℝ))) := by
  refine ⟨0, ?_⟩
  rintro x ⟨n,rfl⟩
  exact div_nonneg (tensorEntanglementSequence_nonneg ρ n) (Nat.cast_nonneg n)

def regularizedRelativeEntropyEntanglementNat (ρ : Density (A × B)) : ℝ :=
  sInf ((fun n : ℕ => tensorEntanglementSequence ρ n / (n : ℝ)) '' Ici 1)

theorem tendsto_relativeEntropyEntanglement_rate (ρ : Density (A × B)) :
    Tendsto (fun n : ℕ => relativeEntropyEntanglementReal (tensorCopies ρ n) / (n : ℝ))
      atTop (𝓝 (regularizedRelativeEntropyEntanglementNat ρ)) := by
  have h := (tensorEntanglementSequence_subadditive ρ).tendsto_lim
    (tensorEntanglementSequence_rates_bddBelow ρ)
  simpa only [Subadditive.lim, regularizedRelativeEntropyEntanglementNat,
    tensorEntanglementSequence] using h

theorem regularizedRelativeEntropyEntanglementNat_nonneg (ρ : Density (A × B)) :
    0 ≤ regularizedRelativeEntropyEntanglementNat ρ := by
  apply le_csInf
  · exact ⟨_, ⟨1, by simp, rfl⟩⟩
  · rintro x ⟨n,hn,rfl⟩
    exact div_nonneg (tensorEntanglementSequence_nonneg ρ n) (Nat.cast_nonneg n)

theorem regularizedRelativeEntropyEntanglementNat_le_rate (ρ : Density (A × B))
    (n : ℕ) (hn : 0 < n) :
    regularizedRelativeEntropyEntanglementNat ρ ≤
      relativeEntropyEntanglementReal (tensorCopies ρ n) / (n : ℝ) := by
  exact csInf_le ((tensorEntanglementSequence_rates_bddBelow ρ).mono
    (image_subset_range _ _)) ⟨n, hn, rfl⟩

theorem regularizedRelativeEntropyEntanglementNat_le (ρ : Density (A × B)) :
    regularizedRelativeEntropyEntanglementNat ρ ≤ relativeEntropyEntanglementReal ρ := by
  simpa only [← tensorEntanglementSequence_one ρ, tensorEntanglementSequence,
    Nat.cast_one, div_one] using regularizedRelativeEntropyEntanglementNat_le_rate ρ 1 (by omega)

theorem regularizedRelativeEntropyEntanglementNat_eq_zero_of_separable
    (ρ : Density (A × B)) (hρ : IsSeparable ρ.matrix) :
    regularizedRelativeEntropyEntanglementNat ρ = 0 := by
  apply le_antisymm
  · have h := regularizedRelativeEntropyEntanglementNat_le ρ
    unfold relativeEntropyEntanglementReal at h
    rw [relativeEntropyEntanglementNat_eq_zero_of_separable ρ hρ] at h
    exact h
  · exact regularizedRelativeEntropyEntanglementNat_nonneg ρ

end QuantumProver.DepolarizingSquashedEntanglement.BCYRelativeEntropy

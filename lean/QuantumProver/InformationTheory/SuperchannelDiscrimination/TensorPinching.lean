import Mathlib
import QuantumProver.InformationTheory.SuperchannelDiscrimination.Pinching

set_option autoImplicit false

noncomputable section
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker

namespace QuantumProver.SuperchannelDiscrimination.TensorPinching

variable {I κ γ : Type*} [Fintype I] [Fintype κ] [Fintype γ]
  [DecidableEq I] [DecidableEq κ] [DecidableEq γ]

abbrev TensorRows (I : Type*) (r : ℕ) := Fin r → I

def tensorMatrix {r : ℕ} (M : Fin r → Matrix I I ℂ) :
    Matrix (TensorRows I r) (TensorRows I r) ℂ :=
  fun x y => ∏ j, M j (x j) (y j)

def tensorPower (A : Matrix I I ℂ) (r : ℕ) :
    Matrix (TensorRows I r) (TensorRows I r) ℂ := tensorMatrix (fun _ => A)

def tensorProjection (P : κ → Matrix I I ℂ) (r : ℕ) (w : Fin r → κ) :
    Matrix (TensorRows I r) (TensorRows I r) ℂ := tensorMatrix (fun j => P (w j))

omit [DecidableEq I] in
theorem tensorMatrix_mul {r : ℕ} (M N : Fin r → Matrix I I ℂ) :
    tensorMatrix M * tensorMatrix N = tensorMatrix (fun j => M j * N j) := by
  ext x y
  simp only [tensorMatrix, Matrix.mul_apply, ← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun j z => M j (x j) z * N j z (y j))).symm

omit [Fintype I] [DecidableEq I] in
theorem tensorMatrix_conjTranspose {r : ℕ} (M : Fin r → Matrix I I ℂ) :
    (tensorMatrix M)ᴴ = tensorMatrix (fun j => (M j)ᴴ) := by
  ext x y
  simp [tensorMatrix, Matrix.conjTranspose_apply]

omit [Fintype I] in
theorem tensorMatrix_one (r : ℕ) :
    tensorMatrix (fun _ : Fin r => (1 : Matrix I I ℂ)) =
      (1 : Matrix (TensorRows I r) (TensorRows I r) ℂ) := by
  classical
  ext x y
  by_cases hxy : x = y
  · subst y
    simp [tensorMatrix]
  · have hsome : ∃ j, x j ≠ y j := by
      by_contra hn
      apply hxy
      funext j
      by_contra hj
      exact hn ⟨j, hj⟩
    obtain ⟨j, hj⟩ := hsome
    have hz : (∏ a : Fin r, (1 : Matrix I I ℂ) (x a) (y a)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ j) (by simp [hj])
    simpa [tensorMatrix, Matrix.one_apply, hxy] using hz

theorem tensorProjection_family {P : κ → Matrix I I ℂ}
    (hP : Pinching.IsProjectionFamily P) (r : ℕ) :
    Pinching.IsProjectionFamily (tensorProjection P r) := by
  constructor
  · intro w
    show (tensorMatrix (fun j => P (w j)))ᴴ = tensorMatrix (fun j => P (w j))
    rw [tensorMatrix_conjTranspose]
    congr 1
    funext j
    exact (hP.selfAdjoint (w j)).eq
  · intro w
    change tensorMatrix (fun j => P (w j)) * tensorMatrix (fun j => P (w j)) = _
    rw [tensorMatrix_mul]
    congr 1
    funext j
    exact hP.idempotent (w j)
  · intro w v hwv
    have hsome : ∃ j, w j ≠ v j := by
      by_contra hn
      apply hwv
      funext j
      by_contra hj
      exact hn ⟨j, hj⟩
    obtain ⟨j, hj⟩ := hsome
    change tensorMatrix (fun a => P (w a)) * tensorMatrix (fun a => P (v a)) = 0
    rw [tensorMatrix_mul]
    ext x y
    change (∏ a, (P (w a) * P (v a)) (x a) (y a)) = 0
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    rw [hP.orthogonal (w j) (v j) hj]
    rfl
  · ext x y
    simp only [Matrix.sum_apply, tensorProjection, tensorMatrix]
    calc
      (∑ w : Fin r → κ, ∏ j, P (w j) (x j) (y j)) =
          ∏ j : Fin r, ∑ i : κ, P i (x j) (y j) :=
        (Fintype.prod_sum (fun j i => P i (x j) (y j))).symm
      _ = ∏ j : Fin r, (1 : Matrix I I ℂ) (x j) (y j) := by
        apply Finset.prod_congr rfl
        intro j hj
        simpa only [Matrix.sum_apply] using
          congrArg (fun A : Matrix I I ℂ => A (x j) (y j)) hP.complete
      _ = (1 : Matrix (TensorRows I r) (TensorRows I r) ℂ) x y :=
        congrArg (fun A : Matrix (TensorRows I r) (TensorRows I r) ℂ => A x y)
          (tensorMatrix_one r)

def groupedProjections (P : κ → Matrix I I ℂ) (f : κ → γ) (a : γ) : Matrix I I ℂ :=
  ∑ i, if f i = a then P i else 0

omit [Fintype γ] [DecidableEq κ] in
theorem projection_mul_group {P : κ → Matrix I I ℂ}
    (hP : Pinching.IsProjectionFamily P) (f : κ → γ) (a : γ) (i : κ) :
    P i * groupedProjections P f a = if f i = a then P i else 0 := by
  classical
  simp only [groupedProjections, Matrix.mul_sum, mul_ite, Matrix.mul_zero]
  calc
    (∑ j, if f j = a then P i * P j else 0) =
        (if f i = a then P i * P i else 0) := by
      apply Finset.sum_eq_single i
      · intro j hj hji
        rw [hP.orthogonal i j (Ne.symm hji)]
        simp
      · intro hi
        exact False.elim (hi (Finset.mem_univ i))
    _ = _ := by rw [hP.idempotent]

omit [DecidableEq κ] in
theorem groupedProjections_family {P : κ → Matrix I I ℂ}
    (hP : Pinching.IsProjectionFamily P) (f : κ → γ) :
    Pinching.IsProjectionFamily (groupedProjections P f) := by
  constructor
  · intro a
    change IsSelfAdjoint (∑ i, if f i = a then P i else 0)
    apply isSelfAdjoint_sum Finset.univ
    intro i hi
    split_ifs
    · exact hP.selfAdjoint i
    · exact (Matrix.PosSemidef.zero (n := I) (R := ℂ)).isHermitian
  · intro a
    change (∑ i, if f i = a then P i else 0) * groupedProjections P f a = _
    rw [Matrix.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    split_ifs with h
    · rw [projection_mul_group hP f a i]
      simp [h]
    · simp
  · intro a b hab
    change (∑ i, if f i = a then P i else 0) * groupedProjections P f b = 0
    rw [Matrix.sum_mul]
    apply Finset.sum_eq_zero
    intro i hi
    split_ifs with h
    · rw [projection_mul_group hP f b i]
      have hf : f i ≠ b := fun he => hab (h.symm.trans he)
      simp [hf]
    · simp
  · change (∑ a, ∑ i, if f i = a then P i else 0) = 1
    rw [Finset.sum_comm]
    simpa using hP.complete

omit [Fintype I] [DecidableEq I] [DecidableEq κ] in
theorem groupedProjections_weighted_sum (P : κ → Matrix I I ℂ)
    (f : κ → γ) (c : γ → ℂ) :
    (∑ a, c a • groupedProjections P f a) = ∑ i, c (f i) • P i := by
  simp only [groupedProjections, Finset.smul_sum, smul_ite, smul_zero]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  simp

abbrev Occupancy (κ : Type*) (r : ℕ) := κ → Fin (r + 1)

def wordOccupancy (r : ℕ) (w : Fin r → κ) : Occupancy κ r := fun i =>
  ⟨(Finset.univ.filter (fun j => w j = i)).card,
    Nat.lt_succ_of_le (by simpa using Finset.card_filter_le Finset.univ (fun j => w j = i))⟩

def typeWeight (eig : κ → ℂ) {r : ℕ} (τ : Occupancy κ r) : ℂ := ∏ i, eig i ^ (τ i).val

def occupancyProjections (P : κ → Matrix I I ℂ) (r : ℕ) :
    Occupancy κ r → Matrix (TensorRows I r) (TensorRows I r) ℂ :=
  groupedProjections (tensorProjection P r) (wordOccupancy r)

def occupancyPinching (P : κ → Matrix I I ℂ) (r : ℕ) :
    Matrix (TensorRows I r) (TensorRows I r) ℂ →ₗ[ℂ]
      Matrix (TensorRows I r) (TensorRows I r) ℂ :=
  Pinching.pinchingMap (occupancyProjections P r)

theorem wordOccupancy_sum (r : ℕ) (w : Fin r → κ) :
    (∑ i, (wordOccupancy r w i).val) = r := by
  simpa [wordOccupancy] using
    Finset.sum_card_fiberwise_eq_card_filter Finset.univ Finset.univ w

theorem wordWeight_by_occupancy (eig : κ → ℂ) (r : ℕ) (w : Fin r → κ) :
    (∏ j, eig (w j)) = typeWeight eig (wordOccupancy r w) := by
  symm
  simpa only [typeWeight, wordOccupancy, Finset.prod_const] using
    Finset.prod_fiberwise' Finset.univ w eig

theorem occupancyProjections_family {P : κ → Matrix I I ℂ}
    (hP : Pinching.IsProjectionFamily P) (r : ℕ) :
    Pinching.IsProjectionFamily (occupancyProjections P r) :=
  groupedProjections_family (tensorProjection_family hP r) (wordOccupancy r)

theorem occupancy_card (r : ℕ) :
    Fintype.card (Occupancy κ r) = (r + 1) ^ Fintype.card κ := by
  simp [Occupancy]

omit [Fintype I] [DecidableEq I] [DecidableEq κ] in
theorem tensorPower_spectralExpansion (P : κ → Matrix I I ℂ) (eig : κ → ℂ) (r : ℕ) :
    tensorPower (Pinching.spectralCombination P eig) r =
      ∑ w : Fin r → κ, (∏ j, eig (w j)) • tensorProjection P r w := by
  ext x y
  simp only [tensorPower, tensorMatrix, Pinching.spectralCombination, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul, tensorProjection, ← Finset.prod_mul_distrib]
  exact Fintype.prod_sum (fun j i => eig i * P i (x j) (y j))

omit [Fintype I] [DecidableEq I] in

theorem tensorPower_occupancy_decomposition (P : κ → Matrix I I ℂ) (eig : κ → ℂ) (r : ℕ) :
    tensorPower (Pinching.spectralCombination P eig) r =
      Pinching.spectralCombination (occupancyProjections P r) (typeWeight eig) := by
  calc
    tensorPower (Pinching.spectralCombination P eig) r =
        ∑ w : Fin r → κ, (∏ j, eig (w j)) • tensorProjection P r w :=
      tensorPower_spectralExpansion P eig r
    _ = ∑ w : Fin r → κ, typeWeight eig (wordOccupancy r w) • tensorProjection P r w := by
      simp only [wordWeight_by_occupancy]
    _ = Pinching.spectralCombination (occupancyProjections P r) (typeWeight eig) :=
      (groupedProjections_weighted_sum (tensorProjection P r) (wordOccupancy r) (typeWeight eig)).symm

omit [Fintype I] [DecidableEq I] in
theorem occupancyProjections_zero_of_unattained (P : κ → Matrix I I ℂ)
    (r : ℕ) (τ : Occupancy κ r) (hτ : ∀ w : Fin r → κ, wordOccupancy r w ≠ τ) :
    occupancyProjections P r τ = 0 := by
  unfold occupancyProjections groupedProjections
  apply Finset.sum_eq_zero
  intro w hw
  simp [hτ w]

omit [Fintype I] [DecidableEq I] in
theorem occupancyProjections_zero_of_wrong_total (P : κ → Matrix I I ℂ)
    (r : ℕ) (τ : Occupancy κ r) (hτ : (∑ i, (τ i).val) ≠ r) :
    occupancyProjections P r τ = 0 := by
  apply occupancyProjections_zero_of_unattained
  intro w he
  apply hτ
  rw [← he, wordOccupancy_sum]

omit [DecidableEq κ] in
theorem typeWeight_zero_of_positive_zero_eigenvalue (eig : κ → ℂ) {r : ℕ}
    (τ : Occupancy κ r) (i : κ) (heig : eig i = 0) (hτ : 0 < (τ i).val) :
    typeWeight eig τ = 0 := by
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  simp [heig, Nat.ne_of_gt hτ]

omit [Fintype I] in
theorem tensorPower_zero (A : Matrix I I ℂ) :
    tensorPower A 0 = (1 : Matrix (TensorRows I 0) (TensorRows I 0) ℂ) := by
  ext x y
  have he : x = y := funext (fun j => Fin.elim0 j)
  simp [tensorPower, tensorMatrix, Matrix.one_apply, he]

theorem occupancyPinching_domination {P : κ → Matrix I I ℂ}
    (hP : Pinching.IsProjectionFamily P) (r : ℕ)
    {X : Matrix (TensorRows I r) (TensorRows I r) ℂ} (hX : X.PosSemidef) :
    (((((r + 1) ^ Fintype.card κ) : ℕ) : ℝ) • occupancyPinching P r X - X).PosSemidef := by
  have h := Pinching.pinching_domination (occupancyProjections_family hP r) hX
  simpa only [occupancy_card, occupancyPinching] using h

theorem le_polynomial_smul_occupancyPinching {P : κ → Matrix I I ℂ}
    (hP : Pinching.IsProjectionFamily P) (r : ℕ)
    {X : Matrix (TensorRows I r) (TensorRows I r) ℂ} (hX : X.PosSemidef) :
    X ≤ (((((r + 1) ^ Fintype.card κ) : ℕ) : ℝ) • occupancyPinching P r X) :=
  sub_nonneg.mp (occupancyPinching_domination hP r hX).nonneg

theorem occupancyPinching_domination_allReferences {P : κ → Matrix I I ℂ}
    (hP : Pinching.IsProjectionFamily P) (r : ℕ)
    (R : Type*) [Fintype R] [DecidableEq R]
    {X : Matrix (TensorRows I r × R) (TensorRows I r × R) ℂ} (hX : X.PosSemidef) :
    (((((r + 1) ^ Fintype.card κ) : ℕ) : ℝ) •
      DiamondControl.amplifyMap (occupancyPinching P r) R X - X).PosSemidef := by
  have h := Pinching.pinching_domination_allReferences (occupancyProjections_family hP r) R hX
  simpa only [occupancy_card, occupancyPinching] using h

theorem occupancyPinching_fixes_comparator {P : κ → Matrix I I ℂ}
    (hP : Pinching.IsProjectionFamily P) (eig : κ → ℂ) (r : ℕ) :
    occupancyPinching P r (tensorPower (Pinching.spectralCombination P eig) r) =
      tensorPower (Pinching.spectralCombination P eig) r := by
  rw [tensorPower_occupancy_decomposition]
  exact Pinching.pinchingMap_fixes_spectralCombination (occupancyProjections_family hP r) (typeWeight eig)

theorem occupancyPinching_commutes_comparator {P : κ → Matrix I I ℂ}
    (hP : Pinching.IsProjectionFamily P) (eig : κ → ℂ) (r : ℕ)
    (X : Matrix (TensorRows I r) (TensorRows I r) ℂ) :
    Commute (occupancyPinching P r X) (tensorPower (Pinching.spectralCombination P eig) r) := by
  rw [tensorPower_occupancy_decomposition]
  exact Pinching.pinching_commutes_spectralCombination (occupancyProjections_family hP r) (typeWeight eig) X

theorem occupancyPinching_completelyPositive (P : κ → Matrix I I ℂ) (r : ℕ) :
    DiamondControl.CompletelyPositive (occupancyPinching P r) :=
  Pinching.pinchingMap_completelyPositive (occupancyProjections P r)

theorem occupancyPinching_tracePreserving {P : κ → Matrix I I ℂ}
    (hP : Pinching.IsProjectionFamily P) (r : ℕ)
    (X : Matrix (TensorRows I r) (TensorRows I r) ℂ) :
    (occupancyPinching P r X).trace = X.trace :=
  Pinching.pinchingMap_tracePreserving (occupancyProjections_family hP r) X

omit [DecidableEq κ] in
theorem typeWeight_zero_copies (eig : κ → ℂ) (τ : Occupancy κ 0) :
    typeWeight eig τ = 1 := by
  simp [typeWeight]

def rowsSuccEquiv (I : Type*) (r : ℕ) : TensorRows I (r + 1) ≃ TensorRows I r × I where
  toFun x := (fun j => x j.castSucc, x (Fin.last r))
  invFun p := Fin.lastCases p.2 (fun j => p.1 j)
  left_inv x := by
    funext j
    refine Fin.lastCases ?_ (fun k => ?_) j <;> simp
  right_inv p := by
    apply Prod.ext
    · funext j
      simp
    · simp

omit [Fintype I] [DecidableEq I] in
theorem tensorPower_succ_submatrix (A : Matrix I I ℂ) (r : ℕ) :
    (tensorPower A (r + 1)).submatrix (rowsSuccEquiv I r).symm (rowsSuccEquiv I r).symm =
      tensorPower A r ⊗ₖ A := by
  ext x y
  simp [tensorPower, tensorMatrix, rowsSuccEquiv,
    Fin.prod_univ_castSucc]

universe u

def RecursiveRows (ι : Type u) : ℕ → Type u
  | 0 => PUnit
  | r + 1 => RecursiveRows ι r × ι

instance recursiveRowsFintype (ι : Type u) [Fintype ι] (r : ℕ) :
    Fintype (RecursiveRows ι r) := by
  induction r with
  | zero => exact inferInstanceAs (Fintype PUnit)
  | succ r ih =>
      letI : Fintype (RecursiveRows ι r) := ih
      exact inferInstanceAs (Fintype (RecursiveRows ι r × ι))

instance recursiveRowsDecidableEq (ι : Type u) [DecidableEq ι] (r : ℕ) :
    DecidableEq (RecursiveRows ι r) := by
  induction r with
  | zero => exact inferInstanceAs (DecidableEq PUnit)
  | succ r ih =>
      letI : DecidableEq (RecursiveRows ι r) := ih
      exact inferInstanceAs (DecidableEq (RecursiveRows ι r × ι))

def rowsRecursiveEquiv (ι : Type u) : (r : ℕ) → TensorRows ι r ≃ RecursiveRows ι r
  | 0 =>
      { toFun := fun _ => PUnit.unit
        invFun := fun _ j => Fin.elim0 j
        left_inv := fun x => funext (fun j => Fin.elim0 j)
        right_inv := fun x => by cases x; rfl }
  | r + 1 => (rowsSuccEquiv ι r).trans
      (Equiv.prodCongr (rowsRecursiveEquiv ι r) (Equiv.refl ι))

def recursiveTensorPower (A : Matrix I I ℂ) : (r : ℕ) →
    Matrix (RecursiveRows I r) (RecursiveRows I r) ℂ
  | 0 => 1
  | r + 1 => recursiveTensorPower A r ⊗ₖ A

omit [Fintype I] in
theorem tensorPower_recursive_submatrix (A : Matrix I I ℂ) (r : ℕ) :
    (tensorPower A r).submatrix (rowsRecursiveEquiv I r).symm (rowsRecursiveEquiv I r).symm =
      recursiveTensorPower A r := by
  induction r with
  | zero =>
      rw [tensorPower_zero]
      exact Matrix.submatrix_one_equiv (rowsRecursiveEquiv I 0).symm
  | succ r ih =>
      let e := Equiv.prodCongr (rowsRecursiveEquiv I r) (Equiv.refl I)
      change ((tensorPower A (r + 1)).submatrix (rowsSuccEquiv I r).symm
        (rowsSuccEquiv I r).symm).submatrix e.symm e.symm =
          recursiveTensorPower A r ⊗ₖ A
      rw [tensorPower_succ_submatrix]
      have hm : (tensorPower A r ⊗ₖ A).submatrix e.symm e.symm =
          ((tensorPower A r).submatrix (rowsRecursiveEquiv I r).symm
            (rowsRecursiveEquiv I r).symm) ⊗ₖ A := by ext x y; rfl
      rw [hm, ih]

omit [DecidableEq κ] in
theorem projectionFamily_submatrix {J : Type*} [Fintype J] [DecidableEq J]
    {P : κ → Matrix I I ℂ} (hP : Pinching.IsProjectionFamily P) (e : J ≃ I) :
    Pinching.IsProjectionFamily (fun i => (P i).submatrix e e) := by
  constructor
  · intro i
    exact (hP.selfAdjoint i).submatrix e
  · intro i
    rw [Matrix.submatrix_mul_equiv, hP.idempotent]
  · intro i j hij
    rw [Matrix.submatrix_mul_equiv, hP.orthogonal i j hij]
    rfl
  · ext x y
    have hs := congrArg (fun M : Matrix I I ℂ => M (e x) (e y)) hP.complete
    simpa [Matrix.sum_apply, Matrix.submatrix_apply, Matrix.one_apply] using hs

def recursiveOccupancyProjections (P : κ → Matrix I I ℂ) (r : ℕ) :
    Occupancy κ r → Matrix (RecursiveRows I r) (RecursiveRows I r) ℂ :=
  fun τ => (occupancyProjections P r τ).submatrix
    (rowsRecursiveEquiv I r).symm (rowsRecursiveEquiv I r).symm

def recursiveOccupancyPinching (P : κ → Matrix I I ℂ) (r : ℕ) :
    Matrix (RecursiveRows I r) (RecursiveRows I r) ℂ →ₗ[ℂ]
      Matrix (RecursiveRows I r) (RecursiveRows I r) ℂ :=
  Pinching.pinchingMap (recursiveOccupancyProjections P r)

theorem recursiveOccupancyProjections_family {P : κ → Matrix I I ℂ}
    (hP : Pinching.IsProjectionFamily P) (r : ℕ) :
    Pinching.IsProjectionFamily (recursiveOccupancyProjections P r) :=
  projectionFamily_submatrix (occupancyProjections_family hP r) (rowsRecursiveEquiv I r).symm

omit [Fintype I] in
theorem recursiveTensorPower_occupancy_decomposition (P : κ → Matrix I I ℂ)
    (eig : κ → ℂ) (r : ℕ) :
    recursiveTensorPower (Pinching.spectralCombination P eig) r =
      Pinching.spectralCombination (recursiveOccupancyProjections P r) (typeWeight eig) := by
  calc
    recursiveTensorPower (Pinching.spectralCombination P eig) r =
        (tensorPower (Pinching.spectralCombination P eig) r).submatrix
          (rowsRecursiveEquiv I r).symm (rowsRecursiveEquiv I r).symm :=
      (tensorPower_recursive_submatrix _ r).symm
    _ = (Pinching.spectralCombination (occupancyProjections P r) (typeWeight eig)).submatrix
          (rowsRecursiveEquiv I r).symm (rowsRecursiveEquiv I r).symm :=
      congrArg (fun M : Matrix (TensorRows I r) (TensorRows I r) ℂ =>
        M.submatrix (rowsRecursiveEquiv I r).symm (rowsRecursiveEquiv I r).symm)
          (tensorPower_occupancy_decomposition P eig r)
    _ = Pinching.spectralCombination (recursiveOccupancyProjections P r) (typeWeight eig) := by
      ext x y
      simp [Pinching.spectralCombination, recursiveOccupancyProjections,
        Matrix.sum_apply, Matrix.smul_apply, Matrix.submatrix_apply]

theorem recursiveOccupancyPinching_domination {P : κ → Matrix I I ℂ}
    (hP : Pinching.IsProjectionFamily P) (r : ℕ)
    {X : Matrix (RecursiveRows I r) (RecursiveRows I r) ℂ} (hX : X.PosSemidef) :
    (((((r + 1) ^ Fintype.card κ) : ℕ) : ℝ) • recursiveOccupancyPinching P r X - X).PosSemidef := by
  have h := Pinching.pinching_domination (recursiveOccupancyProjections_family hP r) hX
  simpa only [occupancy_card, recursiveOccupancyPinching] using h

theorem recursiveOccupancyPinching_domination_allReferences {P : κ → Matrix I I ℂ}
    (hP : Pinching.IsProjectionFamily P) (r : ℕ)
    (R : Type*) [Fintype R] [DecidableEq R]
    {X : Matrix (RecursiveRows I r × R) (RecursiveRows I r × R) ℂ} (hX : X.PosSemidef) :
    (((((r + 1) ^ Fintype.card κ) : ℕ) : ℝ) •
      DiamondControl.amplifyMap (recursiveOccupancyPinching P r) R X - X).PosSemidef := by
  have h := Pinching.pinching_domination_allReferences
    (recursiveOccupancyProjections_family hP r) R hX
  simpa only [occupancy_card, recursiveOccupancyPinching] using h

theorem recursiveOccupancyPinching_fixes_comparator {P : κ → Matrix I I ℂ}
    (hP : Pinching.IsProjectionFamily P) (eig : κ → ℂ) (r : ℕ) :
    recursiveOccupancyPinching P r (recursiveTensorPower (Pinching.spectralCombination P eig) r) =
      recursiveTensorPower (Pinching.spectralCombination P eig) r := by
  rw [recursiveTensorPower_occupancy_decomposition]
  exact Pinching.pinchingMap_fixes_spectralCombination
    (recursiveOccupancyProjections_family hP r) (typeWeight eig)

theorem recursiveOccupancyPinching_commutes_comparator {P : κ → Matrix I I ℂ}
    (hP : Pinching.IsProjectionFamily P) (eig : κ → ℂ) (r : ℕ)
    (X : Matrix (RecursiveRows I r) (RecursiveRows I r) ℂ) :
    Commute (recursiveOccupancyPinching P r X)
      (recursiveTensorPower (Pinching.spectralCombination P eig) r) := by
  rw [recursiveTensorPower_occupancy_decomposition]
  exact Pinching.pinching_commutes_spectralCombination
    (recursiveOccupancyProjections_family hP r) (typeWeight eig) X

theorem recursiveOccupancyPinching_CPTP {P : κ → Matrix I I ℂ}
    (hP : Pinching.IsProjectionFamily P) (r : ℕ) :
    DiamondControl.CompletelyPositive (recursiveOccupancyPinching P r) ∧
      ∀ X, (recursiveOccupancyPinching P r X).trace = X.trace :=
  ⟨Pinching.pinchingMap_completelyPositive (recursiveOccupancyProjections P r),
    Pinching.pinchingMap_tracePreserving (recursiveOccupancyProjections_family hP r)⟩

end QuantumProver.SuperchannelDiscrimination.TensorPinching

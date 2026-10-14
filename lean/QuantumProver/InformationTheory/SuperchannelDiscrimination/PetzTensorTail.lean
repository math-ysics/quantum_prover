import Mathlib
import QuantumProver.InformationTheory.SuperchannelDiscrimination.SpectralPinching
import QuantumProver.InformationTheory.SuperchannelDiscrimination.PetzMoments

set_option autoImplicit false

noncomputable section
open Matrix Filter
open scoped BigOperators Topology ComplexOrder MatrixOrder Matrix.Norms.L2Operator Matrix Kronecker

namespace QuantumProver.SuperchannelDiscrimination.PetzTensorTail

variable {I J κ γ : Type*} [Fintype I] [Fintype J] [Fintype κ] [Fintype γ]
  [DecidableEq I] [DecidableEq J]

theorem spectralCombination_mul {P : κ → Matrix I I ℂ}
    (hP : Pinching.IsProjectionFamily P) (a b : κ → ℂ) :
    Pinching.spectralCombination P (a * b) =
      Pinching.spectralCombination P a * Pinching.spectralCombination P b := by
  classical
  have hi (i : κ) : P i * Pinching.spectralCombination P b = b i • P i := by
    simp only [Pinching.spectralCombination, Matrix.mul_sum, Matrix.mul_smul]
    calc
      (∑ j, b j • (P i * P j)) = b i • (P i * P i) := by
        apply Finset.sum_eq_single i
        · intro j hj hji
          rw [hP.orthogonal i j (Ne.symm hji), smul_zero]
        · intro hi
          exact False.elim (hi (Finset.mem_univ i))
      _ = b i • P i := by rw [hP.idempotent]
  symm
  unfold Pinching.spectralCombination at ⊢
  rw [Matrix.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi'
  rw [Matrix.smul_mul]
  change a i • (P i * Pinching.spectralCombination P b) = (a i * b i) • P i
  rw [hi, smul_smul]

def projectionHom {P : κ → Matrix I I ℂ} (hP : Pinching.IsProjectionFamily P) :
    (κ → ℂ) →⋆ₐ[ℝ] Matrix I I ℂ where
  toFun := Pinching.spectralCombination P
  map_one' := by simpa [Pinching.spectralCombination] using hP.complete
  map_mul' := spectralCombination_mul hP
  map_zero' := by simp [Pinching.spectralCombination]
  map_add' a b := by simp [Pinching.spectralCombination, add_smul, Finset.sum_add_distrib]
  commutes' r := by
    change (∑ i, (r : ℂ) • P i) = algebraMap ℝ (Matrix I I ℂ) r
    rw [← Finset.smul_sum, hP.complete]
    ext x y
    simp [Algebra.algebraMap_eq_smul_one, Matrix.smul_apply]
  map_star' a := by
    simp only [Pinching.spectralCombination, star_sum, star_smul, Pi.star_apply,
      Matrix.star_eq_conjTranspose]
    apply Finset.sum_congr rfl
    intro i hi
    rw [(hP.selfAdjoint i).eq]

theorem projectionHom_apply {P : κ → Matrix I I ℂ} (hP : Pinching.IsProjectionFamily P)
    (a : κ → ℂ) : projectionHom hP a = Pinching.spectralCombination P a := rfl

theorem cfc_projectionFamily {P : κ → Matrix I I ℂ} (hP : Pinching.IsProjectionFamily P)
    (f : ℝ → ℝ) (d : κ → ℝ) :
    cfc f (Pinching.spectralCombination P (fun i => (d i : ℂ))) =
      Pinching.spectralCombination P (fun i => (f (d i) : ℂ)) := by
  classical
  let : IsometricContinuousFunctionalCalculus ℝ (κ → ℂ) IsSelfAdjoint :=
    IsSelfAdjoint.instIsometricContinuousFunctionalCalculus
  let a : κ → ℂ := fun i => (d i : ℂ)
  have ha : IsSelfAdjoint a := by ext i; simp [a]
  have hout : IsSelfAdjoint (projectionHom hP a) := by
    change star (projectionHom hP a) = projectionHom hP a
    rw [← map_star, ha]
  have hf : ContinuousOn f (spectrum ℝ a) := by
    apply Set.Finite.continuousOn
    rw [Pi.spectrum_eq]
    apply Set.finite_iUnion
    intro i
    exact (Set.finite_singleton (d i)).subset (CFC.spectrum_algebraMap_subset (A := ℂ) (d i))
  have hcont : Continuous (projectionHom hP) := by
    change Continuous (fun a : κ → ℂ => Pinching.spectralCombination P a)
    apply continuous_pi
    intro x
    apply continuous_pi
    intro y
    simp only [Pinching.spectralCombination, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    fun_prop
  have hmap := (projectionHom hP).map_cfc f a hf hcont ha hout
  rw [cfc_map_pi (S := ℝ) f a (by simpa only [← Pi.spectrum_eq] using hf) ha
    (fun i => by simp [a, IsSelfAdjoint])] at hmap
  have hscalar : (fun i => cfc f (a i)) = fun i => (f (d i) : ℂ) := by
    funext i
    exact cfc_algebraMap (R := ℝ) (A := ℂ) (d i) f
  rw [hscalar, projectionHom_apply, projectionHom_apply] at hmap
  exact hmap.symm

theorem cfc_diagonal_real (f : ℝ → ℝ) (d : I → ℝ) :
    cfc f (Matrix.diagonal (fun i => (d i : ℂ))) =
      Matrix.diagonal (fun i => (f (d i) : ℂ)) := by
  simpa only [SpectralPinching.coordinateProjection_combination] using
    cfc_projectionFamily (SpectralPinching.coordinateProjection_family (I := I)) f d

def unitaryKronecker (U : Matrix.unitaryGroup I ℂ) (V : Matrix.unitaryGroup J ℂ) :
    Matrix.unitaryGroup (I × J) ℂ :=
  ⟨(U : Matrix I I ℂ) ⊗ₖ (V : Matrix J J ℂ), by
    apply Matrix.mem_unitaryGroup_iff.mpr
    rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_kronecker,
      ← Matrix.mul_kronecker_mul]
    have hU : (U : Matrix I I ℂ) * (U : Matrix I I ℂ)ᴴ = 1 := Unitary.coe_mul_star_self U
    have hV : (V : Matrix J J ℂ) * (V : Matrix J J ℂ)ᴴ = 1 := Unitary.coe_mul_star_self V
    rw [hU, hV, Matrix.one_kronecker_one]⟩

theorem unitaryKronecker_conjugate (U : Matrix.unitaryGroup I ℂ)
    (V : Matrix.unitaryGroup J ℂ) (A : Matrix I I ℂ) (B : Matrix J J ℂ) :
    Unitary.conjStarAlgAut ℝ (Matrix (I × J) (I × J) ℂ) (unitaryKronecker U V) (A ⊗ₖ B) =
      (Unitary.conjStarAlgAut ℝ (Matrix I I ℂ) U A) ⊗ₖ
        (Unitary.conjStarAlgAut ℝ (Matrix J J ℂ) V B) := by
  change ((U : Matrix I I ℂ) ⊗ₖ (V : Matrix J J ℂ)) * (A ⊗ₖ B) *
    ((U : Matrix I I ℂ) ⊗ₖ (V : Matrix J J ℂ))ᴴ =
      ((U : Matrix I I ℂ) * A * (U : Matrix I I ℂ)ᴴ) ⊗ₖ
        ((V : Matrix J J ℂ) * B * (V : Matrix J J ℂ)ᴴ)
  rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
    ← Matrix.mul_kronecker_mul]

theorem cfc_unitary_conjugate (f : ℝ → ℝ) (U : Matrix.unitaryGroup I ℂ)
    {A : Matrix I I ℂ} (hA : A.IsHermitian) :
    cfc f (Unitary.conjStarAlgAut ℝ _ U A) =
      Unitary.conjStarAlgAut ℝ _ U (cfc f A) := by
  have hout : IsSelfAdjoint (Unitary.conjStarAlgAut ℝ _ U A) := by
    change star (Unitary.conjStarAlgAut ℝ _ U A) = Unitary.conjStarAlgAut ℝ _ U A
    rw [← map_star]
    exact congrArg (Unitary.conjStarAlgAut ℝ _ U) hA
  exact (StarAlgHomClass.map_cfc (Unitary.conjStarAlgAut ℝ _ U) f A
    (A.finite_real_spectrum.continuousOn _) (by
      change Continuous (fun X : Matrix I I ℂ =>
        (U : Matrix I I ℂ) * X * (U : Matrix I I ℂ)ᴴ)
      fun_prop) hA hout).symm

theorem cfc_kronecker_spectral (f : ℝ → ℝ) {A : Matrix I I ℂ} {B : Matrix J J ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    cfc f (A ⊗ₖ B) =
      Unitary.conjStarAlgAut ℝ (Matrix (I × J) (I × J) ℂ)
        (unitaryKronecker hA.eigenvectorUnitary hB.eigenvectorUnitary)
        (Matrix.diagonal (fun x : I × J =>
          (f (hA.eigenvalues x.1 * hB.eigenvalues x.2) : ℂ))) := by
  have hd : Matrix.diagonal (fun i => (hA.eigenvalues i : ℂ)) ⊗ₖ
      Matrix.diagonal (fun j => (hB.eigenvalues j : ℂ)) =
      Matrix.diagonal (fun x : I × J => ((hA.eigenvalues x.1 * hB.eigenvalues x.2 : ℝ) : ℂ)) := by
    rw [Matrix.diagonal_kronecker_diagonal]
    simp only [Complex.ofReal_mul]
  have heq : A ⊗ₖ B =
      Unitary.conjStarAlgAut ℝ (Matrix (I × J) (I × J) ℂ)
        (unitaryKronecker hA.eigenvectorUnitary hB.eigenvectorUnitary)
        (Matrix.diagonal (fun x : I × J => ((hA.eigenvalues x.1 * hB.eigenvalues x.2 : ℝ) : ℂ))) := by
    rw [← hd, unitaryKronecker_conjugate]
    exact congrArg₂ Matrix.kronecker hA.spectral_theorem hB.spectral_theorem
  have hdiag : (Matrix.diagonal (fun x : I × J =>
      ((hA.eigenvalues x.1 * hB.eigenvalues x.2 : ℝ) : ℂ))).IsHermitian := by
    simp [Matrix.IsHermitian, Matrix.diagonal_conjTranspose]
  rw [heq, cfc_unitary_conjugate f _ hdiag, cfc_diagonal_real]

theorem cfc_rpow_kronecker {A : Matrix I I ℂ} {B : Matrix J J ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) (p : ℝ) :
    cfc (fun x : ℝ => x ^ p) (A ⊗ₖ B) =
      cfc (fun x : ℝ => x ^ p) A ⊗ₖ cfc (fun x : ℝ => x ^ p) B := by
  rw [cfc_kronecker_spectral _ hA.1 hB.1,
    PetzMoments.cfc_spectral _ hA.1, PetzMoments.cfc_spectral _ hB.1,
    ← unitaryKronecker_conjugate]
  congr 1
  rw [Matrix.diagonal_kronecker_diagonal]
  congr 1
  funext x
  rw [Real.mul_rpow (hA.eigenvalues_nonneg x.1) (hB.eigenvalues_nonneg x.2), Complex.ofReal_mul]

theorem tensorMoment_kronecker {ρ σ : Matrix I I ℂ} {A B : Matrix J J ℂ}
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef)
    (hA : A.PosSemidef) (hB : B.PosSemidef) (s : ℝ) :
    PetzMoments.petzMoment (ρ ⊗ₖ A) (σ ⊗ₖ B) s =
      PetzMoments.petzMoment ρ σ s * PetzMoments.petzMoment A B s := by
  change (cfc (fun x : ℝ => x ^ (1 + s)) (ρ ⊗ₖ A) *
    cfc (fun x : ℝ => x ^ (-s)) (σ ⊗ₖ B)).trace.re = _
  rw [cfc_rpow_kronecker hρ hA, cfc_rpow_kronecker hσ hB,
    ← Matrix.mul_kronecker_mul, Matrix.trace_kronecker,
    PetzMoments.petzMoment_eq_complexTrace ρ σ s,
    PetzMoments.petzMoment_eq_complexTrace A B s]
  simp

theorem recursiveTensorPower_posSemidef {A : Matrix I I ℂ} (hA : A.PosSemidef) (r : ℕ) :
    (TensorPinching.recursiveTensorPower A r).PosSemidef := by
  induction r with
  | zero => exact Matrix.PosSemidef.one
  | succ r ih => exact ih.kronecker hA

theorem recursiveTensorPower_posDef {A : Matrix I I ℂ} (hA : A.PosDef) (r : ℕ) :
    (TensorPinching.recursiveTensorPower A r).PosDef := by
  induction r with
  | zero => exact Matrix.PosDef.one
  | succ r ih => exact ih.kronecker hA

omit [DecidableEq I] in
theorem recursiveRows_card_zero : Fintype.card (TensorPinching.RecursiveRows I 0) = 1 := by
  have hu : Unique (TensorPinching.RecursiveRows I 0) := by
    change Unique PUnit
    infer_instance
  exact @Fintype.card_unique (TensorPinching.RecursiveRows I 0) hu _

theorem recursiveTensorPower_density {A : Matrix I I ℂ}
    (hA : FlaggedStates.IsDensity A) (r : ℕ) :
    FlaggedStates.IsDensity (TensorPinching.recursiveTensorPower A r) := by
  induction r with
  | zero =>
      constructor
      · exact Matrix.PosSemidef.one
      · simp [TensorPinching.recursiveTensorPower, Matrix.trace, recursiveRows_card_zero]
  | succ r ih =>
      constructor
      · exact ih.1.kronecker hA.1
      · change (TensorPinching.recursiveTensorPower A r ⊗ₖ A).trace = 1
        rw [Matrix.trace_kronecker, ih.2, hA.2, one_mul]

theorem recursiveTensorMoment_power {ρ σ : Matrix I I ℂ}
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) (r : ℕ) (s : ℝ) :
    PetzMoments.petzMoment (TensorPinching.recursiveTensorPower ρ r)
      (TensorPinching.recursiveTensorPower σ r) s = (PetzMoments.petzMoment ρ σ s) ^ r := by
  induction r with
  | zero =>
      have hpower (p : ℝ) : cfc (fun x : ℝ => x ^ p)
          (1 : Matrix (TensorPinching.RecursiveRows I 0) (TensorPinching.RecursiveRows I 0) ℂ) = 1 := by
        simpa only [map_one, Real.one_rpow] using
          cfc_algebraMap (R := ℝ)
            (A := Matrix (TensorPinching.RecursiveRows I 0) (TensorPinching.RecursiveRows I 0) ℂ)
            1 (fun x : ℝ => x ^ p)
      change (cfc (fun x : ℝ => x ^ (1 + s)) (1 : Matrix
          (TensorPinching.RecursiveRows I 0) (TensorPinching.RecursiveRows I 0) ℂ) *
        cfc (fun x : ℝ => x ^ (-s)) 1).trace.re = 1
      rw [hpower, hpower, Matrix.one_mul]
      simp [Matrix.trace, Matrix.diag, recursiveRows_card_zero]
  | succ r ih =>
      change PetzMoments.petzMoment (TensorPinching.recursiveTensorPower ρ r ⊗ₖ ρ)
        (TensorPinching.recursiveTensorPower σ r ⊗ₖ σ) s = (PetzMoments.petzMoment ρ σ s) ^ (r + 1)
      rw [tensorMoment_kronecker (recursiveTensorPower_posSemidef hρ r)
        (recursiveTensorPower_posSemidef hσ r) hρ hσ, ih, pow_succ]

theorem iid_density_faithful_moments {ρ σ : Matrix I I ℂ}
    (hρ : FlaggedStates.IsDensity ρ) (hσ : σ.PosDef) (r : ℕ) (s : ℝ) :
    FlaggedStates.IsDensity (TensorPinching.recursiveTensorPower ρ r) ∧
      (TensorPinching.recursiveTensorPower σ r).PosDef ∧
      PetzMoments.petzMoment (TensorPinching.recursiveTensorPower ρ r)
        (TensorPinching.recursiveTensorPower σ r) s = (PetzMoments.petzMoment ρ σ s) ^ r :=
  ⟨recursiveTensorPower_density hρ r, recursiveTensorPower_posDef hσ r,
    recursiveTensorMoment_power hρ.1 hσ.posSemidef r s⟩

def eigenvalueSet {A : Matrix I I ℂ} (hA : A.IsHermitian) : Finset ℝ := by
  classical
  exact Finset.univ.image hA.eigenvalues

abbrev EigenLabel {A : Matrix I I ℂ} (hA : A.IsHermitian) := ↥(eigenvalueSet hA)

def eigenvalueLabel {A : Matrix I I ℂ} (hA : A.IsHermitian) (i : I) : EigenLabel hA :=
  ⟨hA.eigenvalues i, by
    classical
    apply Finset.mem_image.mpr
    exact ⟨i, Finset.mem_univ i, rfl⟩⟩

def coarseProjections {A : Matrix I I ℂ} (hA : A.IsHermitian) :
    EigenLabel hA → Matrix I I ℂ := by
  classical
  exact TensorPinching.groupedProjections (SpectralPinching.spectralProjections hA)
    (eigenvalueLabel hA)

theorem coarseProjections_family {A : Matrix I I ℂ} (hA : A.IsHermitian) :
    Pinching.IsProjectionFamily (coarseProjections hA) := by
  classical
  exact TensorPinching.groupedProjections_family (SpectralPinching.spectralProjections_family hA)
    (eigenvalueLabel hA)

theorem coarseProjections_reconstruction {A : Matrix I I ℂ} (hA : A.IsHermitian) :
    Pinching.spectralCombination (coarseProjections hA) (fun v => (v.val : ℂ)) = A := by
  classical
  change (∑ v, (v.val : ℂ) • TensorPinching.groupedProjections
    (SpectralPinching.spectralProjections hA) (eigenvalueLabel hA) v) = A
  rw [TensorPinching.groupedProjections_weighted_sum]
  exact SpectralPinching.spectralProjections_reconstruction hA

theorem cfc_coarseProjection {A : Matrix I I ℂ} (hA : A.IsHermitian) (v : EigenLabel hA) :
    cfc (fun x : ℝ => if x = v.val then 1 else 0) A = coarseProjections hA v := by
  classical
  have h := cfc_projectionFamily (coarseProjections_family hA)
    (fun x : ℝ => if x = v.val then 1 else 0) (fun w => w.val)
  rw [coarseProjections_reconstruction] at h
  have he : Pinching.spectralCombination (coarseProjections hA)
      (fun w => ((if w.val = v.val then 1 else 0 : ℝ) : ℂ)) = coarseProjections hA v := by
    unfold Pinching.spectralCombination
    rw [Finset.sum_eq_single v]
    · simp
    · intro w hw hwv
      have hval : w.val ≠ v.val := fun he => hwv (Subtype.ext he)
      simp [hval]
    · intro hv
      exact False.elim (hv (Finset.mem_univ v))
  rw [he] at h
  exact h

theorem eigenLabel_nonneg {A : Matrix I I ℂ} (hA : A.PosSemidef) (v : EigenLabel hA.1) :
    0 ≤ v.val := by
  classical
  obtain ⟨i, hi, he⟩ := Finset.mem_image.mp v.property
  rw [← he]
  exact hA.eigenvalues_nonneg i

theorem eigenLabel_pos {A : Matrix I I ℂ} (hA : A.PosDef) (v : EigenLabel hA.1) :
    0 < v.val := by
  classical
  obtain ⟨i, hi, he⟩ := Finset.mem_image.mp v.property
  rw [← he]
  exact hA.eigenvalues_pos i

theorem scalarWeightedJensen (p : ℝ) (hp : 1 ≤ p) (w a : κ → ℝ)
    (hw : ∀ i, 0 ≤ w i) (ha : ∀ i, 0 ≤ a i) (q b : ℝ)
    (hq : 0 ≤ q) (hsum : (∑ i, w i) = q) (hmean : (∑ i, w i * a i) = b * q) :
    q * b ^ p ≤ ∑ i, w i * a i ^ p := by
  classical
  by_cases hq0 : q = 0
  · rw [hq0, zero_mul]
    exact Finset.sum_nonneg fun i hi => mul_nonneg (hw i) (Real.rpow_nonneg (ha i) p)
  · have hqpos : 0 < q := lt_of_le_of_ne hq (Ne.symm hq0)
    have hs : (∑ i, w i / q) = 1 := by rw [← Finset.sum_div, hsum, div_self hq0]
    have hj := (convexOn_rpow hp).map_sum_le
      (t := Finset.univ) (w := fun i => w i / q) (p := a)
      (fun i hi => div_nonneg (hw i) hq) hs (fun i hi => ha i)
    simp only [smul_eq_mul, div_mul_eq_mul_div, ← Finset.sum_div] at hj
    rw [hmean, mul_div_cancel_right₀ _ hq0] at hj
    have h := (le_div_iff₀ hqpos).mp hj
    simpa only [mul_comm q] using h

def productProjections (P : κ → Matrix I I ℂ) (Q : γ → Matrix I I ℂ)
    (v : κ × γ) : Matrix I I ℂ := P v.1 * Q v.2

theorem productProjections_family {P : κ → Matrix I I ℂ} {Q : γ → Matrix I I ℂ}
    (hP : Pinching.IsProjectionFamily P) (hQ : Pinching.IsProjectionFamily Q)
    (hpq : ∀ i j, Commute (P i) (Q j)) :
    Pinching.IsProjectionFamily (productProjections P Q) := by
  constructor
  · intro v
    change (P v.1 * Q v.2)ᴴ = P v.1 * Q v.2
    rw [Matrix.conjTranspose_mul, (hP.selfAdjoint v.1).eq, (hQ.selfAdjoint v.2).eq,
      ← (hpq v.1 v.2).eq]
  · intro v
    change (P v.1 * Q v.2) * (P v.1 * Q v.2) = P v.1 * Q v.2
    calc
      (P v.1 * Q v.2) * (P v.1 * Q v.2) = P v.1 * (Q v.2 * P v.1) * Q v.2 := by
        simp only [Matrix.mul_assoc]
      _ = P v.1 * (P v.1 * Q v.2) * Q v.2 := by rw [← (hpq v.1 v.2).eq]
      _ = (P v.1 * P v.1) * (Q v.2 * Q v.2) := by simp only [Matrix.mul_assoc]
      _ = P v.1 * Q v.2 := by rw [hP.idempotent, hQ.idempotent]
  · intro v w hvw
    change (P v.1 * Q v.2) * (P w.1 * Q w.2) = 0
    have he : (P v.1 * Q v.2) * (P w.1 * Q w.2) =
        (P v.1 * P w.1) * (Q v.2 * Q w.2) := by
      calc
        (P v.1 * Q v.2) * (P w.1 * Q w.2) = P v.1 * (Q v.2 * P w.1) * Q w.2 := by
          simp only [Matrix.mul_assoc]
        _ = P v.1 * (P w.1 * Q v.2) * Q w.2 := by rw [← (hpq w.1 v.2).eq]
        _ = (P v.1 * P w.1) * (Q v.2 * Q w.2) := by simp only [Matrix.mul_assoc]
    rw [he]
    obtain (h1 | h2) : v.1 ≠ w.1 ∨ v.2 ≠ w.2 := by
      rwa [Ne.eq_def, Prod.ext_iff, not_and_or] at hvw
    · rw [hP.orthogonal v.1 w.1 h1, Matrix.zero_mul]
    · rw [hQ.orthogonal v.2 w.2 h2, Matrix.mul_zero]
  · change (∑ v : κ × γ, P v.1 * Q v.2) = 1
    rw [Fintype.sum_prod_type]
    simp_rw [← Matrix.mul_sum, hQ.complete, Matrix.mul_one]
    exact hP.complete

theorem coarseProjections_commute {A B : Matrix I I ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (hAB : Commute A B)
    (v : EigenLabel hA) (w : EigenLabel hB) :
    Commute (coarseProjections hA v) (coarseProjections hB w) := by
  rw [← cfc_coarseProjection hA v, ← cfc_coarseProjection hB w]
  exact ((hAB.cfc_real _).symm.cfc_real _).symm

def jointProjections {A B : Matrix I I ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian) :
    EigenLabel hA × EigenLabel hB → Matrix I I ℂ :=
  productProjections (coarseProjections hA) (coarseProjections hB)

theorem jointProjections_family {A B : Matrix I I ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (hAB : Commute A B) :
    Pinching.IsProjectionFamily (jointProjections hA hB) :=
  productProjections_family (coarseProjections_family hA) (coarseProjections_family hB)
    (coarseProjections_commute hA hB hAB)

theorem jointProjections_left {A B : Matrix I I ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    Pinching.spectralCombination (jointProjections hA hB) (fun v => (v.1.val : ℂ)) = A := by
  change (∑ v : EigenLabel hA × EigenLabel hB,
    (v.1.val : ℂ) • (coarseProjections hA v.1 * coarseProjections hB v.2)) = A
  rw [Fintype.sum_prod_type]
  simp_rw [← Matrix.smul_mul, ← Matrix.mul_sum, (coarseProjections_family hB).complete,
    Matrix.mul_one]
  exact coarseProjections_reconstruction hA

theorem jointProjections_right {A B : Matrix I I ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    Pinching.spectralCombination (jointProjections hA hB) (fun v => (v.2.val : ℂ)) = B := by
  have hrec : (∑ v : EigenLabel hB, (v.val : ℂ) • coarseProjections hB v) = B :=
    coarseProjections_reconstruction hB
  change (∑ v : EigenLabel hA × EigenLabel hB,
    (v.2.val : ℂ) • (coarseProjections hA v.1 * coarseProjections hB v.2)) = B
  rw [Fintype.sum_prod_type]
  simp_rw [← Matrix.mul_smul, ← Matrix.mul_sum, hrec]
  rw [← Matrix.sum_mul, (coarseProjections_family hA).complete, Matrix.one_mul]

theorem cfc_joint_left {A B : Matrix I I ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (hAB : Commute A B) (f : ℝ → ℝ) :
    cfc f A = Pinching.spectralCombination (jointProjections hA hB)
      (fun v => (f v.1.val : ℂ)) := by
  have h := cfc_projectionFamily (jointProjections_family hA hB hAB) f (fun v => v.1.val)
  rw [jointProjections_left] at h
  exact h

theorem cfc_joint_right {A B : Matrix I I ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (hAB : Commute A B) (f : ℝ → ℝ) :
    cfc f B = Pinching.spectralCombination (jointProjections hA hB)
      (fun v => (f v.2.val : ℂ)) := by
  have h := cfc_projectionFamily (jointProjections_family hA hB hAB) f (fun v => v.2.val)
  rw [jointProjections_right] at h
  exact h

omit [DecidableEq I] in
theorem trace_spectralCombination_real (P : κ → Matrix I I ℂ) (d : κ → ℝ) :
    (Pinching.spectralCombination P (fun i => (d i : ℂ))).trace.re =
      ∑ i, d i * (P i).trace.re := by
  simp [Pinching.spectralCombination, Matrix.trace_sum, Matrix.trace_smul, Complex.re_sum]

theorem jointMoment_formula {A B : Matrix I I ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (hAB : Commute A B) (s : ℝ) :
    PetzMoments.petzMoment A B s =
      ∑ v : EigenLabel hA × EigenLabel hB, v.1.val ^ (1 + s) * v.2.val ^ (-s) *
        (jointProjections hA hB v).trace.re := by
  unfold PetzMoments.petzMoment
  rw [cfc_joint_left hA hB hAB, cfc_joint_right hA hB hAB,
    ← spectralCombination_mul (jointProjections_family hA hB hAB)]
  have he : (fun v : EigenLabel hA × EigenLabel hB => ((v.1.val ^ (1 + s) : ℝ) : ℂ)) *
      (fun v => ((v.2.val ^ (-s) : ℝ) : ℂ)) =
      fun v => ((v.1.val ^ (1 + s) * v.2.val ^ (-s) : ℝ) : ℂ) := by
    ext v
    simp
  rw [he, trace_spectralCombination_real]

omit [Fintype I] [DecidableEq I] in
theorem spectralCombination_single [DecidableEq κ] (P : κ → Matrix I I ℂ) (i : κ) (c : ℂ) :
    Pinching.spectralCombination P (Pi.single i c) = c • P i := by
  simp [Pinching.spectralCombination, Pi.single_apply]

theorem spectralCombination_mul_projection {P : κ → Matrix I I ℂ}
    (hP : Pinching.IsProjectionFamily P) (a : κ → ℂ) (i : κ) :
    Pinching.spectralCombination P a * P i = a i • P i := by
  classical
  have hsingle : Pinching.spectralCombination P (Pi.single i 1) = P i := by
    simpa using spectralCombination_single P i 1
  have he : a * Pi.single i 1 = Pi.single i (a i) := by
    ext j
    by_cases hji : j = i <;> simp [hji]
  calc
    Pinching.spectralCombination P a * P i =
        Pinching.spectralCombination P a * Pinching.spectralCombination P (Pi.single i 1) :=
      congrArg (fun M => Pinching.spectralCombination P a * M) hsingle.symm
    _ = Pinching.spectralCombination P (a * Pi.single i 1) :=
      (spectralCombination_mul hP a _).symm
    _ = Pinching.spectralCombination P (Pi.single i (a i)) := congrArg _ he
    _ = a i • P i := spectralCombination_single P i (a i)

omit [DecidableEq I] in
theorem trace_spectralCombination_mul_real (P : κ → Matrix I I ℂ)
    (d : κ → ℝ) (Q : Matrix I I ℂ) :
    (Pinching.spectralCombination P (fun i => (d i : ℂ)) * Q).trace.re =
      ∑ i, d i * (P i * Q).trace.re := by
  simp [Pinching.spectralCombination, Matrix.sum_mul, Matrix.smul_mul,
    Matrix.trace_sum, Matrix.trace_smul, Complex.re_sum]

omit [DecidableEq I] in
theorem trace_mul_spectralCombination_real (X : Matrix I I ℂ)
    (P : κ → Matrix I I ℂ) (d : κ → ℝ) :
    (X * Pinching.spectralCombination P (fun i => (d i : ℂ))).trace.re =
      ∑ i, d i * (X * P i).trace.re := by
  simp [Pinching.spectralCombination, Matrix.mul_sum, Matrix.mul_smul,
    Matrix.trace_sum, Matrix.trace_smul, Complex.re_sum]

theorem trace_projection_weights_sum {P : κ → Matrix I I ℂ}
    (hP : Pinching.IsProjectionFamily P) (Q : Matrix I I ℂ) :
    (∑ i, (P i * Q).trace.re) = Q.trace.re := by
  have h := congrArg (fun M : Matrix I I ℂ => (M * Q).trace.re) hP.complete
  simpa only [Matrix.sum_mul, Matrix.trace_sum, Complex.re_sum, Matrix.one_mul] using h

theorem trace_mul_projection_nonneg {P : κ → Matrix I I ℂ}
    (hP : Pinching.IsProjectionFamily P) (i : κ) {A : Matrix I I ℂ} (hA : A.PosSemidef) :
    0 ≤ (A * P i).trace.re := by
  have hc := hA.mul_mul_conjTranspose_same (P i)
  have htrace : (P i * A * (P i)ᴴ).trace = (A * P i).trace := by
    rw [(hP.selfAdjoint i).eq, Matrix.trace_mul_cycle, hP.idempotent, Matrix.trace_mul_comm]
  have hn := (RCLike.nonneg_iff.mp hc.trace_nonneg).1
  rw [htrace] at hn
  exact hn

theorem cfc_spectralProjections (f : ℝ → ℝ) {A : Matrix I I ℂ} (hA : A.IsHermitian) :
    cfc f A = Pinching.spectralCombination (SpectralPinching.spectralProjections hA)
      (fun i => (f (hA.eigenvalues i) : ℂ)) := by
  have h := cfc_projectionFamily (SpectralPinching.spectralProjections_family hA) f hA.eigenvalues
  rw [SpectralPinching.spectralProjections_reconstruction] at h
  exact h

theorem pinching_trace_pairing {P : κ → Matrix I I ℂ}
    (hP : Pinching.IsProjectionFamily P) (X Y : Matrix I I ℂ) :
    (Pinching.pinchingMap P X * Y).trace = (X * Pinching.pinchingMap P Y).trace := by
  rw [Pinching.pinchingMap_apply P hP.selfAdjoint X,
    Pinching.pinchingMap_apply P hP.selfAdjoint Y]
  simp only [Matrix.sum_mul, Matrix.mul_sum, Matrix.trace_sum]
  apply Finset.sum_congr rfl
  intro i hi
  calc
    (P i * X * P i * Y).trace = (P i * (X * P i * Y)).trace := by
      simp only [Matrix.mul_assoc]
    _ = (X * P i * Y * P i).trace := Matrix.trace_mul_comm _ _
    _ = (X * (P i * Y * P i)).trace := by simp only [Matrix.mul_assoc]

theorem pinching_trace_pairing_fixed {P : κ → Matrix I I ℂ}
    (hP : Pinching.IsProjectionFamily P) (X Y : Matrix I I ℂ)
    (hY : Pinching.pinchingMap P Y = Y) :
    (Pinching.pinchingMap P X * Y).trace = (X * Y).trace := by
  rw [pinching_trace_pairing hP, hY]

theorem pinching_joint_projection_fixed {P : κ → Matrix I I ℂ}
    (hP : Pinching.IsProjectionFamily P) (X : Matrix I I ℂ) (d : κ → ℂ)
    (hA : (Pinching.pinchingMap P X).IsHermitian)
    (hB : (Pinching.spectralCombination P d).IsHermitian)
    (v : EigenLabel hA × EigenLabel hB) :
    Pinching.pinchingMap P (jointProjections hA hB v) = jointProjections hA hB v := by
  apply Pinching.pinchingMap_fixes_commutant hP
  intro i
  have ha : Commute (P i) (coarseProjections hA v.1) := by
    rw [← cfc_coarseProjection]
    exact ((Pinching.pinching_commutes_projector hP i X).symm.cfc_real _).symm
  have hb : Commute (P i) (coarseProjections hB v.2) := by
    rw [← cfc_coarseProjection]
    have h := Pinching.pinching_commutes_projector hP i (Pinching.spectralCombination P d)
    rw [Pinching.pinchingMap_fixes_spectralCombination hP] at h
    exact (h.symm.cfc_real _).symm
  exact ha.mul_right hb

theorem pinching_power_trace_projection_le {P : κ → Matrix I I ℂ}
    (hP : Pinching.IsProjectionFamily P) {ρ : Matrix I I ℂ} (hρ : ρ.PosSemidef)
    {Q : γ → Matrix I I ℂ} (hQ : Pinching.IsProjectionFamily Q) (j : γ)
    (hfix : Pinching.pinchingMap P (Q j) = Q j) (a s : ℝ) (hs : 0 ≤ s)
    (hAQ : Pinching.pinchingMap P ρ * Q j = (a : ℂ) • Q j) :
    a ^ (1 + s) * (Q j).trace.re ≤
      (cfc (fun x : ℝ => x ^ (1 + s)) ρ * Q j).trace.re := by
  classical
  let R := SpectralPinching.spectralProjections hρ.1
  have hR : Pinching.IsProjectionFamily R := SpectralPinching.spectralProjections_family hρ.1
  have hq : 0 ≤ (Q j).trace.re :=
    (RCLike.nonneg_iff.mp (Pinching.projection_posSemidef hQ j).trace_nonneg).1
  have hw (i : I) : 0 ≤ (R i * Q j).trace.re :=
    trace_mul_projection_nonneg hQ j (Pinching.projection_posSemidef hR i)
  have hmean : (∑ i, (R i * Q j).trace.re * hρ.1.eigenvalues i) =
      a * (Q j).trace.re := by
    calc
      (∑ i, (R i * Q j).trace.re * hρ.1.eigenvalues i) =
          ∑ i, hρ.1.eigenvalues i * (R i * Q j).trace.re := by
        apply Finset.sum_congr rfl
        intro i hi
        exact mul_comm _ _
      _ = (ρ * Q j).trace.re := by
        rw [← trace_spectralCombination_mul_real]
        exact congrArg (fun M : Matrix I I ℂ => (M * Q j).trace.re)
          (SpectralPinching.spectralProjections_reconstruction hρ.1)
      _ = (Pinching.pinchingMap P ρ * Q j).trace.re :=
        (congrArg Complex.re (pinching_trace_pairing_fixed hP ρ (Q j) hfix)).symm
      _ = a * (Q j).trace.re := by rw [hAQ]; simp [Matrix.trace_smul]
  have hj := scalarWeightedJensen (1 + s) (by linarith)
    (fun i => (R i * Q j).trace.re) hρ.1.eigenvalues hw hρ.eigenvalues_nonneg
    (Q j).trace.re a hq (trace_projection_weights_sum hR (Q j)) hmean
  calc
    a ^ (1 + s) * (Q j).trace.re = (Q j).trace.re * a ^ (1 + s) := mul_comm _ _
    _ ≤ ∑ i, (R i * Q j).trace.re * (hρ.1.eigenvalues i) ^ (1 + s) := hj
    _ = ∑ i, (hρ.1.eigenvalues i) ^ (1 + s) * (R i * Q j).trace.re := by
      apply Finset.sum_congr rfl
      intro i hi
      exact mul_comm _ _
    _ = (cfc (fun x : ℝ => x ^ (1 + s)) ρ * Q j).trace.re := by
      rw [cfc_spectralProjections _ hρ.1, trace_spectralCombination_mul_real]

theorem pinchingMoment_le {P : κ → Matrix I I ℂ}
    (hP : Pinching.IsProjectionFamily P) {ρ : Matrix I I ℂ} (hρ : ρ.PosSemidef)
    (d : κ → ℂ) (hσ : (Pinching.spectralCombination P d).PosDef)
    (s : ℝ) (hs : 0 ≤ s) :
    PetzMoments.petzMoment (Pinching.pinchingMap P ρ) (Pinching.spectralCombination P d) s ≤
      PetzMoments.petzMoment ρ (Pinching.spectralCombination P d) s := by
  classical
  let A := Pinching.pinchingMap P ρ
  let B := Pinching.spectralCombination P d
  have hA : A.PosSemidef := Pinching.pinchingMap_posSemidef P hρ
  have hB : B.PosDef := hσ
  have hAB : Commute A B := Pinching.pinching_commutes_spectralCombination hP d ρ
  let Q := jointProjections hA.1 hB.1
  have hQ : Pinching.IsProjectionFamily Q := jointProjections_family hA.1 hB.1 hAB
  have hj (v : EigenLabel hA.1 × EigenLabel hB.1) :
      v.1.val ^ (1 + s) * (Q v).trace.re ≤
        (cfc (fun x : ℝ => x ^ (1 + s)) ρ * Q v).trace.re := by
    apply pinching_power_trace_projection_le hP hρ hQ v
      (pinching_joint_projection_fixed hP ρ d hA.1 hB.1 v) v.1.val s hs
    calc
      A * Q v = Pinching.spectralCombination Q (fun w => (w.1.val : ℂ)) * Q v :=
        congrArg (fun M : Matrix I I ℂ => M * Q v)
          (jointProjections_left hA.1 hB.1).symm
      _ = (v.1.val : ℂ) • Q v := spectralCombination_mul_projection hQ _ v
  calc
    PetzMoments.petzMoment A B s =
        ∑ v : EigenLabel hA.1 × EigenLabel hB.1,
          v.1.val ^ (1 + s) * v.2.val ^ (-s) * (Q v).trace.re :=
      jointMoment_formula hA.1 hB.1 hAB s
    _ ≤ ∑ v : EigenLabel hA.1 × EigenLabel hB.1,
        v.2.val ^ (-s) * (cfc (fun x : ℝ => x ^ (1 + s)) ρ * Q v).trace.re := by
      apply Finset.sum_le_sum
      intro v hv
      have hm := mul_le_mul_of_nonneg_left (hj v)
        (Real.rpow_nonneg (le_of_lt (eigenLabel_pos hB v.2)) (-s))
      simpa only [mul_assoc, mul_left_comm, mul_comm] using hm
    _ = PetzMoments.petzMoment ρ B s := by
      unfold PetzMoments.petzMoment
      rw [cfc_joint_right hA.1 hB.1 hAB, trace_mul_spectralCombination_real]

theorem scalarLikelihoodMarkov (a b t s : ℝ) (ha : 0 ≤ a)
    (hb : 0 < b) (ht : 0 < t) (hs : 0 ≤ s) :
    a * (if 0 < a - t * b then 1 else 0) ≤ t ^ (-s) * a ^ (1 + s) * b ^ (-s) := by
  have htb : 0 < t * b := mul_pos ht hb
  by_cases hact : 0 < a - t * b
  · rw [ite_eq_left hact, mul_one]
    have hapos : 0 < a := by linarith
    have hpow := Real.rpow_le_rpow htb.le (by linarith : t * b ≤ a) hs
    calc
      a = (a * (t * b) ^ (-s)) * (t * b) ^ s := by
        rw [mul_assoc, ← Real.rpow_add htb, neg_add_cancel, Real.rpow_zero, mul_one]
      _ ≤ (a * (t * b) ^ (-s)) * a ^ s :=
        mul_le_mul_of_nonneg_left hpow (mul_nonneg ha (Real.rpow_nonneg htb.le (-s)))
      _ = t ^ (-s) * a ^ (1 + s) * b ^ (-s) := by
        rw [Real.mul_rpow ht.le hb.le, Real.rpow_add hapos, Real.rpow_one]
        ring
  · rw [ite_eq_right hact, mul_zero]
    exact mul_nonneg (mul_nonneg (Real.rpow_nonneg ht.le (-s))
      (Real.rpow_nonneg ha (1 + s))) (Real.rpow_nonneg hb.le (-s))

theorem spectralCombination_posSemidef {P : κ → Matrix I I ℂ}
    (hP : Pinching.IsProjectionFamily P) (d : κ → ℝ) (hd : ∀ i, 0 ≤ d i) :
    (Pinching.spectralCombination P (fun i => (d i : ℂ))).PosSemidef := by
  change (∑ i, d i • P i).PosSemidef
  exact Matrix.posSemidef_sum Finset.univ
    (fun i hi => (Pinching.projection_posSemidef hP i).smul (hd i))

theorem spectralCombination_isEffect {P : κ → Matrix I I ℂ}
    (hP : Pinching.IsProjectionFamily P) (d : κ → ℝ)
    (hd0 : ∀ i, 0 ≤ d i) (hd1 : ∀ i, d i ≤ 1) :
    FlaggedStates.IsEffect (Pinching.spectralCombination P (fun i => (d i : ℂ))) := by
  constructor
  · exact spectralCombination_posSemidef hP d hd0
  · have he : Pinching.spectralCombination P (fun i => ((1 - d i : ℝ) : ℂ)) =
        1 - Pinching.spectralCombination P (fun i => (d i : ℂ)) := by
      simp [Pinching.spectralCombination, Complex.ofReal_sub, sub_smul,
        Finset.sum_sub_distrib, hP.complete]
    rw [← he]
    exact spectralCombination_posSemidef hP _ (fun i => sub_nonneg.mpr (hd1 i))

def positiveIndicator (x : ℝ) : ℝ := if 0 < x then 1 else 0

def positiveSpectralTest (H : Matrix I I ℂ) : Matrix I I ℂ := cfc positiveIndicator H

theorem positiveSpectralTest_isEffect {H : Matrix I I ℂ} (hH : H.IsHermitian) :
    FlaggedStates.IsEffect (positiveSpectralTest H) := by
  unfold positiveSpectralTest
  rw [cfc_spectralProjections _ hH]
  apply spectralCombination_isEffect (SpectralPinching.spectralProjections_family hH)
  · intro i
    unfold positiveIndicator
    split_ifs <;> norm_num
  · intro i
    unfold positiveIndicator
    split_ifs <;> norm_num

def spectralUpperTail (A B : Matrix I I ℂ) (t : ℝ) : Matrix I I ℂ :=
  positiveSpectralTest (A - t • B)

theorem spectralUpperTail_joint {A B : Matrix I I ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (hAB : Commute A B) (t : ℝ) :
    spectralUpperTail A B t = Pinching.spectralCombination (jointProjections hA hB)
      (fun v => (positiveIndicator (v.1.val - t * v.2.val) : ℂ)) := by
  have he : Pinching.spectralCombination (jointProjections hA hB)
      (fun v => ((v.1.val - t * v.2.val : ℝ) : ℂ)) = A - t • B := by
    calc
      Pinching.spectralCombination (jointProjections hA hB)
          (fun v => ((v.1.val - t * v.2.val : ℝ) : ℂ)) =
          Pinching.spectralCombination (jointProjections hA hB) (fun v => (v.1.val : ℂ)) -
            t • Pinching.spectralCombination (jointProjections hA hB) (fun v => (v.2.val : ℂ)) := by
        simp only [Pinching.spectralCombination]
        rw [Finset.smul_sum, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro v hv
        ext i j
        change ((v.1.val - t * v.2.val : ℝ) : ℂ) * (jointProjections hA hB v) i j =
          (v.1.val : ℂ) * (jointProjections hA hB v) i j -
            (t : ℂ) * ((v.2.val : ℂ) * (jointProjections hA hB v) i j)
        rw [Complex.ofReal_sub, Complex.ofReal_mul]
        ring
      _ = A - t • B := by rw [jointProjections_left, jointProjections_right]
  unfold spectralUpperTail positiveSpectralTest
  exact (congrArg (cfc positiveIndicator) he).symm.trans
    (cfc_projectionFamily (jointProjections_family hA hB hAB) positiveIndicator _)

theorem spectralUpperTail_trace_formula {A B : Matrix I I ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (hAB : Commute A B) (t : ℝ) :
    (A * spectralUpperTail A B t).trace.re =
      ∑ v : EigenLabel hA × EigenLabel hB,
        v.1.val * positiveIndicator (v.1.val - t * v.2.val) *
          (jointProjections hA hB v).trace.re := by
  rw [spectralUpperTail_joint hA hB hAB, trace_mul_spectralCombination_real]
  apply Finset.sum_congr rfl
  intro v hv
  have he : A * jointProjections hA hB v = (v.1.val : ℂ) • jointProjections hA hB v := by
    calc
      A * jointProjections hA hB v =
          Pinching.spectralCombination (jointProjections hA hB) (fun w => (w.1.val : ℂ)) *
            jointProjections hA hB v :=
        congrArg (fun M : Matrix I I ℂ => M * jointProjections hA hB v)
          (jointProjections_left hA hB).symm
      _ = _ := spectralCombination_mul_projection (jointProjections_family hA hB hAB) _ v
  rw [he, Matrix.trace_smul]
  simp only [smul_eq_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  ring

theorem commutingLikelihoodTail_le {A B : Matrix I I ℂ}
    (hA : A.PosSemidef) (hB : B.PosDef) (hAB : Commute A B)
    (t s : ℝ) (ht : 0 < t) (hs : 0 ≤ s) :
    (A * spectralUpperTail A B t).trace.re ≤ t ^ (-s) * PetzMoments.petzMoment A B s := by
  classical
  rw [spectralUpperTail_trace_formula hA.1 hB.1 hAB, jointMoment_formula hA.1 hB.1 hAB,
    Finset.mul_sum]
  apply Finset.sum_le_sum
  intro v hv
  have hq : 0 ≤ (jointProjections hA.1 hB.1 v).trace.re :=
    (RCLike.nonneg_iff.mp
      (Pinching.projection_posSemidef (jointProjections_family hA.1 hB.1 hAB) v).trace_nonneg).1
  have h := mul_le_mul_of_nonneg_right
    (scalarLikelihoodMarkov v.1.val v.2.val t s (eigenLabel_nonneg hA v.1)
      (eigenLabel_pos hB v.2) ht hs) hq
  simpa only [positiveIndicator, mul_assoc] using h

theorem pinching_upperTail_fixed {P : κ → Matrix I I ℂ}
    (hP : Pinching.IsProjectionFamily P) {ρ : Matrix I I ℂ} (hρ : ρ.PosSemidef)
    (d : κ → ℂ) (hσ : (Pinching.spectralCombination P d).PosDef) (t : ℝ) :
    Pinching.pinchingMap P
      (spectralUpperTail (Pinching.pinchingMap P ρ) (Pinching.spectralCombination P d) t) =
      spectralUpperTail (Pinching.pinchingMap P ρ) (Pinching.spectralCombination P d) t := by
  have hA := Pinching.pinchingMap_posSemidef P hρ
  have hAB := Pinching.pinching_commutes_spectralCombination hP d ρ
  rw [spectralUpperTail_joint hA.1 hσ.1 hAB]
  simp only [Pinching.spectralCombination, map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro v hv
  exact congrArg (fun M : Matrix I I ℂ =>
    (positiveIndicator (v.1.val - t * v.2.val) : ℂ) • M)
    (pinching_joint_projection_fixed hP ρ d hA.1 hσ.1 v)

theorem pinchedLikelihoodTail_le {P : κ → Matrix I I ℂ}
    (hP : Pinching.IsProjectionFamily P) {ρ : Matrix I I ℂ} (hρ : ρ.PosSemidef)
    (d : κ → ℂ) (hσ : (Pinching.spectralCombination P d).PosDef)
    (t s : ℝ) (ht : 0 < t) (hs : 0 ≤ s) :
    (ρ * spectralUpperTail (Pinching.pinchingMap P ρ) (Pinching.spectralCombination P d) t).trace.re ≤
      t ^ (-s) * PetzMoments.petzMoment ρ (Pinching.spectralCombination P d) s := by
  have hA := Pinching.pinchingMap_posSemidef P hρ
  have hAB := Pinching.pinching_commutes_spectralCombination hP d ρ
  calc
    _ = (Pinching.pinchingMap P ρ *
        spectralUpperTail (Pinching.pinchingMap P ρ) (Pinching.spectralCombination P d) t).trace.re :=
      (congrArg Complex.re (pinching_trace_pairing_fixed hP ρ _
        (pinching_upperTail_fixed hP hρ d hσ t))).symm
    _ ≤ t ^ (-s) * PetzMoments.petzMoment
        (Pinching.pinchingMap P ρ) (Pinching.spectralCombination P d) s :=
      commutingLikelihoodTail_le hA hσ hAB t s ht hs
    _ ≤ t ^ (-s) * PetzMoments.petzMoment ρ (Pinching.spectralCombination P d) s :=
      mul_le_mul_of_nonneg_left (pinchingMoment_le hP hρ d hσ s hs) (Real.rpow_nonneg ht.le (-s))

theorem positiveSpectralTest_idempotent {H : Matrix I I ℂ} (hH : H.IsHermitian) :
    positiveSpectralTest H * positiveSpectralTest H = positiveSpectralTest H := by
  classical
  unfold positiveSpectralTest
  rw [cfc_spectralProjections _ hH,
    ← spectralCombination_mul (SpectralPinching.spectralProjections_family hH)]
  congr 1
  ext i
  change (positiveIndicator (hH.eigenvalues i) : ℂ) *
    (positiveIndicator (hH.eigenvalues i) : ℂ) = (positiveIndicator (hH.eigenvalues i) : ℂ)
  unfold positiveIndicator
  split_ifs <;> norm_num

def pinchingCost (I : Type*) [Fintype I] (r : ℕ) : ℕ := (r + 1) ^ Fintype.card I

omit [DecidableEq I] in
theorem pinchingCost_pos (r : ℕ) : 0 < (pinchingCost I r : ℝ) := by
  exact_mod_cast (pow_pos (Nat.succ_pos r) (Fintype.card I))

def iidLikelihoodTailTest (ρ : Matrix I I ℂ) {σ : Matrix I I ℂ}
    (hσ : σ.PosSemidef) (r : ℕ) (L : ℝ) :
    Matrix (TensorPinching.RecursiveRows I r) (TensorPinching.RecursiveRows I r) ℂ :=
  spectralUpperTail
    (SpectralPinching.recursiveComparatorPinching hσ r (TensorPinching.recursiveTensorPower ρ r))
    (TensorPinching.recursiveTensorPower σ r) (L / (pinchingCost I r : ℝ))

theorem iidLikelihoodTailTest_isEffect {ρ σ : Matrix I I ℂ}
    (hρ : ρ.PosSemidef) (hσ : σ.PosDef) (r : ℕ) (L : ℝ) :
    FlaggedStates.IsEffect (iidLikelihoodTailTest ρ hσ.posSemidef r L) := by
  have hA := Pinching.pinchingMap_posSemidef
    (TensorPinching.recursiveOccupancyProjections (SpectralPinching.spectralProjections hσ.1) r)
    (recursiveTensorPower_posSemidef hρ r)
  have hB := recursiveTensorPower_posDef hσ r
  exact positiveSpectralTest_isEffect
    (hA.1.sub (hB.1.smul (IsSelfAdjoint.all (L / (pinchingCost I r : ℝ)))))

theorem iidLikelihoodTail_le {ρ σ : Matrix I I ℂ}
    (hρ : ρ.PosSemidef) (hσ : σ.PosDef) (r : ℕ) (L s : ℝ) (hL : 0 < L) (hs : 0 ≤ s) :
    (TensorPinching.recursiveTensorPower ρ r * iidLikelihoodTailTest ρ hσ.posSemidef r L).trace.re ≤
      (pinchingCost I r : ℝ) ^ s * L ^ (-s) * (PetzMoments.petzMoment ρ σ s) ^ r := by
  classical
  let P := TensorPinching.recursiveOccupancyProjections (SpectralPinching.spectralProjections hσ.1) r
  let d : TensorPinching.Occupancy I r → ℂ :=
    TensorPinching.typeWeight (fun i => (hσ.1.eigenvalues i : ℂ))
  have hP : Pinching.IsProjectionFamily P :=
    TensorPinching.recursiveOccupancyProjections_family (SpectralPinching.spectralProjections_family hσ.1) r
  have heσ : TensorPinching.recursiveTensorPower σ r = Pinching.spectralCombination P d :=
    SpectralPinching.recursiveComparatorPower_occupancy_decomposition hσ.posSemidef r
  have hB : (Pinching.spectralCombination P d).PosDef := by
    rw [← heσ]
    exact recursiveTensorPower_posDef hσ r
  have hv := pinchingCost_pos (I := I) r
  have ht := pinchedLikelihoodTail_le hP (recursiveTensorPower_posSemidef hρ r) d hB
    (L / (pinchingCost I r : ℝ)) s (div_pos hL hv) hs
  rw [← heσ, recursiveTensorMoment_power hρ hσ.posSemidef] at ht
  have hf : (L / (pinchingCost I r : ℝ)) ^ (-s) = (pinchingCost I r : ℝ) ^ s * L ^ (-s) := by
    rw [Real.div_rpow hL.le hv.le, Real.rpow_neg hv.le, div_inv_eq_mul, mul_comm]
  rw [hf] at ht
  exact ht

theorem iid_pinching_likelihood_bundle {ρ σ : Matrix I I ℂ}
    (hρ : FlaggedStates.IsDensity ρ) (hσ : σ.PosDef) (r : ℕ) (L s : ℝ)
    (hL : 0 < L) (hs : 0 ≤ s) :
    FlaggedStates.IsDensity (TensorPinching.recursiveTensorPower ρ r) ∧
    (TensorPinching.recursiveTensorPower σ r).PosDef ∧
    PetzMoments.petzMoment (TensorPinching.recursiveTensorPower ρ r)
      (TensorPinching.recursiveTensorPower σ r) s = (PetzMoments.petzMoment ρ σ s) ^ r ∧
    (((pinchingCost I r : ℝ) • SpectralPinching.recursiveComparatorPinching hσ.posSemidef r
      (TensorPinching.recursiveTensorPower ρ r)) - TensorPinching.recursiveTensorPower ρ r).PosSemidef ∧
    FlaggedStates.IsEffect (iidLikelihoodTailTest ρ hσ.posSemidef r L) ∧
    0 ≤ (TensorPinching.recursiveTensorPower ρ r * iidLikelihoodTailTest ρ hσ.posSemidef r L).trace.re ∧
    (TensorPinching.recursiveTensorPower ρ r * iidLikelihoodTailTest ρ hσ.posSemidef r L).trace.re ≤
      (pinchingCost I r : ℝ) ^ s * L ^ (-s) * (PetzMoments.petzMoment ρ σ s) ^ r := by
  have hd := recursiveTensorPower_density hρ r
  have hE := iidLikelihoodTailTest_isEffect hρ.1 hσ r L
  exact ⟨hd, recursiveTensorPower_posDef hσ r,
    recursiveTensorMoment_power hρ.1 hσ.posSemidef r s,
    SpectralPinching.recursiveComparatorPinching_domination hσ.posSemidef r hd.1,
    hE, (FlaggedStates.acceptanceProbability_bounds hd hE).1,
    iidLikelihoodTail_le hρ.1 hσ r L s hL hs⟩

end QuantumProver.SuperchannelDiscrimination.PetzTensorTail

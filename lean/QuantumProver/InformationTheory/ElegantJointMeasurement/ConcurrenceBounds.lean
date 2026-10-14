import Mathlib

open scoped BigOperators ComplexConjugate

namespace QuantumProver.ElegantJointMeasurement.Determinant

section Polynomial

variable {R : Type*} [CommRing R]

def tailMatrix (E : Matrix (Fin 2) (Fin 2) R) (a b : Fin 2 → R)
    (β γ : R) : Matrix (Fin 2) (Fin 2) R :=
  fun i j => γ * E i j - β * a i * b j

def adjugatePair (E : Matrix (Fin 2) (Fin 2) R) (a b : Fin 2 → R) : R :=
  E 1 1 * a 0 * b 0 - E 0 1 * a 1 * b 0 -
    E 1 0 * a 0 * b 1 + E 0 0 * a 1 * b 1

theorem det_tailMatrix (E : Matrix (Fin 2) (Fin 2) R) (a b : Fin 2 → R)
    (β γ : R) :
    Matrix.det (tailMatrix E a b β γ) =
      γ ^ 2 * Matrix.det E - β * γ * adjugatePair E a b := by
  rw [Matrix.det_fin_two, Matrix.det_fin_two]
  simp only [tailMatrix, adjugatePair]
  ring

theorem det_tailMatrix_zero (E : Matrix (Fin 2) (Fin 2) R) (a b : Fin 2 → R)
    (β : R) : Matrix.det (tailMatrix E a b β 0) = 0 := by
  simp [det_tailMatrix]

theorem det_tailMatrix_factor (E : Matrix (Fin 2) (Fin 2) R) (a b : Fin 2 → R)
    (β γ L : R) (hL : Matrix.det E * L = β * adjugatePair E a b) :
    Matrix.det (tailMatrix E a b β γ) = Matrix.det E * γ * (γ - L) := by
  rw [det_tailMatrix]
  calc
    γ ^ 2 * Matrix.det E - β * γ * adjugatePair E a b =
        γ ^ 2 * Matrix.det E - γ * (β * adjugatePair E a b) := by ring
    _ = γ ^ 2 * Matrix.det E - γ * (Matrix.det E * L) := by rw [← hL]
    _ = Matrix.det E * γ * (γ - L) := by ring

end Polynomial

noncomputable section

def branchPhase (γ : ℂ) : ℂ := conj γ / γ

theorem phase_mul_branch (γ d q : ℂ) :
    branchPhase γ * (γ * (d * γ - q)) =
      d * (conj γ * γ) - conj γ * q := by
  by_cases hγ : γ = 0
  · simp [branchPhase, hγ]
  · unfold branchPhase
    field_simp [hγ]

theorem phase_branch_norm (γ d q δ : ℂ) (hδ : δ = γ * (d * γ - q)) :
    ‖branchPhase γ * δ‖ = ‖δ‖ := by
  by_cases hγ : γ = 0
  · simp [hδ, hγ, branchPhase]
  · rw [branchPhase, norm_mul, norm_div, Complex.norm_conj,
      div_self (norm_ne_zero_iff.mpr hγ), one_mul]

variable {ι : Type*}

theorem sum_conj_mul_eq_of_sum_norm_sq_eq (s : Finset ι) (γ : ι → ℂ)
    (hγ : ∑ i ∈ s, ‖γ i‖ ^ 2 = 1) :
    ∑ i ∈ s, conj (γ i) * γ i = 1 := by
  calc
    ∑ i ∈ s, conj (γ i) * γ i = ∑ i ∈ s, ((‖γ i‖ ^ 2 : ℝ) : ℂ) := by
      simp only [Complex.conj_mul', Complex.ofReal_pow]
    _ = ((∑ i ∈ s, ‖γ i‖ ^ 2 : ℝ) : ℂ) := by push_cast; rfl
    _ = 1 := by rw [hγ]; norm_num

theorem phase_sum_identity (s : Finset ι) (γ q δ : ι → ℂ) (d m : ℂ)
    (hnorm : ∑ i ∈ s, conj (γ i) * γ i = 1)
    (hmoment : ∑ i ∈ s, conj (γ i) * q i = d * m)
    (hbranch : ∀ i ∈ s, δ i = γ i * (d * γ i - q i)) :
    ∑ i ∈ s, branchPhase (γ i) * δ i = d * (1 - m) := by
  calc
    ∑ i ∈ s, branchPhase (γ i) * δ i =
        ∑ i ∈ s, (d * (conj (γ i) * γ i) - conj (γ i) * q i) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [hbranch i hi, phase_mul_branch]
    _ = d * (∑ i ∈ s, conj (γ i) * γ i) -
        ∑ i ∈ s, conj (γ i) * q i := by
      rw [Finset.sum_sub_distrib, Finset.mul_sum]
    _ = d * (1 - m) := by rw [hnorm, hmoment]; ring

theorem branch_norm_sum_lower_bound (s : Finset ι) (γ q δ : ι → ℂ) (d m : ℂ)
    (hnorm : ∑ i ∈ s, conj (γ i) * γ i = 1)
    (hmoment : ∑ i ∈ s, conj (γ i) * q i = d * m)
    (hbranch : ∀ i ∈ s, δ i = γ i * (d * γ i - q i)) :
    ‖d‖ * ‖1 - m‖ ≤ ∑ i ∈ s, ‖δ i‖ := by
  calc
    ‖d‖ * ‖1 - m‖ = ‖d * (1 - m)‖ := (norm_mul d (1 - m)).symm
    _ = ‖∑ i ∈ s, branchPhase (γ i) * δ i‖ := by
      rw [phase_sum_identity s γ q δ d m hnorm hmoment hbranch]
    _ ≤ ∑ i ∈ s, ‖branchPhase (γ i) * δ i‖ := norm_sum_le s _
    _ = ∑ i ∈ s, ‖δ i‖ := by
      apply Finset.sum_congr rfl
      intro i hi
      exact phase_branch_norm (γ i) d (q i) (δ i) (hbranch i hi)

theorem determinant_sum_lower_bound (s : Finset ι) (γ L δ : ι → ℂ) (d m : ℂ)
    (hnorm : ∑ i ∈ s, ‖γ i‖ ^ 2 = 1)
    (hmoment : ∑ i ∈ s, conj (γ i) * L i = m)
    (hbranch : ∀ i ∈ s, δ i = d * γ i * (γ i - L i)) :
    ‖d‖ * ‖1 - m‖ ≤ ∑ i ∈ s, ‖δ i‖ := by
  apply branch_norm_sum_lower_bound s γ (fun i => d * L i) δ d m
    (sum_conj_mul_eq_of_sum_norm_sq_eq s γ hnorm)
  · calc
      ∑ i ∈ s, conj (γ i) * (d * L i) =
          ∑ i ∈ s, d * (conj (γ i) * L i) := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = d * m := by rw [← Finset.mul_sum, hmoment]
  · intro i hi
    rw [hbranch i hi]
    ring

theorem determinant_sum_lower_bound_real (s : Finset ι) (γ L δ : ι → ℂ)
    (d : ℂ) (x : ℝ)
    (hnorm : ∑ i ∈ s, ‖γ i‖ ^ 2 = 1)
    (hmoment : ∑ i ∈ s, conj (γ i) * L i = ((2 * x : ℝ) : ℂ))
    (hbranch : ∀ i ∈ s, δ i = d * γ i * (γ i - L i))
    (hd : ‖d‖ = (1 / 4 : ℝ)) :
    (1 / 4 : ℝ) * |1 - 2 * x| ≤ ∑ i ∈ s, ‖δ i‖ := by
  have h := determinant_sum_lower_bound s γ L δ d ((2 * x : ℝ) : ℂ)
    hnorm hmoment hbranch
  have hcast : (1 : ℂ) - ((2 * x : ℝ) : ℂ) = ((1 - 2 * x : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [hd, hcast, Complex.norm_real, Real.norm_eq_abs] at h
  exact h

theorem adjugatePair_sum_moment (s : Finset ι)
    (E : Matrix (Fin 2) (Fin 2) ℂ) (a b : ι → Fin 2 → ℂ) (γ : ι → ℂ) (β : ℂ)
    (hmoment : ∑ i ∈ s, conj (γ i) • Matrix.vecMulVec (a i) (b i) = β • E) :
    ∑ i ∈ s, conj (γ i) * (β * adjugatePair E (a i) (b i)) =
      Matrix.det E * (2 * β ^ 2) := by
  have hentry (u v : Fin 2) :
      ∑ i ∈ s, conj (γ i) * (a i u * b i v) = β * E u v := by
    have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M u v) hmoment
    simpa only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
      Matrix.vecMulVec_apply] using h
  calc
    ∑ i ∈ s, conj (γ i) * (β * adjugatePair E (a i) (b i)) =
        ∑ i ∈ s, (β * E 1 1 * (conj (γ i) * (a i 0 * b i 0)) -
          β * E 0 1 * (conj (γ i) * (a i 1 * b i 0)) -
          β * E 1 0 * (conj (γ i) * (a i 0 * b i 1)) +
          β * E 0 0 * (conj (γ i) * (a i 1 * b i 1))) := by
      apply Finset.sum_congr rfl
      intro i hi
      simp only [adjugatePair]
      ring
    _ = β * E 1 1 * (∑ i ∈ s, conj (γ i) * (a i 0 * b i 0)) -
        β * E 0 1 * (∑ i ∈ s, conj (γ i) * (a i 1 * b i 0)) -
        β * E 1 0 * (∑ i ∈ s, conj (γ i) * (a i 0 * b i 1)) +
        β * E 0 0 * (∑ i ∈ s, conj (γ i) * (a i 1 * b i 1)) := by
      simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum]
    _ = Matrix.det E * (2 * β ^ 2) := by
      rw [hentry 0 0, hentry 1 0, hentry 0 1, hentry 1 1, Matrix.det_fin_two]
      ring

theorem tail_det_sum_lower_bound (s : Finset ι)
    (E : Matrix (Fin 2) (Fin 2) ℂ) (a b : ι → Fin 2 → ℂ) (γ : ι → ℂ) (β : ℂ)
    (hnorm : ∑ i ∈ s, ‖γ i‖ ^ 2 = 1)
    (hmoment : ∑ i ∈ s, conj (γ i) • Matrix.vecMulVec (a i) (b i) = β • E) :
    ‖Matrix.det E‖ * ‖1 - 2 * β ^ 2‖ ≤
      ∑ i ∈ s, ‖Matrix.det (tailMatrix E (a i) (b i) β (γ i))‖ := by
  apply branch_norm_sum_lower_bound s γ
    (fun i => β * adjugatePair E (a i) (b i))
    (fun i => Matrix.det (tailMatrix E (a i) (b i) β (γ i)))
    (Matrix.det E) (2 * β ^ 2)
    (sum_conj_mul_eq_of_sum_norm_sq_eq s γ hnorm)
    (adjugatePair_sum_moment s E a b γ β hmoment)
  intro i hi
  rw [det_tailMatrix]
  ring

theorem tail_det_sum_lower_bound_real (s : Finset ι)
    (E : Matrix (Fin 2) (Fin 2) ℂ) (a b : ι → Fin 2 → ℂ) (γ : ι → ℂ) (β x : ℝ)
    (hnorm : ∑ i ∈ s, ‖γ i‖ ^ 2 = 1)
    (hmoment : ∑ i ∈ s, conj (γ i) • Matrix.vecMulVec (a i) (b i) = (β : ℂ) • E)
    (hβ : β ^ 2 = x) (hdet : ‖Matrix.det E‖ = (1 / 4 : ℝ)) :
    (1 / 4 : ℝ) * |1 - 2 * x| ≤
      ∑ i ∈ s, ‖Matrix.det (tailMatrix E (a i) (b i) (β : ℂ) (γ i))‖ := by
  have h := tail_det_sum_lower_bound s E a b γ (β : ℂ) hnorm hmoment
  have hcast : (1 : ℂ) - 2 * (β : ℂ) ^ 2 = ((1 - 2 * x : ℝ) : ℂ) := by
    rw [← hβ]
    push_cast
    rfl
  rw [hdet, hcast, Complex.norm_real, Real.norm_eq_abs] at h
  exact h

end

end QuantumProver.ElegantJointMeasurement.Determinant

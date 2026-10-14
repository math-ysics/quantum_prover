import QuantumProver.InformationTheory.AmplitudeDamping.SecretKey.OutputContinuity
import QuantumProver.InformationTheory.AmplitudeDamping.SecretKey.ParallelLanes

set_option autoImplicit false

noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix Kronecker

namespace QuantumProver.AmplitudeDamping.SecretKey.LaneFidelity

open OutputContinuity MatrixTraceNorm IndependentLanes

section TwoLanes

variable {E₁ E₂ : Type*} [Fintype E₁] [Fintype E₂]
  [DecidableEq E₁] [DecidableEq E₂]

theorem keyG_tensor_lower (d₁ d₂ : ℕ) (hd₁ : 0 < d₁) (hd₂ : 0 < d₂)
    (ρ₁ : Density ((Fin d₁ × Fin d₁) × E₁))
    (ρ₂ : Density ((Fin d₂ × Fin d₂) × E₂)) :
    optimalWholeKeySquaredFidelity d₁ hd₁ ρ₁ *
      optimalWholeKeySquaredFidelity d₂ hd₂ ρ₂ ≤
        optimalWholeKeySquaredFidelity (d₁ * d₂) (Nat.mul_pos hd₁ hd₂)
          ((ρ₁.tensor ρ₂).relabel (laneKeyEquiv d₁ d₂ E₁ E₂)) := by
  let G₂ := optimalWholeKeySquaredFidelity d₂ hd₂ ρ₂
  let G₁₂ := optimalWholeKeySquaredFidelity (d₁ * d₂) (Nat.mul_pos hd₁ hd₂)
    ((ρ₁.tensor ρ₂).relabel (laneKeyEquiv d₁ d₂ E₁ E₂))
  have hG₂ : 0 ≤ G₂ := (optimalWholeKeySquaredFidelity_mem_Icc d₂ hd₂ ρ₂).1
  have hG₁₂ : 0 ≤ G₁₂ := (optimalWholeKeySquaredFidelity_mem_Icc
    (d₁ * d₂) (Nat.mul_pos hd₁ hd₂) _).1
  have hprod (ξ₁ : Density E₁) (ξ₂ : Density E₂) :
      squaredFidelity ρ₁ (idealKeyStateAgainst d₁ hd₁ ξ₁) *
        squaredFidelity ρ₂ (idealKeyStateAgainst d₂ hd₂ ξ₂) ≤ G₁₂ := by
    rw [← squaredFidelity_lane_candidate d₁ d₂ hd₁ hd₂ ρ₁ ρ₂ ξ₁ ξ₂]
    exact squaredFidelity_candidate_le_keyG (d₁ * d₂) (Nat.mul_pos hd₁ hd₂) _ (ξ₁.tensor ξ₂)
  have hfirst (ξ₁ : Density E₁) :
      squaredFidelity ρ₁ (idealKeyStateAgainst d₁ hd₁ ξ₁) * G₂ ≤ G₁₂ := by
    let f := squaredFidelity ρ₁ (idealKeyStateAgainst d₁ hd₁ ξ₁)
    have hf0 : 0 ≤ f := squaredFidelity_nonneg _ _
    by_cases hf : 0 < f
    · have hg : G₂ ≤ G₁₂ / f := by
        apply csSup_le
        · exact ⟨_, ⟨ρ₂.marginalRight, rfl⟩⟩
        · rintro y ⟨ξ₂, rfl⟩
          apply (le_div_iff₀ hf).mpr
          simpa only [mul_comm] using hprod ξ₁ ξ₂
      have hm := (le_div_iff₀ hf).mp hg
      simpa only [mul_comm] using hm
    · have hz : f = 0 := le_antisymm (le_of_not_gt hf) hf0
      change f * G₂ ≤ G₁₂
      rw [hz, zero_mul]
      exact hG₁₂
  by_cases hpos : 0 < G₂
  · have hg : optimalWholeKeySquaredFidelity d₁ hd₁ ρ₁ ≤ G₁₂ / G₂ := by
      apply csSup_le
      · exact ⟨_, ⟨ρ₁.marginalRight, rfl⟩⟩
      · rintro y ⟨ξ₁, rfl⟩
        exact (le_div_iff₀ hpos).mpr (hfirst ξ₁)
    exact (le_div_iff₀ hpos).mp hg
  · have hz : G₂ = 0 := le_antisymm (le_of_not_gt hpos) hG₂
    change optimalWholeKeySquaredFidelity d₁ hd₁ ρ₁ * G₂ ≤ G₁₂
    rw [hz, mul_zero]
    exact hG₁₂

end TwoLanes

@[reducible] def laneAlphabet (d : ℕ) : ℕ → ℕ
  | 0 => 1
  | n + 1 => d * laneAlphabet d n

theorem laneAlphabet_eq_pow (d n : ℕ) : laneAlphabet d n = d ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [laneAlphabet, ih, pow_succ']

theorem laneAlphabet_pos (d : ℕ) (hd : 0 < d) (n : ℕ) : 0 < laneAlphabet d n := by
  induction n with
  | zero => exact Nat.zero_lt_succ 0
  | succ n ih => exact Nat.mul_pos hd ih

def emptyEve : Density PUnit where
  mat := 1
  positive := Matrix.PosSemidef.one
  normalized := by simp

section ManyLanes

variable {E : Type*} [Fintype E] [DecidableEq E] {d : ℕ}

def keyLaneDensity (ρ : Density ((Fin d × Fin d) × E)) : (n : ℕ) →
    Density ((Fin (laneAlphabet d n) × Fin (laneAlphabet d n)) × Register E n)
  | 0 => idealKeyStateAgainst 1 (by omega) emptyEve
  | n + 1 => (ρ.tensor (keyLaneDensity ρ n)).relabel
      (laneKeyEquiv d (laneAlphabet d n) E (Register E n))

def keyLaneTensorEquiv (d : ℕ) (E : Type*) : (n : ℕ) →
    ((Fin (laneAlphabet d n) × Fin (laneAlphabet d n)) × Register E n) ≃
      Register ((Fin d × Fin d) × E) n
  | 0 =>
      { toFun := fun _ => PUnit.unit
        invFun := fun _ => ((0, 0), PUnit.unit)
        left_inv := fun _ => Subsingleton.elim _ _
        right_inv := fun _ => Subsingleton.elim _ _ }
  | n + 1 => (laneKeyEquiv d (laneAlphabet d n) E (Register E n)).trans
      ((Equiv.refl ((Fin d × Fin d) × E)).prodCongr (keyLaneTensorEquiv d E n))

theorem keyLaneDensity_mat (ρ : Density ((Fin d × Fin d) × E)) (n : ℕ) :
    (keyLaneDensity ρ n).mat = (matrix ρ.mat n).submatrix
      (keyLaneTensorEquiv d E n) (keyLaneTensorEquiv d E n) := by
  induction n with
  | zero =>
      ext x y
      rcases x with ⟨⟨x₁,x₂⟩,xe⟩
      rcases y with ⟨⟨y₁,y₂⟩,ye⟩
      have hx₁ : x₁ = 0 := Subsingleton.elim _ _
      have hx₂ : x₂ = 0 := Subsingleton.elim _ _
      have hy₁ : y₁ = 0 := Subsingleton.elim _ _
      have hy₂ : y₂ = 0 := Subsingleton.elim _ _
      subst x₁; subst x₂; subst y₁; subst y₂
      cases xe; cases ye
      simp [keyLaneDensity, emptyEve, idealKeyStateAgainst, uniformKeyLaw,
        ProbabilityLaw.copiedDensity, ProbabilityLaw.copiedMatrix, Density.tensor,
        Matrix.kroneckerMap_apply, matrix, keyLaneTensorEquiv, Matrix.one_apply]
  | succ n ih =>
      change (ρ.mat ⊗ₖ (keyLaneDensity ρ n).mat).submatrix _ _ = _
      rw [ih]
      ext x y
      rfl

theorem keyG_pow_le_keyLaneDensity (ρ : Density ((Fin d × Fin d) × E))
    (hd : 0 < d) (n : ℕ) :
    optimalWholeKeySquaredFidelity d hd ρ ^ n ≤
      optimalWholeKeySquaredFidelity (laneAlphabet d n) (laneAlphabet_pos d hd n)
        (keyLaneDensity ρ n) := by
  induction n with
  | zero =>
      have h := squaredFidelity_candidate_le_keyG 1 (by omega)
        (keyLaneDensity ρ 0) emptyEve
      change squaredFidelity (idealKeyStateAgainst 1 _ emptyEve)
        (idealKeyStateAgainst 1 _ emptyEve) ≤ _ at h
      rw [squaredFidelity_self] at h
      simpa only [pow_zero, laneAlphabet] using h
  | succ n ih =>
      have hprod := keyG_tensor_lower d (laneAlphabet d n) hd (laneAlphabet_pos d hd n)
        ρ (keyLaneDensity ρ n)
      have hG := (optimalWholeKeySquaredFidelity_mem_Icc d hd ρ).1
      calc
        _ = optimalWholeKeySquaredFidelity d hd ρ *
          optimalWholeKeySquaredFidelity d hd ρ ^ n := pow_succ' _ _
        _ ≤ optimalWholeKeySquaredFidelity d hd ρ *
          optimalWholeKeySquaredFidelity (laneAlphabet d n) (laneAlphabet_pos d hd n)
            (keyLaneDensity ρ n) := mul_le_mul_of_nonneg_left ih hG
        _ ≤ _ := hprod

end ManyLanes

end QuantumProver.AmplitudeDamping.SecretKey.LaneFidelity

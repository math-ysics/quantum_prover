import QuantumProver.InformationTheory.SuperchannelDiscrimination.FlaggedStates
import QuantumProver.InformationTheory.IsotropicFormation.ProductEnsembles

set_option autoImplicit false

noncomputable section

open Matrix
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace QuantumProver.ConditionalEntropy.ConditionalRange

open QuantumProver.SuperchannelDiscrimination.FlaggedStates

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem trace_cfc_re_eq_sum (f : ℝ → ℝ) {X : Matrix I I ℂ}
    (hX : X.IsHermitian) :
    (cfc f X).trace.re = ∑ i, f (hX.eigenvalues i) := by
  rw [hX.cfc_eq f, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply,
    Matrix.trace_mul_cycle]
  have hU : (hX.eigenvectorUnitary : Matrix I I ℂ)ᴴ *
      (hX.eigenvectorUnitary : Matrix I I ℂ) = 1 :=
    Unitary.coe_star_mul_self hX.eigenvectorUnitary
  rw [Matrix.star_eq_conjTranspose, hU, Matrix.one_mul, Matrix.trace_diagonal]
  simp [Complex.re_sum, Function.comp_def]

theorem trace_re_eq_sum_eigenvalues {X : Matrix I I ℂ} (hX : X.IsHermitian) :
    X.trace.re = ∑ i, hX.eigenvalues i := by
  rw [hX.trace_eq_sum_eigenvalues]
  simp [Complex.re_sum]

theorem entropyBits_eq_spectral {X : Matrix I I ℂ} (hX : X.IsHermitian) :
    entropyBits X = -(∑ i, hX.eigenvalues i * Real.log (hX.eigenvalues i)) /
      Real.log 2 := by
  rw [entropyBits, trace_cfc_re_eq_sum _ hX]

theorem mulLog_tangent {x y : ℝ} (hx : 0 ≤ x) (hy : 0 < y) :
    x-y ≤ x * Real.log x - x * Real.log y := by
  by_cases hx0 : x = 0
  · simp [hx0, hy.le]
  have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
  have hl := mul_le_mul_of_nonneg_left
    (Real.log_le_sub_one_of_pos (div_pos hy hxpos)) hx
  have hid : x * (y/x-1) = y-x := by field_simp [hxpos.ne'] <;> ring
  rw [Real.log_div hy.ne' hxpos.ne', hid] at hl
  nlinarith

theorem scalar_entropy_bounds (x : I → ℝ) (hx : ∀ i, 0 ≤ x i)
    (hsum : ∑ i, x i = 1) :
    0 ≤ -(∑ i, x i * Real.log (x i)) ∧
      -(∑ i, x i * Real.log (x i)) ≤ Real.log (Fintype.card I) := by
  have hn : 0 < Fintype.card I := by
    by_contra h
    have hz : Fintype.card I = 0 := Nat.eq_zero_of_not_pos h
    letI : IsEmpty I := Fintype.card_eq_zero_iff.mp hz
    simp at hsum
  have hnR : 0 < (Fintype.card I : ℝ) := by exact_mod_cast hn
  have hx1 (i : I) : x i ≤ 1 := by
    rw [← hsum]
    exact Finset.single_le_sum (fun j _ => hx j) (Finset.mem_univ i)
  constructor
  · apply neg_nonneg.mpr
    exact Finset.sum_nonpos fun i _ => Real.mul_log_nonpos (hx i) (hx1 i)
  · have ht := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) =>
      mulLog_tangent (hx i) (inv_pos.mpr hnR)
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, hsum, ← Finset.sum_mul] at ht
    rw [mul_inv_cancel₀ hnR.ne', one_mul, Real.log_inv] at ht
    linarith

theorem isDensity_card_pos {X : Matrix I I ℂ} (hX : IsDensity X) :
    0 < Fintype.card I := by
  by_contra h
  have hz : Fintype.card I = 0 := Nat.eq_zero_of_not_pos h
  letI : IsEmpty I := Fintype.card_eq_zero_iff.mp hz
  have ht := hX.2
  simp [Matrix.trace] at ht

theorem entropyBits_bounds {X : Matrix I I ℂ} (hX : IsDensity X) :
    0 ≤ entropyBits X ∧
      entropyBits X ≤ Real.log (Fintype.card I) / Real.log 2 := by
  have hsum : ∑ i, hX.1.1.eigenvalues i = 1 := by
    rw [← trace_re_eq_sum_eigenvalues hX.1.1, hX.2]
    rfl
  have hb := scalar_entropy_bounds hX.1.1.eigenvalues hX.1.eigenvalues_nonneg hsum
  rw [entropyBits_eq_spectral hX.1.1]
  exact ⟨div_nonneg hb.1 (le_of_lt (Real.log_pos (by norm_num))),
    div_le_div_of_nonneg_right hb.2 (le_of_lt (Real.log_pos (by norm_num)))⟩

theorem entropyBits_eq_isotropicEntropy_div_log_two (X : Matrix I I ℂ) :
    entropyBits X = QuantumProver.IsotropicFormation.vonNeumannEntropyNat X /
      Real.log 2 := by
  rw [QuantumProver.IsotropicFormation.vonNeumannEntropyNat,
    Real.negMulLog_eq_neg, cfc_neg, Matrix.trace_neg, Complex.neg_re]
  rfl

theorem entropyBits_squareGram (M : Matrix I I ℂ) :
    entropyBits (Mᴴ * M) = entropyBits (M * Mᴴ) := by
  rw [entropyBits_eq_isotropicEntropy_div_log_two,
    entropyBits_eq_isotropicEntropy_div_log_two,
    QuantumProver.IsotropicFormation.vonNeumannEntropyNat_gram M]

theorem entropyBits_transpose {X : Matrix I I ℂ} (hX : X.IsHermitian) :
    entropyBits Xᵀ = entropyBits X := by
  rw [entropyBits_eq_isotropicEntropy_div_log_two,
    entropyBits_eq_isotropicEntropy_div_log_two]
  exact congrArg (fun t : ℝ => t / Real.log 2)
    (QuantumProver.IsotropicFormation.vonNeumannEntropyNat_eq_of_charpoly_eq
      Xᵀ X hX.transpose hX (Matrix.charpoly_transpose X))

variable {J : Type*} [Fintype J] [DecidableEq J]

def squarePadding (M : Matrix I J ℂ) : Matrix (I ⊕ J) (I ⊕ J) ℂ :=
  Matrix.fromBlocks 0 M 0 0

theorem squarePadding_leftGram (M : Matrix I J ℂ) :
    (squarePadding M)ᴴ * squarePadding M =
      flagBlock (0 : Matrix I I ℂ) (Mᴴ * M) := by
  simp [squarePadding, flagBlock, Matrix.fromBlocks_conjTranspose,
    Matrix.fromBlocks_multiply]

theorem squarePadding_rightGram (M : Matrix I J ℂ) :
    squarePadding M * (squarePadding M)ᴴ =
      flagBlock (M * Mᴴ) (0 : Matrix J J ℂ) := by
  simp [squarePadding, flagBlock, Matrix.fromBlocks_conjTranspose,
    Matrix.fromBlocks_multiply]

theorem entropyBits_rectangularGram (M : Matrix I J ℂ) :
    entropyBits (Mᴴ * M) = entropyBits (M * Mᴴ) := by
  have hh := entropyBits_squareGram (squarePadding M)
  rw [squarePadding_leftGram, squarePadding_rightGram,
    entropyBits_flagBlock Matrix.PosSemidef.zero (Matrix.posSemidef_conjTranspose_mul_self M),
    entropyBits_flagBlock (Matrix.posSemidef_self_mul_conjTranspose M) Matrix.PosSemidef.zero]
    at hh
  have hzI : entropyBits (0 : Matrix I I ℂ) = 0 := by simp [entropyBits]
  have hzJ : entropyBits (0 : Matrix J J ℂ) = 0 := by simp [entropyBits]
  simpa only [hzI, hzJ, zero_add, add_zero] using hh

variable {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
  [DecidableEq A] [DecidableEq B] [DecidableEq C]

def complementaryCoeff (V : Matrix (A × B) C ℂ) : Matrix (A × C) B ℂ :=
  fun ac b => V (ac.1,b) ac.2

def complementaryState (V : Matrix (A × B) C ℂ) :
    Matrix (A × C) (A × C) ℂ :=
  complementaryCoeff V * (complementaryCoeff V)ᴴ

theorem complementaryState_posSemidef (V : Matrix (A × B) C ℂ) :
    (complementaryState V).PosSemidef :=
  Matrix.posSemidef_self_mul_conjTranspose _

theorem complementaryState_trace (V : Matrix (A × B) C ℂ) :
    (complementaryState V).trace = (V * Vᴴ).trace := by
  simp only [Matrix.trace, Matrix.diag, complementaryState, complementaryCoeff,
    Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  exact Finset.sum_comm

theorem complementaryState_isDensity (V : Matrix (A × B) C ℂ)
    (htrace : (V * Vᴴ).trace = 1) : IsDensity (complementaryState V) :=
  ⟨complementaryState_posSemidef V, (complementaryState_trace V).trans htrace⟩

theorem complementaryCoeff_oppositeGram (V : Matrix (A × B) C ℂ) :
    (complementaryCoeff V)ᴴ * complementaryCoeff V =
      (fun b b' => ∑ a, (V * Vᴴ) (a,b) (a,b'))ᵀ := by
  ext b b'
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, complementaryCoeff,
    Matrix.transpose_apply, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro c _
  ring

theorem complementaryState_marginalA (V : Matrix (A × B) C ℂ) :
    (fun a a' => ∑ c, complementaryState V (a,c) (a',c)) =
      (fun a a' => ∑ b, (V * Vᴴ) (a,b) (a',b)) := by
  ext a a'
  simp only [complementaryState, complementaryCoeff, Matrix.mul_apply,
    Matrix.conjTranspose_apply]
  exact Finset.sum_comm

theorem complementaryState_marginalC (V : Matrix (A × B) C ℂ) :
    (fun c c' => ∑ a, complementaryState V (a,c) (a,c')) = (Vᴴ * V)ᵀ := by
  ext c c'
  simp only [complementaryState, complementaryCoeff, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.transpose_apply, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem entropyBits_complementaryState (V : Matrix (A × B) C ℂ)
    (hB : Matrix.IsHermitian
      ((fun b b' => ∑ a, (V * Vᴴ) (a,b) (a,b')) : Matrix B B ℂ)) :
    entropyBits (complementaryState V) =
      entropyBits (fun b b' => ∑ a, (V * Vᴴ) (a,b) (a,b')) := by
  rw [complementaryState, ← entropyBits_rectangularGram,
    complementaryCoeff_oppositeGram, entropyBits_transpose hB]

theorem sqrt_grams {R : Matrix I I ℂ} (hR : R.PosSemidef) :
    CFC.sqrt R * (CFC.sqrt R)ᴴ = R ∧ (CFC.sqrt R)ᴴ * CFC.sqrt R = R := by
  have hV : (CFC.sqrt R)ᴴ = CFC.sqrt R := (CFC.sqrt_nonneg R).posSemidef.1
  rw [hV]
  have hs : CFC.sqrt R * CFC.sqrt R = R := CFC.sqrt_mul_sqrt_self R hR.nonneg
  exact ⟨hs, hs⟩

theorem complementaryState_sqrt_isDensity {R : Matrix (A × B) (A × B) ℂ}
    (hR : IsDensity R) : IsDensity (complementaryState (CFC.sqrt R)) := by
  apply complementaryState_isDensity
  rw [(sqrt_grams hR.1).1, hR.2]

theorem complementaryState_sqrt_marginalA {R : Matrix (A × B) (A × B) ℂ}
    (hR : R.PosSemidef) :
    (fun a a' => ∑ c, complementaryState (CFC.sqrt R) (a,c) (a',c)) =
      (fun a a' => ∑ b, R (a,b) (a',b)) := by
  rw [complementaryState_marginalA, (sqrt_grams hR).1]

theorem complementaryState_sqrt_marginalC {R : Matrix (A × B) (A × B) ℂ}
    (hR : R.PosSemidef) :
    (fun c c' => ∑ a, complementaryState (CFC.sqrt R) (a,c) (a,c')) = Rᵀ := by
  rw [complementaryState_marginalC, (sqrt_grams hR).2]

end QuantumProver.ConditionalEntropy.ConditionalRange

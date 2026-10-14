import Mathlib
import QuantumProver.InformationTheory.BellDiagonalSquashedEntanglement.ScalarEntropyBounds
import QuantumProver.InformationTheory.BellDiagonalSquashedEntanglement.Definitions
import QuantumProver.InformationTheory.BellDiagonalSquashedEntanglement.ScalarOptimization
import QuantumProver.LinearAlgebra.Affinity
import QuantumProver.InformationTheory.ConditionalEntropy.ConditionalRange
import QuantumProver.InformationTheory.DepolarizingPrivateInformation.PrivateInformationInequalities
import QuantumProver.LinearAlgebra.TwoColumnEntropy

noncomputable section

open scoped BigOperators ComplexOrder MatrixOrder Matrix Matrix.Norms.L2Operator

namespace QuantumProver.BellDiagonalSquashedEntanglement.FCColumns

variable {I : Type*} [Fintype I] [DecidableEq I]

def flagAmplitude (A : Matrix I I ℂ) : Matrix (I × I) I ℂ :=
  fun x j => if x.2 = j then A x.1 j else 0

def flagGram (A : Matrix I I ℂ) : Matrix (I × I) (I × I) ℂ :=
  flagAmplitude A * (flagAmplitude A)ᴴ

theorem flagGram_posSemidef (A : Matrix I I ℂ) :
    (flagGram A).PosSemidef :=
  Matrix.posSemidef_self_mul_conjTranspose (flagAmplitude A)

theorem flagGram_apply (A : Matrix I I ℂ) (i j k l : I) :
    flagGram A (i, j) (k, l) =
      if j = l then A i j * star (A k j) else 0 := by
  classical
  unfold flagGram
  rw [Matrix.mul_apply]
  simp only [Matrix.conjTranspose_apply]
  by_cases h : j = l
  · subst l
    rw [if_pos rfl]
    calc
      (∑ t : I, flagAmplitude A (i, j) t * star (flagAmplitude A (k, j) t)) =
          ∑ t : I, if t = j then A i j * star (A k j) else 0 := by
        apply Finset.sum_congr rfl
        intro t ht
        by_cases h' : t = j
        · subst t
          simp [flagAmplitude]
        · simp [flagAmplitude, h', Ne.symm h']
      _ = A i j * star (A k j) := by simp
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro t ht
    by_cases h' : j = t
    · subst t
      simp [flagAmplitude, h, Ne.symm h]
    · simp [flagAmplitude, h']

theorem discard_flagGram (A : Matrix I I ℂ) :
    (fun i k => ∑ j : I, flagGram A (i, j) (k, j)) = A * Aᴴ := by
  ext i k
  simp [flagGram_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]

theorem flagGram_trace (A : Matrix I I ℂ) :
    (flagGram A).trace = (A * Aᴴ).trace := by
  simp [Matrix.trace, Fintype.sum_prod_type, flagGram_apply,
    Matrix.mul_apply, Matrix.conjTranspose_apply]

theorem flagGram_density (A : Matrix I I ℂ) (htrace : (A * Aᴴ).trace = 1) :
    (flagGram A).PosSemidef ∧ (flagGram A).trace = 1 :=
  ⟨flagGram_posSemidef A, (flagGram_trace A).trans htrace⟩

theorem sqrtPSD_columnGram {A : Mat I} (hA : A.PosSemidef) :
    sqrtPSD A * (sqrtPSD A)ᴴ = A := by
  have hsqrt : (CFC.sqrt A).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)
  have hstar : (CFC.sqrt A)ᴴ = CFC.sqrt A := hsqrt.isHermitian.eq
  simp only [sqrtPSD, hstar, ← pow_two]
  exact CFC.sq_sqrt A hA.nonneg

theorem basis_columnGram {A : Mat I} (hA : A.PosSemidef)
    (U : Mat I) (hU : U * Uᴴ = 1) :
    (sqrtPSD A * U) * (sqrtPSD A * U)ᴴ = A := by
  calc
    (sqrtPSD A * U) * (sqrtPSD A * U)ᴴ =
        sqrtPSD A * (U * Uᴴ) * (sqrtPSD A)ᴴ := by
      rw [Matrix.conjTranspose_mul]
      noncomm_ring
    _ = sqrtPSD A * (sqrtPSD A)ᴴ := by rw [hU, mul_one]
    _ = A := sqrtPSD_columnGram hA

def flagStateInBasis (ρ : Density I) (U : Mat I) (hU : U * Uᴴ = 1) :
    Density (I × I) :=
  ⟨flagGram (sqrtPSD ρ.val * U), flagGram_density _ (by
    rw [basis_columnGram ρ.property.1 U hU]
    exact ρ.property.2)⟩

theorem flagStateInBasis_discard (ρ : Density I) (U : Mat I)
    (hU : U * Uᴴ = 1) :
    partialTraceRight (flagStateInBasis ρ U hU).val = ρ.val := by
  change partialTraceRight (flagGram (sqrtPSD ρ.val * U)) = ρ.val
  calc
    partialTraceRight (flagGram (sqrtPSD ρ.val * U)) =
        (sqrtPSD ρ.val * U) * (sqrtPSD ρ.val * U)ᴴ :=
      discard_flagGram _
    _ = ρ.val := basis_columnGram ρ.property.1 U hU

theorem flagStateInBasis_channel (ρ : Density I) (U : Mat I)
    (hU : U * Uᴴ = 1) :
    (partialTraceRightChannel (I := I) (E := I)).map
      (flagStateInBasis ρ U hU).val = ρ.val :=
  flagStateInBasis_discard ρ U hU

theorem actual_flag_additive_cost (ρ₀ ρ₁ : Density I) (U : Mat I)
    (hU : U * Uᴴ = 1) :
    pairCost ρ₀.val ρ₁.val =
      pairCost (flagStateInBasis ρ₀ U hU).val (flagStateInBasis ρ₁ U hU).val +
        (binaryHolevo (flagStateInBasis ρ₀ U hU).val (flagStateInBasis ρ₁ U hU).val -
          binaryHolevo ρ₀.val ρ₁.val) := by
  unfold pairCost
  ring

def columnNormSq (A : Matrix I I ℂ) (j : I) : ℝ :=
  ∑ i : I, Complex.normSq (A i j)

theorem columnNormSq_nonneg (A : Matrix I I ℂ) (j : I) :
    0 ≤ columnNormSq A j := by
  apply Finset.sum_nonneg
  intro i hi
  exact Complex.normSq_nonneg _

def columnOverlap (A B : Mat I) (j : I) : ℂ :=
  ∑ i : I, star (A i j) * B i j

def columnVector (A : Mat I) (j : I) : EuclideanSpace ℂ I :=
  WithLp.toLp 2 (fun i => A i j)

theorem columnVector_norm_sq (A : Mat I) (j : I) :
    ‖columnVector A j‖ ^ 2 = columnNormSq A j := by
  simpa [columnVector, columnNormSq, Complex.normSq_eq_norm_sq] using
    EuclideanSpace.norm_sq_eq (columnVector A j)

theorem columnOverlap_eq_inner (A B : Mat I) (j : I) :
    columnOverlap A B j = inner ℂ (columnVector A j) (columnVector B j) := by
  simp [columnOverlap, columnVector, EuclideanSpace.inner_toLp_toLp,
    dotProduct, mul_comm]

theorem columnOverlap_normSq_le (A B : Mat I) (j : I) :
    Complex.normSq (columnOverlap A B j) ≤
      columnNormSq A j * columnNormSq B j := by
  rw [Complex.normSq_eq_norm_sq, columnOverlap_eq_inner]
  have hcs := norm_inner_le_norm (𝕜 := ℂ) (columnVector A j) (columnVector B j)
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hcs 2
  simpa only [mul_pow, columnVector_norm_sq] using hsq

theorem columnOverlap_zero_of_left_zero (A B : Mat I) (j : I)
    (hp : columnNormSq A j = 0) : columnOverlap A B j = 0 := by
  have h := columnOverlap_normSq_le A B j
  rw [hp, zero_mul] at h
  exact Complex.normSq_eq_zero.mp (le_antisymm h (Complex.normSq_nonneg _))

theorem columnOverlap_zero_of_right_zero (A B : Mat I) (j : I)
    (hq : columnNormSq B j = 0) : columnOverlap A B j = 0 := by
  have h := columnOverlap_normSq_le A B j
  rw [hq, mul_zero] at h
  exact Complex.normSq_eq_zero.mp (le_antisymm h (Complex.normSq_nonneg _))

theorem sum_columnOverlap (A B : Mat I) :
    (∑ j : I, columnOverlap A B j) = (Aᴴ * B).trace := by
  simp [columnOverlap, Matrix.trace, Matrix.mul_apply, Matrix.conjTranspose_apply]

theorem sum_columnNormSq (A : Mat I) :
    (∑ j : I, columnNormSq A j) = (Aᴴ * A).trace.re := by
  simp only [columnNormSq, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro i hi
  rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self]
  rfl

theorem basis_columnNormSq_sum (ρ : Density I) (U : Mat I)
    (hU : U * Uᴴ = 1) :
    (∑ j : I, columnNormSq (sqrtPSD ρ.val * U) j) = 1 := by
  rw [sum_columnNormSq, Matrix.trace_mul_comm,
    basis_columnGram ρ.property.1 U hU, ρ.property.2]
  rfl

theorem sum_basis_columnOverlap (ρ₀ ρ₁ : Density I) (U : Mat I)
    (hU : U * Uᴴ = 1) :
    (∑ j : I, columnOverlap (sqrtPSD ρ₀.val * U) (sqrtPSD ρ₁.val * U) j) =
      (sqrtPSD ρ₀.val * sqrtPSD ρ₁.val).trace := by
  rw [sum_columnOverlap]
  have hsqrt : (sqrtPSD ρ₀.val).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg ρ₀.val)
  have hstar : (sqrtPSD ρ₀.val)ᴴ = sqrtPSD ρ₀.val := hsqrt.isHermitian.eq
  calc
    ((sqrtPSD ρ₀.val * U)ᴴ * (sqrtPSD ρ₁.val * U)).trace =
        ((Uᴴ * (sqrtPSD ρ₀.val * sqrtPSD ρ₁.val)) * U).trace := by
      rw [Matrix.conjTranspose_mul, hstar]
      congr 1
      noncomm_ring
    _ = ((U * Uᴴ) * (sqrtPSD ρ₀.val * sqrtPSD ρ₁.val)).trace := by
      exact Matrix.trace_mul_cycle Uᴴ (sqrtPSD ρ₀.val * sqrtPSD ρ₁.val) U
    _ = (sqrtPSD ρ₀.val * sqrtPSD ρ₁.val).trace := by rw [hU, one_mul]

theorem basis_columnOverlap_real_sum (ρ₀ ρ₁ : Density I) (U : Mat I)
    (hU : U * Uᴴ = 1) :
    (∑ j : I, (columnOverlap (sqrtPSD ρ₀.val * U)
      (sqrtPSD ρ₁.val * U) j).re) = affinity ρ₀.val ρ₁.val := by
  rw [← Complex.re_sum, sum_basis_columnOverlap ρ₀ ρ₁ U hU]
  rfl

def columnMass (A B : Mat I) (j : I) : ℝ :=
  (columnNormSq A j + columnNormSq B j) / 2

def columnRoot (A B : Mat I) (j : I) : ℝ :=
  Real.sqrt (columnNormSq A j * columnNormSq B j)

def columnBeta (A B : Mat I) (j : I) : ℝ :=
  2 * columnRoot A B j / (columnNormSq A j + columnNormSq B j)

def normalizedColumnOverlap (A B : Mat I) (j : I) : ℂ :=
  columnOverlap A B j / (columnRoot A B j : ℂ)

theorem columnMass_nonneg (A B : Mat I) (j : I) : 0 ≤ columnMass A B j := by
  exact div_nonneg (add_nonneg (columnNormSq_nonneg A j)
    (columnNormSq_nonneg B j)) (by norm_num)

theorem columnRoot_sq (A B : Mat I) (j : I) :
    columnRoot A B j ^ 2 = columnNormSq A j * columnNormSq B j :=
  Real.sq_sqrt (mul_nonneg (columnNormSq_nonneg A j) (columnNormSq_nonneg B j))

theorem columnRoot_nonneg (A B : Mat I) (j : I) : 0 ≤ columnRoot A B j :=
  Real.sqrt_nonneg _

theorem columnBeta_nonneg (A B : Mat I) (j : I) : 0 ≤ columnBeta A B j := by
  exact div_nonneg (mul_nonneg (by norm_num) (columnRoot_nonneg A B j))
    (add_nonneg (columnNormSq_nonneg A j) (columnNormSq_nonneg B j))

theorem columnBeta_le_one (A B : Mat I) (j : I) : columnBeta A B j ≤ 1 := by
  have hp := columnNormSq_nonneg A j
  have hq := columnNormSq_nonneg B j
  have hr := columnRoot_nonneg A B j
  have hsq := columnRoot_sq A B j
  have hbound : 2 * columnRoot A B j ≤ columnNormSq A j + columnNormSq B j :=
    by nlinarith [sq_nonneg (columnNormSq A j - columnNormSq B j)]
  by_cases hzero : columnNormSq A j + columnNormSq B j = 0
  · simp [columnBeta, hzero]
  · unfold columnBeta
    apply (div_le_iff₀ (lt_of_le_of_ne (add_nonneg hp hq) (Ne.symm hzero))).mpr
    simpa using hbound

theorem columnMass_mul_beta (A B : Mat I) (j : I) :
    columnMass A B j * columnBeta A B j = columnRoot A B j := by
  have hp := columnNormSq_nonneg A j
  have hq := columnNormSq_nonneg B j
  by_cases hzero : columnNormSq A j + columnNormSq B j = 0
  · have hp0 : columnNormSq A j = 0 := by linarith
    simp [columnMass, columnBeta, columnRoot, hzero, hp0]
  · unfold columnMass columnBeta
    field_simp [hzero]

theorem root_mul_normalizedColumnOverlap (A B : Mat I) (j : I) :
    (columnRoot A B j : ℂ) * normalizedColumnOverlap A B j =
      columnOverlap A B j := by
  by_cases hroot : columnRoot A B j = 0
  · have hcs := columnOverlap_normSq_le A B j
    have hs := columnRoot_sq A B j
    rw [hroot, zero_pow (by norm_num)] at hs
    have ho : columnOverlap A B j = 0 :=
      Complex.normSq_eq_zero.mp (by
        have hn := Complex.normSq_nonneg (columnOverlap A B j)
        nlinarith)
    simp [normalizedColumnOverlap, hroot, ho]
  · unfold normalizedColumnOverlap
    have hz : (columnRoot A B j : ℂ) ≠ 0 := by exact_mod_cast hroot
    field_simp [hz]

theorem normalizedColumnOverlap_norm_le_one (A B : Mat I) (j : I) :
    ‖normalizedColumnOverlap A B j‖ ≤ 1 := by
  by_cases hroot : columnRoot A B j = 0
  · simp [normalizedColumnOverlap, hroot]
  · have hcs := columnOverlap_normSq_le A B j
    have hs := columnRoot_sq A B j
    have hpos : 0 < columnRoot A B j :=
      lt_of_le_of_ne (columnRoot_nonneg A B j) (Ne.symm hroot)
    have hsq : Complex.normSq (normalizedColumnOverlap A B j) ≤ 1 := by
      unfold normalizedColumnOverlap
      rw [Complex.normSq_div, Complex.normSq_ofReal]
      apply (div_le_iff₀ (mul_pos hpos hpos)).mpr
      nlinarith
    rw [Complex.normSq_eq_norm_sq] at hsq
    nlinarith [norm_nonneg (normalizedColumnOverlap A B j)]

theorem column_complex_moment (A B : Mat I) (j : I) :
    ((columnMass A B j * columnBeta A B j : ℝ) : ℂ) *
        normalizedColumnOverlap A B j = columnOverlap A B j := by
  rw [columnMass_mul_beta]
  exact root_mul_normalizedColumnOverlap A B j

theorem basis_columnMass_sum (ρ₀ ρ₁ : Density I) (U : Mat I)
    (hU : U * Uᴴ = 1) :
    (∑ j : I, columnMass (sqrtPSD ρ₀.val * U) (sqrtPSD ρ₁.val * U) j) = 1 := by
  simp only [columnMass]
  rw [← Finset.sum_div, Finset.sum_add_distrib,
    basis_columnNormSq_sum ρ₀ U hU, basis_columnNormSq_sum ρ₁ U hU]
  norm_num

theorem basis_signed_affinity_moment (ρ₀ ρ₁ : Density I) (U : Mat I)
    (hU : U * Uᴴ = 1) :
    (∑ j : I, columnMass (sqrtPSD ρ₀.val * U) (sqrtPSD ρ₁.val * U) j *
        (columnBeta (sqrtPSD ρ₀.val * U) (sqrtPSD ρ₁.val * U) j *
          (normalizedColumnOverlap (sqrtPSD ρ₀.val * U)
            (sqrtPSD ρ₁.val * U) j).re)) = affinity ρ₀.val ρ₁.val := by
  rw [← basis_columnOverlap_real_sum ρ₀ ρ₁ U hU]
  apply Finset.sum_congr rfl
  intro j hj
  have h := congrArg Complex.re (column_complex_moment
    (sqrtPSD ρ₀.val * U) (sqrtPSD ρ₁.val * U) j)
  simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, mul_assoc] using h

def fidelityTransport (ρ₀ ρ₁ : Density I) : Mat I :=
  (sqrtPSD ρ₀.val)⁻¹ *
    sqrtPSD (sqrtPSD ρ₀.val * ρ₁.val * sqrtPSD ρ₀.val) *
      (sqrtPSD ρ₀.val)⁻¹

theorem sqrtPSD_isUnit (ρ : Density I) (hρ : ρ.val.PosDef) :
    IsUnit (sqrtPSD ρ.val) := by
  have hs : sqrtPSD ρ.val ^ 2 = ρ.val := CFC.sq_sqrt ρ.val ρ.property.1.nonneg
  have hpow : IsUnit (sqrtPSD ρ.val ^ 2) := hs.symm ▸ hρ.isUnit
  exact (isUnit_pow_iff (by norm_num : (2 : ℕ) ≠ 0)).mp hpow

theorem fidelityTransport_posSemidef (ρ₀ ρ₁ : Density I) :
    (fidelityTransport ρ₀ ρ₁).PosSemidef := by
  have hroot : (sqrtPSD ρ₀.val).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg ρ₀.val)
  have hinv : ((sqrtPSD ρ₀.val)⁻¹).PosSemidef := hroot.inv
  have hmiddle :
      (sqrtPSD (sqrtPSD ρ₀.val * ρ₁.val * sqrtPSD ρ₀.val)).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg _)
  have h := hmiddle.conjTranspose_mul_mul_same ((sqrtPSD ρ₀.val)⁻¹)
  rw [hinv.isHermitian.eq] at h
  exact h

theorem fidelityTransport_identity (ρ₀ ρ₁ : Density I) (hρ₀ : ρ₀.val.PosDef) :
    fidelityTransport ρ₀ ρ₁ * ρ₀.val * fidelityTransport ρ₀ ρ₁ = ρ₁.val := by
  let R := sqrtPSD ρ₀.val
  let M := sqrtPSD (R * ρ₁.val * R)
  have hR : R.PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg ρ₀.val)
  have hinner : (R * ρ₁.val * R).PosSemidef := by
    have h := ρ₁.property.1.conjTranspose_mul_mul_same R
    rw [hR.isHermitian.eq] at h
    exact h
  have hR2 : R * R = ρ₀.val := by
    change CFC.sqrt ρ₀.val * CFC.sqrt ρ₀.val = ρ₀.val
    rw [← pow_two]
    exact CFC.sq_sqrt ρ₀.val ρ₀.property.1.nonneg
  have hM2 : M * M = R * ρ₁.val * R := by
    change CFC.sqrt (R * ρ₁.val * R) * CFC.sqrt (R * ρ₁.val * R) = _
    rw [← pow_two]
    exact CFC.sq_sqrt _ hinner.nonneg
  have hdet : IsUnit R.det :=
    (Matrix.isUnit_iff_isUnit_det R).mp (sqrtPSD_isUnit ρ₀ hρ₀)
  have hleft : R⁻¹ * R = 1 := Matrix.nonsing_inv_mul R hdet
  have hright : R * R⁻¹ = 1 := Matrix.mul_nonsing_inv R hdet
  change (R⁻¹ * M * R⁻¹) * ρ₀.val * (R⁻¹ * M * R⁻¹) = ρ₁.val
  rw [← hR2]
  calc
    (R⁻¹ * M * R⁻¹) * (R * R) * (R⁻¹ * M * R⁻¹) =
        R⁻¹ * M * ((R⁻¹ * R) * (R * R⁻¹)) * M * R⁻¹ := by noncomm_ring
    _ = R⁻¹ * (M * M) * R⁻¹ := by rw [hleft, hright]; noncomm_ring
    _ = R⁻¹ * (R * ρ₁.val * R) * R⁻¹ := by rw [hM2]
    _ = (R⁻¹ * R) * ρ₁.val * (R * R⁻¹) := by noncomm_ring
    _ = ρ₁.val := by rw [hleft, hright, one_mul, mul_one]

def fcBasis (ρ₀ ρ₁ : Density I) : Matrix.unitaryGroup I ℂ :=
  (fidelityTransport_posSemidef ρ₀ ρ₁).1.eigenvectorUnitary

def fcEigenvalue (ρ₀ ρ₁ : Density I) (j : I) : ℝ :=
  (fidelityTransport_posSemidef ρ₀ ρ₁).1.eigenvalues j

theorem fcBasis_unitary (ρ₀ ρ₁ : Density I) :
    (fcBasis ρ₀ ρ₁ : Mat I) * (fcBasis ρ₀ ρ₁ : Mat I)ᴴ = 1 := by
  simpa only [Unitary.coe_star, Matrix.star_eq_conjTranspose] using
    Unitary.coe_mul_star_self (fcBasis ρ₀ ρ₁)

theorem fcEigenvalue_nonneg (ρ₀ ρ₁ : Density I) (j : I) :
    0 ≤ fcEigenvalue ρ₀ ρ₁ j :=
  (fidelityTransport_posSemidef ρ₀ ρ₁).eigenvalues_nonneg j

theorem fcBasis_diagonal (ρ₀ ρ₁ : Density I) :
    (fcBasis ρ₀ ρ₁ : Mat I)ᴴ * fidelityTransport ρ₀ ρ₁ *
      (fcBasis ρ₀ ρ₁ : Mat I) =
        Matrix.diagonal (fun j => (fcEigenvalue ρ₀ ρ₁ j : ℂ)) := by
  simpa [fcBasis, fcEigenvalue, Unitary.conjStarAlgAut_star_apply,
    Matrix.star_eq_conjTranspose, Function.comp_def, RCLike.ofReal] using
    (fidelityTransport_posSemidef ρ₀ ρ₁).1.conjStarAlgAut_star_eigenvectorUnitary

theorem columnNormSq_diagonalGram (A : Mat I) (j : I) :
    columnNormSq A j = ((Aᴴ * A) j j).re := by
  simp only [columnNormSq, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self]
  rfl

theorem basis_gram_matrix (ρ : Density I) (U : Mat I) :
    (sqrtPSD ρ.val * U)ᴴ * (sqrtPSD ρ.val * U) = Uᴴ * ρ.val * U := by
  have hsqrt : (sqrtPSD ρ.val).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg ρ.val)
  have hstar : (sqrtPSD ρ.val)ᴴ = sqrtPSD ρ.val := hsqrt.isHermitian.eq
  calc
    (sqrtPSD ρ.val * U)ᴴ * (sqrtPSD ρ.val * U) =
        Uᴴ * (sqrtPSD ρ.val * (sqrtPSD ρ.val)ᴴ) * U := by
      rw [Matrix.conjTranspose_mul, hstar]
      noncomm_ring
    _ = Uᴴ * ρ.val * U := by rw [sqrtPSD_columnGram ρ.property.1]

theorem basis_columnNormSq_diagonal (ρ : Density I) (U : Mat I) (j : I) :
    columnNormSq (sqrtPSD ρ.val * U) j = ((Uᴴ * ρ.val * U) j j).re := by
  rw [columnNormSq_diagonalGram, basis_gram_matrix]

theorem fc_rotated_transport (ρ₀ ρ₁ : Density I) (hρ₀ : ρ₀.val.PosDef) :
    (fcBasis ρ₀ ρ₁ : Mat I)ᴴ * ρ₁.val * (fcBasis ρ₀ ρ₁ : Mat I) =
      Matrix.diagonal (fun j => (fcEigenvalue ρ₀ ρ₁ j : ℂ)) *
        ((fcBasis ρ₀ ρ₁ : Mat I)ᴴ * ρ₀.val * (fcBasis ρ₀ ρ₁ : Mat I)) *
          Matrix.diagonal (fun j => (fcEigenvalue ρ₀ ρ₁ j : ℂ)) := by
  let U : Mat I := fcBasis ρ₀ ρ₁
  let T := fidelityTransport ρ₀ ρ₁
  have hU : U * Uᴴ = 1 := fcBasis_unitary ρ₀ ρ₁
  have htransport : T * ρ₀.val * T = ρ₁.val := fidelityTransport_identity ρ₀ ρ₁ hρ₀
  have hdiag : Uᴴ * T * U =
      Matrix.diagonal (fun j => (fcEigenvalue ρ₀ ρ₁ j : ℂ)) := fcBasis_diagonal ρ₀ ρ₁
  change Uᴴ * ρ₁.val * U = _
  calc
    Uᴴ * ρ₁.val * U = Uᴴ * (T * ρ₀.val * T) * U := by rw [htransport]
    _ = (Uᴴ * T * U) * (Uᴴ * ρ₀.val * U) * (Uᴴ * T * U) := by
      symm
      calc
        (Uᴴ * T * U) * (Uᴴ * ρ₀.val * U) * (Uᴴ * T * U) =
            Uᴴ * T * (U * Uᴴ) * ρ₀.val * (U * Uᴴ) * T * U := by noncomm_ring
        _ = Uᴴ * (T * ρ₀.val * T) * U := by rw [hU]; noncomm_ring
    _ = _ := by rw [hdiag]

theorem fc_column_norm_relation (ρ₀ ρ₁ : Density I) (hρ₀ : ρ₀.val.PosDef) (j : I) :
    columnNormSq (sqrtPSD ρ₁.val * (fcBasis ρ₀ ρ₁ : Mat I)) j =
      fcEigenvalue ρ₀ ρ₁ j ^ 2 *
        columnNormSq (sqrtPSD ρ₀.val * (fcBasis ρ₀ ρ₁ : Mat I)) j := by
  rw [basis_columnNormSq_diagonal, basis_columnNormSq_diagonal]
  have h := congrArg Complex.re (congrArg (fun M : Mat I => M j j)
    (fc_rotated_transport ρ₀ ρ₁ hρ₀))
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, sub_zero] at h
  rw [h]
  ring

theorem fc_columnRoot_relation (ρ₀ ρ₁ : Density I) (hρ₀ : ρ₀.val.PosDef) (j : I) :
    columnRoot (sqrtPSD ρ₀.val * (fcBasis ρ₀ ρ₁ : Mat I))
      (sqrtPSD ρ₁.val * (fcBasis ρ₀ ρ₁ : Mat I)) j =
      fcEigenvalue ρ₀ ρ₁ j *
        columnNormSq (sqrtPSD ρ₀.val * (fcBasis ρ₀ ρ₁ : Mat I)) j := by
  have hp := columnNormSq_nonneg (sqrtPSD ρ₀.val * (fcBasis ρ₀ ρ₁ : Mat I)) j
  have ht := fcEigenvalue_nonneg ρ₀ ρ₁ j
  have hr := columnRoot_nonneg (sqrtPSD ρ₀.val * (fcBasis ρ₀ ρ₁ : Mat I))
    (sqrtPSD ρ₁.val * (fcBasis ρ₀ ρ₁ : Mat I)) j
  have hs : columnRoot (sqrtPSD ρ₀.val * (fcBasis ρ₀ ρ₁ : Mat I))
      (sqrtPSD ρ₁.val * (fcBasis ρ₀ ρ₁ : Mat I)) j ^ 2 =
      (fcEigenvalue ρ₀ ρ₁ j *
        columnNormSq (sqrtPSD ρ₀.val * (fcBasis ρ₀ ρ₁ : Mat I)) j) ^ 2 := by
    rw [columnRoot_sq, fc_column_norm_relation ρ₀ ρ₁ hρ₀ j]
    ring
  have hprod := mul_nonneg ht hp
  nlinarith

def basisEffect (U : Mat I) (j : I) : Mat I :=
  Matrix.vecMulVec (fun i => U i j) (star (fun i => U i j))

theorem basisEffect_posSemidef (U : Mat I) (j : I) :
    (basisEffect U j).PosSemidef :=
  Matrix.posSemidef_vecMulVec_self_star (fun i => U i j)

theorem basisEffect_sum (U : Mat I) : (∑ j : I, basisEffect U j) = U * Uᴴ := by
  ext i k
  simp only [Matrix.sum_apply, basisEffect, Matrix.vecMulVec_apply,
    Pi.star_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]

def basisPOVM (U : Mat I) (hU : U * Uᴴ = 1) : POVM I I where
  effect := basisEffect U
  positive := basisEffect_posSemidef U
  normalized := (basisEffect_sum U).trans hU

theorem basis_measurement_diagonal (ρ : Density I) (U : Mat I)
    (hU : U * Uᴴ = 1) (j : I) :
    measurementProbability (basisPOVM U hU) ρ.val j = ((Uᴴ * ρ.val * U) j j).re := by
  have h : (ρ.val * basisEffect U j).trace = (Uᴴ * ρ.val * U) j j := by
    simp only [basisEffect, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
      Matrix.vecMulVec_apply, Pi.star_apply, Matrix.conjTranspose_apply]
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k hk
    apply Finset.sum_congr rfl
    intro i hi
    ring
  exact congrArg Complex.re h

theorem basis_measurement_columnNormSq (ρ : Density I) (U : Mat I)
    (hU : U * Uᴴ = 1) (j : I) :
    measurementProbability (basisPOVM U hU) ρ.val j =
      columnNormSq (sqrtPSD ρ.val * U) j :=
  (basis_measurement_diagonal ρ U hU j).trans (basis_columnNormSq_diagonal ρ U j).symm

def fcPOVM (ρ₀ ρ₁ : Density I) : POVM I I :=
  basisPOVM (fcBasis ρ₀ ρ₁ : Mat I) (fcBasis_unitary ρ₀ ρ₁)

theorem fc_measurement_norm_relation (ρ₀ ρ₁ : Density I) (hρ₀ : ρ₀.val.PosDef) (j : I) :
    measurementProbability (fcPOVM ρ₀ ρ₁) ρ₁.val j =
      fcEigenvalue ρ₀ ρ₁ j ^ 2 * measurementProbability (fcPOVM ρ₀ ρ₁) ρ₀.val j := by
  simp only [fcPOVM, basis_measurement_columnNormSq]
  exact fc_column_norm_relation ρ₀ ρ₁ hρ₀ j

theorem fc_measurement_root_relation (ρ₀ ρ₁ : Density I) (hρ₀ : ρ₀.val.PosDef) (j : I) :
    Real.sqrt (measurementProbability (fcPOVM ρ₀ ρ₁) ρ₀.val j *
      measurementProbability (fcPOVM ρ₀ ρ₁) ρ₁.val j) =
      fcEigenvalue ρ₀ ρ₁ j * measurementProbability (fcPOVM ρ₀ ρ₁) ρ₀.val j := by
  simp only [fcPOVM, basis_measurement_columnNormSq]
  exact fc_columnRoot_relation ρ₀ ρ₁ hρ₀ j

theorem trace_unitary_conjugate (X U : Mat I) (hU : U * Uᴴ = 1) :
    (Uᴴ * X * U).trace = X.trace := by
  calc
    (Uᴴ * X * U).trace = (U * Uᴴ * X).trace := Matrix.trace_mul_cycle Uᴴ X U
    _ = X.trace := by rw [hU, one_mul]

theorem fidelityTransport_trace_density (ρ₀ ρ₁ : Density I) (hρ₀ : ρ₀.val.PosDef) :
    (fidelityTransport ρ₀ ρ₁ * ρ₀.val).trace =
      (sqrtPSD (sqrtPSD ρ₀.val * ρ₁.val * sqrtPSD ρ₀.val)).trace := by
  let R := sqrtPSD ρ₀.val
  let M := sqrtPSD (R * ρ₁.val * R)
  have hR2 : R * R = ρ₀.val := by
    change CFC.sqrt ρ₀.val * CFC.sqrt ρ₀.val = ρ₀.val
    rw [← pow_two]
    exact CFC.sq_sqrt ρ₀.val ρ₀.property.1.nonneg
  have hdet : IsUnit R.det :=
    (Matrix.isUnit_iff_isUnit_det R).mp (sqrtPSD_isUnit ρ₀ hρ₀)
  have hleft : R⁻¹ * R = 1 := Matrix.nonsing_inv_mul R hdet
  have hright : R * R⁻¹ = 1 := Matrix.mul_nonsing_inv R hdet
  have hproduct : fidelityTransport ρ₀ ρ₁ * ρ₀.val = R⁻¹ * M * R := by
    change (R⁻¹ * M * R⁻¹) * ρ₀.val = _
    rw [← hR2]
    calc
      (R⁻¹ * M * R⁻¹) * (R * R) = R⁻¹ * M * (R⁻¹ * R) * R := by noncomm_ring
      _ = R⁻¹ * M * R := by rw [hleft, mul_one]
  change (fidelityTransport ρ₀ ρ₁ * ρ₀.val).trace = M.trace
  rw [hproduct]
  calc
    (R⁻¹ * M * R).trace = (R * R⁻¹ * M).trace := Matrix.trace_mul_cycle R⁻¹ M R
    _ = M.trace := by rw [hright, one_mul]

theorem fc_trace_column_moment (ρ₀ ρ₁ : Density I) :
    (∑ j : I, fcEigenvalue ρ₀ ρ₁ j *
      columnNormSq (sqrtPSD ρ₀.val * (fcBasis ρ₀ ρ₁ : Mat I)) j) =
        (fidelityTransport ρ₀ ρ₁ * ρ₀.val).trace.re := by
  let U : Mat I := fcBasis ρ₀ ρ₁
  let T := fidelityTransport ρ₀ ρ₁
  have hU : U * Uᴴ = 1 := fcBasis_unitary ρ₀ ρ₁
  have hdiag : Uᴴ * T * U =
      Matrix.diagonal (fun j => (fcEigenvalue ρ₀ ρ₁ j : ℂ)) := fcBasis_diagonal ρ₀ ρ₁
  change (∑ j : I, fcEigenvalue ρ₀ ρ₁ j * columnNormSq (sqrtPSD ρ₀.val * U) j) = _
  calc
    (∑ j : I, fcEigenvalue ρ₀ ρ₁ j * columnNormSq (sqrtPSD ρ₀.val * U) j) =
        ∑ j : I, fcEigenvalue ρ₀ ρ₁ j * ((Uᴴ * ρ₀.val * U) j j).re := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [basis_columnNormSq_diagonal]
    _ = (Matrix.diagonal (fun j => (fcEigenvalue ρ₀ ρ₁ j : ℂ)) *
          (Uᴴ * ρ₀.val * U)).trace.re := by
      simp only [Matrix.trace, Matrix.diag_apply, Matrix.diagonal_mul, Complex.re_sum,
        Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    _ = ((Uᴴ * T * U) * (Uᴴ * ρ₀.val * U)).trace.re := by rw [hdiag]
    _ = (Uᴴ * (T * ρ₀.val) * U).trace.re := by
      apply congrArg (fun X : Mat I => X.trace.re)
      calc
        (Uᴴ * T * U) * (Uᴴ * ρ₀.val * U) =
            Uᴴ * T * (U * Uᴴ) * ρ₀.val * U := by noncomm_ring
        _ = Uᴴ * (T * ρ₀.val) * U := by rw [hU]; noncomm_ring
    _ = (T * ρ₀.val).trace.re :=
      congrArg Complex.re (trace_unitary_conjugate (T * ρ₀.val) U hU)

theorem fc_classical_affinity_sandwich (ρ₀ ρ₁ : Density I) (hρ₀ : ρ₀.val.PosDef) :
    (∑ j : I, Real.sqrt (measurementProbability (fcPOVM ρ₀ ρ₁) ρ₀.val j *
      measurementProbability (fcPOVM ρ₀ ρ₁) ρ₁.val j)) =
      (sqrtPSD (sqrtPSD ρ₀.val * ρ₁.val * sqrtPSD ρ₀.val)).trace.re := by
  calc
    (∑ j : I, Real.sqrt (measurementProbability (fcPOVM ρ₀ ρ₁) ρ₀.val j *
        measurementProbability (fcPOVM ρ₀ ρ₁) ρ₁.val j)) =
        ∑ j : I, fcEigenvalue ρ₀ ρ₁ j *
          columnNormSq (sqrtPSD ρ₀.val * (fcBasis ρ₀ ρ₁ : Mat I)) j := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [fc_measurement_root_relation ρ₀ ρ₁ hρ₀ j]
      rw [fcPOVM, basis_measurement_columnNormSq]
    _ = (fidelityTransport ρ₀ ρ₁ * ρ₀.val).trace.re := fc_trace_column_moment ρ₀ ρ₁
    _ = (sqrtPSD (sqrtPSD ρ₀.val * ρ₁.val * sqrtPSD ρ₀.val)).trace.re :=
      congrArg Complex.re (fidelityTransport_trace_density ρ₀ ρ₁ hρ₀)

theorem fc_measurement_affinity_rootFidelity (ρ₀ ρ₁ : Density I)
    (hρ₀ : ρ₀.val.PosDef) :
    (∑ j : I, Real.sqrt (measurementProbability (fcPOVM ρ₀ ρ₁) ρ₀.val j *
      measurementProbability (fcPOVM ρ₀ ρ₁) ρ₁.val j)) = rootFidelity ρ₀.val ρ₁.val := by
  rw [fc_classical_affinity_sandwich ρ₀ ρ₁ hρ₀]
  symm
  exact Geometry.sqrt_product_absolute_trace_sandwich
    ρ₀.val ρ₁.val ρ₀.property.1 ρ₁.property.1

theorem matrix_flag_affinity_le (ρ₀ ρ₁ : Density I) (U : Mat I)
    (hU : U * Uᴴ = 1) :
    affinity (flagStateInBasis ρ₀ U hU).val (flagStateInBasis ρ₁ U hU).val ≤
      affinity ρ₀.val ρ₁.val := by
  have h := QuantumProver.MatrixAnalysis.Affinity.affinity_partialTraceRight
    (flagStateInBasis ρ₀ U hU).val (flagStateInBasis ρ₁ U hU).val
    (flagStateInBasis ρ₀ U hU).property.1 (flagStateInBasis ρ₁ U hU).property.1
  change affinity (flagStateInBasis ρ₀ U hU).val (flagStateInBasis ρ₁ U hU).val ≤
    affinity (partialTraceRight (flagStateInBasis ρ₀ U hU).val)
      (partialTraceRight (flagStateInBasis ρ₁ U hU).val) at h
  simpa only [flagStateInBasis_discard] using h

theorem flagAmplitude_columnGram (A : Mat I) :
    (flagAmplitude A)ᴴ * flagAmplitude A =
      Matrix.diagonal (fun j => (columnNormSq A j : ℂ)) := by
  ext j k
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fintype.sum_prod_type, Matrix.diagonal_apply]
  by_cases h : j = k
  · subst k
    rw [if_pos rfl]
    calc
      (∑ i : I, ∑ l : I, star (flagAmplitude A (i, l) j) *
          flagAmplitude A (i, l) j) =
          ∑ i : I, star (A i j) * A i j := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.sum_eq_single j]
        · simp [flagAmplitude]
        · intro l hl hlj
          simp [flagAmplitude, hlj]
        · simp
      _ = (columnNormSq A j : ℂ) := by
        unfold columnNormSq
        push_cast
        apply Finset.sum_congr rfl
        intro i hi
        rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self]
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro i hi
    apply Finset.sum_eq_zero
    intro l hl
    by_cases hj : l = j
    · subst l
      simp [flagAmplitude, h]
    · simp [flagAmplitude, hj]

theorem flagGram_blockDiagonal (A : Mat I) :
    flagGram A = Matrix.blockDiagonal
      (fun j => Matrix.vecMulVec (fun i => A i j) (star (fun i => A i j))) := by
  ext x y
  rcases x with ⟨i, j⟩
  rcases y with ⟨k, l⟩
  simp only [flagGram_apply, Matrix.blockDiagonal_apply',
    Matrix.vecMulVec_apply, Pi.star_apply]

def columnProjector (A : Mat I) (j : I) : Mat I :=
  Matrix.vecMulVec (fun i => A i j) (star (fun i => A i j))

theorem columnProjector_posSemidef (A : Mat I) (j : I) :
    (columnProjector A j).PosSemidef :=
  Matrix.posSemidef_vecMulVec_self_star (fun i => A i j)

theorem columnProjector_trace (A : Mat I) (j : I) :
    (columnProjector A j).trace = (columnNormSq A j : ℂ) := by
  simp only [columnProjector, Matrix.trace_vecMulVec, dotProduct,
    Pi.star_apply, columnNormSq]
  push_cast
  apply Finset.sum_congr rfl
  intro i hi
  rw [Complex.star_def, mul_comm, ← Complex.normSq_eq_conj_mul_self]

theorem columnProjector_square (A : Mat I) (j : I) :
    columnProjector A j * columnProjector A j =
      columnNormSq A j • columnProjector A j := by
  have hinner : (star (fun i => A i j)) ⬝ᵥ (fun i => A i j) =
      (columnNormSq A j : ℂ) := by
    simp only [dotProduct, Pi.star_apply, columnNormSq]
    push_cast
    apply Finset.sum_congr rfl
    intro i hi
    rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self]
  unfold columnProjector
  rw [Matrix.vecMulVec_mul_vecMulVec, hinner, Matrix.vecMulVec_smul]
  ext i k
  simp [Matrix.smul_apply, Complex.real_smul, smul_eq_mul]

theorem columnProjector_zero (A : Mat I) (j : I) (hp : columnNormSq A j = 0) :
    columnProjector A j = 0 := by
  have hs := columnVector_norm_sq A j
  rw [hp] at hs
  have hn : ‖columnVector A j‖ = 0 := by nlinarith [norm_nonneg (columnVector A j)]
  have hz := norm_eq_zero.mp hn
  have hv : ∀ i, A i j = 0 := by
    intro i
    have h := congrArg (fun v : EuclideanSpace ℂ I => v i) hz
    exact h
  ext i k
  simp [columnProjector, Matrix.vecMulVec_apply, Pi.star_apply, hv]

theorem columnProjector_sqrt (A : Mat I) (j : I) :
    sqrtPSD (columnProjector A j) =
      (1 / Real.sqrt (columnNormSq A j)) • columnProjector A j := by
  by_cases hp : columnNormSq A j = 0
  · rw [columnProjector_zero A j hp]
    simp [sqrtPSD, hp]
  · have hp0 : 0 < columnNormSq A j :=
      lt_of_le_of_ne (columnNormSq_nonneg A j) (Ne.symm hp)
    have hs0 : 0 < Real.sqrt (columnNormSq A j) := Real.sqrt_pos.mpr hp0
    have hscalar : (1 / Real.sqrt (columnNormSq A j)) *
        (1 / Real.sqrt (columnNormSq A j)) * columnNormSq A j = 1 := by
      field_simp [hs0.ne']
      nlinarith [Real.sq_sqrt hp0.le]
    apply CFC.sqrt_unique
    · calc
        ((1 / Real.sqrt (columnNormSq A j)) • columnProjector A j) *
            ((1 / Real.sqrt (columnNormSq A j)) • columnProjector A j) =
            ((1 / Real.sqrt (columnNormSq A j)) *
              (1 / Real.sqrt (columnNormSq A j)) * columnNormSq A j) •
                columnProjector A j := by
          rw [smul_mul_assoc, mul_smul_comm, smul_smul,
            columnProjector_square, smul_smul]
      _ = columnProjector A j := by rw [hscalar, one_smul]
    · exact ((columnProjector_posSemidef A j).smul
        (div_nonneg (by norm_num) (Real.sqrt_nonneg _))).nonneg

theorem columnProjector_trace_product (A B : Mat I) (j : I) :
    (columnProjector A j * columnProjector B j).trace =
      (Complex.normSq (columnOverlap A B j) : ℂ) := by
  have hinner : (star (fun i => A i j)) ⬝ᵥ (fun i => B i j) =
      columnOverlap A B j := rfl
  have hrev : (∑ i : I, A i j * star (B i j)) = star (columnOverlap A B j) := by
    simp only [columnOverlap, star_sum, star_mul, star_star]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  unfold columnProjector
  rw [Matrix.vecMulVec_mul_vecMulVec, hinner, Matrix.trace_vecMulVec]
  change (∑ i : I, A i j * (columnOverlap A B j * star (B i j))) = _
  calc
    _ = columnOverlap A B j * (∑ i : I, A i j * star (B i j)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = columnOverlap A B j * star (columnOverlap A B j) := by rw [hrev]
    _ = (Complex.normSq (columnOverlap A B j) : ℂ) := by
      rw [Complex.star_def, mul_comm, ← Complex.normSq_eq_conj_mul_self]

theorem columnProjector_sandwich (A B : Mat I) (j : I) :
    columnProjector A j * columnProjector B j * columnProjector A j =
      Complex.normSq (columnOverlap A B j) • columnProjector A j := by
  have hAB : (star (fun i => A i j)) ⬝ᵥ (fun i => B i j) =
      columnOverlap A B j := rfl
  have hBA : (star (fun i => B i j)) ⬝ᵥ (fun i => A i j) =
      star (columnOverlap A B j) := by
    simp only [dotProduct, Pi.star_apply, columnOverlap, star_sum, star_mul, star_star]
  have hprod : columnOverlap A B j * star (columnOverlap A B j) =
      (Complex.normSq (columnOverlap A B j) : ℂ) := by
    rw [Complex.star_def, mul_comm, ← Complex.normSq_eq_conj_mul_self]
  unfold columnProjector
  rw [Matrix.vecMulVec_mul_vecMulVec, hAB, Matrix.vecMulVec_mul_vecMulVec,
    smul_dotProduct, hBA, smul_eq_mul, Matrix.vecMulVec_smul, hprod]
  ext i k
  simp [Matrix.smul_apply, Complex.real_smul, smul_eq_mul]

theorem columnProjector_rootFidelity (A B : Mat I) (j : I) :
    rootFidelity (columnProjector A j) (columnProjector B j) =
      ‖columnOverlap A B j‖ := by
  by_cases hp : columnNormSq A j = 0
  · have ho := columnOverlap_zero_of_left_zero A B j hp
    rw [columnProjector_zero A j hp]
    simp [rootFidelity, traceNorm, sqrtPSD, ho]
  · have hp0 : 0 < columnNormSq A j :=
      lt_of_le_of_ne (columnNormSq_nonneg A j) (Ne.symm hp)
    have hs0 : 0 < Real.sqrt (columnNormSq A j) := Real.sqrt_pos.mpr hp0
    have hcancel : (1 / Real.sqrt (columnNormSq A j)) *
        (1 / Real.sqrt (columnNormSq A j)) * columnNormSq A j = 1 := by
      field_simp [hs0.ne']
      nlinarith [Real.sq_sqrt hp0.le]
    have hfactor : (1 / Real.sqrt (columnNormSq A j)) *
        (1 / Real.sqrt (columnNormSq A j)) = 1 / columnNormSq A j := by
      apply (eq_div_iff hp0.ne').mpr
      exact hcancel
    have hsand : sqrtPSD (columnProjector A j) * columnProjector B j *
        sqrtPSD (columnProjector A j) =
          (Complex.normSq (columnOverlap A B j) / columnNormSq A j) •
            columnProjector A j := by
      simp only [columnProjector_sqrt]
      calc
        _ = ((1 / Real.sqrt (columnNormSq A j)) *
            (1 / Real.sqrt (columnNormSq A j))) •
              (columnProjector A j * columnProjector B j * columnProjector A j) := by
          simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
        _ = _ := by
          rw [columnProjector_sandwich, smul_smul, hfactor]
          congr 1
          ring
    have hnonneg : 0 ≤ Complex.normSq (columnOverlap A B j) / columnNormSq A j :=
      div_nonneg (Complex.normSq_nonneg _) hp0.le
    unfold rootFidelity traceNorm sqrtPSD
    rw [Geometry.sqrt_product_absolute_trace_sandwich _ _
      (columnProjector_posSemidef A j) (columnProjector_posSemidef B j)]
    dsimp only [sqrtPSD] at hsand
    rw [hsand, QuantumProver.DepolarizingPrivateInformation.matrix_sqrt_real_smul _ hnonneg
      (columnProjector_posSemidef A j)]
    change (Real.sqrt (Complex.normSq (columnOverlap A B j) / columnNormSq A j) •
      sqrtPSD (columnProjector A j)).trace.re = _
    rw [columnProjector_sqrt]
    simp only [Matrix.trace_smul, Complex.smul_re, columnProjector_trace,
      Complex.ofReal_re]
    rw [Real.sqrt_div (Complex.normSq_nonneg _) _, Complex.normSq_eq_norm_sq,
      Real.sqrt_sq (norm_nonneg _)]
    calc
      _ = ‖columnOverlap A B j‖ *
          ((1 / Real.sqrt (columnNormSq A j)) *
            (1 / Real.sqrt (columnNormSq A j)) * columnNormSq A j) := by ring
      _ = ‖columnOverlap A B j‖ := by rw [hcancel, mul_one]

theorem columnProjector_affinity (A B : Mat I) (j : I) :
    affinity (columnProjector A j) (columnProjector B j) =
      Complex.normSq (columnOverlap A B j) / columnRoot A B j := by
  unfold affinity
  rw [columnProjector_sqrt, columnProjector_sqrt]
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul,
    Matrix.trace_smul, Complex.smul_re, columnProjector_trace_product,
    Complex.ofReal_re]
  unfold columnRoot
  rw [Real.sqrt_mul (columnNormSq_nonneg A j)]
  simp only [div_eq_mul_inv, one_mul, mul_inv_rev]
  ring

theorem columnRoot_mul_normalized_normSq (A B : Mat I) (j : I) :
    columnRoot A B j * Complex.normSq (normalizedColumnOverlap A B j) =
      Complex.normSq (columnOverlap A B j) / columnRoot A B j := by
  by_cases hr : columnRoot A B j = 0
  · simp [hr]
  · unfold normalizedColumnOverlap
    rw [Complex.normSq_div, Complex.normSq_ofReal]
    field_simp [hr]
    <;> ring

theorem columnProjector_affinity_moment (A B : Mat I) (j : I) :
    affinity (columnProjector A j) (columnProjector B j) =
      columnMass A B j *
        (columnBeta A B j * Complex.normSq (normalizedColumnOverlap A B j)) := by
  rw [columnProjector_affinity, ← columnRoot_mul_normalized_normSq,
    ← mul_assoc, columnMass_mul_beta]

theorem flagGram_affinity_moment (A B : Mat I) :
    affinity (flagGram A) (flagGram B) =
      ∑ j : I, columnMass A B j *
        (columnBeta A B j * Complex.normSq (normalizedColumnOverlap A B j)) := by
  calc
    affinity (flagGram A) (flagGram B) =
        ∑ j : I, affinity (columnProjector A j) (columnProjector B j) := by
      have ht := QuantumProver.DepolarizingPrivateInformation.trace_matrixBlockDiagonal_sqrt_product
        (fun j => columnProjector A j) (fun j => columnProjector B j)
        (fun j => columnProjector_posSemidef A j)
        (fun j => columnProjector_posSemidef B j)
      unfold affinity sqrtPSD
      rw [flagGram_blockDiagonal, flagGram_blockDiagonal]
      simpa only [columnProjector, Complex.re_sum] using congrArg Complex.re ht
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      exact columnProjector_affinity_moment A B j

theorem flagStateInBasis_affinity_moment (ρ₀ ρ₁ : Density I) (U : Mat I)
    (hU : U * Uᴴ = 1) :
    affinity (flagStateInBasis ρ₀ U hU).val (flagStateInBasis ρ₁ U hU).val =
      ∑ j : I, columnMass (sqrtPSD ρ₀.val * U) (sqrtPSD ρ₁.val * U) j *
        (columnBeta (sqrtPSD ρ₀.val * U) (sqrtPSD ρ₁.val * U) j *
          Complex.normSq (normalizedColumnOverlap (sqrtPSD ρ₀.val * U)
            (sqrtPSD ρ₁.val * U) j)) :=
  flagGram_affinity_moment _ _

theorem columnOverlap_norm_moment (A B : Mat I) (j : I) :
    ‖columnOverlap A B j‖ =
      columnRoot A B j * ‖normalizedColumnOverlap A B j‖ := by
  have h := congrArg norm (root_mul_normalizedColumnOverlap A B j)
  simpa only [norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (columnRoot_nonneg A B j)] using h.symm

theorem flagGram_rootFidelity_moment (A B : Mat I) :
    rootFidelity (flagGram A) (flagGram B) =
      ∑ j : I, columnRoot A B j * ‖normalizedColumnOverlap A B j‖ := by
  have hA := fun j => columnProjector_posSemidef A j
  have hB := fun j => columnProjector_posSemidef B j
  calc
    rootFidelity (flagGram A) (flagGram B) =
        ∑ j : I, rootFidelity (columnProjector A j) (columnProjector B j) := by
      unfold rootFidelity traceNorm sqrtPSD
      rw [flagGram_blockDiagonal, flagGram_blockDiagonal]
      change (CFC.sqrt
        ((CFC.sqrt (Matrix.blockDiagonal (fun j => columnProjector A j)) *
          CFC.sqrt (Matrix.blockDiagonal (fun j => columnProjector B j)))ᴴ *
         (CFC.sqrt (Matrix.blockDiagonal (fun j => columnProjector A j)) *
          CFC.sqrt (Matrix.blockDiagonal (fun j => columnProjector B j))))).trace.re = _
      simp only [QuantumProver.DepolarizingPrivateInformation.matrixBlockDiagonal_sqrt _ hA,
        QuantumProver.DepolarizingPrivateInformation.matrixBlockDiagonal_sqrt _ hB]
      simp only [← Matrix.blockDiagonal_mul, Matrix.blockDiagonal_conjTranspose]
      rw [
        QuantumProver.DepolarizingPrivateInformation.matrixBlockDiagonal_sqrt _
          (fun j => Matrix.posSemidef_conjTranspose_mul_self _),
        Matrix.trace_blockDiagonal, Complex.re_sum]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [columnProjector_rootFidelity, columnOverlap_norm_moment]

theorem fc_mass_beta_moment (ρ₀ ρ₁ : Density I) (hρ₀ : ρ₀.val.PosDef) :
    (∑ j : I, columnMass (sqrtPSD ρ₀.val * (fcBasis ρ₀ ρ₁ : Mat I))
        (sqrtPSD ρ₁.val * (fcBasis ρ₀ ρ₁ : Mat I)) j *
      columnBeta (sqrtPSD ρ₀.val * (fcBasis ρ₀ ρ₁ : Mat I))
        (sqrtPSD ρ₁.val * (fcBasis ρ₀ ρ₁ : Mat I)) j) =
      rootFidelity ρ₀.val ρ₁.val := by
  rw [← fc_measurement_affinity_rootFidelity ρ₀ ρ₁ hρ₀]
  apply Finset.sum_congr rfl
  intro j hj
  rw [columnMass_mul_beta]
  simp only [fcPOVM, basis_measurement_columnNormSq, columnRoot]

theorem fc_flag_rootFidelity_sq_le (ρ₀ ρ₁ : Density I) (hρ₀ : ρ₀.val.PosDef) :
    rootFidelity
        (flagStateInBasis ρ₀ (fcBasis ρ₀ ρ₁ : Mat I) (fcBasis_unitary ρ₀ ρ₁)).val
        (flagStateInBasis ρ₁ (fcBasis ρ₀ ρ₁ : Mat I) (fcBasis_unitary ρ₀ ρ₁)).val ^ 2 ≤
      rootFidelity ρ₀.val ρ₁.val * affinity ρ₀.val ρ₁.val := by
  let U : Mat I := fcBasis ρ₀ ρ₁
  let A := sqrtPSD ρ₀.val * U
  let B := sqrtPSD ρ₁.val * U
  have hF : (∑ j : I, columnRoot A B j) = rootFidelity ρ₀.val ρ₁.val := by
    simpa only [columnMass_mul_beta] using fc_mass_beta_moment ρ₀ ρ₁ hρ₀
  have hF0 : 0 ≤ rootFidelity ρ₀.val ρ₁.val := by
    rw [← hF]
    exact Finset.sum_nonneg (fun j _ => columnRoot_nonneg A B j)
  have hcs := Scalar.weighted_column_cauchy Finset.univ (columnRoot A B)
    (fun j => ‖normalizedColumnOverlap A B j‖)
    (fun j _ => columnRoot_nonneg A B j)
  have hm : affinity (flagGram A) (flagGram B) =
      ∑ j : I, columnRoot A B j * ‖normalizedColumnOverlap A B j‖ ^ 2 := by
    rw [flagGram_affinity_moment]
    simp only [← mul_assoc, columnMass_mul_beta, Complex.normSq_eq_norm_sq]
  rw [hF, ← hm, ← flagGram_rootFidelity_moment] at hcs
  exact hcs.trans (mul_le_mul_of_nonneg_left
    (matrix_flag_affinity_le ρ₀ ρ₁ U (fcBasis_unitary ρ₀ ρ₁)) hF0)

theorem flagGram_entropy_columnDiagonal (A : Mat I) :
    entropyBits (flagGram A) =
      entropyBits (Matrix.diagonal (fun j => (columnNormSq A j : ℂ))) := by
  have h := QuantumProver.ConditionalEntropy.ConditionalRange.entropyBits_rectangularGram
    (flagAmplitude A)
  rw [flagAmplitude_columnGram] at h
  exact h.symm

end QuantumProver.BellDiagonalSquashedEntanglement.FCColumns

namespace QuantumProver.BellDiagonalSquashedEntanglement.Scalar

theorem binaryEntropy_matrix_bridge (p : ℝ) :
    binaryEntropyBits p = QuantumProver.BellDiagonalSquashedEntanglement.binaryEntropy p := rfl

theorem formationPhi_matrix_bridge (v : ℝ) :
    formationPhi v = QuantumProver.BellDiagonalSquashedEntanglement.phi v := rfl

theorem jointDeficit_matrix_bridge (b u : ℝ) :
    jointDeficit b u = QuantumProver.BellDiagonalSquashedEntanglement.phi (b ^ 2) -
      QuantumProver.BellDiagonalSquashedEntanglement.phi (b ^ 2 - u ^ 2) := rfl

end QuantumProver.BellDiagonalSquashedEntanglement.Scalar

noncomputable section
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace QuantumProver.BellDiagonalSquashedEntanglement.FCColumns

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

def entropyBlockDiagonalHom : (J → Matrix I I ℂ) →⋆ₐ[ℝ]
    Matrix (I × J) (I × J) ℂ where
  toFun := Matrix.blockDiagonal
  map_zero' := Matrix.blockDiagonal_zero
  map_one' := Matrix.blockDiagonal_one
  map_add' := Matrix.blockDiagonal_add
  map_mul' := Matrix.blockDiagonal_mul
  commutes' r := by
    simp [Algebra.algebraMap_eq_smul_one, Matrix.blockDiagonal_smul]
  map_star' B := by
    change Matrix.blockDiagonal (fun j => (B j)ᴴ) = (Matrix.blockDiagonal B)ᴴ
    rw [Matrix.blockDiagonal_conjTranspose]

theorem entropyBlockDiagonalHom_continuous :
    Continuous (entropyBlockDiagonalHom (I := I) (J := J)) := by
  apply continuous_pi
  intro x
  rcases x with ⟨i, j⟩
  apply continuous_pi
  intro y
  rcases y with ⟨k, l⟩
  change Continuous (fun B : J → Matrix I I ℂ => if j = l then B j i k else 0)
  by_cases h : j = l <;> simp only [h, ite_true, ite_false] <;> fun_prop

theorem matrix_cfc_blockDiagonal (f : ℝ → ℝ) (B : J → Matrix I I ℂ)
    (hB : ∀ j, (B j).IsHermitian) :
    cfc f (Matrix.blockDiagonal B) =
      Matrix.blockDiagonal (fun j => cfc f (B j)) := by
  letI : IsometricContinuousFunctionalCalculus ℝ
      (J → Matrix I I ℂ) IsSelfAdjoint :=
    IsSelfAdjoint.instIsometricContinuousFunctionalCalculus
  have hf : ContinuousOn f (⋃ j : J, spectrum ℝ (B j)) :=
    (Set.finite_iUnion (fun j => (B j).finite_real_spectrum)).continuousOn f
  have hab : IsSelfAdjoint B := funext (fun j => hB j)
  have hmap := (entropyBlockDiagonalHom (I := I) (J := J)).map_cfc f B
    (by simpa only [Pi.spectrum_eq] using hf)
    entropyBlockDiagonalHom_continuous hab
    (Matrix.isHermitian_blockDiagonal_iff.mpr hB)
  rw [cfc_map_pi (S := ℝ) f B hf hab hB] at hmap
  exact hmap.symm

theorem matrix_entropyBits_blockDiagonal (B : J → Matrix I I ℂ)
    (hB : ∀ j, (B j).IsHermitian) :
    QuantumProver.SuperchannelDiscrimination.FlaggedStates.entropyBits
        (Matrix.blockDiagonal B) =
      ∑ j : J, QuantumProver.SuperchannelDiscrimination.FlaggedStates.entropyBits (B j) := by
  simp only [QuantumProver.SuperchannelDiscrimination.FlaggedStates.entropyBits,
    matrix_cfc_blockDiagonal _ B hB, Matrix.trace_blockDiagonal, Complex.re_sum]
  rw [← Finset.sum_div, Finset.sum_neg_distrib]

def columnPair (A B : Mat I) (j : I) : Matrix I (Fin 2) ℂ :=
  fun i k => ![A i j, B i j] k

theorem columnPair_rightGram (A B : Mat I) (j : I) :
    columnPair A B j * (columnPair A B j)ᴴ =
      columnProjector A j + columnProjector B j := by
  ext i k
  simp [columnPair, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fin.sum_univ_two, columnProjector, Matrix.vecMulVec_apply, Pi.star_apply]

theorem columnOverlap_self (A : Mat I) (j : I) :
    columnOverlap A A j = (columnNormSq A j : ℂ) := by
  unfold columnOverlap columnNormSq
  push_cast
  apply Finset.sum_congr rfl
  intro i hi
  rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self]

theorem columnPair_gram_zero (A B : Mat I) (j : I) :
    QuantumProver.MatrixAnalysis.TwoColumnEntropy.gram (columnPair A B j) 0 0 =
      (columnNormSq A j : ℂ) := by
  change columnOverlap A A j = _
  exact columnOverlap_self A j

theorem columnPair_gram_one (A B : Mat I) (j : I) :
    QuantumProver.MatrixAnalysis.TwoColumnEntropy.gram (columnPair A B j) 1 1 =
      (columnNormSq B j : ℂ) := by
  change columnOverlap B B j = _
  exact columnOverlap_self B j

theorem columnPair_gram_offdiag (A B : Mat I) (j : I) :
    QuantumProver.MatrixAnalysis.TwoColumnEntropy.gram (columnPair A B j) 0 1 =
      columnOverlap A B j := rfl

theorem columnPair_tau (A B : Mat I) (j : I) :
    QuantumProver.MatrixAnalysis.TwoColumnEntropy.tau
        (QuantumProver.MatrixAnalysis.TwoColumnEntropy.gram (columnPair A B j)) =
      columnNormSq A j + columnNormSq B j := by
  simp only [QuantumProver.MatrixAnalysis.TwoColumnEntropy.tau, QuantumProver.MatrixAnalysis.TwoColumnEntropy.a,
    QuantumProver.MatrixAnalysis.TwoColumnEntropy.b, columnPair_gram_zero, columnPair_gram_one,
    Complex.ofReal_re]

theorem columnPair_delta (A B : Mat I) (j : I) :
    QuantumProver.MatrixAnalysis.TwoColumnEntropy.delta
        (QuantumProver.MatrixAnalysis.TwoColumnEntropy.gram (columnPair A B j)) =
      columnNormSq A j * columnNormSq B j - Complex.normSq (columnOverlap A B j) := by
  simp only [QuantumProver.MatrixAnalysis.TwoColumnEntropy.delta, QuantumProver.MatrixAnalysis.TwoColumnEntropy.a,
    QuantumProver.MatrixAnalysis.TwoColumnEntropy.b, QuantumProver.MatrixAnalysis.TwoColumnEntropy.z,
    columnPair_gram_zero, columnPair_gram_one, columnPair_gram_offdiag, Complex.ofReal_re]

theorem twoColumn_phi_eq (v : ℝ) :
    QuantumProver.MatrixAnalysis.TwoColumnEntropy.phi v = QuantumProver.BellDiagonalSquashedEntanglement.phi v := rfl

theorem columnPair_entropy_formula (A B : Mat I) (j : I) :
    entropyBits (columnProjector A j + columnProjector B j) =
      -((columnNormSq A j + columnNormSq B j) *
        Real.log (columnNormSq A j + columnNormSq B j)) / Real.log 2 +
      (columnNormSq A j + columnNormSq B j) * QuantumProver.BellDiagonalSquashedEntanglement.phi
        (4 * (columnNormSq A j * columnNormSq B j - Complex.normSq (columnOverlap A B j)) /
          (columnNormSq A j + columnNormSq B j) ^ 2) := by
  have h := QuantumProver.MatrixAnalysis.TwoColumnEntropy.entropyBits_twoColumn_phi (columnPair A B j)
  simpa only [columnPair_rightGram, columnPair_tau, columnPair_delta, twoColumn_phi_eq] using h

def columnAverageBlock (A B : Mat I) (j : I) : Mat I :=
  (1 / 2 : ℝ) • (columnProjector A j + columnProjector B j)

theorem columnAverageBlock_posSemidef (A B : Mat I) (j : I) :
    (columnAverageBlock A B j).PosSemidef :=
  ((columnProjector_posSemidef A j).add (columnProjector_posSemidef B j)).smul
    (by norm_num)

theorem columnAverageBlock_entropy (A B : Mat I) (j : I) :
    entropyBits (columnAverageBlock A B j) =
      -(columnMass A B j * Real.log (columnMass A B j)) / Real.log 2 +
      columnMass A B j * QuantumProver.BellDiagonalSquashedEntanglement.phi
        (4 * (columnNormSq A j * columnNormSq B j - Complex.normSq (columnOverlap A B j)) /
          (columnNormSq A j + columnNormSq B j) ^ 2) := by
  have hraw := columnPair_entropy_formula A B j
  change QuantumProver.SuperchannelDiscrimination.FlaggedStates.entropyBits
    (columnProjector A j + columnProjector B j) = _ at hraw
  change QuantumProver.SuperchannelDiscrimination.FlaggedStates.entropyBits
    (columnAverageBlock A B j) = _
  unfold columnAverageBlock
  rw [QuantumProver.SuperchannelDiscrimination.FlaggedStates.entropyBits_smul (1 / 2 : ℝ)
    ((columnProjector_posSemidef A j).add (columnProjector_posSemidef B j)),
    hraw, Matrix.trace_add, columnProjector_trace, columnProjector_trace]
  simp only [Complex.add_re, Complex.ofReal_re]
  unfold columnMass
  rw [show (columnNormSq A j + columnNormSq B j) / 2 =
    (1 / 2 : ℝ) * (columnNormSq A j + columnNormSq B j) by ring,
    QuantumProver.SuperchannelDiscrimination.FlaggedStates.weighted_mul_log]
  ring

theorem columnProjector_entropy (A : Mat I) (j : I) :
    entropyBits (columnProjector A j) =
      -(columnNormSq A j * Real.log (columnNormSq A j)) / Real.log 2 := by
  have hP0 : columnProjector (0 : Mat I) j = 0 := by
    ext i k
    simp [columnProjector, Matrix.vecMulVec_apply]
  have hp0 : columnNormSq (0 : Mat I) j = 0 := by simp [columnNormSq]
  have hu0 : columnOverlap A (0 : Mat I) j = 0 := by simp [columnOverlap]
  have h := columnPair_entropy_formula A (0 : Mat I) j
  rw [hP0, add_zero, hp0, hu0] at h
  norm_num [QuantumProver.BellDiagonalSquashedEntanglement.phi, QuantumProver.BellDiagonalSquashedEntanglement.binaryEntropy] at h
  exact h

theorem flagGram_average_blockDiagonal (A B : Mat I) :
    (1 / 2 : ℝ) • (flagGram A + flagGram B) =
      Matrix.blockDiagonal (columnAverageBlock A B) := by
  rw [flagGram_blockDiagonal, flagGram_blockDiagonal,
    ← Matrix.blockDiagonal_add, ← Matrix.blockDiagonal_smul]
  rfl

theorem flagGram_entropy_columnSum (A : Mat I) :
    entropyBits (flagGram A) =
      ∑ j : I, -(columnNormSq A j * Real.log (columnNormSq A j)) / Real.log 2 := by
  rw [flagGram_blockDiagonal]
  change QuantumProver.SuperchannelDiscrimination.FlaggedStates.entropyBits
    (Matrix.blockDiagonal (columnProjector A)) = _
  rw [matrix_entropyBits_blockDiagonal _ (fun j => (columnProjector_posSemidef A j).1)]
  exact Finset.sum_congr rfl (fun j _ => columnProjector_entropy A j)

theorem flagGram_average_entropy_columnSum (A B : Mat I) :
    entropyBits ((1 / 2 : ℝ) • (flagGram A + flagGram B)) =
      ∑ j : I, (-(columnMass A B j * Real.log (columnMass A B j)) / Real.log 2 +
        columnMass A B j * QuantumProver.BellDiagonalSquashedEntanglement.phi
          (4 * (columnNormSq A j * columnNormSq B j - Complex.normSq (columnOverlap A B j)) /
            (columnNormSq A j + columnNormSq B j) ^ 2)) := by
  rw [flagGram_average_blockDiagonal]
  change QuantumProver.SuperchannelDiscrimination.FlaggedStates.entropyBits
    (Matrix.blockDiagonal (columnAverageBlock A B)) = _
  rw [matrix_entropyBits_blockDiagonal _ (fun j => (columnAverageBlock_posSemidef A B j).1)]
  exact Finset.sum_congr rfl (fun j _ => columnAverageBlock_entropy A B j)

end QuantumProver.BellDiagonalSquashedEntanglement.FCColumns

noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder Matrix Matrix.Norms.L2Operator

namespace QuantumProver.BellDiagonalSquashedEntanglement.FCColumns

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem nonnegative_pair_phi_entropy (p q : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q) :
    -(p * Real.log p + q * Real.log q) / Real.log 2 =
      -((p + q) * Real.log (p + q)) / Real.log 2 +
        (p + q) * QuantumProver.BellDiagonalSquashedEntanglement.phi (4 * (p * q) / (p + q) ^ 2) := by
  let G := QuantumProver.IsotropicFormation.realDiagonal ![p, q]
  have hG : G.PosSemidef := by
    apply Matrix.posSemidef_diagonal_iff.mpr
    intro k
    fin_cases k
    · change (0 : ℂ) ≤ (p : ℂ)
      exact Complex.nonneg_iff.mpr ⟨hp, rfl⟩
    · change (0 : ℂ) ≤ (q : ℂ)
      exact Complex.nonneg_iff.mpr ⟨hq, rfl⟩
  have h := QuantumProver.MatrixAnalysis.TwoColumnEntropy.entropyBits_psd_two_phi hG
  rw [QuantumProver.MatrixAnalysis.TwoColumnEntropy.entropyBits_realDiagonal_two] at h
  simpa [G, QuantumProver.MatrixAnalysis.TwoColumnEntropy.tau, QuantumProver.MatrixAnalysis.TwoColumnEntropy.delta,
    QuantumProver.MatrixAnalysis.TwoColumnEntropy.a, QuantumProver.MatrixAnalysis.TwoColumnEntropy.b,
    QuantumProver.MatrixAnalysis.TwoColumnEntropy.z, QuantumProver.IsotropicFormation.realDiagonal,
    twoColumn_phi_eq] using h

theorem columnBeta_sq (A B : Mat I) (j : I) :
    columnBeta A B j ^ 2 =
      4 * (columnNormSq A j * columnNormSq B j) /
        (columnNormSq A j + columnNormSq B j) ^ 2 := by
  unfold columnBeta columnRoot
  rw [div_pow, mul_pow, Real.sq_sqrt
    (mul_nonneg (columnNormSq_nonneg A j) (columnNormSq_nonneg B j))]
  ring

theorem columnMass_phi_entropy (A B : Mat I) (j : I) :
    columnMass A B j * QuantumProver.BellDiagonalSquashedEntanglement.phi (columnBeta A B j ^ 2) =
      columnMass A B j +
        columnMass A B j * Real.log (columnMass A B j) / Real.log 2 -
        (columnNormSq A j * Real.log (columnNormSq A j) +
          columnNormSq B j * Real.log (columnNormSq B j)) / (2 * Real.log 2) := by
  have h := nonnegative_pair_phi_entropy (columnNormSq A j) (columnNormSq B j)
    (columnNormSq_nonneg A j) (columnNormSq_nonneg B j)
  have hm := QuantumProver.SuperchannelDiscrimination.FlaggedStates.weighted_mul_log
    (1 / 2 : ℝ) (columnNormSq A j + columnNormSq B j)
  have hhalf : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
    rw [one_div, Real.log_inv]
  rw [hhalf, show (1 / 2 : ℝ) * (columnNormSq A j + columnNormSq B j) =
    (columnNormSq A j + columnNormSq B j) / 2 by ring] at hm
  rw [columnBeta_sq]
  unfold columnMass
  field_simp [Scalar.log_two_pos.ne'] at h ⊢
  nlinarith [hm]

theorem columnPair_normalized_argument (A B : Mat I) (j : I) :
    4 * (columnNormSq A j * columnNormSq B j - Complex.normSq (columnOverlap A B j)) /
        (columnNormSq A j + columnNormSq B j) ^ 2 =
      columnBeta A B j ^ 2 * (1 - Complex.normSq (normalizedColumnOverlap A B j)) := by
  have hr2 : columnRoot A B j ^ 2 = columnNormSq A j * columnNormSq B j :=
    Real.sq_sqrt (mul_nonneg (columnNormSq_nonneg A j) (columnNormSq_nonneg B j))
  by_cases hr : columnRoot A B j = 0
  · have hpq : columnNormSq A j * columnNormSq B j = 0 := by simpa [hr] using hr2.symm
    have ho : Complex.normSq (columnOverlap A B j) = 0 :=
      le_antisymm (by simpa [hpq] using columnOverlap_normSq_le A B j)
        (Complex.normSq_nonneg _)
    simp [columnBeta, hr, hpq, ho]
  · have hs : columnNormSq A j + columnNormSq B j ≠ 0 := by
      intro hs
      have hp := columnNormSq_nonneg A j
      have hq := columnNormSq_nonneg B j
      have hp0 : columnNormSq A j = 0 := by linarith
      have hroot : columnRoot A B j = 0 := by simp [columnRoot, hp0]
      exact hr hroot
    unfold normalizedColumnOverlap columnBeta
    rw [Complex.normSq_div, Complex.normSq_ofReal]
    field_simp [hs, hr]
    nlinarith [hr2]

theorem flagGram_pairCost_deficit (A B : Mat I)
    (hMass : ∑ j : I, columnMass A B j = 1) :
    pairCost (flagGram A) (flagGram B) =
      ∑ j : I, columnMass A B j *
        (QuantumProver.BellDiagonalSquashedEntanglement.phi (columnBeta A B j ^ 2) -
          QuantumProver.BellDiagonalSquashedEntanglement.phi (columnBeta A B j ^ 2 *
            (1 - Complex.normSq (normalizedColumnOverlap A B j)))) := by
  unfold pairCost binaryHolevo
  rw [flagGram_average_entropy_columnSum, flagGram_entropy_columnSum,
    flagGram_entropy_columnSum]
  conv_lhs => rw [← hMass]
  rw [← Finset.sum_add_distrib, Finset.sum_div, ← Finset.sum_sub_distrib,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  rw [columnPair_normalized_argument]
  simp only [mul_sub]
  rw [columnMass_phi_entropy]
  ring

theorem flagStateInBasis_pairCost_deficit (ρ₀ ρ₁ : Density I) (U : Mat I)
    (hU : U * Uᴴ = 1) :
    pairCost (flagStateInBasis ρ₀ U hU).val (flagStateInBasis ρ₁ U hU).val =
      ∑ j : I, columnMass (sqrtPSD ρ₀.val * U) (sqrtPSD ρ₁.val * U) j *
        (QuantumProver.BellDiagonalSquashedEntanglement.phi (columnBeta (sqrtPSD ρ₀.val * U) (sqrtPSD ρ₁.val * U) j ^ 2) -
          QuantumProver.BellDiagonalSquashedEntanglement.phi (columnBeta (sqrtPSD ρ₀.val * U) (sqrtPSD ρ₁.val * U) j ^ 2 *
            (1 - Complex.normSq (normalizedColumnOverlap (sqrtPSD ρ₀.val * U)
              (sqrtPSD ρ₁.val * U) j)))) :=
  flagGram_pairCost_deficit _ _ (basis_columnMass_sum ρ₀ ρ₁ U hU)

end QuantumProver.BellDiagonalSquashedEntanglement.FCColumns

noncomputable section
open scoped BigOperators
namespace QuantumProver.BellDiagonalSquashedEntanglement.FCColumns

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem signed_posterior_abs_le (b : ℝ) (z : ℂ) (hb0 : 0 ≤ b) (hz : ‖z‖ ≤ 1) :
    |b * z.re| ≤ b := by
  rw [abs_mul, abs_of_nonneg hb0]
  have hr : |z.re| ≤ 1 := (Complex.abs_re_le_norm z).trans hz
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hr hb0

theorem signed_jointDeficit_le_raw (b : ℝ) (z : ℂ)
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (hz : ‖z‖ ≤ 1) :
    Scalar.jointDeficit b (b * z.re) ≤
      QuantumProver.BellDiagonalSquashedEntanglement.phi (b ^ 2) -
        QuantumProver.BellDiagonalSquashedEntanglement.phi (b ^ 2 * (1 - Complex.normSq z)) := by
  have hb2 : b ^ 2 ≤ 1 := by nlinarith
  have hz2 : Complex.normSq z ≤ 1 := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg z]
  have hr2 := Complex.re_sq_le_normSq z
  have ha0 : 0 ≤ b ^ 2 * (1 - Complex.normSq z) :=
    mul_nonneg (sq_nonneg b) (by linarith)
  have hab : b ^ 2 * (1 - Complex.normSq z) ≤ b ^ 2 - (b * z.re) ^ 2 := by
    have hp := mul_nonneg (sq_nonneg b) (sub_nonneg.mpr hr2)
    nlinarith
  have hc0 : 0 ≤ b ^ 2 - (b * z.re) ^ 2 := ha0.trans hab
  have hc1 : b ^ 2 - (b * z.re) ^ 2 ≤ 1 := by nlinarith [sq_nonneg (b * z.re)]
  have hm := Scalar.formationPhi_monotoneOn
    (show b ^ 2 * (1 - Complex.normSq z) ∈ Set.Icc (0 : ℝ) 1 from ⟨ha0, hab.trans hc1⟩)
    (show b ^ 2 - (b * z.re) ^ 2 ∈ Set.Icc (0 : ℝ) 1 from ⟨hc0, hc1⟩) hab
  change Scalar.formationPhi (b ^ 2) - Scalar.formationPhi (b ^ 2 - (b * z.re) ^ 2) ≤
    Scalar.formationPhi (b ^ 2) - Scalar.formationPhi (b ^ 2 * (1 - Complex.normSq z))
  linarith

theorem fc_flag_jointDeficit_lower (ρ₀ ρ₁ : Density I) (hρ₀ : ρ₀.val.PosDef) :
    Scalar.jointDeficit (rootFidelity ρ₀.val ρ₁.val) (affinity ρ₀.val ρ₁.val) ≤
      pairCost
        (flagStateInBasis ρ₀ (fcBasis ρ₀ ρ₁ : Mat I) (fcBasis_unitary ρ₀ ρ₁)).val
        (flagStateInBasis ρ₁ (fcBasis ρ₀ ρ₁ : Mat I) (fcBasis_unitary ρ₀ ρ₁)).val := by
  let U : Mat I := fcBasis ρ₀ ρ₁
  let A := sqrtPSD ρ₀.val * U
  let B := sqrtPSD ρ₁.val * U
  have hMass : ∑ j : I, columnMass A B j = 1 := basis_columnMass_sum ρ₀ ρ₁ U (fcBasis_unitary ρ₀ ρ₁)
  have hF : ∑ j : I, columnMass A B j * columnBeta A B j =
      rootFidelity ρ₀.val ρ₁.val := fc_mass_beta_moment ρ₀ ρ₁ hρ₀
  have hc : ∑ j : I, columnMass A B j *
      (columnBeta A B j * (normalizedColumnOverlap A B j).re) =
      affinity ρ₀.val ρ₁.val := basis_signed_affinity_moment ρ₀ ρ₁ U (fcBasis_unitary ρ₀ ρ₁)
  have hj := DJointSeries.jointDeficit_jensen Finset.univ
    (columnMass A B) (columnBeta A B)
    (fun j => columnBeta A B j * (normalizedColumnOverlap A B j).re)
    (fun j _ => columnMass_nonneg A B j) hMass
    (fun j _ => columnBeta_nonneg A B j) (fun j _ => columnBeta_le_one A B j)
    (fun j _ => signed_posterior_abs_le _ _ (columnBeta_nonneg A B j)
      (normalizedColumnOverlap_norm_le_one A B j))
  rw [hF, hc] at hj
  have hs : (∑ j : I, columnMass A B j * Scalar.jointDeficit (columnBeta A B j)
      (columnBeta A B j * (normalizedColumnOverlap A B j).re)) ≤
    ∑ j : I, columnMass A B j *
      (QuantumProver.BellDiagonalSquashedEntanglement.phi (columnBeta A B j ^ 2) -
        QuantumProver.BellDiagonalSquashedEntanglement.phi (columnBeta A B j ^ 2 *
          (1 - Complex.normSq (normalizedColumnOverlap A B j)))) := by
    apply Finset.sum_le_sum
    intro j hj
    exact mul_le_mul_of_nonneg_left
      (signed_jointDeficit_le_raw _ _ (columnBeta_nonneg A B j)
        (columnBeta_le_one A B j) (normalizedColumnOverlap_norm_le_one A B j))
      (columnMass_nonneg A B j)
  change Scalar.jointDeficit (rootFidelity ρ₀.val ρ₁.val) (affinity ρ₀.val ρ₁.val) ≤
    pairCost (flagGram A) (flagGram B)
  rw [flagGram_pairCost_deficit A B hMass]
  exact hj.trans hs

end QuantumProver.BellDiagonalSquashedEntanglement.FCColumns

noncomputable section
open Filter Set
open scoped BigOperators Topology ComplexOrder MatrixOrder Matrix Matrix.Norms.L2Operator

namespace QuantumProver.BellDiagonalSquashedEntanglement.SingularLimit

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem tendsto_traceNorm {α : Type*} {l : Filter α} {X : α → Mat I} {A : Mat I}
    (hX : Tendsto X l (𝓝 A)) :
    Tendsto (fun x => traceNorm (X x)) l (𝓝 (traceNorm A)) := by
  have hstar : Tendsto (fun x => (X x)ᴴ) l (𝓝 Aᴴ) := by
    exact (show Continuous (fun M : Mat I => Mᴴ) by fun_prop).continuousAt.tendsto.comp hX
  have hr := QuantumProver.MatrixAnalysis.Affinity.tendsto_sqrtPSD (hstar.mul hX)
    (Eventually.of_forall (fun x => Matrix.posSemidef_conjTranspose_mul_self (X x)))
    (Matrix.posSemidef_conjTranspose_mul_self A)
  exact (show Continuous (fun M : Mat I => M.trace.re) by fun_prop).continuousAt.tendsto.comp hr

theorem tendsto_rootFidelity {α : Type*} {l : Filter α}
    {X Y : α → Mat I} {A B : Mat I}
    (hX : Tendsto X l (𝓝 A)) (hY : Tendsto Y l (𝓝 B))
    (hPX : ∀ᶠ x in l, (X x).PosSemidef) (hPY : ∀ᶠ x in l, (Y x).PosSemidef)
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    Tendsto (fun x => rootFidelity (X x) (Y x)) l (𝓝 (rootFidelity A B)) := by
  exact tendsto_traceNorm ((QuantumProver.MatrixAnalysis.Affinity.tendsto_sqrtPSD hX hPX hA).mul
    (QuantumProver.MatrixAnalysis.Affinity.tendsto_sqrtPSD hY hPY hB))

theorem tendsto_affinity {α : Type*} {l : Filter α}
    {X Y : α → Mat I} {A B : Mat I}
    (hX : Tendsto X l (𝓝 A)) (hY : Tendsto Y l (𝓝 B))
    (hPX : ∀ᶠ x in l, (X x).PosSemidef) (hPY : ∀ᶠ x in l, (Y x).PosSemidef)
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    Tendsto (fun x => affinity (X x) (Y x)) l (𝓝 (affinity A B)) :=
  QuantumProver.MatrixAnalysis.Affinity.tendsto_affinity hX hY hPX hPY hA hB

theorem tendsto_entropyBits {α : Type*} {l : Filter α} {X : α → Mat I} {A : Mat I}
    (hX : Tendsto X l (𝓝 A)) (hHerm : ∀ᶠ x in l, (X x).IsHermitian)
    (hA : A.IsHermitian) :
    Tendsto (fun x => entropyBits (X x)) l (𝓝 (entropyBits A)) := by
  exact (QuantumProver.SuperchannelDiscrimination.EntropyContinuity.tendsto_entropyTrace hX hHerm hA).neg.div_const
    (Real.log 2)

theorem tendsto_pairCost {α : Type*} {l : Filter α}
    {X Y : α → Mat I} {A B : Mat I}
    (hX : Tendsto X l (𝓝 A)) (hY : Tendsto Y l (𝓝 B))
    (hPX : ∀ᶠ x in l, (X x).PosSemidef) (hPY : ∀ᶠ x in l, (Y x).PosSemidef)
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    Tendsto (fun x => pairCost (X x) (Y x)) l (𝓝 (pairCost A B)) := by
  have hAvg : Tendsto (fun x => (1 / 2 : ℝ) • (X x + Y x)) l
      (𝓝 ((1 / 2 : ℝ) • (A + B))) := tendsto_const_nhds.smul (hX.add hY)
  have hAvgHerm : ∀ᶠ x in l, ((1 / 2 : ℝ) • (X x + Y x)).IsHermitian := by
    filter_upwards [hPX, hPY] with x hx hy
    exact (((hx.add hy).smul (by norm_num : (0 : ℝ) ≤ 1 / 2)).isHermitian)
  have hAvgA := ((hA.add hB).smul (by norm_num : (0 : ℝ) ≤ 1 / 2)).isHermitian
  exact tendsto_const_nhds.sub ((tendsto_entropyBits hAvg hAvgHerm hAvgA).sub
    (((tendsto_entropyBits hX (hPX.mono fun _ h => h.isHermitian) hA.isHermitian).add
      (tendsto_entropyBits hY (hPY.mono fun _ h => h.isHermitian) hB.isHermitian)).div_const 2))

def edgeLowerExpression (A B : Mat I) : ℝ :=
  Scalar.jointDeficit (rootFidelity A B) (affinity A B) +
    (rootFidelity A B - Real.sqrt (rootFidelity A B * affinity A B)) ^ 2 / (4 * Real.log 2)

theorem tendsto_edgeLowerExpression {α : Type*} {l : Filter α}
    {X Y : α → Mat I} {A B : Mat I}
    (hX : Tendsto X l (𝓝 A)) (hY : Tendsto Y l (𝓝 B))
    (hPX : ∀ᶠ x in l, (X x).PosSemidef) (hPY : ∀ᶠ x in l, (Y x).PosSemidef)
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    Tendsto (fun x => edgeLowerExpression (X x) (Y x)) l (𝓝 (edgeLowerExpression A B)) := by
  have hF := tendsto_rootFidelity hX hY hPX hPY hA hB
  have hc := tendsto_affinity hX hY hPX hPY hA hB
  have hD := Scalar.jointDeficit_continuous.continuousAt.tendsto.comp (hF.prodMk_nhds hc)
  have hroot := Real.continuous_sqrt.continuousAt.tendsto.comp (hF.mul hc)
  exact hD.add (((hF.sub hroot).pow 2).div_const (4 * Real.log 2))

def maxMixed : Mat I := (1 / (Fintype.card I : ℝ)) • (1 : Mat I)

theorem maxMixed_posSemidef : (maxMixed (I := I)).PosSemidef :=
  Matrix.PosSemidef.one.smul (by positivity)

theorem maxMixed_posDef [Nonempty I] : (maxMixed (I := I)).PosDef :=
  Matrix.PosDef.one.smul (by exact one_div_pos.mpr (Nat.cast_pos.mpr Fintype.card_pos))

theorem maxMixed_trace [Nonempty I] : (maxMixed (I := I)).trace = 1 := by
  have hc : (Fintype.card I : ℝ) ≠ 0 := (Nat.cast_pos.mpr Fintype.card_pos).ne'
  unfold maxMixed
  have hcC : (Fintype.card I : ℂ) ≠ 0 := by exact_mod_cast hc
  simp only [Matrix.trace_smul, Matrix.trace_one, Complex.real_smul,
    Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_natCast]
  field_simp [hcC]

theorem maxMixed_isDensity [Nonempty I] : IsDensity (maxMixed (I := I)) :=
  ⟨maxMixed_posSemidef, maxMixed_trace⟩

def regularizedStateMatrix (A : Mat I) (e : ℝ) : Mat I :=
  QuantumProver.SuperchannelDiscrimination.EntropyContinuity.regularizedNull A maxMixed e

theorem regularizedStateMatrix_isDensity [Nonempty I] (A : Density I) (e : ℝ)
    (he0 : 0 ≤ e) (he1 : e ≤ 1) : IsDensity (regularizedStateMatrix A.val e) := by
  refine ⟨QuantumProver.SuperchannelDiscrimination.EntropyContinuity.regularizedNull_posSemidef
    A.property.1 maxMixed_posSemidef he0 he1, ?_⟩
  simp only [regularizedStateMatrix, QuantumProver.SuperchannelDiscrimination.EntropyContinuity.regularizedNull,
    Matrix.trace_add, Matrix.trace_smul, A.property.2, maxMixed_trace,
    ← add_smul, sub_add_cancel, one_smul]

theorem regularizedStateMatrix_posDef [Nonempty I] {A : Mat I} (hA : A.PosSemidef)
    (e : ℝ) (he0 : 0 < e) (he1 : e ≤ 1) : (regularizedStateMatrix A e).PosDef :=
  QuantumProver.SuperchannelDiscrimination.EntropyContinuity.regularizedNull_posDef hA maxMixed_posDef he0 he1

def faithfulRegularizedDensity [Nonempty I] (A : Density I) (e : ℝ)
    (he0 : 0 ≤ e) (he1 : e ≤ 1) : Density I :=
  ⟨regularizedStateMatrix A.val e, regularizedStateMatrix_isDensity A e he0 he1⟩

theorem regularizedStateMatrix_tendsto (A : Mat I) :
    Tendsto (regularizedStateMatrix A) (𝓝[>] (0 : ℝ)) (𝓝 A) :=
  (QuantumProver.SuperchannelDiscrimination.EntropyContinuity.regularizedNull_tendsto A maxMixed).mono_left
    nhdsWithin_le_nhds

theorem eventually_regularizedStateMatrix_posSemidef {A : Mat I} (hA : A.PosSemidef) :
    ∀ᶠ e : ℝ in 𝓝[>] (0 : ℝ), (regularizedStateMatrix A e).PosSemidef :=
  QuantumProver.SuperchannelDiscrimination.EntropyContinuity.eventually_regularizedNull_posSemidef
    hA maxMixed_posSemidef

theorem eventually_regularizedStateMatrix_posDef [Nonempty I] {A : Mat I} (hA : A.PosSemidef) :
    ∀ᶠ e : ℝ in 𝓝[>] (0 : ℝ), (regularizedStateMatrix A e).PosDef :=
  QuantumProver.SuperchannelDiscrimination.EntropyContinuity.eventually_regularizedNull_posDef hA maxMixed_posDef

theorem regularizedStateMatrix_pairCost_tendsto {A B : Mat I}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    Tendsto (fun e => pairCost (regularizedStateMatrix A e) (regularizedStateMatrix B e))
      (𝓝[>] (0 : ℝ)) (𝓝 (pairCost A B)) :=
  tendsto_pairCost (regularizedStateMatrix_tendsto A) (regularizedStateMatrix_tendsto B)
    (eventually_regularizedStateMatrix_posSemidef hA) (eventually_regularizedStateMatrix_posSemidef hB) hA hB

theorem regularizedStateMatrix_edgeLowerExpression_tendsto {A B : Mat I}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    Tendsto (fun e => edgeLowerExpression (regularizedStateMatrix A e) (regularizedStateMatrix B e))
      (𝓝[>] (0 : ℝ)) (𝓝 (edgeLowerExpression A B)) :=
  tendsto_edgeLowerExpression (regularizedStateMatrix_tendsto A) (regularizedStateMatrix_tendsto B)
    (eventually_regularizedStateMatrix_posSemidef hA) (eventually_regularizedStateMatrix_posSemidef hB) hA hB

theorem affinity_le_rootFidelity (A B : Mat I) : affinity A B ≤ rootFidelity A B := by
  have h := Geometry.norm_trace_unitary_mul_le_absolute_trace (sqrtPSD A * sqrtPSD B)
    (1 : Mat I) (Matrix.unitaryGroup I ℂ).one_mem
  rw [Matrix.one_mul] at h
  exact (Complex.re_le_norm _).trans h

theorem affinity_nonnegative (A B : Mat I) : 0 ≤ affinity A B :=
  QuantumProver.MatrixAnalysis.Affinity.affinity_nonneg A B

theorem regularizedStateMatrix_affinity_tendsto {A B : Mat I}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    Tendsto (fun e => affinity (regularizedStateMatrix A e) (regularizedStateMatrix B e))
      (𝓝[>] (0 : ℝ)) (𝓝 (affinity A B)) :=
  tendsto_affinity (regularizedStateMatrix_tendsto A) (regularizedStateMatrix_tendsto B)
    (eventually_regularizedStateMatrix_posSemidef hA) (eventually_regularizedStateMatrix_posSemidef hB) hA hB

theorem regularizedStateMatrix_rootFidelity_tendsto {A B : Mat I}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    Tendsto (fun e => rootFidelity (regularizedStateMatrix A e) (regularizedStateMatrix B e))
      (𝓝[>] (0 : ℝ)) (𝓝 (rootFidelity A B)) :=
  tendsto_rootFidelity (regularizedStateMatrix_tendsto A) (regularizedStateMatrix_tendsto B)
    (eventually_regularizedStateMatrix_posSemidef hA) (eventually_regularizedStateMatrix_posSemidef hB) hA hB

theorem eventually_regularizedStateMatrix_affinity_positive {A B : Mat I}
    (hA : A.PosSemidef) (hB : B.PosSemidef) (hc : 0 < affinity A B) :
    ∀ᶠ e : ℝ in 𝓝[>] (0 : ℝ),
      0 < affinity (regularizedStateMatrix A e) (regularizedStateMatrix B e) :=
  (regularizedStateMatrix_affinity_tendsto hA hB).eventually (Ioi_mem_nhds hc)

end QuantumProver.BellDiagonalSquashedEntanglement.SingularLimit

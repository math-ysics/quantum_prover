import QuantumProver.InformationTheory.DepolarizingSquashedEntanglement.Fixed16Flags
import QuantumProver.InformationTheory.ConditionalEntropy.ConditionalRange
import QuantumProver.InformationTheory.DepolarizingSquashedEntanglement.EntropyExpansion

set_option autoImplicit false

noncomputable section

open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder Matrix Kronecker
  Matrix.Norms.L2Operator ContinuousFunctionalCalculus

namespace QuantumProver.DepolarizingSquashedEntanglement.Fixed16FlagEntropy

open Identities Fixed16Flags

def uniformFlag : QMatrix (Fin 4) := Matrix.diagonal (fun _ => (1 / 4 : ℂ))

theorem uniformFlag_positive : uniformFlag.PosSemidef := by
  apply Matrix.PosSemidef.diagonal
  intro j
  norm_num [Complex.le_def]

theorem uniformFlag_trace : Matrix.trace uniformFlag = 1 := by
  norm_num [uniformFlag, Matrix.trace, Matrix.diag, Fin.sum_univ_succ]

def controlledFlagLift {I E : Type*} [DecidableEq E]
    (U : Fin 4 → QMatrix I) : Matrix (I × (Fin 4 × E)) (Fin 4 × (I × E)) ℂ :=
  fun x y => if x.2.1 = y.1 ∧ x.2.2 = y.2.2 then U y.1 x.1 y.2.1 else 0

theorem controlledFlagLift_gram {I E : Type*} [Fintype I] [Fintype E]
    [DecidableEq I] [DecidableEq E] (U : Fin 4 → QMatrix I)
    (hU : ∀ j, IsIsometry (U j)) :
    (controlledFlagLift (E := E) U)ᴴ * controlledFlagLift (E := E) U = 1 := by
  ext x y
  rcases x with ⟨j, ⟨i, e⟩⟩
  rcases y with ⟨l, ⟨k, f⟩⟩
  by_cases hj : j = l
  · subst l
    by_cases he : e = f
    · subst f
      have h := congrArg (fun M : QMatrix I => M i k) (hU j)
      simpa [controlledFlagLift, Matrix.mul_apply, Matrix.conjTranspose_apply,
        Matrix.one_apply, Fintype.sum_prod_type, ite_and, apply_ite, mul_ite, ite_mul] using h
    · simp [controlledFlagLift, Matrix.mul_apply, Matrix.conjTranspose_apply,
        Matrix.one_apply, Fintype.sum_prod_type, ite_and, apply_ite, mul_ite, ite_mul, he, Ne.symm he]
  · simp [controlledFlagLift, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.one_apply, Fintype.sum_prod_type, ite_and, apply_ite, ite_and, apply_ite, mul_ite, ite_mul, hj, Ne.symm hj]

def controlledFlagState {I E : Type*} [Fintype I] [Fintype E] [DecidableEq E]
    (U : Fin 4 → QMatrix I) (ρ : QMatrix (I × E)) : QMatrix (I × (Fin 4 × E)) :=
  controlledFlagLift (E := E) U * (uniformFlag ⊗ₖ ρ) *
    (controlledFlagLift (E := E) U)ᴴ

theorem controlledFlagState_apply {I E : Type*} [Fintype I] [Fintype E]
    [DecidableEq I] [DecidableEq E] (U : Fin 4 → QMatrix I)
    (ρ : QMatrix (I × E)) (i k : I) (e f : E) (j l : Fin 4) :
    controlledFlagState U ρ (i, (j, e)) (k, (l, f)) =
      if j = l then (1 / 4 : ℂ) *
        ((U j ⊗ₖ (1 : QMatrix E)) * ρ * (U j ⊗ₖ (1 : QMatrix E))ᴴ)
          (i, e) (k, f) else 0 := by
  by_cases hj : j = l
  · subst l
    simp [controlledFlagState, controlledFlagLift, uniformFlag,
      Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.kroneckerMap_apply,
      Matrix.diagonal_apply, Matrix.one_apply, Fintype.sum_prod_type,
      ite_and, apply_ite, mul_ite, ite_mul, Finset.mul_sum, Finset.sum_mul, mul_assoc, mul_left_comm]
  · simp [controlledFlagState, controlledFlagLift, uniformFlag,
      Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.kroneckerMap_apply,
      Matrix.diagonal_apply, Matrix.one_apply, Fintype.sum_prod_type,
      ite_and, apply_ite, mul_ite, ite_mul, hj, Ne.symm hj]

theorem entropyNat_tensor {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] {A : QMatrix I} {B : QMatrix J}
    (hA : A.PosSemidef) (hAT : Matrix.trace A = 1)
    (hB : B.PosSemidef) (hBT : Matrix.trace B = 1) :
    entropyNat (A ⊗ₖ B) = entropyNat A + entropyNat B := by
  have h := QuantumProver.SuperchannelDiscrimination.TensorEntropy.entropyBits_kronecker
    ⟨hA, hAT⟩ ⟨hB, hBT⟩
  rw [QuantumProver.ConditionalEntropy.ConditionalRange.entropyBits_eq_isotropicEntropy_div_log_two,
    QuantumProver.ConditionalEntropy.ConditionalRange.entropyBits_eq_isotropicEntropy_div_log_two,
    QuantumProver.ConditionalEntropy.ConditionalRange.entropyBits_eq_isotropicEntropy_div_log_two] at h
  change entropyNat (A ⊗ₖ B) / Real.log 2 =
    entropyNat A / Real.log 2 + entropyNat B / Real.log 2 at h
  have hl : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  field_simp [hl] at h
  exact h

theorem controlledFlagState_entropy {I E : Type*} [Fintype I] [Fintype E]
    [DecidableEq I] [DecidableEq E] (U : Fin 4 → QMatrix I)
    (hU : ∀ j, IsIsometry (U j)) {ρ : QMatrix (I × E)}
    (hρ : ρ.PosSemidef) (hρT : Matrix.trace ρ = 1) :
    entropyNat (controlledFlagState U ρ) = entropyNat uniformFlag + entropyNat ρ := by
  have hV := controlledFlagLift_gram (E := E) U hU
  have hp := uniformFlag_positive.kronecker hρ
  change (Matrix.trace (cfc Real.negMulLog
    (QuantumProver.SuperchannelDiscrimination.ZeroExtension.extend (controlledFlagLift (E := E) U)
      (uniformFlag ⊗ₖ ρ)))).re = _
  rw [QuantumProver.SuperchannelDiscrimination.ZeroExtension.cfc_extend (controlledFlagLift (E := E) U)
    hV Real.negMulLog Real.negMulLog_zero hp.1,
    QuantumProver.SuperchannelDiscrimination.ZeroExtension.extend_trace (controlledFlagLift (E := E) U) hV]
  exact entropyNat_tensor uniformFlag_positive uniformFlag_trace hρ hρT

theorem tetraBranchUnitary_gram (j : Fin 4) :
    (Fixed16.tetraBranchUnitary j)ᴴ * Fixed16.tetraBranchUnitary j = 1 := by
  calc
    _ = Fixed16.tetraUnitaryᴴ * (pauli j)ᴴ * pauli j * Fixed16.tetraUnitary := by
      simp only [Fixed16.tetraBranchUnitary, Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = 1 := by
      rw [Matrix.mul_assoc Fixed16.tetraUnitaryᴴ, Fixed16.pauli_gram,
        Matrix.mul_one, Fixed16.tetraUnitary_gram]

theorem omegaDensity_ABE_controlled (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    partialTraceRight (omegaDensity r hr hr1).matrix =
      controlledFlagState Fixed16.tetraBranchMatrix
        (partialTraceRight (seedDensity r hr hr1).matrix) := by
  ext x y
  rcases x with ⟨ab, ⟨j, e⟩⟩
  rcases y with ⟨cd, ⟨l, f⟩⟩
  rw [omegaDensity_ABE_apply, controlledFlagState_apply,
    seedBranchKet_pureDensity, seedBranchLift, partialTraceRight_tensor_sandwich]
  rfl

theorem omegaDensity_ABE_entropy (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    entropyNat (partialTraceRight (omegaDensity r hr hr1).matrix) =
      entropyNat uniformFlag + entropyNat (partialTraceRight (seedDensity r hr hr1).matrix) := by
  rw [omegaDensity_ABE_controlled]
  apply controlledFlagState_entropy Fixed16.tetraBranchMatrix
    Fixed16.tetraBranchMatrix_gram
  · exact partialTraceRight_positive (seedDensity r hr hr1).positive
  · rw [partialTraceRight_trace, (seedDensity r hr hr1).trace_one]

def middleOrder (A B E : Type*) : (A × E) × B ≃ (A × B) × E where
  toFun := fun x => ((x.1.1, x.2), x.1.2)
  invFun := fun x => ((x.1.1, x.2), x.1.2)
  left_inv := by intro x; rfl
  right_inv := by intro x; rfl

def firstOrder (A B E : Type*) : (B × E) × A ≃ (A × B) × E where
  toFun := fun x => ((x.2, x.1.1), x.1.2)
  invFun := fun x => ((x.1.2, x.2), x.1.1)
  left_inv := by intro x; rfl
  right_inv := by intro x; rfl

theorem traceMiddle_localPair {A B E : Type*}
    [Fintype A] [Fintype B] [Fintype E]
    [DecidableEq A] [DecidableEq B] [DecidableEq E]
    (U : QMatrix A) (W : QMatrix B) (hW : IsIsometry W)
    (ρ : QMatrix ((A × B) × E)) :
    traceMiddle (((U ⊗ₖ W) ⊗ₖ (1 : QMatrix E)) * ρ *
      ((U ⊗ₖ W) ⊗ₖ (1 : QMatrix E))ᴴ) =
    (U ⊗ₖ (1 : QMatrix E)) * traceMiddle ρ * (U ⊗ₖ (1 : QMatrix E))ᴴ := by
  let e := middleOrder A B E
  let Q := (U ⊗ₖ W) ⊗ₖ (1 : QMatrix E)
  have hs : Q.submatrix e e = (U ⊗ₖ (1 : QMatrix E)) ⊗ₖ W := by
    ext x y
    simp [Q, e, middleOrder, Matrix.submatrix, Matrix.kroneckerMap_apply]
    ring
  have hc : (Q * ρ * Qᴴ).submatrix e e =
      ((U ⊗ₖ (1 : QMatrix E)) ⊗ₖ W) * (ρ.submatrix e e) *
        ((U ⊗ₖ (1 : QMatrix E)) ⊗ₖ W)ᴴ := by
    rw [← Matrix.submatrix_mul_equiv _ _ e e e,
      ← Matrix.submatrix_mul_equiv _ _ e e e, ← Matrix.conjTranspose_submatrix, hs]
  change partialTraceRight ((Q * ρ * Qᴴ).submatrix e e) =
    (U ⊗ₖ (1 : QMatrix E)) * partialTraceRight (ρ.submatrix e e) *
      (U ⊗ₖ (1 : QMatrix E))ᴴ
  rw [hc]
  exact partialTraceRight_localUnitary _ W hW _

theorem traceFirst_localPair {A B E : Type*}
    [Fintype A] [Fintype B] [Fintype E]
    [DecidableEq A] [DecidableEq B] [DecidableEq E]
    (U : QMatrix A) (W : QMatrix B) (hU : IsIsometry U)
    (ρ : QMatrix ((A × B) × E)) :
    traceFirst (((U ⊗ₖ W) ⊗ₖ (1 : QMatrix E)) * ρ *
      ((U ⊗ₖ W) ⊗ₖ (1 : QMatrix E))ᴴ) =
    (W ⊗ₖ (1 : QMatrix E)) * traceFirst ρ * (W ⊗ₖ (1 : QMatrix E))ᴴ := by
  let e := firstOrder A B E
  let Q := (U ⊗ₖ W) ⊗ₖ (1 : QMatrix E)
  have hs : Q.submatrix e e = (W ⊗ₖ (1 : QMatrix E)) ⊗ₖ U := by
    ext x y
    simp [Q, e, firstOrder, Matrix.submatrix, Matrix.kroneckerMap_apply]
    ring
  have hc : (Q * ρ * Qᴴ).submatrix e e =
      ((W ⊗ₖ (1 : QMatrix E)) ⊗ₖ U) * (ρ.submatrix e e) *
        ((W ⊗ₖ (1 : QMatrix E)) ⊗ₖ U)ᴴ := by
    rw [← Matrix.submatrix_mul_equiv _ _ e e e,
      ← Matrix.submatrix_mul_equiv _ _ e e e, ← Matrix.conjTranspose_submatrix, hs]
  change partialTraceRight ((Q * ρ * Qᴴ).submatrix e e) =
    (W ⊗ₖ (1 : QMatrix E)) * partialTraceRight (ρ.submatrix e e) *
      (W ⊗ₖ (1 : QMatrix E))ᴴ
  rw [hc]
  exact partialTraceRight_localUnitary _ U hU _

def conjugateBranch (j : Fin 4) : QMatrix Qubit :=
  (Fixed16.tetraBranchUnitary j).map (starRingEnd ℂ)

theorem conjugateBranch_gram (j : Fin 4) : IsIsometry (conjugateBranch j) :=
  Fixed16.conjugate_gram (Fixed16.tetraBranchUnitary j) (tetraBranchUnitary_gram j)

theorem seedBranchKet_ABE_marginal (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1) (j : Fin 4) :
    partialTraceRight (pureDensity (seedBranchKet r j)) =
      (Fixed16.tetraBranchMatrix j ⊗ₖ (1 : QMatrix Fixed16.CoreIndex)) *
        partialTraceRight (seedDensity r hr hr1).matrix *
          (Fixed16.tetraBranchMatrix j ⊗ₖ (1 : QMatrix Fixed16.CoreIndex))ᴴ := by
  rw [seedBranchKet_pureDensity, seedBranchLift, partialTraceRight_tensor_sandwich]
  rfl

theorem omegaDensity_AE_controlled (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    traceMiddle (partialTraceRight (omegaDensity r hr hr1).matrix) =
      controlledFlagState conjugateBranch
        (traceMiddle (partialTraceRight (seedDensity r hr hr1).matrix)) := by
  ext x y
  rcases x with ⟨a, ⟨j, e⟩⟩
  rcases y with ⟨c, ⟨l, f⟩⟩
  rw [controlledFlagState_apply]
  change (∑ b : Qubit, partialTraceRight (omegaDensity r hr hr1).matrix
    ((a, b), (j, e)) ((c, b), (l, f))) = _
  simp_rw [omegaDensity_ABE_apply r hr hr1]
  by_cases h : j = l
  · subst l
    simp only [ite_true, ← Finset.mul_sum]
    change (1 / 4 : ℂ) * traceMiddle (partialTraceRight
      (pureDensity (seedBranchKet r j))) (a, e) (c, f) = _
    rw [seedBranchKet_ABE_marginal r hr hr1, Fixed16.tetraBranchMatrix_eq,
      traceMiddle_localPair _ _ (tetraBranchUnitary_gram j)]
    rfl
  · simp [h]

theorem omegaDensity_BE_controlled (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    traceFirst (partialTraceRight (omegaDensity r hr hr1).matrix) =
      controlledFlagState Fixed16.tetraBranchUnitary
        (traceFirst (partialTraceRight (seedDensity r hr hr1).matrix)) := by
  ext x y
  rcases x with ⟨b, ⟨j, e⟩⟩
  rcases y with ⟨d, ⟨l, f⟩⟩
  rw [controlledFlagState_apply]
  change (∑ a : Qubit, partialTraceRight (omegaDensity r hr hr1).matrix
    ((a, b), (j, e)) ((a, d), (l, f))) = _
  simp_rw [omegaDensity_ABE_apply r hr hr1]
  by_cases h : j = l
  · subst l
    simp only [ite_true, ← Finset.mul_sum]
    change (1 / 4 : ℂ) * traceFirst (partialTraceRight
      (pureDensity (seedBranchKet r j))) (b, e) (d, f) = _
    rw [seedBranchKet_ABE_marginal r hr hr1, Fixed16.tetraBranchMatrix_eq]
    exact congrArg (fun M : QMatrix (Qubit × Fixed16.CoreIndex) =>
      (1 / 4 : ℂ) * M (b, e) (d, f))
      (traceFirst_localPair ((Fixed16.tetraBranchUnitary j).map (starRingEnd ℂ))
        (Fixed16.tetraBranchUnitary j)
        (Fixed16.conjugate_gram _ (tetraBranchUnitary_gram j))
        (partialTraceRight (seedDensity r hr hr1).matrix))
  · simp [h]

theorem omegaDensity_E_tensor (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    partialTraceLeft (partialTraceRight (omegaDensity r hr hr1).matrix) =
      uniformFlag ⊗ₖ partialTraceLeft (partialTraceRight (seedDensity r hr hr1).matrix) := by
  ext x y
  rcases x with ⟨j, e⟩
  rcases y with ⟨l, f⟩
  change (∑ ab : Fixed16.CoreIndex, partialTraceRight (omegaDensity r hr hr1).matrix
    (ab, (j, e)) (ab, (l, f))) = _
  simp_rw [omegaDensity_ABE_apply r hr hr1]
  by_cases h : j = l
  · subst l
    simp only [ite_true, ← Finset.mul_sum]
    change (1 / 4 : ℂ) * partialTraceLeft (partialTraceRight
      (pureDensity (seedBranchKet r j))) e f = _
    rw [seedBranchKet_ABE_marginal r hr hr1,
      partialTraceLeft_localUnitary _ _ (Fixed16.tetraBranchMatrix_gram j)]
    simp [uniformFlag, Matrix.kroneckerMap_apply]
  · simp [h, uniformFlag, Matrix.kroneckerMap_apply]

theorem traceMiddle_trace {A B E : Type*} [Fintype A] [Fintype B] [Fintype E]
    (ρ : QMatrix ((A × B) × E)) : Matrix.trace (traceMiddle ρ) = Matrix.trace ρ := by
  simp only [Matrix.trace, Matrix.diag, traceMiddle, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a ha
  exact Finset.sum_comm

theorem traceFirst_trace {A B E : Type*} [Fintype A] [Fintype B] [Fintype E]
    (ρ : QMatrix ((A × B) × E)) : Matrix.trace (traceFirst ρ) = Matrix.trace ρ := by
  simp only [Matrix.trace, Matrix.diag, traceFirst, Fintype.sum_prod_type]
  calc
    _ = ∑ b : B, ∑ a : A, ∑ e : E, ρ ((a, b), e) ((a, b), e) := by
      apply Finset.sum_congr rfl
      intro b hb
      exact Finset.sum_comm
    _ = _ := Finset.sum_comm

theorem traceMiddle_positive {A B E : Type*} [Fintype A] [Fintype B] [Fintype E]
    {ρ : QMatrix ((A × B) × E)} (hρ : ρ.PosSemidef) : (traceMiddle ρ).PosSemidef := by
  exact partialTraceRight_positive (hρ.submatrix (middleOrder A B E))

theorem traceFirst_positive {A B E : Type*} [Fintype A] [Fintype B] [Fintype E]
    {ρ : QMatrix ((A × B) × E)} (hρ : ρ.PosSemidef) : (traceFirst ρ).PosSemidef := by
  exact partialTraceRight_positive (hρ.submatrix (firstOrder A B E))

theorem omegaDensity_AE_entropy (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    entropyNat (traceMiddle (partialTraceRight (omegaDensity r hr hr1).matrix)) =
      entropyNat uniformFlag + entropyNat (traceMiddle (partialTraceRight (seedDensity r hr hr1).matrix)) := by
  rw [omegaDensity_AE_controlled]
  apply controlledFlagState_entropy conjugateBranch conjugateBranch_gram
  · exact traceMiddle_positive (partialTraceRight_positive (seedDensity r hr hr1).positive)
  · rw [traceMiddle_trace, partialTraceRight_trace, (seedDensity r hr hr1).trace_one]

theorem omegaDensity_BE_entropy (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    entropyNat (traceFirst (partialTraceRight (omegaDensity r hr hr1).matrix)) =
      entropyNat uniformFlag + entropyNat (traceFirst (partialTraceRight (seedDensity r hr hr1).matrix)) := by
  rw [omegaDensity_BE_controlled]
  apply controlledFlagState_entropy Fixed16.tetraBranchUnitary tetraBranchUnitary_gram
  · exact traceFirst_positive (partialTraceRight_positive (seedDensity r hr hr1).positive)
  · rw [traceFirst_trace, partialTraceRight_trace, (seedDensity r hr hr1).trace_one]

theorem omegaDensity_E_entropy (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    entropyNat (partialTraceLeft (partialTraceRight (omegaDensity r hr hr1).matrix)) =
      entropyNat uniformFlag + entropyNat (partialTraceLeft (partialTraceRight (seedDensity r hr hr1).matrix)) := by
  rw [omegaDensity_E_tensor]
  apply entropyNat_tensor uniformFlag_positive uniformFlag_trace
  · exact partialTraceLeft_positive (partialTraceRight_positive (seedDensity r hr hr1).positive)
  · rw [partialTraceLeft_trace, partialTraceRight_trace, (seedDensity r hr hr1).trace_one]

theorem omega_cmiNat_eq_seed (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    cmiNat (partialTraceRight (omegaDensity r hr hr1).matrix) =
      cmiNat (partialTraceRight (seedDensity r hr hr1).matrix) := by
  unfold cmiNat
  rw [omegaDensity_AE_entropy, omegaDensity_BE_entropy,
    omegaDensity_E_entropy, omegaDensity_ABE_entropy]
  ring

theorem omega_half_cmiBits_eq_H (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    cmiBits (partialTraceRight (omegaDensity r hr hr1).matrix) / 2 =
      matrixCoreEntropyCombination r hr hr1 / (2 * Real.log 2) := by
  unfold cmiBits
  rw [omega_cmiNat_eq_seed, seed_cmiNat_eq_matrixCoreEntropyCombination,
    div_div, mul_comm]

theorem omega_boundary_half_cmiBits_eq_H (δ : ℝ)
    (hδ : 0 ≤ δ) (hmax : δ ≤ 21 / 512) :
    cmiBits (partialTraceRight (omegaDensity (Scalar.boundaryR δ)
      (Scalar.boundaryR_nonneg hδ)
      ((Scalar.boundaryR_le_quarter hδ hmax).trans (by norm_num))).matrix) / 2 =
      matrixCoreBoundaryEntropy δ hδ hmax := omega_half_cmiBits_eq_H _ _ _

def omegaHalfCMIBits (r : ℝ) : ℝ :=
  cmiBits (partialTraceRight (pureDensity (omegaKet r))) / 2

def boundaryOmegaHalfCMIBits (δ : ℝ) : ℝ := omegaHalfCMIBits (Scalar.boundaryR δ)

theorem boundaryOmegaHalfCMIBits_eq_matrix (δ : ℝ)
    (hδ : 0 ≤ δ) (hmax : δ ≤ 21 / 512) :
    boundaryOmegaHalfCMIBits δ = matrixCoreBoundaryEntropy δ hδ hmax :=
  omega_boundary_half_cmiBits_eq_H δ hδ hmax

theorem boundaryOmegaHalfCMIBits_uniform_remainder :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (δ : ℝ), 0 ≤ δ → δ ≤ 21 / 512 →
      |boundaryOmegaHalfCMIBits δ -
        (3200 * Scalar.boundaryKappa / (81 * Real.log 2)) * δ ^ 2| ≤ C * δ ^ 3 := by
  obtain ⟨C, hC, hb⟩ := matrixCoreBoundaryEntropy_uniform_remainder
  refine ⟨C, hC, ?_⟩
  intro δ hδ hmax
  rw [boundaryOmegaHalfCMIBits_eq_matrix δ hδ hmax]
  exact hb δ hδ hmax

theorem boundaryOmegaHalfCMIBits_quadratic_upper :
    ∃ C : ℝ, 0 < C ∧ ∀ (δ : ℝ), 0 ≤ δ → δ ≤ 21 / 512 →
      boundaryOmegaHalfCMIBits δ ≤ C * δ ^ 2 := by
  obtain ⟨C, hC, hb⟩ := matrixCoreBoundaryEntropy_quadratic_upper
  refine ⟨C, hC, ?_⟩
  intro δ hδ hmax
  rw [boundaryOmegaHalfCMIBits_eq_matrix δ hδ hmax]
  exact hb δ hδ hmax

def identityEnvironmentImage (x y : ℝ) : QMatrix Fixed16.CoreIndex :=
  Matrix.diagonal (fun p =>
    (((if p.1 = 0 then 1 + x else 1 - x) *
      (if p.2 = 0 then 1 + y else 1 - y) : ℝ) : ℂ))

theorem tensorEnvironment_identity {x y : ℝ}
    (hx : 0 ≤ x) (hx1 : x ≤ 1) (hy : 0 ≤ y) (hy1 : y ≤ 1) :
    tensorEnvironment x y (1 : QMatrix Fixed16.CoreIndex) = identityEnvironmentImage x y := by
  have hxs : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx
  have hys : Real.sqrt y ^ 2 = y := Real.sq_sqrt hy
  have hxc : Real.sqrt (1 - x) ^ 2 = 1 - x := Real.sq_sqrt (sub_nonneg.mpr hx1)
  have hyc : Real.sqrt (1 - y) ^ 2 = 1 - y := Real.sq_sqrt (sub_nonneg.mpr hy1)
  ext p q
  rcases p with ⟨a, b⟩
  rcases q with ⟨c, d⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    apply Complex.ext <;>
    norm_num [tensorEnvironment, tensorEnvironmentKraus, Fixed16.environmentKraus,
      Fixed16.weakIsometry, identityEnvironmentImage, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Matrix.kroneckerMap_apply, Matrix.one_apply,
      Matrix.diagonal_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
      Complex.mul_re, Complex.mul_im] <;> try ring_nf
  all_goals norm_num [hxs, hys, hxc, hyc]
  all_goals ring

theorem identityEnvironmentImage_support_lower {x y : ℝ}
    (hx : 0 ≤ x) (hxq : x ≤ 1 / 4) (hy : 0 ≤ y) (hyq : y ≤ 1 / 4) :
    ((1 / 32 : ℝ) • identityEnvironmentImage x y -
      (9 / 512 : ℝ) • (1 : QMatrix Fixed16.CoreIndex)).PosSemidef := by
  let a : Qubit → ℝ := fun i => if i = 0 then 1 + x else 1 - x
  let b : Qubit → ℝ := fun i => if i = 0 then 1 + y else 1 - y
  have ha (i : Qubit) : 3 / 4 ≤ a i := by dsimp [a]; split_ifs <;> linarith
  have hb (i : Qubit) : 3 / 4 ≤ b i := by dsimp [b]; split_ifs <;> linarith
  have hp (p : Fixed16.CoreIndex) : 0 ≤ a p.1 * b p.2 / 32 - 9 / 512 := by
    have hm := mul_le_mul (ha p.1) (hb p.2)
      (by norm_num : (0 : ℝ) ≤ 3 / 4) (by linarith [ha p.1] : 0 ≤ a p.1)
    nlinarith
  have heq : (1 / 32 : ℝ) • identityEnvironmentImage x y -
      (9 / 512 : ℝ) • (1 : QMatrix Fixed16.CoreIndex) =
      Matrix.diagonal (fun p => ((a p.1 * b p.2 / 32 - 9 / 512 : ℝ) : ℂ)) := by
    ext p q
    by_cases h : p = q
    · subst q
      by_cases ha : p.1 = 0 <;> by_cases hb : p.2 = 0 <;>
        apply Complex.ext <;> norm_num [identityEnvironmentImage, a, b, ha, hb, Matrix.smul_apply,
        Matrix.sub_apply, Matrix.one_apply, Matrix.diagonal_apply,
        RCLike.real_smul_eq_coe_mul, Complex.mul_re, Complex.mul_im] <;> ring
    · simp [identityEnvironmentImage, Matrix.smul_apply, Matrix.sub_apply,
        Matrix.one_apply, Matrix.diagonal_apply, h]
  rw [heq]
  apply Matrix.PosSemidef.diagonal
  intro p
  change (0 : ℂ) ≤ ((a p.1 * b p.2 / 32 - 9 / 512 : ℝ) : ℂ)
  simp only [Complex.le_def, Complex.ofReal_re, Complex.ofReal_im,
    Complex.zero_re, Complex.zero_im, and_true]
  exact hp p

theorem tensorEnvironment_coreXi_support_lower {x y : ℝ}
    (hx : 0 ≤ x) (hxq : x ≤ 1 / 4) (hy : 0 ≤ y) (hyq : y ≤ 1 / 4) :
    (tensorEnvironment x y Fixed16.coreXi -
      (9 / 512 : ℝ) • (1 : QMatrix Fixed16.CoreIndex)).PosSemidef := by
  have hx1 : x ≤ 1 := hxq.trans (by norm_num)
  have hy1 : y ≤ 1 := hyq.trans (by norm_num)
  let K := tensorEnvironmentFamily x y hx hx1 hy hy1
  have hK : (K.apply (Fixed16.coreXi -
      (1 / 32 : ℝ) • (1 : QMatrix Fixed16.CoreIndex))).PosSemidef :=
    K.apply_positive Fixed16.coreXi_support_lower
  have hI := identityEnvironmentImage_support_lower hx hxq hy hyq
  rw [← tensorEnvironment_identity hx hx1 hy hy1] at hI
  have heq : tensorEnvironment x y Fixed16.coreXi -
      (9 / 512 : ℝ) • (1 : QMatrix Fixed16.CoreIndex) =
      K.apply (Fixed16.coreXi - (1 / 32 : ℝ) • (1 : QMatrix Fixed16.CoreIndex)) +
        ((1 / 32 : ℝ) • tensorEnvironment x y (1 : QMatrix Fixed16.CoreIndex) -
          (9 / 512 : ℝ) • (1 : QMatrix Fixed16.CoreIndex)) := by
    rw [← tensorEnvironmentFamily_apply x y hx hx1 hy hy1 Fixed16.coreXi,
      ← tensorEnvironmentFamily_apply x y hx hx1 hy hy1 (1 : QMatrix Fixed16.CoreIndex)]
    dsimp only [K]
    simp only [KrausFamily.apply, Matrix.mul_sub, Matrix.sub_mul,
      Matrix.mul_smul, Matrix.smul_mul, Finset.sum_sub_distrib,
      ← Finset.smul_sum]
    abel
  rw [heq]
  exact hK.add hI

theorem eigenvalues_lower_of_support {I : Type*} [Fintype I] [DecidableEq I]
    {ρ : QMatrix I} (hρ : ρ.IsHermitian) {c : ℝ}
    (hc : (ρ - c • (1 : QMatrix I)).PosSemidef) (i : I) : c ≤ hρ.eigenvalues i := by
  let U : QMatrix I := hρ.eigenvectorUnitary
  have hU : Uᴴ * U = 1 := Unitary.coe_star_mul_self hρ.eigenvectorUnitary
  have hdiag : Uᴴ * ρ * U = Matrix.diagonal (fun i => (hρ.eigenvalues i : ℂ)) := by
    simpa only [Unitary.conjStarAlgAut_star_apply, Matrix.star_eq_conjTranspose,
      Function.comp_def, RCLike.ofReal_eq_complex_ofReal, U] using
        hρ.conjStarAlgAut_star_eigenvectorUnitary
  have hcong := hc.conjTranspose_mul_mul_same U
  have heq : Uᴴ * (ρ - c • (1 : QMatrix I)) * U =
      Matrix.diagonal (fun i => (hρ.eigenvalues i : ℂ)) - c • (1 : QMatrix I) := by
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_one, hdiag, hU]
  rw [heq] at hcong
  have hp := hcong.diag_nonneg (i := i)
  have hr := (Complex.le_def.mp hp).1
  simpa [Matrix.sub_apply, Matrix.diagonal_apply, Matrix.smul_apply,
    RCLike.real_smul_eq_coe_mul] using hr

theorem dampedCoreDensity_support_lower {x y : ℝ}
    (hx : 0 ≤ x) (hxq : x ≤ 1 / 4) (hy : 0 ≤ y) (hyq : y ≤ 1 / 4) :
    ((dampedCoreDensity x y hx (hxq.trans (by norm_num))
      hy (hyq.trans (by norm_num))).matrix -
        (9 / 512 : ℝ) • (1 : QMatrix Fixed16.CoreIndex)).PosSemidef := by
  change ((tensorEnvironmentFamily x y hx (hxq.trans (by norm_num))
    hy (hyq.trans (by norm_num))).apply Fixed16.coreXi -
      (9 / 512 : ℝ) • (1 : QMatrix Fixed16.CoreIndex)).PosSemidef
  rw [tensorEnvironmentFamily_apply]
  exact tensorEnvironment_coreXi_support_lower hx hxq hy hyq

theorem dampedCoreDensity_posDef {x y : ℝ}
    (hx : 0 ≤ x) (hxq : x ≤ 1 / 4) (hy : 0 ≤ y) (hyq : y ≤ 1 / 4) :
    (dampedCoreDensity x y hx (hxq.trans (by norm_num))
      hy (hyq.trans (by norm_num))).matrix.PosDef := by
  have hgap := dampedCoreDensity_support_lower hx hxq hy hyq
  have hpositive : ((9 / 512 : ℝ) • (1 : QMatrix Fixed16.CoreIndex)).PosDef :=
    Matrix.PosDef.one.smul (by norm_num)
  simpa only [sub_add_cancel] using Matrix.PosDef.posSemidef_add hgap hpositive

theorem dampedCoreDensity_eigenvalues_lower {x y : ℝ}
    (hx : 0 ≤ x) (hxq : x ≤ 1 / 4) (hy : 0 ≤ y) (hyq : y ≤ 1 / 4)
    (i : Fixed16.CoreIndex) :
    9 / 512 ≤ (dampedCoreDensity x y hx (hxq.trans (by norm_num))
      hy (hyq.trans (by norm_num))).positive.1.eigenvalues i :=
  eigenvalues_lower_of_support _ (dampedCoreDensity_support_lower hx hxq hy hyq) i

end QuantumProver.DepolarizingSquashedEntanglement.Fixed16FlagEntropy

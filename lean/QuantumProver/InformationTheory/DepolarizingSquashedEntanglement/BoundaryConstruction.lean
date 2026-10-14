import QuantumProver.InformationTheory.DepolarizingSquashedEntanglement.BoundaryCalculus
import QuantumProver.InformationTheory.DepolarizingSquashedEntanglement.Definitions

set_option autoImplicit false

noncomputable section

open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder Matrix Kronecker

namespace QuantumProver.DepolarizingSquashedEntanglement.Fixed16

abbrev Qubit := Fin 2
abbrev CoreIndex := Qubit × Qubit

def coreVector (i : CoreIndex) : ℂ :=
  if i = (0, 0) then 2 else if i = (1, 1) then 1 else 0

def coreXi : Matrix CoreIndex CoreIndex ℂ :=
  (7 / 40 : ℝ) • Matrix.vecMulVec coreVector (star coreVector) +
    (1 / 32 : ℝ) • (1 : Matrix CoreIndex CoreIndex ℂ)

theorem coreXi_posSemidef : coreXi.PosSemidef := by
  exact ((Matrix.posSemidef_vecMulVec_self_star coreVector).smul
    (by norm_num : (0 : ℝ) ≤ 7 / 40)).add
    ((Matrix.PosSemidef.one : (1 : Matrix CoreIndex CoreIndex ℂ).PosSemidef).smul
      (by norm_num : (0 : ℝ) ≤ 1 / 32))

theorem coreXi_posDef : coreXi.PosDef := by
  unfold coreXi
  exact Matrix.PosDef.posSemidef_add
    ((Matrix.posSemidef_vecMulVec_self_star coreVector).smul
      (by norm_num : (0 : ℝ) ≤ 7 / 40))
    ((Matrix.PosDef.one : (1 : Matrix CoreIndex CoreIndex ℂ).PosDef).smul
      (by norm_num : (0 : ℝ) < 1 / 32))

theorem coreXi_support_lower :
    (coreXi - (1 / 32 : ℝ) • (1 : Matrix CoreIndex CoreIndex ℂ)).PosSemidef := by
  simp only [coreXi, add_sub_cancel_right]
  exact (Matrix.posSemidef_vecMulVec_self_star coreVector).smul
    (by norm_num : (0 : ℝ) ≤ 7 / 40)

theorem coreXi_trace_one : coreXi.trace = 1 := by
  have hs2 : (starRingEnd ℂ) (2 : ℂ) = 2 := by
    simpa using map_natCast (starRingEnd ℂ) 2
  norm_num [coreXi, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_one,
    Matrix.trace_vecMulVec, dotProduct, Fintype.sum_prod_type,
    Fin.sum_univ_two, coreVector, RCLike.real_smul_eq_coe_mul, hs2]

theorem coreXi_rational_entries :
    coreXi (0, 0) (0, 0) = 117 / 160 ∧
    coreXi (0, 1) (0, 1) = 5 / 160 ∧
    coreXi (1, 0) (1, 0) = 5 / 160 ∧
    coreXi (1, 1) (1, 1) = 33 / 160 ∧
    coreXi (0, 0) (1, 1) = 56 / 160 ∧
    coreXi (1, 1) (0, 0) = 56 / 160 := by
  norm_num [coreXi, coreVector, Matrix.vecMulVec_apply, Matrix.one_apply,
    RCLike.real_smul_eq_coe_mul]

def weakIsometry (r : ℝ) : Matrix (Qubit × Qubit) Qubit ℂ := fun a i =>
  if i = 0 then
    if a = (0, 0) then 1 else 0
  else if a = (0, 1) then (Real.sqrt (1 - r) : ℂ)
  else if a = (1, 0) then (Real.sqrt r : ℂ)
  else 0

theorem weakIsometry_gram {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    (weakIsometry r)ᴴ * weakIsometry r = 1 := by
  have hs0 : (Real.sqrt r : ℂ) * (Real.sqrt r : ℂ) = (r : ℂ) := by
    exact_mod_cast Real.mul_self_sqrt hr
  have hs1 : (Real.sqrt (1 - r) : ℂ) * (Real.sqrt (1 - r) : ℂ) =
      ((1 - r : ℝ) : ℂ) := by
    exact_mod_cast Real.mul_self_sqrt (sub_nonneg.mpr hr1)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [weakIsometry, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.one_apply, hs0, hs1]

theorem weakIsometry_boundary_gram {δ : ℝ} (hδ : 0 ≤ δ) (hmax : δ ≤ 21 / 512) :
    (weakIsometry (Scalar.boundaryR δ))ᴴ * weakIsometry (Scalar.boundaryR δ) = 1 := by
  apply weakIsometry_gram (Scalar.boundaryR_nonneg hδ)
  exact (Scalar.boundaryR_le_quarter hδ hmax).trans (by norm_num)

def weakState (r : ℝ) (ρ : Matrix Qubit Qubit ℂ) :
    Matrix (Qubit × Qubit) (Qubit × Qubit) ℂ :=
  weakIsometry r * ρ * (weakIsometry r)ᴴ

def weakEnvironment (r : ℝ) (ρ : Matrix Qubit Qubit ℂ) : Matrix Qubit Qubit ℂ :=
  fun e f => ∑ a : Qubit, weakState r ρ (a, e) (a, f)

def weakRetained (r : ℝ) (ρ : Matrix Qubit Qubit ℂ) : Matrix Qubit Qubit ℂ :=
  fun a b => ∑ e : Qubit, weakState r ρ (a, e) (b, e)

def environmentKraus (r : ℝ) (a : Qubit) : Matrix Qubit Qubit ℂ :=
  fun e i => weakIsometry r (a, e) i

def retainedKraus (r : ℝ) (e : Qubit) : Matrix Qubit Qubit ℂ :=
  fun a i => weakIsometry r (a, e) i

def survivalKraus (s : ℝ) (k : Qubit) : Matrix Qubit Qubit ℂ :=
  if k = 0 then Matrix.diagonal (fun i : Qubit =>
    if i = 0 then 1 else (Real.sqrt s : ℂ))
  else fun a i => if a = 0 ∧ i = 1 then (Real.sqrt (1 - s) : ℂ) else 0

theorem environmentKraus_eq_survival (r : ℝ) :
    environmentKraus r = survivalKraus (1 - r) := by
  have h : (1 : ℝ) - (1 - r) = r := by ring
  funext k
  ext e i
  fin_cases k <;> fin_cases e <;> fin_cases i <;>
    simp [environmentKraus, weakIsometry, survivalKraus, Matrix.diagonal, h]

theorem retainedKraus_eq_survival (r : ℝ) :
    retainedKraus r = survivalKraus r := by
  funext k
  ext a i
  fin_cases k <;> fin_cases a <;> fin_cases i <;>
    simp [retainedKraus, weakIsometry, survivalKraus, Matrix.diagonal]

theorem environmentKraus_gram {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    (∑ k : Qubit, (environmentKraus r k)ᴴ * environmentKraus r k) = 1 := by
  calc
    _ = (weakIsometry r)ᴴ * weakIsometry r := by
      ext i j
      simp [environmentKraus, Matrix.sum_apply, Matrix.mul_apply,
        Matrix.conjTranspose_apply, Fintype.sum_prod_type]
    _ = 1 := weakIsometry_gram hr hr1

theorem retainedKraus_gram {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    (∑ k : Qubit, (retainedKraus r k)ᴴ * retainedKraus r k) = 1 := by
  calc
    _ = (weakIsometry r)ᴴ * weakIsometry r := by
      ext i j
      simp only [retainedKraus, Matrix.sum_apply, Matrix.mul_apply,
        Matrix.conjTranspose_apply, Fintype.sum_prod_type]
      exact Finset.sum_comm
    _ = 1 := weakIsometry_gram hr hr1

theorem weakEnvironment_eq_kraus (r : ℝ) (ρ : Matrix Qubit Qubit ℂ) :
    weakEnvironment r ρ =
      ∑ k : Qubit, environmentKraus r k * ρ * (environmentKraus r k)ᴴ := by
  ext e f
  simp [weakEnvironment, weakState, environmentKraus, Matrix.sum_apply,
    Matrix.mul_apply, Matrix.conjTranspose_apply]

theorem weakRetained_eq_kraus (r : ℝ) (ρ : Matrix Qubit Qubit ℂ) :
    weakRetained r ρ =
      ∑ k : Qubit, retainedKraus r k * ρ * (retainedKraus r k)ᴴ := by
  ext a b
  simp [weakRetained, weakState, retainedKraus, Matrix.sum_apply,
    Matrix.mul_apply, Matrix.conjTranspose_apply]

def coreBasisReal (p : CoreIndex) (g : Fin 4) : ℝ :=
  if g = 0 then
    (if p = (0, 0) then 2 else if p = (1, 1) then 1 else 0) / Real.sqrt 5
  else if g = 1 then
    (if p = (0, 0) then 1 else if p = (1, 1) then -2 else 0) / Real.sqrt 5
  else if g = 2 then if p = (0, 1) then 1 else 0
  else if p = (1, 0) then 1 else 0

def coreWeight (g : Fin 4) : ℝ := if g = 0 then 29 / 32 else 1 / 32

def corePurifier (pg : CoreIndex × Fin 4) : ℂ :=
  (Real.sqrt (coreWeight pg.2) * coreBasisReal pg.1 pg.2 : ℝ)

def corePurifierReduced : Matrix CoreIndex CoreIndex ℂ :=
  fun p q => ∑ g : Fin 4, corePurifier (p, g) * star (corePurifier (q, g))

theorem corePurifierReduced_eq_coreXi : corePurifierReduced = coreXi := by
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have h5n : Real.sqrt (5 : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have h29n : Real.sqrt (29 : ℝ) ^ 2 = 29 := Real.sq_sqrt (by norm_num)
  have h32n : Real.sqrt (32 : ℝ) ^ 2 = 32 := Real.sq_sqrt (by norm_num)
  have h32ne : Real.sqrt (32 : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have h5four : Real.sqrt (5 : ℝ) ^ 4 = 25 := by
    calc
      Real.sqrt (5 : ℝ) ^ 4 = (Real.sqrt (5 : ℝ) ^ 2) ^ 2 := by ring
      _ = 25 := by rw [h5]; norm_num
  have h32four : Real.sqrt (32 : ℝ) ^ 4 = 1024 := by
    calc
      Real.sqrt (32 : ℝ) ^ 4 = (Real.sqrt (32 : ℝ) ^ 2) ^ 2 := by ring
      _ = 1024 := by rw [h32n]; norm_num
  have h29 : Real.sqrt (29 / 32 : ℝ) ^ 2 = 29 / 32 :=
    Real.sq_sqrt (by norm_num)
  have h1 : Real.sqrt (1 / 32 : ℝ) ^ 2 = 1 / 32 :=
    Real.sq_sqrt (by norm_num)
  ext p q
  rcases p with ⟨a, b⟩
  rcases q with ⟨c, d⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    apply Complex.ext <;>
    norm_num [corePurifierReduced, corePurifier, coreWeight, coreBasisReal,
      coreXi, coreVector, Matrix.vecMulVec_apply, Matrix.one_apply,
      Fin.sum_univ_succ, RCLike.real_smul_eq_coe_mul, Complex.mul_re,
      Complex.mul_im] <;>
    field_simp [h5n, h32ne] <;> ring_nf <;>
    norm_num [h5, h29n, h32n, h5four, h32four, h29, h1]

theorem corePurifier_normalized :
    (∑ pg : CoreIndex × Fin 4, Complex.normSq (corePurifier pg)) = 1 := by
  have ht : corePurifierReduced.trace = 1 := by
    rw [corePurifierReduced_eq_coreXi, coreXi_trace_one]
  have hre := congrArg Complex.re ht
  simpa [corePurifierReduced, Matrix.trace, Matrix.diag,
    Fintype.sum_prod_type, Complex.mul_conj] using hre

def coreEnvironmentPhase (d : Qubit → ℂ) (p : CoreIndex) : ℂ :=
  star (d p.1) * d p.2

def corePurifierPhase (d : Qubit → ℂ) (g : Fin 4) : ℂ :=
  if g = 0 ∨ g = 1 then 1
  else if g = 2 then (star (d 0) * d 1)⁻¹
  else (star (d 1) * d 0)⁻¹

theorem corePurifier_diagonal_phase (d : Qubit → ℂ)
    (hd0 : star (d 0) * d 0 = 1) (hd1 : star (d 1) * d 1 = 1)
    (p : CoreIndex) (g : Fin 4) :
    coreEnvironmentPhase d p * corePurifierPhase d g * corePurifier (p, g) =
      corePurifier (p, g) := by
  have h0 : d 0 ≠ 0 := by
    intro h
    simp [h] at hd0
  have h1 : d 1 ≠ 0 := by
    intro h
    simp [h] at hd1
  have hd0' : (starRingEnd ℂ) (d 0) * d 0 = 1 := hd0
  have hd1' : (starRingEnd ℂ) (d 1) * d 1 = 1 := hd1
  have hs0 : (starRingEnd ℂ) (d 0) ≠ 0 := star_ne_zero.mpr h0
  have hs1 : (starRingEnd ℂ) (d 1) ≠ 0 := star_ne_zero.mpr h1
  rcases p with ⟨a, b⟩
  fin_cases a <;> fin_cases b <;> fin_cases g <;>
    simp [coreEnvironmentPhase, corePurifierPhase, corePurifier, coreWeight,
      coreBasisReal, hd0', hd1'] <;>
    field_simp [h0, h1, hs0, hs1] <;> ring

theorem weakIsometry_diagonal_phase (d : Qubit → ℂ) (r : ℝ)
    (a e i : Qubit) :
    (d a * d e) * weakIsometry r (a, e) i =
      d 0 * weakIsometry r (a, e) i * d i := by
  fin_cases a <;> fin_cases e <;> fin_cases i <;>
    simp [weakIsometry] <;> ring

def tetraCos : ℝ := Real.sqrt ((3 + Real.sqrt 3) / 6)
def tetraOff : ℝ := Real.sqrt ((3 - Real.sqrt 3) / 12)

theorem tetraCos_sq : tetraCos ^ 2 = (3 + Real.sqrt 3) / 6 := by
  apply Real.sq_sqrt
  positivity

theorem tetraOff_sq : tetraOff ^ 2 = (3 - Real.sqrt 3) / 12 := by
  apply Real.sq_sqrt
  have hs : Real.sqrt (3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hn : 0 ≤ Real.sqrt (3 : ℝ) := Real.sqrt_nonneg _
  have hle : Real.sqrt (3 : ℝ) ≤ 3 := by nlinarith
  positivity

theorem tetraCos_mul_tetraOff : tetraCos * tetraOff = Real.sqrt 3 / 6 := by
  have hs : Real.sqrt (3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hp : (tetraCos * tetraOff) ^ 2 = (Real.sqrt 3 / 6) ^ 2 := by
    calc
      _ = tetraCos ^ 2 * tetraOff ^ 2 := by ring
      _ = (Real.sqrt 3 / 6) ^ 2 := by rw [tetraCos_sq, tetraOff_sq]; nlinarith
  have hn : 0 ≤ tetraCos * tetraOff := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hn' : 0 ≤ Real.sqrt (3 : ℝ) / 6 := by positivity
  nlinarith

def tetraUnitary : Matrix Qubit Qubit ℂ :=
  !![(tetraCos : ℂ), (-1 + Complex.I) * tetraOff;
    (1 + Complex.I) * tetraOff, (tetraCos : ℂ)]

theorem tetraUnitary_gram : tetraUnitaryᴴ * tetraUnitary = 1 := by
  have hc := tetraCos_sq
  have hh := tetraOff_sq
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    norm_num [tetraUnitary, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fin.sum_univ_two, Matrix.one_apply, Complex.mul_re, Complex.mul_im] <;>
    nlinarith

theorem pauli_gram (j : Fin 4) :
    (QuantumProver.DepolarizingSquashedEntanglement.pauli j)ᴴ * QuantumProver.DepolarizingSquashedEntanglement.pauli j = 1 := by
  fin_cases j <;> ext a b <;> fin_cases a <;> fin_cases b <;>
    norm_num [QuantumProver.DepolarizingSquashedEntanglement.pauli, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.one_apply, Fin.sum_univ_two]

theorem pauli_transpose_eq_conjugate (j : Fin 4) :
    (QuantumProver.DepolarizingSquashedEntanglement.pauli j).transpose =
      (QuantumProver.DepolarizingSquashedEntanglement.pauli j).map (starRingEnd ℂ) := by
  fin_cases j <;> ext a b <;> fin_cases a <;> fin_cases b <;>
    norm_num [QuantumProver.DepolarizingSquashedEntanglement.pauli, Matrix.transpose_apply, Matrix.map_apply,
      Matrix.one_apply]

def pauliBranchIndex (k j : Fin 4) : Fin 4 :=
  if k = 0 then j else if k = 1 then
    (if j = 0 then 1 else if j = 1 then 0 else if j = 2 then 3 else 2)
  else if k = 2 then
    (if j = 0 then 2 else if j = 1 then 3 else if j = 2 then 0 else 1)
  else (if j = 0 then 3 else if j = 1 then 2 else if j = 2 then 1 else 0)

def pauliBranchPermutation (k : Fin 4) : Equiv.Perm (Fin 4) where
  toFun := pauliBranchIndex k
  invFun := pauliBranchIndex k
  left_inv := by intro j; fin_cases k <;> fin_cases j <;> norm_num [pauliBranchIndex]
  right_inv := by intro j; fin_cases k <;> fin_cases j <;> norm_num [pauliBranchIndex]

def pairedPauli (j : Fin 4) : Matrix CoreIndex CoreIndex ℂ :=
  (QuantumProver.DepolarizingSquashedEntanglement.pauli j).transpose ⊗ₖ QuantumProver.DepolarizingSquashedEntanglement.pauli j

theorem pairedPauli_gram (j : Fin 4) : (pairedPauli j)ᴴ * pairedPauli j = 1 := by
  fin_cases j <;> ext p q
  all_goals rcases p with ⟨a,b⟩; rcases q with ⟨c,d⟩
  all_goals fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    norm_num [pairedPauli, QuantumProver.DepolarizingSquashedEntanglement.pauli, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Matrix.transpose_apply, Matrix.kroneckerMap_apply,
      Matrix.one_apply, Fintype.sum_prod_type, Fin.sum_univ_two]

theorem pairedPauli_mul (k j : Fin 4) :
    pairedPauli k * pairedPauli j = pairedPauli (pauliBranchIndex k j) := by
  fin_cases k <;> fin_cases j <;> ext p q
  all_goals rcases p with ⟨a,b⟩; rcases q with ⟨c,d⟩
  all_goals fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    norm_num [pairedPauli, pauliBranchIndex, QuantumProver.DepolarizingSquashedEntanglement.pauli, Matrix.mul_apply,
      Matrix.transpose_apply, Matrix.kroneckerMap_apply, Matrix.one_apply,
      Fintype.sum_prod_type, Fin.sum_univ_two]

theorem conjugate_gram {I O : Type*} [Fintype I] [Fintype O]
    [DecidableEq I] (U : Matrix O I ℂ) (hU : Uᴴ * U = 1) :
    (U.map (starRingEnd ℂ))ᴴ * U.map (starRingEnd ℂ) = 1 := by
  ext i j
  have h := congrArg (fun M : Matrix I I ℂ => star (M i j)) hU
  simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.map_apply,
    Matrix.one_apply] using h

def tetraCoreMatrix : Matrix CoreIndex CoreIndex ℂ :=
  tetraUnitary.map (starRingEnd ℂ) ⊗ₖ tetraUnitary

theorem tetraCoreMatrix_gram : tetraCoreMatrixᴴ * tetraCoreMatrix = 1 := by
  simp only [tetraCoreMatrix, Matrix.conjTranspose_kronecker,
    ← Matrix.mul_kronecker_mul, conjugate_gram tetraUnitary tetraUnitary_gram,
    tetraUnitary_gram, Matrix.one_kronecker_one]

def tetraBranchUnitary (j : Fin 4) : Matrix Qubit Qubit ℂ :=
  QuantumProver.DepolarizingSquashedEntanglement.pauli j * tetraUnitary

def tetraBranchMatrix (j : Fin 4) : Matrix CoreIndex CoreIndex ℂ :=
  pairedPauli j * tetraCoreMatrix

theorem tetraBranchMatrix_eq (j : Fin 4) :
    tetraBranchMatrix j =
      (tetraBranchUnitary j).map (starRingEnd ℂ) ⊗ₖ tetraBranchUnitary j := by
  simp only [tetraBranchMatrix, pairedPauli, tetraCoreMatrix, tetraBranchUnitary,
    pauli_transpose_eq_conjugate, Matrix.map_mul, Matrix.mul_kronecker_mul]

theorem tetraBranchMatrix_gram (j : Fin 4) :
    (tetraBranchMatrix j)ᴴ * tetraBranchMatrix j = 1 := by
  calc
    _ = tetraCoreMatrixᴴ * ((pairedPauli j)ᴴ * pairedPauli j) * tetraCoreMatrix := by
      simp only [tetraBranchMatrix, Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = 1 := by rw [pairedPauli_gram, Matrix.mul_one, tetraCoreMatrix_gram]

theorem tetraBranchMatrix_pauli_covariance (k j : Fin 4) :
    pairedPauli k * tetraBranchMatrix j = tetraBranchMatrix (pauliBranchPermutation k j) := by
  change pairedPauli k * (pairedPauli j * tetraCoreMatrix) =
    pairedPauli (pauliBranchIndex k j) * tetraCoreMatrix
  rw [← Matrix.mul_assoc, pairedPauli_mul]

end QuantumProver.DepolarizingSquashedEntanglement.Fixed16

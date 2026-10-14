import QuantumProver.InformationTheory.WernerEndpoint.LocalProtocolReindex

noncomputable section

namespace QuantumProver.WernerEndpoint.SingletResource

open scoped BigOperators Kronecker
open OperationalEndpointCost

abbrev QubitPower : ℕ → Type
  | 0 => Unit
  | n + 1 => Fin 2 × QubitPower n

instance qubitPowerFintype (n : ℕ) : Fintype (QubitPower n) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype Unit)
  | succ n ih =>
      letI := ih
      exact inferInstanceAs (Fintype (Fin 2 × QubitPower n))

instance qubitPowerDecidableEq (n : ℕ) : DecidableEq (QubitPower n) := by
  induction n with
  | zero => exact inferInstanceAs (DecidableEq Unit)
  | succ n ih =>
      letI := ih
      exact inferInstanceAs (DecidableEq (Fin 2 × QubitPower n))

theorem qubitPower_card (n : ℕ) : Fintype.card (QubitPower n) = 2 ^ n := by
  induction n with
  | zero => simp [QubitPower]
  | succ n ih => simp [QubitPower, Fintype.card_prod, ih, pow_succ, Nat.mul_comm]

def singletVector : Fin 2 × Fin 2 → ℂ := fun pq =>
  wedgeScale * ((if pq.1 = 0 ∧ pq.2 = 1 then 1 else 0) -
    (if pq.1 = 1 ∧ pq.2 = 0 then 1 else 0))

theorem singletVector_normSq : vectorNormSq singletVector = 1 := by
  have ht : ((vectorNormSq singletVector : ℝ) : ℂ) = 1 := by
    rw [← pureDensity_trace]
    norm_num [Matrix.trace, Matrix.diag, pureDensity, crossDensity, singletVector,
      Fintype.sum_prod_type, Fin.sum_univ_two, wedgeScale_star, wedgeScale_square]
  exact_mod_cast ht

def bobUnitary : Matrix (Fin 2) (Fin 2) ℂ := fun i j =>
  if i = 0 ∧ j = 1 then 1 else if i = 1 ∧ j = 0 then -1 else 0

theorem bobUnitary_gram : bobUnitary.conjTranspose * bobUnitary = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [bobUnitary, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.one_apply, Fin.sum_univ_two]

theorem bobUnitary_cogram : bobUnitary * bobUnitary.conjTranspose = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [bobUnitary, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.one_apply, Fin.sum_univ_two]

theorem bobUnitary_singlet :
    ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ bobUnitary).mulVec singletVector =
      bellVector := by
  ext ⟨i, j⟩
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
      Fin.sum_univ_two, Matrix.kronecker_apply, Matrix.one_apply,
      bobUnitary, singletVector, bellVector]

def pairPowerVector (v : Fin 2 × Fin 2 → ℂ) :
    (n : ℕ) → QubitPower n × QubitPower n → ℂ
  | 0 => fun _ => 1
  | n + 1 => fun pq => v (pq.1.1, pq.2.1) *
      pairPowerVector v n (pq.1.2, pq.2.2)

def singletPowerVector (n : ℕ) := pairPowerVector singletVector n
def bellPowerVector (n : ℕ) := pairPowerVector bellVector n

def bobUnitaryPower : (n : ℕ) → Matrix (QubitPower n) (QubitPower n) ℂ
  | 0 => 1
  | n + 1 => bobUnitary ⊗ₖ bobUnitaryPower n

theorem bobUnitaryPower_gram (n : ℕ) :
    (bobUnitaryPower n).conjTranspose * bobUnitaryPower n = 1 := by
  induction n with
  | zero => simp [bobUnitaryPower]
  | succ n ih =>
      rw [bobUnitaryPower, Matrix.conjTranspose_kronecker,
        ← Matrix.mul_kronecker_mul, bobUnitary_gram, ih, Matrix.one_kronecker_one]

theorem bobUnitaryPower_cogram (n : ℕ) :
    bobUnitaryPower n * (bobUnitaryPower n).conjTranspose = 1 := by
  induction n with
  | zero => simp [bobUnitaryPower]
  | succ n ih =>
      rw [bobUnitaryPower, Matrix.conjTranspose_kronecker,
        ← Matrix.mul_kronecker_mul, bobUnitary_cogram, ih, Matrix.one_kronecker_one]

private theorem localPairTensor_mulVec
    {A₀ B₀ A₁ B₁ C₀ D₀ C₁ D₁ : Type*}
    [Fintype A₀] [Fintype B₀] [Fintype C₀] [Fintype D₀]
    (U : Matrix A₁ A₀ ℂ) (V : Matrix B₁ B₀ ℂ)
    (C : Matrix C₁ C₀ ℂ) (D : Matrix D₁ D₀ ℂ)
    (u : A₀ × B₀ → ℂ) (v : C₀ × D₀ → ℂ) :
    ((U ⊗ₖ C) ⊗ₖ (V ⊗ₖ D)).mulVec
        (fun pq => u (pq.1.1, pq.2.1) * v (pq.1.2, pq.2.2)) =
      fun pq => (U ⊗ₖ V).mulVec u (pq.1.1, pq.2.1) *
        (C ⊗ₖ D).mulVec v (pq.1.2, pq.2.2) := by
  classical
  ext ⟨⟨a, r⟩, ⟨b, s⟩⟩
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Matrix.kronecker_apply]
  calc
    (∑ p : A₀, ∑ t : C₀, ∑ q : B₀, ∑ z : D₀,
      (U a p * C r t) * (V b q * D s z) * (u (p,q) * v (t,z))) =
        ∑ p : A₀, ∑ q : B₀, ∑ t : C₀, ∑ z : D₀,
          (U a p * V b q * u (p,q)) * (C r t * D s z * v (t,z)) := by
      apply Finset.sum_congr rfl
      intro p _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro q _
      apply Finset.sum_congr rfl
      intro t _
      apply Finset.sum_congr rfl
      intro z _
      ring
    _ = _ := by simp only [← Finset.mul_sum, ← Finset.sum_mul]

private theorem localPairTensor_normSq {A B C D : Type*}
    [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    (u : A × B → ℂ) (v : C × D → ℂ) :
    vectorNormSq (fun pq : (A × C) × (B × D) =>
      u (pq.1.1, pq.2.1) * v (pq.1.2, pq.2.2)) =
      vectorNormSq u * vectorNormSq v := by
  simp only [vectorNormSq, Fintype.sum_prod_type, Complex.normSq_mul]
  calc
    (∑ a : A, ∑ c : C, ∑ b : B, ∑ d : D,
      Complex.normSq (u (a,b)) * Complex.normSq (v (c,d))) =
        ∑ a : A, ∑ b : B, ∑ c : C, ∑ d : D,
          Complex.normSq (u (a,b)) * Complex.normSq (v (c,d)) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
    _ = _ := by simp only [← Finset.mul_sum, ← Finset.sum_mul]

theorem pairPowerVector_normSq (v : Fin 2 × Fin 2 → ℂ) (n : ℕ) :
    vectorNormSq (pairPowerVector v n) = vectorNormSq v ^ n := by
  induction n with
  | zero => simp [pairPowerVector, QubitPower, vectorNormSq]
  | succ n ih =>
      change vectorNormSq (fun pq : (Fin 2 × QubitPower n) ×
        (Fin 2 × QubitPower n) => v (pq.1.1,pq.2.1) *
          pairPowerVector v n (pq.1.2,pq.2.2)) = _
      rw [localPairTensor_normSq, ih, pow_succ, mul_comm]

theorem singletPowerVector_normSq (n : ℕ) : vectorNormSq (singletPowerVector n) = 1 := by
  rw [singletPowerVector, pairPowerVector_normSq, singletVector_normSq, one_pow]

theorem bellPowerVector_normSq (n : ℕ) : vectorNormSq (bellPowerVector n) = 1 := by
  rw [bellPowerVector, pairPowerVector_normSq, bellVector_normSq, one_pow]

theorem bobUnitaryPower_singlet (n : ℕ) :
    ((1 : Matrix (QubitPower n) (QubitPower n) ℂ) ⊗ₖ bobUnitaryPower n).mulVec
      (singletPowerVector n) = bellPowerVector n := by
  induction n with
  | zero =>
      simp [bobUnitaryPower, singletPowerVector, bellPowerVector, pairPowerVector]
  | succ n ih =>
      have hOne : (1 : Matrix (Fin 2 × QubitPower n) (Fin 2 × QubitPower n) ℂ) =
          (1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ
            (1 : Matrix (QubitPower n) (QubitPower n) ℂ) :=
        Matrix.one_kronecker_one.symm
      change ((1 : Matrix (Fin 2 × QubitPower n) (Fin 2 × QubitPower n) ℂ) ⊗ₖ
        (bobUnitary ⊗ₖ bobUnitaryPower n)).mulVec
        (fun pq => singletVector (pq.1.1,pq.2.1) *
          singletPowerVector n (pq.1.2,pq.2.2)) =
        fun pq => bellVector (pq.1.1,pq.2.1) * bellPowerVector n (pq.1.2,pq.2.2)
      rw [hOne, localPairTensor_mulVec, bobUnitary_singlet, ih]

theorem bobUnitaryPower_adjoint_bell (n : ℕ) :
    ((1 : Matrix (QubitPower n) (QubitPower n) ℂ) ⊗ₖ
      (bobUnitaryPower n).conjTranspose).mulVec (bellPowerVector n) =
      singletPowerVector n := by
  rw [← bobUnitaryPower_singlet n, Matrix.mulVec_mulVec,
    ← Matrix.mul_kronecker_mul, Matrix.one_mul, bobUnitaryPower_gram,
    Matrix.one_kronecker_one, Matrix.one_mulVec]

section Coordinates

variable {a : ℕ} (n : ℕ) (e : Fin a ≃ QubitPower n)

def singletVectorIn : Fin a × Fin a → ℂ := singletPowerVector n ∘ (e.prodCongr e)
def bellVectorIn : Fin a × Fin a → ℂ := bellPowerVector n ∘ (e.prodCongr e)
def bobUnitaryIn : Matrix (Fin a) (Fin a) ℂ := (bobUnitaryPower n).submatrix e e

theorem singletVectorIn_normSq : vectorNormSq (singletVectorIn n e) = 1 := by
  rw [singletVectorIn, OneWayLocalInstrument.vectorNormSq_equiv,
    singletPowerVector_normSq]

theorem bellVectorIn_normSq : vectorNormSq (bellVectorIn n e) = 1 := by
  rw [bellVectorIn, OneWayLocalInstrument.vectorNormSq_equiv, bellPowerVector_normSq]

theorem bobUnitaryIn_gram : (bobUnitaryIn n e).conjTranspose * bobUnitaryIn n e = 1 := by
  rw [bobUnitaryIn, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv,
    bobUnitaryPower_gram, Matrix.submatrix_one_equiv]

theorem bobUnitaryIn_cogram : bobUnitaryIn n e * (bobUnitaryIn n e).conjTranspose = 1 := by
  rw [bobUnitaryIn, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv,
    bobUnitaryPower_cogram, Matrix.submatrix_one_equiv]

private theorem jointUnitaryIn (U : Matrix (QubitPower n) (QubitPower n) ℂ) :
    ((1 : Matrix (Fin a) (Fin a) ℂ) ⊗ₖ U.submatrix e e) =
      ((1 : Matrix (QubitPower n) (QubitPower n) ℂ) ⊗ₖ U).submatrix
        (e.prodCongr e) (e.prodCongr e) := by
  rw [← Matrix.submatrix_one_equiv (α := ℂ) e]
  rfl

theorem bobUnitaryIn_singlet :
    ((1 : Matrix (Fin a) (Fin a) ℂ) ⊗ₖ bobUnitaryIn n e).mulVec
      (singletVectorIn n e) = bellVectorIn n e := by
  rw [bobUnitaryIn, jointUnitaryIn, singletVectorIn,
    Matrix.submatrix_mulVec_equiv]
  have hV : (singletPowerVector n ∘ (e.prodCongr e)) ∘
      (e.prodCongr e).symm = singletPowerVector n := by
    ext x
    simp only [Function.comp_apply, Equiv.apply_symm_apply]
  rw [hV, bobUnitaryPower_singlet]
  rfl

theorem bobUnitaryIn_adjoint_bell :
    ((1 : Matrix (Fin a) (Fin a) ℂ) ⊗ₖ (bobUnitaryIn n e).conjTranspose).mulVec
      (bellVectorIn n e) = singletVectorIn n e := by
  rw [← bobUnitaryIn_singlet n e, Matrix.mulVec_mulVec,
    ← Matrix.mul_kronecker_mul, Matrix.one_mul, bobUnitaryIn_gram,
    Matrix.one_kronecker_one, Matrix.one_mulVec]

end Coordinates

def prependBobUnitary {a b c d : ℕ} (T : FiniteLocalProtocol c d a b)
    (U : Matrix (Fin b) (Fin b) ℂ) (hU : U.conjTranspose * U = 1) :
    FiniteLocalProtocol c d a b :=
  .bob (h := 1) (z := 1) (fun _ _ => U)
    (by simpa using hU) (fun _ => T)

theorem prependBobUnitary_apply {a b c d : ℕ} (T : FiniteLocalProtocol c d a b)
    (U : Matrix (Fin b) (Fin b) ℂ) (hU : U.conjTranspose * U = 1)
    (ρ : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) :
    (prependBobUnitary T U hU).apply ρ =
      T.apply (((1 : Matrix (Fin a) (Fin a) ℂ) ⊗ₖ U) * ρ *
        ((1 : Matrix (Fin a) (Fin a) ℂ) ⊗ₖ U).conjTranspose) := by
  simp [prependBobUnitary, FiniteLocalProtocol.apply]

def singletToBellProtocol {a c d : ℕ} (n : ℕ) (e : Fin a ≃ QubitPower n)
    (T : FiniteLocalProtocol c d a a) : FiniteLocalProtocol c d a a :=
  prependBobUnitary T (bobUnitaryIn n e) (bobUnitaryIn_gram n e)

def bellToSingletProtocol {a c d : ℕ} (n : ℕ) (e : Fin a ≃ QubitPower n)
    (T : FiniteLocalProtocol c d a a) : FiniteLocalProtocol c d a a :=
  prependBobUnitary T (bobUnitaryIn n e).conjTranspose
    (by simpa using bobUnitaryIn_cogram n e)

theorem singletToBellProtocol_output {a c d : ℕ} (n : ℕ)
    (e : Fin a ≃ QubitPower n) (T : FiniteLocalProtocol c d a a) :
    (singletToBellProtocol n e T).apply (pureDensity (singletVectorIn n e)) =
      T.apply (pureDensity (bellVectorIn n e)) := by
  rw [singletToBellProtocol, prependBobUnitary_apply]
  simp only [pureDensity, sandwich_crossDensity, bobUnitaryIn_singlet]

theorem bellToSingletProtocol_output {a c d : ℕ} (n : ℕ)
    (e : Fin a ≃ QubitPower n) (T : FiniteLocalProtocol c d a a) :
    (bellToSingletProtocol n e T).apply (pureDensity (bellVectorIn n e)) =
      T.apply (pureDensity (singletVectorIn n e)) := by
  rw [bellToSingletProtocol, prependBobUnitary_apply]
  simp only [pureDensity, sandwich_crossDensity, bobUnitaryIn_adjoint_bell]

end QuantumProver.WernerEndpoint.SingletResource

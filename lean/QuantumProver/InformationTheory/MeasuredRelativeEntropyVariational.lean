import QuantumProver.InformationTheory.SuperchannelDiscrimination.TestingTheorems

set_option autoImplicit false

noncomputable section

open scoped BigOperators ComplexOrder MatrixOrder Matrix Matrix.Norms.L2Operator Kronecker
open QuantumProver.SuperchannelDiscrimination
open QuantumProver.SuperchannelDiscrimination.FlaggedStates
open QuantumProver.SuperchannelDiscrimination.KrausCompletion
open QuantumProver.SuperchannelDiscrimination.CPWrappers
open QuantumProver.SuperchannelDiscrimination.TensorEntropy

namespace QuantumProver.MeasuredRelativeEntropyVariational

variable {I K O : Type*} [Fintype I] [DecidableEq I]
  [Fintype K] [Fintype O] [DecidableEq O]

abbrev Mat (I : Type*) := Matrix I I ℂ

structure POVM (I K : Type*) [Fintype I] [Fintype K] [DecidableEq I] where
  effect : K → Mat I
  positive : ∀ k, (effect k).PosSemidef
  normalized : ∑ k, effect k = 1

def measurementProbability (M : POVM I K) (A : Mat I) (k : K) : ℝ :=
  (A * M.effect k).trace.re

def classicalTermBits (p q : ℝ) : EReal :=
  if p = 0 then 0 else if q = 0 then ⊤
    else ((p * (Real.log p - Real.log q) / Real.log 2 : ℝ) : EReal)

def classicalRelativeEntropyBits (p q : K → ℝ) : EReal :=
  ∑ k, classicalTermBits (p k) (q k)

def measuredRelativeEntropyBits (A B : Mat I) : EReal :=
  sSup {z | ∃ m : ℕ, 0 < m ∧ ∃ M : POVM I (Fin m),
    z = classicalRelativeEntropyBits (measurementProbability M A) (measurementProbability M B)}

def matrixObjectiveBits (rho sigma Omega : Mat I) : ℝ :=
  ((rho * cfc Real.log Omega).trace.re + 1 - (sigma * Omega).trace.re) / Real.log 2

def matrixVariationalValues (rho sigma : Mat I) : Set EReal :=
  {z | ∃ Omega : Mat I, Omega.PosDef ∧ z = (matrixObjectiveBits rho sigma Omega : EReal)}

def variationalRelativeEntropyBits (rho sigma : Mat I) : EReal :=
  sSup (matrixVariationalValues rho sigma)

theorem log_two_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)

theorem measurementProbability_nonneg (M : POVM I K) {A : Mat I}
    (hA : A.PosSemidef) (k : K) : 0 ≤ measurementProbability M A k :=
  trace_mul_re_nonneg hA (M.positive k)

theorem measurementProbability_sum (M : POVM I K) (A : Mat I) :
    ∑ k, measurementProbability M A k = A.trace.re := by
  simp only [measurementProbability, ← Complex.re_sum, ← Matrix.trace_sum,
    ← Matrix.mul_sum, M.normalized, Matrix.mul_one]

theorem measurementProbability_sum_density (M : POVM I K) {rho : Mat I}
    (hRho : IsDensity rho) : ∑ k, measurementProbability M rho k = 1 := by
  rw [measurementProbability_sum, hRho.2]
  rfl

def identityPOVM : POVM I (Fin 1) where
  effect := fun _ => 1
  positive := fun _ => Matrix.PosSemidef.one
  normalized := by simp

theorem measuredRelativeEntropyBits_zero {rho : Mat I} (hRho : IsDensity rho) :
    measuredRelativeEntropyBits rho 0 = ⊤ := by
  apply le_antisymm le_top
  apply le_sSup
  refine ⟨1, by decide, identityPOVM, ?_⟩
  simp [classicalRelativeEntropyBits, classicalTermBits, measurementProbability,
    identityPOVM, hRho.2]

def scalarObjectiveBits (p q r : ℝ) : ℝ :=
  (p * Real.log r + p - q * r) / Real.log 2

def scalarVariationalValues (p q : ℝ) : Set EReal :=
  {z | ∃ r : ℝ, 0 < r ∧ z = (scalarObjectiveBits p q r : EReal)}

theorem scalarObjectiveBits_le_classicalTermBits (p q r : ℝ)
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hr : 0 < r) :
    (scalarObjectiveBits p q r : EReal) ≤ classicalTermBits p q := by
  by_cases hp0 : p = 0
  · rw [classicalTermBits, if_pos hp0]
    apply EReal.coe_le_coe
    simp only [scalarObjectiveBits, hp0, zero_mul, zero_add, zero_sub]
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (mul_nonneg hq hr.le)) log_two_pos.le
  rw [classicalTermBits, if_neg hp0]
  by_cases hq0 : q = 0
  · simp only [if_pos hq0, le_top]
  rw [if_neg hq0]
  apply EReal.coe_le_coe
  apply div_le_div_of_nonneg_right _ log_two_pos.le
  have hqpos : 0 < q := lt_of_le_of_ne hq (Ne.symm hq0)
  have h := Klein.scalar_log_tangent hp (mul_pos hqpos hr)
  rw [Real.log_mul hqpos.ne' hr.ne'] at h
  linarith

theorem scalarObjectiveBits_optimum (p q : ℝ) (hp : 0 < p) (hq : 0 < q) :
    scalarObjectiveBits p q (p/q) = p * (Real.log p - Real.log q) / Real.log 2 := by
  unfold scalarObjectiveBits
  rw [Real.log_div hp.ne' hq.ne']
  have h : q * (p/q) = p := by field_simp
  rw [h]
  ring

theorem classicalTermBits_variational (p q : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q) :
    classicalTermBits p q = sSup (scalarVariationalValues p q) := by
  have hupper : sSup (scalarVariationalValues p q) ≤ classicalTermBits p q := by
    apply sSup_le
    rintro z ⟨r, hr, rfl⟩
    exact scalarObjectiveBits_le_classicalTermBits p q r hp hq hr
  apply le_antisymm _ hupper
  by_cases hp0 : p = 0
  · simp only [classicalTermBits, if_pos hp0]
    by_cases hq0 : q = 0
    · have hm : (0 : EReal) ∈ scalarVariationalValues p q := by
        refine ⟨1, by norm_num, ?_⟩
        simp [scalarObjectiveBits, hp0, hq0]
      exact le_sSup hm
    have hqpos : 0 < q := lt_of_le_of_ne hq (Ne.symm hq0)
    by_contra hn
    have hs : sSup (scalarVariationalValues p q) < 0 := lt_of_not_ge hn
    obtain ⟨b, hb, hb0⟩ := EReal.exists_between_coe_real hs
    have hbneg : b < 0 := by exact_mod_cast hb0
    let r := -b * Real.log 2 / (2*q)
    have hr : 0 < r := div_pos (mul_pos (neg_pos.mpr hbneg) log_two_pos) (by positivity)
    have heq : scalarObjectiveBits p q r = b/2 := by
      unfold scalarObjectiveBits r
      rw [hp0]
      field_simp [log_two_pos.ne', hqpos.ne']
      <;> ring
    have hm : ((b/2 : ℝ) : EReal) ≤ sSup (scalarVariationalValues p q) := by
      apply le_sSup
      exact ⟨r, hr, by rw [heq]⟩
    have hbb : (b : EReal) < ((b/2 : ℝ) : EReal) := EReal.coe_lt_coe_iff.mpr (by linarith)
    exact not_lt_of_ge hm (hb.trans hbb)
  have hppos : 0 < p := lt_of_le_of_ne hp (Ne.symm hp0)
  rw [classicalTermBits, if_neg hp0]
  by_cases hq0 : q = 0
  · rw [if_pos hq0]
    by_contra hn
    have hs : sSup (scalarVariationalValues p q) < ⊤ := lt_of_not_ge hn
    obtain ⟨b, hb, _⟩ := EReal.exists_between_coe_real hs
    let r := Real.exp ((b * Real.log 2 - p) / p + 1)
    have hr : 0 < r := Real.exp_pos _
    have heq : scalarObjectiveBits p q r = b + p / Real.log 2 := by
      unfold scalarObjectiveBits r
      rw [hq0, Real.log_exp]
      field_simp [hppos.ne', log_two_pos.ne']
      <;> ring
    have hm : ((b + p/Real.log 2 : ℝ) : EReal) ≤ sSup (scalarVariationalValues p q) := by
      apply le_sSup
      exact ⟨r, hr, by rw [heq]⟩
    have hbb : (b : EReal) < ((b+p/Real.log 2 : ℝ) : EReal) :=
      EReal.coe_lt_coe_iff.mpr (lt_add_of_pos_right _ (div_pos hppos log_two_pos))
    exact not_lt_of_ge hm (hb.trans hbb)
  rw [if_neg hq0]
  apply le_sSup
  refine ⟨p/q, div_pos hppos (lt_of_le_of_ne hq (Ne.symm hq0)), ?_⟩
  rw [scalarObjectiveBits_optimum p q hppos (lt_of_le_of_ne hq (Ne.symm hq0))]

def vectorObjectiveBits (p q r : K → ℝ) : ℝ := ∑ k, scalarObjectiveBits (p k) (q k) (r k)

theorem vectorObjectiveBits_le_classicalRelativeEntropyBits (p q r : K → ℝ)
    (hp : ∀ k, 0 ≤ p k) (hq : ∀ k, 0 ≤ q k) (hr : ∀ k, 0 < r k) :
    (vectorObjectiveBits p q r : EReal) ≤ classicalRelativeEntropyBits p q := by
  let coeHom : ℝ →+ EReal := ⟨⟨(↑), EReal.coe_zero⟩, EReal.coe_add⟩
  have hs := Finset.sum_le_sum fun k (_ : k ∈ Finset.univ) =>
    scalarObjectiveBits_le_classicalTermBits (p k) (q k) (r k) (hp k) (hq k) (hr k)
  change coeHom (∑ k, scalarObjectiveBits (p k) (q k) (r k)) ≤ _
  rw [map_sum]
  exact hs

theorem vectorObjectiveBits_normalized (p q r : K → ℝ) (hpsum : ∑ k, p k = 1) :
    vectorObjectiveBits p q r =
      ((∑ k, p k * Real.log (r k)) + 1 - ∑ k, q k * r k) / Real.log 2 := by
  simp only [vectorObjectiveBits, scalarObjectiveBits, ← Finset.sum_div,
    Finset.sum_sub_distrib, Finset.sum_add_distrib, hpsum]

theorem trace_log_jensen {Phi : Mat I →ₗ[ℂ] Mat O}
    (hPhi : CompletelyPositive Phi) (hu : Phi 1 = 1) {X : Mat I} (hX : X.PosDef)
    {rho : Mat O} (hRho : rho.PosSemidef) :
    (rho * Phi (cfc Real.log X)).trace.re ≤ (rho * cfc Real.log (Phi X)).trace.re := by
  have h := trace_mul_re_nonneg hRho (CPJensen.operator_log_jensen hPhi hu hX)
  simp only [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re] at h
  exact sub_nonneg.mp h

def vectorVariationalValues (p q : K → ℝ) : Set EReal :=
  {z | ∃ r : K → ℝ, (∀ k, 0 < r k) ∧ z = (vectorObjectiveBits p q r : EReal)}

theorem classicalRelativeEntropyBits_finite_of_support (p q : K → ℝ)
    (hs : ∀ k, p k ≠ 0 → q k ≠ 0) :
    classicalRelativeEntropyBits p q =
      ((∑ k, p k * (Real.log (p k) - Real.log (q k)) / Real.log 2 : ℝ) : EReal) := by
  classical
  let coeHom : ℝ →+ EReal := ⟨⟨(↑), EReal.coe_zero⟩, EReal.coe_add⟩
  have hterm (k : K) : classicalTermBits (p k) (q k) =
      ((p k * (Real.log (p k) - Real.log (q k)) / Real.log 2 : ℝ) : EReal) := by
    by_cases hp0 : p k = 0
    · simp [classicalTermBits, hp0]
    · simp only [classicalTermBits, if_neg hp0, if_neg (hs k hp0)]
  simp only [classicalRelativeEntropyBits, hterm]
  exact (map_sum coeHom _ _).symm

def epsilonTests (p q : K → ℝ) (eps : ℝ) : K → ℝ :=
  fun k => if p k = 0 then eps else p k / q k

theorem epsilonTests_pos (p q : K → ℝ) (eps : ℝ)
    (hp : ∀ k, 0 ≤ p k) (hq : ∀ k, 0 ≤ q k)
    (hs : ∀ k, p k ≠ 0 → q k ≠ 0) (heps : 0 < eps) :
    ∀ k, 0 < epsilonTests p q eps k := by
  intro k
  by_cases hp0 : p k = 0
  · simp only [epsilonTests, if_pos hp0]
    exact heps
  · simp only [epsilonTests, if_neg hp0]
    exact div_pos (lt_of_le_of_ne (hp k) (Ne.symm hp0))
      (lt_of_le_of_ne (hq k) (Ne.symm (hs k hp0)))

theorem epsilonTests_term (p q : K → ℝ) (eps : ℝ)
    (hp : ∀ k, 0 ≤ p k) (hq : ∀ k, 0 ≤ q k)
    (hs : ∀ k, p k ≠ 0 → q k ≠ 0) (k : K) :
    scalarObjectiveBits (p k) (q k) (epsilonTests p q eps k) =
      p k * (Real.log (p k) - Real.log (q k)) / Real.log 2 -
        eps * (if p k = 0 then q k else 0) / Real.log 2 := by
  by_cases hp0 : p k = 0
  · simp [scalarObjectiveBits, epsilonTests, hp0]
    ring
  · rw [epsilonTests, if_neg hp0, scalarObjectiveBits_optimum _ _
      (lt_of_le_of_ne (hp k) (Ne.symm hp0))
      (lt_of_le_of_ne (hq k) (Ne.symm (hs k hp0))), if_neg hp0]
    simp

theorem epsilonTests_objective (p q : K → ℝ) (eps : ℝ)
    (hp : ∀ k, 0 ≤ p k) (hq : ∀ k, 0 ≤ q k)
    (hs : ∀ k, p k ≠ 0 → q k ≠ 0) :
    vectorObjectiveBits p q (epsilonTests p q eps) =
      (∑ k, p k * (Real.log (p k) - Real.log (q k)) / Real.log 2) -
        eps * (∑ k, if p k = 0 then q k else 0) / Real.log 2 := by
  simp only [vectorObjectiveBits, epsilonTests_term p q eps hp hq hs,
    Finset.sum_sub_distrib, ← Finset.sum_div, ← Finset.mul_sum]

variable [DecidableEq K]

theorem mismatchTests_objective (p q : K → ℝ) (k : K) (t : ℝ) (hq0 : q k = 0) :
    vectorObjectiveBits p q (fun j => if j = k then Real.exp t else 1) =
      (p k * t + ∑ j, p j - ∑ j, q j) / Real.log 2 := by
  classical
  have hl : ∑ j, p j * Real.log (if j = k then Real.exp t else 1) = p k * t := by
    simp [apply_ite, mul_ite]
  have hq : ∑ j, q j * (if j = k then Real.exp t else 1) = ∑ j, q j := by
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : j = k
    · simp [hj, hq0]
    · simp [hj]
  simp only [vectorObjectiveBits, scalarObjectiveBits, ← Finset.sum_div,
    Finset.sum_sub_distrib, Finset.sum_add_distrib, hl, hq]

theorem classicalRelativeEntropyBits_variational (p q : K → ℝ)
    (hp : ∀ k, 0 ≤ p k) (hq : ∀ k, 0 ≤ q k) :
    classicalRelativeEntropyBits p q = sSup (vectorVariationalValues p q) := by
  classical
  have hupper : sSup (vectorVariationalValues p q) ≤ classicalRelativeEntropyBits p q := by
    apply sSup_le
    rintro z ⟨r, hr, rfl⟩
    exact vectorObjectiveBits_le_classicalRelativeEntropyBits p q r hp hq hr
  apply le_antisymm _ hupper
  by_cases hs : ∀ k, p k ≠ 0 → q k ≠ 0
  · rw [classicalRelativeEntropyBits_finite_of_support p q hs]
    let D := ∑ k, p k * (Real.log (p k) - Real.log (q k)) / Real.log 2
    let C := ∑ k, if p k = 0 then q k else 0
    have hC : 0 ≤ C := Finset.sum_nonneg (fun k _ => by
      split_ifs
      · exact hq k
      · exact le_rfl)
    change (D : EReal) ≤ _
    by_contra hn
    obtain ⟨b, hb, hbD⟩ := EReal.exists_between_coe_real (lt_of_not_ge hn)
    have hbD' : b < D := EReal.coe_lt_coe_iff.mp hbD
    by_cases hC0 : C = 0
    · have heq : vectorObjectiveBits p q (epsilonTests p q 1) = D := by
        rw [epsilonTests_objective p q 1 hp hq hs]
        change D - 1 * C / Real.log 2 = D
        simp [hC0]
      have hm : (D : EReal) ≤ sSup (vectorVariationalValues p q) := by
        apply le_sSup
        exact ⟨epsilonTests p q 1, epsilonTests_pos p q 1 hp hq hs (by norm_num), by rw [heq]⟩
      exact not_lt_of_ge hm (lt_of_not_ge hn)
    · have hCpos : 0 < C := lt_of_le_of_ne hC (Ne.symm hC0)
      let eps := (D-b) * Real.log 2 / (2*C)
      have heps : 0 < eps := div_pos (mul_pos (sub_pos.mpr hbD') log_two_pos) (by positivity)
      have heq : vectorObjectiveBits p q (epsilonTests p q eps) = (D+b)/2 := by
        rw [epsilonTests_objective p q eps hp hq hs]
        change D - eps * C / Real.log 2 = (D+b)/2
        dsimp [eps]
        field_simp [hCpos.ne', log_two_pos.ne']
        <;> ring
      have hm : (((D+b)/2 : ℝ) : EReal) ≤ sSup (vectorVariationalValues p q) := by
        apply le_sSup
        exact ⟨epsilonTests p q eps, epsilonTests_pos p q eps hp hq hs heps, by rw [heq]⟩
      have hbb : (b : EReal) < (((D+b)/2 : ℝ) : EReal) :=
        EReal.coe_lt_coe_iff.mpr (by linarith)
      exact not_lt_of_ge hm (hb.trans hbb)
  · push_neg at hs
    obtain ⟨k, hpk, hqk⟩ := hs
    have hpkpos : 0 < p k := lt_of_le_of_ne (hp k) (Ne.symm hpk)
    have htop : sSup (vectorVariationalValues p q) = ⊤ := by
      apply le_antisymm le_top
      by_contra hn
      obtain ⟨b, hb, _⟩ := EReal.exists_between_coe_real (lt_of_not_ge hn)
      let t := (b * Real.log 2 - ∑ j, p j + ∑ j, q j) / p k + 1
      let r : K → ℝ := fun j => if j = k then Real.exp t else 1
      have hr : ∀ j, 0 < r j := by intro j; dsimp [r]; split_ifs <;> positivity
      have heq : vectorObjectiveBits p q r = b + p k / Real.log 2 := by
        rw [mismatchTests_objective p q k t hqk]
        dsimp [t]
        field_simp [hpkpos.ne', log_two_pos.ne']
        <;> ring
      have hm : ((b+p k/Real.log 2 : ℝ) : EReal) ≤ sSup (vectorVariationalValues p q) := by
        apply le_sSup
        exact ⟨r, hr, by rw [heq]⟩
      have hbb : (b : EReal) < ((b+p k/Real.log 2 : ℝ) : EReal) :=
        EReal.coe_lt_coe_iff.mpr (lt_add_of_pos_right _ (div_pos hpkpos log_two_pos))
      exact not_lt_of_ge hm (hb.trans hbb)
    rw [htop]
    exact le_top

def preparationMap (M : POVM I K) : Mat K →ₗ[ℂ] Mat I where
  toFun X := ∑ k, X k k • M.effect k
  map_add' X Y := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c X := by simp [mul_smul, Finset.smul_sum]

theorem preparationMap_apply (M : POVM I K) (X : Mat K) :
    preparationMap M X = ∑ k, X k k • M.effect k := rfl

theorem preparationMap_completelyPositive (M : POVM I K) :
    CompletelyPositive (preparationMap M) := by
  intro r A hA
  have heq : amplify (preparationMap M) (Fin r) A =
      ∑ k, M.effect k ⊗ₖ A.submatrix (fun j : Fin r => (k,j)) (fun j : Fin r => (k,j)) := by
    ext x y
    simp only [amplify, preparationMap, LinearMap.coe_mk, AddHom.coe_mk,
      Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Matrix.kronecker_apply,
      Matrix.submatrix_apply]
    apply Finset.sum_congr rfl
    intro k _
    exact mul_comm _ _
  rw [heq]
  exact Matrix.posSemidef_sum _ (fun k _ =>
    (M.positive k).kronecker (hA.submatrix (fun j : Fin r => (k,j))))

theorem preparationMap_unital (M : POVM I K) : preparationMap M 1 = 1 := by
  simpa [preparationMap] using M.normalized

def positiveDiagonal (r : K → ℝ) : Mat K := Matrix.diagonal (fun k => (r k : ℂ))

theorem positiveDiagonal_posDef (r : K → ℝ) (hr : ∀ k, 0 < r k) :
    (positiveDiagonal r).PosDef := by
  apply Matrix.PosDef.diagonal
  intro k
  exact Complex.zero_lt_real.mpr (hr k)

theorem preparationMap_positiveDiagonal (M : POVM I K) (r : K → ℝ) :
    preparationMap M (positiveDiagonal r) = ∑ k, (r k : ℂ) • M.effect k := by
  simp [preparationMap, positiveDiagonal]

theorem preparationMap_cfc_log_diagonal (M : POVM I K) (r : K → ℝ) :
    preparationMap M (cfc Real.log (positiveDiagonal r)) =
      ∑ k, (Real.log (r k) : ℂ) • M.effect k := by
  rw [positiveDiagonal, cfc_diagonal_real]
  simp [preparationMap]

theorem trace_preparationMap_diagonal (M : POVM I K) (A : Mat I) (r : K → ℝ) :
    (A * preparationMap M (positiveDiagonal r)).trace.re =
      ∑ k, measurementProbability M A k * r k := by
  rw [preparationMap_positiveDiagonal]
  simp only [Matrix.mul_sum, Matrix.mul_smul, Matrix.trace_sum, Matrix.trace_smul,
    Complex.re_sum, smul_eq_mul, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, measurementProbability]
  apply Finset.sum_congr rfl
  intro k _
  exact mul_comm _ _

theorem trace_preparationMap_log_diagonal (M : POVM I K) (A : Mat I) (r : K → ℝ) :
    (A * preparationMap M (cfc Real.log (positiveDiagonal r))).trace.re =
      ∑ k, measurementProbability M A k * Real.log (r k) := by
  rw [preparationMap_cfc_log_diagonal]
  simp only [Matrix.mul_sum, Matrix.mul_smul, Matrix.trace_sum, Matrix.trace_smul,
    Complex.re_sum, smul_eq_mul, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, measurementProbability]
  apply Finset.sum_congr rfl
  intro k _
  exact mul_comm _ _

theorem vectorObjectiveBits_le_matrixObjectiveBits (M : POVM I K)
    {rho sigma : Mat I} (hRho : IsDensity rho) (r : K → ℝ) (hr : ∀ k, 0 < r k) :
    vectorObjectiveBits (measurementProbability M rho) (measurementProbability M sigma) r ≤
      matrixObjectiveBits rho sigma (preparationMap M (positiveDiagonal r)) := by
  rw [vectorObjectiveBits_normalized _ _ _ (measurementProbability_sum_density M hRho)]
  unfold matrixObjectiveBits
  rw [← trace_preparationMap_log_diagonal, ← trace_preparationMap_diagonal]
  apply div_le_div_of_nonneg_right _ log_two_pos.le
  have hJ := trace_log_jensen (preparationMap_completelyPositive M)
    (preparationMap_unital M) (positiveDiagonal_posDef r hr) hRho.1
  linarith

theorem measuredRelativeEntropyBits_le_variational {rho sigma : Mat I}
    (hRho : IsDensity rho) (hSigma : sigma.PosSemidef) :
    measuredRelativeEntropyBits rho sigma ≤ variationalRelativeEntropyBits rho sigma := by
  apply sSup_le
  rintro z ⟨m, hm, M, rfl⟩
  rw [classicalRelativeEntropyBits_variational _ _
    (measurementProbability_nonneg M hRho.1) (measurementProbability_nonneg M hSigma)]
  apply sSup_le
  rintro z ⟨r, hr, rfl⟩
  apply (EReal.coe_le_coe_iff.mpr (vectorObjectiveBits_le_matrixObjectiveBits M hRho r hr)).trans
  apply le_sSup
  exact ⟨preparationMap M (positiveDiagonal r), CPJensen.map_posDef
    (preparationMap_completelyPositive M) (preparationMap_unital M)
    (positiveDiagonal_posDef r hr), rfl⟩

def basisProjection (k : I) : Mat I :=
  Matrix.diagonal (fun j => if j = k then (1 : ℂ) else 0)

theorem basisProjection_posSemidef (k : I) : (basisProjection k).PosSemidef := by
  apply Matrix.PosSemidef.diagonal
  intro j
  change (0 : ℂ) ≤ if j = k then 1 else 0
  split_ifs <;> positivity

theorem sum_basisProjection : ∑ k : I, basisProjection k = 1 := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [basisProjection, Matrix.sum_apply, Matrix.diagonal_apply]
  · simp [basisProjection, Matrix.sum_apply, Matrix.diagonal_apply, hij]

theorem weighted_basisProjection (r : I → ℝ) :
    ∑ k, (r k : ℂ) • basisProjection k = positiveDiagonal r := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [basisProjection, positiveDiagonal, Matrix.sum_apply, Matrix.diagonal_apply,
      Matrix.smul_apply, smul_eq_mul, mul_ite]
  · simp [basisProjection, positiveDiagonal, Matrix.sum_apply, Matrix.diagonal_apply, hij]

def unitaryPOVM (U : Matrix.unitaryGroup I ℂ) : POVM I I where
  effect k := (U : Mat I) * basisProjection k * (U : Mat I)ᴴ
  positive k := (basisProjection_posSemidef k).mul_mul_conjTranspose_same (U : Mat I)
  normalized := by
    rw [← Matrix.sum_mul, ← Matrix.mul_sum, sum_basisProjection, Matrix.mul_one]
    exact Unitary.coe_mul_star_self U

theorem unitaryPOVM_weighted (U : Matrix.unitaryGroup I ℂ) (r : I → ℝ) :
    ∑ k, (r k : ℂ) • (unitaryPOVM U).effect k =
      (U : Mat I) * positiveDiagonal r * (U : Mat I)ᴴ := by
  change (∑ k, (r k : ℂ) • ((U : Mat I) * basisProjection k * (U : Mat I)ᴴ)) = _
  calc
    _ = ∑ k, ((U : Mat I) * ((r k : ℂ) • basisProjection k)) * (U : Mat I)ᴴ := by
      apply Finset.sum_congr rfl
      intro k _
      simp only [Matrix.smul_mul, Matrix.mul_smul]
    _ = (U : Mat I) * (∑ k, (r k : ℂ) • basisProjection k) * (U : Mat I)ᴴ := by
      rw [Matrix.mul_sum, Matrix.sum_mul]
    _ = _ := by rw [weighted_basisProjection]

theorem trace_weighted_effects (M : POVM I K) (A : Mat I) (r : K → ℝ) :
    (A * ∑ k, (r k : ℂ) • M.effect k).trace.re =
      ∑ k, measurementProbability M A k * r k := by
  rw [← preparationMap_positiveDiagonal]
  exact trace_preparationMap_diagonal M A r

theorem spectralPOVM_reconstruct {Omega : Mat I} (hOmega : Omega.IsHermitian) :
    ∑ k, (hOmega.eigenvalues k : ℂ) • (unitaryPOVM hOmega.eigenvectorUnitary).effect k =
      Omega := by
  rw [unitaryPOVM_weighted]
  exact hOmega.spectral_theorem.symm

theorem spectralPOVM_reconstruct_log {Omega : Mat I} (hOmega : Omega.IsHermitian) :
    ∑ k, (Real.log (hOmega.eigenvalues k) : ℂ) •
      (unitaryPOVM hOmega.eigenvectorUnitary).effect k = cfc Real.log Omega := by
  rw [unitaryPOVM_weighted]
  exact (cfc_spectral Real.log hOmega).symm

theorem matrixObjectiveBits_eq_spectral {rho sigma Omega : Mat I}
    (hRho : IsDensity rho) (hOmega : Omega.PosDef) :
    matrixObjectiveBits rho sigma Omega =
      vectorObjectiveBits (measurementProbability (unitaryPOVM hOmega.1.eigenvectorUnitary) rho)
        (measurementProbability (unitaryPOVM hOmega.1.eigenvectorUnitary) sigma)
        hOmega.1.eigenvalues := by
  have hl : (rho * cfc Real.log Omega).trace.re =
      ∑ k, measurementProbability (unitaryPOVM hOmega.1.eigenvectorUnitary) rho k *
        Real.log (hOmega.1.eigenvalues k) := by
    rw [← spectralPOVM_reconstruct_log hOmega.1]
    exact trace_weighted_effects _ _ _
  have hs : (sigma * Omega).trace.re =
      ∑ k, measurementProbability (unitaryPOVM hOmega.1.eigenvectorUnitary) sigma k *
        hOmega.1.eigenvalues k := by
    simpa only [spectralPOVM_reconstruct hOmega.1] using
      (trace_weighted_effects (unitaryPOVM hOmega.1.eigenvectorUnitary) sigma hOmega.1.eigenvalues)
  rw [matrixObjectiveBits, hl, hs,
    vectorObjectiveBits_normalized _ _ _
      (measurementProbability_sum_density (unitaryPOVM hOmega.1.eigenvectorUnitary) hRho)]

def reindexPOVM (M : POVM I K) (e : O ≃ K) : POVM I O where
  effect k := M.effect (e k)
  positive k := M.positive (e k)
  normalized := (e.sum_comp M.effect).trans M.normalized

theorem classicalRelativeEntropyBits_reindex (M : POVM I K) (e : O ≃ K) (rho sigma : Mat I) :
    classicalRelativeEntropyBits (measurementProbability (reindexPOVM M e) rho)
      (measurementProbability (reindexPOVM M e) sigma) =
    classicalRelativeEntropyBits (measurementProbability M rho) (measurementProbability M sigma) := by
  exact e.sum_comp (fun k => classicalTermBits (measurementProbability M rho k)
    (measurementProbability M sigma k))

theorem dimension_pos_of_density {rho : Mat I} (hRho : IsDensity rho) :
    0 < Fintype.card I := by
  apply Fintype.card_pos_iff.mpr
  by_contra hn
  haveI : IsEmpty I := not_nonempty_iff.mp hn
  have ht : rho.trace = 0 := by simp [Matrix.trace]
  have h := hRho.2
  rw [ht] at h
  exact zero_ne_one h

theorem variationalRelativeEntropyBits_le_measured {rho sigma : Mat I}
    (hRho : IsDensity rho) (hSigma : sigma.PosSemidef) :
    variationalRelativeEntropyBits rho sigma ≤ measuredRelativeEntropyBits rho sigma := by
  apply sSup_le
  rintro z ⟨Omega, hOmega, rfl⟩
  rw [matrixObjectiveBits_eq_spectral hRho hOmega]
  apply (vectorObjectiveBits_le_classicalRelativeEntropyBits _ _ _
    (measurementProbability_nonneg _ hRho.1) (measurementProbability_nonneg _ hSigma)
    hOmega.eigenvalues_pos).trans
  let M := unitaryPOVM hOmega.1.eigenvectorUnitary
  let e : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
  apply le_sSup
  refine ⟨Fintype.card I, dimension_pos_of_density hRho, reindexPOVM M e, ?_⟩
  exact (classicalRelativeEntropyBits_reindex M e rho sigma).symm

theorem measuredRelativeEntropyBits_variational (rho sigma : Mat I)
    (hRho : IsDensity rho) (hSigma : sigma.PosSemidef) :
    measuredRelativeEntropyBits rho sigma =
      sSup {z : EReal | ∃ Omega : Mat I, Omega.PosDef ∧
        z = (((rho * cfc Real.log Omega).trace.re + 1 -
          (sigma * Omega).trace.re) / Real.log 2 : ℝ)} :=
  le_antisymm (measuredRelativeEntropyBits_le_variational hRho hSigma)
    (variationalRelativeEntropyBits_le_measured hRho hSigma)

theorem classicalTermBits_ne_bot (p q : ℝ) : classicalTermBits p q ≠ ⊥ := by
  unfold classicalTermBits
  split_ifs <;> simp

private theorem sum_classicalTermBits_ne_bot (p q : K → ℝ) (s : Finset K) :
    (∑ k ∈ s, classicalTermBits (p k) (q k)) ≠ ⊥ := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert k s hk ih =>
    rw [Finset.sum_insert hk, EReal.add_ne_bot_iff]
    exact ⟨classicalTermBits_ne_bot _ _, ih⟩

theorem classicalRelativeEntropyBits_eq_top_of_zero_reference_event (p q : K → ℝ)
    (k : K) (hp : 0 < p k) (hq : q k = 0) :
    classicalRelativeEntropyBits p q = ⊤ := by
  have hk : classicalTermBits (p k) (q k) = ⊤ := by
    simp [classicalTermBits, hp.ne', hq]
  unfold classicalRelativeEntropyBits
  rw [← Finset.sum_erase_add Finset.univ (fun j => classicalTermBits (p j) (q j))
    (Finset.mem_univ k), hk]
  exact EReal.add_top_of_ne_bot (sum_classicalTermBits_ne_bot p q (Finset.univ.erase k))

theorem measuredRelativeEntropyBits_eq_top_of_zero_reference_event
    {rho sigma : Mat I} {m : ℕ} (hm : 0 < m) (M : POVM I (Fin m)) (k : Fin m)
    (hp : 0 < measurementProbability M rho k) (hq : measurementProbability M sigma k = 0) :
    measuredRelativeEntropyBits rho sigma = ⊤ := by
  apply le_antisymm le_top
  apply le_sSup
  refine ⟨m, hm, M, ?_⟩
  exact (classicalRelativeEntropyBits_eq_top_of_zero_reference_event _ _ k hp hq).symm

theorem variationalRelativeEntropyBits_zero {rho : Mat I} (hRho : IsDensity rho) :
    variationalRelativeEntropyBits rho 0 = ⊤ := by
  apply le_antisymm le_top
  have h := measuredRelativeEntropyBits_le_variational hRho Matrix.PosSemidef.zero
  simpa only [measuredRelativeEntropyBits_zero hRho] using h

theorem measuredRelativeEntropyBits_variational_density (rho sigma : Mat I)
    (hRho : IsDensity rho) (hSigma : IsDensity sigma) :
    measuredRelativeEntropyBits rho sigma = variationalRelativeEntropyBits rho sigma :=
  measuredRelativeEntropyBits_variational rho sigma hRho hSigma.1

end QuantumProver.MeasuredRelativeEntropyVariational

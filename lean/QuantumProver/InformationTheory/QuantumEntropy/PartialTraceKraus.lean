import QuantumProver.InformationTheory.QuantumEntropy.Definitions
import QuantumProver.InformationTheory.QuantumEntropy.TensorReindex
import QuantumProver.InformationTheory.SuperchannelDiscrimination.TestingTheorems

set_option autoImplicit false

noncomputable section

open Matrix
open QuantumProver.SuperchannelDiscrimination.FlaggedStates
open QuantumProver.SuperchannelDiscrimination.KrausCompletion
open QuantumProver.SuperchannelDiscrimination.TensorEntropy
open QuantumProver.SuperchannelDiscrimination.OutputSupport
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker Matrix

namespace QuantumProver.QuantumEntropy

variable {I J A B C : Type*} [Fintype I] [Fintype J]
  [Fintype A] [Fintype B] [Fintype C]
  [DecidableEq I] [DecidableEq J] [DecidableEq A] [DecidableEq B] [DecidableEq C]

def rightTraceKraus (j : J) : Matrix I (I × J) ℂ :=
  fun i x => if x.2 = j then (1 : Matrix I I ℂ) i x.1 else 0

def leftTraceKraus (i : I) : Matrix J (I × J) ℂ :=
  fun j x => if x.1 = i then (1 : Matrix J J ℂ) j x.2 else 0

theorem rightTraceKraus_complete :
    krausGram (rightTraceKraus (I := I) (J := J)) = 1 := by
  ext ⟨i, j⟩ ⟨i', j'⟩
  by_cases hi : i = i' <;> by_cases hj : j = j' <;>
    simp [krausGram, rightTraceKraus, Matrix.sum_apply, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Matrix.one_apply, hi, hj, Prod.ext_iff,
      apply_ite, mul_ite, ite_mul]
  all_goals exact Ne.symm (by assumption)

theorem leftTraceKraus_complete :
    krausGram (leftTraceKraus (I := I) (J := J)) = 1 := by
  ext ⟨i, j⟩ ⟨i', j'⟩
  by_cases hi : i = i' <;> by_cases hj : j = j' <;>
    simp [krausGram, leftTraceKraus, Matrix.sum_apply, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Matrix.one_apply, hi, hj, Prod.ext_iff,
      apply_ite, mul_ite, ite_mul]
  all_goals exact Ne.symm (by assumption)

theorem rightTraceKraus_action (R : Matrix (I × J) (I × J) ℂ) :
    krausAction rightTraceKraus R = partialTrace_right R := by
  ext i i'
  simp [krausAction, rightTraceKraus, partialTrace_right, Matrix.sum_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.one_apply, Fintype.sum_prod_type,
    apply_ite, mul_ite, ite_mul]

theorem leftTraceKraus_action (R : Matrix (I × J) (I × J) ℂ) :
    krausAction leftTraceKraus R = partialTrace_left R := by
  ext j j'
  simp [krausAction, leftTraceKraus, partialTrace_left, Matrix.sum_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.one_apply, Fintype.sum_prod_type,
    apply_ite, mul_ite, ite_mul]

theorem partialTraceRight_posSemidef {R : Matrix (I × J) (I × J) ℂ}
    (hR : R.PosSemidef) : (partialTrace_right R).PosSemidef := by
  rw [← rightTraceKraus_action]
  exact krausAction_posSemidef rightTraceKraus hR

theorem partialTraceLeft_posSemidef {R : Matrix (I × J) (I × J) ℂ}
    (hR : R.PosSemidef) : (partialTrace_left R).PosSemidef := by
  rw [← leftTraceKraus_action]
  exact krausAction_posSemidef leftTraceKraus hR

@[simp] theorem trace_partialTraceRight (R : Matrix (I × J) (I × J) ℂ) :
    (partialTrace_right R).trace = R.trace := by
  rw [← rightTraceKraus_action]
  exact krausAction_tracePreserving rightTraceKraus rightTraceKraus_complete R

@[simp] theorem trace_partialTraceLeft (R : Matrix (I × J) (I × J) ℂ) :
    (partialTrace_left R).trace = R.trace := by
  rw [← leftTraceKraus_action]
  exact krausAction_tracePreserving leftTraceKraus leftTraceKraus_complete R

theorem partialTraceRight_isDensity {R : Matrix (I × J) (I × J) ℂ}
    (hR : IsDensity R) : IsDensity (partialTrace_right R) :=
  ⟨partialTraceRight_posSemidef hR.1, (trace_partialTraceRight R).trans hR.2⟩

theorem partialTraceLeft_isDensity {R : Matrix (I × J) (I × J) ℂ}
    (hR : IsDensity R) : IsDensity (partialTrace_left R) :=
  ⟨partialTraceLeft_posSemidef hR.1, (trace_partialTraceLeft R).trans hR.2⟩

theorem partialTrace_right_mul_trace (R : Matrix (I × J) (I × J) ℂ)
    (X : Matrix I I ℂ) :
    (R * (X ⊗ₖ (1 : Matrix J J ℂ))).trace = (partialTrace_right R * X).trace := by
  calc
    _ = ∑ i, ∑ j, ∑ i', R (i, j) (i', j) * X i' i := by
      simp [Matrix.trace, Matrix.mul_apply, Matrix.kronecker_apply,
        Matrix.one_apply, Fintype.sum_prod_type, mul_ite]
    _ = ∑ i, ∑ i', ∑ j, R (i, j) (i', j) * X i' i := by
      apply Finset.sum_congr rfl
      intro i hi
      exact Finset.sum_comm
    _ = _ := by simp [Matrix.trace, Matrix.mul_apply, partialTrace_right, Finset.sum_mul]

theorem partialTrace_left_mul_trace (R : Matrix (I × J) (I × J) ℂ)
    (Y : Matrix J J ℂ) :
    (R * ((1 : Matrix I I ℂ) ⊗ₖ Y)).trace = (partialTrace_left R * Y).trace := by
  calc
    _ = ∑ i, ∑ j, ∑ j', R (i, j) (i, j') * Y j' j := by
      simp [Matrix.trace, Matrix.mul_apply, Matrix.kronecker_apply,
        Matrix.one_apply, Fintype.sum_prod_type, mul_ite]
    _ = ∑ j, ∑ j', ∑ i, R (i, j) (i, j') * Y j' j := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j hj
      exact Finset.sum_comm
    _ = _ := by simp [Matrix.trace, Matrix.mul_apply, partialTrace_left, Finset.sum_mul]

theorem partialTraceRight_kronecker (X : Matrix I I ℂ) (Y : Matrix J J ℂ) :
    partialTrace_right (X ⊗ₖ Y) = Y.trace • X := by
  ext i i'
  simp [partialTrace_right, Matrix.kronecker_apply, Matrix.trace, Finset.mul_sum, mul_comm]

theorem partialTraceLeft_kronecker (X : Matrix I I ℂ) (Y : Matrix J J ℂ) :
    partialTrace_left (X ⊗ₖ Y) = X.trace • Y := by
  ext j j'
  simp [partialTrace_left, Matrix.kronecker_apply, Matrix.trace, Finset.sum_mul]

theorem kraus_quadratic_sum {O κ : Type*} [Fintype O] [Fintype κ] [DecidableEq O]
    (K : κ → Matrix O I ℂ) (R : Matrix I I ℂ) (x : O → ℂ) :
    (∑ k, star ((K k)ᴴ *ᵥ x) ⬝ᵥ (R *ᵥ ((K k)ᴴ *ᵥ x))) =
      star x ⬝ᵥ (krausAction K R *ᵥ x) := by
  simp only [krausAction, Matrix.sum_mulVec, dotProduct_sum]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose,
    Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul]

theorem kraus_lift_kernel {O κ : Type*} [Fintype O] [Fintype κ] [DecidableEq O]
    (K : κ → Matrix O I ℂ) {R : Matrix I I ℂ} (hR : R.PosSemidef)
    (x : O → ℂ) (hx : krausAction K R *ᵥ x = 0) (k : κ) :
    R *ᵥ ((K k)ᴴ *ᵥ x) = 0 := by
  have hsum : (∑ j, star ((K j)ᴴ *ᵥ x) ⬝ᵥ (R *ᵥ ((K j)ᴴ *ᵥ x))) = 0 := by
    rw [kraus_quadratic_sum, hx]
    simp
  have hk : star ((K k)ᴴ *ᵥ x) ⬝ᵥ (R *ᵥ ((K k)ᴴ *ᵥ x)) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun j _ =>
      hR.dotProduct_mulVec_nonneg ((K j)ᴴ *ᵥ x))).mp hsum k (Finset.mem_univ k)
  exact hR.dotProduct_mulVec_zero_iff.mp hk

theorem mul_right_marginal_kernel {R : Matrix (I × J) (I × J) ℂ}
    (hR : R.PosSemidef) (Q : Matrix I I ℂ)
    (hQ : partialTrace_right R * Q = 0) :
    R * (Q ⊗ₖ (1 : Matrix J J ℂ)) = 0 := by
  ext ⟨i, j⟩ ⟨i', j'⟩
  have hcol : partialTrace_right R *ᵥ (fun k => Q k i') = 0 := by
    funext k
    exact congrArg (fun M : Matrix I I ℂ => M k i') hQ
  have hcol' : krausAction rightTraceKraus R *ᵥ (fun k => Q k i') = 0 := by
    rwa [rightTraceKraus_action]
  have hk := kraus_lift_kernel rightTraceKraus hR (fun k => Q k i') hcol' j'
  simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.kronecker_apply,
    rightTraceKraus, Matrix.conjTranspose_apply, Matrix.one_apply,
    Fintype.sum_prod_type, apply_ite, mul_ite, ite_mul] using congrFun hk (i, j)

theorem mul_left_marginal_kernel {R : Matrix (I × J) (I × J) ℂ}
    (hR : R.PosSemidef) (Q : Matrix J J ℂ)
    (hQ : partialTrace_left R * Q = 0) :
    R * ((1 : Matrix I I ℂ) ⊗ₖ Q) = 0 := by
  ext ⟨i, j⟩ ⟨i', j'⟩
  have hcol : partialTrace_left R *ᵥ (fun k => Q k j') = 0 := by
    funext k
    exact congrArg (fun M : Matrix J J ℂ => M k j') hQ
  have hcol' : krausAction leftTraceKraus R *ᵥ (fun k => Q k j') = 0 := by
    rwa [leftTraceKraus_action]
  have hk := kraus_lift_kernel leftTraceKraus hR (fun k => Q k j') hcol' i'
  simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.kronecker_apply,
    leftTraceKraus, Matrix.conjTranspose_apply, Matrix.one_apply,
    Fintype.sum_prod_type, apply_ite, mul_ite, ite_mul] using congrFun hk (i, j)

theorem hasSupportIn_marginal_tensor {R : Matrix (I × J) (I × J) ℂ}
    (hR : R.PosSemidef) :
    HasSupportIn R (partialTrace_right R ⊗ₖ partialTrace_left R) := by
  let X := partialTrace_right R
  let Y := partialTrace_left R
  have hX : X.IsHermitian := (partialTraceRight_posSemidef hR).1
  have hY : Y.IsHermitian := (partialTraceLeft_posSemidef hR).1
  have hRX : R * (supportProjection X ⊗ₖ (1 : Matrix J J ℂ)) = R := by
    have hz := mul_right_marginal_kernel hR (1 - supportProjection X) (by
      change X * (1 - supportProjection X) = 0
      rw [Matrix.mul_sub, Matrix.mul_one, supportProjection_mul X hX, sub_self])
    have hsub : (1 - supportProjection X) ⊗ₖ (1 : Matrix J J ℂ) =
        1 - supportProjection X ⊗ₖ (1 : Matrix J J ℂ) := by
      calc
        _ = (1 : Matrix I I ℂ) ⊗ₖ (1 : Matrix J J ℂ) -
            supportProjection X ⊗ₖ (1 : Matrix J J ℂ) := by
          ext i j
          simp only [Matrix.kroneckerMap_apply, Matrix.sub_apply, sub_mul]
        _ = _ := by rw [Matrix.one_kronecker_one]
    rw [hsub, Matrix.mul_sub, Matrix.mul_one] at hz
    exact (sub_eq_zero.mp hz).symm
  have hRY : R * ((1 : Matrix I I ℂ) ⊗ₖ supportProjection Y) = R := by
    have hz := mul_left_marginal_kernel hR (1 - supportProjection Y) (by
      change Y * (1 - supportProjection Y) = 0
      rw [Matrix.mul_sub, Matrix.mul_one, supportProjection_mul Y hY, sub_self])
    have hsub : (1 : Matrix I I ℂ) ⊗ₖ (1 - supportProjection Y) =
        1 - (1 : Matrix I I ℂ) ⊗ₖ supportProjection Y := by
      calc
        _ = (1 : Matrix I I ℂ) ⊗ₖ (1 : Matrix J J ℂ) -
            (1 : Matrix I I ℂ) ⊗ₖ supportProjection Y := by
          ext i j
          simp only [Matrix.kroneckerMap_apply, Matrix.sub_apply, mul_sub]
        _ = _ := by rw [Matrix.one_kronecker_one]
    rw [hsub, Matrix.mul_sub, Matrix.mul_one] at hz
    exact (sub_eq_zero.mp hz).symm
  apply (hasSupportIn_iff_mul_supportProjection (isHermitian_kronecker hX hY)).mpr
  rw [supportProjection_kronecker hX hY]
  calc
    R * (supportProjection X ⊗ₖ supportProjection Y) =
        R * ((supportProjection X ⊗ₖ (1 : Matrix J J ℂ)) *
          ((1 : Matrix I I ℂ) ⊗ₖ supportProjection Y)) := by
      rw [← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul]
    _ = R := by rw [← Matrix.mul_assoc, hRX, hRY]

theorem mul_right_marginal_supportProjection
    {R : Matrix (I × J) (I × J) ℂ} (hR : R.PosSemidef) :
    R * ((1 : Matrix I I ℂ) ⊗ₖ supportProjection (partialTrace_left R)) = R := by
  let Y := partialTrace_left R
  let Z := partialTrace_right R
  have hY : Y.IsHermitian := (partialTraceLeft_posSemidef hR).1
  have hZ : Z.IsHermitian := (partialTraceRight_posSemidef hR).1
  have hRZ : R * (supportProjection Z ⊗ₖ supportProjection Y) = R := by
    have h := (hasSupportIn_iff_mul_supportProjection (isHermitian_kronecker hZ hY)).mp
      (hasSupportIn_marginal_tensor hR)
    rwa [supportProjection_kronecker hZ hY] at h
  calc
    _ = (R * (supportProjection Z ⊗ₖ supportProjection Y)) *
        ((1 : Matrix I I ℂ) ⊗ₖ supportProjection Y) := by rw [hRZ]
    _ = R * (supportProjection Z ⊗ₖ supportProjection Y) := by
      rw [Matrix.mul_assoc, ← Matrix.mul_kronecker_mul, Matrix.mul_one,
        supportProjection_idempotent hY]
    _ = R := hRZ

theorem mul_left_marginal_supportProjection
    {R : Matrix (I × J) (I × J) ℂ} (hR : R.PosSemidef) :
    R * (supportProjection (partialTrace_right R) ⊗ₖ (1 : Matrix J J ℂ)) = R := by
  let Y := partialTrace_left R
  let Z := partialTrace_right R
  have hY : Y.IsHermitian := (partialTraceLeft_posSemidef hR).1
  have hZ : Z.IsHermitian := (partialTraceRight_posSemidef hR).1
  have hRZ : R * (supportProjection Z ⊗ₖ supportProjection Y) = R := by
    have h := (hasSupportIn_iff_mul_supportProjection (isHermitian_kronecker hZ hY)).mp
      (hasSupportIn_marginal_tensor hR)
    rwa [supportProjection_kronecker hZ hY] at h
  calc
    _ = (R * (supportProjection Z ⊗ₖ supportProjection Y)) *
        (supportProjection Z ⊗ₖ (1 : Matrix J J ℂ)) := by rw [hRZ]
    _ = R * (supportProjection Z ⊗ₖ supportProjection Y) := by
      rw [Matrix.mul_assoc, ← Matrix.mul_kronecker_mul, Matrix.mul_one,
        supportProjection_idempotent hZ]
    _ = R := hRZ

theorem right_marginal_supportProjection_mul
    {R : Matrix (I × J) (I × J) ℂ} (hR : R.PosSemidef) :
    ((1 : Matrix I I ℂ) ⊗ₖ supportProjection (partialTrace_left R)) * R = R := by
  have h := congrArg Matrix.conjTranspose (mul_right_marginal_supportProjection hR)
  simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_kronecker,
    Matrix.conjTranspose_one, (supportProjection_isHermitian
      (partialTraceLeft_posSemidef hR).1).eq, hR.1.eq] using h

theorem left_marginal_supportProjection_mul
    {R : Matrix (I × J) (I × J) ℂ} (hR : R.PosSemidef) :
    (supportProjection (partialTrace_right R) ⊗ₖ (1 : Matrix J J ℂ)) * R = R := by
  have h := congrArg Matrix.conjTranspose (mul_left_marginal_supportProjection hR)
  simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_kronecker,
    Matrix.conjTranspose_one, (supportProjection_isHermitian
      (partialTraceRight_posSemidef hR).1).eq, hR.1.eq] using h

theorem hasSupportIn_faithful_left_tensor_marginal
    {R : Matrix (I × J) (I × J) ℂ} (hR : R.PosSemidef)
    {X : Matrix I I ℂ} (hX : X.PosDef) :
    HasSupportIn R (X ⊗ₖ partialTrace_left R) := by
  have hY := (partialTraceLeft_posSemidef hR).1
  apply (hasSupportIn_iff_mul_supportProjection (isHermitian_kronecker hX.1 hY)).mpr
  rw [supportProjection_kronecker hX.1 hY,
    QuantumProver.SuperchannelDiscrimination.ModularMatrix.supportProjection_posDef hX]
  exact mul_right_marginal_supportProjection hR

theorem marginalB_eq_partialTraceRight_marginalBC
    (R : Matrix (A × (B × C)) (A × (B × C)) ℂ) :
    marginalB R = partialTrace_right (marginalBC R) := by
  ext b b'
  simp only [marginalB, marginalAB, marginalBC, partialTrace_left, partialTrace_right]
  exact Finset.sum_comm

theorem partialTraceRight_marginalAB
    (R : Matrix (A × (B × C)) (A × (B × C)) ℂ) :
    partialTrace_right (marginalAB R) = marginalA R := by
  ext a a'
  simp [partialTrace_right, marginalAB, marginalA, Fintype.sum_prod_type]

def traceCKraus (c : C) : Matrix (A × B) (A × (B × C)) ℂ :=
  fun ab abc => rightTraceKraus c ab ((abc.1, abc.2.1), abc.2.2)

theorem traceCKraus_action (R : Matrix (A × (B × C)) (A × (B × C)) ℂ) :
    krausAction traceCKraus R = marginalAB R := by
  ext ⟨a, b⟩ ⟨a', b'⟩
  simp [krausAction, traceCKraus, rightTraceKraus, marginalAB,
    Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply,
    Fintype.sum_prod_type, apply_ite, ite_and, mul_ite, ite_mul, Prod.ext_iff]

theorem traceCKraus_complete :
    krausGram (traceCKraus (A := A) (B := B) (C := C)) = 1 := by
  ext ⟨a, b, c⟩ ⟨a', b', c'⟩
  by_cases ha : a = a' <;> by_cases hb : b = b' <;> by_cases hc : c = c' <;>
    simp [krausGram, traceCKraus, rightTraceKraus, Matrix.sum_apply, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Matrix.one_apply, Fintype.sum_prod_type,
      ha, hb, hc, Prod.ext_iff, apply_ite, ite_and, mul_ite, ite_mul]
  all_goals simp_all [eq_comm]

theorem marginalAB_posSemidef {R : Matrix (A × (B × C)) (A × (B × C)) ℂ}
    (hR : R.PosSemidef) : (marginalAB R).PosSemidef := by
  rw [← traceCKraus_action]
  exact krausAction_posSemidef traceCKraus hR

@[simp] theorem trace_marginalAB (R : Matrix (A × (B × C)) (A × (B × C)) ℂ) :
    (marginalAB R).trace = R.trace := by
  rw [← traceCKraus_action]
  exact krausAction_tracePreserving traceCKraus traceCKraus_complete R

theorem marginalAB_isDensity {R : Matrix (A × (B × C)) (A × (B × C)) ℂ}
    (hR : IsDensity R) : IsDensity (marginalAB R) :=
  ⟨marginalAB_posSemidef hR.1, (trace_marginalAB R).trans hR.2⟩

theorem marginalA_isDensity {R : Matrix (A × (B × C)) (A × (B × C)) ℂ}
    (hR : IsDensity R) : IsDensity (marginalA R) := partialTraceRight_isDensity hR

theorem marginalBC_isDensity {R : Matrix (A × (B × C)) (A × (B × C)) ℂ}
    (hR : IsDensity R) : IsDensity (marginalBC R) := partialTraceLeft_isDensity hR

theorem marginalB_isDensity {R : Matrix (A × (B × C)) (A × (B × C)) ℂ}
    (hR : IsDensity R) : IsDensity (marginalB R) :=
  partialTraceLeft_isDensity (marginalAB_isDensity hR)

theorem hasSupportIn_tripartite_comparison
    {R : Matrix (A × (B × C)) (A × (B × C)) ℂ} (hR : R.PosSemidef) :
    HasSupportIn R (marginalA R ⊗ₖ marginalBC R) := hasSupportIn_marginal_tensor hR

theorem traceCKraus_kronecker (X : Matrix A A ℂ) (Y : Matrix (B × C) (B × C) ℂ) :
    krausAction traceCKraus (X ⊗ₖ Y) = X ⊗ₖ partialTrace_right Y := by
  rw [traceCKraus_action]
  ext ⟨a, b⟩ ⟨a', b'⟩
  simp [marginalAB, partialTrace_right, Matrix.kronecker_apply, Finset.mul_sum]

end QuantumProver.QuantumEntropy

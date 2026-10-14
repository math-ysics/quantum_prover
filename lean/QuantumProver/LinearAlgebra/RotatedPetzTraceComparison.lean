import QuantumProver.LinearAlgebra.FourMatrixGoldenThompson
import QuantumProver.InformationTheory.BellDiagonalSquashedEntanglement.ExtensionIdentities
import QuantumProver.InformationTheory.QuantumEntropy.PartialTraceKraus

noncomputable section

open Matrix NormedSpace MeasureTheory
open QuantumProver.FourMatrixGoldenThompson
open QuantumProver.BellDiagonalSquashedEntanglement
open QuantumProver.BellDiagonalSquashedEntanglement.RecoveryGeometry.PetzSupportMap
open QuantumProver.SuperchannelDiscrimination.TensorEntropy
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker

namespace QuantumProver.RotatedPetzTraceComparison

variable {I E : Type*} [Fintype I] [Fintype E] [DecidableEq I] [DecidableEq E]

local instance : NormedAlgebra ℚ (CMat I) :=
  NormedAlgebra.restrictScalars ℚ ℂ (CMat I)

local instance : NormedAlgebra ℚ (CMat (I × E)) :=
  NormedAlgebra.restrictScalars ℚ ℂ (CMat (I × E))

abbrev matrixLog (A : CMat I) : CMat I := cfc Real.log A

theorem matrixLog_isHermitian (A : CMat I) : (matrixLog A).IsHermitian :=
  cfc_predicate _ _

theorem exp_matrixLog {A : CMat I} (hA : A.PosDef) : exp (matrixLog A) = A := by
  simpa only [CFC.log] using CFC.exp_log A hA.isStrictlyPositive

theorem halfExp_matrixLog {A : CMat I} (hA : A.PosDef) :
    halfExp (matrixLog A) = CFC.sqrt A := by
  have hH : ((1 / 2 : ℂ) • matrixLog A).IsHermitian :=
    (matrixLog_isHermitian A).smul (by simp [IsSelfAdjoint])
  have hP : 0 ≤ halfExp (matrixLog A) := (exp_posDef hH).posSemidef.nonneg
  have hsq : halfExp (matrixLog A) * halfExp (matrixLog A) = A := by
    rw [halfExp_mul_self, exp_matrixLog hA]
  exact (CFC.sqrt_unique hsq hP).symm

theorem exp_real_smul_matrixLog (A : CMat I) (hA : A.IsHermitian) (r : ℝ) :
    exp (r • matrixLog A) = cfc (fun x : ℝ => Real.exp (r * Real.log x)) A := by
  have hH : (r • matrixLog A).IsHermitian :=
    (matrixLog_isHermitian A).smul (by simp [IsSelfAdjoint])
  rw [← CFC.real_exp_eq_normedSpace_exp (Matrix.isHermitian_iff_isSelfAdjoint.mp hH)]
  rw [← cfc_const_mul r Real.log A (A.finite_real_spectrum.continuousOn _)]
  exact (cfc_comp' Real.exp (fun x : ℝ => r * Real.log x) A
    Real.continuous_exp.continuousOn (A.finite_real_spectrum.continuousOn _) hA).symm

theorem halfExp_neg_matrixLog {A : CMat I} (hA : A.PosDef) :
    halfExp (-matrixLog A) = inverseRoot A := by
  have hscale : (1 / 2 : ℂ) • (-matrixLog A) = (-1 / 2 : ℝ) • matrixLog A := by
    ext i j
    change (1 / 2 : ℂ) * (-(matrixLog A i j)) =
      ((-1 / 2 : ℝ) : ℂ) * matrixLog A i j
    norm_num
  rw [halfExp, hscale, exp_real_smul_matrixLog A hA.1]
  unfold inverseRoot
  apply cfc_congr
  intro x hx
  dsimp only
  have hxpos : 0 < x := hA.isStrictlyPositive.spectrum_pos hx
  have he : (-1 / 2 : ℝ) * Real.log x = -Real.log (Real.sqrt x) := by
    rw [Real.log_sqrt hxpos.le]
    ring
  rw [he, Real.exp_neg, Real.exp_log (Real.sqrt_pos.mpr hxpos)]

theorem modularPhase_eq_imaginaryExp (A : CMat I) (t : ℝ) :
    (modularPhase A t : CMat I) = imaginaryExp (matrixLog A) t := by
  change exp (Complex.I • ((t / 2 : ℝ) • matrixLog A)) =
    exp ((Complex.I * (t : ℂ) / 2) • matrixLog A)
  congr 1
  ext i j
  change Complex.I * (((t / 2 : ℝ) : ℂ) * matrixLog A i j) =
    (Complex.I * (t : ℂ) / 2) * matrixLog A i j
  push_cast
  ring

theorem imaginaryExp_neg_matrixLog (A : CMat I) (t : ℝ) :
    imaginaryExp (-matrixLog A) t = (modularPhase A t : CMat I)ᴴ := by
  rw [modularPhase_eq_imaginaryExp]
  unfold imaginaryExp
  rw [← Matrix.exp_conjTranspose, Matrix.conjTranspose_smul,
    (matrixLog_isHermitian A).eq]
  congr 1
  simp [smul_neg, neg_smul, neg_div]

theorem E_t_matrixLog {A : CMat I} (hA : A.PosDef) (t : ℝ) :
    E_t (matrixLog A) t = (modularPhase A t : CMat I) * CFC.sqrt A := by
  rw [E_t_factorization_left, halfExp_matrixLog hA, modularPhase_eq_imaginaryExp]

theorem E_t_neg_matrixLog {A : CMat I} (hA : A.PosDef) (t : ℝ) :
    E_t (-matrixLog A) t = inverseRoot A * (modularPhase A t : CMat I)ᴴ := by
  rw [E_t_factorization, halfExp_neg_matrixLog hA, imaginaryExp_neg_matrixLog]

def liftRightHom : CMat I →ₐ[ℂ] CMat (I × E) where
  toFun A := A ⊗ₖ (1 : CMat E)
  map_zero' := by simp
  map_one' := Matrix.one_kronecker_one
  map_add' A B := Matrix.add_kronecker A B _
  map_mul' A B := by rw [← Matrix.mul_kronecker_mul, Matrix.mul_one]
  commutes' z := by
    simp only [Algebra.algebraMap_eq_smul_one, Matrix.smul_kronecker,
      Matrix.one_kronecker_one]

abbrev liftRight (A : CMat I) : CMat (I × E) := liftRightHom A

theorem exp_liftRight (A : CMat I) :
    exp (liftRight (E := E) A) = liftRight (E := E) (exp A) := by
  exact (NormedSpace.map_exp (liftRightHom (I := I) (E := E))
    liftRightHom.toLinearMap.continuous_of_finiteDimensional A).symm

theorem exp_liftRight_matrixLog {A : CMat I} (hA : A.PosDef) :
    exp (liftRight (E := E) (matrixLog A)) = liftRight (E := E) A := by
  rw [exp_liftRight, exp_matrixLog hA]

theorem E_t_liftRight (A : CMat I) (t : ℝ) :
    E_t (liftRight (E := E) A) t = liftRight (E := E) (E_t A t) := by
  unfold E_t
  rw [← map_smul, exp_liftRight]

theorem E_t_neg_liftRight_matrixLog {A : CMat I} (hA : A.PosDef) (t : ℝ) :
    E_t (-(liftRight (E := E) (matrixLog A))) t =
      liftRight (E := E) (inverseRoot A * (modularPhase A t : CMat I)ᴴ) := by
  rw [← map_neg, E_t_liftRight, E_t_neg_matrixLog hA]

theorem liftRight_mul (A B : CMat I) :
    liftRight (E := E) (A * B) = liftRight (E := E) A * liftRight (E := E) B :=
  map_mul liftRightHom A B

theorem liftRight_conjTranspose (A : CMat I) :
    (liftRight (E := E) A)ᴴ = liftRight (E := E) Aᴴ := by
  change (A ⊗ₖ (1 : CMat E))ᴴ = Aᴴ ⊗ₖ (1 : CMat E)
  rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one]

theorem liftRight_isHermitian {A : CMat I} (hA : A.IsHermitian) :
    (liftRight (E := E) A).IsHermitian :=
  isHermitian_kronecker hA Matrix.isHermitian_one

def rotatedPetzMatrix (σ : CMat (I × E)) (A : CMat I) (t : ℝ) : CMat (I × E) :=
  let τ := partialTraceRight σ
  let U := (modularPhase σ t : CMat (I × E))
  let W := (modularPhase τ t : CMat I)
  U * CFC.sqrt σ *
    liftRight (inverseRoot τ * Wᴴ * A * W * inverseRoot τ) *
    CFC.sqrt σ * Uᴴ

set_option maxHeartbeats 1600000 in

theorem fourMatrixIntegrand_eq_rotatedPetzTrace
    (σ Ω : CMat (I × E)) (A : CMat I)
    (hσ : σ.PosDef) (hτ : (partialTraceRight σ).PosDef)
    (hA : A.PosDef) (hΩ : Ω.PosDef) (t : ℝ) :
    fourMatrixIntegrand (matrixLog Ω) (matrixLog σ)
      (-(liftRight (matrixLog (partialTraceRight σ))))
      (liftRight (matrixLog A)) t =
      (Ω * rotatedPetzMatrix σ A t).trace.re := by
  let τ := partialTraceRight σ
  let U := (modularPhase σ t : CMat (I × E))
  let W := (modularPhase τ t : CMat I)
  let R := inverseRoot τ
  have hT : liftRight (E := E) (R * Wᴴ) * liftRight (E := E) A *
      liftRight (E := E) (W * R) =
      liftRight (E := E) (R * Wᴴ * A * W * R) := by
    rw [← liftRight_mul, ← liftRight_mul]
    congr 1
    noncomm_ring
  have hroot : (CFC.sqrt σ)ᴴ = CFC.sqrt σ := (CFC.sqrt_nonneg σ).posSemidef.1.eq
  unfold fourMatrixIntegrand
  rw [exp_matrixLog hΩ, E_t_matrixLog hσ,
    E_t_neg_liftRight_matrixLog hτ, exp_liftRight_matrixLog hA]
  simp only [liftRight_conjTranspose, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose,
    (inverseRoot_isHermitian (partialTraceRight σ)).eq, hroot]
  dsimp only [rotatedPetzMatrix]
  change (Ω * (U * CFC.sqrt σ) * liftRight (R * Wᴴ) * liftRight A *
      liftRight (W * R) * (CFC.sqrt σ * Uᴴ)).trace.re =
    (Ω * (U * CFC.sqrt σ * liftRight (R * Wᴴ * A * W * R) *
      CFC.sqrt σ * Uᴴ)).trace.re
  apply congrArg (fun M : CMat (I × E) => M.trace.re)
  calc
    _ = Ω * (U * CFC.sqrt σ) *
        (liftRight (R * Wᴴ) * liftRight A * liftRight (W * R)) *
        (CFC.sqrt σ * Uᴴ) := by noncomm_ring
    _ = _ := by rw [hT]; noncomm_ring

theorem trace_exp_le_weighted_rotatedPetzTrace
    (σ Ω : CMat (I × E)) (A : CMat I)
    (hσ : σ.PosDef) (hτ : (partialTraceRight σ).PosDef)
    (hA : A.PosDef) (hΩ : Ω.PosDef) :
    (exp (matrixLog Ω + matrixLog σ -
      liftRight (matrixLog (partialTraceRight σ)) + liftRight (matrixLog A))).trace.re ≤
      ∫ t : ℝ, SBTProbabilityWeight.beta0 t *
        (Ω * rotatedPetzMatrix σ A t).trace.re ∂volume := by
  have hgt := four_matrix_gt (matrixLog Ω) (matrixLog σ)
    (-(liftRight (matrixLog (partialTraceRight σ)))) (liftRight (matrixLog A))
    (matrixLog_isHermitian Ω) (matrixLog_isHermitian σ)
    (liftRight_isHermitian (matrixLog_isHermitian (partialTraceRight σ))).neg
    (liftRight_isHermitian (matrixLog_isHermitian A))
  simp_rw [fourMatrixIntegrand_eq_rotatedPetzTrace σ Ω A hσ hτ hA hΩ] at hgt
  simpa only [sub_eq_add_neg] using hgt

theorem integrable_weighted_rotatedPetzTrace
    (σ Ω : CMat (I × E)) (A : CMat I)
    (hσ : σ.PosDef) (hτ : (partialTraceRight σ).PosDef)
    (hA : A.PosDef) (hΩ : Ω.PosDef) :
    Integrable (fun t : ℝ => SBTProbabilityWeight.beta0 t *
      (Ω * rotatedPetzMatrix σ A t).trace.re) volume := by
  have h := integrable_weighted_fourMatrixIntegrand
    (matrixLog Ω) (matrixLog σ)
    (-(liftRight (matrixLog (partialTraceRight σ)))) (liftRight (matrixLog A))
    (matrixLog_isHermitian σ)
    (liftRight_isHermitian (matrixLog_isHermitian (partialTraceRight σ))).neg
  simpa only [fourMatrixIntegrand_eq_rotatedPetzTrace σ Ω A hσ hτ hA hΩ] using h

end QuantumProver.RotatedPetzTraceComparison

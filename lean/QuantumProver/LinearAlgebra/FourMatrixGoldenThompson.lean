import Mathlib
import QuantumProver.LinearAlgebra.SBTProbabilityWeight
import QuantumProver.LinearAlgebra.HirschmanInterpolation
import QuantumProver.InformationTheory.BellDiagonalSquashedEntanglement.ScalarOptimization
import QuantumProver.LinearAlgebra.PPTSupport.SupportBounds

noncomputable section

open Matrix NormedSpace MeasureTheory Filter Set
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator Topology

namespace QuantumProver.FourMatrixGoldenThompson

variable {I : Type*} [Fintype I] [DecidableEq I]

abbrev CMat (I : Type*) := Matrix I I ℂ

local instance : NormedAlgebra ℚ (CMat I) :=
  NormedAlgebra.restrictScalars ℚ ℂ (CMat I)

def halfExp (H : CMat I) : CMat I := exp ((1 / 2 : ℂ) • H)

def imaginaryExp (H : CMat I) (t : ℝ) : CMat I :=
  exp ((Complex.I * (t : ℂ) / 2) • H)

def E_t (H : CMat I) (t : ℝ) : CMat I :=
  exp ((((1 : ℂ) + Complex.I * (t : ℂ)) / 2) • H)

def fourMatrixIntegrand (H1 H2 H3 H4 : CMat I) (t : ℝ) : ℝ :=
  (exp H1 * E_t H2 t * E_t H3 t * exp H4 *
    (E_t H3 t)ᴴ * (E_t H2 t)ᴴ).trace.re

def gramFactor (H1 H2 H3 H4 : CMat I) (t : ℝ) : CMat I :=
  halfExp H1 * E_t H2 t * E_t H3 t * halfExp H4

def stripProduct (H1 H2 H3 H4 : CMat I) (z : ℂ) : CMat I :=
  exp ((z / 2) • H1) * exp ((z / 2) • H2) *
    exp ((z / 2) • H3) * exp ((z / 2) • H4)

theorem E_t_factorization (H : CMat I) (t : ℝ) :
    E_t H t = halfExp H * imaginaryExp H t := by
  have hc : ((1 : ℂ) + Complex.I * (t : ℂ)) / 2 =
      (1 / 2 : ℂ) + Complex.I * (t : ℂ) / 2 := by ring
  unfold E_t halfExp imaginaryExp
  rw [hc, add_smul, Matrix.exp_add_of_commute _ _
    (((Commute.refl H).smul_left (1 / 2 : ℂ)).smul_right
      (Complex.I * (t : ℂ) / 2))]

theorem imaginaryExp_mem_unitary {H : CMat I} (hH : H.IsHermitian) (t : ℝ) :
    imaginaryExp H t ∈ unitary (CMat I) := by
  have hc : Complex.I * (t : ℂ) / 2 ∈ skewAdjoint ℂ := by
    change star (Complex.I * (t : ℂ) / 2) = -(Complex.I * (t : ℂ) / 2)
    simp
    ring
  exact exp_mem_unitary_of_mem_skewAdjoint
    (IsSelfAdjoint.smul_mem_skewAdjoint hc
      (Matrix.isHermitian_iff_isSelfAdjoint.mp hH))

theorem norm_E_t {H : CMat I} (hH : H.IsHermitian) (t : ℝ) :
    ‖E_t H t‖ = ‖halfExp H‖ := by
  rw [E_t_factorization]
  exact CStarRing.norm_mul_mem_unitary _ (imaginaryExp_mem_unitary hH t)

theorem E_t_conjTranspose {H : CMat I} (hH : H.IsHermitian) (t : ℝ) :
    (E_t H t)ᴴ = exp ((((1 : ℂ) - Complex.I * (t : ℂ)) / 2) • H) := by
  rw [E_t, ← Matrix.exp_conjTranspose, Matrix.conjTranspose_smul, hH]
  congr 1
  simp [sub_eq_add_neg]

theorem halfExp_mul_self (H : CMat I) : halfExp H * halfExp H = exp H := by
  unfold halfExp
  rw [← Matrix.exp_add_of_commute _ _ (Commute.refl _), ← add_smul]
  norm_num

theorem halfExp_isHermitian {H : CMat I} (hH : H.IsHermitian) :
    (halfExp H).IsHermitian := by
  unfold halfExp
  apply Matrix.IsHermitian.exp
  apply hH.smul
  simp [IsSelfAdjoint]

theorem fourMatrixIntegrand_eq_gram (H1 H2 H3 H4 : CMat I)
    (h1 : H1.IsHermitian) (h4 : H4.IsHermitian) (t : ℝ) :
    fourMatrixIntegrand H1 H2 H3 H4 t =
      (gramFactor H1 H2 H3 H4 t * (gramFactor H1 H2 H3 H4 t)ᴴ).trace.re := by
  have ha : (halfExp H1)ᴴ = halfExp H1 := halfExp_isHermitian h1
  have hd : (halfExp H4)ᴴ = halfExp H4 := halfExp_isHermitian h4
  have hm : gramFactor H1 H2 H3 H4 t * (gramFactor H1 H2 H3 H4 t)ᴴ =
      halfExp H1 *
        (E_t H2 t * E_t H3 t * exp H4 * (E_t H3 t)ᴴ * (E_t H2 t)ᴴ) *
          halfExp H1 := by
    rw [← halfExp_mul_self H4]
    simp only [gramFactor, Matrix.conjTranspose_mul, ha, hd, Matrix.mul_assoc]
  unfold fourMatrixIntegrand
  rw [hm, Matrix.trace_mul_cycle (halfExp H1)
    (E_t H2 t * E_t H3 t * exp H4 * (E_t H3 t)ᴴ * (E_t H2 t)ᴴ)
    (halfExp H1), halfExp_mul_self]
  simp only [Matrix.mul_assoc]

theorem fourMatrixIntegrand_nonneg (H1 H2 H3 H4 : CMat I)
    (h1 : H1.IsHermitian) (h4 : H4.IsHermitian) (t : ℝ) :
    0 ≤ fourMatrixIntegrand H1 H2 H3 H4 t := by
  rw [fourMatrixIntegrand_eq_gram H1 H2 H3 H4 h1 h4 t]
  exact (Complex.nonneg_iff.mp
    (Matrix.posSemidef_self_mul_conjTranspose (gramFactor H1 H2 H3 H4 t)).trace_nonneg).1

theorem continuous_fourMatrixIntegrand (H1 H2 H3 H4 : CMat I) :
    Continuous (fourMatrixIntegrand H1 H2 H3 H4) := by
  unfold fourMatrixIntegrand E_t
  fun_prop

theorem differentiable_stripProduct (H1 H2 H3 H4 : CMat I) :
    Differentiable ℂ (stripProduct H1 H2 H3 H4) := by
  unfold stripProduct
  have h (H : CMat I) : Differentiable ℂ (fun z : ℂ => exp ((z / 2) • H)) :=
    (differentiable_exp_smul_const ℂ H).comp (differentiable_id.div_const 2)
  exact (((h H1).mul (h H2)).mul (h H3)).mul (h H4)

@[simp] theorem stripProduct_zero (H1 H2 H3 H4 : CMat I) :
    stripProduct H1 H2 H3 H4 0 = 1 := by
  simp [stripProduct]

theorem hasDerivAt_matrix_mul {f g : ℂ → CMat I} {f' g' : CMat I} {z : ℂ}
    (hf : HasDerivAt f f' z) (hg : HasDerivAt g g' z) :
    HasDerivAt (fun w => f w * g w) (f' * g z + f z * g') z := by
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  dsimp only [Matrix.mul_apply, Matrix.add_apply]
  simpa only [Finset.sum_fn, Pi.mul_apply, Finset.sum_apply, Finset.sum_add_distrib] using
    (HasDerivAt.sum (u := Finset.univ) fun k _ =>
      (hasDerivAt_pi.mp (hasDerivAt_pi.mp hf i) k).mul
        (hasDerivAt_pi.mp (hasDerivAt_pi.mp hg k) j))

theorem hasDerivAt_stripProduct_zero (H1 H2 H3 H4 : CMat I) :
    HasDerivAt (stripProduct H1 H2 H3 H4)
      ((1 / 2 : ℂ) • (H1 + H2 + H3 + H4)) 0 := by
  unfold stripProduct
  have h (H : CMat I) : HasDerivAt (fun z : ℂ => exp ((z / 2) • H))
      ((1 / 2 : ℂ) • H) 0 := by
    simpa only [div_eq_mul_inv, smul_smul, one_div, zero_mul, zero_smul, exp_zero, one_mul] using
      hasDerivAt_exp_smul_const ((1 / 2 : ℂ) • H) (0 : ℂ)
  simpa only [Pi.mul_apply, zero_div, zero_smul, exp_zero,
    mul_one, one_mul, smul_add] using
    hasDerivAt_matrix_mul (hasDerivAt_matrix_mul (hasDerivAt_matrix_mul (h H1) (h H2))
      (h H3)) (h H4)

theorem tendsto_stripProduct_firstOrder (H1 H2 H3 H4 : CMat I) :
    Tendsto (fun z : ℂ => z⁻¹ • (stripProduct H1 H2 H3 H4 z - 1))
      (𝓝[≠] 0) (𝓝 ((1 / 2 : ℂ) • (H1 + H2 + H3 + H4))) := by
  simpa only [zero_add, stripProduct_zero] using
    (hasDerivAt_stripProduct_zero H1 H2 H3 H4).tendsto_slope_zero

theorem stripProduct_imaginary_mem_unitary (H1 H2 H3 H4 : CMat I)
    (h1 : H1.IsHermitian) (h2 : H2.IsHermitian)
    (h3 : H3.IsHermitian) (h4 : H4.IsHermitian) (t : ℝ) :
    stripProduct H1 H2 H3 H4 (Complex.I * (t : ℂ)) ∈ unitary (CMat I) := by
  exact (unitary (CMat I)).mul_mem
    ((unitary (CMat I)).mul_mem
      ((unitary (CMat I)).mul_mem
        (imaginaryExp_mem_unitary h1 t) (imaginaryExp_mem_unitary h2 t))
      (imaginaryExp_mem_unitary h3 t))
    (imaginaryExp_mem_unitary h4 t)

theorem E_t_factorization_left (H : CMat I) (t : ℝ) :
    E_t H t = imaginaryExp H t * halfExp H := by
  rw [E_t_factorization]
  exact ((((Commute.refl H).smul_left (1 / 2 : ℂ)).smul_right
    (Complex.I * (t : ℂ) / 2)).exp).eq

theorem stripProduct_one_add_imaginary (H1 H2 H3 H4 : CMat I) (t : ℝ) :
    stripProduct H1 H2 H3 H4 (1 + Complex.I * (t : ℂ)) =
      imaginaryExp H1 t * gramFactor H1 H2 H3 H4 t * imaginaryExp H4 t := by
  change E_t H1 t * E_t H2 t * E_t H3 t * E_t H4 t = _
  rw [E_t_factorization_left H1 t, E_t_factorization H4 t]
  simp only [gramFactor, Matrix.mul_assoc]

theorem trace_gram_unitary_endpoints (U W V : CMat I)
    (hU : U ∈ unitary (CMat I)) (hV : V ∈ unitary (CMat I)) :
    (U * W * V * (U * W * V)ᴴ).trace = (W * Wᴴ).trace := by
  have hu : Uᴴ * U = 1 := Unitary.star_mul_self_of_mem hU
  have hv : V * Vᴴ = 1 := Unitary.mul_star_self_of_mem hV
  have hm : U * W * V * (U * W * V)ᴴ = U * (W * Wᴴ) * Uᴴ := by
    calc
      _ = U * W * (V * Vᴴ) * Wᴴ * Uᴴ := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [hv]; simp only [Matrix.mul_one, Matrix.mul_assoc]
  rw [hm, Matrix.trace_mul_cycle U (W * Wᴴ) Uᴴ, hu, Matrix.one_mul]

theorem stripProduct_boundary_trace (H1 H2 H3 H4 : CMat I)
    (h1 : H1.IsHermitian) (h4 : H4.IsHermitian) (t : ℝ) :
    (stripProduct H1 H2 H3 H4 (1 + Complex.I * (t : ℂ)) *
      (stripProduct H1 H2 H3 H4 (1 + Complex.I * (t : ℂ)))ᴴ).trace.re =
    fourMatrixIntegrand H1 H2 H3 H4 t := by
  rw [stripProduct_one_add_imaginary,
    trace_gram_unitary_endpoints _ _ _
      (imaginaryExp_mem_unitary h1 t) (imaginaryExp_mem_unitary h4 t)]
  exact (fourMatrixIntegrand_eq_gram H1 H2 H3 H4 h1 h4 t).symm

theorem exp_complex_scale_factorization (H : CMat I) (z : ℂ) :
    exp ((z / 2) • H) = exp (((z.re : ℂ) / 2) • H) * imaginaryExp H z.im := by
  have hz : z / 2 = (z.re : ℂ) / 2 + Complex.I * (z.im : ℂ) / 2 := by
    apply Complex.ext <;> simp
  rw [hz, add_smul, Matrix.exp_add_of_commute _ _
    (((Commute.refl H).smul_left ((z.re : ℂ) / 2)).smul_right
      (Complex.I * (z.im : ℂ) / 2))]
  rfl

theorem norm_exp_complex_scale {H : CMat I} (hH : H.IsHermitian) (z : ℂ) :
    ‖exp ((z / 2) • H)‖ = ‖exp (((z.re : ℂ) / 2) • H)‖ := by
  rw [exp_complex_scale_factorization]
  exact CStarRing.norm_mul_mem_unitary _ (imaginaryExp_mem_unitary hH z.im)

theorem exists_stripProduct_bound (H1 H2 H3 H4 : CMat I)
    (h1 : H1.IsHermitian) (h2 : H2.IsHermitian)
    (h3 : H3.IsHermitian) (h4 : H4.IsHermitian) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, 0 ≤ z.re → z.re ≤ 1 →
      ‖stripProduct H1 H2 H3 H4 z‖ ≤ C := by
  let f : ℝ → ℝ := fun x => ‖exp (((x : ℂ) / 2) • H1)‖ *
    ‖exp (((x : ℂ) / 2) • H2)‖ * ‖exp (((x : ℂ) / 2) • H3)‖ *
      ‖exp (((x : ℂ) / 2) • H4)‖
  have hf : Continuous f := by unfold f; fun_prop
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hf.continuousOn : ContinuousOn f (Icc (0 : ℝ) 1))
  refine ⟨max C 0, le_max_right _ _, fun z hz0 hz1 => ?_⟩
  have hm : ‖stripProduct H1 H2 H3 H4 z‖ ≤ f z.re := by
    unfold stripProduct f
    simp only [← norm_exp_complex_scale h1 z, ← norm_exp_complex_scale h2 z,
      ← norm_exp_complex_scale h3 z, ← norm_exp_complex_scale h4 z]
    calc
      _ ≤ ‖exp ((z / 2) • H1) * exp ((z / 2) • H2) * exp ((z / 2) • H3)‖ *
        ‖exp ((z / 2) • H4)‖ := norm_mul_le _ _
      _ ≤ (‖exp ((z / 2) • H1) * exp ((z / 2) • H2)‖ *
        ‖exp ((z / 2) • H3)‖) * ‖exp ((z / 2) • H4)‖ := by
          gcongr; exact norm_mul_le _ _
      _ ≤ _ := by gcongr; exact norm_mul_le _ _
  exact hm.trans (((le_abs_self _).trans (hC z.re ⟨hz0, hz1⟩)).trans (le_max_left _ _))

def traceCLM : CMat I →L[ℂ] ℂ := (Matrix.traceLinearMap I ℂ ℂ).toContinuousLinearMap

theorem norm_re_trace_le (A : CMat I) :
    ‖A.trace.re‖ ≤ ‖traceCLM (I := I)‖ * ‖A‖ := by
  calc
    ‖A.trace.re‖ ≤ ‖A.trace‖ := by simpa only [Real.norm_eq_abs] using Complex.abs_re_le_norm A.trace
    _ ≤ ‖traceCLM (I := I)‖ * ‖A‖ := (traceCLM (I := I)).le_opNorm A

theorem norm_mul_six_le (A B C D F G : CMat I) :
    ‖A * B * C * D * F * G‖ ≤ ‖A‖ * ‖B‖ * ‖C‖ * ‖D‖ * ‖F‖ * ‖G‖ := by
  calc
    _ ≤ ‖A * B * C * D * F‖ * ‖G‖ := norm_mul_le _ _
    _ ≤ (‖A * B * C * D‖ * ‖F‖) * ‖G‖ :=
      mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
    _ ≤ ((‖A * B * C‖ * ‖D‖) * ‖F‖) * ‖G‖ := by gcongr; exact norm_mul_le _ _
    _ ≤ (((‖A * B‖ * ‖C‖) * ‖D‖) * ‖F‖) * ‖G‖ := by gcongr; exact norm_mul_le _ _
    _ ≤ ((((‖A‖ * ‖B‖) * ‖C‖) * ‖D‖) * ‖F‖) * ‖G‖ := by gcongr; exact norm_mul_le _ _

def integrandBound (H1 H2 H3 H4 : CMat I) : ℝ :=
  ‖traceCLM (I := I)‖ *
    (‖exp H1‖ * ‖halfExp H2‖ * ‖halfExp H3‖ * ‖exp H4‖ *
      ‖halfExp H3‖ * ‖halfExp H2‖)

theorem norm_fourMatrixIntegrand_le (H1 H2 H3 H4 : CMat I)
    (h2 : H2.IsHermitian) (h3 : H3.IsHermitian) (t : ℝ) :
    ‖fourMatrixIntegrand H1 H2 H3 H4 t‖ ≤ integrandBound H1 H2 H3 H4 := by
  unfold fourMatrixIntegrand integrandBound
  refine (norm_re_trace_le _).trans ?_
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  simpa only [Matrix.l2_opNorm_conjTranspose, norm_E_t h2, norm_E_t h3] using
    norm_mul_six_le (exp H1) (E_t H2 t) (E_t H3 t) (exp H4)
      (E_t H3 t)ᴴ (E_t H2 t)ᴴ

theorem integrable_weighted_fourMatrixIntegrand (H1 H2 H3 H4 : CMat I)
    (h2 : H2.IsHermitian) (h3 : H3.IsHermitian) :
    Integrable (fun t : ℝ => SBTProbabilityWeight.beta0 t *
      fourMatrixIntegrand H1 H2 H3 H4 t) volume := by
  exact SBTProbabilityWeight.integrable_beta0.mul_bdd
    (continuous_fourMatrixIntegrand H1 H2 H3 H4).aestronglyMeasurable
    (Eventually.of_forall (norm_fourMatrixIntegrand_le H1 H2 H3 H4 h2 h3))

theorem integrable_fourMatrixIntegrand_probability (H1 H2 H3 H4 : CMat I)
    (h2 : H2.IsHermitian) (h3 : H3.IsHermitian) :
    Integrable (fourMatrixIntegrand H1 H2 H3 H4)
      SBTProbabilityWeight.beta0Probability := by
  apply (SBTProbabilityWeight.integrable_beta0Probability_iff _).mpr
  simpa only [smul_eq_mul] using
    integrable_weighted_fourMatrixIntegrand H1 H2 H3 H4 h2 h3

theorem integral_fourMatrixIntegrand_probability (H1 H2 H3 H4 : CMat I) :
    (∫ t : ℝ, fourMatrixIntegrand H1 H2 H3 H4 t
      ∂SBTProbabilityWeight.beta0Probability) =
    ∫ t : ℝ, SBTProbabilityWeight.beta0 t * fourMatrixIntegrand H1 H2 H3 H4 t
      ∂volume :=
  SBTProbabilityWeight.integral_beta0Probability_real _

theorem weighted_integral_fourMatrixIntegrand_nonneg (H1 H2 H3 H4 : CMat I)
    (h1 : H1.IsHermitian) (h4 : H4.IsHermitian) :
    0 ≤ ∫ t : ℝ, SBTProbabilityWeight.beta0 t *
      fourMatrixIntegrand H1 H2 H3 H4 t ∂volume := by
  exact integral_nonneg (fun t => mul_nonneg (SBTProbabilityWeight.beta0_nonneg t)
    (fourMatrixIntegrand_nonneg H1 H2 H3 H4 h1 h4 t))

theorem weighted_integral_fourMatrixIntegrand_le_bound (H1 H2 H3 H4 : CMat I)
    (h2 : H2.IsHermitian) (h3 : H3.IsHermitian) :
    (∫ t : ℝ, SBTProbabilityWeight.beta0 t *
      fourMatrixIntegrand H1 H2 H3 H4 t ∂volume) ≤ integrandBound H1 H2 H3 H4 := by
  calc
    _ ≤ ∫ t : ℝ, SBTProbabilityWeight.beta0 t * integrandBound H1 H2 H3 H4
        ∂volume := by
      apply integral_mono (integrable_weighted_fourMatrixIntegrand H1 H2 H3 H4 h2 h3)
        (SBTProbabilityWeight.integrable_beta0.mul_const _)
      intro t
      apply mul_le_mul_of_nonneg_left _ (SBTProbabilityWeight.beta0_nonneg t)
      exact (le_abs_self _).trans (norm_fourMatrixIntegrand_le H1 H2 H3 H4 h2 h3 t)
    _ = integrandBound H1 H2 H3 H4 := by
      rw [integral_mul_const, SBTProbabilityWeight.integral_beta0_eq_one, one_mul]

def hsNorm (A : CMat I) : ℝ :=
  ‖(WithLp.toLp 2 (BellDiagonalSquashedEntanglement.Geometry.matrixVector A) : EuclideanSpace ℂ (I × I))‖

theorem hsNorm_nonneg (A : CMat I) : 0 ≤ hsNorm A := norm_nonneg _

theorem hsNorm_sq (A : CMat I) : hsNorm A ^ 2 = (A * Aᴴ).trace.re := by
  rw [hsNorm, norm_sq_eq_re_inner (𝕜 := ℂ), BellDiagonalSquashedEntanglement.Geometry.inner_matrixVector,
    Matrix.trace_mul_comm]
  rfl

theorem hsNorm_eq_sqrt_trace (A : CMat I) :
    hsNorm A = Real.sqrt (A * Aᴴ).trace.re := by
  rw [← hsNorm_sq, Real.sqrt_sq (hsNorm_nonneg A)]

@[simp] theorem hsNorm_conjTranspose (A : CMat I) : hsNorm Aᴴ = hsNorm A := by
  apply (sq_eq_sq₀ (hsNorm_nonneg _) (hsNorm_nonneg _)).mp
  rw [hsNorm_sq, hsNorm_sq, Matrix.conjTranspose_conjTranspose, Matrix.trace_mul_comm]

theorem continuous_hsNorm : Continuous (hsNorm (I := I)) := by
  unfold hsNorm BellDiagonalSquashedEntanglement.Geometry.matrixVector
  fun_prop

theorem norm_trace_mul_le_hsNorm (A B : CMat I) :
    ‖(A * B).trace‖ ≤ hsNorm A * hsNorm B := by
  have h := norm_inner_le_norm (𝕜 := ℂ)
    (WithLp.toLp 2 (BellDiagonalSquashedEntanglement.Geometry.matrixVector Aᴴ) : EuclideanSpace ℂ (I × I))
    (WithLp.toLp 2 (BellDiagonalSquashedEntanglement.Geometry.matrixVector B) : EuclideanSpace ℂ (I × I))
  rw [BellDiagonalSquashedEntanglement.Geometry.inner_matrixVector, Matrix.conjTranspose_conjTranspose] at h
  change ‖(A * B).trace‖ ≤ hsNorm Aᴴ * hsNorm B at h
  simpa only [hsNorm_conjTranspose] using h

theorem norm_le_hsNorm (A : CMat I) : ‖A‖ ≤ hsNorm A := by
  have h := QuantumProver.PPTSupport.SupportBounds.posSemidef_norm_le_trace_re
    (Matrix.posSemidef_self_mul_conjTranspose A)
  rw [← hsNorm_sq A] at h
  have hn : ‖A * Aᴴ‖ = ‖A‖ ^ 2 := by
    simpa only [pow_two, Matrix.star_eq_conjTranspose] using
      (CStarRing.norm_self_mul_star (x := A))
  rw [hn] at h
  exact (sq_le_sq₀ (norm_nonneg _) (hsNorm_nonneg _)).mp h

theorem stripProduct_boundary_hsNorm (H1 H2 H3 H4 : CMat I)
    (h1 : H1.IsHermitian) (h4 : H4.IsHermitian) (t : ℝ) :
    hsNorm (stripProduct H1 H2 H3 H4 (1 + Complex.I * (t : ℂ))) =
    Real.sqrt (fourMatrixIntegrand H1 H2 H3 H4 t) := by
  rw [hsNorm_eq_sqrt_trace, stripProduct_boundary_trace H1 H2 H3 H4 h1 h4 t]

theorem stripProduct_reverse_neg_mul_self (H1 H2 H3 H4 : CMat I) (z : ℂ) :
    stripProduct (-H4) (-H3) (-H2) (-H1) z * stripProduct H1 H2 H3 H4 z = 1 := by
  let a (H : CMat I) := exp ((z / 2) • H)
  have h (H : CMat I) : a (-H) * a H = 1 := by
    unfold a
    rw [smul_neg, ← Matrix.exp_add_of_commute _ _ ((Commute.refl ((z / 2) • H)).neg_left),
      neg_add_cancel, exp_zero]
  change (a (-H4) * a (-H3) * a (-H2) * a (-H1)) * (a H1 * a H2 * a H3 * a H4) = 1
  calc
    _ = a (-H4) * (a (-H3) * (a (-H2) * (a (-H1) * a H1) * a H2) * a H3) * a H4 := by
      simp only [Matrix.mul_assoc]
    _ = 1 := by
      rw [h H1, Matrix.mul_one, h H2, Matrix.mul_one, h H3, Matrix.mul_one, h H4]

theorem exists_stripBoundary_hsNorm_bounds [Nonempty I] (H1 H2 H3 H4 : CMat I)
    (h1 : H1.IsHermitian) (h2 : H2.IsHermitian)
    (h3 : H3.IsHermitian) (h4 : H4.IsHermitian) :
    ∃ m M : ℝ, 0 < m ∧ ∀ t : ℝ,
      m ≤ hsNorm (stripProduct H1 H2 H3 H4 (1 + Complex.I * (t : ℂ))) ∧
      hsNorm (stripProduct H1 H2 H3 H4 (1 + Complex.I * (t : ℂ))) ≤ M := by
  obtain ⟨C, hC0, hC⟩ := exists_stripProduct_bound (-H4) (-H3) (-H2) (-H1)
    h4.neg h3.neg h2.neg h1.neg
  have hCp : 0 < C + 1 := by linarith
  refine ⟨(C + 1)⁻¹, Real.sqrt (integrandBound H1 H2 H3 H4), inv_pos.mpr hCp,
    fun t => ⟨?_, ?_⟩⟩
  · have hinv : 1 ≤ (C + 1) *
        hsNorm (stripProduct H1 H2 H3 H4 (1 + Complex.I * (t : ℂ))) := by
      calc
        1 = ‖stripProduct (-H4) (-H3) (-H2) (-H1) (1 + Complex.I * (t : ℂ)) *
            stripProduct H1 H2 H3 H4 (1 + Complex.I * (t : ℂ))‖ := by
          rw [stripProduct_reverse_neg_mul_self, norm_one]
        _ ≤ ‖stripProduct (-H4) (-H3) (-H2) (-H1) (1 + Complex.I * (t : ℂ))‖ *
            ‖stripProduct H1 H2 H3 H4 (1 + Complex.I * (t : ℂ))‖ := norm_mul_le _ _
        _ ≤ (C + 1) * hsNorm (stripProduct H1 H2 H3 H4 (1 + Complex.I * (t : ℂ))) := by
          apply mul_le_mul
            ((hC _ (by simp) (by simp)).trans (by linarith)) (norm_le_hsNorm _)
            (norm_nonneg _) (by linarith)
    have hdiv : (1 : ℝ) / (C + 1) ≤
        hsNorm (stripProduct H1 H2 H3 H4 (1 + Complex.I * (t : ℂ))) :=
      (div_le_iff₀ hCp).mpr (by simpa only [mul_comm] using hinv)
    simpa only [one_div] using hdiv
  · rw [stripProduct_boundary_hsNorm H1 H2 H3 H4 h1 h4 t]
    apply Real.sqrt_le_sqrt
    exact (le_abs_self _).trans (norm_fourMatrixIntegrand_le H1 H2 H3 H4 h2 h3 t)

theorem continuous_log_sqrt_fourMatrixIntegrand [Nonempty I] (H1 H2 H3 H4 : CMat I)
    (h1 : H1.IsHermitian) (h2 : H2.IsHermitian)
    (h3 : H3.IsHermitian) (h4 : H4.IsHermitian) :
    Continuous (fun t : ℝ => Real.log (Real.sqrt (fourMatrixIntegrand H1 H2 H3 H4 t))) := by
  obtain ⟨m, M, hm, hbounds⟩ := exists_stripBoundary_hsNorm_bounds H1 H2 H3 H4 h1 h2 h3 h4
  have hc : Continuous (fun t : ℝ => Real.sqrt (fourMatrixIntegrand H1 H2 H3 H4 t)) :=
    Real.continuous_sqrt.comp (continuous_fourMatrixIntegrand H1 H2 H3 H4)
  apply hc.log
  intro t
  have hpos := hm.trans_le (hbounds t).1
  rw [stripProduct_boundary_hsNorm H1 H2 H3 H4 h1 h4 t] at hpos
  exact hpos.ne'

theorem integrable_weighted_log_sqrt_fourMatrixIntegrand [Nonempty I]
    (H1 H2 H3 H4 : CMat I) (h1 : H1.IsHermitian) (h2 : H2.IsHermitian)
    (h3 : H3.IsHermitian) (h4 : H4.IsHermitian) :
    Integrable (fun t : ℝ => SBTProbabilityWeight.beta0 t *
      Real.log (Real.sqrt (fourMatrixIntegrand H1 H2 H3 H4 t))) volume := by
  obtain ⟨m, M, hm, hbounds⟩ := exists_stripBoundary_hsNorm_bounds H1 H2 H3 H4 h1 h2 h3 h4
  have hc : ContinuousOn Real.log (Icc m M) := fun x hx =>
    (Real.continuousAt_log (hm.trans_le hx.1).ne').continuousWithinAt
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  apply SBTProbabilityWeight.integrable_beta0.mul_bdd
    (continuous_log_sqrt_fourMatrixIntegrand H1 H2 H3 H4 h1 h2 h3 h4).aestronglyMeasurable
  apply Eventually.of_forall
  intro t
  rw [← stripProduct_boundary_hsNorm H1 H2 H3 H4 h1 h4 t]
  exact hC _ (hbounds t)

theorem hsNorm_unitary_endpoints (U W V : CMat I)
    (hU : U ∈ unitary (CMat I)) (hV : V ∈ unitary (CMat I)) :
    hsNorm (U * W * V) = hsNorm W := by
  apply (sq_eq_sq₀ (hsNorm_nonneg _) (hsNorm_nonneg _)).mp
  rw [hsNorm_sq, hsNorm_sq, trace_gram_unitary_endpoints U W V hU hV]

theorem hsNorm_mul_unitary (W V : CMat I) (hV : V ∈ unitary (CMat I)) :
    hsNorm (W * V) = hsNorm W := by
  simpa only [Matrix.one_mul] using hsNorm_unitary_endpoints 1 W V
    (unitary (CMat I)).one_mem hV

theorem hasDerivAt_matrix_trace {f : ℂ → CMat I} {f' : CMat I} {z : ℂ}
    (hf : HasDerivAt f f' z) :
    HasDerivAt (fun w => (f w).trace) f'.trace z := by
  dsimp only [Matrix.trace, Matrix.diag]
  simpa only [Finset.sum_fn] using
    (HasDerivAt.sum (u := Finset.univ) fun i _ =>
      hasDerivAt_pi.mp (hasDerivAt_pi.mp hf i) i)

def stripDualWitness (L H1 H2 H3 H4 : CMat I) (z : ℂ) : ℂ :=
  (exp (((1 : ℂ) - z / 2) • L) * stripProduct H1 H2 H3 H4 z).trace

@[simp] theorem stripDualWitness_zero (L H1 H2 H3 H4 : CMat I) :
    stripDualWitness L H1 H2 H3 H4 0 = (exp L).trace := by
  simp only [stripDualWitness, zero_div, sub_zero, one_smul, stripProduct_zero, Matrix.mul_one]

theorem differentiable_stripDualWitness (L H1 H2 H3 H4 : CMat I) :
    Differentiable ℂ (stripDualWitness L H1 H2 H3 H4) := by
  have hE : Differentiable ℂ (fun z : ℂ => exp (((1 : ℂ) - z / 2) • L)) :=
    (differentiable_exp_smul_const ℂ L).comp
      ((differentiable_id.div_const 2).const_sub (1 : ℂ))
  have hM := hE.mul (differentiable_stripProduct H1 H2 H3 H4)
  exact (traceCLM (I := I)).differentiable.comp hM

theorem dualExp_leftBoundary (L : CMat I) (t : ℝ) :
    exp (((1 : ℂ) - (Complex.I * (t : ℂ)) / 2) • L) =
      exp L * imaginaryExp L (-t) := by
  have hc : (1 : ℂ) - (Complex.I * (t : ℂ)) / 2 =
      1 + Complex.I * ((-t : ℝ) : ℂ) / 2 := by push_cast; ring
  rw [hc, add_smul, one_smul, Matrix.exp_add_of_commute _ _
    ((Commute.refl L).smul_right (Complex.I * ((-t : ℝ) : ℂ) / 2))]
  rfl

theorem dualExp_rightBoundary (L : CMat I) (t : ℝ) :
    exp (((1 : ℂ) - (1 + Complex.I * (t : ℂ)) / 2) • L) = E_t L (-t) := by
  unfold E_t
  congr 1
  congr 1
  push_cast
  ring

theorem hsNorm_halfExp_normalized (L : CMat I) (hL : L.IsHermitian)
    (hn : (exp L).trace = 1) : hsNorm (halfExp L) = 1 := by
  have hsq : hsNorm (halfExp L) ^ 2 = 1 := by
    rw [hsNorm_sq, halfExp_isHermitian hL, halfExp_mul_self, hn]
    rfl
  nlinarith [hsNorm_nonneg (halfExp L)]

theorem norm_stripDualWitness_leftBoundary_le (L H1 H2 H3 H4 : CMat I)
    (hL : L.IsHermitian) (hn : (exp L).trace = 1)
    (h1 : H1.IsHermitian) (h2 : H2.IsHermitian)
    (h3 : H3.IsHermitian) (h4 : H4.IsHermitian) (t : ℝ) :
    ‖stripDualWitness L H1 H2 H3 H4 (Complex.I * (t : ℂ))‖ ≤ 1 := by
  have hP : (exp L).PosSemidef := Matrix.nonneg_iff_posSemidef.mp
    (Matrix.isHermitian_iff_isSelfAdjoint.mp hL).exp_nonneg
  have hU := (unitary (CMat I)).mul_mem (imaginaryExp_mem_unitary hL (-t))
    (stripProduct_imaginary_mem_unitary H1 H2 H3 H4 h1 h2 h3 h4 t)
  calc
    _ = ‖(exp L * (imaginaryExp L (-t) *
        stripProduct H1 H2 H3 H4 (Complex.I * (t : ℂ)))).trace‖ := by
      rw [stripDualWitness, dualExp_leftBoundary, Matrix.mul_assoc]
    _ ≤ (exp L).trace.re := BellDiagonalSquashedEntanglement.Geometry.norm_trace_posSemidef_mul_unitary_le
      _ _ hP hU
    _ = 1 := by rw [hn]; rfl

theorem norm_stripDualWitness_rightBoundary_le (L H1 H2 H3 H4 : CMat I)
    (hL : L.IsHermitian) (hn : (exp L).trace = 1) (t : ℝ) :
    ‖stripDualWitness L H1 H2 H3 H4 (1 + Complex.I * (t : ℂ))‖ ≤
      hsNorm (stripProduct H1 H2 H3 H4 (1 + Complex.I * (t : ℂ))) := by
  have hN : hsNorm (E_t L (-t)) = 1 := by
    rw [E_t_factorization, hsNorm_mul_unitary _ _ (imaginaryExp_mem_unitary hL (-t)),
      hsNorm_halfExp_normalized L hL hn]
  unfold stripDualWitness
  rw [dualExp_rightBoundary]
  simpa only [hN, one_mul] using norm_trace_mul_le_hsNorm
    (E_t L (-t)) (stripProduct H1 H2 H3 H4 (1 + Complex.I * (t : ℂ)))

theorem hasDerivAt_stripDualWitness_zero (L H1 H2 H3 H4 : CMat I) :
    HasDerivAt (stripDualWitness L H1 H2 H3 H4)
      (((exp L * (H1 + H2 + H3 + H4)).trace - (exp L * L).trace) / 2) 0 := by
  have hlin : HasDerivAt (fun z : ℂ => (1 : ℂ) - z / 2) (-(1 / 2 : ℂ)) 0 := by
    simpa only [Pi.sub_def, id_eq, zero_sub] using
      (hasDerivAt_const (0 : ℂ) (1 : ℂ)).sub ((hasDerivAt_id (0 : ℂ)).div_const 2)
  have hE : HasDerivAt (fun z : ℂ => exp (((1 : ℂ) - z / 2) • L))
      ((-(1 / 2 : ℂ)) • (exp L * L)) 0 := by
    simpa only [Function.comp_def, zero_div, sub_zero, one_smul] using
      (hasDerivAt_exp_smul_const L (1 : ℂ)).scomp_of_eq
        (𝕜 := ℂ) (𝕜' := ℂ) (h := fun z : ℂ => (1 : ℂ) - z / 2) 0 hlin (by norm_num)
  have hM := hasDerivAt_matrix_mul hE (hasDerivAt_stripProduct_zero H1 H2 H3 H4)
  have hT := hasDerivAt_matrix_trace hM
  unfold stripDualWitness
  convert hT using 1
  · simp only [stripProduct_zero, zero_div, sub_zero, one_smul, Matrix.mul_one,
      Matrix.trace_add, Matrix.trace_smul, Matrix.mul_smul, smul_eq_mul]
    ring

theorem hasDerivAt_log_norm_stripDualWitness_zero (L H1 H2 H3 H4 : CMat I)
    (hn : (exp L).trace = 1) :
    HasDerivAt (fun x : ℝ => Real.log ‖stripDualWitness L H1 H2 H3 H4 (x : ℂ)‖)
      ((((exp L * (H1 + H2 + H3 + H4)).trace - (exp L * L).trace) / 2).re) 0 := by
  have hz : stripDualWitness L H1 H2 H3 H4 0 ∈ Complex.slitPlane := by
    rw [stripDualWitness_zero, hn]
    simp
  have h := ((hasDerivAt_stripDualWitness_zero L H1 H2 H3 H4).clog hz).real_of_complex
  simpa only [stripDualWitness_zero, hn, div_one, Complex.log_re] using h

theorem tendsto_log_norm_stripDualWitness_div (L H1 H2 H3 H4 : CMat I)
    (hn : (exp L).trace = 1) :
    Tendsto (fun x : ℝ => Real.log ‖stripDualWitness L H1 H2 H3 H4 (x : ℂ)‖ / x)
      (𝓝[>] 0) (𝓝 ((((exp L * (H1 + H2 + H3 + H4)).trace - (exp L * L).trace) / 2).re)) := by
  simpa only [zero_add, Complex.ofReal_zero, stripDualWitness_zero, hn, norm_one,
    Real.log_one, sub_zero, smul_eq_mul, div_eq_mul_inv, mul_comm] using
    (hasDerivAt_log_norm_stripDualWitness_zero L H1 H2 H3 H4 hn).tendsto_slope_zero_right

theorem dualExp_factorization (L : CMat I) (z : ℂ) :
    exp (((1 : ℂ) - z / 2) • L) = exp L * exp ((z / 2) • (-L)) := by
  have hc : ((1 : ℂ) - z / 2) • L = L + (z / 2) • (-L) := by
    simp only [sub_eq_add_neg, add_smul, one_smul, smul_neg, neg_smul]
  rw [hc, Matrix.exp_add_of_commute _ _
    (by simpa only [smul_neg] using (Commute.refl L).neg_right.smul_right (z / 2))]

theorem exists_stripDualWitness_bound (L H1 H2 H3 H4 : CMat I)
    (hL : L.IsHermitian) (h1 : H1.IsHermitian) (h2 : H2.IsHermitian)
    (h3 : H3.IsHermitian) (h4 : H4.IsHermitian) :
    ∃ C : ℝ, ∀ z : ℂ, 0 ≤ z.re → z.re ≤ 1 →
      ‖stripDualWitness L H1 H2 H3 H4 z‖ ≤ C := by
  obtain ⟨CE, hCE0, hCE⟩ := exists_stripProduct_bound (-L) 0 0 0 hL.neg
    Matrix.isHermitian_zero Matrix.isHermitian_zero Matrix.isHermitian_zero
  obtain ⟨CG, hCG0, hCG⟩ := exists_stripProduct_bound H1 H2 H3 H4 h1 h2 h3 h4
  refine ⟨‖traceCLM (I := I)‖ * ((‖exp L‖ * CE) * CG), fun z hz0 hz1 => ?_⟩
  have hE : ‖exp ((z / 2) • (-L))‖ ≤ CE := by
    simpa only [stripProduct, smul_zero, exp_zero, Matrix.mul_one] using hCE z hz0 hz1
  unfold stripDualWitness
  calc
    _ ≤ ‖traceCLM (I := I)‖ *
        ‖exp (((1 : ℂ) - z / 2) • L) * stripProduct H1 H2 H3 H4 z‖ :=
      (traceCLM (I := I)).le_opNorm _
    _ ≤ ‖traceCLM (I := I)‖ *
        (‖exp (((1 : ℂ) - z / 2) • L)‖ * ‖stripProduct H1 H2 H3 H4 z‖) := by
      gcongr; exact norm_mul_le _ _
    _ ≤ _ := by
      rw [dualExp_factorization]
      gcongr
      exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left hE (norm_nonneg _))
      exact hCG z hz0 hz1

theorem fourMatrixIntegrand_pos [Nonempty I] (H1 H2 H3 H4 : CMat I)
    (h1 : H1.IsHermitian) (h2 : H2.IsHermitian)
    (h3 : H3.IsHermitian) (h4 : H4.IsHermitian) (t : ℝ) :
    0 < fourMatrixIntegrand H1 H2 H3 H4 t := by
  obtain ⟨m, M, hm, hbounds⟩ := exists_stripBoundary_hsNorm_bounds H1 H2 H3 H4 h1 h2 h3 h4
  have h := hm.trans_le (hbounds t).1
  rw [stripProduct_boundary_hsNorm H1 H2 H3 H4 h1 h4 t] at h
  exact Real.sqrt_pos.mp h

theorem integrable_weighted_log_fourMatrixIntegrand [Nonempty I]
    (H1 H2 H3 H4 : CMat I) (h1 : H1.IsHermitian) (h2 : H2.IsHermitian)
    (h3 : H3.IsHermitian) (h4 : H4.IsHermitian) :
    Integrable (fun t : ℝ => SBTProbabilityWeight.beta0 t *
      Real.log (fourMatrixIntegrand H1 H2 H3 H4 t)) volume := by
  have hEq : (fun t : ℝ => SBTProbabilityWeight.beta0 t *
      Real.log (fourMatrixIntegrand H1 H2 H3 H4 t)) =
      fun t : ℝ => 2 * (SBTProbabilityWeight.beta0 t *
        Real.log (Real.sqrt (fourMatrixIntegrand H1 H2 H3 H4 t))) := by
    funext t
    rw [Real.log_sqrt (fourMatrixIntegrand_nonneg H1 H2 H3 H4 h1 h4 t)]
    ring
  rw [hEq]
  exact (integrable_weighted_log_sqrt_fourMatrixIntegrand H1 H2 H3 H4 h1 h2 h3 h4).const_mul 2

theorem exp_integral_log_fourMatrixIntegrand_le_integral [Nonempty I]
    (H1 H2 H3 H4 : CMat I) (h1 : H1.IsHermitian) (h2 : H2.IsHermitian)
    (h3 : H3.IsHermitian) (h4 : H4.IsHermitian) :
    Real.exp (∫ t : ℝ, SBTProbabilityWeight.beta0 t *
      Real.log (fourMatrixIntegrand H1 H2 H3 H4 t) ∂volume) ≤
    ∫ t : ℝ, SBTProbabilityWeight.beta0 t * fourMatrixIntegrand H1 H2 H3 H4 t ∂volume := by
  let f : ℝ → ℝ := fun t => Real.log (fourMatrixIntegrand H1 H2 H3 H4 t)
  have hf : Integrable f SBTProbabilityWeight.beta0Probability := by
    apply (SBTProbabilityWeight.integrable_beta0Probability_iff _).mpr
    simpa only [f, smul_eq_mul] using
      integrable_weighted_log_fourMatrixIntegrand H1 H2 H3 H4 h1 h2 h3 h4
  have hExp : Integrable (Real.exp ∘ f) SBTProbabilityWeight.beta0Probability := by
    apply (integrable_fourMatrixIntegrand_probability H1 H2 H3 H4 h2 h3).congr
    apply Eventually.of_forall
    intro t
    exact (Real.exp_log (fourMatrixIntegrand_pos H1 H2 H3 H4 h1 h2 h3 h4 t)).symm
  have h := ConvexOn.map_integral_le convexOn_exp Real.continuous_exp.continuousOn isClosed_univ
    (Eventually.of_forall fun _ => Set.mem_univ _) hf hExp
  have hExpInt : (∫ t : ℝ, Real.exp (f t) ∂SBTProbabilityWeight.beta0Probability) =
      ∫ t : ℝ, fourMatrixIntegrand H1 H2 H3 H4 t ∂SBTProbabilityWeight.beta0Probability := by
    apply integral_congr_ae
    exact Eventually.of_forall fun t => Real.exp_log
      (fourMatrixIntegrand_pos H1 H2 H3 H4 h1 h2 h3 h4 t)
  rw [hExpInt, SBTProbabilityWeight.integral_beta0Probability_real,
    SBTProbabilityWeight.integral_beta0Probability_real] at h
  exact h

theorem four_matrix_gt_of_isEmpty [IsEmpty I] (H1 H2 H3 H4 : CMat I) :
    (exp (H1 + H2 + H3 + H4)).trace.re ≤
      ∫ t : ℝ, SBTProbabilityWeight.beta0 t * fourMatrixIntegrand H1 H2 H3 H4 t ∂volume := by
  simp [Matrix.trace, fourMatrixIntegrand]

theorem exp_posDef {S : CMat I} (hS : S.IsHermitian) : (exp S).PosDef := by
  have hP : (exp S).PosSemidef := Matrix.nonneg_iff_posSemidef.mp
    (Matrix.isHermitian_iff_isSelfAdjoint.mp hS).exp_nonneg
  exact hP.posDef_iff_isUnit.mpr (Matrix.isUnit_exp S)

theorem exp_trace_re_pos [Nonempty I] {S : CMat I} (hS : S.IsHermitian) :
    0 < (exp S).trace.re :=
  (Complex.pos_iff.mp (exp_posDef hS).trace_pos).1

theorem exp_trace_eq_coe_re {S : CMat I} (hS : S.IsHermitian) :
    (exp S).trace = ((exp S).trace.re : ℂ) := by
  have hP : (exp S).PosSemidef := (exp_posDef hS).posSemidef
  apply Complex.ext
  · rfl
  · exact (Complex.nonneg_iff.mp hP.trace_nonneg).2.symm

theorem exp_scalar_identity (z : ℂ) :
    exp (z • (1 : CMat I)) = Complex.exp z • (1 : CMat I) := by
  simp only [Matrix.smul_one_eq_diagonal, Matrix.exp_diagonal, Pi.exp_def,
    ← Complex.exp_eq_exp_ℂ]

def gibbsLog (S : CMat I) : CMat I :=
  S - (Real.log (exp S).trace.re : ℂ) • 1

theorem gibbsLog_isHermitian {S : CMat I} (hS : S.IsHermitian) :
    (gibbsLog S).IsHermitian := by
  exact hS.sub (Matrix.isHermitian_one.smul (by simp [IsSelfAdjoint]))

theorem exp_gibbsLog [Nonempty I] {S : CMat I} (hS : S.IsHermitian) :
    exp (gibbsLog S) = (((exp S).trace.re)⁻¹ : ℂ) • exp S := by
  have hz := exp_trace_re_pos hS
  have hc : Commute S (-(Real.log (exp S).trace.re : ℂ) • (1 : CMat I)) := by
    simpa only [Algebra.algebraMap_eq_smul_one] using
      Algebra.commute_algebraMap_right (-(Real.log (exp S).trace.re : ℂ)) S
  have he : Complex.exp (-(Real.log (exp S).trace.re : ℂ)) =
      (((exp S).trace.re)⁻¹ : ℂ) := by
    rw [← Complex.ofReal_neg, ← Complex.ofReal_exp, Real.exp_neg, Real.exp_log hz,
      Complex.ofReal_inv]
  rw [gibbsLog, sub_eq_add_neg, ← neg_smul, Matrix.exp_add_of_commute S _ hc,
    exp_scalar_identity, he, Matrix.mul_smul, Matrix.mul_one]

theorem trace_exp_gibbsLog [Nonempty I] {S : CMat I} (hS : S.IsHermitian) :
    (exp (gibbsLog S)).trace = 1 := by
  rw [exp_gibbsLog hS, Matrix.trace_smul, smul_eq_mul, exp_trace_eq_coe_re hS]
  exact inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr (exp_trace_re_pos hS).ne')

theorem gibbs_trace_difference [Nonempty I] {S : CMat I} (hS : S.IsHermitian) :
    (exp (gibbsLog S) * S).trace - (exp (gibbsLog S) * gibbsLog S).trace =
      (Real.log (exp S).trace.re : ℂ) := by
  rw [← Matrix.trace_sub, ← Matrix.mul_sub]
  have hd : S - gibbsLog S = (Real.log (exp S).trace.re : ℂ) • (1 : CMat I) := by
    simp only [gibbsLog, sub_sub_cancel]
  rw [hd, Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul,
    trace_exp_gibbsLog hS, smul_eq_mul, mul_one]

theorem tendsto_gibbs_log_norm_stripDualWitness_div [Nonempty I]
    (H1 H2 H3 H4 : CMat I) (h1 : H1.IsHermitian) (h2 : H2.IsHermitian)
    (h3 : H3.IsHermitian) (h4 : H4.IsHermitian) :
    Tendsto (fun x : ℝ =>
      Real.log ‖stripDualWitness (gibbsLog (H1 + H2 + H3 + H4)) H1 H2 H3 H4 (x : ℂ)‖ / x)
      (𝓝[>] 0) (𝓝 (Real.log (exp (H1 + H2 + H3 + H4)).trace.re / 2)) := by
  have hS : (H1 + H2 + H3 + H4).IsHermitian := ((h1.add h2).add h3).add h4
  have hc : ((Real.log (exp (H1 + H2 + H3 + H4)).trace.re : ℂ) / 2).re =
      Real.log (exp (H1 + H2 + H3 + H4)).trace.re / 2 := by
    norm_num [Complex.div_re] <;> ring
  simpa only [gibbs_trace_difference hS, hc] using
    tendsto_log_norm_stripDualWitness_div (gibbsLog (H1 + H2 + H3 + H4)) H1 H2 H3 H4
      (trace_exp_gibbsLog hS)

theorem diffContOnCl_stripDualWitness (L H1 H2 H3 H4 : CMat I) :
    DiffContOnCl ℂ (stripDualWitness L H1 H2 H3 H4)
      (Complex.HadamardThreeLines.verticalStrip 0 1) :=
  (differentiable_stripDualWitness L H1 H2 H3 H4).diffContOnCl

theorem bddAbove_norm_stripDualWitness (L H1 H2 H3 H4 : CMat I)
    (hL : L.IsHermitian) (h1 : H1.IsHermitian) (h2 : H2.IsHermitian)
    (h3 : H3.IsHermitian) (h4 : H4.IsHermitian) :
    BddAbove ((norm ∘ stripDualWitness L H1 H2 H3 H4) ''
      Complex.HadamardThreeLines.verticalClosedStrip 0 1) := by
  obtain ⟨C, hC⟩ := exists_stripDualWitness_bound L H1 H2 H3 H4 hL h1 h2 h3 h4
  refine ⟨C, ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  exact hC z hz.1 hz.2

theorem eventually_stripDualWitness_ne_zero (L H1 H2 H3 H4 : CMat I)
    (hn : (exp L).trace = 1) :
    ∀ᶠ x : ℝ in 𝓝 0, stripDualWitness L H1 H2 H3 H4 (x : ℂ) ≠ 0 := by
  have hc : Continuous (fun x : ℝ => stripDualWitness L H1 H2 H3 H4 (x : ℂ)) :=
    (differentiable_stripDualWitness L H1 H2 H3 H4).continuous.comp Complex.continuous_ofReal
  apply hc.continuousAt.eventually_ne
  simp only [Complex.ofReal_zero, stripDualWitness_zero, hn, ne_eq, one_ne_zero, not_false_eq_true]

theorem continuous_sqrt_fourMatrixIntegrand (H1 H2 H3 H4 : CMat I) :
    Continuous (fun t : ℝ => Real.sqrt (fourMatrixIntegrand H1 H2 H3 H4 t)) :=
  Real.continuous_sqrt.comp (continuous_fourMatrixIntegrand H1 H2 H3 H4)

theorem exists_sqrt_fourMatrixIntegrand_bounds [Nonempty I] (H1 H2 H3 H4 : CMat I)
    (h1 : H1.IsHermitian) (h2 : H2.IsHermitian)
    (h3 : H3.IsHermitian) (h4 : H4.IsHermitian) :
    ∃ m M : ℝ, 0 < m ∧ ∀ t : ℝ,
      m ≤ Real.sqrt (fourMatrixIntegrand H1 H2 H3 H4 t) ∧
      Real.sqrt (fourMatrixIntegrand H1 H2 H3 H4 t) ≤ M := by
  simpa only [stripProduct_boundary_hsNorm H1 H2 H3 H4 h1 h4] using
    exists_stripBoundary_hsNorm_bounds H1 H2 H3 H4 h1 h2 h3 h4

theorem norm_stripDualWitness_rightBoundary_le_sqrt (L H1 H2 H3 H4 : CMat I)
    (hL : L.IsHermitian) (hn : (exp L).trace = 1)
    (h1 : H1.IsHermitian) (h4 : H4.IsHermitian) (t : ℝ) :
    ‖stripDualWitness L H1 H2 H3 H4 (1 + Complex.I * (t : ℂ))‖ ≤
      Real.sqrt (fourMatrixIntegrand H1 H2 H3 H4 t) := by
  simpa only [stripProduct_boundary_hsNorm H1 H2 H3 H4 h1 h4] using
    norm_stripDualWitness_rightBoundary_le L H1 H2 H3 H4 hL hn t

theorem integral_log_sqrt_fourMatrixIntegrand_eq_half (H1 H2 H3 H4 : CMat I)
    (h1 : H1.IsHermitian) (h4 : H4.IsHermitian) :
    (∫ t : ℝ, SBTProbabilityWeight.beta0 t *
      Real.log (Real.sqrt (fourMatrixIntegrand H1 H2 H3 H4 t)) ∂volume) =
    (∫ t : ℝ, SBTProbabilityWeight.beta0 t *
      Real.log (fourMatrixIntegrand H1 H2 H3 H4 t) ∂volume) / 2 := by
  calc
    _ = ∫ t : ℝ, (2 : ℝ)⁻¹ * (SBTProbabilityWeight.beta0 t *
        Real.log (fourMatrixIntegrand H1 H2 H3 H4 t)) ∂volume := by
      apply integral_congr_ae
      exact Eventually.of_forall fun t => by
        dsimp only
        rw [Real.log_sqrt (fourMatrixIntegrand_nonneg H1 H2 H3 H4 h1 h4 t)]
        ring
    _ = (2 : ℝ)⁻¹ * (∫ t : ℝ, SBTProbabilityWeight.beta0 t *
        Real.log (fourMatrixIntegrand H1 H2 H3 H4 t) ∂volume) := integral_const_mul _ _
    _ = _ := by ring

theorem log_partition_le_weighted_log_integrand [Nonempty I]
    (H1 H2 H3 H4 : CMat I) (h1 : H1.IsHermitian) (h2 : H2.IsHermitian)
    (h3 : H3.IsHermitian) (h4 : H4.IsHermitian) :
    Real.log (exp (H1 + H2 + H3 + H4)).trace.re ≤
      ∫ t : ℝ, SBTProbabilityWeight.beta0 t *
        Real.log (fourMatrixIntegrand H1 H2 H3 H4 t) ∂volume := by
  let L := gibbsLog (H1 + H2 + H3 + H4)
  have hS : (H1 + H2 + H3 + H4).IsHermitian := ((h1.add h2).add h3).add h4
  have hL : L.IsHermitian := gibbsLog_isHermitian hS
  have hn : (exp L).trace = 1 := trace_exp_gibbsLog hS
  obtain ⟨m, M, hm, hbounds⟩ :=
    exists_sqrt_fourMatrixIntegrand_bounds H1 H2 H3 H4 h1 h2 h3 h4
  have hne : ∀ᶠ θ : ℝ in 𝓝[>] 0,
      stripDualWitness L H1 H2 H3 H4 (θ : ℂ) ≠ 0 :=
    (eventually_stripDualWitness_ne_zero L H1 H2 H3 H4 hn).filter_mono
      nhdsWithin_le_nhds
  have hle : ∀ᶠ θ : ℝ in 𝓝[>] 0,
      Real.log ‖stripDualWitness L H1 H2 H3 H4 (θ : ℂ)‖ / θ ≤
        ∫ t : ℝ, HirschmanInterpolation.beta θ t *
          Real.log (Real.sqrt (fourMatrixIntegrand H1 H2 H3 H4 t)) ∂volume := by
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1), hne] with θ hθ hθne
    have h := HirschmanInterpolation.hirschman_strip_majorant hθ
      (diffContOnCl_stripDualWitness L H1 H2 H3 H4)
      (bddAbove_norm_stripDualWitness L H1 H2 H3 H4 hL h1 h2 h3 h4) hθne
      (fun _ : ℝ => (1 : ℝ))
      (fun t : ℝ => Real.sqrt (fourMatrixIntegrand H1 H2 H3 H4 t))
      continuous_const (continuous_sqrt_fourMatrixIntegrand H1 H2 H3 H4)
      (m0 := 1) (B0 := 1) (m1 := m) (B1 := M)
      zero_lt_one hm (fun _ => le_rfl) (fun _ => le_rfl)
      (fun t => (hbounds t).1) (fun t => (hbounds t).2)
      (norm_stripDualWitness_leftBoundary_le L H1 H2 H3 H4 hL hn h1 h2 h3 h4)
      (norm_stripDualWitness_rightBoundary_le_sqrt L H1 H2 H3 H4 hL hn h1 h4)
    have h' : Real.log ‖stripDualWitness L H1 H2 H3 H4 (θ : ℂ)‖ ≤
        θ * (∫ t : ℝ, HirschmanInterpolation.beta θ t *
          Real.log (Real.sqrt (fourMatrixIntegrand H1 H2 H3 H4 t)) ∂volume) := by
      simpa only [Real.log_one, mul_zero, integral_zero, zero_mul, zero_add] using h
    exact (div_le_iff₀ hθ.1).mpr (by simpa only [mul_comm] using h')
  have hlimit := le_of_tendsto_of_tendsto
    (tendsto_gibbs_log_norm_stripDualWitness_div H1 H2 H3 H4 h1 h2 h3 h4)
    (HirschmanInterpolation.tendsto_integral_beta_mul_log_majorant
      (fun t : ℝ => Real.sqrt (fourMatrixIntegrand H1 H2 H3 H4 t))
      (continuous_sqrt_fourMatrixIntegrand H1 H2 H3 H4) hm
      (fun t => (hbounds t).1) (fun t => (hbounds t).2)) hle
  rw [integral_log_sqrt_fourMatrixIntegrand_eq_half H1 H2 H3 H4 h1 h4] at hlimit
  linarith

theorem four_matrix_gt (H1 H2 H3 H4 : CMat I)
    (h1 : H1.IsHermitian) (h2 : H2.IsHermitian)
    (h3 : H3.IsHermitian) (h4 : H4.IsHermitian) :
    (exp (H1 + H2 + H3 + H4)).trace.re ≤
      ∫ t : ℝ, SBTProbabilityWeight.beta0 t *
        fourMatrixIntegrand H1 H2 H3 H4 t ∂volume := by
  classical
  cases isEmpty_or_nonempty I with
  | inl hI =>
    haveI := hI
    exact four_matrix_gt_of_isEmpty H1 H2 H3 H4
  | inr hI =>
    haveI := hI
    have hS : (H1 + H2 + H3 + H4).IsHermitian := ((h1.add h2).add h3).add h4
    calc
      _ = Real.exp (Real.log (exp (H1 + H2 + H3 + H4)).trace.re) :=
        (Real.exp_log (exp_trace_re_pos hS)).symm
      _ ≤ Real.exp (∫ t : ℝ, SBTProbabilityWeight.beta0 t *
          Real.log (fourMatrixIntegrand H1 H2 H3 H4 t) ∂volume) :=
        Real.exp_le_exp.mpr (log_partition_le_weighted_log_integrand H1 H2 H3 H4 h1 h2 h3 h4)
      _ ≤ _ := exp_integral_log_fourMatrixIntegrand_le_integral H1 H2 H3 H4 h1 h2 h3 h4

end QuantumProver.FourMatrixGoldenThompson

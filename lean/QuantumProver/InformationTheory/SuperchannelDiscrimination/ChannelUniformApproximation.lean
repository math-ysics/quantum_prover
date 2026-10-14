import QuantumProver.InformationTheory.SuperchannelDiscrimination.CPTPKraus
import QuantumProver.InformationTheory.SuperchannelDiscrimination.PetzSmoothing

set_option autoImplicit false

noncomputable section

open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder Matrix Kronecker

namespace QuantumProver.SuperchannelDiscrimination.ChannelUniformApproximation

variable {I O E F : Type*} [Fintype I] [Fintype O] [Fintype E] [Fintype F]
  [DecidableEq I] [DecidableEq O] [DecidableEq E] [DecidableEq F]

theorem matrix_real_smul (a : ℝ) (M : Matrix I O ℂ) :
    a • M = (a : ℂ) • M := by
  ext i j
  simp only [Matrix.smul_apply, Complex.real_smul, smul_eq_mul]

def krausColumns (K : F → Matrix O I ℂ) : Matrix (I × O) F ℂ :=
  fun x f => K f x.2 x.1

theorem choi_krausMap (K : F → Matrix O I ℂ) :
    CPTPKraus.choi (QuantumProver.ElegantJointMeasurement.CP.krausMap K) = krausColumns K * (krausColumns K)ᴴ := by
  ext ⟨i, o⟩ ⟨j, p⟩
  change (∑ f : F, K f * Matrix.single i j (1 : ℂ) * (K f)ᴴ) o p = _
  simp only [Matrix.sum_apply, QuantumProver.ElegantJointMeasurement.CP.kraus_matrix_unit]
  rfl

def mixEnvironment (C : Matrix E F ℂ) (K : F → Matrix O I ℂ) : E → Matrix O I ℂ :=
  fun e => ∑ f : F, C e f • K f

theorem mixEnvironment_columns (C : Matrix E F ℂ) (K : F → Matrix O I ℂ) :
    krausColumns (mixEnvironment C K) = krausColumns K * Cᵀ := by
  ext ⟨i, o⟩ e
  simp [krausColumns, mixEnvironment, Matrix.sum_apply, Matrix.smul_apply,
    Matrix.mul_apply, Matrix.transpose_apply, mul_comm]

theorem choi_mixEnvironment (C : Matrix E F ℂ) (K : F → Matrix O I ℂ) :
    CPTPKraus.choi (QuantumProver.ElegantJointMeasurement.CP.krausMap (mixEnvironment C K)) =
      krausColumns K * (Cᴴ * C)ᵀ * (krausColumns K)ᴴ := by
  rw [choi_krausMap, mixEnvironment_columns, Matrix.conjTranspose_mul]
  simp only [Matrix.conjTranspose_transpose, Matrix.transpose_mul,
    Matrix.transpose_conjTranspose, Matrix.mul_assoc]

theorem choi_environment_difference (C : Matrix E F ℂ) (K : F → Matrix O I ℂ) (c : ℝ) :
    (c : ℂ) • CPTPKraus.choi (QuantumProver.ElegantJointMeasurement.CP.krausMap K) -
      CPTPKraus.choi (QuantumProver.ElegantJointMeasurement.CP.krausMap (mixEnvironment C K)) =
      krausColumns K * ((c : ℂ) • (1 : Matrix F F ℂ) - Cᴴ * C)ᵀ *
        (krausColumns K)ᴴ := by
  rw [choi_krausMap, choi_mixEnvironment]
  simp only [Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_one,
    Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]

theorem mixEnvironment_cpDom (C : Matrix E F ℂ) (K : F → Matrix O I ℂ) (c : ℝ)
    (hcap : ((c : ℂ) • (1 : Matrix F F ℂ) - Cᴴ * C).PosSemidef) :
    CPTPKraus.CPDom (QuantumProver.ElegantJointMeasurement.CP.krausMap (mixEnvironment C K)) (QuantumProver.ElegantJointMeasurement.CP.krausMap K) c := by
  apply (CPTPKraus.choi_cp_order_iff _ _ c).mp
  rw [choi_environment_difference]
  exact hcap.transpose.mul_mul_conjTranspose_same (krausColumns K)

theorem mixEnvironment_completelyPositive (C : Matrix E F ℂ) (K : F → Matrix O I ℂ) :
    CPTPKraus.CompletelyPositive (QuantumProver.ElegantJointMeasurement.CP.krausMap (mixEnvironment C K)) :=
  (CPTPKraus.completelyPositive_iff_EJMCP _).mpr (QuantumProver.ElegantJointMeasurement.CP.krausMap_completelyPositive _)

theorem krausMap_traceNonincreasing (K : F → Matrix O I ℂ)
    (hres : (1 - ∑ f : F, (K f)ᴴ * K f).PosSemidef) :
    CPTPKraus.TraceNonincreasing (QuantumProver.ElegantJointMeasurement.CP.krausMap K) := by
  intro X hX
  have hnon := CPTPKraus.trace_pairing_nonneg hres hX
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub] at hnon
  rw [QuantumProver.ElegantJointMeasurement.CP.krausMap_trace]
  exact sub_nonneg.mp hnon

theorem mixEnvironment_amplify_dom (C : Matrix E F ℂ) (K : F → Matrix O I ℂ) (c : ℝ)
    (hcap : ((c : ℂ) • (1 : Matrix F F ℂ) - Cᴴ * C).PosSemidef)
    (R : Type*) [Fintype R] [DecidableEq R]
    {X : Matrix (I × R) (I × R) ℂ} (hX : X.PosSemidef) :
    ((c : ℂ) • CPTPKraus.amplify (QuantumProver.ElegantJointMeasurement.CP.krausMap K) R X -
      CPTPKraus.amplify (QuantumProver.ElegantJointMeasurement.CP.krausMap (mixEnvironment C K)) R X).PosSemidef := by
  have h := CPTPKraus.amplify_posSemidef _ (mixEnvironment_cpDom C K c hcap) R hX
  exact h

def traceOutput (J : Matrix (I × O) (I × O) ℂ) : Matrix I I ℂ :=
  fun i j => ∑ o : O, J (i, o) (j, o)

theorem traceOutput_posSemidef {J : Matrix (I × O) (I × O) ℂ} (hJ : J.PosSemidef) :
    (traceOutput J).PosSemidef := by
  have h := Matrix.posSemidef_sum Finset.univ
    (fun o (_ : o ∈ Finset.univ) => hJ.submatrix (fun i : I => (i, o)))
  convert h using 1
  ext i j
  simp [traceOutput, Matrix.sum_apply]

theorem traceOutput_sub (J Z : Matrix (I × O) (I × O) ℂ) :
    traceOutput (J - Z) = traceOutput J - traceOutput Z := by
  ext i j
  simp [traceOutput, Matrix.sub_apply, Finset.sum_sub_distrib]

theorem traceOutput_krausColumns (K : F → Matrix O I ℂ) :
    traceOutput (krausColumns K * (krausColumns K)ᴴ) =
      (∑ f : F, (K f)ᴴ * K f)ᵀ := by
  ext i j
  simp only [traceOutput, krausColumns, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.transpose_apply, Matrix.sum_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro f hf
  apply Finset.sum_congr rfl
  intro o ho
  exact mul_comm _ _

theorem residual_gram_bound (K : F → Matrix O I ℂ)
    (Z : Matrix (I × O) (I × O) ℂ)
    (hres : (Z - krausColumns K * (krausColumns K)ᴴ).PosSemidef) :
    ((traceOutput Z)ᵀ - ∑ f : F, (K f)ᴴ * K f).PosSemidef := by
  have h := (traceOutput_posSemidef hres).transpose
  simpa only [traceOutput_sub, traceOutput_krausColumns, Matrix.transpose_sub,
    Matrix.transpose_transpose] using h

def stackKraus (K : F → Matrix O I ℂ) : Matrix (O × F) I ℂ :=
  fun x i => K x.2 x.1 i

theorem stackKraus_gram (K : F → Matrix O I ℂ) :
    (stackKraus K)ᴴ * stackKraus K = ∑ f : F, (K f)ᴴ * K f := by
  ext i j
  simp only [stackKraus, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.sum_apply, Fintype.sum_prod_type]
  exact Finset.sum_comm

open scoped Matrix.Norms.L2Operator in

theorem residual_stinespring_norm_sq_bound (K : F → Matrix O I ℂ)
    (Z : Matrix (I × O) (I × O) ℂ)
    (hres : (Z - krausColumns K * (krausColumns K)ᴴ).PosSemidef) :
    ‖stackKraus K‖ ^ 2 ≤ ‖(traceOutput Z)ᵀ‖ := by
  have hgram : ((stackKraus K)ᴴ * stackKraus K).PosSemidef :=
    Matrix.posSemidef_conjTranspose_mul_self _
  have hbound : ((traceOutput Z)ᵀ - (stackKraus K)ᴴ * stackKraus K).PosSemidef := by
    rw [stackKraus_gram]
    exact residual_gram_bound K Z hres
  have hnorm := CStarAlgebra.norm_le_norm_of_le_of_nonneg
    (sub_nonneg.mp hbound.nonneg) hgram.nonneg
  simpa only [Matrix.l2_opNorm_conjTranspose_mul_self, pow_two] using hnorm

end QuantumProver.SuperchannelDiscrimination.ChannelUniformApproximation

namespace QuantumProver.SuperchannelDiscrimination.ChannelUniformApproximation

open scoped Matrix.Norms.L2Operator

variable {I O E F : Type*} [Fintype I] [Fintype O] [Fintype E] [Fintype F]
  [DecidableEq I] [DecidableEq O] [DecidableEq E] [DecidableEq F]

def residualKraus (K : E → Matrix O I ℂ) (C : Matrix E F ℂ)
    (B : F → Matrix O I ℂ) : E → Matrix O I ℂ :=
  fun e => K e - mixEnvironment C B e

theorem residualKraus_columns (K : E → Matrix O I ℂ) (C : Matrix E F ℂ)
    (B : F → Matrix O I ℂ) :
    krausColumns (residualKraus K C B) = krausColumns K - krausColumns B * Cᵀ := by
  rw [← mixEnvironment_columns C B]
  rfl

theorem residualKraus_stack (K : E → Matrix O I ℂ) (C : Matrix E F ℂ)
    (B : F → Matrix O I ℂ) :
    stackKraus (residualKraus K C B) = stackKraus K - stackKraus (mixEnvironment C B) := rfl

theorem exists_global_dominated_kraus_approximation
    (K : E → Matrix O I ℂ) (B : F → Matrix O I ℂ)
    {Z : Matrix (I × O) (I × O) ℂ} (hZ : Z.PosSemidef)
    (t : ℝ) (ht : 0 ≤ t)
    (hdom : (t • CPTPKraus.choi (QuantumProver.ElegantJointMeasurement.CP.krausMap B) + Z -
      CPTPKraus.choi (QuantumProver.ElegantJointMeasurement.CP.krausMap K)).PosSemidef) :
    ∃ C : Matrix E F ℂ,
      ‖C‖ ^ 2 ≤ t ∧
      CPTPKraus.CompletelyPositive (QuantumProver.ElegantJointMeasurement.CP.krausMap (mixEnvironment C B)) ∧
      CPTPKraus.CPDom (QuantumProver.ElegantJointMeasurement.CP.krausMap (mixEnvironment C B)) (QuantumProver.ElegantJointMeasurement.CP.krausMap B) t ∧
      (Z - krausColumns (residualKraus K C B) *
        (krausColumns (residualKraus K C B))ᴴ).PosSemidef ∧
      ‖stackKraus K - stackKraus (mixEnvironment C B)‖ ^ 2 ≤ ‖(traceOutput Z)ᵀ‖ := by
  rw [choi_krausMap, choi_krausMap] at hdom
  obtain ⟨C, hcap, hnorm, hres⟩ :=
    GlobalMatrixSplit.exists_global_environmental_split (krausColumns B)
      (krausColumns K) hZ t ht hdom
  have hcap' : ((t : ℂ) • (1 : Matrix F F ℂ) - Cᴴ * C).PosSemidef := by
    simpa only [matrix_real_smul] using hcap
  have hres' : (Z - krausColumns (residualKraus K C B) *
      (krausColumns (residualKraus K C B))ᴴ).PosSemidef := by
    simpa only [residualKraus_columns] using hres
  refine ⟨C, hnorm, mixEnvironment_completelyPositive C B,
    mixEnvironment_cpDom C B t hcap', hres', ?_⟩
  simpa only [residualKraus_stack] using
    residual_stinespring_norm_sq_bound (residualKraus K C B) Z hres'

theorem exists_exact_environmental_kraus_comparison
    (K : E → Matrix O I ℂ) (B : F → Matrix O I ℂ)
    (hs : FlaggedStates.HasSupportIn (CPTPKraus.choi (QuantumProver.ElegantJointMeasurement.CP.krausMap K))
      (CPTPKraus.choi (QuantumProver.ElegantJointMeasurement.CP.krausMap B))) :
    ∃ c : ℝ, 1 ≤ c ∧ ∃ C : Matrix E F ℂ,
      ‖C‖ ^ 2 ≤ c ∧ mixEnvironment C B = K ∧
      CPTPKraus.CPDom (QuantumProver.ElegantJointMeasurement.CP.krausMap K) (QuantumProver.ElegantJointMeasurement.CP.krausMap B) c := by
  rw [choi_krausMap, choi_krausMap] at hs
  obtain ⟨c, hc, C, heq, hcap, hnorm⟩ :=
    GlobalMatrixSplit.exists_exact_environmental_factor_of_support
      (krausColumns B) (krausColumns K) hs
  have hmix : mixEnvironment C B = K := by
    funext e
    ext o i
    exact congrArg (fun M : Matrix (I × O) E ℂ => M (i, o) e)
      ((mixEnvironment_columns C B).trans heq)
  have hcap' : ((c : ℂ) • (1 : Matrix F F ℂ) - Cᴴ * C).PosSemidef := by
    simpa only [matrix_real_smul] using hcap
  refine ⟨c, hc, C, hnorm, hmix, ?_⟩
  simpa only [hmix] using mixEnvironment_cpDom C B c hcap'

end QuantumProver.SuperchannelDiscrimination.ChannelUniformApproximation

namespace QuantumProver.SuperchannelDiscrimination.ChannelUniformApproximation

open scoped Matrix.Norms.L2Operator

variable {I O E F : Type*} [Fintype I] [Fintype O] [Fintype E] [Fintype F]
  [DecidableEq I] [DecidableEq O] [DecidableEq E] [DecidableEq F]

theorem krausMap_traceNonincreasing_of_stack_norm_le_one
    (K : E → Matrix O I ℂ) (hK : ‖stackKraus K‖ ≤ 1) :
    CPTPKraus.TraceNonincreasing (QuantumProver.ElegantJointMeasurement.CP.krausMap K) := by
  have hgram : ((stackKraus K)ᴴ * stackKraus K).PosSemidef :=
    Matrix.posSemidef_conjTranspose_mul_self _
  have hn : ‖(stackKraus K)ᴴ * stackKraus K‖ ≤ 1 := by
    rw [Matrix.l2_opNorm_conjTranspose_mul_self]
    nlinarith [norm_nonneg (stackKraus K)]
  have ho := (CStarAlgebra.norm_le_iff_le_algebraMap
    ((stackKraus K)ᴴ * stackKraus K) zero_le_one hgram.nonneg).mp hn
  apply krausMap_traceNonincreasing
  rw [← stackKraus_gram]
  apply Matrix.nonneg_iff_posSemidef.mp
  apply sub_nonneg.mpr
  simpa only [map_one] using ho

theorem stackKraus_norm_le_one_of_complete
    (K : E → Matrix O I ℂ) (hK : ∑ e : E, (K e)ᴴ * K e = 1) :
    ‖stackKraus K‖ ≤ 1 := by
  have hcap : ((1 : ℝ) • (1 : Matrix I I ℂ) -
      (stackKraus K)ᴴ * stackKraus K).PosSemidef := by
    rw [stackKraus_gram, hK]
    simpa using (Matrix.PosSemidef.zero : (0 : Matrix I I ℂ).PosSemidef)
  have hsq := GlobalMatrixSplit.norm_sq_le_of_right_gram zero_le_one hcap
  nlinarith [norm_nonneg (stackKraus K)]

theorem mixEnvironment_cpDom_of_norm_sq
    (C : Matrix E F ℂ) (B : F → Matrix O I ℂ) (t : ℝ) (ht : 0 ≤ t)
    (hC : ‖C‖ ^ 2 ≤ t) :
    CPTPKraus.CPDom (QuantumProver.ElegantJointMeasurement.CP.krausMap (mixEnvironment C B)) (QuantumProver.ElegantJointMeasurement.CP.krausMap B) t := by
  have hgram : (Cᴴ * C).PosSemidef := Matrix.posSemidef_conjTranspose_mul_self C
  have hn : ‖Cᴴ * C‖ ≤ t := by
    simpa only [Matrix.l2_opNorm_conjTranspose_mul_self, pow_two] using hC
  have ho := (CStarAlgebra.norm_le_iff_le_algebraMap (Cᴴ * C) ht hgram.nonneg).mp hn
  change (algebraMap ℝ (Matrix F F ℂ) t - Cᴴ * C).PosSemidef at ho
  have hcap : (t • (1 : Matrix F F ℂ) - Cᴴ * C).PosSemidef := by
    simpa only [Algebra.algebraMap_eq_smul_one] using ho
  apply mixEnvironment_cpDom
  simpa only [matrix_real_smul] using hcap

theorem mixEnvironment_smul (z : ℂ) (C : Matrix E F ℂ) (B : F → Matrix O I ℂ) :
    mixEnvironment (z • C) B = fun e => z • mixEnvironment C B e := by
  funext e
  simp only [mixEnvironment, Matrix.smul_apply, smul_smul, Finset.smul_sum, smul_eq_mul]

theorem normalized_environmental_approximation
    (K : E → Matrix O I ℂ) (B : F → Matrix O I ℂ) (C : Matrix E F ℂ)
    (hK : ∑ e : E, (K e)ᴴ * K e = 1)
    {δ t : ℝ} (hδ : 0 ≤ δ) (ht : 0 ≤ t) (hC : ‖C‖ ^ 2 ≤ t)
    (hres : ‖stackKraus K - stackKraus (mixEnvironment C B)‖ ≤ δ) :
    let C' := (((1 + δ)⁻¹ : ℝ) : ℂ) • C
    CPTPKraus.CompletelyPositive (QuantumProver.ElegantJointMeasurement.CP.krausMap (mixEnvironment C' B)) ∧
      CPTPKraus.TraceNonincreasing (QuantumProver.ElegantJointMeasurement.CP.krausMap (mixEnvironment C' B)) ∧
      CPTPKraus.CPDom (QuantumProver.ElegantJointMeasurement.CP.krausMap (mixEnvironment C' B)) (QuantumProver.ElegantJointMeasurement.CP.krausMap B) t ∧
      ‖C'‖ ^ 2 ≤ t := by
  let α : ℝ := (1 + δ)⁻¹
  have hden : 0 < 1 + δ := by linarith
  have hα0 : 0 ≤ α := (inv_pos.mpr hden).le
  have hα1 : α ≤ 1 := by
    dsimp [α]
    exact (inv_le_one₀ hden).mpr (by linarith)
  have hαnorm : ‖(α : ℂ)‖ = α := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hα0]
  have hnormC : ‖(α : ℂ) • C‖ ≤ ‖C‖ := by
    rw [norm_smul, hαnorm]
    nlinarith [norm_nonneg C]
  have hsqC : ‖(α : ℂ) • C‖ ^ 2 ≤ t := by
    nlinarith [norm_nonneg ((α : ℂ) • C), norm_nonneg C]
  have hS : ‖stackKraus (mixEnvironment C B)‖ ≤ 1 + δ := by
    calc
      ‖stackKraus (mixEnvironment C B)‖ =
          ‖stackKraus K - (stackKraus K - stackKraus (mixEnvironment C B))‖ := by
        congr 1
        abel
      _ ≤ ‖stackKraus K‖ + ‖stackKraus K - stackKraus (mixEnvironment C B)‖ :=
        norm_sub_le _ _
      _ ≤ 1 + δ := add_le_add (stackKraus_norm_le_one_of_complete K hK) hres
  have hstack : stackKraus (mixEnvironment ((α : ℂ) • C) B) =
      (α : ℂ) • stackKraus (mixEnvironment C B) := by
    rw [mixEnvironment_smul]
    rfl
  have hnorm : ‖stackKraus (mixEnvironment ((α : ℂ) • C) B)‖ ≤ 1 := by
    rw [hstack, norm_smul, hαnorm]
    calc
      α * ‖stackKraus (mixEnvironment C B)‖ ≤ α * (1 + δ) :=
        mul_le_mul_of_nonneg_left hS hα0
      _ = 1 := inv_mul_cancel₀ (ne_of_gt hden)
  exact ⟨mixEnvironment_completelyPositive _ B,
    krausMap_traceNonincreasing_of_stack_norm_le_one _ hnorm,
    mixEnvironment_cpDom_of_norm_sq _ B t ht hsqC, hsqC⟩

end QuantumProver.SuperchannelDiscrimination.ChannelUniformApproximation

namespace QuantumProver.SuperchannelDiscrimination.ChannelUniformApproximation

open scoped Matrix.Norms.L2Operator

variable {I O E F J : Type*}
  [Fintype I] [Fintype O] [Fintype E] [Fintype F] [Fintype J]
  [DecidableEq I] [DecidableEq O] [DecidableEq E] [DecidableEq F] [DecidableEq J]

theorem normalized_environmental_residual_norm
    (K : E → Matrix O I ℂ) (B : F → Matrix O I ℂ) (C : Matrix E F ℂ)
    (hK : ∑ e : E, (K e)ᴴ * K e = 1) {δ : ℝ} (hδ : 0 ≤ δ)
    (hres : ‖stackKraus K - stackKraus (mixEnvironment C B)‖ ≤ δ) :
    ‖stackKraus K - stackKraus
      (mixEnvironment ((((1 + δ)⁻¹ : ℝ) : ℂ) • C) B)‖ ≤ 2 * δ := by
  let α : ℝ := (1 + δ)⁻¹
  let V := stackKraus K
  let W := stackKraus (mixEnvironment C B)
  have hden : 0 < 1 + δ := by linarith
  have hα0 : 0 ≤ α := (inv_pos.mpr hden).le
  have hα1 : α ≤ 1 := (inv_le_one₀ hden).mpr (by linarith)
  have hαid : α * (1 + δ) = 1 := inv_mul_cancel₀ (ne_of_gt hden)
  have hαnorm : ‖(α : ℂ)‖ = α := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hα0]
  have hαsubnorm : ‖(1 : ℂ) - (α : ℂ)‖ = 1 - α := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hα1)]
  have hstack : stackKraus (mixEnvironment ((α : ℂ) • C) B) = (α : ℂ) • W := by
    rw [mixEnvironment_smul]
    rfl
  have heq : V - (α : ℂ) • W =
      ((1 : ℂ) - (α : ℂ)) • V + (α : ℂ) • (V - W) := by
    rw [sub_smul, smul_sub, one_smul]
    abel
  rw [show (((1 + δ)⁻¹ : ℝ) : ℂ) = (α : ℂ) from rfl, hstack, heq]
  calc
    ‖((1 : ℂ) - (α : ℂ)) • V + (α : ℂ) • (V - W)‖ ≤
        ‖((1 : ℂ) - (α : ℂ)) • V‖ + ‖(α : ℂ) • (V - W)‖ := norm_add_le _ _
    _ = (1 - α) * ‖V‖ + α * ‖V - W‖ := by rw [norm_smul, norm_smul, hαsubnorm, hαnorm]
    _ ≤ (1 - α) * 1 + α * δ := add_le_add
      (mul_le_mul_of_nonneg_left (stackKraus_norm_le_one_of_complete K hK)
        (sub_nonneg.mpr hα1))
      (mul_le_mul_of_nonneg_left hres hα0)
    _ ≤ 2 * δ := by nlinarith

theorem effect_operator_norm_le_one {Q : Matrix J J ℂ} (hQ : FlaggedStates.IsEffect Q) :
    ‖Q‖ ≤ 1 := by
  apply (CStarAlgebra.norm_le_iff_le_algebraMap Q zero_le_one hQ.1.nonneg).mpr
  simpa only [map_one] using (sub_nonneg.mp hQ.2.nonneg)

theorem dilation_effect_pullback_error
    (V W : Matrix J I ℂ) {Q : Matrix J J ℂ} (hQ : FlaggedStates.IsEffect Q) :
    ‖Vᴴ * Q * V - Wᴴ * Q * W‖ ≤ ‖V - W‖ * (‖V‖ + ‖W‖) := by
  have heq : Vᴴ * Q * V - Wᴴ * Q * W =
      (V - W)ᴴ * Q * V + Wᴴ * Q * (V - W) := by
    simp only [Matrix.conjTranspose_sub, Matrix.sub_mul, Matrix.mul_sub]
    abel
  have hQn := effect_operator_norm_le_one hQ
  have hL : ‖(V - W)ᴴ * Q * V‖ ≤ ‖V - W‖ * ‖V‖ := by
    calc
      _ ≤ ‖(V - W)ᴴ * Q‖ * ‖V‖ := Matrix.l2_opNorm_mul _ _
      _ ≤ (‖(V - W)ᴴ‖ * ‖Q‖) * ‖V‖ :=
        mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _)
      _ ≤ ‖V - W‖ * ‖V‖ := by
        rw [Matrix.l2_opNorm_conjTranspose]
        exact mul_le_mul_of_nonneg_right
          (by nlinarith [norm_nonneg (V - W)]) (norm_nonneg V)
  have hR : ‖Wᴴ * Q * (V - W)‖ ≤ ‖W‖ * ‖V - W‖ := by
    calc
      _ ≤ ‖Wᴴ * Q‖ * ‖V - W‖ := Matrix.l2_opNorm_mul _ _
      _ ≤ (‖Wᴴ‖ * ‖Q‖) * ‖V - W‖ :=
        mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _)
      _ ≤ ‖W‖ * ‖V - W‖ := by
        rw [Matrix.l2_opNorm_conjTranspose]
        exact mul_le_mul_of_nonneg_right
          (by nlinarith [norm_nonneg W]) (norm_nonneg (V - W))
  rw [heq]
  exact (norm_add_le _ _).trans ((add_le_add hL hR).trans_eq (by ring))

end QuantumProver.SuperchannelDiscrimination.ChannelUniformApproximation

namespace QuantumProver.SuperchannelDiscrimination.ChannelUniformApproximation

open scoped Matrix.Norms.L2Operator

variable {I O : Type*} [Fintype I] [Fintype O] [DecidableEq I] [DecidableEq O]

theorem posSemidef_opNorm_transpose {A : Matrix I I ℂ} (hA : A.PosSemidef) :
    ‖Aᵀ‖ = ‖A‖ := by
  have hbound (M : Matrix I I ℂ) (hM : M.PosSemidef) : ‖Mᵀ‖ ≤ ‖M‖ := by
    have ho := (CStarAlgebra.norm_le_iff_le_algebraMap M (norm_nonneg M) hM.nonneg).mp
      (le_refl ‖M‖)
    change (algebraMap ℝ (Matrix I I ℂ) ‖M‖ - M).PosSemidef at ho
    have hcap : (‖M‖ • (1 : Matrix I I ℂ) - Mᵀ).PosSemidef := by
      simpa only [Algebra.algebraMap_eq_smul_one, Matrix.transpose_sub,
        Matrix.transpose_smul, Matrix.transpose_one] using ho.transpose
    apply (CStarAlgebra.norm_le_iff_le_algebraMap Mᵀ (norm_nonneg M)
      hM.transpose.nonneg).mpr
    change (algebraMap ℝ (Matrix I I ℂ) ‖M‖ - Mᵀ).PosSemidef
    simpa only [Algebra.algebraMap_eq_smul_one] using hcap
  apply le_antisymm (hbound A hA)
  simpa only [Matrix.transpose_transpose] using hbound Aᵀ hA.transpose

theorem global_dual_marginal_norm_transpose
    {Z : Matrix (I × O) (I × O) ℂ} (hZ : Z.PosSemidef) :
    ‖(traceOutput Z)ᵀ‖ = ‖traceOutput Z‖ :=
  posSemidef_opNorm_transpose (traceOutput_posSemidef hZ)

end QuantumProver.SuperchannelDiscrimination.ChannelUniformApproximation

namespace QuantumProver.SuperchannelDiscrimination.ChannelUniformApproximation

open scoped Matrix.Norms.L2Operator

variable {I O F : Type*} [Fintype I] [Fintype O] [Fintype F]
  [DecidableEq I] [DecidableEq O] [DecidableEq F]

def referenceKraus (K : F → Matrix O I ℂ) (R : Type*) [Fintype R] [DecidableEq R] :
    F → Matrix (O × R) (I × R) ℂ := fun f => K f ⊗ₖ (1 : Matrix R R ℂ)

theorem referenceKraus_block (K : F → Matrix O I ℂ)
    (R : Type*) [Fintype R] [DecidableEq R]
    (f : F) (X : Matrix (I × R) (I × R) ℂ) (o p : O) (r s : R) :
    (referenceKraus K R f * X * (referenceKraus K R f)ᴴ) (o, r) (p, s) =
      (K f * Matrix.of (fun i j => X (i, r) (j, s)) * (K f)ᴴ) o p := by
  simp [referenceKraus, Matrix.mul_apply, Matrix.kronecker_apply,
    Matrix.one_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Fintype.sum_prod_type,
    apply_ite, mul_ite, ite_mul]

theorem referenceKraus_reconstruct (K : F → Matrix O I ℂ)
    (R : Type*) [Fintype R] [DecidableEq R]
    (X : Matrix (I × R) (I × R) ℂ) :
    QuantumProver.ElegantJointMeasurement.CP.krausMap (referenceKraus K R) X = CPTPKraus.amplify (QuantumProver.ElegantJointMeasurement.CP.krausMap K) R X := by
  ext ⟨o, r⟩ ⟨p, s⟩
  change (∑ f : F, referenceKraus K R f * X * (referenceKraus K R f)ᴴ) (o, r) (p, s) = _
  simp only [Matrix.sum_apply, referenceKraus_block]
  change (∑ f : F, (K f * Matrix.of (fun i j => X (i, r) (j, s)) * (K f)ᴴ) o p) =
    (∑ f : F, K f * Matrix.of (fun i j => X (i, r) (j, s)) * (K f)ᴴ) o p
  simp only [Matrix.sum_apply]

theorem referenceKraus_gram (K : F → Matrix O I ℂ)
    (R : Type*) [Fintype R] [DecidableEq R] :
    (∑ f : F, (referenceKraus K R f)ᴴ * referenceKraus K R f) =
      (∑ f : F, (K f)ᴴ * K f) ⊗ₖ (1 : Matrix R R ℂ) := by
  simp only [referenceKraus, Matrix.conjTranspose_kronecker,
    Matrix.conjTranspose_one, ← Matrix.mul_kronecker_mul, Matrix.one_mul]
  ext i j
  simp [Matrix.sum_apply, Matrix.kronecker_apply, Finset.sum_mul]

theorem referenceKraus_stack_norm_le (K : F → Matrix O I ℂ)
    (R : Type*) [Fintype R] [DecidableEq R] :
    ‖stackKraus (referenceKraus K R)‖ ≤ ‖stackKraus K‖ := by
  let c : ℝ := ‖stackKraus K‖ ^ 2
  have hc : 0 ≤ c := sq_nonneg _
  have hG : ((stackKraus K)ᴴ * stackKraus K).PosSemidef :=
    Matrix.posSemidef_conjTranspose_mul_self _
  have hn : ‖(stackKraus K)ᴴ * stackKraus K‖ ≤ c := by
    simp only [Matrix.l2_opNorm_conjTranspose_mul_self, c, pow_two, le_refl]
  have ho := (CStarAlgebra.norm_le_iff_le_algebraMap
    ((stackKraus K)ᴴ * stackKraus K) hc hG.nonneg).mp hn
  change (algebraMap ℝ (Matrix I I ℂ) c - (stackKraus K)ᴴ * stackKraus K).PosSemidef at ho
  have hcap : (c • (1 : Matrix I I ℂ) - ∑ f : F, (K f)ᴴ * K f).PosSemidef := by
    simpa only [Algebra.algebraMap_eq_smul_one, stackKraus_gram] using ho
  have h := hcap.kronecker (Matrix.PosSemidef.one : (1 : Matrix R R ℂ).PosSemidef)
  have hsub (A B : Matrix I I ℂ) :
      (A - B) ⊗ₖ (1 : Matrix R R ℂ) =
        A ⊗ₖ (1 : Matrix R R ℂ) - B ⊗ₖ (1 : Matrix R R ℂ) := by
    ext ⟨i, r⟩ ⟨j, s⟩
    simp [Matrix.kronecker_apply, Matrix.sub_apply, sub_mul]
  rw [hsub, Matrix.smul_kronecker, Matrix.one_kronecker_one] at h
  have hcapR : (c • (1 : Matrix (I × R) (I × R) ℂ) -
      (stackKraus (referenceKraus K R))ᴴ * stackKraus (referenceKraus K R)).PosSemidef := by
    rw [stackKraus_gram, referenceKraus_gram]
    exact h
  have hsq := GlobalMatrixSplit.norm_sq_le_of_right_gram hc hcapR
  change ‖stackKraus (referenceKraus K R)‖ ^ 2 ≤ ‖stackKraus K‖ ^ 2 at hsq
  nlinarith [norm_nonneg (stackKraus (referenceKraus K R)), norm_nonneg (stackKraus K)]

theorem referenceKraus_sub (K L : F → Matrix O I ℂ)
    (R : Type*) [Fintype R] [DecidableEq R] :
    referenceKraus (fun f => K f - L f) R =
      fun f => referenceKraus K R f - referenceKraus L R f := by
  funext f
  ext ⟨o, r⟩ ⟨i, s⟩
  simp [referenceKraus, Matrix.kronecker_apply, Matrix.sub_apply, sub_mul]

theorem referenceKraus_stack_difference_norm_le (K L : F → Matrix O I ℂ)
    (R : Type*) [Fintype R] [DecidableEq R] :
    ‖stackKraus (referenceKraus K R) - stackKraus (referenceKraus L R)‖ ≤
      ‖stackKraus K - stackKraus L‖ := by
  have h := referenceKraus_stack_norm_le (fun f => K f - L f) R
  rw [referenceKraus_sub] at h
  exact h

theorem reference_dilation_effect_pullback_error
    (K L : F → Matrix O I ℂ) (R : Type*) [Fintype R] [DecidableEq R]
    {δ : ℝ} (hδ : 0 ≤ δ) (hK : ‖stackKraus K‖ ≤ 1) (hL : ‖stackKraus L‖ ≤ 1)
    (hdiff : ‖stackKraus K - stackKraus L‖ ≤ δ)
    {Q : Matrix ((O × R) × F) ((O × R) × F) ℂ} (hQ : FlaggedStates.IsEffect Q) :
    ‖(stackKraus (referenceKraus K R))ᴴ * Q * stackKraus (referenceKraus K R) -
      (stackKraus (referenceKraus L R))ᴴ * Q * stackKraus (referenceKraus L R)‖ ≤ 2 * δ := by
  have hK' := (referenceKraus_stack_norm_le K R).trans hK
  have hL' := (referenceKraus_stack_norm_le L R).trans hL
  have hd := (referenceKraus_stack_difference_norm_le K L R).trans hdiff
  have h := dilation_effect_pullback_error
    (stackKraus (referenceKraus K R)) (stackKraus (referenceKraus L R)) hQ
  nlinarith [norm_nonneg (stackKraus (referenceKraus K R) -
    stackKraus (referenceKraus L R)), norm_nonneg (stackKraus (referenceKraus K R)),
    norm_nonneg (stackKraus (referenceKraus L R))]

end QuantumProver.SuperchannelDiscrimination.ChannelUniformApproximation

namespace QuantumProver.SuperchannelDiscrimination.ChannelUniformApproximation

open scoped Matrix.Norms.L2Operator

variable {I O F : Type*} [Fintype I] [Fintype O] [Fintype F]
  [DecidableEq I] [DecidableEq O] [DecidableEq F]

theorem effect_kronecker_identity {Q : Matrix O O ℂ} (hQ : FlaggedStates.IsEffect Q) :
    FlaggedStates.IsEffect (Q ⊗ₖ (1 : Matrix F F ℂ)) := by
  constructor
  · exact hQ.1.kronecker Matrix.PosSemidef.one
  · convert hQ.2.kronecker (Matrix.PosSemidef.one : (1 : Matrix F F ℂ).PosSemidef) using 1
    ext ⟨o, f⟩ ⟨p, g⟩
    by_cases hop : o = p <;> by_cases hfg : f = g <;>
      simp [Matrix.kronecker_apply, Matrix.one_apply, Matrix.sub_apply, hop, hfg]

theorem stackKraus_effect_gram (K : F → Matrix O I ℂ) (Q : Matrix O O ℂ) :
    (stackKraus K)ᴴ * (Q ⊗ₖ (1 : Matrix F F ℂ)) * stackKraus K =
      ∑ f : F, (K f)ᴴ * Q * K f := by
  have hQV : (Q ⊗ₖ (1 : Matrix F F ℂ)) * stackKraus K =
      stackKraus (fun f => Q * K f) := by
    ext ⟨o, f⟩ i
    simp [Matrix.mul_apply, Matrix.kronecker_apply, Matrix.one_apply,
      stackKraus, Fintype.sum_prod_type, ite_mul, mul_ite]
  rw [Matrix.mul_assoc, hQV]
  have hsum : (∑ f : F, (K f)ᴴ * Q * K f) =
      ∑ f : F, (K f)ᴴ * (Q * K f) := by
    simp only [Matrix.mul_assoc]
  rw [hsum]
  ext i j
  simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, stackKraus]
  rw [Fintype.sum_prod_type]
  exact Finset.sum_comm

theorem krausMap_effect_trace_eq_pullback
    (K : F → Matrix O I ℂ) (X : Matrix I I ℂ) (Q : Matrix O O ℂ) :
    (QuantumProver.ElegantJointMeasurement.CP.krausMap K X * Q).trace =
      (X * ((stackKraus K)ᴴ * (Q ⊗ₖ (1 : Matrix F F ℂ)) * stackKraus K)).trace := by
  rw [stackKraus_effect_gram]
  change ((∑ f : F, K f * X * (K f)ᴴ) * Q).trace = _
  simp only [Finset.sum_mul, Finset.mul_sum, Matrix.trace_sum]
  apply Finset.sum_congr rfl
  intro f hf
  calc
    ((K f * X * (K f)ᴴ) * Q).trace = (K f * (X * ((K f)ᴴ * Q))).trace := by
      simp only [Matrix.mul_assoc]
    _ = ((X * ((K f)ᴴ * Q)) * K f).trace := Matrix.trace_mul_comm _ _
    _ = (X * ((K f)ᴴ * Q * K f)).trace := by simp only [Matrix.mul_assoc]

theorem density_trace_pairing_abs_le_opNorm
    {X H : Matrix I I ℂ} (hX : FlaggedStates.IsDensity X) (hH : H.IsHermitian) :
    |(X * H).trace.re| ≤ ‖H‖ := by
  have hupper (M : Matrix I I ℂ) (hM : M.IsHermitian) : (M * X).trace.re ≤ ‖M‖ := by
    have ho := hM.isSelfAdjoint.le_algebraMap_norm_self
    change (algebraMap ℝ (Matrix I I ℂ) ‖M‖ - M).PosSemidef at ho
    have hcap : (((‖M‖ : ℝ) : ℂ) • (1 : Matrix I I ℂ) - M).PosSemidef := by
      simpa only [Algebra.algebraMap_eq_smul_one, matrix_real_smul] using ho
    have ht := FlaggedStates.trace_mul_re_nonneg hcap hX.1
    have ht' : 0 ≤ ‖M‖ - (M * X).trace.re := by
      simpa [Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul,
        Matrix.trace_sub, Matrix.trace_smul, hX.2] using ht
    exact sub_nonneg.mp ht'
  have hup := hupper H hH
  have hlo := hupper (-H) hH.neg
  rw [Matrix.trace_mul_comm X H]
  apply abs_le.mpr
  constructor
  · have hlo' : -(H * X).trace.re ≤ ‖H‖ := by
      simpa only [Matrix.neg_mul, Matrix.trace_neg, Complex.neg_re, norm_neg] using hlo
    linarith
  · exact hup

theorem reference_kraus_born_probability_error
    (K L : F → Matrix O I ℂ) (R : Type*) [Fintype R] [DecidableEq R]
    {δ : ℝ} (hδ : 0 ≤ δ) (hK : ‖stackKraus K‖ ≤ 1) (hL : ‖stackKraus L‖ ≤ 1)
    (hdiff : ‖stackKraus K - stackKraus L‖ ≤ δ)
    {X : Matrix (I × R) (I × R) ℂ} (hX : FlaggedStates.IsDensity X)
    {Q : Matrix (O × R) (O × R) ℂ} (hQ : FlaggedStates.IsEffect Q) :
    |FlaggedStates.acceptanceProbability (CPTPKraus.amplify (QuantumProver.ElegantJointMeasurement.CP.krausMap K) R X) Q -
      FlaggedStates.acceptanceProbability (CPTPKraus.amplify (QuantumProver.ElegantJointMeasurement.CP.krausMap L) R X) Q| ≤ 2 * δ := by
  let V := stackKraus (referenceKraus K R)
  let W := stackKraus (referenceKraus L R)
  let A := Vᴴ * (Q ⊗ₖ (1 : Matrix F F ℂ)) * V
  let B := Wᴴ * (Q ⊗ₖ (1 : Matrix F F ℂ)) * W
  have hQE := effect_kronecker_identity hQ (F := F)
  have hA : A.PosSemidef := by
    simpa only [A, Matrix.conjTranspose_conjTranspose] using
      hQE.1.mul_mul_conjTranspose_same Vᴴ
  have hB : B.PosSemidef := by
    simpa only [B, Matrix.conjTranspose_conjTranspose] using
      hQE.1.mul_mul_conjTranspose_same Wᴴ
  have hn : ‖A - B‖ ≤ 2 * δ :=
    reference_dilation_effect_pullback_error K L R hδ hK hL hdiff hQE
  have ht := density_trace_pairing_abs_le_opNorm hX (hA.isHermitian.sub hB.isHermitian)
  rw [← referenceKraus_reconstruct K R X, ← referenceKraus_reconstruct L R X]
  unfold FlaggedStates.acceptanceProbability
  rw [krausMap_effect_trace_eq_pullback, krausMap_effect_trace_eq_pullback]
  change |(X * A).trace.re - (X * B).trace.re| ≤ 2 * δ
  rw [← Complex.sub_re, ← Matrix.trace_sub, ← Matrix.mul_sub]
  exact ht.trans hn

end QuantumProver.SuperchannelDiscrimination.ChannelUniformApproximation

namespace QuantumProver.SuperchannelDiscrimination.ChannelUniformApproximation

open Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Matrix

variable {I O E F : Type*} [Fintype I] [Fintype O] [Fintype E] [Fintype F]
  [DecidableEq I] [DecidableEq O]

def traceOutputLinear : Matrix (I × O) (I × O) ℂ →ₗ[ℂ] Matrix I I ℂ where
  toFun := traceOutput
  map_add' X Y := by
    ext i j
    simp [traceOutput, Finset.sum_add_distrib]
  map_smul' c X := by
    ext i j
    simp [traceOutput, Finset.mul_sum]

theorem traceOutput_continuous :
    Continuous (traceOutput (I := I) (O := O)) :=
  traceOutputLinear.continuous_of_finiteDimensional

theorem traceOutput_trace (Z : Matrix (I × O) (I × O) ℂ) :
    (traceOutput Z).trace = Z.trace := by
  simp only [Matrix.trace, Matrix.diag, traceOutput, Fintype.sum_prod_type]

theorem posSemidef_opNorm_le_trace {J : Type*} [Fintype J] [DecidableEq J]
    {A : Matrix J J ℂ} (hA : A.PosSemidef) : ‖A‖ ≤ A.trace.re := by
  have ht : 0 ≤ A.trace.re := (Complex.nonneg_iff.mp hA.trace_nonneg).1
  have htr : A.trace.re = ∑ j : J, hA.1.eigenvalues j := by
    have h := congrArg Complex.re hA.1.trace_eq_sum_eigenvalues
    simpa using h
  have hc : ‖cfc (fun x : ℝ => x) A‖ ≤ A.trace.re := by
    apply norm_cfc_le ht
    intro x hx
    rw [hA.1.spectrum_real_eq_range_eigenvalues] at hx
    obtain ⟨j, rfl⟩ := hx
    rw [Real.norm_eq_abs, abs_of_nonneg (hA.eigenvalues_nonneg j), htr]
    exact Finset.single_le_sum (fun k _ => hA.eigenvalues_nonneg k) (Finset.mem_univ j)
  simpa only [cfc_id' ℝ A hA.1.isSelfAdjoint] using hc

theorem posSemidef_trace_le_card_opNorm {J : Type*} [Fintype J] [DecidableEq J]
    {A : Matrix J J ℂ} (hA : A.PosSemidef) :
    A.trace.re ≤ (Fintype.card J : ℝ) * ‖A‖ := by
  have ho := (CStarAlgebra.norm_le_iff_le_algebraMap A (norm_nonneg A) hA.nonneg).mp
    (le_refl ‖A‖)
  have hp : (‖A‖ • (1 : Matrix J J ℂ) - A).PosSemidef := by
    change (algebraMap ℝ (Matrix J J ℂ) ‖A‖ - A).PosSemidef at ho
    simpa only [Algebra.algebraMap_eq_smul_one] using ho
  have ht := (Complex.nonneg_iff.mp hp.trace_nonneg).1
  simp only [Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one,
    Complex.sub_re, Complex.smul_re, Complex.natCast_re, smul_eq_mul] at ht
  nlinarith

theorem global_dual_objective_coercive {Z : Matrix (I × O) (I × O) ℂ}
    (hZ : Z.PosSemidef) : ‖Z‖ ≤ (Fintype.card I : ℝ) * ‖traceOutput Z‖ := by
  calc
    ‖Z‖ ≤ Z.trace.re := posSemidef_opNorm_le_trace hZ
    _ = (traceOutput Z).trace.re := congrArg Complex.re (traceOutput_trace Z).symm
    _ ≤ _ := posSemidef_trace_le_card_opNorm (traceOutput_posSemidef hZ)

def globalDualFeasible (K : E → Matrix O I ℂ) (B : F → Matrix O I ℂ) (t : ℝ) :
    Set (Matrix (I × O) (I × O) ℂ) :=
  {Z | Z.PosSemidef ∧
    (t • (krausColumns B * (krausColumns B)ᴴ) + Z -
      krausColumns K * (krausColumns K)ᴴ).PosSemidef}

def globalDualObjective (Z : Matrix (I × O) (I × O) ℂ) : ℝ := ‖traceOutput Z‖

theorem globalDualObjective_continuous :
    Continuous (globalDualObjective (I := I) (O := O)) :=
  continuous_norm.comp traceOutput_continuous

theorem globalDualFeasible_closed (K : E → Matrix O I ℂ)
    (B : F → Matrix O I ℂ) (t : ℝ) : IsClosed (globalDualFeasible K B t) := by
  have hAffine : Continuous (fun Z : Matrix (I × O) (I × O) ℂ =>
      t • (krausColumns B * (krausColumns B)ᴴ) + Z -
        krausColumns K * (krausColumns K)ᴴ) :=
    (continuous_const.add continuous_id).sub continuous_const
  simp only [globalDualFeasible, ← Matrix.nonneg_iff_posSemidef]
  exact (isClosed_le continuous_const continuous_id).inter
    (isClosed_le continuous_const hAffine)

theorem globalDualFeasible_nonempty (K : E → Matrix O I ℂ)
    (B : F → Matrix O I ℂ) {t : ℝ} (ht : 0 ≤ t) :
    (globalDualFeasible K B t).Nonempty := by
  refine ⟨krausColumns K * (krausColumns K)ᴴ, ?_, ?_⟩
  · exact Matrix.posSemidef_self_mul_conjTranspose _
  · simpa only [add_sub_cancel_right] using
      (Matrix.posSemidef_self_mul_conjTranspose (krausColumns B)).smul ht

theorem globalDualSublevel_compact (K : E → Matrix O I ℂ)
    (B : F → Matrix O I ℂ) (t c : ℝ) :
    IsCompact {Z | Z ∈ globalDualFeasible K B t ∧ globalDualObjective Z ≤ c} := by
  have hclosed : IsClosed {Z | Z ∈ globalDualFeasible K B t ∧
      globalDualObjective Z ≤ c} :=
    (globalDualFeasible_closed K B t).inter
      (isClosed_le globalDualObjective_continuous continuous_const)
  refine (isCompact_closedBall (0 : Matrix (I × O) (I × O) ℂ)
    ((Fintype.card I : ℝ) * c)).of_isClosed_subset hclosed ?_
  intro Z hZ
  rw [Metric.mem_closedBall, dist_zero_right]
  exact (global_dual_objective_coercive hZ.1.1).trans
    (mul_le_mul_of_nonneg_left hZ.2 (Nat.cast_nonneg _))

theorem exists_global_dual_minimizer (K : E → Matrix O I ℂ)
    (B : F → Matrix O I ℂ) {t : ℝ} (ht : 0 ≤ t) :
    ∃ Z ∈ globalDualFeasible K B t,
      ∀ W ∈ globalDualFeasible K B t, globalDualObjective Z ≤ globalDualObjective W := by
  obtain ⟨Z₀, hZ₀⟩ := globalDualFeasible_nonempty K B ht
  let S := {Z | Z ∈ globalDualFeasible K B t ∧
    globalDualObjective Z ≤ globalDualObjective Z₀}
  have hS : IsCompact S := globalDualSublevel_compact K B t (globalDualObjective Z₀)
  obtain ⟨Z, hZ, hmin⟩ := hS.exists_isMinOn ⟨Z₀, hZ₀, le_refl _⟩
    globalDualObjective_continuous.continuousOn
  refine ⟨Z, hZ.1, ?_⟩
  intro W hW
  by_cases hWc : globalDualObjective W ≤ globalDualObjective Z₀
  · exact hmin ⟨hW, hWc⟩
  · exact hZ.2.trans (le_of_not_ge hWc)

end QuantumProver.SuperchannelDiscrimination.ChannelUniformApproximation

namespace QuantumProver.SuperchannelDiscrimination.ChannelUniformApproximation

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Matrix

variable {I O E F : Type*} [Fintype I] [Fintype O] [Fintype E] [Fintype F]
  [DecidableEq I] [DecidableEq O] [DecidableEq E] [DecidableEq F]

def tensorPairEquiv (A B : Type*) (k : ℕ) :
    ((Fin k → A) × (Fin k → B)) ≃ (Fin k → A × B) where
  toFun x a := (x.1 a, x.2 a)
  invFun x := (fun a => (x a).1, fun a => (x a).2)
  left_inv x := by cases x; rfl
  right_inv x := by funext a; exact Prod.eta (x a)

def tensorKraus (K : E → Matrix O I ℂ) (k : ℕ) :
    (Fin k → E) → Matrix (Fin k → O) (Fin k → I) ℂ :=
  fun f => TensorWordTruncation.tensorMatrix (fun a => K (f a))

theorem tensorKraus_apply (K : E → Matrix O I ℂ) (k : ℕ)
    (f : Fin k → E) (o : Fin k → O) (i : Fin k → I) :
    tensorKraus K k f o i = ∏ a, K (f a) (o a) (i a) := rfl

theorem stackKraus_tensorKraus (K : E → Matrix O I ℂ) (k : ℕ) :
    stackKraus (tensorKraus K k) =
      (TensorWordTruncation.tensorMatrix (fun _ : Fin k => stackKraus K)).submatrix
        (tensorPairEquiv O E k) (Equiv.refl (Fin k → I)) := by
  ext ⟨o, f⟩ i
  rfl

theorem stackKraus_tensorKraus_norm (K : E → Matrix O I ℂ) (k : ℕ) :
    ‖stackKraus (tensorKraus K k)‖ =
      ‖TensorWordTruncation.tensorMatrix (fun _ : Fin k => stackKraus K)‖ := by
  rw [stackKraus_tensorKraus]
  exact TensorWordTruncation.norm_submatrix_equiv _ _ _

theorem stackKraus_tensorKraus_norm_le_one (K : E → Matrix O I ℂ)
    (hK : ‖stackKraus K‖ ≤ 1) (k : ℕ) : ‖stackKraus (tensorKraus K k)‖ ≤ 1 := by
  rw [stackKraus_tensorKraus_norm]
  exact TensorWordTruncation.tensorMatrix_const_norm_le_one _ hK k

theorem krausColumns_tensorKraus (K : E → Matrix O I ℂ) (k : ℕ) :
    krausColumns (tensorKraus K k) =
      (TensorWordTruncation.tensorMatrix (fun _ : Fin k => krausColumns K)).submatrix
        (tensorPairEquiv I O k) (Equiv.refl (Fin k → E)) := by
  ext ⟨i, o⟩ f
  rfl

theorem choi_tensorKraus (K : E → Matrix O I ℂ) (k : ℕ) :
    CPTPKraus.choi (QuantumProver.ElegantJointMeasurement.CP.krausMap (tensorKraus K k)) =
      (TensorWordTruncation.tensorMatrix
        (fun _ : Fin k => CPTPKraus.choi (QuantumProver.ElegantJointMeasurement.CP.krausMap K))).submatrix
        (tensorPairEquiv I O k) (tensorPairEquiv I O k) := by
  rw [choi_krausMap, krausColumns_tensorKraus, Matrix.conjTranspose_submatrix,
    Matrix.submatrix_mul_equiv]
  rw [← TensorWordTruncation.tensorMatrix_conjTranspose,
    ← TensorWordTruncation.tensorMatrix_mul]
  simp only [choi_krausMap]

theorem tensorKraus_gram (K : E → Matrix O I ℂ) (k : ℕ) :
    (∑ f : Fin k → E, (tensorKraus K k f)ᴴ * tensorKraus K k f) =
      TensorWordTruncation.tensorMatrix
        (fun _ : Fin k => ∑ e : E, (K e)ᴴ * K e) := by
  rw [← stackKraus_gram (tensorKraus K k), stackKraus_tensorKraus]
  rw [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv]
  change (TensorWordTruncation.tensorMatrix (fun _ : Fin k => stackKraus K))ᴴ *
      TensorWordTruncation.tensorMatrix (fun _ : Fin k => stackKraus K) = _
  rw [← TensorWordTruncation.tensorMatrix_conjTranspose,
    ← TensorWordTruncation.tensorMatrix_mul]
  simp only [stackKraus_gram]

theorem tensorKraus_complete (K : E → Matrix O I ℂ)
    (hK : (∑ e : E, (K e)ᴴ * K e) = 1) (k : ℕ) :
    (∑ f : Fin k → E, (tensorKraus K k f)ᴴ * tensorKraus K k f) = 1 := by
  rw [tensorKraus_gram, hK]
  ext i j
  by_cases hij : i = j
  · subst j
    simp [TensorWordTruncation.tensorMatrix, Matrix.one_apply]
  · obtain ⟨a, ha⟩ := Function.ne_iff.mp hij
    have hp : (∏ a : Fin k, (1 : Matrix I I ℂ) (i a) (j a)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ a) (by simp [Matrix.one_apply, ha])
    simpa only [TensorWordTruncation.tensorMatrix, Matrix.one_apply, if_neg hij] using hp

theorem tensorKraus_completelyPositive (K : E → Matrix O I ℂ) (k : ℕ) :
    CPTPKraus.CompletelyPositive (QuantumProver.ElegantJointMeasurement.CP.krausMap (tensorKraus K k)) :=
  (CPTPKraus.completelyPositive_iff_EJMCP _).mpr (QuantumProver.ElegantJointMeasurement.CP.krausMap_completelyPositive _)

theorem tensorKraus_tracePreserving (K : E → Matrix O I ℂ)
    (hK : (∑ e : E, (K e)ᴴ * K e) = 1) (k : ℕ) :
    CPTPKraus.TracePreserving (QuantumProver.ElegantJointMeasurement.CP.krausMap (tensorKraus K k)) :=
  (QuantumProver.ElegantJointMeasurement.CP.krausMap_trace_preserving_iff _).mpr (tensorKraus_complete K hK k)

theorem tensorKraus_mixEnvironment (C : Matrix E F ℂ) (B : F → Matrix O I ℂ) (k : ℕ) :
    tensorKraus (mixEnvironment C B) k =
      mixEnvironment (TensorWordTruncation.tensorMatrix (fun _ : Fin k => C))
        (tensorKraus B k) := by
  classical
  ext f o i
  simp only [tensorKraus, TensorWordTruncation.tensorMatrix, mixEnvironment,
    Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro z _
  exact Finset.prod_mul_distrib

theorem tensor_environment_cpDom (B : F → Matrix O I ℂ) (k : ℕ)
    (D : Matrix (Fin k → E) (Fin k → F) ℂ) (c : ℝ)
    (hD : ((c : ℂ) • (1 : Matrix (Fin k → F) (Fin k → F) ℂ) - Dᴴ * D).PosSemidef) :
    CPTPKraus.CPDom (QuantumProver.ElegantJointMeasurement.CP.krausMap (mixEnvironment D (tensorKraus B k)))
      (QuantumProver.ElegantJointMeasurement.CP.krausMap (tensorKraus B k)) c :=
  mixEnvironment_cpDom D (tensorKraus B k) c hD

theorem retained_tensor_environment_cpDom (B : F → Matrix O I ℂ)
    (C H : Matrix E F ℂ) (k ell : ℕ) {delta bound : ℝ}
    (hd : 0 ≤ delta) (hb : 0 ≤ bound)
    (hR : ‖TensorWordTruncation.retained C H k ell‖ ≤ bound) :
    CPTPKraus.CPDom
      (QuantumProver.ElegantJointMeasurement.CP.krausMap (mixEnvironment
        (TensorWordTruncation.attenuatedRetained C H k ell delta) (tensorKraus B k)))
      (QuantumProver.ElegantJointMeasurement.CP.krausMap (tensorKraus B k)) ((bound / (1 + delta)) ^ 2) := by
  have hbn : 0 ≤ bound / (1 + delta) := div_nonneg hb (by linarith)
  have hn := TensorWordTruncation.attenuatedRetained_norm_le_bound C H k ell hd hR
  have hg := TensorWordTruncation.right_gram_le_of_norm_le
    (TensorWordTruncation.attenuatedRetained C H k ell delta) hbn hn
  apply tensor_environment_cpDom B k _ _
  simpa only [matrix_real_smul] using hg

end QuantumProver.SuperchannelDiscrimination.ChannelUniformApproximation

namespace QuantumProver.SuperchannelDiscrimination.ChannelUniformApproximation

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Matrix

variable {I O E F : Type*} [Fintype I] [Fintype O] [Fintype E] [Fintype F]
  [DecidableEq I] [DecidableEq O] [DecidableEq E] [DecidableEq F]

theorem stackKraus_mixEnvironment_action (C : Matrix E F ℂ)
    (B : F → Matrix O I ℂ) :
    stackKraus (mixEnvironment C B) = TensorWordTruncation.action (stackKraus B) C := by
  ext ⟨o, e⟩ i
  simp only [stackKraus, mixEnvironment, Matrix.sum_apply, Matrix.smul_apply,
    smul_eq_mul, TensorWordTruncation.action]

theorem stackKraus_tensor_environment_action (B : F → Matrix O I ℂ) (k : ℕ)
    (D : Matrix (Fin k → E) (Fin k → F) ℂ) :
    stackKraus (mixEnvironment D (tensorKraus B k)) =
      (TensorWordTruncation.tensorAction (stackKraus B) D).submatrix
        (tensorPairEquiv O E k) (Equiv.refl (Fin k → I)) := by
  ext ⟨o, e⟩ i
  simp only [stackKraus, mixEnvironment, Matrix.sum_apply, Matrix.smul_apply,
    smul_eq_mul, tensorKraus, TensorWordTruncation.tensorMatrix,
    TensorWordTruncation.tensorAction, Matrix.submatrix_apply, tensorPairEquiv,
    Equiv.coe_fn_mk, Equiv.refl_apply]

theorem stackKraus_tensor_environment_action_norm (B : F → Matrix O I ℂ) (k : ℕ)
    (D : Matrix (Fin k → E) (Fin k → F) ℂ) :
    ‖stackKraus (mixEnvironment D (tensorKraus B k))‖ =
      ‖TensorWordTruncation.tensorAction (stackKraus B) D‖ := by
  rw [stackKraus_tensor_environment_action]
  exact TensorWordTruncation.norm_submatrix_equiv _ _ _

theorem stackKraus_tensor_environment_action_difference_norm
    (B : F → Matrix O I ℂ) (k : ℕ)
    (D G : Matrix (Fin k → E) (Fin k → F) ℂ) :
    ‖stackKraus (mixEnvironment D (tensorKraus B k)) -
        stackKraus (mixEnvironment G (tensorKraus B k))‖ =
      ‖TensorWordTruncation.tensorAction (stackKraus B) D -
        TensorWordTruncation.tensorAction (stackKraus B) G‖ := by
  have heq : stackKraus (mixEnvironment D (tensorKraus B k)) -
      stackKraus (mixEnvironment G (tensorKraus B k)) =
      (TensorWordTruncation.tensorAction (stackKraus B) D -
        TensorWordTruncation.tensorAction (stackKraus B) G).submatrix
          (tensorPairEquiv O E k) (Equiv.refl (Fin k → I)) := by
    rw [stackKraus_tensor_environment_action, stackKraus_tensor_environment_action]
    rfl
  rw [heq]
  exact TensorWordTruncation.norm_submatrix_equiv _ _ _

theorem tensor_environment_total_eq (K : E → Matrix O I ℂ)
    (B : F → Matrix O I ℂ) (C H : Matrix E F ℂ)
    (hK : mixEnvironment (C + H) B = K) (k : ℕ) :
    mixEnvironment (TensorWordTruncation.tensorMatrix (fun _ : Fin k => C + H))
      (tensorKraus B k) = tensorKraus K k := by
  rw [← tensorKraus_mixEnvironment, hK]

theorem retained_tensor_physical_control (K : E → Matrix O I ℂ)
    (B : F → Matrix O I ℂ) (C H : Matrix E F ℂ)
    (hK : (∑ e : E, (K e)ᴴ * K e) = 1)
    (hSplit : mixEnvironment (C + H) B = K)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (hepsilon_one : epsilon ≤ 1)
    (hbad : ‖stackKraus (mixEnvironment H B)‖ ≤ epsilon)
    (beta : ℝ) (k : ℕ) :
    let D := TensorWordTruncation.attenuatedRetained C H k ⌊beta * k⌋₊
      ((TensorWordTruncation.epsilonTailBase epsilon beta) ^ k)
    CPTPKraus.CompletelyPositive (QuantumProver.ElegantJointMeasurement.CP.krausMap (mixEnvironment D (tensorKraus B k))) ∧
      CPTPKraus.TraceNonincreasing (QuantumProver.ElegantJointMeasurement.CP.krausMap (mixEnvironment D (tensorKraus B k))) ∧
      ‖stackKraus (mixEnvironment D (tensorKraus B k))‖ ≤ 1 ∧
      ‖stackKraus (mixEnvironment D (tensorKraus B k)) - stackKraus (tensorKraus K k)‖ ≤
        2 * (TensorWordTruncation.epsilonTailBase epsilon beta) ^ k := by
  dsimp only
  have htotal : ‖TensorWordTruncation.action (stackKraus B) (C + H)‖ ≤ 1 := by
    rw [← stackKraus_mixEnvironment_action, hSplit]
    exact stackKraus_norm_le_one_of_complete K hK
  have hb : ‖TensorWordTruncation.action (stackKraus B) H‖ ≤ epsilon := by
    simpa only [← stackKraus_mixEnvironment_action] using hbad
  obtain ⟨_, hn, hd⟩ := TensorWordTruncation.same_action_tail_and_contraction
    (stackKraus B) C H hepsilon hepsilon_one htotal hb beta k
  have hn' : ‖stackKraus (mixEnvironment
      (TensorWordTruncation.attenuatedRetained C H k ⌊beta * k⌋₊
        ((TensorWordTruncation.epsilonTailBase epsilon beta) ^ k))
      (tensorKraus B k))‖ ≤ 1 := by
    rw [stackKraus_tensor_environment_action_norm]
    exact hn
  refine ⟨mixEnvironment_completelyPositive _ _,
    krausMap_traceNonincreasing_of_stack_norm_le_one _ hn', hn', ?_⟩
  rw [← tensor_environment_total_eq K B C H hSplit k,
    stackKraus_tensor_environment_action_difference_norm]
  exact hd

theorem retained_tensor_reference_probability_error (K : E → Matrix O I ℂ)
    (B : F → Matrix O I ℂ) (C H : Matrix E F ℂ)
    (hK : (∑ e : E, (K e)ᴴ * K e) = 1)
    (hSplit : mixEnvironment (C + H) B = K)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (hepsilon_one : epsilon ≤ 1)
    (hbad : ‖stackKraus (mixEnvironment H B)‖ ≤ epsilon)
    (beta : ℝ) (k : ℕ) (R : Type*) [Fintype R] [DecidableEq R]
    {X : Matrix ((Fin k → I) × R) ((Fin k → I) × R) ℂ}
    (hX : FlaggedStates.IsDensity X)
    {Q : Matrix ((Fin k → O) × R) ((Fin k → O) × R) ℂ}
    (hQ : FlaggedStates.IsEffect Q) :
    let D := TensorWordTruncation.attenuatedRetained C H k ⌊beta * k⌋₊
      ((TensorWordTruncation.epsilonTailBase epsilon beta) ^ k)
    |FlaggedStates.acceptanceProbability
        (CPTPKraus.amplify (QuantumProver.ElegantJointMeasurement.CP.krausMap (mixEnvironment D (tensorKraus B k))) R X) Q -
      FlaggedStates.acceptanceProbability
        (CPTPKraus.amplify (QuantumProver.ElegantJointMeasurement.CP.krausMap (tensorKraus K k)) R X) Q| ≤
          4 * (TensorWordTruncation.epsilonTailBase epsilon beta) ^ k := by
  dsimp only
  have h := retained_tensor_physical_control K B C H hK hSplit
    hepsilon hepsilon_one hbad beta k
  have hq : 0 ≤ (TensorWordTruncation.epsilonTailBase epsilon beta) ^ k :=
    pow_nonneg (TensorWordTruncation.epsilonTailBase_nonneg hepsilon.le beta) k
  have hb := reference_kraus_born_probability_error
    (mixEnvironment (TensorWordTruncation.attenuatedRetained C H k ⌊beta * k⌋₊
      ((TensorWordTruncation.epsilonTailBase epsilon beta) ^ k)) (tensorKraus B k))
    (tensorKraus K k) R (mul_nonneg (by norm_num) hq) h.2.2.1
    (stackKraus_tensorKraus_norm_le_one K (stackKraus_norm_le_one_of_complete K hK) k)
    h.2.2.2 hX hQ
  simpa only [← mul_assoc, show (2 : ℝ) * 2 = 4 by norm_num] using hb

end QuantumProver.SuperchannelDiscrimination.ChannelUniformApproximation

namespace QuantumProver.SuperchannelDiscrimination.ChannelUniformApproximation

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Matrix

variable {I O E F : Type*} [Fintype I] [Fintype O] [Fintype E] [Fintype F]
  [DecidableEq I] [DecidableEq O] [DecidableEq E] [DecidableEq F]

theorem exists_global_physical_environment_split
    (K : E → Matrix O I ℂ) (B : F → Matrix O I ℂ)
    {Z : Matrix (I × O) (I × O) ℂ} (hZ : Z.PosSemidef)
    {u w epsilon : ℝ} (hu : 0 ≤ u) (huw : u ≤ w) (hepsilon : 0 ≤ epsilon)
    (hwhole : (w ^ 2 • CPTPKraus.choi (QuantumProver.ElegantJointMeasurement.CP.krausMap B) -
      CPTPKraus.choi (QuantumProver.ElegantJointMeasurement.CP.krausMap K)).PosSemidef)
    (hdual : (u ^ 2 • CPTPKraus.choi (QuantumProver.ElegantJointMeasurement.CP.krausMap B) + Z -
      CPTPKraus.choi (QuantumProver.ElegantJointMeasurement.CP.krausMap K)).PosSemidef)
    (hsmall : ‖traceOutput Z‖ ≤ epsilon ^ 2) :
    ∃ C H : Matrix E F ℂ,
      mixEnvironment (C + H) B = K ∧
      (u ^ 2 • (1 : Matrix F F ℂ) - Cᴴ * C).PosSemidef ∧
      ‖C‖ ≤ u ∧ ‖H‖ ≤ 2 * w ∧
      (Z - krausColumns (mixEnvironment H B) *
        (krausColumns (mixEnvironment H B))ᴴ).PosSemidef ∧
      ‖stackKraus (mixEnvironment H B)‖ ≤ epsilon := by
  rw [choi_krausMap, choi_krausMap] at hwhole hdual
  obtain ⟨C, H, _, hrec, hcap, hC, hH, _, hres⟩ :=
    TensorWordTruncation.exists_constructed_environmental_good_bad
      (krausColumns B) (krausColumns K) hZ hu huw hwhole hdual
  have hmix : mixEnvironment (C + H) B = K := by
    funext e
    ext o i
    exact congrArg (fun M : Matrix (I × O) E ℂ => M (i, o) e)
      ((mixEnvironment_columns (C + H) B).trans hrec)
  have hres' : (Z - krausColumns (mixEnvironment H B) *
      (krausColumns (mixEnvironment H B))ᴴ).PosSemidef := by
    simpa only [mixEnvironment_columns] using hres
  have hsq := residual_stinespring_norm_sq_bound (mixEnvironment H B) Z hres'
  rw [global_dual_marginal_norm_transpose hZ] at hsq
  have hbad : ‖stackKraus (mixEnvironment H B)‖ ≤ epsilon := by
    nlinarith [norm_nonneg (stackKraus (mixEnvironment H B))]
  exact ⟨C, H, hmix, hcap, hC, hH, hres', hbad⟩

theorem dyadic_half_sq (x : ℝ) : ((2 : ℝ) ^ (x / 2)) ^ 2 = (2 : ℝ) ^ x := by
  calc
    _ = (2 : ℝ) ^ (x / 2) * (2 : ℝ) ^ (x / 2) := by ring
    _ = (2 : ℝ) ^ (x / 2 + x / 2) :=
      (Real.rpow_add (by norm_num) _ _).symm
    _ = _ := by congr 1; ring

theorem exists_dyadic_global_physical_split
    (K : E → Matrix O I ℂ) (B : F → Matrix O I ℂ) (m : ℕ)
    {r S epsilon : ℝ} (hrS : r ≤ S) (hepsilon : 0 ≤ epsilon)
    {Z : Matrix (I × O) (I × O) ℂ} (hZ : Z.PosSemidef)
    (hwhole : ((2 : ℝ) ^ ((m : ℝ) * S) •
      CPTPKraus.choi (QuantumProver.ElegantJointMeasurement.CP.krausMap B) - CPTPKraus.choi (QuantumProver.ElegantJointMeasurement.CP.krausMap K)).PosSemidef)
    (hdual : ((2 : ℝ) ^ ((m : ℝ) * r) •
      CPTPKraus.choi (QuantumProver.ElegantJointMeasurement.CP.krausMap B) + Z -
        CPTPKraus.choi (QuantumProver.ElegantJointMeasurement.CP.krausMap K)).PosSemidef)
    (hsmall : ‖traceOutput Z‖ ≤ epsilon ^ 2) :
    ∃ C H : Matrix E F ℂ,
      mixEnvironment (C + H) B = K ∧
      ‖C‖ ≤ (2 : ℝ) ^ ((m : ℝ) * r / 2) ∧
      ‖H‖ ≤ 2 * (2 : ℝ) ^ ((m : ℝ) * S / 2) ∧
      ‖stackKraus (mixEnvironment H B)‖ ≤ epsilon := by
  have hu : 0 ≤ (2 : ℝ) ^ ((m : ℝ) * r / 2) := Real.rpow_nonneg (by norm_num) _
  have huw : (2 : ℝ) ^ ((m : ℝ) * r / 2) ≤ (2 : ℝ) ^ ((m : ℝ) * S / 2) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hrS (Nat.cast_nonneg m)) (by norm_num)
  have hwhole' : (((2 : ℝ) ^ ((m : ℝ) * S / 2)) ^ 2 •
      CPTPKraus.choi (QuantumProver.ElegantJointMeasurement.CP.krausMap B) - CPTPKraus.choi (QuantumProver.ElegantJointMeasurement.CP.krausMap K)).PosSemidef := by
    simpa only [dyadic_half_sq] using hwhole
  have hdual' : (((2 : ℝ) ^ ((m : ℝ) * r / 2)) ^ 2 •
      CPTPKraus.choi (QuantumProver.ElegantJointMeasurement.CP.krausMap B) + Z -
        CPTPKraus.choi (QuantumProver.ElegantJointMeasurement.CP.krausMap K)).PosSemidef := by
    simpa only [dyadic_half_sq] using hdual
  obtain ⟨C, H, hmix, _, hC, hH, _, hbad⟩ :=
    exists_global_physical_environment_split K B hZ hu huw hepsilon hwhole' hdual' hsmall
  exact ⟨C, H, hmix, hC, hH, hbad⟩

theorem exists_global_physical_tensor_rate_parameters {r S R : ℝ}
    (hrS : r ≤ S) (hrR : r < R) :
    ∃ (beta epsilon0 : ℝ) (m0 : ℕ),
      0 < beta ∧ 0 < epsilon0 ∧ epsilon0 ≤ 1 ∧ 0 < m0 ∧
      ∀ (m : ℕ), m0 ≤ m → ∀ (epsilon : ℝ), 0 < epsilon → epsilon ≤ epsilon0 →
      ∀ (K : E → Matrix O I ℂ) (B : F → Matrix O I ℂ),
        (∑ e : E, (K e)ᴴ * K e) = 1 →
      ∀ (Z : Matrix (I × O) (I × O) ℂ), Z.PosSemidef →
        ((2 : ℝ) ^ ((m : ℝ) * S) • CPTPKraus.choi (QuantumProver.ElegantJointMeasurement.CP.krausMap B) -
          CPTPKraus.choi (QuantumProver.ElegantJointMeasurement.CP.krausMap K)).PosSemidef →
        ((2 : ℝ) ^ ((m : ℝ) * r) • CPTPKraus.choi (QuantumProver.ElegantJointMeasurement.CP.krausMap B) + Z -
          CPTPKraus.choi (QuantumProver.ElegantJointMeasurement.CP.krausMap K)).PosSemidef →
        ‖traceOutput Z‖ ≤ epsilon ^ 2 →
      ∃ C H : Matrix E F ℂ,
        mixEnvironment (C + H) B = K ∧ ‖stackKraus (mixEnvironment H B)‖ ≤ epsilon ∧
        TensorWordTruncation.epsilonTailBase epsilon beta < 1 ∧
        ∀ k : ℕ,
          let D := TensorWordTruncation.attenuatedRetained C H k ⌊beta * k⌋₊
            ((TensorWordTruncation.epsilonTailBase epsilon beta) ^ k)
          CPTPKraus.CompletelyPositive (QuantumProver.ElegantJointMeasurement.CP.krausMap (mixEnvironment D (tensorKraus B k))) ∧
          CPTPKraus.TraceNonincreasing (QuantumProver.ElegantJointMeasurement.CP.krausMap (mixEnvironment D (tensorKraus B k))) ∧
          CPTPKraus.CPDom (QuantumProver.ElegantJointMeasurement.CP.krausMap (mixEnvironment D (tensorKraus B k)))
            (QuantumProver.ElegantJointMeasurement.CP.krausMap (tensorKraus B k)) ((2 : ℝ) ^ ((m : ℝ) * k * R)) ∧
          ‖stackKraus (mixEnvironment D (tensorKraus B k))‖ ≤ 1 ∧
          ‖stackKraus (mixEnvironment D (tensorKraus B k)) -
            stackKraus (tensorKraus K k)‖ ≤
              2 * (TensorWordTruncation.epsilonTailBase epsilon beta) ^ k ∧
          ‖D‖ ≤ (2 : ℝ) ^ ((m : ℝ) * k * R / 2) := by
  obtain ⟨beta, epsilon0, m0, hbeta, he0, he01, hm0, hfamily⟩ :=
    TensorWordTruncation.exists_physical_environment_rate_parameters
      (I := I) (O := O) (E := E) (F := F) hrS hrR
  refine ⟨beta, epsilon0, m0, hbeta, he0, he01, hm0, ?_⟩
  intro m hm epsilon hepsilon hesmall K B hK Z hZ hwhole hdual hsmall
  obtain ⟨C, H, hmix, hC, hH, hbad⟩ :=
    exists_dyadic_global_physical_split K B m hrS hepsilon.le hZ hwhole hdual hsmall
  obtain ⟨hq, hrate⟩ := hfamily m hm epsilon hepsilon hesmall
  have htotal : ‖TensorWordTruncation.action (stackKraus B) (C + H)‖ ≤ 1 := by
    rw [← stackKraus_mixEnvironment_action, hmix]
    exact stackKraus_norm_le_one_of_complete K hK
  have hb : ‖TensorWordTruncation.action (stackKraus B) H‖ ≤ epsilon := by
    simpa only [← stackKraus_mixEnvironment_action] using hbad
  refine ⟨C, H, hmix, hbad, hq, ?_⟩
  intro k
  dsimp only
  have hc := hrate (stackKraus B) C H hC hH htotal hb k
  have hp := retained_tensor_physical_control K B C H hK hmix
    hepsilon (hesmall.trans he01) hbad beta k
  have hcp := tensor_environment_cpDom B k
    (TensorWordTruncation.attenuatedRetained C H k ⌊beta * k⌋₊
      ((TensorWordTruncation.epsilonTailBase epsilon beta) ^ k))
    ((2 : ℝ) ^ ((m : ℝ) * k * R))
    (by simpa only [matrix_real_smul] using hc.2.2.2)
  exact ⟨hp.1, hp.2.1, hcp, hp.2.2.1, hp.2.2.2, hc.2.2.1⟩

end QuantumProver.SuperchannelDiscrimination.ChannelUniformApproximation

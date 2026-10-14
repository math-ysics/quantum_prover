import QuantumProver.InformationTheory.SuperchannelDiscrimination.Definitions
import QuantumProver.InformationTheory.SuperchannelDiscrimination.EntropyInequalities
import QuantumProver.InformationTheory.SuperchannelDiscrimination.BinaryTesting
import QuantumProver.InformationTheory.SuperchannelDiscrimination.FlaggedStates
import QuantumProver.InformationTheory.SuperchannelDiscrimination.CPTPKraus

set_option autoImplicit false

noncomputable section

open Filter Set
open scoped Topology

namespace QuantumProver.SuperchannelDiscrimination

def UniformBinaryConverse (S : StrategyFamily) (B : ℝ) : Prop :=
  ∀ n, 0 < n → ∀ T, T ∈ S n →
    extendedBinaryRelativeEntropyBits (1 - T.alpha) T.beta ≤ (((n : ℝ) * B : ℝ) : EReal)

theorem uniformBinaryConverse_of_perUseWitnesses {S : StrategyFamily} {B : ℝ}
    (h : ∀ n, 0 < n → ∀ T, T ∈ S n → ∃ v : ℕ → ℝ,
      v 0 ≤ 0 ∧ (∀ k, k < n → v (k + 1) ≤ v k + B) ∧
        extendedBinaryRelativeEntropyBits (1 - T.alpha) T.beta ≤ (v n : EReal)) :
    UniformBinaryConverse S B := by
  intro n hn T hT
  rcases h n hn T hT with ⟨v, h0, hs, hD⟩
  exact hD.trans (EReal.coe_le_coe_iff.mpr (divergence_telescopes_upto h0 hs))

def converseProbability (B epsilon : ℝ) (n : ℕ) : ℝ :=
  Real.exp (-(((n : ℝ) * B + 1) / (1 - epsilon)) * Real.log 2)

theorem converseProbability_eq_rpow (B epsilon : ℝ) (n : ℕ) :
    converseProbability B epsilon n =
      (2 : ℝ) ^ (-((n : ℝ) * B + 1) / (1 - epsilon)) := by
  rw [converseProbability, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  congr 1
  ring

theorem converseProbability_le_of_uniformBinaryConverse {S : StrategyFamily} {B epsilon : ℝ}
    (hB : 0 ≤ B) (hS : UniformBinaryConverse S B) (hepsilon : epsilon < 1)
    {n : ℕ} (hn : 0 < n) {T : BinaryTest} (hT : Feasible S epsilon n T) :
    converseProbability B epsilon n ≤ T.beta := by
  rw [converseProbability_eq_rpow]
  exact typeII_lower_bound_of_extended_divergence
    (p := 1 - T.alpha) (q := T.beta) (n := n)
    (by linarith [T.alpha_nonneg]) (by linarith [hT.2])
    T.beta_nonneg T.beta_le_one hepsilon hB (hS n hn T hT.1)

theorem converseProbability_le_optimalBeta {S : StrategyFamily} {B epsilon : ℝ}
    (hB : 0 ≤ B) (hS : UniformBinaryConverse S B) (hepsilon : epsilon < 1)
    {n : ℕ} (hn : 0 < n) :
    ENNReal.ofReal (converseProbability B epsilon n) ≤ optimalBeta S epsilon n := by
  apply le_optimalBeta
  intro T hT
  exact ENNReal.ofReal_le_ofReal
    (converseProbability_le_of_uniformBinaryConverse hB hS hepsilon hn hT)

theorem positiveBlockRate_le_of_uniformBinaryConverse {S : StrategyFamily} {B epsilon : ℝ}
    (hB : 0 ≤ B) (hS : UniformBinaryConverse S B) (hepsilon : epsilon < 1) (k : ℕ) :
    positiveBlockRate S epsilon k ≤
      (((B + 1 / ((k + 1 : ℕ) : ℝ)) / (1 - epsilon) : ℝ) : EReal) := by
  have hn : 0 < k + 1 := Nat.succ_pos _
  have hnR : 0 < ((k + 1 : ℕ) : ℝ) := by exact_mod_cast hn
  have hbeta := converseProbability_le_optimalBeta hB hS hepsilon hn
  have hlog := negLogTwo_antitone hbeta
  rw [converseProbability, negLogTwo_exp] at hlog
  have hrate := mul_le_mul_of_nonneg_right hlog
    (EReal.coe_nonneg.mpr (by positivity : 0 ≤ (1 / ((k + 1 : ℕ) : ℝ) : ℝ)))
  unfold positiveBlockRate
  refine hrate.trans_eq ?_
  rw [← EReal.coe_mul]
  congr 1
  field_simp [ne_of_gt hnR, ne_of_gt (sub_pos.mpr hepsilon)]

theorem fixedErrorLowerRate_le_of_uniformBinaryConverse {S : StrategyFamily} {B epsilon : ℝ}
    (hB : 0 ≤ B) (hS : UniformBinaryConverse S B) (hepsilon : epsilon < 1) :
    fixedErrorLowerRate S epsilon ≤ ((B / (1 - epsilon) : ℝ) : EReal) := by
  have hlimR : Tendsto
      (fun k : ℕ => (B + 1 / ((k + 1 : ℕ) : ℝ)) / (1 - epsilon)) atTop
      (𝓝 (B / (1 - epsilon))) := by
    have hone : Tendsto (fun k : ℕ => 1 / ((k + 1 : ℕ) : ℝ)) atTop (𝓝 (0 : ℝ)) :=
      (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (tendsto_add_atTop_nat 1)
    convert (tendsto_const_nhds.add hone).div_const
      (1 - epsilon) using 1 <;> simp
  have hlim := EReal.tendsto_coe.mpr hlimR
  exact (Filter.liminf_le_liminf
    (.of_forall (positiveBlockRate_le_of_uniformBinaryConverse hB hS hepsilon))).trans_eq
      hlim.liminf_eq

theorem orderedSteinExponent_le_of_fixedErrorBounds {S : StrategyFamily} {B : ℝ}
    (h : ∀ epsilon ∈ Ioo (0 : ℝ) 1,
      fixedErrorLowerRate S epsilon ≤ ((B / (1 - epsilon) : ℝ) : EReal)) :
    orderedSteinExponent S ≤ (B : EReal) := by
  have hlimR : Tendsto (fun epsilon : ℝ => B / (1 - epsilon))
      (𝓝[>] (0 : ℝ)) (𝓝 B) := by
    have hcont : ContinuousAt (fun epsilon : ℝ => B / (1 - epsilon)) 0 :=
      continuousAt_const.div (continuousAt_const.sub continuousAt_id) (by norm_num)
    simpa using hcont.continuousWithinAt.tendsto
  have hlim := EReal.tendsto_coe.mpr hlimR
  apply ge_of_tendsto hlim
  filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with epsilon hepsilon
  exact (orderedSteinExponent_le_fixedErrorLowerRate S hepsilon).trans (h epsilon hepsilon)

theorem orderedSteinExponent_le_of_uniformBinaryConverse {S : StrategyFamily} {B : ℝ}
    (hB : 0 ≤ B) (hS : UniformBinaryConverse S B) :
    orderedSteinExponent S ≤ (B : EReal) := by
  apply orderedSteinExponent_le_of_fixedErrorBounds
  intro epsilon hepsilon
  exact fixedErrorLowerRate_le_of_uniformBinaryConverse hB hS hepsilon.2

theorem conditional_orderedSteinExponent_eq {P N : StrategyFamily} {B : ℝ}
    (hB : 0 ≤ B) (hPN : ∀ n, P n ⊆ N n)
    (hparallel : orderedSteinExponent P = (B : EReal))
    (hconverse : UniformBinaryConverse N B) :
    orderedSteinExponent N = orderedSteinExponent P := by
  apply le_antisymm
  · rw [hparallel]
    exact orderedSteinExponent_le_of_uniformBinaryConverse hB hconverse
  · exact orderedSteinExponent_mono_family hPN

theorem orderedSteinExponent_eq_of_parallel_top {P N : StrategyFamily}
    (hPN : ∀ n, P n ⊆ N n) (hparallel : orderedSteinExponent P = ⊤) :
    orderedSteinExponent N = orderedSteinExponent P := by
  apply le_antisymm
  · rw [hparallel]
    exact le_top
  · exact orderedSteinExponent_mono_family hPN

theorem conditional_orderedSteinExponent_eq_all {P N : StrategyFamily}
    (hP : HasAcceptAll P) (hPN : ∀ n, P n ⊆ N n)
    (hconverse : ∀ B : ℝ, orderedSteinExponent P = (B : EReal) →
      UniformBinaryConverse N B) :
    orderedSteinExponent N = orderedSteinExponent P := by
  cases hparallel : orderedSteinExponent P with
  | bot =>
      have hnonneg := orderedSteinExponent_nonneg hP
      rw [hparallel] at hnonneg
      exact (not_le_of_gt (by norm_num : (⊥ : EReal) < 0) hnonneg).elim
  | top =>
      simpa only [hparallel] using orderedSteinExponent_eq_of_parallel_top hPN hparallel
  | coe B =>
      have hB : 0 ≤ B := by
        apply EReal.coe_nonneg.mp
        simpa [hparallel] using orderedSteinExponent_nonneg hP
      simpa only [hparallel] using
        conditional_orderedSteinExponent_eq hB hPN hparallel (hconverse B hparallel)

end QuantumProver.SuperchannelDiscrimination

namespace QuantumProver.SuperchannelDiscrimination.KrausCompletion

open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker Matrix

variable {I O κ : Type*} [Fintype I] [Fintype O] [Fintype κ]
  [DecidableEq I] [DecidableEq O]

def krausAction (K : κ → Matrix O I ℂ) (A : Matrix I I ℂ) : Matrix O O ℂ :=
  ∑ k, K k * A * (K k)ᴴ

def krausGram (K : κ → Matrix O I ℂ) : Matrix I I ℂ :=
  ∑ k, (K k)ᴴ * K k

theorem krausGram_posSemidef (K : κ → Matrix O I ℂ) : (krausGram K).PosSemidef := by
  simpa [krausGram] using Matrix.posSemidef_sum Finset.univ
    (fun k _ => Matrix.posSemidef_conjTranspose_mul_self (K k))

theorem krausAction_posSemidef (K : κ → Matrix O I ℂ)
    {A : Matrix I I ℂ} (hA : A.PosSemidef) : (krausAction K A).PosSemidef := by
  simpa [krausAction] using Matrix.posSemidef_sum Finset.univ
    (fun k _ => hA.mul_mul_conjTranspose_same (K k))

theorem trace_krausAction (K : κ → Matrix O I ℂ) (A : Matrix I I ℂ) :
    (krausAction K A).trace = (krausGram K * A).trace := by
  simp only [krausAction, krausGram, Matrix.sum_mul, Matrix.trace_sum]
  exact Finset.sum_congr rfl fun k _ => Matrix.trace_mul_cycle (K k) A (K k)ᴴ

theorem trace_mul_nonneg_of_posSemidef {H A : Matrix I I ℂ}
    (hH : H.PosSemidef) (hA : A.PosSemidef) : 0 ≤ (H * A).trace := by
  have hsqrt : (CFC.sqrt H).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg H)
  have htrace : (CFC.sqrt H * A * (CFC.sqrt H)ᴴ).trace = (H * A).trace := by
    rw [Matrix.trace_mul_cycle, hsqrt.isHermitian.eq,
      CFC.sqrt_mul_sqrt_self H hH.nonneg]
  have h := (hA.mul_mul_conjTranspose_same (CFC.sqrt H)).trace_nonneg
  rwa [htrace] at h

theorem trace_mul_mono_of_posSemidef {H G A : Matrix I I ℂ}
    (hHG : (G - H).PosSemidef) (hA : A.PosSemidef) :
    (H * A).trace ≤ (G * A).trace := by
  have h := trace_mul_nonneg_of_posSemidef hHG hA
  rw [Matrix.sub_mul, Matrix.trace_sub] at h
  exact sub_nonneg.mp h

theorem residual_expectation_le {H A : Matrix I I ℂ} {δ : ℝ}
    (hHD : (δ • (1 : Matrix I I ℂ) - H).PosSemidef)
    (hA : A.PosSemidef) (htrace : A.trace = 1) :
    (H * A).trace ≤ (δ : ℂ) := by
  have h := trace_mul_mono_of_posSemidef hHD hA
  simpa [Matrix.smul_mul, Matrix.trace_smul, htrace] using h

theorem krausAction_success_trace_ge (K : κ → Matrix O I ℂ) {A : Matrix I I ℂ}
    {δ : ℝ} (hHD : (δ • (1 : Matrix I I ℂ) - (1 - krausGram K)).PosSemidef)
    (hA : A.PosSemidef) (htrace : A.trace = 1) :
    (1 : ℂ) - (δ : ℂ) ≤ (krausAction K A).trace := by
  have h := residual_expectation_le hHD hA htrace
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub, htrace,
    ← trace_krausAction] at h
  exact sub_le_comm.mp h

theorem krausAction_traceNonincreasing (K : κ → Matrix O I ℂ)
    (hK : (1 - krausGram K).PosSemidef) {A : Matrix I I ℂ} (hA : A.PosSemidef) :
    (krausAction K A).trace ≤ A.trace := by
  have h := trace_mul_nonneg_of_posSemidef hK hA
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub, ← trace_krausAction] at h
  exact sub_nonneg.mp h

theorem residual_posSemidef_of_traceNonincreasing (K : κ → Matrix O I ℂ)
    (hT : ∀ A : Matrix I I ℂ, A.PosSemidef → (krausAction K A).trace ≤ A.trace) :
    (1 - krausGram K).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    (Matrix.isHermitian_one.sub (krausGram_posSemidef K).isHermitian)
  intro x
  have h : 0 ≤ ((1 - krausGram K) * Matrix.vecMulVec x (star x)).trace := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub, ← trace_krausAction]
    exact sub_nonneg.mpr (hT _ (Matrix.posSemidef_vecMulVec_self_star x))
  rwa [Matrix.mul_vecMulVec, Matrix.trace_vecMulVec, dotProduct_comm] at h

theorem residual_posSemidef_iff_traceNonincreasing (K : κ → Matrix O I ℂ) :
    (1 - krausGram K).PosSemidef ↔
      ∀ A : Matrix I I ℂ, A.PosSemidef → (krausAction K A).trace ≤ A.trace := by
  exact ⟨fun hK A hA => krausAction_traceNonincreasing K hK hA,
    residual_posSemidef_of_traceNonincreasing K⟩

theorem krausAction_tracePreserving (K : κ → Matrix O I ℂ)
    (hK : krausGram K = 1) (A : Matrix I I ℂ) :
    (krausAction K A).trace = A.trace := by
  rw [trace_krausAction, hK, Matrix.one_mul]

theorem krausAction_add (K : κ → Matrix O I ℂ) (A B : Matrix I I ℂ) :
    krausAction K (A + B) = krausAction K A + krausAction K B := by
  simp [krausAction, Matrix.mul_add, Matrix.add_mul, Finset.sum_add_distrib]

theorem krausAction_smul (K : κ → Matrix O I ℂ) (c : ℂ) (A : Matrix I I ℂ) :
    krausAction K (c • A) = c • krausAction K A := by
  simp [krausAction, Matrix.mul_smul, Matrix.smul_mul, Finset.smul_sum]

def krausMap (K : κ → Matrix O I ℂ) : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ where
  toFun := krausAction K
  map_add' := krausAction_add K
  map_smul' := krausAction_smul K

def amplify (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ)
    (R : Type*) [Fintype R] (A : Matrix (I × R) (I × R) ℂ) :
    Matrix (O × R) (O × R) ℂ :=
  fun x y => Φ (fun i j => A (i, x.2) (j, y.2)) x.1 y.1

def stabilizedKraus (K : κ → Matrix O I ℂ) (R : Type*) [Fintype R] [DecidableEq R] :
    κ → Matrix (O × R) (I × R) ℂ :=
  fun k => K k ⊗ₖ (1 : Matrix R R ℂ)

theorem stabilizedKraus_posSemidef (K : κ → Matrix O I ℂ)
    (R : Type*) [Fintype R] [DecidableEq R]
    {A : Matrix (I × R) (I × R) ℂ} (hA : A.PosSemidef) :
    (krausAction (stabilizedKraus K R) A).PosSemidef :=
  krausAction_posSemidef _ hA

theorem stabilizedKraus_gram (K : κ → Matrix O I ℂ)
    (R : Type*) [Fintype R] [DecidableEq R] :
    krausGram (stabilizedKraus K R) = krausGram K ⊗ₖ (1 : Matrix R R ℂ) := by
  simp only [krausGram, stabilizedKraus, Matrix.conjTranspose_kronecker,
    Matrix.conjTranspose_one, ← Matrix.mul_kronecker_mul, Matrix.one_mul]
  ext i j
  simp [Matrix.sum_apply, Matrix.kronecker_apply, Finset.sum_mul]

theorem stabilizedKraus_tracePreserving (K : κ → Matrix O I ℂ)
    (hK : krausGram K = 1) (R : Type*) [Fintype R] [DecidableEq R]
    (A : Matrix (I × R) (I × R) ℂ) :
    (krausAction (stabilizedKraus K R) A).trace = A.trace := by
  apply krausAction_tracePreserving
  rw [stabilizedKraus_gram, hK, Matrix.one_kronecker_one]

theorem amplify_krausMap (K : κ → Matrix O I ℂ)
    (R : Type*) [Fintype R] [DecidableEq R]
    (A : Matrix (I × R) (I × R) ℂ) :
    amplify (krausMap K) R A = krausAction (stabilizedKraus K R) A := by
  ext x y
  simp [amplify, krausMap, krausAction, stabilizedKraus, Matrix.sum_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.kronecker_apply, Fintype.sum_prod_type,
    Matrix.one_apply, Finset.mul_sum, Finset.sum_mul]
  simp [apply_ite, mul_ite, ite_mul, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro j hj
  change (∑ i : I, K k x.1 i * A (i, x.2) (j, y.2)) * star (K k y.1 j) =
    ∑ i : I, K k x.1 i * A (i, x.2) (j, y.2) * star (K k y.1 j)
  rw [Finset.sum_mul]

theorem krausMap_completelyPositive (K : κ → Matrix O I ℂ)
    (R : Type*) [Fintype R] [DecidableEq R]
    {A : Matrix (I × R) (I × R) ℂ} (hA : A.PosSemidef) :
    (amplify (krausMap K) R A).PosSemidef := by
  rw [amplify_krausMap]
  exact stabilizedKraus_posSemidef K R hA

def resetKraus (o₀ : O) (C : Matrix I I ℂ) : I → Matrix O I ℂ :=
  fun i => Matrix.single o₀ i (1 : ℂ) * C

theorem resetKraus_gram (o₀ : O) (C : Matrix I I ℂ) :
    krausGram (resetKraus o₀ C) = Cᴴ * C := by
  calc
    krausGram (resetKraus o₀ C) =
        Cᴴ * (∑ i : I, (Matrix.single o₀ i (1 : ℂ))ᴴ *
          Matrix.single o₀ i (1 : ℂ)) * C := by
      simp only [krausGram, resetKraus, Matrix.conjTranspose_mul,
        Matrix.mul_assoc, Matrix.mul_sum, Matrix.sum_mul]
    _ = Cᴴ * C := by
      simp [Matrix.conjTranspose_single, Matrix.sum_single_one]

theorem resetKraus_action (o₀ : O) (C A : Matrix I I ℂ) :
    krausAction (resetKraus o₀ C) A =
      (C * A * Cᴴ).trace • Matrix.single o₀ o₀ (1 : ℂ) := by
  have heach (i : I) :
      resetKraus o₀ C i * A * (resetKraus o₀ C i)ᴴ =
        Matrix.single o₀ o₀ ((C * A * Cᴴ) i i) := by
    calc
      resetKraus o₀ C i * A * (resetKraus o₀ C i)ᴴ =
          Matrix.single o₀ i (1 : ℂ) * (C * A * Cᴴ) * Matrix.single i o₀ (1 : ℂ) := by
        simp only [resetKraus, Matrix.conjTranspose_mul, Matrix.conjTranspose_single,
          star_one, Matrix.mul_assoc]
      _ = Matrix.single o₀ o₀ ((C * A * Cᴴ) i i) := by simp
  simp only [krausAction, heach]
  ext a b
  by_cases ha : o₀ = a <;> by_cases hb : o₀ = b <;>
    simp [Matrix.sum_apply, Matrix.single_apply, Matrix.smul_apply,
      Matrix.trace, Matrix.diag, ha, hb]

def repairKraus (o₀ : O) (H : Matrix I I ℂ) : I → Matrix O I ℂ :=
  resetKraus o₀ (CFC.sqrt H)

theorem repairKraus_gram (o₀ : O) {H : Matrix I I ℂ} (hH : H.PosSemidef) :
    krausGram (repairKraus o₀ H) = H := by
  have hsqrt : (CFC.sqrt H).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg H)
  rw [repairKraus, resetKraus_gram, hsqrt.isHermitian.eq,
    CFC.sqrt_mul_sqrt_self H hH.nonneg]

theorem repairKraus_action (o₀ : O) {H : Matrix I I ℂ} (hH : H.PosSemidef)
    (A : Matrix I I ℂ) :
    krausAction (repairKraus o₀ H) A =
      (H * A).trace • Matrix.single o₀ o₀ (1 : ℂ) := by
  have hsqrt : (CFC.sqrt H).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg H)
  rw [repairKraus, resetKraus_action]
  congr 1
  rw [Matrix.trace_mul_cycle, hsqrt.isHermitian.eq,
    CFC.sqrt_mul_sqrt_self H hH.nonneg]

variable {ι : Type*} [Fintype ι]

def flaggedKraus (K : κ → Matrix O I ℂ) (J : ι → Matrix O I ℂ) :
    κ ⊕ ι → Matrix (O ⊕ O) I ℂ :=
  Sum.elim (fun k => Matrix.fromRows (K k) (0 : Matrix O I ℂ))
    (fun j => Matrix.fromRows (0 : Matrix O I ℂ) (J j))

theorem flaggedKraus_gram (K : κ → Matrix O I ℂ) (J : ι → Matrix O I ℂ) :
    krausGram (flaggedKraus K J) = krausGram K + krausGram J := by
  simp [krausGram, flaggedKraus, Fintype.sum_sum_type,
    Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose,
    Matrix.fromCols_mul_fromRows]

theorem flaggedKraus_action (K : κ → Matrix O I ℂ) (J : ι → Matrix O I ℂ)
    (A : Matrix I I ℂ) :
    krausAction (flaggedKraus K J) A =
      Matrix.fromBlocks (krausAction K A) 0 0 (krausAction J A) := by
  ext (a | a) (b | b) <;>
    simp [krausAction, flaggedKraus, Matrix.sum_apply, Fintype.sum_sum_type,
      Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose,
      Matrix.fromRows_mul_fromCols]

def completionKraus (K : κ → Matrix O I ℂ) (o₀ : O) :
    κ ⊕ I → Matrix (O ⊕ O) I ℂ :=
  flaggedKraus K (repairKraus o₀ (1 - krausGram K))

theorem completionKraus_gram (K : κ → Matrix O I ℂ) (o₀ : O)
    (hK : (1 - krausGram K).PosSemidef) :
    krausGram (completionKraus K o₀) = 1 := by
  rw [completionKraus, flaggedKraus_gram, repairKraus_gram o₀ hK]
  abel

theorem completionKraus_tracePreserving (K : κ → Matrix O I ℂ) (o₀ : O)
    (hK : (1 - krausGram K).PosSemidef) (A : Matrix I I ℂ) :
    (krausAction (completionKraus K o₀) A).trace = A.trace :=
  krausAction_tracePreserving _ (completionKraus_gram K o₀ hK) A

theorem completionKraus_action (K : κ → Matrix O I ℂ) (o₀ : O)
    (hK : (1 - krausGram K).PosSemidef) (A : Matrix I I ℂ) :
    krausAction (completionKraus K o₀) A =
      Matrix.fromBlocks (krausAction K A) 0 0
        (((1 - krausGram K) * A).trace • Matrix.single o₀ o₀ (1 : ℂ)) := by
  rw [completionKraus, flaggedKraus_action, repairKraus_action o₀ hK]

structure FiniteCPTP (I O : Type*) [Fintype I] [Fintype O] where
  map : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ
  completelyPositive : ∀ (r : ℕ) (A : Matrix (I × Fin r) (I × Fin r) ℂ),
    A.PosSemidef → (amplify map (Fin r) A).PosSemidef
  tracePreserving : ∀ A, (map A).trace = A.trace

def completedChannel (K : κ → Matrix O I ℂ) (o₀ : O)
    (hK : (1 - krausGram K).PosSemidef) : FiniteCPTP I (O ⊕ O) where
  map := krausMap (completionKraus K o₀)
  completelyPositive r A hA := krausMap_completelyPositive _ (Fin r) hA
  tracePreserving A := completionKraus_tracePreserving K o₀ hK A

def completedChannelOfTNI (K : κ → Matrix O I ℂ) (o₀ : O)
    (hT : ∀ A : Matrix I I ℂ, A.PosSemidef → (krausAction K A).trace ≤ A.trace) :
    FiniteCPTP I (O ⊕ O) :=
  completedChannel K o₀ (residual_posSemidef_of_traceNonincreasing K hT)

theorem exists_flagged_completion_of_traceNonincreasing
    (K : κ → Matrix O I ℂ) (o₀ : O)
    (hT : ∀ A : Matrix I I ℂ, A.PosSemidef → (krausAction K A).trace ≤ A.trace) :
    ∃ Φ : FiniteCPTP I (O ⊕ O), ∀ A : Matrix I I ℂ,
      Φ.map A = Matrix.fromBlocks (krausAction K A) 0 0
        (((1 - krausGram K) * A).trace • Matrix.single o₀ o₀ (1 : ℂ)) := by
  let hK := residual_posSemidef_of_traceNonincreasing K hT
  refine ⟨completedChannel K o₀ hK, ?_⟩
  intro A
  exact completionKraus_action K o₀ hK A

theorem completedChannel_density (K : κ → Matrix O I ℂ) (o₀ : O)
    (hK : (1 - krausGram K).PosSemidef) {A : Matrix I I ℂ}
    (hA : A.PosSemidef) (htrace : A.trace = 1) :
    ((completedChannel K o₀ hK).map A).PosSemidef ∧
      ((completedChannel K o₀ hK).map A).trace = 1 := by
  constructor
  · exact krausAction_posSemidef _ hA
  · exact ((completedChannel K o₀ hK).tracePreserving A).trans htrace

theorem completedChannel_amplify_tracePreserving (K : κ → Matrix O I ℂ) (o₀ : O)
    (hK : (1 - krausGram K).PosSemidef) (R : Type*) [Fintype R] [DecidableEq R]
    (A : Matrix (I × R) (I × R) ℂ) :
    (amplify (completedChannel K o₀ hK).map R A).trace = A.trace := by
  change (amplify (krausMap (completionKraus K o₀)) R A).trace = A.trace
  rw [amplify_krausMap]
  exact stabilizedKraus_tracePreserving _ (completionKraus_gram K o₀ hK) R A

variable {P Jdx : Type*} [Fintype P] [DecidableEq P] [Fintype Jdx]

def flagIndexEquiv (O : Type*) : (O ⊕ O) ≃ O × Bool where
  toFun := Sum.elim (fun o => (o, false)) (fun o => (o, true))
  invFun := fun x => if x.2 then Sum.inr x.1 else Sum.inl x.1
  left_inv x := by cases x <;> rfl
  right_inv x := by rcases x with ⟨o, b⟩; cases b <;> rfl

def flagIdentityKraus (L : Jdx → Matrix P O ℂ) :
    Jdx → Matrix (P ⊕ P) (O ⊕ O) ℂ :=
  fun l => Matrix.fromBlocks (L l) 0 0 (L l)

theorem flagIdentityKraus_tensor (L : Jdx → Matrix P O ℂ) (l : Jdx) :
    Matrix.reindex (flagIndexEquiv P) (flagIndexEquiv O) (flagIdentityKraus L l) =
      L l ⊗ₖ (1 : Matrix Bool Bool ℂ) := by
  ext ⟨p, b⟩ ⟨o, c⟩
  cases b <;> cases c <;>
    simp [flagIndexEquiv, flagIdentityKraus, Matrix.reindex_apply,
      Matrix.submatrix_apply, Matrix.kronecker_apply, Matrix.one_apply]

theorem flagIdentityKraus_gram (L : Jdx → Matrix P O ℂ) :
    krausGram (flagIdentityKraus L) =
      Matrix.fromBlocks (krausGram L) 0 0 (krausGram L) := by
  ext (a | a) (b | b) <;>
    simp [krausGram, flagIdentityKraus, Matrix.fromBlocks_conjTranspose,
      Matrix.fromBlocks_multiply, Matrix.sum_apply]

theorem flagIdentityKraus_complete (L : Jdx → Matrix P O ℂ) (hL : krausGram L = 1) :
    krausGram (flagIdentityKraus L) = 1 := by
  rw [flagIdentityKraus_gram, hL, Matrix.fromBlocks_one]

theorem flagIdentityKraus_action (L : Jdx → Matrix P O ℂ) (A B : Matrix O O ℂ) :
    krausAction (flagIdentityKraus L) (Matrix.fromBlocks A 0 0 B) =
      Matrix.fromBlocks (krausAction L A) 0 0 (krausAction L B) := by
  ext (a | a) (b | b) <;>
    simp [krausAction, flagIdentityKraus, Matrix.fromBlocks_conjTranspose,
      Matrix.fromBlocks_multiply, Matrix.sum_apply]

def flagIdentityChannel (L : Jdx → Matrix P O ℂ) (hL : krausGram L = 1) :
    FiniteCPTP (O ⊕ O) (P ⊕ P) where
  map := krausMap (flagIdentityKraus L)
  completelyPositive r A hA := krausMap_completelyPositive _ (Fin r) hA
  tracePreserving A := krausAction_tracePreserving _ (flagIdentityKraus_complete L hL) A

theorem postprocess_completion (K : κ → Matrix O I ℂ) (o₀ : O)
    (hK : (1 - krausGram K).PosSemidef) (L : Jdx → Matrix P O ℂ)
    (A : Matrix I I ℂ) :
    krausAction (flagIdentityKraus L) (krausAction (completionKraus K o₀) A) =
      Matrix.fromBlocks (krausAction L (krausAction K A)) 0 0
        (((1 - krausGram K) * A).trace •
          krausAction L (Matrix.single o₀ o₀ (1 : ℂ))) := by
  rw [completionKraus_action K o₀ hK A, flagIdentityKraus_action, krausAction_smul]

theorem postprocess_success_trace (K : κ → Matrix O I ℂ) (L : Jdx → Matrix P O ℂ)
    (hL : krausGram L = 1) (A : Matrix I I ℂ) :
    (krausAction L (krausAction K A)).trace = (krausAction K A).trace :=
  krausAction_tracePreserving L hL _

theorem amplify_flaggedKraus (K : κ → Matrix O I ℂ) (J : ι → Matrix O I ℂ)
    (R : Type*) [Fintype R] (A : Matrix (I × R) (I × R) ℂ) :
    Matrix.reindex (Equiv.sumProdDistrib O O R) (Equiv.sumProdDistrib O O R)
      (amplify (krausMap (flaggedKraus K J)) R A) =
      Matrix.fromBlocks (amplify (krausMap K) R A) 0 0
        (amplify (krausMap J) R A) := by
  ext (a | a) (b | b) <;>
    simp [Matrix.reindex_apply, Matrix.submatrix_apply,
      Equiv.sumProdDistrib_symm_apply_left, Equiv.sumProdDistrib_symm_apply_right,
      amplify, krausMap, flaggedKraus_action]
  all_goals
    rw [flaggedKraus_action K J (fun i j => A (i, a.2) (j, b.2))]
    rfl

theorem completedChannel_protected_flagBlocks (K : κ → Matrix O I ℂ) (o₀ : O)
    (hK : (1 - krausGram K).PosSemidef) (R : Type*) [Fintype R]
    (A : Matrix (I × R) (I × R) ℂ) :
    Matrix.reindex (Equiv.sumProdDistrib O O R) (Equiv.sumProdDistrib O O R)
      (amplify (completedChannel K o₀ hK).map R A) =
      Matrix.fromBlocks (amplify (krausMap K) R A) 0 0
        (amplify (krausMap (repairKraus o₀ (1 - krausGram K))) R A) :=
  amplify_flaggedKraus K (repairKraus o₀ (1 - krausGram K)) R A

end QuantumProver.SuperchannelDiscrimination.KrausCompletion

namespace QuantumProver.SuperchannelDiscrimination.CPWrappers

open KrausCompletion
open scoped ComplexOrder MatrixOrder Matrix

variable {I O P C D R : Type*}
  [Fintype I] [Fintype O] [Fintype P] [Fintype C] [Fintype D] [Fintype R]
  [DecidableEq I] [DecidableEq O] [DecidableEq P]
  [DecidableEq C] [DecidableEq D] [DecidableEq R]

def CompletelyPositive (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) : Prop :=
  ∀ (r : ℕ) (A : Matrix (I × Fin r) (I × Fin r) ℂ),
    A.PosSemidef → (amplify Φ (Fin r) A).PosSemidef

def CPDom (Φ Ψ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) (c : ℝ) : Prop :=
  CompletelyPositive ((c : ℂ) • Ψ - Φ)

def amplifyMap (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) (R : Type*) [Fintype R] :
    Matrix (I × R) (I × R) ℂ →ₗ[ℂ] Matrix (O × R) (O × R) ℂ where
  toFun := amplify Φ R
  map_add' A B := by
    ext x y
    exact congrArg (fun M : Matrix O O ℂ => M x.1 y.1)
      (Φ.map_add (fun i j => A (i, x.2) (j, y.2))
        (fun i j => B (i, x.2) (j, y.2)))
  map_smul' z A := by
    ext x y
    exact congrArg (fun M : Matrix O O ℂ => M x.1 y.1)
      (Φ.map_smul z (fun i j => A (i, x.2) (j, y.2)))

theorem completelyPositive_allReferences
    {Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ} (hΦ : CompletelyPositive Φ)
    (R : Type*) [Fintype R] [DecidableEq R]
    {A : Matrix (I × R) (I × R) ℂ} (hA : A.PosSemidef) :
    (amplify Φ R A).PosSemidef := by
  let e : Fin (Fintype.card R) ≃ R := (Fintype.equivFin R).symm
  let ei : (I × Fin (Fintype.card R)) ≃ I × R :=
    Equiv.prodCongr (Equiv.refl I) e
  let eo : (O × Fin (Fintype.card R)) ≃ O × R :=
    Equiv.prodCongr (Equiv.refl O) e
  have h := hΦ (Fintype.card R) (A.submatrix ei ei) (hA.submatrix ei)
  have heq : amplify Φ (Fin (Fintype.card R)) (A.submatrix ei ei) =
      (amplify Φ R A).submatrix eo eo := by
    ext x y
    rfl
  rw [heq] at h
  exact (Matrix.posSemidef_submatrix_equiv eo).mp h

theorem amplifyMap_comp
    (Φ : Matrix O O ℂ →ₗ[ℂ] Matrix P P ℂ)
    (Ψ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) (R : Type*) [Fintype R] :
    amplifyMap (Φ.comp Ψ) R = (amplifyMap Φ R).comp (amplifyMap Ψ R) := by
  ext A x y
  rfl

theorem completelyPositive_comp
    {Φ : Matrix O O ℂ →ₗ[ℂ] Matrix P P ℂ}
    {Ψ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ}
    (hΦ : CompletelyPositive Φ) (hΨ : CompletelyPositive Ψ) :
    CompletelyPositive (Φ.comp Ψ) := by
  intro r A hA
  change ((amplifyMap (Φ.comp Ψ) (Fin r)) A).PosSemidef
  rw [amplifyMap_comp]
  exact hΦ r _ (hΨ r A hA)

theorem amplifyMap_difference
    (Φ Ψ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) (c : ℝ)
    (R : Type*) [Fintype R] :
    amplifyMap ((c : ℂ) • Ψ - Φ) R =
      (c : ℂ) • amplifyMap Ψ R - amplifyMap Φ R := by
  ext A x y
  rfl

theorem completelyPositive_amplifyMap
    {Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ} (hΦ : CompletelyPositive Φ)
    (R : Type*) [Fintype R] [DecidableEq R] :
    CompletelyPositive (amplifyMap Φ R) := by
  intro r A hA
  let ei := Equiv.prodAssoc I R (Fin r)
  let eo := Equiv.prodAssoc O R (Fin r)
  have h := completelyPositive_allReferences hΦ (R × Fin r)
    (hA := hA.submatrix ei.symm)
  have heq : amplify Φ (R × Fin r) (A.submatrix ei.symm ei.symm) =
      (amplify (amplifyMap Φ R) (Fin r) A).submatrix eo.symm eo.symm := by
    ext x y
    rfl
  rw [heq] at h
  exact (Matrix.posSemidef_submatrix_equiv eo.symm).mp h

theorem cpDom_precompose
    {Φ Ψ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ} {c : ℝ}
    (h : CPDom Φ Ψ c) {pre : Matrix C C ℂ →ₗ[ℂ] Matrix I I ℂ}
    (hpre : CompletelyPositive pre) : CPDom (Φ.comp pre) (Ψ.comp pre) c := by
  unfold CPDom at *
  have hd := completelyPositive_comp h hpre
  simpa only [LinearMap.sub_comp, LinearMap.smul_comp] using hd

theorem cpDom_postcompose
    {Φ Ψ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ} {c : ℝ}
    (h : CPDom Φ Ψ c) {post : Matrix O O ℂ →ₗ[ℂ] Matrix P P ℂ}
    (hpost : CompletelyPositive post) : CPDom (post.comp Φ) (post.comp Ψ) c := by
  unfold CPDom at *
  have hd := completelyPositive_comp hpost h
  simpa only [LinearMap.comp_sub, LinearMap.comp_smul] using hd

theorem cpDom_amplifyMap
    {Φ Ψ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ} {c : ℝ}
    (h : CPDom Φ Ψ c) (R : Type*) [Fintype R] [DecidableEq R] :
    CPDom (amplifyMap Φ R) (amplifyMap Ψ R) c := by
  unfold CPDom at *
  simpa only [amplifyMap_difference] using completelyPositive_amplifyMap h R

def reindexMap (e : I ≃ O) : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ where
  toFun := Matrix.reindex e e
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem reindexMap_apply (e : I ≃ O) (A : Matrix I I ℂ) :
    reindexMap e A = Matrix.reindex e e A := rfl

theorem completelyPositive_reindexMap (e : I ≃ O) :
    CompletelyPositive (reindexMap e) := by
  intro r A hA
  have h := hA.submatrix (Equiv.prodCongr e.symm (Equiv.refl (Fin r)))
  exact h

theorem reindexMap_tracePreserving (e : I ≃ O) (A : Matrix I I ℂ) :
    (reindexMap e A).trace = A.trace := by
  exact e.symm.sum_comp (fun i => A i i)

def reindexChannel (e : I ≃ O) : FiniteCPTP I O where
  map := reindexMap e
  completelyPositive := completelyPositive_reindexMap e
  tracePreserving := reindexMap_tracePreserving e

def composeChannel (Φ : FiniteCPTP O P) (Ψ : FiniteCPTP I O) : FiniteCPTP I P where
  map := Φ.map.comp Ψ.map
  completelyPositive := completelyPositive_comp Φ.completelyPositive Ψ.completelyPositive
  tracePreserving A := (Φ.tracePreserving (Ψ.map A)).trans (Ψ.tracePreserving A)

theorem amplifyMap_tracePreserving
    (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ)
    (hΦ : ∀ A, (Φ A).trace = A.trace)
    (R : Type*) [Fintype R] (A : Matrix (I × R) (I × R) ℂ) :
    (amplifyMap Φ R A).trace = A.trace := by
  calc
    (amplifyMap Φ R A).trace =
        ∑ r : R, (Φ (fun i j => A (i, r) (j, r))).trace := by
      simp only [amplifyMap, amplify, Matrix.trace, Matrix.diag, Fintype.sum_prod_type]
      exact Finset.sum_comm
    _ = ∑ r : R, Matrix.trace ((fun i j => A (i, r) (j, r)) : Matrix I I ℂ) := by
      apply Finset.sum_congr rfl
      intro r hr
      exact hΦ _
    _ = A.trace := by
      simp only [Matrix.trace, Matrix.diag, Fintype.sum_prod_type]
      exact Finset.sum_comm

def amplifiedChannel (Φ : FiniteCPTP I O) (R : Type*) [Fintype R] [DecidableEq R] :
    FiniteCPTP (I × R) (O × R) where
  map := amplifyMap Φ.map R
  completelyPositive := completelyPositive_amplifyMap Φ.completelyPositive R
  tracePreserving := amplifyMap_tracePreserving Φ.map Φ.tracePreserving R

def amplifyLeftMap (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) (R : Type*) [Fintype R] :
    Matrix (R × I) (R × I) ℂ →ₗ[ℂ] Matrix (R × O) (R × O) ℂ :=
  (reindexMap (Equiv.prodComm O R)).comp
    ((amplifyMap Φ R).comp (reindexMap (Equiv.prodComm R I)))

theorem amplifyLeftMap_apply (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ)
    (R : Type*) [Fintype R] (A : Matrix (R × I) (R × I) ℂ) (x y : R × O) :
    amplifyLeftMap Φ R A x y = Φ (fun i j => A (x.1, i) (y.1, j)) x.2 y.2 := rfl

theorem completelyPositive_amplifyLeftMap
    {Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ} (hΦ : CompletelyPositive Φ)
    (R : Type*) [Fintype R] [DecidableEq R] :
    CompletelyPositive (amplifyLeftMap Φ R) :=
  completelyPositive_comp (completelyPositive_reindexMap _)
    (completelyPositive_comp (completelyPositive_amplifyMap hΦ R)
      (completelyPositive_reindexMap _))

theorem amplifyLeftMap_difference
    (Φ Ψ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) (c : ℝ)
    (R : Type*) [Fintype R] :
    amplifyLeftMap ((c : ℂ) • Ψ - Φ) R =
      (c : ℂ) • amplifyLeftMap Ψ R - amplifyLeftMap Φ R := by
  simp only [amplifyLeftMap, amplifyMap_difference,
    LinearMap.comp_sub, LinearMap.comp_smul, LinearMap.sub_comp, LinearMap.smul_comp]

theorem cpDom_amplifyLeftMap
    {Φ Ψ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ} {c : ℝ}
    (h : CPDom Φ Ψ c) (R : Type*) [Fintype R] [DecidableEq R] :
    CPDom (amplifyLeftMap Φ R) (amplifyLeftMap Ψ R) c := by
  unfold CPDom at *
  simpa only [amplifyLeftMap_difference] using completelyPositive_amplifyLeftMap h R

def amplifiedLeftChannel (Φ : FiniteCPTP I O) (R : Type*)
    [Fintype R] [DecidableEq R] : FiniteCPTP (R × I) (R × O) :=
  composeChannel (reindexChannel (Equiv.prodComm O R))
    (composeChannel (amplifiedChannel Φ R) (reindexChannel (Equiv.prodComm R I)))

structure FiniteSuperchannel (I O C D R : Type*)
    [Fintype I] [Fintype O] [Fintype C] [Fintype D] [Fintype R] where
  pre : FiniteCPTP C (R × I)
  post : FiniteCPTP (R × O) D

def FiniteSuperchannel.applyLinear (Γ : FiniteSuperchannel I O C D R)
    (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) : Matrix C C ℂ →ₗ[ℂ] Matrix D D ℂ :=
  Γ.post.map.comp ((amplifyLeftMap Φ R).comp Γ.pre.map)

def FiniteSuperchannel.applyChannel (Γ : FiniteSuperchannel I O C D R)
    (Φ : FiniteCPTP I O) : FiniteCPTP C D :=
  composeChannel Γ.post (composeChannel (amplifiedLeftChannel Φ R) Γ.pre)

theorem FiniteSuperchannel.applyChannel_map (Γ : FiniteSuperchannel I O C D R)
    (Φ : FiniteCPTP I O) : (Γ.applyChannel Φ).map = Γ.applyLinear Φ.map := rfl

theorem cpDom_superchannel (Γ : FiniteSuperchannel I O C D R)
    {Φ Ψ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ} {c : ℝ} (h : CPDom Φ Ψ c) :
    CPDom (Γ.applyLinear Φ) (Γ.applyLinear Ψ) c :=
  cpDom_postcompose
    (cpDom_precompose (cpDom_amplifyLeftMap h R) Γ.pre.completelyPositive)
    Γ.post.completelyPositive

theorem completelyPositive_positive
    {Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ} (hΦ : CompletelyPositive Φ)
    {A : Matrix I I ℂ} (hA : A.PosSemidef) : (Φ A).PosSemidef := by
  have h := hΦ 1 (A.submatrix Prod.fst Prod.fst) (hA.submatrix Prod.fst)
  have heq : (amplify Φ (Fin 1) (A.submatrix Prod.fst Prod.fst)).submatrix
      (fun o => (o, (0 : Fin 1))) (fun o => (o, (0 : Fin 1))) = Φ A := by
    ext i j
    rfl
  rw [← heq]
  exact h.submatrix _

theorem cpDom_outputOrder
    {Φ Ψ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ} {c : ℝ}
    (h : CPDom Φ Ψ c) {A : Matrix I I ℂ} (hA : A.PosSemidef) :
    ((c : ℂ) • Ψ A - Φ A).PosSemidef :=
  completelyPositive_positive h hA

def acceptance (A E : Matrix O O ℂ) : ℝ := (A * E).trace.re

theorem acceptance_le_of_outputOrder {A B E : Matrix O O ℂ} {c : ℝ}
    (hAB : ((c : ℂ) • B - A).PosSemidef) (hE : E.PosSemidef) :
    acceptance A E ≤ c * acceptance B E := by
  have h := (Complex.le_def.mp (trace_mul_mono_of_posSemidef hAB hE)).1
  simpa only [acceptance, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] using h

theorem cpDom_acceptance
    {Φ Ψ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ} {c : ℝ}
    (h : CPDom Φ Ψ c) {A : Matrix I I ℂ} (hA : A.PosSemidef)
    {E : Matrix O O ℂ} (hE : E.PosSemidef) :
    acceptance (Φ A) E ≤ c * acceptance (Ψ A) E :=
  acceptance_le_of_outputOrder (cpDom_outputOrder h hA) hE

theorem cpDom_superchannel_acceptance (Γ : FiniteSuperchannel I O C D R)
    {Φ Ψ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ} {c : ℝ}
    (h : CPDom Φ Ψ c) {A : Matrix C C ℂ} (hA : A.PosSemidef)
    {E : Matrix D D ℂ} (hE : E.PosSemidef) :
    acceptance (Γ.applyLinear Φ A) E ≤ c * acceptance (Γ.applyLinear Ψ A) E :=
  cpDom_acceptance (cpDom_superchannel Γ h) hA hE

theorem cpDom_superchannel_reference_acceptance (Γ : FiniteSuperchannel I O C D R)
    {Φ Ψ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ} {c : ℝ}
    (h : CPDom Φ Ψ c) (T : Type*) [Fintype T] [DecidableEq T]
    {A : Matrix (C × T) (C × T) ℂ} (hA : A.PosSemidef)
    {E : Matrix (D × T) (D × T) ℂ} (hE : E.PosSemidef) :
    acceptance (amplifyMap (Γ.applyLinear Φ) T A) E ≤
      c * acceptance (amplifyMap (Γ.applyLinear Ψ) T A) E :=
  cpDom_acceptance (cpDom_amplifyMap (cpDom_superchannel Γ h) T) hA hE

theorem acceptance_nonneg {A E : Matrix O O ℂ}
    (hA : A.PosSemidef) (hE : E.PosSemidef) : 0 ≤ acceptance A E :=
  (Complex.le_def.mp (trace_mul_nonneg_of_posSemidef hA hE)).1

theorem acceptance_le_trace {A E : Matrix O O ℂ}
    (hA : A.PosSemidef) (hE : (1 - E).PosSemidef) :
    acceptance A E ≤ A.trace.re := by
  have h := (Complex.le_def.mp (trace_mul_nonneg_of_posSemidef hA hE)).1
  simp only [Matrix.mul_sub, Matrix.mul_one, Matrix.trace_sub, Complex.sub_re] at h
  exact sub_nonneg.mp h

theorem channel_density (Φ : FiniteCPTP I O) {A : Matrix I I ℂ}
    (hA : A.PosSemidef) (htrace : A.trace = 1) :
    (Φ.map A).PosSemidef ∧ (Φ.map A).trace = 1 :=
  ⟨completelyPositive_positive Φ.completelyPositive hA,
    (Φ.tracePreserving A).trans htrace⟩

theorem channel_acceptance_bounds (Φ : FiniteCPTP I O) {A : Matrix I I ℂ}
    (hA : A.PosSemidef) (htrace : A.trace = 1) {E : Matrix O O ℂ}
    (hE : E.PosSemidef ∧ (1 - E).PosSemidef) :
    0 ≤ acceptance (Φ.map A) E ∧ acceptance (Φ.map A) E ≤ 1 := by
  have hρ := channel_density Φ hA htrace
  refine ⟨acceptance_nonneg hρ.1 hE.1, ?_⟩
  simpa only [hρ.2, Complex.one_re] using acceptance_le_trace hρ.1 hE.2

theorem superchannel_channel_density (Γ : FiniteSuperchannel I O C D R)
    (Φ : FiniteCPTP I O) {A : Matrix C C ℂ}
    (hA : A.PosSemidef) (htrace : A.trace = 1) :
    (Γ.applyLinear Φ.map A).PosSemidef ∧ (Γ.applyLinear Φ.map A).trace = 1 :=
  channel_density (Γ.applyChannel Φ) hA htrace

theorem superchannel_normalized_acceptance (Γ : FiniteSuperchannel I O C D R)
    (Φ Ψ : FiniteCPTP I O) {c : ℝ} (h : CPDom Φ.map Ψ.map c)
    {A : Matrix C C ℂ} (hA : A.PosSemidef) (htrace : A.trace = 1)
    {E : Matrix D D ℂ} (hE : E.PosSemidef ∧ (1 - E).PosSemidef) :
    (0 ≤ acceptance (Γ.applyLinear Φ.map A) E ∧
      acceptance (Γ.applyLinear Φ.map A) E ≤ 1) ∧
    (0 ≤ acceptance (Γ.applyLinear Ψ.map A) E ∧
      acceptance (Γ.applyLinear Ψ.map A) E ≤ 1) ∧
    acceptance (Γ.applyLinear Φ.map A) E ≤ c * acceptance (Γ.applyLinear Ψ.map A) E :=
  ⟨channel_acceptance_bounds (Γ.applyChannel Φ) hA htrace hE,
    channel_acceptance_bounds (Γ.applyChannel Ψ) hA htrace hE,
    cpDom_superchannel_acceptance Γ h hA hE.1⟩

theorem cpDom_state_outputOrder
    {Φ Ψ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ} {b c : ℝ}
    (hΦ : CompletelyPositive Φ) (h : CPDom Φ Ψ c) (hb : 0 ≤ b)
    {A B : Matrix I I ℂ} (hB : B.PosSemidef)
    (hAB : ((b : ℂ) • B - A).PosSemidef) :
    (((b * c : ℝ) : ℂ) • Ψ B - Φ A).PosSemidef := by
  have h₁ := completelyPositive_positive hΦ hAB
  simp only [map_sub, map_smul] at h₁
  have h₂ : ((b : ℂ) • ((c : ℂ) • Ψ B - Φ B)).PosSemidef :=
    (cpDom_outputOrder h hB).smul (Complex.zero_le_real.mpr hb)
  have heq : ((b : ℂ) • Φ B - Φ A) +
      (b : ℂ) • ((c : ℂ) • Ψ B - Φ B) =
        (((b * c : ℝ) : ℂ) • Ψ B - Φ A) := by
    simp only [smul_sub, smul_smul, Complex.ofReal_mul]
    abel
  rw [← heq]
  exact h₁.add h₂

theorem superchannel_completelyPositive (Γ : FiniteSuperchannel I O C D R)
    {Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ} (hΦ : CompletelyPositive Φ) :
    CompletelyPositive (Γ.applyLinear Φ) :=
  completelyPositive_comp Γ.post.completelyPositive
    (completelyPositive_comp (completelyPositive_amplifyLeftMap hΦ R)
      Γ.pre.completelyPositive)

theorem cpDom_superchannel_state_acceptance (Γ : FiniteSuperchannel I O C D R)
    {Φ Ψ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ} {b c : ℝ}
    (hΦ : CompletelyPositive Φ) (h : CPDom Φ Ψ c) (hb : 0 ≤ b)
    {A B : Matrix C C ℂ} (hB : B.PosSemidef)
    (hAB : ((b : ℂ) • B - A).PosSemidef)
    {E : Matrix D D ℂ} (hE : E.PosSemidef) :
    acceptance (Γ.applyLinear Φ A) E ≤
      (b * c) * acceptance (Γ.applyLinear Ψ B) E :=
  acceptance_le_of_outputOrder
    (cpDom_state_outputOrder (superchannel_completelyPositive Γ hΦ)
      (cpDom_superchannel Γ h) hb hB hAB) hE

theorem cpDom_superchannel_reference_state_acceptance
    (Γ : FiniteSuperchannel I O C D R)
    {Φ Ψ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ} {b c : ℝ}
    (hΦ : CompletelyPositive Φ) (h : CPDom Φ Ψ c) (hb : 0 ≤ b)
    (T : Type*) [Fintype T] [DecidableEq T]
    {A B : Matrix (C × T) (C × T) ℂ} (hB : B.PosSemidef)
    (hAB : ((b : ℂ) • B - A).PosSemidef)
    {E : Matrix (D × T) (D × T) ℂ} (hE : E.PosSemidef) :
    acceptance (amplifyMap (Γ.applyLinear Φ) T A) E ≤
      (b * c) * acceptance (amplifyMap (Γ.applyLinear Ψ) T B) E :=
  acceptance_le_of_outputOrder
    (cpDom_state_outputOrder
      (completelyPositive_amplifyMap (superchannel_completelyPositive Γ hΦ) T)
      (cpDom_amplifyMap (cpDom_superchannel Γ h) T) hb hB hAB) hE

def TraceNonincreasing (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) : Prop :=
  ∀ A, A.PosSemidef → (Φ A).trace ≤ A.trace

theorem amplifyMap_traceNonincreasing
    {Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ} (hΦ : TraceNonincreasing Φ)
    (R : Type*) [Fintype R] {A : Matrix (I × R) (I × R) ℂ}
    (hA : A.PosSemidef) : (amplifyMap Φ R A).trace ≤ A.trace := by
  calc
    (amplifyMap Φ R A).trace =
        ∑ r : R, (Φ (fun i j => A (i, r) (j, r))).trace := by
      simp only [amplifyMap, amplify, Matrix.trace, Matrix.diag, Fintype.sum_prod_type]
      exact Finset.sum_comm
    _ ≤ ∑ r : R, Matrix.trace ((fun i j => A (i, r) (j, r)) : Matrix I I ℂ) := by
      apply Finset.sum_le_sum
      intro r hr
      exact hΦ _ (hA.submatrix (fun i => (i, r)))
    _ = A.trace := by
      simp only [Matrix.trace, Matrix.diag, Fintype.sum_prod_type]
      exact Finset.sum_comm

theorem amplifyLeftMap_traceNonincreasing
    {Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ} (hΦ : TraceNonincreasing Φ)
    (R : Type*) [Fintype R] {A : Matrix (R × I) (R × I) ℂ}
    (hA : A.PosSemidef) : (amplifyLeftMap Φ R A).trace ≤ A.trace := by
  classical
  change (reindexMap (Equiv.prodComm O R)
    (amplifyMap Φ R (reindexMap (Equiv.prodComm R I) A))).trace ≤ A.trace
  rw [reindexMap_tracePreserving]
  have hpos := completelyPositive_positive
    (completelyPositive_reindexMap (Equiv.prodComm R I)) hA
  exact (amplifyMap_traceNonincreasing hΦ R hpos).trans_eq
    (reindexMap_tracePreserving (Equiv.prodComm R I) A)

theorem superchannel_traceNonincreasing (Γ : FiniteSuperchannel I O C D R)
    {Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ} (hΦ : TraceNonincreasing Φ) :
    TraceNonincreasing (Γ.applyLinear Φ) := by
  intro A hA
  change (Γ.post.map (amplifyLeftMap Φ R (Γ.pre.map A))).trace ≤ A.trace
  rw [Γ.post.tracePreserving]
  have hpre := completelyPositive_positive Γ.pre.completelyPositive hA
  exact (amplifyLeftMap_traceNonincreasing hΦ R hpre).trans_eq
    (Γ.pre.tracePreserving A)

theorem superchannel_subnormalized (Γ : FiniteSuperchannel I O C D R)
    {Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ}
    (hΦ : CompletelyPositive Φ) (hT : TraceNonincreasing Φ)
    {A : Matrix C C ℂ} (hA : A.PosSemidef) (htrace : A.trace = 1) :
    (Γ.applyLinear Φ A).PosSemidef ∧
      0 ≤ (Γ.applyLinear Φ A).trace ∧ (Γ.applyLinear Φ A).trace ≤ 1 := by
  have hpos := completelyPositive_positive (superchannel_completelyPositive Γ hΦ) hA
  refine ⟨hpos, hpos.trace_nonneg, ?_⟩
  exact (superchannel_traceNonincreasing Γ hT A hA).trans_eq htrace

def flagLiftMap (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) :
    Matrix (I ⊕ I) (I ⊕ I) ℂ →ₗ[ℂ] Matrix (O ⊕ O) (O ⊕ O) ℂ :=
  (reindexMap (flagIndexEquiv O).symm).comp
    ((amplifyMap Φ Bool).comp (reindexMap (flagIndexEquiv I)))

theorem flagLiftMap_action (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ)
    (A B : Matrix I I ℂ) :
    flagLiftMap Φ (Matrix.fromBlocks A 0 0 B) =
      Matrix.fromBlocks (Φ A) 0 0 (Φ B) := by
  ext (a | a) (b | b)
  · rfl
  · change Φ 0 a b = 0
    rw [map_zero]
    rfl
  · change Φ 0 a b = 0
    rw [map_zero]
    rfl
  · rfl

theorem completelyPositive_flagLiftMap
    {Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ} (hΦ : CompletelyPositive Φ) :
    CompletelyPositive (flagLiftMap Φ) :=
  completelyPositive_comp (completelyPositive_reindexMap _)
    (completelyPositive_comp (completelyPositive_amplifyMap hΦ Bool)
      (completelyPositive_reindexMap _))

def flagLiftChannel (Φ : FiniteCPTP I O) : FiniteCPTP (I ⊕ I) (O ⊕ O) :=
  composeChannel (reindexChannel (flagIndexEquiv O).symm)
    (composeChannel (amplifiedChannel Φ Bool) (reindexChannel (flagIndexEquiv I)))

theorem flagLiftChannel_map (Φ : FiniteCPTP I O) :
    (flagLiftChannel Φ).map = flagLiftMap Φ.map := rfl

theorem flagLiftMap_traceNonincreasing
    {Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ} (hΦ : TraceNonincreasing Φ) :
    TraceNonincreasing (flagLiftMap Φ) := by
  intro A hA
  change (reindexMap (flagIndexEquiv O).symm
    (amplifyMap Φ Bool (reindexMap (flagIndexEquiv I) A))).trace ≤ A.trace
  rw [reindexMap_tracePreserving]
  exact (amplifyMap_traceNonincreasing hΦ Bool
    (completelyPositive_positive (completelyPositive_reindexMap _) hA)).trans_eq
      (reindexMap_tracePreserving (flagIndexEquiv I) A)

theorem cpDom_flagLiftMap
    {Φ Ψ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ} {c : ℝ} (h : CPDom Φ Ψ c) :
    CPDom (flagLiftMap Φ) (flagLiftMap Ψ) c :=
  cpDom_postcompose
    (cpDom_precompose (cpDom_amplifyMap h Bool) (completelyPositive_reindexMap _))
    (completelyPositive_reindexMap _)

theorem flagLiftMap_success_trace (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ)
    (A B : Matrix I I ℂ) (E : Matrix O O ℂ) :
    (flagLiftMap Φ (Matrix.fromBlocks A 0 0 B) *
      Matrix.fromBlocks E 0 0 (0 : Matrix O O ℂ)).trace = (Φ A * E).trace := by
  rw [flagLiftMap_action, Matrix.fromBlocks_multiply]
  simp [Matrix.trace, Matrix.diag, Fintype.sum_sum_type]

theorem flagLiftMap_success_acceptance (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ)
    (A B : Matrix I I ℂ) (E : Matrix O O ℂ) :
    acceptance (flagLiftMap Φ (Matrix.fromBlocks A 0 0 B))
      (Matrix.fromBlocks E 0 0 (0 : Matrix O O ℂ)) = acceptance (Φ A) E :=
  congrArg Complex.re (flagLiftMap_success_trace Φ A B E)

theorem cpDom_superchannel_flagged_acceptance (Γ : FiniteSuperchannel I O C D R)
    {Φ Ψ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ} {b c : ℝ}
    (hΦ : CompletelyPositive Φ) (h : CPDom Φ Ψ c) (hb : 0 ≤ b)
    {A B : Matrix C C ℂ} (hB : B.PosSemidef)
    (hAB : ((b : ℂ) • B - A).PosSemidef)
    (repair : Matrix C C ℂ) {E : Matrix D D ℂ} (hE : E.PosSemidef) :
    acceptance (flagLiftMap (Γ.applyLinear Φ) (Matrix.fromBlocks A 0 0 repair))
      (Matrix.fromBlocks E 0 0 (0 : Matrix D D ℂ)) ≤
        (b * c) * acceptance (Γ.applyLinear Ψ B) E := by
  rw [flagLiftMap_success_acceptance]
  exact cpDom_superchannel_state_acceptance Γ hΦ h hb hB hAB hE

def FiniteSuperchannel.wrapFlaggedLinear (Γ : FiniteSuperchannel I O C D R)
    (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix (O ⊕ O) (O ⊕ O) ℂ) :
    Matrix C C ℂ →ₗ[ℂ] Matrix (D ⊕ D) (D ⊕ D) ℂ :=
  (flagLiftMap Γ.post.map).comp
    ((reindexMap (Equiv.prodSumDistrib R O O)).comp
      ((amplifyLeftMap Φ R).comp Γ.pre.map))

def FiniteSuperchannel.wrapFlaggedChannel (Γ : FiniteSuperchannel I O C D R)
    (Φ : FiniteCPTP I (O ⊕ O)) : FiniteCPTP C (D ⊕ D) :=
  composeChannel (flagLiftChannel Γ.post)
    (composeChannel (reindexChannel (Equiv.prodSumDistrib R O O))
      (composeChannel (amplifiedLeftChannel Φ R) Γ.pre))

theorem FiniteSuperchannel.wrapFlaggedChannel_map
    (Γ : FiniteSuperchannel I O C D R) (Φ : FiniteCPTP I (O ⊕ O)) :
    (Γ.wrapFlaggedChannel Φ).map = Γ.wrapFlaggedLinear Φ.map := rfl

variable {κ ι : Type*} [Fintype κ] [Fintype ι]

theorem krausMap_apply (K : κ → Matrix O I ℂ) (A : Matrix I I ℂ) :
    krausMap K A = krausAction K A := rfl

theorem amplifyLeftMap_flaggedKraus (K : κ → Matrix O I ℂ)
    (J : ι → Matrix O I ℂ) (R : Type*) [Fintype R]
    (A : Matrix (R × I) (R × I) ℂ) :
    reindexMap (Equiv.prodSumDistrib R O O)
      (amplifyLeftMap (krausMap (flaggedKraus K J)) R A) =
      Matrix.fromBlocks (amplifyLeftMap (krausMap K) R A) 0 0
        (amplifyLeftMap (krausMap J) R A) := by
  ext (a | a) (b | b)
  · exact congrArg (fun M : Matrix (O ⊕ O) (O ⊕ O) ℂ =>
      M (Sum.inl a.2) (Sum.inl b.2))
      (flaggedKraus_action K J (fun i j => A (a.1, i) (b.1, j)))
  · exact congrArg (fun M : Matrix (O ⊕ O) (O ⊕ O) ℂ =>
      M (Sum.inl a.2) (Sum.inr b.2))
      (flaggedKraus_action K J (fun i j => A (a.1, i) (b.1, j)))
  · exact congrArg (fun M : Matrix (O ⊕ O) (O ⊕ O) ℂ =>
      M (Sum.inr a.2) (Sum.inl b.2))
      (flaggedKraus_action K J (fun i j => A (a.1, i) (b.1, j)))
  · exact congrArg (fun M : Matrix (O ⊕ O) (O ⊕ O) ℂ =>
      M (Sum.inr a.2) (Sum.inr b.2))
      (flaggedKraus_action K J (fun i j => A (a.1, i) (b.1, j)))

theorem superchannel_flaggedKraus_action (Γ : FiniteSuperchannel I O C D R)
    (K : κ → Matrix O I ℂ) (J : ι → Matrix O I ℂ) (A : Matrix C C ℂ) :
    Γ.wrapFlaggedLinear (krausMap (flaggedKraus K J)) A =
      Matrix.fromBlocks (Γ.applyLinear (krausMap K) A) 0 0
        (Γ.applyLinear (krausMap J) A) := by
  change flagLiftMap Γ.post.map
    (reindexMap (Equiv.prodSumDistrib R O O)
      (amplifyLeftMap (krausMap (flaggedKraus K J)) R (Γ.pre.map A))) = _
  rw [amplifyLeftMap_flaggedKraus, flagLiftMap_action]
  rfl

theorem superchannel_completedChannel_action (Γ : FiniteSuperchannel I O C D R)
    (K : κ → Matrix O I ℂ) (o₀ : O) (hK : (1 - krausGram K).PosSemidef)
    (A : Matrix C C ℂ) :
    (Γ.wrapFlaggedChannel (completedChannel K o₀ hK)).map A =
      Matrix.fromBlocks (Γ.applyLinear (krausMap K) A) 0 0
        (Γ.applyLinear (krausMap (repairKraus o₀ (1 - krausGram K))) A) :=
  superchannel_flaggedKraus_action Γ K _ A

theorem superchannel_completedChannel_density (Γ : FiniteSuperchannel I O C D R)
    (K : κ → Matrix O I ℂ) (o₀ : O) (hK : (1 - krausGram K).PosSemidef)
    {A : Matrix C C ℂ} (hA : A.PosSemidef) (htrace : A.trace = 1) :
    ((Γ.wrapFlaggedChannel (completedChannel K o₀ hK)).map A).PosSemidef ∧
      ((Γ.wrapFlaggedChannel (completedChannel K o₀ hK)).map A).trace = 1 :=
  channel_density (Γ.wrapFlaggedChannel (completedChannel K o₀ hK)) hA htrace

theorem superchannel_completedChannel_success_acceptance
    (Γ : FiniteSuperchannel I O C D R) (K : κ → Matrix O I ℂ) (o₀ : O)
    (hK : (1 - krausGram K).PosSemidef) (A : Matrix C C ℂ) (E : Matrix D D ℂ) :
    acceptance ((Γ.wrapFlaggedChannel (completedChannel K o₀ hK)).map A)
      (Matrix.fromBlocks E 0 0 (0 : Matrix D D ℂ)) =
        acceptance (Γ.applyLinear (krausMap K) A) E := by
  rw [superchannel_completedChannel_action]
  change (Matrix.fromBlocks (Γ.applyLinear (krausMap K) A) 0 0
    (Γ.applyLinear (krausMap (repairKraus o₀ (1 - krausGram K))) A) *
      Matrix.fromBlocks E 0 0 (0 : Matrix D D ℂ)).trace.re = _
  rw [Matrix.fromBlocks_multiply]
  simp [acceptance, Matrix.trace, Matrix.diag, Fintype.sum_sum_type]

theorem superchannel_completedChannel_acceptance_domination
    (Γ : FiniteSuperchannel I O C D R) (K : κ → Matrix O I ℂ) (o₀ : O)
    (hK : (1 - krausGram K).PosSemidef)
    {Ψ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ} {b c : ℝ}
    (h : CPDom (krausMap K) Ψ c) (hb : 0 ≤ b)
    {A B : Matrix C C ℂ} (hB : B.PosSemidef)
    (hAB : ((b : ℂ) • B - A).PosSemidef)
    {E : Matrix D D ℂ} (hE : E.PosSemidef) :
    acceptance ((Γ.wrapFlaggedChannel (completedChannel K o₀ hK)).map A)
      (Matrix.fromBlocks E 0 0 (0 : Matrix D D ℂ)) ≤
        (b * c) * acceptance (Γ.applyLinear Ψ B) E := by
  rw [superchannel_completedChannel_success_acceptance]
  exact cpDom_superchannel_state_acceptance Γ
    (fun r X hX => krausMap_completelyPositive K (Fin r) hX) h hb hB hAB hE

theorem krausMap_success_trace_ge_weighted (K : κ → Matrix O I ℂ)
    {δ : ℝ} (hHD : (δ • (1 : Matrix I I ℂ) - (1 - krausGram K)).PosSemidef)
    {A : Matrix I I ℂ} (hA : A.PosSemidef) :
    (1 - (δ : ℂ)) * A.trace ≤ (krausMap K A).trace := by
  have h := trace_mul_mono_of_posSemidef hHD hA
  simp only [Matrix.smul_mul, Matrix.one_mul, Matrix.trace_smul] at h
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub, ← trace_krausAction] at h
  simpa only [sub_mul, one_mul, Complex.real_smul, krausMap_apply] using sub_le_comm.mp h

theorem amplifyMap_success_trace_ge (K : κ → Matrix O I ℂ)
    {δ : ℝ} (hHD : (δ • (1 : Matrix I I ℂ) - (1 - krausGram K)).PosSemidef)
    (R : Type*) [Fintype R] {A : Matrix (I × R) (I × R) ℂ}
    (hA : A.PosSemidef) :
    (1 - (δ : ℂ)) * A.trace ≤ (amplifyMap (krausMap K) R A).trace := by
  have hsum : (∑ r : R, (1 - (δ : ℂ)) *
      Matrix.trace ((fun i j => A (i, r) (j, r)) : Matrix I I ℂ)) ≤
      ∑ r : R, (krausMap K (fun i j => A (i, r) (j, r))).trace := by
    apply Finset.sum_le_sum
    intro r hr
    exact krausMap_success_trace_ge_weighted K hHD (hA.submatrix (fun i => (i, r)))
  have hinput : (∑ r : R, Matrix.trace ((fun i j => A (i, r) (j, r)) : Matrix I I ℂ)) =
      A.trace := by
    simp only [Matrix.trace, Matrix.diag, Fintype.sum_prod_type]
    exact Finset.sum_comm
  have houtput : (∑ r : R, (krausMap K (fun i j => A (i, r) (j, r))).trace) =
      (amplifyMap (krausMap K) R A).trace := by
    simp only [Matrix.trace, Matrix.diag, amplifyMap, amplify, Fintype.sum_prod_type]
    exact Finset.sum_comm
  rw [← Finset.mul_sum, hinput, houtput] at hsum
  exact hsum

theorem amplifyLeftMap_success_trace_ge (K : κ → Matrix O I ℂ)
    {δ : ℝ} (hHD : (δ • (1 : Matrix I I ℂ) - (1 - krausGram K)).PosSemidef)
    (R : Type*) [Fintype R] {A : Matrix (R × I) (R × I) ℂ}
    (hA : A.PosSemidef) :
    (1 - (δ : ℂ)) * A.trace ≤ (amplifyLeftMap (krausMap K) R A).trace := by
  classical
  have h := amplifyMap_success_trace_ge K hHD R
    (completelyPositive_positive (completelyPositive_reindexMap (Equiv.prodComm R I)) hA)
  rw [reindexMap_tracePreserving] at h
  change (1 - (δ : ℂ)) * A.trace ≤
    (reindexMap (Equiv.prodComm O R)
      (amplifyMap (krausMap K) R (reindexMap (Equiv.prodComm R I) A))).trace
  rw [reindexMap_tracePreserving]
  exact h

theorem superchannel_success_trace_ge (Γ : FiniteSuperchannel I O C D R)
    (K : κ → Matrix O I ℂ) {δ : ℝ}
    (hHD : (δ • (1 : Matrix I I ℂ) - (1 - krausGram K)).PosSemidef)
    {A : Matrix C C ℂ} (hA : A.PosSemidef) (htrace : A.trace = 1) :
    (1 : ℂ) - (δ : ℂ) ≤ (Γ.applyLinear (krausMap K) A).trace := by
  have h := amplifyLeftMap_success_trace_ge K hHD R
    (completelyPositive_positive Γ.pre.completelyPositive hA)
  rw [Γ.pre.tracePreserving, htrace, mul_one] at h
  change (1 : ℂ) - (δ : ℂ) ≤
    (Γ.post.map (amplifyLeftMap (krausMap K) R (Γ.pre.map A))).trace
  rw [Γ.post.tracePreserving]
  exact h

end QuantumProver.SuperchannelDiscrimination.CPWrappers

namespace QuantumProver.SuperchannelDiscrimination.TensorEntropy

open FlaggedStates
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker Matrix

variable {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]

def diagonalHom : (n → ℂ) →⋆ₐ[ℝ] Matrix n n ℂ :=
  { Matrix.diagonalAlgHom (n := n) (α := ℂ) ℝ with
    map_star' d := by
      change Matrix.diagonal (star d) = star (Matrix.diagonal d)
      rw [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]
      }

theorem diagonalHom_apply (d : n → ℂ) : diagonalHom d = Matrix.diagonal d := rfl

theorem cfc_diagonal_real (f : ℝ → ℝ) (d : n → ℝ) :
    cfc f (Matrix.diagonal (fun i => (d i : ℂ))) =
      Matrix.diagonal (fun i => (f (d i) : ℂ)) := by
  letI : IsometricContinuousFunctionalCalculus ℝ (n → ℂ) IsSelfAdjoint :=
    IsSelfAdjoint.instIsometricContinuousFunctionalCalculus
  let a : n → ℂ := fun i => (d i : ℂ)
  have ha : IsSelfAdjoint a := by ext i; simp [a, IsSelfAdjoint]
  have hdiag : (Matrix.diagonal a).IsHermitian := by
    simp [Matrix.IsHermitian, Matrix.diagonal_conjTranspose, a]
  have hf : ContinuousOn f (spectrum ℝ a) := by
    apply Set.Finite.continuousOn
    rw [Pi.spectrum_eq]
    apply Set.finite_iUnion
    intro i
    exact (Set.finite_singleton (d i)).subset (CFC.spectrum_algebraMap_subset (A := ℂ) (d i))
  have hcont : Continuous (diagonalHom (n := n)) := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    simp only [diagonalHom_apply, Matrix.diagonal_apply]
    split_ifs <;> fun_prop
  have hmap := (diagonalHom (n := n)).map_cfc f a hf hcont ha hdiag
  rw [cfc_map_pi (S := ℝ) f a (by simpa only [← Pi.spectrum_eq] using hf) ha
    (fun i => by simp [a, IsSelfAdjoint])] at hmap
  have hscalar : (fun i => cfc f (a i)) = fun i => (f (d i) : ℂ) := by
    funext i
    exact cfc_algebraMap (R := ℝ) (A := ℂ) (d i) f
  rw [hscalar, diagonalHom_apply, diagonalHom_apply] at hmap
  exact hmap.symm

def unitaryKronecker (U : Matrix.unitaryGroup n ℂ) (V : Matrix.unitaryGroup m ℂ) :
    Matrix.unitaryGroup (n × m) ℂ :=
  ⟨(U : Matrix n n ℂ) ⊗ₖ (V : Matrix m m ℂ), by
    apply Matrix.mem_unitaryGroup_iff.mpr
    rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_kronecker,
      ← Matrix.mul_kronecker_mul]
    have hU : (U : Matrix n n ℂ) * (U : Matrix n n ℂ)ᴴ = 1 :=
      Unitary.mul_star_self_of_mem U.prop
    have hV : (V : Matrix m m ℂ) * (V : Matrix m m ℂ)ᴴ = 1 :=
      Unitary.mul_star_self_of_mem V.prop
    rw [hU, hV, Matrix.one_kronecker_one]⟩

set_option maxHeartbeats 800000 in
theorem unitaryKronecker_conjugate (U : Matrix.unitaryGroup n ℂ)
    (V : Matrix.unitaryGroup m ℂ) (A : Matrix n n ℂ) (B : Matrix m m ℂ) :
    Unitary.conjStarAlgAut ℝ (Matrix (n × m) (n × m) ℂ) (unitaryKronecker U V) (A ⊗ₖ B) =
      (Unitary.conjStarAlgAut ℝ (Matrix n n ℂ) U A) ⊗ₖ
        (Unitary.conjStarAlgAut ℝ (Matrix m m ℂ) V B) := by
  change ((U : Matrix n n ℂ) ⊗ₖ (V : Matrix m m ℂ)) * (A ⊗ₖ B) *
    ((U : Matrix n n ℂ) ⊗ₖ (V : Matrix m m ℂ))ᴴ =
      ((U : Matrix n n ℂ) * A * (U : Matrix n n ℂ)ᴴ) ⊗ₖ
        ((V : Matrix m m ℂ) * B * (V : Matrix m m ℂ)ᴴ)
  rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
    ← Matrix.mul_kronecker_mul]

theorem cfc_unitary_conjugate (f : ℝ → ℝ) (U : Matrix.unitaryGroup n ℂ)
    {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    cfc f (Unitary.conjStarAlgAut ℝ _ U A) =
      Unitary.conjStarAlgAut ℝ _ U (cfc f A) := by
  have hout : IsSelfAdjoint (Unitary.conjStarAlgAut ℝ _ U A) := by
    change star (Unitary.conjStarAlgAut ℝ _ U A) = Unitary.conjStarAlgAut ℝ _ U A
    rw [← map_star]
    exact congrArg (Unitary.conjStarAlgAut ℝ _ U) hA
  exact (StarAlgHomClass.map_cfc (Unitary.conjStarAlgAut ℝ _ U) f A
    (A.finite_real_spectrum.continuousOn _) (by
      change Continuous (fun X : Matrix n n ℂ =>
        (U : Matrix n n ℂ) * X * (U : Matrix n n ℂ)ᴴ)
      fun_prop) hA hout).symm

set_option maxHeartbeats 800000 in

theorem cfc_kronecker_spectral (f : ℝ → ℝ) {A : Matrix n n ℂ} {B : Matrix m m ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    cfc f (A ⊗ₖ B) =
      Unitary.conjStarAlgAut ℝ (Matrix (n × m) (n × m) ℂ)
        (unitaryKronecker hA.eigenvectorUnitary hB.eigenvectorUnitary)
        (Matrix.diagonal (fun x : n × m =>
          (f (hA.eigenvalues x.1 * hB.eigenvalues x.2) : ℂ))) := by
  have hd : Matrix.diagonal (fun i => (hA.eigenvalues i : ℂ)) ⊗ₖ
      Matrix.diagonal (fun j => (hB.eigenvalues j : ℂ)) =
      Matrix.diagonal (fun x : n × m => ((hA.eigenvalues x.1 * hB.eigenvalues x.2 : ℝ) : ℂ)) := by
    rw [Matrix.diagonal_kronecker_diagonal]
    simp only [Complex.ofReal_mul]
  have heq : A ⊗ₖ B =
      Unitary.conjStarAlgAut ℝ (Matrix (n × m) (n × m) ℂ)
        (unitaryKronecker hA.eigenvectorUnitary hB.eigenvectorUnitary)
        (Matrix.diagonal (fun x : n × m => ((hA.eigenvalues x.1 * hB.eigenvalues x.2 : ℝ) : ℂ))) := by
    rw [← hd, unitaryKronecker_conjugate]
    exact congrArg₂ Matrix.kronecker hA.spectral_theorem hB.spectral_theorem
  have hdiag : (Matrix.diagonal (fun x : n × m =>
      ((hA.eigenvalues x.1 * hB.eigenvalues x.2 : ℝ) : ℂ))).IsHermitian := by
    simp [Matrix.IsHermitian, Matrix.diagonal_conjTranspose]
  rw [heq, cfc_unitary_conjugate f _ hdiag, cfc_diagonal_real]

theorem cfc_spectral (f : ℝ → ℝ) {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    cfc f A = Unitary.conjStarAlgAut ℝ (Matrix n n ℂ) hA.eigenvectorUnitary
      (Matrix.diagonal (fun i => (f (hA.eigenvalues i) : ℂ))) :=
  hA.cfc_eq f

set_option maxHeartbeats 800000 in

theorem cfc_mul_log_kronecker {A : Matrix n n ℂ} {B : Matrix m m ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    cfc (fun x : ℝ => x * Real.log x) (A ⊗ₖ B) =
      cfc (fun x : ℝ => x * Real.log x) A ⊗ₖ B +
        A ⊗ₖ cfc (fun x : ℝ => x * Real.log x) B := by
  let f : ℝ → ℝ := fun x => x * Real.log x
  have hd : Matrix.diagonal (fun x : n × m =>
      (f (hA.eigenvalues x.1 * hB.eigenvalues x.2) : ℂ)) =
      Matrix.diagonal (fun i => (f (hA.eigenvalues i) : ℂ)) ⊗ₖ
        Matrix.diagonal (fun j => (hB.eigenvalues j : ℂ)) +
      Matrix.diagonal (fun i => (hA.eigenvalues i : ℂ)) ⊗ₖ
        Matrix.diagonal (fun j => (f (hB.eigenvalues j) : ℂ)) := by
    rw [Matrix.diagonal_kronecker_diagonal, Matrix.diagonal_kronecker_diagonal,
      Matrix.diagonal_add]
    congr 1
    funext x
    have hs : f (hA.eigenvalues x.1 * hB.eigenvalues x.2) =
        f (hA.eigenvalues x.1) * hB.eigenvalues x.2 +
          hA.eigenvalues x.1 * f (hB.eigenvalues x.2) := by
      dsimp [f]
      rw [weighted_mul_log]
      ring
    exact_mod_cast hs
  calc
    cfc f (A ⊗ₖ B) =
        Unitary.conjStarAlgAut ℝ (Matrix (n × m) (n × m) ℂ)
          (unitaryKronecker hA.eigenvectorUnitary hB.eigenvectorUnitary)
          (Matrix.diagonal (fun x : n × m =>
            (f (hA.eigenvalues x.1 * hB.eigenvalues x.2) : ℂ))) :=
      cfc_kronecker_spectral f hA hB
    _ = cfc f A ⊗ₖ B + A ⊗ₖ cfc f B := by
      rw [hd, map_add, unitaryKronecker_conjugate, unitaryKronecker_conjugate]
      exact congrArg₂ HAdd.hAdd
        (congrArg₂ Matrix.kronecker (cfc_spectral f hA).symm hB.spectral_theorem.symm)
        (congrArg₂ Matrix.kronecker hA.spectral_theorem.symm (cfc_spectral f hB).symm)

set_option maxHeartbeats 800000 in

theorem cfc_log_kronecker {A : Matrix n n ℂ} {B : Matrix m m ℂ}
    (hA : A.PosDef) (hB : B.PosDef) :
    cfc Real.log (A ⊗ₖ B) =
      cfc Real.log A ⊗ₖ (1 : Matrix m m ℂ) +
        (1 : Matrix n n ℂ) ⊗ₖ cfc Real.log B := by
  have hd : Matrix.diagonal (fun x : n × m =>
      (Real.log (hA.1.eigenvalues x.1 * hB.1.eigenvalues x.2) : ℂ)) =
      Matrix.diagonal (fun i => (Real.log (hA.1.eigenvalues i) : ℂ)) ⊗ₖ
        (1 : Matrix m m ℂ) + (1 : Matrix n n ℂ) ⊗ₖ
        Matrix.diagonal (fun j => (Real.log (hB.1.eigenvalues j) : ℂ)) := by
    have hn : (1 : Matrix n n ℂ) = Matrix.diagonal (fun _ => 1) := Matrix.diagonal_one.symm
    have hm : (1 : Matrix m m ℂ) = Matrix.diagonal (fun _ => 1) := Matrix.diagonal_one.symm
    rw [hn, hm, Matrix.diagonal_kronecker_diagonal,
      Matrix.diagonal_kronecker_diagonal, Matrix.diagonal_add]
    congr 1
    funext x
    simp only [mul_one, one_mul]
    rw [Real.log_mul (ne_of_gt (hA.eigenvalues_pos x.1))
      (ne_of_gt (hB.eigenvalues_pos x.2)), Complex.ofReal_add]
  calc
    cfc Real.log (A ⊗ₖ B) =
        Unitary.conjStarAlgAut ℝ (Matrix (n × m) (n × m) ℂ)
          (unitaryKronecker hA.1.eigenvectorUnitary hB.1.eigenvectorUnitary)
          (Matrix.diagonal (fun x : n × m =>
            (Real.log (hA.1.eigenvalues x.1 * hB.1.eigenvalues x.2) : ℂ))) :=
      cfc_kronecker_spectral Real.log hA.1 hB.1
    _ = cfc Real.log A ⊗ₖ (1 : Matrix m m ℂ) +
        (1 : Matrix n n ℂ) ⊗ₖ cfc Real.log B := by
      rw [hd, map_add, unitaryKronecker_conjugate, unitaryKronecker_conjugate,
        map_one, map_one]
      exact congrArg₂ HAdd.hAdd
        (congrArg₂ Matrix.kronecker (cfc_spectral Real.log hA.1).symm rfl)
        (congrArg₂ Matrix.kronecker rfl (cfc_spectral Real.log hB.1).symm)

theorem isDensity_kronecker {A : Matrix n n ℂ} {B : Matrix m m ℂ}
    (hA : IsDensity A) (hB : IsDensity B) : IsDensity (A ⊗ₖ B) := by
  refine ⟨hA.1.kronecker hB.1, ?_⟩
  rw [Matrix.trace_kronecker, hA.2, hB.2, mul_one]

theorem entropyBits_kronecker {A : Matrix n n ℂ} {B : Matrix m m ℂ}
    (hA : IsDensity A) (hB : IsDensity B) :
    entropyBits (A ⊗ₖ B) = entropyBits A + entropyBits B := by
  simp only [entropyBits, cfc_mul_log_kronecker hA.1.1 hB.1.1,
    Matrix.trace_add, Matrix.trace_kronecker, hA.2, hB.2,
    mul_one, one_mul, Complex.add_re]
  ring

theorem finiteRelativeEntropyBits_kronecker {A B : Matrix n n ℂ} {C D : Matrix m m ℂ}
    (hA : IsDensity A) (hB : B.PosDef) (hC : IsDensity C) (hD : D.PosDef) :
    finiteRelativeEntropyBits (A ⊗ₖ C) (B ⊗ₖ D) =
      finiteRelativeEntropyBits A B + finiteRelativeEntropyBits C D := by
  have hprod : (A ⊗ₖ C) *
      (cfc Real.log B ⊗ₖ (1 : Matrix m m ℂ) +
        (1 : Matrix n n ℂ) ⊗ₖ cfc Real.log D) =
      (A * cfc Real.log B) ⊗ₖ C + A ⊗ₖ (C * cfc Real.log D) := by
    rw [Matrix.mul_add, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
      Matrix.mul_one, Matrix.mul_one]
  rw [finiteRelativeEntropyBits_eq_spectral (hA.1.kronecker hC.1).1,
    finiteRelativeEntropyBits_eq_spectral hA.1.1,
    finiteRelativeEntropyBits_eq_spectral hC.1.1,
    cfc_mul_log_kronecker hA.1.1 hC.1.1, cfc_log_kronecker hB hD, hprod]
  simp only [Matrix.trace_add, Matrix.trace_kronecker, hA.2, hC.2,
    mul_one, one_mul, Complex.add_re]
  ring

theorem hasSupportIn_kronecker_of_posDef {A : Matrix n n ℂ} {C : Matrix m m ℂ}
    {B : Matrix n n ℂ} {D : Matrix m m ℂ} (hB : B.PosDef) (hD : D.PosDef) :
    HasSupportIn (A ⊗ₖ C) (B ⊗ₖ D) :=
  hasSupportIn_of_posDef _ (hB.kronecker hD)

theorem relativeEntropyBits_kronecker_of_posDef
    {A B : Matrix n n ℂ} {C D : Matrix m m ℂ}
    (hA : IsDensity A) (hB : B.PosDef) (hC : IsDensity C) (hD : D.PosDef) :
    relativeEntropyBits (A ⊗ₖ C) (B ⊗ₖ D) =
      relativeEntropyBits A B + relativeEntropyBits C D := by
  rw [relativeEntropyBits_of_posDef _ (hB.kronecker hD),
    relativeEntropyBits_of_posDef _ hB, relativeEntropyBits_of_posDef _ hD,
    finiteRelativeEntropyBits_kronecker hA hB hC hD, EReal.coe_add]

universe u

def TensorIndex (ι : Type u) : ℕ → Type u
  | 0 => PUnit
  | k + 1 => TensorIndex ι k × ι

instance tensorIndexFintype (ι : Type u) [Fintype ι] (k : ℕ) :
    Fintype (TensorIndex ι k) := by
  induction k with
  | zero => exact inferInstanceAs (Fintype PUnit)
  | succ k ih =>
      letI : Fintype (TensorIndex ι k) := ih
      exact inferInstanceAs (Fintype (TensorIndex ι k × ι))

instance tensorIndexDecidableEq (ι : Type u) [DecidableEq ι] (k : ℕ) :
    DecidableEq (TensorIndex ι k) := by
  induction k with
  | zero => exact inferInstanceAs (DecidableEq PUnit)
  | succ k ih =>
      letI : DecidableEq (TensorIndex ι k) := ih
      exact inferInstanceAs (DecidableEq (TensorIndex ι k × ι))

def tensorPower (A : Matrix n n ℂ) : (k : ℕ) →
    Matrix (TensorIndex n k) (TensorIndex n k) ℂ
  | 0 => 1
  | k + 1 => tensorPower A k ⊗ₖ A

theorem tensorPower_isDensity {A : Matrix n n ℂ} (hA : IsDensity A) (k : ℕ) :
    IsDensity (tensorPower A k) := by
  induction k with
  | zero =>
      refine ⟨Matrix.PosSemidef.one, ?_⟩
      change (1 : Matrix PUnit PUnit ℂ).trace = 1
      simp [Matrix.trace, Matrix.diag, Matrix.one_apply]
  | succ k ih => exact isDensity_kronecker ih hA

theorem tensorPower_posDef {B : Matrix n n ℂ} (hB : B.PosDef) (k : ℕ) :
    (tensorPower B k).PosDef := by
  induction k with
  | zero => exact Matrix.PosDef.one
  | succ k ih => exact ih.kronecker hB

theorem tensorPower_hasSupportIn {A B : Matrix n n ℂ} (hB : B.PosDef) (k : ℕ) :
    HasSupportIn (tensorPower A k) (tensorPower B k) :=
  hasSupportIn_of_posDef _ (tensorPower_posDef hB k)

theorem entropyBits_tensorPower {A : Matrix n n ℂ} (hA : IsDensity A) (k : ℕ) :
    entropyBits (tensorPower A k) = (k : ℝ) * entropyBits A := by
  induction k with
  | zero => simp [tensorPower, entropyBits, cfc_one]
  | succ k ih =>
      change entropyBits (tensorPower A k ⊗ₖ A) = ((k + 1 : ℕ) : ℝ) * entropyBits A
      rw [entropyBits_kronecker (tensorPower_isDensity hA k) hA, ih]
      push_cast
      ring

theorem finiteRelativeEntropyBits_tensorPower {A B : Matrix n n ℂ}
    (hA : IsDensity A) (hB : B.PosDef) (k : ℕ) :
    finiteRelativeEntropyBits (tensorPower A k) (tensorPower B k) =
      (k : ℝ) * finiteRelativeEntropyBits A B := by
  induction k with
  | zero => simp [tensorPower, finiteRelativeEntropyBits]
  | succ k ih =>
      change finiteRelativeEntropyBits (tensorPower A k ⊗ₖ A) (tensorPower B k ⊗ₖ B) =
        ((k + 1 : ℕ) : ℝ) * finiteRelativeEntropyBits A B
      rw [finiteRelativeEntropyBits_kronecker (tensorPower_isDensity hA k)
        (tensorPower_posDef hB k) hA hB, ih]
      push_cast
      ring

theorem relativeEntropyBits_tensorPower {A B : Matrix n n ℂ}
    (hA : IsDensity A) (hB : B.PosDef) (k : ℕ) :
    relativeEntropyBits (tensorPower A k) (tensorPower B k) =
      (k : EReal) * relativeEntropyBits A B := by
  rw [relativeEntropyBits_of_posDef _ (tensorPower_posDef hB k),
    relativeEntropyBits_of_posDef _ hB, finiteRelativeEntropyBits_tensorPower hA hB k,
    EReal.coe_mul, EReal.coe_natCast]

theorem iid_density_relativeEntropy {A B : Matrix n n ℂ}
    (hA : IsDensity A) (hB : IsDensity B) (hBdef : B.PosDef) (k : ℕ) :
    IsDensity (tensorPower A k) ∧ IsDensity (tensorPower B k) ∧
      (tensorPower B k).PosDef ∧ HasSupportIn (tensorPower A k) (tensorPower B k) ∧
      relativeEntropyBits (tensorPower A k) (tensorPower B k) =
        (k : EReal) * relativeEntropyBits A B :=
  ⟨tensorPower_isDensity hA k, tensorPower_isDensity hB k,
    tensorPower_posDef hBdef k, tensorPower_hasSupportIn hBdef k,
    relativeEntropyBits_tensorPower hA hBdef k⟩

theorem tensorIndex_card (ι : Type u) [Fintype ι] (k : ℕ) :
    Fintype.card (TensorIndex ι k) = Fintype.card ι ^ k := by
  induction k with
  | zero =>
      change Fintype.card PUnit = 1
      exact Fintype.card_punit
  | succ k ih =>
      change Fintype.card (TensorIndex ι k × ι) = Fintype.card ι ^ (k + 1)
      rw [Fintype.card_prod, ih, pow_succ]

theorem tensor_density_relativeEntropy {A B : Matrix n n ℂ} {C D : Matrix m m ℂ}
    (hA : IsDensity A) (hB : IsDensity B) (hBdef : B.PosDef)
    (hC : IsDensity C) (hD : IsDensity D) (hDdef : D.PosDef) :
    IsDensity (A ⊗ₖ C) ∧ IsDensity (B ⊗ₖ D) ∧ (B ⊗ₖ D).PosDef ∧
      HasSupportIn (A ⊗ₖ C) (B ⊗ₖ D) ∧
      relativeEntropyBits (A ⊗ₖ C) (B ⊗ₖ D) =
        relativeEntropyBits A B + relativeEntropyBits C D :=
  ⟨isDensity_kronecker hA hC, isDensity_kronecker hB hD, hBdef.kronecker hDdef,
    hasSupportIn_kronecker_of_posDef hBdef hDdef,
    relativeEntropyBits_kronecker_of_posDef hA hBdef hC hDdef⟩

def nonzeroWeight (x : ℝ) : ℝ := if x = 0 then 0 else 1

def supportProjection (B : Matrix n n ℂ) : Matrix n n ℂ := cfc nonzeroWeight B

theorem supportProjection_mul (B : Matrix n n ℂ) (hB : B.IsHermitian) :
    B * supportProjection B = B := by
  have hf : (fun x : ℝ => x * nonzeroWeight x) = (fun x : ℝ => x) := by
    funext x
    by_cases hx : x = 0 <;> simp [nonzeroWeight, hx]
  calc
    B * supportProjection B = cfc (fun x : ℝ => x) B * cfc nonzeroWeight B := by
      exact congrArg (fun M : Matrix n n ℂ => M * cfc nonzeroWeight B)
        (cfc_id' (p := IsSelfAdjoint) ℝ B hB).symm
    _ = cfc (fun x : ℝ => x * nonzeroWeight x) B :=
      (cfc_mul (p := IsSelfAdjoint) _ _ B (B.finite_real_spectrum.continuousOn _)
        (B.finite_real_spectrum.continuousOn _)).symm
    _ = B := by rw [hf, cfc_id' (p := IsSelfAdjoint) ℝ B hB]

theorem supportProjection_eq_inverse_mul (B : Matrix n n ℂ) (hB : B.IsHermitian) :
    supportProjection B = cfc (fun x : ℝ => x⁻¹) B * B := by
  have hf : nonzeroWeight = (fun x : ℝ => x⁻¹ * x) := by
    funext x
    by_cases hx : x = 0 <;> simp [nonzeroWeight, hx]
  unfold supportProjection
  rw [hf, cfc_mul (p := IsSelfAdjoint) _ _ B
    (B.finite_real_spectrum.continuousOn _) (B.finite_real_spectrum.continuousOn _),
    cfc_id' (p := IsSelfAdjoint) ℝ B hB]

theorem hasSupportIn_iff_mul_supportProjection {A B : Matrix n n ℂ}
    (hB : B.IsHermitian) : HasSupportIn A B ↔ A * supportProjection B = A := by
  constructor
  · intro hab
    have hBQ : B * (1 - supportProjection B) = 0 := by
      rw [Matrix.mul_sub, Matrix.mul_one, supportProjection_mul B hB, sub_self]
    have hAQ : A * (1 - supportProjection B) = 0 := by
      ext i j
      have hcol : B *ᵥ (fun k => (1 - supportProjection B) k j) = 0 := by
        exact funext fun k => congrArg (fun M : Matrix n n ℂ => M k j) hBQ
      exact congrFun (hab _ hcol) i
    rw [Matrix.mul_sub, Matrix.mul_one] at hAQ
    exact (sub_eq_zero.mp hAQ).symm
  · intro hAP v hv
    have hPv : supportProjection B *ᵥ v = 0 := by
      rw [supportProjection_eq_inverse_mul B hB, ← Matrix.mulVec_mulVec, hv,
        Matrix.mulVec_zero]
    rw [← hAP, ← Matrix.mulVec_mulVec, hPv, Matrix.mulVec_zero]

set_option maxHeartbeats 800000 in
theorem supportProjection_kronecker {B : Matrix n n ℂ} {D : Matrix m m ℂ}
    (hB : B.IsHermitian) (hD : D.IsHermitian) :
    supportProjection (B ⊗ₖ D) = supportProjection B ⊗ₖ supportProjection D := by
  have hd : Matrix.diagonal (fun x : n × m =>
      (nonzeroWeight (hB.eigenvalues x.1 * hD.eigenvalues x.2) : ℂ)) =
      Matrix.diagonal (fun i => (nonzeroWeight (hB.eigenvalues i) : ℂ)) ⊗ₖ
        Matrix.diagonal (fun j => (nonzeroWeight (hD.eigenvalues j) : ℂ)) := by
    rw [Matrix.diagonal_kronecker_diagonal]
    congr 1
    funext x
    have hs : nonzeroWeight (hB.eigenvalues x.1 * hD.eigenvalues x.2) =
        nonzeroWeight (hB.eigenvalues x.1) * nonzeroWeight (hD.eigenvalues x.2) := by
      by_cases hb : hB.eigenvalues x.1 = 0 <;>
        by_cases hd : hD.eigenvalues x.2 = 0 <;>
          simp [nonzeroWeight, hb, hd, mul_ne_zero]
    exact_mod_cast hs
  unfold supportProjection
  rw [cfc_kronecker_spectral nonzeroWeight hB hD, hd, unitaryKronecker_conjugate]
  exact congrArg₂ Matrix.kronecker
    (cfc_spectral nonzeroWeight hB).symm (cfc_spectral nonzeroWeight hD).symm

set_option maxHeartbeats 800000 in

theorem cfc_log_kronecker_support {B : Matrix n n ℂ} {D : Matrix m m ℂ}
    (hB : B.IsHermitian) (hD : D.IsHermitian) :
    cfc Real.log (B ⊗ₖ D) =
      cfc Real.log B ⊗ₖ supportProjection D +
        supportProjection B ⊗ₖ cfc Real.log D := by
  have hd : Matrix.diagonal (fun x : n × m =>
      (Real.log (hB.eigenvalues x.1 * hD.eigenvalues x.2) : ℂ)) =
      Matrix.diagonal (fun i => (Real.log (hB.eigenvalues i) : ℂ)) ⊗ₖ
        Matrix.diagonal (fun j => (nonzeroWeight (hD.eigenvalues j) : ℂ)) +
      Matrix.diagonal (fun i => (nonzeroWeight (hB.eigenvalues i) : ℂ)) ⊗ₖ
        Matrix.diagonal (fun j => (Real.log (hD.eigenvalues j) : ℂ)) := by
    rw [Matrix.diagonal_kronecker_diagonal, Matrix.diagonal_kronecker_diagonal,
      Matrix.diagonal_add]
    congr 1
    funext x
    have hs : Real.log (hB.eigenvalues x.1 * hD.eigenvalues x.2) =
        Real.log (hB.eigenvalues x.1) * nonzeroWeight (hD.eigenvalues x.2) +
          nonzeroWeight (hB.eigenvalues x.1) * Real.log (hD.eigenvalues x.2) := by
      by_cases hb : hB.eigenvalues x.1 = 0
      · simp [nonzeroWeight, hb]
      by_cases hd : hD.eigenvalues x.2 = 0
      · simp [nonzeroWeight, hd]
      simp only [nonzeroWeight, if_neg hb, if_neg hd, mul_one, one_mul]
      exact Real.log_mul hb hd
    exact_mod_cast hs
  rw [cfc_kronecker_spectral Real.log hB hD, hd, map_add,
    unitaryKronecker_conjugate, unitaryKronecker_conjugate]
  exact congrArg₂ HAdd.hAdd
    (congrArg₂ Matrix.kronecker (cfc_spectral Real.log hB).symm
      (cfc_spectral nonzeroWeight hD).symm)
    (congrArg₂ Matrix.kronecker (cfc_spectral nonzeroWeight hB).symm
      (cfc_spectral Real.log hD).symm)

theorem finiteRelativeEntropyBits_kronecker_of_support
    {A B : Matrix n n ℂ} {C D : Matrix m m ℂ}
    (hA : IsDensity A) (hB : B.IsHermitian) (hC : IsDensity C) (hD : D.IsHermitian)
    (hab : HasSupportIn A B) (hcd : HasSupportIn C D) :
    finiteRelativeEntropyBits (A ⊗ₖ C) (B ⊗ₖ D) =
      finiteRelativeEntropyBits A B + finiteRelativeEntropyBits C D := by
  have hAP := (hasSupportIn_iff_mul_supportProjection hB).mp hab
  have hCP := (hasSupportIn_iff_mul_supportProjection hD).mp hcd
  have hprod : (A ⊗ₖ C) *
      (cfc Real.log B ⊗ₖ supportProjection D +
        supportProjection B ⊗ₖ cfc Real.log D) =
      (A * cfc Real.log B) ⊗ₖ C + A ⊗ₖ (C * cfc Real.log D) := by
    rw [Matrix.mul_add, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, hAP, hCP]
  rw [finiteRelativeEntropyBits_eq_spectral (hA.1.kronecker hC.1).1,
    finiteRelativeEntropyBits_eq_spectral hA.1.1,
    finiteRelativeEntropyBits_eq_spectral hC.1.1,
    cfc_mul_log_kronecker hA.1.1 hC.1.1, cfc_log_kronecker_support hB hD, hprod]
  simp only [Matrix.trace_add, Matrix.trace_kronecker, hA.2, hC.2,
    mul_one, one_mul, Complex.add_re]
  ring

def vectorKronecker (v : n → ℂ) (w : m → ℂ) : n × m → ℂ :=
  fun x => v x.1 * w x.2

theorem kronecker_mulVec (A : Matrix n n ℂ) (B : Matrix m m ℂ)
    (v : n → ℂ) (w : m → ℂ) :
    (A ⊗ₖ B) *ᵥ vectorKronecker v w = vectorKronecker (A *ᵥ v) (B *ᵥ w) := by
  ext ⟨i, j⟩
  simp only [Matrix.mulVec, dotProduct, vectorKronecker, Matrix.kronecker_apply,
    Fintype.sum_prod_type, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  ring

theorem exists_diag_ne_zero {A : Matrix n n ℂ} (htrace : A.trace = 1) :
    ∃ i, A i i ≠ 0 := by
  by_contra! h
  have hz : A.trace = 0 := by simp [Matrix.trace, Matrix.diag, h]
  rw [htrace] at hz
  exact one_ne_zero hz

theorem isHermitian_kronecker {B : Matrix n n ℂ} {D : Matrix m m ℂ}
    (hB : B.IsHermitian) (hD : D.IsHermitian) : (B ⊗ₖ D).IsHermitian := by
  change (B ⊗ₖ D)ᴴ = B ⊗ₖ D
  rw [Matrix.conjTranspose_kronecker, hB.eq, hD.eq]

theorem hasSupportIn_kronecker_iff {A B : Matrix n n ℂ} {C D : Matrix m m ℂ}
    (hAtrace : A.trace = 1) (hCtrace : C.trace = 1)
    (hB : B.IsHermitian) (hD : D.IsHermitian) :
    HasSupportIn (A ⊗ₖ C) (B ⊗ₖ D) ↔ HasSupportIn A B ∧ HasSupportIn C D := by
  constructor
  · intro ht
    constructor
    · intro v hv
      obtain ⟨j, hj⟩ := exists_diag_ne_zero hCtrace
      have hker : (B ⊗ₖ D) *ᵥ vectorKronecker v (Pi.single j 1) = 0 := by
        rw [kronecker_mulVec]
        ext x
        simp [vectorKronecker, hv]
      have hz := ht _ hker
      rw [kronecker_mulVec] at hz
      ext i
      have hi : (A *ᵥ v) i * C j j = 0 := by
        simpa [vectorKronecker, Matrix.mulVec_single_one] using congrFun hz (i, j)
      exact (mul_eq_zero.mp hi).resolve_right hj
    · intro w hw
      obtain ⟨i, hi⟩ := exists_diag_ne_zero hAtrace
      have hker : (B ⊗ₖ D) *ᵥ vectorKronecker (Pi.single i 1) w = 0 := by
        rw [kronecker_mulVec]
        ext x
        simp [vectorKronecker, hw]
      have hz := ht _ hker
      rw [kronecker_mulVec] at hz
      ext j
      have hj : A i i * (C *ᵥ w) j = 0 := by
        simpa [vectorKronecker, Matrix.mulVec_single_one] using congrFun hz (i, j)
      exact (mul_eq_zero.mp hj).resolve_left hi
  · rintro ⟨hab, hcd⟩
    apply (hasSupportIn_iff_mul_supportProjection (isHermitian_kronecker hB hD)).mpr
    rw [supportProjection_kronecker hB hD, ← Matrix.mul_kronecker_mul,
      (hasSupportIn_iff_mul_supportProjection hB).mp hab,
      (hasSupportIn_iff_mul_supportProjection hD).mp hcd]

theorem relativeEntropyBits_kronecker {A B : Matrix n n ℂ} {C D : Matrix m m ℂ}
    (hA : IsDensity A) (hB : B.PosSemidef) (hC : IsDensity C) (hD : D.PosSemidef) :
    relativeEntropyBits (A ⊗ₖ C) (B ⊗ₖ D) =
      relativeEntropyBits A B + relativeEntropyBits C D := by
  have hs := hasSupportIn_kronecker_iff hA.2 hC.2 hB.1 hD.1
  by_cases hab : HasSupportIn A B <;> by_cases hcd : HasSupportIn C D
  · simp [relativeEntropyBits, hs, hab, hcd,
      finiteRelativeEntropyBits_kronecker_of_support hA hB.1 hC hD.1 hab hcd,
      EReal.coe_add]
  all_goals simp [relativeEntropyBits, hs, hab, hcd]

theorem tensorPower_posSemidef {B : Matrix n n ℂ} (hB : B.PosSemidef) (k : ℕ) :
    (tensorPower B k).PosSemidef := by
  induction k with
  | zero => exact Matrix.PosSemidef.one
  | succ k ih => exact ih.kronecker hB

theorem relativeEntropyBits_tensorPower_general {A B : Matrix n n ℂ}
    (hA : IsDensity A) (hB : B.PosSemidef) (k : ℕ) :
    relativeEntropyBits (tensorPower A k) (tensorPower B k) =
      (k : EReal) * relativeEntropyBits A B := by
  induction k with
  | zero =>
      rw [relativeEntropyBits_of_posDef _ (show (tensorPower B 0).PosDef from
        Matrix.PosDef.one)]
      simp [tensorPower, finiteRelativeEntropyBits]
  | succ k ih =>
      change relativeEntropyBits (tensorPower A k ⊗ₖ A) (tensorPower B k ⊗ₖ B) =
        ((k + 1 : ℕ) : EReal) * relativeEntropyBits A B
      rw [relativeEntropyBits_kronecker (tensorPower_isDensity hA k)
        (tensorPower_posSemidef hB k) hA hB, ih, Nat.cast_succ,
        EReal.right_distrib_of_nonneg (by positivity) (by positivity), one_mul]

theorem iid_density_relativeEntropy_general {A B : Matrix n n ℂ}
    (hA : IsDensity A) (hB : IsDensity B) (k : ℕ) :
    IsDensity (tensorPower A k) ∧ IsDensity (tensorPower B k) ∧
      relativeEntropyBits (tensorPower A k) (tensorPower B k) =
        (k : EReal) * relativeEntropyBits A B :=
  ⟨tensorPower_isDensity hA k, tensorPower_isDensity hB k,
    relativeEntropyBits_tensorPower_general hA hB.1 k⟩

theorem hasSupportIn_tensorPower_iff {A B : Matrix n n ℂ}
    (hA : IsDensity A) (hB : B.PosSemidef) (k : ℕ) :
    HasSupportIn (tensorPower A k) (tensorPower B k) ↔
      k = 0 ∨ HasSupportIn A B := by
  induction k with
  | zero =>
      have hs : HasSupportIn (tensorPower A 0) (tensorPower B 0) :=
        hasSupportIn_of_posDef _ Matrix.PosDef.one
      simp [hs]
  | succ k ih =>
      change HasSupportIn (tensorPower A k ⊗ₖ A) (tensorPower B k ⊗ₖ B) ↔
        k + 1 = 0 ∨ HasSupportIn A B
      rw [hasSupportIn_kronecker_iff (tensorPower_isDensity hA k).2 hA.2
        (tensorPower_posSemidef hB k).1 hB.1, ih]
      simp only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, false_or]
      tauto

theorem tensor_density_relativeEntropy_general {A B : Matrix n n ℂ}
    {C D : Matrix m m ℂ} (hA : IsDensity A) (hB : IsDensity B)
    (hC : IsDensity C) (hD : IsDensity D) :
    IsDensity (A ⊗ₖ C) ∧ IsDensity (B ⊗ₖ D) ∧
      (HasSupportIn (A ⊗ₖ C) (B ⊗ₖ D) ↔ HasSupportIn A B ∧ HasSupportIn C D) ∧
      relativeEntropyBits (A ⊗ₖ C) (B ⊗ₖ D) =
        relativeEntropyBits A B + relativeEntropyBits C D :=
  ⟨isDensity_kronecker hA hC, isDensity_kronecker hB hD,
    hasSupportIn_kronecker_iff hA.2 hC.2 hB.1.1 hD.1.1,
    relativeEntropyBits_kronecker hA hB.1 hC hD.1⟩

theorem iid_density_support_relativeEntropy_general {A B : Matrix n n ℂ}
    (hA : IsDensity A) (hB : IsDensity B) (k : ℕ) :
    IsDensity (tensorPower A k) ∧ IsDensity (tensorPower B k) ∧
      (HasSupportIn (tensorPower A k) (tensorPower B k) ↔ k = 0 ∨ HasSupportIn A B) ∧
      relativeEntropyBits (tensorPower A k) (tensorPower B k) =
        (k : EReal) * relativeEntropyBits A B :=
  ⟨tensorPower_isDensity hA k, tensorPower_isDensity hB k,
    hasSupportIn_tensorPower_iff hA hB.1 k, relativeEntropyBits_tensorPower_general hA hB.1 k⟩

end QuantumProver.SuperchannelDiscrimination.TensorEntropy

namespace QuantumProver.SuperchannelDiscrimination.Klein

open FlaggedStates TensorEntropy
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

def overlapWeight (U : Matrix.unitaryGroup n ℂ) (i j : n) : ℝ :=
  Complex.normSq ((U : Matrix n n ℂ) i j)

theorem overlapWeight_nonneg (U : Matrix.unitaryGroup n ℂ) (i j : n) :
    0 ≤ overlapWeight U i j := Complex.normSq_nonneg _

theorem overlapWeight_sum_row (U : Matrix.unitaryGroup n ℂ) (i : n) :
    ∑ j, overlapWeight U i j = 1 := by
  have hu : (U : Matrix n n ℂ) * (U : Matrix n n ℂ)ᴴ = 1 :=
    Unitary.coe_mul_star_self U
  have hi := congrArg (fun M : Matrix n n ℂ => (M i i).re) hu
  simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.mul_conj,
    Complex.re_sum, overlapWeight] using hi

theorem overlapWeight_sum_col (U : Matrix.unitaryGroup n ℂ) (j : n) :
    ∑ i, overlapWeight U i j = 1 := by
  have hu : (U : Matrix n n ℂ)ᴴ * (U : Matrix n n ℂ) = 1 :=
    Unitary.coe_star_mul_self U
  have hj := congrArg (fun M : Matrix n n ℂ => (M j j).re) hu
  simpa [Matrix.mul_apply, Matrix.conjTranspose_apply,
    ← Complex.normSq_eq_conj_mul_self, Complex.re_sum, overlapWeight] using hj

theorem overlap_sum_rows (U : Matrix.unitaryGroup n ℂ) (a : n → ℝ) :
    ∑ i, ∑ j, a i * overlapWeight U i j = ∑ i, a i := by
  simp_rw [← Finset.mul_sum, overlapWeight_sum_row, mul_one]

theorem overlap_sum_cols (U : Matrix.unitaryGroup n ℂ) (b : n → ℝ) :
    ∑ i, ∑ j, b j * overlapWeight U i j = ∑ j, b j := by
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, overlapWeight_sum_col, mul_one]

theorem trace_unitary_conjugate (U : Matrix.unitaryGroup n ℂ) (X : Matrix n n ℂ) :
    (Unitary.conjStarAlgAut ℝ (Matrix n n ℂ) U X).trace = X.trace := by
  change ((U : Matrix n n ℂ) * X * (U : Matrix n n ℂ)ᴴ).trace = X.trace
  rw [Matrix.trace_mul_cycle]
  have hu : (U : Matrix n n ℂ)ᴴ * (U : Matrix n n ℂ) = 1 :=
    Unitary.coe_star_mul_self U
  rw [hu, Matrix.one_mul]

theorem trace_cfc_eq_sum (f : ℝ → ℝ) {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    (cfc f A).trace.re = ∑ i, f (hA.eigenvalues i) := by
  rw [cfc_spectral f hA, trace_unitary_conjugate, Matrix.trace_diagonal]
  simp [Complex.re_sum]

theorem trace_eq_sum_eigenvalues_re {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    A.trace.re = ∑ i, hA.eigenvalues i := by
  rw [hA.trace_eq_sum_eigenvalues]
  simp [Complex.re_sum]

theorem trace_diagonal_overlap (U : Matrix.unitaryGroup n ℂ) (a b : n → ℝ) :
    (Matrix.diagonal (fun i => (a i : ℂ)) *
      Unitary.conjStarAlgAut ℝ (Matrix n n ℂ) U
        (Matrix.diagonal (fun j => (b j : ℂ)))).trace.re =
      ∑ i, ∑ j, a i * b j * overlapWeight U i j := by
  change (Matrix.diagonal (fun i => (a i : ℂ)) *
    ((U : Matrix n n ℂ) * Matrix.diagonal (fun j => (b j : ℂ)) *
      (U : Matrix n n ℂ)ᴴ)).trace.re = _
  have hentry (i : n) : (Matrix.diagonal (fun i => (a i : ℂ)) *
      ((U : Matrix n n ℂ) * Matrix.diagonal (fun j => (b j : ℂ)) *
        (U : Matrix n n ℂ)ᴴ)) i i =
      ∑ j, (a i : ℂ) * (((U : Matrix n n ℂ) i j * (b j : ℂ)) *
        starRingEnd ℂ ((U : Matrix n n ℂ) i j)) := by
    rw [Matrix.diagonal_mul, Matrix.mul_apply]
    simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply, Finset.mul_sum,
      Complex.star_def]
  simp only [Matrix.trace, Matrix.diag, hentry, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  have h : (a i : ℂ) * (((U : Matrix n n ℂ) i j * (b j : ℂ)) *
      starRingEnd ℂ ((U : Matrix n n ℂ) i j)) =
      ((a i * b j : ℝ) : ℂ) *
        ((U : Matrix n n ℂ) i j * starRingEnd ℂ ((U : Matrix n n ℂ) i j)) := by
    push_cast
    ring
  rw [h, Complex.mul_conj, Complex.re_ofReal_mul]
  rfl

def overlapUnitary {A B : Matrix n n ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian) :
    Matrix.unitaryGroup n ℂ := star hA.eigenvectorUnitary * hB.eigenvectorUnitary

theorem trace_mul_cfc_eq_overlap (f : ℝ → ℝ) {A B : Matrix n n ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (A * cfc f B).trace.re =
      ∑ i, ∑ j, hA.eigenvalues i * f (hB.eigenvalues j) *
        overlapWeight (overlapUnitary hA hB) i j := by
  have ha : A = Unitary.conjStarAlgAut ℝ (Matrix n n ℂ) hA.eigenvectorUnitary
      (Matrix.diagonal (fun i => (hA.eigenvalues i : ℂ))) := hA.spectral_theorem
  have hu : hA.eigenvectorUnitary * overlapUnitary hA hB = hB.eigenvectorUnitary := by
    simp [overlapUnitary, ← mul_assoc]
  have hp : A * cfc f B =
      Unitary.conjStarAlgAut ℝ (Matrix n n ℂ) hA.eigenvectorUnitary
        (Matrix.diagonal (fun i => (hA.eigenvalues i : ℂ)) *
          Unitary.conjStarAlgAut ℝ (Matrix n n ℂ) (overlapUnitary hA hB)
            (Matrix.diagonal (fun j => (f (hB.eigenvalues j) : ℂ)))) := by
    rw [map_mul, ← Unitary.conjStarAlgAut_mul_apply, hu,
      ← ha, ← cfc_spectral f hB]
  rw [hp, trace_unitary_conjugate, trace_diagonal_overlap]

theorem scalar_log_tangent {x y : ℝ} (hx : 0 ≤ x) (hy : 0 < y) :
    x - y ≤ x * Real.log x - x * Real.log y := by
  by_cases hx0 : x = 0
  · simp [hx0, hy.le]
  have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
  have hl := mul_le_mul_of_nonneg_left
    (Real.log_le_sub_one_of_pos (div_pos hy hxpos)) hx
  have hid : x * (y / x - 1) = y - x := by
    field_simp
  rw [Real.log_div hy.ne' hxpos.ne', hid] at hl
  nlinarith

theorem klein_trace_of_posDef {A B : Matrix n n ℂ}
    (hA : A.PosSemidef) (hB : B.PosDef) :
    A.trace.re - B.trace.re ≤
      (cfc (fun x : ℝ => x * Real.log x) A).trace.re -
        (A * cfc Real.log B).trace.re := by
  let U := overlapUnitary hA.1 hB.1
  have hpoint (i j : n) :
      (hA.1.eigenvalues i - hB.1.eigenvalues j) * overlapWeight U i j ≤
        (hA.1.eigenvalues i * Real.log (hA.1.eigenvalues i) -
          hA.1.eigenvalues i * Real.log (hB.1.eigenvalues j)) * overlapWeight U i j :=
    mul_le_mul_of_nonneg_right (scalar_log_tangent (hA.eigenvalues_nonneg i)
      (hB.eigenvalues_pos j)) (overlapWeight_nonneg U i j)
  have hs := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) =>
    Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) => hpoint i j
  simp_rw [sub_mul, Finset.sum_sub_distrib] at hs
  rw [overlap_sum_rows, overlap_sum_cols, overlap_sum_rows] at hs
  rw [trace_eq_sum_eigenvalues_re hA.1, trace_eq_sum_eigenvalues_re hB.1,
    trace_cfc_eq_sum _ hA.1, trace_mul_cfc_eq_overlap _ hA.1 hB.1]
  exact hs

theorem finiteRelativeEntropyBits_nonneg_of_posDef {A B : Matrix n n ℂ}
    (hA : IsDensity A) (hB : IsDensity B) (hBdef : B.PosDef) :
    0 ≤ finiteRelativeEntropyBits A B := by
  rw [finiteRelativeEntropyBits_eq_spectral hA.1.1]
  apply div_nonneg
  · have h := klein_trace_of_posDef hA.1 hBdef
    simpa [hA.2, hB.2] using h
  · exact le_of_lt (Real.log_pos (by norm_num))

theorem relativeEntropyBits_nonneg_of_posDef {A B : Matrix n n ℂ}
    (hA : IsDensity A) (hB : IsDensity B) (hBdef : B.PosDef) :
    0 ≤ relativeEntropyBits A B := by
  rw [relativeEntropyBits_of_posDef _ hBdef]
  exact_mod_cast finiteRelativeEntropyBits_nonneg_of_posDef hA hB hBdef

theorem support_overlap_mul_eq_zero {A B : Matrix n n ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (hab : HasSupportIn A B)
    (i j : n) (hj : hB.eigenvalues j = 0) :
    (hA.eigenvalues i : ℂ) *
      (overlapUnitary hA hB : Matrix n n ℂ) i j = 0 := by
  let U := overlapUnitary hA hB
  have hAP := (hasSupportIn_iff_mul_supportProjection hB).mp hab
  have hdiag : Unitary.conjStarAlgAut ℝ (Matrix n n ℂ)
      (star hA.eigenvectorUnitary) A =
      Matrix.diagonal (fun k => (hA.eigenvalues k : ℂ)) :=
    hA.conjStarAlgAut_star_eigenvectorUnitary
  have hx := congrArg (Unitary.conjStarAlgAut ℝ (Matrix n n ℂ)
    (star hA.eigenvectorUnitary)) hAP
  rw [map_mul, hdiag, supportProjection, cfc_spectral nonzeroWeight hB,
    ← Unitary.conjStarAlgAut_mul_apply] at hx
  change Matrix.diagonal (fun k => (hA.eigenvalues k : ℂ)) *
    Unitary.conjStarAlgAut ℝ (Matrix n n ℂ) U
      (Matrix.diagonal (fun k => (nonzeroWeight (hB.eigenvalues k) : ℂ))) =
    Matrix.diagonal (fun k => (hA.eigenvalues k : ℂ)) at hx
  have hy := congrArg (fun M : Matrix n n ℂ => M * (U : Matrix n n ℂ)) hx
  change (Matrix.diagonal (fun k => (hA.eigenvalues k : ℂ)) *
    ((U : Matrix n n ℂ) *
      Matrix.diagonal (fun k => (nonzeroWeight (hB.eigenvalues k) : ℂ)) *
      (U : Matrix n n ℂ)ᴴ)) * (U : Matrix n n ℂ) = _ at hy
  have hu : (U : Matrix n n ℂ)ᴴ * (U : Matrix n n ℂ) = 1 :=
    Unitary.coe_star_mul_self U
  simp only [Matrix.mul_assoc, hu, Matrix.mul_one] at hy
  have hij := congrArg (fun M : Matrix n n ℂ => M i j) hy
  simpa [Matrix.diagonal_mul, Matrix.mul_diagonal, nonzeroWeight, hj] using hij.symm

theorem support_overlap_weight_eq_zero {A B : Matrix n n ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (hab : HasSupportIn A B)
    (i j : n) (hj : hB.eigenvalues j = 0) :
    hA.eigenvalues i * overlapWeight (overlapUnitary hA hB) i j = 0 := by
  have hz := support_overlap_mul_eq_zero hA hB hab i j hj
  have hr := congrArg (fun z : ℂ =>
    (z * starRingEnd ℂ ((overlapUnitary hA hB : Matrix n n ℂ) i j)).re) hz
  rw [mul_assoc, Complex.mul_conj, Complex.re_ofReal_mul, Complex.ofReal_re] at hr
  simpa [overlapWeight] using hr

theorem klein_trace_of_support {A B : Matrix n n ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) (hab : HasSupportIn A B) :
    A.trace.re - B.trace.re ≤
      (cfc (fun x : ℝ => x * Real.log x) A).trace.re -
        (A * cfc Real.log B).trace.re := by
  let U := overlapUnitary hA.1 hB.1
  have hpoint (i j : n) :
      (hA.1.eigenvalues i - hB.1.eigenvalues j) * overlapWeight U i j ≤
        (hA.1.eigenvalues i * Real.log (hA.1.eigenvalues i) -
          hA.1.eigenvalues i * Real.log (hB.1.eigenvalues j)) * overlapWeight U i j := by
    by_cases hj : hB.1.eigenvalues j = 0
    · have hw : hA.1.eigenvalues i * overlapWeight U i j = 0 :=
        support_overlap_weight_eq_zero hA.1 hB.1 hab i j hj
      have hlog : hA.1.eigenvalues i * Real.log (hA.1.eigenvalues i) *
          overlapWeight U i j = 0 := by
        calc
          _ = Real.log (hA.1.eigenvalues i) *
            (hA.1.eigenvalues i * overlapWeight U i j) := by ring
          _ = 0 := by rw [hw, mul_zero]
      simp only [hj, Real.log_zero, mul_zero, sub_zero]
      rw [hw, hlog]
    · exact mul_le_mul_of_nonneg_right
        (scalar_log_tangent (hA.eigenvalues_nonneg i)
          (lt_of_le_of_ne (hB.eigenvalues_nonneg j) (Ne.symm hj)))
        (overlapWeight_nonneg U i j)
  have hs := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) =>
    Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) => hpoint i j
  simp_rw [sub_mul, Finset.sum_sub_distrib] at hs
  rw [overlap_sum_rows, overlap_sum_cols, overlap_sum_rows] at hs
  rw [trace_eq_sum_eigenvalues_re hA.1, trace_eq_sum_eigenvalues_re hB.1,
    trace_cfc_eq_sum _ hA.1, trace_mul_cfc_eq_overlap _ hA.1 hB.1]
  exact hs

theorem finiteRelativeEntropyBits_nonneg_of_support {A B : Matrix n n ℂ}
    (hA : IsDensity A) (hB : IsDensity B) (hab : HasSupportIn A B) :
    0 ≤ finiteRelativeEntropyBits A B := by
  rw [finiteRelativeEntropyBits_eq_spectral hA.1.1]
  apply div_nonneg
  · have h := klein_trace_of_support hA.1 hB.1 hab
    simpa [hA.2, hB.2] using h
  · exact le_of_lt (Real.log_pos (by norm_num))

theorem relativeEntropyBits_nonneg {A B : Matrix n n ℂ}
    (hA : IsDensity A) (hB : IsDensity B) : 0 ≤ relativeEntropyBits A B := by
  by_cases hab : HasSupportIn A B
  · simp only [relativeEntropyBits, hab, ite_true]
    exact_mod_cast finiteRelativeEntropyBits_nonneg_of_support hA hB hab
  · simp [relativeEntropyBits, hab]

end QuantumProver.SuperchannelDiscrimination.Klein

namespace QuantumProver.SuperchannelDiscrimination.MatrixLog

open FlaggedStates TensorEntropy Klein
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem cfc_mulLog_eq_mul_log {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    cfc (fun x : ℝ => x * Real.log x) A = A * cfc Real.log A := by
  rw [cfc_mul (p := IsSelfAdjoint) (fun x : ℝ => x) Real.log A
    (A.finite_real_spectrum.continuousOn _) (A.finite_real_spectrum.continuousOn _),
    cfc_id' (p := IsSelfAdjoint) ℝ A hA]

theorem klein_trace_direct_of_support {A B : Matrix n n ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) (hab : HasSupportIn A B) :
    A.trace.re - B.trace.re ≤ (A * (cfc Real.log A - cfc Real.log B)).trace.re := by
  rw [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re,
    ← cfc_mulLog_eq_mul_log hA.1]
  exact klein_trace_of_support hA hB hab

theorem inverse_order {A B : Matrix n n ℂ} (hA : A.PosDef)
    (hAB : (B - A).PosSemidef) : (A⁻¹ - B⁻¹).PosSemidef := by
  have hab : A ≤ B := sub_nonneg.mp hAB.nonneg
  have h := CStarAlgebra.ringInverse_le_ringInverse hab hA.isStrictlyPositive
  rw [← Matrix.nonsing_inv_eq_ringInverse, ← Matrix.nonsing_inv_eq_ringInverse] at h
  exact Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr h)

theorem shift_posDef {A : Matrix n n ℂ} (hA : A.PosDef) {t : ℝ} (ht : 0 ≤ t) :
    (A + t • (1 : Matrix n n ℂ)).PosDef :=
  Matrix.isStrictlyPositive_iff_posDef.mp
    (hA.isStrictlyPositive.add_nonneg (Matrix.PosSemidef.one.smul ht).nonneg)

theorem shifted_inverse_order {A B : Matrix n n ℂ} (hA : A.PosDef)
    (hAB : (B - A).PosSemidef) {t : ℝ} (ht : 0 ≤ t) :
    ((A + t • (1 : Matrix n n ℂ))⁻¹ -
      (B + t • (1 : Matrix n n ℂ))⁻¹).PosSemidef := by
  apply inverse_order (shift_posDef hA ht)
  simpa only [add_sub_add_right_eq_sub] using hAB

theorem shifted_inverse_cfc {A : Matrix n n ℂ} (hA : A.PosDef)
    {t : ℝ} (ht : 0 ≤ t) :
    (A + t • (1 : Matrix n n ℂ))⁻¹ =
      cfc (fun x : ℝ => (x + t)⁻¹) A := by
  have hspec : ∀ x ∈ spectrum ℝ A, x + t ≠ 0 := by
    intro x hx
    rw [hA.1.spectrum_real_eq_range_eigenvalues] at hx
    obtain ⟨i, rfl⟩ := hx
    exact ne_of_gt (add_pos_of_pos_of_nonneg (hA.eigenvalues_pos i) ht)
  have hshift : cfc (fun x : ℝ => x + t) A = A + t • (1 : Matrix n n ℂ) := by
    rw [cfc_add_const (p := IsSelfAdjoint) t (fun x : ℝ => x) A
      (A.finite_real_spectrum.continuousOn _) hA.1,
      cfc_id' (p := IsSelfAdjoint) ℝ A hA.1]
    rw [Algebra.algebraMap_eq_smul_one]
  have h := cfc_inv (p := IsSelfAdjoint) (f := fun x : ℝ => x + t)
    (a := A) hspec (A.finite_real_spectrum.continuousOn _) hA.1
  rw [hshift, ← Matrix.nonsing_inv_eq_ringInverse] at h
  exact h.symm

def quadraticValue (X : Matrix n n ℂ) (v : n → ℂ) : ℝ :=
  (star v ⬝ᵥ (X *ᵥ v)).re

def eigenCoordinates {A : Matrix n n ℂ} (hA : A.IsHermitian) (v : n → ℂ) : n → ℂ :=
  (hA.eigenvectorUnitary : Matrix n n ℂ)ᴴ *ᵥ v

theorem quadraticValue_cfc_eq_sum (f : ℝ → ℝ) {A : Matrix n n ℂ}
    (hA : A.IsHermitian) (v : n → ℂ) :
    quadraticValue (cfc f A) v =
      ∑ i, f (hA.eigenvalues i) * Complex.normSq (eigenCoordinates hA v i) := by
  rw [cfc_spectral f hA]
  unfold quadraticValue
  change (star v ⬝ᵥ (((hA.eigenvectorUnitary : Matrix n n ℂ) *
    Matrix.diagonal (fun i => (f (hA.eigenvalues i) : ℂ)) *
    (hA.eigenvectorUnitary : Matrix n n ℂ)ᴴ) *ᵥ v)).re = _
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec]
  have hs : star v ᵥ* (hA.eigenvectorUnitary : Matrix n n ℂ) =
      star (eigenCoordinates hA v) := by
    rw [eigenCoordinates, Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose]
  rw [hs]
  change (star (eigenCoordinates hA v) ⬝ᵥ
    (Matrix.diagonal (fun i => (f (hA.eigenvalues i) : ℂ)) *ᵥ
      eigenCoordinates hA v)).re = _
  have hd : Matrix.diagonal (fun i => (f (hA.eigenvalues i) : ℂ)) *ᵥ
      eigenCoordinates hA v = fun i => (f (hA.eigenvalues i) : ℂ) * eigenCoordinates hA v i := by
    ext i
    simp [Matrix.mulVec, dotProduct, Matrix.diagonal_apply]
  rw [hd]
  simp only [dotProduct, Complex.re_sum, Pi.star_apply, Complex.star_def]
  apply Finset.sum_congr rfl
  intro i hi
  have hp : starRingEnd ℂ (eigenCoordinates hA v i) *
      ((f (hA.eigenvalues i) : ℂ) * eigenCoordinates hA v i) =
      (f (hA.eigenvalues i) : ℂ) *
        (starRingEnd ℂ (eigenCoordinates hA v i) * eigenCoordinates hA v i) := by ring
  rw [hp, ← Complex.normSq_eq_conj_mul_self, Complex.re_ofReal_mul, Complex.ofReal_re]

theorem eigenCoordinateNorm_sum {A : Matrix n n ℂ} (hA : A.IsHermitian) (v : n → ℂ) :
    ∑ i, Complex.normSq (eigenCoordinates hA v i) = quadraticValue 1 v := by
  have h := quadraticValue_cfc_eq_sum (fun _ : ℝ => 1) hA v
  rw [cfc_const_one (p := IsSelfAdjoint) ℝ A hA] at h
  simpa using h.symm

theorem shifted_inverse_quadratic {A : Matrix n n ℂ} (hA : A.PosDef)
    (v : n → ℂ) {t : ℝ} (ht : 0 ≤ t) :
    quadraticValue ((A + t • (1 : Matrix n n ℂ))⁻¹) v =
      ∑ i, (t + hA.1.eigenvalues i)⁻¹ * Complex.normSq (eigenCoordinates hA.1 v i) := by
  rw [shifted_inverse_cfc hA ht, quadraticValue_cfc_eq_sum _ hA.1]
  simp only [add_comm]

theorem quadraticValue_sub (A B : Matrix n n ℂ) (v : n → ℂ) :
    quadraticValue (A - B) v = quadraticValue A v - quadraticValue B v := by
  unfold quadraticValue
  rw [Matrix.sub_mulVec, dotProduct_sub, Complex.sub_re]

theorem quadraticValue_nonneg {A : Matrix n n ℂ} (hA : A.PosSemidef) (v : n → ℂ) :
    0 ≤ quadraticValue A v :=
  (RCLike.nonneg_iff.mp (hA.dotProduct_mulVec_nonneg v)).1

theorem posSemidef_of_quadraticValue_nonneg {A : Matrix n n ℂ}
    (hA : A.IsHermitian) (hq : ∀ v, 0 ≤ quadraticValue A v) : A.PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hA
  intro v
  apply RCLike.nonneg_iff.mpr
  refine ⟨hq v, ?_⟩
  have h := congrArg Complex.im (hA.star_dotProduct_mulVec_comm v v)
  simp only [Complex.star_def, Complex.conj_im] at h
  change (star v ⬝ᵥ (A *ᵥ v)).im = 0
  linarith

def logShiftSum (a w : n → ℝ) (t : ℝ) : ℝ :=
  ∑ i, Real.log (t + a i) * w i

set_option backward.isDefEq.respectTransparency false in
theorem logShiftSum_hasDerivAt (a w : n → ℝ) (t : ℝ)
    (ht : ∀ i, t + a i ≠ 0) :
    HasDerivAt (logShiftSum a w) (∑ i, (t + a i)⁻¹ * w i) t := by
  unfold logShiftSum
  simpa only [one_div, id_eq] using HasDerivAt.fun_sum
    (u := Finset.univ) (fun i _ =>
      (((hasDerivAt_id t).add_const (a i)).log (ht i)).mul_const (w i))

theorem logShiftSum_sub_log_tendsto (a w : n → ℝ) :
    Tendsto (fun t : ℝ => logShiftSum a w t - Real.log t * ∑ i, w i)
      atTop (𝓝 0) := by
  have h := tendsto_finsetSum Finset.univ (fun i _ =>
    (Real.tendsto_log_comp_add_sub_log (a i)).mul_const (w i))
  simpa only [logShiftSum, sub_mul, Finset.sum_sub_distrib,
    ← Finset.mul_sum, zero_mul, Finset.sum_const_zero] using h

theorem logShiftSum_difference_tendsto (a b w z : n → ℝ)
    (hw : ∑ i, w i = ∑ i, z i) :
    Tendsto (fun t : ℝ => logShiftSum a w t - logShiftSum b z t) atTop (𝓝 0) := by
  have h := (logShiftSum_sub_log_tendsto a w).sub (logShiftSum_sub_log_tendsto b z)
  have heq : (fun t : ℝ => (logShiftSum a w t - Real.log t * ∑ i, w i) -
      (logShiftSum b z t - Real.log t * ∑ i, z i)) =
      (fun t : ℝ => logShiftSum a w t - logShiftSum b z t) := by
    funext t
    rw [hw]
    ring
  simpa only [heq, sub_zero] using h

theorem logShiftDerivative_nonneg {A B : Matrix n n ℂ}
    (hA : A.PosDef) (hB : B.PosDef) (hAB : (B - A).PosSemidef)
    (v : n → ℂ) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ (∑ i, (t + hA.1.eigenvalues i)⁻¹ * Complex.normSq (eigenCoordinates hA.1 v i)) -
      (∑ i, (t + hB.1.eigenvalues i)⁻¹ * Complex.normSq (eigenCoordinates hB.1 v i)) := by
  have h := quadraticValue_nonneg (shifted_inverse_order hA hAB ht) v
  rwa [quadraticValue_sub, shifted_inverse_quadratic hA v ht,
    shifted_inverse_quadratic hB v ht] at h

set_option backward.isDefEq.respectTransparency false in

theorem log_quadratic_order {A B : Matrix n n ℂ}
    (hA : A.PosDef) (hB : B.PosDef) (hAB : (B - A).PosSemidef) (v : n → ℂ) :
    quadraticValue (cfc Real.log A) v ≤ quadraticValue (cfc Real.log B) v := by
  let wa : n → ℝ := fun i => Complex.normSq (eigenCoordinates hA.1 v i)
  let wb : n → ℝ := fun i => Complex.normSq (eigenCoordinates hB.1 v i)
  let g : ℝ → ℝ := fun t => logShiftSum hA.1.eigenvalues wa t -
    logShiftSum hB.1.eigenvalues wb t
  let dg : ℝ → ℝ := fun t =>
    (∑ i, (t + hA.1.eigenvalues i)⁻¹ * wa i) -
      (∑ i, (t + hB.1.eigenvalues i)⁻¹ * wb i)
  have hd (t : ℝ) (ht : 0 ≤ t) : HasDerivAt g (dg t) t :=
    (logShiftSum_hasDerivAt hA.1.eigenvalues wa t (fun i =>
      ne_of_gt (add_pos_of_nonneg_of_pos ht (hA.eigenvalues_pos i)))).sub
    (logShiftSum_hasDerivAt hB.1.eigenvalues wb t (fun i =>
      ne_of_gt (add_pos_of_nonneg_of_pos ht (hB.eigenvalues_pos i))))
  have hmono : MonotoneOn g (Ici (0 : ℝ)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici (0 : ℝ))
    · intro t ht
      exact (hd t ht).continuousAt.continuousWithinAt
    · intro t ht
      exact (hd t (interior_subset ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [(hd t (interior_subset ht)).deriv]
      exact logShiftDerivative_nonneg hA hB hAB v (interior_subset ht)
  have hw : ∑ i, wa i = ∑ i, wb i := by
    dsimp [wa, wb]
    rw [eigenCoordinateNorm_sum, eigenCoordinateNorm_sum]
  have hlim : Tendsto g atTop (𝓝 0) :=
    logShiftSum_difference_tendsto hA.1.eigenvalues hB.1.eigenvalues wa wb hw
  have hevent : ∀ᶠ t : ℝ in atTop, g 0 ≤ g t := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    exact hmono (by simp) ht ht
  have hz : g 0 ≤ 0 := ge_of_tendsto hlim hevent
  have hzero : g 0 = quadraticValue (cfc Real.log A) v -
      quadraticValue (cfc Real.log B) v := by
    rw [quadraticValue_cfc_eq_sum _ hA.1, quadraticValue_cfc_eq_sum _ hB.1]
    simp [g, logShiftSum, wa, wb]
  rw [hzero] at hz
  exact sub_nonpos.mp hz

theorem operator_log_monotone {A B : Matrix n n ℂ}
    (hA : A.PosDef) (hB : B.PosDef) (hAB : (B - A).PosSemidef) :
    (cfc Real.log B - cfc Real.log A).PosSemidef := by
  have ha : (cfc Real.log A).IsHermitian := cfc_predicate (p := IsSelfAdjoint) Real.log A
  have hb : (cfc Real.log B).IsHermitian := cfc_predicate (p := IsSelfAdjoint) Real.log B
  apply posSemidef_of_quadraticValue_nonneg (hb.sub ha)
  intro v
  rw [quadraticValue_sub]
  exact sub_nonneg.mpr (log_quadratic_order hA hB hAB v)

theorem finiteRelativeEntropyBits_alternative_order {A B C : Matrix n n ℂ}
    (hA : A.PosSemidef) (hB : B.PosDef) (hC : C.PosDef)
    (hBC : (C - B).PosSemidef) :
    finiteRelativeEntropyBits A C ≤ finiteRelativeEntropyBits A B := by
  have h := FlaggedStates.trace_mul_re_nonneg hA (operator_log_monotone hB hC hBC)
  simp only [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re] at h
  rw [finiteRelativeEntropyBits_eq_spectral hA.1,
    finiteRelativeEntropyBits_eq_spectral hA.1]
  apply div_le_div_of_nonneg_right _ (le_of_lt (Real.log_pos (by norm_num)))
  linarith

theorem relativeEntropyBits_alternative_order {A B C : Matrix n n ℂ}
    (hA : A.PosSemidef) (hB : B.PosDef) (hC : C.PosDef)
    (hBC : (C - B).PosSemidef) :
    relativeEntropyBits A C ≤ relativeEntropyBits A B := by
  rw [relativeEntropyBits_of_posDef _ hC, relativeEntropyBits_of_posDef _ hB]
  exact_mod_cast finiteRelativeEntropyBits_alternative_order hA hB hC hBC

theorem finiteRelativeEntropyBits_le_log_of_order_of_posDef {A B : Matrix n n ℂ}
    (hA : IsDensity A) (hAdef : A.PosDef) (hB : B.PosDef)
    {c : ℝ} (hc : 0 < c) (hdom : (c • B - A).PosSemidef) :
    finiteRelativeEntropyBits A B ≤ Real.log c / Real.log 2 := by
  have hlog : cfc Real.log (c • B) = Real.log c • (1 : Matrix n n ℂ) + cfc Real.log B := by
    simpa only [CFC.log, Algebra.algebraMap_eq_smul_one] using
      CFC.log_smul' B hc hB.isStrictlyPositive
  have h := FlaggedStates.trace_mul_re_nonneg hA.1
    (operator_log_monotone hAdef (hB.smul hc) hdom)
  rw [hlog] at h
  simp only [Matrix.mul_sub, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one,
    Matrix.trace_sub, Matrix.trace_add, Matrix.trace_smul, Complex.sub_re,
    Complex.add_re, Complex.smul_re, hA.2, Complex.one_re, smul_eq_mul, mul_one] at h
  rw [finiteRelativeEntropyBits_eq_spectral hA.1.1,
    cfc_mulLog_eq_mul_log hA.1.1]
  apply div_le_div_of_nonneg_right _ (le_of_lt (Real.log_pos (by norm_num)))
  linarith

theorem relativeEntropyBits_le_log_of_order_of_posDef {A B : Matrix n n ℂ}
    (hA : IsDensity A) (hAdef : A.PosDef) (hB : B.PosDef)
    {c : ℝ} (hc : 0 < c) (hdom : (c • B - A).PosSemidef) :
    relativeEntropyBits A B ≤ (Real.log c / Real.log 2 : ℝ) := by
  rw [relativeEntropyBits_of_posDef _ hB]
  exact_mod_cast finiteRelativeEntropyBits_le_log_of_order_of_posDef hA hAdef hB hc hdom

theorem finiteRelativeEntropyBits_ge_traceDifference_of_support {A B : Matrix n n ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) (hab : HasSupportIn A B) :
    (A.trace.re - B.trace.re) / Real.log 2 ≤ finiteRelativeEntropyBits A B := by
  rw [finiteRelativeEntropyBits_eq_spectral hA.1]
  exact div_le_div_of_nonneg_right (klein_trace_of_support hA hB hab)
    (le_of_lt (Real.log_pos (by norm_num)))

theorem relativeEntropyBits_ge_traceDifference {A B : Matrix n n ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    (((A.trace.re - B.trace.re) / Real.log 2 : ℝ) : EReal) ≤ relativeEntropyBits A B := by
  by_cases hab : HasSupportIn A B
  · simp only [relativeEntropyBits, hab, ite_true]
    exact_mod_cast finiteRelativeEntropyBits_ge_traceDifference_of_support hA hB hab
  · simp [relativeEntropyBits, hab]

end QuantumProver.SuperchannelDiscrimination.MatrixLog

namespace QuantumProver.SuperchannelDiscrimination.CPJensen

open CPWrappers MatrixLog TensorEntropy
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator Matrix

variable {I O : Type*} [Fintype I] [Fintype O] [DecidableEq I] [DecidableEq O]

theorem flagLiftMap_fromBlocks (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ)
    (A B C D : Matrix I I ℂ) :
    flagLiftMap Φ (Matrix.fromBlocks A B C D) =
      Matrix.fromBlocks (Φ A) (Φ B) (Φ C) (Φ D) := by
  ext (i | i) (j | j) <;> rfl

theorem map_posDef {Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ}
    (hΦ : CompletelyPositive Φ) (hu : Φ 1 = 1)
    {X : Matrix I I ℂ} (hX : X.PosDef) : (Φ X).PosDef := by
  classical
  by_cases hI : Nonempty I
  · letI : Nonempty I := hI
    obtain ⟨r, hr, hrX⟩ :=
      (CFC.exists_pos_algebraMap_le_iff X hX.1).mpr
        (fun x hx => hX.isStrictlyPositive.spectrum_pos hx)
    have hpos := completelyPositive_positive hΦ
      (Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr hrX))
    rw [map_sub, Algebra.algebraMap_eq_smul_one, Φ.map_smul_of_tower, hu] at hpos
    exact Matrix.isStrictlyPositive_iff_posDef.mp
      ((Matrix.PosDef.one.smul hr).isStrictlyPositive.of_le
        (sub_nonneg.mp hpos.nonneg))
  · have hXone : X = 1 := by
      ext i j
      exact (hI ⟨i⟩).elim
    rw [hXone, hu]
    exact Matrix.PosDef.one

theorem inverseBlock_posSemidef {X : Matrix I I ℂ} (hX : X.PosDef) :
    (Matrix.fromBlocks X 1 1 X⁻¹).PosSemidef := by
  letI : Invertible X := hX.isUnit.invertible
  have h := (Matrix.PosDef.fromBlocks₁₁ (1 : Matrix I I ℂ) X⁻¹ hX).mpr
    (by simpa using (Matrix.PosSemidef.zero : (0 : Matrix I I ℂ).PosSemidef))
  simpa using h

theorem schur_block_congruence {X : Matrix I I ℂ} (hX : X.PosDef)
    (D : Matrix I I ℂ) :
    (Matrix.fromBlocks 1 (-X⁻¹) 0 1)ᴴ *
        Matrix.fromBlocks X 1 1 D * Matrix.fromBlocks 1 (-X⁻¹) 0 1 =
      Matrix.fromBlocks X 0 0 (D - X⁻¹) := by
  letI : Invertible X := hX.isUnit.invertible
  simp [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, hX.inv.1.eq,
    sub_eq_add_neg, add_comm]

theorem inverse_jensen {Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ}
    (hΦ : CompletelyPositive Φ) (hu : Φ 1 = 1)
    {X : Matrix I I ℂ} (hX : X.PosDef) :
    (Φ X⁻¹ - (Φ X)⁻¹).PosSemidef := by
  have hY := map_posDef hΦ hu hX
  have hblock := completelyPositive_positive (completelyPositive_flagLiftMap hΦ)
    (inverseBlock_posSemidef hX)
  rw [flagLiftMap_fromBlocks, hu] at hblock
  have hschur := hblock.conjTranspose_mul_mul_same
    (Matrix.fromBlocks 1 (-(Φ X)⁻¹) 0 1 : Matrix (O ⊕ O) (O ⊕ O) ℂ)
  rw [schur_block_congruence hY] at hschur
  exact hschur.submatrix Sum.inr

theorem map_isHermitian {Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ}
    (hΦ : CompletelyPositive Φ) (hu : Φ 1 = 1)
    {H : Matrix I I ℂ} (hH : H.IsHermitian) : (Φ H).IsHermitian := by
  have hp : (H + ‖H‖ • (1 : Matrix I I ℂ)).PosSemidef := by
    have h := IsSelfAdjoint.neg_algebraMap_norm_le_self H hH
    simpa [sub_neg_eq_add, Algebra.algebraMap_eq_smul_one] using
      (Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr h))
  have hq := (completelyPositive_positive hΦ hp).1
  rw [map_add, Φ.map_smul_of_tower, hu] at hq
  have heq : Φ H = (Φ H + ‖H‖ • (1 : Matrix O O ℂ)) -
      ‖H‖ • (1 : Matrix O O ℂ) := by abel
  rw [heq]
  exact hq.sub (Matrix.PosSemidef.one.smul (norm_nonneg H)).1

def spectralCoordinate {X : Matrix I I ℂ} (hX : X.IsHermitian) (i : I) :
    Matrix I I ℂ :=
  Unitary.conjStarAlgAut ℝ (Matrix I I ℂ) hX.eigenvectorUnitary
    (Matrix.diagonal (Pi.single i (1 : ℂ)))

theorem cfc_eq_coordinate_sum (f : ℝ → ℝ) {X : Matrix I I ℂ}
    (hX : X.IsHermitian) :
    cfc f X = ∑ i, f (hX.eigenvalues i) • spectralCoordinate hX i := by
  classical
  rw [cfc_spectral f hX]
  have hd : Matrix.diagonal (fun i => (f (hX.eigenvalues i) : ℂ)) =
      ∑ i, f (hX.eigenvalues i) • Matrix.diagonal (Pi.single i (1 : ℂ)) := by
    ext i j
    simp [Matrix.sum_apply, Matrix.diagonal_apply, Pi.single_apply]
  rw [hd, map_sum]
  simp only [map_smul, spectralCoordinate]

def imageSpectralWeight (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ)
    {X : Matrix I I ℂ} (hX : X.IsHermitian) (v : O → ℂ) (i : I) : ℝ :=
  quadraticValue (Φ (spectralCoordinate hX i)) v

theorem image_cfc_quadratic (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ)
    (f : ℝ → ℝ) {X : Matrix I I ℂ} (hX : X.IsHermitian) (v : O → ℂ) :
    quadraticValue (Φ (cfc f X)) v =
      ∑ i, f (hX.eigenvalues i) * imageSpectralWeight Φ hX v i := by
  rw [cfc_eq_coordinate_sum f hX, map_sum]
  simp only [Φ.map_smul_of_tower]
  unfold imageSpectralWeight quadraticValue
  simp only [Matrix.sum_mulVec, dotProduct_sum, Complex.re_sum,
    Matrix.smul_mulVec, dotProduct_smul, Complex.smul_re, smul_eq_mul]

theorem imageSpectralWeight_sum (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ)
    (hu : Φ 1 = 1) {X : Matrix I I ℂ} (hX : X.IsHermitian) (v : O → ℂ) :
    ∑ i, imageSpectralWeight Φ hX v i = quadraticValue 1 v := by
  have h := image_cfc_quadratic Φ (fun _ : ℝ => 1) hX v
  rw [cfc_const_one (p := IsSelfAdjoint) ℝ X hX, hu] at h
  simpa using h.symm

theorem image_shifted_inverse_quadratic
    (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) {X : Matrix I I ℂ}
    (hX : X.PosDef) (v : O → ℂ) {t : ℝ} (ht : 0 ≤ t) :
    quadraticValue (Φ ((X + t • (1 : Matrix I I ℂ))⁻¹)) v =
      ∑ i, (t + hX.1.eigenvalues i)⁻¹ * imageSpectralWeight Φ hX.1 v i := by
  rw [shifted_inverse_cfc hX ht, image_cfc_quadratic Φ _ hX.1 v]
  simp only [add_comm]

theorem shifted_inverse_jensen {Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ}
    (hΦ : CompletelyPositive Φ) (hu : Φ 1 = 1)
    {X : Matrix I I ℂ} (hX : X.PosDef) {t : ℝ} (ht : 0 ≤ t) :
    (Φ ((X + t • (1 : Matrix I I ℂ))⁻¹) -
      (Φ X + t • (1 : Matrix O O ℂ))⁻¹).PosSemidef := by
  have h := inverse_jensen hΦ hu (shift_posDef hX ht)
  rwa [map_add, Φ.map_smul_of_tower, hu] at h

theorem image_logShiftDerivative_nonneg
    {Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ}
    (hΦ : CompletelyPositive Φ) (hu : Φ 1 = 1)
    {X : Matrix I I ℂ} (hX : X.PosDef) (v : O → ℂ)
    {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ (∑ i, (t + hX.1.eigenvalues i)⁻¹ * imageSpectralWeight Φ hX.1 v i) -
      (∑ i, (t + (map_posDef hΦ hu hX).1.eigenvalues i)⁻¹ *
        Complex.normSq (eigenCoordinates (map_posDef hΦ hu hX).1 v i)) := by
  have h := quadraticValue_nonneg (shifted_inverse_jensen hΦ hu hX ht) v
  rwa [quadraticValue_sub, image_shifted_inverse_quadratic Φ hX v ht,
    shifted_inverse_quadratic (map_posDef hΦ hu hX) v ht] at h

set_option backward.isDefEq.respectTransparency false in

theorem log_quadratic_jensen {Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ}
    (hΦ : CompletelyPositive Φ) (hu : Φ 1 = 1)
    {X : Matrix I I ℂ} (hX : X.PosDef) (v : O → ℂ) :
    quadraticValue (Φ (cfc Real.log X)) v ≤ quadraticValue (cfc Real.log (Φ X)) v := by
  let hY := map_posDef hΦ hu hX
  let wa : I → ℝ := imageSpectralWeight Φ hX.1 v
  let wb : O → ℝ := fun i => Complex.normSq (eigenCoordinates hY.1 v i)
  let g : ℝ → ℝ := fun t => logShiftSum hX.1.eigenvalues wa t -
    logShiftSum hY.1.eigenvalues wb t
  let dg : ℝ → ℝ := fun t =>
    (∑ i, (t + hX.1.eigenvalues i)⁻¹ * wa i) -
      (∑ i, (t + hY.1.eigenvalues i)⁻¹ * wb i)
  have hd (t : ℝ) (ht : 0 ≤ t) : HasDerivAt g (dg t) t :=
    (logShiftSum_hasDerivAt hX.1.eigenvalues wa t (fun i =>
      ne_of_gt (add_pos_of_nonneg_of_pos ht (hX.eigenvalues_pos i)))).sub
    (logShiftSum_hasDerivAt hY.1.eigenvalues wb t (fun i =>
      ne_of_gt (add_pos_of_nonneg_of_pos ht (hY.eigenvalues_pos i))))
  have hmono : MonotoneOn g (Ici (0 : ℝ)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici (0 : ℝ))
    · intro t ht
      exact (hd t ht).continuousAt.continuousWithinAt
    · intro t ht
      exact (hd t (interior_subset ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [(hd t (interior_subset ht)).deriv]
      exact image_logShiftDerivative_nonneg hΦ hu hX v (interior_subset ht)
  have hw : ∑ i, wa i = ∑ i, wb i := by
    dsimp [wa, wb]
    rw [imageSpectralWeight_sum Φ hu, eigenCoordinateNorm_sum]
  have hlim : Tendsto g atTop (𝓝 0) := by
    have h := (logShiftSum_sub_log_tendsto hX.1.eigenvalues wa).sub
      (logShiftSum_sub_log_tendsto hY.1.eigenvalues wb)
    have heq : (fun t : ℝ =>
        (logShiftSum hX.1.eigenvalues wa t - Real.log t * ∑ i, wa i) -
          (logShiftSum hY.1.eigenvalues wb t - Real.log t * ∑ i, wb i)) = g := by
      funext t
      dsimp [g]
      rw [hw]
      ring
    simpa only [heq, sub_zero] using h
  have hevent : ∀ᶠ t : ℝ in atTop, g 0 ≤ g t := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    exact hmono (by simp) ht ht
  have hz : g 0 ≤ 0 := ge_of_tendsto hlim hevent
  have hzero : g 0 = quadraticValue (Φ (cfc Real.log X)) v -
      quadraticValue (cfc Real.log (Φ X)) v := by
    rw [image_cfc_quadratic Φ _ hX.1, quadraticValue_cfc_eq_sum _ hY.1]
    simp [g, logShiftSum, wa, wb]
  rw [hzero] at hz
  exact sub_nonpos.mp hz

theorem operator_log_jensen {Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ}
    (hΦ : CompletelyPositive Φ) (hu : Φ 1 = 1)
    {X : Matrix I I ℂ} (hX : X.PosDef) :
    (cfc Real.log (Φ X) - Φ (cfc Real.log X)).PosSemidef := by
  have hXin : (cfc Real.log X).IsHermitian := cfc_predicate (p := IsSelfAdjoint) Real.log X
  have hYlog : (cfc Real.log (Φ X)).IsHermitian :=
    cfc_predicate (p := IsSelfAdjoint) Real.log (Φ X)
  apply posSemidef_of_quadraticValue_nonneg
    (hYlog.sub (map_isHermitian hΦ hu hXin))
  intro v
  rw [quadraticValue_sub]
  exact sub_nonneg.mpr (log_quadratic_jensen hΦ hu hX v)

end QuantumProver.SuperchannelDiscrimination.CPJensen

namespace QuantumProver.SuperchannelDiscrimination.CPSchwarz

open KrausCompletion CPWrappers CPJensen MatrixLog FlaggedStates
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator Matrix

variable {I O κ : Type*} [Fintype I] [Fintype O] [Fintype κ]
  [DecidableEq I] [DecidableEq O]

theorem gramBlock_posSemidef (Z : Matrix I I ℂ) :
    (Matrix.fromBlocks (Zᴴ * Z) Zᴴ Z 1).PosSemidef := by
  have h := Matrix.posSemidef_conjTranspose_mul_self
    (Matrix.fromBlocks Z 1 0 0 : Matrix (I ⊕ I) (I ⊕ I) ℂ)
  simpa [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply] using h

theorem map_conjTranspose {Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ}
    (hΦ : CompletelyPositive Φ) (Z : Matrix I I ℂ) :
    Φ Zᴴ = (Φ Z)ᴴ := by
  have hblock := completelyPositive_positive (completelyPositive_flagLiftMap hΦ)
    (gramBlock_posSemidef Z)
  rw [flagLiftMap_fromBlocks] at hblock
  exact (Matrix.isHermitian_fromBlocks_iff.mp hblock.1).2.2.1.symm

theorem map_isHermitian_of_cp {Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ}
    (hΦ : CompletelyPositive Φ) {H : Matrix I I ℂ} (hH : H.IsHermitian) :
    (Φ H).IsHermitian := by
  change (Φ H)ᴴ = Φ H
  rw [← map_conjTranspose hΦ H, hH.eq]

theorem kadison_schwarz {Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ}
    (hΦ : CompletelyPositive Φ) (hu : Φ 1 = 1) (Z : Matrix I I ℂ) :
    (Φ (Zᴴ * Z) - (Φ Z)ᴴ * Φ Z).PosSemidef := by
  letI : Invertible (1 : Matrix O O ℂ) := invertibleOne
  have hblock := completelyPositive_positive (completelyPositive_flagLiftMap hΦ)
    (gramBlock_posSemidef Z)
  rw [flagLiftMap_fromBlocks, hu, map_conjTranspose hΦ Z] at hblock
  have h := (Matrix.PosDef.fromBlocks₂₂ (Φ (Zᴴ * Z)) ((Φ Z)ᴴ)
    (Matrix.PosDef.one : (1 : Matrix O O ℂ).PosDef)).mp (by simpa using hblock)
  simpa using h

theorem kadison_schwarz_right {Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ}
    (hΦ : CompletelyPositive Φ) (hu : Φ 1 = 1) (Z : Matrix I I ℂ) :
    (Φ (Z * Zᴴ) - Φ Z * (Φ Z)ᴴ).PosSemidef := by
  have h := kadison_schwarz hΦ hu Zᴴ
  simpa [map_conjTranspose hΦ Z] using h

def adjointKrausMap (K : κ → Matrix O I ℂ) :
    Matrix O O ℂ →ₗ[ℂ] Matrix I I ℂ := krausMap (fun k => (K k)ᴴ)

theorem adjointKrausMap_completelyPositive (K : κ → Matrix O I ℂ) :
    CompletelyPositive (adjointKrausMap K) := by
  intro r A hA
  exact krausMap_completelyPositive (fun k => (K k)ᴴ) (Fin r) hA

theorem adjointKrausMap_unital (K : κ → Matrix O I ℂ)
    (hK : krausGram K = 1) : adjointKrausMap K 1 = 1 := by
  simpa [adjointKrausMap, krausMap, krausAction, krausGram] using hK

theorem adjointKrausMap_schwarz (K : κ → Matrix O I ℂ)
    (hK : krausGram K = 1) (Z : Matrix O O ℂ) :
    (adjointKrausMap K (Zᴴ * Z) -
      (adjointKrausMap K Z)ᴴ * adjointKrausMap K Z).PosSemidef :=
  kadison_schwarz (adjointKrausMap_completelyPositive K) (adjointKrausMap_unital K hK) Z

theorem trace_kraus_adjoint (K : κ → Matrix O I ℂ)
    (A : Matrix I I ℂ) (B : Matrix O O ℂ) :
    (krausAction K A * B).trace = (A * adjointKrausMap K B).trace := by
  change (krausAction K A * B).trace = (A * krausAction (fun k => (K k)ᴴ) B).trace
  simp only [krausAction, Matrix.sum_mul,
    Matrix.mul_sum, Matrix.trace_sum, Matrix.conjTranspose_conjTranspose]
  apply Finset.sum_congr rfl
  intro k hk
  simpa only [Matrix.mul_assoc] using
    Matrix.trace_mul_comm (K k) (A * ((K k)ᴴ * B))

theorem adjoint_weighted_square_le (K : κ → Matrix O I ℂ)
    (hK : krausGram K = 1) {A : Matrix I I ℂ} (hA : A.PosSemidef)
    (Z : Matrix O O ℂ) :
    (A * ((adjointKrausMap K Z)ᴴ * adjointKrausMap K Z)).trace.re ≤
      (krausAction K A * (Zᴴ * Z)).trace.re := by
  have h := FlaggedStates.trace_mul_re_nonneg hA (adjointKrausMap_schwarz K hK Z)
  rw [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re,
    ← trace_kraus_adjoint K A (Zᴴ * Z)] at h
  exact sub_nonneg.mp h

theorem adjoint_weighted_square_right_le (K : κ → Matrix O I ℂ)
    (hK : krausGram K = 1) {A : Matrix I I ℂ} (hA : A.PosSemidef)
    (Z : Matrix O O ℂ) :
    (A * (adjointKrausMap K Z * (adjointKrausMap K Z)ᴴ)).trace.re ≤
      (krausAction K A * (Z * Zᴴ)).trace.re := by
  have h := FlaggedStates.trace_mul_re_nonneg hA
    (kadison_schwarz_right (adjointKrausMap_completelyPositive K)
      (adjointKrausMap_unital K hK) Z)
  rw [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re,
    ← trace_kraus_adjoint K A (Z * Zᴴ)] at h
  exact sub_nonneg.mp h

theorem sqrt_posDef {A : Matrix I I ℂ} (hA : A.PosDef) : (CFC.sqrt A).PosDef :=
  Matrix.isStrictlyPositive_iff_posDef.mp (IsStrictlyPositive.sqrt A hA.isStrictlyPositive)

theorem trace_square_right_sqrt {A : Matrix I I ℂ} (hA : A.PosSemidef)
    (Z : Matrix I I ℂ) :
    ((Z * CFC.sqrt A)ᴴ * (Z * CFC.sqrt A)).trace = (A * (Zᴴ * Z)).trace := by
  have hroot : (CFC.sqrt A).IsHermitian :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)).1
  calc
    _ = (CFC.sqrt A * (Zᴴ * Z) * CFC.sqrt A).trace := by
      simp only [Matrix.conjTranspose_mul, hroot.eq, Matrix.mul_assoc]
    _ = (A * (Zᴴ * Z)).trace := by
      rw [Matrix.trace_mul_cycle, CFC.sqrt_mul_sqrt_self A hA.nonneg]

theorem trace_square_right_inverse_sqrt {A : Matrix I I ℂ} (hA : A.PosDef)
    (Z : Matrix I I ℂ) :
    (A * ((Z * (CFC.sqrt A)⁻¹)ᴴ * (Z * (CFC.sqrt A)⁻¹))).trace = (Zᴴ * Z).trace := by
  let R := CFC.sqrt A
  have hR : R.PosDef := sqrt_posDef hA
  letI : Invertible R := hR.isUnit.invertible
  have hsq : R * R = A := CFC.sqrt_mul_sqrt_self A hA.posSemidef.nonneg
  have hinv : R⁻¹ * A * R⁻¹ = 1 := by
    calc
      _ = R⁻¹ * (R * R) * R⁻¹ := by rw [hsq]
      _ = (R⁻¹ * R) * (R * R⁻¹) := by simp only [Matrix.mul_assoc]
      _ = 1 := by simp
  change (A * ((Z * R⁻¹)ᴴ * (Z * R⁻¹))).trace = _
  calc
    _ = ((A * R⁻¹) * (Zᴴ * Z) * R⁻¹).trace := by
      simp only [Matrix.conjTranspose_mul, hR.inv.1.eq, Matrix.mul_assoc]
    _ = ((R⁻¹ * A * R⁻¹) * (Zᴴ * Z)).trace := by
      rw [Matrix.trace_mul_cycle]
      simp only [Matrix.mul_assoc]
    _ = (Zᴴ * Z).trace := by rw [hinv, Matrix.one_mul]

def weightedPullback (K : κ → Matrix O I ℂ) (A : Matrix I I ℂ)
    (Z : Matrix O O ℂ) : Matrix I I ℂ :=
  adjointKrausMap K (Z * (CFC.sqrt (krausAction K A))⁻¹) * CFC.sqrt A

theorem weightedPullback_square_le (K : κ → Matrix O I ℂ)
    (hK : krausGram K = 1) {A : Matrix I I ℂ} (hA : A.PosSemidef)
    (hOut : (krausAction K A).PosDef) (Z : Matrix O O ℂ) :
    ((weightedPullback K A Z)ᴴ * weightedPullback K A Z).trace.re ≤ (Zᴴ * Z).trace.re := by
  have h := adjoint_weighted_square_le K hK hA
    (Z * (CFC.sqrt (krausAction K A))⁻¹)
  rw [trace_square_right_inverse_sqrt hOut Z] at h
  rw [weightedPullback, trace_square_right_sqrt hA]
  exact h

theorem weightedPullback_sqrt (K : κ → Matrix O I ℂ)
    (hK : krausGram K = 1) {A : Matrix I I ℂ}
    (hOut : (krausAction K A).PosDef) :
    weightedPullback K A (CFC.sqrt (krausAction K A)) = CFC.sqrt A := by
  letI : Invertible (CFC.sqrt (krausAction K A)) := (sqrt_posDef hOut).isUnit.invertible
  rw [weightedPullback, Matrix.mul_inv_of_invertible, adjointKrausMap_unital K hK,
    Matrix.one_mul]

theorem inverse_sqrt_square {A : Matrix I I ℂ} (hA : A.PosDef) :
    (CFC.sqrt A)⁻¹ * (CFC.sqrt A)⁻¹ = A⁻¹ := by
  rw [← Matrix.mul_inv_rev, CFC.sqrt_mul_sqrt_self A hA.posSemidef.nonneg]

theorem sqrt_inverse_sandwich {A : Matrix I I ℂ} (hA : A.PosDef) :
    CFC.sqrt A * A⁻¹ * CFC.sqrt A = 1 := by
  letI : Invertible (CFC.sqrt A) := (sqrt_posDef hA).isUnit.invertible
  rw [← inverse_sqrt_square hA]
  simp [← Matrix.mul_assoc]

theorem trace_modular_right_sqrt {A : Matrix I I ℂ} (hA : A.PosDef)
    (B Z : Matrix I I ℂ) :
    ((Z * CFC.sqrt A)ᴴ * B * (Z * CFC.sqrt A) * A⁻¹).trace =
      (B * (Z * Zᴴ)).trace := by
  have hroot := (sqrt_posDef hA).1
  calc
    _ = (CFC.sqrt A * (Zᴴ * B * Z) * (CFC.sqrt A * A⁻¹)).trace := by
      simp only [Matrix.conjTranspose_mul, hroot.eq, Matrix.mul_assoc]
    _ = ((CFC.sqrt A * A⁻¹ * CFC.sqrt A) * (Zᴴ * B * Z)).trace := by
      rw [Matrix.trace_mul_cycle]
    _ = (Zᴴ * B * Z).trace := by rw [sqrt_inverse_sandwich hA, Matrix.one_mul]
    _ = (B * (Z * Zᴴ)).trace := by
      simpa only [Matrix.mul_assoc] using Matrix.trace_mul_comm Zᴴ (B * Z)

theorem trace_modular_eq_inverse_sqrt {A : Matrix I I ℂ} (hA : A.PosDef)
    (B Z : Matrix I I ℂ) :
    (Zᴴ * B * Z * A⁻¹).trace =
      (B * ((Z * (CFC.sqrt A)⁻¹) * (Z * (CFC.sqrt A)⁻¹)ᴴ)).trace := by
  have hrootinv := (sqrt_posDef hA).inv.1
  calc
    _ = (B * (Z * A⁻¹ * Zᴴ)).trace := by
      simpa only [Matrix.mul_assoc] using Matrix.trace_mul_comm Zᴴ (B * Z * A⁻¹)
    _ = _ := by
      rw [← inverse_sqrt_square hA]
      simp only [Matrix.conjTranspose_mul, hrootinv.eq, Matrix.mul_assoc]

theorem weightedPullback_modular_le (K : κ → Matrix O I ℂ)
    (hK : krausGram K = 1) {A B : Matrix I I ℂ} (hA : A.PosDef)
    (hB : B.PosSemidef) (hOut : (krausAction K A).PosDef) (Z : Matrix O O ℂ) :
    ((weightedPullback K A Z)ᴴ * B * weightedPullback K A Z * A⁻¹).trace.re ≤
      (Zᴴ * krausAction K B * Z * (krausAction K A)⁻¹).trace.re := by
  rw [weightedPullback, trace_modular_right_sqrt hA,
    trace_modular_eq_inverse_sqrt hOut]
  exact adjoint_weighted_square_right_le K hK hB
    (Z * (CFC.sqrt (krausAction K A))⁻¹)

end QuantumProver.SuperchannelDiscrimination.CPSchwarz

namespace QuantumProver.SuperchannelDiscrimination.ModularMatrix

open KrausCompletion CPWrappers CPJensen CPSchwarz MatrixLog TensorEntropy FlaggedStates
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator Matrix Kronecker

variable {I O κ : Type*} [Fintype I] [Fintype O] [Fintype κ]
  [DecidableEq I] [DecidableEq O]

def flatten (Z : Matrix I I ℂ) : I × I → ℂ := fun x => Z x.1 x.2
def unflatten (z : I × I → ℂ) : Matrix I I ℂ := fun i j => z (i, j)

def flattenLinearEquiv : Matrix I I ℂ ≃ₗ[ℂ] (I × I → ℂ) where
  toFun := flatten
  invFun := unflatten
  left_inv Z := rfl
  right_inv z := by ext ⟨i, j⟩; rfl
  map_add' Z W := rfl
  map_smul' c Z := rfl

theorem flatten_unflatten (z : I × I → ℂ) : flatten (unflatten z) = z := by
  ext ⟨i, j⟩
  rfl

theorem flatten_trace_pairing (X Y : Matrix I I ℂ) :
    star (flatten X) ⬝ᵥ flatten Y = (Xᴴ * Y).trace := by
  simp only [flatten, dotProduct, Pi.star_apply, Matrix.trace, Matrix.diag,
    Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type]
  exact Finset.sum_comm

def delta (B A : Matrix I I ℂ) : Matrix (I × I) (I × I) ℂ := B ⊗ₖ A⁻¹ᵀ

theorem delta_mulVec_flatten (B A Z : Matrix I I ℂ) :
    delta B A *ᵥ flatten Z = flatten (B * Z * A⁻¹) := by
  ext ⟨i, j⟩
  simp only [delta, flatten, Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
    Matrix.kronecker_apply, Matrix.transpose_apply, Matrix.mul_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  ring

theorem delta_posSemidef {A B : Matrix I I ℂ} (hA : A.PosDef) (hB : B.PosSemidef) :
    (delta B A).PosSemidef := hB.kronecker hA.inv.posSemidef.transpose

theorem delta_posDef {A B : Matrix I I ℂ} (hA : A.PosDef) (hB : B.PosDef) :
    (delta B A).PosDef := hB.kronecker hA.inv.transpose

theorem delta_quadratic (B A Z : Matrix I I ℂ) :
    quadraticValue (delta B A) (flatten Z) = (Zᴴ * B * Z * A⁻¹).trace.re := by
  unfold quadraticValue
  rw [delta_mulVec_flatten, flatten_trace_pairing]
  simp only [Matrix.mul_assoc]

theorem identity_quadratic (Z : Matrix I I ℂ) :
    quadraticValue 1 (flatten Z) = (Zᴴ * Z).trace.re := by
  unfold quadraticValue
  rw [Matrix.one_mulVec, flatten_trace_pairing]

def weightedPullbackLinear (K : κ → Matrix O I ℂ) (A : Matrix I I ℂ) :
    Matrix O O ℂ →ₗ[ℂ] Matrix I I ℂ where
  toFun := weightedPullback K A
  map_add' Z W := by simp [weightedPullback, Matrix.add_mul, map_add]
  map_smul' c Z := by simp [weightedPullback, Matrix.smul_mul, map_smul]

def flatPullbackLinear (K : κ → Matrix O I ℂ) (A : Matrix I I ℂ) :
    (O × O → ℂ) →ₗ[ℂ] (I × I → ℂ) :=
  flattenLinearEquiv.toLinearMap.comp
    ((weightedPullbackLinear K A).comp (flattenLinearEquiv (I := O)).symm.toLinearMap)

def pullbackMatrix (K : κ → Matrix O I ℂ) (A : Matrix I I ℂ) :
    Matrix (I × I) (O × O) ℂ := LinearMap.toMatrix' (flatPullbackLinear K A)

theorem pullbackMatrix_action (K : κ → Matrix O I ℂ) (A : Matrix I I ℂ)
    (Z : Matrix O O ℂ) :
    pullbackMatrix K A *ᵥ flatten Z = flatten (weightedPullback K A Z) := by
  rw [pullbackMatrix, LinearMap.toMatrix'_mulVec]
  rfl

theorem quadratic_congruence (V : Matrix I O ℂ) (M : Matrix I I ℂ) (v : O → ℂ) :
    quadraticValue (Vᴴ * M * V) v = quadraticValue M (V *ᵥ v) := by
  unfold quadraticValue
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    ← Matrix.star_mulVec]

theorem quadratic_gram (V : Matrix I O ℂ) (v : O → ℂ) :
    quadraticValue (Vᴴ * V) v = quadraticValue 1 (V *ᵥ v) := by
  simpa using quadratic_congruence V 1 v

theorem pullbackMatrix_contraction (K : κ → Matrix O I ℂ)
    (hK : krausGram K = 1) {A : Matrix I I ℂ} (hA : A.PosSemidef)
    (hOut : (krausAction K A).PosDef) :
    (1 - (pullbackMatrix K A)ᴴ * pullbackMatrix K A).PosSemidef := by
  apply posSemidef_of_quadraticValue_nonneg
    (Matrix.isHermitian_one.sub
      (Matrix.posSemidef_conjTranspose_mul_self (pullbackMatrix K A)).1)
  intro v
  rw [quadraticValue_sub, quadratic_gram]
  have h := weightedPullback_square_le K hK hA hOut (unflatten v)
  rw [← identity_quadratic, ← identity_quadratic, ← pullbackMatrix_action,
    flatten_unflatten] at h
  exact sub_nonneg.mpr h

theorem pullbackMatrix_modular_order (K : κ → Matrix O I ℂ)
    (hK : krausGram K = 1) {A B : Matrix I I ℂ} (hA : A.PosDef)
    (hB : B.PosSemidef) (hOut : (krausAction K A).PosDef) :
    (delta (krausAction K B) (krausAction K A) -
      (pullbackMatrix K A)ᴴ * delta B A * pullbackMatrix K A).PosSemidef := by
  have hout := delta_posSemidef hOut (krausAction_posSemidef K hB)
  have hin := (delta_posSemidef hA hB).conjTranspose_mul_mul_same (pullbackMatrix K A)
  apply posSemidef_of_quadraticValue_nonneg (hout.1.sub hin.1)
  intro v
  have h := weightedPullback_modular_le K hK hA hB hOut (unflatten v)
  rw [← delta_quadratic, ← delta_quadratic, ← pullbackMatrix_action,
    flatten_unflatten] at h
  rw [quadraticValue_sub, quadratic_congruence]
  exact sub_nonneg.mpr h

theorem pullbackMatrix_sqrt (K : κ → Matrix O I ℂ)
    (hK : krausGram K = 1) {A : Matrix I I ℂ}
    (hOut : (krausAction K A).PosDef) :
    pullbackMatrix K A *ᵥ flatten (CFC.sqrt (krausAction K A)) = flatten (CFC.sqrt A) := by
  rw [pullbackMatrix_action, weightedPullback_sqrt K hK hOut]

def conjugateHom : Matrix I I ℂ →⋆ₐ[ℝ] Matrix I I ℂ where
  __ := (starRingEnd ℂ).mapMatrix
  commutes' r := by
    ext i j
    simp [RingHom.mapMatrix_apply, Matrix.algebraMap_eq_diagonal, Matrix.diagonal_apply]
    split_ifs <;> simp
  map_star' X := by
    ext i j
    rfl

theorem conjugateHom_eq_transpose {A : Matrix I I ℂ} (hA : A.IsHermitian) :
    conjugateHom A = Aᵀ := by
  ext i j
  exact congrArg (fun M : Matrix I I ℂ => M j i) hA.eq

theorem cfc_transpose (f : ℝ → ℝ) {A : Matrix I I ℂ} (hA : A.IsHermitian) :
    cfc f Aᵀ = (cfc f A)ᵀ := by
  have hc : Continuous (conjugateHom (I := I)) := by
    change Continuous (fun X : Matrix I I ℂ => X.map (starRingEnd ℂ))
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    fun_prop
  have h := (conjugateHom (I := I)).map_cfc f A
    (A.finite_real_spectrum.continuousOn _) hc hA (by
      rw [conjugateHom_eq_transpose hA]
      exact hA.transpose)
  rw [conjugateHom_eq_transpose hA,
    conjugateHom_eq_transpose (cfc_predicate (p := IsSelfAdjoint) f A)] at h
  exact h.symm

theorem cfc_log_inverse {A : Matrix I I ℂ} (hA : A.PosDef) :
    cfc Real.log A⁻¹ = -cfc Real.log A := by
  have hinv : A⁻¹ = cfc (fun x : ℝ => x⁻¹) A := by
    simpa using shifted_inverse_cfc hA (t := 0) (by simp)
  have hc := cfc_comp (p := IsSelfAdjoint) Real.log (fun x : ℝ => x⁻¹) A hA.1
    ((A.finite_real_spectrum.image _).continuousOn _)
    (A.finite_real_spectrum.continuousOn _)
  rw [hinv, ← hc]
  have hf : (Real.log ∘ (fun x : ℝ => x⁻¹)) = fun x => -Real.log x := by
    funext x
    exact Real.log_inv x
  rw [hf, cfc_neg]

theorem supportProjection_posDef {A : Matrix I I ℂ} (hA : A.PosDef) :
    supportProjection A = 1 := by
  letI : Invertible A := hA.isUnit.invertible
  rw [supportProjection_eq_inverse_mul A hA.1]
  have hi : cfc (fun x : ℝ => x⁻¹) A = A⁻¹ := by
    simpa using (shifted_inverse_cfc hA (t := 0) (by simp)).symm
  rw [hi, Matrix.inv_mul_of_invertible]

theorem cfc_log_delta {A B : Matrix I I ℂ} (hA : A.PosDef) (hB : B.PosDef) :
    cfc Real.log (delta B A) =
      cfc Real.log B ⊗ₖ (1 : Matrix I I ℂ) -
        (1 : Matrix I I ℂ) ⊗ₖ (cfc Real.log A)ᵀ := by
  rw [delta, cfc_log_kronecker_support hB.1 hA.inv.transpose.1,
    supportProjection_posDef hA.inv.transpose, supportProjection_posDef hB,
    cfc_transpose Real.log hA.inv.1, cfc_log_inverse hA]
  ext x y
  simp [sub_eq_add_neg, Matrix.kronecker_apply, Matrix.transpose_apply]

theorem kronecker_transpose_mulVec_flatten (B C Z : Matrix I I ℂ) :
    (B ⊗ₖ Cᵀ) *ᵥ flatten Z = flatten (B * Z * C) := by
  ext ⟨i, j⟩
  simp only [flatten, Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
    Matrix.kronecker_apply, Matrix.transpose_apply, Matrix.mul_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  ring

theorem kronecker_transpose_quadratic (B C Z : Matrix I I ℂ) :
    quadraticValue (B ⊗ₖ Cᵀ) (flatten Z) = (Zᴴ * B * Z * C).trace.re := by
  unfold quadraticValue
  rw [kronecker_transpose_mulVec_flatten, flatten_trace_pairing]
  simp only [Matrix.mul_assoc]

def relativeEntropyNats (A B : Matrix I I ℂ) : ℝ :=
  (A * (cfc Real.log A - cfc Real.log B)).trace.re

theorem finiteRelativeEntropyBits_eq_nats {A B : Matrix I I ℂ} (hA : A.IsHermitian) :
    finiteRelativeEntropyBits A B = relativeEntropyNats A B / Real.log 2 := by
  rw [finiteRelativeEntropyBits_eq_spectral hA, cfc_mulLog_eq_mul_log hA]
  simp [relativeEntropyNats, Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re]

theorem modular_log_quadratic {A B : Matrix I I ℂ} (hA : A.PosDef) (hB : B.PosDef) :
    quadraticValue (cfc Real.log (delta B A)) (flatten (CFC.sqrt A)) =
      -relativeEntropyNats A B := by
  have hs : (CFC.sqrt A).IsHermitian := (sqrt_posDef hA).1
  have htr : (CFC.sqrt A * cfc Real.log B * CFC.sqrt A).trace =
      (A * cfc Real.log B).trace := by
    rw [Matrix.trace_mul_cycle, CFC.sqrt_mul_sqrt_self A hA.posSemidef.nonneg]
  rw [cfc_log_delta hA hB, quadraticValue_sub]
  have hfirst : quadraticValue (cfc Real.log B ⊗ₖ (1 : Matrix I I ℂ))
      (flatten (CFC.sqrt A)) = (A * cfc Real.log B).trace.re := by
    have h := kronecker_transpose_quadratic (cfc Real.log B) (1 : Matrix I I ℂ) (CFC.sqrt A)
    simpa [hs.eq, htr] using h
  have hsecond : quadraticValue ((1 : Matrix I I ℂ) ⊗ₖ (cfc Real.log A)ᵀ)
      (flatten (CFC.sqrt A)) = (A * cfc Real.log A).trace.re := by
    have h := kronecker_transpose_quadratic (1 : Matrix I I ℂ) (cfc Real.log A) (CFC.sqrt A)
    simpa [hs.eq, CFC.sqrt_mul_sqrt_self A hA.posSemidef.nonneg] using h
  rw [hfirst, hsecond]
  simp [relativeEntropyNats, Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re]

end QuantumProver.SuperchannelDiscrimination.ModularMatrix

namespace QuantumProver.SuperchannelDiscrimination.LogCompression

open KrausCompletion CPWrappers CPJensen CPSchwarz MatrixLog ModularMatrix FlaggedStates
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator Matrix

variable {I O : Type*} [Fintype I] [Fintype O] [DecidableEq I] [DecidableEq O]

def residual (V : Matrix I O ℂ) : Matrix O O ℂ := 1 - Vᴴ * V

def dilation (V : Matrix I O ℂ) : Matrix (I ⊕ O) O ℂ :=
  Matrix.fromRows V (CFC.sqrt (residual V))

def compression (W : Matrix I O ℂ) : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ :=
  krausMap (fun _ : Unit => Wᴴ)

theorem compression_apply (W : Matrix I O ℂ) (X : Matrix I I ℂ) :
    compression W X = Wᴴ * X * W := by
  simp [compression, krausMap, krausAction]

theorem compression_cp (W : Matrix I O ℂ) : CompletelyPositive (compression W) := by
  intro r X hX
  exact krausMap_completelyPositive (fun _ : Unit => Wᴴ) (Fin r) hX

theorem dilation_isometry (V : Matrix I O ℂ) (hV : (residual V).PosSemidef) :
    (dilation V)ᴴ * dilation V = 1 := by
  have hs : (CFC.sqrt (residual V)).IsHermitian :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg _)).1
  rw [dilation, Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose,
    Matrix.fromCols_mul_fromRows, hs.eq, CFC.sqrt_mul_sqrt_self _ hV.nonneg]
  simp [residual]

theorem dilation_compression_unital (V : Matrix I O ℂ)
    (hV : (residual V).PosSemidef) : compression (dilation V) 1 = 1 := by
  rw [compression_apply, Matrix.mul_one, dilation_isometry V hV]

theorem block_posDef {X : Matrix I I ℂ} {Y : Matrix O O ℂ}
    (hX : X.PosDef) (hY : Y.PosDef) : (flagBlock X Y).PosDef := by
  have hp := flagBlock_posSemidef hX.posSemidef hY.posSemidef
  apply hp.posDef_iff_isUnit.mpr
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  rw [flagBlock, Matrix.det_fromBlocks_zero₁₂]
  exact ((Matrix.isUnit_iff_isUnit_det X).mp hX.isUnit).mul
    ((Matrix.isUnit_iff_isUnit_det Y).mp hY.isUnit)

theorem dilation_block_action (V : Matrix I O ℂ) (X : Matrix I I ℂ) (Y : Matrix O O ℂ) :
    compression (dilation V) (flagBlock X Y) = Vᴴ * X * V +
      (CFC.sqrt (residual V))ᴴ * Y * CFC.sqrt (residual V) := by
  simp [compression_apply, dilation, flagBlock,
    Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose,
    Matrix.fromCols_mul_fromBlocks, Matrix.fromCols_mul_fromRows]

theorem dilation_scalar_action (V : Matrix I O ℂ) (hV : (residual V).PosSemidef)
    (X : Matrix I I ℂ) (c : ℝ) :
    compression (dilation V) (flagBlock X (c • (1 : Matrix O O ℂ))) =
      Vᴴ * X * V + c • residual V := by
  have hs : (CFC.sqrt (residual V)).IsHermitian :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg _)).1
  rw [dilation_block_action, hs.eq]
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
    CFC.sqrt_mul_sqrt_self _ hV.nonneg]

theorem cfc_log_scalar (c : ℝ) :
    cfc Real.log (c • (1 : Matrix O O ℂ)) = Real.log c • (1 : Matrix O O ℂ) := by
  simpa only [Algebra.algebraMap_eq_smul_one] using
    cfc_algebraMap (R := ℝ) (A := Matrix O O ℂ) c Real.log

theorem quadratic_add (X Y : Matrix O O ℂ) (v : O → ℂ) :
    quadraticValue (X + Y) v = quadraticValue X v + quadraticValue Y v := by
  simp [quadraticValue, Matrix.add_mulVec, dotProduct_add, Complex.add_re]

theorem quadratic_smul (c : ℝ) (X : Matrix O O ℂ) (v : O → ℂ) :
    quadraticValue (c • X) v = c * quadraticValue X v := by
  simp [quadraticValue, Matrix.smul_mulVec, dotProduct_smul, Complex.smul_re, smul_eq_mul]

theorem dilation_log_quadratic (V : Matrix I O ℂ) (hV : (residual V).PosSemidef)
    {X : Matrix I I ℂ} (hX : X.PosDef) (c : ℝ) (v : O → ℂ) :
    quadraticValue (compression (dilation V)
      (cfc Real.log (flagBlock X (c • (1 : Matrix O O ℂ))))) v =
      quadraticValue (cfc Real.log X) (V *ᵥ v) + Real.log c * quadraticValue (residual V) v := by
  have hcH : (c • (1 : Matrix O O ℂ)).IsHermitian :=
    Matrix.isHermitian_one.smul (show IsSelfAdjoint c from rfl)
  rw [cfc_flagBlock Real.log hX.1 hcH, cfc_log_scalar,
    dilation_scalar_action V hV, quadratic_add, quadratic_congruence, quadratic_smul]

theorem log_quadratic_bound_shift (V : Matrix I O ℂ) (hV : (residual V).PosSemidef)
    {X : Matrix I I ℂ} {Y : Matrix O O ℂ} (hX : X.PosDef) (hY : Y.PosDef)
    (hXY : (Y - Vᴴ * X * V).PosSemidef) (v : O → ℂ)
    (hv : quadraticValue (residual V) v = 0) {c : ℝ} (hc : 0 < c) :
    quadraticValue (cfc Real.log X) (V *ᵥ v) ≤
      quadraticValue (cfc Real.log (Y + c • (1 : Matrix O O ℂ))) v := by
  let Φ := compression (dilation V)
  let B := flagBlock X (c • (1 : Matrix O O ℂ))
  have hb : B.PosDef := block_posDef hX (Matrix.PosDef.one.smul hc)
  have hcp := compression_cp (dilation V)
  have hu := dilation_compression_unital V hV
  have hPhi := map_posDef hcp hu hb
  have hJ := quadraticValue_nonneg (operator_log_jensen hcp hu hb) v
  rw [quadraticValue_sub, dilation_log_quadratic V hV hX c v, hv, mul_zero, add_zero] at hJ
  have hg := Matrix.posSemidef_conjTranspose_mul_self V
  have hdom : (Y + c • (1 : Matrix O O ℂ) - Φ B).PosSemidef := by
    have hsum := hXY.add (hg.smul hc.le)
    have heq : Y + c • (1 : Matrix O O ℂ) - Φ B =
        (Y - Vᴴ * X * V) + c • (Vᴴ * V) := by
      dsimp [Φ, B]
      rw [dilation_scalar_action V hV, residual, smul_sub]
      abel
    rw [heq]
    exact hsum
  have hM := quadraticValue_nonneg
    (operator_log_monotone hPhi (shift_posDef hY hc.le) hdom) v
  rw [quadraticValue_sub] at hM
  exact (sub_nonneg.mp hJ).trans (sub_nonneg.mp hM)

theorem shifted_log_cfc {X : Matrix O O ℂ} (hX : X.IsHermitian) (t : ℝ) :
    cfc Real.log (X + t • (1 : Matrix O O ℂ)) =
      cfc (fun x : ℝ => Real.log (x + t)) X := by
  have hshift : cfc (fun x : ℝ => x + t) X = X + t • (1 : Matrix O O ℂ) := by
    rw [cfc_add_const (p := IsSelfAdjoint) t (fun x : ℝ => x) X
      (X.finite_real_spectrum.continuousOn _) hX,
      cfc_id' (p := IsSelfAdjoint) ℝ X hX, Algebra.algebraMap_eq_smul_one]
  have hc := cfc_comp (p := IsSelfAdjoint) Real.log (fun x : ℝ => x + t) X hX
    ((X.finite_real_spectrum.image _).continuousOn _)
    (X.finite_real_spectrum.continuousOn _)
  rw [hshift] at hc
  exact hc.symm

set_option backward.isDefEq.respectTransparency false in

theorem log_quadratic_contraction (V : Matrix I O ℂ) (hV : (residual V).PosSemidef)
    {X : Matrix I I ℂ} {Y : Matrix O O ℂ} (hX : X.PosDef) (hY : Y.PosDef)
    (hXY : (Y - Vᴴ * X * V).PosSemidef) (v : O → ℂ)
    (hv : quadraticValue (residual V) v = 0) :
    quadraticValue (cfc Real.log X) (V *ᵥ v) ≤ quadraticValue (cfc Real.log Y) v := by
  let w : O → ℝ := fun i => Complex.normSq (eigenCoordinates hY.1 v i)
  let g : ℝ → ℝ := logShiftSum hY.1.eigenvalues w
  have heq (t : ℝ) : quadraticValue (cfc Real.log (Y + t • (1 : Matrix O O ℂ))) v = g t := by
    rw [shifted_log_cfc hY.1 t, quadraticValue_cfc_eq_sum _ hY.1]
    simp [g, w, logShiftSum, add_comm]
  have hd := logShiftSum_hasDerivAt hY.1.eigenvalues w 0
    (fun i => by simpa using ne_of_gt (hY.eigenvalues_pos i))
  have hlim : Tendsto g (𝓝[>] (0 : ℝ)) (𝓝 (g 0)) :=
    hd.continuousAt.tendsto.mono_left inf_le_left
  have hevent : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ),
      quadraticValue (cfc Real.log X) (V *ᵥ v) ≤ g t := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    rw [← heq t]
    exact log_quadratic_bound_shift V hV hX hY hXY v hv ht
  have h := ge_of_tendsto hlim hevent
  rw [← heq 0] at h
  simpa using h

end QuantumProver.SuperchannelDiscrimination.LogCompression

namespace QuantumProver.SuperchannelDiscrimination.ModularMatrix

open KrausCompletion CPWrappers CPJensen CPSchwarz MatrixLog TensorEntropy FlaggedStates LogCompression
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator Matrix Kronecker

variable {I O κ : Type*} [Fintype I] [Fintype O] [Fintype κ]
  [DecidableEq I] [DecidableEq O]

theorem identity_sqrt_quadratic {A : Matrix I I ℂ} (hA : A.PosSemidef) :
    quadraticValue 1 (flatten (CFC.sqrt A)) = A.trace.re := by
  have hs : (CFC.sqrt A).IsHermitian :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)).1
  rw [identity_quadratic, hs.eq, CFC.sqrt_mul_sqrt_self A hA.nonneg]

theorem pullback_residual_quadratic_zero (K : κ → Matrix O I ℂ)
    (hK : krausGram K = 1) {A : Matrix I I ℂ} (hA : A.PosSemidef)
    (hOut : (krausAction K A).PosDef) :
    quadraticValue (LogCompression.residual (pullbackMatrix K A))
      (flatten (CFC.sqrt (krausAction K A))) = 0 := by
  rw [LogCompression.residual, quadraticValue_sub, quadratic_gram, pullbackMatrix_sqrt K hK hOut,
    identity_sqrt_quadratic hOut.posSemidef, identity_sqrt_quadratic hA,
    krausAction_tracePreserving K hK A, sub_self]

theorem relativeEntropyNats_kraus_dpi_of_posDef (K : κ → Matrix O I ℂ)
    (hK : krausGram K = 1) {A B : Matrix I I ℂ} (hA : A.PosDef) (hB : B.PosDef)
    (hOutA : (krausAction K A).PosDef) (hOutB : (krausAction K B).PosDef) :
    relativeEntropyNats (krausAction K A) (krausAction K B) ≤ relativeEntropyNats A B := by
  have h := log_quadratic_contraction (pullbackMatrix K A)
    (pullbackMatrix_contraction K hK hA.posSemidef hOutA)
    (delta_posDef hA hB) (delta_posDef hOutA hOutB)
    (pullbackMatrix_modular_order K hK hA hB.posSemidef hOutA)
    (flatten (CFC.sqrt (krausAction K A)))
    (pullback_residual_quadratic_zero K hK hA.posSemidef hOutA)
  rw [pullbackMatrix_sqrt K hK hOutA, modular_log_quadratic hA hB,
    modular_log_quadratic hOutA hOutB] at h
  exact neg_le_neg_iff.mp h

theorem finiteRelativeEntropyBits_kraus_dpi_of_posDef (K : κ → Matrix O I ℂ)
    (hK : krausGram K = 1) {A B : Matrix I I ℂ} (hA : A.PosDef) (hB : B.PosDef)
    (hOutA : (krausAction K A).PosDef) (hOutB : (krausAction K B).PosDef) :
    finiteRelativeEntropyBits (krausAction K A) (krausAction K B) ≤ finiteRelativeEntropyBits A B := by
  rw [finiteRelativeEntropyBits_eq_nats hOutA.1, finiteRelativeEntropyBits_eq_nats hA.1]
  exact div_le_div_of_nonneg_right
    (relativeEntropyNats_kraus_dpi_of_posDef K hK hA hB hOutA hOutB)
    (le_of_lt (Real.log_pos (by norm_num)))

theorem relativeEntropyBits_kraus_dpi_of_posDef (K : κ → Matrix O I ℂ)
    (hK : krausGram K = 1) {A B : Matrix I I ℂ} (hA : A.PosDef) (hB : B.PosDef)
    (hOutA : (krausAction K A).PosDef) (hOutB : (krausAction K B).PosDef) :
    relativeEntropyBits (krausAction K A) (krausAction K B) ≤ relativeEntropyBits A B := by
  rw [relativeEntropyBits_of_posDef _ hOutB, relativeEntropyBits_of_posDef _ hB]
  exact_mod_cast finiteRelativeEntropyBits_kraus_dpi_of_posDef K hK hA hB hOutA hOutB

theorem delta_shift_posDef {A B : Matrix I I ℂ} (hA : A.PosDef) (hB : B.PosSemidef)
    {t : ℝ} (ht : 0 < t) : (delta B A + t • (1 : Matrix (I × I) (I × I) ℂ)).PosDef := by
  have hs := (Matrix.PosDef.one.smul ht).isStrictlyPositive.add_nonneg
    (delta_posSemidef hA hB).nonneg
  simpa only [add_comm] using Matrix.isStrictlyPositive_iff_posDef.mp hs

theorem delta_resolvent_cfc {A B : Matrix I I ℂ} (hA : A.PosDef) (hB : B.PosSemidef)
    {t : ℝ} (ht : 0 < t) :
    (delta B A + t • (1 : Matrix (I × I) (I × I) ℂ))⁻¹ =
      cfc (fun x : ℝ => (x + t)⁻¹) (delta B A) := by
  have hD := delta_posSemidef hA hB
  have hspec : ∀ x ∈ spectrum ℝ (delta B A), x + t ≠ 0 := by
    intro x hx
    rw [hD.1.spectrum_real_eq_range_eigenvalues] at hx
    obtain ⟨i, rfl⟩ := hx
    exact ne_of_gt (add_pos_of_nonneg_of_pos (hD.eigenvalues_nonneg i) ht)
  have hshift : cfc (fun x : ℝ => x + t) (delta B A) =
      delta B A + t • (1 : Matrix (I × I) (I × I) ℂ) := by
    rw [cfc_add_const (p := IsSelfAdjoint) t (fun x : ℝ => x) (delta B A)
      ((delta B A).finite_real_spectrum.continuousOn _) hD.1,
      cfc_id' (p := IsSelfAdjoint) ℝ (delta B A) hD.1, Algebra.algebraMap_eq_smul_one]
  have h := cfc_inv (p := IsSelfAdjoint) (f := fun x : ℝ => x + t)
    (a := delta B A) hspec ((delta B A).finite_real_spectrum.continuousOn _) hD.1
  rw [hshift, ← Matrix.nonsing_inv_eq_ringInverse] at h
  exact h.symm

end QuantumProver.SuperchannelDiscrimination.ModularMatrix

namespace QuantumProver.SuperchannelDiscrimination.EntropyContinuity

open Matrix KrausCompletion FlaggedStates ModularMatrix MatrixLog
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

variable {I O κ α : Type*} [Fintype I] [Fintype O] [Fintype κ]
  [DecidableEq I] [DecidableEq O]

theorem tendsto_mulLogCFC {l : Filter α} {X : α → Matrix I I ℂ}
    {A : Matrix I I ℂ} (hX : Tendsto X l (𝓝 A))
    (hHerm : ∀ᶠ x in l, (X x).IsHermitian) (hA : A.IsHermitian) :
    Tendsto (fun x => cfc (fun t : ℝ => t * Real.log t) (X x)) l
      (𝓝 (cfc (fun t : ℝ => t * Real.log t) A)) := by
  let r : ℝ := (‖A‖ + 1) * ‖(1 : Matrix I I ℂ)‖
  have hn : ∀ᶠ x in l, ‖X x‖ < ‖A‖ + 1 :=
    hX.norm.eventually (Iio_mem_nhds (lt_add_one ‖A‖))
  have hspec : ∀ᶠ x in l, spectrum ℝ (X x) ⊆ Metric.closedBall 0 r := by
    filter_upwards [hn] with x hx
    exact (spectrum.subset_closedBall_norm_mul (X x)).trans
      (Metric.closedBall_subset_closedBall
        (mul_le_mul_of_nonneg_right hx.le (norm_nonneg _)))
  have hspecA : spectrum ℝ A ⊆ Metric.closedBall 0 r :=
    (spectrum.subset_closedBall_norm_mul A).trans
      (Metric.closedBall_subset_closedBall
        (mul_le_mul_of_nonneg_right (by linarith : ‖A‖ ≤ ‖A‖ + 1) (norm_nonneg _)))
  exact hX.cfc (isCompact_closedBall (0 : ℝ) r) (fun t : ℝ => t * Real.log t)
    hspec (hHerm.mono fun _ h => h.isSelfAdjoint) hspecA hA.isSelfAdjoint
    Real.continuous_mul_log.continuousOn

def entropyTrace (A : Matrix I I ℂ) : ℝ :=
  (cfc (fun t : ℝ => t * Real.log t) A).trace.re

theorem tendsto_entropyTrace {l : Filter α} {X : α → Matrix I I ℂ}
    {A : Matrix I I ℂ} (hX : Tendsto X l (𝓝 A))
    (hHerm : ∀ᶠ x in l, (X x).IsHermitian) (hA : A.IsHermitian) :
    Tendsto (fun x => entropyTrace (X x)) l (𝓝 (entropyTrace A)) := by
  have ht : Continuous (fun M : Matrix I I ℂ => M.trace.re) := by fun_prop
  exact ht.continuousAt.tendsto.comp (tendsto_mulLogCFC hX hHerm hA)

theorem relativeEntropyNats_eq_entropyTrace {A B : Matrix I I ℂ}
    (hA : A.IsHermitian) :
    relativeEntropyNats A B = entropyTrace A - (A * cfc Real.log B).trace.re := by
  rw [entropyTrace, cfc_mulLog_eq_mul_log hA]
  simp [relativeEntropyNats, Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re]

theorem tendsto_relativeEntropyNats_left {l : Filter α} {X : α → Matrix I I ℂ}
    {A : Matrix I I ℂ} (B : Matrix I I ℂ) (hX : Tendsto X l (𝓝 A))
    (hHerm : ∀ᶠ x in l, (X x).IsHermitian) (hA : A.IsHermitian) :
    Tendsto (fun x => relativeEntropyNats (X x) B) l (𝓝 (relativeEntropyNats A B)) := by
  have ht : Continuous (fun M : Matrix I I ℂ => (M * cfc Real.log B).trace.re) := by
    fun_prop
  rw [relativeEntropyNats_eq_entropyTrace hA]
  apply ((tendsto_entropyTrace hX hHerm hA).sub
    (ht.continuousAt.tendsto.comp hX)).congr'
  filter_upwards [hHerm] with x hx
  exact (relativeEntropyNats_eq_entropyTrace hx).symm

theorem tendsto_finiteRelativeEntropyBits_left {l : Filter α} {X : α → Matrix I I ℂ}
    {A : Matrix I I ℂ} (B : Matrix I I ℂ) (hX : Tendsto X l (𝓝 A))
    (hHerm : ∀ᶠ x in l, (X x).IsHermitian) (hA : A.IsHermitian) :
    Tendsto (fun x => finiteRelativeEntropyBits (X x) B) l
      (𝓝 (finiteRelativeEntropyBits A B)) := by
  exact (tendsto_relativeEntropyNats_left B hX hHerm hA).div_const (Real.log 2)

theorem tendsto_relativeEntropyBits_left_of_posDef {l : Filter α}
    {X : α → Matrix I I ℂ} {A B : Matrix I I ℂ} (hB : B.PosDef)
    (hX : Tendsto X l (𝓝 A)) (hHerm : ∀ᶠ x in l, (X x).IsHermitian)
    (hA : A.IsHermitian) :
    Tendsto (fun x => relativeEntropyBits (X x) B) l (𝓝 (relativeEntropyBits A B)) := by
  simp_rw [relativeEntropyBits_of_posDef _ hB]
  exact EReal.tendsto_coe.mpr (tendsto_finiteRelativeEntropyBits_left B hX hHerm hA)

def regularizedNull (A B : Matrix I I ℂ) (δ : ℝ) : Matrix I I ℂ :=
  (1 - δ) • A + δ • B

theorem regularizedNull_posSemidef {A B : Matrix I I ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    (regularizedNull A B δ).PosSemidef :=
  (hA.smul (sub_nonneg.mpr hδ1)).add (hB.smul hδ0)

theorem regularizedNull_posDef {A B : Matrix I I ℂ}
    (hA : A.PosSemidef) (hB : B.PosDef) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    (regularizedNull A B δ).PosDef :=
  Matrix.PosDef.posSemidef_add (hA.smul (sub_nonneg.mpr hδ1)) (hB.smul hδ0)

theorem regularizedNull_continuous (A B : Matrix I I ℂ) :
    Continuous (regularizedNull A B) := by
  unfold regularizedNull
  fun_prop

theorem regularizedNull_tendsto (A B : Matrix I I ℂ) :
    Tendsto (regularizedNull A B) (𝓝 0) (𝓝 A) := by
  simpa [regularizedNull] using
    ((regularizedNull_continuous A B).continuousAt (x := (0 : ℝ))).tendsto

theorem krausAction_regularizedNull (K : κ → Matrix O I ℂ)
    (A B : Matrix I I ℂ) (δ : ℝ) :
    krausAction K (regularizedNull A B δ) =
      regularizedNull (krausAction K A) (krausAction K B) δ := by
  change (krausMap K) ((1 - δ) • A + δ • B) =
    (1 - δ) • (krausMap K) A + δ • (krausMap K) B
  rw [map_add, (krausMap K).map_smul_of_tower, (krausMap K).map_smul_of_tower]

theorem eventually_delta_unit :
    ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ), 0 < δ ∧ δ < 1 := by
  have hlt : ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ), δ < 1 :=
    (show ∀ᶠ δ : ℝ in 𝓝 (0 : ℝ), δ < 1 from
      Iio_mem_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hlt] with δ hδ0 hδ1
  exact ⟨hδ0, hδ1⟩

theorem eventually_regularizedNull_posSemidef {A B : Matrix I I ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ), (regularizedNull A B δ).PosSemidef := by
  filter_upwards [eventually_delta_unit] with δ hδ
  exact regularizedNull_posSemidef hA hB hδ.1.le hδ.2.le

theorem eventually_regularizedNull_posDef {A B : Matrix I I ℂ}
    (hA : A.PosSemidef) (hB : B.PosDef) :
    ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ), (regularizedNull A B δ).PosDef := by
  filter_upwards [eventually_delta_unit] with δ hδ
  exact regularizedNull_posDef hA hB hδ.1 hδ.2.le

theorem regularizedNull_entropyTrace_tendsto {A B : Matrix I I ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    Tendsto (fun δ => entropyTrace (regularizedNull A B δ)) (𝓝[>] (0 : ℝ))
      (𝓝 (entropyTrace A)) :=
  tendsto_entropyTrace ((regularizedNull_tendsto A B).mono_left nhdsWithin_le_nhds)
    ((eventually_regularizedNull_posSemidef hA hB).mono fun _ h => h.1) hA.1

theorem regularizedNull_relativeEntropyNats_tendsto {A B : Matrix I I ℂ}
    (hA : A.PosSemidef) (hB : B.PosDef) :
    Tendsto (fun δ => relativeEntropyNats (regularizedNull A B δ) B) (𝓝[>] (0 : ℝ))
      (𝓝 (relativeEntropyNats A B)) :=
  tendsto_relativeEntropyNats_left B
    ((regularizedNull_tendsto A B).mono_left nhdsWithin_le_nhds)
    ((eventually_regularizedNull_posDef hA hB).mono fun _ h => h.1) hA.1

theorem regularizedNull_finiteRelativeEntropyBits_tendsto {A B : Matrix I I ℂ}
    (hA : A.PosSemidef) (hB : B.PosDef) :
    Tendsto (fun δ => finiteRelativeEntropyBits (regularizedNull A B δ) B)
      (𝓝[>] (0 : ℝ)) (𝓝 (finiteRelativeEntropyBits A B)) :=
  tendsto_finiteRelativeEntropyBits_left B
    ((regularizedNull_tendsto A B).mono_left nhdsWithin_le_nhds)
    ((eventually_regularizedNull_posDef hA hB).mono fun _ h => h.1) hA.1

theorem regularizedNull_relativeEntropyBits_tendsto {A B : Matrix I I ℂ}
    (hA : A.PosSemidef) (hB : B.PosDef) :
    Tendsto (fun δ => relativeEntropyBits (regularizedNull A B δ) B)
      (𝓝[>] (0 : ℝ)) (𝓝 (relativeEntropyBits A B)) :=
  tendsto_relativeEntropyBits_left_of_posDef hB
    ((regularizedNull_tendsto A B).mono_left nhdsWithin_le_nhds)
    ((eventually_regularizedNull_posDef hA hB).mono fun _ h => h.1) hA.1

theorem krausAction_regularizedNull_posDef (K : κ → Matrix O I ℂ)
    {A B : Matrix I I ℂ} (hA : A.PosSemidef)
    (hOutB : (krausAction K B).PosDef) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    (krausAction K (regularizedNull A B δ)).PosDef := by
  rw [krausAction_regularizedNull]
  exact regularizedNull_posDef (krausAction_posSemidef K hA) hOutB hδ0 hδ1

theorem relativeEntropyNats_kraus_dpi_of_posSemidef (K : κ → Matrix O I ℂ)
    (hK : krausGram K = 1) {A B : Matrix I I ℂ} (hA : A.PosSemidef)
    (hB : B.PosDef) (hOutB : (krausAction K B).PosDef) :
    relativeEntropyNats (krausAction K A) (krausAction K B) ≤ relativeEntropyNats A B := by
  have hin := regularizedNull_relativeEntropyNats_tendsto hA hB
  have hout := regularizedNull_relativeEntropyNats_tendsto
    (krausAction_posSemidef K hA) hOutB
  have hineq : ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ),
      relativeEntropyNats (regularizedNull (krausAction K A) (krausAction K B) δ)
          (krausAction K B) ≤ relativeEntropyNats (regularizedNull A B δ) B := by
    filter_upwards [eventually_delta_unit] with δ hδ
    have h := ModularMatrix.relativeEntropyNats_kraus_dpi_of_posDef K hK
      (regularizedNull_posDef hA hB hδ.1 hδ.2.le) hB
      (krausAction_regularizedNull_posDef K hA hOutB hδ.1 hδ.2.le) hOutB
    simpa only [krausAction_regularizedNull] using h
  exact le_of_tendsto_of_tendsto hout hin hineq

theorem finiteRelativeEntropyBits_kraus_dpi_of_posSemidef (K : κ → Matrix O I ℂ)
    (hK : krausGram K = 1) {A B : Matrix I I ℂ} (hA : A.PosSemidef)
    (hB : B.PosDef) (hOutB : (krausAction K B).PosDef) :
    finiteRelativeEntropyBits (krausAction K A) (krausAction K B) ≤ finiteRelativeEntropyBits A B := by
  rw [finiteRelativeEntropyBits_eq_nats (krausAction_posSemidef K hA).1,
    finiteRelativeEntropyBits_eq_nats hA.1]
  exact div_le_div_of_nonneg_right
    (relativeEntropyNats_kraus_dpi_of_posSemidef K hK hA hB hOutB)
    (le_of_lt (Real.log_pos (by norm_num)))

theorem relativeEntropyBits_kraus_dpi_of_posSemidef (K : κ → Matrix O I ℂ)
    (hK : krausGram K = 1) {A B : Matrix I I ℂ} (hA : A.PosSemidef)
    (hB : B.PosDef) (hOutB : (krausAction K B).PosDef) :
    relativeEntropyBits (krausAction K A) (krausAction K B) ≤ relativeEntropyBits A B := by
  rw [relativeEntropyBits_of_posDef _ hOutB, relativeEntropyBits_of_posDef _ hB]
  exact_mod_cast finiteRelativeEntropyBits_kraus_dpi_of_posSemidef K hK hA hB hOutB

end QuantumProver.SuperchannelDiscrimination.EntropyContinuity

namespace QuantumProver.SuperchannelDiscrimination.ZeroExtension

open Matrix FlaggedStates TensorEntropy ModularMatrix EntropyContinuity
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

variable {J O : Type*} [Fintype J] [Fintype O] [DecidableEq J] [DecidableEq O]

def extend (U : Matrix O J ℂ) (X : Matrix J J ℂ) : Matrix O O ℂ := U * X * Uᴴ

theorem extend_isHermitian (U : Matrix O J ℂ) {X : Matrix J J ℂ}
    (hX : X.IsHermitian) : (extend U X).IsHermitian := by
  simp only [extend, Matrix.IsHermitian, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, hX.eq, Matrix.mul_assoc]

theorem extend_posSemidef (U : Matrix O J ℂ) {X : Matrix J J ℂ}
    (hX : X.PosSemidef) : (extend U X).PosSemidef :=
  hX.mul_mul_conjTranspose_same U

def embeddingHom (U : Matrix O J ℂ) (hU : Uᴴ * U = 1) :
    Matrix J J ℂ →⋆ₙₐ[ℝ] Matrix O O ℂ where
  toFun := extend U
  map_zero' := by simp [extend]
  map_add' X Y := by simp [extend, Matrix.mul_add, Matrix.add_mul]
  map_mul' X Y := by
    change U * (X * Y) * Uᴴ = (U * X * Uᴴ) * (U * Y * Uᴴ)
    symm
    calc
      (U * X * Uᴴ) * (U * Y * Uᴴ) = U * X * (Uᴴ * U) * Y * Uᴴ := by
        simp only [Matrix.mul_assoc]
      _ = U * (X * Y) * Uᴴ := by rw [hU]; simp [Matrix.mul_assoc]
  map_smul' r X := by simp [extend, Matrix.mul_smul, Matrix.smul_mul]
  map_star' X := by
    change U * Xᴴ * Uᴴ = (U * X * Uᴴ)ᴴ
    simp [Matrix.conjTranspose_mul, Matrix.mul_assoc]

theorem extend_mul (U : Matrix O J ℂ) (hU : Uᴴ * U = 1)
    (X Y : Matrix J J ℂ) : extend U X * extend U Y = extend U (X * Y) :=
  ((embeddingHom U hU).map_mul X Y).symm

theorem extend_trace (U : Matrix O J ℂ) (hU : Uᴴ * U = 1) (X : Matrix J J ℂ) :
    (extend U X).trace = X.trace := by
  rw [extend, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hU, Matrix.one_mul]

theorem finite_real_quasispectrum (X : Matrix J J ℂ) : (quasispectrum ℝ X).Finite := by
  rw [quasispectrum_eq_spectrum_union_zero]
  exact X.finite_real_spectrum.union (Set.finite_singleton 0)

theorem cfc_extend (U : Matrix O J ℂ) (hU : Uᴴ * U = 1) (f : ℝ → ℝ)
    (hf0 : f 0 = 0) {X : Matrix J J ℂ} (hX : X.IsHermitian) :
    cfc f (extend U X) = extend U (cfc f X) := by
  have hfX := (finite_real_quasispectrum X).continuousOn f
  have hfE := (finite_real_quasispectrum (extend U X)).continuousOn f
  have hcont : Continuous (embeddingHom U hU) := by
    change Continuous (fun X : Matrix J J ℂ => U * X * Uᴴ)
    fun_prop
  have h := (embeddingHom U hU).map_cfcₙ f X hfX hf0 hcont hX.isSelfAdjoint
    (extend_isHermitian U hX).isSelfAdjoint
  change extend U (cfcₙ f X) = cfcₙ f (extend U X) at h
  rw [cfcₙ_eq_cfc hfX hf0, cfcₙ_eq_cfc hfE hf0] at h
  exact h.symm

theorem entropyTrace_extend (U : Matrix O J ℂ) (hU : Uᴴ * U = 1)
    {X : Matrix J J ℂ} (hX : X.IsHermitian) : entropyTrace (extend U X) = entropyTrace X := by
  rw [entropyTrace, cfc_extend U hU (fun t : ℝ => t * Real.log t) (by simp) hX,
    extend_trace U hU]
  rfl

theorem comparatorLogTrace_extend (U : Matrix O J ℂ) (hU : Uᴴ * U = 1)
    (X : Matrix J J ℂ) {Y : Matrix J J ℂ} (hY : Y.IsHermitian) :
    (extend U X * cfc Real.log (extend U Y)).trace = (X * cfc Real.log Y).trace := by
  rw [cfc_extend U hU Real.log (by simp) hY, extend_mul U hU, extend_trace U hU]

theorem relativeEntropyNats_extend (U : Matrix O J ℂ) (hU : Uᴴ * U = 1)
    {X Y : Matrix J J ℂ} (hX : X.IsHermitian) (hY : Y.IsHermitian) :
    relativeEntropyNats (extend U X) (extend U Y) = relativeEntropyNats X Y := by
  rw [relativeEntropyNats_eq_entropyTrace (extend_isHermitian U hX),
    entropyTrace_extend U hU hX, comparatorLogTrace_extend U hU X hY,
    relativeEntropyNats_eq_entropyTrace hX]

theorem finiteRelativeEntropyBits_extend (U : Matrix O J ℂ) (hU : Uᴴ * U = 1)
    {X Y : Matrix J J ℂ} (hX : X.IsHermitian) (hY : Y.IsHermitian) :
    finiteRelativeEntropyBits (extend U X) (extend U Y) = finiteRelativeEntropyBits X Y := by
  rw [finiteRelativeEntropyBits_eq_nats (extend_isHermitian U hX),
    relativeEntropyNats_extend U hU hX hY, finiteRelativeEntropyBits_eq_nats hX]

theorem hasSupportIn_extend_of_posDef (U : Matrix O J ℂ) (hU : Uᴴ * U = 1)
    (X : Matrix J J ℂ) {Y : Matrix J J ℂ} (hY : Y.PosDef) :
    HasSupportIn (extend U X) (extend U Y) := by
  intro v hv
  have hy : Y *ᵥ (Uᴴ *ᵥ v) = 0 := by
    calc
      Y *ᵥ (Uᴴ *ᵥ v) = Uᴴ *ᵥ ((extend U Y) *ᵥ v) := by
        simp only [extend, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hU, Matrix.one_mul]
      _ = 0 := by rw [hv, Matrix.mulVec_zero]
  have hx := hasSupportIn_of_posDef X hY (Uᴴ *ᵥ v) hy
  calc
    (extend U X) *ᵥ v = U *ᵥ (X *ᵥ (Uᴴ *ᵥ v)) := by
      simp only [extend, Matrix.mulVec_mulVec, Matrix.mul_assoc]
    _ = 0 := by rw [hx, Matrix.mulVec_zero]

theorem relativeEntropyBits_extend_of_posDef (U : Matrix O J ℂ) (hU : Uᴴ * U = 1)
    {X Y : Matrix J J ℂ} (hX : X.PosSemidef) (hY : Y.PosDef) :
    relativeEntropyBits (extend U X) (extend U Y) = relativeEntropyBits X Y := by
  simp only [relativeEntropyBits, hasSupportIn_extend_of_posDef U hU X hY,
    hasSupportIn_of_posDef X hY, if_true, finiteRelativeEntropyBits_extend U hU hX.1 hY.1]

end QuantumProver.SuperchannelDiscrimination.ZeroExtension

namespace QuantumProver.SuperchannelDiscrimination.OutputSupport

open Matrix KrausCompletion FlaggedStates TensorEntropy ModularMatrix EntropyContinuity ZeroExtension
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Matrix

variable {I O κ : Type*} [Fintype I] [Fintype O] [Fintype κ]
  [DecidableEq I] [DecidableEq O]

theorem supportProjection_isHermitian {C : Matrix O O ℂ} (hC : C.IsHermitian) :
    (supportProjection C).IsHermitian :=
  cfc_predicate nonzeroWeight C

theorem supportProjection_mul_left {C : Matrix O O ℂ} (hC : C.IsHermitian) :
    supportProjection C * C = C := by
  have h := congrArg Matrix.conjTranspose (supportProjection_mul C hC)
  simpa only [Matrix.conjTranspose_mul, hC.eq, (supportProjection_isHermitian hC).eq] using h

theorem complement_mul_zero {C : Matrix O O ℂ} (hC : C.IsHermitian) :
    (1 - supportProjection C) * C = 0 := by
  rw [Matrix.sub_mul, Matrix.one_mul, supportProjection_mul_left hC, sub_self]

theorem supportProjection_idempotent {C : Matrix O O ℂ} (hC : C.IsHermitian) :
    supportProjection C * supportProjection C = supportProjection C := by
  have hf : (fun x : ℝ => nonzeroWeight x * nonzeroWeight x) = nonzeroWeight := by
    funext x
    by_cases hx : x = 0 <;> simp [nonzeroWeight, hx]
  rw [supportProjection, ← cfc_mul (p := IsSelfAdjoint) _ _ C
    (C.finite_real_spectrum.continuousOn _) (C.finite_real_spectrum.continuousOn _), hf]

theorem complement_posSemidef {C : Matrix O O ℂ} (hC : C.IsHermitian) :
    (1 - supportProjection C).PosSemidef := by
  have hQ : (1 - supportProjection C).IsHermitian := by
    change (1 - supportProjection C)ᴴ = 1 - supportProjection C
    simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_one,
      (supportProjection_isHermitian hC).eq]
  have hsq : (1 - supportProjection C) * (1 - supportProjection C) =
      1 - supportProjection C := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
      supportProjection_idempotent hC]
    abel
  have hgram := Matrix.posSemidef_self_mul_conjTranspose (1 - supportProjection C)
  have htranspose : (1 - supportProjection C)ᴴ = 1 - supportProjection C := hQ
  rw [htranspose, hsq] at hgram
  exact hgram

abbrev supportIndex {C : Matrix O O ℂ} (hC : C.PosSemidef) : Type _ :=
  {i : O // 0 < hC.1.eigenvalues i}

noncomputable instance supportIndex_fintype {C : Matrix O O ℂ} (hC : C.PosSemidef) :
    Fintype (supportIndex hC) := Fintype.ofFinite _

def supportIsometry {C : Matrix O O ℂ} (hC : C.PosSemidef) :
    Matrix O (supportIndex hC) ℂ :=
  fun i j => (hC.1.eigenvectorUnitary : Matrix O O ℂ) i j.val

set_option backward.isDefEq.respectTransparency false in
theorem supportIsometry_gram {C : Matrix O O ℂ} (hC : C.PosSemidef) :
    (supportIsometry hC)ᴴ * supportIsometry hC = 1 := by
  have hu : (hC.1.eigenvectorUnitary : Matrix O O ℂ)ᴴ *
      (hC.1.eigenvectorUnitary : Matrix O O ℂ) = 1 :=
    Unitary.coe_star_mul_self hC.1.eigenvectorUnitary
  ext i j
  have h := congrArg (fun M : Matrix O O ℂ => M i.val j.val) hu
  simpa [supportIsometry, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.one_apply, Subtype.ext_iff] using h

set_option backward.isDefEq.respectTransparency false in
theorem supportIsometry_comparator {C : Matrix O O ℂ} (hC : C.PosSemidef) :
    (supportIsometry hC)ᴴ * C * supportIsometry hC =
      Matrix.diagonal (fun i : supportIndex hC => (hC.1.eigenvalues i.val : ℂ)) := by
  have hd : (hC.1.eigenvectorUnitary : Matrix O O ℂ)ᴴ * C *
      (hC.1.eigenvectorUnitary : Matrix O O ℂ) =
      Matrix.diagonal (fun i => (hC.1.eigenvalues i : ℂ)) := by
    let E : Matrix O O ℂ := hC.1.eigenvectorUnitary
    let D : Matrix O O ℂ := Matrix.diagonal (fun i => (hC.1.eigenvalues i : ℂ))
    have hs := cfc_spectral (fun x : ℝ => x) hC.1
    rw [cfc_id' (p := IsSelfAdjoint) ℝ C hC.1] at hs
    change C = E * D * Eᴴ at hs
    have hu : Eᴴ * E = 1 := Unitary.coe_star_mul_self hC.1.eigenvectorUnitary
    change Eᴴ * C * E = D
    calc
      Eᴴ * C * E = Eᴴ * (E * D * Eᴴ) * E := by rw [hs]
      _ = (Eᴴ * E) * D * (Eᴴ * E) := by simp only [Matrix.mul_assoc]
      _ = D := by rw [hu]; simp
  ext i j
  have h := congrArg (fun M : Matrix O O ℂ => M i.val j.val) hd
  simpa [supportIsometry, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.diagonal_apply, Subtype.ext_iff] using h

theorem supportIsometry_comparator_posDef {C : Matrix O O ℂ} (hC : C.PosSemidef) :
    ((supportIsometry hC)ᴴ * C * supportIsometry hC).PosDef := by
  rw [supportIsometry_comparator hC, Matrix.posDef_diagonal_iff]
  intro i
  exact_mod_cast i.property

theorem supportIndex_sum {C : Matrix O O ℂ} (hC : C.PosSemidef) (f : O → ℂ) :
    (∑ i : supportIndex hC, f i.val) =
      ∑ i : O, if 0 < hC.1.eigenvalues i then f i else 0 := by
  classical
  rw [← Finset.sum_filter]
  exact (Finset.sum_subtype (Finset.univ.filter (fun i => 0 < hC.1.eigenvalues i))
    (by simp) f).symm

set_option backward.isDefEq.respectTransparency false in
theorem supportIsometry_projection {C : Matrix O O ℂ} (hC : C.PosSemidef) :
    supportIsometry hC * (supportIsometry hC)ᴴ = supportProjection C := by
  classical
  rw [supportProjection, cfc_spectral nonzeroWeight hC.1]
  change supportIsometry hC * (supportIsometry hC)ᴴ =
    (hC.1.eigenvectorUnitary : Matrix O O ℂ) *
      Matrix.diagonal (fun i => (nonzeroWeight (hC.1.eigenvalues i) : ℂ)) *
      (hC.1.eigenvectorUnitary : Matrix O O ℂ)ᴴ
  ext i j
  simp only [Matrix.mul_apply, Matrix.diagonal_apply, Matrix.conjTranspose_apply,
    mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, supportIsometry]
  rw [supportIndex_sum hC (fun k =>
    (hC.1.eigenvectorUnitary : Matrix O O ℂ) i k *
      star ((hC.1.eigenvectorUnitary : Matrix O O ℂ) j k))]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hk : 0 < hC.1.eigenvalues k
  · simp [hk, nonzeroWeight, ne_of_gt hk]
  · have hz : hC.1.eigenvalues k = 0 :=
      le_antisymm (le_of_not_gt hk) (hC.eigenvalues_nonneg k)
    simp [hk, nonzeroWeight, hz]

theorem kraus_supportProjection (K : κ → Matrix O I ℂ) {B : Matrix I I ℂ}
    (hB : B.PosDef) (k : κ) :
    supportProjection (krausAction K B) * K k = K k := by
  classical
  let C := krausAction K B
  let Q := 1 - supportProjection C
  let R := CFC.sqrt B
  let T : κ → Matrix O I ℂ := fun j => Q * K j * R
  have hC : C.PosSemidef := krausAction_posSemidef K hB.posSemidef
  have hQ : Q.IsHermitian := (complement_posSemidef hC.1).1
  have hR : R.PosDef := CPSchwarz.sqrt_posDef hB
  have hsquare (j : κ) : T j * (T j)ᴴ = Q * (K j * B * (K j)ᴴ) * Q := by
    calc
      T j * (T j)ᴴ = Q * K j * (R * R) * (K j)ᴴ * Q := by
        simp only [T, Matrix.conjTranspose_mul, hR.1.eq, hQ.eq, Matrix.mul_assoc]
      _ = Q * (K j * B * (K j)ᴴ) * Q := by
        rw [show R * R = B from CFC.sqrt_mul_sqrt_self B hB.posSemidef.nonneg]
        simp only [Matrix.mul_assoc]
  have hsum : (∑ j, T j * (T j)ᴴ) = Q * C * Q := by
    simp_rw [hsquare]
    simp only [C, krausAction, Matrix.mul_sum, Matrix.sum_mul]
  have hzero : Q * C * Q = 0 := by
    change (1 - supportProjection C) * C * Q = 0
    rw [complement_mul_zero hC.1, Matrix.zero_mul]
  have htrace : (∑ j, (T j * (T j)ᴴ).trace) = 0 := by
    rw [← Matrix.trace_sum, hsum, hzero, Matrix.trace_zero]
  have hk : (T k * (T k)ᴴ).trace = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun j _ =>
      (Matrix.posSemidef_self_mul_conjTranspose (T j)).trace_nonneg)).mp htrace k
      (Finset.mem_univ k)
  have hTk : T k = 0 := Matrix.trace_mul_conjTranspose_self_eq_zero_iff.mp hk
  letI : Invertible R := hR.isUnit.invertible
  have hQK : Q * K k = 0 := by
    calc
      Q * K k = (Q * K k * R) * R⁻¹ := by simp [Matrix.mul_assoc]
      _ = 0 := by change T k * R⁻¹ = 0; rw [hTk, Matrix.zero_mul]
  change (1 - supportProjection (krausAction K B)) * K k = 0 at hQK
  rw [Matrix.sub_mul, Matrix.one_mul] at hQK
  exact (sub_eq_zero.mp hQK).symm

abbrev krausSupportIndex (K : κ → Matrix O I ℂ) {B : Matrix I I ℂ} (hB : B.PosDef) :=
  supportIndex (krausAction_posSemidef K hB.posSemidef)

def krausSupportIsometry (K : κ → Matrix O I ℂ) {B : Matrix I I ℂ} (hB : B.PosDef) :
    Matrix O (krausSupportIndex K hB) ℂ :=
  supportIsometry (krausAction_posSemidef K hB.posSemidef)

def compressedKraus (K : κ → Matrix O I ℂ) {B : Matrix I I ℂ} (hB : B.PosDef) :
    κ → Matrix (krausSupportIndex K hB) I ℂ :=
  fun k => (krausSupportIsometry K hB)ᴴ * K k

theorem krausSupportIsometry_gram (K : κ → Matrix O I ℂ) {B : Matrix I I ℂ}
    (hB : B.PosDef) :
    (krausSupportIsometry K hB)ᴴ * krausSupportIsometry K hB = 1 :=
  supportIsometry_gram (krausAction_posSemidef K hB.posSemidef)

theorem compressedKraus_reconstruct (K : κ → Matrix O I ℂ) {B : Matrix I I ℂ}
    (hB : B.PosDef) (k : κ) :
    krausSupportIsometry K hB * compressedKraus K hB k = K k := by
  rw [compressedKraus, ← Matrix.mul_assoc]
  change (supportIsometry (krausAction_posSemidef K hB.posSemidef) *
    (supportIsometry (krausAction_posSemidef K hB.posSemidef))ᴴ) * K k = K k
  rw [supportIsometry_projection, kraus_supportProjection K hB k]

theorem compressedKraus_gram (K : κ → Matrix O I ℂ) (hK : krausGram K = 1)
    {B : Matrix I I ℂ} (hB : B.PosDef) : krausGram (compressedKraus K hB) = 1 := by
  classical
  let U := krausSupportIsometry K hB
  have hr (k : κ) : U * (Uᴴ * K k) = K k := compressedKraus_reconstruct K hB k
  calc
    krausGram (compressedKraus K hB) = ∑ k, (K k)ᴴ * (U * (Uᴴ * K k)) := by
      simp only [krausGram, compressedKraus, U, Matrix.conjTranspose_mul,
        Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
    _ = krausGram K := by simp_rw [hr]; rfl
    _ = 1 := hK

theorem compressedKraus_action (K : κ → Matrix O I ℂ) {B : Matrix I I ℂ}
    (hB : B.PosDef) (A : Matrix I I ℂ) :
    krausAction (compressedKraus K hB) A =
      (krausSupportIsometry K hB)ᴴ * krausAction K A * krausSupportIsometry K hB := by
  simp only [krausAction, compressedKraus, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_assoc]

set_option backward.isDefEq.respectTransparency false in

theorem krausAction_reconstruct (K : κ → Matrix O I ℂ) {B : Matrix I I ℂ}
    (hB : B.PosDef) (A : Matrix I I ℂ) :
    krausAction K A = extend (krausSupportIsometry K hB)
      (krausAction (compressedKraus K hB) A) := by
  classical
  let U := krausSupportIsometry K hB
  let L := compressedKraus K hB
  change (∑ k, K k * A * (K k)ᴴ) = U * (∑ k, L k * A * (L k)ᴴ) * Uᴴ
  simp only [Matrix.mul_sum, Matrix.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  have hr : U * L k = K k := compressedKraus_reconstruct K hB k
  calc
    K k * A * (K k)ᴴ = (U * L k) * A * (U * L k)ᴴ :=
      (congrArg (fun M : Matrix O I ℂ => M * A * Mᴴ) hr).symm
    _ = U * (L k * A * (L k)ᴴ) * Uᴴ := by
      simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]

theorem compressedKraus_comparator_posDef (K : κ → Matrix O I ℂ)
    {B : Matrix I I ℂ} (hB : B.PosDef) :
    (krausAction (compressedKraus K hB) B).PosDef := by
  rw [compressedKraus_action]
  exact supportIsometry_comparator_posDef (krausAction_posSemidef K hB.posSemidef)

theorem relativeEntropyNats_kraus_dpi (K : κ → Matrix O I ℂ) (hK : krausGram K = 1)
    {A B : Matrix I I ℂ} (hA : A.PosSemidef) (hB : B.PosDef) :
    relativeEntropyNats (krausAction K A) (krausAction K B) ≤ relativeEntropyNats A B := by
  have hcmp := compressedKraus_comparator_posDef K hB
  have h := EntropyContinuity.relativeEntropyNats_kraus_dpi_of_posSemidef
    (compressedKraus K hB) (compressedKraus_gram K hK hB) hA hB hcmp
  have heq : relativeEntropyNats (krausAction K A) (krausAction K B) =
      relativeEntropyNats (krausAction (compressedKraus K hB) A)
        (krausAction (compressedKraus K hB) B) := by
    calc
      _ = relativeEntropyNats (extend (krausSupportIsometry K hB)
          (krausAction (compressedKraus K hB) A))
          (extend (krausSupportIsometry K hB) (krausAction (compressedKraus K hB) B)) :=
        congrArg₂ relativeEntropyNats (krausAction_reconstruct K hB A)
          (krausAction_reconstruct K hB B)
      _ = _ := relativeEntropyNats_extend (krausSupportIsometry K hB)
        (krausSupportIsometry_gram K hB)
        (krausAction_posSemidef (compressedKraus K hB) hA).1 hcmp.1
  exact heq.le.trans h

theorem finiteRelativeEntropyBits_kraus_dpi (K : κ → Matrix O I ℂ) (hK : krausGram K = 1)
    {A B : Matrix I I ℂ} (hA : A.PosSemidef) (hB : B.PosDef) :
    finiteRelativeEntropyBits (krausAction K A) (krausAction K B) ≤ finiteRelativeEntropyBits A B := by
  rw [finiteRelativeEntropyBits_eq_nats (krausAction_posSemidef K hA).1,
    finiteRelativeEntropyBits_eq_nats hA.1]
  exact div_le_div_of_nonneg_right (relativeEntropyNats_kraus_dpi K hK hA hB)
    (le_of_lt (Real.log_pos (by norm_num)))

theorem relativeEntropyBits_kraus_dpi (K : κ → Matrix O I ℂ) (hK : krausGram K = 1)
    {A B : Matrix I I ℂ} (hA : A.PosSemidef) (hB : B.PosDef) :
    relativeEntropyBits (krausAction K A) (krausAction K B) ≤ relativeEntropyBits A B := by
  have hcmp := compressedKraus_comparator_posDef K hB
  have h := EntropyContinuity.relativeEntropyBits_kraus_dpi_of_posSemidef
    (compressedKraus K hB) (compressedKraus_gram K hK hB) hA hB hcmp
  have heq : relativeEntropyBits (krausAction K A) (krausAction K B) =
      relativeEntropyBits (krausAction (compressedKraus K hB) A)
        (krausAction (compressedKraus K hB) B) := by
    calc
      _ = relativeEntropyBits (extend (krausSupportIsometry K hB)
          (krausAction (compressedKraus K hB) A))
          (extend (krausSupportIsometry K hB) (krausAction (compressedKraus K hB) B)) :=
        congrArg₂ relativeEntropyBits (krausAction_reconstruct K hB A)
          (krausAction_reconstruct K hB B)
      _ = _ := relativeEntropyBits_extend_of_posDef (krausSupportIsometry K hB)
        (krausSupportIsometry_gram K hB)
        (krausAction_posSemidef (compressedKraus K hB) hA) hcmp
  exact heq.le.trans h

theorem supportIndex_nonempty_of_trace_pos {C : Matrix O O ℂ} (hC : C.PosSemidef)
    (ht : 0 < C.trace.re) : Nonempty (supportIndex hC) := by
  classical
  by_contra h
  have hz (i : O) : hC.1.eigenvalues i = 0 := by
    have hp : ¬ 0 < hC.1.eigenvalues i := fun hi => h ⟨⟨i, hi⟩⟩
    exact le_antisymm (le_of_not_gt hp) (hC.eigenvalues_nonneg i)
  have htrace : C.trace.re = 0 := by
    rw [Klein.trace_eq_sum_eigenvalues_re hC.1]
    simp_rw [hz]
    simp
  exact (ne_of_gt ht) htrace

theorem krausSupportIndex_nonempty_of_trace_pos (K : κ → Matrix O I ℂ)
    (hK : krausGram K = 1) {B : Matrix I I ℂ} (hB : B.PosDef)
    (ht : 0 < B.trace.re) : Nonempty (krausSupportIndex K hB) := by
  apply supportIndex_nonempty_of_trace_pos (krausAction_posSemidef K hB.posSemidef)
  rw [krausAction_tracePreserving K hK B]
  exact ht

theorem input_isEmpty_of_support_empty (K : κ → Matrix O I ℂ) (hK : krausGram K = 1)
    {B : Matrix I I ℂ} (hB : B.PosDef) (hS : ¬ Nonempty (krausSupportIndex K hB)) :
    IsEmpty I := by
  classical
  refine ⟨fun i => ?_⟩
  haveI : Nonempty I := ⟨i⟩
  have ht : 0 < B.trace.re := by
    rw [Klein.trace_eq_sum_eigenvalues_re hB.1]
    exact Finset.sum_pos (fun j _ => hB.eigenvalues_pos j) Finset.univ_nonempty
  exact hS (krausSupportIndex_nonempty_of_trace_pos K hK hB ht)

end QuantumProver.SuperchannelDiscrimination.OutputSupport

namespace QuantumProver.SuperchannelDiscrimination.ZeroExtension

open Matrix FlaggedStates

variable {J O : Type*} [Fintype J] [Fintype O] [DecidableEq J] [DecidableEq O]

theorem pullback_mulVec (U : Matrix O J ℂ) (hU : Uᴴ * U = 1)
    (X : Matrix J J ℂ) (v : O → ℂ) :
    Uᴴ *ᵥ ((extend U X) *ᵥ v) = X *ᵥ (Uᴴ *ᵥ v) := by
  simp only [extend, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hU, Matrix.one_mul]

theorem hasSupportIn_extend_iff (U : Matrix O J ℂ) (hU : Uᴴ * U = 1)
    (X Y : Matrix J J ℂ) :
    HasSupportIn (extend U X) (extend U Y) ↔ HasSupportIn X Y := by
  constructor
  · intro hs v hv
    have hY : (extend U Y) *ᵥ (U *ᵥ v) = 0 := by
      calc
        _ = U *ᵥ (Y *ᵥ v) := by
          simp only [extend, Matrix.mulVec_mulVec, Matrix.mul_assoc, hU, Matrix.mul_one]
        _ = 0 := by rw [hv, Matrix.mulVec_zero]
    have hX := hs (U *ᵥ v) hY
    have hX' : X *ᵥ (Uᴴ *ᵥ (U *ᵥ v)) = 0 := by
      rw [← pullback_mulVec U hU X (U *ᵥ v), hX, Matrix.mulVec_zero]
    simpa only [Matrix.mulVec_mulVec, hU, Matrix.one_mulVec] using hX'
  · intro hs v hv
    have hY : Y *ᵥ (Uᴴ *ᵥ v) = 0 := by
      rw [← pullback_mulVec U hU Y v, hv, Matrix.mulVec_zero]
    have hX := hs (Uᴴ *ᵥ v) hY
    calc
      (extend U X) *ᵥ v = U *ᵥ (X *ᵥ (Uᴴ *ᵥ v)) := by
        simp only [extend, Matrix.mulVec_mulVec, Matrix.mul_assoc]
      _ = 0 := by rw [hX, Matrix.mulVec_zero]

theorem relativeEntropyBits_extend (U : Matrix O J ℂ) (hU : Uᴴ * U = 1)
    {X Y : Matrix J J ℂ} (hX : X.IsHermitian) (hY : Y.IsHermitian) :
    relativeEntropyBits (extend U X) (extend U Y) = relativeEntropyBits X Y := by
  classical
  by_cases hs : HasSupportIn X Y
  · have hsE : HasSupportIn (extend U X) (extend U Y) :=
      (hasSupportIn_extend_iff U hU X Y).mpr hs
    rw [relativeEntropyBits, if_pos hsE, relativeEntropyBits, if_pos hs]
    exact congrArg (fun r : ℝ => (r : EReal))
      (finiteRelativeEntropyBits_extend U hU hX hY)
  · have hsE : ¬ HasSupportIn (extend U X) (extend U Y) :=
      fun h => hs ((hasSupportIn_extend_iff U hU X Y).mp h)
    rw [relativeEntropyBits, if_neg hsE, relativeEntropyBits, if_neg hs]

end QuantumProver.SuperchannelDiscrimination.ZeroExtension

namespace QuantumProver.SuperchannelDiscrimination.InputSupport

open Matrix KrausCompletion FlaggedStates TensorEntropy ModularMatrix OutputSupport ZeroExtension
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Matrix

variable {I O κ : Type*} [Fintype I] [Fintype O] [Fintype κ]
  [DecidableEq I] [DecidableEq O]

theorem supportProjection_mul_right_of_hasSupportIn {A B : Matrix I I ℂ}
    (hB : B.IsHermitian) (hs : HasSupportIn A B) : A * supportProjection B = A := by
  have hBQ : B * (1 - supportProjection B) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, supportProjection_mul B hB, sub_self]
  have hAQ : A * (1 - supportProjection B) = 0 := by
    apply Matrix.ext_iff_mulVec.mpr
    intro v
    have hBv : B *ᵥ ((1 - supportProjection B) *ᵥ v) = 0 := by
      rw [Matrix.mulVec_mulVec, hBQ, Matrix.zero_mulVec]
    simpa only [Matrix.mulVec_mulVec, Matrix.zero_mulVec] using
      hs ((1 - supportProjection B) *ᵥ v) hBv
  have h := hAQ
  rw [Matrix.mul_sub, Matrix.mul_one] at h
  exact (sub_eq_zero.mp h).symm

theorem supportProjection_mul_left_of_hasSupportIn {A B : Matrix I I ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (hs : HasSupportIn A B) :
    supportProjection B * A = A := by
  have h := congrArg Matrix.conjTranspose
    (supportProjection_mul_right_of_hasSupportIn hB hs)
  simpa only [Matrix.conjTranspose_mul, hA.eq,
    (supportProjection_isHermitian hB).eq] using h

def compress {B : Matrix I I ℂ} (hB : B.PosSemidef) (A : Matrix I I ℂ) :
    Matrix (supportIndex hB) (supportIndex hB) ℂ :=
  (supportIsometry hB)ᴴ * A * supportIsometry hB

theorem compress_isHermitian {A B : Matrix I I ℂ} (hB : B.PosSemidef)
    (hA : A.IsHermitian) : (compress hB A).IsHermitian := by
  change ((supportIsometry hB)ᴴ * A * supportIsometry hB)ᴴ =
    (supportIsometry hB)ᴴ * A * supportIsometry hB
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    hA.eq, Matrix.mul_assoc]

theorem compress_posSemidef {A B : Matrix I I ℂ} (hB : B.PosSemidef)
    (hA : A.PosSemidef) : (compress hB A).PosSemidef := by
  simpa only [compress, Matrix.conjTranspose_conjTranspose] using
    hA.mul_mul_conjTranspose_same (supportIsometry hB)ᴴ

theorem compress_comparator_posDef {B : Matrix I I ℂ} (hB : B.PosSemidef) :
    (compress hB B).PosDef := supportIsometry_comparator_posDef hB

theorem reconstruct_of_hasSupportIn {A B : Matrix I I ℂ}
    (hA : A.IsHermitian) (hB : B.PosSemidef) (hs : HasSupportIn A B) :
    A = extend (supportIsometry hB) (compress hB A) := by
  symm
  calc
    extend (supportIsometry hB) (compress hB A) =
        (supportIsometry hB * (supportIsometry hB)ᴴ) * A *
          (supportIsometry hB * (supportIsometry hB)ᴴ) := by
      simp only [extend, compress, Matrix.mul_assoc]
    _ = supportProjection B * A * supportProjection B := by
      rw [supportIsometry_projection hB]
    _ = A := by
      rw [supportProjection_mul_left_of_hasSupportIn hA hB.1 hs,
        supportProjection_mul_right_of_hasSupportIn hB.1 hs]

theorem reconstruct_comparator {B : Matrix I I ℂ} (hB : B.PosSemidef) :
    B = extend (supportIsometry hB) (compress hB B) :=
  reconstruct_of_hasSupportIn hB.1 hB (hasSupportIn_self B)

def inputCompressedKraus (K : κ → Matrix O I ℂ) {B : Matrix I I ℂ}
    (hB : B.PosSemidef) : κ → Matrix O (supportIndex hB) ℂ :=
  fun k => K k * supportIsometry hB

theorem inputCompressedKraus_gram (K : κ → Matrix O I ℂ) (hK : krausGram K = 1)
    {B : Matrix I I ℂ} (hB : B.PosSemidef) :
    krausGram (inputCompressedKraus K hB) = 1 := by
  calc
    krausGram (inputCompressedKraus K hB) =
        (supportIsometry hB)ᴴ * krausGram K * supportIsometry hB := by
      simp only [krausGram, inputCompressedKraus, Matrix.conjTranspose_mul,
        Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_assoc]
    _ = 1 := by rw [hK, Matrix.mul_one, supportIsometry_gram hB]

theorem inputCompressedKraus_action (K : κ → Matrix O I ℂ)
    {B : Matrix I I ℂ} (hB : B.PosSemidef)
    (X : Matrix (supportIndex hB) (supportIndex hB) ℂ) :
    krausAction (inputCompressedKraus K hB) X =
      krausAction K (extend (supportIsometry hB) X) := by
  simp only [krausAction, inputCompressedKraus, extend, Matrix.conjTranspose_mul,
    Matrix.mul_assoc]

theorem krausAction_eq_inputCompression (K : κ → Matrix O I ℂ)
    {A B : Matrix I I ℂ} (hA : A.IsHermitian) (hB : B.PosSemidef)
    (hs : HasSupportIn A B) :
    krausAction K A = krausAction (inputCompressedKraus K hB) (compress hB A) := by
  calc
    krausAction K A = krausAction K (extend (supportIsometry hB) (compress hB A)) :=
      congrArg (krausAction K) (reconstruct_of_hasSupportIn hA hB hs)
    _ = _ := (inputCompressedKraus_action K hB (compress hB A)).symm

theorem relativeEntropyBits_eq_compressed {A B : Matrix I I ℂ}
    (hA : A.IsHermitian) (hB : B.PosSemidef) (hs : HasSupportIn A B) :
    relativeEntropyBits A B = relativeEntropyBits (compress hB A) (compress hB B) := by
  calc
    relativeEntropyBits A B =
        relativeEntropyBits (extend (supportIsometry hB) (compress hB A))
          (extend (supportIsometry hB) (compress hB B)) :=
      congrArg₂ relativeEntropyBits (reconstruct_of_hasSupportIn hA hB hs)
        (reconstruct_comparator hB)
    _ = _ := relativeEntropyBits_extend (supportIsometry hB) (supportIsometry_gram hB)
      (compress_isHermitian hB hA) (compress_isHermitian hB hB.1)

theorem relativeEntropyBits_kraus_dpi_of_hasSupportIn (K : κ → Matrix O I ℂ)
    (hK : krausGram K = 1) {A B : Matrix I I ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) (hs : HasSupportIn A B) :
    relativeEntropyBits (krausAction K A) (krausAction K B) ≤ relativeEntropyBits A B := by
  have h := OutputSupport.relativeEntropyBits_kraus_dpi (inputCompressedKraus K hB)
    (inputCompressedKraus_gram K hK hB) (compress_posSemidef hB hA)
    (compress_comparator_posDef hB)
  calc
    relativeEntropyBits (krausAction K A) (krausAction K B) =
        relativeEntropyBits (krausAction (inputCompressedKraus K hB) (compress hB A))
          (krausAction (inputCompressedKraus K hB) (compress hB B)) :=
      congrArg₂ relativeEntropyBits (krausAction_eq_inputCompression K hA.1 hB hs)
        (krausAction_eq_inputCompression K hB.1 hB (hasSupportIn_self B))
    _ ≤ relativeEntropyBits (compress hB A) (compress hB B) := h
    _ = relativeEntropyBits A B := (relativeEntropyBits_eq_compressed hA.1 hB hs).symm

theorem relativeEntropyBits_kraus_dpi (K : κ → Matrix O I ℂ)
    (hK : krausGram K = 1) {A B : Matrix I I ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    relativeEntropyBits (krausAction K A) (krausAction K B) ≤ relativeEntropyBits A B := by
  classical
  by_cases hs : HasSupportIn A B
  · exact relativeEntropyBits_kraus_dpi_of_hasSupportIn K hK hA hB hs
  · rw [(relativeEntropyBits_eq_top_iff A B).mpr hs]
    exact le_top

theorem numerator_eq_zero_of_zero_comparator (A : Matrix I I ℂ)
    (hs : HasSupportIn A 0) : A = 0 := by
  apply Matrix.ext_iff_mulVec.mpr
  intro v
  simpa only [Matrix.zero_mulVec] using hs v (Matrix.zero_mulVec v)

theorem comparator_eq_zero_of_empty_support {B : Matrix I I ℂ}
    (hB : B.PosSemidef) [IsEmpty (supportIndex hB)] : B = 0 := by
  ext i j
  have h := congrArg (fun M : Matrix I I ℂ => M i j) (reconstruct_comparator hB)
  simpa [extend, Matrix.mul_apply] using h

theorem numerator_eq_zero_of_empty_support {A B : Matrix I I ℂ}
    (hB : B.PosSemidef) [IsEmpty (supportIndex hB)] (hs : HasSupportIn A B) : A = 0 := by
  have hB0 := comparator_eq_zero_of_empty_support hB
  have hs0 : HasSupportIn A 0 := by simpa only [hB0] using hs
  exact numerator_eq_zero_of_zero_comparator A hs0

end QuantumProver.SuperchannelDiscrimination.InputSupport

namespace QuantumProver.SuperchannelDiscrimination.AbstractDPI

open Matrix KrausCompletion CPWrappers FlaggedStates
open scoped BigOperators ComplexOrder MatrixOrder Matrix

variable {I O : Type*} [Fintype I] [Fintype O] [DecidableEq I] [DecidableEq O]

theorem amplify_eq (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ)
    (R : Type*) [Fintype R] (A : Matrix (I × R) (I × R) ℂ) :
    KrausCompletion.amplify Φ R A = CPTPKraus.amplify Φ R A := rfl

theorem completelyPositive_iff (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) :
    CPWrappers.CompletelyPositive Φ ↔ CPTPKraus.CompletelyPositive Φ := Iff.rfl

theorem tracePreserving_iff (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) :
    (∀ A : Matrix I I ℂ, (Φ A).trace = A.trace) ↔ CPTPKraus.TracePreserving Φ := Iff.rfl

theorem canonicalKraus_complete (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ)
    (hCP : CPWrappers.CompletelyPositive Φ)
    (hTP : ∀ A : Matrix I I ℂ, (Φ A).trace = A.trace) :
    krausGram (CPTPKraus.canonicalKraus Φ) = 1 :=
  CPTPKraus.canonicalKraus_gram Φ ((completelyPositive_iff Φ).mp hCP)
    ((tracePreserving_iff Φ).mp hTP)

theorem canonicalKraus_reconstruct (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ)
    (hCP : CPWrappers.CompletelyPositive Φ) (A : Matrix I I ℂ) :
    Φ A = krausAction (CPTPKraus.canonicalKraus Φ) A :=
  CPTPKraus.canonicalKraus_reconstruct Φ ((completelyPositive_iff Φ).mp hCP) A

theorem exists_complete_kraus (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ)
    (hCP : CPWrappers.CompletelyPositive Φ)
    (hTP : ∀ A : Matrix I I ℂ, (Φ A).trace = A.trace) :
    ∃ K : I × O → Matrix O I ℂ, krausGram K = 1 ∧
      ∀ A : Matrix I I ℂ, Φ A = krausAction K A :=
  ⟨CPTPKraus.canonicalKraus Φ, canonicalKraus_complete Φ hCP hTP,
    canonicalKraus_reconstruct Φ hCP⟩

theorem relativeEntropyBits_map_dpi (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ)
    (hCP : CPWrappers.CompletelyPositive Φ)
    (hTP : ∀ X : Matrix I I ℂ, (Φ X).trace = X.trace)
    {A B : Matrix I I ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    relativeEntropyBits (Φ A) (Φ B) ≤ relativeEntropyBits A B := by
  calc
    relativeEntropyBits (Φ A) (Φ B) =
        relativeEntropyBits (krausAction (CPTPKraus.canonicalKraus Φ) A)
          (krausAction (CPTPKraus.canonicalKraus Φ) B) :=
      congrArg₂ relativeEntropyBits (canonicalKraus_reconstruct Φ hCP A)
        (canonicalKraus_reconstruct Φ hCP B)
    _ ≤ _ := InputSupport.relativeEntropyBits_kraus_dpi (CPTPKraus.canonicalKraus Φ)
      (canonicalKraus_complete Φ hCP hTP) hA hB

theorem relativeEntropyBits_cptp_dpi (Φ : FiniteCPTP I O)
    {A B : Matrix I I ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    relativeEntropyBits (Φ.map A) (Φ.map B) ≤ relativeEntropyBits A B :=
  relativeEntropyBits_map_dpi Φ.map Φ.completelyPositive Φ.tracePreserving hA hB

theorem relativeEntropyBits_map_amplify_dpi
    (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) (hCP : CPWrappers.CompletelyPositive Φ)
    (hTP : ∀ X : Matrix I I ℂ, (Φ X).trace = X.trace)
    (R : Type*) [Fintype R] [DecidableEq R]
    {A B : Matrix (I × R) (I × R) ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    relativeEntropyBits (amplifyMap Φ R A) (amplifyMap Φ R B) ≤ relativeEntropyBits A B :=
  relativeEntropyBits_map_dpi (amplifyMap Φ R) (completelyPositive_amplifyMap hCP R)
    (amplifyMap_tracePreserving Φ hTP R) hA hB

theorem relativeEntropyBits_cptp_amplify_dpi (Φ : FiniteCPTP I O)
    (R : Type*) [Fintype R] [DecidableEq R]
    {A B : Matrix (I × R) (I × R) ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    relativeEntropyBits (KrausCompletion.amplify Φ.map R A)
      (KrausCompletion.amplify Φ.map R B) ≤ relativeEntropyBits A B :=
  relativeEntropyBits_cptp_dpi (amplifiedChannel Φ R) hA hB

theorem relativeEntropyBits_cptp_amplifyLeft_dpi (Φ : FiniteCPTP I O)
    (R : Type*) [Fintype R] [DecidableEq R]
    {A B : Matrix (R × I) (R × I) ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    relativeEntropyBits (amplifyLeftMap Φ.map R A)
      (amplifyLeftMap Φ.map R B) ≤ relativeEntropyBits A B :=
  relativeEntropyBits_cptp_dpi (amplifiedLeftChannel Φ R) hA hB

end QuantumProver.SuperchannelDiscrimination.AbstractDPI

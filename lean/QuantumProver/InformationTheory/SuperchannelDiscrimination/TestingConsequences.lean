import QuantumProver.InformationTheory.SuperchannelDiscrimination.StrategyAssembly
import QuantumProver.InformationTheory.SuperchannelDiscrimination.QuantumSteinAchievability
import QuantumProver.InformationTheory.SuperchannelDiscrimination.PetzSmoothing

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Matrix Filter
open scoped BigOperators Topology ComplexOrder MatrixOrder Matrix Kronecker

namespace QuantumProver.SuperchannelDiscrimination.Corollaries

open FlaggedStates TensorPinching

universe u

variable {I J : Type u} [Fintype I] [Fintype J]
  [DecidableEq I] [DecidableEq J]

def recursiveIsometry (U : Matrix I J ℂ) : (n : ℕ) →
    Matrix (RecursiveRows I n) (RecursiveRows J n) ℂ
  | 0 => (1 : Matrix (RecursiveRows I 0) (RecursiveRows I 0) ℂ)
  | n + 1 => recursiveIsometry U n ⊗ₖ U

theorem recursiveIsometry_gram (U : Matrix I J ℂ) (hU : Uᴴ * U = 1) (n : ℕ) :
    (recursiveIsometry U n)ᴴ * recursiveIsometry U n = 1 := by
  induction n with
  | zero =>
      change (1 : Matrix PUnit PUnit ℂ)ᴴ * (1 : Matrix PUnit PUnit ℂ) =
        (1 : Matrix PUnit PUnit ℂ)
      simp only [Matrix.conjTranspose_one, Matrix.one_mul]
  | succ n ih =>
      change (recursiveIsometry U n ⊗ₖ U)ᴴ *
        (recursiveIsometry U n ⊗ₖ U) = 1
      rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
        ih, hU, Matrix.one_kronecker_one]

theorem isometry_complement_posSemidef (U : Matrix I J ℂ) (hU : Uᴴ * U = 1) :
    (1 - U * Uᴴ).PosSemidef := by
  have hproj : (U * Uᴴ) * (U * Uᴴ) = U * Uᴴ := by
    calc
      (U * Uᴴ) * (U * Uᴴ) = U * (Uᴴ * U) * Uᴴ := by
        simp only [Matrix.mul_assoc]
      _ = U * Uᴴ := by rw [hU]; simp
  have hself : (1 - U * Uᴴ)ᴴ = 1 - U * Uᴴ := by
    simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_one,
      Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  have hsquare : (1 - U * Uᴴ) * (1 - U * Uᴴ) = 1 - U * Uᴴ := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul,
      Matrix.mul_one, hproj]
    abel
  have h := Matrix.posSemidef_conjTranspose_mul_self (1 - U * Uᴴ)
  rw [hself, hsquare] at h
  exact h

theorem extend_isEffect (U : Matrix I J ℂ) (hU : Uᴴ * U = 1)
    {E : Matrix J J ℂ} (hE : IsEffect E) : IsEffect (ZeroExtension.extend U E) := by
  refine ⟨ZeroExtension.extend_posSemidef U hE.1, ?_⟩
  have heq : 1 - ZeroExtension.extend U E =
      (1 - U * Uᴴ) + ZeroExtension.extend U (1 - E) := by
    simp only [ZeroExtension.extend, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one]
    abel
  rw [heq]
  exact (isometry_complement_posSemidef U hU).add
    (ZeroExtension.extend_posSemidef U hE.2)

theorem extend_isDensity (U : Matrix I J ℂ) (hU : Uᴴ * U = 1)
    {ρ : Matrix J J ℂ} (hρ : IsDensity ρ) : IsDensity (ZeroExtension.extend U ρ) :=
  ⟨ZeroExtension.extend_posSemidef U hρ.1,
    by rw [ZeroExtension.extend_trace U hU, hρ.2]⟩

theorem acceptanceProbability_extend (U : Matrix I J ℂ) (hU : Uᴴ * U = 1)
    (ρ E : Matrix J J ℂ) :
    acceptanceProbability (ZeroExtension.extend U ρ) (ZeroExtension.extend U E) =
      acceptanceProbability ρ E := by
  unfold acceptanceProbability
  rw [ZeroExtension.extend_mul U hU, ZeroExtension.extend_trace U hU]

theorem recursiveTensorPower_extend (U : Matrix I J ℂ) (A : Matrix J J ℂ) (n : ℕ) :
    recursiveTensorPower (ZeroExtension.extend U A) n =
      ZeroExtension.extend (recursiveIsometry U n) (recursiveTensorPower A n) := by
  induction n with
  | zero =>
      change (1 : Matrix PUnit PUnit ℂ) =
        (1 : Matrix PUnit PUnit ℂ) * (1 : Matrix PUnit PUnit ℂ) *
          (1 : Matrix PUnit PUnit ℂ)ᴴ
      simp only [Matrix.conjTranspose_one, Matrix.one_mul]
  | succ n ih =>
      change recursiveTensorPower (ZeroExtension.extend U A) n ⊗ₖ
          ZeroExtension.extend U A =
        ZeroExtension.extend (recursiveIsometry U n ⊗ₖ U)
          (recursiveTensorPower A n ⊗ₖ A)
      rw [ih]
      simp only [ZeroExtension.extend, Matrix.conjTranspose_kronecker,
        ← Matrix.mul_kronecker_mul]

theorem binaryTest_ext {S T : BinaryTest} (ha : S.alpha = T.alpha)
    (hb : S.beta = T.beta) : S = T := by
  cases S
  cases T
  simp_all

theorem iidStrategyFamily_embed (U : Matrix I J ℂ) (hU : Uᴴ * U = 1)
    {ρc σc : Matrix J J ℂ} (hρc : IsDensity ρc) (hσc : IsDensity σc)
    {ρ σ : Matrix I I ℂ} (hρ : IsDensity ρ) (hσ : IsDensity σ)
    (hr : ρ = ZeroExtension.extend U ρc) (hs : σ = ZeroExtension.extend U σc) :
    ∀ n, QuantumSteinAchievability.iidStrategyFamily ρc σc hρc hσc n ⊆
      QuantumSteinAchievability.iidStrategyFamily ρ σ hρ hσ n := by
  intro n T hT
  rcases hT with ⟨⟨E, hE⟩, rfl⟩
  refine ⟨⟨ZeroExtension.extend (recursiveIsometry U n) E,
    extend_isEffect _ (recursiveIsometry_gram U hU n) hE⟩, ?_⟩
  apply binaryTest_ext
  · rw [QuantumSteinAchievability.binaryTestOfEffect_alpha,
      QuantumSteinAchievability.binaryTestOfEffect_alpha,
      QuantumSteinAchievability.acceptanceProbability_complement
        (PetzTensorTail.recursiveTensorPower_density hρ n),
      QuantumSteinAchievability.acceptanceProbability_complement
        (PetzTensorTail.recursiveTensorPower_density hρc n),
      hr, recursiveTensorPower_extend U ρc n,
      acceptanceProbability_extend _ (recursiveIsometry_gram U hU n)]
  · rw [QuantumSteinAchievability.binaryTestOfEffect_beta,
      QuantumSteinAchievability.binaryTestOfEffect_beta,
      hs, recursiveTensorPower_extend U σc n,
      acceptanceProbability_extend _ (recursiveIsometry_gram U hU n)]

theorem compress_isDensity {ρ σ : Matrix I I ℂ}
    (hρ : IsDensity ρ) (hσ : σ.PosSemidef) (hs : HasSupportIn ρ σ) :
    IsDensity (InputSupport.compress hσ ρ) := by
  classical
  refine ⟨InputSupport.compress_posSemidef hσ hρ.1, ?_⟩
  calc
    (InputSupport.compress hσ ρ).trace =
        (ZeroExtension.extend (OutputSupport.supportIsometry hσ)
          (InputSupport.compress hσ ρ)).trace :=
      (ZeroExtension.extend_trace _ (OutputSupport.supportIsometry_gram hσ) _).symm
    _ = ρ.trace := congrArg Matrix.trace
      (InputSupport.reconstruct_of_hasSupportIn hρ.1.1 hσ hs).symm
    _ = 1 := hρ.2

theorem relativeEntropyBits_le_iid_orderedSteinExponent_of_support
    (ρ σ : Matrix I I ℂ) (hρ : IsDensity ρ) (hσ : IsDensity σ)
    (hs : HasSupportIn ρ σ) :
    relativeEntropyBits ρ σ ≤ orderedSteinExponent
      (QuantumSteinAchievability.iidStrategyFamily ρ σ hρ hσ) := by
  classical
  have hρc := compress_isDensity hρ hσ.1 hs
  have hσc := compress_isDensity hσ hσ.1 (hasSupportIn_self σ)
  have hEmbed := iidStrategyFamily_embed (OutputSupport.supportIsometry hσ.1)
    (OutputSupport.supportIsometry_gram hσ.1) hρc hσc hρ hσ
    (InputSupport.reconstruct_of_hasSupportIn hρ.1.1 hσ.1 hs)
    (InputSupport.reconstruct_comparator hσ.1)
  rw [InputSupport.relativeEntropyBits_eq_compressed hρ.1.1 hσ.1 hs]
  exact (QuantumSteinAchievability.relativeEntropyBits_le_iid_orderedSteinExponent
    _ _ hρc hσc (InputSupport.compress_comparator_posDef hσ.1)).trans
      (orderedSteinExponent_mono_family hEmbed)

theorem supportProjection_isEffect {σ : Matrix I I ℂ} (hσ : σ.PosSemidef) :
    IsEffect (TensorEntropy.supportProjection σ) := by
  constructor
  · rw [← OutputSupport.supportIsometry_projection hσ]
    exact Matrix.posSemidef_self_mul_conjTranspose _
  · exact OutputSupport.complement_posSemidef hσ.1

theorem supportRejection_probability_pos {ρ σ : Matrix I I ℂ}
    (hρ : IsDensity ρ) (hσ : σ.PosSemidef) (hs : ¬ HasSupportIn ρ σ) :
    0 < acceptanceProbability ρ (1 - TensorEntropy.supportProjection σ) := by
  have hnonneg := (acceptanceProbability_bounds hρ
    (QuantumSteinAchievability.effect_complement (supportProjection_isEffect hσ))).1
  by_contra hpos
  have hz := le_antisymm (le_of_not_gt hpos) hnonneg
  let Q := 1 - TensorEntropy.supportProjection σ
  let H := CFC.sqrt ρ
  have hQ : Q.IsHermitian := (OutputSupport.complement_posSemidef hσ.1).1
  have hH : H.IsHermitian := (CFC.sqrt_nonneg ρ).posSemidef.1
  have hHsq : H * H = ρ := CFC.sqrt_mul_sqrt_self ρ hρ.1.nonneg
  have hQsq : Q * Q = Q := by
    dsimp only [Q]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
      OutputSupport.supportProjection_idempotent hσ.1]
    abel
  have hsquare : (Q * H) * (Q * H)ᴴ = Q * ρ * Q := by
    calc
      (Q * H) * (Q * H)ᴴ = Q * (H * H) * Q := by
        simp only [Matrix.conjTranspose_mul, hH.eq, hQ.eq, Matrix.mul_assoc]
      _ = Q * ρ * Q := by rw [hHsq]
  have htraceRe : ((Q * H) * (Q * H)ᴴ).trace.re = 0 := by
    rw [hsquare, Matrix.trace_mul_cycle, hQsq, Matrix.trace_mul_comm]
    exact hz
  have htrace : ((Q * H) * (Q * H)ᴴ).trace = 0 := by
    apply Complex.ext
    · simpa only [Complex.zero_re] using htraceRe
    · have him := (Complex.nonneg_iff.mp
        (Matrix.posSemidef_self_mul_conjTranspose (Q * H)).trace_nonneg).2
      simpa only [Complex.zero_im] using him.symm
  have hQH : Q * H = 0 := Matrix.trace_mul_conjTranspose_self_eq_zero_iff.mp htrace
  have hQρ : Q * ρ = 0 := by
    calc
      Q * ρ = Q * (H * H) := by rw [hHsq]
      _ = (Q * H) * H := by rw [Matrix.mul_assoc]
      _ = 0 := by rw [hQH, Matrix.zero_mul]
  have hρQ : ρ * Q = 0 := by
    have h := congrArg Matrix.conjTranspose hQρ
    simpa only [Matrix.conjTranspose_mul, hρ.1.1.eq, hQ.eq,
      Matrix.conjTranspose_zero] using h
  have hmul : ρ * TensorEntropy.supportProjection σ = ρ := by
    change ρ * (1 - TensorEntropy.supportProjection σ) = 0 at hρQ
    rw [Matrix.mul_sub, Matrix.mul_one] at hρQ
    exact (sub_eq_zero.mp hρQ).symm
  exact hs ((TensorEntropy.hasSupportIn_iff_mul_supportProjection hσ.1).mpr hmul)

theorem recursiveTensorPower_mul (A B : Matrix I I ℂ) (n : ℕ) :
    recursiveTensorPower (A * B) n =
      recursiveTensorPower A n * recursiveTensorPower B n := by
  induction n with
  | zero =>
      change (1 : Matrix PUnit PUnit ℂ) =
        (1 : Matrix PUnit PUnit ℂ) * (1 : Matrix PUnit PUnit ℂ)
      simp only [Matrix.one_mul]
  | succ n ih =>
      change recursiveTensorPower (A * B) n ⊗ₖ (A * B) =
        (recursiveTensorPower A n ⊗ₖ A) * (recursiveTensorPower B n ⊗ₖ B)
      rw [ih, Matrix.mul_kronecker_mul]

theorem recursiveTensorPower_trace (A : Matrix I I ℂ) (n : ℕ) :
    (recursiveTensorPower A n).trace = A.trace ^ n := by
  induction n with
  | zero =>
      change (1 : Matrix PUnit PUnit ℂ).trace = A.trace ^ 0
      simp [Matrix.trace, Matrix.diag]
  | succ n ih =>
      change (recursiveTensorPower A n ⊗ₖ A).trace = A.trace ^ (n + 1)
      rw [Matrix.trace_kronecker, ih, pow_succ]

theorem projection_isEffect {P : Matrix I I ℂ}
    (hP : P.IsHermitian) (hP2 : P * P = P) : IsEffect P := by
  have hp := Matrix.posSemidef_conjTranspose_mul_self P
  rw [hP.eq, hP2] at hp
  refine ⟨hp, ?_⟩
  have hc : (1 - P).IsHermitian := Matrix.isHermitian_one.sub hP
  have hc2 : (1 - P) * (1 - P) = 1 - P := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hP2]
    abel
  have h := Matrix.posSemidef_conjTranspose_mul_self (1 - P)
  rw [hc.eq, hc2] at h
  exact h

theorem recursiveTensorPower_projection_isEffect {P : Matrix I I ℂ}
    (hP : P.IsHermitian) (hP2 : P * P = P) (n : ℕ) :
    IsEffect (recursiveTensorPower P n) := by
  have hH : (recursiveTensorPower P n).IsHermitian := by
    induction n with
    | zero => exact Matrix.isHermitian_one
    | succ n ih =>
        change (recursiveTensorPower P n ⊗ₖ P)ᴴ = recursiveTensorPower P n ⊗ₖ P
        rw [Matrix.conjTranspose_kronecker, ih.eq, hP.eq]
  apply projection_isEffect hH
  rw [← recursiveTensorPower_mul, hP2]

theorem acceptanceProbability_tensorPower {A P : Matrix I I ℂ}
    (hA : A.PosSemidef) (hP : P.PosSemidef) (n : ℕ) :
    acceptanceProbability (recursiveTensorPower A n) (recursiveTensorPower P n) =
      acceptanceProbability A P ^ n := by
  have ht : (A * P).trace = (acceptanceProbability A P : ℂ) := by
    apply Complex.ext
    · rfl
    · have him := (Complex.nonneg_iff.mp
        (KrausCompletion.trace_mul_nonneg_of_posSemidef hA hP)).2
      simpa only [Complex.ofReal_im] using him.symm
  unfold acceptanceProbability
  rw [← recursiveTensorPower_mul, recursiveTensorPower_trace, ht]
  rw [← Complex.ofReal_pow, Complex.ofReal_re]
  simp only [Complex.ofReal_re]

def kernelSteinEffect (σ : Matrix I I ℂ) (n : ℕ) :
    Matrix (RecursiveRows I n) (RecursiveRows I n) ℂ :=
  1 - recursiveTensorPower (TensorEntropy.supportProjection σ) n

theorem kernelSteinEffect_isEffect {σ : Matrix I I ℂ}
    (hσ : σ.PosSemidef) (n : ℕ) : IsEffect (kernelSteinEffect σ n) :=
  QuantumSteinAchievability.effect_complement
    (recursiveTensorPower_projection_isEffect
      (OutputSupport.supportProjection_isHermitian hσ.1)
      (OutputSupport.supportProjection_idempotent hσ.1) n)

def kernelSteinTest (ρ σ : Matrix I I ℂ) (hρ : IsDensity ρ) (hσ : IsDensity σ)
    (n : ℕ) : BinaryTest :=
  QuantumSteinAchievability.binaryTestOfEffect
    (recursiveTensorPower ρ n) (recursiveTensorPower σ n)
    (PetzTensorTail.recursiveTensorPower_density hρ n)
    (PetzTensorTail.recursiveTensorPower_density hσ n)
    (kernelSteinEffect σ n) (kernelSteinEffect_isEffect hσ.1 n)

theorem kernelSteinTest_mem (ρ σ : Matrix I I ℂ)
    (hρ : IsDensity ρ) (hσ : IsDensity σ) (n : ℕ) :
    kernelSteinTest ρ σ hρ hσ n ∈
      QuantumSteinAchievability.iidStrategyFamily ρ σ hρ hσ n :=
  ⟨⟨_, kernelSteinEffect_isEffect hσ.1 n⟩, rfl⟩

theorem kernelSteinTest_alpha (ρ σ : Matrix I I ℂ)
    (hρ : IsDensity ρ) (hσ : IsDensity σ) (n : ℕ) :
    (kernelSteinTest ρ σ hρ hσ n).alpha =
      acceptanceProbability ρ (TensorEntropy.supportProjection σ) ^ n := by
  unfold kernelSteinTest
  rw [QuantumSteinAchievability.binaryTestOfEffect_alpha]
  simp only [kernelSteinEffect, sub_sub_cancel]
  exact acceptanceProbability_tensorPower hρ.1 (supportProjection_isEffect hσ.1).1 n

theorem kernelSteinTest_beta (ρ σ : Matrix I I ℂ)
    (hρ : IsDensity ρ) (hσ : IsDensity σ) (n : ℕ) :
    (kernelSteinTest ρ σ hρ hσ n).beta = 0 := by
  have hs : acceptanceProbability σ (TensorEntropy.supportProjection σ) = 1 := by
    unfold acceptanceProbability
    rw [TensorEntropy.supportProjection_mul σ hσ.1.1, hσ.2]
    rfl
  unfold kernelSteinTest
  rw [QuantumSteinAchievability.binaryTestOfEffect_beta]
  unfold kernelSteinEffect
  rw [QuantumSteinAchievability.acceptanceProbability_complement
    (PetzTensorTail.recursiveTensorPower_density hσ n),
    acceptanceProbability_tensorPower hσ.1 (supportProjection_isEffect hσ.1).1 n, hs]
  simp

theorem kernelSteinTest_alpha_tendsto (ρ σ : Matrix I I ℂ)
    (hρ : IsDensity ρ) (hσ : IsDensity σ) (hs : ¬ HasSupportIn ρ σ) :
    Filter.Tendsto (fun n => (kernelSteinTest ρ σ hρ hσ n).alpha)
      Filter.atTop (𝓝 0) := by
  have hbounds := acceptanceProbability_bounds hρ (supportProjection_isEffect hσ.1)
  have hpos := supportRejection_probability_pos hρ hσ.1 hs
  rw [QuantumSteinAchievability.acceptanceProbability_complement hρ] at hpos
  simpa only [kernelSteinTest_alpha] using
    (tendsto_pow_atTop_nhds_zero_of_lt_one hbounds.1 (by linarith))

theorem iid_orderedSteinExponent_eq_top_of_not_support
    (ρ σ : Matrix I I ℂ) (hρ : IsDensity ρ) (hσ : IsDensity σ)
    (hs : ¬ HasSupportIn ρ σ) :
    orderedSteinExponent (QuantumSteinAchievability.iidStrategyFamily ρ σ hρ hσ) = ⊤ := by
  have hRate (R : ℝ) : ((R / Real.log 2 : ℝ) : EReal) ≤
      orderedSteinExponent (QuantumSteinAchievability.iidStrategyFamily ρ σ hρ hσ) := by
    apply QuantumSteinAchievability.le_orderedSteinExponent_of_testSequence
      (kernelSteinTest ρ σ hρ hσ) (kernelSteinTest_mem ρ σ hρ hσ)
      (kernelSteinTest_alpha_tendsto ρ σ hρ hσ hs)
    intro n
    rw [kernelSteinTest_beta]
    exact (Real.exp_pos _).le
  apply eq_top_iff.mpr
  by_contra hnot
  rcases EReal.exists_between_coe_real (lt_of_not_ge hnot) with ⟨r, hr, _⟩
  have hb := hRate (r * Real.log 2)
  rw [mul_div_cancel_right₀ r (ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 2)))] at hb
  exact not_le_of_gt hr hb

theorem relativeEntropyBits_le_iid_orderedSteinExponent
    (ρ σ : Matrix I I ℂ) (hρ : IsDensity ρ) (hσ : IsDensity σ) :
    relativeEntropyBits ρ σ ≤ orderedSteinExponent
      (QuantumSteinAchievability.iidStrategyFamily ρ σ hρ hσ) := by
  classical
  by_cases hs : HasSupportIn ρ σ
  · exact relativeEntropyBits_le_iid_orderedSteinExponent_of_support ρ σ hρ hσ hs
  · rw [iid_orderedSteinExponent_eq_top_of_not_support ρ σ hρ hσ hs]
    exact le_top

theorem iid_bits_effect_achievability (ρ σ : Matrix I I ℂ)
    (hρ : IsDensity ρ) (hσ : IsDensity σ) {r : ℝ}
    (hr : (r : EReal) < relativeEntropyBits ρ σ) :
    ∃ E : (n : ℕ) → Matrix (RecursiveRows I n) (RecursiveRows I n) ℂ,
      (∀ n, IsEffect (E n)) ∧
      Filter.Tendsto (fun n => acceptanceProbability (recursiveTensorPower ρ n) (1 - E n))
        Filter.atTop (𝓝 0) ∧
      (∀ n, acceptanceProbability (recursiveTensorPower σ n) (E n) ≤
        (2 : ℝ) ^ (-(n : ℝ) * r)) := by
  classical
  by_cases hs : HasSupportIn ρ σ
  · let U := OutputSupport.supportIsometry hσ.1
    let ρc := InputSupport.compress hσ.1 ρ
    let σc := InputSupport.compress hσ.1 σ
    have hU : Uᴴ * U = 1 := OutputSupport.supportIsometry_gram hσ.1
    have hρc : IsDensity ρc := compress_isDensity hρ hσ.1 hs
    have hσc : IsDensity σc := compress_isDensity hσ hσ.1 (hasSupportIn_self σ)
    have hσcPD : σc.PosDef := InputSupport.compress_comparator_posDef hσ.1
    have hrc : (r : EReal) < relativeEntropyBits ρc σc := by
      simpa only [InputSupport.relativeEntropyBits_eq_compressed hρ.1.1 hσ.1 hs] using hr
    have hAch := QuantumSteinAchievability.iid_bits_rate_achievability
      ρc σc hρc hσc hσcPD hrc
    let Ec := fun n => QuantumSteinAchievability.iidNeymanPearsonEffect ρc σc
      (r * Real.log 2) n
    let E := fun n => ZeroExtension.extend (recursiveIsometry U n) (Ec n)
    have hE (n : ℕ) : IsEffect (E n) :=
      extend_isEffect _ (recursiveIsometry_gram U hU n)
        (QuantumSteinAchievability.iidNeymanPearsonEffect_isEffect hρc hσc _ n)
    have hρn (n : ℕ) : recursiveTensorPower ρ n =
        ZeroExtension.extend (recursiveIsometry U n) (recursiveTensorPower ρc n) := by
      calc
        recursiveTensorPower ρ n = recursiveTensorPower (ZeroExtension.extend U ρc) n :=
          congrArg (fun A => recursiveTensorPower A n)
            (InputSupport.reconstruct_of_hasSupportIn hρ.1.1 hσ.1 hs)
        _ = _ := recursiveTensorPower_extend U ρc n
    have hσn (n : ℕ) : recursiveTensorPower σ n =
        ZeroExtension.extend (recursiveIsometry U n) (recursiveTensorPower σc n) := by
      calc
        recursiveTensorPower σ n = recursiveTensorPower (ZeroExtension.extend U σc) n :=
          congrArg (fun A => recursiveTensorPower A n) (InputSupport.reconstruct_comparator hσ.1)
        _ = _ := recursiveTensorPower_extend U σc n
    have ha (n : ℕ) : acceptanceProbability (recursiveTensorPower ρ n) (1 - E n) =
        (QuantumSteinAchievability.iidNeymanPearsonTest ρc σc hρc hσc
          (r * Real.log 2) n).alpha := by
      change acceptanceProbability (recursiveTensorPower ρ n)
          (1 - ZeroExtension.extend (recursiveIsometry U n) (Ec n)) =
        acceptanceProbability (recursiveTensorPower ρc n) (1 - Ec n)
      rw [QuantumSteinAchievability.acceptanceProbability_complement
        (PetzTensorTail.recursiveTensorPower_density hρ n),
        QuantumSteinAchievability.acceptanceProbability_complement
          (PetzTensorTail.recursiveTensorPower_density hρc n),
        hρn n, acceptanceProbability_extend _ (recursiveIsometry_gram U hU n)]
    have hb (n : ℕ) : acceptanceProbability (recursiveTensorPower σ n) (E n) =
        (QuantumSteinAchievability.iidNeymanPearsonTest ρc σc hρc hσc
          (r * Real.log 2) n).beta := by
      change acceptanceProbability (recursiveTensorPower σ n)
          (ZeroExtension.extend (recursiveIsometry U n) (Ec n)) =
        acceptanceProbability (recursiveTensorPower σc n) (Ec n)
      rw [hσn n, acceptanceProbability_extend _ (recursiveIsometry_gram U hU n)]
    refine ⟨E, hE, ?_, ?_⟩
    · simpa only [ha] using hAch.1
    · intro n
      rw [hb n]
      exact hAch.2.2 n
  · refine ⟨kernelSteinEffect σ, kernelSteinEffect_isEffect hσ.1, ?_, ?_⟩
    · exact kernelSteinTest_alpha_tendsto ρ σ hρ hσ hs
    · intro n
      change (kernelSteinTest ρ σ hρ hσ n).beta ≤ (2 : ℝ) ^ (-(n : ℝ) * r)
      rw [kernelSteinTest_beta]
      exact (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _).le

theorem recursiveTensorPower_relativeEntropyBits {ρ σ : Matrix I I ℂ}
    (hρ : IsDensity ρ) (hσ : σ.PosSemidef) (n : ℕ) :
    relativeEntropyBits (recursiveTensorPower ρ n) (recursiveTensorPower σ n) =
      (n : EReal) * relativeEntropyBits ρ σ := by
  induction n with
  | zero =>
      rw [relativeEntropyBits_of_posDef _ (show (recursiveTensorPower σ 0).PosDef from
        Matrix.PosDef.one)]
      simp [recursiveTensorPower, finiteRelativeEntropyBits]
  | succ n ih =>
      change relativeEntropyBits (recursiveTensorPower ρ n ⊗ₖ ρ)
        (recursiveTensorPower σ n ⊗ₖ σ) =
          ((n + 1 : ℕ) : EReal) * relativeEntropyBits ρ σ
      rw [TensorEntropy.relativeEntropyBits_kronecker
        (PetzTensorTail.recursiveTensorPower_density hρ n)
        (PetzTensorTail.recursiveTensorPower_posSemidef hσ n) hρ hσ,
        ih, Nat.cast_succ,
        EReal.right_distrib_of_nonneg (by positivity) (by positivity), one_mul]

theorem iidStrategyFamily_uniformBinaryConverse (ρ σ : Matrix I I ℂ)
    (hρ : IsDensity ρ) (hσ : IsDensity σ) {B : ℝ}
    (hD : relativeEntropyBits ρ σ ≤ (B : EReal)) :
    UniformBinaryConverse (QuantumSteinAchievability.iidStrategyFamily ρ σ hρ hσ) B := by
  intro n hn T hT
  rcases hT with ⟨⟨E, hE⟩, rfl⟩
  rw [QuantumSteinAchievability.binaryTestOfEffect_alpha,
    QuantumSteinAchievability.binaryTestOfEffect_beta,
    QuantumSteinAchievability.acceptanceProbability_complement
      (PetzTensorTail.recursiveTensorPower_density hρ n)]
  simp only [sub_sub_cancel]
  calc
    extendedBinaryRelativeEntropyBits
        (acceptanceProbability (recursiveTensorPower ρ n) E)
        (acceptanceProbability (recursiveTensorPower σ n) E) ≤
      relativeEntropyBits (recursiveTensorPower ρ n) (recursiveTensorPower σ n) :=
        MatrixStrategyAssembly.MatrixBinaryTesting.binary_errors_entropy_dpi
          (PetzTensorTail.recursiveTensorPower_density hρ n)
          (PetzTensorTail.recursiveTensorPower_density hσ n) hE
    _ = (n : EReal) * relativeEntropyBits ρ σ :=
      recursiveTensorPower_relativeEntropyBits hρ hσ.1 n
    _ ≤ (n : EReal) * (B : EReal) :=
      mul_le_mul_of_nonneg_left hD (by positivity)
    _ = (((n : ℝ) * B : ℝ) : EReal) := by norm_cast

theorem iid_orderedSteinExponent_le_relativeEntropyBits (ρ σ : Matrix I I ℂ)
    (hρ : IsDensity ρ) (hσ : IsDensity σ) :
    orderedSteinExponent (QuantumSteinAchievability.iidStrategyFamily ρ σ hρ hσ) ≤
      relativeEntropyBits ρ σ := by
  cases hD : relativeEntropyBits ρ σ with
  | bot => exact False.elim ((relativeEntropyBits_ne_bot ρ σ) hD)
  | top => exact le_top
  | coe B =>
      have hB : 0 ≤ B := EReal.coe_nonneg.mp (by
        simpa only [hD] using Klein.relativeEntropyBits_nonneg hρ hσ)
      exact orderedSteinExponent_le_of_uniformBinaryConverse hB
        (iidStrategyFamily_uniformBinaryConverse ρ σ hρ hσ (by rw [hD]))

theorem iid_orderedSteinExponent_eq_relativeEntropyBits (ρ σ : Matrix I I ℂ)
    (hρ : IsDensity ρ) (hσ : IsDensity σ) :
    orderedSteinExponent (QuantumSteinAchievability.iidStrategyFamily ρ σ hρ hσ) =
      relativeEntropyBits ρ σ :=
  le_antisymm (iid_orderedSteinExponent_le_relativeEntropyBits ρ σ hρ hσ)
    (relativeEntropyBits_le_iid_orderedSteinExponent ρ σ hρ hσ)

def positiveNormalize (A : Matrix I I ℂ) : Matrix I I ℂ := (A.trace.re)⁻¹ • A

theorem positiveNormalize_isDensity {A : Matrix I I ℂ}
    (hA : A.PosSemidef) (ht : 0 < A.trace.re) : IsDensity (positiveNormalize A) := by
  refine ⟨hA.smul (inv_nonneg.mpr ht.le), ?_⟩
  have him : A.trace.im = 0 := (Complex.nonneg_iff.mp hA.trace_nonneg).2.symm
  have heq : A.trace = (A.trace.re : ℂ) := by
    apply Complex.ext <;> simp [him]
  simp only [positiveNormalize, Matrix.trace_smul]
  apply Complex.ext
  · simp [Complex.smul_re, smul_eq_mul, inv_mul_cancel₀ (ne_of_gt ht)]
  · simp [Complex.smul_im, smul_eq_mul, him]

theorem positiveNormalize_traceNorm_le {ρ A : Matrix I I ℂ}
    (hρ : IsDensity ρ) (hA : A.PosSemidef) (ht : 0 < A.trace.re)
    (ht1 : A.trace.re ≤ 1) :
    EffectPerturbation.traceNorm (ρ - positiveNormalize A) ≤
      2 * EffectPerturbation.traceNorm (ρ - A) := by
  obtain ⟨E, hE, he⟩ :=
    (EffectPerturbation.density_traceNorm_effect_characterization
      hρ (positiveNormalize_isDensity hA ht)).2
  have hp : 0 ≤ acceptanceProbability A E := trace_mul_re_nonneg hA hE.1
  have hi : 1 ≤ (A.trace.re)⁻¹ := by
    rw [← one_div]
    exact (le_div_iff₀ ht).mpr (by simpa using ht1)
  have hn : acceptanceProbability (positiveNormalize A) E =
      (A.trace.re)⁻¹ * acceptanceProbability A E := by
    simp only [positiveNormalize, acceptanceProbability, Matrix.smul_mul,
      Matrix.trace_smul, Complex.smul_re, smul_eq_mul]
  have hv : |acceptanceProbability ρ E - acceptanceProbability A E| ≤
      EffectPerturbation.traceNorm (ρ - A) := by
    have heq : acceptanceProbability ρ E - acceptanceProbability A E =
        EffectPerturbation.effectValue E (ρ - A) := by
      rw [← EffectPerturbation.effectValue_eq_acceptance,
        ← EffectPerturbation.effectValue_eq_acceptance]
      simp only [EffectPerturbation.effectValue, Matrix.mul_sub,
        Matrix.trace_sub, Complex.sub_re]
    rw [heq]
    exact EffectPerturbation.effectValue_abs_le_traceNorm hE (hρ.1.1.sub hA.1)
  have hle : acceptanceProbability ρ E - acceptanceProbability (positiveNormalize A) E ≤
      acceptanceProbability ρ E - acceptanceProbability A E := by
    rw [hn]
    nlinarith
  have h := le_abs_self (acceptanceProbability ρ E - acceptanceProbability A E)
  linarith

def normalizedIIDCrop (ρ : Matrix I I ℂ) {σ : Matrix I I ℂ}
    (hσ : σ.PosSemidef) (rate : ℝ) (n : ℕ) :
    Matrix (RecursiveRows I n) (RecursiveRows I n) ℂ :=
  let A := PetzSmoothing.iidSmoothedState ρ hσ n (PetzSmoothing.rateBudget n rate)
  if 0 < A.trace.re then positiveNormalize A else recursiveTensorPower ρ n

theorem normalizedIIDCrop_isDensity {ρ σ : Matrix I I ℂ}
    (hρ : IsDensity ρ) (hσ : σ.PosDef) (rate : ℝ) (n : ℕ) :
    IsDensity (normalizedIIDCrop ρ hσ.posSemidef rate n) := by
  unfold normalizedIIDCrop
  dsimp only
  split_ifs with ht
  · exact positiveNormalize_isDensity
      (PetzSmoothing.cropMap_posSemidef _
        (PetzTensorTail.recursiveTensorPower_posSemidef hρ.1 n)) ht
  · exact PetzTensorTail.recursiveTensorPower_density hρ n

theorem normalizedIIDCrop_traceNorm_tendsto {ρ σ : Matrix I I ℂ}
    (hρ : IsDensity ρ) (hσ : σ.PosDef) (rate : ℝ)
    (hrate : relativeEntropyBits ρ σ < (rate : EReal)) :
    Filter.Tendsto (fun n : ℕ => EffectPerturbation.traceNorm
      (recursiveTensorPower ρ n - normalizedIIDCrop ρ hσ.posSemidef rate n))
      Filter.atTop (𝓝 0) := by
  have hlim : Filter.Tendsto (fun n : ℕ => 2 * EffectPerturbation.traceNorm
      (recursiveTensorPower ρ n - PetzSmoothing.iidSmoothedState ρ hσ.posSemidef n
        (PetzSmoothing.rateBudget n rate))) Filter.atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (PetzSmoothing.iidCrop_traceNorm_tendsto hρ hσ rate hrate).const_mul 2
  apply squeeze_zero (fun n => EffectPerturbation.traceNorm_nonneg _) ?_ hlim
  intro n
  unfold normalizedIIDCrop
  dsimp only
  split_ifs with ht
  · apply positiveNormalize_traceNorm_le (PetzTensorTail.recursiveTensorPower_density hρ n)
      (PetzSmoothing.cropMap_posSemidef _
        (PetzTensorTail.recursiveTensorPower_posSemidef hρ.1 n)) ht
    change (PetzSmoothing.iidSmoothedState ρ hσ.posSemidef n
      (PetzSmoothing.rateBudget n rate)).trace.re ≤ 1
    rw [PetzSmoothing.iidCrop_trace hρ hσ]
    linarith [(PetzSmoothing.discardedMass_bounds hρ hσ n
      (PetzSmoothing.rateBudget n rate)).1]
  · simp only [sub_self, EffectPerturbation.traceNorm, CFC.abs_zero,
      Matrix.trace_zero, Complex.zero_re]
    exact mul_nonneg (by norm_num) (EffectPerturbation.traceNorm_nonneg _)

theorem normalizedIIDCrop_eventual_cap {ρ σ : Matrix I I ℂ}
    (hρ : IsDensity ρ) (hσ : σ.PosDef) (rate₀ rate : ℝ)
    (hD : relativeEntropyBits ρ σ < (rate₀ : EReal)) (hRate : rate₀ < rate) :
    ∀ᶠ n : ℕ in Filter.atTop,
      ((PetzSmoothing.rateBudget n rate) • recursiveTensorPower σ n -
        normalizedIIDCrop ρ hσ.posSemidef rate₀ n).PosSemidef := by
  have htrace := PetzSmoothing.iidCrop_trace_tendsto hρ hσ rate₀ hD
  have ht : ∀ᶠ n : ℕ in Filter.atTop, (1 / 2 : ℝ) <
      (PetzSmoothing.iidSmoothedState ρ hσ.posSemidef n
        (PetzSmoothing.rateBudget n rate₀)).trace.re :=
    htrace.eventually (eventually_gt_nhds (by norm_num : (1 / 2 : ℝ) < 1))
  have hnl : Filter.Tendsto (fun n : ℕ => (n : ℝ) * (rate - rate₀))
      Filter.atTop Filter.atTop :=
    Filter.Tendsto.atTop_mul_const (sub_pos.mpr hRate) tendsto_natCast_atTop_atTop
  filter_upwards [ht, hnl.eventually (eventually_ge_atTop (1 : ℝ))] with n ht hn
  let A := PetzSmoothing.iidSmoothedState ρ hσ.posSemidef n
    (PetzSmoothing.rateBudget n rate₀)
  have ht0 : 0 < A.trace.re := by dsimp [A]; linarith
  have hi : (A.trace.re)⁻¹ ≤ 2 := by
    rw [← one_div]
    apply (div_le_iff₀ ht0).mpr
    dsimp [A]
    linarith
  have hb : 2 * PetzSmoothing.rateBudget n rate₀ ≤ PetzSmoothing.rateBudget n rate := by
    unfold PetzSmoothing.rateBudget
    calc
      2 * (2 : ℝ) ^ ((n : ℝ) * rate₀) = (2 : ℝ) ^ ((n : ℝ) * rate₀ + 1) := by
        rw [Real.rpow_add (by norm_num), Real.rpow_one]
        ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith)
  have hcoef : (A.trace.re)⁻¹ * PetzSmoothing.rateBudget n rate₀ ≤
      PetzSmoothing.rateBudget n rate :=
    (mul_le_mul_of_nonneg_right hi (PetzSmoothing.rateBudget_pos n rate₀).le).trans hb
  have hcap := (PetzSmoothing.iidCrop_cap hρ.1 hσ n
    (PetzSmoothing.rateBudget n rate₀) (PetzSmoothing.rateBudget_pos n rate₀).le).smul
      (inv_nonneg.mpr ht0.le)
  have hrest := (PetzTensorTail.recursiveTensorPower_posSemidef hσ.posSemidef n).smul
    (sub_nonneg.mpr hcoef)
  have heq : (PetzSmoothing.rateBudget n rate) • recursiveTensorPower σ n -
      positiveNormalize A =
      (PetzSmoothing.rateBudget n rate -
        (A.trace.re)⁻¹ * PetzSmoothing.rateBudget n rate₀) • recursiveTensorPower σ n +
      (A.trace.re)⁻¹ • (PetzSmoothing.rateBudget n rate₀ • recursiveTensorPower σ n - A) := by
    simp only [positiveNormalize, sub_smul, smul_sub, smul_smul]
    abel
  change (PetzSmoothing.rateBudget n rate • recursiveTensorPower σ n -
    (if 0 < A.trace.re then positiveNormalize A else recursiveTensorPower ρ n)).PosSemidef
  rw [if_pos ht0, heq]
  exact hrest.add hcap

def supportExtendLinear (U : Matrix I J ℂ) : Matrix J J ℂ →ₗ[ℂ] Matrix I I ℂ where
  toFun := ZeroExtension.extend U
  map_add' := by
    intro A B
    simp only [ZeroExtension.extend, Matrix.mul_add, Matrix.add_mul]
  map_smul' := by
    intro c A
    simp [ZeroExtension.extend, Matrix.mul_smul, Matrix.smul_mul]

theorem traceNorm_extend_le (U : Matrix I J ℂ) (hU : Uᴴ * U = 1)
    {A : Matrix J J ℂ} (hA : A.IsHermitian) :
    EffectPerturbation.traceNorm (ZeroExtension.extend U A) ≤
      EffectPerturbation.traceNorm A :=
  EffectPerturbation.traceNorm_contracts_positive_tracePreserving (supportExtendLinear U)
    (fun X hX => ZeroExtension.extend_posSemidef U hX)
    (fun X => ZeroExtension.extend_trace U hU X) hA

theorem normalized_state_smoothing {ρ σ : Matrix I I ℂ}
    (hρ : IsDensity ρ) (hσ : IsDensity σ) (rate : ℝ)
    (hrate : relativeEntropyBits ρ σ < (rate : EReal)) :
    ∃ ν : (n : ℕ) → Matrix (RecursiveRows I n) (RecursiveRows I n) ℂ,
      (∀ n, IsDensity (ν n)) ∧
      Tendsto (fun n : ℕ => EffectPerturbation.traceNorm
        (recursiveTensorPower ρ n - ν n)) atTop (𝓝 0) ∧
      ∀ᶠ n : ℕ in atTop,
        (((2 : ℝ) ^ ((n : ℝ) * rate)) • recursiveTensorPower σ n - ν n).PosSemidef := by
  classical
  have hs : HasSupportIn ρ σ := by
    by_contra hn
    simp only [relativeEntropyBits, hn, ite_false] at hrate
    exact not_lt_of_ge le_top hrate
  let U := OutputSupport.supportIsometry hσ.1
  let ρc := InputSupport.compress hσ.1 ρ
  let σc := InputSupport.compress hσ.1 σ
  have hU : Uᴴ * U = 1 := OutputSupport.supportIsometry_gram hσ.1
  have hρc : IsDensity ρc := compress_isDensity hρ hσ.1 hs
  have hσc : IsDensity σc := compress_isDensity hσ hσ.1 (hasSupportIn_self σ)
  have hσcdef : σc.PosDef := InputSupport.compress_comparator_posDef hσ.1
  let d := finiteRelativeEntropyBits ρ σ
  have hD : relativeEntropyBits ρc σc = (d : EReal) := by
    calc
      relativeEntropyBits ρc σc = relativeEntropyBits ρ σ :=
        (InputSupport.relativeEntropyBits_eq_compressed hρ.1.1 hσ.1 hs).symm
      _ = _ := by simp only [relativeEntropyBits, hs, ite_true]; rfl
  have hd : d < rate := by
    exact EReal.coe_lt_coe_iff.mp (by
      simpa only [relativeEntropyBits, hs, ite_true] using hrate)
  let rate₀ := (d + rate) / 2
  have hd₀ : relativeEntropyBits ρc σc < (rate₀ : EReal) := by
    rw [hD]
    exact EReal.coe_lt_coe_iff.mpr (by dsimp [rate₀]; linarith)
  have h₀r : rate₀ < rate := by dsimp [rate₀]; linarith
  let νc := normalizedIIDCrop ρc hσcdef.posSemidef rate₀
  let ν (n : ℕ) := ZeroExtension.extend (recursiveIsometry U n) (νc n)
  have hνc (n : ℕ) : IsDensity (νc n) :=
    normalizedIIDCrop_isDensity hρc hσcdef rate₀ n
  have hν (n : ℕ) : IsDensity (ν n) :=
    extend_isDensity _ (recursiveIsometry_gram U hU n) (hνc n)
  have hρn (n : ℕ) : recursiveTensorPower ρ n =
      ZeroExtension.extend (recursiveIsometry U n) (recursiveTensorPower ρc n) := by
    calc
      recursiveTensorPower ρ n = recursiveTensorPower (ZeroExtension.extend U ρc) n :=
        congrArg (fun A => recursiveTensorPower A n)
          (InputSupport.reconstruct_of_hasSupportIn hρ.1.1 hσ.1 hs)
      _ = _ := recursiveTensorPower_extend U ρc n
  have hσn (n : ℕ) : recursiveTensorPower σ n =
      ZeroExtension.extend (recursiveIsometry U n) (recursiveTensorPower σc n) := by
    calc
      recursiveTensorPower σ n = recursiveTensorPower (ZeroExtension.extend U σc) n :=
        congrArg (fun A => recursiveTensorPower A n)
          (InputSupport.reconstruct_comparator hσ.1)
      _ = _ := recursiveTensorPower_extend U σc n
  refine ⟨ν, hν, ?_, ?_⟩
  · apply squeeze_zero (fun n => EffectPerturbation.traceNorm_nonneg _) ?_
      (normalizedIIDCrop_traceNorm_tendsto hρc hσcdef rate₀ hd₀)
    intro n
    have heq : recursiveTensorPower ρ n - ν n =
        ZeroExtension.extend (recursiveIsometry U n)
          (recursiveTensorPower ρc n - νc n) := by
      rw [hρn n]
      simp only [ν, ZeroExtension.extend, Matrix.mul_sub, Matrix.sub_mul]
    rw [heq]
    exact traceNorm_extend_le _ (recursiveIsometry_gram U hU n)
      ((PetzTensorTail.recursiveTensorPower_density hρc n).1.1.sub (hνc n).1.1)
  · filter_upwards [normalizedIIDCrop_eventual_cap hρc hσcdef rate₀ rate hd₀ h₀r]
      with n hcap
    have heq : ((2 : ℝ) ^ ((n : ℝ) * rate)) • recursiveTensorPower σ n - ν n =
        ZeroExtension.extend (recursiveIsometry U n)
          (PetzSmoothing.rateBudget n rate • recursiveTensorPower σc n - νc n) := by
      rw [hσn n]
      simp only [ν, PetzSmoothing.rateBudget, ZeroExtension.extend,
        Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul]
    rw [heq]
    exact ZeroExtension.extend_posSemidef _ hcap

end QuantumProver.SuperchannelDiscrimination.Corollaries

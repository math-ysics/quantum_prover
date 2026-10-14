import QuantumProver.InformationTheory.SuperchannelDiscrimination.DiamondControl
import QuantumProver.InformationTheory.SuperchannelDiscrimination.ChannelUniformApproximation
import QuantumProver.LinearAlgebra.SandwichedDPI.TraceNorm
import QuantumProver.InformationTheory.QuantumEntropy.PartialTraceKraus

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Matrix Kronecker

namespace QuantumProver.SuperchannelDiscrimination.ChannelUniformDiamond

open Matrix DiamondControl ChannelUniformApproximation

variable {I J O E R : Type*} [Fintype I] [Fintype J] [Fintype O] [Fintype E] [Fintype R]
  [DecidableEq I] [DecidableEq J] [DecidableEq O] [DecidableEq E] [DecidableEq R]

theorem nuclearNorm_eq_sharedTraceNorm (X : Matrix I I ℂ) :
    nuclearNorm X = QuantumProver.SandwichedDPI.traceNorm X := rfl

theorem re_trace_pairing_le_opNorm_nuclear (S X : Matrix I I ℂ) :
    (S * X).trace.re ≤ ‖S‖ * nuclearNorm X := by
  by_cases hS : S = 0
  · simp only [hS, Matrix.zero_mul, Matrix.trace_zero, Complex.zero_re, norm_zero, zero_mul, le_refl]
  · have hn : 0 < ‖S‖ := norm_pos_iff.mpr hS
    let c : ℂ := ((‖S‖⁻¹ : ℝ) : ℂ)
    have hc : ‖c‖ = ‖S‖⁻¹ := by
      simp only [c, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (inv_pos.mpr hn).le]
    have hnorm : ‖c • S‖ ≤ 1 := by
      rw [norm_smul, hc, inv_mul_cancel₀ hn.ne']
    have ht := QuantumProver.SandwichedDPI.re_trace_mul_le_traceNorm_of_contraction X (c • S)
      (QuantumProver.SandwichedDPI.contraction_deficit_of_norm_le_one hnorm)
    rw [← nuclearNorm_eq_sharedTraceNorm] at ht
    have ht' : ‖S‖⁻¹ * (S * X).trace.re ≤ nuclearNorm X := by
      simpa only [Matrix.smul_mul, Matrix.trace_smul, c, smul_eq_mul,
        Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] using ht
    have hm := mul_le_mul_of_nonneg_left ht' hn.le
    rw [← mul_assoc, mul_inv_cancel₀ hn.ne', one_mul] at hm
    exact hm

theorem unitary_opNorm_le_one {U : Matrix J J ℂ} (hU : U ∈ Matrix.unitaryGroup J ℂ) :
    ‖U‖ ≤ 1 := by
  have hu : Uᴴ * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hU
  have hcap : ((1 : ℝ) • (1 : Matrix J J ℂ) - Uᴴ * U).PosSemidef := by
    simpa only [one_smul, hu, sub_self] using (Matrix.PosSemidef.zero (n := J) (R := ℂ))
  have hsq := GlobalMatrixSplit.norm_sq_le_of_right_gram (by norm_num : (0 : ℝ) ≤ 1) hcap
  nlinarith [norm_nonneg U]

theorem pullback_difference_norm_le (S : Matrix J J ℂ) (V W : Matrix J I ℂ)
    (hS : ‖S‖ ≤ 1) (hV : ‖V‖ ≤ 1) (hW : ‖W‖ ≤ 1)
    {delta : ℝ} (hdiff : ‖V - W‖ ≤ delta) :
    ‖Vᴴ * S * V - Wᴴ * S * W‖ ≤ 2 * delta := by
  have hd : 0 ≤ delta := (norm_nonneg _).trans hdiff
  have heq : Vᴴ * S * V - Wᴴ * S * W =
      (V - W)ᴴ * S * V + Wᴴ * S * (V - W) := by
    rw [Matrix.conjTranspose_sub, Matrix.sub_mul, Matrix.sub_mul, Matrix.mul_sub]
    abel
  have hDS : ‖(V - W)ᴴ * S‖ ≤ delta := by
    calc
      _ ≤ ‖(V - W)ᴴ‖ * ‖S‖ := Matrix.l2_opNorm_mul _ _
      _ = ‖V - W‖ * ‖S‖ := by rw [Matrix.l2_opNorm_conjTranspose]
      _ ≤ ‖V - W‖ * 1 := mul_le_mul_of_nonneg_left hS (norm_nonneg _)
      _ ≤ delta := by simpa only [mul_one] using hdiff
  have hWS : ‖Wᴴ * S‖ ≤ 1 := by
    calc
      _ ≤ ‖Wᴴ‖ * ‖S‖ := Matrix.l2_opNorm_mul _ _
      _ = ‖W‖ * ‖S‖ := by rw [Matrix.l2_opNorm_conjTranspose]
      _ ≤ 1 * 1 := mul_le_mul hW hS (norm_nonneg S) (by norm_num)
      _ = 1 := by norm_num
  have hfirst : ‖(V - W)ᴴ * S * V‖ ≤ delta :=
    (Matrix.l2_opNorm_mul _ _).trans
      (by simpa only [mul_one] using mul_le_mul hDS hV (norm_nonneg V) hd)
  have hsecond : ‖Wᴴ * S * (V - W)‖ ≤ delta :=
    (Matrix.l2_opNorm_mul _ _).trans
      (by simpa only [one_mul] using mul_le_mul hWS hdiff (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1))
  rw [heq]
  exact (norm_add_le _ _).trans (by linarith)

theorem trace_pullback_difference (S : Matrix J J ℂ) (V W : Matrix J I ℂ)
    (X : Matrix I I ℂ) :
    (S * (V * X * Vᴴ - W * X * Wᴴ)).trace =
      ((Vᴴ * S * V - Wᴴ * S * W) * X).trace := by
  have hcycle (A : Matrix J I ℂ) :
      (S * (A * X * Aᴴ)).trace = ((Aᴴ * S * A) * X).trace := by
    calc
      _ = ((S * A * X) * Aᴴ).trace := by simp only [Matrix.mul_assoc]
      _ = (Aᴴ * (S * A * X)).trace := Matrix.trace_mul_comm _ _
      _ = _ := by simp only [Matrix.mul_assoc]
  rw [Matrix.mul_sub, Matrix.trace_sub, Matrix.sub_mul, Matrix.trace_sub, hcycle V, hcycle W]

theorem sandwich_nuclearNorm_le_two_delta (V W : Matrix J I ℂ)
    (hV : ‖V‖ ≤ 1) (hW : ‖W‖ ≤ 1) {delta : ℝ} (hdiff : ‖V - W‖ ≤ delta)
    (X : Matrix I I ℂ) :
    nuclearNorm (V * X * Vᴴ - W * X * Wᴴ) ≤ 2 * delta * nuclearNorm X := by
  obtain ⟨U, hU, htrace⟩ := QuantumProver.SandwichedDPI.exists_unitary_traceNorm_attainer
    (V * X * Vᴴ - W * X * Wᴴ)
  have htrace' : (U * (V * X * Vᴴ - W * X * Wᴴ)).trace.re =
      nuclearNorm (V * X * Vᴴ - W * X * Wᴴ) := by
    simpa only [← nuclearNorm_eq_sharedTraceNorm] using htrace
  rw [← htrace', trace_pullback_difference]
  exact (re_trace_pairing_le_opNorm_nuclear _ X).trans
    (mul_le_mul_of_nonneg_right
      (pullback_difference_norm_le U V W (unitary_opNorm_le_one hU) hV hW hdiff)
      (nuclearNorm_nonneg X))

theorem traceEnvironment_eq_partialTraceRight (X : Matrix (O × E) (O × E) ℂ) :
    StackTraceNorm.traceEnvironment X = QuantumProver.QuantumEntropy.partialTrace_right X := by
  ext o p
  simp only [StackTraceNorm.traceEnvironment_apply, QuantumProver.QuantumEntropy.partialTrace_right]

theorem traceEnvironment_nuclearNorm_le (X : Matrix (O × E) (O × E) ℂ) :
    nuclearNorm (StackTraceNorm.traceEnvironment X) ≤ nuclearNorm X := by
  have h := QuantumProver.SandwichedDPI.traceNorm_krausAction_le
    (QuantumProver.QuantumEntropy.rightTraceKraus (I := O) (J := E))
    QuantumProver.QuantumEntropy.rightTraceKraus_complete X
  rw [QuantumProver.QuantumEntropy.rightTraceKraus_action] at h
  rw [traceEnvironment_eq_partialTraceRight]
  simpa only [← nuclearNorm_eq_sharedTraceNorm] using h

theorem traceEnvironment_sub (A B : Matrix (O × E) (O × E) ℂ) :
    StackTraceNorm.traceEnvironment (A - B) =
      StackTraceNorm.traceEnvironment A - StackTraceNorm.traceEnvironment B :=
  (StackTraceNorm.traceEnvironmentMap (O := O) (E := E)).map_sub A B

theorem traceEnvironment_stackKraus_sandwich (K : E → Matrix O I ℂ)
    (X : Matrix I I ℂ) :
    StackTraceNorm.traceEnvironment (stackKraus K * X * (stackKraus K)ᴴ) =
      QuantumProver.ElegantJointMeasurement.CP.krausMap K X := by
  ext o p
  rw [StackTraceNorm.traceEnvironment_apply]
  change (∑ e : E, (stackKraus K * X * (stackKraus K)ᴴ) (o, e) (p, e)) =
    (∑ e : E, K e * X * (K e)ᴴ) o p
  rw [Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro e _
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, stackKraus]

theorem krausMap_difference_nuclearNorm_le (K L : E → Matrix O I ℂ)
    (hK : ‖stackKraus K‖ ≤ 1) (hL : ‖stackKraus L‖ ≤ 1)
    {delta : ℝ} (hdiff : ‖stackKraus K - stackKraus L‖ ≤ delta)
    (X : Matrix I I ℂ) :
    nuclearNorm (QuantumProver.ElegantJointMeasurement.CP.krausMap K X - QuantumProver.ElegantJointMeasurement.CP.krausMap L X) ≤ 2 * delta * nuclearNorm X := by
  have h := traceEnvironment_nuclearNorm_le
    (stackKraus K * X * (stackKraus K)ᴴ - stackKraus L * X * (stackKraus L)ᴴ)
  rw [traceEnvironment_sub, traceEnvironment_stackKraus_sandwich,
    traceEnvironment_stackKraus_sandwich] at h
  exact h.trans (sandwich_nuclearNorm_le_two_delta _ _ hK hL hdiff X)

theorem reference_krausMap_difference_nuclearNorm_le (K L : E → Matrix O I ℂ)
    (hK : ‖stackKraus K‖ ≤ 1) (hL : ‖stackKraus L‖ ≤ 1)
    {delta : ℝ} (hdiff : ‖stackKraus K - stackKraus L‖ ≤ delta)
    (R : Type*) [Fintype R] [DecidableEq R]
    (X : Matrix (I × R) (I × R) ℂ) :
    nuclearNorm (CPTPKraus.amplify (QuantumProver.ElegantJointMeasurement.CP.krausMap K) R X -
      CPTPKraus.amplify (QuantumProver.ElegantJointMeasurement.CP.krausMap L) R X) ≤ 2 * delta * nuclearNorm X := by
  have hK' := (referenceKraus_stack_norm_le K R).trans hK
  have hL' := (referenceKraus_stack_norm_le L R).trans hL
  have hd := (referenceKraus_stack_difference_norm_le K L R).trans hdiff
  have h := krausMap_difference_nuclearNorm_le (referenceKraus K R) (referenceKraus L R)
    hK' hL' hd X
  simpa only [referenceKraus_reconstruct] using h

theorem diamondBudget_krausMap_difference_le (K L : E → Matrix O I ℂ)
    (hK : ‖stackKraus K‖ ≤ 1) (hL : ‖stackKraus L‖ ≤ 1)
    {delta : ℝ} (hdiff : ‖stackKraus K - stackKraus L‖ ≤ delta) :
    diamondBudget (QuantumProver.ElegantJointMeasurement.CP.krausMap K - QuantumProver.ElegantJointMeasurement.CP.krausMap L) ≤ ((2 * delta : ℝ) : EReal) := by
  rw [diamondBudget_le_iff]
  intro k X hX
  apply EReal.coe_le_coe_iff.mpr
  rw [amplifyMap_sub]
  change nuclearNorm (CPTPKraus.amplify (QuantumProver.ElegantJointMeasurement.CP.krausMap K) (Fin k) X -
    CPTPKraus.amplify (QuantumProver.ElegantJointMeasurement.CP.krausMap L) (Fin k) X) ≤ 2 * delta
  have hd : 0 ≤ delta := (norm_nonneg _).trans hdiff
  exact (reference_krausMap_difference_nuclearNorm_le K L hK hL hdiff (Fin k) X).trans
    (by nlinarith [nuclearNorm_nonneg X])

end QuantumProver.SuperchannelDiscrimination.ChannelUniformDiamond

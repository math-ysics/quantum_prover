import QuantumProver.InformationTheory.SuperchannelDiscrimination.ChannelTestingDual
import QuantumProver.InformationTheory.SuperchannelDiscrimination.ChannelUniformTensorTransport
import QuantumProver.InformationTheory.SuperchannelDiscrimination.ChannelUniformDiamond

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace QuantumProver.SuperchannelDiscrimination.ChannelUniformFactory

open Matrix KrausCompletion CPWrappers FlaggedStates TensorEntropy ChannelRegularization
open ChannelUniformApproximation TensorWordTruncation Filter
open scoped BigOperators ComplexOrder MatrixOrder Matrix Kronecker Matrix.Norms.L2Operator Topology

variable {I O E F : Type*} [Fintype I] [Fintype O] [Fintype E] [Fintype F]
  [DecidableEq I] [DecidableEq O] [DecidableEq E] [DecidableEq F]

def powerRowsEquiv (A : Type*) : (n : ℕ) → (Fin n → A) ≃ TensorIndex A n
  | 0 =>
    { toFun := fun _ => PUnit.unit
      invFun := fun _ j => Fin.elim0 j
      left_inv := fun x => funext (fun j => Fin.elim0 j)
      right_inv := fun x => by cases x; rfl }
  | n + 1 => (TensorPinching.rowsSuccEquiv A n).trans
      (Equiv.prodCongr (powerRowsEquiv A n) (Equiv.refl A))

theorem tensorUnitOutput_rows (Φ : FiniteCPTP I O) (n : ℕ)
    (i j : Fin n → I) (o p : Fin n → O) :
    tensorUnitOutput Φ n (powerRowsEquiv I n i) (powerRowsEquiv I n j)
      (powerRowsEquiv O n o) (powerRowsEquiv O n p) =
        ∏ a : Fin n, Φ.map (Matrix.single (i a) (j a) 1) (o a) (p a) := by
  induction n with
  | zero => simpa [tensorUnitOutput, Matrix.one_apply] using (Subsingleton.elim o p)
  | succ n ih =>
      change tensorUnitOutput Φ n
          (powerRowsEquiv I n (fun a => i a.castSucc))
          (powerRowsEquiv I n (fun a => j a.castSucc))
          (powerRowsEquiv O n (fun a => o a.castSucc))
          (powerRowsEquiv O n (fun a => p a.castSucc)) *
        Φ.map (Matrix.single (i (Fin.last n)) (j (Fin.last n)) 1)
          (o (Fin.last n)) (p (Fin.last n)) = _
      rw [ih, Fin.prod_univ_castSucc]

theorem tensorKraus_matrix_unit (K : E → Matrix O I ℂ) (n : ℕ)
    (i j : Fin n → I) (o p : Fin n → O) :
    QuantumProver.ElegantJointMeasurement.CP.krausMap (ChannelUniformApproximation.tensorKraus K n)
        (Matrix.single i j 1) o p =
      ∏ a : Fin n, QuantumProver.ElegantJointMeasurement.CP.krausMap K (Matrix.single (i a) (j a) 1) (o a) (p a) := by
  change (∑ f : Fin n → E, ChannelUniformApproximation.tensorKraus K n f *
    Matrix.single i j (1 : ℂ) * (ChannelUniformApproximation.tensorKraus K n f)ᴴ) o p = _
  simp only [Matrix.sum_apply, QuantumProver.ElegantJointMeasurement.CP.kraus_matrix_unit,
    ChannelUniformApproximation.tensorKraus, tensorMatrix, map_prod]
  change (∑ f : Fin n → E,
    (∏ a : Fin n, (K (f a)) (o a) (i a)) *
      (∏ a : Fin n, star ((K (f a)) (p a) (j a)))) = _
  calc
    _ = ∑ f : Fin n → E, ∏ a : Fin n,
        (K (f a)) (o a) (i a) * star ((K (f a)) (p a) (j a)) := by
      apply Finset.sum_congr rfl
      intro f _
      exact (Finset.prod_mul_distrib).symm
    _ = ∏ a : Fin n, ∑ e : E,
        (K e) (o a) (i a) * star ((K e) (p a) (j a)) := by
      rw [Fintype.prod_sum]
    _ = _ := by
      apply Finset.prod_congr rfl
      intro a _
      change _ = (∑ e : E, K e * Matrix.single (i a) (j a) (1 : ℂ) * (K e)ᴴ) (o a) (p a)
      simp only [Matrix.sum_apply, QuantumProver.ElegantJointMeasurement.CP.kraus_matrix_unit, starRingEnd_apply]

def powerKraus (K : E → Matrix O I ℂ) (n : ℕ) :
    (Fin n → E) → Matrix (TensorIndex O n) (TensorIndex I n) ℂ :=
  fun e => (ChannelUniformApproximation.tensorKraus K n e).submatrix
    (powerRowsEquiv O n).symm (powerRowsEquiv I n).symm

theorem powerKraus_map (Φ : FiniteCPTP I O) (K : E → Matrix O I ℂ)
    (hK : QuantumProver.ElegantJointMeasurement.CP.krausMap K = Φ.map) (n : ℕ) :
    QuantumProver.ElegantJointMeasurement.CP.krausMap (powerKraus K n) = (channelPower Φ n).map := by
  apply matrixMap_ext_units
  intro i j
  ext o p
  change (∑ e : Fin n → E, powerKraus K n e * Matrix.single i j (1 : ℂ) *
    (powerKraus K n e)ᴴ) o p = _
  simp only [Matrix.sum_apply, QuantumProver.ElegantJointMeasurement.CP.kraus_matrix_unit, powerKraus,
    Matrix.submatrix_apply]
  have ht := tensorKraus_matrix_unit K n ((powerRowsEquiv I n).symm i)
    ((powerRowsEquiv I n).symm j) ((powerRowsEquiv O n).symm o)
      ((powerRowsEquiv O n).symm p)
  change (∑ e : Fin n → E, ChannelUniformApproximation.tensorKraus K n e *
    Matrix.single ((powerRowsEquiv I n).symm i) ((powerRowsEquiv I n).symm j) (1 : ℂ) *
      (ChannelUniformApproximation.tensorKraus K n e)ᴴ)
    ((powerRowsEquiv O n).symm o) ((powerRowsEquiv O n).symm p) = _ at ht
  simp only [Matrix.sum_apply, QuantumProver.ElegantJointMeasurement.CP.kraus_matrix_unit] at ht
  change (∑ e : Fin n → E, ChannelUniformApproximation.tensorKraus K n e
      ((powerRowsEquiv O n).symm o) ((powerRowsEquiv I n).symm i) *
    star (ChannelUniformApproximation.tensorKraus K n e
      ((powerRowsEquiv O n).symm p) ((powerRowsEquiv I n).symm j))) = _
  have hl : (∑ e : Fin n → E, ChannelUniformApproximation.tensorKraus K n e
      ((powerRowsEquiv O n).symm o) ((powerRowsEquiv I n).symm i) *
    star (ChannelUniformApproximation.tensorKraus K n e
      ((powerRowsEquiv O n).symm p) ((powerRowsEquiv I n).symm j))) =
    ∏ a : Fin n, Φ.map (Matrix.single
      (((powerRowsEquiv I n).symm i) a) (((powerRowsEquiv I n).symm j) a) 1)
      (((powerRowsEquiv O n).symm o) a) (((powerRowsEquiv O n).symm p) a) := by
    rw [← hK]
    exact ht
  rw [hl, channelPower_map_single]
  simpa only [Equiv.apply_symm_apply] using (tensorUnitOutput_rows Φ n
    ((powerRowsEquiv I n).symm i) ((powerRowsEquiv I n).symm j)
    ((powerRowsEquiv O n).symm o) ((powerRowsEquiv O n).symm p)).symm

theorem powerKraus_complete (Φ : FiniteCPTP I O) (K : E → Matrix O I ℂ)
    (hK : QuantumProver.ElegantJointMeasurement.CP.krausMap K = Φ.map) (n : ℕ) :
    (∑ e : Fin n → E, (powerKraus K n e)ᴴ * powerKraus K n e) = 1 := by
  apply (QuantumProver.ElegantJointMeasurement.CP.krausMap_trace_preserving_iff _).mp
  rw [powerKraus_map Φ K hK n]
  exact (channelPower Φ n).tracePreserving

theorem powerKraus_mixEnvironment (B : F → Matrix O I ℂ) (n : ℕ)
    (C : Matrix (Fin n → E) (Fin n → F) ℂ) :
    mixEnvironment C (powerKraus B n) =
      fun e => (mixEnvironment C (ChannelUniformApproximation.tensorKraus B n) e).submatrix
        (powerRowsEquiv O n).symm (powerRowsEquiv I n).symm := by
  ext e o i
  simp only [mixEnvironment, powerKraus, Matrix.sum_apply, Matrix.smul_apply,
    Matrix.submatrix_apply, smul_eq_mul]

theorem powerKraus_stack_norm (K : E → Matrix O I ℂ) (n : ℕ) :
    ‖stackKraus (powerKraus K n)‖ =
      ‖stackKraus (ChannelUniformApproximation.tensorKraus K n)‖ := by
  have heq : stackKraus (powerKraus K n) =
      (stackKraus (ChannelUniformApproximation.tensorKraus K n)).submatrix
        (Equiv.prodCongr (powerRowsEquiv O n).symm (Equiv.refl (Fin n → E)))
          (powerRowsEquiv I n).symm := by
    ext x i
    rfl
  rw [heq]
  exact norm_submatrix_equiv _ _ _

theorem powerKraus_stack_difference_norm (K : E → Matrix O I ℂ)
    (B : F → Matrix O I ℂ) (n : ℕ) (C : Matrix (Fin n → E) (Fin n → F) ℂ) :
    ‖stackKraus (powerKraus K n) - stackKraus (mixEnvironment C (powerKraus B n))‖ =
      ‖stackKraus (ChannelUniformApproximation.tensorKraus K n) -
        stackKraus (mixEnvironment C (ChannelUniformApproximation.tensorKraus B n))‖ := by
  have heq : stackKraus (powerKraus K n) - stackKraus (mixEnvironment C (powerKraus B n)) =
      (stackKraus (ChannelUniformApproximation.tensorKraus K n) -
        stackKraus (mixEnvironment C (ChannelUniformApproximation.tensorKraus B n))).submatrix
        (Equiv.prodCongr (powerRowsEquiv O n).symm (Equiv.refl (Fin n → E)))
          (powerRowsEquiv I n).symm := by
    rw [powerKraus_mixEnvironment]
    ext x i
    rfl
  rw [heq]
  exact norm_submatrix_equiv _ _ _

theorem exists_tensor_weak_family (Φ Ψ : FiniteCPTP I O) [Nonempty I]
    (K : E → Matrix O I ℂ) (B : F → Matrix O I ℂ)
    (hK : QuantumProver.ElegantJointMeasurement.CP.krausMap K = Φ.map) (hB : QuantumProver.ElegantJointMeasurement.CP.krausMap B = Ψ.map)
    {budget r delta : ℝ} (hr : 0 < r) (hd : 0 ≤ delta)
    (hReg : regularizedRelativeEntropyBits Φ Ψ ≤ (budget : EReal))
    (hgap : budget < r * delta ^ 2) :
    ∃ C : (n : ℕ) → Matrix (Fin n → E) (Fin n → F) ℂ,
      ∀ᶠ n : ℕ in atTop,
        ‖C n‖ ≤ (2 : ℝ) ^ ((n : ℝ) * r / 2) ∧
        ‖stackKraus (ChannelUniformApproximation.tensorKraus K n) -
          stackKraus (mixEnvironment (C n) (ChannelUniformApproximation.tensorKraus B n))‖ ≤ delta := by
  obtain ⟨C, hC⟩ := ChannelTestingDual.exists_channelPower_global_weak_kraus_family
    Φ Ψ hr hd hReg hgap (fun n => Fin n → E) (fun n => Fin n → F)
    (fun n => powerKraus K n) (fun n => powerKraus B n)
    (fun n => powerKraus_map Φ K hK n) (fun n => powerKraus_map Ψ B hB n)
  refine ⟨C, ?_⟩
  filter_upwards [hC] with n hn
  exact ⟨hn.1, by simpa only [← powerKraus_stack_difference_norm] using hn.2.2.2⟩

def dilationResidual (K : E → Matrix O I ℂ) (B : F → Matrix O I ℂ) (n : ℕ)
    (C : Matrix (Fin n → E) (Fin n → F) ℂ) : ℝ :=
  ‖stackKraus (ChannelUniformApproximation.tensorKraus K n) -
    stackKraus (mixEnvironment C (ChannelUniformApproximation.tensorKraus B n))‖

def ApproximationRate (K : E → Matrix O I ℂ) (B : F → Matrix O I ℂ) (S : ℝ) : Prop :=
  ∃ C : (n : ℕ) → Matrix (Fin n → E) (Fin n → F) ℂ,
    ∃ κ γ α : ℝ, 0 < κ ∧ 0 < γ ∧ 0 < α ∧ α ≤ 1 ∧
      ∀ᶠ n : ℕ in atTop, ‖C n‖ ≤ (2 : ℝ) ^ ((n : ℝ) * S / 2) ∧
        dilationResidual K B n (C n) ≤ κ * Real.exp (-γ * (n : ℝ) ^ α)

theorem tensor_coefficient_norm_le_dyadic (C : Matrix E F ℂ) (L : ℝ)
    (hC : ‖C‖ ≤ (2 : ℝ) ^ (L / 2)) (n : ℕ) :
    ‖tensorMatrix (fun _ : Fin n => C)‖ ≤ (2 : ℝ) ^ ((n : ℝ) * L / 2) := by
  calc
    _ ≤ ∏ _ : Fin n, ‖C‖ := tensorMatrix_norm_le _
    _ = ‖C‖ ^ n := by simp
    _ ≤ ((2 : ℝ) ^ (L / 2)) ^ n := pow_le_pow_left₀ (norm_nonneg C) hC n
    _ = _ := by
      rw [← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2)]
      congr 1
      ring

theorem exact_factor_residual_zero (K : E → Matrix O I ℂ) (B : F → Matrix O I ℂ)
    (C : Matrix E F ℂ) (hC : mixEnvironment C B = K) (n : ℕ) :
    dilationResidual K B n (tensorMatrix (fun _ : Fin n => C)) = 0 := by
  unfold dilationResidual
  rw [← tensorKraus_mixEnvironment, hC, sub_self, norm_zero]

theorem exact_factor_approximationRate (K : E → Matrix O I ℂ) (B : F → Matrix O I ℂ)
    (C : Matrix E F ℂ) (L : ℝ) (hC : mixEnvironment C B = K)
    (hNorm : ‖C‖ ≤ (2 : ℝ) ^ (L / 2)) : ApproximationRate K B L := by
  refine ⟨fun n => tensorMatrix (fun _ : Fin n => C), 1, 1, 1,
    by norm_num, by norm_num, by norm_num, by norm_num, ?_⟩
  exact Eventually.of_forall fun n => ⟨tensor_coefficient_norm_le_dyadic C L hNorm n,
    by rw [exact_factor_residual_zero K B C hC n]; positivity⟩

theorem exists_exact_dyadic_factor (Φ Ψ : FiniteCPTP I O) [Nonempty I]
    (K : E → Matrix O I ℂ) (B : F → Matrix O I ℂ)
    (hK : QuantumProver.ElegantJointMeasurement.CP.krausMap K = Φ.map) (hB : QuantumProver.ElegantJointMeasurement.CP.krausMap B = Ψ.map)
    {budget : ℝ} (hReg : regularizedRelativeEntropyBits Φ Ψ ≤ (budget : EReal))
    (threshold : ℝ) :
    ∃ L : ℝ, threshold ≤ L ∧ ∃ C : Matrix E F ℂ,
      mixEnvironment C B = K ∧ ‖C‖ ≤ (2 : ℝ) ^ (L / 2) := by
  have hs := ChannelChoiSupport.choi_support_of_regularized_le_real Φ Ψ hReg
  rw [← hK, ← hB] at hs
  obtain ⟨c, hc, C, hCsq, hmix, _⟩ := exists_exact_environmental_kraus_comparison K B hs
  let q : ℝ := max 1 ‖C‖
  have hq : 0 < q := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  let ell : ℝ := 2 * Real.log q / Real.log 2
  let L := max threshold ell
  have hdyadic : (2 : ℝ) ^ (ell / 2) = q := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    have heq : Real.log 2 * (ell / 2) = Real.log q := by
      dsimp [ell]
      field_simp [(Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne']
    rw [heq, Real.exp_log hq]
  refine ⟨L, le_max_left _ _, C, hmix, ?_⟩
  calc
    ‖C‖ ≤ q := le_max_right _ _
    _ = (2 : ℝ) ^ (ell / 2) := hdyadic.symm
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (div_le_div_of_nonneg_right (le_max_right _ _) (by norm_num))

open WeakRateReduction ChannelUniformTensorTransport

theorem stretched_bound_tendsto_zero (errors : ℕ → ℝ) {κ γ α : ℝ}
    (herrors : ∀ n, 0 ≤ errors n) (hγ : 0 < γ) (hα : 0 < α)
    (hbound : ∀ᶠ n : ℕ in atTop, errors n ≤ κ * Real.exp (-γ * (n : ℝ) ^ α)) :
    Tendsto errors atTop (𝓝 0) := by
  have ht : Tendsto (fun n : ℕ => κ * Real.exp (-γ * (n : ℝ) ^ α)) atTop (𝓝 0) := by
    simpa using (nat_rpow_mul_stretched_exp_tendsto 0 hα hγ).const_mul κ
  exact squeeze_zero' (Eventually.of_forall herrors) hbound ht

theorem approximationRate_mono (K : E → Matrix O I ℂ) (B : F → Matrix O I ℂ)
    {S R : ℝ} (hSR : S ≤ R) (hS : ApproximationRate K B S) : ApproximationRate K B R := by
  obtain ⟨C, κ, γ, α, hκ, hγ, hα0, hα1, hC⟩ := hS
  refine ⟨C, κ, γ, α, hκ, hγ, hα0, hα1, ?_⟩
  filter_upwards [hC] with n hn
  refine ⟨hn.1.trans ?_, hn.2⟩
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  nlinarith [Nat.cast_nonneg (α := ℝ) n]

theorem descentRate_bounds {r L b : ℝ} (hrL : r ≤ L) (hb0 : 0 ≤ b) (hb1 : b < 1)
    (j : ℕ) : r ≤ descentRate r L b j ∧ descentRate r L b j ≤ L := by
  have ht := descentTheta_bounds hb0 hb1
  have hp0 := pow_nonneg ht.1.le j
  have hp1 : descentTheta b ^ j ≤ 1 := pow_le_one₀ ht.1.le ht.2.2.le
  unfold descentRate
  constructor
  · nlinarith [mul_nonneg hp0 (sub_nonneg.mpr hrL)]
  · nlinarith [mul_le_mul_of_nonneg_right hp1 (sub_nonneg.mpr hrL)]

theorem approximationRate_reduction_step
    (K : E → Matrix O I ℂ) (B : F → Matrix O I ℂ)
    (hK : ∑ e, (K e)ᴴ * K e = 1)
    (Cstar : Matrix E F ℂ) (hCstar : mixEnvironment Cstar B = K)
    {L r S R delta : ℝ} (hCstarNorm : ‖Cstar‖ ≤ (2 : ℝ) ^ (L / 2))
    (hd0 : 0 ≤ delta) (hd1 : delta < 1) (hrS : r ≤ S) (hSL : S ≤ L)
    (hgap : (1 - beta delta) * r + beta delta * S < R)
    (Cw : (n : ℕ) → Matrix (Fin n → E) (Fin n → F) ℂ)
    (hWeak : ∀ᶠ n : ℕ in atTop,
      ‖Cw n‖ ≤ (2 : ℝ) ^ ((n : ℝ) * r / 2) ∧ dilationResidual K B n (Cw n) ≤ delta)
    (hS : ApproximationRate K B S) : ApproximationRate K B R := by
  obtain ⟨Ca, κ, γ, α, hκ, hγ, hα0, hα1, hCa⟩ := hS
  let errors : ℕ → ℝ := fun n => dilationResidual K B n (Ca n)
  have he0 : ∀ n, 0 ≤ errors n := fun n => norm_nonneg _
  have hsource : ∀ᶠ n : ℕ in atTop, errors n ≤ κ * Real.exp (-γ * (n : ℝ) ^ α) :=
    hCa.mono fun _ h => h.2
  have hsmall := (stretched_bound_tendsto_zero errors he0 hγ hα0 hsource).eventually
    (Iio_mem_nhds (by linarith : (0 : ℝ) < (1 - delta) / 2))
  let Db := fun N => retained (Cw (blockSize N)) (Ca (blockSize N) - Cw (blockSize N))
    (blockCount N) ⌊beta delta * blockCount N⌋₊
  let Cp := fun N => integerPaddedCoefficient N (Db N)
    (tensorMatrix (fun _ : Fin (paddingSize N) => Cstar))
  let convex := (1 - beta delta) * r + beta delta * S
  have hb := beta_bounds hd0 hd1
  have hconvL : convex ≤ L := by
    dsimp [convex]
    nlinarith [mul_nonneg (sub_nonneg.mpr hb.2.le) (sub_nonneg.mpr hrS)]
  have hl := lambda_bounds hd0 hd1
  let γnext := min ((-Real.log (lambda delta)) / 2) ((γ * (2 : ℝ) ^ (-α)) / 2)
  have hγnext : 0 < γnext := stretchedExponent_pos hl.1 hl.2 hγ
  refine ⟨Cp, 2, γnext, α / 2, by norm_num, hγnext, by linarith, by linarith, ?_⟩
  have habs := eventually_dyadic_padding_absorption hgap hconvL
  have herr := eventually_full_integer_error_bound errors hl.1 hl.2 he0 hκ hγ hα0 hα1 hsource
  have hweakBlock := blockSize_tendsto_atTop.eventually hWeak
  have haccurateBlock := blockSize_tendsto_atTop.eventually hCa
  have hsmallBlock := blockSize_tendsto_atTop.eventually hsmall
  filter_upwards [hweakBlock, haccurateBlock, hsmallBlock, habs, herr]
    with N hw ha hsm hab he
  have hV := stackKraus_tensorKraus_norm_le_one K (stackKraus_norm_le_one_of_complete K hK) (blockSize N)
  have hW : ‖action (stackKraus (tensorKraus B (blockSize N))) (Cw (blockSize N)) -
      stackKraus (tensorKraus K (blockSize N))‖ ≤ delta := by
    rw [← stackKraus_mixEnvironment_action, norm_sub_rev]
    exact hw.2
  have hA : ‖action (stackKraus (tensorKraus B (blockSize N))) (Ca (blockSize N)) -
      stackKraus (tensorKraus K (blockSize N))‖ ≤ errors (blockSize N) := by
    rw [← stackKraus_mixEnvironment_action, norm_sub_rev]
    exact le_rfl
  have hfirst := same_environment_weak_rate_reduction
    (stackKraus (tensorKraus B (blockSize N))) (Cw (blockSize N)) (Ca (blockSize N))
    (stackKraus (tensorKraus K (blockSize N))) hd1 hsm.le hV hW hA
    (blockSize N) (blockCount N) hrS hw.1 ha.1
  constructor
  · calc
      ‖Cp N‖ ≤ ‖Db N‖ * ‖tensorMatrix (fun _ : Fin (paddingSize N) => Cstar)‖ :=
        integerPaddedCoefficient_norm_le _ _ _
      _ ≤ ((3 : ℝ) ^ blockCount N * (2 : ℝ) ^
          ((blockSize N : ℝ) * (blockCount N : ℝ) * convex / 2)) *
          (2 : ℝ) ^ ((paddingSize N : ℝ) * L / 2) :=
        mul_le_mul hfirst.1 (tensor_coefficient_norm_le_dyadic Cstar L hCstarNorm _)
          (norm_nonneg _) (by positivity)
      _ ≤ _ := hab
  · have hpad := stackKraus_tensorKraus_norm_le_one K (stackKraus_norm_le_one_of_complete K hK) (paddingSize N)
    have hphysical := integerPaddedCoefficient_residual_norm_le K B Cstar hCstar N (Db N) hpad
    rw [tensorStack_mixed_difference_norm_eq (tensorKraus K (blockSize N))
      (tensorKraus B (blockSize N)) (blockCount N) (Db N)] at hphysical
    change dilationResidual K B N (Cp N) ≤ _
    unfold dilationResidual
    rw [norm_sub_rev]
    exact hphysical.trans (hfirst.2.trans he)

theorem approximationRate_finite_descent
    (K : E → Matrix O I ℂ) (B : F → Matrix O I ℂ)
    (hK : ∑ e, (K e)ᴴ * K e = 1)
    (Cstar : Matrix E F ℂ) (hCstar : mixEnvironment Cstar B = K)
    {L r R delta : ℝ} (hCstarNorm : ‖Cstar‖ ≤ (2 : ℝ) ^ (L / 2))
    (hd0 : 0 ≤ delta) (hd1 : delta < 1) (hrL : r < L) (hrR : r < R)
    (Cw : (n : ℕ) → Matrix (Fin n → E) (Fin n → F) ℂ)
    (hWeak : ∀ᶠ n : ℕ in atTop,
      ‖Cw n‖ ≤ (2 : ℝ) ^ ((n : ℝ) * r / 2) ∧ dilationResidual K B n (Cw n) ≤ delta) :
    ApproximationRate K B R := by
  have hb := beta_bounds hd0 hd1
  have hdescent : ∀ j, ApproximationRate K B (descentRate r L (beta delta) j) := by
    intro j
    induction j with
    | zero => simpa [descentRate] using exact_factor_approximationRate K B Cstar L hCstar hCstarNorm
    | succ j ih =>
      have hbounds := descentRate_bounds hrL.le hb.1.le hb.2 j
      exact approximationRate_reduction_step K B hK Cstar hCstar hCstarNorm hd0 hd1
        hbounds.1 hbounds.2 (descentRate_step_gap hb.1.le hb.2 hrL j) Cw hWeak ih
  obtain ⟨j, hj⟩ := exists_finite_descent (L := L) hb.1.le hb.2 hrR
  exact approximationRate_mono K B hj.le (hdescent j)

theorem exists_weak_error_margin {budget r : ℝ} (hb : 0 ≤ budget) (hr : 0 < r)
    (hbr : budget < r) : ∃ delta : ℝ, 0 ≤ delta ∧ delta < 1 ∧ budget < r * delta ^ 2 := by
  obtain ⟨q, hbq, hq⟩ := exists_between ((div_lt_one hr).mpr hbr)
  have hq0 : 0 < q := lt_of_le_of_lt (div_nonneg hb hr.le) hbq
  have hs0 := Real.sqrt_nonneg q
  have hsq := Real.sq_sqrt hq0.le
  have hbqr := (div_lt_iff₀ hr).mp hbq
  refine ⟨Real.sqrt q, hs0, ?_, ?_⟩ <;> nlinarith

theorem exists_accurate_tensor_family (Φ Ψ : FiniteCPTP I O) [Nonempty I]
    (K : E → Matrix O I ℂ) (B : F → Matrix O I ℂ)
    (hK : QuantumProver.ElegantJointMeasurement.CP.krausMap K = Φ.map) (hB : QuantumProver.ElegantJointMeasurement.CP.krausMap B = Ψ.map)
    {budget a : ℝ} (hReg : regularizedRelativeEntropyBits Φ Ψ ≤ (budget : EReal))
    (hba : budget < a) : ApproximationRate K B a := by
  have hb : 0 ≤ budget := by
    have h := (regularizedRelativeEntropyBits_nonneg Φ Ψ).trans hReg
    exact_mod_cast h
  let r := (budget + a) / 2
  have hr : 0 < r := by dsimp [r]; linarith
  have hbr : budget < r := by dsimp [r]; linarith
  have hra : r < a := by dsimp [r]; linarith
  obtain ⟨delta, hd0, hd1, hgap⟩ := exists_weak_error_margin hb hr hbr
  obtain ⟨Cw, hCw⟩ := exists_tensor_weak_family Φ Ψ K B hK hB hr hd0 hReg hgap
  obtain ⟨L, hL, Cstar, hCstar, hCstarNorm⟩ := exists_exact_dyadic_factor Φ Ψ K B hK hB hReg (a + 1)
  have hcomplete : ∑ e, (K e)ᴴ * K e = 1 := by
    apply (QuantumProver.ElegantJointMeasurement.CP.krausMap_trace_preserving_iff K).mp
    rw [hK]
    exact Φ.tracePreserving
  exact approximationRate_finite_descent K B hcomplete Cstar hCstar hCstarNorm
    hd0 hd1 (by linarith) hra Cw hCw

theorem normalized_stack_error_le (V W : Matrix (O × E) I ℂ)
    (hV : ‖V‖ ≤ 1) {δ : ℝ} (hδ : 0 ≤ δ) (hres : ‖V - W‖ ≤ δ) :
    ‖V - (((1 + δ)⁻¹ : ℝ) : ℂ) • W‖ ≤ 2 * δ := by
  let t : ℝ := (1 + δ)⁻¹
  have hden : 0 < 1 + δ := by linarith
  have ht0 : 0 ≤ t := (inv_pos.mpr hden).le
  have ht1 : t ≤ 1 := (inv_le_one₀ hden).mpr (by linarith)
  have hW : ‖W‖ ≤ 1 + δ := by
    calc
      ‖W‖ = ‖V - (V - W)‖ := by congr 1; abel
      _ ≤ ‖V‖ + ‖V - W‖ := norm_sub_le _ _
      _ ≤ _ := add_le_add hV hres
  have hscalar : ‖((1 - t : ℝ) : ℂ)‖ = 1 - t := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  have hdecomp : V - (t : ℂ) • W = (V - W) + ((1 - t : ℝ) : ℂ) • W := by
    simp only [Complex.ofReal_sub, Complex.ofReal_one, sub_smul, one_smul]
    abel
  calc
    _ = ‖(V - W) + ((1 - t : ℝ) : ℂ) • W‖ := congrArg norm hdecomp
    _ ≤ ‖V - W‖ + ‖((1 - t : ℝ) : ℂ) • W‖ := norm_add_le _ _
    _ = ‖V - W‖ + (1 - t) * ‖W‖ := by rw [norm_smul, hscalar]
    _ ≤ δ + (1 - t) * (1 + δ) := add_le_add hres (mul_le_mul_of_nonneg_left hW (by linarith))
    _ = _ := by
      dsimp [t]
      field_simp [hden.ne']
      ring

def normalizedCoefficient (K : E → Matrix O I ℂ) (B : F → Matrix O I ℂ) (n : ℕ)
    (C : Matrix (Fin n → E) (Fin n → F) ℂ) : Matrix (Fin n → E) (Fin n → F) ℂ :=
  (((1 + dilationResidual K B n C)⁻¹ : ℝ) : ℂ) • C

theorem normalizedCoefficient_norm_le (K : E → Matrix O I ℂ) (B : F → Matrix O I ℂ)
    (n : ℕ) (C : Matrix (Fin n → E) (Fin n → F) ℂ) :
    ‖normalizedCoefficient K B n C‖ ≤ ‖C‖ := by
  have hd : 0 ≤ dilationResidual K B n C := norm_nonneg _
  have ht0 : 0 ≤ (1 + dilationResidual K B n C)⁻¹ := by positivity
  have ht1 : (1 + dilationResidual K B n C)⁻¹ ≤ 1 :=
    (inv_le_one₀ (by linarith)).mpr (by linarith)
  rw [normalizedCoefficient, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0]
  nlinarith [norm_nonneg C]

theorem normalizedCoefficient_residual_le (K : E → Matrix O I ℂ) (B : F → Matrix O I ℂ)
    (hK : ∑ e, (K e)ᴴ * K e = 1) (n : ℕ)
    (C : Matrix (Fin n → E) (Fin n → F) ℂ) :
    dilationResidual K B n (normalizedCoefficient K B n C) ≤ 2 * dilationResidual K B n C := by
  have hstack : stackKraus (mixEnvironment (normalizedCoefficient K B n C) (tensorKraus B n)) =
      (((1 + dilationResidual K B n C)⁻¹ : ℝ) : ℂ) • stackKraus (mixEnvironment C (tensorKraus B n)) := by
    rw [normalizedCoefficient, mixEnvironment_smul]
    rfl
  unfold dilationResidual at ⊢
  rw [hstack]
  exact normalized_stack_error_le _ _
    (stackKraus_tensorKraus_norm_le_one K (stackKraus_norm_le_one_of_complete K hK) n)
    (norm_nonneg _) le_rfl

theorem exists_normalized_channel_family (Φ Ψ : FiniteCPTP I O) [Nonempty I]
    (K : E → Matrix O I ℂ) (B : F → Matrix O I ℂ)
    (hK : QuantumProver.ElegantJointMeasurement.CP.krausMap K = Φ.map) (hB : QuantumProver.ElegantJointMeasurement.CP.krausMap B = Ψ.map)
    {budget a : ℝ} (hReg : regularizedRelativeEntropyBits Φ Ψ ≤ (budget : EReal))
    (hba : budget < a) :
    ∃ C : (n : ℕ) → Matrix (Fin n → E) (Fin n → F) ℂ,
      (∀ n, CPTPKraus.CompletelyPositive (QuantumProver.ElegantJointMeasurement.CP.krausMap (mixEnvironment (C n) (powerKraus B n))) ∧
        CPTPKraus.TraceNonincreasing (QuantumProver.ElegantJointMeasurement.CP.krausMap (mixEnvironment (C n) (powerKraus B n)))) ∧
      ∃ κ γ α : ℝ, 0 < κ ∧ 0 < γ ∧ 0 < α ∧ α ≤ 1 ∧
        ∀ᶠ n : ℕ in atTop,
          CPTPKraus.CPDom (QuantumProver.ElegantJointMeasurement.CP.krausMap (mixEnvironment (C n) (powerKraus B n)))
            (channelPower Ψ n).map ((2 : ℝ) ^ ((n : ℝ) * a)) ∧
          ‖stackKraus (powerKraus K n) - stackKraus (mixEnvironment (C n) (powerKraus B n))‖ ≤
            κ * Real.exp (-γ * (n : ℝ) ^ α) := by
  obtain ⟨Craw, κ, γ, α, hκ, hγ, hα0, hα1, hraw⟩ := exists_accurate_tensor_family Φ Ψ K B hK hB hReg hba
  let C := fun n => normalizedCoefficient K B n (Craw n)
  have hcomplete : ∑ e, (K e)ᴴ * K e = 1 := by
    apply (QuantumProver.ElegantJointMeasurement.CP.krausMap_trace_preserving_iff K).mp
    rw [hK]
    exact Φ.tracePreserving
  have hproperties (n : ℕ) (t : ℝ) (ht : 0 ≤ t) (hnorm : ‖Craw n‖ ^ 2 ≤ t) :
      CPTPKraus.CompletelyPositive (QuantumProver.ElegantJointMeasurement.CP.krausMap (mixEnvironment (C n) (powerKraus B n))) ∧
        CPTPKraus.TraceNonincreasing (QuantumProver.ElegantJointMeasurement.CP.krausMap (mixEnvironment (C n) (powerKraus B n))) ∧
        CPTPKraus.CPDom (QuantumProver.ElegantJointMeasurement.CP.krausMap (mixEnvironment (C n) (powerKraus B n)))
          (channelPower Ψ n).map t := by
    have hp := normalized_environmental_approximation (powerKraus K n) (powerKraus B n) (Craw n)
      (δ := dilationResidual K B n (Craw n))
      (powerKraus_complete Φ K hK n) (norm_nonneg _) ht hnorm
      (by rw [powerKraus_stack_difference_norm]; exact le_rfl)
    dsimp only at hp
    rw [powerKraus_map Ψ B hB n] at hp
    exact ⟨hp.1, hp.2.1, hp.2.2.1⟩
  refine ⟨C, (fun n => by
    have hp := hproperties n (‖Craw n‖ ^ 2) (sq_nonneg _) le_rfl
    exact ⟨hp.1, hp.2.1⟩),
    2 * κ, γ, α, by positivity, hγ, hα0, hα1, ?_⟩
  filter_upwards [hraw] with n hn
  have hcap : ‖Craw n‖ ^ 2 ≤ (2 : ℝ) ^ ((n : ℝ) * a) := by
    rw [← dyadic_half_sq ((n : ℝ) * a)]
    exact pow_le_pow_left₀ (norm_nonneg _) hn.1 2
  refine ⟨(hproperties n _ (Real.rpow_nonneg (by norm_num) _) hcap).2.2, ?_⟩
  rw [powerKraus_stack_difference_norm]
  calc
    _ ≤ 2 * dilationResidual K B n (Craw n) := normalizedCoefficient_residual_le K B hcomplete n (Craw n)
    _ ≤ 2 * (κ * Real.exp (-γ * (n : ℝ) ^ α)) := mul_le_mul_of_nonneg_left hn.2 (by norm_num)
    _ = _ := by ring

theorem fixed_padding_dyadic_absorption {v a L : ℝ} (hva : v < a) (hvL : v ≤ L)
    (m : ℕ) (hm : 0 < m) :
    ∀ᶠ N : ℕ in atTop,
      (2 : ℝ) ^ ((m : ℝ) * (N / m : ℕ) * v / 2) *
        (2 : ℝ) ^ ((N % m : ℕ) * L / 2) ≤ (2 : ℝ) ^ ((N : ℝ) * a / 2) := by
  have hlarge : ∀ᶠ N : ℕ in atTop, (m : ℝ) * (L - v) / (a - v) ≤ (N : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop _)
  filter_upwards [hlarge] with N hN
  have hmul := (div_le_iff₀ (sub_pos.mpr hva)).mp hN
  have hmod : ((N % m : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast (Nat.mod_lt N hm).le
  have hid : ((N / m : ℕ) : ℝ) * m + (N % m : ℕ) = (N : ℝ) := by
    exact_mod_cast (show (N / m) * m + N % m = N by simpa only [Nat.mul_comm] using Nat.div_add_mod N m)
  have hpad := mul_le_mul_of_nonneg_right hmod (sub_nonneg.mpr hvL)
  rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  nlinarith [congrArg (fun x : ℝ => x * v) hid]

theorem geometric_fixed_blocks_exponential {lam : ℝ} (hl0 : 0 < lam) (hl1 : lam < 1)
    (m : ℕ) (hm : 0 < m) (N : ℕ) :
    lam ^ (N / m) ≤ Real.exp (-Real.log lam) *
      Real.exp (-((-Real.log lam) / (m : ℝ)) * (N : ℝ)) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hlog := Real.log_neg hl0 hl1
  have hmod : ((N % m : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast (Nat.mod_lt N hm).le
  have hid : ((N / m : ℕ) : ℝ) * m + (N % m : ℕ) = (N : ℝ) := by
    exact_mod_cast (show (N / m) * m + N % m = N by simpa only [Nat.mul_comm] using Nat.div_add_mod N m)
  have hdiv : (N : ℝ) / m ≤ ((N / m : ℕ) : ℝ) + 1 := (div_le_iff₀ hmR).mpr (by nlinarith)
  have hlogmul := mul_le_mul_of_nonpos_left hdiv hlog.le
  have hexponent : Real.log lam * ((N / m : ℕ) : ℝ) ≤
      -Real.log lam + -((-Real.log lam) / (m : ℝ)) * (N : ℝ) := by
    have heq : -Real.log lam + -((-Real.log lam) / (m : ℝ)) * (N : ℝ) =
        -Real.log lam + Real.log lam * ((N : ℝ) / m) := by ring
    rw [heq]
    linarith
  rw [← Real.rpow_natCast, Real.rpow_def_of_pos hl0, ← Real.exp_add]
  exact Real.exp_le_exp.mpr hexponent

theorem fixed_block_retained_error
    (K : E → Matrix O I ℂ) (B : F → Matrix O I ℂ)
    (Cexact Ca : Matrix E F ℂ) (hmix : mixEnvironment Cexact B = K)
    (hK : ‖stackKraus K‖ ≤ 1) {epsilon : ℝ} (he0 : 0 < epsilon) (he1 : epsilon ≤ 1)
    (herr : ‖stackKraus K - stackKraus (mixEnvironment Ca B)‖ ≤ epsilon)
    (b : ℝ) (k : ℕ) :
    ‖stackKraus (mixEnvironment (retained Ca (Cexact - Ca) k ⌊b * k⌋₊) (tensorKraus B k)) -
      stackKraus (tensorKraus K k)‖ ≤ (epsilonTailBase epsilon b) ^ k := by
  have hsum : action (stackKraus B) Ca + action (stackKraus B) (Cexact - Ca) = stackKraus K := by
    rw [← action_add]
    have hc : Ca + (Cexact - Ca) = Cexact := by abel
    rw [hc, ← stackKraus_mixEnvironment_action, hmix]
  have hbad : ‖action (stackKraus B) (Cexact - Ca)‖ ≤ epsilon := by
    rw [action_sub, ← stackKraus_mixEnvironment_action, hmix, ← stackKraus_mixEnvironment_action]
    exact herr
  have htail := physical_omitted_le_epsilon_base
    (action (stackKraus B) Ca) (action (stackKraus B) (Cexact - Ca)) he0 he1
    (by rw [hsum]; exact hK) hbad b k
  have ht := retained_target_tensor_error_le
    (action (stackKraus B) Ca) (action (stackKraus B) (Cexact - Ca)) (stackKraus K)
    (e := 0) (by norm_num) hK (by rw [hsum, sub_self, norm_zero]) k ⌊b * k⌋₊ htail
  rw [tensorStack_mixed_difference_norm_eq, tensorAction_retained]
  simpa using ht

theorem exists_exponential_tensor_family (Φ Ψ : FiniteCPTP I O) [Nonempty I]
    (K : E → Matrix O I ℂ) (B : F → Matrix O I ℂ)
    (hK : QuantumProver.ElegantJointMeasurement.CP.krausMap K = Φ.map) (hB : QuantumProver.ElegantJointMeasurement.CP.krausMap B = Ψ.map)
    {budget a : ℝ} (hReg : regularizedRelativeEntropyBits Φ Ψ ≤ (budget : EReal))
    (hba : budget < a) :
    ∃ C : (n : ℕ) → Matrix (Fin n → E) (Fin n → F) ℂ,
      ∃ κ γ : ℝ, 0 < κ ∧ 0 < γ ∧ ∀ᶠ n : ℕ in atTop,
        ‖C n‖ ≤ (2 : ℝ) ^ ((n : ℝ) * a / 2) ∧
          dilationResidual K B n (C n) ≤ κ * Real.exp (-γ * (n : ℝ)) := by
  let R0 := (budget + a) / 2
  have hbR : budget < R0 := by dsimp [R0]; linarith
  have hRa : R0 < a := by dsimp [R0]; linarith
  obtain ⟨Ca, κold, γold, αold, hκold, hγold, hαold, hαold1, hCa⟩ :=
    exists_accurate_tensor_family Φ Ψ K B hK hB hReg hbR
  obtain ⟨L, hL, Cstar, hCstar, hCstarNorm⟩ := exists_exact_dyadic_factor Φ Ψ K B hK hB hReg (a + 1)
  let v := (R0 + a) / 2
  have hRv : R0 < v := by dsimp [v]; linarith
  have hva : v < a := by dsimp [v]; linarith
  have hRL : R0 ≤ L := by linarith
  have hvL : v ≤ L := by linarith
  obtain ⟨b, epsilon0, m0, hb, he0, he01, hm0, hepsilon, hblockNorm⟩ := exists_rate_parameters hRL hRv
  let epsilon := epsilon0 / 2
  have hepsilon0 : 0 < epsilon := by dsimp [epsilon]; linarith
  have hepsilonSmall : epsilon ≤ epsilon0 := by dsimp [epsilon]; linarith
  have hepsilon1 : epsilon ≤ 1 := hepsilonSmall.trans he01
  let lam := epsilonTailBase epsilon b
  have hlam0 : 0 < lam := by
    dsimp [lam, epsilonTailBase]
    exact mul_pos (Real.rpow_pos_of_pos hepsilon0 _) (by positivity)
  have hlam1 : lam < 1 := (hepsilon epsilon hepsilon0 hepsilonSmall).2
  have herrors := stretched_bound_tendsto_zero
    (fun n => dilationResidual K B n (Ca n)) (fun _ => norm_nonneg _) hγold hαold
    (hCa.mono fun _ h => h.2)
  obtain ⟨m, ⟨hCm, herrm⟩, hmlarge⟩ :=
    ((hCa.and (herrors.eventually (Iio_mem_nhds hepsilon0))).and (eventually_ge_atTop m0)).exists
  have hm : 0 < m := hm0.trans_le hmlarge
  have hcomplete : ∑ e, (K e)ᴴ * K e = 1 := by
    apply (QuantumProver.ElegantJointMeasurement.CP.krausMap_trace_preserving_iff K).mp
    rw [hK]
    exact Φ.tracePreserving
  let Cexact := tensorMatrix (fun _ : Fin m => Cstar)
  have hmixExact : mixEnvironment Cexact (tensorKraus B m) = tensorKraus K m := by
    dsimp [Cexact]
    rw [← tensorKraus_mixEnvironment, hCstar]
  have hCmL : ‖Ca m‖ ≤ (2 : ℝ) ^ ((m : ℝ) * L / 2) := hCm.1.trans (by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    nlinarith [Nat.cast_nonneg (α := ℝ) m])
  have hdiffNorm : ‖Cexact - Ca m‖ ≤ 2 * (2 : ℝ) ^ ((m : ℝ) * L / 2) := by
    calc
      _ ≤ ‖Cexact‖ + ‖Ca m‖ := norm_sub_le _ _
      _ ≤ (2 : ℝ) ^ ((m : ℝ) * L / 2) + (2 : ℝ) ^ ((m : ℝ) * L / 2) :=
        add_le_add (tensor_coefficient_norm_le_dyadic Cstar L hCstarNorm m) hCmL
      _ = _ := by ring
  let Db := fun k => retained (Ca m) (Cexact - Ca m) k ⌊b * k⌋₊
  have hDbNorm (k : ℕ) : ‖Db k‖ ≤ (2 : ℝ) ^ ((m : ℝ) * k * v / 2) :=
    (retained_norm_le_dyadic_scale (Ca m) (Cexact - Ca m) m k hRL hb.le hCm.1 hdiffNorm).trans
      (hblockNorm m hmlarge k)
  have hDbError (k : ℕ) :
      ‖stackKraus (mixEnvironment (Db k) (tensorKraus (tensorKraus B m) k)) -
        stackKraus (tensorKraus (tensorKraus K m) k)‖ ≤ lam ^ k :=
    fixed_block_retained_error (tensorKraus K m) (tensorKraus B m) Cexact (Ca m) hmixExact
      (stackKraus_tensorKraus_norm_le_one K (stackKraus_norm_le_one_of_complete K hcomplete) m)
      hepsilon0 hepsilon1 herrm.le b k
  have hlocal (k h : ℕ) :
      ∃ C : Matrix (Fin (k * m + h) → E) (Fin (k * m + h) → F) ℂ,
        ‖C‖ ≤ (2 : ℝ) ^ ((m : ℝ) * k * v / 2) * (2 : ℝ) ^ ((h : ℝ) * L / 2) ∧
          dilationResidual K B (k * m + h) C ≤ lam ^ k := by
    refine ⟨blockPaddedCoefficient k m h (Db k) (tensorMatrix (fun _ : Fin h => Cstar)), ?_, ?_⟩
    · exact (blockPaddedCoefficient_norm_le _ _ _ _ _).trans
        (mul_le_mul (hDbNorm k) (tensor_coefficient_norm_le_dyadic Cstar L hCstarNorm h)
          (norm_nonneg _) (by positivity))
    · unfold dilationResidual
      rw [norm_sub_rev]
      exact (blockPaddedCoefficient_residual_norm_le K B Cstar hCstar k m h (Db k)
        (stackKraus_tensorKraus_norm_le_one K (stackKraus_norm_le_one_of_complete K hcomplete) h)).trans
        (hDbError k)
  let κ := Real.exp (-Real.log lam)
  let γ := (-Real.log lam) / (m : ℝ)
  have hκ : 0 < κ := Real.exp_pos _
  have hγ : 0 < γ := div_pos (neg_pos.mpr (Real.log_neg hlam0 hlam1)) (by exact_mod_cast hm)
  have hExists : ∀ᶠ N : ℕ in atTop,
      ∃ C : Matrix (Fin N → E) (Fin N → F) ℂ,
        ‖C‖ ≤ (2 : ℝ) ^ ((N : ℝ) * a / 2) ∧
          dilationResidual K B N C ≤ κ * Real.exp (-γ * (N : ℝ)) := by
    filter_upwards [fixed_padding_dyadic_absorption hva hvL m hm] with N hN
    have hlen : (N / m) * m + N % m = N := by simpa only [Nat.mul_comm] using Nat.div_add_mod N m
    have hex : ∃ C : Matrix (Fin N → E) (Fin N → F) ℂ,
        ‖C‖ ≤ (2 : ℝ) ^ ((m : ℝ) * (N / m : ℕ) * v / 2) *
          (2 : ℝ) ^ ((N % m : ℕ) * L / 2) ∧ dilationResidual K B N C ≤ lam ^ (N / m) := by
      let P := fun nn : ℕ => ∃ C : Matrix (Fin nn → E) (Fin nn → F) ℂ,
        ‖C‖ ≤ (2 : ℝ) ^ ((m : ℝ) * (N / m : ℕ) * v / 2) *
          (2 : ℝ) ^ ((N % m : ℕ) * L / 2) ∧ dilationResidual K B nn C ≤ lam ^ (N / m)
      exact (congrArg P hlen).mp (hlocal (N / m) (N % m))
    obtain ⟨C, hCn, hCe⟩ := hex
    exact ⟨C, hCn.trans hN, hCe.trans (geometric_fixed_blocks_exponential hlam0 hlam1 m hm N)⟩
  obtain ⟨N0, hN0⟩ := eventually_atTop.1 hExists
  have hEach (N : ℕ) : ∃ C : Matrix (Fin N → E) (Fin N → F) ℂ,
      N0 ≤ N → ‖C‖ ≤ (2 : ℝ) ^ ((N : ℝ) * a / 2) ∧
        dilationResidual K B N C ≤ κ * Real.exp (-γ * (N : ℝ)) := by
    by_cases hN : N0 ≤ N
    · obtain ⟨C, hC⟩ := hN0 N hN
      exact ⟨C, fun _ => hC⟩
    · exact ⟨0, fun h => (hN h).elim⟩
  choose C hC using hEach
  exact ⟨C, κ, γ, hκ, hγ, (eventually_ge_atTop N0).mono fun N hN => hC N hN⟩

theorem normalized_stack_norm_le_one (V W : Matrix (O × E) I ℂ)
    (hV : ‖V‖ ≤ 1) {δ : ℝ} (hδ : 0 ≤ δ) (hres : ‖V - W‖ ≤ δ) :
    ‖(((1 + δ)⁻¹ : ℝ) : ℂ) • W‖ ≤ 1 := by
  have hden : 0 < 1 + δ := by linarith
  have hW : ‖W‖ ≤ 1 + δ := by
    calc
      ‖W‖ = ‖V - (V - W)‖ := by congr 1; abel
      _ ≤ ‖V‖ + ‖V - W‖ := norm_sub_le _ _
      _ ≤ _ := add_le_add hV hres
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hden)]
  calc
    _ ≤ (1 + δ)⁻¹ * (1 + δ) := mul_le_mul_of_nonneg_left hW (inv_nonneg.mpr hden.le)
    _ = _ := inv_mul_cancel₀ hden.ne'

theorem normalized_power_stack_norm_le_one (Φ : FiniteCPTP I O)
    (K : E → Matrix O I ℂ) (B : F → Matrix O I ℂ)
    (hK : QuantumProver.ElegantJointMeasurement.CP.krausMap K = Φ.map) (n : ℕ)
    (C : Matrix (Fin n → E) (Fin n → F) ℂ) :
    ‖stackKraus (mixEnvironment (normalizedCoefficient K B n C) (powerKraus B n))‖ ≤ 1 := by
  have hstack : stackKraus (mixEnvironment (normalizedCoefficient K B n C) (powerKraus B n)) =
      (((1 + dilationResidual K B n C)⁻¹ : ℝ) : ℂ) • stackKraus (mixEnvironment C (powerKraus B n)) := by
    rw [normalizedCoefficient, mixEnvironment_smul]
    rfl
  rw [hstack]
  exact normalized_stack_norm_le_one _ _
    (stackKraus_norm_le_one_of_complete _ (powerKraus_complete Φ K hK n))
    (norm_nonneg _) (by rw [powerKraus_stack_difference_norm]; exact le_rfl)

theorem normalized_power_diamondBudget_le (Φ : FiniteCPTP I O)
    (K : E → Matrix O I ℂ) (B : F → Matrix O I ℂ)
    (hK : QuantumProver.ElegantJointMeasurement.CP.krausMap K = Φ.map) (n : ℕ)
    (C : Matrix (Fin n → E) (Fin n → F) ℂ) :
    DiamondControl.diamondBudget ((channelPower Φ n).map -
      QuantumProver.ElegantJointMeasurement.CP.krausMap (mixEnvironment (normalizedCoefficient K B n C) (powerKraus B n))) ≤
        ((4 * dilationResidual K B n C : ℝ) : EReal) := by
  have hcomplete : ∑ e, (K e)ᴴ * K e = 1 := by
    apply (QuantumProver.ElegantJointMeasurement.CP.krausMap_trace_preserving_iff K).mp
    rw [hK]
    exact Φ.tracePreserving
  have herr : ‖stackKraus (powerKraus K n) -
      stackKraus (mixEnvironment (normalizedCoefficient K B n C) (powerKraus B n))‖ ≤
        2 * dilationResidual K B n C := by
    rw [powerKraus_stack_difference_norm]
    exact normalizedCoefficient_residual_le K B hcomplete n C
  have hd := ChannelUniformDiamond.diamondBudget_krausMap_difference_le (powerKraus K n)
    (mixEnvironment (normalizedCoefficient K B n C) (powerKraus B n))
    (stackKraus_norm_le_one_of_complete _ (powerKraus_complete Φ K hK n))
    (normalized_power_stack_norm_le_one Φ K B hK n C) herr
  rw [powerKraus_map Φ K hK n] at hd
  convert hd using 1 <;> congr 1 <;> ring

theorem exists_exponential_channel_family (Φ Ψ : FiniteCPTP I O) [Nonempty I]
    (K : E → Matrix O I ℂ) (B : F → Matrix O I ℂ)
    (hK : QuantumProver.ElegantJointMeasurement.CP.krausMap K = Φ.map) (hB : QuantumProver.ElegantJointMeasurement.CP.krausMap B = Ψ.map)
    {budget a : ℝ} (hReg : regularizedRelativeEntropyBits Φ Ψ ≤ (budget : EReal))
    (hba : budget < a) :
    ∃ Λ : (n : ℕ) → Matrix (TensorIndex I n) (TensorIndex I n) ℂ →ₗ[ℂ]
      Matrix (TensorIndex O n) (TensorIndex O n) ℂ,
      (∀ n, CPTPKraus.CompletelyPositive (Λ n) ∧ CPTPKraus.TraceNonincreasing (Λ n)) ∧
      ∃ κ γ : ℝ, 0 < κ ∧ 0 < γ ∧ ∀ᶠ n : ℕ in atTop,
        CPTPKraus.CPDom (Λ n) (channelPower Ψ n).map ((2 : ℝ) ^ ((n : ℝ) * a)) ∧
          DiamondControl.diamondBudget ((channelPower Φ n).map - Λ n) ≤
            ((κ * Real.exp (-γ * (n : ℝ)) : ℝ) : EReal) := by
  obtain ⟨Craw, κ, γ, hκ, hγ, hraw⟩ := exists_exponential_tensor_family Φ Ψ K B hK hB hReg hba
  let C := fun n => normalizedCoefficient K B n (Craw n)
  let Λ := fun n => QuantumProver.ElegantJointMeasurement.CP.krausMap (mixEnvironment (C n) (powerKraus B n))
  have hproperties (n : ℕ) (t : ℝ) (ht : 0 ≤ t) (hnorm : ‖Craw n‖ ^ 2 ≤ t) :
      CPTPKraus.CompletelyPositive (Λ n) ∧ CPTPKraus.TraceNonincreasing (Λ n) ∧
        CPTPKraus.CPDom (Λ n) (channelPower Ψ n).map t := by
    have hp := normalized_environmental_approximation (powerKraus K n) (powerKraus B n) (Craw n)
      (δ := dilationResidual K B n (Craw n))
      (powerKraus_complete Φ K hK n) (norm_nonneg _) ht hnorm
      (by rw [powerKraus_stack_difference_norm]; exact le_rfl)
    dsimp only at hp
    rw [powerKraus_map Ψ B hB n] at hp
    exact ⟨hp.1, hp.2.1, hp.2.2.1⟩
  refine ⟨Λ, (fun n => by
    have hp := hproperties n (‖Craw n‖ ^ 2) (sq_nonneg _) le_rfl
    exact ⟨hp.1, hp.2.1⟩), 4 * κ, γ, by positivity, hγ, ?_⟩
  filter_upwards [hraw] with n hn
  have hcap : ‖Craw n‖ ^ 2 ≤ (2 : ℝ) ^ ((n : ℝ) * a) := by
    rw [← dyadic_half_sq ((n : ℝ) * a)]
    exact pow_le_pow_left₀ (norm_nonneg _) hn.1 2
  refine ⟨(hproperties n _ (Real.rpow_nonneg (by norm_num) _) hcap).2.2, ?_⟩
  exact (normalized_power_diamondBudget_le Φ K B hK n (Craw n)).trans
    (EReal.coe_le_coe_iff.mpr (by nlinarith [hn.2]))

theorem exponential_error_tendsto_zero (κ : ℝ) {γ : ℝ} (hγ : 0 < γ) :
    Tendsto (fun n : ℕ => κ * Real.exp (-γ * (n : ℝ))) atTop (𝓝 0) := by
  simpa using (nat_rpow_mul_stretched_exp_tendsto 0 (by norm_num : (0 : ℝ) < 1) hγ).const_mul κ

theorem exists_channel_uniform_approximation (Φ Ψ : FiniteCPTP I O) [Nonempty I]
    {a : ℝ} (ha : regularizedRelativeEntropyBits Φ Ψ < (a : EReal)) :
    ∃ Λ : (n : ℕ) → Matrix (TensorIndex I n) (TensorIndex I n) ℂ →ₗ[ℂ]
      Matrix (TensorIndex O n) (TensorIndex O n) ℂ,
      (∀ n, CPTPKraus.CompletelyPositive (Λ n) ∧ CPTPKraus.TraceNonincreasing (Λ n)) ∧
      ∃ κ γ : ℝ, 0 < κ ∧ 0 < γ ∧ ∀ᶠ n : ℕ in atTop,
        CPTPKraus.CPDom (Λ n) (channelPower Ψ n).map ((2 : ℝ) ^ ((n : ℝ) * a)) ∧
          DiamondControl.diamondBudget ((channelPower Φ n).map - Λ n) ≤
            ((κ * Real.exp (-γ * (n : ℝ)) : ℝ) : EReal) := by
  have htop : regularizedRelativeEntropyBits Φ Ψ ≠ ⊤ := ne_top_of_lt ha
  have hreal := EReal.coe_toReal htop (regularizedRelativeEntropyBits_ne_bot Φ Ψ)
  have hrate : (regularizedRelativeEntropyBits Φ Ψ).toReal < a := by
    apply EReal.coe_lt_coe_iff.mp
    rwa [hreal]
  exact exists_exponential_channel_family Φ Ψ (CPTPKraus.canonicalKraus Φ.map)
    (CPTPKraus.canonicalKraus Ψ.map)
    (CPTPKraus.canonicalKraus_reconstruct_map Φ.map Φ.completelyPositive).symm
    (CPTPKraus.canonicalKraus_reconstruct_map Ψ.map Ψ.completelyPositive).symm
    hreal.symm.le hrate

theorem exists_channel_uniform_approximation_tendsto (Φ Ψ : FiniteCPTP I O) [Nonempty I]
    {a : ℝ} (ha : regularizedRelativeEntropyBits Φ Ψ < (a : EReal)) :
    ∃ Λ : (n : ℕ) → Matrix (TensorIndex I n) (TensorIndex I n) ℂ →ₗ[ℂ]
      Matrix (TensorIndex O n) (TensorIndex O n) ℂ,
      ∃ errors : ℕ → ℝ, (∀ n, 0 ≤ errors n) ∧ Tendsto errors atTop (𝓝 0) ∧
        (∀ n, CPTPKraus.CompletelyPositive (Λ n) ∧ CPTPKraus.TraceNonincreasing (Λ n)) ∧
        ∀ᶠ n : ℕ in atTop,
          CPTPKraus.CPDom (Λ n) (channelPower Ψ n).map ((2 : ℝ) ^ ((n : ℝ) * a)) ∧
            DiamondControl.diamondBudget ((channelPower Φ n).map - Λ n) ≤ ((errors n : ℝ) : EReal) := by
  obtain ⟨Λ, hΛ, κ, γ, hκ, hγ, hbound⟩ := exists_channel_uniform_approximation Φ Ψ ha
  exact ⟨Λ, (fun n => κ * Real.exp (-γ * (n : ℝ))), (fun n => by positivity),
    exponential_error_tendsto_zero κ hγ, hΛ, hbound⟩

end QuantumProver.SuperchannelDiscrimination.ChannelUniformFactory

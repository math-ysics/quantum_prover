import QuantumProver.InformationTheory.SuperchannelDiscrimination.TestingConsequences
import QuantumProver.InformationTheory.SuperchannelDiscrimination.DiamondControl

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace QuantumProver.QuantumSteinStrongConverse

open Matrix Filter
open QuantumProver.SuperchannelDiscrimination
open FlaggedStates TensorPinching TensorEntropy
open scoped BigOperators Topology ComplexOrder MatrixOrder Matrix Kronecker

variable {I : Type*} [Fintype I] [DecidableEq I]

def statePowerIndex (A : Type*) : (n : ℕ) → RecursiveRows A n ≃ TensorIndex A n
  | 0 => Equiv.refl PUnit
  | n + 1 => Equiv.prodCongr (statePowerIndex A n) (Equiv.refl A)

theorem matrix_tensorPower_transport (X : Matrix I I ℂ) (n : ℕ) :
    Matrix.reindex (statePowerIndex I n) (statePowerIndex I n) (recursiveTensorPower X n) =
      TensorEntropy.tensorPower X n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change Matrix.reindex (statePowerIndex I n) (statePowerIndex I n)
          (recursiveTensorPower X n) ⊗ₖ X = TensorEntropy.tensorPower X n ⊗ₖ X
      rw [ih]

theorem trace_reindex {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (e : A ≃ B) (X : Matrix A A ℂ) :
    (Matrix.reindex e e X).trace = X.trace :=
  e.symm.sum_comp (fun x => X x x)

theorem traceNorm_reindex {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (e : A ≃ B) (X : Matrix A A ℂ) :
    EffectPerturbation.traceNorm (Matrix.reindex e e X) = EffectPerturbation.traceNorm X :=
  DiamondControl.nuclearNorm_submatrix_equiv e.symm X

theorem dyadic_nats_cap (n : ℕ) (a : ℝ) :
    (2 : ℝ) ^ ((n : ℝ) * (a / Real.log 2)) = Real.exp ((n : ℝ) * a) := by
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  congr 1
  field_simp [ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 2))] <;> ring

theorem normalized_state_smoothing_nats {ρ σ : Matrix I I ℂ}
    (hρ : IsDensity ρ) (hσ : IsDensity σ) (hσpd : σ.PosDef)
    {a : ℝ} (ha : PetzMoments.relativeEntropyNats ρ σ < a) :
    ∃ ν : (n : ℕ) → Matrix (TensorIndex I n) (TensorIndex I n) ℂ,
      (∀ n, IsDensity (ν n)) ∧
      Tendsto (fun n => EffectPerturbation.traceNorm (TensorEntropy.tensorPower ρ n - ν n))
        atTop (𝓝 0) ∧
      ∀ᶠ n : ℕ in atTop,
        (Real.exp ((n : ℝ) * a) • TensorEntropy.tensorPower σ n - ν n).PosSemidef := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hb : relativeEntropyBits ρ σ < ((a / Real.log 2 : ℝ) : EReal) := by
    rw [PetzMoments.relativeEntropyBits_eq_nats_of_posDef hσpd]
    exact EReal.coe_lt_coe_iff.mpr ((div_lt_div_iff_of_pos_right hl).mpr ha)
  obtain ⟨ν₀, hν₀, ht, hcap⟩ :=
    Corollaries.normalized_state_smoothing hρ hσ (a / Real.log 2) hb
  let ν := fun n => Matrix.reindex (statePowerIndex I n) (statePowerIndex I n) (ν₀ n)
  have hnorm (n : ℕ) :
      EffectPerturbation.traceNorm (TensorEntropy.tensorPower ρ n - ν n) =
        EffectPerturbation.traceNorm (recursiveTensorPower ρ n - ν₀ n) := by
    rw [← matrix_tensorPower_transport]
    change EffectPerturbation.traceNorm
      (Matrix.reindex (statePowerIndex I n) (statePowerIndex I n)
        (recursiveTensorPower ρ n - ν₀ n)) = _
    exact traceNorm_reindex _ _
  refine ⟨ν, (fun n => ⟨(hν₀ n).1.submatrix (statePowerIndex I n).symm, ?_⟩), ?_, ?_⟩
  · exact (trace_reindex (statePowerIndex I n) (ν₀ n)).trans (hν₀ n).2
  · simpa only [hnorm] using ht
  · filter_upwards [hcap] with n hn
    have h := hn.submatrix (statePowerIndex I n).symm
    change (((2 : ℝ) ^ ((n : ℝ) * (a / Real.log 2))) •
      Matrix.reindex (statePowerIndex I n) (statePowerIndex I n)
        (recursiveTensorPower σ n) - ν n).PosSemidef at h
    rwa [matrix_tensorPower_transport, dyadic_nats_cap] at h

theorem acceptance_le_traceNorm_add_order {ρ ν σ T : Matrix I I ℂ} {c : ℝ}
    (hρ : ρ.IsHermitian) (hν : ν.IsHermitian) (hT : IsEffect T)
    (hcap : (c • σ - ν).PosSemidef) :
    acceptanceProbability ρ T ≤ EffectPerturbation.traceNorm (ρ - ν) +
      c * acceptanceProbability σ T := by
  have hd := EffectPerturbation.acceptanceDifference_abs_le_traceNorm hT hρ hν
  have hc := trace_mul_re_nonneg hcap hT.1
  have hp : acceptanceProbability ν T ≤ c * acceptanceProbability σ T := by
    change 0 ≤ ((c • σ - ν) * T).trace.re at hc
    simp only [Matrix.sub_mul, Matrix.smul_mul, Matrix.trace_sub, Matrix.trace_smul,
      Complex.sub_re, Complex.smul_re, smul_eq_mul] at hc
    unfold acceptanceProbability
    linarith
  have ha := le_abs_self (acceptanceProbability ρ T - acceptanceProbability ν T)
  linarith

theorem exponential_rate_gap_tendsto_zero {a r : ℝ} (har : a < r) :
    Tendsto (fun n : ℕ => Real.exp ((n : ℝ) * (a - r))) atTop (𝓝 0) := by
  exact Real.tendsto_exp_atBot.comp
    (Filter.Tendsto.atTop_mul_const_of_neg (sub_neg.mpr har)
      (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop))

theorem exists_uniform_acceptance_envelope {ρ σ : Matrix I I ℂ}
    (hρ : IsDensity ρ) (hσ : IsDensity σ) (hσpd : σ.PosDef)
    {r : ℝ} (hr : PetzMoments.relativeEntropyNats ρ σ < r) :
    ∃ ε : ℕ → ℝ, (∀ n, 0 ≤ ε n) ∧ Tendsto ε atTop (𝓝 0) ∧
      ∀ᶠ n : ℕ in atTop, ∀ T : Matrix (TensorIndex I n) (TensorIndex I n) ℂ,
        IsEffect T → acceptanceProbability (TensorEntropy.tensorPower σ n) T ≤
          Real.exp (-(n : ℝ) * r) →
        acceptanceProbability (TensorEntropy.tensorPower ρ n) T ≤ ε n := by
  let a := (PetzMoments.relativeEntropyNats ρ σ + r) / 2
  have hDa : PetzMoments.relativeEntropyNats ρ σ < a := by dsimp [a]; linarith
  have har : a < r := by dsimp [a]; linarith
  obtain ⟨ν, hν, ht, hcap⟩ := normalized_state_smoothing_nats hρ hσ hσpd hDa
  let ε := fun n => EffectPerturbation.traceNorm (TensorEntropy.tensorPower ρ n - ν n) +
    Real.exp ((n : ℝ) * (a - r))
  refine ⟨ε, (fun n => add_nonneg (DiamondControl.nuclearNorm_nonneg _)
    (Real.exp_nonneg _)), ?_, ?_⟩
  · simpa only [add_zero] using ht.add (exponential_rate_gap_tendsto_zero har)
  · filter_upwards [hcap] with n hn
    intro T hT hβ
    have h := acceptance_le_traceNorm_add_order
      (TensorEntropy.tensorPower_isDensity hρ n).1.1 (hν n).1.1 hT hn
    calc
      acceptanceProbability (TensorEntropy.tensorPower ρ n) T ≤
          EffectPerturbation.traceNorm (TensorEntropy.tensorPower ρ n - ν n) +
            Real.exp ((n : ℝ) * a) * acceptanceProbability (TensorEntropy.tensorPower σ n) T := h
      _ ≤ EffectPerturbation.traceNorm (TensorEntropy.tensorPower ρ n - ν n) +
            Real.exp ((n : ℝ) * a) * Real.exp (-(n : ℝ) * r) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hβ (Real.exp_nonneg _))
      _ = ε n := by
        rw [← Real.exp_add]
        dsimp [ε]
        congr 2
        ring

theorem iid_strong_converse_nats {ρ σ : Matrix I I ℂ}
    (hρ : IsDensity ρ) (hσ : IsDensity σ) (hσpd : σ.PosDef)
    {r : ℝ} (hr : PetzMoments.relativeEntropyNats ρ σ < r)
    (T : (n : ℕ) → Matrix (TensorIndex I n) (TensorIndex I n) ℂ)
    (hT : ∀ n, IsEffect (T n))
    (hβ : ∀ᶠ n : ℕ in atTop,
      acceptanceProbability (TensorEntropy.tensorPower σ n) (T n) ≤ Real.exp (-(n : ℝ) * r)) :
    Tendsto (fun n => acceptanceProbability (TensorEntropy.tensorPower ρ n) (T n))
      atTop (𝓝 0) := by
  obtain ⟨ε, hε, ht, hbound⟩ := exists_uniform_acceptance_envelope hρ hσ hσpd hr
  apply squeeze_zero' (Eventually.of_forall (fun n =>
    trace_mul_re_nonneg (TensorEntropy.tensorPower_isDensity hρ n).1 (hT n).1)) _ ht
  filter_upwards [hbound, hβ] with n hn hβn
  exact hn (T n) (hT n) hβn

theorem iid_typeI_error_tendsto_one_nats {ρ σ : Matrix I I ℂ}
    (hρ : IsDensity ρ) (hσ : IsDensity σ) (hσpd : σ.PosDef)
    {r : ℝ} (hr : PetzMoments.relativeEntropyNats ρ σ < r)
    (T : (n : ℕ) → Matrix (TensorIndex I n) (TensorIndex I n) ℂ)
    (hT : ∀ n, IsEffect (T n))
    (hβ : ∀ᶠ n : ℕ in atTop,
      acceptanceProbability (TensorEntropy.tensorPower σ n) (T n) ≤ Real.exp (-(n : ℝ) * r)) :
    Tendsto (fun n => 1 - acceptanceProbability (TensorEntropy.tensorPower ρ n) (T n))
      atTop (𝓝 1) := by
  simpa only [sub_zero] using
    ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub
      (iid_strong_converse_nats hρ hσ hσpd hr T hT hβ))

end QuantumProver.QuantumSteinStrongConverse

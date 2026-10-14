import QuantumProver.InformationTheory.AmplitudeDamping.SecretKey.OutputContinuity
import QuantumProver.InformationTheory.AmplitudeDamping.SecretKey.WeakBinaryConjugate

set_option autoImplicit false
noncomputable section

namespace QuantumProver.AmplitudeDamping.SecretKey.MatrixWeakOutputClosure

open WeakBinaryConjugate OutputContinuity MatrixTraceNorm

def weakTestLowerBound (d : ℕ) (x : ℝ) : ℝ := sSup (testValues d x)

theorem weakTestLowerBound_eq_literal (d : ℕ) (x : ℝ) :
    weakTestLowerBound d x =
      sSup {y : ℝ | ∃ s : ℝ, 0 ≤ s ∧
        y = s * x - log2 (1 + ((2 : ℝ) ^ s - 1) / (d : ℝ))} := rfl

theorem testValues_bddAbove_of_pos {d : ℕ} (hd : 0 < d)
    {x : ℝ} (hx : x ≤ 1) : BddAbove (testValues d x) := by
  by_cases hd1 : d = 1
  · subst d
    refine ⟨0, ?_⟩
    rintro y ⟨s, hs, rfl⟩
    have hlog : log2 ((2 : ℝ) ^ s) = s := by
      unfold log2
      rw [Real.log_rpow (by norm_num : 0 < (2 : ℝ))]
      exact mul_div_cancel_right₀ s (Real.log_pos (by norm_num : 1 < (2 : ℝ))).ne'
    have hnorm : 1 + ((2 : ℝ) ^ s - 1) / (1 : ℝ) = (2 : ℝ) ^ s := by ring
    unfold testValue
    simp only [Nat.cast_one]
    rw [hnorm, hlog]
    have hmul : s * x ≤ s := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hx hs
    linarith
  · exact testValues_bddAbove (by omega) hx

theorem testValue_le_weakTestLowerBound {d : ℕ} (hd : 0 < d)
    {x s : ℝ} (hx : x ≤ 1) (hs : 0 ≤ s) :
    testValue d x s ≤ weakTestLowerBound d x :=
  le_csSup (testValues_bddAbove_of_pos hd hx) ⟨s, hs, rfl⟩

variable {E : Type*} [Fintype E] [DecidableEq E]

theorem weakTestLowerBound_le_of_operationalApproximation {d : ℕ} (hd : 0 < d)
    (S : Set (Density ((Fin d × Fin d) × E))) {B : ℝ}
    (hfinite : ∀ τ ∈ S, weakTestLowerBound d
      (optimalWholeKeySquaredFidelity d hd τ) ≤ B)
    (ρ : Density ((Fin d × Fin d) × E))
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ τ ∈ S, traceNorm (ρ.mat - τ.mat) < ε) :
    weakTestLowerBound d (optimalWholeKeySquaredFidelity d hd ρ) ≤ B := by
  apply csSup_le (testValues_nonempty d _)
  rintro v ⟨s, hs, rfl⟩
  by_cases hs0 : s = 0
  · obtain ⟨τ, hτ, _⟩ := happrox 1 (by norm_num)
    have ht := (testValue_le_weakTestLowerBound hd
      (optimalWholeKeySquaredFidelity_mem_Icc d hd τ).2 hs).trans (hfinite τ hτ)
    simpa only [hs0, testValue_zero_parameter] using ht
  · have hsp : 0 < s := lt_of_le_of_ne hs (Ne.symm hs0)
    have hG : optimalWholeKeySquaredFidelity d hd ρ ≤
        (B + log2 (1 + ((2 : ℝ) ^ s - 1) / (d : ℝ))) / s := by
      apply keyG_le_of_operationalApproximation hd S _ ρ happrox
      intro τ hτ
      have ht := (testValue_le_weakTestLowerBound hd
        (optimalWholeKeySquaredFidelity_mem_Icc d hd τ).2 hs).trans (hfinite τ hτ)
      apply (le_div_iff₀ hsp).mpr
      unfold testValue at ht
      linarith
    have hmul := (le_div_iff₀ hsp).mp hG
    unfold testValue
    linarith

theorem weak_bound_on_operationalOutputs {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (m d : ℕ) (hd : 0 < d) (k B : ℝ)
    (hfinite : ∀ C : FiniteSeedKeyCode p m d k, weakTestLowerBound d
      (optimalWholeKeySquaredFidelity d hd (C.output hp0 hp1)) ≤ B)
    (ρ : Density ((Fin d × Fin d) × E))
    (hρ : ρ ∈ operationalSeedKeyOutputs hp0 hp1 m d k) :
    weakTestLowerBound d (optimalWholeKeySquaredFidelity d hd ρ) ≤ B := by
  apply weakTestLowerBound_le_of_operationalApproximation hd
    (finiteSeedKeyOutputs hp0 hp1 m d k) _ ρ hρ
  rintro τ ⟨C, e, rfl⟩
  rw [keyG_Eve_relabel d hd e]
  exact hfinite C

theorem entropy_bound_on_operationalOutputs {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (m d : ℕ) (hd : 0 < d) (hd2 : 2 ≤ d) (k B : ℝ)
    (hfinite : ∀ C : FiniteSeedKeyCode p m d k, weakTestLowerBound d
      (optimalWholeKeySquaredFidelity d hd (C.output hp0 hp1)) ≤ B)
    (ρ : Density ((Fin d × Fin d) × E))
    (hρ : ρ ∈ operationalSeedKeyOutputs hp0 hp1 m d k) :
    optimalWholeKeySquaredFidelity d hd ρ * log2 (d : ℝ) -
      binaryEntropyBits (optimalWholeKeySquaredFidelity d hd ρ) ≤ B := by
  have hG := optimalWholeKeySquaredFidelity_mem_Icc d hd ρ
  have hsoft : optimalWholeKeySquaredFidelity d hd ρ * log2 (d : ℝ) -
      binaryEntropyBits (optimalWholeKeySquaredFidelity d hd ρ) ≤
      weakTestLowerBound d (optimalWholeKeySquaredFidelity d hd ρ) :=
    weak_binary_entropy_bound hd2 hG.1 hG.2
  exact hsoft.trans (weak_bound_on_operationalOutputs hp0 hp1 m d hd k B hfinite ρ hρ)

end QuantumProver.AmplitudeDamping.SecretKey.MatrixWeakOutputClosure

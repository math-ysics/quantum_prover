import QuantumProver.InformationTheory.AmplitudeDamping.SecretKey.FiniteAdaptiveConverse
import QuantumProver.InformationTheory.AmplitudeDamping.SecretKey.ProtocolIdentities
import QuantumProver.InformationTheory.AmplitudeDamping.SecretKey.KeyErrorConversion

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section
open Matrix Kronecker Filter
open scoped Topology BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace QuantumProver.AmplitudeDamping.SecretKey.FiniteAdaptiveErrorConverse

open OutputContinuity

section NuclearEntries

variable {I : Type*} [Fintype I] [DecidableEq I]

private theorem trace_real_eq_sum_eigenvalues {X : Matrix I I ℂ} (hX : X.PosSemidef) :
    X.trace.re = ∑ i, hX.1.eigenvalues i := by
  simpa only [Complex.re_sum, RCLike.ofReal_eq_complex_ofReal, Complex.ofReal_re] using
    congrArg Complex.re hX.1.trace_eq_sum_eigenvalues

private theorem matrix_norm_le_trace_real_of_posSemidef {X : Matrix I I ℂ}
    (hX : X.PosSemidef) : ‖X‖ ≤ X.trace.re := by
  have ht : 0 ≤ X.trace.re := (Complex.nonneg_iff.mp hX.trace_nonneg).1
  have hn : ‖cfc (id : ℝ → ℝ) X‖ ≤ X.trace.re := by
    apply norm_cfc_le ht
    intro x hx
    obtain ⟨i, rfl⟩ := hX.1.spectrum_real_eq_range_eigenvalues ▸ hx
    rw [id_eq, Real.norm_eq_abs, abs_of_nonneg (hX.eigenvalues_nonneg i),
      trace_real_eq_sum_eigenvalues hX]
    exact Finset.single_le_sum (fun j _ => hX.eigenvalues_nonneg j) (Finset.mem_univ i)
  simpa only [cfc_id ℝ X hX.1.isSelfAdjoint] using hn

theorem matrix_norm_le_traceNorm (X : Matrix I I ℂ) : ‖X‖ ≤ traceNorm X := by
  simpa only [CFC.norm_abs, QuantumProver.AmplitudeDamping.SecretKey.traceNorm] using
    matrix_norm_le_trace_real_of_posSemidef (CFC.abs_nonneg X).posSemidef

theorem norm_entry_le_traceNorm (X : Matrix I I ℂ) (i j : I) :
    ‖X i j‖ ≤ traceNorm X := by
  let v : EuclideanSpace ℂ I := PiLp.single 2 j 1
  let w : EuclideanSpace ℂ I := (EuclideanSpace.equiv I ℂ).symm (X *ᵥ v)
  have hw : w i = X i j := by
    simp [w, v]
  have he := PiLp.norm_apply_le w i
  rw [hw] at he
  have hn := Matrix.l2_opNorm_mulVec X v
  change ‖w‖ ≤ ‖X‖ * ‖v‖ at hn
  have hv : ‖v‖ = 1 := by simp [v]
  rw [hv, mul_one] at hn
  exact (he.trans hn).trans (matrix_norm_le_traceNorm X)

end NuclearEntries

section ActualClassicalOutputs

variable {p k : ℝ} {m d : ℕ} {E F : Type*}
  [Fintype E] [Fintype F] [DecidableEq E] [DecidableEq F]

theorem isCCQ_relabel_Eve (e : F ≃ E)
    (ρ : Density ((Fin d × Fin d) × E)) (hρ : IsCCQ ρ) :
    IsCCQ (ρ.relabel ((Equiv.refl (Fin d × Fin d)).prodCongr e)) := by
  intro x y f f' hxy
  exact hρ x y (e f) (e f') hxy

theorem code_output_isCCQ (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (C : FiniteSeedKeyCode p m d k) : IsCCQ (C.output hp0 hp1) := by
  classical
  exact SemanticVerification.finalKeyStateWithPriorEveLabels_isCCQ hp0 hp1
    C.protocol C.labelA C.labelB (Fin C.priorEveSize) C.initialDensity

theorem finiteSeedKeyOutputs_isCCQ (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (ρ : Density ((Fin d × Fin d) × E))
    (hρ : ρ ∈ finiteSeedKeyOutputs hp0 hp1 m d k) : IsCCQ ρ := by
  classical
  rcases hρ with ⟨C, e, rfl⟩
  exact isCCQ_relabel_Eve e _ (code_output_isCCQ hp0 hp1 C)

theorem operationalSeedKeyOutputs_isCCQ (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (ρ : Density ((Fin d × Fin d) × E))
    (hρ : ρ ∈ operationalSeedKeyOutputs hp0 hp1 m d k) : IsCCQ ρ := by
  intro x y e e' hxy
  apply norm_eq_zero.mp
  apply le_antisymm ?_ (norm_nonneg _)
  apply le_of_forall_pos_le_add
  intro ε hε
  rcases hρ ε hε with ⟨τ, hτ, hdist⟩
  have ht := finiteSeedKeyOutputs_isCCQ hp0 hp1 τ hτ x y e e' hxy
  have hEntry := norm_entry_le_traceNorm (ρ.mat - τ.mat) (x, e) (y, e')
  rw [Matrix.sub_apply, ht, sub_zero] at hEntry
  simpa only [zero_add] using hEntry.trans hdist.le

end ActualClassicalOutputs

section HalfExponent

theorem sqrt_min_one_two_rpow (r : ℝ) :
    Real.sqrt (min 1 ((2 : ℝ) ^ r)) = min 1 ((2 : ℝ) ^ (r / 2)) := by
  have hroot : Real.sqrt ((2 : ℝ) ^ r) = (2 : ℝ) ^ (r / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    ring
  by_cases h : (2 : ℝ) ^ r ≤ 1
  · have hhalf : (2 : ℝ) ^ (r / 2) ≤ 1 := by
      rw [← hroot]
      simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt h
    rw [min_eq_right h, hroot, min_eq_right hhalf]
  · have h1 : 1 ≤ (2 : ℝ) ^ r := (lt_of_not_ge h).le
    have hhalf : 1 ≤ (2 : ℝ) ^ (r / 2) := by
      rw [← hroot]
      simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt h1
    rw [min_eq_left h1, Real.sqrt_one, min_eq_left hhalf]

theorem sqrt_min_strongExponentBound (p z k : ℝ) (m d : ℕ) :
    Real.sqrt (min 1 (strongExponentBound p z k m d)) =
      min 1 ((2 : ℝ) ^ (-(z / 2) * (log2 (d : ℝ) - k - (m : ℝ) * channelBz p z))) := by
  unfold strongExponentBound
  rw [sqrt_min_one_two_rpow]
  congr 2
  ring

end HalfExponent

section PhysicalErrorConverse

open KeyErrorConversion

variable {p k z : ℝ} {m d : ℕ}

theorem code_error_strong_converse
    (hp0 : 0 < p) (hp1 : p < 1) (C : FiniteSeedKeyCode p m d k)
    (hd : 0 < d) (hz0 : 0 < z) (hz1 : z < 1) :
    1 - min 1 ((2 : ℝ) ^ (-(z / 2) *
      (log2 (d : ℝ) - k - (m : ℝ) * channelBz p z))) ≤
      disagreementError (C.output hp0.le hp1.le) +
        aliceSecrecyError hd (C.output hp0.le hp1.le) := by
  have hG := FiniteAdaptiveConverse.code_keyG_strong_converse hp0 hp1 C hd hz0 hz1
  have hRoot := Real.sqrt_le_sqrt hG
  rw [sqrt_min_strongExponentBound] at hRoot
  have hError := error_ge_one_sub_sqrt_keyG hd (C.output hp0.le hp1.le)
    (code_output_isCCQ hp0.le hp1.le C)
  linarith

theorem code_error_strong_converse_of_error_bounds
    (hp0 : 0 < p) (hp1 : p < 1) (C : FiniteSeedKeyCode p m d k)
    (hd : 0 < d) (hz0 : 0 < z) (hz1 : z < 1) {epsilon delta : ℝ}
    (hCorrect : disagreementError (C.output hp0.le hp1.le) ≤ epsilon)
    (hSecret : aliceSecrecyError hd (C.output hp0.le hp1.le) ≤ delta) :
    1 - min 1 ((2 : ℝ) ^ (-(z / 2) *
      (log2 (d : ℝ) - k - (m : ℝ) * channelBz p z))) ≤ epsilon + delta :=
  (code_error_strong_converse hp0 hp1 C hd hz0 hz1).trans (add_le_add hCorrect hSecret)

variable {E : Type*} [Fintype E] [DecidableEq E]

theorem finiteSeedKeyOutputs_error_strong_converse
    (hp0 : 0 < p) (hp1 : p < 1) (hd : 0 < d) (hz0 : 0 < z) (hz1 : z < 1)
    (ρ : Density ((Fin d × Fin d) × E))
    (hρ : ρ ∈ finiteSeedKeyOutputs hp0.le hp1.le m d k) :
    1 - min 1 ((2 : ℝ) ^ (-(z / 2) *
      (log2 (d : ℝ) - k - (m : ℝ) * channelBz p z))) ≤
      disagreementError ρ + aliceSecrecyError hd ρ := by
  rcases hρ with ⟨C, e, rfl⟩
  rw [disagreementError_Eve_relabel, aliceSecrecyError_Eve_relabel]
  exact code_error_strong_converse hp0 hp1 C hd hz0 hz1

theorem operationalSeedKeyOutputs_error_strong_converse
    (hp0 : 0 < p) (hp1 : p < 1) (hd : 0 < d) (hz0 : 0 < z) (hz1 : z < 1)
    (ρ : Density ((Fin d × Fin d) × E))
    (hρ : ρ ∈ operationalSeedKeyOutputs hp0.le hp1.le m d k) :
    1 - min 1 ((2 : ℝ) ^ (-(z / 2) *
      (log2 (d : ℝ) - k - (m : ℝ) * channelBz p z))) ≤
      disagreementError ρ + aliceSecrecyError hd ρ := by
  have hG := FiniteAdaptiveConverse.strong_bound_on_operationalOutputs
    hp0 hp1 hd hz0 hz1 ρ hρ
  have hRoot := Real.sqrt_le_sqrt hG
  rw [sqrt_min_strongExponentBound] at hRoot
  have hError := error_ge_one_sub_sqrt_keyG hd ρ
    (operationalSeedKeyOutputs_isCCQ hp0.le hp1.le ρ hρ)
  linarith

end PhysicalErrorConverse

end QuantumProver.AmplitudeDamping.SecretKey.FiniteAdaptiveErrorConverse

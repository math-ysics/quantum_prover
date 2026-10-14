import QuantumProver.InformationTheory.DepolarizingSquashedEntanglement.BCYRelativeEntropy
import QuantumProver.InformationTheory.ConditionalEntropy.Main

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

noncomputable section

open Matrix Set Filter
open scoped Topology BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker

namespace QuantumProver.DepolarizingSquashedEntanglement.BCYERContinuity

open BCYRelativeEntropy
open QuantumProver.SuperchannelDiscrimination.FlaggedStates (HasSupportIn)

variable {A B I : Type*} [Fintype A] [Fintype B] [Fintype I]
  [DecidableEq A] [DecidableEq B] [DecidableEq I]

def densityOfMatrix (R : QMatrix I)
    (hR : QuantumProver.ConditionalEntropy.IsDensity R) : Density I := ⟨R, hR.1, hR.2⟩

def mixDensity (p : ℝ) (ρ τ : Density I) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : Density I :=
  densityOfMatrix (QuantumProver.ConditionalEntropy.mix p ρ.matrix τ.matrix)
    (QuantumProver.ConditionalEntropy.mix_isDensity (density_matrix ρ) (density_matrix τ) hp0 hp1)

def binaryEntropyNat (p : ℝ) : ℝ := QuantumProver.ConditionalEntropy.binaryEntropy p * Real.log 2

theorem entropyNat_eq_entropyBits_mul_log (R : QMatrix I) :
    entropyNat R = QuantumProver.QuantumEntropy.entropyBits R * Real.log 2 := by
  rw [entropyNat_eq_shared, QuantumProver.QuantumEntropy.entropyNats_eq_entropyBits_mul_log_two]

theorem entropyNat_le_log_card (ρ : Density I) :
    entropyNat ρ.matrix ≤ Real.log (Fintype.card I : ℝ) := by
  have h := (QuantumProver.ConditionalEntropy.ConditionalRange.entropyBits_bounds (density_matrix ρ)).2
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h' := mul_le_mul_of_nonneg_right h hl.le
  rw [div_mul_cancel₀ _ hl.ne', ← entropyNat_eq_entropyBits_mul_log] at h'
  exact h'

theorem rightMarginal_entropy_excess_le_log_left (ρ : Density (A × B)) :
    entropyNat (rightMarginal ρ).matrix - entropyNat ρ.matrix ≤
      Real.log (Fintype.card A : ℝ) := by
  have h := (QuantumProver.ConditionalEntropy.conditionalEntropy_bounds (density_matrix ρ)).1
  rw [QuantumProver.ConditionalEntropy.conditionalEntropyBits, QuantumProver.ConditionalEntropy.logDimA] at h
  change -(Real.log (Fintype.card A : ℝ) / Real.log 2) ≤
    QuantumProver.QuantumEntropy.entropyBits ρ.matrix -
      QuantumProver.QuantumEntropy.entropyBits (rightMarginal ρ).matrix at h
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hn := mul_le_mul_of_nonneg_right h hl.le
  simp only [neg_mul, div_mul_cancel₀ _ hl.ne', sub_mul,
    ← entropyNat_eq_entropyBits_mul_log] at hn
  linarith

theorem erNat_le_two_log_left (ρ : Density (A × B)) :
    relativeEntropyEntanglementNat ρ ≤ (2 * Real.log (Fintype.card A : ℝ) : ℝ) := by
  refine (relativeEntropyEntanglementNat_le_mutualInformation ρ).trans ?_
  have hA := entropyNat_le_log_card (leftMarginal ρ)
  have hC := rightMarginal_entropy_excess_le_log_left ρ
  exact_mod_cast (show entropyNat (leftMarginal ρ).matrix +
    entropyNat (rightMarginal ρ).matrix - entropyNat ρ.matrix ≤
      2 * Real.log (Fintype.card A : ℝ) by linarith)

theorem erReal_le_two_log_left (ρ : Density (A × B)) :
    relativeEntropyEntanglementReal ρ ≤ 2 * Real.log (Fintype.card A : ℝ) := by
  have h := erNat_le_two_log_left ρ
  rw [← coe_relativeEntropyEntanglementReal] at h
  exact_mod_cast h

theorem card_copyIndex (A : Type*) [Fintype A] (n : ℕ) :
    Fintype.card (CopyIndex A n) = (Fintype.card A) ^ n := by
  induction n with
  | zero => exact Fintype.card_unique
  | succ n ih =>
    change Fintype.card (CopyIndex A n × A) = _
    rw [Fintype.card_prod, ih, pow_succ]

theorem log_card_copyIndex (A : Type*) [Fintype A] (n : ℕ) :
    Real.log (Fintype.card (CopyIndex A n) : ℝ) =
      (n : ℝ) * Real.log (Fintype.card A : ℝ) := by
  rw [card_copyIndex, Nat.cast_pow, Real.log_pow]

def finiteUmegakiNats (R S : QMatrix I) : ℝ :=
  (R * (cfc Real.log R - cfc Real.log S)).trace.re

theorem finiteUmegakiNats_eq_entropy {R : QMatrix I} (hR : R.IsHermitian)
    (S : QMatrix I) :
    finiteUmegakiNats R S = -entropyNat R - (R * cfc Real.log S).trace.re := by
  have h := QuantumProver.QuantumEntropy.entropyNats_eq_neg_trace_mul_log hR
  rw [← entropyNat_eq_shared] at h
  simp only [finiteUmegakiNats, Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re]
  linarith

theorem finiteUmegakiNats_mix_identity (ρ τ : Density I) (S : QMatrix I)
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    finiteUmegakiNats (mixDensity p ρ τ hp0 hp1).matrix S =
      (1-p) * finiteUmegakiNats ρ.matrix S + p * finiteUmegakiNats τ.matrix S +
      (1-p) * entropyNat ρ.matrix + p * entropyNat τ.matrix -
        entropyNat (mixDensity p ρ τ hp0 hp1).matrix := by
  rw [finiteUmegakiNats_eq_entropy (mixDensity p ρ τ hp0 hp1).positive.1,
    finiteUmegakiNats_eq_entropy ρ.positive.1, finiteUmegakiNats_eq_entropy τ.positive.1]
  simp only [mixDensity, densityOfMatrix, QuantumProver.ConditionalEntropy.mix,
    Matrix.add_mul, Matrix.smul_mul, Matrix.trace_add, Matrix.trace_smul,
    Complex.add_re, Complex.smul_re, smul_eq_mul]
  ring

theorem entropyNat_mix_upper (ρ τ : Density I) {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    entropyNat (mixDensity p ρ τ hp0 hp1).matrix ≤
      (1-p) * entropyNat ρ.matrix + p * entropyNat τ.matrix + binaryEntropyNat p := by
  have h := QuantumProver.ConditionalEntropy.entropyBits_mix_upper
    (density_matrix ρ) (density_matrix τ) hp0 hp1
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hn := mul_le_mul_of_nonneg_right h hl.le
  simpa only [add_mul, mul_assoc, ← entropyNat_eq_entropyBits_mul_log,
    binaryEntropyNat, mixDensity, densityOfMatrix] using hn

omit [DecidableEq I] in

theorem support_in_positive_sum {R T : QMatrix I} (hR : R.PosSemidef) (hT : T.PosSemidef)
    {x y : ℝ} (hx : 0 < x) (hy : 0 ≤ y) : HasSupportIn R (x • R + y • T) := by
  intro v hv
  let a : ℂ := star v ⬝ᵥ (x • R) *ᵥ v
  let b : ℂ := star v ⬝ᵥ (y • T) *ᵥ v
  have ha : 0 ≤ a := (hR.smul hx.le).dotProduct_mulVec_nonneg v
  have hb : 0 ≤ b := (hT.smul hy).dotProduct_mulVec_nonneg v
  have hab : a + b = 0 := by
    have hz : star v ⬝ᵥ (x • R + y • T) *ᵥ v = 0 := by rw [hv]; simp
    simpa only [Matrix.add_mulVec, dotProduct_add, a, b] using hz
  have haZero : a = 0 := le_antisymm (hab ▸ le_add_of_nonneg_right hb) ha
  have hScaled : x • (star v ⬝ᵥ R *ᵥ v) = 0 := by
    simpa only [a, Matrix.smul_mulVec, dotProduct_smul] using haZero
  exact hR.dotProduct_mulVec_zero_iff.mp
    ((smul_eq_zero.mp hScaled).resolve_left hx.ne')

theorem erReal_le_finite_of_support (ρ σ : Density (A × B))
    (hσ : IsSeparable σ.matrix) (hs : HasSupportIn ρ.matrix σ.matrix) :
    relativeEntropyEntanglementReal ρ ≤ finiteUmegakiNats ρ.matrix σ.matrix := by
  have h := relativeEntropyEntanglementNat_le ρ σ hσ
  rw [← coe_relativeEntropyEntanglementReal, umegakiNats_of_support _ _ hs] at h
  change (relativeEntropyEntanglementReal ρ : EReal) ≤
    (finiteUmegakiNats ρ.matrix σ.matrix : EReal) at h
  exact_mod_cast h

theorem erReal_mix_approx_affine_lower (ρ τ : Density (A × B)) {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (1-p) * relativeEntropyEntanglementReal ρ + p * relativeEntropyEntanglementReal τ ≤
      relativeEntropyEntanglementReal (mixDensity p ρ τ hp0 hp1) + binaryEntropyNat p := by
  by_cases hz : p = 0
  · subst p
    have hm : mixDensity 0 ρ τ hp0 hp1 = ρ := by
      apply density_ext
      simp [mixDensity, densityOfMatrix, QuantumProver.ConditionalEntropy.mix]
    rw [hm]
    simp [binaryEntropyNat]
  by_cases ho : p = 1
  · subst p
    have hm : mixDensity 1 ρ τ hp0 hp1 = τ := by
      apply density_ext
      simp [mixDensity, densityOfMatrix, QuantumProver.ConditionalEntropy.mix]
    rw [hm]
    simp [binaryEntropyNat]
  have hp : 0 < p := lt_of_le_of_ne hp0 (Ne.symm hz)
  have hq : p < 1 := lt_of_le_of_ne hp1 ho
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨σ, hσ⟩ := exists_separable_near (mixDensity p ρ τ hp0 hp1) hε
  have hsM : HasSupportIn (mixDensity p ρ τ hp0 hp1).matrix σ.val.matrix := by
    by_contra hsM
    have ht := (umegakiNats_eq_top_iff _ _).mpr hsM
    rw [ht] at hσ
    exact not_lt_of_ge le_top hσ
  have hsR : HasSupportIn ρ.matrix (mixDensity p ρ τ hp0 hp1).matrix :=
    support_in_positive_sum ρ.positive τ.positive (sub_pos.mpr hq) hp0
  have hsT : HasSupportIn τ.matrix (mixDensity p ρ τ hp0 hp1).matrix := by
    simpa only [mixDensity, densityOfMatrix, QuantumProver.ConditionalEntropy.mix, add_comm] using
      support_in_positive_sum τ.positive ρ.positive hp (sub_nonneg.mpr hp1)
  have hR := erReal_le_finite_of_support ρ σ.val σ.property
    (fun v hv => hsR v (hsM v hv))
  have hT := erReal_le_finite_of_support τ σ.val σ.property
    (fun v hv => hsT v (hsM v hv))
  rw [umegakiNats_of_support _ _ hsM] at hσ
  change (finiteUmegakiNats (mixDensity p ρ τ hp0 hp1).matrix σ.val.matrix : EReal) <
    ((relativeEntropyEntanglementReal (mixDensity p ρ τ hp0 hp1) + ε : ℝ) : EReal) at hσ
  have hNear : finiteUmegakiNats (mixDensity p ρ τ hp0 hp1).matrix σ.val.matrix <
      relativeEntropyEntanglementReal (mixDensity p ρ τ hp0 hp1) + ε := by exact_mod_cast hσ
  have hWeighted := add_le_add
    (mul_le_mul_of_nonneg_left hR (sub_nonneg.mpr hp1))
    (mul_le_mul_of_nonneg_left hT hp0)
  have hIdentity := finiteUmegakiNats_mix_identity ρ τ σ.val.matrix hp0 hp1
  have hEntropy := entropyNat_mix_upper ρ τ hp0 hp1
  linarith

open QuantumProver.SuperchannelDiscrimination.TensorEntropy
open QuantumProver.SuperchannelDiscrimination.FlaggedStates (flagBlock)

theorem cfc_log_positive_smul {S : QMatrix I} (hS : S.IsHermitian)
    {c : ℝ} (hc : 0 < c) :
    cfc Real.log (c • S) = Real.log c • supportProjection S + cfc Real.log S := by
  have hf : (fun x : ℝ => Real.log (c*x)) =
      (fun x : ℝ => Real.log c * nonzeroWeight x + Real.log x) := by
    funext x
    by_cases hx : x = 0
    · simp [hx, nonzeroWeight]
    · simp only [nonzeroWeight, ite_eq_right hx, mul_one]
      exact Real.log_mul hc.ne' hx
  rw [← cfc_comp_const_mul (p := IsSelfAdjoint) c Real.log S
    ((S.finite_real_spectrum.image _).continuousOn _) hS, hf,
    cfc_add S _ _ (S.finite_real_spectrum.continuousOn _)
      (S.finite_real_spectrum.continuousOn _),
    cfc_const_mul _ _ S (S.finite_real_spectrum.continuousOn _)]
  rfl

omit [DecidableEq I] in
theorem support_positive_smul {R S : QMatrix I} (hs : HasSupportIn R S)
    {c : ℝ} (hc : 0 < c) : HasSupportIn (c • R) (c • S) := by
  intro v hv
  have hvS : S *ᵥ v = 0 := by
    rw [Matrix.smul_mulVec] at hv
    exact (smul_eq_zero.mp hv).resolve_left hc.ne'
  rw [Matrix.smul_mulVec, hs v hvS, smul_zero]

theorem finiteUmegakiNats_positive_smul {R S : QMatrix I}
    (hR : R.IsHermitian) (hS : S.IsHermitian) (hs : HasSupportIn R S)
    {c : ℝ} (hc : 0 < c) :
    finiteUmegakiNats (c • R) (c • S) = c * finiteUmegakiNats R S := by
  have hRR := supportProjection_mul R hR
  have hRS := (hasSupportIn_iff_mul_supportProjection hS).mp hs
  have hd : R * (cfc Real.log (c • R) - cfc Real.log (c • S)) =
      R * (cfc Real.log R - cfc Real.log S) := by
    rw [cfc_log_positive_smul hR hc, cfc_log_positive_smul hS hc]
    simp only [Matrix.mul_sub, Matrix.mul_add, Matrix.mul_smul, hRR, hRS]
    abel
  unfold finiteUmegakiNats
  rw [Matrix.smul_mul, hd, Matrix.trace_smul, Complex.smul_re, smul_eq_mul]

theorem finiteUmegakiNats_eq_finiteBits (R S : QMatrix I) :
    finiteUmegakiNats R S =
      QuantumProver.SuperchannelDiscrimination.FlaggedStates.finiteRelativeEntropyBits R S * Real.log 2 := by
  simp only [finiteUmegakiNats,
    QuantumProver.SuperchannelDiscrimination.FlaggedStates.finiteRelativeEntropyBits,
    div_mul_cancel₀ _ (ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 2)))]

theorem finiteUmegakiNats_flagBlock {R S T U : QMatrix I}
    (hR : R.IsHermitian) (hS : S.IsHermitian) (hT : T.IsHermitian) (hU : U.IsHermitian) :
    finiteUmegakiNats (flagBlock R T) (flagBlock S U) =
      finiteUmegakiNats R S + finiteUmegakiNats T U := by
  simp only [finiteUmegakiNats_eq_finiteBits,
    QuantumProver.SuperchannelDiscrimination.FlaggedStates.finiteRelativeEntropyBits_flagBlock_of_hermitian
      hR hS hT hU, add_mul]

theorem umegakiNats_mix_le (ρ τ σ ω : Density I)
    (hs : HasSupportIn ρ.matrix σ.matrix) (ht : HasSupportIn τ.matrix ω.matrix)
    {p : ℝ} (hp : 0 < p) (hq : p < 1) :
    umegakiNats (mixDensity p ρ τ hp.le hq.le).matrix
      (mixDensity p σ ω hp.le hq.le).matrix ≤
      (((1-p) * finiteUmegakiNats ρ.matrix σ.matrix +
        p * finiteUmegakiNats τ.matrix ω.matrix : ℝ) : EReal) := by
  let F := QuantumProver.ConditionalEntropy.MixtureEntropy.binaryFlagged (I := I)
  have hFR := QuantumProver.ConditionalEntropy.MixtureEntropy.binaryFlagged_posSemidef
    hp.le hq.le ρ.positive τ.positive
  have hFS := QuantumProver.ConditionalEntropy.MixtureEntropy.binaryFlagged_posSemidef
    hp.le hq.le σ.positive ω.positive
  have hD := QuantumProver.SuperchannelDiscrimination.InputSupport.relativeEntropyBits_kraus_dpi
    (QuantumProver.QuantumEntropy.rightTraceKraus (I := I) (J := Bool))
    QuantumProver.QuantumEntropy.rightTraceKraus_complete hFR hFS
  rw [QuantumProver.QuantumEntropy.rightTraceKraus_action,
    QuantumProver.QuantumEntropy.rightTraceKraus_action] at hD
  change QuantumProver.SuperchannelDiscrimination.FlaggedStates.relativeEntropyBits
      ((fun i j => ∑ b : Bool, F p ρ.matrix τ.matrix (i,b) (j,b)))
      ((fun i j => ∑ b : Bool, F p σ.matrix ω.matrix (i,b) (j,b))) ≤ _ at hD
  rw [QuantumProver.ConditionalEntropy.MixtureEntropy.binaryFlagged_quantumMarginal,
    QuantumProver.ConditionalEntropy.MixtureEntropy.binaryFlagged_quantumMarginal] at hD
  have hNat := mul_le_mul_of_nonneg_right hD
    (EReal.coe_nonneg.mpr (le_of_lt (Real.log_pos (by norm_num : (1 : ℝ) < 2))))
  change umegakiNats (mixDensity p ρ τ hp.le hq.le).matrix
      (mixDensity p σ ω hp.le hq.le).matrix ≤
    umegakiNats (F p ρ.matrix τ.matrix) (F p σ.matrix ω.matrix) at hNat
  have hsFlag := (QuantumProver.SuperchannelDiscrimination.FlaggedStates.hasSupportIn_flagBlock_iff
    ((1-p) • ρ.matrix) ((1-p) • σ.matrix) (p • τ.matrix) (p • ω.matrix)).mpr
      ⟨support_positive_smul hs (sub_pos.mpr hq), support_positive_smul ht hp⟩
  have hFlagR := QuantumProver.SuperchannelDiscrimination.FlaggedStates.flagBlock_posSemidef
    (ρ.positive.smul (sub_nonneg.mpr hq.le)) (τ.positive.smul hp.le)
  have hFlagS := QuantumProver.SuperchannelDiscrimination.FlaggedStates.flagBlock_posSemidef
    (σ.positive.smul (sub_nonneg.mpr hq.le)) (ω.positive.smul hp.le)
  change _ ≤ umegakiNats
    (Matrix.reindex (QuantumProver.ConditionalEntropy.MixtureEntropy.flagEquiv I)
      (QuantumProver.ConditionalEntropy.MixtureEntropy.flagEquiv I)
      (flagBlock ((1-p) • ρ.matrix) (p • τ.matrix)))
    (Matrix.reindex (QuantumProver.ConditionalEntropy.MixtureEntropy.flagEquiv I)
      (QuantumProver.ConditionalEntropy.MixtureEntropy.flagEquiv I)
      (flagBlock ((1-p) • σ.matrix) (p • ω.matrix))) at hNat
  rw [umegakiNats_reindex _ hFlagR hFlagS, umegakiNats_of_support _ _ hsFlag] at hNat
  change _ ≤ (finiteUmegakiNats _ _ : EReal) at hNat
  rw [finiteUmegakiNats_flagBlock (ρ.positive.smul (sub_nonneg.mpr hq.le)).1
    (σ.positive.smul (sub_nonneg.mpr hq.le)).1
    (τ.positive.smul hp.le).1 (ω.positive.smul hp.le).1] at hNat
  rw [finiteUmegakiNats_positive_smul ρ.positive.1 σ.positive.1 hs (sub_pos.mpr hq),
    finiteUmegakiNats_positive_smul τ.positive.1 ω.positive.1 ht hp] at hNat
  exact hNat

theorem exists_separable_near_finite (ρ : Density (A × B)) {ε : ℝ} (hε : 0 < ε) :
    ∃ σ : SeparableDensity A B, HasSupportIn ρ.matrix σ.val.matrix ∧
      finiteUmegakiNats ρ.matrix σ.val.matrix < relativeEntropyEntanglementReal ρ + ε := by
  obtain ⟨σ, hσ⟩ := exists_separable_near ρ hε
  have hs : HasSupportIn ρ.matrix σ.val.matrix := by
    by_contra hs
    rw [(umegakiNats_eq_top_iff _ _).mpr hs] at hσ
    exact not_lt_of_ge le_top hσ
  refine ⟨σ, hs, ?_⟩
  rw [umegakiNats_of_support _ _ hs] at hσ
  exact_mod_cast hσ

theorem mixDensity_separable (σ ω : Density (A × B))
    (hσ : IsSeparable σ.matrix) (hω : IsSeparable ω.matrix)
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    IsSeparable (mixDensity p σ ω hp0 hp1).matrix :=
  (convex_convexHull ℝ _) hσ hω (sub_nonneg.mpr hp1) hp0 (by ring)

theorem erReal_mix_convex (ρ τ : Density (A × B)) {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    relativeEntropyEntanglementReal (mixDensity p ρ τ hp0 hp1) ≤
      (1-p) * relativeEntropyEntanglementReal ρ + p * relativeEntropyEntanglementReal τ := by
  by_cases hz : p = 0
  · subst p
    have hm : mixDensity 0 ρ τ hp0 hp1 = ρ := by
      apply density_ext
      simp [mixDensity, densityOfMatrix, QuantumProver.ConditionalEntropy.mix]
    simp [hm]
  by_cases ho : p = 1
  · subst p
    have hm : mixDensity 1 ρ τ hp0 hp1 = τ := by
      apply density_ext
      simp [mixDensity, densityOfMatrix, QuantumProver.ConditionalEntropy.mix]
    simp [hm]
  have hp : 0 < p := lt_of_le_of_ne hp0 (Ne.symm hz)
  have hq : p < 1 := lt_of_le_of_ne hp1 ho
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨σ, hs, hnS⟩ := exists_separable_near_finite ρ hε
  obtain ⟨ω, ht, hnT⟩ := exists_separable_near_finite τ hε
  have hSep := mixDensity_separable σ.val ω.val σ.property ω.property hp0 hp1
  have h := (relativeEntropyEntanglementNat_le (mixDensity p ρ τ hp0 hp1)
    (mixDensity p σ.val ω.val hp0 hp1) hSep).trans
      (umegakiNats_mix_le ρ τ σ.val ω.val hs ht hp hq)
  rw [← coe_relativeEntropyEntanglementReal] at h
  have hReal : relativeEntropyEntanglementReal (mixDensity p ρ τ hp0 hp1) ≤
      (1-p) * finiteUmegakiNats ρ.matrix σ.val.matrix +
        p * finiteUmegakiNats τ.matrix ω.val.matrix := by exact_mod_cast h
  have hWeighted := add_le_add
    (mul_le_mul_of_nonneg_left hnS.le (sub_nonneg.mpr hp1))
    (mul_le_mul_of_nonneg_left hnT.le hp0)
  nlinarith

theorem affine_scalar_bound (ε M a b x y w H : ℝ) (hε : 0 ≤ ε)
    (hLower : (1-ε/(1+ε))*a + (ε/(1+ε))*x ≤ w+H)
    (hUpper : w ≤ (1-ε/(1+ε))*b + (ε/(1+ε))*y)
    (hx : 0 ≤ x) (hy : y ≤ M) :
    a-b ≤ ε*M + (1+ε)*H := by
  have hd : 0 < 1+ε := by linarith
  have hBase : (1+ε)*(1-ε/(1+ε)) = 1 := by field_simp [hd.ne']; ring
  have hNoise : (1+ε)*(ε/(1+ε)) = ε := by field_simp [hd.ne']
  have hCombined : (1-ε/(1+ε))*a + (ε/(1+ε))*x ≤
      (1-ε/(1+ε))*b + (ε/(1+ε))*y + H := by linarith
  have hs := mul_le_mul_of_nonneg_left
    hCombined hd.le
  simp only [mul_add, ← mul_assoc, hBase, hNoise, one_mul] at hs
  have hxy : y-x ≤ M := by linarith
  have hm := mul_le_mul_of_nonneg_left hxy hε
  nlinarith

def continuityBound (A : Type*) [Fintype A] (ε : ℝ) : ℝ :=
  2*ε*Real.log (Fintype.card A : ℝ) + (1+ε)*binaryEntropyNat (ε/(1+ε))

theorem erReal_continuity (ρ σ : Density (A × B)) {ε : ℝ}
    (hDistance : QuantumProver.ConditionalEntropy.traceDistance ρ.matrix σ.matrix ≤ ε) :
    |relativeEntropyEntanglementReal ρ - relativeEntropyEntanglementReal σ| ≤
      continuityBound A ε := by
  have hε := (QuantumProver.ConditionalEntropy.traceDistance_nonneg ρ.matrix σ.matrix).trans hDistance
  obtain ⟨W, TPlus, TMinus, hW, hPlus, hMinus, hWS, hWR⟩ :=
    QuantumProver.ConditionalEntropy.JordanCoupling.exists_common_density_coupling
      (density_matrix ρ) (density_matrix σ) hDistance
  obtain ⟨_, _, hp0, hpLt, _, hBase⟩ :=
    QuantumProver.ConditionalEntropy.JordanCoupling.coupling_weights hε
  let w : Density (A × B) := densityOfMatrix W hW
  let x : Density (A × B) := densityOfMatrix TMinus hMinus
  let y : Density (A × B) := densityOfMatrix TPlus hPlus
  have hMixR : mixDensity (ε/(1+ε)) ρ x hp0 hpLt.le = w := by
    apply density_ext
    simpa only [mixDensity, densityOfMatrix, QuantumProver.ConditionalEntropy.mix, hBase, x, w] using hWR.symm
  have hMixS : mixDensity (ε/(1+ε)) σ y hp0 hpLt.le = w := by
    apply density_ext
    simpa only [mixDensity, densityOfMatrix, QuantumProver.ConditionalEntropy.mix, hBase, y, w] using hWS.symm
  have hRL := erReal_mix_approx_affine_lower ρ x hp0 hpLt.le
  have hRU := erReal_mix_convex ρ x hp0 hpLt.le
  have hSL := erReal_mix_approx_affine_lower σ y hp0 hpLt.le
  have hSU := erReal_mix_convex σ y hp0 hpLt.le
  rw [hMixR] at hRL hRU
  rw [hMixS] at hSL hSU
  have hForward := affine_scalar_bound ε (2*Real.log (Fintype.card A : ℝ))
    (relativeEntropyEntanglementReal ρ) (relativeEntropyEntanglementReal σ)
    (relativeEntropyEntanglementReal x) (relativeEntropyEntanglementReal y)
    (relativeEntropyEntanglementReal w) (binaryEntropyNat (ε/(1+ε))) hε hRL hSU
      (relativeEntropyEntanglementReal_nonneg x) (erReal_le_two_log_left y)
  have hBackward := affine_scalar_bound ε (2*Real.log (Fintype.card A : ℝ))
    (relativeEntropyEntanglementReal σ) (relativeEntropyEntanglementReal ρ)
    (relativeEntropyEntanglementReal y) (relativeEntropyEntanglementReal x)
    (relativeEntropyEntanglementReal w) (binaryEntropyNat (ε/(1+ε))) hε hSL hRU
      (relativeEntropyEntanglementReal_nonneg y) (erReal_le_two_log_left x)
  apply abs_le.mpr
  constructor <;> dsimp only [continuityBound] <;> nlinarith

theorem continuityBound_tendsto_zero (A : Type*) [Fintype A] :
    Tendsto (continuityBound A) (𝓝 (0 : ℝ)) (𝓝 (0 : ℝ)) := by
  have hNoise : ContinuousAt (fun ε : ℝ => ε/(1+ε)) 0 :=
    continuousAt_id.div (continuousAt_const.add continuousAt_id) (by norm_num)
  have hEntropy : ContinuousAt (fun ε : ℝ => binaryEntropyNat (ε/(1+ε))) 0 :=
    (QuantumProver.ConditionalEntropy.binaryEntropy_continuous.mul continuous_const).continuousAt.comp hNoise
  have hLinear : ContinuousAt (fun ε : ℝ => 2*ε*Real.log (Fintype.card A : ℝ)) 0 :=
    (continuousAt_const.mul continuousAt_id).mul continuousAt_const
  have hCost : ContinuousAt (fun ε : ℝ => (1+ε)*binaryEntropyNat (ε/(1+ε))) 0 :=
    (continuousAt_const.add continuousAt_id).mul hEntropy
  have h : ContinuousAt (continuityBound A) 0 := hLinear.add hCost
  have hz : continuityBound A 0 = 0 := by simp [continuityBound, binaryEntropyNat]
  simpa only [hz] using h.tendsto

theorem binaryEntropyNat_le_log_two {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    binaryEntropyNat p ≤ Real.log 2 := by
  let U : Density Unit := ⟨1, Matrix.PosSemidef.one, by simp⟩
  let F : Density (Unit × Bool) := densityOfMatrix
    (QuantumProver.ConditionalEntropy.MixtureEntropy.binaryFlagged p U.matrix U.matrix)
    (QuantumProver.ConditionalEntropy.MixtureEntropy.binaryFlagged_isDensity hp0 hp1
      (density_matrix U) (density_matrix U))
  have he : entropyNat (rightMarginal F).matrix = binaryEntropyNat p := by
    rw [entropyNat_eq_entropyBits_mul_log]
    change QuantumProver.QuantumEntropy.entropyBits
      (fun b b' => ∑ i : Unit,
        QuantumProver.ConditionalEntropy.MixtureEntropy.binaryFlagged p U.matrix U.matrix (i,b) (i,b')) *
          Real.log 2 = _
    rw [QuantumProver.ConditionalEntropy.MixtureEntropy.binaryFlagged_flagMarginal U.trace_one U.trace_one]
    exact congrArg (fun z : ℝ => z * Real.log 2)
      (QuantumProver.ConditionalEntropy.MixtureEntropy.entropyBits_binaryDiagonal hp0 hp1)
  have h := entropyNat_le_log_card (rightMarginal F)
  rw [he] at h
  simpa using h

theorem erReal_continuity_coarse (ρ σ : Density (A × B)) {ε : ℝ}
    (hDistance : QuantumProver.ConditionalEntropy.traceDistance ρ.matrix σ.matrix ≤ ε)
    (hε1 : ε ≤ 1) :
    |relativeEntropyEntanglementReal ρ - relativeEntropyEntanglementReal σ| ≤
      2*ε*Real.log (Fintype.card A : ℝ) + 2*Real.log 2 := by
  have hε0 := (QuantumProver.ConditionalEntropy.traceDistance_nonneg ρ.matrix σ.matrix).trans hDistance
  obtain ⟨_, _, hp0, hp1, _, _⟩ :=
    QuantumProver.ConditionalEntropy.JordanCoupling.coupling_weights hε0
  have hb := binaryEntropyNat_le_log_two hp0 hp1.le
  have hc := mul_le_mul_of_nonneg_left hb (by linarith : 0 ≤ 1+ε)
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h := erReal_continuity ρ σ hDistance
  dsimp only [continuityBound] at h
  nlinarith

theorem erReal_continuity_copy_rate {Bcopy : ℕ → Type*}
    [∀ n, Fintype (Bcopy n)] [∀ n, DecidableEq (Bcopy n)]
    (ρ σ : ∀ n, Density (CopyIndex A n × Bcopy n))
    (hDistance : Tendsto (fun n =>
      QuantumProver.ConditionalEntropy.traceDistance (ρ n).matrix (σ n).matrix) atTop (𝓝 0)) :
    Tendsto (fun n =>
      (relativeEntropyEntanglementReal (ρ n) - relativeEntropyEntanglementReal (σ n)) / (n : ℝ))
        atTop (𝓝 0) := by
  let δ := fun n => QuantumProver.ConditionalEntropy.traceDistance (ρ n).matrix (σ n).matrix
  have hLinear : Tendsto (fun n => 2*δ n*Real.log (Fintype.card A : ℝ)) atTop (𝓝 0) := by
    simpa only [mul_zero, zero_mul] using
      ((tendsto_const_nhds (x := (2 : ℝ))).mul hDistance).mul_const
        (Real.log (Fintype.card A : ℝ))
  have hCost := tendsto_const_div_atTop_nhds_zero_nat (2*Real.log 2)
  have hBound : Tendsto (fun n : ℕ => 2*δ n*Real.log (Fintype.card A : ℝ) +
      (2*Real.log 2)/(n : ℝ)) atTop (𝓝 0) := by
    simpa only [zero_add] using hLinear.add hCost
  rw [tendsto_zero_iff_abs_tendsto_zero]
  apply squeeze_zero' (Filter.Eventually.of_forall (fun n => abs_nonneg _)) ?_ hBound
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hδ1 : δ n ≤ 1 :=
    QuantumProver.ConditionalEntropy.JordanCoupling.density_halfDistance_le_one
      (density_matrix (ρ n)) (density_matrix (σ n))
  have h := erReal_continuity_coarse (ρ n) (σ n) (le_refl (δ n)) hδ1
  rw [log_card_copyIndex] at h
  have hd := div_le_div_of_nonneg_right h hnR.le
  have hc : (2*δ n*((n : ℝ)*Real.log (Fintype.card A : ℝ)) + 2*Real.log 2)/(n : ℝ) =
      2*δ n*Real.log (Fintype.card A : ℝ) + (2*Real.log 2)/(n : ℝ) := by
    field_simp [hnR.ne']
    <;> ring
  rw [hc] at hd
  simpa only [abs_div, abs_of_pos hnR] using hd

theorem erReal_continuity_copy_rate_traceNorm {Bcopy : ℕ → Type*}
    [∀ n, Fintype (Bcopy n)] [∀ n, DecidableEq (Bcopy n)]
    (ρ σ : ∀ n, Density (CopyIndex A n × Bcopy n))
    (hNorm : Tendsto (fun n => QuantumProver.ConditionalEntropy.traceNorm
      ((ρ n).matrix - (σ n).matrix)) atTop (𝓝 0)) :
    Tendsto (fun n =>
      (relativeEntropyEntanglementReal (ρ n) - relativeEntropyEntanglementReal (σ n)) / (n : ℝ))
        atTop (𝓝 0) := by
  apply erReal_continuity_copy_rate ρ σ
  simpa only [QuantumProver.ConditionalEntropy.traceDistance, zero_div] using hNorm.div_const 2

end QuantumProver.DepolarizingSquashedEntanglement.BCYERContinuity

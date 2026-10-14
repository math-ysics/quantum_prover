import QuantumProver.InformationTheory.DepolarizingSquashedEntanglement.BCYRelativeEntropy
import QuantumProver.InformationTheory.ConditionalEntropy.MixtureEntropy

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

noncomputable section

open Matrix Set Filter
open scoped Topology BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
  Kronecker ContinuousFunctionalCalculus
open QuantumProver.SuperchannelDiscrimination.FlaggedStates
open QuantumProver.SuperchannelDiscrimination.TensorEntropy
open QuantumProver.SuperchannelDiscrimination.MatrixLog

namespace QuantumProver.DepolarizingSquashedEntanglement.BCYNonlockability

open BCYRelativeEntropy

variable {A E B I J : Type*} [Fintype A] [Fintype E] [Fintype B]
  [Fintype I] [Fintype J] [DecidableEq A] [DecidableEq E] [DecidableEq B]
  [DecidableEq I] [DecidableEq J]

theorem density_nonempty (ρ : Density I) : Nonempty I :=
  Fintype.card_pos_iff.mp
    (QuantumProver.ConditionalEntropy.ConditionalRange.isDensity_card_pos (density_matrix ρ))

def uniformDensity (J : Type*) [Fintype J] [DecidableEq J] [Nonempty J] : Density J where
  matrix := (Fintype.card J : ℝ)⁻¹ • (1 : QMatrix J)
  positive := Matrix.PosSemidef.one.smul (by positivity)
  trace_one := by
    rw [Matrix.trace_smul,Matrix.trace_one]
    apply Complex.ext
    · simp only [Complex.smul_re,Complex.natCast_re,smul_eq_mul,Complex.one_re]
      exact inv_mul_cancel₀ (ne_of_gt (by positivity : 0 < (Fintype.card J : ℝ)))
    · simp

theorem uniformDensity_posDef [Nonempty J] : (uniformDensity J).matrix.PosDef :=
  Matrix.PosDef.one.smul (by positivity)

theorem uniformDensity_log [Nonempty J] :
    cfc Real.log (uniformDensity J).matrix=
      (-Real.log (Fintype.card J : ℝ)) • (1 : QMatrix J) := by
  have h := cfc_algebraMap (A := QMatrix J) (p := IsSelfAdjoint)
    (Fintype.card J : ℝ)⁻¹ Real.log
  simpa only [uniformDensity,Algebra.algebraMap_eq_smul_one,Real.log_inv] using h

theorem marginal_support_lift {R : QMatrix (I × J)} (hR : R.PosSemidef)
    {S : QMatrix I} (hS : S.IsHermitian) {T : QMatrix J} (hT : T.PosDef)
    (hs : HasSupportIn (partialTraceRight R) S) : HasSupportIn R (S ⊗ₖ T) := by
  have hSP : QuantumProver.QuantumEntropy.partialTrace_right R*supportProjection S=
      QuantumProver.QuantumEntropy.partialTrace_right R :=
    (hasSupportIn_iff_mul_supportProjection hS).mp hs
  have hz := QuantumProver.QuantumEntropy.mul_right_marginal_kernel hR (1-supportProjection S) (by
    rw [Matrix.mul_sub,Matrix.mul_one,hSP,sub_self])
  have hsub : (1-supportProjection S) ⊗ₖ (1 : QMatrix J)=
      1-supportProjection S ⊗ₖ (1 : QMatrix J) := by
    calc
      _ = (1 : QMatrix I) ⊗ₖ (1 : QMatrix J)-
          supportProjection S ⊗ₖ (1 : QMatrix J) := by
        ext i j
        simp only [Matrix.kroneckerMap_apply,Matrix.sub_apply,sub_mul]
      _ = _ := by rw [Matrix.one_kronecker_one]
  rw [hsub,Matrix.mul_sub,Matrix.mul_one] at hz
  apply (hasSupportIn_iff_mul_supportProjection (isHermitian_kronecker hS hT.1)).mpr
  rw [supportProjection_kronecker hS hT.1,
    QuantumProver.SuperchannelDiscrimination.ModularMatrix.supportProjection_posDef hT]
  exact (sub_eq_zero.mp hz).symm

theorem trace_self_log {X : QMatrix I} (hX : X.IsHermitian) :
    (Matrix.trace (X*cfc Real.log X)).re= -entropyNat X := by
  rw [entropyNat_eq_shared,QuantumProver.QuantumEntropy.entropyNats,cfc_mulLog_eq_mul_log hX]
  ring

theorem marginal_entropy_excess_le_log_dimension (ρ : Density (I × J)) :
    entropyNat (leftMarginal ρ).matrix-entropyNat ρ.matrix ≤
      Real.log (Fintype.card J : ℝ) := by
  let R := densityReindex (Equiv.prodComm I J) ρ
  have h := (QuantumProver.ConditionalEntropy.conditionalEntropy_bounds (density_matrix R)).1
  have hm : QuantumProver.QuantumEntropy.partialTrace_left R.matrix=(leftMarginal ρ).matrix := by
    ext i j
    rfl
  have he : QuantumProver.QuantumEntropy.entropyBits R.matrix=
      QuantumProver.QuantumEntropy.entropyBits ρ.matrix :=
    QuantumProver.QuantumEntropy.entropyBits_reindex (Equiv.prodComm I J) ρ.positive.1
  rw [QuantumProver.ConditionalEntropy.conditionalEntropyBits,hm,
    QuantumProver.ConditionalEntropy.logDimA] at h
  change -(Real.log (Fintype.card J : ℝ)/Real.log 2) ≤
    QuantumProver.QuantumEntropy.entropyBits R.matrix-
      QuantumProver.QuantumEntropy.entropyBits (leftMarginal ρ).matrix at h
  rw [he] at h
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hn := mul_le_mul_of_nonneg_right h hl.le
  simp only [neg_mul,div_mul_cancel₀ _ hl.ne',sub_mul,
    ← QuantumProver.QuantumEntropy.entropyNats_eq_entropyBits_mul_log_two,
    ← entropyNat_eq_shared] at hn
  linarith

theorem uniform_extension_increment_of_support [Nonempty J]
    (ρ : Density (I × J)) (σ : Density I)
    (hs : HasSupportIn (leftMarginal ρ).matrix σ.matrix) :
    umegakiNats ρ.matrix (σ.matrix ⊗ₖ (uniformDensity J).matrix)=
      umegakiNats (leftMarginal ρ).matrix σ.matrix+
        ((entropyNat (leftMarginal ρ).matrix-entropyNat ρ.matrix+
          Real.log (Fintype.card J : ℝ) : ℝ) : EReal) := by
  have hs' := marginal_support_lift ρ.positive σ.positive.1
    (uniformDensity_posDef (J := J)) hs
  rw [umegakiNats_of_support _ _ hs',umegakiNats_of_support _ _ hs,← EReal.coe_add]
  apply congrArg (fun x : ℝ => (x : EReal))
  rw [Matrix.mul_sub,Matrix.trace_sub,Complex.sub_re,
    QuantumProver.QuantumEntropy.comparatorLogTrace_tensor σ.positive.1
      (uniformDensity J).positive.1 hs',Complex.add_re,uniformDensity_log,
    Matrix.mul_smul,Matrix.mul_one,Matrix.trace_smul,Complex.smul_re,smul_eq_mul]
  change (ρ.matrix*cfc Real.log ρ.matrix).trace.re-
    (((leftMarginal ρ).matrix*cfc Real.log σ.matrix).trace.re+
      (-Real.log (Fintype.card J : ℝ))*(rightMarginal ρ).matrix.trace.re)=
      ((leftMarginal ρ).matrix*(cfc Real.log (leftMarginal ρ).matrix-
        cfc Real.log σ.matrix)).trace.re+
      (entropyNat (leftMarginal ρ).matrix-entropyNat ρ.matrix+
        Real.log (Fintype.card J : ℝ))
  rw [(rightMarginal ρ).trace_one,Complex.one_re,Matrix.mul_sub,Matrix.trace_sub,
    Complex.sub_re,trace_self_log ρ.positive.1,
    trace_self_log (leftMarginal ρ).positive.1]
  ring

theorem umegakiNats_uniform_extension_le [Nonempty J]
    (ρ : Density (I × J)) (σ : Density I) :
    umegakiNats ρ.matrix (σ.matrix ⊗ₖ (uniformDensity J).matrix) ≤
      umegakiNats (leftMarginal ρ).matrix σ.matrix+
        ((2*Real.log (Fintype.card J : ℝ) : ℝ) : EReal) := by
  by_cases hs : HasSupportIn (leftMarginal ρ).matrix σ.matrix
  · rw [uniform_extension_increment_of_support ρ σ hs]
    exact add_le_add le_rfl (EReal.coe_le_coe_iff.mpr
      (by linarith [marginal_entropy_excess_le_log_dimension ρ]))
  · have ht := (umegakiNats_eq_top_iff (leftMarginal ρ).matrix σ.matrix).2 hs
    simp only [ht,EReal.top_add_coe,le_top]

def appendLocalDensity (σ : Density (A × E)) (τ : Density B) : Density (A × (E × B)) :=
  densityReindex (Equiv.prodAssoc A E B) (productDensity σ τ)

private def appendMatrixLinear (τ : Density B) :
    QMatrix (A × E) →ₗ[ℝ] QMatrix (A × (E × B)) :=
  (Matrix.reindexLinearEquiv ℝ ℂ (Equiv.prodAssoc A E B)
    (Equiv.prodAssoc A E B)).toLinearMap.comp
    ((Matrix.kroneckerBilinear : QMatrix (A × E) →ₗ[ℝ]
      QMatrix B →ₗ[ℝ] QMatrix ((A × E) × B)).flip τ.matrix)

theorem appendLocalDensity_separable (σ : Density (A × E)) (hσ : IsSeparable σ.matrix)
    (τ : Density B) : IsSeparable (appendLocalDensity σ τ).matrix := by
  apply isSeparable_map_of_products (appendMatrixLinear (A := A) (E := E) τ) _ hσ
  intro a e
  have heq : appendMatrixLinear τ (a.matrix ⊗ₖ e.matrix)=
      a.matrix ⊗ₖ (e.matrix ⊗ₖ τ.matrix) := by
    ext i j
    change (a.matrix i.1 j.1*e.matrix i.2.1 j.2.1)*τ.matrix i.2.2 j.2.2=
      a.matrix i.1 j.1*(e.matrix i.2.1 j.2.1*τ.matrix i.2.2 j.2.2)
    ring
  rw [heq]
  exact productDensity_separable a (productDensity e τ)

def discardLastDensity (ρ : Density (A × (E × B))) : Density (A × E) :=
  leftMarginal (densityReindex (Equiv.prodAssoc A E B).symm ρ)

theorem relativeEntropyEntanglementReal_nonlockability_last
    (ρ : Density (A × (E × B))) :
    relativeEntropyEntanglementReal ρ ≤
      relativeEntropyEntanglementReal (discardLastDensity ρ)+
        2*Real.log (Fintype.card B : ℝ) := by
  let R := densityReindex (Equiv.prodAssoc A E B).symm ρ
  letI : Nonempty B := density_nonempty (rightMarginal R)
  let τ := uniformDensity B
  have hr : Matrix.reindex (Equiv.prodAssoc A E B)
      (Equiv.prodAssoc A E B) R.matrix=ρ.matrix := by
    ext i j
    change ρ.matrix ((Equiv.prodAssoc A E B) ((Equiv.prodAssoc A E B).symm i))
      ((Equiv.prodAssoc A E B) ((Equiv.prodAssoc A E B).symm j))=ρ.matrix i j
    simp only [Equiv.apply_symm_apply]
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨σ,hσ⟩ := exists_separable_near (discardLastDensity ρ) (half_pos hε)
  have hle := relativeEntropyEntanglementNat_le ρ (appendLocalDensity σ.val τ)
    (appendLocalDensity_separable σ.val σ.property τ)
  have heq : umegakiNats ρ.matrix (appendLocalDensity σ.val τ).matrix=
      umegakiNats R.matrix (σ.val.matrix ⊗ₖ τ.matrix) := by
    rw [← hr]
    exact umegakiNats_reindex (Equiv.prodAssoc A E B) R.positive
      (σ.val.positive.kronecker τ.positive)
  rw [heq] at hle
  have hbound := umegakiNats_uniform_extension_le R σ.val
  have hc : ((2*Real.log (Fintype.card B : ℝ) : ℝ) : EReal) <
      ((2*Real.log (Fintype.card B : ℝ)+ε/2 : ℝ) : EReal) := by
    exact_mod_cast lt_add_of_pos_right (2*Real.log (Fintype.card B : ℝ)) (half_pos hε)
  have hlt := (hle.trans hbound).trans_lt (EReal.add_lt_add hσ hc)
  rw [← coe_relativeEntropyEntanglementReal,← EReal.coe_add] at hlt
  have hreal : relativeEntropyEntanglementReal ρ <
      (relativeEntropyEntanglementReal (discardLastDensity ρ)+ε/2)+
        (2*Real.log (Fintype.card B : ℝ)+ε/2) := by
    exact_mod_cast hlt
  linarith

theorem relativeEntropyEntanglementNat_nonlockability_last
    (ρ : Density (A × (E × B))) :
    relativeEntropyEntanglementNat ρ ≤
      relativeEntropyEntanglementNat (discardLastDensity ρ)+
        ((2*Real.log (Fintype.card B : ℝ) : ℝ) : EReal) := by
  rw [← coe_relativeEntropyEntanglementReal ρ,
    ← coe_relativeEntropyEntanglementReal (discardLastDensity ρ),← EReal.coe_add]
  exact_mod_cast relativeEntropyEntanglementReal_nonlockability_last ρ

theorem relativeEntropyEntanglementBits_nonlockability_last
    (ρ : Density (A × (E × B))) :
    relativeEntropyEntanglementReal ρ/Real.log 2 ≤
      relativeEntropyEntanglementReal (discardLastDensity ρ)/Real.log 2+
        2*(Real.log (Fintype.card B : ℝ)/Real.log 2) := by
  have h := div_le_div_of_nonneg_right
    (relativeEntropyEntanglementReal_nonlockability_last ρ)
    (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
  simpa only [add_div,mul_div_assoc] using h

def discardMiddleDensity (ρ : Density (A × (B × E))) : Density (A × E) :=
  discardLastDensity
    (densityReindex (Equiv.prodCongr (Equiv.refl A) (Equiv.prodComm B E)) ρ)

theorem discardMiddleDensity_matrix (ρ : Density (A × (B × E))) :
    (discardMiddleDensity ρ).matrix=
      (fun i j : A × E => ∑ b, ρ.matrix (i.1,(b,i.2)) (j.1,(b,j.2))) := by
  ext i j
  rfl

theorem relativeEntropyEntanglementReal_nonlockability
    (ρ : Density (A × (B × E))) :
    relativeEntropyEntanglementReal ρ ≤
      relativeEntropyEntanglementReal (discardMiddleDensity ρ)+
        2*Real.log (Fintype.card B : ℝ) := by
  have h := relativeEntropyEntanglementReal_nonlockability_last
    (densityReindex (Equiv.prodCongr (Equiv.refl A) (Equiv.prodComm B E)) ρ)
  rw [relativeEntropyEntanglementReal_reindex (Equiv.refl A) (Equiv.prodComm B E)] at h
  exact h

theorem relativeEntropyEntanglementNat_nonlockability
    (ρ : Density (A × (B × E))) :
    relativeEntropyEntanglementNat ρ ≤
      relativeEntropyEntanglementNat (discardMiddleDensity ρ)+
        ((2*Real.log (Fintype.card B : ℝ) : ℝ) : EReal) := by
  rw [← coe_relativeEntropyEntanglementReal ρ,
    ← coe_relativeEntropyEntanglementReal (discardMiddleDensity ρ),← EReal.coe_add]
  exact_mod_cast relativeEntropyEntanglementReal_nonlockability ρ

theorem relativeEntropyEntanglementBits_nonlockability
    (ρ : Density (A × (B × E))) :
    relativeEntropyEntanglementReal ρ/Real.log 2 ≤
      relativeEntropyEntanglementReal (discardMiddleDensity ρ)/Real.log 2+
        2*(Real.log (Fintype.card B : ℝ)/Real.log 2) := by
  have h := div_le_div_of_nonneg_right
    (relativeEntropyEntanglementReal_nonlockability ρ)
    (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
  simpa only [add_div,mul_div_assoc] using h

end QuantumProver.DepolarizingSquashedEntanglement.BCYNonlockability

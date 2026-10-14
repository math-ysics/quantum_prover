import QuantumProver.InformationTheory.SuperchannelDiscrimination.ChannelUniformApproximation
import QuantumProver.InformationTheory.SuperchannelDiscrimination.ChannelTestingPrimal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace QuantumProver.SuperchannelDiscrimination.ChannelTestingPhysical

open Matrix KrausCompletion CPWrappers FlaggedStates TensorEntropy ChannelRegularization
open scoped BigOperators ComplexOrder MatrixOrder Matrix Kronecker Matrix.Norms.L2Operator

variable {I O R E : Type*} [Fintype I] [Fintype O] [Fintype R] [Fintype E]
  [DecidableEq I] [DecidableEq O] [DecidableEq R] [DecidableEq E]

def legalTester (ρ : Matrix I I ℂ) (T : Matrix (I × O) (I × O) ℂ) : Prop :=
  IsDensity ρ ∧ T.PosSemidef ∧ (ρ ⊗ₖ (1 : Matrix O O ℂ) - T).PosSemidef

def choiTestingValue (H : Matrix (I × O) (I × O) ℂ) : EReal :=
  ⨆ (ρ : Matrix I I ℂ) (T : Matrix (I × O) (I × O) ℂ) (_h : legalTester ρ T),
    ((H * T).trace.re : EReal)

def purifiedVector (A : Matrix R I ℂ) : I × R → ℂ := fun x => A x.2 x.1

def vectorInput (A : Matrix R I ℂ) : Matrix (I × R) (I × R) ℂ :=
  Matrix.vecMulVec (purifiedVector A) (star (purifiedVector A))

theorem vectorInput_posSemidef (A : Matrix R I ℂ) : (vectorInput A).PosSemidef :=
  Matrix.posSemidef_vecMulVec_self_star _

theorem vectorInput_trace (A : Matrix R I ℂ) :
    (vectorInput A).trace = (Aᴴ * A).trace := by
  simp only [vectorInput, purifiedVector, Matrix.trace, Matrix.diag,
    Matrix.vecMulVec, Pi.star_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro r hr
  exact mul_comm _ _

theorem kronecker_identity_congruence_apply (A : Matrix R I ℂ)
    (J : Matrix (I × O) (I × O) ℂ) (r s : R) (o p : O) :
    ((A ⊗ₖ (1 : Matrix O O ℂ)) * J * (A ⊗ₖ (1 : Matrix O O ℂ))ᴴ) (r, o) (s, p) =
      ∑ i : I, ∑ j : I, A r i * star (A s j) * J (i, o) (j, p) := by
  simp [Matrix.mul_apply, Matrix.kronecker_apply, Matrix.conjTranspose_apply,
    Fintype.sum_prod_type, Matrix.one_apply, apply_ite,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem vectorInput_output (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ)
    (A : Matrix R I ℂ) :
    Matrix.reindex (Equiv.prodComm O R) (Equiv.prodComm O R)
        (amplify Φ R (vectorInput A)) =
      (A ⊗ₖ (1 : Matrix O O ℂ)) * CPTPKraus.choi Φ *
        (A ⊗ₖ (1 : Matrix O O ℂ))ᴴ := by
  ext ⟨r, o⟩ ⟨s, p⟩
  change Φ (fun a b => vectorInput A (a, r) (b, s)) o p = _
  conv_lhs => rw [← CPTPKraus.fromChoi_choi Φ, CPTPKraus.fromChoi_apply]
  rw [kronecker_identity_congruence_apply]
  rfl

theorem sqrt_kronecker_gram {ρ : Matrix I I ℂ} (hρ : ρ.PosSemidef) :
    (CFC.sqrt ρ ⊗ₖ (1 : Matrix O O ℂ)) *
      (CFC.sqrt ρ ⊗ₖ (1 : Matrix O O ℂ))ᴴ = ρ ⊗ₖ (1 : Matrix O O ℂ) := by
  rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
    (CFC.sqrt_nonneg ρ).posSemidef.1.eq, ← Matrix.mul_kronecker_mul,
    CFC.sqrt_mul_sqrt_self ρ hρ.nonneg, Matrix.one_mul]

theorem sqrt_vectorInput_isDensity {ρ : Matrix I I ℂ} (hρ : IsDensity ρ) :
    IsDensity (vectorInput (CFC.sqrt ρ)) := by
  refine ⟨vectorInput_posSemidef _, ?_⟩
  rw [vectorInput_trace, (CFC.sqrt_nonneg ρ).posSemidef.1.eq,
    CFC.sqrt_mul_sqrt_self ρ hρ.1.nonneg, hρ.2]

theorem legalTester_effect_factor {ρ : Matrix I I ℂ}
    {T : Matrix (I × O) (I × O) ℂ} (h : legalTester ρ T) :
    ∃ F : Matrix (I × O) (I × O) ℂ, IsEffect F ∧
      T = (CFC.sqrt ρ ⊗ₖ (1 : Matrix O O ℂ)) * F *
        (CFC.sqrt ρ ⊗ₖ (1 : Matrix O O ℂ))ᴴ := by
  let B := CFC.sqrt ρ ⊗ₖ (1 : Matrix O O ℂ)
  let K := CFC.sqrt T
  have hdom : ((1 : ℝ) • (B * Bᴴ) - K * Kᴴ).PosSemidef := by
    simpa only [B, K, one_smul, sqrt_kronecker_gram h.1.1,
      (CFC.sqrt_nonneg T).posSemidef.1.eq,
      CFC.sqrt_mul_sqrt_self T h.2.1.nonneg] using h.2.2
  obtain ⟨D, hBD, hD⟩ := GlobalMatrixSplit.exists_bounded_column_factor
    B K 1 (by norm_num) hdom
  refine ⟨D * Dᴴ, ⟨Matrix.posSemidef_self_mul_conjTranspose D,
    by simpa only [one_smul] using hD⟩, ?_⟩
  calc
    T = K * Kᴴ := by
      rw [show Kᴴ = K from (CFC.sqrt_nonneg T).posSemidef.1.eq]
      exact (CFC.sqrt_mul_sqrt_self T h.2.1.nonneg).symm
    _ = (B * D) * (B * D)ᴴ := by rw [hBD]
    _ = _ := by simp only [B, Matrix.conjTranspose_mul, Matrix.mul_assoc]

theorem reindex_isEffect (e : I ≃ R) {F : Matrix I I ℂ} (hF : IsEffect F) :
    IsEffect (Matrix.reindex e e F) := by
  refine ⟨hF.1.submatrix e.symm, ?_⟩
  have hc := hF.2.submatrix e.symm
  change ((1 : Matrix I I ℂ).submatrix e.symm e.symm -
    F.submatrix e.symm e.symm).PosSemidef at hc
  rw [Matrix.submatrix_one_equiv] at hc
  exact hc

theorem acceptanceProbability_reindex (e : I ≃ R) (X F : Matrix I I ℂ) :
    acceptanceProbability (Matrix.reindex e e X) (Matrix.reindex e e F) =
      acceptanceProbability X F := by
  unfold acceptanceProbability
  have hm : Matrix.reindex e e X * Matrix.reindex e e F =
      Matrix.reindex e e (X * F) :=
    (Matrix.reindexRingEquiv ℂ e).map_mul X F |>.symm
  rw [hm]
  exact congrArg Complex.re (reindexMap_tracePreserving e (X * F))

theorem vectorInput_probability (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ)
    (A : Matrix R I ℂ) (F : Matrix (R × O) (R × O) ℂ) :
    acceptanceProbability (amplify Φ R (vectorInput A))
        (Matrix.reindex (Equiv.prodComm R O) (Equiv.prodComm R O) F) =
      (CPTPKraus.choi Φ * ((A ⊗ₖ (1 : Matrix O O ℂ))ᴴ * F *
        (A ⊗ₖ (1 : Matrix O O ℂ)))).trace.re := by
  have hr := acceptanceProbability_reindex (Equiv.prodComm O R)
    (amplify Φ R (vectorInput A))
    (Matrix.reindex (Equiv.prodComm R O) (Equiv.prodComm R O) F)
  have he : Matrix.reindex (Equiv.prodComm O R) (Equiv.prodComm O R)
      (Matrix.reindex (Equiv.prodComm R O) (Equiv.prodComm R O) F) = F := by
    ext x y
    rfl
  rw [he, vectorInput_output] at hr
  rw [← hr]
  unfold acceptanceProbability
  apply congrArg Complex.re
  simpa only [Matrix.mul_assoc] using Matrix.trace_mul_comm
    (A ⊗ₖ (1 : Matrix O O ℂ))
    (CPTPKraus.choi Φ * (A ⊗ₖ (1 : Matrix O O ℂ))ᴴ * F)

theorem legalTester_physical_realization {ρ : Matrix I I ℂ}
    {T : Matrix (I × O) (I × O) ℂ} (h : legalTester ρ T) :
    ∃ ξ : Matrix (I × I) (I × I) ℂ,
      ∃ F : Matrix (O × I) (O × I) ℂ, IsDensity ξ ∧ IsEffect F ∧
        ∀ Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ,
          acceptanceProbability (amplify Φ I ξ) F = (CPTPKraus.choi Φ * T).trace.re := by
  obtain ⟨G, hG, hTG⟩ := legalTester_effect_factor h
  refine ⟨vectorInput (CFC.sqrt ρ),
    Matrix.reindex (Equiv.prodComm I O) (Equiv.prodComm I O) G,
    sqrt_vectorInput_isDensity h.1, reindex_isEffect _ hG, ?_⟩
  intro Φ
  rw [vectorInput_probability]
  have hM : (CFC.sqrt ρ ⊗ₖ (1 : Matrix O O ℂ))ᴴ =
      CFC.sqrt ρ ⊗ₖ (1 : Matrix O O ℂ) := by
    rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
      (CFC.sqrt_nonneg ρ).posSemidef.1.eq]
  rw [hM] at hTG ⊢
  rw [← hTG]

def inputColumn (ξ : Matrix (I × R) (I × R) ℂ) (e : I × R) : Matrix R I ℂ :=
  fun r i => CFC.sqrt ξ (i, r) e

def physicalMargin (ξ : Matrix (I × R) (I × R) ℂ) : Matrix I I ℂ :=
  ∑ e : I × R, (inputColumn ξ e)ᴴ * inputColumn ξ e

def physicalTester (ξ : Matrix (I × R) (I × R) ℂ)
    (F : Matrix (O × R) (O × R) ℂ) : Matrix (I × O) (I × O) ℂ :=
  ∑ e : I × R, (inputColumn ξ e ⊗ₖ (1 : Matrix O O ℂ))ᴴ *
    Matrix.reindex (Equiv.prodComm O R) (Equiv.prodComm O R) F *
    (inputColumn ξ e ⊗ₖ (1 : Matrix O O ℂ))

theorem inputColumns_reconstruct {ξ : Matrix (I × R) (I × R) ℂ}
    (hξ : ξ.PosSemidef) : (∑ e : I × R, vectorInput (inputColumn ξ e)) = ξ := by
  calc
    _ = CFC.sqrt ξ * (CFC.sqrt ξ)ᴴ := by
      ext ⟨i, r⟩ ⟨j, s⟩
      simp only [Matrix.sum_apply, vectorInput, purifiedVector, inputColumn,
        Matrix.vecMulVec, Pi.star_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
      rfl
    _ = ξ := by rw [(CFC.sqrt_nonneg ξ).posSemidef.1.eq,
      CFC.sqrt_mul_sqrt_self ξ hξ.nonneg]

theorem physicalMargin_isDensity {ξ : Matrix (I × R) (I × R) ℂ}
    (hξ : IsDensity ξ) : IsDensity (physicalMargin ξ) := by
  refine ⟨Matrix.posSemidef_sum Finset.univ
    (fun e _ => Matrix.posSemidef_conjTranspose_mul_self (inputColumn ξ e)), ?_⟩
  rw [physicalMargin, Matrix.trace_sum]
  simp_rw [← vectorInput_trace]
  rw [← Matrix.trace_sum, inputColumns_reconstruct hξ.1, hξ.2]

theorem physicalTester_posSemidef (ξ : Matrix (I × R) (I × R) ℂ)
    {F : Matrix (O × R) (O × R) ℂ} (hF : F.PosSemidef) :
    (physicalTester ξ F).PosSemidef := by
  apply Matrix.posSemidef_sum Finset.univ
  intro e he
  have hG : (Matrix.reindex (Equiv.prodComm O R) (Equiv.prodComm O R) F).PosSemidef :=
    hF.submatrix (Equiv.prodComm O R).symm
  have h := hG.mul_mul_conjTranspose_same
    (inputColumn ξ e ⊗ₖ (1 : Matrix O O ℂ))ᴴ
  rw [Matrix.conjTranspose_conjTranspose] at h
  exact h

theorem physicalTester_le_margin (ξ : Matrix (I × R) (I × R) ℂ)
    {F : Matrix (O × R) (O × R) ℂ} (hF : IsEffect F) :
    (physicalMargin ξ ⊗ₖ (1 : Matrix O O ℂ) - physicalTester ξ F).PosSemidef := by
  let G := Matrix.reindex (Equiv.prodComm O R) (Equiv.prodComm O R) F
  have hG : IsEffect G := reindex_isEffect _ hF
  have hm (e : I × R) : (inputColumn ξ e ⊗ₖ (1 : Matrix O O ℂ))ᴴ *
      (inputColumn ξ e ⊗ₖ (1 : Matrix O O ℂ)) =
        ((inputColumn ξ e)ᴴ * inputColumn ξ e) ⊗ₖ (1 : Matrix O O ℂ) := by
    rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
      ← Matrix.mul_kronecker_mul, Matrix.one_mul]
  have hs : physicalMargin ξ ⊗ₖ (1 : Matrix O O ℂ) =
      ∑ e : I × R, ((inputColumn ξ e)ᴴ * inputColumn ξ e) ⊗ₖ
        (1 : Matrix O O ℂ) := by
    ext ⟨i, o⟩ ⟨j, p⟩
    simp only [physicalMargin, Matrix.kronecker_apply, Matrix.sum_apply, Finset.sum_mul]
  have heq : physicalMargin ξ ⊗ₖ (1 : Matrix O O ℂ) - physicalTester ξ F =
      ∑ e : I × R, (inputColumn ξ e ⊗ₖ (1 : Matrix O O ℂ))ᴴ * (1 - G) *
        (inputColumn ξ e ⊗ₖ (1 : Matrix O O ℂ)) := by
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one,
      Finset.sum_sub_distrib, hm]
    rw [hs]
    rfl
  rw [heq]
  apply Matrix.posSemidef_sum Finset.univ
  intro e he
  simpa only [Matrix.conjTranspose_conjTranspose] using
    hG.2.mul_mul_conjTranspose_same (inputColumn ξ e ⊗ₖ (1 : Matrix O O ℂ))ᴴ

theorem physicalTester_legal {ξ : Matrix (I × R) (I × R) ℂ}
    {F : Matrix (O × R) (O × R) ℂ} (hξ : IsDensity ξ) (hF : IsEffect F) :
    legalTester (physicalMargin ξ) (physicalTester ξ F) :=
  ⟨physicalMargin_isDensity hξ, physicalTester_posSemidef ξ hF.1,
    physicalTester_le_margin ξ hF⟩

theorem physicalTester_probability (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ)
    {ξ : Matrix (I × R) (I × R) ℂ} (hξ : ξ.PosSemidef)
    (F : Matrix (O × R) (O × R) ℂ) :
    acceptanceProbability (amplify Φ R ξ) F =
      (CPTPKraus.choi Φ * physicalTester ξ F).trace.re := by
  have hp (e : I × R) : acceptanceProbability
      (amplify Φ R (vectorInput (inputColumn ξ e))) F =
      (CPTPKraus.choi Φ * ((inputColumn ξ e ⊗ₖ (1 : Matrix O O ℂ))ᴴ *
        Matrix.reindex (Equiv.prodComm O R) (Equiv.prodComm O R) F *
        (inputColumn ξ e ⊗ₖ (1 : Matrix O O ℂ)))).trace.re := by
    have h := vectorInput_probability Φ (inputColumn ξ e)
      (Matrix.reindex (Equiv.prodComm O R) (Equiv.prodComm O R) F)
    exact h
  conv_lhs => rw [← inputColumns_reconstruct hξ]
  have hsum : amplify Φ R (∑ e : I × R, vectorInput (inputColumn ξ e)) =
      ∑ e : I × R, amplify Φ R (vectorInput (inputColumn ξ e)) := by
    ext x y
    change Φ (fun a b => (∑ e : I × R, vectorInput (inputColumn ξ e)) (a, x.2) (b, y.2))
      x.1 y.1 = _
    simp only [Matrix.sum_apply]
    have hf : (fun a b => ∑ e : I × R, vectorInput (inputColumn ξ e) (a, x.2) (b, y.2)) =
        ∑ e : I × R, (fun a b => vectorInput (inputColumn ξ e) (a, x.2) (b, y.2)) := by
      ext a b
      simp only [Finset.sum_apply]
    rw [hf, map_sum]
    simp only [Matrix.sum_apply]
    rfl
  rw [hsum]
  simp only [acceptanceProbability, Matrix.sum_mul, Matrix.trace_sum, Complex.re_sum,
    physicalTester, Matrix.mul_sum]
  exact Finset.sum_congr rfl (fun e _ => hp e)

def physicalTestingValue (Φ Ψ : FiniteCPTP I O) (t : ℝ) : EReal :=
  ⨆ (k : ℕ) (ξ : Matrix (I × Fin k) (I × Fin k) ℂ) (_hξ : IsDensity ξ)
    (F : Matrix (O × Fin k) (O × Fin k) ℂ) (_hF : IsEffect F),
    ((acceptanceProbability (amplify Φ.map (Fin k) ξ) F -
      t * acceptanceProbability (amplify Ψ.map (Fin k) ξ) F : ℝ) : EReal)

theorem physicalTestingValue_witness_le (Φ Ψ : FiniteCPTP I O) (t : ℝ)
    (R : Type*) [Fintype R] [DecidableEq R]
    {ξ : Matrix (I × R) (I × R) ℂ} {F : Matrix (O × R) (O × R) ℂ}
    (hξ : IsDensity ξ) (hF : IsEffect F) :
    ((acceptanceProbability (amplify Φ.map R ξ) F -
      t * acceptanceProbability (amplify Ψ.map R ξ) F : ℝ) : EReal) ≤
        physicalTestingValue Φ Ψ t := by
  let e : R ≃ Fin (Fintype.card R) := Fintype.equivFin R
  let eI := Equiv.prodCongr (Equiv.refl I) e
  let eO := Equiv.prodCongr (Equiv.refl O) e
  let ξ' := Matrix.reindex eI eI ξ
  let F' := Matrix.reindex eO eO F
  have hξ' : IsDensity ξ' := channel_density (reindexChannel eI) hξ.1 hξ.2
  have hF' : IsEffect F' := reindex_isEffect eO hF
  have hp (Ω : FiniteCPTP I O) :
      acceptanceProbability (amplify Ω.map (Fin (Fintype.card R)) ξ') F' =
        acceptanceProbability (amplify Ω.map R ξ) F := by
    change acceptanceProbability (amplify Ω.map (Fin (Fintype.card R))
      (Matrix.reindex (Equiv.prodCongr (Equiv.refl I) e)
        (Equiv.prodCongr (Equiv.refl I) e) ξ))
      (Matrix.reindex eO eO F) = _
    rw [amplify_reindex_reference]
    exact acceptanceProbability_reindex eO _ _
  rw [← hp Φ, ← hp Ψ]
  exact le_iSup_of_le (Fintype.card R) (le_iSup_of_le ξ'
    (le_iSup_of_le hξ' (le_iSup_of_le F' (le_iSup_of_le hF' le_rfl))))

theorem difference_pairing (H K T : Matrix (I × O) (I × O) ℂ) (t : ℝ) :
    ((H - t • K) * T).trace.re = (H * T).trace.re - t * (K * T).trace.re := by
  simp only [Matrix.sub_mul, Matrix.smul_mul, Matrix.trace_sub,
    Matrix.trace_smul, Complex.sub_re, Complex.smul_re, smul_eq_mul]

theorem physicalTestingValue_le_choiTestingValue (Φ Ψ : FiniteCPTP I O) (t : ℝ) :
    physicalTestingValue Φ Ψ t ≤
      choiTestingValue (CPTPKraus.choi Φ.map - t • CPTPKraus.choi Ψ.map) := by
  refine iSup_le fun k => iSup_le fun ξ => iSup_le fun hξ =>
    iSup_le fun F => iSup_le fun hF => ?_
  have hp := physicalTester_probability Φ.map hξ.1 F
  have hq := physicalTester_probability Ψ.map hξ.1 F
  rw [hp, hq, ← difference_pairing]
  exact le_iSup_of_le (physicalMargin ξ) (le_iSup_of_le (physicalTester ξ F)
    (le_iSup_of_le (physicalTester_legal hξ hF) le_rfl))

theorem choiTestingValue_le_physicalTestingValue (Φ Ψ : FiniteCPTP I O) (t : ℝ) :
    choiTestingValue (CPTPKraus.choi Φ.map - t • CPTPKraus.choi Ψ.map) ≤
      physicalTestingValue Φ Ψ t := by
  refine iSup_le fun ρ => iSup_le fun T => iSup_le fun h => ?_
  obtain ⟨ξ, F, hξ, hF, hp⟩ := legalTester_physical_realization h
  rw [difference_pairing, ← hp Φ.map, ← hp Ψ.map]
  exact physicalTestingValue_witness_le Φ Ψ t I hξ hF

theorem choiTestingValue_eq_physicalTestingValue (Φ Ψ : FiniteCPTP I O) (t : ℝ) :
    choiTestingValue (CPTPKraus.choi Φ.map - t • CPTPKraus.choi Ψ.map) =
      physicalTestingValue Φ Ψ t :=
  le_antisymm (choiTestingValue_le_physicalTestingValue Φ Ψ t)
    (physicalTestingValue_le_choiTestingValue Φ Ψ t)

theorem channelPower_choiTestingValue_eq_testingAdvantage
    (Φ Ψ : FiniteCPTP I O) (n : ℕ) (t : ℝ) :
    choiTestingValue (CPTPKraus.choi (channelPower Φ n).map -
      t • CPTPKraus.choi (channelPower Ψ n).map) =
        ChannelTestingPrimal.testingAdvantage Φ Ψ n t :=
  choiTestingValue_eq_physicalTestingValue (channelPower Φ n) (channelPower Ψ n) t

theorem channelPower_choiTestingValue_dyadic_le (Φ Ψ : FiniteCPTP I O) [Nonempty I]
    {n : ℕ} (hn : 0 < n) {r B : ℝ} (hr : 0 < r)
    (hReg : regularizedRelativeEntropyBits Φ Ψ ≤ (B : EReal)) :
    choiTestingValue (CPTPKraus.choi (channelPower Φ n).map -
      ((2 : ℝ) ^ ((n : ℝ) * r)) • CPTPKraus.choi (channelPower Ψ n).map) ≤
      ((min 1 (((n : ℝ) * B + 1) / ((n : ℝ) * r)) : ℝ) : EReal) := by
  rw [channelPower_choiTestingValue_eq_testingAdvantage]
  exact ChannelTestingPrimal.testingAdvantage_dyadic_le Φ Ψ hn hr hReg

end QuantumProver.SuperchannelDiscrimination.ChannelTestingPhysical

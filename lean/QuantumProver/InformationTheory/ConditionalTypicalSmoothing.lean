import QuantumProver.InformationTheory.QuantumEntropy.PartialTraceKraus
import QuantumProver.InformationTheory.QuantumEntropy.TensorReindex
import QuantumProver.InformationTheory.QuantumTypicalProjectors
import QuantumProver.LinearAlgebra.SandwichedDPI.TraceNorm
import QuantumProver.InformationTheory.SuperchannelDiscrimination.TestingConsequences

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 5000

noncomputable section

namespace QuantumProver.ConditionalTypicalSmoothing

open Matrix Filter
open QuantumProver.SuperchannelDiscrimination
open PetzSmoothing FlaggedStates
open scoped BigOperators Topology ComplexOrder MatrixOrder Matrix Kronecker

variable {I X Y : Type*} [Fintype I] [DecidableEq I]
  [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]

abbrev traceNorm {J : Type*} [Fintype J] [DecidableEq J]
    (A : Matrix J J ℂ) : ℝ := EffectPerturbation.traceNorm A

theorem traceNorm_add_le (A B : Matrix I I ℂ) :
    traceNorm (A + B) ≤ traceNorm A + traceNorm B := by
  obtain ⟨U, hU, ht⟩ := QuantumProver.SandwichedDPI.exists_unitary_traceNorm_attainer (A + B)
  change QuantumProver.SandwichedDPI.traceNorm (A + B) ≤
    QuantumProver.SandwichedDPI.traceNorm A + QuantumProver.SandwichedDPI.traceNorm B
  rw [← ht, Matrix.mul_add, Matrix.trace_add, Complex.add_re]
  exact add_le_add (QuantumProver.SandwichedDPI.re_trace_unitary_mul_le_traceNorm A U hU)
    (QuantumProver.SandwichedDPI.re_trace_unitary_mul_le_traceNorm B U hU)

def doubleCrop (P Q R : Matrix I I ℂ) : Matrix I I ℂ :=
  cropMap Q (cropMap P R)

theorem doubleCrop_posSemidef (P Q : Matrix I I ℂ) {R : Matrix I I ℂ}
    (hR : R.PosSemidef) : (doubleCrop P Q R).PosSemidef :=
  cropMap_posSemidef Q (cropMap_posSemidef P hR)

theorem doubleCrop_trace_le {P Q R : Matrix I I ℂ}
    (hP : IsProjection P) (hQ : IsProjection Q) (hR : R.PosSemidef) :
    (doubleCrop P Q R).trace.re ≤ R.trace.re :=
  (cropMap_trace_re_le hQ (cropMap_posSemidef P hR)).trans
    (cropMap_trace_re_le hP hR)

theorem doubleCrop_supported {P Q R : Matrix I I ℂ} (hQ : IsProjection Q) :
    Q * doubleCrop P Q R = doubleCrop P Q R ∧
      doubleCrop P Q R * Q = doubleCrop P Q R := by
  simp only [doubleCrop, cropMap_apply, hQ.selfAdjoint.eq]
  constructor
  · simp only [← Matrix.mul_assoc, hQ.idempotent]
  · simp only [Matrix.mul_assoc, hQ.idempotent]

theorem crop_traceNorm_contracts {Q : Matrix I I ℂ} (hQ : IsProjection Q)
    {A : Matrix I I ℂ} (hA : A.IsHermitian) :
    traceNorm (cropMap Q A) ≤ traceNorm A :=
  EffectPerturbation.traceNorm_contracts_positive_traceNonincreasing (cropMap Q)
    (fun _ h => cropMap_posSemidef Q h)
    (fun _ h => cropMap_trace_re_le hQ h) hA

theorem crop_gentle {P R : Matrix I I ℂ} (hR : IsDensity R) (hP : IsProjection P) :
    traceNorm (R - cropMap P R) ≤ 2 * Real.sqrt (1 - (R * P).trace.re) := by
  have h := gentle_crop_traceNorm hR hP.complement
  have ht : (R * (1 - P)).trace.re = 1 - (R * P).trace.re := by
    simp only [Matrix.mul_sub, Matrix.mul_one, Matrix.trace_sub, hR.2,
      Complex.sub_re, Complex.one_re]
  simpa only [sub_sub_cancel, ht] using h

theorem doubleCrop_gentle {P Q R : Matrix I I ℂ}
    (hR : IsDensity R) (hP : IsProjection P) (hQ : IsProjection Q) :
    traceNorm (R - doubleCrop P Q R) ≤
      2 * Real.sqrt (1 - (R * P).trace.re) +
        2 * Real.sqrt (1 - (R * Q).trace.re) := by
  have he : R - doubleCrop P Q R =
      cropMap Q (R - cropMap P R) + (R - cropMap Q R) := by
    rw [map_sub]
    dsimp only [doubleCrop]
    abel
  rw [he]
  exact (traceNorm_add_le _ _).trans
    (add_le_add
      ((crop_traceNorm_contracts hQ (hR.1.1.sub (cropMap_posSemidef P hR.1).1)).trans
        (crop_gentle hR hP)) (crop_gentle hR hQ))

theorem doubleCrop_projector_cap {P Q R : Matrix I I ℂ}
    (hQ : IsProjection Q) (c : ℝ)
    (hcap : (c • (1 : Matrix I I ℂ) - cropMap P R).PosSemidef) :
    (c • Q - doubleCrop P Q R).PosSemidef := by
  have h := cropMap_posSemidef Q hcap
  convert h using 1
  simp only [doubleCrop, cropMap_apply, hQ.selfAdjoint.eq, Matrix.mul_sub,
    Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
    hQ.idempotent]

theorem doubleCrop_identity_cap {P Q R : Matrix I I ℂ}
    (hQ : IsProjection Q) {c : ℝ} (hc : 0 ≤ c)
    (hcap : (c • (1 : Matrix I I ℂ) - cropMap P R).PosSemidef) :
    (c • (1 : Matrix I I ℂ) - doubleCrop P Q R).PosSemidef := by
  have h := (doubleCrop_projector_cap hQ c hcap).add (hQ.complement.posSemidef.smul hc)
  convert h using 1
  simp only [smul_sub]
  abel

theorem doubleCrop_conditional_cap {P Q R S : Matrix I I ℂ}
    (hQ : IsProjection Q) {c d : ℝ} (hc : 0 ≤ c) (hd : 0 < d)
    (hcap : (c • (1 : Matrix I I ℂ) - cropMap P R).PosSemidef)
    (hlower : (S - d • Q).PosSemidef) :
    ((c / d) • S - doubleCrop P Q R).PosSemidef := by
  have h := (doubleCrop_projector_cap hQ c hcap).add
    (hlower.smul (div_nonneg hc hd.le))
  have hcd : (c / d) * d = c := div_mul_cancel₀ c hd.ne'
  convert h using 1
  simp only [smul_sub, smul_smul, hcd]
  abel

theorem doubleCrop_purity_le {P Q R : Matrix I I ℂ}
    (hR : R.PosSemidef) (hQ : IsProjection Q) {c : ℝ} (hc : 0 ≤ c)
    (hcap : (c • (1 : Matrix I I ℂ) - cropMap P R).PosSemidef) :
    (doubleCrop P Q R * doubleCrop P Q R).trace.re ≤
      c * (doubleCrop P Q R).trace.re := by
  have h := trace_mul_re_nonneg
    (doubleCrop_posSemidef P Q hR) (doubleCrop_identity_cap hQ hc hcap)
  simp only [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one,
    Matrix.trace_sub, Matrix.trace_smul, Complex.sub_re,
    Complex.smul_re, smul_eq_mul] at h
  linarith

def normalizedDoubleCrop (P Q R : Matrix I I ℂ) : Matrix I I ℂ :=
  if 0 < (doubleCrop P Q R).trace.re then
    Corollaries.positiveNormalize (doubleCrop P Q R) else R

theorem normalizedDoubleCrop_isDensity {P Q R : Matrix I I ℂ} (hR : IsDensity R) :
    IsDensity (normalizedDoubleCrop P Q R) := by
  unfold normalizedDoubleCrop
  split_ifs with ht
  · exact Corollaries.positiveNormalize_isDensity (doubleCrop_posSemidef P Q hR.1) ht
  · exact hR

theorem normalizedDoubleCrop_error_le {P Q R : Matrix I I ℂ}
    (hR : IsDensity R) (hP : IsProjection P) (hQ : IsProjection Q) :
    traceNorm (R - normalizedDoubleCrop P Q R) ≤ 2 * traceNorm (R - doubleCrop P Q R) := by
  unfold normalizedDoubleCrop
  split_ifs with ht
  · exact Corollaries.positiveNormalize_traceNorm_le hR
      (doubleCrop_posSemidef P Q hR.1) ht
      (by simpa only [hR.2, Complex.one_re] using doubleCrop_trace_le hP hQ hR.1)
  · simpa only [sub_self, EffectPerturbation.traceNorm, CFC.abs_zero,
      Matrix.trace_zero, Complex.zero_re] using
      mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (EffectPerturbation.traceNorm_nonneg _)

theorem normalizedDoubleCrop_cap {P Q R S : Matrix I I ℂ}
    (ht : 0 < (doubleCrop P Q R).trace.re) {c : ℝ}
    (hcap : (c • S - doubleCrop P Q R).PosSemidef) :
    ((c / (doubleCrop P Q R).trace.re) • S - normalizedDoubleCrop P Q R).PosSemidef := by
  rw [normalizedDoubleCrop, if_pos ht]
  have h := hcap.smul (inv_nonneg.mpr ht.le)
  convert h using 1
  simp only [Corollaries.positiveNormalize, smul_sub, smul_smul, div_eq_mul_inv]
  rw [mul_comm]

theorem marginalProjection_isProjection {Q : Matrix Y Y ℂ} (hQ : IsProjection Q) :
    IsProjection ((1 : Matrix X X ℂ) ⊗ₖ Q) := by
  refine ⟨?_, ?_⟩
  · simp only [Matrix.IsHermitian, Matrix.conjTranspose_kronecker,
      Matrix.conjTranspose_one, hQ.selfAdjoint.eq]
  rw [← Matrix.mul_kronecker_mul, Matrix.one_mul, hQ.idempotent]

theorem bipartite_doubleCrop_conditional_cap
    {P R : Matrix (X × Y) (X × Y) ℂ} {Q S : Matrix Y Y ℂ}
    (hQ : IsProjection Q) {c d : ℝ} (hc : 0 ≤ c) (hd : 0 < d)
    (hcap : (c • (1 : Matrix (X × Y) (X × Y) ℂ) - cropMap P R).PosSemidef)
    (hlower : (S - d • Q).PosSemidef) :
    ((c / d) • ((1 : Matrix X X ℂ) ⊗ₖ S) -
      doubleCrop P ((1 : Matrix X X ℂ) ⊗ₖ Q) R).PosSemidef := by
  apply doubleCrop_conditional_cap (marginalProjection_isProjection hQ) hc hd hcap
  have h := (Matrix.PosSemidef.one (n := X) (R := ℂ)).kronecker hlower
  convert h using 1
  ext i j
  simp only [Matrix.sub_apply, Matrix.kroneckerMap_apply, Matrix.kronecker_apply, Matrix.smul_apply,
    smul_eq_mul, Complex.real_smul]
  ring

theorem localProjection_isProjection {U : Matrix X X ℂ} {V : Matrix Y Y ℂ}
    (hU : IsProjection U) (hV : IsProjection V) : IsProjection (U ⊗ₖ V) := by
  constructor
  · simp only [Matrix.IsHermitian, Matrix.conjTranspose_kronecker,
      hU.selfAdjoint.eq, hV.selfAdjoint.eq]
  · rw [← Matrix.mul_kronecker_mul, hU.idempotent, hV.idempotent]

def tripleCrop (U : Matrix X X ℂ) (P : Matrix (X × Y) (X × Y) ℂ)
    (V : Matrix Y Y ℂ) (R : Matrix (X × Y) (X × Y) ℂ) : Matrix (X × Y) (X × Y) ℂ :=
  doubleCrop P (U ⊗ₖ V) R

theorem localProjection_acceptance_union
    {R : Matrix (X × Y) (X × Y) ℂ} {U : Matrix X X ℂ} {V : Matrix Y Y ℂ}
    (hR : IsDensity R) (hU : IsProjection U) (hV : IsProjection V) :
    1 - (R * (U ⊗ₖ V)).trace.re ≤
      (1 - (R * (U ⊗ₖ (1 : Matrix Y Y ℂ))).trace.re) +
        (1 - (R * ((1 : Matrix X X ℂ) ⊗ₖ V)).trace.re) := by
  have h := trace_mul_re_nonneg hR.1 (hU.complement.posSemidef.kronecker hV.complement.posSemidef)
  have he : (1 - U) ⊗ₖ (1 - V) =
      (1 : Matrix (X × Y) (X × Y) ℂ) - U ⊗ₖ (1 : Matrix Y Y ℂ) -
        (1 : Matrix X X ℂ) ⊗ₖ V + U ⊗ₖ V := by
    rw [← Matrix.one_kronecker_one]
    ext i j
    simp only [Matrix.kroneckerMap_apply, Matrix.kronecker_apply, Matrix.sub_apply, Matrix.add_apply]
    ring
  rw [he] at h
  simp only [Matrix.mul_add, Matrix.mul_sub, Matrix.mul_one,
    Matrix.trace_add, Matrix.trace_sub, Complex.add_re, Complex.sub_re,
    hR.2, Complex.one_re] at h
  linarith

theorem tripleCrop_gentle
    {R P : Matrix (X × Y) (X × Y) ℂ} {U : Matrix X X ℂ} {V : Matrix Y Y ℂ}
    (hR : IsDensity R) (hP : IsProjection P) (hU : IsProjection U) (hV : IsProjection V) :
    traceNorm (R - tripleCrop U P V R) ≤
      2 * Real.sqrt (1 - (R * P).trace.re) +
        2 * Real.sqrt ((1 - (R * (U ⊗ₖ (1 : Matrix Y Y ℂ))).trace.re) +
          (1 - (R * ((1 : Matrix X X ℂ) ⊗ₖ V)).trace.re)) := by
  exact (doubleCrop_gentle hR hP (localProjection_isProjection hU hV)).trans
    (add_le_add le_rfl (mul_le_mul_of_nonneg_left
      (Real.sqrt_le_sqrt (localProjection_acceptance_union hR hU hV)) (show (0 : ℝ) ≤ 2 by norm_num)))

theorem tripleCrop_conditional_cap
    {P R : Matrix (X × Y) (X × Y) ℂ} {U : Matrix X X ℂ} {V S : Matrix Y Y ℂ}
    (hU : IsProjection U) (hV : IsProjection V) {c d : ℝ} (hc : 0 ≤ c) (hd : 0 < d)
    (hcap : (c • (1 : Matrix (X × Y) (X × Y) ℂ) - cropMap P R).PosSemidef)
    (hlower : (S - d • V).PosSemidef) :
    ((c / d) • ((1 : Matrix X X ℂ) ⊗ₖ S) - tripleCrop U P V R).PosSemidef := by
  apply doubleCrop_conditional_cap (localProjection_isProjection hU hV) hc hd hcap
  have h := ((Matrix.PosSemidef.one (n := X) (R := ℂ)).kronecker hlower).add
    ((hU.complement.posSemidef.kronecker hV.posSemidef).smul hd.le)
  convert h using 1
  ext i j
  simp only [Matrix.kroneckerMap_apply, Matrix.kronecker_apply, Matrix.sub_apply, Matrix.add_apply,
    Matrix.smul_apply, smul_eq_mul, Complex.real_smul]
  ring

theorem tripleCrop_local_support
    {P R : Matrix (X × Y) (X × Y) ℂ} {U : Matrix X X ℂ} {V : Matrix Y Y ℂ}
    (hU : IsProjection U) (hV : IsProjection V) :
    (U ⊗ₖ (1 : Matrix Y Y ℂ)) * tripleCrop U P V R = tripleCrop U P V R ∧
      tripleCrop U P V R * ((1 : Matrix X X ℂ) ⊗ₖ V) = tripleCrop U P V R := by
  have hL : (U ⊗ₖ (1 : Matrix Y Y ℂ)) * (U ⊗ₖ V) = U ⊗ₖ V := by
    rw [← Matrix.mul_kronecker_mul, hU.idempotent, Matrix.one_mul]
  have hR : (U ⊗ₖ V) * ((1 : Matrix X X ℂ) ⊗ₖ V) = U ⊗ₖ V := by
    rw [← Matrix.mul_kronecker_mul, Matrix.mul_one, hV.idempotent]
  simp only [tripleCrop, doubleCrop, cropMap_apply,
    (localProjection_isProjection hU hV).selfAdjoint.eq]
  constructor
  · simp only [← Matrix.mul_assoc, hL]
  · simp only [Matrix.mul_assoc, hR]

theorem partialTrace_left_mul_local (R : Matrix (X × Y) (X × Y) ℂ) (V : Matrix Y Y ℂ) :
    QuantumProver.QuantumEntropy.partialTrace_left (R * ((1 : Matrix X X ℂ) ⊗ₖ V)) =
      QuantumProver.QuantumEntropy.partialTrace_left R * V := by
  ext y y'
  simp only [QuantumProver.QuantumEntropy.partialTrace_left, Matrix.mul_apply,
    Fintype.sum_prod_type, Matrix.kroneckerMap_apply, Matrix.kronecker_apply, Matrix.one_apply]
  simp only [ite_mul, mul_ite, one_mul, mul_one, zero_mul, mul_zero, Finset.sum_ite_irrel,
    Finset.sum_const_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [Finset.sum_comm]
  simp only [Finset.sum_mul]

theorem tripleCrop_marginal_supported
    {P R : Matrix (X × Y) (X × Y) ℂ} {U : Matrix X X ℂ} {V : Matrix Y Y ℂ}
    (hU : IsProjection U) (hV : IsProjection V) :
    QuantumProver.QuantumEntropy.partialTrace_left (tripleCrop U P V R) * V =
      QuantumProver.QuantumEntropy.partialTrace_left (tripleCrop U P V R) := by
  rw [← partialTrace_left_mul_local, (tripleCrop_local_support hU hV).2]

theorem tripleCrop_marginal_rank_le
    {P R : Matrix (X × Y) (X × Y) ℂ} {U : Matrix X X ℂ} {V : Matrix Y Y ℂ}
    (hU : IsProjection U) (hV : IsProjection V) :
    Matrix.rank (QuantumProver.QuantumEntropy.partialTrace_left (tripleCrop U P V R)) ≤ Matrix.rank V := by
  rw [← tripleCrop_marginal_supported hU hV]
  exact Matrix.rank_mul_le_right _ _

section Limits

variable {J : ℕ → Type*} [∀ n, Fintype (J n)] [∀ n, DecidableEq (J n)]

theorem doubleCrop_error_tendsto_zero
    (R P Q : (n : ℕ) → Matrix (J n) (J n) ℂ)
    (hR : ∀ n, IsDensity (R n)) (hP : ∀ n, IsProjection (P n))
    (hQ : ∀ n, IsProjection (Q n))
    (hp : Tendsto (fun n => (R n * P n).trace.re) atTop (𝓝 1))
    (hq : Tendsto (fun n => (R n * Q n).trace.re) atTop (𝓝 1)) :
    Tendsto (fun n => traceNorm (R n - doubleCrop (P n) (Q n) (R n))) atTop (𝓝 0) := by
  have hp0 : Tendsto (fun n => 1 - (R n * P n).trace.re) atTop (𝓝 0) := by
    simpa only [sub_self] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub hp
  have hq0 : Tendsto (fun n => 1 - (R n * Q n).trace.re) atTop (𝓝 0) := by
    simpa only [sub_self] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub hq
  have hps := Real.continuous_sqrt.continuousAt.tendsto.comp hp0
  have hqs := Real.continuous_sqrt.continuousAt.tendsto.comp hq0
  have hlim : Tendsto (fun n =>
      2 * Real.sqrt (1 - (R n * P n).trace.re) +
        2 * Real.sqrt (1 - (R n * Q n).trace.re)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.sqrt_zero, mul_zero, add_zero] using
      (hps.const_mul 2).add (hqs.const_mul 2)
  exact squeeze_zero (fun n => EffectPerturbation.traceNorm_nonneg _)
    (fun n => doubleCrop_gentle (hR n) (hP n) (hQ n)) hlim

theorem doubleCrop_trace_tendsto_one
    (R P Q : (n : ℕ) → Matrix (J n) (J n) ℂ)
    (hR : ∀ n, IsDensity (R n)) (hP : ∀ n, IsProjection (P n))
    (hQ : ∀ n, IsProjection (Q n))
    (hp : Tendsto (fun n => (R n * P n).trace.re) atTop (𝓝 1))
    (hq : Tendsto (fun n => (R n * Q n).trace.re) atTop (𝓝 1)) :
    Tendsto (fun n => (doubleCrop (P n) (Q n) (R n)).trace.re) atTop (𝓝 1) := by
  have hlim := doubleCrop_error_tendsto_zero R P Q hR hP hQ hp hq
  have hmass (n : ℕ) : |(doubleCrop (P n) (Q n) (R n)).trace.re - 1| ≤
      traceNorm (R n - doubleCrop (P n) (Q n) (R n)) := by
    have h := EffectPerturbation.effectValue_abs_le_traceNorm
      (show IsEffect (1 : Matrix (J n) (J n) ℂ) from
        ⟨Matrix.PosSemidef.one, by simp only [sub_self]; exact Matrix.PosSemidef.zero⟩)
      ((hR n).1.1.sub (doubleCrop_posSemidef (P n) (Q n) (hR n).1).1)
    simpa only [EffectPerturbation.effectValue, Matrix.one_mul,
      Matrix.trace_sub, (hR n).2, Complex.sub_re, Complex.one_re, abs_sub_comm] using h
  apply (tendsto_iff_norm_sub_tendsto_zero).mpr
  exact squeeze_zero (fun n => norm_nonneg _) (fun n => by
    simpa only [Real.norm_eq_abs] using hmass n) hlim

theorem normalizedDoubleCrop_error_tendsto_zero
    (R P Q : (n : ℕ) → Matrix (J n) (J n) ℂ)
    (hR : ∀ n, IsDensity (R n)) (hP : ∀ n, IsProjection (P n))
    (hQ : ∀ n, IsProjection (Q n))
    (hp : Tendsto (fun n => (R n * P n).trace.re) atTop (𝓝 1))
    (hq : Tendsto (fun n => (R n * Q n).trace.re) atTop (𝓝 1)) :
    Tendsto (fun n => traceNorm (R n - normalizedDoubleCrop (P n) (Q n) (R n)))
      atTop (𝓝 0) := by
  have hlim : Tendsto (fun n => 2 * traceNorm (R n - doubleCrop (P n) (Q n) (R n)))
      atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (doubleCrop_error_tendsto_zero R P Q hR hP hQ hp hq).const_mul 2
  exact squeeze_zero (fun n => EffectPerturbation.traceNorm_nonneg _)
    (fun n => normalizedDoubleCrop_error_le (hR n) (hP n) (hQ n)) hlim

end Limits

open QuantumProver.QuantumTypicalProjectors
open TensorEntropy

def powerGrouping (A B : Type*) : (n : ℕ) →
    TensorIndex (A × B) n ≃ TensorIndex A n × TensorIndex B n
  | 0 => {
      toFun := fun _ => (PUnit.unit, PUnit.unit)
      invFun := fun _ => PUnit.unit
      left_inv := by intro x; cases x; rfl
      right_inv := by rintro ⟨x,y⟩; cases x; cases y; rfl }
  | n + 1 => (Equiv.prodCongr (powerGrouping A B n) (Equiv.refl (A × B))).trans
      (Equiv.prodProdProdComm (TensorIndex A n) (TensorIndex B n) A B)

def groupedPower (R : Matrix (X × Y) (X × Y) ℂ) (n : ℕ) :
    Matrix (TensorIndex X n × TensorIndex Y n) (TensorIndex X n × TensorIndex Y n) ℂ :=
  Matrix.reindex (powerGrouping X Y n) (powerGrouping X Y n) (tensorPower R n)

theorem groupedPower_isDensity {R : Matrix (X × Y) (X × Y) ℂ}
    (hR : IsDensity R) (n : ℕ) : IsDensity (groupedPower R n) :=
  ⟨(tensorPower_isDensity hR n).1.submatrix (powerGrouping X Y n).symm,
    (QuantumProver.QuantumEntropy.trace_reindex (powerGrouping X Y n) _).trans
      (tensorPower_isDensity hR n).2⟩

theorem groupedPower_succ_apply (R : Matrix (X × Y) (X × Y) ℂ) (n : ℕ)
    (x x' : TensorIndex X n) (y y' : TensorIndex Y n) (i i' : X) (j j' : Y) :
    groupedPower R (n + 1) ((x,i),(y,j)) ((x',i'),(y',j')) =
      groupedPower R n (x,y) (x',y') * R (i,j) (i',j') := rfl

theorem groupedPower_left_marginal (R : Matrix (X × Y) (X × Y) ℂ) (n : ℕ) :
    QuantumProver.QuantumEntropy.partialTrace_left (groupedPower R n) =
      tensorPower (QuantumProver.QuantumEntropy.partialTrace_left R) n := by
  induction n with
  | zero =>
      ext y y'
      cases y
      cases y'
      simp [QuantumProver.QuantumEntropy.partialTrace_left, groupedPower, powerGrouping,
        tensorPower, Matrix.reindex_apply, Matrix.one_apply]
  | succ n ih =>
      ext yy yy'
      rcases yy with ⟨y,j⟩
      rcases yy' with ⟨y',j'⟩
      change (∑ x : TensorIndex X n × X,
        groupedPower R (n + 1) (x,(y,j)) (x,(y',j'))) =
          tensorPower (QuantumProver.QuantumEntropy.partialTrace_left R) n y y' *
            QuantumProver.QuantumEntropy.partialTrace_left R j j'
      simp only [Fintype.sum_prod_type, groupedPower_succ_apply,
        ← Finset.mul_sum, ← Finset.sum_mul]
      change QuantumProver.QuantumEntropy.partialTrace_left (groupedPower R n) y y' *
        QuantumProver.QuantumEntropy.partialTrace_left R j j' = _
      rw [ih]

theorem groupedPower_right_marginal (R : Matrix (X × Y) (X × Y) ℂ) (n : ℕ) :
    QuantumProver.QuantumEntropy.partialTrace_right (groupedPower R n) =
      tensorPower (QuantumProver.QuantumEntropy.partialTrace_right R) n := by
  induction n with
  | zero =>
      ext x x'
      cases x
      cases x'
      simp [QuantumProver.QuantumEntropy.partialTrace_right, groupedPower, powerGrouping,
        tensorPower, Matrix.reindex_apply, Matrix.one_apply]
  | succ n ih =>
      ext xx xx'
      rcases xx with ⟨x,i⟩
      rcases xx' with ⟨x',i'⟩
      change (∑ y : TensorIndex Y n × Y,
        groupedPower R (n + 1) ((x,i),y) ((x',i'),y)) =
          tensorPower (QuantumProver.QuantumEntropy.partialTrace_right R) n x x' *
            QuantumProver.QuantumEntropy.partialTrace_right R i i'
      simp only [Fintype.sum_prod_type, groupedPower_succ_apply,
        ← Finset.mul_sum, ← Finset.sum_mul]
      change QuantumProver.QuantumEntropy.partialTrace_right (groupedPower R n) x x' *
        QuantumProver.QuantumEntropy.partialTrace_right R i i' = _
      rw [ih]

theorem reindex_cropMap {A B : Type*} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] (e : A ≃ B) (P R : Matrix A A ℂ) :
    Matrix.reindex e e (cropMap P R) =
      cropMap (Matrix.reindex e e P) (Matrix.reindex e e R) := by
  simp only [cropMap_apply, Matrix.reindex_apply, Matrix.submatrix_mul_equiv,
    Matrix.conjTranspose_submatrix]

def jointTypical {R : Matrix (X × Y) (X × Y) ℂ}
    (hR : IsDensity R) (δ : ℝ) (n : ℕ) :
    Matrix (TensorIndex X n × TensorIndex Y n) (TensorIndex X n × TensorIndex Y n) ℂ :=
  Matrix.reindex (powerGrouping X Y n) (powerGrouping X Y n) (typicalProjector hR δ n)

def senderTypical {R : Matrix (X × Y) (X × Y) ℂ}
    (hR : IsDensity R) (δ : ℝ) (n : ℕ) : Matrix (TensorIndex X n) (TensorIndex X n) ℂ :=
  typicalProjector (QuantumProver.QuantumEntropy.partialTraceRight_isDensity hR) δ n

def referenceTypical {R : Matrix (X × Y) (X × Y) ℂ}
    (hR : IsDensity R) (δ : ℝ) (n : ℕ) : Matrix (TensorIndex Y n) (TensorIndex Y n) ℂ :=
  typicalProjector (QuantumProver.QuantumEntropy.partialTraceLeft_isDensity hR) δ n

def iidRawProxy {R : Matrix (X × Y) (X × Y) ℂ}
    (hR : IsDensity R) (δ : ℝ) (n : ℕ) :
    Matrix (TensorIndex X n × TensorIndex Y n) (TensorIndex X n × TensorIndex Y n) ℂ :=
  tripleCrop (senderTypical hR δ n) (jointTypical hR δ n)
    (referenceTypical hR δ n) (groupedPower R n)

def iidProxy {R : Matrix (X × Y) (X × Y) ℂ}
    (hR : IsDensity R) (δ : ℝ) (n : ℕ) :
    Matrix (TensorIndex X n × TensorIndex Y n) (TensorIndex X n × TensorIndex Y n) ℂ :=
  normalizedDoubleCrop (jointTypical hR δ n)
    (senderTypical hR δ n ⊗ₖ referenceTypical hR δ n) (groupedPower R n)

theorem jointTypical_isProjection {R : Matrix (X × Y) (X × Y) ℂ}
    (hR : IsDensity R) (δ : ℝ) (n : ℕ) : IsProjection (jointTypical hR δ n) := by
  have h := typicalProjector_isProjection hR δ n
  let F := Matrix.reindexRingEquiv ℂ (powerGrouping X Y n)
  constructor
  · exact h.selfAdjoint.submatrix (powerGrouping X Y n).symm
  · change F (typicalProjector hR δ n) * F (typicalProjector hR δ n) =
      F (typicalProjector hR δ n)
    rw [← map_mul, h.idempotent]

theorem jointTypical_acceptance_tendsto_one {R : Matrix (X × Y) (X × Y) ℂ}
    (hR : IsDensity R) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun n => (groupedPower R n * jointTypical hR δ n).trace.re) atTop (𝓝 1) := by
  have he (n : ℕ) : (groupedPower R n * jointTypical hR δ n).trace =
      (tensorPower R n * typicalProjector hR δ n).trace := by
    let F := Matrix.reindexRingEquiv ℂ (powerGrouping X Y n)
    change (F (tensorPower R n) * F (typicalProjector hR δ n)).trace = _
    rw [← (Matrix.reindexRingEquiv ℂ (powerGrouping X Y n)).map_mul]
    exact QuantumProver.QuantumEntropy.trace_reindex _ _
  simpa only [he] using typicalProjector_acceptance_tendsto_one hR hδ

theorem senderTypical_acceptance_tendsto_one {R : Matrix (X × Y) (X × Y) ℂ}
    (hR : IsDensity R) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun n => (groupedPower R n *
      (senderTypical hR δ n ⊗ₖ (1 : Matrix (TensorIndex Y n) (TensorIndex Y n) ℂ))).trace.re)
        atTop (𝓝 1) := by
  simp_rw [QuantumProver.QuantumEntropy.partialTrace_right_mul_trace, groupedPower_right_marginal]
  exact typicalProjector_acceptance_tendsto_one
    (QuantumProver.QuantumEntropy.partialTraceRight_isDensity hR) hδ

theorem referenceTypical_acceptance_tendsto_one {R : Matrix (X × Y) (X × Y) ℂ}
    (hR : IsDensity R) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun n => (groupedPower R n *
      ((1 : Matrix (TensorIndex X n) (TensorIndex X n) ℂ) ⊗ₖ referenceTypical hR δ n)).trace.re)
        atTop (𝓝 1) := by
  simp_rw [QuantumProver.QuantumEntropy.partialTrace_left_mul_trace, groupedPower_left_marginal]
  exact typicalProjector_acceptance_tendsto_one
    (QuantumProver.QuantumEntropy.partialTraceLeft_isDensity hR) hδ

theorem jointTypical_crop_upper_identity {R : Matrix (X × Y) (X × Y) ℂ}
    (hR : IsDensity R) (δ : ℝ) (n : ℕ) :
    (Real.exp (-(n : ℝ) * (QuantumProver.QuantumEntropy.entropyNats R - δ)) •
      (1 : Matrix (TensorIndex X n × TensorIndex Y n) (TensorIndex X n × TensorIndex Y n) ℂ) -
        cropMap (jointTypical hR δ n) (groupedPower R n)).PosSemidef := by
  let F := Matrix.reindexRingEquiv ℂ (powerGrouping X Y n)
  have hp := typicalProjector_isProjection hR δ n
  have h := typicalProjector_crop_upper_identity hR δ n
  change (Real.exp (-(n : ℝ) * (QuantumProver.QuantumEntropy.entropyNats R - δ)) • 1 -
    cropMap (F (typicalProjector hR δ n)) (F (tensorPower R n))).PosSemidef
  have hf : F (cropMap (typicalProjector hR δ n) (tensorPower R n)) =
      cropMap (F (typicalProjector hR δ n)) (F (tensorPower R n)) :=
    reindex_cropMap (powerGrouping X Y n) _ _
  rw [← hf]
  have hs : Real.exp (-(n : ℝ) * (QuantumProver.QuantumEntropy.entropyNats R - δ)) • (1 : Matrix _ _ ℂ) =
      F (Real.exp (-(n : ℝ) * (QuantumProver.QuantumEntropy.entropyNats R - δ)) • (1 : Matrix _ _ ℂ)) := by
    rw [show F (Real.exp (-(n : ℝ) * (QuantumProver.QuantumEntropy.entropyNats R - δ)) • 1) =
      Real.exp (-(n : ℝ) * (QuantumProver.QuantumEntropy.entropyNats R - δ)) • F 1 from rfl, map_one]
  rw [hs, ← map_sub]
  exact (show (Real.exp (-(n : ℝ) * (QuantumProver.QuantumEntropy.entropyNats R - δ)) • 1 -
    cropMap (typicalProjector hR δ n) (tensorPower R n)).PosSemidef from
      by simpa only [cropMap_apply, hp.selfAdjoint.eq] using h).submatrix (powerGrouping X Y n).symm

theorem iidRawProxy_purity_le {R : Matrix (X × Y) (X × Y) ℂ}
    (hR : IsDensity R) (δ : ℝ) (n : ℕ) :
    (iidRawProxy hR δ n * iidRawProxy hR δ n).trace.re ≤
      Real.exp (-(n : ℝ) * (QuantumProver.QuantumEntropy.entropyNats R - δ)) *
        (iidRawProxy hR δ n).trace.re :=
  doubleCrop_purity_le (groupedPower_isDensity hR n).1
    (localProjection_isProjection
      (typicalProjector_isProjection (QuantumProver.QuantumEntropy.partialTraceRight_isDensity hR) δ n)
      (typicalProjector_isProjection (QuantumProver.QuantumEntropy.partialTraceLeft_isDensity hR) δ n))
    (Real.exp_nonneg _) (jointTypical_crop_upper_identity hR δ n)

theorem iidRawProxy_conditional_cap {R : Matrix (X × Y) (X × Y) ℂ}
    (hR : IsDensity R) (δ : ℝ) (n : ℕ) :
    (Real.exp (-(n : ℝ) * (QuantumProver.QuantumEntropy.entropyNats R -
      QuantumProver.QuantumEntropy.entropyNats (QuantumProver.QuantumEntropy.partialTrace_left R) - 2 * δ)) •
      ((1 : Matrix (TensorIndex X n) (TensorIndex X n) ℂ) ⊗ₖ
        tensorPower (QuantumProver.QuantumEntropy.partialTrace_left R) n) - iidRawProxy hR δ n).PosSemidef := by
  have h := tripleCrop_conditional_cap
    (typicalProjector_isProjection (QuantumProver.QuantumEntropy.partialTraceRight_isDensity hR) δ n)
    (typicalProjector_isProjection (QuantumProver.QuantumEntropy.partialTraceLeft_isDensity hR) δ n)
    (Real.exp_nonneg _) (Real.exp_pos _) (jointTypical_crop_upper_identity hR δ n)
    (typicalProjector_global_lower (QuantumProver.QuantumEntropy.partialTraceLeft_isDensity hR) δ n)
  have he : Real.exp (-(n : ℝ) * (QuantumProver.QuantumEntropy.entropyNats R - δ)) /
      Real.exp (-(n : ℝ) * (QuantumProver.QuantumEntropy.entropyNats (QuantumProver.QuantumEntropy.partialTrace_left R) + δ)) =
      Real.exp (-(n : ℝ) * (QuantumProver.QuantumEntropy.entropyNats R -
        QuantumProver.QuantumEntropy.entropyNats (QuantumProver.QuantumEntropy.partialTrace_left R) - 2 * δ)) := by
    rw [← Real.exp_sub]
    congr 1
    ring
  simpa only [he, iidRawProxy, senderTypical, referenceTypical] using h

section LocalLimits

variable {A B : ℕ → Type*} [∀ n, Fintype (A n)] [∀ n, DecidableEq (A n)]
  [∀ n, Fintype (B n)] [∀ n, DecidableEq (B n)]

theorem localProjection_acceptance_tendsto_one
    (R : (n : ℕ) → Matrix (A n × B n) (A n × B n) ℂ)
    (U : (n : ℕ) → Matrix (A n) (A n) ℂ) (V : (n : ℕ) → Matrix (B n) (B n) ℂ)
    (hR : ∀ n, IsDensity (R n)) (hU : ∀ n, IsProjection (U n)) (hV : ∀ n, IsProjection (V n))
    (hu : Tendsto (fun n => (R n * (U n ⊗ₖ (1 : Matrix (B n) (B n) ℂ))).trace.re) atTop (𝓝 1))
    (hv : Tendsto (fun n => (R n * ((1 : Matrix (A n) (A n) ℂ) ⊗ₖ V n)).trace.re) atTop (𝓝 1)) :
    Tendsto (fun n => (R n * (U n ⊗ₖ V n)).trace.re) atTop (𝓝 1) := by
  have hu0 := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub hu
  have hv0 := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub hv
  have hlim : Tendsto (fun n =>
      (1 - (R n * (U n ⊗ₖ (1 : Matrix (B n) (B n) ℂ))).trace.re) +
        (1 - (R n * ((1 : Matrix (A n) (A n) ℂ) ⊗ₖ V n)).trace.re)) atTop (𝓝 0) := by
    simpa only [sub_self, add_zero] using hu0.add hv0
  have hbad : Tendsto (fun n => 1 - (R n * (U n ⊗ₖ V n)).trace.re) atTop (𝓝 0) := by
    apply squeeze_zero _ (fun n => localProjection_acceptance_union (hR n) (hU n) (hV n)) hlim
    intro n
    have h := trace_mul_re_nonneg (hR n).1 (localProjection_isProjection (hU n) (hV n)).complement.posSemidef
    simpa only [Matrix.mul_sub, Matrix.mul_one, Matrix.trace_sub, Complex.sub_re,
      (hR n).2, Complex.one_re] using h
  simpa only [sub_sub_cancel, sub_zero] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub hbad

end LocalLimits

theorem iidLocal_acceptance_tendsto_one {R : Matrix (X × Y) (X × Y) ℂ}
    (hR : IsDensity R) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun n => (groupedPower R n *
      (senderTypical hR δ n ⊗ₖ referenceTypical hR δ n)).trace.re) atTop (𝓝 1) :=
  localProjection_acceptance_tendsto_one (groupedPower R) (senderTypical hR δ) (referenceTypical hR δ)
    (groupedPower_isDensity hR)
    (typicalProjector_isProjection (QuantumProver.QuantumEntropy.partialTraceRight_isDensity hR) δ)
    (typicalProjector_isProjection (QuantumProver.QuantumEntropy.partialTraceLeft_isDensity hR) δ)
    (senderTypical_acceptance_tendsto_one hR hδ) (referenceTypical_acceptance_tendsto_one hR hδ)

theorem iidRawProxy_trace_tendsto_one {R : Matrix (X × Y) (X × Y) ℂ}
    (hR : IsDensity R) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun n => (iidRawProxy hR δ n).trace.re) atTop (𝓝 1) :=
  doubleCrop_trace_tendsto_one (groupedPower R) (jointTypical hR δ)
    (fun n => senderTypical hR δ n ⊗ₖ referenceTypical hR δ n) (groupedPower_isDensity hR)
    (jointTypical_isProjection hR δ)
    (fun n => localProjection_isProjection
      (typicalProjector_isProjection (QuantumProver.QuantumEntropy.partialTraceRight_isDensity hR) δ n)
      (typicalProjector_isProjection (QuantumProver.QuantumEntropy.partialTraceLeft_isDensity hR) δ n))
    (jointTypical_acceptance_tendsto_one hR hδ) (iidLocal_acceptance_tendsto_one hR hδ)

theorem iidProxy_isDensity {R : Matrix (X × Y) (X × Y) ℂ}
    (hR : IsDensity R) (δ : ℝ) (n : ℕ) : IsDensity (iidProxy hR δ n) :=
  normalizedDoubleCrop_isDensity (groupedPower_isDensity hR n)

theorem iidProxy_error_tendsto_zero {R : Matrix (X × Y) (X × Y) ℂ}
    (hR : IsDensity R) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun n => traceNorm (groupedPower R n - iidProxy hR δ n)) atTop (𝓝 0) :=
  normalizedDoubleCrop_error_tendsto_zero (groupedPower R) (jointTypical hR δ)
    (fun n => senderTypical hR δ n ⊗ₖ referenceTypical hR δ n) (groupedPower_isDensity hR)
    (jointTypical_isProjection hR δ)
    (fun n => localProjection_isProjection
      (typicalProjector_isProjection (QuantumProver.QuantumEntropy.partialTraceRight_isDensity hR) δ n)
      (typicalProjector_isProjection (QuantumProver.QuantumEntropy.partialTraceLeft_isDensity hR) δ n))
    (jointTypical_acceptance_tendsto_one hR hδ) (iidLocal_acceptance_tendsto_one hR hδ)

theorem mass_inverse_eventually_le_exp (m : ℕ → ℝ)
    (hm : Tendsto m atTop (𝓝 1)) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, 0 < m n ∧ (m n)⁻¹ ≤ Real.exp ((n : ℝ) * δ) := by
  have hmhalf := hm.eventually (eventually_gt_nhds (by norm_num : (1 / 2 : ℝ) < 1))
  have hexp : Tendsto (fun n : ℕ => Real.exp ((n : ℝ) * δ)) atTop atTop :=
    Real.tendsto_exp_atTop.comp (Filter.Tendsto.atTop_mul_const hδ tendsto_natCast_atTop_atTop)
  filter_upwards [hmhalf, hexp.eventually (eventually_ge_atTop (2 : ℝ))] with n hn he
  have hp : 0 < m n := by linarith
  refine ⟨hp, (le_trans ?_ he)⟩
  exact (inv_le_iff_one_le_mul₀ hp).mpr (by linarith)

theorem iidProxy_support_of_mass_pos {R : Matrix (X × Y) (X × Y) ℂ}
    (hR : IsDensity R) (δ : ℝ) (n : ℕ) (ht : 0 < (iidRawProxy hR δ n).trace.re) :
    (senderTypical hR δ n ⊗ₖ (1 : Matrix (TensorIndex Y n) (TensorIndex Y n) ℂ)) * iidProxy hR δ n =
      iidProxy hR δ n ∧
    iidProxy hR δ n * ((1 : Matrix (TensorIndex X n) (TensorIndex X n) ℂ) ⊗ₖ referenceTypical hR δ n) =
      iidProxy hR δ n := by
  have hs := tripleCrop_local_support
    (typicalProjector_isProjection (QuantumProver.QuantumEntropy.partialTraceRight_isDensity hR) δ n)
    (typicalProjector_isProjection (QuantumProver.QuantumEntropy.partialTraceLeft_isDensity hR) δ n)
    (P := jointTypical hR δ n) (R := groupedPower R n)
  change (senderTypical hR δ n ⊗ₖ (1 : Matrix (TensorIndex Y n) (TensorIndex Y n) ℂ)) * iidRawProxy hR δ n =
      iidRawProxy hR δ n ∧
    iidRawProxy hR δ n * ((1 : Matrix (TensorIndex X n) (TensorIndex X n) ℂ) ⊗ₖ referenceTypical hR δ n) =
      iidRawProxy hR δ n at hs
  have hn : iidProxy hR δ n = (iidRawProxy hR δ n).trace.re⁻¹ • iidRawProxy hR δ n := by
    unfold iidProxy normalizedDoubleCrop
    change (if 0 < (iidRawProxy hR δ n).trace.re then
      Corollaries.positiveNormalize (iidRawProxy hR δ n) else groupedPower R n) = _
    rw [ite_eq_left ht]
    rfl
  rw [hn]
  constructor
  · rw [Matrix.mul_smul, hs.1]
  · rw [Matrix.smul_mul, hs.2]

theorem iidProxy_reference_rank_le {R : Matrix (X × Y) (X × Y) ℂ}
    (hR : IsDensity R) (δ : ℝ) (n : ℕ) (ht : 0 < (iidRawProxy hR δ n).trace.re) :
    (Matrix.rank (QuantumProver.QuantumEntropy.partialTrace_left (iidProxy hR δ n)) : ℝ) ≤
      Real.exp ((n : ℝ) * (QuantumProver.QuantumEntropy.entropyNats (QuantumProver.QuantumEntropy.partialTrace_left R) + δ)) := by
  have hs : QuantumProver.QuantumEntropy.partialTrace_left (iidProxy hR δ n) * referenceTypical hR δ n =
      QuantumProver.QuantumEntropy.partialTrace_left (iidProxy hR δ n) := by
    rw [← partialTrace_left_mul_local, (iidProxy_support_of_mass_pos hR δ n ht).2]
  have hr : Matrix.rank (QuantumProver.QuantumEntropy.partialTrace_left (iidProxy hR δ n)) ≤
      Matrix.rank (referenceTypical hR δ n) := by
    rw [← hs]
    exact Matrix.rank_mul_le_right _ _
  have hrR : (Matrix.rank (QuantumProver.QuantumEntropy.partialTrace_left (iidProxy hR δ n)) : ℝ) ≤
      (Matrix.rank (referenceTypical hR δ n) : ℝ) := by exact_mod_cast hr
  exact hrR.trans
    (typicalProjector_rank_le_exp (QuantumProver.QuantumEntropy.partialTraceLeft_isDensity hR) δ n)

theorem iidProxy_purity_le_of_mass_pos {R : Matrix (X × Y) (X × Y) ℂ}
    (hR : IsDensity R) (δ : ℝ) (n : ℕ) (ht : 0 < (iidRawProxy hR δ n).trace.re) :
    (iidProxy hR δ n * iidProxy hR δ n).trace.re ≤
      Real.exp (-(n : ℝ) * (QuantumProver.QuantumEntropy.entropyNats R - δ)) /
        (iidRawProxy hR δ n).trace.re := by
  have hcap := normalizedDoubleCrop_cap
    (P := jointTypical hR δ n) (Q := senderTypical hR δ n ⊗ₖ referenceTypical hR δ n)
    (R := groupedPower R n) (S := 1) ht
    (doubleCrop_identity_cap
      (localProjection_isProjection
        (typicalProjector_isProjection (QuantumProver.QuantumEntropy.partialTraceRight_isDensity hR) δ n)
        (typicalProjector_isProjection (QuantumProver.QuantumEntropy.partialTraceLeft_isDensity hR) δ n))
      (Real.exp_nonneg _) (jointTypical_crop_upper_identity hR δ n))
  have h := trace_mul_re_nonneg (iidProxy_isDensity hR δ n).1 hcap
  change 0 ≤ (iidProxy hR δ n *
    ((Real.exp (-(n : ℝ) * (QuantumProver.QuantumEntropy.entropyNats R - δ)) /
      (iidRawProxy hR δ n).trace.re) • 1 - iidProxy hR δ n)).trace.re at h
  simp only [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one, Matrix.trace_sub,
    Matrix.trace_smul, Complex.sub_re, Complex.smul_re,
    (iidProxy_isDensity hR δ n).2, Complex.one_re, smul_eq_mul, mul_one] at h
  linarith

theorem iidProxy_eventual_purity {R : Matrix (X × Y) (X × Y) ℂ}
    (hR : IsDensity R) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop,
      (iidProxy hR δ n * iidProxy hR δ n).trace.re ≤
        Real.exp (-(n : ℝ) * (QuantumProver.QuantumEntropy.entropyNats R - 2 * δ)) := by
  filter_upwards [mass_inverse_eventually_le_exp _ (iidRawProxy_trace_tendsto_one hR hδ) hδ] with n hn
  refine (iidProxy_purity_le_of_mass_pos hR δ n hn.1).trans ?_
  rw [div_eq_mul_inv]
  calc
    _ ≤ Real.exp (-(n : ℝ) * (QuantumProver.QuantumEntropy.entropyNats R - δ)) *
        Real.exp ((n : ℝ) * δ) := mul_le_mul_of_nonneg_left hn.2 (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem iidProxy_eventual_conditional_cap {R : Matrix (X × Y) (X × Y) ℂ}
    (hR : IsDensity R) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop,
      (Real.exp (-(n : ℝ) * (QuantumProver.QuantumEntropy.entropyNats R -
        QuantumProver.QuantumEntropy.entropyNats (QuantumProver.QuantumEntropy.partialTrace_left R) - 3 * δ)) •
        ((1 : Matrix (TensorIndex X n) (TensorIndex X n) ℂ) ⊗ₖ
          tensorPower (QuantumProver.QuantumEntropy.partialTrace_left R) n) - iidProxy hR δ n).PosSemidef := by
  filter_upwards [mass_inverse_eventually_le_exp _ (iidRawProxy_trace_tendsto_one hR hδ) hδ] with n hn
  have h := normalizedDoubleCrop_cap
    (P := jointTypical hR δ n) (Q := senderTypical hR δ n ⊗ₖ referenceTypical hR δ n)
    (R := groupedPower R n) hn.1 (iidRawProxy_conditional_cap hR δ n)
  have hc : Real.exp (-(n : ℝ) * (QuantumProver.QuantumEntropy.entropyNats R -
      QuantumProver.QuantumEntropy.entropyNats (QuantumProver.QuantumEntropy.partialTrace_left R) - 2 * δ)) /
        (iidRawProxy hR δ n).trace.re ≤
      Real.exp (-(n : ℝ) * (QuantumProver.QuantumEntropy.entropyNats R -
        QuantumProver.QuantumEntropy.entropyNats (QuantumProver.QuantumEntropy.partialTrace_left R) - 3 * δ)) := by
    rw [div_eq_mul_inv]
    calc
      _ ≤ Real.exp (-(n : ℝ) * (QuantumProver.QuantumEntropy.entropyNats R -
          QuantumProver.QuantumEntropy.entropyNats (QuantumProver.QuantumEntropy.partialTrace_left R) - 2 * δ)) *
            Real.exp ((n : ℝ) * δ) := mul_le_mul_of_nonneg_left hn.2 (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hS := (Matrix.PosSemidef.one (n := TensorIndex X n) (R := ℂ)).kronecker
    (tensorPower_isDensity (QuantumProver.QuantumEntropy.partialTraceLeft_isDensity hR) n).1
  have hd := hS.smul (sub_nonneg.mpr hc)
  convert h.add hd using 1
  simp only [sub_smul, iidProxy, iidRawProxy, tripleCrop]
  abel

theorem iidProxy_eventual_rank_purity {R : Matrix (X × Y) (X × Y) ℂ}
    (hR : IsDensity R) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop,
      (Matrix.rank (QuantumProver.QuantumEntropy.partialTrace_left (iidProxy hR δ n)) : ℝ) *
        (iidProxy hR δ n * iidProxy hR δ n).trace.re ≤
      Real.exp (-(n : ℝ) * (QuantumProver.QuantumEntropy.entropyNats R -
        QuantumProver.QuantumEntropy.entropyNats (QuantumProver.QuantumEntropy.partialTrace_left R) - 3 * δ)) := by
  filter_upwards [mass_inverse_eventually_le_exp _ (iidRawProxy_trace_tendsto_one hR hδ) hδ,
    iidProxy_eventual_purity hR hδ] with n hn hp
  have hr := iidProxy_reference_rank_le hR δ n hn.1
  have hp0 := trace_mul_re_nonneg (iidProxy_isDensity hR δ n).1 (iidProxy_isDensity hR δ n).1
  calc
    _ ≤ Real.exp ((n : ℝ) * (QuantumProver.QuantumEntropy.entropyNats (QuantumProver.QuantumEntropy.partialTrace_left R) + δ)) *
        Real.exp (-(n : ℝ) * (QuantumProver.QuantumEntropy.entropyNats R - 2 * δ)) :=
      mul_le_mul hr hp hp0 (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem senderTypical_eq_of_common_marginal
    {Z : Type*} [Fintype Z] [DecidableEq Z]
    {R : Matrix (X × Y) (X × Y) ℂ} {S : Matrix (X × Z) (X × Z) ℂ}
    (hR : IsDensity R) (hS : IsDensity S)
    (hcommon : QuantumProver.QuantumEntropy.partialTrace_right R = QuantumProver.QuantumEntropy.partialTrace_right S)
    (δ : ℝ) (n : ℕ) : senderTypical hR δ n = senderTypical hS δ n := by
  unfold senderTypical
  have he {M N : Matrix X X ℂ} (hM : IsDensity M) (hN : IsDensity N) (hMN : M = N) :
      typicalProjector hM δ n = typicalProjector hN δ n := by
    subst N
    rfl
  exact he _ _ hcommon

theorem iidProxy_normalization_overhead_tendsto_zero {R : Matrix (X × Y) (X × Y) ℂ}
    (hR : IsDensity R) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun n => Real.log ((iidRawProxy hR δ n).trace.re⁻¹) / (n : ℝ)) atTop (𝓝 0) := by
  have hlog := (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp
    (iidRawProxy_trace_tendsto_one hR hδ)
  have hi : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  simpa only [Function.comp_def, Real.log_inv, div_eq_mul_inv, Real.log_one, neg_zero, zero_mul]
    using hlog.neg.mul hi

theorem conditional_typical_iid_smoothing {R : Matrix (X × Y) (X × Y) ℂ}
    (hR : IsDensity R) (δ : ℝ) (hδ : 0 < δ) :
    (∀ n, IsDensity (iidProxy hR δ n)) ∧
    (∀ n, (Matrix.rank (senderTypical hR δ n) : ℝ) ≤
      Real.exp ((n : ℝ) * (QuantumProver.QuantumEntropy.entropyNats (QuantumProver.QuantumEntropy.partialTrace_right R) + δ))) ∧
    Tendsto (fun n => traceNorm (groupedPower R n - iidProxy hR δ n)) atTop (𝓝 0) ∧
    ∀ᶠ n : ℕ in atTop,
      (senderTypical hR δ n ⊗ₖ (1 : Matrix (TensorIndex Y n) (TensorIndex Y n) ℂ)) * iidProxy hR δ n =
        iidProxy hR δ n ∧
      iidProxy hR δ n * ((1 : Matrix (TensorIndex X n) (TensorIndex X n) ℂ) ⊗ₖ referenceTypical hR δ n) =
        iidProxy hR δ n ∧
      (Matrix.rank (QuantumProver.QuantumEntropy.partialTrace_left (iidProxy hR δ n)) : ℝ) ≤
        Real.exp ((n : ℝ) * (QuantumProver.QuantumEntropy.entropyNats (QuantumProver.QuantumEntropy.partialTrace_left R) + δ)) ∧
      (iidProxy hR δ n * iidProxy hR δ n).trace.re ≤
        Real.exp (-(n : ℝ) * (QuantumProver.QuantumEntropy.entropyNats R - 2 * δ)) ∧
      (Matrix.rank (QuantumProver.QuantumEntropy.partialTrace_left (iidProxy hR δ n)) : ℝ) *
        (iidProxy hR δ n * iidProxy hR δ n).trace.re ≤
        Real.exp (-(n : ℝ) * (QuantumProver.QuantumEntropy.entropyNats R -
          QuantumProver.QuantumEntropy.entropyNats (QuantumProver.QuantumEntropy.partialTrace_left R) - 3 * δ)) ∧
      (Real.exp (-(n : ℝ) * (QuantumProver.QuantumEntropy.entropyNats R -
        QuantumProver.QuantumEntropy.entropyNats (QuantumProver.QuantumEntropy.partialTrace_left R) - 3 * δ)) •
        ((1 : Matrix (TensorIndex X n) (TensorIndex X n) ℂ) ⊗ₖ
          tensorPower (QuantumProver.QuantumEntropy.partialTrace_left R) n) - iidProxy hR δ n).PosSemidef := by
  refine ⟨iidProxy_isDensity hR δ,
    typicalProjector_rank_le_exp (QuantumProver.QuantumEntropy.partialTraceRight_isDensity hR) δ,
    iidProxy_error_tendsto_zero hR hδ, ?_⟩
  filter_upwards [mass_inverse_eventually_le_exp _ (iidRawProxy_trace_tendsto_one hR hδ) hδ,
    iidProxy_eventual_purity hR hδ, iidProxy_eventual_rank_purity hR hδ,
    iidProxy_eventual_conditional_cap hR hδ] with n ht hp hprod hcap
  exact ⟨(iidProxy_support_of_mass_pos hR δ n ht.1).1,
    (iidProxy_support_of_mass_pos hR δ n ht.1).2,
    iidProxy_reference_rank_le hR δ n ht.1, hp, hprod, hcap⟩

theorem exists_iid_conditional_operator_smoothing {R : Matrix (X × Y) (X × Y) ℂ}
    (hR : IsDensity R) (h : ℝ)
    (hh : h < QuantumProver.QuantumEntropy.entropyNats R -
      QuantumProver.QuantumEntropy.entropyNats (QuantumProver.QuantumEntropy.partialTrace_left R)) :
    ∃ N : (n : ℕ) → Matrix (TensorIndex X n × TensorIndex Y n) (TensorIndex X n × TensorIndex Y n) ℂ,
      (∀ n, IsDensity (N n)) ∧
      Tendsto (fun n => traceNorm (groupedPower R n - N n)) atTop (𝓝 0) ∧
      ∀ᶠ n : ℕ in atTop,
        (Real.exp (-(n : ℝ) * h) •
          ((1 : Matrix (TensorIndex X n) (TensorIndex X n) ℂ) ⊗ₖ
            tensorPower (QuantumProver.QuantumEntropy.partialTrace_left R) n) - N n).PosSemidef := by
  let δ := (QuantumProver.QuantumEntropy.entropyNats R -
    QuantumProver.QuantumEntropy.entropyNats (QuantumProver.QuantumEntropy.partialTrace_left R) - h) / 4
  have hδ : 0 < δ := div_pos (sub_pos.mpr hh) (by norm_num)
  refine ⟨iidProxy hR δ, iidProxy_isDensity hR δ, iidProxy_error_tendsto_zero hR hδ, ?_⟩
  filter_upwards [iidProxy_eventual_conditional_cap hR hδ] with n hn
  have hc : Real.exp (-(n : ℝ) * (QuantumProver.QuantumEntropy.entropyNats R -
      QuantumProver.QuantumEntropy.entropyNats (QuantumProver.QuantumEntropy.partialTrace_left R) - 3 * δ)) ≤
      Real.exp (-(n : ℝ) * h) := by
    apply Real.exp_le_exp.mpr
    have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    dsimp only [δ]
    nlinarith
  have hS := (Matrix.PosSemidef.one (n := TensorIndex X n) (R := ℂ)).kronecker
    (tensorPower_isDensity (QuantumProver.QuantumEntropy.partialTraceLeft_isDensity hR) n).1
  have hd := hS.smul (sub_nonneg.mpr hc)
  convert hn.add hd using 1
  simp only [sub_smul]
  abel

end QuantumProver.ConditionalTypicalSmoothing

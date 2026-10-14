import QuantumProver.InformationTheory.BellDiagonalSquashedEntanglement.Definitions
import QuantumProver.InformationTheory.BellDiagonalSquashedEntanglement.ScalarOptimization
import QuantumProver.InformationTheory.SuperchannelDiscrimination.CPTPKraus
import QuantumProver.InformationTheory.SuperchannelDiscrimination.TestingTheorems
import QuantumProver.LinearAlgebra.Affinity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

noncomputable section

open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder Matrix
  Matrix.Norms.L2Operator

namespace QuantumProver.BellDiagonalSquashedEntanglement

namespace RecoveryGeometry

variable {I O E : Type*} [Fintype I] [Fintype O] [Fintype E]
  [DecidableEq I] [DecidableEq O] [DecidableEq E]

theorem traceRight_eq_partialTraceRight (A : Mat (I × E)) :
    Geometry.traceRight A = partialTraceRight A := rfl

theorem pureMatrix_eq_outer (v : I → ℂ) : Geometry.pureMatrix v = outer v := rfl

theorem density_has_matrixPurification (A : Density I) :
    ∃ v : I × I → ℂ, IsDensity (outer v) ∧ partialTraceRight (outer v) = A.val := by
  refine ⟨Geometry.sqrtColumns A.val, ?_, ?_⟩
  · exact ⟨Geometry.pureMatrix_posSemidef _,
      (Geometry.pureMatrix_sqrtColumns_trace A.val A.property.1).trans A.property.2⟩
  · exact Geometry.traceRight_pureMatrix_sqrtColumns A.val A.property.1

theorem density_index_nonempty (A : Density I) : Nonempty I := by
  by_contra h
  haveI : IsEmpty I := not_nonempty_iff.mp h
  have hz : A.val.trace = 0 := by simp [Matrix.trace]
  exact one_ne_zero (A.property.2.symm.trans hz)

theorem channel_has_matrixStinespring (N : Channel I O) :
    ∃ V : Matrix (O × (I × O)) I ℂ,
      Vᴴ * V = 1 ∧ ∀ A : Mat I, partialTraceRight (V * A * Vᴴ) = N.map A := by
  have hCP : QuantumProver.SuperchannelDiscrimination.CPTPKraus.CompletelyPositive N.map :=
    N.completelyPositive
  have hTP : QuantumProver.SuperchannelDiscrimination.CPTPKraus.TracePreserving N.map :=
    N.tracePreserving
  let K := QuantumProver.SuperchannelDiscrimination.CPTPKraus.canonicalKraus N.map
  have hK : ∑ q : I × O, (K q)ᴴ * K q = 1 :=
    QuantumProver.SuperchannelDiscrimination.CPTPKraus.canonicalKraus_gram N.map hCP hTP
  refine ⟨Geometry.krausDilation K, Geometry.krausDilation_isometry K hK, ?_⟩
  intro A
  change Geometry.traceRight (Geometry.krausDilation K * A *
    (Geometry.krausDilation K)ᴴ) = N.map A
  rw [Geometry.traceRight_krausDilation]
  exact (QuantumProver.SuperchannelDiscrimination.CPTPKraus.canonicalKraus_reconstruct
    N.map hCP A).symm

def supportCompletionChannel
    (Φ : Mat I →ₗ[ℂ] Mat O) (hCP : CompletelyPositive Φ)
    (P : Mat I) (hHerm : Pᴴ = P) (hIdem : P * P = P)
    (hTrace : ∀ A : Mat I, (Φ A).trace = (P * A).trace) (o₀ : O) : Channel I O := by
  have hCP' : QuantumProver.SuperchannelDiscrimination.CPTPKraus.CompletelyPositive Φ := hCP
  let K := QuantumProver.SuperchannelDiscrimination.CPTPKraus.canonicalKraus Φ
  let Q : Mat I := 1 - P
  have hQ : Q.PosSemidef := Geometry.complement_posSemidef P hHerm hIdem
  have hK : ∑ q : I × O, (K q)ᴴ * K q = P :=
    QuantumProver.SuperchannelDiscrimination.CPTPKraus.canonicalGram_eq_of_tracePairing
      Φ hCP' P hTrace
  have hNorm : ∑ q : I × O, (K q)ᴴ * K q = 1 - Q := by
    have h : (1 : Mat I) - (1 - P) = P := by abel
    exact hK.trans h.symm
  let L := Geometry.completedKraus K Q o₀
  have hL : ∑ q : (I × O) ⊕ I, (L q)ᴴ * L q = 1 :=
    Geometry.completedKraus_gram K Q hQ o₀ hNorm
  refine ⟨QuantumProver.ElegantJointMeasurement.CP.krausMap L, ?_, ?_⟩
  · exact (QuantumProver.SuperchannelDiscrimination.CPTPKraus.completelyPositive_iff_EJMCP _).mpr
      (QuantumProver.ElegantJointMeasurement.CP.krausMap_completelyPositive L)
  · exact (QuantumProver.ElegantJointMeasurement.CP.krausMap_trace_preserving_iff L).mpr hL

theorem supportCompletionChannel_action
    (Φ : Mat I →ₗ[ℂ] Mat O) (hCP : CompletelyPositive Φ)
    (P : Mat I) (hHerm : Pᴴ = P) (hIdem : P * P = P)
    (hTrace : ∀ A : Mat I, (Φ A).trace = (P * A).trace) (o₀ : O) (A : Mat I) :
    (supportCompletionChannel Φ hCP P hHerm hIdem hTrace o₀).map A =
      Φ A + Matrix.single o₀ o₀ (((1 - P) * A).trace) := by
  change Geometry.krausAction
    (Geometry.completedKraus
      (QuantumProver.SuperchannelDiscrimination.CPTPKraus.canonicalKraus Φ) (1 - P) o₀) A = _
  rw [Geometry.completedKraus_action _ (1 - P)
    (Geometry.complement_posSemidef P hHerm hIdem) o₀ A]
  dsimp only [Geometry.krausAction]
  rw [← QuantumProver.SuperchannelDiscrimination.CPTPKraus.canonicalKraus_reconstruct Φ hCP A]

theorem supportCompletionChannel_on_supported
    (Φ : Mat I →ₗ[ℂ] Mat O) (hCP : CompletelyPositive Φ)
    (P : Mat I) (hHerm : Pᴴ = P) (hIdem : P * P = P)
    (hTrace : ∀ A : Mat I, (Φ A).trace = (P * A).trace) (o₀ : O)
    (A : Mat I) (hPA : P * A = A) :
    (supportCompletionChannel Φ hCP P hHerm hIdem hTrace o₀).map A = Φ A := by
  rw [supportCompletionChannel_action]
  have hz : (1 - P) * A = 0 := by
    rw [Matrix.sub_mul, Matrix.one_mul, hPA, sub_self]
  simp [hz]

namespace ReferenceEntropy

open QuantumProver.SuperchannelDiscrimination.FlaggedStates

theorem hasSupportIn_equalPriorAverage_left {A B : Mat I}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    HasSupportIn A ((1 / 2 : ℝ) • (A + B)) := by
  intro v hv
  have hsum : (A + B) *ᵥ v = 0 := by
    have h := congrArg (fun w : I → ℂ => (2 : ℝ) • w) hv
    simpa only [Matrix.smul_mulVec, smul_smul, smul_zero,
      show (2 : ℝ) * (1 / 2) = 1 by norm_num, one_smul] using h
  have hz : star v ⬝ᵥ A *ᵥ v + star v ⬝ᵥ B *ᵥ v = 0 := by
    simpa only [Matrix.add_mulVec, dotProduct_add, dotProduct_zero] using
      congrArg (fun w : I → ℂ => star v ⬝ᵥ w) hsum
  have hle : star v ⬝ᵥ A *ᵥ v ≤ 0 :=
    le_of_le_of_eq (le_add_of_nonneg_right (hB.dotProduct_mulVec_nonneg v)) hz
  exact hA.dotProduct_mulVec_zero_iff.mp
    (le_antisymm hle (hA.dotProduct_mulVec_nonneg v))

theorem hasSupportIn_equalPriorAverage_right {A B : Mat I}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    HasSupportIn B ((1 / 2 : ℝ) • (A + B)) := by
  simpa only [add_comm] using hasSupportIn_equalPriorAverage_left hB hA

theorem binaryHolevo_eq_average_finiteRelativeEntropy {A B : Mat I}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    binaryHolevo A B =
      (finiteRelativeEntropyBits A ((1 / 2 : ℝ) • (A + B)) +
       finiteRelativeEntropyBits B ((1 / 2 : ℝ) • (A + B))) / 2 := by
  let μ : Mat I := (1 / 2 : ℝ) • (A + B)
  have hμ : μ.IsHermitian := ((hA.add hB).smul (by norm_num)).isHermitian
  have hprod : cfc (fun x : ℝ => x * Real.log x) μ = μ * cfc Real.log μ := by
    rw [cfc_mul (p := IsSelfAdjoint) (fun x : ℝ => x) Real.log μ
      (μ.finite_real_spectrum.continuousOn _) (μ.finite_real_spectrum.continuousOn _),
      cfc_id' (p := IsSelfAdjoint) ℝ μ hμ]
  have hlin : (μ * cfc Real.log μ).trace.re =
      ((A * cfc Real.log μ).trace.re + (B * cfc Real.log μ).trace.re) / 2 := by
    simp only [μ, Matrix.smul_mul, Matrix.add_mul, Matrix.trace_smul,
      Matrix.trace_add, Complex.add_re, Complex.smul_re]
    ring
  rw [finiteRelativeEntropyBits_eq_spectral hA.isHermitian,
    finiteRelativeEntropyBits_eq_spectral hB.isHermitian]
  change -(cfc (fun x : ℝ => x * Real.log x) μ).trace.re / Real.log 2 -
      (-(cfc (fun x : ℝ => x * Real.log x) A).trace.re / Real.log 2 +
       -(cfc (fun x : ℝ => x * Real.log x) B).trace.re / Real.log 2) / 2 = _
  rw [hprod, hlin]
  ring

theorem relativeEntropyBits_equalPriorAverage {A B : Mat I}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    relativeEntropyBits A ((1 / 2 : ℝ) • (A + B)) =
      (finiteRelativeEntropyBits A ((1 / 2 : ℝ) • (A + B)) : EReal) ∧
    relativeEntropyBits B ((1 / 2 : ℝ) • (A + B)) =
      (finiteRelativeEntropyBits B ((1 / 2 : ℝ) • (A + B)) : EReal) := by
  exact ⟨by simp only [relativeEntropyBits,
      if_pos (hasSupportIn_equalPriorAverage_left hA hB)],
    by simp only [relativeEntropyBits,
      if_pos (hasSupportIn_equalPriorAverage_right hA hB)]⟩

theorem channel_equalPriorAverage (N : Channel I O) (A B : Mat I) :
    N.map ((1 / 2 : ℝ) • (A + B)) =
      (1 / 2 : ℝ) • (N.map A + N.map B) := by
  rw [N.map.map_smul_of_tower, map_add]

theorem binaryHolevoLoss_eq_average_referenceGaps
    (A B : Density I) (N : Channel I O) :
    binaryHolevo A.val B.val - binaryHolevo (N.map A.val) (N.map B.val) =
      (finiteRelativeEntropyBits A.val ((1 / 2 : ℝ) • (A.val + B.val)) -
       finiteRelativeEntropyBits (N.map A.val)
         (N.map ((1 / 2 : ℝ) • (A.val + B.val))) +
       (finiteRelativeEntropyBits B.val ((1 / 2 : ℝ) • (A.val + B.val)) -
        finiteRelativeEntropyBits (N.map B.val)
          (N.map ((1 / 2 : ℝ) • (A.val + B.val))))) / 2 := by
  rw [channel_equalPriorAverage,
    binaryHolevo_eq_average_finiteRelativeEntropy A.property.1 B.property.1,
    binaryHolevo_eq_average_finiteRelativeEntropy
      (N.posSemidef A.property.1) (N.posSemidef B.property.1)]
  ring

theorem channel_outputs_supported_on_average (A B : Density I) (N : Channel I O) :
    HasSupportIn (N.map A.val) (N.map ((1 / 2 : ℝ) • (A.val + B.val))) ∧
    HasSupportIn (N.map B.val) (N.map ((1 / 2 : ℝ) • (A.val + B.val))) := by
  rw [channel_equalPriorAverage]
  exact ⟨hasSupportIn_equalPriorAverage_left
    (N.posSemidef A.property.1) (N.posSemidef B.property.1),
    hasSupportIn_equalPriorAverage_right
      (N.posSemidef A.property.1) (N.posSemidef B.property.1)⟩

end ReferenceEntropy

namespace MeasuredDivergence

theorem weighted_log_ge_hellinger (p q : ℝ) (hp : 0 < p) (hq : 0 < q) :
    2 * (p - Real.sqrt (p * q)) ≤ p * (Real.log p - Real.log q) := by
  let r := Real.sqrt (q / p)
  have hr : 0 < r := Real.sqrt_pos.mpr (div_pos hq hp)
  have hrlog : Real.log r = (Real.log q - Real.log p) / 2 := by
    dsimp only [r]
    rw [Real.log_sqrt (le_of_lt (div_pos hq hp)), Real.log_div hq.ne' hp.ne']
  have hrpow : r ^ 2 = q / p := Real.sq_sqrt (le_of_lt (div_pos hq hp))
  have hprpow : (p * r) ^ 2 = p * q := by
    rw [mul_pow, hrpow]
    field_simp [hp.ne']
    <;> ring
  have hpr : p * r = Real.sqrt (p * q) := by
    have hroot := Real.sq_sqrt (le_of_lt (mul_pos hp hq))
    have hn := Real.sqrt_nonneg (p * q)
    have hpn := mul_nonneg hp.le hr.le
    nlinarith
  have h := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos hr) hp.le
  rw [hrlog] at h
  nlinarith

theorem classicalRelativeEntropyBits_ge_hellinger
    {K : Type*} [Fintype K] (p q : K → ℝ)
    (hp : ∀ k, 0 ≤ p k) (hq : ∀ k, 0 ≤ q k) (hpsum : ∑ k, p k = 1) :
    ((2 * (1 - ∑ k, Real.sqrt (p k * q k)) / Real.log 2 : ℝ) : EReal) ≤
      classicalRelativeEntropyBits p q := by
  classical
  let f : K → ℝ := fun k => 2 * (p k - Real.sqrt (p k * q k)) / Real.log 2
  have hterm : ∀ k,
      (f k : EReal) ≤
        if p k = 0 then 0 else if q k = 0 then ⊤
        else ((p k * (Real.log (p k) - Real.log (q k)) / Real.log 2 : ℝ) : EReal) := by
    intro k
    by_cases hp0 : p k = 0
    · simp [f, hp0]
    · rw [if_neg hp0]
      by_cases hq0 : q k = 0
      · simp only [if_pos hq0, le_top]
      · rw [if_neg hq0]
        apply EReal.coe_le_coe
        exact div_le_div_of_nonneg_right
          (weighted_log_ge_hellinger (p k) (q k)
            (lt_of_le_of_ne (hp k) (Ne.symm hp0))
            (lt_of_le_of_ne (hq k) (Ne.symm hq0))) log_two_pos.le
  let coeHom : ℝ →+ EReal := ⟨⟨(↑), EReal.coe_zero⟩, EReal.coe_add⟩
  have hcast : (∑ k, (f k : EReal)) = ((∑ k, f k : ℝ) : EReal) :=
    (map_sum coeHom f Finset.univ).symm
  have hsum : (∑ k, f k) = 2 * (1 - ∑ k, Real.sqrt (p k * q k)) / Real.log 2 := by
    rw [show (∑ k, f k) = (∑ k, 2 * (p k - Real.sqrt (p k * q k))) /
        Real.log 2 by simp only [f, Finset.sum_div],
      ← Finset.mul_sum, Finset.sum_sub_distrib, hpsum]
  rw [← hsum, ← hcast]
  exact Finset.sum_le_sum fun k hk => hterm k

theorem measurementProbability_nonneg (A : Density I)
    {K : Type*} [Fintype K] (M : POVM I K) (k : K) :
    0 ≤ measurementProbability M A.val k :=
  QuantumProver.SuperchannelDiscrimination.FlaggedStates.trace_mul_re_nonneg
    A.property.1 (M.positive k)

theorem measurementProbability_sum (A : Density I)
    {K : Type*} [Fintype K] (M : POVM I K) :
    ∑ k, measurementProbability M A.val k = 1 := by
  simp only [measurementProbability, ← Complex.re_sum]
  rw [← Matrix.trace_sum, ← Finset.mul_sum, M.normalized, Matrix.mul_one, A.property.2]
  simp

theorem measuredRelativeEntropyBits_ge_measurement_hellinger
    (A B : Density I) (m : ℕ) (hm : 0 < m) (M : POVM I (Fin m)) :
    ((2 * (1 - ∑ k, Real.sqrt
      (measurementProbability M A.val k * measurementProbability M B.val k)) /
      Real.log 2 : ℝ) : EReal) ≤ measuredRelativeEntropyBits A.val B.val := by
  apply le_trans (classicalRelativeEntropyBits_ge_hellinger _ _
    (measurementProbability_nonneg A M) (measurementProbability_nonneg B M)
    (measurementProbability_sum A M))
  exact le_sSup ⟨m, hm, M, rfl⟩

def reindexPOVM {K L : Type*} [Fintype K] [Fintype L]
    (M : POVM I K) (e : L ≃ K) : POVM I L where
  effect := fun l => M.effect (e l)
  positive l := M.positive (e l)
  normalized := by rw [Equiv.sum_comp e (fun k => M.effect k), M.normalized]

theorem measuredRelativeEntropyBits_ge_finite_measurement_hellinger
    (A B : Density I) {K : Type*} [Fintype K] [Nonempty K] (M : POVM I K) :
    ((2 * (1 - ∑ k, Real.sqrt
      (measurementProbability M A.val k * measurementProbability M B.val k)) /
      Real.log 2 : ℝ) : EReal) ≤ measuredRelativeEntropyBits A.val B.val := by
  let e := Fintype.equivFin K
  have h := measuredRelativeEntropyBits_ge_measurement_hellinger A B
    (Fintype.card K) (Fintype.card_pos_iff.mpr inferInstance) (reindexPOVM M e.symm)
  have hsum : (∑ k : Fin (Fintype.card K), Real.sqrt
      (measurementProbability (reindexPOVM M e.symm) A.val k *
        measurementProbability (reindexPOVM M e.symm) B.val k)) =
      ∑ k : K, Real.sqrt
        (measurementProbability M A.val k * measurementProbability M B.val k) :=
    Equiv.sum_comp e.symm (fun k => Real.sqrt
      (measurementProbability M A.val k * measurementProbability M B.val k))
  rw [hsum] at h
  exact h

theorem measuredRelativeEntropyBits_ge_bures_of_attaining_measurement
    (A B : Density I) {K : Type*} [Fintype K] [Nonempty K] (M : POVM I K)
    (hF : (∑ k, Real.sqrt
      (measurementProbability M A.val k * measurementProbability M B.val k)) =
        rootFidelity A.val B.val) :
    ((2 * (1 - rootFidelity A.val B.val) / Real.log 2 : ℝ) : EReal) ≤
      measuredRelativeEntropyBits A.val B.val := by
  have h := measuredRelativeEntropyBits_ge_finite_measurement_hellinger A B M
  rwa [hF] at h

end MeasuredDivergence

namespace PetzSupportMap

open QuantumProver.SuperchannelDiscrimination.TensorEntropy
open QuantumProver.SuperchannelDiscrimination.OutputSupport

def inverseRoot (A : Mat I) : Mat I := cfc (fun x : ℝ => (Real.sqrt x)⁻¹) A

theorem inverseRoot_isHermitian (A : Mat I) : (inverseRoot A).IsHermitian :=
  cfc_predicate _ _

theorem inverseRoot_sandwich (A : Mat I) (hA : A.PosSemidef) :
    inverseRoot A * A * inverseRoot A = supportProjection A := by
  calc
    _ = cfc (fun x : ℝ => (Real.sqrt x)⁻¹) A * cfc (fun x : ℝ => x) A *
        cfc (fun x : ℝ => (Real.sqrt x)⁻¹) A := by
      rw [cfc_id' (p := IsSelfAdjoint) ℝ A hA.isHermitian]
      rfl
    _ = cfc (fun x : ℝ => (Real.sqrt x)⁻¹ * x * (Real.sqrt x)⁻¹) A := by
      rw [← cfc_mul (p := IsSelfAdjoint) _ _ A
        (A.finite_real_spectrum.continuousOn _) (A.finite_real_spectrum.continuousOn _),
        ← cfc_mul (p := IsSelfAdjoint) _ _ A
          (A.finite_real_spectrum.continuousOn _) (A.finite_real_spectrum.continuousOn _)]
    _ = _ := by
      unfold supportProjection
      apply cfc_congr
      intro x hx
      have hx0 : 0 ≤ x := spectrum_nonneg_of_nonneg hA.nonneg hx
      by_cases hz : x = 0
      · simp [nonzeroWeight, hz]
      · rw [nonzeroWeight, if_neg hz]
        have hs : Real.sqrt x ≠ 0 :=
          ne_of_gt (Real.sqrt_pos.mpr (lt_of_le_of_ne hx0 (Ne.symm hz)))
        calc
          _ = (Real.sqrt x)⁻¹ * (Real.sqrt x * Real.sqrt x) * (Real.sqrt x)⁻¹ :=
            congrArg (fun y : ℝ => (Real.sqrt x)⁻¹ * y * (Real.sqrt x)⁻¹)
              (Real.mul_self_sqrt hx0).symm
          _ = _ := by field_simp [hs]

def petzKraus (N : Channel I O) (σ : Density I) : I × O → Matrix I O ℂ :=
  fun q => CFC.sqrt σ.val *
    (QuantumProver.SuperchannelDiscrimination.CPTPKraus.canonicalKraus N.map q)ᴴ *
      inverseRoot (N.map σ.val)

theorem petzKraus_gram (N : Channel I O) (σ : Density I) :
    (∑ q : I × O, (petzKraus N σ q)ᴴ * petzKraus N σ q) =
      supportProjection (N.map σ.val) := by
  let K := QuantumProver.SuperchannelDiscrimination.CPTPKraus.canonicalKraus N.map
  let R := inverseRoot (N.map σ.val)
  have hS : (CFC.sqrt σ.val).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg _)
  have hR : Rᴴ = R := (inverseRoot_isHermitian _).eq
  calc
    _ = ∑ q : I × O,
        R * (K q * (CFC.sqrt σ.val * CFC.sqrt σ.val) * (K q)ᴴ) * R := by
      apply Finset.sum_congr rfl
      intro q hq
      simp only [petzKraus, Matrix.conjTranspose_mul,
        Matrix.conjTranspose_conjTranspose, hS.isHermitian.eq,
        (inverseRoot_isHermitian _).eq]
      change _ = inverseRoot (N.map σ.val) *
        (K q * (CFC.sqrt σ.val * CFC.sqrt σ.val) * (K q)ᴴ) * inverseRoot (N.map σ.val)
      simp only [K, Matrix.mul_assoc]
    _ = R * (∑ q : I × O, K q * σ.val * (K q)ᴴ) * R := by
      rw [CFC.sqrt_mul_sqrt_self σ.val σ.property.1.nonneg,
        Finset.mul_sum, Finset.sum_mul]
    _ = R * N.map σ.val * R := by
      rw [← QuantumProver.SuperchannelDiscrimination.CPTPKraus.canonicalKraus_reconstruct
        N.map N.completelyPositive σ.val]
    _ = _ := inverseRoot_sandwich _ (N.posSemidef σ.property.1)

def completedPetzChannel (N : Channel I O) (σ : Density I) (o₀ : I) : Channel O I := by
  let P := supportProjection (N.map σ.val)
  let Φ := QuantumProver.ElegantJointMeasurement.CP.krausMap (petzKraus N σ)
  have hΦ : CompletelyPositive Φ :=
    (QuantumProver.SuperchannelDiscrimination.CPTPKraus.completelyPositive_iff_EJMCP _).mpr
      (QuantumProver.ElegantJointMeasurement.CP.krausMap_completelyPositive _)
  have hτ := (N.posSemidef σ.property.1).isHermitian
  have hTrace : ∀ A : Mat O, (Φ A).trace = (P * A).trace := by
    intro A
    change (Geometry.krausAction (petzKraus N σ) A).trace = _
    rw [Geometry.trace_krausAction, petzKraus_gram]
  exact supportCompletionChannel Φ hΦ P (supportProjection_isHermitian hτ).eq
    (supportProjection_idempotent hτ) hTrace o₀

def logarithmSelfAdjoint (A : Mat I) : selfAdjoint (Mat I) :=
  ⟨cfc Real.log A, cfc_predicate _ _⟩

def modularPhase (A : Mat I) (t : ℝ) : Matrix.unitaryGroup I ℂ :=
  selfAdjoint.expUnitary ((t / 2 : ℝ) • logarithmSelfAdjoint A)

theorem modularPhase_commutes_support (A : Mat I) (t : ℝ) :
    Commute (modularPhase A t : Mat I) (supportProjection A) := by
  have h : Commute (cfc Real.log A) (supportProjection A) :=
    cfc_commute_cfc Real.log nonzeroWeight A
  have h' := (h.smul_left (t / 2 : ℝ)).smul_left Complex.I
  change Commute (NormedSpace.exp (Complex.I • ((t / 2 : ℝ) • cfc Real.log A)))
    (supportProjection A)
  exact h'.exp_left

def rotatedPetzKraus (N : Channel I O) (σ : Density I) (t : ℝ) :
    I × O → Matrix I O ℂ :=
  fun q => (modularPhase σ.val t : Mat I) * petzKraus N σ q *
    (modularPhase (N.map σ.val) t : Mat O)ᴴ

theorem rotatedPetzKraus_gram (N : Channel I O) (σ : Density I) (t : ℝ) :
    (∑ q : I × O, (rotatedPetzKraus N σ t q)ᴴ * rotatedPetzKraus N σ t q) =
      supportProjection (N.map σ.val) := by
  let U := modularPhase σ.val t
  let W := modularPhase (N.map σ.val) t
  have hU : (U : Mat I)ᴴ * (U : Mat I) = 1 := Matrix.mem_unitaryGroup_iff'.mp U.property
  have hW : (W : Mat O) * (W : Mat O)ᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp W.property
  have hP := (modularPhase_commutes_support (N.map σ.val) t).eq
  calc
    _ = ∑ q : I × O,
        (W : Mat O) * ((petzKraus N σ q)ᴴ * petzKraus N σ q) * (W : Mat O)ᴴ := by
      apply Finset.sum_congr rfl
      intro q hq
      change (((U : Mat I) * petzKraus N σ q * (W : Mat O)ᴴ)ᴴ *
          ((U : Mat I) * petzKraus N σ q * (W : Mat O)ᴴ)) = _
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
        Matrix.conjTranspose_conjTranspose]
      calc
        _ = (W : Mat O) * (petzKraus N σ q)ᴴ *
            ((U : Mat I)ᴴ * (U : Mat I)) * petzKraus N σ q * (W : Mat O)ᴴ := by
          simp only [Matrix.mul_assoc]
        _ = _ := by simp only [hU, Matrix.mul_one, Matrix.mul_assoc]
    _ = (W : Mat O) * (∑ q : I × O, (petzKraus N σ q)ᴴ * petzKraus N σ q) *
        (W : Mat O)ᴴ := by rw [Finset.mul_sum, Finset.sum_mul]
    _ = (W : Mat O) * supportProjection (N.map σ.val) * (W : Mat O)ᴴ := by
      rw [petzKraus_gram]
    _ = _ := by rw [hP, Matrix.mul_assoc, hW, Matrix.mul_one]

def completedRotatedPetzChannel (N : Channel I O) (σ : Density I)
    (t : ℝ) (o₀ : I) : Channel O I := by
  let P := supportProjection (N.map σ.val)
  let Φ := QuantumProver.ElegantJointMeasurement.CP.krausMap (rotatedPetzKraus N σ t)
  have hΦ : CompletelyPositive Φ :=
    (QuantumProver.SuperchannelDiscrimination.CPTPKraus.completelyPositive_iff_EJMCP _).mpr
      (QuantumProver.ElegantJointMeasurement.CP.krausMap_completelyPositive _)
  have hτ := (N.posSemidef σ.property.1).isHermitian
  have hTrace : ∀ A : Mat O, (Φ A).trace = (P * A).trace := by
    intro A
    change (Geometry.krausAction (rotatedPetzKraus N σ t) A).trace = _
    rw [Geometry.trace_krausAction, rotatedPetzKraus_gram]
  exact supportCompletionChannel Φ hΦ P (supportProjection_isHermitian hτ).eq
    (supportProjection_idempotent hτ) hTrace o₀

end PetzSupportMap

end RecoveryGeometry

end QuantumProver.BellDiagonalSquashedEntanglement

namespace QuantumProver.BellDiagonalSquashedEntanglement.RecoveryGeometry.UhlmannGeometry

variable {I J E : Type*} [Fintype I] [Fintype J] [Fintype E]
  [DecidableEq I] [DecidableEq J] [DecidableEq E]

theorem traceNorm_isometry (V : Matrix J I ℂ) (hV : Vᴴ * V = 1)
    (M : Mat I) : traceNorm (V * M * Vᴴ) = traceNorm M := by
  have hGram : (V * M * Vᴴ)ᴴ * (V * M * Vᴴ) = V * (Mᴴ * M) * Vᴴ := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose]
    calc
      _ = V * (Mᴴ * (Vᴴ * V) * M) * Vᴴ := by simp only [Matrix.mul_assoc]
      _ = _ := by simp only [hV, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc]
  have hRoot : CFC.sqrt (V * (Mᴴ * M) * Vᴴ) =
      V * CFC.sqrt (Mᴴ * M) * Vᴴ :=
    QuantumProver.MatrixAnalysis.Affinity.sqrtPSD_isometry V hV _
      (Matrix.posSemidef_conjTranspose_mul_self M)
  unfold traceNorm
  rw [hGram, hRoot]
  rw [Matrix.trace_mul_cycle, hV, Matrix.one_mul]

theorem rootFidelity_isometry (V : Matrix J I ℂ) (hV : Vᴴ * V = 1)
    (A B : Mat I) (hA : A.PosSemidef) (hB : B.PosSemidef) :
    rootFidelity (V * A * Vᴴ) (V * B * Vᴴ) = rootFidelity A B := by
  unfold rootFidelity sqrtPSD
  have hRootA : CFC.sqrt (V * A * Vᴴ) = V * CFC.sqrt A * Vᴴ :=
    QuantumProver.MatrixAnalysis.Affinity.sqrtPSD_isometry V hV A hA
  have hRootB : CFC.sqrt (V * B * Vᴴ) = V * CFC.sqrt B * Vᴴ :=
    QuantumProver.MatrixAnalysis.Affinity.sqrtPSD_isometry V hV B hB
  rw [hRootA, hRootB]
  have heq : (V * CFC.sqrt A * Vᴴ) * (V * CFC.sqrt B * Vᴴ) =
      V * (CFC.sqrt A * CFC.sqrt B) * Vᴴ := by
    calc
      _ = V * CFC.sqrt A * (Vᴴ * V) * CFC.sqrt B * Vᴴ := by
        simp only [Matrix.mul_assoc]
      _ = _ := by rw [hV, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  rw [heq, traceNorm_isometry V hV]

def leftEmbedding : Matrix (I ⊕ E) I ℂ :=
  fun s i => match s with
    | Sum.inl j => if j = i then 1 else 0
    | Sum.inr _ => 0

def rightEmbedding : Matrix (I ⊕ E) E ℂ :=
  fun s e => match s with
    | Sum.inl _ => 0
    | Sum.inr f => if f = e then 1 else 0

theorem leftEmbedding_isometry :
    (leftEmbedding (I := I) (E := E))ᴴ *
      leftEmbedding (I := I) (E := E) = (1 : Mat I) := by
  ext i j
  simp [leftEmbedding, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fintype.sum_sum_type, Matrix.one_apply, eq_comm]

theorem rightEmbedding_isometry :
    (rightEmbedding (I := I) (E := E))ᴴ *
      rightEmbedding (I := I) (E := E) = (1 : Mat E) := by
  ext i j
  simp [rightEmbedding, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fintype.sum_sum_type, Matrix.one_apply, eq_comm]

theorem norm_trace_factor_overlap_le_rootFidelity (C D : Matrix I E ℂ) :
    ‖(Cᴴ * D).trace‖ ≤ rootFidelity (C * Cᴴ) (D * Dᴴ) := by
  let A := C * Cᴴ
  let B := D * Dᴴ
  let P : Matrix (I ⊕ E) I ℂ := leftEmbedding
  let Q : Matrix (I ⊕ E) E ℂ := rightEmbedding
  let M := CFC.sqrt A * CFC.sqrt B
  have hP : Pᴴ * P = 1 := leftEmbedding_isometry
  have hQ : Qᴴ * Q = 1 := rightEmbedding_isometry
  have hA : A.PosSemidef := Matrix.posSemidef_self_mul_conjTranspose C
  have hB : B.PosSemidef := Matrix.posSemidef_self_mul_conjTranspose D
  have hsA : (CFC.sqrt A)ᴴ = CFC.sqrt A :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)).isHermitian.eq
  have hsB : (CFC.sqrt B)ᴴ = CFC.sqrt B :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg B)).isHermitian.eq
  have hSA : (P * CFC.sqrt A)ᴴ * (P * CFC.sqrt A) = A := by
    rw [Matrix.conjTranspose_mul, hsA]
    calc
      _ = CFC.sqrt A * (Pᴴ * P) * CFC.sqrt A := by simp only [Matrix.mul_assoc]
      _ = A := by rw [hP, Matrix.mul_one, CFC.sqrt_mul_sqrt_self A hA.nonneg]
  have hSB : (P * CFC.sqrt B)ᴴ * (P * CFC.sqrt B) = B := by
    rw [Matrix.conjTranspose_mul, hsB]
    calc
      _ = CFC.sqrt B * (Pᴴ * P) * CFC.sqrt B := by simp only [Matrix.mul_assoc]
      _ = B := by rw [hP, Matrix.mul_one, CFC.sqrt_mul_sqrt_self B hB.nonneg]
  have hC : (Q * Cᴴ)ᴴ * (Q * Cᴴ) = A := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    calc
      _ = C * (Qᴴ * Q) * Cᴴ := by simp only [Matrix.mul_assoc]
      _ = A := by rw [hQ, Matrix.mul_one]
  have hD : (Q * Dᴴ)ᴴ * (Q * Dᴴ) = B := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    calc
      _ = D * (Qᴴ * Q) * Dᴴ := by simp only [Matrix.mul_assoc]
      _ = B := by rw [hQ, Matrix.mul_one]
  obtain ⟨U, hU, hCU⟩ := Geometry.exists_unitary_mul_of_gram_eq
    (P * CFC.sqrt A) (Q * Cᴴ) (hSA.trans hC.symm)
  obtain ⟨W, hW, hDW⟩ := Geometry.exists_unitary_mul_of_gram_eq
    (P * CFC.sqrt B) (Q * Dᴴ) (hSB.trans hD.symm)
  have hWstar : Wᴴ ∈ Matrix.unitaryGroup (I ⊕ E) ℂ := by
    apply Matrix.mem_unitaryGroup_iff'.mpr
    simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose] using
      (Matrix.mem_unitaryGroup_iff.mp hW)
  have hWU : Wᴴ * U ∈ Matrix.unitaryGroup (I ⊕ E) ℂ :=
    (Matrix.unitaryGroup (I ⊕ E) ℂ).mul_mem hWstar hU
  have ht : ((Q * Cᴴ) * (Q * Dᴴ)ᴴ).trace = (Cᴴ * D).trace := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    calc
      _ = (Q * (Cᴴ * D) * Qᴴ).trace := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [Matrix.trace_mul_cycle, hQ, Matrix.one_mul]
  have hf : ((Q * Cᴴ) * (Q * Dᴴ)ᴴ).trace =
      ((Wᴴ * U) * (P * M * Pᴴ)).trace := by
    rw [hCU, hDW, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hsB]
    calc
      _ = (U * (P * M * Pᴴ) * Wᴴ).trace := by simp only [M, Matrix.mul_assoc]
      _ = _ := Matrix.trace_mul_cycle _ _ _
  calc
    _ = ‖((Wᴴ * U) * (P * M * Pᴴ)).trace‖ := by rw [← ht, hf]
    _ ≤ traceNorm (P * M * Pᴴ) :=
      Geometry.norm_trace_unitary_mul_le_absolute_trace _ _ hWU
    _ = traceNorm M := traceNorm_isometry P hP M
    _ = _ := rfl

theorem purification_overlap_le_rootFidelity (v w : I × E → ℂ) :
    ‖inner ℂ (WithLp.toLp 2 v) (WithLp.toLp 2 w)‖ ≤
      rootFidelity (partialTraceRight (outer v)) (partialTraceRight (outer w)) := by
  change ‖inner ℂ (WithLp.toLp 2 (Geometry.matrixVector (Geometry.columns v)))
      (WithLp.toLp 2 (Geometry.matrixVector (Geometry.columns w)))‖ ≤
    rootFidelity (Geometry.traceRight (Geometry.pureMatrix v))
      (Geometry.traceRight (Geometry.pureMatrix w))
  rw [Geometry.inner_matrixVector, Geometry.traceRight_pureMatrix,
    Geometry.traceRight_pureMatrix]
  exact norm_trace_factor_overlap_le_rootFidelity _ _

theorem norm_purification_eq_one (v : I × E → ℂ) (hv : IsDensity (outer v)) :
    ‖WithLp.toLp 2 v‖ = 1 := by
  have hi : inner ℂ (WithLp.toLp 2 v) (WithLp.toLp 2 v) = 1 := by
    calc
      _ = ((Geometry.columns v)ᴴ * Geometry.columns v).trace :=
        Geometry.inner_matrixVector _ _
      _ = (Geometry.columns v * (Geometry.columns v)ᴴ).trace :=
        Matrix.trace_mul_comm _ _
      _ = (outer v).trace := by
        rw [← Geometry.traceRight_pureMatrix, Geometry.trace_traceRight]
        rfl
      _ = 1 := hv.2
  have hn := norm_sq_eq_re_inner (𝕜 := ℂ) (WithLp.toLp 2 v)
  rw [hi] at hn
  change ‖WithLp.toLp 2 v‖ ^ 2 = 1 at hn
  nlinarith [norm_nonneg (WithLp.toLp 2 v)]

theorem density_has_fidelity_attaining_purifications (A B : Density I) :
    ∃ v w : I × I → ℂ,
      IsDensity (outer v) ∧ IsDensity (outer w) ∧
      partialTraceRight (outer v) = A.val ∧
      partialTraceRight (outer w) = B.val ∧
      ‖inner ℂ (WithLp.toLp 2 v) (WithLp.toLp 2 w)‖ = rootFidelity A.val B.val := by
  obtain ⟨v, w, hv, hw, hinner⟩ :=
    Geometry.exists_aligned_squareRoot_purifications A.val B.val A.property.1 B.property.1
  refine ⟨v, w, ?_, ?_, hv, hw, ?_⟩
  · refine ⟨Geometry.pureMatrix_posSemidef _, ?_⟩
    change (Geometry.pureMatrix v).trace = 1
    rw [← Geometry.trace_traceRight, hv, A.property.2]
  · refine ⟨Geometry.pureMatrix_posSemidef _, ?_⟩
    change (Geometry.pureMatrix w).trace = 1
    rw [← Geometry.trace_traceRight, hw, B.property.2]
  · rw [hinner, Geometry.norm_absolute_trace_eq_real_trace]
    rfl

theorem rootFidelity_nonneg (A B : Density I) : 0 ≤ rootFidelity A.val B.val := by
  obtain ⟨v, w, hv, hw, hm0, hm1, hf⟩ := density_has_fidelity_attaining_purifications A B
  rw [← hf]
  exact norm_nonneg _

theorem rootFidelity_le_one (A B : Density I) : rootFidelity A.val B.val ≤ 1 := by
  obtain ⟨v, w, hv, hw, hm0, hm1, hf⟩ := density_has_fidelity_attaining_purifications A B
  have h := norm_inner_le_norm (𝕜 := ℂ) (WithLp.toLp 2 v) (WithLp.toLp 2 w)
  simpa only [hf, norm_purification_eq_one v hv, norm_purification_eq_one w hw, mul_one]
    using h

end QuantumProver.BellDiagonalSquashedEntanglement.RecoveryGeometry.UhlmannGeometry

namespace QuantumProver.BellDiagonalSquashedEntanglement.RecoveryGeometry.UhlmannGeometry

variable {I O E J : Type*} [Fintype I] [Fintype O] [Fintype E] [Fintype J]
  [DecidableEq I] [DecidableEq O] [DecidableEq E] [DecidableEq J]

def krausLiftColumns (K : J → Matrix O I ℂ) (C : Matrix I E ℂ) :
    Matrix O (J × E) ℂ := fun o q => (K q.1 * C) o q.2

theorem krausLiftColumns_marginal (K : J → Matrix O I ℂ) (C : Matrix I E ℂ) :
    krausLiftColumns K C * (krausLiftColumns K C)ᴴ =
      Geometry.krausAction K (C * Cᴴ) := by
  have heq : krausLiftColumns K C * (krausLiftColumns K C)ᴴ =
      ∑ j : J, (K j * C) * (K j * C)ᴴ := by
    ext o p
    simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
      krausLiftColumns, Fintype.sum_prod_type]
  rw [heq]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]

theorem krausLiftColumns_trace_overlap (K : J → Matrix O I ℂ)
    (C D : Matrix I E ℂ) (hK : ∑ j : J, (K j)ᴴ * K j = 1) :
    ((krausLiftColumns K C)ᴴ * krausLiftColumns K D).trace = (Cᴴ * D).trace := by
  have heq : ((krausLiftColumns K C)ᴴ * krausLiftColumns K D).trace =
      ∑ j : J, ((K j * C)ᴴ * (K j * D)).trace := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply,
      Matrix.conjTranspose_apply, krausLiftColumns, Fintype.sum_prod_type]
  calc
    _ = ∑ j : J, ((K j * C)ᴴ * (K j * D)).trace := heq
    _ = (Cᴴ * (∑ j : J, (K j)ᴴ * K j) * D).trace := by
      rw [Matrix.mul_sum, Matrix.sum_mul, Matrix.trace_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [Matrix.conjTranspose_mul]
      simp only [Matrix.mul_assoc]
    _ = _ := by rw [hK, Matrix.mul_one]

theorem rootFidelity_channel_mono (N : Channel I O) (A B : Mat I)
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    rootFidelity A B ≤ rootFidelity (N.map A) (N.map B) := by
  obtain ⟨v, w, hv, hw, hinner⟩ := Geometry.exists_aligned_squareRoot_purifications A B hA hB
  let C := Geometry.columns v
  let D := Geometry.columns w
  let K := QuantumProver.SuperchannelDiscrimination.CPTPKraus.canonicalKraus N.map
  have hK : ∑ j : I × O, (K j)ᴴ * K j = 1 :=
    QuantumProver.SuperchannelDiscrimination.CPTPKraus.canonicalKraus_gram
      N.map N.completelyPositive N.tracePreserving
  have hC : C * Cᴴ = A := (Geometry.traceRight_pureMatrix v).symm.trans hv
  have hD : D * Dᴴ = B := (Geometry.traceRight_pureMatrix w).symm.trans hw
  have hCout : krausLiftColumns K C * (krausLiftColumns K C)ᴴ = N.map A := by
    rw [krausLiftColumns_marginal, hC]
    exact (QuantumProver.SuperchannelDiscrimination.CPTPKraus.canonicalKraus_reconstruct
      N.map N.completelyPositive A).symm
  have hDout : krausLiftColumns K D * (krausLiftColumns K D)ᴴ = N.map B := by
    rw [krausLiftColumns_marginal, hD]
    exact (QuantumProver.SuperchannelDiscrimination.CPTPKraus.canonicalKraus_reconstruct
      N.map N.completelyPositive B).symm
  have htr : (Cᴴ * D).trace =
      (CFC.sqrt ((CFC.sqrt A * CFC.sqrt B)ᴴ * (CFC.sqrt A * CFC.sqrt B))).trace := by
    calc
      _ = inner ℂ (WithLp.toLp 2 v) (WithLp.toLp 2 w) :=
        (Geometry.inner_matrixVector C D).symm
      _ = _ := hinner
  have h := norm_trace_factor_overlap_le_rootFidelity
    (krausLiftColumns K C) (krausLiftColumns K D)
  rw [hCout, hDout, krausLiftColumns_trace_overlap K C D hK,
    htr, Geometry.norm_absolute_trace_eq_real_trace] at h
  exact h

end QuantumProver.BellDiagonalSquashedEntanglement.RecoveryGeometry.UhlmannGeometry

namespace QuantumProver.BellDiagonalSquashedEntanglement.RecoveryGeometry.UhlmannGeometry

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem positive_absolute_trace_as_complex (M : Mat I) :
    (CFC.sqrt (Mᴴ * M)).trace = (traceNorm M : ℂ) := by
  have hp : (CFC.sqrt (Mᴴ * M)).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg _)
  calc
    _ = (‖(CFC.sqrt (Mᴴ * M)).trace‖ : ℂ) :=
      Complex.eq_coe_norm_of_nonneg hp.trace_nonneg
    _ = ((CFC.sqrt (Mᴴ * M)).trace.re : ℂ) := by
      rw [Geometry.norm_absolute_trace_eq_real_trace]
    _ = _ := rfl

theorem exists_alignment_to_fixed_purification (A B : Density I)
    (w : I × I → ℂ) (hw : IsDensity (outer w))
    (hMargW : partialTraceRight (outer w) = B.val) :
    ∃ v : I × I → ℂ,
      IsDensity (outer v) ∧ partialTraceRight (outer v) = A.val ∧
      ‖WithLp.toLp 2 v - WithLp.toLp 2 w‖ ^ 2 =
        2 * (1 - rootFidelity A.val B.val) := by
  obtain ⟨x, y, hx, hy, hxy⟩ :=
    Geometry.exists_aligned_squareRoot_purifications A.val B.val A.property.1 B.property.1
  obtain ⟨U, hU, hYU⟩ := Geometry.exists_ancillary_unitary_of_same_marginal
    y w (hy.trans hMargW.symm)
  let v := Geometry.matrixVector (Geometry.columns x * U)
  have hUU : U * Uᴴ = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff.mp hU
  have hm : partialTraceRight (outer v) = A.val := by
    change Geometry.traceRight (Geometry.pureMatrix v) = A.val
    rw [Geometry.traceRight_pureMatrix_matrixVector, Matrix.conjTranspose_mul]
    calc
      _ = Geometry.columns x * (U * Uᴴ) * (Geometry.columns x)ᴴ := by
        simp only [Matrix.mul_assoc]
      _ = A.val := by
        rw [hUU, Matrix.mul_one, ← Geometry.traceRight_pureMatrix, hx]
  have hv : IsDensity (outer v) := by
    refine ⟨Geometry.pureMatrix_posSemidef _, ?_⟩
    change (Geometry.pureMatrix v).trace = 1
    rw [← Geometry.trace_traceRight]
    exact congrArg Matrix.trace hm |>.trans A.property.2
  have hi : inner ℂ (WithLp.toLp 2 v) (WithLp.toLp 2 w) =
      (rootFidelity A.val B.val : ℂ) := by
    calc
      _ = ((Geometry.columns x * U)ᴴ * Geometry.columns w).trace :=
        Geometry.inner_matrixVector _ _
      _ = (Uᴴ * ((Geometry.columns x)ᴴ * Geometry.columns y) * U).trace := by
        rw [hYU, Matrix.conjTranspose_mul]
        simp only [Matrix.mul_assoc]
      _ = ((Geometry.columns x)ᴴ * Geometry.columns y).trace := by
        rw [Matrix.trace_mul_cycle, hUU, Matrix.one_mul]
      _ = inner ℂ (WithLp.toLp 2 x) (WithLp.toLp 2 y) :=
        (Geometry.inner_matrixVector _ _).symm
      _ = _ := hxy.trans (positive_absolute_trace_as_complex _)
  refine ⟨v, hv, hm, ?_⟩
  have h := Geometry.unit_norm_sub_sq (WithLp.toLp 2 v) (WithLp.toLp 2 w)
    (norm_purification_eq_one v hv) (norm_purification_eq_one w hw)
  rw [hi, Complex.ofReal_re] at h
  linarith

theorem rootFidelity_difference_has_bures_budget (A₀ A₁ B₀ B₁ : Density I) :
    ∃ b₀ b₁ : ℝ, 0 ≤ b₀ ∧ 0 ≤ b₁ ∧
      rootFidelity B₀.val B₁.val - rootFidelity A₀.val A₁.val ≤ b₀ + b₁ ∧
      b₀ ^ 2 = 2 * (1 - rootFidelity A₀.val B₀.val) ∧
      b₁ ^ 2 = 2 * (1 - rootFidelity A₁.val B₁.val) := by
  obtain ⟨w₀, w₁, hw₀, hw₁, hm₀, hm₁, hF⟩ :=
    density_has_fidelity_attaining_purifications B₀ B₁
  obtain ⟨v₀, hv₀, hmA₀, hd₀⟩ := exists_alignment_to_fixed_purification A₀ B₀ w₀ hw₀ hm₀
  obtain ⟨v₁, hv₁, hmA₁, hd₁⟩ := exists_alignment_to_fixed_purification A₁ B₁ w₁ hw₁ hm₁
  let b₀ := ‖WithLp.toLp 2 v₀ - WithLp.toLp 2 w₀‖
  let b₁ := ‖WithLp.toLp 2 v₁ - WithLp.toLp 2 w₁‖
  refine ⟨b₀, b₁, norm_nonneg _, norm_nonneg _, ?_, hd₀, hd₁⟩
  have represented_hPhysical := purification_overlap_le_rootFidelity v₀ v₁
  rw [hmA₀, hmA₁] at represented_hPhysical
  have hDifference := Geometry.two_unit_overlap_difference_le
    (WithLp.toLp 2 v₀) (WithLp.toLp 2 v₁) (WithLp.toLp 2 w₀) (WithLp.toLp 2 w₁)
    (norm_purification_eq_one v₁ hv₁) (norm_purification_eq_one w₀ hw₀)
  rw [hF] at hDifference
  have hNeg := neg_le_abs
    (‖inner ℂ (WithLp.toLp 2 v₀) (WithLp.toLp 2 v₁)‖ - rootFidelity B₀.val B₁.val)
  change _ ≤ b₀ + b₁ at hDifference
  linarith

end QuantumProver.BellDiagonalSquashedEntanglement.RecoveryGeometry.UhlmannGeometry

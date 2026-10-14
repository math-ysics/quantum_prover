import Mathlib
import QuantumProver.InformationTheory.ElegantJointMeasurement.IConcurrence
import QuantumProver.InformationTheory.ElegantJointMeasurement.ContinuousInstrumentQuadrature
import QuantumProver.InformationTheory.ElegantJointMeasurement.ContinuousCPInstruments

open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder Matrix Kronecker
open scoped Matrix.Norms.L2Operator
open Filter Topology

namespace QuantumProver.ElegantJointMeasurement.InstrumentNormalization

noncomputable section

set_option maxHeartbeats 600000

variable {κ : Type*} [Fintype κ] [DecidableEq κ]
variable {ι η : ℕ → Type*} [∀ n, Fintype (ι n)] [∀ n, Fintype (η n)]

def gramTotal (K : (n : ℕ) → ι n → Matrix (η n) κ ℂ) (n : ℕ) : Matrix κ κ ℂ :=
  ∑ s, (K n s)ᴴ * K n s

omit [DecidableEq κ] in
theorem gramTotal_posSemidef (K : (n : ℕ) → ι n → Matrix (η n) κ ℂ) (n : ℕ) :
    (gramTotal K n).PosSemidef := by
  exact Matrix.posSemidef_sum _ fun s _ => Matrix.posSemidef_conjTranspose_mul_self (K n s)

theorem eventually_gramTotal_posDef (K : (n : ℕ) → ι n → Matrix (η n) κ ℂ)
    (hK : Tendsto (gramTotal K) atTop (𝓝 1)) :
    ∀ᶠ n in atTop, (gramTotal K n).PosDef := by
  have hd : Tendsto (fun n => (gramTotal K n).det) atTop (𝓝 (1 : ℂ)) := by
    simpa only [Function.comp_def, id_eq, Matrix.det_one] using
      (continuous_id.matrix_det.tendsto (1 : Matrix κ κ ℂ)).comp hK
  filter_upwards [hd.eventually_ne (by norm_num : (1 : ℂ) ≠ 0)] with n hn
  exact (gramTotal_posSemidef K n).posDef_iff_det_ne_zero.mpr hn

def normalizer (K : (n : ℕ) → ι n → Matrix (η n) κ ℂ) (n : ℕ) : Matrix κ κ ℂ := by
  classical
  exact if (gramTotal K n).PosDef then (CFC.sqrt (gramTotal K n))⁻¹ else 1

theorem normalizer_eq_inv_sqrt (K : (n : ℕ) → ι n → Matrix (η n) κ ℂ)
    (n : ℕ) (hn : (gramTotal K n).PosDef) :
    normalizer K n = (CFC.sqrt (gramTotal K n))⁻¹ := by
  simp [normalizer, hn]

theorem normalizer_posSemidef (K : (n : ℕ) → ι n → Matrix (η n) κ ℂ) (n : ℕ) :
    (normalizer K n).PosSemidef := by
  unfold normalizer
  split_ifs
  · exact (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (gramTotal K n))).inv
  · exact Matrix.PosSemidef.one

theorem normalizer_conjTranspose (K : (n : ℕ) → ι n → Matrix (η n) κ ℂ) (n : ℕ) :
    (normalizer K n)ᴴ = normalizer K n :=
  (normalizer_posSemidef K n).isHermitian

theorem normalizer_posDef_of_posDef (K : (n : ℕ) → ι n → Matrix (η n) κ ℂ)
    (n : ℕ) (hn : (gramTotal K n).PosDef) : (normalizer K n).PosDef := by
  rw [normalizer_eq_inv_sqrt K n hn]
  apply Matrix.PosDef.inv
  apply (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (gramTotal K n))).posDef_iff_isUnit.mpr
  exact (CFC.isUnit_sqrt_iff _ hn.posSemidef.nonneg).mpr hn.isUnit

theorem normalizer_gramTotal_normalizer (K : (n : ℕ) → ι n → Matrix (η n) κ ℂ)
    (n : ℕ) (hn : (gramTotal K n).PosDef) :
    normalizer K n * gramTotal K n * normalizer K n = 1 := by
  rw [normalizer_eq_inv_sqrt K n hn]
  have hs : IsUnit (CFC.sqrt (gramTotal K n)) :=
    (CFC.isUnit_sqrt_iff _ hn.posSemidef.nonneg).mpr hn.isUnit
  let _ := hs.invertible
  have hsq : CFC.sqrt (gramTotal K n) * CFC.sqrt (gramTotal K n) = gramTotal K n := by
    simpa only [pow_two] using CFC.sq_sqrt (gramTotal K n) hn.posSemidef.nonneg
  calc
    (CFC.sqrt (gramTotal K n))⁻¹ * gramTotal K n * (CFC.sqrt (gramTotal K n))⁻¹ =
        (CFC.sqrt (gramTotal K n))⁻¹ *
          (CFC.sqrt (gramTotal K n) * CFC.sqrt (gramTotal K n)) *
          (CFC.sqrt (gramTotal K n))⁻¹ := by rw [hsq]
    _ = 1 := by
      rw [← Matrix.mul_assoc, Matrix.inv_mul_of_invertible, Matrix.one_mul,
        Matrix.mul_inv_of_invertible]

theorem sqrt_gramTotal_tendsto (K : (n : ℕ) → ι n → Matrix (η n) κ ℂ)
    (hK : Tendsto (gramTotal K) atTop (𝓝 1)) :
    Tendsto (fun n => CFC.sqrt (gramTotal K n)) atTop (𝓝 1) := by
  have hwithin : Tendsto (gramTotal K) atTop (𝓝[{A : Matrix κ κ ℂ | 0 ≤ A}] 1) :=
    tendsto_nhdsWithin_iff.mpr ⟨hK,
      Filter.Eventually.of_forall (fun n => (gramTotal_posSemidef K n).nonneg)⟩
  have hmem : (1 : Matrix κ κ ℂ) ∈ {A : Matrix κ κ ℂ | 0 ≤ A} := by
    change (0 : Matrix κ κ ℂ) ≤ 1
    exact Matrix.PosSemidef.one.nonneg
  simpa only [Function.comp_def, CFC.sqrt_one] using
    (CFC.continuousOn_sqrt.continuousWithinAt hmem).tendsto.comp hwithin

theorem normalizer_tendsto (K : (n : ℕ) → ι n → Matrix (η n) κ ℂ)
    (hK : Tendsto (gramTotal K) atTop (𝓝 1)) :
    Tendsto (normalizer K) atTop (𝓝 1) := by
  have hi : ContinuousAt (fun A : Matrix κ κ ℂ => A⁻¹) 1 :=
    continuousAt_matrix_inv 1 (by
      simpa only [Matrix.det_one, Units.val_one] using
        NormedRing.inverse_continuousAt (1 : ℂˣ))
  have ht : Tendsto (fun n => (CFC.sqrt (gramTotal K n))⁻¹) atTop (𝓝 1) := by
    simpa only [Function.comp_def, inv_one] using
      hi.tendsto.comp (sqrt_gramTotal_tendsto K hK)
  apply ht.congr'
  filter_upwards [eventually_gramTotal_posDef K hK] with n hn
  exact (normalizer_eq_inv_sqrt K n hn).symm

def normalizedKraus (K : (n : ℕ) → ι n → Matrix (η n) κ ℂ)
    (n : ℕ) (s : ι n) : Matrix (η n) κ ℂ := K n s * normalizer K n

theorem normalizedKraus_gramTotal (K : (n : ℕ) → ι n → Matrix (η n) κ ℂ) (n : ℕ) :
    (∑ s, (normalizedKraus K n s)ᴴ * normalizedKraus K n s) =
      (normalizer K n)ᴴ * gramTotal K n * normalizer K n := by
  simp only [normalizedKraus, Matrix.conjTranspose_mul, gramTotal, Matrix.mul_sum,
    Matrix.sum_mul, Matrix.mul_assoc]

theorem normalizedKraus_complete_of_posDef (K : (n : ℕ) → ι n → Matrix (η n) κ ℂ)
    (n : ℕ) (hn : (gramTotal K n).PosDef) :
    (∑ s, (normalizedKraus K n s)ᴴ * normalizedKraus K n s) = 1 := by
  rw [normalizedKraus_gramTotal, normalizer_conjTranspose]
  exact normalizer_gramTotal_normalizer K n hn

theorem normalizedKraus_complete (K : (n : ℕ) → ι n → Matrix (η n) κ ℂ)
    (hK : Tendsto (gramTotal K) atTop (𝓝 1)) :
    ∀ᶠ n in atTop, (∑ s, (normalizedKraus K n s)ᴴ * normalizedKraus K n s) = 1 := by
  filter_upwards [eventually_gramTotal_posDef K hK] with n hn
  exact normalizedKraus_complete_of_posDef K n hn

theorem normalized_effect_limit {J : Type*} [Fintype J]
    (K : (n : ℕ) → ι n → Matrix (η n) κ ℂ)
    (hK : Tendsto (gramTotal K) atTop (𝓝 1))
    (F : ℕ → J → Matrix κ κ ℂ) (F₀ : J → Matrix κ κ ℂ)
    (hF : Tendsto F atTop (𝓝 F₀)) :
    Tendsto (fun n j => (normalizer K n)ᴴ * F n j * normalizer K n)
      atTop (𝓝 F₀) := by
  apply tendsto_pi_nhds.mpr
  intro j
  have hN := normalizer_tendsto K hK
  have hNH : Tendsto (fun n => (normalizer K n)ᴴ) atTop (𝓝 (1 : Matrix κ κ ℂ)) := by
    simpa only [Function.comp_def, id_eq, Matrix.conjTranspose_one] using
      (continuous_id.matrix_conjTranspose.tendsto (1 : Matrix κ κ ℂ)).comp hN
  simpa only [Matrix.one_mul, Matrix.mul_one] using
    (hNH.mul (tendsto_pi_nhds.mp hF j)).mul hN

def localNormalizer {ν : Type*} [Fintype ν] [DecidableEq ν]
    (K : (n : ℕ) → ι n → Matrix (η n) κ ℂ) (n : ℕ) :
    Matrix (κ × ν) (κ × ν) ℂ := normalizer K n ⊗ₖ (1 : Matrix ν ν ℂ)

theorem localNormalizer_tendsto {ν : Type*} [Fintype ν] [DecidableEq ν]
    (K : (n : ℕ) → ι n → Matrix (η n) κ ℂ)
    (hK : Tendsto (gramTotal K) atTop (𝓝 1)) :
    Tendsto (localNormalizer (ν := ν) K) atTop (𝓝 1) := by
  have hc : Continuous (fun A : Matrix κ κ ℂ => A ⊗ₖ (1 : Matrix ν ν ℂ)) := by
    apply continuous_matrix
    intro i j
    change Continuous (fun A : Matrix κ κ ℂ => A i.1 j.1 * (1 : Matrix ν ν ℂ) i.2 j.2)
    exact (continuous_apply_apply i.1 j.1).mul continuous_const
  change Tendsto (fun n => normalizer K n ⊗ₖ (1 : Matrix ν ν ℂ)) atTop (𝓝 1)
  simpa only [Function.comp_def, Matrix.one_kronecker_one] using
    (hc.tendsto (1 : Matrix κ κ ℂ)).comp (normalizer_tendsto K hK)

theorem normalized_local_effect_limit {ν J : Type*}
    [Fintype ν] [DecidableEq ν] [Fintype J]
    (K : (n : ℕ) → ι n → Matrix (η n) κ ℂ)
    (hK : Tendsto (gramTotal K) atTop (𝓝 1))
    (F : ℕ → J → Matrix (κ × ν) (κ × ν) ℂ)
    (F₀ : J → Matrix (κ × ν) (κ × ν) ℂ)
    (hF : Tendsto F atTop (𝓝 F₀)) :
    Tendsto (fun n j => (localNormalizer K n)ᴴ * F n j * localNormalizer K n)
      atTop (𝓝 F₀) := by
  apply tendsto_pi_nhds.mpr
  intro j
  have hN := localNormalizer_tendsto (ν := ν) K hK
  have hNH : Tendsto (fun n => (localNormalizer (ν := ν) K n)ᴴ)
      atTop (𝓝 (1 : Matrix (κ × ν) (κ × ν) ℂ)) := by
    simpa only [Function.comp_def, id_eq, Matrix.conjTranspose_one] using
      (continuous_id.matrix_conjTranspose.tendsto (1 : Matrix (κ × ν) (κ × ν) ℂ)).comp hN
  simpa only [Matrix.one_mul, Matrix.mul_one] using
    (hNH.mul (tendsto_pi_nhds.mp hF j)).mul hN

def groupedEffect {J : Type*} [DecidableEq J]
    (K : (n : ℕ) → ι n → Matrix (η n) κ ℂ)
    (report : (n : ℕ) → ι n → J) (n : ℕ) (j : J) : Matrix κ κ ℂ :=
  ∑ s, if report n s = j then (K n s)ᴴ * K n s else 0

theorem normalized_groupedEffect_eq {J : Type*} [DecidableEq J]
    (K : (n : ℕ) → ι n → Matrix (η n) κ ℂ)
    (report : (n : ℕ) → ι n → J) (n : ℕ) (j : J) :
    groupedEffect (normalizedKraus K) report n j =
      (normalizer K n)ᴴ * groupedEffect K report n j * normalizer K n := by
  unfold groupedEffect
  simp only [Matrix.mul_sum, Matrix.sum_mul]
  apply Finset.sum_congr rfl
  intro s hs
  split_ifs
  · simp only [normalizedKraus, Matrix.conjTranspose_mul, Matrix.mul_assoc]
  · simp

theorem finite_quadrature_normalization {J : Type*} [Fintype J] [DecidableEq J]
    (K : (n : ℕ) → ι n → Matrix (η n) κ ℂ)
    (report : (n : ℕ) → ι n → J) (F₀ : J → Matrix κ κ ℂ)
    (hK : Tendsto (gramTotal K) atTop (𝓝 1))
    (hF : Tendsto (groupedEffect K report) atTop (𝓝 F₀)) :
    (∀ᶠ n in atTop, (∑ s, (normalizedKraus K n s)ᴴ * normalizedKraus K n s) = 1) ∧
      Tendsto (normalizer K) atTop (𝓝 1) ∧
      Tendsto (groupedEffect (normalizedKraus K) report) atTop (𝓝 F₀) := by
  refine ⟨normalizedKraus_complete K hK, normalizer_tendsto K hK, ?_⟩
  apply (normalized_effect_limit K hK (groupedEffect K report) F₀ hF).congr'
  exact Filter.Eventually.of_forall fun n =>
    funext fun j => (normalized_groupedEffect_eq K report n j).symm

theorem finite_quadrature_normalization_shift {J : Type*} [Fintype J] [DecidableEq J]
    (K : (n : ℕ) → ι n → Matrix (η n) κ ℂ)
    (report : (n : ℕ) → ι n → J) (F₀ : J → Matrix κ κ ℂ)
    (hK : Tendsto (gramTotal K) atTop (𝓝 1))
    (hF : Tendsto (groupedEffect K report) atTop (𝓝 F₀)) :
    ∃ N : ℕ,
      (∀ n, (∑ s, (normalizedKraus K (n + N) s)ᴴ * normalizedKraus K (n + N) s) = 1) ∧
      Tendsto (fun n => normalizer K (n + N)) atTop (𝓝 1) ∧
      Tendsto (fun n => groupedEffect (normalizedKraus K) report (n + N)) atTop (𝓝 F₀) := by
  obtain ⟨hc, hN, hF'⟩ := finite_quadrature_normalization K report F₀ hK hF
  obtain ⟨N, htail⟩ := eventually_atTop.mp hc
  refine ⟨N, fun n => htail (n + N) (by omega), ?_, ?_⟩
  · simpa only [Function.comp_def] using hN.comp (tendsto_add_atTop_nat N)
  · simpa only [Function.comp_def] using hF'.comp (tendsto_add_atTop_nat N)

omit [Fintype κ] [DecidableEq κ] in

theorem tendsto_matrix_iff_entries {X : Type*} {l : Filter X}
    (A : X → Matrix κ κ ℂ) (A₀ : Matrix κ κ ℂ) :
    Tendsto A l (𝓝 A₀) ↔ ∀ i j, Tendsto (fun x => A x i j) l (𝓝 (A₀ i j)) := by
  constructor
  · intro h i j
    exact tendsto_pi_nhds.mp (tendsto_pi_nhds.mp h i) j
  · intro h
    exact tendsto_pi_nhds.mpr fun i => tendsto_pi_nhds.mpr fun j => h i j

end
end QuantumProver.ElegantJointMeasurement.InstrumentNormalization

namespace QuantumProver.ElegantJointMeasurement.InstrumentNormalization

noncomputable section

open QuantumProver.ElegantJointMeasurement.CP
open QuantumProver.ElegantJointMeasurement.CP.FiniteLocalCPInstrumentTree

variable {m n p r : ℕ}

def singleKrausMap {I O : Type*} [Fintype I] [Fintype O]
    [DecidableEq I] [DecidableEq O] (A : Matrix O I ℂ) :
    Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ :=
  QuantumProver.ElegantJointMeasurement.CP.krausMap (fun _ : Unit => A)

theorem singleKrausMap_completelyPositive {I O : Type*} [Fintype I] [Fintype O]
    [DecidableEq I] [DecidableEq O] (A : Matrix O I ℂ) :
    QuantumProver.ElegantJointMeasurement.CP.CompletelyPositive (singleKrausMap A) :=
  QuantumProver.ElegantJointMeasurement.CP.krausMap_completelyPositive (fun _ : Unit => A)

theorem singleKrausMap_total_trace_preserving {I O S : Type*}
    [Fintype I] [Fintype O] [Fintype S] [DecidableEq I] [DecidableEq O]
    (A : S → Matrix O I ℂ) (hA : (∑ s, (A s)ᴴ * A s) = 1)
    (X : Matrix I I ℂ) : (∑ s, singleKrausMap (A s) X).trace = X.trace := by
  have heq : (∑ s, singleKrausMap (A s) X) = QuantumProver.ElegantJointMeasurement.CP.krausMap A X := by
    simp [singleKrausMap, QuantumProver.ElegantJointMeasurement.CP.krausMap]
  rw [heq]
  exact (QuantumProver.ElegantJointMeasurement.CP.krausMap_trace_preserving_iff A).mpr hA X

theorem singleKrausMap_leftApplication (A : Matrix (Fin p) (Fin m) ℂ)
    (X : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) :
    QuantumProver.ElegantJointMeasurement.CP.leftApplication (singleKrausMap A) X = QuantumProver.ElegantJointMeasurement.CP.leftKrausApplication A X := by
  ext i j
  rw [QuantumProver.ElegantJointMeasurement.CP.leftKrausApplication_block A X i.1 j.1 i.2 j.2]
  simp [QuantumProver.ElegantJointMeasurement.CP.leftApplication, singleKrausMap, QuantumProver.ElegantJointMeasurement.CP.krausMap]
  rfl

theorem singleKrausMap_rightApplication (A : Matrix (Fin p) (Fin n) ℂ)
    (X : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) :
    QuantumProver.ElegantJointMeasurement.CP.rightApplication (singleKrausMap A) X = QuantumProver.ElegantJointMeasurement.CP.rightKrausApplication A X := by
  ext i j
  rw [QuantumProver.ElegantJointMeasurement.CP.rightKrausApplication_block A X i.1 j.1 i.2 j.2]
  simp [QuantumProver.ElegantJointMeasurement.CP.rightApplication, singleKrausMap, QuantumProver.ElegantJointMeasurement.CP.krausMap]
  rfl

def krausAliceNode (A : Fin r → Matrix (Fin p) (Fin m) ℂ)
    (hA : (∑ s, (A s)ᴴ * A s) = 1)
    (next : Fin r → QuantumProver.ElegantJointMeasurement.CP.FiniteLocalCPInstrumentTree p n) :
    QuantumProver.ElegantJointMeasurement.CP.FiniteLocalCPInstrumentTree m n :=
  .alice m n p r (fun s => singleKrausMap (A s))
    (fun s => singleKrausMap_completelyPositive (A s))
    (singleKrausMap_total_trace_preserving A hA) next

def krausBobNode (A : Fin r → Matrix (Fin p) (Fin n) ℂ)
    (hA : (∑ s, (A s)ᴴ * A s) = 1)
    (next : Fin r → QuantumProver.ElegantJointMeasurement.CP.FiniteLocalCPInstrumentTree m p) :
    QuantumProver.ElegantJointMeasurement.CP.FiniteLocalCPInstrumentTree m n :=
  .bob m n p r (fun s => singleKrausMap (A s))
    (fun s => singleKrausMap_completelyPositive (A s))
    (singleKrausMap_total_trace_preserving A hA) next

def krausAliceLabels {L : Type*} (A : Fin r → Matrix (Fin p) (Fin m) ℂ)
    (hA : (∑ s, (A s)ᴴ * A s) = 1)
    (next : Fin r → QuantumProver.ElegantJointMeasurement.CP.FiniteLocalCPInstrumentTree p n)
    (labels : ∀ s, LeafLabels (next s) L) : LeafLabels (krausAliceNode A hA next) L := labels

def krausBobLabels {L : Type*} (A : Fin r → Matrix (Fin p) (Fin n) ℂ)
    (hA : (∑ s, (A s)ᴴ * A s) = 1)
    (next : Fin r → QuantumProver.ElegantJointMeasurement.CP.FiniteLocalCPInstrumentTree m p)
    (labels : ∀ s, LeafLabels (next s) L) : LeafLabels (krausBobNode A hA next) L := labels

def aliceConditionalEffect {L : Type*} [DecidableEq L]
    (A : Fin r → Matrix (Fin p) (Fin m) ℂ)
    (next : Fin r → QuantumProver.ElegantJointMeasurement.CP.FiniteLocalCPInstrumentTree p n)
    (labels : ∀ s, LeafLabels (next s) L) (ell : L) :
    Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ :=
  ∑ s, (A s ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ))ᴴ *
    (next s).matrixReportedEffect (labels s) ell *
    (A s ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ))

def bobConditionalEffect {L : Type*} [DecidableEq L]
    (A : Fin r → Matrix (Fin p) (Fin n) ℂ)
    (next : Fin r → QuantumProver.ElegantJointMeasurement.CP.FiniteLocalCPInstrumentTree m p)
    (labels : ∀ s, LeafLabels (next s) L) (ell : L) :
    Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ :=
  ∑ s, ((1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ A s)ᴴ *
    (next s).matrixReportedEffect (labels s) ell *
    ((1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ A s)

theorem trace_pullback_sandwich {I O : Type*} [Fintype I] [Fintype O]
    (A : Matrix O I ℂ) (D : Matrix O O ℂ) (X : Matrix I I ℂ) :
    (D * (A * X * Aᴴ)).trace = ((Aᴴ * D * A) * X).trace := by
  calc
    _ = ((D * A) * X * Aᴴ).trace := by simp only [Matrix.mul_assoc]
    _ = (Aᴴ * (D * A) * X).trace := Matrix.trace_mul_cycle (D * A) X Aᴴ
    _ = _ := by simp only [Matrix.mul_assoc]

theorem pullback_mul {I O : Type*} [Fintype I] [Fintype O]
    (A : Matrix O I ℂ) (R : Matrix I I ℂ) (D : Matrix O O ℂ) :
    (A * R)ᴴ * D * (A * R) = Rᴴ * (Aᴴ * D * A) * R := by
  rw [Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]

theorem krausAliceNode_matrixReportedEffect {L : Type*} [DecidableEq L]
    (A : Fin r → Matrix (Fin p) (Fin m) ℂ)
    (hA : (∑ s, (A s)ᴴ * A s) = 1)
    (next : Fin r → QuantumProver.ElegantJointMeasurement.CP.FiniteLocalCPInstrumentTree p n)
    (labels : ∀ s, LeafLabels (next s) L) (ell : L) :
    (krausAliceNode A hA next).matrixReportedEffect (krausAliceLabels A hA next labels) ell =
      aliceConditionalEffect A next labels ell := by
  symm
  apply (krausAliceNode A hA next).matrixReportedEffect_unique
    (krausAliceLabels A hA next labels) ell
  intro X
  simp only [krausAliceNode, krausAliceLabels, matrixReportedEvaluation,
    LinearMap.sum_apply, LinearMap.comp_apply, singleKrausMap_leftApplication,
    matrixReportedEvaluation_eq_trace_effect, QuantumProver.ElegantJointMeasurement.CP.leftKrausApplication,
    trace_pullback_sandwich, aliceConditionalEffect, Matrix.sum_mul, Matrix.trace_sum]

theorem krausBobNode_matrixReportedEffect {L : Type*} [DecidableEq L]
    (A : Fin r → Matrix (Fin p) (Fin n) ℂ)
    (hA : (∑ s, (A s)ᴴ * A s) = 1)
    (next : Fin r → QuantumProver.ElegantJointMeasurement.CP.FiniteLocalCPInstrumentTree m p)
    (labels : ∀ s, LeafLabels (next s) L) (ell : L) :
    (krausBobNode A hA next).matrixReportedEffect (krausBobLabels A hA next labels) ell =
      bobConditionalEffect A next labels ell := by
  symm
  apply (krausBobNode A hA next).matrixReportedEffect_unique
    (krausBobLabels A hA next labels) ell
  intro X
  simp only [krausBobNode, krausBobLabels, matrixReportedEvaluation,
    LinearMap.sum_apply, LinearMap.comp_apply, singleKrausMap_rightApplication,
    matrixReportedEvaluation_eq_trace_effect, QuantumProver.ElegantJointMeasurement.CP.rightKrausApplication,
    trace_pullback_sandwich, bobConditionalEffect, Matrix.sum_mul, Matrix.trace_sum]

variable {output outcomes : ℕ → ℕ}

def normalizedAliceNode
    (K : (a : ℕ) → Fin (outcomes a) → Matrix (Fin (output a)) (Fin m) ℂ)
    (a : ℕ) (ha : (gramTotal K a).PosDef)
    (next : Fin (outcomes a) → QuantumProver.ElegantJointMeasurement.CP.FiniteLocalCPInstrumentTree (output a) n) :
    QuantumProver.ElegantJointMeasurement.CP.FiniteLocalCPInstrumentTree m n :=
  krausAliceNode (normalizedKraus K a) (normalizedKraus_complete_of_posDef K a ha) next

def normalizedBobNode
    (K : (a : ℕ) → Fin (outcomes a) → Matrix (Fin (output a)) (Fin n) ℂ)
    (a : ℕ) (ha : (gramTotal K a).PosDef)
    (next : Fin (outcomes a) → QuantumProver.ElegantJointMeasurement.CP.FiniteLocalCPInstrumentTree m (output a)) :
    QuantumProver.ElegantJointMeasurement.CP.FiniteLocalCPInstrumentTree m n :=
  krausBobNode (normalizedKraus K a) (normalizedKraus_complete_of_posDef K a ha) next

def normalizedAliceLabels {L : Type*}
    (K : (a : ℕ) → Fin (outcomes a) → Matrix (Fin (output a)) (Fin m) ℂ)
    (a : ℕ) (ha : (gramTotal K a).PosDef)
    (next : Fin (outcomes a) → QuantumProver.ElegantJointMeasurement.CP.FiniteLocalCPInstrumentTree (output a) n)
    (labels : ∀ s, LeafLabels (next s) L) : LeafLabels (normalizedAliceNode K a ha next) L :=
  krausAliceLabels _ _ next labels

def normalizedBobLabels {L : Type*}
    (K : (a : ℕ) → Fin (outcomes a) → Matrix (Fin (output a)) (Fin n) ℂ)
    (a : ℕ) (ha : (gramTotal K a).PosDef)
    (next : Fin (outcomes a) → QuantumProver.ElegantJointMeasurement.CP.FiniteLocalCPInstrumentTree m (output a))
    (labels : ∀ s, LeafLabels (next s) L) : LeafLabels (normalizedBobNode K a ha next) L :=
  krausBobLabels _ _ next labels

def rightLocalNormalizer {κ ν : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ν] [DecidableEq ν] {ι η : ℕ → Type*}
    [∀ a, Fintype (ι a)] [∀ a, Fintype (η a)]
    (K : (a : ℕ) → ι a → Matrix (η a) κ ℂ) (a : ℕ) :
    Matrix (ν × κ) (ν × κ) ℂ := (1 : Matrix ν ν ℂ) ⊗ₖ normalizer K a

theorem normalizedAliceNode_effect {L : Type*} [DecidableEq L]
    (K : (a : ℕ) → Fin (outcomes a) → Matrix (Fin (output a)) (Fin m) ℂ)
    (a : ℕ) (ha : (gramTotal K a).PosDef)
    (next : Fin (outcomes a) → QuantumProver.ElegantJointMeasurement.CP.FiniteLocalCPInstrumentTree (output a) n)
    (labels : ∀ s, LeafLabels (next s) L) (ell : L) :
    (normalizedAliceNode K a ha next).matrixReportedEffect
      (normalizedAliceLabels K a ha next labels) ell =
      (localNormalizer K a)ᴴ * aliceConditionalEffect (K a) next labels ell * localNormalizer K a := by
  change (krausAliceNode (normalizedKraus K a) _ next).matrixReportedEffect
    (krausAliceLabels _ _ next labels) ell = _
  rw [krausAliceNode_matrixReportedEffect]
  simp only [aliceConditionalEffect, Matrix.mul_sum, Matrix.sum_mul]
  apply Finset.sum_congr rfl
  intro s hs
  have heq : normalizedKraus K a s ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ) =
      (K a s ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ)) * localNormalizer K a := by
    change (K a s * normalizer K a) ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ) =
      (K a s ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ)) *
        (normalizer K a ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ))
    rw [← Matrix.mul_kronecker_mul, Matrix.one_mul]
  calc
    _ = ((K a s ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ)) * localNormalizer K a)ᴴ *
        (next s).matrixReportedEffect (labels s) ell *
        ((K a s ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ)) * localNormalizer K a) :=
      congrArg (fun B : Matrix (Fin (output a) × Fin n) (Fin m × Fin n) ℂ =>
        Bᴴ * (next s).matrixReportedEffect (labels s) ell * B) heq
    _ = _ := pullback_mul _ _ _

theorem normalizedBobNode_effect {L : Type*} [DecidableEq L]
    (K : (a : ℕ) → Fin (outcomes a) → Matrix (Fin (output a)) (Fin n) ℂ)
    (a : ℕ) (ha : (gramTotal K a).PosDef)
    (next : Fin (outcomes a) → QuantumProver.ElegantJointMeasurement.CP.FiniteLocalCPInstrumentTree m (output a))
    (labels : ∀ s, LeafLabels (next s) L) (ell : L) :
    (normalizedBobNode K a ha next).matrixReportedEffect
      (normalizedBobLabels K a ha next labels) ell =
      (rightLocalNormalizer K a)ᴴ * bobConditionalEffect (K a) next labels ell *
        rightLocalNormalizer K a := by
  change (krausBobNode (normalizedKraus K a) _ next).matrixReportedEffect
    (krausBobLabels _ _ next labels) ell = _
  rw [krausBobNode_matrixReportedEffect]
  simp only [bobConditionalEffect, Matrix.mul_sum, Matrix.sum_mul]
  apply Finset.sum_congr rfl
  intro s hs
  have heq : (1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ normalizedKraus K a s =
      ((1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ K a s) * rightLocalNormalizer K a := by
    change (1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ (K a s * normalizer K a) =
      ((1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ K a s) *
        ((1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ normalizer K a)
    rw [← Matrix.mul_kronecker_mul, Matrix.one_mul]
  calc
    _ = (((1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ K a s) * rightLocalNormalizer K a)ᴴ *
        (next s).matrixReportedEffect (labels s) ell *
        (((1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ K a s) * rightLocalNormalizer K a) :=
      congrArg (fun B : Matrix (Fin m × Fin (output a)) (Fin m × Fin n) ℂ =>
        Bᴴ * (next s).matrixReportedEffect (labels s) ell * B) heq
    _ = _ := pullback_mul _ _ _

theorem normalizedAliceNode_complete {L : Type*} [Fintype L] [DecidableEq L]
    (K : (a : ℕ) → Fin (outcomes a) → Matrix (Fin (output a)) (Fin m) ℂ)
    (a : ℕ) (ha : (gramTotal K a).PosDef)
    (next : Fin (outcomes a) → QuantumProver.ElegantJointMeasurement.CP.FiniteLocalCPInstrumentTree (output a) n)
    (labels : ∀ s, LeafLabels (next s) L) :
    (∑ ell, (normalizedAliceNode K a ha next).matrixReportedEffect
      (normalizedAliceLabels K a ha next labels) ell) = 1 :=
  (normalizedAliceNode K a ha next).sum_matrixReportedEffect _

theorem normalizedBobNode_complete {L : Type*} [Fintype L] [DecidableEq L]
    (K : (a : ℕ) → Fin (outcomes a) → Matrix (Fin (output a)) (Fin n) ℂ)
    (a : ℕ) (ha : (gramTotal K a).PosDef)
    (next : Fin (outcomes a) → QuantumProver.ElegantJointMeasurement.CP.FiniteLocalCPInstrumentTree m (output a))
    (labels : ∀ s, LeafLabels (next s) L) :
    (∑ ell, (normalizedBobNode K a ha next).matrixReportedEffect
      (normalizedBobLabels K a ha next labels) ell) = 1 :=
  (normalizedBobNode K a ha next).sum_matrixReportedEffect _

theorem rightLocalNormalizer_tendsto {κ ν : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ν] [DecidableEq ν] {ι η : ℕ → Type*}
    [∀ a, Fintype (ι a)] [∀ a, Fintype (η a)]
    (K : (a : ℕ) → ι a → Matrix (η a) κ ℂ)
    (hK : Tendsto (gramTotal K) atTop (𝓝 1)) :
    Tendsto (rightLocalNormalizer (ν := ν) K) atTop (𝓝 1) := by
  have hc : Continuous (fun A : Matrix κ κ ℂ => (1 : Matrix ν ν ℂ) ⊗ₖ A) := by
    apply continuous_matrix
    intro i j
    change Continuous (fun A : Matrix κ κ ℂ => (1 : Matrix ν ν ℂ) i.1 j.1 * A i.2 j.2)
    exact continuous_const.mul (continuous_apply_apply i.2 j.2)
  change Tendsto (fun a => (1 : Matrix ν ν ℂ) ⊗ₖ normalizer K a) atTop (𝓝 1)
  simpa only [Function.comp_def, Matrix.one_kronecker_one] using
    (hc.tendsto (1 : Matrix κ κ ℂ)).comp (normalizer_tendsto K hK)

theorem normalized_right_local_effect_limit {κ ν L : Type*}
    [Fintype κ] [DecidableEq κ] [Fintype ν] [DecidableEq ν] [Fintype L]
    {ι η : ℕ → Type*} [∀ a, Fintype (ι a)] [∀ a, Fintype (η a)]
    (K : (a : ℕ) → ι a → Matrix (η a) κ ℂ)
    (hK : Tendsto (gramTotal K) atTop (𝓝 1))
    (F : ℕ → L → Matrix (ν × κ) (ν × κ) ℂ)
    (F₀ : L → Matrix (ν × κ) (ν × κ) ℂ)
    (hF : Tendsto F atTop (𝓝 F₀)) :
    Tendsto (fun a ell => (rightLocalNormalizer K a)ᴴ * F a ell * rightLocalNormalizer K a)
      atTop (𝓝 F₀) := by
  apply tendsto_pi_nhds.mpr
  intro ell
  have hN := rightLocalNormalizer_tendsto (ν := ν) K hK
  have hNH : Tendsto (fun a => (rightLocalNormalizer (ν := ν) K a)ᴴ)
      atTop (𝓝 (1 : Matrix (ν × κ) (ν × κ) ℂ)) := by
    simpa only [Function.comp_def, id_eq, Matrix.conjTranspose_one] using
      (continuous_id.matrix_conjTranspose.tendsto (1 : Matrix (ν × κ) (ν × κ) ℂ)).comp hN
  simpa only [Matrix.one_mul, Matrix.mul_one] using
    (hNH.mul (tendsto_pi_nhds.mp hF ell)).mul hN

def normalizationShift {κ : Type*} [Fintype κ] [DecidableEq κ]
    {ι η : ℕ → Type*} [∀ a, Fintype (ι a)] [∀ a, Fintype (η a)]
    (K : (a : ℕ) → ι a → Matrix (η a) κ ℂ)
    (hK : Tendsto (gramTotal K) atTop (𝓝 1)) : ℕ :=
  Classical.choose (eventually_atTop.mp (eventually_gramTotal_posDef K hK))

theorem normalizationShift_posDef {κ : Type*} [Fintype κ] [DecidableEq κ]
    {ι η : ℕ → Type*} [∀ a, Fintype (ι a)] [∀ a, Fintype (η a)]
    (K : (a : ℕ) → ι a → Matrix (η a) κ ℂ)
    (hK : Tendsto (gramTotal K) atTop (𝓝 1)) (a : ℕ) :
    (gramTotal K (a + normalizationShift K hK)).PosDef := by
  have htail := Classical.choose_spec (eventually_atTop.mp (eventually_gramTotal_posDef K hK))
  exact htail _ (by change normalizationShift K hK ≤ a + normalizationShift K hK; omega)

def normalizedAliceShiftNode
    (K : (a : ℕ) → Fin (outcomes a) → Matrix (Fin (output a)) (Fin m) ℂ)
    (hK : Tendsto (gramTotal K) atTop (𝓝 1))
    (next : (a : ℕ) → Fin (outcomes a) → QuantumProver.ElegantJointMeasurement.CP.FiniteLocalCPInstrumentTree (output a) n)
    (a : ℕ) : QuantumProver.ElegantJointMeasurement.CP.FiniteLocalCPInstrumentTree m n :=
  normalizedAliceNode K (a + normalizationShift K hK)
    (normalizationShift_posDef K hK a) (next (a + normalizationShift K hK))

def normalizedBobShiftNode
    (K : (a : ℕ) → Fin (outcomes a) → Matrix (Fin (output a)) (Fin n) ℂ)
    (hK : Tendsto (gramTotal K) atTop (𝓝 1))
    (next : (a : ℕ) → Fin (outcomes a) → QuantumProver.ElegantJointMeasurement.CP.FiniteLocalCPInstrumentTree m (output a))
    (a : ℕ) : QuantumProver.ElegantJointMeasurement.CP.FiniteLocalCPInstrumentTree m n :=
  normalizedBobNode K (a + normalizationShift K hK)
    (normalizationShift_posDef K hK a) (next (a + normalizationShift K hK))

def normalizedAliceShiftLabels {L : Type*}
    (K : (a : ℕ) → Fin (outcomes a) → Matrix (Fin (output a)) (Fin m) ℂ)
    (hK : Tendsto (gramTotal K) atTop (𝓝 1))
    (next : (a : ℕ) → Fin (outcomes a) → QuantumProver.ElegantJointMeasurement.CP.FiniteLocalCPInstrumentTree (output a) n)
    (labels : ∀ a s, LeafLabels (next a s) L) (a : ℕ) :
    LeafLabels (normalizedAliceShiftNode K hK next a) L :=
  normalizedAliceLabels K (a + normalizationShift K hK)
    (normalizationShift_posDef K hK a) (next (a + normalizationShift K hK))
    (labels (a + normalizationShift K hK))

def normalizedBobShiftLabels {L : Type*}
    (K : (a : ℕ) → Fin (outcomes a) → Matrix (Fin (output a)) (Fin n) ℂ)
    (hK : Tendsto (gramTotal K) atTop (𝓝 1))
    (next : (a : ℕ) → Fin (outcomes a) → QuantumProver.ElegantJointMeasurement.CP.FiniteLocalCPInstrumentTree m (output a))
    (labels : ∀ a s, LeafLabels (next a s) L) (a : ℕ) :
    LeafLabels (normalizedBobShiftNode K hK next a) L :=
  normalizedBobLabels K (a + normalizationShift K hK)
    (normalizationShift_posDef K hK a) (next (a + normalizationShift K hK))
    (labels (a + normalizationShift K hK))

theorem normalizedAliceShiftNode_effect {L : Type*} [DecidableEq L]
    (K : (a : ℕ) → Fin (outcomes a) → Matrix (Fin (output a)) (Fin m) ℂ)
    (hK : Tendsto (gramTotal K) atTop (𝓝 1))
    (next : (a : ℕ) → Fin (outcomes a) → QuantumProver.ElegantJointMeasurement.CP.FiniteLocalCPInstrumentTree (output a) n)
    (labels : ∀ a s, LeafLabels (next a s) L) (a : ℕ) (ell : L) :
    (normalizedAliceShiftNode K hK next a).matrixReportedEffect
      (normalizedAliceShiftLabels K hK next labels a) ell =
      (localNormalizer K (a + normalizationShift K hK))ᴴ *
        aliceConditionalEffect (K (a + normalizationShift K hK))
          (next (a + normalizationShift K hK)) (labels (a + normalizationShift K hK)) ell *
        localNormalizer K (a + normalizationShift K hK) :=
  normalizedAliceNode_effect K _ (normalizationShift_posDef K hK a) _ _ ell

theorem normalizedBobShiftNode_effect {L : Type*} [DecidableEq L]
    (K : (a : ℕ) → Fin (outcomes a) → Matrix (Fin (output a)) (Fin n) ℂ)
    (hK : Tendsto (gramTotal K) atTop (𝓝 1))
    (next : (a : ℕ) → Fin (outcomes a) → QuantumProver.ElegantJointMeasurement.CP.FiniteLocalCPInstrumentTree m (output a))
    (labels : ∀ a s, LeafLabels (next a s) L) (a : ℕ) (ell : L) :
    (normalizedBobShiftNode K hK next a).matrixReportedEffect
      (normalizedBobShiftLabels K hK next labels a) ell =
      (rightLocalNormalizer K (a + normalizationShift K hK))ᴴ *
        bobConditionalEffect (K (a + normalizationShift K hK))
          (next (a + normalizationShift K hK)) (labels (a + normalizationShift K hK)) ell *
        rightLocalNormalizer K (a + normalizationShift K hK) :=
  normalizedBobNode_effect K _ (normalizationShift_posDef K hK a) _ _ ell

theorem normalizedAliceShiftNode_complete {L : Type*} [Fintype L] [DecidableEq L]
    (K : (a : ℕ) → Fin (outcomes a) → Matrix (Fin (output a)) (Fin m) ℂ)
    (hK : Tendsto (gramTotal K) atTop (𝓝 1))
    (next : (a : ℕ) → Fin (outcomes a) → QuantumProver.ElegantJointMeasurement.CP.FiniteLocalCPInstrumentTree (output a) n)
    (labels : ∀ a s, LeafLabels (next a s) L) (a : ℕ) :
    (∑ ell, (normalizedAliceShiftNode K hK next a).matrixReportedEffect
      (normalizedAliceShiftLabels K hK next labels a) ell) = 1 :=
  (normalizedAliceShiftNode K hK next a).sum_matrixReportedEffect _

theorem normalizedBobShiftNode_complete {L : Type*} [Fintype L] [DecidableEq L]
    (K : (a : ℕ) → Fin (outcomes a) → Matrix (Fin (output a)) (Fin n) ℂ)
    (hK : Tendsto (gramTotal K) atTop (𝓝 1))
    (next : (a : ℕ) → Fin (outcomes a) → QuantumProver.ElegantJointMeasurement.CP.FiniteLocalCPInstrumentTree m (output a))
    (labels : ∀ a s, LeafLabels (next a s) L) (a : ℕ) :
    (∑ ell, (normalizedBobShiftNode K hK next a).matrixReportedEffect
      (normalizedBobShiftLabels K hK next labels a) ell) = 1 :=
  (normalizedBobShiftNode K hK next a).sum_matrixReportedEffect _

theorem matrixTree_trace_preserving {L : Type*} [Fintype L] [DecidableEq L]
    (T : QuantumProver.ElegantJointMeasurement.CP.FiniteLocalCPInstrumentTree m n) (labels : LeafLabels T L)
    (X : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) :
    (∑ ell, T.matrixReportedEvaluation labels ell X) = X.trace := by
  simp_rw [matrixReportedEvaluation_eq_trace_effect]
  rw [← Matrix.trace_sum, ← Matrix.sum_mul, T.sum_matrixReportedEffect labels, Matrix.one_mul]

theorem normalizedAliceShiftNode_tendsto {L : Type*} [Fintype L] [DecidableEq L]
    (K : (a : ℕ) → Fin (outcomes a) → Matrix (Fin (output a)) (Fin m) ℂ)
    (hK : Tendsto (gramTotal K) atTop (𝓝 1))
    (next : (a : ℕ) → Fin (outcomes a) → QuantumProver.ElegantJointMeasurement.CP.FiniteLocalCPInstrumentTree (output a) n)
    (labels : ∀ a s, LeafLabels (next a s) L)
    (F₀ : L → Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ)
    (hF : Tendsto (fun a ell => aliceConditionalEffect (K a) (next a) (labels a) ell)
      atTop (𝓝 F₀)) :
    Tendsto (fun a ell => (normalizedAliceShiftNode K hK next a).matrixReportedEffect
      (normalizedAliceShiftLabels K hK next labels a) ell) atTop (𝓝 F₀) := by
  have ht := normalized_local_effect_limit K hK
    (fun a ell => aliceConditionalEffect (K a) (next a) (labels a) ell) F₀ hF
  apply (ht.comp (tendsto_add_atTop_nat (normalizationShift K hK))).congr'
  exact Filter.Eventually.of_forall fun a =>
    funext fun ell => (normalizedAliceShiftNode_effect K hK next labels a ell).symm

theorem normalizedBobShiftNode_tendsto {L : Type*} [Fintype L] [DecidableEq L]
    (K : (a : ℕ) → Fin (outcomes a) → Matrix (Fin (output a)) (Fin n) ℂ)
    (hK : Tendsto (gramTotal K) atTop (𝓝 1))
    (next : (a : ℕ) → Fin (outcomes a) → QuantumProver.ElegantJointMeasurement.CP.FiniteLocalCPInstrumentTree m (output a))
    (labels : ∀ a s, LeafLabels (next a s) L)
    (F₀ : L → Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ)
    (hF : Tendsto (fun a ell => bobConditionalEffect (K a) (next a) (labels a) ell)
      atTop (𝓝 F₀)) :
    Tendsto (fun a ell => (normalizedBobShiftNode K hK next a).matrixReportedEffect
      (normalizedBobShiftLabels K hK next labels a) ell) atTop (𝓝 F₀) := by
  have ht := normalized_right_local_effect_limit K hK
    (fun a ell => bobConditionalEffect (K a) (next a) (labels a) ell) F₀ hF
  apply (ht.comp (tendsto_add_atTop_nat (normalizationShift K hK))).congr'
  exact Filter.Eventually.of_forall fun a =>
    funext fun ell => (normalizedBobShiftNode_effect K hK next labels a ell).symm

end
end QuantumProver.ElegantJointMeasurement.InstrumentNormalization

namespace QuantumProver.ElegantJointMeasurement.InstrumentNormalization

noncomputable section

open MeasureTheory Set
open QuantumProver.ElegantJointMeasurement.CP QuantumProver.ElegantJointMeasurement.CP.FiniteLocalCPInstrumentTree
open QuantumProver.ElegantJointMeasurement.ContinuousInstrumentQuadrature

variable {Ω L : Type*} [MeasurableSpace Ω] [Fintype L] [DecidableEq L]
variable {m n p : ℕ}

def aliceOutcomeEffect (K : Ω → Matrix (Fin p) (Fin m) ℂ)
    (next : Ω → FiniteLocalCPInstrumentTree p n)
    (labels : ∀ ω, LeafLabels (next ω) L) (ω : Ω) (ell : L) :
    Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ :=
  (K ω ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ))ᴴ *
    (next ω).matrixReportedEffect (labels ω) ell *
    (K ω ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ))

def bobOutcomeEffect (K : Ω → Matrix (Fin p) (Fin n) ℂ)
    (next : Ω → FiniteLocalCPInstrumentTree m p)
    (labels : ∀ ω, LeafLabels (next ω) L) (ω : Ω) (ell : L) :
    Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ :=
  ((1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ K ω)ᴴ *
    (next ω).matrixReportedEffect (labels ω) ell *
    ((1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ K ω)

def sampledKrausFamily {I O : Type*} [Fintype I] [Fintype O]
    (K : Ω → Matrix O I ℂ) {samples : ℕ → ℕ}
    (w : (a : ℕ) → Fin (samples a) → ℝ)
    (point : (a : ℕ) → Fin (samples a) → Ω) (a : ℕ) (i : Fin (samples a)) :
    Matrix O I ℂ := weightedKraus (w a i) (K (point a i))

omit [MeasurableSpace Ω] [Fintype L] in
theorem sampledAliceConditionalEffect_eq_weighted {r : ℕ}
    (K : Ω → Matrix (Fin p) (Fin m) ℂ)
    (next : Ω → FiniteLocalCPInstrumentTree p n)
    (labels : ∀ ω, LeafLabels (next ω) L)
    (w : Fin r → ℝ) (point : Fin r → Ω) (hw : ∀ i, 0 ≤ w i) (ell : L) :
    aliceConditionalEffect (fun i => weightedKraus (w i) (K (point i)))
      (fun i => next (point i)) (fun i => labels (point i)) ell =
      ∑ i, w i • aliceOutcomeEffect K next labels (point i) ell := by
  unfold aliceConditionalEffect
  apply Finset.sum_congr rfl
  intro i _
  simp only [weightedKraus, Matrix.smul_kronecker, Matrix.conjTranspose_smul,
    star_trivial, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    Real.mul_self_sqrt (hw i), aliceOutcomeEffect]

omit [MeasurableSpace Ω] [Fintype L] in
theorem sampledBobConditionalEffect_eq_weighted {r : ℕ}
    (K : Ω → Matrix (Fin p) (Fin n) ℂ)
    (next : Ω → FiniteLocalCPInstrumentTree m p)
    (labels : ∀ ω, LeafLabels (next ω) L)
    (w : Fin r → ℝ) (point : Fin r → Ω) (hw : ∀ i, 0 ≤ w i) (ell : L) :
    bobConditionalEffect (fun i => weightedKraus (w i) (K (point i)))
      (fun i => next (point i)) (fun i => labels (point i)) ell =
      ∑ i, w i • bobOutcomeEffect K next labels (point i) ell := by
  unfold bobConditionalEffect
  apply Finset.sum_congr rfl
  intro i _
  simp only [weightedKraus, Matrix.kronecker_smul, Matrix.conjTranspose_smul,
    star_trivial, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    Real.mul_self_sqrt (hw i), bobOutcomeEffect]

theorem exists_normalized_alice_node_quadrature_on
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (K : Ω → Matrix (Fin p) (Fin m) ℂ)
    (next : Ω → FiniteLocalCPInstrumentTree p n)
    (labels : ∀ ω, LeafLabels (next ω) L)
    (hGramInt : Integrable (fun ω => (K ω)ᴴ * K ω) μ)
    (hGramComplete : (∫ ω, (K ω)ᴴ * K ω ∂μ) = 1)
    (hEffectInt : Integrable (aliceOutcomeEffect K next labels) μ)
    (s : Set Ω) (hs : ∀ᵐ ω ∂μ, ω ∈ s) :
    ∃ (samples : ℕ → ℕ) (w : (a : ℕ) → Fin (samples a) → ℝ)
      (point : (a : ℕ) → Fin (samples a) → Ω),
      (∀ a i, 0 ≤ w a i) ∧
      (∀ a, (∑ i, w a i) = μ.real univ) ∧ (∀ a i, point a i ∈ s) ∧
      ∃ hG : Tendsto (gramTotal (sampledKrausFamily K w point)) atTop (𝓝 1),
        (∀ a, (∑ ell,
          (normalizedAliceShiftNode (sampledKrausFamily K w point) hG
            (fun a i => next (point a i)) a).matrixReportedEffect
              (normalizedAliceShiftLabels (sampledKrausFamily K w point) hG
                (fun a i => next (point a i)) (fun a i => labels (point a i)) a) ell) = 1) ∧
        Tendsto (fun a ell =>
          (normalizedAliceShiftNode (sampledKrausFamily K w point) hG
            (fun a i => next (point a i)) a).matrixReportedEffect
              (normalizedAliceShiftLabels (sampledKrausFamily K w point) hG
                (fun a i => next (point a i)) (fun a i => labels (point a i)) a) ell)
          atTop (𝓝 (∫ ω, aliceOutcomeEffect K next labels ω ∂μ)) := by
  obtain ⟨samples, w, point, hw, hmass, hpoint, hG', hF'⟩ :=
    exists_joint_sampled_kraus_quadrature_on μ K (aliceOutcomeEffect K next labels)
      (hGramInt.prodMk hEffectInt) s hs
  have hG : Tendsto (gramTotal (sampledKrausFamily K w point)) atTop (𝓝 1) := by
    change Tendsto (fun a => ∑ i,
      (weightedKraus (w a i) (K (point a i)))ᴴ *
        weightedKraus (w a i) (K (point a i))) atTop (𝓝 1)
    simpa only [hGramComplete] using hG'
  have hvalues (a : ℕ) :
      (fun ell => aliceConditionalEffect (sampledKrausFamily K w point a)
        (fun i => next (point a i)) (fun i => labels (point a i)) ell) =
        ∑ i, w a i • aliceOutcomeEffect K next labels (point a i) := by
    funext ell
    change aliceConditionalEffect (fun i => weightedKraus (w a i) (K (point a i)))
      (fun i => next (point a i)) (fun i => labels (point a i)) ell = _
    simpa only [Finset.sum_apply, Pi.smul_apply] using
      sampledAliceConditionalEffect_eq_weighted K next labels (w a) (point a) (hw a) ell
  have hF := hF'.congr' (Filter.Eventually.of_forall fun a => (hvalues a).symm)
  refine ⟨samples, w, point, hw, hmass, hpoint, hG, ?_, ?_⟩
  · intro a
    exact normalizedAliceShiftNode_complete (sampledKrausFamily K w point) hG
      (fun a i => next (point a i)) (fun a i => labels (point a i)) a
  · exact normalizedAliceShiftNode_tendsto (sampledKrausFamily K w point) hG
      (fun a i => next (point a i)) (fun a i => labels (point a i)) _ hF

theorem exists_normalized_bob_node_quadrature_on
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (K : Ω → Matrix (Fin p) (Fin n) ℂ)
    (next : Ω → FiniteLocalCPInstrumentTree m p)
    (labels : ∀ ω, LeafLabels (next ω) L)
    (hGramInt : Integrable (fun ω => (K ω)ᴴ * K ω) μ)
    (hGramComplete : (∫ ω, (K ω)ᴴ * K ω ∂μ) = 1)
    (hEffectInt : Integrable (bobOutcomeEffect K next labels) μ)
    (s : Set Ω) (hs : ∀ᵐ ω ∂μ, ω ∈ s) :
    ∃ (samples : ℕ → ℕ) (w : (a : ℕ) → Fin (samples a) → ℝ)
      (point : (a : ℕ) → Fin (samples a) → Ω),
      (∀ a i, 0 ≤ w a i) ∧
      (∀ a, (∑ i, w a i) = μ.real univ) ∧ (∀ a i, point a i ∈ s) ∧
      ∃ hG : Tendsto (gramTotal (sampledKrausFamily K w point)) atTop (𝓝 1),
        (∀ a, (∑ ell,
          (normalizedBobShiftNode (sampledKrausFamily K w point) hG
            (fun a i => next (point a i)) a).matrixReportedEffect
              (normalizedBobShiftLabels (sampledKrausFamily K w point) hG
                (fun a i => next (point a i)) (fun a i => labels (point a i)) a) ell) = 1) ∧
        Tendsto (fun a ell =>
          (normalizedBobShiftNode (sampledKrausFamily K w point) hG
            (fun a i => next (point a i)) a).matrixReportedEffect
              (normalizedBobShiftLabels (sampledKrausFamily K w point) hG
                (fun a i => next (point a i)) (fun a i => labels (point a i)) a) ell)
          atTop (𝓝 (∫ ω, bobOutcomeEffect K next labels ω ∂μ)) := by
  obtain ⟨samples, w, point, hw, hmass, hpoint, hG', hF'⟩ :=
    exists_joint_sampled_kraus_quadrature_on μ K (bobOutcomeEffect K next labels)
      (hGramInt.prodMk hEffectInt) s hs
  have hG : Tendsto (gramTotal (sampledKrausFamily K w point)) atTop (𝓝 1) := by
    change Tendsto (fun a => ∑ i,
      (weightedKraus (w a i) (K (point a i)))ᴴ *
        weightedKraus (w a i) (K (point a i))) atTop (𝓝 1)
    simpa only [hGramComplete] using hG'
  have hvalues (a : ℕ) :
      (fun ell => bobConditionalEffect (sampledKrausFamily K w point a)
        (fun i => next (point a i)) (fun i => labels (point a i)) ell) =
        ∑ i, w a i • bobOutcomeEffect K next labels (point a i) := by
    funext ell
    change bobConditionalEffect (fun i => weightedKraus (w a i) (K (point a i)))
      (fun i => next (point a i)) (fun i => labels (point a i)) ell = _
    simpa only [Finset.sum_apply, Pi.smul_apply] using
      sampledBobConditionalEffect_eq_weighted K next labels (w a) (point a) (hw a) ell
  have hF := hF'.congr' (Filter.Eventually.of_forall fun a => (hvalues a).symm)
  refine ⟨samples, w, point, hw, hmass, hpoint, hG, ?_, ?_⟩
  · intro a
    exact normalizedBobShiftNode_complete (sampledKrausFamily K w point) hG
      (fun a i => next (point a i)) (fun a i => labels (point a i)) a
  · exact normalizedBobShiftNode_tendsto (sampledKrausFamily K w point) hG
      (fun a i => next (point a i)) (fun a i => labels (point a i)) _ hF

end
end QuantumProver.ElegantJointMeasurement.InstrumentNormalization

namespace QuantumProver.ElegantJointMeasurement.InstrumentNormalization

noncomputable section

open MeasureTheory Set
open QuantumProver.ElegantJointMeasurement.CP QuantumProver.ElegantJointMeasurement.CP.FiniteLocalCPInstrumentTree
open QuantumProver.ElegantJointMeasurement.ContinuousInstrumentQuadrature QuantumProver.ElegantJointMeasurement.ContinuousCPInstruments

set_option maxHeartbeats 800000

variable {Ω L : Type*} [MeasurableSpace Ω] [Fintype L] [DecidableEq L]
variable {m n p : ℕ}

theorem weightedMatrix_pullback {I O : Type*} [Fintype I] [Fintype O]
    (w : ℝ) (A : Matrix O I ℂ) (D : Matrix O O ℂ) (hw : 0 ≤ w) :
    (weightedKraus w A)ᴴ * D * weightedKraus w A = w • (Aᴴ * D * A) := by
  simp only [weightedKraus, Matrix.conjTranspose_smul, star_trivial,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul, Real.mul_self_sqrt hw]

def cpAliceOutcomeEffect
    (Φ : Ω → (Matrix (Fin m) (Fin m) ℂ →ₗ[ℂ] Matrix (Fin p) (Fin p) ℂ))
    (next : Ω → FiniteLocalCPInstrumentTree p n)
    (labels : ∀ ω, LeafLabels (next ω) L) (ω : Ω) (ell : L) :
    Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ :=
  ∑ q : Fin m × Fin p,
    (canonicalKraus Φ ω q ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ))ᴴ *
      (next ω).matrixReportedEffect (labels ω) ell *
      (canonicalKraus Φ ω q ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ))

def cpBobOutcomeEffect
    (Φ : Ω → (Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin p) (Fin p) ℂ))
    (next : Ω → FiniteLocalCPInstrumentTree m p)
    (labels : ∀ ω, LeafLabels (next ω) L) (ω : Ω) (ell : L) :
    Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ :=
  ∑ q : Fin n × Fin p,
    ((1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ canonicalKraus Φ ω q)ᴴ *
      (next ω).matrixReportedEffect (labels ω) ell *
      ((1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ canonicalKraus Φ ω q)

omit [MeasurableSpace Ω] [Fintype L] in

theorem cpAliceOutcomeEffect_matrix_evaluation
    (Φ : Ω → (Matrix (Fin m) (Fin m) ℂ →ₗ[ℂ] Matrix (Fin p) (Fin p) ℂ))
    (hCP : ∀ ω, CompletelyPositive (Φ ω))
    (next : Ω → FiniteLocalCPInstrumentTree p n)
    (labels : ∀ ω, LeafLabels (next ω) L) (ω : Ω) (ell : L)
    (X : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) :
    (cpAliceOutcomeEffect Φ next labels ω ell * X).trace =
      (next ω).matrixReportedEvaluation (labels ω) ell (leftApplication (Φ ω) X) := by
  rw [leftApplication_eq_kraus (Φ ω) (hCP ω)]
  simp only [cpAliceOutcomeEffect, Matrix.sum_mul, Matrix.trace_sum, map_sum,
    canonicalKraus, matrixReportedEvaluation_eq_trace_effect, leftKrausApplication,
    trace_pullback_sandwich]

omit [MeasurableSpace Ω] [Fintype L] in
theorem cpBobOutcomeEffect_matrix_evaluation
    (Φ : Ω → (Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin p) (Fin p) ℂ))
    (hCP : ∀ ω, CompletelyPositive (Φ ω))
    (next : Ω → FiniteLocalCPInstrumentTree m p)
    (labels : ∀ ω, LeafLabels (next ω) L) (ω : Ω) (ell : L)
    (X : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) :
    (cpBobOutcomeEffect Φ next labels ω ell * X).trace =
      (next ω).matrixReportedEvaluation (labels ω) ell (rightApplication (Φ ω) X) := by
  rw [rightApplication_eq_kraus (Φ ω) (hCP ω)]
  simp only [cpBobOutcomeEffect, Matrix.sum_mul, Matrix.trace_sum, map_sum,
    canonicalKraus, matrixReportedEvaluation_eq_trace_effect, rightKrausApplication,
    trace_pullback_sandwich]

def cpSampleIndex (I O : Type*) [Fintype I] [Fintype O] (r : ℕ) :
    Fin (Fintype.card (Fin r × (I × O))) ≃ (Fin r × (I × O)) :=
  (Fintype.equivFin (Fin r × (I × O))).symm

def cpSamplePoint (I O : Type*) [Fintype I] [Fintype O] {samples : ℕ → ℕ}
    (point : (a : ℕ) → Fin (samples a) → Ω) (a : ℕ)
    (i : Fin (Fintype.card (Fin (samples a) × (I × O)))) : Ω :=
  point a ((cpSampleIndex I O (samples a)) i).1

def sampledCPKrausFamily {I O : Type*} [Fintype I] [Fintype O]
    [DecidableEq I] [DecidableEq O]
    (Φ : Ω → (Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ)) {samples : ℕ → ℕ}
    (w : (a : ℕ) → Fin (samples a) → ℝ)
    (point : (a : ℕ) → Fin (samples a) → Ω) (a : ℕ)
    (i : Fin (Fintype.card (Fin (samples a) × (I × O)))) : Matrix O I ℂ :=
  QuantumProver.ElegantJointMeasurement.ContinuousCPInstruments.sampledKraus Φ (w a) (point a)
    ((cpSampleIndex I O (samples a)) i)

omit [MeasurableSpace Ω] in
theorem sampledCPKrausFamily_totalGram {I O : Type*} [Fintype I] [Fintype O]
    [DecidableEq I] [DecidableEq O]
    (Φ : Ω → (Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ)) {samples : ℕ → ℕ}
    (w : (a : ℕ) → Fin (samples a) → ℝ)
    (point : (a : ℕ) → Fin (samples a) → Ω) (a : ℕ) :
    gramTotal (sampledCPKrausFamily Φ w point) a =
      ∑ z : Fin (samples a) × (I × O),
        (QuantumProver.ElegantJointMeasurement.ContinuousCPInstruments.sampledKraus Φ (w a) (point a) z)ᴴ *
          QuantumProver.ElegantJointMeasurement.ContinuousCPInstruments.sampledKraus Φ (w a) (point a) z := by
  change (∑ i,
    (QuantumProver.ElegantJointMeasurement.ContinuousCPInstruments.sampledKraus Φ (w a) (point a)
      ((cpSampleIndex I O (samples a)) i))ᴴ *
      QuantumProver.ElegantJointMeasurement.ContinuousCPInstruments.sampledKraus Φ (w a) (point a)
        ((cpSampleIndex I O (samples a)) i)) = _
  exact (cpSampleIndex I O (samples a)).sum_comp
    (fun z : Fin (samples a) × (I × O) =>
      (QuantumProver.ElegantJointMeasurement.ContinuousCPInstruments.sampledKraus Φ (w a) (point a) z)ᴴ *
        QuantumProver.ElegantJointMeasurement.ContinuousCPInstruments.sampledKraus Φ (w a) (point a) z)

omit [MeasurableSpace Ω] [Fintype L] in
theorem sampledCPAliceConditionalEffect_eq_weighted
    (Φ : Ω → (Matrix (Fin m) (Fin m) ℂ →ₗ[ℂ] Matrix (Fin p) (Fin p) ℂ))
    (next : Ω → FiniteLocalCPInstrumentTree p n)
    (labels : ∀ ω, LeafLabels (next ω) L) {samples : ℕ → ℕ}
    (w : (a : ℕ) → Fin (samples a) → ℝ)
    (point : (a : ℕ) → Fin (samples a) → Ω)
    (hw : ∀ a i, 0 ≤ w a i) (a : ℕ) (ell : L) :
    aliceConditionalEffect (sampledCPKrausFamily Φ w point a)
      (fun i => next (cpSamplePoint (Fin m) (Fin p) point a i))
      (fun i => labels (cpSamplePoint (Fin m) (Fin p) point a i)) ell =
      ∑ i, w a i • cpAliceOutcomeEffect Φ next labels (point a i) ell := by
  let g : Fin (samples a) × (Fin m × Fin p) →
      Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ := fun z =>
    (QuantumProver.ElegantJointMeasurement.ContinuousCPInstruments.sampledKraus Φ (w a) (point a) z ⊗ₖ
      (1 : Matrix (Fin n) (Fin n) ℂ))ᴴ *
      (next (point a z.1)).matrixReportedEffect (labels (point a z.1)) ell *
      (QuantumProver.ElegantJointMeasurement.ContinuousCPInstruments.sampledKraus Φ (w a) (point a) z ⊗ₖ
        (1 : Matrix (Fin n) (Fin n) ℂ))
  change (∑ i, g ((cpSampleIndex (Fin m) (Fin p) (samples a)) i)) = _
  calc
    _ = ∑ z, g z := (cpSampleIndex (Fin m) (Fin p) (samples a)).sum_comp g
    _ = _ := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro i _
      rw [cpAliceOutcomeEffect, Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro q _
      simpa only [g, QuantumProver.ElegantJointMeasurement.ContinuousCPInstruments.sampledKraus, weightedKraus,
        Matrix.smul_kronecker] using
        weightedMatrix_pullback (w a i)
          (canonicalKraus Φ (point a i) q ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ))
          ((next (point a i)).matrixReportedEffect (labels (point a i)) ell) (hw a i)

omit [MeasurableSpace Ω] [Fintype L] in
theorem sampledCPBobConditionalEffect_eq_weighted
    (Φ : Ω → (Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin p) (Fin p) ℂ))
    (next : Ω → FiniteLocalCPInstrumentTree m p)
    (labels : ∀ ω, LeafLabels (next ω) L) {samples : ℕ → ℕ}
    (w : (a : ℕ) → Fin (samples a) → ℝ)
    (point : (a : ℕ) → Fin (samples a) → Ω)
    (hw : ∀ a i, 0 ≤ w a i) (a : ℕ) (ell : L) :
    bobConditionalEffect (sampledCPKrausFamily Φ w point a)
      (fun i => next (cpSamplePoint (Fin n) (Fin p) point a i))
      (fun i => labels (cpSamplePoint (Fin n) (Fin p) point a i)) ell =
      ∑ i, w a i • cpBobOutcomeEffect Φ next labels (point a i) ell := by
  let g : Fin (samples a) × (Fin n × Fin p) →
      Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ := fun z =>
    ((1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ
      QuantumProver.ElegantJointMeasurement.ContinuousCPInstruments.sampledKraus Φ (w a) (point a) z)ᴴ *
      (next (point a z.1)).matrixReportedEffect (labels (point a z.1)) ell *
      ((1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ
        QuantumProver.ElegantJointMeasurement.ContinuousCPInstruments.sampledKraus Φ (w a) (point a) z)
  change (∑ i, g ((cpSampleIndex (Fin n) (Fin p) (samples a)) i)) = _
  calc
    _ = ∑ z, g z := (cpSampleIndex (Fin n) (Fin p) (samples a)).sum_comp g
    _ = _ := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro i _
      rw [cpBobOutcomeEffect, Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro q _
      simpa only [g, QuantumProver.ElegantJointMeasurement.ContinuousCPInstruments.sampledKraus, weightedKraus,
        Matrix.kronecker_smul] using
        weightedMatrix_pullback (w a i)
          ((1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ canonicalKraus Φ (point a i) q)
          ((next (point a i)).matrixReportedEffect (labels (point a i)) ell) (hw a i)

theorem exists_normalized_cp_alice_node_quadrature_on
    (μ : Measure Ω) [IsFiniteMeasure μ] (hm : 0 < m)
    (Φ : Ω → (Matrix (Fin m) (Fin m) ℂ →ₗ[ℂ] Matrix (Fin p) (Fin p) ℂ))
    (hΦ : CoordinateMeasurable Φ) (hCP : ∀ ω, CompletelyPositive (Φ ω))
    (htrace : MatrixTraceComplete μ Φ)
    (next : Ω → FiniteLocalCPInstrumentTree p n)
    (labels : ∀ ω, LeafLabels (next ω) L)
    (hEffectInt : Integrable (cpAliceOutcomeEffect Φ next labels) μ)
    (s : Set Ω) (hs : ∀ᵐ ω ∂μ, ω ∈ s) :
    ∃ (samples : ℕ → ℕ) (w : (a : ℕ) → Fin (samples a) → ℝ)
      (point : (a : ℕ) → Fin (samples a) → Ω),
      (∀ a i, 0 ≤ w a i) ∧
      (∀ a, (∑ i, w a i) = μ.real univ) ∧ (∀ a i, point a i ∈ s) ∧
      ∃ hG : Tendsto (gramTotal (sampledCPKrausFamily Φ w point)) atTop (𝓝 1),
        (∀ a, (∑ ell,
          (normalizedAliceShiftNode (sampledCPKrausFamily Φ w point) hG
            (fun a i => next (cpSamplePoint (Fin m) (Fin p) point a i)) a).matrixReportedEffect
              (normalizedAliceShiftLabels (sampledCPKrausFamily Φ w point) hG
                (fun a i => next (cpSamplePoint (Fin m) (Fin p) point a i))
                (fun a i => labels (cpSamplePoint (Fin m) (Fin p) point a i)) a) ell) = 1) ∧
        Tendsto (fun a ell =>
          (normalizedAliceShiftNode (sampledCPKrausFamily Φ w point) hG
            (fun a i => next (cpSamplePoint (Fin m) (Fin p) point a i)) a).matrixReportedEffect
              (normalizedAliceShiftLabels (sampledCPKrausFamily Φ w point) hG
                (fun a i => next (cpSamplePoint (Fin m) (Fin p) point a i))
                (fun a i => labels (cpSamplePoint (Fin m) (Fin p) point a i)) a) ell)
          atTop (𝓝 (∫ ω, cpAliceOutcomeEffect Φ next labels ω ∂μ)) := by
  let : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  obtain ⟨samples, w, point, hw, hmass, hpoint, hG', hF'⟩ :=
    exists_matrix_joint_quadrature_on μ Φ hΦ hCP htrace
      (cpAliceOutcomeEffect Φ next labels) hEffectInt s hs
  have hG : Tendsto (gramTotal (sampledCPKrausFamily Φ w point)) atTop (𝓝 1) :=
    hG'.congr' (Filter.Eventually.of_forall fun a =>
      (sampledCPKrausFamily_totalGram Φ w point a).symm)
  have hvalues (a : ℕ) :
      (fun ell => aliceConditionalEffect (sampledCPKrausFamily Φ w point a)
        (fun i => next (cpSamplePoint (Fin m) (Fin p) point a i))
        (fun i => labels (cpSamplePoint (Fin m) (Fin p) point a i)) ell) =
        ∑ i, w a i • cpAliceOutcomeEffect Φ next labels (point a i) := by
    funext ell
    simpa only [Finset.sum_apply, Pi.smul_apply] using
      sampledCPAliceConditionalEffect_eq_weighted Φ next labels w point hw a ell
  have hF := hF'.congr' (Filter.Eventually.of_forall fun a => (hvalues a).symm)
  refine ⟨samples, w, point, hw, hmass, hpoint, hG, ?_, ?_⟩
  · intro a
    exact normalizedAliceShiftNode_complete (sampledCPKrausFamily Φ w point) hG
      (fun a i => next (cpSamplePoint (Fin m) (Fin p) point a i))
      (fun a i => labels (cpSamplePoint (Fin m) (Fin p) point a i)) a
  · exact normalizedAliceShiftNode_tendsto (sampledCPKrausFamily Φ w point) hG
      (fun a i => next (cpSamplePoint (Fin m) (Fin p) point a i))
      (fun a i => labels (cpSamplePoint (Fin m) (Fin p) point a i)) _ hF

theorem exists_normalized_cp_bob_node_quadrature_on
    (μ : Measure Ω) [IsFiniteMeasure μ] (hn : 0 < n)
    (Φ : Ω → (Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin p) (Fin p) ℂ))
    (hΦ : CoordinateMeasurable Φ) (hCP : ∀ ω, CompletelyPositive (Φ ω))
    (htrace : MatrixTraceComplete μ Φ)
    (next : Ω → FiniteLocalCPInstrumentTree m p)
    (labels : ∀ ω, LeafLabels (next ω) L)
    (hEffectInt : Integrable (cpBobOutcomeEffect Φ next labels) μ)
    (s : Set Ω) (hs : ∀ᵐ ω ∂μ, ω ∈ s) :
    ∃ (samples : ℕ → ℕ) (w : (a : ℕ) → Fin (samples a) → ℝ)
      (point : (a : ℕ) → Fin (samples a) → Ω),
      (∀ a i, 0 ≤ w a i) ∧
      (∀ a, (∑ i, w a i) = μ.real univ) ∧ (∀ a i, point a i ∈ s) ∧
      ∃ hG : Tendsto (gramTotal (sampledCPKrausFamily Φ w point)) atTop (𝓝 1),
        (∀ a, (∑ ell,
          (normalizedBobShiftNode (sampledCPKrausFamily Φ w point) hG
            (fun a i => next (cpSamplePoint (Fin n) (Fin p) point a i)) a).matrixReportedEffect
              (normalizedBobShiftLabels (sampledCPKrausFamily Φ w point) hG
                (fun a i => next (cpSamplePoint (Fin n) (Fin p) point a i))
                (fun a i => labels (cpSamplePoint (Fin n) (Fin p) point a i)) a) ell) = 1) ∧
        Tendsto (fun a ell =>
          (normalizedBobShiftNode (sampledCPKrausFamily Φ w point) hG
            (fun a i => next (cpSamplePoint (Fin n) (Fin p) point a i)) a).matrixReportedEffect
              (normalizedBobShiftLabels (sampledCPKrausFamily Φ w point) hG
                (fun a i => next (cpSamplePoint (Fin n) (Fin p) point a i))
                (fun a i => labels (cpSamplePoint (Fin n) (Fin p) point a i)) a) ell)
          atTop (𝓝 (∫ ω, cpBobOutcomeEffect Φ next labels ω ∂μ)) := by
  let : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨samples, w, point, hw, hmass, hpoint, hG', hF'⟩ :=
    exists_matrix_joint_quadrature_on μ Φ hΦ hCP htrace
      (cpBobOutcomeEffect Φ next labels) hEffectInt s hs
  have hG : Tendsto (gramTotal (sampledCPKrausFamily Φ w point)) atTop (𝓝 1) :=
    hG'.congr' (Filter.Eventually.of_forall fun a =>
      (sampledCPKrausFamily_totalGram Φ w point a).symm)
  have hvalues (a : ℕ) :
      (fun ell => bobConditionalEffect (sampledCPKrausFamily Φ w point a)
        (fun i => next (cpSamplePoint (Fin n) (Fin p) point a i))
        (fun i => labels (cpSamplePoint (Fin n) (Fin p) point a i)) ell) =
        ∑ i, w a i • cpBobOutcomeEffect Φ next labels (point a i) := by
    funext ell
    simpa only [Finset.sum_apply, Pi.smul_apply] using
      sampledCPBobConditionalEffect_eq_weighted Φ next labels w point hw a ell
  have hF := hF'.congr' (Filter.Eventually.of_forall fun a => (hvalues a).symm)
  refine ⟨samples, w, point, hw, hmass, hpoint, hG, ?_, ?_⟩
  · intro a
    exact normalizedBobShiftNode_complete (sampledCPKrausFamily Φ w point) hG
      (fun a i => next (cpSamplePoint (Fin n) (Fin p) point a i))
      (fun a i => labels (cpSamplePoint (Fin n) (Fin p) point a i)) a
  · exact normalizedBobShiftNode_tendsto (sampledCPKrausFamily Φ w point) hG
      (fun a i => next (cpSamplePoint (Fin n) (Fin p) point a i))
      (fun a i => labels (cpSamplePoint (Fin n) (Fin p) point a i)) _ hF

end
end QuantumProver.ElegantJointMeasurement.InstrumentNormalization

namespace QuantumProver.ElegantJointMeasurement.InstrumentNormalization

noncomputable section

open MeasureTheory Set
open QuantumProver.ElegantJointMeasurement.CP QuantumProver.ElegantJointMeasurement.CP.FiniteLocalCPInstrumentTree
open QuantumProver.ElegantJointMeasurement.ContinuousCPInstruments

set_option maxHeartbeats 800000

theorem matrix_pullback_mono {I O : Type*} [Fintype I] [Fintype O]
    (A : Matrix O I ℂ) {E F : Matrix O O ℂ} (hEF : E ≤ F) :
    Aᴴ * E * A ≤ Aᴴ * F * A := by
  apply Matrix.le_iff.mpr
  simpa only [Matrix.conjTranspose_conjTranspose, Matrix.mul_sub, Matrix.sub_mul] using
    (Matrix.le_iff.mp hEF).mul_mul_conjTranspose_same Aᴴ

theorem matrix_pullback_posSemidef {I O : Type*} [Fintype I] [Fintype O]
    (A : Matrix O I ℂ) {E : Matrix O O ℂ} (hE : E.PosSemidef) :
    (Aᴴ * E * A).PosSemidef := by
  simpa only [Matrix.conjTranspose_conjTranspose] using hE.mul_mul_conjTranspose_same Aᴴ

theorem matrixReportedEffect_bounds {m n : ℕ} {L : Type*} [Fintype L] [DecidableEq L]
    (T : FiniteLocalCPInstrumentTree m n) (labels : LeafLabels T L) (ell : L) :
    (T.matrixReportedEffect labels ell).PosSemidef ∧ T.matrixReportedEffect labels ell ≤ 1 := by
  refine ⟨T.matrixReportedEffect_posSemidef labels ell, ?_⟩
  have h := Finset.single_le_sum
    (fun j (_ : j ∈ Finset.univ) => (T.matrixReportedEffect_posSemidef labels j).nonneg)
    (Finset.mem_univ ell)
  simpa only [T.sum_matrixReportedEffect labels] using h

theorem posSemidef_norm_trace_domination {I : Type*} [Fintype I] [DecidableEq I]
    (E G : Matrix I I ℂ) (hE : E.PosSemidef) (hEG : E ≤ G) : ‖E‖ ≤ G.trace.re := by
  have ht := (Complex.nonneg_iff.mp (Matrix.le_iff.mp hEG).trace_nonneg).1
  simp only [Matrix.trace_sub, Complex.sub_re, sub_nonneg] at ht
  exact (QuantumProver.ElegantJointMeasurement.ContinuousCPInstruments.posSemidef_norm_le_trace E hE).trans ht

theorem sum_left_kronecker {S I J : Type*} [Fintype S]
    (A : S → Matrix I I ℂ) (B : Matrix J J ℂ) :
    (∑ s, A s ⊗ₖ B) = (∑ s, A s) ⊗ₖ B := by
  ext i j
  simp only [Matrix.sum_apply, Matrix.kroneckerMap_apply, Finset.sum_mul]

theorem sum_right_kronecker {S I J : Type*} [Fintype S]
    (A : Matrix I I ℂ) (B : S → Matrix J J ℂ) :
    (∑ s, A ⊗ₖ B s) = A ⊗ₖ (∑ s, B s) := by
  ext i j
  simp only [Matrix.sum_apply, Matrix.kroneckerMap_apply, Finset.mul_sum]

theorem trace_left_kronecker_one {m n : ℕ} (G : Matrix (Fin m) (Fin m) ℂ) :
    (G ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ)).trace.re = (n : ℝ) * G.trace.re := by
  simp [Matrix.trace_kronecker, Complex.mul_re, mul_comm]

theorem trace_right_kronecker_one {m n : ℕ} (G : Matrix (Fin n) (Fin n) ℂ) :
    ((1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ G).trace.re = (m : ℝ) * G.trace.re := by
  simp [Matrix.trace_kronecker, Complex.mul_re]

variable {Ω L : Type*} [MeasurableSpace Ω] [Fintype L] [DecidableEq L]
variable {m n p : ℕ}

omit [MeasurableSpace Ω] in
theorem aliceOutcomeEffect_bounds
    (K : Ω → Matrix (Fin p) (Fin m) ℂ)
    (next : Ω → FiniteLocalCPInstrumentTree p n)
    (labels : ∀ ω, LeafLabels (next ω) L) (ω : Ω) (ell : L) :
    (aliceOutcomeEffect K next labels ω ell).PosSemidef ∧
      aliceOutcomeEffect K next labels ω ell ≤
        ((K ω)ᴴ * K ω) ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ) := by
  have hE := matrixReportedEffect_bounds (next ω) (labels ω) ell
  refine ⟨matrix_pullback_posSemidef _ hE.1, ?_⟩
  simpa only [aliceOutcomeEffect, Matrix.mul_one, Matrix.conjTranspose_kronecker,
    Matrix.conjTranspose_one, ← Matrix.mul_kronecker_mul, Matrix.one_mul] using
    matrix_pullback_mono (K ω ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ)) hE.2

omit [MeasurableSpace Ω] in
theorem bobOutcomeEffect_bounds
    (K : Ω → Matrix (Fin p) (Fin n) ℂ)
    (next : Ω → FiniteLocalCPInstrumentTree m p)
    (labels : ∀ ω, LeafLabels (next ω) L) (ω : Ω) (ell : L) :
    (bobOutcomeEffect K next labels ω ell).PosSemidef ∧
      bobOutcomeEffect K next labels ω ell ≤
        (1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ ((K ω)ᴴ * K ω) := by
  have hE := matrixReportedEffect_bounds (next ω) (labels ω) ell
  refine ⟨matrix_pullback_posSemidef _ hE.1, ?_⟩
  simpa only [bobOutcomeEffect, Matrix.mul_one, Matrix.conjTranspose_kronecker,
    Matrix.conjTranspose_one, ← Matrix.mul_kronecker_mul, Matrix.one_mul] using
    matrix_pullback_mono ((1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ K ω) hE.2

omit [MeasurableSpace Ω] in
theorem cpAliceOutcomeEffect_bounds
    (Φ : Ω → (Matrix (Fin m) (Fin m) ℂ →ₗ[ℂ] Matrix (Fin p) (Fin p) ℂ))
    (next : Ω → FiniteLocalCPInstrumentTree p n)
    (labels : ∀ ω, LeafLabels (next ω) L) (ω : Ω) (ell : L) :
    (cpAliceOutcomeEffect Φ next labels ω ell).PosSemidef ∧
      cpAliceOutcomeEffect Φ next labels ω ell ≤
        canonicalGram Φ ω ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ) := by
  have hb (q : Fin m × Fin p) :=
    aliceOutcomeEffect_bounds (fun ω => canonicalKraus Φ ω q) next labels ω ell
  constructor
  · exact Matrix.posSemidef_sum _ fun q _ => (hb q).1
  · have h := Finset.sum_le_sum (fun q (_ : q ∈ Finset.univ) => (hb q).2)
    simpa only [cpAliceOutcomeEffect, aliceOutcomeEffect, canonicalGram,
      sum_left_kronecker] using h

omit [MeasurableSpace Ω] in
theorem cpBobOutcomeEffect_bounds
    (Φ : Ω → (Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin p) (Fin p) ℂ))
    (next : Ω → FiniteLocalCPInstrumentTree m p)
    (labels : ∀ ω, LeafLabels (next ω) L) (ω : Ω) (ell : L) :
    (cpBobOutcomeEffect Φ next labels ω ell).PosSemidef ∧
      cpBobOutcomeEffect Φ next labels ω ell ≤
        (1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ canonicalGram Φ ω := by
  have hb (q : Fin n × Fin p) :=
    bobOutcomeEffect_bounds (fun ω => canonicalKraus Φ ω q) next labels ω ell
  constructor
  · exact Matrix.posSemidef_sum _ fun q _ => (hb q).1
  · have h := Finset.sum_le_sum (fun q (_ : q ∈ Finset.univ) => (hb q).2)
    simpa only [cpBobOutcomeEffect, bobOutcomeEffect, canonicalGram,
      sum_right_kronecker] using h

omit [MeasurableSpace Ω] in
theorem cpAliceOutcomeEffect_norm_bound
    (Φ : Ω → (Matrix (Fin m) (Fin m) ℂ →ₗ[ℂ] Matrix (Fin p) (Fin p) ℂ))
    (next : Ω → FiniteLocalCPInstrumentTree p n)
    (labels : ∀ ω, LeafLabels (next ω) L) (ω : Ω) (ell : L) :
    ‖cpAliceOutcomeEffect Φ next labels ω ell‖ ≤ (n : ℝ) * (canonicalGram Φ ω).trace.re := by
  have hb := cpAliceOutcomeEffect_bounds Φ next labels ω ell
  simpa only [trace_left_kronecker_one] using posSemidef_norm_trace_domination _ _ hb.1 hb.2

omit [MeasurableSpace Ω] in
theorem cpBobOutcomeEffect_norm_bound
    (Φ : Ω → (Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin p) (Fin p) ℂ))
    (next : Ω → FiniteLocalCPInstrumentTree m p)
    (labels : ∀ ω, LeafLabels (next ω) L) (ω : Ω) (ell : L) :
    ‖cpBobOutcomeEffect Φ next labels ω ell‖ ≤ (m : ℝ) * (canonicalGram Φ ω).trace.re := by
  have hb := cpBobOutcomeEffect_bounds Φ next labels ω ell
  simpa only [trace_right_kronecker_one] using posSemidef_norm_trace_domination _ _ hb.1 hb.2

def realMatrixTraceCLM {I : Type*} [Fintype I] [DecidableEq I] :
    Matrix I I ℂ →L[ℝ] ℝ :=
  Complex.reCLM.comp (Matrix.traceLinearMap I ℝ ℂ).toContinuousLinearMap

private theorem measurable_matrix_pullback {I O : Type*} [Fintype I] [Fintype O]
    (A : Ω → Matrix O I ℂ) (D : Ω → Matrix O O ℂ)
    (hA : Measurable A) (hD : Measurable D) :
    Measurable (fun ω => (A ω)ᴴ * D ω * A ω) := by
  have ha : ∀ i j, Measurable (fun ω => A ω i j) := fun i j =>
    (measurable_pi_apply j).comp ((measurable_pi_apply i).comp hA)
  have hd : ∀ i j, Measurable (fun ω => D ω i j) := fun i j =>
    (measurable_pi_apply j).comp ((measurable_pi_apply i).comp hD)
  refine Measurable.of_eval fun i => Measurable.of_eval fun j => ?_
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
  fun_prop

private theorem measurable_left_tensor (K : Ω → Matrix (Fin p) (Fin m) ℂ)
    (hK : Measurable K) :
    Measurable (fun ω => K ω ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ)) := by
  refine Measurable.of_eval fun i => Measurable.of_eval fun j => ?_
  simp only [Matrix.kroneckerMap_apply]
  exact ((measurable_pi_apply j.1).comp ((measurable_pi_apply i.1).comp hK)).mul measurable_const

private theorem measurable_right_tensor (K : Ω → Matrix (Fin p) (Fin n) ℂ)
    (hK : Measurable K) :
    Measurable (fun ω => (1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ K ω) := by
  refine Measurable.of_eval fun i => Measurable.of_eval fun j => ?_
  simp only [Matrix.kroneckerMap_apply]
  exact measurable_const.mul
    ((measurable_pi_apply j.2).comp ((measurable_pi_apply i.2).comp hK))

omit [Fintype L] in
theorem measurable_cpAliceOutcomeEffect
    (Φ : Ω → (Matrix (Fin m) (Fin m) ℂ →ₗ[ℂ] Matrix (Fin p) (Fin p) ℂ))
    (hΦ : CoordinateMeasurable Φ) (next : Ω → FiniteLocalCPInstrumentTree p n)
    (labels : ∀ ω, LeafLabels (next ω) L)
    (hChild : ∀ ell, Measurable (fun ω => (next ω).matrixReportedEffect (labels ω) ell)) :
    Measurable (cpAliceOutcomeEffect Φ next labels) := by
  apply Measurable.of_eval
  intro ell
  exact Finset.measurable_sum Finset.univ fun q _ =>
    measurable_matrix_pullback _ _
      (measurable_left_tensor _ (measurable_canonicalKraus Φ hΦ q)) (hChild ell)

omit [Fintype L] in
theorem measurable_cpBobOutcomeEffect
    (Φ : Ω → (Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin p) (Fin p) ℂ))
    (hΦ : CoordinateMeasurable Φ) (next : Ω → FiniteLocalCPInstrumentTree m p)
    (labels : ∀ ω, LeafLabels (next ω) L)
    (hChild : ∀ ell, Measurable (fun ω => (next ω).matrixReportedEffect (labels ω) ell)) :
    Measurable (cpBobOutcomeEffect Φ next labels) := by
  apply Measurable.of_eval
  intro ell
  exact Finset.measurable_sum Finset.univ fun q _ =>
    measurable_matrix_pullback _ _
      (measurable_right_tensor _ (measurable_canonicalKraus Φ hΦ q)) (hChild ell)

theorem integrable_cpAliceOutcomeEffect
    (μ : Measure Ω) (hm : 0 < m)
    (Φ : Ω → (Matrix (Fin m) (Fin m) ℂ →ₗ[ℂ] Matrix (Fin p) (Fin p) ℂ))
    (hΦ : CoordinateMeasurable Φ) (hCP : ∀ ω, CompletelyPositive (Φ ω))
    (htrace : MatrixTraceComplete μ Φ) (next : Ω → FiniteLocalCPInstrumentTree p n)
    (labels : ∀ ω, LeafLabels (next ω) L)
    (hChild : ∀ ell, Measurable (fun ω => (next ω).matrixReportedEffect (labels ω) ell)) :
    Integrable (cpAliceOutcomeEffect Φ next labels) μ := by
  let : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  have ht := (realMatrixTraceCLM (I := Fin m)).integrable_comp
    (integrable_canonicalGram μ Φ hΦ hCP htrace)
  change Integrable (fun ω => (canonicalGram Φ ω).trace.re) μ at ht
  apply (ht.const_mul (n : ℝ)).mono'
    (measurable_cpAliceOutcomeEffect Φ hΦ next labels hChild).stronglyMeasurable.aestronglyMeasurable
  exact Filter.Eventually.of_forall fun ω => by
    apply (pi_norm_le_iff_of_nonneg (mul_nonneg (Nat.cast_nonneg n)
      (Complex.nonneg_iff.mp (canonicalGram_posSemidef Φ ω).trace_nonneg).1)).mpr
    intro ell
    exact cpAliceOutcomeEffect_norm_bound Φ next labels ω ell

theorem integrable_cpBobOutcomeEffect
    (μ : Measure Ω) (hn : 0 < n)
    (Φ : Ω → (Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin p) (Fin p) ℂ))
    (hΦ : CoordinateMeasurable Φ) (hCP : ∀ ω, CompletelyPositive (Φ ω))
    (htrace : MatrixTraceComplete μ Φ) (next : Ω → FiniteLocalCPInstrumentTree m p)
    (labels : ∀ ω, LeafLabels (next ω) L)
    (hChild : ∀ ell, Measurable (fun ω => (next ω).matrixReportedEffect (labels ω) ell)) :
    Integrable (cpBobOutcomeEffect Φ next labels) μ := by
  let : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have ht := (realMatrixTraceCLM (I := Fin n)).integrable_comp
    (integrable_canonicalGram μ Φ hΦ hCP htrace)
  change Integrable (fun ω => (canonicalGram Φ ω).trace.re) μ at ht
  apply (ht.const_mul (m : ℝ)).mono'
    (measurable_cpBobOutcomeEffect Φ hΦ next labels hChild).stronglyMeasurable.aestronglyMeasurable
  exact Filter.Eventually.of_forall fun ω => by
    apply (pi_norm_le_iff_of_nonneg (mul_nonneg (Nat.cast_nonneg m)
      (Complex.nonneg_iff.mp (canonicalGram_posSemidef Φ ω).trace_nonneg).1)).mpr
    intro ell
    exact cpBobOutcomeEffect_norm_bound Φ next labels ω ell

end
end QuantumProver.ElegantJointMeasurement.InstrumentNormalization

namespace QuantumProver.ElegantJointMeasurement.InstrumentNormalization

noncomputable section

open QuantumProver.ElegantJointMeasurement.CP QuantumProver.ElegantJointMeasurement.CP.FiniteLocalCPInstrumentTree

set_option maxHeartbeats 800000

def summedPullback {S I O : Type*} [Fintype S] [Fintype O]
    (A : S → Matrix O I ℂ) (D : S → Matrix O O ℂ) : Matrix I I ℂ :=
  ∑ s, (A s)ᴴ * D s * A s

theorem summedPullback_loewner_bounds {S I O : Type*}
    [Fintype S] [Fintype I] [Fintype O] [DecidableEq O]
    (A : S → Matrix O I ℂ) (D : S → Matrix O O ℂ) (eta : ℝ)
    (hLower : ∀ s, (-eta) • (1 : Matrix O O ℂ) ≤ D s)
    (hUpper : ∀ s, D s ≤ eta • (1 : Matrix O O ℂ)) :
    (-eta) • (∑ s, (A s)ᴴ * A s) ≤ summedPullback A D ∧
      summedPullback A D ≤ eta • (∑ s, (A s)ᴴ * A s) := by
  constructor
  · have h := Finset.sum_le_sum (fun s (_ : s ∈ Finset.univ) =>
      matrix_pullback_mono (A s) (hLower s))
    simpa only [summedPullback, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
      ← Finset.smul_sum] using h
  · have h := Finset.sum_le_sum (fun s (_ : s ∈ Finset.univ) =>
      matrix_pullback_mono (A s) (hUpper s))
    simpa only [summedPullback, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
      ← Finset.smul_sum] using h

theorem summedPullback_isHermitian {S I O : Type*}
    [Fintype S] [Fintype I] [Fintype O]
    (A : S → Matrix O I ℂ) (D : S → Matrix O O ℂ) (hD : ∀ s, (D s).IsHermitian) :
    (summedPullback A D).IsHermitian := by
  change (∑ s, (A s)ᴴ * D s * A s)ᴴ = ∑ s, (A s)ᴴ * D s * A s
  rw [Matrix.conjTranspose_sum]
  apply Finset.sum_congr rfl
  intro s _
  exact Matrix.isHermitian_conjTranspose_mul_mul (A s) (hD s)

theorem hermitian_order_norm_bound {I : Type*} [Fintype I] [DecidableEq I]
    (D : Matrix I I ℂ) (eta : ℝ) (hEta : 0 ≤ eta) (hD : D.IsHermitian)
    (hLower : (-eta) • (1 : Matrix I I ℂ) ≤ D)
    (hUpper : D ≤ eta • (1 : Matrix I I ℂ)) : ‖D‖ ≤ eta := by
  have hOne : ‖(1 : Matrix I I ℂ)‖ ≤ 1 := by
    rcases subsingleton_or_nontrivial (Matrix I I ℂ) with hs | hn
    · let := hs
      simp only [Subsingleton.elim (1 : Matrix I I ℂ) 0, norm_zero, zero_le_one]
    · let := hn
      simp only [CStarRing.norm_one, le_refl]
  have hPos : ‖eta • (1 : Matrix I I ℂ)‖ ≤ eta := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hEta]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hOne hEta
  have hNeg : ‖(-eta) • (1 : Matrix I I ℂ)‖ ≤ eta := by
    simpa only [neg_smul, norm_neg] using hPos
  exact (IsSelfAdjoint.norm_le_max_of_le_of_le hLower hUpper hD.isSelfAdjoint).trans
    (max_le hNeg hPos)

theorem hermitian_order_euclideanOperatorNorm_bound {I : Type*}
    [Fintype I] [DecidableEq I]
    (D : Matrix I I ℂ) (eta : ℝ) (hEta : 0 ≤ eta) (hD : D.IsHermitian)
    (hLower : (-eta) • (1 : Matrix I I ℂ) ≤ D)
    (hUpper : D ≤ eta • (1 : Matrix I I ℂ)) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℂ) D‖ ≤ eta := by
  change ‖D‖ ≤ eta
  exact hermitian_order_norm_bound D eta hEta hD hLower hUpper

theorem summedPullback_complete_error_bound {S I O : Type*}
    [Fintype S] [Fintype I] [Fintype O] [DecidableEq I] [DecidableEq O]
    (A : S → Matrix O I ℂ) (D : S → Matrix O O ℂ) (eta : ℝ) (hEta : 0 ≤ eta)
    (hComplete : (∑ s, (A s)ᴴ * A s) = 1) (hD : ∀ s, (D s).IsHermitian)
    (hLower : ∀ s, (-eta) • (1 : Matrix O O ℂ) ≤ D s)
    (hUpper : ∀ s, D s ≤ eta • (1 : Matrix O O ℂ)) :
    ((-eta) • (1 : Matrix I I ℂ) ≤ summedPullback A D ∧
      summedPullback A D ≤ eta • (1 : Matrix I I ℂ)) ∧
      ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (summedPullback A D)‖ ≤ eta := by
  have hb := summedPullback_loewner_bounds A D eta hLower hUpper
  rw [hComplete] at hb
  exact ⟨hb, hermitian_order_euclideanOperatorNorm_bound _ eta hEta
    (summedPullback_isHermitian A D hD) hb.1 hb.2⟩

theorem leftKrausGram {S : Type*} [Fintype S] {m n p : ℕ}
    (K : S → Matrix (Fin p) (Fin m) ℂ) :
    (∑ s, (K s ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ))ᴴ *
      (K s ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ))) =
      (∑ s, (K s)ᴴ * K s) ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ) := by
  simp only [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
    ← Matrix.mul_kronecker_mul, Matrix.one_mul]
  exact sum_left_kronecker (fun s => (K s)ᴴ * K s) (1 : Matrix (Fin n) (Fin n) ℂ)

theorem rightKrausGram {S : Type*} [Fintype S] {m n p : ℕ}
    (K : S → Matrix (Fin p) (Fin n) ℂ) :
    (∑ s, ((1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ K s)ᴴ *
      ((1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ K s)) =
      (1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ (∑ s, (K s)ᴴ * K s) := by
  simp only [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
    ← Matrix.mul_kronecker_mul, Matrix.one_mul]
  exact sum_right_kronecker (1 : Matrix (Fin m) (Fin m) ℂ) (fun s => (K s)ᴴ * K s)

variable {L : Type*} [DecidableEq L] {m n p r : ℕ}

theorem aliceConditionalEffect_sub
    (K : Fin r → Matrix (Fin p) (Fin m) ℂ)
    (T U : Fin r → FiniteLocalCPInstrumentTree p n)
    (labelsT : ∀ s, LeafLabels (T s) L) (labelsU : ∀ s, LeafLabels (U s) L) (ell : L) :
    aliceConditionalEffect K T labelsT ell - aliceConditionalEffect K U labelsU ell =
      summedPullback (fun s => K s ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ))
        (fun s => (T s).matrixReportedEffect (labelsT s) ell -
          (U s).matrixReportedEffect (labelsU s) ell) := by
  unfold aliceConditionalEffect summedPullback
  rw [← Finset.sum_sub_distrib]
  simp only [Matrix.mul_sub, Matrix.sub_mul]

theorem bobConditionalEffect_sub
    (K : Fin r → Matrix (Fin p) (Fin n) ℂ)
    (T U : Fin r → FiniteLocalCPInstrumentTree m p)
    (labelsT : ∀ s, LeafLabels (T s) L) (labelsU : ∀ s, LeafLabels (U s) L) (ell : L) :
    bobConditionalEffect K T labelsT ell - bobConditionalEffect K U labelsU ell =
      summedPullback (fun s => (1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ K s)
        (fun s => (T s).matrixReportedEffect (labelsT s) ell -
          (U s).matrixReportedEffect (labelsU s) ell) := by
  unfold bobConditionalEffect summedPullback
  rw [← Finset.sum_sub_distrib]
  simp only [Matrix.mul_sub, Matrix.sub_mul]

theorem aliceConditionalEffect_replacement_order
    (K : Fin r → Matrix (Fin p) (Fin m) ℂ)
    (T U : Fin r → FiniteLocalCPInstrumentTree p n)
    (labelsT : ∀ s, LeafLabels (T s) L) (labelsU : ∀ s, LeafLabels (U s) L)
    (ell : L) (eta : ℝ)
    (hLower : ∀ s, (-eta) • (1 : Matrix (Fin p × Fin n) (Fin p × Fin n) ℂ) ≤
      (T s).matrixReportedEffect (labelsT s) ell - (U s).matrixReportedEffect (labelsU s) ell)
    (hUpper : ∀ s, (T s).matrixReportedEffect (labelsT s) ell -
      (U s).matrixReportedEffect (labelsU s) ell ≤
        eta • (1 : Matrix (Fin p × Fin n) (Fin p × Fin n) ℂ)) :
    (-eta) • ((∑ s, (K s)ᴴ * K s) ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ)) ≤
      aliceConditionalEffect K T labelsT ell - aliceConditionalEffect K U labelsU ell ∧
    aliceConditionalEffect K T labelsT ell - aliceConditionalEffect K U labelsU ell ≤
      eta • ((∑ s, (K s)ᴴ * K s) ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ)) := by
  rw [aliceConditionalEffect_sub]
  simpa only [leftKrausGram] using summedPullback_loewner_bounds
    (fun s => K s ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ)) _ eta hLower hUpper

theorem bobConditionalEffect_replacement_order
    (K : Fin r → Matrix (Fin p) (Fin n) ℂ)
    (T U : Fin r → FiniteLocalCPInstrumentTree m p)
    (labelsT : ∀ s, LeafLabels (T s) L) (labelsU : ∀ s, LeafLabels (U s) L)
    (ell : L) (eta : ℝ)
    (hLower : ∀ s, (-eta) • (1 : Matrix (Fin m × Fin p) (Fin m × Fin p) ℂ) ≤
      (T s).matrixReportedEffect (labelsT s) ell - (U s).matrixReportedEffect (labelsU s) ell)
    (hUpper : ∀ s, (T s).matrixReportedEffect (labelsT s) ell -
      (U s).matrixReportedEffect (labelsU s) ell ≤
        eta • (1 : Matrix (Fin m × Fin p) (Fin m × Fin p) ℂ)) :
    (-eta) • ((1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ (∑ s, (K s)ᴴ * K s)) ≤
      bobConditionalEffect K T labelsT ell - bobConditionalEffect K U labelsU ell ∧
    bobConditionalEffect K T labelsT ell - bobConditionalEffect K U labelsU ell ≤
      eta • ((1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ (∑ s, (K s)ᴴ * K s)) := by
  rw [bobConditionalEffect_sub]
  simpa only [rightKrausGram] using summedPullback_loewner_bounds
    (fun s => (1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ K s) _ eta hLower hUpper

variable {output outcomes : ℕ → ℕ}

theorem normalizedAliceNode_replacement_bound
    (K : (a : ℕ) → Fin (outcomes a) → Matrix (Fin (output a)) (Fin m) ℂ)
    (a : ℕ) (ha : (gramTotal K a).PosDef)
    (T U : Fin (outcomes a) → FiniteLocalCPInstrumentTree (output a) n)
    (labelsT : ∀ s, LeafLabels (T s) L) (labelsU : ∀ s, LeafLabels (U s) L)
    (ell : L) (eta : ℝ) (hEta : 0 ≤ eta)
    (hLower : ∀ s, (-eta) • (1 : Matrix (Fin (output a) × Fin n) (Fin (output a) × Fin n) ℂ) ≤
      (T s).matrixReportedEffect (labelsT s) ell - (U s).matrixReportedEffect (labelsU s) ell)
    (hUpper : ∀ s, (T s).matrixReportedEffect (labelsT s) ell -
      (U s).matrixReportedEffect (labelsU s) ell ≤
        eta • (1 : Matrix (Fin (output a) × Fin n) (Fin (output a) × Fin n) ℂ)) :
    let D := (normalizedAliceNode K a ha T).matrixReportedEffect
      (normalizedAliceLabels K a ha T labelsT) ell -
      (normalizedAliceNode K a ha U).matrixReportedEffect (normalizedAliceLabels K a ha U labelsU) ell
    ((-eta) • (1 : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) ≤ D ∧
      D ≤ eta • (1 : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ)) ∧
      ‖Matrix.toEuclideanCLM (𝕜 := ℂ) D‖ ≤ eta := by
  change ((-eta) • 1 ≤ _ ∧ _ ≤ eta • 1) ∧ _
  have heq :
      (normalizedAliceNode K a ha T).matrixReportedEffect (normalizedAliceLabels K a ha T labelsT) ell -
        (normalizedAliceNode K a ha U).matrixReportedEffect (normalizedAliceLabels K a ha U labelsU) ell =
      summedPullback (fun s => normalizedKraus K a s ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ))
        (fun s => (T s).matrixReportedEffect (labelsT s) ell -
          (U s).matrixReportedEffect (labelsU s) ell) := by
    change (krausAliceNode (normalizedKraus K a) _ T).matrixReportedEffect
      (krausAliceLabels _ _ T labelsT) ell -
      (krausAliceNode (normalizedKraus K a) _ U).matrixReportedEffect
        (krausAliceLabels _ _ U labelsU) ell = _
    rw [krausAliceNode_matrixReportedEffect, krausAliceNode_matrixReportedEffect,
      aliceConditionalEffect_sub]
  rw [heq]
  apply summedPullback_complete_error_bound _ _ eta hEta ?_ ?_ hLower hUpper
  · rw [leftKrausGram, normalizedKraus_complete_of_posDef K a ha, Matrix.one_kronecker_one]
  · intro s
    exact ((T s).matrixReportedEffect_posSemidef (labelsT s) ell).isHermitian.sub
      ((U s).matrixReportedEffect_posSemidef (labelsU s) ell).isHermitian

theorem normalizedBobNode_replacement_bound
    (K : (a : ℕ) → Fin (outcomes a) → Matrix (Fin (output a)) (Fin n) ℂ)
    (a : ℕ) (ha : (gramTotal K a).PosDef)
    (T U : Fin (outcomes a) → FiniteLocalCPInstrumentTree m (output a))
    (labelsT : ∀ s, LeafLabels (T s) L) (labelsU : ∀ s, LeafLabels (U s) L)
    (ell : L) (eta : ℝ) (hEta : 0 ≤ eta)
    (hLower : ∀ s, (-eta) • (1 : Matrix (Fin m × Fin (output a)) (Fin m × Fin (output a)) ℂ) ≤
      (T s).matrixReportedEffect (labelsT s) ell - (U s).matrixReportedEffect (labelsU s) ell)
    (hUpper : ∀ s, (T s).matrixReportedEffect (labelsT s) ell -
      (U s).matrixReportedEffect (labelsU s) ell ≤
        eta • (1 : Matrix (Fin m × Fin (output a)) (Fin m × Fin (output a)) ℂ)) :
    let D := (normalizedBobNode K a ha T).matrixReportedEffect
      (normalizedBobLabels K a ha T labelsT) ell -
      (normalizedBobNode K a ha U).matrixReportedEffect (normalizedBobLabels K a ha U labelsU) ell
    ((-eta) • (1 : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) ≤ D ∧
      D ≤ eta • (1 : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ)) ∧
      ‖Matrix.toEuclideanCLM (𝕜 := ℂ) D‖ ≤ eta := by
  change ((-eta) • 1 ≤ _ ∧ _ ≤ eta • 1) ∧ _
  have heq :
      (normalizedBobNode K a ha T).matrixReportedEffect (normalizedBobLabels K a ha T labelsT) ell -
        (normalizedBobNode K a ha U).matrixReportedEffect (normalizedBobLabels K a ha U labelsU) ell =
      summedPullback (fun s => (1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ normalizedKraus K a s)
        (fun s => (T s).matrixReportedEffect (labelsT s) ell -
          (U s).matrixReportedEffect (labelsU s) ell) := by
    change (krausBobNode (normalizedKraus K a) _ T).matrixReportedEffect
      (krausBobLabels _ _ T labelsT) ell -
      (krausBobNode (normalizedKraus K a) _ U).matrixReportedEffect
        (krausBobLabels _ _ U labelsU) ell = _
    rw [krausBobNode_matrixReportedEffect, krausBobNode_matrixReportedEffect,
      bobConditionalEffect_sub]
  rw [heq]
  apply summedPullback_complete_error_bound _ _ eta hEta ?_ ?_ hLower hUpper
  · rw [rightKrausGram, normalizedKraus_complete_of_posDef K a ha, Matrix.one_kronecker_one]
  · intro s
    exact ((T s).matrixReportedEffect_posSemidef (labelsT s) ell).isHermitian.sub
      ((U s).matrixReportedEffect_posSemidef (labelsU s) ell).isHermitian

end
end QuantumProver.ElegantJointMeasurement.InstrumentNormalization

namespace QuantumProver.ElegantJointMeasurement.InstrumentNormalization

noncomputable section

open MeasureTheory

set_option maxHeartbeats 800000

variable {Ω J : Type*} [MeasurableSpace Ω] [Fintype J] {m n p : ℕ}

def leftConditionalEffects
    (K : Ω → Matrix (Fin p) (Fin m) ℂ)
    (E : Ω → J → Matrix (Fin p × Fin n) (Fin p × Fin n) ℂ)
    (ω : Ω) (j : J) : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ :=
  (K ω ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ))ᴴ * E ω j *
    (K ω ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ))

def rightConditionalEffects
    (K : Ω → Matrix (Fin p) (Fin n) ℂ)
    (E : Ω → J → Matrix (Fin m × Fin p) (Fin m × Fin p) ℂ)
    (ω : Ω) (j : J) : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ :=
  ((1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ K ω)ᴴ * E ω j *
    ((1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ K ω)

omit [MeasurableSpace Ω] [Fintype J] in
theorem leftConditionalEffects_bounds
    (K : Ω → Matrix (Fin p) (Fin m) ℂ)
    (E : Ω → J → Matrix (Fin p × Fin n) (Fin p × Fin n) ℂ)
    (hEpsd : ∀ ω j, (E ω j).PosSemidef) (hEle : ∀ ω j, E ω j ≤ 1)
    (ω : Ω) (j : J) :
    (leftConditionalEffects K E ω j).PosSemidef ∧
      leftConditionalEffects K E ω j ≤
        ((K ω)ᴴ * K ω) ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ) := by
  refine ⟨matrix_pullback_posSemidef _ (hEpsd ω j), ?_⟩
  simpa only [leftConditionalEffects, Matrix.mul_one, Matrix.conjTranspose_kronecker,
    Matrix.conjTranspose_one, ← Matrix.mul_kronecker_mul, Matrix.one_mul] using
    matrix_pullback_mono (K ω ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ)) (hEle ω j)

omit [MeasurableSpace Ω] [Fintype J] in
theorem rightConditionalEffects_bounds
    (K : Ω → Matrix (Fin p) (Fin n) ℂ)
    (E : Ω → J → Matrix (Fin m × Fin p) (Fin m × Fin p) ℂ)
    (hEpsd : ∀ ω j, (E ω j).PosSemidef) (hEle : ∀ ω j, E ω j ≤ 1)
    (ω : Ω) (j : J) :
    (rightConditionalEffects K E ω j).PosSemidef ∧
      rightConditionalEffects K E ω j ≤
        (1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ ((K ω)ᴴ * K ω) := by
  refine ⟨matrix_pullback_posSemidef _ (hEpsd ω j), ?_⟩
  simpa only [rightConditionalEffects, Matrix.mul_one, Matrix.conjTranspose_kronecker,
    Matrix.conjTranspose_one, ← Matrix.mul_kronecker_mul, Matrix.one_mul] using
    matrix_pullback_mono ((1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ K ω) (hEle ω j)

omit [MeasurableSpace Ω] [Fintype J] in
theorem leftConditionalEffects_norm_bound
    (K : Ω → Matrix (Fin p) (Fin m) ℂ)
    (E : Ω → J → Matrix (Fin p × Fin n) (Fin p × Fin n) ℂ)
    (hEpsd : ∀ ω j, (E ω j).PosSemidef) (hEle : ∀ ω j, E ω j ≤ 1)
    (ω : Ω) (j : J) :
    ‖leftConditionalEffects K E ω j‖ ≤ (n : ℝ) * ((K ω)ᴴ * K ω).trace.re := by
  have hb := leftConditionalEffects_bounds K E hEpsd hEle ω j
  simpa only [trace_left_kronecker_one] using
    posSemidef_norm_trace_domination _ _ hb.1 hb.2

omit [MeasurableSpace Ω] [Fintype J] in
theorem rightConditionalEffects_norm_bound
    (K : Ω → Matrix (Fin p) (Fin n) ℂ)
    (E : Ω → J → Matrix (Fin m × Fin p) (Fin m × Fin p) ℂ)
    (hEpsd : ∀ ω j, (E ω j).PosSemidef) (hEle : ∀ ω j, E ω j ≤ 1)
    (ω : Ω) (j : J) :
    ‖rightConditionalEffects K E ω j‖ ≤ (m : ℝ) * ((K ω)ᴴ * K ω).trace.re := by
  have hb := rightConditionalEffects_bounds K E hEpsd hEle ω j
  simpa only [trace_right_kronecker_one] using
    posSemidef_norm_trace_domination _ _ hb.1 hb.2

omit [Fintype J] in
theorem measurable_leftConditionalEffects
    (K : Ω → Matrix (Fin p) (Fin m) ℂ)
    (E : Ω → J → Matrix (Fin p × Fin n) (Fin p × Fin n) ℂ)
    (hK : Measurable K) (hE : ∀ j, Measurable (fun ω => E ω j)) :
    Measurable (leftConditionalEffects K E) := by
  exact Measurable.of_eval fun j =>
    measurable_matrix_pullback _ _ (measurable_left_tensor K hK) (hE j)

omit [Fintype J] in
theorem measurable_rightConditionalEffects
    (K : Ω → Matrix (Fin p) (Fin n) ℂ)
    (E : Ω → J → Matrix (Fin m × Fin p) (Fin m × Fin p) ℂ)
    (hK : Measurable K) (hE : ∀ j, Measurable (fun ω => E ω j)) :
    Measurable (rightConditionalEffects K E) := by
  exact Measurable.of_eval fun j =>
    measurable_matrix_pullback _ _ (measurable_right_tensor K hK) (hE j)

theorem integrable_leftConditionalEffects
    (μ : Measure Ω) (K : Ω → Matrix (Fin p) (Fin m) ℂ)
    (E : Ω → J → Matrix (Fin p × Fin n) (Fin p × Fin n) ℂ)
    (hK : Measurable K) (hE : ∀ j, Measurable (fun ω => E ω j))
    (hGramInt : Integrable (fun ω => (K ω)ᴴ * K ω) μ)
    (hEpsd : ∀ ω j, (E ω j).PosSemidef) (hEle : ∀ ω j, E ω j ≤ 1) :
    Integrable (leftConditionalEffects K E) μ := by
  have ht := (realMatrixTraceCLM (I := Fin m)).integrable_comp hGramInt
  change Integrable (fun ω => ((K ω)ᴴ * K ω).trace.re) μ at ht
  apply (ht.const_mul (n : ℝ)).mono'
    (measurable_leftConditionalEffects K E hK hE).stronglyMeasurable.aestronglyMeasurable
  exact Filter.Eventually.of_forall fun ω => by
    apply (pi_norm_le_iff_of_nonneg (mul_nonneg (Nat.cast_nonneg n)
      (Complex.nonneg_iff.mp (Matrix.posSemidef_conjTranspose_mul_self (K ω)).trace_nonneg).1)).mpr
    intro j
    exact leftConditionalEffects_norm_bound K E hEpsd hEle ω j

theorem integrable_rightConditionalEffects
    (μ : Measure Ω) (K : Ω → Matrix (Fin p) (Fin n) ℂ)
    (E : Ω → J → Matrix (Fin m × Fin p) (Fin m × Fin p) ℂ)
    (hK : Measurable K) (hE : ∀ j, Measurable (fun ω => E ω j))
    (hGramInt : Integrable (fun ω => (K ω)ᴴ * K ω) μ)
    (hEpsd : ∀ ω j, (E ω j).PosSemidef) (hEle : ∀ ω j, E ω j ≤ 1) :
    Integrable (rightConditionalEffects K E) μ := by
  have ht := (realMatrixTraceCLM (I := Fin n)).integrable_comp hGramInt
  change Integrable (fun ω => ((K ω)ᴴ * K ω).trace.re) μ at ht
  apply (ht.const_mul (m : ℝ)).mono'
    (measurable_rightConditionalEffects K E hK hE).stronglyMeasurable.aestronglyMeasurable
  exact Filter.Eventually.of_forall fun ω => by
    apply (pi_norm_le_iff_of_nonneg (mul_nonneg (Nat.cast_nonneg m)
      (Complex.nonneg_iff.mp (Matrix.posSemidef_conjTranspose_mul_self (K ω)).trace_nonneg).1)).mpr
    intro j
    exact rightConditionalEffects_norm_bound K E hEpsd hEle ω j

end
end QuantumProver.ElegantJointMeasurement.InstrumentNormalization

namespace QuantumProver.ElegantJointMeasurement.InstrumentNormalization

noncomputable section

open QuantumProver.ElegantJointMeasurement.CP QuantumProver.ElegantJointMeasurement.CP.FiniteLocalCPInstrumentTree

set_option maxHeartbeats 800000

theorem summedPullback_sub {S I O : Type*} [Fintype S] [Fintype O]
    (A : S → Matrix O I ℂ) (E F : S → Matrix O O ℂ) :
    summedPullback A E - summedPullback A F = summedPullback A (fun s => E s - F s) := by
  simp only [summedPullback, Matrix.mul_sub, Matrix.sub_mul, Finset.sum_sub_distrib]

theorem leftPullback_error_order {S : Type*} [Fintype S] {m n p : ℕ}
    (K : S → Matrix (Fin p) (Fin m) ℂ)
    (D : S → Matrix (Fin p × Fin n) (Fin p × Fin n) ℂ) (eta : ℝ)
    (hLower : ∀ s, (-eta) • (1 : Matrix (Fin p × Fin n) (Fin p × Fin n) ℂ) ≤ D s)
    (hUpper : ∀ s, D s ≤ eta • (1 : Matrix (Fin p × Fin n) (Fin p × Fin n) ℂ)) :
    (-eta) • ((∑ s, (K s)ᴴ * K s) ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ)) ≤
      summedPullback (fun s => K s ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ)) D ∧
    summedPullback (fun s => K s ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ)) D ≤
      eta • ((∑ s, (K s)ᴴ * K s) ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ)) := by
  simpa only [leftKrausGram] using summedPullback_loewner_bounds
    (fun s => K s ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ)) D eta hLower hUpper

theorem rightPullback_error_order {S : Type*} [Fintype S] {m n p : ℕ}
    (K : S → Matrix (Fin p) (Fin n) ℂ)
    (D : S → Matrix (Fin m × Fin p) (Fin m × Fin p) ℂ) (eta : ℝ)
    (hLower : ∀ s, (-eta) • (1 : Matrix (Fin m × Fin p) (Fin m × Fin p) ℂ) ≤ D s)
    (hUpper : ∀ s, D s ≤ eta • (1 : Matrix (Fin m × Fin p) (Fin m × Fin p) ℂ)) :
    (-eta) • ((1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ (∑ s, (K s)ᴴ * K s)) ≤
      summedPullback (fun s => (1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ K s) D ∧
    summedPullback (fun s => (1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ K s) D ≤
      eta • ((1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ (∑ s, (K s)ᴴ * K s)) := by
  simpa only [rightKrausGram] using summedPullback_loewner_bounds
    (fun s => (1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ K s) D eta hLower hUpper

variable {m n : ℕ} {output outcomes : ℕ → ℕ}

theorem normalizedLeftPullback_error_bound
    (K : (a : ℕ) → Fin (outcomes a) → Matrix (Fin (output a)) (Fin m) ℂ)
    (a : ℕ) (ha : (gramTotal K a).PosDef)
    (D : Fin (outcomes a) → Matrix (Fin (output a) × Fin n) (Fin (output a) × Fin n) ℂ)
    (eta : ℝ) (hEta : 0 ≤ eta) (hD : ∀ s, (D s).IsHermitian)
    (hLower : ∀ s, (-eta) • (1 : Matrix (Fin (output a) × Fin n) (Fin (output a) × Fin n) ℂ) ≤ D s)
    (hUpper : ∀ s, D s ≤ eta • (1 : Matrix (Fin (output a) × Fin n) (Fin (output a) × Fin n) ℂ)) :
    let R := summedPullback (fun s => normalizedKraus K a s ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ)) D
    ((-eta) • (1 : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) ≤ R ∧ R ≤ eta • 1) ∧
      ‖Matrix.toEuclideanCLM (𝕜 := ℂ) R‖ ≤ eta := by
  apply summedPullback_complete_error_bound _ _ eta hEta ?_ hD hLower hUpper
  rw [leftKrausGram, normalizedKraus_complete_of_posDef K a ha, Matrix.one_kronecker_one]

theorem normalizedRightPullback_error_bound
    (K : (a : ℕ) → Fin (outcomes a) → Matrix (Fin (output a)) (Fin n) ℂ)
    (a : ℕ) (ha : (gramTotal K a).PosDef)
    (D : Fin (outcomes a) → Matrix (Fin m × Fin (output a)) (Fin m × Fin (output a)) ℂ)
    (eta : ℝ) (hEta : 0 ≤ eta) (hD : ∀ s, (D s).IsHermitian)
    (hLower : ∀ s, (-eta) • (1 : Matrix (Fin m × Fin (output a)) (Fin m × Fin (output a)) ℂ) ≤ D s)
    (hUpper : ∀ s, D s ≤ eta • (1 : Matrix (Fin m × Fin (output a)) (Fin m × Fin (output a)) ℂ)) :
    let R := summedPullback (fun s => (1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ normalizedKraus K a s) D
    ((-eta) • (1 : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) ≤ R ∧ R ≤ eta • 1) ∧
      ‖Matrix.toEuclideanCLM (𝕜 := ℂ) R‖ ≤ eta := by
  apply summedPullback_complete_error_bound _ _ eta hEta ?_ hD hLower hUpper
  rw [rightKrausGram, normalizedKraus_complete_of_posDef K a ha, Matrix.one_kronecker_one]

variable {L : Type*} [DecidableEq L]

theorem normalizedLeftChildReplacement_bound
    (K : (a : ℕ) → Fin (outcomes a) → Matrix (Fin (output a)) (Fin m) ℂ)
    (a : ℕ) (ha : (gramTotal K a).PosDef)
    (E : Fin (outcomes a) → Matrix (Fin (output a) × Fin n) (Fin (output a) × Fin n) ℂ)
    (U : Fin (outcomes a) → FiniteLocalCPInstrumentTree (output a) n)
    (labelsU : ∀ s, LeafLabels (U s) L) (ell : L)
    (eta : ℝ) (hEta : 0 ≤ eta) (hE : ∀ s, (E s).IsHermitian)
    (hLower : ∀ s, (-eta) • (1 : Matrix (Fin (output a) × Fin n) (Fin (output a) × Fin n) ℂ) ≤
      E s - (U s).matrixReportedEffect (labelsU s) ell)
    (hUpper : ∀ s, E s - (U s).matrixReportedEffect (labelsU s) ell ≤
      eta • (1 : Matrix (Fin (output a) × Fin n) (Fin (output a) × Fin n) ℂ)) :
    let R := summedPullback (fun s => normalizedKraus K a s ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ)) E -
      (normalizedAliceNode K a ha U).matrixReportedEffect (normalizedAliceLabels K a ha U labelsU) ell
    ((-eta) • (1 : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) ≤ R ∧ R ≤ eta • 1) ∧
      ‖Matrix.toEuclideanCLM (𝕜 := ℂ) R‖ ≤ eta := by
  change ((-eta) • 1 ≤ _ ∧ _ ≤ eta • 1) ∧ _
  have heq : (normalizedAliceNode K a ha U).matrixReportedEffect
      (normalizedAliceLabels K a ha U labelsU) ell =
      summedPullback (fun s => normalizedKraus K a s ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ))
        (fun s => (U s).matrixReportedEffect (labelsU s) ell) := by
    change (krausAliceNode (normalizedKraus K a) _ U).matrixReportedEffect
      (krausAliceLabels _ _ U labelsU) ell = _
    exact krausAliceNode_matrixReportedEffect _ _ U labelsU ell
  rw [heq, summedPullback_sub]
  exact normalizedLeftPullback_error_bound K a ha _ eta hEta
    (fun s => (hE s).sub ((U s).matrixReportedEffect_posSemidef (labelsU s) ell).isHermitian)
    hLower hUpper

theorem normalizedRightChildReplacement_bound
    (K : (a : ℕ) → Fin (outcomes a) → Matrix (Fin (output a)) (Fin n) ℂ)
    (a : ℕ) (ha : (gramTotal K a).PosDef)
    (E : Fin (outcomes a) → Matrix (Fin m × Fin (output a)) (Fin m × Fin (output a)) ℂ)
    (U : Fin (outcomes a) → FiniteLocalCPInstrumentTree m (output a))
    (labelsU : ∀ s, LeafLabels (U s) L) (ell : L)
    (eta : ℝ) (hEta : 0 ≤ eta) (hE : ∀ s, (E s).IsHermitian)
    (hLower : ∀ s, (-eta) • (1 : Matrix (Fin m × Fin (output a)) (Fin m × Fin (output a)) ℂ) ≤
      E s - (U s).matrixReportedEffect (labelsU s) ell)
    (hUpper : ∀ s, E s - (U s).matrixReportedEffect (labelsU s) ell ≤
      eta • (1 : Matrix (Fin m × Fin (output a)) (Fin m × Fin (output a)) ℂ)) :
    let R := summedPullback (fun s => (1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ normalizedKraus K a s) E -
      (normalizedBobNode K a ha U).matrixReportedEffect (normalizedBobLabels K a ha U labelsU) ell
    ((-eta) • (1 : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) ≤ R ∧ R ≤ eta • 1) ∧
      ‖Matrix.toEuclideanCLM (𝕜 := ℂ) R‖ ≤ eta := by
  change ((-eta) • 1 ≤ _ ∧ _ ≤ eta • 1) ∧ _
  have heq : (normalizedBobNode K a ha U).matrixReportedEffect
      (normalizedBobLabels K a ha U labelsU) ell =
      summedPullback (fun s => (1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ normalizedKraus K a s)
        (fun s => (U s).matrixReportedEffect (labelsU s) ell) := by
    change (krausBobNode (normalizedKraus K a) _ U).matrixReportedEffect
      (krausBobLabels _ _ U labelsU) ell = _
    exact krausBobNode_matrixReportedEffect _ _ U labelsU ell
  rw [heq, summedPullback_sub]
  exact normalizedRightPullback_error_bound K a ha _ eta hEta
    (fun s => (hE s).sub ((U s).matrixReportedEffect_posSemidef (labelsU s) ell).isHermitian)
    hLower hUpper

end
end QuantumProver.ElegantJointMeasurement.InstrumentNormalization

import QuantumProver.InformationTheory.AmplitudeDamping.SecretKey.PrivateTestResource
import QuantumProver.InformationTheory.AmplitudeDamping.SecretKey.EntropyBounds
import QuantumProver.InformationTheory.SuperchannelDiscrimination.QuantumTestingPowerBound
import QuantumProver.InformationTheory.MeasuredRelativeEntropyVariational
import QuantumProver.InformationTheory.AmplitudeDamping.SecretKey.ParallelLanes
import QuantumProver.InformationTheory.AmplitudeDamping.SecretKey.WeakBinaryConjugate
import QuantumProver.InformationTheory.AmplitudeDamping.SecretKey.ProductPrivacyTest

set_option autoImplicit false
noncomputable section
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker

namespace QuantumProver.AmplitudeDamping.SecretKey.WeakPrivateTestResource

open QuantumProver.SuperchannelDiscrimination
open PrivateTestResource PrivateTest

abbrev umegakiBits {I : Type*} [Fintype I] [DecidableEq I]
    (ρ σ : Matrix I I ℂ) : EReal := FlaggedStates.relativeEntropyBits ρ σ

variable {I O Z : Type*} [Fintype I] [Fintype O] [Fintype Z]
  [DecidableEq I] [DecidableEq O]

theorem channel_umegaki_le (C : KrausChannel I O Z) (ρ σ : Density I) :
    umegakiBits (C.onDensity ρ).mat (C.onDensity σ).mat ≤
      umegakiBits ρ.mat σ.mat :=
  InputSupport.relativeEntropyBits_kraus_dpi C.op C.complete ρ.positive σ.positive

section Resource

variable {A B A' B' : Type*}
  [Fintype A] [Fintype B] [Fintype A'] [Fintype B']
  [DecidableEq A] [DecidableEq B] [DecidableEq A'] [DecidableEq B']

def normalizedSEPUmegaki (ρ : Density (A × B)) : EReal :=
  sInf ((fun σ : Density (A × B) => umegakiBits ρ.mat σ.mat) ''
    {σ : Density (A × B) | IsSeparable σ})

theorem normalizedSEPUmegaki_le_comparison (ρ σ : Density (A × B))
    (hσ : IsSeparable σ) : normalizedSEPUmegaki ρ ≤ umegakiBits ρ.mat σ.mat :=
  sInf_le ⟨σ, hσ, rfl⟩

theorem normalizedSEPUmegaki_localProductChannel_le
    (K : Z → Matrix A' A ℂ) (L : Z → Matrix B' B ℂ)
    (hKL : ∑ z, (K z ⊗ₖ L z)ᴴ * (K z ⊗ₖ L z) = 1)
    (ρ : Density (A × B)) :
    normalizedSEPUmegaki ((localProductChannel K L hKL).onDensity ρ) ≤
      normalizedSEPUmegaki ρ := by
  unfold normalizedSEPUmegaki
  apply le_sInf
  rintro x ⟨σ, hσ, rfl⟩
  exact (normalizedSEPUmegaki_le_comparison
    ((localProductChannel K L hKL).onDensity ρ)
    ((localProductChannel K L hKL).onDensity σ)
    (localProductChannel_separable K L hKL σ hσ)).trans (channel_umegaki_le _ ρ σ)

end Resource

section PhysicalPOVM

open QuantumProver.MeasuredRelativeEntropyVariational

variable {K : Type*} [Fintype K] [DecidableEq K]

theorem diagonal_support_iff (p q : K → ℝ) :
    FlaggedStates.HasSupportIn (diagonal (fun i => (p i : ℂ)))
      (diagonal (fun i => (q i : ℂ))) ↔ ∀ i, q i = 0 → p i = 0 := by
  constructor
  · intro hs i hqi
    have hv : diagonal (fun j => (q j : ℂ)) *ᵥ Pi.single i 1 = 0 := by
      ext j
      by_cases hji : j = i
      · subst j; simp [Matrix.mulVec_diagonal, hqi]
      · simp [Matrix.mulVec_diagonal, hji]
    have hh := congrFun (hs (Pi.single i 1) hv) i
    exact_mod_cast (by simpa [Matrix.mulVec_diagonal] using hh : (p i : ℂ) = 0)
  · intro hs v hv
    ext i
    have hh := congrFun hv i
    simp only [Matrix.mulVec_diagonal, Pi.zero_apply] at hh ⊢
    by_cases hqi : q i = 0
    · rw [hs i hqi]; simp
    · have hqiC : (q i : ℂ) ≠ 0 := by exact_mod_cast hqi
      rw [(mul_eq_zero.mp hh).resolve_left hqiC]; simp

theorem diagonal_umegaki_eq_classical (p q : K → ℝ) (hp : ∀ i, 0 ≤ p i) :
    umegakiBits (diagonal (fun i => (p i : ℂ))) (diagonal (fun i => (q i : ℂ))) =
      classicalRelativeEntropyBits p q := by
  classical
  by_cases hs : ∀ i, q i = 0 → p i = 0
  · have hs' : ∀ i, p i ≠ 0 → q i ≠ 0 := by
      intro i hi hq
      exact hi (hs i hq)
    rw [classicalRelativeEntropyBits_finite_of_support p q hs']
    unfold umegakiBits
    rw [FlaggedStates.relativeEntropyBits, ite_eq_left ((diagonal_support_iff p q).mpr hs)]
    congr 1
    simp [FlaggedStates.finiteRelativeEntropyBits, TensorEntropy.cfc_diagonal_real,
      Complex.re_sum, Finset.sum_div,
      Finset.sum_sub_distrib, mul_sub, mul_div_assoc, sub_div]
  · obtain ⟨i, hqi, hpi⟩ : ∃ i, q i = 0 ∧ p i ≠ 0 := by
      obtain ⟨i, hqi, hpi⟩ : ∃ i, ∃ (_ : q i = 0), p i ≠ 0 := by
        simpa only [not_forall, not_imp] using hs
      exact ⟨i, hqi, hpi⟩
    have hpos : 0 < p i := lt_of_le_of_ne (hp i) (Ne.symm hpi)
    rw [classicalRelativeEntropyBits_eq_top_of_zero_reference_event p q i hpos hqi]
    simp [umegakiBits, FlaggedStates.relativeEntropyBits, diagonal_support_iff, hs]

omit [DecidableEq I] in
theorem trace_mul_eq_real {X Y : Matrix I I ℂ}
    (hX : X.IsHermitian) (hY : Y.IsHermitian) :
    (((X * Y).trace.re : ℝ) : ℂ) = (X * Y).trace := by
  have hs : star (X * Y).trace = (X * Y).trace := by
    rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, hX.eq, hY.eq,
      Matrix.trace_mul_comm]
  apply Complex.ext
  · rfl
  · have hi := congrArg Complex.im hs
    simp only [Complex.star_def, Complex.conj_im] at hi
    simp only [Complex.ofReal_im]
    linarith

theorem povm_classical_umegaki_le (M : POVM I K) (ρ σ : Density I) :
    classicalRelativeEntropyBits (measurementProbability M ρ.mat)
      (measurementProbability M σ.mat) ≤ umegakiBits ρ.mat σ.mat := by
  let C := finiteMeasurementChannel M.effect M.positive M.normalized
  have h := channel_umegaki_le C ρ σ
  have hEval (X : Density I) :
      (C.onDensity X).mat = diagonal (fun b => (measurementProbability M X.mat b : ℂ)) := by
    change C.eval X.mat = _
    rw [finiteMeasurementChannel_eval]
    congr 1
    funext b
    exact (trace_mul_eq_real (M.positive b).1 X.positive.1).symm.trans
      (by rw [Matrix.trace_mul_comm]; rfl)
  rw [hEval ρ, hEval σ, diagonal_umegaki_eq_classical _ _
    (measurementProbability_nonneg M ρ.positive)] at h
  exact h

omit [DecidableEq K] in

theorem classical_kl_exponential_test (p q f : K → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    (hpsum : ∑ i, p i = 1) (hqsum : ∑ i, q i = 1) :
    (((∑ i, p i * f i) - Real.log (∑ i, q i * Real.exp (f i))) / Real.log 2 : ℝ) ≤
      (classicalRelativeEntropyBits p q : EReal) := by
  let Z : ℝ := ∑ i, q i * Real.exp (f i)
  have hZ : 0 < Z := by
    obtain ⟨i, hi⟩ : ∃ i, 0 < q i := by
      by_contra hn
      have hz : ∑ i, q i = 0 := Finset.sum_eq_zero (fun i _ => by
        have hh : ¬ 0 < q i := (not_exists.mp hn) i
        exact le_antisymm (le_of_not_gt hh) (hq i))
      linarith
    exact (mul_pos hi (Real.exp_pos _)).trans_le
      (Finset.single_le_sum (fun j _ => mul_nonneg (hq j) (Real.exp_pos _).le)
        (Finset.mem_univ i))
  let r : K → ℝ := fun i => Real.exp (f i) / Z
  have hr : ∀ i, 0 < r i := fun i => div_pos (Real.exp_pos _) hZ
  have hlog : ∀ i, Real.log (r i) = f i - Real.log Z := by
    intro i
    exact (Real.log_div (Real.exp_pos _).ne' hZ.ne').trans
      (by rw [Real.log_exp])
  have hqr : ∑ i, q i * r i = 1 := by
    simp only [r, ← mul_div_assoc, ← Finset.sum_div]
    exact div_self hZ.ne'
  have hpf : ∑ i, p i * Real.log (r i) = (∑ i, p i * f i) - Real.log Z := by
    simp only [hlog, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hpsum, one_mul]
  have h := vectorObjectiveBits_le_classicalRelativeEntropyBits p q r hp hq hr
  rw [vectorObjectiveBits_normalized p q r hpsum, hqr, hpf] at h
  simpa only [add_sub_cancel_right] using h

theorem povm_umegaki_exponential_test (M : POVM I K) (ρ σ : Density I) (f : K → ℝ) :
    (((∑ i, measurementProbability M ρ.mat i * f i) -
      Real.log (∑ i, measurementProbability M σ.mat i * Real.exp (f i))) /
      Real.log 2 : ℝ) ≤ (umegakiBits ρ.mat σ.mat : EReal) :=
  (classical_kl_exponential_test _ _ f
    (measurementProbability_nonneg M ρ.positive)
    (measurementProbability_nonneg M σ.positive)
    (measurementProbability_sum_density M ⟨ρ.positive, ρ.normalized⟩)
    (measurementProbability_sum_density M ⟨σ.positive, σ.normalized⟩)).trans
    (povm_classical_umegaki_le M ρ σ)

end PhysicalPOVM

section WeakScalar

def testMoment (d : ℕ) (s : ℝ) : ℝ := 1 + (2 ^ s - 1) / (d : ℝ)

def testObjective (d : ℕ) (x s : ℝ) : ℝ := s * x - log2 (testMoment d s)

def weakTestValues (d : ℕ) (x : ℝ) : Set ℝ :=
  {y | ∃ s : ℝ, 0 ≤ s ∧ y = testObjective d x s}

def weakTestLowerBound (d : ℕ) (x : ℝ) : ℝ := sSup (weakTestValues d x)

theorem testMoment_ge_one (d : ℕ) {s : ℝ} (hs : 0 ≤ s) : 1 ≤ testMoment d s := by
  have hpow : 1 ≤ (2 : ℝ) ^ s := Real.one_le_rpow (by norm_num) hs
  exact le_add_of_nonneg_right (div_nonneg (sub_nonneg.mpr hpow) (Nat.cast_nonneg d))

theorem testObjective_zero (d : ℕ) (x : ℝ) : testObjective d x 0 = 0 := by
  simp [testObjective, testMoment, log2]

theorem weakTestValues_nonempty (d : ℕ) (x : ℝ) : (weakTestValues d x).Nonempty :=
  ⟨0, 0, le_rfl, (testObjective_zero d x).symm⟩

theorem testObjective_le_log_card {d : ℕ} (hd : 0 < d) {x s : ℝ}
    (hx : x ≤ 1) (hs : 0 ≤ s) : testObjective d x s ≤ log2 (d : ℝ) := by
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hdOne : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hpow : 0 < (2 : ℝ) ^ s := Real.rpow_pos_of_pos (by norm_num) _
  have hm : (2 : ℝ) ^ s / d ≤ testMoment d s := by
    unfold testMoment
    apply (div_le_iff₀ hdR).mpr
    have hcalc : (1 + ((2 : ℝ) ^ s - 1) / d) * d = d + (2 : ℝ) ^ s - 1 := by
      field_simp
      ring
    rw [hcalc]
    linarith
  have hl := Real.log_le_log (div_pos hpow hdR) hm
  rw [Real.log_div hpow.ne' hdR.ne', Real.log_rpow (by norm_num : 0 < (2 : ℝ))] at hl
  unfold testObjective log2
  have hmul : s * x ≤ s := by nlinarith
  have hlogTwo := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  apply (le_div_iff₀ hlogTwo).mpr
  have hidentity : (s * x - Real.log (testMoment d s) / Real.log 2) * Real.log 2 =
      s * x * Real.log 2 - Real.log (testMoment d s) := by
    field_simp
  rw [hidentity]
  nlinarith

theorem weakTestValues_bddAbove {d : ℕ} (hd : 0 < d) {x : ℝ} (hx : x ≤ 1) :
    BddAbove (weakTestValues d x) := by
  refine ⟨log2 (d : ℝ), ?_⟩
  rintro y ⟨s, hs, rfl⟩
  exact testObjective_le_log_card hd hx hs

theorem weakTestLowerBound_nonneg (d : ℕ) (x : ℝ) (hB : BddAbove (weakTestValues d x)) :
    0 ≤ weakTestLowerBound d x :=
  le_csSup hB ⟨0, le_rfl, (testObjective_zero d x).symm⟩

theorem weakTestLowerBound_le_ereal {d : ℕ} (_hd : 0 < d) {x : ℝ} (_hx : x ≤ 1)
    {R : EReal} (h : ∀ s : ℝ, 0 ≤ s → (testObjective d x s : EReal) ≤ R) :
    (weakTestLowerBound d x : EReal) ≤ R := by
  by_contra hn
  have hlt : R < (weakTestLowerBound d x : EReal) := lt_of_not_ge hn
  obtain ⟨r, hRr, hrL⟩ := EReal.exists_between_coe_real hlt
  have hrL' : r < weakTestLowerBound d x := EReal.coe_lt_coe_iff.mp hrL
  obtain ⟨y, hy, hry⟩ := exists_lt_of_lt_csSup (weakTestValues_nonempty d x) hrL'
  obtain ⟨s, hs, rfl⟩ := hy
  exact not_lt_of_ge (h s hs) (hRr.trans (EReal.coe_lt_coe_iff.mpr hry))

end WeakScalar

section PrivateBinary

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] {d : ℕ}

def matrixPrivacyBinaryChannel
    (U : Fin d → EuclideanSpace ℂ (A × B) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (A × B))
    (hd : 0 < d) : KrausCompletion.FiniteCPTP
      ((Fin d × A) × (Fin d × B)) BinaryMeasurement.Outcome where
  map := BinaryMeasurement.measurement (privacyEffect U)
  completelyPositive := BinaryMeasurement.measurement_completelyPositive
    ⟨privacyEffect_posSemidef U, privacyEffect_complement_posSemidef U hd⟩
  tracePreserving := BinaryMeasurement.measurement_tracePreserving (privacyEffect U)

theorem privacy_binary_umegaki_dpi
    (U : Fin d → EuclideanSpace ℂ (A × B) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (A × B))
    (hd : 0 < d) (ρ σ : Density ((Fin d × A) × (Fin d × B))) :
    extendedBinaryRelativeEntropyBits (privacyAcceptance U ρ.mat)
      (privacyAcceptance U σ.mat) ≤ umegakiBits ρ.mat σ.mat := by
  have h := AbstractDPI.relativeEntropyBits_cptp_dpi
    (matrixPrivacyBinaryChannel U hd) ρ.positive σ.positive
  change FlaggedStates.relativeEntropyBits
    (BinaryMeasurement.measurement (privacyEffect U) ρ.mat)
    (BinaryMeasurement.measurement (privacyEffect U) σ.mat) ≤ _ at h
  rw [BinaryMeasurement.measurement_relativeEntropyBits
    ⟨ρ.positive, ρ.normalized⟩ ⟨σ.positive, σ.normalized⟩
    ⟨privacyEffect_posSemidef U, privacyEffect_complement_posSemidef U hd⟩] at h
  have hpass (X : Matrix ((Fin d × A) × (Fin d × B))
      ((Fin d × A) × (Fin d × B)) ℂ) :
      FlaggedStates.acceptanceProbability X (privacyEffect U) = privacyAcceptance U X := by
    rw [FlaggedStates.acceptanceProbability, Matrix.trace_mul_comm, privacyEffect_trace]
  simpa only [hpass] using h

open QuantumProver.MeasuredRelativeEntropyVariational

def privacyPOVM
    (U : Fin d → EuclideanSpace ℂ (A × B) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (A × B))
    (hd : 0 < d) : POVM ((Fin d × A) × (Fin d × B)) (Fin 2) where
  effect := privacyBinaryEffect U
  positive := privacyBinaryEffect_positive U hd
  normalized := privacyBinaryEffect_sum U

theorem privacyPOVM_probability
    (U : Fin d → EuclideanSpace ℂ (A × B) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (A × B))
    (hd : 0 < d) (ρ : Density ((Fin d × A) × (Fin d × B))) :
    measurementProbability (privacyPOVM U hd) ρ.mat = binaryWeights (privacyAcceptance U ρ.mat) := by
  funext b
  unfold measurementProbability privacyPOVM binaryWeights privacyBinaryEffect
  by_cases hb : b = 0
  · simp only [hb, ite_true]
    rw [Matrix.trace_mul_comm, privacyEffect_trace]
  · simp only [hb, ite_false, Matrix.mul_sub, Matrix.mul_one, Matrix.trace_sub,
      Complex.sub_re, ρ.normalized, Complex.one_re]
    rw [Matrix.trace_mul_comm, privacyEffect_trace]

theorem privacy_umegaki_testObjective
    (U : Fin d → EuclideanSpace ℂ (A × B) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (A × B))
    (hd : 0 < d) (ρ σ : Density ((Fin d × A) × (Fin d × B))) (hσ : IsSeparable σ)
    {s : ℝ} (hs : 0 ≤ s) :
    (testObjective d (privacyAcceptance U ρ.mat) s : EReal) ≤ umegakiBits ρ.mat σ.mat := by
  let p := privacyAcceptance U ρ.mat
  let q := privacyAcceptance U σ.mat
  let f : Fin 2 → ℝ := fun b => if b = 0 then s * Real.log 2 else 0
  have h := povm_umegaki_exponential_test (privacyPOVM U hd) ρ σ f
  rw [privacyPOVM_probability U hd ρ, privacyPOVM_probability U hd σ] at h
  have he : Real.exp (s * Real.log 2) = (2 : ℝ) ^ s := by
    rw [Real.rpow_def_of_pos (by norm_num : 0 < (2 : ℝ))]
    congr 1
    ring
  have hmean : ∑ b : Fin 2, binaryWeights p b * f b = s * p * Real.log 2 := by
    simp only [Fin.sum_univ_two, binaryWeights, f]
    norm_num
    ring
  have hZeq : ∑ b : Fin 2, binaryWeights q b * Real.exp (f b) = 1 + q * ((2 : ℝ) ^ s - 1) := by
    simp only [Fin.sum_univ_two, binaryWeights, f]
    norm_num
    rw [he]
    ring
  rw [hmean, hZeq] at h
  have hsid : (s * p * Real.log 2 - Real.log (1 + q * ((2 : ℝ) ^ s - 1))) / Real.log 2 =
      s * p - log2 (1 + q * ((2 : ℝ) ^ s - 1)) := by
    unfold log2
    field_simp [ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 2))]
  rw [hsid] at h
  have ht : 0 ≤ (2 : ℝ) ^ s - 1 :=
    sub_nonneg.mpr (Real.one_le_rpow (by norm_num) hs)
  have hq0 : 0 ≤ q := (privacyAcceptance_density_mem_Icc U hd σ).1
  have hq : q ≤ 1 / (d : ℝ) := privacyAcceptance_separable_le U σ hσ
  have hZpos : 0 < 1 + q * ((2 : ℝ) ^ s - 1) := by positivity
  have hZle : 1 + q * ((2 : ℝ) ^ s - 1) ≤ testMoment d s := by
    unfold testMoment
    have hh := mul_le_mul_of_nonneg_right hq ht
    have hh' : q * ((2 : ℝ) ^ s - 1) ≤ ((2 : ℝ) ^ s - 1) / d := by
      simpa only [one_div_mul_eq_div] using hh
    linarith
  have hl : log2 (1 + q * ((2 : ℝ) ^ s - 1)) ≤ log2 (testMoment d s) :=
    div_le_div_of_nonneg_right (Real.log_le_log hZpos hZle)
      (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
  exact (EReal.coe_le_coe_iff.mpr (by dsimp [testObjective]; linarith :
    testObjective d p s ≤ s * p - log2 (1 + q * ((2 : ℝ) ^ s - 1)))).trans h

theorem privacy_normalizedSEP_weak_test
    (U : Fin d → EuclideanSpace ℂ (A × B) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (A × B))
    (hd : 0 < d) (ρ : Density ((Fin d × A) × (Fin d × B))) :
    (weakTestLowerBound d (privacyAcceptance U ρ.mat) : EReal) ≤ normalizedSEPUmegaki ρ := by
  apply le_sInf
  rintro x ⟨σ, hσ, rfl⟩
  exact weakTestLowerBound_le_ereal hd (privacyAcceptance_density_mem_Icc U hd ρ).2
    (fun _ hs => privacy_umegaki_testObjective U hd ρ σ hσ hs)

end PrivateBinary

section LocalPrivateLift

open PhysicalPurification

variable {A B R : Type*} [Fintype A] [Fintype B] [Fintype R]
  [DecidableEq A] [DecidableEq B] [DecidableEq R] {d : ℕ}

theorem normalizedSEPUmegaki_keyRecording_le
    (labelA : A → Fin d) (labelB : B → Fin d) (ρ : Density (A × B)) :
    normalizedSEPUmegaki ((keyRecordingChannel labelA labelB).onDensity ρ) ≤
      normalizedSEPUmegaki ρ :=
  normalizedSEPUmegaki_localProductChannel_le
    (fun _ : Unit => labelRecordingMatrix labelA)
    (fun _ : Unit => labelRecordingMatrix labelB)
    (keyRecordingChannel labelA labelB).complete ρ

theorem normalizedSEPUmegaki_keyPadding_le
    (ρ : Density ((Fin d × A) × (Fin d × B))) :
    normalizedSEPUmegaki
      ((keyPaddingChannel (E := R) (d := d) (A := A) (B := B)).onDensity ρ) ≤
      normalizedSEPUmegaki ρ :=
  normalizedSEPUmegaki_localProductChannel_le
    (fun z : Unit => ((paddingChannel (S := A) (E := R)).withMemory (Fin d)).op z)
    (fun _ : Unit => (1 : Matrix (Fin d × B) (Fin d × B) ℂ))
    (keyPaddingChannel (E := R) (d := d) (A := A) (B := B)).complete ρ

end LocalPrivateLift

section RetainedPrivateLift

open PhysicalProtocol PhysicalPurification

variable {p : ℝ} {a b af bf d : ℕ} {E : Type*} [Fintype E] [DecidableEq E]

theorem retainedPrivateLift_umegaki_le
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (P : FiniteKeyProtocol p a b af bf)
    (labelA : Fin af → Fin d) (labelB : Fin bf → Fin d)
    (ρ : Density ((Fin a × Fin b) × E)) :
    normalizedSEPUmegaki (honestMarginal
      ((P.retainedProtocolPrivateLiftChannel (E := E) hp0 hp1 labelA labelB).onDensity ρ)) ≤
      normalizedSEPUmegaki
        (honestMarginal ((PublicHistory.wholeRetainedChannelWithEve_B hp0 hp1 P E).onDensity ρ)) := by
  rw [retainedPrivateLift_honest_eq]
  exact (normalizedSEPUmegaki_keyPadding_le _).trans
    (normalizedSEPUmegaki_keyRecording_le _ _ _)

end RetainedPrivateLift

section TensorPOVM

open QuantumProver.MeasuredRelativeEntropyVariational IndependentLanes

variable {K : Type*} [Fintype K] [DecidableEq K] {n : ℕ}

def tensorPOVM (M : POVM I K) : (n : ℕ) → POVM (Register I n) (Register K n)
  | 0 =>
      { effect := fun _ => 1
        positive := fun _ => Matrix.PosSemidef.one
        normalized := by simp [Register] }
  | n + 1 =>
      { effect := fun o => M.effect o.1 ⊗ₖ (tensorPOVM M n).effect o.2
        positive := fun o => (M.positive o.1).kronecker ((tensorPOVM M n).positive o.2)
        normalized := by
          have hs : (∑ o : K × Register K n,
              M.effect o.1 ⊗ₖ (tensorPOVM M n).effect o.2) =
              (∑ k, M.effect k) ⊗ₖ (∑ o, (tensorPOVM M n).effect o) := by
            ext x y
            simp [Fintype.sum_prod_type, Matrix.sum_apply, Matrix.kroneckerMap_apply,
              Finset.mul_sum, Finset.sum_mul]
            exact Finset.sum_comm
          rw [hs, M.normalized, (tensorPOVM M n).normalized, Matrix.one_kronecker_one] }

def relabelInputPOVM (M : POVM I K) (e : O ≃ I) : POVM O K where
  effect o := (M.effect o).submatrix e e
  positive o := (M.positive o).submatrix e
  normalized := by
    have hs : (∑ o, (M.effect o).submatrix e e) = (∑ o, M.effect o).submatrix e e := by
      ext x y
      simp only [Matrix.sum_apply, Matrix.submatrix_apply]
    rw [hs, M.normalized, Matrix.submatrix_one_equiv]

omit [DecidableEq K] in
theorem relabelInputPOVM_probability (M : POVM I K) (e : O ≃ I)
    (X : Matrix I I ℂ) (o : K) :
    measurementProbability (relabelInputPOVM M e) (X.submatrix e e) o =
      measurementProbability M X o := by
  unfold measurementProbability relabelInputPOVM
  rw [Matrix.submatrix_mul_equiv, trace_submatrix_equiv]

omit [DecidableEq K] in
theorem tensorPOVM_probability (M : POVM I K) (ρ : Density I)
    (σ : Density (Register I n)) (o : K × Register K n) :
    measurementProbability (tensorPOVM M (n + 1)) (ρ.tensor σ).mat o =
      measurementProbability M ρ.mat o.1 * measurementProbability (tensorPOVM M n) σ.mat o.2 := by
  unfold measurementProbability
  change ((ρ.mat ⊗ₖ σ.mat) * (M.effect o.1 ⊗ₖ (tensorPOVM M n).effect o.2)).trace.re = _
  rw [← Matrix.mul_kronecker_mul, Matrix.trace_kronecker]
  rw [← trace_mul_eq_real ρ.positive.1 (M.positive o.1).1,
    ← trace_mul_eq_real σ.positive.1 ((tensorPOVM M n).positive o.2).1]
  simp

end TensorPOVM

section ProductPrivacyPOVM

open QuantumProver.MeasuredRelativeEntropyVariational IndependentLanes

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] {d : ℕ}

def passCount : (n : ℕ) → Register (Fin 2) n → ℕ
  | 0, _ => 0
  | n + 1, o => (if o.1 = 0 then 1 else 0) + passCount n o.2

def privacyLanePOVM
    (U : Fin d → EuclideanSpace ℂ (A × B) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (A × B))
    (hd : 0 < d) (n : ℕ) : POVM
      (Register (Fin d × A) n × Register (Fin d × B) n) (Register (Fin 2) n) :=
  relabelInputPOVM (tensorPOVM (privacyPOVM U hd) n)
    (pairEquiv (Fin d × A) (Fin d × B) n).symm

def privacyLaneDensity (ρ : Density ((Fin d × A) × (Fin d × B))) (n : ℕ) :
    Density (Register (Fin d × A) n × Register (Fin d × B) n) :=
  (IndependentLanes.density ρ n).relabel (pairEquiv (Fin d × A) (Fin d × B) n).symm

theorem privacy_tensor_mean
    (U : Fin d → EuclideanSpace ℂ (A × B) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (A × B))
    (hd : 0 < d) (ρ : Density ((Fin d × A) × (Fin d × B))) (n : ℕ) :
    ∑ o : Register (Fin 2) n,
      measurementProbability (tensorPOVM (privacyPOVM U hd) n)
        (IndependentLanes.density ρ n).mat o * (passCount n o : ℝ) =
      (n : ℝ) * privacyAcceptance U ρ.mat := by
  induction n with
  | zero => simp [passCount, Register]
  | succ n ih =>
      change (∑ o : Fin 2 × Register (Fin 2) n,
        measurementProbability (tensorPOVM (privacyPOVM U hd) (n + 1))
          (ρ.tensor (IndependentLanes.density ρ n)).mat o *
          ((if o.1 = 0 then 1 else 0) + passCount n o.2 : ℕ)) = _
      rw [Fintype.sum_prod_type]
      have hprod (b : Fin 2) (o : Register (Fin 2) n) :
          measurementProbability (tensorPOVM (privacyPOVM U hd) (n + 1))
            (ρ.tensor (IndependentLanes.density ρ n)).mat (b, o) =
          measurementProbability (privacyPOVM U hd) ρ.mat b *
            measurementProbability (tensorPOVM (privacyPOVM U hd) n)
              (IndependentLanes.density ρ n).mat o :=
        tensorPOVM_probability (n := n) (privacyPOVM U hd) ρ (IndependentLanes.density ρ n) (b, o)
      simp only [hprod, Nat.cast_add, mul_add,
        Finset.sum_add_distrib]
      have hsum := measurementProbability_sum_density
        (tensorPOVM (privacyPOVM U hd) n)
        ⟨(IndependentLanes.density ρ n).positive, (IndependentLanes.density ρ n).normalized⟩
      have hsingle : ∑ b : Fin 2, measurementProbability (privacyPOVM U hd) ρ.mat b *
          ((if b = 0 then 1 else 0 : ℕ) : ℝ) = privacyAcceptance U ρ.mat := by
        rw [privacyPOVM_probability]
        simp [binaryWeights]
      have hsumHead := measurementProbability_sum_density (privacyPOVM U hd)
        ⟨ρ.positive, ρ.normalized⟩
      have htail0 (b : Fin 2) :
          (∑ o : Register (Fin 2) n,
            (measurementProbability (privacyPOVM U hd) ρ.mat b *
              measurementProbability (tensorPOVM (privacyPOVM U hd) n)
                (IndependentLanes.density ρ n).mat o) *
              ((if b = 0 then 1 else 0 : ℕ) : ℝ)) =
          measurementProbability (privacyPOVM U hd) ρ.mat b *
            ((if b = 0 then 1 else 0 : ℕ) : ℝ) := by
        calc
          _ = (measurementProbability (privacyPOVM U hd) ρ.mat b *
              ((if b = 0 then 1 else 0 : ℕ) : ℝ)) *
              (∑ o : Register (Fin 2) n,
                measurementProbability (tensorPOVM (privacyPOVM U hd) n)
                  (IndependentLanes.density ρ n).mat o) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro o _
            ring
          _ = _ := by rw [hsum, mul_one]
      have htail1 (b : Fin 2) :
          (∑ o : Register (Fin 2) n,
            (measurementProbability (privacyPOVM U hd) ρ.mat b *
              measurementProbability (tensorPOVM (privacyPOVM U hd) n)
                (IndependentLanes.density ρ n).mat o) * (passCount n o : ℝ)) =
          measurementProbability (privacyPOVM U hd) ρ.mat b *
            ((n : ℝ) * privacyAcceptance U ρ.mat) := by
        rw [← ih, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro o _
        ring
      simp only [htail0, htail1]
      rw [hsingle, ← Finset.sum_mul, hsumHead]
      push_cast
      ring

theorem privacy_binary_weighted (U : Fin d → EuclideanSpace ℂ (A × B) ≃ₗᵢ[ℂ]
    EuclideanSpace ℂ (A × B)) (r : ℝ) :
    (∑ b : Fin 2, ((r ^ (if b = 0 then 1 else 0 : ℕ) : ℝ) : ℂ) • privacyBinaryEffect U b) =
      1 + ((r - 1 : ℝ) : ℂ) • privacyEffect U := by
  simp only [Fin.sum_univ_two, privacyBinaryEffect]
  norm_num
  ext x y
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  simp only [Complex.real_smul]
  ring

theorem privacy_tensor_weighted
    (U : Fin d → EuclideanSpace ℂ (A × B) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (A × B))
    (hd : 0 < d) (n : ℕ) (r : ℝ) :
    (∑ o : Register (Fin 2) n,
      ((r ^ passCount n o : ℝ) : ℂ) • (tensorPOVM (privacyPOVM U hd) n).effect o) =
      IndependentLanes.matrix (1 + ((r - 1 : ℝ) : ℂ) • privacyEffect U) n := by
  induction n with
  | zero => simp [passCount, tensorPOVM, IndependentLanes.matrix, Register]
  | succ n ih =>
      have hs : (∑ o : Fin 2 × Register (Fin 2) n,
          ((r ^ ((if o.1 = 0 then 1 else 0 : ℕ) + passCount n o.2) : ℝ) : ℂ) •
            ((privacyPOVM U hd).effect o.1 ⊗ₖ (tensorPOVM (privacyPOVM U hd) n).effect o.2)) =
          (∑ b : Fin 2, ((r ^ (if b = 0 then 1 else 0 : ℕ) : ℝ) : ℂ) •
            (privacyPOVM U hd).effect b) ⊗ₖ
          (∑ o : Register (Fin 2) n, ((r ^ passCount n o : ℝ) : ℂ) •
            (tensorPOVM (privacyPOVM U hd) n).effect o) := by
        ext x y
        simp only [Fintype.sum_prod_type, Matrix.sum_apply, Matrix.smul_apply,
          Matrix.kroneckerMap_apply, pow_add, Complex.ofReal_mul, smul_eq_mul]
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro b _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro o _
        ring
      change (∑ o : Fin 2 × Register (Fin 2) n,
        ((r ^ ((if o.1 = 0 then 1 else 0 : ℕ) + passCount n o.2) : ℝ) : ℂ) •
          ((privacyPOVM U hd).effect o.1 ⊗ₖ (tensorPOVM (privacyPOVM U hd) n).effect o.2)) = _
      rw [hs, ih]
      change (∑ b : Fin 2, _ • privacyBinaryEffect U b) ⊗ₖ _ = _
      rw [privacy_binary_weighted]
      rfl

theorem privacy_lane_mean
    (U : Fin d → EuclideanSpace ℂ (A × B) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (A × B))
    (hd : 0 < d) (ρ : Density ((Fin d × A) × (Fin d × B))) (n : ℕ) :
    ∑ o : Register (Fin 2) n,
      measurementProbability (privacyLanePOVM U hd n) (privacyLaneDensity ρ n).mat o *
        (passCount n o : ℝ) = (n : ℝ) * privacyAcceptance U ρ.mat := by
  simp only [privacyLanePOVM, privacyLaneDensity, Density.relabel,
    relabelInputPOVM_probability]
  exact privacy_tensor_mean U hd ρ n

end ProductPrivacyPOVM

section AffineSupremum

theorem affine_csSup_le_ereal {S : Set ℝ} (hS : S.Nonempty) {a b : ℝ}
    (ha : 0 ≤ a) {R : EReal} (h : ∀ x ∈ S, ((a * x + b : ℝ) : EReal) ≤ R) :
    ((a * sSup S + b : ℝ) : EReal) ≤ R := by
  by_cases ha0 : a = 0
  · obtain ⟨x, hx⟩ := hS
    simpa only [ha0, zero_mul, zero_add] using h x hx
  have haPos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
  by_contra hn
  obtain ⟨r, hRr, hrSup⟩ := EReal.exists_between_coe_real (lt_of_not_ge hn)
  have hrSup' : r < a * sSup S + b := EReal.coe_lt_coe_iff.mp hrSup
  have hlevel : (r - b) / a < sSup S := (div_lt_iff₀ haPos).mpr (by nlinarith)
  obtain ⟨x, hx, hxl⟩ := exists_lt_of_lt_csSup hS hlevel
  have hrx : r < a * x + b := by
    have hh := (div_lt_iff₀ haPos).mp hxl
    nlinarith
  exact not_lt_of_ge (h x hx) (hRr.trans (EReal.coe_lt_coe_iff.mpr hrx))

theorem scaled_weakTestLowerBound_le_ereal (d : ℕ) (x : ℝ) (N : ℕ)
    {R : EReal} (h : ∀ s : ℝ, 0 ≤ s → (((N : ℝ) * testObjective d x s : ℝ) : EReal) ≤ R) :
    (((N : ℝ) * weakTestLowerBound d x : ℝ) : EReal) ≤ R := by
  have hh : ∀ y ∈ weakTestValues d x, (((N : ℝ) * y + 0 : ℝ) : EReal) ≤ R := by
    rintro y ⟨s, hs, rfl⟩
    simpa only [add_zero] using h s hs
  simpa only [add_zero, weakTestLowerBound] using affine_csSup_le_ereal (weakTestValues_nonempty d x)
    (Nat.cast_nonneg N) hh

end AffineSupremum

section WholeEveEndpoint

open PhysicalProtocol PhysicalPurification MatrixTraceNorm

variable {p : ℝ} {a b af bf d : ℕ} {E : Type*} [Fintype E] [DecidableEq E]

theorem protocol_keyG_umegaki_weak_test
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (P : FiniteKeyProtocol p a b af bf)
    (labelA : Fin af → Fin d) (labelB : Fin bf → Fin d)
    (C : Matrix (Fin a × Fin b) E ℂ) (hC : (Cᴴ * C).trace = 1) (hd : 0 < d) :
    (weakTestLowerBound d (optimalWholeKeySquaredFidelity d hd
      (P.finalKeyStateWithPriorEveLabels hp0 hp1 labelA labelB E (density C hC))) : EReal) ≤
      normalizedSEPUmegaki (honestMarginal
        ((P.retainedProtocolPrivateLiftChannel (E := E) hp0 hp1 labelA labelB).onDensity
          (density C hC))) := by
  let keyState := P.finalKeyStateWithPriorEveLabels hp0 hp1 labelA labelB E (density C hC)
  let rhoHat := honestMarginal
    ((P.retainedProtocolPrivateLiftChannel (E := E) hp0 hp1 labelA labelB).onDensity (density C hC))
  let S : Set ℝ := Set.range fun xi : Density (P.Environment × E) =>
    squaredFidelity keyState (idealKeyStateAgainst d hd xi)
  apply le_sInf
  rintro x ⟨σ, hσ, rfl⟩
  apply weakTestLowerBound_le_ereal hd (optimalWholeKeySquaredFidelity_mem_Icc d hd keyState).2
  intro s hs
  have hEach : ∀ y ∈ S,
      ((s * y - log2 (testMoment d s) : ℝ) : EReal) ≤ umegakiBits rhoHat.mat σ.mat := by
    rintro y ⟨xi, rfl⟩
    obtain ⟨U, hU⟩ := P.exists_private_test_of_protocol_candidate_channel
      hp0 hp1 labelA labelB C hC hd xi
    have hTest := privacy_umegaki_testObjective U hd rhoHat σ hσ hs
    have hmono : testObjective d (squaredFidelity keyState (idealKeyStateAgainst d hd xi)) s ≤
        testObjective d (privacyAcceptance U rhoHat.mat) s := by
      unfold testObjective
      exact sub_le_sub_right (mul_le_mul_of_nonneg_left hU hs) _
    exact (EReal.coe_le_coe_iff.mpr hmono).trans hTest
  change ((s * sSup S + (-log2 (testMoment d s)) : ℝ) : EReal) ≤ _
  apply affine_csSup_le_ereal
  · exact ⟨_, ⟨keyState.marginalRight, rfl⟩⟩
  · exact hs
  · intro y hy
    simpa only [sub_eq_add_neg] using hEach y hy

end WholeEveEndpoint

section ExtensivePrivacy

open QuantumProver.MeasuredRelativeEntropyVariational IndependentLanes

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] {d : ℕ}

theorem privacy_lane_moment
    (U : Fin d → EuclideanSpace ℂ (A × B) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (A × B))
    (hd : 0 < d) (N : ℕ) (r : ℝ)
    (σ : Density (Register (Fin d × A) N × Register (Fin d × B) N)) :
    (∑ o : Register (Fin 2) N,
      measurementProbability (privacyLanePOVM U hd N) σ.mat o * r ^ passCount N o) =
      (σ.mat * (IndependentLanes.matrix
        (1 + ((r - 1 : ℝ) : ℂ) • privacyEffect U) N).submatrix
          (pairEquiv (Fin d × A) (Fin d × B) N).symm
          (pairEquiv (Fin d × A) (Fin d × B) N).symm).trace.re := by
  have hw : (∑ o : Register (Fin 2) N, ((r ^ passCount N o : ℝ) : ℂ) •
      (privacyLanePOVM U hd N).effect o) =
      (IndependentLanes.matrix (1 + ((r - 1 : ℝ) : ℂ) • privacyEffect U) N).submatrix
        (pairEquiv (Fin d × A) (Fin d × B) N).symm
        (pairEquiv (Fin d × A) (Fin d × B) N).symm := by
    rw [← privacy_tensor_weighted U hd N r]
    ext x y
    simp only [privacyLanePOVM, relabelInputPOVM, Matrix.sum_apply,
      Matrix.submatrix_apply, Matrix.smul_apply]
  have h := trace_weighted_effects (privacyLanePOVM U hd N) σ.mat
    (fun o => r ^ passCount N o)
  rw [hw] at h
  exact h.symm

theorem exp_passCount (N : ℕ) (o : Register (Fin 2) N) (s : ℝ) :
    Real.exp (s * (passCount N o : ℝ) * Real.log 2) = ((2 : ℝ) ^ s) ^ passCount N o := by
  calc
    _ = Real.exp ((passCount N o : ℝ) * (s * Real.log 2)) := by congr 1; ring
    _ = Real.exp (s * Real.log 2) ^ passCount N o := Real.exp_nat_mul _ _
    _ = _ := by
      rw [Real.rpow_def_of_pos (by norm_num : 0 < (2 : ℝ))]
      congr 2
      ring

theorem privacy_lane_umegaki_testObjective
    (U : Fin d → EuclideanSpace ℂ (A × B) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (A × B))
    (hd : 0 < d) (ρ : Density ((Fin d × A) × (Fin d × B))) (N : ℕ)
    (σ : Density (Register (Fin d × A) N × Register (Fin d × B) N))
    (hσ : IsSeparable σ) {s : ℝ} (hs : 0 ≤ s) :
    (((N : ℝ) * testObjective d (privacyAcceptance U ρ.mat) s : ℝ) : EReal) ≤
      umegakiBits (privacyLaneDensity ρ N).mat σ.mat := by
  let M := privacyLanePOVM U hd N
  let p := measurementProbability M (privacyLaneDensity ρ N).mat
  let q := measurementProbability M σ.mat
  let f : Register (Fin 2) N → ℝ := fun o => s * (passCount N o : ℝ) * Real.log 2
  let Z : ℝ := ∑ o : Register (Fin 2) N, q o * Real.exp (f o)
  have hq : ∀ o, 0 ≤ q o := measurementProbability_nonneg M σ.positive
  have hqsum : ∑ o, q o = 1 := measurementProbability_sum_density M ⟨σ.positive, σ.normalized⟩
  have hZpos : 0 < Z := by
    have he : ∀ o, 1 ≤ Real.exp (f o) := by
      intro o
      apply Real.one_le_exp_iff.mpr
      exact mul_nonneg (mul_nonneg hs (Nat.cast_nonneg _))
        (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
    have hz : 1 ≤ Z := by
      rw [← hqsum]
      exact Finset.sum_le_sum (fun o _ => by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left (he o) (hq o))
    exact zero_lt_one.trans_le hz
  have hMean : ∑ o : Register (Fin 2) N, p o * f o =
      ((N : ℝ) * privacyAcceptance U ρ.mat) * (s * Real.log 2) := by
    calc
      _ = (∑ o : Register (Fin 2) N, p o * (passCount N o : ℝ)) * (s * Real.log 2) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro o _
        dsimp [f]
        ring
      _ = _ := by rw [privacy_lane_mean U hd ρ N]
  have hMoment : Z ≤ testMoment d s ^ N := by
    have ht : 0 ≤ (2 : ℝ) ^ s - 1 := sub_nonneg.mpr (Real.one_le_rpow (by norm_num) hs)
    have hBound := ProductPrivacyTest.privacy_mgf_separable_le_complex
      U N ((2 : ℝ) ^ s - 1) ht σ hσ
    have hZeq : Z = (σ.mat * (IndependentLanes.matrix
        (1 + (((2 : ℝ) ^ s - 1 : ℝ) : ℂ) • privacyEffect U) N).submatrix
          (pairEquiv (Fin d × A) (Fin d × B) N).symm
          (pairEquiv (Fin d × A) (Fin d × B) N).symm).trace.re := by
      dsimp [Z, q, M, f]
      simp only [exp_passCount]
      exact privacy_lane_moment U hd N ((2 : ℝ) ^ s) σ
    rw [hZeq]
    rw [Matrix.trace_mul_comm]
    exact hBound
  have hKL := povm_umegaki_exponential_test M (privacyLaneDensity ρ N) σ f
  rw [hMean] at hKL
  change (((((N : ℝ) * privacyAcceptance U ρ.mat) * (s * Real.log 2) - Real.log Z) /
    Real.log 2 : ℝ) : EReal) ≤ _ at hKL
  have hAlg : (((N : ℝ) * privacyAcceptance U ρ.mat) * (s * Real.log 2) - Real.log Z) /
      Real.log 2 = (N : ℝ) * s * privacyAcceptance U ρ.mat - log2 Z := by
    unfold log2
    field_simp [(Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne']
  rw [hAlg] at hKL
  have hLog : log2 Z ≤ (N : ℝ) * log2 (testMoment d s) := by
    have hh := Real.log_le_log hZpos hMoment
    rw [Real.log_pow] at hh
    simpa only [log2, mul_div_assoc] using
      div_le_div_of_nonneg_right hh (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
  have hLower : (N : ℝ) * testObjective d (privacyAcceptance U ρ.mat) s ≤
      (N : ℝ) * s * privacyAcceptance U ρ.mat - log2 Z := by
    unfold testObjective
    nlinarith
  exact (EReal.coe_le_coe_iff.mpr hLower).trans hKL

theorem privacy_normalizedSEP_extensive_weak_test
    (U : Fin d → EuclideanSpace ℂ (A × B) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (A × B))
    (hd : 0 < d) (ρ : Density ((Fin d × A) × (Fin d × B))) (N : ℕ) :
    (((N : ℝ) * weakTestLowerBound d (privacyAcceptance U ρ.mat) : ℝ) : EReal) ≤
      normalizedSEPUmegaki (privacyLaneDensity ρ N) := by
  apply le_sInf
  rintro x ⟨σ, hσ, rfl⟩
  exact scaled_weakTestLowerBound_le_ereal d _ N
    (fun _ hs => privacy_lane_umegaki_testObjective U hd ρ N σ hσ hs)

end ExtensivePrivacy

section WholeEveExtensive

open PhysicalProtocol PhysicalPurification MatrixTraceNorm IndependentLanes

variable {p : ℝ} {a b af bf d : ℕ} {E : Type*} [Fintype E] [DecidableEq E]

set_option backward.isDefEq.respectTransparency false in

theorem protocol_keyG_extensive_umegaki_weak_test
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (P : FiniteKeyProtocol p a b af bf)
    (labelA : Fin af → Fin d) (labelB : Fin bf → Fin d)
    (C : Matrix (Fin a × Fin b) E ℂ) (hC : (Cᴴ * C).trace = 1) (hd : 0 < d) (N : ℕ) :
    (((N : ℝ) * weakTestLowerBound d (optimalWholeKeySquaredFidelity d hd
      (P.finalKeyStateWithPriorEveLabels hp0 hp1 labelA labelB E (density C hC))) : ℝ) : EReal) ≤
      normalizedSEPUmegaki (privacyLaneDensity (honestMarginal
        ((P.retainedProtocolPrivateLiftChannel (E := E) hp0 hp1 labelA labelB).onDensity
          (density C hC))) N) := by
  letI : DecidableEq (Register (Fin d ×
      ((P.comparisonPublicHistory_B × Fin af) ⊕ (P.Environment × E))) N) :=
    registerDecidableEq _ N
  letI : DecidableEq (Register (Fin d × (P.comparisonPublicHistory_B × Fin bf)) N) :=
    registerDecidableEq _ N
  let keyState := P.finalKeyStateWithPriorEveLabels hp0 hp1 labelA labelB E (density C hC)
  let rhoHat := honestMarginal
    ((P.retainedProtocolPrivateLiftChannel (E := E) hp0 hp1 labelA labelB).onDensity (density C hC))
  let S : Set ℝ := Set.range fun xi : Density (P.Environment × E) =>
    squaredFidelity keyState (idealKeyStateAgainst d hd xi)
  apply le_sInf
  rintro x ⟨σ, hσ, rfl⟩
  apply scaled_weakTestLowerBound_le_ereal
  intro s hs
  change (((N : ℝ) * testObjective d
    (optimalWholeKeySquaredFidelity d hd keyState) s : ℝ) : EReal) ≤
      umegakiBits (privacyLaneDensity rhoHat N).mat σ.mat
  have hEach : ∀ y ∈ S,
      (((N : ℝ) * s * y + (-(N : ℝ) * log2 (testMoment d s)) : ℝ) : EReal) ≤
        umegakiBits (privacyLaneDensity rhoHat N).mat σ.mat := by
    rintro y ⟨xi, rfl⟩
    obtain ⟨U, hU⟩ := P.exists_private_test_of_protocol_candidate_channel
      hp0 hp1 labelA labelB C hC hd xi
    have hTest := privacy_lane_umegaki_testObjective U hd rhoHat N σ hσ hs
    have hmono : (N : ℝ) * testObjective d
        (squaredFidelity keyState (idealKeyStateAgainst d hd xi)) s ≤
        (N : ℝ) * testObjective d (privacyAcceptance U rhoHat.mat) s := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg N)
      unfold testObjective
      exact sub_le_sub_right (mul_le_mul_of_nonneg_left hU hs) _
    have hh := (EReal.coe_le_coe_iff.mpr hmono).trans hTest
    have hScalar : (N : ℝ) * s * squaredFidelity keyState (idealKeyStateAgainst d hd xi) +
        (-(N : ℝ) * log2 (testMoment d s)) =
        (N : ℝ) * testObjective d (squaredFidelity keyState (idealKeyStateAgainst d hd xi)) s := by
      unfold testObjective
      ring
    rw [hScalar]
    exact hh
  have hObj : (N : ℝ) * testObjective d (optimalWholeKeySquaredFidelity d hd keyState) s =
      (N : ℝ) * s * sSup S + (-(N : ℝ) * log2 (testMoment d s)) := by
    unfold testObjective optimalWholeKeySquaredFidelity
    change (N : ℝ) * (s * sSup S - log2 (testMoment d s)) = _
    ring
  rw [hObj]
  apply affine_csSup_le_ereal (S := S)
  · exact ⟨_, ⟨keyState.marginalRight, rfl⟩⟩
  · exact mul_nonneg (Nat.cast_nonneg N) hs
  · exact hEach

end WholeEveExtensive

theorem weakTestLowerBound_binary_entropy {d : ℕ} (hd : 2 ≤ d) {x : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    x * log2 (d : ℝ) - binaryEntropyBits x ≤ weakTestLowerBound d x := by
  simpa only [weakTestLowerBound, weakTestValues, testObjective, testMoment] using
    WeakBinaryConjugate.weak_binary_entropy_bound hd hx0 hx1

section BinaryEntropyEndpoint

open PhysicalProtocol PhysicalPurification MatrixTraceNorm

variable {p : ℝ} {a b af bf d : ℕ} {E : Type*} [Fintype E] [DecidableEq E]

theorem protocol_keyG_extensive_umegaki_binary_entropy
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (P : FiniteKeyProtocol p a b af bf)
    (labelA : Fin af → Fin d) (labelB : Fin bf → Fin d)
    (C : Matrix (Fin a × Fin b) E ℂ) (hC : (Cᴴ * C).trace = 1) (hd : 0 < d)
    (hd2 : 2 ≤ d) (N : ℕ) :
    ((((N : ℝ) * (optimalWholeKeySquaredFidelity d hd
      (P.finalKeyStateWithPriorEveLabels hp0 hp1 labelA labelB E (density C hC)) *
      log2 (d : ℝ) - binaryEntropyBits (optimalWholeKeySquaredFidelity d hd
        (P.finalKeyStateWithPriorEveLabels hp0 hp1 labelA labelB E (density C hC)))) : ℝ) : EReal)) ≤
      normalizedSEPUmegaki (privacyLaneDensity (honestMarginal
        ((P.retainedProtocolPrivateLiftChannel (E := E) hp0 hp1 labelA labelB).onDensity
          (density C hC))) N) := by
  have hG := optimalWholeKeySquaredFidelity_mem_Icc d hd
    (P.finalKeyStateWithPriorEveLabels hp0 hp1 labelA labelB E (density C hC))
  have hL := mul_le_mul_of_nonneg_left (weakTestLowerBound_binary_entropy hd2 hG.1 hG.2)
    (Nat.cast_nonneg N)
  exact (EReal.coe_le_coe_iff.mpr hL).trans
    (protocol_keyG_extensive_umegaki_weak_test hp0 hp1 P labelA labelB C hC hd N)

end BinaryEntropyEndpoint
end QuantumProver.AmplitudeDamping.SecretKey.WeakPrivateTestResource

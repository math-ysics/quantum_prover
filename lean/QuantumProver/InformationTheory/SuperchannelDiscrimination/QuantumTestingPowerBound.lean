import Mathlib
import QuantumProver.InformationTheory.SuperchannelDiscrimination.PetzTensorTail
import QuantumProver.InformationTheory.SuperchannelDiscrimination.EffectPerturbation
import QuantumProver.InformationTheory.SuperchannelDiscrimination.CPTPKraus

set_option autoImplicit false

noncomputable section
open Matrix
open scoped BigOperators Topology ComplexOrder MatrixOrder Matrix.Norms.L2Operator Matrix

namespace QuantumProver.SuperchannelDiscrimination.QuantumTestingPowerBound

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem trace_mul_mono_right {X A B : Matrix I I ℂ}
    (hX : X.PosSemidef) (hAB : A ≤ B) :
    (X * A).trace.re ≤ (X * B).trace.re := by
  have hn := FlaggedStates.trace_mul_re_nonneg hX (Matrix.le_iff.mp hAB)
  simp only [mul_sub, Matrix.trace_sub, Complex.sub_re] at hn
  exact sub_nonneg.mp hn

theorem trace_mul_mono_left {X A B : Matrix I I ℂ}
    (hX : X.PosSemidef) (hAB : A ≤ B) :
    (A * X).trace.re ≤ (B * X).trace.re := by
  rw [Matrix.trace_mul_comm A X, Matrix.trace_mul_comm B X]
  exact trace_mul_mono_right hX hAB

theorem rpow_mul_complement {A : Matrix I I ℂ} (hA : A.PosSemidef) (s : ℝ) :
    A ^ (1 - s) * A ^ s = A := by
  rw [CFC.rpow_eq_cfc_real hA.nonneg, CFC.rpow_eq_cfc_real hA.nonneg,
    ← cfc_mul (p := IsSelfAdjoint) (fun x : ℝ => x ^ (1 - s))
      (fun x : ℝ => x ^ s) A (A.finite_real_spectrum.continuousOn _)
      (A.finite_real_spectrum.continuousOn _)]
  calc
    cfc (fun x : ℝ => x ^ (1 - s) * x ^ s) A = cfc (fun x : ℝ => x) A := by
      apply cfc_congr
      intro x hx
      rw [hA.1.spectrum_real_eq_range_eigenvalues] at hx
      obtain ⟨i, rfl⟩ := hx
      change (hA.1.eigenvalues i) ^ (1 - s) * (hA.1.eigenvalues i) ^ s =
        hA.1.eigenvalues i
      simpa only [sub_add_cancel, Real.rpow_one] using
        (Real.rpow_add' (hA.eigenvalues_nonneg i) (by ring_nf; norm_num :
          (1 - s) + s ≠ 0)).symm
    _ = A := cfc_id' ℝ A hA.1.isSelfAdjoint

def commonUpper (A B : Matrix I I ℂ) : Matrix I I ℂ := B + (A - B)⁺

theorem le_commonUpper_right (A B : Matrix I I ℂ) : B ≤ commonUpper A B := by
  exact le_add_of_nonneg_right (CFC.posPart_nonneg (A - B))

theorem le_commonUpper_left {A B : Matrix I I ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) : A ≤ commonUpper A B := by
  have hp := CFC.le_posPart (hA.sub hB).isSelfAdjoint
  calc
    A = (A - B) + B := (sub_add_cancel A B).symm
    _ ≤ (A - B)⁺ + B := add_le_add hp (le_refl B)
    _ = commonUpper A B := add_comm _ _

theorem commonUpper_posSemidef {A B : Matrix I I ℂ} (hB : B.PosSemidef) :
    (commonUpper A B).PosSemidef :=
  hB.add (CFC.posPart_nonneg (A - B)).posSemidef

theorem audenaert_trace_power {A B : Matrix I I ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) (s : ℝ)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    A.trace.re - (A - B)⁺.trace.re ≤ (A ^ (1 - s) * B ^ s).trace.re := by
  let C := commonUpper A B
  have hC : C.PosSemidef := commonUpper_posSemidef hB
  have hAC : A ≤ C := le_commonUpper_left hA.1 hB.1
  have hBC : B ≤ C := le_commonUpper_right A B
  have hpAC : A ^ s ≤ C ^ s := CFC.rpow_le_rpow ⟨hs0, hs1⟩ hAC
  have hpBC : B ^ s ≤ C ^ s := CFC.rpow_le_rpow ⟨hs0, hs1⟩ hBC
  have hqAC : A ^ (1 - s) ≤ C ^ (1 - s) :=
    CFC.rpow_le_rpow ⟨by linarith, by linarith⟩ hAC
  have hqBC : B ^ (1 - s) ≤ C ^ (1 - s) :=
    CFC.rpow_le_rpow ⟨by linarith, by linarith⟩ hBC
  have h1 := trace_mul_mono_right (CFC.rpow_nonneg (a := A) (y := 1 - s)).posSemidef hpAC
  have h2 := trace_mul_mono_left (Matrix.le_iff.mp hpBC) hqAC
  have h3 := trace_mul_mono_left (CFC.rpow_nonneg (a := B) (y := s)).posSemidef hqBC
  rw [rpow_mul_complement hA s] at h1
  simp only [mul_sub, Matrix.trace_sub, Complex.sub_re,
    rpow_mul_complement hC s] at h2
  rw [rpow_mul_complement hB s] at h3
  have hc : C.trace.re = B.trace.re + (A - B)⁺.trace.re := by
    simp only [C, commonUpper, Matrix.trace_add, Complex.add_re]
  linarith

theorem positiveSpectralTest_eq_positiveSupport (H : Matrix I I ℂ) :
    PetzTensorTail.positiveSpectralTest H = EffectPerturbation.positiveSupport H := rfl

theorem np_error_eq_trace_sub_posPart {A B : Matrix I I ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (A * (1 - PetzTensorTail.positiveSpectralTest (A - B))).trace.re +
      (B * PetzTensorTail.positiveSpectralTest (A - B)).trace.re =
      A.trace.re - (A - B)⁺.trace.re := by
  have hp := EffectPerturbation.positiveSupport_mul (hA.sub hB)
  rw [← positiveSpectralTest_eq_positiveSupport] at hp
  have htr : ((A - B) * PetzTensorTail.positiveSpectralTest (A - B)).trace =
      (A - B)⁺.trace :=
    (Matrix.trace_mul_comm _ _).trans (congrArg Matrix.trace hp)
  have ht := congrArg Complex.re htr
  simp only [sub_mul, Matrix.trace_sub, Complex.sub_re] at ht
  simp only [mul_sub, mul_one, Matrix.trace_sub, Complex.sub_re]
  linarith

theorem audenaert_testing_power_cfc {A B : Matrix I I ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) (t s : ℝ)
    (ht : 0 < t) (hs0 : 0 < s) (hs1 : s < 1) :
    (A * (1 - PetzTensorTail.spectralUpperTail A B t)).trace.re +
      t * (B * PetzTensorTail.spectralUpperTail A B t).trace.re ≤
      (cfc (fun x : ℝ => x ^ (1 - s)) A *
        cfc (fun x : ℝ => x ^ s) (t • B)).trace.re := by
  have hBt : (t • B).PosSemidef := hB.smul ht.le
  have h := audenaert_trace_power hA hBt s hs0.le hs1.le
  rw [CFC.rpow_eq_cfc_real hA.nonneg, CFC.rpow_eq_cfc_real hBt.nonneg] at h
  rw [← np_error_eq_trace_sub_posPart hA.1 hBt.1] at h
  simpa only [PetzTensorTail.spectralUpperTail, Matrix.smul_mul, Matrix.trace_smul,
    Complex.smul_re, smul_eq_mul] using h

theorem cfc_rpow_smul {B : Matrix I I ℂ} (hB : B.PosSemidef)
    (t s : ℝ) (ht : 0 < t) :
    cfc (fun x : ℝ => x ^ s) (t • B) =
      t ^ s • cfc (fun x : ℝ => x ^ s) B := by
  rw [← cfc_comp_smul (p := IsSelfAdjoint) t (fun x : ℝ => x ^ s) B
    ((B.finite_real_spectrum.image (fun x : ℝ => t • x)).continuousOn _) hB.1.isSelfAdjoint]
  calc
    cfc (fun x : ℝ => (t * x) ^ s) B = cfc (fun x : ℝ => t ^ s * x ^ s) B := by
      apply cfc_congr
      intro x hx
      rw [hB.1.spectrum_real_eq_range_eigenvalues] at hx
      obtain ⟨i, rfl⟩ := hx
      change (t * hB.1.eigenvalues i) ^ s = t ^ s * (hB.1.eigenvalues i) ^ s
      exact Real.mul_rpow ht.le (hB.eigenvalues_nonneg i)
    _ = t ^ s • cfc (fun x : ℝ => x ^ s) B :=
      cfc_smul (p := IsSelfAdjoint) (t ^ s) (fun x : ℝ => x ^ s) B
        (B.finite_real_spectrum.continuousOn _)

theorem audenaert_testing_power {A B : Matrix I I ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) (t s : ℝ)
    (ht : 0 < t) (hs0 : 0 < s) (hs1 : s < 1) :
    (A * (1 - PetzTensorTail.spectralUpperTail A B t)).trace.re +
      t * (B * PetzTensorTail.spectralUpperTail A B t).trace.re ≤
      t ^ s * PetzMoments.petzMoment A B (-s) := by
  have h := audenaert_testing_power_cfc hA hB t s ht hs0 hs1
  rw [cfc_rpow_smul hB t s ht, Matrix.mul_smul, Matrix.trace_smul] at h
  simpa only [PetzMoments.petzMoment, neg_neg, ← sub_eq_add_neg,
    Complex.smul_re, smul_eq_mul] using h

theorem np_typeI_le_petzMoment {A B : Matrix I I ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) (t s : ℝ)
    (ht : 0 < t) (hs0 : 0 < s) (hs1 : s < 1) :
    (A * (1 - PetzTensorTail.spectralUpperTail A B t)).trace.re ≤
      t ^ s * PetzMoments.petzMoment A B (-s) := by
  have hT := PetzTensorTail.positiveSpectralTest_isEffect (hA.1.sub (hB.smul ht.le).1)
  have hb := FlaggedStates.trace_mul_re_nonneg hB hT.1
  have h := audenaert_testing_power hA hB t s ht hs0 hs1
  have hb' := mul_nonneg ht.le hb
  change 0 ≤ t * (B * PetzTensorTail.spectralUpperTail A B t).trace.re at hb'
  linarith

end QuantumProver.SuperchannelDiscrimination.QuantumTestingPowerBound

namespace QuantumProver.SuperchannelDiscrimination.BinaryMeasurement

open scoped Kronecker

variable {I : Type*} [Fintype I] [DecidableEq I]

abbrev Outcome := Unit ⊕ Unit

def effectPart (T : Matrix I I ℂ) : Outcome → Matrix I I ℂ :=
  Sum.elim (fun _ => T) (fun _ => 1 - T)

def measurement (T : Matrix I I ℂ) : Matrix I I ℂ →ₗ[ℂ] Matrix Outcome Outcome ℂ where
  toFun X := Matrix.diagonal (fun b => (effectPart T b * X).trace)
  map_add' X Y := by
    simp only [Matrix.mul_add, Matrix.trace_add, Matrix.diagonal_add]
  map_smul' z X := by
    ext b c
    simp [Matrix.trace_smul, Matrix.diagonal, Matrix.smul_apply]

theorem measurement_apply (T : Matrix I I ℂ) (X : Matrix I I ℂ) :
    measurement T X = FlaggedStates.flagBlock
      ((T * X).trace • (1 : Matrix Unit Unit ℂ))
      (((1 - T) * X).trace • (1 : Matrix Unit Unit ℂ)) := by
  ext b c
  cases b <;> cases c <;> simp [measurement, effectPart, FlaggedStates.flagBlock,
    Matrix.diagonal, Matrix.fromBlocks]

theorem measurement_tracePreserving (T : Matrix I I ℂ) :
    CPTPKraus.TracePreserving (measurement T) := by
  intro X
  rw [measurement_apply, FlaggedStates.flagBlock_trace]
  simp only [Matrix.trace_smul, Matrix.trace_one, Fintype.card_unique,
    Nat.cast_one, smul_eq_mul, mul_one, sub_mul, one_mul, Matrix.trace_sub]
  abel

def rowKraus (b : Outcome) (S : Matrix I I ℂ) (i : I) : Matrix Outcome I ℂ :=
  fun a j => if a = b then S i j else 0

omit [DecidableEq I] in
theorem rowKraus_gram (b : Outcome) (S : Matrix I I ℂ) :
    (∑ i : I, (rowKraus b S i)ᴴ * rowKraus b S i) = Sᴴ * S := by
  ext j k
  simp [rowKraus, Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    mul_ite]

omit [DecidableEq I] in
theorem rowKraus_born (b : Outcome) (S X : Matrix I I ℂ) :
    (∑ i : I, rowKraus b S i * X * (rowKraus b S i)ᴴ) =
      (S * X * Sᴴ).trace • Matrix.single b b (1 : ℂ) := by
  ext a c
  by_cases ha : a = b <;> by_cases hc : c = b
  · subst a
    subst c
    simp [rowKraus, Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.trace, Matrix.diag, Finset.sum_mul, Matrix.smul_apply]
  · simp [rowKraus, ha, hc, Ne.symm hc, Matrix.sum_apply, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Matrix.smul_apply]
  · simp [rowKraus, ha, hc, Ne.symm ha, Matrix.sum_apply, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Matrix.smul_apply]
  · simp [rowKraus, ha, hc, Ne.symm ha, Ne.symm hc, Matrix.sum_apply, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Matrix.smul_apply]

def measurementKraus (T : Matrix I I ℂ) (q : Outcome × I) : Matrix Outcome I ℂ :=
  rowKraus q.1 (CFC.sqrt (effectPart T q.1)) q.2

omit [Fintype I] in
theorem effectPart_posSemidef {T : Matrix I I ℂ}
    (hT : FlaggedStates.IsEffect T) (b : Outcome) : (effectPart T b).PosSemidef := by
  cases b
  · exact hT.1
  · exact hT.2

theorem effectPart_sqrt_gram {T : Matrix I I ℂ}
    (hT : FlaggedStates.IsEffect T) (b : Outcome) :
    (CFC.sqrt (effectPart T b))ᴴ * CFC.sqrt (effectPart T b) = effectPart T b := by
  have hs : (CFC.sqrt (effectPart T b))ᴴ = CFC.sqrt (effectPart T b) :=
    (CFC.sqrt_nonneg _).posSemidef.1
  rw [hs, CFC.sqrt_mul_sqrt_self _ (effectPart_posSemidef hT b).nonneg]

theorem effectPart_sqrt_trace {T : Matrix I I ℂ}
    (hT : FlaggedStates.IsEffect T) (b : Outcome) (X : Matrix I I ℂ) :
    (CFC.sqrt (effectPart T b) * X * (CFC.sqrt (effectPart T b))ᴴ).trace =
      (effectPart T b * X).trace := by
  rw [Matrix.trace_mul_cycle, effectPart_sqrt_gram hT]

theorem measurementKraus_complete {T : Matrix I I ℂ}
    (hT : FlaggedStates.IsEffect T) :
    (∑ q : Outcome × I, (measurementKraus T q)ᴴ * measurementKraus T q) = 1 := by
  simp only [Fintype.sum_prod_type, measurementKraus, rowKraus_gram,
    effectPart_sqrt_gram hT]
  simp [effectPart, Fintype.sum_sum_type]

theorem measurement_eq_krausMap {T : Matrix I I ℂ}
    (hT : FlaggedStates.IsEffect T) : measurement T = QuantumProver.ElegantJointMeasurement.CP.krausMap (measurementKraus T) := by
  apply LinearMap.ext
  intro X
  change Matrix.diagonal (fun b => (effectPart T b * X).trace) =
    ∑ q : Outcome × I, measurementKraus T q * X * (measurementKraus T q)ᴴ
  rw [Fintype.sum_prod_type]
  simp only [measurementKraus, rowKraus_born, effectPart_sqrt_trace hT]
  ext a c
  cases a <;> cases c <;> simp [Matrix.diagonal]

theorem measurement_completelyPositive {T : Matrix I I ℂ}
    (hT : FlaggedStates.IsEffect T) : CPTPKraus.CompletelyPositive (measurement T) := by
  rw [measurement_eq_krausMap hT]
  exact (CPTPKraus.completelyPositive_iff_EJMCP _).mpr (QuantumProver.ElegantJointMeasurement.CP.krausMap_completelyPositive _)

theorem measurement_amplify_reconstruct {T : Matrix I I ℂ}
    (hT : FlaggedStates.IsEffect T) (R : Type*) [Fintype R] [DecidableEq R]
    (X : Matrix (I × R) (I × R) ℂ) :
    CPTPKraus.amplify (measurement T) R X = ∑ q : Outcome × I,
      (measurementKraus T q ⊗ₖ (1 : Matrix R R ℂ)) * X *
        (measurementKraus T q ⊗ₖ (1 : Matrix R R ℂ))ᴴ := by
  rw [measurement_eq_krausMap hT]
  exact CPTPKraus.amplify_krausMap_reconstruct _ _ _

theorem measurement_amplify_posSemidef {T : Matrix I I ℂ}
    (hT : FlaggedStates.IsEffect T) (R : Type*) [Fintype R] [DecidableEq R]
    {X : Matrix (I × R) (I × R) ℂ} (hX : X.PosSemidef) :
    (CPTPKraus.amplify (measurement T) R X).PosSemidef := by
  rw [measurement_amplify_reconstruct hT]
  exact (Finset.sum_nonneg fun q _ =>
    (hX.mul_mul_conjTranspose_same (measurementKraus T q ⊗ₖ (1 : Matrix R R ℂ))).nonneg).posSemidef

theorem measurement_amplify_tracePreserving {T : Matrix I I ℂ}
    (hT : FlaggedStates.IsEffect T) (R : Type*) [Fintype R] [DecidableEq R]
    (X : Matrix (I × R) (I × R) ℂ) :
    (CPTPKraus.amplify (measurement T) R X).trace = X.trace :=
  CPTPKraus.amplify_tracePreserving _ (measurement_completelyPositive hT)
    (measurement_tracePreserving T) R X

theorem measurement_amplify_apply (T : Matrix I I ℂ)
    (R : Type*) [Fintype R] [DecidableEq R]
    (X : Matrix (I × R) (I × R) ℂ) (b c : Outcome) (r s : R) :
    CPTPKraus.amplify (measurement T) R X (b, r) (c, s) =
      if b = c then (effectPart T b * Matrix.of (fun i j => X (i, r) (j, s))).trace else 0 := by
  rfl

def scalarMatrix (p : ℝ) : Matrix Unit Unit ℂ := algebraMap ℝ (Matrix Unit Unit ℂ) p

@[simp] theorem scalarMatrix_apply (p : ℝ) (a b : Unit) : scalarMatrix p a b = (p : ℂ) := by
  cases a
  cases b
  simp [scalarMatrix, Algebra.algebraMap_eq_smul_one, Matrix.smul_apply]

@[simp] theorem scalarMatrix_trace (p : ℝ) : (scalarMatrix p).trace = (p : ℂ) := by
  simp [Matrix.trace, Matrix.diag]

theorem scalarMatrix_isHermitian (p : ℝ) : (scalarMatrix p).IsHermitian := by
  rw [scalarMatrix, Algebra.algebraMap_eq_smul_one]
  exact Matrix.isHermitian_one.smul (by rfl : IsSelfAdjoint p)

theorem scalarMatrix_posSemidef {p : ℝ} (hp : 0 ≤ p) : (scalarMatrix p).PosSemidef := by
  simpa [scalarMatrix, Algebra.algebraMap_eq_smul_one] using
    (Matrix.PosSemidef.one : (1 : Matrix Unit Unit ℂ).PosSemidef).smul hp

@[simp] theorem scalarMatrix_cfc (f : ℝ → ℝ) (p : ℝ) :
    cfc f (scalarMatrix p) = scalarMatrix (f p) := cfc_algebraMap p f

theorem scalarMatrix_hasSupportIn (p q : ℝ) :
    FlaggedStates.HasSupportIn (scalarMatrix p) (scalarMatrix q) ↔ (q = 0 → p = 0) := by
  constructor
  · intro h hq
    have hv := h (fun _ => (1 : ℂ)) (by
      ext u
      simp [hq, Matrix.mulVec, dotProduct])
    have hp : (p : ℂ) = 0 := by
      simpa [Matrix.mulVec, dotProduct] using congrFun hv ()
    exact_mod_cast hp
  · intro h v hv
    by_cases hq : q = 0
    · have hp := h hq
      ext u
      simp [hp, Matrix.mulVec, dotProduct]
    · have hq' : (q : ℂ) ≠ 0 := by exact_mod_cast hq
      have hm : (q : ℂ) * v () = 0 := by
        simpa [Matrix.mulVec, dotProduct] using congrFun hv ()
      have hv0 : v = 0 := by
        ext u
        cases u
        exact (mul_eq_zero.mp hm).resolve_left hq'
      simp [hv0]

theorem scalarMatrix_finiteRelativeEntropyBits (p q : ℝ) :
    FlaggedStates.finiteRelativeEntropyBits (scalarMatrix p) (scalarMatrix q) =
      p * (Real.log p - Real.log q) / Real.log 2 := by
  have hsub : scalarMatrix (Real.log p) - scalarMatrix (Real.log q) =
      scalarMatrix (Real.log p - Real.log q) := (map_sub (algebraMap ℝ _) _ _).symm
  have hmul : scalarMatrix p * scalarMatrix (Real.log p - Real.log q) =
      scalarMatrix (p * (Real.log p - Real.log q)) := (map_mul (algebraMap ℝ _) _ _).symm
  simp only [FlaggedStates.finiteRelativeEntropyBits, scalarMatrix_cfc, hsub, hmul,
    scalarMatrix_trace, Complex.ofReal_re]

def binaryState (p : ℝ) : Matrix Outcome Outcome ℂ :=
  FlaggedStates.flagBlock (scalarMatrix p) (scalarMatrix (1 - p))

theorem binaryState_isDensity {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    FlaggedStates.IsDensity (binaryState p) := by
  apply FlaggedStates.flagBlock_isDensity (scalarMatrix_posSemidef hp0)
    (scalarMatrix_posSemidef (sub_nonneg.mpr hp1))
  simp

theorem binaryState_hasSupportIn (p q : ℝ) :
    FlaggedStates.HasSupportIn (binaryState p) (binaryState q) ↔
      (q = 0 → p = 0) ∧ (q = 1 → p = 1) := by
  rw [binaryState, binaryState, FlaggedStates.hasSupportIn_flagBlock_iff,
    scalarMatrix_hasSupportIn, scalarMatrix_hasSupportIn]
  constructor
  · rintro ⟨h0, h1⟩
    refine ⟨h0, fun hq => ?_⟩
    have hp := h1 (by simp [hq])
    linarith
  · rintro ⟨h0, h1⟩
    refine ⟨h0, fun hq => ?_⟩
    have hp := h1 (by linarith)
    linarith

theorem binaryState_finiteRelativeEntropyBits (p q : ℝ) (hq0 : q ≠ 0) (hq1 : q ≠ 1) :
    FlaggedStates.finiteRelativeEntropyBits (binaryState p) (binaryState q) =
      binaryRelativeEntropyBits p q := by
  rw [binaryState, binaryState,
    FlaggedStates.finiteRelativeEntropyBits_flagBlock_of_hermitian
      (scalarMatrix_isHermitian p) (scalarMatrix_isHermitian q)
      (scalarMatrix_isHermitian (1 - p)) (scalarMatrix_isHermitian (1 - q)),
    scalarMatrix_finiteRelativeEntropyBits, scalarMatrix_finiteRelativeEntropyBits,
    binaryRelativeEntropyBits, weighted_log_quotient p hq0,
    weighted_log_quotient (1 - p) (sub_ne_zero.mpr (Ne.symm hq1))]
  ring

theorem binaryState_relativeEntropyBits (p q : ℝ) :
    FlaggedStates.relativeEntropyBits (binaryState p) (binaryState q) =
      extendedBinaryRelativeEntropyBits p q := by
  by_cases hq0 : q = 0
  · subst q
    by_cases hp0 : p = 0
    · subst p
      simp [FlaggedStates.relativeEntropyBits, FlaggedStates.hasSupportIn_self,
        FlaggedStates.finiteRelativeEntropyBits, extendedBinaryRelativeEntropyBits]
    · have hsup : ¬ FlaggedStates.HasSupportIn (binaryState p) (binaryState 0) := by
        rw [binaryState_hasSupportIn]
        simp [hp0]
      simp [FlaggedStates.relativeEntropyBits, hsup, extendedBinaryRelativeEntropyBits, hp0]
  · by_cases hq1 : q = 1
    · subst q
      by_cases hp1 : p = 1
      · subst p
        simp [FlaggedStates.relativeEntropyBits, FlaggedStates.hasSupportIn_self,
          FlaggedStates.finiteRelativeEntropyBits, extendedBinaryRelativeEntropyBits]
      · have hsup : ¬ FlaggedStates.HasSupportIn (binaryState p) (binaryState 1) := by
          rw [binaryState_hasSupportIn]
          simp [hp1]
        simp [FlaggedStates.relativeEntropyBits, hsup, extendedBinaryRelativeEntropyBits, hp1]
    · have hsup : FlaggedStates.HasSupportIn (binaryState p) (binaryState q) :=
        (binaryState_hasSupportIn p q).mpr ⟨fun h => False.elim (hq0 h),
          fun h => False.elim (hq1 h)⟩
      simp only [FlaggedStates.relativeEntropyBits, ite_eq_left hsup,
        binaryState_finiteRelativeEntropyBits p q hq0 hq1]
      simp [extendedBinaryRelativeEntropyBits, hq0, hq1]

end QuantumProver.SuperchannelDiscrimination.BinaryMeasurement

namespace QuantumProver.SuperchannelDiscrimination.BinaryMeasurement

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem trace_mul_eq_ofReal {A B : Matrix I I ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (A * B).trace = ((A * B).trace.re : ℂ) := by
  simpa only [cfc_id' (p := IsSelfAdjoint) ℝ A hA,
    cfc_id' (p := IsSelfAdjoint) ℝ B hB] using
    PetzMoments.trace_cfc_mul_cfc_real (fun x : ℝ => x) (fun x : ℝ => x) A B

theorem measurement_accept_entry (T X : Matrix I I ℂ) :
    measurement T X (Sum.inl ()) (Sum.inl ()) = (X * T).trace := by
  change (T * X).trace = (X * T).trace
  exact Matrix.trace_mul_comm T X

theorem measurement_reject_entry (T X : Matrix I I ℂ) :
    measurement T X (Sum.inr ()) (Sum.inr ()) = (X * (1 - T)).trace := by
  change ((1 - T) * X).trace = (X * (1 - T)).trace
  exact Matrix.trace_mul_comm (1 - T) X

theorem measurement_amplify_isDensity {T : Matrix I I ℂ}
    (hT : FlaggedStates.IsEffect T) (R : Type*) [Fintype R] [DecidableEq R]
    {X : Matrix (I × R) (I × R) ℂ} (hX : FlaggedStates.IsDensity X) :
    FlaggedStates.IsDensity (CPTPKraus.amplify (measurement T) R X) :=
  ⟨measurement_amplify_posSemidef hT R hX.1,
    (measurement_amplify_tracePreserving hT R X).trans hX.2⟩

theorem measurement_density_eq_binaryState {ρ T : Matrix I I ℂ}
    (hρ : FlaggedStates.IsDensity ρ) (hT : FlaggedStates.IsEffect T) :
    measurement T ρ = binaryState (FlaggedStates.acceptanceProbability ρ T) := by
  have hp : (T * ρ).trace = (FlaggedStates.acceptanceProbability ρ T : ℂ) := by
    rw [Matrix.trace_mul_comm T ρ]
    exact trace_mul_eq_ofReal hρ.1.1 hT.1.1
  have hc : ((1 - T) * ρ).trace =
      ((1 - FlaggedStates.acceptanceProbability ρ T : ℝ) : ℂ) := by
    rw [sub_mul, one_mul, Matrix.trace_sub, hρ.2, hp]
    simp
  rw [measurement_apply, binaryState, hp, hc]
  ext b c
  cases b <;> cases c <;> simp [FlaggedStates.flagBlock,
    Matrix.fromBlocks, Matrix.smul_apply, smul_eq_mul]

theorem measurement_isDensity {ρ T : Matrix I I ℂ}
    (hρ : FlaggedStates.IsDensity ρ) (hT : FlaggedStates.IsEffect T) :
    FlaggedStates.IsDensity (measurement T ρ) := by
  rw [measurement_density_eq_binaryState hρ hT]
  exact binaryState_isDensity (FlaggedStates.acceptanceProbability_bounds hρ hT).1
    (FlaggedStates.acceptanceProbability_bounds hρ hT).2

theorem measurement_relativeEntropyBits {ρ σ T : Matrix I I ℂ}
    (hρ : FlaggedStates.IsDensity ρ) (hσ : FlaggedStates.IsDensity σ)
    (hT : FlaggedStates.IsEffect T) :
    FlaggedStates.relativeEntropyBits (measurement T ρ) (measurement T σ) =
      extendedBinaryRelativeEntropyBits
        (FlaggedStates.acceptanceProbability ρ T) (FlaggedStates.acceptanceProbability σ T) := by
  rw [measurement_density_eq_binaryState hρ hT, measurement_density_eq_binaryState hσ hT]
  exact binaryState_relativeEntropyBits _ _

theorem acceptanceProbability_eq_one_sub_typeI {ρ T : Matrix I I ℂ}
    (hρ : FlaggedStates.IsDensity ρ) :
    FlaggedStates.acceptanceProbability ρ T = 1 - (ρ * (1 - T)).trace.re := by
  simp only [Matrix.mul_sub, Matrix.mul_one, Matrix.trace_sub, Complex.sub_re,
    hρ.2, Complex.one_re, FlaggedStates.acceptanceProbability]
  ring

theorem measurement_relativeEntropyBits_errors {ρ σ T : Matrix I I ℂ}
    (hρ : FlaggedStates.IsDensity ρ) (hσ : FlaggedStates.IsDensity σ)
    (hT : FlaggedStates.IsEffect T) :
    FlaggedStates.relativeEntropyBits (measurement T ρ) (measurement T σ) =
      extendedBinaryRelativeEntropyBits (1 - (ρ * (1 - T)).trace.re) (σ * T).trace.re := by
  rw [measurement_relativeEntropyBits hρ hσ hT, acceptanceProbability_eq_one_sub_typeI hρ]
  rfl

end QuantumProver.SuperchannelDiscrimination.BinaryMeasurement

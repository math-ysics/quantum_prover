import Mathlib
import QuantumProver.InformationTheory.SuperchannelDiscrimination.SpectralPinching
import QuantumProver.InformationTheory.SuperchannelDiscrimination.PetzMoments
import QuantumProver.InformationTheory.SuperchannelDiscrimination.PetzTensorTail

set_option autoImplicit false

noncomputable section
open Matrix Filter
open scoped BigOperators Topology ComplexOrder MatrixOrder Matrix.Norms.L2Operator Matrix Kronecker

namespace QuantumProver.SuperchannelDiscrimination.PetzSmoothing

variable {I κ R : Type*} [Fintype I] [Fintype κ] [Fintype R]
  [DecidableEq I] [DecidableEq R]

structure IsProjection (Q : Matrix I I ℂ) : Prop where
  selfAdjoint : Q.IsHermitian
  idempotent : Q * Q = Q

omit [DecidableEq I] in
theorem IsProjection.posSemidef {Q : Matrix I I ℂ} (hQ : IsProjection Q) : Q.PosSemidef := by
  simpa only [hQ.selfAdjoint.eq, hQ.idempotent] using Matrix.posSemidef_conjTranspose_mul_self Q

theorem IsProjection.complement {Q : Matrix I I ℂ} (hQ : IsProjection Q) :
    IsProjection (1 - Q) := by
  constructor
  · exact Matrix.isHermitian_one.sub hQ.selfAdjoint
  · simp only [sub_mul, mul_sub, Matrix.one_mul, Matrix.mul_one, hQ.idempotent]
    abel

theorem IsProjection.isEffect {Q : Matrix I I ℂ} (hQ : IsProjection Q) :
    FlaggedStates.IsEffect Q := ⟨hQ.posSemidef, hQ.complement.posSemidef⟩

def complementaryCutoff (A B : Matrix I I ℂ) (t : ℝ) : Matrix I I ℂ :=
  1 - PetzTensorTail.spectralUpperTail A B t

theorem complementaryCutoff_isProjection {A B : Matrix I I ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (t : ℝ) :
    IsProjection (complementaryCutoff A B t) := by
  have hH : (A - t • B).IsHermitian := hA.sub (hB.smul (IsSelfAdjoint.all t))
  exact (show IsProjection (PetzTensorTail.positiveSpectralTest (A - t • B)) from
    ⟨(PetzTensorTail.positiveSpectralTest_isEffect hH).1.1,
      PetzTensorTail.positiveSpectralTest_idempotent hH⟩).complement

def cropMap (Q : Matrix I I ℂ) : Matrix I I ℂ →ₗ[ℂ] Matrix I I ℂ :=
  Pinching.pinchingMap (fun _ : Unit => Q)

theorem cropMap_apply (Q X : Matrix I I ℂ) : cropMap Q X = Q * X * Qᴴ := by
  simp [cropMap, Pinching.pinchingMap]

theorem cropMap_completelyPositive (Q : Matrix I I ℂ) :
    DiamondControl.CompletelyPositive (cropMap Q) :=
  Pinching.pinchingMap_completelyPositive _

theorem cropMap_positive_allReferences (Q : Matrix I I ℂ)
    (R : Type*) [Fintype R] [DecidableEq R] {X : Matrix (I × R) (I × R) ℂ}
    (hX : X.PosSemidef) : (DiamondControl.amplifyMap (cropMap Q) R X).PosSemidef :=
  Pinching.pinchingMap_completelyPositive_allReferences _ R hX

theorem cropMap_posSemidef (Q : Matrix I I ℂ) {X : Matrix I I ℂ} (hX : X.PosSemidef) :
    (cropMap Q X).PosSemidef := by
  rw [cropMap_apply]
  exact hX.mul_mul_conjTranspose_same Q

theorem cropMap_trace {Q : Matrix I I ℂ} (hQ : IsProjection Q) (X : Matrix I I ℂ) :
    (cropMap Q X).trace = (X * Q).trace := by
  rw [cropMap_apply, hQ.selfAdjoint.eq, Matrix.trace_mul_cycle, hQ.idempotent,
    Matrix.trace_mul_comm]

theorem cropMap_trace_re_le {Q : Matrix I I ℂ} (hQ : IsProjection Q)
    {X : Matrix I I ℂ} (hX : X.PosSemidef) : (cropMap Q X).trace.re ≤ X.trace.re := by
  have h := FlaggedStates.trace_mul_re_nonneg hX hQ.complement.posSemidef
  rw [cropMap_trace hQ]
  simp only [Matrix.mul_sub, Matrix.mul_one, Matrix.trace_sub, Complex.sub_re] at h
  linarith

theorem cropMap_traceNonincreasing {Q : Matrix I I ℂ} (hQ : IsProjection Q)
    {X : Matrix I I ℂ} (hX : X.PosSemidef) : (cropMap Q X).trace ≤ X.trace := by
  have hdiff : 0 ≤ X.trace - (cropMap Q X).trace := by
    apply Complex.nonneg_iff.mpr
    constructor
    · simpa only [Complex.sub_re] using sub_nonneg.mpr (cropMap_trace_re_le hQ hX)
    · have hx := (Complex.nonneg_iff.mp hX.trace_nonneg).2
      have hc := (Complex.nonneg_iff.mp (cropMap_posSemidef Q hX).trace_nonneg).2
      simp only [Complex.sub_im, hx.symm, hc.symm, sub_self]
  exact sub_nonneg.mp hdiff

omit [DecidableEq I] in
theorem weighted_trace_cauchySchwarz {ρ : Matrix I I ℂ} (hρ : ρ.PosSemidef)
    (X Y : Matrix I I ℂ) :
    ‖(Y * ρ * Xᴴ).trace‖ ≤
      Real.sqrt (X * ρ * Xᴴ).trace.re * Real.sqrt (Y * ρ * Yᴴ).trace.re := by
  let : SeminormedAddCommGroup (Matrix I I ℂ) := ρ.toMatrixSeminormedAddCommGroup hρ
  let : InnerProductSpace ℂ (Matrix I I ℂ) := ρ.toMatrixInnerProductSpace hρ
  have h := norm_inner_le_norm (𝕜 := ℂ) X Y
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ) X, norm_eq_sqrt_re_inner (𝕜 := ℂ) Y] at h
  exact h

theorem complementaryCutoff_joint {A B : Matrix I I ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (hAB : Commute A B) (t : ℝ) :
    complementaryCutoff A B t =
      Pinching.spectralCombination (PetzTensorTail.jointProjections hA hB)
        (fun v => ((1 - PetzTensorTail.positiveIndicator (v.1.val - t * v.2.val) : ℝ) : ℂ)) := by
  unfold complementaryCutoff
  rw [PetzTensorTail.spectralUpperTail_joint hA hB hAB]
  have he := (PetzTensorTail.jointProjections_family hA hB hAB).complete
  simp only [Pinching.spectralCombination, Complex.ofReal_sub, Complex.ofReal_one,
    sub_smul, one_smul, Finset.sum_sub_distrib]
  rw [he]

theorem commuting_cutoff_cap {A B : Matrix I I ℂ}
    (hA : A.PosSemidef) (hB : B.PosDef) (hAB : Commute A B) (t : ℝ) (ht : 0 ≤ t) :
    (t • B - cropMap (complementaryCutoff A B t) A).PosSemidef := by
  classical
  let P := PetzTensorTail.jointProjections hA.1 hB.1
  have hP : Pinching.IsProjectionFamily P := PetzTensorTail.jointProjections_family hA.1 hB.1 hAB
  let q : PetzTensorTail.EigenLabel hA.1 × PetzTensorTail.EigenLabel hB.1 → ℝ :=
    fun v => 1 - PetzTensorTail.positiveIndicator (v.1.val - t * v.2.val)
  let Q := complementaryCutoff A B t
  have hQ : IsProjection Q := complementaryCutoff_isProjection hA.1 hB.1 t
  have hQF : Q = Pinching.spectralCombination P (fun v => (q v : ℂ)) :=
    complementaryCutoff_joint hA.1 hB.1 hAB t
  have hAF : Pinching.spectralCombination P (fun v => (v.1.val : ℂ)) = A :=
    PetzTensorTail.jointProjections_left hA.1 hB.1
  have hBF : Pinching.spectralCombination P (fun v => (v.2.val : ℂ)) = B :=
    PetzTensorTail.jointProjections_right hA.1 hB.1
  have hcrop : Q * A * Q = Pinching.spectralCombination P
      (fun v => ((q v * v.1.val * q v : ℝ) : ℂ)) := by
    calc
      Q * A * Q = Pinching.spectralCombination P (fun v => (q v : ℂ)) * A *
          Pinching.spectralCombination P (fun v => (q v : ℂ)) :=
        congrArg₂ (fun X Y : Matrix I I ℂ => X * A * Y) hQF hQF
      _ = Pinching.spectralCombination P (fun v => (q v : ℂ)) *
          Pinching.spectralCombination P (fun v => (v.1.val : ℂ)) *
          Pinching.spectralCombination P (fun v => (q v : ℂ)) :=
        congrArg (fun M : Matrix I I ℂ => Pinching.spectralCombination P (fun v => (q v : ℂ)) *
          M * Pinching.spectralCombination P (fun v => (q v : ℂ))) hAF.symm
      _ = _ := by
        rw [← PetzTensorTail.spectralCombination_mul hP, ← PetzTensorTail.spectralCombination_mul hP]
        congr 1
        ext v
        simp
  let c : PetzTensorTail.EigenLabel hA.1 × PetzTensorTail.EigenLabel hB.1 → ℝ :=
    fun v => t * v.2.val - q v * v.1.val * q v
  have hc (v) : 0 ≤ c v := by
    have hb := (PetzTensorTail.eigenLabel_pos hB v.2).le
    by_cases hact : 0 < v.1.val - t * v.2.val
    · simp only [c, q, PetzTensorTail.positiveIndicator, ite_eq_left hact, sub_self,
        zero_mul, mul_zero, sub_zero]
      exact mul_nonneg ht hb
    · simp only [c, q, PetzTensorTail.positiveIndicator, ite_eq_right hact, sub_zero,
        one_mul, mul_one]
      linarith
  have hdiff : Pinching.spectralCombination P (fun v => (c v : ℂ)) = t • B - Q * A * Q := by
    calc
      Pinching.spectralCombination P (fun v => (c v : ℂ)) =
          t • Pinching.spectralCombination P (fun v => (v.2.val : ℂ)) -
            Pinching.spectralCombination P (fun v => ((q v * v.1.val * q v : ℝ) : ℂ)) := by
        simp only [Pinching.spectralCombination]
        rw [Finset.smul_sum, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro v hv
        ext i j
        change (c v : ℂ) * P v i j = (t : ℂ) * ((v.2.val : ℂ) * P v i j) -
          ((q v * v.1.val * q v : ℝ) : ℂ) * P v i j
        simp only [c, Complex.ofReal_sub, Complex.ofReal_mul]
        ring
      _ = t • B - Q * A * Q := congrArg₂ (fun X Y : Matrix I I ℂ => t • X - Y) hBF hcrop.symm
  have hp := PetzTensorTail.spectralCombination_posSemidef hP c hc
  rw [hdiff] at hp
  rw [cropMap_apply]
  change (t • B - Q * A * Qᴴ).PosSemidef
  rw [hQ.selfAdjoint.eq]
  exact hp

theorem cutoff_crop_cap_of_domination {X A B : Matrix I I ℂ}
    (hA : A.PosSemidef) (hB : B.PosDef) (hAB : Commute A B)
    (v t : ℝ) (hv : 0 ≤ v) (ht : 0 ≤ t) (hdom : (v • A - X).PosSemidef) :
    ((v * t) • B - cropMap (complementaryCutoff A B t) X).PosSemidef := by
  let Q := complementaryCutoff A B t
  have hQ : IsProjection Q := complementaryCutoff_isProjection hA.1 hB.1 t
  have h1 := hdom.mul_mul_conjTranspose_same Q
  have h2 := (commuting_cutoff_cap hA hB hAB t ht).smul hv
  change (v • (t • B - cropMap Q A)).PosSemidef at h2
  have h := h1.add h2
  change ((v * t) • B - cropMap Q X).PosSemidef
  convert h using 1
  simp only [cropMap_apply, hQ.selfAdjoint.eq, Matrix.mul_sub, Matrix.sub_mul,
    Matrix.mul_smul, Matrix.smul_mul, smul_sub, smul_smul]
  abel

def reflection (E : Matrix I I ℂ) : Matrix I I ℂ := (2 : ℝ) • E - 1

omit [Fintype I] in
theorem reflection_isHermitian {E : Matrix I I ℂ} (hE : E.IsHermitian) :
    (reflection E).IsHermitian :=
  (hE.smul (IsSelfAdjoint.all (2 : ℝ))).sub Matrix.isHermitian_one

theorem reflection_sq {E : Matrix I I ℂ} (hE : E * E = E) :
    reflection E * reflection E = 1 := by
  simp only [reflection, two_smul, sub_mul, mul_sub, add_mul, mul_add,
    Matrix.one_mul, Matrix.mul_one, hE]
  abel

theorem trace_reflection_sandwich {H : Matrix I I ℂ}
    (hH : H.IsHermitian) (hHsq : H * H = 1) (X : Matrix I I ℂ) :
    (H * X * Hᴴ).trace = X.trace := by
  rw [hH.eq, Matrix.trace_mul_cycle, hHsq, Matrix.one_mul]

theorem trace_projection_sandwich {Q : Matrix I I ℂ} (hQ : IsProjection Q)
    (X : Matrix I I ℂ) : (Q * X * Qᴴ).trace = (X * Q).trace := by
  rw [← cropMap_apply, cropMap_trace hQ]

theorem reflection_projection_sandwich_trace {H Q : Matrix I I ℂ}
    (hH : H.IsHermitian) (hHsq : H * H = 1) (hQ : IsProjection Q)
    (X : Matrix I I ℂ) : ((H * Q) * X * (H * Q)ᴴ).trace = (X * Q).trace := by
  rw [Matrix.conjTranspose_mul]
  calc
    ((H * Q) * X * (Qᴴ * Hᴴ)).trace = (H * (Q * X * Qᴴ) * Hᴴ).trace := by
      simp only [Matrix.mul_assoc]
    _ = (Q * X * Qᴴ).trace := trace_reflection_sandwich hH hHsq _
    _ = (X * Q).trace := trace_projection_sandwich hQ X

theorem reflection_observable_disturbance {ρ T H : Matrix I I ℂ}
    (hρ : FlaggedStates.IsDensity ρ) (hT : IsProjection T)
    (hH : H.IsHermitian) (hHsq : H * H = 1) :
    ‖(H * (ρ - cropMap (1 - T) ρ)).trace‖ ≤ 2 * Real.sqrt (ρ * T).trace.re := by
  let Q := 1 - T
  have hQ : IsProjection Q := hT.complement
  have hquadT := reflection_projection_sandwich_trace hH hHsq hT ρ
  have hquadQ := reflection_projection_sandwich_trace hH hHsq hQ ρ
  have h1 := weighted_trace_cauchySchwarz hρ.1 (1 : Matrix I I ℂ) (H * T)
  simp only [Matrix.conjTranspose_one, Matrix.mul_one, hρ.2,
    Complex.one_re, Real.sqrt_one, one_mul, hquadT] at h1
  have h2 := weighted_trace_cauchySchwarz hρ.1 T (H * Q)
  rw [trace_projection_sandwich hT, hquadQ] at h2
  have hq1 : (ρ * Q).trace.re ≤ 1 := (FlaggedStates.acceptanceProbability_bounds hρ hQ.isEffect).2
  have hqroot : Real.sqrt (ρ * Q).trace.re ≤ 1 := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hq1
  have h2' : ‖(H * Q * ρ * Tᴴ).trace‖ ≤ Real.sqrt (ρ * T).trace.re := by
    calc
      _ ≤ Real.sqrt (ρ * T).trace.re * Real.sqrt (ρ * Q).trace.re := h2
      _ ≤ Real.sqrt (ρ * T).trace.re * 1 :=
        mul_le_mul_of_nonneg_left hqroot (Real.sqrt_nonneg _)
      _ = _ := mul_one _
  have he : H * (ρ - cropMap Q ρ) = H * T * ρ + H * Q * ρ * Tᴴ := by
    rw [cropMap_apply, hQ.selfAdjoint.eq, hT.selfAdjoint.eq]
    dsimp [Q]
    noncomm_ring
  change ‖(H * (ρ - cropMap Q ρ)).trace‖ ≤ _
  rw [he, Matrix.trace_add]
  calc
    _ ≤ ‖(H * T * ρ).trace‖ + ‖(H * Q * ρ * Tᴴ).trace‖ := norm_add_le _ _
    _ ≤ Real.sqrt (ρ * T).trace.re + Real.sqrt (ρ * T).trace.re := add_le_add h1 h2'
    _ = _ := by ring

theorem reflection_traceNorm_witness {D : Matrix I I ℂ} (hD : D.IsHermitian) :
    EffectPerturbation.traceNorm D =
      (reflection (EffectPerturbation.positiveSupport D) * D).trace.re := by
  rw [EffectPerturbation.traceNorm_eq_positiveSupport hD]
  simp only [reflection, Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul,
    Matrix.trace_sub, Matrix.trace_smul, Complex.sub_re, Complex.smul_re, smul_eq_mul,
    EffectPerturbation.effectValue]

theorem gentle_crop_traceNorm {ρ T : Matrix I I ℂ}
    (hρ : FlaggedStates.IsDensity ρ) (hT : IsProjection T) :
    EffectPerturbation.traceNorm (ρ - cropMap (1 - T) ρ) ≤
      2 * Real.sqrt (ρ * T).trace.re := by
  let D := ρ - cropMap (1 - T) ρ
  have hD : D.IsHermitian := hρ.1.1.sub (cropMap_posSemidef (1 - T) hρ.1).1
  let E := EffectPerturbation.positiveSupport D
  have hE : IsProjection E :=
    ⟨(EffectPerturbation.positiveSupport_isEffect hD).1.1,
      EffectPerturbation.positiveSupport_idempotent D⟩
  have h := reflection_observable_disturbance hρ hT
    (reflection_isHermitian hE.selfAdjoint) (reflection_sq hE.idempotent)
  calc
    EffectPerturbation.traceNorm D = (reflection E * D).trace.re := reflection_traceNorm_witness hD
    _ ≤ ‖(reflection E * D).trace‖ := Complex.re_le_norm _
    _ ≤ 2 * Real.sqrt (ρ * T).trace.re := h

def iidCutoff (ρ : Matrix I I ℂ) {σ : Matrix I I ℂ} (hσ : σ.PosSemidef)
    (n : ℕ) (L : ℝ) : Matrix (TensorPinching.RecursiveRows I n) (TensorPinching.RecursiveRows I n) ℂ :=
  1 - PetzTensorTail.iidLikelihoodTailTest ρ hσ n L

def iidCropMap (ρ : Matrix I I ℂ) {σ : Matrix I I ℂ} (hσ : σ.PosSemidef)
    (n : ℕ) (L : ℝ) :
    Matrix (TensorPinching.RecursiveRows I n) (TensorPinching.RecursiveRows I n) ℂ →ₗ[ℂ]
      Matrix (TensorPinching.RecursiveRows I n) (TensorPinching.RecursiveRows I n) ℂ :=
  cropMap (iidCutoff ρ hσ n L)

def iidSmoothedState (ρ : Matrix I I ℂ) {σ : Matrix I I ℂ} (hσ : σ.PosSemidef)
    (n : ℕ) (L : ℝ) : Matrix (TensorPinching.RecursiveRows I n) (TensorPinching.RecursiveRows I n) ℂ :=
  iidCropMap ρ hσ n L (TensorPinching.recursiveTensorPower ρ n)

def discardedMass (ρ : Matrix I I ℂ) {σ : Matrix I I ℂ} (hσ : σ.PosSemidef)
    (n : ℕ) (L : ℝ) : ℝ :=
  (TensorPinching.recursiveTensorPower ρ n * PetzTensorTail.iidLikelihoodTailTest ρ hσ n L).trace.re

theorem iidTest_isProjection {ρ σ : Matrix I I ℂ}
    (hρ : ρ.PosSemidef) (hσ : σ.PosDef) (n : ℕ) (L : ℝ) :
    IsProjection (PetzTensorTail.iidLikelihoodTailTest ρ hσ.posSemidef n L) := by
  have hA := Pinching.pinchingMap_posSemidef
    (TensorPinching.recursiveOccupancyProjections (SpectralPinching.spectralProjections hσ.1) n)
    (PetzTensorTail.recursiveTensorPower_posSemidef hρ n)
  have hB := PetzTensorTail.recursiveTensorPower_posDef hσ n
  have hH := hA.1.sub
    (hB.1.smul (IsSelfAdjoint.all (L / (PetzTensorTail.pinchingCost I n : ℝ))))
  exact ⟨(PetzTensorTail.iidLikelihoodTailTest_isEffect hρ hσ n L).1.1,
    PetzTensorTail.positiveSpectralTest_idempotent hH⟩

theorem iidCutoff_isProjection {ρ σ : Matrix I I ℂ}
    (hρ : ρ.PosSemidef) (hσ : σ.PosDef) (n : ℕ) (L : ℝ) :
    IsProjection (iidCutoff ρ hσ.posSemidef n L) := (iidTest_isProjection hρ hσ n L).complement

theorem iidCropMap_CP_TNI {ρ σ : Matrix I I ℂ}
    (hρ : ρ.PosSemidef) (hσ : σ.PosDef) (n : ℕ) (L : ℝ) :
    DiamondControl.CompletelyPositive (iidCropMap ρ hσ.posSemidef n L) ∧
    ∀ X, X.PosSemidef → (iidCropMap ρ hσ.posSemidef n L X).trace ≤ X.trace :=
  ⟨cropMap_completelyPositive _, fun _ hX => cropMap_traceNonincreasing (iidCutoff_isProjection hρ hσ n L) hX⟩

theorem iidCrop_cap {ρ σ : Matrix I I ℂ}
    (hρ : ρ.PosSemidef) (hσ : σ.PosDef) (n : ℕ) (L : ℝ) (hL : 0 ≤ L) :
    (L • TensorPinching.recursiveTensorPower σ n - iidSmoothedState ρ hσ.posSemidef n L).PosSemidef := by
  let X := TensorPinching.recursiveTensorPower ρ n
  let A := SpectralPinching.recursiveComparatorPinching hσ.posSemidef n X
  let B := TensorPinching.recursiveTensorPower σ n
  let v : ℝ := (PetzTensorTail.pinchingCost I n : ℝ)
  have hX := PetzTensorTail.recursiveTensorPower_posSemidef hρ n
  have hA : A.PosSemidef := Pinching.pinchingMap_posSemidef _ hX
  have hB : B.PosDef := PetzTensorTail.recursiveTensorPower_posDef hσ n
  have hAB : Commute A B := SpectralPinching.recursiveComparatorPinching_commutes_comparator hσ.posSemidef n X
  have hv : 0 < v := PetzTensorTail.pinchingCost_pos n
  have hdom : (v • A - X).PosSemidef :=
    SpectralPinching.recursiveComparatorPinching_domination hσ.posSemidef n hX
  have h := cutoff_crop_cap_of_domination hA hB hAB v (L / v) hv.le (div_nonneg hL hv.le) hdom
  have hcoef : v * (L / v) = L := by field_simp
  rw [hcoef] at h
  exact h

theorem iidCrop_trace {ρ σ : Matrix I I ℂ}
    (hρ : FlaggedStates.IsDensity ρ) (hσ : σ.PosDef) (n : ℕ) (L : ℝ) :
    (iidSmoothedState ρ hσ.posSemidef n L).trace.re = 1 - discardedMass ρ hσ.posSemidef n L := by
  have hn := PetzTensorTail.recursiveTensorPower_density hρ n
  unfold iidSmoothedState iidCropMap
  rw [cropMap_trace (iidCutoff_isProjection hρ.1 hσ n L)]
  simp only [iidCutoff, Matrix.mul_sub, Matrix.mul_one, Matrix.trace_sub, Complex.sub_re,
    hn.2, Complex.one_re, discardedMass]

theorem discardedMass_bounds {ρ σ : Matrix I I ℂ}
    (hρ : FlaggedStates.IsDensity ρ) (hσ : σ.PosDef) (n : ℕ) (L : ℝ) :
    0 ≤ discardedMass ρ hσ.posSemidef n L ∧ discardedMass ρ hσ.posSemidef n L ≤ 1 :=
  FlaggedStates.acceptanceProbability_bounds (PetzTensorTail.recursiveTensorPower_density hρ n)
    (PetzTensorTail.iidLikelihoodTailTest_isEffect hρ.1 hσ n L)

theorem iidCrop_gentle {ρ σ : Matrix I I ℂ}
    (hρ : FlaggedStates.IsDensity ρ) (hσ : σ.PosDef) (n : ℕ) (L : ℝ) :
    EffectPerturbation.traceNorm (TensorPinching.recursiveTensorPower ρ n - iidSmoothedState ρ hσ.posSemidef n L) ≤
      2 * Real.sqrt (discardedMass ρ hσ.posSemidef n L) :=
  gentle_crop_traceNorm (PetzTensorTail.recursiveTensorPower_density hρ n) (iidTest_isProjection hρ.1 hσ n L)

theorem choose_petzExponent_bits {ρ σ : Matrix I I ℂ}
    (hρ : FlaggedStates.IsDensity ρ) (hσ : σ.PosDef) (rate : ℝ)
    (hrate : FlaggedStates.relativeEntropyBits ρ σ < (rate : EReal)) :
    ∃ s : ℝ, 0 < s ∧ 0 < PetzMoments.petzMoment ρ σ s ∧
      Real.log (PetzMoments.petzMoment ρ σ s) < s * rate * Real.log 2 := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hreal : PetzMoments.relativeEntropyNats ρ σ / Real.log 2 < rate := by
    rw [PetzMoments.relativeEntropyBits_eq_nats_of_posDef hσ] at hrate
    exact_mod_cast hrate
  have hD : PetzMoments.relativeEntropyNats ρ σ < rate * Real.log 2 :=
    (div_lt_iff₀ hl2).mp hreal
  have hlt : ∀ᶠ s : ℝ in 𝓝[>] 0,
      Real.log (PetzMoments.petzMoment ρ σ s) / s < rate * Real.log 2 :=
    (PetzMoments.log_petzMoment_div_tendsto_right hρ hσ).eventually (eventually_lt_nhds hD)
  have hpos : ∀ᶠ s : ℝ in 𝓝[>] 0, 0 < PetzMoments.petzMoment ρ σ s :=
    (PetzMoments.petzMoment_eventually_pos hρ hσ).filter_mono nhdsWithin_le_nhds
  have hevent : ∀ᶠ s : ℝ in 𝓝[>] 0, 0 < s ∧ 0 < PetzMoments.petzMoment ρ σ s ∧
      Real.log (PetzMoments.petzMoment ρ σ s) < s * rate * Real.log 2 := by
    filter_upwards [self_mem_nhdsWithin, hpos, hlt] with s hs hm hr
    refine ⟨hs, hm, ?_⟩
    simpa only [mul_assoc, mul_left_comm, mul_comm] using (div_lt_iff₀ hs).mp hr
  exact hevent.exists

def rateBudget (n : ℕ) (rate : ℝ) : ℝ := (2 : ℝ) ^ ((n : ℝ) * rate)

theorem rateBudget_pos (n : ℕ) (rate : ℝ) : 0 < rateBudget n rate :=
  Real.rpow_pos_of_pos (by norm_num) _

theorem moment_budget_exp (M rate s : ℝ) (hM : 0 < M) (n : ℕ) :
    (rateBudget n rate) ^ (-s) * M ^ n =
      Real.exp (-(s * rate * Real.log 2 - Real.log M) * (n : ℝ)) := by
  unfold rateBudget
  rw [Real.rpow_def_of_pos (Real.rpow_pos_of_pos (by norm_num : 0 < (2 : ℝ)) _),
    Real.log_rpow (by norm_num : 0 < (2 : ℝ)), ← Real.rpow_natCast M n,
    Real.rpow_def_of_pos hM, ← Real.exp_add]
  congr 1
  ring

omit [DecidableEq I] in
theorem iid_petzBudget_tendsto (M rate s : ℝ) (hM : 0 < M)
    (hgap : Real.log M < s * rate * Real.log 2) :
    Tendsto (fun n : ℕ => (PetzTensorTail.pinchingCost I n : ℝ) ^ s *
      (rateBudget n rate) ^ (-s) * M ^ n) atTop (𝓝 0) := by
  let b := s * rate * Real.log 2 - Real.log M
  let c : ℝ := (Fintype.card I : ℝ) * s
  have hb : 0 < b := sub_pos.mpr hgap
  have hx : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have ht := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero c b hb).comp hx
  have hlim : Tendsto (fun n : ℕ => Real.exp b *
      (((n : ℝ) + 1) ^ c * Real.exp (-b * ((n : ℝ) + 1)))) atTop (𝓝 0) := by
    simpa only [Function.comp_def, mul_zero] using ht.const_mul (Real.exp b)
  have hcost (n : ℕ) : (PetzTensorTail.pinchingCost I n : ℝ) ^ s = ((n : ℝ) + 1) ^ c := by
    rw [PetzTensorTail.pinchingCost, Nat.cast_pow, Nat.cast_add, Nat.cast_one,
      ← Real.rpow_natCast ((n : ℝ) + 1) (Fintype.card I),
      ← Real.rpow_mul (by positivity : 0 ≤ (n : ℝ) + 1)]
  convert hlim using 1
  ext n
  rw [hcost, mul_assoc, moment_budget_exp M rate s hM n]
  change ((n : ℝ) + 1) ^ c * Real.exp (-b * (n : ℝ)) =
    Real.exp b * (((n : ℝ) + 1) ^ c * Real.exp (-b * ((n : ℝ) + 1)))
  calc
    _ = ((n : ℝ) + 1) ^ c * Real.exp (b + -b * ((n : ℝ) + 1)) := by
      congr 1
      congr 1
      ring
    _ = _ := by rw [Real.exp_add]; ring

theorem discardedMass_tendsto {ρ σ : Matrix I I ℂ}
    (hρ : FlaggedStates.IsDensity ρ) (hσ : σ.PosDef) (rate : ℝ)
    (hrate : FlaggedStates.relativeEntropyBits ρ σ < (rate : EReal)) :
    Tendsto (fun n : ℕ => discardedMass ρ hσ.posSemidef n (rateBudget n rate)) atTop (𝓝 0) := by
  obtain ⟨s, hs, hM, hgap⟩ := choose_petzExponent_bits hρ hσ rate hrate
  exact squeeze_zero (fun n => (discardedMass_bounds hρ hσ n (rateBudget n rate)).1)
    (fun n => PetzTensorTail.iidLikelihoodTail_le hρ.1 hσ n (rateBudget n rate) s
      (rateBudget_pos n rate) hs.le)
    (iid_petzBudget_tendsto (I := I) _ rate s hM hgap)

theorem iidCrop_traceNorm_tendsto {ρ σ : Matrix I I ℂ}
    (hρ : FlaggedStates.IsDensity ρ) (hσ : σ.PosDef) (rate : ℝ)
    (hrate : FlaggedStates.relativeEntropyBits ρ σ < (rate : EReal)) :
    Tendsto (fun n : ℕ => EffectPerturbation.traceNorm (TensorPinching.recursiveTensorPower ρ n -
      iidSmoothedState ρ hσ.posSemidef n (rateBudget n rate))) atTop (𝓝 0) := by
  have hm := discardedMass_tendsto hρ hσ rate hrate
  have hsqrt : Tendsto (fun n : ℕ => Real.sqrt (discardedMass ρ hσ.posSemidef n (rateBudget n rate)))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.sqrt_zero] using Real.continuous_sqrt.continuousAt.tendsto.comp hm
  have hbound : Tendsto (fun n : ℕ => 2 * Real.sqrt (discardedMass ρ hσ.posSemidef n (rateBudget n rate)))
      atTop (𝓝 0) := by simpa only [mul_zero] using hsqrt.const_mul 2
  exact squeeze_zero (fun n => EffectPerturbation.traceNorm_nonneg _)
    (fun n => iidCrop_gentle hρ hσ n (rateBudget n rate)) hbound

theorem iidCrop_trace_tendsto {ρ σ : Matrix I I ℂ}
    (hρ : FlaggedStates.IsDensity ρ) (hσ : σ.PosDef) (rate : ℝ)
    (hrate : FlaggedStates.relativeEntropyBits ρ σ < (rate : EReal)) :
    Tendsto (fun n : ℕ => (iidSmoothedState ρ hσ.posSemidef n (rateBudget n rate)).trace.re)
      atTop (𝓝 1) := by
  have h := (discardedMass_tendsto hρ hσ rate hrate).const_sub 1
  simpa only [iidCrop_trace hρ hσ, sub_zero] using h

theorem faithful_state_TNI_smoothing {ρ σ : Matrix I I ℂ}
    (hρ : FlaggedStates.IsDensity ρ) (hσdensity : FlaggedStates.IsDensity σ)
    (hσ : σ.PosDef) (rate : ℝ)
    (hrate : FlaggedStates.relativeEntropyBits ρ σ < (rate : EReal)) :
    (∀ n : ℕ,
      FlaggedStates.IsDensity (TensorPinching.recursiveTensorPower σ n) ∧
      (iidSmoothedState ρ hσ.posSemidef n (rateBudget n rate)).PosSemidef ∧
      DiamondControl.CompletelyPositive (iidCropMap ρ hσ.posSemidef n (rateBudget n rate)) ∧
      (∀ X, X.PosSemidef → (iidCropMap ρ hσ.posSemidef n (rateBudget n rate) X).trace ≤ X.trace) ∧
      ((rateBudget n rate) • TensorPinching.recursiveTensorPower σ n -
        iidSmoothedState ρ hσ.posSemidef n (rateBudget n rate)).PosSemidef) ∧
    Tendsto (fun n : ℕ => discardedMass ρ hσ.posSemidef n (rateBudget n rate)) atTop (𝓝 0) ∧
    Tendsto (fun n : ℕ => EffectPerturbation.traceNorm (TensorPinching.recursiveTensorPower ρ n -
      iidSmoothedState ρ hσ.posSemidef n (rateBudget n rate))) atTop (𝓝 0) ∧
    Tendsto (fun n : ℕ => (iidSmoothedState ρ hσ.posSemidef n (rateBudget n rate)).trace.re) atTop (𝓝 1) := by
  refine ⟨?_, discardedMass_tendsto hρ hσ rate hrate,
    iidCrop_traceNorm_tendsto hρ hσ rate hrate, iidCrop_trace_tendsto hρ hσ rate hrate⟩
  intro n
  have hc := iidCropMap_CP_TNI hρ.1 hσ n (rateBudget n rate)
  exact ⟨PetzTensorTail.recursiveTensorPower_density hσdensity n,
    cropMap_posSemidef _ (PetzTensorTail.recursiveTensorPower_posSemidef hρ.1 n),
    hc.1, hc.2, iidCrop_cap hρ.1 hσ n (rateBudget n rate) (rateBudget_pos n rate).le⟩

end QuantumProver.SuperchannelDiscrimination.PetzSmoothing

namespace QuantumProver.SuperchannelDiscrimination.GlobalMatrixSplit

variable {I E F : Type*} [Fintype I] [Fintype E] [Fintype F]
  [DecidableEq I] [DecidableEq E] [DecidableEq F]

def pseudoInverse (H : Matrix I I ℂ) : Matrix I I ℂ := cfc (fun x : ℝ => x⁻¹) H

theorem pseudoInverse_isHermitian (H : Matrix I I ℂ) :
    (pseudoInverse H).IsHermitian := cfc_predicate _ _

theorem pseudoInverse_inner {H : Matrix I I ℂ} (hH : H.IsHermitian) :
    pseudoInverse H * H * pseudoInverse H = pseudoInverse H := by
  have hf : (fun x : ℝ => x⁻¹ * x * x⁻¹) = (fun x : ℝ => x⁻¹) := by
    funext x
    by_cases hx : x = 0 <;> simp [hx]
  calc
    _ = cfc (fun x : ℝ => x⁻¹) H * cfc (fun x : ℝ => x) H *
        cfc (fun x : ℝ => x⁻¹) H := by rw [cfc_id' (p := IsSelfAdjoint) ℝ H hH]; rfl
    _ = cfc (fun x : ℝ => x⁻¹ * x * x⁻¹) H := by
      rw [← cfc_mul (p := IsSelfAdjoint) _ _ H (H.finite_real_spectrum.continuousOn _)
        (H.finite_real_spectrum.continuousOn _),
        ← cfc_mul (p := IsSelfAdjoint) _ _ H (H.finite_real_spectrum.continuousOn _)
        (H.finite_real_spectrum.continuousOn _)]
    _ = _ := by rw [hf]; rfl

theorem pseudoInverse_outer {H : Matrix I I ℂ} (hH : H.IsHermitian) :
    H * pseudoInverse H * H = H := by
  have hf : (fun x : ℝ => x * x⁻¹ * x) = (fun x : ℝ => x) := by
    funext x
    by_cases hx : x = 0 <;> simp [hx]
  calc
    _ = cfc (fun x : ℝ => x) H * cfc (fun x : ℝ => x⁻¹) H *
        cfc (fun x : ℝ => x) H := by rw [cfc_id' (p := IsSelfAdjoint) ℝ H hH]; rfl
    _ = cfc (fun x : ℝ => x * x⁻¹ * x) H := by
      rw [← cfc_mul (p := IsSelfAdjoint) _ _ H (H.finite_real_spectrum.continuousOn _)
        (H.finite_real_spectrum.continuousOn _),
        ← cfc_mul (p := IsSelfAdjoint) _ _ H (H.finite_real_spectrum.continuousOn _)
        (H.finite_real_spectrum.continuousOn _)]
    _ = H := by rw [hf, cfc_id' (p := IsSelfAdjoint) ℝ H hH]

omit [DecidableEq E] in

theorem reconstruct_columns_of_gram_domination {H : Matrix I I ℂ}
    (hH : H.IsHermitian) (K : Matrix I E ℂ) (c : ℝ)
    (hdom : (c • H - K * Kᴴ).PosSemidef) :
    H * pseudoInverse H * K = K := by
  let Q : Matrix I I ℂ := 1 - H * pseudoInverse H
  have hQH : Q * H = 0 := by
    change (1 - H * pseudoInverse H) * H = 0
    rw [Matrix.sub_mul, Matrix.one_mul, pseudoInverse_outer hH, sub_self]
  have hneg : (-((Q * K) * (Q * K)ᴴ)).PosSemidef := by
    have hc := hdom.mul_mul_conjTranspose_same Q
    have heq : Q * (c • H - K * Kᴴ) * Qᴴ = -((Q * K) * (Q * K)ᴴ) := by
      calc
        _ = c • (Q * H * Qᴴ) - (Q * K) * (Q * K)ᴴ := by
          simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul,
            Matrix.smul_mul, Matrix.conjTranspose_mul, Matrix.mul_assoc]
        _ = _ := by rw [hQH, Matrix.zero_mul, smul_zero, zero_sub]
    exact heq ▸ hc
  have hzero : (Q * K) * (Q * K)ᴴ = 0 :=
    le_antisymm (neg_nonneg.mp hneg.nonneg)
      (Matrix.posSemidef_self_mul_conjTranspose (Q * K)).nonneg
  have hQK : Q * K = 0 := Matrix.self_mul_conjTranspose_eq_zero.mp hzero
  have hs : K - H * pseudoInverse H * K = 0 := by
    simpa only [Q, Matrix.sub_mul, Matrix.one_mul] using hQK
  exact (sub_eq_zero.mp hs).symm

theorem sandwich_le_self {H B P : Matrix I I ℂ}
    (hB : B.PosSemidef) (hHB : (H - B).PosSemidef)
    (hP : P.IsHermitian) (hPHP : P * H * P = P) :
    (B - B * P * B).PosSemidef := by
  have h1 := hB.mul_mul_conjTranspose_same (1 - B * P)
  have h2 := hHB.mul_mul_conjTranspose_same (B * P)
  have heq : (1 - B * P) * B * (1 - B * P)ᴴ +
      (B * P) * (H - B) * (B * P)ᴴ = B - B * P * B := by
    simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_one,
      Matrix.conjTranspose_mul, hP.eq, hB.1.eq]
    calc
      _ = B - B * P * B - B * P * B + B * (P * H * P) * B := by noncomm_ring
      _ = _ := by rw [hPHP]; noncomm_ring
  exact heq ▸ h1.add h2

def columnPiece (B H : Matrix I I ℂ) (K : Matrix I E ℂ) : Matrix I E ℂ :=
  B * pseudoInverse H * K

omit [DecidableEq E] in
theorem columnPiece_gram_le {H B : Matrix I I ℂ}
    (hH : H.IsHermitian) (hB : B.PosSemidef) (hHB : (H - B).PosSemidef)
    (K : Matrix I E ℂ) (hK : (H - K * Kᴴ).PosSemidef) :
    (B - columnPiece B H K * (columnPiece B H K)ᴴ).PosSemidef := by
  have hP := pseudoInverse_isHermitian H
  have h1 := sandwich_le_self hB hHB hP (pseudoInverse_inner hH)
  have h2 := hK.mul_mul_conjTranspose_same (B * pseudoInverse H)
  have heq : B - B * pseudoInverse H * B +
      (B * pseudoInverse H) * (H - K * Kᴴ) * (B * pseudoInverse H)ᴴ =
      B - columnPiece B H K * (columnPiece B H K)ᴴ := by
    simp only [columnPiece, Matrix.conjTranspose_mul, hP.eq, hB.1.eq]
    calc
      _ = B - B * pseudoInverse H * B +
          B * (pseudoInverse H * H * pseudoInverse H) * B -
          (B * pseudoInverse H * K) * (Kᴴ * pseudoInverse H * B) := by
        simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
        abel
      _ = _ := by
        rw [pseudoInverse_inner hH]
        simp only [Matrix.mul_assoc]
        abel
  exact heq ▸ h1.add h2

omit [DecidableEq E] in

theorem singular_positive_column_split {A Z : Matrix I I ℂ}
    (hA : A.PosSemidef) (hZ : Z.PosSemidef) (K : Matrix I E ℂ)
    (hK : (A + Z - K * Kᴴ).PosSemidef) :
    columnPiece A (A + Z) K + columnPiece Z (A + Z) K = K ∧
    (A - columnPiece A (A + Z) K * (columnPiece A (A + Z) K)ᴴ).PosSemidef ∧
    (Z - columnPiece Z (A + Z) K * (columnPiece Z (A + Z) K)ᴴ).PosSemidef := by
  have hH := (hA.add hZ).1
  refine ⟨?_, columnPiece_gram_le hH hA ?_ K hK,
    columnPiece_gram_le hH hZ ?_ K hK⟩
  · simp only [columnPiece, ← Matrix.add_mul]
    exact reconstruct_columns_of_gram_domination hH K 1 (by simpa using hK)
  · simpa only [add_sub_cancel_left] using hZ
  · simpa only [add_sub_cancel_right] using hA

def douglasFactor (B : Matrix I F ℂ) (K : Matrix I E ℂ) : Matrix F E ℂ :=
  Bᴴ * pseudoInverse (B * Bᴴ) * K

omit [DecidableEq E] [DecidableEq F] in
theorem douglasFactor_reconstruct (B : Matrix I F ℂ) (K : Matrix I E ℂ) (c : ℝ)
    (hdom : (c • (B * Bᴴ) - K * Kᴴ).PosSemidef) :
    B * douglasFactor B K = K := by
  simpa only [douglasFactor, Matrix.mul_assoc] using
    reconstruct_columns_of_gram_domination (Matrix.posSemidef_self_mul_conjTranspose B).1 K c hdom

omit [DecidableEq F] in
theorem comparator_column_projection (B : Matrix I F ℂ) :
    PetzSmoothing.IsProjection (Bᴴ * pseudoInverse (B * Bᴴ) * B) := by
  have hP := pseudoInverse_isHermitian (B * Bᴴ)
  constructor
  · change (Bᴴ * pseudoInverse (B * Bᴴ) * B)ᴴ = _
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hP.eq,
      Matrix.mul_assoc]
  · calc
      _ = Bᴴ * (pseudoInverse (B * Bᴴ) * (B * Bᴴ) * pseudoInverse (B * Bᴴ)) * B := by
        simp only [Matrix.mul_assoc]
      _ = _ := by rw [pseudoInverse_inner (Matrix.posSemidef_self_mul_conjTranspose B).1]

omit [DecidableEq E] in
theorem douglasFactor_gram_le (B : Matrix I F ℂ) (K : Matrix I E ℂ) (c : ℝ)
    (hc : 0 ≤ c) (hdom : (c • (B * Bᴴ) - K * Kᴴ).PosSemidef) :
    (c • (1 : Matrix F F ℂ) - douglasFactor B K * (douglasFactor B K)ᴴ).PosSemidef := by
  let P := pseudoInverse (B * Bᴴ)
  have hP : P.IsHermitian := pseudoInverse_isHermitian (B * Bᴴ)
  have h1 := hdom.mul_mul_conjTranspose_same (Bᴴ * P)
  have h2 := (comparator_column_projection B).complement.posSemidef.smul hc
  have heq : (Bᴴ * P) * (c • (B * Bᴴ) - K * Kᴴ) * (Bᴴ * P)ᴴ +
      c • (1 - Bᴴ * P * B) =
      c • (1 : Matrix F F ℂ) - douglasFactor B K * (douglasFactor B K)ᴴ := by
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      hP.eq, douglasFactor]
    calc
      _ = c • (Bᴴ * (P * (B * Bᴴ) * P) * B) -
          (Bᴴ * P * K) * (Kᴴ * P * B) + c • (1 - Bᴴ * P * B) := by
        simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
          Matrix.mul_assoc]
      _ = _ := by
        rw [show P * (B * Bᴴ) * P = P from
          pseudoInverse_inner (Matrix.posSemidef_self_mul_conjTranspose B).1]
        simp only [smul_sub, P, (pseudoInverse_isHermitian (B * Bᴴ)).eq, Matrix.mul_assoc]
        abel
  exact heq ▸ h1.add h2

omit [DecidableEq E] in

theorem exists_bounded_column_factor (B : Matrix I F ℂ) (K : Matrix I E ℂ)
    (c : ℝ) (hc : 0 ≤ c) (hdom : (c • (B * Bᴴ) - K * Kᴴ).PosSemidef) :
    ∃ D : Matrix F E ℂ, B * D = K ∧ (c • (1 : Matrix F F ℂ) - D * Dᴴ).PosSemidef :=
  ⟨douglasFactor B K, douglasFactor_reconstruct B K c hdom,
    douglasFactor_gram_le B K c hc hdom⟩

theorem norm_sq_le_of_left_gram {D : Matrix F E ℂ} {c : ℝ} (hc : 0 ≤ c)
    (hD : (c • (1 : Matrix F F ℂ) - D * Dᴴ).PosSemidef) : ‖D‖ ^ 2 ≤ c := by
  have hn : ‖D * Dᴴ‖ ≤ c :=
    (CStarAlgebra.norm_le_iff_le_algebraMap (D * Dᴴ) hc
      (Matrix.posSemidef_self_mul_conjTranspose D).nonneg).2 (by
        simpa only [Algebra.algebraMap_eq_smul_one, Matrix.le_iff] using hD)
  have heq : ‖D * Dᴴ‖ = ‖D‖ ^ 2 := by
    simpa only [Matrix.conjTranspose_conjTranspose, Matrix.l2_opNorm_conjTranspose, pow_two] using
      Matrix.l2_opNorm_conjTranspose_mul_self Dᴴ
  rwa [heq] at hn

omit [DecidableEq E] in
theorem norm_sq_le_of_right_gram {C : Matrix E F ℂ} {c : ℝ} (hc : 0 ≤ c)
    (hC : (c • (1 : Matrix F F ℂ) - Cᴴ * C).PosSemidef) : ‖C‖ ^ 2 ≤ c := by
  have hn : ‖Cᴴ * C‖ ≤ c :=
    (CStarAlgebra.norm_le_iff_le_algebraMap (Cᴴ * C) hc
      (Matrix.posSemidef_conjTranspose_mul_self C).nonneg).2 (by
        simpa only [Algebra.algebraMap_eq_smul_one, Matrix.le_iff] using hC)
  simpa only [Matrix.l2_opNorm_conjTranspose_mul_self, pow_two] using hn

theorem douglasFactor_norm_sq_le (B : Matrix I F ℂ) (K : Matrix I E ℂ)
    (c : ℝ) (hc : 0 ≤ c) (hdom : (c • (B * Bᴴ) - K * Kᴴ).PosSemidef) :
    ‖douglasFactor B K‖ ^ 2 ≤ c :=
  norm_sq_le_of_left_gram hc (douglasFactor_gram_le B K c hc hdom)

omit [DecidableEq E] in

theorem environmentalFactor_gram_le (B : Matrix I F ℂ) (K : Matrix I E ℂ)
    (c : ℝ) (hc : 0 ≤ c) (hdom : (c • (B * Bᴴ) - K * Kᴴ).PosSemidef) :
    (c • (1 : Matrix F F ℂ) - (douglasFactor B K)ᵀᴴ * (douglasFactor B K)ᵀ).PosSemidef := by
  have h := (douglasFactor_gram_le B K c hc hdom).transpose
  simpa only [Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_one,
    Matrix.transpose_mul, Matrix.conjTranspose_transpose_eq_transpose_conjTranspose] using h

omit [DecidableEq E] in
theorem environmentalFactor_norm_sq_le (B : Matrix I F ℂ) (K : Matrix I E ℂ)
    (c : ℝ) (hc : 0 ≤ c) (hdom : (c • (B * Bᴴ) - K * Kᴴ).PosSemidef) :
    ‖(douglasFactor B K)ᵀ‖ ^ 2 ≤ c :=
  norm_sq_le_of_right_gram hc (environmentalFactor_gram_le B K c hc hdom)

omit [DecidableEq E] in

theorem exists_global_environmental_split (B : Matrix I F ℂ) (K : Matrix I E ℂ)
    {Z : Matrix I I ℂ} (hZ : Z.PosSemidef) (t : ℝ) (ht : 0 ≤ t)
    (hdom : (t • (B * Bᴴ) + Z - K * Kᴴ).PosSemidef) :
    ∃ C : Matrix E F ℂ,
      (t • (1 : Matrix F F ℂ) - Cᴴ * C).PosSemidef ∧ ‖C‖ ^ 2 ≤ t ∧
      (Z - (K - B * Cᵀ) * (K - B * Cᵀ)ᴴ).PosSemidef := by
  let A := t • (B * Bᴴ)
  let K0 := columnPiece A (A + Z) K
  let K1 := columnPiece Z (A + Z) K
  have hsplit := singular_positive_column_split
    ((Matrix.posSemidef_self_mul_conjTranspose B).smul ht) hZ K hdom
  have h0 : (t • (B * Bᴴ) - K0 * K0ᴴ).PosSemidef := hsplit.2.1
  let C := (douglasFactor B K0)ᵀ
  have hBC : B * Cᵀ = K0 := by
    simpa only [C, Matrix.transpose_transpose] using douglasFactor_reconstruct B K0 t h0
  have hsum : K0 + K1 = K := hsplit.1
  have hres : K - B * Cᵀ = K1 := by rw [hBC, ← hsum]; abel
  refine ⟨C, environmentalFactor_gram_le B K0 t ht h0,
    environmentalFactor_norm_sq_le B K0 t ht h0, ?_⟩
  rw [hres]
  exact hsplit.2.2

omit [DecidableEq E] in

theorem reconstruct_columns_of_support {H : Matrix I I ℂ} (hH : H.IsHermitian)
    (K : Matrix I E ℂ) (hs : FlaggedStates.HasSupportIn (K * Kᴴ) H) :
    H * pseudoInverse H * K = K := by
  let Q : Matrix I I ℂ := 1 - H * pseudoInverse H
  have hQH : Q * H = 0 := by
    change (1 - H * pseudoInverse H) * H = 0
    rw [Matrix.sub_mul, Matrix.one_mul, pseudoInverse_outer hH, sub_self]
  have hHQ : H * Qᴴ = 0 := by
    have h := congrArg Matrix.conjTranspose hQH
    simpa only [Matrix.conjTranspose_mul, hH.eq, Matrix.conjTranspose_zero] using h
  have hKQ : (K * Kᴴ) * Qᴴ = 0 := by
    ext i j
    have hv : H *ᵥ (fun k => Qᴴ k j) = 0 := by
      ext l
      exact congrArg (fun M : Matrix I I ℂ => M l j) hHQ
    exact congrFun (hs (fun k => Qᴴ k j) hv) i
  have hk : Kᴴ * Qᴴ = 0 := (Matrix.self_mul_conjTranspose_mul_eq_zero K Qᴴ).mp hKQ
  have hQK : Q * K = 0 := by
    have h := congrArg Matrix.conjTranspose hk
    simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.conjTranspose_zero] using h
  have heq : K - H * pseudoInverse H * K = 0 := by
    simpa only [Q, Matrix.sub_mul, Matrix.one_mul] using hQK
  exact (sub_eq_zero.mp heq).symm

theorem left_gram_le_norm_sq (D : Matrix F E ℂ) :
    (‖D‖ ^ 2 • (1 : Matrix F F ℂ) - D * Dᴴ).PosSemidef := by
  have heq : ‖D * Dᴴ‖ = ‖D‖ ^ 2 := by
    simpa only [Matrix.conjTranspose_conjTranspose, Matrix.l2_opNorm_conjTranspose, pow_two] using
      Matrix.l2_opNorm_conjTranspose_mul_self Dᴴ
  have h : D * Dᴴ ≤ algebraMap ℝ (Matrix F F ℂ) (‖D‖ ^ 2) :=
    (CStarAlgebra.norm_le_iff_le_algebraMap (D * Dᴴ) (sq_nonneg _)
      (Matrix.posSemidef_self_mul_conjTranspose D).nonneg).mp (by rw [heq])
  simpa only [Algebra.algebraMap_eq_smul_one, Matrix.le_iff] using h

omit [DecidableEq E] [DecidableEq F] in
theorem douglasFactor_reconstruct_of_support (B : Matrix I F ℂ) (K : Matrix I E ℂ)
    (hs : FlaggedStates.HasSupportIn (K * Kᴴ) (B * Bᴴ)) :
    B * douglasFactor B K = K := by
  simpa only [douglasFactor, Matrix.mul_assoc] using
    reconstruct_columns_of_support (Matrix.posSemidef_self_mul_conjTranspose B).1 K hs

theorem exists_finite_gram_domination_of_support (B : Matrix I F ℂ) (K : Matrix I E ℂ)
    (hs : FlaggedStates.HasSupportIn (K * Kᴴ) (B * Bᴴ)) :
    ∃ c : ℝ, 1 ≤ c ∧ (c • (B * Bᴴ) - K * Kᴴ).PosSemidef := by
  let D := douglasFactor B K
  let c := ‖D‖ ^ 2 + 1
  have hD : (c • (1 : Matrix F F ℂ) - D * Dᴴ).PosSemidef := by
    have h := Matrix.PosSemidef.one.add (left_gram_le_norm_sq D)
    have heq : (1 : Matrix F F ℂ) + (‖D‖ ^ 2 • 1 - D * Dᴴ) = c • 1 - D * Dᴴ := by
      simp only [c, add_smul, one_smul]
      abel
    exact heq ▸ h
  have hBD : B * D = K := douglasFactor_reconstruct_of_support B K hs
  have heq : B * (c • (1 : Matrix F F ℂ) - D * Dᴴ) * Bᴴ =
      c • (B * Bᴴ) - K * Kᴴ := by
    calc
      _ = c • (B * Bᴴ) - (B * D) * (B * D)ᴴ := by
        simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
          Matrix.mul_one, Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [hBD]
  refine ⟨c, ?_, heq ▸ hD.mul_mul_conjTranspose_same B⟩
  dsimp [c]
  linarith [sq_nonneg ‖D‖]

theorem exists_exact_environmental_factor_of_support (B : Matrix I F ℂ) (K : Matrix I E ℂ)
    (hs : FlaggedStates.HasSupportIn (K * Kᴴ) (B * Bᴴ)) :
    ∃ c : ℝ, 1 ≤ c ∧ ∃ C : Matrix E F ℂ,
      B * Cᵀ = K ∧ (c • (1 : Matrix F F ℂ) - Cᴴ * C).PosSemidef ∧ ‖C‖ ^ 2 ≤ c := by
  obtain ⟨c, hc, hdom⟩ := exists_finite_gram_domination_of_support B K hs
  have hc0 : 0 ≤ c := zero_le_one.trans hc
  refine ⟨c, hc, (douglasFactor B K)ᵀ, ?_,
    environmentalFactor_gram_le B K c hc0 hdom,
    environmentalFactor_norm_sq_le B K c hc0 hdom⟩
  simpa only [Matrix.transpose_transpose] using douglasFactor_reconstruct B K c hdom

omit [DecidableEq I] in
theorem hasSupportIn_of_finite_domination {A H : Matrix I I ℂ}
    (hA : A.PosSemidef) (c : ℝ) (hdom : (c • H - A).PosSemidef) :
    FlaggedStates.HasSupportIn A H := by
  intro v hv
  have hn : 0 ≤ -(star v ⬝ᵥ (A *ᵥ v)) := by
    simpa only [Matrix.sub_mulVec, Matrix.smul_mulVec, hv, smul_zero, zero_sub,
      dotProduct_neg] using hdom.dotProduct_mulVec_nonneg v
  have heq : star v ⬝ᵥ (A *ᵥ v) = 0 :=
    le_antisymm (neg_nonneg.mp hn) (hA.dotProduct_mulVec_nonneg v)
  exact hA.dotProduct_mulVec_zero_iff.mp heq

theorem exists_finite_domination_of_support {A H : Matrix I I ℂ}
    (hA : A.PosSemidef) (hH : H.PosSemidef) (hs : FlaggedStates.HasSupportIn A H) :
    ∃ c : ℝ, 1 ≤ c ∧ (c • H - A).PosSemidef := by
  let B := CFC.sqrt H
  let K := CFC.sqrt A
  have hB : B.IsHermitian := (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg H)).1
  have hK : K.IsHermitian := (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)).1
  have hBB : B * Bᴴ = H := by
    rw [hB.eq]
    exact CFC.sqrt_mul_sqrt_self H hH.nonneg
  have hKK : K * Kᴴ = A := by
    rw [hK.eq]
    exact CFC.sqrt_mul_sqrt_self A hA.nonneg
  obtain ⟨c, hc, hdom⟩ := exists_finite_gram_domination_of_support B K
    (by rw [hKK, hBB]; exact hs)
  exact ⟨c, hc, by simpa only [hBB, hKK] using hdom⟩

theorem support_iff_finite_domination {A H : Matrix I I ℂ}
    (hA : A.PosSemidef) (hH : H.PosSemidef) :
    FlaggedStates.HasSupportIn A H ↔ ∃ c : ℝ, 1 ≤ c ∧ (c • H - A).PosSemidef := by
  refine ⟨exists_finite_domination_of_support hA hH, ?_⟩
  rintro ⟨c, _, hdom⟩
  exact hasSupportIn_of_finite_domination hA c hdom

theorem finite_relativeEntropy_iff_finite_domination {A H : Matrix I I ℂ}
    (hA : A.PosSemidef) (hH : H.PosSemidef) :
    FlaggedStates.relativeEntropyBits A H ≠ ⊤ ↔
      ∃ c : ℝ, 1 ≤ c ∧ (c • H - A).PosSemidef := by
  rw [← support_iff_finite_domination hA hH]
  simp only [ne_eq, FlaggedStates.relativeEntropyBits_eq_top_iff, not_not]

end QuantumProver.SuperchannelDiscrimination.GlobalMatrixSplit

namespace QuantumProver.SuperchannelDiscrimination.TensorWordTruncation

variable {I J K L I' J' : Type*} [Fintype I] [Fintype J] [Fintype K] [Fintype L]
  [Fintype I'] [Fintype J'] [DecidableEq I] [DecidableEq J] [DecidableEq K]
  [DecidableEq L] [DecidableEq I'] [DecidableEq J']

theorem right_gram_le_norm_sq (A : Matrix I J ℂ) :
    (‖A‖ ^ 2 • (1 : Matrix J J ℂ) - Aᴴ * A).PosSemidef := by
  simpa only [Matrix.conjTranspose_conjTranspose, Matrix.l2_opNorm_conjTranspose] using
    GlobalMatrixSplit.left_gram_le_norm_sq Aᴴ

omit [DecidableEq I'] in
theorem norm_submatrix_le (A : Matrix I J ℂ) (e : I' ≃ I) (f : J' ≃ J) :
    ‖A.submatrix e f‖ ≤ ‖A‖ := by
  have h := (right_gram_le_norm_sq A).submatrix f
  have hg : (A.submatrix e f)ᴴ * A.submatrix e f = (Aᴴ * A).submatrix f f := by
    rw [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv]
  have hc : (‖A‖ ^ 2 • (1 : Matrix J' J' ℂ) -
      (A.submatrix e f)ᴴ * A.submatrix e f).PosSemidef := by
    have hid : (1 : Matrix J J ℂ).submatrix f f = (1 : Matrix J' J' ℂ) :=
      Matrix.submatrix_one_equiv f
    change (‖A‖ ^ 2 • ((1 : Matrix J J ℂ).submatrix f f) -
      (Aᴴ * A).submatrix f f).PosSemidef at h
    rw [hid] at h
    rw [hg]
    exact h
  have hn := GlobalMatrixSplit.norm_sq_le_of_right_gram (sq_nonneg ‖A‖) hc
  nlinarith [norm_nonneg (A.submatrix e f), norm_nonneg A]

theorem norm_submatrix_equiv (A : Matrix I J ℂ) (e : I' ≃ I) (f : J' ≃ J) :
    ‖A.submatrix e f‖ = ‖A‖ := by
  apply le_antisymm (norm_submatrix_le A e f)
  have h := norm_submatrix_le (A.submatrix e f) e.symm f.symm
  have heq : (A.submatrix e f).submatrix e.symm f.symm = A := by ext x y; simp
  rw [heq] at h
  exact h

theorem norm_kronecker_le (A : Matrix I J ℂ) (B : Matrix K L ℂ) :
    ‖A ⊗ₖ B‖ ≤ ‖A‖ * ‖B‖ := by
  have h1 := (right_gram_le_norm_sq A).kronecker
    ((Matrix.PosSemidef.one : (1 : Matrix L L ℂ).PosSemidef).smul (sq_nonneg ‖B‖))
  have h2 := (Matrix.posSemidef_conjTranspose_mul_self A).kronecker (right_gram_le_norm_sq B)
  have heq : (‖A‖ ^ 2 • (1 : Matrix J J ℂ) - Aᴴ * A) ⊗ₖ
      (‖B‖ ^ 2 • (1 : Matrix L L ℂ)) +
      (Aᴴ * A) ⊗ₖ (‖B‖ ^ 2 • (1 : Matrix L L ℂ) - Bᴴ * B) =
      (‖A‖ ^ 2 * ‖B‖ ^ 2) • (1 : Matrix (J × L) (J × L) ℂ) -
        (A ⊗ₖ B)ᴴ * (A ⊗ₖ B) := by
    rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
      ← Matrix.one_kronecker_one (m := J) (n := L)]
    ext x y
    simp only [Matrix.kroneckerMap_apply, Matrix.sub_apply, Matrix.add_apply,
      Matrix.smul_apply, Complex.real_smul, Complex.ofReal_mul]
    ring
  have hn := GlobalMatrixSplit.norm_sq_le_of_right_gram
    (mul_nonneg (sq_nonneg ‖A‖) (sq_nonneg ‖B‖)) (heq ▸ h1.add h2)
  have hp : 0 ≤ ‖A‖ * ‖B‖ := mul_nonneg (norm_nonneg A) (norm_nonneg B)
  nlinarith [norm_nonneg (A ⊗ₖ B)]

def tensorMatrix {k : ℕ} (M : Fin k → Matrix I J ℂ) :
    Matrix (Fin k → I) (Fin k → J) ℂ := fun x y => ∏ i, M i (x i) (y i)

omit [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] in
theorem tensorMatrix_succ_submatrix {k : ℕ} (M : Fin (k + 1) → Matrix I J ℂ) :
    (tensorMatrix M).submatrix (TensorPinching.rowsSuccEquiv I k).symm
      (TensorPinching.rowsSuccEquiv J k).symm =
      tensorMatrix (fun i => M i.castSucc) ⊗ₖ M (Fin.last k) := by
  ext x y
  simp [tensorMatrix, TensorPinching.rowsSuccEquiv, Fin.prod_univ_castSucc]

theorem tensorMatrix_norm_le {k : ℕ} (M : Fin k → Matrix I J ℂ) :
    ‖tensorMatrix M‖ ≤ ∏ i, ‖M i‖ := by
  induction k with
  | zero =>
      let e : Unit ≃ (Fin 0 → I) := Equiv.ofUnique _ _
      let f : Unit ≃ (Fin 0 → J) := Equiv.ofUnique _ _
      have heq : (tensorMatrix M).submatrix e f = (1 : Matrix Unit Unit ℂ) := by
        ext x y
        cases x
        cases y
        simp [tensorMatrix]
      calc
        _ = ‖(tensorMatrix M).submatrix e f‖ := (norm_submatrix_equiv _ e f).symm
        _ ≤ _ := by rw [heq]; simp
  | succ k ih =>
      calc
        _ = ‖(tensorMatrix M).submatrix (TensorPinching.rowsSuccEquiv I k).symm
          (TensorPinching.rowsSuccEquiv J k).symm‖ := (norm_submatrix_equiv _ _ _).symm
        _ = ‖tensorMatrix (fun i => M i.castSucc) ⊗ₖ M (Fin.last k)‖ := by
          rw [tensorMatrix_succ_submatrix]
        _ ≤ ‖tensorMatrix (fun i => M i.castSucc)‖ * ‖M (Fin.last k)‖ := norm_kronecker_le _ _
        _ ≤ (∏ i : Fin k, ‖M i.castSucc‖) * ‖M (Fin.last k)‖ :=
          mul_le_mul_of_nonneg_right (ih _) (norm_nonneg _)
        _ = _ := (Fin.prod_univ_castSucc (fun i : Fin (k + 1) => ‖M i‖)).symm

def word {k : ℕ} (X H : Matrix I J ℂ) (s : Finset (Fin k)) :
    Matrix (Fin k → I) (Fin k → J) ℂ :=
  tensorMatrix (fun i => if i ∈ s then H else X)

omit [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] in
theorem word_apply {k : ℕ} (X H : Matrix I J ℂ) (s : Finset (Fin k))
    (x : Fin k → I) (y : Fin k → J) :
    word X H s x y = (∏ i ∈ s, H (x i) (y i)) * ∏ i ∈ sᶜ, X (x i) (y i) := by
  unfold word tensorMatrix
  calc
    _ = ∏ i : Fin k, if i ∈ s then H (x i) (y i) else X (x i) (y i) := by
      apply Finset.prod_congr rfl
      intro i _
      by_cases hi : i ∈ s <;> simp [hi]
    _ = _ := by
      have hf : (Finset.univ : Finset (Fin k)).filter (fun i => i ∈ s) = s := by ext i; simp
      have hg : (Finset.univ : Finset (Fin k)).filter (fun i => i ∉ s) = sᶜ := by ext i; simp
      rw [Finset.prod_ite, hf, hg]

theorem word_norm_le {k : ℕ} (X H : Matrix I J ℂ) {a b : ℝ}
    (_ha : 0 ≤ a) (_hb : 0 ≤ b) (hX : ‖X‖ ≤ a) (hH : ‖H‖ ≤ b) (s : Finset (Fin k)) :
    ‖word X H s‖ ≤ b ^ s.card * a ^ (k - s.card) := by
  calc
    _ ≤ ∏ i : Fin k, ‖if i ∈ s then H else X‖ := tensorMatrix_norm_le _
    _ ≤ ∏ i : Fin k, if i ∈ s then b else a := by
      apply Finset.prod_le_prod₀
      · intro i _
        exact norm_nonneg _
      · intro i _
        by_cases hi : i ∈ s <;> simp only [hi, ite_true, ite_false]
        · exact hH
        · exact hX
    _ = _ := by
      rw [Finset.prod_ite]
      have hf : (Finset.univ : Finset (Fin k)).filter (fun i => i ∈ s) = s := by ext i; simp
      have hg : (Finset.univ : Finset (Fin k)).filter (fun i => i ∉ s) = sᶜ := by ext i; simp
      rw [hf, hg, Finset.prod_const, Finset.prod_const]
      simp [Finset.card_compl]

omit [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] in

theorem tensorMatrix_add_eq_sum_words (X H : Matrix I J ℂ) (k : ℕ) :
    tensorMatrix (fun _ : Fin k => X + H) = ∑ s : Finset (Fin k), word X H s := by
  ext x y
  simp only [tensorMatrix, Matrix.add_apply, Matrix.sum_apply]
  calc
    _ = ∏ i : Fin k, (H (x i) (y i) + X (x i) (y i)) := by
      apply Finset.prod_congr rfl
      intro i _
      exact add_comm _ _
    _ = ∑ s : Finset (Fin k), (∏ i ∈ s, H (x i) (y i)) * ∏ i ∈ sᶜ, X (x i) (y i) :=
      Fintype.prod_add _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro s _
      exact (word_apply X H s x y).symm

def retained (X H : Matrix I J ℂ) (k ell : ℕ) : Matrix (Fin k → I) (Fin k → J) ℂ :=
  ∑ s : Finset (Fin k) with s.card ≤ ell, word X H s

def omitted (X H : Matrix I J ℂ) (k ell : ℕ) : Matrix (Fin k → I) (Fin k → J) ℂ :=
  ∑ s : Finset (Fin k) with ¬s.card ≤ ell, word X H s

omit [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] in
theorem retained_add_omitted (X H : Matrix I J ℂ) (k ell : ℕ) :
    retained X H k ell + omitted X H k ell = tensorMatrix (fun _ : Fin k => X + H) := by
  rw [tensorMatrix_add_eq_sum_words]
  exact Finset.sum_filter_add_sum_filter_not _ _ _

omit [DecidableEq J] in
theorem tensorMatrix_of_singular_split {A Z : Matrix I I ℂ}
    (hA : A.PosSemidef) (hZ : Z.PosSemidef) (F : Matrix I J ℂ)
    (hF : (A + Z - F * Fᴴ).PosSemidef) (k ell : ℕ) :
    retained (GlobalMatrixSplit.columnPiece A (A + Z) F)
      (GlobalMatrixSplit.columnPiece Z (A + Z) F) k ell +
    omitted (GlobalMatrixSplit.columnPiece A (A + Z) F)
      (GlobalMatrixSplit.columnPiece Z (A + Z) F) k ell = tensorMatrix (fun _ : Fin k => F) := by
  rw [retained_add_omitted, (GlobalMatrixSplit.singular_positive_column_split hA hZ F hF).1]

end QuantumProver.SuperchannelDiscrimination.TensorWordTruncation

namespace QuantumProver.SuperchannelDiscrimination.TensorWordTruncation

variable {I J K : Type*} [Fintype I] [Fintype J] [Fintype K]
  [DecidableEq I] [DecidableEq J] [DecidableEq K]

theorem sum_subsets_by_card (k : ℕ) (f : ℕ → ℝ) :
    (∑ s : Finset (Fin k), f s.card) =
      ∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) * f j := by
  change (∑ s ∈ (Finset.univ : Finset (Fin k)).powerset, f s.card) = _
  rw [Finset.sum_powerset]
  simp only [Finset.sum_powersetCard, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

theorem retained_norm_le_binomial (X H : Matrix I J ℂ) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hX : ‖X‖ ≤ a) (hH : ‖H‖ ≤ b) (k ell : ℕ) :
    ‖retained X H k ell‖ ≤
      ∑ j ∈ (Finset.range (k + 1)).filter (fun j => j ≤ ell),
        (k.choose j : ℝ) * b ^ j * a ^ (k - j) := by
  calc
    _ ≤ ∑ s : Finset (Fin k) with s.card ≤ ell, ‖word X H s‖ := norm_sum_le _ _
    _ ≤ ∑ s : Finset (Fin k) with s.card ≤ ell,
        b ^ s.card * a ^ (k - s.card) := by
      apply Finset.sum_le_sum
      intro s _
      exact word_norm_le X H ha hb hX hH s
    _ = _ := by
      rw [Finset.sum_filter, sum_subsets_by_card k
        (fun j => if j ≤ ell then b ^ j * a ^ (k - j) else 0)]
      simp only [mul_ite, mul_zero, Finset.sum_filter, mul_assoc]

theorem omitted_norm_le_binomial (X H : Matrix I J ℂ) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hX : ‖X‖ ≤ a) (hH : ‖H‖ ≤ b) (k ell : ℕ) :
    ‖omitted X H k ell‖ ≤
      ∑ j ∈ (Finset.range (k + 1)).filter (fun j => ¬j ≤ ell),
        (k.choose j : ℝ) * b ^ j * a ^ (k - j) := by
  calc
    _ ≤ ∑ s : Finset (Fin k) with ¬s.card ≤ ell, ‖word X H s‖ := norm_sum_le _ _
    _ ≤ ∑ s : Finset (Fin k) with ¬s.card ≤ ell,
        b ^ s.card * a ^ (k - s.card) := by
      apply Finset.sum_le_sum
      intro s _
      exact word_norm_le X H ha hb hX hH s
    _ = _ := by
      rw [Finset.sum_filter, sum_subsets_by_card k
        (fun j => if ¬j ≤ ell then b ^ j * a ^ (k - j) else 0)]
      simp only [mul_ite, mul_zero, Finset.sum_filter, mul_assoc]

theorem omitted_norm_le_generating (X H : Matrix I J ℂ) {a b z : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hz : 1 ≤ z)
    (hX : ‖X‖ ≤ a) (hH : ‖H‖ ≤ b) (k ell : ℕ) :
    ‖omitted X H k ell‖ ≤ (z ^ (ell + 1))⁻¹ * (a + z * b) ^ k := by
  have hz0 : 0 < z := lt_of_lt_of_le zero_lt_one hz
  have hd : 0 < z ^ (ell + 1) := pow_pos hz0 _
  have hp (s : Finset (Fin k)) (hs : ¬s.card ≤ ell) :
      b ^ s.card * a ^ (k - s.card) ≤
        (z ^ (ell + 1))⁻¹ * ((z * b) ^ s.card * a ^ (k - s.card)) := by
    have hj : ell + 1 ≤ s.card := by omega
    rw [mul_comm (z ^ (ell + 1))⁻¹, ← div_eq_mul_inv, le_div_iff₀ hd]
    calc
      _ = z ^ (ell + 1) * (b ^ s.card * a ^ (k - s.card)) := mul_comm _ _
      _ ≤ z ^ s.card * (b ^ s.card * a ^ (k - s.card)) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hz hj)
          (mul_nonneg (pow_nonneg hb _) (pow_nonneg ha _))
      _ = _ := by rw [mul_pow]; ring
  have hsum :
      (∑ s : Finset (Fin k) with ¬s.card ≤ ell,
        (z * b) ^ s.card * a ^ (k - s.card)) ≤ (a + z * b) ^ k := by
    calc
      _ ≤ ∑ s : Finset (Fin k), (z * b) ^ s.card * a ^ (k - s.card) := by
        rw [Finset.sum_filter]
        apply Finset.sum_le_sum
        intro s _
        by_cases hs : ¬s.card ≤ ell
        · simpa only [ite_eq_left hs] using le_refl ((z * b) ^ s.card * a ^ (k - s.card))
        · simpa only [hs, ite_false] using
            mul_nonneg (pow_nonneg (mul_nonneg hz0.le hb) s.card) (pow_nonneg ha (k - s.card))
      _ = _ := by
        simpa only [Fintype.card_fin, add_comm] using
          Fintype.sum_pow_mul_eq_add_pow (Fin k) (z * b) a
  calc
    _ ≤ ∑ s : Finset (Fin k) with ¬s.card ≤ ell, ‖word X H s‖ := norm_sum_le _ _
    _ ≤ ∑ s : Finset (Fin k) with ¬s.card ≤ ell,
        (z ^ (ell + 1))⁻¹ * ((z * b) ^ s.card * a ^ (k - s.card)) := by
      apply Finset.sum_le_sum
      intro s hs
      exact (word_norm_le X H ha hb hX hH s).trans (hp s (Finset.mem_filter.mp hs).2)
    _ = (z ^ (ell + 1))⁻¹ *
        ∑ s : Finset (Fin k) with ¬s.card ≤ ell,
          (z * b) ^ s.card * a ^ (k - s.card) := (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hd.le)

theorem omitted_norm_le_real_cutoff (X H : Matrix I J ℂ) {a b z theta : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hz : 1 ≤ z)
    (hX : ‖X‖ ≤ a) (hH : ‖H‖ ≤ b) (k ell : ℕ)
    (hcut : theta ≤ ((ell + 1 : ℕ) : ℝ)) :
    ‖omitted X H k ell‖ ≤ z ^ (-theta) * (a + z * b) ^ k := by
  have hz0 : 0 < z := lt_of_lt_of_le zero_lt_one hz
  refine (omitted_norm_le_generating X H ha hb hz hX hH k ell).trans ?_
  apply mul_le_mul_of_nonneg_right _
    (pow_nonneg (add_nonneg ha (mul_nonneg hz0.le hb)) _)
  calc
    (z ^ (ell + 1))⁻¹ = z ^ (-((ell + 1 : ℕ) : ℝ)) := by
      rw [Real.rpow_neg hz0.le, Real.rpow_natCast]
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hz (neg_le_neg hcut)

theorem omitted_norm_le_floor_cutoff (X H : Matrix I J ℂ) {a b z theta : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hz : 1 ≤ z)
    (hX : ‖X‖ ≤ a) (hH : ‖H‖ ≤ b) (k : ℕ) :
    ‖omitted X H k ⌊theta⌋₊‖ ≤ z ^ (-theta) * (a + z * b) ^ k := by
  apply omitted_norm_le_real_cutoff X H ha hb hz hX hH
  exact le_of_lt (by simpa only [Nat.cast_add, Nat.cast_one] using Nat.lt_floor_add_one theta)

theorem retained_norm_le_environment_scale (X H : Matrix I J ℂ) {u w theta : ℝ}
    (hu : 0 < u) (huw : u ≤ w) (hX : ‖X‖ ≤ u) (hH : ‖H‖ ≤ 2 * w)
    (k ell : ℕ) (hcut : (ell : ℝ) ≤ theta) :
    ‖retained X H k ell‖ ≤ (3 : ℝ) ^ k * u ^ k * (w / u) ^ theta := by
  have hw : 0 ≤ w := hu.le.trans huw
  have hr : 1 ≤ w / u := (one_le_div hu).mpr huw
  have hp (s : Finset (Fin k)) (hs : s.card ≤ ell) :
      (2 * w) ^ s.card * u ^ (k - s.card) ≤
        (u ^ k * (w / u) ^ theta) * (2 : ℝ) ^ s.card := by
    have hjk : s.card ≤ k := by simpa only [Fintype.card_fin] using s.card_le_univ
    have hjtheta : (s.card : ℝ) ≤ theta := (Nat.cast_le.mpr hs).trans hcut
    have hw' : w = (w / u) * u := (div_mul_cancel₀ w hu.ne').symm
    have heq : (2 * w) ^ s.card * u ^ (k - s.card) =
        (u ^ k * (w / u) ^ s.card) * (2 : ℝ) ^ s.card := by
      calc
        _ = (2 * ((w / u) * u)) ^ s.card * u ^ (k - s.card) := by rw [← hw']
        _ = (2 : ℝ) ^ s.card * (w / u) ^ s.card *
            (u ^ s.card * u ^ (k - s.card)) := by simp only [mul_pow]; ring
        _ = _ := by rw [← pow_add, Nat.add_sub_of_le hjk]; ring
    rw [heq]
    have hpow : (w / u) ^ s.card ≤ (w / u) ^ theta := by
      simpa only [Real.rpow_natCast] using
        Real.rpow_le_rpow_of_exponent_le hr hjtheta
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hpow (pow_nonneg hu.le _)) (pow_nonneg (by norm_num) _)
  have hsum : (∑ s : Finset (Fin k) with s.card ≤ ell, (2 : ℝ) ^ s.card) ≤ (3 : ℝ) ^ k := by
    calc
      _ ≤ ∑ s : Finset (Fin k), (2 : ℝ) ^ s.card := by
        rw [Finset.sum_filter]
        apply Finset.sum_le_sum
        intro s _
        by_cases hs : s.card ≤ ell
        · simpa only [ite_eq_left hs] using le_refl ((2 : ℝ) ^ s.card)
        · simpa only [hs, ite_false] using pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) s.card
      _ = _ := by
        have h := Fintype.sum_pow_mul_eq_add_pow (Fin k) (2 : ℝ) 1
        norm_num only [Fintype.card_fin, one_pow, mul_one] at h
        exact h
  calc
    _ ≤ ∑ s : Finset (Fin k) with s.card ≤ ell, ‖word X H s‖ := norm_sum_le _ _
    _ ≤ ∑ s : Finset (Fin k) with s.card ≤ ell,
        (u ^ k * (w / u) ^ theta) * (2 : ℝ) ^ s.card := by
      apply Finset.sum_le_sum
      intro s hs
      exact (word_norm_le X H hu.le (mul_nonneg (by norm_num) hw) hX hH s).trans
        (hp s (Finset.mem_filter.mp hs).2)
    _ = (u ^ k * (w / u) ^ theta) *
        ∑ s : Finset (Fin k) with s.card ≤ ell, (2 : ℝ) ^ s.card := (Finset.mul_sum _ _ _).symm
    _ ≤ (u ^ k * (w / u) ^ theta) * (3 : ℝ) ^ k :=
      mul_le_mul_of_nonneg_left hsum
        (mul_nonneg (pow_nonneg hu.le _) (Real.rpow_nonneg (div_nonneg hw hu.le) _))
    _ = _ := by ring

theorem dyadic_environment_scale (m k : ℕ) (r S beta : ℝ) :
    ((2 : ℝ) ^ ((m : ℝ) * r / 2)) ^ k *
      (((2 : ℝ) ^ ((m : ℝ) * S / 2)) /
        ((2 : ℝ) ^ ((m : ℝ) * r / 2))) ^ (beta * k) =
      (2 : ℝ) ^ ((m : ℝ) * k * ((1 - beta) * r + beta * S) / 2) := by
  rw [← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2),
    ← Real.rpow_sub (by norm_num : (0 : ℝ) < 2),
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
    ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  congr 1
  ring

theorem retained_norm_le_dyadic_scale (X H : Matrix I J ℂ) (m k : ℕ)
    {r S beta : ℝ} (hrS : r ≤ S) (hbeta : 0 ≤ beta)
    (hX : ‖X‖ ≤ (2 : ℝ) ^ ((m : ℝ) * r / 2))
    (hH : ‖H‖ ≤ 2 * (2 : ℝ) ^ ((m : ℝ) * S / 2)) :
    ‖retained X H k ⌊beta * k⌋₊‖ ≤
      (3 : ℝ) ^ k * (2 : ℝ) ^ ((m : ℝ) * k * ((1 - beta) * r + beta * S) / 2) := by
  have hu : 0 < (2 : ℝ) ^ ((m : ℝ) * r / 2) := Real.rpow_pos_of_pos (by norm_num) _
  have huw : (2 : ℝ) ^ ((m : ℝ) * r / 2) ≤ (2 : ℝ) ^ ((m : ℝ) * S / 2) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    nlinarith [show (0 : ℝ) ≤ (m : ℝ) from Nat.cast_nonneg m]
  have hcut : (⌊beta * k⌋₊ : ℝ) ≤ beta * k :=
    Nat.floor_le (mul_nonneg hbeta (Nat.cast_nonneg k))
  refine (retained_norm_le_environment_scale X H hu huw hX hH k _ hcut).trans_eq ?_
  rw [mul_assoc, dyadic_environment_scale]

theorem right_gram_le_of_norm_le (D : Matrix I J ℂ) {c : ℝ}
    (hc : 0 ≤ c) (hD : ‖D‖ ≤ c) : (c ^ 2 • (1 : Matrix J J ℂ) - Dᴴ * D).PosSemidef := by
  have hdiff : 0 ≤ c ^ 2 - ‖D‖ ^ 2 := by nlinarith [norm_nonneg D]
  have hp := (Matrix.PosSemidef.one.smul hdiff).add (right_gram_le_norm_sq D)
  convert hp using 1
  module

def contractRetained (X H : Matrix I J ℂ) (k ell : ℕ) (bound : ℝ) :
    Matrix (Fin k → I) (Fin k → J) ℂ :=
  (max 1 bound)⁻¹ • retained X H k ell

omit [DecidableEq I] in
theorem contractRetained_norm_le_one (X H : Matrix I J ℂ) (k ell : ℕ) (bound : ℝ)
    (hbound : ‖retained X H k ell‖ ≤ bound) : ‖contractRetained X H k ell bound‖ ≤ 1 := by
  have hm : 0 < max 1 bound := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  unfold contractRetained
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hm), mul_comm, ← div_eq_mul_inv,
    div_le_one hm]
  exact hbound.trans (le_max_right _ _)

theorem contractRetained_right_gram (X H : Matrix I J ℂ) (k ell : ℕ) (bound : ℝ)
    (hbound : ‖retained X H k ell‖ ≤ bound) :
    (1 - (contractRetained X H k ell bound)ᴴ * contractRetained X H k ell bound).PosSemidef := by
  simpa only [one_pow, one_smul] using right_gram_le_of_norm_le
    (contractRetained X H k ell bound) (by norm_num : (0 : ℝ) ≤ 1)
      (contractRetained_norm_le_one X H k ell bound hbound)

omit [DecidableEq I] [DecidableEq K] in

theorem choi_column_cap_of_right_gram (B : Matrix K J ℂ) (D : Matrix I J ℂ) (c : ℝ)
    (hc : (c • (1 : Matrix J J ℂ) - Dᴴ * D).PosSemidef) :
    (c • (B * Bᴴ) - (B * Dᵀ) * (B * Dᵀ)ᴴ).PosSemidef := by
  have ht : (c • (1 : Matrix J J ℂ) - Dᵀ * Dᵀᴴ).PosSemidef := by
    simpa only [Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_one,
      Matrix.transpose_mul, Matrix.conjTranspose_transpose_eq_transpose_conjTranspose] using hc.transpose
  have h := ht.mul_mul_conjTranspose_same B
  simpa only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_one, Matrix.conjTranspose_mul, Matrix.mul_assoc] using h

theorem columnPiece_norm_le_of_cap {A Z : Matrix I I ℂ}
    (hA : A.PosSemidef) (hZ : Z.PosSemidef) (F : Matrix I J ℂ)
    (hF : (A + Z - F * Fᴴ).PosSemidef) {a : ℝ} (ha : 0 ≤ a)
    (hcap : (a ^ 2 • (1 : Matrix I I ℂ) - A).PosSemidef) :
    ‖GlobalMatrixSplit.columnPiece A (A + Z) F‖ ≤ a := by
  have h0 := (GlobalMatrixSplit.singular_positive_column_split hA hZ F hF).2.1
  have hgram : (a ^ 2 • (1 : Matrix I I ℂ) -
      GlobalMatrixSplit.columnPiece A (A + Z) F *
        (GlobalMatrixSplit.columnPiece A (A + Z) F)ᴴ).PosSemidef := by
    convert hcap.add h0 using 1
    abel
  have hn := GlobalMatrixSplit.norm_sq_le_of_left_gram (sq_nonneg a) hgram
  nlinarith [norm_nonneg (GlobalMatrixSplit.columnPiece A (A + Z) F)]

theorem singular_split_tensor_tail {A Z : Matrix I I ℂ}
    (hA : A.PosSemidef) (hZ : Z.PosSemidef) (F : Matrix I J ℂ)
    (hF : (A + Z - F * Fᴴ).PosSemidef) {a b z : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hz : 1 ≤ z)
    (hAcap : (a ^ 2 • (1 : Matrix I I ℂ) - A).PosSemidef)
    (hZcap : (b ^ 2 • (1 : Matrix I I ℂ) - Z).PosSemidef) (k ell : ℕ) :
    retained (GlobalMatrixSplit.columnPiece A (A + Z) F)
        (GlobalMatrixSplit.columnPiece Z (A + Z) F) k ell +
      omitted (GlobalMatrixSplit.columnPiece A (A + Z) F)
        (GlobalMatrixSplit.columnPiece Z (A + Z) F) k ell = tensorMatrix (fun _ : Fin k => F) ∧
    ‖omitted (GlobalMatrixSplit.columnPiece A (A + Z) F)
        (GlobalMatrixSplit.columnPiece Z (A + Z) F) k ell‖ ≤
      (z ^ (ell + 1))⁻¹ * (a + z * b) ^ k := by
  refine ⟨tensorMatrix_of_singular_split hA hZ F hF k ell, ?_⟩
  have hX := columnPiece_norm_le_of_cap hA hZ F hF ha hAcap
  have hswap : (Z + A - F * Fᴴ).PosSemidef := by simpa only [add_comm Z A] using hF
  have hH := columnPiece_norm_le_of_cap hZ hA F hswap hb hZcap
  have hH' : ‖GlobalMatrixSplit.columnPiece Z (A + Z) F‖ ≤ b := by
    simpa only [add_comm Z A] using hH
  exact omitted_norm_le_generating _ _ ha hb hz hX hH' k ell

end QuantumProver.SuperchannelDiscrimination.TensorWordTruncation

namespace QuantumProver.SuperchannelDiscrimination.TensorWordTruncation

variable {I J K : Type*} [Fintype I] [Fintype J] [Fintype K]
  [DecidableEq I] [DecidableEq J] [DecidableEq K]

omit [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] in
theorem tensorMatrix_transpose {k : ℕ} (M : Fin k → Matrix I J ℂ) :
    tensorMatrix (fun i => (M i)ᵀ) = (tensorMatrix M)ᵀ := rfl

omit [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] in
theorem tensorMatrix_conjTranspose {k : ℕ} (M : Fin k → Matrix I J ℂ) :
    tensorMatrix (fun i => (M i)ᴴ) = (tensorMatrix M)ᴴ := by
  ext x y
  simp [tensorMatrix, Matrix.conjTranspose_apply]

omit [Fintype I] [Fintype K] [DecidableEq I] [DecidableEq J] [DecidableEq K] in
theorem tensorMatrix_mul {k : ℕ} (M : Fin k → Matrix I J ℂ) (N : Fin k → Matrix J K ℂ) :
    tensorMatrix (fun i => M i * N i) = tensorMatrix M * tensorMatrix N := by
  classical
  ext x y
  simp only [tensorMatrix, Matrix.mul_apply]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro z _
  exact Finset.prod_mul_distrib

theorem tensorMatrix_const_norm_le_one (F : Matrix I J ℂ) (hF : ‖F‖ ≤ 1) (k : ℕ) :
    ‖tensorMatrix (fun _ : Fin k => F)‖ ≤ 1 := by
  calc
    _ ≤ ∏ _ : Fin k, ‖F‖ := tensorMatrix_norm_le _
    _ ≤ ∏ _ : Fin k, (1 : ℝ) :=
      Finset.prod_le_prod₀ (fun _ _ => norm_nonneg F) (fun _ _ => hF)
    _ = _ := by simp

omit [DecidableEq I] in
theorem retained_norm_le_one_add_error (X H : Matrix I J ℂ) (k ell : ℕ) {delta : ℝ}
    (htotal : ‖tensorMatrix (fun _ : Fin k => X + H)‖ ≤ 1)
    (homitted : ‖omitted X H k ell‖ ≤ delta) : ‖retained X H k ell‖ ≤ 1 + delta := by
  have heq : retained X H k ell =
      tensorMatrix (fun _ : Fin k => X + H) - omitted X H k ell :=
    eq_sub_iff_add_eq.mpr (retained_add_omitted X H k ell)
  rw [heq]
  exact (norm_sub_le _ _).trans (add_le_add htotal homitted)

def attenuatedRetained (X H : Matrix I J ℂ) (k ell : ℕ) (delta : ℝ) :
    Matrix (Fin k → I) (Fin k → J) ℂ := (1 + delta)⁻¹ • retained X H k ell

omit [DecidableEq I] in
theorem attenuatedRetained_norm_le_bound (X H : Matrix I J ℂ) (k ell : ℕ)
    {delta bound : ℝ} (hdelta : 0 ≤ delta) (hbound : ‖retained X H k ell‖ ≤ bound) :
    ‖attenuatedRetained X H k ell delta‖ ≤ bound / (1 + delta) := by
  have h1 : 0 < 1 + delta := by linarith
  unfold attenuatedRetained
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr h1), div_eq_mul_inv]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left hbound (inv_nonneg.mpr h1.le)

omit [DecidableEq I] in
theorem attenuatedRetained_norm_le_one (X H : Matrix I J ℂ) (k ell : ℕ) {delta : ℝ}
    (hdelta : 0 ≤ delta) (htotal : ‖tensorMatrix (fun _ : Fin k => X + H)‖ ≤ 1)
    (homitted : ‖omitted X H k ell‖ ≤ delta) : ‖attenuatedRetained X H k ell delta‖ ≤ 1 := by
  have h1 : 0 < 1 + delta := by linarith
  simpa only [div_self h1.ne'] using attenuatedRetained_norm_le_bound X H k ell hdelta
    (retained_norm_le_one_add_error X H k ell htotal homitted)

omit [DecidableEq I] in
theorem attenuatedRetained_disturbance (X H : Matrix I J ℂ) (k ell : ℕ) {delta : ℝ}
    (hdelta : 0 ≤ delta) (htotal : ‖tensorMatrix (fun _ : Fin k => X + H)‖ ≤ 1)
    (homitted : ‖omitted X H k ell‖ ≤ delta) :
    ‖attenuatedRetained X H k ell delta - tensorMatrix (fun _ : Fin k => X + H)‖ ≤ 2 * delta := by
  have h1 : 0 < 1 + delta := by linarith
  have hdiv : 0 ≤ delta / (1 + delta) := div_nonneg hdelta h1.le
  have hs : (1 + delta)⁻¹ - 1 = -(delta / (1 + delta)) := by field_simp [h1.ne']; ring
  have hterm : ‖((1 + delta)⁻¹ - 1) • retained X H k ell‖ ≤ delta := by
    calc
      _ = (delta / (1 + delta)) * ‖retained X H k ell‖ := by
        rw [hs, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg hdiv]
      _ ≤ (delta / (1 + delta)) * (1 + delta) :=
        mul_le_mul_of_nonneg_left (retained_norm_le_one_add_error X H k ell htotal homitted) hdiv
      _ = _ := div_mul_cancel₀ delta h1.ne'
  have heq : attenuatedRetained X H k ell delta - tensorMatrix (fun _ : Fin k => X + H) =
      ((1 + delta)⁻¹ - 1) • retained X H k ell - omitted X H k ell := by
    rw [← retained_add_omitted X H k ell]
    unfold attenuatedRetained
    module
  rw [heq]
  calc
    _ ≤ ‖((1 + delta)⁻¹ - 1) • retained X H k ell‖ + ‖omitted X H k ell‖ := norm_sub_le _ _
    _ ≤ delta + delta := add_le_add hterm homitted
    _ = _ := by ring

theorem attenuatedRetained_right_gram (X H : Matrix I J ℂ) (k ell : ℕ) {delta : ℝ}
    (hdelta : 0 ≤ delta) (htotal : ‖tensorMatrix (fun _ : Fin k => X + H)‖ ≤ 1)
    (homitted : ‖omitted X H k ell‖ ≤ delta) :
    (1 - (attenuatedRetained X H k ell delta)ᴴ * attenuatedRetained X H k ell delta).PosSemidef := by
  simpa only [one_pow, one_smul] using right_gram_le_of_norm_le
    (attenuatedRetained X H k ell delta) (by norm_num : (0 : ℝ) ≤ 1)
      (attenuatedRetained_norm_le_one X H k ell hdelta htotal homitted)

omit [DecidableEq K] in
theorem attenuatedRetained_choi_column_cap (k ell : ℕ) (B : Matrix K (Fin k → J) ℂ)
    (X H : Matrix I J ℂ) {delta bound : ℝ}
    (hdelta : 0 ≤ delta) (hbound : 0 ≤ bound) (hnorm : ‖retained X H k ell‖ ≤ bound) :
    ((bound / (1 + delta)) ^ 2 • (B * Bᴴ) -
      (B * (attenuatedRetained X H k ell delta)ᵀ) *
        (B * (attenuatedRetained X H k ell delta)ᵀ)ᴴ).PosSemidef := by
  have h1 : 0 < 1 + delta := by linarith
  exact choi_column_cap_of_right_gram B _ _ (right_gram_le_of_norm_le _
    (div_nonneg hbound h1.le) (attenuatedRetained_norm_le_bound X H k ell hdelta hnorm))

end QuantumProver.SuperchannelDiscrimination.TensorWordTruncation

namespace QuantumProver.SuperchannelDiscrimination.TensorWordTruncation

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

theorem omitted_norm_le_geometric (X H : Matrix I J ℂ) {a b z beta : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hz : 1 ≤ z)
    (hX : ‖X‖ ≤ a) (hH : ‖H‖ ≤ b) (k : ℕ) :
    ‖omitted X H k ⌊beta * k⌋₊‖ ≤ (z ^ (-beta) * (a + z * b)) ^ k := by
  have hz0 : 0 < z := lt_of_lt_of_le zero_lt_one hz
  refine (omitted_norm_le_floor_cutoff X H ha hb hz hX hH k).trans_eq ?_
  rw [show -(beta * (k : ℝ)) = (-beta) * (k : ℝ) by ring,
    Real.rpow_mul_natCast hz0.le, ← mul_pow]

end QuantumProver.SuperchannelDiscrimination.TensorWordTruncation

namespace QuantumProver.SuperchannelDiscrimination.TensorWordTruncation

variable {I J K : Type*} [Fintype I] [Fintype J] [Fintype K]
  [DecidableEq I] [DecidableEq J] [DecidableEq K]

omit [Fintype I] [Fintype K] [DecidableEq I] [DecidableEq J] [DecidableEq K] in
theorem word_right_factor {k : ℕ} (B : Matrix K J ℂ) (X H : Matrix I J ℂ)
    (s : Finset (Fin k)) :
    word (B * Xᵀ) (B * Hᵀ) s =
      tensorMatrix (fun _ : Fin k => B) * (word X H s)ᵀ := by
  unfold word
  rw [← tensorMatrix_transpose, ← tensorMatrix_mul]
  apply congrArg tensorMatrix
  funext i
  by_cases hi : i ∈ s <;> simp [hi]

omit [Fintype I] [Fintype K] [DecidableEq I] [DecidableEq J] [DecidableEq K] in
theorem retained_right_factor (B : Matrix K J ℂ) (X H : Matrix I J ℂ) (k ell : ℕ) :
    retained (B * Xᵀ) (B * Hᵀ) k ell =
      tensorMatrix (fun _ : Fin k => B) * (retained X H k ell)ᵀ := by
  unfold retained
  simp_rw [word_right_factor]
  rw [← Matrix.mul_sum, ← Matrix.transpose_sum]

omit [Fintype I] [Fintype K] [DecidableEq I] [DecidableEq J] [DecidableEq K] in
theorem omitted_right_factor (B : Matrix K J ℂ) (X H : Matrix I J ℂ) (k ell : ℕ) :
    omitted (B * Xᵀ) (B * Hᵀ) k ell =
      tensorMatrix (fun _ : Fin k => B) * (omitted X H k ell)ᵀ := by
  unfold omitted
  simp_rw [word_right_factor]
  rw [← Matrix.mul_sum, ← Matrix.transpose_sum]

end QuantumProver.SuperchannelDiscrimination.TensorWordTruncation

namespace QuantumProver.SuperchannelDiscrimination.TensorWordTruncation

variable {I E F : Type*} [Fintype I] [Fintype E] [Fintype F]
  [DecidableEq I] [DecidableEq F]

theorem exists_constructed_environmental_good_bad (B : Matrix I F ℂ) (K : Matrix I E ℂ)
    {Z : Matrix I I ℂ} (hZ : Z.PosSemidef) {u w : ℝ}
    (hu : 0 ≤ u) (huw : u ≤ w)
    (hwhole : (w ^ 2 • (B * Bᴴ) - K * Kᴴ).PosSemidef)
    (hdual : (u ^ 2 • (B * Bᴴ) + Z - K * Kᴴ).PosSemidef) :
    ∃ C H : Matrix E F ℂ,
      C + H = (GlobalMatrixSplit.douglasFactor B K)ᵀ ∧
      B * (C + H)ᵀ = K ∧
      (u ^ 2 • (1 : Matrix F F ℂ) - Cᴴ * C).PosSemidef ∧
      ‖C‖ ≤ u ∧ ‖H‖ ≤ 2 * w ∧
      B * Hᵀ = K - B * Cᵀ ∧
      (Z - (B * Hᵀ) * (B * Hᵀ)ᴴ).PosSemidef := by
  let D := (GlobalMatrixSplit.douglasFactor B K)ᵀ
  have hw : 0 ≤ w := hu.trans huw
  have hDrec : B * Dᵀ = K := by
    simpa only [D, Matrix.transpose_transpose] using
      GlobalMatrixSplit.douglasFactor_reconstruct B K (w ^ 2) hwhole
  have hDsq : ‖D‖ ^ 2 ≤ w ^ 2 :=
    GlobalMatrixSplit.environmentalFactor_norm_sq_le B K (w ^ 2) (sq_nonneg w) hwhole
  have hDn : ‖D‖ ≤ w := by nlinarith [norm_nonneg D]
  obtain ⟨C, hCcap, hCsq, hres⟩ :=
    GlobalMatrixSplit.exists_global_environmental_split B K hZ (u ^ 2) (sq_nonneg u) hdual
  let H := D - C
  have hCn : ‖C‖ ≤ u := by nlinarith [norm_nonneg C]
  have hHn : ‖H‖ ≤ 2 * w := by
    calc
      _ ≤ ‖D‖ + ‖C‖ := norm_sub_le _ _
      _ ≤ w + u := add_le_add hDn hCn
      _ ≤ _ := by linarith
  have hsum : C + H = D := by dsimp [H]; abel
  have hbad : B * Hᵀ = K - B * Cᵀ := by
    dsimp [H]
    rw [Matrix.transpose_sub, Matrix.mul_sub, hDrec]
  refine ⟨C, H, hsum, ?_, hCcap, hCn, hHn, hbad, ?_⟩
  · rw [hsum, hDrec]
  · simpa only [hbad] using hres

end QuantumProver.SuperchannelDiscrimination.TensorWordTruncation

namespace QuantumProver.SuperchannelDiscrimination.TensorWordTruncation

def epsilonTailBase (epsilon beta : ℝ) : ℝ :=
  epsilon ^ (beta / 2) * (1 + epsilon + Real.sqrt epsilon)

theorem epsilonTailBase_nonneg {epsilon : ℝ} (hepsilon : 0 ≤ epsilon) (beta : ℝ) :
    0 ≤ epsilonTailBase epsilon beta := by
  unfold epsilonTailBase
  exact mul_nonneg (Real.rpow_nonneg hepsilon _) (by positivity)

theorem epsilon_generating_base {epsilon : ℝ} (hepsilon : 0 < epsilon) (beta : ℝ) :
    (epsilon ^ (-(1 / 2 : ℝ))) ^ (-beta) *
      (1 + epsilon + epsilon ^ (-(1 / 2 : ℝ)) * epsilon) =
        epsilonTailBase epsilon beta := by
  have hfirst : (epsilon ^ (-(1 / 2 : ℝ))) ^ (-beta) = epsilon ^ (beta / 2) := by
    rw [← Real.rpow_mul hepsilon.le]
    congr 1
    ring
  have hsecond : epsilon ^ (-(1 / 2 : ℝ)) * epsilon = Real.sqrt epsilon := by
    calc
      _ = epsilon ^ (-(1 / 2 : ℝ)) * epsilon ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = epsilon ^ (-(1 / 2 : ℝ) + 1) := (Real.rpow_add hepsilon _ _).symm
      _ = epsilon ^ (1 / 2 : ℝ) := by congr 1; ring
      _ = _ := (Real.sqrt_eq_rpow epsilon).symm
  rw [hfirst, hsecond]
  rfl

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

omit [DecidableEq I] in
theorem good_norm_of_total_and_bad (X H : Matrix I J ℂ) {epsilon : ℝ}
    (htotal : ‖X + H‖ ≤ 1) (hbad : ‖H‖ ≤ epsilon) : ‖X‖ ≤ 1 + epsilon := by
  have heq : X = (X + H) - H := by abel
  rw [heq]
  exact (norm_sub_le _ _).trans (add_le_add htotal hbad)

theorem physical_omitted_le_epsilon_base (X H : Matrix I J ℂ) {epsilon : ℝ}
    (hepsilon : 0 < epsilon) (hepsilon_one : epsilon ≤ 1)
    (htotal : ‖X + H‖ ≤ 1) (hbad : ‖H‖ ≤ epsilon) (beta : ℝ) (k : ℕ) :
    ‖omitted X H k ⌊beta * k⌋₊‖ ≤ (epsilonTailBase epsilon beta) ^ k := by
  have hz : 1 ≤ epsilon ^ (-(1 / 2 : ℝ)) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hepsilon hepsilon_one (by norm_num)
  simpa only [epsilon_generating_base hepsilon beta] using
    omitted_norm_le_geometric X H (beta := beta) (by linarith : 0 ≤ 1 + epsilon) hepsilon.le hz
      (good_norm_of_total_and_bad X H htotal hbad) hbad k

theorem physical_attenuation_norm_le_one (X H : Matrix I J ℂ) {epsilon : ℝ}
    (hepsilon : 0 < epsilon) (hepsilon_one : epsilon ≤ 1)
    (htotal : ‖X + H‖ ≤ 1) (hbad : ‖H‖ ≤ epsilon) (beta : ℝ) (k : ℕ) :
    ‖attenuatedRetained X H k ⌊beta * k⌋₊ ((epsilonTailBase epsilon beta) ^ k)‖ ≤ 1 := by
  exact attenuatedRetained_norm_le_one X H k _
    (pow_nonneg (epsilonTailBase_nonneg hepsilon.le beta) k)
    (tensorMatrix_const_norm_le_one _ htotal k)
    (physical_omitted_le_epsilon_base X H hepsilon hepsilon_one htotal hbad beta k)

theorem physical_attenuation_disturbance (X H : Matrix I J ℂ) {epsilon : ℝ}
    (hepsilon : 0 < epsilon) (hepsilon_one : epsilon ≤ 1)
    (htotal : ‖X + H‖ ≤ 1) (hbad : ‖H‖ ≤ epsilon) (beta : ℝ) (k : ℕ) :
    ‖attenuatedRetained X H k ⌊beta * k⌋₊ ((epsilonTailBase epsilon beta) ^ k) -
      tensorMatrix (fun _ : Fin k => X + H)‖ ≤ 2 * (epsilonTailBase epsilon beta) ^ k := by
  exact attenuatedRetained_disturbance X H k _
    (pow_nonneg (epsilonTailBase_nonneg hepsilon.le beta) k)
    (tensorMatrix_const_norm_le_one _ htotal k)
    (physical_omitted_le_epsilon_base X H hepsilon hepsilon_one htotal hbad beta k)

omit [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] in
theorem exists_epsilon_threshold {beta : ℝ} (hbeta : 0 < beta) :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 ∧
      ∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ epsilon0 → epsilonTailBase epsilon beta < 1 := by
  let epsilon0 : ℝ := (1 / 4 : ℝ) ^ (2 / beta)
  have h0 : 0 < epsilon0 := Real.rpow_pos_of_pos (by norm_num) _
  have h01 : epsilon0 ≤ 1 :=
    Real.rpow_le_one (by norm_num) (by norm_num) (by positivity)
  have hcancel : (2 / beta) * (beta / 2) = (1 : ℝ) := by field_simp
  have hp0 : epsilon0 ^ (beta / 2) = (1 / 4 : ℝ) := by
    dsimp [epsilon0]
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 1 / 4), hcancel, Real.rpow_one]
  refine ⟨epsilon0, h0, h01, ?_⟩
  intro epsilon hepsilon hle
  have hepsilon_one : epsilon ≤ 1 := hle.trans h01
  have hsqrt : Real.sqrt epsilon ≤ 1 := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_one hepsilon.le hepsilon_one (by norm_num)
  have hsmall : epsilon ^ (beta / 2) ≤ 1 / 4 :=
    (Real.rpow_le_rpow hepsilon.le hle (by positivity)).trans_eq hp0
  have hfactor : 1 + epsilon + Real.sqrt epsilon ≤ 3 := by linarith
  unfold epsilonTailBase
  calc
    _ ≤ epsilon ^ (beta / 2) * 3 :=
      mul_le_mul_of_nonneg_left hfactor (Real.rpow_nonneg hepsilon.le _)
    _ ≤ (1 / 4 : ℝ) * 3 := mul_le_mul_of_nonneg_right hsmall (by norm_num)
    _ < 1 := by norm_num

omit [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] in
theorem exists_beta_rate_gap {r S R : ℝ} (hrS : r ≤ S) (hrR : r < R) :
    ∃ beta : ℝ, 0 < beta ∧ (1 - beta) * r + beta * S < R := by
  let beta : ℝ := (R - r) / (2 * (S - r + 1))
  have hden : 0 < 2 * (S - r + 1) := by linarith
  have hbeta : 0 < beta := div_pos (sub_pos.mpr hrR) hden
  have hid : beta * (2 * (S - r + 1)) = R - r := div_mul_cancel₀ _ hden.ne'
  refine ⟨beta, hbeta, ?_⟩
  nlinarith

omit [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] in
theorem exists_dyadic_block_threshold {a R : ℝ} (haR : a < R) :
    ∃ m0 : ℕ, 0 < m0 ∧ ∀ m : ℕ, m0 ≤ m → ∀ k : ℕ,
      (3 : ℝ) ^ k * (2 : ℝ) ^ ((m : ℝ) * k * a / 2) ≤
        (2 : ℝ) ^ ((m : ℝ) * k * R / 2) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hden : 0 < (R - a) * Real.log 2 := mul_pos (sub_pos.mpr haR) hlog2
  obtain ⟨m0, hm0⟩ := exists_nat_gt (max 0 (2 * Real.log 3 / ((R - a) * Real.log 2)))
  have hm0pos : 0 < m0 := Nat.cast_pos.mp ((le_max_left _ _).trans_lt hm0)
  refine ⟨m0, hm0pos, ?_⟩
  intro m hm k
  have hlarge : 2 * Real.log 3 / ((R - a) * Real.log 2) < (m : ℝ) :=
    ((le_max_right _ _).trans_lt hm0).trans_le (Nat.cast_le.mpr hm)
  have hcross := (div_lt_iff₀ hden).mp hlarge
  have hlog : Real.log 3 ≤ ((m : ℝ) * (R - a) / 2) * Real.log 2 := by
    nlinarith
  have hfactor : (3 : ℝ) ≤ (2 : ℝ) ^ ((m : ℝ) * (R - a) / 2) :=
    (Real.le_rpow_iff_log_le (by norm_num : (0 : ℝ) < 3) (by norm_num)).mpr hlog
  calc
    _ ≤ ((2 : ℝ) ^ ((m : ℝ) * (R - a) / 2)) ^ k *
        (2 : ℝ) ^ ((m : ℝ) * k * a / 2) := by
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num) hfactor k)
        (Real.rpow_nonneg (by norm_num) _)
    _ = (2 : ℝ) ^ (((m : ℝ) * (R - a) / 2) * k + (m : ℝ) * k * a / 2) := by
      rw [← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2),
        ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    _ = _ := by congr 1; ring

omit [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] in
theorem exists_rate_parameters {r S R : ℝ} (hrS : r ≤ S) (hrR : r < R) :
    ∃ (beta epsilon0 : ℝ) (m0 : ℕ),
      0 < beta ∧ 0 < epsilon0 ∧ epsilon0 ≤ 1 ∧ 0 < m0 ∧
      (∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ epsilon0 →
        0 ≤ epsilonTailBase epsilon beta ∧ epsilonTailBase epsilon beta < 1) ∧
      ∀ m : ℕ, m0 ≤ m → ∀ k : ℕ,
        (3 : ℝ) ^ k * (2 : ℝ) ^ ((m : ℝ) * k * ((1 - beta) * r + beta * S) / 2) ≤
          (2 : ℝ) ^ ((m : ℝ) * k * R / 2) := by
  obtain ⟨beta, hbeta, hgap⟩ := exists_beta_rate_gap hrS hrR
  obtain ⟨epsilon0, he0, he01, he⟩ := exists_epsilon_threshold hbeta
  obtain ⟨m0, hm0, hm⟩ := exists_dyadic_block_threshold hgap
  exact ⟨beta, epsilon0, m0, hbeta, he0, he01, hm0,
    fun epsilon hepsilon hle => ⟨epsilonTailBase_nonneg hepsilon.le beta, he epsilon hepsilon hle⟩,
    hm⟩

omit [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] in
theorem epsilonTailBase_pow_tendsto {epsilon beta : ℝ} (hepsilon : 0 ≤ epsilon)
    (hbase : epsilonTailBase epsilon beta < 1) :
    Tendsto (fun k : ℕ => (epsilonTailBase epsilon beta) ^ k) atTop (𝓝 0) :=
  tendsto_pow_atTop_nhds_zero_of_lt_one (epsilonTailBase_nonneg hepsilon beta) hbase

end QuantumProver.SuperchannelDiscrimination.TensorWordTruncation

namespace QuantumProver.SuperchannelDiscrimination.TensorWordTruncation

variable {I O E F : Type*} [Fintype F]

def action (B : Matrix (O × F) I ℂ) (D : Matrix E F ℂ) : Matrix (O × E) I ℂ :=
  fun oe i => ∑ f, D oe.2 f * B (oe.1, f) i

def tensorAction {k : ℕ} (B : Matrix (O × F) I ℂ)
    (D : Matrix (Fin k → E) (Fin k → F) ℂ) :
      Matrix (Fin k → O × E) (Fin k → I) ℂ :=
  fun oe i => ∑ f : Fin k → F,
    D (fun a => (oe a).2) f * ∏ a, B ((oe a).1, f a) (i a)

theorem action_add (B : Matrix (O × F) I ℂ) (C H : Matrix E F ℂ) :
    action B (C + H) = action B C + action B H := by
  ext oe i
  simp only [action, Matrix.add_apply, add_mul, Finset.sum_add_distrib]

theorem action_smul (B : Matrix (O × F) I ℂ) (D : Matrix E F ℂ) (a : ℝ) :
    action B (a • D) = a • action B D := by
  ext oe i
  simp only [action, Matrix.smul_apply, smul_mul_assoc, Finset.smul_sum]

theorem tensorAction_smul {k : ℕ} (B : Matrix (O × F) I ℂ)
    (D : Matrix (Fin k → E) (Fin k → F) ℂ) (a : ℝ) :
    tensorAction B (a • D) = a • tensorAction B D := by
  ext oe i
  simp only [tensorAction, Matrix.smul_apply, smul_mul_assoc, Finset.smul_sum]

theorem tensorAction_sum {k : ℕ} {A : Type*} (B : Matrix (O × F) I ℂ)
    (s : Finset A) (D : A → Matrix (Fin k → E) (Fin k → F) ℂ) :
    tensorAction B (∑ a ∈ s, D a) = ∑ a ∈ s, tensorAction B (D a) := by
  ext oe i
  simp only [tensorAction, Matrix.sum_apply, Finset.sum_mul]
  exact Finset.sum_comm

theorem tensorAction_tensorMatrix {k : ℕ} (B : Matrix (O × F) I ℂ)
    (D : Fin k → Matrix E F ℂ) :
    tensorAction B (tensorMatrix D) = tensorMatrix (fun a => action B (D a)) := by
  classical
  ext oe i
  simp only [tensorAction, tensorMatrix, action]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro f _
  exact (Finset.prod_mul_distrib).symm

theorem tensorAction_word {k : ℕ} (B : Matrix (O × F) I ℂ)
    (C H : Matrix E F ℂ) (s : Finset (Fin k)) :
    tensorAction B (word C H s) = word (action B C) (action B H) s := by
  unfold word
  rw [tensorAction_tensorMatrix]
  apply congrArg tensorMatrix
  funext a
  by_cases ha : a ∈ s <;> simp [ha]

theorem tensorAction_retained (B : Matrix (O × F) I ℂ)
    (C H : Matrix E F ℂ) (k ell : ℕ) :
    tensorAction B (retained C H k ell) = retained (action B C) (action B H) k ell := by
  unfold retained
  rw [tensorAction_sum]
  simp_rw [tensorAction_word]

theorem tensorAction_omitted (B : Matrix (O × F) I ℂ)
    (C H : Matrix E F ℂ) (k ell : ℕ) :
    tensorAction B (omitted C H k ell) = omitted (action B C) (action B H) k ell := by
  unfold omitted
  rw [tensorAction_sum]
  simp_rw [tensorAction_word]

theorem tensorAction_attenuatedRetained (B : Matrix (O × F) I ℂ)
    (C H : Matrix E F ℂ) (k ell : ℕ) (delta : ℝ) :
    tensorAction B (attenuatedRetained C H k ell delta) =
      attenuatedRetained (action B C) (action B H) k ell delta := by
  unfold attenuatedRetained
  rw [tensorAction_smul, tensorAction_retained]

theorem tensorAction_total (B : Matrix (O × F) I ℂ) (C H : Matrix E F ℂ) (k : ℕ) :
    tensorAction B (tensorMatrix (fun _ : Fin k => C + H)) =
      tensorMatrix (fun _ : Fin k => action B C + action B H) := by
  rw [tensorAction_tensorMatrix, action_add]

end QuantumProver.SuperchannelDiscrimination.TensorWordTruncation

namespace QuantumProver.SuperchannelDiscrimination.TensorWordTruncation

variable {I O E F : Type*} [Fintype I] [Fintype O] [Fintype E] [Fintype F]
  [DecidableEq I] [DecidableEq O] [DecidableEq E] [DecidableEq F]

omit [DecidableEq F] in
theorem same_action_tail_and_contraction (B : Matrix (O × F) I ℂ) (C H : Matrix E F ℂ)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (hepsilon_one : epsilon ≤ 1)
    (htotal : ‖action B (C + H)‖ ≤ 1) (hbad : ‖action B H‖ ≤ epsilon)
    (beta : ℝ) (k : ℕ) :
    ‖tensorAction B (omitted C H k ⌊beta * k⌋₊)‖ ≤ (epsilonTailBase epsilon beta) ^ k ∧
    ‖tensorAction B (attenuatedRetained C H k ⌊beta * k⌋₊
      ((epsilonTailBase epsilon beta) ^ k))‖ ≤ 1 ∧
    ‖tensorAction B (attenuatedRetained C H k ⌊beta * k⌋₊
      ((epsilonTailBase epsilon beta) ^ k)) -
      tensorAction B (tensorMatrix (fun _ : Fin k => C + H))‖ ≤
        2 * (epsilonTailBase epsilon beta) ^ k := by
  have ht : ‖action B C + action B H‖ ≤ 1 := by simpa only [action_add] using htotal
  refine ⟨?_, ?_, ?_⟩
  · rw [tensorAction_omitted]
    exact physical_omitted_le_epsilon_base _ _ hepsilon hepsilon_one ht hbad beta k
  · rw [tensorAction_attenuatedRetained]
    exact physical_attenuation_norm_le_one _ _ hepsilon hepsilon_one ht hbad beta k
  · rw [tensorAction_attenuatedRetained, tensorAction_total]
    exact physical_attenuation_disturbance _ _ hepsilon hepsilon_one ht hbad beta k

theorem same_environment_rate_truncation (B : Matrix (O × F) I ℂ) (C H : Matrix E F ℂ)
    {epsilon beta r S R : ℝ} (hepsilon : 0 < epsilon) (hepsilon_one : epsilon ≤ 1)
    (hrS : r ≤ S) (hbeta : 0 ≤ beta) (m k : ℕ)
    (hC : ‖C‖ ≤ (2 : ℝ) ^ ((m : ℝ) * r / 2))
    (hH : ‖H‖ ≤ 2 * (2 : ℝ) ^ ((m : ℝ) * S / 2))
    (htotal : ‖action B (C + H)‖ ≤ 1) (hbad : ‖action B H‖ ≤ epsilon)
    (habsorb : (3 : ℝ) ^ k *
      (2 : ℝ) ^ ((m : ℝ) * k * ((1 - beta) * r + beta * S) / 2) ≤
        (2 : ℝ) ^ ((m : ℝ) * k * R / 2)) :
    let D := attenuatedRetained C H k ⌊beta * k⌋₊ ((epsilonTailBase epsilon beta) ^ k)
    ‖tensorAction B D‖ ≤ 1 ∧
    ‖tensorAction B D - tensorAction B (tensorMatrix (fun _ : Fin k => C + H))‖ ≤
      2 * (epsilonTailBase epsilon beta) ^ k ∧
    ‖D‖ ≤ (2 : ℝ) ^ ((m : ℝ) * k * R / 2) ∧
    ((2 : ℝ) ^ ((m : ℝ) * k * R) • (1 : Matrix (Fin k → F) (Fin k → F) ℂ) -
      Dᴴ * D).PosSemidef := by
  dsimp only
  let D := attenuatedRetained C H k ⌊beta * k⌋₊ ((epsilonTailBase epsilon beta) ^ k)
  let bound : ℝ := (2 : ℝ) ^ ((m : ℝ) * k * R / 2)
  have hb : 0 ≤ bound := Real.rpow_nonneg (by norm_num) _
  have hq : 0 ≤ (epsilonTailBase epsilon beta) ^ k :=
    pow_nonneg (epsilonTailBase_nonneg hepsilon.le beta) k
  have hret : ‖retained C H k ⌊beta * k⌋₊‖ ≤ bound :=
    (retained_norm_le_dyadic_scale C H m k hrS hbeta hC hH).trans habsorb
  have hD : ‖D‖ ≤ bound := by
    refine (attenuatedRetained_norm_le_bound C H k _ hq hret).trans ?_
    apply (div_le_iff₀ (by linarith : 0 < 1 + (epsilonTailBase epsilon beta) ^ k)).mpr
    nlinarith
  have hsquare : bound ^ 2 = (2 : ℝ) ^ ((m : ℝ) * k * R) := by
    dsimp [bound]
    rw [← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    norm_num
  obtain ⟨_, hphys, herr⟩ :=
    same_action_tail_and_contraction B C H hepsilon hepsilon_one htotal hbad beta k
  refine ⟨hphys, herr, hD, ?_⟩
  simpa only [hsquare] using right_gram_le_of_norm_le D hb hD

theorem exists_physical_environment_rate_parameters {r S R : ℝ}
    (hrS : r ≤ S) (hrR : r < R) :
    ∃ (beta epsilon0 : ℝ) (m0 : ℕ),
      0 < beta ∧ 0 < epsilon0 ∧ epsilon0 ≤ 1 ∧ 0 < m0 ∧
      ∀ (m : ℕ), m0 ≤ m → ∀ (epsilon : ℝ), 0 < epsilon → epsilon ≤ epsilon0 →
        epsilonTailBase epsilon beta < 1 ∧
        ∀ (B : Matrix (O × F) I ℂ) (C H : Matrix E F ℂ),
          ‖C‖ ≤ (2 : ℝ) ^ ((m : ℝ) * r / 2) →
          ‖H‖ ≤ 2 * (2 : ℝ) ^ ((m : ℝ) * S / 2) →
          ‖action B (C + H)‖ ≤ 1 → ‖action B H‖ ≤ epsilon → ∀ k : ℕ,
          let D := attenuatedRetained C H k ⌊beta * k⌋₊ ((epsilonTailBase epsilon beta) ^ k)
          ‖tensorAction B D‖ ≤ 1 ∧
          ‖tensorAction B D - tensorAction B (tensorMatrix (fun _ : Fin k => C + H))‖ ≤
            2 * (epsilonTailBase epsilon beta) ^ k ∧
          ‖D‖ ≤ (2 : ℝ) ^ ((m : ℝ) * k * R / 2) ∧
          ((2 : ℝ) ^ ((m : ℝ) * k * R) • (1 : Matrix (Fin k → F) (Fin k → F) ℂ) -
            Dᴴ * D).PosSemidef := by
  obtain ⟨beta, epsilon0, m0, hbeta, he0, he01, hm0, he, hm⟩ := exists_rate_parameters hrS hrR
  refine ⟨beta, epsilon0, m0, hbeta, he0, he01, hm0, ?_⟩
  intro m hmlarge epsilon hepsilon hesmall
  refine ⟨(he epsilon hepsilon hesmall).2, ?_⟩
  intro B C H hC hH htotal hbad k
  exact same_environment_rate_truncation B C H hepsilon (hesmall.trans he01) hrS hbeta.le
    m k hC hH htotal hbad (hm m hmlarge k)

end QuantumProver.SuperchannelDiscrimination.TensorWordTruncation

namespace QuantumProver.SuperchannelDiscrimination.StackTraceNorm

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

theorem trace_sandwich_re_le_norm_sq {rho : Matrix I I ℂ} (hrho : rho.PosSemidef)
    (V : Matrix J I ℂ) : (V * rho * Vᴴ).trace.re ≤ ‖V‖ ^ 2 * rho.trace.re := by
  have hp := FlaggedStates.trace_mul_re_nonneg hrho
    (TensorWordTruncation.right_gram_le_norm_sq V)
  have hc : (V * rho * Vᴴ).trace = (rho * (Vᴴ * V)).trace := by
    calc
      _ = (Vᴴ * V * rho).trace := Matrix.trace_mul_cycle V rho Vᴴ
      _ = _ := Matrix.trace_mul_comm _ _
  simp only [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one, Matrix.trace_sub,
    Matrix.trace_smul, Complex.sub_re, Complex.smul_re, smul_eq_mul] at hp
  rw [hc]
  linarith

theorem trace_sandwich_re_le_of_density_norm {rho : Matrix I I ℂ}
    (hrho : rho.PosSemidef) (htrace : rho.trace = 1)
    (V : Matrix J I ℂ) {c : ℝ} (hV : ‖V‖ ≤ c) :
    (V * rho * Vᴴ).trace.re ≤ c ^ 2 := by
  have hc : 0 ≤ c := (norm_nonneg V).trans hV
  have hbound := trace_sandwich_re_le_norm_sq hrho V
  simp only [htrace, Complex.one_re, mul_one] at hbound
  exact hbound.trans (by nlinarith [norm_nonneg V])

omit [Fintype J] [DecidableEq I] [DecidableEq J] in
theorem polarization_gram_sub (rho : Matrix I I ℂ) (U B : Matrix J I ℂ) (t : ℝ) :
    (U + t • B) * rho * (U + t • B)ᴴ -
      (U - t • B) * rho * (U - t • B)ᴴ =
        (2 * t) • (U * rho * Bᴴ + B * rho * Uᴴ) := by
  simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_sub,
    Matrix.conjTranspose_smul, star_trivial, Matrix.add_mul, Matrix.sub_mul,
    Matrix.mul_add, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul,
    smul_add, smul_sub, smul_smul, Matrix.mul_assoc]
  module

omit [Fintype J] [DecidableEq I] [DecidableEq J] in
theorem polarization_gram_add (rho : Matrix I I ℂ) (U B : Matrix J I ℂ) (t : ℝ) :
    (U + t • B) * rho * (U + t • B)ᴴ +
      (U - t • B) * rho * (U - t • B)ᴴ =
        (2 : ℝ) • (U * rho * Uᴴ) + (2 * t ^ 2) • (B * rho * Bᴴ) := by
  simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_sub,
    Matrix.conjTranspose_smul, star_trivial, Matrix.add_mul, Matrix.sub_mul,
    Matrix.mul_add, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul,
    smul_add, smul_sub, smul_smul, Matrix.mul_assoc]
  module

omit [DecidableEq I] in
theorem traceNorm_cross_le_scaled_traces {rho : Matrix I I ℂ} (hrho : rho.PosSemidef)
    (U B : Matrix J I ℂ) {t : ℝ} (ht : 0 < t) :
    EffectPerturbation.traceNorm (U * rho * Bᴴ + B * rho * Uᴴ) ≤
      (U * rho * Uᴴ).trace.re / t + t * (B * rho * Bᴴ).trace.re := by
  let P : Matrix J J ℂ := (1 / (2 * t) : ℝ) •
    ((U + t • B) * rho * (U + t • B)ᴴ)
  let Q : Matrix J J ℂ := (1 / (2 * t) : ℝ) •
    ((U - t • B) * rho * (U - t • B)ᴴ)
  have hp : P.PosSemidef :=
    (hrho.mul_mul_conjTranspose_same (U + t • B)).smul (by positivity)
  have hq : Q.PosSemidef :=
    (hrho.mul_mul_conjTranspose_same (U - t • B)).smul (by positivity)
  have hcancel : (1 / (2 * t) : ℝ) * (2 * t) = 1 := by field_simp [ht.ne']
  have hcoef1 : (1 / (2 * t) : ℝ) * 2 = t⁻¹ := by field_simp [ht.ne']
  have hcoef2 : (1 / (2 * t) : ℝ) * (2 * t ^ 2) = t := by field_simp [ht.ne']
  have hdiff : P - Q = U * rho * Bᴴ + B * rho * Uᴴ := by
    dsimp [P, Q]
    rw [← smul_sub, polarization_gram_sub, smul_smul, hcancel, one_smul]
  have hsum : P + Q = t⁻¹ • (U * rho * Uᴴ) + t • (B * rho * Bᴴ) := by
    dsimp [P, Q]
    rw [← smul_add, polarization_gram_add, smul_add, smul_smul, smul_smul, hcoef1, hcoef2]
  have htr : P.trace.re + Q.trace.re =
      (U * rho * Uᴴ).trace.re / t + t * (B * rho * Bᴴ).trace.re := by
    rw [← Complex.add_re, ← Matrix.trace_add, hsum, Matrix.trace_add,
      Matrix.trace_smul, Matrix.trace_smul, Complex.add_re, Complex.smul_re, Complex.smul_re]
    rw [div_eq_mul_inv]
    ring
  rw [← hdiff]
  exact (EffectPerturbation.traceNorm_sub_le_traces hp hq).trans_eq htr

theorem sandwich_traceNorm_le_two_delta {rho : Matrix I I ℂ}
    (hrho : rho.PosSemidef) (htrace : rho.trace = 1)
    (V W : Matrix J I ℂ) (hV : ‖V‖ ≤ 1) (hW : ‖W‖ ≤ 1)
    {delta : ℝ} (hdiff : ‖V - W‖ ≤ delta) :
    EffectPerturbation.traceNorm (V * rho * Vᴴ - W * rho * Wᴴ) ≤ 2 * delta := by
  have hdelta : 0 ≤ delta := (norm_nonneg (V - W)).trans hdiff
  by_cases hdzero : delta = 0
  · subst delta
    have heq : V = W := sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hdiff (norm_nonneg _)))
    rw [heq, sub_self, EffectPerturbation.traceNorm_of_posSemidef Matrix.PosSemidef.zero]
    simp only [Matrix.trace_zero, Complex.zero_re, mul_zero, le_refl]
  · have hdpos : 0 < delta := lt_of_le_of_ne hdelta (Ne.symm hdzero)
    let U : Matrix J I ℂ := V - W
    let B : Matrix J I ℂ := (1 / 2 : ℝ) • (V + W)
    have hB : ‖B‖ ≤ 1 := by
      calc
        _ = (1 / 2 : ℝ) * ‖V + W‖ := by
          dsimp only [B]
          rw [norm_smul]
          norm_num
        _ ≤ (1 / 2 : ℝ) * (‖V‖ + ‖W‖) :=
          mul_le_mul_of_nonneg_left (norm_add_le _ _) (by norm_num)
        _ ≤ 1 := by linarith
    have hcross : U * rho * Bᴴ + B * rho * Uᴴ = V * rho * Vᴴ - W * rho * Wᴴ := by
      dsimp [U, B]
      simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_sub,
        Matrix.conjTranspose_smul, star_trivial, Matrix.add_mul, Matrix.sub_mul,
        Matrix.mul_add, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul,
        smul_add, smul_sub, Matrix.mul_assoc]
      module
    have hUtrace := trace_sandwich_re_le_of_density_norm hrho htrace U hdiff
    have hBtrace := trace_sandwich_re_le_of_density_norm hrho htrace B hB
    have hleft : (U * rho * Uᴴ).trace.re / delta ≤ delta := by
      apply (div_le_iff₀ hdpos).mpr
      nlinarith
    have hright : delta * (B * rho * Bᴴ).trace.re ≤ delta := by nlinarith
    rw [← hcross]
    exact (traceNorm_cross_le_scaled_traces hrho U B hdpos).trans (by linarith)

end QuantumProver.SuperchannelDiscrimination.StackTraceNorm

namespace QuantumProver.SuperchannelDiscrimination.StackTraceNorm

variable {I J R : Type*} [Fintype I] [Fintype J] [Fintype R]
  [DecidableEq I] [DecidableEq J] [DecidableEq R]

def referenceLift (V : Matrix J I ℂ) : Matrix (R × J) (R × I) ℂ :=
  (1 : Matrix R R ℂ) ⊗ₖ V

theorem identity_norm_le_one : ‖(1 : Matrix R R ℂ)‖ ≤ 1 := by
  have hsq : ‖(1 : Matrix R R ℂ)‖ ^ 2 ≤ 1 :=
    GlobalMatrixSplit.norm_sq_le_of_right_gram (by norm_num : (0 : ℝ) ≤ 1) (by
      simp only [one_smul, Matrix.conjTranspose_one, Matrix.one_mul, sub_self]
      exact Matrix.PosSemidef.zero)
  nlinarith [norm_nonneg (1 : Matrix R R ℂ)]

omit [Fintype I] [Fintype J] [Fintype R] [DecidableEq I] [DecidableEq J] in
theorem referenceLift_apply (V : Matrix J I ℂ) (r s : R) (j : J) (i : I) :
    referenceLift (R := R) V (r, j) (s, i) = (if r = s then 1 else 0) * V j i := by
  simp only [referenceLift, Matrix.kronecker_apply, Matrix.one_apply]

omit [Fintype I] [Fintype J] [Fintype R] [DecidableEq I] [DecidableEq J] in
theorem referenceLift_sub (V W : Matrix J I ℂ) :
    referenceLift (R := R) (V - W) = referenceLift (R := R) V - referenceLift (R := R) W := by
  ext x y
  simp only [referenceLift, Matrix.kroneckerMap_apply, Matrix.sub_apply, mul_sub]

theorem referenceLift_norm_le (V : Matrix J I ℂ) :
    ‖referenceLift (R := R) V‖ ≤ ‖V‖ := by
  calc
    _ ≤ ‖(1 : Matrix R R ℂ)‖ * ‖V‖ := TensorWordTruncation.norm_kronecker_le _ _
    _ ≤ 1 * ‖V‖ := mul_le_mul_of_nonneg_right identity_norm_le_one (norm_nonneg V)
    _ = _ := one_mul _

theorem referenceLift_difference_norm_le (V W : Matrix J I ℂ) :
    ‖referenceLift (R := R) V - referenceLift (R := R) W‖ ≤ ‖V - W‖ := by
  rw [← referenceLift_sub]
  exact referenceLift_norm_le (V - W)

theorem reference_sandwich_traceNorm_le_two_delta
    {rho : Matrix (R × I) (R × I) ℂ} (hrho : rho.PosSemidef) (htrace : rho.trace = 1)
    (V W : Matrix J I ℂ) (hV : ‖V‖ ≤ 1) (hW : ‖W‖ ≤ 1)
    {delta : ℝ} (hdiff : ‖V - W‖ ≤ delta) :
    EffectPerturbation.traceNorm
      (referenceLift (R := R) V * rho * (referenceLift (R := R) V)ᴴ -
        referenceLift (R := R) W * rho * (referenceLift (R := R) W)ᴴ) ≤ 2 * delta := by
  exact sandwich_traceNorm_le_two_delta hrho htrace
    (referenceLift (R := R) V) (referenceLift (R := R) W)
    ((referenceLift_norm_le (R := R) V).trans hV)
    ((referenceLift_norm_le (R := R) W).trans hW)
    ((referenceLift_difference_norm_le (R := R) V W).trans hdiff)

end QuantumProver.SuperchannelDiscrimination.StackTraceNorm

namespace QuantumProver.SuperchannelDiscrimination.StackTraceNorm

variable {I O E : Type*}

def traceEnvironment [Fintype E] (X : Matrix (O × E) (O × E) ℂ) : Matrix O O ℂ :=
  ∑ e : E, X.submatrix (fun o => (o, e)) (fun o => (o, e))

theorem traceEnvironment_apply [Fintype E] (X : Matrix (O × E) (O × E) ℂ) (o p : O) :
    traceEnvironment X o p = ∑ e : E, X (o, e) (p, e) := by
  simp only [traceEnvironment, Matrix.sum_apply, Matrix.submatrix_apply]

def traceEnvironmentMap [Fintype E] :
    Matrix (O × E) (O × E) ℂ →ₗ[ℂ] Matrix O O ℂ where
  toFun := traceEnvironment
  map_add' X Y := by
    ext o p
    simp only [traceEnvironment_apply, Matrix.add_apply, Finset.sum_add_distrib]
  map_smul' a X := by
    ext o p
    simp only [traceEnvironment_apply, Matrix.smul_apply, Finset.smul_sum, RingHom.id_apply]

theorem traceEnvironment_posSemidef [Fintype O] [Fintype E] [DecidableEq O]
    {X : Matrix (O × E) (O × E) ℂ} (hX : X.PosSemidef) :
    (traceEnvironment X).PosSemidef := by
  have hp : 0 ≤ ∑ e : E, X.submatrix (fun o => (o, e)) (fun o => (o, e)) :=
    Finset.sum_nonneg (fun e _ => (hX.submatrix (fun o => (o, e))).nonneg)
  exact hp.posSemidef

theorem traceEnvironment_trace [Fintype O] [Fintype E]
    (X : Matrix (O × E) (O × E) ℂ) : (traceEnvironment X).trace = X.trace := by
  simp only [Matrix.trace, Matrix.diag, traceEnvironment_apply, Fintype.sum_prod_type]

theorem traceEnvironment_difference_contracts [Fintype O] [Fintype E]
    [DecidableEq O] [DecidableEq E] {A B : Matrix (O × E) (O × E) ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    EffectPerturbation.traceNorm (traceEnvironment A - traceEnvironment B) ≤
      EffectPerturbation.traceNorm (A - B) :=
  EffectPerturbation.traceNorm_difference_contracts traceEnvironmentMap
    (fun _ hX => traceEnvironment_posSemidef hX) traceEnvironment_trace hA hB

theorem traced_sandwich_traceNorm_le_two_delta [Fintype I] [Fintype O] [Fintype E]
    [DecidableEq I] [DecidableEq O] [DecidableEq E]
    {rho : Matrix I I ℂ} (hrho : rho.PosSemidef) (htrace : rho.trace = 1)
    (V W : Matrix (O × E) I ℂ) (hV : ‖V‖ ≤ 1) (hW : ‖W‖ ≤ 1)
    {delta : ℝ} (hdiff : ‖V - W‖ ≤ delta) :
    EffectPerturbation.traceNorm
      (traceEnvironment (V * rho * Vᴴ) - traceEnvironment (W * rho * Wᴴ)) ≤ 2 * delta := by
  exact (traceEnvironment_difference_contracts
    (hrho.mul_mul_conjTranspose_same V).isHermitian
    (hrho.mul_mul_conjTranspose_same W).isHermitian).trans
      (sandwich_traceNorm_le_two_delta hrho htrace V W hV hW hdiff)

end QuantumProver.SuperchannelDiscrimination.StackTraceNorm

namespace QuantumProver.SuperchannelDiscrimination.StackTraceNorm

variable {I O E R : Type*}

def referenceTraceEnvironment [Fintype E]
    (X : Matrix (R × (O × E)) (R × (O × E)) ℂ) : Matrix (R × O) (R × O) ℂ :=
  ∑ e : E, X.submatrix (fun ro => (ro.1, (ro.2, e))) (fun ro => (ro.1, (ro.2, e)))

theorem referenceTraceEnvironment_apply [Fintype E]
    (X : Matrix (R × (O × E)) (R × (O × E)) ℂ) (ro so : R × O) :
    referenceTraceEnvironment X ro so = ∑ e : E, X (ro.1, (ro.2, e)) (so.1, (so.2, e)) := by
  simp only [referenceTraceEnvironment, Matrix.sum_apply, Matrix.submatrix_apply]

def referenceTraceEnvironmentMap [Fintype E] :
    Matrix (R × (O × E)) (R × (O × E)) ℂ →ₗ[ℂ] Matrix (R × O) (R × O) ℂ where
  toFun := referenceTraceEnvironment
  map_add' X Y := by
    ext ro so
    simp only [referenceTraceEnvironment_apply, Matrix.add_apply, Finset.sum_add_distrib]
  map_smul' a X := by
    ext ro so
    simp only [referenceTraceEnvironment_apply, Matrix.smul_apply, Finset.smul_sum, RingHom.id_apply]

theorem referenceTraceEnvironment_posSemidef [Fintype R] [Fintype O] [Fintype E]
    [DecidableEq R] [DecidableEq O]
    {X : Matrix (R × (O × E)) (R × (O × E)) ℂ} (hX : X.PosSemidef) :
    (referenceTraceEnvironment X).PosSemidef := by
  have hp : 0 ≤ ∑ e : E,
      X.submatrix (fun ro : R × O => (ro.1, (ro.2, e)))
        (fun ro : R × O => (ro.1, (ro.2, e))) :=
    Finset.sum_nonneg (fun e _ =>
      (hX.submatrix (fun ro : R × O => (ro.1, (ro.2, e)))).nonneg)
  exact hp.posSemidef

theorem referenceTraceEnvironment_trace [Fintype R] [Fintype O] [Fintype E]
    (X : Matrix (R × (O × E)) (R × (O × E)) ℂ) :
    (referenceTraceEnvironment X).trace = X.trace := by
  simp only [Matrix.trace, Matrix.diag, referenceTraceEnvironment_apply, Fintype.sum_prod_type]

theorem referenceTraceEnvironment_difference_contracts [Fintype R] [Fintype O] [Fintype E]
    [DecidableEq R] [DecidableEq O] [DecidableEq E]
    {A B : Matrix (R × (O × E)) (R × (O × E)) ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    EffectPerturbation.traceNorm
      (referenceTraceEnvironment A - referenceTraceEnvironment B) ≤
        EffectPerturbation.traceNorm (A - B) :=
  EffectPerturbation.traceNorm_difference_contracts referenceTraceEnvironmentMap
    (fun _ hX => referenceTraceEnvironment_posSemidef hX) referenceTraceEnvironment_trace hA hB

theorem reference_traced_sandwich_traceNorm_le_two_delta
    [Fintype I] [Fintype O] [Fintype E] [Fintype R]
    [DecidableEq I] [DecidableEq O] [DecidableEq E] [DecidableEq R]
    {rho : Matrix (R × I) (R × I) ℂ} (hrho : rho.PosSemidef) (htrace : rho.trace = 1)
    (V W : Matrix (O × E) I ℂ) (hV : ‖V‖ ≤ 1) (hW : ‖W‖ ≤ 1)
    {delta : ℝ} (hdiff : ‖V - W‖ ≤ delta) :
    EffectPerturbation.traceNorm
      (referenceTraceEnvironment
        (referenceLift (R := R) V * rho * (referenceLift (R := R) V)ᴴ) -
        referenceTraceEnvironment
        (referenceLift (R := R) W * rho * (referenceLift (R := R) W)ᴴ)) ≤ 2 * delta := by
  exact (referenceTraceEnvironment_difference_contracts
    (hrho.mul_mul_conjTranspose_same (referenceLift (R := R) V)).isHermitian
    (hrho.mul_mul_conjTranspose_same (referenceLift (R := R) W)).isHermitian).trans
      (reference_sandwich_traceNorm_le_two_delta (R := R) hrho htrace V W hV hW hdiff)

end QuantumProver.SuperchannelDiscrimination.StackTraceNorm

namespace QuantumProver.SuperchannelDiscrimination.TensorWordTruncation

variable {I J : Type*} [Fintype I] [Fintype J]
  [DecidableEq I] [DecidableEq J]

theorem tensorMatrix_const_succ_difference_norm_le
    (Y V : Matrix I J ℂ) (k : ℕ) :
    ‖tensorMatrix (fun _ : Fin (k + 1) => Y) -
      tensorMatrix (fun _ : Fin (k + 1) => V)‖ ≤
      ‖tensorMatrix (fun _ : Fin k => Y) -
        tensorMatrix (fun _ : Fin k => V)‖ * ‖Y‖ +
      ‖tensorMatrix (fun _ : Fin k => V)‖ * ‖Y - V‖ := by
  let e := (TensorPinching.rowsSuccEquiv I k).symm
  let f := (TensorPinching.rowsSuccEquiv J k).symm
  have heq :
      (tensorMatrix (fun _ : Fin (k + 1) => Y) -
        tensorMatrix (fun _ : Fin (k + 1) => V)).submatrix e f =
      (tensorMatrix (fun _ : Fin k => Y) -
        tensorMatrix (fun _ : Fin k => V)) ⊗ₖ Y +
        tensorMatrix (fun _ : Fin k => V) ⊗ₖ (Y - V) := by
    change (tensorMatrix (fun _ : Fin (k + 1) => Y)).submatrix e f -
      (tensorMatrix (fun _ : Fin (k + 1) => V)).submatrix e f = _
    dsimp only [e, f]
    rw [tensorMatrix_succ_submatrix, tensorMatrix_succ_submatrix]
    ext x y
    simp only [Matrix.kroneckerMap_apply, Matrix.sub_apply, Matrix.add_apply]
    ring
  calc
    _ = ‖(tensorMatrix (fun _ : Fin (k + 1) => Y) -
        tensorMatrix (fun _ : Fin (k + 1) => V)).submatrix e f‖ :=
      (norm_submatrix_equiv _ e f).symm
    _ = _ := congrArg norm heq
    _ ≤ ‖(tensorMatrix (fun _ : Fin k => Y) -
          tensorMatrix (fun _ : Fin k => V)) ⊗ₖ Y‖ +
        ‖tensorMatrix (fun _ : Fin k => V) ⊗ₖ (Y - V)‖ := norm_add_le _ _
    _ ≤ _ := add_le_add (norm_kronecker_le _ _) (norm_kronecker_le _ _)

theorem tensorMatrix_const_difference_norm_le
    (Y V : Matrix I J ℂ) {e : ℝ} (he0 : 0 ≤ e)
    (hV : ‖V‖ ≤ 1) (he : ‖Y - V‖ ≤ e) (k : ℕ) :
    ‖tensorMatrix (fun _ : Fin k => Y) -
      tensorMatrix (fun _ : Fin k => V)‖ ≤
      (k : ℝ) * e * (1 + e) ^ (k - 1) := by
  have hY : ‖Y‖ ≤ 1 + e := by
    have hy : Y = (Y - V) + V := by abel
    calc
      _ = ‖(Y - V) + V‖ := congrArg norm hy
      _ ≤ ‖Y - V‖ + ‖V‖ := norm_add_le _ _
      _ ≤ e + 1 := add_le_add he hV
      _ = _ := by ring
  induction k with
  | zero =>
      have hz : tensorMatrix (fun _ : Fin 0 => Y) =
          tensorMatrix (fun _ : Fin 0 => V) := by
        ext x y
        simp [tensorMatrix]
      rw [hz, sub_self, norm_zero]
      simp
  | succ k ih =>
      have hvk := tensorMatrix_const_norm_le_one V hV k
      have hc : 0 ≤ (k : ℝ) * e * (1 + e) ^ (k - 1) := by positivity
      have hb :
          ‖tensorMatrix (fun _ : Fin (k + 1) => Y) -
            tensorMatrix (fun _ : Fin (k + 1) => V)‖ ≤
            ((k : ℝ) * e * (1 + e) ^ (k - 1)) * (1 + e) + e := by
        calc
          _ ≤ _ := tensorMatrix_const_succ_difference_norm_le Y V k
          _ ≤ ((k : ℝ) * e * (1 + e) ^ (k - 1)) * (1 + e) + 1 * e :=
            add_le_add (mul_le_mul ih hY (norm_nonneg Y) hc)
              (mul_le_mul hvk he (norm_nonneg (Y - V)) (by norm_num))
          _ = _ := by ring
      have hs : ((k : ℝ) * e * (1 + e) ^ (k - 1)) * (1 + e) + e ≤
          ((k + 1 : ℕ) : ℝ) * e * (1 + e) ^ k := by
        by_cases hk : k = 0
        · subst k
          simp
        · have hp : (1 + e) ^ (k - 1) * (1 + e) = (1 + e) ^ k := by
            rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hk)]
          have hu : (1 : ℝ) ≤ (1 + e) ^ k :=
            one_le_pow₀ (by linarith : (1 : ℝ) ≤ 1 + e)
          have heu : e ≤ e * (1 + e) ^ k := by nlinarith
          calc
            _ = ((k : ℝ) * e) * ((1 + e) ^ (k - 1) * (1 + e)) + e := by ring
            _ = ((k : ℝ) * e) * (1 + e) ^ k + e := by rw [hp]
            _ ≤ ((k : ℝ) * e) * (1 + e) ^ k + e * (1 + e) ^ k :=
              add_le_add le_rfl heu
            _ = _ := by push_cast; ring
      simpa only [Nat.succ_eq_add_one, Nat.add_sub_cancel] using hb.trans hs

theorem weak_pair_norms (X Y V : Matrix I J ℂ) {delta e : ℝ}
    (hV : ‖V‖ ≤ 1) (hX : ‖X - V‖ ≤ delta)
    (hY : ‖Y - V‖ ≤ e) (he : e ≤ (1 - delta) / 2) :
    ‖X‖ ≤ 1 + delta ∧ ‖Y - X‖ ≤ (1 + delta) / 2 := by
  constructor
  · have hx : X = (X - V) + V := by abel
    calc
      _ = ‖(X - V) + V‖ := congrArg norm hx
      _ ≤ ‖X - V‖ + ‖V‖ := norm_add_le _ _
      _ ≤ delta + 1 := add_le_add hX hV
      _ = _ := by ring
  · have hyx : Y - X = (Y - V) - (X - V) := by abel
    calc
      _ = ‖(Y - V) - (X - V)‖ := congrArg norm hyx
      _ ≤ ‖Y - V‖ + ‖X - V‖ := norm_sub_le _ _
      _ ≤ e + delta := add_le_add hY hX
      _ ≤ _ := by linarith

theorem retained_target_tensor_error_le
    (X H V : Matrix I J ℂ) {e tail : ℝ} (he0 : 0 ≤ e)
    (hV : ‖V‖ ≤ 1) (he : ‖X + H - V‖ ≤ e)
    (k ell : ℕ) (htail : ‖omitted X H k ell‖ ≤ tail) :
    ‖retained X H k ell - tensorMatrix (fun _ : Fin k => V)‖ ≤
      tail + (k : ℝ) * e * (1 + e) ^ (k - 1) := by
  have hsum := retained_add_omitted X H k ell
  have hd : retained X H k ell - tensorMatrix (fun _ : Fin k => V) =
      -omitted X H k ell +
      (tensorMatrix (fun _ : Fin k => X + H) - tensorMatrix (fun _ : Fin k => V)) := by
    rw [← hsum]
    abel
  rw [hd]
  calc
    _ ≤ ‖-omitted X H k ell‖ +
        ‖tensorMatrix (fun _ : Fin k => X + H) - tensorMatrix (fun _ : Fin k => V)‖ :=
      norm_add_le _ _
    _ ≤ _ := by
      rw [norm_neg]
      exact add_le_add htail (tensorMatrix_const_difference_norm_le (X + H) V he0 hV he k)

end QuantumProver.SuperchannelDiscrimination.TensorWordTruncation

namespace QuantumProver.SuperchannelDiscrimination.TensorWordTruncation

variable {I O E F : Type*} [Fintype F]

theorem action_sub (B : Matrix (O × F) I ℂ) (Ca Cw : Matrix E F ℂ) :
    action B (Ca - Cw) = action B Ca - action B Cw := by
  ext oe i
  simp only [action, Matrix.sub_apply, sub_mul, Finset.sum_sub_distrib]

theorem action_weak_accurate_decomposition
    (B : Matrix (O × F) I ℂ) (Cw Ca : Matrix E F ℂ) :
    action B Cw + action B (Ca - Cw) = action B Ca := by
  rw [action_sub]
  abel

end QuantumProver.SuperchannelDiscrimination.TensorWordTruncation

namespace QuantumProver.SuperchannelDiscrimination.WeakRateReduction

def z (delta : ℝ) : ℝ := 4 * (1 + delta) / (1 - delta)
def q (delta : ℝ) : ℝ := (3 + delta) / 4
def beta (delta : ℝ) : ℝ := 1 + Real.log (q delta) / (2 * Real.log (z delta))
def lambda (delta : ℝ) : ℝ := Real.sqrt (q delta)

theorem z_ge_four {delta : ℝ} (hd0 : 0 ≤ delta) (hd1 : delta < 1) :
    4 ≤ z delta := by
  unfold z
  apply (le_div_iff₀ (by linarith : 0 < 1 - delta)).mpr
  linarith

theorem q_bounds {delta : ℝ} (hd0 : 0 ≤ delta) (hd1 : delta < 1) :
    3 / 4 ≤ q delta ∧ q delta < 1 := by
  unfold q
  constructor <;> linarith

theorem q_mul_z_sq_gt_one {delta : ℝ} (hd0 : 0 ≤ delta) (hd1 : delta < 1) :
    1 < q delta * (z delta) ^ 2 := by
  have hz := z_ge_four hd0 hd1
  have hq := (q_bounds hd0 hd1).1
  have hzsq : (16 : ℝ) ≤ (z delta) ^ 2 := by nlinarith
  have hm := mul_le_mul_of_nonneg_right hq (sq_nonneg (z delta))
  nlinarith

theorem beta_bounds {delta : ℝ} (hd0 : 0 ≤ delta) (hd1 : delta < 1) :
    0 < beta delta ∧ beta delta < 1 := by
  have hz4 := z_ge_four hd0 hd1
  have hz0 : 0 < z delta := by linarith
  have hq := q_bounds hd0 hd1
  have hq0 : 0 < q delta := by linarith [hq.1]
  have hlz : 0 < Real.log (z delta) := Real.log_pos (by linarith)
  have hlq : Real.log (q delta) < 0 := Real.log_neg hq0 hq.2
  have hsum : 0 < Real.log (q delta) + 2 * Real.log (z delta) := by
    have h := Real.log_pos (q_mul_z_sq_gt_one hd0 hd1)
    rw [Real.log_mul hq0.ne' (pow_ne_zero 2 hz0.ne'), Real.log_pow] at h
    norm_num at h
    exact h
  have hrlo : -1 < Real.log (q delta) / (2 * Real.log (z delta)) := by
    apply (lt_div_iff₀ (by positivity : 0 < 2 * Real.log (z delta))).mpr
    linarith
  have hrhi : Real.log (q delta) / (2 * Real.log (z delta)) < 0 :=
    div_neg_of_neg_of_pos hlq (by positivity)
  unfold beta
  constructor <;> linarith

theorem lambda_bounds {delta : ℝ} (hd0 : 0 ≤ delta) (hd1 : delta < 1) :
    0 < lambda delta ∧ lambda delta < 1 := by
  have hq := q_bounds hd0 hd1
  have hq0 : 0 < q delta := by linarith [hq.1]
  have hs := Real.sq_sqrt hq0.le
  have hp := Real.sqrt_pos.mpr hq0
  unfold lambda
  constructor
  · exact hp
  · nlinarith [Real.sqrt_nonneg (q delta)]

theorem lambda_eq_exp {delta : ℝ} (hd0 : 0 ≤ delta) (hd1 : delta < 1) :
    lambda delta = Real.exp (Real.log (q delta) / 2) := by
  have hq0 : 0 < q delta := by linarith [(q_bounds hd0 hd1).1]
  rw [lambda, Real.sqrt_eq_rpow, Real.rpow_def_of_pos hq0]
  congr 1
  ring

theorem generating_sum {delta : ℝ} (hd1 : delta < 1) :
    (1 + delta) + z delta * ((1 + delta) / 2) = z delta * q delta := by
  unfold z q
  field_simp [ne_of_gt (by linarith : 0 < 1 - delta)]
  ring

theorem generating_base_eq_lambda {delta : ℝ} (hd0 : 0 ≤ delta) (hd1 : delta < 1) :
    (z delta) ^ (-beta delta) * ((1 + delta) + z delta * ((1 + delta) / 2)) =
      lambda delta := by
  have hz0 : 0 < z delta := by linarith [z_ge_four hd0 hd1]
  have hq0 : 0 < q delta := by linarith [(q_bounds hd0 hd1).1]
  have hlz : 0 < Real.log (z delta) := Real.log_pos (by linarith [z_ge_four hd0 hd1])
  calc
    _ = Real.exp (Real.log (z delta) * (-beta delta)) * (z delta * q delta) := by
      rw [Real.rpow_def_of_pos hz0, generating_sum hd1]
    _ = Real.exp (Real.log (z delta) * (-beta delta)) *
        Real.exp (Real.log (z delta) + Real.log (q delta)) := by
      rw [Real.exp_add, Real.exp_log hz0, Real.exp_log hq0]
    _ = Real.exp (Real.log (q delta) / 2) := by
      rw [← Real.exp_add]
      congr 1
      unfold beta
      field_simp [hlz.ne']
      ring
    _ = _ := (lambda_eq_exp hd0 hd1).symm

theorem lambda_pow_tendsto {delta : ℝ} (hd0 : 0 ≤ delta) (hd1 : delta < 1) :
    Tendsto (fun k : ℕ => (lambda delta) ^ k) atTop (𝓝 0) :=
  tendsto_pow_atTop_nhds_zero_of_lt_one (lambda_bounds hd0 hd1).1.le
    (lambda_bounds hd0 hd1).2

end QuantumProver.SuperchannelDiscrimination.WeakRateReduction

namespace QuantumProver.SuperchannelDiscrimination.TensorWordTruncation

variable {I O E F : Type*} [Fintype I] [Fintype O] [Fintype E] [Fintype F]
  [DecidableEq I] [DecidableEq O] [DecidableEq E] [DecidableEq F]

theorem same_environment_weak_rate_reduction
    (B : Matrix (O × F) I ℂ) (Cw Ca : Matrix E F ℂ) (V : Matrix (O × E) I ℂ)
    {delta e r S : ℝ} (hd1 : delta < 1) (he : e ≤ (1 - delta) / 2)
    (hV : ‖V‖ ≤ 1) (hw : ‖action B Cw - V‖ ≤ delta)
    (ha : ‖action B Ca - V‖ ≤ e) (m k : ℕ) (hrS : r ≤ S)
    (hCw : ‖Cw‖ ≤ (2 : ℝ) ^ ((m : ℝ) * r / 2))
    (hCa : ‖Ca‖ ≤ (2 : ℝ) ^ ((m : ℝ) * S / 2)) :
    ‖retained Cw (Ca - Cw) k ⌊WeakRateReduction.beta delta * k⌋₊‖ ≤
        (3 : ℝ) ^ k * (2 : ℝ) ^
          ((m : ℝ) * k * ((1 - WeakRateReduction.beta delta) * r +
            WeakRateReduction.beta delta * S) / 2) ∧
      ‖tensorAction B (retained Cw (Ca - Cw) k ⌊WeakRateReduction.beta delta * k⌋₊) -
        tensorMatrix (fun _ : Fin k => V)‖ ≤
          (WeakRateReduction.lambda delta) ^ k + (k : ℝ) * e * (1 + e) ^ (k - 1) := by
  have hd0 : 0 ≤ delta := (norm_nonneg _).trans hw
  have he0 : 0 ≤ e := (norm_nonneg _).trans ha
  have hbeta := WeakRateReduction.beta_bounds hd0 hd1
  have hnorms := weak_pair_norms (action B Cw) (action B Ca) V hV hw ha he
  have hH : ‖action B (Ca - Cw)‖ ≤ (1 + delta) / 2 := by
    rw [action_sub]
    exact hnorms.2
  have htail :
      ‖omitted (action B Cw) (action B (Ca - Cw)) k
        ⌊WeakRateReduction.beta delta * k⌋₊‖ ≤ (WeakRateReduction.lambda delta) ^ k := by
    have ht := omitted_norm_le_geometric (action B Cw) (action B (Ca - Cw))
      (a := 1 + delta) (b := (1 + delta) / 2)
      (z := WeakRateReduction.z delta) (beta := WeakRateReduction.beta delta)
      (by linarith) (by linarith) (by linarith [WeakRateReduction.z_ge_four hd0 hd1])
      hnorms.1 hH k
    rw [WeakRateReduction.generating_base_eq_lambda hd0 hd1] at ht
    exact ht
  have hsum : ‖action B Cw + action B (Ca - Cw) - V‖ ≤ e := by
    rw [action_weak_accurate_decomposition]
    exact ha
  have hscale : (2 : ℝ) ^ ((m : ℝ) * r / 2) ≤ (2 : ℝ) ^ ((m : ℝ) * S / 2) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    nlinarith [Nat.cast_nonneg (α := ℝ) m]
  have hcoeff : ‖Ca - Cw‖ ≤ 2 * (2 : ℝ) ^ ((m : ℝ) * S / 2) := by
    calc
      _ ≤ ‖Ca‖ + ‖Cw‖ := norm_sub_le _ _
      _ ≤ (2 : ℝ) ^ ((m : ℝ) * S / 2) + (2 : ℝ) ^ ((m : ℝ) * S / 2) :=
        add_le_add hCa (hCw.trans hscale)
      _ = _ := by ring
  constructor
  · exact retained_norm_le_dyadic_scale Cw (Ca - Cw) m k hrS hbeta.1.le hCw hcoeff
  · rw [tensorAction_retained]
    exact retained_target_tensor_error_le (action B Cw) (action B (Ca - Cw)) V he0 hV hsum
      k _ htail

end QuantumProver.SuperchannelDiscrimination.TensorWordTruncation

namespace QuantumProver.SuperchannelDiscrimination.TensorWordTruncation

def rowsAddEquiv (I : Type*) (m h : ℕ) :
    (Fin (m + h) → I) ≃ (Fin m → I) × (Fin h → I) where
  toFun x := (fun i => x (Fin.castAdd h i), fun j => x (Fin.natAdd m j))
  invFun x := Fin.addCases x.1 x.2
  left_inv x := by
    funext i
    refine Fin.addCases ?_ ?_ i <;> intro j <;> simp
  right_inv x := by
    apply Prod.ext <;> funext i <;> simp

def rowsMulEquiv (I : Type*) (k m : ℕ) :
    (Fin (k * m) → I) ≃ (Fin k → Fin m → I) :=
  (Equiv.arrowCongr finProdFinEquiv.symm (Equiv.refl I)).trans (Equiv.curry _ _ _)

@[simp] theorem rowsMulEquiv_symm_apply (I : Type*) (k m : ℕ)
    (x : Fin k → Fin m → I) (a : Fin k) (b : Fin m) :
    (rowsMulEquiv I k m).symm x (finProdFinEquiv (a, b)) = x a b := by
  simp [rowsMulEquiv, Equiv.arrowCongr, Equiv.curry]

def rowsBlockPaddingEquiv (I : Type*) (k m h : ℕ) :
    (Fin (k * m + h) → I) ≃ (Fin k → Fin m → I) × (Fin h → I) :=
  (rowsAddEquiv I (k * m) h).trans
    (Equiv.prodCongr (rowsMulEquiv I k m) (Equiv.refl (Fin h → I)))

variable {I J : Type*}

theorem tensorMatrix_const_add_submatrix (V : Matrix I J ℂ) (m h : ℕ) :
    (tensorMatrix (fun _ : Fin (m + h) => V)).submatrix
        (rowsAddEquiv I m h).symm (rowsAddEquiv J m h).symm =
      tensorMatrix (fun _ : Fin m => V) ⊗ₖ tensorMatrix (fun _ : Fin h => V) := by
  ext x y
  simp [tensorMatrix, rowsAddEquiv, Fin.prod_univ_add, Matrix.kroneckerMap_apply]

theorem tensorMatrix_const_mul_submatrix (V : Matrix I J ℂ) (k m : ℕ) :
    (tensorMatrix (fun _ : Fin (k * m) => V)).submatrix
        (rowsMulEquiv I k m).symm (rowsMulEquiv J k m).symm =
      tensorMatrix (fun _ : Fin k => tensorMatrix (fun _ : Fin m => V)) := by
  ext x y
  simp only [Matrix.submatrix_apply, tensorMatrix]
  rw [← Fintype.prod_prod_type' (fun a b => V (x a b) (y a b))]
  apply Fintype.prod_equiv finProdFinEquiv.symm
  intro a
  simp [rowsMulEquiv, Equiv.arrowCongr, Equiv.curry]

theorem tensorMatrix_const_block_padding_submatrix (V : Matrix I J ℂ) (k m h : ℕ) :
    (tensorMatrix (fun _ : Fin (k * m + h) => V)).submatrix
        (rowsBlockPaddingEquiv I k m h).symm (rowsBlockPaddingEquiv J k m h).symm =
      tensorMatrix (fun _ : Fin k => tensorMatrix (fun _ : Fin m => V)) ⊗ₖ
        tensorMatrix (fun _ : Fin h => V) := by
  let ei := Equiv.prodCongr (rowsMulEquiv I k m) (Equiv.refl (Fin h → I))
  let ej := Equiv.prodCongr (rowsMulEquiv J k m) (Equiv.refl (Fin h → J))
  change ((tensorMatrix (fun _ : Fin (k * m + h) => V)).submatrix
    (rowsAddEquiv I (k * m) h).symm (rowsAddEquiv J (k * m) h).symm).submatrix ei.symm ej.symm = _
  rw [tensorMatrix_const_add_submatrix]
  have heq :
      (tensorMatrix (fun _ : Fin (k * m) => V) ⊗ₖ tensorMatrix (fun _ : Fin h => V)).submatrix
        ei.symm ej.symm =
      ((tensorMatrix (fun _ : Fin (k * m) => V)).submatrix
        (rowsMulEquiv I k m).symm (rowsMulEquiv J k m).symm) ⊗ₖ
          tensorMatrix (fun _ : Fin h => V) := by
    ext x y
    rfl
  rw [heq, tensorMatrix_const_mul_submatrix]

variable {A B : Type*} [Fintype I] [Fintype J] [Fintype A] [Fintype B]
  [DecidableEq I] [DecidableEq J] [DecidableEq A] [DecidableEq B]

theorem kronecker_padding_difference_norm_le (V W : Matrix I J ℂ) (P : Matrix A B ℂ)
    (hP : ‖P‖ ≤ 1) : ‖V ⊗ₖ P - W ⊗ₖ P‖ ≤ ‖V - W‖ := by
  have heq : V ⊗ₖ P - W ⊗ₖ P = (V - W) ⊗ₖ P := by
    ext x y
    simp only [Matrix.sub_apply, Matrix.kroneckerMap_apply]
    ring
  rw [heq]
  exact (norm_kronecker_le _ _).trans
    (by simpa using mul_le_mul_of_nonneg_left hP (norm_nonneg (V - W)))

end QuantumProver.SuperchannelDiscrimination.TensorWordTruncation

namespace QuantumProver.SuperchannelDiscrimination.WeakRateReduction

theorem blockSize_tendsto_atTop : Tendsto blockSize atTop atTop := by
  apply tendsto_atTop.2
  intro b
  filter_upwards [eventually_ge_atTop (b * b)] with N hN
  exact Nat.le_sqrt.mpr hN

theorem nat_rpow_mul_stretched_exp_tendsto (s : ℝ) {p gamma : ℝ}
    (hp : 0 < p) (hg : 0 < gamma) :
    Tendsto (fun N : ℕ => (N : ℝ) ^ s * Real.exp (-gamma * (N : ℝ) ^ p)) atTop (𝓝 0) := by
  have ht := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (s / p) gamma hg).comp
    ((tendsto_rpow_atTop hp).comp tendsto_natCast_atTop_atTop)
  refine ht.congr' (Eventually.of_forall ?_)
  intro N
  have he : p * (s / p) = s := by field_simp [hp.ne']
  simp only [Function.comp_apply, ← Real.rpow_mul (Nat.cast_nonneg N), he]

theorem eventually_polynomial_absorption (C s : ℝ) {p gamma : ℝ}
    (hp : 0 < p) (hg : 0 < gamma) :
    ∀ᶠ N : ℕ in atTop,
      C * (N : ℝ) ^ s * Real.exp (-gamma * (N : ℝ) ^ p) ≤
        Real.exp (-(gamma / 2) * (N : ℝ) ^ p) := by
  have ht : Tendsto (fun N : ℕ => C * ((N : ℝ) ^ s *
      Real.exp (-(gamma / 2) * (N : ℝ) ^ p))) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (nat_rpow_mul_stretched_exp_tendsto s hp (by linarith : 0 < gamma / 2)).const_mul C
  have hevent := ht.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hevent] with N hN
  have hsmall : C * (N : ℝ) ^ s * Real.exp (-(gamma / 2) * (N : ℝ) ^ p) ≤ 1 := by
    simpa only [mul_zero, mul_assoc] using hN.le
  have hex : Real.exp (-gamma * (N : ℝ) ^ p) =
      Real.exp (-(gamma / 2) * (N : ℝ) ^ p) * Real.exp (-(gamma / 2) * (N : ℝ) ^ p) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    _ = (C * (N : ℝ) ^ s * Real.exp (-(gamma / 2) * (N : ℝ) ^ p)) *
        Real.exp (-(gamma / 2) * (N : ℝ) ^ p) := by
      rw [hex]
      ring
    _ ≤ 1 * Real.exp (-(gamma / 2) * (N : ℝ) ^ p) :=
      mul_le_mul_of_nonneg_right hsmall (Real.exp_pos _).le
    _ = _ := one_mul _

theorem sqrt_half_rpow (N : ℕ) (alpha : ℝ) :
    (Real.sqrt (N : ℝ) / 2) ^ alpha = (2 : ℝ) ^ (-alpha) * (N : ℝ) ^ (alpha / 2) := by
  rw [Real.div_rpow (Real.sqrt_nonneg _) (by norm_num), Real.sqrt_eq_rpow,
    ← Real.rpow_mul (Nat.cast_nonneg N), show (1 / (2 : ℝ)) * alpha = alpha / 2 by ring,
    Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
  ring

theorem blockSize_rpow_lower {N : ℕ} (hN : 4 ≤ N) {alpha : ℝ} (ha : 0 ≤ alpha) :
    (2 : ℝ) ^ (-alpha) * (N : ℝ) ^ (alpha / 2) ≤ (blockSize N : ℝ) ^ alpha := by
  rw [← sqrt_half_rpow]
  exact Real.rpow_le_rpow (by positivity) (blockSize_real_bounds hN).1 ha

theorem block_error_bound {N : ℕ} (hN : 4 ≤ N) {alpha gamma K e : ℝ}
    (ha : 0 ≤ alpha) (hg : 0 ≤ gamma) (hK : 0 ≤ K)
    (he : e ≤ K * Real.exp (-gamma * (blockSize N : ℝ) ^ alpha)) :
    e ≤ K * Real.exp (-(gamma * (2 : ℝ) ^ (-alpha)) * (N : ℝ) ^ (alpha / 2)) := by
  refine he.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hK)
  have h := mul_le_mul_of_nonneg_left (blockSize_rpow_lower hN ha) hg
  nlinarith

theorem repeated_error_factor_le_two {e : ℝ} (he : 0 ≤ e) (k : ℕ)
    (hke : (k : ℝ) * e ≤ Real.log 2) : (1 + e) ^ (k - 1) ≤ 2 := by
  have hbase : 1 + e ≤ Real.exp e := by linarith [Real.add_one_le_exp e]
  have hpow := pow_le_pow_left₀ (by linarith : 0 ≤ 1 + e) hbase (k - 1)
  have hkm1 : ((k - 1 : ℕ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast Nat.sub_le k 1
  calc
    _ ≤ (Real.exp e) ^ (k - 1) := hpow
    _ = Real.exp (((k - 1 : ℕ) : ℝ) * e) := (Real.exp_nat_mul e (k - 1)).symm
    _ ≤ Real.exp ((k : ℝ) * e) := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hkm1 he)
    _ ≤ Real.exp (Real.log 2) := Real.exp_le_exp.mpr hke
    _ = _ := Real.exp_log (by norm_num)

theorem lambda_blockCount_bound {lam p : ℝ} (hlam0 : 0 < lam) (hlam1 : lam < 1)
    (hp : p ≤ 1 / 2) {N : ℕ} (hN : 4 ≤ N) :
    lam ^ blockCount N ≤ Real.exp (-((-Real.log lam) / 2) * (N : ℝ) ^ p) := by
  have hl : Real.log lam < 0 := Real.log_neg hlam0 hlam1
  have hcount := (blockCount_real_bounds hN).1
  have hNp : (N : ℝ) ^ p ≤ Real.sqrt (N : ℝ) := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ N)) hp
  have hm := mul_le_mul_of_nonpos_left hcount hl.le
  have hp' := mul_le_mul_of_nonpos_left hNp hl.le
  rw [← Real.rpow_natCast, Real.rpow_def_of_pos hlam0]
  apply Real.exp_le_exp.mpr
  nlinarith

theorem eventually_repetition_stretched_bound (errors : ℕ → ℝ) {K gamma alpha : ℝ}
    (herrors : ∀ m, 0 ≤ errors m) (hK : 0 < K) (hg : 0 < gamma)
    (ha : 0 < alpha)
    (hsource : ∀ᶠ m : ℕ in atTop, errors m ≤ K * Real.exp (-gamma * (m : ℝ) ^ alpha)) :
    ∀ᶠ N : ℕ in atTop,
      (blockCount N : ℝ) * errors (blockSize N) *
          (1 + errors (blockSize N)) ^ (blockCount N - 1) ≤
        Real.exp (-((gamma * (2 : ℝ) ^ (-alpha)) / 2) * (N : ℝ) ^ (alpha / 2)) := by
  let c := gamma * (2 : ℝ) ^ (-alpha)
  have hc : 0 < c := mul_pos hg (Real.rpow_pos_of_pos (by norm_num) _)
  have hp : 0 < alpha / 2 := by linarith
  have hlim : Tendsto (fun N : ℕ => 2 * K * Real.sqrt (N : ℝ) *
      Real.exp (-c * (N : ℝ) ^ (alpha / 2))) atTop (𝓝 0) := by
    convert (nat_rpow_mul_stretched_exp_tendsto (1 / 2) hp hc).const_mul (2 * K) using 1
    · ext N
      rw [Real.sqrt_eq_rpow]
      ring
    · simp
  have hsmall := hlim.eventually (Iio_mem_nhds (Real.log_pos (by norm_num : (1 : ℝ) < 2)))
  have habsorb := eventually_polynomial_absorption (4 * K) (1 / 2) hp hc
  filter_upwards [eventually_ge_atTop 4, blockSize_tendsto_atTop.eventually hsource,
    hsmall, habsorb] with N hN hsrc hsm hab
  have he0 := herrors (blockSize N)
  have he := block_error_bound hN ha.le hg.le hK.le hsrc
  have hs0 := Real.sqrt_nonneg (N : ℝ)
  have hk := (blockCount_real_bounds hN).2
  have hke : (blockCount N : ℝ) * errors (blockSize N) ≤ Real.log 2 := by
    calc
      _ ≤ (2 * Real.sqrt (N : ℝ)) * errors (blockSize N) := mul_le_mul_of_nonneg_right hk he0
      _ ≤ (2 * Real.sqrt (N : ℝ)) * (K * Real.exp (-c * (N : ℝ) ^ (alpha / 2))) :=
        mul_le_mul_of_nonneg_left he (by positivity)
      _ = 2 * K * Real.sqrt (N : ℝ) * Real.exp (-c * (N : ℝ) ^ (alpha / 2)) := by ring
      _ ≤ _ := hsm.le
  have hfactor := repeated_error_factor_le_two he0 (blockCount N) hke
  have hab' : 4 * K * Real.sqrt (N : ℝ) * Real.exp (-c * (N : ℝ) ^ (alpha / 2)) ≤
      Real.exp (-(c / 2) * (N : ℝ) ^ (alpha / 2)) := by
    simpa only [Real.sqrt_eq_rpow] using hab
  calc
    _ ≤ ((blockCount N : ℝ) * errors (blockSize N)) * 2 :=
      mul_le_mul_of_nonneg_left hfactor (by positivity)
    _ ≤ ((2 * Real.sqrt (N : ℝ)) * (K * Real.exp (-c * (N : ℝ) ^ (alpha / 2)))) * 2 := by
      apply mul_le_mul_of_nonneg_right _ (by norm_num)
      exact mul_le_mul hk he he0 (by positivity)
    _ = 4 * K * Real.sqrt (N : ℝ) * Real.exp (-c * (N : ℝ) ^ (alpha / 2)) := by ring
    _ ≤ _ := hab'

theorem stretchedExponent_pos {lam gamma alpha : ℝ}
    (hlam0 : 0 < lam) (hlam1 : lam < 1) (hg : 0 < gamma) :
    0 < min ((-Real.log lam) / 2) ((gamma * (2 : ℝ) ^ (-alpha)) / 2) := by
  have hl := Real.log_neg hlam0 hlam1
  have hc := mul_pos hg (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) (-alpha))
  exact lt_min (by linarith) (by linarith)

theorem eventually_full_integer_error_bound (errors : ℕ → ℝ) {lam K gamma alpha : ℝ}
    (hlam0 : 0 < lam) (hlam1 : lam < 1) (herrors : ∀ m, 0 ≤ errors m)
    (hK : 0 < K) (hg : 0 < gamma) (ha0 : 0 < alpha) (ha1 : alpha ≤ 1)
    (hsource : ∀ᶠ m : ℕ in atTop, errors m ≤ K * Real.exp (-gamma * (m : ℝ) ^ alpha)) :
    ∀ᶠ N : ℕ in atTop,
      lam ^ blockCount N + (blockCount N : ℝ) * errors (blockSize N) *
          (1 + errors (blockSize N)) ^ (blockCount N - 1) ≤
        2 * Real.exp (-(min ((-Real.log lam) / 2) ((gamma * (2 : ℝ) ^ (-alpha)) / 2)) *
          (N : ℝ) ^ (alpha / 2)) := by
  filter_upwards [eventually_ge_atTop 4,
    eventually_repetition_stretched_bound errors herrors hK hg ha0 hsource] with N hN hrep
  have htail := lambda_blockCount_bound hlam0 hlam1 (by linarith : alpha / 2 ≤ 1 / 2) hN
  have hp0 : 0 ≤ (N : ℝ) ^ (alpha / 2) := Real.rpow_nonneg (Nat.cast_nonneg N) _
  have hmin1 := min_le_left ((-Real.log lam) / 2) ((gamma * (2 : ℝ) ^ (-alpha)) / 2)
  have hmin2 := min_le_right ((-Real.log lam) / 2) ((gamma * (2 : ℝ) ^ (-alpha)) / 2)
  let cmin := min ((-Real.log lam) / 2) ((gamma * (2 : ℝ) ^ (-alpha)) / 2)
  have htail' : lam ^ blockCount N ≤ Real.exp (-cmin * (N : ℝ) ^ (alpha / 2)) :=
    htail.trans (Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_right hmin1 hp0]))
  have hrep' : (blockCount N : ℝ) * errors (blockSize N) *
      (1 + errors (blockSize N)) ^ (blockCount N - 1) ≤
      Real.exp (-cmin * (N : ℝ) ^ (alpha / 2)) :=
    hrep.trans (Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_right hmin2 hp0]))
  calc
    _ ≤ _ := add_le_add htail' hrep'
    _ = _ := by ring

end QuantumProver.SuperchannelDiscrimination.WeakRateReduction

namespace QuantumProver.SuperchannelDiscrimination.WeakRateReduction

theorem three_pow_eq_dyadic (k : ℕ) :
    (3 : ℝ) ^ k = (2 : ℝ) ^ ((k : ℝ) * (Real.log 3 / Real.log 2)) := by
  rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3),
    Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  congr 1
  field_simp [(Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne']

theorem eventually_dyadic_padding_absorption {a R L : ℝ} (haR : a < R) (haL : a ≤ L) :
    ∀ᶠ N : ℕ in atTop,
      ((3 : ℝ) ^ blockCount N * (2 : ℝ) ^
        ((blockSize N : ℝ) * (blockCount N : ℝ) * a / 2)) *
        (2 : ℝ) ^ ((paddingSize N : ℝ) * L / 2) ≤ (2 : ℝ) ^ ((N : ℝ) * R / 2) := by
  have hc : 0 ≤ Real.log 3 / Real.log 2 :=
    (div_pos (Real.log_pos (by norm_num)) (Real.log_pos (by norm_num))).le
  filter_upwards [eventually_all_integer_rate_absorption haR haL hc] with N hN
  rw [three_pow_eq_dyadic, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
    ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  linarith

end QuantumProver.SuperchannelDiscrimination.WeakRateReduction

namespace QuantumProver.SuperchannelDiscrimination.TensorWordTruncation

def rowsCastEquiv (I : Type*) {m n : ℕ} (h : m = n) : (Fin n → I) ≃ (Fin m → I) :=
  Equiv.arrowCongr (finCongr h).symm (Equiv.refl I)

theorem tensorMatrix_const_cast_submatrix {I J : Type*} (V : Matrix I J ℂ)
    {m n : ℕ} (h : m = n) :
    (tensorMatrix (fun _ : Fin n => V)).submatrix (rowsCastEquiv I h).symm (rowsCastEquiv J h).symm =
      tensorMatrix (fun _ : Fin m => V) := by
  subst n
  rfl

def rowsIntegerPaddingEquiv (I : Type*) (N : ℕ) :
    (Fin N → I) ≃
      (Fin (WeakRateReduction.blockCount N) → Fin (WeakRateReduction.blockSize N) → I) ×
        (Fin (WeakRateReduction.paddingSize N) → I) :=
  (rowsCastEquiv I (show WeakRateReduction.blockCount N * WeakRateReduction.blockSize N +
    WeakRateReduction.paddingSize N = N by
      simpa only [mul_comm] using WeakRateReduction.block_padding_identity N)).trans
    (rowsBlockPaddingEquiv I (WeakRateReduction.blockCount N) (WeakRateReduction.blockSize N)
      (WeakRateReduction.paddingSize N))

theorem tensorMatrix_const_integer_padding_submatrix {I J : Type*}
    (V : Matrix I J ℂ) (N : ℕ) :
    (tensorMatrix (fun _ : Fin N => V)).submatrix
        (rowsIntegerPaddingEquiv I N).symm (rowsIntegerPaddingEquiv J N).symm =
      tensorMatrix (fun _ : Fin (WeakRateReduction.blockCount N) =>
        tensorMatrix (fun _ : Fin (WeakRateReduction.blockSize N) => V)) ⊗ₖ
          tensorMatrix (fun _ : Fin (WeakRateReduction.paddingSize N) => V) := by
  let hlen : WeakRateReduction.blockCount N * WeakRateReduction.blockSize N +
      WeakRateReduction.paddingSize N = N := by
    simpa only [mul_comm] using WeakRateReduction.block_padding_identity N
  change ((tensorMatrix (fun _ : Fin N => V)).submatrix (rowsCastEquiv I hlen).symm
    (rowsCastEquiv J hlen).symm).submatrix
      (rowsBlockPaddingEquiv I (WeakRateReduction.blockCount N) (WeakRateReduction.blockSize N)
        (WeakRateReduction.paddingSize N)).symm
      (rowsBlockPaddingEquiv J (WeakRateReduction.blockCount N) (WeakRateReduction.blockSize N)
        (WeakRateReduction.paddingSize N)).symm = _
  rw [tensorMatrix_const_cast_submatrix, tensorMatrix_const_block_padding_submatrix]

end QuantumProver.SuperchannelDiscrimination.TensorWordTruncation

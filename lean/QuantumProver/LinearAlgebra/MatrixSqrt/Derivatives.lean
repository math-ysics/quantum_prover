import QuantumProver.LinearAlgebra.MatrixSqrt.Definitions

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

noncomputable section

open Matrix Set Filter
open scoped ContDiff Topology ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace QuantumProver.MatrixAnalysis.MatrixSqrt

variable {I : Type*} [Fintype I] [DecidableEq I]

def psdCone : Set (Mat I) := {A | 0 ≤ A}

def hsVector (X : Mat I) : EuclideanSpace ℂ (I × I) :=
  WithLp.toLp 2 (fun ij => X ij.1 ij.2)

theorem inner_hsVector (X Y : Mat I) :
    inner ℂ (hsVector X) (hsVector Y) = (Xᴴ * Y).trace := by
  simp only [hsVector, PiLp.inner_apply, PiLp.toLp_apply, RCLike.inner_apply',
    Fintype.sum_prod_type, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, RCLike.star_def]
  rw [Finset.sum_comm]

theorem hsNorm_eq_norm_hsVector (X : Mat I) : hsNorm X = ‖hsVector X‖ := by
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), inner_hsVector]
  rfl

theorem hsNorm_sq (X : Mat I) : hsNorm X ^ 2 = (Xᴴ * X).trace.re := by
  exact Real.sq_sqrt (Complex.nonneg_iff.mp (Matrix.posSemidef_conjTranspose_mul_self X).trace_nonneg).1

theorem hs_trace_pair_le (X Y : Mat I) : (Xᴴ * Y).trace.re ≤ hsNorm X * hsNorm Y := by
  rw [← inner_hsVector, hsNorm_eq_norm_hsVector, hsNorm_eq_norm_hsVector]
  exact re_inner_le_norm (𝕜 := ℂ) (hsVector X) (hsVector Y)

theorem abs_hs_trace_pair_le (X Y : Mat I) :
    |(Xᴴ * Y).trace.re| ≤ hsNorm X * hsNorm Y := by
  rw [← inner_hsVector, hsNorm_eq_norm_hsVector, hsNorm_eq_norm_hsVector]
  exact (Complex.abs_re_le_norm _).trans (norm_inner_le_norm (hsVector X) (hsVector Y))

section FrobeniusEstimates

open scoped Matrix.Norms.Frobenius

theorem hsNorm_eq_frobenius (X : Mat I) : hsNorm X = ‖X‖ := by
  rw [hsNorm_eq_norm_hsVector, PiLp.norm_eq_of_L2, Matrix.frobenius_norm_def]
  simp only [hsVector, PiLp.toLp_apply, Fintype.sum_prod_type, Real.rpow_two,
    Real.sqrt_eq_rpow]

theorem hsNorm_add_le (X Y : Mat I) : hsNorm (X + Y) ≤ hsNorm X + hsNorm Y := by
  simp only [hsNorm_eq_frobenius]
  exact norm_add_le X Y

theorem hsNorm_mul_le (X Y : Mat I) : hsNorm (X * Y) ≤ hsNorm X * hsNorm Y := by
  simp only [hsNorm_eq_frobenius]
  exact Matrix.frobenius_norm_mul X Y

theorem hsNorm_smul (c : ℝ) (X : Mat I) : hsNorm (c • X) = |c| * hsNorm X := by
  simp only [hsNorm_eq_frobenius, norm_smul, Real.norm_eq_abs]

theorem hsNorm_neg (X : Mat I) : hsNorm (-X) = hsNorm X := by
  simp only [hsNorm_eq_frobenius, norm_neg]

theorem hsNorm_conjTranspose (X : Mat I) : hsNorm Xᴴ = hsNorm X := by
  simp only [hsNorm_eq_frobenius, Matrix.frobenius_norm_conjTranspose]

end FrobeniusEstimates

theorem abs_trace_mul_le_hs (X Y : Mat I) : |(X * Y).trace.re| ≤ hsNorm X * hsNorm Y := by
  simpa only [Matrix.conjTranspose_conjTranspose, hsNorm_conjTranspose] using
    abs_hs_trace_pair_le Xᴴ Y

theorem hsNorm_sub_le (X Y : Mat I) : hsNorm (X - Y) ≤ hsNorm X + hsNorm Y := by
  simpa only [sub_eq_add_neg, hsNorm_neg] using hsNorm_add_le X (-Y)

theorem sylvester_hs_coercive {S : Mat I} {a : ℝ}
    (hFloor : (S - a • 1).PosSemidef) (X : Mat I) :
    2 * a * hsNorm X ^ 2 ≤ (Xᴴ * sylvester S X).trace.re := by
  have hLeftPSD := hFloor.conjTranspose_mul_mul_same X
  have hRightPSD := hFloor.mul_mul_conjTranspose_same X
  have hLeft := (Complex.nonneg_iff.mp hLeftPSD.trace_nonneg).1
  have hRight := (Complex.nonneg_iff.mp hRightPSD.trace_nonneg).1
  have hCycle : (X * S * Xᴴ).trace = (Xᴴ * X * S).trace := by
    exact Matrix.trace_mul_cycle X S Xᴴ
  have hXX : (X * Xᴴ).trace = (Xᴴ * X).trace := Matrix.trace_mul_comm X Xᴴ
  simp only [mul_sub, sub_mul, Matrix.smul_mul, Matrix.mul_smul, one_mul, mul_one,
    Matrix.trace_sub, Matrix.trace_smul, Complex.sub_re, Complex.smul_re, smul_eq_mul, hCycle, hXX] at hLeft hRight
  simp only [sylvester, mul_add, Matrix.trace_add, Complex.add_re, ← mul_assoc]
  rw [hsNorm_sq]
  linarith

theorem sylvester_hs_bound {S H X : Mat I} {a : ℝ}
    (ha : 0 < a) (hFloor : (S - a • 1).PosSemidef)
    (hEquation : sylvester S X = H) : hsNorm X ≤ hsNorm H / (2 * a) := by
  have hCoercive := sylvester_hs_coercive hFloor X
  rw [hEquation] at hCoercive
  have hPair := hs_trace_pair_le X H
  have hXNonneg := hsNorm_nonneg X
  have hHNonneg := hsNorm_nonneg H
  by_cases hZero : hsNorm X = 0
  · rw [hZero]
    positivity
  · have hXPos : 0 < hsNorm X := lt_of_le_of_ne hXNonneg (by intro h; exact hZero h.symm)
    apply (le_div_iff₀ (mul_pos (by norm_num) ha)).mpr
    have hCancel : (hsNorm X * (2 * a)) * hsNorm X ≤ hsNorm H * hsNorm X := by
      calc
        _ = 2 * a * hsNorm X ^ 2 := by ring
        _ ≤ hsNorm X * hsNorm H := hCoercive.trans hPair
        _ = hsNorm H * hsNorm X := mul_comm _ _
    exact le_of_mul_le_mul_right hCancel hXPos

theorem sylvester_inverse_isHermitian (S : Mat I) (hS : S.PosDef)
    (H : Mat I) (hH : H.IsHermitian) :
    ((sylvesterEquiv S hS).symm H).IsHermitian := by
  let X := (sylvesterEquiv S hS).symm H
  have hEq : sylvester S X = H := sylvester_inverse_equation S hS H
  have hAdjoint := congrArg Matrix.conjTranspose hEq
  simp only [sylvester, Matrix.conjTranspose_add, Matrix.conjTranspose_mul,
    hS.isHermitian.eq, hH.eq] at hAdjoint
  have hAdjointEquation : sylvester S Xᴴ = H := by
    simpa only [sylvester, add_comm] using hAdjoint
  exact sylvester_solution_unique S hS H Xᴴ hAdjointEquation

theorem posDef_exists_scalar_floor {A : Mat I} (hA : A.PosDef) :
    ∃ r : ℝ, 0 < r ∧ algebraMap ℝ (Mat I) r ≤ A := by
  rcases subsingleton_or_nontrivial (Mat I) with hTrivial | hNontrivial
  · letI := hTrivial
    exact ⟨1, zero_lt_one, le_of_eq (Subsingleton.elim _ _)⟩
  · letI := hNontrivial
    exact (CFC.exists_pos_algebraMap_le_iff A hA.isHermitian.isSelfAdjoint).mpr
      (fun _ hx => hA.isStrictlyPositive.spectrum_pos hx)

theorem isOpen_positiveCone : IsOpen (positiveCone : Set (Herm I)) := by
  rw [Metric.isOpen_iff]
  intro A hA
  obtain ⟨r, hr, hFloor⟩ := posDef_exists_scalar_floor hA
  refine ⟨r, hr, ?_⟩
  intro B hB
  have hNorm : ‖(B : Mat I) - (A : Mat I)‖ < r := by
    simpa [Metric.mem_ball, dist_eq_norm, Submodule.coe_sub] using hB
  have hDifference : IsSelfAdjoint ((B : Mat I) - (A : Mat I)) := B.property.sub A.property
  have hLower := hDifference.neg_algebraMap_norm_le_self
  have hNewFloor : algebraMap ℝ (Mat I) (r - ‖(B : Mat I) - (A : Mat I)‖) ≤ (B : Mat I) := by
    calc
      _ = algebraMap ℝ (Mat I) r +
          -(algebraMap ℝ (Mat I) ‖(B : Mat I) - (A : Mat I)‖) := by rw [map_sub, sub_eq_add_neg]
      _ ≤ (A : Mat I) + ((B : Mat I) - (A : Mat I)) := add_le_add hFloor hLower
      _ = (B : Mat I) := by abel
  exact (isStrictlyPositive_algebraMap (sub_pos.mpr hNorm)).of_le hNewFloor |>.posDef

theorem rootFloor_of_spectralFloor {A : Mat I} {a : ℝ}
    (ha : 0 ≤ a) (hFloor : spectralFloor (a ^ 2) A) : rootFloor a A := by
  have hOrder : a ^ 2 • (1 : Mat I) ≤ A := sub_nonneg.mp hFloor.nonneg
  have hRootScalar : CFC.sqrt (a ^ 2 • (1 : Mat I)) = a • (1 : Mat I) := by
    exact CFC.sqrt_unique
      (by simp only [Matrix.smul_mul, Matrix.mul_smul, mul_one, smul_smul, pow_two])
      (smul_nonneg ha zero_le_one)
  have hRootOrder := CFC.monotone_sqrt hOrder
  rw [hRootScalar] at hRootOrder
  exact (sub_nonneg.mpr hRootOrder).posSemidef

theorem posDef_of_spectralFloor {A : Mat I} {m : ℝ}
    (hm : 0 < m) (hFloor : spectralFloor m A) : A.PosDef :=
  ((isStrictlyPositive_one (A := Mat I)).smul hm).of_le
    (sub_nonneg.mp hFloor.nonneg) |>.posDef

theorem contDiff_square : ContDiff ℂ ∞ (fun X : Mat I => X * X) :=
  contDiff_id.mul contDiff_id

theorem hasFDerivAt_square (S : Mat I) :
    HasFDerivAt (fun X : Mat I => X * X) (sylvesterCLM S) S := by
  convert! (hasFDerivAt_id S).mul' (hasFDerivAt_id S) using 1

theorem hasFDerivAt_square_equiv (S : Mat I) (hS : S.PosDef) :
    HasFDerivAt (fun X : Mat I => X * X)
      (sylvesterEquiv S hS : Mat I →L[ℂ] Mat I) S := by
  convert hasFDerivAt_square S using 1
  ext X
  rfl

theorem exists_smooth_sqrt_extension {A : Mat I} (hA : A.PosDef) :
    ∃ g : Mat I → Mat I,
      ContDiffAt ℂ ∞ g A ∧
      HasFDerivAt g
        ((sylvesterEquiv (CFC.sqrt A) (sqrt_posDef hA)).symm : Mat I →L[ℂ] Mat I) A ∧
      g A = CFC.sqrt A ∧
      CFC.sqrt =ᶠ[𝓝[psdCone] A] g := by
  let S : Mat I := CFC.sqrt A
  have hS : S.PosDef := sqrt_posDef hA
  let f : Mat I → Mat I := fun X => X * X
  have hf : ContDiffAt ℂ ∞ f S := contDiff_square.contDiffAt
  have hf' : HasFDerivAt f (sylvesterEquiv S hS : Mat I →L[ℂ] Mat I) S :=
    hasFDerivAt_square_equiv S hS
  have hn : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  let e := hf.toOpenPartialHomeomorph f hf' hn
  let g := hf.localInverse hf' hn
  have hSquare : f S = A := CFC.sqrt_mul_sqrt_self A hA.posSemidef.nonneg
  have hSource : S ∈ e.source := hf.mem_toOpenPartialHomeomorph_source hf' hn
  have hContinuous : ContinuousWithinAt CFC.sqrt psdCone A :=
    CFC.continuousOn_sqrt A hA.posSemidef.nonneg
  have hNear : ∀ᶠ X in 𝓝[psdCone] A, CFC.sqrt X ∈ e.source :=
    hContinuous (e.open_source.mem_nhds hSource)
  have hEqual : CFC.sqrt =ᶠ[𝓝[psdCone] A] g := by
    filter_upwards [hNear, self_mem_nhdsWithin] with X hX hPSD
    have hRootSquare : f (CFC.sqrt X) = X :=
      CFC.sqrt_mul_sqrt_self X hPSD
    have hInv := e.left_inv hX
    change g (f (CFC.sqrt X)) = CFC.sqrt X at hInv
    rw [hRootSquare] at hInv
    exact hInv.symm
  refine ⟨g, ?_, ?_, ?_, hEqual⟩
  · simpa only [hSquare] using hf.to_localInverse hf' hn
  · have hd := (hf.hasStrictFDerivAt' hf' hn).to_localInverse.hasFDerivAt
    simpa [Mat, g, S, ContDiffAt.localInverse, hSquare] using hd
  · simpa only [hSquare] using hf.localInverse_apply_image hf' hn

theorem contDiffWithinAt_sqrt {A : Mat I} (hA : A.PosDef) :
    ContDiffWithinAt ℝ ∞ CFC.sqrt psdCone A := by
  obtain ⟨g, hg, _, hAt, hEq⟩ := exists_smooth_sqrt_extension hA
  exact (hg.restrict_scalars ℝ).contDiffWithinAt.congr_of_eventuallyEq hEq hAt.symm

theorem hasFDerivWithinAt_sqrt {A : Mat I} (hA : A.PosDef) :
    HasFDerivWithinAt CFC.sqrt
      (((sylvesterEquiv (CFC.sqrt A) (sqrt_posDef hA)).symm : Mat I →L[ℂ] Mat I).restrictScalars ℝ)
      psdCone A := by
  obtain ⟨g, _, hg, hAt, hEq⟩ := exists_smooth_sqrt_extension hA
  exact (hg.restrictScalars ℝ).hasFDerivWithinAt.congr_of_eventuallyEq hEq hAt.symm

theorem contDiffAt_sqrt_onHerm {A : Herm I} (hA : (A : Mat I).PosDef) :
    ContDiffAt ℝ ∞ (fun X : Herm I => CFC.sqrt (X : Mat I)) A := by
  have hWithin : ContDiffWithinAt ℝ ∞ (fun X : Herm I => CFC.sqrt (X : Mat I)) positiveCone A :=
    (contDiffWithinAt_sqrt hA).comp A
      (selfAdjoint.submodule ℝ (Mat I)).subtypeL.contDiff.contDiffWithinAt
      (fun X hX => hX.posSemidef.nonneg)
  exact hWithin.contDiffAt (isOpen_positiveCone.mem_nhds hA)

theorem contDiffOn_sqrt_onHerm :
    ContDiffOn ℝ ∞ (fun X : Herm I => CFC.sqrt (X : Mat I)) positiveCone :=
  fun _ hA => (contDiffAt_sqrt_onHerm hA).contDiffWithinAt

def sqrtDerivative (A : Herm I) (hA : (A : Mat I).PosDef) : Herm I →L[ℝ] Mat I :=
  (((sylvesterEquiv (CFC.sqrt (A : Mat I)) (sqrt_posDef hA)).symm : Mat I →L[ℂ] Mat I).restrictScalars ℝ).comp
    (selfAdjoint.submodule ℝ (Mat I)).subtypeL

theorem hasFDerivAt_sqrt_onHerm {A : Herm I} (hA : (A : Mat I).PosDef) :
    HasFDerivAt (fun X : Herm I => CFC.sqrt (X : Mat I)) (sqrtDerivative A hA) A := by
  have hWithin : HasFDerivWithinAt (fun X : Herm I => CFC.sqrt (X : Mat I))
      (sqrtDerivative A hA) positiveCone A :=
    (hasFDerivWithinAt_sqrt hA).comp A
      ((selfAdjoint.submodule ℝ (Mat I)).subtypeL.hasFDerivAt.hasFDerivWithinAt)
      (fun X hX => hX.posSemidef.nonneg)
  exact hWithin.hasFDerivAt (isOpen_positiveCone.mem_nhds hA)

theorem sqrtDerivative_sylvester (A H : Herm I) (hA : (A : Mat I).PosDef) :
    sylvester (CFC.sqrt (A : Mat I)) (sqrtDerivative A hA H) = (H : Mat I) :=
  sylvester_inverse_equation (CFC.sqrt (A : Mat I)) (sqrt_posDef hA) (H : Mat I)

theorem contDiffOn_sqrt_path {s : Set ℝ} {rho : ℝ → Mat I}
    (hRho : ContDiffOn ℝ ∞ rho s) (hFaithful : ∀ t ∈ s, (rho t).PosDef) :
    ContDiffOn ℝ ∞ (fun t => CFC.sqrt (rho t)) s := by
  intro t ht
  exact (contDiffWithinAt_sqrt (hFaithful t ht)).comp t (hRho t ht)
    (fun u hu => (hFaithful u hu).posSemidef.nonneg)

def affineHerm (tau H : Herm I) (t : ℝ) : Herm I := tau + t • H

def affineRoot (tau H : Herm I) (t : ℝ) : Mat I :=
  CFC.sqrt (affineHerm tau H t : Mat I)

theorem contDiff_affineHerm (tau H : Herm I) : ContDiff ℝ ∞ (affineHerm tau H) := by
  unfold affineHerm
  fun_prop

theorem contDiffAt_affineRoot (tau H : Herm I) (t : ℝ)
    (hPD : (affineHerm tau H t : Mat I).PosDef) :
    ContDiffAt ℝ ∞ (affineRoot tau H) t :=
  (contDiffAt_sqrt_onHerm hPD).comp t (contDiff_affineHerm tau H).contDiffAt

theorem iteratedDeriv_affine (tau H : Mat I) (n : ℕ) (t : ℝ) :
    iteratedDeriv n (fun u : ℝ => tau + u • H) t =
      if n = 0 then tau + t • H else if n = 1 then H else 0 := by
  cases n with
  | zero => simp
  | succ n =>
    rw [iteratedDeriv_const_add (Nat.succ_pos n),
      iteratedDeriv_smul_const (by fun_prop) H]
    cases n with
    | zero => simp [iteratedDeriv_fun_id]
    | succ n => simp [iteratedDeriv_fun_id]

theorem natCast_matrix_mul (n : ℕ) (X Y : Mat I) :
    (n : Mat I) * X * Y = (n : ℝ) • (X * Y) := by
  rw [Nat.cast_smul_eq_nsmul ℝ, nsmul_eq_mul, mul_assoc]

theorem affineRoot_square_jet (tau H : Herm I) (t : ℝ) (n : ℕ)
    (hPD : (affineHerm tau H t : Mat I).PosDef) :
    (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) •
      (iteratedDeriv i (affineRoot tau H) t * iteratedDeriv (n - i) (affineRoot tau H) t)) =
      iteratedDeriv n (fun u : ℝ => (tau : Mat I) + u • (H : Mat I)) t := by
  have hNear : ∀ᶠ u in 𝓝 t, (affineHerm tau H u : Mat I).PosDef :=
    (contDiff_affineHerm tau H).continuous.continuousAt
      (isOpen_positiveCone.mem_nhds hPD)
  have hSquare : (fun u => affineRoot tau H u * affineRoot tau H u) =ᶠ[𝓝 t]
      (fun u => (tau : Mat I) + u • (H : Mat I)) := by
    filter_upwards [hNear] with u hu
    exact CFC.sqrt_mul_sqrt_self _ hu.posSemidef.nonneg
  have hJets := (hSquare.iteratedDeriv n).self_of_nhds
  have hSmooth : ContDiffAt ℝ n (affineRoot tau H) t :=
    (contDiffAt_affineRoot tau H t hPD).of_le (by simp)
  change iteratedDeriv n ((affineRoot tau H) * (affineRoot tau H)) t = _ at hJets
  rw [iteratedDeriv_mul hSmooth hSmooth] at hJets
  simp_rw [natCast_matrix_mul] at hJets
  exact hJets

theorem affineRoot_sylvester_one (tau H : Herm I) (t : ℝ)
    (hPD : (affineHerm tau H t : Mat I).PosDef) :
    sylvester (affineRoot tau H t) (iteratedDeriv 1 (affineRoot tau H) t) = (H : Mat I) := by
  have hEq := affineRoot_square_jet tau H t 1 hPD
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose_zero_right,
    Nat.choose_self, Nat.sub_self, Nat.sub_zero, iteratedDeriv_zero, zero_add, one_smul,
    iteratedDeriv_affine] at hEq
  exact hEq

theorem affineRoot_sylvester_two (tau H : Herm I) (t : ℝ)
    (hPD : (affineHerm tau H t : Mat I).PosDef) :
    sylvester (affineRoot tau H t) (iteratedDeriv 2 (affineRoot tau H) t) =
      -(2 : ℝ) • (iteratedDeriv 1 (affineRoot tau H) t * iteratedDeriv 1 (affineRoot tau H) t) := by
  have hEq := affineRoot_square_jet tau H t 2 hPD
  norm_num [Finset.sum_range_succ, Nat.choose, iteratedDeriv_affine] at hEq
  unfold sylvester
  simp only [iteratedDeriv_one]
  linear_combination (norm := module) hEq

theorem affineRoot_sylvester_three (tau H : Herm I) (t : ℝ)
    (hPD : (affineHerm tau H t : Mat I).PosDef) :
    sylvester (affineRoot tau H t) (iteratedDeriv 3 (affineRoot tau H) t) =
      -(3 : ℝ) • (iteratedDeriv 1 (affineRoot tau H) t * iteratedDeriv 2 (affineRoot tau H) t +
        iteratedDeriv 2 (affineRoot tau H) t * iteratedDeriv 1 (affineRoot tau H) t) := by
  have hEq := affineRoot_square_jet tau H t 3 hPD
  norm_num [Finset.sum_range_succ, Nat.choose, iteratedDeriv_affine] at hEq
  unfold sylvester
  simp only [iteratedDeriv_one]
  linear_combination (norm := module) hEq

theorem affineRoot_sylvester_four (tau H : Herm I) (t : ℝ)
    (hPD : (affineHerm tau H t : Mat I).PosDef) :
    sylvester (affineRoot tau H t) (iteratedDeriv 4 (affineRoot tau H) t) =
      -(4 : ℝ) • (iteratedDeriv 1 (affineRoot tau H) t * iteratedDeriv 3 (affineRoot tau H) t +
        iteratedDeriv 3 (affineRoot tau H) t * iteratedDeriv 1 (affineRoot tau H) t) -
      (6 : ℝ) • (iteratedDeriv 2 (affineRoot tau H) t * iteratedDeriv 2 (affineRoot tau H) t) := by
  have hEq := affineRoot_square_jet tau H t 4 hPD
  norm_num [Finset.sum_range_succ, Nat.choose, iteratedDeriv_affine] at hEq
  unfold sylvester
  simp only [iteratedDeriv_one]
  linear_combination (norm := module) hEq

theorem affineRoot_hs_derivative_bounds_saved (tau H : Herm I) (t : ℝ)
    (hPD : (affineHerm tau H t : Mat I).PosDef)
    (hFloor : spectralFloor (1 / 441) (affineHerm tau H t : Mat I))
    (hH : hsNorm (H : Mat I) ≤ 1) :
    hsNorm (iteratedDeriv 1 (affineRoot tau H) t) ≤ 21 / 2 ∧
    hsNorm (iteratedDeriv 2 (affineRoot tau H) t) ≤ 2400 ∧
    hsNorm (iteratedDeriv 3 (affineRoot tau H) t) ≤ 1600000 ∧
    hsNorm (iteratedDeriv 4 (affineRoot tau H) t) ≤ 1800000000 := by
  have hInputFloor : spectralFloor ((1 / 21 : ℝ) ^ 2) (affineHerm tau H t : Mat I) := by
    norm_num
    exact hFloor
  have hRoot : (affineRoot tau H t - (1 / 21 : ℝ) • 1).PosSemidef :=
    rootFloor_of_spectralFloor (by norm_num) hInputFloor
  have h1Nonneg := hsNorm_nonneg (iteratedDeriv 1 (affineRoot tau H) t)
  have h2Nonneg := hsNorm_nonneg (iteratedDeriv 2 (affineRoot tau H) t)
  have h3Nonneg := hsNorm_nonneg (iteratedDeriv 3 (affineRoot tau H) t)
  have h1 : hsNorm (iteratedDeriv 1 (affineRoot tau H) t) ≤ 21 / 2 := by
    calc
      _ ≤ hsNorm (H : Mat I) / (2 * (1 / 21)) :=
        sylvester_hs_bound (by norm_num) hRoot (affineRoot_sylvester_one tau H t hPD)
      _ ≤ 1 / (2 * (1 / 21)) := by gcongr
      _ = 21 / 2 := by norm_num
  have hRhs2 : hsNorm (-(2 : ℝ) •
      (iteratedDeriv 1 (affineRoot tau H) t * iteratedDeriv 1 (affineRoot tau H) t)) ≤
      2 * (21 / 2) * (21 / 2) := by
    calc
      _ = 2 * hsNorm (iteratedDeriv 1 (affineRoot tau H) t * iteratedDeriv 1 (affineRoot tau H) t) := by
        rw [hsNorm_smul]; norm_num
      _ ≤ 2 * (hsNorm (iteratedDeriv 1 (affineRoot tau H) t) *
          hsNorm (iteratedDeriv 1 (affineRoot tau H) t)) := by
        gcongr; exact hsNorm_mul_le _ _
      _ ≤ 2 * ((21 / 2) * (21 / 2)) := by gcongr
      _ = _ := by ring
  have h2 : hsNorm (iteratedDeriv 2 (affineRoot tau H) t) ≤ 2400 := by
    calc
      _ ≤ hsNorm (-(2 : ℝ) •
          (iteratedDeriv 1 (affineRoot tau H) t * iteratedDeriv 1 (affineRoot tau H) t)) / (2 * (1 / 21)) :=
        sylvester_hs_bound (by norm_num) hRoot (affineRoot_sylvester_two tau H t hPD)
      _ ≤ (2 * (21 / 2) * (21 / 2)) / (2 * (1 / 21)) := by gcongr
      _ ≤ 2400 := by norm_num
  have hRhs3 : hsNorm (-(3 : ℝ) •
      (iteratedDeriv 1 (affineRoot tau H) t * iteratedDeriv 2 (affineRoot tau H) t +
        iteratedDeriv 2 (affineRoot tau H) t * iteratedDeriv 1 (affineRoot tau H) t)) ≤
      3 * ((21 / 2) * 2400 + 2400 * (21 / 2)) := by
    calc
      _ = 3 * hsNorm (iteratedDeriv 1 (affineRoot tau H) t * iteratedDeriv 2 (affineRoot tau H) t +
          iteratedDeriv 2 (affineRoot tau H) t * iteratedDeriv 1 (affineRoot tau H) t) := by
        rw [hsNorm_smul]; norm_num
      _ ≤ 3 * (hsNorm (iteratedDeriv 1 (affineRoot tau H) t * iteratedDeriv 2 (affineRoot tau H) t) +
          hsNorm (iteratedDeriv 2 (affineRoot tau H) t * iteratedDeriv 1 (affineRoot tau H) t)) := by
        gcongr; exact hsNorm_add_le _ _
      _ ≤ 3 * (hsNorm (iteratedDeriv 1 (affineRoot tau H) t) * hsNorm (iteratedDeriv 2 (affineRoot tau H) t) +
          hsNorm (iteratedDeriv 2 (affineRoot tau H) t) * hsNorm (iteratedDeriv 1 (affineRoot tau H) t)) := by
        gcongr <;> apply hsNorm_mul_le
      _ ≤ 3 * ((21 / 2) * 2400 + 2400 * (21 / 2)) := by gcongr
  have h3 : hsNorm (iteratedDeriv 3 (affineRoot tau H) t) ≤ 1600000 := by
    calc
      _ ≤ hsNorm (-(3 : ℝ) •
          (iteratedDeriv 1 (affineRoot tau H) t * iteratedDeriv 2 (affineRoot tau H) t +
            iteratedDeriv 2 (affineRoot tau H) t * iteratedDeriv 1 (affineRoot tau H) t)) / (2 * (1 / 21)) :=
        sylvester_hs_bound (by norm_num) hRoot (affineRoot_sylvester_three tau H t hPD)
      _ ≤ (3 * ((21 / 2) * 2400 + 2400 * (21 / 2))) / (2 * (1 / 21)) := by gcongr
      _ ≤ 1600000 := by norm_num
  have hRhs4 : hsNorm (-(4 : ℝ) •
      (iteratedDeriv 1 (affineRoot tau H) t * iteratedDeriv 3 (affineRoot tau H) t +
        iteratedDeriv 3 (affineRoot tau H) t * iteratedDeriv 1 (affineRoot tau H) t) -
      (6 : ℝ) • (iteratedDeriv 2 (affineRoot tau H) t * iteratedDeriv 2 (affineRoot tau H) t)) ≤
      4 * ((21 / 2) * 1600000 + 1600000 * (21 / 2)) + 6 * (2400 * 2400) := by
    calc
      _ ≤ hsNorm (-(4 : ℝ) •
          (iteratedDeriv 1 (affineRoot tau H) t * iteratedDeriv 3 (affineRoot tau H) t +
            iteratedDeriv 3 (affineRoot tau H) t * iteratedDeriv 1 (affineRoot tau H) t)) +
          hsNorm ((6 : ℝ) • (iteratedDeriv 2 (affineRoot tau H) t * iteratedDeriv 2 (affineRoot tau H) t)) :=
        hsNorm_sub_le _ _
      _ = 4 * hsNorm (iteratedDeriv 1 (affineRoot tau H) t * iteratedDeriv 3 (affineRoot tau H) t +
          iteratedDeriv 3 (affineRoot tau H) t * iteratedDeriv 1 (affineRoot tau H) t) +
          6 * hsNorm (iteratedDeriv 2 (affineRoot tau H) t * iteratedDeriv 2 (affineRoot tau H) t) := by
        simp only [hsNorm_smul]; norm_num
      _ ≤ 4 * (hsNorm (iteratedDeriv 1 (affineRoot tau H) t * iteratedDeriv 3 (affineRoot tau H) t) +
          hsNorm (iteratedDeriv 3 (affineRoot tau H) t * iteratedDeriv 1 (affineRoot tau H) t)) +
          6 * hsNorm (iteratedDeriv 2 (affineRoot tau H) t * iteratedDeriv 2 (affineRoot tau H) t) := by
        gcongr; exact hsNorm_add_le _ _
      _ ≤ 4 * (hsNorm (iteratedDeriv 1 (affineRoot tau H) t) * hsNorm (iteratedDeriv 3 (affineRoot tau H) t) +
          hsNorm (iteratedDeriv 3 (affineRoot tau H) t) * hsNorm (iteratedDeriv 1 (affineRoot tau H) t)) +
          6 * (hsNorm (iteratedDeriv 2 (affineRoot tau H) t) * hsNorm (iteratedDeriv 2 (affineRoot tau H) t)) := by
        gcongr <;> apply hsNorm_mul_le
      _ ≤ 4 * ((21 / 2) * 1600000 + 1600000 * (21 / 2)) + 6 * (2400 * 2400) := by gcongr
  have h4 : hsNorm (iteratedDeriv 4 (affineRoot tau H) t) ≤ 1800000000 := by
    calc
      _ ≤ hsNorm (-(4 : ℝ) •
          (iteratedDeriv 1 (affineRoot tau H) t * iteratedDeriv 3 (affineRoot tau H) t +
            iteratedDeriv 3 (affineRoot tau H) t * iteratedDeriv 1 (affineRoot tau H) t) -
          (6 : ℝ) • (iteratedDeriv 2 (affineRoot tau H) t * iteratedDeriv 2 (affineRoot tau H) t)) / (2 * (1 / 21)) :=
        sylvester_hs_bound (by norm_num) hRoot (affineRoot_sylvester_four tau H t hPD)
      _ ≤ (4 * ((21 / 2) * 1600000 + 1600000 * (21 / 2)) + 6 * (2400 * 2400)) / (2 * (1 / 21)) := by gcongr
      _ ≤ 1800000000 := by norm_num
  exact ⟨h1, h2, h3, h4⟩

def realTraceCLM : Mat I →L[ℝ] ℝ where
  toLinearMap := Complex.reLm.comp (Matrix.traceLinearMap I ℝ ℂ)
  cont := by
    change Continuous (fun X : Mat I => X.trace.re)
    fun_prop

theorem iteratedDeriv_realTrace {f : ℝ → Mat I} {n : ℕ} {t : ℝ}
    (hf : ContDiffAt ℝ n f t) :
    iteratedDeriv n (fun u => (f u).trace.re) t = (iteratedDeriv n f t).trace.re := by
  have hMap := (realTraceCLM (I := I)).iteratedFDeriv_comp_left hf le_rfl
  exact congrArg (fun M => M (fun _ : Fin n => (1 : ℝ))) hMap

def affineAffinity (tau H : Herm I) (t : ℝ) : ℝ :=
  (affineRoot tau H t * affineRoot tau (-H) t).trace.re

theorem contDiffAt_affineAffinity (tau H : Herm I) (t : ℝ)
    (hPlus : (affineHerm tau H t : Mat I).PosDef)
    (hMinus : (affineHerm tau (-H) t : Mat I).PosDef) :
    ContDiffAt ℝ ∞ (affineAffinity tau H) t :=
  (realTraceCLM (I := I)).contDiff.contDiffAt.comp t
    ((contDiffAt_affineRoot tau H t hPlus).mul (contDiffAt_affineRoot tau (-H) t hMinus))

theorem contDiffOn_affineAffinity (tau H : Herm I) {s : Set ℝ}
    (hPlus : ∀ t ∈ s, (affineHerm tau H t : Mat I).PosDef)
    (hMinus : ∀ t ∈ s, (affineHerm tau (-H) t : Mat I).PosDef) :
    ContDiffOn ℝ ∞ (affineAffinity tau H) s :=
  fun t ht => (contDiffAt_affineAffinity tau H t (hPlus t ht) (hMinus t ht)).contDiffWithinAt

theorem affineAffinity_jet (tau H : Herm I) (t : ℝ) (n : ℕ)
    (hPlus : (affineHerm tau H t : Mat I).PosDef)
    (hMinus : (affineHerm tau (-H) t : Mat I).PosDef) :
    iteratedDeriv n (affineAffinity tau H) t =
      ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
        (iteratedDeriv i (affineRoot tau H) t * iteratedDeriv (n - i) (affineRoot tau (-H)) t).trace.re := by
  have hP : ContDiffAt ℝ n (affineRoot tau H) t :=
    (contDiffAt_affineRoot tau H t hPlus).of_le (by simp)
  have hM : ContDiffAt ℝ n (affineRoot tau (-H)) t :=
    (contDiffAt_affineRoot tau (-H) t hMinus).of_le (by simp)
  unfold affineAffinity
  rw [iteratedDeriv_realTrace (hP.mul hM)]
  change (iteratedDeriv n ((affineRoot tau H) * (affineRoot tau (-H))) t).trace.re = _
  rw [iteratedDeriv_mul hP hM]
  simp_rw [natCast_matrix_mul]
  simp only [Matrix.trace_sum, Matrix.trace_smul]
  change (Complex.reLm (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) •
    (iteratedDeriv i (affineRoot tau H) t * iteratedDeriv (n - i) (affineRoot tau (-H)) t).trace)) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  exact (Complex.reLm.map_smul (n.choose i : ℝ) _).trans (by simp only [smul_eq_mul]; rfl)

theorem affineRoot_neg_direction (tau H : Herm I) :
    affineRoot tau (-H) = fun t => affineRoot tau H (-t) := by
  funext t
  simp [affineRoot, affineHerm, Submodule.coe_add, Submodule.coe_smul,
    Submodule.coe_neg, smul_neg, neg_smul]

theorem affineAffinity_second (tau H : Herm I) (hTau : (tau : Mat I).PosDef) :
    iteratedDeriv 2 (affineAffinity tau H) 0 =
      -4 * (iteratedDeriv 1 (affineRoot tau H) 0 * iteratedDeriv 1 (affineRoot tau H) 0).trace.re := by
  have hPD : (affineHerm tau H 0 : Mat I).PosDef := by simpa [affineHerm] using hTau
  have hMD : (affineHerm tau (-H) 0 : Mat I).PosDef := by simpa [affineHerm] using hTau
  have hJet := affineAffinity_jet tau H 0 2 hPD hMD
  have hSquare := affineRoot_sylvester_two tau H 0 hPD
  have hTrace := congrArg (fun X : Mat I => X.trace.re) hSquare
  rw [affineRoot_neg_direction] at hJet
  simp only [iteratedDeriv_comp_neg, neg_zero] at hJet
  norm_num [Finset.sum_range_succ, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.trace_smul, Complex.smul_re] at hJet
  simp only [sylvester, Matrix.trace_add, Complex.add_re,
    Matrix.trace_smul, Complex.smul_re, smul_eq_mul] at hTrace
  simp only [iteratedDeriv_one] at hJet hTrace ⊢
  linarith

theorem affineAffinity_second_sylvester (tau H : Herm I) (hTau : (tau : Mat I).PosDef) :
    iteratedDeriv 2 (affineAffinity tau H) 0 =
      -4 * (((sylvesterEquiv (CFC.sqrt (tau : Mat I)) (sqrt_posDef hTau)).symm (H : Mat I)) *
        ((sylvesterEquiv (CFC.sqrt (tau : Mat I)) (sqrt_posDef hTau)).symm (H : Mat I))).trace.re := by
  have hPD : (affineHerm tau H 0 : Mat I).PosDef := by simpa [affineHerm] using hTau
  have hEquation := affineRoot_sylvester_one tau H 0 hPD
  have hSolution : iteratedDeriv 1 (affineRoot tau H) 0 =
      (sylvesterEquiv (CFC.sqrt (tau : Mat I)) (sqrt_posDef hTau)).symm (H : Mat I) := by
    apply sylvester_solution_unique (CFC.sqrt (tau : Mat I)) (sqrt_posDef hTau) (H : Mat I)
    simpa only [affineRoot, affineHerm, zero_smul, add_zero] using hEquation
  rw [affineAffinity_second tau H hTau, hSolution]

theorem affineAffinity_fourth_bound_saved (tau H : Herm I) (t : ℝ)
    (hTauTrace : (tau : Mat I).trace = 1) (hHTrace : (H : Mat I).trace = 0)
    (hH : hsNorm (H : Mat I) ≤ 1)
    (hPlusFloor : spectralFloor (1 / 441) (affineHerm tau H t : Mat I))
    (hMinusFloor : spectralFloor (1 / 441) (affineHerm tau (-H) t : Mat I)) :
    |iteratedDeriv 4 (affineAffinity tau H) t| < 4000000000 := by
  have hP := posDef_of_spectralFloor (by norm_num : (0 : ℝ) < 1 / 441) hPlusFloor
  have hM := posDef_of_spectralFloor (by norm_num : (0 : ℝ) < 1 / 441) hMinusFloor
  have hNegH : hsNorm ((-H : Herm I) : Mat I) ≤ 1 := by
    simpa only [Submodule.coe_neg, hsNorm_neg] using hH
  obtain ⟨hp1, hp2, hp3, hp4⟩ := affineRoot_hs_derivative_bounds_saved tau H t hP hPlusFloor hH
  obtain ⟨hm1, hm2, hm3, hm4⟩ := affineRoot_hs_derivative_bounds_saved tau (-H) t hM hMinusFloor hNegH
  have hp1n := hsNorm_nonneg (iteratedDeriv 1 (affineRoot tau H) t)
  have hp2n := hsNorm_nonneg (iteratedDeriv 2 (affineRoot tau H) t)
  have hp3n := hsNorm_nonneg (iteratedDeriv 3 (affineRoot tau H) t)
  have hm1n := hsNorm_nonneg (iteratedDeriv 1 (affineRoot tau (-H)) t)
  have hm2n := hsNorm_nonneg (iteratedDeriv 2 (affineRoot tau (-H)) t)
  have hm3n := hsNorm_nonneg (iteratedDeriv 3 (affineRoot tau (-H)) t)
  have hp0 : hsNorm (affineRoot tau H t) = 1 := by
    apply hsNorm_sqrt_of_trace_one hP.posSemidef
    simp only [affineHerm, Submodule.coe_add, Submodule.coe_smul, Matrix.trace_add,
      Matrix.trace_smul, hTauTrace, hHTrace, smul_zero, add_zero]
  have hm0 : hsNorm (affineRoot tau (-H) t) = 1 := by
    apply hsNorm_sqrt_of_trace_one hM.posSemidef
    simp only [affineHerm, Submodule.coe_add, Submodule.coe_smul, Submodule.coe_neg,
      Matrix.trace_add, Matrix.trace_smul, Matrix.trace_neg, hTauTrace, hHTrace,
      neg_zero, smul_zero, add_zero]
  have h13 : hsNorm (iteratedDeriv 1 (affineRoot tau H) t) *
      hsNorm (iteratedDeriv 3 (affineRoot tau (-H)) t) ≤ (21 / 2) * 1600000 := by
    gcongr
  have h22 : hsNorm (iteratedDeriv 2 (affineRoot tau H) t) *
      hsNorm (iteratedDeriv 2 (affineRoot tau (-H)) t) ≤ 2400 * 2400 := by
    gcongr
  have h31 : hsNorm (iteratedDeriv 3 (affineRoot tau H) t) *
      hsNorm (iteratedDeriv 1 (affineRoot tau (-H)) t) ≤ 1600000 * (21 / 2) := by
    gcongr
  have hSumBound :
      |∑ i ∈ Finset.range 5, (Nat.choose 4 i : ℝ) *
        (iteratedDeriv i (affineRoot tau H) t * iteratedDeriv (4 - i) (affineRoot tau (-H)) t).trace.re| ≤
      ∑ i ∈ Finset.range 5, (Nat.choose 4 i : ℝ) *
        (hsNorm (iteratedDeriv i (affineRoot tau H) t) * hsNorm (iteratedDeriv (4 - i) (affineRoot tau (-H)) t)) := by
    calc
      _ ≤ ∑ i ∈ Finset.range 5, |(Nat.choose 4 i : ℝ) *
          (iteratedDeriv i (affineRoot tau H) t * iteratedDeriv (4 - i) (affineRoot tau (-H)) t).trace.re| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro i _
        rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
        gcongr
        exact abs_trace_mul_le_hs _ _
  rw [← affineAffinity_jet tau H t 4 hP hM] at hSumBound
  norm_num [Finset.sum_range_succ, Nat.choose, hp0, hm0] at hSumBound
  simp only [iteratedDeriv_one] at h13 h31
  linarith [h13, h22, h31, hp4, hm4]

end QuantumProver.MatrixAnalysis.MatrixSqrt

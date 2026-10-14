import QuantumProver.InformationTheory.DepolarizingSquashedEntanglement.BCYTensorRegularization
import QuantumProver.InformationTheory.DepolarizingSquashedEntanglement.BCYOneWaySeparation
import QuantumProver.InformationTheory.QuantumRelativeEntropyContinuity
import QuantumProver.InformationTheory.DepolarizingSquashedEntanglement.BCYPinching
import QuantumProver.InformationTheory.DepolarizingSquashedEntanglement.BCYCommutingTests
import QuantumProver.InformationTheory.DepolarizingSquashedEntanglement.BCYAsymptoticGap
import QuantumProver.InformationTheory.DepolarizingSquashedEntanglement.BCYTestingMinimax
import QuantumProver.InformationTheory.DepolarizingSquashedEntanglement.BCYTestingPrimitives
import QuantumProver.InformationTheory.DepolarizingSquashedEntanglement.BCYLowerThresholdMass
import QuantumProver.InformationTheory.DepolarizingSquashedEntanglement.BCYUpperThresholdMass
import QuantumProver.InformationTheory.DepolarizingSquashedEntanglement.BCYDiagonalTests

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

open Matrix Set Filter
open scoped Topology BigOperators ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator Kronecker

namespace QuantumProver.DepolarizingSquashedEntanglement.BCYGeneralizedStein

open BCYRelativeEntropy

variable {A B I : Type*} [Fintype A] [Fintype B] [Fintype I]
  [DecidableEq A] [DecidableEq B] [DecidableEq I]

def separableCopies (A B : Type*) [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (n : ℕ) :
    Set (QMatrix (CopyIndex A n × CopyIndex B n)) :=
  BCYOneWaySeparation.separableMatrices (CopyIndex A n) (CopyIndex B n)

theorem separableCopies_isCompact (n : ℕ) :
    IsCompact (separableCopies A B n) :=
  BCYOneWaySeparation.separableMatrices_isCompact

theorem separableCopies_isClosed (n : ℕ) :
    IsClosed (separableCopies A B n) :=
  (separableCopies_isCompact (A := A) (B := B) n).isClosed

theorem separableCopies_convex (n : ℕ) :
    Convex ℝ (separableCopies A B n) :=
  BCYOneWaySeparation.separableMatrices_convex

def uniformDensity (I : Type*) [Fintype I] [DecidableEq I] [Nonempty I] :
    Density I where
  matrix := (1 / (Fintype.card I : ℝ)) • (1 : QMatrix I)
  positive := Matrix.PosSemidef.one.smul (by positivity)
  trace_one := by
    have hc : (Fintype.card I : ℂ) ≠ 0 := by
      exact_mod_cast (Fintype.card_pos (α := I)).ne'
    simp only [Matrix.trace_smul, Matrix.trace_one, Complex.real_smul,
      Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_natCast]
    field_simp [hc]

theorem uniformDensity_posDef [Nonempty I] :
    (uniformDensity I).matrix.PosDef :=
  Matrix.PosDef.one.smul (one_div_pos.mpr (Nat.cast_pos.mpr Fintype.card_pos))

def faithfulReference (A B : Type*) [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] [Nonempty A] [Nonempty B] :
    Density (A × B) :=
  productDensity (uniformDensity A) (uniformDensity B)

theorem faithfulReference_separable [Nonempty A] [Nonempty B] :
    IsSeparable (faithfulReference A B).matrix :=
  productDensity_separable _ _

theorem faithfulReference_posDef [Nonempty A] [Nonempty B] :
    (faithfulReference A B).matrix.PosDef :=
  (uniformDensity_posDef (I := A)).kronecker (uniformDensity_posDef (I := B))

theorem tensorCopies_posDef (ρ : Density (A × B)) (hρ : ρ.matrix.PosDef)
    (n : ℕ) : (tensorCopies ρ n).matrix.PosDef :=
  (QuantumProver.SuperchannelDiscrimination.TensorEntropy.tensorPower_posDef hρ n).submatrix
    (copyGrouping A B n).symm.injective

def faithfulSeparableCopies [Nonempty A] [Nonempty B] (n : ℕ) :
    SeparableDensity (CopyIndex A n) (CopyIndex B n) :=
  ⟨tensorCopies (faithfulReference A B) n,
    tensorCopies_separable _ faithfulReference_separable n⟩

theorem faithfulSeparableCopies_posDef [Nonempty A] [Nonempty B] (n : ℕ) :
    (faithfulSeparableCopies (A := A) (B := B) n).val.matrix.PosDef :=
  tensorCopies_posDef _ faithfulReference_posDef n

def regularizedSeparable [Nonempty A] [Nonempty B]
    (σ : SeparableDensity A B) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    SeparableDensity A B :=
  ⟨{ matrix := (1 - δ) • σ.val.matrix + δ • (faithfulReference A B).matrix
     positive := (σ.val.positive.smul (sub_nonneg.mpr hδ1)).add
       ((faithfulReference A B).positive.smul hδ0)
     trace_one := by
       simp only [Matrix.trace_add, Matrix.trace_smul, σ.val.trace_one,
         (faithfulReference A B).trace_one, ← add_smul, sub_add_cancel, one_smul] },
   (convex_convexHull ℝ _) σ.property faithfulReference_separable
     (sub_nonneg.mpr hδ1) hδ0 (sub_add_cancel 1 δ)⟩

theorem regularizedSeparable_posDef [Nonempty A] [Nonempty B]
    (σ : SeparableDensity A B) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    (regularizedSeparable σ δ hδ0.le hδ1).val.matrix.PosDef :=
  Matrix.PosDef.posSemidef_add (σ.val.positive.smul (sub_nonneg.mpr hδ1))
    (faithfulReference_posDef.smul hδ0)

theorem regularizedSeparable_reference_lower [Nonempty A] [Nonempty B]
    (σ : SeparableDensity A B) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    ((regularizedSeparable σ δ hδ0 hδ1).val.matrix -
      δ • (faithfulReference A B).matrix).PosSemidef := by
  change ((1 - δ) • σ.val.matrix + δ • (faithfulReference A B).matrix -
    δ • (faithfulReference A B).matrix).PosSemidef
  rw [add_sub_cancel_right]
  exact σ.val.positive.smul (sub_nonneg.mpr hδ1)

def discardLastCopy (n : ℕ)
    (σ : SeparableDensity (CopyIndex A (n + 1)) (CopyIndex B (n + 1))) :
    SeparableDensity (CopyIndex A n) (CopyIndex B n) :=
  ⟨BCYMeasurement.testedDensity σ.val,
    BCYMeasurement.testedDensity_isSeparable σ.val σ.property⟩

theorem discardLastCopy_matrix (n : ℕ)
    (σ : SeparableDensity (CopyIndex A (n + 1)) (CopyIndex B (n + 1)))
    (u v : CopyIndex A n × CopyIndex B n) :
    (discardLastCopy n σ).val.matrix u v =
      ∑ a : A, ∑ b : B, σ.val.matrix ((u.1,a),(u.2,b)) ((v.1,a),(v.2,b)) := rfl

end QuantumProver.DepolarizingSquashedEntanglement.BCYGeneralizedStein

namespace QuantumProver.DepolarizingSquashedEntanglement.BCYGeneralizedStein

def logarithmicGridIndex (κ : ℝ) (n : ℕ) (x : ℝ) : ℤ :=
  Int.ceil ((Real.log x + κ * (n : ℝ)) / κ)

def logarithmicGrid (κ : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  κ * (logarithmicGridIndex κ n x : ℝ) - κ * (n : ℝ)

theorem logarithmicGrid_bounds {κ : ℝ} (hκ : 0 < κ) (n : ℕ) (x : ℝ) :
    Real.log x ≤ logarithmicGrid κ n x ∧
      logarithmicGrid κ n x ≤ Real.log x + κ := by
  have hl := Int.le_ceil ((Real.log x + κ * (n : ℝ)) / κ)
  have hu := (Int.ceil_lt_add_one ((Real.log x + κ * (n : ℝ)) / κ)).le
  have hld := mul_le_mul_of_nonneg_left hl hκ.le
  have hud := mul_le_mul_of_nonneg_left hu hκ.le
  have he : κ * ((Real.log x + κ * (n : ℝ)) / κ) =
      Real.log x + κ * (n : ℝ) := by field_simp
  simp only [mul_add, mul_one] at hud
  rw [he] at hld hud
  dsimp [logarithmicGrid, logarithmicGridIndex]
  constructor <;> linarith

theorem logarithmicGridIndex_mem {κ : ℝ} (hκ : 0 < κ) (n : ℕ) (x : ℝ)
    (hlo : -κ * (n : ℝ) ≤ Real.log x) (hhi : Real.log x ≤ 0) :
    logarithmicGridIndex κ n x ∈ Finset.Icc 0 (n : ℤ) := by
  apply Finset.mem_Icc.mpr
  constructor
  · exact Int.ceil_nonneg (div_nonneg (by linarith) hκ.le)
  · apply Int.ceil_le.mpr
    change (Real.log x + κ * (n : ℝ)) / κ ≤ (n : ℝ)
    apply (div_le_iff₀ hκ).mpr
    nlinarith

theorem logarithmicGrid_level_count {κ : ℝ} (hκ : 0 < κ) (n : ℕ)
    {J : Type*} [Fintype J] [DecidableEq J] (x : J → ℝ)
    (hlo : ∀ j, -κ * (n : ℝ) ≤ Real.log (x j))
    (hhi : ∀ j, Real.log (x j) ≤ 0) :
    (Finset.univ.image (fun j => logarithmicGridIndex κ n (x j))).card ≤ n + 1 := by
  have hs : Finset.univ.image (fun j => logarithmicGridIndex κ n (x j)) ⊆
      Finset.Icc 0 (n : ℤ) := by
    intro z hz
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hz
    exact logarithmicGridIndex_mem hκ n (x j) (hlo j) (hhi j)
  have hc := Finset.card_le_card hs
  simpa [Int.card_Icc] using hc

def roundedSpectralWeight (κ : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  Real.exp (logarithmicGrid κ n x)

theorem roundedSpectralWeight_bounds {κ : ℝ} (hκ : 0 < κ)
    (n : ℕ) {x : ℝ} (hx : 0 < x) :
    x ≤ roundedSpectralWeight κ n x ∧
      roundedSpectralWeight κ n x ≤ Real.exp κ * x := by
  obtain ⟨hl,hu⟩ := logarithmicGrid_bounds hκ n x
  constructor
  · calc
      x = Real.exp (Real.log x) := (Real.exp_log hx).symm
      _ ≤ roundedSpectralWeight κ n x := Real.exp_le_exp.mpr hl
  · have h := Real.exp_le_exp.mpr hu
    simpa only [roundedSpectralWeight, Real.exp_add, Real.exp_log hx,
      mul_comm x (Real.exp κ)] using h

end QuantumProver.DepolarizingSquashedEntanglement.BCYGeneralizedStein

namespace QuantumProver.DepolarizingSquashedEntanglement.BCYGeneralizedStein

variable {I : Type*} [Fintype I] [DecidableEq I]

def roundedMatrix (κ : ℝ) (n : ℕ) (R : QMatrix I) : QMatrix I :=
  cfc (roundedSpectralWeight κ n) R

theorem roundedMatrix_posDef {R : QMatrix I} (hR : R.IsHermitian)
    (κ : ℝ) (n : ℕ) : (roundedMatrix κ n R).PosDef := by
  apply Matrix.IsStrictlyPositive.posDef
  apply (cfc_isStrictlyPositive_iff (p := IsSelfAdjoint)
    (roundedSpectralWeight κ n) R (R.finite_real_spectrum.continuousOn _) hR).mpr
  intro x hx
  exact Real.exp_pos _

theorem roundedMatrix_bounds {R : QMatrix I} (hR : R.PosDef)
    {κ : ℝ} (hκ : 0 < κ) (n : ℕ) :
    R ≤ roundedMatrix κ n R ∧ roundedMatrix κ n R ≤ Real.exp κ • R := by
  constructor
  · calc
      R = cfc (fun x : ℝ => x) R := (cfc_id' ℝ R hR.1).symm
      _ ≤ cfc (roundedSpectralWeight κ n) R := by
        apply cfc_mono (p := IsSelfAdjoint) _
          (R.finite_real_spectrum.continuousOn _)
          (R.finite_real_spectrum.continuousOn _)
        intro x hx
        exact (roundedSpectralWeight_bounds hκ n
          (hR.isStrictlyPositive.spectrum_pos hx)).1
  · calc
      roundedMatrix κ n R ≤ cfc (fun x : ℝ => Real.exp κ * x) R := by
        apply cfc_mono (p := IsSelfAdjoint) _
          (R.finite_real_spectrum.continuousOn _)
          (R.finite_real_spectrum.continuousOn _)
        intro x hx
        exact (roundedSpectralWeight_bounds hκ n
          (hR.isStrictlyPositive.spectrum_pos hx)).2
      _ = Real.exp κ • R := cfc_const_mul_id _ R hR.1

private theorem matrixTrace_mono {X Y : QMatrix I} (h : X ≤ Y) :
    X.trace.re ≤ Y.trace.re := by
  have ht := (Complex.nonneg_iff.mp (Matrix.le_iff.mp h).trace_nonneg).1
  simpa only [Matrix.trace_sub, Complex.sub_re, sub_nonneg] using ht

def roundingTrace (κ : ℝ) (n : ℕ) (ρ : Density I) : ℝ :=
  (roundedMatrix κ n ρ.matrix).trace.re

theorem roundingTrace_bounds (ρ : Density I) (hρ : ρ.matrix.PosDef)
    {κ : ℝ} (hκ : 0 < κ) (n : ℕ) :
    1 ≤ roundingTrace κ n ρ ∧ roundingTrace κ n ρ ≤ Real.exp κ := by
  obtain ⟨hl,hu⟩ := roundedMatrix_bounds hρ hκ n
  constructor
  · simpa only [roundingTrace, ρ.trace_one, Complex.one_re] using matrixTrace_mono hl
  · simpa only [roundingTrace, Matrix.trace_smul, Complex.smul_re,
      ρ.trace_one, Complex.one_re, smul_eq_mul, mul_one] using matrixTrace_mono hu

def roundedDensity (ρ : Density I) (hρ : ρ.matrix.PosDef)
    (κ : ℝ) (hκ : 0 < κ) (n : ℕ) : Density I where
  matrix := (1 / roundingTrace κ n ρ) • roundedMatrix κ n ρ.matrix
  positive := (roundedMatrix_posDef ρ.positive.1 κ n).posSemidef.smul
    (one_div_nonneg.mpr (zero_le_one.trans (roundingTrace_bounds ρ hρ hκ n).1))
  trace_one := by
    have hz : roundingTrace κ n ρ ≠ 0 :=
      ne_of_gt (zero_lt_one.trans_le (roundingTrace_bounds ρ hρ hκ n).1)
    have him := (Complex.nonneg_iff.mp
      (roundedMatrix_posDef ρ.positive.1 κ n).posSemidef.trace_nonneg).2
    have ht : (roundingTrace κ n ρ : ℂ) = (roundedMatrix κ n ρ.matrix).trace := by
      apply Complex.ext
      · rfl
      · simpa only [Complex.ofReal_im] using him
    rw [Matrix.trace_smul, Complex.real_smul, ← ht, ← Complex.ofReal_mul,
      one_div_mul_cancel hz, Complex.ofReal_one]

theorem roundedDensity_posDef (ρ : Density I) (hρ : ρ.matrix.PosDef)
    (κ : ℝ) (hκ : 0 < κ) (n : ℕ) :
    (roundedDensity ρ hρ κ hκ n).matrix.PosDef :=
  (roundedMatrix_posDef ρ.positive.1 κ n).smul
    (one_div_pos.mpr (zero_lt_one.trans_le (roundingTrace_bounds ρ hρ hκ n).1))

theorem roundedDensity_bounds (ρ : Density I) (hρ : ρ.matrix.PosDef)
    {κ : ℝ} (hκ : 0 < κ) (n : ℕ) :
    Real.exp (-κ) • ρ.matrix ≤ (roundedDensity ρ hρ κ hκ n).matrix ∧
      (roundedDensity ρ hρ κ hκ n).matrix ≤ Real.exp κ • ρ.matrix := by
  obtain ⟨hl,hu⟩ := roundedMatrix_bounds hρ hκ n
  obtain ⟨hzl,hzu⟩ := roundingTrace_bounds ρ hρ hκ n
  have hzpos : 0 < roundingTrace κ n ρ := zero_lt_one.trans_le hzl
  have hcl : Real.exp (-κ) ≤ 1 / roundingTrace κ n ρ := by
    rw [Real.exp_neg]
    simpa only [one_div] using one_div_le_one_div_of_le hzpos hzu
  have hcu : 1 / roundingTrace κ n ρ ≤ 1 := by
    simpa only [one_div_one] using one_div_le_one_div_of_le zero_lt_one hzl
  constructor
  · calc
      Real.exp (-κ) • ρ.matrix ≤ (1 / roundingTrace κ n ρ) • ρ.matrix :=
        smul_le_smul_of_nonneg_right hcl ρ.positive.nonneg
      _ ≤ (1 / roundingTrace κ n ρ) • roundedMatrix κ n ρ.matrix :=
        smul_le_smul_of_nonneg_left hl (one_div_nonneg.mpr hzpos.le)
  · calc
      (roundedDensity ρ hρ κ hκ n).matrix ≤ roundedMatrix κ n ρ.matrix := by
        simpa only [roundedDensity, one_smul] using smul_le_smul_of_nonneg_right hcu
          (roundedMatrix_posDef ρ.positive.1 κ n).posSemidef.nonneg
      _ ≤ Real.exp κ • ρ.matrix := hu

private theorem matrix_cfc_log_exp_smul {R : QMatrix I} (hR : R.PosDef) (a : ℝ) :
    cfc Real.log (Real.exp a • R) = a • (1 : QMatrix I) + cfc Real.log R := by
  simpa only [CFC.log, Algebra.algebraMap_eq_smul_one, Real.log_exp] using
    CFC.log_smul' R (Real.exp_pos a) hR.isStrictlyPositive

theorem roundedDensity_log_bounds (ρ : Density I) (hρ : ρ.matrix.PosDef)
    {κ : ℝ} (hκ : 0 < κ) (n : ℕ) :
    cfc Real.log ρ.matrix - κ • (1 : QMatrix I) ≤
        cfc Real.log (roundedDensity ρ hρ κ hκ n).matrix ∧
      cfc Real.log (roundedDensity ρ hρ κ hκ n).matrix ≤
        κ • (1 : QMatrix I) + cfc Real.log ρ.matrix := by
  obtain ⟨hl,hu⟩ := roundedDensity_bounds ρ hρ hκ n
  have hr := roundedDensity_posDef ρ hρ κ hκ n
  have hlow := QuantumProver.SuperchannelDiscrimination.MatrixLog.operator_log_monotone
    (hρ.smul (Real.exp_pos (-κ))) hr (Matrix.le_iff.mp hl)
  have hupp := QuantumProver.SuperchannelDiscrimination.MatrixLog.operator_log_monotone
    hr (hρ.smul (Real.exp_pos κ)) (Matrix.le_iff.mp hu)
  rw [matrix_cfc_log_exp_smul hρ] at hlow hupp
  constructor
  · have h := Matrix.le_iff.mpr hlow
    simpa only [neg_smul, sub_eq_add_neg, add_comm] using h
  · exact Matrix.le_iff.mpr hupp

theorem roundedDensity_relativeEntropy_displacement
    (ρ σ : Density I) (hσ : σ.matrix.PosDef)
    {κ : ℝ} (hκ : 0 < κ) (n : ℕ) :
    |(ρ.matrix * (cfc Real.log ρ.matrix - cfc Real.log σ.matrix)).trace.re -
      (ρ.matrix * (cfc Real.log ρ.matrix -
        cfc Real.log (roundedDensity σ hσ κ hκ n).matrix)).trace.re| ≤ κ := by
  obtain ⟨hl,hu⟩ := roundedDensity_log_bounds σ hσ hκ n
  have hlow := QuantumProver.SuperchannelDiscrimination.FlaggedStates.trace_mul_re_nonneg
    ρ.positive (Matrix.le_iff.mp hl)
  have hupp := QuantumProver.SuperchannelDiscrimination.FlaggedStates.trace_mul_re_nonneg
    ρ.positive (Matrix.le_iff.mp hu)
  simp only [Matrix.mul_sub, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one,
    Matrix.trace_sub, Matrix.trace_add, Matrix.trace_smul, Complex.sub_re,
    Complex.add_re, Complex.smul_re, ρ.trace_one, Complex.one_re,
    smul_eq_mul, mul_one] at hlow hupp
  apply abs_le.mpr
  constructor <;> simp only [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re] <;> linarith

private theorem density_eigenvalue_le_one (ρ : Density I) (i : I) :
    ρ.positive.1.eigenvalues i ≤ 1 := by
  have hs : ∑ j, ρ.positive.1.eigenvalues j = 1 := by
    have ht := ρ.trace_one
    rw [ρ.positive.1.trace_eq_sum_eigenvalues] at ht
    have htr := congrArg Complex.re ht
    simpa using htr
  rw [← hs]
  exact Finset.single_le_sum (fun j _ => ρ.positive.eigenvalues_nonneg j) (Finset.mem_univ i)

theorem roundedDensity_spectrum_ncard (ρ : Density I) (hρ : ρ.matrix.PosDef)
    {κ : ℝ} (hκ : 0 < κ) (n : ℕ)
    (hfloor : Real.exp (-κ * (n : ℝ)) • (1 : QMatrix I) ≤ ρ.matrix) :
    (spectrum ℝ (roundedDensity ρ hρ κ hκ n).matrix).ncard ≤ n + 1 := by
  classical
  let G : Finset ℤ := Finset.univ.image
    (fun i => logarithmicGridIndex κ n (ρ.positive.1.eigenvalues i))
  let g : ℤ → ℝ := fun z => (1 / roundingTrace κ n ρ) *
    Real.exp (κ * (z : ℝ) - κ * (n : ℝ))
  have hg : G.card ≤ n + 1 := by
    apply logarithmicGrid_level_count hκ n ρ.positive.1.eigenvalues
    · intro i
      have hi := (algebraMap_le_iff_le_spectrum (R := ℝ) (a := ρ.matrix)
        ρ.positive.1).mp (by simpa only [Algebra.algebraMap_eq_smul_one] using hfloor)
        _ (ρ.positive.1.eigenvalues_mem_spectrum_real i)
      calc
        -κ * (n : ℝ) = Real.log (Real.exp (-κ * (n : ℝ))) := (Real.log_exp _).symm
        _ ≤ Real.log (ρ.positive.1.eigenvalues i) := Real.log_le_log (Real.exp_pos _) hi
    · intro i
      simpa only [Real.log_one] using Real.log_le_log (hρ.eigenvalues_pos i)
        (density_eigenvalue_le_one ρ i)
  have hcfc : (roundedDensity ρ hρ κ hκ n).matrix =
      cfc (fun x : ℝ => (1 / roundingTrace κ n ρ) * roundedSpectralWeight κ n x)
        ρ.matrix :=
    (cfc_const_mul _ _ ρ.matrix (ρ.matrix.finite_real_spectrum.continuousOn _)).symm
  have hs : spectrum ℝ (roundedDensity ρ hρ κ hκ n).matrix ⊆ g '' (G : Set ℤ) := by
    rw [hcfc, cfc_map_spectrum (p := IsSelfAdjoint) _ _ ρ.positive.1
      (ρ.matrix.finite_real_spectrum.continuousOn _),
      ρ.positive.1.spectrum_real_eq_range_eigenvalues]
    rintro x ⟨y,⟨i,rfl⟩,rfl⟩
    refine ⟨logarithmicGridIndex κ n (ρ.positive.1.eigenvalues i), ?_, rfl⟩
    simp only [G, Finset.coe_image, Finset.coe_univ, Set.mem_image, Set.mem_univ, true_and]
    exact ⟨i,rfl⟩
  calc
    (spectrum ℝ (roundedDensity ρ hρ κ hκ n).matrix).ncard ≤ (g '' (G : Set ℤ)).ncard :=
      Set.ncard_le_ncard hs (G.finite_toSet.image g)
    _ ≤ (G : Set ℤ).ncard := Set.ncard_image_le G.finite_toSet
    _ = G.card := Set.ncard_coe_finset G
    _ ≤ n + 1 := hg

end QuantumProver.DepolarizingSquashedEntanglement.BCYGeneralizedStein

namespace QuantumProver.DepolarizingSquashedEntanglement.BCYGeneralizedStein

open BCYRelativeEntropy
open QuantumProver.SuperchannelDiscrimination.TensorEntropy

variable {A B I : Type*} [Fintype A] [Fintype B] [Fintype I]
  [DecidableEq A] [DecidableEq B] [DecidableEq I]

def referenceWeight (A B : Type*) [Fintype A] [Fintype B] : ℝ :=
  (1 / (Fintype.card A : ℝ)) * (1 / (Fintype.card B : ℝ))

theorem referenceWeight_bounds [Nonempty A] [Nonempty B] :
    0 < referenceWeight A B ∧ referenceWeight A B ≤ 1 := by
  have ha : (1 : ℝ) ≤ Fintype.card A := by exact_mod_cast Fintype.card_pos (α := A)
  have hb : (1 : ℝ) ≤ Fintype.card B := by exact_mod_cast Fintype.card_pos (α := B)
  have hap : 0 < (1 / (Fintype.card A : ℝ)) := one_div_pos.mpr (zero_lt_one.trans_le ha)
  have hbp : 0 < (1 / (Fintype.card B : ℝ)) := one_div_pos.mpr (zero_lt_one.trans_le hb)
  have hau : (1 / (Fintype.card A : ℝ)) ≤ 1 := by
    simpa only [one_div_one] using one_div_le_one_div_of_le zero_lt_one ha
  have hbu : (1 / (Fintype.card B : ℝ)) ≤ 1 := by
    simpa only [one_div_one] using one_div_le_one_div_of_le zero_lt_one hb
  constructor
  · exact mul_pos hap hbp
  · change (1 / (Fintype.card A : ℝ)) * (1 / (Fintype.card B : ℝ)) ≤ 1
    nlinarith

theorem faithfulReference_matrix [Nonempty A] [Nonempty B] :
    (faithfulReference A B).matrix = referenceWeight A B • (1 : QMatrix (A × B)) := by
  change ((1 / (Fintype.card A : ℝ)) • (1 : QMatrix A)) ⊗ₖ
    ((1 / (Fintype.card B : ℝ)) • (1 : QMatrix B)) = _
  rw [Matrix.smul_kronecker, Matrix.kronecker_smul, smul_smul,
    Matrix.one_kronecker_one]
  rfl

private theorem tensorPower_scalar_identity (a : ℝ) (n : ℕ) :
    tensorPower (a • (1 : QMatrix I)) n = a ^ n • (1 : QMatrix (TensorIndex I n)) := by
  induction n with
  | zero => simp [tensorPower]
  | succ n ih =>
    change tensorPower (a • (1 : QMatrix I)) n ⊗ₖ (a • (1 : QMatrix I)) = _
    rw [ih, Matrix.smul_kronecker, Matrix.kronecker_smul, smul_smul,
      Matrix.one_kronecker_one, pow_succ]
    rfl

theorem faithfulSeparableCopies_matrix [Nonempty A] [Nonempty B] (n : ℕ) :
    (faithfulSeparableCopies (A := A) (B := B) n).val.matrix =
      (referenceWeight A B) ^ n • (1 : QMatrix (CopyIndex A n × CopyIndex B n)) := by
  change Matrix.reindex (copyGrouping A B n) (copyGrouping A B n)
    (tensorPower (faithfulReference A B).matrix n) = _
  rw [faithfulReference_matrix, tensorPower_scalar_identity]
  change (Matrix.reindexLinearEquiv ℝ ℂ (copyGrouping A B n) (copyGrouping A B n))
    ((referenceWeight A B) ^ n • (1 : QMatrix (TensorIndex (A × B) n))) = _
  rw [map_smul, Matrix.reindexLinearEquiv_one]

def threeSeparableMixture (σ₀ σ₁ σ₂ : SeparableDensity A B) : SeparableDensity A B :=
  ⟨{ matrix := (1 / 3 : ℝ) • σ₀.val.matrix + (1 / 3 : ℝ) • σ₁.val.matrix +
       (1 / 3 : ℝ) • σ₂.val.matrix
     positive := ((σ₀.val.positive.smul (by norm_num)).add
       (σ₁.val.positive.smul (by norm_num))).add (σ₂.val.positive.smul (by norm_num))
     trace_one := by
       simp only [Matrix.trace_add, Matrix.trace_smul, σ₀.val.trace_one,
         σ₁.val.trace_one, σ₂.val.trace_one, Complex.real_smul]
       norm_num }, by
    have h12 := (convex_convexHull ℝ _) σ₁.property σ₂.property
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
    have h := (convex_convexHull ℝ _) σ₀.property h12
      (by norm_num : (0 : ℝ) ≤ 1 / 3) (by norm_num : (0 : ℝ) ≤ 2 / 3)
      (by norm_num : (1 / 3 : ℝ) + 2 / 3 = 1)
    norm_num only [smul_add, smul_smul] at h
    simpa only [IsSeparable, add_assoc] using h⟩

theorem threeSeparableMixture_lower_third (σ₀ σ₁ σ₂ : SeparableDensity A B) :
    (1 / 3 : ℝ) • σ₂.val.matrix ≤ (threeSeparableMixture σ₀ σ₁ σ₂).val.matrix := by
  change ((1 / 3 : ℝ) • σ₀.val.matrix + (1 / 3 : ℝ) • σ₁.val.matrix +
    (1 / 3 : ℝ) • σ₂.val.matrix - (1 / 3 : ℝ) • σ₂.val.matrix).PosSemidef
  rw [add_sub_cancel_right]
  exact (σ₀.val.positive.smul (by norm_num)).add (σ₁.val.positive.smul (by norm_num))

theorem threeSeparableMixture_lower_first (σ₀ σ₁ σ₂ : SeparableDensity A B) :
    (1 / 3 : ℝ) • σ₀.val.matrix ≤ (threeSeparableMixture σ₀ σ₁ σ₂).val.matrix := by
  change ((1 / 3 : ℝ) • σ₀.val.matrix + (1 / 3 : ℝ) • σ₁.val.matrix +
    (1 / 3 : ℝ) • σ₂.val.matrix - (1 / 3 : ℝ) • σ₀.val.matrix).PosSemidef
  have he : (1 / 3 : ℝ) • σ₀.val.matrix + (1 / 3 : ℝ) • σ₁.val.matrix +
      (1 / 3 : ℝ) • σ₂.val.matrix - (1 / 3 : ℝ) • σ₀.val.matrix =
        (1 / 3 : ℝ) • σ₁.val.matrix + (1 / 3 : ℝ) • σ₂.val.matrix := by abel
  rw [he]
  exact (σ₁.val.positive.smul (by norm_num)).add (σ₂.val.positive.smul (by norm_num))

theorem threeSeparableMixture_posDef (σ₀ σ₁ σ₂ : SeparableDensity A B)
    (hσ₂ : σ₂.val.matrix.PosDef) :
    (threeSeparableMixture σ₀ σ₁ σ₂).val.matrix.PosDef :=
  Matrix.PosDef.posSemidef_add
    ((σ₀.val.positive.smul (by norm_num)).add (σ₁.val.positive.smul (by norm_num)))
    (hσ₂.smul (by norm_num))

def faithfulFloorKappa (A B : Type*) [Fintype A] [Fintype B] : ℝ :=
  -Real.log (referenceWeight A B / 3)

theorem faithfulFloorKappa_pos [Nonempty A] [Nonempty B] :
    0 < faithfulFloorKappa A B := by
  obtain ⟨hp,hu⟩ := referenceWeight_bounds (A := A) (B := B)
  exact neg_pos.mpr (Real.log_neg (by positivity) (by linarith))

theorem faithfulFloorKappa_exp [Nonempty A] [Nonempty B] :
    Real.exp (-faithfulFloorKappa A B) = referenceWeight A B / 3 := by
  rw [faithfulFloorKappa, neg_neg, Real.exp_log (by
    have hp := (referenceWeight_bounds (A := A) (B := B)).1
    positivity)]

theorem threeSeparableMixture_exponential_floor [Nonempty A] [Nonempty B]
    (n : ℕ) (hn : 1 ≤ n)
    (σ₀ σ₁ : SeparableDensity (CopyIndex A n) (CopyIndex B n)) :
    Real.exp (-faithfulFloorKappa A B * (n : ℝ)) •
        (1 : QMatrix (CopyIndex A n × CopyIndex B n)) ≤
      (threeSeparableMixture σ₀ σ₁ (faithfulSeparableCopies n)).val.matrix := by
  have hw : 0 ≤ referenceWeight A B := (referenceWeight_bounds (A := A) (B := B)).1.le
  have hscalar : Real.exp (-faithfulFloorKappa A B * (n : ℝ)) ≤
      (1 / 3 : ℝ) * referenceWeight A B ^ n := by
    cases n with
    | zero => omega
    | succ k =>
      have hp : (1 / 3 : ℝ) ^ (k + 1) ≤ 1 / 3 := by
        have ht : (1 / 3 : ℝ) ^ k ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
        rw [pow_succ]
        nlinarith
      calc
        Real.exp (-faithfulFloorKappa A B * ((k + 1 : ℕ) : ℝ)) =
            Real.exp (-faithfulFloorKappa A B) ^ (k + 1) := by
          rw [mul_comm, Real.exp_nat_mul]
        _ = (referenceWeight A B / 3) ^ (k + 1) := by rw [faithfulFloorKappa_exp]
        _ = referenceWeight A B ^ (k + 1) * (1 / 3 : ℝ) ^ (k + 1) := by
          rw [div_eq_mul_inv, mul_pow]
          norm_num
        _ ≤ referenceWeight A B ^ (k + 1) * (1 / 3 : ℝ) :=
          mul_le_mul_of_nonneg_left hp (pow_nonneg hw _)
        _ = (1 / 3 : ℝ) * referenceWeight A B ^ (k + 1) := mul_comm _ _
  calc
    Real.exp (-faithfulFloorKappa A B * (n : ℝ)) •
        (1 : QMatrix (CopyIndex A n × CopyIndex B n)) ≤
      ((1 / 3 : ℝ) * referenceWeight A B ^ n) • (1 : QMatrix _) :=
        smul_le_smul_of_nonneg_right hscalar Matrix.PosSemidef.one.nonneg
    _ = (1 / 3 : ℝ) • (faithfulSeparableCopies (A := A) (B := B) n).val.matrix := by
      rw [faithfulSeparableCopies_matrix, smul_smul]
    _ ≤ (threeSeparableMixture σ₀ σ₁ (faithfulSeparableCopies n)).val.matrix :=
      threeSeparableMixture_lower_third _ _ _

end QuantumProver.DepolarizingSquashedEntanglement.BCYGeneralizedStein

namespace QuantumProver.DepolarizingSquashedEntanglement.BCYGeneralizedStein

open BCYRelativeEntropy
open QuantumProver.QuantumRelativeEntropyContinuity
open QuantumProver.SuperchannelDiscrimination.FlaggedStates

variable {A B I : Type*} [Fintype A] [Fintype B] [Fintype I]
  [DecidableEq A] [DecidableEq B] [DecidableEq I]

private theorem matrix_cfc_log_affine {R : QMatrix I} (hR : R.IsHermitian)
    (a b : ℝ) : cfc Real.log (a • R + b • (1 : QMatrix I)) =
      cfc (fun x : ℝ => Real.log (a * x + b)) R := by
  have hm : cfc (fun x : ℝ => a * x + b) R = a • R + b • (1 : QMatrix I) := by
    rw [cfc_add_const (p := IsSelfAdjoint) b (fun x : ℝ => a * x) R
      (R.finite_real_spectrum.continuousOn _) hR,
      cfc_const_mul_id (p := IsSelfAdjoint) a R hR, Algebra.algebraMap_eq_smul_one]
  rw [← hm]
  exact (cfc_comp' (p := IsSelfAdjoint) Real.log (fun x : ℝ => a * x + b) R
    ((R.finite_real_spectrum.image _).continuousOn _)
    (R.finite_real_spectrum.continuousOn _) hR).symm

def referenceMixtureMatrix [Nonempty A] [Nonempty B]
    (σ : Density (A × B)) (δ : ℝ) : QMatrix (A × B) :=
  (1 - δ) • σ.matrix + δ • (faithfulReference A B).matrix

def referenceMixtureObjective [Nonempty A] [Nonempty B]
    (ρ σ : Density (A × B)) (δ : ℝ) : ℝ :=
  (ρ.matrix * (cfc Real.log ρ.matrix - cfc Real.log (referenceMixtureMatrix σ δ))).trace.re

theorem referenceMixture_log [Nonempty A] [Nonempty B]
    (σ : Density (A × B)) (δ : ℝ) :
    cfc Real.log (referenceMixtureMatrix σ δ) =
      cfc (fun x : ℝ => Real.log ((1 - δ) * x + δ * referenceWeight A B)) σ.matrix := by
  rw [referenceMixtureMatrix, faithfulReference_matrix, smul_smul]
  exact matrix_cfc_log_affine σ.positive.1 _ _

theorem referenceMixtureObjective_tendsto [Nonempty A] [Nonempty B]
    (ρ σ : Density (A × B)) (hs : HasSupportIn ρ.matrix σ.matrix) :
    Tendsto (referenceMixtureObjective ρ σ) (𝓝 (0 : ℝ))
      (𝓝 ((ρ.matrix * (cfc Real.log ρ.matrix - cfc Real.log σ.matrix)).trace.re)) := by
  have ht (i : A × B) : Tendsto
      (fun δ : ℝ => spectralWeight ρ.matrix σ.positive.1 i *
        Real.log ((1 - δ) * σ.positive.1.eigenvalues i + δ * referenceWeight A B))
      (𝓝 0) (𝓝 (spectralWeight ρ.matrix σ.positive.1 i *
        Real.log (σ.positive.1.eigenvalues i))) := by
    by_cases hi : σ.positive.1.eigenvalues i = 0
    · rw [(hasSupportIn_iff_zero_spectralWeight ρ.positive σ.positive.1).mp hs i hi]
      simp
    · have hc : ContinuousAt
          (fun δ : ℝ => Real.log ((1 - δ) * σ.positive.1.eigenvalues i +
            δ * referenceWeight A B)) 0 := by
        apply ContinuousAt.log
        · fun_prop
        · simpa using hi
      simpa using tendsto_const_nhds.mul hc.tendsto
  have hsum := tendsto_finset_sum Finset.univ (fun i _ => ht i)
  have hself : Tendsto (fun _ : ℝ => (ρ.matrix * cfc Real.log ρ.matrix).trace.re)
      (𝓝 0) (𝓝 ((ρ.matrix * cfc Real.log ρ.matrix).trace.re)) := tendsto_const_nhds
  have h := hself.sub hsum
  convert h using 1
  · ext δ
    simp only [referenceMixtureObjective, Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re]
    rw [referenceMixture_log, trace_mul_cfc_re_eq_sum ρ.matrix σ.positive.1]
  · simp only [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re]
    rw [trace_mul_cfc_re_eq_sum ρ.matrix σ.positive.1 Real.log]

theorem exists_faithful_separable_near [Nonempty A] [Nonempty B]
    (ρ : Density (A × B)) {ε : ℝ} (hε : 0 < ε) :
    ∃ σ : SeparableDensity A B, σ.val.matrix.PosDef ∧
      umegakiNats ρ.matrix σ.val.matrix < (relativeEntropyEntanglementReal ρ + ε : ℝ) := by
  obtain ⟨σ,hnear⟩ := exists_separable_near ρ (ε := ε / 2) (by positivity)
  have hs : HasSupportIn ρ.matrix σ.val.matrix := by
    by_contra hn
    rw [(umegakiNats_eq_top_iff _ _).mpr hn] at hnear
    exact not_lt_of_ge le_top hnear
  have hnearReal : (ρ.matrix * (cfc Real.log ρ.matrix - cfc Real.log σ.val.matrix)).trace.re <
      relativeEntropyEntanglementReal ρ + ε / 2 := by
    rw [umegakiNats_of_support _ _ hs] at hnear
    exact EReal.coe_lt_coe_iff.mp hnear
  have hlt : (ρ.matrix * (cfc Real.log ρ.matrix - cfc Real.log σ.val.matrix)).trace.re <
      relativeEntropyEntanglementReal ρ + ε := by linarith
  have ho : ∀ᶠ δ : ℝ in 𝓝[>] 0,
      referenceMixtureObjective ρ σ.val δ < relativeEntropyEntanglementReal ρ + ε :=
    ((referenceMixtureObjective_tendsto ρ σ.val hs).mono_left nhdsWithin_le_nhds).eventually
      (eventually_lt_nhds hlt)
  have hgt : ∀ᶠ δ : ℝ in 𝓝[>] 0, 0 < δ := self_mem_nhdsWithin
  have hltOne : ∀ᶠ δ : ℝ in 𝓝[>] 0, δ < 1 :=
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds
  obtain ⟨δ,hδ,hδOne,hobj⟩ := (hgt.and (hltOne.and ho)).exists
  have hp := regularizedSeparable_posDef σ δ hδ hδOne.le
  refine ⟨regularizedSeparable σ δ hδ.le hδOne.le, hp, ?_⟩
  rw [umegakiNats_of_support _ _ (hasSupportIn_of_posDef ρ.matrix hp)]
  apply EReal.coe_lt_coe_iff.mpr
  exact hobj

end QuantumProver.DepolarizingSquashedEntanglement.BCYGeneralizedStein

namespace QuantumProver.DepolarizingSquashedEntanglement.BCYGeneralizedStein

open BCYRelativeEntropy
open QuantumProver.SuperchannelDiscrimination.FlaggedStates

variable {A B : Type*} [Fintype A] [Fintype B]
  [DecidableEq A] [DecidableEq B] [Nonempty A] [Nonempty B]

theorem exists_faithful_block_near (ρ : Density (A × B)) {ε : ℝ} (hε : 0 < ε) :
    ∃ m : ℕ, 1 ≤ m ∧
      ∃ σ : SeparableDensity (CopyIndex A m) (CopyIndex B m), σ.val.matrix.PosDef ∧
        ((tensorCopies ρ m).matrix * (cfc Real.log (tensorCopies ρ m).matrix -
          cfc Real.log σ.val.matrix)).trace.re / (m : ℝ) <
            regularizedRelativeEntropyEntanglementNat ρ + ε := by
  have he : ∀ᶠ m : ℕ in atTop,
      relativeEntropyEntanglementReal (tensorCopies ρ m) / (m : ℝ) <
        regularizedRelativeEntropyEntanglementNat ρ + ε / 2 :=
    (tendsto_relativeEntropyEntanglement_rate ρ).eventually
      (eventually_lt_nhds (by linarith : regularizedRelativeEntropyEntanglementNat ρ <
        regularizedRelativeEntropyEntanglementNat ρ + ε / 2))
  obtain ⟨m,hm,hrate⟩ := ((eventually_ge_atTop 1).and he).exists
  have hmp : 0 < (m : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hm)
  letI : Nonempty (CopyIndex A m) := Fintype.card_pos_iff.mp (by
    change 0 < Fintype.card (QuantumProver.SuperchannelDiscrimination.TensorEntropy.TensorIndex A m)
    rw [QuantumProver.SuperchannelDiscrimination.TensorEntropy.tensorIndex_card]
    positivity)
  letI : Nonempty (CopyIndex B m) := Fintype.card_pos_iff.mp (by
    change 0 < Fintype.card (QuantumProver.SuperchannelDiscrimination.TensorEntropy.TensorIndex B m)
    rw [QuantumProver.SuperchannelDiscrimination.TensorEntropy.tensorIndex_card]
    positivity)
  obtain ⟨σ,hσpd,hval⟩ := exists_faithful_separable_near (tensorCopies ρ m)
    (ε := (m : ℝ) * ε / 2) (by positivity)
  rw [umegakiNats_of_support _ _ (hasSupportIn_of_posDef _ hσpd)] at hval
  have hv := EReal.coe_lt_coe_iff.mp hval
  refine ⟨m,hm,σ,hσpd,?_⟩
  calc
    ((tensorCopies ρ m).matrix * (cfc Real.log (tensorCopies ρ m).matrix -
        cfc Real.log σ.val.matrix)).trace.re / (m : ℝ) <
      (relativeEntropyEntanglementReal (tensorCopies ρ m) + (m : ℝ) * ε / 2) / (m : ℝ) :=
        div_lt_div_of_pos_right hv hmp
    _ = relativeEntropyEntanglementReal (tensorCopies ρ m) / (m : ℝ) + ε / 2 := by
      field_simp [hmp.ne']
    _ < regularizedRelativeEntropyEntanglementNat ρ + ε := by linarith

end QuantumProver.DepolarizingSquashedEntanglement.BCYGeneralizedStein

namespace QuantumProver.DepolarizingSquashedEntanglement.BCYGeneralizedStein

open BCYRelativeEntropy BCYPinching

variable {A B : Type*} [Fintype A] [Fintype B]
  [DecidableEq A] [DecidableEq B] [Nonempty A] [Nonempty B]

theorem exists_faithful_block_below_rate (ρ : Density (A × B)) {R : ℝ}
    (hR : regularizedRelativeEntropyEntanglementNat ρ < R) :
    ∃ m : ℕ, 1 ≤ m ∧
      ∃ σ : SeparableDensity (CopyIndex A m) (CopyIndex B m), σ.val.matrix.PosDef ∧
        finiteRelativeEntropyNats (tensorCopies ρ m).matrix σ.val.matrix / (m : ℝ) < R := by
  obtain ⟨m,hm,σ,hσ,hnear⟩ := exists_faithful_block_near ρ
    (ε := R - regularizedRelativeEntropyEntanglementNat ρ) (sub_pos.mpr hR)
  refine ⟨m,hm,σ,hσ,?_⟩
  simpa only [finiteRelativeEntropyNats, add_sub_cancel] using hnear

omit [Nonempty A] [Nonempty B] in
theorem threeSeparableMixture_lower_second
    (σ₀ σ₁ σ₂ : SeparableDensity A B) :
    (1 / 3 : ℝ) • σ₁.val.matrix ≤ (threeSeparableMixture σ₀ σ₁ σ₂).val.matrix := by
  change ((1 / 3 : ℝ) • σ₀.val.matrix + (1 / 3 : ℝ) • σ₁.val.matrix +
    (1 / 3 : ℝ) • σ₂.val.matrix - (1 / 3 : ℝ) • σ₁.val.matrix).PosSemidef
  have he : (1 / 3 : ℝ) • σ₀.val.matrix + (1 / 3 : ℝ) • σ₁.val.matrix +
      (1 / 3 : ℝ) • σ₂.val.matrix - (1 / 3 : ℝ) • σ₁.val.matrix =
        (1 / 3 : ℝ) • σ₀.val.matrix + (1 / 3 : ℝ) • σ₂.val.matrix := by abel
  rw [he]
  exact (σ₀.val.positive.smul (by norm_num)).add (σ₂.val.positive.smul (by norm_num))

def roundedSeparableMixture (n : ℕ)
    (σ₀ σ₁ : SeparableDensity (CopyIndex A n) (CopyIndex B n)) :
    Density (CopyIndex A n × CopyIndex B n) :=
  roundedDensity (threeSeparableMixture σ₀ σ₁ (faithfulSeparableCopies n)).val
    (threeSeparableMixture_posDef _ _ _ (faithfulSeparableCopies_posDef n))
    (faithfulFloorKappa A B) faithfulFloorKappa_pos n

theorem roundedSeparableMixture_posDef (n : ℕ)
    (σ₀ σ₁ : SeparableDensity (CopyIndex A n) (CopyIndex B n)) :
    (roundedSeparableMixture n σ₀ σ₁).matrix.PosDef :=
  roundedDensity_posDef _ _ _ _ _

theorem roundedSeparableMixture_spectrum_ncard (n : ℕ) (hn : 1 ≤ n)
    (σ₀ σ₁ : SeparableDensity (CopyIndex A n) (CopyIndex B n)) :
    (spectrum ℝ (roundedSeparableMixture n σ₀ σ₁).matrix).ncard ≤ n + 1 :=
  roundedDensity_spectrum_ncard _ _ faithfulFloorKappa_pos n
    (threeSeparableMixture_exponential_floor n hn σ₀ σ₁)

theorem roundedSeparableMixture_component_domination (n : ℕ)
    (σ₀ σ₁ : SeparableDensity (CopyIndex A n) (CopyIndex B n)) :
    σ₀.val.matrix ≤ (3 * Real.exp (faithfulFloorKappa A B)) •
        (roundedSeparableMixture n σ₀ σ₁).matrix ∧
      σ₁.val.matrix ≤ (3 * Real.exp (faithfulFloorKappa A B)) •
        (roundedSeparableMixture n σ₀ σ₁).matrix := by
  let κ := faithfulFloorKappa A B
  let σ := threeSeparableMixture σ₀ σ₁ (faithfulSeparableCopies n)
  have hr : Real.exp (-κ) • σ.val.matrix ≤
      (roundedSeparableMixture n σ₀ σ₁).matrix :=
    (roundedDensity_bounds _ _ faithfulFloorKappa_pos n).1
  have hc : (3 * Real.exp κ) * (Real.exp (-κ) * (1 / 3)) = 1 := by
    rw [Real.exp_neg]
    field_simp [Real.exp_ne_zero]
  have hcomponent (τ : SeparableDensity (CopyIndex A n) (CopyIndex B n))
      (hτ : (1 / 3 : ℝ) • τ.val.matrix ≤ σ.val.matrix) :
      τ.val.matrix ≤ (3 * Real.exp κ) • (roundedSeparableMixture n σ₀ σ₁).matrix := by
    have hs : (Real.exp (-κ) * (1 / 3)) • τ.val.matrix ≤
        (roundedSeparableMixture n σ₀ σ₁).matrix := by
      calc
        _ = Real.exp (-κ) • ((1 / 3 : ℝ) • τ.val.matrix) := (smul_smul _ _ _).symm
        _ ≤ Real.exp (-κ) • σ.val.matrix :=
          smul_le_smul_of_nonneg_left hτ (Real.exp_pos _).le
        _ ≤ _ := hr
    have h := smul_le_smul_of_nonneg_left hs (by positivity : 0 ≤ 3 * Real.exp κ)
    simpa only [smul_smul, hc, one_smul] using h
  exact ⟨hcomponent σ₀ (threeSeparableMixture_lower_first _ _ _),
    hcomponent σ₁ (threeSeparableMixture_lower_second _ _ _)⟩

theorem roundedSeparableMixture_exponential_floor (n : ℕ) (hn : 1 ≤ n)
    (σ₀ σ₁ : SeparableDensity (CopyIndex A n) (CopyIndex B n)) :
    Real.exp (-2 * (n : ℝ) * faithfulFloorKappa A B) •
        (1 : QMatrix (CopyIndex A n × CopyIndex B n)) ≤
      (roundedSeparableMixture n σ₀ σ₁).matrix := by
  let κ := faithfulFloorKappa A B
  have hκ : 0 < κ := faithfulFloorKappa_pos
  have hnr : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hs : Real.exp (-2 * (n : ℝ) * κ) ≤ Real.exp (-κ) * Real.exp (-κ * (n : ℝ)) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by nlinarith)
  calc
    _ ≤ (Real.exp (-κ) * Real.exp (-κ * (n : ℝ))) •
        (1 : QMatrix (CopyIndex A n × CopyIndex B n)) :=
      smul_le_smul_of_nonneg_right hs
        (Matrix.PosSemidef.one : (1 : QMatrix (CopyIndex A n × CopyIndex B n)).PosSemidef).nonneg
    _ = Real.exp (-κ) • (Real.exp (-κ * (n : ℝ)) •
        (1 : QMatrix (CopyIndex A n × CopyIndex B n))) :=
      (smul_smul _ _ _).symm
    _ ≤ Real.exp (-κ) •
        (threeSeparableMixture σ₀ σ₁ (faithfulSeparableCopies n)).val.matrix :=
      smul_le_smul_of_nonneg_left (threeSeparableMixture_exponential_floor n hn σ₀ σ₁)
        (Real.exp_pos _).le
    _ ≤ (roundedSeparableMixture n σ₀ σ₁).matrix :=
      (roundedDensity_bounds _ _ faithfulFloorKappa_pos n).1

theorem roundedSeparableMixture_pinching_error (n : ℕ) (hn : 1 ≤ n)
    (ρ : Density (CopyIndex A n × CopyIndex B n))
    (σ₀ σ₁ : SeparableDensity (CopyIndex A n) (CopyIndex B n)) :
    |finiteRelativeEntropyNats ρ.matrix
        (threeSeparableMixture σ₀ σ₁ (faithfulSeparableCopies n)).val.matrix -
      finiteRelativeEntropyNats
        (pinchedDensity ρ (roundedSeparableMixture_posDef n σ₀ σ₁).1).matrix
        (roundedSeparableMixture n σ₀ σ₁).matrix| ≤
      faithfulFloorKappa A B + Real.log ((n : ℝ) + 1) := by
  have hd := roundedDensity_relativeEntropy_displacement ρ
    (threeSeparableMixture σ₀ σ₁ (faithfulSeparableCopies n)).val
    (threeSeparableMixture_posDef σ₀ σ₁ (faithfulSeparableCopies n)
      (faithfulSeparableCopies_posDef (A := A) (B := B) n))
    (faithfulFloorKappa_pos (A := A) (B := B)) n
  change |finiteRelativeEntropyNats ρ.matrix
      (threeSeparableMixture σ₀ σ₁ (faithfulSeparableCopies n)).val.matrix -
    finiteRelativeEntropyNats ρ.matrix (roundedSeparableMixture n σ₀ σ₁).matrix| ≤
      faithfulFloorKappa A B at hd
  have hp := umegakiNats_pinching_cost_of_count ρ
    (roundedSeparableMixture_posDef n σ₀ σ₁) n
    (roundedSeparableMixture_spectrum_ncard n hn σ₀ σ₁)
  rw [BCYPinching.umegakiNats_of_posDef _ (roundedSeparableMixture_posDef n σ₀ σ₁),
    BCYPinching.umegakiNats_of_posDef _ (roundedSeparableMixture_posDef n σ₀ σ₁),
    ← EReal.coe_sub, EReal.coe_le_coe_iff] at hp
  have hnonneg := finiteRelativeEntropyNats_sub_pinching_nonneg ρ
    (roundedSeparableMixture_posDef n σ₀ σ₁).1
  have hlog : 0 ≤ Real.log ((n : ℝ) + 1) :=
    Real.log_nonneg (le_add_of_nonneg_left (Nat.cast_nonneg n))
  obtain ⟨hdl,hdu⟩ := abs_le.mp hd
  apply abs_le.mpr
  constructor <;> linarith

end QuantumProver.DepolarizingSquashedEntanglement.BCYGeneralizedStein

namespace QuantumProver.DepolarizingSquashedEntanglement.BCYGeneralizedStein

open BCYRelativeEntropy BCYPinching

def roundingPinchingError (κ : ℝ) (n : ℕ) : ℝ :=
  (κ + Real.log ((n : ℝ) + 1)) / (n : ℝ)

theorem roundingPinchingError_tendsto (κ : ℝ) :
    Tendsto (roundingPinchingError κ) atTop (𝓝 0) := by
  have ht : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_mono (fun _ => le_add_of_nonneg_right (show (0 : ℝ) ≤ 1 by norm_num))
      tendsto_natCast_atTop_atTop
  have hl : Tendsto (fun n : ℕ => Real.log ((n : ℝ) + 1) / (n : ℝ))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, pow_one, one_mul, add_neg_cancel_right] using
      (Real.tendsto_pow_log_div_mul_add_atTop 1 (-1) 1 one_ne_zero).comp ht
  change Tendsto (fun n : ℕ => (κ + Real.log ((n : ℝ) + 1)) / (n : ℝ)) atTop (𝓝 0)
  simpa only [add_div, zero_add] using
    (tendsto_const_div_atTop_nhds_zero_nat κ).add hl

variable {A B : Type*} [Fintype A] [Fintype B]
  [DecidableEq A] [DecidableEq B] [Nonempty A] [Nonempty B]

theorem roundedSeparableMixture_rate_le_pinched_rate (n : ℕ) (hn : 1 ≤ n)
    (ρ : Density (CopyIndex A n × CopyIndex B n))
    (σ₀ σ₁ : SeparableDensity (CopyIndex A n) (CopyIndex B n)) :
    finiteRelativeEntropyNats ρ.matrix
        (threeSeparableMixture σ₀ σ₁ (faithfulSeparableCopies n)).val.matrix / (n : ℝ) ≤
      finiteRelativeEntropyNats
        (pinchedDensity ρ (roundedSeparableMixture_posDef n σ₀ σ₁).1).matrix
        (roundedSeparableMixture n σ₀ σ₁).matrix / (n : ℝ) +
      roundingPinchingError (faithfulFloorKappa A B) n := by
  have h := (abs_le.mp (roundedSeparableMixture_pinching_error n hn ρ σ₀ σ₁)).2
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hd := div_le_div_of_nonneg_right h hn0.le
  rw [sub_div] at hd
  dsimp only [roundingPinchingError]
  linarith

theorem regularizedER_le_threeSeparableMixture_rate (ρ : Density (A × B))
    (n : ℕ) (hn : 1 ≤ n)
    (σ₀ σ₁ : SeparableDensity (CopyIndex A n) (CopyIndex B n)) :
    regularizedRelativeEntropyEntanglementNat ρ ≤
      finiteRelativeEntropyNats (tensorCopies ρ n).matrix
        (threeSeparableMixture σ₀ σ₁ (faithfulSeparableCopies n)).val.matrix / (n : ℝ) := by
  have hsep := relativeEntropyEntanglementNat_le (tensorCopies ρ n)
    (threeSeparableMixture σ₀ σ₁ (faithfulSeparableCopies n)).val
    (threeSeparableMixture σ₀ σ₁ (faithfulSeparableCopies n)).property
  rw [← coe_relativeEntropyEntanglementReal,
    BCYPinching.umegakiNats_of_posDef _
      (threeSeparableMixture_posDef σ₀ σ₁ (faithfulSeparableCopies n)
        (faithfulSeparableCopies_posDef (A := A) (B := B) n)),
    EReal.coe_le_coe_iff] at hsep
  exact (regularizedRelativeEntropyEntanglementNat_le_rate ρ n (by omega)).trans
    (div_le_div_of_nonneg_right hsep (Nat.cast_nonneg n))

end QuantumProver.DepolarizingSquashedEntanglement.BCYGeneralizedStein

namespace QuantumProver.DepolarizingSquashedEntanglement.BCYGeneralizedStein

open BCYRelativeEntropy BCYPinching BCYCommutingTests BCYCompositeTesting

variable {A B : Type*} [Fintype A] [Fintype B]
  [DecidableEq A] [DecidableEq B] [Nonempty A] [Nonempty B]

def mixtureLikelihoodTest (ρ : Density (A × B)) (n : ℕ)
    (σ₀ σ₁ : SeparableDensity (CopyIndex A n) (CopyIndex B n)) (a : ℝ) :
    BinaryEffect (CopyIndex A n × CopyIndex B n) :=
  likelihoodTest (tensorCopies ρ n) (roundedSeparableMixture n σ₀ σ₁)
    (roundedSeparableMixture_posDef n σ₀ σ₁) ((n : ℝ) * a)

def mixtureThresholdMass (ρ : Density (A × B)) (n : ℕ)
    (σ₀ σ₁ : SeparableDensity (CopyIndex A n) (CopyIndex B n)) (a : ℝ) : ℝ :=
  acceptance (tensorCopies ρ n) (mixtureLikelihoodTest ρ n σ₀ σ₁ a)

theorem mixtureThresholdMass_bounds (ρ : Density (A × B)) (n : ℕ)
    (σ₀ σ₁ : SeparableDensity (CopyIndex A n) (CopyIndex B n)) (a : ℝ) :
    0 ≤ mixtureThresholdMass ρ n σ₀ σ₁ a ∧ mixtureThresholdMass ρ n σ₀ σ₁ a ≤ 1 :=
  acceptance_bounds _ _

theorem mixtureLikelihoodTest_beta_le_exp (ρ : Density (A × B)) (n : ℕ)
    (σ₀ σ₁ : SeparableDensity (CopyIndex A n) (CopyIndex B n)) (a : ℝ) :
    acceptance (roundedSeparableMixture n σ₀ σ₁) (mixtureLikelihoodTest ρ n σ₀ σ₁ a) ≤
      Real.exp (-(n : ℝ) * a) := by
  simpa only [mixtureLikelihoodTest, neg_mul] using
    likelihoodTest_beta_le_exp (tensorCopies ρ n) (roundedSeparableMixture n σ₀ σ₁)
      (roundedSeparableMixture_posDef n σ₀ σ₁) ((n : ℝ) * a)

theorem threeSeparableMixture_rate_le_three_regions (ρ : Density (A × B))
    (n : ℕ) (hn : 1 ≤ n)
    (σ₀ σ₁ : SeparableDensity (CopyIndex A n) (CopyIndex B n))
    (lower upper : ℝ) (horder : lower ≤ upper) :
    finiteRelativeEntropyNats (tensorCopies ρ n).matrix
        (threeSeparableMixture σ₀ σ₁ (faithfulSeparableCopies n)).val.matrix / (n : ℝ) ≤
      lower + (upper - lower) * mixtureThresholdMass ρ n σ₀ σ₁ lower +
        (2 * faithfulFloorKappa A B - upper) * mixtureThresholdMass ρ n σ₀ σ₁ upper +
        roundingPinchingError (faithfulFloorKappa A B) n := by
  have h := pinched_finiteRelativeEntropyNats_div_le_three_regions
    (tensorCopies ρ n) (roundedSeparableMixture n σ₀ σ₁)
    (roundedSeparableMixture_posDef n σ₀ σ₁) n hn
    (faithfulFloorKappa A B) lower upper horder
    (roundedSeparableMixture_exponential_floor n hn σ₀ σ₁)
  rw [likelihoodTest_acceptance_pinched_eq_physical,
    likelihoodTest_acceptance_pinched_eq_physical] at h
  have herr := roundedSeparableMixture_rate_le_pinched_rate n hn (tensorCopies ρ n) σ₀ σ₁
  dsimp only [mixtureThresholdMass, mixtureLikelihoodTest]
  linarith

theorem mixture_threshold_limits_contradict_rate_gap (ρ : Density (A × B))
    (σ₀ σ₁ : (n : ℕ) → SeparableDensity (CopyIndex A n) (CopyIndex B n))
    (Re epsilon eta : ℝ) (he : epsilon < 1) (heta0 : 0 < eta) (heta : eta ≤ epsilon)
    (hgap : Re < regularizedRelativeEntropyEntanglementNat ρ)
    (hlow : ∀ slack : ℝ, 0 < slack →
      liminf (fun n => (mixtureThresholdMass ρ n (σ₀ n) (σ₁ n) (Re + slack) : EReal))
        atTop ≤ ((1 - epsilon : ℝ) : EReal))
    (hhigh : ∀ slack : ℝ, 0 < slack →
      Tendsto (fun n => mixtureThresholdMass ρ n (σ₀ n) (σ₁ n)
        (regularizedRelativeEntropyEntanglementNat ρ +
          BCYThreeRegions.epsilon0 epsilon eta (regularizedRelativeEntropyEntanglementNat ρ) Re +
          slack)) atTop (𝓝 0)) : False := by
  let Rprime := regularizedRelativeEntropyEntanglementNat ρ
  let e0 := BCYThreeRegions.epsilon0 epsilon eta Rprime Re
  let a : ℕ → ℝ := fun n => finiteRelativeEntropyNats (tensorCopies ρ n).matrix
    (threeSeparableMixture (σ₀ n) (σ₁ n) (faithfulSeparableCopies n)).val.matrix / (n : ℝ)
  let u : ℝ → ℕ → ℝ := fun slack n =>
    mixtureThresholdMass ρ n (σ₀ n) (σ₁ n) (Re + slack)
  let v : ℝ → ℕ → ℝ := fun slack n =>
    mixtureThresholdMass ρ n (σ₀ n) (σ₁ n) (Rprime + e0 + slack)
  have he0 : 0 ≤ e0 := BCYThreeRegions.epsilon0_nonneg he heta hgap.le
  have hpoint (slack : ℝ) (_hs : 0 < slack) : ∀ᶠ n in atTop,
      a n ≤ Re + slack + (Rprime + e0 - Re) * u slack n +
        (2 * faithfulFloorKappa A B - Rprime - e0 - slack) * v slack n +
        roundingPinchingError (faithfulFloorKappa A B) n := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have h := threeSeparableMixture_rate_le_three_regions ρ n hn (σ₀ n) (σ₁ n)
      (Re + slack) (Rprime + e0 + slack) (by dsimp [Rprime] at *; linarith)
    convert h using 1 <;> dsimp [a, u, v] <;> ring
  have hc := BCYAsymptoticGap.liminf_le_three_region_contraction a u v
    (fun _ => roundingPinchingError (faithfulFloorKappa A B))
    Re Rprime (faithfulFloorKappa A B) epsilon eta he heta hgap.le
    (fun slack _ => Filter.Eventually.of_forall (fun n => mixtureThresholdMass_bounds ρ n _ _ _))
    hlow hhigh (fun _ _ => roundingPinchingError_tendsto _) hpoint
  have hl : (Rprime : EReal) ≤ liminf (fun n => (a n : EReal)) atTop := by
    apply Filter.le_liminf_of_le (h := ?_)
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact EReal.coe_le_coe_iff.mpr (regularizedER_le_threeSeparableMixture_rate ρ n hn _ _)
  have hr : Re + (1 - eta) * (Rprime - Re) < Rprime := by
    dsimp [Rprime] at *
    nlinarith
  exact (not_le_of_gt hr) (EReal.coe_le_coe_iff.mp (hl.trans hc))

end QuantumProver.DepolarizingSquashedEntanglement.BCYGeneralizedStein

namespace QuantumProver.DepolarizingSquashedEntanglement.BCYGeneralizedStein

open BCYRelativeEntropy BCYCompositeTesting

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

theorem hypothesisTestingNat_nonneg (ρ : Density (A × B)) {epsilon : ℝ}
    (he : 0 ≤ epsilon) : 0 ≤ hypothesisTestingNat ρ epsilon := by
  have hb : fixedErrorBeta ρ epsilon ≤ 1 := by
    let T : {T : BinaryEffect (A × B) // 1 - epsilon ≤ acceptance ρ T} :=
      ⟨acceptAllEffect _, by simpa only [acceptance_acceptAll] using sub_le_self 1 he⟩
    apply iInf_le_of_le T
    change ENNReal.ofReal (worstSeparableBeta (acceptAllEffect (A × B))) ≤ 1
    rw [worstSeparableBeta_acceptAll ρ, ENNReal.ofReal_one]
  have hl := ENNReal.log_monotone hb
  simpa only [hypothesisTestingNat, ENNReal.log_one, neg_zero] using EReal.neg_le_neg_iff.mpr hl

theorem hypothesisTestingNat_ne_bot (ρ : Density (A × B)) {epsilon : ℝ}
    (he : 0 ≤ epsilon) : hypothesisTestingNat ρ epsilon ≠ ⊥ :=
  ne_of_gt ((EReal.bot_lt_coe 0).trans_le (hypothesisTestingNat_nonneg ρ he))

theorem hypothesisTestingNat_ne_top (ρ : Density (A × B)) {epsilon : ℝ}
    (he : epsilon < 1) : hypothesisTestingNat ρ epsilon ≠ ⊤ :=
  ne_of_lt ((hypothesisTestingNat_le ρ he).trans_lt (EReal.coe_lt_top _))

theorem coe_hypothesisTestingNat_toReal (ρ : Density (A × B)) {epsilon : ℝ}
    (he0 : 0 ≤ epsilon) (he1 : epsilon < 1) :
    ((hypothesisTestingNat ρ epsilon).toReal : EReal) = hypothesisTestingNat ρ epsilon :=
  EReal.coe_toReal (hypothesisTestingNat_ne_top ρ he1) (hypothesisTestingNat_ne_bot ρ he0)

def fixedErrorRateReal (ρ : Density (A × B)) (epsilon : ℝ) (n : ℕ) : ℝ :=
  (hypothesisTestingNat (tensorCopies ρ n) epsilon).toReal / (n : ℝ)

theorem fixedErrorRateReal_nonneg (ρ : Density (A × B)) {epsilon : ℝ}
    (he : 0 ≤ epsilon) (n : ℕ) : 0 ≤ fixedErrorRateReal ρ epsilon n :=
  div_nonneg (EReal.toReal_nonneg (hypothesisTestingNat_nonneg (tensorCopies ρ n) he))
    (Nat.cast_nonneg n)

theorem coe_fixedErrorRateReal (ρ : Density (A × B)) {epsilon : ℝ}
    (he0 : 0 ≤ epsilon) (he1 : epsilon < 1) (n : ℕ) :
    (fixedErrorRateReal ρ epsilon n : EReal) =
      hypothesisTestingNat (tensorCopies ρ n) epsilon * ((1 / (n : ℝ) : ℝ) : EReal) := by
  rw [fixedErrorRateReal, div_eq_mul_inv, EReal.coe_mul,
    coe_hypothesisTestingNat_toReal _ he0 he1, one_div]

def worstTestingAlternative (ρ : Density (A × B)) (epsilon : ℝ)
    (he0 : 0 ≤ epsilon) (n : ℕ) : SeparableDensity (CopyIndex A n) (CopyIndex B n) :=
  Classical.choose (BCYTestingMinimax.exists_hypothesisTestingNat_eq_singleAlternative
    (tensorCopies ρ n) he0)

theorem worstTestingAlternative_hypothesisTesting (ρ : Density (A × B))
    (epsilon : ℝ) (he0 : 0 ≤ epsilon) (n : ℕ) :
    hypothesisTestingNat (tensorCopies ρ n) epsilon =
      hypothesisTestingSingleNat (tensorCopies ρ n)
        (worstTestingAlternative ρ epsilon he0 n).val epsilon :=
  Classical.choose_spec (BCYTestingMinimax.exists_hypothesisTestingNat_eq_singleAlternative
    (tensorCopies ρ n) he0)

end QuantumProver.DepolarizingSquashedEntanglement.BCYGeneralizedStein

namespace QuantumProver.DepolarizingSquashedEntanglement.BCYGeneralizedStein

open BCYRelativeEntropy BCYCompositeTesting BCYTestingPrimitives

variable {A B : Type*} [Fintype A] [Fintype B]
  [DecidableEq A] [DecidableEq B] [Nonempty A] [Nonempty B]

theorem mixtureLikelihoodTest_component_beta_bounds (ρ : Density (A × B)) (n : ℕ)
    (σ₀ σ₁ : SeparableDensity (CopyIndex A n) (CopyIndex B n)) (a : ℝ) :
    acceptance σ₀.val (mixtureLikelihoodTest ρ n σ₀ σ₁ a) ≤
        (3 * Real.exp (faithfulFloorKappa A B)) * Real.exp (-(n : ℝ) * a) ∧
      acceptance σ₁.val (mixtureLikelihoodTest ρ n σ₀ σ₁ a) ≤
        (3 * Real.exp (faithfulFloorKappa A B)) * Real.exp (-(n : ℝ) * a) := by
  have hβ := mixtureLikelihoodTest_beta_le_exp ρ n σ₀ σ₁ a
  have hC : 0 ≤ 3 * Real.exp (faithfulFloorKappa A B) := by positivity
  obtain ⟨h₀,h₁⟩ := roundedSeparableMixture_component_domination n σ₀ σ₁
  exact ⟨(acceptance_le_mul_of_alternative_le σ₀.val _ _ h₀).trans
      (mul_le_mul_of_nonneg_left hβ hC),
    (acceptance_le_mul_of_alternative_le σ₁.val _ _ h₁).trans
      (mul_le_mul_of_nonneg_left hβ hC)⟩

theorem mixtureThresholdMass_imp_fixedErrorRate (ρ : Density (A × B))
    {epsilon : ℝ} (he0 : 0 ≤ epsilon) (he1 : epsilon < 1)
    (n : ℕ) (hn : 1 ≤ n)
    (σ₁ : SeparableDensity (CopyIndex A n) (CopyIndex B n)) (a : ℝ)
    (ha : 1 - epsilon ≤ mixtureThresholdMass ρ n
      (worstTestingAlternative ρ epsilon he0 n) σ₁ a) :
    a - Real.log (3 * Real.exp (faithfulFloorKappa A B)) / (n : ℝ) ≤
      fixedErrorRateReal ρ epsilon n := by
  let C := 3 * Real.exp (faithfulFloorKappa A B)
  have hC : 0 < C := by dsimp [C]; positivity
  let T := mixtureLikelihoodTest ρ n (worstTestingAlternative ρ epsilon he0 n) σ₁ a
  have hβ := (mixtureLikelihoodTest_component_beta_bounds ρ n
    (worstTestingAlternative ρ epsilon he0 n) σ₁ a).1
  have hex : C * Real.exp (-(n : ℝ) * a) = Real.exp (-((n : ℝ) * a - Real.log C)) := by
    calc
      _ = Real.exp (Real.log C) * Real.exp (-(n : ℝ) * a) := by rw [Real.exp_log hC]
      _ = Real.exp (Real.log C + -(n : ℝ) * a) := (Real.exp_add _ _).symm
      _ = _ := by congr 1; ring
  have hb : acceptance (worstTestingAlternative ρ epsilon he0 n).val T ≤
      Real.exp (-((n : ℝ) * a - Real.log C)) := by
    simpa only [← hex] using hβ
  have hH := hypothesisTestingSingleNat_ge_of_beta_bound (tensorCopies ρ n)
    (worstTestingAlternative ρ epsilon he0 n).val T ha hb
  rw [← worstTestingAlternative_hypothesisTesting ρ epsilon he0 n,
    ← coe_hypothesisTestingNat_toReal _ he0 he1, EReal.coe_le_coe_iff] at hH
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hd := div_le_div_of_nonneg_right hH hn0.le
  rw [sub_div] at hd
  have hcancel : (n : ℝ) * a / (n : ℝ) = a := by field_simp
  simpa only [hcancel, fixedErrorRateReal] using hd

end QuantumProver.DepolarizingSquashedEntanglement.BCYGeneralizedStein

namespace QuantumProver.DepolarizingSquashedEntanglement.BCYGeneralizedStein

open BCYRelativeEntropy BCYPinching BCYCompositeTesting

variable {A B : Type*} [Fintype A] [Fintype B]
  [DecidableEq A] [DecidableEq B] [Nonempty A] [Nonempty B]

theorem generalizedStein_fixed_error_lower_bound (ρ : Density (A × B))
    {epsilon : ℝ} (he : 0 < epsilon) (he1 : epsilon < 1) :
    (regularizedRelativeEntropyEntanglementNat ρ : EReal) ≤
      liminf (fun n => hypothesisTestingNat (tensorCopies ρ n) epsilon *
        ((1 / (n : ℝ) : ℝ) : EReal)) atTop := by
  have he0 : 0 ≤ epsilon := he.le
  have hrep : (fun n : ℕ => hypothesisTestingNat (tensorCopies ρ n) epsilon *
      ((1 / (n : ℝ) : ℝ) : EReal)) =
        (fun n => (fixedErrorRateReal ρ epsilon n : EReal)) := by
    funext n
    exact (coe_fixedErrorRateReal ρ he0 he1 n).symm
  rw [hrep]
  by_contra hnot
  have hgapE : liminf (fun n => (fixedErrorRateReal ρ epsilon n : EReal)) atTop <
      (regularizedRelativeEntropyEntanglementNat ρ : EReal) := lt_of_not_ge hnot
  have hzero : (0 : EReal) ≤
      liminf (fun n => (fixedErrorRateReal ρ epsilon n : EReal)) atTop := by
    apply Filter.le_liminf_of_le (h := ?_)
    exact Filter.Eventually.of_forall (fun n =>
      EReal.coe_nonneg.mpr (fixedErrorRateReal_nonneg ρ he0 n))
  have hbot : liminf (fun n => (fixedErrorRateReal ρ epsilon n : EReal)) atTop ≠ ⊥ :=
    ne_of_gt ((EReal.bot_lt_coe 0).trans_le hzero)
  have htop : liminf (fun n => (fixedErrorRateReal ρ epsilon n : EReal)) atTop ≠ ⊤ :=
    ne_of_lt (hgapE.trans (EReal.coe_lt_top _))
  let Re : ℝ := (liminf (fun n => (fixedErrorRateReal ρ epsilon n : EReal)) atTop).toReal
  have hcoe : (Re : EReal) =
      liminf (fun n => (fixedErrorRateReal ρ epsilon n : EReal)) atTop :=
    EReal.coe_toReal htop hbot
  have hgap : Re < regularizedRelativeEntropyEntanglementNat ρ := by
    apply EReal.coe_lt_coe_iff.mp
    rw [hcoe]
    exact hgapE
  let eta := epsilon / 2
  let e0 := BCYThreeRegions.epsilon0 epsilon eta
    (regularizedRelativeEntropyEntanglementNat ρ) Re
  have heta0 : 0 < eta := by dsimp [eta]; positivity
  have heta : eta ≤ epsilon := by dsimp [eta]; linarith
  have he0pos : 0 < e0 := by
    dsimp [e0, eta, BCYThreeRegions.epsilon0]
    exact mul_pos (div_pos (by linarith) (by linarith)) (sub_pos.mpr hgap)
  obtain ⟨m,hm,σ,hσ,hRate⟩ := exists_faithful_block_below_rate ρ
    (R := regularizedRelativeEntropyEntanglementNat ρ + e0) (by linarith)
  let ω : SeparableDensity A B := ⟨faithfulReference A B, faithfulReference_separable⟩
  have hω : ω.val.matrix.PosDef := faithfulReference_posDef
  let σ₀ := worstTestingAlternative ρ epsilon he0
  let σ₁ := BCYBlockStrongConverse.paddedBlockComparison m σ ω
  let S : (n : ℕ) → Density (CopyIndex A n × CopyIndex B n) :=
    fun n => roundedSeparableMixture n (σ₀ n) (σ₁ n)
  have hS (n : ℕ) : (S n).matrix.PosDef := roundedSeparableMixture_posDef n _ _
  let C := 3 * Real.exp (faithfulFloorKappa A B)
  have hC : 0 < C := by dsimp [C]; positivity
  have hWorst (n : ℕ) : hypothesisTestingNat (tensorCopies ρ n) epsilon =
      hypothesisTestingSingleNat (tensorCopies ρ n) (σ₀ n).val epsilon :=
    worstTestingAlternative_hypothesisTesting ρ epsilon he0 n
  have hOrderStar (n : ℕ) : (σ₀ n).val.matrix ≤ C • (S n).matrix :=
    (roundedSeparableMixture_component_domination n (σ₀ n) (σ₁ n)).1
  have hOrderPad (n : ℕ) : (σ₁ n).val.matrix ≤ C • (S n).matrix :=
    (roundedSeparableMixture_component_domination n (σ₀ n) (σ₁ n)).2
  have hRe : liminf (fun n => hypothesisTestingNat (tensorCopies ρ n) epsilon *
      ((1 / (n : ℝ) : ℝ) : EReal)) atTop = (Re : EReal) := by
    rw [hrep]
    exact hcoe.symm
  have hlow (slack : ℝ) (hs : 0 < slack) :
      liminf (fun n => (mixtureThresholdMass ρ n (σ₀ n) (σ₁ n) (Re + slack) : EReal))
        atTop ≤ ((1 - epsilon : ℝ) : EReal) := by
    exact BCYLowerThresholdMass.lower_threshold_mass_liminf_le
      ρ epsilon he0 he1 σ₀ S hS hWorst C hC hOrderStar Re hRe slack hs
  have hhigh (slack : ℝ) (hs : 0 < slack) :
      Tendsto (fun n => mixtureThresholdMass ρ n (σ₀ n) (σ₁ n)
        (regularizedRelativeEntropyEntanglementNat ρ + e0 + slack)) atTop (𝓝 0) := by
    exact BCYUpperThresholdMass.upper_threshold_mass_tendsto_zero
      ρ m (by omega) σ ω hσ hω S hS C hC hOrderPad
      (regularizedRelativeEntropyEntanglementNat ρ + e0) hRate slack hs
  exact mixture_threshold_limits_contradict_rate_gap ρ σ₀ σ₁ Re epsilon eta
    he1 heta0 heta hgap hlow hhigh

theorem generalizedStein_achievable_regularizedER (ρ : Density (A × B)) :
    AchievableAllRate ρ (regularizedRelativeEntropyEntanglementNat ρ : EReal) := by
  apply BCYDiagonalTests.achievableAllRate_of_fixed_error_lower_bound
  intro epsilon he he1
  exact generalizedStein_fixed_error_lower_bound ρ he he1

theorem generalizedStein_allEffectsTestingRateNat (ρ : Density (A × B)) :
    allEffectsTestingRateNat ρ = (regularizedRelativeEntropyEntanglementNat ρ : EReal) := by
  exact le_antisymm (allEffectsTestingRateNat_le_regularizedER ρ)
    (le_sSup (generalizedStein_achievable_regularizedER ρ))

theorem generalizedStein_allEffectsTestingRateReal (ρ : Density (A × B)) :
    allEffectsTestingRateReal ρ = regularizedRelativeEntropyEntanglementNat ρ := by
  apply EReal.coe_eq_coe_iff.mp
  rw [coe_allEffectsTestingRateReal, generalizedStein_allEffectsTestingRateNat]

end QuantumProver.DepolarizingSquashedEntanglement.BCYGeneralizedStein

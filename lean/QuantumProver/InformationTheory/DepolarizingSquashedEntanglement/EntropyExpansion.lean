import QuantumProver.InformationTheory.DepolarizingSquashedEntanglement.Definitions
import QuantumProver.InformationTheory.SuperchannelDiscrimination.TestingTheorems
import QuantumProver.InformationTheory.ConditionalEntropy.ConditionalRange

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace QuantumProver.DepolarizingSquashedEntanglement
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
  ContinuousFunctionalCalculus Kronecker

theorem entropyNat_isometric_embedding {I O : Type*} [Fintype I] [Fintype O]
    [DecidableEq I] [DecidableEq O] (V : Matrix O I ℂ)
    (hV : IsIsometry V) {ρ : QMatrix I} (hρ : ρ.IsHermitian) :
    entropyNat (V * ρ * V.conjTranspose) = entropyNat ρ := by
  change (Matrix.trace (cfc Real.negMulLog
    (QuantumProver.SuperchannelDiscrimination.ZeroExtension.extend V ρ))).re = _
  rw [QuantumProver.SuperchannelDiscrimination.ZeroExtension.cfc_extend V hV
    Real.negMulLog Real.negMulLog_zero hρ,
    QuantumProver.SuperchannelDiscrimination.ZeroExtension.extend_trace V hV]
  rfl

theorem isometry_kronecker {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] {U : QMatrix A} {W : QMatrix B}
    (hU : IsIsometry U) (hW : IsIsometry W) : IsIsometry (U ⊗ₖ W) := by
  rw [IsIsometry,Matrix.conjTranspose_kronecker,← Matrix.mul_kronecker_mul,
    hU,hW,Matrix.one_kronecker_one]

theorem partialTraceRight_conjugate_retained {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (U : QMatrix A) (ρ : QMatrix (A×B)) :
    partialTraceRight ((U ⊗ₖ (1 : QMatrix B))*ρ*(U ⊗ₖ (1 : QMatrix B)).conjTranspose)=
      U*partialTraceRight ρ*U.conjTranspose := by
  rw [Matrix.conjTranspose_kronecker,Matrix.conjTranspose_one]
  ext i j
  simp only [partialTraceRight,QuantumProver.WernerEndpoint.partialTraceLeft,Matrix.mul_apply,
    Matrix.conjTranspose_apply,Matrix.kronecker_apply,Fintype.sum_prod_type,
    Matrix.one_apply,mul_ite,ite_mul,mul_one,
    one_mul,mul_zero,zero_mul,Finset.sum_ite_eq',Finset.sum_ite_eq,
    Finset.mem_univ,if_true,Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_irrel,Finset.sum_ite_eq',Finset.sum_ite_eq,
    Finset.sum_const_zero,Finset.mem_univ,ite_true]
  rw [Finset.sum_comm]

theorem partialTraceRight_conjugate_discarded {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (W : QMatrix B) (hW : IsIsometry W) (ρ : QMatrix (A×B)) :
    partialTraceRight (((1 : QMatrix A) ⊗ₖ W)*ρ*((1 : QMatrix A) ⊗ₖ W).conjTranspose)=
      partialTraceRight ρ := by
  ext i j
  let block : QMatrix B := fun e f => ρ (i,e) (j,f)
  have hslice :
      (((1 : QMatrix A) ⊗ₖ W)*ρ*((1 : QMatrix A) ⊗ₖ W).conjTranspose).submatrix
        (fun e => (i,e)) (fun f => (j,f))=W*block*W.conjTranspose := by
    rw [Matrix.conjTranspose_kronecker,Matrix.conjTranspose_one]
    ext e f
    simp [Matrix.mul_apply,Matrix.conjTranspose_apply,Matrix.kronecker_apply,
      Fintype.sum_prod_type,Matrix.one_apply,Matrix.submatrix_apply,block,
      ite_mul,mul_ite]
  change Matrix.trace
      ((((1 : QMatrix A) ⊗ₖ W)*ρ*((1 : QMatrix A) ⊗ₖ W).conjTranspose).submatrix
        (fun e => (i,e)) (fun f => (j,f)))=Matrix.trace block
  rw [hslice,Matrix.trace_mul_cycle,hW,Matrix.one_mul]

theorem partialTraceRight_localUnitary {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (U : QMatrix A) (W : QMatrix B) (hW : IsIsometry W)
    (ρ : QMatrix (A×B)) :
    partialTraceRight ((U ⊗ₖ W)*ρ*(U ⊗ₖ W).conjTranspose)=
      U*partialTraceRight ρ*U.conjTranspose := by
  have hfactor : U ⊗ₖ W=(U ⊗ₖ (1 : QMatrix B))*((1 : QMatrix A) ⊗ₖ W) := by
    rw [← Matrix.mul_kronecker_mul,Matrix.mul_one,Matrix.one_mul]
  rw [hfactor,Matrix.conjTranspose_mul]
  have hassoc :
      ((U ⊗ₖ (1 : QMatrix B))*((1 : QMatrix A) ⊗ₖ W))*ρ*
        (((1 : QMatrix A) ⊗ₖ W).conjTranspose*(U ⊗ₖ (1 : QMatrix B)).conjTranspose)=
      (U ⊗ₖ (1 : QMatrix B))*
        (((1 : QMatrix A) ⊗ₖ W)*ρ*((1 : QMatrix A) ⊗ₖ W).conjTranspose)*
          (U ⊗ₖ (1 : QMatrix B)).conjTranspose := by
    simp only [Matrix.mul_assoc]
  rw [hassoc,partialTraceRight_conjugate_retained,
    partialTraceRight_conjugate_discarded W hW]

theorem partialTraceLeft_localUnitary {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (U : QMatrix A) (W : QMatrix B) (hU : IsIsometry U)
    (ρ : QMatrix (A×B)) :
    partialTraceLeft ((U ⊗ₖ W)*ρ*(U ⊗ₖ W).conjTranspose)=
      W*partialTraceLeft ρ*W.conjTranspose := by
  let e : B×A ≃ A×B := Equiv.prodComm B A
  have hs : (U ⊗ₖ W).submatrix e e=W ⊗ₖ U := by
    ext x y
    simp [e,Matrix.kronecker_apply,mul_comm]
  have hc :
      ((U ⊗ₖ W)*ρ*(U ⊗ₖ W).conjTranspose).submatrix e e=
        (W ⊗ₖ U)*(ρ.submatrix e e)*(W ⊗ₖ U).conjTranspose := by
    rw [← Matrix.submatrix_mul_equiv _ _ e e e,
      ← Matrix.submatrix_mul_equiv _ _ e e e,
      ← Matrix.conjTranspose_submatrix,hs]
  change partialTraceRight
      (((U ⊗ₖ W)*ρ*(U ⊗ₖ W).conjTranspose).submatrix e e)=
        W*partialTraceRight (ρ.submatrix e e)*W.conjTranspose
  rw [hc]
  exact partialTraceRight_localUnitary W U hU (ρ.submatrix e e)

def splitterScale : ℝ := (Real.sqrt 2)⁻¹

theorem splitterScale_sq : splitterScale ^ 2 = 1 / 2 := by
  rw [splitterScale, inv_pow, Real.sq_sqrt (by norm_num : (0 : ℝ)   ≤   2)]
  norm_num

theorem splitterScale_complex_sq : (splitterScale : ℂ) ^ 2 = 1 / 2 := by
  rw [← Complex.ofReal_pow, splitterScale_sq]
  norm_num

theorem pureDensity_partialTraceRight_gram {I J : Type*}
    [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (M : Matrix I J ℂ) :
    partialTraceRight (pureDensity (fun x : I×J => M x.1 x.2)) =
      M*M.conjTranspose := by
  ext i j
  simp [partialTraceRight, QuantumProver.WernerEndpoint.partialTraceLeft, pureDensity,
    QuantumProver.WernerEndpoint.pureDensity, QuantumProver.WernerEndpoint.crossDensity, Matrix.mul_apply,
    Matrix.conjTranspose_apply]

theorem pureDensity_partialTraceLeft_gram {I J : Type*}
    [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (M : Matrix I J ℂ) :
    partialTraceLeft (pureDensity (fun x : I×J => M x.1 x.2)) =
      (M.conjTranspose*M).transpose := by
  ext i j
  simp [partialTraceLeft, QuantumProver.WernerEndpoint.partialTraceRight, pureDensity,
    QuantumProver.WernerEndpoint.pureDensity, QuantumProver.WernerEndpoint.crossDensity, Matrix.mul_apply,
    Matrix.conjTranspose_apply, mul_comm]

def fourImageVector {E G : Type*} (p : ℝ)
    (M : CanonicalEnvironment → Matrix E G ℂ) :
    (((Qubit×Qubit)×E)×G) → ℂ :=
  fun x => (splitterScale : ℂ) * ∑ j,
    (Real.sqrt (pauliWeight p j) : ℂ) * pauli j x.1.1.2 x.1.1.1 *
      M j x.1.2 x.2

def fourImageAmplitudeE {E G : Type*} (p : ℝ)
    (M : CanonicalEnvironment → Matrix E G ℂ) :
    Matrix (Qubit×E) (Qubit×G) ℂ :=
  fun re bg => fourImageVector p M (((re.1,bg.1),re.2),bg.2)

def fourImageAmplitudeG {E G : Type*} (p : ℝ)
    (M : CanonicalEnvironment → Matrix E G ℂ) :
    Matrix (Qubit×G) (Qubit×E) ℂ :=
  fun rg be => fourImageVector p M (((rg.1,be.1),be.2),rg.2)

theorem fourImageAmplitudeE_pauli {E G : Type*} (p : ℝ)
    (M : CanonicalEnvironment → Matrix E G ℂ) :
    fourImageAmplitudeE p M = (splitterScale : ℂ) • ∑ j,
      (Real.sqrt (pauliWeight p j) : ℂ) • ((pauli j).transpose ⊗ₖ M j) := by
  ext ⟨r,e⟩ ⟨b,g⟩
  simp [fourImageAmplitudeE, fourImageVector, Matrix.sum_apply,
    Matrix.smul_apply, Matrix.kronecker_apply, Finset.mul_sum, mul_assoc]

theorem fourImageAmplitudeG_pauli {E G : Type*} (p : ℝ)
    (M : CanonicalEnvironment → Matrix E G ℂ) :
    fourImageAmplitudeG p M = (splitterScale : ℂ) • ∑ j,
      (Real.sqrt (pauliWeight p j) : ℂ) •
        ((pauli j).transpose ⊗ₖ (M j).transpose) := by
  ext ⟨r,g⟩ ⟨b,e⟩
  simp [fourImageAmplitudeG, fourImageVector, Matrix.sum_apply,
    Matrix.smul_apply, Matrix.kronecker_apply, Finset.mul_sum, mul_assoc]

theorem fourImageE_gram {E G : Type*} [Fintype E] [Fintype G]
    [DecidableEq E] [DecidableEq G] (p : ℝ)
    (M : CanonicalEnvironment → Matrix E G ℂ) :
    traceMiddle (partialTraceRight (pureDensity (fourImageVector p M))) =
      fourImageAmplitudeE p M * (fourImageAmplitudeE p M).conjTranspose := by
  ext ⟨r,e⟩ ⟨s,f⟩
  simp [traceMiddle, partialTraceRight, QuantumProver.WernerEndpoint.partialTraceLeft,
    pureDensity, QuantumProver.WernerEndpoint.pureDensity, QuantumProver.WernerEndpoint.crossDensity,
    Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type,
    fourImageAmplitudeE]

theorem entropyNat_oppositeGram {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (M : Matrix I J ℂ) :
    entropyNat (M.conjTranspose*M) = entropyNat (M*M.conjTranspose) := by
  have h := QuantumProver.ConditionalEntropy.ConditionalRange.entropyBits_rectangularGram M
  rw [QuantumProver.ConditionalEntropy.ConditionalRange.entropyBits_eq_isotropicEntropy_div_log_two
      (M.conjTranspose*M),
    QuantumProver.ConditionalEntropy.ConditionalRange.entropyBits_eq_isotropicEntropy_div_log_two
      (M*M.conjTranspose)] at h
  change entropyNat (M.conjTranspose*M)/Real.log 2 =
    entropyNat (M*M.conjTranspose)/Real.log 2 at h
  have hl : Real.log 2≠0 := ne_of_gt (Real.log_pos (by norm_num))
  field_simp [hl] at h
  exact h

theorem entropyNat_transpose {I : Type*} [Fintype I] [DecidableEq I]
    {X : QMatrix I} (hX : X.IsHermitian) : entropyNat X.transpose = entropyNat X := by
  have h := QuantumProver.ConditionalEntropy.ConditionalRange.entropyBits_transpose hX
  rw [QuantumProver.ConditionalEntropy.ConditionalRange.entropyBits_eq_isotropicEntropy_div_log_two
      X.transpose,
    QuantumProver.ConditionalEntropy.ConditionalRange.entropyBits_eq_isotropicEntropy_div_log_two
      X] at h
  change entropyNat X.transpose/Real.log 2 = entropyNat X/Real.log 2 at h
  have hl : Real.log 2≠0 := ne_of_gt (Real.log_pos (by norm_num))
  field_simp [hl] at h
  exact h

end QuantumProver.DepolarizingSquashedEntanglement

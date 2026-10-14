import QuantumProver.InformationTheory.DepolarizingSquashedEntanglement.EntropyExpansion
import QuantumProver.InformationTheory.DepolarizingSquashedEntanglement.StinespringEntropyBounds
import QuantumProver.InformationTheory.DepolarizingSquashedEntanglement.EntropySharing
import QuantumProver.InformationTheory.DepolarizingSquashedEntanglement.Fixed16FlagEntropy
import QuantumProver.InformationTheory.SuperchannelDiscrimination.TestingTheorems
import QuantumProver.InformationTheory.ConditionalEntropy.ConditionalRange
import QuantumProver.InformationTheory.ConditionalEntropy.MixtureEntropy

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace QuantumProver.DepolarizingSquashedEntanglement

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
  ContinuousFunctionalCalculus

namespace MatrixBridge

variable {I O : Type*} [Fintype I] [Fintype O]
  [DecidableEq I] [DecidableEq O]

theorem amplify_right_as_left {R : Type*} [Fintype R]
    (Φ : QMatrix I →ₗ[ℂ] QMatrix O) (A : QMatrix (I × R)) :
    QuantumProver.SuperchannelDiscrimination.KrausCompletion.amplify Φ R A =
      (QuantumProver.DepolarizingSquashedEntanglement.amplify Φ (A.submatrix Prod.swap Prod.swap)).submatrix
        Prod.swap Prod.swap := rfl

theorem amplify_left_as_right {R : Type*} [Fintype R]
    (Φ : QMatrix I →ₗ[ℂ] QMatrix O) (A : QMatrix (R × I)) :
    QuantumProver.DepolarizingSquashedEntanglement.amplify Φ A =
      (QuantumProver.SuperchannelDiscrimination.KrausCompletion.amplify Φ R
        (A.submatrix Prod.swap Prod.swap)).submatrix Prod.swap Prod.swap := rfl

theorem completelyPositive_iff
    (Φ : QMatrix I →ₗ[ℂ] QMatrix O) :
    IsCompletelyPositive Φ ↔
      QuantumProver.SuperchannelDiscrimination.CPWrappers.CompletelyPositive Φ := by
  constructor
  · intro h n A hA
    rw [amplify_right_as_left]
    exact (h n _ (hA.submatrix Prod.swap)).submatrix Prod.swap
  · intro h n A hA
    rw [amplify_left_as_right]
    exact (h n _ (hA.submatrix Prod.swap)).submatrix Prod.swap

end MatrixBridge

namespace CPTP

variable {I O : Type*} [Fintype I] [Fintype O]
  [DecidableEq I] [DecidableEq O]

def represented_toMatrix (Φ : CPTP I O) :
    QuantumProver.SuperchannelDiscrimination.KrausCompletion.FiniteCPTP I O where
  map := Φ.map
  completelyPositive := (MatrixBridge.completelyPositive_iff Φ.map).mp
    Φ.completelyPositive
  tracePreserving := Φ.tracePreserving

def ofMatrix (Φ : QuantumProver.SuperchannelDiscrimination.KrausCompletion.FiniteCPTP I O) :
    CPTP I O where
  map := Φ.map
  completelyPositive := (MatrixBridge.completelyPositive_iff Φ.map).mpr
    Φ.completelyPositive
  tracePreserving := Φ.tracePreserving

@[simp] theorem toMatrix_map (Φ : CPTP I O) : Φ.represented_toMatrix.map = Φ.map := rfl
@[simp] theorem ofMatrix_map
    (Φ : QuantumProver.SuperchannelDiscrimination.KrausCompletion.FiniteCPTP I O) :
    (ofMatrix Φ).map = Φ.map := rfl

theorem exists_complete_kraus (Φ : CPTP I O) :
    ∃ K : I × O → Matrix O I ℂ,
      (∑ k, (K k).conjTranspose * K k = 1) ∧
      ∀ A : QMatrix I, Φ.map A = ∑ k, K k * A * (K k).conjTranspose := by
  simpa only [QuantumProver.SuperchannelDiscrimination.KrausCompletion.krausGram,
    QuantumProver.SuperchannelDiscrimination.KrausCompletion.krausAction] using
    QuantumProver.SuperchannelDiscrimination.AbstractDPI.exists_complete_kraus Φ.map
      Φ.represented_toMatrix.completelyPositive Φ.tracePreserving

def canonicalKraus (Φ : CPTP I O) : I × O → Matrix O I ℂ :=
  QuantumProver.SuperchannelDiscrimination.CPTPKraus.canonicalKraus Φ.map

theorem canonicalKraus_complete (Φ : CPTP I O) :
    ∑ k, (Φ.canonicalKraus k).conjTranspose * Φ.canonicalKraus k = 1 :=
  QuantumProver.SuperchannelDiscrimination.AbstractDPI.canonicalKraus_complete Φ.map
    Φ.represented_toMatrix.completelyPositive Φ.tracePreserving

theorem canonicalKraus_reconstruct (Φ : CPTP I O) (A : QMatrix I) :
    Φ.map A = ∑ k, Φ.canonicalKraus k * A * (Φ.canonicalKraus k).conjTranspose :=
  QuantumProver.SuperchannelDiscrimination.AbstractDPI.canonicalKraus_reconstruct Φ.map
    Φ.represented_toMatrix.completelyPositive A

def stinespringCoefficients (Φ : CPTP I O) : Matrix (O × (I × O)) I ℂ :=
  fun x i => Φ.canonicalKraus x.2 x.1 i

theorem stinespringCoefficients_isometry (Φ : CPTP I O) :
    IsIsometry Φ.stinespringCoefficients := by
  ext i j
  have h := congrArg (fun M : QMatrix I => M i j) Φ.canonicalKraus_complete
  simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply] at h
  change (∑ x : O × (I × O),
    star (Φ.canonicalKraus x.2 x.1 i) * Φ.canonicalKraus x.2 x.1 j) = _
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  exact h

def stinespring (Φ : CPTP I O) : QuantumProver.WernerEndpoint.Stinespring I O (I × O) where
  coeff := Φ.stinespringCoefficients
  gram_eq_one := Φ.stinespringCoefficients_isometry

theorem stinespring_apply (Φ : CPTP I O) (A : QMatrix I) :
    Φ.stinespring.apply A = Φ.map A := by
  rw [Φ.canonicalKraus_reconstruct]
  ext o p
  simp [stinespring, stinespringCoefficients, QuantumProver.WernerEndpoint.Stinespring.apply,
    QuantumProver.WernerEndpoint.partialTraceLeft, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fintype.sum_prod_type, Matrix.sum_apply, Finset.sum_mul]

theorem amplify_eq_stinespring {R : Type*} [Fintype R] [DecidableEq R]
    (Φ : CPTP I O) (A : QMatrix (R × I)) :
    amplify Φ.map A = Φ.stinespring.amplify A := by
  ext ⟨r, o⟩ ⟨s, p⟩
  exact ((QuantumProver.WernerEndpoint.Stinespring.amplify_block Φ.stinespring A r s o p).trans
    (congrArg (fun M : QMatrix O => M o p)
      (Φ.stinespring_apply (fun y z => A (r, y) (s, z))))).symm

theorem amplify_pureDensity_eq_reduced {R : Type*} [Fintype R] [DecidableEq R]
    (Φ : CPTP I O) (ψ : (R × I) → ℂ) :
    amplify Φ.map (pureDensity ψ) =
      partialTraceRight (pureDensity (fun x : (R × O) × (I × O) =>
        (Φ.stinespring.withReference R).amplitudes ψ x.1 x.2)) := by
  rw [amplify_eq_stinespring]
  change (Φ.stinespring.withReference R).apply (QuantumProver.WernerEndpoint.pureDensity ψ) = _
  rw [QuantumProver.WernerEndpoint.Stinespring.apply_pureDensity]
  rfl

theorem amplify_positive {R : Type*} [Fintype R] [DecidableEq R]
    (Φ : CPTP I O) {A : QMatrix (R × I)} (hA : A.PosSemidef) :
    (amplify Φ.map A).PosSemidef := by
  rw [MatrixBridge.amplify_left_as_right]
  have h := QuantumProver.SuperchannelDiscrimination.CPWrappers.completelyPositive_allReferences
    Φ.represented_toMatrix.completelyPositive R (hA := hA.submatrix Prod.swap)
  exact h.submatrix Prod.swap

theorem amplify_trace {R : Type*} [Fintype R] [DecidableEq R]
    (Φ : CPTP I O) (A : QMatrix (R × I)) :
    Matrix.trace (amplify Φ.map A) = Matrix.trace A := by
  simp only [Matrix.trace, Matrix.diag, Fintype.sum_prod_type, QuantumProver.DepolarizingSquashedEntanglement.amplify]
  apply Finset.sum_congr rfl
  intro r _
  exact Φ.tracePreserving (fun i j => A (r, i) (r, j))

theorem relativeEntropyBits_dpi (Φ : CPTP I O) {A B : QMatrix I}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    QuantumProver.SuperchannelDiscrimination.FlaggedStates.relativeEntropyBits
        (Φ.map A) (Φ.map B)   ≤
      QuantumProver.SuperchannelDiscrimination.FlaggedStates.relativeEntropyBits A B :=
  QuantumProver.SuperchannelDiscrimination.AbstractDPI.relativeEntropyBits_cptp_dpi
    Φ.represented_toMatrix hA hB

end CPTP

def squashingImageMatrices {E : Type*} [Fintype E] [DecidableEq E]
    (S : CPTP CanonicalEnvironment E) (j : CanonicalEnvironment) :
    Matrix E (CanonicalEnvironment × E) ℂ :=
  fun e g => S.stinespring.coeff (e, g) j

theorem squashingImageMatrices_orthonormal {E : Type*} [Fintype E] [DecidableEq E]
    (S : CPTP CanonicalEnvironment E) (i j : CanonicalEnvironment) :
    Matrix.trace ((squashingImageMatrices S i).conjTranspose *
      squashingImageMatrices S j) = if i = j then 1 else 0 := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    squashingImageMatrices]
  rw [Finset.sum_comm]
  have h := congrArg (fun M : QMatrix CanonicalEnvironment => M i j)
    S.stinespring.gram_eq_one
  simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type,
    Matrix.one_apply] using h

namespace KrausFamily

variable {I O : Type*} [Fintype I] [Fintype O]
  [DecidableEq I] [DecidableEq O]

def toCPTP (K : KrausFamily I O) : CPTP I O where
  map := K.toLinearMap
  completelyPositive := by
    apply (MatrixBridge.completelyPositive_iff K.toLinearMap).mpr
    intro n A hA
    exact QuantumProver.SuperchannelDiscrimination.KrausCompletion.krausMap_completelyPositive
      K.operator (Fin n) hA
  tracePreserving := K.trace_apply

@[simp] theorem toCPTP_apply (K : KrausFamily I O) (A : QMatrix I) :
    K.toCPTP.map A = K.apply A := rfl

end KrausFamily

theorem pauli_unitary (j : CanonicalEnvironment) :
    (pauli j).conjTranspose * pauli j = 1 := by
  fin_cases j <;> ext i k <;> fin_cases i <;> fin_cases k <;>
    norm_num [pauli, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two]

theorem pauliWeight_nonneg {p : ℝ} (hp0 : 0   ≤   p) (hp1 : p   ≤   1)
    (j : CanonicalEnvironment) : 0   ≤   pauliWeight p j := by
  unfold pauliWeight
  split_ifs
  · linarith
  · exact div_nonneg hp0 (by norm_num)

theorem pauliWeight_sum (p : ℝ) : ∑ j, pauliWeight p j = 1 := by
  norm_num [pauliWeight, Fin.sum_univ_succ] <;> ring

def pauliOperator (p : ℝ) (j : CanonicalEnvironment) : QMatrix Qubit :=
  (Real.sqrt (pauliWeight p j) : ℝ) • pauli j

theorem pauliOperator_gram {p : ℝ} (hp0 : 0   ≤   p) (hp1 : p   ≤   1)
    (j : CanonicalEnvironment) :
    (pauliOperator p j).conjTranspose * pauliOperator p j =
      (pauliWeight p j : ℝ) • (1 : QMatrix Qubit) := by
  calc
    _ = (Real.sqrt (pauliWeight p j) * Real.sqrt (pauliWeight p j) : ℝ) •
        ((pauli j).conjTranspose * pauli j) := by
      simp [pauliOperator, Matrix.conjTranspose_smul, Matrix.smul_mul,
        Matrix.mul_smul, smul_smul]
    _ = (pauliWeight p j : ℝ) • (1 : QMatrix Qubit) := by
      rw [Real.mul_self_sqrt (pauliWeight_nonneg hp0 hp1 j), pauli_unitary]

theorem pauliOperator_sandwich {p : ℝ} (hp0 : 0   ≤   p) (hp1 : p   ≤   1)
    (j : CanonicalEnvironment) (ρ : QMatrix Qubit) :
    pauliOperator p j * ρ * (pauliOperator p j).conjTranspose =
      (pauliWeight p j : ℝ) • (pauli j * ρ * (pauli j).conjTranspose) := by
  calc
    _ = (Real.sqrt (pauliWeight p j) * Real.sqrt (pauliWeight p j) : ℝ) •
        (pauli j * ρ * (pauli j).conjTranspose) := by
      simp [pauliOperator, Matrix.conjTranspose_smul, Matrix.smul_mul,
        Matrix.mul_smul, smul_smul]
    _ = _ := by rw [Real.mul_self_sqrt (pauliWeight_nonneg hp0 hp1 j)]

theorem weightedPauli_eq_depolarizing (p : ℝ) (ρ : QMatrix Qubit) :
    (∑ j, (pauliWeight p j : ℝ) • (pauli j * ρ * (pauli j).conjTranspose)) =
      depolarizing p ρ := by
  ext i k
  fin_cases i <;> fin_cases k <;> apply Complex.ext <;>
    simp [pauliWeight, pauli, depolarizing, Matrix.sum_apply, Matrix.smul_apply,
      Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.trace, Matrix.vecMul,
      Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, RCLike.real_smul_eq_coe_mul, Complex.star_def,
      Complex.mul_re, Complex.mul_im] <;> ring

def pauliFamily (p : ℝ) (hp0 : 0   ≤   p) (hp1 : p   ≤   1) : KrausFamily Qubit Qubit where
  count := 4
  operator := pauliOperator p
  complete := by
    simp_rw [pauliOperator_gram hp0 hp1]
    rw [← Finset.sum_smul, pauliWeight_sum, one_smul]

theorem pauliFamily_apply {p : ℝ} (hp0 : 0   ≤   p) (hp1 : p   ≤   1)
    (ρ : QMatrix Qubit) : (pauliFamily p hp0 hp1).apply ρ = depolarizing p ρ := by
  change (∑ j, pauliOperator p j * ρ * (pauliOperator p j).conjTranspose) = _
  simp_rw [pauliOperator_sandwich hp0 hp1]
  exact weightedPauli_eq_depolarizing p ρ

def depolarizingChannel (p : ℝ) (hp0 : 0   ≤   p) (hp1 : p   ≤   1) : CPTP Qubit Qubit :=
  (pauliFamily p hp0 hp1).toCPTP

theorem depolarizingChannel_apply {p : ℝ} (hp0 : 0   ≤   p) (hp1 : p   ≤   1)
    (ρ : QMatrix Qubit) : (depolarizingChannel p hp0 hp1).map ρ = depolarizing p ρ :=
  pauliFamily_apply hp0 hp1 ρ

theorem canonicalIsometry_isometry {p : ℝ} (hp0 : 0   ≤   p) (hp1 : p   ≤   1) :
    IsIsometry (canonicalIsometry p) := by
  ext i j
  have h := congrArg (fun M : QMatrix Qubit => M i j) (pauliFamily p hp0 hp1).complete
  simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    pauliFamily, pauliOperator, Matrix.smul_apply, RCLike.real_smul_eq_coe_mul] at h
  change (∑ x : Qubit × CanonicalEnvironment,
    star (((Real.sqrt (pauliWeight p x.2) : ℝ) : ℂ) * pauli x.2 x.1 i) *
      (((Real.sqrt (pauliWeight p x.2) : ℝ) : ℂ) * pauli x.2 x.1 j)) = _
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  exact h

def canonicalStinespring (p : ℝ) (hp0 : 0   ≤   p) (hp1 : p   ≤   1) :
    QuantumProver.WernerEndpoint.Stinespring Qubit Qubit CanonicalEnvironment where
  coeff := canonicalIsometry p
  gram_eq_one := canonicalIsometry_isometry hp0 hp1

theorem canonicalStinespring_apply {p : ℝ} (hp0 : 0   ≤   p) (hp1 : p   ≤   1)
    (ρ : QMatrix Qubit) : (canonicalStinespring p hp0 hp1).apply ρ = depolarizing p ρ := by
  rw [← pauliFamily_apply hp0 hp1 ρ]
  ext i j
  simp [canonicalStinespring, canonicalIsometry, pauliFamily, pauliOperator,
    KrausFamily.apply, QuantumProver.WernerEndpoint.Stinespring.apply, QuantumProver.WernerEndpoint.partialTraceLeft,
    Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.sum_apply,
    RCLike.real_smul_eq_coe_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro e _
  ring

theorem extendedInputKet_eq_referenceAmplitude {p : ℝ} (hp0 : 0   ≤   p) (hp1 : p   ≤   1)
    {R : Type*} [Fintype R] [DecidableEq R] (ψ : (R × Qubit) → ℂ) :
    extendedInputKet p ψ = fun x =>
      ((canonicalStinespring p hp0 hp1).withReference R).amplitudes ψ x.1 x.2 := by
  funext x
  simp [extendedInputKet, canonicalStinespring, QuantumProver.WernerEndpoint.Stinespring.amplitudes,
    QuantumProver.WernerEndpoint.Stinespring.withReference, QuantumProver.WernerEndpoint.Stinespring.referenceCoeff,
    Fintype.sum_prod_type, ite_mul, Finset.sum_ite_irrel]

theorem extendedInputKet_normSq {p : ℝ} (hp0 : 0   ≤   p) (hp1 : p   ≤   1)
    {R : Type*} [Fintype R] [DecidableEq R] (ψ : (R × Qubit) → ℂ) :
    vectorNormSq (extendedInputKet p ψ) = vectorNormSq ψ := by
  rw [extendedInputKet_eq_referenceAmplitude hp0 hp1]
  exact ((canonicalStinespring p hp0 hp1).withReference R).amplitudes_normSq ψ

theorem postSquashing_positive (p : ℝ) {R E : Type*} [Fintype R] [Fintype E]
    [DecidableEq R] [DecidableEq E] (ψ : (R × Qubit) → ℂ)
    (S : CPTP CanonicalEnvironment E) : (postSquashing p ψ S).PosSemidef :=
  S.amplify_positive (QuantumProver.WernerEndpoint.pureDensity_posSemidef _)

theorem postSquashing_trace (p : ℝ) {R E : Type*} [Fintype R] [Fintype E]
    [DecidableEq R] [DecidableEq E] (ψ : (R × Qubit) → ℂ)
    (S : CPTP CanonicalEnvironment E) :
    Matrix.trace (postSquashing p ψ S) = (vectorNormSq (extendedInputKet p ψ) : ℂ) := by
  rw [postSquashing, S.amplify_trace]
  exact QuantumProver.WernerEndpoint.pureDensity_trace _

def postSquashingDensity {p : ℝ} (hp0 : 0   ≤   p) (hp1 : p   ≤   1)
    {R E : Type*} [Fintype R] [Fintype E] [DecidableEq R] [DecidableEq E]
    (ψ : (R × Qubit) → ℂ) (hψ : IsNormalized ψ)
    (S : CPTP CanonicalEnvironment E) : Density ((R × Qubit) × E) where
  matrix := postSquashing p ψ S
  positive := postSquashing_positive p ψ S
  trace_one := by
    rw [postSquashing_trace, extendedInputKet_normSq hp0 hp1,
      show vectorNormSq ψ = 1 from hψ] <;> norm_num

theorem pureDensity_positive {I : Type*} [Fintype I] (v : I → ℂ) :
    (pureDensity v).PosSemidef := QuantumProver.WernerEndpoint.pureDensity_posSemidef v

theorem pureDensity_trace {I : Type*} [Fintype I] (v : I → ℂ) :
    Matrix.trace (pureDensity v) = (vectorNormSq v : ℂ) :=
  QuantumProver.WernerEndpoint.pureDensity_trace v

def normalizedPureDensity {I : Type*} [Fintype I] [DecidableEq I]
    (v : I → ℂ) (hv : IsNormalized v) : Density I where
  matrix := pureDensity v
  positive := pureDensity_positive v
  trace_one := by
    rw [pureDensity_trace, show vectorNormSq v = 1 from hv] <;> norm_num

def splitterCoefficient : Matrix (CanonicalEnvironment × CanonicalEnvironment)
    CanonicalEnvironment ℂ :=
  fun x j => if j = 0 then (if x = (0, 0) then 1 else 0) else
    (splitterScale : ℂ) *
      ((if x = (j, 0) then 1 else 0) + (if x = (0, j) then 1 else 0))

theorem splitterCoefficient_isometry : IsIsometry splitterCoefficient := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [splitterCoefficient, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fintype.sum_prod_type, Fin.sum_univ_succ, Complex.star_def,
      ← Complex.ofReal_mul, ← pow_two, splitterScale_sq, splitterScale_complex_sq]

def splitterKraus : KrausFamily CanonicalEnvironment CanonicalEnvironment where
  count := 4
  operator := fun g e j => splitterCoefficient (e, g) j
  complete := by
    ext i j
    change (∑ g : CanonicalEnvironment, ∑ e : CanonicalEnvironment,
      star (splitterCoefficient (e, g) i) * splitterCoefficient (e, g) j) = _
    rw [Finset.sum_comm]
    have h := congrArg (fun M : QMatrix CanonicalEnvironment => M i j)
      splitterCoefficient_isometry
    simpa [IsIsometry, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fintype.sum_prod_type] using h

def splitterSquashing : CPTP CanonicalEnvironment CanonicalEnvironment :=
  splitterKraus.toCPTP

def basisKet {I : Type*} [DecidableEq I] (i : I) : I → ℂ :=
  fun j => if j = i then 1 else 0

theorem basisKet_normalized {I : Type*} [Fintype I] [DecidableEq I] (i : I) :
    IsNormalized (basisKet i) := by
  simp [IsNormalized, vectorNormSq, QuantumProver.WernerEndpoint.vectorNormSq, basisKet]

theorem inputCosts_nonempty (p : ℝ) {r : ℕ} (ψ : (Fin r × Qubit) → ℂ) :
    (inputCosts p ψ).Nonempty := by
  refine ⟨cmiBits (postSquashing p ψ (CPTP.identity CanonicalEnvironment)), ?_⟩
  exact ⟨4, CPTP.identity CanonicalEnvironment, rfl⟩

theorem channelInputValues_nonempty (p : ℝ) : (channelInputValues p).Nonempty := by
  let ψ : (Fin 1 × Qubit) → ℂ := basisKet (0, 0)
  exact ⟨squashedInputValue p ψ, 1, ψ, basisKet_normalized (0, 0), rfl⟩

theorem squashedInputValue_le_cost (p : ℝ) {r : ℕ} (ψ : (Fin r × Qubit) → ℂ)
    (hbelow : BddBelow (inputCosts p ψ)) {e : ℕ}
    (S : CPTP CanonicalEnvironment (Fin e)) :
    squashedInputValue p ψ   ≤   (1 / 2 : ℝ) * cmiBits (postSquashing p ψ S) := by
  apply mul_le_mul_of_nonneg_left
    (csInf_le hbelow (show cmiBits (postSquashing p ψ S) ∈ inputCosts p ψ from
      ⟨e, S, rfl⟩))
  norm_num

theorem channelSquashed_le_of_fixed_squashing (p : ℝ) {e : ℕ}
    (S : CPTP CanonicalEnvironment (Fin e)) (B : ℝ)
    (hbelow : ∀ r : ℕ, ∀ ψ : (Fin r × Qubit) → ℂ,
      IsNormalized ψ → BddBelow (inputCosts p ψ))
    (hcost : ∀ r : ℕ, ∀ ψ : (Fin r × Qubit) → ℂ,
      IsNormalized ψ → (1 / 2 : ℝ) * cmiBits (postSquashing p ψ S)   ≤   B) :
    channelSquashed p   ≤   B := by
  change sSup (channelInputValues p)   ≤   B
  apply csSup_le (channelInputValues_nonempty p)
  intro x hx
  rcases hx with ⟨r, ψ, hψ, rfl⟩
  exact (squashedInputValue_le_cost p ψ (hbelow r ψ hψ) S).trans (hcost r ψ hψ)

theorem channelSquashed_eq_of_cost_dominance (p : ℝ) {r₀ : ℕ}
    (ψ₀ : (Fin r₀ × Qubit) → ℂ) (hψ₀ : IsNormalized ψ₀)
    (hbelow : ∀ r : ℕ, ∀ ψ : (Fin r × Qubit) → ℂ,
      IsNormalized ψ → BddBelow (inputCosts p ψ))
    (hdom : ∀ r : ℕ, ∀ ψ : (Fin r × Qubit) → ℂ, IsNormalized ψ →
      ∀ b ∈ inputCosts p ψ₀, ∃ a ∈ inputCosts p ψ, a   ≤   b) :
    channelSquashed p = squashedInputValue p ψ₀ := by
  have hinput : ∀ r : ℕ, ∀ ψ : (Fin r × Qubit) → ℂ, IsNormalized ψ →
      squashedInputValue p ψ   ≤   squashedInputValue p ψ₀ := by
    intro r ψ hψ
    unfold squashedInputValue
    apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ)   ≤   1 / 2)
    apply le_csInf (inputCosts_nonempty p ψ₀)
    intro b hb
    rcases hdom r ψ hψ b hb with ⟨a, ha, hab⟩
    exact (csInf_le (hbelow r ψ hψ) ha).trans hab
  have hvalues : ∀ x ∈ channelInputValues p, x   ≤   squashedInputValue p ψ₀ := by
    intro x hx
    rcases hx with ⟨r, ψ, hψ, rfl⟩
    exact hinput r ψ hψ
  apply le_antisymm
  · exact csSup_le (channelInputValues_nonempty p) hvalues
  · exact le_csSup ⟨squashedInputValue p ψ₀, hvalues⟩ ⟨r₀, ψ₀, hψ₀, rfl⟩

theorem entropyNat_eq_of_charpoly_eq {I : Type*} [Fintype I] [DecidableEq I]
    {A B : QMatrix I} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hchar : A.charpoly = B.charpoly) : entropyNat A = entropyNat B := by
  have heig := (hA.eigenvalues_eq_eigenvalues_iff hB).mpr hchar
  unfold entropyNat
  rw [QuantumProver.SuperchannelDiscrimination.Klein.trace_cfc_eq_sum _ hA,
    QuantumProver.SuperchannelDiscrimination.Klein.trace_cfc_eq_sum _ hB, heig]

def realSymmetricTwo (a b z : ℝ) : QMatrix Qubit :=
  !![(a : ℂ), (z : ℂ); (z : ℂ), (b : ℂ)]

def symmetricTwoGap (a b z : ℝ) : ℝ := Real.sqrt ((a - b)^2 + 4*z^2)

def symmetricTwoPlus (a b z : ℝ) : ℝ := (a + b + symmetricTwoGap a b z) / 2

def symmetricTwoMinus (a b z : ℝ) : ℝ := (a + b - symmetricTwoGap a b z) / 2

theorem symmetricTwoGap_sq (a b z : ℝ) :
    symmetricTwoGap a b z ^ 2 = (a-b)^2 + 4*z^2 := by
  apply Real.sq_sqrt
  positivity

theorem symmetricTwo_eigenvalue_sum (a b z : ℝ) :
    symmetricTwoPlus a b z + symmetricTwoMinus a b z = a+b := by
  unfold symmetricTwoPlus symmetricTwoMinus
  ring

theorem symmetricTwo_eigenvalue_product (a b z : ℝ) :
    symmetricTwoPlus a b z * symmetricTwoMinus a b z = a*b-z^2 := by
  unfold symmetricTwoPlus symmetricTwoMinus
  nlinarith [symmetricTwoGap_sq a b z]

theorem realSymmetricTwo_hermitian (a b z : ℝ) :
    (realSymmetricTwo a b z).IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [realSymmetricTwo, Matrix.conjTranspose_apply]

theorem realSymmetricTwo_charpoly (a b z : ℝ) :
    (realSymmetricTwo a b z).charpoly =
      (Matrix.diagonal (fun i : Qubit =>
        if i=0 then (symmetricTwoPlus a b z : ℂ)
        else (symmetricTwoMinus a b z : ℂ))).charpoly := by
  have hsum : (symmetricTwoPlus a b z : ℂ) + (symmetricTwoMinus a b z : ℂ) =
      (a : ℂ) + (b : ℂ) := by
    exact_mod_cast symmetricTwo_eigenvalue_sum a b z
  have hprod : (symmetricTwoPlus a b z : ℂ) * (symmetricTwoMinus a b z : ℂ) =
      (a : ℂ)*(b : ℂ)-(z : ℂ)^2 := by
    exact_mod_cast symmetricTwo_eigenvalue_product a b z
  rw [Matrix.charpoly_fin_two, Matrix.charpoly_fin_two]
  simp [realSymmetricTwo, Matrix.trace, Matrix.diag, Fin.sum_univ_two,
    Matrix.det_fin_two, hsum, hprod, pow_two]

def pauliSign (k j : CanonicalEnvironment) : ℝ :=
  if k=0 ∨ j=0 ∨ k=j then 1 else -1

theorem pauliSign_sq (k j : CanonicalEnvironment) : pauliSign k j ^ 2 = 1 := by
  unfold pauliSign
  split_ifs <;> norm_num

def pauliEnvironmentUnitary (k : CanonicalEnvironment) : QMatrix CanonicalEnvironment :=
  Matrix.diagonal (fun j => (pauliSign k j : ℂ))

theorem pauliEnvironmentUnitary_isometry (k : CanonicalEnvironment) :
    IsIsometry (pauliEnvironmentUnitary k) := by
  change (pauliEnvironmentUnitary k).conjTranspose * pauliEnvironmentUnitary k = 1
  simp only [pauliEnvironmentUnitary, Matrix.diagonal_conjTranspose,
    Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases hij : i=j
  · subst j
    by_cases hsign : k=0 ∨ i=0 ∨ k=i <;>
      simp [Matrix.diagonal_apply, Matrix.one_apply, pauliSign, hsign]
  · simp [Matrix.diagonal_apply, Matrix.one_apply, hij]

theorem pauli_commutation (k j : CanonicalEnvironment) :
    pauli j * pauli k = (pauliSign k j : ℝ) • (pauli k * pauli j) := by
  fin_cases k <;> fin_cases j <;> ext b i <;>
    fin_cases b <;> fin_cases i <;>
    norm_num [pauli, pauliSign, Matrix.mul_apply, Matrix.smul_apply,
      Fin.sum_univ_two]

open scoped Kronecker

theorem canonicalIsometry_pauli_equivariance (p : ℝ)
    (k : CanonicalEnvironment) :
    canonicalIsometry p * pauli k =
      (pauli k ⊗ₖ pauliEnvironmentUnitary k) * canonicalIsometry p := by
  ext ⟨b,j⟩ i
  have hcomm := congrArg (fun M : QMatrix Qubit => M b i) (pauli_commutation k j)
  change (pauli j * pauli k) b i =
    (pauliSign k j : ℝ) • (pauli k * pauli j) b i at hcomm
  have hl : (canonicalIsometry p * pauli k) (b,j) i =
      (Real.sqrt (pauliWeight p j) : ℂ) * (pauli j * pauli k) b i := by
    simp [Matrix.mul_apply, canonicalIsometry, Finset.mul_sum]
    ring
  have hr : ((pauli k ⊗ₖ pauliEnvironmentUnitary k) * canonicalIsometry p) (b,j) i =
      (Real.sqrt (pauliWeight p j) : ℂ) * (pauliSign k j : ℂ) *
        (pauli k * pauli j) b i := by
    simp [Matrix.mul_apply, Matrix.kronecker_apply, canonicalIsometry,
      pauliEnvironmentUnitary, Matrix.diagonal_apply, Fintype.sum_prod_type,
      Finset.mul_sum, Finset.sum_mul, mul_ite, ite_mul, Complex.real_smul]
    ring
  rw [hl, hr, hcomm, Complex.real_smul]
  ring

namespace CPTP

def ofCompleteKraus {I O K : Type*} [Fintype I] [Fintype O] [Fintype K]
    [DecidableEq I] [DecidableEq O] (L : K → Matrix O I ℂ)
    (hL : ∑ k, (L k).conjTranspose * L k = 1) : CPTP I O where
  map := QuantumProver.SuperchannelDiscrimination.KrausCompletion.krausMap L
  completelyPositive := by
    apply (MatrixBridge.completelyPositive_iff _).mpr
    intro n A hA
    exact QuantumProver.SuperchannelDiscrimination.KrausCompletion.krausMap_completelyPositive
      L (Fin n) hA
  tracePreserving :=
    QuantumProver.SuperchannelDiscrimination.KrausCompletion.krausAction_tracePreserving L hL

@[simp] theorem ofCompleteKraus_apply {I O K : Type*}
    [Fintype I] [Fintype O] [Fintype K] [DecidableEq I] [DecidableEq O]
    (L : K → Matrix O I ℂ) (hL : ∑ k, (L k).conjTranspose * L k = 1)
    (A : QMatrix I) : (ofCompleteKraus L hL).map A =
      ∑ k, L k * A * (L k).conjTranspose := rfl

end CPTP

def pauliFlagEmbedding {E : Type*} [DecidableEq E] (k : CanonicalEnvironment) :
    Matrix (CanonicalEnvironment × E) E ℂ :=
  fun x e => if x=(k,e) then 1 else 0

theorem pauliFlagEmbedding_isometry {E : Type*} [Fintype E] [DecidableEq E]
    (k : CanonicalEnvironment) : IsIsometry (pauliFlagEmbedding (E:=E) k) := by
  ext i j
  simp [IsIsometry, pauliFlagEmbedding, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Fintype.sum_prod_type, Prod.mk.injEq,
    Matrix.one_apply, eq_comm]

theorem gram_left_isometry {I E O : Type*} [Fintype I] [Fintype E] [Fintype O]
    [DecidableEq I] [DecidableEq E] [DecidableEq O]
    (V : Matrix O E ℂ) (hV : IsIsometry V) (K : Matrix E I ℂ) :
    (V*K).conjTranspose*(V*K) = K.conjTranspose*K := by
  rw [Matrix.conjTranspose_mul, Matrix.mul_assoc,
    ← Matrix.mul_assoc V.conjTranspose V K, hV, Matrix.one_mul]

def pauliFlagKraus {E : Type*} [Fintype E] [DecidableEq E]
    (S : CPTP CanonicalEnvironment E)
    (kg : CanonicalEnvironment × (CanonicalEnvironment × E)) :
    Matrix (CanonicalEnvironment × E) CanonicalEnvironment ℂ :=
  (1/2 : ℂ) • ((pauliFlagEmbedding (E:=E) kg.1 * S.canonicalKraus kg.2) *
    pauliEnvironmentUnitary kg.1)

theorem pauliFlagKraus_fixed_gram {E : Type*} [Fintype E] [DecidableEq E]
    (S : CPTP CanonicalEnvironment E) (k : CanonicalEnvironment) :
    (∑ g : CanonicalEnvironment × E,
      (pauliFlagKraus S (k,g)).conjTranspose * pauliFlagKraus S (k,g)) =
      (1/4 : ℂ) • (1 : QMatrix CanonicalEnvironment) := by
  have hterm (g : CanonicalEnvironment × E) :
      (pauliFlagKraus S (k,g)).conjTranspose * pauliFlagKraus S (k,g) =
      (1/4 : ℂ) • ((pauliEnvironmentUnitary k).conjTranspose *
        ((S.canonicalKraus g).conjTranspose * S.canonicalKraus g) *
          pauliEnvironmentUnitary k) := by
    have hraw :
        ((pauliFlagEmbedding (E:=E) k * S.canonicalKraus g) * pauliEnvironmentUnitary k).conjTranspose *
          ((pauliFlagEmbedding (E:=E) k * S.canonicalKraus g) * pauliEnvironmentUnitary k) =
        (pauliEnvironmentUnitary k).conjTranspose *
          ((S.canonicalKraus g).conjTranspose * S.canonicalKraus g) *
          pauliEnvironmentUnitary k := by
      calc
        _ = (pauliEnvironmentUnitary k).conjTranspose *
            ((pauliFlagEmbedding (E:=E) k * S.canonicalKraus g).conjTranspose *
              (pauliFlagEmbedding (E:=E) k * S.canonicalKraus g)) *
                pauliEnvironmentUnitary k := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
        _ = _ := by rw [gram_left_isometry (pauliFlagEmbedding (E:=E) k)
          (pauliFlagEmbedding_isometry (E:=E) k)]
    rw [pauliFlagKraus, Matrix.conjTranspose_smul, Matrix.smul_mul,
      Matrix.mul_smul, smul_smul]
    norm_num
    simpa only [Matrix.conjTranspose_mul] using hraw
  simp_rw [hterm]
  rw [← Finset.smul_sum, ← Matrix.sum_mul, ← Matrix.mul_sum, S.canonicalKraus_complete]
  simpa [Matrix.smul_mul, Matrix.mul_smul] using
    congrArg (fun M : QMatrix CanonicalEnvironment => (1/4 : ℂ) • M)
      (pauliEnvironmentUnitary_isometry k)

theorem pauliFlagKraus_complete {E : Type*} [Fintype E] [DecidableEq E]
    (S : CPTP CanonicalEnvironment E) :
    ∑ kg, (pauliFlagKraus S kg).conjTranspose * pauliFlagKraus S kg = 1 := by
  rw [Fintype.sum_prod_type]
  simp_rw [pauliFlagKraus_fixed_gram]
  ext i j
  by_cases hij : i=j <;>
    norm_num [Fin.sum_univ_succ, Matrix.sum_apply, Matrix.add_apply,
      Matrix.smul_apply, Matrix.one_apply, hij]

def pauliFlagSquashing {E : Type*} [Fintype E] [DecidableEq E]
    (S : CPTP CanonicalEnvironment E) :
    CPTP CanonicalEnvironment (CanonicalEnvironment × E) :=
  CPTP.ofCompleteKraus (pauliFlagKraus S) (pauliFlagKraus_complete S)

def bellKet : (Qubit × Qubit) → ℂ :=
  fun x => if x.1=x.2 then (splitterScale : ℂ) else 0

theorem bellKet_normalized : IsNormalized bellKet := by
  norm_num [IsNormalized, vectorNormSq, QuantumProver.WernerEndpoint.vectorNormSq, bellKet,
    Fintype.sum_prod_type, Fin.sum_univ_succ, Complex.normSq_apply,
    splitterScale_sq]
  nlinarith [splitterScale_sq]

theorem fourImageVector_actual_stinespring {E : Type*} [Fintype E] [DecidableEq E]
    (p : ℝ) (S : CPTP CanonicalEnvironment E) :
    fourImageVector p (squashingImageMatrices S) =
      fun x => (S.stinespring.withReference (Qubit×Qubit)).amplitudes
        (extendedInputKet p bellKet) x.1 x.2 := by
  funext x
  rcases x with ⟨⟨⟨r,b⟩,e⟩,g⟩
  simp [fourImageVector, squashingImageMatrices, QuantumProver.WernerEndpoint.Stinespring.amplitudes,
    QuantumProver.WernerEndpoint.Stinespring.withReference, QuantumProver.WernerEndpoint.Stinespring.referenceCoeff,
    extendedInputKet, canonicalIsometry, bellKet, Fintype.sum_prod_type,
    Finset.mul_sum, Finset.sum_mul, mul_assoc, mul_left_comm, mul_comm]

theorem postSquashing_bell_fourImages {E : Type*} [Fintype E] [DecidableEq E]
    (p : ℝ) (S : CPTP CanonicalEnvironment E) :
    postSquashing p bellKet S =
      partialTraceRight (pureDensity (fourImageVector p (squashingImageMatrices S))) := by
  rw [fourImageVector_actual_stinespring]
  exact S.amplify_pureDensity_eq_reduced (extendedInputKet p bellKet)

theorem postSquashing_bell_AE_gram {E : Type*} [Fintype E] [DecidableEq E]
    (p : ℝ) (S : CPTP CanonicalEnvironment E) :
    traceMiddle (postSquashing p bellKet S) =
      fourImageAmplitudeE p (squashingImageMatrices S) *
        (fourImageAmplitudeE p (squashingImageMatrices S)).conjTranspose := by
  rw [postSquashing_bell_fourImages, fourImageE_gram]

namespace CPTP

theorem amplify_partialTraceRight {I O R : Type*}
    [Fintype I] [Fintype O] [Fintype R]
    [DecidableEq I] [DecidableEq O] [DecidableEq R]
    (S : CPTP I O) (A : QMatrix (R×I)) :
    partialTraceRight (amplify S.map A) = partialTraceRight A := by
  ext r s
  exact S.tracePreserving (fun i j => A (r,i) (s,j))

end CPTP

theorem postSquashing_AB {R E : Type*} [Fintype R] [Fintype E]
    [DecidableEq R] [DecidableEq E] (p : ℝ)
    (ψ : (R×Qubit) → ℂ) (S : CPTP CanonicalEnvironment E) :
    partialTraceRight (postSquashing p ψ S) =
      partialTraceRight (pureDensity (extendedInputKet p ψ)) :=
  S.amplify_partialTraceRight _

theorem extendedInputKet_AB {R : Type*} [Fintype R] [DecidableEq R]
    {p : ℝ} (hp0 : 0  ≤  p) (hp1 : p  ≤  1) (ψ : (R×Qubit) → ℂ) :
    partialTraceRight (pureDensity (extendedInputKet p ψ)) =
      amplify (depolarizingChannel p hp0 hp1).map (pureDensity ψ) := by
  let N := canonicalStinespring p hp0 hp1
  have h := QuantumProver.WernerEndpoint.Stinespring.apply_pureDensity (N.withReference R) ψ
  change N.amplify (pureDensity ψ) =
    QuantumProver.WernerEndpoint.reducedLeft ((N.withReference R).amplitudes ψ) at h
  have hr : QuantumProver.WernerEndpoint.reducedLeft ((N.withReference R).amplitudes ψ) =
      partialTraceRight (pureDensity (fun x =>
        (N.withReference R).amplitudes ψ x.1 x.2)) := by
    ext x y
    rfl
  rw [hr] at h
  rw [extendedInputKet_eq_referenceAmplitude hp0 hp1, ← h]
  ext ⟨r,b⟩ ⟨s,c⟩
  rw [QuantumProver.WernerEndpoint.Stinespring.amplify_block]
  change (canonicalStinespring p hp0 hp1).apply
      (fun i j => pureDensity ψ (r,i) (s,j)) b c =
    (depolarizingChannel p hp0 hp1).map (fun i j => pureDensity ψ (r,i) (s,j)) b c
  exact (congrArg (fun M : QMatrix Qubit => M b c)
    (canonicalStinespring_apply hp0 hp1 (fun i j => pureDensity ψ (r,i) (s,j)))).trans
      (congrArg (fun M : QMatrix Qubit => M b c)
        (depolarizingChannel_apply hp0 hp1 (fun i j => pureDensity ψ (r,i) (s,j)))).symm

theorem bellDensity_partialTraceRight :
    partialTraceRight (pureDensity bellKet) = (1/2 : ℂ) • (1 : QMatrix Qubit) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [partialTraceRight, QuantumProver.WernerEndpoint.partialTraceLeft,
      pureDensity, QuantumProver.WernerEndpoint.pureDensity, QuantumProver.WernerEndpoint.crossDensity,
      bellKet, Fin.sum_univ_succ, Matrix.smul_apply, Matrix.one_apply,
      ← Complex.ofReal_mul, ← pow_two, splitterScale_sq, splitterScale_complex_sq]

theorem depolarizing_bell_density {p : ℝ} (hp0 : 0  ≤  p) (hp1 : p  ≤  1) :
    amplify (depolarizingChannel p hp0 hp1).map (pureDensity bellKet) =
      ((1-p : ℝ) : ℂ) • pureDensity bellKet +
        ((p/4 : ℝ) : ℂ) • (1 : QMatrix (Qubit×Qubit)) := by
  ext ⟨r,b⟩ ⟨s,c⟩
  change (depolarizingChannel p hp0 hp1).map
    (fun i j => pureDensity bellKet (r,i) (s,j)) b c = _
  apply (congrArg (fun M : QMatrix Qubit => M b c)
    (depolarizingChannel_apply hp0 hp1 (fun i j => pureDensity bellKet (r,i) (s,j)))).trans
  fin_cases r <;> fin_cases b <;> fin_cases s <;> fin_cases c <;>
    simp [amplify, depolarizingChannel_apply, depolarizing, pureDensity,
      QuantumProver.WernerEndpoint.pureDensity, QuantumProver.WernerEndpoint.crossDensity, bellKet,
      Matrix.trace, Matrix.diag, Fin.sum_univ_succ, Matrix.smul_apply, Pi.smul_apply,
      Matrix.one_apply, ← Complex.ofReal_mul, ← pow_two, splitterScale_sq,
      splitterScale_complex_sq] <;> ring

theorem postSquashing_bell_A_marginal {p : ℝ} (hp0 : 0  ≤  p) (hp1 : p  ≤  1)
    {E : Type*} [Fintype E] [DecidableEq E]
    (S : CPTP CanonicalEnvironment E) :
    partialTraceRight (partialTraceRight (postSquashing p bellKet S)) =
      (1/2 : ℂ) • (1 : QMatrix Qubit) := by
  rw [postSquashing_AB, extendedInputKet_AB hp0 hp1,
    CPTP.amplify_partialTraceRight, bellDensity_partialTraceRight]

theorem negMulLog_one_sub_bounds {x : ℝ} (hx0 : 0<x) (hx1 : x<1) :
    x-x^2   ≤   Real.negMulLog (1-x) ∧ Real.negMulLog (1-x)   ≤   x := by
  have ht : 0<1-x := by linarith
  have hupper := Real.log_le_sub_one_of_pos ht
  have hlower := Real.one_sub_inv_le_log_of_pos ht
  have hprodUpper := mul_le_mul_of_nonneg_left hupper (le_of_lt ht)
  have hprodLower := mul_le_mul_of_nonneg_left hlower (le_of_lt ht)
  have hinv : (1-x)*(1-x)⁻¹=1 := mul_inv_cancel₀ (ne_of_gt ht)
  rw [Real.negMulLog_def]
  constructor <;> nlinarith

theorem binaryEntropyNat_remainder {x : ℝ} (hx0 : 0<x) (hx1 : x<1) :
    |Real.binEntropy x - Real.negMulLog x - x|   ≤   x^2 := by
  rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  rcases negMulLog_one_sub_bounds hx0 hx1 with ⟨hl,hu⟩
  rw [abs_le]
  constructor <;> linarith

theorem binaryEntropyNat_le_atom_add {x : ℝ} (hx0 : 0<x) (hx1 : x<1) :
    Real.binEntropy x   ≤   Real.negMulLog x+x := by
  rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  linarith [(negMulLog_one_sub_bounds hx0 hx1).2]

theorem negMulLog_le_two_sqrt {x : ℝ} (hx0 : 0<x) :
    Real.negMulLog x   ≤   2*Real.sqrt x := by
  have hs : 0<Real.sqrt x := Real.sqrt_pos.2 hx0
  have hsq : Real.sqrt x^2=x := Real.sq_sqrt (le_of_lt hx0)
  have hinv : Real.sqrt x*(Real.sqrt x)⁻¹=1 := mul_inv_cancel₀ (ne_of_gt hs)
  have hxinv : x*(Real.sqrt x)⁻¹=Real.sqrt x := by
    calc
      _ = (Real.sqrt x)^2*(Real.sqrt x)⁻¹ :=
        congrArg (fun y : ℝ => y*(Real.sqrt x)⁻¹) hsq.symm
      _ = Real.sqrt x*(Real.sqrt x*(Real.sqrt x)⁻¹) := by ring
      _ = _ := by rw [hinv]; ring
  have hlog := Real.log_le_sub_one_of_pos (inv_pos.2 hs)
  rw [Real.log_inv, Real.log_sqrt (le_of_lt hx0)] at hlog
  have hprod := mul_le_mul_of_nonneg_left hlog (show 0  ≤  2*x by positivity)
  rw [Real.negMulLog_def]
  nlinarith

theorem binaryEntropyNat_le_three_sqrt {x : ℝ} (hx0 : 0<x) (hx1 : x<1) :
    Real.binEntropy x   ≤   3*Real.sqrt x := by
  have hsq : Real.sqrt x^2=x := Real.sq_sqrt (le_of_lt hx0)
  have hs0 := Real.sqrt_nonneg x
  have hs1 : Real.sqrt x  ≤  1 := by
    apply Real.sqrt_le_iff.mpr
    exact ⟨by norm_num, by nlinarith⟩
  have hxle : x  ≤  Real.sqrt x := by nlinarith
  exact (binaryEntropyNat_le_atom_add hx0 hx1).trans (by
    linarith [negMulLog_le_two_sqrt hx0])

def splitterSmallEigenvalue (u : ℝ) : ℝ := (1-Real.sqrt (1-4*u^2))/2

theorem splitterSmallEigenvalue_bounds {u : ℝ} (hu0 : 0<u) (hu1 : u  ≤  1/4) :
    0<splitterSmallEigenvalue u ∧ splitterSmallEigenvalue u<1 ∧
      splitterSmallEigenvalue u  ≤  2*u^2 := by
  have hd : 0  ≤  1-4*u^2 := by nlinarith
  have hs := Real.sqrt_nonneg (1-4*u^2)
  have hsq := Real.sq_sqrt hd
  have hs1 : Real.sqrt (1-4*u^2)<1 := by
    nlinarith [sq_nonneg (Real.sqrt (1-4*u^2)-1)]
  unfold splitterSmallEigenvalue
  constructor
  · linarith
  constructor
  · linarith
  · have hprod := mul_nonneg hs (show 0  ≤  1-Real.sqrt (1-4*u^2) by linarith)
    nlinarith

theorem splitterSmallEigenvalue_entropy {u : ℝ} (hu0 : 0<u) (hu1 : u  ≤  1/4) :
    Real.binEntropy (splitterSmallEigenvalue u)   ≤   6*u := by
  rcases splitterSmallEigenvalue_bounds hu0 hu1 with ⟨hq0,hq1,hqbound⟩
  have hs := Real.sqrt_nonneg (splitterSmallEigenvalue u)
  have hsq := Real.sq_sqrt (le_of_lt hq0)
  have hsle : Real.sqrt (splitterSmallEigenvalue u)  ≤  2*u := by
    apply Real.sqrt_le_iff.mpr
    exact ⟨by linarith, by nlinarith⟩
  exact (binaryEntropyNat_le_three_sqrt hq0 hq1).trans (by linarith)

def pureAGCoefficient {A B E G : Type*} (ψ : (((A×B)×E)×G) → ℂ) :
    Matrix (A×G) (B×E) ℂ :=
  fun ag be => ψ (((ag.1,be.1),be.2),ag.2)

theorem pure_BE_oppositeGram {A B E G : Type*}
    [Fintype A] [Fintype B] [Fintype E] [Fintype G]
    [DecidableEq A] [DecidableEq B] [DecidableEq E] [DecidableEq G]
    (ψ : (((A×B)×E)×G) → ℂ) :
    traceFirst (partialTraceRight (pureDensity ψ)) =
      ((pureAGCoefficient ψ).conjTranspose * pureAGCoefficient ψ).transpose := by
  ext ⟨b,e⟩ ⟨c,f⟩
  simp [traceFirst, partialTraceRight, QuantumProver.WernerEndpoint.partialTraceLeft,
    pureDensity, QuantumProver.WernerEndpoint.pureDensity, QuantumProver.WernerEndpoint.crossDensity,
    Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.transpose_apply,
    Fintype.sum_prod_type, pureAGCoefficient, mul_comm]

theorem cmiNat_pure_complementary {A B E G : Type*}
    [Fintype A] [Fintype B] [Fintype E] [Fintype G]
    [DecidableEq A] [DecidableEq B] [DecidableEq E] [DecidableEq G]
    (ψ : (((A×B)×E)×G) → ℂ) :
    cmiNat (partialTraceRight (pureDensity ψ)) =
      (entropyNat (traceMiddle (partialTraceRight (pureDensity ψ))) -
        entropyNat (partialTraceLeft (partialTraceRight (pureDensity ψ)))) +
      (entropyNat (pureAGCoefficient ψ * (pureAGCoefficient ψ).conjTranspose) -
        entropyNat (partialTraceLeft (pureDensity ψ))) := by
  let M : Matrix ((A×B)×E) G ℂ := fun x g => ψ (x,g)
  have hABE : partialTraceRight (pureDensity ψ) = M*M.conjTranspose :=
    pureDensity_partialTraceRight_gram M
  have hG : partialTraceLeft (pureDensity ψ) = (M.conjTranspose*M).transpose :=
    pureDensity_partialTraceLeft_gram M
  have hSABE : entropyNat (partialTraceRight (pureDensity ψ)) =
      entropyNat (partialTraceLeft (pureDensity ψ)) := by
    rw [hABE,hG,entropyNat_transpose (Matrix.posSemidef_conjTranspose_mul_self M).1]
    exact (entropyNat_oppositeGram M).symm
  have hSBE : entropyNat (traceFirst (partialTraceRight (pureDensity ψ))) =
      entropyNat (pureAGCoefficient ψ * (pureAGCoefficient ψ).conjTranspose) := by
    rw [pure_BE_oppositeGram,
      entropyNat_transpose (Matrix.posSemidef_conjTranspose_mul_self (pureAGCoefficient ψ)).1]
    exact entropyNat_oppositeGram (pureAGCoefficient ψ)
  unfold cmiNat
  rw [hSABE,hSBE]
  ring

theorem entropyNat_diagonalReal {I : Type*} [Fintype I] [DecidableEq I]
    (d : I → ℝ) : entropyNat (Matrix.diagonal (fun i => (d i : ℂ))) =
      ∑ i, Real.negMulLog (d i) := by
  rw [entropyNat, QuantumProver.SuperchannelDiscrimination.TensorEntropy.cfc_diagonal_real,
    Matrix.trace_diagonal]
  simp [Complex.re_sum]

theorem entropyNat_realSymmetricTwo (a b z : ℝ) :
    entropyNat (realSymmetricTwo a b z) =
      Real.negMulLog (symmetricTwoPlus a b z) +
        Real.negMulLog (symmetricTwoMinus a b z) := by
  let d : Qubit → ℝ := fun i =>
    if i=0 then symmetricTwoPlus a b z else symmetricTwoMinus a b z
  have hd : (Matrix.diagonal (fun i => (d i : ℂ))).IsHermitian := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [d, Matrix.conjTranspose_apply, Matrix.diagonal_apply]
  have hchar : (realSymmetricTwo a b z).charpoly =
      (Matrix.diagonal (fun i => (d i : ℂ))).charpoly := by
    simpa only [d, apply_ite] using realSymmetricTwo_charpoly a b z
  rw [entropyNat_eq_of_charpoly_eq (realSymmetricTwo_hermitian a b z) hd hchar,
    entropyNat_diagonalReal]
  norm_num [d, Fin.sum_univ_succ]

def splitterBinaryState (u : ℝ) : QMatrix Qubit :=
  realSymmetricTwo (1-u) u (Real.sqrt ((1-2*u)*u))

theorem splitterBinaryState_trace (u : ℝ) : Matrix.trace (splitterBinaryState u) = 1 := by
  simp [splitterBinaryState, realSymmetricTwo, Matrix.trace, Matrix.diag,
    Fin.sum_univ_succ] <;> ring

theorem splitterBinaryState_eigenvalues {u : ℝ} (hu0 : 0  ≤  u) (hu1 : u  ≤  1/2) :
    symmetricTwoPlus (1-u) u (Real.sqrt ((1-2*u)*u)) = 1-splitterSmallEigenvalue u ∧
    symmetricTwoMinus (1-u) u (Real.sqrt ((1-2*u)*u)) = splitterSmallEigenvalue u := by
  have hf : 0  ≤  1-2*u := by linarith
  have hsq := Real.sq_sqrt (mul_nonneg hf hu0)
  have hdisc : (1-u-u)^2+4*(Real.sqrt ((1-2*u)*u))^2 = 1-4*u^2 := by
    nlinarith
  unfold symmetricTwoPlus symmetricTwoMinus symmetricTwoGap splitterSmallEigenvalue
  rw [hdisc]
  constructor <;> ring

theorem splitterBinaryState_entropy {u : ℝ} (hu0 : 0  ≤  u) (hu1 : u  ≤  1/2) :
    entropyNat (splitterBinaryState u) = Real.binEntropy (splitterSmallEigenvalue u) := by
  rw [splitterBinaryState, entropyNat_realSymmetricTwo]
  rcases splitterBinaryState_eigenvalues hu0 hu1 with ⟨hp,hm⟩
  rw [hp,hm,Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  ring

theorem CPTP.amplify_eq_chosen_stinespring {I O G R : Type*}
    [Fintype I] [Fintype O] [Fintype G] [Fintype R]
    [DecidableEq I] [DecidableEq O] [DecidableEq G] [DecidableEq R]
    (S : CPTP I O) (N : QuantumProver.WernerEndpoint.Stinespring I O G)
    (hN : ∀ ρ : QMatrix I, N.apply ρ = S.map ρ)
    (ρ : QMatrix (R×I)) : amplify S.map ρ = N.amplify ρ := by
  ext ⟨r,b⟩ ⟨s,c⟩
  rw [QuantumProver.WernerEndpoint.Stinespring.amplify_block]
  exact (congrArg (fun X : QMatrix O => X b c)
    (hN (fun i j => ρ (r,i) (s,j)))).symm

theorem CPTP.amplify_pureDensity_eq_chosen_stinespring {I O G R : Type*}
    [Fintype I] [Fintype O] [Fintype G] [Fintype R]
    [DecidableEq I] [DecidableEq O] [DecidableEq G] [DecidableEq R]
    (S : CPTP I O) (N : QuantumProver.WernerEndpoint.Stinespring I O G)
    (hN : ∀ ρ : QMatrix I, N.apply ρ = S.map ρ)
    (ψ : (R×I) → ℂ) :
    amplify S.map (pureDensity ψ) =
      partialTraceRight (pureDensity (fun x : (R×O)×G =>
        (N.withReference R).amplitudes ψ x.1 x.2)) := by
  rw [S.amplify_eq_chosen_stinespring N hN]
  exact (N.withReference R).apply_pureDensity ψ

def splitterStinespring : QuantumProver.WernerEndpoint.Stinespring CanonicalEnvironment
    CanonicalEnvironment CanonicalEnvironment :=
  ⟨splitterCoefficient, splitterCoefficient_isometry⟩

theorem splitterStinespring_apply (ρ : QMatrix CanonicalEnvironment) :
    splitterStinespring.apply ρ = splitterSquashing.map ρ := by
  ext e f
  simp [splitterStinespring, QuantumProver.WernerEndpoint.Stinespring.apply,
    QuantumProver.WernerEndpoint.partialTraceLeft, splitterSquashing, splitterKraus,
    KrausFamily.toCPTP, KrausFamily.toLinearMap, KrausFamily.apply,
    Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.sum_apply,
    Fintype.sum_prod_type, Finset.mul_sum, Finset.sum_mul] <;> ring

def splitterImageMatrices (j : CanonicalEnvironment) :
    Matrix CanonicalEnvironment CanonicalEnvironment ℂ :=
  fun e g => splitterCoefficient (e,g) j

theorem fourImageVector_splitter_stinespring (p : ℝ) :
    fourImageVector p splitterImageMatrices =
      fun x => (splitterStinespring.withReference (Qubit×Qubit)).amplitudes
        (extendedInputKet p bellKet) x.1 x.2 := by
  funext x
  rcases x with ⟨⟨⟨r,b⟩,e⟩,g⟩
  simp [fourImageVector, splitterImageMatrices, splitterStinespring,
    QuantumProver.WernerEndpoint.Stinespring.amplitudes,
    QuantumProver.WernerEndpoint.Stinespring.withReference,
    QuantumProver.WernerEndpoint.Stinespring.referenceCoeff,
    extendedInputKet, canonicalIsometry, bellKet, Fintype.sum_prod_type,
    Finset.mul_sum, Finset.sum_mul, mul_assoc, mul_left_comm, mul_comm]

theorem postSquashing_bell_splitter_fourImages (p : ℝ) :
    postSquashing p bellKet splitterSquashing =
      partialTraceRight (pureDensity (fourImageVector p splitterImageMatrices)) := by
  rw [fourImageVector_splitter_stinespring]
  exact splitterSquashing.amplify_pureDensity_eq_chosen_stinespring
    splitterStinespring splitterStinespring_apply (extendedInputKet p bellKet)

def splitterTripletScale : ℝ := (Real.sqrt 3)⁻¹

theorem splitterTripletScale_sq : splitterTripletScale^2 = 1/3 := by
  rw [splitterTripletScale, inv_pow, Real.sq_sqrt (by norm_num : (0:ℝ)  ≤  3)]
  norm_num

theorem splitterTripletScale_sqrt : splitterTripletScale * Real.sqrt 3 = 1 := by
  unfold splitterTripletScale
  exact inv_mul_cancel₀ (ne_of_gt (Real.sqrt_pos.mpr (by norm_num)))

theorem splitterTripletScale_complex_sq : (splitterTripletScale : ℂ)^2=1/3 := by
  rw [← Complex.ofReal_pow, splitterTripletScale_sq]
  norm_num

def splitterSupportEmbedding : Matrix (Qubit×CanonicalEnvironment) (Qubit×Qubit) ℂ :=
  fun x ik => if ik.2=0 then (if x.2=0 ∧ x.1=ik.1 then 1 else 0)
    else if x.2=0 then 0 else (splitterTripletScale : ℂ) * pauli x.2 ik.1 x.1

theorem splitterSupportEmbedding_isometry : IsIsometry splitterSupportEmbedding := by
  have hI : ((splitterTripletScale : ℂ)*Complex.I)^2=-(1/3 : ℂ) := by
    rw [mul_pow,splitterTripletScale_complex_sq,Complex.I_sq]
    norm_num
  ext ⟨i,k⟩ ⟨j,l⟩
  fin_cases i <;> fin_cases k <;> fin_cases j <;> fin_cases l <;>
    norm_num [splitterSupportEmbedding, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fintype.sum_prod_type, Fin.sum_univ_succ, pauli,
      ← Complex.ofReal_mul, ← pow_two, splitterTripletScale_sq,
      splitterTripletScale_complex_sq, Complex.star_def,hI] <;>
    (try decide) <;> norm_num [hI]

def splitterAlgebraAmplitude (f a : ℝ) :
    Matrix (Qubit×CanonicalEnvironment) (Qubit×CanonicalEnvironment) ℂ :=
  (splitterScale : ℂ) • ∑ j,
    (if j=0 then (f:ℂ) else (a:ℂ)) • ((pauli j).transpose ⊗ₖ splitterImageMatrices j)

def splitterAlgebraBinary (f a : ℝ) : QMatrix Qubit :=
  realSymmetricTwo (f^2+3*a^2/2) (3*a^2/2)
    (Real.sqrt 3 * splitterScale * f * a)

set_option maxHeartbeats 1200000 in

theorem splitterAlgebraAmplitude_gram (f a : ℝ) :
    splitterAlgebraAmplitude f a * (splitterAlgebraAmplitude f a).conjTranspose =
      splitterSupportEmbedding *
        (((1/2 : ℂ) • (1 : QMatrix Qubit)) ⊗ₖ splitterAlgebraBinary f a) *
          splitterSupportEmbedding.conjTranspose := by
  have hcross : f*a*splitterScale*splitterTripletScale*Real.sqrt 3 =
      f*a*splitterScale := by
    calc
      _ = f*a*splitterScale*(splitterTripletScale*Real.sqrt 3) := by ring
      _ = _ := by rw [splitterTripletScale_sqrt]; ring
  have hs3 : splitterScale^3=splitterScale/2 := by
    calc
      _ = splitterScale*splitterScale^2 := by ring
      _ = _ := by rw [splitterScale_sq]; ring
  have hs4 : splitterScale^4=(1/4 : ℝ) := by
    calc
      _ = (splitterScale^2)^2 := by ring
      _ = _ := by rw [splitterScale_sq]; norm_num
  ext ⟨r,e⟩ ⟨s,g⟩
  fin_cases r <;> fin_cases e <;> fin_cases s <;> fin_cases g <;>
    simp [splitterAlgebraAmplitude, splitterAlgebraBinary, realSymmetricTwo,
      splitterSupportEmbedding, splitterImageMatrices, splitterCoefficient,
      Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.sum_apply,
      Matrix.smul_apply, Pi.smul_apply, Matrix.one_apply, Matrix.kronecker_apply,
      Matrix.transpose_apply, Fintype.sum_prod_type, Fin.sum_univ_succ,
      pauli, Complex.star_def, mul_add, add_mul] <;>
    apply Complex.ext <;>
    simp [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im] <;>
    ring_nf <;>
    (try simp [← Complex.ofReal_pow,splitterScale_sq,splitterTripletScale_sq,hs3,hs4]) <;>
    ring_nf <;> first | rfl | nlinarith [hcross]

theorem posSemidef_of_charpoly_eq {I : Type*} [Fintype I] [DecidableEq I]
    {A B : QMatrix I} (hA : A.IsHermitian) (hB : B.PosSemidef)
    (hc : A.charpoly=B.charpoly) : A.PosSemidef := by
  apply hA.posSemidef_iff_eigenvalues_nonneg.mpr
  rw [(hA.eigenvalues_eq_eigenvalues_iff hB.1).mpr hc]
  exact hB.1.posSemidef_iff_eigenvalues_nonneg.mp hB

theorem splitterBinaryState_positive {u : ℝ} (hu0 : 0  ≤  u) (hu1 : u  ≤  1/2) :
    (splitterBinaryState u).PosSemidef := by
  have hdisc : 0  ≤  1-4*u^2 := by nlinarith
  have hs0 := Real.sqrt_nonneg (1-4*u^2)
  have hs1 : Real.sqrt (1-4*u^2)  ≤  1 := by
    apply Real.sqrt_le_iff.mpr
    exact ⟨by norm_num, by nlinarith⟩
  have hq0 : 0  ≤  splitterSmallEigenvalue u := by
    unfold splitterSmallEigenvalue
    linarith
  have hq1 : splitterSmallEigenvalue u  ≤  1 := by
    unfold splitterSmallEigenvalue
    linarith
  rcases splitterBinaryState_eigenvalues hu0 hu1 with ⟨hp,hm⟩
  apply posSemidef_of_charpoly_eq
    (realSymmetricTwo_hermitian (1-u) u (Real.sqrt ((1-2*u)*u)))
    _ (realSymmetricTwo_charpoly (1-u) u (Real.sqrt ((1-2*u)*u)))
  apply Matrix.PosSemidef.diagonal
  intro i
  fin_cases i
  · simp [hp]
    exact_mod_cast hq1
  · simp [hm]
    exact_mod_cast hq0

theorem entropyNat_kronecker {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] {A : QMatrix I} {B : QMatrix J}
    (hA : A.PosSemidef) (hAT : Matrix.trace A=1)
    (hB : B.PosSemidef) (hBT : Matrix.trace B=1) :
    entropyNat (A ⊗ₖ B)=entropyNat A+entropyNat B := by
  have h := QuantumProver.SuperchannelDiscrimination.TensorEntropy.entropyBits_kronecker
    ⟨hA,hAT⟩ ⟨hB,hBT⟩
  rw [QuantumProver.ConditionalEntropy.ConditionalRange.entropyBits_eq_isotropicEntropy_div_log_two,
    QuantumProver.ConditionalEntropy.ConditionalRange.entropyBits_eq_isotropicEntropy_div_log_two,
    QuantumProver.ConditionalEntropy.ConditionalRange.entropyBits_eq_isotropicEntropy_div_log_two] at h
  change entropyNat (A ⊗ₖ B)/Real.log 2 =
    entropyNat A/Real.log 2+entropyNat B/Real.log 2 at h
  have hl : Real.log 2≠0 := ne_of_gt (Real.log_pos (by norm_num))
  field_simp [hl] at h
  exact h

theorem splitterAlgebraBinary_eq_binaryState {f a : ℝ}
    (hf : 0  ≤  f) (ha : 0  ≤  a) (hn : f^2+3*a^2=1) :
    splitterAlgebraBinary f a = splitterBinaryState (3*a^2/2) := by
  have hs : 0  ≤  splitterScale := by unfold splitterScale; positivity
  have hz : 0  ≤  Real.sqrt 3*splitterScale*f*a := by positivity
  have hf2 : f^2=1-3*a^2 := by linarith
  have hz2 : (Real.sqrt 3*splitterScale*f*a)^2 =
      (1-2*(3*a^2/2))*(3*a^2/2) := by
    simp only [mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ)  ≤  3),
      splitterScale_sq,hf2]
    ring
  have hroot : Real.sqrt 3*splitterScale*f*a =
      Real.sqrt ((1-2*(3*a^2/2))*(3*a^2/2)) := by
    calc
      _ = Real.sqrt ((Real.sqrt 3*splitterScale*f*a)^2) := (Real.sqrt_sq hz).symm
      _ = _ := by rw [hz2]
  unfold splitterAlgebraBinary splitterBinaryState
  rw [hroot,hf2]
  congr 1 <;> ring

theorem fourImageAmplitudeE_splitter_algebra (p : ℝ) :
    fourImageAmplitudeE p splitterImageMatrices =
      splitterAlgebraAmplitude (Real.sqrt (1-3*p/4)) (Real.sqrt (p/4)) := by
  rw [fourImageAmplitudeE_pauli]
  simp [splitterAlgebraAmplitude,pauliWeight,apply_ite]

theorem postSquashing_bell_splitter_AE_supported {p : ℝ}
    (hp0 : 0  ≤  p) (hp1 : p  ≤  1) :
    traceMiddle (postSquashing p bellKet splitterSquashing) =
      splitterSupportEmbedding *
        (((1/2 : ℂ) • (1 : QMatrix Qubit)) ⊗ₖ splitterBinaryState (3*p/8)) *
          splitterSupportEmbedding.conjTranspose := by
  have hF : 0  ≤  1-3*p/4 := by linarith
  have ha : 0  ≤  p/4 := by positivity
  have hf2 := Real.sq_sqrt hF
  have ha2 := Real.sq_sqrt ha
  have hn : (Real.sqrt (1-3*p/4))^2+3*(Real.sqrt (p/4))^2=1 := by
    rw [hf2,ha2]
    ring
  rw [postSquashing_bell_splitter_fourImages, fourImageE_gram,
    fourImageAmplitudeE_splitter_algebra, splitterAlgebraAmplitude_gram,
    splitterAlgebraBinary_eq_binaryState (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hn,
    ha2]
  have hu : (3*(p/4)/2 : ℝ)=3*p/8 := by ring
  rw [hu]

theorem CPTP.amplify_partialTraceLeft {I O R : Type*}
    [Fintype I] [Fintype O] [Fintype R]
    [DecidableEq I] [DecidableEq O] [DecidableEq R]
    (S : CPTP I O) (ρ : QMatrix (R×I)) :
    partialTraceLeft (amplify S.map ρ)=S.map (partialTraceLeft ρ) := by
  let blocks : R → QMatrix I := fun r i j => ρ (r,i) (r,j)
  have ht : partialTraceLeft ρ=∑ r,blocks r := by
    ext i j
    simp [partialTraceLeft,QuantumProver.WernerEndpoint.partialTraceRight,blocks,Matrix.sum_apply]
  rw [ht,map_sum]
  ext o p
  simp [partialTraceLeft,QuantumProver.WernerEndpoint.partialTraceRight,amplify,blocks,Matrix.sum_apply]

def pureBGCoefficient {A B E G : Type*} (ψ : (((A×B)×E)×G) → ℂ) :
    Matrix (B×G) (A×E) ℂ :=
  fun bg ae => ψ (((ae.1,bg.1),ae.2),bg.2)

theorem pure_AE_oppositeGram {A B E G : Type*}
    [Fintype A] [Fintype B] [Fintype E] [Fintype G]
    [DecidableEq A] [DecidableEq B] [DecidableEq E] [DecidableEq G]
    (ψ : (((A×B)×E)×G) → ℂ) :
    traceMiddle (partialTraceRight (pureDensity ψ))=
      ((pureBGCoefficient ψ).conjTranspose*pureBGCoefficient ψ).transpose := by
  ext ⟨a,e⟩ ⟨c,f⟩
  simp [traceMiddle,partialTraceRight,QuantumProver.WernerEndpoint.partialTraceLeft,
    pureDensity,QuantumProver.WernerEndpoint.pureDensity,QuantumProver.WernerEndpoint.crossDensity,
    Matrix.mul_apply,Matrix.conjTranspose_apply,Matrix.transpose_apply,
    Fintype.sum_prod_type,pureBGCoefficient,mul_comm]

theorem pure_BG_environmental_margin {A B E G : Type*}
    [Fintype A] [Fintype B] [Fintype E] [Fintype G]
    [DecidableEq A] [DecidableEq B] [DecidableEq E] [DecidableEq G]
    (ψ : (((A×B)×E)×G) → ℂ) :
    partialTraceLeft (pureBGCoefficient ψ*(pureBGCoefficient ψ).conjTranspose)=
      partialTraceLeft (pureDensity ψ) := by
  ext g h
  simp only [partialTraceLeft,QuantumProver.WernerEndpoint.partialTraceRight,
    pureDensity,QuantumProver.WernerEndpoint.pureDensity,QuantumProver.WernerEndpoint.crossDensity,
    Matrix.mul_apply,Matrix.conjTranspose_apply,pureBGCoefficient,
    Fintype.sum_prod_type]
  rw [Finset.sum_comm]

theorem cmiNat_pure_retained_conditional {A B E G : Type*}
    [Fintype A] [Fintype B] [Fintype E] [Fintype G]
    [DecidableEq A] [DecidableEq B] [DecidableEq E] [DecidableEq G]
    (ψ : (((A×B)×E)×G) → ℂ) :
    cmiNat (partialTraceRight (pureDensity ψ))=
      (entropyNat (traceFirst (partialTraceRight (pureDensity ψ)))-
        entropyNat (partialTraceLeft (partialTraceRight (pureDensity ψ))))+
      (entropyNat (pureBGCoefficient ψ*(pureBGCoefficient ψ).conjTranspose)-
        entropyNat (partialTraceLeft
          (pureBGCoefficient ψ*(pureBGCoefficient ψ).conjTranspose))) := by
  let M : Matrix ((A×B)×E) G ℂ := fun x g => ψ (x,g)
  have hABE : partialTraceRight (pureDensity ψ)=M*M.conjTranspose :=
    pureDensity_partialTraceRight_gram M
  have hG : partialTraceLeft (pureDensity ψ)=(M.conjTranspose*M).transpose :=
    pureDensity_partialTraceLeft_gram M
  have hSABE : entropyNat (partialTraceRight (pureDensity ψ))=
      entropyNat (partialTraceLeft (pureDensity ψ)) := by
    rw [hABE,hG,entropyNat_transpose (Matrix.posSemidef_conjTranspose_mul_self M).1]
    exact (entropyNat_oppositeGram M).symm
  have hSAE : entropyNat (traceMiddle (partialTraceRight (pureDensity ψ)))=
      entropyNat (pureBGCoefficient ψ*(pureBGCoefficient ψ).conjTranspose) := by
    rw [pure_AE_oppositeGram,
      entropyNat_transpose (Matrix.posSemidef_conjTranspose_mul_self (pureBGCoefficient ψ)).1]
    exact entropyNat_oppositeGram (pureBGCoefficient ψ)
  unfold cmiNat
  rw [hSAE,hSABE,pure_BG_environmental_margin]
  ring

def splitterEnvironmentalState (u : ℝ) : QMatrix CanonicalEnvironment :=
  Matrix.diagonal (fun j => ((if j=0 then 1-u else u/3 : ℝ) : ℂ))

theorem splitterEnvironmentalState_entropy (u : ℝ) :
    entropyNat (splitterEnvironmentalState u)=Real.binEntropy u+u*Real.log 3 := by
  have hthird : Real.negMulLog (u/3) =
      (1/3)*Real.negMulLog u+(u/3)*Real.log 3 := by
    rw [div_eq_mul_inv, Real.negMulLog_mul]
    simp [Real.negMulLog, Real.log_inv] <;> ring
  rw [splitterEnvironmentalState, entropyNat_diagonalReal,
    Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  norm_num [Fin.sum_univ_succ]
  rw [hthird]
  ring

theorem halfIdentity_entropy :
    entropyNat ((1/2 : ℂ) • (1 : QMatrix Qubit))=Real.log 2 := by
  have hloghalf : Real.log (1/2 : ℝ)=-Real.log 2 := by
    rw [one_div,Real.log_inv]
  have heq : (1/2 : ℂ) • (1 : QMatrix Qubit) =
      Matrix.diagonal (fun _ : Qubit => ((1/2 : ℝ) : ℂ)) := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [Matrix.smul_apply,Matrix.one_apply]
  rw [heq,entropyNat_diagonalReal]
  norm_num [Fin.sum_univ_succ,Real.negMulLog,hloghalf] <;> ring

theorem entropyNat_postSquashing_bell_splitter_AE {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    entropyNat (traceMiddle (postSquashing p bellKet splitterSquashing)) =
      Real.log 2+Real.binEntropy (splitterSmallEigenvalue (3*p/8)) := by
  have hu0 : 0 ≤ 3*p/8 := by positivity
  have hu1 : 3*p/8 ≤ 1/2 := by linarith
  have hhalf : ((1/2 : ℂ) • (1 : QMatrix Qubit)).PosSemidef := by
    rw [← bellDensity_partialTraceRight]
    exact QuantumProver.WernerEndpoint.partialTraceLeft_posSemidef _ (pureDensity_positive bellKet)
  have hhalfT : Matrix.trace ((1/2 : ℂ) • (1 : QMatrix Qubit))=1 := by
    norm_num [Matrix.trace,Matrix.diag,Matrix.smul_apply,Fin.sum_univ_succ]
  have hK := splitterBinaryState_positive hu0 hu1
  rw [postSquashing_bell_splitter_AE_supported hp0 hp1,
    entropyNat_isometric_embedding splitterSupportEmbedding
      splitterSupportEmbedding_isometry (hhalf.kronecker hK).1,
    entropyNat_kronecker hhalf hhalfT hK (splitterBinaryState_trace _),
    halfIdentity_entropy,splitterBinaryState_entropy hu0 hu1]

theorem traceMiddle_environmental_margin {A B E : Type*}
    [Fintype A] [Fintype B] [Fintype E]
    [DecidableEq A] [DecidableEq B] [DecidableEq E]
    (ρ : QMatrix ((A×B)×E)) :
    partialTraceLeft (traceMiddle ρ)=partialTraceLeft ρ := by
  ext e f
  simp [partialTraceLeft,QuantumProver.WernerEndpoint.partialTraceRight,traceMiddle,
    Fintype.sum_prod_type]

theorem postSquashing_bell_splitter_E {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    partialTraceLeft (postSquashing p bellKet splitterSquashing)=
      splitterEnvironmentalState (3*p/8) := by
  rw [← traceMiddle_environmental_margin,postSquashing_bell_splitter_AE_supported hp0 hp1]
  ext e f
  fin_cases e <;> fin_cases f <;>
    norm_num [partialTraceLeft,QuantumProver.WernerEndpoint.partialTraceRight,
      splitterSupportEmbedding,splitterBinaryState,realSymmetricTwo,
      splitterEnvironmentalState,Matrix.mul_apply,Matrix.conjTranspose_apply,
      Matrix.kronecker_apply,Matrix.smul_apply,Pi.smul_apply,Matrix.one_apply,
      Fintype.sum_prod_type,Fin.sum_univ_succ,pauli,Complex.star_def,
      ← Complex.ofReal_mul,← pow_two,splitterTripletScale_complex_sq,
      splitterTripletScale_sq] <;> ring_nf <;>
    norm_num [splitterTripletScale_complex_sq,Complex.I_sq] <;> ring

theorem splitterCoefficient_swap (e g j : CanonicalEnvironment) :
    splitterCoefficient (e,g) j=splitterCoefficient (g,e) j := by
  fin_cases e <;> fin_cases g <;> fin_cases j <;>
    simp [splitterCoefficient]

theorem splitterImageMatrices_transpose (j : CanonicalEnvironment) :
    (splitterImageMatrices j).transpose=splitterImageMatrices j := by
  ext e g
  exact splitterCoefficient_swap g e j

theorem fourImageVector_splitter_swap (p : ℝ) (x : Qubit×Qubit)
    (e g : CanonicalEnvironment) :
    fourImageVector p splitterImageMatrices ((x,e),g)=
      fourImageVector p splitterImageMatrices ((x,g),e) := by
  unfold fourImageVector
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [splitterImageMatrices,splitterImageMatrices,splitterCoefficient_swap e g j]

theorem fourImageAmplitudeG_splitter (p : ℝ) :
    fourImageAmplitudeG p splitterImageMatrices=fourImageAmplitudeE p splitterImageMatrices := by
  rw [fourImageAmplitudeG_pauli,fourImageAmplitudeE_pauli]
  simp_rw [splitterImageMatrices_transpose]

theorem pureEnvironmentalMargins_eq_of_swap {X E : Type*}
    [Fintype X] [Fintype E] [DecidableEq X] [DecidableEq E]
    (ψ : ((X×E)×E) → ℂ)
    (hψ : ∀ x e g, ψ ((x,e),g)=ψ ((x,g),e)) :
    partialTraceLeft (partialTraceRight (pureDensity ψ))=
      partialTraceLeft (pureDensity ψ) := by
  ext e f
  simp only [partialTraceLeft,partialTraceRight,QuantumProver.WernerEndpoint.partialTraceLeft,
    QuantumProver.WernerEndpoint.partialTraceRight,pureDensity,QuantumProver.WernerEndpoint.pureDensity,
    QuantumProver.WernerEndpoint.crossDensity,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro g _
  rw [hψ x e g,hψ x f g]

theorem splitterBellCost {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    cmiBits (postSquashing p bellKet splitterSquashing)/2 =
      1+(Real.binEntropy (splitterSmallEigenvalue (3*p/8))-
        Real.binEntropy (3*p/8)-(3*p/8)*Real.log 3)/Real.log 2 := by
  let ψ := fourImageVector p splitterImageMatrices
  have hpost := postSquashing_bell_splitter_fourImages p
  have hG : partialTraceLeft (pureDensity ψ)=
      partialTraceLeft (postSquashing p bellKet splitterSquashing) := by
    rw [hpost]
    exact (pureEnvironmentalMargins_eq_of_swap ψ (fourImageVector_splitter_swap p)).symm
  have hAG : pureAGCoefficient ψ=fourImageAmplitudeG p splitterImageMatrices := rfl
  have hAE : fourImageAmplitudeE p splitterImageMatrices *
      (fourImageAmplitudeE p splitterImageMatrices).conjTranspose =
        traceMiddle (postSquashing p bellKet splitterSquashing) := by
    rw [hpost,fourImageE_gram]
  unfold cmiBits
  rw [hpost,cmiNat_pure_complementary,hAG,fourImageAmplitudeG_splitter,hAE,hG]
  rw [← hpost,entropyNat_postSquashing_bell_splitter_AE hp0 hp1,
    postSquashing_bell_splitter_E hp0 hp1,splitterEnvironmentalState_entropy]
  have hl : Real.log 2≠0 := ne_of_gt (Real.log_pos (by norm_num))
  field_simp [hl]
  ring

def splitterScalarBellCost (p : ℝ) : ℝ :=
  1+(Real.binEntropy (splitterSmallEigenvalue (3*p/8))-
    Real.binEntropy (3*p/8)-(3*p/8)*Real.log 3)/Real.log 2

theorem splitterScalarBellCost_lowNoise {p : ℝ}
    (hp0 : 0 < p) (hp1 : p  ≤  1/2) :
    |splitterScalarBellCost p-lowNoiseProfile p|  ≤
      (3*p/8)*(8+Real.log 8)/Real.log 2 := by
  let u : ℝ := 3*p/8
  have hu0 : 0 < u := by dsimp [u]; positivity
  have huq : u  ≤  1/4 := by dsimp [u]; linarith
  have hu1 : u < 1 := by linarith
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl8 : 0  ≤  Real.log 8 := Real.log_nonneg (by norm_num)
  have hmul : 0  ≤  u*Real.log 8 := mul_nonneg hu0.le hl8
  have hu2 : u^2  ≤  u := by nlinarith
  have hlogu : Real.log u=Real.log p+Real.log 3-Real.log 8 := by
    dsimp [u]
    rw [Real.log_div (mul_ne_zero (by norm_num) hp0.ne') (by norm_num),
      Real.log_mul (by norm_num) hp0.ne']
    ring
  rcases splitterSmallEigenvalue_bounds hu0 huq with ⟨hq0,hq1,_⟩
  have hqlo := Real.binEntropy_nonneg hq0.le hq1.le
  have hqhi := splitterSmallEigenvalue_entropy hu0 huq
  have hrem := binaryEntropyNat_remainder hu0 hu1
  rw [abs_le] at hrem
  have hid : splitterScalarBellCost p-lowNoiseProfile p =
      (Real.binEntropy (splitterSmallEigenvalue u)-u*(1+Real.log 8)-
        (Real.binEntropy u-Real.negMulLog u-u))/Real.log 2 := by
    unfold splitterScalarBellCost lowNoiseProfile
    change 1+(Real.binEntropy (splitterSmallEigenvalue u)-Real.binEntropy u-
        u*Real.log 3)/Real.log 2-(1-u*(Real.log (1/p)/Real.log 2)) = _
    rw [Real.negMulLog_def]
    dsimp only
    rw [hlogu,one_div,Real.log_inv]
    field_simp [hl.ne']
    ring
  rw [hid,abs_div,abs_of_pos hl]
  change |Real.binEntropy (splitterSmallEigenvalue u)-u*(1+Real.log 8)-
      (Real.binEntropy u-Real.negMulLog u-u)|/Real.log 2  ≤
        u*(8+Real.log 8)/Real.log 2
  apply div_le_div_of_nonneg_right _ hl.le
  rw [abs_le]
  constructor <;> nlinarith [hrem.1,hrem.2,hqlo,hqhi]

theorem splitterBellInput_lowNoise {p : ℝ} (hp0 : 0 < p) (hp1 : p  ≤  1/2) :
    |cmiBits (postSquashing p bellKet splitterSquashing)/2-lowNoiseProfile p|  ≤
      (3*p/8)*(8+Real.log 8)/Real.log 2 := by
  rw [splitterBellCost hp0.le (by linarith : p  ≤  1)]
  exact splitterScalarBellCost_lowNoise hp0 hp1

def inputCoefficient {R I : Type*} (ψ : (R×I) → ℂ) : Matrix I R ℂ :=
  fun i r => ψ (r,i)

def physicalPureExtension {R B E G : Type*}
    (M : Matrix ((B×E)×G) R ℂ) : (((R×B)×E)×G) → ℂ :=
  fun x => M ((x.1.1.2,x.1.2),x.2) x.1.1.1

def swapExtensionEG {B E G R : Type*} (M : Matrix ((B×E)×G) R ℂ) :
    Matrix ((B×G)×E) R ℂ := fun x r => M ((x.1.1,x.2),x.1.2) r

theorem physicalPureExtension_BE {R B E G : Type*}
    [Fintype R] [Fintype B] [Fintype E] [Fintype G]
    [DecidableEq R] [DecidableEq B] [DecidableEq E] [DecidableEq G]
    (M : Matrix ((B×E)×G) R ℂ) :
    traceFirst (partialTraceRight (pureDensity (physicalPureExtension M)))=
      partialTraceRight (M*M.conjTranspose) := by
  ext ⟨b,e⟩ ⟨c,f⟩
  simp only [traceFirst,partialTraceRight,QuantumProver.WernerEndpoint.partialTraceLeft,
    pureDensity,QuantumProver.WernerEndpoint.pureDensity,QuantumProver.WernerEndpoint.crossDensity,
    physicalPureExtension,Matrix.mul_apply,Matrix.conjTranspose_apply]
  rw [Finset.sum_comm]

theorem physicalPureExtension_BG {R B E G : Type*}
    [Fintype R] [Fintype B] [Fintype E] [Fintype G]
    [DecidableEq R] [DecidableEq B] [DecidableEq E] [DecidableEq G]
    (M : Matrix ((B×E)×G) R ℂ) :
    pureBGCoefficient (physicalPureExtension M)*
      (pureBGCoefficient (physicalPureExtension M)).conjTranspose =
        partialTraceRight (swapExtensionEG M*(swapExtensionEG M).conjTranspose) := by
  ext ⟨b,g⟩ ⟨c,h⟩
  simp only [pureBGCoefficient,physicalPureExtension,swapExtensionEG,
    partialTraceRight,QuantumProver.WernerEndpoint.partialTraceLeft,Matrix.mul_apply,
    Matrix.conjTranspose_apply,Fintype.sum_prod_type]
  rw [Finset.sum_comm]

theorem traceFirst_environmental_margin {A B E : Type*}
    [Fintype A] [Fintype B] [Fintype E]
    [DecidableEq A] [DecidableEq B] [DecidableEq E]
    (ρ : QMatrix ((A×B)×E)) :
    partialTraceLeft (traceFirst ρ)=partialTraceLeft ρ := by
  ext e f
  simp only [partialTraceLeft,QuantumProver.WernerEndpoint.partialTraceRight,traceFirst,
    Fintype.sum_prod_type]
  rw [Finset.sum_comm]

theorem pureInput_compression {R I O : Type*}
    [Fintype R] [Fintype I] [Fintype O]
    [DecidableEq R] [DecidableEq I] [DecidableEq O]
    (ψ : (R×I) → ℂ) (V : Matrix O I ℂ) :
    (V*inputCoefficient ψ)*(V*inputCoefficient ψ).conjTranspose =
      V*partialTraceLeft (pureDensity ψ)*V.conjTranspose := by
  let P : Matrix I R ℂ := fun i r => ψ (r,i)
  have hp : partialTraceLeft (pureDensity ψ)=P*P.conjTranspose := by
    ext i j
    simp [partialTraceLeft,QuantumProver.WernerEndpoint.partialTraceRight,pureDensity,
      QuantumProver.WernerEndpoint.pureDensity,QuantumProver.WernerEndpoint.crossDensity,P,
      Matrix.mul_apply,Matrix.conjTranspose_apply]
  change (V*P)*(V*P).conjTranspose = _
  rw [hp,Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]

def retainedCostNat {B E G : Type*} [Fintype B] [Fintype E] [Fintype G]
    [DecidableEq B] [DecidableEq E] [DecidableEq G]
    (M : Matrix ((B×E)×G) ((B×E)×G) ℂ)
    (N : Matrix ((B×G)×E) ((B×G)×E) ℂ) : ℝ :=
  (entropyNat (partialTraceRight M)-
    entropyNat (partialTraceLeft (partialTraceRight M)))+
  (entropyNat (partialTraceRight N)-
    entropyNat (partialTraceLeft (partialTraceRight N)))

theorem cmiNat_input_density {R I B E G : Type*}
    [Fintype R] [Fintype I] [Fintype B] [Fintype E] [Fintype G]
    [DecidableEq R] [DecidableEq I] [DecidableEq B] [DecidableEq E] [DecidableEq G]
    (ψ : (R×I) → ℂ) (V : Matrix ((B×E)×G) I ℂ) :
    cmiNat (partialTraceRight
      (pureDensity (physicalPureExtension (V*inputCoefficient ψ))))=
    retainedCostNat
      (V*partialTraceLeft (pureDensity ψ)*V.conjTranspose)
      (swapExtensionEG V*partialTraceLeft (pureDensity ψ)*(swapExtensionEG V).conjTranspose) := by
  rw [cmiNat_pure_retained_conditional,← traceFirst_environmental_margin,
    physicalPureExtension_BE,physicalPureExtension_BG]
  have hs : swapExtensionEG (V*inputCoefficient ψ)=
      swapExtensionEG V*inputCoefficient ψ := by
    ext x r
    rfl
  rw [hs,pureInput_compression,pureInput_compression]
  rfl

def jointSquashingCoefficient {E : Type*} [Fintype E] [DecidableEq E]
    (p : ℝ) (S : CPTP CanonicalEnvironment E) :
    Matrix ((Qubit×E)×(CanonicalEnvironment×E)) Qubit ℂ :=
  S.stinespring.referenceCoeff Qubit * canonicalIsometry p

theorem jointSquashingCoefficient_apply {E : Type*} [Fintype E] [DecidableEq E]
    (p : ℝ) (S : CPTP CanonicalEnvironment E) (b : Qubit) (e : E)
    (g : CanonicalEnvironment×E) (i : Qubit) :
    jointSquashingCoefficient p S ((b,e),g) i =
      ∑ j, S.stinespring.coeff (e,g) j * canonicalIsometry p (b,j) i := by
  simp [jointSquashingCoefficient,Matrix.mul_apply,
    QuantumProver.WernerEndpoint.Stinespring.referenceCoeff,Fintype.sum_prod_type,ite_mul]

theorem jointSquashingCoefficient_isometry {E : Type*}
    [Fintype E] [DecidableEq E] {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (S : CPTP CanonicalEnvironment E) : IsIsometry (jointSquashingCoefficient p S) := by
  unfold jointSquashingCoefficient IsIsometry
  rw [Matrix.conjTranspose_mul]
  calc
    _ = (canonicalIsometry p).conjTranspose *
        ((S.stinespring.referenceCoeff Qubit).conjTranspose *
          S.stinespring.referenceCoeff Qubit) * canonicalIsometry p := by
      simp only [Matrix.mul_assoc]
    _ = _ := by
      rw [S.stinespring.referenceCoeff_isometry,Matrix.mul_one,
        canonicalIsometry_isometry hp0 hp1]

theorem postSquashing_joint_extension {R E : Type*}
    [Fintype R] [Fintype E] [DecidableEq R] [DecidableEq E]
    (p : ℝ) (ψ : (R×Qubit) → ℂ) (S : CPTP CanonicalEnvironment E) :
    postSquashing p ψ S=
      partialTraceRight (pureDensity (physicalPureExtension
        (jointSquashingCoefficient p S*inputCoefficient ψ))) := by
  have hvec :
      (fun x : ((R×Qubit)×E)×(CanonicalEnvironment×E) =>
        (S.stinespring.withReference (R×Qubit)).amplitudes
          (extendedInputKet p ψ) x.1 x.2) =
      physicalPureExtension (jointSquashingCoefficient p S*inputCoefficient ψ) := by
    funext x
    rcases x with ⟨⟨⟨r,b⟩,e⟩,g⟩
    simp [physicalPureExtension,inputCoefficient,Matrix.mul_apply,jointSquashingCoefficient_apply,
      QuantumProver.WernerEndpoint.Stinespring.amplitudes,QuantumProver.WernerEndpoint.Stinespring.withReference,
      QuantumProver.WernerEndpoint.Stinespring.referenceCoeff,extendedInputKet,
      Fintype.sum_prod_type,ite_mul,Finset.sum_ite_irrel,
      Finset.mul_sum,Finset.sum_mul]
    simp only [mul_add,Finset.sum_add_distrib,mul_assoc]
  rw [postSquashing,S.amplify_pureDensity_eq_reduced,hvec]

theorem postSquashing_input_density {R E : Type*}
    [Fintype R] [Fintype E] [DecidableEq R] [DecidableEq E]
    (p : ℝ) (ψ : (R×Qubit) → ℂ) (S : CPTP CanonicalEnvironment E) :
    cmiNat (postSquashing p ψ S)=
      retainedCostNat
        (jointSquashingCoefficient p S*partialTraceLeft (pureDensity ψ)*
          (jointSquashingCoefficient p S).conjTranspose)
        (swapExtensionEG (jointSquashingCoefficient p S)*partialTraceLeft (pureDensity ψ)*
          (swapExtensionEG (jointSquashingCoefficient p S)).conjTranspose) := by
  rw [postSquashing_joint_extension,cmiNat_input_density]

theorem entropyNat_eq_matrixNats {I : Type*} [Fintype I] [DecidableEq I]
    {ρ : QMatrix I} (hρ : ρ.IsHermitian) :
    entropyNat ρ = QuantumProver.QuantumEntropy.entropyNats ρ := by
  rw [entropyNat, QuantumProver.QuantumEntropy.entropyNats,
    QuantumProver.ConditionalEntropy.ConditionalRange.trace_cfc_re_eq_sum _ hρ,
    QuantumProver.ConditionalEntropy.ConditionalRange.trace_cfc_re_eq_sum _ hρ]
  simp only [Real.negMulLog_eq_neg, Finset.sum_neg_distrib]

theorem entropyBits_eq_matrixBits {I : Type*} [Fintype I] [DecidableEq I]
    {ρ : QMatrix I} (hρ : ρ.IsHermitian) :
    entropyBits ρ = QuantumProver.QuantumEntropy.entropyBits ρ := by
  rw [entropyBits, entropyNat_eq_matrixNats hρ,
    QuantumProver.QuantumEntropy.entropyNats_eq_entropyBits_mul_log_two,
    mul_div_cancel_right₀ _ (ne_of_gt (Real.log_pos (by norm_num)))]

theorem entropyNat_reindex {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (e : I ≃ J)
    {ρ : QMatrix I} (hρ : ρ.IsHermitian) :
    entropyNat (Matrix.reindex e e ρ) = entropyNat ρ := by
  calc
    _ = QuantumProver.QuantumEntropy.entropyNats (Matrix.reindex e e ρ) :=
      entropyNat_eq_matrixNats (hρ.submatrix e.symm)
    _ = QuantumProver.QuantumEntropy.entropyNats ρ := by
      rw [QuantumProver.QuantumEntropy.entropyNats_eq_entropyBits_mul_log_two,
        QuantumProver.QuantumEntropy.entropyNats_eq_entropyBits_mul_log_two]
      exact congrArg (fun x : ℝ => x*Real.log 2)
        (QuantumProver.ConditionalEntropy.MixtureEntropy.entropyBits_reindex e hρ)
    _ = _ := (entropyNat_eq_matrixNats hρ).symm

theorem traceMiddle_positive {A B E : Type*}
    [Fintype A] [Fintype B] [Fintype E]
    {ρ : QMatrix ((A×B)×E)} (hρ : ρ.PosSemidef) :
    (traceMiddle ρ).PosSemidef := by
  let f : (A×E)×B → (A×B)×E := fun x => ((x.1.1,x.2),x.1.2)
  exact partialTraceRight_positive (hρ.submatrix f)

theorem traceFirst_positive {A B E : Type*}
    [Fintype A] [Fintype B] [Fintype E]
    {ρ : QMatrix ((A×B)×E)} (hρ : ρ.PosSemidef) :
    (traceFirst ρ).PosSemidef := by
  let f : (B×E)×A → (A×B)×E := fun x => ((x.2,x.1.1),x.1.2)
  exact partialTraceRight_positive (hρ.submatrix f)

def cmiRegisterEquiv (A B E : Type*) : ((A×B)×E) ≃ A×(E×B) where
  toFun := fun x => (x.1.1,(x.2,x.1.2))
  invFun := fun x => ((x.1,x.2.2),x.2.1)
  left_inv := by intro x; rfl
  right_inv := by intro x; rfl

theorem cmiNat_nonneg_of_positive {A B E : Type*}
    [Fintype A] [Fintype B] [Fintype E]
    [DecidableEq A] [DecidableEq B] [DecidableEq E]
    {ρ : QMatrix ((A×B)×E)} (hρ : ρ.PosSemidef) : 0 ≤ cmiNat ρ := by
  let e := cmiRegisterEquiv A B E
  let σ := Matrix.reindex e e ρ
  have hσ : σ.PosSemidef := hρ.submatrix e.symm
  have hAB : QuantumProver.QuantumEntropy.marginalAB σ = traceMiddle ρ := rfl
  have hBC : QuantumProver.QuantumEntropy.marginalBC σ =
      Matrix.reindex (Equiv.prodComm B E) (Equiv.prodComm B E) (traceFirst ρ) := rfl
  have hB : QuantumProver.QuantumEntropy.marginalB σ = partialTraceLeft ρ := by
    change partialTraceLeft (traceMiddle ρ) = partialTraceLeft ρ
    exact traceMiddle_environmental_margin ρ
  have htotal : QuantumProver.QuantumEntropy.entropyNats σ = entropyNat ρ := by
    rw [← entropyNat_eq_matrixNats hσ.1]
    exact entropyNat_reindex e hρ.1
  have hmiddle : QuantumProver.QuantumEntropy.entropyNats (QuantumProver.QuantumEntropy.marginalAB σ) =
      entropyNat (traceMiddle ρ) := by
    rw [hAB, ← entropyNat_eq_matrixNats (traceMiddle_positive hρ).1]
  have hfirst : QuantumProver.QuantumEntropy.entropyNats (QuantumProver.QuantumEntropy.marginalBC σ) =
      entropyNat (traceFirst ρ) := by
    rw [hBC]
    have hbridge := entropyNat_eq_matrixNats
      ((traceFirst_positive hρ).1.submatrix (Equiv.prodComm B E).symm)
    calc
      _ = entropyNat (Matrix.reindex (Equiv.prodComm B E) (Equiv.prodComm B E)
          (traceFirst ρ)) := hbridge.symm
      _ = _ := entropyNat_reindex (Equiv.prodComm B E) (traceFirst_positive hρ).1
  have henv : QuantumProver.QuantumEntropy.entropyNats (QuantumProver.QuantumEntropy.marginalB σ) =
      entropyNat (partialTraceLeft ρ) := by
    rw [hB, ← entropyNat_eq_matrixNats (partialTraceLeft_positive hρ).1]
  have hssa := QuantumProver.QuantumEntropy.strongSubadditivity_nats_of_posSemidef hσ
  rw [htotal,hmiddle,hfirst,henv] at hssa
  unfold cmiNat
  linarith only [hssa]

theorem cmiBits_nonneg_of_positive {A B E : Type*}
    [Fintype A] [Fintype B] [Fintype E]
    [DecidableEq A] [DecidableEq B] [DecidableEq E]
    {ρ : QMatrix ((A×B)×E)} (hρ : ρ.PosSemidef) : 0 ≤ cmiBits ρ :=
  div_nonneg (cmiNat_nonneg_of_positive hρ) (Real.log_nonneg (by norm_num))

theorem inputCosts_nonneg (p : ℝ) {r : ℕ} (ψ : (Fin r×Qubit) → ℂ)
    {x : ℝ} (hx : x ∈ inputCosts p ψ) : 0 ≤ x := by
  rcases hx with ⟨e,S,rfl⟩
  exact cmiBits_nonneg_of_positive (postSquashing_positive p ψ S)

theorem inputCosts_bddBelow (p : ℝ) {r : ℕ} (ψ : (Fin r×Qubit) → ℂ) :
    BddBelow (inputCosts p ψ) :=
  ⟨0, fun _ hx => inputCosts_nonneg p ψ hx⟩

theorem squashedInputValue_nonneg (p : ℝ) {r : ℕ} (ψ : (Fin r×Qubit) → ℂ) :
    0 ≤ squashedInputValue p ψ := by
  unfold squashedInputValue
  exact mul_nonneg (by norm_num) (le_csInf (inputCosts_nonempty p ψ)
    (fun _ hx => inputCosts_nonneg p ψ hx))

def conditionalNat {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (ρ : QMatrix (A×B)) : ℝ :=
  entropyNat ρ - entropyNat (partialTraceLeft ρ)

theorem conditionalNat_eq_matrix {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] {ρ : QMatrix (A×B)} (hρ : ρ.PosSemidef) :
    conditionalNat ρ = QuantumProver.ConditionalEntropy.conditionalEntropyBits ρ * Real.log 2 := by
  rw [conditionalNat, entropyNat_eq_matrixNats hρ.1,
    entropyNat_eq_matrixNats (partialTraceLeft_positive hρ).1,
    QuantumProver.QuantumEntropy.entropyNats_eq_entropyBits_mul_log_two,
    QuantumProver.QuantumEntropy.entropyNats_eq_entropyBits_mul_log_two]
  unfold QuantumProver.ConditionalEntropy.conditionalEntropyBits
  change QuantumProver.QuantumEntropy.entropyBits ρ * Real.log 2 -
      QuantumProver.QuantumEntropy.entropyBits (partialTraceLeft ρ) * Real.log 2 =
    (QuantumProver.QuantumEntropy.entropyBits ρ -
      QuantumProver.QuantumEntropy.entropyBits (partialTraceLeft ρ)) * Real.log 2
  ring

theorem conditionalNat_mix_lower {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] {ρ σ : QMatrix (A×B)}
    (hρ : QuantumProver.QuantumEntropy.IsDensity ρ) (hσ : QuantumProver.QuantumEntropy.IsDensity σ)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (1-t)*conditionalNat ρ+t*conditionalNat σ ≤
      conditionalNat (QuantumProver.ConditionalEntropy.mix t ρ σ) := by
  have hmix := QuantumProver.ConditionalEntropy.mix_isDensity hρ hσ ht0 ht1
  calc
    _ = ((1-t)*QuantumProver.ConditionalEntropy.conditionalEntropyBits ρ+
        t*QuantumProver.ConditionalEntropy.conditionalEntropyBits σ)*Real.log 2 := by
      rw [conditionalNat_eq_matrix hρ.1,conditionalNat_eq_matrix hσ.1]
      ring
    _ ≤ QuantumProver.ConditionalEntropy.conditionalEntropyBits
        (QuantumProver.ConditionalEntropy.mix t ρ σ)*Real.log 2 :=
      mul_le_mul_of_nonneg_right
        (QuantumProver.ConditionalEntropy.conditionalEntropy_mix_lower hρ hσ ht0 ht1)
        (Real.log_nonneg (by norm_num))
    _ = _ := (conditionalNat_eq_matrix hmix.1).symm

theorem isometry_output_isDensity {I O : Type*} [Fintype I] [Fintype O]
    [DecidableEq I] [DecidableEq O] (V : Matrix O I ℂ) (hV : IsIsometry V)
    {ρ : QMatrix I} (hρ : QuantumProver.QuantumEntropy.IsDensity ρ) :
    QuantumProver.QuantumEntropy.IsDensity (V*ρ*V.conjTranspose) := by
  refine ⟨hρ.1.mul_mul_conjTranspose_same V, ?_⟩
  rw [Matrix.trace_mul_cycle, hV, Matrix.one_mul, hρ.2]

theorem swapExtensionEG_gram {I B E G : Type*}
    [Fintype I] [Fintype B] [Fintype E] [Fintype G]
    (V : Matrix ((B×E)×G) I ℂ) :
    (swapExtensionEG V).conjTranspose*swapExtensionEG V=V.conjTranspose*V := by
  ext i j
  simp only [Matrix.mul_apply,Matrix.conjTranspose_apply,swapExtensionEG,
    Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro b _
  exact Finset.sum_comm

theorem swapExtensionEG_isometry {I B E G : Type*}
    [Fintype I] [Fintype B] [Fintype E] [Fintype G] [DecidableEq I]
    (V : Matrix ((B×E)×G) I ℂ) (hV : IsIsometry V) :
    IsIsometry (swapExtensionEG V) := by
  rw [IsIsometry,swapExtensionEG_gram]
  exact hV

def isometryCostNat {I B E G : Type*}
    [Fintype I] [Fintype B] [Fintype E] [Fintype G]
    [DecidableEq I] [DecidableEq B] [DecidableEq E] [DecidableEq G]
    (V : Matrix ((B×E)×G) I ℂ) (ρ : QMatrix I) : ℝ :=
  retainedCostNat (V*ρ*V.conjTranspose)
    (swapExtensionEG V*ρ*(swapExtensionEG V).conjTranspose)

theorem compression_mix {I O : Type*} [Fintype I]
    (V : Matrix O I ℂ) (t : ℝ) (ρ σ : QMatrix I) :
    V*QuantumProver.ConditionalEntropy.mix t ρ σ*V.conjTranspose =
      QuantumProver.ConditionalEntropy.mix t (V*ρ*V.conjTranspose) (V*σ*V.conjTranspose) := by
  simp [QuantumProver.ConditionalEntropy.mix,Matrix.mul_add,Matrix.add_mul,
    Matrix.mul_smul,Matrix.smul_mul]

theorem isometryCostNat_mix_lower {I B E G : Type*}
    [Fintype I] [Fintype B] [Fintype E] [Fintype G]
    [DecidableEq I] [DecidableEq B] [DecidableEq E] [DecidableEq G]
    (V : Matrix ((B×E)×G) I ℂ) (hV : IsIsometry V)
    {ρ σ : QMatrix I} (hρ : QuantumProver.QuantumEntropy.IsDensity ρ)
    (hσ : QuantumProver.QuantumEntropy.IsDensity σ) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (1-t)*isometryCostNat V ρ+t*isometryCostNat V σ ≤
      isometryCostNat V (QuantumProver.ConditionalEntropy.mix t ρ σ) := by
  have hR := isometry_output_isDensity V hV hρ
  have hS := isometry_output_isDensity V hV hσ
  have hVR := isometry_output_isDensity (swapExtensionEG V)
    (swapExtensionEG_isometry V hV) hρ
  have hVS := isometry_output_isDensity (swapExtensionEG V)
    (swapExtensionEG_isometry V hV) hσ
  have hE := conditionalNat_mix_lower
    (QuantumProver.QuantumEntropy.partialTraceRight_isDensity hR)
    (QuantumProver.QuantumEntropy.partialTraceRight_isDensity hS) ht0 ht1
  have hG := conditionalNat_mix_lower
    (QuantumProver.QuantumEntropy.partialTraceRight_isDensity hVR)
    (QuantumProver.QuantumEntropy.partialTraceRight_isDensity hVS) ht0 ht1
  have hEM : partialTraceRight (V*QuantumProver.ConditionalEntropy.mix t ρ σ*V.conjTranspose)=
      QuantumProver.ConditionalEntropy.mix t (partialTraceRight (V*ρ*V.conjTranspose))
        (partialTraceRight (V*σ*V.conjTranspose)) := by
    rw [compression_mix]
    ext x y
    simp [partialTraceRight,QuantumProver.WernerEndpoint.partialTraceLeft,
      QuantumProver.ConditionalEntropy.mix,Finset.sum_add_distrib,Finset.smul_sum]
  have hGM : partialTraceRight (swapExtensionEG V*
      QuantumProver.ConditionalEntropy.mix t ρ σ*(swapExtensionEG V).conjTranspose)=
      QuantumProver.ConditionalEntropy.mix t
        (partialTraceRight (swapExtensionEG V*ρ*(swapExtensionEG V).conjTranspose))
        (partialTraceRight (swapExtensionEG V*σ*(swapExtensionEG V).conjTranspose)) := by
    rw [compression_mix]
    ext x y
    simp [partialTraceRight,QuantumProver.WernerEndpoint.partialTraceLeft,
      QuantumProver.ConditionalEntropy.mix,Finset.sum_add_distrib,Finset.smul_sum]
  change (1-t)*(conditionalNat (partialTraceRight (V*ρ*V.conjTranspose))+
    conditionalNat (partialTraceRight (swapExtensionEG V*ρ*(swapExtensionEG V).conjTranspose)))+
    t*(conditionalNat (partialTraceRight (V*σ*V.conjTranspose))+
    conditionalNat (partialTraceRight (swapExtensionEG V*σ*(swapExtensionEG V).conjTranspose))) ≤
      conditionalNat (partialTraceRight (V*QuantumProver.ConditionalEntropy.mix t ρ σ*V.conjTranspose))+
      conditionalNat (partialTraceRight (swapExtensionEG V*
        QuantumProver.ConditionalEntropy.mix t ρ σ*(swapExtensionEG V).conjTranspose))
  rw [hEM,hGM]
  change (1-t)*conditionalNat (partialTraceRight (V*ρ*V.conjTranspose))+
    t*conditionalNat (partialTraceRight (V*σ*V.conjTranspose)) ≤
      conditionalNat (QuantumProver.ConditionalEntropy.mix t
        (partialTraceRight (V*ρ*V.conjTranspose))
        (partialTraceRight (V*σ*V.conjTranspose))) at hE
  change (1-t)*conditionalNat (partialTraceRight
      (swapExtensionEG V*ρ*(swapExtensionEG V).conjTranspose))+
    t*conditionalNat (partialTraceRight (swapExtensionEG V*σ*(swapExtensionEG V).conjTranspose)) ≤
      conditionalNat (QuantumProver.ConditionalEntropy.mix t
        (partialTraceRight (swapExtensionEG V*ρ*(swapExtensionEG V).conjTranspose))
        (partialTraceRight (swapExtensionEG V*σ*(swapExtensionEG V).conjTranspose))) at hG
  linarith only [hE,hG]

theorem conditionalNat_upper {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] {ρ : QMatrix (A×B)}
    (hρ : QuantumProver.QuantumEntropy.IsDensity ρ) :
    conditionalNat ρ ≤ Real.log (Fintype.card A) := by
  calc
    _ = QuantumProver.ConditionalEntropy.conditionalEntropyBits ρ*Real.log 2 :=
      conditionalNat_eq_matrix hρ.1
    _ ≤ QuantumProver.ConditionalEntropy.logDimA A*Real.log 2 :=
      mul_le_mul_of_nonneg_right (QuantumProver.ConditionalEntropy.conditionalEntropy_bounds hρ).2
        (Real.log_nonneg (by norm_num))
    _ = _ := by
      rw [QuantumProver.ConditionalEntropy.logDimA,div_mul_cancel₀ _
        (ne_of_gt (Real.log_pos (by norm_num)))]

theorem isometryCostNat_upper {I B E G : Type*}
    [Fintype I] [Fintype B] [Fintype E] [Fintype G]
    [DecidableEq I] [DecidableEq B] [DecidableEq E] [DecidableEq G]
    (V : Matrix ((B×E)×G) I ℂ) (hV : IsIsometry V)
    {ρ : QMatrix I} (hρ : QuantumProver.QuantumEntropy.IsDensity ρ) :
    isometryCostNat V ρ ≤ 2*Real.log (Fintype.card B) := by
  have hE := conditionalNat_upper (QuantumProver.QuantumEntropy.partialTraceRight_isDensity
    (isometry_output_isDensity V hV hρ))
  have hG := conditionalNat_upper (QuantumProver.QuantumEntropy.partialTraceRight_isDensity
    (isometry_output_isDensity (swapExtensionEG V) (swapExtensionEG_isometry V hV) hρ))
  change conditionalNat (partialTraceRight (V*ρ*V.conjTranspose))+
      conditionalNat (partialTraceRight
        (swapExtensionEG V*ρ*(swapExtensionEG V).conjTranspose)) ≤ _
  change conditionalNat (partialTraceRight (V*ρ*V.conjTranspose)) ≤
    Real.log (Fintype.card B) at hE
  change conditionalNat (partialTraceRight (swapExtensionEG V*ρ*(swapExtensionEG V).conjTranspose)) ≤
    Real.log (Fintype.card B) at hG
  linarith only [hE,hG]

theorem pureInputDensity_isDensity {R I : Type*} [Fintype R] [Fintype I]
    [DecidableEq R] [DecidableEq I] (ψ : (R×I) → ℂ) (hψ : IsNormalized ψ) :
    QuantumProver.QuantumEntropy.IsDensity (partialTraceLeft (pureDensity ψ)) := by
  refine ⟨partialTraceLeft_positive (pureDensity_positive ψ), ?_⟩
  rw [partialTraceLeft_trace,pureDensity_trace,show vectorNormSq ψ=1 from hψ]
  norm_num

theorem postSquashing_halfCost_le_one {R E : Type*}
    [Fintype R] [Fintype E] [DecidableEq R] [DecidableEq E]
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (ψ : (R×Qubit) → ℂ)
    (hψ : IsNormalized ψ) (S : CPTP CanonicalEnvironment E) :
    cmiBits (postSquashing p ψ S)/2 ≤ 1 := by
  have h := isometryCostNat_upper (jointSquashingCoefficient p S)
    (jointSquashingCoefficient_isometry hp0 hp1 S) (pureInputDensity_isDensity ψ hψ)
  have heq : cmiNat (postSquashing p ψ S)=
      isometryCostNat (jointSquashingCoefficient p S)
        (partialTraceLeft (pureDensity ψ)) := postSquashing_input_density p ψ S
  rw [← heq] at h
  norm_num only [Fintype.card_fin] at h
  unfold cmiBits
  rw [div_div]
  apply (div_le_iff₀ (mul_pos (Real.log_pos (by norm_num)) (by norm_num))).2
  nlinarith only [h]

theorem channelInputValues_bddAbove {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    BddAbove (channelInputValues p) := by
  refine ⟨1, ?_⟩
  intro x hx
  rcases hx with ⟨r,ψ,hψ,rfl⟩
  have h := squashedInputValue_le_cost p ψ (inputCosts_bddBelow p ψ)
    (CPTP.identity CanonicalEnvironment)
  have hb := postSquashing_halfCost_le_one hp0 hp1 ψ hψ
    (CPTP.identity CanonicalEnvironment)
  have hcost : (1/2 : ℝ)*cmiBits
      (postSquashing p ψ (CPTP.identity CanonicalEnvironment)) ≤ 1 := by
    simpa only [div_eq_mul_inv,mul_comm,one_mul] using hb
  exact h.trans hcost

theorem channelSquashed_le_one {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    channelSquashed p ≤ 1 := by
  apply channelSquashed_le_of_fixed_squashing p (CPTP.identity CanonicalEnvironment) 1
    (fun _ ψ _ => inputCosts_bddBelow p ψ)
  intro r ψ hψ
  simpa only [div_eq_mul_inv,mul_comm,one_mul] using
    postSquashing_halfCost_le_one hp0 hp1 ψ hψ (CPTP.identity CanonicalEnvironment)

theorem channelSquashed_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    0 ≤ channelSquashed p := by
  rcases channelInputValues_nonempty p with ⟨x,hx⟩
  have hx0 : 0 ≤ x := by
    rcases hx with ⟨r,ψ,hψ,rfl⟩
    exact squashedInputValue_nonneg p ψ
  exact hx0.trans (le_csSup (channelInputValues_bddAbove hp0 hp1) hx)

theorem isometryCostNat_concaveOn {I B E G : Type*}
    [Fintype I] [Fintype B] [Fintype E] [Fintype G]
    [DecidableEq I] [DecidableEq B] [DecidableEq E] [DecidableEq G]
    (V : Matrix ((B×E)×G) I ℂ) (hV : IsIsometry V) :
    ConcaveOn ℝ {ρ : QMatrix I | QuantumProver.QuantumEntropy.IsDensity ρ} (isometryCostNat V) := by
  refine ⟨QuantumProver.ConditionalEntropy.convex_isDensity, ?_⟩
  intro ρ hρ σ hσ a b ha hb hab
  have h := isometryCostNat_mix_lower V hV hρ hσ hb (by linarith only [ha,hab])
  have hab' : 1-b=a := by linarith only [hab]
  simpa only [QuantumProver.ConditionalEntropy.mix,hab',smul_eq_mul] using h

theorem pauliAverage_eq_halfIdentity (ρ : QMatrix Qubit) (hρ : Matrix.trace ρ=1) :
    (∑ k : CanonicalEnvironment,(1/4 : ℝ) • (pauli k*ρ*(pauli k).conjTranspose))=
      (1/2 : ℂ) • (1 : QMatrix Qubit) := by
  have hw (k : CanonicalEnvironment) : pauliWeight 1 k=1/4 := by
    fin_cases k <;> norm_num [pauliWeight]
  have h := weightedPauli_eq_depolarizing 1 ρ
  simp_rw [hw] at h
  simpa [depolarizing,hρ] using h

theorem isometryCostNat_le_halfIdentity_of_pauliInvariant {B E G : Type*}
    [Fintype B] [Fintype E] [Fintype G]
    [DecidableEq B] [DecidableEq E] [DecidableEq G]
    (V : Matrix ((B×E)×G) Qubit ℂ) (hV : IsIsometry V)
    (hInvariant : ∀ (k : CanonicalEnvironment) (σ : QMatrix Qubit),
      QuantumProver.QuantumEntropy.IsDensity σ →
      isometryCostNat V (pauli k*σ*(pauli k).conjTranspose)=isometryCostNat V σ)
    {ρ : QMatrix Qubit} (hρ : QuantumProver.QuantumEntropy.IsDensity ρ) :
    isometryCostNat V ρ ≤ isometryCostNat V ((1/2 : ℂ) • (1 : QMatrix Qubit)) := by
  have hpoint (k : CanonicalEnvironment) (_ : k ∈ (Finset.univ : Finset CanonicalEnvironment)) :
      pauli k*ρ*(pauli k).conjTranspose ∈
        {σ : QMatrix Qubit | QuantumProver.QuantumEntropy.IsDensity σ} :=
    isometry_output_isDensity (pauli k) (pauli_unitary k) hρ
  have hw : ∑ k : CanonicalEnvironment, (1/4 : ℝ)=1 := by norm_num
  have h := (isometryCostNat_concaveOn V hV).le_map_sum
    (t := Finset.univ) (w := fun _ : CanonicalEnvironment => (1/4 : ℝ))
    (p := fun k => pauli k*ρ*(pauli k).conjTranspose)
    (by intro k hk; norm_num) hw hpoint
  have hleft : (∑ k : CanonicalEnvironment,
      (1/4 : ℝ) • isometryCostNat V (pauli k*ρ*(pauli k).conjTranspose))=
        isometryCostNat V ρ := by
    simp_rw [hInvariant _ ρ hρ]
    norm_num [smul_eq_mul] <;> ring
  rw [hleft,pauliAverage_eq_halfIdentity ρ hρ.2] at h
  exact h

theorem pureInput_cmiNat_le_halfIdentity_of_pauliInvariant {R B E G : Type*}
    [Fintype R] [Fintype B] [Fintype E] [Fintype G]
    [DecidableEq R] [DecidableEq B] [DecidableEq E] [DecidableEq G]
    (V : Matrix ((B×E)×G) Qubit ℂ) (hV : IsIsometry V)
    (hInvariant : ∀ (k : CanonicalEnvironment) (σ : QMatrix Qubit),
      QuantumProver.QuantumEntropy.IsDensity σ →
      isometryCostNat V (pauli k*σ*(pauli k).conjTranspose)=isometryCostNat V σ)
    (ψ : (R×Qubit) → ℂ) (hψ : IsNormalized ψ) :
    cmiNat (partialTraceRight
      (pureDensity (physicalPureExtension (V*inputCoefficient ψ)))) ≤
        isometryCostNat V ((1/2 : ℂ) • (1 : QMatrix Qubit)) := by
  rw [cmiNat_input_density]
  exact isometryCostNat_le_halfIdentity_of_pauliInvariant V hV hInvariant
    (pureInputDensity_isDensity ψ hψ)

theorem conditionalNat_localUnitary {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (U : QMatrix A) (W : QMatrix B) (hU : IsIsometry U) (hW : IsIsometry W)
    {ρ : QMatrix (A×B)} (hρ : ρ.PosSemidef) :
    conditionalNat ((U ⊗ₖ W)*ρ*(U ⊗ₖ W).conjTranspose)=conditionalNat ρ := by
  rw [conditionalNat,partialTraceLeft_localUnitary U W hU,
    entropyNat_isometric_embedding (U ⊗ₖ W) (isometry_kronecker hU hW) hρ.1,
    entropyNat_isometric_embedding W hW (partialTraceLeft_positive hρ).1]
  rfl

theorem compression_of_intertwining {I O : Type*} [Fintype I] [Fintype O]
    (V : Matrix O I ℂ) (P : QMatrix I) (K : QMatrix O)
    (hcov : V*P=K*V) (ρ : QMatrix I) :
    V*(P*ρ*P.conjTranspose)*V.conjTranspose=
      K*(V*ρ*V.conjTranspose)*K.conjTranspose := by
  calc
    _ = (V*P)*ρ*(V*P).conjTranspose := by
      simp only [Matrix.conjTranspose_mul,Matrix.mul_assoc]
    _ = (K*V)*ρ*(K*V).conjTranspose := by rw [hcov]
    _ = _ := by simp only [Matrix.conjTranspose_mul,Matrix.mul_assoc]

theorem swapExtensionEG_mul {I J B E G : Type*} [Fintype I]
    (V : Matrix ((B×E)×G) I ℂ) (P : Matrix I J ℂ) :
    swapExtensionEG (V*P)=swapExtensionEG V*P := by
  ext x j
  rfl

theorem swapExtensionEG_localUnitary {I B E G : Type*}
    [Fintype B] [Fintype E] [Fintype G]
    (UB : QMatrix B) (UE : QMatrix E) (UG : QMatrix G)
    (V : Matrix ((B×E)×G) I ℂ) :
    swapExtensionEG (((UB ⊗ₖ UE) ⊗ₖ UG)*V)=
      ((UB ⊗ₖ UG) ⊗ₖ UE)*swapExtensionEG V := by
  ext ⟨⟨b,g⟩,e⟩ i
  simp only [swapExtensionEG,Matrix.mul_apply,Matrix.kronecker_apply,
    Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro c hc
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro h hh
  apply Finset.sum_congr rfl
  intro f hf
  ring

theorem isometryCostNat_localCovariance {I B E G : Type*}
    [Fintype I] [Fintype B] [Fintype E] [Fintype G]
    [DecidableEq I] [DecidableEq B] [DecidableEq E] [DecidableEq G]
    (V : Matrix ((B×E)×G) I ℂ) (P : QMatrix I)
    (UB : QMatrix B) (UE : QMatrix E) (UG : QMatrix G)
    (hB : IsIsometry UB) (hE : IsIsometry UE) (hG : IsIsometry UG)
    (hcov : V*P=((UB ⊗ₖ UE) ⊗ₖ UG)*V)
    {ρ : QMatrix I} (hρ : ρ.PosSemidef) :
    isometryCostNat V (P*ρ*P.conjTranspose)=isometryCostNat V ρ := by
  have hswap : swapExtensionEG V*P=
      ((UB ⊗ₖ UG) ⊗ₖ UE)*swapExtensionEG V := by
    rw [← swapExtensionEG_mul,hcov,swapExtensionEG_localUnitary]
  have he := hρ.mul_mul_conjTranspose_same V
  have hg := hρ.mul_mul_conjTranspose_same (swapExtensionEG V)
  unfold isometryCostNat retainedCostNat
  change conditionalNat
      (partialTraceRight (V*(P*ρ*P.conjTranspose)*V.conjTranspose))+
    conditionalNat (partialTraceRight
      (swapExtensionEG V*(P*ρ*P.conjTranspose)*(swapExtensionEG V).conjTranspose))=
    conditionalNat (partialTraceRight (V*ρ*V.conjTranspose))+
    conditionalNat (partialTraceRight
      (swapExtensionEG V*ρ*(swapExtensionEG V).conjTranspose))
  rw [compression_of_intertwining V P _ hcov,
    compression_of_intertwining (swapExtensionEG V) P _ hswap,
    partialTraceRight_localUnitary (UB ⊗ₖ UE) UG hG,
    partialTraceRight_localUnitary (UB ⊗ₖ UG) UE hE,
    conditionalNat_localUnitary UB UE hB hE (partialTraceRight_positive he),
    conditionalNat_localUnitary UB UG hB hG (partialTraceRight_positive hg)]

theorem isometryCostNat_le_halfIdentity_of_localCovariance {B E G : Type*}
    [Fintype B] [Fintype E] [Fintype G]
    [DecidableEq B] [DecidableEq E] [DecidableEq G]
    (V : Matrix ((B×E)×G) Qubit ℂ) (hV : IsIsometry V)
    (UB : CanonicalEnvironment → QMatrix B)
    (UE : CanonicalEnvironment → QMatrix E)
    (UG : CanonicalEnvironment → QMatrix G)
    (hB : ∀ k,IsIsometry (UB k)) (hE : ∀ k,IsIsometry (UE k))
    (hG : ∀ k,IsIsometry (UG k))
    (hcov : ∀ k,V*pauli k=((UB k ⊗ₖ UE k) ⊗ₖ UG k)*V)
    {ρ : QMatrix Qubit} (hρ : QuantumProver.QuantumEntropy.IsDensity ρ) :
    isometryCostNat V ρ ≤ isometryCostNat V ((1/2 : ℂ) • (1 : QMatrix Qubit)) := by
  apply isometryCostNat_le_halfIdentity_of_pauliInvariant V hV _ hρ
  intro k σ hσ
  exact isometryCostNat_localCovariance V (pauli k) (UB k) (UE k) (UG k)
    (hB k) (hE k) (hG k) (hcov k) hσ.1

def chosenJointCoefficient {E G : Type*} [Fintype E] [Fintype G]
    (p : ℝ) (N : QuantumProver.WernerEndpoint.Stinespring CanonicalEnvironment E G) :
    Matrix ((Qubit×E)×G) Qubit ℂ := N.referenceCoeff Qubit*canonicalIsometry p

theorem chosenJointCoefficient_apply {E G : Type*} [Fintype E] [Fintype G]
    (p : ℝ) (N : QuantumProver.WernerEndpoint.Stinespring CanonicalEnvironment E G)
    (b : Qubit) (e : E) (g : G) (i : Qubit) :
    chosenJointCoefficient p N ((b,e),g) i=
      ∑ j,N.coeff (e,g) j*canonicalIsometry p (b,j) i := by
  simp [chosenJointCoefficient,Matrix.mul_apply,
    QuantumProver.WernerEndpoint.Stinespring.referenceCoeff,Fintype.sum_prod_type,ite_mul]

theorem chosenJointCoefficient_isometry {E G : Type*}
    [Fintype E] [Fintype G] [DecidableEq E] [DecidableEq G]
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (N : QuantumProver.WernerEndpoint.Stinespring CanonicalEnvironment E G) :
    IsIsometry (chosenJointCoefficient p N) := by
  unfold chosenJointCoefficient IsIsometry
  rw [Matrix.conjTranspose_mul]
  calc
    _ = (canonicalIsometry p).conjTranspose*
        ((N.referenceCoeff Qubit).conjTranspose*N.referenceCoeff Qubit)*canonicalIsometry p := by
      simp only [Matrix.mul_assoc]
    _ = _ := by rw [N.referenceCoeff_isometry,Matrix.mul_one,
      canonicalIsometry_isometry hp0 hp1]

theorem postSquashing_chosen_joint_extension {R E G : Type*}
    [Fintype R] [Fintype E] [Fintype G]
    [DecidableEq R] [DecidableEq E] [DecidableEq G]
    (p : ℝ) (ψ : (R×Qubit) → ℂ) (S : CPTP CanonicalEnvironment E)
    (N : QuantumProver.WernerEndpoint.Stinespring CanonicalEnvironment E G)
    (hN : ∀ ρ : QMatrix CanonicalEnvironment,N.apply ρ=S.map ρ) :
    postSquashing p ψ S=partialTraceRight (pureDensity
      (physicalPureExtension (chosenJointCoefficient p N*inputCoefficient ψ))) := by
  have hvec :
      (fun x : ((R×Qubit)×E)×G => (N.withReference (R×Qubit)).amplitudes
        (extendedInputKet p ψ) x.1 x.2)=
      physicalPureExtension (chosenJointCoefficient p N*inputCoefficient ψ) := by
    funext x
    rcases x with ⟨⟨⟨r,b⟩,e⟩,g⟩
    simp [physicalPureExtension,inputCoefficient,Matrix.mul_apply,chosenJointCoefficient_apply,
      QuantumProver.WernerEndpoint.Stinespring.amplitudes,QuantumProver.WernerEndpoint.Stinespring.withReference,
      QuantumProver.WernerEndpoint.Stinespring.referenceCoeff,extendedInputKet,
      Fintype.sum_prod_type,ite_mul,Finset.sum_ite_irrel,Finset.mul_sum,Finset.sum_mul]
    simp only [mul_add,Finset.sum_add_distrib,mul_assoc]
  rw [postSquashing,S.amplify_pureDensity_eq_chosen_stinespring N hN,hvec]

theorem postSquashing_chosen_input_density {R E G : Type*}
    [Fintype R] [Fintype E] [Fintype G]
    [DecidableEq R] [DecidableEq E] [DecidableEq G]
    (p : ℝ) (ψ : (R×Qubit) → ℂ) (S : CPTP CanonicalEnvironment E)
    (N : QuantumProver.WernerEndpoint.Stinespring CanonicalEnvironment E G)
    (hN : ∀ ρ : QMatrix CanonicalEnvironment,N.apply ρ=S.map ρ) :
    cmiNat (postSquashing p ψ S)=
      isometryCostNat (chosenJointCoefficient p N) (partialTraceLeft (pureDensity ψ)) := by
  rw [postSquashing_chosen_joint_extension p ψ S N hN,cmiNat_input_density]
  rfl

theorem referenceCoeff_intertwining {I B E G : Type*}
    [Fintype I] [Fintype B] [Fintype E] [Fintype G]
    [DecidableEq I] [DecidableEq B]
    (N : QuantumProver.WernerEndpoint.Stinespring I E G) (U : QMatrix B) (D : QMatrix I)
    (UE : QMatrix E) (UG : QMatrix G)
    (hcov : N.coeff*D=(UE ⊗ₖ UG)*N.coeff) :
    N.referenceCoeff B*(U ⊗ₖ D)=((U ⊗ₖ UE) ⊗ₖ UG)*N.referenceCoeff B := by
  ext ⟨⟨b,e⟩,g⟩ ⟨c,j⟩
  calc
    _ = U b c*(N.coeff*D) (e,g) j := by
      simp [QuantumProver.WernerEndpoint.Stinespring.referenceCoeff,Matrix.mul_apply,
        Matrix.kronecker_apply,Fintype.sum_prod_type,ite_mul,mul_ite,
        Finset.mul_sum,Finset.sum_mul,mul_assoc,mul_left_comm,mul_comm]
    _ = U b c*((UE ⊗ₖ UG)*N.coeff) (e,g) j := by rw [hcov]
    _ = _ := by
      simp [QuantumProver.WernerEndpoint.Stinespring.referenceCoeff,Matrix.mul_apply,
        Matrix.kronecker_apply,Fintype.sum_prod_type,ite_mul,mul_ite,
        Finset.mul_sum,Finset.sum_mul,mul_assoc,mul_left_comm,mul_comm]

theorem chosenJointCoefficient_covariance {E G : Type*}
    [Fintype E] [Fintype G] (p : ℝ)
    (N : QuantumProver.WernerEndpoint.Stinespring CanonicalEnvironment E G)
    (k : CanonicalEnvironment) (UE : QMatrix E) (UG : QMatrix G)
    (hcov : N.coeff*pauliEnvironmentUnitary k=(UE ⊗ₖ UG)*N.coeff) :
    chosenJointCoefficient p N*pauli k=
      ((pauli k ⊗ₖ UE) ⊗ₖ UG)*chosenJointCoefficient p N := by
  unfold chosenJointCoefficient
  rw [Matrix.mul_assoc,canonicalIsometry_pauli_equivariance,
    ← Matrix.mul_assoc,referenceCoeff_intertwining N (pauli k)
      (pauliEnvironmentUnitary k) UE UG hcov]
  simp only [Matrix.mul_assoc]

theorem bellDensity_partialTraceLeft :
    partialTraceLeft (pureDensity bellKet)=(1/2 : ℂ) • (1 : QMatrix Qubit) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [partialTraceLeft,QuantumProver.WernerEndpoint.partialTraceRight,pureDensity,
      QuantumProver.WernerEndpoint.pureDensity,QuantumProver.WernerEndpoint.crossDensity,bellKet,
      Fin.sum_univ_succ,Matrix.smul_apply,Matrix.one_apply,
      ← Complex.ofReal_mul,← pow_two,splitterScale_sq,splitterScale_complex_sq]

theorem postSquashing_cmiNat_le_bell_of_chosenCovariance {R E G : Type*}
    [Fintype R] [Fintype E] [Fintype G]
    [DecidableEq R] [DecidableEq E] [DecidableEq G]
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (S : CPTP CanonicalEnvironment E)
    (N : QuantumProver.WernerEndpoint.Stinespring CanonicalEnvironment E G)
    (hN : ∀ ρ : QMatrix CanonicalEnvironment,N.apply ρ=S.map ρ)
    (UE : CanonicalEnvironment → QMatrix E) (UG : CanonicalEnvironment → QMatrix G)
    (hE : ∀ k,IsIsometry (UE k)) (hG : ∀ k,IsIsometry (UG k))
    (hcov : ∀ k,chosenJointCoefficient p N*pauli k=
      ((pauli k ⊗ₖ UE k) ⊗ₖ UG k)*chosenJointCoefficient p N)
    (ψ : (R×Qubit) → ℂ) (hψ : IsNormalized ψ) :
    cmiNat (postSquashing p ψ S) ≤ cmiNat (postSquashing p bellKet S) := by
  rw [postSquashing_chosen_input_density p ψ S N hN,
    postSquashing_chosen_input_density p bellKet S N hN,bellDensity_partialTraceLeft]
  exact isometryCostNat_le_halfIdentity_of_localCovariance
    (chosenJointCoefficient p N) (chosenJointCoefficient_isometry hp0 hp1 N)
    pauli UE UG pauli_unitary hE hG hcov (pureInputDensity_isDensity ψ hψ)

theorem channelSquashed_le_bell_of_chosenCovariance {e : ℕ} {G : Type*}
    [Fintype G] [DecidableEq G] {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (S : CPTP CanonicalEnvironment (Fin e))
    (N : QuantumProver.WernerEndpoint.Stinespring CanonicalEnvironment (Fin e) G)
    (hN : ∀ ρ : QMatrix CanonicalEnvironment,N.apply ρ=S.map ρ)
    (UE : CanonicalEnvironment → QMatrix (Fin e))
    (UG : CanonicalEnvironment → QMatrix G)
    (hE : ∀ k,IsIsometry (UE k)) (hG : ∀ k,IsIsometry (UG k))
    (hcov : ∀ k,chosenJointCoefficient p N*pauli k=
      ((pauli k ⊗ₖ UE k) ⊗ₖ UG k)*chosenJointCoefficient p N) :
    channelSquashed p ≤ (1/2 : ℝ)*cmiBits (postSquashing p bellKet S) := by
  apply channelSquashed_le_of_fixed_squashing p S _
    (fun r ψ hψ => inputCosts_bddBelow p ψ)
  intro r ψ hψ
  have h := postSquashing_cmiNat_le_bell_of_chosenCovariance hp0 hp1
    S N hN UE UG hE hG hcov ψ hψ
  exact mul_le_mul_of_nonneg_left
    (div_le_div_of_nonneg_right h (Real.log_nonneg (by norm_num))) (by norm_num)

theorem splitterCoefficient_pauli_sign (k e g j : CanonicalEnvironment) :
    splitterCoefficient (e,g) j*(pauliSign k j : ℂ)=
      (pauliSign k e : ℂ)*(pauliSign k g : ℂ)*splitterCoefficient (e,g) j := by
  by_cases hj : j=0
  · subst j
    by_cases hx : (e,g)=(0,0)
    · have he : e=0 := congrArg Prod.fst hx
      have hg : g=0 := congrArg Prod.snd hx
      subst e
      subst g
      simp [splitterCoefficient,pauliSign]
    · simp [splitterCoefficient,hx,pauliSign]
  · by_cases h10 : (e,g)=(j,0)
    · have he : e=j := congrArg Prod.fst h10
      have hg : g=0 := congrArg Prod.snd h10
      subst e
      subst g
      simp [splitterCoefficient,hj,pauliSign,mul_assoc,mul_left_comm,mul_comm]
    · by_cases h01 : (e,g)=(0,j)
      · have he : e=0 := congrArg Prod.fst h01
        have hg : g=j := congrArg Prod.snd h01
        subst e
        subst g
        simp [splitterCoefficient,hj,pauliSign,mul_assoc,mul_left_comm,mul_comm]
      · simp [splitterCoefficient,hj,h10,h01]

theorem splitterCoefficient_pauli_equivariance (k : CanonicalEnvironment) :
    splitterCoefficient*pauliEnvironmentUnitary k=
      (pauliEnvironmentUnitary k ⊗ₖ pauliEnvironmentUnitary k)*splitterCoefficient := by
  ext ⟨e,g⟩ j
  simpa [pauliEnvironmentUnitary,Matrix.mul_apply,Matrix.kronecker_apply,
    Matrix.diagonal_apply,Fintype.sum_prod_type,ite_mul,mul_ite,mul_assoc] using
      splitterCoefficient_pauli_sign k e g j

theorem splitterJointCoefficient_pauli_covariance (p : ℝ) (k : CanonicalEnvironment) :
    chosenJointCoefficient p splitterStinespring*pauli k=
      ((pauli k ⊗ₖ pauliEnvironmentUnitary k) ⊗ₖ pauliEnvironmentUnitary k)*
        chosenJointCoefficient p splitterStinespring := by
  exact chosenJointCoefficient_covariance p splitterStinespring k _ _
    (splitterCoefficient_pauli_equivariance k)

theorem postSquashing_splitter_cmiNat_le_bell {R : Type*}
    [Fintype R] [DecidableEq R] {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (ψ : (R×Qubit) → ℂ) (hψ : IsNormalized ψ) :
    cmiNat (postSquashing p ψ splitterSquashing) ≤
      cmiNat (postSquashing p bellKet splitterSquashing) := by
  exact postSquashing_cmiNat_le_bell_of_chosenCovariance hp0 hp1
    splitterSquashing splitterStinespring splitterStinespring_apply
    pauliEnvironmentUnitary pauliEnvironmentUnitary
    pauliEnvironmentUnitary_isometry pauliEnvironmentUnitary_isometry
    (splitterJointCoefficient_pauli_covariance p) ψ hψ

theorem channelSquashed_le_splitter_bell {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    channelSquashed p ≤ (1/2 : ℝ)*cmiBits (postSquashing p bellKet splitterSquashing) := by
  exact channelSquashed_le_bell_of_chosenCovariance hp0 hp1
    splitterSquashing splitterStinespring splitterStinespring_apply
    pauliEnvironmentUnitary pauliEnvironmentUnitary
    pauliEnvironmentUnitary_isometry pauliEnvironmentUnitary_isometry
    (splitterJointCoefficient_pauli_covariance p)

theorem channelSquashed_le_splitterScalarBellCost {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : channelSquashed p ≤ splitterScalarBellCost p := by
  calc
    _ ≤ cmiBits (postSquashing p bellKet splitterSquashing)/2 := by
      simpa only [div_eq_mul_inv,mul_comm,one_mul] using
        channelSquashed_le_splitter_bell hp0 hp1
    _ = _ := splitterBellCost hp0 hp1

theorem channelSquashed_lowNoise_upper {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1/2) :
    channelSquashed p ≤ lowNoiseProfile p+(3*p/8)*(8+Real.log 8)/Real.log 2 := by
  have hs := channelSquashed_le_splitterScalarBellCost hp0.le (by linarith only [hp1])
  have hr := (abs_le.mp (splitterScalarBellCost_lowNoise hp0 hp1)).2
  linarith only [hs,hr]

def pureChoiCoefficient {A B E G : Type*}
    (Ω : (((A×B)×E)×G) → ℂ) : Matrix ((B×E)×G) A ℂ :=
  fun x a => Ω (((a,x.1.1),x.1.2),x.2)

def pureChoiIsometry {B E G : Type*}
    (Ω : (((Qubit×B)×E)×G) → ℂ) : Matrix ((B×E)×G) Qubit ℂ :=
  ((splitterScale : ℂ)⁻¹) • pureChoiCoefficient Ω

theorem pureChoiCoefficient_gram {A B E G : Type*}
    [Fintype A] [Fintype B] [Fintype E] [Fintype G]
    (Ω : (((A×B)×E)×G) → ℂ) :
    ((pureChoiCoefficient Ω).conjTranspose*pureChoiCoefficient Ω).transpose=
      partialTraceRight (traceMiddle (partialTraceRight (pureDensity Ω))) := by
  ext a c
  simp only [pureChoiCoefficient,Matrix.transpose_apply,Matrix.mul_apply,
    Matrix.conjTranspose_apply,Fintype.sum_prod_type,partialTraceRight,
    QuantumProver.WernerEndpoint.partialTraceLeft,traceMiddle,pureDensity,
    QuantumProver.WernerEndpoint.pureDensity,QuantumProver.WernerEndpoint.crossDensity]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e he
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro g hg
  ring

theorem splitterScale_complex_ne_zero : (splitterScale : ℂ) ≠ 0 := by
  intro h
  have hs := splitterScale_complex_sq
  rw [h] at hs
  norm_num at hs

theorem splitterScale_inv_norm :
    star ((splitterScale : ℂ)⁻¹)*(splitterScale : ℂ)⁻¹=2 := by
  simp only [star_inv,Complex.star_def,map_inv₀,Complex.conj_ofReal]
  rw [← pow_two,inv_pow,splitterScale_complex_sq]
  norm_num

theorem pureChoiIsometry_isometry {B E G : Type*}
    [Fintype B] [Fintype E] [Fintype G]
    (Ω : (((Qubit×B)×E)×G) → ℂ)
    (hA : partialTraceRight (traceMiddle (partialTraceRight (pureDensity Ω)))=
      (1/2 : ℂ) • (1 : QMatrix Qubit)) : IsIsometry (pureChoiIsometry Ω) := by
  have hg := pureChoiCoefficient_gram Ω
  rw [hA] at hg
  have hgram : (pureChoiCoefficient Ω).conjTranspose*pureChoiCoefficient Ω=
      (1/2 : ℂ) • (1 : QMatrix Qubit) := by
    have h := congrArg Matrix.transpose hg
    simpa only [Matrix.transpose_transpose,Matrix.transpose_smul,Matrix.transpose_one] using h
  rw [IsIsometry,pureChoiIsometry,Matrix.conjTranspose_smul,
    Matrix.smul_mul,Matrix.mul_smul,smul_smul,splitterScale_inv_norm,hgram]
  norm_num [smul_smul]

theorem pureChoiIsometry_bell_extension {B E G : Type*}
    (Ω : (((Qubit×B)×E)×G) → ℂ) :
    physicalPureExtension (pureChoiIsometry Ω*inputCoefficient bellKet)=Ω := by
  funext x
  rcases x with ⟨⟨⟨a,b⟩,e⟩,g⟩
  simp [physicalPureExtension,pureChoiIsometry,pureChoiCoefficient,inputCoefficient,
    Matrix.mul_apply,Matrix.smul_apply,bellKet,mul_ite,
    mul_assoc,mul_left_comm,mul_comm]
  rw [← mul_assoc,mul_inv_cancel₀ splitterScale_complex_ne_zero,one_mul]

theorem pureChoiCoefficient_localAction {A B E G : Type*}
    [Fintype A] [Fintype B] [Fintype E] [Fintype G]
    (U : QMatrix A) (UB : QMatrix B) (UE : QMatrix E) (UG : QMatrix G)
    (Ω : (((A×B)×E)×G) → ℂ) :
    ((UB ⊗ₖ UE) ⊗ₖ UG)*pureChoiCoefficient Ω*U.transpose=
      pureChoiCoefficient ((((U ⊗ₖ UB) ⊗ₖ UE) ⊗ₖ UG).mulVec Ω) := by
  ext ⟨⟨b,e⟩,g⟩ a
  simp only [pureChoiCoefficient,Matrix.mul_apply,Matrix.transpose_apply,
    Matrix.mulVec,dotProduct,Matrix.kronecker_apply,Fintype.sum_prod_type,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro c hc
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.sum_congr rfl
  intro f hf
  apply Finset.sum_congr rfl
  intro h hh
  ring

theorem pureChoiIsometry_intertwining {B E G : Type*}
    [Fintype B] [Fintype E] [Fintype G]
    (P : QMatrix Qubit) (hP : P*P=1)
    (UB : QMatrix B) (UE : QMatrix E) (UG : QMatrix G)
    (Ω : (((Qubit×B)×E)×G) → ℂ)
    (hΩ : ((((P.transpose ⊗ₖ UB) ⊗ₖ UE) ⊗ₖ UG).mulVec Ω)=Ω) :
    pureChoiIsometry Ω*P=((UB ⊗ₖ UE) ⊗ₖ UG)*pureChoiIsometry Ω := by
  have h := pureChoiCoefficient_localAction P.transpose UB UE UG Ω
  rw [Matrix.transpose_transpose,hΩ] at h
  have hmatrix : pureChoiCoefficient Ω*P=
      ((UB ⊗ₖ UE) ⊗ₖ UG)*pureChoiCoefficient Ω := by
    calc
      _ = (((UB ⊗ₖ UE) ⊗ₖ UG)*pureChoiCoefficient Ω*P)*P := by rw [h]
      _ = _ := by rw [Matrix.mul_assoc,hP,Matrix.mul_one]
  rw [pureChoiIsometry,Matrix.smul_mul,Matrix.mul_smul,hmatrix]

theorem pauli_square (k : CanonicalEnvironment) : pauli k*pauli k=1 := by
  fin_cases k <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [pauli,Matrix.mul_apply,Fin.sum_univ_two]

def canonicalBellBasis : Matrix (Qubit×Qubit) CanonicalEnvironment ℂ :=
  fun ab j => (splitterScale : ℂ)*pauli j ab.2 ab.1

theorem canonicalBellBasis_gram : canonicalBellBasis.conjTranspose*canonicalBellBasis=1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [canonicalBellBasis,pauli,Matrix.mul_apply,Matrix.conjTranspose_apply,
      Matrix.one_apply,Fintype.sum_prod_type,Fin.sum_univ_two,
      Complex.star_def,← Complex.ofReal_mul,← pow_two,
      splitterScale_sq,splitterScale_complex_sq] <;> ring_nf <;>
    norm_num [splitterScale_complex_sq,Complex.I_sq]

theorem canonicalBellBasis_right_gram :
    canonicalBellBasis*canonicalBellBasis.conjTranspose=1 := by
  ext ⟨a,b⟩ ⟨c,d⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    norm_num [canonicalBellBasis,pauli,Matrix.mul_apply,Matrix.conjTranspose_apply,
      Matrix.one_apply,Fin.sum_univ_succ,Complex.star_def,
      ← Complex.ofReal_mul,← pow_two,splitterScale_sq,splitterScale_complex_sq] <;>
    ring_nf <;> norm_num [splitterScale_complex_sq,Complex.I_sq]

def conjugateBellBasis : Matrix (Qubit×Qubit) CanonicalEnvironment ℂ :=
  canonicalBellBasis.conjTranspose.transpose

theorem conjugateBellBasis_conjTranspose :
    conjugateBellBasis.conjTranspose=canonicalBellBasis.transpose := by
  rw [conjugateBellBasis,Matrix.conjTranspose_transpose_eq_transpose_conjTranspose,
    Matrix.conjTranspose_conjTranspose]

theorem transposeBellBasis_conjugate : canonicalBellBasis.transpose*conjugateBellBasis=1 := by
  rw [conjugateBellBasis,← Matrix.transpose_mul,canonicalBellBasis_gram,Matrix.transpose_one]

theorem conjugateBellBasis_transpose : conjugateBellBasis*canonicalBellBasis.transpose=1 := by
  rw [conjugateBellBasis,← Matrix.transpose_mul,canonicalBellBasis_right_gram,Matrix.transpose_one]

def choiEnvironmentCoefficient {E G : Type*}
    (Ω : (((Qubit×Qubit)×E)×G) → ℂ) : Matrix (E×G) (Qubit×Qubit) ℂ :=
  fun eg ab => Ω ((ab,eg.1),eg.2)

theorem choiEnvironmentCoefficient_gram {E G : Type*} [Fintype E] [Fintype G]
    (Ω : (((Qubit×Qubit)×E)×G) → ℂ) :
    ((choiEnvironmentCoefficient Ω).conjTranspose*choiEnvironmentCoefficient Ω).transpose=
      partialTraceRight (partialTraceRight (pureDensity Ω)) := by
  ext ab cd
  simp only [choiEnvironmentCoefficient,Matrix.transpose_apply,Matrix.mul_apply,
    Matrix.conjTranspose_apply,Fintype.sum_prod_type,partialTraceRight,
    QuantumProver.WernerEndpoint.partialTraceLeft,pureDensity,QuantumProver.WernerEndpoint.pureDensity,
    QuantumProver.WernerEndpoint.crossDensity]
  apply Finset.sum_congr rfl
  intro e he
  apply Finset.sum_congr rfl
  intro g hg
  ring

def canonicalWeightDiagonal (p : ℝ) : QMatrix CanonicalEnvironment :=
  Matrix.diagonal (fun j => (pauliWeight p j : ℂ))

def canonicalRootDiagonal (p : ℝ) : QMatrix CanonicalEnvironment :=
  Matrix.diagonal (fun j => (Real.sqrt (pauliWeight p j) : ℂ))

def canonicalInvRootDiagonal (p : ℝ) : QMatrix CanonicalEnvironment :=
  Matrix.diagonal (fun j => (Real.sqrt (pauliWeight p j) : ℂ)⁻¹)

theorem complex_sqrt_ne_zero {q : ℝ} (hq : 0 < q) : (Real.sqrt q : ℂ) ≠ 0 := by
  exact_mod_cast (ne_of_gt (Real.sqrt_pos.2 hq))

theorem inv_sqrt_weight {q : ℝ} (hq : 0 < q) :
    (Real.sqrt q : ℂ)⁻¹*(q : ℂ)*(Real.sqrt q : ℂ)⁻¹=1 := by
  have hs : (Real.sqrt q : ℂ)^2=(q : ℂ) := by
    exact_mod_cast Real.sq_sqrt hq.le
  rw [← hs]
  field_simp [complex_sqrt_ne_zero hq] <;> ring

theorem canonicalInvRootDiagonal_conjTranspose (p : ℝ) :
    (canonicalInvRootDiagonal p).conjTranspose=canonicalInvRootDiagonal p := by
  simp [canonicalInvRootDiagonal,Matrix.diagonal_conjTranspose,Complex.star_def]

theorem canonicalInvRootDiagonal_weight {p : ℝ}
    (hq : ∀ j : CanonicalEnvironment,0 < pauliWeight p j) :
    canonicalInvRootDiagonal p*canonicalWeightDiagonal p*canonicalInvRootDiagonal p=1 := by
  rw [canonicalInvRootDiagonal,canonicalWeightDiagonal,
    Matrix.diagonal_mul_diagonal,Matrix.diagonal_mul_diagonal]
  ext i j
  simp [Matrix.diagonal_apply,Matrix.one_apply,inv_sqrt_weight (hq i)]

theorem canonicalInvRootDiagonal_root {p : ℝ}
    (hq : ∀ j : CanonicalEnvironment,0 < pauliWeight p j) :
    canonicalInvRootDiagonal p*canonicalRootDiagonal p=1 := by
  rw [canonicalInvRootDiagonal,canonicalRootDiagonal,Matrix.diagonal_mul_diagonal]
  ext i j
  simp [Matrix.diagonal_apply,Matrix.one_apply,complex_sqrt_ne_zero (hq i)]

def physicalEnvironmentExtraction {E G : Type*} [Fintype E] [Fintype G]
    (p : ℝ) (Ω : (((Qubit×Qubit)×E)×G) → ℂ) :
    Matrix (E×G) CanonicalEnvironment ℂ :=
  choiEnvironmentCoefficient Ω*conjugateBellBasis*canonicalInvRootDiagonal p

theorem physicalEnvironmentExtraction_isometry {E G : Type*}
    [Fintype E] [Fintype G] {p : ℝ}
    (hq : ∀ j : CanonicalEnvironment,0 < pauliWeight p j)
    (Ω : (((Qubit×Qubit)×E)×G) → ℂ)
    (hAB : partialTraceRight (partialTraceRight (pureDensity Ω))=
      canonicalBellBasis*canonicalWeightDiagonal p*canonicalBellBasis.conjTranspose) :
    IsIsometry (physicalEnvironmentExtraction p Ω) := by
  have hm := congrArg Matrix.transpose (choiEnvironmentCoefficient_gram Ω)
  rw [Matrix.transpose_transpose,hAB] at hm
  have hm' : (choiEnvironmentCoefficient Ω).conjTranspose*choiEnvironmentCoefficient Ω=
      conjugateBellBasis*canonicalWeightDiagonal p*canonicalBellBasis.transpose := by
    rw [hm,Matrix.transpose_mul,Matrix.transpose_mul,canonicalWeightDiagonal,
      Matrix.diagonal_transpose]
    simp only [conjugateBellBasis,Matrix.mul_assoc]
  unfold IsIsometry physicalEnvironmentExtraction
  rw [Matrix.conjTranspose_mul,Matrix.conjTranspose_mul,
    canonicalInvRootDiagonal_conjTranspose,conjugateBellBasis_conjTranspose]
  calc
    _ = canonicalInvRootDiagonal p*canonicalBellBasis.transpose*
        ((choiEnvironmentCoefficient Ω).conjTranspose*choiEnvironmentCoefficient Ω)*
          conjugateBellBasis*canonicalInvRootDiagonal p := by simp only [Matrix.mul_assoc]
    _ = canonicalInvRootDiagonal p*(canonicalBellBasis.transpose*conjugateBellBasis)*
        canonicalWeightDiagonal p*(canonicalBellBasis.transpose*conjugateBellBasis)*
          canonicalInvRootDiagonal p := by rw [hm']; simp only [Matrix.mul_assoc]
    _ = canonicalInvRootDiagonal p*canonicalWeightDiagonal p*canonicalInvRootDiagonal p := by
      simp only [transposeBellBasis_conjugate,Matrix.mul_one,Matrix.one_mul]
    _ = 1 := canonicalInvRootDiagonal_weight hq

theorem physicalEnvironmentExtraction_reconstruct {E G : Type*}
    [Fintype E] [Fintype G] {p : ℝ}
    (hq : ∀ j : CanonicalEnvironment,0 < pauliWeight p j)
    (Ω : (((Qubit×Qubit)×E)×G) → ℂ) :
    physicalEnvironmentExtraction p Ω*canonicalRootDiagonal p*canonicalBellBasis.transpose=
      choiEnvironmentCoefficient Ω := by
  unfold physicalEnvironmentExtraction
  calc
    _ = choiEnvironmentCoefficient Ω*conjugateBellBasis*
        (canonicalInvRootDiagonal p*canonicalRootDiagonal p)*canonicalBellBasis.transpose := by
      simp only [Matrix.mul_assoc]
    _ = _ := by rw [canonicalInvRootDiagonal_root hq,Matrix.mul_one,
      Matrix.mul_assoc,conjugateBellBasis_transpose,Matrix.mul_one]

def physicalEnvironmentStinespring {E G : Type*} [Fintype E] [Fintype G]
    {p : ℝ} (hq : ∀ j : CanonicalEnvironment,0 < pauliWeight p j)
    (Ω : (((Qubit×Qubit)×E)×G) → ℂ)
    (hAB : partialTraceRight (partialTraceRight (pureDensity Ω))=
      canonicalBellBasis*canonicalWeightDiagonal p*canonicalBellBasis.conjTranspose) :
    QuantumProver.WernerEndpoint.Stinespring CanonicalEnvironment E G :=
  ⟨physicalEnvironmentExtraction p Ω,physicalEnvironmentExtraction_isometry hq Ω hAB⟩

def CPTP.ofStinespring {I E G : Type*}
    [Fintype I] [Fintype E] [Fintype G] [DecidableEq I] [DecidableEq E]
    (N : QuantumProver.WernerEndpoint.Stinespring I E G) : CPTP I E :=
  CPTP.ofCompleteKraus (fun g e i => N.coeff (e,g) i) (by
    ext i j
    simp only [Matrix.sum_apply,Matrix.mul_apply,Matrix.conjTranspose_apply]
    change (∑ g : G,∑ e : E,star (N.coeff (e,g) i)*N.coeff (e,g) j)=_
    rw [Finset.sum_comm]
    have h := congrArg (fun M : QMatrix I => M i j) N.gram_eq_one
    simpa [Matrix.mul_apply,Matrix.conjTranspose_apply,Fintype.sum_prod_type] using h)

theorem CPTP.ofStinespring_apply {I E G : Type*}
    [Fintype I] [Fintype E] [Fintype G] [DecidableEq I] [DecidableEq E]
    (N : QuantumProver.WernerEndpoint.Stinespring I E G) (ρ : QMatrix I) :
    (CPTP.ofStinespring N).map ρ=N.apply ρ := by
  rw [CPTP.ofStinespring,CPTP.ofCompleteKraus_apply]
  ext e f
  simp [QuantumProver.WernerEndpoint.Stinespring.apply,QuantumProver.WernerEndpoint.partialTraceLeft,
    Matrix.sum_apply,Matrix.mul_apply,Matrix.conjTranspose_apply,
    Fintype.sum_prod_type,Finset.sum_mul,Finset.mul_sum]

theorem canonicalBellBoundary_marginal (δ : ℝ) :
    canonicalBellBasis*canonicalWeightDiagonal (boundaryMixing δ)*
      canonicalBellBasis.conjTranspose = Fixed16Flags.boundaryIsotropic δ := by
  ext ⟨a,b⟩ ⟨c,d⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    apply Complex.ext <;>
    norm_num [canonicalBellBasis,canonicalWeightDiagonal,pauliWeight,boundaryMixing,
      Fixed16Flags.boundaryIsotropic,Fixed16Flags.symmetricX,pauli,
      Matrix.mul_apply,Matrix.diagonal_apply,Matrix.conjTranspose_apply,
      Fin.sum_univ_succ,Complex.star_def,Complex.mul_re,Complex.mul_im] <;>
    ring_nf <;> simp [splitterScale_sq] <;> ring

theorem fixed16Omega_Bell_marginal {δ : ℝ}
    (hδ : 0 ≤ δ) (hmax : δ ≤ 21/512) :
    partialTraceRight (partialTraceRight (pureDensity
      (Identities.omegaKet (Scalar.boundaryR δ)))) =
      canonicalBellBasis*canonicalWeightDiagonal (boundaryMixing δ)*
        canonicalBellBasis.conjTranspose := by
  rw [canonicalBellBoundary_marginal]
  have hr := Scalar.boundaryR_nonneg hδ
  have hr1 : Scalar.boundaryR δ ≤ 1 :=
    (Scalar.boundaryR_le_quarter hδ hmax).trans (by norm_num)
  have hm := Fixed16Flags.omegaDensity_AB_exact (Scalar.boundaryR δ) hr hr1
  change partialTraceRight (partialTraceRight (pureDensity
    (Identities.omegaKet (Scalar.boundaryR δ)))) = _ at hm
  rw [Scalar.boundaryDelta_boundaryR hδ] at hm
  exact hm

def fixed16Stinespring (δ : ℝ) (hδ : 0 ≤ δ) (hmax : δ ≤ 21/512) :
    QuantumProver.WernerEndpoint.Stinespring CanonicalEnvironment
      Identities.FixedEnvironment Identities.FixedPurifier :=
  physicalEnvironmentStinespring
    (Identities.pauliWeights_boundary_positive hδ hmax)
    (Identities.omegaKet (Scalar.boundaryR δ)) (fixed16Omega_Bell_marginal hδ hmax)

def fixed16Squashing (δ : ℝ) (hδ : 0 ≤ δ) (hmax : δ ≤ 21/512) :
    CPTP CanonicalEnvironment Identities.FixedEnvironment :=
  CPTP.ofStinespring (fixed16Stinespring δ hδ hmax)

theorem fixed16Squashing_apply (δ : ℝ) (hδ : 0 ≤ δ) (hmax : δ ≤ 21/512)
    (ρ : QMatrix CanonicalEnvironment) :
    (fixed16Squashing δ hδ hmax).map ρ = (fixed16Stinespring δ hδ hmax).apply ρ :=
  CPTP.ofStinespring_apply _ _

theorem chosenJointCoefficient_bell_array {E G : Type*}
    [Fintype E] [Fintype G] (p : ℝ)
    (N : QuantumProver.WernerEndpoint.Stinespring CanonicalEnvironment E G) :
    (splitterScale : ℂ) • chosenJointCoefficient p N =
      fun x a => (N.coeff*canonicalRootDiagonal p*canonicalBellBasis.transpose)
        (x.1.2,x.2) (a,x.1.1) := by
  ext ⟨⟨b,e⟩,g⟩ a
  rw [Matrix.smul_apply,chosenJointCoefficient_apply]
  change (splitterScale : ℂ)*(∑ j,N.coeff (e,g) j*
    ((Real.sqrt (pauliWeight p j) : ℂ)*pauli j b a)) =
      ∑ j,(N.coeff*canonicalRootDiagonal p) (e,g) j*
        ((splitterScale : ℂ)*pauli j b a)
  simp only [canonicalRootDiagonal,Matrix.mul_diagonal]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem physicalEnvironment_chosenJoint_eq_pureChoi {E G : Type*}
    [Fintype E] [Fintype G] {p : ℝ}
    (hq : ∀ j : CanonicalEnvironment,0 < pauliWeight p j)
    (Ω : (((Qubit×Qubit)×E)×G) → ℂ)
    (hAB : partialTraceRight (partialTraceRight (pureDensity Ω))=
      canonicalBellBasis*canonicalWeightDiagonal p*canonicalBellBasis.conjTranspose) :
    chosenJointCoefficient p (physicalEnvironmentStinespring hq Ω hAB)=
      pureChoiIsometry Ω := by
  have hr := physicalEnvironmentExtraction_reconstruct hq Ω
  have hcoef : (splitterScale : ℂ) •
      chosenJointCoefficient p (physicalEnvironmentStinespring hq Ω hAB)=
      pureChoiCoefficient Ω := by
    rw [chosenJointCoefficient_bell_array]
    ext ⟨⟨b,e⟩,g⟩ a
    exact congrArg (fun M => M (e,g) (a,b)) hr
  have h := congrArg (fun M => (splitterScale : ℂ)⁻¹ • M) hcoef
  simpa only [smul_smul,inv_mul_cancel₀ splitterScale_complex_ne_zero,
    one_smul,pureChoiIsometry] using h

theorem fixed16Joint_eq_pureChoi (δ : ℝ) (hδ : 0 ≤ δ) (hmax : δ ≤ 21/512) :
    chosenJointCoefficient (boundaryMixing δ) (fixed16Stinespring δ hδ hmax)=
      pureChoiIsometry (Identities.omegaKet (Scalar.boundaryR δ)) :=
  physicalEnvironment_chosenJoint_eq_pureChoi _ _ _

theorem fixed16Squashing_Bell_extension (δ : ℝ) (hδ : 0 ≤ δ) (hmax : δ ≤ 21/512) :
    postSquashing (boundaryMixing δ) bellKet (fixed16Squashing δ hδ hmax)=
      partialTraceRight (pureDensity (Identities.omegaKet (Scalar.boundaryR δ))) := by
  rw [postSquashing_chosen_joint_extension (boundaryMixing δ) bellKet
    (fixed16Squashing δ hδ hmax) (fixed16Stinespring δ hδ hmax)
    (fun ρ => (fixed16Squashing_apply δ hδ hmax ρ).symm),
    fixed16Joint_eq_pureChoi,pureChoiIsometry_bell_extension]

theorem fixed16Joint_pauli_covariance (δ : ℝ) (hδ : 0 ≤ δ) (hmax : δ ≤ 21/512)
    (k : CanonicalEnvironment) :
    chosenJointCoefficient (boundaryMixing δ) (fixed16Stinespring δ hδ hmax)*pauli k=
      ((pauli k ⊗ₖ Identities.environmentFlagPauli k) ⊗ₖ
        Identities.purifierFlagPauli k)*
        chosenJointCoefficient (boundaryMixing δ) (fixed16Stinespring δ hδ hmax) := by
  rw [fixed16Joint_eq_pureChoi]
  apply pureChoiIsometry_intertwining (pauli k) (pauli_square k)
    (pauli k) (Identities.environmentFlagPauli k) (Identities.purifierFlagPauli k)
  exact Identities.omegaKet_pauli_covariance k (Scalar.boundaryR δ)

theorem fixed16Squashing_cmiNat_le_bell {R : Type*} [Fintype R] [DecidableEq R]
    (δ : ℝ) (hδ : 0 ≤ δ) (hmax : δ ≤ 21/512)
    (ψ : (R×Qubit) → ℂ) (hψ : IsNormalized ψ) :
    cmiNat (postSquashing (boundaryMixing δ) ψ (fixed16Squashing δ hδ hmax)) ≤
      cmiNat (postSquashing (boundaryMixing δ) bellKet (fixed16Squashing δ hδ hmax)) := by
  have hp := Identities.boundaryMixing_physical hδ hmax
  apply postSquashing_cmiNat_le_bell_of_chosenCovariance hp.1 hp.2
    (fixed16Squashing δ hδ hmax) (fixed16Stinespring δ hδ hmax)
    (fun ρ => (fixed16Squashing_apply δ hδ hmax ρ).symm)
    Identities.environmentFlagPauli Identities.purifierFlagPauli
    Identities.environmentFlagPauli_gram Identities.purifierFlagPauli_gram
    (fixed16Joint_pauli_covariance δ hδ hmax) ψ hψ

theorem fixed16Squashing_Bell_cost (δ : ℝ) (hδ : 0 ≤ δ) (hmax : δ ≤ 21/512) :
    cmiBits (postSquashing (boundaryMixing δ) bellKet (fixed16Squashing δ hδ hmax))/2 =
      Fixed16FlagEntropy.boundaryOmegaHalfCMIBits δ := by
  rw [fixed16Squashing_Bell_extension]
  rfl

def CPTP.reindexOutput {I E F : Type*} [Fintype I] [Fintype E] [Fintype F]
    (S : CPTP I E) (e : E ≃ F) : CPTP I F where
  map := (Matrix.reindexLinearEquiv ℂ ℂ e e).toLinearMap.comp S.map
  completelyPositive := by
    intro n ρ hρ
    change ((amplify S.map ρ).submatrix
      (fun x : Fin n×F => (x.1,e.symm x.2))
      (fun x : Fin n×F => (x.1,e.symm x.2))).PosSemidef
    exact (S.completelyPositive n ρ hρ).submatrix _
  tracePreserving := by
    intro ρ
    change (∑ f : F,S.map ρ (e.symm f) (e.symm f)) = Matrix.trace ρ
    calc
      _ = ∑ k : E,S.map ρ k k := e.symm.sum_comp (fun k => S.map ρ k k)
      _ = _ := S.tracePreserving ρ

theorem CPTP.reindexOutput_apply {I E F : Type*}
    [Fintype I] [Fintype E] [Fintype F] (S : CPTP I E) (e : E ≃ F)
    (ρ : QMatrix I) :
    (S.reindexOutput e).map ρ = Matrix.reindex e e (S.map ρ) := rfl

theorem postSquashing_reindexOutput {R E F : Type*}
    [Fintype R] [Fintype E] [Fintype F] (p : ℝ)
    (ψ : (R×Qubit) → ℂ) (S : CPTP CanonicalEnvironment E) (e : E ≃ F) :
    postSquashing p ψ (S.reindexOutput e)=
      Matrix.reindex (Equiv.prodCongr (Equiv.refl (R×Qubit)) e)
        (Equiv.prodCongr (Equiv.refl (R×Qubit)) e) (postSquashing p ψ S) := rfl

theorem traceMiddle_reindexEnvironment {A B E F : Type*}
    [Fintype B] (e : E ≃ F) (ρ : QMatrix ((A×B)×E)) :
    traceMiddle (Matrix.reindex (Equiv.prodCongr (Equiv.refl (A×B)) e)
      (Equiv.prodCongr (Equiv.refl (A×B)) e) ρ)=
      Matrix.reindex (Equiv.prodCongr (Equiv.refl A) e)
        (Equiv.prodCongr (Equiv.refl A) e) (traceMiddle ρ) := rfl

theorem traceFirst_reindexEnvironment {A B E F : Type*}
    [Fintype A] (e : E ≃ F) (ρ : QMatrix ((A×B)×E)) :
    traceFirst (Matrix.reindex (Equiv.prodCongr (Equiv.refl (A×B)) e)
      (Equiv.prodCongr (Equiv.refl (A×B)) e) ρ)=
      Matrix.reindex (Equiv.prodCongr (Equiv.refl B) e)
        (Equiv.prodCongr (Equiv.refl B) e) (traceFirst ρ) := rfl

theorem partialTraceLeft_reindexEnvironment {A E F : Type*}
    [Fintype A] (e : E ≃ F) (ρ : QMatrix (A×E)) :
    partialTraceLeft (Matrix.reindex (Equiv.prodCongr (Equiv.refl A) e)
      (Equiv.prodCongr (Equiv.refl A) e) ρ)=
      Matrix.reindex e e (partialTraceLeft ρ) := rfl

theorem cmiNat_reindexEnvironment {A B E F : Type*}
    [Fintype A] [Fintype B] [Fintype E] [Fintype F]
    [DecidableEq A] [DecidableEq B] [DecidableEq E] [DecidableEq F]
    (e : E ≃ F) {ρ : QMatrix ((A×B)×E)} (hρ : ρ.PosSemidef) :
    cmiNat (Matrix.reindex (Equiv.prodCongr (Equiv.refl (A×B)) e)
      (Equiv.prodCongr (Equiv.refl (A×B)) e) ρ)=cmiNat ρ := by
  unfold cmiNat
  rw [traceMiddle_reindexEnvironment,traceFirst_reindexEnvironment,
    partialTraceLeft_reindexEnvironment,
    entropyNat_reindex _ (traceMiddle_positive hρ).1,
    entropyNat_reindex _ (traceFirst_positive hρ).1,
    entropyNat_reindex _ (partialTraceLeft_positive hρ).1,
    entropyNat_reindex _ hρ.1]

theorem cmiBits_reindexEnvironment {A B E F : Type*}
    [Fintype A] [Fintype B] [Fintype E] [Fintype F]
    [DecidableEq A] [DecidableEq B] [DecidableEq E] [DecidableEq F]
    (e : E ≃ F) {ρ : QMatrix ((A×B)×E)} (hρ : ρ.PosSemidef) :
    cmiBits (Matrix.reindex (Equiv.prodCongr (Equiv.refl (A×B)) e)
      (Equiv.prodCongr (Equiv.refl (A×B)) e) ρ)=cmiBits ρ := by
  rw [cmiBits,cmiBits,cmiNat_reindexEnvironment e hρ]

def fixed16EnvironmentEquiv : Identities.FixedEnvironment ≃ Fin 16 :=
  Fintype.equivFinOfCardEq Identities.fixedEnvironment_card

def fixed16SquashingFin (δ : ℝ) (hδ : 0 ≤ δ) (hmax : δ ≤ 21/512) :
    CPTP CanonicalEnvironment (Fin 16) :=
  (fixed16Squashing δ hδ hmax).reindexOutput fixed16EnvironmentEquiv

theorem fixed16SquashingFin_cmiBits {R : Type*} [Fintype R] [DecidableEq R]
    (δ : ℝ) (hδ : 0 ≤ δ) (hmax : δ ≤ 21/512) (ψ : (R×Qubit) → ℂ) :
    cmiBits (postSquashing (boundaryMixing δ) ψ (fixed16SquashingFin δ hδ hmax))=
      cmiBits (postSquashing (boundaryMixing δ) ψ (fixed16Squashing δ hδ hmax)) := by
  rw [fixed16SquashingFin,postSquashing_reindexOutput]
  exact cmiBits_reindexEnvironment fixed16EnvironmentEquiv (postSquashing_positive _ _ _)

theorem fixed16SquashingFin_halfCost_le {R : Type*} [Fintype R] [DecidableEq R]
    (δ : ℝ) (hδ : 0 ≤ δ) (hmax : δ ≤ 21/512)
    (ψ : (R×Qubit) → ℂ) (hψ : IsNormalized ψ) :
    cmiBits (postSquashing (boundaryMixing δ) ψ (fixed16SquashingFin δ hδ hmax))/2 ≤
      Fixed16FlagEntropy.boundaryOmegaHalfCMIBits δ := by
  rw [fixed16SquashingFin_cmiBits,← fixed16Squashing_Bell_cost δ hδ hmax]
  apply div_le_div_of_nonneg_right _ (by norm_num : (0 : ℝ) ≤ 2)
  unfold cmiBits
  exact div_le_div_of_nonneg_right (fixed16Squashing_cmiNat_le_bell δ hδ hmax ψ hψ)
    (Real.log_pos (by norm_num)).le

theorem fixed16SquashingFin_Bell_cost (δ : ℝ) (hδ : 0 ≤ δ) (hmax : δ ≤ 21/512) :
    cmiBits (postSquashing (boundaryMixing δ) bellKet (fixed16SquashingFin δ hδ hmax))/2 =
      Fixed16FlagEntropy.boundaryOmegaHalfCMIBits δ := by
  rw [fixed16SquashingFin_cmiBits,fixed16Squashing_Bell_cost]

def fixed16MapHalfCosts (δ : ℝ) (hδ : 0 ≤ δ) (hmax : δ ≤ 21/512) : Set ℝ :=
  {x | ∃ r : ℕ, ∃ ψ : (Fin r×Qubit) → ℂ, IsNormalized ψ ∧
    x=cmiBits (postSquashing (boundaryMixing δ) ψ (fixed16SquashingFin δ hδ hmax))/2}

theorem fixed16SameMapMaximum (δ : ℝ) (hδ : 0 ≤ δ) (hmax : δ ≤ 21/512) :
    IsGreatest (fixed16MapHalfCosts δ hδ hmax)
      (Fixed16FlagEntropy.boundaryOmegaHalfCMIBits δ) := by
  constructor
  · exact ⟨2,bellKet,bellKet_normalized,(fixed16SquashingFin_Bell_cost δ hδ hmax).symm⟩
  · rintro x ⟨r,ψ,hψ,rfl⟩
    exact fixed16SquashingFin_halfCost_le δ hδ hmax ψ hψ

theorem channelSquashed_boundary_le_fixed16Cost (δ : ℝ)
    (hδ : 0 ≤ δ) (hmax : δ ≤ 21/512) :
    channelSquashed (boundaryMixing δ) ≤ Fixed16FlagEntropy.boundaryOmegaHalfCMIBits δ := by
  apply channelSquashed_le_of_fixed_squashing (boundaryMixing δ)
    (fixed16SquashingFin δ hδ hmax) _ (fun r ψ hψ => inputCosts_bddBelow _ ψ)
  intro r ψ hψ
  simpa only [div_eq_mul_inv,mul_comm,one_mul] using
    fixed16SquashingFin_halfCost_le δ hδ hmax ψ hψ

theorem channelSquashed_boundary_quadratic_upper :
    ∃ C : ℝ, 0 < C ∧ ∀ δ : ℝ, 0 ≤ δ → δ ≤ 21/512 →
      channelSquashed (boundaryMixing δ) ≤ C*δ^2 := by
  obtain ⟨C,hC,hb⟩ := Fixed16FlagEntropy.boundaryOmegaHalfCMIBits_quadratic_upper
  exact ⟨C,hC,fun δ hδ hmax =>
    (channelSquashed_boundary_le_fixed16Cost δ hδ hmax).trans (hb δ hδ hmax)⟩

theorem fixed16SameMapCost_uniform_remainder :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (δ : ℝ) (hδ : 0 ≤ δ) (hmax : δ ≤ 21/512),
      |cmiBits (postSquashing (boundaryMixing δ) bellKet (fixed16SquashingFin δ hδ hmax))/2-
        (3200*Scalar.boundaryKappa/(81*Real.log 2))*δ^2| ≤ C*δ^3 := by
  obtain ⟨C,hC,hb⟩ := Fixed16FlagEntropy.boundaryOmegaHalfCMIBits_uniform_remainder
  refine ⟨C,hC,?_⟩
  intro δ hδ hmax
  rw [fixed16SquashingFin_Bell_cost]
  exact hb δ hδ hmax

theorem CPTP.partialTraceRight_amplify {I E R : Type*}
    [Fintype I] [Fintype E] [Fintype R]
    (S : CPTP I E) (ρ : QMatrix (R×I)) :
    partialTraceRight (amplify S.map ρ)=partialTraceRight ρ := by
  ext r s
  exact S.tracePreserving (fun i j => ρ (r,i) (s,j))

theorem referenceCoeff_preserves_retained {I B E G : Type*}
    [Fintype I] [Fintype B] [Fintype E] [Fintype G]
    [DecidableEq I] [DecidableEq B]
    (N : QuantumProver.WernerEndpoint.Stinespring I E G) (ρ : QMatrix (B×I)) :
    partialTraceRight (partialTraceRight
      (N.referenceCoeff B*ρ*(N.referenceCoeff B).conjTranspose))=
      partialTraceRight ρ := by
  ext b c
  let block : QMatrix I := fun i j => ρ (b,i) (c,j)
  have hs :
      (N.referenceCoeff B*ρ*(N.referenceCoeff B).conjTranspose).submatrix
        (fun x : E×G => ((b,x.1),x.2))
        (fun x : E×G => ((c,x.1),x.2))=
      N.coeff*block*N.coeff.conjTranspose := by
    ext x y
    simp [QuantumProver.WernerEndpoint.Stinespring.referenceCoeff,Matrix.submatrix,
      Matrix.mul_apply,Matrix.conjTranspose_apply,Fintype.sum_prod_type,
      ite_mul,mul_ite,apply_ite,Finset.sum_mul,Finset.mul_sum,block]
  have ht : Matrix.trace
    ((N.referenceCoeff B*ρ*(N.referenceCoeff B).conjTranspose).submatrix
      (fun x : E×G => ((b,x.1),x.2))
      (fun x : E×G => ((c,x.1),x.2)))=
      partialTraceRight (partialTraceRight
        (N.referenceCoeff B*ρ*(N.referenceCoeff B).conjTranspose)) b c := by
    simp [Matrix.trace,Matrix.diag,Matrix.submatrix,Fintype.sum_prod_type,
      partialTraceRight,QuantumProver.WernerEndpoint.partialTraceLeft]
  change _ = Matrix.trace block
  rw [← ht,hs,Matrix.trace_mul_cycle,N.gram_eq_one,Matrix.one_mul]

theorem chosenJointCoefficient_physical_channel {E G : Type*}
    [Fintype E] [Fintype G] [DecidableEq E] [DecidableEq G]
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (N : QuantumProver.WernerEndpoint.Stinespring CanonicalEnvironment E G) (ρ : QMatrix Qubit) :
    partialTraceRight (partialTraceRight
      (chosenJointCoefficient p N*ρ*(chosenJointCoefficient p N).conjTranspose))=
      depolarizing p ρ := by
  have hc :
      chosenJointCoefficient p N*ρ*(chosenJointCoefficient p N).conjTranspose=
      N.referenceCoeff Qubit*(canonicalIsometry p*ρ*(canonicalIsometry p).conjTranspose)*
        (N.referenceCoeff Qubit).conjTranspose := by
    simp only [chosenJointCoefficient,Matrix.conjTranspose_mul,Matrix.mul_assoc]
  rw [hc,referenceCoeff_preserves_retained]
  exact canonicalStinespring_apply hp0 hp1 ρ

theorem fixed16Joint_physical_channel (δ : ℝ)
    (hδ : 0 ≤ δ) (hmax : δ ≤ 21/512) (ρ : QMatrix Qubit) :
    partialTraceRight (partialTraceRight
      (chosenJointCoefficient (boundaryMixing δ) (fixed16Stinespring δ hδ hmax)*ρ*
        (chosenJointCoefficient (boundaryMixing δ) (fixed16Stinespring δ hδ hmax)).conjTranspose))=
      depolarizing (boundaryMixing δ) ρ := by
  have hp := Identities.boundaryMixing_physical hδ hmax
  exact chosenJointCoefficient_physical_channel hp.1 hp.2 _ ρ

theorem pureAGCoefficient_fourImageVector {E G : Type*}
    (p : ℝ) (M : CanonicalEnvironment → Matrix E G ℂ) :
    pureAGCoefficient (fourImageVector p M)=fourImageAmplitudeG p M := rfl

theorem postSquashing_bell_half_cmiNat_fourImage {E : Type*}
    [Fintype E] [DecidableEq E] (p : ℝ) (S : CPTP CanonicalEnvironment E) :
    (1/2 : ℝ)*cmiNat (postSquashing p bellKet S)=
      (entropyNat
          (fourImageAmplitudeE p (squashingImageMatrices S)*
            (fourImageAmplitudeE p (squashingImageMatrices S)).conjTranspose)+
        entropyNat
          (fourImageAmplitudeG p (squashingImageMatrices S)*
            (fourImageAmplitudeG p (squashingImageMatrices S)).conjTranspose)-
        entropyNat (partialTraceLeft (partialTraceRight
          (pureDensity (fourImageVector p (squashingImageMatrices S)))))-
        entropyNat (partialTraceLeft
          (pureDensity (fourImageVector p (squashingImageMatrices S)))))/2 := by
  rw [postSquashing_bell_fourImages,cmiNat_pure_complementary,
    fourImageE_gram,pureAGCoefficient_fourImageVector]
  ring

def fourImageFcalLoss (p : ℝ) : ℝ :=
  (p/4)*Fcal (4/p)+(p/8)*Fcal ((8-4*p)/p)+(6+2*Real.log 2)*(p/4)

theorem fourImageFcalLoss_uniform_log_bound {p : ℝ}
    (hp0 : 0 < p) (hp1 : p ≤ 1/2) :
    fourImageFcalLoss p ≤ (3*p/8)*Real.log (1/p)+
      ((18+11*Real.log 2)/8)*p := by
  have hm1 : 2 ≤ 4/p := (le_div_iff₀ hp0).mpr (by linarith only [hp1])
  have hm2 : 2 ≤ (8-4*p)/p := (le_div_iff₀ hp0).mpr (by linarith only [hp1])
  have hratioPos : 0 < (8-4*p)/p := by
    apply div_pos _ hp0
    linarith only [hp1]
  have hratioLe : (8-4*p)/p ≤ 8/p := by
    exact div_le_div_of_nonneg_right (by linarith only [hp0]) hp0.le
  have hlogLe := Real.log_le_log hratioPos hratioLe
  have hF1 := c1_Fcal_log_add_two hm1
  have hF2 : Fcal ((8-4*p)/p) ≤ Real.log (8/p)+2 := by
    have hF := c1_Fcal_log_add_two hm2
    linarith only [hF,hlogLe]
  have h1 := mul_le_mul_of_nonneg_left hF1 (by positivity : (0:ℝ) ≤ p/4)
  have h2 := mul_le_mul_of_nonneg_left hF2 (by positivity : (0:ℝ) ≤ p/8)
  have hlog4 : Real.log (4/p)=Real.log (1/p)+2*Real.log 2 := by
    rw [Real.log_div (by norm_num : (4:ℝ)≠0) hp0.ne',
      Real.log_div (by norm_num : (1:ℝ)≠0) hp0.ne',Real.log_one]
    have hpow := Real.log_pow (2:ℝ) 2
    norm_num at hpow
    rw [hpow]
    ring
  have hlog8 : Real.log (8/p)=Real.log (1/p)+3*Real.log 2 := by
    rw [Real.log_div (by norm_num : (8:ℝ)≠0) hp0.ne',
      Real.log_div (by norm_num : (1:ℝ)≠0) hp0.ne',Real.log_one]
    have hpow := Real.log_pow (2:ℝ) 3
    norm_num at hpow
    rw [hpow]
    ring
  calc
    fourImageFcalLoss p ≤
        (p/4)*(Real.log (4/p)+2)+(p/8)*(Real.log (8/p)+2)+
          (6+2*Real.log 2)*(p/4) := by
      dsimp [fourImageFcalLoss]
      linarith only [h1,h2]
    _ = _ := by rw [hlog4,hlog8]; ring

theorem postSquashing_bell_half_cmiNat_eq_fourImageHalfCost {E : Type*}
    [Fintype E] [DecidableEq E] (p : ℝ) (S : CPTP CanonicalEnvironment E) :
    (1/2 : ℝ)*cmiNat (postSquashing p bellKet S)=
      EntropySharing.fourImageHalfCostNat p (squashingImageMatrices S) :=
  postSquashing_bell_half_cmiNat_fourImage p S

theorem postSquashing_bell_half_cmiNat_lower_Fcal {E : Type*}
    [Fintype E] [DecidableEq E] {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1)
    (S : CPTP CanonicalEnvironment E) :
    Real.log 2-fourImageFcalLoss p ≤ (1/2 : ℝ)*cmiNat (postSquashing p bellKet S) := by
  have hM : EntropySharing.ImageOrthonormal (squashingImageMatrices S) :=
    squashingImageMatrices_orthonormal S
  have hc := EntropySharing.fourImageHalfCostNat_lower hM hp0 hp1
  have harg0 : 1/EntropySharing.noiseWeight p=4/p := by
    dsimp [EntropySharing.noiseWeight]
    field_simp [hp0.ne']
  have harg1 : 2*EntropySharing.coherentWeight p/EntropySharing.noiseWeight p=
      (8-4*p)/p := by
    dsimp [EntropySharing.noiseWeight,EntropySharing.coherentWeight]
    field_simp [hp0.ne']
    ring
  rw [harg0,harg1,← postSquashing_bell_half_cmiNat_eq_fourImageHalfCost p S] at hc
  dsimp [EntropySharing.noiseWeight] at hc
  dsimp [fourImageFcalLoss]
  linarith only [hc]

theorem postSquashing_bell_half_cmiBits_lowNoise_lower {E : Type*}
    [Fintype E] [DecidableEq E] {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1/2)
    (S : CPTP CanonicalEnvironment E) :
    lowNoiseProfile p-((18+11*Real.log 2)/(8*Real.log 2))*p ≤
      (1/2 : ℝ)*cmiBits (postSquashing p bellKet S) := by
  have hc := postSquashing_bell_half_cmiNat_lower_Fcal hp0 (by linarith only [hp1]) S
  have he := fourImageFcalLoss_uniform_log_bound hp0 hp1
  have hnat : Real.log 2-(3*p/8)*Real.log (1/p)-((18+11*Real.log 2)/8)*p ≤
      (1/2 : ℝ)*cmiNat (postSquashing p bellKet S) := by linarith only [hc,he]
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  calc
    lowNoiseProfile p-((18+11*Real.log 2)/(8*Real.log 2))*p =
      (Real.log 2-(3*p/8)*Real.log (1/p)-((18+11*Real.log 2)/8)*p)/Real.log 2 := by
        dsimp [lowNoiseProfile]
        field_simp [hl.ne']
    _ ≤ ((1/2 : ℝ)*cmiNat (postSquashing p bellKet S))/Real.log 2 :=
      div_le_div_of_nonneg_right hnat hl.le
    _ = _ := by rw [cmiBits]; ring

theorem squashedInputValue_bell_lowNoise_lower {p : ℝ}
    (hp0 : 0 < p) (hp1 : p ≤ 1/2) :
    lowNoiseProfile p-((18+11*Real.log 2)/(8*Real.log 2))*p ≤
      squashedInputValue p bellKet := by
  have hInf : 2*(lowNoiseProfile p-((18+11*Real.log 2)/(8*Real.log 2))*p) ≤
      sInf (inputCosts p bellKet) := by
    apply le_csInf (inputCosts_nonempty p bellKet)
    intro x hx
    rcases hx with ⟨e,S,rfl⟩
    have h := postSquashing_bell_half_cmiBits_lowNoise_lower hp0 hp1 S
    linarith only [h]
  unfold squashedInputValue
  linarith only [hInf]

theorem channelSquashed_lowNoise_lower {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1/2) :
    lowNoiseProfile p-((18+11*Real.log 2)/(8*Real.log 2))*p ≤ channelSquashed p := by
  have hBell : squashedInputValue p bellKet ≤ channelSquashed p :=
    le_csSup (channelInputValues_bddAbove hp0.le (by linarith only [hp1]))
      ⟨2,bellKet,bellKet_normalized,rfl⟩
  exact (squashedInputValue_bell_lowNoise_lower hp0 hp1).trans hBell

theorem channelSquashed_lowNoise_uniform_remainder :
    ∃ C : ℝ,0<C ∧ ∀ p : ℝ,0<p → p≤1/2 →
      |channelSquashed p-lowNoiseProfile p| ≤ C*p := by
  let L : ℝ := (18+11*Real.log 2)/(8*Real.log 2)
  let U : ℝ := (3/8)*(8+Real.log 8)/Real.log 2
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h8 : 0 < Real.log 8 := Real.log_pos (by norm_num)
  have hL : 0<L := by dsimp [L]; positivity
  have hU : 0<U := by dsimp [U]; positivity
  refine ⟨L+U+1,by linarith,?_⟩
  intro p hp0 hp1
  have hlow := channelSquashed_lowNoise_lower hp0 hp1
  change lowNoiseProfile p-L*p ≤ channelSquashed p at hlow
  have hupp : channelSquashed p ≤ lowNoiseProfile p+U*p := by
    have h := channelSquashed_lowNoise_upper hp0 hp1
    convert h using 1
    dsimp [U]
    ring
  apply abs_le.mpr
  constructor <;> nlinarith only [hlow,hupp,hL,hU,hp0]

open Filter
open scoped Topology

theorem channelSquashed_lowNoise_isBigO :
    Asymptotics.IsBigO (𝓝[>] (0:ℝ))
      (fun p : ℝ => channelSquashed p-lowNoiseProfile p) (fun p : ℝ => p) := by
  obtain ⟨C,hC,hbound⟩ := channelSquashed_lowNoise_uniform_remainder
  apply Asymptotics.IsBigO.of_bound C
  have hpos : ∀ᶠ p : ℝ in 𝓝[>] (0:ℝ),0<p := self_mem_nhdsWithin
  have hsmall : ∀ᶠ p : ℝ in 𝓝[>] (0:ℝ),p<1/2 :=
    (eventually_lt_nhds (by norm_num : (0:ℝ)<1/2)).filter_mono nhdsWithin_le_nhds
  filter_upwards [hpos,hsmall] with p hp hs
  simpa only [Real.norm_eq_abs,abs_of_pos hp] using hbound p hp hs.le

end QuantumProver.DepolarizingSquashedEntanglement

import QuantumProver.InformationTheory.DepolarizingSquashedEntanglement.EntropyExpansion
import QuantumProver.InformationTheory.DepolarizingSquashedEntanglement.BoundaryEntropyBounds
import QuantumProver.InformationTheory.DepolarizingSquashedEntanglement.StinespringEntropyBounds
import QuantumProver.InformationTheory.ConditionalEntropy.MixtureEntropy

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix Kronecker
  Matrix.Norms.L2Operator ContinuousFunctionalCalculus

namespace QuantumProver.DepolarizingSquashedEntanglement.EntropySharing

variable {E G : Type*} [Fintype E] [Fintype G] [DecidableEq E] [DecidableEq G]

def ImageOrthonormal (M : CanonicalEnvironment → Matrix E G ℂ) : Prop :=
  ∀ i j, Matrix.trace ((M i)ᴴ * M j) = if i = j then 1 else 0

theorem hsSq_fromBlocks {I J K L : Type*}
    [Fintype I] [Fintype J] [Fintype K] [Fintype L]
    [DecidableEq I] [DecidableEq J] [DecidableEq K] [DecidableEq L]
    (A : Matrix I K ℂ) (B : Matrix I L ℂ)
    (C : Matrix J K ℂ) (D : Matrix J L ℂ) :
    hsSq (Matrix.fromBlocks A B C D) = hsSq A + hsSq B + hsSq C + hsSq D := by
  simp only [hsSq, c1_trace_gram, c1HsMass_fromBlocks]

theorem hsSq_smul_real (c : ℝ) (M : Matrix E G ℂ) :
    hsSq (c • M) = c ^ 2 * hsSq M := by
  simp [hsSq, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, Matrix.trace_smul, Complex.smul_re, pow_two, mul_assoc]

theorem hsSq_two_orthonormal {M N : Matrix E G ℂ}
    (hM : Matrix.trace (Mᴴ * M) = 1) (hN : Matrix.trace (Nᴴ * N) = 1)
    (hMN : Matrix.trace (Mᴴ * N) = 0) (hNM : Matrix.trace (Nᴴ * M) = 0)
    (a b : ℂ) : hsSq (a • M + b • N) = Complex.normSq a + Complex.normSq b := by
  simp only [hsSq, Matrix.conjTranspose_add, Matrix.conjTranspose_smul,
    Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, Matrix.trace_add, Matrix.trace_smul, hM, hN, hMN, hNM]
  simp [c1_star_mul_re_normSq, Complex.normSq_apply]

theorem image_hsSq_one {M : CanonicalEnvironment → Matrix E G ℂ}
    (hM : ImageOrthonormal M) (i : CanonicalEnvironment) : hsSq (M i) = 1 := by
  simpa [hsSq] using congrArg Complex.re (hM i i)

theorem image_hsSq_two {M : CanonicalEnvironment → Matrix E G ℂ}
    (hM : ImageOrthonormal M) {i j : CanonicalEnvironment} (hij : i ≠ j)
    (a b : ℂ) : hsSq (a • M i + b • M j) = Complex.normSq a + Complex.normSq b := by
  apply hsSq_two_orthonormal
  · simpa using hM i i
  · simpa using hM j j
  · simpa [hij] using hM i j
  · simpa [Ne.symm hij] using hM j i

theorem images_transpose_orthonormal {M : CanonicalEnvironment → Matrix E G ℂ}
    (hM : ImageOrthonormal M) : ImageOrthonormal (fun i => (M i).transpose) := by
  intro i j
  have heq : Matrix.trace ((M i).transposeᴴ * (M j).transpose) =
      Matrix.trace ((M i)ᴴ * M j) := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Matrix.transpose_apply]
    exact Finset.sum_comm
  rw [heq]
  exact hM i j

def vacuumWeight (p : ℝ) : ℝ := 1 - 3 * p / 4
def noiseWeight (p : ℝ) : ℝ := p / 4
def coherentWeight (p : ℝ) : ℝ := 1 - p / 2

def coherentPlus (p : ℝ) (M : CanonicalEnvironment → Matrix E G ℂ) : Matrix E G ℂ :=
  (Real.sqrt (vacuumWeight p) : ℂ) • M 0 + (Real.sqrt (noiseWeight p) : ℂ) • M 3

def coherentMinus (p : ℝ) (M : CanonicalEnvironment → Matrix E G ℂ) : Matrix E G ℂ :=
  (Real.sqrt (vacuumWeight p) : ℂ) • M 0 - (Real.sqrt (noiseWeight p) : ℂ) • M 3

def noisePlus (M : CanonicalEnvironment → Matrix E G ℂ) : Matrix E G ℂ := M 1 + Complex.I • M 2
def noiseMinus (M : CanonicalEnvironment → Matrix E G ℂ) : Matrix E G ℂ := M 1 - Complex.I • M 2

theorem noisePlus_hsSq {M : CanonicalEnvironment → Matrix E G ℂ}
    (hM : ImageOrthonormal M) : hsSq (noisePlus M) = 2 := by
  have h := image_hsSq_two hM (by decide : (1 : CanonicalEnvironment) ≠ 2) 1 Complex.I
  norm_num [noisePlus, Complex.normSq_apply] at h ⊢
  exact h

theorem noiseMinus_hsSq {M : CanonicalEnvironment → Matrix E G ℂ}
    (hM : ImageOrthonormal M) : hsSq (noiseMinus M) = 2 := by
  have h := image_hsSq_two hM (by decide : (1 : CanonicalEnvironment) ≠ 2) 1 (-Complex.I)
  norm_num [noiseMinus, sub_eq_add_neg, Complex.normSq_apply] at h ⊢
  exact h

theorem coherentPlus_hsSq {M : CanonicalEnvironment → Matrix E G ℂ}
    (hM : ImageOrthonormal M) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    hsSq (coherentPlus p M) = coherentWeight p := by
  have hF : 0 ≤ vacuumWeight p := by dsimp [vacuumWeight]; linarith
  have ha : 0 ≤ noiseWeight p := by dsimp [noiseWeight]; positivity
  rw [coherentPlus, image_hsSq_two hM (by decide : (0 : CanonicalEnvironment) ≠ 3)]
  simp only [Complex.normSq_ofReal, ← pow_two, Real.sq_sqrt hF, Real.sq_sqrt ha]
  dsimp [vacuumWeight, noiseWeight, coherentWeight]
  ring

theorem coherentMinus_hsSq {M : CanonicalEnvironment → Matrix E G ℂ}
    (hM : ImageOrthonormal M) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    hsSq (coherentMinus p M) = coherentWeight p := by
  have hF : 0 ≤ vacuumWeight p := by dsimp [vacuumWeight]; linarith
  have ha : 0 ≤ noiseWeight p := by dsimp [noiseWeight]; positivity
  rw [coherentMinus, sub_eq_add_neg, ← neg_smul,
    image_hsSq_two hM (by decide : (0 : CanonicalEnvironment) ≠ 3)]
  simp only [Complex.normSq_neg, Complex.normSq_ofReal, ← pow_two,
    Real.sq_sqrt hF, Real.sq_sqrt ha]
  dsimp [vacuumWeight, noiseWeight, coherentWeight]
  ring

def spinIndex (I : Type*) : I ⊕ I → Qubit × I
  | Sum.inl i => (0, i)
  | Sum.inr i => (1, i)

def spinAmplitude (p : ℝ) (M : CanonicalEnvironment → Matrix E G ℂ) :
    Matrix (E ⊕ E) (G ⊕ G) ℂ :=
  (splitterScale : ℝ) • Matrix.fromBlocks (coherentPlus p M)
    ((Real.sqrt (noiseWeight p) : ℝ) • noisePlus M)
    ((Real.sqrt (noiseWeight p) : ℝ) • noiseMinus M) (coherentMinus p M)

theorem fourImageAmplitudeE_spin (p : ℝ) (M : CanonicalEnvironment → Matrix E G ℂ) :
    (fourImageAmplitudeE p M).submatrix (spinIndex E) (spinIndex G) = spinAmplitude p M := by
  ext i j
  cases i <;> cases j <;>
    norm_num [fourImageAmplitudeE, fourImageVector, spinIndex, spinAmplitude,
      coherentPlus, coherentMinus, noisePlus, noiseMinus, vacuumWeight, noiseWeight,
      pauliWeight, pauli, Fin.sum_univ_succ, Matrix.submatrix_apply,
      Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply, Complex.real_smul] <;> try ring
  all_goals simp

theorem fourImageAmplitudeG_spin (p : ℝ) (M : CanonicalEnvironment → Matrix E G ℂ) :
    (fourImageAmplitudeG p M).submatrix (spinIndex G) (spinIndex E) =
      spinAmplitude p (fun i => (M i).transpose) := by
  have heq : fourImageAmplitudeG p M = fourImageAmplitudeE p (fun i => (M i).transpose) := rfl
  rw [heq, fourImageAmplitudeE_spin]

theorem spinAmplitude_offLeft_hsSq {M : CanonicalEnvironment → Matrix E G ℂ}
    (hM : ImageOrthonormal M) {p : ℝ} (hp0 : 0 ≤ p) :
    hsSq ((spinAmplitude p M).submatrix Sum.inl Sum.inr) = noiseWeight p := by
  have ha : 0 ≤ noiseWeight p := by dsimp [noiseWeight]; positivity
  have heq : (spinAmplitude p M).submatrix Sum.inl Sum.inr =
      (splitterScale * Real.sqrt (noiseWeight p) : ℝ) • noisePlus M := by
    ext e g
    simp [spinAmplitude, Matrix.submatrix_apply, smul_smul, mul_assoc]
  rw [heq, hsSq_smul_real, mul_pow, splitterScale_sq, Real.sq_sqrt ha, noisePlus_hsSq hM]
  ring

theorem spinAmplitude_offRight_hsSq {M : CanonicalEnvironment → Matrix E G ℂ}
    (hM : ImageOrthonormal M) {p : ℝ} (hp0 : 0 ≤ p) :
    hsSq ((spinAmplitude p M).submatrix Sum.inr Sum.inl) = noiseWeight p := by
  have ha : 0 ≤ noiseWeight p := by dsimp [noiseWeight]; positivity
  have heq : (spinAmplitude p M).submatrix Sum.inr Sum.inl =
      (splitterScale * Real.sqrt (noiseWeight p) : ℝ) • noiseMinus M := by
    ext e g
    simp [spinAmplitude, Matrix.submatrix_apply, smul_smul, mul_assoc]
  rw [heq, hsSq_smul_real, mul_pow, splitterScale_sq, Real.sq_sqrt ha, noiseMinus_hsSq hM]
  ring

theorem spinAmplitude_hsSq {M : CanonicalEnvironment → Matrix E G ℂ}
    (hM : ImageOrthonormal M) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    hsSq (spinAmplitude p M) = 1 := by
  have ha : 0 ≤ noiseWeight p := by dsimp [noiseWeight]; positivity
  rw [spinAmplitude, hsSq_smul_real, splitterScale_sq, hsSq_fromBlocks,
    coherentPlus_hsSq hM hp0 hp1, coherentMinus_hsSq hM hp0 hp1,
    hsSq_smul_real, hsSq_smul_real, Real.sq_sqrt ha,
    noisePlus_hsSq hM, noiseMinus_hsSq hM]
  dsimp [coherentWeight, noiseWeight]
  ring

def coherentCopyAmplitude (p : ℝ) (M : CanonicalEnvironment → Matrix E G ℂ) :
    Matrix (E ⊕ E) (G ⊕ G) ℂ :=
  (splitterScale : ℝ) • Matrix.fromBlocks
    ((Real.sqrt (vacuumWeight p) : ℝ) • M 0) ((Real.sqrt (noiseWeight p) : ℝ) • M 3)
    ((Real.sqrt (noiseWeight p) : ℝ) • M 3) ((Real.sqrt (vacuumWeight p) : ℝ) • M 0)

theorem coherentCopyAmplitude_hsSq {M : CanonicalEnvironment → Matrix E G ℂ}
    (hM : ImageOrthonormal M) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    hsSq (coherentCopyAmplitude p M) = coherentWeight p := by
  have hF : 0 ≤ vacuumWeight p := by dsimp [vacuumWeight]; linarith
  have ha : 0 ≤ noiseWeight p := by dsimp [noiseWeight]; positivity
  rw [coherentCopyAmplitude, hsSq_smul_real, splitterScale_sq, hsSq_fromBlocks]
  simp only [hsSq_smul_real, Real.sq_sqrt hF, Real.sq_sqrt ha, image_hsSq_one hM]
  dsimp [vacuumWeight, noiseWeight, coherentWeight]
  ring

theorem coherentCopyAmplitude_off_hsSq {M : CanonicalEnvironment → Matrix E G ℂ}
    (hM : ImageOrthonormal M) {p : ℝ} (hp0 : 0 ≤ p) :
    hsSq ((coherentCopyAmplitude p M).submatrix Sum.inl Sum.inr) +
      hsSq ((coherentCopyAmplitude p M).submatrix Sum.inr Sum.inl) = noiseWeight p := by
  have ha : 0 ≤ noiseWeight p := by dsimp [noiseWeight]; positivity
  have h01 : (coherentCopyAmplitude p M).submatrix Sum.inl Sum.inr =
      (splitterScale * Real.sqrt (noiseWeight p) : ℝ) • M 3 := by
    ext e g
    simp [coherentCopyAmplitude, Matrix.submatrix_apply, smul_smul, mul_assoc]
  have h10 : (coherentCopyAmplitude p M).submatrix Sum.inr Sum.inl =
      (splitterScale * Real.sqrt (noiseWeight p) : ℝ) • M 3 := by
    ext e g
    simp [coherentCopyAmplitude, Matrix.submatrix_apply, smul_smul, mul_assoc]
  rw [h01, h10, hsSq_smul_real, mul_pow, splitterScale_sq, Real.sq_sqrt ha, image_hsSq_one hM]
  ring

theorem entropyNat_smul {I : Type*} [Fintype I] [DecidableEq I]
    (c : ℝ) {A : QMatrix I} (hA : A.PosSemidef) :
    entropyNat (c • A) = c * entropyNat A - (c * Real.log c) * A.trace.re := by
  have h := QuantumProver.SuperchannelDiscrimination.FlaggedStates.entropyBits_smul c hA
  rw [QuantumProver.ConditionalEntropy.ConditionalRange.entropyBits_eq_isotropicEntropy_div_log_two,
    QuantumProver.ConditionalEntropy.ConditionalRange.entropyBits_eq_isotropicEntropy_div_log_two] at h
  change entropyNat (c • A) / Real.log 2 =
    c * (entropyNat A / Real.log 2) - (c * Real.log c / Real.log 2) * A.trace.re at h
  have hl : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  field_simp [hl] at h
  simpa only [mul_sub, mul_assoc] using h

theorem entropyNat_blockDiagonal {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] {A : QMatrix I} {B : QMatrix J}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    entropyNat (Matrix.fromBlocks A 0 0 B) = entropyNat A + entropyNat B := by
  have h := QuantumProver.SuperchannelDiscrimination.FlaggedStates.entropyBits_flagBlock hA hB
  rw [QuantumProver.ConditionalEntropy.ConditionalRange.entropyBits_eq_isotropicEntropy_div_log_two,
    QuantumProver.ConditionalEntropy.ConditionalRange.entropyBits_eq_isotropicEntropy_div_log_two,
    QuantumProver.ConditionalEntropy.ConditionalRange.entropyBits_eq_isotropicEntropy_div_log_two] at h
  change entropyNat (Matrix.fromBlocks A 0 0 B) / Real.log 2 =
    entropyNat A / Real.log 2 + entropyNat B / Real.log 2 at h
  have hl : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  field_simp [hl] at h
  exact h

theorem trace_blockDiagonal {I J : Type*} [Fintype I] [Fintype J]
    (A : QMatrix I) (B : QMatrix J) :
    Matrix.trace (Matrix.fromBlocks A 0 0 B) = Matrix.trace A + Matrix.trace B := by
  simp only [Matrix.trace, Matrix.diag_apply, Fintype.sum_sum_type,
    Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₂₂]

def copyHadamard (I : Type*) [DecidableEq I] : QMatrix (I ⊕ I) :=
  (splitterScale : ℝ) • Matrix.fromBlocks
    (1 : QMatrix I) (1 : QMatrix I) (1 : QMatrix I) (-1 : QMatrix I)

theorem copyHadamard_conjTranspose {I : Type*} [DecidableEq I] :
    (copyHadamard I)ᴴ = copyHadamard I := by
  simp only [copyHadamard, Matrix.conjTranspose_smul, star_trivial,
    Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_one, Matrix.conjTranspose_neg]

theorem copyHadamard_gram {I : Type*} [Fintype I] [DecidableEq I] :
    IsIsometry (copyHadamard I) := by
  unfold IsIsometry
  simp only [copyHadamard, Matrix.conjTranspose_smul, star_trivial,
    Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_one, Matrix.conjTranspose_neg,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.fromBlocks_multiply,
    Matrix.one_mul, Matrix.mul_one, Matrix.neg_mul, Matrix.mul_neg,
    neg_neg, add_neg_cancel, neg_add_cancel]
  rw [← pow_two, splitterScale_sq]
  ext i j
  cases i <;> cases j <;>
    norm_num [Matrix.smul_apply, Matrix.add_apply, Matrix.one_apply, Matrix.ofNat_apply]

def symmetricCopyAmplitude (A V : Matrix E G ℂ) : Matrix (E ⊕ E) (G ⊕ G) ℂ :=
  (splitterScale : ℝ) • Matrix.fromBlocks A V V A

theorem coherentCopyAmplitude_eq (p : ℝ) (M : CanonicalEnvironment → Matrix E G ℂ) :
    coherentCopyAmplitude p M = symmetricCopyAmplitude
      ((Real.sqrt (vacuumWeight p) : ℝ) • M 0)
      ((Real.sqrt (noiseWeight p) : ℝ) • M 3) := rfl

theorem symmetricCopyAmplitude_hadamard (A V : Matrix E G ℂ) :
    copyHadamard E * symmetricCopyAmplitude A V * copyHadamard G =
      (splitterScale : ℝ) • Matrix.fromBlocks (A + V) 0 0 (A - V) := by
  have hc3 : (splitterScale : ℂ)^3 = (splitterScale : ℂ)/2 := by
    rw [pow_succ, splitterScale_complex_sq]
    ring
  ext i j
  cases i <;> cases j <;>
    simp [copyHadamard, symmetricCopyAmplitude, Matrix.mul_apply,
      Fintype.sum_sum_type, Matrix.smul_apply, Matrix.one_apply,
      Matrix.add_apply, Matrix.sub_apply, ite_mul, mul_ite, Finset.mul_sum,
      Finset.sum_mul, Complex.real_smul] <;> ring_nf <;> simp [hc3] <;> ring

theorem symmetricCopyAmplitude_leftGram (A V : Matrix E G ℂ) :
    symmetricCopyAmplitude A V * (symmetricCopyAmplitude A V)ᴴ =
      (1/2 : ℝ) • Matrix.fromBlocks
        (A*Aᴴ + V*Vᴴ) (A*Vᴴ + V*Aᴴ) (A*Vᴴ + V*Aᴴ) (A*Aᴴ + V*Vᴴ) := by
  simp only [symmetricCopyAmplitude, Matrix.conjTranspose_smul, star_trivial,
    Matrix.fromBlocks_conjTranspose, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, Matrix.fromBlocks_multiply]
  rw [← pow_two, splitterScale_sq]
  congr 1
  congr 1 <;> abel

theorem symmetricCopyAmplitude_leftPinch (A V : Matrix E G ℂ) :
    binaryPinch (symmetricCopyAmplitude A V * (symmetricCopyAmplitude A V)ᴴ) =
      (1/2 : ℝ) • Matrix.fromBlocks (A*Aᴴ + V*Vᴴ) 0 0 (A*Aᴴ + V*Vᴴ) := by
  rw [symmetricCopyAmplitude_leftGram]
  ext i j
  cases i <;> cases j <;> simp [binaryPinch, Matrix.smul_apply]

theorem scaledBlockDiagonal_leftGram (P Q : Matrix E G ℂ) :
    ((splitterScale : ℝ) • Matrix.fromBlocks P 0 0 Q) *
      ((splitterScale : ℝ) • Matrix.fromBlocks P 0 0 Q)ᴴ =
        (1/2 : ℝ) • Matrix.fromBlocks (P*Pᴴ) 0 0 (Q*Qᴴ) := by
  simp only [Matrix.conjTranspose_smul, star_trivial,
    Matrix.fromBlocks_conjTranspose, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, Matrix.fromBlocks_multiply, Matrix.conjTranspose_zero,
    Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
  rw [← pow_two, splitterScale_sq]

def copyHolevoMassLeft (A V : Matrix E G ℂ) : ℝ :=
  entropyNat (A*Aᴴ + V*Vᴴ) -
    (entropyNat ((A+V)*(A+V)ᴴ) + entropyNat ((A-V)*(A-V)ᴴ)) / 2

def copyHolevoMassRight (A V : Matrix E G ℂ) : ℝ :=
  entropyNat (Aᴴ*A + Vᴴ*V) -
    (entropyNat ((A+V)ᴴ*(A+V)) + entropyNat ((A-V)ᴴ*(A-V))) / 2

theorem symmetricCopyAmplitude_leftCoherence (A V : Matrix E G ℂ) :
    binaryCoherenceNat (symmetricCopyAmplitude A V * (symmetricCopyAmplitude A V)ᴴ) =
      copyHolevoMassLeft A V := by
  let L := symmetricCopyAmplitude A V
  let P := A+V
  let Q := A-V
  let R := A*Aᴴ+V*Vᴴ
  let D := (splitterScale : ℝ) • Matrix.fromBlocks P 0 0 Q
  have hHright : copyHadamard G * (copyHadamard G)ᴴ = 1 := by
    rw [copyHadamard_conjTranspose]
    simpa only [IsIsometry, copyHadamard_conjTranspose] using (copyHadamard_gram (I := G))
  have hdiag : copyHadamard E * L * copyHadamard G = D :=
    symmetricCopyAmplitude_hadamard A V
  have hcong : D*Dᴴ = copyHadamard E * (L*Lᴴ) * (copyHadamard E)ᴴ := by
    rw [← hdiag, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
    calc
      _ = copyHadamard E * L * (copyHadamard G * (copyHadamard G)ᴴ) *
          Lᴴ * (copyHadamard E)ᴴ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hHright, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  have hentropy : entropyNat (L*Lᴴ) =
      entropyNat ((1/2 : ℝ) • Matrix.fromBlocks (P*Pᴴ) 0 0 (Q*Qᴴ)) := by
    calc
      _ = entropyNat (copyHadamard E * (L*Lᴴ) * (copyHadamard E)ᴴ) :=
        (entropyNat_isometric_embedding _ copyHadamard_gram
          (Matrix.posSemidef_self_mul_conjTranspose L).1).symm
      _ = entropyNat (D*Dᴴ) := congrArg entropyNat hcong.symm
      _ = _ := by rw [scaledBlockDiagonal_leftGram]
  have hR : R.PosSemidef :=
    (Matrix.posSemidef_self_mul_conjTranspose A).add (Matrix.posSemidef_self_mul_conjTranspose V)
  have hP : (P*Pᴴ).PosSemidef := Matrix.posSemidef_self_mul_conjTranspose P
  have hQ : (Q*Qᴴ).PosSemidef := Matrix.posSemidef_self_mul_conjTranspose Q
  have hRR : (Matrix.fromBlocks R 0 0 R).PosSemidef :=
    QuantumProver.SuperchannelDiscrimination.FlaggedStates.flagBlock_posSemidef hR hR
  have hPQ : (Matrix.fromBlocks (P*Pᴴ) 0 0 (Q*Qᴴ)).PosSemidef :=
    QuantumProver.SuperchannelDiscrimination.FlaggedStates.flagBlock_posSemidef hP hQ
  have htrace : (Matrix.trace (P*Pᴴ)).re + (Matrix.trace (Q*Qᴴ)).re =
      2 * (Matrix.trace R).re := by
    dsimp [P,Q,R]
    simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_sub,
      Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub,
      Matrix.trace_add, Matrix.trace_sub, Complex.add_re, Complex.sub_re]
    ring
  change entropyNat (binaryPinch (L*Lᴴ)) - entropyNat (L*Lᴴ) = copyHolevoMassLeft A V
  rw [symmetricCopyAmplitude_leftPinch, hentropy,
    entropyNat_smul (1/2) hRR, entropyNat_smul (1/2) hPQ,
    entropyNat_blockDiagonal hR hR, entropyNat_blockDiagonal hP hQ]
  simp only [trace_blockDiagonal, Complex.add_re]
  rw [htrace]
  dsimp [copyHolevoMassLeft,P,Q,R]
  ring

theorem symmetricCopyAmplitude_conjTranspose (A V : Matrix E G ℂ) :
    (symmetricCopyAmplitude A V)ᴴ = symmetricCopyAmplitude Aᴴ Vᴴ := by
  simp only [symmetricCopyAmplitude, Matrix.conjTranspose_smul, star_trivial,
    Matrix.fromBlocks_conjTranspose]

theorem symmetricCopyAmplitude_rightCoherence (A V : Matrix E G ℂ) :
    binaryCoherenceNat ((symmetricCopyAmplitude A V)ᴴ * symmetricCopyAmplitude A V) =
      copyHolevoMassRight A V := by
  have h := symmetricCopyAmplitude_leftCoherence Aᴴ Vᴴ
  rw [← symmetricCopyAmplitude_conjTranspose, Matrix.conjTranspose_conjTranspose] at h
  simpa only [copyHolevoMassLeft,copyHolevoMassRight,Matrix.conjTranspose_add,
    Matrix.conjTranspose_sub,Matrix.conjTranspose_conjTranspose] using h

def binaryHolevoBits {I : Type*} [Fintype I] [DecidableEq I] (R S : QMatrix I) : ℝ :=
  QuantumProver.ConditionalEntropy.entropyBits (QuantumProver.ConditionalEntropy.mix (1/2) R S) -
    (QuantumProver.ConditionalEntropy.entropyBits R + QuantumProver.ConditionalEntropy.entropyBits S)/2

def binaryHolevoNat {I : Type*} [Fintype I] [DecidableEq I] (R S : QMatrix I) : ℝ :=
  entropyNat (QuantumProver.ConditionalEntropy.mix (1/2) R S) - (entropyNat R + entropyNat S)/2

theorem binaryHolevoBits_eq_nat {I : Type*} [Fintype I] [DecidableEq I] (R S : QMatrix I) :
    binaryHolevoBits R S = binaryHolevoNat R S / Real.log 2 := by
  unfold binaryHolevoBits binaryHolevoNat
  change QuantumProver.SuperchannelDiscrimination.FlaggedStates.entropyBits
      (QuantumProver.ConditionalEntropy.mix (1/2) R S) -
      (QuantumProver.SuperchannelDiscrimination.FlaggedStates.entropyBits R +
        QuantumProver.SuperchannelDiscrimination.FlaggedStates.entropyBits S)/2 = _
  rw [QuantumProver.ConditionalEntropy.ConditionalRange.entropyBits_eq_isotropicEntropy_div_log_two,
    QuantumProver.ConditionalEntropy.ConditionalRange.entropyBits_eq_isotropicEntropy_div_log_two,
    QuantumProver.ConditionalEntropy.ConditionalRange.entropyBits_eq_isotropicEntropy_div_log_two]
  change entropyNat (QuantumProver.ConditionalEntropy.mix (1/2) R S)/Real.log 2 -
    (entropyNat R/Real.log 2 + entropyNat S/Real.log 2)/2 = _
  ring

theorem binaryEntropy_half : QuantumProver.ConditionalEntropy.binaryEntropy (1/2) = 1 := by
  have hl : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  norm_num [QuantumProver.ConditionalEntropy.binaryEntropy,
    QuantumProver.SuperchannelDiscrimination.FlaggedStates.flagEntropyBits, Real.log_div]
  field_simp [hl]
  ring

theorem binaryHolevoBits_bounds {I : Type*} [Fintype I] [DecidableEq I]
    {R S : QMatrix I} (hR : QuantumProver.ConditionalEntropy.IsDensity R)
    (hS : QuantumProver.ConditionalEntropy.IsDensity S) :
    0 ≤ binaryHolevoBits R S ∧ binaryHolevoBits R S ≤ 1 := by
  have hL := QuantumProver.ConditionalEntropy.entropyBits_mix_lower hR hS
    (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (1/2 : ℝ) ≤ 1)
  have hU := QuantumProver.ConditionalEntropy.entropyBits_mix_upper hR hS
    (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (1/2 : ℝ) ≤ 1)
  rw [binaryEntropy_half] at hU
  unfold binaryHolevoBits
  constructor <;> linarith only [hL,hU]

theorem binaryHolevoNat_bounds {I : Type*} [Fintype I] [DecidableEq I]
    {R S : QMatrix I} (hR : QuantumProver.ConditionalEntropy.IsDensity R)
    (hS : QuantumProver.ConditionalEntropy.IsDensity S) :
    0 ≤ binaryHolevoNat R S ∧ binaryHolevoNat R S ≤ Real.log 2 := by
  have h := binaryHolevoBits_bounds hR hS
  rw [binaryHolevoBits_eq_nat] at h
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  constructor
  · have hp := mul_nonneg h.1 hl.le
    simpa only [div_mul_cancel₀ _ hl.ne'] using hp
  · exact (div_le_one hl).mp h.2

theorem conditionalFirstFlagged_half {I : Type*} [Fintype I] [DecidableEq I]
    {R S : QMatrix I} (hR : QuantumProver.ConditionalEntropy.IsDensity R)
    (hS : QuantumProver.ConditionalEntropy.IsDensity S) :
    QuantumProver.ConditionalEntropy.conditionalEntropyBits
      (QuantumProver.ConditionalEntropy.MixtureEntropy.firstFlagged (1/2) R S) =
        1 - binaryHolevoBits R S := by
  rw [QuantumProver.ConditionalEntropy.MixtureEntropy.conditionalEntropy_firstFlagged
    (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (1/2 : ℝ) ≤ 1) hR hS,
    binaryEntropy_half]
  unfold binaryHolevoBits
  ring

theorem firstFlagged_mix_commute {I : Type*} [Fintype I] [DecidableEq I]
    (p t : ℝ) (R0 R1 S0 S1 : QMatrix I) :
    QuantumProver.ConditionalEntropy.mix t
      (QuantumProver.ConditionalEntropy.MixtureEntropy.firstFlagged p R0 R1)
      (QuantumProver.ConditionalEntropy.MixtureEntropy.firstFlagged p S0 S1) =
    QuantumProver.ConditionalEntropy.MixtureEntropy.firstFlagged p
      (QuantumProver.ConditionalEntropy.mix t R0 S0) (QuantumProver.ConditionalEntropy.mix t R1 S1) := by
  ext ⟨b,i⟩ ⟨c,j⟩
  cases b <;> cases c <;>
    simp [QuantumProver.ConditionalEntropy.mix, QuantumProver.ConditionalEntropy.MixtureEntropy.firstFlagged,
      Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.smul_apply, Matrix.add_apply,
      Complex.real_smul] <;> ring

theorem binaryHolevoBits_mix_upper {I : Type*} [Fintype I] [DecidableEq I]
    {R0 R1 S0 S1 : QMatrix I}
    (hR0 : QuantumProver.ConditionalEntropy.IsDensity R0)
    (hR1 : QuantumProver.ConditionalEntropy.IsDensity R1)
    (hS0 : QuantumProver.ConditionalEntropy.IsDensity S0)
    (hS1 : QuantumProver.ConditionalEntropy.IsDensity S1)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    binaryHolevoBits (QuantumProver.ConditionalEntropy.mix t R0 S0)
      (QuantumProver.ConditionalEntropy.mix t R1 S1) ≤
        (1-t) * binaryHolevoBits R0 R1 + t * binaryHolevoBits S0 S1 := by
  have hR := QuantumProver.ConditionalEntropy.MixtureEntropy.firstFlagged_isDensity
    (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (1/2 : ℝ) ≤ 1) hR0 hR1
  have hS := QuantumProver.ConditionalEntropy.MixtureEntropy.firstFlagged_isDensity
    (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (1/2 : ℝ) ≤ 1) hS0 hS1
  have h0 := QuantumProver.ConditionalEntropy.mix_isDensity hR0 hS0 ht0 ht1
  have h1 := QuantumProver.ConditionalEntropy.mix_isDensity hR1 hS1 ht0 ht1
  have hc := QuantumProver.ConditionalEntropy.conditionalEntropy_mix_lower hR hS ht0 ht1
  rw [firstFlagged_mix_commute, conditionalFirstFlagged_half hR0 hR1,
    conditionalFirstFlagged_half hS0 hS1, conditionalFirstFlagged_half h0 h1] at hc
  nlinarith only [hc]

theorem binaryHolevoNat_mix_upper {I : Type*} [Fintype I] [DecidableEq I]
    {R0 R1 S0 S1 : QMatrix I}
    (hR0 : QuantumProver.ConditionalEntropy.IsDensity R0)
    (hR1 : QuantumProver.ConditionalEntropy.IsDensity R1)
    (hS0 : QuantumProver.ConditionalEntropy.IsDensity S0)
    (hS1 : QuantumProver.ConditionalEntropy.IsDensity S1)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    binaryHolevoNat (QuantumProver.ConditionalEntropy.mix t R0 S0)
      (QuantumProver.ConditionalEntropy.mix t R1 S1) ≤
        (1-t) * binaryHolevoNat R0 R1 + t * binaryHolevoNat S0 S1 := by
  have h := binaryHolevoBits_mix_upper hR0 hR1 hS0 hS1 ht0 ht1
  simp only [binaryHolevoBits_eq_nat] at h
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  calc
    _ = (binaryHolevoNat (QuantumProver.ConditionalEntropy.mix t R0 S0)
      (QuantumProver.ConditionalEntropy.mix t R1 S1) / Real.log 2) * Real.log 2 :=
        (div_mul_cancel₀ _ hl.ne').symm
    _ ≤ ((1-t) * (binaryHolevoNat R0 R1 / Real.log 2) +
      t * (binaryHolevoNat S0 S1 / Real.log 2)) * Real.log 2 :=
        mul_le_mul_of_nonneg_right h hl.le
    _ = _ := by field_simp [hl.ne'] <;> ring

def normalizedGram (w : ℝ) (T : Matrix E G ℂ) : QMatrix E :=
  w⁻¹ • (T*Tᴴ)

theorem leftGram_trace (T : Matrix E G ℂ) :
    Matrix.trace (T*Tᴴ) = (hsSq T : ℂ) := by
  have h := Complex.eq_re_of_ofReal_le
    (Matrix.posSemidef_self_mul_conjTranspose T).trace_nonneg
  calc
    Matrix.trace (T*Tᴴ) = ((Matrix.trace (T*Tᴴ)).re : ℂ) := h
    _ = _ := by rw [Matrix.trace_mul_comm]; rfl

theorem normalizedGram_isDensity (T : Matrix E G ℂ) {w : ℝ}
    (hw : 0 < w) (hT : hsSq T = w) :
    QuantumProver.ConditionalEntropy.IsDensity (normalizedGram w T) := by
  constructor
  · exact (Matrix.posSemidef_self_mul_conjTranspose T).smul (inv_nonneg.mpr hw.le)
  · rw [normalizedGram, Matrix.trace_smul, leftGram_trace, hT]
    simp [Complex.real_smul, ← Complex.ofReal_mul, hw.ne']

theorem mix_smul {I : Type*} (c t : ℝ) (R S : QMatrix I) :
    QuantumProver.ConditionalEntropy.mix t (c • R) (c • S) =
      c • QuantumProver.ConditionalEntropy.mix t R S := by
  ext i j
  simp [QuantumProver.ConditionalEntropy.mix, Matrix.smul_apply, Matrix.add_apply,
    Complex.real_smul]
  ring

theorem binaryHolevoNat_smul {I : Type*} [Fintype I] [DecidableEq I]
    {R S : QMatrix I} (hR : R.PosSemidef) (hS : S.PosSemidef) (c : ℝ) :
    binaryHolevoNat (c • R) (c • S) = c * binaryHolevoNat R S := by
  have hm : (QuantumProver.ConditionalEntropy.mix (1/2) R S).PosSemidef :=
    (hR.smul (by norm_num : (0:ℝ) ≤ 1-1/2)).add
      (hS.smul (by norm_num : (0:ℝ) ≤ 1/2))
  unfold binaryHolevoNat
  rw [mix_smul, entropyNat_smul c hm, entropyNat_smul c hR, entropyNat_smul c hS]
  simp only [QuantumProver.ConditionalEntropy.mix, Matrix.trace_add, Matrix.trace_smul,
    Complex.add_re, Complex.smul_re]
  ring

theorem binaryHolevoNat_transpose {I : Type*} [Fintype I] [DecidableEq I]
    {R S : QMatrix I} (hR : R.PosSemidef) (hS : S.PosSemidef) :
    binaryHolevoNat R.transpose S.transpose = binaryHolevoNat R S := by
  have hm : (QuantumProver.ConditionalEntropy.mix (1/2) R S).PosSemidef :=
    (hR.smul (by norm_num : (0:ℝ) ≤ 1-1/2)).add
      (hS.smul (by norm_num : (0:ℝ) ≤ 1/2))
  have he : QuantumProver.ConditionalEntropy.mix (1/2) R.transpose S.transpose =
      (QuantumProver.ConditionalEntropy.mix (1/2) R S).transpose := by
    ext i j
    rfl
  unfold binaryHolevoNat
  rw [he, entropyNat_transpose hm.1, entropyNat_transpose hR.1, entropyNat_transpose hS.1]

theorem coherentPair_average_left (A V : Matrix E G ℂ) :
    QuantumProver.ConditionalEntropy.mix (1/2) ((A+V)*(A+V)ᴴ) ((A-V)*(A-V)ᴴ) =
      A*Aᴴ+V*Vᴴ := by
  simp only [QuantumProver.ConditionalEntropy.mix, Matrix.conjTranspose_add,
    Matrix.conjTranspose_sub, Matrix.add_mul, Matrix.mul_add,
    Matrix.sub_mul, Matrix.mul_sub]
  module

theorem copyHolevoMassLeft_eq_holevo (A V : Matrix E G ℂ) :
    copyHolevoMassLeft A V = binaryHolevoNat ((A+V)*(A+V)ᴴ) ((A-V)*(A-V)ᴴ) := by
  rw [binaryHolevoNat, coherentPair_average_left]
  rfl

theorem copyHolevoMassLeft_eq_normalized (A V : Matrix E G ℂ)
    {w : ℝ} (hw : 0 < w) :
    copyHolevoMassLeft A V = w * binaryHolevoNat
      (normalizedGram w (A+V)) (normalizedGram w (A-V)) := by
  rw [copyHolevoMassLeft_eq_holevo]
  have h := binaryHolevoNat_smul
    ((Matrix.posSemidef_self_mul_conjTranspose (A+V)).smul (inv_nonneg.mpr hw.le))
    ((Matrix.posSemidef_self_mul_conjTranspose (A-V)).smul (inv_nonneg.mpr hw.le)) w
  simpa only [normalizedGram, smul_smul, mul_inv_cancel₀ hw.ne', one_smul] using h

theorem coherentWeight_pos {p : ℝ} (hp1 : p ≤ 1) : 0 < coherentWeight p := by
  dsimp [coherentWeight]
  linarith

theorem coherentPlus_normalized_isDensity
    {M : CanonicalEnvironment → Matrix E G ℂ} (hM : ImageOrthonormal M)
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    QuantumProver.ConditionalEntropy.IsDensity
      (normalizedGram (coherentWeight p) (coherentPlus p M)) :=
  normalizedGram_isDensity _ (coherentWeight_pos hp1) (coherentPlus_hsSq hM hp0 hp1)

theorem coherentMinus_normalized_isDensity
    {M : CanonicalEnvironment → Matrix E G ℂ} (hM : ImageOrthonormal M)
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    QuantumProver.ConditionalEntropy.IsDensity
      (normalizedGram (coherentWeight p) (coherentMinus p M)) :=
  normalizedGram_isDensity _ (coherentWeight_pos hp1) (coherentMinus_hsSq hM hp0 hp1)

theorem noisePlus_normalized_isDensity
    {M : CanonicalEnvironment → Matrix E G ℂ} (hM : ImageOrthonormal M) :
    QuantumProver.ConditionalEntropy.IsDensity (normalizedGram 2 (noisePlus M)) :=
  normalizedGram_isDensity _ (by norm_num) (noisePlus_hsSq hM)

theorem noiseMinus_normalized_isDensity
    {M : CanonicalEnvironment → Matrix E G ℂ} (hM : ImageOrthonormal M) :
    QuantumProver.ConditionalEntropy.IsDensity (normalizedGram 2 (noiseMinus M)) :=
  normalizedGram_isDensity _ (by norm_num) (noiseMinus_hsSq hM)

section RectangularDilation

variable {I0 I1 J0 J1 : Type*}
  [Fintype I0] [Fintype I1] [Fintype J0] [Fintype J1]
  [DecidableEq I0] [DecidableEq I1] [DecidableEq J0] [DecidableEq J1]

def sectorRegroup : ((I0 ⊕ I1) ⊕ (J0 ⊕ J1)) ≃ ((I0 ⊕ J0) ⊕ (I1 ⊕ J1)) where
  toFun
    | Sum.inl (Sum.inl i) => Sum.inl (Sum.inl i)
    | Sum.inl (Sum.inr i) => Sum.inr (Sum.inl i)
    | Sum.inr (Sum.inl j) => Sum.inl (Sum.inr j)
    | Sum.inr (Sum.inr j) => Sum.inr (Sum.inr j)
  invFun
    | Sum.inl (Sum.inl i) => Sum.inl (Sum.inl i)
    | Sum.inl (Sum.inr j) => Sum.inr (Sum.inl j)
    | Sum.inr (Sum.inl i) => Sum.inl (Sum.inr i)
    | Sum.inr (Sum.inr j) => Sum.inr (Sum.inr j)
  left_inv := by rintro ((i|i)|(j|j)) <;> rfl
  right_inv := by rintro ((i|j)|(i|j)) <;> rfl

def hermitianDilation {I J : Type*} (T : Matrix I J ℂ) : QMatrix (I ⊕ J) :=
  Matrix.fromBlocks 0 T Tᴴ 0

theorem hermitianDilation_isHermitian {I J : Type*} (T : Matrix I J ℂ) :
    (hermitianDilation T).IsHermitian :=
  Matrix.IsHermitian.fromBlocks Matrix.isHermitian_zero (by simp) Matrix.isHermitian_zero

def groupedDilation (T : Matrix (I0 ⊕ I1) (J0 ⊕ J1) ℂ) :
    QMatrix ((I0 ⊕ J0) ⊕ (I1 ⊕ J1)) :=
  Matrix.reindex sectorRegroup sectorRegroup (hermitianDilation T)

theorem groupedDilation_isHermitian (T : Matrix (I0 ⊕ I1) (J0 ⊕ J1) ℂ) :
    (groupedDilation T).IsHermitian :=
  (hermitianDilation_isHermitian T).submatrix sectorRegroup.symm

theorem hermitianDilation_square {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (T : Matrix I J ℂ) :
    hermitianDilation T * hermitianDilation T =
      Matrix.fromBlocks (T*Tᴴ) 0 0 (Tᴴ*T) := by
  simp [hermitianDilation, Matrix.fromBlocks_multiply]

theorem groupedDilation_square (T : Matrix (I0 ⊕ I1) (J0 ⊕ J1) ℂ) :
    groupedDilation T * groupedDilation T =
      Matrix.reindex sectorRegroup sectorRegroup
        (Matrix.fromBlocks (T*Tᴴ) 0 0 (Tᴴ*T)) := by
  rw [groupedDilation]
  change (Matrix.reindexAlgEquiv ℝ ℂ sectorRegroup) (hermitianDilation T) *
    (Matrix.reindexAlgEquiv ℝ ℂ sectorRegroup) (hermitianDilation T) = _
  rw [← map_mul, hermitianDilation_square]
  rfl

theorem binaryPinch_blockDiagonal (R : QMatrix (I0 ⊕ I1))
    (S : QMatrix (J0 ⊕ J1)) :
    binaryPinch (Matrix.reindex sectorRegroup sectorRegroup
      (Matrix.fromBlocks R 0 0 S)) =
    Matrix.reindex sectorRegroup sectorRegroup
      (Matrix.fromBlocks (binaryPinch R) 0 0 (binaryPinch S)) := by
  ext x y
  rcases x with (a|b)|(c|d) <;> rcases y with (e|f)|(g|h) <;> rfl

theorem binaryPinch_posSemidef {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] {R : QMatrix (I ⊕ J)}
    (hR : R.PosSemidef) : (binaryPinch R).PosSemidef := by
  have he : binaryPinch R = Matrix.fromBlocks
      (R.submatrix Sum.inl Sum.inl) 0 0 (R.submatrix Sum.inr Sum.inr) := by
    ext i j
    cases i <;> cases j <;> rfl
  rw [he]
  exact QuantumProver.SuperchannelDiscrimination.FlaggedStates.flagBlock_posSemidef
    (hR.submatrix Sum.inl) (hR.submatrix Sum.inr)

theorem entropyNat_reindex {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (e : I ≃ J) {R : QMatrix I}
    (hR : R.IsHermitian) : entropyNat (Matrix.reindex e e R) = entropyNat R := by
  have h := QuantumProver.ConditionalEntropy.MixtureEntropy.entropyBits_reindex e hR
  change QuantumProver.SuperchannelDiscrimination.FlaggedStates.entropyBits (Matrix.reindex e e R) =
    QuantumProver.SuperchannelDiscrimination.FlaggedStates.entropyBits R at h
  rw [QuantumProver.ConditionalEntropy.ConditionalRange.entropyBits_eq_isotropicEntropy_div_log_two,
    QuantumProver.ConditionalEntropy.ConditionalRange.entropyBits_eq_isotropicEntropy_div_log_two] at h
  change entropyNat (Matrix.reindex e e R)/Real.log 2 = entropyNat R/Real.log 2 at h
  have hl : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  field_simp [hl] at h
  exact h

theorem groupedDilation_square_coherence (T : Matrix (I0 ⊕ I1) (J0 ⊕ J1) ℂ) :
    binaryCoherenceNat (groupedDilation T * groupedDilation T) =
      binaryCoherenceNat (T*Tᴴ) + binaryCoherenceNat (Tᴴ*T) := by
  have hR := Matrix.posSemidef_self_mul_conjTranspose T
  have hS := Matrix.posSemidef_conjTranspose_mul_self T
  have hpR := binaryPinch_posSemidef hR
  have hpS := binaryPinch_posSemidef hS
  have hd : (Matrix.fromBlocks (T*Tᴴ) 0 0 (Tᴴ*T)).PosSemidef :=
    QuantumProver.SuperchannelDiscrimination.FlaggedStates.flagBlock_posSemidef hR hS
  have hpd : (Matrix.fromBlocks (binaryPinch (T*Tᴴ)) 0 0
      (binaryPinch (Tᴴ*T))).PosSemidef :=
    QuantumProver.SuperchannelDiscrimination.FlaggedStates.flagBlock_posSemidef hpR hpS
  rw [binaryCoherenceNat, groupedDilation_square, binaryPinch_blockDiagonal,
    entropyNat_reindex sectorRegroup hpd.1, entropyNat_reindex sectorRegroup hd.1,
    entropyNat_blockDiagonal hpR hpS, entropyNat_blockDiagonal hR hS]
  unfold binaryCoherenceNat
  ring

theorem groupedDilation_eq_binary (T : Matrix (I0 ⊕ I1) (J0 ⊕ J1) ℂ) :
    groupedDilation T = c1Binary
      (hermitianDilation (T.submatrix Sum.inl Sum.inl))
      (hermitianDilation (T.submatrix Sum.inr Sum.inr))
      (Matrix.fromBlocks 0 (T.submatrix Sum.inr Sum.inl)
        (T.submatrix Sum.inl Sum.inr)ᴴ 0) := by
  ext x y
  rcases x with (a|b)|(c|d) <;> rcases y with (e|f)|(g|h) <;>
    simp [groupedDilation, sectorRegroup, hermitianDilation, c1Binary,
      Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.conjTranspose_apply]

theorem hsSq_conjTranspose (T : Matrix E G ℂ) : hsSq Tᴴ = hsSq T := by
  simp only [hsSq, c1_trace_gram, c1HsMass_conjTranspose]

theorem groupedDilation_noise_budget (T : Matrix (I0 ⊕ I1) (J0 ⊕ J1) ℂ) :
    hsSq (Matrix.fromBlocks 0 (T.submatrix Sum.inr Sum.inl)
      (T.submatrix Sum.inl Sum.inr)ᴴ 0) =
        hsSq (T.submatrix Sum.inl Sum.inr) + hsSq (T.submatrix Sum.inr Sum.inl) := by
  rw [hsSq_fromBlocks, hsSq_conjTranspose]
  simp only [hsSq, Matrix.conjTranspose_zero, Matrix.zero_mul, Matrix.trace_zero,
    Complex.zero_re]
  ring

theorem groupedDilation_trace_budget (T : Matrix (I0 ⊕ I1) (J0 ⊕ J1) ℂ) :
    (Matrix.trace (groupedDilation T * groupedDilation T)).re = 2*hsSq T := by
  rw [groupedDilation_square, QuantumProver.ConditionalEntropy.MixtureEntropy.trace_reindex,
    trace_blockDiagonal, Complex.add_re, leftGram_trace, Complex.ofReal_re]
  unfold hsSq
  ring

end RectangularDilation

theorem weightedGram_as_mix (P N : Matrix E G ℂ) {w a : ℝ}
    (hw : 0 < w) (hweights : w+2*a=1) :
    P*Pᴴ+a • (N*Nᴴ) = QuantumProver.ConditionalEntropy.mix (2*a)
      (normalizedGram w P) (normalizedGram 2 N) := by
  have he : 1-2*a=w := by linarith
  rw [QuantumProver.ConditionalEntropy.mix, normalizedGram, normalizedGram,
    he, smul_smul, mul_inv_cancel₀ hw.ne', one_smul, smul_smul]
  have he2 : 2*a*(2:ℝ)⁻¹=a := by ring
  rw [he2]

theorem weightedGram_isDensity (P N : Matrix E G ℂ) {w a : ℝ}
    (hw : 0 < w) (ha : 0 ≤ a) (hweights : w+2*a=1)
    (hP : hsSq P=w) (hN : hsSq N=2) :
    QuantumProver.ConditionalEntropy.IsDensity (P*Pᴴ+a • (N*Nᴴ)) := by
  rw [weightedGram_as_mix P N hw hweights]
  exact QuantumProver.ConditionalEntropy.mix_isDensity
    (normalizedGram_isDensity P hw hP)
    (normalizedGram_isDensity N (by norm_num) hN)
    (by positivity) (by linarith)

theorem weightedGram_holevo_upper (P Q N O : Matrix E G ℂ) {w a : ℝ}
    (hw : 0 < w) (ha : 0 ≤ a) (hweights : w+2*a=1)
    (hP : hsSq P=w) (hQ : hsSq Q=w) (hN : hsSq N=2) (hO : hsSq O=2) :
    binaryHolevoNat (P*Pᴴ+a • (N*Nᴴ)) (Q*Qᴴ+a • (O*Oᴴ)) ≤
      w * binaryHolevoNat (normalizedGram w P) (normalizedGram w Q) +
        2*a*Real.log 2 := by
  have hdP := normalizedGram_isDensity P hw hP
  have hdQ := normalizedGram_isDensity Q hw hQ
  have hdN := normalizedGram_isDensity N (by norm_num : (0:ℝ)<2) hN
  have hdO := normalizedGram_isDensity O (by norm_num : (0:ℝ)<2) hO
  have hm := binaryHolevoNat_mix_upper hdP hdQ hdN hdO
    (by positivity : (0:ℝ) ≤ 2*a) (by linarith : 2*a ≤ 1)
  have hn := (binaryHolevoNat_bounds hdN hdO).2
  have he : 1-2*a=w := by linarith
  rw [← weightedGram_as_mix P N hw hweights, ← weightedGram_as_mix Q O hw hweights,
    he] at hm
  have hn' := mul_le_mul_of_nonneg_left hn (by positivity : (0:ℝ) ≤ 2*a)
  linarith only [hm,hn']

def coherentHolevoLeft (p : ℝ) (M : CanonicalEnvironment → Matrix E G ℂ) : ℝ :=
  binaryHolevoNat (normalizedGram (coherentWeight p) (coherentPlus p M))
    (normalizedGram (coherentWeight p) (coherentMinus p M))

def coherentHolevoRight (p : ℝ) (M : CanonicalEnvironment → Matrix E G ℂ) : ℝ :=
  binaryHolevoNat (normalizedGram (coherentWeight p) (coherentPlus p M)ᴴ)
    (normalizedGram (coherentWeight p) (coherentMinus p M)ᴴ)

def classicalHolevoLeft (p : ℝ) (M : CanonicalEnvironment → Matrix E G ℂ) : ℝ :=
  binaryHolevoNat
    (coherentPlus p M*(coherentPlus p M)ᴴ+noiseWeight p • (noisePlus M*(noisePlus M)ᴴ))
    (coherentMinus p M*(coherentMinus p M)ᴴ+noiseWeight p • (noiseMinus M*(noiseMinus M)ᴴ))

def classicalHolevoRight (p : ℝ) (M : CanonicalEnvironment → Matrix E G ℂ) : ℝ :=
  binaryHolevoNat
    ((coherentPlus p M)ᴴ*coherentPlus p M+noiseWeight p • ((noiseMinus M)ᴴ*noiseMinus M))
    ((coherentMinus p M)ᴴ*coherentMinus p M+noiseWeight p • ((noisePlus M)ᴴ*noisePlus M))

theorem physical_weights (p : ℝ) : coherentWeight p+2*noiseWeight p=1 := by
  dsimp [coherentWeight,noiseWeight]
  ring

theorem classicalHolevoLeft_upper {M : CanonicalEnvironment → Matrix E G ℂ}
    (hM : ImageOrthonormal M) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    classicalHolevoLeft p M ≤ coherentWeight p * coherentHolevoLeft p M +
      2*noiseWeight p*Real.log 2 :=
  weightedGram_holevo_upper (coherentPlus p M) (coherentMinus p M) (noisePlus M) (noiseMinus M)
    (coherentWeight_pos hp1) (by dsimp [noiseWeight]; positivity) (physical_weights p)
    (coherentPlus_hsSq hM hp0 hp1) (coherentMinus_hsSq hM hp0 hp1)
    (noisePlus_hsSq hM) (noiseMinus_hsSq hM)

theorem classicalHolevoRight_upper {M : CanonicalEnvironment → Matrix E G ℂ}
    (hM : ImageOrthonormal M) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    classicalHolevoRight p M ≤ coherentWeight p * coherentHolevoRight p M +
      2*noiseWeight p*Real.log 2 := by
  have h := weightedGram_holevo_upper (coherentPlus p M)ᴴ (coherentMinus p M)ᴴ
    (noiseMinus M)ᴴ (noisePlus M)ᴴ
    (coherentWeight_pos hp1) (by dsimp [noiseWeight]; positivity) (physical_weights p)
    (by rw [hsSq_conjTranspose]; exact coherentPlus_hsSq hM hp0 hp1)
    (by rw [hsSq_conjTranspose]; exact coherentMinus_hsSq hM hp0 hp1)
    (by rw [hsSq_conjTranspose]; exact noiseMinus_hsSq hM)
    (by rw [hsSq_conjTranspose]; exact noisePlus_hsSq hM)
  simpa only [classicalHolevoRight,coherentHolevoRight,
    Matrix.conjTranspose_conjTranspose] using h

theorem normalizedGram_transpose (w : ℝ) (T : Matrix E G ℂ) :
    normalizedGram w T.transpose = (normalizedGram w Tᴴ).transpose := by
  simp only [normalizedGram, Matrix.conjTranspose_conjTranspose,
    Matrix.transpose_smul, Matrix.transpose_mul]
  rfl

theorem coherentHolevoLeft_transpose (p : ℝ) (M : CanonicalEnvironment → Matrix E G ℂ)
    (hp1 : p ≤ 1) :
    coherentHolevoLeft p (fun i => (M i).transpose) = coherentHolevoRight p M := by
  have hP : coherentPlus p (fun i => (M i).transpose) = (coherentPlus p M).transpose := rfl
  have hQ : coherentMinus p (fun i => (M i).transpose) = (coherentMinus p M).transpose := rfl
  unfold coherentHolevoLeft coherentHolevoRight
  rw [hP,hQ,normalizedGram_transpose,normalizedGram_transpose]
  apply binaryHolevoNat_transpose
  · exact (Matrix.posSemidef_self_mul_conjTranspose (coherentPlus p M)ᴴ).smul
      (inv_nonneg.mpr (coherentWeight_pos hp1).le)
  · exact (Matrix.posSemidef_self_mul_conjTranspose (coherentMinus p M)ᴴ).smul
      (inv_nonneg.mpr (coherentWeight_pos hp1).le)

theorem coherentHolevoRight_transpose (p : ℝ) (M : CanonicalEnvironment → Matrix E G ℂ)
    (hp1 : p ≤ 1) :
    coherentHolevoRight p (fun i => (M i).transpose) = coherentHolevoLeft p M := by
  have h := coherentHolevoLeft_transpose p (fun i => (M i).transpose) hp1
  simpa only [Matrix.transpose_transpose] using h.symm

def fourClassicalHolevo (p : ℝ) (M : CanonicalEnvironment → Matrix E G ℂ) : ℝ :=
  classicalHolevoLeft p M+classicalHolevoRight p M+
    classicalHolevoLeft p (fun i => (M i).transpose)+
    classicalHolevoRight p (fun i => (M i).transpose)

theorem fourClassicalHolevo_upper {M : CanonicalEnvironment → Matrix E G ℂ}
    (hM : ImageOrthonormal M) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    fourClassicalHolevo p M ≤
      2*coherentWeight p*(coherentHolevoLeft p M+coherentHolevoRight p M)+
        8*noiseWeight p*Real.log 2 := by
  have ht := images_transpose_orthonormal hM
  have h0 := classicalHolevoLeft_upper hM hp0 hp1
  have h1 := classicalHolevoRight_upper hM hp0 hp1
  have h2 := classicalHolevoLeft_upper ht hp0 hp1
  have h3 := classicalHolevoRight_upper ht hp0 hp1
  rw [coherentHolevoLeft_transpose p M hp1] at h2
  rw [coherentHolevoRight_transpose p M hp1] at h3
  unfold fourClassicalHolevo
  linarith only [h0,h1,h2,h3]

theorem copyHolevoMassRight_eq_normalized (A V : Matrix E G ℂ)
    {w : ℝ} (hw : 0 < w) :
    copyHolevoMassRight A V = w * binaryHolevoNat
      (normalizedGram w (A+V)ᴴ) (normalizedGram w (A-V)ᴴ) := by
  have h := copyHolevoMassLeft_eq_normalized Aᴴ Vᴴ hw
  simpa only [copyHolevoMassLeft,copyHolevoMassRight,Matrix.conjTranspose_conjTranspose,
    Matrix.conjTranspose_add,Matrix.conjTranspose_sub] using h

theorem coherentCopyAmplitude_eq_complex (p : ℝ)
    (M : CanonicalEnvironment → Matrix E G ℂ) :
    coherentCopyAmplitude p M = symmetricCopyAmplitude
      ((Real.sqrt (vacuumWeight p) : ℂ) • M 0)
      ((Real.sqrt (noiseWeight p) : ℂ) • M 3) := by
  ext i j
  cases i <;> cases j <;>
    simp [coherentCopyAmplitude,symmetricCopyAmplitude,Matrix.smul_apply,Complex.real_smul]

theorem coherentCopyAmplitude_leftCoherence (p : ℝ)
    (M : CanonicalEnvironment → Matrix E G ℂ) (hp1 : p ≤ 1) :
    binaryCoherenceNat (coherentCopyAmplitude p M*(coherentCopyAmplitude p M)ᴴ) =
      coherentWeight p*coherentHolevoLeft p M := by
  rw [coherentCopyAmplitude_eq_complex, symmetricCopyAmplitude_leftCoherence,
    copyHolevoMassLeft_eq_normalized _ _ (coherentWeight_pos hp1)]
  rfl

theorem coherentCopyAmplitude_rightCoherence (p : ℝ)
    (M : CanonicalEnvironment → Matrix E G ℂ) (hp1 : p ≤ 1) :
    binaryCoherenceNat ((coherentCopyAmplitude p M)ᴴ*coherentCopyAmplitude p M) =
      coherentWeight p*coherentHolevoRight p M := by
  rw [coherentCopyAmplitude_eq_complex, symmetricCopyAmplitude_rightCoherence,
    copyHolevoMassRight_eq_normalized _ _ (coherentWeight_pos hp1)]
  rfl

def spinLeftPlus (p : ℝ) (M : CanonicalEnvironment → Matrix E G ℂ) : QMatrix E :=
  coherentPlus p M*(coherentPlus p M)ᴴ+noiseWeight p • (noisePlus M*(noisePlus M)ᴴ)

def spinLeftMinus (p : ℝ) (M : CanonicalEnvironment → Matrix E G ℂ) : QMatrix E :=
  coherentMinus p M*(coherentMinus p M)ᴴ+noiseWeight p • (noiseMinus M*(noiseMinus M)ᴴ)

def spinRightPlus (p : ℝ) (M : CanonicalEnvironment → Matrix E G ℂ) : QMatrix G :=
  (coherentPlus p M)ᴴ*coherentPlus p M+noiseWeight p • ((noiseMinus M)ᴴ*noiseMinus M)

def spinRightMinus (p : ℝ) (M : CanonicalEnvironment → Matrix E G ℂ) : QMatrix G :=
  (coherentMinus p M)ᴴ*coherentMinus p M+noiseWeight p • ((noisePlus M)ᴴ*noisePlus M)

theorem spinLeftPlus_isDensity {M : CanonicalEnvironment → Matrix E G ℂ}
    (hM : ImageOrthonormal M) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    QuantumProver.ConditionalEntropy.IsDensity (spinLeftPlus p M) :=
  weightedGram_isDensity (coherentPlus p M) (noisePlus M) (coherentWeight_pos hp1)
    (by dsimp [noiseWeight]; positivity) (physical_weights p)
    (coherentPlus_hsSq hM hp0 hp1) (noisePlus_hsSq hM)

theorem spinLeftMinus_isDensity {M : CanonicalEnvironment → Matrix E G ℂ}
    (hM : ImageOrthonormal M) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    QuantumProver.ConditionalEntropy.IsDensity (spinLeftMinus p M) :=
  weightedGram_isDensity (coherentMinus p M) (noiseMinus M) (coherentWeight_pos hp1)
    (by dsimp [noiseWeight]; positivity) (physical_weights p)
    (coherentMinus_hsSq hM hp0 hp1) (noiseMinus_hsSq hM)

theorem spinRightPlus_isDensity {M : CanonicalEnvironment → Matrix E G ℂ}
    (hM : ImageOrthonormal M) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    QuantumProver.ConditionalEntropy.IsDensity (spinRightPlus p M) := by
  have h := weightedGram_isDensity (coherentPlus p M)ᴴ (noiseMinus M)ᴴ
    (coherentWeight_pos hp1) (by dsimp [noiseWeight]; positivity) (physical_weights p)
    (by rw [hsSq_conjTranspose]; exact coherentPlus_hsSq hM hp0 hp1)
    (by rw [hsSq_conjTranspose]; exact noiseMinus_hsSq hM)
  simpa only [spinRightPlus,Matrix.conjTranspose_conjTranspose] using h

theorem spinRightMinus_isDensity {M : CanonicalEnvironment → Matrix E G ℂ}
    (hM : ImageOrthonormal M) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    QuantumProver.ConditionalEntropy.IsDensity (spinRightMinus p M) := by
  have h := weightedGram_isDensity (coherentMinus p M)ᴴ (noisePlus M)ᴴ
    (coherentWeight_pos hp1) (by dsimp [noiseWeight]; positivity) (physical_weights p)
    (by rw [hsSq_conjTranspose]; exact coherentMinus_hsSq hM hp0 hp1)
    (by rw [hsSq_conjTranspose]; exact noisePlus_hsSq hM)
  simpa only [spinRightMinus,Matrix.conjTranspose_conjTranspose] using h

theorem spinAmplitude_leftPinch {p : ℝ} (hp0 : 0 ≤ p)
    (M : CanonicalEnvironment → Matrix E G ℂ) :
    binaryPinch (spinAmplitude p M*(spinAmplitude p M)ᴴ) =
      (1/2 : ℝ) • Matrix.fromBlocks (spinLeftPlus p M) 0 0 (spinLeftMinus p M) := by
  have ha : 0 ≤ noiseWeight p := by dsimp [noiseWeight]; positivity
  have hsq : Real.sqrt (noiseWeight p)*Real.sqrt (noiseWeight p)=noiseWeight p := by
    simpa only [pow_two] using Real.sq_sqrt ha
  have hc : splitterScale*splitterScale=(1/2 : ℝ) := by
    simpa only [pow_two] using splitterScale_sq
  simp only [spinAmplitude,Matrix.conjTranspose_smul,star_trivial,
    Matrix.smul_mul,Matrix.mul_smul,smul_smul,Matrix.fromBlocks_conjTranspose,
    Matrix.fromBlocks_multiply]
  ext i j
  cases i <;> cases j <;>
    simp [binaryPinch,spinLeftPlus,spinLeftMinus,Matrix.smul_apply,hc,hsq] <;> ring

theorem spinAmplitude_rightPinch {p : ℝ} (hp0 : 0 ≤ p)
    (M : CanonicalEnvironment → Matrix E G ℂ) :
    binaryPinch ((spinAmplitude p M)ᴴ*spinAmplitude p M) =
      (1/2 : ℝ) • Matrix.fromBlocks (spinRightPlus p M) 0 0 (spinRightMinus p M) := by
  have ha : 0 ≤ noiseWeight p := by dsimp [noiseWeight]; positivity
  have hsq : Real.sqrt (noiseWeight p)*Real.sqrt (noiseWeight p)=noiseWeight p := by
    simpa only [pow_two] using Real.sq_sqrt ha
  have hc : splitterScale*splitterScale=(1/2 : ℝ) := by
    simpa only [pow_two] using splitterScale_sq
  simp only [spinAmplitude,Matrix.conjTranspose_smul,star_trivial,
    Matrix.smul_mul,Matrix.mul_smul,smul_smul,Matrix.fromBlocks_conjTranspose,
    Matrix.fromBlocks_multiply]
  ext i j
  cases i <;> cases j <;>
    simp [binaryPinch,spinRightPlus,spinRightMinus,Matrix.smul_apply,hc,hsq] <;> ring

theorem entropyNat_half_flag {I : Type*} [Fintype I] [DecidableEq I]
    {R S : QMatrix I} (hR : QuantumProver.ConditionalEntropy.IsDensity R)
    (hS : QuantumProver.ConditionalEntropy.IsDensity S) :
    entropyNat ((1/2 : ℝ) • Matrix.fromBlocks R 0 0 S) =
      Real.log 2+(entropyNat R+entropyNat S)/2 := by
  have hd : (Matrix.fromBlocks R 0 0 S).PosSemidef :=
    QuantumProver.SuperchannelDiscrimination.FlaggedStates.flagBlock_posSemidef hR.1 hS.1
  have hl : Real.log (1/2 : ℝ) = -Real.log 2 := by
    rw [Real.log_div (by norm_num : (1:ℝ)≠0) (by norm_num : (2:ℝ)≠0),Real.log_one]
    ring
  rw [entropyNat_smul (1/2) hd,entropyNat_blockDiagonal hR.1 hS.1,
    trace_blockDiagonal,hR.2,hS.2,hl]
  norm_num
  ring

def spinEnvironmentLeft (p : ℝ) (M : CanonicalEnvironment → Matrix E G ℂ) : QMatrix E :=
  QuantumProver.ConditionalEntropy.mix (1/2) (spinLeftPlus p M) (spinLeftMinus p M)

def spinEnvironmentRight (p : ℝ) (M : CanonicalEnvironment → Matrix E G ℂ) : QMatrix G :=
  QuantumProver.ConditionalEntropy.mix (1/2) (spinRightPlus p M) (spinRightMinus p M)

def spinInformationLeft (p : ℝ) (M : CanonicalEnvironment → Matrix E G ℂ) : ℝ :=
  Real.log 2+entropyNat (spinEnvironmentLeft p M)-
    entropyNat (spinAmplitude p M*(spinAmplitude p M)ᴴ)

def spinInformationRight (p : ℝ) (M : CanonicalEnvironment → Matrix E G ℂ) : ℝ :=
  Real.log 2+entropyNat (spinEnvironmentRight p M)-
    entropyNat ((spinAmplitude p M)ᴴ*spinAmplitude p M)

theorem spinInformationLeft_decomposition {M : CanonicalEnvironment → Matrix E G ℂ}
    (hM : ImageOrthonormal M) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    spinInformationLeft p M = classicalHolevoLeft p M+
      binaryCoherenceNat (spinAmplitude p M*(spinAmplitude p M)ᴴ) := by
  have he : entropyNat (binaryPinch (spinAmplitude p M*(spinAmplitude p M)ᴴ)) =
      Real.log 2+(entropyNat (spinLeftPlus p M)+entropyNat (spinLeftMinus p M))/2 := by
    rw [spinAmplitude_leftPinch hp0]
    exact entropyNat_half_flag (spinLeftPlus_isDensity hM hp0 hp1)
      (spinLeftMinus_isDensity hM hp0 hp1)
  change Real.log 2+entropyNat (QuantumProver.ConditionalEntropy.mix (1/2)
    (spinLeftPlus p M) (spinLeftMinus p M))-
    entropyNat (spinAmplitude p M*(spinAmplitude p M)ᴴ) =
      (entropyNat (QuantumProver.ConditionalEntropy.mix (1/2) (spinLeftPlus p M) (spinLeftMinus p M))-
        (entropyNat (spinLeftPlus p M)+entropyNat (spinLeftMinus p M))/2)+
      (entropyNat (binaryPinch (spinAmplitude p M*(spinAmplitude p M)ᴴ))-
        entropyNat (spinAmplitude p M*(spinAmplitude p M)ᴴ))
  rw [he]
  ring

theorem spinInformationRight_decomposition {M : CanonicalEnvironment → Matrix E G ℂ}
    (hM : ImageOrthonormal M) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    spinInformationRight p M = classicalHolevoRight p M+
      binaryCoherenceNat ((spinAmplitude p M)ᴴ*spinAmplitude p M) := by
  have he : entropyNat (binaryPinch ((spinAmplitude p M)ᴴ*spinAmplitude p M)) =
      Real.log 2+(entropyNat (spinRightPlus p M)+entropyNat (spinRightMinus p M))/2 := by
    rw [spinAmplitude_rightPinch hp0]
    exact entropyNat_half_flag (spinRightPlus_isDensity hM hp0 hp1)
      (spinRightMinus_isDensity hM hp0 hp1)
  change Real.log 2+entropyNat (QuantumProver.ConditionalEntropy.mix (1/2)
    (spinRightPlus p M) (spinRightMinus p M))-
    entropyNat ((spinAmplitude p M)ᴴ*spinAmplitude p M) =
      (entropyNat (QuantumProver.ConditionalEntropy.mix (1/2) (spinRightPlus p M) (spinRightMinus p M))-
        (entropyNat (spinRightPlus p M)+entropyNat (spinRightMinus p M))/2)+
      (entropyNat (binaryPinch ((spinAmplitude p M)ᴴ*spinAmplitude p M))-
        entropyNat ((spinAmplitude p M)ᴴ*spinAmplitude p M))
  rw [he]
  ring

section RectangularC1

variable {I0 I1 J0 J1 : Type*}
  [Fintype I0] [Fintype I1] [Fintype J0] [Fintype J1]
  [DecidableEq I0] [DecidableEq I1] [DecidableEq J0] [DecidableEq J1]

theorem rectangularC1 (T : Matrix (I0 ⊕ I1) (J0 ⊕ J1) ℂ) :
    binaryCoherenceNat (T*Tᴴ)+binaryCoherenceNat (Tᴴ*T) ≤
      (hsSq (T.submatrix Sum.inl Sum.inr)+hsSq (T.submatrix Sum.inr Sum.inl))*
        Fcal ((2*hsSq T)/
          (hsSq (T.submatrix Sum.inl Sum.inr)+hsSq (T.submatrix Sum.inr Sum.inl)))+
      4*(hsSq (T.submatrix Sum.inl Sum.inr)+hsSq (T.submatrix Sum.inr Sum.inl)) := by
  have h := c1_hermitian_square_entropy_bound (groupedDilation_isHermitian T)
  have hz : (groupedDilation T).submatrix Sum.inr Sum.inl =
      Matrix.fromBlocks 0 (T.submatrix Sum.inr Sum.inl)
        (T.submatrix Sum.inl Sum.inr)ᴴ 0 := by
    rw [groupedDilation_eq_binary]
    ext i j
    cases i <;> cases j <;> rfl
  rw [groupedDilation_square_coherence,hz,groupedDilation_noise_budget,
    groupedDilation_trace_budget] at h
  exact h

end RectangularC1

theorem spinCoherencePair_upper {M : CanonicalEnvironment → Matrix E G ℂ}
    (hM : ImageOrthonormal M) {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) :
    binaryCoherenceNat (spinAmplitude p M*(spinAmplitude p M)ᴴ)+
      binaryCoherenceNat ((spinAmplitude p M)ᴴ*spinAmplitude p M) ≤
        2*noiseWeight p*(Fcal (1/noiseWeight p)+4) := by
  have ha : noiseWeight p ≠ 0 := by dsimp [noiseWeight]; positivity
  have h := rectangularC1 (spinAmplitude p M)
  rw [spinAmplitude_hsSq hM hp0.le hp1,
    spinAmplitude_offLeft_hsSq hM hp0.le,
    spinAmplitude_offRight_hsSq hM hp0.le] at h
  have he : (2*1 : ℝ)/(noiseWeight p+noiseWeight p)=1/noiseWeight p := by
    field_simp [ha]
    ring
  rw [he] at h
  nlinarith only [h]

theorem coherentHolevo_joint_upper {M : CanonicalEnvironment → Matrix E G ℂ}
    (hM : ImageOrthonormal M) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    coherentWeight p*(coherentHolevoLeft p M+coherentHolevoRight p M) ≤
      noiseWeight p*(Fcal (2*coherentWeight p/noiseWeight p)+4) := by
  have h := rectangularC1 (coherentCopyAmplitude p M)
  rw [coherentCopyAmplitude_hsSq hM hp0 hp1,
    coherentCopyAmplitude_off_hsSq hM hp0,
    coherentCopyAmplitude_leftCoherence p M hp1,
    coherentCopyAmplitude_rightCoherence p M hp1] at h
  nlinarith only [h]

def fourSpinInformation (p : ℝ) (M : CanonicalEnvironment → Matrix E G ℂ) : ℝ :=
  spinInformationLeft p M+spinInformationRight p M+
    spinInformationLeft p (fun i => (M i).transpose)+
    spinInformationRight p (fun i => (M i).transpose)

theorem fourSpinInformation_upper {M : CanonicalEnvironment → Matrix E G ℂ}
    (hM : ImageOrthonormal M) {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) :
    fourSpinInformation p M ≤
      4*noiseWeight p*(Fcal (1/noiseWeight p)+4)+
        2*noiseWeight p*(Fcal (2*coherentWeight p/noiseWeight p)+4)+
        8*noiseWeight p*Real.log 2 := by
  have ht := images_transpose_orthonormal hM
  have hs0 := spinCoherencePair_upper hM hp0 hp1
  have hs1 := spinCoherencePair_upper ht hp0 hp1
  have hc := coherentHolevo_joint_upper hM hp0.le hp1
  have hf := fourClassicalHolevo_upper hM hp0.le hp1
  unfold fourSpinInformation
  rw [spinInformationLeft_decomposition hM hp0.le hp1,
    spinInformationRight_decomposition hM hp0.le hp1,
    spinInformationLeft_decomposition ht hp0.le hp1,
    spinInformationRight_decomposition ht hp0.le hp1]
  unfold fourClassicalHolevo at hf
  nlinarith only [hs0,hs1,hc,hf]

def spinEquiv (I : Type*) : (I ⊕ I) ≃ (Qubit×I) where
  toFun := spinIndex I
  invFun x := if x.1=0 then Sum.inl x.2 else Sum.inr x.2
  left_inv := by intro x; cases x <;> simp [spinIndex]
  right_inv := by rintro ⟨q,i⟩; fin_cases q <;> simp [spinIndex]

theorem fourImageAmplitudeE_spinGram (p : ℝ)
    (M : CanonicalEnvironment → Matrix E G ℂ) :
    (fourImageAmplitudeE p M*(fourImageAmplitudeE p M)ᴴ).submatrix
      (spinEquiv E) (spinEquiv E) = spinAmplitude p M*(spinAmplitude p M)ᴴ := by
  rw [← Matrix.submatrix_mul_equiv _ _ (spinEquiv E) (spinEquiv G) (spinEquiv E),
    ← Matrix.conjTranspose_submatrix]
  change (fourImageAmplitudeE p M).submatrix (spinIndex E) (spinIndex G)*
    ((fourImageAmplitudeE p M).submatrix (spinIndex E) (spinIndex G))ᴴ = _
  rw [fourImageAmplitudeE_spin]

theorem fourImageAmplitudeE_spin_entropy (p : ℝ)
    (M : CanonicalEnvironment → Matrix E G ℂ) :
    entropyNat (fourImageAmplitudeE p M*(fourImageAmplitudeE p M)ᴴ) =
      entropyNat (spinAmplitude p M*(spinAmplitude p M)ᴴ) := by
  have h := entropyNat_reindex (spinEquiv E).symm
    (Matrix.posSemidef_self_mul_conjTranspose (fourImageAmplitudeE p M)).1
  change entropyNat ((fourImageAmplitudeE p M*(fourImageAmplitudeE p M)ᴴ).submatrix
    (spinEquiv E) (spinEquiv E)) = _ at h
  rw [fourImageAmplitudeE_spinGram] at h
  exact h.symm

theorem fourImageAmplitudeG_spin_entropy (p : ℝ)
    (M : CanonicalEnvironment → Matrix E G ℂ) :
    entropyNat (fourImageAmplitudeG p M*(fourImageAmplitudeG p M)ᴴ) =
      entropyNat (spinAmplitude p (fun i => (M i).transpose)*
        (spinAmplitude p (fun i => (M i).transpose))ᴴ) :=
  fourImageAmplitudeE_spin_entropy p (fun i => (M i).transpose)

theorem spinEnvironmentLeft_eq_partialTraceGram {p : ℝ} (hp0 : 0 ≤ p)
    (M : CanonicalEnvironment → Matrix E G ℂ) :
    spinEnvironmentLeft p M=
      partialTraceLeft (fourImageAmplitudeE p M*(fourImageAmplitudeE p M)ᴴ) := by
  ext e f
  have h0 := congrArg (fun K : QMatrix (E⊕E) => K (Sum.inl e) (Sum.inl f))
    (spinAmplitude_leftPinch hp0 M)
  have h1 := congrArg (fun K : QMatrix (E⊕E) => K (Sum.inr e) (Sum.inr f))
    (spinAmplitude_leftPinch hp0 M)
  simp only [binaryPinch,Matrix.smul_apply,Matrix.fromBlocks_apply₁₁,
    Matrix.fromBlocks_apply₂₂] at h0 h1
  have hg0 := congrArg (fun K : QMatrix (E⊕E) => K (Sum.inl e) (Sum.inl f))
    (fourImageAmplitudeE_spinGram p M)
  have hg1 := congrArg (fun K : QMatrix (E⊕E) => K (Sum.inr e) (Sum.inr f))
    (fourImageAmplitudeE_spinGram p M)
  change (fourImageAmplitudeE p M*(fourImageAmplitudeE p M)ᴴ) (0,e) (0,f)=_ at hg0
  change (fourImageAmplitudeE p M*(fourImageAmplitudeE p M)ᴴ) (1,e) (1,f)=_ at hg1
  change _=∑ q : Qubit,(fourImageAmplitudeE p M*(fourImageAmplitudeE p M)ᴴ) (q,e) (q,f)
  rw [Fin.sum_univ_two,hg0,hg1,h0,h1]
  norm_num [spinEnvironmentLeft,QuantumProver.ConditionalEntropy.mix,Matrix.add_apply,Matrix.smul_apply]

theorem fourImageEnvironmentE_spin {p : ℝ} (hp0 : 0 ≤ p)
    (M : CanonicalEnvironment → Matrix E G ℂ) :
    partialTraceLeft (partialTraceRight (pureDensity (fourImageVector p M)))=
      spinEnvironmentLeft p M := by
  have htrace : partialTraceLeft (partialTraceRight (pureDensity (fourImageVector p M)))=
      partialTraceLeft (traceMiddle (partialTraceRight (pureDensity (fourImageVector p M)))) := by
    ext e f
    simp only [partialTraceLeft,QuantumProver.WernerEndpoint.partialTraceRight,traceMiddle,
      Fintype.sum_prod_type]
  rw [htrace,fourImageE_gram,← spinEnvironmentLeft_eq_partialTraceGram hp0]

theorem fourImageEnvironmentG_spin {p : ℝ} (hp0 : 0 ≤ p)
    (M : CanonicalEnvironment → Matrix E G ℂ) :
    partialTraceLeft (pureDensity (fourImageVector p M))=
      spinEnvironmentLeft p (fun i => (M i).transpose) := by
  have hs : partialTraceLeft (pureDensity (fourImageVector p M))=
      partialTraceLeft (partialTraceRight
        (pureDensity (fourImageVector p (fun i => (M i).transpose)))) := by
    ext g h
    simp only [partialTraceLeft,partialTraceRight,QuantumProver.WernerEndpoint.partialTraceRight,
      QuantumProver.WernerEndpoint.partialTraceLeft,pureDensity,QuantumProver.WernerEndpoint.pureDensity,
      QuantumProver.WernerEndpoint.crossDensity,Fintype.sum_prod_type,fourImageVector,
      Matrix.transpose_apply]
  rw [hs,fourImageEnvironmentE_spin hp0]

theorem leftGram_transpose (T : Matrix E G ℂ) :
    T.transpose*T.transposeᴴ=(Tᴴ*T).transpose := by
  rw [Matrix.transpose_mul]
  rfl

theorem spinEnvironmentRight_transpose (p : ℝ)
    (M : CanonicalEnvironment → Matrix E G ℂ) :
    spinEnvironmentRight p M=(spinEnvironmentLeft p (fun i => (M i).transpose)).transpose := by
  have hP : coherentPlus p (fun i => (M i).transpose)=(coherentPlus p M).transpose := rfl
  have hQ : coherentMinus p (fun i => (M i).transpose)=(coherentMinus p M).transpose := rfl
  have hN : noisePlus (fun i => (M i).transpose)=(noisePlus M).transpose := rfl
  have hO : noiseMinus (fun i => (M i).transpose)=(noiseMinus M).transpose := rfl
  simp only [spinEnvironmentRight,spinEnvironmentLeft,QuantumProver.ConditionalEntropy.mix,
    spinRightPlus,spinRightMinus,spinLeftPlus,spinLeftMinus,hP,hQ,hN,hO,
    leftGram_transpose,Matrix.transpose_add,Matrix.transpose_smul,Matrix.transpose_transpose]
  module

theorem spinEnvironmentLeft_isDensity {M : CanonicalEnvironment → Matrix E G ℂ}
    (hM : ImageOrthonormal M) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    QuantumProver.ConditionalEntropy.IsDensity (spinEnvironmentLeft p M) :=
  QuantumProver.ConditionalEntropy.mix_isDensity (spinLeftPlus_isDensity hM hp0 hp1)
    (spinLeftMinus_isDensity hM hp0 hp1) (by norm_num) (by norm_num)

theorem spinEnvironmentRight_entropy (p : ℝ)
    {M : CanonicalEnvironment → Matrix E G ℂ} (hM : ImageOrthonormal M)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    entropyNat (spinEnvironmentRight p M)=
      entropyNat (spinEnvironmentLeft p (fun i => (M i).transpose)) := by
  rw [spinEnvironmentRight_transpose]
  exact entropyNat_transpose
    (spinEnvironmentLeft_isDensity (images_transpose_orthonormal hM) hp0 hp1).1.1

def fourImageHalfCostNat (p : ℝ) (M : CanonicalEnvironment → Matrix E G ℂ) : ℝ :=
  (entropyNat (fourImageAmplitudeE p M*(fourImageAmplitudeE p M)ᴴ)+
    entropyNat (fourImageAmplitudeG p M*(fourImageAmplitudeG p M)ᴴ)-
    entropyNat (partialTraceLeft (partialTraceRight (pureDensity (fourImageVector p M))))-
    entropyNat (partialTraceLeft (pureDensity (fourImageVector p M))))/2

theorem fourSpinInformation_eq_halfCost {M : CanonicalEnvironment → Matrix E G ℂ}
    (hM : ImageOrthonormal M) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    fourSpinInformation p M=4*(Real.log 2-fourImageHalfCostNat p M) := by
  have ht := images_transpose_orthonormal hM
  have hER := spinEnvironmentRight_entropy p hM hp0 hp1
  have hGR := spinEnvironmentRight_entropy p ht hp0 hp1
  simp only [Matrix.transpose_transpose] at hGR
  unfold fourSpinInformation spinInformationLeft spinInformationRight fourImageHalfCostNat
  rw [hER,hGR,entropyNat_oppositeGram,entropyNat_oppositeGram,
    fourImageAmplitudeE_spin_entropy,fourImageAmplitudeG_spin_entropy,
    fourImageEnvironmentE_spin hp0,fourImageEnvironmentG_spin hp0]
  ring

theorem fourImageHalfCostNat_lower {M : CanonicalEnvironment → Matrix E G ℂ}
    (hM : ImageOrthonormal M) {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) :
    Real.log 2-noiseWeight p*Fcal (1/noiseWeight p)-
      (noiseWeight p/2)*Fcal (2*coherentWeight p/noiseWeight p)-
      (6+2*Real.log 2)*noiseWeight p ≤ fourImageHalfCostNat p M := by
  have h := fourSpinInformation_upper hM hp0 hp1
  rw [fourSpinInformation_eq_halfCost hM hp0.le hp1] at h
  nlinarith only [h]

end QuantumProver.DepolarizingSquashedEntanglement.EntropySharing

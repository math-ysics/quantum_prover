import QuantumProver.InformationTheory.BellDiagonalSquashedEntanglement.Definitions
import QuantumProver.InformationTheory.ConditionalEntropy.ConditionalRange
import QuantumProver.LinearAlgebra.AbsoluteHS
import QuantumProver.InformationTheory.QuantumEntropy.StrongSubadditivity
import QuantumProver.InformationTheory.BellDiagonalSquashedEntanglement.ExtensionGeometry
import QuantumProver.InformationTheory.BellDiagonalSquashedEntanglement.RecoveryGeometry

set_option autoImplicit false

noncomputable section

open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Filter Set Matrix

namespace QuantumProver.BellDiagonalSquashedEntanglement

variable {E : Type*} [Fintype E] [DecidableEq E]

theorem sqrtPSD_conjTranspose (A : Mat E) : (sqrtPSD A)ᴴ = sqrtPSD A := by
  exact (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)).isHermitian.eq

theorem sqrtPSD_mul_self (A : Mat E) (hA : A.PosSemidef) :
    sqrtPSD A * sqrtPSD A = A :=
  CFC.sqrt_mul_sqrt_self A hA.nonneg

theorem affinity_trace (A B : Mat E) :
    (sqrtPSD A * sqrtPSD B).trace = (affinity A B : ℂ) := by
  have hstar : star (sqrtPSD A * sqrtPSD B).trace =
      (sqrtPSD A * sqrtPSD B).trace := by
    rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul,
      sqrtPSD_conjTranspose, sqrtPSD_conjTranspose, Matrix.trace_mul_comm]
  have him : (sqrtPSD A * sqrtPSD B).trace.im = 0 := by
    have hi := congrArg Complex.im hstar
    simp only [Complex.star_def, Complex.conj_im] at hi
    linarith
  apply Complex.ext
  · rfl
  · simpa only [Complex.ofReal_im] using him

theorem pairKernel_conjTranspose_mul {A B : Mat E}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    (pairKernel A B)ᴴ * pairKernel A B = A + B := by
  have heq : (pairKernel A B)ᴴ * pairKernel A B =
      (sqrtPSD A)ᴴ * sqrtPSD A + (sqrtPSD B)ᴴ * sqrtPSD B := by
    ext i j
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, pairKernel,
      Fintype.sum_prod_type, Fin.sum_univ_two]
  rw [heq, sqrtPSD_conjTranspose, sqrtPSD_conjTranspose,
    sqrtPSD_mul_self A hA, sqrtPSD_mul_self B hB]

theorem pairGram_trace {A B : Mat E} (hA : IsDensity A) (hB : IsDensity B) :
    (pairGram A B).trace = 1 := by
  rw [pairGram, Matrix.trace_smul, Matrix.trace_mul_comm,
    pairKernel_conjTranspose_mul hA.1 hB.1, Matrix.trace_add, hA.2, hB.2]
  norm_num

theorem pairGram_isDensity {A B : Mat E} (hA : IsDensity A) (hB : IsDensity B) :
    IsDensity (pairGram A B) :=
  ⟨pairGram_posSemidef A B, pairGram_trace hA hB⟩

theorem sqrtPSD_rowGram {A : Mat E} (hA : A.PosSemidef) (i j : E) :
    (∑ k, sqrtPSD A i k * star (sqrtPSD A j k)) = A i j := by
  change (sqrtPSD A * (sqrtPSD A)ᴴ) i j = A i j
  rw [sqrtPSD_conjTranspose, sqrtPSD_mul_self A hA]

theorem sqrtPSD_rowGram_ringEnd {A : Mat E} (hA : A.PosSemidef) (i j : E) :
    (∑ k, sqrtPSD A i k * (starRingEnd ℂ) (sqrtPSD A j k)) = A i j :=
  sqrtPSD_rowGram hA i j

theorem pairGram_marginalE {A B : Mat E}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    marginalE (pairGram A B) = (1 / 2 : ℝ) • (A + B) := by
  ext i j
  simp [marginalE, partialTraceLeft, pairGram, pairKernel,
    Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type,
    Fin.sum_univ_two, sqrtPSD_rowGram_ringEnd hA,
    sqrtPSD_rowGram_ringEnd hB, smul_eq_mul] <;> ring

def pairRootBlock (A B : Mat E) (x : AB) : Mat E :=
  if x = (0, 0) then sqrtPSD A else if x = (1, 1) then sqrtPSD B else 0

theorem pairKernel_apply_rootBlock (A B : Mat E) (x : AB × E) (j : E) :
    pairKernel A B x j = pairRootBlock A B x.1 x.2 j := by
  simp only [pairKernel, pairRootBlock, ite_apply]
  split_ifs <;> rfl

theorem pairGram_partialTrace_entry (A B : Mat E) (x y : AB) :
    partialTraceRight (pairGram A B) x y =
      (1 / 2 : ℝ) • (pairRootBlock A B x * (pairRootBlock A B y)ᴴ).trace := by
  simp only [partialTraceRight, pairGram, Matrix.smul_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, pairKernel_apply_rootBlock, Matrix.trace]
  exact Finset.smul_sum.symm

theorem pairGram_partialTrace {A B : Mat E} (hA : IsDensity A) (hB : IsDensity B) :
    partialTraceRight (pairGram A B) = bellEdge (affinity A B) := by
  ext x y
  rcases x with ⟨a, b⟩
  rcases y with ⟨d, e⟩
  rw [pairGram_partialTrace_entry]
  fin_cases a <;> fin_cases b <;> fin_cases d <;> fin_cases e <;>
    simp [pairRootBlock, bellEdge, outer, ket00, ket11, evenVector,
      Matrix.vecMulVec, sqrtPSD_conjTranspose, sqrtPSD_mul_self A hA.1,
      sqrtPSD_mul_self B hB.1, Matrix.trace_mul_comm (sqrtPSD B) (sqrtPSD A),
      affinity_trace, hA.2, hB.2, smul_eq_mul] <;>
    push_cast <;> ring

theorem pairGram_feasible {n : ℕ} (hn : 0 < n) (A B : Density (Fin n)) :
    ∃ ω : Density (AB × Fin n),
      partialTraceRight ω.val = bellEdge (affinity A.val B.val) := by
  exact ⟨⟨pairGram A.val B.val, pairGram_isDensity A.property B.property⟩,
    pairGram_partialTrace A.property B.property⟩

def matrixReindexHom {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (e : I ≃ J) : Mat I →⋆ₐ[ℝ] Mat J where
  __ := (Matrix.reindexAlgEquiv ℝ ℂ e).toAlgHom
  map_star' X := by ext i j; rfl

theorem matrixReindexHom_continuous {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (e : I ≃ J) :
    Continuous (matrixReindexHom e) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  change Continuous (fun X : Mat I => X (e.symm i) (e.symm j))
  fun_prop

theorem matrixReindexHom_trace {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (e : I ≃ J) (X : Mat I) :
    (matrixReindexHom e X).trace = X.trace := by
  change (∑ j, X (e.symm j) (e.symm j)) = ∑ i, X i i
  exact e.symm.sum_comp (fun i => X i i)

theorem entropyBits_reindex {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (e : I ≃ J) {X : Mat I}
    (hX : X.IsHermitian) :
    entropyBits (matrixReindexHom e X) = entropyBits X := by
  have hmap := (matrixReindexHom e).map_cfc (fun x : ℝ => x * Real.log x) X
    (X.finite_real_spectrum.continuousOn _) (matrixReindexHom_continuous e) hX
  change -(cfc (fun x : ℝ => x * Real.log x) (matrixReindexHom e X)).trace.re /
    Real.log 2 = -(cfc (fun x : ℝ => x * Real.log x) X).trace.re / Real.log 2
  rw [← hmap, matrixReindexHom_trace]

def qubitSumEquiv (E : Type*) : Qubit × E ≃ E ⊕ E where
  toFun x := if x.1 = 0 then Sum.inl x.2 else Sum.inr x.2
  invFun x := match x with | Sum.inl e => (0, e) | Sum.inr e => (1, e)
  left_inv x := by rcases x with ⟨a, e⟩; fin_cases a <;> simp
  right_inv x := by cases x <;> simp

def pairFlagBlock (A B : Mat E) : Mat (Qubit × E) :=
  matrixReindexHom (qubitSumEquiv E).symm
    (QuantumProver.SuperchannelDiscrimination.FlaggedStates.flagBlock
      ((1 / 2 : ℝ) • A) ((1 / 2 : ℝ) • B))

theorem pairGram_marginalAE {A B : Mat E}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    marginalAE (pairGram A B) = pairFlagBlock A B := by
  ext x y
  rcases x with ⟨a, i⟩
  rcases y with ⟨d, j⟩
  fin_cases a <;> fin_cases d <;>
    simp [marginalAE, pairGram, pairKernel, pairFlagBlock, matrixReindexHom,
      qubitSumEquiv, QuantumProver.SuperchannelDiscrimination.FlaggedStates.flagBlock,
      Matrix.reindex_apply, Matrix.submatrix, Matrix.fromBlocks,
      Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two,
      sqrtPSD_rowGram_ringEnd hA, sqrtPSD_rowGram_ringEnd hB, smul_eq_mul]

theorem pairGram_marginalBE {A B : Mat E}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    marginalBE (pairGram A B) = pairFlagBlock A B := by
  ext x y
  rcases x with ⟨a, i⟩
  rcases y with ⟨d, j⟩
  fin_cases a <;> fin_cases d <;>
    simp [marginalBE, pairGram, pairKernel, pairFlagBlock, matrixReindexHom,
      qubitSumEquiv, QuantumProver.SuperchannelDiscrimination.FlaggedStates.flagBlock,
      Matrix.reindex_apply, Matrix.submatrix, Matrix.fromBlocks,
      Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two,
      sqrtPSD_rowGram_ringEnd hA, sqrtPSD_rowGram_ringEnd hB, smul_eq_mul]

theorem flagEntropyBits_half :
    QuantumProver.SuperchannelDiscrimination.FlaggedStates.flagEntropyBits (1 / 2) = 1 := by
  have heq : 1 - (1 / 2 : ℝ) = 1 / 2 := by norm_num
  unfold QuantumProver.SuperchannelDiscrimination.FlaggedStates.flagEntropyBits
  rw [heq]
  have hlog : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
    rw [one_div, Real.log_inv]
  rw [hlog]
  field_simp [log_two_pos.ne'] <;> ring

theorem entropyBits_pairFlagBlock {A B : Mat E}
    (hA : IsDensity A) (hB : IsDensity B) :
    entropyBits (pairFlagBlock A B) = 1 + (entropyBits A + entropyBits B) / 2 := by
  rw [pairFlagBlock, entropyBits_reindex (qubitSumEquiv E).symm
    (QuantumProver.SuperchannelDiscrimination.FlaggedStates.flagBlock_isHermitian
      (hA.1.smul (show (0 : ℝ) ≤ 1 / 2 by norm_num)).isHermitian
      (hB.1.smul (show (0 : ℝ) ≤ 1 / 2 by norm_num)).isHermitian)]
  have heq : 1 - (1 / 2 : ℝ) = 1 / 2 := by norm_num
  have h := QuantumProver.SuperchannelDiscrimination.FlaggedStates.entropyBits_flagged_density
    hA hB (p := 1 / 2) (by norm_num) (by norm_num)
  rw [heq, flagEntropyBits_half] at h
  calc
    entropyBits (QuantumProver.SuperchannelDiscrimination.FlaggedStates.flagBlock
      ((1 / 2 : ℝ) • A) ((1 / 2 : ℝ) • B)) =
        1 + (1 / 2 : ℝ) * entropyBits A + (1 / 2 : ℝ) * entropyBits B := h
    _ = 1 + (entropyBits A + entropyBits B) / 2 := by ring

theorem entropyBits_pairGram_marginalAE {A B : Mat E}
    (hA : IsDensity A) (hB : IsDensity B) :
    entropyBits (marginalAE (pairGram A B)) =
      1 + (entropyBits A + entropyBits B) / 2 := by
  rw [pairGram_marginalAE hA.1 hB.1, entropyBits_pairFlagBlock hA hB]

theorem entropyBits_pairGram_marginalBE {A B : Mat E}
    (hA : IsDensity A) (hB : IsDensity B) :
    entropyBits (marginalBE (pairGram A B)) =
      1 + (entropyBits A + entropyBits B) / 2 := by
  rw [pairGram_marginalBE hA.1 hB.1, entropyBits_pairFlagBlock hA hB]

theorem entropyBits_oppositeGrams {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (M : Matrix I J ℂ) :
    entropyBits (Mᴴ * M) = entropyBits (M * Mᴴ) :=
  QuantumProver.ConditionalEntropy.ConditionalRange.entropyBits_rectangularGram M

theorem pairGram_jointEntropy {A B : Mat E}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    entropyBits (pairGram A B) = entropyBits ((1 / 2 : ℝ) • (A + B)) := by
  let M := pairKernel A B
  have hc : Mᴴ * M = A + B := pairKernel_conjTranspose_mul hA hB
  have hg : entropyBits (M * Mᴴ) = entropyBits (A + B) := by
    rw [← entropyBits_oppositeGrams M, hc]
  have ht : (M * Mᴴ).trace.re = (A + B).trace.re := by
    rw [Matrix.trace_mul_comm M Mᴴ, hc]
  change entropyBits ((1 / 2 : ℝ) • (M * Mᴴ)) =
    entropyBits ((1 / 2 : ℝ) • (A + B))
  calc
    entropyBits ((1 / 2 : ℝ) • (M * Mᴴ)) =
        (1 / 2 : ℝ) * entropyBits (M * Mᴴ) -
          ((1 / 2 : ℝ) * Real.log (1 / 2) / Real.log 2) * (M * Mᴴ).trace.re :=
      QuantumProver.SuperchannelDiscrimination.FlaggedStates.entropyBits_smul
        (1 / 2 : ℝ) (Matrix.posSemidef_self_mul_conjTranspose M)
    _ = (1 / 2 : ℝ) * entropyBits (A + B) -
          ((1 / 2 : ℝ) * Real.log (1 / 2) / Real.log 2) * (A + B).trace.re := by
      rw [hg, ht]
    _ = entropyBits ((1 / 2 : ℝ) • (A + B)) :=
      (QuantumProver.SuperchannelDiscrimination.FlaggedStates.entropyBits_smul
        (1 / 2 : ℝ) (hA.add hB)).symm

theorem pairGram_halfCMI {A B : Mat E} (hA : IsDensity A) (hB : IsDensity B) :
    halfCMI (pairGram A B) = pairCost A B := by
  rw [halfCMI, entropyBits_pairGram_marginalAE hA hB,
    entropyBits_pairGram_marginalBE hA hB, pairGram_marginalE hA.1 hB.1,
    pairGram_jointEntropy hA.1 hB.1]
  unfold pairCost binaryHolevo
  ring

theorem pairCost_mem_extensionCosts {c : ℝ} {n : ℕ}
    (hn : 0 < n) (A B : Density (Fin n)) (haff : affinity A.val B.val = c) :
    pairCost A.val B.val ∈ extensionCosts c := by
  refine ⟨n, hn, ⟨pairGram A.val B.val, pairGram_isDensity A.property B.property⟩,
    ?_, ?_⟩
  · simpa only [haff] using pairGram_partialTrace A.property B.property
  · exact (pairGram_halfCMI A.property B.property).symm

theorem finitePairCosts_subset_extensionCosts (c : ℝ) :
    finitePairCosts c ⊆ extensionCosts c := by
  rintro z ⟨n, hn, A, B, haff, rfl⟩
  exact pairCost_mem_extensionCosts hn A B haff

theorem squashedEntanglement_le_positivePairInfimum {c : ℝ}
    (hb : BddBelow (extensionCosts c)) (hp : (finitePairCosts c).Nonempty) :
    squashedEntanglement c ≤ positivePairInfimum c := by
  exact csInf_le_csInf hb hp (finitePairCosts_subset_extensionCosts c)

theorem psd_column_zero_of_diagonal {I : Type*} [Fintype I] [DecidableEq I]
    {X : Mat I} (hX : X.PosSemidef) {i : I} (hi : X i i = 0) (j : I) :
    X j i = 0 := by
  have hquad : star (Pi.single i (1 : ℂ)) ⬝ᵥ X *ᵥ Pi.single i 1 = 0 := by
    simp [Matrix.mulVec_single_one, dotProduct, Pi.single_apply, hi]
  have hv := hX.dotProduct_mulVec_zero_iff.mp hquad
  simpa [Matrix.mulVec_single_one] using congr_fun hv j

theorem psd_row_zero_of_diagonal {I : Type*} [Fintype I] [DecidableEq I]
    {X : Mat I} (hX : X.PosSemidef) {i : I} (hi : X i i = 0) (j : I) :
    X i j = 0 := by
  have hh := congr_fun (congr_fun hX.isHermitian.eq i) j
  simp only [Matrix.conjTranspose_apply, psd_column_zero_of_diagonal hX hi j,
    star_zero] at hh
  exact hh.symm

theorem bellEdge_offParity_diagonal (c : ℝ) (x : AB) (hx : x.1 ≠ x.2) :
    bellEdge c x x = 0 := by
  have h00 : x ≠ (0, 0) := by
    intro h
    exact hx ((congrArg Prod.fst h).trans (congrArg Prod.snd h).symm)
  have h11 : x ≠ (1, 1) := by
    intro h
    exact hx ((congrArg Prod.fst h).trans (congrArg Prod.snd h).symm)
  simp [bellEdge, outer, evenVector, ket00, ket11, Matrix.vecMulVec, h00, h11]

theorem extension_offParity_diagonal {c : ℝ} {ω : Mat (AB × E)}
    (hω : ω.PosSemidef) (hmarginal : partialTraceRight ω = bellEdge c)
    (x : AB) (hx : x.1 ≠ x.2) (e : E) : ω (x, e) (x, e) = 0 := by
  have hsum : (∑ f : E, (ω (x, f) (x, f)).re) = 0 := by
    have hh := congrArg (fun X : Mat AB => (X x x).re) hmarginal
    rw [bellEdge_offParity_diagonal c x hx] at hh
    simpa only [partialTraceRight, Complex.re_sum, Complex.zero_re] using hh
  have hnonneg : 0 ≤ (ω (x, e) (x, e)).re :=
    (Complex.nonneg_iff.mp (hω.diag_nonneg (i := (x, e)))).1
  have hle : (ω (x, e) (x, e)).re ≤ ∑ f : E, (ω (x, f) (x, f)).re :=
    Finset.single_le_sum
      (fun f _ => (Complex.nonneg_iff.mp (hω.diag_nonneg (i := (x, f)))).1)
      (Finset.mem_univ e)
  rw [hsum] at hle
  have him : (ω (x, e) (x, e)).im = 0 :=
    (Complex.nonneg_iff.mp (hω.diag_nonneg (i := (x, e)))).2.symm
  apply Complex.ext
  · exact le_antisymm hle hnonneg
  · exact him

theorem extension_offParity_row {c : ℝ} {ω : Mat (AB × E)}
    (hω : ω.PosSemidef) (hmarginal : partialTraceRight ω = bellEdge c)
    (x : AB) (hx : x.1 ≠ x.2) (e : E) (y : AB × E) : ω (x, e) y = 0 :=
  psd_row_zero_of_diagonal hω (extension_offParity_diagonal hω hmarginal x hx e) y

theorem extension_offParity_column {c : ℝ} {ω : Mat (AB × E)}
    (hω : ω.PosSemidef) (hmarginal : partialTraceRight ω = bellEdge c)
    (x : AB) (hx : x.1 ≠ x.2) (e : E) (y : AB × E) : ω y (x, e) = 0 :=
  psd_column_zero_of_diagonal hω (extension_offParity_diagonal hω hmarginal x hx e) y

def extensionRootBlock (ω : Mat (AB × E)) (q : Qubit) : Matrix E (AB × E) ℂ :=
  fun e j => sqrtPSD ω ((q, q), e) j

def extensionConditionalE (ω : Mat (AB × E)) (q : Qubit) : Mat E :=
  (2 : ℝ) • (extensionRootBlock ω q * (extensionRootBlock ω q)ᴴ)

def extensionConditionalG (ω : Mat (AB × E)) (q : Qubit) : Mat (AB × E) :=
  (2 : ℝ) • ((extensionRootBlock ω q)ᴴ * extensionRootBlock ω q)

theorem extensionRootBlock_leftGram (ω : Mat (AB × E))
    (hω : ω.PosSemidef) (q : Qubit) :
    extensionRootBlock ω q * (extensionRootBlock ω q)ᴴ =
      ω.submatrix (fun e : E => ((q, q), e)) (fun e : E => ((q, q), e)) := by
  ext e f
  change (∑ k : AB × E, sqrtPSD ω ((q, q), e) k *
    star (sqrtPSD ω ((q, q), f) k)) = ω ((q, q), e) ((q, q), f)
  exact sqrtPSD_rowGram hω ((q, q), e) ((q, q), f)

theorem bellEdge_evenDiagonal (c : ℝ) (q : Qubit) :
    bellEdge c (q, q) (q, q) = ((1 / 2 : ℝ) : ℂ) := by
  fin_cases q <;> norm_num [bellEdge, outer, evenVector, ket00, ket11,
    Matrix.vecMulVec] <;> push_cast <;> ring

theorem bellEdge_reverseOffDiagonal (c : ℝ) :
    bellEdge c (1, 1) (0, 0) = ((c / 2 : ℝ) : ℂ) := by
  simp [bellEdge, outer, evenVector, ket00, ket11, Matrix.vecMulVec]

theorem extensionConditionalE_trace {c : ℝ} {ω : Mat (AB × E)}
    (hω : ω.PosSemidef) (hmarginal : partialTraceRight ω = bellEdge c) (q : Qubit) :
    (extensionConditionalE ω q).trace = 1 := by
  have htrace :
      (ω.submatrix (fun e : E => ((q, q), e))
        (fun e : E => ((q, q), e))).trace = ((1 / 2 : ℝ) : ℂ) := by
    have hh := congr_fun (congr_fun hmarginal (q, q)) (q, q)
    rw [bellEdge_evenDiagonal c q] at hh
    change (∑ e : E, ω ((q, q), e) ((q, q), e)) = _
    exact hh
  rw [extensionConditionalE, Matrix.trace_smul,
    extensionRootBlock_leftGram ω hω q, htrace]
  norm_num

theorem extensionConditionalE_isDensity {c : ℝ} {ω : Mat (AB × E)}
    (hω : ω.PosSemidef) (hmarginal : partialTraceRight ω = bellEdge c) (q : Qubit) :
    IsDensity (extensionConditionalE ω q) := by
  refine ⟨(Matrix.posSemidef_self_mul_conjTranspose (extensionRootBlock ω q)).smul
    (show (0 : ℝ) ≤ 2 by norm_num), extensionConditionalE_trace hω hmarginal q⟩

theorem extensionConditionalG_isDensity {c : ℝ} {ω : Mat (AB × E)}
    (hω : ω.PosSemidef) (hmarginal : partialTraceRight ω = bellEdge c) (q : Qubit) :
    IsDensity (extensionConditionalG ω q) := by
  refine ⟨(Matrix.posSemidef_conjTranspose_mul_self (extensionRootBlock ω q)).smul
    (show (0 : ℝ) ≤ 2 by norm_num), ?_⟩
  rw [extensionConditionalG, Matrix.trace_smul,
    Matrix.trace_mul_comm (extensionRootBlock ω q)ᴴ (extensionRootBlock ω q)]
  simpa only [extensionConditionalE, Matrix.trace_smul]
    using extensionConditionalE_trace hω hmarginal q

theorem extensionRootBlocks_overlap {c : ℝ} {ω : Mat (AB × E)}
    (hω : ω.PosSemidef) (hmarginal : partialTraceRight ω = bellEdge c) :
    (2 : ℝ) • (extensionRootBlock ω 1 * (extensionRootBlock ω 0)ᴴ).trace = (c : ℂ) := by
  have htrace : (extensionRootBlock ω 1 * (extensionRootBlock ω 0)ᴴ).trace =
      partialTraceRight ω (1, 1) (0, 0) := by
    simp only [Matrix.trace, Matrix.mul_apply, Matrix.conjTranspose_apply,
      extensionRootBlock, partialTraceRight]
    apply Finset.sum_congr rfl
    intro e _
    exact sqrtPSD_rowGram hω ((1, 1), e) ((0, 0), e)
  rw [htrace, hmarginal, bellEdge_reverseOffDiagonal]
  push_cast
  norm_num
  ring

theorem sqrtPSD_column_zero_of_diagonal {I : Type*} [Fintype I] [DecidableEq I]
    {X : Mat I} (hX : X.PosSemidef) {i : I} (hi : X i i = 0) (j : I) :
    sqrtPSD X j i = 0 := by
  have hgram : (sqrtPSD X)ᴴ * sqrtPSD X = X := by
    rw [sqrtPSD_conjTranspose, sqrtPSD_mul_self X hX]
  have hd := congrArg (fun Y : Mat I => Y i i) hgram
  rw [hi] at hd
  have hdot : star ((sqrtPSD X).col i) ⬝ᵥ (sqrtPSD X).col i = 0 := by
    change (∑ k : I, star (sqrtPSD X k i) * sqrtPSD X k i) = 0
    simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply] using hd
  have hzero := dotProduct_star_self_eq_zero.mp hdot
  have hcol := congr_fun hzero j
  change sqrtPSD X j i = 0 at hcol
  exact hcol

theorem sqrtPSD_row_zero_of_diagonal {I : Type*} [Fintype I] [DecidableEq I]
    {X : Mat I} (hX : X.PosSemidef) {i : I} (hi : X i i = 0) (j : I) :
    sqrtPSD X i j = 0 := by
  have hh := congr_fun (congr_fun (sqrtPSD_conjTranspose X) i) j
  simp only [Matrix.conjTranspose_apply, sqrtPSD_column_zero_of_diagonal hX hi j,
    star_zero] at hh
  exact hh.symm

theorem extensionRoot_offParity_row {c : ℝ} {ω : Mat (AB × E)}
    (hω : ω.PosSemidef) (hmarginal : partialTraceRight ω = bellEdge c)
    (x : AB) (hx : x.1 ≠ x.2) (e : E) (j : AB × E) : sqrtPSD ω (x, e) j = 0 :=
  sqrtPSD_row_zero_of_diagonal hω
    (extension_offParity_diagonal hω hmarginal x hx e) j

theorem extensionConditionalE_average {c : ℝ} {ω : Mat (AB × E)}
    (hω : ω.PosSemidef) (hmarginal : partialTraceRight ω = bellEdge c) :
    (1 / 2 : ℝ) • (extensionConditionalE ω 0 + extensionConditionalE ω 1) = marginalE ω := by
  have h01 (i j : E) : ω ((0, 1), i) ((0, 1), j) = 0 :=
    extension_offParity_row hω hmarginal (0, 1) (by decide) i ((0, 1), j)
  have h10 (i j : E) : ω ((1, 0), i) ((1, 0), j) = 0 :=
    extension_offParity_row hω hmarginal (1, 0) (by decide) i ((1, 0), j)
  rw [extensionConditionalE, extensionConditionalE,
    extensionRootBlock_leftGram ω hω 0, extensionRootBlock_leftGram ω hω 1]
  ext i j
  simp [marginalE, partialTraceLeft, Fintype.sum_prod_type, Fin.sum_univ_two,
    Matrix.submatrix_apply, Complex.real_smul, h01, h10] <;> ring

theorem extensionConditionalG_average {c : ℝ} {ω : Mat (AB × E)}
    (hω : ω.PosSemidef) (hmarginal : partialTraceRight ω = bellEdge c) :
    (1 / 2 : ℝ) • (extensionConditionalG ω 0 + extensionConditionalG ω 1) = ω := by
  have h01 (e : E) (j : AB × E) : sqrtPSD ω ((0, 1), e) j = 0 :=
    extensionRoot_offParity_row hω hmarginal (0, 1) (by decide) e j
  have h10 (e : E) (j : AB × E) : sqrtPSD ω ((1, 0), e) j = 0 :=
    extensionRoot_offParity_row hω hmarginal (1, 0) (by decide) e j
  have hsum : (extensionRootBlock ω 0)ᴴ * extensionRootBlock ω 0 +
      (extensionRootBlock ω 1)ᴴ * extensionRootBlock ω 1 = (sqrtPSD ω)ᴴ * sqrtPSD ω := by
    ext i j
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, extensionRootBlock,
      Fintype.sum_prod_type, Fin.sum_univ_two, h01, h10]
  unfold extensionConditionalG
  rw [← smul_add, smul_smul]
  norm_num
  rw [hsum, sqrtPSD_conjTranspose, sqrtPSD_mul_self ω hω]

theorem extension_marginalAE_flag {c : ℝ} {ω : Mat (AB × E)}
    (hω : ω.PosSemidef) (hm : partialTraceRight ω = bellEdge c) :
    marginalAE ω = pairFlagBlock
      (extensionConditionalE ω 0) (extensionConditionalE ω 1) := by
  have h01 (e : E) (y : AB × E) : ω ((0, 1), e) y = 0 :=
    extension_offParity_row hω hm (0, 1) (by decide) e y
  have h10 (e : E) (y : AB × E) : ω ((1, 0), e) y = 0 :=
    extension_offParity_row hω hm (1, 0) (by decide) e y
  have h01c (e : E) (y : AB × E) : ω y ((0, 1), e) = 0 :=
    extension_offParity_column hω hm (0, 1) (by decide) e y
  have h10c (e : E) (y : AB × E) : ω y ((1, 0), e) = 0 :=
    extension_offParity_column hω hm (1, 0) (by decide) e y
  ext x y
  rcases x with ⟨a, i⟩
  rcases y with ⟨b, j⟩
  fin_cases a <;> fin_cases b <;>
    simp [marginalAE, pairFlagBlock, matrixReindexHom, qubitSumEquiv,
      QuantumProver.SuperchannelDiscrimination.FlaggedStates.flagBlock,
      Matrix.reindex_apply, Matrix.submatrix, Matrix.fromBlocks,
      Fin.sum_univ_two, extensionConditionalE,
      extensionRootBlock_leftGram ω hω 0, extensionRootBlock_leftGram ω hω 1,
      h01, h10, h01c, h10c, Complex.real_smul] <;> ring

theorem extension_marginalBE_eq_AE {c : ℝ} {ω : Mat (AB × E)}
    (hω : ω.PosSemidef) (hm : partialTraceRight ω = bellEdge c) :
    marginalBE ω = marginalAE ω := by
  have h01 (e : E) (y : AB × E) : ω ((0, 1), e) y = 0 :=
    extension_offParity_row hω hm (0, 1) (by decide) e y
  have h10 (e : E) (y : AB × E) : ω ((1, 0), e) y = 0 :=
    extension_offParity_row hω hm (1, 0) (by decide) e y
  have h01c (e : E) (y : AB × E) : ω y ((0, 1), e) = 0 :=
    extension_offParity_column hω hm (0, 1) (by decide) e y
  have h10c (e : E) (y : AB × E) : ω y ((1, 0), e) = 0 :=
    extension_offParity_column hω hm (1, 0) (by decide) e y
  ext x y
  rcases x with ⟨a, i⟩
  rcases y with ⟨b, j⟩
  fin_cases a <;> fin_cases b <;>
    simp [marginalBE, marginalAE, Fin.sum_univ_two, h01, h10, h01c, h10c]

theorem extension_marginalBE_flag {c : ℝ} {ω : Mat (AB × E)}
    (hω : ω.PosSemidef) (hm : partialTraceRight ω = bellEdge c) :
    marginalBE ω = pairFlagBlock
      (extensionConditionalE ω 0) (extensionConditionalE ω 1) := by
  rw [extension_marginalBE_eq_AE hω hm, extension_marginalAE_flag hω hm]

theorem extensionConditionalG_entropy_eq_E (ω : Mat (AB × E)) (q : Qubit) :
    entropyBits (extensionConditionalG ω q) =
      entropyBits (extensionConditionalE ω q) := by
  let M := extensionRootBlock ω q
  have hgram : entropyBits (Mᴴ * M) = entropyBits (M * Mᴴ) :=
    entropyBits_oppositeGrams M
  change entropyBits ((2 : ℝ) • (Mᴴ * M)) = entropyBits ((2 : ℝ) • (M * Mᴴ))
  calc
    entropyBits ((2 : ℝ) • (Mᴴ * M)) =
        2 * entropyBits (Mᴴ * M) -
          (2 * Real.log 2 / Real.log 2) * (Mᴴ * M).trace.re :=
      QuantumProver.SuperchannelDiscrimination.FlaggedStates.entropyBits_smul 2
        (Matrix.posSemidef_conjTranspose_mul_self M)
    _ = 2 * entropyBits (M * Mᴴ) -
          (2 * Real.log 2 / Real.log 2) * (M * Mᴴ).trace.re := by
      rw [hgram, Matrix.trace_mul_comm Mᴴ M]
    _ = entropyBits ((2 : ℝ) • (M * Mᴴ)) :=
      (QuantumProver.SuperchannelDiscrimination.FlaggedStates.entropyBits_smul 2
        (Matrix.posSemidef_self_mul_conjTranspose M)).symm

theorem extension_halfCMI_average_pairCost {c : ℝ} {ω : Mat (AB × E)}
    (hω : ω.PosSemidef) (hm : partialTraceRight ω = bellEdge c) :
    halfCMI ω =
      (pairCost (extensionConditionalE ω 0) (extensionConditionalE ω 1) +
       pairCost (extensionConditionalG ω 0) (extensionConditionalG ω 1)) / 2 := by
  have h0 := extensionConditionalE_isDensity hω hm (0 : Qubit)
  have h1 := extensionConditionalE_isDensity hω hm (1 : Qubit)
  have heavg := congrArg entropyBits (extensionConditionalE_average hω hm)
  have hgavg := congrArg entropyBits (extensionConditionalG_average hω hm)
  simp only [halfCMI, pairCost, binaryHolevo,
    extension_marginalAE_flag hω hm, extension_marginalBE_flag hω hm,
    entropyBits_pairFlagBlock h0 h1, heavg, hgavg,
    extensionConditionalG_entropy_eq_E ω 0, extensionConditionalG_entropy_eq_E ω 1]
  ring

theorem extension_conditional_affinity_sum_ge {c : ℝ} {ω : Mat (AB × E)}
    (hω : ω.PosSemidef) (hm : partialTraceRight ω = bellEdge c) :
    2 * c ≤
      affinity (extensionConditionalE ω 0) (extensionConditionalE ω 1) +
      affinity (extensionConditionalG ω 0) (extensionConditionalG ω 1) := by
  have ho : 2 * (extensionRootBlock ω 1 * (extensionRootBlock ω 0)ᴴ).trace =
      (c : ℂ) := by
    simpa [Complex.real_smul] using extensionRootBlocks_overlap hω hm
  have h := QuantumProver.MatrixAnalysis.AbsoluteHS.conditional_marginal_affinity
    (extensionRootBlock ω 0) (extensionRootBlock ω 1) c ho
  simpa only [extensionConditionalE, extensionConditionalG, affinity, sqrtPSD,
    QuantumProver.MatrixAnalysis.Affinity.affinity, QuantumProver.MatrixAnalysis.Affinity.sqrtPSD, two_smul] using h

def trivialExtension (A : Mat AB) : Mat (AB × Fin 1) :=
  A.submatrix (fun x => x.1) (fun x => x.1)

theorem trivialExtension_trace (A : Mat AB) : (trivialExtension A).trace = A.trace := by
  simp [trivialExtension, Matrix.trace, Fintype.sum_prod_type]

theorem trivialExtension_isDensity {A : Mat AB} (hA : IsDensity A) :
    IsDensity (trivialExtension A) :=
  ⟨hA.1.submatrix (fun x : AB × Fin 1 => x.1), (trivialExtension_trace A).trans hA.2⟩

theorem trivialExtension_partialTrace (A : Mat AB) :
    partialTraceRight (trivialExtension A) = A := by
  ext i j
  simp [partialTraceRight, trivialExtension]

theorem extensionCosts_nonempty {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    (extensionCosts c).Nonempty := by
  let ω : Density (AB × Fin 1) :=
    ⟨trivialExtension (bellEdge c), trivialExtension_isDensity (bellEdge_isDensity hc0 hc1)⟩
  refine ⟨halfCMI ω.val, 1, by norm_num, ω, ?_, rfl⟩
  exact trivialExtension_partialTrace (bellEdge c)

theorem physical_lower_of_every_extension {c L : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hpoint : ∀ n : ℕ, 0 < n → ∀ ω : Density (AB × Fin n),
      partialTraceRight ω.val = bellEdge c → L ≤ halfCMI ω.val) :
    L ≤ squashedEntanglement c := by
  apply le_csInf (extensionCosts_nonempty hc0 hc1)
  rintro z ⟨n, hn, ω, hω, rfl⟩
  exact hpoint n hn ω hω

theorem squashedEntanglement_le_feasible {c : ℝ} (hb : BddBelow (extensionCosts c))
    {n : ℕ} (hn : 0 < n) (ω : Density (AB × Fin n))
    (hω : partialTraceRight ω.val = bellEdge c) :
    squashedEntanglement c ≤ halfCMI ω.val := by
  exact csInf_le hb ⟨n, hn, ω, hω, rfl⟩

theorem physical_upper_of_one_extension {c U : ℝ} (hb : BddBelow (extensionCosts c))
    {n : ℕ} (hn : 0 < n) (ω : Density (AB × Fin n))
    (hω : partialTraceRight ω.val = bellEdge c) (hU : halfCMI ω.val ≤ U) :
    squashedEntanglement c ≤ U :=
  (squashedEntanglement_le_feasible hb hn ω hω).trans hU

def PhysicalPairInfimumStatement : Prop :=
  ∀ c : ℝ, 0 < c → c ≤ 1 → squashedEntanglement c = positivePairInfimum c

def PhysicalAdditiveFlagCostStatement : Prop :=
  ∀ n : ℕ, 0 < n → ∀ A B : Density (Fin n),
    0 < affinity A.val B.val →
    pairCost A.val B.val ≥
      phi ((rootFidelity A.val B.val) ^ 2) -
      phi ((rootFidelity A.val B.val) ^ 2 - (affinity A.val B.val) ^ 2) +
      (rootFidelity A.val B.val -
        Real.sqrt (rootFidelity A.val B.val * affinity A.val B.val)) ^ 2 /
        (4 * Real.log 2)

def leadingEdgeTerm (c : ℝ) : ℝ := (c ^ 2 / 2) * (Real.log (1 / c) / Real.log 2)

def PhysicalAsymptoticStatement : Prop :=
  Asymptotics.IsBigO (nhdsWithin 0 (Ioi 0))
    (fun c : ℝ => squashedEntanglement c - leadingEdgeTerm c) (fun c : ℝ => c ^ 2) ∧
  Asymptotics.IsBigO (nhdsWithin 0 (Ioi 0))
    (fun c : ℝ => phi (c ^ 2) - squashedEntanglement c) (fun c : ℝ => c ^ 2)

def BellEdgeTheorem : Prop :=
  PhysicalPairInfimumStatement ∧ UniversalHolevoFidelityLoss ∧
    PhysicalAdditiveFlagCostStatement ∧ PhysicalSmallCoherenceBound ∧
    PhysicalAsymptoticStatement

end QuantumProver.BellDiagonalSquashedEntanglement

namespace QuantumProver.BellDiagonalSquashedEntanglement

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

theorem matrixReindexHom_posSemidef (e : I ≃ J) {A : Mat I}
    (hA : A.PosSemidef) : (matrixReindexHom e A).PosSemidef :=
  hA.submatrix e.symm

theorem matrixReindexHom_isDensity (e : I ≃ J) {A : Mat I}
    (hA : IsDensity A) : IsDensity (matrixReindexHom e A) :=
  ⟨matrixReindexHom_posSemidef e hA.1, (matrixReindexHom_trace e A).trans hA.2⟩

theorem sqrtPSD_reindex (e : I ≃ J) {A : Mat I} (hA : A.PosSemidef) :
    sqrtPSD (matrixReindexHom e A) = matrixReindexHom e (sqrtPSD A) := by
  apply CFC.sqrt_unique
  · rw [← map_mul, sqrtPSD_mul_self A hA]
  · exact (matrixReindexHom_posSemidef e
      (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A))).nonneg

theorem affinity_reindex (e : I ≃ J) {A B : Mat I}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    affinity (matrixReindexHom e A) (matrixReindexHom e B) = affinity A B := by
  unfold affinity
  rw [sqrtPSD_reindex e hA, sqrtPSD_reindex e hB, ← map_mul,
    matrixReindexHom_trace]

theorem pairCost_reindex (e : I ≃ J) {A B : Mat I}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    pairCost (matrixReindexHom e A) (matrixReindexHom e B) = pairCost A B := by
  unfold pairCost binaryHolevo
  rw [← map_add, ← map_smul,
    entropyBits_reindex e ((hA.add hB).smul (show (0 : ℝ) ≤ 1 / 2 by norm_num)).isHermitian,
    entropyBits_reindex e hA.isHermitian, entropyBits_reindex e hB.isHermitian]

variable {E : Type*} [Fintype E] [DecidableEq E]

def cmiIndexEquiv (E : Type*) : (AB × E) ≃ (Qubit × (E × Qubit)) where
  toFun x := (x.1.1, (x.2, x.1.2))
  invFun x := ((x.1, x.2.2), x.2.1)
  left_inv x := by rcases x with ⟨⟨a, b⟩, e⟩; rfl
  right_inv x := by rcases x with ⟨a, ⟨e, b⟩⟩; rfl

def cmiReindex (ω : Mat (AB × E)) : Mat (Qubit × (E × Qubit)) :=
  matrixReindexHom (cmiIndexEquiv E) ω

theorem cmiReindex_marginalAB (ω : Mat (AB × E)) :
    QuantumProver.QuantumEntropy.marginalAB (cmiReindex ω) = marginalAE ω := by
  ext x y
  rfl

theorem cmiReindex_marginalBC (ω : Mat (AB × E)) :
    QuantumProver.QuantumEntropy.marginalBC (cmiReindex ω) =
      matrixReindexHom (Equiv.prodComm Qubit E) (marginalBE ω) := by
  ext x y
  rfl

theorem cmiReindex_marginalB (ω : Mat (AB × E)) :
    QuantumProver.QuantumEntropy.marginalB (cmiReindex ω) = marginalE ω := by
  ext e f
  simp [QuantumProver.QuantumEntropy.marginalB, QuantumProver.QuantumEntropy.partialTrace_left,
    cmiReindex_marginalAB, marginalAE, marginalE, partialTraceLeft,
    Fintype.sum_prod_type]

theorem marginalBE_posSemidef {ω : Mat (AB × E)} (hω : ω.PosSemidef) :
    (marginalBE ω).PosSemidef := by
  have heq : marginalBE ω =
      ∑ a : Qubit, ω.submatrix (fun x : Qubit × E => ((a, x.1), x.2))
        (fun x : Qubit × E => ((a, x.1), x.2)) := by
    ext x y
    exact (Matrix.sum_apply x y Finset.univ
      (fun a : Qubit => ω.submatrix (fun x : Qubit × E => ((a, x.1), x.2))
        (fun x : Qubit × E => ((a, x.1), x.2)))).symm
  rw [heq]
  exact Matrix.posSemidef_sum _
    (fun a _ => hω.submatrix (fun x : Qubit × E => ((a, x.1), x.2)))

theorem halfCMI_nonneg {ω : Mat (AB × E)} (hω : ω.PosSemidef) :
    0 ≤ halfCMI ω := by
  have h := QuantumProver.QuantumEntropy.strongSubadditivity_of_posSemidef
    (matrixReindexHom_posSemidef (cmiIndexEquiv E) hω)
  change entropyBits (QuantumProver.QuantumEntropy.marginalB (cmiReindex ω)) +
      entropyBits (cmiReindex ω) ≤
    entropyBits (QuantumProver.QuantumEntropy.marginalAB (cmiReindex ω)) +
      entropyBits (QuantumProver.QuantumEntropy.marginalBC (cmiReindex ω)) at h
  rw [cmiReindex_marginalB, cmiReindex_marginalAB, cmiReindex_marginalBC,
    entropyBits_reindex (Equiv.prodComm Qubit E) (marginalBE_posSemidef hω).isHermitian,
    cmiReindex, entropyBits_reindex (cmiIndexEquiv E) hω.isHermitian] at h
  unfold halfCMI
  linarith only [h]

theorem pairCost_nonneg {A B : Mat E} (hA : IsDensity A) (hB : IsDensity B) :
    0 ≤ pairCost A B := by
  rw [← pairGram_halfCMI hA hB]
  exact halfCMI_nonneg (pairGram_posSemidef A B)

end QuantumProver.BellDiagonalSquashedEntanglement

namespace QuantumProver.BellDiagonalSquashedEntanglement

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

def weightedPairBlock (p : ℝ) (A : Mat I) (B : Mat J) : Mat (I ⊕ J) :=
  QuantumProver.SuperchannelDiscrimination.FlaggedStates.flagBlock (p • A) ((1 - p) • B)

theorem sqrtPSD_flagBlock {A : Mat I} {B : Mat J}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    sqrtPSD (QuantumProver.SuperchannelDiscrimination.FlaggedStates.flagBlock A B) =
      QuantumProver.SuperchannelDiscrimination.FlaggedStates.flagBlock (sqrtPSD A) (sqrtPSD B) := by
  apply CFC.sqrt_unique
  · rw [QuantumProver.SuperchannelDiscrimination.FlaggedStates.flagBlock_mul,
      sqrtPSD_mul_self A hA, sqrtPSD_mul_self B hB]
  · exact (QuantumProver.SuperchannelDiscrimination.FlaggedStates.flagBlock_posSemidef
      (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A))
      (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg B))).nonneg

theorem affinity_flagBlock {A₀ A₁ : Mat I} {B₀ B₁ : Mat J}
    (hA₀ : A₀.PosSemidef) (hA₁ : A₁.PosSemidef)
    (hB₀ : B₀.PosSemidef) (hB₁ : B₁.PosSemidef) :
    affinity
        (QuantumProver.SuperchannelDiscrimination.FlaggedStates.flagBlock A₀ B₀)
        (QuantumProver.SuperchannelDiscrimination.FlaggedStates.flagBlock A₁ B₁) =
      affinity A₀ A₁ + affinity B₀ B₁ := by
  unfold affinity
  rw [sqrtPSD_flagBlock hA₀ hB₀, sqrtPSD_flagBlock hA₁ hB₁,
    QuantumProver.SuperchannelDiscrimination.FlaggedStates.flagBlock_mul,
    QuantumProver.SuperchannelDiscrimination.FlaggedStates.flagBlock_trace,
    Complex.add_re]

theorem affinity_smul_nonneg_matrix (p : ℝ) (hp : 0 ≤ p)
    {A B : Mat I} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    affinity (p • A) (p • B) = p * affinity A B := by
  simpa only [affinity, sqrtPSD, QuantumProver.MatrixAnalysis.Affinity.affinity,
    QuantumProver.MatrixAnalysis.Affinity.sqrtPSD] using
    QuantumProver.MatrixAnalysis.AbsoluteHS.affinity_smul_nonneg p hp hA hB

theorem weightedPairBlock_isDensity {p : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    {A : Mat I} {B : Mat J} (hA : IsDensity A) (hB : IsDensity B) :
    IsDensity (weightedPairBlock p A B) := by
  refine ⟨QuantumProver.SuperchannelDiscrimination.FlaggedStates.flagBlock_posSemidef
    (hA.1.smul hp₀) (hB.1.smul (sub_nonneg.mpr hp₁)), ?_⟩
  simp only [weightedPairBlock,
    QuantumProver.SuperchannelDiscrimination.FlaggedStates.flagBlock_trace,
    Matrix.trace_smul, hA.2, hB.2]
  simp [Complex.real_smul]

theorem weightedPairBlock_average (p : ℝ) (A₀ A₁ : Mat I) (B₀ B₁ : Mat J) :
    (1 / 2 : ℝ) •
        (weightedPairBlock p A₀ B₀ + weightedPairBlock p A₁ B₁) =
      weightedPairBlock p ((1 / 2 : ℝ) • (A₀ + A₁))
        ((1 / 2 : ℝ) • (B₀ + B₁)) := by
  ext x y
  cases x <;> cases y <;>
    simp [weightedPairBlock,
      QuantumProver.SuperchannelDiscrimination.FlaggedStates.flagBlock,
      Matrix.fromBlocks, Complex.real_smul] <;> ring

theorem entropyBits_weightedPairBlock {p : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    {A : Mat I} {B : Mat J} (hA : IsDensity A) (hB : IsDensity B) :
    entropyBits (weightedPairBlock p A B) =
      QuantumProver.SuperchannelDiscrimination.FlaggedStates.flagEntropyBits p +
        p * entropyBits A + (1 - p) * entropyBits B := by
  exact QuantumProver.SuperchannelDiscrimination.FlaggedStates.entropyBits_flagged_density
    hA hB hp₀ hp₁

theorem pairCost_weightedPairBlock {p : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    {A₀ A₁ : Mat I} {B₀ B₁ : Mat J}
    (hA₀ : IsDensity A₀) (hA₁ : IsDensity A₁)
    (hB₀ : IsDensity B₀) (hB₁ : IsDensity B₁) :
    pairCost (weightedPairBlock p A₀ B₀) (weightedPairBlock p A₁ B₁) =
      p * pairCost A₀ A₁ + (1 - p) * pairCost B₀ B₁ := by
  unfold pairCost binaryHolevo
  rw [weightedPairBlock_average,
    entropyBits_weightedPairBlock hp₀ hp₁
      (equalPriorAverage_isDensity hA₀ hA₁) (equalPriorAverage_isDensity hB₀ hB₁),
    entropyBits_weightedPairBlock hp₀ hp₁ hA₀ hB₀,
    entropyBits_weightedPairBlock hp₀ hp₁ hA₁ hB₁]
  ring

theorem affinity_weightedPairBlock {p : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    {A₀ A₁ : Mat I} {B₀ B₁ : Mat J}
    (hA₀ : A₀.PosSemidef) (hA₁ : A₁.PosSemidef)
    (hB₀ : B₀.PosSemidef) (hB₁ : B₁.PosSemidef) :
    affinity (weightedPairBlock p A₀ B₀) (weightedPairBlock p A₁ B₁) =
      p * affinity A₀ A₁ + (1 - p) * affinity B₀ B₁ := by
  rw [weightedPairBlock, weightedPairBlock,
    affinity_flagBlock (hA₀.smul hp₀) (hA₁.smul hp₀)
      (hB₀.smul (sub_nonneg.mpr hp₁)) (hB₁.smul (sub_nonneg.mpr hp₁)),
    affinity_smul_nonneg_matrix p hp₀ hA₀ hA₁,
    affinity_smul_nonneg_matrix (1 - p) (sub_nonneg.mpr hp₁) hB₀ hB₁]

variable {E : Type*} [Fintype E] [DecidableEq E]

def combinedConditionalPair (ω : Mat (AB × E)) (q : Qubit) : Mat (E ⊕ (AB × E)) :=
  weightedPairBlock (1 / 2) (extensionConditionalE ω q) (extensionConditionalG ω q)

theorem combinedConditionalPair_isDensity {c : ℝ} {ω : Mat (AB × E)}
    (hω : ω.PosSemidef) (hm : partialTraceRight ω = bellEdge c) (q : Qubit) :
    IsDensity (combinedConditionalPair ω q) :=
  weightedPairBlock_isDensity (by norm_num) (by norm_num)
    (extensionConditionalE_isDensity hω hm q) (extensionConditionalG_isDensity hω hm q)

theorem combinedConditionalPair_cost {c : ℝ} {ω : Mat (AB × E)}
    (hω : ω.PosSemidef) (hm : partialTraceRight ω = bellEdge c) :
    pairCost (combinedConditionalPair ω 0) (combinedConditionalPair ω 1) = halfCMI ω := by
  rw [combinedConditionalPair, combinedConditionalPair,
    pairCost_weightedPairBlock (by norm_num) (by norm_num)
      (extensionConditionalE_isDensity hω hm 0) (extensionConditionalE_isDensity hω hm 1)
      (extensionConditionalG_isDensity hω hm 0) (extensionConditionalG_isDensity hω hm 1),
    extension_halfCMI_average_pairCost hω hm]
  ring

theorem combinedConditionalPair_affinity_ge {c : ℝ} {ω : Mat (AB × E)}
    (hω : ω.PosSemidef) (hm : partialTraceRight ω = bellEdge c) :
    c ≤ affinity (combinedConditionalPair ω 0) (combinedConditionalPair ω 1) := by
  rw [combinedConditionalPair, combinedConditionalPair,
    affinity_weightedPairBlock (by norm_num) (by norm_num)
      (extensionConditionalE_isDensity hω hm 0).1
      (extensionConditionalE_isDensity hω hm 1).1
      (extensionConditionalG_isDensity hω hm 0).1
      (extensionConditionalG_isDensity hω hm 1).1]
  have h := extension_conditional_affinity_sum_ge hω hm
  linarith

abbrev OrthogonalPairIndex := Unit ⊕ Unit

def orthogonalPairZero : Mat OrthogonalPairIndex :=
  QuantumProver.SuperchannelDiscrimination.FlaggedStates.flagBlock
    (1 : Mat Unit) (0 : Mat Unit)

def orthogonalPairOne : Mat OrthogonalPairIndex :=
  QuantumProver.SuperchannelDiscrimination.FlaggedStates.flagBlock
    (0 : Mat Unit) (1 : Mat Unit)

theorem orthogonalPairZero_isDensity : IsDensity orthogonalPairZero := by
  refine ⟨QuantumProver.SuperchannelDiscrimination.FlaggedStates.flagBlock_posSemidef
    (Matrix.nonneg_iff_posSemidef.mp (show 0 ≤ (1 : Mat Unit) from zero_le_one))
    (Matrix.nonneg_iff_posSemidef.mp le_rfl), ?_⟩
  rw [orthogonalPairZero,
    QuantumProver.SuperchannelDiscrimination.FlaggedStates.flagBlock_trace]
  simp [Matrix.trace]

theorem orthogonalPairOne_isDensity : IsDensity orthogonalPairOne := by
  refine ⟨QuantumProver.SuperchannelDiscrimination.FlaggedStates.flagBlock_posSemidef
    (Matrix.nonneg_iff_posSemidef.mp le_rfl)
    (Matrix.nonneg_iff_posSemidef.mp (show 0 ≤ (1 : Mat Unit) from zero_le_one)), ?_⟩
  rw [orthogonalPairOne,
    QuantumProver.SuperchannelDiscrimination.FlaggedStates.flagBlock_trace]
  simp [Matrix.trace]

theorem entropyBits_one_matrix (T : Type*) [Fintype T] [DecidableEq T] :
    entropyBits (1 : Mat T) = 0 := by
  simp [entropyBits, QuantumProver.SuperchannelDiscrimination.FlaggedStates.entropyBits]

theorem entropyBits_zero_matrix (T : Type*) [Fintype T] [DecidableEq T] :
    entropyBits (0 : Mat T) = 0 := by
  simp [entropyBits, QuantumProver.SuperchannelDiscrimination.FlaggedStates.entropyBits]

theorem orthogonalPair_entropies :
    entropyBits orthogonalPairZero = 0 ∧ entropyBits orthogonalPairOne = 0 := by
  have h0 : (0 : Mat Unit).PosSemidef := Matrix.nonneg_iff_posSemidef.mp le_rfl
  have h1 : (1 : Mat Unit).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp (show 0 ≤ (1 : Mat Unit) from zero_le_one)
  constructor
  · change QuantumProver.SuperchannelDiscrimination.FlaggedStates.entropyBits
      (QuantumProver.SuperchannelDiscrimination.FlaggedStates.flagBlock
        (1 : Mat Unit) (0 : Mat Unit)) = 0
    rw [QuantumProver.SuperchannelDiscrimination.FlaggedStates.entropyBits_flagBlock h1 h0]
    simp [QuantumProver.SuperchannelDiscrimination.FlaggedStates.entropyBits]
  · change QuantumProver.SuperchannelDiscrimination.FlaggedStates.entropyBits
      (QuantumProver.SuperchannelDiscrimination.FlaggedStates.flagBlock
        (0 : Mat Unit) (1 : Mat Unit)) = 0
    rw [QuantumProver.SuperchannelDiscrimination.FlaggedStates.entropyBits_flagBlock h0 h1]
    simp [QuantumProver.SuperchannelDiscrimination.FlaggedStates.entropyBits]

theorem orthogonalPair_affinity : affinity orthogonalPairZero orthogonalPairOne = 0 := by
  have h0 : (0 : Mat Unit).PosSemidef := Matrix.nonneg_iff_posSemidef.mp le_rfl
  have h1 : (1 : Mat Unit).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp (show 0 ≤ (1 : Mat Unit) from zero_le_one)
  rw [orthogonalPairZero, orthogonalPairOne, affinity_flagBlock h1 h0 h0 h1]
  simp [affinity, sqrtPSD]

theorem orthogonalPair_average_entropy :
    entropyBits ((1 / 2 : ℝ) • (orthogonalPairZero + orthogonalPairOne)) = 1 := by
  have heq : (1 / 2 : ℝ) • (orthogonalPairZero + orthogonalPairOne) =
      weightedPairBlock (1 / 2) (1 : Mat Unit) (1 : Mat Unit) := by
    ext x y
    cases x <;> cases y <;>
      simp [weightedPairBlock, orthogonalPairZero, orthogonalPairOne,
        QuantumProver.SuperchannelDiscrimination.FlaggedStates.flagBlock, Matrix.fromBlocks] <;> norm_num
  rw [heq, entropyBits_weightedPairBlock (by norm_num) (by norm_num)
    (show IsDensity (1 : Mat Unit) from
      ⟨Matrix.nonneg_iff_posSemidef.mp zero_le_one, by simp [Matrix.trace]⟩)
    (show IsDensity (1 : Mat Unit) from
      ⟨Matrix.nonneg_iff_posSemidef.mp zero_le_one, by simp [Matrix.trace]⟩)]
  simpa only [entropyBits_one_matrix, mul_zero, add_zero] using flagEntropyBits_half

theorem orthogonalPair_cost : pairCost orthogonalPairZero orthogonalPairOne = 0 := by
  rw [pairCost, binaryHolevo, orthogonalPair_entropies.1,
    orthogonalPair_entropies.2, orthogonalPair_average_entropy]
  norm_num

def exactAffinityAdjustedZero (c : ℝ) (A B : Mat I) : Mat (I ⊕ OrthogonalPairIndex) :=
  weightedPairBlock (c / affinity A B) A orthogonalPairZero

def exactAffinityAdjustedOne (c : ℝ) (A B : Mat I) : Mat (I ⊕ OrthogonalPairIndex) :=
  weightedPairBlock (c / affinity A B) B orthogonalPairOne

theorem exactAffinityAdjustment_weight {c : ℝ} {A B : Mat I}
    (hc : 0 < c) (ha : c ≤ affinity A B) :
    0 ≤ c / affinity A B ∧ c / affinity A B ≤ 1 := by
  have hapos : 0 < affinity A B := lt_of_lt_of_le hc ha
  exact ⟨div_nonneg hc.le hapos.le, (div_le_one hapos).mpr ha⟩

theorem exactAffinityAdjusted_isDensity {c : ℝ} {A B : Mat I}
    (hA : IsDensity A) (hB : IsDensity B) (hc : 0 < c) (ha : c ≤ affinity A B) :
    IsDensity (exactAffinityAdjustedZero c A B) ∧
      IsDensity (exactAffinityAdjustedOne c A B) := by
  obtain ⟨hp0, hp1⟩ := exactAffinityAdjustment_weight hc ha
  exact ⟨weightedPairBlock_isDensity hp0 hp1 hA orthogonalPairZero_isDensity,
    weightedPairBlock_isDensity hp0 hp1 hB orthogonalPairOne_isDensity⟩

theorem exactAffinityAdjusted_affinity {c : ℝ} {A B : Mat I}
    (hA : IsDensity A) (hB : IsDensity B) (hc : 0 < c) (ha : c ≤ affinity A B) :
    affinity (exactAffinityAdjustedZero c A B) (exactAffinityAdjustedOne c A B) = c := by
  obtain ⟨hp0, hp1⟩ := exactAffinityAdjustment_weight hc ha
  rw [exactAffinityAdjustedZero, exactAffinityAdjustedOne,
    affinity_weightedPairBlock hp0 hp1 hA.1 hB.1
      orthogonalPairZero_isDensity.1 orthogonalPairOne_isDensity.1,
    orthogonalPair_affinity, mul_zero, add_zero]
  exact div_mul_cancel₀ c (ne_of_gt (lt_of_lt_of_le hc ha))

theorem exactAffinityAdjusted_cost {c : ℝ} {A B : Mat I}
    (hA : IsDensity A) (hB : IsDensity B) (hc : 0 < c) (ha : c ≤ affinity A B) :
    pairCost (exactAffinityAdjustedZero c A B) (exactAffinityAdjustedOne c A B) =
      (c / affinity A B) * pairCost A B := by
  obtain ⟨hp0, hp1⟩ := exactAffinityAdjustment_weight hc ha
  rw [exactAffinityAdjustedZero, exactAffinityAdjustedOne,
    pairCost_weightedPairBlock hp0 hp1 hA hB
      orthogonalPairZero_isDensity orthogonalPairOne_isDensity,
    orthogonalPair_cost, mul_zero, add_zero]

end QuantumProver.BellDiagonalSquashedEntanglement

namespace QuantumProver.BellDiagonalSquashedEntanglement

variable {E : Type*} [Fintype E] [DecidableEq E]

theorem every_extension_has_exact_pair {c : ℝ} {ω : Mat (AB × E)}
    (hc : 0 < c) (hω : ω.PosSemidef) (hm : partialTraceRight ω = bellEdge c) :
    ∃ z ∈ finitePairCosts c, z ≤ halfCMI ω := by
  let A := combinedConditionalPair ω 0
  let B := combinedConditionalPair ω 1
  have hA : IsDensity A := combinedConditionalPair_isDensity hω hm 0
  have hB : IsDensity B := combinedConditionalPair_isDensity hω hm 1
  have ha : c ≤ affinity A B := combinedConditionalPair_affinity_ge hω hm
  have hcost : pairCost A B = halfCMI ω := combinedConditionalPair_cost hω hm
  let T := (E ⊕ (AB × E)) ⊕ OrthogonalPairIndex
  let C : Mat T := exactAffinityAdjustedZero c A B
  let D : Mat T := exactAffinityAdjustedOne c A B
  have hCD : IsDensity C ∧ IsDensity D := exactAffinityAdjusted_isDensity hA hB hc ha
  have haff : affinity C D = c := exactAffinityAdjusted_affinity hA hB hc ha
  have hcostCD : pairCost C D = (c / affinity A B) * halfCMI ω := by
    rw [exactAffinityAdjusted_cost hA hB hc ha, hcost]
  have hle : pairCost C D ≤ halfCMI ω := by
    rw [hcostCD]
    exact mul_le_of_le_one_left (halfCMI_nonneg hω) (exactAffinityAdjustment_weight hc ha).2
  let e : T ≃ Fin (Fintype.card T) := Fintype.equivFin T
  let Cfin : Density (Fin (Fintype.card T)) :=
    ⟨matrixReindexHom e C, matrixReindexHom_isDensity e hCD.1⟩
  let Dfin : Density (Fin (Fintype.card T)) :=
    ⟨matrixReindexHom e D, matrixReindexHom_isDensity e hCD.2⟩
  have hn : 0 < Fintype.card T :=
    QuantumProver.ConditionalEntropy.ConditionalRange.isDensity_card_pos hCD.1
  refine ⟨pairCost Cfin.val Dfin.val,
    ⟨Fintype.card T, hn, Cfin, Dfin, ?_, rfl⟩, ?_⟩
  · exact (affinity_reindex e hCD.1.1 hCD.2.1).trans haff
  · exact (pairCost_reindex e hCD.1.1 hCD.2.1).le.trans hle

theorem extensionCosts_bddBelow (c : ℝ) : BddBelow (extensionCosts c) := by
  refine ⟨0, ?_⟩
  rintro z ⟨n, hn, ω, hm, rfl⟩
  exact halfCMI_nonneg ω.property.1

theorem finitePairCosts_bddBelow (c : ℝ) : BddBelow (finitePairCosts c) := by
  refine ⟨0, ?_⟩
  rintro z ⟨n, hn, A, B, haff, rfl⟩
  exact pairCost_nonneg A.property B.property

theorem finitePairCosts_nonempty {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) :
    (finitePairCosts c).Nonempty := by
  obtain ⟨z, n, hn, ω, hm, hz⟩ := extensionCosts_nonempty hc.le hc1
  obtain ⟨w, hw, hle⟩ := every_extension_has_exact_pair hc ω.property.1 hm
  exact ⟨w, hw⟩

theorem squashedEntanglement_nonneg {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    0 ≤ squashedEntanglement c := by
  apply le_csInf (extensionCosts_nonempty hc0 hc1)
  rintro z ⟨n, hn, ω, hm, rfl⟩
  exact halfCMI_nonneg ω.property.1

theorem positivePairInfimum_nonneg {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) :
    0 ≤ positivePairInfimum c := by
  apply le_csInf (finitePairCosts_nonempty hc hc1)
  rintro z ⟨n, hn, A, B, haff, rfl⟩
  exact pairCost_nonneg A.property B.property

theorem physicalPairInfimum_eq {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) :
    squashedEntanglement c = positivePairInfimum c := by
  apply le_antisymm
  · exact squashedEntanglement_le_positivePairInfimum
      (extensionCosts_bddBelow c) (finitePairCosts_nonempty hc hc1)
  · apply le_csInf (extensionCosts_nonempty hc.le hc1)
    rintro z ⟨n, hn, ω, hm, rfl⟩
    obtain ⟨w, hw, hle⟩ := every_extension_has_exact_pair hc ω.property.1 hm
    exact (csInf_le (finitePairCosts_bddBelow c) hw).trans hle

theorem physicalPairInfimumStatement_proved : PhysicalPairInfimumStatement := by
  intro c hc hc1
  exact physicalPairInfimum_eq hc hc1

end QuantumProver.BellDiagonalSquashedEntanglement

namespace QuantumProver.BellDiagonalSquashedEntanglement

theorem unitIdentity_isDensity : IsDensity (1 : Mat Unit) :=
  ⟨Matrix.PosSemidef.one, by simp [Matrix.trace]⟩

theorem sqrtPSD_unit_scalar (p : ℝ) (hp : 0 ≤ p) :
    sqrtPSD (p • (1 : Mat Unit)) = Real.sqrt p • (1 : Mat Unit) := by
  have h := QuantumProver.MatrixAnalysis.AbsoluteHS.sqrtPSD_smul_nonneg p hp
    (Matrix.PosSemidef.one (n := Unit) (R := ℂ))
  simpa [sqrtPSD, QuantumProver.MatrixAnalysis.Affinity.sqrtPSD] using h

theorem affinity_unit_scalars (p q : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q) :
    affinity (p • (1 : Mat Unit)) (q • (1 : Mat Unit)) =
      Real.sqrt p * Real.sqrt q := by
  unfold affinity
  rw [sqrtPSD_unit_scalar p hp, sqrtPSD_unit_scalar q hq]
  simp [Matrix.trace, Complex.real_smul, mul_comm]

def commutingPairZero (p : ℝ) : Mat OrthogonalPairIndex :=
  weightedPairBlock p (1 : Mat Unit) (1 : Mat Unit)

def commutingPairOne (p : ℝ) : Mat OrthogonalPairIndex :=
  weightedPairBlock (1 - p) (1 : Mat Unit) (1 : Mat Unit)

theorem commutingPair_isDensity {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    IsDensity (commutingPairZero p) ∧ IsDensity (commutingPairOne p) :=
  ⟨weightedPairBlock_isDensity hp0 hp1 unitIdentity_isDensity unitIdentity_isDensity,
    weightedPairBlock_isDensity (sub_nonneg.mpr hp1) (by linarith)
      unitIdentity_isDensity unitIdentity_isDensity⟩

theorem binaryEntropy_symm_matrix (p : ℝ) : binaryEntropy (1 - p) = binaryEntropy p := by
  have h : 1 - (1 - p) = p := by ring
  unfold binaryEntropy
  rw [h]
  congr 1
  ring

theorem commutingPair_entropies {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    entropyBits (commutingPairZero p) = binaryEntropy p ∧
      entropyBits (commutingPairOne p) = binaryEntropy p := by
  have h0 := entropyBits_weightedPairBlock hp0 hp1
    unitIdentity_isDensity unitIdentity_isDensity
  have h1 := entropyBits_weightedPairBlock (sub_nonneg.mpr hp1)
    (show 1 - p ≤ 1 by linarith) unitIdentity_isDensity unitIdentity_isDensity
  have hf (r : ℝ) : QuantumProver.SuperchannelDiscrimination.FlaggedStates.flagEntropyBits r =
      binaryEntropy r := rfl
  constructor
  · simpa only [commutingPairZero, entropyBits_one_matrix, hf, mul_zero, add_zero] using h0
  · simpa only [commutingPairOne, entropyBits_one_matrix, hf, mul_zero, add_zero,
      binaryEntropy_symm_matrix] using h1

theorem commutingPair_average (p : ℝ) :
    (1 / 2 : ℝ) • (commutingPairZero p + commutingPairOne p) =
      weightedPairBlock (1 / 2) (1 : Mat Unit) (1 : Mat Unit) := by
  ext x y
  cases x <;> cases y <;>
    simp [commutingPairZero, commutingPairOne, weightedPairBlock,
      QuantumProver.SuperchannelDiscrimination.FlaggedStates.flagBlock,
      Matrix.fromBlocks, Complex.real_smul] <;> ring

theorem commutingPair_cost {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    pairCost (commutingPairZero p) (commutingPairOne p) = binaryEntropy p := by
  have h := entropyBits_weightedPairBlock (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    (show (1 / 2 : ℝ) ≤ 1 by norm_num) unitIdentity_isDensity unitIdentity_isDensity
  have hm : entropyBits (weightedPairBlock (1 / 2) (1 : Mat Unit) (1 : Mat Unit)) = 1 := by
    simpa only [entropyBits_one_matrix, flagEntropyBits_half, mul_zero, add_zero] using h
  rw [pairCost, binaryHolevo, commutingPair_average,
    (commutingPair_entropies hp0 hp1).1, (commutingPair_entropies hp0 hp1).2, hm]
  ring

theorem commutingPair_affinity {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    affinity (commutingPairZero p) (commutingPairOne p) =
      2 * Real.sqrt (p * (1 - p)) := by
  have hq0 : 0 ≤ 1 - p := sub_nonneg.mpr hp1
  have hq1 : 0 ≤ 1 - (1 - p) := by linarith
  unfold commutingPairZero commutingPairOne weightedPairBlock
  rw [affinity_flagBlock (Matrix.PosSemidef.one.smul hp0)
      (Matrix.PosSemidef.one.smul hq0) (Matrix.PosSemidef.one.smul hq0)
      (Matrix.PosSemidef.one.smul hq1),
    affinity_unit_scalars p (1 - p) hp0 hq0,
    affinity_unit_scalars (1 - p) (1 - (1 - p)) hq0 hq1]
  have heq : 1 - (1 - p) = p := by ring
  rw [heq, Real.sqrt_mul hp0]
  ring

def formationPrior (c : ℝ) : ℝ := (1 + Real.sqrt (1 - c ^ 2)) / 2

theorem formationPrior_bounds {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    0 ≤ formationPrior c ∧ formationPrior c ≤ 1 := by
  have hroot : Real.sqrt (1 - c ^ 2) ≤ 1 :=
    Real.sqrt_le_one.mpr (by nlinarith [sq_nonneg c])
  unfold formationPrior
  constructor <;> nlinarith [Real.sqrt_nonneg (1 - c ^ 2)]

theorem formationPrior_product {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    formationPrior c * (1 - formationPrior c) = c ^ 2 / 4 := by
  have hnonneg : 0 ≤ 1 - c ^ 2 := by nlinarith
  have hroot := Real.sq_sqrt hnonneg
  unfold formationPrior
  nlinarith

theorem formationPair_affinity {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    affinity (commutingPairZero (formationPrior c))
      (commutingPairOne (formationPrior c)) = c := by
  obtain ⟨hp0, hp1⟩ := formationPrior_bounds hc0 hc1
  rw [commutingPair_affinity hp0 hp1, formationPrior_product hc0 hc1]
  have hs : Real.sqrt (c ^ 2 / 4) = c / 2 := by
    apply (Real.sqrt_eq_iff_mul_self_eq (by positivity) (by positivity)).mpr
    ring
  rw [hs]
  ring

theorem formationPair_cost {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    pairCost (commutingPairZero (formationPrior c))
      (commutingPairOne (formationPrior c)) = phi (c ^ 2) := by
  obtain ⟨hp0, hp1⟩ := formationPrior_bounds hc0 hc1
  exact commutingPair_cost hp0 hp1

theorem physical_formation_upper {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    squashedEntanglement c ≤ phi (c ^ 2) := by
  obtain ⟨hp0, hp1⟩ := formationPrior_bounds hc0 hc1
  have hpair := commutingPair_isDensity hp0 hp1
  let e : OrthogonalPairIndex ≃ Fin (Fintype.card OrthogonalPairIndex) :=
    Fintype.equivFin OrthogonalPairIndex
  let A : Density (Fin (Fintype.card OrthogonalPairIndex)) :=
    ⟨matrixReindexHom e (commutingPairZero (formationPrior c)),
      matrixReindexHom_isDensity e hpair.1⟩
  let B : Density (Fin (Fintype.card OrthogonalPairIndex)) :=
    ⟨matrixReindexHom e (commutingPairOne (formationPrior c)),
      matrixReindexHom_isDensity e hpair.2⟩
  have hn : 0 < Fintype.card OrthogonalPairIndex := by norm_num [OrthogonalPairIndex]
  have haff : affinity A.val B.val = c :=
    (affinity_reindex e hpair.1.1 hpair.2.1).trans (formationPair_affinity hc0 hc1)
  have hz := pairCost_mem_extensionCosts hn A B haff
  have hcost : pairCost A.val B.val = phi (c ^ 2) :=
    (pairCost_reindex e hpair.1.1 hpair.2.1).trans (formationPair_cost hc0 hc1)
  exact (csInf_le (extensionCosts_bddBelow c) hz).trans_eq hcost

end QuantumProver.BellDiagonalSquashedEntanglement

namespace QuantumProver.BellDiagonalSquashedEntanglement

theorem binaryEntropy_smallPrior_upper {v p : ℝ} (hv0 : 0 < v) (hv1 : v ≤ 1)
    (hp0 : 0 ≤ p) (hpupper : p ≤ v / 2) (hproduct : p * (1 - p) = v / 4) :
    binaryEntropy p ≤ -(v * Real.log v) / (4 * Real.log 2) +
      (3 / Real.log 2) * v := by
  have hpidentity : p = v / 4 + p ^ 2 := by nlinarith [hproduct]
  have hplower : v / 4 ≤ p := by nlinarith [sq_nonneg p]
  have hppos : 0 < p := lt_of_lt_of_le (by positivity : 0 < v / 4) hplower
  have hpHalf : p ≤ 1 / 2 := by linarith
  have hqpos : 0 < 1 - p := by linarith
  let L : ℝ := Real.log 4 - Real.log v
  have hL_eq : Real.log (4 / v) = L := by
    rw [Real.log_div (by norm_num) hv0.ne']
  have hLnonneg : 0 ≤ L := by
    have hlogv : Real.log v ≤ 0 := Real.log_nonpos hv0.le hv1
    have hlog4 : 0 ≤ Real.log (4 : ℝ) := Real.log_nonneg (by norm_num)
    dsimp [L]
    linarith
  have hLupper : L ≤ 4 / v - 1 := by
    have h := Real.log_le_sub_one_of_pos (show 0 < 4 / v by positivity)
    rwa [hL_eq] at h
  have hfirst : -(p * Real.log p) ≤ p * L := by
    have hlog := Real.log_le_log (show 0 < v / 4 by positivity) hplower
    calc
      -(p * Real.log p) ≤ -(p * Real.log (v / 4)) :=
        neg_le_neg (mul_le_mul_of_nonneg_left hlog hp0)
      _ = p * L := by
        rw [Real.log_div hv0.ne' (by norm_num)]
        dsimp [L]
        ring
  have hsecond : -((1 - p) * Real.log (1 - p)) ≤ p := by
    have hlog := Real.log_le_sub_one_of_pos (inv_pos.mpr hqpos)
    rw [Real.log_inv] at hlog
    calc
      -((1 - p) * Real.log (1 - p)) = (1 - p) * (-Real.log (1 - p)) := by ring
      _ ≤ (1 - p) * ((1 - p)⁻¹ - 1) :=
        mul_le_mul_of_nonneg_left hlog hqpos.le
      _ = p := by field_simp [hqpos.ne'] <;> ring
  have hpsq : p ^ 2 ≤ v ^ 2 / 4 := by
    have h := mul_nonneg (sub_nonneg.mpr hpupper)
      (add_nonneg (by positivity : 0 ≤ v / 2) hp0)
    nlinarith
  have hquadratic : p ^ 2 * L ≤ v := by
    calc
      p ^ 2 * L ≤ (v ^ 2 / 4) * L := mul_le_mul_of_nonneg_right hpsq hLnonneg
      _ ≤ (v ^ 2 / 4) * (4 / v - 1) :=
        mul_le_mul_of_nonneg_left hLupper (by positivity)
      _ = v - v ^ 2 / 4 := by field_simp [hv0.ne'] <;> ring
      _ ≤ v := by nlinarith [sq_nonneg v]
  have hlog4upper : (v / 4) * Real.log 4 ≤ (3 / 4) * v := by
    have hlog := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 by norm_num)
    have h := mul_le_mul_of_nonneg_left hlog (show 0 ≤ v / 4 by positivity)
    nlinarith
  have hnumerator : -(p * Real.log p + (1 - p) * Real.log (1 - p)) ≤
      -(v / 4) * Real.log v + 3 * v := by
    calc
      -(p * Real.log p + (1 - p) * Real.log (1 - p)) ≤ p * L + p := by
        linarith [hfirst, hsecond]
      _ = -(v / 4) * Real.log v + (v / 4) * Real.log 4 + p ^ 2 * L + p := by
        have hm := congrArg (fun x : ℝ => x * L) hpidentity
        dsimp [L]
        dsimp [L] at hm
        nlinarith [hm]
      _ ≤ -(v / 4) * Real.log v + 3 * v := by
        nlinarith [hquadratic, hlog4upper, hpupper]
  calc
    binaryEntropy p ≤ (-(v / 4) * Real.log v + 3 * v) / Real.log 2 :=
      div_le_div_of_nonneg_right hnumerator log_two_pos.le
    _ = -(v * Real.log v) / (4 * Real.log 2) + (3 / Real.log 2) * v := by ring

def formationSmallPrior (c : ℝ) : ℝ := 1 - formationPrior c

theorem formationSmallPrior_bounds {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    0 ≤ formationSmallPrior c ∧ formationSmallPrior c ≤ c ^ 2 / 2 ∧
      formationSmallPrior c * (1 - formationSmallPrior c) = c ^ 2 / 4 := by
  obtain ⟨hq0, hq1⟩ := formationPrior_bounds hc0 hc1
  have hprod := formationPrior_product hc0 hc1
  have hqHalf : (1 / 2 : ℝ) ≤ formationPrior c := by
    unfold formationPrior
    nlinarith [Real.sqrt_nonneg (1 - c ^ 2)]
  have hp0 : 0 ≤ formationSmallPrior c := by dsimp [formationSmallPrior]; linarith
  have hpq : formationSmallPrior c * (1 - formationSmallPrior c) = c ^ 2 / 4 := by
    dsimp [formationSmallPrior]
    nlinarith
  have hpHalf : (1 / 2 : ℝ) ≤ 1 - formationSmallPrior c := by
    dsimp [formationSmallPrior]
    linarith
  have h := mul_le_mul_of_nonneg_left hpHalf hp0
  exact ⟨hp0, by nlinarith [hpq], hpq⟩

theorem formationPhi_le_leadingEdgeTerm {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1) :
    phi (c ^ 2) ≤ leadingEdgeTerm c + (3 / Real.log 2) * c ^ 2 := by
  obtain ⟨hp0, hpupper, hpq⟩ := formationSmallPrior_bounds hc0.le hc1
  have hv0 : 0 < c ^ 2 := sq_pos_of_pos hc0
  have hv1 : c ^ 2 ≤ 1 := by nlinarith
  have h := binaryEntropy_smallPrior_upper hv0 hv1 hp0 hpupper hpq
  have hphi : phi (c ^ 2) = binaryEntropy (formationSmallPrior c) := by
    exact (binaryEntropy_symm_matrix (formationPrior c)).symm
  have hleading : -(c ^ 2 * Real.log (c ^ 2)) / (4 * Real.log 2) = leadingEdgeTerm c := by
    rw [leadingEdgeTerm, one_div, Real.log_inv, Real.log_pow]
    ring
  rwa [← hphi, hleading] at h

theorem squashedEntanglement_sub_leading_le {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1) :
    squashedEntanglement c - leadingEdgeTerm c ≤ (3 / Real.log 2) * c ^ 2 := by
  have h := (physical_formation_upper hc0.le hc1).trans
    (formationPhi_le_leadingEdgeTerm hc0 hc1)
  linarith

end QuantumProver.BellDiagonalSquashedEntanglement

namespace QuantumProver.BellDiagonalSquashedEntanglement

theorem binaryEntropy_smallPrior_lower {v p : ℝ} (hv0 : 0 < v) (hv1 : v ≤ 1 / 16)
    (hp0 : 0 ≤ p) (hpupper : p ≤ v / 2) (hproduct : p * (1 - p) = v / 4) :
    -(v * Real.log v) / (4 * Real.log 2) ≤ binaryEntropy p := by
  have hpidentity : p = v / 4 + p ^ 2 := by nlinarith [hproduct]
  have hplower : v / 4 ≤ p := by nlinarith [sq_nonneg p]
  have htpos : 0 < v / 4 := by positivity
  have hppos : 0 < p := htpos.trans_le hplower
  have hpQuarter : p ≤ 1 / 4 := by linarith
  have hqpos : 0 < 1 - p := by linarith
  have hlog2lower : 1 / 2 ≤ Real.log (2 : ℝ) := by
    have h := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 2 by norm_num)
    norm_num at h ⊢
    exact h
  have hlog4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    have h := Real.log_mul (show (2 : ℝ) ≠ 0 by norm_num)
      (show (2 : ℝ) ≠ 0 by norm_num)
    norm_num at h
    linarith
  have hlogp : Real.log p ≤ -1 := by
    calc
      Real.log p ≤ Real.log (1 / 4 : ℝ) := Real.log_le_log hppos hpQuarter
      _ = -Real.log 4 := by rw [one_div, Real.log_inv]
      _ ≤ -1 := by linarith
  have hratio := Real.log_le_sub_one_of_pos (div_pos hppos htpos)
  have hscaled := mul_le_mul_of_nonneg_left hratio htpos.le
  rw [Real.log_div hppos.ne' htpos.ne'] at hscaled
  have hcancel : (v / 4) * (p / (v / 4) - 1) = p - v / 4 := by
    field_simp [hv0.ne'] <;> ring
  rw [hcancel] at hscaled
  have hnonnegative := mul_nonneg (sub_nonneg.mpr hplower)
    (show 0 ≤ -Real.log p - 1 by linarith)
  have hfirst : -((v / 4) * Real.log (v / 4)) ≤ -(p * Real.log p) := by
    nlinarith [hscaled, hnonnegative]
  have hsecond : 0 ≤ -((1 - p) * Real.log (1 - p)) := by
    exact neg_nonneg.mpr (mul_nonpos_of_nonneg_of_nonpos hqpos.le
      (Real.log_nonpos hqpos.le (by linarith)))
  rw [Real.log_div hv0.ne' (by norm_num)] at hfirst
  have hlog4nonneg : 0 ≤ (v / 4) * Real.log 4 := by
    exact mul_nonneg htpos.le (Real.log_nonneg (by norm_num))
  have hnumerator : -(v / 4) * Real.log v ≤
      -(p * Real.log p + (1 - p) * Real.log (1 - p)) := by
    nlinarith [hfirst, hsecond, hlog4nonneg]
  calc
    -(v * Real.log v) / (4 * Real.log 2) = (-(v / 4) * Real.log v) / Real.log 2 := by ring
    _ ≤ binaryEntropy p := div_le_div_of_nonneg_right hnumerator log_two_pos.le

theorem leadingEdgeTerm_le_formationPhi {c : ℝ} (hc0 : 0 < c) (hc4 : c ≤ 1 / 4) :
    leadingEdgeTerm c ≤ phi (c ^ 2) := by
  have hc1 : c ≤ 1 := by linarith
  obtain ⟨hp0, hpupper, hpq⟩ := formationSmallPrior_bounds hc0.le hc1
  have hv0 : 0 < c ^ 2 := sq_pos_of_pos hc0
  have hv1 : c ^ 2 ≤ 1 / 16 := by nlinarith
  have h := binaryEntropy_smallPrior_lower hv0 hv1 hp0 hpupper hpq
  have hphi : phi (c ^ 2) = binaryEntropy (formationSmallPrior c) :=
    (binaryEntropy_symm_matrix (formationPrior c)).symm
  have hleading : -(c ^ 2 * Real.log (c ^ 2)) / (4 * Real.log 2) = leadingEdgeTerm c := by
    rw [leadingEdgeTerm, one_div, Real.log_inv, Real.log_pow]
    ring
  rwa [← hphi, hleading] at h

theorem formationPhi_sub_leading_bigO :
    Asymptotics.IsBigO (nhdsWithin 0 (Ioi 0))
      (fun c : ℝ => phi (c ^ 2) - leadingEdgeTerm c) (fun c : ℝ => c ^ 2) := by
  apply Asymptotics.IsBigO.of_bound (3 / Real.log 2)
  have hsmall : ∀ᶠ c : ℝ in nhdsWithin 0 (Ioi 0), c < 1 / 4 :=
    (eventually_lt_nhds (show (0 : ℝ) < 1 / 4 by norm_num)).filter_mono nhdsWithin_le_nhds
  filter_upwards [eventually_mem_nhdsWithin, hsmall] with c hc0 hc4
  have hlo := leadingEdgeTerm_le_formationPhi hc0 hc4.le
  have hhi := formationPhi_le_leadingEdgeTerm hc0 (show c ≤ 1 by linarith)
  have hbound : phi (c ^ 2) - leadingEdgeTerm c ≤ (3 / Real.log 2) * c ^ 2 := by
    linarith
  simpa only [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hlo),
    abs_of_nonneg (sq_nonneg c)] using hbound

end QuantumProver.BellDiagonalSquashedEntanglement

namespace QuantumProver.BellDiagonalSquashedEntanglement.E9Limit

open scoped Topology

variable {I : Type*} [Fintype I] [DecidableEq I]

def pairRegion : Set (Mat I × Mat I) :=
  {p | p.1.PosSemidef ∧ p.2.PosSemidef ∧
    SingularLimit.edgeLowerExpression p.1 p.2 ≤ pairCost p.1 p.2}

theorem pairRegion_mem_of_tendsto {α : Type*} {l : Filter α} [NeBot l]
    {X : α → Mat I × Mat I} {p : Mat I × Mat I}
    (hX : Tendsto X l (𝓝 p)) (hRegion : ∀ᶠ x in l, X x ∈ pairRegion) :
    p ∈ pairRegion := by
  have hFirst : Tendsto (fun x => (X x).1) l (𝓝 p.1) :=
    (continuous_fst.tendsto p).comp hX
  have hSecond : Tendsto (fun x => (X x).2) l (𝓝 p.2) :=
    (continuous_snd.tendsto p).comp hX
  have hPSDfirst : ∀ᶠ x in l, (X x).1.PosSemidef := hRegion.mono fun _ h => h.1
  have hPSDsecond : ∀ᶠ x in l, (X x).2.PosSemidef := hRegion.mono fun _ h => h.2.1
  have hPfirst : p.1.PosSemidef := Matrix.posSemidef_is_closed.mem_of_tendsto hFirst hPSDfirst
  have hPsecond : p.2.PosSemidef := Matrix.posSemidef_is_closed.mem_of_tendsto hSecond hPSDsecond
  have hLower := SingularLimit.tendsto_edgeLowerExpression hFirst hSecond
    hPSDfirst hPSDsecond hPfirst hPsecond
  have hCost := SingularLimit.tendsto_pairCost hFirst hSecond
    hPSDfirst hPSDsecond hPfirst hPsecond
  exact ⟨hPfirst, hPsecond,
    le_of_tendsto_of_tendsto hLower hCost (hRegion.mono fun _ h => h.2.2)⟩

theorem pairRegion_isClosed : IsClosed (pairRegion (I := I)) := by
  apply IsSeqClosed.isClosed
  intro X p hRegion hX
  exact pairRegion_mem_of_tendsto hX (Eventually.of_forall hRegion)

def regularizedPair (A B : Mat I) (e : ℝ) : Mat I × Mat I :=
  (SingularLimit.regularizedStateMatrix A e, SingularLimit.regularizedStateMatrix B e)

theorem regularizedPair_tendsto (A B : Mat I) :
    Tendsto (regularizedPair A B) (nhdsWithin 0 (Ioi 0)) (𝓝 (A, B)) :=
  (SingularLimit.regularizedStateMatrix_tendsto A).prodMk_nhds
    (SingularLimit.regularizedStateMatrix_tendsto B)

theorem pair_mem_of_regularized_mem {A B : Mat I}
    (hRegion : ∀ᶠ e : ℝ in nhdsWithin 0 (Ioi 0), regularizedPair A B e ∈ pairRegion) :
    (A, B) ∈ pairRegion :=
  pairRegion_mem_of_tendsto (regularizedPair_tendsto A B) hRegion

theorem regularizedPair_eventually_posDef [Nonempty I] {A B : Mat I}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    ∀ᶠ e : ℝ in nhdsWithin 0 (Ioi 0),
      (regularizedPair A B e).1.PosDef ∧ (regularizedPair A B e).2.PosDef :=
  (SingularLimit.eventually_regularizedStateMatrix_posDef hA).and
    (SingularLimit.eventually_regularizedStateMatrix_posDef hB)

end QuantumProver.BellDiagonalSquashedEntanglement.E9Limit

namespace QuantumProver.BellDiagonalSquashedEntanglement

open scoped Topology

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem density_index_nonempty_matrix (A : Density I) : Nonempty I := by
  by_contra h
  haveI : IsEmpty I := not_nonempty_iff.mp h
  have hz : A.val.trace = 0 := by simp [Matrix.trace]
  exact one_ne_zero (A.property.2.symm.trans hz)

theorem rootFidelity_le_one_of_posDef (A B : Density I) (hA : A.val.PosDef) :
    rootFidelity A.val B.val ≤ 1 := by
  let U : Mat I := FCColumns.fcBasis A B
  rw [← FCColumns.fc_mass_beta_moment A B hA]
  calc
    _ ≤ ∑ j : I, FCColumns.columnMass (sqrtPSD A.val * U) (sqrtPSD B.val * U) j := by
      apply Finset.sum_le_sum
      intro j hj
      exact (mul_le_mul_of_nonneg_left
        (FCColumns.columnBeta_le_one (sqrtPSD A.val * U) (sqrtPSD B.val * U) j)
        (FCColumns.columnMass_nonneg (sqrtPSD A.val * U) (sqrtPSD B.val * U) j)).trans_eq
          (mul_one _)
    _ = 1 := FCColumns.basis_columnMass_sum A B U (FCColumns.fcBasis_unitary A B)

theorem rootFidelity_le_one_matrix (A B : Density I) : rootFidelity A.val B.val ≤ 1 := by
  haveI : Nonempty I := density_index_nonempty_matrix A
  have hlim := SingularLimit.tendsto_rootFidelity
    (SingularLimit.regularizedStateMatrix_tendsto A.val)
    (SingularLimit.regularizedStateMatrix_tendsto B.val)
    (SingularLimit.eventually_regularizedStateMatrix_posSemidef A.property.1)
    (SingularLimit.eventually_regularizedStateMatrix_posSemidef B.property.1)
    A.property.1 B.property.1
  apply le_of_tendsto hlim
  filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with e he
  exact rootFidelity_le_one_of_posDef
    (SingularLimit.faithfulRegularizedDensity A e he.1.le he.2.le)
    (SingularLimit.faithfulRegularizedDensity B e he.1.le he.2.le)
    (SingularLimit.regularizedStateMatrix_posDef A.property.1 e he.1 he.2.le)

theorem matrix_pair_scalar_domain (A B : Density I) :
    0 ≤ affinity A.val B.val ∧ affinity A.val B.val ≤ rootFidelity A.val B.val ∧
      rootFidelity A.val B.val ≤ 1 :=
  ⟨SingularLimit.affinity_nonnegative A.val B.val,
    SingularLimit.affinity_le_rootFidelity A.val B.val, rootFidelity_le_one_matrix A B⟩

def lowerEdgeTerm (c : ℝ) : ℝ :=
  c ^ 2 * Real.log (1 / (4 * c)) / (2 * Real.log 2)

theorem lowerEdgeTerm_le_edgeLowerExpression (A B : Density I)
    (hc : 0 < affinity A.val B.val) :
    lowerEdgeTerm (affinity A.val B.val) ≤ SingularLimit.edgeLowerExpression A.val B.val := by
  let c := affinity A.val B.val
  let F := rootFidelity A.val B.val
  let loss := (F - Real.sqrt (F * c)) ^ 2 / (4 * Real.log 2)
  have hden : 4 * Real.log (2 : ℝ) ≠ 0 := mul_ne_zero (by norm_num) log_two_pos.ne'
  have hloss : (F - Real.sqrt (F * c)) ^ 2 ≤ 4 * Real.log 2 * loss := by
    apply le_of_eq
    dsimp only [loss]
    field_simp [hden]
  have h := Scalar.small_coherence_scalar_reduction c F
    (Scalar.jointDeficit F c + loss) loss hc
    (SingularLimit.affinity_le_rootFidelity A.val B.val) (rootFidelity_le_one_matrix A B)
    le_rfl hloss
  exact h

theorem lowerEdgeTerm_eq_leading_sub_sq {c : ℝ} (hc : 0 < c) :
    lowerEdgeTerm c = leadingEdgeTerm c - c ^ 2 := by
  have hlog4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    calc
      Real.log (4 : ℝ) = Real.log ((2 : ℝ) ^ 2) := by norm_num
      _ = 2 * Real.log 2 := Real.log_pow (2 : ℝ) 2
  simp only [lowerEdgeTerm, leadingEdgeTerm, one_div, Real.log_inv]
  rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) hc.ne', hlog4]
  field_simp [log_two_pos.ne']
  ring

theorem lowerEdgeTerm_sub_leading_bigO :
    Asymptotics.IsBigO (nhdsWithin 0 (Ioi 0))
      (fun c : ℝ => lowerEdgeTerm c - leadingEdgeTerm c) (fun c : ℝ => c ^ 2) := by
  apply Asymptotics.IsBigO.of_bound 1
  filter_upwards [eventually_mem_nhdsWithin] with c hc
  rw [lowerEdgeTerm_eq_leading_sub_sq hc]
  simp [Real.norm_eq_abs, sq_nonneg c]

theorem formationPhi_sub_lowerEdge_bigO :
    Asymptotics.IsBigO (nhdsWithin 0 (Ioi 0))
      (fun c : ℝ => phi (c ^ 2) - lowerEdgeTerm c) (fun c : ℝ => c ^ 2) := by
  apply Asymptotics.IsBigO.of_bound (1 + 3 / Real.log 2)
  have hsmall : ∀ᶠ c : ℝ in nhdsWithin 0 (Ioi 0), c < 1 / 4 :=
    (eventually_lt_nhds (show (0 : ℝ) < 1 / 4 by norm_num)).filter_mono nhdsWithin_le_nhds
  filter_upwards [eventually_mem_nhdsWithin, hsmall] with c hc0 hc4
  have hlo := leadingEdgeTerm_le_formationPhi hc0 hc4.le
  have hhi := formationPhi_le_leadingEdgeTerm hc0 (show c ≤ 1 by linarith)
  have hlow := lowerEdgeTerm_eq_leading_sub_sq hc0
  have hgap : 0 ≤ phi (c ^ 2) - lowerEdgeTerm c := by nlinarith [sq_nonneg c]
  have hbound : phi (c ^ 2) - lowerEdgeTerm c ≤ (1 + 3 / Real.log 2) * c ^ 2 := by
    nlinarith
  simpa only [Real.norm_eq_abs, abs_of_nonneg hgap, abs_of_nonneg (sq_nonneg c)] using hbound

end QuantumProver.BellDiagonalSquashedEntanglement

namespace QuantumProver.BellDiagonalSquashedEntanglement

open Filter Set
open scoped Topology

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem matrix_E9_of_posDef (A B : Density I) (hA : A.val.PosDef)
    (hc : 0 < affinity A.val B.val) :
    SingularLimit.edgeLowerExpression A.val B.val ≤ pairCost A.val B.val := by
  let U : Mat I := FCColumns.fcBasis A B
  let hU : U * Uᴴ = 1 := FCColumns.fcBasis_unitary A B
  let G₀ : Density (I × I) := FCColumns.flagStateInBasis A U hU
  let G₁ : Density (I × I) := FCColumns.flagStateInBasis B U hU
  let loss : ℝ := binaryHolevo G₀.val G₁.val - binaryHolevo A.val B.val
  have hGain : (rootFidelity A.val B.val - rootFidelity G₀.val G₁.val) ^ 2 ≤
      4 * Real.log 2 * loss := by
    simpa only [G₀, G₁, FCColumns.flagStateInBasis_channel, loss] using
      RecoveryGeometry.FidelityLoss.rootFidelity_increase_sq_le_holevoLoss
        G₀ G₁ (partialTraceRightChannel (I := I) (E := I))
  have hMoment : (rootFidelity G₀.val G₁.val) ^ 2 ≤
      rootFidelity A.val B.val * affinity A.val B.val :=
    FCColumns.fc_flag_rootFidelity_sq_le A B hA
  have hDomain := matrix_pair_scalar_domain A B
  have hFlagDomain := matrix_pair_scalar_domain G₀ G₁
  have hFhat : 0 ≤ rootFidelity G₀.val G₁.val := hFlagDomain.1.trans hFlagDomain.2.1
  have hReplace := Scalar.flag_gain_replacement
    (affinity A.val B.val) (rootFidelity A.val B.val) (rootFidelity G₀.val G₁.val) loss
    hc.le hDomain.2.1 hFhat hMoment hGain
  have hDen : 0 < 4 * Real.log 2 := mul_pos (by norm_num) log_two_pos
  have hRatio : (rootFidelity A.val B.val -
      Real.sqrt (rootFidelity A.val B.val * affinity A.val B.val)) ^ 2 /
      (4 * Real.log 2) ≤ loss := by
    apply (div_le_iff₀ hDen).mpr
    simpa only [mul_comm] using hReplace
  have hFlag : Scalar.jointDeficit (rootFidelity A.val B.val) (affinity A.val B.val) ≤
      pairCost G₀.val G₁.val := FCColumns.fc_flag_jointDeficit_lower A B hA
  have hAdd : pairCost A.val B.val = pairCost G₀.val G₁.val + loss :=
    FCColumns.actual_flag_additive_cost A B U hU
  unfold SingularLimit.edgeLowerExpression
  linarith

theorem matrix_E9 (A B : Density I) (hc : 0 < affinity A.val B.val) :
    SingularLimit.edgeLowerExpression A.val B.val ≤ pairCost A.val B.val := by
  haveI : Nonempty I := density_index_nonempty_matrix A
  have hSmall : ∀ᶠ e : ℝ in nhdsWithin 0 (Ioi 0), e < 1 :=
    (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds
  have hAff := SingularLimit.eventually_regularizedStateMatrix_affinity_positive
    A.property.1 B.property.1 hc
  have hRegion : ∀ᶠ e : ℝ in nhdsWithin 0 (Ioi 0),
      E9Limit.regularizedPair A.val B.val e ∈ E9Limit.pairRegion := by
    filter_upwards [eventually_mem_nhdsWithin, hSmall, hAff] with e he0 he1 heAff
    let Ae := SingularLimit.faithfulRegularizedDensity A e he0.le he1.le
    let Be := SingularLimit.faithfulRegularizedDensity B e he0.le he1.le
    have hAePD : Ae.val.PosDef :=
      SingularLimit.regularizedStateMatrix_posDef A.property.1 e he0 he1.le
    exact ⟨Ae.property.1, Be.property.1, matrix_E9_of_posDef Ae Be hAePD heAff⟩
  exact (E9Limit.pair_mem_of_regularized_mem hRegion).2.2

theorem physicalAdditiveFlagCostStatement_proved : PhysicalAdditiveFlagCostStatement := by
  intro n hn A B hc
  simpa only [SingularLimit.edgeLowerExpression, Scalar.jointDeficit_matrix_bridge] using
    matrix_E9 A B hc

theorem matrix_pair_lower_edge (A B : Density I) (hc : 0 < affinity A.val B.val) :
    lowerEdgeTerm (affinity A.val B.val) ≤ pairCost A.val B.val :=
  (lowerEdgeTerm_le_edgeLowerExpression A B hc).trans (matrix_E9 A B hc)

theorem physical_lower_edge_bound {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) :
    lowerEdgeTerm c ≤ squashedEntanglement c := by
  rw [physicalPairInfimum_eq hc hc1]
  apply le_csInf (finitePairCosts_nonempty hc hc1)
  rintro z ⟨n, hn, A, B, hAff, rfl⟩
  have h := matrix_pair_lower_edge A B (by simpa only [hAff] using hc)
  simpa only [hAff] using h

theorem physicalSmallCoherenceBound_proved : PhysicalSmallCoherenceBound := by
  intro c hc hc4
  have hc1 : c ≤ 1 := by linarith
  exact ⟨physical_lower_edge_bound hc hc1, physical_formation_upper hc.le hc1⟩

theorem physical_formation_deficit_nonneg {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    0 ≤ phi (c ^ 2) - squashedEntanglement c :=
  sub_nonneg.mpr (physical_formation_upper hc0 hc1)

theorem physical_sub_leading_bigO :
    Asymptotics.IsBigO (nhdsWithin 0 (Ioi 0))
      (fun c : ℝ => squashedEntanglement c - leadingEdgeTerm c) (fun c : ℝ => c ^ 2) := by
  apply Asymptotics.IsBigO.of_bound (1 + 3 / Real.log 2)
  have hSmall : ∀ᶠ c : ℝ in nhdsWithin 0 (Ioi 0), c < 1 / 4 :=
    (eventually_lt_nhds (show (0 : ℝ) < 1 / 4 by norm_num)).filter_mono nhdsWithin_le_nhds
  filter_upwards [eventually_mem_nhdsWithin, hSmall] with c hc hc4
  have hc1 : c ≤ 1 := by linarith
  have hLower := physical_lower_edge_bound hc hc1
  have hUpper := (physical_formation_upper hc.le hc1).trans
    (formationPhi_le_leadingEdgeTerm hc hc1)
  rw [lowerEdgeTerm_eq_leading_sub_sq hc] at hLower
  have hC : 0 ≤ (3 / Real.log 2) * c ^ 2 :=
    mul_nonneg (div_nonneg (by norm_num) log_two_pos.le) (sq_nonneg c)
  have hNorm : |squashedEntanglement c - leadingEdgeTerm c| ≤
      (1 + 3 / Real.log 2) * c ^ 2 := by
    apply abs_le.mpr
    constructor <;> nlinarith [sq_nonneg c]
  simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg c)] using hNorm

theorem physical_formation_deficit_bigO :
    Asymptotics.IsBigO (nhdsWithin 0 (Ioi 0))
      (fun c : ℝ => phi (c ^ 2) - squashedEntanglement c) (fun c : ℝ => c ^ 2) := by
  apply Asymptotics.IsBigO.of_bound (1 + 3 / Real.log 2)
  have hSmall : ∀ᶠ c : ℝ in nhdsWithin 0 (Ioi 0), c < 1 / 4 :=
    (eventually_lt_nhds (show (0 : ℝ) < 1 / 4 by norm_num)).filter_mono nhdsWithin_le_nhds
  filter_upwards [eventually_mem_nhdsWithin, hSmall] with c hc hc4
  have hc1 : c ≤ 1 := by linarith
  have hLower := physical_lower_edge_bound hc hc1
  have hUpper := formationPhi_le_leadingEdgeTerm hc hc1
  rw [lowerEdgeTerm_eq_leading_sub_sq hc] at hLower
  have hGap := physical_formation_deficit_nonneg hc.le hc1
  have hBound : phi (c ^ 2) - squashedEntanglement c ≤
      (1 + 3 / Real.log 2) * c ^ 2 := by nlinarith
  simpa only [Real.norm_eq_abs, abs_of_nonneg hGap,
    abs_of_nonneg (sq_nonneg c)] using hBound

theorem physicalAsymptoticStatement_proved : PhysicalAsymptoticStatement :=
  ⟨physical_sub_leading_bigO, physical_formation_deficit_bigO⟩

theorem universalHolevoFidelityLoss_proved : UniversalHolevoFidelityLoss := by
  intro n m hn hm A B N
  exact RecoveryGeometry.FidelityLoss.rootFidelity_increase_sq_le_holevoLoss A B N

theorem bellEdgeTheorem : BellEdgeTheorem :=
  ⟨physicalPairInfimumStatement_proved, universalHolevoFidelityLoss_proved,
    physicalAdditiveFlagCostStatement_proved, physicalSmallCoherenceBound_proved,
    physicalAsymptoticStatement_proved⟩

end QuantumProver.BellDiagonalSquashedEntanglement

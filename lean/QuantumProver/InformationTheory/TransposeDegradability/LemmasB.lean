import QuantumProver.InformationTheory.TransposeDegradability.Definitions
import QuantumProver.InformationTheory.TransposeDegradability.FoundationB
import Mathlib.Analysis.Matrix.Order
import Mathlib.Tactic.FinCases

/-!
The explicit bosonic qubit extension. The tensor indices are literally
`((reference, first qubit), second qubit)`. No environment filter, Gram rank
assumption, or assumed ordinary degrader enters this module.
-/

noncomputable section

open Matrix
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace TransposeDegradability

section QubitFactors

variable {R K : Type} [Fintype K]

/-- The Gram of a factor in the fixed `00,01,10,11` order. -/
abbrev qubitGram (A B G D : Matrix R K ℂ) :
    Matrix ((R × Qubit) × Qubit) ((R × Qubit) × Qubit) ℂ :=
  qubitFactor A B G D * (qubitFactor A B G D)ᴴ

theorem firstMarginal_qubitGram_00 (A B G D : Matrix R K ℂ) (r s : R) :
    firstMarginal (qubitGram A B G D) (r, 0) (s, 0) =
      (A * Aᴴ + B * Bᴴ) r s := by
  simp [firstMarginal, partialTraceRight, qubitGram, Fin.sum_univ_two,
    Matrix.mul_apply, Matrix.conjTranspose_apply]

theorem firstMarginal_qubitGram_01 (A B G D : Matrix R K ℂ) (r s : R) :
    firstMarginal (qubitGram A B G D) (r, 0) (s, 1) =
      (A * Gᴴ + B * Dᴴ) r s := by
  simp [firstMarginal, partialTraceRight, qubitGram, Fin.sum_univ_two,
    Matrix.mul_apply, Matrix.conjTranspose_apply]

theorem firstMarginal_qubitGram_10 (A B G D : Matrix R K ℂ) (r s : R) :
    firstMarginal (qubitGram A B G D) (r, 1) (s, 0) =
      (G * Aᴴ + D * Bᴴ) r s := by
  simp [firstMarginal, partialTraceRight, qubitGram, Fin.sum_univ_two,
    Matrix.mul_apply, Matrix.conjTranspose_apply]

theorem firstMarginal_qubitGram_11 (A B G D : Matrix R K ℂ) (r s : R) :
    firstMarginal (qubitGram A B G D) (r, 1) (s, 1) =
      (G * Gᴴ + D * Dᴴ) r s := by
  simp [firstMarginal, partialTraceRight, qubitGram, Fin.sum_univ_two,
    Matrix.mul_apply, Matrix.conjTranspose_apply]

theorem secondMarginal_qubitGram_00 (A B G D : Matrix R K ℂ) (r s : R) :
    secondMarginal (qubitGram A B G D) (r, 0) (s, 0) =
      (A * Aᴴ + G * Gᴴ) r s := by
  simp [secondMarginal, partialTraceMiddle, qubitGram, Fin.sum_univ_two,
    Matrix.mul_apply, Matrix.conjTranspose_apply]

/-- The physical output transpose preserves the 00 reference block. -/
theorem partialTransposeRight_firstMarginal_qubitGram_00
    (A B G D : Matrix R K ℂ) (r s : R) :
    partialTransposeRight (firstMarginal (qubitGram A B G D)) (r, 0) (s, 0) =
      (A * Aᴴ + B * Bᴴ) r s := by
  exact firstMarginal_qubitGram_00 A B G D r s

/-- The physical output transpose exchanges 01 with 10, leaving r,s fixed. -/
theorem partialTransposeRight_firstMarginal_qubitGram_01
    (A B G D : Matrix R K ℂ) (r s : R) :
    partialTransposeRight (firstMarginal (qubitGram A B G D)) (r, 0) (s, 1) =
      (G * Aᴴ + D * Bᴴ) r s := by
  exact firstMarginal_qubitGram_10 A B G D r s

/-- The physical output transpose exchanges 10 with 01, leaving r,s fixed. -/
theorem partialTransposeRight_firstMarginal_qubitGram_10
    (A B G D : Matrix R K ℂ) (r s : R) :
    partialTransposeRight (firstMarginal (qubitGram A B G D)) (r, 1) (s, 0) =
      (A * Gᴴ + B * Dᴴ) r s := by
  exact firstMarginal_qubitGram_01 A B G D r s

/-- The physical output transpose preserves the 11 reference block. -/
theorem partialTransposeRight_firstMarginal_qubitGram_11
    (A B G D : Matrix R K ℂ) (r s : R) :
    partialTransposeRight (firstMarginal (qubitGram A B G D)) (r, 1) (s, 1) =
      (G * Gᴴ + D * Dᴴ) r s := by
  exact firstMarginal_qubitGram_11 A B G D r s

/-- Equal physical 00 blocks give the rectangular alignment hypothesis. -/
theorem rowGram_eq_of_diagonal_agreement (A B G D : Matrix R K ℂ)
    (hdiag : ∀ r s, firstMarginal (qubitGram A B G D) (r, 0) (s, 0) =
      secondMarginal (qubitGram A B G D) (r, 0) (s, 0)) :
    B * Bᴴ = G * Gᴴ := by
  ext r s
  have h := hdiag r s
  rw [firstMarginal_qubitGram_00, secondMarginal_qubitGram_00] at h
  exact add_left_cancel h

omit [Fintype K] in
theorem symmetric_qubitFactor_rows (A G D : Matrix R K ℂ)
    (p : (R × Qubit) × Qubit) (k : K) :
    qubitFactor A G G D (swapQubitsIndex p) k = qubitFactor A G G D p k := by
  rcases p with ⟨⟨r, e⟩, f⟩
  fin_cases e <;> fin_cases f <;> simp [swapQubitsIndex, qubitFactor]

theorem symmetric_qubitGram_bosonic (A G D : Matrix R K ℂ) :
    Bosonic (qubitGram A G G D) := by
  intro p q
  simp only [qubitGram, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro k _
  rw [symmetric_qubitFactor_rows]

theorem aligned_qubitGram_firstMarginal [DecidableEq K] (A B G D : Matrix R K ℂ)
    (W : Matrix K K ℂ) (hW : W * Wᴴ = 1)
    (hG : G = B * W) (hGram : B * Bᴴ = G * Gᴴ) :
    firstMarginal (qubitGram A G G (D * W)) =
      firstMarginal (qubitGram A B G D) := by
  have hcross := aligned_crossGram B G D W hW hG
  have hcrossAdj : (D * W) * Gᴴ = D * Bᴴ := by
    simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
      using congrArg Matrix.conjTranspose hcross
  have hlast := aligned_lastGram D W hW
  ext ⟨r, e⟩ ⟨s, f⟩
  fin_cases e <;> fin_cases f
  · calc
      _ = (A * Aᴴ + G * Gᴴ) r s := firstMarginal_qubitGram_00 A G G (D * W) r s
      _ = (A * Aᴴ + B * Bᴴ) r s :=
        congrArg (fun M : Matrix R R ℂ => (A * Aᴴ + M) r s) hGram.symm
      _ = _ := (firstMarginal_qubitGram_00 A B G D r s).symm
  · calc
      _ = (A * Gᴴ + G * (D * W)ᴴ) r s := firstMarginal_qubitGram_01 A G G (D * W) r s
      _ = (A * Gᴴ + B * Dᴴ) r s :=
        congrArg (fun M : Matrix R R ℂ => (A * Gᴴ + M) r s) hcross
      _ = _ := (firstMarginal_qubitGram_01 A B G D r s).symm
  · calc
      _ = (G * Aᴴ + (D * W) * Gᴴ) r s := firstMarginal_qubitGram_10 A G G (D * W) r s
      _ = (G * Aᴴ + D * Bᴴ) r s :=
        congrArg (fun M : Matrix R R ℂ => (G * Aᴴ + M) r s) hcrossAdj
      _ = _ := (firstMarginal_qubitGram_10 A B G D r s).symm
  · calc
      _ = (G * Gᴴ + (D * W) * (D * W)ᴴ) r s := firstMarginal_qubitGram_11 A G G (D * W) r s
      _ = (G * Gᴴ + D * Dᴴ) r s :=
        congrArg (fun M : Matrix R R ℂ => (G * Gᴴ + M) r s) hlast
      _ = _ := (firstMarginal_qubitGram_11 A B G D r s).symm

end QubitFactors

section BosonicMarginals

variable {R : Type}

theorem bosonic_columns_of_isHermitian
    (X : Matrix ((R × Qubit) × Qubit) ((R × Qubit) × Qubit) ℂ)
    (hH : X.IsHermitian) (hB : Bosonic X) (p q : (R × Qubit) × Qubit) :
    X p (swapQubitsIndex q) = X p q := by
  calc
    X p (swapQubitsIndex q) = star (X (swapQubitsIndex q) p) :=
      (hH.apply p (swapQubitsIndex q)).symm
    _ = star (X q p) := by rw [hB q p]
    _ = X p q := hH.apply p q

/-- Row-swap support plus Hermiticity identifies the two literal marginals. -/
theorem secondMarginal_eq_firstMarginal_of_bosonic
    (X : Matrix ((R × Qubit) × Qubit) ((R × Qubit) × Qubit) ℂ)
    (hH : X.IsHermitian) (hB : Bosonic X) :
    secondMarginal X = firstMarginal X := by
  ext ⟨r, e⟩ ⟨s, f⟩
  simp only [secondMarginal, partialTraceMiddle, firstMarginal, partialTraceRight]
  apply Finset.sum_congr rfl
  intro d _
  calc
    X ((r, d), e) ((s, d), f) = X ((r, e), d) ((s, d), f) :=
      hB ((r, e), d) ((s, d), f)
    _ = X ((r, e), d) ((s, f), d) :=
      bosonic_columns_of_isHermitian X hH hB ((r, e), d) ((s, f), d)

end BosonicMarginals

section Extension

variable {R : Type} [Fintype R] [DecidableEq R]

/-- Positive matrices admit a literal finite Gram factor, including zero rank. -/
theorem exists_gramFactor_of_posSemidef {N : Type} [Fintype N] [DecidableEq N]
    (X : Matrix N N ℂ) (hX : X.PosSemidef) :
    ∃ L : Matrix N N ℂ, L * Lᴴ = X := by
  let L := CFC.sqrt X
  have hL : Lᴴ = L :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg X)).isHermitian
  refine ⟨L, ?_⟩
  rw [hL]
  simpa only [L, pow_two] using CFC.sq_sqrt X hX.nonneg

theorem hasBosonicSelfExtension_qubitGram_of_rowGram_eq
    {K : Type} [Fintype K] [DecidableEq K] (A B G D : Matrix R K ℂ)
    (hGram : B * Bᴴ = G * Gᴴ) :
    HasBosonicSelfExtension (firstMarginal (qubitGram A B G D)) := by
  obtain ⟨W, hW, _, hG⟩ := exists_unitary_right_of_rowGram_eq B G hGram
  let σ := qubitGram A G G (D * W)
  have hσ : σ.PosSemidef := Matrix.posSemidef_self_mul_conjTranspose _
  have hB : Bosonic σ := symmetric_qubitGram_bosonic A G (D * W)
  have hfirst : firstMarginal σ = firstMarginal (qubitGram A B G D) :=
    aligned_qubitGram_firstMarginal A B G D W hW hG hGram
  refine ⟨σ, hσ, hB, hfirst, ?_⟩
  exact (secondMarginal_eq_firstMarginal_of_bosonic σ hσ.isHermitian hB).trans hfirst

/-- The source qubit extension lemma, quantified over every positive matrix.
Only agreement of the two 00 blocks is used; no partial-transpose positivity
or invertibility assumption is hidden in the statement. -/
theorem hasBosonicSelfExtension_of_diagonal_agreement
    (ω : Matrix ((R × Qubit) × Qubit) ((R × Qubit) × Qubit) ℂ)
    (hω : ω.PosSemidef)
    (hdiag : ∀ r s, firstMarginal ω (r, 0) (s, 0) =
      secondMarginal ω (r, 0) (s, 0)) :
    HasBosonicSelfExtension (firstMarginal ω) := by
  obtain ⟨L, hL⟩ := exists_gramFactor_of_posSemidef ω hω
  let A : Matrix R ((R × Qubit) × Qubit) ℂ := fun r k => L ((r, 0), 0) k
  let B : Matrix R ((R × Qubit) × Qubit) ℂ := fun r k => L ((r, 0), 1) k
  let G : Matrix R ((R × Qubit) × Qubit) ℂ := fun r k => L ((r, 1), 0) k
  let D : Matrix R ((R × Qubit) × Qubit) ℂ := fun r k => L ((r, 1), 1) k
  have hfactor : qubitFactor A B G D = L := by
    ext ⟨⟨r, e⟩, f⟩ k
    fin_cases e <;> fin_cases f <;> simp [qubitFactor, A, B, G, D]
  have hGram : qubitGram A B G D = ω := by
    rw [qubitGram, hfactor, hL]
  have hdiagFactor : ∀ r s,
      firstMarginal (qubitGram A B G D) (r, 0) (s, 0) =
      secondMarginal (qubitGram A B G D) (r, 0) (s, 0) := by
    simpa only [hGram] using hdiag
  have hrow := rowGram_eq_of_diagonal_agreement A B G D hdiagFactor
  simpa only [hGram] using hasBosonicSelfExtension_qubitGram_of_rowGram_eq A B G D hrow

/-- Ordered feasibility for the physical output-qubit transpose yields an
ordinary bosonic self-extension. The reference index is never transposed. -/
theorem hasBosonicSelfExtension_of_ordered_marginals
    (ρ : Matrix (R × Qubit) (R × Qubit) ℂ)
    (ω : Matrix ((R × Qubit) × Qubit) ((R × Qubit) × Qubit) ℂ)
    (hω : ω.PosSemidef) (hfirst : firstMarginal ω = ρ)
    (hsecond : secondMarginal ω = partialTransposeRight ρ) :
    HasBosonicSelfExtension ρ := by
  have hdiag : ∀ r s, firstMarginal ω (r, 0) (s, 0) =
      secondMarginal ω (r, 0) (s, 0) := by
    intro r s
    rw [hfirst, hsecond, partialTransposeRight_diagonal_block]
  simpa only [hfirst] using hasBosonicSelfExtension_of_diagonal_agreement ω hω hdiag

end Extension

end TransposeDegradability

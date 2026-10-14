import QuantumProver.InformationTheory.TransposeDegradability.Definitions
import QuantumProver.InformationTheory.TransposeDegradability.LemmasB
import QuantumProver.InformationTheory.TransposeDegradability.LemmasC

/-!
Conjugate degradability implies ordinary degradability for support-minimal
channels with a qubit environment. Conjugation on Hermitian matrices is expressed
by the complex-linear transpose map. The proof uses a bosonic extension and
whole-output CPTP reconstruction.
-/

noncomputable section

namespace TransposeDegradability

open Matrix
open scoped ComplexOrder

variable {I J E : Type} [Fintype I] [Fintype J] [Fintype E] [DecidableEq I]

theorem sandwich_matrixUnit_apply (V : Matrix J I ℂ) (i i' : I) (j j' : J) :
    (V * Matrix.single i i' (1 : ℂ) * Vᴴ) j j' = V j i * star (V j' i') := by
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.single_apply, ite_and]

theorem stinespringOutput_matrixUnit_apply (V : Matrix (J × E) I ℂ)
    (i i' : I) (b b' : J) :
    stinespringOutput V (Matrix.single i i' (1 : ℂ)) b b' =
      ∑ e, V (b, e) i * star (V (b', e) i') := by
  simp only [stinespringOutput_apply, partialTraceRight, sandwich_matrixUnit_apply]

theorem stinespringComplement_matrixUnit_apply (V : Matrix (J × E) I ℂ)
    (i i' : I) (e e' : E) :
    stinespringComplement V (Matrix.single i i' (1 : ℂ)) e e' =
      ∑ b, V (b, e) i * star (V (b, e') i') := by
  simp only [stinespringComplement_apply, partialTraceLeft, sandwich_matrixUnit_apply]

/-- Raw input Choi orientation; normalization by the input dimension is unnecessary. -/
theorem purificationMatrix_mul_conjTranspose_eq_choi
    (V : Matrix (J × E) I ℂ) :
    purificationMatrix V * (purificationMatrix V)ᴴ = choi (stinespringComplement V) := by
  ext ⟨i, e⟩ ⟨i', e'⟩
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, purificationMatrix,
    choi_apply, stinespringComplement_matrixUnit_apply]

theorem partialTraceMiddle_purificationState_eq_choi
    (V : Matrix (J × E) I ℂ) :
    partialTraceMiddle (purificationState (purificationMatrix V)) =
      choi (stinespringOutput V) := by
  ext ⟨i, b⟩ ⟨i', b'⟩
  simp only [partialTraceMiddle, purificationState_apply, purificationMatrix,
    choi_apply, stinespringOutput_matrixUnit_apply]

/-- Apply the proposed transpose degrader to the whole output of the raw purification. -/
def orderedExtension (V : Matrix (J × Qubit) I ℂ)
    (D : Matrix J J ℂ →ₗ[ℂ] Matrix Qubit Qubit ℂ) :
    Matrix ((I × Qubit) × Qubit) ((I × Qubit) × Qubit) ℂ :=
  amplify D (I × Qubit) (purificationState (purificationMatrix V))

omit [DecidableEq I] in
theorem orderedExtension_posSemidef (V : Matrix (J × Qubit) I ℂ)
    (D : Matrix J J ℂ →ₗ[ℂ] Matrix Qubit Qubit ℂ) (hD : CPTP D) :
    (orderedExtension V D).PosSemidef :=
  hD.1 (I × Qubit) _ (purificationState_posSemidef _)

omit [Fintype I] [DecidableEq I] in
theorem orderedExtension_firstMarginal (V : Matrix (J × Qubit) I ℂ)
    (D : Matrix J J ℂ →ₗ[ℂ] Matrix Qubit Qubit ℂ) (hD : TracePreserving D) :
    firstMarginal (orderedExtension V D) =
      purificationMatrix V * (purificationMatrix V)ᴴ := by
  simpa [firstMarginal, orderedExtension] using
    partialTraceRight_amplify_of_tracePreserving D hD
      (purificationState (purificationMatrix V))

theorem orderedExtension_secondMarginal (V : Matrix (J × Qubit) I ℂ)
    (D : Matrix J J ℂ →ₗ[ℂ] Matrix Qubit Qubit ℂ) :
    secondMarginal (orderedExtension V D) = choi (D.comp (stinespringOutput V)) := by
  change partialTraceMiddle
    (amplify D (I × Qubit) (purificationState (purificationMatrix V))) = _
  rw [partialTraceMiddle_amplify, partialTraceMiddle_purificationState_eq_choi,
    ← choi_comp]

theorem orderedExtension_transposeMarginal (V : Matrix (J × Qubit) I ℂ)
    (D : Matrix J J ℂ →ₗ[ℂ] Matrix Qubit Qubit ℂ)
    (hfac : ∀ X, D (stinespringOutput V X) = (stinespringComplement V X)ᵀ) :
    secondMarginal (orderedExtension V D) =
      partialTransposeRight (purificationMatrix V * (purificationMatrix V)ᴴ) := by
  have hc : D.comp (stinespringOutput V) =
      transposeLinear.comp (stinespringComplement V) := by
    apply LinearMap.ext
    intro X
    exact hfac X
  rw [orderedExtension_secondMarginal, hc, choi_transpose_comp,
    ← purificationMatrix_mul_conjTranspose_eq_choi]

theorem orderedExtension_diagonal_agreement (V : Matrix (J × Qubit) I ℂ)
    (D : Matrix J J ℂ →ₗ[ℂ] Matrix Qubit Qubit ℂ) (hD : TracePreserving D)
    (hfac : ∀ X, D (stinespringOutput V X) = (stinespringComplement V X)ᵀ) :
    ∀ r s, firstMarginal (orderedExtension V D) (r, 0) (s, 0) =
      secondMarginal (orderedExtension V D) (r, 0) (s, 0) := by
  intro r s
  rw [orderedExtension_firstMarginal V D hD, orderedExtension_transposeMarginal V D hfac]
  rfl

/-- Choi injectivity turns the reconstructed marginal identity into equality
on every input operator. The reconstructed map is defined on all of `J`. -/
theorem ordinaryDegradable_of_reconstruction
    (V : Matrix (J × Qubit) I ℂ)
    (D : Matrix J J ℂ →ₗ[ℂ] Matrix Qubit Qubit ℂ) (hD : CPTP D)
    (σ : Matrix ((I × Qubit) × Qubit) ((I × Qubit) × Qubit) ℂ)
    (hreproduce : amplify D (I × Qubit) (purificationState (purificationMatrix V)) = σ)
    (hsecond : secondMarginal σ = purificationMatrix V * (purificationMatrix V)ᴴ) :
    OrdinaryDegradable V := by
  have hc : choi (D.comp (stinespringOutput V)) = choi (stinespringComplement V) := by
    calc
      _ = secondMarginal (orderedExtension V D) :=
        (orderedExtension_secondMarginal V D).symm
      _ = secondMarginal σ := congrArg secondMarginal hreproduce
      _ = purificationMatrix V * (purificationMatrix V)ᴴ := hsecond
      _ = choi (stinespringComplement V) := purificationMatrix_mul_conjTranspose_eq_choi V
  have hmap := choi_injective hc
  refine ⟨D, hD, ?_⟩
  intro X
  exact LinearMap.congr_fun hmap X

/-- The exact universal theorem, with explicit operational semantics. -/
def EnvironmentQubitTDImpliesOrdinary : Prop :=
  ∀ (n m : ℕ), 0 < n → 0 < m →
    ∀ V : Matrix (Fin m × Qubit) (Fin n) ℂ,
      IsStinespringIsometry V → SupportMinimal V →
      TransposeDegradable V → OrdinaryDegradable V

/-- The actual construction needs only full output support, rather than an
extra rank hypothesis. Positivity and trace preservation are stated for the underlying linear maps. -/
theorem ordinaryDegradable_of_transposeDegradable [DecidableEq J]
    (V : Matrix (J × Qubit) I ℂ) (hSupport : SupportMinimal V)
    (hTD : TransposeDegradable V) : OrdinaryDegradable V := by
  obtain ⟨D, hD, hfac⟩ := hTD
  have hExtension := hasBosonicSelfExtension_of_diagonal_agreement
    (orderedExtension V D) (orderedExtension_posSemidef V D hD)
    (orderedExtension_diagonal_agreement V D hD.2 hfac)
  rw [orderedExtension_firstMarginal V D hD.2] at hExtension
  obtain ⟨σ, hσ, _hBosonic, hfirst, hsecond⟩ := hExtension
  have hGram : (purificationGram (purificationMatrix V)).PosDef := by
    simpa only [purificationGram] using purificationMatrix_gram_posDef hSupport
  obtain ⟨Dordinary, hDordinary, hreproduce⟩ := exists_CPTP_from_extension
    (purificationMatrix V) hGram σ hσ hfirst
  exact ordinaryDegradable_of_reconstruction V Dordinary hDordinary σ hreproduce hsecond

/-- Every actual finite environment-qubit TD channel has a whole-output
ordinary CPTP degrader. This is not a complete Pareto-frontier theorem. -/
theorem environmentQubit_td_implies_ordinary : EnvironmentQubitTDImpliesOrdinary := by
  intro n m _hn _hm V _hIsometry hSupport hTD
  exact ordinaryDegradable_of_transposeDegradable V hSupport hTD

theorem no_strictTransposeDegradable_qubit [DecidableEq J]
    (V : Matrix (J × Qubit) I ℂ) (hSupport : SupportMinimal V) :
    ¬ StrictlyTransposeDegradable V := by
  intro h
  exact h.2 (ordinaryDegradable_of_transposeDegradable V hSupport h.1)

theorem not_strictlyTransposeDegradable_of_ordinary
    {I J : Type} [Fintype I] [Fintype J]
    {V : Matrix (J × Qubit) I ℂ} (h : OrdinaryDegradable V) :
    ¬ StrictlyTransposeDegradable V := by
  intro hs
  exact hs.2 h

end TransposeDegradability

import QuantumProver.InformationTheory.WernerEndpoint.DensityEnsembleExistence
import QuantumProver.InformationTheory.WernerEndpoint.OperationalEndpointCost
import QuantumProver.InformationTheory.ConditionalEntropy.MixtureEntropy

noncomputable section

namespace QuantumProver.WernerEndpoint.LocalEntropy

open scoped BigOperators Kronecker ComplexOrder
open QuantumProver.QuantumEntropy

theorem localInstrument_average_retainedEntropy_le {H A B O : Type*}
    [Fintype H] [Fintype A] [Fintype B] [Fintype O]
    [DecidableEq A] [DecidableEq B] [DecidableEq O]
    (K : H → Matrix O A ℂ) (hK : ∑ h, (K h).conjTranspose * K h = 1)
    (ρ : Matrix (A × B) (A × B) ℂ) (hρ : IsDensity ρ) :
    (∑ h, QuantumProver.LocalInstrumentMarginals.branchProbability (K h) ρ *
      entropyBits (QuantumProver.LocalInstrumentMarginals.normalizedUntouchedMarginal K ρ h)) ≤
      entropyBits (QuantumProver.QuantumEntropy.partialTrace_left ρ) := by
  have hj := QuantumProver.ConditionalEntropy.entropyBits_weightedSum_lower
    (fun h => QuantumProver.LocalInstrumentMarginals.branchProbability (K h) ρ)
    (QuantumProver.LocalInstrumentMarginals.normalizedUntouchedMarginal K ρ)
    (fun h => QuantumProver.LocalInstrumentMarginals.branchProbability_nonneg (K h) hρ.1)
    (QuantumProver.LocalInstrumentMarginals.sum_branchProbabilities_eq_one K hK hρ)
    (fun h => QuantumProver.LocalInstrumentMarginals.normalizedUntouchedMarginal_isDensity K hK hρ h)
  rw [QuantumProver.LocalInstrumentMarginals.weighted_normalizedUntouchedMarginals K hK hρ.1] at hj
  exact hj

theorem alice_step_average_bobEntropy_le {a b a' h z : ℕ}
    (K : Fin h → Fin z → Matrix (Fin a') (Fin a) ℂ)
    (hK : ∑ j, ∑ k, (K j k).conjTranspose * K j k = 1)
    (ρ : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) (hρ : IsDensity ρ) :
    (∑ jk : Fin h × Fin z,
      QuantumProver.LocalInstrumentMarginals.branchProbability (K jk.1 jk.2) ρ *
        entropyBits (QuantumProver.LocalInstrumentMarginals.normalizedUntouchedMarginal
          (fun uv : Fin h × Fin z => K uv.1 uv.2) ρ jk)) ≤
      entropyBits (QuantumProver.QuantumEntropy.partialTrace_left ρ) := by
  exact localInstrument_average_retainedEntropy_le
    (fun jk : Fin h × Fin z => K jk.1 jk.2)
    (by simpa only [Fintype.sum_prod_type] using hK) ρ hρ

def normalizedPureVector {I : Type*} [Fintype I] (v fallback : I → ℂ) : I → ℂ :=
  if vectorNormSq v = 0 then fallback else
    (((Real.sqrt (vectorNormSq v))⁻¹ : ℝ) : ℂ) • v

private theorem inverse_norm_factor {I : Type*} [Fintype I] (v : I → ℂ) :
    Complex.normSq (((Real.sqrt (vectorNormSq v))⁻¹ : ℝ) : ℂ) =
      (vectorNormSq v)⁻¹ := by
  simp only [Complex.normSq_ofReal, ← sq, inv_pow]
  rw [Real.sq_sqrt (matrix_vectorNormSq_nonneg v)]

theorem normalizedPureVector_normSq {I : Type*} [Fintype I] (v fallback : I → ℂ)
    (hf : vectorNormSq fallback = 1) : vectorNormSq (normalizedPureVector v fallback) = 1 := by
  by_cases hz : vectorNormSq v = 0
  · simp only [normalizedPureVector, if_pos hz, hf]
  · rw [normalizedPureVector, if_neg hz, matrix_vectorNormSq_scalar,
      inverse_norm_factor, inv_mul_cancel₀ hz]

theorem normalizedPureVector_density_of_nonzero {I : Type*} [Fintype I]
    (v fallback : I → ℂ) (hz : vectorNormSq v ≠ 0) :
    pureDensity (normalizedPureVector v fallback) =
      ((vectorNormSq v)⁻¹ : ℝ) • pureDensity v := by
  rw [normalizedPureVector, if_neg hz, matrix_pureDensity_scalar, inverse_norm_factor]
  ext i j
  simp [Matrix.smul_apply, smul_eq_mul, Complex.real_smul]

theorem branchProbability_pure {A B O : Type*}
    [Fintype A] [Fintype B] [Fintype O] [DecidableEq B]
    (K : Matrix O A ℂ) (ψ : A × B → ℂ) :
    QuantumProver.LocalInstrumentMarginals.branchProbability K (pureDensity ψ) =
      vectorNormSq ((QuantumProver.LocalInstrumentMarginals.localLift K).mulVec ψ) := by
  unfold QuantumProver.LocalInstrumentMarginals.branchProbability QuantumProver.LocalInstrumentMarginals.branch
  rw [show pureDensity ψ = crossDensity ψ ψ from rfl, sandwich_crossDensity]
  simpa only [pureDensity, Complex.ofReal_re] using
    congrArg Complex.re (pureDensity_trace
      ((QuantumProver.LocalInstrumentMarginals.localLift K).mulVec ψ))

theorem normalizedBranch_pure_of_probability_ne_zero {H A B O : Type*}
    [Fintype H] [Fintype A] [Fintype B] [Fintype O]
    [DecidableEq A] [DecidableEq B] [DecidableEq O]
    (K : H → Matrix O A ℂ) (ψ : A × B → ℂ) (fallback : O × B → ℂ) (h : H)
    (hp : QuantumProver.LocalInstrumentMarginals.branchProbability (K h) (pureDensity ψ) ≠ 0) :
    QuantumProver.LocalInstrumentMarginals.normalizedBranch K (pureDensity ψ) h =
      pureDensity (normalizedPureVector
        ((QuantumProver.LocalInstrumentMarginals.localLift (K h)).mulVec ψ) fallback) := by
  have hv : vectorNormSq ((QuantumProver.LocalInstrumentMarginals.localLift (K h)).mulVec ψ) ≠ 0 := by
    rw [← branchProbability_pure]
    exact hp
  rw [QuantumProver.LocalInstrumentMarginals.normalizedBranch, if_neg hp,
    normalizedPureVector_density_of_nonzero _ _ hv, ← branchProbability_pure]
  congr 1
  exact sandwich_crossDensity (QuantumProver.LocalInstrumentMarginals.localLift (K h)) ψ ψ

theorem localMeasurement_average_pureAliceEntropy_le {H A B O : Type*}
    [Fintype H] [Fintype A] [Fintype B] [Fintype O]
    [DecidableEq A] [DecidableEq B] [DecidableEq O]
    (K : H → Matrix O A ℂ) (hK : ∑ h, (K h).conjTranspose * K h = 1)
    (ψ : A × B → ℂ) (hψ : vectorNormSq ψ = 1) (fallback : O × B → ℂ) :
    (∑ h, QuantumProver.LocalInstrumentMarginals.branchProbability (K h) (pureDensity ψ) *
      AntisymmetricEnsembleCost.aliceEntropy (normalizedPureVector
        ((QuantumProver.LocalInstrumentMarginals.localLift (K h)).mulVec ψ) fallback)) ≤
      AntisymmetricEnsembleCost.aliceEntropy ψ := by
  have hρ : IsDensity (pureDensity ψ) := ⟨pureDensity_posSemidef ψ, by
    rw [pureDensity_trace, hψ]
    rfl⟩
  have hj := localInstrument_average_retainedEntropy_le K hK (pureDensity ψ) hρ
  have he (h : H) :
      QuantumProver.LocalInstrumentMarginals.branchProbability (K h) (pureDensity ψ) *
        AntisymmetricEnsembleCost.aliceEntropy (normalizedPureVector
          ((QuantumProver.LocalInstrumentMarginals.localLift (K h)).mulVec ψ) fallback) =
      QuantumProver.LocalInstrumentMarginals.branchProbability (K h) (pureDensity ψ) *
        entropyBits (QuantumProver.LocalInstrumentMarginals.normalizedUntouchedMarginal K (pureDensity ψ) h) := by
    by_cases hp : QuantumProver.LocalInstrumentMarginals.branchProbability (K h) (pureDensity ψ) = 0
    · rw [hp, zero_mul, zero_mul]
    · rw [QuantumProver.LocalInstrumentMarginals.normalizedUntouchedMarginal,
        normalizedBranch_pure_of_probability_ne_zero K ψ fallback h hp]
      change _ * AntisymmetricEntropyCost.vonNeumannEntropyBits
        (partialTraceLeft (pureDensity _)) =
        _ * entropyBits (partialTraceRight (pureDensity _))
      rw [AntisymmetricEntropyCost.pure_marginal_entropy_eq,
        AntisymmetricEntropyCost.vonNeumannEntropyBits_eq_quantumEntropyBits]
  calc
    _ = ∑ h, QuantumProver.LocalInstrumentMarginals.branchProbability (K h) (pureDensity ψ) *
        entropyBits (QuantumProver.LocalInstrumentMarginals.normalizedUntouchedMarginal K (pureDensity ψ) h) :=
      Finset.sum_congr rfl (fun h _ => he h)
    _ ≤ entropyBits (QuantumProver.QuantumEntropy.partialTrace_left (pureDensity ψ)) := hj
    _ = AntisymmetricEnsembleCost.aliceEntropy ψ := by
      change entropyBits (partialTraceRight (pureDensity ψ)) =
        AntisymmetricEntropyCost.vonNeumannEntropyBits (partialTraceLeft (pureDensity ψ))
      rw [AntisymmetricEntropyCost.pure_marginal_entropy_eq,
        AntisymmetricEntropyCost.vonNeumannEntropyBits_eq_quantumEntropyBits]

theorem exists_unitVector_of_density {I : Type*} [Fintype I] [DecidableEq I]
    (ρ : Matrix I I ℂ) (hρ : IsDensity ρ) : ∃ v : I → ℂ, vectorNormSq v = 1 := by
  classical
  have hI : Nonempty I := by
    by_contra hn
    letI : IsEmpty I := not_nonempty_iff.mp hn
    have ht : Matrix.trace ρ = 0 := by simp [Matrix.trace]
    rw [hρ.2] at ht
    exact one_ne_zero ht
  obtain ⟨i⟩ := hI
  refine ⟨Pi.single i 1, ?_⟩
  simp [vectorNormSq, Pi.single_apply]

def mixturePureEnsemble {J X : Type*} [Fintype J] [Fintype X] [DecidableEq X]
    (w : J → ℝ) (hw : ∀ j, 0 ≤ w j) (hs : ∑ j, w j = 1)
    (ρ : J → Matrix X X ℂ) (E : ∀ j, AntisymmetricEnsembleCost.FinitePureEnsemble (ρ j)) :
    AntisymmetricEnsembleCost.FinitePureEnsemble (∑ j, (w j : ℂ) • ρ j) where
  count := Fintype.card (Σ j, Fin (E j).count)
  weight := fun t =>
    let u := (Fintype.equivFin (Σ j, Fin (E j).count)).symm t
    w u.1 * (E u.1).weight u.2
  weight_nonneg := fun t => mul_nonneg (hw _) ((E _).weight_nonneg _)
  weight_sum := by
    rw [(Fintype.equivFin (Σ j, Fin (E j).count)).symm.sum_comp
      (fun u => w u.1 * (E u.1).weight u.2), Fintype.sum_sigma]
    simp only [← Finset.mul_sum, (E _).weight_sum, mul_one]
    exact hs
  vector := fun t =>
    let u := (Fintype.equivFin (Σ j, Fin (E j).count)).symm t
    (E u.1).vector u.2
  normalized := fun t => (E _).normalized _
  barycenter := by
    have he := (Fintype.equivFin (Σ j, Fin (E j).count)).symm.sum_comp
      (fun u => ((w u.1 * (E u.1).weight u.2 : ℝ) : ℂ) • pureDensity ((E u.1).vector u.2))
    rw [he, Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro j _
    conv_lhs => rw [(E j).barycenter]
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro t _
    rw [smul_smul, Complex.ofReal_mul]

theorem mixturePureEnsemble_averageAliceEntropy {J A B : Type*}
    [Fintype J] [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (w : J → ℝ) (hw : ∀ j, 0 ≤ w j) (hs : ∑ j, w j = 1)
    (ρ : J → Matrix (A × B) (A × B) ℂ)
    (E : ∀ j, AntisymmetricEnsembleCost.FinitePureEnsemble (ρ j)) :
    (mixturePureEnsemble w hw hs ρ E).averageAliceEntropy =
      ∑ j, w j * (E j).averageAliceEntropy := by
  have he := (Fintype.equivFin (Σ j, Fin (E j).count)).symm.sum_comp
    (fun u => (w u.1 * (E u.1).weight u.2) *
      AntisymmetricEnsembleCost.aliceEntropy ((E u.1).vector u.2))
  change (∑ t,
    let u := (Fintype.equivFin (Σ j, Fin (E j).count)).symm t
    (w u.1 * (E u.1).weight u.2) *
      AntisymmetricEnsembleCost.aliceEntropy ((E u.1).vector u.2)) = _
  rw [he, Fintype.sum_sigma]
  simp only [AntisymmetricEnsembleCost.FinitePureEnsemble.averageAliceEntropy,
    Finset.mul_sum, mul_assoc]

def swapVector {A B : Type*} (ψ : A × B → ℂ) : B × A → ℂ :=
  fun ba => ψ (ba.2, ba.1)

theorem vectorNormSq_swap {A B : Type*} [Fintype A] [Fintype B] (ψ : A × B → ℂ) :
    vectorNormSq (swapVector ψ) = vectorNormSq ψ := by
  simp only [vectorNormSq, swapVector, Fintype.sum_prod_type]
  exact Finset.sum_comm

theorem pureAliceEntropy_swap {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (ψ : A × B → ℂ) :
    AntisymmetricEnsembleCost.aliceEntropy (swapVector ψ) =
      AntisymmetricEnsembleCost.aliceEntropy ψ := by
  change AntisymmetricEntropyCost.vonNeumannEntropyBits
    (partialTraceLeft (pureDensity (swapVector ψ))) =
      AntisymmetricEntropyCost.vonNeumannEntropyBits (partialTraceLeft (pureDensity ψ))
  rw [show partialTraceLeft (pureDensity (swapVector ψ)) =
      partialTraceRight (pureDensity ψ) from rfl]
  exact (AntisymmetricEntropyCost.pure_marginal_entropy_eq ψ).symm

theorem normalizedPureVector_swap {A B : Type*} [Fintype A] [Fintype B]
    (ψ fallback : A × B → ℂ) :
    normalizedPureVector (swapVector ψ) (swapVector fallback) =
      swapVector (normalizedPureVector ψ fallback) := by
  funext ba
  by_cases hz : vectorNormSq ψ = 0 <;>
    simp [normalizedPureVector, vectorNormSq_swap, hz, swapVector, Pi.smul_apply]

theorem localLift_mulVec_swap {A B O : Type*}
    [Fintype A] [Fintype B] [Fintype O] [DecidableEq A] [DecidableEq B]
    (K : Matrix O B ℂ) (ψ : A × B → ℂ) :
    (QuantumProver.LocalInstrumentMarginals.localLift K).mulVec (swapVector ψ) =
      swapVector (((1 : Matrix A A ℂ) ⊗ₖ K).mulVec ψ) := by
  ext oa
  simp [QuantumProver.LocalInstrumentMarginals.localLift, swapVector, Matrix.mulVec, dotProduct,
    Matrix.kronecker_apply, Matrix.one_apply, Fintype.sum_prod_type, mul_ite, ite_mul]

theorem localMeasurementBob_average_pureAliceEntropy_le {H A B O : Type*}
    [Fintype H] [Fintype A] [Fintype B] [Fintype O]
    [DecidableEq A] [DecidableEq B] [DecidableEq O]
    (K : H → Matrix O B ℂ) (hK : ∑ h, (K h).conjTranspose * K h = 1)
    (ψ : A × B → ℂ) (hψ : vectorNormSq ψ = 1) (fallback : A × O → ℂ) :
    (∑ h, vectorNormSq (((1 : Matrix A A ℂ) ⊗ₖ K h).mulVec ψ) *
      AntisymmetricEnsembleCost.aliceEntropy (normalizedPureVector
        (((1 : Matrix A A ℂ) ⊗ₖ K h).mulVec ψ) fallback)) ≤
      AntisymmetricEnsembleCost.aliceEntropy ψ := by
  have hj := localMeasurement_average_pureAliceEntropy_le K hK
    (swapVector ψ) (by rw [vectorNormSq_swap, hψ]) (swapVector fallback)
  simpa only [branchProbability_pure, localLift_mulVec_swap, vectorNormSq_swap,
    normalizedPureVector_swap, pureAliceEntropy_swap] using hj

theorem weighted_normalizedPureDensity {I : Type*} [Fintype I]
    (v fallback : I → ℂ) :
    (vectorNormSq v : ℂ) • pureDensity (normalizedPureVector v fallback) = pureDensity v := by
  by_cases hz : vectorNormSq v = 0
  · have hv := matrix_vectorNormSq_eq_zero v hz
    rw [hz, Complex.ofReal_zero, zero_smul, hv]
    ext i j
    simp [pureDensity, crossDensity]
  · rw [normalizedPureVector, if_neg hz, matrix_pureDensity_scalar,
      inverse_norm_factor, smul_smul]
    have hp : (vectorNormSq v : ℂ) ≠ 0 := by exact_mod_cast hz
    rw [Complex.ofReal_inv, mul_inv_cancel₀ hp, one_smul]

theorem sandwich_pureDensity {I O : Type*} [Fintype I]
    (V : Matrix O I ℂ) (ψ : I → ℂ) :
    V * pureDensity ψ * V.conjTranspose = pureDensity (V.mulVec ψ) :=
  sandwich_crossDensity V ψ ψ

theorem isometry_mulVec_normSq {I O : Type*} [Fintype I] [Fintype O] [DecidableEq I]
    (V : Matrix O I ℂ) (hV : V.conjTranspose * V = 1) (ψ : I → ℂ) :
    vectorNormSq (V.mulVec ψ) = vectorNormSq ψ := by
  have ht := Matrix.trace_mul_cycle V (pureDensity ψ) V.conjTranspose
  rw [sandwich_pureDensity, pureDensity_trace, hV, Matrix.one_mul, pureDensity_trace] at ht
  exact Complex.ofReal_injective ht

theorem kraus_vectorNormSq_mass {H I O : Type*}
    [Fintype H] [Fintype I] [Fintype O] [DecidableEq I]
    (L : H → Matrix O I ℂ) (hL : ∑ h, (L h).conjTranspose * L h = 1)
    (ψ : I → ℂ) (hψ : vectorNormSq ψ = 1) :
    (∑ h, vectorNormSq ((L h).mulVec ψ)) = 1 := by
  have ht := congrArg Complex.re
    (OperationalEndpointCost.finiteKrausApply_trace L hL (pureDensity ψ))
  simp only [OperationalEndpointCost.finiteKrausApply, Matrix.trace_sum,
    Complex.re_sum, sandwich_pureDensity, pureDensity_trace, Complex.ofReal_re] at ht
  exact ht.trans hψ

theorem localIsometryAlice_entropy_le {A B O : Type*}
    [Fintype A] [Fintype B] [Fintype O]
    [DecidableEq A] [DecidableEq B] [DecidableEq O]
    (L : Matrix O A ℂ) (hL : L.conjTranspose * L = 1)
    (ψ : A × B → ℂ) (hψ : vectorNormSq ψ = 1) :
    AntisymmetricEnsembleCost.aliceEntropy
      ((L ⊗ₖ (1 : Matrix B B ℂ)).mulVec ψ) ≤ AntisymmetricEnsembleCost.aliceEntropy ψ := by
  have hc : (L ⊗ₖ (1 : Matrix B B ℂ)).conjTranspose *
      (L ⊗ₖ (1 : Matrix B B ℂ)) = 1 := by
    rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
      hL, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.one_kronecker_one]
  have hm := (isometry_mulVec_normSq _ hc ψ).trans hψ
  have hj := localMeasurement_average_pureAliceEntropy_le
    (fun _ : Unit => L) (by simpa using hL) ψ hψ
    ((L ⊗ₖ (1 : Matrix B B ℂ)).mulVec ψ)
  simpa [branchProbability_pure, QuantumProver.LocalInstrumentMarginals.localLift,
    hm, normalizedPureVector] using hj

theorem localIsometryBob_entropy_le {A B O : Type*}
    [Fintype A] [Fintype B] [Fintype O]
    [DecidableEq A] [DecidableEq B] [DecidableEq O]
    (L : Matrix O B ℂ) (hL : L.conjTranspose * L = 1)
    (ψ : A × B → ℂ) (hψ : vectorNormSq ψ = 1) :
    AntisymmetricEnsembleCost.aliceEntropy
      (((1 : Matrix A A ℂ) ⊗ₖ L).mulVec ψ) ≤ AntisymmetricEnsembleCost.aliceEntropy ψ := by
  have hc : ((1 : Matrix A A ℂ) ⊗ₖ L).conjTranspose *
      ((1 : Matrix A A ℂ) ⊗ₖ L) = 1 := by
    rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
      Matrix.conjTranspose_one, Matrix.one_mul, hL, Matrix.one_kronecker_one]
  have hm := (isometry_mulVec_normSq _ hc ψ).trans hψ
  have hj := localMeasurementBob_average_pureAliceEntropy_le
    (fun _ : Unit => L) (by simpa using hL) ψ hψ
    (((1 : Matrix A A ℂ) ⊗ₖ L).mulVec ψ)
  simpa [hm, normalizedPureVector] using hj

def singletonPureEnsemble {I : Type*} [Fintype I] [DecidableEq I]
    (ψ : I → ℂ) (hψ : vectorNormSq ψ = 1) :
    AntisymmetricEnsembleCost.FinitePureEnsemble (pureDensity ψ) where
  count := 1
  weight := fun _ => 1
  weight_nonneg := fun _ => by norm_num
  weight_sum := by simp
  vector := fun _ => ψ
  normalized := fun _ => hψ
  barycenter := by simp

theorem singletonPureEnsemble_averageAliceEntropy {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (ψ : A × B → ℂ) (hψ : vectorNormSq ψ = 1) :
    (singletonPureEnsemble ψ hψ).averageAliceEntropy =
      AntisymmetricEnsembleCost.aliceEntropy ψ := by
  change (∑ i : Fin 1, 1 * AntisymmetricEnsembleCost.aliceEntropy ψ) = _
  simp

theorem adaptiveStep_exists_entropyEnsemble {c d a b a' b' h z : ℕ}
    (L : Fin h → Fin z → Matrix (Fin a' × Fin b') (Fin a × Fin b) ℂ)
    (hL : ∑ j, ∑ k, (L j k).conjTranspose * L j k = 1)
    (next : Fin h → OperationalEndpointCost.FiniteLocalProtocol c d a' b')
    (hnext : ∀ j (u : Fin a' × Fin b' → ℂ), vectorNormSq u = 1 →
      ∃ E : AntisymmetricEnsembleCost.FinitePureEnsemble ((next j).apply (pureDensity u)),
        E.averageAliceEntropy ≤ AntisymmetricEnsembleCost.aliceEntropy u)
    (ψ : Fin a × Fin b → ℂ) (hψ : vectorNormSq ψ = 1)
    (hStep : ∀ fallback : Fin a' × Fin b' → ℂ, vectorNormSq fallback = 1 →
      (∑ jk : Fin h × Fin z, vectorNormSq ((L jk.1 jk.2).mulVec ψ) *
        AntisymmetricEnsembleCost.aliceEntropy
          (normalizedPureVector ((L jk.1 jk.2).mulVec ψ) fallback)) ≤
        AntisymmetricEnsembleCost.aliceEntropy ψ) :
    ∃ E : AntisymmetricEnsembleCost.FinitePureEnsemble
        (∑ j, (next j).apply (∑ k, L j k * pureDensity ψ * (L j k).conjTranspose)),
      E.averageAliceEntropy ≤ AntisymmetricEnsembleCost.aliceEntropy ψ := by
  classical
  let J := Fin h × Fin z
  let Lj : J → Matrix (Fin a' × Fin b') (Fin a × Fin b) ℂ := fun jk => L jk.1 jk.2
  have hc : ∑ jk, (Lj jk).conjTranspose * Lj jk = 1 := by
    simpa only [Lj, J, Fintype.sum_prod_type] using hL
  have hρ : IsDensity (OperationalEndpointCost.finiteKrausApply Lj (pureDensity ψ)) :=
    ⟨OperationalEndpointCost.finiteKrausApply_posSemidef Lj _ (pureDensity_posSemidef ψ), by
      rw [OperationalEndpointCost.finiteKrausApply_trace Lj hc, pureDensity_trace, hψ]
      rfl⟩
  obtain ⟨fallback, hf⟩ := exists_unitVector_of_density _ hρ
  let w : J → ℝ := fun jk => vectorNormSq ((Lj jk).mulVec ψ)
  let v : J → Fin a' × Fin b' → ℂ := fun jk =>
    normalizedPureVector ((Lj jk).mulVec ψ) fallback
  have hw : ∀ jk, 0 ≤ w jk := fun jk => matrix_vectorNormSq_nonneg _
  have hs : ∑ jk, w jk = 1 := kraus_vectorNormSq_mass Lj hc ψ hψ
  let ρ : J → Matrix (Fin c × Fin d) (Fin c × Fin d) ℂ := fun jk =>
    (next jk.1).apply (pureDensity (v jk))
  have hE : ∀ jk : J, ∃ E : AntisymmetricEnsembleCost.FinitePureEnsemble (ρ jk),
      E.averageAliceEntropy ≤ AntisymmetricEnsembleCost.aliceEntropy (v jk) := by
    intro jk
    exact hnext jk.1 (v jk) (normalizedPureVector_normSq _ _ hf)
  choose E he using hE
  have hstate : (∑ j, (next j).apply (∑ k, L j k * pureDensity ψ * (L j k).conjTranspose)) =
      ∑ jk : J, (w jk : ℂ) • ρ jk := by
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro j _
    rw [OperationalEndpointCost.FiniteLocalProtocol.apply_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [sandwich_pureDensity]
    change (next j).apply (pureDensity ((L j k).mulVec ψ)) =
      (vectorNormSq ((L j k).mulVec ψ) : ℂ) •
        (next j).apply (pureDensity (normalizedPureVector ((L j k).mulVec ψ) fallback))
    rw [← OperationalEndpointCost.FiniteLocalProtocol.apply_smul,
      weighted_normalizedPureDensity]
  rw [hstate]
  refine ⟨mixturePureEnsemble w hw hs ρ E, ?_⟩
  rw [mixturePureEnsemble_averageAliceEntropy]
  exact (Finset.sum_le_sum (fun jk _ => mul_le_mul_of_nonneg_left (he jk) (hw jk))).trans
    (hStep fallback hf)

theorem finiteLocalProtocol_output_entropyEnsemble {c d a b : ℕ}
    (T : OperationalEndpointCost.FiniteLocalProtocol c d a b)
    (ψ : Fin a × Fin b → ℂ) (hψ : vectorNormSq ψ = 1) :
    ∃ E : AntisymmetricEnsembleCost.FinitePureEnsemble (T.apply (pureDensity ψ)),
      E.averageAliceEntropy ≤ AntisymmetricEnsembleCost.aliceEntropy ψ := by
  induction T with
  | @terminal a b LA LB hLA hLB =>
    have hV : (LA ⊗ₖ LB).conjTranspose * (LA ⊗ₖ LB) = 1 := by
      rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
        hLA, hLB, Matrix.one_kronecker_one]
    have hv := (isometry_mulVec_normSq _ hV ψ).trans hψ
    have hLAj : (LA ⊗ₖ (1 : Matrix (Fin b) (Fin b) ℂ)).conjTranspose *
        (LA ⊗ₖ (1 : Matrix (Fin b) (Fin b) ℂ)) = 1 := by
      rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
        hLA, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.one_kronecker_one]
    have hψA := (isometry_mulVec_normSq _ hLAj ψ).trans hψ
    have hA := localIsometryAlice_entropy_le LA hLA ψ hψ
    have hB := localIsometryBob_entropy_le LB hLB
      ((LA ⊗ₖ (1 : Matrix (Fin b) (Fin b) ℂ)).mulVec ψ) hψA
    have hprod : (((1 : Matrix (Fin c) (Fin c) ℂ) ⊗ₖ LB).mulVec
        ((LA ⊗ₖ (1 : Matrix (Fin b) (Fin b) ℂ)).mulVec ψ)) =
        (LA ⊗ₖ LB).mulVec ψ := by
      rw [Matrix.mulVec_mulVec, ← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one]
    rw [hprod] at hB
    change ∃ E : AntisymmetricEnsembleCost.FinitePureEnsemble
        ((LA ⊗ₖ LB) * pureDensity ψ * (LA ⊗ₖ LB).conjTranspose),
      E.averageAliceEntropy ≤ AntisymmetricEnsembleCost.aliceEntropy ψ
    rw [sandwich_pureDensity]
    refine ⟨singletonPureEnsemble _ hv, ?_⟩
    rw [singletonPureEnsemble_averageAliceEntropy]
    exact hB.trans hA
  | @alice a b a' h z K hK next ih =>
    change ∃ E : AntisymmetricEnsembleCost.FinitePureEnsemble
        (∑ j, (next j).apply (∑ k, (K j k ⊗ₖ (1 : Matrix (Fin b) (Fin b) ℂ)) *
          pureDensity ψ * (K j k ⊗ₖ (1 : Matrix (Fin b) (Fin b) ℂ)).conjTranspose)),
      E.averageAliceEntropy ≤ AntisymmetricEnsembleCost.aliceEntropy ψ
    apply adaptiveStep_exists_entropyEnsemble
      (fun j k => K j k ⊗ₖ (1 : Matrix (Fin b) (Fin b) ℂ))
      (OperationalEndpointCost.FiniteLocalProtocol.alice_joint_complete K hK) next ih ψ hψ
    intro fallback _
    have hs := localMeasurement_average_pureAliceEntropy_le
      (fun jk : Fin h × Fin z => K jk.1 jk.2)
      (by simpa only [Fintype.sum_prod_type] using hK) ψ hψ fallback
    simpa only [branchProbability_pure, QuantumProver.LocalInstrumentMarginals.localLift] using hs
  | @bob a b b' h z K hK next ih =>
    change ∃ E : AntisymmetricEnsembleCost.FinitePureEnsemble
        (∑ j, (next j).apply (∑ k, ((1 : Matrix (Fin a) (Fin a) ℂ) ⊗ₖ K j k) *
          pureDensity ψ * ((1 : Matrix (Fin a) (Fin a) ℂ) ⊗ₖ K j k).conjTranspose)),
      E.averageAliceEntropy ≤ AntisymmetricEnsembleCost.aliceEntropy ψ
    apply adaptiveStep_exists_entropyEnsemble
      (fun j k => (1 : Matrix (Fin a) (Fin a) ℂ) ⊗ₖ K j k)
      (OperationalEndpointCost.FiniteLocalProtocol.bob_joint_complete K hK) next ih ψ hψ
    intro fallback _
    exact localMeasurementBob_average_pureAliceEntropy_le
      (fun jk : Fin h × Fin z => K jk.1 jk.2)
      (by simpa only [Fintype.sum_prod_type] using hK) ψ hψ fallback

theorem finiteLocalProtocol_pure_finiteConvexRoof_le {c d a b : ℕ}
    (T : OperationalEndpointCost.FiniteLocalProtocol c d a b)
    (ψ : Fin a × Fin b → ℂ) (hψ : vectorNormSq ψ = 1) :
    AntisymmetricEnsembleCost.finiteConvexRoof (T.apply (pureDensity ψ)) ≤
      (AntisymmetricEnsembleCost.aliceEntropy ψ : EReal) := by
  obtain ⟨E, hE⟩ := finiteLocalProtocol_output_entropyEnsemble T ψ hψ
  unfold AntisymmetricEnsembleCost.finiteConvexRoof
  apply iInf_le_of_le E
  exact_mod_cast hE

theorem finiteLocalProtocol_ensemble_entropy_le {c d a b : ℕ}
    (T : OperationalEndpointCost.FiniteLocalProtocol c d a b)
    (ρ : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ)
    (E : AntisymmetricEnsembleCost.FinitePureEnsemble ρ) :
    ∃ F : AntisymmetricEnsembleCost.FinitePureEnsemble (T.apply ρ),
      F.averageAliceEntropy ≤ E.averageAliceEntropy := by
  classical
  let σ : Fin E.count → Matrix (Fin c × Fin d) (Fin c × Fin d) ℂ := fun j =>
    T.apply (pureDensity (E.vector j))
  have hF : ∀ j, ∃ F : AntisymmetricEnsembleCost.FinitePureEnsemble (σ j),
      F.averageAliceEntropy ≤ AntisymmetricEnsembleCost.aliceEntropy (E.vector j) := by
    intro j
    exact finiteLocalProtocol_output_entropyEnsemble T (E.vector j) (E.normalized j)
  choose F hF using hF
  have hstate : T.apply ρ = ∑ j, (E.weight j : ℂ) • σ j := by
    calc
      _ = T.apply (∑ j, (E.weight j : ℂ) • pureDensity (E.vector j)) :=
        congrArg T.apply E.barycenter
      _ = _ := by
        rw [OperationalEndpointCost.FiniteLocalProtocol.apply_sum]
        simp_rw [OperationalEndpointCost.FiniteLocalProtocol.apply_smul]
        rfl
  rw [hstate]
  refine ⟨mixturePureEnsemble E.weight E.weight_nonneg E.weight_sum σ F, ?_⟩
  rw [mixturePureEnsemble_averageAliceEntropy]
  exact Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hF j) (E.weight_nonneg j))

theorem finiteLocalProtocol_finiteConvexRoof_le {c d a b : ℕ}
    (T : OperationalEndpointCost.FiniteLocalProtocol c d a b)
    (ρ : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) :
    AntisymmetricEnsembleCost.finiteConvexRoof (T.apply ρ) ≤
      AntisymmetricEnsembleCost.finiteConvexRoof ρ := by
  unfold AntisymmetricEnsembleCost.finiteConvexRoof
  apply le_iInf
  intro E
  obtain ⟨F, hF⟩ := finiteLocalProtocol_ensemble_entropy_le T ρ E
  apply iInf_le_of_le F
  exact_mod_cast hF

end QuantumProver.WernerEndpoint.LocalEntropy

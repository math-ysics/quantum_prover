import QuantumProver.InformationTheory.WernerEndpoint.AntisymmetricStates
import QuantumProver.InformationTheory.ElegantJointMeasurement.TailReferencePurity
import QuantumProver.InformationTheory.QuantumEntropy.Definitions
import QuantumProver.InformationTheory.ConditionalEntropy.ConditionalRange

noncomputable section
namespace QuantumProver.WernerEndpoint.AntisymmetricEntropyCost

open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator ContinuousFunctionalCalculus
open Matrix Unitary

variable {X : Type*} [Fintype X] [DecidableEq X]

theorem rclike_complex_cast (r : ℝ) : (RCLike.ofReal r : ℂ) = Complex.ofReal r := by
  with_reducible_and_instances rfl

def vonNeumannEntropyBits (ρ : Matrix X X ℂ) : ℝ :=
  QuantumProver.ElegantJointMeasurement.TailReference.vonNeumannEntropyBits ρ

theorem entropy_type_identity (ρ : Matrix X X ℂ) :
    vonNeumannEntropyBits ρ = (Matrix.trace (cfc Real.negMulLog ρ)).re / Real.log 2 := rfl

theorem normalized_sum_sq_pos (p : X → ℝ) (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) :
    0 < ∑ i, p i ^ 2 := by
  have hex : ∃ i, 0 < p i := by
    by_contra h
    push_neg at h
    have hz : ∑ i, p i = 0 := Finset.sum_eq_zero (fun i _ => le_antisymm (h i) (hp i))
    linarith
  obtain ⟨i, hi⟩ := hex
  exact (sq_pos_of_pos hi).trans_le (Finset.single_le_sum (fun j _ => sq_nonneg (p j))
    (Finset.mem_univ i))

theorem normalized_log_jensen (p : X → ℝ) (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) :
    (∑ i, p i * Real.log (p i)) ≤ Real.log (∑ i, p i ^ 2) := by
  let a := ∑ i, p i ^ 2
  have ha : 0 < a := normalized_sum_sq_pos p hp hs
  have ht (i : X) : p i * Real.log (p i) - p i * Real.log a ≤ p i ^ 2 / a - p i := by
    by_cases hz : p i = 0
    · simp [hz]
    · have hi : 0 < p i := lt_of_le_of_ne (hp i) (Ne.symm hz)
      calc
        _ = p i * Real.log (p i / a) := by
          rw [Real.log_div (ne_of_gt hi) (ne_of_gt ha)]
          ring
        _ ≤ p i * (p i / a - 1) :=
          mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos (div_pos hi ha)) (hp i)
        _ = _ := by ring
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => ht i)
  simp only [Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.sum_div, hs, one_mul] at hsum
  change (∑ i, p i * Real.log (p i)) - Real.log a ≤ a / a - 1 at hsum
  rw [div_self (ne_of_gt ha)] at hsum
  dsimp [a] at hsum ⊢
  linarith

theorem entropyBits_ge_renyi_two (p : X → ℝ) (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) :
    -Real.log (∑ i, p i ^ 2) / Real.log 2 ≤ QuantumProver.ElegantJointMeasurement.Entropy.entropyBits p := by
  have h := normalized_log_jensen p hp hs
  have hn : -Real.log (∑ i, p i ^ 2) ≤ ∑ i, Real.negMulLog (p i) := by
    simp only [Real.negMulLog_eq_neg, Finset.sum_neg_distrib]
    linarith
  exact (div_le_div_iff_of_pos_right (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mpr hn

theorem density_spectral_probability (ρ : Matrix X X ℂ) (hρ : ρ.PosSemidef)
    (htrace : Matrix.trace ρ = 1) :
    (∀ i, 0 ≤ hρ.isHermitian.eigenvalues i) ∧ (∑ i, hρ.isHermitian.eigenvalues i) = 1 := by
  refine ⟨hρ.eigenvalues_nonneg, ?_⟩
  have ht := congrArg Complex.re hρ.isHermitian.trace_eq_sum_eigenvalues
  rw [htrace] at ht
  simpa only [Complex.one_re, Complex.re_sum, rclike_complex_cast, Complex.ofReal_re] using ht.symm

theorem cfc_entropy_spectral (ρ : Matrix X X ℂ) (hρ : ρ.IsHermitian) :
    vonNeumannEntropyBits ρ = QuantumProver.ElegantJointMeasurement.Entropy.entropyBits hρ.eigenvalues := by
  rw [entropy_type_identity, hρ.cfc_eq, Matrix.IsHermitian.cfc,
    Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose,
    QuantumProver.ElegantJointMeasurement.TailReference.trace_unitary_conjugate,
    Matrix.trace_diagonal]
  simp only [Function.comp_apply, rclike_complex_cast, Complex.re_sum, Complex.ofReal_re,
    QuantumProver.ElegantJointMeasurement.Entropy.entropyBits]

theorem hermitian_purity_spectral (ρ : Matrix X X ℂ) (hρ : ρ.IsHermitian) :
    purity ρ = ∑ i, hρ.eigenvalues i ^ 2 := by
  let U := hρ.eigenvectorUnitary
  let D : Matrix X X ℂ := Matrix.diagonal (fun i => Complex.ofReal (hρ.eigenvalues i))
  have hd : ρ = (U : Matrix X X ℂ) * D * (U : Matrix X X ℂ)ᴴ := by
    simpa only [U, D, Unitary.conjStarAlgAut_apply, Function.comp_def,
      Matrix.star_eq_conjTranspose, rclike_complex_cast] using hρ.spectral_theorem
  have hu : (U : Matrix X X ℂ)ᴴ * (U : Matrix X X ℂ) = 1 := Unitary.coe_star_mul_self U
  have hdd : D * D = Matrix.diagonal (fun i => Complex.ofReal (hρ.eigenvalues i ^ 2)) := by
    simp only [D, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    simp [pow_two]
  have hsq : ρ * ρ = (U : Matrix X X ℂ) *
      Matrix.diagonal (fun i => Complex.ofReal (hρ.eigenvalues i ^ 2)) *
        (U : Matrix X X ℂ)ᴴ := by
    calc
      ρ * ρ = ((U : Matrix X X ℂ) * D * (U : Matrix X X ℂ)ᴴ) *
        ((U : Matrix X X ℂ) * D * (U : Matrix X X ℂ)ᴴ) := congrArg₂ (fun A B => A * B) hd hd
      _ = (U : Matrix X X ℂ) * (D * ((U : Matrix X X ℂ)ᴴ *
        (U : Matrix X X ℂ)) * D) * (U : Matrix X X ℂ)ᴴ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hu]; simp only [Matrix.mul_one, hdd]
  rw [purity, hsq, QuantumProver.ElegantJointMeasurement.TailReference.trace_unitary_conjugate, Matrix.trace_diagonal]
  simp only [Complex.re_sum, Complex.ofReal_re]

theorem density_entropy_ge_renyi_two (ρ : Matrix X X ℂ) (hρ : ρ.PosSemidef)
    (htrace : Matrix.trace ρ = 1) :
    -Real.log (purity ρ) / Real.log 2 ≤ vonNeumannEntropyBits ρ := by
  obtain ⟨hp, hs⟩ := density_spectral_probability ρ hρ htrace
  rw [cfc_entropy_spectral ρ hρ.isHermitian, hermitian_purity_spectral ρ hρ.isHermitian]
  exact entropyBits_ge_renyi_two _ hp hs

theorem density_purity_pos (ρ : Matrix X X ℂ) (hρ : ρ.PosSemidef)
    (htrace : Matrix.trace ρ = 1) : 0 < purity ρ := by
  obtain ⟨hp, hs⟩ := density_spectral_probability ρ hρ htrace
  rw [hermitian_purity_spectral ρ hρ.isHermitian]
  exact normalized_sum_sq_pos _ hp hs

theorem vonNeumannEntropyBits_eq_quantumEntropyBits (ρ : Matrix X X ℂ) :
    vonNeumannEntropyBits ρ = QuantumProver.QuantumEntropy.entropyBits ρ := by
  rw [entropy_type_identity, Real.negMulLog_eq_neg, cfc_neg,
    Matrix.trace_neg, Complex.neg_re]
  rfl

theorem pure_marginal_entropy_eq {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (ψ : A × B → ℂ) :
    vonNeumannEntropyBits (partialTraceLeft (pureDensity ψ)) =
      vonNeumannEntropyBits (partialTraceRight (pureDensity ψ)) := by
  let M : Matrix A B ℂ := fun a b => ψ (a,b)
  have hLeft : partialTraceLeft (pureDensity ψ) = M * M.conjTranspose := by
    ext a a'
    rfl
  have hRight : partialTraceRight (pureDensity ψ) =
      (M.conjTranspose * M).transpose := by
    ext b b'
    change (∑ a : A, ψ (a,b) * star (ψ (a,b'))) =
      ∑ a : A, star (ψ (a,b')) * ψ (a,b)
    apply Finset.sum_congr rfl
    intro a _
    ring
  rw [hLeft, hRight, vonNeumannEntropyBits_eq_quantumEntropyBits,
    vonNeumannEntropyBits_eq_quantumEntropyBits]
  change QuantumProver.SuperchannelDiscrimination.FlaggedStates.entropyBits (M * M.conjTranspose) =
    QuantumProver.SuperchannelDiscrimination.FlaggedStates.entropyBits
      (M.conjTranspose * M).transpose
  rw [QuantumProver.ConditionalEntropy.ConditionalRange.entropyBits_transpose
      (Matrix.posSemidef_conjTranspose_mul_self M).isHermitian]
  exact (QuantumProver.ConditionalEntropy.ConditionalRange.entropyBits_rectangularGram M).symm

end QuantumProver.WernerEndpoint.AntisymmetricEntropyCost

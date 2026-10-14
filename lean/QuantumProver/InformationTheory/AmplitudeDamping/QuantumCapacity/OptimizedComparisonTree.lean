import QuantumProver.InformationTheory.AmplitudeDamping.QuantumCapacity.OptimizedBlockChannels

set_option autoImplicit false
set_option maxHeartbeats 1200000

noncomputable section
open Matrix
open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder Matrix Kronecker

namespace QuantumProver.AmplitudeDamping.FiniteModel

def FiniteBlockProtocolB.optimizedPhaseOutput {p : ℝ} {n a b af bf : ℕ}
    (P : FiniteBlockProtocolB p n a b af bf) (z : ℝ) (σ : BipartiteMatrix a b) :
    BipartiteMatrix af bf :=
  match P with
  | .done _ _ => σ
  | .alice K next => ∑ j, (next j).optimizedPhaseOutput z
      (aliceOperator (b := b) (K.operator j) * σ *
        (aliceOperator (b := b) (K.operator j))ᴴ)
  | .bob K next => ∑ j, (next j).optimizedPhaseOutput z
      (bobOperator (a := a) (K.operator j) * σ *
        (bobOperator (a := a) (K.operator j))ᴴ)
  | .blockCall (a := a₀) (b := b₀) next =>
      next.optimizedPhaseOutput z (matrixOptimizedPhaseBlockOutput n p z a₀ b₀ σ)

theorem FiniteBlockProtocolB.optimizedPhaseOutput_posSemidef {p : ℝ} {n a b af bf : ℕ}
    (P : FiniteBlockProtocolB p n a b af bf) (z : ℝ) {σ : BipartiteMatrix a b}
    (hσ : σ.PosSemidef) : (P.optimizedPhaseOutput z σ).PosSemidef := by
  induction P with
  | done a b => exact hσ
  | alice K next ih =>
      exact Matrix.posSemidef_sum _ fun j _ =>
        ih j (hσ.mul_mul_conjTranspose_same _)
  | bob K next ih =>
      exact Matrix.posSemidef_sum _ fun j _ =>
        ih j (hσ.mul_mul_conjTranspose_same _)
  | blockCall next ih =>
      exact ih (matrixOptimizedPhaseBlockOutput_posSemidef _ _ _ _ _ hσ)

theorem FiniteBlockProtocolB.optimizedPhaseOutput_trace {p : ℝ} {n a b af bf : ℕ}
    (P : FiniteBlockProtocolB p n a b af bf) (z : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (σ : BipartiteMatrix a b) : (P.optimizedPhaseOutput z σ).trace = σ.trace := by
  induction P with
  | done a b => rfl
  | alice K next ih =>
      rw [FiniteBlockProtocolB.optimizedPhaseOutput, Matrix.trace_sum]
      simp_rw [ih]
      simpa only [Matrix.trace_sum] using krausSum_trace _ (aliceOperator_gram K) σ
  | bob K next ih =>
      rw [FiniteBlockProtocolB.optimizedPhaseOutput, Matrix.trace_sum]
      simp_rw [ih]
      simpa only [Matrix.trace_sum] using krausSum_trace _ (bobOperator_gram K) σ
  | blockCall next ih =>
      rw [FiniteBlockProtocolB.optimizedPhaseOutput, ih,
        matrixOptimizedPhaseBlockOutput_trace _ _ _ _ _ hp0 hp1]

theorem FiniteBlockProtocolB.optimizedPhaseOutput_sepPositive {p : ℝ} {n a b af bf : ℕ}
    (P : FiniteBlockProtocolB p n a b af bf) (z : ℝ) {σ : BipartiteMatrix a b}
    (hσ : SepPositive σ) : SepPositive (P.optimizedPhaseOutput z σ) := by
  induction P with
  | done a b => exact hσ
  | alice K next ih =>
      exact SepPositive.sum _ fun j => ih j (hσ.local_conjugation (K.operator j) 1)
  | bob K next ih =>
      exact SepPositive.sum _ fun j => ih j (hσ.local_conjugation 1 (K.operator j))
  | blockCall next ih =>
      exact ih (matrixOptimizedPhaseBlockOutput_sepPositive _ _ _ _ _ hσ)

theorem FiniteBlockProtocolB.optimizedPhaseOutput_isDensity {p : ℝ} {n a b af bf : ℕ}
    (P : FiniteBlockProtocolB p n a b af bf) (z : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {σ : BipartiteMatrix a b} (hσ : IsDensity σ) : IsDensity (P.optimizedPhaseOutput z σ) :=
  ⟨P.optimizedPhaseOutput_posSemidef z hσ.1,
    (P.optimizedPhaseOutput_trace z hp0 hp1 σ).trans hσ.2⟩

theorem FiniteBlockProtocolB.optimizedPhaseOutput_isSeparable {p : ℝ} {n a b af bf : ℕ}
    (P : FiniteBlockProtocolB p n a b af bf) (z : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {σ : BipartiteMatrix a b} (hσ : IsSeparable a b σ) :
    IsSeparable af bf (P.optimizedPhaseOutput z σ) :=
  (P.optimizedPhaseOutput_sepPositive z hσ.sepPositive).isSeparable
    ((P.optimizedPhaseOutput_trace z hp0 hp1 σ).trans hσ.isDensity.2)

end QuantumProver.AmplitudeDamping.FiniteModel

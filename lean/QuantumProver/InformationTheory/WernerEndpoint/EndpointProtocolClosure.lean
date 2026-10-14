import QuantumProver.InformationTheory.WernerEndpoint.OperationalEndpointCost
import Mathlib.Analysis.Matrix.Normed

set_option autoImplicit false

noncomputable section

namespace QuantumProver.WernerEndpoint.EndpointProtocolClosure

open OperationalEndpointCost
open scoped BigOperators ComplexOrder Topology Matrix.Norms.Elementwise

abbrev OutputMatrix (c d : ℕ) := Matrix (Fin c × Fin d) (Fin c × Fin d) ℂ

def finiteOutputs {c d a b : ℕ} (ψ : Fin a × Fin b → ℂ) : Set (OutputMatrix c d) :=
  {ρ | ∃ T : FiniteLocalProtocol c d a b, ρ = T.apply (pureDensity ψ)}

def outputClosure {c d a b : ℕ} (ψ : Fin a × Fin b → ℂ) : Set (OutputMatrix c d) :=
  closure (finiteOutputs ψ)

theorem finiteOutput_mem_closure {c d a b : ℕ} (ψ : Fin a × Fin b → ℂ)
    (T : FiniteLocalProtocol c d a b) : T.apply (pureDensity ψ) ∈ outputClosure ψ :=
  subset_closure ⟨T, rfl⟩

theorem outputClosure_isClosed {c d a b : ℕ} (ψ : Fin a × Fin b → ℂ) :
    IsClosed (outputClosure (c := c) (d := d) ψ) := isClosed_closure

theorem finiteOutputs_isDensity {c d a b : ℕ} (ψ : Fin a × Fin b → ℂ)
    (hψ : vectorNormSq ψ = 1) {ρ : OutputMatrix c d} (hρ : ρ ∈ finiteOutputs ψ) :
    ρ.PosSemidef ∧ Matrix.trace ρ = 1 := by
  rcases hρ with ⟨T, rfl⟩
  refine ⟨T.apply_posSemidef _ (pureDensity_posSemidef ψ), ?_⟩
  rw [T.apply_trace, pureDensity_trace, hψ]
  rfl

theorem densitySet_isClosed (c d : ℕ) :
    IsClosed {ρ : OutputMatrix c d | ρ.PosSemidef ∧ Matrix.trace ρ = 1} := by
  exact Matrix.posSemidef_is_closed.inter
    (isClosed_eq continuous_id.matrix_trace continuous_const)

theorem outputClosure_isDensity {c d a b : ℕ} (ψ : Fin a × Fin b → ℂ)
    (hψ : vectorNormSq ψ = 1) {ρ : OutputMatrix c d} (hρ : ρ ∈ outputClosure ψ) :
    ρ.PosSemidef ∧ Matrix.trace ρ = 1 := by
  exact closure_minimal (fun _ h => finiteOutputs_isDensity ψ hψ h)
    (densitySet_isClosed c d) hρ

theorem mem_outputClosure_iff_approximation {c d a b : ℕ}
    (ψ : Fin a × Fin b → ℂ) (ρ : OutputMatrix c d) :
    ρ ∈ outputClosure ψ ↔ ∀ epsilon : ℝ, 0 < epsilon →
      ∃ T : FiniteLocalProtocol c d a b,
        dist (T.apply (pureDensity ψ)) ρ < epsilon := by
  constructor
  · intro h epsilon hepsilon
    obtain ⟨σ, hσ, hDist⟩ := Metric.mem_closure_iff.mp h epsilon hepsilon
    rcases hσ with ⟨T, rfl⟩
    exact ⟨T, by simpa only [dist_comm] using hDist⟩
  · intro h
    apply Metric.mem_closure_iff.mpr
    intro epsilon hepsilon
    obtain ⟨T, hT⟩ := h epsilon hepsilon
    exact ⟨T.apply (pureDensity ψ), ⟨T, rfl⟩, by simpa only [dist_comm] using hT⟩

def expectation {c d : ℕ} (P ρ : OutputMatrix c d) : ℝ :=
  (Matrix.trace (P * ρ)).re

theorem continuous_expectation {c d : ℕ} (P : OutputMatrix c d) :
    Continuous (expectation P) := by
  exact Complex.continuous_re.comp
    ((continuous_const.matrix_mul continuous_id).matrix_trace)

theorem outputClosure_expectation_le {c d a b : ℕ}
    (ψ : Fin a × Fin b → ℂ) (P : OutputMatrix c d) (r : ℝ)
    (hFinite : ∀ T : FiniteLocalProtocol c d a b,
      expectation P (T.apply (pureDensity ψ)) ≤ r)
    {ρ : OutputMatrix c d} (hρ : ρ ∈ outputClosure ψ) : expectation P ρ ≤ r := by
  have hClosed : IsClosed {σ : OutputMatrix c d | expectation P σ ≤ r} :=
    isClosed_le (continuous_expectation P) continuous_const
  apply closure_minimal (t := {σ : OutputMatrix c d | expectation P σ ≤ r}) ?_ hClosed hρ
  rintro σ ⟨T, rfl⟩
  exact hFinite T

theorem outputClosure_continuous_loss_le {c d a b : ℕ}
    (ψ : Fin a × Fin b → ℂ) (P : OutputMatrix c d) (loss : ℝ → ℝ)
    (hLoss : Continuous loss) (r : ℝ)
    (hFinite : ∀ T : FiniteLocalProtocol c d a b,
      loss (1 - expectation P (T.apply (pureDensity ψ))) ≤ r)
    {ρ : OutputMatrix c d} (hρ : ρ ∈ outputClosure ψ) :
    loss (1 - expectation P ρ) ≤ r := by
  have hContinuous : Continuous (fun σ : OutputMatrix c d =>
      loss (1 - expectation P σ)) :=
    hLoss.comp (continuous_const.sub (continuous_expectation P))
  have hClosed : IsClosed {σ : OutputMatrix c d | loss (1 - expectation P σ) ≤ r} :=
    isClosed_le hContinuous continuous_const
  apply closure_minimal (t := {σ : OutputMatrix c d | loss (1 - expectation P σ) ≤ r})
    ?_ hClosed hρ
  rintro σ ⟨T, rfl⟩
  exact hFinite T

end QuantumProver.WernerEndpoint.EndpointProtocolClosure

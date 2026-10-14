import QuantumProver.InformationTheory.DepolarizingSquashedEntanglement.PressureBound
import QuantumProver.InformationTheory.DepolarizingSquashedEntanglement.BCYOneWaySeparation

set_option autoImplicit false
set_option maxHeartbeats 1200000

noncomputable section

open Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker

namespace QuantumProver.DepolarizingSquashedEntanglement.BCYBoundary

variable {E : Type*} [Fintype E] [DecidableEq E]

def boundaryBellDensity (δ : ℝ) (hδ : 0 ≤ δ) (hmax : δ ≤ 21/512)
    (S : CPTP CanonicalEnvironment E) : Density ((Qubit × Qubit) × E) :=
  postSquashingDensity (Identities.boundaryMixing_physical hδ hmax).1
    (Identities.boundaryMixing_physical hδ hmax).2 bellKet bellKet_normalized S

def boundaryBellABDensity (δ : ℝ) (hδ : 0 ≤ δ) (hmax : δ ≤ 21/512)
    (S : CPTP CanonicalEnvironment E) : Density (Qubit × Qubit) where
  matrix := partialTraceRight (boundaryBellDensity δ hδ hmax S).matrix
  positive := partialTraceRight_positive (boundaryBellDensity δ hδ hmax S).positive
  trace_one := (partialTraceRight_trace _).trans
    (boundaryBellDensity δ hδ hmax S).trace_one

theorem boundaryBellABDensity_channel (δ : ℝ) (hδ : 0 ≤ δ) (hmax : δ ≤ 21/512)
    (S : CPTP CanonicalEnvironment E) :
    (boundaryBellABDensity δ hδ hmax S).matrix =
      ((1-boundaryMixing δ : ℝ) : ℂ) • pureDensity bellKet +
        ((boundaryMixing δ/4 : ℝ) : ℂ) • (1 : QMatrix (Qubit × Qubit)) := by
  have hp := Identities.boundaryMixing_physical hδ hmax
  change partialTraceRight (postSquashing (boundaryMixing δ) bellKet S) = _
  rw [postSquashing_AB, extendedInputKet_AB hp.1 hp.2, depolarizing_bell_density]

theorem boundaryBellABDensity_fidelity (δ : ℝ) (hδ : 0 ≤ δ) (hmax : δ ≤ 21/512)
    (S : CPTP CanonicalEnvironment E) :
    (Matrix.trace (c1BellProjector * (boundaryBellABDensity δ hδ hmax S).matrix)).re =
      1/2+δ := by
  rw [boundaryBellABDensity_channel, ← PressureBound.bellProjector_eq_pureDensity]
  simp only [Matrix.mul_add, Matrix.mul_smul, Matrix.trace_add, Complex.add_re,
    PressureBound.bellProjector_square, Matrix.mul_one, Matrix.trace_smul,
    c1BellProjector_trace, smul_eq_mul, mul_one, Complex.ofReal_re]
  dsimp [boundaryMixing]
  ring

theorem separableOneWayDistance_lower_of_fidelity (ρ : Density (Qubit × Qubit))
    (δ : ℝ)
    (hF : (Matrix.trace (c1BellProjector * ρ.matrix)).re = (1/2 : ℝ)+δ) :
    4*δ/3 ≤ BCYOneWaySeparation.separableOneWayDistance ρ := by
  unfold BCYOneWaySeparation.separableOneWayDistance
  apply le_csInf
  · exact ⟨_, BCYOneWaySeparation.marginalProduct ρ,
      BCYOneWaySeparation.marginalProduct_isSeparable ρ, rfl⟩
  · rintro v ⟨σ, hσ, rfl⟩
    exact c1_oneWay_distance_boundary_witness ρ σ hσ δ hF

theorem boundaryBellABDensity_separableOneWayDistance_lower
    (δ : ℝ) (hδ : 0 ≤ δ) (hmax : δ ≤ 21/512)
    (S : CPTP CanonicalEnvironment E) :
    4*δ/3 ≤ BCYOneWaySeparation.separableOneWayDistance
      (boundaryBellABDensity δ hδ hmax S) :=
  separableOneWayDistance_lower_of_fidelity _ δ
    (boundaryBellABDensity_fidelity δ hδ hmax S)

theorem separableOneWayDistance_squared_lower_of_fidelity
    (ρ : Density (Qubit × Qubit)) (δ : ℝ) (hδ : 0 ≤ δ)
    (hF : (Matrix.trace (c1BellProjector * ρ.matrix)).re = (1/2 : ℝ)+δ) :
    δ^2/(9*Real.log 2) ≤
      (BCYOneWaySeparation.separableOneWayDistance ρ)^2/(16*Real.log 2) := by
  have hd := separableOneWayDistance_lower_of_fidelity ρ δ hF
  have hleft : 0 ≤ 4*δ/3 := by positivity
  have hs := (sq_le_sq₀ hleft (hleft.trans hd)).mpr hd
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  calc
    δ^2/(9*Real.log 2) = (4*δ/3)^2/(16*Real.log 2) := by
      field_simp [hl.ne'] <;> ring
    _ ≤ _ := div_le_div_of_nonneg_right hs (by positivity)

theorem boundaryBellABDensity_separableOneWayDistance_squared_lower
    (δ : ℝ) (hδ : 0 ≤ δ) (hmax : δ ≤ 21/512)
    (S : CPTP CanonicalEnvironment E) :
    δ^2/(9*Real.log 2) ≤
      (BCYOneWaySeparation.separableOneWayDistance
        (boundaryBellABDensity δ hδ hmax S))^2/(16*Real.log 2) :=
  separableOneWayDistance_squared_lower_of_fidelity _ δ hδ
    (boundaryBellABDensity_fidelity δ hδ hmax S)

end QuantumProver.DepolarizingSquashedEntanglement.BCYBoundary

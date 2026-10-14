import QuantumProver.InformationTheory.WernerEndpoint.PurityTheorems
import QuantumProver.QuantumChannels.SquareQuantumTerminal

set_option autoImplicit false

noncomputable section

namespace QuantumProver.WernerEndpoint

open OperationalEndpointCost
open scoped ComplexOrder Topology

abbrev SingletOutputMatrix (d n : ℕ) :=
  EndpointProtocolClosure.OutputMatrix (Fintype.card (PhysicalPower d n))
    (Fintype.card (PhysicalPower d n))

def physicalSingletOutput (d n : ℕ) (σ : SingletOutputMatrix d n) :
    Matrix (PhysicalPower d n × PhysicalPower d n)
      (PhysicalPower d n × PhysicalPower d n) ℂ :=
  σ.submatrix (physicalPairFiniteEquiv d n).symm (physicalPairFiniteEquiv d n).symm

theorem outputLimit_mem_outputClosure {a b c d : ℕ}
    (ψ : Fin a × Fin b → ℂ) (outputs : ℕ → EndpointProtocolClosure.OutputMatrix c d)
    (σ : EndpointProtocolClosure.OutputMatrix c d)
    (hPrefix : ∀ N, outputs N ∈ EndpointProtocolClosure.outputClosure ψ)
    (hLimit : Filter.Tendsto outputs Filter.atTop (nhds σ)) :
    σ ∈ EndpointProtocolClosure.outputClosure ψ :=
  (EndpointProtocolClosure.outputClosure_isClosed ψ).mem_of_tendsto hLimit
    (Filter.Eventually.of_forall hPrefix)

theorem physicalSingletOutput_density (d n m : ℕ) (σ : SingletOutputMatrix d n)
    (hσ : σ ∈ EndpointProtocolClosure.outputClosure (finiteSingletPairPowerVector m)) :
    (physicalSingletOutput d n σ).PosSemidef ∧
      (physicalSingletOutput d n σ).trace = 1 := by
  have hDensity := EndpointProtocolClosure.outputClosure_isDensity
    (finiteSingletPairPowerVector m) (finiteSingletPairPowerVector_normSq m) hσ
  refine ⟨hDensity.1.submatrix _, ?_⟩
  exact ((physicalPairFiniteEquiv d n).symm.sum_comp (fun i => σ i i)).trans hDensity.2

theorem physicalAntisymmetricState_singletOutputClosure_projector_lower
    (d : ℕ) (hd : 2 ≤ d) (n m : ℕ) (σ : SingletOutputMatrix d n)
    (hσ : σ ∈ EndpointProtocolClosure.outputClosure (finiteSingletPairPowerVector m)) :
    (n : ℝ) - QuantumProver.ConditionalEntropy.winterBound (PhysicalPower d n)
      (Real.sqrt (1 - (Matrix.trace (physicalTensorAntisymmetrizer d n *
        physicalSingletOutput d n σ)).re)) ≤ (m : ℝ) := by
  rw [outputClosure_singlet_eq_bell] at hσ
  exact physicalAntisymmetricState_finiteOutputClosure_projector_lower d hd n m σ hσ

theorem physicalAntisymmetricState_singletOutputClosure_leakage_bounds
    (d : ℕ) (hd : 2 ≤ d) (n m : ℕ) (σ : SingletOutputMatrix d n)
    (hσ : σ ∈ EndpointProtocolClosure.outputClosure (finiteSingletPairPowerVector m))
    (epsilon : ℝ) (hBures : FidelityError.buresDistance
      (physicalSingletOutput d n σ) (physicalAntisymmetricState d n) ≤ epsilon) :
    0 ≤ 1 - (Matrix.trace (physicalTensorAntisymmetrizer d n *
      physicalSingletOutput d n σ)).re ∧
    1 - (Matrix.trace (physicalTensorAntisymmetrizer d n *
      physicalSingletOutput d n σ)).re ≤ epsilon := by
  let rho := physicalSingletOutput d n σ
  have hRho := physicalSingletOutput_density d n m σ hσ
  have hEffect := projector_isEffect (physicalTensorAntisymmetrizer d n)
    (physicalTensorAntisymmetrizer_hermitian d n)
    (physicalTensorAntisymmetrizer_idempotent d n)
  have hAccept := QuantumProver.SuperchannelDiscrimination.FlaggedStates.acceptanceProbability_bounds
    hRho hEffect
  rw [QuantumProver.SuperchannelDiscrimination.FlaggedStates.acceptanceProbability,
    Matrix.trace_mul_comm] at hAccept
  have hDistance := FidelityError.halfTraceDistance_le_of_buresDistance_le
    rho (physicalAntisymmetricState d n) hRho
    (physicalAntisymmetricState_density d hd n) epsilon hBures
  unfold FidelityError.halfTraceDistance at hDistance
  have hTrace : rho.trace = (physicalAntisymmetricState d n).trace := by
    rw [hRho.2, (physicalAntisymmetricState_density d hd n).2]
  have hExp := effect_expectation_schatten_distance
    (physicalTensorAntisymmetrizer d n) rho (physicalAntisymmetricState d n)
    hEffect hRho.1.isHermitian (physicalAntisymmetricState_posSemidef d n).isHermitian hTrace
  rw [physicalAntisymmetricState_projector_expectation_one d hd n] at hExp
  have hLow := (abs_le.mp hExp).1
  constructor <;> dsimp only [rho] at * <;> linarith

theorem physicalAntisymmetricState_singletOutputClosure_uniform_rate_lower
    (d : ℕ) (hd : 2 ≤ d) (n m : ℕ) (hn : 0 < n) (σ : SingletOutputMatrix d n)
    (hσ : σ ∈ EndpointProtocolClosure.outputClosure (finiteSingletPairPowerVector m)) :
    1 - QuantumProver.ConditionalEntropy.winterBound (Fin d)
      (Real.sqrt (1 - (Matrix.trace (physicalTensorAntisymmetrizer d n *
        physicalSingletOutput d n σ)).re)) ≤ (m : ℝ) / (n : ℝ) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hResource := physicalAntisymmetricState_singletOutputClosure_projector_lower
    d hd n m σ hσ
  have hDiv := (div_le_div_iff_of_pos_right hnR).mpr hResource
  rw [sub_div, div_self (ne_of_gt hnR)] at hDiv
  have hUniform := perCopy_physicalWinterBound_le d n hn
    (Real.sqrt (1 - (Matrix.trace (physicalTensorAntisymmetrizer d n *
      physicalSingletOutput d n σ)).re)) (Real.sqrt_nonneg _)
  linarith

theorem singletOutputClosure_HHTRate_lower (d : ℕ) (hd : 2 ≤ d) (r : ℝ)
    (hRate : ∀ epsilon : ℝ, 0 < epsilon → ∀ delta : ℝ, 0 < delta →
      ∃ n m : ℕ, 0 < n ∧ ∃ σ : SingletOutputMatrix d n,
        σ ∈ EndpointProtocolClosure.outputClosure (finiteSingletPairPowerVector m) ∧
        |r - (m : ℝ) / (n : ℝ)| ≤ delta ∧
        FidelityError.buresDistance (physicalSingletOutput d n σ)
          (physicalAntisymmetricState d n) ≤ epsilon) : 1 ≤ r := by
  classical
  let epsilon : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
  have hPositive : ∀ k, 0 < epsilon k := fun k => one_div_pos.mpr (by positivity)
  have hEpsilon : Filter.Tendsto epsilon Filter.atTop (nhds (0 : ℝ)) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  choose n m hn σ hσ hApprox hBures using
    fun k : ℕ => hRate (epsilon k) (hPositive k) (epsilon k) (hPositive k)
  let leakage : ℕ → ℝ := fun k => 1 - (Matrix.trace (physicalTensorAntisymmetrizer d (n k) *
    physicalSingletOutput d (n k) (σ k))).re
  have hLeak : ∀ k, 0 ≤ leakage k ∧ leakage k ≤ epsilon k := fun k =>
    physicalAntisymmetricState_singletOutputClosure_leakage_bounds
      d hd (n k) (m k) (σ k) (hσ k) (epsilon k) (hBures k)
  have hLeakLimit : Filter.Tendsto leakage Filter.atTop (nhds (0 : ℝ)) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hEpsilon
      (fun k => (hLeak k).1) (fun k => (hLeak k).2)
  have hSqrt : Filter.Tendsto (fun k => Real.sqrt (leakage k))
      Filter.atTop (nhds (0 : ℝ)) := by
    simpa only [Function.comp_def, Real.sqrt_zero] using
      Real.continuous_sqrt.continuousAt.tendsto.comp hLeakLimit
  have hCorrection : Filter.Tendsto
      (fun k => QuantumProver.ConditionalEntropy.winterBound (Fin d) (Real.sqrt (leakage k)))
      Filter.atTop (nhds (0 : ℝ)) :=
    (QuantumProver.ConditionalEntropy.winterBound_tendsto_zero (Fin d)).comp hSqrt
  have hBound : ∀ k, 1 -
      QuantumProver.ConditionalEntropy.winterBound (Fin d) (Real.sqrt (leakage k)) - epsilon k ≤ r := by
    intro k
    have hResource := physicalAntisymmetricState_singletOutputClosure_uniform_rate_lower
      d hd (n k) (m k) (hn k) (σ k) (hσ k)
    have hRatio := (abs_le.mp (hApprox k)).1
    change 1 - QuantumProver.ConditionalEntropy.winterBound (Fin d) (Real.sqrt (leakage k)) ≤
      (m k : ℝ) / (n k : ℝ) at hResource
    linarith
  have hLimit : Filter.Tendsto (fun k => 1 -
      QuantumProver.ConditionalEntropy.winterBound (Fin d) (Real.sqrt (leakage k)) - epsilon k)
      Filter.atTop (nhds (1 : ℝ)) := by
    simpa only [sub_zero] using
      ((tendsto_const_nhds (x := (1 : ℝ))).sub hCorrection).sub hEpsilon
  exact le_of_tendsto_of_tendsto hLimit tendsto_const_nhds (Filter.Eventually.of_forall hBound)

section SquareQuantumOutput

open QuantumProver.ElegantJointMeasurement.HilbertSquareProcess QuantumProver.MatrixSquareQuantumTerminal
open scoped Matrix.Norms.L2Operator

universe u

variable {R : Type u} [MeasurableSpace R] {a b c d : ℕ}

theorem squareQuantumOutputLimit_exists_finiteProtocol_approx
    (P : SquareProcess a b R) (Q : (N : ℕ) → FinalTerminal a b c d R N)
    (hc : 0 < c) (hd : 0 < d) (X : QuantumProver.ElegantJointMeasurement.HilbertSquareProcess.JointMatrix a b)
    (σ : QuantumProver.ElegantJointMeasurement.HilbertSquareProcess.JointMatrix c d)
    (hLimit : Filter.Tendsto (fun N => finiteHorizonChannel P N (Q N) X)
      Filter.atTop (nhds σ)) (ε : ℝ) (hε : 0 < ε) :
    ∃ U : FiniteLocalProtocol c d a b, ‖U.apply X - σ‖ < ε := by
  have hHalf : 0 < ε / 2 := half_pos hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hLimit (ε / 2) hHalf
  obtain ⟨U, hU⟩ := QuantumProver.MatrixSquareQuantumTerminal.exists_finiteProtocol_output_approx
    P N (Q N) hc hd X (ε / 2) hHalf
  have hTail : ‖finiteHorizonChannel P N (Q N) X - σ‖ < ε / 2 := by
    simpa only [dist_eq_norm] using hN N le_rfl
  refine ⟨U, ?_⟩
  calc
    ‖U.apply X - σ‖ ≤ ‖U.apply X - finiteHorizonChannel P N (Q N) X‖ +
        ‖finiteHorizonChannel P N (Q N) X - σ‖ := by
      simpa only [dist_eq_norm] using
        dist_triangle (U.apply X) (finiteHorizonChannel P N (Q N) X) σ
    _ < ε := by linarith

theorem squareQuantumOutputLimit_mem_outputClosure
    (P : SquareProcess a b R) (Q : (N : ℕ) → FinalTerminal a b c d R N)
    (hc : 0 < c) (hd : 0 < d) (ψ : Fin a × Fin b → ℂ)
    (σ : QuantumProver.ElegantJointMeasurement.HilbertSquareProcess.JointMatrix c d)
    (hLimit : Filter.Tendsto (fun N => finiteHorizonChannel P N (Q N) (pureDensity ψ))
      Filter.atTop (nhds σ)) :
    σ ∈ EndpointProtocolClosure.outputClosure ψ :=
  outputLimit_mem_outputClosure ψ _ σ
    (fun N => pureOutput_mem_outputClosure P N (Q N) hc hd ψ) hLimit

theorem squareQuantumOutputLimit_isDensity
    (P : SquareProcess a b R) (Q : (N : ℕ) → FinalTerminal a b c d R N)
    (hc : 0 < c) (hd : 0 < d) (ψ : Fin a × Fin b → ℂ)
    (hψ : vectorNormSq ψ = 1) (σ : QuantumProver.ElegantJointMeasurement.HilbertSquareProcess.JointMatrix c d)
    (hLimit : Filter.Tendsto (fun N => finiteHorizonChannel P N (Q N) (pureDensity ψ))
      Filter.atTop (nhds σ)) : QuantumProver.QuantumEntropy.IsDensity σ :=
  EndpointProtocolClosure.outputClosure_isDensity ψ hψ
    (squareQuantumOutputLimit_mem_outputClosure P Q hc hd ψ σ hLimit)

private theorem singletOutput_dimension_pos (d n : ℕ) (hd : 2 ≤ d) :
    0 < Fintype.card (PhysicalPower d n) := by
  rw [physicalPower_card]
  exact pow_pos (by omega) n

theorem physicalAntisymmetricState_squareQuantumOutputLimit_projector_lower
    (d : ℕ) (hd : 2 ≤ d) (n m : ℕ)
    (P : SquareProcess (Fintype.card (PhysicalPower 2 m))
      (Fintype.card (PhysicalPower 2 m)) R)
    (Q : (N : ℕ) → FinalTerminal (Fintype.card (PhysicalPower 2 m))
      (Fintype.card (PhysicalPower 2 m)) (Fintype.card (PhysicalPower d n))
      (Fintype.card (PhysicalPower d n)) R N)
    (σ : SingletOutputMatrix d n)
    (hLimit : Filter.Tendsto (fun N => finiteHorizonChannel P N (Q N)
        (pureDensity (finiteSingletPairPowerVector m))) Filter.atTop (nhds σ)) :
    (n : ℝ) - QuantumProver.ConditionalEntropy.winterBound (PhysicalPower d n)
      (Real.sqrt (1 - (Matrix.trace (physicalTensorAntisymmetrizer d n *
        physicalSingletOutput d n σ)).re)) ≤ (m : ℝ) :=
  physicalAntisymmetricState_singletOutputClosure_projector_lower d hd n m σ
    (squareQuantumOutputLimit_mem_outputClosure P Q (singletOutput_dimension_pos d n hd)
      (singletOutput_dimension_pos d n hd) (finiteSingletPairPowerVector m) σ hLimit)

theorem physicalAntisymmetricState_squareQuantumOutputLimit_uniform_rate_lower
    (d : ℕ) (hd : 2 ≤ d) (n m : ℕ) (hn : 0 < n)
    (P : SquareProcess (Fintype.card (PhysicalPower 2 m))
      (Fintype.card (PhysicalPower 2 m)) R)
    (Q : (N : ℕ) → FinalTerminal (Fintype.card (PhysicalPower 2 m))
      (Fintype.card (PhysicalPower 2 m)) (Fintype.card (PhysicalPower d n))
      (Fintype.card (PhysicalPower d n)) R N)
    (σ : SingletOutputMatrix d n)
    (hLimit : Filter.Tendsto (fun N => finiteHorizonChannel P N (Q N)
        (pureDensity (finiteSingletPairPowerVector m))) Filter.atTop (nhds σ)) :
    1 - QuantumProver.ConditionalEntropy.winterBound (Fin d)
      (Real.sqrt (1 - (Matrix.trace (physicalTensorAntisymmetrizer d n *
        physicalSingletOutput d n σ)).re)) ≤ (m : ℝ) / (n : ℝ) :=
  physicalAntisymmetricState_singletOutputClosure_uniform_rate_lower d hd n m hn σ
    (squareQuantumOutputLimit_mem_outputClosure P Q (singletOutput_dimension_pos d n hd)
      (singletOutput_dimension_pos d n hd) (finiteSingletPairPowerVector m) σ hLimit)

end SquareQuantumOutput

def endpointSingletFinitePreparation (d : ℕ) (hd : 2 ≤ d) (n : ℕ) :
    FiniteLocalProtocol (Fintype.card (PhysicalPower d n))
      (Fintype.card (PhysicalPower d n)) (Fintype.card (PhysicalPower 2 n))
      (Fintype.card (PhysicalPower 2 n)) :=
  SingletResource.singletToBellProtocol n (finiteQubitEquiv n)
    (endpointFiniteLocalProtocol d hd n)

theorem endpointSingletFinitePreparation_physicalOutput (d : ℕ) (hd : 2 ≤ d) (n : ℕ) :
    physicalSingletOutput d n ((endpointSingletFinitePreparation d hd n).apply
      (pureDensity (finiteSingletPairPowerVector n))) = physicalAntisymmetricState d n := by
  change physicalFiniteSingletProtocolOutput d n n
    (endpointSingletFinitePreparation d hd n) = physicalAntisymmetricState d n
  unfold endpointSingletFinitePreparation
  rw [physicalFiniteSingletProtocolOutput_toBell, physicalFiniteProtocolOutput_endpoint]

theorem endpointSingletFinitePreparation_buresError_zero (d : ℕ) (hd : 2 ≤ d) (n : ℕ) :
    FidelityError.buresDistance
      (physicalSingletOutput d n ((endpointSingletFinitePreparation d hd n).apply
        (pureDensity (finiteSingletPairPowerVector n)))) (physicalAntisymmetricState d n) = 0 := by
  rw [endpointSingletFinitePreparation_physicalOutput,
    FidelityError.buresDistance_self _ (physicalAntisymmetricState_density d hd n)]

end QuantumProver.WernerEndpoint

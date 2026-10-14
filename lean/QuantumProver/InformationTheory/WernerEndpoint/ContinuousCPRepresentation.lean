import QuantumProver.InformationTheory.WernerEndpoint.AllDimensionalMoment
import QuantumProver.InformationTheory.ElegantJointMeasurement.ContinuousCPInstruments
import QuantumProver.InformationTheory.ConditionalEntropy.ContinuousLocalInstrument
import Mathlib.MeasureTheory.Integral.Prod

set_option autoImplicit false
set_option maxHeartbeats 1200000

noncomputable section

namespace QuantumProver.WernerEndpoint.ContinuousCPRepresentation

open MeasureTheory Matrix
open QuantumProver.SuperchannelDiscrimination.CPTPKraus
open QuantumProver.ConditionalEntropy
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker

variable {Ω I O R : Type*} [MeasurableSpace Ω]
  [Fintype I] [Fintype O] [DecidableEq I] [DecidableEq O]

abbrev CPMap := Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ
abbrev Hidden (I O : Type*) [Fintype I] [Fintype O] := Fin (Fintype.card (I × O))

def refinedKraus (Φ : Ω → CPMap (I := I) (O := O)) : Ω × Hidden I O → Matrix O I ℂ :=
  fun xq => canonicalKraus (Φ xq.1) ((Fintype.equivFin (I × O)).symm xq.2)

def refinedMeasure (μ : Measure Ω) : Measure (Ω × Hidden I O) := μ.prod Measure.count

theorem refinedKraus_measurable (Φ : Ω → CPMap (I := I) (O := O))
    (hΦ : QuantumProver.ElegantJointMeasurement.ContinuousCPInstruments.CoordinateMeasurable Φ) : Measurable (refinedKraus Φ) := by
  apply measurable_from_prod_countable_left
  intro q
  exact QuantumProver.ElegantJointMeasurement.ContinuousCPInstruments.measurable_canonicalKraus Φ hΦ
    ((Fintype.equivFin (I × O)).symm q)

private theorem refinedGram_measurable (Φ : Ω → CPMap (I := I) (O := O))
    (hΦ : QuantumProver.ElegantJointMeasurement.ContinuousCPInstruments.CoordinateMeasurable Φ) :
    Measurable (fun xq => (refinedKraus Φ xq).conjTranspose * refinedKraus Φ xq) := by
  have hK := refinedKraus_measurable Φ hΦ
  have hc : Continuous (fun K : Matrix O I ℂ => K.conjTranspose * K) := by fun_prop
  exact hc.measurable.comp hK

variable [Nonempty I]

theorem refinedGram_integrable (μ : Measure Ω) [IsFiniteMeasure μ]
    (Φ : Ω → CPMap (I := I) (O := O))
    (hΦ : QuantumProver.ElegantJointMeasurement.ContinuousCPInstruments.CoordinateMeasurable Φ)
    (hCP : ∀ x, CompletelyPositive (Φ x))
    (hTotal : QuantumProver.ElegantJointMeasurement.ContinuousCPInstruments.MatrixTraceComplete μ Φ) :
    Integrable (fun xq => (refinedKraus Φ xq).conjTranspose * refinedKraus Φ xq)
      (refinedMeasure (I := I) (O := O) μ) := by
  have hFamily := QuantumProver.ElegantJointMeasurement.ContinuousCPInstruments.integrable_canonicalKraus_gram_family
    μ Φ hΦ (fun x => completelyPositive_to_EJMCP (hCP x)) hTotal
  apply (hFamily.norm.comp_fst (Measure.count : Measure (Hidden I O))).mono'
    (refinedGram_measurable Φ hΦ).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun xq =>
    norm_le_pi_norm (fun q : I × O =>
      (QuantumProver.ElegantJointMeasurement.ContinuousCPInstruments.canonicalKraus Φ xq.1 q).conjTranspose *
        QuantumProver.ElegantJointMeasurement.ContinuousCPInstruments.canonicalKraus Φ xq.1 q)
      ((Fintype.equivFin (I × O)).symm xq.2)

theorem refinedGram_complete (μ : Measure Ω) [IsFiniteMeasure μ]
    (Φ : Ω → CPMap (I := I) (O := O))
    (hΦ : QuantumProver.ElegantJointMeasurement.ContinuousCPInstruments.CoordinateMeasurable Φ)
    (hCP : ∀ x, CompletelyPositive (Φ x))
    (hTotal : QuantumProver.ElegantJointMeasurement.ContinuousCPInstruments.MatrixTraceComplete μ Φ) :
    (∫ xq, (refinedKraus Φ xq).conjTranspose * refinedKraus Φ xq
      ∂refinedMeasure (I := I) (O := O) μ) = 1 := by
  rw [refinedMeasure, integral_prod _ (refinedGram_integrable μ Φ hΦ hCP hTotal)]
  simp only [integral_count]
  have hSum (x : Ω) : (∑ q : Hidden I O,
      (refinedKraus Φ (x,q)).conjTranspose * refinedKraus Φ (x,q)) =
      QuantumProver.ElegantJointMeasurement.ContinuousCPInstruments.canonicalGram Φ x :=
    (Fintype.equivFin (I × O)).symm.sum_comp (fun q =>
      (QuantumProver.ElegantJointMeasurement.ContinuousCPInstruments.canonicalKraus Φ x q).conjTranspose *
        QuantumProver.ElegantJointMeasurement.ContinuousCPInstruments.canonicalKraus Φ x q)
  simp_rw [hSum]
  exact QuantumProver.ElegantJointMeasurement.ContinuousCPInstruments.integral_canonicalGram_eq_one μ Φ hΦ
    (fun x => completelyPositive_to_EJMCP (hCP x)) hTotal

private def singleKrausMap (K : Matrix O I ℂ) : CPMap (I := I) (O := O) :=
  QuantumProver.ElegantJointMeasurement.CP.krausMap (fun _ : Unit => K)

private theorem singleKrausMap_coordinateMeasurable {X : Type*} [MeasurableSpace X]
    (K : X → Matrix O I ℂ) (hK : Measurable K) :
    QuantumProver.ElegantJointMeasurement.ContinuousCPInstruments.CoordinateMeasurable (fun x => singleKrausMap (K x)) := by
  intro i j o p
  have hi : Measurable (fun x => K x o i) :=
    (measurable_pi_apply i).comp ((measurable_pi_apply o).comp hK)
  have hj : Measurable (fun x => K x p j) :=
    (measurable_pi_apply j).comp ((measurable_pi_apply p).comp hK)
  simpa [singleKrausMap, QuantumProver.ElegantJointMeasurement.CP.krausMap, QuantumProver.ElegantJointMeasurement.CP.kraus_matrix_unit,
    Function.comp_def, Pi.mul_apply] using
    hi.fun_mul (continuous_star.measurable.comp hj)

private def tracePairing (X : Matrix I I ℂ) : Matrix I I ℂ →L[ℂ] ℂ :=
  ({ toFun := fun G => (G * X).trace
     map_add' := by intro A B; simp [Matrix.add_mul, Matrix.trace_add]
     map_smul' := by intro z A; simp [Matrix.trace_smul] } :
    Matrix I I ℂ →ₗ[ℂ] ℂ).toContinuousLinearMap

private theorem refinedSingleMap_traceComplete (μ : Measure Ω) [IsFiniteMeasure μ]
    (Φ : Ω → CPMap (I := I) (O := O))
    (hΦ : QuantumProver.ElegantJointMeasurement.ContinuousCPInstruments.CoordinateMeasurable Φ)
    (hCP : ∀ x, CompletelyPositive (Φ x))
    (hTotal : QuantumProver.ElegantJointMeasurement.ContinuousCPInstruments.MatrixTraceComplete μ Φ) :
    QuantumProver.ElegantJointMeasurement.ContinuousCPInstruments.MatrixTraceComplete (refinedMeasure (I := I) (O := O) μ)
      (fun xq => singleKrausMap (refinedKraus Φ xq)) := by
  intro X
  have hcomm := (tracePairing X).integral_comp_comm (refinedGram_integrable μ Φ hΦ hCP hTotal)
  change (∫ xq, ((refinedKraus Φ xq).conjTranspose * refinedKraus Φ xq * X).trace
    ∂refinedMeasure (I := I) (O := O) μ) =
    ((∫ xq, (refinedKraus Φ xq).conjTranspose * refinedKraus Φ xq
      ∂refinedMeasure (I := I) (O := O) μ) * X).trace at hcomm
  calc
    _ = ∫ xq, ((refinedKraus Φ xq).conjTranspose * refinedKraus Φ xq * X).trace
        ∂refinedMeasure (I := I) (O := O) μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun xq => by
        simpa only [singleKrausMap, Fintype.sum_unique, Matrix.one_mul] using
          QuantumProver.ElegantJointMeasurement.CP.krausMap_trace (fun _ : Unit => refinedKraus Φ xq) X
    _ = _ := hcomm
    _ = X.trace := by rw [refinedGram_complete μ Φ hΦ hCP hTotal, Matrix.one_mul]

section References

variable [Fintype R] [DecidableEq R]

private def referenceChoiReadout (ρ : Matrix (I × R) (I × R) ℂ) :
    Matrix (I × O) (I × O) ℂ →L[ℂ] Matrix (O × R) (O × R) ℂ :=
  ({ toFun := fun C => Matrix.of (fun x y =>
       ∑ i, ∑ j, ρ (i,x.2) (j,y.2) * C (i,x.1) (j,y.1))
     map_add' := by
       intro C D
       ext x y
       change (∑ i, ∑ j, ρ (i,x.2) (j,y.2) * (C + D) (i,x.1) (j,y.1)) =
         (∑ i, ∑ j, ρ (i,x.2) (j,y.2) * C (i,x.1) (j,y.1)) +
           ∑ i, ∑ j, ρ (i,x.2) (j,y.2) * D (i,x.1) (j,y.1)
       simp only [Matrix.add_apply, mul_add, Finset.sum_add_distrib]
     map_smul' := by
       intro z C
       ext x y
       change (∑ i, ∑ j, ρ (i,x.2) (j,y.2) * (z • C) (i,x.1) (j,y.1)) =
         z * ∑ i, ∑ j, ρ (i,x.2) (j,y.2) * C (i,x.1) (j,y.1)
       simp only [Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
       apply Finset.sum_congr rfl
       intro i _
       apply Finset.sum_congr rfl
       intro j _
       ring } : Matrix (I × O) (I × O) ℂ →ₗ[ℂ] Matrix (O × R) (O × R) ℂ).toContinuousLinearMap

omit [DecidableEq O] [Nonempty I] [DecidableEq R] in
private theorem amplify_eq_referenceChoiReadout (Φ : CPMap (I := I) (O := O))
    (ρ : Matrix (I × R) (I × R) ℂ) :
    amplify Φ R ρ = referenceChoiReadout ρ (QuantumProver.ElegantJointMeasurement.CP.choi Φ) := by
  ext ⟨o,r⟩ ⟨p,s⟩
  change Φ (fun i j => ρ (i,r) (j,s)) o p =
    ∑ i, ∑ j, ρ (i,r) (j,s) * Φ (Matrix.single i j 1) o p
  conv_lhs => rw [Matrix.matrix_eq_sum_single (fun i j => ρ (i,r) (j,s))]
  rw [map_sum, Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_sum, Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro j _
  have hSingle : Matrix.single i j (ρ (i,r) (j,s)) =
      ρ (i,r) (j,s) • Matrix.single i j (1 : ℂ) := by simp [Matrix.smul_single]
  rw [hSingle, map_smul]
  rfl

theorem referenceAction_integrable (μ : Measure Ω)
    (Φ : Ω → CPMap (I := I) (O := O))
    (hΦ : QuantumProver.ElegantJointMeasurement.ContinuousCPInstruments.CoordinateMeasurable Φ)
    (hCP : ∀ x, CompletelyPositive (Φ x))
    (hTotal : QuantumProver.ElegantJointMeasurement.ContinuousCPInstruments.MatrixTraceComplete μ Φ)
    (ρ : Matrix (I × R) (I × R) ℂ) : Integrable (fun x => amplify (Φ x) R ρ) μ := by
  have hChoi := QuantumProver.ElegantJointMeasurement.ContinuousCPInstruments.integrable_choi μ Φ hΦ
    (fun x => completelyPositive_to_EJMCP (hCP x)) hTotal
  simpa only [← amplify_eq_referenceChoiReadout] using
    (referenceChoiReadout ρ).integrable_comp hChoi

theorem refinedReferenceBranch_integrable (μ : Measure Ω) [IsFiniteMeasure μ]
    (Φ : Ω → CPMap (I := I) (O := O))
    (hΦ : QuantumProver.ElegantJointMeasurement.ContinuousCPInstruments.CoordinateMeasurable Φ)
    (hCP : ∀ x, CompletelyPositive (Φ x))
    (hTotal : QuantumProver.ElegantJointMeasurement.ContinuousCPInstruments.MatrixTraceComplete μ Φ)
    (ρ : Matrix (I × R) (I × R) ℂ) :
    Integrable (fun xq => (refinedKraus Φ xq ⊗ₖ (1 : Matrix R R ℂ)) * ρ *
      (refinedKraus Φ xq ⊗ₖ (1 : Matrix R R ℂ)).conjTranspose)
      (refinedMeasure (I := I) (O := O) μ) := by
  have hChoi := QuantumProver.ElegantJointMeasurement.ContinuousCPInstruments.integrable_choi
    (refinedMeasure (I := I) (O := O) μ) (fun xq => singleKrausMap (refinedKraus Φ xq))
    (singleKrausMap_coordinateMeasurable _ (refinedKraus_measurable Φ hΦ))
    (fun xq => QuantumProver.ElegantJointMeasurement.CP.krausMap_completelyPositive (fun _ : Unit => refinedKraus Φ xq))
    (refinedSingleMap_traceComplete μ Φ hΦ hCP hTotal)
  have hi := (referenceChoiReadout ρ).integrable_comp hChoi
  simp only [← amplify_eq_referenceChoiReadout, singleKrausMap,
    amplify_krausMap_reconstruct, Fintype.sum_unique] at hi
  exact hi

omit [MeasurableSpace Ω] [Nonempty I] in

theorem referenceAction_eq_refined_sum (Φ : Ω → CPMap (I := I) (O := O))
    (hCP : ∀ x, CompletelyPositive (Φ x)) (x : Ω)
    (ρ : Matrix (I × R) (I × R) ℂ) :
    amplify (Φ x) R ρ = ∑ q : Hidden I O,
      (refinedKraus Φ (x,q) ⊗ₖ (1 : Matrix R R ℂ)) * ρ *
        (refinedKraus Φ (x,q) ⊗ₖ (1 : Matrix R R ℂ)).conjTranspose := by
  rw [canonicalKraus_reconstruct_map (Φ x) (hCP x), amplify_krausMap_reconstruct]
  exact ((Fintype.equivFin (I × O)).symm.sum_comp (fun q =>
    (canonicalKraus (Φ x) q ⊗ₖ (1 : Matrix R R ℂ)) * ρ *
      (canonicalKraus (Φ x) q ⊗ₖ (1 : Matrix R R ℂ)).conjTranspose)).symm

theorem integral_referenceAction_eq_refinement (μ : Measure Ω) [IsFiniteMeasure μ]
    (Φ : Ω → CPMap (I := I) (O := O))
    (hΦ : QuantumProver.ElegantJointMeasurement.ContinuousCPInstruments.CoordinateMeasurable Φ)
    (hCP : ∀ x, CompletelyPositive (Φ x))
    (hTotal : QuantumProver.ElegantJointMeasurement.ContinuousCPInstruments.MatrixTraceComplete μ Φ)
    (ρ : Matrix (I × R) (I × R) ℂ) :
    (∫ x, amplify (Φ x) R ρ ∂μ) =
      ∫ xq, (refinedKraus Φ xq ⊗ₖ (1 : Matrix R R ℂ)) * ρ *
        (refinedKraus Φ xq ⊗ₖ (1 : Matrix R R ℂ)).conjTranspose
          ∂refinedMeasure (I := I) (O := O) μ := by
  rw [refinedMeasure, integral_prod _ (refinedReferenceBranch_integrable μ Φ hΦ hCP hTotal ρ)]
  simp only [integral_count]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => referenceAction_eq_refined_sum Φ hCP x ρ

omit [Nonempty I] in

theorem integral_referenceAction_withContinuation_eq
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (Φ : Ω → CPMap (I := I) (O := O)) (hCP : ∀ x, CompletelyPositive (Φ x))
    (L : Ω → (Matrix (O × R) (O × R) ℂ →L[ℂ] V))
    (ρ : Matrix (I × R) (I × R) ℂ)
    (hMoment : Integrable (fun xq => L xq.1
      ((refinedKraus Φ xq ⊗ₖ (1 : Matrix R R ℂ)) * ρ *
        (refinedKraus Φ xq ⊗ₖ (1 : Matrix R R ℂ)).conjTranspose))
          (refinedMeasure (I := I) (O := O) μ)) :
    (∫ x, L x (amplify (Φ x) R ρ) ∂μ) =
      ∫ xq, L xq.1 ((refinedKraus Φ xq ⊗ₖ (1 : Matrix R R ℂ)) * ρ *
        (refinedKraus Φ xq ⊗ₖ (1 : Matrix R R ℂ)).conjTranspose)
          ∂refinedMeasure (I := I) (O := O) μ := by
  rw [refinedMeasure, integral_prod _ hMoment]
  simp only [integral_count]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    dsimp only
    rw [referenceAction_eq_refined_sum Φ hCP x ρ, map_sum]

end References

section BornAndEntropy

variable [Fintype R] [DecidableEq R]

theorem refinedBornMeasure_isProbability (μ : Measure Ω) [IsFiniteMeasure μ]
    (Φ : Ω → CPMap (I := I) (O := O))
    (hΦ : QuantumProver.ElegantJointMeasurement.ContinuousCPInstruments.CoordinateMeasurable Φ)
    (hCP : ∀ x, CompletelyPositive (Φ x))
    (hTotal : QuantumProver.ElegantJointMeasurement.ContinuousCPInstruments.MatrixTraceComplete μ Φ)
    (ρ : Matrix (I × R) (I × R) ℂ) (hρ : QuantumProver.QuantumEntropy.IsDensity ρ) :
    IsProbabilityMeasure (ContinuousLocalInstrument.bornMeasure
      (refinedMeasure (I := I) (O := O) μ) (refinedKraus Φ) ρ) :=
  ContinuousLocalInstrument.bornMeasure_isProbability _ _
    (refinedGram_complete μ Φ hΦ hCP hTotal) ρ hρ

theorem refinedNormalizedBranch_isDensity (μ : Measure Ω) [IsFiniteMeasure μ]
    (Φ : Ω → CPMap (I := I) (O := O))
    (hΦ : QuantumProver.ElegantJointMeasurement.ContinuousCPInstruments.CoordinateMeasurable Φ)
    (hCP : ∀ x, CompletelyPositive (Φ x))
    (hTotal : QuantumProver.ElegantJointMeasurement.ContinuousCPInstruments.MatrixTraceComplete μ Φ)
    (ρ : Matrix (I × R) (I × R) ℂ) (hρ : QuantumProver.QuantumEntropy.IsDensity ρ)
    (xq : Ω × Hidden I O) :
    QuantumProver.QuantumEntropy.IsDensity (ContinuousLocalInstrument.normalizedBranch
      (refinedMeasure (I := I) (O := O) μ) (refinedKraus Φ) ρ xq) :=
  ContinuousLocalInstrument.normalizedBranch_isDensity _ _
    (refinedKraus_measurable Φ hΦ) (refinedGram_complete μ Φ hΦ hCP hTotal) ρ hρ xq

theorem refinedRetainedMarginal_integral (μ : Measure Ω) [IsFiniteMeasure μ]
    (Φ : Ω → CPMap (I := I) (O := O))
    (hΦ : QuantumProver.ElegantJointMeasurement.ContinuousCPInstruments.CoordinateMeasurable Φ)
    (hCP : ∀ x, CompletelyPositive (Φ x))
    (hTotal : QuantumProver.ElegantJointMeasurement.ContinuousCPInstruments.MatrixTraceComplete μ Φ)
    (ρ : Matrix (I × R) (I × R) ℂ) (hρ : QuantumProver.QuantumEntropy.IsDensity ρ) :
    (∫ xq, ContinuousLocalInstrument.normalizedUntouchedMarginal
      (refinedMeasure (I := I) (O := O) μ) (refinedKraus Φ) ρ xq
      ∂ContinuousLocalInstrument.bornMeasure
        (refinedMeasure (I := I) (O := O) μ) (refinedKraus Φ) ρ) =
      QuantumProver.QuantumEntropy.partialTrace_left ρ :=
  ContinuousLocalInstrument.integral_normalizedUntouchedMarginal _ _
    (refinedKraus_measurable Φ hΦ) (refinedGram_complete μ Φ hΦ hCP hTotal) ρ hρ

theorem refined_average_pureEntropy_le (μ : Measure Ω) [IsFiniteMeasure μ]
    (Φ : Ω → CPMap (I := I) (O := O))
    (hΦ : QuantumProver.ElegantJointMeasurement.ContinuousCPInstruments.CoordinateMeasurable Φ)
    (hCP : ∀ x, CompletelyPositive (Φ x))
    (hTotal : QuantumProver.ElegantJointMeasurement.ContinuousCPInstruments.MatrixTraceComplete μ Φ)
    (ψ : I × R → ℂ) (hψ : QuantumProver.WernerEndpoint.vectorNormSq ψ = 1) :
    (∫ xq, QuantumProver.QuantumEntropy.entropyBits (QuantumProver.QuantumEntropy.partialTrace_left
      (ContinuousLocalInstrument.pureDensity
        (ContinuousLocalInstrument.normalizedPureBranchVector (refinedKraus Φ) ψ xq)))
      ∂ContinuousLocalInstrument.bornMeasure (refinedMeasure (I := I) (O := O) μ)
        (refinedKraus Φ) (ContinuousLocalInstrument.pureDensity ψ)) ≤
      QuantumProver.QuantumEntropy.entropyBits
        (QuantumProver.QuantumEntropy.partialTrace_left (ContinuousLocalInstrument.pureDensity ψ)) :=
  ContinuousLocalInstrument.average_pure_retainedEntropy_le _ _
    (refinedKraus_measurable Φ hΦ) (refinedGram_complete μ Φ hΦ hCP hTotal) ψ hψ

end BornAndEntropy
end QuantumProver.WernerEndpoint.ContinuousCPRepresentation

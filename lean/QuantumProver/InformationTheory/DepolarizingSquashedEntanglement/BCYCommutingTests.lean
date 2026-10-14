import QuantumProver.InformationTheory.DepolarizingSquashedEntanglement.BCYPinching
import QuantumProver.InformationTheory.DepolarizingSquashedEntanglement.BCYCompositeTesting
import QuantumProver.InformationTheory.DepolarizingSquashedEntanglement.BCYThreeRegions

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace QuantumProver.DepolarizingSquashedEntanglement.BCYCommutingTests

open BCYRelativeEntropy BCYPinching BCYCompositeTesting
open QuantumProver.Equipartition.FiniteModel
open QuantumProver.Equipartition.FiniteModel.Testing
open QuantumProver.Equipartition.FiniteModel.PinchingUmegaki

variable {I : Type*} [Fintype I] [DecidableEq I]

abbrev JointIndex (S : Density I) (hS : S.matrix.PosDef) := SpectralLabels hS.1 × I

def nullEigenvalue (ρ S : Density I) (hS : S.matrix.PosDef) (z : JointIndex S hS) : ℝ :=
  (spectralPinching_posSemidef hS.1 ρ.positive).1.eigenvalues z.2

def referenceEigenvalue (S : Density I) (hS : S.matrix.PosDef)
    (z : JointIndex S hS) : ℝ := (z.1 : ℝ)

def overlapWeight (ρ S : Density I) (hS : S.matrix.PosDef) (z : JointIndex S hS) : ℝ :=
  compressedSpectralOverlap ρ.positive hS.posSemidef z

abbrev physicalPOVM (ρ S : Density I) (hS : S.matrix.PosDef) :=
  compressedSpectralPOVM ρ.positive hS.posSemidef

def likelihoodSet (ρ S : Density I) (hS : S.matrix.PosDef) (t : ℝ) :
    Finset (Fin (Fintype.card (JointIndex S hS))) := by
  classical
  exact Finset.univ.filter (fun i =>
    Real.exp t * referenceEigenvalue S hS ((Fintype.equivFin (JointIndex S hS)).symm i) ≤
      nullEigenvalue ρ S hS ((Fintype.equivFin (JointIndex S hS)).symm i))

def likelihoodTest (ρ S : Density I) (hS : S.matrix.PosDef) (t : ℝ) : BinaryEffect I where
  matrix := ∑ i ∈ likelihoodSet ρ S hS t, (physicalPOVM ρ S hS).outcome i
  positive := (povm_subset_isEffect (physicalPOVM ρ S hS) (likelihoodSet ρ S hS t)).1
  complement_positive :=
    (povm_subset_isEffect (physicalPOVM ρ S hS) (likelihoodSet ρ S hS t)).2

theorem overlapWeight_nonneg (ρ S : Density I) (hS : S.matrix.PosDef)
    (z : JointIndex S hS) : 0 ≤ overlapWeight ρ S hS z :=
  compressedSpectralOverlap_nonneg ρ.positive hS.posSemidef z

theorem nullEigenvalue_nonneg (ρ S : Density I) (hS : S.matrix.PosDef)
    (z : JointIndex S hS) : 0 ≤ nullEigenvalue ρ S hS z :=
  (spectralPinching_posSemidef hS.1 ρ.positive).eigenvalues_nonneg z.2

theorem nullEigenvalue_le_one (ρ S : Density I) (hS : S.matrix.PosDef)
    (z : JointIndex S hS) : nullEigenvalue ρ S hS z ≤ 1 := by
  classical
  let hR := spectralPinching_posSemidef hS.1 ρ.positive
  have hs : ∑ j, hR.1.eigenvalues j = 1 := by
    have ht := (pinchedDensity ρ hS.1).trace_one
    rw [pinchedDensity_matrix, hR.1.trace_eq_sum_eigenvalues] at ht
    simpa using congrArg Complex.re ht
  change hR.1.eigenvalues z.2 ≤ 1
  rw [← hs]
  exact Finset.single_le_sum (fun j _ => hR.eigenvalues_nonneg j) (Finset.mem_univ z.2)

theorem referenceEigenvalue_nonneg (S : Density I) (hS : S.matrix.PosDef)
    (z : JointIndex S hS) : 0 ≤ referenceEigenvalue S hS z :=
  spectralLabel_value_nonneg hS.posSemidef z.1

theorem overlap_null_mass (ρ S : Density I) (hS : S.matrix.PosDef) :
    ∑ z : JointIndex S hS, overlapWeight ρ S hS z * nullEigenvalue ρ S hS z = 1 := by
  classical
  calc
    _ = ∑ z : JointIndex S hS,
        measurementMass (physicalPOVM ρ S hS) ρ.matrix
          ((Fintype.equivFin (JointIndex S hS)) z) := by
      apply Finset.sum_congr rfl
      intro z _
      rw [compressedSpectralPOVM_null_mass]
      exact mul_comm _ _
    _ = ∑ i, measurementMass (physicalPOVM ρ S hS) ρ.matrix i :=
      Equiv.sum_comp (Fintype.equivFin (JointIndex S hS)) _
    _ = 1 := measurementMass_sum _ ⟨ρ.positive, ρ.trace_one⟩

theorem likelihoodTest_acceptance_eq_sum (η ρ S : Density I)
    (hS : S.matrix.PosDef) (t : ℝ) :
    acceptance η (likelihoodTest ρ S hS t) =
      ∑ z : JointIndex S hS,
        if Real.exp t * referenceEigenvalue S hS z ≤ nullEigenvalue ρ S hS z then
          measurementMass (physicalPOVM ρ S hS) η.matrix
            ((Fintype.equivFin (JointIndex S hS)) z) else 0 := by
  classical
  change tracePair η.matrix
    (∑ i ∈ likelihoodSet ρ S hS t, (physicalPOVM ρ S hS).outcome i) = _
  rw [tracePair_sum_right, likelihoodSet, Finset.sum_filter]
  simpa only [Equiv.symm_apply_apply, measurementMass] using
    (Equiv.sum_comp (Fintype.equivFin (JointIndex S hS)) (fun i =>
      if Real.exp t * referenceEigenvalue S hS ((Fintype.equivFin (JointIndex S hS)).symm i) ≤
          nullEigenvalue ρ S hS ((Fintype.equivFin (JointIndex S hS)).symm i) then
        measurementMass (physicalPOVM ρ S hS) η.matrix i else 0)).symm

theorem likelihoodTest_acceptance_physical (ρ S : Density I)
    (hS : S.matrix.PosDef) (n a : ℝ) :
    acceptance ρ (likelihoodTest ρ S hS (n * a)) =
      BCYThreeRegions.upperMass n (overlapWeight ρ S hS)
        (nullEigenvalue ρ S hS) (referenceEigenvalue S hS) a := by
  classical
  rw [likelihoodTest_acceptance_eq_sum, BCYThreeRegions.upperMass]
  apply Finset.sum_congr rfl
  intro z _
  split_ifs
  · rw [compressedSpectralPOVM_null_mass]
    exact mul_comm _ _
  · rfl

theorem physicalPOVM_mass_pinched (ρ S : Density I) (hS : S.matrix.PosDef)
    (z : JointIndex S hS) :
    measurementMass (physicalPOVM ρ S hS) (pinchedDensity ρ hS.1).matrix
        ((Fintype.equivFin (JointIndex S hS)) z) =
      measurementMass (physicalPOVM ρ S hS) ρ.matrix
        ((Fintype.equivFin (JointIndex S hS)) z) := by
  classical
  rw [physicalPOVM, compressedSpectralPOVM, compressedProjectionPOVM_mass,
    compressedProjectionPOVM_mass]
  exact (tracePair_compressionOutcome_eq_pinched (spectralPinchingProjection hS.1)
    (spectralPinchingProjection_mul hS.1) _ ρ.matrix z).symm

theorem likelihoodTest_acceptance_pinched_eq_physical (ρ S : Density I)
    (hS : S.matrix.PosDef) (t : ℝ) :
    acceptance (pinchedDensity ρ hS.1) (likelihoodTest ρ S hS t) =
      acceptance ρ (likelihoodTest ρ S hS t) := by
  rw [likelihoodTest_acceptance_eq_sum, likelihoodTest_acceptance_eq_sum]
  simp_rw [physicalPOVM_mass_pinched]

theorem likelihoodTest_acceptance_pinched (ρ S : Density I)
    (hS : S.matrix.PosDef) (n a : ℝ) :
    acceptance (pinchedDensity ρ hS.1) (likelihoodTest ρ S hS (n * a)) =
      BCYThreeRegions.upperMass n (overlapWeight ρ S hS)
        (nullEigenvalue ρ S hS) (referenceEigenvalue S hS) a := by
  rw [likelihoodTest_acceptance_pinched_eq_physical, likelihoodTest_acceptance_physical]

theorem likelihoodTest_reference_acceptance_eq_sum (ρ S : Density I)
    (hS : S.matrix.PosDef) (t : ℝ) :
    acceptance S (likelihoodTest ρ S hS t) =
      ∑ z : JointIndex S hS,
        if Real.exp t * referenceEigenvalue S hS z ≤ nullEigenvalue ρ S hS z then
          overlapWeight ρ S hS z * referenceEigenvalue S hS z else 0 := by
  classical
  rw [likelihoodTest_acceptance_eq_sum]
  apply Finset.sum_congr rfl
  intro z _
  split_ifs
  · rw [compressedSpectralPOVM_alternative_mass]
    exact mul_comm _ _
  · rfl

theorem likelihoodTest_beta_le_exp (ρ S : Density I)
    (hS : S.matrix.PosDef) (t : ℝ) :
    acceptance S (likelihoodTest ρ S hS t) ≤ Real.exp (-t) := by
  classical
  rw [likelihoodTest_reference_acceptance_eq_sum]
  have he : Real.exp (-t) * Real.exp t = 1 := by rw [← Real.exp_add]; simp
  calc
    _ ≤ ∑ z : JointIndex S hS,
        Real.exp (-t) * (if Real.exp t * referenceEigenvalue S hS z ≤
          nullEigenvalue ρ S hS z then overlapWeight ρ S hS z * nullEigenvalue ρ S hS z else 0) := by
      apply Finset.sum_le_sum
      intro z _
      split_ifs with hz
      · have hh := mul_le_mul_of_nonneg_left hz (Real.exp_pos (-t)).le
        rw [← mul_assoc, he, one_mul] at hh
        have hw := mul_le_mul_of_nonneg_left hh (overlapWeight_nonneg ρ S hS z)
        calc
          _ ≤ overlapWeight ρ S hS z * (Real.exp (-t) * nullEigenvalue ρ S hS z) := hw
          _ = Real.exp (-t) * (overlapWeight ρ S hS z * nullEigenvalue ρ S hS z) := by ring
      · simp
    _ = Real.exp (-t) * BCYThreeRegions.upperMass 1
        (overlapWeight ρ S hS) (nullEigenvalue ρ S hS) (referenceEigenvalue S hS) t := by
      rw [← Finset.mul_sum]
      simp only [BCYThreeRegions.upperMass, one_mul]
    _ ≤ Real.exp (-t) := by
      have hm := BCYThreeRegions.upperMass_le_one 1
        (overlapWeight ρ S hS) (nullEigenvalue ρ S hS) (referenceEigenvalue S hS) t
        (overlapWeight_nonneg ρ S hS) (nullEigenvalue_nonneg ρ S hS) (overlap_null_mass ρ S hS)
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hm (Real.exp_pos (-t)).le

theorem referenceEigenvalue_mem_spectrum (S : Density I) (hS : S.matrix.PosDef)
    (z : JointIndex S hS) : referenceEigenvalue S hS z ∈ spectrum ℝ S.matrix := by
  classical
  obtain ⟨j, _, hj⟩ := Finset.mem_image.mp z.1.property
  rw [referenceEigenvalue, ← hj]
  exact hS.1.eigenvalues_mem_spectrum_real j

theorem referenceEigenvalue_lower (S : Density I) (hS : S.matrix.PosDef)
    (c : ℝ) (hfloor : c • (1 : QMatrix I) ≤ S.matrix) (z : JointIndex S hS) :
    c ≤ referenceEigenvalue S hS z := by
  exact (algebraMap_le_iff_le_spectrum (R := ℝ) (a := S.matrix) hS.1).mp
    (by simpa only [Algebra.algebraMap_eq_smul_one] using hfloor) _
    (referenceEigenvalue_mem_spectrum S hS z)

theorem pinched_finiteRelativeEntropyNats_eq_weighted_sum (ρ S : Density I)
    (hS : S.matrix.PosDef) :
    finiteRelativeEntropyNats (pinchedDensity ρ hS.1).matrix S.matrix =
      ∑ z : JointIndex S hS, overlapWeight ρ S hS z * nullEigenvalue ρ S hS z *
        (Real.log (nullEigenvalue ρ S hS z) - Real.log (referenceEigenvalue S hS z)) := by
  have hh := congrArg (fun x : ℝ => x * Real.log 2)
    (umegakiReal_spectralPinching_eq_sum ρ.positive hS.posSemidef)
  rw [umegakiReal_mul_log_two, Finset.sum_mul] at hh
  change finiteRelativeEntropyNats (pinchedDensity ρ hS.1).matrix S.matrix = _ at hh
  rw [hh]
  apply Finset.sum_congr rfl
  intro z _
  simp only [nullEigenvalue, referenceEigenvalue, overlapWeight, logTwo]
  field_simp [(Real.log_pos (show (1 : ℝ) < 2 by norm_num)).ne'] <;> ring

theorem pinched_finiteRelativeEntropyNats_div_le_three_regions (ρ S : Density I)
    (hS : S.matrix.PosDef) (n : ℕ) (hn : 1 ≤ n) (kappa lower upper : ℝ)
    (horder : lower ≤ upper)
    (hfloor : Real.exp (-2 * (n : ℝ) * kappa) • (1 : QMatrix I) ≤ S.matrix) :
    finiteRelativeEntropyNats (pinchedDensity ρ hS.1).matrix S.matrix / (n : ℝ) ≤
      lower + (upper - lower) *
        acceptance (pinchedDensity ρ hS.1) (likelihoodTest ρ S hS ((n : ℝ) * lower)) +
      (2 * kappa - upper) *
        acceptance (pinchedDensity ρ hS.1) (likelihoodTest ρ S hS ((n : ℝ) * upper)) := by
  rw [pinched_finiteRelativeEntropyNats_eq_weighted_sum,
    likelihoodTest_acceptance_pinched, likelihoodTest_acceptance_pinched]
  exact BCYThreeRegions.weighted_log_div_le_three_regions (n : ℝ) kappa lower upper
    (overlapWeight ρ S hS) (nullEigenvalue ρ S hS) (referenceEigenvalue S hS)
    (by exact_mod_cast hn) horder (overlapWeight_nonneg ρ S hS)
    (nullEigenvalue_nonneg ρ S hS) (nullEigenvalue_le_one ρ S hS)
    (referenceEigenvalue_lower S hS _ hfloor) (overlap_null_mass ρ S hS)

end QuantumProver.DepolarizingSquashedEntanglement.BCYCommutingTests

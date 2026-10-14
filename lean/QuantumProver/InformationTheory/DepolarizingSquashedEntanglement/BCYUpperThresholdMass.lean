import QuantumProver.InformationTheory.DepolarizingSquashedEntanglement.BCYBlockStrongConverse
import QuantumProver.InformationTheory.DepolarizingSquashedEntanglement.BCYTestingPrimitives
import QuantumProver.InformationTheory.DepolarizingSquashedEntanglement.BCYCommutingTests

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

open Matrix Filter Set
open scoped Topology BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace QuantumProver.DepolarizingSquashedEntanglement.BCYUpperThresholdMass

open BCYRelativeEntropy BCYCompositeTesting BCYTestingPrimitives
open BCYPinching BCYCommutingTests BCYBlockStrongConverse

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

theorem tendsto_log_const_div (C : ℝ) :
    Tendsto (fun n : ℕ => Real.log C / (n : ℝ)) atTop (𝓝 0) :=
  tendsto_const_div_atTop_nhds_zero_nat (Real.log C)

theorem eventually_const_mul_exp_le {C a slack : ℝ} (hC : 0 < C)
    (hs : 0 < slack) :
    ∀ᶠ n : ℕ in atTop,
      C * Real.exp (-(n : ℝ) * (a + slack)) ≤
        Real.exp (-(n : ℝ) * (a + slack / 2)) := by
  have hSmall : ∀ᶠ n : ℕ in atTop, Real.log C / (n : ℝ) < slack / 2 :=
    (tendsto_log_const_div C).eventually (Iio_mem_nhds (half_pos hs))
  filter_upwards [hSmall, eventually_ge_atTop 1] with n hn hPos
  have hnR : 0 < (n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hPos)
  have hCost : Real.log C ≤ (n : ℝ) * (slack / 2) := by
    have h := (div_lt_iff₀ hnR).mp hn
    nlinarith
  calc
    C * Real.exp (-(n : ℝ) * (a + slack)) =
        Real.exp (Real.log C + -(n : ℝ) * (a + slack)) := by
      rw [Real.exp_add, Real.exp_log hC]
    _ ≤ Real.exp (-(n : ℝ) * (a + slack / 2)) := by
      apply Real.exp_le_exp.mpr
      nlinarith

theorem likelihoodTest_padded_beta_le (rho : Density (A × B)) (m n : ℕ)
    (sigma : SeparableDensity (CopyIndex A m) (CopyIndex B m))
    (omega : SeparableDensity A B)
    (S : Density (CopyIndex A n × CopyIndex B n)) (hS : S.matrix.PosDef)
    {C : ℝ} (hC : 0 ≤ C)
    (hOrder : (paddedBlockComparison m sigma omega n).val.matrix ≤ C • S.matrix)
    (a slack : ℝ) :
    acceptance (paddedBlockComparison m sigma omega n).val
      (likelihoodTest (tensorCopies rho n) S hS ((n : ℝ) * (a + slack))) ≤
        C * Real.exp (-(n : ℝ) * (a + slack)) := by
  calc
    _ ≤ C * acceptance S
        (likelihoodTest (tensorCopies rho n) S hS ((n : ℝ) * (a + slack))) :=
      acceptance_le_mul_of_alternative_le _ _ _ hOrder
    _ ≤ C * Real.exp (-(n : ℝ) * (a + slack)) := by
      apply mul_le_mul_of_nonneg_left _ hC
      simpa only [neg_mul] using
        likelihoodTest_beta_le_exp (tensorCopies rho n) S hS ((n : ℝ) * (a + slack))

theorem eventually_likelihoodTest_padded_beta_le (rho : Density (A × B)) (m : ℕ)
    (sigma : SeparableDensity (CopyIndex A m) (CopyIndex B m))
    (omega : SeparableDensity A B)
    (S : (n : ℕ) → Density (CopyIndex A n × CopyIndex B n))
    (hS : ∀ n, (S n).matrix.PosDef) {C : ℝ} (hC : 0 < C)
    (hOrder : ∀ n,
      (paddedBlockComparison m sigma omega n).val.matrix ≤ C • (S n).matrix)
    (a slack : ℝ) (hs : 0 < slack) :
    ∀ᶠ n : ℕ in atTop,
      acceptance (paddedBlockComparison m sigma omega n).val
        (likelihoodTest (tensorCopies rho n) (S n) (hS n) ((n : ℝ) * (a + slack))) ≤
          Real.exp (-(n : ℝ) * (a + slack / 2)) := by
  filter_upwards [eventually_const_mul_exp_le (a := a) hC hs] with n hn
  exact (likelihoodTest_padded_beta_le rho m n sigma omega (S n) (hS n)
    hC.le (hOrder n) a slack).trans hn

theorem exists_upper_threshold_acceptance_envelope (rho : Density (A × B))
    (m : ℕ) (hm : 0 < m)
    (sigma : SeparableDensity (CopyIndex A m) (CopyIndex B m))
    (omega : SeparableDensity A B)
    (hSigma : sigma.val.matrix.PosDef) (hOmega : omega.val.matrix.PosDef)
    (S : (n : ℕ) → Density (CopyIndex A n × CopyIndex B n))
    (hS : ∀ n, (S n).matrix.PosDef) (C : ℝ) (hC : 0 < C)
    (hOrder : ∀ n,
      (paddedBlockComparison m sigma omega n).val.matrix ≤ C • (S n).matrix)
    (a : ℝ)
    (hRate : finiteRelativeEntropyNats (tensorCopies rho m).matrix sigma.val.matrix /
      (m : ℝ) < a) (slack : ℝ) (hs : 0 < slack) :
    ∃ eta : ℕ → ℝ, (∀ n, 0 ≤ eta n) ∧ Tendsto eta atTop (𝓝 0) ∧
      ∀ᶠ n : ℕ in atTop,
        acceptance (tensorCopies rho n)
          (likelihoodTest (tensorCopies rho n) (S n) (hS n) ((n : ℝ) * (a + slack))) ≤
            eta n := by
  have hRatePetz : QuantumProver.SuperchannelDiscrimination.PetzMoments.relativeEntropyNats
      (tensorCopies rho m).matrix sigma.val.matrix / (m : ℝ) < a + slack / 2 := by
    change finiteRelativeEntropyNats (tensorCopies rho m).matrix sigma.val.matrix /
      (m : ℝ) < a + slack / 2
    exact hRate.trans (lt_add_of_pos_right a (half_pos hs))
  obtain ⟨eta, hEta, hLim, hBound⟩ := exists_uniform_block_acceptance_envelope
    rho m hm sigma omega hSigma hOmega hRatePetz
  refine ⟨eta, hEta, hLim, ?_⟩
  filter_upwards [hBound,
    eventually_likelihoodTest_padded_beta_le rho m sigma omega S hS hC hOrder a slack hs]
    with n hn hBeta
  exact hn (likelihoodTest (tensorCopies rho n) (S n) (hS n)
    ((n : ℝ) * (a + slack))).matrix
    (likelihoodTest (tensorCopies rho n) (S n) (hS n) ((n : ℝ) * (a + slack))).represented hBeta

theorem upper_threshold_mass_tendsto_zero (rho : Density (A × B))
    (m : ℕ) (hm : 0 < m)
    (sigma : SeparableDensity (CopyIndex A m) (CopyIndex B m))
    (omega : SeparableDensity A B)
    (hSigma : sigma.val.matrix.PosDef) (hOmega : omega.val.matrix.PosDef)
    (S : (n : ℕ) → Density (CopyIndex A n × CopyIndex B n))
    (hS : ∀ n, (S n).matrix.PosDef) (C : ℝ) (hC : 0 < C)
    (hOrder : ∀ n,
      (paddedBlockComparison m sigma omega n).val.matrix ≤ C • (S n).matrix)
    (a : ℝ)
    (hRate : finiteRelativeEntropyNats (tensorCopies rho m).matrix sigma.val.matrix /
      (m : ℝ) < a) (slack : ℝ) (hs : 0 < slack) :
    Tendsto (fun n : ℕ => acceptance (tensorCopies rho n)
      (likelihoodTest (tensorCopies rho n) (S n) (hS n) ((n : ℝ) * (a + slack))))
      atTop (𝓝 0) := by
  obtain ⟨eta, hEta, hLim, hBound⟩ := exists_upper_threshold_acceptance_envelope
    rho m hm sigma omega hSigma hOmega S hS C hC hOrder a hRate slack hs
  exact squeeze_zero' (Eventually.of_forall (fun n =>
    (acceptance_bounds (tensorCopies rho n)
      (likelihoodTest (tensorCopies rho n) (S n) (hS n) ((n : ℝ) * (a + slack)))).1))
    hBound hLim

theorem pinched_upper_threshold_mass_tendsto_zero (rho : Density (A × B))
    (m : ℕ) (hm : 0 < m)
    (sigma : SeparableDensity (CopyIndex A m) (CopyIndex B m))
    (omega : SeparableDensity A B)
    (hSigma : sigma.val.matrix.PosDef) (hOmega : omega.val.matrix.PosDef)
    (S : (n : ℕ) → Density (CopyIndex A n × CopyIndex B n))
    (hS : ∀ n, (S n).matrix.PosDef) (C : ℝ) (hC : 0 < C)
    (hOrder : ∀ n,
      (paddedBlockComparison m sigma omega n).val.matrix ≤ C • (S n).matrix)
    (a : ℝ)
    (hRate : finiteRelativeEntropyNats (tensorCopies rho m).matrix sigma.val.matrix /
      (m : ℝ) < a) (slack : ℝ) (hs : 0 < slack) :
    Tendsto (fun n : ℕ =>
      acceptance (pinchedDensity (tensorCopies rho n) (hS n).1)
        (likelihoodTest (tensorCopies rho n) (S n) (hS n) ((n : ℝ) * (a + slack))))
      atTop (𝓝 0) := by
  simpa only [likelihoodTest_acceptance_pinched_eq_physical] using
    upper_threshold_mass_tendsto_zero rho m hm sigma omega hSigma hOmega S hS C hC
      hOrder a hRate slack hs

theorem upper_spectral_mass_tendsto_zero (rho : Density (A × B))
    (m : ℕ) (hm : 0 < m)
    (sigma : SeparableDensity (CopyIndex A m) (CopyIndex B m))
    (omega : SeparableDensity A B)
    (hSigma : sigma.val.matrix.PosDef) (hOmega : omega.val.matrix.PosDef)
    (S : (n : ℕ) → Density (CopyIndex A n × CopyIndex B n))
    (hS : ∀ n, (S n).matrix.PosDef) (C : ℝ) (hC : 0 < C)
    (hOrder : ∀ n,
      (paddedBlockComparison m sigma omega n).val.matrix ≤ C • (S n).matrix)
    (a : ℝ)
    (hRate : finiteRelativeEntropyNats (tensorCopies rho m).matrix sigma.val.matrix /
      (m : ℝ) < a) (slack : ℝ) (hs : 0 < slack) :
    Tendsto (fun n : ℕ => BCYThreeRegions.upperMass (n : ℝ)
      (overlapWeight (tensorCopies rho n) (S n) (hS n))
      (nullEigenvalue (tensorCopies rho n) (S n) (hS n))
      (referenceEigenvalue (S n) (hS n)) (a + slack)) atTop (𝓝 0) := by
  simpa only [likelihoodTest_acceptance_physical] using
    upper_threshold_mass_tendsto_zero rho m hm sigma omega hSigma hOmega S hS C hC
      hOrder a hRate slack hs

end QuantumProver.DepolarizingSquashedEntanglement.BCYUpperThresholdMass

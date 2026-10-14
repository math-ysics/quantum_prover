import QuantumProver.InformationTheory.WernerEndpoint.ContinuousStateProtocol
import QuantumProver.InformationTheory.WernerEndpoint.FiniteHeterogeneousProtocol

set_option autoImplicit false
set_option maxHeartbeats 1200000

noncomputable section

namespace QuantumProver.WernerEndpoint.VariableFiniteChildReplacement

open OperationalEndpointCost MatrixContinuousStateProtocol
open scoped BigOperators ComplexOrder MatrixOrder Matrix Kronecker
  Matrix.Norms.L2Operator

theorem exists_finite_child_replacement {a b c d h : ℕ}
    (p q : Fin h → ℕ) (D : ∀ i, Channel (p i) (q i) a b)
    (Phi : ∀ i, Channel c d (p i) (q i))
    (hChild : ∀ i (eta : ℝ), 0 < eta →
      ∃ T : FiniteLocalProtocol c d (p i) (q i), ‖finiteChannel T - Phi i‖ < eta)
    (epsilon : ℝ) (hEpsilon : 0 < epsilon) :
    ∃ T : ∀ i, FiniteLocalProtocol c d (p i) (q i),
      ‖(∑ i, (finiteChannel (T i)).comp (D i)) -
        (∑ i, (Phi i).comp (D i))‖ < epsilon := by
  classical
  let C : ℝ := ∑ i, ‖D i‖
  have hC : 0 ≤ C := Finset.sum_nonneg (fun i _ => norm_nonneg (D i))
  let eta : ℝ := epsilon / (C + 1)
  have hDen : 0 < C + 1 := by linarith
  have hEta : 0 < eta := div_pos hEpsilon hDen
  choose T hT using fun i : Fin h => hChild i eta hEta
  refine ⟨T, ?_⟩
  have hTerm (i : Fin h) :
      ‖(finiteChannel (T i) - Phi i).comp (D i)‖ ≤ eta * ‖D i‖ := by
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul_of_nonneg_right (le_of_lt (hT i)) (norm_nonneg _))
  have hDifference : (∑ i, (finiteChannel (T i)).comp (D i)) -
      (∑ i, (Phi i).comp (D i)) =
      ∑ i, (finiteChannel (T i) - Phi i).comp (D i) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    exact (ContinuousLinearMap.sub_comp _ _ _).symm
  rw [hDifference]
  calc
    ‖∑ i, (finiteChannel (T i) - Phi i).comp (D i)‖ ≤
        ∑ i, ‖(finiteChannel (T i) - Phi i).comp (D i)‖ := norm_sum_le _ _
    _ ≤ ∑ i, eta * ‖D i‖ := Finset.sum_le_sum (fun i _ => hTerm i)
    _ = eta * C := by rw [← Finset.mul_sum]
    _ < eta * (C + 1) := mul_lt_mul_of_pos_left (by linarith) hEta
    _ = epsilon := by
      dsimp only [eta]
      exact div_mul_cancel₀ epsilon (ne_of_gt hDen)

theorem aliceNode_channel {h a b c d : ℕ} (hc : 0 < c) (hd : 0 < d)
    (p : Fin h → ℕ) (K : ∀ i, Matrix (Fin (p i)) (Fin a) ℂ)
    (hK : ∑ i, (K i).conjTranspose * K i = 1)
    (next : ∀ i, FiniteLocalProtocol c d (p i) b) :
    finiteChannel (FiniteHeterogeneousProtocol.aliceNode hc hd p K hK next) =
      ∑ i, (finiteChannel (next i)).comp (LocalChannelMoments.leftSandwichCLM (K i)) := by
  ext rho : 1
  simpa only [finiteChannel_apply, sum_apply, ContinuousLinearMap.comp_apply,
    LocalChannelMoments.leftSandwichCLM_apply] using
    FiniteHeterogeneousProtocol.aliceNode_apply hc hd p K hK next rho

theorem bobNode_channel {h a b c d : ℕ} (hc : 0 < c) (hd : 0 < d)
    (p : Fin h → ℕ) (K : ∀ i, Matrix (Fin (p i)) (Fin b) ℂ)
    (hK : ∑ i, (K i).conjTranspose * K i = 1)
    (next : ∀ i, FiniteLocalProtocol c d a (p i)) :
    finiteChannel (FiniteHeterogeneousProtocol.bobNode hc hd p K hK next) =
      ∑ i, (finiteChannel (next i)).comp (LocalChannelMoments.rightSandwichCLM (K i)) := by
  ext rho : 1
  simpa only [finiteChannel_apply, sum_apply, ContinuousLinearMap.comp_apply,
    LocalChannelMoments.rightSandwichCLM_apply] using
    FiniteHeterogeneousProtocol.bobNode_apply hc hd p K hK next rho

theorem approximate_alice_with_finite_children {h a b c d : ℕ}
    (hc : 0 < c) (hd : 0 < d) (p : Fin h → ℕ)
    (K : ∀ i, Matrix (Fin (p i)) (Fin a) ℂ)
    (hK : ∑ i, (K i).conjTranspose * K i = 1)
    (Phi : ∀ i, Channel c d (p i) b)
    (hChild : ∀ i (eta : ℝ), 0 < eta →
      ∃ T : FiniteLocalProtocol c d (p i) b, ‖finiteChannel T - Phi i‖ < eta)
    (epsilon : ℝ) (hEpsilon : 0 < epsilon) :
    ∃ U : FiniteLocalProtocol c d a b,
      ‖finiteChannel U -
        (∑ i, (Phi i).comp (LocalChannelMoments.leftSandwichCLM (K i)))‖ < epsilon := by
  obtain ⟨next, hNext⟩ := exists_finite_child_replacement p (fun _ => b)
    (fun i => LocalChannelMoments.leftSandwichCLM (K i)) Phi hChild epsilon hEpsilon
  refine ⟨FiniteHeterogeneousProtocol.aliceNode hc hd p K hK next, ?_⟩
  rw [aliceNode_channel]
  exact hNext

theorem approximate_bob_with_finite_children {h a b c d : ℕ}
    (hc : 0 < c) (hd : 0 < d) (p : Fin h → ℕ)
    (K : ∀ i, Matrix (Fin (p i)) (Fin b) ℂ)
    (hK : ∑ i, (K i).conjTranspose * K i = 1)
    (Phi : ∀ i, Channel c d a (p i))
    (hChild : ∀ i (eta : ℝ), 0 < eta →
      ∃ T : FiniteLocalProtocol c d a (p i), ‖finiteChannel T - Phi i‖ < eta)
    (epsilon : ℝ) (hEpsilon : 0 < epsilon) :
    ∃ U : FiniteLocalProtocol c d a b,
      ‖finiteChannel U -
        (∑ i, (Phi i).comp (LocalChannelMoments.rightSandwichCLM (K i)))‖ < epsilon := by
  obtain ⟨next, hNext⟩ := exists_finite_child_replacement (fun _ => a) p
    (fun i => LocalChannelMoments.rightSandwichCLM (K i)) Phi hChild epsilon hEpsilon
  refine ⟨FiniteHeterogeneousProtocol.bobNode hc hd p K hK next, ?_⟩
  rw [bobNode_channel]
  exact hNext

end QuantumProver.WernerEndpoint.VariableFiniteChildReplacement

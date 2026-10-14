import QuantumProver.InformationTheory.AmplitudeDamping.QuantumCapacity.ParallelLanes

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open scoped BigOperators ComplexConjugate ComplexOrder Matrix Kronecker

namespace QuantumProver.AmplitudeDamping.FiniteModel
theorem FiniteProtocol.UniformCallsB.calls_le {p : ℝ} {a b af bf m : ℕ}
    {P : FiniteProtocol p a b af bf} (hP : P.UniformCallsB m) : P.calls ≤ m := by
  induction P generalizing m with
  | done a b => exact Nat.zero_le m
  | alice K next ih => exact Finset.sup_le fun z _ => ih z (hP z)
  | bob K next ih => exact Finset.sup_le fun z _ => ih z (hP z)
  | call next ih =>
    rcases hP with ⟨k, hm, hk⟩
    change next.calls + 1 ≤ m
    rw [hm]
    exact Nat.add_le_add_right (ih hk) 1

theorem FiniteBlockProtocolB.exists_merge_scalarB {p : ℝ}
    {n a b af bf c d cf df m : ℕ}
    (P : FiniteBlockProtocolB p n a b af bf) (Q : FiniteProtocol p c d cf df)
    (hP : P.UniformCallsB m) (hQ : Q.UniformCallsB m) :
    ∃ R : FiniteBlockProtocolB p (n + 1) (a * c) (b * d) (af * cf) (bf * df),
      R.calls ≤ m ∧ R.UniformCallsB m ∧ ∀ ρ σ,
        R.output (pairMatrixB ρ σ) = pairMatrixB (P.output ρ) (Q.output σ) := by
  induction P generalizing c d cf df m with
  | done a b =>
    induction Q generalizing m with
    | done c d =>
      refine ⟨.done (a * c) (b * d), ?_, ?_, ?_⟩
      · exact Nat.zero_le m
      · exact hP
      · intro ρ σ; rfl
    | alice K next ihQ =>
      choose R hR using fun z => ihQ z hP (hQ z)
      refine ⟨.alice (tensorRightInstrumentB K a) R, ?_, ?_, ?_⟩
      · exact Finset.sup_le fun z _ => (hR z).1
      · exact fun z => (hR z).2.1
      · intro ρ σ
        have ho := fun z => (hR z).2.2
        simp only [FiniteBlockProtocolB.output, FiniteProtocol.output,
          alice_tensorRight_actionB, ho, pairMatrixB_sum_right]
    | bob K next ihQ =>
      choose R hR using fun z => ihQ z hP (hQ z)
      refine ⟨.bob (tensorRightInstrumentB K b) R, ?_, ?_, ?_⟩
      · exact Finset.sup_le fun z _ => (hR z).1
      · exact fun z => (hR z).2.1
      · intro ρ σ
        have ho := fun z => (hR z).2.2
        simp only [FiniteBlockProtocolB.output, FiniteProtocol.output,
          bob_tensorRight_actionB, ho, pairMatrixB_sum_right]
    | call next ihQ =>
      rcases hQ with ⟨k, hm, hk⟩
      change m = 0 at hP
      omega
  | alice K next ihP =>
    choose R hR using fun z => ihP z Q (hP z) hQ
    refine ⟨.alice (tensorLeftInstrumentB K c) R, ?_, ?_, ?_⟩
    · exact Finset.sup_le fun z _ => (hR z).1
    · exact fun z => (hR z).2.1
    · intro ρ σ
      have ho := fun z => (hR z).2.2
      simp only [FiniteBlockProtocolB.output, alice_tensorLeft_actionB,
        ho, pairMatrixB_sum_left]
  | bob K next ihP =>
    choose R hR using fun z => ihP z Q (hP z) hQ
    refine ⟨.bob (tensorLeftInstrumentB K d) R, ?_, ?_, ?_⟩
    · exact Finset.sup_le fun z _ => (hR z).1
    · exact fun z => (hR z).2.1
    · intro ρ σ
      have ho := fun z => (hR z).2.2
      simp only [FiniteBlockProtocolB.output, bob_tensorLeft_actionB,
        ho, pairMatrixB_sum_left]
  | @blockCall a₀ b₀ af₀ bf₀ nextP ihP =>
    induction Q generalizing m with
    | done c d =>
      rcases hP with ⟨k, hm, hk⟩
      change m = 0 at hQ
      omega
    | alice K next ihQ =>
      choose R hR using fun z => ihQ z hP (hQ z)
      refine ⟨.alice (tensorRightInstrumentB K (doubleDimB n a₀)) R, ?_, ?_, ?_⟩
      · exact Finset.sup_le fun z _ => (hR z).1
      · exact fun z => (hR z).2.1
      · intro ρ σ
        have ho := fun z => (hR z).2.2
        simp only [FiniteBlockProtocolB.output, FiniteProtocol.output,
          alice_tensorRight_actionB, ho, pairMatrixB_sum_right]
    | bob K next ihQ =>
      choose R hR using fun z => ihQ z hP (hQ z)
      refine ⟨.bob (tensorRightInstrumentB K b₀) R, ?_, ?_, ?_⟩
      · exact Finset.sup_le fun z _ => (hR z).1
      · exact fun z => (hR z).2.1
      · intro ρ σ
        have ho := fun z => (hR z).2.2
        simp only [FiniteBlockProtocolB.output, FiniteProtocol.output,
          bob_tensorRight_actionB, ho, pairMatrixB_sum_right]
    | @call c₀ d₀ cf₀ df₀ nextQ ihQ =>
      rcases hP with ⟨k, hm, hN⟩
      rcases hQ with ⟨l, hmQ, hM⟩
      have hkl : l = k := by omega
      subst l
      rcases ihP nextQ hN hM with ⟨R, hC, hU, hO⟩
      refine ⟨mergeBlockCallThenB p n a₀ b₀ c₀ d₀ R, ?_, ?_, ?_⟩
      · rw [mergeBlockCallThenB_calls, hm]
        exact Nat.add_le_add_right hC 1
      · rw [hm]
        exact mergeBlockCallThenB_uniform p n a₀ b₀ c₀ d₀ hU
      · intro ρ σ
        rw [mergeBlockCallThenB_product_output]
        exact hO _ _

def lanePowerDimB : ℕ → ℕ → ℕ
  | 0, a => a
  | n + 1, a => lanePowerDimB n a * a

theorem lanePowerDimB_eq_pow (n a : ℕ) : lanePowerDimB n a = a ^ (n + 1) := by
  induction n with
  | zero => simp [lanePowerDimB]
  | succ n ih => simp only [lanePowerDimB, ih, pow_succ]

def lanePowerMatrixB {a b : ℕ} (ρ : BipartiteMatrix a b) :
    (n : ℕ) → BipartiteMatrix (lanePowerDimB n a) (lanePowerDimB n b)
  | 0 => ρ
  | n + 1 => pairMatrixB (lanePowerMatrixB ρ n) ρ

theorem FiniteProtocol.exists_uniform_lanesB {p : ℝ} {a b af bf m : ℕ}
    (P : FiniteProtocol p a b af bf) (hP : P.UniformCallsB m) :
    ∀ n, ∃ R : FiniteBlockProtocolB p (n + 1)
      (lanePowerDimB n a) (lanePowerDimB n b)
      (lanePowerDimB n af) (lanePowerDimB n bf),
      R.calls ≤ m ∧ R.UniformCallsB m ∧ ∀ ρ,
        R.output (lanePowerMatrixB ρ n) = lanePowerMatrixB (P.output ρ) n := by
  intro n
  induction n with
  | zero =>
    refine ⟨P.toBlockOneB, ?_, P.toBlockOneB_uniform hP, ?_⟩
    · change P.toBlockOneB.calls ≤ m
      exact P.toBlockOneB_calls.le.trans hP.calls_le
    · intro ρ
      exact P.toBlockOneB_output ρ
  | succ n ih =>
    rcases ih with ⟨R, hC, hU, hO⟩
    rcases R.exists_merge_scalarB P hU hP with ⟨S, hSC, hSU, hSO⟩
    refine ⟨S, hSC, hSU, ?_⟩
    intro ρ
    change S.output (pairMatrixB (lanePowerMatrixB ρ n) ρ) =
      pairMatrixB (lanePowerMatrixB (P.output ρ) n) (P.output ρ)
    rw [hSO, hO]

theorem FiniteProtocol.exists_independent_lanesB {p : ℝ} {a b af bf : ℕ}
    (P : FiniteProtocol p a b af bf) (m : ℕ) (hP : P.calls ≤ m) (n : ℕ) :
    ∃ R : FiniteBlockProtocolB p (n + 1)
      (lanePowerDimB n a) (lanePowerDimB n b)
      (lanePowerDimB n af) (lanePowerDimB n bf),
      R.calls ≤ m ∧ R.UniformCallsB m ∧ R.represented_toMatrix.calls ≤ (n + 1) * m ∧ ∀ ρ,
        R.output (lanePowerMatrixB ρ n) = lanePowerMatrixB (P.output ρ) n := by
  rcases P.exists_uniform_paddingB m hP with ⟨Q, hC, hU, hO⟩
  rcases Q.exists_uniform_lanesB hU n with ⟨R, hRC, hRU, hRO⟩
  refine ⟨R, hRC, hRU, R.toMatrix_calls_bound hRC, ?_⟩
  intro ρ
  calc
    _ = lanePowerMatrixB (Q.output ρ) n := hRO ρ
    _ = _ := congrArg (fun M => lanePowerMatrixB M n) (hO ρ)

theorem FiniteProtocol.exists_independent_matrix_lanesB {p : ℝ} {a b af bf : ℕ}
    (P : FiniteProtocol p a b af bf) (m : ℕ) (hP : P.calls ≤ m) (n : ℕ) :
    ∃ S : FiniteProtocol p (lanePowerDimB n a) (lanePowerDimB n b)
      (lanePowerDimB n af) (lanePowerDimB n bf),
      S.calls ≤ (n + 1) * m ∧ ∀ ρ,
        S.output (lanePowerMatrixB ρ n) = lanePowerMatrixB (P.output ρ) n := by
  rcases P.exists_independent_lanesB m hP n with ⟨R, hC, hU, hN, hO⟩
  refine ⟨R.represented_toMatrix, hN, ?_⟩
  intro ρ
  calc
    _ = R.output (lanePowerMatrixB ρ n) := R.toMatrix_output _
    _ = _ := hO ρ

end QuantumProver.AmplitudeDamping.FiniteModel

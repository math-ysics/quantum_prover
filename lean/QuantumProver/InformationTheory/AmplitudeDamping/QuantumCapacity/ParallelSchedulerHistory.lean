import QuantumProver.InformationTheory.AmplitudeDamping.QuantumCapacity.ParallelScheduler

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open scoped BigOperators ComplexConjugate ComplexOrder Matrix Kronecker

namespace QuantumProver.AmplitudeDamping.FiniteModel

inductive MergeScalarDerivationB (p : ℝ) (n : ℕ) :
    {a b af bf c d cf df : ℕ} →
    FiniteBlockProtocolB p n a b af bf → FiniteProtocol p c d cf df →
    FiniteBlockProtocolB p (n + 1) (a * c) (b * d) (af * cf) (bf * df) → Prop
  | done (a b c d : ℕ) : MergeScalarDerivationB p n
      (.done a b) (.done c d) (.done (a * c) (b * d))
  | aliceLeft {a b ao af bf c d cf df k : ℕ}
      (K : KrausInstrument a ao k)
      (P : Fin k → FiniteBlockProtocolB p n ao b af bf)
      (Q : FiniteProtocol p c d cf df)
      (R : Fin k → FiniteBlockProtocolB p (n + 1) (ao * c) (b * d) (af * cf) (bf * df))
      (next : ∀ z, MergeScalarDerivationB p n (P z) Q (R z)) :
      MergeScalarDerivationB p n (.alice K P) Q (.alice (tensorLeftInstrumentB K c) R)
  | bobLeft {a b bo af bf c d cf df k : ℕ}
      (K : KrausInstrument b bo k)
      (P : Fin k → FiniteBlockProtocolB p n a bo af bf)
      (Q : FiniteProtocol p c d cf df)
      (R : Fin k → FiniteBlockProtocolB p (n + 1) (a * c) (bo * d) (af * cf) (bf * df))
      (next : ∀ z, MergeScalarDerivationB p n (P z) Q (R z)) :
      MergeScalarDerivationB p n (.bob K P) Q (.bob (tensorLeftInstrumentB K d) R)
  | aliceRight {a b af bf c d co cf df k : ℕ}
      (K : KrausInstrument c co k)
      (P : FiniteBlockProtocolB p n a b af bf)
      (Q : Fin k → FiniteProtocol p co d cf df)
      (R : Fin k → FiniteBlockProtocolB p (n + 1) (a * co) (b * d) (af * cf) (bf * df))
      (next : ∀ z, MergeScalarDerivationB p n P (Q z) (R z)) :
      MergeScalarDerivationB p n P (.alice K Q) (.alice (tensorRightInstrumentB K a) R)
  | bobRight {a b af bf c d do_ cf df k : ℕ}
      (K : KrausInstrument d do_ k)
      (P : FiniteBlockProtocolB p n a b af bf)
      (Q : Fin k → FiniteProtocol p c do_ cf df)
      (R : Fin k → FiniteBlockProtocolB p (n + 1) (a * c) (b * do_) (af * cf) (bf * df))
      (next : ∀ z, MergeScalarDerivationB p n P (Q z) (R z)) :
      MergeScalarDerivationB p n P (.bob K Q) (.bob (tensorRightInstrumentB K b) R)
  | pairedCall {a b af bf c d cf df : ℕ}
      (P : FiniteBlockProtocolB p n a (doubleDimB n b) af bf)
      (Q : FiniteProtocol p c (2 * d) cf df)
      (R : FiniteBlockProtocolB p (n + 1) (a * c) (doubleDimB n b * (2 * d))
        (af * cf) (bf * df))
      (next : MergeScalarDerivationB p n P Q R) :
      MergeScalarDerivationB p n (.blockCall P) (.call Q)
        (mergeBlockCallThenB p n a b c d R)

theorem MergeScalarDerivationB.output_eq {p : ℝ} {n a b af bf c d cf df : ℕ}
    {P : FiniteBlockProtocolB p n a b af bf} {Q : FiniteProtocol p c d cf df}
    {R : FiniteBlockProtocolB p (n + 1) (a * c) (b * d) (af * cf) (bf * df)}
    (h : MergeScalarDerivationB p n P Q R) : ∀ ρ σ,
      R.output (pairMatrixB ρ σ) = pairMatrixB (P.output ρ) (Q.output σ) := by
  induction h with
  | done a b c d => intro ρ σ; rfl
  | aliceLeft K P Q R next ih =>
    intro ρ σ
    simp only [FiniteBlockProtocolB.output, alice_tensorLeft_actionB, ih,
      pairMatrixB_sum_left]
  | bobLeft K P Q R next ih =>
    intro ρ σ
    simp only [FiniteBlockProtocolB.output, bob_tensorLeft_actionB, ih,
      pairMatrixB_sum_left]
  | aliceRight K P Q R next ih =>
    intro ρ σ
    simp only [FiniteBlockProtocolB.output, FiniteProtocol.output,
      alice_tensorRight_actionB, ih, pairMatrixB_sum_right]
  | bobRight K P Q R next ih =>
    intro ρ σ
    simp only [FiniteBlockProtocolB.output, FiniteProtocol.output,
      bob_tensorRight_actionB, ih, pairMatrixB_sum_right]
  | pairedCall P Q R next ih =>
    intro ρ σ
    rw [mergeBlockCallThenB_product_output]
    exact ih _ _

theorem MergeScalarDerivationB.uniform {p : ℝ} {n a b af bf c d cf df : ℕ}
    {P : FiniteBlockProtocolB p n a b af bf} {Q : FiniteProtocol p c d cf df}
    {R : FiniteBlockProtocolB p (n + 1) (a * c) (b * d) (af * cf) (bf * df)}
    (h : MergeScalarDerivationB p n P Q R) :
    ∀ {m}, P.UniformCallsB m → Q.UniformCallsB m → R.UniformCallsB m := by
  induction h with
  | done a b c d => intro m hP hQ; exact hP
  | aliceLeft K P Q R next ih =>
    intro m hP hQ
    exact fun z => ih z (hP z) hQ
  | bobLeft K P Q R next ih =>
    intro m hP hQ
    exact fun z => ih z (hP z) hQ
  | aliceRight K P Q R next ih =>
    intro m hP hQ
    exact fun z => ih z hP (hQ z)
  | bobRight K P Q R next ih =>
    intro m hP hQ
    exact fun z => ih z hP (hQ z)
  | pairedCall P Q R next ih =>
    intro m hP hQ
    rcases hP with ⟨k, hm, hN⟩
    rcases hQ with ⟨l, hmQ, hM⟩
    have hkl : l = k := by omega
    subst l
    rw [hm]
    exact mergeBlockCallThenB_uniform _ _ _ _ _ _ (ih hN hM)

theorem FiniteBlockProtocolB.UniformCallsB.calls_le {p : ℝ} {n a b af bf m : ℕ}
    {P : FiniteBlockProtocolB p n a b af bf} (hP : P.UniformCallsB m) : P.calls ≤ m := by
  induction P generalizing m with
  | done a b => exact Nat.zero_le m
  | alice K next ih => exact Finset.sup_le fun z _ => ih z (hP z)
  | bob K next ih => exact Finset.sup_le fun z _ => ih z (hP z)
  | blockCall next ih =>
    rcases hP with ⟨k, hm, hk⟩
    change next.calls + 1 ≤ m
    rw [hm]
    exact Nat.add_le_add_right (ih hk) 1

theorem FiniteBlockProtocolB.exists_merge_derivationB {p : ℝ}
    {n a b af bf c d cf df m : ℕ}
    (P : FiniteBlockProtocolB p n a b af bf) (Q : FiniteProtocol p c d cf df)
    (hP : P.UniformCallsB m) (hQ : Q.UniformCallsB m) :
    ∃ R : FiniteBlockProtocolB p (n + 1) (a * c) (b * d) (af * cf) (bf * df),
      MergeScalarDerivationB p n P Q R := by
  induction P generalizing c d cf df m with
  | done a b =>
    induction Q generalizing m with
    | done c d => exact ⟨.done (a * c) (b * d), .done a b c d⟩
    | alice K next ihQ =>
      choose R hR using fun z => ihQ z hP (hQ z)
      exact ⟨.alice (tensorRightInstrumentB K a) R,
        .aliceRight K (.done a b) next R hR⟩
    | bob K next ihQ =>
      choose R hR using fun z => ihQ z hP (hQ z)
      exact ⟨.bob (tensorRightInstrumentB K b) R,
        .bobRight K (.done a b) next R hR⟩
    | call next ihQ =>
      rcases hQ with ⟨k, hm, hk⟩
      change m = 0 at hP
      omega
  | alice K next ihP =>
    choose R hR using fun z => ihP z Q (hP z) hQ
    exact ⟨.alice (tensorLeftInstrumentB K c) R, .aliceLeft K next Q R hR⟩
  | bob K next ihP =>
    choose R hR using fun z => ihP z Q (hP z) hQ
    exact ⟨.bob (tensorLeftInstrumentB K d) R, .bobLeft K next Q R hR⟩
  | @blockCall a₀ b₀ af₀ bf₀ nextP ihP =>
    induction Q generalizing m with
    | done c d =>
      rcases hP with ⟨k, hm, hk⟩
      change m = 0 at hQ
      omega
    | alice K next ihQ =>
      choose R hR using fun z => ihQ z hP (hQ z)
      exact ⟨.alice (tensorRightInstrumentB K (doubleDimB n a₀)) R,
        .aliceRight K (.blockCall nextP) next R hR⟩
    | bob K next ihQ =>
      choose R hR using fun z => ihQ z hP (hQ z)
      exact ⟨.bob (tensorRightInstrumentB K b₀) R,
        .bobRight K (.blockCall nextP) next R hR⟩
    | @call c₀ d₀ cf₀ df₀ nextQ ihQ =>
      rcases hP with ⟨k, hm, hN⟩
      rcases hQ with ⟨l, hmQ, hM⟩
      have hkl : l = k := by omega
      subst l
      rcases ihP nextQ hN hM with ⟨R, hR⟩
      exact ⟨mergeBlockCallThenB p n a₀ b₀ c₀ d₀ R, .pairedCall nextP nextQ R hR⟩

theorem FiniteBlockProtocolB.exists_merge_scalar_with_derivationB {p : ℝ}
    {n a b af bf c d cf df m : ℕ}
    (P : FiniteBlockProtocolB p n a b af bf) (Q : FiniteProtocol p c d cf df)
    (hP : P.UniformCallsB m) (hQ : Q.UniformCallsB m) :
    ∃ R : FiniteBlockProtocolB p (n + 1) (a * c) (b * d) (af * cf) (bf * df),
      MergeScalarDerivationB p n P Q R ∧ R.calls ≤ m ∧ R.UniformCallsB m ∧
      ∀ ρ σ, R.output (pairMatrixB ρ σ) = pairMatrixB (P.output ρ) (Q.output σ) := by
  rcases P.exists_merge_derivationB Q hP hQ with ⟨R, hR⟩
  have hU := hR.uniform hP hQ
  exact ⟨R, hR, hU.calls_le, hU, hR.output_eq⟩

inductive IndependentLanesDerivationB (p : ℝ) {a b af bf : ℕ}
    (P : FiniteProtocol p a b af bf) : (n : ℕ) →
    FiniteBlockProtocolB p (n + 1) (lanePowerDimB n a) (lanePowerDimB n b)
      (lanePowerDimB n af) (lanePowerDimB n bf) → Prop
  | one : IndependentLanesDerivationB p P 0 P.toBlockOneB
  | append {n : ℕ}
      (R : FiniteBlockProtocolB p (n + 1) (lanePowerDimB n a) (lanePowerDimB n b)
        (lanePowerDimB n af) (lanePowerDimB n bf))
      (S : FiniteBlockProtocolB p (n + 1 + 1) (lanePowerDimB (n + 1) a)
        (lanePowerDimB (n + 1) b) (lanePowerDimB (n + 1) af) (lanePowerDimB (n + 1) bf))
      (previous : IndependentLanesDerivationB p P n R)
      (merge : MergeScalarDerivationB p (n + 1) R P S) :
      IndependentLanesDerivationB p P (n + 1) S

theorem IndependentLanesDerivationB.uniform {p : ℝ} {a b af bf n m : ℕ}
    {P : FiniteProtocol p a b af bf}
    {R : FiniteBlockProtocolB p (n + 1) (lanePowerDimB n a) (lanePowerDimB n b)
      (lanePowerDimB n af) (lanePowerDimB n bf)}
    (h : IndependentLanesDerivationB p P n R) (hP : P.UniformCallsB m) :
    R.UniformCallsB m := by
  induction h with
  | one => exact P.toBlockOneB_uniform hP
  | append R S previous merge ih => exact merge.uniform ih hP

theorem IndependentLanesDerivationB.output_eq {p : ℝ} {a b af bf n : ℕ}
    {P : FiniteProtocol p a b af bf}
    {R : FiniteBlockProtocolB p (n + 1) (lanePowerDimB n a) (lanePowerDimB n b)
      (lanePowerDimB n af) (lanePowerDimB n bf)}
    (h : IndependentLanesDerivationB p P n R) : ∀ ρ,
    R.output (lanePowerMatrixB ρ n) = lanePowerMatrixB (P.output ρ) n := by
  induction h with
  | one => intro ρ; exact P.toBlockOneB_output ρ
  | append R S previous merge ih =>
    intro ρ
    change S.output (pairMatrixB (lanePowerMatrixB ρ _) ρ) =
      pairMatrixB (lanePowerMatrixB (P.output ρ) _) (P.output ρ)
    exact (merge.output_eq _ _).trans
      (congrArg (fun M => pairMatrixB M (P.output ρ)) (ih ρ))

theorem FiniteProtocol.exists_uniform_lanes_with_derivationB {p : ℝ} {a b af bf m : ℕ}
    (P : FiniteProtocol p a b af bf) (hP : P.UniformCallsB m) :
    ∀ n, ∃ R : FiniteBlockProtocolB p (n + 1) (lanePowerDimB n a) (lanePowerDimB n b)
      (lanePowerDimB n af) (lanePowerDimB n bf),
      IndependentLanesDerivationB p P n R ∧ R.calls ≤ m ∧ R.UniformCallsB m ∧
      R.represented_toMatrix.calls ≤ (n + 1) * m ∧ ∀ ρ,
      R.output (lanePowerMatrixB ρ n) = lanePowerMatrixB (P.output ρ) n := by
  intro n
  have hex : ∀ n, ∃ R : FiniteBlockProtocolB p (n + 1)
      (lanePowerDimB n a) (lanePowerDimB n b) (lanePowerDimB n af) (lanePowerDimB n bf),
      IndependentLanesDerivationB p P n R := by
    intro n
    induction n with
    | zero => exact ⟨P.toBlockOneB, .one⟩
    | succ n ih =>
      rcases ih with ⟨R, hR⟩
      rcases R.exists_merge_derivationB P (hR.uniform hP) hP with ⟨S, hS⟩
      exact ⟨S, .append R S hR hS⟩
  rcases hex n with ⟨R, hR⟩
  have hU := hR.uniform hP
  exact ⟨R, hR, hU.calls_le, hU, R.toMatrix_calls_bound hU.calls_le, hR.output_eq⟩

theorem FiniteProtocol.exists_padded_lanes_with_derivationB {p : ℝ} {a b af bf : ℕ}
    (P : FiniteProtocol p a b af bf) (m : ℕ) (hP : P.calls ≤ m) (n : ℕ) :
    ∃ Q : FiniteProtocol p a b af bf,
      Q.calls ≤ m ∧ Q.UniformCallsB m ∧ (∀ ρ, Q.output ρ = P.output ρ) ∧
      ∃ R : FiniteBlockProtocolB p (n + 1) (lanePowerDimB n a) (lanePowerDimB n b)
        (lanePowerDimB n af) (lanePowerDimB n bf),
        IndependentLanesDerivationB p Q n R ∧ R.calls ≤ m ∧ R.UniformCallsB m ∧
        R.represented_toMatrix.calls ≤ (n + 1) * m ∧ ∀ ρ,
        R.output (lanePowerMatrixB ρ n) = lanePowerMatrixB (P.output ρ) n := by
  rcases P.exists_uniform_paddingB m hP with ⟨Q, hC, hU, hO⟩
  rcases Q.exists_uniform_lanes_with_derivationB hU n with ⟨R, hR, hRC, hRU, hN, hRO⟩
  refine ⟨Q, hC, hU, hO, R, hR, hRC, hRU, hN, ?_⟩
  intro ρ
  rw [hRO, hO]

end QuantumProver.AmplitudeDamping.FiniteModel

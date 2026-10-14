import QuantumProver.InformationTheory.AmplitudeDamping.SecretKey.IdleEvePadding
import QuantumProver.InformationTheory.AmplitudeDamping.SecretKey.KeyEveIsometry

set_option autoImplicit false
set_option maxHeartbeats 600000

noncomputable section

open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix Kronecker

namespace QuantumProver.AmplitudeDamping.SecretKey.UniformPaddingKeyTransport

open QuantumProver.AmplitudeDamping.FiniteModel
open PhysicalProtocol PhysicalProtocol.FiniteKeyProtocol PublicHistory
open IdleEvePadding KeyEveIsometry IndependentLanes

theorem padding_finalKeyMatrix_B {E : Type*} [Fintype E] [DecidableEq E]
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {a b af bf d m : ℕ}
    {P Q : FiniteProtocol p a b af bf} (h : UniformPaddingDerivationB p m P Q) :
    ∃ f : (fromQuantum_B P).Environment → (fromQuantum_B Q).Environment,
    ∃ g : (fromQuantum_B Q).Environment → (fromQuantum_B P).Environment,
      Function.LeftInverse g f ∧
      let V := basisEmbedding_B
        (historyWithOldEveEmbedding_B (A := Fin d × Fin d) (E := E) f)
      Vᴴ * V = 1 ∧
      ∀ (labelA : Fin af → Fin d) (labelB : Fin bf → Fin d)
        (ρ : Density ((Fin a × Fin b) × E)),
        ((fromQuantum_B Q).finalKeyStateWithPriorEveLabels hp0 hp1 labelA labelB E ρ).mat =
          V * ((fromQuantum_B P).finalKeyStateWithPriorEveLabels hp0 hp1 labelA labelB E ρ).mat * Vᴴ := by
  rcases padding_readout_isometry_B (E := E) (K := Fin d × Fin d) h with
    ⟨f,g,hfg,hV,hO⟩
  refine ⟨f,g,hfg,hV,?_⟩
  intro labelA labelB ρ
  exact hO (fun i : Fin af × Fin bf => (labelA i.1,labelB i.2)) ρ.mat

theorem padding_finalKeyDensity_B {E : Type*} [Fintype E] [DecidableEq E]
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {a b af bf d m : ℕ}
    {P Q : FiniteProtocol p a b af bf} (h : UniformPaddingDerivationB p m P Q) :
    ∃ f : (fromQuantum_B P).Environment → (fromQuantum_B Q).Environment,
    ∃ g : (fromQuantum_B Q).Environment → (fromQuantum_B P).Environment,
      Function.LeftInverse g f ∧
      let V := basisEmbedding_B
        (historyWithOldEveEmbedding_B (A := Fin d × Fin d) (E := E) f)
      ∃ hV : Vᴴ * V = 1,
      ∀ (labelA : Fin af → Fin d) (labelB : Fin bf → Fin d)
        (ρ : Density ((Fin a × Fin b) × E)),
        (fromQuantum_B Q).finalKeyStateWithPriorEveLabels hp0 hp1 labelA labelB E ρ =
          isometryDensity V hV
            ((fromQuantum_B P).finalKeyStateWithPriorEveLabels hp0 hp1 labelA labelB E ρ) := by
  rcases padding_finalKeyMatrix_B hp0 hp1 (E := E) (d := d) h with ⟨f,g,hfg,hV,hO⟩
  refine ⟨f,g,hfg,hV,?_⟩
  intro labelA labelB ρ
  exact Density.eq_of_mat_eq (hO labelA labelB ρ)

theorem padding_keyG_le_B {E : Type*} [Fintype E] [DecidableEq E]
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {a b af bf d m : ℕ} (hd : 0 < d)
    {P Q : FiniteProtocol p a b af bf} (h : UniformPaddingDerivationB p m P Q)
    (labelA : Fin af → Fin d) (labelB : Fin bf → Fin d)
    (ρ : Density ((Fin a × Fin b) × E)) :
    optimalWholeKeySquaredFidelity d hd
      ((fromQuantum_B P).finalKeyStateWithPriorEveLabels hp0 hp1 labelA labelB E ρ) ≤
    optimalWholeKeySquaredFidelity d hd
      ((fromQuantum_B Q).finalKeyStateWithPriorEveLabels hp0 hp1 labelA labelB E ρ) := by
  rcases padding_finalKeyMatrix_B hp0 hp1 (E := E) (d := d) h with ⟨f,g,hfg,hV,hO⟩
  exact keyG_groundHistory_le d hd f hfg.injective
    ((fromQuantum_B P).finalKeyStateWithPriorEveLabels hp0 hp1 labelA labelB E ρ)
    ((fromQuantum_B Q).finalKeyStateWithPriorEveLabels hp0 hp1 labelA labelB E ρ)
    (hO labelA labelB ρ)

theorem exists_uniformPadding_keyG_B {E : Type*} [Fintype E] [DecidableEq E]
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {a b af bf d : ℕ} (hd : 0 < d)
    (P : FiniteProtocol p a b af bf) (m : ℕ) (hP : P.calls ≤ m) :
    ∃ Q : FiniteProtocol p a b af bf,
      UniformPaddingDerivationB p m P Q ∧ Q.calls ≤ m ∧ Q.UniformCallsB m ∧
      ∀ (labelA : Fin af → Fin d) (labelB : Fin bf → Fin d)
        (ρ : Density ((Fin a × Fin b) × E)),
        optimalWholeKeySquaredFidelity d hd
          ((fromQuantum_B P).finalKeyStateWithPriorEveLabels hp0 hp1 labelA labelB E ρ) ≤
        optimalWholeKeySquaredFidelity d hd
          ((fromQuantum_B Q).finalKeyStateWithPriorEveLabels hp0 hp1 labelA labelB E ρ) := by
  rcases P.exists_uniform_padding_with_derivationB m hP with ⟨Q,hQ,hQC,hQU,hQO⟩
  exact ⟨Q,hQ,hQC,hQU,padding_keyG_le_B hp0 hp1 hd hQ⟩

end QuantumProver.AmplitudeDamping.SecretKey.UniformPaddingKeyTransport

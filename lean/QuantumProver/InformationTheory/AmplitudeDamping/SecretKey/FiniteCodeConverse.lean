import QuantumProver.InformationTheory.AmplitudeDamping.SecretKey.PrivateTestResource
import QuantumProver.InformationTheory.AmplitudeDamping.SecretKey.OutputContinuity
import QuantumProver.InformationTheory.AmplitudeDamping.SecretKey.InitialSeedAncillas
import QuantumProver.InformationTheory.AmplitudeDamping.SecretKey.SeedKeyReadoutTransport

set_option autoImplicit false

noncomputable section

open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix Kronecker

namespace QuantumProver.AmplitudeDamping.SecretKey.FiniteCodeConverse

open PrivateTestResource
open QuantumProver.AmplitudeDamping.FiniteModel (sandwichedDivergence)

section LaboratoryCharts

variable {A B A' B' : Type*} [Fintype A] [Fintype B] [Fintype A'] [Fintype B']
  [DecidableEq A] [DecidableEq B] [DecidableEq A'] [DecidableEq B']

theorem normalizedSEP_relabel_le (eA : A' ≃ A) (eB : B' ≃ B)
    (ρ : Density (A × B)) (α : ℝ) :
    normalizedSEPEntanglement α (ρ.relabel (eA.prodCongr eB)) ≤
      normalizedSEPEntanglement α ρ := by
  unfold normalizedSEPEntanglement
  apply le_sInf
  rintro x ⟨σ, hσ, rfl⟩
  have hσ' : IsSeparable (σ.relabel (eA.prodCongr eB)) :=
    separableCone_submatrix_product_B eA eB hσ
  have hD : sandwichedDivergence α (ρ.relabel (eA.prodCongr eB)).mat
      (σ.relabel (eA.prodCongr eB)).mat = sandwichedDivergence α ρ.mat σ.mat :=
    QuantumProver.AmplitudeDamping.TensorPower.sandwichedDivergence_submatrix_equiv
      ρ.positive σ.positive (eA.prodCongr eB) α
  exact (normalizedSEPEntanglement_le_comparison α
    (ρ.relabel (eA.prodCongr eB)) (σ.relabel (eA.prodCongr eB)) hσ').trans_eq hD

theorem normalizedSEP_relabel (eA : A' ≃ A) (eB : B' ≃ B)
    (ρ : Density (A × B)) (α : ℝ) :
    normalizedSEPEntanglement α (ρ.relabel (eA.prodCongr eB)) =
      normalizedSEPEntanglement α ρ := by
  apply le_antisymm (normalizedSEP_relabel_le eA eB ρ α)
  have hρ : (ρ.relabel (eA.prodCongr eB)).relabel (eA.symm.prodCongr eB.symm) = ρ := by
    apply Density.eq_of_mat_eq
    ext x y
    rcases x with ⟨x₁, x₂⟩
    rcases y with ⟨y₁, y₂⟩
    change ρ.mat (eA (eA.symm x₁), eB (eB.symm x₂))
      (eA (eA.symm y₁), eB (eB.symm y₂)) = ρ.mat (x₁,x₂) (y₁,y₂)
    simp only [Equiv.apply_symm_apply]
  have h := normalizedSEP_relabel_le eA.symm eB.symm (ρ.relabel (eA.prodCongr eB)) α
  rw [hρ] at h
  exact h

theorem normalizedSEP_le_quantum_chart {a b : ℕ}
    (eA : Fin a ≃ A) (eB : Fin b ≃ B) (ρ : Density (A × B)) (α : ℝ) :
    normalizedSEPEntanglement α ρ ≤
      QuantumProver.AmplitudeDamping.FiniteModel.sandwichedEntanglement α a b
        (ρ.relabel (eA.prodCongr eB)).mat := by
  rw [← normalizedSEP_relabel eA eB ρ α]
  exact normalizedSEPEntanglement_le_quantum _ α

end LaboratoryCharts

theorem localProduct_resource_le_quantum {a b ao bo : ℕ} {Z : Type*} [Fintype Z]
    (K : Z → Matrix (Fin ao) (Fin a) ℂ) (L : Z → Matrix (Fin bo) (Fin b) ℂ)
    (hKL : ∑ z, (K z ⊗ₖ L z)ᴴ * (K z ⊗ₖ L z) = 1)
    (ρ : Density (Fin a × Fin b)) {α : ℝ} (hα : 1 < α) :
    normalizedSEPEntanglement α ((localProductChannel K L hKL).onDensity ρ) ≤
      QuantumProver.AmplitudeDamping.FiniteModel.sandwichedEntanglement α a b ρ.mat :=
  (normalizedSEPEntanglement_le_quantum _ α).trans
    (QuantumProver.AmplitudeDamping.FiniteModel.sandwichedEntanglement_local_kraus_le
      K L hKL ρ.positive hα)

section RetainedResource

open PhysicalProtocol PhysicalPurification PrivateTest

variable {p : ℝ} {a b af bf d ah bh : ℕ} {E : Type*} [Fintype E] [DecidableEq E]

theorem protocol_keyG_strong_bound_of_quantum_retained_resource_le
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (P : FiniteKeyProtocol p a b af bf)
    (labelA : Fin af → Fin d) (labelB : Fin bf → Fin d)
    (C : Matrix (Fin a × Fin b) E ℂ) (hC : (Cᴴ * C).trace = 1)
    (eA : Fin ah ≃ P.comparisonPublicHistory_B × Fin af)
    (eB : Fin bh ≃ P.comparisonPublicHistory_B × Fin bf)
    (hd : 0 < d) (m : ℕ) (k z : ℝ) (hz0 : 0 < z) (hz1 : z < 1)
    (hE : QuantumProver.AmplitudeDamping.FiniteModel.sandwichedEntanglement (1 / (1 - z)) ah bh
      ((honestMarginal ((PublicHistory.wholeRetainedChannelWithEve_B hp0 hp1 P E).onDensity
        (density C hC))).relabel (eA.prodCongr eB)).mat ≤
        ((k + (m : ℝ) * channelBz p z : ℝ) : EReal)) :
    optimalWholeKeySquaredFidelity d hd
      (P.finalKeyStateWithPriorEveLabels hp0 hp1 labelA labelB E (density C hC)) ≤
      min 1 ((2 : ℝ) ^ (-z * (log2 (d : ℝ) - k - (m : ℝ) * channelBz p z))) :=
  protocol_keyG_strong_bound_of_retained_resource_le hp0 hp1 P labelA labelB C hC hd m k z hz0 hz1
    ((normalizedSEP_le_quantum_chart eA eB _ _).trans hE)

end RetainedResource

section PhysicalCodePreparation

open OutputContinuity PhysicalProtocol PhysicalPurification PrivateTest
open InitialSeed InitialSeedAncillas

variable {p k : ℝ} {m d : ℕ}

theorem code_seedSize_pos (C : FiniteSeedKeyCode p m d k) : 0 < C.seedSize := by
  by_contra hn
  have hzero : C.seedSize = 0 := Nat.eq_zero_of_not_pos hn
  have hsum : (∑ i : Fin C.seedSize, C.seedLaw.weight i) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    exfalso
    have hi : i.val < 0 := lt_of_lt_of_le i.isLt hzero.le
    exact Nat.not_lt_zero _ hi
  have hnorm := C.seedLaw.normalized
  rw [hsum] at hnorm
  norm_num at hnorm

def preparedProtocol (C : FiniteSeedKeyCode p m d k) :
    FiniteKeyProtocol p
      (C.seedSize * ((C.aliceAncillaSize * C.priorEveSize) * (C.seedSize * C.aliceAncillaSize)))
      (C.bobAncillaSize * (C.seedSize * C.bobAncillaSize))
      (C.seedSize * ((C.aliceAncillaSize * C.priorEveSize) * C.aliceFinalSize))
      (C.bobAncillaSize * C.bobFinalSize) :=
  seedPureProtocol (f := C.priorEveSize) C.protocol

def preparedInput (C : FiniteSeedKeyCode p m d k) :
    Density ((Fin (C.seedSize * ((C.aliceAncillaSize * C.priorEveSize) *
      (C.seedSize * C.aliceAncillaSize))) ×
      Fin (C.bobAncillaSize * (C.seedSize * C.bobAncillaSize))) × Fin C.priorEveSize) :=
  seedPureMatrixInput C.seedLaw C.aliceAncilla C.bobAncilla C.priorEve

def preparedCoefficient (C : FiniteSeedKeyCode p m d k) :
    Matrix (Fin (C.seedSize * ((C.aliceAncillaSize * C.priorEveSize) *
      (C.seedSize * C.aliceAncillaSize))) ×
      Fin (C.bobAncillaSize * (C.seedSize * C.bobAncillaSize))) (Fin C.priorEveSize) ℂ :=
  seedPureMatrixCoefficient C.seedLaw C.aliceAncilla C.bobAncilla C.priorEve

theorem preparedCoefficient_normalized (C : FiniteSeedKeyCode p m d k) :
    ((preparedCoefficient C)ᴴ * preparedCoefficient C).trace = 1 :=
  seedPureMatrixCoefficient_normalized C.seedLaw C.aliceAncilla C.bobAncilla C.priorEve

theorem preparedInput_eq_density (C : FiniteSeedKeyCode p m d k) :
    preparedInput C = density (preparedCoefficient C) (preparedCoefficient_normalized C) := by
  apply Density.eq_of_mat_eq
  exact seedPureMatrixInput_coefficient C.seedLaw C.aliceAncilla C.bobAncilla C.priorEve

theorem preparedProtocol_calls (C : FiniteSeedKeyCode p m d k) :
    (preparedProtocol C).calls = C.protocol.calls := seedPureProtocol_calls C.protocol

theorem preparedProtocol_calls_le (C : FiniteSeedKeyCode p m d k) :
    (preparedProtocol C).calls ≤ m := by
  rw [preparedProtocol_calls]
  exact C.calls_le

theorem preparedInput_quantum_resource_le_bits (C : FiniteSeedKeyCode p m d k)
    {z : ℝ} (hz0 : 0 < z) (hz1 : z < 1) :
    QuantumProver.AmplitudeDamping.FiniteModel.sandwichedEntanglement (1 / (1 - z))
      (C.seedSize * ((C.aliceAncillaSize * C.priorEveSize) * (C.seedSize * C.aliceAncillaSize)))
      (C.bobAncillaSize * (C.seedSize * C.bobAncillaSize))
      (honestMarginal (preparedInput C)).mat ≤ (k : EReal) := by
  letI : Nonempty (Fin C.seedSize) := ⟨⟨0, code_seedSize_pos C⟩⟩
  exact seedPureMatrixInput_resource_le_bits C.seedLaw C.aliceAncilla C.bobAncilla C.priorEve
    hz0 hz1 C.seed_alphabet_le

theorem preparedInput_matrix_resource_le_bits (C : FiniteSeedKeyCode p m d k)
    {z : ℝ} (hz0 : 0 < z) (hz1 : z < 1) :
    normalizedSEPEntanglement (1 / (1 - z)) (honestMarginal (preparedInput C)) ≤ (k : EReal) :=
  (normalizedSEPEntanglement_le_quantum _ _).trans
    (preparedInput_quantum_resource_le_bits C hz0 hz1)

theorem code_initialHonest_eq_copiedAncillas (C : FiniteSeedKeyCode p m d k) :
    C.initialHonest = copiedSeedAncillas C.seedLaw C.aliceAncilla C.bobAncilla := rfl

theorem prepared_fullOutput_recovers_physical (C : FiniteSeedKeyCode p m d k) :
    forgetPrivateBobOutput C.bobAncillaSize C.protocol
      (forgetPrivateAliceOutput (C.aliceAncillaSize * C.priorEveSize)
        (withPrivateBob C.bobAncillaSize C.protocol)
        (forgetPrivateAliceOutput C.seedSize
          (withPrivateAlice (C.aliceAncillaSize * C.priorEveSize)
            (withPrivateBob C.bobAncillaSize C.protocol))
          (PublicHistory.localPriorEveMatrix_B (preparedProtocol C)
            (density (preparedCoefficient C) (preparedCoefficient_normalized C)).mat))) =
      PublicHistory.localPriorEveMatrix_B C.protocol C.initialDensity.mat := by
  rw [← preparedInput_eq_density]
  exact seedPureProtocol_physical_output C.protocol C.seedLaw C.aliceAncilla C.bobAncilla C.priorEve

end PhysicalCodePreparation

section PhysicalCodeReadout

open OutputContinuity PhysicalProtocol PhysicalPurification PrivateTest
open SeedKeyReadoutTransport

variable {p k : ℝ} {m d : ℕ}

def preparedLabelA (C : FiniteSeedKeyCode p m d k) :
    Fin (C.seedSize * ((C.aliceAncillaSize * C.priorEveSize) * C.aliceFinalSize)) → Fin d :=
  seedAliceKeyLabel C.labelA

def preparedLabelB (C : FiniteSeedKeyCode p m d k) :
    Fin (C.bobAncillaSize * C.bobFinalSize) → Fin d := seedBobKeyLabel C.labelB

def preparedEveEquiv (C : FiniteSeedKeyCode p m d k) :
    ((preparedProtocol C).Environment × Fin C.priorEveSize) ≃
      (C.protocol.Environment × Fin C.priorEveSize) := seedPureEveEquiv C.protocol

theorem prepared_finalKeyState (C : FiniteSeedKeyCode p m d k)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (preparedProtocol C).finalKeyStateWithPriorEveLabels hp0 hp1
      (preparedLabelA C) (preparedLabelB C) (Fin C.priorEveSize) (preparedInput C) =
      (C.output hp0 hp1).relabel
        ((Equiv.refl (Fin d × Fin d)).prodCongr (preparedEveEquiv C)) :=
  seedPureProtocol_finalKeyState hp0 hp1 C.protocol C.labelA C.labelB
    C.seedLaw C.aliceAncilla C.bobAncilla C.priorEve

theorem prepared_keyG (C : FiniteSeedKeyCode p m d k)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hd : 0 < d) :
    optimalWholeKeySquaredFidelity d hd
      ((preparedProtocol C).finalKeyStateWithPriorEveLabels hp0 hp1
        (preparedLabelA C) (preparedLabelB C) (Fin C.priorEveSize) (preparedInput C)) =
      optimalWholeKeySquaredFidelity d hd (C.output hp0 hp1) := by
  rw [prepared_finalKeyState]
  exact keyG_Eve_relabel d hd (preparedEveEquiv C) (C.output hp0 hp1)

def preparedRetainedHonest (C : FiniteSeedKeyCode p m d k)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    Density (((preparedProtocol C).comparisonPublicHistory_B ×
      Fin (C.seedSize * ((C.aliceAncillaSize * C.priorEveSize) * C.aliceFinalSize))) ×
      ((preparedProtocol C).comparisonPublicHistory_B × Fin (C.bobAncillaSize * C.bobFinalSize))) := by
  classical
  exact honestMarginal ((PublicHistory.wholeRetainedChannelWithEve_B hp0 hp1
    (preparedProtocol C) (Fin C.priorEveSize)).onDensity (preparedInput C))

theorem code_keyG_strong_bound_of_retained_resource_le
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (C : FiniteSeedKeyCode p m d k)
    (hd : 0 < d) {z : ℝ} (hz0 : 0 < z) (hz1 : z < 1)
    (hE : normalizedSEPEntanglement (1 / (1 - z)) (preparedRetainedHonest C hp0 hp1) ≤
      ((k + (m : ℝ) * channelBz p z : ℝ) : EReal)) :
    optimalWholeKeySquaredFidelity d hd (C.output hp0 hp1) ≤
      min 1 (strongExponentBound p z k m d) := by
  have hE' : normalizedSEPEntanglement (1 / (1 - z))
      (honestMarginal ((PublicHistory.wholeRetainedChannelWithEve_B hp0 hp1
        (preparedProtocol C) (Fin C.priorEveSize)).onDensity
          (density (preparedCoefficient C) (preparedCoefficient_normalized C)))) ≤
        ((k + (m : ℝ) * channelBz p z : ℝ) : EReal) := by
    simpa only [preparedRetainedHonest, preparedInput_eq_density] using hE
  have h := protocol_keyG_strong_bound_of_retained_resource_le hp0 hp1 (preparedProtocol C)
    (preparedLabelA C) (preparedLabelB C) (preparedCoefficient C)
    (preparedCoefficient_normalized C) hd m k z hz0 hz1 hE'
  rw [← preparedInput_eq_density C, prepared_keyG C hp0 hp1 hd] at h
  exact h

theorem code_keyG_strong_bound_of_quantum_retained_resource_le
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (C : FiniteSeedKeyCode p m d k)
    {ah bh : ℕ}
    (eA : Fin ah ≃ (preparedProtocol C).comparisonPublicHistory_B ×
      Fin (C.seedSize * ((C.aliceAncillaSize * C.priorEveSize) * C.aliceFinalSize)))
    (eB : Fin bh ≃ (preparedProtocol C).comparisonPublicHistory_B ×
      Fin (C.bobAncillaSize * C.bobFinalSize))
    (hd : 0 < d) {z : ℝ} (hz0 : 0 < z) (hz1 : z < 1)
    (hE : QuantumProver.AmplitudeDamping.FiniteModel.sandwichedEntanglement (1 / (1 - z)) ah bh
      ((preparedRetainedHonest C hp0 hp1).relabel (eA.prodCongr eB)).mat ≤
        ((k + (m : ℝ) * channelBz p z : ℝ) : EReal)) :
    optimalWholeKeySquaredFidelity d hd (C.output hp0 hp1) ≤
      min 1 (strongExponentBound p z k m d) :=
  code_keyG_strong_bound_of_retained_resource_le hp0 hp1 C hd hz0 hz1
    ((normalizedSEP_le_quantum_chart eA eB _ _).trans hE)

end PhysicalCodeReadout

end QuantumProver.AmplitudeDamping.SecretKey.FiniteCodeConverse

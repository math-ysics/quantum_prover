import QuantumProver.InformationTheory.WernerEndpoint.AllDimensionalMoment
import QuantumProver.InformationTheory.WernerEndpoint.OperationalEndpointCost

set_option autoImplicit false

noncomputable section

namespace QuantumProver.WernerEndpoint.MatrixCPProtocol

open OperationalEndpointCost
open QuantumProver.SuperchannelDiscrimination.CPTPKraus
open scoped BigOperators Kronecker

abbrev LocalMap (a a' : ℕ) := Matrix (Fin a) (Fin a) ℂ →ₗ[ℂ] Matrix (Fin a') (Fin a') ℂ
abbrev JointMatrix (a b : ℕ) := Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ

def finiteSelectiveKraus {h a a' : ℕ} (Φ : Fin h → LocalMap a a') :
    Fin h → Fin (Fintype.card (Fin a × Fin a')) → Matrix (Fin a') (Fin a) ℂ :=
  fun j k => CPInstrument.selectiveKraus Φ
    (j, (Fintype.equivFin (Fin a × Fin a')).symm k)

theorem finiteSelectiveKraus_complete {h a a' : ℕ}
    (Φ : Fin h → LocalMap a a') (hCP : ∀ j, CompletelyPositive (Φ j))
    (hTotal : ∀ ρ : Matrix (Fin a) (Fin a) ℂ, ∑ j, (Φ j ρ).trace = ρ.trace) :
    (∑ j, ∑ k, (finiteSelectiveKraus Φ j k).conjTranspose *
      finiteSelectiveKraus Φ j k) = 1 := by
  have hSum : (∑ j, ∑ k, (finiteSelectiveKraus Φ j k).conjTranspose *
      finiteSelectiveKraus Φ j k) =
      ∑ je : Fin h × (Fin a × Fin a'),
        (CPInstrument.selectiveKraus Φ je).conjTranspose * CPInstrument.selectiveKraus Φ je := by
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro j _
    exact (Fintype.equivFin (Fin a × Fin a')).symm.sum_comp
      (fun e => (CPInstrument.selectiveKraus Φ (j,e)).conjTranspose *
        CPInstrument.selectiveKraus Φ (j,e))
  rw [hSum]
  exact CPInstrument.selectiveKraus_totalGram Φ hCP hTotal

private theorem selectiveBranch_eq_krausMap {h a a' : ℕ}
    (Φ : Fin h → LocalMap a a') (hCP : ∀ j, CompletelyPositive (Φ j)) (j : Fin h) :
    Φ j = QuantumProver.ElegantJointMeasurement.CP.krausMap (fun e : Fin a × Fin a' => CPInstrument.selectiveKraus Φ (j,e)) := by
  apply LinearMap.ext
  intro ρ
  exact CPInstrument.selectiveKraus_branch Φ hCP j ρ

def aliceReferenceApply {a b a' : ℕ} (Φ : LocalMap a a') (ρ : JointMatrix a b) :
    JointMatrix a' b := amplify Φ (Fin b) ρ

def bobReferenceApply {a b b' : ℕ} (Φ : LocalMap b b') (ρ : JointMatrix a b) :
    JointMatrix a b' := QuantumProver.ElegantJointMeasurement.CP.amplification Φ a ρ

@[simp] theorem aliceReferenceApply_block {a b a' : ℕ}
    (Φ : LocalMap a a') (ρ : JointMatrix a b)
    (o p : Fin a') (r s : Fin b) :
    aliceReferenceApply Φ ρ (o,r) (p,s) = Φ (fun i j => ρ (i,r) (j,s)) o p := rfl

@[simp] theorem bobReferenceApply_block {a b b' : ℕ}
    (Φ : LocalMap b b') (ρ : JointMatrix a b)
    (r s : Fin a) (o p : Fin b') :
    bobReferenceApply Φ ρ (r,o) (s,p) = Φ (fun i j => ρ (r,i) (s,j)) o p := rfl

theorem aliceReferenceApply_eq_finiteKraus {h a b a' : ℕ}
    (Φ : Fin h → LocalMap a a') (hCP : ∀ j, CompletelyPositive (Φ j))
    (j : Fin h) (ρ : JointMatrix a b) :
    aliceReferenceApply (Φ j) ρ = ∑ k,
      (finiteSelectiveKraus Φ j k ⊗ₖ (1 : Matrix (Fin b) (Fin b) ℂ)) * ρ *
        (finiteSelectiveKraus Φ j k ⊗ₖ (1 : Matrix (Fin b) (Fin b) ℂ)).conjTranspose := by
  unfold aliceReferenceApply
  rw [selectiveBranch_eq_krausMap Φ hCP j, amplify_krausMap_reconstruct]
  exact ((Fintype.equivFin (Fin a × Fin a')).symm.sum_comp (fun e =>
    (CPInstrument.selectiveKraus Φ (j,e) ⊗ₖ (1 : Matrix (Fin b) (Fin b) ℂ)) * ρ *
      (CPInstrument.selectiveKraus Φ (j,e) ⊗ₖ (1 : Matrix (Fin b) (Fin b) ℂ)).conjTranspose)).symm

theorem bobReferenceApply_eq_finiteKraus {h a b b' : ℕ}
    (Φ : Fin h → LocalMap b b') (hCP : ∀ j, CompletelyPositive (Φ j))
    (j : Fin h) (ρ : JointMatrix a b) :
    bobReferenceApply (Φ j) ρ = ∑ k,
      ((1 : Matrix (Fin a) (Fin a) ℂ) ⊗ₖ finiteSelectiveKraus Φ j k) * ρ *
        ((1 : Matrix (Fin a) (Fin a) ℂ) ⊗ₖ finiteSelectiveKraus Φ j k).conjTranspose := by
  unfold bobReferenceApply
  rw [selectiveBranch_eq_krausMap Φ hCP j, QuantumProver.ElegantJointMeasurement.CP.amplification_krausMap]
  exact ((Fintype.equivFin (Fin b × Fin b')).symm.sum_comp (fun e =>
    ((1 : Matrix (Fin a) (Fin a) ℂ) ⊗ₖ CPInstrument.selectiveKraus Φ (j,e)) * ρ *
      ((1 : Matrix (Fin a) (Fin a) ℂ) ⊗ₖ CPInstrument.selectiveKraus Φ (j,e)).conjTranspose)).symm

def aliceCPNode {h a b a' c d : ℕ}
    (Φ : Fin h → LocalMap a a') (hCP : ∀ j, CompletelyPositive (Φ j))
    (hTotal : ∀ ρ : Matrix (Fin a) (Fin a) ℂ, ∑ j, (Φ j ρ).trace = ρ.trace)
    (next : Fin h → FiniteLocalProtocol c d a' b) : FiniteLocalProtocol c d a b :=
  .alice (finiteSelectiveKraus Φ) (finiteSelectiveKraus_complete Φ hCP hTotal) next

def bobCPNode {h a b b' c d : ℕ}
    (Φ : Fin h → LocalMap b b') (hCP : ∀ j, CompletelyPositive (Φ j))
    (hTotal : ∀ ρ : Matrix (Fin b) (Fin b) ℂ, ∑ j, (Φ j ρ).trace = ρ.trace)
    (next : Fin h → FiniteLocalProtocol c d a b') : FiniteLocalProtocol c d a b :=
  .bob (finiteSelectiveKraus Φ) (finiteSelectiveKraus_complete Φ hCP hTotal) next

theorem aliceCPNode_apply {h a b a' c d : ℕ}
    (Φ : Fin h → LocalMap a a') (hCP : ∀ j, CompletelyPositive (Φ j))
    (hTotal : ∀ ρ : Matrix (Fin a) (Fin a) ℂ, ∑ j, (Φ j ρ).trace = ρ.trace)
    (next : Fin h → FiniteLocalProtocol c d a' b) (ρ : JointMatrix a b) :
    (aliceCPNode Φ hCP hTotal next).apply ρ =
      ∑ j, (next j).apply (aliceReferenceApply (Φ j) ρ) := by
  rw [aliceCPNode, FiniteLocalProtocol.apply]
  simp_rw [← aliceReferenceApply_eq_finiteKraus Φ hCP]

theorem bobCPNode_apply {h a b b' c d : ℕ}
    (Φ : Fin h → LocalMap b b') (hCP : ∀ j, CompletelyPositive (Φ j))
    (hTotal : ∀ ρ : Matrix (Fin b) (Fin b) ℂ, ∑ j, (Φ j ρ).trace = ρ.trace)
    (next : Fin h → FiniteLocalProtocol c d a b') (ρ : JointMatrix a b) :
    (bobCPNode Φ hCP hTotal next).apply ρ =
      ∑ j, (next j).apply (bobReferenceApply (Φ j) ρ) := by
  rw [bobCPNode, FiniteLocalProtocol.apply]
  simp_rw [← bobReferenceApply_eq_finiteKraus Φ hCP]

inductive FiniteCPProtocol (c d : ℕ) : ℕ → ℕ → Type
  | terminal {a b : ℕ}
      (LA : Matrix (Fin c) (Fin a) ℂ) (LB : Matrix (Fin d) (Fin b) ℂ)
      (hLA : LA.conjTranspose * LA = 1) (hLB : LB.conjTranspose * LB = 1) :
      FiniteCPProtocol c d a b
  | alice {a b a' h : ℕ}
      (Φ : Fin h → LocalMap a a') (hCP : ∀ j, CompletelyPositive (Φ j))
      (hTotal : ∀ ρ : Matrix (Fin a) (Fin a) ℂ, ∑ j, (Φ j ρ).trace = ρ.trace)
      (next : Fin h → FiniteCPProtocol c d a' b) : FiniteCPProtocol c d a b
  | bob {a b b' h : ℕ}
      (Φ : Fin h → LocalMap b b') (hCP : ∀ j, CompletelyPositive (Φ j))
      (hTotal : ∀ ρ : Matrix (Fin b) (Fin b) ℂ, ∑ j, (Φ j ρ).trace = ρ.trace)
      (next : Fin h → FiniteCPProtocol c d a b') : FiniteCPProtocol c d a b

namespace FiniteCPProtocol

def apply {c d a b : ℕ} (T : FiniteCPProtocol c d a b) (ρ : JointMatrix a b) : JointMatrix c d :=
  match T with
  | .terminal LA LB _ _ => (LA ⊗ₖ LB) * ρ * (LA ⊗ₖ LB).conjTranspose
  | .alice Φ _ _ next => ∑ j, (next j).apply (aliceReferenceApply (Φ j) ρ)
  | .bob Φ _ _ next => ∑ j, (next j).apply (bobReferenceApply (Φ j) ρ)

def represented_toMatrix {c d a b : ℕ} (T : FiniteCPProtocol c d a b) : FiniteLocalProtocol c d a b :=
  match T with
  | .terminal LA LB hLA hLB => .terminal LA LB hLA hLB
  | .alice Φ hCP hTotal next => aliceCPNode Φ hCP hTotal (fun j => (next j).represented_toMatrix)
  | .bob Φ hCP hTotal next => bobCPNode Φ hCP hTotal (fun j => (next j).represented_toMatrix)

theorem represented_toMatrix_apply {c d a b : ℕ} (T : FiniteCPProtocol c d a b) (ρ : JointMatrix a b) :
    T.represented_toMatrix.apply ρ = T.apply ρ := by
  induction T with
  | terminal LA LB hLA hLB => rfl
  | alice Φ hCP hTotal next ih =>
      rw [represented_toMatrix, aliceCPNode_apply, apply]
      apply Finset.sum_congr rfl
      intro j _
      exact ih j _
  | bob Φ hCP hTotal next ih =>
      rw [represented_toMatrix, bobCPNode_apply, apply]
      apply Finset.sum_congr rfl
      intro j _
      exact ih j _

theorem exists_matrix_allComplex {c d a b : ℕ} (T : FiniteCPProtocol c d a b) :
    ∃ S : FiniteLocalProtocol c d a b, ∀ ρ : JointMatrix a b, S.apply ρ = T.apply ρ :=
  ⟨T.represented_toMatrix, T.represented_toMatrix_apply⟩

end FiniteCPProtocol
end QuantumProver.WernerEndpoint.MatrixCPProtocol

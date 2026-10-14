import QuantumProver.InformationTheory.WernerEndpoint.OperationalEndpointCost
import QuantumProver.InformationTheory.ElegantJointMeasurement.Teleportation

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

namespace QuantumProver.ElegantJointMeasurement.HilbertFiniteEJMProtocol

open scoped BigOperators Kronecker ComplexOrder
open QuantumProver.WernerEndpoint.OperationalEndpointCost QuantumProver.ElegantJointMeasurement.Teleportation

def labelColumn (j : Fin 4) : Matrix (Fin 4) (Fin 1) ℂ :=
  fun i _ => if i = j then 1 else 0

theorem labelColumn_isometry (j : Fin 4) :
    (labelColumn j).conjTranspose * labelColumn j = 1 := by
  ext i k
  fin_cases i; fin_cases k
  simp [labelColumn, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply]

def sharedTerminal (j : Fin 4) : FiniteLocalProtocol 4 4 1 1 :=
  .terminal (labelColumn j) (labelColumn j)
    (labelColumn_isometry j) (labelColumn_isometry j)

def bobMeasurement : FiniteLocalProtocol 4 4 1 4 :=
  .bob (h := 4) (z := 1) (fun j _ => bobFinBra j)
    (by simpa only [Fin.sum_univ_one] using bobFinBra_complete) sharedTerminal

def bobCorrection (m : Fin 4) : FiniteLocalProtocol 4 4 1 4 :=
  .bob (h := 1) (z := 1) (fun _ _ => bobFinCorrection m)
    (by simpa only [Fin.sum_univ_one] using bobFinCorrection_unitary_left m)
    (fun _ => bobMeasurement)

def oneEbitProtocol : FiniteLocalProtocol 4 4 4 4 :=
  .alice (h := 4) (z := 1) (fun m _ => aliceFinBra m)
    (by simpa only [Fin.sum_univ_one] using aliceFinBra_complete) bobCorrection

def protocolLeaf (m j : Fin 4) : FiniteLocalProtocol.leafIndex oneEbitProtocol :=
  ⟨m, 0, ⟨0, 0, ⟨j, 0, ()⟩⟩⟩

def leafLabelEquiv : FiniteLocalProtocol.leafIndex oneEbitProtocol ≃ (Fin 4 × Fin 4) where
  toFun u := (u.1, u.2.2.2.2.1)
  invFun q := protocolLeaf q.1 q.2
  left_inv u := by
    rcases u with ⟨m, ka, kc, kb, j, kj, u⟩
    have ha : ka = 0 := Subsingleton.elim _ _
    have hc : kc = 0 := Subsingleton.elim _ _
    have hb : kb = 0 := Subsingleton.elim _ _
    have hj : kj = 0 := Subsingleton.elim _ _
    subst ka; subst kc; subst kb; subst kj
    cases u
    rfl
  right_inv q := rfl

def terminalBra (m j : Fin 4) : Matrix (Fin 1 × Fin 1) (Fin 4 × Fin 4) ℂ :=
  aliceFinBra m ⊗ₖ (bobFinBra j * bobFinCorrection m)

def sharedColumn (j : Fin 4) : Matrix (Fin 4 × Fin 4) (Fin 1 × Fin 1) ℂ :=
  labelColumn j ⊗ₖ labelColumn j

theorem protocolLeaf_kraus (m j : Fin 4) :
    FiniteLocalProtocol.leafKraus oneEbitProtocol (protocolLeaf m j) =
      sharedColumn j * terminalBra m j := by
  change (labelColumn j * aliceFinBra m) ⊗ₖ
      ((labelColumn j * bobFinBra j) * bobFinCorrection m) = _
  rw [Matrix.mul_assoc]
  exact Matrix.mul_kronecker_mul _ _ _ _

theorem terminalBra_effect (m j : Fin 4) :
    (terminalBra m j).conjTranspose * terminalBra m j =
      (finiteBranchPair m j).productEffect := by
  ext ⟨i, k⟩ ⟨l, t⟩
  simp [terminalBra, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fintype.sum_prod_type,
    QuantumProver.ElegantJointMeasurement.Concurrence.SystemBraPair.productEffect_apply, finiteBranchPair]

theorem sharedColumn_isometry (j : Fin 4) :
    (sharedColumn j).conjTranspose * sharedColumn j = 1 := by
  rw [sharedColumn, Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
    labelColumn_isometry, Matrix.one_kronecker_one]

theorem sharedColumn_sandwich (j : Fin 4)
    (Y : Matrix (Fin 1 × Fin 1) (Fin 1 × Fin 1) ℂ) :
    sharedColumn j * Y * (sharedColumn j).conjTranspose =
      Matrix.trace Y • sharedLabelProjector j := by
  ext ⟨a, b⟩ ⟨c, d⟩
  simp [sharedColumn, labelColumn, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fintype.sum_prod_type,
    Matrix.trace, Matrix.diag, sharedLabelProjector, Matrix.diagonal_apply,
    Matrix.smul_apply]
  split_ifs <;> simp_all <;> aesop

theorem protocolLeaf_effect (m j : Fin 4) :
    (FiniteLocalProtocol.leafKraus oneEbitProtocol (protocolLeaf m j)).conjTranspose *
      FiniteLocalProtocol.leafKraus oneEbitProtocol (protocolLeaf m j) =
        (finiteBranchPair m j).productEffect := by
  rw [protocolLeaf_kraus]
  calc
    _ = (terminalBra m j).conjTranspose *
        ((sharedColumn j).conjTranspose * sharedColumn j) * terminalBra m j := by
      simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = (terminalBra m j).conjTranspose * terminalBra m j := by
      rw [sharedColumn_isometry, Matrix.mul_one]
    _ = _ := terminalBra_effect m j

theorem protocolLeaf_sandwich (m j : Fin 4)
    (X : Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) ℂ) :
    FiniteLocalProtocol.leafKraus oneEbitProtocol (protocolLeaf m j) * X *
        (FiniteLocalProtocol.leafKraus oneEbitProtocol (protocolLeaf m j)).conjTranspose =
      Matrix.trace ((finiteBranchPair m j).productEffect * X) • sharedLabelProjector j := by
  rw [protocolLeaf_kraus]
  calc
    _ = sharedColumn j * (terminalBra m j * X * (terminalBra m j).conjTranspose) *
        (sharedColumn j).conjTranspose := by
      simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = _ := by
      rw [sharedColumn_sandwich, Matrix.trace_mul_cycle, terminalBra_effect]

theorem oneEbitProtocol_apply
    (X : Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) ℂ) :
    oneEbitProtocol.apply X =
      ∑ m : Fin 4, ∑ j : Fin 4,
        Matrix.trace ((finiteBranchPair m j).productEffect * X) • sharedLabelProjector j := by
  rw [FiniteLocalProtocol.apply_eq_leafKraus]
  rw [← leafLabelEquiv.symm.sum_comp]
  simp only [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro m _
  apply Finset.sum_congr rfl
  intro j _
  exact protocolLeaf_sandwich m j X

theorem oneEbitProtocol_physical_output (ρ : Matrix SystemIndex SystemIndex ℂ) :
    oneEbitProtocol.apply (matrixResourceEmbedding * ρ * matrixResourceEmbedding.conjTranspose) =
      physicalClassicalChannel ρ := by
  rw [oneEbitProtocol_apply, Finset.sum_comm]
  have hs (j : Fin 4) :
      (∑ m : Fin 4, Matrix.trace ((finiteBranchPair m j).productEffect *
        (matrixResourceEmbedding * ρ * matrixResourceEmbedding.conjTranspose)) •
          sharedLabelProjector j) =
      Matrix.trace (matrixCoarseEffect j *
        (matrixResourceEmbedding * ρ * matrixResourceEmbedding.conjTranspose)) •
          sharedLabelProjector j := by
    rw [matrixCoarseEffect, Matrix.sum_mul, Matrix.trace_sum, Finset.sum_smul]
  simp_rw [hs]
  exact finite_tree_exact_shared_classical_channel ρ

def occurrenceLeafEquiv : Fin oneEbitFiniteTree.terminalBraPairs.length ≃
    FiniteLocalProtocol.leafIndex oneEbitProtocol :=
  PhysicalUpper.occurrenceEquiv.trans leafLabelEquiv.symm

theorem occurrenceLeaf_report (i : Fin oneEbitFiniteTree.terminalBraPairs.length) :
    (leafLabelEquiv (occurrenceLeafEquiv i)).2 = PhysicalUpper.occurrenceReport i := by
  exact congrArg Prod.snd (leafLabelEquiv.apply_symm_apply (PhysicalUpper.occurrenceEquiv i))

theorem occurrenceLeaf_effect (i : Fin oneEbitFiniteTree.terminalBraPairs.length) :
    (FiniteLocalProtocol.leafKraus oneEbitProtocol (occurrenceLeafEquiv i)).conjTranspose *
      FiniteLocalProtocol.leafKraus oneEbitProtocol (occurrenceLeafEquiv i) =
        (oneEbitFiniteTree.terminalBraPairs.get i).productEffect := by
  rw [PhysicalUpper.occurrence_terminal_pair]
  exact protocolLeaf_effect (PhysicalUpper.occurrenceEquiv i).1
    (PhysicalUpper.occurrenceEquiv i).2

end QuantumProver.ElegantJointMeasurement.HilbertFiniteEJMProtocol

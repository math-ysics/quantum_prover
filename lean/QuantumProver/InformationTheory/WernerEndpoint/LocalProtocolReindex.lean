import QuantumProver.InformationTheory.WernerEndpoint.OperationalEndpointCost
import QuantumProver.InformationTheory.QuantumEntropy.EntropyReindex

noncomputable section

namespace QuantumProver.WernerEndpoint.OperationalEndpointCost.OneWayLocalInstrument

open scoped BigOperators Kronecker

private theorem sum_submatrix {H I J I' J' : Type*} [Fintype H]
    (M : H → Matrix I J ℂ) (r : I' → I) (c : J' → J) :
    (∑ h, (M h).submatrix r c) = (∑ h, M h).submatrix r c := by
  ext i j
  simp only [Matrix.sum_apply, Matrix.submatrix_apply]

section LocalSpaces

variable {H A₀ B₀ A₁ B₁ A₀' B₀' A₁' B₁' : Type*}
  [Fintype H] [Fintype A₀] [Fintype B₀] [Fintype A₁] [Fintype B₁]
  [Fintype A₀'] [Fintype B₀'] [Fintype A₁'] [Fintype B₁']
  [DecidableEq A₀] [DecidableEq B₀] [DecidableEq A₀'] [DecidableEq B₀']

def localReindex (I : OneWayLocalInstrument H A₀ B₀ A₁ B₁)
    (eA₀ : A₀' ≃ A₀) (eB₀ : B₀' ≃ B₀) (eA₁ : A₁' ≃ A₁) (eB₁ : B₁' ≃ B₁) :
    OneWayLocalInstrument H A₀' B₀' A₁' B₁' where
  alice := fun h => (I.alice h).submatrix eA₁ eA₀
  bob := fun h => (I.bob h).submatrix eB₁ eB₀
  alice_complete := by
    simp only [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv]
    rw [sum_submatrix, I.alice_complete, Matrix.submatrix_one_equiv]
  bob_isometry := by
    intro h
    simp only [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv,
      I.bob_isometry, Matrix.submatrix_one_equiv]

@[simp] theorem localReindex_alice (I : OneWayLocalInstrument H A₀ B₀ A₁ B₁)
    (eA₀ : A₀' ≃ A₀) (eB₀ : B₀' ≃ B₀) (eA₁ : A₁' ≃ A₁) (eB₁ : B₁' ≃ B₁)
    (h : H) :
    (I.localReindex eA₀ eB₀ eA₁ eB₁).alice h = (I.alice h).submatrix eA₁ eA₀ := rfl

@[simp] theorem localReindex_bob (I : OneWayLocalInstrument H A₀ B₀ A₁ B₁)
    (eA₀ : A₀' ≃ A₀) (eB₀ : B₀' ≃ B₀) (eA₁ : A₁' ≃ A₁) (eB₁ : B₁' ≃ B₁)
    (h : H) :
    (I.localReindex eA₀ eB₀ eA₁ eB₁).bob h = (I.bob h).submatrix eB₁ eB₀ := rfl

theorem localReindex_branch (I : OneWayLocalInstrument H A₀ B₀ A₁ B₁)
    (eA₀ : A₀' ≃ A₀) (eB₀ : B₀' ≃ B₀) (eA₁ : A₁' ≃ A₁) (eB₁ : B₁' ≃ B₁)
    (h : H) :
    (I.localReindex eA₀ eB₀ eA₁ eB₁).branch h =
      (I.branch h).submatrix (eA₁.prodCongr eB₁) (eA₀.prodCongr eB₀) := by
  ext ab cd
  rfl

theorem localReindex_apply (I : OneWayLocalInstrument H A₀ B₀ A₁ B₁)
    (eA₀ : A₀' ≃ A₀) (eB₀ : B₀' ≃ B₀) (eA₁ : A₁' ≃ A₁) (eB₁ : B₁' ≃ B₁)
    (ρ : Matrix (A₀ × B₀) (A₀ × B₀) ℂ) :
    (I.localReindex eA₀ eB₀ eA₁ eB₁).apply
      (ρ.submatrix (eA₀.prodCongr eB₀) (eA₀.prodCongr eB₀)) =
        (I.apply ρ).submatrix (eA₁.prodCongr eB₁) (eA₁.prodCongr eB₁) := by
  unfold apply
  simp_rw [localReindex_branch, Matrix.conjTranspose_submatrix,
    Matrix.submatrix_mul_equiv]
  exact sum_submatrix _ _ _

theorem vectorNormSq_equiv {X X' : Type*} [Fintype X] [Fintype X']
    (e : X' ≃ X) (v : X → ℂ) : vectorNormSq (v ∘ e) = vectorNormSq v := by
  exact e.sum_comp (fun x => Complex.normSq (v x))

theorem pureDensity_submatrix_equiv {X X' : Type*} (e : X' ≃ X) (v : X → ℂ) :
    pureDensity (v ∘ e) = (pureDensity v).submatrix e e := rfl

theorem localReindex_apply_pureDensity (I : OneWayLocalInstrument H A₀ B₀ A₁ B₁)
    (eA₀ : A₀' ≃ A₀) (eB₀ : B₀' ≃ B₀) (eA₁ : A₁' ≃ A₁) (eB₁ : B₁' ≃ B₁)
    (v : A₀ × B₀ → ℂ) :
    (I.localReindex eA₀ eB₀ eA₁ eB₁).apply
      (pureDensity (v ∘ (eA₀.prodCongr eB₀))) =
        (I.apply (pureDensity v)).submatrix (eA₁.prodCongr eB₁) (eA₁.prodCongr eB₁) := by
  rw [pureDensity_submatrix_equiv]
  exact localReindex_apply I eA₀ eB₀ eA₁ eB₁ _

end LocalSpaces

section FiniteCoordinates

variable {H A₀ B₀ A₁ B₁ : Type*}
  [Fintype H] [Fintype A₀] [Fintype B₀] [Fintype A₁] [Fintype B₁]
  [DecidableEq A₀] [DecidableEq B₀]

def toFin (I : OneWayLocalInstrument H A₀ B₀ A₁ B₁) :
    OneWayLocalInstrument (Fin (Fintype.card H))
      (Fin (Fintype.card A₀)) (Fin (Fintype.card B₀))
      (Fin (Fintype.card A₁)) (Fin (Fintype.card B₁)) :=
  (I.localReindex (Fintype.equivFin A₀).symm (Fintype.equivFin B₀).symm
    (Fintype.equivFin A₁).symm (Fintype.equivFin B₁).symm).reindex
      (Fintype.equivFin H).symm

theorem toFin_apply (I : OneWayLocalInstrument H A₀ B₀ A₁ B₁)
    (ρ : Matrix (A₀ × B₀) (A₀ × B₀) ℂ) :
    I.toFin.apply (ρ.submatrix
      ((Fintype.equivFin A₀).symm.prodCongr (Fintype.equivFin B₀).symm)
      ((Fintype.equivFin A₀).symm.prodCongr (Fintype.equivFin B₀).symm)) =
        (I.apply ρ).submatrix
          ((Fintype.equivFin A₁).symm.prodCongr (Fintype.equivFin B₁).symm)
          ((Fintype.equivFin A₁).symm.prodCongr (Fintype.equivFin B₁).symm) := by
  unfold toFin
  rw [reindex_apply]
  exact localReindex_apply I _ _ _ _ ρ

def toFiniteLocalProtocolOfFintype (I : OneWayLocalInstrument H A₀ B₀ A₁ B₁) :
    FiniteLocalProtocol (Fintype.card A₁) (Fintype.card B₁)
      (Fintype.card A₀) (Fintype.card B₀) :=
  I.toFin.toFiniteLocalProtocol

theorem toFiniteLocalProtocolOfFintype_apply
    (I : OneWayLocalInstrument H A₀ B₀ A₁ B₁)
    (ρ : Matrix (A₀ × B₀) (A₀ × B₀) ℂ) :
    I.toFiniteLocalProtocolOfFintype.apply (ρ.submatrix
      ((Fintype.equivFin A₀).symm.prodCongr (Fintype.equivFin B₀).symm)
      ((Fintype.equivFin A₀).symm.prodCongr (Fintype.equivFin B₀).symm)) =
        (I.apply ρ).submatrix
          ((Fintype.equivFin A₁).symm.prodCongr (Fintype.equivFin B₁).symm)
          ((Fintype.equivFin A₁).symm.prodCongr (Fintype.equivFin B₁).symm) := by
  rw [toFiniteLocalProtocolOfFintype, toFiniteLocalProtocol_apply]
  exact toFin_apply I ρ

theorem toFiniteLocalProtocolOfFintype_apply_pureDensity
    (I : OneWayLocalInstrument H A₀ B₀ A₁ B₁) (v : A₀ × B₀ → ℂ) :
    I.toFiniteLocalProtocolOfFintype.apply
      (pureDensity (v ∘
        ((Fintype.equivFin A₀).symm.prodCongr (Fintype.equivFin B₀).symm))) =
        (I.apply (pureDensity v)).submatrix
          ((Fintype.equivFin A₁).symm.prodCongr (Fintype.equivFin B₁).symm)
          ((Fintype.equivFin A₁).symm.prodCongr (Fintype.equivFin B₁).symm) := by
  rw [pureDensity_submatrix_equiv]
  exact toFiniteLocalProtocolOfFintype_apply I _

theorem exists_finiteLocalProtocol_reindexed
    (I : OneWayLocalInstrument H A₀ B₀ A₁ B₁) :
    ∃ T : FiniteLocalProtocol (Fintype.card A₁) (Fintype.card B₁)
        (Fintype.card A₀) (Fintype.card B₀),
      ∀ ρ : Matrix (A₀ × B₀) (A₀ × B₀) ℂ,
        T.apply (ρ.submatrix
          ((Fintype.equivFin A₀).symm.prodCongr (Fintype.equivFin B₀).symm)
          ((Fintype.equivFin A₀).symm.prodCongr (Fintype.equivFin B₀).symm)) =
            (I.apply ρ).submatrix
              ((Fintype.equivFin A₁).symm.prodCongr (Fintype.equivFin B₁).symm)
              ((Fintype.equivFin A₁).symm.prodCongr (Fintype.equivFin B₁).symm) :=
  ⟨I.toFiniteLocalProtocolOfFintype, toFiniteLocalProtocolOfFintype_apply I⟩

end FiniteCoordinates

end QuantumProver.WernerEndpoint.OperationalEndpointCost.OneWayLocalInstrument

namespace QuantumProver.WernerEndpoint.OperationalEndpointCost.OneWayLocalInstrument

open scoped BigOperators ComplexOrder

section PartialTraces

variable {A B A' B' : Type*} [Fintype A] [Fintype B] [Fintype A'] [Fintype B']

omit [Fintype A] [Fintype A'] in

theorem partialTraceLeft_submatrix_prodEquiv (eA : A' ≃ A) (eB : B' ≃ B)
    (ρ : Matrix (A × B) (A × B) ℂ) :
    partialTraceLeft (ρ.submatrix (eA.prodCongr eB) (eA.prodCongr eB)) =
      (partialTraceLeft ρ).submatrix eA eA := by
  ext a c
  exact eB.sum_comp (fun b => ρ (eA a, b) (eA c, b))

omit [Fintype B] [Fintype B'] in

theorem partialTraceRight_submatrix_prodEquiv (eA : A' ≃ A) (eB : B' ≃ B)
    (ρ : Matrix (A × B) (A × B) ℂ) :
    partialTraceRight (ρ.submatrix (eA.prodCongr eB) (eA.prodCongr eB)) =
      (partialTraceRight ρ).submatrix eB eB := by
  ext b d
  exact eA.sum_comp (fun a => ρ (a, eB b) (a, eB d))

end PartialTraces

theorem vonNeumannEntropyBits_submatrix_equiv {X X' : Type*}
    [Fintype X] [Fintype X'] [DecidableEq X] [DecidableEq X']
    (e : X' ≃ X) {ρ : Matrix X X ℂ} (hρ : ρ.IsHermitian) :
    AntisymmetricEntropyCost.vonNeumannEntropyBits (ρ.submatrix e e) =
      AntisymmetricEntropyCost.vonNeumannEntropyBits ρ := by
  rw [AntisymmetricEntropyCost.vonNeumannEntropyBits_eq_quantumEntropyBits,
    AntisymmetricEntropyCost.vonNeumannEntropyBits_eq_quantumEntropyBits]
  simpa only [Matrix.reindex_apply, Equiv.symm_symm] using
    QuantumProver.QuantumEntropy.entropyBits_reindex e.symm hρ

section PureMarginals

variable {A B A' B' : Type*} [Fintype A] [Fintype B] [Fintype A'] [Fintype B']
  [DecidableEq A] [DecidableEq B] [DecidableEq A'] [DecidableEq B']

theorem pure_marginalLeft_entropy_prodEquiv (eA : A' ≃ A) (eB : B' ≃ B)
    (ψ : A × B → ℂ) :
    AntisymmetricEntropyCost.vonNeumannEntropyBits
      (partialTraceLeft (pureDensity (ψ ∘ (eA.prodCongr eB)))) =
        AntisymmetricEntropyCost.vonNeumannEntropyBits (partialTraceLeft (pureDensity ψ)) := by
  rw [pureDensity_submatrix_equiv, partialTraceLeft_submatrix_prodEquiv]
  exact vonNeumannEntropyBits_submatrix_equiv eA
    (partialTraceLeft_posSemidef _ (pureDensity_posSemidef ψ)).isHermitian

theorem pure_marginalRight_entropy_prodEquiv (eA : A' ≃ A) (eB : B' ≃ B)
    (ψ : A × B → ℂ) :
    AntisymmetricEntropyCost.vonNeumannEntropyBits
      (partialTraceRight (pureDensity (ψ ∘ (eA.prodCongr eB)))) =
        AntisymmetricEntropyCost.vonNeumannEntropyBits (partialTraceRight (pureDensity ψ)) := by
  rw [pureDensity_submatrix_equiv, partialTraceRight_submatrix_prodEquiv]
  exact vonNeumannEntropyBits_submatrix_equiv eB
    (partialTraceRight_posSemidef _ (pureDensity_posSemidef ψ)).isHermitian

end PureMarginals

end QuantumProver.WernerEndpoint.OperationalEndpointCost.OneWayLocalInstrument

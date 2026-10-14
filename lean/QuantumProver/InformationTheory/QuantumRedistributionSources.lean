import QuantumProver.InformationTheory.QuantumRedistributionEntropy
import QuantumProver.InformationTheory.ConditionalTypicalSmoothing
import QuantumProver.InformationTheory.DepolarizingSquashedEntanglement.BCYPurification

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 5000

noncomputable section

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Kronecker

namespace QuantumProver.QuantumRedistributionSources

open QuantumProver.QuantumEntropy QuantumProver.QuantumRedistributionEntropy
open QuantumProver.DepolarizingSquashedEntanglement (Density)
open QuantumProver.DepolarizingSquashedEntanglement.BCYRelativeEntropy
open QuantumProver.SuperchannelDiscrimination.TensorEntropy

variable {A B E C : Type*} [Fintype A] [Fintype B] [Fintype E] [Fintype C]
  [DecidableEq A] [DecidableEq B] [DecidableEq E] [DecidableEq C]

def sourceBAC (ψ : PhysicalIndex A B E C → ℂ) :
    Matrix (B × (A × C)) (B × (A × C)) ℂ :=
  Matrix.reindex (Equiv.prodComm (A × C) B) (Equiv.prodComm (A × C) B)
    (reducedABC ψ)

def sourceBAE (ψ : PhysicalIndex A B E C → ℂ) :
    Matrix (B × (A × E)) (B × (A × E)) ℂ :=
  Matrix.reindex (Equiv.prodComm (A × E) B) (Equiv.prodComm (A × E) B)
    (reducedBAE ψ)

omit [Fintype A] [Fintype B] [Fintype C]
  [DecidableEq A] [DecidableEq B] [DecidableEq E] [DecidableEq C] in
theorem sourceBAC_apply (ψ : PhysicalIndex A B E C → ℂ)
    (b b' : B) (a a' : A) (c c' : C) :
    sourceBAC ψ (b,(a,c)) (b',(a',c')) =
      ∑ e : E, ψ (((a,b),e),c) * star (ψ (((a',b'),e),c')) := rfl

omit [Fintype A] [Fintype B] [Fintype E]
  [DecidableEq A] [DecidableEq B] [DecidableEq E] [DecidableEq C] in
theorem sourceBAE_apply (ψ : PhysicalIndex A B E C → ℂ)
    (b b' : B) (a a' : A) (e e' : E) :
    sourceBAE ψ (b,(a,e)) (b',(a',e')) =
      ∑ c : C, ψ (((a,b),e),c) * star (ψ (((a',b'),e'),c)) := rfl

private theorem reindex_isDensity {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (e : I ≃ J)
    {R : Matrix I I ℂ} (hR : IsDensity R) : IsDensity (Matrix.reindex e e R) :=
  ⟨hR.1.submatrix e.symm, (trace_reindex e R).trans hR.2⟩

theorem sourceBAC_isDensity (ψ : PhysicalIndex A B E C → ℂ) (hψ : normSq ψ = 1) :
    IsDensity (sourceBAC ψ) :=
  reindex_isDensity _ (partialTraceRight_isDensity (pureChart_isDensity _ ψ hψ))

theorem sourceBAE_isDensity (ψ : PhysicalIndex A B E C → ℂ) (hψ : normSq ψ = 1) :
    IsDensity (sourceBAE ψ) :=
  reindex_isDensity _ (partialTraceRight_isDensity (pureChart_isDensity _ ψ hψ))

omit [Fintype B] [DecidableEq A] [DecidableEq B] [DecidableEq E] [DecidableEq C] in

theorem sourceBAC_sender (ψ : PhysicalIndex A B E C → ℂ) :
    partialTrace_right (sourceBAC ψ) = reducedB ψ := by
  ext b b'
  simp only [sourceBAC, reducedABC, reducedB, reducedBE, partialTrace_right,
    transportKet, pureMatrix,
    QuantumProver.ConditionalEntropy.ContinuousLocalInstrument.pureDensity,
    Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.prodComm_symm,
    Equiv.prodComm_apply, acBEChart, beACChart, Fintype.sum_prod_type]
  calc
    _ = ∑ a : A, ∑ e : E, ∑ c : C,
        ψ (((a,b),e),c) * star (ψ (((a,b'),e),c)) := by
      apply Finset.sum_congr rfl
      intro a ha
      exact Finset.sum_comm
    _ = _ := Finset.sum_comm

omit [Fintype B] [DecidableEq A] [DecidableEq B] [DecidableEq E] [DecidableEq C] in
theorem sourceBAE_sender (ψ : PhysicalIndex A B E C → ℂ) :
    partialTrace_right (sourceBAE ψ) = reducedB ψ := by
  ext b b'
  simp only [sourceBAE, reducedBAE, reducedB, reducedBE, partialTrace_right,
    transportKet, pureMatrix,
    QuantumProver.ConditionalEntropy.ContinuousLocalInstrument.pureDensity,
    Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.prodComm_symm,
    Equiv.prodComm_apply, aeBCChart, beACChart, Fintype.sum_prod_type]
  exact Finset.sum_comm

omit [Fintype B] [DecidableEq A] [DecidableEq B] [DecidableEq E] [DecidableEq C] in
theorem source_sender_eq (ψ : PhysicalIndex A B E C → ℂ) :
    partialTrace_right (sourceBAC ψ) = partialTrace_right (sourceBAE ψ) := by
  rw [sourceBAC_sender, sourceBAE_sender]

omit [Fintype A] [Fintype C]
  [DecidableEq A] [DecidableEq B] [DecidableEq E] [DecidableEq C] in
theorem sourceBAC_reference (ψ : PhysicalIndex A B E C → ℂ) :
    partialTrace_left (sourceBAC ψ) = reducedAC ψ := by
  change partialTrace_right (reducedABC ψ) = reducedAC ψ
  exact reducedAC_from_ABC ψ

omit [Fintype A] [Fintype E]
  [DecidableEq A] [DecidableEq B] [DecidableEq E] [DecidableEq C] in
theorem sourceBAE_reference (ψ : PhysicalIndex A B E C → ℂ) :
    partialTrace_left (sourceBAE ψ) = reducedAE ψ := by
  change partialTrace_right (reducedBAE ψ) = reducedAE ψ
  exact reducedAE_from_BAE ψ

theorem sourceBAC_conditional_nats (ψ : PhysicalIndex A B E C → ℂ) :
    entropyNats (sourceBAC ψ) - entropyNats (partialTrace_left (sourceBAC ψ)) =
      conditionalBACNat ψ := by
  rw [sourceBAC_reference]
  unfold sourceBAC conditionalBACNat
  have hH : (reducedABC ψ).IsHermitian := (partialTraceRight_posSemidef
    (QuantumProver.ConditionalEntropy.ContinuousLocalInstrument.pureDensity_posSemidef _)).1
  rw [entropyNats_reindex _ hH]

theorem sourceBAE_conditional_nats (ψ : PhysicalIndex A B E C → ℂ) :
    entropyNats (sourceBAE ψ) - entropyNats (partialTrace_left (sourceBAE ψ)) =
      conditionalBAENat ψ := by
  rw [sourceBAE_reference]
  unfold sourceBAE conditionalBAENat
  have hH : (reducedBAE ψ).IsHermitian := (partialTraceRight_posSemidef
    (QuantumProver.ConditionalEntropy.ContinuousLocalInstrument.pureDensity_posSemidef _)).1
  rw [entropyNats_reindex _ hH]

theorem sourceBAC_conditional_bits_nats (ψ : PhysicalIndex A B E C → ℂ) :
    QuantumProver.ConditionalEntropy.conditionalEntropyBits (sourceBAC ψ) * Real.log 2 =
      conditionalBACNat ψ := (conditionalBACNat_eq_matrix ψ).symm

theorem sourceBAE_conditional_bits_nats (ψ : PhysicalIndex A B E C → ℂ) :
    QuantumProver.ConditionalEntropy.conditionalEntropyBits (sourceBAE ψ) * Real.log 2 =
      conditionalBAENat ψ := (conditionalBAENat_eq_matrix ψ).symm

def spectatorGrouping (X Y Z : Type*) (n : ℕ) :
    TensorIndex X n × TensorIndex (Y × Z) n ≃
      TensorIndex X n × (TensorIndex Y n × TensorIndex Z n) :=
  Equiv.prodCongr (Equiv.refl _) (QuantumProver.ConditionalTypicalSmoothing.powerGrouping Y Z n)

theorem partialTrace_right_reindex_spectator {X Y Z : Type*}
    [Fintype X] [Fintype Y] [Fintype Z]
    [DecidableEq X] [DecidableEq Y] [DecidableEq Z]
    (e : Y ≃ Z) (R : Matrix (X × Y) (X × Y) ℂ) :
    partialTrace_right
      (Matrix.reindex (Equiv.prodCongr (Equiv.refl X) e)
        (Equiv.prodCongr (Equiv.refl X) e) R) = partialTrace_right R := by
  ext x x'
  exact e.symm.sum_comp (fun y => R (x,y) (x',y))

theorem partialTrace_left_reindex_spectator {X Y Z : Type*}
    [Fintype X] [Fintype Y] [Fintype Z]
    [DecidableEq X] [DecidableEq Y] [DecidableEq Z]
    (e : Y ≃ Z) (R : Matrix (X × Y) (X × Y) ℂ) :
    partialTrace_left
      (Matrix.reindex (Equiv.prodCongr (Equiv.refl X) e)
        (Equiv.prodCongr (Equiv.refl X) e) R) =
      Matrix.reindex e e (partialTrace_left R) := by
  ext y y'
  rfl

open QuantumProver.DepolarizingSquashedEntanglement.BCYPurification

def sourceBACCopies (ρ : Density (A × (B × E))) (n : ℕ) :
    Matrix (CopyIndex B n × (CopyIndex A n × CopyIndex (A × (B × E)) n))
      (CopyIndex B n × (CopyIndex A n × CopyIndex (A × (B × E)) n)) ℂ :=
  sourceBAC (sourceKetCopies ρ n)

def sourceBAECopies (ρ : Density (A × (B × E))) (n : ℕ) :
    Matrix (CopyIndex B n × (CopyIndex A n × CopyIndex E n))
      (CopyIndex B n × (CopyIndex A n × CopyIndex E n)) ℂ :=
  sourceBAE (sourceKetCopies ρ n)

private theorem sum_cross_product {I J : Type*} [Fintype I] [Fintype J]
    (f f' : I → ℂ) (g g' : J → ℂ) :
    (∑ i, ∑ j, (f i * g j) * star (f' i * g' j)) =
      (∑ i, f i * star (f' i)) * (∑ j, g j * star (g' j)) := by
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [star_mul]
  ring

theorem sourceBACCopies_succ_apply (ρ : Density (A × (B × E))) (n : ℕ)
    (b b' : CopyIndex B n) (a a' : CopyIndex A n)
    (c c' : CopyIndex (A × (B × E)) n)
    (j j' : B) (i i' : A) (l l' : A × (B × E)) :
    sourceBACCopies ρ (n+1) ((b,j),((a,i),(c,l))) ((b',j'),((a',i'),(c',l'))) =
      sourceBACCopies ρ n (b,(a,c)) (b',(a',c')) *
        sourceBAC (sourceKet ρ) (j,(i,l)) (j',(i',l')) := by
  change (∑ x : CopyIndex E n × E,
    (sourceKetCopies ρ n (((a,b),x.1),c) * sourceKet ρ (((i,j),x.2),l)) *
      star (sourceKetCopies ρ n (((a',b'),x.1),c') * sourceKet ρ (((i',j'),x.2),l'))) =
    (∑ x : CopyIndex E n,
      sourceKetCopies ρ n (((a,b),x),c) * star (sourceKetCopies ρ n (((a',b'),x),c'))) *
      (∑ x : E, sourceKet ρ (((i,j),x),l) * star (sourceKet ρ (((i',j'),x),l')))
  rw [Fintype.sum_prod_type]
  exact sum_cross_product
    (fun x : CopyIndex E n => sourceKetCopies ρ n (((a,b),x),c))
    (fun x : CopyIndex E n => sourceKetCopies ρ n (((a',b'),x),c'))
    (fun x : E => sourceKet ρ (((i,j),x),l))
    (fun x : E => sourceKet ρ (((i',j'),x),l'))

theorem sourceBAECopies_succ_apply (ρ : Density (A × (B × E))) (n : ℕ)
    (b b' : CopyIndex B n) (a a' : CopyIndex A n) (e e' : CopyIndex E n)
    (j j' : B) (i i' : A) (k k' : E) :
    sourceBAECopies ρ (n+1) ((b,j),((a,i),(e,k))) ((b',j'),((a',i'),(e',k'))) =
      sourceBAECopies ρ n (b,(a,e)) (b',(a',e')) *
        sourceBAE (sourceKet ρ) (j,(i,k)) (j',(i',k')) := by
  change (∑ x : CopyIndex (A × (B × E)) n × (A × (B × E)),
    (sourceKetCopies ρ n (((a,b),e),x.1) * sourceKet ρ (((i,j),k),x.2)) *
      star (sourceKetCopies ρ n (((a',b'),e'),x.1) * sourceKet ρ (((i',j'),k'),x.2))) =
    (∑ x : CopyIndex (A × (B × E)) n,
      sourceKetCopies ρ n (((a,b),e),x) * star (sourceKetCopies ρ n (((a',b'),e'),x))) *
      (∑ x : A × (B × E), sourceKet ρ (((i,j),k),x) * star (sourceKet ρ (((i',j'),k'),x)))
  rw [Fintype.sum_prod_type]
  exact sum_cross_product
    (fun x : CopyIndex (A × (B × E)) n => sourceKetCopies ρ n (((a,b),e),x))
    (fun x : CopyIndex (A × (B × E)) n => sourceKetCopies ρ n (((a',b'),e'),x))
    (fun x : A × (B × E) => sourceKet ρ (((i,j),k),x))
    (fun x : A × (B × E) => sourceKet ρ (((i',j'),k'),x))

theorem sourceBACCopies_eq_groupedPower (ρ : Density (A × (B × E))) (n : ℕ) :
    sourceBACCopies ρ n =
      Matrix.reindex (spectatorGrouping B A (A × (B × E)) n)
        (spectatorGrouping B A (A × (B × E)) n)
        (QuantumProver.ConditionalTypicalSmoothing.groupedPower (sourceBAC (sourceKet ρ)) n) := by
  induction n with
  | zero =>
      ext ⟨b,a,c⟩ ⟨b',a',c'⟩
      cases b; cases a; cases c; cases b'; cases a'; cases c'
      simp [sourceBACCopies, sourceBAC_apply, sourceKetCopies, spectatorGrouping,
        QuantumProver.ConditionalTypicalSmoothing.groupedPower,
        QuantumProver.ConditionalTypicalSmoothing.powerGrouping, tensorPower,
        Matrix.reindex_apply]
  | succ n ih =>
      ext ⟨⟨b,j⟩,⟨⟨a,i⟩,⟨c,l⟩⟩⟩ ⟨⟨b',j'⟩,⟨⟨a',i'⟩,⟨c',l'⟩⟩⟩
      rw [sourceBACCopies_succ_apply, ih]
      rfl

theorem sourceBAECopies_eq_groupedPower (ρ : Density (A × (B × E))) (n : ℕ) :
    sourceBAECopies ρ n =
      Matrix.reindex (spectatorGrouping B A E n) (spectatorGrouping B A E n)
        (QuantumProver.ConditionalTypicalSmoothing.groupedPower (sourceBAE (sourceKet ρ)) n) := by
  induction n with
  | zero =>
      ext ⟨b,a,e⟩ ⟨b',a',e'⟩
      cases b; cases a; cases e; cases b'; cases a'; cases e'
      simp [sourceBAECopies, sourceBAE_apply, sourceKetCopies, spectatorGrouping,
        QuantumProver.ConditionalTypicalSmoothing.groupedPower,
        QuantumProver.ConditionalTypicalSmoothing.powerGrouping, tensorPower,
        Matrix.reindex_apply]
  | succ n ih =>
      ext ⟨⟨b,j⟩,⟨⟨a,i⟩,⟨e,k⟩⟩⟩ ⟨⟨b',j'⟩,⟨⟨a',i'⟩,⟨e',k'⟩⟩⟩
      rw [sourceBAECopies_succ_apply, ih]
      rfl

theorem sourceBACCopies_isDensity (ρ : Density (A × (B × E))) (n : ℕ) :
    IsDensity (sourceBACCopies ρ n) :=
  sourceBAC_isDensity _ (sourceKetCopies_normalized ρ n)

theorem sourceBAECopies_isDensity (ρ : Density (A × (B × E))) (n : ℕ) :
    IsDensity (sourceBAECopies ρ n) :=
  sourceBAE_isDensity _ (sourceKetCopies_normalized ρ n)

theorem sourceBACCopies_sender (ρ : Density (A × (B × E))) (n : ℕ) :
    partialTrace_right (sourceBACCopies ρ n) = tensorPower (reducedB (sourceKet ρ)) n := by
  rw [sourceBACCopies_eq_groupedPower, spectatorGrouping,
    partialTrace_right_reindex_spectator,
    QuantumProver.ConditionalTypicalSmoothing.groupedPower_right_marginal, sourceBAC_sender]

theorem sourceBAECopies_sender (ρ : Density (A × (B × E))) (n : ℕ) :
    partialTrace_right (sourceBAECopies ρ n) = tensorPower (reducedB (sourceKet ρ)) n := by
  rw [sourceBAECopies_eq_groupedPower, spectatorGrouping,
    partialTrace_right_reindex_spectator,
    QuantumProver.ConditionalTypicalSmoothing.groupedPower_right_marginal, sourceBAE_sender]

theorem sourceBACCopies_reference (ρ : Density (A × (B × E))) (n : ℕ) :
    partialTrace_left (sourceBACCopies ρ n) =
      Matrix.reindex (QuantumProver.ConditionalTypicalSmoothing.powerGrouping A (A × (B × E)) n)
        (QuantumProver.ConditionalTypicalSmoothing.powerGrouping A (A × (B × E)) n)
        (tensorPower (reducedAC (sourceKet ρ)) n) := by
  rw [sourceBACCopies_eq_groupedPower, spectatorGrouping,
    partialTrace_left_reindex_spectator,
    QuantumProver.ConditionalTypicalSmoothing.groupedPower_left_marginal, sourceBAC_reference]

theorem sourceBAECopies_reference (ρ : Density (A × (B × E))) (n : ℕ) :
    partialTrace_left (sourceBAECopies ρ n) =
      Matrix.reindex (QuantumProver.ConditionalTypicalSmoothing.powerGrouping A E n)
        (QuantumProver.ConditionalTypicalSmoothing.powerGrouping A E n)
        (tensorPower (reducedAE (sourceKet ρ)) n) := by
  rw [sourceBAECopies_eq_groupedPower, spectatorGrouping,
    partialTrace_left_reindex_spectator,
    QuantumProver.ConditionalTypicalSmoothing.groupedPower_left_marginal, sourceBAE_reference]

end QuantumProver.QuantumRedistributionSources

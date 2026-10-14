import QuantumProver.InformationTheory.DepolarizingSquashedEntanglement.BCYRedistributionCode
import QuantumProver.InformationTheory.ConditionalEntropy.ConditionalRange
import QuantumProver.InformationTheory.SuperchannelDiscrimination.DiamondControl

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

noncomputable section

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker

namespace QuantumProver.DepolarizingSquashedEntanglement.BCYPurification

open BCYRelativeEntropy

variable {A B E C I J : Type*} [Fintype A] [Fintype B] [Fintype E]
  [Fintype C] [Fintype I] [Fintype J]
  [DecidableEq A] [DecidableEq B] [DecidableEq E] [DecidableEq C]
  [DecidableEq I] [DecidableEq J]

def sourceEquiv (A B E : Type*) : (A × (B × E)) ≃ ((A × B) × E) :=
  (Equiv.prodAssoc A B E).symm

def wireEquiv (A B E C : Type*) : (((A × B) × E) × C) ≃ ((A × C) × (B × E)) where
  toFun z := ((z.1.1.1,z.2),(z.1.1.2,z.1.2))
  invFun z := (((z.1.1,z.2.1),z.2.2),z.1.2)
  left_inv := by rintro ⟨⟨⟨a,b⟩,e⟩,c⟩; rfl
  right_inv := by rintro ⟨⟨a,c⟩,⟨b,e⟩⟩; rfl

def sourceMarginal (ρ : Density (A × (B × E))) : Density ((A × B) × E) :=
  densityReindex (sourceEquiv A B E) ρ

def sourceKet (ρ : Density (A × (B × E))) :
    (((A × B) × E) × (A × (B × E))) → ℂ :=
  fun z => (CFC.sqrt ρ.matrix) ((sourceEquiv A B E).symm z.1) z.2

theorem sourceKet_marginal (ρ : Density (A × (B × E))) :
    partialTraceRight (pureDensity (sourceKet ρ)) = (sourceMarginal ρ).matrix := by
  ext ⟨⟨a,b⟩,e⟩ ⟨⟨a',b'⟩,e'⟩
  have h := congrArg (fun R : QMatrix (A × (B × E)) => R (a,(b,e)) (a',(b',e')))
    (QuantumProver.ConditionalEntropy.ConditionalRange.sqrt_grams ρ.positive).1
  simpa only [sourceKet,sourceMarginal,densityReindex,sourceEquiv,Matrix.reindex_apply,
    Matrix.submatrix_apply,
    Equiv.prodAssoc_symm_apply,Equiv.symm_symm,Equiv.prodAssoc_apply,
    partialTraceRight,QuantumProver.WernerEndpoint.partialTraceLeft,pureDensity,
    QuantumProver.WernerEndpoint.pureDensity,QuantumProver.WernerEndpoint.crossDensity,Matrix.mul_apply,
    Matrix.conjTranspose_apply] using h

theorem sourceKet_trace (ρ : Density (A × (B × E))) :
    Matrix.trace (pureDensity (sourceKet ρ)) = 1 := by
  rw [← partialTraceRight_trace,sourceKet_marginal]
  exact (sourceMarginal ρ).trace_one

theorem sourceKet_normalized (ρ : Density (A × (B × E))) :
    IsNormalized (sourceKet ρ) := by
  change QuantumProver.WernerEndpoint.vectorNormSq (sourceKet ρ) = 1
  have h := congrArg Complex.re (sourceKet_trace ρ)
  change (Matrix.trace (QuantumProver.WernerEndpoint.pureDensity (sourceKet ρ))).re = (1 : ℂ).re at h
  simpa only [QuantumProver.WernerEndpoint.pureDensity_trace,Complex.ofReal_re,Complex.one_re] using h

theorem sourcePurifier_nonempty (ρ : Density (A × (B × E))) : Nonempty (A × (B × E)) := by
  classical
  by_contra h
  haveI : IsEmpty (A × (B × E)) := not_nonempty_iff.mp h
  have ht := ρ.trace_one
  simp [Matrix.trace] at ht

def sourceDensity (ρ : Density (A × (B × E))) :
    Density (((A × B) × E) × (A × (B × E))) where
  matrix := pureDensity (sourceKet ρ)
  positive := QuantumProver.WernerEndpoint.pureDensity_posSemidef _
  trace_one := sourceKet_trace ρ

theorem pureDensity_reindex (e : I ≃ J) (ψ : I → ℂ) :
    pureDensity (fun j => ψ (e.symm j)) = Matrix.reindex e e (pureDensity ψ) := by
  ext i j
  rfl

theorem normalized_reindex (e : I ≃ J) (ψ : I → ℂ) (hψ : IsNormalized ψ) :
    IsNormalized (fun j => ψ (e.symm j)) := by
  have ht : Matrix.trace (pureDensity (fun j => ψ (e.symm j))) = 1 := by
    rw [pureDensity_reindex,QuantumProver.QuantumEntropy.trace_reindex]
    change Matrix.trace (QuantumProver.WernerEndpoint.pureDensity ψ) = 1
    rw [QuantumProver.WernerEndpoint.pureDensity_trace]
    change (vectorNormSq ψ : ℂ) = 1
    rw [hψ]
    rfl
  have h := congrArg Complex.re ht
  change QuantumProver.WernerEndpoint.vectorNormSq (fun j => ψ (e.symm j)) = 1
  change (Matrix.trace (QuantumProver.WernerEndpoint.pureDensity _)).re = (1 : ℂ).re at h
  simpa only [QuantumProver.WernerEndpoint.pureDensity_trace,Complex.ofReal_re,Complex.one_re] using h

def sourceWireKet (ρ : Density (A × (B × E))) :
    ((A × (A × (B × E))) × (B × E)) → ℂ :=
  fun z => sourceKet ρ ((wireEquiv A B E (A × (B × E))).symm z)

theorem sourceWireKet_normalized (ρ : Density (A × (B × E))) :
    IsNormalized (sourceWireKet ρ) :=
  normalized_reindex _ _ (sourceKet_normalized ρ)

theorem sourceWireKet_density (ρ : Density (A × (B × E))) :
    pureDensity (sourceWireKet ρ) =
      (densityReindex (wireEquiv A B E (A × (B × E))) (sourceDensity ρ)).matrix :=
  pureDensity_reindex _ _

def sourceKetCopies (ρ : Density (A × (B × E))) : (n : ℕ) →
    (((CopyIndex A n × CopyIndex B n) × CopyIndex E n) ×
      CopyIndex (A × (B × E)) n) → ℂ
  | 0 => fun _ => 1
  | n+1 => fun z =>
      sourceKetCopies ρ n (((z.1.1.1.1,z.1.1.2.1),z.1.2.1),z.2.1) *
        sourceKet ρ (((z.1.1.1.2,z.1.1.2.2),z.1.2.2),z.2.2)

def sourceCopiesMarginal (ρ : Density (A × (B × E))) (n : ℕ) :
    Density ((CopyIndex A n × CopyIndex B n) × CopyIndex E n) :=
  densityReindex (sourceEquiv (CopyIndex A n) (CopyIndex B n) (CopyIndex E n))
    (BCYRedistributionCode.tripleCopies ρ n)

theorem sourceKetCopies_marginal (ρ : Density (A × (B × E))) (n : ℕ) :
    partialTraceRight (pureDensity (sourceKetCopies ρ n)) = (sourceCopiesMarginal ρ n).matrix := by
  induction n with
  | zero =>
      ext ⟨⟨a,b⟩,e⟩ ⟨⟨a',b'⟩,e'⟩
      cases a; cases b; cases e; cases a'; cases b'; cases e'
      simp [partialTraceRight,QuantumProver.WernerEndpoint.partialTraceLeft,pureDensity,
        QuantumProver.WernerEndpoint.pureDensity,QuantumProver.WernerEndpoint.crossDensity,sourceKetCopies,
        sourceCopiesMarginal,BCYRedistributionCode.tripleCopies,tensorCopies,
        matrixTensorPowerDensity,densityReindex,sourceEquiv,copyGrouping,
        QuantumProver.SuperchannelDiscrimination.TensorEntropy.tensorPower]
  | succ n ih =>
      ext ⟨⟨⟨a,i⟩,⟨b,j⟩⟩,⟨e,k⟩⟩ ⟨⟨⟨a',i'⟩,⟨b',j'⟩⟩,⟨e',k'⟩⟩
      have hi := congrArg (fun R : QMatrix ((CopyIndex A n × CopyIndex B n) × CopyIndex E n) =>
        R ((a,b),e) ((a',b'),e')) ih
      have hs := congrArg (fun R : QMatrix ((A × B) × E) => R ((i,j),k) ((i',j'),k'))
        (sourceKet_marginal ρ)
      change (∑ c : CopyIndex (A × (B × E)) n × (A × (B × E)),
        (sourceKetCopies ρ n (((a,b),e),c.1) * sourceKet ρ (((i,j),k),c.2)) *
          star (sourceKetCopies ρ n (((a',b'),e'),c.1) * sourceKet ρ (((i',j'),k'),c.2))) =
        (BCYRedistributionCode.tripleCopies ρ n).matrix (a,(b,e)) (a',(b',e')) *
          ρ.matrix (i,(j,k)) (i',(j',k'))
      rw [Fintype.sum_prod_type]
      simp only [star_mul]
      simp only [partialTraceRight,QuantumProver.WernerEndpoint.partialTraceLeft,pureDensity,
        QuantumProver.WernerEndpoint.pureDensity,QuantumProver.WernerEndpoint.crossDensity] at hi hs
      calc
        _ = (∑ c, sourceKetCopies ρ n (((a,b),e),c) *
              star (sourceKetCopies ρ n (((a',b'),e'),c))) *
            (∑ c, sourceKet ρ (((i,j),k),c) * star (sourceKet ρ (((i',j'),k'),c))) := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro c hc
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro d hd
          ring
        _ = _ := by rw [hi,hs]; rfl

theorem sourceKetCopies_trace (ρ : Density (A × (B × E))) (n : ℕ) :
    Matrix.trace (pureDensity (sourceKetCopies ρ n)) = 1 := by
  rw [← partialTraceRight_trace,sourceKetCopies_marginal]
  exact (sourceCopiesMarginal ρ n).trace_one

theorem sourceKetCopies_physical_marginal (ρ : Density (A × (B × E))) (n : ℕ) :
    Matrix.reindex
      (sourceEquiv (CopyIndex A n) (CopyIndex B n) (CopyIndex E n)).symm
      (sourceEquiv (CopyIndex A n) (CopyIndex B n) (CopyIndex E n)).symm
      (partialTraceRight (pureDensity (sourceKetCopies ρ n))) =
        (BCYRedistributionCode.tripleCopies ρ n).matrix := by
  rw [sourceKetCopies_marginal]
  ext i j
  rfl

theorem sourceCopiesPurifier_nonempty (ρ : Density (A × (B × E))) (n : ℕ) :
    Nonempty (CopyIndex (A × (B × E)) n) := by
  induction n with
  | zero => exact ⟨PUnit.unit⟩
  | succ n ih => exact ⟨(Classical.choice ih,Classical.choice (sourcePurifier_nonempty ρ))⟩

theorem sourceKetCopies_normalized (ρ : Density (A × (B × E))) (n : ℕ) :
    IsNormalized (sourceKetCopies ρ n) := by
  change QuantumProver.WernerEndpoint.vectorNormSq (sourceKetCopies ρ n) = 1
  have h := congrArg Complex.re (sourceKetCopies_trace ρ n)
  change (Matrix.trace (QuantumProver.WernerEndpoint.pureDensity _)).re = (1 : ℂ).re at h
  simpa only [QuantumProver.WernerEndpoint.pureDensity_trace,Complex.ofReal_re,Complex.one_re] using h

def sourceCopiesDensity (ρ : Density (A × (B × E))) (n : ℕ) :
    Density (((CopyIndex A n × CopyIndex B n) × CopyIndex E n) ×
      CopyIndex (A × (B × E)) n) where
  matrix := pureDensity (sourceKetCopies ρ n)
  positive := QuantumProver.WernerEndpoint.pureDensity_posSemidef _
  trace_one := sourceKetCopies_trace ρ n

def sourceCopiesWireKet (ρ : Density (A × (B × E))) (n : ℕ) :
    ((CopyIndex A n × CopyIndex (A × (B × E)) n) × (CopyIndex B n × CopyIndex E n)) → ℂ :=
  fun z => sourceKetCopies ρ n
    ((wireEquiv (CopyIndex A n) (CopyIndex B n) (CopyIndex E n)
      (CopyIndex (A × (B × E)) n)).symm z)

theorem sourceCopiesWireKet_normalized (ρ : Density (A × (B × E))) (n : ℕ) :
    IsNormalized (sourceCopiesWireKet ρ n) := by
  classical
  exact normalized_reindex _ _ (sourceKetCopies_normalized ρ n)

theorem sourceCopiesWireKet_density (ρ : Density (A × (B × E))) (n : ℕ) :
    pureDensity (sourceCopiesWireKet ρ n) =
      Matrix.reindex
        (wireEquiv (CopyIndex A n) (CopyIndex B n) (CopyIndex E n) (CopyIndex (A × (B × E)) n))
        (wireEquiv (CopyIndex A n) (CopyIndex B n) (CopyIndex E n) (CopyIndex (A × (B × E)) n))
        (sourceCopiesDensity ρ n).matrix := by
  classical
  exact pureDensity_reindex _ _

theorem traceDistance_reindex (e : I ≃ J) (R S : QMatrix I) :
    QuantumProver.ConditionalEntropy.traceDistance (Matrix.reindex e e R) (Matrix.reindex e e S) =
      QuantumProver.ConditionalEntropy.traceDistance R S := by
  unfold QuantumProver.ConditionalEntropy.traceDistance
  congr 1
  change QuantumProver.SuperchannelDiscrimination.EffectPerturbation.traceNorm
    ((R-S).submatrix e.symm e.symm) = _
  exact QuantumProver.SuperchannelDiscrimination.DiamondControl.nuclearNorm_submatrix_equiv e.symm (R-S)

theorem sourceMarginal_traceDistance (ρ σ : Density (A × (B × E))) :
    QuantumProver.ConditionalEntropy.traceDistance
      (partialTraceRight (pureDensity (sourceKet ρ)))
      (partialTraceRight (pureDensity (sourceKet σ))) =
      QuantumProver.ConditionalEntropy.traceDistance ρ.matrix σ.matrix := by
  rw [sourceKet_marginal,sourceKet_marginal]
  exact traceDistance_reindex _ _ _

theorem sourceCopyMarginal_traceDistance (ρ σ : Density (A × (B × E))) (n : ℕ) :
    QuantumProver.ConditionalEntropy.traceDistance
      (partialTraceRight (pureDensity (sourceKetCopies ρ n)))
      (partialTraceRight (pureDensity (sourceKetCopies σ n))) =
      QuantumProver.ConditionalEntropy.traceDistance (BCYRedistributionCode.tripleCopies ρ n).matrix
        (BCYRedistributionCode.tripleCopies σ n).matrix := by
  rw [sourceKetCopies_marginal,sourceKetCopies_marginal]
  exact traceDistance_reindex _ _ _

end QuantumProver.DepolarizingSquashedEntanglement.BCYPurification

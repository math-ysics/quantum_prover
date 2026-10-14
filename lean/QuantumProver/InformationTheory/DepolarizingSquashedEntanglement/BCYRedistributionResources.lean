import QuantumProver.InformationTheory.DepolarizingSquashedEntanglement.BCYPurification

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker

namespace QuantumProver.DepolarizingSquashedEntanglement.BCYRedistributionResources

open BCYRelativeEntropy BCYNonlockability

variable {R S D T U A B E : Type*}
  [Fintype R] [Fintype S] [Fintype D] [Fintype T] [Fintype U]
  [Fintype A] [Fintype B] [Fintype E]
  [DecidableEq R] [DecidableEq S] [DecidableEq D] [DecidableEq T]
  [DecidableEq U] [DecidableEq A] [DecidableEq B] [DecidableEq E]

def discardReferenceLast (M : QMatrix ((R × D) × T)) : QMatrix (R × T) :=
  fun x y => ∑ d, M ((x.1,d),x.2) ((y.1,d),y.2)

def discardReferenceEquiv (R D T : Type*) : ((R × D) × T) ≃ ((R × T) × D) where
  toFun z := ((z.1.1,z.2),z.1.2)
  invFun z := ((z.1.1,z.2),z.1.2)
  left_inv := by rintro ⟨⟨r,d⟩,t⟩; rfl
  right_inv := by rintro ⟨⟨r,t⟩,d⟩; rfl

theorem discardReferenceLast_eq_partialTrace (M : QMatrix ((R × D) × T)) :
    discardReferenceLast M = partialTraceRight
      (Matrix.reindex (discardReferenceEquiv R D T) (discardReferenceEquiv R D T) M) := by
  ext x y
  rfl

theorem discardReferenceLast_positive {M : QMatrix ((R × D) × T)}
    (hM : M.PosSemidef) : (discardReferenceLast M).PosSemidef := by
  rw [discardReferenceLast_eq_partialTrace]
  exact partialTraceRight_positive (hM.submatrix (discardReferenceEquiv R D T).symm)

theorem discardReferenceLast_trace (M : QMatrix ((R × D) × T)) :
    Matrix.trace (discardReferenceLast M) = Matrix.trace M := by
  rw [discardReferenceLast_eq_partialTrace,partialTraceRight_trace,
    QuantumProver.QuantumEntropy.trace_reindex]

def discardReferenceDensity (rho : Density ((R × D) × T)) : Density (R × T) where
  matrix := discardReferenceLast rho.matrix
  positive := discardReferenceLast_positive rho.positive
  trace_one := (discardReferenceLast_trace rho.matrix).trans rho.trace_one

theorem discardReferenceLast_amplify (Phi : QMatrix T →ₗ[ℂ] QMatrix U)
    (M : QMatrix ((R × D) × T)) :
    discardReferenceLast (amplify Phi M) = amplify Phi (discardReferenceLast M) := by
  ext ⟨r,u⟩ ⟨r',u'⟩
  let f : D → QMatrix T := fun d i j => M ((r,d),i) ((r',d),j)
  change (∑ d, Phi (f d) u u') =
    Phi (fun i j => ∑ d, M ((r,d),i) ((r',d),j)) u u'
  have hsum : (∑ d, f d) = (fun i j => ∑ d, M ((r,d),i) ((r',d),j)) := by
    ext i j
    simp only [Matrix.sum_apply]
    rfl
  calc
    _ = (∑ d, Phi (f d)) u u' := by simp only [Matrix.sum_apply]
    _ = Phi (∑ d, f d) u u' :=
      (congrArg (fun N : QMatrix U => N u u') (map_sum Phi f Finset.univ)).symm
    _ = _ := by rw [hsum]

def resourceCoefficient (D : Type*) [Fintype D] : ℂ :=
  (Real.sqrt (Fintype.card D : ℝ) : ℂ)⁻¹

theorem resourceCoefficient_mul_star (D : Type*) [Fintype D] :
    resourceCoefficient D * star (resourceCoefficient D) = ((Fintype.card D : ℝ)⁻¹ : ℂ) := by
  rw [resourceCoefficient,Complex.star_def,Complex.mul_conj,Complex.normSq_inv,
    Complex.normSq_ofReal,Real.mul_self_sqrt (Nat.cast_nonneg _)]
  simp

def eprResource (D : Type*) [Fintype D] [DecidableEq D] : D × D → ℂ :=
  fun d => if d.1=d.2 then resourceCoefficient D else 0

def eprLift (psi : R × S → ℂ) (D : Type*) [Fintype D] [DecidableEq D] :
    (R × D) × (S × D) → ℂ :=
  fun z => psi (z.1.1,z.2.1) * eprResource D (z.1.2,z.2.2)

theorem eprLift_pure_apply (psi : R × S → ℂ) (r r' : R) (s s' : S)
    (d d' k k' : D) :
    pureDensity (eprLift psi D) ((r,d),(s,k)) ((r',d'),(s',k')) =
      if d=k ∧ d'=k' then
        (psi (r,s) * star (psi (r',s'))) * ((Fintype.card D : ℝ)⁻¹ : ℂ) else 0 := by
  by_cases hd : d=k <;> by_cases hd' : d'=k'
  · simp only [pureDensity,QuantumProver.WernerEndpoint.pureDensity,QuantumProver.WernerEndpoint.crossDensity,
      eprLift,eprResource,if_pos hd,if_pos hd',star_mul,if_pos (And.intro hd hd')]
    calc
      _ = (psi (r,s) * star (psi (r',s'))) *
          (resourceCoefficient D * star (resourceCoefficient D)) := by ring
      _ = _ := by rw [resourceCoefficient_mul_star]
  · simp [pureDensity,QuantumProver.WernerEndpoint.pureDensity,QuantumProver.WernerEndpoint.crossDensity,
      eprLift,eprResource,hd,hd']
  · simp [pureDensity,QuantumProver.WernerEndpoint.pureDensity,QuantumProver.WernerEndpoint.crossDensity,
      eprLift,eprResource,hd,hd']
  · simp [pureDensity,QuantumProver.WernerEndpoint.pureDensity,QuantumProver.WernerEndpoint.crossDensity,
      eprLift,eprResource,hd,hd']

theorem eprLift_leftMarginal [Nonempty D] (psi : R × S → ℂ) :
    partialTraceRight (pureDensity (eprLift psi D)) =
      partialTraceRight (pureDensity psi) ⊗ₖ (uniformDensity D).matrix := by
  ext ⟨r,d⟩ ⟨r',d'⟩
  simp only [partialTraceRight,QuantumProver.WernerEndpoint.partialTraceLeft,Fintype.sum_prod_type,
    eprLift_pure_apply]
  by_cases hd : d=d'
  · subst d'
    simp [Matrix.kronecker_apply,uniformDensity,Matrix.one_apply,
      partialTraceRight,QuantumProver.WernerEndpoint.partialTraceLeft,
      pureDensity,QuantumProver.WernerEndpoint.pureDensity,QuantumProver.WernerEndpoint.crossDensity,
      ← Finset.sum_mul]
  · have hh : ∀ k : D, ¬ (d=k ∧ d'=k) := by
      intro k hk
      exact hd (hk.1.trans hk.2.symm)
    simp [hh,Matrix.kronecker_apply,uniformDensity,Matrix.one_apply,hd]

theorem pureDensity_trace_of_normalized (psi : R × S → ℂ) (hpsi : IsNormalized psi) :
    Matrix.trace (pureDensity psi) = 1 := by
  rw [pureDensity,QuantumProver.WernerEndpoint.pureDensity_trace]
  change (vectorNormSq psi : ℂ) = 1
  rw [hpsi]
  rfl

def pureSourceDensity (psi : R × S → ℂ) (hpsi : IsNormalized psi) : Density (R × S) where
  matrix := pureDensity psi
  positive := QuantumProver.WernerEndpoint.pureDensity_posSemidef psi
  trace_one := pureDensity_trace_of_normalized psi hpsi

theorem eprLift_trace [Nonempty D] (psi : R × S → ℂ) (hpsi : IsNormalized psi) :
    Matrix.trace (pureDensity (eprLift psi D)) = 1 := by
  rw [← partialTraceRight_trace,eprLift_leftMarginal,Matrix.trace_kronecker,
    (uniformDensity D).trace_one,mul_one,partialTraceRight_trace]
  exact pureDensity_trace_of_normalized psi hpsi

theorem eprLift_normalized [Nonempty D] (psi : R × S → ℂ) (hpsi : IsNormalized psi) :
    IsNormalized (eprLift psi D) := by
  change QuantumProver.WernerEndpoint.vectorNormSq (eprLift psi D) = 1
  have h := congrArg Complex.re (eprLift_trace (D := D) psi hpsi)
  change (Matrix.trace (QuantumProver.WernerEndpoint.pureDensity _)).re = (1 : ℂ).re at h
  simpa only [QuantumProver.WernerEndpoint.pureDensity_trace,Complex.ofReal_re,Complex.one_re] using h

def eprLiftDensity [Nonempty D] (psi : R × S → ℂ) (hpsi : IsNormalized psi) :
    Density ((R × D) × (S × D)) where
  matrix := pureDensity (eprLift psi D)
  positive := QuantumProver.WernerEndpoint.pureDensity_posSemidef _
  trace_one := eprLift_trace psi hpsi

theorem eprLift_discardReference [Nonempty D] (psi : R × S → ℂ) :
    discardReferenceLast (pureDensity (eprLift psi D)) =
      Matrix.reindex (Equiv.prodAssoc R S D) (Equiv.prodAssoc R S D)
        (pureDensity psi ⊗ₖ (uniformDensity D).matrix) := by
  ext ⟨r,⟨s,d⟩⟩ ⟨r',⟨s',d'⟩⟩
  simp only [discardReferenceLast,eprLift_pure_apply]
  by_cases hd : d=d'
  · subst d'
    simp [Matrix.reindex_apply,
      Matrix.submatrix_apply,Matrix.kronecker_apply,uniformDensity,Matrix.one_apply,
      pureDensity,QuantumProver.WernerEndpoint.pureDensity,QuantumProver.WernerEndpoint.crossDensity,eq_comm]
  · have hh : ∀ k : D, ¬ (k=d ∧ k=d') := by
      intro k hk
      exact hd (hk.1.symm.trans hk.2)
    simp [hh,Matrix.reindex_apply,
      Matrix.submatrix_apply,Matrix.kronecker_apply,uniformDensity,Matrix.one_apply,hd]

theorem eprLift_discardReference_density [Nonempty D] (psi : R × S → ℂ)
    (hpsi : IsNormalized psi) :
    discardReferenceDensity (eprLiftDensity (D := D) psi hpsi) =
      appendLocalDensity (pureSourceDensity psi hpsi) (uniformDensity D) := by
  apply density_ext
  exact eprLift_discardReference psi

theorem sourceWire_discardPurifier (rho : Density (A × (B × E))) :
    discardReferenceLast (pureDensity (BCYPurification.sourceWireKet rho)) = rho.matrix := by
  ext ⟨a,⟨b,e⟩⟩ ⟨a',⟨b',e'⟩⟩
  have h := congrArg (fun M : QMatrix ((A × B) × E) => M ((a,b),e) ((a',b'),e'))
    (BCYPurification.sourceKet_marginal rho)
  simpa only [discardReferenceLast,BCYPurification.sourceWireKet,BCYPurification.wireEquiv,
    partialTraceRight,QuantumProver.WernerEndpoint.partialTraceLeft,BCYPurification.sourceMarginal,
    pureDensity,QuantumProver.WernerEndpoint.pureDensity,QuantumProver.WernerEndpoint.crossDensity,
    densityReindex,BCYPurification.sourceEquiv,Matrix.reindex_apply,Matrix.submatrix_apply,
    Equiv.prodAssoc_symm_apply,Equiv.symm_symm,Equiv.prodAssoc_apply,Equiv.prodAssoc,Equiv.symm,
    Equiv.coe_fn_mk] using h

theorem sourceCopiesWire_discardPurifier (rho : Density (A × (B × E))) (n : ℕ) :
    discardReferenceLast (pureDensity (BCYPurification.sourceCopiesWireKet rho n)) =
      (BCYRedistributionCode.tripleCopies rho n).matrix := by
  classical
  ext ⟨a,⟨b,e⟩⟩ ⟨a',⟨b',e'⟩⟩
  have h := congrArg
    (fun M : QMatrix ((CopyIndex A n × CopyIndex B n) × CopyIndex E n) =>
      M ((a,b),e) ((a',b'),e')) (BCYPurification.sourceKetCopies_marginal rho n)
  simpa only [discardReferenceLast,BCYPurification.sourceCopiesWireKet,BCYPurification.wireEquiv,
    partialTraceRight,QuantumProver.WernerEndpoint.partialTraceLeft,BCYPurification.sourceCopiesMarginal,
    pureDensity,QuantumProver.WernerEndpoint.pureDensity,QuantumProver.WernerEndpoint.crossDensity,
    densityReindex,BCYPurification.sourceEquiv,Matrix.reindex_apply,Matrix.submatrix_apply,
    Equiv.prodAssoc_symm_apply,Equiv.symm_symm,Equiv.prodAssoc_apply,Equiv.prodAssoc,Equiv.symm,
    Equiv.coe_fn_mk] using h

theorem eprLift_discardReference_amplify [Nonempty D] (psi : R × S → ℂ) :
    discardReferenceLast (pureDensity (eprLift psi D)) =
      amplify (BCYRedistributionCode.appendRightChannel (I := S) (uniformDensity D)).map
        (pureDensity psi) := by
  rw [eprLift_discardReference]
  ext ⟨r,⟨s,d⟩⟩ ⟨r',⟨s',d'⟩⟩
  rfl

theorem sourceWireEPR_discardPhysical [Nonempty D] (rho : Density (A × (B × E))) :
    discardReferenceLast
      (discardReferenceLast (pureDensity (eprLift (BCYPurification.sourceWireKet rho) D))) =
        (appendLocalDensity rho (uniformDensity D)).matrix := by
  rw [eprLift_discardReference_amplify,discardReferenceLast_amplify,sourceWire_discardPurifier]
  rfl

theorem sourceCopiesWireEPR_discardPhysical [Nonempty D]
    (rho : Density (A × (B × E))) (n : ℕ) :
    discardReferenceLast
      (discardReferenceLast (pureDensity (eprLift (BCYPurification.sourceCopiesWireKet rho n) D))) =
      amplify (BCYRedistributionCode.appendRightChannel
        (I := CopyIndex B n × CopyIndex E n) (uniformDensity D)).map
        (BCYRedistributionCode.tripleCopies rho n).matrix := by
  rw [eprLift_discardReference_amplify,discardReferenceLast_amplify,
    sourceCopiesWire_discardPurifier]

end QuantumProver.DepolarizingSquashedEntanglement.BCYRedistributionResources

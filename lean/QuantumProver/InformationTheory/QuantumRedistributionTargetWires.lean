import QuantumProver.InformationTheory.QuantumDecoupling
import QuantumProver.InformationTheory.DepolarizingSquashedEntanglement.BCYRedistributionResources

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
noncomputable section

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Kronecker

namespace QuantumProver.QuantumRedistributionTargetWires

open QuantumProver.DepolarizingSquashedEntanglement
open QuantumProver.UnitarySecondMoment

variable {A C E B K D F G R S J : Type*}
  [Fintype A] [Fintype C] [Fintype E] [Fintype B] [Fintype K]
  [Fintype D] [Fintype F] [Fintype G] [Fintype R] [Fintype S] [Fintype J]
  [DecidableEq A] [DecidableEq C] [DecidableEq E] [DecidableEq B] [DecidableEq K]
  [DecidableEq D] [DecidableEq F] [DecidableEq G] [DecidableEq R]
  [DecidableEq S] [DecidableEq J]

def sourceBACEquiv (A C B E : Type*) :
    ((A × C) × (B × E)) ≃ ((B × (A × C)) × E) where
  toFun x := ((x.2.1, x.1), x.2.2)
  invFun x := (x.1.2, (x.1.1, x.2))
  left_inv := by rintro ⟨⟨a,c⟩,⟨b,e⟩⟩; rfl
  right_inv := by rintro ⟨⟨b,⟨a,c⟩⟩,e⟩; rfl

def sourceBAEEquiv (A C B E : Type*) :
    ((A × C) × (B × E)) ≃ ((B × (A × E)) × C) where
  toFun x := ((x.2.1, (x.1.1, x.2.2)), x.1.2)
  invFun x := ((x.1.2.1, x.2), (x.1.1, x.1.2.2))
  left_inv := by rintro ⟨⟨a,c⟩,⟨b,e⟩⟩; rfl
  right_inv := by rintro ⟨⟨b,⟨a,e⟩⟩,c⟩; rfl

def sourceBACKet (χ : (A × C) × (B × E) → ℂ) : (B × (A × C)) × E → ℂ :=
  fun x => χ (x.1.2, (x.1.1, x.2))

def sourceBAEKet (χ : (A × C) × (B × E) → ℂ) : (B × (A × E)) × C → ℂ :=
  fun x => χ ((x.1.2.1, x.2), (x.1.1, x.1.2.2))

def rhoBAC (χ : (A × C) × (B × E) → ℂ) : QMatrix (B × (A × C)) :=
  partialTraceRight (pureDensity (sourceBACKet χ))

def rhoBAE (χ : (A × C) × (B × E) → ℂ) : QMatrix (B × (A × E)) :=
  partialTraceRight (pureDensity (sourceBAEKet χ))

def senderAction (M : Matrix K B ℂ) (χ : (A × C) × (B × E) → ℂ) :
    (A × C) × (K × E) → ℂ :=
  fun x => ∑ b, M x.2.1 b * χ (x.1, (b, x.2.2))

def liftSenderKet (M : Matrix K B ℂ) (ψ : (B × R) × S → ℂ) : (K × R) × S → ℂ :=
  fun x => ∑ b, M x.1.1 b * ψ ((b, x.1.2), x.2)

omit [Fintype K] [DecidableEq B] [DecidableEq K] [DecidableEq S] in

theorem liftSenderKet_marginal (M : Matrix K B ℂ) (ψ : (B × R) × S → ℂ) :
    partialTraceRight (pureDensity (liftSenderKet M ψ)) =
      (M ⊗ₖ (1 : Matrix R R ℂ)) * partialTraceRight (pureDensity ψ) *
        (M ⊗ₖ (1 : Matrix R R ℂ))ᴴ := by
  ext ⟨k,r⟩ ⟨l,t⟩
  simp only [partialTraceRight, QuantumProver.WernerEndpoint.partialTraceLeft, pureDensity,
    QuantumProver.WernerEndpoint.pureDensity, QuantumProver.WernerEndpoint.crossDensity, liftSenderKet,
    Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
    Matrix.mul_apply, Fintype.sum_prod_type, Matrix.kroneckerMap_apply, Matrix.one_apply,
    mul_ite, ite_mul, mul_one, mul_zero, zero_mul, Matrix.conjTranspose_apply,
    star_sum, star_mul, Finset.sum_mul, Finset.mul_sum]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq',
    Finset.sum_ite_eq, Finset.mem_univ, ite_eq_left]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b' _
  apply Finset.sum_congr rfl
  intro s _
  ring

omit [Fintype K] [DecidableEq B] [DecidableEq K] [DecidableEq E] in
theorem rhoBAC_senderAction (M : Matrix K B ℂ) (χ : (A × C) × (B × E) → ℂ) :
    rhoBAC (senderAction M χ) = (M ⊗ₖ (1 : Matrix (A × C) (A × C) ℂ)) * rhoBAC χ *
      (M ⊗ₖ (1 : Matrix (A × C) (A × C) ℂ))ᴴ :=
  liftSenderKet_marginal M (sourceBACKet χ)

omit [Fintype K] [DecidableEq B] [DecidableEq K] [DecidableEq C] in
theorem rhoBAE_senderAction (M : Matrix K B ℂ) (χ : (A × C) × (B × E) → ℂ) :
    rhoBAE (senderAction M χ) = (M ⊗ₖ (1 : Matrix (A × E) (A × E) ℂ)) * rhoBAE χ *
      (M ⊗ₖ (1 : Matrix (A × E) (A × E) ℂ))ᴴ :=
  liftSenderKet_marginal M (sourceBAEKet χ)

def splitD (D F G : Type*) : ((D × F) × G) ≃ ((F × G) × D) where
  toFun x := ((x.1.2, x.2), x.1.1)
  invFun x := ((x.2, x.1.1), x.1.2)
  left_inv := by rintro ⟨⟨d,f⟩,g⟩; rfl
  right_inv := by rintro ⟨⟨f,g⟩,d⟩; rfl

def splitF (D F G : Type*) : ((D × F) × G) ≃ ((D × G) × F) where
  toFun x := ((x.1.1, x.2), x.1.2)
  invFun x := ((x.1.1, x.2), x.1.2)
  left_inv := by rintro ⟨⟨d,f⟩,g⟩; rfl
  right_inv := by rintro ⟨⟨d,g⟩,f⟩; rfl

def chartD {d : ℕ} (p : Fin d ≃ ((D × F) × G)) : Fin d ≃ ((F × G) × D) :=
  p.trans (splitD D F G)

def chartF {d : ℕ} (p : Fin d ≃ ((D × F) × G)) : Fin d ≃ ((D × G) × F) :=
  p.trans (splitF D F G)

def targetKet {d : ℕ} (p : Fin d ≃ ((D × F) × G)) (U : UGroup d)
    (χ : (A × C) × (Fin d × E) → ℂ) : ((A × C) × D) × ((E × F) × G) → ℂ :=
  fun x => ∑ i, (U : CMat d) (p.symm ((x.1.2, x.2.1.2), x.2.2)) i *
    χ (x.1.1, (i, x.2.1.1))

def splitKet {d : ℕ} (e : Fin d ≃ J × K) (U : UGroup d)
    (ψ : (Fin d × R) × S → ℂ) : (K × R) × (J × S) → ℂ :=
  fun x => ∑ i, (U : CMat d) (e.symm (x.2.1, x.1.1)) i * ψ ((i, x.1.2), x.2.2)

omit [Fintype K] [DecidableEq K] [DecidableEq S] [DecidableEq J] in

theorem splitKet_marginal {d : ℕ} (e : Fin d ≃ J × K) (U : UGroup d)
    (ψ : (Fin d × R) × S → ℂ) :
    partialTraceRight (pureDensity (splitKet e U ψ)) =
      QuantumDecoupling.decoupledMarginal e (partialTraceRight (pureDensity ψ)) U := by
  ext ⟨k,r⟩ ⟨l,t⟩
  rw [QuantumDecoupling.decoupledMarginal_apply]
  simp only [partialTraceRight, QuantumProver.WernerEndpoint.partialTraceLeft, pureDensity,
    QuantumProver.WernerEndpoint.pureDensity, QuantumProver.WernerEndpoint.crossDensity, splitKet,
    QuantumDecoupling.partialRetain, QuantumDecoupling.matrixBlock,
    Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type,
    star_sum, star_mul, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i' _
  apply Finset.sum_congr rfl
  intro s _
  ring

def firstComplementEquiv (E F G : Type*) : ((E × F) × G) ≃ ((F × G) × E) where
  toFun x := ((x.1.2, x.2), x.1.1)
  invFun x := ((x.2, x.1.1), x.1.2)
  left_inv := by rintro ⟨⟨e,f⟩,g⟩; rfl
  right_inv := by rintro ⟨⟨f,g⟩,e⟩; rfl

omit [Fintype D] [DecidableEq E] [DecidableEq D] [DecidableEq F] [DecidableEq G] in
theorem target_firstMarginal {d : ℕ} (p : Fin d ≃ ((D × F) × G)) (U : UGroup d)
    (χ : (A × C) × (Fin d × E) → ℂ) :
    partialTraceRight (pureDensity (targetKet p U χ)) =
      Matrix.reindex (Equiv.prodComm D (A × C)) (Equiv.prodComm D (A × C))
        (QuantumDecoupling.decoupledMarginal (chartD p) (rhoBAC χ) U) := by
  unfold rhoBAC
  rw [← splitKet_marginal]
  ext ⟨⟨a,c⟩,k⟩ ⟨⟨a',c'⟩,l⟩
  let f : (F × G) × E → ℂ := fun y =>
    targetKet p U χ (((a,c),k),((y.2,y.1.1),y.1.2)) *
      star (targetKet p U χ (((a',c'),l),((y.2,y.1.1),y.1.2)))
  change (∑ x : (E × F) × G, f (firstComplementEquiv E F G x)) = ∑ y, f y
  exact (firstComplementEquiv E F G).sum_comp f

def retainedTarget {d : ℕ} (p : Fin d ≃ ((D × F) × G)) (U : UGroup d)
    (χ : (A × C) × (Fin d × E) → ℂ) : QMatrix (A × (E × F)) :=
  amplify (BCYRedistributionCode.discardRightChannel (E × F) G).map
    (BCYRedistributionResources.discardReferenceLast
      (BCYRedistributionResources.discardReferenceLast (pureDensity (targetKet p U χ))))

def retainedChart (A E F : Type*) : (F × (A × E)) ≃ (A × (E × F)) where
  toFun x := (x.2.1, (x.2.2, x.1))
  invFun x := (x.2.2, (x.1, x.2.1))
  left_inv := by rintro ⟨f,⟨a,e⟩⟩; rfl
  right_inv := by rintro ⟨a,⟨e,f⟩⟩; rfl

def retainedComplementEquiv (C D G : Type*) : (G × (C × D)) ≃ ((D × G) × C) where
  toFun x := ((x.2.2, x.1), x.2.1)
  invFun x := (x.1.2, (x.2, x.1.1))
  left_inv := by rintro ⟨g,⟨c,d⟩⟩; rfl
  right_inv := by rintro ⟨⟨d,g⟩,c⟩; rfl

omit [DecidableEq C] [DecidableEq D] [DecidableEq F] [DecidableEq G] in
theorem target_retainedMarginal {d : ℕ} (p : Fin d ≃ ((D × F) × G)) (U : UGroup d)
    (χ : (A × C) × (Fin d × E) → ℂ) :
    retainedTarget p U χ = Matrix.reindex (retainedChart A E F) (retainedChart A E F)
      (QuantumDecoupling.decoupledMarginal (chartF p) (rhoBAE χ) U) := by
  unfold rhoBAE
  rw [← splitKet_marginal]
  ext ⟨a,⟨e,f⟩⟩ ⟨a',⟨e',f'⟩⟩
  let h : (D × G) × C → ℂ := fun y =>
    targetKet p U χ (((a,y.2),y.1.1),((e,f),y.1.2)) *
      star (targetKet p U χ (((a',y.2),y.1.1),((e',f'),y.1.2)))
  change (∑ g : G, ∑ c : C, ∑ k : D, h ((k,g),c)) = ∑ y, h y
  simpa only [Fintype.sum_prod_type, retainedComplementEquiv, Equiv.coe_fn_mk] using
    (retainedComplementEquiv C D G).sum_comp h

omit [DecidableEq A] [DecidableEq C] [DecidableEq E] [DecidableEq B] in
theorem rhoBAC_posSemidef (χ : (A × C) × (B × E) → ℂ) : (rhoBAC χ).PosSemidef :=
  partialTraceRight_positive (QuantumProver.WernerEndpoint.pureDensity_posSemidef _)

omit [DecidableEq A] [DecidableEq C] [DecidableEq E] [DecidableEq B] in
theorem rhoBAE_posSemidef (χ : (A × C) × (B × E) → ℂ) : (rhoBAE χ).PosSemidef :=
  partialTraceRight_positive (QuantumProver.WernerEndpoint.pureDensity_posSemidef _)

theorem rhoBAC_isDensity (χ : (A × C) × (B × E) → ℂ) (hχ : IsNormalized χ) :
    SuperchannelDiscrimination.FlaggedStates.IsDensity (rhoBAC χ) := by
  have hψ := BCYPurification.normalized_reindex (sourceBACEquiv A C B E) χ hχ
  refine ⟨rhoBAC_posSemidef χ, ?_⟩
  rw [rhoBAC, partialTraceRight_trace]
  exact BCYRedistributionResources.pureDensity_trace_of_normalized _ hψ

theorem rhoBAE_isDensity (χ : (A × C) × (B × E) → ℂ) (hχ : IsNormalized χ) :
    SuperchannelDiscrimination.FlaggedStates.IsDensity (rhoBAE χ) := by
  have hψ := BCYPurification.normalized_reindex (sourceBAEEquiv A C B E) χ hχ
  refine ⟨rhoBAE_posSemidef χ, ?_⟩
  rw [rhoBAE, partialTraceRight_trace]
  exact BCYRedistributionResources.pureDensity_trace_of_normalized _ hψ

theorem targetKet_normalized {d : ℕ} (p : Fin d ≃ ((D × F) × G)) (U : UGroup d)
    (χ : (A × C) × (Fin d × E) → ℂ) (hχ : IsNormalized χ) :
    IsNormalized (targetKet p U χ) := by
  have hρ := QuantumDecoupling.decoupledMarginal_isDensity (chartD p) (rhoBAC_isDensity χ hχ) U
  have ht : Matrix.trace (pureDensity (targetKet p U χ)) = 1 := by
    rw [← partialTraceRight_trace, target_firstMarginal, QuantumEntropy.trace_reindex]
    exact hρ.2
  have h := congrArg Complex.re ht
  change QuantumProver.WernerEndpoint.vectorNormSq (targetKet p U χ) = 1
  simpa only [pureDensity, QuantumProver.WernerEndpoint.pureDensity_trace, Complex.ofReal_re, Complex.one_re] using h

theorem target_isDensity {d : ℕ} (p : Fin d ≃ ((D × F) × G)) (U : UGroup d)
    (χ : (A × C) × (Fin d × E) → ℂ) (hχ : IsNormalized χ) :
    SuperchannelDiscrimination.FlaggedStates.IsDensity (pureDensity (targetKet p U χ)) :=
  ⟨QuantumProver.WernerEndpoint.pureDensity_posSemidef _,
    BCYRedistributionResources.pureDensity_trace_of_normalized _ (targetKet_normalized p U χ hχ)⟩

omit [DecidableEq C] in
theorem retainedTarget_posSemidef {d : ℕ} (p : Fin d ≃ ((D × F) × G)) (U : UGroup d)
    (χ : (A × C) × (Fin d × E) → ℂ) : (retainedTarget p U χ).PosSemidef := by
  rw [target_retainedMarginal]
  exact (QuantumDecoupling.decoupledMarginal_posSemidef (chartF p) (rhoBAE_posSemidef χ) U).submatrix
    (retainedChart A E F).symm

theorem retainedTarget_isDensity {d : ℕ} (p : Fin d ≃ ((D × F) × G)) (U : UGroup d)
    (χ : (A × C) × (Fin d × E) → ℂ) (hχ : IsNormalized χ) :
    SuperchannelDiscrimination.FlaggedStates.IsDensity (retainedTarget p U χ) := by
  refine ⟨retainedTarget_posSemidef p U χ, ?_⟩
  rw [target_retainedMarginal, QuantumEntropy.trace_reindex]
  exact (QuantumDecoupling.decoupledMarginal_isDensity (chartF p) (rhoBAE_isDensity χ hχ) U).2

end QuantumProver.QuantumRedistributionTargetWires

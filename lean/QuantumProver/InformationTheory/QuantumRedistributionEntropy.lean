import QuantumProver.InformationTheory.ConditionalEntropy.ContinuousLocalInstrument
import QuantumProver.InformationTheory.QuantumEntropy.EntropyReindex
import QuantumProver.InformationTheory.QuantumEntropy.TensorLogTrace
import QuantumProver.InformationTheory.DepolarizingSquashedEntanglement.Definitions

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

noncomputable section

open Matrix
open scoped Topology BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace QuantumProver.QuantumRedistributionEntropy

open QuantumProver.QuantumEntropy

abbrev pureMatrix {I : Type*} (ψ : I → ℂ) : Matrix I I ℂ :=
  QuantumProver.ConditionalEntropy.ContinuousLocalInstrument.pureDensity ψ

abbrev normSq {I : Type*} [Fintype I] (ψ : I → ℂ) : ℝ :=
  QuantumProver.ConditionalEntropy.ContinuousLocalInstrument.vectorNormSq ψ

def transportKet {I J : Type*} (e : I ≃ J) (ψ : I → ℂ) : J → ℂ :=
  fun j => ψ (e.symm j)

theorem pureMatrix_transport {I J : Type*} (e : I ≃ J) (ψ : I → ℂ) :
    pureMatrix (transportKet e ψ) = Matrix.reindex e e (pureMatrix ψ) := rfl

theorem normSq_transport {I J : Type*} [Fintype I] [Fintype J]
    (e : I ≃ J) (ψ : I → ℂ) : normSq (transportKet e ψ) = normSq ψ :=
  e.symm.sum_comp (fun i => Complex.normSq (ψ i))

theorem pureMatrix_isDensity {I : Type*} [Fintype I] [DecidableEq I]
    (ψ : I → ℂ) (hψ : normSq ψ = 1) : IsDensity (pureMatrix ψ) :=
  QuantumProver.ConditionalEntropy.ContinuousLocalInstrument.pureDensity_isDensity ψ hψ

theorem pureChart_isDensity {I J : Type*} [Fintype I] [Fintype J] [DecidableEq J]
    (e : I ≃ J) (ψ : I → ℂ) (hψ : normSq ψ = 1) :
    IsDensity (pureMatrix (transportKet e ψ)) :=
  pureMatrix_isDensity _ ((normSq_transport e ψ).trans hψ)

theorem pure_marginal_entropy_nats {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (ψ : I × J → ℂ) :
    entropyNats (partialTrace_right (pureMatrix ψ)) =
      entropyNats (partialTrace_left (pureMatrix ψ)) := by
  rw [entropyNats_eq_entropyBits_mul_log_two, entropyNats_eq_entropyBits_mul_log_two]
  exact congrArg (fun x : ℝ => x * Real.log 2)
    (QuantumProver.ConditionalEntropy.ContinuousLocalInstrument.pure_marginal_entropy_eq ψ)

variable {A B E C : Type*} [Fintype A] [Fintype B] [Fintype E] [Fintype C]
  [DecidableEq A] [DecidableEq B] [DecidableEq E] [DecidableEq C]

abbrev PhysicalIndex (A B E C : Type*) := ((A × B) × E) × C

def physicalChart (A B E C : Type*) :
    PhysicalIndex A B E C ≃ (A × (B × E)) × C :=
  Equiv.prodCongr (Equiv.prodAssoc A B E) (Equiv.refl C)

def beACChart (A B E C : Type*) : PhysicalIndex A B E C ≃ (B × E) × (A × C) where
  toFun x := ((x.1.1.2,x.1.2),(x.1.1.1,x.2))
  invFun x := (((x.2.1,x.1.1),x.1.2),x.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

def bcAEChart (A B E C : Type*) : PhysicalIndex A B E C ≃ (B × C) × (A × E) where
  toFun x := ((x.1.1.2,x.2),(x.1.1.1,x.1.2))
  invFun x := (((x.2.1,x.1.1),x.2.2),x.1.2)
  left_inv _ := rfl
  right_inv _ := rfl

def acBEChart (A B E C : Type*) : PhysicalIndex A B E C ≃ ((A × C) × B) × E where
  toFun x := (((x.1.1.1,x.2),x.1.1.2),x.1.2)
  invFun x := (((x.1.1.1,x.1.2),x.2),x.1.1.2)
  left_inv _ := rfl
  right_inv _ := rfl

def aeBCChart (A B E C : Type*) : PhysicalIndex A B E C ≃ ((A × E) × B) × C where
  toFun x := (((x.1.1.1,x.1.2),x.1.1.2),x.2)
  invFun x := (((x.1.1.1,x.1.2),x.1.1.2),x.2)
  left_inv _ := rfl
  right_inv _ := rfl

def swapBEChart (A B E : Type*) : (A × B) × E ≃ (A × E) × B where
  toFun x := ((x.1.1,x.2),x.1.2)
  invFun x := ((x.1.1,x.2),x.1.2)
  left_inv _ := rfl
  right_inv _ := rfl

def ssaChart (A B E : Type*) : (A × B) × E ≃ A × (E × B) :=
  (swapBEChart A B E).trans (Equiv.prodAssoc A E B)

def reducedABE (ψ : PhysicalIndex A B E C → ℂ) : Matrix ((A × B) × E) ((A × B) × E) ℂ :=
  partialTrace_right (pureMatrix ψ)

def reducedABC (ψ : PhysicalIndex A B E C → ℂ) : Matrix ((A × C) × B) ((A × C) × B) ℂ :=
  partialTrace_right (pureMatrix (transportKet (acBEChart A B E C) ψ))

def reducedBAE (ψ : PhysicalIndex A B E C → ℂ) : Matrix ((A × E) × B) ((A × E) × B) ℂ :=
  partialTrace_right (pureMatrix (transportKet (aeBCChart A B E C) ψ))

def reducedBE (ψ : PhysicalIndex A B E C → ℂ) : Matrix (B × E) (B × E) ℂ :=
  partialTrace_right (pureMatrix (transportKet (beACChart A B E C) ψ))

def reducedAC (ψ : PhysicalIndex A B E C → ℂ) : Matrix (A × C) (A × C) ℂ :=
  partialTrace_left (pureMatrix (transportKet (beACChart A B E C) ψ))

def reducedBC (ψ : PhysicalIndex A B E C → ℂ) : Matrix (B × C) (B × C) ℂ :=
  partialTrace_right (pureMatrix (transportKet (bcAEChart A B E C) ψ))

def reducedAE (ψ : PhysicalIndex A B E C → ℂ) : Matrix (A × E) (A × E) ℂ :=
  partialTrace_left (pureMatrix (transportKet (bcAEChart A B E C) ψ))

def reducedB (ψ : PhysicalIndex A B E C → ℂ) : Matrix B B ℂ := partialTrace_right (reducedBE ψ)

def reducedE (ψ : PhysicalIndex A B E C → ℂ) : Matrix E E ℂ := partialTrace_left (reducedBE ψ)

def reducedC (ψ : PhysicalIndex A B E C → ℂ) : Matrix C C ℂ := partialTrace_left (reducedBC ψ)

private theorem sum_move_last_first {I J K : Type*} [Fintype I] [Fintype J] [Fintype K]
    (f : I → J → K → ℂ) : (∑ i, ∑ j, ∑ k, f i j k) = ∑ k, ∑ i, ∑ j, f i j k := by
  calc
    _ = ∑ i, ∑ k, ∑ j, f i j k := by
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm
    _ = _ := Finset.sum_comm

private theorem sum_reverse_three {I J K : Type*} [Fintype I] [Fintype J] [Fintype K]
    (f : I → J → K → ℂ) : (∑ i, ∑ j, ∑ k, f i j k) = ∑ k, ∑ j, ∑ i, f i j k := by
  calc
    _ = ∑ j, ∑ i, ∑ k, f i j k := Finset.sum_comm
    _ = ∑ j, ∑ k, ∑ i, f i j k := by
      apply Finset.sum_congr rfl
      intro j _
      exact Finset.sum_comm
    _ = _ := Finset.sum_comm

omit [Fintype A] [Fintype C] [DecidableEq A] [DecidableEq B] [DecidableEq E] [DecidableEq C] in
theorem reducedAC_from_ABC (ψ : PhysicalIndex A B E C → ℂ) :
    partialTrace_right (reducedABC ψ) = reducedAC ψ := by
  ext i j
  simp only [reducedABC, reducedAC, partialTrace_right, partialTrace_left, transportKet,
    pureMatrix, QuantumProver.ConditionalEntropy.ContinuousLocalInstrument.pureDensity,
    acBEChart, beACChart, Fintype.sum_prod_type]
  rfl

omit [Fintype A] [Fintype E] [DecidableEq A] [DecidableEq B] [DecidableEq E] [DecidableEq C] in
theorem reducedAE_from_BAE (ψ : PhysicalIndex A B E C → ℂ) :
    partialTrace_right (reducedBAE ψ) = reducedAE ψ := by
  ext i j
  simp only [reducedBAE, reducedAE, partialTrace_right, partialTrace_left, transportKet,
    pureMatrix, QuantumProver.ConditionalEntropy.ContinuousLocalInstrument.pureDensity,
    aeBCChart, bcAEChart, Fintype.sum_prod_type]
  rfl

omit [Fintype E] [DecidableEq A] [DecidableEq B] [DecidableEq E] [DecidableEq C] in
theorem reducedE_from_ABC (ψ : PhysicalIndex A B E C → ℂ) :
    partialTrace_left (pureMatrix (transportKet (acBEChart A B E C) ψ)) = reducedE ψ := by
  ext e e'
  simp only [reducedE, reducedBE, partialTrace_right, partialTrace_left, transportKet,
    pureMatrix, QuantumProver.ConditionalEntropy.ContinuousLocalInstrument.pureDensity,
    acBEChart, beACChart, Fintype.sum_prod_type]
  exact sum_move_last_first _

omit [Fintype C] [DecidableEq A] [DecidableEq B] [DecidableEq E] [DecidableEq C] in
theorem reducedC_from_ABE (ψ : PhysicalIndex A B E C → ℂ) :
    partialTrace_left (pureMatrix ψ) = reducedC ψ := by
  ext c c'
  simp only [reducedC, reducedBC, partialTrace_right, partialTrace_left, transportKet,
    pureMatrix, QuantumProver.ConditionalEntropy.ContinuousLocalInstrument.pureDensity,
    bcAEChart, Fintype.sum_prod_type]
  exact Finset.sum_comm

omit [Fintype B] [DecidableEq A] [DecidableEq B] [DecidableEq E] [DecidableEq C] in
theorem reducedB_from_BC (ψ : PhysicalIndex A B E C → ℂ) :
    partialTrace_right (reducedBC ψ) = reducedB ψ := by
  ext b b'
  simp only [reducedB, reducedBC, reducedBE, partialTrace_right, transportKet,
    pureMatrix, QuantumProver.ConditionalEntropy.ContinuousLocalInstrument.pureDensity,
    bcAEChart, beACChart, Fintype.sum_prod_type]
  exact sum_reverse_three _

omit [Fintype A] [Fintype B] [Fintype E]
  [DecidableEq A] [DecidableEq B] [DecidableEq E] [DecidableEq C] in
theorem reducedBAE_reindex (ψ : PhysicalIndex A B E C → ℂ) :
    reducedBAE ψ = Matrix.reindex (swapBEChart A B E) (swapBEChart A B E) (reducedABE ψ) := by
  ext i j
  rfl

theorem reducedBE_isDensity (ψ : PhysicalIndex A B E C → ℂ) (hψ : normSq ψ = 1) :
    IsDensity (reducedBE ψ) := partialTraceRight_isDensity (pureChart_isDensity _ ψ hψ)

theorem reducedBC_isDensity (ψ : PhysicalIndex A B E C → ℂ) (hψ : normSq ψ = 1) :
    IsDensity (reducedBC ψ) := partialTraceRight_isDensity (pureChart_isDensity _ ψ hψ)

theorem reducedABE_isDensity (ψ : PhysicalIndex A B E C → ℂ) (hψ : normSq ψ = 1) :
    IsDensity (reducedABE ψ) := partialTraceRight_isDensity (pureMatrix_isDensity ψ hψ)

theorem entropyAC_eq_BE (ψ : PhysicalIndex A B E C → ℂ) :
    entropyNats (reducedAC ψ) = entropyNats (reducedBE ψ) :=
  (pure_marginal_entropy_nats (transportKet (beACChart A B E C) ψ)).symm

theorem entropyAE_eq_BC (ψ : PhysicalIndex A B E C → ℂ) :
    entropyNats (reducedAE ψ) = entropyNats (reducedBC ψ) :=
  (pure_marginal_entropy_nats (transportKet (bcAEChart A B E C) ψ)).symm

theorem entropyABC_eq_E (ψ : PhysicalIndex A B E C → ℂ) :
    entropyNats (reducedABC ψ) = entropyNats (reducedE ψ) := by
  have h := pure_marginal_entropy_nats (transportKet (acBEChart A B E C) ψ)
  rw [reducedE_from_ABC] at h
  exact h

theorem entropyABE_eq_C (ψ : PhysicalIndex A B E C → ℂ) :
    entropyNats (reducedABE ψ) = entropyNats (reducedC ψ) := by
  have h := pure_marginal_entropy_nats ψ
  rw [reducedC_from_ABE] at h
  exact h

theorem entropyBAE_eq_ABE (ψ : PhysicalIndex A B E C → ℂ) :
    entropyNats (reducedBAE ψ) = entropyNats (reducedABE ψ) := by
  rw [reducedBAE_reindex]
  exact entropyNats_reindex _ (partialTraceRight_posSemidef
    (QuantumProver.ConditionalEntropy.ContinuousLocalInstrument.pureDensity_posSemidef ψ)).1

def sentEntropyNat (ψ : PhysicalIndex A B E C → ℂ) : ℝ := entropyNats (reducedB ψ)

def conditionalBACNat (ψ : PhysicalIndex A B E C → ℂ) : ℝ :=
  entropyNats (reducedABC ψ) - entropyNats (reducedAC ψ)

def conditionalBAENat (ψ : PhysicalIndex A B E C → ℂ) : ℝ :=
  entropyNats (reducedBAE ψ) - entropyNats (reducedAE ψ)

def consumedBudgetNat (ψ : PhysicalIndex A B E C → ℂ) : ℝ :=
  sentEntropyNat ψ + conditionalBACNat ψ

def generatedBudgetNat (ψ : PhysicalIndex A B E C → ℂ) : ℝ :=
  sentEntropyNat ψ + conditionalBAENat ψ

def cmiNat (ψ : PhysicalIndex A B E C → ℂ) : ℝ :=
  entropyNats (reducedAE ψ) + entropyNats (reducedBE ψ) -
    entropyNats (reducedE ψ) - entropyNats (reducedABE ψ)

private theorem conditionalLastNat_eq_bits_swap {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] {R : Matrix (I × J) (I × J) ℂ} (hR : R.IsHermitian) :
    entropyNats R - entropyNats (partialTrace_right R) =
      QuantumProver.ConditionalEntropy.conditionalEntropyBits
        (Matrix.reindex (Equiv.prodComm I J) (Equiv.prodComm I J) R) * Real.log 2 := by
  have hm : partialTrace_left
      (Matrix.reindex (Equiv.prodComm I J) (Equiv.prodComm I J) R) = partialTrace_right R := rfl
  rw [QuantumProver.ConditionalEntropy.conditionalEntropyBits, sub_mul]
  simp only [← entropyNats_eq_entropyBits_mul_log_two]
  rw [hm, entropyNats_reindex _ hR]

theorem conditionalBACNat_eq_matrix (ψ : PhysicalIndex A B E C → ℂ) :
    conditionalBACNat ψ = QuantumProver.ConditionalEntropy.conditionalEntropyBits
      (Matrix.reindex (Equiv.prodComm (A × C) B) (Equiv.prodComm (A × C) B)
        (reducedABC ψ)) * Real.log 2 := by
  unfold conditionalBACNat
  rw [← reducedAC_from_ABC]
  exact conditionalLastNat_eq_bits_swap (partialTraceRight_posSemidef
    (QuantumProver.ConditionalEntropy.ContinuousLocalInstrument.pureDensity_posSemidef _)).1

theorem conditionalBAENat_eq_matrix (ψ : PhysicalIndex A B E C → ℂ) :
    conditionalBAENat ψ = QuantumProver.ConditionalEntropy.conditionalEntropyBits
      (Matrix.reindex (Equiv.prodComm (A × E) B) (Equiv.prodComm (A × E) B)
        (reducedBAE ψ)) * Real.log 2 := by
  unfold conditionalBAENat
  rw [← reducedAE_from_BAE]
  exact conditionalLastNat_eq_bits_swap (partialTraceRight_posSemidef
    (QuantumProver.ConditionalEntropy.ContinuousLocalInstrument.pureDensity_posSemidef _)).1

theorem consumedBudgetNat_eq_mutualInformation (ψ : PhysicalIndex A B E C → ℂ) :
    consumedBudgetNat ψ = entropyNats (reducedB ψ) + entropyNats (reducedE ψ) -
      entropyNats (reducedBE ψ) := by
  unfold consumedBudgetNat sentEntropyNat conditionalBACNat
  rw [entropyABC_eq_E, entropyAC_eq_BE]
  ring

theorem generatedBudgetNat_eq_mutualInformation (ψ : PhysicalIndex A B E C → ℂ) :
    generatedBudgetNat ψ = entropyNats (reducedB ψ) + entropyNats (reducedC ψ) -
      entropyNats (reducedBC ψ) := by
  unfold generatedBudgetNat sentEntropyNat conditionalBAENat
  rw [entropyBAE_eq_ABE, entropyABE_eq_C, entropyAE_eq_BC]
  ring

theorem budget_sum_eq_two_entropy_sub_cmi (ψ : PhysicalIndex A B E C → ℂ) :
    consumedBudgetNat ψ + generatedBudgetNat ψ = 2*sentEntropyNat ψ - cmiNat ψ := by
  unfold consumedBudgetNat generatedBudgetNat conditionalBACNat conditionalBAENat cmiNat
  rw [entropyABC_eq_E, entropyAC_eq_BE, entropyBAE_eq_ABE]
  ring

theorem half_cmi_eq_residual_entropy (ψ : PhysicalIndex A B E C → ℂ) :
    sentEntropyNat ψ - (consumedBudgetNat ψ + generatedBudgetNat ψ)/2 = cmiNat ψ/2 := by
  rw [budget_sum_eq_two_entropy_sub_cmi]
  ring

theorem entropyNats_subadditivity {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] {R : Matrix (I × J) (I × J) ℂ} (hR : IsDensity R) :
    entropyNats R ≤ entropyNats (partialTrace_right R) + entropyNats (partialTrace_left R) := by
  have h := mul_le_mul_of_nonneg_right (QuantumProver.ConditionalEntropy.entropyBits_subadditivity hR)
    (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
  simpa only [add_mul, ← entropyNats_eq_entropyBits_mul_log_two] using h

theorem sentEntropyNat_nonneg (ψ : PhysicalIndex A B E C → ℂ) (hψ : normSq ψ = 1) :
    0 ≤ sentEntropyNat ψ := by
  have h := (QuantumProver.ConditionalEntropy.ConditionalRange.entropyBits_bounds
    (partialTraceRight_isDensity (reducedBE_isDensity ψ hψ))).1
  unfold sentEntropyNat
  rw [entropyNats_eq_entropyBits_mul_log_two]
  exact mul_nonneg h (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le

theorem consumedBudgetNat_nonneg (ψ : PhysicalIndex A B E C → ℂ) (hψ : normSq ψ = 1) :
    0 ≤ consumedBudgetNat ψ := by
  have h := entropyNats_subadditivity (reducedBE_isDensity ψ hψ)
  rw [consumedBudgetNat_eq_mutualInformation]
  exact sub_nonneg.mpr h

theorem generatedBudgetNat_nonneg (ψ : PhysicalIndex A B E C → ℂ) (hψ : normSq ψ = 1) :
    0 ≤ generatedBudgetNat ψ := by
  have h := entropyNats_subadditivity (reducedBC_isDensity ψ hψ)
  rw [reducedB_from_BC] at h
  rw [generatedBudgetNat_eq_mutualInformation]
  exact sub_nonneg.mpr h

omit [Fintype E] [DecidableEq A] [DecidableEq B] [DecidableEq E] [DecidableEq C] in
theorem reducedE_from_AE (ψ : PhysicalIndex A B E C → ℂ) :
    partialTrace_left (reducedAE ψ) = reducedE ψ := by
  ext e e'
  simp only [reducedAE, reducedE, reducedBE, partialTrace_right, partialTrace_left,
    transportKet, pureMatrix, QuantumProver.ConditionalEntropy.ContinuousLocalInstrument.pureDensity,
    bcAEChart, beACChart, Fintype.sum_prod_type]
  exact Finset.sum_comm

omit [Fintype A] [Fintype E] [DecidableEq A] [DecidableEq B] [DecidableEq E] [DecidableEq C] in
theorem physical_traceMiddle (ψ : PhysicalIndex A B E C → ℂ) :
    QuantumProver.DepolarizingSquashedEntanglement.traceMiddle (reducedABE ψ) = reducedAE ψ := by
  ext i j
  simp only [QuantumProver.DepolarizingSquashedEntanglement.traceMiddle, reducedABE, reducedAE, partialTrace_right,
    partialTrace_left, transportKet, pureMatrix,
    QuantumProver.ConditionalEntropy.ContinuousLocalInstrument.pureDensity,
    bcAEChart, Fintype.sum_prod_type]
  rfl

omit [Fintype B] [Fintype E] [DecidableEq A] [DecidableEq B] [DecidableEq E] [DecidableEq C] in
theorem physical_traceFirst (ψ : PhysicalIndex A B E C → ℂ) :
    QuantumProver.DepolarizingSquashedEntanglement.traceFirst (reducedABE ψ) = reducedBE ψ := by
  ext i j
  simp only [QuantumProver.DepolarizingSquashedEntanglement.traceFirst, reducedABE, reducedBE, partialTrace_right,
    transportKet, pureMatrix, QuantumProver.ConditionalEntropy.ContinuousLocalInstrument.pureDensity,
    beACChart, Fintype.sum_prod_type]
  rfl

omit [Fintype E] [DecidableEq A] [DecidableEq B] [DecidableEq E] [DecidableEq C] in
theorem physical_traceE (ψ : PhysicalIndex A B E C → ℂ) :
    QuantumProver.DepolarizingSquashedEntanglement.partialTraceLeft (reducedABE ψ) = reducedE ψ := by
  ext e e'
  simp only [QuantumProver.DepolarizingSquashedEntanglement.partialTraceLeft, QuantumProver.WernerEndpoint.partialTraceRight,
    reducedABE, reducedE, reducedBE, partialTrace_right, partialTrace_left, transportKet,
    pureMatrix, QuantumProver.ConditionalEntropy.ContinuousLocalInstrument.pureDensity,
    beACChart, Fintype.sum_prod_type]
  exact Finset.sum_comm

private theorem entropyNat_eq_nats {I : Type*} [Fintype I] [DecidableEq I]
    (R : Matrix I I ℂ) : QuantumProver.DepolarizingSquashedEntanglement.entropyNat R = entropyNats R :=
  (entropyNats_eq_trace_cfc_negMulLog R).symm

omit [DecidableEq C] in
theorem cmiNat_eq_physical (ψ : PhysicalIndex A B E C → ℂ) :
    cmiNat ψ = QuantumProver.DepolarizingSquashedEntanglement.cmiNat (reducedABE ψ) := by
  unfold QuantumProver.DepolarizingSquashedEntanglement.cmiNat
  rw [physical_traceMiddle, physical_traceFirst, physical_traceE]
  simp only [entropyNat_eq_nats]
  rfl

theorem cmiNat_nonneg (ψ : PhysicalIndex A B E C → ℂ) (hψ : normSq ψ = 1) :
    0 ≤ cmiNat ψ := by
  let R := Matrix.reindex (ssaChart A B E) (ssaChart A B E) (reducedABE ψ)
  have hR : R.PosSemidef := (reducedABE_isDensity ψ hψ).1.submatrix (ssaChart A B E).symm
  have hAE : marginalAB R = reducedAE ψ := by
    change QuantumProver.DepolarizingSquashedEntanglement.traceMiddle (reducedABE ψ) = reducedAE ψ
    exact physical_traceMiddle ψ
  have hEB : marginalBC R = Matrix.reindex (Equiv.prodComm B E)
      (Equiv.prodComm B E) (reducedBE ψ) := by
    ext i j
    change QuantumProver.DepolarizingSquashedEntanglement.traceFirst (reducedABE ψ) (i.2,i.1) (j.2,j.1) =
      reducedBE ψ (i.2,i.1) (j.2,j.1)
    exact congrArg (fun M : Matrix (B × E) (B × E) ℂ => M (i.2,i.1) (j.2,j.1))
      (physical_traceFirst ψ)
  have hE : marginalB R = reducedE ψ := by
    change partialTrace_left (marginalAB R) = reducedE ψ
    rw [hAE, reducedE_from_AE]
  have hTotal : entropyNats R = entropyNats (reducedABE ψ) :=
    entropyNats_reindex _ (reducedABE_isDensity ψ hψ).1.1
  have hPair : entropyNats (marginalBC R) = entropyNats (reducedBE ψ) := by
    rw [hEB]
    exact entropyNats_reindex _ (reducedBE_isDensity ψ hψ).1.1
  have h := strongSubadditivity_nats_of_posSemidef hR
  rw [hE, hAE, hTotal, hPair] at h
  unfold cmiNat
  linarith

theorem budget_sum_le_two_entropy (ψ : PhysicalIndex A B E C → ℂ) (hψ : normSq ψ = 1) :
    consumedBudgetNat ψ + generatedBudgetNat ψ ≤ 2*sentEntropyNat ψ := by
  rw [budget_sum_eq_two_entropy_sub_cmi]
  exact sub_le_self _ (cmiNat_nonneg ψ hψ)

theorem scalar_packing_hypotheses (ψ : PhysicalIndex A B E C → ℂ) (hψ : normSq ψ = 1) :
    0 ≤ sentEntropyNat ψ ∧ 0 ≤ consumedBudgetNat ψ ∧ 0 ≤ generatedBudgetNat ψ ∧
      consumedBudgetNat ψ + generatedBudgetNat ψ ≤ 2*sentEntropyNat ψ :=
  ⟨sentEntropyNat_nonneg ψ hψ, consumedBudgetNat_nonneg ψ hψ,
    generatedBudgetNat_nonneg ψ hψ, budget_sum_le_two_entropy ψ hψ⟩

end QuantumProver.QuantumRedistributionEntropy

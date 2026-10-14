import Mathlib
import QuantumProver.InformationTheory.SuperchannelDiscrimination.FlaggedStates

set_option autoImplicit false

noncomputable section

open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix

namespace QuantumProver.BellDiagonalSquashedEntanglement

abbrev Qubit := Fin 2
abbrev AB := Qubit × Qubit
abbrev Mat (I : Type*) := Matrix I I ℂ

variable {I O E : Type*} [Fintype I] [Fintype O] [Fintype E]
  [DecidableEq I] [DecidableEq O] [DecidableEq E]

abbrev IsDensity (A : Mat I) : Prop :=
  QuantumProver.SuperchannelDiscrimination.FlaggedStates.IsDensity A

abbrev Density (I : Type*) [Fintype I] [DecidableEq I] :=
  {A : Mat I // IsDensity A}

abbrev entropyBits (A : Mat I) : ℝ :=
  QuantumProver.SuperchannelDiscrimination.FlaggedStates.entropyBits A

def sqrtPSD (A : Mat I) : Mat I := CFC.sqrt A

def traceNorm (A : Mat I) : ℝ := (CFC.sqrt (Aᴴ * A)).trace.re

def affinity (A B : Mat I) : ℝ := (sqrtPSD A * sqrtPSD B).trace.re

def rootFidelity (A B : Mat I) : ℝ := traceNorm (sqrtPSD A * sqrtPSD B)

def binaryHolevo (A B : Mat I) : ℝ :=
  entropyBits ((1 / 2 : ℝ) • (A + B)) - (entropyBits A + entropyBits B) / 2

def pairCost (A B : Mat I) : ℝ := 1 - binaryHolevo A B

def binaryEntropy (p : ℝ) : ℝ :=
  -(p * Real.log p + (1 - p) * Real.log (1 - p)) / Real.log 2

def phi (v : ℝ) : ℝ := binaryEntropy ((1 + Real.sqrt (1 - v)) / 2)

theorem log_two_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)

theorem equalPriorAverage_isDensity {A B : Mat I}
    (hA : IsDensity A) (hB : IsDensity B) :
    IsDensity ((1 / 2 : ℝ) • (A + B)) := by
  refine ⟨(hA.1.add hB.1).smul (by norm_num), ?_⟩
  simp [Matrix.trace_smul, Matrix.trace_add, hA.2, hB.2] <;> norm_num

def partialTraceRight (A : Mat (I × E)) : Mat I :=
  fun i j => ∑ e : E, A (i, e) (j, e)

def partialTraceLeft (A : Mat (I × E)) : Mat E :=
  fun e f => ∑ i : I, A (i, e) (i, f)

def partialTraceRightLM : Mat (I × E) →ₗ[ℂ] Mat I where
  toFun := partialTraceRight
  map_add' A B := by ext i j; simp [partialTraceRight, Finset.sum_add_distrib]
  map_smul' r A := by ext i j; simp [partialTraceRight, Finset.mul_sum, smul_eq_mul]

theorem partialTraceRight_trace (A : Mat (I × E)) :
    (partialTraceRight A).trace = A.trace := by
  simp [partialTraceRight, Matrix.trace, Fintype.sum_prod_type]

theorem partialTraceRight_posSemidef {A : Mat (I × E)} (hA : A.PosSemidef) :
    (partialTraceRight A).PosSemidef := by
  have heq : partialTraceRight A =
      ∑ e : E, A.submatrix (fun i : I => (i, e)) (fun i : I => (i, e)) := by
    ext i j
    exact (Matrix.sum_apply i j Finset.univ
      (fun e : E => A.submatrix (fun i : I => (i, e)) (fun i : I => (i, e)))).symm
  rw [heq]
  exact Matrix.posSemidef_sum _ (fun e _ => hA.submatrix (fun i : I => (i, e)))

theorem partialTraceRight_isDensity {A : Mat (I × E)} (hA : IsDensity A) :
    IsDensity (partialTraceRight A) :=
  ⟨partialTraceRight_posSemidef hA.1, (partialTraceRight_trace A).trans hA.2⟩

def amplify (Φ : Mat I →ₗ[ℂ] Mat O) (R : Type*) [Fintype R]
    (A : Mat (I × R)) : Mat (O × R) :=
  fun x y => Φ (fun i j => A (i, x.2) (j, y.2)) x.1 y.1

def CompletelyPositive (Φ : Mat I →ₗ[ℂ] Mat O) : Prop :=
  ∀ r : ℕ, ∀ A : Mat (I × Fin r), A.PosSemidef → (amplify Φ (Fin r) A).PosSemidef

def TracePreserving (Φ : Mat I →ₗ[ℂ] Mat O) : Prop :=
  ∀ A : Mat I, (Φ A).trace = A.trace

structure Channel (I O : Type*) [Fintype I] [Fintype O]
    [DecidableEq I] [DecidableEq O] where
  map : Mat I →ₗ[ℂ] Mat O
  completelyPositive : CompletelyPositive map
  tracePreserving : TracePreserving map

theorem Channel.posSemidef (N : Channel I O) {A : Mat I} (hA : A.PosSemidef) :
    (N.map A).PosSemidef := by
  have h := N.completelyPositive 1
    (A.submatrix (fun x : I × Fin 1 => x.1) (fun x : I × Fin 1 => x.1))
    (hA.submatrix (fun x : I × Fin 1 => x.1))
  have hp := h.submatrix (fun o : O => (o, (0 : Fin 1)))
  have heq :
      (amplify N.map (Fin 1)
        (A.submatrix (fun x : I × Fin 1 => x.1) (fun x : I × Fin 1 => x.1))).submatrix
        (fun o : O => (o, (0 : Fin 1))) (fun o : O => (o, (0 : Fin 1))) = N.map A := by
    ext i j
    rfl
  rw [heq] at hp
  exact hp

theorem Channel.isDensity (N : Channel I O) {A : Mat I} (hA : IsDensity A) :
    IsDensity (N.map A) :=
  ⟨N.posSemidef hA.1, (N.tracePreserving A).trans hA.2⟩

theorem partialTraceRight_completelyPositive :
    CompletelyPositive (partialTraceRightLM (I := I) (E := E)) := by
  intro r A hA
  have heq : amplify (partialTraceRightLM (I := I) (E := E)) (Fin r) A =
      ∑ e : E, A.submatrix (fun x : I × Fin r => ((x.1, e), x.2))
        (fun x : I × Fin r => ((x.1, e), x.2)) := by
    ext x y
    change (∑ e : E, A ((x.1, e), x.2) ((y.1, e), y.2)) = _
    exact (Matrix.sum_apply x y Finset.univ
      (fun e : E => A.submatrix (fun x : I × Fin r => ((x.1, e), x.2))
        (fun x : I × Fin r => ((x.1, e), x.2)))).symm
  rw [heq]
  exact Matrix.posSemidef_sum _
    (fun e _ => hA.submatrix (fun x : I × Fin r => ((x.1, e), x.2)))

def partialTraceRightChannel : Channel (I × E) I where
  map := partialTraceRightLM
  completelyPositive := partialTraceRight_completelyPositive
  tracePreserving := partialTraceRight_trace

def ket00 : AB → ℂ := fun x => if x = (0, 0) then 1 else 0
def ket11 : AB → ℂ := fun x => if x = (1, 1) then 1 else 0
def evenVector : AB → ℂ := ket00 + ket11

def outer (v : I → ℂ) : Mat I := Matrix.vecMulVec v (star v)

def bellEdge (c : ℝ) : Mat AB :=
  ((1 - c) / 2) • (outer ket00 + outer ket11) + (c / 2) • outer evenVector

theorem bellEdge_posSemidef {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    (bellEdge c).PosSemidef := by
  unfold bellEdge
  have hfirst : (((1 - c) / 2 : ℝ) • (outer ket00 + outer ket11)).PosSemidef :=
    ((Matrix.posSemidef_vecMulVec_self_star ket00).add
    (Matrix.posSemidef_vecMulVec_self_star ket11)).smul
      (div_nonneg (sub_nonneg.mpr hc1) (by norm_num))
  exact hfirst.add ((Matrix.posSemidef_vecMulVec_self_star evenVector).smul
    (div_nonneg hc0 (by norm_num)))

theorem bellEdge_trace (c : ℝ) : (bellEdge c).trace = 1 := by
  norm_num [bellEdge, outer, evenVector, ket00, ket11, Matrix.trace,
    Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.vecMulVec] <;> push_cast <;> ring

theorem bellEdge_isDensity {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    IsDensity (bellEdge c) := ⟨bellEdge_posSemidef hc0 hc1, bellEdge_trace c⟩

theorem bellEdge_offDiagonal (c : ℝ) :
    bellEdge c (0, 0) (1, 1) = ((c / 2 : ℝ) : ℂ) := by
  simp [bellEdge, outer, evenVector, ket00, ket11, Matrix.vecMulVec]

def marginalAE (ω : Mat (AB × E)) : Mat (Qubit × E) :=
  fun x y => ∑ b : Qubit, ω ((x.1, b), x.2) ((y.1, b), y.2)

def marginalBE (ω : Mat (AB × E)) : Mat (Qubit × E) :=
  fun x y => ∑ a : Qubit, ω ((a, x.1), x.2) ((a, y.1), y.2)

def marginalE (ω : Mat (AB × E)) : Mat E := partialTraceLeft ω

def halfCMI (ω : Mat (AB × E)) : ℝ :=
  (entropyBits (marginalAE ω) + entropyBits (marginalBE ω) -
    entropyBits (marginalE ω) - entropyBits ω) / 2

def extensionCosts (c : ℝ) : Set ℝ :=
  {z | ∃ n : ℕ, 0 < n ∧ ∃ ω : Density (AB × Fin n),
    partialTraceRight ω.val = bellEdge c ∧ z = halfCMI ω.val}

def squashedEntanglement (c : ℝ) : ℝ := sInf (extensionCosts c)

def finitePairCosts (c : ℝ) : Set ℝ :=
  {z | ∃ n : ℕ, 0 < n ∧ ∃ A B : Density (Fin n),
    affinity A.val B.val = c ∧ z = pairCost A.val B.val}

def positivePairInfimum (c : ℝ) : ℝ := sInf (finitePairCosts c)

def pairKernel (A B : Mat E) : Matrix (AB × E) E ℂ :=
  fun x j => if x.1 = (0, 0) then sqrtPSD A x.2 j
    else if x.1 = (1, 1) then sqrtPSD B x.2 j else 0

def pairGram (A B : Mat E) : Mat (AB × E) :=
  (1 / 2 : ℝ) • (pairKernel A B * (pairKernel A B)ᴴ)

theorem pairGram_posSemidef (A B : Mat E) : (pairGram A B).PosSemidef := by
  exact (Matrix.posSemidef_self_mul_conjTranspose (pairKernel A B)).smul (by norm_num)

structure POVM (I K : Type*) [Fintype I] [Fintype K] [DecidableEq I] where
  effect : K → Mat I
  positive : ∀ k, (effect k).PosSemidef
  normalized : ∑ k, effect k = 1

def measurementProbability {K : Type*} [Fintype K] (M : POVM I K)
    (A : Mat I) (k : K) : ℝ := (A * M.effect k).trace.re

def classicalRelativeEntropyBits {K : Type*} [Fintype K] (p q : K → ℝ) : EReal :=
  ∑ k, if p k = 0 then 0 else if q k = 0 then ⊤
    else ((p k * (Real.log (p k) - Real.log (q k)) / Real.log 2 : ℝ) : EReal)

def measuredRelativeEntropyBits (A B : Mat I) : EReal :=
  sSup {z | ∃ m : ℕ, 0 < m ∧ ∃ M : POVM I (Fin m),
    z = classicalRelativeEntropyBits (measurementProbability M A) (measurementProbability M B)}

def PhysicalSmallCoherenceBound : Prop :=
  ∀ c : ℝ, 0 < c → c ≤ 1 / 4 →
    c ^ 2 * Real.log (1 / (4 * c)) / (2 * Real.log 2) ≤ squashedEntanglement c ∧
    squashedEntanglement c ≤ phi (c ^ 2)

def UniversalHolevoFidelityLoss : Prop :=
  ∀ n m : ℕ, 0 < n → 0 < m → ∀ A B : Density (Fin n),
    ∀ N : Channel (Fin n) (Fin m),
      (rootFidelity (N.map A.val) (N.map B.val) - rootFidelity A.val B.val) ^ 2 ≤
        4 * Real.log 2 * (binaryHolevo A.val B.val - binaryHolevo (N.map A.val) (N.map B.val))

end QuantumProver.BellDiagonalSquashedEntanglement

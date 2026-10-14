import Mathlib

noncomputable section

namespace QuantumProver.Equipartition.FiniteModel

open scoped BigOperators ComplexOrder
open Matrix

abbrev CMat (ι : Type*) := Matrix ι ι ℂ
abbrev Word (d n : ℕ) := Fin n → Fin d
abbrev QMat (d n : ℕ) := CMat (Word d n)

section MatrixModel

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def IsState (ρ : CMat ι) : Prop := ρ.PosSemidef ∧ Matrix.trace ρ = 1

def IsEffect (Q : CMat ι) : Prop := Q.PosSemidef ∧ (1 - Q).PosSemidef

def tracePair (A B : CMat ι) : ℝ := (Matrix.trace (A * B)).re

def LoewnerLE (A B : CMat ι) : Prop := (B - A).PosSemidef

def SupportLE (ρ σ : CMat ι) : Prop :=
  ∀ v : ι → ℂ, σ.mulVec v = 0 → ρ.mulVec v = 0

def logTwo (x : ℝ) : ℝ := Real.log x / Real.log 2

def matrixLog (A : CMat ι) : CMat ι := cfc Real.log A

def matrixRpow (A : CMat ι) (t : ℝ) : CMat ι := cfc (fun x => Real.rpow x t) A

def matrixSupport (A : CMat ι) : CMat ι :=
  cfc (fun (x : ℝ) => if x = 0 then (0 : ℝ) else 1) A

def spectrumValue (A : CMat ι) (i : ι) : ℝ :=
  if h : A.IsHermitian then h.eigenvalues i else 0

def spectrumUnitary (A : CMat ι) : CMat ι :=
  if h : A.IsHermitian then (h.eigenvectorUnitary : CMat ι) else 1

theorem spectrumValue_of_isHermitian {A : CMat ι} (h : A.IsHermitian) (i : ι) :
    spectrumValue A i = h.eigenvalues i := by
  simp [spectrumValue, h]

theorem spectrumUnitary_of_isHermitian {A : CMat ι} (h : A.IsHermitian) :
    spectrumUnitary A = (h.eigenvectorUnitary : CMat ι) := by
  simp [spectrumUnitary, h]

theorem matrixLog_of_isHermitian {A : CMat ι} (h : A.IsHermitian) :
    matrixLog A = h.cfc Real.log := by
  exact h.cfc_eq Real.log

theorem matrixRpow_of_isHermitian {A : CMat ι} (h : A.IsHermitian) (t : ℝ) :
    matrixRpow A t = h.cfc (fun x => Real.rpow x t) := by
  exact h.cfc_eq (fun x => Real.rpow x t)

theorem IsState.isHermitian {ρ : CMat ι} (h : IsState ρ) : ρ.IsHermitian :=
  h.1.isHermitian

theorem IsState.trace_real {ρ : CMat ι} (h : IsState ρ) : (Matrix.trace ρ).re = 1 := by
  rw [h.2]
  rfl

theorem supportLE_self (A : CMat ι) : SupportLE A A := by
  intro v hv
  exact hv

theorem supportLE_trans {A B C : CMat ι} (hAB : SupportLE A B)
    (hBC : SupportLE B C) : SupportLE A C := by
  intro v hv
  exact hAB v (hBC v hv)

theorem supportLE_of_psd_domination {ρ σ : CMat ι} (hρ : ρ.PosSemidef)
    {a : ℂ} (hdom : LoewnerLE ρ (a • σ)) : SupportLE ρ σ := by
  intro v hv
  apply hρ.dotProduct_mulVec_zero_iff.mp
  have hn := hρ.dotProduct_mulVec_nonneg v
  have hd : (a • σ - ρ).PosSemidef := hdom
  have hneg : 0 ≤ -(star v ⬝ᵥ (ρ *ᵥ v)) := by
    simpa [sub_mulVec, smul_mulVec, hv, dotProduct_neg] using
      hd.dotProduct_mulVec_nonneg v
  exact le_antisymm (neg_nonneg.mp hneg) hn

def nsWeight (ρ σ : CMat ι) (z : ι × ι) : ℝ :=
  spectrumValue ρ z.1 *
    Complex.normSq (((spectrumUnitary ρ)ᴴ * spectrumUnitary σ) z.1 z.2)

def nsLikelihood (ρ σ : CMat ι) (z : ι × ι) : ℝ :=
  logTwo (spectrumValue ρ z.1) - logTwo (spectrumValue σ z.2)

def nsExpectation (ρ σ : CMat ι) (f : ι × ι → ℝ) : ℝ :=
  ∑ z, nsWeight ρ σ z * f z

def nsWeightedMoment (ρ σ : CMat ι) (centre t : ℝ) : ℝ :=
  nsExpectation ρ σ (fun z =>
    (nsLikelihood ρ σ z - centre) ^ 2 *
      Real.exp (t * |nsLikelihood ρ σ z - centre|))

def umegakiReal (ρ σ : CMat ι) : ℝ :=
  tracePair ρ (matrixLog ρ - matrixLog σ) / Real.log 2

def umegaki (ρ σ : CMat ι) : EReal := by
  classical
  exact if SupportLE ρ σ then (umegakiReal ρ σ : EReal) else ⊤

theorem umegaki_of_support {ρ σ : CMat ι} (hs : SupportLE ρ σ) :
    umegaki ρ σ = (umegakiReal ρ σ : EReal) := by
  simp [umegaki, hs]

theorem umegaki_finite_of_domination {ρ σ : CMat ι} (hρ : ρ.PosSemidef)
    {a : ℂ} (hdom : LoewnerLE ρ (a • σ)) :
    umegaki ρ σ ≠ ⊤ ∧ umegaki ρ σ ≠ ⊥ := by
  rw [umegaki_of_support (supportLE_of_psd_domination hρ hdom)]
  simp

def petzTrace (ρ σ : CMat ι) (α : ℝ) : ℝ :=
  tracePair (matrixRpow ρ α) (matrixRpow σ (1 - α))

def sandwichedTrace (ρ σ : CMat ι) (α : ℝ) : ℝ :=
  let S := matrixRpow σ ((1 - α) / (2 * α))
  (Matrix.trace (matrixRpow (S * ρ * S) α)).re

def petzDivergence (ρ σ : CMat ι) (α : ℝ) : EReal := by
  classical
  exact if α = 1 then umegaki ρ σ
  else if 1 < α ∧ ¬SupportLE ρ σ then ⊤
  else if petzTrace ρ σ α = 0 then ⊤
  else (logTwo (petzTrace ρ σ α) / (α - 1) : EReal)

def sandwichedDivergence (ρ σ : CMat ι) (α : ℝ) : EReal := by
  classical
  exact if α = 1 then umegaki ρ σ
  else if 1 < α ∧ ¬SupportLE ρ σ then ⊤
  else if sandwichedTrace ρ σ α = 0 then ⊤
  else (logTwo (sandwichedTrace ρ σ α) / (α - 1) : EReal)

def testingCosts (ε : ℝ) (ρ σ : CMat ι) : Set ℝ :=
  {b | ∃ Q : CMat ι, IsEffect Q ∧ 1 - ε ≤ tracePair ρ Q ∧ b = tracePair σ Q}

def testingBeta (ε : ℝ) (ρ σ : CMat ι) : ℝ := sInf (testingCosts ε ρ σ)

def testingDivergence (ε : ℝ) (ρ σ : CMat ι) : EReal :=
  if testingBeta ε ρ σ = 0 then ⊤ else (-logTwo (testingBeta ε ρ σ) : EReal)

def positivePolar (S : Set (CMat ι)) : Set (CMat ι) :=
  {X | X.PosSemidef ∧ ∀ Y ∈ S, tracePair Y X ≤ 1}

theorem isEffect_one : IsEffect (1 : CMat ι) := by
  refine ⟨Matrix.PosSemidef.one, ?_⟩
  simpa using (Matrix.PosSemidef.zero : (0 : CMat ι).PosSemidef)

theorem tracePair_one_right (A : CMat ι) : tracePair A 1 = (Matrix.trace A).re := by
  simp [tracePair]

theorem testingCosts_nonempty {ε : ℝ} (hε : 0 ≤ ε) {ρ σ : CMat ι}
    (hρ : IsState ρ) : (testingCosts ε ρ σ).Nonempty := by
  refine ⟨tracePair σ 1, 1, isEffect_one, ?_, rfl⟩
  rw [tracePair_one_right, hρ.trace_real]
  linarith

structure FinitePOVM (ι : Type*) [Fintype ι] [DecidableEq ι] (L : ℕ) where
  outcome : Fin L → CMat ι
  positive : ∀ i, (outcome i).PosSemidef
  sum_outcome : ∑ i, outcome i = 1

def measurementMass {L : ℕ} (M : FinitePOVM ι L) (ρ : CMat ι) : Fin L → ℝ :=
  fun i => tracePair ρ (M.outcome i)

def classicalSupportLE {L : ℕ} (p q : Fin L → ℝ) : Prop :=
  ∀ i, q i = 0 → p i = 0

def classicalUmegaki {L : ℕ} (p q : Fin L → ℝ) : EReal := by
  classical
  exact if classicalSupportLE p q then
    ((∑ i, p i * (logTwo (p i) - logTwo (q i)) : ℝ) : EReal) else ⊤

def classicalRenyiTrace {L : ℕ} (p q : Fin L → ℝ) (α : ℝ) : ℝ :=
  ∑ i, Real.rpow (p i) α * Real.rpow (q i) (1 - α)

def classicalRenyiDivergence {L : ℕ} (p q : Fin L → ℝ) (α : ℝ) : EReal := by
  classical
  exact if α = 1 then classicalUmegaki p q
  else if 1 < α ∧ ¬classicalSupportLE p q then ⊤
  else if classicalRenyiTrace p q α = 0 then ⊤
  else (logTwo (classicalRenyiTrace p q α) / (α - 1) : EReal)

def measuredDivergence (ρ σ : CMat ι) (α : ℝ) : EReal :=
  sSup {a | ∃ L : ℕ, ∃ M : FinitePOVM ι L,
    a = classicalRenyiDivergence (measurementMass M ρ) (measurementMass M σ) α}

end MatrixModel

section TensorModel

def tensorMatrix {d m n : ℕ} (A : QMat d m) (B : QMat d n) : QMat d (m + n) :=
  fun x y =>
    A (fun i => x (Fin.castAdd n i)) (fun i => y (Fin.castAdd n i)) *
      B (fun j => x (Fin.natAdd m j)) (fun j => y (Fin.natAdd m j))

def sitePermute {d n : ℕ} (p : Equiv.Perm (Fin n)) (A : QMat d n) : QMat d n :=
  fun x y => A (fun i => x (p i)) (fun i => y (p i))

def partialTraceRight {ι κ : Type*} [Fintype κ] (A : CMat (ι × κ)) : CMat ι :=
  fun i j => ∑ k, A (i, k) (j, k)

structure QuantumFamilies (d : ℕ) where
  null : (n : ℕ) → Set (QMat d n)
  alternative : (n : ℕ) → Set (QMat d n)

structure PhysicalAssumptions {d : ℕ} (F : QuantumFamilies d) : Prop where
  null_nonempty : ∀ n, 0 < n → (F.null n).Nonempty
  alternative_nonempty : ∀ n, 0 < n → (F.alternative n).Nonempty
  null_states : ∀ n, 0 < n → ∀ ρ ∈ F.null n, IsState ρ
  alternative_positive : ∀ n, 0 < n → ∀ σ ∈ F.alternative n, σ.PosSemidef
  null_compact : ∀ n, 0 < n → IsCompact (F.null n)
  alternative_compact : ∀ n, 0 < n → IsCompact (F.alternative n)
  null_convex : ∀ n, 0 < n → Convex ℝ (F.null n)
  alternative_convex : ∀ n, 0 < n → Convex ℝ (F.alternative n)
  null_permutation : ∀ n, 0 < n → ∀ p : Equiv.Perm (Fin n),
    ∀ ρ ∈ F.null n, sitePermute p ρ ∈ F.null n
  alternative_permutation : ∀ n, 0 < n → ∀ p : Equiv.Perm (Fin n),
    ∀ σ ∈ F.alternative n, sitePermute p σ ∈ F.alternative n
  null_tensor : ∀ m n, 0 < m → 0 < n → ∀ ρ ∈ F.null m,
    ∀ τ ∈ F.null n, tensorMatrix ρ τ ∈ F.null (m + n)
  alternative_tensor : ∀ m n, 0 < m → 0 < n → ∀ σ ∈ F.alternative m,
    ∀ τ ∈ F.alternative n, tensorMatrix σ τ ∈ F.alternative (m + n)
  null_polar_tensor : ∀ m n, 0 < m → 0 < n → ∀ X ∈ positivePolar (F.null m),
    ∀ Y ∈ positivePolar (F.null n), tensorMatrix X Y ∈ positivePolar (F.null (m + n))
  alternative_polar_tensor : ∀ m n, 0 < m → 0 < n →
    ∀ X ∈ positivePolar (F.alternative m), ∀ Y ∈ positivePolar (F.alternative n),
      tensorMatrix X Y ∈ positivePolar (F.alternative (m + n))
  linear_growth : ∃ C : ℝ, ∀ n, 0 < n → ∀ ρ ∈ F.null n,
    ∀ σ ∈ F.alternative n,
      LoewnerLE ρ ((Real.rpow 2 (C * (n : ℝ)) : ℂ) • σ) ∧
        logTwo (Matrix.trace σ).re ≤ C * (n : ℝ)

theorem physical_pair_umegaki_finite {d : ℕ} {F : QuantumFamilies d}
    (hF : PhysicalAssumptions F) {n : ℕ} (hn : 0 < n)
    {ρ σ : QMat d n} (hρ : ρ ∈ F.null n) (hσ : σ ∈ F.alternative n) :
    umegaki ρ σ ≠ ⊤ ∧ umegaki ρ σ ≠ ⊥ := by
  obtain ⟨C, hC⟩ := hF.linear_growth
  exact umegaki_finite_of_domination (hF.null_states n hn ρ hρ).1
    (hC n hn ρ hρ σ hσ).1

def setUmegaki {d : ℕ} (F : QuantumFamilies d) (n : ℕ) : EReal :=
  sInf {a | ∃ ρ ∈ F.null n, ∃ σ ∈ F.alternative n, a = umegaki ρ σ}

def setTestingDivergence {d : ℕ} (F : QuantumFamilies d) (n : ℕ) (ε : ℝ) : EReal :=
  sInf {a | ∃ ρ ∈ F.null n, ∃ σ ∈ F.alternative n, a = testingDivergence ε ρ σ}

def setPetzDivergence {d : ℕ} (F : QuantumFamilies d) (n : ℕ) (α : ℝ) : EReal :=
  sInf {a | ∃ ρ ∈ F.null n, ∃ σ ∈ F.alternative n, a = petzDivergence ρ σ α}

def setSandwichedDivergence {d : ℕ} (F : QuantumFamilies d) (n : ℕ) (α : ℝ) : EReal :=
  sInf {a | ∃ ρ ∈ F.null n, ∃ σ ∈ F.alternative n, a = sandwichedDivergence ρ σ α}

def setMeasuredDivergence {d : ℕ} (F : QuantumFamilies d) (n : ℕ) (α : ℝ) : EReal :=
  sInf {a | ∃ ρ ∈ F.null n, ∃ σ ∈ F.alternative n, a = measuredDivergence ρ σ α}

def entropyRates {d : ℕ} (F : QuantumFamilies d) : Set ℝ :=
  {r | ∃ n : ℕ, 0 < n ∧ r = (setUmegaki F n).toReal / (n : ℝ)}

def regularizedRate {d : ℕ} (F : QuantumFamilies d) : ℝ := sInf (entropyRates F)

def IsExactMinimizer {d n : ℕ} (F : QuantumFamilies d) (ρ σ : QMat d n) : Prop :=
  ρ ∈ F.null n ∧ σ ∈ F.alternative n ∧ umegaki ρ σ = setUmegaki F n

def pinchingOverhead (d n : ℕ) : ℝ :=
  2 * ((d : ℝ) ^ 2 + (d : ℝ)) * logTwo ((n : ℝ) + (d : ℝ))

def blockLog (n : ℕ) : ℝ := logTwo ((n : ℝ) + 1)

def testingRemainder (n : ℕ) : ℝ :=
  Real.sqrt (n : ℝ) * Real.rpow (blockLog n) (3 / 2 : ℝ)

theorem entropyRate_mem {d : ℕ} (F : QuantumFamilies d) {n : ℕ} (hn : 0 < n) :
    (setUmegaki F n).toReal / (n : ℝ) ∈ entropyRates F :=
  ⟨n, hn, rfl⟩

end TensorModel

end QuantumProver.Equipartition.FiniteModel

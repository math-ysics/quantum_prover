import QuantumProver.InformationTheory.DepolarizingPrivateInformation.PauliEntropyBounds
import QuantumProver.InformationTheory.DepolarizingPrivateInformation.PrivateInformationBounds

noncomputable section

namespace QuantumProver.DepolarizingPrivateInformation

open scoped BigOperators ComplexOrder
open Matrix

abbrev QubitWord (n : ℕ) := Fin n → Qubit
abbrev ErrorWord (n : ℕ) := Fin n → PauliIndex
abbrev PairQubit := Qubit × Qubit

def logTwo (x : ℝ) : ℝ := Real.log x / Real.log 2

def matrixEntropy {ι : Type*} [Fintype ι] [DecidableEq ι] (ρ : CMat ι) : ℝ :=
  if h : ρ.IsHermitian then
    - ∑ i, h.eigenvalues i * logTwo (h.eigenvalues i)
  else 0

theorem matrixEntropy_of_isHermitian {ι : Type*} [Fintype ι] [DecidableEq ι]
    {ρ : CMat ι} (h : ρ.IsHermitian) :
    matrixEntropy ρ = - ∑ i, h.eigenvalues i * logTwo (h.eigenvalues i) := by
  simp [matrixEntropy, h]

structure FiniteEnsemble (ι : Type*) [Fintype ι] (L : ℕ) where
  weight : Fin L → ℝ
  weight_nonneg : ∀ x, 0 ≤ weight x
  weight_sum : ∑ x, weight x = 1
  state : Fin L → Density ι

def ensembleMean {ι : Type*} [Fintype ι] {L : ℕ}
    (E : FiniteEnsemble ι L) : CMat ι :=
  ∑ x, (E.weight x : ℂ) • (E.state x).mat

def tensorKraus (p : ℝ) (n : ℕ) (e : ErrorWord n) : CMat (QubitWord n) :=
  fun x y => ∏ i, kraus p (e i) (x i) (y i)

def bobTensorChannel (p : ℝ) (n : ℕ)
    (ρ : CMat (QubitWord n)) : CMat (QubitWord n) :=
  ∑ e, tensorKraus p n e * ρ * (tensorKraus p n e)ᴴ

def eveTensorChannel (p : ℝ) (n : ℕ)
    (ρ : CMat (QubitWord n)) : CMat (ErrorWord n) :=
  fun e f => Matrix.trace (tensorKraus p n e * ρ * (tensorKraus p n f)ᴴ)

def channelHolevo {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    {L : ℕ} (Φ : CMat ι → CMat κ) (E : FiniteEnsemble ι L) : ℝ :=
  matrixEntropy (Φ (ensembleMean E)) -
    ∑ x, E.weight x * matrixEntropy (Φ (E.state x).mat)

def privateInformation (p : ℝ) (n : ℕ) {L : ℕ}
    (E : FiniteEnsemble (QubitWord n) L) : ℝ :=
  channelHolevo (bobTensorChannel p n) E -
    channelHolevo (eveTensorChannel p n) E

def privateRates (p : ℝ) : Set ℝ :=
  {r | ∃ (n L : ℕ) (E : FiniteEnsemble (QubitWord n) L),
    0 < n ∧ r = privateInformation p n E / (n : ℝ)}

def privateCapacity (p : ℝ) : ℝ := sSup (privateRates p)

theorem finite_ensemble_rate_mem (p : ℝ) (n L : ℕ)
    (E : FiniteEnsemble (QubitWord n) L) (hn : 0 < n) :
    privateInformation p n E / (n : ℝ) ∈ privateRates p := by
  exact ⟨n, L, E, hn, rfl⟩

def spinSign (b : Qubit) : ℝ := if b = 0 then 1 else -1

def correlatedMass (u v : ℝ) (x : PairQubit) : ℝ :=
  (1 + u * spinSign x.1 * spinSign x.2 +
    v * (spinSign x.1 + spinSign x.2)) / 4

def twoUseRho (u v : ℝ) : CMat PairQubit :=
  Matrix.diagonal (fun x => (correlatedMass u v x : ℂ))

theorem correlatedMass_sum (u v : ℝ) :
    ∑ x, correlatedMass u v x = 1 := by
  simp [Fintype.sum_prod_type, Fin.sum_univ_two, correlatedMass, spinSign]
  <;> ring

theorem twoUseRho_trace (u v : ℝ) : Matrix.trace (twoUseRho u v) = 1 := by
  simp only [twoUseRho, Matrix.trace_diagonal]
  exact_mod_cast correlatedMass_sum u v

theorem correlatedMass_nonneg {u v : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (hv : 2 * |v| ≤ 1 - u) (x : PairQubit) :
    0 ≤ correlatedMass u v x := by
  have hv0 : 0 ≤ |v| := abs_nonneg v
  have hvplus : v ≤ |v| := le_abs_self v
  have hvminus : -v ≤ |v| := neg_le_abs v
  rcases x with ⟨x, y⟩
  fin_cases x <;> fin_cases y <;>
    norm_num [correlatedMass, spinSign] <;> linarith

theorem twoUseRho_psd {u v : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (hv : 2 * |v| ≤ 1 - u) : (twoUseRho u v).PosSemidef := by
  apply Matrix.PosSemidef.diagonal
  intro x
  exact Complex.zero_le_real.mpr (correlatedMass_nonneg hu0 hu1 hv x)

def twoUseDensity (u v : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (hv : 2 * |v| ≤ 1 - u) : Density PairQubit where
  mat := twoUseRho u v
  psd := twoUseRho_psd hu0 hu1 hv
  trace_one := twoUseRho_trace u v

def evenSite (m : ℕ) (j : Fin m) : Fin (2 * m) := ⟨2 * j.val, by omega⟩
def oddSite (m : ℕ) (j : Fin m) : Fin (2 * m) := ⟨2 * j.val + 1, by omega⟩

def repeatedTwoUseRho (u v : ℝ) (m : ℕ) : CMat (QubitWord (2 * m)) :=
  fun x y => ∏ j, twoUseRho u v
    (x (evenSite m j), x (oddSite m j))
    (y (evenSite m j), y (oddSite m j))

def signedRepeatedInput (u v : ℝ) (m : ℕ) (x : Fin 2) :
    CMat (QubitWord (2 * m)) :=
  repeatedTwoUseRho u (if x = 0 then v else -v) m

def savedBinaryPrivateInformation (p u v : ℝ) (m : ℕ) : ℝ :=
  let Rplus := repeatedTwoUseRho u v m
  let Rminus := repeatedTwoUseRho u (-v) m
  let Rmean := (1 / 2 : ℂ) • (Rplus + Rminus)
  (matrixEntropy (bobTensorChannel p (2 * m) Rmean) -
    (matrixEntropy (bobTensorChannel p (2 * m) Rplus) +
      matrixEntropy (bobTensorChannel p (2 * m) Rminus)) / 2) -
  (matrixEntropy (eveTensorChannel p (2 * m) Rmean) -
    (matrixEntropy (eveTensorChannel p (2 * m) Rplus) +
      matrixEntropy (eveTensorChannel p (2 * m) Rminus)) / 2)

theorem correlatedMass_pos {u v : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1)
    (hv : 2 * |v| < 1 - u) (x : PairQubit) :
    0 < correlatedMass u v x := by
  have hv0 : 0 ≤ |v| := abs_nonneg v
  have hvplus : v ≤ |v| := le_abs_self v
  have hvminus : -v ≤ |v| := neg_le_abs v
  rcases x with ⟨x, y⟩
  fin_cases x <;> fin_cases y <;>
    norm_num [correlatedMass, spinSign] <;> linarith

theorem twoUseRho_posDef {u v : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1)
    (hv : 2 * |v| < 1 - u) : (twoUseRho u v).PosDef := by
  apply Matrix.PosDef.diagonal
  intro x
  exact Complex.zero_lt_real.mpr (correlatedMass_pos hu0 hu1 hv x)

end QuantumProver.DepolarizingPrivateInformation

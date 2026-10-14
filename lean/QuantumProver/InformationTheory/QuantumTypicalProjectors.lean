import QuantumProver.InformationTheory.QuantumEntropy.Definitions
import QuantumProver.InformationTheory.SuperchannelDiscrimination.TestingTheorems
import QuantumProver.InformationTheory.SuperchannelDiscrimination.PetzSmoothing

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option maxRecDepth 4000

noncomputable section

namespace QuantumProver.QuantumTypicalProjectors

open Matrix Filter
open QuantumProver.SuperchannelDiscrimination
open scoped BigOperators Topology ComplexOrder MatrixOrder Matrix Kronecker

variable {I : Type*} [Fintype I] [DecidableEq I]

local instance (p : Prop) : Decidable p := Classical.propDecidable p

abbrev Word (I : Type*) (n : ℕ) := Fin n → I

def iidWeight (p : I → ℝ) (n : ℕ) (x : Word I n) : ℝ := ∏ j, p (x j)

def iidSum (f : I → ℝ) (n : ℕ) (x : Word I n) : ℝ := ∑ j, f (x j)

theorem iidWeight_nonneg (p : I → ℝ) (hp : ∀ i, 0 ≤ p i) (n : ℕ) (x : Word I n) :
    0 ≤ iidWeight p n x := Finset.prod_nonneg fun j _ => hp (x j)

theorem iidWeight_sum (p : I → ℝ) (hp : ∑ i, p i = 1) (n : ℕ) :
    ∑ x : Word I n, iidWeight p n x = 1 := by
  change (∑ x : Fin n → I, ∏ j, p (x j)) = 1
  rw [← Fintype.prod_sum]
  simp only [hp, Finset.prod_const_one]

theorem iidWeight_succ (p : I → ℝ) (n : ℕ) (x : Word I n) (i : I) :
    iidWeight p (n + 1) ((TensorPinching.rowsSuccEquiv I n).symm (x, i)) =
      iidWeight p n x * p i := by
  simp [iidWeight, TensorPinching.rowsSuccEquiv, Fin.prod_univ_castSucc]

theorem iidSum_succ (f : I → ℝ) (n : ℕ) (x : Word I n) (i : I) :
    iidSum f (n + 1) ((TensorPinching.rowsSuccEquiv I n).symm (x, i)) =
      iidSum f n x + f i := by
  simp [iidSum, TensorPinching.rowsSuccEquiv, Fin.sum_univ_castSucc]

theorem sum_words_succ (n : ℕ) (F : Word I (n + 1) → ℝ) :
    ∑ x, F x = ∑ x : Word I n, ∑ i : I, F ((TensorPinching.rowsSuccEquiv I n).symm (x, i)) := by
  calc
    (∑ x, F x) = ∑ p : Word I n × I, F ((TensorPinching.rowsSuccEquiv I n).symm p) :=
      ((TensorPinching.rowsSuccEquiv I n).symm.sum_comp F).symm
    _ = _ := Fintype.sum_prod_type _

def finiteIIDPMF (p : I → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i = 1)
    (n : ℕ) : PMF (Word I n) :=
  PMF.ofFintype (fun x => ENNReal.ofReal (iidWeight p n x)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun x _ => iidWeight_nonneg p hp0 n x)]
    simp only [iidWeight_sum p hp1 n, ENNReal.ofReal_one])

theorem finiteIIDPMF_apply (p : I → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i = 1)
    (n : ℕ) (x : Word I n) : finiteIIDPMF p hp0 hp1 n x = ENNReal.ofReal (iidWeight p n x) := rfl

theorem iid_centered_first_moment (p f : I → ℝ) (hp : ∑ i, p i = 1)
    (hf : ∑ i, p i * f i = 0) (n : ℕ) :
    ∑ x : Word I n, iidWeight p n x * iidSum f n x = 0 := by
  induction n with
  | zero => simp [iidSum]
  | succ n ih =>
      rw [sum_words_succ]
      simp only [iidWeight_succ, iidSum_succ]
      have hexpand (x : Word I n) (i : I) :
          iidWeight p n x * p i * (iidSum f n x + f i) =
            (iidWeight p n x * iidSum f n x) * p i + iidWeight p n x * (p i * f i) := by ring
      simp_rw [hexpand, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
      simp only [hp, hf, mul_one, mul_zero, add_zero, ih]

theorem iid_centered_second_moment (p f : I → ℝ) (hp : ∑ i, p i = 1)
    (hf : ∑ i, p i * f i = 0) (n : ℕ) :
    ∑ x : Word I n, iidWeight p n x * (iidSum f n x) ^ 2 =
      (n : ℝ) * ∑ i, p i * (f i) ^ 2 := by
  induction n with
  | zero => simp [iidSum]
  | succ n ih =>
      rw [sum_words_succ]
      simp only [iidWeight_succ, iidSum_succ]
      have hexpand (x : Word I n) (i : I) :
          iidWeight p n x * p i * (iidSum f n x + f i) ^ 2 =
            (iidWeight p n x * (iidSum f n x) ^ 2) * p i +
              (2 * (iidWeight p n x * iidSum f n x)) * (p i * f i) +
              iidWeight p n x * (p i * (f i) ^ 2) := by ring
      simp_rw [hexpand, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
      simp only [hp, hf, mul_one, mul_zero, add_zero, zero_add,
        iidWeight_sum p hp n, one_mul, ih, Nat.cast_add, Nat.cast_one]
      ring

def iidBadMass (p f : I → ℝ) (δ : ℝ) (n : ℕ) : ℝ :=
  ∑ x : Word I n, if (n : ℝ) * δ < |iidSum f n x| then iidWeight p n x else 0

theorem iidBadMass_nonneg (p f : I → ℝ) (hp : ∀ i, 0 ≤ p i) (δ : ℝ) (n : ℕ) :
    0 ≤ iidBadMass p f δ n := by
  apply Finset.sum_nonneg
  intro x hx
  split_ifs
  · exact iidWeight_nonneg p hp n x
  · exact le_rfl

theorem iidBadMass_chebyshev (p f : I → ℝ) (hp0 : ∀ i, 0 ≤ p i)
    (hp1 : ∑ i, p i = 1) (hf : ∑ i, p i * f i = 0)
    {δ : ℝ} (hδ : 0 < δ) {n : ℕ} (hn : 0 < n) :
    iidBadMass p f δ n ≤ (∑ i, p i * (f i) ^ 2) / ((n : ℝ) * δ ^ 2) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hsq : 0 < ((n : ℝ) * δ) ^ 2 := sq_pos_of_pos (mul_pos hnR hδ)
  have hmoment : iidBadMass p f δ n * ((n : ℝ) * δ) ^ 2 ≤
      (n : ℝ) * ∑ i, p i * (f i) ^ 2 := by
    rw [iidBadMass, Finset.sum_mul, ← iid_centered_second_moment p f hp1 hf n]
    apply Finset.sum_le_sum
    intro x hx
    split_ifs with h
    · have hs : ((n : ℝ) * δ) ^ 2 ≤ (iidSum f n x) ^ 2 := by
        have habs := sq_abs (iidSum f n x)
        have ha : 0 ≤ (n : ℝ) * δ := (mul_pos hnR hδ).le
        nlinarith [abs_nonneg (iidSum f n x)]
      exact mul_le_mul_of_nonneg_left hs (iidWeight_nonneg p hp0 n x)
    · simp only [zero_mul]
      exact mul_nonneg (iidWeight_nonneg p hp0 n x) (sq_nonneg _)
  calc
    iidBadMass p f δ n ≤ ((n : ℝ) * ∑ i, p i * (f i) ^ 2) / ((n : ℝ) * δ) ^ 2 :=
      (le_div_iff₀ hsq).mpr hmoment
    _ = (∑ i, p i * (f i) ^ 2) / ((n : ℝ) * δ ^ 2) := by
      field_simp [ne_of_gt hnR, ne_of_gt hδ] <;> ring

theorem iidBadMass_tendsto_zero (p f : I → ℝ) (hp0 : ∀ i, 0 ≤ p i)
    (hp1 : ∑ i, p i = 1) (hf : ∑ i, p i * f i = 0) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (iidBadMass p f δ) atTop (𝓝 0) := by
  have hlim : Tendsto (fun n : ℕ => (∑ i, p i * (f i) ^ 2) / ((n : ℝ) * δ ^ 2))
      atTop (𝓝 0) := by
    convert (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul
      ((∑ i, p i * (f i) ^ 2) / δ ^ 2) using 1
    · funext n
      simp only [div_eq_mul_inv, _root_.mul_inv_rev, one_mul]
      ring
    · simp
  apply squeeze_zero' (Eventually.of_forall (iidBadMass_nonneg p f hp0 δ)) _ hlim
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact iidBadMass_chebyshev p f hp0 hp1 hf hδ (by omega)

def eigenWeight {ρ : Matrix I I ℂ} (hρ : FlaggedStates.IsDensity ρ) (i : I) : ℝ :=
  hρ.1.1.eigenvalues i

theorem eigenWeight_nonneg {ρ : Matrix I I ℂ} (hρ : FlaggedStates.IsDensity ρ) (i : I) :
    0 ≤ eigenWeight hρ i := hρ.1.eigenvalues_nonneg i

theorem eigenWeight_sum {ρ : Matrix I I ℂ} (hρ : FlaggedStates.IsDensity ρ) :
    ∑ i, eigenWeight hρ i = 1 := by
  have h := congrArg Complex.re hρ.1.1.trace_eq_sum_eigenvalues
  calc
    (∑ i, eigenWeight hρ i) = ρ.trace.re := by
      simpa [eigenWeight] using h.symm
    _ = 1 := by simpa only [Complex.one_re] using congrArg Complex.re hρ.2

theorem unitary_conjugate_trace (U : Matrix.unitaryGroup I ℂ) (A : Matrix I I ℂ) :
    (Unitary.conjStarAlgAut ℝ (Matrix I I ℂ) U A).trace = A.trace := by
  change ((U : Matrix I I ℂ) * A * (U : Matrix I I ℂ)ᴴ).trace = A.trace
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc]
  have hU : (U : Matrix I I ℂ)ᴴ * (U : Matrix I I ℂ) = 1 := Unitary.coe_star_mul_self U
  rw [hU, Matrix.one_mul]

theorem entropyNats_eq_eigenWeight_sum {ρ : Matrix I I ℂ} (hρ : FlaggedStates.IsDensity ρ) :
    QuantumProver.QuantumEntropy.entropyNats ρ = -∑ i, eigenWeight hρ i * Real.log (eigenWeight hρ i) := by
  rw [QuantumProver.QuantumEntropy.entropyNats, PetzMoments.cfc_spectral _ hρ.1.1,
    unitary_conjugate_trace, Matrix.trace_diagonal]
  simp only [Complex.re_sum, Complex.ofReal_re, eigenWeight]

def centeredScore {ρ : Matrix I I ℂ} (hρ : FlaggedStates.IsDensity ρ) (i : I) : ℝ :=
  -Real.log (eigenWeight hρ i) - QuantumProver.QuantumEntropy.entropyNats ρ

def spectralVariance {ρ : Matrix I I ℂ} (hρ : FlaggedStates.IsDensity ρ) : ℝ :=
  ∑ i, eigenWeight hρ i * (centeredScore hρ i) ^ 2

theorem centeredScore_mean_zero {ρ : Matrix I I ℂ} (hρ : FlaggedStates.IsDensity ρ) :
    ∑ i, eigenWeight hρ i * centeredScore hρ i = 0 := by
  have hm : ∑ i, eigenWeight hρ i * (-Real.log (eigenWeight hρ i)) =
      QuantumProver.QuantumEntropy.entropyNats ρ := by
    simpa only [mul_neg, Finset.sum_neg_distrib] using (entropyNats_eq_eigenWeight_sum hρ).symm
  simp only [centeredScore, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul,
    eigenWeight_sum hρ, one_mul, hm, sub_self]

def iidSpectrumPMF {ρ : Matrix I I ℂ} (hρ : FlaggedStates.IsDensity ρ) (n : ℕ) :
    PMF (Word I n) := finiteIIDPMF (eigenWeight hρ) (eigenWeight_nonneg hρ) (eigenWeight_sum hρ) n

theorem spectral_iid_centered_weak_law {ρ : Matrix I I ℂ} (hρ : FlaggedStates.IsDensity ρ)
    {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (iidBadMass (eigenWeight hρ) (centeredScore hρ) δ) atTop (𝓝 0) :=
  iidBadMass_tendsto_zero _ _ (eigenWeight_nonneg hρ) (eigenWeight_sum hρ)
    (centeredScore_mean_zero hρ) hδ

def typicalWord {ρ : Matrix I I ℂ} (hρ : FlaggedStates.IsDensity ρ)
    (δ : ℝ) (n : ℕ) (x : Word I n) : Prop :=
  0 < iidWeight (eigenWeight hρ) n x ∧
    |-Real.log (iidWeight (eigenWeight hρ) n x) -
      (n : ℝ) * QuantumProver.QuantumEntropy.entropyNats ρ| ≤ (n : ℝ) * δ

def typicalMass {ρ : Matrix I I ℂ} (hρ : FlaggedStates.IsDensity ρ) (δ : ℝ) (n : ℕ) : ℝ := by
  classical
  exact ∑ x : Word I n, if typicalWord hρ δ n x then iidWeight (eigenWeight hρ) n x else 0

theorem centered_iidSum_eq_log_weight {ρ : Matrix I I ℂ} (hρ : FlaggedStates.IsDensity ρ)
    (n : ℕ) (x : Word I n) (hx : 0 < iidWeight (eigenWeight hρ) n x) :
    iidSum (centeredScore hρ) n x =
      -Real.log (iidWeight (eigenWeight hρ) n x) -
        (n : ℝ) * QuantumProver.QuantumEntropy.entropyNats ρ := by
  have hne (j : Fin n) (hj : j ∈ (Finset.univ : Finset (Fin n))) :
      eigenWeight hρ (x j) ≠ 0 := by
    intro hz
    have : iidWeight (eigenWeight hρ) n x = 0 := Finset.prod_eq_zero hj hz
    exact (ne_of_gt hx) this
  simp only [iidSum, centeredScore, Finset.sum_sub_distrib, Finset.sum_neg_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [iidWeight, Real.log_prod hne]

theorem typicalMass_add_badMass {ρ : Matrix I I ℂ} (hρ : FlaggedStates.IsDensity ρ)
    (δ : ℝ) (n : ℕ) :
    typicalMass hρ δ n + iidBadMass (eigenWeight hρ) (centeredScore hρ) δ n = 1 := by
  classical
  rw [typicalMass, iidBadMass, ← Finset.sum_add_distrib,
    ← iidWeight_sum (eigenWeight hρ) (eigenWeight_sum hρ) n]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases hp : 0 < iidWeight (eigenWeight hρ) n x
  · by_cases hs : |iidSum (centeredScore hρ) n x| ≤ (n : ℝ) * δ
    · simp [typicalWord, hp, ← centered_iidSum_eq_log_weight hρ n x hp,
        hs, not_lt.mpr hs]
    · have hs' : (n : ℝ) * δ < |iidSum (centeredScore hρ) n x| := lt_of_not_ge hs
      simp [typicalWord, hp, ← centered_iidSum_eq_log_weight hρ n x hp, hs, hs']
  · have hz : iidWeight (eigenWeight hρ) n x = 0 := le_antisymm (le_of_not_gt hp)
      (iidWeight_nonneg _ (eigenWeight_nonneg hρ) n x)
    simp [typicalWord, hp, hz]

theorem typicalMass_le_one {ρ : Matrix I I ℂ} (hρ : FlaggedStates.IsDensity ρ)
    (δ : ℝ) (n : ℕ) : typicalMass hρ δ n ≤ 1 := by
  have h := typicalMass_add_badMass hρ δ n
  have hb := iidBadMass_nonneg (eigenWeight hρ) (centeredScore hρ) (eigenWeight_nonneg hρ) δ n
  linarith

theorem typicalMass_tendsto_one {ρ : Matrix I I ℂ} (hρ : FlaggedStates.IsDensity ρ)
    {δ : ℝ} (hδ : 0 < δ) : Tendsto (typicalMass hρ δ) atTop (𝓝 1) := by
  have heq (n : ℕ) : typicalMass hρ δ n =
      1 - iidBadMass (eigenWeight hρ) (centeredScore hρ) δ n := by
    linarith [typicalMass_add_badMass hρ δ n]
  have hfun : typicalMass hρ δ = fun n =>
      1 - iidBadMass (eigenWeight hρ) (centeredScore hρ) δ n := funext heq
  rw [hfun]
  simpa only [sub_zero] using
    ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub
      (spectral_iid_centered_weak_law hρ hδ))

theorem typicalWord_eigenvalue_bounds {ρ : Matrix I I ℂ} (hρ : FlaggedStates.IsDensity ρ)
    {δ : ℝ} {n : ℕ} {x : Word I n} (hx : typicalWord hρ δ n x) :
    Real.exp (-(n : ℝ) * (QuantumProver.QuantumEntropy.entropyNats ρ + δ)) ≤
      iidWeight (eigenWeight hρ) n x ∧
      iidWeight (eigenWeight hρ) n x ≤
        Real.exp (-(n : ℝ) * (QuantumProver.QuantumEntropy.entropyNats ρ - δ)) := by
  obtain ⟨hp, hb⟩ := hx
  obtain ⟨hl, hu⟩ := abs_le.mp hb
  constructor
  · have hlog : -(n : ℝ) * (QuantumProver.QuantumEntropy.entropyNats ρ + δ) ≤
        Real.log (iidWeight (eigenWeight hρ) n x) := by nlinarith
    simpa only [Real.exp_log hp] using Real.exp_le_exp.mpr hlog
  · have hlog : Real.log (iidWeight (eigenWeight hρ) n x) ≤
        -(n : ℝ) * (QuantumProver.QuantumEntropy.entropyNats ρ - δ) := by nlinarith
    simpa only [Real.exp_log hp] using Real.exp_le_exp.mpr hlog

def wordUnitary {ρ : Matrix I I ℂ} (hρ : FlaggedStates.IsDensity ρ) (n : ℕ) :
    Matrix.unitaryGroup (Word I n) ℂ :=
  ⟨TensorPinching.tensorMatrix (fun _ => (hρ.1.1.eigenvectorUnitary : Matrix I I ℂ)), by
    apply Matrix.mem_unitaryGroup_iff.mpr
    change TensorPinching.tensorMatrix (fun _ : Fin n => (hρ.1.1.eigenvectorUnitary : Matrix I I ℂ)) *
      (TensorPinching.tensorMatrix (fun _ : Fin n => (hρ.1.1.eigenvectorUnitary : Matrix I I ℂ)))ᴴ = 1
    rw [TensorPinching.tensorMatrix_conjTranspose, TensorPinching.tensorMatrix_mul]
    have hU : (hρ.1.1.eigenvectorUnitary : Matrix I I ℂ) *
        (hρ.1.1.eigenvectorUnitary : Matrix I I ℂ)ᴴ = 1 :=
      Unitary.coe_mul_star_self hρ.1.1.eigenvectorUnitary
    simp only [hU, TensorPinching.tensorMatrix_one]⟩

def wordTypicalDiagonal {ρ : Matrix I I ℂ} (hρ : FlaggedStates.IsDensity ρ)
    (δ : ℝ) (n : ℕ) : Matrix (Word I n) (Word I n) ℂ := by
  classical
  exact Matrix.diagonal (fun x => if typicalWord hρ δ n x then 1 else 0)

def wordTypicalProjector {ρ : Matrix I I ℂ} (hρ : FlaggedStates.IsDensity ρ)
    (δ : ℝ) (n : ℕ) : Matrix (Word I n) (Word I n) ℂ :=
  Unitary.conjStarAlgAut ℝ _ (wordUnitary hρ n) (wordTypicalDiagonal hρ δ n)

def wordWeightDiagonal {ρ : Matrix I I ℂ} (hρ : FlaggedStates.IsDensity ρ) (n : ℕ) :
    Matrix (Word I n) (Word I n) ℂ :=
  Matrix.diagonal (fun x => (iidWeight (eigenWeight hρ) n x : ℂ))

theorem flatTensorPower_diagonal (p : I → ℝ) (n : ℕ) :
    TensorPinching.tensorPower (Matrix.diagonal (fun i => (p i : ℂ))) n =
      Matrix.diagonal (fun x : Word I n => (iidWeight p n x : ℂ)) := by
  ext x y
  by_cases hxy : x = y
  · subst y
    simp [TensorPinching.tensorPower, TensorPinching.tensorMatrix, iidWeight, Complex.ofReal_prod]
  · have hsome : ∃ j, x j ≠ y j := by
      by_contra hn
      apply hxy
      funext j
      by_contra hj
      exact hn ⟨j, hj⟩
    obtain ⟨j, hj⟩ := hsome
    simp only [Matrix.diagonal_apply_ne _ hxy]
    change (∏ a : Fin n, (Matrix.diagonal (fun i => (p i : ℂ))) (x a) (y a)) = 0
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    simp [Matrix.diagonal_apply, hj]

theorem wordTensorPower_spectral {ρ : Matrix I I ℂ} (hρ : FlaggedStates.IsDensity ρ) (n : ℕ) :
    TensorPinching.tensorPower ρ n =
      Unitary.conjStarAlgAut ℝ _ (wordUnitary hρ n) (wordWeightDiagonal hρ n) := by
  rw [wordWeightDiagonal, ← flatTensorPower_diagonal]
  change TensorPinching.tensorMatrix (fun _ : Fin n => ρ) =
    TensorPinching.tensorMatrix (fun _ : Fin n => (hρ.1.1.eigenvectorUnitary : Matrix I I ℂ)) *
      TensorPinching.tensorMatrix (fun _ : Fin n => Matrix.diagonal (fun i => (eigenWeight hρ i : ℂ))) *
      (TensorPinching.tensorMatrix (fun _ : Fin n => (hρ.1.1.eigenvectorUnitary : Matrix I I ℂ)))ᴴ
  rw [TensorPinching.tensorMatrix_conjTranspose, TensorPinching.tensorMatrix_mul,
    TensorPinching.tensorMatrix_mul]
  congr 1
  funext j
  exact hρ.1.1.spectral_theorem

theorem wordTypicalDiagonal_isProjection {ρ : Matrix I I ℂ} (hρ : FlaggedStates.IsDensity ρ)
    (δ : ℝ) (n : ℕ) : PetzSmoothing.IsProjection (wordTypicalDiagonal hρ δ n) := by
  classical
  constructor
  · simp [wordTypicalDiagonal, Matrix.IsHermitian, Matrix.diagonal_conjTranspose]
  · change Matrix.diagonal (fun x : Word I n => if typicalWord hρ δ n x then (1 : ℂ) else 0) *
        Matrix.diagonal (fun x : Word I n => if typicalWord hρ δ n x then (1 : ℂ) else 0) = _
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext x
    split_ifs <;> simp

theorem wordTypicalProjector_isProjection {ρ : Matrix I I ℂ} (hρ : FlaggedStates.IsDensity ρ)
    (δ : ℝ) (n : ℕ) : PetzSmoothing.IsProjection (wordTypicalProjector hρ δ n) := by
  let F := Unitary.conjStarAlgAut ℝ (Matrix (Word I n) (Word I n) ℂ) (wordUnitary hρ n)
  have hD := wordTypicalDiagonal_isProjection hρ δ n
  constructor
  · change star (F (wordTypicalDiagonal hρ δ n)) = F (wordTypicalDiagonal hρ δ n)
    rw [← map_star]
    exact congrArg F hD.selfAdjoint.eq
  · change F (wordTypicalDiagonal hρ δ n) * F (wordTypicalDiagonal hρ δ n) =
      F (wordTypicalDiagonal hρ δ n)
    rw [← map_mul, hD.idempotent]

theorem wordTypicalProjector_commutes {ρ : Matrix I I ℂ} (hρ : FlaggedStates.IsDensity ρ)
    (δ : ℝ) (n : ℕ) :
    Commute (wordTypicalProjector hρ δ n) (TensorPinching.tensorPower ρ n) := by
  rw [wordTensorPower_spectral hρ n]
  let F := Unitary.conjStarAlgAut ℝ (Matrix (Word I n) (Word I n) ℂ) (wordUnitary hρ n)
  change F (wordTypicalDiagonal hρ δ n) * F (wordWeightDiagonal hρ n) =
    F (wordWeightDiagonal hρ n) * F (wordTypicalDiagonal hρ δ n)
  rw [← map_mul, ← map_mul]
  congr 1
  change Matrix.diagonal _ * Matrix.diagonal _ = Matrix.diagonal _ * Matrix.diagonal _
  rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext x
  exact mul_comm _ _

theorem wordTypicalProjector_acceptance {ρ : Matrix I I ℂ} (hρ : FlaggedStates.IsDensity ρ)
    (δ : ℝ) (n : ℕ) :
    (TensorPinching.tensorPower ρ n * wordTypicalProjector hρ δ n).trace.re =
      typicalMass hρ δ n := by
  classical
  rw [wordTensorPower_spectral hρ n, wordTypicalProjector, ← map_mul,
    unitary_conjugate_trace, wordWeightDiagonal, wordTypicalDiagonal,
    Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal, Complex.re_sum, typicalMass]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases h : typicalWord hρ δ n x <;> simp [h]

def wordIndex (I : Type*) : (n : ℕ) → Word I n ≃ TensorEntropy.TensorIndex I n
  | 0 => {
      toFun := fun _ => PUnit.unit
      invFun := fun _ => Fin.elim0
      left_inv := fun x => by funext j; exact Fin.elim0 j
      right_inv := fun x => by cases x; rfl }
  | n + 1 => (TensorPinching.rowsSuccEquiv I n).trans
      (Equiv.prodCongr (wordIndex I n) (Equiv.refl I))

theorem wordTensorPower_matrix (ρ : Matrix I I ℂ) (n : ℕ) :
    Matrix.reindex (wordIndex I n) (wordIndex I n) (TensorPinching.tensorPower ρ n) =
      TensorEntropy.tensorPower ρ n := by
  induction n with
  | zero =>
      ext x y
      cases x
      cases y
      simp [wordIndex, TensorPinching.tensorPower, TensorPinching.tensorMatrix,
        TensorEntropy.tensorPower, Matrix.reindex_apply, Matrix.submatrix_apply]
  | succ n ih =>
      ext ⟨xs, i⟩ ⟨ys, j⟩
      have h := congrArg (fun A : Matrix (TensorEntropy.TensorIndex I n)
        (TensorEntropy.TensorIndex I n) ℂ => A xs ys) ih
      change TensorPinching.tensorPower ρ (n + 1)
        ((TensorPinching.rowsSuccEquiv I n).symm ((wordIndex I n).symm xs, i))
        ((TensorPinching.rowsSuccEquiv I n).symm ((wordIndex I n).symm ys, j)) =
          TensorEntropy.tensorPower ρ n xs ys * ρ i j
      have hs := congrArg (fun A : Matrix (Word I n × I) (Word I n × I) ℂ =>
        A ((wordIndex I n).symm xs, i) ((wordIndex I n).symm ys, j))
          (TensorPinching.tensorPower_succ_submatrix ρ n)
      change TensorPinching.tensorPower ρ (n + 1)
        ((TensorPinching.rowsSuccEquiv I n).symm ((wordIndex I n).symm xs, i))
        ((TensorPinching.rowsSuccEquiv I n).symm ((wordIndex I n).symm ys, j)) =
          TensorPinching.tensorPower ρ n ((wordIndex I n).symm xs) ((wordIndex I n).symm ys) * ρ i j at hs
      exact hs.trans (congrArg (fun z : ℂ => z * ρ i j) h)

def typicalProjector {ρ : Matrix I I ℂ} (hρ : FlaggedStates.IsDensity ρ)
    (δ : ℝ) (n : ℕ) : Matrix (TensorEntropy.TensorIndex I n) (TensorEntropy.TensorIndex I n) ℂ :=
  Matrix.reindex (wordIndex I n) (wordIndex I n) (wordTypicalProjector hρ δ n)

theorem typicalProjector_isProjection {ρ : Matrix I I ℂ} (hρ : FlaggedStates.IsDensity ρ)
    (δ : ℝ) (n : ℕ) : PetzSmoothing.IsProjection (typicalProjector hρ δ n) := by
  have h := wordTypicalProjector_isProjection hρ δ n
  let F := Matrix.reindexRingEquiv ℂ (wordIndex I n)
  constructor
  · exact h.selfAdjoint.submatrix (wordIndex I n).symm
  · change F (wordTypicalProjector hρ δ n) * F (wordTypicalProjector hρ δ n) =
      F (wordTypicalProjector hρ δ n)
    rw [← map_mul, h.idempotent]

theorem typicalProjector_isEffect {ρ : Matrix I I ℂ} (hρ : FlaggedStates.IsDensity ρ)
    (δ : ℝ) (n : ℕ) : FlaggedStates.IsEffect (typicalProjector hρ δ n) :=
  (typicalProjector_isProjection hρ δ n).isEffect

theorem typicalProjector_commutes {ρ : Matrix I I ℂ} (hρ : FlaggedStates.IsDensity ρ)
    (δ : ℝ) (n : ℕ) :
    Commute (typicalProjector hρ δ n) (TensorEntropy.tensorPower ρ n) := by
  rw [← wordTensorPower_matrix ρ n]
  exact (wordTypicalProjector_commutes hρ δ n).map (Matrix.reindexRingEquiv ℂ (wordIndex I n))

theorem typicalProjector_acceptance {ρ : Matrix I I ℂ} (hρ : FlaggedStates.IsDensity ρ)
    (δ : ℝ) (n : ℕ) :
    (TensorEntropy.tensorPower ρ n * typicalProjector hρ δ n).trace.re = typicalMass hρ δ n := by
  rw [← wordTensorPower_matrix ρ n]
  let F := Matrix.reindexRingEquiv ℂ (wordIndex I n)
  change (F (TensorPinching.tensorPower ρ n) * F (wordTypicalProjector hρ δ n)).trace.re = _
  rw [← map_mul]
  have htrace (A : Matrix (Word I n) (Word I n) ℂ) : (F A).trace = A.trace :=
    (wordIndex I n).symm.sum_comp (fun x => A x x)
  rw [htrace]
  exact wordTypicalProjector_acceptance hρ δ n

theorem typicalProjector_acceptance_tendsto_one {ρ : Matrix I I ℂ}
    (hρ : FlaggedStates.IsDensity ρ) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun n => (TensorEntropy.tensorPower ρ n * typicalProjector hρ δ n).trace.re)
      atTop (𝓝 1) := by
  simpa only [typicalProjector_acceptance] using typicalMass_tendsto_one hρ hδ

def typicalCount {ρ : Matrix I I ℂ} (hρ : FlaggedStates.IsDensity ρ)
    (δ : ℝ) (n : ℕ) : ℕ := by
  classical
  exact Fintype.card {x : Word I n // typicalWord hρ δ n x}

theorem typicalCount_eq_sum {ρ : Matrix I I ℂ} (hρ : FlaggedStates.IsDensity ρ)
    (δ : ℝ) (n : ℕ) :
    (typicalCount hρ δ n : ℝ) = ∑ x : Word I n, if typicalWord hρ δ n x then 1 else 0 := by
  classical
  rw [typicalCount, Fintype.card_subtype, Finset.sum_boole]

theorem typicalCount_weight_bounds {ρ : Matrix I I ℂ} (hρ : FlaggedStates.IsDensity ρ)
    (δ : ℝ) (n : ℕ) :
    Real.exp (-(n : ℝ) * (QuantumProver.QuantumEntropy.entropyNats ρ + δ)) *
        (typicalCount hρ δ n : ℝ) ≤ typicalMass hρ δ n ∧
      typicalMass hρ δ n ≤
        Real.exp (-(n : ℝ) * (QuantumProver.QuantumEntropy.entropyNats ρ - δ)) *
          (typicalCount hρ δ n : ℝ) := by
  classical
  rw [typicalCount_eq_sum, typicalMass, Finset.mul_sum, Finset.mul_sum]
  constructor <;> apply Finset.sum_le_sum <;> intro x hx
  · by_cases ht : typicalWord hρ δ n x
    · simpa only [ht, ite_true, mul_one] using (typicalWord_eigenvalue_bounds hρ ht).1
    · simp [ht]
  · by_cases ht : typicalWord hρ δ n x
    · simpa only [ht, ite_true, mul_one] using (typicalWord_eigenvalue_bounds hρ ht).2
    · simp [ht]

theorem typicalCount_le_exp {ρ : Matrix I I ℂ} (hρ : FlaggedStates.IsDensity ρ)
    (δ : ℝ) (n : ℕ) :
    (typicalCount hρ δ n : ℝ) ≤ Real.exp ((n : ℝ) * (QuantumProver.QuantumEntropy.entropyNats ρ + δ)) := by
  have h := (typicalCount_weight_bounds hρ δ n).1.trans (typicalMass_le_one hρ δ n)
  have he : Real.exp (-(n : ℝ) * (QuantumProver.QuantumEntropy.entropyNats ρ + δ)) *
      Real.exp ((n : ℝ) * (QuantumProver.QuantumEntropy.entropyNats ρ + δ)) = 1 := by
    rw [← Real.exp_add]
    convert Real.exp_zero using 1 <;> ring
  apply (mul_le_mul_iff_right₀ (Real.exp_pos (-(n : ℝ) *
    (QuantumProver.QuantumEntropy.entropyNats ρ + δ)))).mp
  rw [he]
  exact h

theorem wordTypicalProjector_rank {ρ : Matrix I I ℂ} (hρ : FlaggedStates.IsDensity ρ)
    (δ : ℝ) (n : ℕ) : (wordTypicalProjector hρ δ n).rank = typicalCount hρ δ n := by
  classical
  let U := (wordUnitary hρ n : Matrix (Word I n) (Word I n) ℂ)
  have hU : IsUnit U.det := (Matrix.isUnit_iff_isUnit_det U).mp Unitary.isUnit_coe
  have hUs : IsUnit Uᴴ.det := (Matrix.isUnit_iff_isUnit_det Uᴴ).mp
    (show IsUnit Uᴴ from Unitary.isUnit_coe (U := star (wordUnitary hρ n)))
  change (U * wordTypicalDiagonal hρ δ n * Uᴴ).rank = _
  rw [Matrix.rank_mul_eq_left_of_isUnit_det Uᴴ _ hUs,
    Matrix.rank_mul_eq_right_of_isUnit_det U _ hU, wordTypicalDiagonal, Matrix.rank_diagonal]
  exact Fintype.card_congr (Equiv.subtypeEquivRight (fun x => by
    by_cases ht : typicalWord hρ δ n x <;> simp [ht]))

theorem typicalProjector_rank {ρ : Matrix I I ℂ} (hρ : FlaggedStates.IsDensity ρ)
    (δ : ℝ) (n : ℕ) : (typicalProjector hρ δ n).rank = typicalCount hρ δ n := by
  rw [typicalProjector, Matrix.rank_reindex, wordTypicalProjector_rank]

theorem typicalProjector_trace_eq_rank {ρ : Matrix I I ℂ} (hρ : FlaggedStates.IsDensity ρ)
    (δ : ℝ) (n : ℕ) : (typicalProjector hρ δ n).trace.re =
      ((typicalProjector hρ δ n).rank : ℝ) := by
  classical
  rw [typicalProjector_rank]
  have htrace (A : Matrix (Word I n) (Word I n) ℂ) :
      (Matrix.reindex (wordIndex I n) (wordIndex I n) A).trace = A.trace :=
    (wordIndex I n).symm.sum_comp (fun x => A x x)
  rw [typicalProjector, htrace, wordTypicalProjector, unitary_conjugate_trace,
    wordTypicalDiagonal, Matrix.trace_diagonal, Complex.re_sum, typicalCount_eq_sum]
  apply Finset.sum_congr rfl
  intro x hx
  split_ifs <;> simp

theorem typicalProjector_rank_le_exp {ρ : Matrix I I ℂ} (hρ : FlaggedStates.IsDensity ρ)
    (δ : ℝ) (n : ℕ) :
    ((typicalProjector hρ δ n).rank : ℝ) ≤
      Real.exp ((n : ℝ) * (QuantumProver.QuantumEntropy.entropyNats ρ + δ)) := by
  rw [typicalProjector_rank]
  exact typicalCount_le_exp hρ δ n

theorem typicalProjector_rank_eventually_ge_half_exp {ρ : Matrix I I ℂ}
    (hρ : FlaggedStates.IsDensity ρ) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop,
      (1 / 2 : ℝ) * Real.exp ((n : ℝ) * (QuantumProver.QuantumEntropy.entropyNats ρ - δ)) ≤
        ((typicalProjector hρ δ n).rank : ℝ) := by
  have hm := (typicalMass_tendsto_one hρ hδ).eventually
    (eventually_gt_nhds (by norm_num : (1 / 2 : ℝ) < 1))
  filter_upwards [hm] with n hn
  rw [typicalProjector_rank]
  have hb := (typicalCount_weight_bounds hρ δ n).2
  have he : Real.exp ((n : ℝ) * (QuantumProver.QuantumEntropy.entropyNats ρ - δ)) *
      Real.exp (-(n : ℝ) * (QuantumProver.QuantumEntropy.entropyNats ρ - δ)) = 1 := by
    rw [← Real.exp_add]
    convert Real.exp_zero using 1 <;> ring
  have h := mul_le_mul_of_nonneg_left ((le_of_lt hn).trans hb)
    (Real.exp_nonneg ((n : ℝ) * (QuantumProver.QuantumEntropy.entropyNats ρ - δ)))
  simpa only [← mul_assoc, he, one_mul, mul_comm (Real.exp _) (1 / 2 : ℝ)] using h

theorem wordConjugate_posSemidef {ρ : Matrix I I ℂ} (hρ : FlaggedStates.IsDensity ρ)
    (n : ℕ) {D : Matrix (Word I n) (Word I n) ℂ} (hD : D.PosSemidef) :
    (Unitary.conjStarAlgAut ℝ _ (wordUnitary hρ n) D).PosSemidef :=
  hD.mul_mul_conjTranspose_same (wordUnitary hρ n : Matrix (Word I n) (Word I n) ℂ)

def wordCropDiagonal {ρ : Matrix I I ℂ} (hρ : FlaggedStates.IsDensity ρ)
    (δ : ℝ) (n : ℕ) : Matrix (Word I n) (Word I n) ℂ := by
  classical
  exact Matrix.diagonal (fun x => if typicalWord hρ δ n x then
    (iidWeight (eigenWeight hρ) n x : ℂ) else 0)

theorem wordTypicalProjector_crop {ρ : Matrix I I ℂ} (hρ : FlaggedStates.IsDensity ρ)
    (δ : ℝ) (n : ℕ) :
    wordTypicalProjector hρ δ n * TensorPinching.tensorPower ρ n * wordTypicalProjector hρ δ n =
      Unitary.conjStarAlgAut ℝ _ (wordUnitary hρ n) (wordCropDiagonal hρ δ n) := by
  classical
  rw [wordTensorPower_spectral]
  let F := Unitary.conjStarAlgAut ℝ (Matrix (Word I n) (Word I n) ℂ) (wordUnitary hρ n)
  change F (wordTypicalDiagonal hρ δ n) * F (wordWeightDiagonal hρ n) *
    F (wordTypicalDiagonal hρ δ n) = F (wordCropDiagonal hρ δ n)
  rw [← map_mul, ← map_mul]
  congr 1
  rw [wordTypicalDiagonal, wordWeightDiagonal, wordCropDiagonal,
    Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext x
  split_ifs <;> simp

theorem wordTypicalProjector_sandwich {ρ : Matrix I I ℂ} (hρ : FlaggedStates.IsDensity ρ)
    (δ : ℝ) (n : ℕ) :
    (wordTypicalProjector hρ δ n * TensorPinching.tensorPower ρ n * wordTypicalProjector hρ δ n -
      Real.exp (-(n : ℝ) * (QuantumProver.QuantumEntropy.entropyNats ρ + δ)) •
        wordTypicalProjector hρ δ n).PosSemidef ∧
    (Real.exp (-(n : ℝ) * (QuantumProver.QuantumEntropy.entropyNats ρ - δ)) •
      wordTypicalProjector hρ δ n -
        wordTypicalProjector hρ δ n * TensorPinching.tensorPower ρ n * wordTypicalProjector hρ δ n).PosSemidef := by
  classical
  rw [wordTypicalProjector_crop, wordTypicalProjector]
  constructor
  · rw [← map_smul, ← map_sub]
    apply wordConjugate_posSemidef hρ n
    rw [wordCropDiagonal, wordTypicalDiagonal, ← Matrix.diagonal_smul,
      Matrix.diagonal_sub, Matrix.posSemidef_diagonal_iff]
    intro x
    by_cases ht : typicalWord hρ δ n x
    · simp only [ht, ite_true, Pi.smul_apply, Algebra.smul_def, mul_one]
      change (0 : ℂ) ≤ (iidWeight (eigenWeight hρ) n x : ℂ) -
        (Real.exp (-(n : ℝ) * (QuantumProver.QuantumEntropy.entropyNats ρ + δ)) : ℂ)
      rw [← Complex.ofReal_sub]
      exact Complex.zero_le_real.mpr (sub_nonneg.mpr (typicalWord_eigenvalue_bounds hρ ht).1)
    · simp [ht]
  · rw [← map_smul, ← map_sub]
    apply wordConjugate_posSemidef hρ n
    rw [wordCropDiagonal, wordTypicalDiagonal, ← Matrix.diagonal_smul,
      Matrix.diagonal_sub, Matrix.posSemidef_diagonal_iff]
    intro x
    by_cases ht : typicalWord hρ δ n x
    · simp only [ht, ite_true, Pi.smul_apply, Algebra.smul_def, mul_one]
      change (0 : ℂ) ≤ (Real.exp (-(n : ℝ) * (QuantumProver.QuantumEntropy.entropyNats ρ - δ)) : ℂ) -
        (iidWeight (eigenWeight hρ) n x : ℂ)
      rw [← Complex.ofReal_sub]
      exact Complex.zero_le_real.mpr (sub_nonneg.mpr (typicalWord_eigenvalue_bounds hρ ht).2)
    · simp [ht]

theorem wordTypicalProjector_global_lower {ρ : Matrix I I ℂ} (hρ : FlaggedStates.IsDensity ρ)
    (δ : ℝ) (n : ℕ) :
    (TensorPinching.tensorPower ρ n -
      Real.exp (-(n : ℝ) * (QuantumProver.QuantumEntropy.entropyNats ρ + δ)) •
        wordTypicalProjector hρ δ n).PosSemidef := by
  classical
  rw [wordTensorPower_spectral, wordTypicalProjector, ← map_smul, ← map_sub]
  apply wordConjugate_posSemidef hρ n
  rw [wordWeightDiagonal, wordTypicalDiagonal, ← Matrix.diagonal_smul,
    Matrix.diagonal_sub, Matrix.posSemidef_diagonal_iff]
  intro x
  by_cases ht : typicalWord hρ δ n x
  · simp only [ht, ite_true, Pi.smul_apply, Algebra.smul_def, mul_one]
    change (0 : ℂ) ≤ (iidWeight (eigenWeight hρ) n x : ℂ) -
      (Real.exp (-(n : ℝ) * (QuantumProver.QuantumEntropy.entropyNats ρ + δ)) : ℂ)
    rw [← Complex.ofReal_sub]
    exact Complex.zero_le_real.mpr (sub_nonneg.mpr (typicalWord_eigenvalue_bounds hρ ht).1)
  · simp only [ht, ite_false, Pi.smul_apply, smul_zero, sub_zero]
    exact Complex.zero_le_real.mpr (iidWeight_nonneg _ (eigenWeight_nonneg hρ) n x)

theorem wordTypicalProjector_crop_upper_identity {ρ : Matrix I I ℂ}
    (hρ : FlaggedStates.IsDensity ρ) (δ : ℝ) (n : ℕ) :
    (Real.exp (-(n : ℝ) * (QuantumProver.QuantumEntropy.entropyNats ρ - δ)) • (1 : Matrix (Word I n) (Word I n) ℂ) -
      wordTypicalProjector hρ δ n * TensorPinching.tensorPower ρ n * wordTypicalProjector hρ δ n).PosSemidef := by
  classical
  rw [wordTypicalProjector_crop]
  let F := Unitary.conjStarAlgAut ℝ (Matrix (Word I n) (Word I n) ℂ) (wordUnitary hρ n)
  change (Real.exp (-(n : ℝ) * (QuantumProver.QuantumEntropy.entropyNats ρ - δ)) • 1 -
    F (wordCropDiagonal hρ δ n)).PosSemidef
  rw [← map_one F, ← map_smul, ← map_sub]
  apply wordConjugate_posSemidef hρ n
  rw [← Matrix.diagonal_one, wordCropDiagonal, ← Matrix.diagonal_smul,
    Matrix.diagonal_sub, Matrix.posSemidef_diagonal_iff]
  intro x
  by_cases ht : typicalWord hρ δ n x
  · simp only [ht, ite_true, Pi.smul_apply, Pi.one_apply, Algebra.smul_def, mul_one]
    change (0 : ℂ) ≤ (Real.exp (-(n : ℝ) * (QuantumProver.QuantumEntropy.entropyNats ρ - δ)) : ℂ) -
      (iidWeight (eigenWeight hρ) n x : ℂ)
    rw [← Complex.ofReal_sub]
    exact Complex.zero_le_real.mpr (sub_nonneg.mpr (typicalWord_eigenvalue_bounds hρ ht).2)
  · simp only [ht, ite_false, Pi.smul_apply, Pi.one_apply, Algebra.smul_def, mul_one, sub_zero]
    exact Complex.zero_le_real.mpr (Real.exp_nonneg (-(n : ℝ) * (QuantumProver.QuantumEntropy.entropyNats ρ - δ)))

theorem typicalProjector_sandwich {ρ : Matrix I I ℂ} (hρ : FlaggedStates.IsDensity ρ)
    (δ : ℝ) (n : ℕ) :
    (typicalProjector hρ δ n * TensorEntropy.tensorPower ρ n * typicalProjector hρ δ n -
      Real.exp (-(n : ℝ) * (QuantumProver.QuantumEntropy.entropyNats ρ + δ)) • typicalProjector hρ δ n).PosSemidef ∧
    (Real.exp (-(n : ℝ) * (QuantumProver.QuantumEntropy.entropyNats ρ - δ)) • typicalProjector hρ δ n -
      typicalProjector hρ δ n * TensorEntropy.tensorPower ρ n * typicalProjector hρ δ n).PosSemidef := by
  rw [← wordTensorPower_matrix ρ n]
  let F := Matrix.reindexRingEquiv ℂ (wordIndex I n)
  have h := wordTypicalProjector_sandwich hρ δ n
  constructor
  · change (F (wordTypicalProjector hρ δ n) * F (TensorPinching.tensorPower ρ n) *
      F (wordTypicalProjector hρ δ n) -
      Real.exp (-(n : ℝ) * (QuantumProver.QuantumEntropy.entropyNats ρ + δ)) • F (wordTypicalProjector hρ δ n)).PosSemidef
    rw [← map_mul, ← map_mul]
    have hs : Real.exp (-(n : ℝ) * (QuantumProver.QuantumEntropy.entropyNats ρ + δ)) •
        F (wordTypicalProjector hρ δ n) =
      F (Real.exp (-(n : ℝ) * (QuantumProver.QuantumEntropy.entropyNats ρ + δ)) • wordTypicalProjector hρ δ n) := rfl
    rw [hs, ← map_sub]
    exact h.1.submatrix (wordIndex I n).symm
  · change (Real.exp (-(n : ℝ) * (QuantumProver.QuantumEntropy.entropyNats ρ - δ)) •
      F (wordTypicalProjector hρ δ n) -
      F (wordTypicalProjector hρ δ n) * F (TensorPinching.tensorPower ρ n) * F (wordTypicalProjector hρ δ n)).PosSemidef
    rw [← map_mul, ← map_mul]
    have hs : Real.exp (-(n : ℝ) * (QuantumProver.QuantumEntropy.entropyNats ρ - δ)) •
        F (wordTypicalProjector hρ δ n) =
      F (Real.exp (-(n : ℝ) * (QuantumProver.QuantumEntropy.entropyNats ρ - δ)) • wordTypicalProjector hρ δ n) := rfl
    rw [hs, ← map_sub]
    exact h.2.submatrix (wordIndex I n).symm

theorem typicalProjector_global_lower {ρ : Matrix I I ℂ} (hρ : FlaggedStates.IsDensity ρ)
    (δ : ℝ) (n : ℕ) :
    (TensorEntropy.tensorPower ρ n -
      Real.exp (-(n : ℝ) * (QuantumProver.QuantumEntropy.entropyNats ρ + δ)) • typicalProjector hρ δ n).PosSemidef := by
  rw [← wordTensorPower_matrix ρ n]
  let F := Matrix.reindexRingEquiv ℂ (wordIndex I n)
  change (F (TensorPinching.tensorPower ρ n) -
    Real.exp (-(n : ℝ) * (QuantumProver.QuantumEntropy.entropyNats ρ + δ)) • F (wordTypicalProjector hρ δ n)).PosSemidef
  have hs : Real.exp (-(n : ℝ) * (QuantumProver.QuantumEntropy.entropyNats ρ + δ)) •
      F (wordTypicalProjector hρ δ n) =
    F (Real.exp (-(n : ℝ) * (QuantumProver.QuantumEntropy.entropyNats ρ + δ)) • wordTypicalProjector hρ δ n) := rfl
  rw [hs, ← map_sub]
  exact (wordTypicalProjector_global_lower hρ δ n).submatrix (wordIndex I n).symm

theorem typicalProjector_crop_upper_identity {ρ : Matrix I I ℂ}
    (hρ : FlaggedStates.IsDensity ρ) (δ : ℝ) (n : ℕ) :
    (Real.exp (-(n : ℝ) * (QuantumProver.QuantumEntropy.entropyNats ρ - δ)) •
      (1 : Matrix (TensorEntropy.TensorIndex I n) (TensorEntropy.TensorIndex I n) ℂ) -
      typicalProjector hρ δ n * TensorEntropy.tensorPower ρ n * typicalProjector hρ δ n).PosSemidef := by
  rw [← wordTensorPower_matrix ρ n]
  let F := Matrix.reindexRingEquiv ℂ (wordIndex I n)
  change (Real.exp (-(n : ℝ) * (QuantumProver.QuantumEntropy.entropyNats ρ - δ)) • 1 -
    F (wordTypicalProjector hρ δ n) * F (TensorPinching.tensorPower ρ n) * F (wordTypicalProjector hρ δ n)).PosSemidef
  rw [← map_mul, ← map_mul, ← map_one F]
  have hs : Real.exp (-(n : ℝ) * (QuantumProver.QuantumEntropy.entropyNats ρ - δ)) • F 1 =
    F (Real.exp (-(n : ℝ) * (QuantumProver.QuantumEntropy.entropyNats ρ - δ)) • 1) := rfl
  rw [hs, ← map_sub]
  exact (wordTypicalProjector_crop_upper_identity hρ δ n).submatrix (wordIndex I n).symm

theorem typicalWord_zero_weight_excluded {ρ : Matrix I I ℂ} (hρ : FlaggedStates.IsDensity ρ)
    (δ : ℝ) (n : ℕ) (x : Word I n) (hx : iidWeight (eigenWeight hρ) n x = 0) :
    ¬ typicalWord hρ δ n x := by
  intro ht
  exact (ne_of_gt ht.1) hx

theorem typicalWord_zero_copy {ρ : Matrix I I ℂ} (hρ : FlaggedStates.IsDensity ρ)
    (δ : ℝ) (x : Word I 0) : typicalWord hρ δ 0 x := by
  simp [typicalWord, iidWeight]

theorem typicalProjector_zero_copy {ρ : Matrix I I ℂ} (hρ : FlaggedStates.IsDensity ρ)
    (δ : ℝ) : typicalProjector hρ δ 0 = 1 := by
  classical
  have hD : wordTypicalDiagonal hρ δ 0 = 1 := by
    simp only [wordTypicalDiagonal, typicalWord_zero_copy, ite_true, Matrix.diagonal_one]
  rw [typicalProjector, wordTypicalProjector, hD, map_one]
  exact (Matrix.reindexRingEquiv ℂ (wordIndex I 0)).map_one

end QuantumProver.QuantumTypicalProjectors

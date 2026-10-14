import QuantumProver.InformationTheory.ConditionalEntropy.ConditionalRange

noncomputable section

open scoped BigOperators ComplexOrder MatrixOrder Matrix Matrix.Norms.L2Operator

namespace QuantumProver.MatrixAnalysis.TwoColumnEntropy

open QuantumProver.SuperchannelDiscrimination.FlaggedStates
open QuantumProver.IsotropicFormation

variable {I : Type*} [Fintype I] [DecidableEq I]

def a (G : Matrix (Fin 2) (Fin 2) ℂ) : ℝ := (G 0 0).re
def b (G : Matrix (Fin 2) (Fin 2) ℂ) : ℝ := (G 1 1).re
def z (G : Matrix (Fin 2) (Fin 2) ℂ) : ℂ := G 0 1
def tau (G : Matrix (Fin 2) (Fin 2) ℂ) : ℝ := a G + b G
def delta (G : Matrix (Fin 2) (Fin 2) ℂ) : ℝ := a G * b G - Complex.normSq (z G)
def discriminant (G : Matrix (Fin 2) (Fin 2) ℂ) : ℝ :=
  (a G - b G)^2 + 4 * Complex.normSq (z G)
def lambdaPlus (G : Matrix (Fin 2) (Fin 2) ℂ) : ℝ :=
  (tau G + Real.sqrt (discriminant G)) / 2
def lambdaMinus (G : Matrix (Fin 2) (Fin 2) ℂ) : ℝ :=
  (tau G - Real.sqrt (discriminant G)) / 2

def phi (v : ℝ) : ℝ := flagEntropyBits ((1 + Real.sqrt (1-v)) / 2)

theorem diag_eq_ofReal {G : Matrix (Fin 2) (Fin 2) ℂ} (hG : G.PosSemidef)
    (i : Fin 2) : G i i = ((G i i).re : ℂ) := by
  apply Complex.ext
  · rfl
  · simpa only [Complex.ofReal_im] using
      (Complex.nonneg_iff.mp (hG.diag_nonneg (i := i))).2.symm

theorem tau_nonneg {G : Matrix (Fin 2) (Fin 2) ℂ} (hG : G.PosSemidef) : 0 ≤ tau G :=
  add_nonneg (Complex.nonneg_iff.mp (hG.diag_nonneg (i := 0))).1
    (Complex.nonneg_iff.mp (hG.diag_nonneg (i := 1))).1

theorem trace_eq_tau {G : Matrix (Fin 2) (Fin 2) ℂ} (hG : G.PosSemidef) :
    G.trace = (tau G : ℂ) := by
  simp only [Matrix.trace, Matrix.diag, Fin.sum_univ_two]
  rw [diag_eq_ofReal hG 0, diag_eq_ofReal hG 1]
  simp [tau, a, b]

theorem det_eq_delta {G : Matrix (Fin 2) (Fin 2) ℂ} (hG : G.PosSemidef) :
    G.det = (delta G : ℂ) := by
  rw [Matrix.det_fin_two, diag_eq_ofReal hG 0, diag_eq_ofReal hG 1]
  have h10 : G 1 0 = star (z G) := (hG.isHermitian.apply 1 0).symm
  rw [h10]
  simp [delta, a, b, z, Complex.star_def, Complex.mul_conj]

theorem delta_nonneg {G : Matrix (Fin 2) (Fin 2) ℂ} (hG : G.PosSemidef) : 0 ≤ delta G := by
  have h := (Complex.nonneg_iff.mp hG.det_nonneg).1
  rw [det_eq_delta hG] at h
  simpa using h

theorem discriminant_nonneg (G : Matrix (Fin 2) (Fin 2) ℂ) : 0 ≤ discriminant G := by
  have hz := Complex.normSq_nonneg (z G)
  unfold discriminant
  nlinarith [sq_nonneg (a G-b G)]

theorem discriminant_eq (G : Matrix (Fin 2) (Fin 2) ℂ) :
    discriminant G = (tau G)^2 - 4 * delta G := by
  unfold discriminant tau delta
  ring

theorem sqrt_discriminant_le_tau {G : Matrix (Fin 2) (Fin 2) ℂ} (hG : G.PosSemidef) :
    Real.sqrt (discriminant G) ≤ tau G := by
  have hle : discriminant G ≤ (tau G)^2 := by
    rw [discriminant_eq]
    linarith [delta_nonneg hG]
  exact (Real.sqrt_le_sqrt hle).trans_eq (Real.sqrt_sq (tau_nonneg hG))

theorem lambda_nonneg {G : Matrix (Fin 2) (Fin 2) ℂ} (hG : G.PosSemidef) :
    0 ≤ lambdaPlus G ∧ 0 ≤ lambdaMinus G := by
  have ht := tau_nonneg hG
  have hr := Real.sqrt_nonneg (discriminant G)
  have hb := sqrt_discriminant_le_tau hG
  unfold lambdaPlus lambdaMinus
  constructor <;> linarith

theorem lambda_sum (G : Matrix (Fin 2) (Fin 2) ℂ) :
    lambdaPlus G + lambdaMinus G = tau G := by
  unfold lambdaPlus lambdaMinus
  ring

theorem lambda_product (G : Matrix (Fin 2) (Fin 2) ℂ) :
    lambdaPlus G * lambdaMinus G = delta G := by
  have hr := Real.sq_sqrt (discriminant_nonneg G)
  have hd := discriminant_eq G
  unfold lambdaPlus lambdaMinus
  nlinarith

theorem gram_charpoly {G : Matrix (Fin 2) (Fin 2) ℂ} (hG : G.PosSemidef) :
    G.charpoly = (realDiagonal ![lambdaPlus G, lambdaMinus G]).charpoly := by
  have ht : (realDiagonal ![lambdaPlus G, lambdaMinus G]).trace =
      ((lambdaPlus G + lambdaMinus G : ℝ) : ℂ) := by
    simp [realDiagonal, Matrix.trace, Fin.sum_univ_two]
  have hd : (realDiagonal ![lambdaPlus G, lambdaMinus G]).det =
      ((lambdaPlus G * lambdaMinus G : ℝ) : ℂ) := by
    simp [realDiagonal, Matrix.det_fin_two]
  rw [Matrix.charpoly_fin_two, Matrix.charpoly_fin_two, trace_eq_tau hG,
    det_eq_delta hG, ht, hd, lambda_sum, lambda_product]

theorem entropyBits_realDiagonal_two (x y : ℝ) :
    entropyBits (realDiagonal ![x,y]) = -(x * Real.log x + y * Real.log y) / Real.log 2 := by
  rw [QuantumProver.ConditionalEntropy.ConditionalRange.entropyBits_eq_isotropicEntropy_div_log_two,
    vonNeumannEntropyNat_realDiagonal]
  simp [classicalEntropy, Fin.sum_univ_two, Real.negMulLog_eq_neg] <;> ring

theorem entropyBits_psd_two {G : Matrix (Fin 2) (Fin 2) ℂ} (hG : G.PosSemidef) :
    entropyBits G = -(lambdaPlus G * Real.log (lambdaPlus G) +
      lambdaMinus G * Real.log (lambdaMinus G)) / Real.log 2 := by
  have h := vonNeumannEntropyNat_eq_of_charpoly_eq G
    (realDiagonal ![lambdaPlus G,lambdaMinus G]) hG.isHermitian
    (realDiagonal_isHermitian _) (gram_charpoly hG)
  have hb : entropyBits G = entropyBits (realDiagonal ![lambdaPlus G,lambdaMinus G]) := by
    rw [QuantumProver.ConditionalEntropy.ConditionalRange.entropyBits_eq_isotropicEntropy_div_log_two,
      QuantumProver.ConditionalEntropy.ConditionalRange.entropyBits_eq_isotropicEntropy_div_log_two, h]
  rw [hb, entropyBits_realDiagonal_two]

theorem entropyBits_psd_two_phi {G : Matrix (Fin 2) (Fin 2) ℂ} (hG : G.PosSemidef) :
    entropyBits G = -(tau G * Real.log (tau G)) / Real.log 2 +
      tau G * phi (4 * delta G / (tau G)^2) := by
  rw [entropyBits_psd_two hG]
  by_cases ht : tau G = 0
  · have hs := lambda_sum G
    have hn := lambda_nonneg hG
    have hp : lambdaPlus G = 0 := by rw [ht] at hs; linarith
    have hm : lambdaMinus G = 0 := by rw [ht] at hs; linarith
    simp [hp,hm,ht]
  have htpos : 0 < tau G := lt_of_le_of_ne (tau_nonneg hG) (Ne.symm ht)
  have hq : 1 - 4 * delta G / (tau G)^2 = discriminant G / (tau G)^2 := by
    rw [discriminant_eq]
    field_simp [ht]
    <;> ring
  have hroot : Real.sqrt (1 - 4 * delta G / (tau G)^2) =
      Real.sqrt (discriminant G) / tau G := by
    rw [hq, Real.sqrt_div (discriminant_nonneg G), Real.sqrt_sq htpos.le]
  let q := (1 + Real.sqrt (1 - 4 * delta G / (tau G)^2)) / 2
  have hp : lambdaPlus G = tau G * q := by
    dsimp [lambdaPlus,q]
    rw [hroot]
    field_simp [ht]
    <;> ring
  have hm : lambdaMinus G = tau G * (1-q) := by
    dsimp [lambdaMinus,q]
    rw [hroot]
    field_simp [ht]
    <;> ring
  rw [hp,hm,weighted_mul_log,weighted_mul_log]
  change _ = -(tau G * Real.log (tau G)) / Real.log 2 + tau G * flagEntropyBits q
  unfold flagEntropyBits
  ring

def gram (M : Matrix I (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ := Mᴴ * M

theorem twoColumn_lambda_nonneg (M : Matrix I (Fin 2) ℂ) :
    0 ≤ lambdaPlus (gram M) ∧ 0 ≤ lambdaMinus (gram M) :=
  lambda_nonneg (Matrix.posSemidef_conjTranspose_mul_self M)

theorem entropyBits_twoColumn (M : Matrix I (Fin 2) ℂ) :
    entropyBits (M * Mᴴ) =
      -(lambdaPlus (gram M) * Real.log (lambdaPlus (gram M)) +
        lambdaMinus (gram M) * Real.log (lambdaMinus (gram M))) / Real.log 2 := by
  rw [← QuantumProver.ConditionalEntropy.ConditionalRange.entropyBits_rectangularGram M]
  exact entropyBits_psd_two (Matrix.posSemidef_conjTranspose_mul_self M)

theorem entropyBits_twoColumn_phi (M : Matrix I (Fin 2) ℂ) :
    entropyBits (M * Mᴴ) = -(tau (gram M) * Real.log (tau (gram M))) / Real.log 2 +
      tau (gram M) * phi (4 * delta (gram M) / (tau (gram M))^2) := by
  rw [← QuantumProver.ConditionalEntropy.ConditionalRange.entropyBits_rectangularGram M]
  exact entropyBits_psd_two_phi (Matrix.posSemidef_conjTranspose_mul_self M)

def innerSum (v w : I → ℂ) : ℂ := ∑ i, star (v i) * w i

def outer (v : I → ℂ) : Matrix I I ℂ := Matrix.vecMulVec v (star v)
def weightedOuter (p : ℝ) (v w : I → ℂ) : Matrix I I ℂ :=
  p • outer v + (1-p) • outer w
def weightedColumns (p : ℝ) (v w : I → ℂ) : Matrix I (Fin 2) ℂ :=
  fun i j => ![(Real.sqrt p : ℂ) * v i, (Real.sqrt (1-p) : ℂ) * w i] j

theorem sqrt_ofReal_square (r : ℝ) (hr : 0 ≤ r) :
    (Real.sqrt r : ℂ) * (Real.sqrt r : ℂ) = (r : ℂ) := by
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt hr]

theorem weightedColumns_rightGram (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (v w : I → ℂ) :
    weightedColumns p v w * (weightedColumns p v w)ᴴ = weightedOuter p v w := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, weightedColumns,
    Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    weightedOuter, Matrix.add_apply, Matrix.smul_apply, outer, Matrix.vecMulVec_apply,
    Pi.star_apply, star_mul, Complex.star_def, Complex.conj_ofReal, Complex.real_smul]
  have hpS := sqrt_ofReal_square p hp
  have hqS := sqrt_ofReal_square (1-p) (sub_nonneg.mpr hp1)
  calc
    _ = ((Real.sqrt p : ℂ) * (Real.sqrt p : ℂ)) * (v i * star (v j)) +
        ((Real.sqrt (1-p) : ℂ) * (Real.sqrt (1-p) : ℂ)) * (w i * star (w j)) := by
          simp only [Complex.star_def, map_mul, Complex.conj_ofReal]
          ring
    _ = _ := by rw [hpS,hqS]; rfl

theorem sum_star_mul_self_of_unit (v : I → ℂ) (hv : ∑ i, ‖v i‖^2 = 1) :
    ∑ i, star (v i) * v i = (1 : ℂ) := by
  calc
    _ = ((∑ i, ‖v i‖^2 : ℝ) : ℂ) := by
      simp only [Complex.star_def, Complex.conj_mul', Complex.ofReal_sum, Complex.ofReal_pow]
    _ = 1 := by rw [hv]; rfl

theorem weightedColumns_gram_zero (p : ℝ) (hp : 0 ≤ p) (v w : I → ℂ)
    (hv : ∑ i, ‖v i‖^2 = 1) :
    gram (weightedColumns p v w) 0 0 = (p : ℂ) := by
  change (∑ i, star ((Real.sqrt p : ℂ) * v i) * ((Real.sqrt p : ℂ) * v i)) = _
  calc
    _ = ((Real.sqrt p : ℂ) * (Real.sqrt p : ℂ)) * (∑ i, star (v i) * v i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      simp only [star_mul, Complex.star_def, Complex.conj_ofReal]
      ring
    _ = _ := by rw [sqrt_ofReal_square p hp, sum_star_mul_self_of_unit v hv, mul_one]

theorem weightedColumns_gram_one (p : ℝ) (hp1 : p ≤ 1) (v w : I → ℂ)
    (hw : ∑ i, ‖w i‖^2 = 1) :
    gram (weightedColumns p v w) 1 1 = ((1-p : ℝ) : ℂ) := by
  change (∑ i, star ((Real.sqrt (1-p) : ℂ) * w i) * ((Real.sqrt (1-p) : ℂ) * w i)) = _
  calc
    _ = ((Real.sqrt (1-p) : ℂ) * (Real.sqrt (1-p) : ℂ)) * (∑ i, star (w i) * w i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      simp only [star_mul, Complex.star_def, Complex.conj_ofReal]
      ring
    _ = _ := by rw [sqrt_ofReal_square (1-p) (sub_nonneg.mpr hp1),
        sum_star_mul_self_of_unit w hw, mul_one]

theorem weightedColumns_gram_offdiag (p : ℝ) (v w : I → ℂ) :
    z (gram (weightedColumns p v w)) =
      ((Real.sqrt p : ℂ) * (Real.sqrt (1-p) : ℂ)) * innerSum v w := by
  change (∑ i, star ((Real.sqrt p : ℂ) * v i) * ((Real.sqrt (1-p) : ℂ) * w i)) = _
  unfold innerSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [star_mul, Complex.star_def, Complex.conj_ofReal]
  ring

theorem weightedColumns_tau_delta (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (v w : I → ℂ)
    (hv : ∑ i, ‖v i‖^2 = 1) (hw : ∑ i, ‖w i‖^2 = 1) :
    tau (gram (weightedColumns p v w)) = 1 ∧
    delta (gram (weightedColumns p v w)) = p * (1-p) * (1-Complex.normSq (innerSum v w)) := by
  have h0 := weightedColumns_gram_zero p hp v w hv
  have h1 := weightedColumns_gram_one p hp1 v w hw
  have ha : a (gram (weightedColumns p v w)) = p := by simp [a,h0]
  have hb : b (gram (weightedColumns p v w)) = 1-p := by simp [b,h1]
  have hz := weightedColumns_gram_offdiag p v w
  constructor
  · simp [tau,ha,hb]
  · unfold delta
    rw [ha,hb,hz]
    simp only [Complex.normSq_mul, Complex.normSq_ofReal,
      Real.mul_self_sqrt hp, Real.mul_self_sqrt (sub_nonneg.mpr hp1)]
    ring

theorem entropyBits_weighted_unit_outer (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (v w : I → ℂ)
    (hv : ∑ i, ‖v i‖^2 = 1) (hw : ∑ i, ‖w i‖^2 = 1) :
    entropyBits (weightedOuter p v w) =
      phi (4 * p * (1-p) * (1-Complex.normSq (innerSum v w))) := by
  rw [← weightedColumns_rightGram p hp hp1 v w, entropyBits_twoColumn_phi]
  obtain ⟨ht,hd⟩ := weightedColumns_tau_delta p hp hp1 v w hv hw
  rw [ht,hd]
  simp only [Real.log_one, mul_zero, neg_zero, zero_div, one_pow, div_one, one_mul,
    zero_add]
  congr 1
  ring

end QuantumProver.MatrixAnalysis.TwoColumnEntropy

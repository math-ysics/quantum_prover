import QuantumProver.InformationTheory.WernerEndpoint.AntisymmetricEntropyCost
import QuantumProver.InformationTheory.WernerEndpoint.SchattenSupport

noncomputable section
namespace QuantumProver.WernerEndpoint.AntisymmetricEnsembleCost

open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator
open Matrix AntisymmetricEntropyCost

variable {X : Type*} [Fintype X] [DecidableEq X]

structure FinitePureEnsemble (ρ : Matrix X X ℂ) where
  count : ℕ
  weight : Fin count → ℝ
  weight_nonneg : ∀ j, 0 ≤ weight j
  weight_sum : ∑ j, weight j = 1
  vector : Fin count → X → ℂ
  normalized : ∀ j, vectorNormSq (vector j) = 1
  barycenter : ρ = ∑ j, (weight j : ℂ) • pureDensity (vector j)

theorem vectorNormSq_nonneg (v : X → ℂ) : 0 ≤ vectorNormSq v :=
  Finset.sum_nonneg (fun i _ => Complex.normSq_nonneg _)

theorem vectorNormSq_eq_zero (v : X → ℂ) (h : vectorNormSq v = 0) : v = 0 := by
  funext i
  have hi := Finset.single_le_sum (fun j _ => Complex.normSq_nonneg (v j)) (Finset.mem_univ i)
  change Complex.normSq (v i) ≤ vectorNormSq v at hi
  rw [h] at hi
  exact Complex.normSq_eq_zero.mp (le_antisymm hi (Complex.normSq_nonneg _))

theorem FinitePureEnsemble.residual_trace {ρ : Matrix X X ℂ} (E : FinitePureEnsemble ρ)
    (V : Matrix X X ℂ) :
    (Matrix.trace (V * ρ * Vᴴ)).re =
      ∑ j, E.weight j * vectorNormSq (V.mulVec (E.vector j)) := by
  calc
    (Matrix.trace (V * ρ * Vᴴ)).re =
      (Matrix.trace (V * (∑ j, (E.weight j : ℂ) • pureDensity (E.vector j)) * Vᴴ)).re :=
        congrArg (fun Q => (Matrix.trace (V * Q * Vᴴ)).re) E.barycenter
    _ = _ := by
      simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul,
        Matrix.trace_sum, Matrix.trace_smul, Complex.re_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [show V * pureDensity (E.vector j) * Vᴴ = pureDensity (V.mulVec (E.vector j)) from
        sandwich_crossDensity V (E.vector j) (E.vector j), pureDensity_trace]
      simp [rclike_complex_cast]

theorem FinitePureEnsemble.support_inheritance {ρ : Matrix X X ℂ}
    (E : FinitePureEnsemble ρ) (P : Matrix X X ℂ) (hP : P * P = P)
    (hsupp : ρ = P * ρ * P) (j : Fin E.count) (hwj : 0 < E.weight j) :
    P.mulVec (E.vector j) = E.vector j := by
  let R : Matrix X X ℂ := 1 - P
  have hRP : R * P = 0 := by simp [R, Matrix.sub_mul, hP]
  have hz : R * ρ * Rᴴ = 0 := by
    rw [hsupp]
    simp only [← Matrix.mul_assoc, hRP, Matrix.zero_mul]
  have ht := E.residual_trace R
  rw [hz, Matrix.trace_zero, Complex.zero_re] at ht
  have hle := Finset.single_le_sum (fun k _ => mul_nonneg (E.weight_nonneg k)
    (vectorNormSq_nonneg (R.mulVec (E.vector k)))) (Finset.mem_univ j)
  rw [← ht] at hle
  have hn := vectorNormSq_nonneg (R.mulVec (E.vector j))
  have hnorm : vectorNormSq (R.mulVec (E.vector j)) = 0 := by nlinarith
  have hv := vectorNormSq_eq_zero _ hnorm
  funext i
  have hi := congrFun hv i
  simp only [R, Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply, Pi.zero_apply] at hi
  exact (sub_eq_zero.mp hi).symm

theorem neg_log_half_pow (n : ℕ) :
    -Real.log ((1 / 2 : ℝ) ^ n) / Real.log 2 = (n : ℝ) := by
  rw [Real.log_pow]
  have hh : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
    rw [Real.log_div (by norm_num) (by norm_num), Real.log_one, zero_sub]
  rw [hh]
  field_simp [ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 2))] <;> ring

theorem density_entropy_ge_nat_of_purity (ρ : Matrix X X ℂ) (hρ : ρ.PosSemidef)
    (htrace : Matrix.trace ρ = 1) (n : ℕ) (hcap : purity ρ ≤ (1 / 2 : ℝ) ^ n) :
    (n : ℝ) ≤ vonNeumannEntropyBits ρ := by
  have hp := density_purity_pos ρ hρ htrace
  have hl := Real.log_le_log hp hcap
  have hd : -Real.log ((1 / 2 : ℝ) ^ n) / Real.log 2 ≤
      -Real.log (purity ρ) / Real.log 2 :=
    (div_le_div_iff_of_pos_right (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mpr (neg_le_neg hl)
  rw [neg_log_half_pow] at hd
  exact hd.trans (density_entropy_ge_renyi_two ρ hρ htrace)

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

def aliceDensity (ψ : A × B → ℂ) : Matrix A A ℂ := partialTraceLeft (pureDensity ψ)

def aliceEntropy (ψ : A × B → ℂ) : ℝ := vonNeumannEntropyBits (aliceDensity ψ)

def FinitePureEnsemble.averageAliceEntropy {ρ : Matrix (A × B) (A × B) ℂ}
    (E : FinitePureEnsemble ρ) : ℝ := ∑ j, E.weight j * aliceEntropy (E.vector j)

theorem alice_entropy_ge_nat_of_purity (ψ : A × B → ℂ) (hnorm : vectorNormSq ψ = 1)
    (n : ℕ) (hcap : purity (partialTraceLeft (pureDensity ψ)) ≤ (1 / 2 : ℝ) ^ n) :
    (n : ℝ) ≤ aliceEntropy ψ := by
  apply density_entropy_ge_nat_of_purity _
    (partialTraceLeft_posSemidef _ (pureDensity_posSemidef ψ)) _ n hcap
  change Matrix.trace (partialTraceLeft (pureDensity ψ)) = 1
  rw [partialTraceLeft_trace, pureDensity_trace, hnorm]
  rfl

theorem FinitePureEnsemble.average_entropy_lower_from_range_purity
    {ρ : Matrix (A × B) (A × B) ℂ} (E : FinitePureEnsemble ρ)
    (P : Matrix (A × B) (A × B) ℂ) (hP : P * P = P)
    (hsupp : ρ = P * ρ * P) (n : ℕ)
    (hpur : ∀ ψ : A × B → ℂ, vectorNormSq ψ = 1 → P.mulVec ψ = ψ →
      purity (partialTraceLeft (pureDensity ψ)) ≤ (1 / 2 : ℝ) ^ n) :
    (n : ℝ) ≤ E.averageAliceEntropy := by
  have ht (j : Fin E.count) : E.weight j * (n : ℝ) ≤ E.weight j * aliceEntropy (E.vector j) := by
    by_cases hz : E.weight j = 0
    · simp [hz]
    · have hj : 0 < E.weight j := lt_of_le_of_ne (E.weight_nonneg j) (Ne.symm hz)
      exact mul_le_mul_of_nonneg_left
        (alice_entropy_ge_nat_of_purity (E.vector j) (E.normalized j) n
          (hpur (E.vector j) (E.normalized j) (E.support_inheritance P hP hsupp j hj)))
        (E.weight_nonneg j)
  have hsum := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => ht j)
  simpa only [← Finset.sum_mul, E.weight_sum, one_mul, FinitePureEnsemble.averageAliceEntropy] using hsum

def finiteConvexRoof (ρ : Matrix (A × B) (A × B) ℂ) : EReal :=
  ⨅ E : FinitePureEnsemble ρ, (E.averageAliceEntropy : EReal)

theorem finiteConvexRoof_lower_from_range_purity (ρ : Matrix (A × B) (A × B) ℂ)
    (P : Matrix (A × B) (A × B) ℂ) (hP : P * P = P)
    (hsupp : ρ = P * ρ * P) (n : ℕ)
    (hpur : ∀ ψ : A × B → ℂ, vectorNormSq ψ = 1 → P.mulVec ψ = ψ →
      purity (partialTraceLeft (pureDensity ψ)) ≤ (1 / 2 : ℝ) ^ n) :
    (n : EReal) ≤ finiteConvexRoof ρ := by
  apply le_iInf
  intro E
  exact_mod_cast E.average_entropy_lower_from_range_purity P hP hsupp n hpur

theorem FinitePureEnsemble.trace_one {ρ : Matrix X X ℂ} (E : FinitePureEnsemble ρ) :
    Matrix.trace ρ = 1 := by
  rw [E.barycenter, Matrix.trace_sum]
  simp only [Matrix.trace_smul, pureDensity_trace, E.normalized,
    Complex.ofReal_one, smul_eq_mul, mul_one]
  exact_mod_cast E.weight_sum

theorem projector_sandwich_trace (P ρ : Matrix X X ℂ)
    (hPH : P.conjTranspose = P) (hP2 : P * P = P) :
    Matrix.trace (P * ρ * P.conjTranspose) = Matrix.trace (P * ρ) := by
  rw [Matrix.trace_mul_cycle, hPH, hP2]

theorem complement_projector_idempotent (P : Matrix X X ℂ) (hP2 : P * P = P) :
    (1-P) * (1-P) = 1-P := by
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hP2]
  abel

theorem complement_projector_hermitian (P : Matrix X X ℂ)
    (hPH : P.conjTranspose = P) : (1-P).conjTranspose = 1-P := by
  simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hPH]

theorem FinitePureEnsemble.projector_mass {ρ : Matrix X X ℂ}
    (E : FinitePureEnsemble ρ) (P : Matrix X X ℂ)
    (hPH : P.conjTranspose = P) (hP2 : P * P = P) :
    (∑ j, E.weight j * vectorNormSq (P.mulVec (E.vector j))) =
      (Matrix.trace (P * ρ)).re := by
  have ht := E.residual_trace P
  rw [projector_sandwich_trace P ρ hPH hP2] at ht
  exact ht.symm

theorem FinitePureEnsemble.projector_leakage {ρ : Matrix X X ℂ}
    (E : FinitePureEnsemble ρ) (P : Matrix X X ℂ)
    (hPH : P.conjTranspose = P) (hP2 : P * P = P) :
    (∑ j, E.weight j * vectorNormSq ((1-P).mulVec (E.vector j))) =
      1 - (Matrix.trace (P * ρ)).re := by
  rw [E.projector_mass (1-P) (complement_projector_hermitian P hPH)
    (complement_projector_idempotent P hP2)]
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub, E.trace_one]
  simp only [Complex.sub_re, Complex.one_re]

theorem projector_vectorNormSq_split (P : Matrix X X ℂ)
    (hPH : P.conjTranspose = P) (hP2 : P * P = P) (v : X → ℂ) :
    vectorNormSq (P.mulVec v) + vectorNormSq ((1-P).mulVec v) = vectorNormSq v := by
  have hp := projector_sandwich_trace P (pureDensity v) hPH hP2
  have hr := projector_sandwich_trace (1-P) (pureDensity v)
    (complement_projector_hermitian P hPH) (complement_projector_idempotent P hP2)
  have hsand (Q : Matrix X X ℂ) : Q * pureDensity v * Q.conjTranspose =
      pureDensity (Q.mulVec v) := sandwich_crossDensity Q v v
  rw [hsand P, pureDensity_trace] at hp
  rw [hsand (1-P), pureDensity_trace] at hr
  have hcomp : P + (1-P) = 1 := by abel
  have hsum : Matrix.trace (P * pureDensity v) + Matrix.trace ((1-P) * pureDensity v) =
      Matrix.trace (pureDensity v) := by
    rw [← Matrix.trace_add, ← Matrix.add_mul, hcomp, Matrix.one_mul]
  rw [← hp, ← hr, pureDensity_trace] at hsum
  exact_mod_cast hsum

theorem projector_vectorNormSq_le_one (P : Matrix X X ℂ)
    (hPH : P.conjTranspose = P) (hP2 : P * P = P)
    (v : X → ℂ) (hv : vectorNormSq v = 1) :
    vectorNormSq (P.mulVec v) ≤ 1 := by
  have hs := projector_vectorNormSq_split P hPH hP2 v
  have hr := vectorNormSq_nonneg ((1-P).mulVec v)
  rw [hv] at hs
  linarith

def normalizedProjectorVector (P : Matrix X X ℂ) (v : X → ℂ) : X → ℂ :=
  (((Real.sqrt (vectorNormSq (P.mulVec v)))⁻¹ : ℝ) : ℂ) • P.mulVec v

theorem normalizedProjectorVector_range (P : Matrix X X ℂ) (hP2 : P * P = P)
    (v : X → ℂ) : P.mulVec (normalizedProjectorVector P v) = normalizedProjectorVector P v := by
  rw [normalizedProjectorVector, Matrix.mulVec_smul, Matrix.mulVec_mulVec, hP2]

theorem normalizedProjectorVector_normSq (P : Matrix X X ℂ) (v : X → ℂ)
    (hp : 0 < vectorNormSq (P.mulVec v)) :
    vectorNormSq (normalizedProjectorVector P v) = 1 := by
  have hscale : Complex.normSq (((Real.sqrt (vectorNormSq (P.mulVec v)))⁻¹ : ℝ) : ℂ) =
      (vectorNormSq (P.mulVec v))⁻¹ := by
    simp only [Complex.normSq_ofReal, ← sq, inv_pow]
    rw [Real.sq_sqrt (vectorNormSq_nonneg _)]
  rw [normalizedProjectorVector, matrix_vectorNormSq_scalar, hscale,
    inv_mul_cancel₀ (ne_of_gt hp)]

theorem normalizedProjectorVector_density (P : Matrix X X ℂ) (v : X → ℂ) :
    pureDensity (normalizedProjectorVector P v) =
      (((vectorNormSq (P.mulVec v))⁻¹ : ℝ) : ℂ) •
        (P * pureDensity v * P.conjTranspose) := by
  have hscale : Complex.normSq (((Real.sqrt (vectorNormSq (P.mulVec v)))⁻¹ : ℝ) : ℂ) =
      (vectorNormSq (P.mulVec v))⁻¹ := by
    simp only [Complex.normSq_ofReal, ← sq, inv_pow]
    rw [Real.sq_sqrt (vectorNormSq_nonneg _)]
  rw [normalizedProjectorVector, matrix_pureDensity_scalar, hscale]
  rw [show P * pureDensity v * P.conjTranspose = pureDensity (P.mulVec v) from
    sandwich_crossDensity P v v]

theorem vectorNormSq_complex_dot (v : X → ℂ) :
    (vectorNormSq v : ℂ) = dotProduct (star v) v := by
  simp [vectorNormSq, dotProduct, Pi.star_apply, Complex.mul_conj, mul_comm]

theorem projector_normSq_expectation (P : Matrix X X ℂ)
    (hPH : P.conjTranspose = P) (hP2 : P * P = P) (v : X → ℂ) :
    (vectorNormSq (P.mulVec v) : ℂ) = dotProduct (star v) (P.mulVec v) := by
  rw [vectorNormSq_complex_dot, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec,
    Matrix.mulVec_mulVec, hPH, hP2]

theorem normalizedProjectorVector_overlap (P : Matrix X X ℂ)
    (hPH : P.conjTranspose = P) (hP2 : P * P = P) (v : X → ℂ)
    (hp : 0 < vectorNormSq (P.mulVec v)) :
    Complex.normSq (dotProduct (star v) (normalizedProjectorVector P v)) =
      vectorNormSq (P.mulVec v) := by
  have hscale : Complex.normSq (((Real.sqrt (vectorNormSq (P.mulVec v)))⁻¹ : ℝ) : ℂ) =
      (vectorNormSq (P.mulVec v))⁻¹ := by
    simp only [Complex.normSq_ofReal, ← sq, inv_pow]
    rw [Real.sq_sqrt (vectorNormSq_nonneg _)]
  have heq : dotProduct (star v) (normalizedProjectorVector P v) =
      (((Real.sqrt (vectorNormSq (P.mulVec v)))⁻¹ : ℝ) : ℂ) *
        dotProduct (star v) (P.mulVec v) := by
    simp [normalizedProjectorVector, dotProduct, Pi.smul_apply,
      smul_eq_mul, Finset.mul_sum, mul_left_comm]
  rw [heq, ← projector_normSq_expectation P hPH hP2 v,
    Complex.normSq_mul, hscale, Complex.normSq_ofReal]
  field_simp [ne_of_gt hp]

theorem pureDensity_mul_trace (v w : X → ℂ) :
    Matrix.trace (pureDensity v * pureDensity w) =
      (Complex.normSq (dotProduct (star v) w) : ℂ) := by
  have hprod : Matrix.trace (pureDensity v * pureDensity w) =
      (∑ i, v i * star (w i)) * (∑ j, star (v j) * w j) := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, pureDensity,
      crossDensity, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hstar : (∑ i, v i * star (w i)) = star (dotProduct (star v) w) := by
    simp [dotProduct, star_sum, star_mul, mul_comm]
  rw [hprod]
  change (∑ i, v i * star (w i)) * dotProduct (star v) w = _
  rw [hstar, mul_comm]
  simpa only [Complex.star_def] using Complex.mul_conj (dotProduct (star v) w)

theorem pureDensity_difference_rank_le_two (v w : X → ℂ) :
    Matrix.rank (pureDensity v - pureDensity w) ≤ 2 := by
  let U : Matrix X (Fin 2) ℂ := Matrix.of (fun i p => if p = 0 then v i else w i)
  let V : Matrix (Fin 2) X ℂ := Matrix.of (fun p j => if p = 0 then star (v j) else -star (w j))
  have hf : pureDensity v - pureDensity w = U * V := by
    ext i j
    change v i * star (v j) - w i * star (w j) = ∑ p : Fin 2, U i p * V p j
    simp [U, V, Fin.sum_univ_two, sub_eq_add_neg]
  rw [hf]
  exact (Matrix.rank_mul_le_left U V).trans (by simpa using Matrix.rank_le_card_width U)

theorem pureDensity_difference_hsNormSq (v w : X → ℂ)
    (hv : vectorNormSq v = 1) (hw : vectorNormSq w = 1) :
    hsNormSq (pureDensity v - pureDensity w) =
      2 * (1 - Complex.normSq (dotProduct (star v) w)) := by
  have hD : (pureDensity v - pureDensity w).conjTranspose = pureDensity v - pureDensity w := by
    ext i j
    simp [Matrix.conjTranspose_apply, Matrix.sub_apply, pureDensity,
      crossDensity, star_mul, mul_comm]
  have hvv : dotProduct (star v) v = 1 := by
    rw [← vectorNormSq_complex_dot, hv]
    rfl
  have hww : dotProduct (star w) w = 1 := by
    rw [← vectorNormSq_complex_dot, hw]
    rfl
  rw [hsNormSq_eq_trace, hD, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub]
  simp only [Matrix.trace_sub]
  rw [Matrix.trace_mul_comm (pureDensity w) (pureDensity v)]
  simp only [pureDensity_mul_trace, hvv, hww, Complex.normSq_one,
    Complex.ofReal_one, Complex.sub_re, Complex.one_re, Complex.ofReal_re]
  ring

theorem normalizedProjectorVector_schatten_distance
    (P : Matrix X X ℂ) (hPH : P.conjTranspose = P) (hP2 : P * P = P)
    (v : X → ℂ) (hv : vectorNormSq v = 1) (hp : 0 < vectorNormSq (P.mulVec v)) :
    SchattenSupport.schattenOne (pureDensity v - pureDensity (normalizedProjectorVector P v)) ≤
      2 * Real.sqrt (1 - vectorNormSq (P.mulVec v)) := by
  let D := pureDensity v - pureDensity (normalizedProjectorVector P v)
  have hh : hsNormSq D = 2 * (1 - vectorNormSq (P.mulVec v)) := by
    dsimp only [D]
    rw [pureDensity_difference_hsNormSq v _ hv (normalizedProjectorVector_normSq P v hp),
      normalizedProjectorVector_overlap P hPH hP2 v hp]
  have hr : (Matrix.rank D : ℝ) ≤ 2 := by
    exact_mod_cast pureDensity_difference_rank_le_two v (normalizedProjectorVector P v)
  have hn : 0 ≤ hsNormSq D := Finset.sum_nonneg (fun i _ =>
    Finset.sum_nonneg (fun j _ => sq_nonneg ‖D i j‖))
  have hs := SchattenSupport.schattenOne_sq_le_rank_hsNormSq D
  have hsq : SchattenSupport.schattenOne D ^ 2 ≤
      4 * (1 - vectorNormSq (P.mulVec v)) := by
    calc
      _ ≤ (Matrix.rank D : ℝ) * hsNormSq D := hs
      _ ≤ 2 * hsNormSq D := mul_le_mul_of_nonneg_right hr hn
      _ = _ := by rw [hh]; ring
  have hleak : 0 ≤ 1 - vectorNormSq (P.mulVec v) := by
    linarith [projector_vectorNormSq_le_one P hPH hP2 v hv]
  nlinarith [SchattenSupport.schattenOne_nonneg D,
    Real.sqrt_nonneg (1 - vectorNormSq (P.mulVec v)), Real.sq_sqrt hleak]

theorem pureDensity_schatten_distance_le_two (v w : X → ℂ)
    (hv : vectorNormSq v = 1) (hw : vectorNormSq w = 1) :
    SchattenSupport.schattenOne (pureDensity v - pureDensity w) ≤ 2 := by
  let D := pureDensity v - pureDensity w
  have hr : (Matrix.rank D : ℝ) ≤ 2 := by
    exact_mod_cast pureDensity_difference_rank_le_two v w
  have hn : 0 ≤ hsNormSq D := Finset.sum_nonneg (fun i _ =>
    Finset.sum_nonneg (fun j _ => sq_nonneg ‖D i j‖))
  have hs := SchattenSupport.schattenOne_sq_le_rank_hsNormSq D
  have hh : hsNormSq D = 2 * (1-Complex.normSq (dotProduct (star v) w)) :=
    pureDensity_difference_hsNormSq v w hv hw
  have hsq : SchattenSupport.schattenOne D ^ 2 ≤ 4 := by
    calc
      _ ≤ (Matrix.rank D : ℝ) * hsNormSq D := hs
      _ ≤ 2 * hsNormSq D := mul_le_mul_of_nonneg_right hr hn
      _ ≤ 4 := by rw [hh]; nlinarith [Complex.normSq_nonneg (dotProduct (star v) w)]
  nlinarith [SchattenSupport.schattenOne_nonneg D]

def supportedProjectionOr (P : Matrix X X ℂ) (v fallback : X → ℂ) : X → ℂ :=
  if vectorNormSq (P.mulVec v) = 0 then fallback else normalizedProjectorVector P v

theorem supportedProjectionOr_normSq (P : Matrix X X ℂ) (v fallback : X → ℂ)
    (hf : vectorNormSq fallback = 1) :
    vectorNormSq (supportedProjectionOr P v fallback) = 1 := by
  by_cases hz : vectorNormSq (P.mulVec v) = 0
  · simp only [supportedProjectionOr, hz, if_pos, hf]
  · simp only [supportedProjectionOr, hz, if_neg]
    exact normalizedProjectorVector_normSq P v
      (lt_of_le_of_ne (vectorNormSq_nonneg _) (Ne.symm hz))

theorem supportedProjectionOr_range (P : Matrix X X ℂ) (hP2 : P * P = P)
    (v fallback : X → ℂ) (hf : P.mulVec fallback = fallback) :
    P.mulVec (supportedProjectionOr P v fallback) = supportedProjectionOr P v fallback := by
  by_cases hz : vectorNormSq (P.mulVec v) = 0
  · simp only [supportedProjectionOr, hz, if_pos, hf]
  · simp only [supportedProjectionOr, hz, if_neg]
    exact normalizedProjectorVector_range P hP2 v

theorem supportedProjectionOr_schatten_distance (P : Matrix X X ℂ)
    (hPH : P.conjTranspose = P) (hP2 : P * P = P) (v fallback : X → ℂ)
    (hv : vectorNormSq v = 1) (hf : vectorNormSq fallback = 1) :
    SchattenSupport.schattenOne (pureDensity v - pureDensity (supportedProjectionOr P v fallback)) ≤
      2 * Real.sqrt (1-vectorNormSq (P.mulVec v)) := by
  by_cases hz : vectorNormSq (P.mulVec v) = 0
  · simp only [supportedProjectionOr, hz, if_pos, sub_zero, Real.sqrt_one, mul_one]
    exact pureDensity_schatten_distance_le_two v fallback hv hf
  · simp only [supportedProjectionOr, hz, if_neg]
    exact normalizedProjectorVector_schatten_distance P hPH hP2 v hv
      (lt_of_le_of_ne (vectorNormSq_nonneg _) (Ne.symm hz))

theorem exists_supported_nearby (P : Matrix X X ℂ)
    (hPH : P.conjTranspose = P) (hP2 : P * P = P)
    (fallback : X → ℂ) (hf : vectorNormSq fallback = 1) (hfr : P.mulVec fallback = fallback)
    (v : X → ℂ) (hv : vectorNormSq v = 1) :
    ∃ w : X → ℂ, vectorNormSq w = 1 ∧ P.mulVec w = w ∧
      SchattenSupport.schattenOne (pureDensity v - pureDensity w) ≤
        2 * Real.sqrt (1-vectorNormSq (P.mulVec v)) :=
  ⟨supportedProjectionOr P v fallback,
    supportedProjectionOr_normSq P v fallback hf,
    supportedProjectionOr_range P hP2 v fallback hfr,
    supportedProjectionOr_schatten_distance P hPH hP2 v fallback hv hf⟩

theorem FinitePureEnsemble.posSemidef {ρ : Matrix X X ℂ} (E : FinitePureEnsemble ρ) :
    ρ.PosSemidef := by
  rw [E.barycenter]
  apply Matrix.posSemidef_sum
  intro j _
  have hscale : (E.weight j : ℂ) • pureDensity (E.vector j) =
      E.weight j • pureDensity (E.vector j) := by
    ext i k
    simp only [Matrix.smul_apply, RCLike.real_smul_eq_coe_mul, smul_eq_mul,
      rclike_complex_cast]
  rw [hscale]
  exact (pureDensity_posSemidef _).smul (E.weight_nonneg j)

def FinitePureEnsemble.supportedReplacementDensity {ρ : Matrix X X ℂ}
    (E : FinitePureEnsemble ρ) (P : Matrix X X ℂ) (fallback : X → ℂ) : Matrix X X ℂ :=
  ∑ j, (E.weight j : ℂ) • pureDensity (supportedProjectionOr P (E.vector j) fallback)

def FinitePureEnsemble.supportedReplacementEnsemble {ρ : Matrix X X ℂ}
    (E : FinitePureEnsemble ρ) (P : Matrix X X ℂ) (fallback : X → ℂ)
    (hf : vectorNormSq fallback = 1) :
    FinitePureEnsemble (E.supportedReplacementDensity P fallback) where
  count := E.count
  weight := E.weight
  weight_nonneg := E.weight_nonneg
  weight_sum := E.weight_sum
  vector := fun j => supportedProjectionOr P (E.vector j) fallback
  normalized := fun j => supportedProjectionOr_normSq P (E.vector j) fallback hf
  barycenter := rfl

@[simp] theorem FinitePureEnsemble.supportedReplacementEnsemble_count {ρ : Matrix X X ℂ}
    (E : FinitePureEnsemble ρ) (P : Matrix X X ℂ) (fallback : X → ℂ)
    (hf : vectorNormSq fallback = 1) :
    (E.supportedReplacementEnsemble P fallback hf).count = E.count := rfl

@[simp] theorem FinitePureEnsemble.supportedReplacementEnsemble_weight {ρ : Matrix X X ℂ}
    (E : FinitePureEnsemble ρ) (P : Matrix X X ℂ) (fallback : X → ℂ)
    (hf : vectorNormSq fallback = 1) (j : Fin E.count) :
    (E.supportedReplacementEnsemble P fallback hf).weight j = E.weight j := rfl

@[simp] theorem FinitePureEnsemble.supportedReplacementEnsemble_vector {ρ : Matrix X X ℂ}
    (E : FinitePureEnsemble ρ) (P : Matrix X X ℂ) (fallback : X → ℂ)
    (hf : vectorNormSq fallback = 1) (j : Fin E.count) :
    (E.supportedReplacementEnsemble P fallback hf).vector j =
      supportedProjectionOr P (E.vector j) fallback := rfl

theorem FinitePureEnsemble.supportedReplacementDensity_posSemidef {ρ : Matrix X X ℂ}
    (E : FinitePureEnsemble ρ) (P : Matrix X X ℂ) (fallback : X → ℂ)
    (hf : vectorNormSq fallback = 1) : (E.supportedReplacementDensity P fallback).PosSemidef :=
  (E.supportedReplacementEnsemble P fallback hf).posSemidef

theorem FinitePureEnsemble.supportedReplacementDensity_trace {ρ : Matrix X X ℂ}
    (E : FinitePureEnsemble ρ) (P : Matrix X X ℂ) (fallback : X → ℂ)
    (hf : vectorNormSq fallback = 1) : Matrix.trace (E.supportedReplacementDensity P fallback) = 1 :=
  (E.supportedReplacementEnsemble P fallback hf).trace_one

theorem FinitePureEnsemble.supportedReplacementEnsemble_range {ρ : Matrix X X ℂ}
    (E : FinitePureEnsemble ρ) (P : Matrix X X ℂ) (hP2 : P * P = P)
    (fallback : X → ℂ) (hf : vectorNormSq fallback = 1)
    (hfr : P.mulVec fallback = fallback) (j : Fin E.count) :
    P.mulVec ((E.supportedReplacementEnsemble P fallback hf).vector j) =
      (E.supportedReplacementEnsemble P fallback hf).vector j :=
  supportedProjectionOr_range P hP2 (E.vector j) fallback hfr

theorem FinitePureEnsemble.supportedReplacementDensity_support {ρ : Matrix X X ℂ}
    (E : FinitePureEnsemble ρ) (P : Matrix X X ℂ)
    (hPH : P.conjTranspose = P) (hP2 : P * P = P)
    (fallback : X → ℂ) (hfr : P.mulVec fallback = fallback) :
    E.supportedReplacementDensity P fallback =
      P * E.supportedReplacementDensity P fallback * P := by
  symm
  simp only [FinitePureEnsemble.supportedReplacementDensity,
    Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul]
  apply Finset.sum_congr rfl
  intro j _
  have hs := sandwich_crossDensity P (supportedProjectionOr P (E.vector j) fallback)
    (supportedProjectionOr P (E.vector j) fallback)
  rw [hPH, supportedProjectionOr_range P hP2 (E.vector j) fallback hfr] at hs
  exact congrArg (fun Q : Matrix X X ℂ => (E.weight j : ℂ) • Q) hs

theorem weighted_sqrt_average_le {K : Type*} [Fintype K]
    (weight leak : K → ℝ) (hw : ∀ j, 0 ≤ weight j)
    (hw1 : ∑ j, weight j = 1) (hl : ∀ j, 0 ≤ leak j) :
    (∑ j, weight j * Real.sqrt (leak j)) ≤ Real.sqrt (∑ j, weight j * leak j) := by
  have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (Finset.univ : Finset K)
    (r := fun j => weight j * Real.sqrt (leak j))
    (f := weight) (g := fun j => weight j * leak j)
    (fun j _ => hw j) (fun j _ => mul_nonneg (hw j) (hl j))
    (by
      intro j _
      rw [mul_pow, Real.sq_sqrt (hl j)]
      exact le_of_eq (by ring))
  rw [hw1, one_mul] at hcs
  have hn : 0 ≤ ∑ j, weight j * leak j :=
    Finset.sum_nonneg (fun j _ => mul_nonneg (hw j) (hl j))
  have ha : 0 ≤ ∑ j, weight j * Real.sqrt (leak j) :=
    Finset.sum_nonneg (fun j _ => mul_nonneg (hw j) (Real.sqrt_nonneg _))
  nlinarith [Real.sq_sqrt hn, Real.sqrt_nonneg (∑ j, weight j * leak j)]

theorem FinitePureEnsemble.projector_leakage_bounds {ρ : Matrix X X ℂ}
    (E : FinitePureEnsemble ρ) (P : Matrix X X ℂ)
    (hPH : P.conjTranspose = P) (hP2 : P * P = P) :
    0 ≤ 1 - (Matrix.trace (P * ρ)).re ∧ 1 - (Matrix.trace (P * ρ)).re ≤ 1 := by
  have hl : 0 ≤ ∑ j, E.weight j * vectorNormSq ((1-P).mulVec (E.vector j)) :=
    Finset.sum_nonneg (fun j _ => mul_nonneg (E.weight_nonneg j) (vectorNormSq_nonneg _))
  have hm : 0 ≤ ∑ j, E.weight j * vectorNormSq (P.mulVec (E.vector j)) :=
    Finset.sum_nonneg (fun j _ => mul_nonneg (E.weight_nonneg j) (vectorNormSq_nonneg _))
  rw [E.projector_leakage P hPH hP2] at hl
  rw [E.projector_mass P hPH hP2] at hm
  exact ⟨hl, by linarith⟩

theorem FinitePureEnsemble.supportedReplacement_average_distance_le_leakage
    {ρ : Matrix X X ℂ} (E : FinitePureEnsemble ρ) (P : Matrix X X ℂ)
    (hPH : P.conjTranspose = P) (hP2 : P * P = P)
    (fallback : X → ℂ) (hf : vectorNormSq fallback = 1) :
    (∑ j, E.weight j * SchattenSupport.schattenOne
      (pureDensity (E.vector j) - pureDensity (supportedProjectionOr P (E.vector j) fallback))) ≤
      2 * Real.sqrt (∑ j, E.weight j * vectorNormSq ((1-P).mulVec (E.vector j))) := by
  have hleak (j : Fin E.count) : vectorNormSq ((1-P).mulVec (E.vector j)) =
      1-vectorNormSq (P.mulVec (E.vector j)) := by
    have hs := projector_vectorNormSq_split P hPH hP2 (E.vector j)
    rw [E.normalized j] at hs
    linarith
  calc
    _ ≤ ∑ j, E.weight j * (2 * Real.sqrt (vectorNormSq ((1-P).mulVec (E.vector j)))) := by
      apply Finset.sum_le_sum
      intro j _
      have hd := supportedProjectionOr_schatten_distance P hPH hP2 (E.vector j) fallback
        (E.normalized j) hf
      rw [← hleak j] at hd
      exact mul_le_mul_of_nonneg_left hd (E.weight_nonneg j)
    _ = 2 * ∑ j, E.weight j * Real.sqrt (vectorNormSq ((1-P).mulVec (E.vector j))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (weighted_sqrt_average_le E.weight (fun j => vectorNormSq ((1-P).mulVec (E.vector j)))
        E.weight_nonneg E.weight_sum (fun _ => vectorNormSq_nonneg _)) (by norm_num)

theorem FinitePureEnsemble.supportedReplacement_average_distance_le
    {ρ : Matrix X X ℂ} (E : FinitePureEnsemble ρ) (P : Matrix X X ℂ)
    (hPH : P.conjTranspose = P) (hP2 : P * P = P)
    (fallback : X → ℂ) (hf : vectorNormSq fallback = 1) :
    (∑ j, E.weight j * SchattenSupport.schattenOne
      (pureDensity (E.vector j) - pureDensity (supportedProjectionOr P (E.vector j) fallback))) ≤
      2 * Real.sqrt (1 - (Matrix.trace (P * ρ)).re) := by
  rw [← E.projector_leakage P hPH hP2]
  exact E.supportedReplacement_average_distance_le_leakage P hPH hP2 fallback hf

theorem FinitePureEnsemble.supportedReplacement_certificate
    {ρ : Matrix X X ℂ} (E : FinitePureEnsemble ρ) (P : Matrix X X ℂ)
    (hPH : P.conjTranspose = P) (hP2 : P * P = P)
    (fallback : X → ℂ) (hf : vectorNormSq fallback = 1) (hfr : P.mulVec fallback = fallback) :
    (E.supportedReplacementDensity P fallback).PosSemidef ∧
    Matrix.trace (E.supportedReplacementDensity P fallback) = 1 ∧
    E.supportedReplacementDensity P fallback = P * E.supportedReplacementDensity P fallback * P ∧
    (∀ j : Fin E.count, vectorNormSq (supportedProjectionOr P (E.vector j) fallback) = 1 ∧
      P.mulVec (supportedProjectionOr P (E.vector j) fallback) =
        supportedProjectionOr P (E.vector j) fallback) ∧
    (∑ j, E.weight j * SchattenSupport.schattenOne
      (pureDensity (E.vector j) - pureDensity (supportedProjectionOr P (E.vector j) fallback))) ≤
      2 * Real.sqrt (1 - (Matrix.trace (P * ρ)).re) := by
  refine ⟨E.supportedReplacementDensity_posSemidef P fallback hf,
    E.supportedReplacementDensity_trace P fallback hf,
    E.supportedReplacementDensity_support P hPH hP2 fallback hfr, ?_,
    E.supportedReplacement_average_distance_le P hPH hP2 fallback hf⟩
  intro j
  exact ⟨supportedProjectionOr_normSq P (E.vector j) fallback hf,
    supportedProjectionOr_range P hP2 (E.vector j) fallback hfr⟩

end QuantumProver.WernerEndpoint.AntisymmetricEnsembleCost

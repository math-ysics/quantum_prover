import QuantumProver.InformationTheory.WernerEndpoint.TakagiRankSix
import QuantumProver.InformationTheory.WernerEndpoint.ChannelCoherence

noncomputable section

namespace QuantumProver.WernerEndpoint.TakagiContraction

open scoped BigOperators ComplexOrder
open Matrix ComplexTakagi SchattenSupport TakagiRankSix

variable {Y B E : Type*} [Fintype Y] [Fintype B] [Fintype E] [DecidableEq Y]

def unitaryColumn (U : Matrix.unitaryGroup Y ℂ) (i : Y) : Y → ℂ :=
  fun y => (U : Matrix Y Y ℂ) y i

theorem unitaryColumn_normSq (U : Matrix.unitaryGroup Y ℂ) (i : Y) :
    vectorNormSq (unitaryColumn U i) = 1 := by
  have h := congrArg (fun M : Matrix Y Y ℂ => (M i i).re) (unitary_left U)
  simpa [vectorNormSq, unitaryColumn, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.mul_conj, mul_comm, Complex.re_sum] using h

theorem unitaryColumn_orthogonal (U : Matrix.unitaryGroup Y ℂ) (i j : Y) (hij : i ≠ j) :
    (∑ y, unitaryColumn U i y * star (unitaryColumn U j y)) = 0 := by
  have h := congrArg (fun M : Matrix Y Y ℂ => M j i) (unitary_left U)
  simpa [unitaryColumn, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.one_apply, hij.symm, mul_comm] using h

def transitionSquare (N : Stinespring Y B E) (U : Matrix.unitaryGroup Y ℂ) (i j : Y) : ℂ :=
  Matrix.trace (N.apply (crossDensity (unitaryColumn U j) (unitaryColumn U i)) *
    N.apply (crossDensity (unitaryColumn U j) (unitaryColumn U i)))

theorem transitionSquare_diagonal_nonneg (N : Stinespring Y B E)
    (U : Matrix.unitaryGroup Y ℂ) (i : Y) : 0 ≤ (transitionSquare N U i i).re := by
  change 0 ≤ purity (N.apply (pureDensity (unitaryColumn U i)))
  exact purity_nonneg_of_hermitian _ (N.apply_posSemidef _ (pureDensity_posSemidef _)).isHermitian

theorem transitionSquare_offdiagonal_lower (N : Stinespring Y B E) (β : ℝ)
    (hbound : ∀ w : Y → ℂ, vectorNormSq w = 1 → purity (N.apply (pureDensity w)) ≤ β)
    (U : Matrix.unitaryGroup Y ℂ) (i j : Y) (hij : i ≠ j) :
    -β / 2 ≤ (transitionSquare N U i j).re := by
  have h := N.orthogonal_transition_coherence β hbound
    (unitaryColumn U i) (unitaryColumn U j) (unitaryColumn_normSq U i)
    (unitaryColumn_normSq U j) (unitaryColumn_orthogonal U i j hij)
  have hr := Complex.abs_re_le_norm (transitionSquare N U i j)
  have hl := neg_le_of_abs_le hr
  change ‖transitionSquare N U i j‖ ≤ β / 2 at h
  linarith

theorem offdiagonal_weight_sum (s : Y → ℝ) :
    (∑ i, ∑ j, if i = j then 0 else s i * s j) =
      (∑ i, s i) ^ 2 - ∑ i, s i ^ 2 := by
  have hp (i j) : (if i = j then 0 else s i * s j) =
      s i * s j - (if i = j then s i ^ 2 else 0) := by
    by_cases h : i = j
    · subst j
      simp [pow_two]
    · simp [h]
  simp_rw [hp, Finset.sum_sub_distrib]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
  simp_rw [← Finset.mul_sum]
  rw [← Finset.sum_mul]
  ring

theorem takagi_weighted_trace_lower (N : Stinespring Y B E) (β : ℝ)
    (hbound : ∀ w : Y → ℂ, vectorNormSq w = 1 → purity (N.apply (pureDensity w)) ≤ β)
    (U : Matrix.unitaryGroup Y ℂ) (s : Y → ℝ) (hs : ∀ i, 0 ≤ s i) :
    -β * ((∑ i, s i) ^ 2 - ∑ i, s i ^ 2) / 2 ≤
      ∑ i, ∑ j, s i * s j * (transitionSquare N U i j).re := by
  have ht : (∑ i, ∑ j, if i = j then 0 else (-β / 2) * (s i * s j)) ≤
      ∑ i, ∑ j, s i * s j * (transitionSquare N U i j).re := by
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    by_cases hij : i = j
    · subst j
      rw [if_pos rfl]
      exact mul_nonneg (mul_nonneg (hs i) (hs i)) (transitionSquare_diagonal_nonneg N U i)
    · rw [if_neg hij]
      have h := mul_le_mul_of_nonneg_left (transitionSquare_offdiagonal_lower N β hbound U i j hij)
        (mul_nonneg (hs i) (hs j))
      simpa only [mul_comm] using h
  have hf (i j) : (if i = j then 0 else (-β / 2) * (s i * s j)) =
      (-β / 2) * (if i = j then 0 else s i * s j) := by
    split_ifs <;> simp
  simp_rw [hf, ← Finset.mul_sum] at ht
  rw [offdiagonal_weight_sum] at ht
  nlinarith

theorem matrixVec_sum {I : Type*} [Fintype I] {J : Type*} [Fintype J]
    (K : Matrix J J ℂ) (v : I → J → ℂ) :
    K.mulVec (∑ i, v i) = ∑ i, K.mulVec (v i) := by
  ext j
  simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Finset.mul_sum]
  rw [Finset.sum_comm]

theorem quadratic_real_sum {I : Type*} [Fintype I] {J : Type*} [Fintype J]
    (K : Matrix J J ℂ) (v : I → J → ℂ) (s : I → ℝ) :
    dotProduct (star (∑ i, (s i : ℂ) • v i))
      (K.mulVec (∑ i, (s i : ℂ) • v i)) =
      ∑ i, ∑ j, ((s i * s j : ℝ) : ℂ) * dotProduct (star (v i)) (K.mulVec (v j)) := by
  simp only [star_sum, matrixVec_sum, star_smul, Matrix.mulVec_smul,
    sum_dotProduct, dotProduct_sum, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp [Complex.star_def, mul_assoc]
  ring

theorem takagi_vector_expansion (M : Matrix Y Y ℂ) (U : Matrix.unitaryGroup Y ℂ) (s : Y → ℝ)
    (hM : M = (U : Matrix Y Y ℂ) * Matrix.diagonal (fun i => Complex.ofReal (s i)) *
      (U : Matrix Y Y ℂ)ᵀ) :
    (fun ij : Y × Y => M ij.1 ij.2) =
      ∑ i, (s i : ℂ) • tensorVector (unitaryColumn U i) (unitaryColumn U i) := by
  funext ij
  rw [hM, Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul, tensorVector, unitaryColumn]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem actual_takagi_contraction_expansion (N : Stinespring Y B E)
    (M : Matrix Y Y ℂ) (U : Matrix.unitaryGroup Y ℂ) (s : Y → ℝ)
    (hM : M = (U : Matrix Y Y ℂ) * Matrix.diagonal (fun i => Complex.ofReal (s i)) *
      (U : Matrix Y Y ℂ)ᵀ) :
    (dotProduct (star (fun ij : Y × Y => M ij.1 ij.2))
      (N.replicaKernel.mulVec (fun ij : Y × Y => M ij.1 ij.2))).re =
      ∑ i, ∑ j, s i * s j * (transitionSquare N U i j).re := by
  rw [takagi_vector_expansion M U s hM, quadratic_real_sum]
  simp only [N.replicaKernel_pair, transitionSquare, Complex.re_sum,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

theorem trace_mul_hsNormSq_sq {I : Type*} [Fintype I]
    (R S : Matrix I I ℂ) :
    ‖Matrix.trace (R * S)‖ ^ 2 ≤ hsNormSq R * hsNormSq S := by
  classical
  have ht : ‖Matrix.trace (R * S)‖ ≤
      ∑ ij : I × I, ‖R ij.1 ij.2‖ * ‖S ij.2 ij.1‖ := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
    calc
      ‖∑ i, ∑ j, R i j * S j i‖ ≤ ∑ i, ‖∑ j, R i j * S j i‖ :=
        norm_sum_le _ _
      _ ≤ ∑ i, ∑ j, ‖R i j‖ * ‖S j i‖ := by
        apply Finset.sum_le_sum
        intro i _
        simpa only [norm_mul] using
          (norm_sum_le Finset.univ (fun j => R i j * S j i))
      _ = _ := by rw [Fintype.sum_prod_type]
  have hc := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (I × I))
    (fun ij => ‖R ij.1 ij.2‖) (fun ij => ‖S ij.2 ij.1‖)
  have ha : (∑ ij : I × I, ‖R ij.1 ij.2‖ ^ 2) = hsNormSq R := by
    simp only [Fintype.sum_prod_type, hsNormSq]
  have hb : (∑ ij : I × I, ‖S ij.2 ij.1‖ ^ 2) = hsNormSq S := by
    simp only [Fintype.sum_prod_type, hsNormSq]
    exact Finset.sum_comm
  rw [ha, hb] at hc
  have hp : 0 ≤ ∑ ij : I × I, ‖R ij.1 ij.2‖ * ‖S ij.2 ij.1‖ :=
    Finset.sum_nonneg (fun _ _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))
  nlinarith [norm_nonneg (Matrix.trace (R * S))]

def columnPurity (N : Stinespring Y B E) (U : Matrix.unitaryGroup Y ℂ) (i : Y) : ℝ :=
  purity (N.apply (pureDensity (unitaryColumn U i)))

theorem columnPurity_nonneg (N : Stinespring Y B E)
    (U : Matrix.unitaryGroup Y ℂ) (i : Y) : 0 ≤ columnPurity N U i := by
  exact transitionSquare_diagonal_nonneg N U i

theorem transitionSquare_norm_le_columnPurity (N : Stinespring Y B E)
    (U : Matrix.unitaryGroup Y ℂ) (i j : Y) :
    ‖transitionSquare N U i j‖ ≤
      Real.sqrt (columnPurity N U i) * Real.sqrt (columnPurity N U j) := by
  let Ai := N.amplitudes (unitaryColumn U i)
  let Aj := N.amplitudes (unitaryColumn U j)
  have hi : columnPurity N U i = hsNormSq (reducedLeft Ai) := by
    unfold columnPurity
    rw [N.apply_pureDensity]
    exact purity_eq_hsNormSq_of_hermitian _ (reducedLeft_conjTranspose Ai)
  have hj : columnPurity N U j = hsNormSq (reducedLeft Aj) := by
    unfold columnPurity
    rw [N.apply_pureDensity]
    exact purity_eq_hsNormSq_of_hermitian _ (reducedLeft_conjTranspose Aj)
  have he : transitionSquare N U i j =
      Matrix.trace (crossLeft Aj Ai * crossLeft Aj Ai) := by
    simp only [transitionSquare, N.apply_crossDensity, Ai, Aj]
  have hco := transition_norm_le_output_overlap Aj Ai
  have hle : ‖transitionSquare N U i j‖ ≤
      ‖Matrix.trace (reducedLeft Aj * reducedLeft Ai)‖ := by
    rw [he]
    exact hco.trans (Complex.re_le_norm _)
  have hcs := trace_mul_hsNormSq_sq (reducedLeft Aj) (reducedLeft Ai)
  rw [← hi, ← hj] at hcs
  have hp : (Real.sqrt (columnPurity N U i) * Real.sqrt (columnPurity N U j)) ^ 2 =
      columnPurity N U i * columnPurity N U j := by
    rw [mul_pow, Real.sq_sqrt (columnPurity_nonneg N U i),
      Real.sq_sqrt (columnPurity_nonneg N U j)]
  have hroot : 0 ≤ Real.sqrt (columnPurity N U i) * Real.sqrt (columnPurity N U j) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  nlinarith [norm_nonneg (transitionSquare N U i j),
    norm_nonneg (Matrix.trace (reducedLeft Aj * reducedLeft Ai))]

theorem sparse_sum_sq_le_six {I : Type*} [Fintype I] [DecidableEq I]
    (s x : I → ℝ) (hzero : ∀ i, s i = 0 → x i = 0)
    (hcard : (Finset.univ.filter (fun i => s i ≠ 0)).card ≤ 6) :
    (∑ i, x i) ^ 2 ≤ 6 * ∑ i, x i ^ 2 := by
  classical
  let T := Finset.univ.filter (fun i => s i ≠ 0)
  have hx : (∑ i ∈ T, x i) = ∑ i, x i := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro i _ hi
    have hz : s i = 0 := by simpa [T] using hi
    exact hzero i hz
  have hx2 : (∑ i ∈ T, x i ^ 2) = ∑ i, x i ^ 2 := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro i _ hi
    have hz : s i = 0 := by simpa [T] using hi
    rw [hzero i hz]
    simp
  have hc := Finset.sum_mul_sq_le_sq_mul_sq T (fun _ : I => (1 : ℝ)) x
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at hc
  rw [hx, hx2] at hc
  have hn : (T.card : ℝ) ≤ 6 := by exact_mod_cast hcard
  exact hc.trans (mul_le_mul_of_nonneg_right hn
    (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))

theorem retained_diagonal_trace_lower (N : Stinespring Y B E) (β : ℝ)
    (hbound : ∀ w : Y → ℂ, vectorNormSq w = 1 → purity (N.apply (pureDensity w)) ≤ β)
    (U : Matrix.unitaryGroup Y ℂ) (s : Y → ℝ) (hs : ∀ i, 0 ≤ s i) :
    (6 * (∑ i, (s i * Real.sqrt (columnPurity N U i)) ^ 2) -
      (∑ i, s i * Real.sqrt (columnPurity N U i)) ^ 2) / 5 -
      (2 * β / 5) * ((∑ i, s i) ^ 2 - ∑ i, s i ^ 2) ≤
      ∑ i, ∑ j, s i * s j * (transitionSquare N U i j).re := by
  classical
  let x : Y → ℝ := fun i => s i * Real.sqrt (columnPurity N U i)
  have hp (i j : Y) :
      (if i = j then x i ^ 2 else 0) -
        (2 * β / 5) * (if i = j then 0 else s i * s j) -
        (1 / 5 : ℝ) * (if i = j then 0 else x i * x j) ≤
      s i * s j * (transitionSquare N U i j).re := by
    by_cases hij : i = j
    · subst j
      simp only [ite_true, mul_zero, sub_zero]
      have hxi : x i ^ 2 = s i ^ 2 * columnPurity N U i := by
        dsimp [x]
        rw [mul_pow, Real.sq_sqrt (columnPurity_nonneg N U i)]
      rw [hxi]
      change s i ^ 2 * columnPurity N U i ≤ s i * s i * columnPurity N U i
      exact le_of_eq (by ring)
    · simp only [if_neg hij]
      have ha := transitionSquare_offdiagonal_lower N β hbound U i j hij
      have hb := transitionSquare_norm_le_columnPurity N U i j
      have hr : -(Real.sqrt (columnPurity N U i) * Real.sqrt (columnPurity N U j)) ≤
          (transitionSquare N U i j).re :=
        (neg_le_neg hb).trans (neg_le_of_abs_le (Complex.abs_re_le_norm _))
      have hmix : -(2 * β / 5) -
          (Real.sqrt (columnPurity N U i) * Real.sqrt (columnPurity N U j)) / 5 ≤
          (transitionSquare N U i j).re := by linarith
      have hw := mul_le_mul_of_nonneg_left hmix (mul_nonneg (hs i) (hs j))
      convert hw using 1 <;> dsimp [x] <;> ring
  have h := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
    Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hp i j))
  have hd : (∑ i : Y, ∑ j : Y, if i = j then x i ^ 2 else 0) = ∑ i, x i ^ 2 := by
    simp
  have hb : (∑ i : Y, ∑ j : Y,
      (2 * β / 5) * (if i = j then 0 else s i * s j)) =
      (2 * β / 5) * (∑ i, ∑ j, if i = j then 0 else s i * s j) := by
    simp only [← Finset.mul_sum]
  have hx : (∑ i : Y, ∑ j : Y,
      (1 / 5 : ℝ) * (if i = j then 0 else x i * x j)) =
      (1 / 5 : ℝ) * (∑ i, ∑ j, if i = j then 0 else x i * x j) := by
    simp only [← Finset.mul_sum]
  simp only [Finset.sum_sub_distrib] at h
  rw [hd, hb, hx, offdiagonal_weight_sum s, offdiagonal_weight_sum x] at h
  dsimp [x] at h
  nlinarith

theorem rank_six_weighted_trace_exterior_lower
    (N : Stinespring Y B E) (β : ℝ)
    (hbound : ∀ w : Y → ℂ, vectorNormSq w = 1 → purity (N.apply (pureDensity w)) ≤ β)
    (U : Matrix.unitaryGroup Y ℂ) (s : Y → ℝ) (hs : ∀ i, 0 ≤ s i)
    (hcard : (Finset.univ.filter (fun i => s i ≠ 0)).card ≤ 6) :
    -(2 * β / 5) * ((∑ i, s i) ^ 2 - ∑ i, s i ^ 2) ≤
      ∑ i, ∑ j, s i * s j * (transitionSquare N U i j).re := by
  have h := retained_diagonal_trace_lower N β hbound U s hs
  have hx := sparse_sum_sq_le_six s (fun i => s i * Real.sqrt (columnPurity N U i))
    (fun i hi => by simp [hi]) hcard
  linarith

theorem rank_six_weighted_trace_hs_lower [Nonempty Y]
    (N : Stinespring Y B E) (β : ℝ)
    (hbound : ∀ w : Y → ℂ, vectorNormSq w = 1 → purity (N.apply (pureDensity w)) ≤ β)
    (U : Matrix.unitaryGroup Y ℂ) (s : Y → ℝ) (hs : ∀ i, 0 ≤ s i)
    (hcard : (Finset.univ.filter (fun i => s i ≠ 0)).card ≤ 6) :
    -2 * β * (∑ i, s i ^ 2) ≤
      ∑ i, ∑ j, s i * s j * (transitionSquare N U i j).re := by
  classical
  have h := retained_diagonal_trace_lower N β hbound U s hs
  have hx := sparse_sum_sq_le_six s (fun i => s i * Real.sqrt (columnPurity N U i))
    (fun i hi => by simp [hi]) hcard
  have hss := sparse_sum_sq_le_six s s (fun _ hi => hi) hcard
  let i : Y := Classical.arbitrary Y
  have hβ : 0 ≤ β := (columnPurity_nonneg N U i).trans
    (hbound (unitaryColumn U i) (unitaryColumn_normSq U i))
  have hmul := mul_le_mul_of_nonneg_left hss hβ
  nlinarith

end QuantumProver.WernerEndpoint.TakagiContraction

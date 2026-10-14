import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 1200000

noncomputable section

open scoped BigOperators ComplexConjugate ComplexOrder Matrix.Norms.L2Operator InnerProductSpace
open WithLp

namespace QuantumProver.PositiveKernelOperator

abbrev FiniteCoefficients := ℕ →₀ ℂ

def principalBlock (F : ℕ → ℕ → ℂ) (n : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => F i.val j.val

def FinitePositive (F : ℕ → ℕ → ℂ) : Prop :=
  ∀ n, (principalBlock F n).PosSemidef

def diagonalMass (F : ℕ → ℕ → ℂ) : ℝ := ∑' i, (F i i).re

theorem diagonal_nonneg (F : ℕ → ℕ → ℂ) (hF : FinitePositive F) (i : ℕ) :
    0 ≤ (F i i).re := by
  have h := (hF (i + 1)).diag_nonneg (i := ⟨i, Nat.lt_succ_self i⟩)
  exact (Complex.nonneg_iff.mp h).1

theorem hermitian_entry (F : ℕ → ℕ → ℂ) (hF : FinitePositive F) (i j : ℕ) :
    star (F j i) = F i j := by
  let n := max i j + 1
  let ii : Fin n := ⟨i, Nat.lt_succ_of_le (Nat.le_max_left i j)⟩
  let jj : Fin n := ⟨j, Nat.lt_succ_of_le (Nat.le_max_right i j)⟩
  exact congrFun (congrFun (hF n).isHermitian.eq ii) jj

theorem diagonalMass_nonneg (F : ℕ → ℕ → ℂ) (hF : FinitePositive F) :
    0 ≤ diagonalMass F := tsum_nonneg (diagonal_nonneg F hF)

theorem finite_positive_norm_le_trace {α : Type*} [Fintype α] [DecidableEq α]
    (R : Matrix α α ℂ) (hR : R.PosSemidef) : ‖R‖ ≤ R.trace.re := by
  have hnorm : ‖R‖ = ‖fun i => (hR.isHermitian.eigenvalues i : ℂ)‖ := by
    conv_lhs => rw [hR.isHermitian.spectral_theorem, Unitary.conjStarAlgAut_apply]
    simp only [← Unitary.coe_star, CStarRing.norm_mul_coe_unitary,
      CStarRing.norm_coe_unitary_mul, Matrix.l2_opNorm_diagonal]
    rfl
  have ht : R.trace.re = ∑ i, hR.isHermitian.eigenvalues i := by
    rw [hR.isHermitian.trace_eq_sum_eigenvalues]
    simp
  rw [hnorm, ht]
  apply (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg
    (fun i _ => hR.eigenvalues_nonneg i))).mpr
  intro i
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hR.eigenvalues_nonneg i)]
  exact Finset.single_le_sum (fun k _ => hR.eigenvalues_nonneg k) (Finset.mem_univ i)

theorem principalBlock_norm_le_mass (F : ℕ → ℕ → ℂ) (hF : FinitePositive F)
    (hdiag : Summable (fun i => (F i i).re)) (n : ℕ) :
    ‖principalBlock F n‖ ≤ diagonalMass F := by
  refine (finite_positive_norm_le_trace _ (hF n)).trans ?_
  change (∑ i : Fin n, F i.val i.val).re ≤ diagonalMass F
  rw [Complex.re_sum, ← Finset.sum_range (fun i : ℕ => (F i i).re)]
  exact hdiag.sum_le_tsum (Finset.range n) (fun i _ => diagonal_nonneg F hF i)

def finiteForm (F : ℕ → ℕ → ℂ) :
    FiniteCoefficients →ₗ⋆[ℂ] FiniteCoefficients →ₗ[ℂ] ℂ :=
  Finsupp.lsum ℂ fun i =>
    (LinearMap.id.smulRight (Finsupp.linearCombination ℂ (F i))).comp
      (starLinearEquiv ℂ).toLinearMap

theorem finiteForm_apply (F : ℕ → ℕ → ℂ) (x y : FiniteCoefficients) :
    finiteForm F x y = x.sum (fun i a => y.sum (fun j c => star a * F i j * c)) := by
  simp [finiteForm, Finsupp.lsum_apply, Finsupp.linearCombination_apply,
    Finsupp.sum, Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]

theorem finiteForm_single (F : ℕ → ℕ → ℂ) (i j : ℕ) :
    finiteForm F (Finsupp.single i 1) (Finsupp.single j 1) = F i j := by
  simp [finiteForm_apply]

def finiteCoordinates (x : FiniteCoefficients) (n : ℕ) : EuclideanSpace ℂ (Fin n) :=
  toLp 2 (fun i : Fin n => x i.val)

theorem finiteForm_eq_matrix (F : ℕ → ℕ → ℂ) (x y : FiniteCoefficients) (n : ℕ)
    (hx : x.support ⊆ Finset.range n) (hy : y.support ⊆ Finset.range n) :
    finiteForm F x y = inner ℂ (finiteCoordinates x n)
      (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) (principalBlock F n) (finiteCoordinates y n)) := by
  rw [finiteForm_apply, Finsupp.sum_of_support_subset x hx _ (by simp)]
  calc
    _ = ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, star (x i) * F i j * y j := by
      apply Finset.sum_congr rfl
      intro i hi
      exact Finsupp.sum_of_support_subset y hy _ (by simp)
    _ = _ := by
      simp only [finiteCoordinates, Matrix.toEuclideanCLM_toLp, PiLp.inner_apply, PiLp.toLp_apply,
        RCLike.inner_apply', Matrix.mulVec, dotProduct, principalBlock,
        Finset.mul_sum, mul_assoc]
      change (∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, star (x i) * (F i j * y j)) =
        ∑ i : Fin n, ∑ j : Fin n, star (x i.val) * (F i.val j.val * y j.val)
      rw [← Finset.sum_range (fun i : ℕ => ∑ j : Fin n, star (x i) * (F i j.val * y j.val))]
      apply Finset.sum_congr rfl
      intro i hi
      exact Finset.sum_range (fun j : ℕ => star (x i) * (F i j * y j))

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

def basisEmbedding (b : HilbertBasis ℕ ℂ E) : FiniteCoefficients →ₗ[ℂ] E :=
  Finsupp.linearCombination ℂ b

@[simp] theorem basisEmbedding_single (b : HilbertBasis ℕ ℂ E) (i : ℕ) :
    basisEmbedding b (Finsupp.single i 1) = b i := by simp [basisEmbedding]

theorem basisEmbedding_dense (b : HilbertBasis ℕ ℂ E) : DenseRange (basisEmbedding b) := by
  change Dense (Set.range (basisEmbedding b))
  rw [← LinearMap.coe_range, basisEmbedding, Finsupp.range_linearCombination]
  exact Submodule.dense_iff_topologicalClosure_eq_top.mpr b.dense_span

theorem finiteCoordinates_norm (b : HilbertBasis ℕ ℂ E) (x : FiniteCoefficients) (n : ℕ)
    (hx : x.support ⊆ Finset.range n) :
    ‖finiteCoordinates x n‖ = ‖basisEmbedding b x‖ := by
  have hi : inner ℂ (basisEmbedding b x) (basisEmbedding b x) =
      inner ℂ (finiteCoordinates x n) (finiteCoordinates x n) := by
    rw [basisEmbedding, b.orthonormal.inner_finsupp_eq_sum_left]
    rw [Finsupp.sum_of_support_subset x hx _ (by simp)]
    simp only [finiteCoordinates, PiLp.inner_apply, PiLp.toLp_apply, RCLike.inner_apply']
    exact Finset.sum_range (fun i : ℕ => star (x i) * x i)
  have hs : ‖basisEmbedding b x‖ ^ 2 = ‖finiteCoordinates x n‖ ^ 2 := by
    rw [@norm_sq_eq_re_inner ℂ E, @norm_sq_eq_re_inner ℂ (EuclideanSpace ℂ (Fin n)), hi]
  nlinarith [norm_nonneg (finiteCoordinates x n), norm_nonneg (basisEmbedding b x)]

theorem finiteForm_bound (b : HilbertBasis ℕ ℂ E) (F : ℕ → ℕ → ℂ)
    (hF : FinitePositive F) (hdiag : Summable (fun i => (F i i).re))
    (x y : FiniteCoefficients) :
    ‖finiteForm F x y‖ ≤ diagonalMass F * ‖basisEmbedding b x‖ * ‖basisEmbedding b y‖ := by
  let n := (x.support ∪ y.support).sup id + 1
  have hx : x.support ⊆ Finset.range n := by
    intro i hi
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le
      (Finset.le_sup (f := id) (Finset.mem_union_left y.support hi)))
  have hy : y.support ⊆ Finset.range n := by
    intro i hi
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le
      (Finset.le_sup (f := id) (Finset.mem_union_right x.support hi)))
  rw [finiteForm_eq_matrix F x y n hx hy]
  calc
    _ ≤ ‖finiteCoordinates x n‖ *
      ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) (principalBlock F n) (finiteCoordinates y n)‖ :=
        norm_inner_le_norm _ _
    _ ≤ ‖finiteCoordinates x n‖ * (‖principalBlock F n‖ * ‖finiteCoordinates y n‖) := by
        exact mul_le_mul_of_nonneg_left
          ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) _).le_opNorm _) (norm_nonneg _)
    _ ≤ diagonalMass F * ‖basisEmbedding b x‖ * ‖basisEmbedding b y‖ := by
      rw [finiteCoordinates_norm b x n hx, finiteCoordinates_norm b y n hy]
      calc
        _ = (‖principalBlock F n‖ * ‖basisEmbedding b x‖) * ‖basisEmbedding b y‖ := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (principalBlock_norm_le_mass F hF hdiag n) (norm_nonneg _))
          (norm_nonneg _)

theorem finiteForm_nonneg (F : ℕ → ℕ → ℂ) (hF : FinitePositive F)
    (x : FiniteCoefficients) : 0 ≤ finiteForm F x x := by
  let n := x.support.sup id + 1
  have hx : x.support ⊆ Finset.range n := by
    intro i hi
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup (f := id) hi))
  rw [finiteForm_eq_matrix F x x n hx hx]
  simpa [finiteCoordinates, Matrix.toEuclideanCLM_toLp, PiLp.inner_apply, PiLp.toLp_apply,
    RCLike.inner_apply', dotProduct, mul_comm] using
      (hF n).dotProduct_mulVec_nonneg (fun i : Fin n => x i.val)

def rowFunctional (b : HilbertBasis ℕ ℂ E) (F : ℕ → ℕ → ℂ)
    (x : FiniteCoefficients) : E →L[ℂ] ℂ :=
  (finiteForm F x).extendOfNorm (basisEmbedding b)

theorem rowFunctional_apply_embedding (b : HilbertBasis ℕ ℂ E) (F : ℕ → ℕ → ℂ)
    (hF : FinitePositive F) (hdiag : Summable (fun i => (F i i).re))
    (x y : FiniteCoefficients) :
    rowFunctional b F x (basisEmbedding b y) = finiteForm F x y :=
  LinearMap.extendOfNorm_eq (basisEmbedding_dense b)
    ⟨diagonalMass F * ‖basisEmbedding b x‖, finiteForm_bound b F hF hdiag x⟩ y

theorem norm_rowFunctional_le (b : HilbertBasis ℕ ℂ E) (F : ℕ → ℕ → ℂ)
    (hF : FinitePositive F) (hdiag : Summable (fun i => (F i i).re))
    (x : FiniteCoefficients) :
    ‖rowFunctional b F x‖ ≤ diagonalMass F * ‖basisEmbedding b x‖ :=
  LinearMap.opNorm_extendOfNorm_le (basisEmbedding_dense b)
    (mul_nonneg (diagonalMass_nonneg F hF) (norm_nonneg _)) (finiteForm_bound b F hF hdiag x)

def denseForm (b : HilbertBasis ℕ ℂ E) (F : ℕ → ℕ → ℂ)
    (hF : FinitePositive F) (hdiag : Summable (fun i => (F i i).re)) :
    FiniteCoefficients →ₗ⋆[ℂ] E →L[ℂ] ℂ where
  toFun := rowFunctional b F
  map_add' x y := by
    change rowFunctional b F (x + y) = rowFunctional b F x + rowFunctional b F y
    apply DFunLike.coe_injective
    apply (basisEmbedding_dense b).equalizer (by fun_prop) (by fun_prop)
    funext w
    simp [Function.comp_def, rowFunctional_apply_embedding b F hF hdiag, map_add]
  map_smul' c x := by
    change rowFunctional b F (c • x) = star c • rowFunctional b F x
    apply DFunLike.coe_injective
    apply (basisEmbedding_dense b).equalizer (by fun_prop) (by fun_prop)
    funext w
    simp [Function.comp_def, rowFunctional_apply_embedding b F hF hdiag, map_smulₛₗ]

@[simp] theorem denseForm_apply (b : HilbertBasis ℕ ℂ E) (F : ℕ → ℕ → ℂ)
    (hF : FinitePositive F) (hdiag : Summable (fun i => (F i i).re)) (x : FiniteCoefficients) :
    denseForm b F hF hdiag x = rowFunctional b F x := rfl

def boundedForm (b : HilbertBasis ℕ ℂ E) (F : ℕ → ℕ → ℂ)
    (hF : FinitePositive F) (hdiag : Summable (fun i => (F i i).re)) :
    E →L⋆[ℂ] E →L[ℂ] ℂ :=
  (denseForm b F hF hdiag).extendOfNorm (basisEmbedding b)

theorem boundedForm_apply_embedding (b : HilbertBasis ℕ ℂ E) (F : ℕ → ℕ → ℂ)
    (hF : FinitePositive F) (hdiag : Summable (fun i => (F i i).re))
    (x : FiniteCoefficients) :
    boundedForm b F hF hdiag (basisEmbedding b x) = rowFunctional b F x :=
  LinearMap.extendOfNorm_eq (basisEmbedding_dense b)
    ⟨diagonalMass F, norm_rowFunctional_le b F hF hdiag⟩ x

theorem boundedForm_embedding_embedding (b : HilbertBasis ℕ ℂ E) (F : ℕ → ℕ → ℂ)
    (hF : FinitePositive F) (hdiag : Summable (fun i => (F i i).re))
    (x y : FiniteCoefficients) :
    boundedForm b F hF hdiag (basisEmbedding b x) (basisEmbedding b y) = finiteForm F x y := by
  rw [boundedForm_apply_embedding, rowFunctional_apply_embedding b F hF hdiag]

theorem norm_boundedForm_apply_le (b : HilbertBasis ℕ ℂ E) (F : ℕ → ℕ → ℂ)
    (hF : FinitePositive F) (hdiag : Summable (fun i => (F i i).re)) (x : E) :
    ‖boundedForm b F hF hdiag x‖ ≤ diagonalMass F * ‖x‖ :=
  LinearMap.norm_extendOfNorm_apply_le (basisEmbedding_dense b) (diagonalMass F)
    (norm_rowFunctional_le b F hF hdiag) x

def operator (b : HilbertBasis ℕ ℂ E) (F : ℕ → ℕ → ℂ)
    (hF : FinitePositive F) (hdiag : Summable (fun i => (F i i).re)) : E →L[ℂ] E :=
  InnerProductSpace.continuousLinearMapOfBilin (boundedForm b F hF hdiag)

theorem inner_operator (b : HilbertBasis ℕ ℂ E) (F : ℕ → ℕ → ℂ)
    (hF : FinitePositive F) (hdiag : Summable (fun i => (F i i).re)) (x y : E) :
    inner ℂ (operator b F hF hdiag x) y = boundedForm b F hF hdiag x y :=
  InnerProductSpace.continuousLinearMapOfBilin_apply _ x y

theorem inner_operator_embedding (b : HilbertBasis ℕ ℂ E) (F : ℕ → ℕ → ℂ)
    (hF : FinitePositive F) (hdiag : Summable (fun i => (F i i).re))
    (x y : FiniteCoefficients) :
    inner ℂ (operator b F hF hdiag (basisEmbedding b x)) (basisEmbedding b y) = finiteForm F x y := by
  rw [inner_operator, boundedForm_embedding_embedding]

theorem operator_coefficient (b : HilbertBasis ℕ ℂ E) (F : ℕ → ℕ → ℂ)
    (hF : FinitePositive F) (hdiag : Summable (fun i => (F i i).re)) (i j : ℕ) :
    inner ℂ (b i) (operator b F hF hdiag (b j)) = F i j := by
  rw [← inner_conj_symm, ← basisEmbedding_single b i, ← basisEmbedding_single b j,
    inner_operator_embedding, finiteForm_single]
  exact hermitian_entry F hF i j

theorem norm_operator_apply_le (b : HilbertBasis ℕ ℂ E) (F : ℕ → ℕ → ℂ)
    (hF : FinitePositive F) (hdiag : Summable (fun i => (F i i).re)) (x : E) :
    ‖operator b F hF hdiag x‖ ≤ diagonalMass F * ‖x‖ := by
  have hn : ‖operator b F hF hdiag x‖ = ‖boundedForm b F hF hdiag x‖ :=
    (InnerProductSpace.toDual ℂ E).symm.norm_map _
  rw [hn]
  exact norm_boundedForm_apply_le b F hF hdiag x

theorem norm_operator_le (b : HilbertBasis ℕ ℂ E) (F : ℕ → ℕ → ℂ)
    (hF : FinitePositive F) (hdiag : Summable (fun i => (F i i).re)) :
    ‖operator b F hF hdiag‖ ≤ diagonalMass F :=
  (operator b F hF hdiag).opNorm_le_bound (diagonalMass_nonneg F hF)
    (norm_operator_apply_le b F hF hdiag)

theorem operator_isPositive (b : HilbertBasis ℕ ℂ E) (F : ℕ → ℕ → ℂ)
    (hF : FinitePositive F) (hdiag : Summable (fun i => (F i i).re)) :
    (operator b F hF hdiag).IsPositive := by
  rw [ContinuousLinearMap.isPositive_iff_complex]
  let q : E → ℂ := fun x => inner ℂ (operator b F hF hdiag x) x
  have hq : Continuous q := by fun_prop
  have hr : Continuous (fun x => (q x).re) := Complex.continuous_re.comp hq
  have hclosed : IsClosed {x : E | ((q x).re : ℂ) = q x ∧ 0 ≤ (q x).re} :=
    (isClosed_eq (Complex.continuous_ofReal.comp hr) hq).inter (isClosed_le continuous_const hr)
  change ∀ x : E, ((q x).re : ℂ) = q x ∧ 0 ≤ (q x).re
  intro z
  refine (basisEmbedding_dense b).induction_on z hclosed ?_
  intro x
  dsimp only [q]
  rw [inner_operator_embedding]
  have hp := Complex.nonneg_iff.mp (finiteForm_nonneg F hF x)
  exact ⟨by apply Complex.ext <;> simp [hp.2], hp.1⟩

theorem operator_coefficient_left (b : HilbertBasis ℕ ℂ E) (F : ℕ → ℕ → ℂ)
    (hF : FinitePositive F) (hdiag : Summable (fun i => (F i i).re)) (i j : ℕ) :
    inner ℂ (operator b F hF hdiag (b i)) (b j) = F i j := by
  rw [(operator_isPositive b F hF hdiag).inner_left_eq_inner_right, operator_coefficient]

theorem operator_diagonal_summable (b : HilbertBasis ℕ ℂ E) (F : ℕ → ℕ → ℂ)
    (hF : FinitePositive F) (hdiag : Summable (fun i => (F i i).re)) :
    Summable (fun i => (inner ℂ (b i) (operator b F hF hdiag (b i))).re) := by
  simpa only [operator_coefficient] using hdiag

theorem operator_diagonal_summable_left (b : HilbertBasis ℕ ℂ E) (F : ℕ → ℕ → ℂ)
    (hF : FinitePositive F) (hdiag : Summable (fun i => (F i i).re)) :
    Summable (fun i => (inner ℂ (operator b F hF hdiag (b i)) (b i)).re) := by
  simpa only [operator_coefficient_left] using hdiag

theorem operator_diagonalMass (b : HilbertBasis ℕ ℂ E) (F : ℕ → ℕ → ℂ)
    (hF : FinitePositive F) (hdiag : Summable (fun i => (F i i).re)) :
    (∑' i, (inner ℂ (operator b F hF hdiag (b i)) (b i)).re) = diagonalMass F := by
  simp only [operator_coefficient_left, diagonalMass]

theorem coefficient_ext (b : HilbertBasis ℕ ℂ E) {D S : E →L[ℂ] E}
    (h : ∀ i j, inner ℂ (b i) (D (b j)) = inner ℂ (b i) (S (b j))) : D = S := by
  have hj : ∀ j, D (b j) = S (b j) := by
    intro j
    apply b.repr.injective
    ext i
    simpa only [HilbertBasis.repr_apply_apply] using h i j
  ext x
  refine (basisEmbedding_dense b).induction_on x ?_ ?_
  · exact isClosed_eq D.continuous S.continuous
  · intro y
    simp [basisEmbedding, Finsupp.linearCombination_apply, Finsupp.sum, hj]

theorem operator_unique (b : HilbertBasis ℕ ℂ E) (F : ℕ → ℕ → ℂ)
    (hF : FinitePositive F) (hdiag : Summable (fun i => (F i i).re))
    (D : E →L[ℂ] E) (hD : ∀ i j, inner ℂ (b i) (D (b j)) = F i j) :
    D = operator b F hF hdiag := by
  apply coefficient_ext b
  intro i j
  rw [hD, operator_coefficient]

theorem exists_positive_operator (b : HilbertBasis ℕ ℂ E) (F : ℕ → ℕ → ℂ)
    (hF : FinitePositive F) (hdiag : Summable (fun i => (F i i).re)) :
    ∃ D : E →L[ℂ] E, D.IsPositive ∧ (∀ i j, inner ℂ (b i) (D (b j)) = F i j) ∧
      ‖D‖ ≤ ∑' i, (F i i).re :=
  ⟨operator b F hF hdiag, operator_isPositive b F hF hdiag,
    operator_coefficient b F hF hdiag, norm_operator_le b F hF hdiag⟩

end QuantumProver.PositiveKernelOperator

import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.Adjoint

set_option autoImplicit false

noncomputable section

open Filter
open scoped BigOperators Topology InnerProductSpace ComplexOrder MatrixOrder

namespace QuantumProver.HilbertFiniteCompression

variable {𝕜 E F ι I : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

def finiteProjection (b : HilbertBasis ι 𝕜 E) (s : Finset ι) : E →L[𝕜] E :=
  ∑ i ∈ s, InnerProductSpace.rankOne 𝕜 (b i) (b i)

theorem finiteProjection_apply (b : HilbertBasis ι 𝕜 E) (s : Finset ι) (x : E) :
    finiteProjection b s x = ∑ i ∈ s, inner 𝕜 (b i) x • b i := by
  simp only [finiteProjection, sum_apply, InnerProductSpace.rankOne_apply]

theorem finiteProjection_inner (b : HilbertBasis ι 𝕜 E) (s : Finset ι) (x y : E) :
    inner 𝕜 (finiteProjection b s x) y = inner 𝕜 x (finiteProjection b s y) := by
  simp only [finiteProjection_apply, sum_inner, inner_sum, inner_smul_left,
    inner_smul_right, inner_conj_symm]
  apply Finset.sum_congr rfl
  intro i hi
  exact mul_comm _ _

theorem finiteProjection_idempotent (b : HilbertBasis ι 𝕜 E) (s : Finset ι) (x : E) :
    finiteProjection b s (finiteProjection b s x) = finiteProjection b s x := by
  rw [finiteProjection_apply, finiteProjection_apply]
  apply Finset.sum_congr rfl
  intro i hi
  rw [b.orthonormal.inner_right_sum _ hi]

theorem finiteProjection_isSymmetricProjection
    (b : HilbertBasis ι 𝕜 E) (s : Finset ι) :
    (finiteProjection b s).toLinearMap.IsSymmetricProjection := by
  refine ⟨?_, finiteProjection_inner b s⟩
  apply LinearMap.ext
  intro x
  exact finiteProjection_idempotent b s x

theorem finiteProjection_isStarProjection [CompleteSpace E]
    (b : HilbertBasis ι 𝕜 E) (s : Finset ι) :
    IsStarProjection (finiteProjection b s) :=
  ContinuousLinearMap.isStarProjection_iff_isSymmetricProjection.mpr
    (finiteProjection_isSymmetricProjection b s)

theorem finiteProjection_mem_span (b : HilbertBasis ι 𝕜 E) (s : Finset ι) (x : E) :
    finiteProjection b s x ∈ Submodule.span 𝕜 (b '' (s : Set ι)) := by
  rw [finiteProjection_apply]
  apply Submodule.sum_mem
  intro i hi
  apply Submodule.smul_mem
  exact Submodule.subset_span ⟨i, hi, rfl⟩

theorem norm_finiteProjection_apply_le (b : HilbertBasis ι 𝕜 E) (s : Finset ι) (x : E) :
    ‖finiteProjection b s x‖ ≤ ‖x‖ := by
  have hinner : inner 𝕜 (finiteProjection b s x) (finiteProjection b s x) =
      inner 𝕜 (finiteProjection b s x) x := by
    rw [← finiteProjection_inner, finiteProjection_idempotent]
  have hsq : ‖finiteProjection b s x‖ ^ 2 ≤ ‖finiteProjection b s x‖ * ‖x‖ := by
    rw [@InnerProductSpace.norm_sq_eq_re_inner 𝕜 E, hinner]
    exact (RCLike.re_le_norm _).trans (norm_inner_le_norm _ _)
  nlinarith [norm_nonneg (finiteProjection b s x), norm_nonneg x]

theorem norm_finiteProjection_le_one (b : HilbertBasis ι 𝕜 E) (s : Finset ι) :
    ‖finiteProjection b s‖ ≤ 1 :=
  (finiteProjection b s).opNorm_le_bound (by norm_num)
    (by intro x; simpa using norm_finiteProjection_apply_le b s x)

theorem tendsto_finiteProjection_apply (b : HilbertBasis ι 𝕜 E) (x : E) :
    Tendsto (fun s : Finset ι => finiteProjection b s x) atTop (𝓝 x) := by
  simpa only [HasSum, SummationFilter.unconditional_filter, finiteProjection_apply,
    b.repr_apply_apply] using b.hasSum_repr x

theorem tendsto_initialProjection_apply (b : HilbertBasis ℕ 𝕜 E) (x : E) :
    Tendsto (fun n : ℕ => finiteProjection b (Finset.range n) x) atTop (𝓝 x) := by
  simpa only [finiteProjection_apply, b.repr_apply_apply] using
    (b.hasSum_repr x).tendsto_sum_nat

variable [Fintype I]

theorem opNorm_le_sum_columns (e : OrthonormalBasis I 𝕜 F) (K : F →L[𝕜] E) :
    ‖K‖ ≤ ∑ i, ‖K (e i)‖ := by
  apply K.opNorm_le_bound (Finset.sum_nonneg (fun i _ => norm_nonneg _))
  intro x
  have hKx : K x = ∑ i, inner 𝕜 (e i) x • K (e i) := by
    simpa only [map_sum, map_smul] using (congrArg K (e.sum_repr' x)).symm
  rw [hKx]
  calc
    ‖∑ i, inner 𝕜 (e i) x • K (e i)‖ ≤ ∑ i, ‖inner 𝕜 (e i) x • K (e i)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i, ‖K (e i)‖ * ‖x‖ := by
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_smul, mul_comm]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      simpa only [e.norm_eq_one, one_mul] using norm_inner_le_norm (e i) x
    _ = (∑ i, ‖K (e i)‖) * ‖x‖ := (Finset.sum_mul _ _ _).symm

theorem tendsto_finiteProjection_comp (b : HilbertBasis ι 𝕜 E)
    (e : OrthonormalBasis I 𝕜 F) (K : F →L[𝕜] E) :
    Tendsto (fun s : Finset ι => finiteProjection b s ∘L K) atTop (𝓝 K) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hcol (i : I) : Tendsto
      (fun s : Finset ι => ‖(finiteProjection b s ∘L K - K) (e i)‖) atTop (𝓝 0) := by
    simpa using ((tendsto_finiteProjection_apply b (K (e i))).sub_const (K (e i))).norm
  have hsum : Tendsto
      (fun s : Finset ι => ∑ i, ‖(finiteProjection b s ∘L K - K) (e i)‖) atTop (𝓝 0) := by
    simpa using tendsto_finsetSum Finset.univ (fun i _ => hcol i)
  exact squeeze_zero (fun s => norm_nonneg _)
    (fun s => opNorm_le_sum_columns e _) hsum

theorem gram_posSemidef (v : I → E) : (Matrix.gram 𝕜 v).PosSemidef :=
  Matrix.posSemidef_gram 𝕜 v

omit [Fintype I] in
theorem tendsto_projectedGram (b : HilbertBasis ι 𝕜 E) (v : I → E) :
    Tendsto (fun s : Finset ι => Matrix.gram 𝕜 (fun i => finiteProjection b s (v i)))
      atTop (𝓝 (Matrix.gram 𝕜 v)) := by
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  exact (tendsto_finiteProjection_apply b (v i)).inner
    (tendsto_finiteProjection_apply b (v j))

end QuantumProver.HilbertFiniteCompression

import QuantumProver.LinearAlgebra.NuclearOperator
import QuantumProver.LinearAlgebra.HilbertNuclearTrace
import QuantumProver.LinearAlgebra.HilbertFiniteCompression
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.Normed.Group.Tannery

set_option autoImplicit false
set_option maxHeartbeats 1200000

noncomputable section

open Filter
open scoped BigOperators Topology lp Classical ENNReal InnerProductSpace

namespace QuantumProver.HilbertNuclearCompression

open NuclearOperator HilbertFiniteCompression

variable {𝕜 E ι : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

section Composition

variable {F G H : Type*}
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  [NormedAddCommGroup H] [NormedSpace 𝕜 H] [CompleteSpace H]

def operatorComposition (L : F →L[𝕜] H) (R : G →L[𝕜] E) :
    (E →L[𝕜] F) →L[𝕜] (G →L[𝕜] H) :=
  (ContinuousLinearMap.compL 𝕜 G F H L) ∘L (ContinuousLinearMap.compL 𝕜 G E F).flip R

@[simp] theorem operatorComposition_apply (L : F →L[𝕜] H) (R : G →L[𝕜] E) (T : E →L[𝕜] F) :
    operatorComposition L R T = L ∘L T ∘L R := rfl

def compositionAtom (L : F →L[𝕜] H) (R : G →L[𝕜] E) (a : Atom 𝕜 E F) : Nuclear 𝕜 G H :=
  rankOne (a.1.1 ∘L R) (L a.2.1)

@[simp] theorem toOperator_compositionAtom (L : F →L[𝕜] H) (R : G →L[𝕜] E) (a : Atom 𝕜 E F) :
    toOperator (compositionAtom L R a) = operatorComposition L R (atomOperator a) := by
  rw [compositionAtom, toOperator_rankOne]
  ext x
  simp [operatorComposition, atomOperator]

theorem norm_compositionAtom_le (L : F →L[𝕜] H) (R : G →L[𝕜] E) (a : Atom 𝕜 E F) :
    ‖compositionAtom L R a‖ ≤ ‖L‖ * ‖R‖ := by
  have hφ : ‖a.1.1 ∘L R‖ ≤ ‖R‖ :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans (by
      simpa using mul_le_mul_of_nonneg_right a.1.2 (norm_nonneg R))
  have hy : ‖L a.2.1‖ ≤ ‖L‖ :=
    (L.le_opNorm _).trans (by simpa using mul_le_mul_of_nonneg_left a.2.2 (norm_nonneg L))
  rw [compositionAtom, norm_rankOne]
  exact (mul_le_mul hφ hy (norm_nonneg _) (norm_nonneg R)).trans_eq (mul_comm _ _)

def compositionTerms (L : F →L[𝕜] H) (R : G →L[𝕜] E) :
    Coefficients 𝕜 E F →L[𝕜] ℓ¹(Atom 𝕜 E F, Nuclear 𝕜 G H) :=
  lp.mapCLM 1 (fun a => ContinuousLinearMap.toSpanSingleton 𝕜 (compositionAtom L R a))
    (mul_nonneg (norm_nonneg L) (norm_nonneg R))
    (fun a => by simpa using norm_compositionAtom_le L R a)

theorem norm_compositionTerms_le (L : F →L[𝕜] H) (R : G →L[𝕜] E) :
    ‖compositionTerms L R‖ ≤ ‖L‖ * ‖R‖ :=
  lp.norm_mapCLM_le 1
    (fun a => ContinuousLinearMap.toSpanSingleton 𝕜 (compositionAtom L R a))
    (mul_nonneg (norm_nonneg L) (norm_nonneg R))
    (fun a => by simpa using norm_compositionAtom_le L R a)

def compositionCoefficients (L : F →L[𝕜] H) (R : G →L[𝕜] E) :
    Coefficients 𝕜 E F →L[𝕜] Nuclear 𝕜 G H :=
  lp.tsumCLM 𝕜 (Atom 𝕜 E F) (Nuclear 𝕜 G H) ∘L compositionTerms L R

@[simp] theorem compositionCoefficients_apply (L : F →L[𝕜] H) (R : G →L[𝕜] E)
    (c : Coefficients 𝕜 E F) :
    compositionCoefficients L R c = ∑' a, c a • compositionAtom L R a := by
  simp [compositionCoefficients, compositionTerms]

theorem norm_compositionCoefficients_le (L : F →L[𝕜] H) (R : G →L[𝕜] E) :
    ‖compositionCoefficients L R‖ ≤ ‖L‖ * ‖R‖ := by
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
  calc
    ‖lp.tsumCLM 𝕜 (Atom 𝕜 E F) (Nuclear 𝕜 G H)‖ * ‖compositionTerms L R‖
        ≤ 1 * (‖L‖ * ‖R‖) := mul_le_mul lp.norm_tsumCLM_le
          (norm_compositionTerms_le L R) (norm_nonneg (compositionTerms L R)) zero_le_one
    _ = ‖L‖ * ‖R‖ := one_mul _

theorem compositionCoefficients_single (L : F →L[𝕜] H) (R : G →L[𝕜] E)
    (a : Atom 𝕜 E F) (c : 𝕜) :
    compositionCoefficients L R (lp.single 1 a c : Coefficients 𝕜 E F) =
      c • compositionAtom L R a := by
  rw [compositionCoefficients_apply, tsum_eq_single a]
  · simp
  · intro a' hne
    simp [lp.single_apply, Pi.single_eq_of_ne hne]

theorem hasSum_compositionCoefficients (L : F →L[𝕜] H) (R : G →L[𝕜] E)
    (c : Coefficients 𝕜 E F) :
    HasSum (fun a => c a • compositionAtom L R a) (compositionCoefficients L R c) := by
  simpa only [compositionCoefficients_single] using
    (lp.hasSum_single (by simp : (1 : ℝ≥0∞) ≠ ⊤) c).mapL (compositionCoefficients L R)

theorem toOperator_compositionCoefficients (L : F →L[𝕜] H) (R : G →L[𝕜] E)
    (c : Coefficients 𝕜 E F) :
    toOperator (compositionCoefficients L R c) = operatorComposition L R (synthesis c) := by
  have h₁ := (hasSum_compositionCoefficients L R c).mapL
    (toOperator (𝕜 := 𝕜) (E := G) (F := H))
  have h₂ := ((hasSum_ofCoefficients c).mapL
    (toOperator (𝕜 := 𝕜) (E := E) (F := F))).mapL (operatorComposition L R)
  simp only [map_smul, toOperator_compositionAtom] at h₁
  simp only [map_smul, toOperator_ofAtom, toOperator_ofCoefficients] at h₂
  exact h₁.unique h₂

theorem synthesisKernel_le_compositionCoefficients_ker (L : F →L[𝕜] H) (R : G →L[𝕜] E) :
    synthesisKernel (𝕜 := 𝕜) (E := E) (F := F) ≤ (compositionCoefficients L R).ker := by
  intro c hc
  change compositionCoefficients L R c = 0
  apply toOperator_injective
  rw [toOperator_compositionCoefficients, map_zero]
  have hs : synthesis c = 0 := hc
  simp [hs]

def compose (L : F →L[𝕜] H) (R : G →L[𝕜] E) : Nuclear 𝕜 E F →L[𝕜] Nuclear 𝕜 G H :=
  synthesisKernel.liftQL (compositionCoefficients L R)
    (synthesisKernel_le_compositionCoefficients_ker L R)

@[simp] theorem compose_ofCoefficients (L : F →L[𝕜] H) (R : G →L[𝕜] E)
    (c : Coefficients 𝕜 E F) :
    compose L R (ofCoefficients c) = compositionCoefficients L R c := rfl

@[simp] theorem toOperator_compose (L : F →L[𝕜] H) (R : G →L[𝕜] E) (T : Nuclear 𝕜 E F) :
    toOperator (compose L R T) = L ∘L toOperator T ∘L R := by
  obtain ⟨c, rfl⟩ := ofCoefficients_surjective T
  exact toOperator_compositionCoefficients L R c

@[simp] theorem compose_rankOne (L : F →L[𝕜] H) (R : G →L[𝕜] E)
    (φ : E →L[𝕜] 𝕜) (y : F) :
    compose L R (rankOne φ y) = rankOne (φ ∘L R) (L y) := by
  apply toOperator_injective
  rw [toOperator_compose, toOperator_rankOne, toOperator_rankOne]
  ext x
  simp

theorem norm_compose_apply_le (L : F →L[𝕜] H) (R : G →L[𝕜] E) (T : Nuclear 𝕜 E F) :
    ‖compose L R T‖ ≤ (‖L‖ * ‖R‖) * ‖T‖ := by
  let K := ‖L‖ * ‖R‖
  have hK : 0 ≤ K := mul_nonneg (norm_nonneg L) (norm_nonneg R)
  apply le_of_forall_pos_le_add
  intro ε hε
  have hden : 0 < K + 1 := by linarith
  obtain ⟨c, hc, hcost⟩ := exists_representation_norm_lt T (div_pos hε hden)
  rw [← hc, compose_ofCoefficients]
  calc
    ‖compositionCoefficients L R c‖ ≤ K * ‖c‖ :=
      (compositionCoefficients L R).le_of_opNorm_le (norm_compositionCoefficients_le L R) c
    _ ≤ K * (‖ofCoefficients c‖ + ε / (K + 1)) :=
      mul_le_mul_of_nonneg_left (by simpa only [hc] using hcost.le) hK
    _ ≤ K * ‖ofCoefficients c‖ + ε := by
      rw [mul_add]
      apply add_le_add_right
      rw [← mul_div_assoc]
      apply (div_le_iff₀ hden).mpr
      nlinarith

end Composition

def compression (b : HilbertBasis ι 𝕜 E) (s : Finset ι) :
    Nuclear 𝕜 E E →L[𝕜] Nuclear 𝕜 E E :=
  compose (finiteProjection b s) (finiteProjection b s)

@[simp] theorem toOperator_compression (b : HilbertBasis ι 𝕜 E) (s : Finset ι)
    (T : Nuclear 𝕜 E E) :
    toOperator (compression b s T) = finiteProjection b s ∘L toOperator T ∘L finiteProjection b s :=
  toOperator_compose _ _ T

theorem norm_compression_apply_le (b : HilbertBasis ι 𝕜 E) (s : Finset ι)
    (T : Nuclear 𝕜 E E) : ‖compression b s T‖ ≤ ‖T‖ := by
  refine (norm_compose_apply_le _ _ T).trans ?_
  have hp := norm_finiteProjection_le_one b s
  have hsq : ‖finiteProjection b s‖ * ‖finiteProjection b s‖ ≤ 1 := by
    simpa using mul_le_mul hp hp (norm_nonneg (finiteProjection b s)) zero_le_one
  simpa using mul_le_mul_of_nonneg_right hsq (norm_nonneg T)

theorem compression_range_le_span (b : HilbertBasis ι 𝕜 E) (s : Finset ι)
    (T : Nuclear 𝕜 E E) :
    (toOperator (compression b s T)).toLinearMap.range ≤ Submodule.span 𝕜 (b '' (s : Set ι)) := by
  rintro y ⟨x, rfl⟩
  change toOperator (compression b s T) x ∈ _
  rw [toOperator_compression]
  exact finiteProjection_mem_span b s _

theorem compression_finiteRank (b : HilbertBasis ι 𝕜 E) (s : Finset ι)
    (T : Nuclear 𝕜 E E) : FiniteDimensional 𝕜 (toOperator (compression b s T)).toLinearMap.range := by
  letI := FiniteDimensional.span_of_finite 𝕜 (s.finite_toSet.image b)
  exact Submodule.finiteDimensional_of_le (compression_range_le_span b s T)

theorem compression_isPositive (b : HilbertBasis ι 𝕜 E) (s : Finset ι)
    (T : Nuclear 𝕜 E E) (hT : (toOperator T).IsPositive) :
    (toOperator (compression b s T)).IsPositive := by
  have hp : (finiteProjection b s).adjoint = finiteProjection b s :=
    LinearMap.IsSymmetric.clm_adjoint_eq (finiteProjection_inner b s)
  rw [toOperator_compression]
  simpa only [hp] using hT.conj_adjoint (finiteProjection b s)

theorem rankOne_atom_eq_ofAtom (a : Atom 𝕜 E E) : rankOne a.1.1 a.2.1 = ofAtom a := by
  apply toOperator_injective
  simp only [toOperator_rankOne, toOperator_ofAtom, atomOperator]

theorem rankOne_sub_identity (φ ψ : E →L[𝕜] 𝕜) (y z : E) :
    rankOne φ y - rankOne ψ z = rankOne (φ - ψ) y + rankOne ψ (y - z) := by
  apply toOperator_injective
  ext x
  simp only [map_sub, map_add, toOperator_rankOne, add_apply, sub_apply,
    ContinuousLinearMap.smulRight_apply, sub_smul, smul_sub]
  abel

theorem norm_rankOne_sub_le (φ ψ : E →L[𝕜] 𝕜) (y z : E) :
    ‖rankOne φ y - rankOne ψ z‖ ≤ ‖φ - ψ‖ * ‖y‖ + ‖ψ‖ * ‖y - z‖ := by
  rw [rankOne_sub_identity]
  simpa only [norm_rankOne] using norm_add_le (rankOne (φ - ψ) y) (rankOne ψ (y - z))

theorem functional_projection_tendsto (b : HilbertBasis ι 𝕜 E) (φ : E →L[𝕜] 𝕜) :
    Tendsto (fun s : Finset ι => φ ∘L finiteProjection b s) atTop (𝓝 φ) := by
  let v := (InnerProductSpace.toDual 𝕜 E).symm φ
  have hv (x : E) : inner 𝕜 v x = φ x := InnerProductSpace.toDual_symm_apply
  have heq (s : Finset ι) : φ ∘L finiteProjection b s = innerSL 𝕜 (finiteProjection b s v) := by
    ext x
    rw [ContinuousLinearMap.comp_apply, innerSL_apply_apply, finiteProjection_inner, hv]
  have hφ : innerSL 𝕜 v = φ := ContinuousLinearMap.ext hv
  have hnorm (s : Finset ι) : ‖φ ∘L finiteProjection b s - φ‖ = ‖finiteProjection b s v - v‖ := by
    rw [heq s, ← hφ, ← map_sub, innerSL_apply_norm]
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [hnorm, sub_self, norm_zero] using
    ((tendsto_finiteProjection_apply b v).sub_const v).norm

theorem compositionAtom_projection_tendsto (b : HilbertBasis ι 𝕜 E) (a : Atom 𝕜 E E) :
    Tendsto (fun s : Finset ι => compositionAtom (finiteProjection b s) (finiteProjection b s) a)
      atTop (𝓝 (ofAtom a)) := by
  rw [← rankOne_atom_eq_ofAtom a]
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hφ := ((functional_projection_tendsto b a.1.1).sub_const a.1.1).norm
  have hy := ((tendsto_finiteProjection_apply b a.2.1).sub_const a.2.1).norm
  apply squeeze_zero (fun s => norm_nonneg _) (fun s => ?_) (by simpa using hφ.add hy)
  refine (norm_rankOne_sub_le (a.1.1 ∘L finiteProjection b s) a.1.1
    (finiteProjection b s a.2.1) a.2.1).trans ?_
  apply add_le_add
  · exact (mul_le_mul_of_nonneg_left
      ((norm_finiteProjection_apply_le b s a.2.1).trans a.2.2) (norm_nonneg _)).trans_eq
        (mul_one _)
  · exact (mul_le_mul_of_nonneg_right a.1.2 (norm_nonneg _)).trans_eq (one_mul _)

theorem norm_compositionAtom_projection_le_one (b : HilbertBasis ι 𝕜 E)
    (s : Finset ι) (a : Atom 𝕜 E E) :
    ‖compositionAtom (finiteProjection b s) (finiteProjection b s) a‖ ≤ 1 := by
  refine (norm_compositionAtom_le _ _ a).trans ?_
  simpa using mul_le_mul (norm_finiteProjection_le_one b s) (norm_finiteProjection_le_one b s)
    (norm_nonneg (finiteProjection b s)) zero_le_one

theorem compression_tendsto (b : HilbertBasis ι 𝕜 E) (T : Nuclear 𝕜 E E) :
    Tendsto (fun s : Finset ι => compression b s T) atTop (𝓝 T) := by
  obtain ⟨c, rfl⟩ := ofCoefficients_surjective T
  change Tendsto (fun s : Finset ι =>
    compositionCoefficients (finiteProjection b s) (finiteProjection b s) c)
      atTop (𝓝 (ofCoefficients c))
  simp_rw [compositionCoefficients_apply]
  have hsum : Summable (fun a => ‖c a‖) := by simpa using c.2.summable
  have h := tendsto_tsum_of_dominated_convergence hsum
    (fun a => (compositionAtom_projection_tendsto b a).const_smul (c a))
    (Eventually.of_forall (fun s a => by
      rw [norm_smul]
      simpa using mul_le_mul_of_nonneg_left (norm_compositionAtom_projection_le_one b s a)
        (norm_nonneg (c a))))
  simpa only [(hasSum_ofCoefficients c).tsum_eq] using h

theorem initial_compression_tendsto (b : HilbertBasis ℕ 𝕜 E) (T : Nuclear 𝕜 E E) :
    Tendsto (fun n : ℕ => compression b (Finset.range n) T) atTop (𝓝 T) :=
  (compression_tendsto b T).comp Filter.tendsto_finset_range

theorem trace_compression_tendsto (b : HilbertBasis ι 𝕜 E) (T : Nuclear 𝕜 E E) :
    Tendsto (fun s : Finset ι => HilbertNuclearTrace.trace (compression b s T))
      atTop (𝓝 (HilbertNuclearTrace.trace T)) :=
  (HilbertNuclearTrace.trace (𝕜 := 𝕜) (E := E)).continuous.tendsto T |>.comp (compression_tendsto b T)

end QuantumProver.HilbertNuclearCompression

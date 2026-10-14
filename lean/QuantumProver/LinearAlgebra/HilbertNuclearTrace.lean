import QuantumProver.LinearAlgebra.NuclearOperator
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Topology.Algebra.InfiniteSum.Real

set_option autoImplicit false

noncomputable section

open Filter
open scoped BigOperators Topology lp Classical ENNReal InnerProductSpace

namespace QuantumProver.HilbertNuclearTrace

open NuclearOperator

variable {𝕜 E ι : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

def diagonal (b : HilbertBasis ι 𝕜 E) (T : E →L[𝕜] E) (i : ι) : 𝕜 :=
  inner 𝕜 (b i) (T (b i))

def diagonalCLM (b : HilbertBasis ι 𝕜 E) (i : ι) : (E →L[𝕜] E) →L[𝕜] 𝕜 :=
  (innerSL 𝕜 (b i)) ∘L (ContinuousLinearMap.apply 𝕜 E (b i))

@[simp] theorem diagonalCLM_apply (b : HilbertBasis ι 𝕜 E) (i : ι) (T : E →L[𝕜] E) :
    diagonalCLM b i T = diagonal b T i := rfl

theorem hasSum_rankOne_diagonal (b : HilbertBasis ι 𝕜 E)
    (φ : E →L[𝕜] 𝕜) (y : E) :
    HasSum (fun i => diagonal b (φ.smulRight y) i) (φ y) := by
  simpa only [diagonal, ContinuousLinearMap.smulRight_apply, inner_smul_right,
    map_smul, HilbertBasis.repr_apply_apply, smul_eq_mul, mul_comm] using
      (b.hasSum_repr y).mapL φ

theorem rankOne_diagonal_cost (b : HilbertBasis ι 𝕜 E)
    (φ : E →L[𝕜] 𝕜) (y : E) :
    Summable (fun i => ‖diagonal b (φ.smulRight y) i‖) ∧
      ∑' i, ‖diagonal b (φ.smulRight y) i‖ ≤ ‖φ‖ * ‖y‖ := by
  let v := (InnerProductSpace.toDual 𝕜 E).symm φ
  have hvnorm : ‖v‖ = ‖φ‖ := (InnerProductSpace.toDual 𝕜 E).symm.norm_map φ
  have heq (i : ι) : ‖diagonal b (φ.smulRight y) i‖ =
      ‖b.repr v i‖ * ‖b.repr y i‖ := by
    rw [diagonal, ContinuousLinearMap.smulRight_apply, inner_smul_right, norm_mul]
    rw [← InnerProductSpace.toDual_symm_apply (𝕜 := 𝕜) (x := b i) (y := φ)]
    rw [HilbertBasis.repr_apply_apply, HilbertBasis.repr_apply_apply]
    change ‖inner 𝕜 v (b i)‖ * ‖inner 𝕜 (b i) y‖ =
      ‖inner 𝕜 (b i) v‖ * ‖inner 𝕜 (b i) y‖
    rw [norm_inner_symm v (b i)]
  have hh : (2 : ℝ≥0∞).toReal.HolderConjugate (2 : ℝ≥0∞).toReal := by
    rw [Real.holderConjugate_iff]
    norm_num
  have h := lp.tsum_mul_le_mul_norm hh (b.repr v) (b.repr y)
  constructor
  · simpa only [heq] using h.1
  · calc
      ∑' i, ‖diagonal b (φ.smulRight y) i‖ = ∑' i, ‖b.repr v i‖ * ‖b.repr y i‖ :=
        tsum_congr heq
      _ ≤ ‖b.repr v‖ * ‖b.repr y‖ := h.2
      _ = ‖φ‖ * ‖y‖ := by rw [b.repr.norm_map, b.repr.norm_map, hvnorm]

theorem atom_diagonal_cost (b : HilbertBasis ι 𝕜 E) (a : Atom 𝕜 E E) :
    Summable (fun i => ‖diagonal b (atomOperator a) i‖) ∧
      ∑' i, ‖diagonal b (atomOperator a) i‖ ≤ 1 := by
  have h := rankOne_diagonal_cost b a.1.1 a.2.1
  refine ⟨h.1, h.2.trans ?_⟩
  calc
    ‖a.1.1‖ * ‖a.2.1‖ ≤ 1 * 1 := mul_le_mul a.1.2 a.2.2 (norm_nonneg _) zero_le_one
    _ = 1 := one_mul _

def atomPairing (a : Atom 𝕜 E E) : 𝕜 := a.1.1 a.2.1

theorem norm_atomPairing_le_one (a : Atom 𝕜 E E) : ‖atomPairing a‖ ≤ 1 := by
  refine (a.1.1.le_opNorm a.2.1).trans ?_
  calc
    ‖a.1.1‖ * ‖a.2.1‖ ≤ 1 * 1 := mul_le_mul a.1.2 a.2.2 (norm_nonneg _) zero_le_one
    _ = 1 := one_mul _

def pairingTerms : Coefficients 𝕜 E E →L[𝕜] ℓ¹(Atom 𝕜 E E, 𝕜) :=
  lp.mapCLM 1 (fun a => ContinuousLinearMap.toSpanSingleton 𝕜 (atomPairing a))
    zero_le_one (fun a => by simpa using norm_atomPairing_le_one a)

theorem norm_pairingTerms_le_one : ‖pairingTerms (𝕜 := 𝕜) (E := E)‖ ≤ 1 :=
  lp.norm_mapCLM_le 1
    (fun a => ContinuousLinearMap.toSpanSingleton 𝕜 (atomPairing a))
    zero_le_one (fun a => by simpa using norm_atomPairing_le_one a)

def coefficientTrace : Coefficients 𝕜 E E →L[𝕜] 𝕜 :=
  lp.tsumCLM 𝕜 (Atom 𝕜 E E) 𝕜 ∘L pairingTerms

@[simp] theorem coefficientTrace_apply (c : Coefficients 𝕜 E E) :
    coefficientTrace c = ∑' a, c a * atomPairing a := by
  simp [coefficientTrace, pairingTerms, smul_eq_mul]

theorem norm_coefficientTrace_le_one : ‖coefficientTrace (𝕜 := 𝕜) (E := E)‖ ≤ 1 := by
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
  calc
    ‖lp.tsumCLM 𝕜 (Atom 𝕜 E E) 𝕜‖ * ‖pairingTerms (𝕜 := 𝕜) (E := E)‖ ≤ 1 * 1 :=
      mul_le_mul lp.norm_tsumCLM_le norm_pairingTerms_le_one
        (norm_nonneg (pairingTerms (𝕜 := 𝕜) (E := E))) zero_le_one
    _ = 1 := one_mul _

theorem norm_coefficientTrace_apply_le (c : Coefficients 𝕜 E E) :
    ‖coefficientTrace c‖ ≤ ‖c‖ := by
  simpa using (coefficientTrace (𝕜 := 𝕜) (E := E)).le_of_opNorm_le
    norm_coefficientTrace_le_one c

theorem hasSum_synthesis_diagonal (b : HilbertBasis ι 𝕜 E)
    (c : Coefficients 𝕜 E E) (i : ι) :
    HasSum (fun a => c a * diagonal b (atomOperator a) i) (diagonal b (synthesis c) i) := by
  simpa only [map_smul, toOperator_ofAtom, toOperator_ofCoefficients,
    diagonalCLM_apply, smul_eq_mul] using
      ((hasSum_ofCoefficients c).mapL (toOperator (𝕜 := 𝕜) (E := E) (F := E))).mapL
        (diagonalCLM b i)

theorem summable_norm_diagonal_row (b : HilbertBasis ι 𝕜 E)
    (c : Coefficients 𝕜 E E) (a : Atom 𝕜 E E) :
    Summable (fun i => ‖c a * diagonal b (atomOperator a) i‖) := by
  simpa only [norm_mul] using (atom_diagonal_cost b a).1.mul_left ‖c a‖

theorem tsum_norm_diagonal_row_le (b : HilbertBasis ι 𝕜 E)
    (c : Coefficients 𝕜 E E) (a : Atom 𝕜 E E) :
    ∑' i, ‖c a * diagonal b (atomOperator a) i‖ ≤ ‖c a‖ := by
  simp only [norm_mul, tsum_mul_left]
  simpa using mul_le_mul_of_nonneg_left (atom_diagonal_cost b a).2 (norm_nonneg (c a))

theorem summable_norm_diagonal_double (b : HilbertBasis ι 𝕜 E)
    (c : Coefficients 𝕜 E E) :
    Summable (fun p : Atom 𝕜 E E × ι =>
      ‖c p.1 * diagonal b (atomOperator p.1) p.2‖) := by
  refine (summable_prod_of_nonneg (fun p => norm_nonneg _)).mpr ⟨?_, ?_⟩
  · exact summable_norm_diagonal_row b c
  · exact Summable.of_nonneg_of_le (fun a => tsum_nonneg (fun i => norm_nonneg _))
      (tsum_norm_diagonal_row_le b c) (by simpa using c.2.summable)

theorem summable_norm_synthesis_diagonal (b : HilbertBasis ι 𝕜 E)
    (c : Coefficients 𝕜 E E) : Summable (fun i => ‖diagonal b (synthesis c) i‖) := by
  have h := summable_norm_diagonal_double b c
  refine Summable.of_nonneg_of_le (fun i => norm_nonneg _) (fun i => ?_) h.prod_symm.prod
  rw [← (hasSum_synthesis_diagonal b c i).tsum_eq]
  exact norm_tsum_le_tsum_norm (h.prod_symm.prod_factor i)

set_option maxHeartbeats 1200000 in

theorem coefficientTrace_eq_diagonal_tsum (b : HilbertBasis ι 𝕜 E)
    (c : Coefficients 𝕜 E E) :
    coefficientTrace c = ∑' i, diagonal b (synthesis c) i := by
  have h : Summable (fun p : Atom 𝕜 E E × ι =>
      c p.1 * diagonal b (atomOperator p.1) p.2) :=
    (summable_norm_diagonal_double b c).of_norm
  rw [coefficientTrace_apply]
  calc
    ∑' a, c a * atomPairing a = ∑' a, ∑' i, c a * diagonal b (atomOperator a) i := by
      apply tsum_congr
      intro a
      simpa only [atomOperator, atomPairing] using
        ((hasSum_rankOne_diagonal b a.1.1 a.2.1).mul_left (c a)).tsum_eq.symm
    _ = ∑' i, ∑' a, c a * diagonal b (atomOperator a) i := h.tsum_comm.symm
    _ = ∑' i, diagonal b (synthesis c) i :=
      tsum_congr (fun i => (hasSum_synthesis_diagonal b c i).tsum_eq)

theorem synthesisKernel_le_coefficientTrace_ker :
    synthesisKernel (𝕜 := 𝕜) (E := E) (F := E) ≤
      (coefficientTrace (𝕜 := 𝕜) (E := E)).ker := by
  obtain ⟨w, b, hb⟩ := exists_hilbertBasis 𝕜 E
  intro c hc
  change coefficientTrace c = 0
  rw [coefficientTrace_eq_diagonal_tsum b c]
  have hs : synthesis c = 0 := hc
  simp [hs, diagonal]

def trace : Nuclear 𝕜 E E →L[𝕜] 𝕜 :=
  synthesisKernel.liftQL coefficientTrace synthesisKernel_le_coefficientTrace_ker

@[simp] theorem trace_ofCoefficients (c : Coefficients 𝕜 E E) :
    trace (ofCoefficients c) = coefficientTrace c := rfl

theorem norm_trace_apply_le (T : Nuclear 𝕜 E E) : ‖trace T‖ ≤ ‖T‖ := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨c, rfl, hc⟩ := exists_representation_norm_lt T hε
  exact (norm_coefficientTrace_apply_le c).trans hc.le

theorem norm_trace_le_one : ‖trace (𝕜 := 𝕜) (E := E)‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun T => by simpa using norm_trace_apply_le T)

theorem summable_norm_diagonal (b : HilbertBasis ι 𝕜 E) (T : Nuclear 𝕜 E E) :
    Summable (fun i => ‖diagonal b (toOperator T) i‖) := by
  obtain ⟨c, rfl⟩ := ofCoefficients_surjective T
  exact summable_norm_synthesis_diagonal b c

theorem trace_eq_diagonal_tsum (b : HilbertBasis ι 𝕜 E) (T : Nuclear 𝕜 E E) :
    trace T = ∑' i, inner 𝕜 (b i) (toOperator T (b i)) := by
  obtain ⟨c, rfl⟩ := ofCoefficients_surjective T
  exact coefficientTrace_eq_diagonal_tsum b c

theorem hasSum_diagonal (b : HilbertBasis ι 𝕜 E) (T : Nuclear 𝕜 E E) :
    HasSum (fun i => inner 𝕜 (b i) (toOperator T (b i))) (trace T) := by
  rw [trace_eq_diagonal_tsum b T]
  exact (summable_norm_diagonal b T).of_norm.hasSum

@[simp] theorem trace_rankOne (φ : E →L[𝕜] 𝕜) (y : E) : trace (rankOne φ y) = φ y := by
  obtain ⟨w, b, hb⟩ := exists_hilbertBasis 𝕜 E
  rw [trace_eq_diagonal_tsum b, toOperator_rankOne]
  exact (hasSum_rankOne_diagonal b φ y).tsum_eq

@[simp] theorem trace_ofSeries {κ : Type*} (φ : κ → E →L[𝕜] 𝕜) (y : κ → E)
    (h : Summable (fun i => ‖φ i‖ * ‖y i‖)) :
    trace (ofSeries φ y h) = ∑' i, φ i (y i) := by
  rw [ofSeries, ContinuousLinearMap.map_tsum _ (summable_rankOne φ y h)]
  simp

theorem re_trace_eq_tsum_re_diagonal (b : HilbertBasis ι 𝕜 E) (T : Nuclear 𝕜 E E) :
    RCLike.re (trace T) = ∑' i, RCLike.re (inner 𝕜 (b i) (toOperator T (b i))) := by
  rw [trace_eq_diagonal_tsum b T]
  exact RCLike.reCLM.map_tsum (hasSum_diagonal b T).summable

theorem re_trace_le_norm (T : Nuclear 𝕜 E E) : RCLike.re (trace T) ≤ ‖T‖ :=
  (RCLike.re_le_norm _).trans (norm_trace_apply_le T)

end QuantumProver.HilbertNuclearTrace

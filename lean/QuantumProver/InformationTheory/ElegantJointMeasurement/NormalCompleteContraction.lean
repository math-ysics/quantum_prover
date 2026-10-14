import QuantumProver.InformationTheory.ElegantJointMeasurement.NormalInstrumentAbsorption

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000

open MeasureTheory Set Filter Function InnerProductSpace
open scoped BigOperators InnerProduct ComplexOrder Topology

namespace QuantumProver.ElegantJointMeasurement.NormalCompleteContraction

open QuantumProver.ElegantJointMeasurement.HilbertChoi QuantumProver.ElegantJointMeasurement.NuclearChoi QuantumProver.ElegantJointMeasurement.NormalCPInstruments
open QuantumProver.ElegantJointMeasurement.NormalInstrumentAbsorption
open QuantumProver.HilbertNuclearCompression
open QuantumProver.NuclearOperator (toOperator toOperator_injective)

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable {R S : Type} [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S]

local instance blockComplete {K : Type} [Fintype K]
    {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G] :
    CompleteSpace (BlockSpace K G) := PiLp.completeSpace 2 (fun _ : K => G)

theorem inner_insert_left (i : R) (x : E) (v : BlockSpace R E) :
    inner ℂ (insert i x) v = inner ℂ x (v i) := by
  rw [PiLp.inner_apply]
  have hterm (j : R) : inner ℂ (insert i x j) (v j) =
      if j = i then inner ℂ x (v i) else 0 := by
    by_cases h : j = i
    · subst j
      simp [insert_apply_apply]
    · simp [insert_apply_apply, h]
  simp_rw [hterm]
  simp

theorem innerSL_insert (v : BlockSpace R E) (i : R) :
    innerSL ℂ v ∘L insert i = innerSL ℂ (v i) := by
  ext x
  change inner ℂ v (insert i x) = inner ℂ (v i) x
  rw [← inner_conj_symm, inner_insert_left, inner_conj_symm]

theorem insert_adjoint (i : R) :
    (insert (E := E) i).adjoint = PiLp.proj 2 (fun _ : R => E) i := by
  ext v
  apply ext_inner_left ℂ
  intro x
  exact ((insert (E := E) i).adjoint_inner_right x v).trans
    (inner_insert_left i x v)

theorem nuclearBlock_isPositive (T : Nuclear (BlockSpace R E))
    (hT : (toOperator T).IsPositive) (i : R) :
    (toOperator (nuclearBlock i i T)).IsPositive := by
  rw [toOperator_nuclearBlock, ← insert_adjoint]
  exact hT.adjoint_conj (insert i)

theorem trace_nuclearAssembly (A : R → R → Nuclear E) :
    QuantumProver.HilbertNuclearTrace.trace (nuclearAssembly A) =
      ∑ r, QuantumProver.HilbertNuclearTrace.trace (A r r) := by
  simp only [nuclearAssembly, map_sum, trace_block]
  simp

theorem sum_trace_nuclearBlock (T : Nuclear (BlockSpace R E)) :
    (∑ r, QuantumProver.HilbertNuclearTrace.trace (nuclearBlock r r T)) =
      QuantumProver.HilbertNuclearTrace.trace T := by
  exact (trace_nuclearAssembly (fun i j => nuclearBlock i j T)).symm.trans
    (congrArg QuantumProver.HilbertNuclearTrace.trace (nuclearAssembly_nuclearBlock T))

theorem trace_normalAmplification (Φ : NormalOperation F E)
    (hTP : ∀ T, QuantumProver.HilbertNuclearTrace.trace (Φ T) =
      QuantumProver.HilbertNuclearTrace.trace T)
    (T : Nuclear (BlockSpace R F)) :
    QuantumProver.HilbertNuclearTrace.trace (normalAmplification Φ T) =
      QuantumProver.HilbertNuclearTrace.trace T := by
  rw [normalAmplification_apply, trace_nuclearAssembly]
  simp only [hTP]
  exact sum_trace_nuclearBlock T

def TraceNonincreasing (Φ : NormalOperation F E) : Prop :=
  ∀ T : Nuclear F, (toOperator T).IsPositive →
    (QuantumProver.HilbertNuclearTrace.trace (Φ T)).re ≤
      (QuantumProver.HilbertNuclearTrace.trace T).re

theorem re_trace_normalAmplification_le (Φ : NormalOperation F E)
    (hTNI : TraceNonincreasing Φ) (T : Nuclear (BlockSpace R F))
    (hT : (toOperator T).IsPositive) :
    (QuantumProver.HilbertNuclearTrace.trace (normalAmplification Φ T)).re ≤
      (QuantumProver.HilbertNuclearTrace.trace T).re := by
  rw [normalAmplification_apply, trace_nuclearAssembly, ← sum_trace_nuclearBlock T]
  change RCLike.re (∑ r, QuantumProver.HilbertNuclearTrace.trace (Φ (nuclearBlock r r T))) ≤
    RCLike.re (∑ r, QuantumProver.HilbertNuclearTrace.trace (nuclearBlock r r T))
  simp only [map_sum]
  exact Finset.sum_le_sum (fun i _ => hTNI _ (nuclearBlock_isPositive T hT i))

theorem nuclearBlock_rankOne (x y : BlockSpace R E) (i j : R) :
    nuclearBlock i j (QuantumProver.NuclearOperator.rankOne (innerSL ℂ x) y) =
      QuantumProver.NuclearOperator.rankOne (innerSL ℂ (x j)) (y i) := by
  simp only [nuclearBlock, compose_rankOne, innerSL_insert, PiLp.proj_apply]

theorem positiveNuclearColumns_hasSum {L : Type*} (b : HilbertBasis L ℂ E)
    (T : Nuclear E) (hT : (toOperator T).IsPositive) :
    HasSum (nuclearColumn b (toOperator T)) T := by
  have hd0 := ((QuantumProver.HilbertNuclearTrace.hasSum_diagonal b T).mapL Complex.reCLM).summable
  have hd : Summable (fun l => (inner ℂ (toOperator T (b l)) (b l)).re) := by
    convert hd0 using 1
    funext l
    exact inner_re_symm (𝕜 := ℂ) _ _
  have heq := positiveLift_eq_of_toOperator b (toOperator T) hT hd T rfl
  simpa only [heq] using nuclearColumns_hasSum b (toOperator T) hT hd

theorem norm_positive_twoBlock_offDiagonal_le (T : Nuclear (BlockSpace (Fin 2) E))
    (hT : (toOperator T).IsPositive) :
    ‖nuclearBlock 0 1 T‖ ≤ (QuantumProver.HilbertNuclearTrace.trace T).re / 2 := by
  obtain ⟨L, b, hb⟩ := exists_hilbertBasis ℂ (BlockSpace (Fin 2) E)
  let D := toOperator T
  let c := nuclearColumn b D
  let d : L → ℝ := fun l => (inner ℂ (D (b l)) (b l)).re
  have hd0 := ((QuantumProver.HilbertNuclearTrace.hasSum_diagonal b T).mapL Complex.reCLM).summable
  have hd : Summable d := by
    convert hd0 using 1
    funext l
    change (inner ℂ (D (b l)) (b l)).re = (inner ℂ (b l) (D (b l))).re
    exact inner_re_symm (𝕜 := ℂ) (D (b l)) (b l)
  have htrace : (∑' l, d l) = (QuantumProver.HilbertNuclearTrace.trace T).re := by
    change (∑' l, d l) = RCLike.re (QuantumProver.HilbertNuclearTrace.trace T)
    rw [QuantumProver.HilbertNuclearTrace.re_trace_eq_tsum_re_diagonal b]
    apply tsum_congr
    intro l
    change (inner ℂ (D (b l)) (b l)).re = (inner ℂ (b l) (D (b l))).re
    exact inner_re_symm (𝕜 := ℂ) (D (b l)) (b l)
  have hs : HasSum c T := positiveNuclearColumns_hasSum b T hT
  have hx (l : L) : ‖nuclearBlock (E := E) 0 1 (c l)‖ ≤ d l / 2 := by
    let v := squareRootColumn b D l
    have hv : ‖v‖ ^ 2 = ‖v 0‖ ^ 2 + ‖v 1‖ ^ 2 := by
      rw [PiLp.norm_sq_eq_of_L2]
      simp only [Fin.sum_univ_two]
    have hvd : ‖v‖ ^ 2 = d l := squareRootColumn_norm_sq b D hT l
    change ‖nuclearBlock (E := E) 0 1
      (QuantumProver.NuclearOperator.rankOne (innerSL ℂ v) v)‖ ≤ d l / 2
    rw [nuclearBlock_rankOne, QuantumProver.NuclearOperator.norm_rankOne, innerSL_apply_norm]
    nlinarith [sq_nonneg (‖v 0‖ - ‖v 1‖)]
  have hn : Summable (fun l => ‖nuclearBlock (E := E) 0 1 (c l)‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hx (hd.div_const 2)
  have hh := (nuclearBlock (E := E) 0 1).hasSum hs
  rw [← hh.tsum_eq]
  calc
    ‖∑' l, nuclearBlock (E := E) 0 1 (c l)‖ ≤
        ∑' l, ‖nuclearBlock (E := E) 0 1 (c l)‖ := norm_tsum_le_tsum_norm hn
    _ ≤ ∑' l, d l / 2 := hn.tsum_le_tsum hx (hd.div_const 2)
    _ = (QuantumProver.HilbertNuclearTrace.trace T).re / 2 := by rw [tsum_div_const, htrace]

@[simp] theorem nuclearBlock_normalAmplification (Φ : NormalOperation F E)
    (T : Nuclear (BlockSpace R F)) (i j : R) :
    nuclearBlock i j (normalAmplification Φ T) = Φ (nuclearBlock i j T) := by
  rw [normalAmplification_apply, nuclearBlock_nuclearAssembly]

theorem nuclearRankOne_isPositive (x : E) :
    (toOperator (QuantumProver.NuclearOperator.rankOne (innerSL ℂ x) x)).IsPositive := by
  rw [QuantumProver.NuclearOperator.toOperator_rankOne]
  exact InnerProductSpace.isPositive_rankOne_self x

theorem norm_operation_rankOne_le_one (Φ : NormalOperation F E)
    (hCP : NormalCompletelyPositive Φ) (hTNI : TraceNonincreasing Φ)
    (x y : F) (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) :
    ‖Φ (QuantumProver.NuclearOperator.rankOne (innerSL ℂ x) y)‖ ≤ 1 := by
  let w : BlockSpace (Fin 2) F := WithLp.toLp 2 (fun i => if i = 0 then y else x)
  let A := QuantumProver.NuclearOperator.rankOne (innerSL ℂ w) w
  have hA : (toOperator A).IsPositive := nuclearRankOne_isPositive w
  have hB := hCP (Fin 2) A hA
  have hb : nuclearBlock 0 1 (normalAmplification Φ A) =
      Φ (QuantumProver.NuclearOperator.rankOne (innerSL ℂ x) y) := by
    rw [nuclearBlock_normalAmplification]
    simp [A, nuclearBlock_rankOne, w]
  have ht := re_trace_normalAmplification_le Φ hTNI A hA
  have htrace : (QuantumProver.HilbertNuclearTrace.trace A).re = ‖w‖ ^ 2 := by
    simp [A, QuantumProver.HilbertNuclearTrace.trace_rankOne, inner_self_eq_norm_sq_to_K]
    norm_cast
  have hw : ‖w‖ ^ 2 = ‖y‖ ^ 2 + ‖x‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    simp [w, Fin.sum_univ_two]
  have hoff := norm_positive_twoBlock_offDiagonal_le (normalAmplification Φ A) hB
  rw [hb] at hoff
  nlinarith [norm_nonneg x, norm_nonneg y]

theorem norm_operation_ofAtom_le_one (Φ : NormalOperation F E)
    (hCP : NormalCompletelyPositive Φ) (hTNI : TraceNonincreasing Φ)
    (a : QuantumProver.NuclearOperator.Atom ℂ F F) :
    ‖Φ (QuantumProver.NuclearOperator.ofAtom a)‖ ≤ 1 := by
  let x : F := (InnerProductSpace.toDual ℂ F).symm a.1.1
  have hx : ‖x‖ ≤ 1 := by
    dsimp only [x]
    rw [(InnerProductSpace.toDual ℂ F).symm.norm_map]
    exact a.1.2
  have hφ : innerSL ℂ x = a.1.1 := by
    change InnerProductSpace.toDual ℂ F x = a.1.1
    exact (InnerProductSpace.toDual ℂ F).apply_symm_apply a.1.1
  rw [ofAtom_eq_rankOne, ← hφ]
  exact norm_operation_rankOne_le_one Φ hCP hTNI x a.2.1 hx a.2.2

theorem normalOperation_norm_le_of_cp_trace_nonincreasing (Φ : NormalOperation F E)
    (hCP : NormalCompletelyPositive Φ) (hTNI : TraceNonincreasing Φ)
    (T : Nuclear F) : ‖Φ T‖ ≤ ‖T‖ := by
  have hcoeff (c : QuantumProver.NuclearOperator.Coefficients ℂ F F) :
      ‖Φ (QuantumProver.NuclearOperator.ofCoefficients c)‖ ≤ ‖c‖ := by
    have hc : Summable (fun a => ‖c a‖) := by simpa using c.2.summable
    have hb (a : QuantumProver.NuclearOperator.Atom ℂ F F) :
        ‖Φ (c a • QuantumProver.NuclearOperator.ofAtom a)‖ ≤ ‖c a‖ := by
      rw [map_smul, norm_smul]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left
        (norm_operation_ofAtom_le_one Φ hCP hTNI a) (norm_nonneg (c a))
    have hn : Summable (fun a => ‖Φ (c a • QuantumProver.NuclearOperator.ofAtom a)‖) :=
      Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hb hc
    have hs := Φ.hasSum (QuantumProver.NuclearOperator.hasSum_ofCoefficients c)
    rw [← hs.tsum_eq]
    calc
      ‖∑' a, Φ (c a • QuantumProver.NuclearOperator.ofAtom a)‖ ≤
          ∑' a, ‖Φ (c a • QuantumProver.NuclearOperator.ofAtom a)‖ := norm_tsum_le_tsum_norm hn
      _ ≤ ∑' a, ‖c a‖ := hn.tsum_le_tsum hb hc
      _ = ‖c‖ := by
        simpa using (lp.norm_eq_tsum_rpow (by norm_num : 0 < (1 : ENNReal).toReal) c).symm
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨c, hc, hcost⟩ := QuantumProver.NuclearOperator.exists_representation_norm_lt T hε
  rw [← hc]
  exact (hcoeff c).trans (by simpa only [hc] using hcost.le)

def blockCurry : BlockSpace (Σ _ : S, R) E ≃ₗᵢ[ℂ] BlockSpace S (BlockSpace R E) :=
  LinearIsometryEquiv.piLpCurry ℂ 2 (fun (_ : S) (_ : R) => E)

@[simp] theorem blockCurry_apply_apply (x : BlockSpace (Σ _ : S, R) E) (s : S) (r : R) :
    blockCurry x s r = x ⟨s, r⟩ := rfl

@[simp] theorem blockCurry_symm_apply_apply (x : BlockSpace S (BlockSpace R E))
    (p : Σ _ : S, R) : blockCurry.symm x p = x p.1 p.2 := rfl

theorem blockCurry_insert (s : S) (r : R) (x : E) :
    blockCurry (insert ⟨s, r⟩ x) = insert s (insert r x) := by
  ext t u
  by_cases ht : t = s <;> by_cases hu : u = r <;>
    simp [insert_apply_apply, ht, hu]

def curryNuclear (T : Nuclear (BlockSpace (Σ _ : S, R) E)) :
    Nuclear (BlockSpace S (BlockSpace R E)) :=
  compose
    (blockCurry (E := E) (R := R) (S := S) :
      BlockSpace (Σ _ : S, R) E →L[ℂ] BlockSpace S (BlockSpace R E))
    ((blockCurry (E := E) (R := R) (S := S)).symm :
      BlockSpace S (BlockSpace R E) →L[ℂ] BlockSpace (Σ _ : S, R) E) T

def uncurryNuclear (T : Nuclear (BlockSpace S (BlockSpace R E))) :
    Nuclear (BlockSpace (Σ _ : S, R) E) :=
  compose
    ((blockCurry (E := E) (R := R) (S := S)).symm :
      BlockSpace S (BlockSpace R E) →L[ℂ] BlockSpace (Σ _ : S, R) E)
    (blockCurry (E := E) (R := R) (S := S) :
      BlockSpace (Σ _ : S, R) E →L[ℂ] BlockSpace S (BlockSpace R E)) T

theorem curryNuclear_isPositive (T : Nuclear (BlockSpace (Σ _ : S, R) E))
    (hT : (toOperator T).IsPositive) : (toOperator (curryNuclear T)).IsPositive := by
  rw [curryNuclear, toOperator_compose]
  simpa only [LinearIsometryEquiv.adjoint_eq_symm] using
    hT.conj_adjoint
      (blockCurry (E := E) (R := R) (S := S) :
        BlockSpace (Σ _ : S, R) E →L[ℂ] BlockSpace S (BlockSpace R E))

theorem uncurryNuclear_isPositive (T : Nuclear (BlockSpace S (BlockSpace R E)))
    (hT : (toOperator T).IsPositive) : (toOperator (uncurryNuclear T)).IsPositive := by
  rw [uncurryNuclear, toOperator_compose]
  simpa only [LinearIsometryEquiv.adjoint_eq_symm, LinearIsometryEquiv.symm_symm] using
    hT.conj_adjoint
      ((blockCurry (E := E) (R := R) (S := S)).symm :
        BlockSpace S (BlockSpace R E) →L[ℂ] BlockSpace (Σ _ : S, R) E)

@[simp] theorem curryNuclear_uncurryNuclear (T : Nuclear (BlockSpace S (BlockSpace R E))) :
    curryNuclear (uncurryNuclear T) = T := by
  apply toOperator_injective
  simp only [curryNuclear, uncurryNuclear, toOperator_compose]
  apply ContinuousLinearMap.ext
  intro x
  change blockCurry (blockCurry.symm (toOperator T (blockCurry (blockCurry.symm x)))) =
    toOperator T x
  simp only [LinearIsometryEquiv.apply_symm_apply]

theorem nuclearBlock_ext (T U : Nuclear (BlockSpace R E))
    (h : ∀ i j, nuclearBlock i j T = nuclearBlock i j U) : T = U := by
  rw [← nuclearAssembly_nuclearBlock T, ← nuclearAssembly_nuclearBlock U]
  congr 1
  funext i j
  exact h i j

@[simp] theorem nuclearBlock_uncurryNuclear (T : Nuclear (BlockSpace S (BlockSpace R E)))
    (p q : Σ _ : S, R) :
    nuclearBlock p q (uncurryNuclear T) = nuclearBlock p.2 q.2 (nuclearBlock p.1 q.1 T) := by
  apply toOperator_injective
  simp only [uncurryNuclear, toOperator_compose, toOperator_nuclearBlock]
  apply ContinuousLinearMap.ext
  intro x
  change blockCurry.symm (toOperator T (blockCurry (insert q x))) p =
    toOperator T (insert q.1 (insert q.2 x)) p.1 p.2
  rw [blockCurry_symm_apply_apply]
  cases q with
  | mk s r => rw [blockCurry_insert]

theorem uncurryNuclear_normalAmplification (Φ : NormalOperation F E)
    (T : Nuclear (BlockSpace S (BlockSpace R F))) :
    uncurryNuclear (normalAmplification (R := S) (normalAmplification (R := R) Φ) T) =
      normalAmplification (R := Σ _ : S, R) Φ (uncurryNuclear T) := by
  apply nuclearBlock_ext
  intro p q
  simp only [nuclearBlock_uncurryNuclear, nuclearBlock_normalAmplification]

theorem normalCompletelyPositive_normalAmplification (Φ : NormalOperation F E)
    (hCP : NormalCompletelyPositive Φ) :
    NormalCompletelyPositive (normalAmplification (R := R) Φ) := by
  intro S _ _ T hT
  have hFlat := uncurryNuclear_isPositive T hT
  have hOut := hCP (Σ _ : S, R) (uncurryNuclear T) hFlat
  have hBack := curryNuclear_isPositive _ hOut
  rw [← uncurryNuclear_normalAmplification, curryNuclear_uncurryNuclear] at hBack
  exact hBack

theorem normalAmplification_norm_le_of_cp_trace_nonincreasing (Φ : NormalOperation F E)
    (hCP : NormalCompletelyPositive Φ) (hTNI : TraceNonincreasing Φ)
    (T : Nuclear (BlockSpace R F)) : ‖normalAmplification Φ T‖ ≤ ‖T‖ :=
  normalOperation_norm_le_of_cp_trace_nonincreasing (normalAmplification Φ)
    (normalCompletelyPositive_normalAmplification Φ hCP)
    (fun U hU => re_trace_normalAmplification_le Φ hTNI U hU) T

theorem normalAmplification_norm_le_of_cp_trace_preserving (Φ : NormalOperation F E)
    (hCP : NormalCompletelyPositive Φ)
    (hTP : ∀ T, QuantumProver.HilbertNuclearTrace.trace (Φ T) = QuantumProver.HilbertNuclearTrace.trace T)
    (T : Nuclear (BlockSpace R F)) : ‖normalAmplification Φ T‖ ≤ ‖T‖ :=
  normalAmplification_norm_le_of_cp_trace_nonincreasing Φ hCP
    (fun U _ => (congrArg Complex.re (hTP U)).le) T

theorem normalOperation_isPositive (Φ : NormalOperation F E)
    (hCP : NormalCompletelyPositive Φ) (T : Nuclear F)
    (hT : (toOperator T).IsPositive) : (toOperator (Φ T)).IsPositive := by
  let A : Nuclear (BlockSpace (Fin 1) F) :=
    compose (QuantumProver.ElegantJointMeasurement.HilbertChoi.insert (E := F) (0 : Fin 1))
      (PiLp.proj 2 (fun _ : Fin 1 => F) 0) T
  have hA : (toOperator A).IsPositive := by
    dsimp only [A]
    rw [toOperator_compose, ← insert_adjoint]
    exact hT.conj_adjoint (QuantumProver.ElegantJointMeasurement.HilbertChoi.insert (E := F) (0 : Fin 1))
  have hcorner : nuclearBlock 0 0 A = T := by
    apply toOperator_injective
    simp only [A, toOperator_nuclearBlock, toOperator_compose]
    ext x
    simp [insert_apply_apply]
  have hOut := nuclearBlock_isPositive (normalAmplification Φ A) (hCP (Fin 1) A hA) 0
  simpa only [nuclearBlock_normalAmplification, hcorner] using hOut

theorem re_trace_nonneg_of_isPositive (T : Nuclear E)
    (hT : (toOperator T).IsPositive) : 0 ≤ (QuantumProver.HilbertNuclearTrace.trace T).re := by
  obtain ⟨L, b, hb⟩ := exists_hilbertBasis ℂ E
  rw [← norm_positive_nuclear_eq_re_trace b T hT]
  exact norm_nonneg T

namespace Instrument

variable {H Ω : Type*} [MeasurableSpace H] [MeasurableSpace Ω]
variable (P : QuantumProver.ElegantJointMeasurement.NormalInstrumentAbsorption.Instrument F E H Ω)

theorem operation_union_apply (h : H) (s t : Set Ω)
    (hs : MeasurableSet s) (ht : MeasurableSet t) (hd : Disjoint s t) (T : Nuclear F) :
    P.operation h (s ∪ t) T = P.operation h s T + P.operation h t T := by
  classical
  let a : ℕ → Set Ω := fun n => if n = 0 then s else if n = 1 then t else ∅
  have ha : ∀ n, MeasurableSet (a n) := by
    intro n
    dsimp only [a]
    split_ifs <;> first | exact hs | exact ht | exact MeasurableSet.empty
  have hdis : Pairwise (Disjoint on a) := by
    intro i j hij
    change Disjoint (a i) (a j)
    dsimp only [a]
    split_ifs <;> subst_vars <;> simp_all [disjoint_comm]
  have hu : (⋃ n, a n) = s ∪ t := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_union]
    constructor
    · rintro ⟨n, hn⟩
      dsimp only [a] at hn
      split_ifs at hn with h0 h1
      · exact Or.inl hn
      · exact Or.inr hn
      · exact False.elim hn
    · intro hx
      rcases hx with hx | hx
      · exact ⟨0, by simpa [a] using hx⟩
      · exact ⟨1, by simpa [a] using hx⟩
  have represented_hPhysical := P.countable_additivity h a ha hdis T
  rw [hu] at represented_hPhysical
  have hFinite : HasSum (fun n => P.operation h (a n) T)
      (P.operation h s T + P.operation h t T) := by
    convert (hasSum_ite_eq (0 : ℕ) (P.operation h s T)).add
      (hasSum_ite_eq (1 : ℕ) (P.operation h t T)) using 1
    funext n
    by_cases h0 : n = 0
    · subst n
      simp [a]
    · by_cases h1 : n = 1
      · subst n
        simp [a]
      · simp [a, h0, h1, P.empty]
  exact represented_hPhysical.unique hFinite

theorem traceNonincreasing (h : H) (s : Set Ω) (hs : MeasurableSet s) :
    TraceNonincreasing (P.operation h s) := by
  intro T hT
  have hAdd : P.operation h univ T = P.operation h s T + P.operation h sᶜ T := by
    simpa only [union_compl_self] using
      operation_union_apply P h s sᶜ hs hs.compl disjoint_compl_right T
  have hTrace : (QuantumProver.HilbertNuclearTrace.trace (P.operation h s T)).re +
      (QuantumProver.HilbertNuclearTrace.trace (P.operation h sᶜ T)).re =
      (QuantumProver.HilbertNuclearTrace.trace T).re := by
    have he := congrArg (fun U : Nuclear E => (QuantumProver.HilbertNuclearTrace.trace U).re) hAdd
    simp only [map_add, Complex.add_re] at he
    exact he.symm.trans (congrArg Complex.re (P.trace_preserving h T))
  have hp := re_trace_nonneg_of_isPositive (P.operation h sᶜ T)
    (normalOperation_isPositive _ (P.completelyPositive h sᶜ hs.compl) T hT)
  linarith

theorem normalAmplification_norm_le (h : H) (s : Set Ω) (hs : MeasurableSet s)
    (T : Nuclear (BlockSpace R F)) :
    ‖normalAmplification (P.operation h s) T‖ ≤ ‖T‖ :=
  normalAmplification_norm_le_of_cp_trace_nonincreasing _
    (P.completelyPositive h s hs) (traceNonincreasing P h s hs) T

end Instrument

end QuantumProver.ElegantJointMeasurement.NormalCompleteContraction

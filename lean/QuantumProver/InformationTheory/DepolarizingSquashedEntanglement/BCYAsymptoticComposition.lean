import QuantumProver.InformationTheory.DepolarizingSquashedEntanglement.BCYTestComposition
import QuantumProver.InformationTheory.DepolarizingSquashedEntanglement.BCYTensorRegularization
import QuantumProver.InformationTheory.DepolarizingSquashedEntanglement.BCYCompositeTesting

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

noncomputable section
open Matrix Set Filter
open scoped BigOperators Topology ComplexOrder MatrixOrder Kronecker Matrix.Norms.L2Operator

namespace QuantumProver.DepolarizingSquashedEntanglement.BCYAsymptoticComposition

open BCYRelativeEntropy BCYTestComposition BCYCompositeTesting
open QuantumProver.SuperchannelDiscrimination

variable {A B E I J : Type*}
  [Fintype A] [Fintype B] [Fintype E] [Fintype I] [Fintype J]
  [DecidableEq A] [DecidableEq B] [DecidableEq E] [DecidableEq I] [DecidableEq J]

structure OneWayTest (A B : Type*) [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] where
  firstCount : ℕ
  secondCount : ℕ
  measurement : OneWayPOVM A B (Fin firstCount) (Fin secondCount)
  accepted : Finset (Fin firstCount × Fin secondCount)

namespace OneWayTest

def conditionalEffect (P : OneWayTest A B) (x : Fin P.firstCount) : QMatrix B :=
  ∑ y, if (x, y) ∈ P.accepted then P.measurement.bob x y else 0

theorem conditionalEffect_isEffect (P : OneWayTest A B) (x : Fin P.firstCount) :
    FlaggedStates.IsEffect (P.conditionalEffect x) := by
  have hpos : (P.conditionalEffect x).PosSemidef := by
    apply Matrix.posSemidef_sum
    intro y _
    split_ifs <;> first | exact P.measurement.bob_positive x y | exact Matrix.PosSemidef.zero
  refine ⟨hpos, ?_⟩
  have heq : 1 - P.conditionalEffect x =
      ∑ y, if (x, y) ∈ P.accepted then 0 else P.measurement.bob x y := by
    have hs : P.conditionalEffect x +
        (∑ y, if (x, y) ∈ P.accepted then 0 else P.measurement.bob x y) = 1 := by
      rw [conditionalEffect, ← Finset.sum_add_distrib]
      convert P.measurement.bob_complete x using 1
      apply Finset.sum_congr rfl
      intro y _
      split_ifs <;> simp only [add_zero, zero_add]
    rw [← hs]
    abel
  rw [heq]
  apply Matrix.posSemidef_sum
  intro y _
  split_ifs <;> first | exact P.measurement.bob_positive x y | exact Matrix.PosSemidef.zero

def receiverEffect (P : OneWayTest A B) : QMatrix (B × A) :=
  acceptedEffect P.conditionalEffect P.measurement.alice

theorem receiverEffect_isEffect (P : OneWayTest A B) :
    FlaggedStates.IsEffect P.receiverEffect :=
  acceptedEffect_isEffect _ _ P.conditionalEffect_isEffect P.measurement.alice_positive
    (by rw [P.measurement.alice_complete]; simpa using
      (Matrix.PosSemidef.zero : (0 : QMatrix A).PosSemidef))

def effectMatrix (P : OneWayTest A B) : QMatrix (A × B) :=
  P.receiverEffect.submatrix Prod.swap Prod.swap

theorem effectMatrix_isEffect (P : OneWayTest A B) :
    FlaggedStates.IsEffect P.effectMatrix := by
  refine ⟨P.receiverEffect_isEffect.1.submatrix _, ?_⟩
  have heq : 1 - P.effectMatrix =
      (1 - P.receiverEffect).submatrix Prod.swap Prod.swap := by
    change 1 - P.receiverEffect.submatrix (Equiv.prodComm A B) (Equiv.prodComm A B) =
      (1 - P.receiverEffect).submatrix (Equiv.prodComm A B) (Equiv.prodComm A B)
    simp only [Matrix.submatrix_sub, Pi.sub_apply, Matrix.submatrix_one_equiv]
  rw [heq]
  exact P.receiverEffect_isEffect.2.submatrix _

theorem effectMatrix_eq_fine_sum (P : OneWayTest A B) :
    P.effectMatrix = ∑ z ∈ P.accepted, P.measurement.alice z.1 ⊗ₖ P.measurement.bob z.1 z.2 := by
  ext i j
  simp only [effectMatrix, receiverEffect, acceptedEffect, conditionalEffect,
    Matrix.submatrix_apply, Matrix.sum_apply, Matrix.kroneckerMap_apply, Prod.swap]
  simp only [Finset.sum_mul, Matrix.ite_apply, Matrix.zero_apply, ite_mul, zero_mul]
  let f : Fin P.firstCount × Fin P.secondCount → ℂ := fun z =>
    P.measurement.alice z.1 i.1 j.1 * P.measurement.bob z.1 z.2 i.2 j.2
  have heq : (∑ x, ∑ y, if (x, y) ∈ P.accepted then f (x, y) else 0) =
      ∑ z ∈ P.accepted, f z := by
    rw [← Fintype.sum_prod_type (fun z : Fin P.firstCount × Fin P.secondCount =>
      if z ∈ P.accepted then f z else 0)]
    simp only [Finset.sum_ite_mem_eq]
  convert heq using 1
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  split_ifs <;> simp only [f, mul_comm]

theorem acceptance_eq_fine_probability (P : OneWayTest A B) (ρ : Density (A × B)) :
    (ρ.matrix * P.effectMatrix).trace.re =
      ∑ z ∈ P.accepted, oneWayOutcome P.measurement ρ.matrix z.1 z.2 := by
  rw [P.effectMatrix_eq_fine_sum]
  simp only [Matrix.mul_sum, Matrix.trace_sum, Complex.re_sum, oneWayOutcome]

end OneWayTest

def partySwapDensity (ρ : Density (A × B)) : Density (B × A) :=
  densityReindex (Equiv.prodComm A B) ρ

def groupedDensity (ρ : Density (A × (E × B))) : Density ((A × E) × B) :=
  densityReindex aeGrouping.symm ρ

def environmentDensity (ρ : Density (A × (E × B))) : Density (A × E) where
  matrix := partialTraceRight (regroupAE ρ.matrix)
  positive := partialTraceRight_positive (ρ.positive.submatrix _)
  trace_one := (partialTraceRight_trace _).trans
    ((aeGrouping.sum_comp (fun i => ρ.matrix i i)).trans ρ.trace_one)

def pairDensity (ρ : Density (A × (E × B))) : Density (A × B) :=
  abDensity (groupedDensity ρ)

def copySplit (n : ℕ) :
    (CopyIndex A n × CopyIndex (E × B) n) ≃
      (CopyIndex A n × (CopyIndex E n × CopyIndex B n)) :=
  Equiv.prodCongr (Equiv.refl _) (copyGrouping E B n)

def splitCopyDensity (ρ : Density (A × (E × B))) (n : ℕ) :
    Density (CopyIndex A n × (CopyIndex E n × CopyIndex B n)) :=
  densityReindex (copySplit n) (tensorCopies ρ n)

def groupedCopyDensity (ρ : Density (A × (E × B))) (n : ℕ) :
    Density ((CopyIndex A n × CopyIndex E n) × CopyIndex B n) :=
  groupedDensity (splitCopyDensity ρ n)

theorem groupedCopyDensity_succ_apply (ρ : Density (A × (E × B))) (n : ℕ)
    (a a' : CopyIndex A n) (e e' : CopyIndex E n) (b b' : CopyIndex B n)
    (i i' : A) (j j' : E) (k k' : B) :
    (groupedCopyDensity ρ (n + 1)).matrix (((a, i), (e, j)), (b, k))
      (((a', i'), (e', j')), (b', k')) =
      (groupedCopyDensity ρ n).matrix ((a, e), b) ((a', e'), b') *
        ρ.matrix (i, (j, k)) (i', (j', k')) := by
  change (tensorCopies ρ (n + 1)).matrix
      ((a, i), ((copyGrouping E B (n + 1)).symm ((e, j), (b, k))))
      ((a', i'), ((copyGrouping E B (n + 1)).symm ((e', j'), (b', k')))) = _
  change (tensorCopies ρ n).matrix (a, (copyGrouping E B n).symm (e, b))
      (a', (copyGrouping E B n).symm (e', b')) * ρ.matrix (i, (j, k)) (i', (j', k')) = _
  rfl

theorem groupedCopyDensity_zero_apply (ρ : Density (A × (E × B)))
    (a a' : CopyIndex A 0) (e e' : CopyIndex E 0) (b b' : CopyIndex B 0) :
    (groupedCopyDensity ρ 0).matrix ((a, e), b) ((a', e'), b') = 1 := by
  cases a
  cases a'
  cases e
  cases e'
  cases b
  cases b'
  rfl

theorem environmentDensity_tensorCopies (ρ : Density (A × (E × B))) (n : ℕ) :
    partialTraceRight (groupedCopyDensity ρ n).matrix =
      (tensorCopies (environmentDensity ρ) n).matrix := by
  induction n with
  | zero =>
      ext i j
      rcases i with ⟨a, e⟩
      rcases j with ⟨a', e'⟩
      cases a
      cases a'
      cases e
      cases e'
      simp only [partialTraceRight, QuantumProver.WernerEndpoint.partialTraceLeft, Fintype.sum_unique]
      rfl
  | succ n ih =>
      ext i j
      rcases i with ⟨⟨a, ai⟩, ⟨e, ei⟩⟩
      rcases j with ⟨⟨a', aj⟩, ⟨e', ej⟩⟩
      change (∑ bk : CopyIndex B n × B,
        (groupedCopyDensity ρ (n + 1)).matrix (((a, ai), (e, ei)), bk)
          (((a', aj), (e', ej)), bk)) = _
      simp only [Fintype.sum_prod_type, groupedCopyDensity_succ_apply,
        tensorCopies_succ_apply, environmentDensity, regroupAE, partialTraceRight,
        QuantumProver.WernerEndpoint.partialTraceLeft, Matrix.submatrix_apply, aeGrouping, Equiv.coe_fn_mk,
        ← Finset.mul_sum, ← Finset.sum_mul]
      change partialTraceRight (groupedCopyDensity ρ n).matrix (a, e) (a', e') *
        (environmentDensity ρ).matrix (ai, ei) (aj, ej) = _
      rw [ih]
      rfl

theorem pairDensity_tensorCopies (ρ : Density (A × (E × B))) (n : ℕ) :
    abMarginal (groupedCopyDensity ρ n).matrix =
      (tensorCopies (pairDensity ρ) n).matrix := by
  induction n with
  | zero =>
      ext i j
      rcases i with ⟨a, b⟩
      rcases j with ⟨a', b'⟩
      cases a
      cases a'
      cases b
      cases b'
      simp only [abMarginal_apply, Fintype.sum_unique]
      rfl
  | succ n ih =>
      ext i j
      rcases i with ⟨⟨a, ai⟩, ⟨b, bi⟩⟩
      rcases j with ⟨⟨a', aj⟩, ⟨b', bj⟩⟩
      change (∑ ej : CopyIndex E n × E,
        (groupedCopyDensity ρ (n + 1)).matrix (((a, ai), ej), (b, bi))
          (((a', aj), ej), (b', bj))) = _
      simp only [Fintype.sum_prod_type, groupedCopyDensity_succ_apply,
        tensorCopies_succ_apply, ← Finset.mul_sum, ← Finset.sum_mul]
      change abMarginal (groupedCopyDensity ρ n).matrix (a, b) (a', b') *
        (pairDensity ρ).matrix (ai, bi) (aj, bj) = _
      rw [ih]

theorem tensorCopies_partySwap (ρ : Density (A × B)) (n : ℕ) :
    (tensorCopies (partySwapDensity ρ) n).matrix =
      (tensorCopies ρ n).matrix.submatrix Prod.swap Prod.swap := by
  induction n with
  | zero =>
      ext i j
      rcases i with ⟨b, a⟩
      rcases j with ⟨b', a'⟩
      cases a
      cases a'
      cases b
      cases b'
      rfl
  | succ n ih =>
      ext i j
      rcases i with ⟨⟨b, bi⟩, ⟨a, ai⟩⟩
      rcases j with ⟨⟨b', bj⟩, ⟨a', aj⟩⟩
      change (tensorCopies (partySwapDensity ρ) n).matrix (b, a) (b', a') *
        ρ.matrix (ai, bi) (aj, bj) =
        (tensorCopies ρ n).matrix (a, b) (a', b') * ρ.matrix (ai, bi) (aj, bj)
      rw [ih]
      rfl

def reindexEffect (e : I ≃ J) (T : BinaryEffect I) : BinaryEffect J where
  matrix := Matrix.reindex e e T.matrix
  positive := T.positive.submatrix e.symm
  complement_positive := by
    have heq : 1 - Matrix.reindex e e T.matrix = Matrix.reindex e e (1 - T.matrix) := by
      simp only [Matrix.reindex_apply, Matrix.submatrix_sub, Pi.sub_apply,
        Matrix.submatrix_one_equiv]
    rw [heq]
    exact T.complement_positive.submatrix e.symm

theorem acceptance_reindex (e : I ≃ J) (ρ : Density I) (T : BinaryEffect I) :
    acceptance (densityReindex e ρ) (reindexEffect e T) = acceptance ρ T := by
  change ((ρ.matrix.submatrix e.symm e.symm) *
    (T.matrix.submatrix e.symm e.symm)).trace.re = (ρ.matrix * T.matrix).trace.re
  rw [Matrix.submatrix_mul_equiv]
  exact congrArg Complex.re (e.symm.sum_comp (fun i => (ρ.matrix * T.matrix) i i))

theorem isSeparable_partySwap {R : QMatrix (A × B)} (hR : IsSeparable R) :
    IsSeparable (R.submatrix Prod.swap Prod.swap) := by
  let L : QMatrix (A × B) →ₗ[ℝ] QMatrix (B × A) :=
    { toFun := fun X => X.submatrix Prod.swap Prod.swap
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  apply isSeparable_map_of_products L _ hR
  intro a b
  convert productDensity_separable b a using 1
  ext i j
  change a.matrix i.2 j.2 * b.matrix i.1 j.1 =
    b.matrix i.1 j.1 * a.matrix i.2 j.2
  exact mul_comm _ _

namespace OneWayTest

def toBinaryEffect (P : OneWayTest A B) : BinaryEffect (A × B) where
  matrix := P.effectMatrix
  positive := P.effectMatrix_isEffect.1
  complement_positive := P.effectMatrix_isEffect.2

def receiverBinaryEffect (P : OneWayTest A B) : BinaryEffect (B × A) where
  matrix := P.receiverEffect
  positive := P.receiverEffect_isEffect.1
  complement_positive := P.receiverEffect_isEffect.2

theorem acceptance_receiver (P : OneWayTest A B) (ρ : Density (B × A)) :
    acceptance (partySwapDensity ρ) P.toBinaryEffect =
      acceptance ρ P.receiverBinaryEffect :=
  acceptance_reindex (Equiv.prodComm B A) ρ P.receiverBinaryEffect

theorem worstSeparableBeta_receiver (P : OneWayTest A B) (ρ : Density (A × B)) :
    worstSeparableBeta P.receiverBinaryEffect = worstSeparableBeta P.toBinaryEffect := by
  apply le_antisymm
  · apply worstSeparableBeta_le (partySwapDensity ρ)
    intro σ
    rw [← P.acceptance_receiver σ.val]
    exact acceptance_le_worstSeparableBeta _
      ⟨partySwapDensity σ.val, isSeparable_partySwap σ.property⟩
  · apply worstSeparableBeta_le ρ
    intro σ
    have h := acceptance_le_worstSeparableBeta P.receiverBinaryEffect
      ⟨partySwapDensity σ.val, isSeparable_partySwap σ.property⟩
    rw [← P.acceptance_receiver (partySwapDensity σ.val)] at h
    convert h using 1
    rfl

end OneWayTest

def composeReceiverTest (Q : BinaryEffect (A × E)) (P : OneWayTest B A) :
    BinaryEffect ((A × E) × B) where
  matrix := composedEffect P.conditionalEffect P.measurement.alice Q.matrix
  positive := (composedEffect_isEffect _ _ P.conditionalEffect_isEffect
    P.measurement.alice_positive
    (by rw [P.measurement.alice_complete]; simpa using
      (Matrix.PosSemidef.zero : (0 : QMatrix B).PosSemidef)) Q.represented).1
  complement_positive := (composedEffect_isEffect _ _ P.conditionalEffect_isEffect
    P.measurement.alice_positive
    (by rw [P.measurement.alice_complete]; simpa using
      (Matrix.PosSemidef.zero : (0 : QMatrix B).PosSemidef)) Q.represented).2

def copyCompositionGrouping (n : ℕ) :
    ((CopyIndex A n × CopyIndex E n) × CopyIndex B n) ≃
      (CopyIndex A n × CopyIndex (E × B) n) :=
  aeGrouping.trans (copySplit n).symm

def composeCopyTest (n : ℕ)
    (Q : BinaryEffect (CopyIndex A n × CopyIndex E n))
    (P : OneWayTest (CopyIndex B n) (CopyIndex A n)) :
    BinaryEffect (CopyIndex A n × CopyIndex (E × B) n) :=
  reindexEffect (copyCompositionGrouping n) (composeReceiverTest Q P)

theorem groupedCopyDensity_reindex (ρ : Density (A × (E × B))) (n : ℕ) :
    densityReindex (copyCompositionGrouping n) (groupedCopyDensity ρ n) =
      tensorCopies ρ n := by
  apply density_ext
  ext i j
  change (tensorCopies ρ n).matrix
    ((copySplit n).symm ((copySplit n) i))
    ((copySplit n).symm ((copySplit n) j)) = _
  simp only [Equiv.symm_apply_apply]

theorem composeCopyTest_acceptance (ρ : Density (A × (E × B))) (n : ℕ)
    (Q : BinaryEffect (CopyIndex A n × CopyIndex E n))
    (P : OneWayTest (CopyIndex B n) (CopyIndex A n)) :
    acceptance (tensorCopies ρ n) (composeCopyTest n Q P) =
      (composedEffect P.conditionalEffect P.measurement.alice Q.matrix *
        (groupedCopyDensity ρ n).matrix).trace.re := by
  rw [← groupedCopyDensity_reindex ρ n]
  rw [composeCopyTest, acceptance_reindex]
  exact congrArg Complex.re (Matrix.trace_mul_comm _ _)

theorem composeCopyTest_separable_bound (ρ : Density (A × (E × B))) (n : ℕ)
    (Q : BinaryEffect (CopyIndex A n × CopyIndex E n))
    (P : OneWayTest (CopyIndex B n) (CopyIndex A n))
    (σ : SeparableDensity (CopyIndex A n) (CopyIndex (E × B) n)) :
    acceptance σ.val (composeCopyTest n Q P) ≤
      worstSeparableBeta Q * worstSeparableBeta P.toBinaryEffect := by
  let τ := densityReindex (copySplit n) σ.val
  have hτ : IsSeparable τ.matrix :=
    isSeparable_reindex (Equiv.refl _) (copyGrouping E B n) σ.property
  have heq : densityReindex (copyCompositionGrouping n) (groupedDensity τ) = σ.val := by
    apply density_ext
    ext i j
    change σ.val.matrix ((copySplit n).symm ((copySplit n) i))
      ((copySplit n).symm ((copySplit n) j)) = _
    simp only [Equiv.symm_apply_apply]
  rw [← heq, composeCopyTest, acceptance_reindex]
  change ((regroupAE τ.matrix) *
    composedEffect P.conditionalEffect P.measurement.alice Q.matrix).trace.re ≤ _
  rw [Matrix.trace_mul_comm]
  apply composedEffect_separable_bound _ _ (fun k => (P.conditionalEffect_isEffect k).1)
    P.measurement.alice_positive Q.matrix
    (worstSeparableBeta_bounds (tensorCopies (environmentDensity ρ) n) Q).1
  · intro η hη
    rw [Matrix.trace_mul_comm]
    exact acceptance_le_worstSeparableBeta Q ⟨η, hη⟩
  · intro η hη
    rw [Matrix.trace_mul_comm]
    have h := acceptance_le_worstSeparableBeta P.receiverBinaryEffect ⟨η, hη⟩
    rw [P.worstSeparableBeta_receiver (tensorCopies (partySwapDensity (pairDensity ρ)) n)] at h
    exact h
  · exact hτ

theorem composeCopyTest_worstBeta_bound (ρ : Density (A × (E × B))) (n : ℕ)
    (Q : BinaryEffect (CopyIndex A n × CopyIndex E n))
    (P : OneWayTest (CopyIndex B n) (CopyIndex A n)) :
    worstSeparableBeta (composeCopyTest n Q P) ≤
      worstSeparableBeta Q * worstSeparableBeta P.toBinaryEffect :=
  worstSeparableBeta_le (tensorCopies ρ n) _ (composeCopyTest_separable_bound ρ n Q P)

theorem composeCopyTest_typeI_tendsto (ρ : Density (A × (E × B)))
    (Q : ∀ n, BinaryEffect (CopyIndex A n × CopyIndex E n))
    (P : ∀ n, OneWayTest (CopyIndex B n) (CopyIndex A n))
    (hQ : Tendsto (fun n => acceptance (tensorCopies (environmentDensity ρ) n) (Q n))
      atTop (𝓝 1))
    (hP : Tendsto (fun n => acceptance
      (tensorCopies (partySwapDensity (pairDensity ρ)) n) (P n).toBinaryEffect)
      atTop (𝓝 1)) :
    Tendsto (fun n => acceptance (tensorCopies ρ n) (composeCopyTest n (Q n) (P n)))
      atTop (𝓝 1) := by
  have hQ' : Tendsto (fun n => ((Q n).matrix *
      partialTraceRight (groupedCopyDensity ρ n).matrix).trace.re) atTop (𝓝 1) := by
    convert hQ using 1
    funext n
    rw [environmentDensity_tensorCopies]
    exact congrArg Complex.re (Matrix.trace_mul_comm _ _)
  have hP' : Tendsto (fun n => (acceptedEffect (P n).conditionalEffect
      (P n).measurement.alice * abMarginal (groupedCopyDensity ρ n).matrix).trace.re)
      atTop (𝓝 1) := by
    have heq : ∀ n, acceptance
        (tensorCopies (partySwapDensity (pairDensity ρ)) n) (P n).toBinaryEffect =
        (acceptedEffect (P n).conditionalEffect (P n).measurement.alice *
          abMarginal (groupedCopyDensity ρ n).matrix).trace.re := by
      intro n
      have hg : acceptance (tensorCopies (partySwapDensity (pairDensity ρ)) n)
          (P n).toBinaryEffect =
          acceptance (partySwapDensity (tensorCopies (pairDensity ρ) n))
            (P n).toBinaryEffect := by
        unfold acceptance
        rw [tensorCopies_partySwap]
        rfl
      rw [hg, (P n).acceptance_receiver]
      change ((tensorCopies (pairDensity ρ) n).matrix *
        acceptedEffect (P n).conditionalEffect (P n).measurement.alice).trace.re = _
      rw [Matrix.trace_mul_comm, pairDensity_tensorCopies]
    simpa only [heq] using hP
  have h := composedEffect_typeI_tendsto
    (fun n => (P n).conditionalEffect) (fun n => (P n).measurement.alice)
    (fun n => (P n).conditionalEffect_isEffect)
    (fun n => (P n).measurement.alice_positive)
    (fun n => by rw [(P n).measurement.alice_complete]; simpa using
      (Matrix.PosSemidef.zero : (0 : QMatrix (CopyIndex B n)).PosSemidef))
    (fun n => (Q n).matrix) (fun n => (Q n).represented) (groupedCopyDensity ρ) hQ' hP'
  simpa only [composeCopyTest_acceptance] using h

theorem binaryEffect_ext (T U : BinaryEffect I) (h : T.matrix = U.matrix) : T = U := by
  cases T
  cases U
  cases h
  rfl

def AchievableOneWayRate (ρ : Density (A × B)) (r : EReal) : Prop :=
  ∃ P : (n : ℕ) → OneWayTest (CopyIndex A n) (CopyIndex B n),
    Tendsto (fun n => acceptance (tensorCopies ρ n) (P n).toBinaryEffect) atTop (𝓝 1) ∧
      r ≤ Filter.liminf (fun n => copyTestRateNat ρ (P n).toBinaryEffect) atTop

def oneWayTestingRateNat (ρ : Density (A × B)) : EReal :=
  sSup {r : EReal | AchievableOneWayRate ρ r}

theorem achievableOneWayRate_to_all (ρ : Density (A × B)) {r : EReal}
    (hr : AchievableOneWayRate ρ r) : AchievableAllRate ρ r := by
  obtain ⟨P, ha, hb⟩ := hr
  exact ⟨fun n => (P n).toBinaryEffect, ha, hb⟩

theorem oneWayTestingRateNat_le_all (ρ : Density (A × B)) :
    oneWayTestingRateNat ρ ≤ allEffectsTestingRateNat ρ := by
  apply sSup_le
  intro r hr
  exact le_sSup (achievableOneWayRate_to_all ρ hr)

def oneWayAcceptAll (A B : Type*) [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] : OneWayTest A B where
  firstCount := 1
  secondCount := 1
  measurement := {
    alice := fun _ => 1
    alice_positive := fun _ => Matrix.PosSemidef.one
    alice_complete := by simp
    bob := fun _ _ => 1
    bob_positive := fun _ _ => Matrix.PosSemidef.one
    bob_complete := fun _ => by simp }
  accepted := Finset.univ

@[simp] theorem oneWayAcceptAll_matrix :
    (oneWayAcceptAll A B).effectMatrix = 1 := by
  rw [OneWayTest.effectMatrix_eq_fine_sum]
  simp only [oneWayAcceptAll, Finset.sum_const,
    Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Nat.mul_one,
    one_smul, Matrix.one_kronecker_one]

theorem achievableOneWayRate_zero (ρ : Density (A × B)) :
    AchievableOneWayRate ρ 0 := by
  let P : ∀ n, OneWayTest (CopyIndex A n) (CopyIndex B n) :=
    fun n => oneWayAcceptAll _ _
  have heq : ∀ n, (P n).toBinaryEffect = acceptAllEffect _ := by
    intro n
    apply binaryEffect_ext
    exact oneWayAcceptAll_matrix
  refine ⟨P, ?_, ?_⟩
  · simpa only [heq, acceptance_acceptAll] using
      (tendsto_const_nhds (x := (1 : ℝ)) : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1))
  · simp only [heq, copyTestRateNat_acceptAll]
    simp

theorem oneWayTestingRateNat_nonneg (ρ : Density (A × B)) :
    0 ≤ oneWayTestingRateNat ρ := le_sSup (achievableOneWayRate_zero ρ)

theorem oneWayTestingRateNat_ne_top (ρ : Density (A × B)) :
    oneWayTestingRateNat ρ ≠ ⊤ :=
  ne_of_lt ((oneWayTestingRateNat_le_all ρ).trans_lt
    (lt_top_iff_ne_top.mpr (allEffectsTestingRateNat_ne_top ρ)))

theorem oneWayTestingRateNat_ne_bot (ρ : Density (A × B)) :
    oneWayTestingRateNat ρ ≠ ⊥ :=
  ne_of_gt ((EReal.bot_lt_coe 0).trans_le (oneWayTestingRateNat_nonneg ρ))

def oneWayTestingRateReal (ρ : Density (A × B)) : ℝ :=
  (oneWayTestingRateNat ρ).toReal

theorem coe_oneWayTestingRateReal (ρ : Density (A × B)) :
    (oneWayTestingRateReal ρ : EReal) = oneWayTestingRateNat ρ :=
  EReal.coe_toReal (oneWayTestingRateNat_ne_top ρ) (oneWayTestingRateNat_ne_bot ρ)

theorem achievableOneWayRate_of_uniform_separable_bound (ρ : Density (A × B)) (r : ℝ)
    (P : ∀ n, OneWayTest (CopyIndex A n) (CopyIndex B n))
    (ha : Tendsto (fun n => acceptance (tensorCopies ρ n) (P n).toBinaryEffect)
      atTop (𝓝 1))
    (hb : ∀ n, 0 < n → ∀ σ : SeparableDensity (CopyIndex A n) (CopyIndex B n),
      acceptance σ.val (P n).toBinaryEffect ≤ Real.exp (-(n : ℝ) * r)) :
    AchievableOneWayRate ρ (r : EReal) := by
  refine ⟨P, ha, ?_⟩
  apply Filter.le_liminf_of_le (h := ?_)
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact copyTestRateNat_ge_of_beta_bound ρ (by omega) (P n).toBinaryEffect
    (worstSeparableBeta_le (tensorCopies ρ n) _ (hb n (by omega)))

theorem negLogNat_nonneg_of_le_one {q : ℝ} (hq : q ≤ 1) : 0 ≤ negLogNat q := by
  have h := negLogNat_antitone hq
  have heq : negLogNat 1 = 0 := by rw [negLogNat_of_pos zero_lt_one]; simp
  rwa [heq] at h

theorem negLogNat_mul {p q : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    negLogNat (p * q) = negLogNat p + negLogNat q := by
  by_cases hp : p = 0
  · rw [hp, zero_mul, negLogNat_zero]
    exact (EReal.top_add_of_ne_bot
      (ne_of_gt ((EReal.bot_lt_coe 0).trans_le (negLogNat_nonneg_of_le_one hq1)))).symm
  · by_cases hq : q = 0
    · rw [hq, mul_zero, negLogNat_zero]
      exact (EReal.add_top_of_ne_bot
        (ne_of_gt ((EReal.bot_lt_coe 0).trans_le (negLogNat_nonneg_of_le_one hp1)))).symm
    · have hp' : 0 < p := lt_of_le_of_ne hp0 (Ne.symm hp)
      have hq' : 0 < q := lt_of_le_of_ne hq0 (Ne.symm hq)
      rw [negLogNat_of_pos (mul_pos hp' hq'), negLogNat_of_pos hp',
        negLogNat_of_pos hq', Real.log_mul hp hq]
      rw [neg_add, EReal.coe_add]

theorem composeCopyTest_rate_bound (ρ : Density (A × (E × B))) (n : ℕ)
    (Q : BinaryEffect (CopyIndex A n × CopyIndex E n))
    (P : OneWayTest (CopyIndex B n) (CopyIndex A n)) :
    copyTestRateNat (environmentDensity ρ) Q +
      copyTestRateNat (partySwapDensity (pairDensity ρ)) P.toBinaryEffect ≤
      copyTestRateNat ρ (composeCopyTest n Q P) := by
  by_cases hn : n = 0
  · simp only [copyTestRateNat, hn, ite_true, zero_add]
    exact le_rfl
  · have hQ := worstSeparableBeta_bounds (tensorCopies (environmentDensity ρ) n) Q
    have hP := worstSeparableBeta_bounds (tensorCopies (partySwapDensity (pairDensity ρ)) n)
      P.toBinaryEffect
    rw [copyTestRateNat, copyTestRateNat, copyTestRateNat,
      ite_eq_right hn, ite_eq_right hn, ite_eq_right hn,
      ← EReal.right_distrib_of_nonneg (negLogNat_nonneg_of_le_one hQ.2)
        (negLogNat_nonneg_of_le_one hP.2), ← negLogNat_mul hQ.1 hQ.2 hP.1 hP.2]
    exact mul_le_mul_of_nonneg_right
      (negLogNat_antitone (composeCopyTest_worstBeta_bound ρ n Q P))
      (EReal.coe_nonneg.mpr (one_div_nonneg.mpr (Nat.cast_nonneg n)))

theorem achievableAllRate_receiver_compose (ρ : Density (A × (E × B)))
    {rQ rP : EReal}
    (hQ : AchievableAllRate (environmentDensity ρ) rQ)
    (hP : AchievableOneWayRate (partySwapDensity (pairDensity ρ)) rP) :
    AchievableAllRate ρ (rQ + rP) := by
  obtain ⟨Q, hQa, hQr⟩ := hQ
  obtain ⟨P, hPa, hPr⟩ := hP
  refine ⟨fun n => composeCopyTest n (Q n) (P n),
    composeCopyTest_typeI_tendsto ρ Q P hQa hPa, ?_⟩
  apply (add_le_add hQr hPr).trans
  apply EReal.le_liminf_add.trans
  exact Filter.liminf_le_liminf (Filter.Eventually.of_forall
    (fun n => composeCopyTest_rate_bound ρ n (Q n) (P n)))

theorem allEffectsTestingRateNat_receiver_ge_sum (ρ : Density (A × (E × B))) :
    allEffectsTestingRateNat (environmentDensity ρ) +
      oneWayTestingRateNat (partySwapDensity (pairDensity ρ)) ≤
      allEffectsTestingRateNat ρ := by
  apply EReal.add_le_of_forall_lt
  intro rQ hQ rP hP
  obtain ⟨q, hqa, hq⟩ := lt_sSup_iff.mp hQ
  obtain ⟨p, hpa, hp⟩ := lt_sSup_iff.mp hP
  exact (add_le_add hq.le hp.le).trans
    (le_sSup (achievableAllRate_receiver_compose ρ hqa hpa))

theorem allEffectsTestingRateReal_receiver_ge_sum (ρ : Density (A × (E × B))) :
    allEffectsTestingRateReal (environmentDensity ρ) +
      oneWayTestingRateReal (partySwapDensity (pairDensity ρ)) ≤
      allEffectsTestingRateReal ρ := by
  have h := allEffectsTestingRateNat_receiver_ge_sum ρ
  rw [← coe_allEffectsTestingRateReal, ← coe_oneWayTestingRateReal,
    ← coe_allEffectsTestingRateReal, ← EReal.coe_add] at h
  exact EReal.coe_le_coe_iff.mp h

end QuantumProver.DepolarizingSquashedEntanglement.BCYAsymptoticComposition

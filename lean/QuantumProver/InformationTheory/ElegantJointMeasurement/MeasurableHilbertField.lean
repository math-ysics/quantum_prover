import Mathlib
import QuantumProver.InformationTheory.ElegantJointMeasurement.SeparableHilbertEmbedding
import QuantumProver.LinearAlgebra.CountableGramSchmidt
import QuantumProver.LinearAlgebra.CountableFrameProjection

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section

open MeasureTheory Set Function
open scoped BigOperators ComplexConjugate

namespace QuantumProver.ElegantJointMeasurement.MeasurableHilbertField

universe u v
variable {Z : Type u} [MeasurableSpace Z] (E : Z → Type v)
  [∀ z, NormedAddCommGroup (E z)] [∀ z, InnerProductSpace ℂ (E z)]
  [∀ z, CompleteSpace (E z)]

structure FundamentalFamily where
  vector : (z : Z) → ℕ → E z
  pairingMeasurable : ∀ i j, Measurable (fun z => inner ℂ (vector z i) (vector z j))
  dense : ∀ z, (Submodule.span ℂ (Set.range (vector z))).topologicalClosure = ⊤

namespace FundamentalFamily
variable {E}

def IsMeasurableSection (F : FundamentalFamily E) (s : (z : Z) → E z) : Prop :=
  ∀ i, Measurable (fun z => inner ℂ (F.vector z i) (s z))

theorem fundamental_measurableSection (F : FundamentalFamily E) (j : ℕ) :
    F.IsMeasurableSection (fun z => F.vector z j) := fun i => F.pairingMeasurable i j

theorem zero_measurableSection (F : FundamentalFamily E) :
    F.IsMeasurableSection (fun z => (0 : E z)) := by
  intro i
  simpa only [inner_zero_right] using (measurable_const : Measurable (fun _ : Z => (0 : ℂ)))

theorem add_measurableSection (F : FundamentalFamily E) (s t : (z : Z) → E z)
    (hs : F.IsMeasurableSection s) (ht : F.IsMeasurableSection t) :
    F.IsMeasurableSection (fun z => s z + t z) := by
  intro i
  have heq : (fun z => inner ℂ (F.vector z i) (s z + t z)) =
      ((fun z => inner ℂ (F.vector z i) (s z)) +
        fun z => inner ℂ (F.vector z i) (t z)) := by
    funext z
    simp only [inner_add_right, Pi.add_apply]
  rw [heq]
  exact (hs i).add (ht i)

theorem smul_measurableSection (F : FundamentalFamily E) (c : Z → ℂ)
    (hc : Measurable c) (s : (z : Z) → E z) (hs : F.IsMeasurableSection s) :
    F.IsMeasurableSection (fun z => c z • s z) := by
  intro i
  have heq : (fun z => inner ℂ (F.vector z i) (c z • s z)) =
      c * (fun z => inner ℂ (F.vector z i) (s z)) := by
    funext z
    simp only [inner_smul_right, Pi.mul_apply]
  rw [heq]
  exact hc.mul (hs i)

def finiteCombination (F : FundamentalFamily E) (s : Finset ℕ) (c : ℕ → Z → ℂ)
    (z : Z) : E z := ∑ i ∈ s, c i z • F.vector z i

theorem finiteCombination_measurableSection (F : FundamentalFamily E)
    (s : Finset ℕ) (c : ℕ → Z → ℂ) (hc : ∀ i ∈ s, Measurable (c i)) :
    F.IsMeasurableSection (F.finiteCombination s c) := by
  intro j
  simp only [finiteCombination, inner_sum, inner_smul_right]
  exact Finset.measurable_sum s (fun i hi => (hc i hi).mul (F.pairingMeasurable j i))

theorem measurable_inner_finiteCombination (F : FundamentalFamily E)
    (s t : Finset ℕ) (c d : ℕ → Z → ℂ)
    (hc : ∀ i ∈ s, Measurable (c i)) (hd : ∀ j ∈ t, Measurable (d j)) :
    Measurable (fun z => inner ℂ (F.finiteCombination s c z) (F.finiteCombination t d z)) := by
  simp only [finiteCombination, sum_inner, inner_sum, inner_smul_left, inner_smul_right]
  apply Finset.measurable_sum t
  intro j hj
  apply (hd j hj).mul
  apply Finset.measurable_sum s
  intro i hi
  exact (continuous_star.measurable.comp (hc i hi)).mul (F.pairingMeasurable i j)

theorem measurable_norm_of_inner_self (s : (z : Z) → E z)
    (hs : Measurable (fun z => inner ℂ (s z) (s z))) :
    Measurable (fun z => ‖s z‖) := by
  have hm := (Complex.continuous_re.measurable.comp hs).sqrt
  convert hm using 1
  funext z
  exact norm_eq_sqrt_re_inner (𝕜 := ℂ) (s z)

theorem measurable_norm_finiteCombination (F : FundamentalFamily E)
    (s : Finset ℕ) (c : ℕ → Z → ℂ) (hc : ∀ i ∈ s, Measurable (c i)) :
    Measurable (fun z => ‖F.finiteCombination s c z‖) :=
  measurable_norm_of_inner_self _ (F.measurable_inner_finiteCombination s s c c hc hc)

theorem measurable_norm_fundamental (F : FundamentalFamily E) (i : ℕ) :
    Measurable (fun z => ‖F.vector z i‖) :=
  measurable_norm_of_inner_self _ (F.pairingMeasurable i i)

def residual (F : FundamentalFamily E) (n : ℕ) (z : Z) : E z :=
  QuantumProver.CountableGramSchmidt.residual (F.vector z) n

def frame (F : FundamentalFamily E) (n : ℕ) (z : Z) : E z :=
  QuantumProver.CountableGramSchmidt.frame (F.vector z) n

theorem residual_formula (F : FundamentalFamily E) (z : Z) (n : ℕ) :
    F.residual n z = F.vector z n - ∑ i ∈ Finset.Iio n,
      (inner ℂ (F.residual i z) (F.vector z n) / (‖F.residual i z‖ : ℂ) ^ 2) •
        F.residual i z := by
  exact eq_sub_iff_add_eq.mpr
    (QuantumProver.CountableGramSchmidt.residual_decomposition (F.vector z) n).symm

theorem residual_inner_self (F : FundamentalFamily E) (z : Z) (n : ℕ) :
    inner ℂ (F.residual n z) (F.residual n z) =
      inner ℂ (F.residual n z) (F.vector z n) := by
  classical
  have hz : inner ℂ (F.residual n z) (∑ i ∈ Finset.Iio n,
      (inner ℂ (F.residual i z) (F.vector z n) / (‖F.residual i z‖ : ℂ) ^ 2) •
        F.residual i z) = 0 := by
    rw [inner_sum]
    apply Finset.sum_eq_zero
    intro i hi
    rw [inner_smul_right]
    have hni : n ≠ i := (Finset.mem_Iio.mp hi).ne'
    have horth : inner ℂ (F.residual n z) (F.residual i z) = 0 :=
      InnerProductSpace.gramSchmidt_orthogonal ℂ (F.vector z) hni
    rw [horth, mul_zero]
  have hd := QuantumProver.CountableGramSchmidt.residual_decomposition (F.vector z) n
  calc
    inner ℂ (F.residual n z) (F.residual n z) =
        inner ℂ (F.residual n z) (F.residual n z + ∑ i ∈ Finset.Iio n,
          (inner ℂ (F.residual i z) (F.vector z n) / (‖F.residual i z‖ : ℂ) ^ 2) •
            F.residual i z) := by rw [inner_add_right, hz, add_zero]
    _ = inner ℂ (F.residual n z) (F.vector z n) :=
      congrArg (fun x => inner ℂ (F.residual n z) x) hd.symm

theorem measurable_residual_inner_section (F : FundamentalFamily E) (n : ℕ)
    (s : (z : Z) → E z) (hs : F.IsMeasurableSection s) :
    Measurable (fun z => inner ℂ (F.residual n z) (s z)) := by
  classical
  suffices hall : ∀ n, ∀ s : (z : Z) → E z, F.IsMeasurableSection s →
      Measurable (fun z => inner ℂ (F.residual n z) (s z)) from hall n s hs
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro s hs
    have hn : ∀ i ∈ Finset.Iio n, Measurable (fun z => ‖F.residual i z‖) := by
      intro i hi
      apply measurable_norm_of_inner_self
      have heq : (fun z => inner ℂ (F.residual i z) (F.residual i z)) =
          (fun z => inner ℂ (F.residual i z) (F.vector z i)) :=
        funext (fun z => F.residual_inner_self z i)
      rw [heq]
      exact ih i (Finset.mem_Iio.mp hi) _ (F.fundamental_measurableSection i)
    have ha : ∀ i ∈ Finset.Iio n, Measurable (fun z =>
        inner ℂ (F.residual i z) (F.vector z n) / (‖F.residual i z‖ : ℂ) ^ 2) := by
      intro i hi
      exact (ih i (Finset.mem_Iio.mp hi) _ (F.fundamental_measurableSection n)).div
        ((Complex.continuous_ofReal.measurable.comp (hn i hi)).pow_const 2)
    have heq : (fun z => inner ℂ (F.residual n z) (s z)) =
        (fun z => inner ℂ (F.vector z n) (s z) - ∑ i ∈ Finset.Iio n,
          star (inner ℂ (F.residual i z) (F.vector z n) /
            (‖F.residual i z‖ : ℂ) ^ 2) * inner ℂ (F.residual i z) (s z)) := by
      funext z
      rw [F.residual_formula]
      simp only [inner_sub_left, sum_inner, inner_smul_left, starRingEnd_apply]
    rw [heq]
    exact (hs n).sub (Finset.measurable_sum (Finset.Iio n) (fun i hi =>
      (continuous_star.measurable.comp (ha i hi)).mul
        (ih i (Finset.mem_Iio.mp hi) s hs)))

theorem measurable_norm_residual (F : FundamentalFamily E) (n : ℕ) :
    Measurable (fun z => ‖F.residual n z‖) := by
  apply measurable_norm_of_inner_self
  have heq : (fun z => inner ℂ (F.residual n z) (F.residual n z)) =
      (fun z => inner ℂ (F.residual n z) (F.vector z n)) :=
    funext (fun z => F.residual_inner_self z n)
  rw [heq]
  exact F.measurable_residual_inner_section n _ (F.fundamental_measurableSection n)

theorem frame_formula (F : FundamentalFamily E) (n : ℕ) (z : Z) :
    F.frame n z = (‖F.residual n z‖ : ℂ)⁻¹ • F.residual n z := rfl

theorem measurable_frame_inner_section (F : FundamentalFamily E) (n : ℕ)
    (s : (z : Z) → E z) (hs : F.IsMeasurableSection s) :
    Measurable (fun z => inner ℂ (F.frame n z) (s z)) := by
  have heq : (fun z => inner ℂ (F.frame n z) (s z)) =
      (fun z => star ((‖F.residual n z‖ : ℂ)⁻¹) *
        inner ℂ (F.residual n z) (s z)) := by
    funext z
    rw [F.frame_formula]
    simp only [inner_smul_left, starRingEnd_apply]
  rw [heq]
  exact (continuous_star.measurable.comp
    (Complex.continuous_ofReal.measurable.comp (F.measurable_norm_residual n)).inv).mul
      (F.measurable_residual_inner_section n s hs)

theorem frame_measurableSection (F : FundamentalFamily E) (n : ℕ) :
    F.IsMeasurableSection (F.frame n) := by
  intro i
  have heq : (fun z => inner ℂ (F.vector z i) (F.frame n z)) =
      (fun z => star (inner ℂ (F.frame n z) (F.vector z i))) := by
    funext z
    exact (inner_conj_symm _ _).symm
  rw [heq]
  exact continuous_star.measurable.comp
    (F.measurable_frame_inner_section n _ (F.fundamental_measurableSection i))

def embedding (F : FundamentalFamily E) (z : Z) :
    E z →ₗᵢ[ℂ] QuantumProver.ElegantJointMeasurement.SeparableHilbertEmbedding.CommonHilbert :=
  QuantumProver.CountableGramSchmidt.coordinateEmbedding (F.vector z) (F.dense z)

theorem embedding_apply (F : FundamentalFamily E) (z : Z) (x : E z) (n : ℕ) :
    F.embedding z x n = inner ℂ (F.frame n z) x := rfl

theorem measurable_embedding_coordinate (F : FundamentalFamily E)
    (s : (z : Z) → E z) (hs : F.IsMeasurableSection s) (n : ℕ) :
    Measurable (fun z => F.embedding z (s z) n) :=
  F.measurable_frame_inner_section n s hs

theorem stronglyMeasurable_embedding_section (F : FundamentalFamily E)
    (s : (z : Z) → E z) (hs : F.IsMeasurableSection s) :
    StronglyMeasurable (fun z => F.embedding z (s z)) := by
  let b := QuantumProver.ElegantJointMeasurement.SeparableHilbertEmbedding.commonBasis
  have hm : ∀ i, Measurable (fun z => b.repr (F.embedding z (s z)) i) := by
    intro i
    change Measurable (fun z => F.embedding z (s z) i)
    exact F.measurable_embedding_coordinate s hs i
  apply stronglyMeasurable_of_tendsto (Filter.atTop : Filter ℕ)
    (fun n => Finset.stronglyMeasurable_fun_sum (Finset.range n)
      (fun i hi => (hm i).stronglyMeasurable.smul_const (b i)))
  apply tendsto_pi_nhds.mpr
  intro z
  exact (b.hasSum_repr (F.embedding z (s z))).tendsto_sum_nat

theorem measurable_norm_section (F : FundamentalFamily E)
    (s : (z : Z) → E z) (hs : F.IsMeasurableSection s) :
    Measurable (fun z => ‖s z‖) := by
  have hm := (F.stronglyMeasurable_embedding_section s hs).norm.measurable
  simpa only [LinearIsometry.norm_map] using hm

end FundamentalFamily
end QuantumProver.ElegantJointMeasurement.MeasurableHilbertField

namespace QuantumProver.ElegantJointMeasurement.MeasurableHilbertField
namespace FundamentalFamily

open scoped Classical

universe u v
variable {Z : Type u} [MeasurableSpace Z] {E : Z → Type v}
  [∀ z, NormedAddCommGroup (E z)] [∀ z, InnerProductSpace ℂ (E z)]
  [∀ z, CompleteSpace (E z)]

open QuantumProver.ElegantJointMeasurement.SeparableHilbertEmbedding

theorem stronglyMeasurable_common_of_coordinates (u : Z → CommonHilbert)
    (hu : ∀ n, Measurable (fun z => u z n)) : StronglyMeasurable u := by
  let b := commonBasis
  have hm : ∀ i, Measurable (fun z => b.repr (u z) i) := hu
  apply stronglyMeasurable_of_tendsto (Filter.atTop : Filter ℕ)
    (fun n => Finset.stronglyMeasurable_fun_sum (Finset.range n)
      (fun i hi => (hm i).stronglyMeasurable.smul_const (b i)))
  apply tendsto_pi_nhds.mpr
  intro z
  exact (b.hasSum_repr (u z)).tendsto_sum_nat

theorem measurableSet_frame_nonzero (F : FundamentalFamily E) (n : ℕ) :
    MeasurableSet {z | F.frame n z ≠ 0} := by
  have hz := measurableSet_eq_fun
    (F.measurable_norm_section (F.frame n) (F.frame_measurableSection n))
    (measurable_const : Measurable (fun _ : Z => (0 : ℝ)))
  simpa only [Set.compl_ofPred, norm_eq_zero] using hz.compl

def rangeProjection (F : FundamentalFamily E) (z : Z) : CommonHilbert →L[ℂ] CommonHilbert :=
  QuantumProver.CountableFrameProjection.rangeProjection (F.vector z) (F.dense z)

theorem rangeProjection_coordinate (F : FundamentalFamily E) (z : Z)
    (y : CommonHilbert) (n : ℕ) :
    F.rangeProjection z y n = if F.frame n z ≠ 0 then y n else 0 :=
  QuantumProver.CountableFrameProjection.rangeProjection_apply_coordinate
    (F.vector z) (F.dense z) y n

theorem stronglyMeasurable_rangeProjection_apply (F : FundamentalFamily E)
    (u : Z → CommonHilbert) (hu : StronglyMeasurable u) :
    StronglyMeasurable (fun z => F.rangeProjection z (u z)) := by
  classical
  apply stronglyMeasurable_common_of_coordinates
  intro n
  have hm : Measurable (fun z => u z n) :=
    ((lp.evalCLM ℂ (fun _ : ℕ => ℂ) 2 n).continuous.comp_stronglyMeasurable hu).measurable
  have heq : (fun z => F.rangeProjection z (u z) n) =
      (fun z => if F.frame n z ≠ 0 then u z n else 0) :=
    funext (fun z => F.rangeProjection_coordinate z (u z) n)
  rw [heq]
  exact Measurable.ite (F.measurableSet_frame_nonzero n) hm measurable_const

def NonzeroFiber (F : FundamentalFamily E) (z : Z) : Prop := ∃ n, F.frame n z ≠ 0

theorem measurableSet_nonzeroFiber (F : FundamentalFamily E) :
    MeasurableSet {z | F.NonzeroFiber z} := by
  have heq : {z | F.NonzeroFiber z} = ⋃ n, {z | F.frame n z ≠ 0} := by
    ext z
    simp only [NonzeroFiber, Set.mem_setOf_eq, Set.mem_iUnion]
  rw [heq]
  exact MeasurableSet.iUnion (fun n => F.measurableSet_frame_nonzero n)

theorem zeroFiber_iff (F : FundamentalFamily E) (z : Z) :
    ¬ F.NonzeroFiber z ↔ ∀ x : E z, x = 0 := by
  constructor
  · intro h x
    apply QuantumProver.CountableGramSchmidt.coefficients_complete (F.vector z) (F.dense z) x
    intro n
    have hz : F.frame n z = 0 := by
      by_contra hn
      exact h ⟨n, hn⟩
    change inner ℂ (F.frame n z) x = 0
    rw [hz, inner_zero_left]
  · intro h ⟨n, hn⟩
    exact hn (h (F.frame n z))

private def UnitCandidate (F : FundamentalFamily E) (z : Z) (n : ℕ) : Prop :=
  F.frame n z ≠ 0 ∨ (n = 0 ∧ ¬ F.NonzeroFiber z)

private theorem unitCandidate_exists (F : FundamentalFamily E) (z : Z) :
    ∃ n, F.UnitCandidate z n := by
  classical
  by_cases h : F.NonzeroFiber z
  · obtain ⟨n, hn⟩ := h
    exact ⟨n, Or.inl hn⟩
  · exact ⟨0, Or.inr ⟨rfl, h⟩⟩

def firstUnitIndex (F : FundamentalFamily E) (z : Z) : ℕ :=
  Nat.find (F.unitCandidate_exists z)

theorem measurable_firstUnitIndex (F : FundamentalFamily E) :
    Measurable F.firstUnitIndex := by
  classical
  apply measurable_find (F.unitCandidate_exists)
  intro n
  exact (F.measurableSet_frame_nonzero n).union
    ((MeasurableSet.const (n = 0)).inter F.measurableSet_nonzeroFiber.compl)

theorem frame_firstUnitIndex_ne_zero (F : FundamentalFamily E) (z : Z)
    (hz : F.NonzeroFiber z) : F.frame (F.firstUnitIndex z) z ≠ 0 := by
  have h := Nat.find_spec (F.unitCandidate_exists z)
  rcases h with hn | ⟨_, hzero⟩
  · exact hn
  · exact (hzero hz).elim

def unitSection (F : FundamentalFamily E) (z : Z) : E z :=
  if F.NonzeroFiber z then F.frame (F.firstUnitIndex z) z else 0

theorem unitSection_norm (F : FundamentalFamily E) (z : Z) (hz : F.NonzeroFiber z) :
    ‖F.unitSection z‖ = 1 := by
  classical
  rw [unitSection, ite_eq_left hz]
  have h := QuantumProver.CountableGramSchmidt.frame_norm_zero_or_one
    (F.vector z) (F.firstUnitIndex z)
  exact h.resolve_left (norm_ne_zero_iff.mpr (F.frame_firstUnitIndex_ne_zero z hz))

theorem unitSection_zero (F : FundamentalFamily E) (z : Z) (hz : ¬ F.NonzeroFiber z) :
    F.unitSection z = 0 := by
  classical
  rw [unitSection, ite_eq_right hz]

theorem unitSection_measurableSection (F : FundamentalFamily E) :
    F.IsMeasurableSection F.unitSection := by
  classical
  intro i
  have hm : Measurable (fun p : Z × ℕ => inner ℂ (F.vector p.1 i) (F.frame p.2 p.1)) :=
    measurable_from_prod_countable_left (fun n => F.frame_measurableSection n i)
  have hselected : Measurable (fun z =>
      inner ℂ (F.vector z i) (F.frame (F.firstUnitIndex z) z)) :=
    hm.comp (measurable_id.prodMk F.measurable_firstUnitIndex)
  have heq : (fun z => inner ℂ (F.vector z i) (F.unitSection z)) =
      (fun z => if F.NonzeroFiber z then
        inner ℂ (F.vector z i) (F.frame (F.firstUnitIndex z) z) else 0) := by
    funext z
    by_cases hz : F.NonzeroFiber z <;> simp only [unitSection, hz, ite_true, ite_false,
      inner_zero_right]
  rw [heq]
  exact Measurable.ite F.measurableSet_nonzeroFiber hselected measurable_const

theorem stronglyMeasurable_embedding_unitSection (F : FundamentalFamily E) :
    StronglyMeasurable (fun z => F.embedding z (F.unitSection z)) :=
  F.stronglyMeasurable_embedding_section _ F.unitSection_measurableSection

end FundamentalFamily
end QuantumProver.ElegantJointMeasurement.MeasurableHilbertField

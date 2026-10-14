import QuantumProver.InformationTheory.ElegantJointMeasurement.ResourceCode
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

open scoped BigOperators ComplexConjugate
open Set InnerProductSpace

namespace QuantumProver.ElegantJointMeasurement.Augmented

noncomputable section

set_option maxHeartbeats 400000

section CompactHull

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
  [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] [FiniteDimensional ℝ V]

def combinationMap (n : ℕ) (p : (Fin n → ℝ) × (Fin n → V)) : V :=
  ∑ i, p.1 i • p.2 i

def combinations (n : ℕ) (s : Set V) : Set V :=
  combinationMap n '' (stdSimplex ℝ (Fin n) ×ˢ {z : Fin n → V | ∀ i, z i ∈ s})

theorem continuous_combinationMap (n : ℕ) :
    Continuous (combinationMap n : (Fin n → ℝ) × (Fin n → V) → V) := by
  unfold combinationMap
  fun_prop

theorem isCompact_combinations (n : ℕ) {s : Set V} (hs : IsCompact s) :
    IsCompact (combinations n s) :=
  ((isCompact_stdSimplex ℝ (Fin n)).prod (isCompact_pi_infinite fun _ => hs)).image
    (continuous_combinationMap n)

theorem mem_convexHull_bounded_combination {s : Set V} {x : V}
    (hx : x ∈ convexHull ℝ s) :
    ∃ n ≤ Module.finrank ℝ V + 1, x ∈ combinations n s := by
  classical
  rw [convexHull_eq_union] at hx
  simp only [Set.mem_iUnion, exists_prop] at hx
  obtain ⟨t, ht, hind, hx⟩ := hx
  have hcard : t.card ≤ Module.finrank ℝ V + 1 := by
    have h := hind.card_le_finrank_succ
    simpa using h.trans (Nat.add_le_add_right (Submodule.finrank_le _) 1)
  rw [Finset.convexHull_eq] at hx
  obtain ⟨w, hw, hsum, hx⟩ := hx
  let e : t ≃ Fin t.card := by simpa only [Fintype.card_coe] using Fintype.equivFin t
  let W : Fin t.card → ℝ := fun i => w (e.symm i)
  let Z : Fin t.card → V := fun i => (e.symm i : V)
  have hsum' : ∑ i, W i = 1 := by
    calc
      ∑ i, W i = ∑ i : t, w (i : V) := by
        simpa [W] using (e.symm.sum_comp (fun i : t => w (i : V)))
      _ = ∑ i ∈ t, w i := by simp only [Finset.univ_eq_attach, Finset.sum_attach]
      _ = 1 := hsum
  have heq : combinationMap t.card (W, Z) = x := by
    unfold combinationMap
    calc
      ∑ i, W i • Z i = ∑ i : t, w (i : V) • (i : V) := by
        simpa [W, Z] using (e.symm.sum_comp (fun i : t => w (i : V) • (i : V)))
      _ = ∑ i ∈ t, w i • i := by
        rw [Finset.univ_eq_attach]
        exact Finset.sum_attach t (fun i : V => w i • i)
      _ = t.centerMass w id := by rw [t.centerMass_eq_of_sum_1 id hsum]; rfl
      _ = x := hx
  refine ⟨t.card, hcard, (W, Z), ?_, heq⟩
  exact ⟨⟨fun i => hw _ (e.symm i).property, hsum'⟩,
    fun i => ht (e.symm i).property⟩

theorem combinations_subset_convexHull (n : ℕ) (s : Set V) :
    combinations n s ⊆ convexHull ℝ s := by
  rintro x ⟨⟨w, z⟩, ⟨hw, hz⟩, rfl⟩
  exact mem_convexHull_of_exists_fintype w z hw.1 hw.2 hz rfl

theorem isCompact_convexHull {s : Set V} (hs : IsCompact s) :
    IsCompact (convexHull ℝ s) := by
  have heq : convexHull ℝ s =
      ⋃ n ∈ Set.Iic (Module.finrank ℝ V + 1), combinations n s := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_Iic, exists_prop]
    constructor
    · intro hx
      exact mem_convexHull_bounded_combination hx
    · rintro ⟨n, hn, hx⟩
      exact combinations_subset_convexHull n s hx
  rw [heq]
  exact (Set.finite_Iic _).isCompact_biUnion fun n _ => isCompact_combinations n hs

def boundedScaledHull (B : ℝ) (s : Set V) : Set V :=
  {0} ∪ (fun p : ℝ × V => p.1 • p.2) '' (Set.Icc 0 B ×ˢ convexHull ℝ s)

theorem isCompact_boundedScaledHull (B : ℝ) {s : Set V} (hs : IsCompact s) :
    IsCompact (boundedScaledHull B s) :=
  isCompact_singleton.union ((isCompact_Icc.prod (isCompact_convexHull hs)).image
    (continuous_fst.smul continuous_snd))

theorem nonnegative_combination_mem_boundedScaledHull {ι : Type*} [Fintype ι]
    {s : Set V} (B : ℝ) (w : ι → ℝ) (z : ι → V)
    (hw : ∀ i, 0 ≤ w i) (hz : ∀ i, z i ∈ s) (hB : ∑ i, w i ≤ B) :
    (∑ i, w i • z i) ∈ boundedScaledHull B s := by
  classical
  have ht : 0 ≤ ∑ i, w i := Finset.sum_nonneg fun i _ => hw i
  by_cases hzero : ∑ i, w i = 0
  · have hwzero : ∀ i, w i = 0 := by
      intro i
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hw i)).mp hzero i (Finset.mem_univ i)
    left
    simp [hwzero]
  · right
    let t := ∑ i, w i
    let W : ι → ℝ := fun i => w i / t
    have hW : ∑ i, W i = 1 := by
      simp only [W, ← Finset.sum_div]
      exact div_self hzero
    have hcomb : (∑ i, W i • z i) ∈ convexHull ℝ s :=
      mem_convexHull_of_exists_fintype W z (fun i => div_nonneg (hw i) ht) hW hz rfl
    refine ⟨(t, ∑ i, W i • z i), ⟨⟨ht, hB⟩, hcomb⟩, ?_⟩
    simp only [Finset.smul_sum, smul_smul, W]
    congr 1
    ext i
    rw [mul_div_cancel₀ _ hzero]

theorem boundedScaledHull_finite_representation {s : Set V} {B : ℝ} {x : V}
    (hx : x ∈ boundedScaledHull B s) :
    ∃ n ≤ Module.finrank ℝ V + 1, ∃ (w : Fin n → ℝ) (z : Fin n → V),
      (∀ i, 0 ≤ w i) ∧ (∀ i, z i ∈ s) ∧ (∑ i, w i • z i) = x := by
  classical
  rcases hx with hx | ⟨⟨r, y⟩, ⟨hr, hy⟩, rfl⟩
  · have hxzero : x = 0 := hx
    refine ⟨0, by omega, Fin.elim0, Fin.elim0, ?_, ?_, ?_⟩
    · exact fun i => Fin.elim0 i
    · exact fun i => Fin.elim0 i
    · simpa using hxzero.symm
  · obtain ⟨n, hn, ⟨w, z⟩, ⟨hw, hz⟩, heq⟩ := mem_convexHull_bounded_combination hy
    refine ⟨n, hn, (fun i => r * w i), z,
      (fun i => mul_nonneg hr.1 (hw.1 i)), hz, ?_⟩
    simpa only [combinationMap, Finset.smul_sum, smul_smul] using congrArg (r • ·) heq

theorem boundedScaledHull_limit [T2Space V] {η : Type*} {l : Filter η} [l.NeBot]
    {s : Set V} (hs : IsCompact s) {B : ℝ} {f : η → V} {x : V}
    (hlim : Filter.Tendsto f l (nhds x))
    (hf : ∀ᶠ i in l, f i ∈ boundedScaledHull B s) : x ∈ boundedScaledHull B s :=
  (isCompact_boundedScaledHull B hs).isClosed.mem_of_tendsto hlim hf

end CompactHull

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

abbrev Local (κ : Type*) := EuclideanSpace ℂ (Fin 2 × κ)
abbrev Index (κ : Type*) := (Fin 2 × κ) × (Fin 2 × κ)
abbrev Ket (κ : Type*) := QuantumProver.ElegantJointMeasurement.ResourceCode.ExtendedSpace (Fin 2) (Fin 2) κ
abbrev Augmented (κ : Type*) := Matrix (Index κ) (Index κ) ℂ × ℝ

instance augmentedFiniteDimensional : FiniteDimensional ℝ (Augmented κ) := by
  change FiniteDimensional ℝ ((Index κ → Index κ → ℂ) × ℝ)
  infer_instance

def localMatrix (a : Local κ) : Matrix (Fin 2) κ ℂ := fun i k => a (i, k)

def product (p : Local κ × Local κ) : Ket κ :=
  QuantumProver.ElegantJointMeasurement.ResourceCode.productKet (localMatrix p.1) (localMatrix p.2)

def unitPairs (κ : Type*) [Fintype κ] : Set (Local κ × Local κ) :=
  Metric.sphere 0 1 ×ˢ Metric.sphere 0 1

def effectMatrix (z : Ket κ) : Matrix (Index κ) (Index κ) ℂ :=
  Matrix.vecMulVec (fun i => z i) (fun j => conj (z j))

def tailMatrix (β : κ → ℝ) (k : κ) (z : Ket κ) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => ∑ t ∈ Finset.univ.erase k, (β t : ℂ) * z ((i, t), (j, t))

def augmentedMap (β : κ → ℝ) (k : κ) (p : Local κ × Local κ) : Augmented κ :=
  (effectMatrix (product p), ‖(tailMatrix β k (product p)).det‖)

def atoms (β : κ → ℝ) (k : κ) : Set (Augmented κ) :=
  augmentedMap β k '' unitPairs κ

theorem effectMatrix_eq_rankOne (z : Ket κ) :
    effectMatrix z = Matrix.toEuclideanLin.symm (rankOne ℂ z z).toLinearMap := by
  rw [InnerProductSpace.symm_toEuclideanLin_rankOne]
  rfl

theorem tailMatrix_product (β : κ → ℝ) (k : κ) (p : Local κ × Local κ) :
    tailMatrix β k (product p) =
      QuantumProver.ElegantJointMeasurement.ResourceCode.tailContraction β (localMatrix p.1) (localMatrix p.2) k := by
  ext i j
  simp only [tailMatrix, QuantumProver.ElegantJointMeasurement.ResourceCode.tailContraction_apply, product,
    QuantumProver.ElegantJointMeasurement.ResourceCode.productKet_apply]
  apply Finset.sum_congr rfl
  intro t ht
  ring

theorem continuous_product : Continuous (product : Local κ × Local κ → Ket κ) := by
  unfold product QuantumProver.ElegantJointMeasurement.ResourceCode.productKet localMatrix
  apply (PiLp.continuous_toLp 2 (fun _ : Index κ => ℂ)).comp
  fun_prop

theorem continuous_effectMatrix : Continuous (effectMatrix : Ket κ → Matrix (Index κ) (Index κ) ℂ) := by
  unfold effectMatrix Matrix.vecMulVec
  fun_prop

theorem continuous_tailMatrix (β : κ → ℝ) (k : κ) :
    Continuous (tailMatrix β k : Ket κ → Matrix (Fin 2) (Fin 2) ℂ) := by
  unfold tailMatrix
  fun_prop

theorem continuous_augmentedMap (β : κ → ℝ) (k : κ) :
    Continuous (augmentedMap β k : Local κ × Local κ → Augmented κ) :=
  (continuous_effectMatrix.comp continuous_product).prodMk
    (((continuous_tailMatrix β k).comp continuous_product).matrix_det.norm)

theorem isCompact_unitPairs : IsCompact (unitPairs κ) :=
  (isCompact_sphere 0 1).prod (isCompact_sphere 0 1)

theorem isCompact_atoms (β : κ → ℝ) (k : κ) : IsCompact (atoms β k) :=
  isCompact_unitPairs.image (continuous_augmentedMap β k)

theorem isCompact_augmentedHull (β : κ → ℝ) (k : κ) :
    IsCompact (convexHull ℝ (atoms β k)) :=
  isCompact_convexHull (V := Augmented κ) (isCompact_atoms β k)

theorem product_norm_sq (p : Local κ × Local κ) :
    ‖product p‖ ^ 2 = ‖p.1‖ ^ 2 * ‖p.2‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
  change (∑ i : Fin 2 × κ, ∑ j : Fin 2 × κ, ‖p.1 i * p.2 j‖ ^ 2) = _
  simp only [norm_mul, mul_pow, ← Finset.mul_sum, ← Finset.sum_mul]
  rw [← EuclideanSpace.norm_sq_eq, ← EuclideanSpace.norm_sq_eq]

theorem product_norm_of_unit {p : Local κ × Local κ} (hp : p ∈ unitPairs κ) :
    ‖product p‖ = 1 := by
  have h1 : ‖p.1‖ = 1 := by simpa [unitPairs, Metric.mem_sphere, dist_zero_right] using hp.1
  have h2 : ‖p.2‖ = 1 := by simpa [unitPairs, Metric.mem_sphere, dist_zero_right] using hp.2
  have hs := product_norm_sq p
  rw [h1, h2] at hs
  nlinarith [norm_nonneg (product p)]

def effectMass (F : Matrix (Index κ) (Index κ) ℂ) : ℝ := F.trace.re

theorem effectMass_rankOne (z : Ket κ) : effectMass (effectMatrix z) = ‖z‖ ^ 2 := by
  simp [effectMass, effectMatrix, Matrix.trace, Matrix.diag, Matrix.vecMulVec_apply,
    Complex.mul_conj', EuclideanSpace.norm_sq_eq, ← Complex.ofReal_pow]

theorem atom_mass {β : κ → ℝ} {k : κ} {z : Augmented κ} (hz : z ∈ atoms β k) :
    effectMass z.1 = 1 := by
  obtain ⟨p, hp, rfl⟩ := hz
  change effectMass (effectMatrix (product p)) = 1
  rw [effectMass_rankOne, product_norm_of_unit hp]
  norm_num

def massLinear : Augmented κ →ₗ[ℝ] ℝ where
  toFun z := effectMass z.1
  map_add' z w := by simp [effectMass, Matrix.trace_add]
  map_smul' r z := by simp [effectMass, Matrix.trace_smul]

theorem hull_mass {β : κ → ℝ} {k : κ} {z : Augmented κ}
    (hz : z ∈ convexHull ℝ (atoms β k)) : massLinear z = 1 := by
  have hsub : atoms β k ⊆ massLinear ⁻¹' ({1} : Set ℝ) := by
    intro z hz
    exact atom_mass hz
  exact convexHull_min hsub ((convex_singleton (1 : ℝ)).linear_preimage massLinear) hz

theorem boundedScaledHull_zero_mass {β : κ → ℝ} {k : κ} {B : ℝ} {z : Augmented κ}
    (hz : z ∈ boundedScaledHull B (atoms β k)) (hm : massLinear z = 0) : z = 0 := by
  rcases hz with hz | ⟨⟨r, y⟩, ⟨hr, hy⟩, rfl⟩
  · exact hz
  · have hmass : massLinear (r • y) = r := by simp [hull_mass hy]
    have hrzero : r = 0 := hmass.symm.trans hm
    simp [hrzero]

theorem augmented_finite_representation {β : κ → ℝ} {k : κ} {B : ℝ} {x : Augmented κ}
    (hx : x ∈ boundedScaledHull B (atoms β k)) :
    ∃ n ≤ Module.finrank ℝ (Augmented κ) + 1,
      ∃ (w : Fin n → ℝ) (p : Fin n → Local κ × Local κ),
        (∀ i, 0 ≤ w i) ∧ (∀ i, p i ∈ unitPairs κ) ∧
        (∑ i, w i) = effectMass x.1 ∧ (∑ i, w i • augmentedMap β k (p i)) = x := by
  classical
  obtain ⟨n, hn, w, z, hw, hz, heq⟩ := boundedScaledHull_finite_representation hx
  have hzmass : ∀ i, massLinear (z i) = 1 := fun i => atom_mass (hz i)
  have hsum : (∑ i, w i) = effectMass x.1 := by
    change (∑ i, w i) = massLinear x
    rw [← heq, map_sum]
    simp [hzmass]
  have hp : ∀ i, ∃ p, p ∈ unitPairs κ ∧ augmentedMap β k p = z i := hz
  choose p hp heqp using hp
  refine ⟨n, hn, w, p, hw, hp, hsum, ?_⟩
  simpa only [heqp] using heq

theorem representation_coordinates {β : κ → ℝ} {k : κ} {n : ℕ}
    {w : Fin n → ℝ} {p : Fin n → Local κ × Local κ} {x : Augmented κ}
    (h : (∑ i, w i • augmentedMap β k (p i)) = x) :
    (∑ i, w i • effectMatrix (product (p i))) = x.1 ∧
    (∑ i, w i * ‖(QuantumProver.ElegantJointMeasurement.ResourceCode.tailContraction β
      (localMatrix (p i).1) (localMatrix (p i).2) k).det‖) = x.2 := by
  constructor
  · simpa [augmentedMap, Prod.fst_sum] using congrArg Prod.fst h
  · simpa [augmentedMap, tailMatrix_product, smul_eq_mul, Prod.snd_sum] using congrArg Prod.snd h

theorem limit_of_finite_product_moments {η : Type*} {l : Filter η} [l.NeBot]
    (β : κ → ℝ) (k : κ) (B C : ℝ) (f : η → Augmented κ) (x : Augmented κ)
    (hlim : Filter.Tendsto f l (nhds x))
    (hfinite : ∀ᶠ t in l, ∃ (n : ℕ) (w : Fin n → ℝ) (p : Fin n → Local κ × Local κ),
      (∀ i, 0 ≤ w i) ∧ (∀ i, p i ∈ unitPairs κ) ∧
      (∑ i, w i) ≤ B ∧ (∑ i, w i • augmentedMap β k (p i)) = f t)
    (hcost : ∀ᶠ t in l, (f t).2 ≤ C) :
    (∃ n ≤ Module.finrank ℝ (Augmented κ) + 1,
      ∃ (w : Fin n → ℝ) (p : Fin n → Local κ × Local κ),
        (∀ i, 0 ≤ w i) ∧ (∀ i, p i ∈ unitPairs κ) ∧
        (∑ i, w i) = effectMass x.1 ∧ (∑ i, w i • augmentedMap β k (p i)) = x) ∧
      x.2 ≤ C := by
  have hmem : ∀ᶠ t in l, f t ∈ boundedScaledHull B (atoms β k) := by
    filter_upwards [hfinite] with t ht
    obtain ⟨n, w, p, hw, hp, hB, heq⟩ := ht
    rw [← heq]
    exact nonnegative_combination_mem_boundedScaledHull B w (fun i => augmentedMap β k (p i))
      hw (fun i => ⟨p i, hp i, rfl⟩) hB
  have hx := boundedScaledHull_limit (isCompact_atoms β k) hlim hmem
  refine ⟨augmented_finite_representation hx, ?_⟩
  exact (isClosed_Iic : IsClosed (Set.Iic C)).mem_of_tendsto
    (continuous_snd.tendsto x |>.comp hlim) hcost

theorem effectMatrix_smul (r : ℝ) (z : Ket κ) :
    effectMatrix (r • z) = r ^ 2 • effectMatrix z := by
  ext i j
  change ((r : ℂ) * z i) * conj ((r : ℂ) * z j) =
    ((r ^ 2 : ℝ) : ℂ) * (z i * conj (z j))
  rw [map_mul, Complex.conj_ofReal, Complex.ofReal_pow]
  ring

theorem tailMatrix_smul (β : κ → ℝ) (k : κ) (r : ℝ) (z : Ket κ) :
    tailMatrix β k (r • z) = r • tailMatrix β k z := by
  ext i j
  simp only [tailMatrix, PiLp.smul_apply, Matrix.smul_apply,
    RCLike.real_smul_eq_coe_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t ht
  ring

theorem tailCost_smul (β : κ → ℝ) (k : κ) (r : ℝ) (z : Ket κ) :
    ‖(tailMatrix β k (r • z)).det‖ = r ^ 2 * ‖(tailMatrix β k z).det‖ := by
  rw [tailMatrix_smul, Matrix.det_smul_of_tower]
  simp [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg r)]

theorem product_smul (r s : ℝ) (p : Local κ × Local κ) :
    product (r • p.1, s • p.2) = (r * s) • product p := by
  ext z
  change ((r : ℂ) * p.1 z.1) * ((s : ℂ) * p.2 z.2) =
    ((r * s : ℝ) : ℂ) * (p.1 z.1 * p.2 z.2)
  rw [Complex.ofReal_mul]
  ring

theorem augmentedMap_smul (β : κ → ℝ) (k : κ) (r s : ℝ) (p : Local κ × Local κ) :
    augmentedMap β k (r • p.1, s • p.2) = (r * s) ^ 2 • augmentedMap β k p := by
  apply Prod.ext
  · exact (congrArg effectMatrix (product_smul r s p)).trans (effectMatrix_smul (r * s) (product p))
  · change ‖(tailMatrix β k (product (r • p.1, s • p.2))).det‖ =
      (r * s) ^ 2 * ‖(tailMatrix β k (product p)).det‖
    exact (congrArg (fun z => ‖(tailMatrix β k z).det‖) (product_smul r s p)).trans
      (tailCost_smul β k (r * s) (product p))

theorem product_zero_left (b : Local κ) : product (0, b) = 0 := by
  ext z
  simp [product, QuantumProver.ElegantJointMeasurement.ResourceCode.productKet, localMatrix]

theorem product_zero_right (a : Local κ) : product (a, 0) = 0 := by
  ext z
  simp [product, QuantumProver.ElegantJointMeasurement.ResourceCode.productKet, localMatrix]

theorem augmentedMap_zero_product (β : κ → ℝ) (k : κ) {p : Local κ × Local κ}
    (hp : product p = 0) : augmentedMap β k p = 0 := by
  apply Prod.ext
  · ext i j
    simp [augmentedMap, hp, effectMatrix, Matrix.vecMulVec_apply]
  · simp [augmentedMap, hp, tailMatrix, Matrix.det_fin_two]

def defaultPair (k : κ) : Local κ × Local κ :=
  (EuclideanSpace.single (0, k) 1, EuclideanSpace.single (0, k) 1)

theorem defaultPair_unit (k : κ) : defaultPair k ∈ unitPairs κ := by
  simp [defaultPair, unitPairs, Metric.mem_sphere, dist_zero_right]

theorem exists_normalized_atom (β : κ → ℝ) (k : κ) (p : Local κ × Local κ) :
    ∃ q, q ∈ unitPairs κ ∧
      augmentedMap β k p = (‖p.1‖ * ‖p.2‖) ^ 2 • augmentedMap β k q := by
  by_cases ha : p.1 = 0
  · refine ⟨defaultPair k, defaultPair_unit k, ?_⟩
    have hprod : product p = 0 := by
      change product (p.1, p.2) = 0
      rw [ha]
      exact product_zero_left p.2
    simp [ha, augmentedMap_zero_product β k hprod]
  by_cases hb : p.2 = 0
  · refine ⟨defaultPair k, defaultPair_unit k, ?_⟩
    have hprod : product p = 0 := by
      change product (p.1, p.2) = 0
      rw [hb]
      exact product_zero_right p.1
    simp [hb, augmentedMap_zero_product β k hprod]
  let q : Local κ × Local κ := (NormedSpace.normalize p.1, NormedSpace.normalize p.2)
  have hq : q ∈ unitPairs κ := by
    exact ⟨by simpa [q, Metric.mem_sphere, dist_zero_right] using NormedSpace.norm_normalize ha,
      by simpa [q, Metric.mem_sphere, dist_zero_right] using NormedSpace.norm_normalize hb⟩
  refine ⟨q, hq, ?_⟩
  calc
    augmentedMap β k p = augmentedMap β k (‖p.1‖ • q.1, ‖p.2‖ • q.2) := by
      congr 1
      ext <;> simp [q, NormedSpace.norm_smul_normalize]
    _ = (‖p.1‖ * ‖p.2‖) ^ 2 • augmentedMap β k q := augmentedMap_smul β k _ _ q

theorem augmentedMap_mass (β : κ → ℝ) (k : κ) (p : Local κ × Local κ) :
    massLinear (augmentedMap β k p) = (‖p.1‖ * ‖p.2‖) ^ 2 := by
  change effectMass (effectMatrix (product p)) = _
  rw [effectMass_rankOne, product_norm_sq, mul_pow]

theorem raw_product_sum_mem_boundedScaledHull {ι : Type*} [Fintype ι]
    (β : κ → ℝ) (k : κ) (B : ℝ) (p : ι → Local κ × Local κ)
    (hB : massLinear (∑ i, augmentedMap β k (p i)) ≤ B) :
    (∑ i, augmentedMap β k (p i)) ∈ boundedScaledHull B (atoms β k) := by
  classical
  choose q hq heq using fun i => exists_normalized_atom β k (p i)
  let w : ι → ℝ := fun i => (‖(p i).1‖ * ‖(p i).2‖) ^ 2
  have hw : ∀ i, 0 ≤ w i := fun i => sq_nonneg _
  have hweight : ∑ i, w i ≤ B := by
    simpa only [map_sum, augmentedMap_mass, w] using hB
  have hsum : (∑ i, augmentedMap β k (p i)) = ∑ i, w i • augmentedMap β k (q i) := by
    apply Finset.sum_congr rfl
    intro i hi
    exact heq i
  rw [hsum]
  exact nonnegative_combination_mem_boundedScaledHull B w (fun i => augmentedMap β k (q i))
    hw (fun i => ⟨q i, hq i, rfl⟩) hweight

theorem limit_of_raw_product_moments {η : Type*} {l : Filter η} [l.NeBot]
    (β : κ → ℝ) (k : κ) (B C : ℝ) (f : η → Augmented κ) (x : Augmented κ)
    (hlim : Filter.Tendsto f l (nhds x))
    (hfinite : ∀ᶠ t in l, ∃ (n : ℕ) (p : Fin n → Local κ × Local κ),
      (∑ i, augmentedMap β k (p i)) = f t)
    (htrace : ∀ᶠ t in l, effectMass (f t).1 ≤ B)
    (hcost : ∀ᶠ t in l, (f t).2 ≤ C) :
    (∃ n ≤ Module.finrank ℝ (Augmented κ) + 1,
      ∃ (w : Fin n → ℝ) (p : Fin n → Local κ × Local κ),
        (∀ i, 0 ≤ w i) ∧ (∀ i, p i ∈ unitPairs κ) ∧
        (∑ i, w i) = effectMass x.1 ∧ (∑ i, w i • augmentedMap β k (p i)) = x) ∧
      x.2 ≤ C := by
  have hmem : ∀ᶠ t in l, f t ∈ boundedScaledHull B (atoms β k) := by
    filter_upwards [hfinite, htrace] with t ht hB
    obtain ⟨n, p, heq⟩ := ht
    rw [← heq] at hB ⊢
    exact raw_product_sum_mem_boundedScaledHull β k B p hB
  have hx := boundedScaledHull_limit (isCompact_atoms β k) hlim hmem
  refine ⟨augmented_finite_representation hx, ?_⟩
  exact (isClosed_Iic : IsClosed (Set.Iic C)).mem_of_tendsto
    (continuous_snd.tendsto x |>.comp hlim) hcost

theorem effect_limit_finite_cost_representation {η : Type*} {l : Filter η} [l.NeBot]
    (β : κ → ℝ) (k : κ) (B C : ℝ) (f : η → Augmented κ)
    (F : Matrix (Index κ) (Index κ) ℂ)
    (hlim : Filter.Tendsto (fun t => (f t).1) l (nhds F))
    (hfinite : ∀ᶠ t in l, ∃ (n : ℕ) (p : Fin n → Local κ × Local κ),
      (∑ i, augmentedMap β k (p i)) = f t)
    (htrace : ∀ᶠ t in l, effectMass (f t).1 ≤ B)
    (hcost : ∀ᶠ t in l, (f t).2 ≤ C) :
    ∃ c : ℝ, 0 ≤ c ∧ c ≤ C ∧
      ∃ n ≤ Module.finrank ℝ (Augmented κ) + 1,
        ∃ (w : Fin n → ℝ) (p : Fin n → Local κ × Local κ),
          (∀ i, 0 ≤ w i) ∧ (∀ i, p i ∈ unitPairs κ) ∧
          (∑ i, w i) = effectMass F ∧
          (∑ i, w i • effectMatrix (product (p i))) = F ∧
          (∑ i, w i * ‖(QuantumProver.ElegantJointMeasurement.ResourceCode.tailContraction β
            (localMatrix (p i).1) (localMatrix (p i).2) k).det‖) = c := by
  have hmem : ∀ᶠ t in l, f t ∈ boundedScaledHull B (atoms β k) := by
    filter_upwards [hfinite, htrace] with t ht hB
    obtain ⟨n, p, heq⟩ := ht
    rw [← heq] at hB ⊢
    exact raw_product_sum_mem_boundedScaledHull β k B p hB
  obtain ⟨x, hx, hcluster⟩ :=
    (isCompact_boundedScaledHull B (isCompact_atoms β k)).exists_mapClusterPt_of_frequently hmem.frequently
  obtain ⟨U, hU, hUl⟩ := mapClusterPt_iff_ultrafilter.mp hcluster
  have hxfirst : x.1 = F :=
    tendsto_nhds_unique ((continuous_fst.tendsto x).comp hUl) (hlim.mono_left hU)
  have hxCost : x.2 ≤ C := (isClosed_Iic : IsClosed (Set.Iic C)).mem_of_tendsto
    ((continuous_snd.tendsto x).comp hUl) (Filter.Eventually.filter_mono hU hcost)
  obtain ⟨n, hn, w, p, hw, hp, hsum, heq⟩ := augmented_finite_representation hx
  obtain ⟨heffect, hcosteq⟩ := representation_coordinates heq
  have hc0 : 0 ≤ x.2 := by
    rw [← hcosteq]
    exact Finset.sum_nonneg fun i _ => mul_nonneg (hw i) (norm_nonneg _)
  refine ⟨x.2, hc0, hxCost, n, hn, w, p, hw, hp, ?_, ?_, hcosteq⟩
  · simpa only [hxfirst] using hsum
  · simpa only [hxfirst] using heffect

theorem finite_outcome_effect_limit_cost_representation
    {η ι : Type*} [Fintype ι] {l : Filter η} [l.NeBot]
    (β : κ → ℝ) (k : κ) (B : ι → ℝ) (C : ℝ)
    (f : η → ι → Augmented κ) (F : ι → Matrix (Index κ) (Index κ) ℂ)
    (hlim : Filter.Tendsto (fun t j => (f t j).1) l (nhds F))
    (hfinite : ∀ᶠ t in l, ∀ j, ∃ (n : ℕ) (p : Fin n → Local κ × Local κ),
      (∑ i, augmentedMap β k (p i)) = f t j)
    (htrace : ∀ᶠ t in l, ∀ j, effectMass (f t j).1 ≤ B j)
    (hcost : ∀ᶠ t in l, (∑ j, (f t j).2) ≤ C) :
    ∃ c : ι → ℝ, (∀ j, 0 ≤ c j) ∧ (∑ j, c j) ≤ C ∧
      ∀ j, ∃ n ≤ Module.finrank ℝ (Augmented κ) + 1,
        ∃ (w : Fin n → ℝ) (p : Fin n → Local κ × Local κ),
          (∀ i, 0 ≤ w i) ∧ (∀ i, p i ∈ unitPairs κ) ∧
          (∑ i, w i) = effectMass (F j) ∧
          (∑ i, w i • effectMatrix (product (p i))) = F j ∧
          (∑ i, w i * ‖(QuantumProver.ElegantJointMeasurement.ResourceCode.tailContraction β
            (localMatrix (p i).1) (localMatrix (p i).2) k).det‖) = c j := by
  have hcompact : IsCompact {y : ι → Augmented κ |
      ∀ j, y j ∈ boundedScaledHull (B j) (atoms β k)} :=
    isCompact_pi_infinite fun j => isCompact_boundedScaledHull (B j) (isCompact_atoms β k)
  have hmem : ∀ᶠ t in l, ∀ j, f t j ∈ boundedScaledHull (B j) (atoms β k) := by
    filter_upwards [hfinite, htrace] with t ht hB
    intro j
    obtain ⟨n, p, heq⟩ := ht j
    have hBj := hB j
    rw [← heq] at hBj ⊢
    exact raw_product_sum_mem_boundedScaledHull β k (B j) p hBj
  obtain ⟨x, hx, hcluster⟩ := hcompact.exists_mapClusterPt_of_frequently hmem.frequently
  obtain ⟨U, hU, hUl⟩ := mapClusterPt_iff_ultrafilter.mp hcluster
  have hfirst : Continuous (fun y : ι → Augmented κ => fun j => (y j).1) := by fun_prop
  have hcostfun : Continuous (fun y : ι → Augmented κ => ∑ j, (y j).2) := by fun_prop
  have hxfirst : (fun j => (x j).1) = F :=
    tendsto_nhds_unique ((hfirst.tendsto x).comp hUl) (hlim.mono_left hU)
  have hxCost : (∑ j, (x j).2) ≤ C := (isClosed_Iic : IsClosed (Set.Iic C)).mem_of_tendsto
    ((hcostfun.tendsto x).comp hUl) (Filter.Eventually.filter_mono hU hcost)
  have hrepr : ∀ j, ∃ n ≤ Module.finrank ℝ (Augmented κ) + 1,
      ∃ (w : Fin n → ℝ) (p : Fin n → Local κ × Local κ),
        (∀ i, 0 ≤ w i) ∧ (∀ i, p i ∈ unitPairs κ) ∧
        (∑ i, w i) = effectMass (F j) ∧
        (∑ i, w i • effectMatrix (product (p i))) = F j ∧
        (∑ i, w i * ‖(QuantumProver.ElegantJointMeasurement.ResourceCode.tailContraction β
          (localMatrix (p i).1) (localMatrix (p i).2) k).det‖) = (x j).2 := by
    intro j
    obtain ⟨n, hn, w, p, hw, hp, hsum, heq⟩ := augmented_finite_representation (hx j)
    obtain ⟨heffect, hcosteq⟩ := representation_coordinates heq
    refine ⟨n, hn, w, p, hw, hp, ?_, ?_, hcosteq⟩
    · simpa only [congrFun hxfirst j] using hsum
    · simpa only [congrFun hxfirst j] using heffect
  refine ⟨fun j => (x j).2, ?_, hxCost, hrepr⟩
  intro j
  obtain ⟨n, hn, w, p, hw, hp, hsum, heffect, hcosteq⟩ := hrepr j
  change 0 ≤ (x j).2
  rw [← hcosteq]
  exact Finset.sum_nonneg fun i _ => mul_nonneg (hw i) (norm_nonneg _)

end

end QuantumProver.ElegantJointMeasurement.Augmented

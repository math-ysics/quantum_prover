import QuantumProver.InformationTheory.DepolarizingSquashedEntanglement.Definitions

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix Kronecker Matrix.Norms.L2Operator

namespace QuantumProver.DepolarizingSquashedEntanglement.BCYMeasurement

variable {A B C D X Y : Type*}
  [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

private theorem re_finset_sum {ι : Type*} (s : Finset ι) (f : ι → ℂ) :
    (∑ i ∈ s, f i).re = ∑ i ∈ s, (f i).re := map_sum Complex.reCLM _ _

def productDensities (A B : Type*) [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] : Set (QMatrix (A × B)) :=
  {R | ∃ a : Density A, ∃ b : Density B, R = a.matrix ⊗ₖ b.matrix}

def separableCone (A B : Type*) [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] : PointedCone ℝ (QMatrix (A × B)) :=
  PointedCone.hull ℝ (productDensities A B)

theorem separableCone_convex : Convex ℝ (separableCone A B : Set (QMatrix (A × B))) := by
  intro R hR S hS a b ha hb _
  exact (separableCone A B).add_mem
    (PointedCone.smul_mem _ ha hR) (PointedCone.smul_mem _ hb hS)

theorem isSeparable_mem_cone {R : QMatrix (A × B)} (hR : IsSeparable R) :
    R ∈ separableCone A B :=
  (convexHull_min (PointedCone.subset_hull (R := ℝ)) separableCone_convex) hR

theorem productDensities_trace_one {R : QMatrix (A × B)}
    (hR : R ∈ productDensities A B) : R.trace = 1 := by
  obtain ⟨a, b, rfl⟩ := hR
  rw [Matrix.trace_kronecker, a.trace_one, b.trace_one, one_mul]

theorem normalize_cone_isSeparable {R : QMatrix (A × B)}
    (hR : R ∈ separableCone A B) (htrace : 0 < R.trace.re) :
    IsSeparable (R.trace.re⁻¹ • R) := by
  classical
  obtain ⟨w, hw, hw0, heq⟩ := PointedCone.mem_hull_set.mp hR
  change (∑ S ∈ w.support, w S • S) = R at heq
  have hsum : (∑ S ∈ w.support, w S) = R.trace.re := by
    rw [← heq, Matrix.trace_sum, re_finset_sum]
    apply Finset.sum_congr rfl
    intro S hS
    rw [Matrix.trace_smul, Complex.smul_re, productDensities_trace_one (hw hS)]
    simp
  have hmem := w.support.centerMass_mem_convexHull
    (fun S _ => hw0 S) (by rw [hsum]; exact htrace) (fun S hS => hw hS)
  change R.trace.re⁻¹ • R ∈ convexHull ℝ (productDensities A B)
  simpa only [Finset.centerMass, hsum, heq] using hmem

private theorem sqrtProduct_gram {S T : Type*} [Fintype S] [Fintype T]
    [DecidableEq S] [DecidableEq T] {a : QMatrix S} {b : QMatrix T}
    (ha : a.PosSemidef) (hb : b.PosSemidef) :
    (CFC.sqrt a ⊗ₖ CFC.sqrt b)ᴴ * (CFC.sqrt a ⊗ₖ CFC.sqrt b) = a ⊗ₖ b := by
  rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
    (CFC.sqrt_nonneg a).posSemidef.1.eq, (CFC.sqrt_nonneg b).posSemidef.1.eq,
    CFC.sqrt_mul_sqrt_self a ha.nonneg, CFC.sqrt_mul_sqrt_self b hb.nonneg]

theorem product_posSemidef {a : QMatrix A} {b : QMatrix B}
    (ha : a.PosSemidef) (hb : b.PosSemidef) : (a ⊗ₖ b).PosSemidef := by
  rw [← sqrtProduct_gram ha hb]
  exact Matrix.posSemidef_conjTranspose_mul_self _

theorem cone_posSemidef {R : QMatrix (A × B)} (hR : R ∈ separableCone A B) :
    R.PosSemidef := by
  classical
  obtain ⟨w, hw, hw0, heq⟩ := PointedCone.mem_hull_set.mp hR
  change (∑ S ∈ w.support, w S • S) = R at heq
  rw [← heq]
  apply Matrix.posSemidef_sum
  intro S hS
  obtain ⟨a, b, rfl⟩ := hw hS
  exact (product_posSemidef a.positive b.positive).smul (hw0 _)

private theorem trace_re_pos_of_posSemidef_ne_zero {S : Type*}
    [Fintype S] [DecidableEq S] {a : QMatrix S} (ha : a.PosSemidef) (hzero : a ≠ 0) :
    0 < a.trace.re := by
  have hn := Complex.nonneg_iff.mp ha.trace_nonneg
  have hne : a.trace.re ≠ 0 := by
    intro hz
    apply hzero
    apply ha.trace_eq_zero_iff.mp
    apply Complex.ext <;> simp [hz, hn.2]
  exact lt_of_le_of_ne hn.1 hne.symm

def normalizedDensity {S : Type*} [Fintype S] [DecidableEq S]
    (a : QMatrix S) (ha : a.PosSemidef) (ht : 0 < a.trace.re) : Density S where
  matrix := a.trace.re⁻¹ • a
  positive := ha.smul (inv_nonneg.mpr ht.le)
  trace_one := by
    have him : a.trace.im = 0 := (Complex.nonneg_iff.mp ha.trace_nonneg).2.symm
    rw [Matrix.trace_smul]
    apply Complex.ext
    · simp only [Complex.smul_re, smul_eq_mul, Complex.one_re, inv_mul_cancel₀ ht.ne']
    · simp only [Complex.smul_im, smul_eq_mul, him, mul_zero, Complex.one_im]

theorem product_mem_cone {a : QMatrix A} {b : QMatrix B}
    (ha : a.PosSemidef) (hb : b.PosSemidef) : a ⊗ₖ b ∈ separableCone A B := by
  by_cases hazero : a = 0
  · simp only [hazero, Matrix.zero_kronecker]
    exact (separableCone A B).zero_mem
  by_cases hbzero : b = 0
  · simp only [hbzero, Matrix.kronecker_zero]
    exact (separableCone A B).zero_mem
  have hta := trace_re_pos_of_posSemidef_ne_zero ha hazero
  have htb := trace_re_pos_of_posSemidef_ne_zero hb hbzero
  let a' := normalizedDensity a ha hta
  let b' := normalizedDensity b hb htb
  have hea : a = a.trace.re • a'.matrix := by
    dsimp [a', normalizedDensity]
    rw [smul_smul, mul_inv_cancel₀ hta.ne', one_smul]
  have heb : b = b.trace.re • b'.matrix := by
    dsimp [b', normalizedDensity]
    rw [smul_smul, mul_inv_cancel₀ htb.ne', one_smul]
  have hbase : a'.matrix ⊗ₖ b'.matrix ∈ separableCone A B :=
    PointedCone.subset_hull ⟨a', b', rfl⟩
  rw [hea, heb, Matrix.smul_kronecker, Matrix.kronecker_smul, smul_smul]
  exact PointedCone.smul_mem _ (mul_nonneg hta.le htb.le) hbase

section LocalFilters

variable [Fintype C] [Fintype D] [DecidableEq C] [DecidableEq D]

def localFilter (L : Matrix C A ℂ) (R : Matrix D B ℂ)
    (ρ : QMatrix (A × B)) : QMatrix (C × D) := (L ⊗ₖ R) * ρ * (L ⊗ₖ R)ᴴ

omit [DecidableEq A] [DecidableEq B] [Fintype C] [Fintype D]
  [DecidableEq C] [DecidableEq D] in
theorem localFilter_product (L : Matrix C A ℂ) (R : Matrix D B ℂ)
    (a : QMatrix A) (b : QMatrix B) :
    localFilter L R (a ⊗ₖ b) = (L * a * Lᴴ) ⊗ₖ (R * b * Rᴴ) := by
  rw [localFilter, Matrix.conjTranspose_kronecker,
    ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]

theorem localFilter_mem_cone (L : Matrix C A ℂ) (R : Matrix D B ℂ)
    {ρ : QMatrix (A × B)} (hρ : ρ ∈ separableCone A B) :
    localFilter L R ρ ∈ separableCone C D := by
  classical
  obtain ⟨w, hw, hw0, heq⟩ := PointedCone.mem_hull_set.mp hρ
  change (∑ S ∈ w.support, w S • S) = ρ at heq
  rw [← heq]
  simp only [localFilter, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul]
  apply (separableCone C D).sum_mem
  intro S hS
  obtain ⟨a, b, rfl⟩ := hw hS
  apply PointedCone.smul_mem _ (hw0 _)
  change localFilter L R (a.matrix ⊗ₖ b.matrix) ∈ _
  rw [localFilter_product]
  exact product_mem_cone (a.positive.mul_mul_conjTranspose_same L)
    (b.positive.mul_mul_conjTranspose_same R)

end LocalFilters

section Measurement

variable [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]

def fineKraus (M : OneWayPOVM A B X Y) (z : X × Y) : QMatrix (A × B) :=
  CFC.sqrt (M.alice z.1) ⊗ₖ CFC.sqrt (M.bob z.1 z.2)

omit [DecidableEq X] [DecidableEq Y] in
theorem fineKraus_gram (M : OneWayPOVM A B X Y) (z : X × Y) :
    (fineKraus M z)ᴴ * fineKraus M z = M.alice z.1 ⊗ₖ M.bob z.1 z.2 :=
  sqrtProduct_gram (M.alice_positive _) (M.bob_positive _ _)

omit [DecidableEq X] [DecidableEq Y] in
theorem fineKraus_complete (M : OneWayPOVM A B X Y) :
    (∑ z, (fineKraus M z)ᴴ * fineKraus M z) = 1 := by
  simp only [fineKraus_gram, Fintype.sum_prod_type]
  have heq : (∑ x, ∑ y, M.alice x ⊗ₖ M.bob x y) =
      (∑ x, M.alice x) ⊗ₖ (1 : QMatrix B) := by
    ext i j
    simp only [Matrix.sum_apply, Matrix.kroneckerMap_apply]
    have hb (x : X) : (∑ y, M.bob x y i.2 j.2) = (1 : QMatrix B) i.2 j.2 := by
      simpa only [Matrix.sum_apply] using congrArg (fun T : QMatrix B => T i.2 j.2)
        (M.bob_complete x)
    simp_rw [← Finset.mul_sum, hb]
    rw [← Finset.sum_mul]
  rw [heq, M.alice_complete, Matrix.one_kronecker_one]

def coarseApply (M : OneWayPOVM A B X Y) (s : Finset (X × Y))
    (ρ : QMatrix (A × B)) : QMatrix (A × B) :=
  ∑ z ∈ s, fineKraus M z * ρ * (fineKraus M z)ᴴ

omit [DecidableEq X] [DecidableEq Y] in
theorem coarseApply_posSemidef (M : OneWayPOVM A B X Y) (s : Finset (X × Y))
    {ρ : QMatrix (A × B)} (hρ : ρ.PosSemidef) : (coarseApply M s ρ).PosSemidef :=
  Matrix.posSemidef_sum s (fun _ _ => hρ.mul_mul_conjTranspose_same _)

omit [DecidableEq X] [DecidableEq Y] in
theorem coarseApply_mem_cone (M : OneWayPOVM A B X Y) (s : Finset (X × Y))
    {ρ : QMatrix (A × B)} (hρ : ρ ∈ separableCone A B) :
    coarseApply M s ρ ∈ separableCone A B := by
  apply (separableCone A B).sum_mem
  intro z _
  exact localFilter_mem_cone _ _ hρ

omit [DecidableEq X] [DecidableEq Y] in
theorem coarseApply_zero (M : OneWayPOVM A B X Y) (s : Finset (X × Y)) :
    coarseApply M s 0 = 0 := by simp [coarseApply]

omit [DecidableEq X] [DecidableEq Y] in
theorem coarseApply_smul (M : OneWayPOVM A B X Y) (s : Finset (X × Y))
    (r : ℝ) (ρ : QMatrix (A × B)) :
    coarseApply M s (r • ρ) = r • coarseApply M s ρ := by
  simp only [coarseApply, Matrix.mul_smul, Matrix.smul_mul, Finset.smul_sum]

theorem normalizedDensity_coarse_probability (M : OneWayPOVM A B X Y)
    (s : Finset (X × Y)) (ρ : QMatrix (A × B)) (hρ : ρ.PosSemidef)
    (ht : 0 < ρ.trace.re) :
    (coarseApply M s (normalizedDensity ρ hρ ht).matrix).trace.re =
      (coarseApply M s ρ).trace.re / ρ.trace.re := by
  simp only [normalizedDensity, coarseApply_smul, Matrix.trace_smul,
    Complex.smul_re, smul_eq_mul, div_eq_mul_inv, mul_comm]

omit [DecidableEq X] [DecidableEq Y] in
theorem coarseApply_trace (M : OneWayPOVM A B X Y) (s : Finset (X × Y))
    (ρ : QMatrix (A × B)) :
    (coarseApply M s ρ).trace = ∑ z ∈ s, (ρ * (M.alice z.1 ⊗ₖ M.bob z.1 z.2)).trace := by
  unfold coarseApply
  rw [Matrix.trace_sum]
  apply Finset.sum_congr rfl
  intro z _
  rw [Matrix.trace_mul_cycle, fineKraus_gram, Matrix.trace_mul_comm]

theorem coarseApply_probability (M : OneWayPOVM A B X Y) (s : Finset (X × Y))
    (ρ : QMatrix (A × B)) :
    (coarseApply M s ρ).trace.re = ∑ z ∈ s, oneWayOutcome M ρ z.1 z.2 := by
  rw [coarseApply_trace, re_finset_sum]
  rfl

theorem coarseApply_complement_add (M : OneWayPOVM A B X Y) (s : Finset (X × Y))
    (ρ : QMatrix (A × B)) :
    coarseApply M s ρ + coarseApply M (Finset.univ \ s) ρ = coarseApply M Finset.univ ρ := by
  unfold coarseApply
  exact Finset.sum_add_sum_compl s _

theorem coarseApply_total_trace (M : OneWayPOVM A B X Y) (ρ : QMatrix (A × B)) :
    (coarseApply M Finset.univ ρ).trace = ρ.trace := by
  unfold coarseApply
  rw [Matrix.trace_sum]
  calc
    _ = ∑ z, ((fineKraus M z)ᴴ * fineKraus M z * ρ).trace := by
      apply Finset.sum_congr rfl
      intro z _
      exact Matrix.trace_mul_cycle _ _ _
    _ = ((∑ z, (fineKraus M z)ᴴ * fineKraus M z) * ρ).trace := by
      rw [Matrix.sum_mul, Matrix.trace_sum]
    _ = ρ.trace := by rw [fineKraus_complete, Matrix.one_mul]

theorem coarseApply_trace_complement_sum (M : OneWayPOVM A B X Y)
    (s : Finset (X × Y)) (ρ : QMatrix (A × B)) :
    (coarseApply M s ρ).trace + (coarseApply M (Finset.univ \ s) ρ).trace = ρ.trace := by
  rw [← Matrix.trace_add, coarseApply_complement_add, coarseApply_total_trace]

omit [DecidableEq X] [DecidableEq Y] in
theorem coarseApply_probability_nonneg (M : OneWayPOVM A B X Y)
    (s : Finset (X × Y)) {ρ : QMatrix (A × B)} (hρ : ρ.PosSemidef) :
    0 ≤ (coarseApply M s ρ).trace.re :=
  (Complex.nonneg_iff.mp (coarseApply_posSemidef M s hρ).trace_nonneg).1

theorem coarseApply_probability_le_one (M : OneWayPOVM A B X Y)
    (s : Finset (X × Y)) (ρ : Density (A × B)) :
    (coarseApply M s ρ.matrix).trace.re ≤ 1 := by
  have hsum := congrArg Complex.re (coarseApply_trace_complement_sum M s ρ.matrix)
  have hnon := coarseApply_probability_nonneg M (Finset.univ \ s) ρ.positive
  rw [Complex.add_re, ρ.trace_one, Complex.one_re] at hsum
  linarith

omit [DecidableEq X] [DecidableEq Y] in
theorem coarseApply_eq_zero_of_probability_zero (M : OneWayPOVM A B X Y)
    (s : Finset (X × Y)) {ρ : QMatrix (A × B)} (hρ : ρ.PosSemidef)
    (hz : (coarseApply M s ρ).trace.re = 0) : coarseApply M s ρ = 0 := by
  have h := coarseApply_posSemidef M s hρ
  apply h.trace_eq_zero_iff.mp
  have him : (coarseApply M s ρ).trace.im = 0 :=
    (Complex.nonneg_iff.mp h.trace_nonneg).2.symm
  apply Complex.ext <;> simp [hz, him]

def coarseDensity (M : OneWayPOVM A B X Y) (s : Finset (X × Y))
    (ρ : Density (A × B)) (ht : 0 < (coarseApply M s ρ.matrix).trace.re) :
    Density (A × B) :=
  normalizedDensity _ (coarseApply_posSemidef M s ρ.positive) ht

omit [DecidableEq X] [DecidableEq Y] in
theorem coarseDensity_isSeparable (M : OneWayPOVM A B X Y) (s : Finset (X × Y))
    (ρ : Density (A × B)) (hρ : IsSeparable ρ.matrix)
    (ht : 0 < (coarseApply M s ρ.matrix).trace.re) :
    IsSeparable (coarseDensity M s ρ ht).matrix :=
  normalize_cone_isSeparable (coarseApply_mem_cone M s (isSeparable_mem_cone hρ)) ht

end Measurement

section Companions

variable [Fintype C] [Fintype D] [DecidableEq C] [DecidableEq D]
  [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]

private theorem sum_kronecker_left {S T ι : Type*} [Fintype ι]
    (f : ι → QMatrix S) (a : QMatrix T) :
    (∑ i, f i ⊗ₖ a) = (∑ i, f i) ⊗ₖ a := by
  ext u v
  simp only [Matrix.sum_apply, Matrix.kroneckerMap_apply, Finset.sum_mul]

private theorem sqrt_kronecker_one {S T : Type*} [Fintype S] [Fintype T]
    [DecidableEq S] [DecidableEq T] {a : QMatrix S} (ha : a.PosSemidef) :
    CFC.sqrt (a ⊗ₖ (1 : QMatrix T)) = CFC.sqrt a ⊗ₖ (1 : QMatrix T) := by
  have hprod : (CFC.sqrt a ⊗ₖ (1 : QMatrix T)) *
      (CFC.sqrt a ⊗ₖ (1 : QMatrix T)) = a ⊗ₖ (1 : QMatrix T) := by
    rw [← Matrix.mul_kronecker_mul, CFC.sqrt_mul_sqrt_self a ha.nonneg, Matrix.one_mul]
  exact CFC.sqrt_unique hprod
    (product_posSemidef (CFC.sqrt_nonneg a).posSemidef Matrix.PosSemidef.one).nonneg

def companionPOVM (M : OneWayPOVM A B X Y) : OneWayPOVM (A × C) (B × D) X Y where
  alice x := M.alice x ⊗ₖ (1 : QMatrix C)
  alice_positive x := product_posSemidef (M.alice_positive x) Matrix.PosSemidef.one
  alice_complete := by rw [sum_kronecker_left, M.alice_complete, Matrix.one_kronecker_one]
  bob x y := M.bob x y ⊗ₖ (1 : QMatrix D)
  bob_positive x y := product_posSemidef (M.bob_positive x y) Matrix.PosSemidef.one
  bob_complete x := by rw [sum_kronecker_left, M.bob_complete x, Matrix.one_kronecker_one]

omit [DecidableEq X] [DecidableEq Y] in
theorem fineKraus_companion (M : OneWayPOVM A B X Y) (z : X × Y) :
    fineKraus (companionPOVM (C := C) (D := D) M) z =
      (CFC.sqrt (M.alice z.1) ⊗ₖ (1 : QMatrix C)) ⊗ₖ
        (CFC.sqrt (M.bob z.1 z.2) ⊗ₖ (1 : QMatrix D)) := by
  unfold fineKraus companionPOVM
  rw [sqrt_kronecker_one (M.alice_positive _), sqrt_kronecker_one (M.bob_positive _ _)]

def companionApply (M : OneWayPOVM A B X Y) (s : Finset (X × Y))
    (ρ : QMatrix ((A × C) × (B × D))) : QMatrix ((A × C) × (B × D)) :=
  coarseApply (companionPOVM M) s ρ

omit [DecidableEq X] [DecidableEq Y] in
theorem companionApply_mem_cone (M : OneWayPOVM A B X Y) (s : Finset (X × Y))
    {ρ : QMatrix ((A × C) × (B × D))} (hρ : ρ ∈ separableCone (A × C) (B × D)) :
    companionApply M s ρ ∈ separableCone (A × C) (B × D) :=
  coarseApply_mem_cone _ s hρ

def testedMarginal (ρ : QMatrix ((A × C) × (B × D))) : QMatrix (A × B) :=
  fun u v => ∑ c, ∑ d, ρ ((u.1, c), (u.2, d)) ((v.1, c), (v.2, d))

def remainderMarginal (ρ : QMatrix ((A × C) × (B × D))) : QMatrix (C × D) :=
  fun u v => ∑ a, ∑ b, ρ ((a, u.1), (b, u.2)) ((a, v.1), (b, v.2))

omit [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
  [DecidableEq C] [DecidableEq D] in
theorem testedMarginal_product (a : QMatrix (A × C)) (b : QMatrix (B × D)) :
    testedMarginal (a ⊗ₖ b) = partialTraceRight a ⊗ₖ partialTraceRight b := by
  ext u v
  simp only [testedMarginal, partialTraceRight, QuantumProver.WernerEndpoint.partialTraceLeft,
    Matrix.kroneckerMap_apply]
  rw [Finset.sum_mul]
  simp only [Finset.mul_sum]

omit [DecidableEq A] [DecidableEq B] [Fintype C] [Fintype D]
  [DecidableEq C] [DecidableEq D] in
theorem remainderMarginal_product (a : QMatrix (A × C)) (b : QMatrix (B × D)) :
    remainderMarginal (a ⊗ₖ b) = partialTraceLeft a ⊗ₖ partialTraceLeft b := by
  ext u v
  simp only [remainderMarginal, partialTraceLeft, QuantumProver.WernerEndpoint.partialTraceRight,
    Matrix.kroneckerMap_apply]
  rw [Finset.sum_mul]
  simp only [Finset.mul_sum]

theorem testedMarginal_mem_cone {ρ : QMatrix ((A × C) × (B × D))}
    (hρ : ρ ∈ separableCone (A × C) (B × D)) : testedMarginal ρ ∈ separableCone A B := by
  classical
  obtain ⟨w, hw, hw0, heq⟩ := PointedCone.mem_hull_set.mp hρ
  change (∑ S ∈ w.support, w S • S) = ρ at heq
  have hmap : testedMarginal ρ = ∑ S ∈ w.support, w S • testedMarginal S := by
    rw [← heq]
    ext u v
    simp only [testedMarginal, Matrix.sum_apply, Matrix.smul_apply,
      Finset.smul_sum]
    trans ∑ c, ∑ S ∈ w.support, ∑ d,
      w S • S ((u.1, c), (u.2, d)) ((v.1, c), (v.2, d))
    · apply Finset.sum_congr rfl
      intro c _
      exact Finset.sum_comm
    · exact Finset.sum_comm
  rw [hmap]
  apply (separableCone A B).sum_mem
  intro S hS
  obtain ⟨a, b, rfl⟩ := hw hS
  apply PointedCone.smul_mem _ (hw0 _)
  rw [testedMarginal_product]
  exact product_mem_cone (partialTraceRight_positive a.positive)
    (partialTraceRight_positive b.positive)

theorem remainderMarginal_mem_cone {ρ : QMatrix ((A × C) × (B × D))}
    (hρ : ρ ∈ separableCone (A × C) (B × D)) : remainderMarginal ρ ∈ separableCone C D := by
  classical
  obtain ⟨w, hw, hw0, heq⟩ := PointedCone.mem_hull_set.mp hρ
  change (∑ S ∈ w.support, w S • S) = ρ at heq
  have hmap : remainderMarginal ρ = ∑ S ∈ w.support, w S • remainderMarginal S := by
    rw [← heq]
    ext u v
    simp only [remainderMarginal, Matrix.sum_apply, Matrix.smul_apply,
      Finset.smul_sum]
    trans ∑ a, ∑ S ∈ w.support, ∑ b,
      w S • S ((a, u.1), (b, u.2)) ((a, v.1), (b, v.2))
    · apply Finset.sum_congr rfl
      intro a _
      exact Finset.sum_comm
    · exact Finset.sum_comm
  rw [hmap]
  apply (separableCone C D).sum_mem
  intro S hS
  obtain ⟨a, b, rfl⟩ := hw hS
  apply PointedCone.smul_mem _ (hw0 _)
  rw [remainderMarginal_product]
  exact product_mem_cone (partialTraceLeft_positive a.positive)
    (partialTraceLeft_positive b.positive)

def companionGrouping : ((A × B) × (C × D)) ≃ ((A × C) × (B × D)) where
  toFun u := ((u.1.1, u.2.1), (u.1.2, u.2.2))
  invFun u := ((u.1.1, u.2.1), (u.1.2, u.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

private theorem trace_submatrix_equiv {S T : Type*} [Fintype S] [Fintype T]
    (e : S ≃ T) (ρ : QMatrix T) : (ρ.submatrix e e).trace = ρ.trace :=
  e.sum_comp (fun i => ρ i i)

omit [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
  [DecidableEq C] [DecidableEq D] in
theorem testedMarginal_eq_partialTrace (ρ : QMatrix ((A × C) × (B × D))) :
    testedMarginal ρ = partialTraceRight
      (ρ.submatrix (companionGrouping (A := A) (B := B) (C := C) (D := D))
        companionGrouping) := by
  ext u v
  simp only [testedMarginal, partialTraceRight, QuantumProver.WernerEndpoint.partialTraceLeft,
    Matrix.submatrix_apply, companionGrouping, Equiv.coe_fn_mk, Fintype.sum_prod_type]

omit [DecidableEq A] [DecidableEq B] [Fintype C] [Fintype D]
  [DecidableEq C] [DecidableEq D] in
theorem remainderMarginal_eq_partialTrace (ρ : QMatrix ((A × C) × (B × D))) :
    remainderMarginal ρ = partialTraceLeft
      (ρ.submatrix (companionGrouping (A := A) (B := B) (C := C) (D := D))
        companionGrouping) := by
  ext u v
  simp only [remainderMarginal, partialTraceLeft, QuantumProver.WernerEndpoint.partialTraceRight,
    Matrix.submatrix_apply, companionGrouping, Equiv.coe_fn_mk, Fintype.sum_prod_type]

omit [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D] in
theorem testedMarginal_posSemidef {ρ : QMatrix ((A × C) × (B × D))}
    (hρ : ρ.PosSemidef) : (testedMarginal ρ).PosSemidef := by
  rw [testedMarginal_eq_partialTrace]
  exact partialTraceRight_positive (hρ.submatrix _)

omit [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D] in
theorem remainderMarginal_posSemidef {ρ : QMatrix ((A × C) × (B × D))}
    (hρ : ρ.PosSemidef) : (remainderMarginal ρ).PosSemidef := by
  rw [remainderMarginal_eq_partialTrace]
  exact partialTraceLeft_positive (hρ.submatrix _)

omit [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D] in
theorem testedMarginal_trace (ρ : QMatrix ((A × C) × (B × D))) :
    (testedMarginal ρ).trace = ρ.trace := by
  rw [testedMarginal_eq_partialTrace, partialTraceRight_trace, trace_submatrix_equiv]

omit [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D] in
theorem remainderMarginal_trace (ρ : QMatrix ((A × C) × (B × D))) :
    (remainderMarginal ρ).trace = ρ.trace := by
  rw [remainderMarginal_eq_partialTrace, partialTraceLeft_trace, trace_submatrix_equiv]

private theorem trace_mul_tensor_one {S T : Type*} [Fintype S] [Fintype T]
    [DecidableEq T] (ρ : QMatrix (S × T)) (a : QMatrix S) :
    (ρ * (a ⊗ₖ (1 : QMatrix T))).trace = (partialTraceRight ρ * a).trace := by
  classical
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Fintype.sum_prod_type,
    Matrix.kroneckerMap_apply, Matrix.one_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, partialTraceRight,
    QuantumProver.WernerEndpoint.partialTraceLeft, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  exact Finset.sum_comm

omit [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
  [Fintype C] [Fintype D] in
private theorem companionEffect_grouping (a : QMatrix A) (b : QMatrix B) :
    ((a ⊗ₖ (1 : QMatrix C)) ⊗ₖ (b ⊗ₖ (1 : QMatrix D))).submatrix
      (companionGrouping (A := A) (B := B) (C := C) (D := D)) companionGrouping =
      (a ⊗ₖ b) ⊗ₖ (1 : QMatrix (C × D)) := by
  rw [← Matrix.one_kronecker_one]
  ext u v
  simp only [Matrix.submatrix_apply, companionGrouping, Equiv.coe_fn_mk,
    Matrix.kroneckerMap_apply]
  ring

theorem companionApply_trace_eq_tested (M : OneWayPOVM A B X Y)
    (s : Finset (X × Y)) (ρ : QMatrix ((A × C) × (B × D))) :
    (companionApply M s ρ).trace = (coarseApply M s (testedMarginal ρ)).trace := by
  rw [companionApply, coarseApply_trace, coarseApply_trace]
  apply Finset.sum_congr rfl
  intro z _
  change (ρ * ((M.alice z.1 ⊗ₖ (1 : QMatrix C)) ⊗ₖ
    (M.bob z.1 z.2 ⊗ₖ (1 : QMatrix D)))).trace = _
  rw [← trace_submatrix_equiv (companionGrouping (A := A) (B := B) (C := C) (D := D)),
    ← Matrix.submatrix_mul_equiv (e₂ := companionGrouping (A := A) (B := B) (C := C) (D := D)),
    companionEffect_grouping, trace_mul_tensor_one, ← testedMarginal_eq_partialTrace]

theorem companionApply_probability (M : OneWayPOVM A B X Y)
    (s : Finset (X × Y)) (ρ : QMatrix ((A × C) × (B × D))) :
    (companionApply M s ρ).trace.re = ∑ z ∈ s, oneWayOutcome M (testedMarginal ρ) z.1 z.2 := by
  rw [companionApply_trace_eq_tested, coarseApply_probability]

def testedDensity (ρ : Density ((A × C) × (B × D))) : Density (A × B) where
  matrix := testedMarginal ρ.matrix
  positive := testedMarginal_posSemidef ρ.positive
  trace_one := (testedMarginal_trace _).trans ρ.trace_one

theorem testedDensity_isSeparable (ρ : Density ((A × C) × (B × D)))
    (hρ : IsSeparable ρ.matrix) : IsSeparable (testedDensity ρ).matrix := by
  have ht : (testedMarginal ρ.matrix).trace.re = 1 := by
    rw [testedMarginal_trace, ρ.trace_one, Complex.one_re]
  have h := normalize_cone_isSeparable (testedMarginal_mem_cone (isSeparable_mem_cone hρ))
    (by rw [ht]; exact zero_lt_one)
  simpa only [ht, inv_one, one_smul, testedDensity] using h

def remainderDensity (M : OneWayPOVM A B X Y) (s : Finset (X × Y))
    (ρ : Density ((A × C) × (B × D)))
    (ht : 0 < (companionApply M s ρ.matrix).trace.re) : Density (C × D) :=
  normalizedDensity (remainderMarginal (companionApply M s ρ.matrix))
    (remainderMarginal_posSemidef (coarseApply_posSemidef _ s ρ.positive))
    (by rw [remainderMarginal_trace]; exact ht)

theorem remainderDensity_isSeparable (M : OneWayPOVM A B X Y) (s : Finset (X × Y))
    (ρ : Density ((A × C) × (B × D))) (hρ : IsSeparable ρ.matrix)
    (ht : 0 < (companionApply M s ρ.matrix).trace.re) :
    IsSeparable (remainderDensity M s ρ ht).matrix :=
  normalize_cone_isSeparable
    (remainderMarginal_mem_cone (companionApply_mem_cone M s (isSeparable_mem_cone hρ)))
    (by rw [remainderMarginal_trace]; exact ht)

theorem companionApply_probability_nonneg (M : OneWayPOVM A B X Y)
    (s : Finset (X × Y)) {ρ : QMatrix ((A × C) × (B × D))} (hρ : ρ.PosSemidef) :
    0 ≤ (companionApply M s ρ).trace.re := coarseApply_probability_nonneg _ s hρ

theorem companionApply_probability_le_one (M : OneWayPOVM A B X Y)
    (s : Finset (X × Y)) (ρ : Density ((A × C) × (B × D))) :
    (companionApply M s ρ.matrix).trace.re ≤ 1 := coarseApply_probability_le_one _ s ρ

theorem companionApply_trace_complement_sum (M : OneWayPOVM A B X Y)
    (s : Finset (X × Y)) (ρ : QMatrix ((A × C) × (B × D))) :
    (companionApply M s ρ).trace + (companionApply M (Finset.univ \ s) ρ).trace = ρ.trace :=
  coarseApply_trace_complement_sum _ s ρ

end Companions

end QuantumProver.DepolarizingSquashedEntanglement.BCYMeasurement

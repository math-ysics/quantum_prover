import QuantumProver.InformationTheory.Equipartition.FamilyIdentities

noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace QuantumProver.Equipartition.FiniteModel.PermutationSpectrum
open Testing

abbrev Histogram (d n : ℕ) := (Fin d × Fin d) → Fin (n + 1)

def pairHistogram {d n : ℕ} (x y : Word d n) : Histogram d n := fun a =>
  ⟨Fintype.card {i : Fin n // (x i, y i) = a},
    Nat.lt_succ_of_le (by simpa using
      Fintype.card_subtype_le (fun i : Fin n => (x i, y i) = a))⟩

theorem exists_site_perm_of_pairHistogram_eq {d n : ℕ} {x y u v : Word d n}
    (hh : pairHistogram x y = pairHistogram u v) :
    ∃ p : Equiv.Perm (Fin n), ∀ i, (u (p i), v (p i)) = (x i, y i) := by
  let e : ∀ a : Fin d × Fin d,
      {i : Fin n // (x i, y i) = a} ≃ {i : Fin n // (u i, v i) = a} :=
    fun a => Fintype.equivOfCardEq (congrArg Fin.val (congrFun hh a))
  exact ⟨Equiv.ofFiberEquiv e, Equiv.ofFiberEquiv_map e⟩

def invariantMatrices (d n : ℕ) : Submodule ℂ (QMat d n) where
  carrier := {A | ∀ p : Equiv.Perm (Fin n), sitePermute p A = A}
  zero_mem' := by intro p; rfl
  add_mem' := by
    intro A B hA hB p
    ext x y
    exact congrArg₂ (fun a b : ℂ => a + b)
      (congrArg (fun M : QMat d n => M x y) (hA p))
      (congrArg (fun M : QMat d n => M x y) (hB p))
  smul_mem' := by
    intro c A hA p
    ext x y
    exact congrArg (fun a : ℂ => c * a)
      (congrArg (fun M : QMat d n => M x y) (hA p))

theorem invariant_entry_eq_of_pairHistogram_eq {d n : ℕ} {A : QMat d n}
    (hA : A ∈ invariantMatrices d n) {x y u v : Word d n}
    (hh : pairHistogram x y = pairHistogram u v) : A x y = A u v := by
  obtain ⟨p, hp⟩ := exists_site_perm_of_pairHistogram_eq hh
  have hx : (fun i => u (p i)) = x := funext fun i => congrArg Prod.fst (hp i)
  have hy : (fun i => v (p i)) = y := funext fun i => congrArg Prod.snd (hp i)
  have he := congrArg (fun M : QMat d n => M u v) (hA p)
  change A (fun i => u (p i)) (fun i => v (p i)) = A u v at he
  rwa [hx, hy] at he

def invariantCoordinates (d n : ℕ) : invariantMatrices d n →ₗ[ℂ] (Histogram d n → ℂ) where
  toFun A h := if hh : ∃ xy : Word d n × Word d n, pairHistogram xy.1 xy.2 = h
    then A.1 (Classical.choose hh).1 (Classical.choose hh).2 else 0
  map_add' A B := by
    ext h
    by_cases hh : ∃ xy : Word d n × Word d n, pairHistogram xy.1 xy.2 = h
    · simp only [hh, dite_true, Submodule.coe_add, Matrix.add_apply, Pi.add_apply]
    · simp only [hh, dite_false, Pi.add_apply, add_zero]
  map_smul' c A := by
    ext h
    by_cases hh : ∃ xy : Word d n × Word d n, pairHistogram xy.1 xy.2 = h
    · simp only [hh, dite_true, Submodule.coe_smul, Matrix.smul_apply, Pi.smul_apply,
        RingHom.id_apply]
    · simp only [hh, dite_false, Pi.smul_apply, smul_zero]

theorem invariantCoordinates_pair {d n : ℕ} (A : invariantMatrices d n)
    (x y : Word d n) : invariantCoordinates d n A (pairHistogram x y) = A.1 x y := by
  have hh : ∃ xy : Word d n × Word d n, pairHistogram xy.1 xy.2 = pairHistogram x y :=
    ⟨(x, y), rfl⟩
  change (if hp : ∃ xy : Word d n × Word d n,
      pairHistogram xy.1 xy.2 = pairHistogram x y
    then A.1 (Classical.choose hp).1 (Classical.choose hp).2 else 0) = A.1 x y
  rw [dif_pos hh]
  exact invariant_entry_eq_of_pairHistogram_eq A.2 (Classical.choose_spec hh)

theorem invariantCoordinates_injective (d n : ℕ) :
    Function.Injective (invariantCoordinates d n) := by
  intro A B h
  apply Subtype.ext
  ext x y
  have he := congrFun h (pairHistogram x y)
  simpa only [invariantCoordinates_pair] using he

theorem invariantMatrices_finrank_le (d n : ℕ) :
    Module.finrank ℂ (invariantMatrices d n) ≤ (n + 1) ^ (d * d) := by
  have h := (invariantCoordinates d n).finrank_le_finrank_of_injective
    (invariantCoordinates_injective d n)
  simpa only [Module.finrank_pi, Module.finrank_self, Finset.sum_const,
    Finset.card_univ, smul_eq_mul, mul_one, Histogram, Fintype.card_fun,
    Fintype.card_fin, Fintype.card_prod] using h

def wordSitePermEquiv {d n : ℕ} (p : Equiv.Perm (Fin n)) : Word d n ≃ Word d n where
  toFun x := fun i => x (p i)
  invFun x := fun i => x (p.symm i)
  left_inv x := by funext i; simp
  right_inv x := by funext i; simp

def reindexStarAlgHom {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (e : ι ≃ κ) : CMat κ →⋆ₐ[ℝ] CMat ι :=
  { (Matrix.reindexAlgEquiv ℝ ℂ e.symm).toAlgHom with
    map_star' A := by
      change Aᴴ.submatrix e e = (A.submatrix e e)ᴴ
      rw [Matrix.conjTranspose_submatrix] }

theorem sitePermute_cfc {d n : ℕ} (p : Equiv.Perm (Fin n)) (f : ℝ → ℝ)
    {A : QMat d n} (hA : A.IsHermitian) :
    sitePermute p (cfc f A) = cfc f (sitePermute p A) := by
  let e := wordSitePermEquiv (d := d) p
  have hc : Continuous (reindexStarAlgHom e) := by
    change Continuous (fun M : QMat d n => M.submatrix e e)
    fun_prop
  exact (reindexStarAlgHom e).map_cfc f A
    (A.finite_real_spectrum.continuousOn _) hc hA (hA.submatrix e)

theorem spectralPinchingProjection_siteInvariant {d n : ℕ} {σ : QMat d n}
    (hσ : σ.IsHermitian) (hinv : σ ∈ invariantMatrices d n) (k : SpectralLabels hσ) :
    spectralPinchingProjection hσ k ∈ invariantMatrices d n := by
  intro p
  rw [spectralPinchingProjection_eq_cfc, sitePermute_cfc p _ hσ, hinv p]

theorem spectralPinchingProjection_ne_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    {σ : CMat ι} (hσ : σ.IsHermitian) (k : SpectralLabels hσ) :
    spectralPinchingProjection hσ k ≠ 0 := by
  classical
  obtain ⟨j, _, hj⟩ := Finset.mem_image.mp k.property
  have hjlabel : spectralLabel hσ j = k := Subtype.ext hj
  intro hP
  let φ := Unitary.conjStarAlgAut ℂ (CMat ι) hσ.eigenvectorUnitary
  have hmap : φ (diagonalSelector (spectralLabel hσ) k) = φ 0 := by
    change spectralPinchingProjection hσ k = φ 0
    simpa using hP
  have hD := φ.injective hmap
  have he := congrArg (fun M : CMat ι => M j j) hD
  have h10 : (1 : ℂ) = 0 := by simpa [diagonalSelector, hjlabel] using he
  exact one_ne_zero h10

theorem spectralPinchingProjection_linearIndependent {ι : Type*}
    [Fintype ι] [DecidableEq ι] {σ : CMat ι} (hσ : σ.IsHermitian) :
    LinearIndependent ℂ (spectralPinchingProjection hσ) := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro c hc k
  have hm := congrArg (fun M : CMat ι => spectralPinchingProjection hσ k * M) hc
  have hz : c k • spectralPinchingProjection hσ k = 0 := by
    simpa [Finset.mul_sum, Matrix.mul_smul, spectralPinchingProjection_mul] using hm
  exact (smul_eq_zero.mp hz).resolve_right (spectralPinchingProjection_ne_zero hσ k)

theorem spectralBlockCount_le_polynomial {d n : ℕ} {σ : QMat d n}
    (hσ : σ.IsHermitian) (hinv : σ ∈ invariantMatrices d n) :
    spectralBlockCount hσ ≤ (n + 1) ^ (d * d) := by
  let P : SpectralLabels hσ → invariantMatrices d n := fun k =>
    ⟨spectralPinchingProjection hσ k, spectralPinchingProjection_siteInvariant hσ hinv k⟩
  have hP : LinearIndependent ℂ P :=
    LinearIndependent.of_comp (invariantMatrices d n).subtype
      (spectralPinchingProjection_linearIndependent hσ)
  exact hP.fintype_card_le_finrank.trans (invariantMatrices_finrank_le d n)

theorem log_spectralBlockCount_le {d n : ℕ} {σ : QMat d n}
    (hσ : σ.IsHermitian) (hinv : σ ∈ invariantMatrices d n) :
    logTwo (spectralBlockCount hσ : ℝ) ≤ (d : ℝ) ^ 2 * blockLog n := by
  by_cases hz : spectralBlockCount hσ = 0
  · simpa only [hz, Nat.cast_zero, logTwo, Real.log_zero, zero_div] using
      mul_nonneg (sq_nonneg (d : ℝ)) (blockLog_nonneg n)
  have hp := spectralBlockCount_le_polynomial hσ hinv
  have hpR : (spectralBlockCount hσ : ℝ) ≤ ((n : ℝ) + 1) ^ (d * d) := by
    exact_mod_cast hp
  have hv : 0 < (spectralBlockCount hσ : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero hz
  have hm := logTwo_mono_pos hv hpR
  have he : logTwo (((n : ℝ) + 1) ^ (d * d)) = (d : ℝ) ^ 2 * blockLog n := by
    unfold blockLog logTwo
    rw [Real.log_pow]
    simp only [Nat.cast_mul]
    ring
  rwa [he] at hm

theorem polynomialLog_le_pinchingOverhead {d n : ℕ} (hd : 0 < d) :
    (d : ℝ) ^ 2 * blockLog n ≤ pinchingOverhead d n := by
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hd
  have hm : blockLog n ≤ logTwo ((n : ℝ) + (d : ℝ)) :=
    logTwo_mono_pos (by positivity) (by linarith)
  have hc : (d : ℝ) ^ 2 ≤ 2 * ((d : ℝ) ^ 2 + (d : ℝ)) := by nlinarith
  calc
    (d : ℝ) ^ 2 * blockLog n ≤
        (d : ℝ) ^ 2 * logTwo ((n : ℝ) + (d : ℝ)) :=
      mul_le_mul_of_nonneg_left hm (sq_nonneg _)
    _ ≤ pinchingOverhead d n :=
      mul_le_mul_of_nonneg_right hc ((blockLog_nonneg n).trans hm)

theorem sitePermute_comp {d n : ℕ} (p q : Equiv.Perm (Fin n)) (A : QMat d n) :
    sitePermute p (sitePermute q A) = sitePermute (p * q) A := rfl

theorem sitePermute_real_smul {d n : ℕ} (p : Equiv.Perm (Fin n))
    (a : ℝ) (A : QMat d n) : sitePermute p (a • A) = a • sitePermute p A := rfl

theorem sitePermute_sum {d n : ℕ} {κ : Type*} [Fintype κ]
    (p : Equiv.Perm (Fin n)) (A : κ → QMat d n) :
    sitePermute p (∑ k, A k) = ∑ k, sitePermute p (A k) := by
  ext x y
  simp [sitePermute, Matrix.sum_apply]

def siteAverage {d n : ℕ} (A : QMat d n) : QMat d n :=
  (Fintype.card (Equiv.Perm (Fin n)) : ℝ)⁻¹ • ∑ p, sitePermute p A

theorem siteAverage_invariant {d n : ℕ} (A : QMat d n) :
    siteAverage A ∈ invariantMatrices d n := by
  intro p
  rw [siteAverage, sitePermute_real_smul, sitePermute_sum]
  simp only [sitePermute_comp]
  congr 1
  exact Equiv.sum_comp (Equiv.mulLeft p) (fun q => sitePermute q A)

theorem siteAverage_mem_of_convex {d n : ℕ} {S : Set (QMat d n)}
    (hS : Convex ℝ S) (hperm : ∀ p : Equiv.Perm (Fin n), ∀ A ∈ S, sitePermute p A ∈ S)
    {A : QMat d n} (hA : A ∈ S) : siteAverage A ∈ S := by
  let v : ℝ := Fintype.card (Equiv.Perm (Fin n))
  have hv : 0 < v := by dsimp [v]; exact_mod_cast Fintype.card_pos
  have hw : ∑ p : Equiv.Perm (Fin n), v⁻¹ = 1 := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact mul_inv_cancel₀ hv.ne'
  have hm := hS.sum_mem (t := Finset.univ) (w := fun _ : Equiv.Perm (Fin n) => v⁻¹)
    (z := fun p => sitePermute p A)
    (fun _ _ => inv_nonneg.mpr hv.le) hw (fun p _ => hperm p A hA)
  simpa only [siteAverage, Finset.smul_sum, v] using hm

theorem siteAverage_mem_null {d n : ℕ} {F : QuantumFamilies d}
    (hF : PhysicalAssumptions F) (hn : 0 < n) {ρ : QMat d n} (hρ : ρ ∈ F.null n) :
    siteAverage ρ ∈ F.null n :=
  siteAverage_mem_of_convex (hF.null_convex n hn) (hF.null_permutation n hn) hρ

theorem siteAverage_mem_alternative {d n : ℕ} {F : QuantumFamilies d}
    (hF : PhysicalAssumptions F) (hn : 0 < n) {σ : QMat d n} (hσ : σ ∈ F.alternative n) :
    siteAverage σ ∈ F.alternative n :=
  siteAverage_mem_of_convex (hF.alternative_convex n hn) (hF.alternative_permutation n hn) hσ

theorem physical_pair_sandwich_sub_polynomialLog_le_measured {d n : ℕ}
    {F : QuantumFamilies d} (hF : PhysicalAssumptions F) (hn : 0 < n)
    {ρ σ : QMat d n} (hρ : ρ ∈ F.null n) (hσ : σ ∈ F.alternative n)
    (hinv : σ ∈ invariantMatrices d n) {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
    sandwichedDivergence ρ σ α - (((d : ℝ) ^ 2 * blockLog n : ℝ) : EReal) ≤
      measuredDivergence ρ σ α := by
  obtain ⟨C, hC⟩ := hF.linear_growth
  have hr := hF.null_states n hn ρ hρ
  have hs := hF.alternative_positive n hn σ hσ
  have ha : 0 < Real.rpow 2 (C * (n : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
  have hb := sandwichedDivergence_sub_log_spectralCount_le_measured
    hr hs ha (hC n hn ρ hρ σ hσ).1 hα hα1
  have hl : (logTwo (spectralBlockCount hs.1 : ℝ) : EReal) ≤
      (((d : ℝ) ^ 2 * blockLog n : ℝ) : EReal) :=
    EReal.coe_le_coe (log_spectralBlockCount_le hs.1 hinv)
  exact (EReal.sub_le_sub (le_refl (sandwichedDivergence ρ σ α)) hl).trans hb

end QuantumProver.Equipartition.FiniteModel.PermutationSpectrum

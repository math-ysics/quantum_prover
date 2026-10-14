import Mathlib

set_option autoImplicit false

noncomputable section

open scoped BigOperators ComplexConjugate ComplexOrder Matrix Kronecker

namespace QuantumProver.AmplitudeDamping.FiniteModel

variable {I O Z : Type*} [Fintype I] [Fintype O] [Fintype Z]
  [DecidableEq I] [DecidableEq O]

def krausSumB (K : Z → Matrix O I ℂ) (ρ : Matrix I I ℂ) : Matrix O O ℂ :=
  ∑ z, K z * ρ * (K z)ᴴ

theorem krausSumB_posSemidef (K : Z → Matrix O I ℂ)
    {ρ : Matrix I I ℂ} (hρ : ρ.PosSemidef) : (krausSumB K ρ).PosSemidef := by
  exact Matrix.posSemidef_sum _ fun z _ => hρ.mul_mul_conjTranspose_same (K z)

theorem krausSumB_smul (K : Z → Matrix O I ℂ) (a : ℂ)
    (ρ : Matrix I I ℂ) :
    krausSumB (fun z => a • K z) ρ = (star a * a) • krausSumB K ρ := by
  simp only [krausSumB, Matrix.conjTranspose_smul, Matrix.smul_mul,
    Matrix.mul_smul, smul_smul, ← Finset.smul_sum]

def referenceKrausB (K : Z → Matrix O I ℂ)
    (R : Type*) [Fintype R] [DecidableEq R] :
    Z → Matrix (O × R) (I × R) ℂ :=
  fun z => K z ⊗ₖ (1 : Matrix R R ℂ)

theorem referenceKrausB_smul (K : Z → Matrix O I ℂ) (a : ℂ)
    (R : Type*) [Fintype R] [DecidableEq R] :
    referenceKrausB (fun z => a • K z) R = fun z => a • referenceKrausB K R z := by
  funext z
  exact Matrix.smul_kronecker _ _ _

theorem krausSumB_reference_smul (K : Z → Matrix O I ℂ) (a : ℂ)
    (R : Type*) [Fintype R] [DecidableEq R]
    (ρ : Matrix (I × R) (I × R) ℂ) :
    krausSumB (referenceKrausB (fun z => a • K z) R) ρ =
      (star a * a) • krausSumB (referenceKrausB K R) ρ := by
  rw [referenceKrausB_smul, krausSumB_smul]

theorem referenceKrausB_block (K : Z → Matrix O I ℂ)
    (R : Type*) [Fintype R] [DecidableEq R]
    (z : Z) (ρ : Matrix (I × R) (I × R) ℂ)
    (o p : O) (r s : R) :
    (referenceKrausB K R z * ρ * (referenceKrausB K R z)ᴴ) (o, r) (p, s) =
      (K z * Matrix.of (fun i j => ρ (i, r) (j, s)) * (K z)ᴴ) o p := by
  simp [referenceKrausB, Matrix.mul_apply, Matrix.kronecker_apply,
    Matrix.one_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type,
    Matrix.of_apply, apply_ite, mul_ite, ite_mul]

theorem krausSumB_entry (K : Z → Matrix O I ℂ) (ρ : Matrix I I ℂ) (o p : O) :
    krausSumB K ρ o p =
      ∑ j, ∑ i, (∑ z, K z o i * star (K z p j)) * ρ i j := by
  simp only [krausSumB, Matrix.sum_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro z _
  ring

theorem krausSumB_eq_of_coefficients {J : Type*} [Fintype J]
    (K : Z → Matrix O I ℂ) (L : J → Matrix O I ℂ)
    (h : ∀ o p i j, (∑ z, K z o i * star (K z p j)) =
      ∑ x, L x o i * star (L x p j)) (ρ : Matrix I I ℂ) :
    krausSumB K ρ = krausSumB L ρ := by
  ext o p
  simp only [krausSumB_entry, h]

theorem krausSumB_reference_congr {J : Type*} [Fintype J]
    (K : Z → Matrix O I ℂ) (L : J → Matrix O I ℂ)
    (h : ∀ ρ : Matrix I I ℂ, krausSumB K ρ = krausSumB L ρ)
    (R : Type*) [Fintype R] [DecidableEq R]
    (ρ : Matrix (I × R) (I × R) ℂ) :
    krausSumB (referenceKrausB K R) ρ = krausSumB (referenceKrausB L R) ρ := by
  ext ⟨o, r⟩ ⟨p, s⟩
  simp only [krausSumB, Matrix.sum_apply, referenceKrausB_block]
  simpa only [krausSumB, Matrix.sum_apply] using
    congrArg (fun M : Matrix O O ℂ => M o p)
      (h (Matrix.of (fun i j => ρ (i, r) (j, s))))

theorem krausSumB_reference_posSemidef (K : Z → Matrix O I ℂ)
    (R : Type*) [Fintype R] [DecidableEq R]
    {ρ : Matrix (I × R) (I × R) ℂ} (hρ : ρ.PosSemidef) :
    (krausSumB (referenceKrausB K R) ρ).PosSemidef :=
  krausSumB_posSemidef _ hρ

theorem referenceKrausB_gram (K : Z → Matrix O I ℂ)
    (R : Type*) [Fintype R] [DecidableEq R] :
    (∑ z, (referenceKrausB K R z)ᴴ * referenceKrausB K R z) =
      (∑ z, (K z)ᴴ * K z) ⊗ₖ (1 : Matrix R R ℂ) := by
  simp only [referenceKrausB, Matrix.conjTranspose_kronecker,
    Matrix.conjTranspose_one, ← Matrix.mul_kronecker_mul, Matrix.one_mul]
  ext i j
  simp [Matrix.sum_apply, Matrix.kronecker_apply, Finset.sum_mul]

theorem referenceKrausB_complete (K : Z → Matrix O I ℂ)
    (hK : ∑ z, (K z)ᴴ * K z = 1)
    (R : Type*) [Fintype R] [DecidableEq R] :
    ∑ z, (referenceKrausB K R z)ᴴ * referenceKrausB K R z = 1 := by
  rw [referenceKrausB_gram, hK, Matrix.one_kronecker_one]

theorem krausSumB_trace (K : Z → Matrix O I ℂ) (ρ : Matrix I I ℂ) :
    (krausSumB K ρ).trace = ((∑ z, (K z)ᴴ * K z) * ρ).trace := by
  simp only [krausSumB, Matrix.trace_sum, Matrix.sum_mul]
  apply Finset.sum_congr rfl
  intro z _
  exact Matrix.trace_mul_cycle _ _ _

theorem krausSumB_trace_preserving (K : Z → Matrix O I ℂ)
    (hK : ∑ z, (K z)ᴴ * K z = 1) (ρ : Matrix I I ℂ) :
    (krausSumB K ρ).trace = ρ.trace := by
  rw [krausSumB_trace, hK, Matrix.one_mul]

theorem krausSumB_reference_subfamily_residual [DecidableEq Z]
    (K : Z → Matrix O I ℂ) (selected : Finset Z)
    (R : Type*) [Fintype R] [DecidableEq R]
    {ρ : Matrix (I × R) (I × R) ℂ} (hρ : ρ.PosSemidef) :
    (krausSumB (referenceKrausB K R) ρ -
      ∑ z ∈ selected, referenceKrausB K R z * ρ *
        (referenceKrausB K R z)ᴴ).PosSemidef := by
  rw [krausSumB, ← Finset.sum_sdiff_eq_sub (Finset.subset_univ selected)]
  exact Matrix.posSemidef_sum _ fun z _ =>
    hρ.mul_mul_conjTranspose_same (referenceKrausB K R z)

abbrev WeightBasisB (n w : ℕ) := {S : Finset (Fin n) // S.card = w}

def rawLossKrausB (n w r : ℕ) (L : Finset (Fin n)) :
    Matrix (Finset (Fin n)) (WeightBasisB n w) ℂ :=
  fun T S => if L ∈ S.val.powersetCard (w - r) ∧ T = S.val \ L then 1 else 0

theorem deletion_injectiveB {n : ℕ} {S U L : Finset (Fin n)}
    (hLS : L ⊆ S) (hLU : L ⊆ U) (h : S \ L = U \ L) : S = U := by
  calc
    S = (S \ L) ∪ L := (Finset.sdiff_union_of_subset hLS).symm
    _ = (U \ L) ∪ L := by rw [h]
    _ = U := Finset.sdiff_union_of_subset hLU

theorem rawLossKrausB_survivor_support {n w r : ℕ} (hr : r ≤ w)
    (L T : Finset (Fin n)) (S : WeightBasisB n w)
    (h : rawLossKrausB n w r L T S ≠ 0) : T.card = r := by
  have hcond : L ∈ S.val.powersetCard (w - r) ∧ T = S.val \ L := by
    by_contra hc
    exact h (by change (if L ∈ S.val.powersetCard (w - r) ∧ T = S.val \ L
      then (1 : ℂ) else 0) = 0; rw [if_neg hc])
  rcases Finset.mem_powersetCard.mp hcond.1 with ⟨hLS, hL⟩
  rw [hcond.2, Finset.card_sdiff_of_subset hLS, S.property, hL]
  omega

theorem rawLossKrausB_gram_entry (n w r : ℕ) (L : Finset (Fin n))
    (S U : WeightBasisB n w) :
    ((rawLossKrausB n w r L)ᴴ * rawLossKrausB n w r L) S U =
      if L ∈ S.val.powersetCard (w - r) ∧ S = U then 1 else 0 := by
  classical
  by_cases hS : L ∈ S.val.powersetCard (w - r)
  · by_cases hU : L ∈ U.val.powersetCard (w - r)
    · have hiff : S.val \ L = U.val \ L ↔ S = U := by
        constructor
        · intro h
          apply Subtype.ext
          exact deletion_injectiveB (Finset.mem_powersetCard.mp hS).1
            (Finset.mem_powersetCard.mp hU).1 h
        · rintro rfl
          rfl
      have hiff' : U.val \ L = S.val \ L ↔ S = U :=
        ⟨fun h => hiff.mp h.symm, fun h => (hiff.mpr h).symm⟩
      simp [Matrix.mul_apply, Matrix.conjTranspose_apply, rawLossKrausB,
        hS, hU, ite_mul, mul_ite, hiff']
    · have hne : S ≠ U := by rintro rfl; exact hU hS
      simp [Matrix.mul_apply, Matrix.conjTranspose_apply, rawLossKrausB, hS, hU, hne]
  · simp [Matrix.mul_apply, Matrix.conjTranspose_apply, rawLossKrausB, hS]

theorem rawLossKrausB_gram (n w r : ℕ) (hr : r ≤ w) :
    (∑ L : Finset (Fin n), (rawLossKrausB n w r L)ᴴ * rawLossKrausB n w r L) =
      (w.choose r : ℂ) • (1 : Matrix (WeightBasisB n w) (WeightBasisB n w) ℂ) := by
  classical
  ext S U
  simp only [Matrix.sum_apply, rawLossKrausB_gram_entry, Matrix.smul_apply,
    smul_eq_mul, Matrix.one_apply]
  by_cases hSU : S = U
  · subst U
    have hfilter : (Finset.univ : Finset (Finset (Fin n))).filter
        (fun L => L ∈ S.val.powersetCard (w - r)) = S.val.powersetCard (w - r) := by
      ext L
      simp
    simp only [and_true, ite_true, mul_one]
    rw [Finset.sum_ite, hfilter]
    simp [Finset.card_powersetCard, S.property, Nat.choose_symm hr]
  · simp [hSU]

def lossNormalizerB (w r : ℕ) : ℂ := (Real.sqrt (w.choose r : ℝ) : ℂ)⁻¹

def lossKrausB (n w r : ℕ) (L : Finset (Fin n)) :
    Matrix (Finset (Fin n)) (WeightBasisB n w) ℂ :=
  lossNormalizerB w r • rawLossKrausB n w r L

theorem lossNormalizerB_norm (w r : ℕ) :
    star (lossNormalizerB w r) * lossNormalizerB w r = (w.choose r : ℂ)⁻¹ := by
  simp [lossNormalizerB, ← mul_inv, ← Complex.ofReal_mul,
    Real.mul_self_sqrt (Nat.cast_nonneg (w.choose r))]

theorem lossKrausB_complete (n w r : ℕ) (hr : r ≤ w) :
    ∑ L : Finset (Fin n), (lossKrausB n w r L)ᴴ * lossKrausB n w r L = 1 := by
  have hd : (w.choose r : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.choose_pos hr).ne'
  simp only [lossKrausB, Matrix.conjTranspose_smul, Matrix.smul_mul,
    Matrix.mul_smul, smul_smul, ← Finset.smul_sum]
  rw [mul_comm (lossNormalizerB w r) (star (lossNormalizerB w r))]
  rw [lossNormalizerB_norm, rawLossKrausB_gram n w r hr]
  simp [smul_smul, hd]

theorem lossKrausB_reference_complete (n w r : ℕ) (hr : r ≤ w)
    (R : Type*) [Fintype R] [DecidableEq R] :
    ∑ L : Finset (Fin n), (referenceKrausB (lossKrausB n w r) R L)ᴴ *
      referenceKrausB (lossKrausB n w r) R L = 1 :=
  referenceKrausB_complete _ (lossKrausB_complete n w r hr) R

theorem lossChannelB_reference_trace_preserving (n w r : ℕ) (hr : r ≤ w)
    (R : Type*) [Fintype R] [DecidableEq R]
    (ρ : Matrix (WeightBasisB n w × R) (WeightBasisB n w × R) ℂ) :
    (krausSumB (referenceKrausB (lossKrausB n w r) R) ρ).trace = ρ.trace :=
  krausSumB_trace_preserving _ (lossKrausB_reference_complete n w r hr R) ρ

theorem lossChannelB_reference_eq (n w r : ℕ)
    (R : Type*) [Fintype R] [DecidableEq R]
    (ρ : Matrix (WeightBasisB n w × R) (WeightBasisB n w × R) ℂ) :
    krausSumB (referenceKrausB (lossKrausB n w r) R) ρ =
      (w.choose r : ℝ)⁻¹ • krausSumB (referenceKrausB (rawLossKrausB n w r) R) ρ := by
  change krausSumB (referenceKrausB
    (fun L => lossNormalizerB w r • rawLossKrausB n w r L) R) ρ = _
  rw [krausSumB_reference_smul, lossNormalizerB_norm]
  have hcoeff : (w.choose r : ℂ)⁻¹ = Complex.ofReal ((w.choose r : ℝ)⁻¹) := by
    simp
  rw [hcoeff, Complex.coe_smul]

def physicalBitEntryB (p : ℝ) : Bool → Bool → Bool → ℂ
  | false, false, false => 1
  | false, true, true => (Real.sqrt (1 - p) : ℂ)
  | true, false, true => (Real.sqrt p : ℂ)
  | _, _, _ => 0

def physicalTensorKrausB (n : ℕ) (p : ℝ) (L : Finset (Fin n)) :
    Matrix (Finset (Fin n)) (Finset (Fin n)) ℂ :=
  fun T S => ∏ i : Fin n, physicalBitEntryB p
    (decide (i ∈ L)) (decide (i ∈ T)) (decide (i ∈ S))

def physicalSectorKrausB (n w : ℕ) (p : ℝ) (L : Finset (Fin n)) :
    Matrix (Finset (Fin n)) (WeightBasisB n w) ℂ :=
  fun T S => physicalTensorKrausB n p L T S.val

theorem prod_membership_constantB {A : Type*} [Fintype A] [DecidableEq A]
    (S : Finset A) (a : ℂ) :
    (∏ i : A, if i ∈ S then a else 1) = a ^ S.card := by
  simp [Finset.prod_ite]

theorem physicalTensorKrausB_entry (n : ℕ) (p : ℝ) (L T S : Finset (Fin n)) :
    physicalTensorKrausB n p L T S =
      if L ⊆ S ∧ T = S \ L then
        (Real.sqrt (1 - p) : ℂ) ^ T.card * (Real.sqrt p : ℂ) ^ L.card
      else 0 := by
  classical
  change (∏ i : Fin n, physicalBitEntryB p
    (decide (i ∈ L)) (decide (i ∈ T)) (decide (i ∈ S))) = _
  by_cases hLS : L ⊆ S
  · by_cases hT : T = S \ L
    · subst T
      rw [if_pos ⟨hLS, rfl⟩]
      have hentry (i : Fin n) : physicalBitEntryB p
          (decide (i ∈ L)) (decide (i ∈ S \ L)) (decide (i ∈ S)) =
          (if i ∈ S \ L then (Real.sqrt (1 - p) : ℂ) else 1) *
            (if i ∈ L then (Real.sqrt p : ℂ) else 1) := by
        have himp : i ∈ L → i ∈ S := fun hi => hLS hi
        by_cases hiS : i ∈ S <;> by_cases hiL : i ∈ L <;>
          simp_all [physicalBitEntryB, Finset.mem_sdiff]
      simp_rw [hentry]
      rw [Finset.prod_mul_distrib, prod_membership_constantB,
        prod_membership_constantB]
    · rw [if_neg (fun h => hT h.2)]
      have hdiff : ∃ i : Fin n, ¬(i ∈ T ↔ i ∈ S \ L) := by
        by_contra h
        push_neg at h
        exact hT (Finset.ext h)
      obtain ⟨i, hi⟩ := hdiff
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      by_cases hiL : i ∈ L <;> by_cases hiT : i ∈ T <;> by_cases hiS : i ∈ S <;>
        simp_all [physicalBitEntryB, Finset.mem_sdiff]
  · rw [if_neg (fun h => hLS h.1)]
    have hnot := hLS
    change ¬∀ i : Fin n, i ∈ L → i ∈ S at hnot
    push_neg at hnot
    obtain ⟨i, hiL, hiS⟩ := hnot
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    by_cases hiT : i ∈ T <;> simp [physicalBitEntryB, hiL, hiS, hiT]

def physicalCoefficientB (p : ℝ) (w r : ℕ) : ℂ :=
  (Real.sqrt (1 - p) : ℂ) ^ r * (Real.sqrt p : ℂ) ^ (w - r)

theorem physicalSectorKrausB_eq_rawLoss (n w r : ℕ) (hr : r ≤ w)
    (p : ℝ) (L : Finset (Fin n)) (hL : L.card = w - r) :
    physicalSectorKrausB n w p L = physicalCoefficientB p w r • rawLossKrausB n w r L := by
  ext T S
  change physicalTensorKrausB n p L T S.val = _
  rw [physicalTensorKrausB_entry]
  simp only [Matrix.smul_apply, smul_eq_mul, rawLossKrausB,
    Finset.mem_powersetCard, hL, and_true]
  by_cases h : L ⊆ S.val ∧ T = S.val \ L
  · rw [if_pos h, if_pos h, mul_one]
    have hT : T.card = r := by
      rw [h.2, Finset.card_sdiff_of_subset h.1, S.property, hL]
      omega
    simp only [physicalCoefficientB, hT, hL]
  · rw [if_neg h, if_neg h, mul_zero]

def physicalSurvivorKrausB (n w r : ℕ) (p : ℝ) (L : Finset (Fin n)) :
    Matrix (Finset (Fin n)) (WeightBasisB n w) ℂ :=
  if L.card = w - r then physicalSectorKrausB n w p L else 0

theorem physicalSurvivorKrausB_eq (n w r : ℕ) (hr : r ≤ w)
    (p : ℝ) (L : Finset (Fin n)) :
    physicalSurvivorKrausB n w r p L =
      physicalCoefficientB p w r • rawLossKrausB n w r L := by
  by_cases hL : L.card = w - r
  · rw [physicalSurvivorKrausB, if_pos hL]
    exact physicalSectorKrausB_eq_rawLoss n w r hr p L hL
  · ext T S
    simp [physicalSurvivorKrausB, hL, rawLossKrausB, Finset.mem_powersetCard,
      Matrix.smul_apply]

def physicalSurvivorProbabilityB (p : ℝ) (w r : ℕ) : ℝ :=
  (w.choose r : ℝ) * (1 - p) ^ r * p ^ (w - r)

theorem physicalCoefficientB_norm (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (w r : ℕ) :
    star (physicalCoefficientB p w r) * physicalCoefficientB p w r =
      Complex.ofReal ((1 - p) ^ r * p ^ (w - r)) := by
  have hq : (Real.sqrt (1 - p) : ℂ) * (Real.sqrt (1 - p) : ℂ) =
      Complex.ofReal (1 - p) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (sub_nonneg.mpr hp1)]
  have hp : (Real.sqrt p : ℂ) * (Real.sqrt p : ℂ) = Complex.ofReal p := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hp0]
  simp only [physicalCoefficientB, star_mul, star_pow]
  have hstarQ : star (Real.sqrt (1 - p) : ℂ) = (Real.sqrt (1 - p) : ℂ) := by simp
  have hstarP : star (Real.sqrt p : ℂ) = (Real.sqrt p : ℂ) := by simp
  rw [hstarQ, hstarP]
  calc
    _ = ((Real.sqrt (1 - p) : ℂ) * (Real.sqrt (1 - p) : ℂ)) ^ r *
        ((Real.sqrt p : ℂ) * (Real.sqrt p : ℂ)) ^ (w - r) := by
          rw [mul_pow, mul_pow]
          ring
    _ = _ := by rw [hq, hp]; simp

theorem physicalSurvivorChannelB_reference_eq (n w r : ℕ) (hr : r ≤ w)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (R : Type*) [Fintype R] [DecidableEq R]
    (ρ : Matrix (WeightBasisB n w × R) (WeightBasisB n w × R) ℂ) :
    krausSumB (referenceKrausB (physicalSurvivorKrausB n w r p) R) ρ =
      physicalSurvivorProbabilityB p w r •
        krausSumB (referenceKrausB (lossKrausB n w r) R) ρ := by
  have hd : (w.choose r : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.choose_pos hr).ne'
  have hfamily : physicalSurvivorKrausB n w r p =
      fun L => physicalCoefficientB p w r • rawLossKrausB n w r L := by
    funext L
    exact physicalSurvivorKrausB_eq n w r hr p L
  rw [hfamily, krausSumB_reference_smul, physicalCoefficientB_norm p hp0 hp1,
    Complex.coe_smul, lossChannelB_reference_eq, smul_smul]
  congr 1
  simp only [physicalSurvivorProbabilityB]
  field_simp [hd] <;> ring

theorem physicalSurvivorChannelB_reference_trace (n w r : ℕ) (hr : r ≤ w)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (R : Type*) [Fintype R] [DecidableEq R]
    (ρ : Matrix (WeightBasisB n w × R) (WeightBasisB n w × R) ℂ) :
    (krausSumB (referenceKrausB (physicalSurvivorKrausB n w r p) R) ρ).trace =
      (physicalSurvivorProbabilityB p w r : ℂ) * ρ.trace := by
  rw [physicalSurvivorChannelB_reference_eq n w r hr p hp0 hp1,
    Matrix.trace_smul, lossChannelB_reference_trace_preserving n w r hr]
  rfl

theorem physicalSectorKrausB_zero_of_card_gt (n w : ℕ) (p : ℝ)
    (L : Finset (Fin n)) (hL : w < L.card) : physicalSectorKrausB n w p L = 0 := by
  ext T S
  have hnot : ¬L ⊆ S.val := by
    intro h
    have hc := Finset.card_le_card h
    rw [S.property] at hc
    omega
  simp [physicalSectorKrausB, physicalTensorKrausB_entry, hnot]

theorem physicalSurvivorKrausB_sandwich (n w r : ℕ) (p : ℝ)
    (L : Finset (Fin n)) (R : Type*) [Fintype R] [DecidableEq R]
    (ρ : Matrix (WeightBasisB n w × R) (WeightBasisB n w × R) ℂ) :
    referenceKrausB (physicalSurvivorKrausB n w r p) R L * ρ *
        (referenceKrausB (physicalSurvivorKrausB n w r p) R L)ᴴ =
      if L.card = w - r then
        referenceKrausB (physicalSectorKrausB n w p) R L * ρ *
          (referenceKrausB (physicalSectorKrausB n w p) R L)ᴴ
      else 0 := by
  by_cases h : L.card = w - r <;>
    simp [physicalSurvivorKrausB, referenceKrausB, h]

theorem physicalSectorChannelB_reference_sum_branches (n w : ℕ) (p : ℝ)
    (R : Type*) [Fintype R] [DecidableEq R]
    (ρ : Matrix (WeightBasisB n w × R) (WeightBasisB n w × R) ℂ) :
    krausSumB (referenceKrausB (physicalSectorKrausB n w p) R) ρ =
      ∑ r ∈ Finset.range (w + 1),
        krausSumB (referenceKrausB (physicalSurvivorKrausB n w r p) R) ρ := by
  classical
  simp only [krausSumB]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro L _
  simp_rw [physicalSurvivorKrausB_sandwich]
  by_cases hL : L.card ≤ w
  · have hmem : w - L.card ∈ Finset.range (w + 1) := by
      simp only [Finset.mem_range]
      omega
    rw [Finset.sum_eq_single (w - L.card)]
    · simp [Nat.sub_sub_self hL]
    · intro r hr hne
      have hrw : r ≤ w := by have := Finset.mem_range.mp hr; omega
      have hcard : L.card ≠ w - r := by intro he; omega
      simp [hcard]
    · simp [hmem]
  · have hgt : w < L.card := by omega
    have hz := physicalSectorKrausB_zero_of_card_gt n w p L hgt
    have hsum : (∑ r ∈ Finset.range (w + 1),
        if L.card = w - r then
          referenceKrausB (physicalSectorKrausB n w p) R L * ρ *
            (referenceKrausB (physicalSectorKrausB n w p) R L)ᴴ
        else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro r hr
      have hcard : L.card ≠ w - r := by omega
      simp [hcard]
    rw [hsum]
    simp [referenceKrausB, hz]

theorem physicalSectorChannelB_reference_eq (n w : ℕ)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (R : Type*) [Fintype R] [DecidableEq R]
    (ρ : Matrix (WeightBasisB n w × R) (WeightBasisB n w × R) ℂ) :
    krausSumB (referenceKrausB (physicalSectorKrausB n w p) R) ρ =
      ∑ r ∈ Finset.range (w + 1), physicalSurvivorProbabilityB p w r •
        krausSumB (referenceKrausB (lossKrausB n w r) R) ρ := by
  rw [physicalSectorChannelB_reference_sum_branches]
  apply Finset.sum_congr rfl
  intro r hr
  have hrw : r ≤ w := by have := Finset.mem_range.mp hr; omega
  exact physicalSurvivorChannelB_reference_eq n w r hrw p hp0 hp1 R ρ

end QuantumProver.AmplitudeDamping.FiniteModel

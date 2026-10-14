import QuantumProver.InformationTheory.VisibleCompression.Definitions

/-!
# The explicit finite dimension-nine complement ensemble

The fixed label alphabet contains nine standard-basis labels and all eight
independent cube-root phases with the first coordinate fixed. We use symbolic
root-of-unity identities and finite-product sums, never enumeration of labels.
-/

noncomputable section

namespace VisibleCompression

open Matrix
open scoped BigOperators ComplexOrder

/-- Von Neumann entropy in bits, using the actual density-matrix spectrum. -/
def densityEntropyBits {B : Type*} [Fintype B] [DecidableEq B]
    (ρ : Density B) : ℝ :=
  -∑ i, ρ.positive.isHermitian.eigenvalues i *
    log2 (ρ.positive.isHermitian.eigenvalues i)

namespace D9

abbrev Phase := Fin 8 → Fin 3
abbrev Label := Fin 9 ⊕ Phase

theorem label_card : Fintype.card Label = 6570 := by
  simp only [Label, Phase, Fintype.card_sum, Fintype.card_fun, Fintype.card_fin]
  norm_num

def weight : Label → ℝ
  | .inl _ => 1 / 90
  | .inr _ => 1 / 7290

theorem weight_pos (x : Label) : 0 < weight x := by
  cases x <;> norm_num [weight]

theorem weight_sum : ∑ x, weight x = 1 := by
  simp only [Fintype.sum_sum_type, weight, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, Fintype.card_fin, Phase, Fintype.card_fun]
  norm_num

def p : ProbWeights Label where
  weight := weight
  nonneg x := (weight_pos x).le
  normalized := weight_sum

theorem p_fullSupport : p.FullSupport := weight_pos

def zeta : ℂ := Complex.exp (2 * Real.pi * Complex.I / 3)

theorem zeta_primitive : IsPrimitiveRoot zeta 3 :=
  Complex.isPrimitiveRoot_exp 3 (by norm_num)

theorem zeta_norm : ‖zeta‖ = 1 := zeta_primitive.norm'_eq_one (by norm_num)

theorem zeta_pow_three : zeta ^ 3 = 1 := zeta_primitive.pow_eq_one

def phaseVector (r : Phase) : Fin 9 → ℂ :=
  Fin.cases (1 / 3) (fun j => zeta ^ (r j).val / 3)

def u : Label → Fin 9 → ℂ
  | .inl i => Pi.single i 1
  | .inr r => phaseVector r

theorem phaseVector_norm (r : Phase) (i : Fin 9) : ‖phaseVector r i‖ = 1 / 3 := by
  refine Fin.cases ?_ (fun j => ?_) i
  · norm_num [phaseVector]
  · simp [phaseVector, norm_div, norm_pow, zeta_norm]

theorem phaseVector_star_mul (r : Phase) (i : Fin 9) :
    star (phaseVector r i) * phaseVector r i = (1 / 9 : ℂ) := by
  have h := RCLike.conj_mul (phaseVector r i)
  rw [phaseVector_norm] at h
  norm_num at h
  exact h

theorem u_unit (x : Label) : star (u x) ⬝ᵥ u x = 1 := by
  cases x with
  | inl i => simp [u, dotProduct, Pi.star_apply, Pi.single_apply]
  | inr r =>
    simp only [u, dotProduct, Pi.star_apply, phaseVector_star_mul]
    norm_num

def Q (x : Label) : Matrix (Fin 9) (Fin 9) ℂ :=
  Matrix.vecMulVec (u x) (star (u x))

def P (x : Label) : Matrix (Fin 9) (Fin 9) ℂ := 1 - Q x

def signalMatrix (x : Label) : Matrix (Fin 9) (Fin 9) ℂ := (1 / 8 : ℝ) • P x

theorem Q_posSemidef (x : Label) : (Q x).PosSemidef :=
  Matrix.posSemidef_vecMulVec_self_star (u x)

theorem Q_trace (x : Label) : (Q x).trace = 1 := by
  rw [Q, Matrix.trace_vecMulVec, dotProduct_comm, u_unit]

theorem Q_idempotent (x : Label) : Q x * Q x = Q x := by
  rw [Q, Matrix.vecMulVec_mul_vecMulVec, u_unit, one_smul]

theorem P_hermitian (x : Label) : (P x).IsHermitian :=
  Matrix.isHermitian_one.sub (Q_posSemidef x).isHermitian

theorem P_idempotent (x : Label) : P x * P x = P x := by
  simp only [P, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
    Q_idempotent]
  abel

theorem P_posSemidef (x : Label) : (P x).PosSemidef := by
  have h := Matrix.posSemidef_conjTranspose_mul_self (P x)
  rwa [(P_hermitian x).eq, P_idempotent] at h

theorem P_trace (x : Label) : (P x).trace = 8 := by
  rw [P, Matrix.trace_sub, Q_trace]
  norm_num

theorem signalMatrix_posSemidef (x : Label) : (signalMatrix x).PosSemidef :=
  (P_posSemidef x).smul (show (0 : ℝ) ≤ 1 / 8 by norm_num)

theorem signalMatrix_trace (x : Label) : (signalMatrix x).trace = 1 := by
  rw [signalMatrix, Matrix.trace_smul, P_trace]
  norm_num [smul_eq_mul]

def W (x : Label) : Density (Fin 9) where
  mat := signalMatrix x
  positive := signalMatrix_posSemidef x
  normalized := signalMatrix_trace x

theorem W_quadratic (x : Label) : (W x).mat * (W x).mat = (1 / 8 : ℝ) • (W x).mat := by
  change ((1 / 8 : ℝ) • P x) * ((1 / 8 : ℝ) • P x) = _
  rw [Matrix.smul_mul, Matrix.mul_smul, P_idempotent]
  rfl

/-- The actual eigenvalues of each complement density are zero or 1/8. -/
theorem W_eigenvalues (x : Label) (i : Fin 9) :
    (W x).positive.isHermitian.eigenvalues i = 0 ∨
      (W x).positive.isHermitian.eigenvalues i = 1 / 8 := by
  let h := (W x).positive.isHermitian
  have he : ⇑(h.eigenvectorBasis i) ≠ 0 := by
    intro hz
    apply h.eigenvectorBasis.orthonormal.ne_zero i
    exact (WithLp.ofLp_eq_zero 2).mp hz
  have hv := congrArg (fun A : Matrix (Fin 9) (Fin 9) ℂ =>
    A *ᵥ ⇑(h.eigenvectorBasis i)) (W_quadratic x)
  simp only [← Matrix.mulVec_mulVec, h.mulVec_eigenvectorBasis,
    Matrix.mulVec_smul, Matrix.smul_mulVec, smul_smul] at hv
  have hscalar := smul_left_injective ℝ he hv
  have hpoly : h.eigenvalues i * (h.eigenvalues i - 1 / 8) = 0 := by
    nlinarith [hscalar]
  exact (mul_eq_zero.mp hpoly).imp id (fun hz => sub_eq_zero.mp hz)

theorem W_sum_eigenvalues (x : Label) :
    ∑ i, (W x).positive.isHermitian.eigenvalues i = 1 := by
  have h := congrArg (fun z : ℂ => RCLike.re z)
    (W x).positive.isHermitian.trace_eq_sum_eigenvalues
  rw [(W x).normalized] at h
  simpa only [map_sum, RCLike.ofReal_re, RCLike.one_re] using h.symm

/-- This is the spectral entropy of the actual constructed density matrix. -/
theorem W_entropy (x : Label) : densityEntropyBits (W x) = log2 8 := by
  have hterm (i : Fin 9) :
      (W x).positive.isHermitian.eigenvalues i *
          log2 ((W x).positive.isHermitian.eigenvalues i) =
        (W x).positive.isHermitian.eigenvalues i * log2 (1 / 8) := by
    rcases W_eigenvalues x i with hz | he
    · rw [hz, zero_mul, zero_mul]
    · rw [he]
  unfold densityEntropyBits
  simp_rw [hterm]
  rw [← Finset.sum_mul, W_sum_eigenvalues, one_mul]
  unfold log2
  rw [show (1 / 8 : ℝ) = (8 : ℝ)⁻¹ by norm_num, Real.log_inv]
  ring

theorem zeta_power_unit (k : ℕ) : zeta ^ k * (starRingEnd ℂ) (zeta ^ k) = 1 := by
  have h := RCLike.mul_conj (zeta ^ k)
  norm_num [norm_pow, zeta_norm] at h
  simpa only [map_pow] using h

theorem zeta_power_cube (k : ℕ) : (zeta ^ k) ^ 3 = 1 := by
  rw [← pow_mul, Nat.mul_comm, pow_mul, zeta_pow_three, one_pow]

/-- The only scalar character average needed below. The exponents count
at most two occurrences of an output coordinate. -/
theorem cube_phase_sum (a b : ℕ) (ha : a < 3) (hb : b < 3) :
    (∑ t : Fin 3, (zeta ^ t.val) ^ a * star ((zeta ^ t.val) ^ b)) =
      if a = b then (3 : ℂ) else 0 := by
  simp only [RCLike.star_def]
  by_cases hab : a = b
  · subst b
    rw [if_pos rfl]
    have ht (t : Fin 3) :
        (zeta ^ t.val) ^ a * (starRingEnd ℂ) ((zeta ^ t.val) ^ a) = (1 : ℂ) := by
      rw [← pow_mul]
      exact zeta_power_unit _
    simp_rw [ht]
    norm_num
  · rw [if_neg hab]
    let c := zeta ^ a * (starRingEnd ℂ) (zeta ^ b)
    have hc3 : c ^ 3 = 1 := by
      dsimp [c]
      rw [mul_pow, zeta_power_cube, ← map_pow, zeta_power_cube]
      simp
    have hc : c ≠ 1 := by
      intro he
      have hm := congrArg (fun z : ℂ => z * zeta ^ b) he
      have hu : (starRingEnd ℂ) (zeta ^ b) * zeta ^ b = 1 := by
        rw [mul_comm, zeta_power_unit]
      dsimp [c] at hm
      rw [mul_assoc, hu, mul_one, one_mul] at hm
      exact hab (zeta_primitive.pow_inj ha hb hm)
    have ht (t : Fin 3) :
        (zeta ^ t.val) ^ a * (starRingEnd ℂ) ((zeta ^ t.val) ^ b) = c ^ t.val := by
      dsimp [c]
      simp only [mul_pow, map_pow, ← pow_mul, Nat.mul_comm]
    simp_rw [ht]
    have hg : (1 - c) * (1 + c + c ^ 2) = 0 := by
      calc
        (1 - c) * (1 + c + c ^ 2) = 1 - c ^ 3 := by ring
        _ = 0 := by rw [hc3, sub_self]
    have hs : 1 + c + c ^ 2 = 0 :=
      (mul_eq_zero.mp hg).resolve_left (sub_ne_zero.mpr hc.symm)
    simpa [Fin.sum_univ_succ, add_assoc, add_comm, add_left_comm] using hs

/-- Factorization of all eight independent phases. This symbolic identity
replaces any enumeration of the 6561 phase labels. -/
theorem phase_product_sum (a b : Fin 8 → ℕ)
    (ha : ∀ h, a h < 3) (hb : ∀ h, b h < 3) :
    (∑ r : Phase, ∏ h, (zeta ^ (r h).val) ^ a h *
      star ((zeta ^ (r h).val) ^ b h)) =
      if a = b then (6561 : ℂ) else 0 := by
  classical
  change (∑ r : Fin 8 → Fin 3, ∏ h, (zeta ^ (r h).val) ^ a h *
    star ((zeta ^ (r h).val) ^ b h)) = _
  rw [← Fintype.prod_sum (fun (h : Fin 8) (t : Fin 3) =>
    (zeta ^ t.val) ^ a h * star ((zeta ^ t.val) ^ b h))]
  simp_rw [cube_phase_sum _ _ (ha _) (hb _)]
  by_cases hab : a = b
  · subst b
    simp
    norm_num
  · rw [if_neg hab]
    obtain ⟨h, hh⟩ := Function.ne_iff.mp hab
    apply Finset.prod_eq_zero (Finset.mem_univ h)
    simp [hh]

def indicator (i : Fin 9) (h : Fin 8) : ℕ := if i = h.succ then 1 else 0

theorem indicator_lt_three (i : Fin 9) (h : Fin 8) : indicator i h < 3 := by
  unfold indicator
  split_ifs <;> omega

theorem phaseVector_product (r : Phase) (i : Fin 9) :
    phaseVector r i = (1 / 3 : ℂ) *
      ∏ h, (zeta ^ (r h).val) ^ indicator i h := by
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [phaseVector, indicator, eq_comm]
  · simp [phaseVector, indicator, apply_ite, div_eq_mul_inv, mul_comm]

theorem Q_phase_entry (r : Phase) (i j : Fin 9) :
    Q (.inr r) i j = (1 / 9 : ℂ) *
      ∏ h, (zeta ^ (r h).val) ^ indicator i h *
        star ((zeta ^ (r h).val) ^ indicator j h) := by
  simp only [Q, Matrix.vecMulVec_apply, u, Pi.star_apply,
    phaseVector_product, star_mul, star_prod]
  rw [Finset.prod_mul_distrib]
  norm_num
  ring

theorem indicator_injective : Function.Injective indicator := by
  intro i j he
  rcases Fin.eq_zero_or_eq_succ i with hi | ⟨a, hi⟩
  · subst i
    rcases Fin.eq_zero_or_eq_succ j with hj | ⟨b, hj⟩
    · subst j
      rfl
    · subst j
      have hb := congrFun he b
      simp [indicator, eq_comm] at hb
  · subst i
    rcases Fin.eq_zero_or_eq_succ j with hj | ⟨b, hj⟩
    · subst j
      have ha := congrFun he a
      simp [indicator, eq_comm] at ha
    · subst j
      have ha := congrFun he a
      by_cases hab : a = b
      · subst b
        rfl
      · simp [indicator, hab, eq_comm] at ha

theorem Q_phase_sum_entry (i j : Fin 9) :
    (∑ r : Phase, Q (.inr r) i j) = (729 : ℂ) * (1 : Matrix (Fin 9) (Fin 9) ℂ) i j := by
  simp_rw [Q_phase_entry]
  rw [← Finset.mul_sum, phase_product_sum (indicator i) (indicator j)
    (indicator_lt_three i) (indicator_lt_three j)]
  simp only [indicator_injective.eq_iff]
  by_cases hij : i = j <;> norm_num [hij, Matrix.one_apply]

theorem Q_basis_sum : (∑ i : Fin 9, Q (.inl i)) = (1 : Matrix (Fin 9) (Fin 9) ℂ) := by
  ext i j
  simp [Matrix.sum_apply, Q, u, Matrix.vecMulVec_apply, Pi.star_apply, Pi.single_apply,
    Matrix.one_apply, eq_comm]

/-- Actual first moment of the finite pure-projector distribution. -/
theorem Q_mean : (∑ x, p.weight x • Q x) = (1 / 9 : ℝ) •
    (1 : Matrix (Fin 9) (Fin 9) ℂ) := by
  ext i j
  simp only [Matrix.sum_apply, Matrix.smul_apply, Fintype.sum_sum_type, p, weight]
  rw [← Finset.smul_sum, ← Finset.smul_sum]
  have hb := congrArg (fun A : Matrix (Fin 9) (Fin 9) ℂ => A i j) Q_basis_sum
  simp only [Matrix.sum_apply] at hb
  rw [hb, Q_phase_sum_entry]
  by_cases hij : i = j <;> simp [Matrix.one_apply, hij, smul_eq_mul] <;> norm_num

theorem P_mean : (∑ x, p.weight x • P x) = (8 / 9 : ℝ) •
    (1 : Matrix (Fin 9) (Fin 9) ℂ) := by
  simp only [P, smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul,
    p.normalized, Q_mean, one_smul]
  calc
    (1 : Matrix (Fin 9) (Fin 9) ℂ) - (1 / 9 : ℝ) • 1 =
        ((1 : ℝ) - 1 / 9) • (1 : Matrix (Fin 9) (Fin 9) ℂ) := by
      rw [sub_smul, one_smul]
    _ = (8 / 9 : ℝ) • (1 : Matrix (Fin 9) (Fin 9) ℂ) := by norm_num

def meanMatrix : Matrix (Fin 9) (Fin 9) ℂ := ∑ x, p.weight x • (W x).mat

theorem meanMatrix_posSemidef : meanMatrix.PosSemidef :=
  Matrix.posSemidef_sum Finset.univ (fun x _ => (W x).positive.smul (p.nonneg x))

theorem meanMatrix_trace : meanMatrix.trace = 1 := by
  simp only [meanMatrix, Matrix.trace_sum, Matrix.trace_smul, (W _).normalized]
  change (∑ x, (p.weight x : ℂ) * 1) = 1
  simp only [mul_one]
  exact_mod_cast p.normalized

def meanState : Density (Fin 9) where
  mat := meanMatrix
  positive := meanMatrix_posSemidef
  normalized := meanMatrix_trace

/-- The actual average of the actual density matrices is maximally mixed. -/
theorem meanState_matrix : meanState.mat = (1 / 9 : ℝ) •
    (1 : Matrix (Fin 9) (Fin 9) ℂ) := by
  change (∑ x, p.weight x • ((1 / 8 : ℝ) • P x)) = _
  calc
    (∑ x, p.weight x • ((1 / 8 : ℝ) • P x)) =
        (1 / 8 : ℝ) • ∑ x, p.weight x • P x := by
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro x _
      rw [smul_smul, smul_smul, mul_comm]
    _ = (1 / 9 : ℝ) • (1 : Matrix (Fin 9) (Fin 9) ℂ) := by
      rw [P_mean, smul_smul]
      norm_num

theorem meanState_eigenvalues (i : Fin 9) :
    meanState.positive.isHermitian.eigenvalues i = 1 / 9 := by
  let h := meanState.positive.isHermitian
  let v : Fin 9 → ℂ := ⇑(h.eigenvectorBasis i)
  have hv : RCLike.re (star ⇑(h.eigenvectorBasis i) ⬝ᵥ
      ⇑(h.eigenvectorBasis i)) = 1 := by
    rw [dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct]
    norm_num [inner_self_eq_norm_sq_to_K, h.eigenvectorBasis.orthonormal.1 i]
  have haction : meanState.mat *ᵥ v = (1 / 9 : ℝ) • v := by
    rw [meanState_matrix, Matrix.smul_mulVec, Matrix.one_mulVec]
  rw [h.eigenvalues_eq]
  change RCLike.re (star v ⬝ᵥ (meanState.mat *ᵥ v)) = 1 / 9
  rw [haction, dotProduct_smul, RCLike.smul_re]
  change (1 / 9 : ℝ) * RCLike.re (star ⇑(h.eigenvectorBasis i) ⬝ᵥ
    ⇑(h.eigenvectorBasis i)) = 1 / 9
  rw [hv, mul_one]

theorem meanState_entropy : densityEntropyBits meanState = log2 9 := by
  unfold densityEntropyBits
  simp_rw [meanState_eigenvalues]
  norm_num
  have hlog : log2 (1 / 9) = -log2 9 := by
    unfold log2
    rw [show (1 / 9 : ℝ) = (9 : ℝ)⁻¹ by norm_num, Real.log_inv]
    ring
  rw [hlog]
  ring

/-- Holevo information of this actual finite ensemble, in bits. -/
def holevoBits : ℝ := densityEntropyBits meanState -
  ∑ x, p.weight x * densityEntropyBits (W x)

theorem holevoBits_eq : holevoBits = log2 (9 / 8) := by
  unfold holevoBits
  simp_rw [W_entropy]
  rw [← Finset.sum_mul, p.normalized, one_mul, meanState_entropy]
  unfold log2
  rw [Real.log_div (by norm_num : (9 : ℝ) ≠ 0) (by norm_num : (8 : ℝ) ≠ 0)]
  ring

theorem holevoBits_eq_holevoD9 : holevoBits = holevoD9 := holevoBits_eq

def pairIndicator (i k : Fin 9) (h : Fin 8) : ℕ := indicator i h + indicator k h

def pairCount (i k h : Fin 9) : ℕ :=
  (if i = h then 1 else 0) + (if k = h then 1 else 0)

theorem pairCount_sum (i k : Fin 9) : ∑ h, pairCount i k h = 2 := by
  simp [pairCount, Finset.sum_add_distrib]

/-- Equality on the eight independently phased coordinates also forces
equality at coordinate zero, since each side counts exactly two indices. -/
theorem pairIndicator_full_counts {i k j l : Fin 9}
    (he : pairIndicator i k = pairIndicator j l) :
    ∀ h, pairCount i k h = pairCount j l h := by
  have hs : (∑ h : Fin 8, pairCount i k h.succ) =
      ∑ h : Fin 8, pairCount j l h.succ := by
    apply Finset.sum_congr rfl
    intro h _
    exact congrFun he h
  have hi := pairCount_sum i k
  have hj := pairCount_sum j l
  rw [Fin.sum_univ_succ] at hi hj
  have hz : pairCount i k 0 = pairCount j l 0 := by omega
  intro h
  exact Fin.cases hz (fun a => congrFun he a) h

theorem pairCount_eq_iff (i k j l : Fin 9) :
    (∀ h, pairCount i k h = pairCount j l h) ↔
      (i = j ∧ k = l) ∨ (i = l ∧ k = j) := by
  constructor
  · intro he
    by_cases hij : i = j
    · subst j
      left
      refine ⟨rfl, ?_⟩
      by_contra hkl
      have hk := he k
      simp [pairCount, hkl, eq_comm] at hk
    · right
      have hil : i = l := by
        by_contra hil
        have hi := he i
        simp [pairCount, hij, hil, eq_comm] at hi
      refine ⟨hil, ?_⟩
      subst l
      by_contra hkj
      have hk := he k
      simp [pairCount, hkj, eq_comm] at hk
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact fun _ => rfl
    · intro h
      simp [pairCount, Nat.add_comm]

theorem pairIndicator_eq_iff (i k j l : Fin 9) :
    pairIndicator i k = pairIndicator j l ↔
      (i = j ∧ k = l) ∨ (i = l ∧ k = j) := by
  constructor
  · intro he
    exact (pairCount_eq_iff i k j l).mp (pairIndicator_full_counts he)
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rfl
    · funext h
      exact Nat.add_comm _ _

theorem pairIndicator_lt_three (i k : Fin 9) (h : Fin 8) :
    pairIndicator i k h < 3 := by
  unfold pairIndicator indicator
  split_ifs <;> omega

theorem Q_phase_product_entry (r : Phase) (i j k l : Fin 9) :
    Q (.inr r) i j * Q (.inr r) k l = (1 / 81 : ℂ) *
      ∏ h, (zeta ^ (r h).val) ^ pairIndicator i k h *
        star ((zeta ^ (r h).val) ^ pairIndicator j l h) := by
  rw [Q_phase_entry, Q_phase_entry]
  calc
    (1 / 9 : ℂ) * (∏ h, (zeta ^ (r h).val) ^ indicator i h *
        star ((zeta ^ (r h).val) ^ indicator j h)) *
      ((1 / 9 : ℂ) * (∏ h, (zeta ^ (r h).val) ^ indicator k h *
        star ((zeta ^ (r h).val) ^ indicator l h))) =
      (1 / 81 : ℂ) * ∏ h,
        ((zeta ^ (r h).val) ^ indicator i h * star ((zeta ^ (r h).val) ^ indicator j h)) *
        ((zeta ^ (r h).val) ^ indicator k h * star ((zeta ^ (r h).val) ^ indicator l h)) := by
      simp only [Finset.prod_mul_distrib]
      ring
    _ = _ := by
      congr 1
      apply Finset.prod_congr rfl
      intro h _
      simp only [pairIndicator, pow_add, RCLike.star_def, map_mul]
      ring

theorem Q_phase_second_sum (i j k l : Fin 9) :
    (∑ r : Phase, Q (.inr r) i j * Q (.inr r) k l) =
      (81 : ℂ) * if (i = j ∧ k = l) ∨ (i = l ∧ k = j) then 1 else 0 := by
  simp_rw [Q_phase_product_entry]
  rw [← Finset.mul_sum, phase_product_sum (pairIndicator i k) (pairIndicator j l)
    (pairIndicator_lt_three i k) (pairIndicator_lt_three j l)]
  simp only [pairIndicator_eq_iff]
  split_ifs <;> norm_num

theorem Q_basis_second_sum (i j k l : Fin 9) :
    (∑ a : Fin 9, Q (.inl a) i j * Q (.inl a) k l) =
      if i = j ∧ k = l ∧ i = l then (1 : ℂ) else 0 := by
  simp [Q, u, Matrix.vecMulVec_apply, Pi.star_apply, Pi.single_apply,
    ite_mul, mul_ite, ite_and, eq_comm]
  by_cases hij : i = j <;> by_cases hkl : k = l <;> by_cases hil : i = l <;>
    simp_all [eq_comm]

/-- Exact one-copy pure-projector second moment of the constructed ensemble. -/
theorem Q_second_moment (i j k l : Fin 9) :
    (∑ x, (p.weight x : ℂ) * (Q x i j * Q x k l)) =
      (1 / 90 : ℂ) * (1 : Matrix (Fin 9) (Fin 9) ℂ) i j *
        (1 : Matrix (Fin 9) (Fin 9) ℂ) k l +
      (1 / 90 : ℂ) * (1 : Matrix (Fin 9) (Fin 9) ℂ) i l *
        (1 : Matrix (Fin 9) (Fin 9) ℂ) k j := by
  simp only [Fintype.sum_sum_type, p, weight]
  push_cast
  rw [← Finset.mul_sum, ← Finset.mul_sum, Q_basis_second_sum, Q_phase_second_sum]
  by_cases hij : i = j <;> by_cases hkl : k = l <;>
    by_cases hil : i = l <;> by_cases hkj : k = j <;>
    simp_all [Matrix.one_apply] <;> norm_num

theorem Q_mean_entry (i j : Fin 9) :
    (∑ x, (p.weight x : ℂ) * Q x i j) =
      (1 / 9 : ℂ) * (1 : Matrix (Fin 9) (Fin 9) ℂ) i j := by
  have h := congrArg (fun A : Matrix (Fin 9) (Fin 9) ℂ => A i j) Q_mean
  simp only [Matrix.sum_apply, Matrix.smul_apply, RCLike.real_smul_eq_coe_mul] at h
  norm_num at h
  simpa only [Fintype.sum_sum_type] using h

theorem weight_complex_sum : (∑ x, (p.weight x : ℂ)) = 1 := by
  exact_mod_cast p.normalized

/-- Exact one-copy support-projector moment; every term uses the actual
finite full-support ensemble rather than an assumed design field. -/
theorem P_second_moment (i j k l : Fin 9) :
    (∑ x, (p.weight x : ℂ) * (P x i j * P x k l)) =
      (71 / 90 : ℂ) * (1 : Matrix (Fin 9) (Fin 9) ℂ) i j *
        (1 : Matrix (Fin 9) (Fin 9) ℂ) k l +
      (1 / 90 : ℂ) * (1 : Matrix (Fin 9) (Fin 9) ℂ) i l *
        (1 : Matrix (Fin 9) (Fin 9) ℂ) k j := by
  have hterm (x : Label) : (p.weight x : ℂ) * (P x i j * P x k l) =
      (p.weight x : ℂ) * ((1 : Matrix (Fin 9) (Fin 9) ℂ) i j *
        (1 : Matrix (Fin 9) (Fin 9) ℂ) k l) -
      (1 : Matrix (Fin 9) (Fin 9) ℂ) i j * ((p.weight x : ℂ) * Q x k l) -
      (1 : Matrix (Fin 9) (Fin 9) ℂ) k l * ((p.weight x : ℂ) * Q x i j) +
      (p.weight x : ℂ) * (Q x i j * Q x k l) := by
    simp only [P, Matrix.sub_apply]
    ring
  simp_rw [hterm]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    ← Finset.sum_mul, ← Finset.mul_sum, ← Finset.mul_sum,
    weight_complex_sum, Q_mean_entry, Q_mean_entry, Q_second_moment]
  ring

theorem W_matrix (x : Label) : (W x).mat = (1 / 8 : ℝ) • P x := rfl

theorem W_support (x : Label) : P x * (W x).mat = (W x).mat := by
  rw [W_matrix, Matrix.mul_smul, P_idempotent]

theorem one_sub_P_posSemidef (x : Label) : (1 - P x).PosSemidef := by
  simpa only [P, sub_sub_cancel] using Q_posSemidef x

theorem W_eighth_eigenvalue_count (x : Label) :
    (Finset.univ.filter (fun i => (W x).positive.isHermitian.eigenvalues i = 1 / 8)).card = 8 := by
  classical
  let ev : Fin 9 → ℝ := (W x).positive.isHermitian.eigenvalues
  have hs : (∑ i, ev i) = ∑ i, if ev i = 1 / 8 then (1 / 8 : ℝ) else 0 := by
    apply Finset.sum_congr rfl
    intro i _
    rcases W_eigenvalues x i with hz | he
    · change (W x).positive.isHermitian.eigenvalues i = _
      change (W x).positive.isHermitian.eigenvalues i =
        if (W x).positive.isHermitian.eigenvalues i = 1 / 8 then (1 / 8 : ℝ) else 0
      norm_num [hz]
    · change (W x).positive.isHermitian.eigenvalues i = _
      change (W x).positive.isHermitian.eigenvalues i =
        if (W x).positive.isHermitian.eigenvalues i = 1 / 8 then (1 / 8 : ℝ) else 0
      rw [he]
      simp
  have ht := W_sum_eigenvalues x
  change (∑ i, ev i) = 1 at ht
  rw [hs] at ht
  simp only [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero,
    nsmul_eq_mul, mul_zero, add_zero] at ht
  have hc : ((Finset.univ.filter (fun i => ev i = 1 / 8)).card : ℝ) = 8 := by
    nlinarith [ht]
  exact_mod_cast hc

theorem W_zero_eigenvalue_count (x : Label) :
    (Finset.univ.filter (fun i => (W x).positive.isHermitian.eigenvalues i = 0)).card = 1 := by
  classical
  have heq : Finset.univ.filter (fun i => (W x).positive.isHermitian.eigenvalues i = 0) =
      (Finset.univ.filter (fun i => (W x).positive.isHermitian.eigenvalues i = 1 / 8))ᶜ := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_compl]
    rcases W_eigenvalues x i with hz | he
    · norm_num [hz]
    · norm_num [he]
  rw [heq, Finset.card_compl, W_eighth_eigenvalue_count]
  norm_num

end D9
end VisibleCompression

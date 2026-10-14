import QuantumProver.InformationTheory.WernerEndpoint.ChannelCoherence

noncomputable section

namespace QuantumProver.WernerEndpoint.EnsemblePhase

open scoped BigOperators
open Matrix

variable {K : Type*} [Fintype K] [DecidableEq K]

abbrev Phase (K : Type*) := K → Fin 3

def zeta : ℂ := Complex.exp (2 * Real.pi * Complex.I / 3)

theorem zeta_primitive : IsPrimitiveRoot zeta 3 :=
  Complex.isPrimitiveRoot_exp 3 (by norm_num)

theorem zeta_norm : ‖zeta‖ = 1 := zeta_primitive.norm'_eq_one (by norm_num)

theorem zeta_pow_three : zeta ^ 3 = 1 := zeta_primitive.pow_eq_one

def phase (r : Phase K) (i : K) : ℂ := zeta ^ (r i).val

theorem phase_norm (r : Phase K) (i : K) : ‖phase r i‖ = 1 := by
  simp [phase, norm_pow, zeta_norm]

theorem zeta_power_unit (k : ℕ) : zeta ^ k * star (zeta ^ k) = 1 := by
  simpa [← Complex.sq_norm, norm_pow, zeta_norm] using Complex.mul_conj (zeta ^ k)

theorem zeta_power_cube (k : ℕ) : (zeta ^ k) ^ 3 = 1 := by
  rw [← pow_mul, Nat.mul_comm, pow_mul, zeta_pow_three, one_pow]

theorem cube_phase_sum (a b : ℕ) (ha : a < 3) (hb : b < 3) :
    (∑ t : Fin 3, (zeta ^ t.val) ^ a * star ((zeta ^ t.val) ^ b)) =
      if a = b then (3 : ℂ) else 0 := by
  simp only [Complex.star_def]
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
        simpa only [Complex.star_def, mul_comm] using zeta_power_unit b
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

theorem phase_product_sum (a b : K → ℕ)
    (ha : ∀ i, a i < 3) (hb : ∀ i, b i < 3) :
    (∑ r : Phase K, ∏ i, phase r i ^ a i * star (phase r i ^ b i)) =
      if a = b then (3 : ℂ) ^ Fintype.card K else 0 := by
  change (∑ r : K → Fin 3, ∏ i, (zeta ^ (r i).val) ^ a i *
    star ((zeta ^ (r i).val) ^ b i)) = _
  rw [← Fintype.prod_sum (fun (i : K) (t : Fin 3) =>
    (zeta ^ t.val) ^ a i * star ((zeta ^ t.val) ^ b i))]
  simp_rw [cube_phase_sum _ _ (ha _) (hb _)]
  by_cases hab : a = b
  · subst b
    simp
  · rw [if_neg hab]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hab
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [hi]

def indicator (i h : K) : ℕ := if i = h then 1 else 0

def pairCount (i k h : K) : ℕ := indicator i h + indicator k h

theorem pairCount_lt_three (i k h : K) : pairCount i k h < 3 := by
  unfold pairCount indicator
  split_ifs <;> omega

theorem pairCount_eq_iff (i k j l : K) :
    pairCount i k = pairCount j l ↔
      (i = j ∧ k = l) ∨ (i = l ∧ k = j) := by
  constructor
  · intro he
    by_cases hij : i = j
    · subst j
      left
      refine ⟨rfl, ?_⟩
      by_contra hkl
      have hk := congrFun he k
      simp [pairCount, indicator, hkl, eq_comm] at hk
    · right
      have hil : i = l := by
        by_contra hil
        have hi := congrFun he i
        simp [pairCount, indicator, hij, hil, eq_comm] at hi
      refine ⟨hil, ?_⟩
      subst l
      by_contra hkj
      have hk := congrFun he k
      simp [pairCount, indicator, hkj, eq_comm] at hk
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rfl
    · funext h
      exact Nat.add_comm _ _

theorem phase_pair_product (r : Phase K) (i j k l : K) :
    phase r i * star (phase r j) * phase r k * star (phase r l) =
      ∏ h, phase r h ^ pairCount i k h * star (phase r h ^ pairCount j l h) := by
  simp only [pairCount, pow_add, star_mul, Finset.prod_mul_distrib]
  have hp (i : K) : (∏ h, phase r h ^ indicator i h) = phase r i := by
    simp [indicator, apply_ite]
  simp only [← star_prod, hp]
  ring

theorem phase_fourth_sum (i j k l : K) :
    (∑ r : Phase K, phase r i * star (phase r j) * phase r k * star (phase r l)) =
      (3 : ℂ) ^ Fintype.card K *
        if (i = j ∧ k = l) ∨ (i = l ∧ k = j) then 1 else 0 := by
  simp_rw [phase_pair_product]
  rw [phase_product_sum _ _ (pairCount_lt_three i k) (pairCount_lt_three j l)]
  simp only [pairCount_eq_iff]
  split_ifs <;> simp

theorem pairing_indicator (i j k l : K) :
    (if (i = j ∧ k = l) ∨ (i = l ∧ k = j) then (1 : ℂ) else 0) =
      (if i = j ∧ k = l then 1 else 0) +
      (if i = l ∧ k = j then 1 else 0) -
      (if i = j ∧ j = k ∧ k = l then 1 else 0) := by
  by_cases hij : i = j <;> by_cases hjk : j = k <;>
    by_cases hkl : k = l <;> by_cases hil : i = l <;>
    simp_all

theorem phase_contraction_sum (T : K → K → K → K → ℂ) :
    (∑ r : Phase K, ∑ i, ∑ j, ∑ k, ∑ l,
      (phase r i * star (phase r j) * phase r k * star (phase r l)) * T i j k l) =
      (3 : ℂ) ^ Fintype.card K *
        ((∑ i, ∑ k, T i i k k) + (∑ i, ∑ j, T i j j i) - ∑ i, T i i i i) := by
  have hreorder : (∑ r : Phase K, ∑ i, ∑ j, ∑ k, ∑ l,
      (phase r i * star (phase r j) * phase r k * star (phase r l)) * T i j k l) =
      ∑ i, ∑ j, ∑ k, ∑ l, ∑ r : Phase K,
      (phase r i * star (phase r j) * phase r k * star (phase r l)) * T i j k l := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    exact Finset.sum_comm
  rw [hreorder]
  simp_rw [← Finset.sum_mul, phase_fourth_sum, pairing_indicator]
  simp only [mul_assoc, add_mul, sub_mul]
  simp_rw [← Finset.mul_sum]
  congr 1
  simp [Finset.sum_add_distrib, Finset.sum_sub_distrib, ite_mul, ite_and, eq_comm]

variable {B E : Type*} [Fintype B] [Fintype E]

def phasedAmplitudes (U : K → Matrix B E ℂ) (r : Phase K) : Matrix B E ℂ :=
  ∑ i, phase r i • U i

theorem crossLeft_sum_left (U : K → Matrix B E ℂ) (W : Matrix B E ℂ) :
    crossLeft (∑ i, U i) W = ∑ i, crossLeft (U i) W := by
  ext b c
  simp only [crossLeft, Matrix.sum_apply, Finset.sum_mul]
  exact Finset.sum_comm

theorem crossLeft_sum_right (U : Matrix B E ℂ) (W : K → Matrix B E ℂ) :
    crossLeft U (∑ i, W i) = ∑ i, crossLeft U (W i) := by
  ext b c
  simp only [crossLeft, Matrix.sum_apply, star_sum, Finset.mul_sum]
  exact Finset.sum_comm

theorem reducedLeft_phasedAmplitudes (U : K → Matrix B E ℂ) (r : Phase K) :
    reducedLeft (phasedAmplitudes U r) =
      ∑ i, ∑ j, (phase r i * star (phase r j)) • crossLeft (U i) (U j) := by
  unfold reducedLeft phasedAmplitudes
  rw [crossLeft_sum_left]
  simp_rw [crossLeft_sum_right, crossLeft_smul_left, crossLeft_smul_right, smul_smul]

theorem phased_trace_square (U : K → Matrix B E ℂ) (r : Phase K) :
    Matrix.trace (reducedLeft (phasedAmplitudes U r) *
      reducedLeft (phasedAmplitudes U r)) =
      ∑ i, ∑ j, ∑ k, ∑ l,
        (phase r i * star (phase r j) * phase r k * star (phase r l)) *
          Matrix.trace (crossLeft (U i) (U j) * crossLeft (U k) (U l)) := by
  rw [reducedLeft_phasedAmplitudes]
  simp only [Finset.sum_mul, Finset.mul_sum, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, Matrix.trace_sum, Matrix.trace_smul, smul_eq_mul, mul_assoc]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  rw [Matrix.trace_mul_comm]

theorem cross_reverse_product_trace (U W : Matrix B E ℂ) :
    Matrix.trace (crossLeft U W * crossLeft W U) =
      Matrix.trace (reducedRight U * reducedRight W) := by
  rw [crossLeft_eq_mul, crossLeft_eq_mul]
  unfold reducedRight
  rw [crossRight_eq_mul_transpose, crossRight_eq_mul_transpose,
    ← Matrix.transpose_mul, Matrix.trace_transpose]
  simpa only [Matrix.mul_assoc] using
    Matrix.trace_mul_comm U ((Wᴴ * W) * Uᴴ)

theorem trace_sum_square {J : Type*} [Fintype J] (R : K → Matrix J J ℂ) :
    Matrix.trace ((∑ i, R i) * (∑ i, R i)) =
      ∑ i, ∑ j, Matrix.trace (R i * R j) := by
  simp only [Finset.sum_mul, Finset.mul_sum, Matrix.trace_sum]
  exact Finset.sum_comm

theorem phase_reduced_trace_sum (U : K → Matrix B E ℂ) :
    (∑ r : Phase K, Matrix.trace (reducedLeft (phasedAmplitudes U r) *
      reducedLeft (phasedAmplitudes U r))) =
      (3 : ℂ) ^ Fintype.card K *
        (Matrix.trace ((∑ i, reducedLeft (U i)) * (∑ i, reducedLeft (U i))) +
         Matrix.trace ((∑ i, reducedRight (U i)) * (∑ i, reducedRight (U i))) -
         ∑ i, Matrix.trace (reducedLeft (U i) * reducedLeft (U i))) := by
  simp_rw [phased_trace_square]
  rw [phase_contraction_sum]
  have hi : (∑ i, ∑ k, Matrix.trace (crossLeft (U i) (U i) * crossLeft (U k) (U k))) =
      Matrix.trace ((∑ i, reducedLeft (U i)) * (∑ i, reducedLeft (U i))) :=
    (trace_sum_square (fun i => reducedLeft (U i))).symm
  have hc : (∑ i, ∑ j, Matrix.trace (crossLeft (U i) (U j) * crossLeft (U j) (U i))) =
      Matrix.trace ((∑ i, reducedRight (U i)) * (∑ i, reducedRight (U i))) := by
    simp_rw [cross_reverse_product_trace]
    exact (trace_sum_square (fun i => reducedRight (U i))).symm
  rw [hi, hc]
  rfl

theorem phase_reduced_purity_sum (U : K → Matrix B E ℂ) :
    (∑ r : Phase K, purity (reducedLeft (phasedAmplitudes U r))) =
      (3 : ℝ) ^ Fintype.card K *
        (purity (∑ i, reducedLeft (U i)) + purity (∑ i, reducedRight (U i)) -
          ∑ i, purity (reducedLeft (U i))) := by
  have h := congrArg Complex.re (phase_reduced_trace_sum U)
  have hco : Complex.ofReal ((3 : ℝ) ^ Fintype.card K) = (3 : ℂ) ^ Fintype.card K := by
    norm_cast
  have hr := congrArg Complex.re hco
  have hi := congrArg Complex.im hco
  simp only [Complex.ofReal_re] at hr
  simp only [Complex.ofReal_im] at hi
  simpa only [purity, Complex.re_sum, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.add_re, Complex.sub_re, ← hr, ← hi, zero_mul, sub_zero] using h

variable {I : Type*} [Fintype I]

theorem pureDensity_sum_smul (ψ : K → I → ℂ) (c : K → ℂ) :
    pureDensity (∑ i, c i • ψ i) =
      ∑ i, ∑ j, (c i * star (c j)) • crossDensity (ψ i) (ψ j) := by
  ext x y
  simp [pureDensity, crossDensity, Matrix.sum_apply, Matrix.smul_apply,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul, star_sum, star_mul,
    Finset.sum_mul, Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc]
  exact Finset.sum_comm

theorem vectorNormSq_sum_orthogonal (ψ : K → I → ℂ) (c : K → ℂ)
    (hgram : ∀ i j, (∑ x, ψ i x * star (ψ j x)) = if i = j then 1 else 0) :
    vectorNormSq (∑ i, c i • ψ i) = ∑ i, Complex.normSq (c i) := by
  have htrace : Matrix.trace (pureDensity (∑ i, c i • ψ i)) =
      ((∑ i, Complex.normSq (c i) : ℝ) : ℂ) := by
    rw [pureDensity_sum_smul]
    simp only [Matrix.trace_sum, Matrix.trace_smul, smul_eq_mul]
    have ht (i j : K) : Matrix.trace (crossDensity (ψ i) (ψ j)) =
        if i = j then 1 else 0 := hgram i j
    simp_rw [ht]
    simp [Complex.mul_conj, Complex.star_def]
  rw [pureDensity_trace] at htrace
  exact_mod_cast htrace

def phasedInput (t : K → ℝ) (ψ : K → I → ℂ) (r : Phase K) : I → ℂ :=
  ∑ i, ((t i : ℂ) * phase r i) • ψ i

theorem phasedInput_normSq (t : K → ℝ) (ψ : K → I → ℂ) (r : Phase K)
    (hgram : ∀ i j, (∑ x, ψ i x * star (ψ j x)) = if i = j then 1 else 0) :
    vectorNormSq (phasedInput t ψ r) = ∑ i, t i ^ 2 := by
  rw [phasedInput, vectorNormSq_sum_orthogonal ψ _ hgram]
  apply Finset.sum_congr rfl
  intro i _
  have hn : Complex.normSq (phase r i) = 1 := by
    rw [← Complex.sq_norm, phase_norm]
    norm_num
  simp [Complex.normSq_mul, hn, Complex.normSq_ofReal, pow_two]

theorem partialTraceLeft_sum (R : K → Matrix (B × E) (B × E) ℂ) :
    partialTraceLeft (∑ i, R i) = ∑ i, partialTraceLeft (R i) := by
  ext b c
  simp only [partialTraceLeft, Matrix.sum_apply]
  exact Finset.sum_comm

theorem partialTraceRight_sum (R : K → Matrix (B × E) (B × E) ℂ) :
    partialTraceRight (∑ i, R i) = ∑ i, partialTraceRight (R i) := by
  ext e f
  simp only [partialTraceRight, Matrix.sum_apply]
  exact Finset.sum_comm

theorem partialTraceLeft_smul (R : Matrix (B × E) (B × E) ℂ) (z : ℂ) :
    partialTraceLeft (z • R) = z • partialTraceLeft R := by
  ext b c
  simp [partialTraceLeft, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]

theorem partialTraceRight_smul (R : Matrix (B × E) (B × E) ℂ) (z : ℂ) :
    partialTraceRight (z • R) = z • partialTraceRight R := by
  ext e f
  simp [partialTraceRight, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]

variable [DecidableEq I]

theorem apply_sum (N : Stinespring I B E) (R : K → Matrix I I ℂ) :
    N.apply (∑ i, R i) = ∑ i, N.apply (R i) := by
  unfold Stinespring.apply
  rw [Matrix.mul_sum, Matrix.sum_mul, partialTraceLeft_sum]

theorem complement_sum (N : Stinespring I B E) (R : K → Matrix I I ℂ) :
    N.complement (∑ i, R i) = ∑ i, N.complement (R i) := by
  unfold Stinespring.complement
  rw [Matrix.mul_sum, Matrix.sum_mul, partialTraceRight_sum]

theorem apply_smul (N : Stinespring I B E) (R : Matrix I I ℂ) (z : ℂ) :
    N.apply (z • R) = z • N.apply R := by
  unfold Stinespring.apply
  rw [Matrix.mul_smul, Matrix.smul_mul, partialTraceLeft_smul]

theorem complement_smul (N : Stinespring I B E) (R : Matrix I I ℂ) (z : ℂ) :
    N.complement (z • R) = z • N.complement R := by
  unfold Stinespring.complement
  rw [Matrix.mul_smul, Matrix.smul_mul, partialTraceRight_smul]

theorem amplitudes_sum (N : Stinespring I B E) (u : K → I → ℂ) :
    N.amplitudes (∑ i, u i) = ∑ i, N.amplitudes (u i) := by
  ext b e
  simp only [Stinespring.amplitudes, Finset.sum_apply, Finset.mul_sum, Matrix.sum_apply]
  exact Finset.sum_comm

theorem amplitudes_phasedInput (N : Stinespring I B E) (t : K → ℝ)
    (ψ : K → I → ℂ) (r : Phase K) :
    N.amplitudes (phasedInput t ψ r) =
      phasedAmplitudes (fun i => (t i : ℂ) • N.amplitudes (ψ i)) r := by
  rw [phasedInput, amplitudes_sum]
  simp_rw [N.amplitudes_smul]
  simp only [phasedAmplitudes, smul_smul, mul_comm]

theorem reducedRight_smul (U : Matrix B E ℂ) (z : ℂ) :
    reducedRight (z • U) = (Complex.normSq z : ℂ) • reducedRight U := by
  ext e f
  simp only [reducedRight, crossRight, Matrix.smul_apply, smul_eq_mul, star_mul]
  have h : z * star z = (Complex.normSq z : ℂ) := by
    simpa only [Complex.star_def] using Complex.mul_conj z
  simp only [← h, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  ring

def weightedDensity (t : K → ℝ) (ψ : K → I → ℂ) : Matrix I I ℂ :=
  ∑ i, ((t i ^ 2 : ℝ) : ℂ) • pureDensity (ψ i)

theorem apply_weightedDensity (N : Stinespring I B E) (t : K → ℝ)
    (ψ : K → I → ℂ) :
    N.apply (weightedDensity t ψ) =
      ∑ i, reducedLeft ((t i : ℂ) • N.amplitudes (ψ i)) := by
  rw [weightedDensity, apply_sum]
  simp_rw [apply_smul, N.apply_pureDensity, reducedLeft_smul]
  simp [Complex.normSq_ofReal, pow_two]

theorem complement_weightedDensity (N : Stinespring I B E) (t : K → ℝ)
    (ψ : K → I → ℂ) :
    N.complement (weightedDensity t ψ) =
      ∑ i, reducedRight ((t i : ℂ) • N.amplitudes (ψ i)) := by
  rw [weightedDensity, complement_sum]
  simp_rw [complement_smul, N.complement_pureDensity, reducedRight_smul]
  simp [Complex.normSq_ofReal, pow_two]

theorem orthogonal_ensemble_purity (N : Stinespring I B E) (β : ℝ)
    (hbound : ∀ w : I → ℂ, vectorNormSq w = 1 → purity (N.apply (pureDensity w)) ≤ β)
    (t : K → ℝ) (ψ : K → I → ℂ)
    (hgram : ∀ i j, (∑ x, ψ i x * star (ψ j x)) = if i = j then 1 else 0)
    (ht : ∑ i, t i ^ 2 = 1) :
    purity (N.apply (weightedDensity t ψ)) + purity (N.complement (weightedDensity t ψ)) ≤
      β * (1 + ∑ i, t i ^ 4) := by
  let U : K → Matrix B E ℂ := fun i => (t i : ℂ) • N.amplitudes (ψ i)
  have hphase (r : Phase K) : purity (reducedLeft (phasedAmplitudes U r)) ≤ β := by
    have h := hbound (phasedInput t ψ r) (by rw [phasedInput_normSq t ψ r hgram, ht])
    rw [N.apply_pureDensity, amplitudes_phasedInput] at h
    exact h
  have havg := Finset.sum_le_sum (fun r (_ : r ∈ (Finset.univ : Finset (Phase K))) => hphase r)
  rw [phase_reduced_purity_sum] at havg
  have hcard : (Fintype.card (Phase K) : ℝ) = (3 : ℝ) ^ Fintype.card K := by
    simp [Phase, Fintype.card_fun]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard] at havg
  have hcpos : 0 < (3 : ℝ) ^ Fintype.card K := by positivity
  have hm := le_of_mul_le_mul_left havg hcpos
  have hdiag : (∑ i, purity (reducedLeft (U i))) ≤ β * (∑ i, t i ^ 4) := by
    have hi (i : K) : vectorNormSq (ψ i) = 1 := by
      have h := congrArg Complex.re (hgram i i)
      simpa [vectorNormSq, Complex.re_sum, Complex.mul_conj] using h
    calc
      (∑ i, purity (reducedLeft (U i))) =
          ∑ i, t i ^ 4 * purity (N.apply (pureDensity (ψ i))) := by
        apply Finset.sum_congr rfl
        intro i _
        have hsc := QuantumProver.WernerEndpoint.reducedLeft_smul (N.amplitudes (ψ i)) (t i : ℂ)
        change purity (reducedLeft ((t i : ℂ) • N.amplitudes (ψ i))) = _
        rw [hsc]
        simp only [Complex.normSq_ofReal]
        rw [← pow_two, purity_real_smul, N.apply_pureDensity]
        ring
      _ ≤ ∑ i, t i ^ 4 * β := by
        apply Finset.sum_le_sum
        intro i _
        exact mul_le_mul_of_nonneg_left (hbound (ψ i) (hi i)) (by positivity)
      _ = _ := by rw [← Finset.sum_mul, mul_comm]
  rw [apply_weightedDensity, complement_weightedDensity]
  change purity (∑ i, reducedLeft (U i)) + purity (∑ i, reducedRight (U i)) ≤ _
  linarith

theorem crossDensity_mul (u v w z : I → ℂ) :
    crossDensity u v * crossDensity w z =
      (∑ x, w x * star (v x)) • crossDensity u z := by
  ext x y
  simp [crossDensity, Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul,
    Finset.sum_mul, Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc]

theorem pureDensity_orthogonal_mul (ψ : K → I → ℂ)
    (hgram : ∀ i j, (∑ x, ψ i x * star (ψ j x)) = if i = j then 1 else 0) (i j : K) :
    pureDensity (ψ i) * pureDensity (ψ j) = if i = j then pureDensity (ψ i) else 0 := by
  unfold pureDensity
  rw [crossDensity_mul, hgram]
  by_cases hij : i = j
  · subst j
    simp
  · simp [hij, Ne.symm hij]

theorem weightedDensity_purity (t : K → ℝ) (ψ : K → I → ℂ)
    (hgram : ∀ i j, (∑ x, ψ i x * star (ψ j x)) = if i = j then 1 else 0) :
    purity (weightedDensity t ψ) = ∑ i, t i ^ 4 := by
  have hp (i : K) : Matrix.trace (pureDensity (ψ i)) = 1 := by
    simpa [pureDensity, crossDensity, Matrix.trace, Matrix.diag]
      using hgram i i
  have htrace : Matrix.trace (weightedDensity t ψ * weightedDensity t ψ) =
      ((∑ i, t i ^ 4 : ℝ) : ℂ) := by
    simp only [weightedDensity, Finset.sum_mul, Finset.mul_sum, Matrix.smul_mul,
      Matrix.mul_smul, smul_smul, pureDensity_orthogonal_mul ψ hgram,
      smul_ite, smul_zero, Matrix.trace_sum, Matrix.trace_smul, smul_eq_mul]
    simp [hp, eq_comm, apply_ite, Matrix.trace_smul]
    push_cast
    apply Finset.sum_congr rfl
    intro i _
    ring
  unfold purity
  rw [htrace]
  rfl

theorem orthogonal_ensemble_purity_marginal (N : Stinespring I B E) (β : ℝ)
    (hbound : ∀ w : I → ℂ, vectorNormSq w = 1 → purity (N.apply (pureDensity w)) ≤ β)
    (t : K → ℝ) (ψ : K → I → ℂ)
    (hgram : ∀ i j, (∑ x, ψ i x * star (ψ j x)) = if i = j then 1 else 0)
    (ht : ∑ i, t i ^ 2 = 1) :
    purity (N.apply (weightedDensity t ψ)) + purity (N.complement (weightedDensity t ψ)) ≤
      β * (1 + purity (weightedDensity t ψ)) := by
  rw [weightedDensity_purity t ψ hgram]
  exact orthogonal_ensemble_purity N β hbound t ψ hgram ht

end QuantumProver.WernerEndpoint.EnsemblePhase

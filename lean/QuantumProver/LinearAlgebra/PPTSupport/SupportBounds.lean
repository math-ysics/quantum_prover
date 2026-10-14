import Mathlib

set_option autoImplicit false

noncomputable section

open Matrix
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace QuantumProver.PPTSupport.SupportBounds

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem trace_mul_re_nonneg {A B : Matrix n n ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) : 0 ≤ (A * B).trace.re := by
  have hS : (CFC.sqrt A)ᴴ = CFC.sqrt A := (CFC.sqrt_nonneg A).posSemidef.1
  have hpos : (CFC.sqrt A * B * CFC.sqrt A).PosSemidef := by
    simpa only [hS] using hB.mul_mul_conjTranspose_same (CFC.sqrt A)
  have htrace : (CFC.sqrt A * B * CFC.sqrt A).trace = (A * B).trace := by
    rw [Matrix.trace_mul_cycle, ← pow_two, CFC.sq_sqrt A hA.nonneg]
  exact (Complex.nonneg_iff.mp (htrace ▸ hpos.trace_nonneg)).1

theorem trace_eq_zero_of_posSemidef_re_eq_zero {A : Matrix n n ℂ}
    (hA : A.PosSemidef) (htrace : A.trace.re = 0) : A.trace = 0 := by
  apply Complex.ext
  · exact htrace
  · simpa using (Complex.nonneg_iff.mp hA.trace_nonneg).2.symm

theorem posSemidef_eq_zero_of_trace_eq_zero {A : Matrix n n ℂ}
    (hA : A.PosSemidef) (htrace : A.trace = 0) : A = 0 := by
  have hS : (CFC.sqrt A)ᴴ = CFC.sqrt A := (CFC.sqrt_nonneg A).posSemidef.1
  have hsq : (CFC.sqrt A)ᴴ * CFC.sqrt A = A := by
    rw [hS, ← pow_two, CFC.sq_sqrt A hA.nonneg]
  have hz : CFC.sqrt A = 0 :=
    Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp (by rwa [hsq])
  rw [← hsq, hz]
  simp

theorem posSemidef_eq_zero_of_trace_re_eq_zero {A : Matrix n n ℂ}
    (hA : A.PosSemidef) (htrace : A.trace.re = 0) : A = 0 :=
  posSemidef_eq_zero_of_trace_eq_zero hA
    (trace_eq_zero_of_posSemidef_re_eq_zero hA htrace)

theorem mul_eq_zero_of_posSemidef_trace_re_eq_zero {A B : Matrix n n ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef)
    (htrace : (A * B).trace.re = 0) : A * B = 0 := by
  let S := CFC.sqrt A
  let T := CFC.sqrt B
  have hS : Sᴴ = S := (CFC.sqrt_nonneg A).posSemidef.1
  have hT : Tᴴ = T := (CFC.sqrt_nonneg B).posSemidef.1
  have hSS : S * S = A := by
    change CFC.sqrt A * CFC.sqrt A = A
    rw [← pow_two, CFC.sq_sqrt A hA.nonneg]
  have hTT : T * T = B := by
    change CFC.sqrt B * CFC.sqrt B = B
    rw [← pow_two, CFC.sq_sqrt B hB.nonneg]
  have hgram : (T * S)ᴴ * (T * S) = S * B * S := by
    rw [Matrix.conjTranspose_mul, hS, hT, Matrix.mul_assoc,
      ← Matrix.mul_assoc T T S, hTT, ← Matrix.mul_assoc]
  have htr : ((T * S)ᴴ * (T * S)).trace.re = 0 := by
    rw [hgram, Matrix.trace_mul_cycle, hSS]
    exact htrace
  have hzero : T * S = 0 :=
    Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp
      (trace_eq_zero_of_posSemidef_re_eq_zero
        (Matrix.posSemidef_conjTranspose_mul_self (T * S)) htr)
  have hBA : B * A = 0 := by
    calc
      B * A = (T * T) * (S * S) := by rw [hTT, hSS]
      _ = T * (T * S) * S := by simp only [Matrix.mul_assoc]
      _ = 0 := by rw [hzero]; simp
  have h := congrArg Matrix.conjTranspose hBA
  simpa only [Matrix.conjTranspose_mul, hA.1.eq, hB.1.eq, Matrix.conjTranspose_zero] using h

theorem projection_posSemidef {P : Matrix n n ℂ}
    (hP : P.IsHermitian) (hPP : P * P = P) : P.PosSemidef := by
  simpa only [hP.eq, hPP] using Matrix.posSemidef_self_mul_conjTranspose P

theorem feasible_mul_projection {P E : Matrix n n ℂ}
    (hP : P.IsHermitian) (hPP : P * P = P)
    (hEP : (E - P).PosSemidef) (hEcomp : (1 - E).PosSemidef) :
    E * P = P ∧ P * E = P := by
  have hPpos := projection_posSemidef hP hPP
  have ha := trace_mul_re_nonneg hPpos hEP
  have hb := trace_mul_re_nonneg hPpos hEcomp
  have hsum : (P * (E - P)).trace.re + (P * (1 - E)).trace.re = 0 := by
    have hm : P * (E - P) + P * (1 - E) = 0 := by
      rw [Matrix.mul_sub, Matrix.mul_sub, Matrix.mul_one, hPP]
      abel
    rw [← Complex.add_re, ← Matrix.trace_add, hm, Matrix.trace_zero, Complex.zero_re]
  have hz : (P * (1 - E)).trace.re = 0 := by linarith
  have hzero := mul_eq_zero_of_posSemidef_trace_re_eq_zero hPpos hEcomp hz
  have hPE : P * E = P := by
    rw [Matrix.mul_sub, Matrix.mul_one] at hzero
    exact (sub_eq_zero.mp hzero).symm
  have hE : E.IsHermitian := by
    simpa only [sub_add_cancel] using hEP.1.add hP
  have hEP' : E * P = P := by
    have h := congrArg Matrix.conjTranspose hPE
    simpa only [Matrix.conjTranspose_mul, hP.eq, hE.eq] using h
  exact ⟨hEP', hPE⟩

theorem feasible_support_decomposition {P E : Matrix n n ℂ}
    (hP : P.IsHermitian) (hPP : P * P = P)
    (hEP : (E - P).PosSemidef) (hEcomp : (1 - E).PosSemidef) :
    E = P + (1 - P) * E * (1 - P) := by
  obtain ⟨hEP', hPE⟩ := feasible_mul_projection hP hPP hEP hEcomp
  symm
  calc
    P + (1 - P) * E * (1 - P) =
        P + E - P * E - E * P + P * E * P := by noncomm_ring
    _ = E := by rw [hPE, hEP', hPP]; abel

theorem feasible_complement_supported {P E : Matrix n n ℂ}
    (hP : P.IsHermitian) (hPP : P * P = P)
    (hEP : (E - P).PosSemidef) (hEcomp : (1 - E).PosSemidef) :
    (1 - P) * (E - P) * (1 - P) = E - P := by
  obtain ⟨hEP', hPE⟩ := feasible_mul_projection hP hPP hEP hEcomp
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul,
    hPP, hEP', hPE]
  abel

theorem complement_compression_trace_pairing {Q X Z : Matrix n n ℂ}
    (hX : Q * X * Q = X) :
    ((Q * Z * Q) * X).trace = (Z * X).trace := by
  calc
    ((Q * Z * Q) * X).trace = (Q * (Z * Q) * X).trace := by simp only [Matrix.mul_assoc]
    _ = (X * Q * (Z * Q)).trace := Matrix.trace_mul_cycle Q (Z * Q) X
    _ = ((Z * Q) * (X * Q)).trace := Matrix.trace_mul_comm (X * Q) (Z * Q)
    _ = (Z * (Q * X * Q)).trace := by simp only [Matrix.mul_assoc]
    _ = (Z * X).trace := by rw [hX]

theorem feasible_dual_pairing_lower {P E Z : Matrix n n ℂ}
    (hP : P.IsHermitian) (hPP : P * P = P)
    (hEP : (E - P).PosSemidef) (hEcomp : (1 - E).PosSemidef)
    (hZ : ((1 - P) * Z * (1 - P)).PosSemidef) :
    (P * Z).trace.re ≤ (E * Z).trace.re := by
  have hcomp := feasible_complement_supported hP hPP hEP hEcomp
  have hnonneg := trace_mul_re_nonneg hZ hEP
  rw [complement_compression_trace_pairing hcomp, Matrix.trace_mul_comm,
    Matrix.sub_mul, Matrix.trace_sub, Complex.sub_re] at hnonneg
  exact sub_nonneg.mp hnonneg

theorem real_algebraMap_trace_mul (c : ℝ) (A : Matrix n n ℂ) :
    (algebraMap ℝ (Matrix n n ℂ) c * A).trace.re = c * A.trace.re := by
  simp [Algebra.algebraMap_eq_smul_one, Matrix.smul_mul, Matrix.trace_smul]

theorem hermitian_trace_pairing_le_norm {E Y : Matrix n n ℂ}
    (hE : E.IsHermitian) (hY : Y.IsHermitian) :
    (E * Y).trace.re ≤ ‖E‖ * (CFC.abs Y).trace.re := by
  have hupper : (algebraMap ℝ (Matrix n n ℂ) ‖E‖ - E).PosSemidef :=
    Matrix.le_iff.mp (IsSelfAdjoint.le_algebraMap_norm_self E hE.isSelfAdjoint)
  have hlower : (E + algebraMap ℝ (Matrix n n ℂ) ‖E‖).PosSemidef := by
    have h := Matrix.le_iff.mp
      (IsSelfAdjoint.neg_algebraMap_norm_le_self E hE.isSelfAdjoint)
    simpa only [sub_neg_eq_add] using h
  have hpos : Y⁺.PosSemidef := (CFC.posPart_nonneg Y).posSemidef
  have hneg : Y⁻.PosSemidef := (CFC.negPart_nonneg Y).posSemidef
  have hp := trace_mul_re_nonneg hupper hpos
  have hn := trace_mul_re_nonneg hlower hneg
  rw [Matrix.sub_mul, Matrix.trace_sub, Complex.sub_re, real_algebraMap_trace_mul] at hp
  rw [Matrix.add_mul, Matrix.trace_add, Complex.add_re, real_algebraMap_trace_mul] at hn
  have hparts : (E * Y).trace.re = (E * Y⁺).trace.re - (E * Y⁻).trace.re := by
    nth_rw 1 [← CFC.posPart_sub_negPart Y hY.isSelfAdjoint]
    simp only [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re]
  have habs : (CFC.abs Y).trace.re = Y⁺.trace.re + Y⁻.trace.re := by
    rw [← CFC.posPart_add_negPart Y hY.isSelfAdjoint, Matrix.trace_add, Complex.add_re]
  rw [hparts, habs, mul_add]
  linarith

theorem hermitian_trace_pairing_abs_le_norm {E Y : Matrix n n ℂ}
    (hE : E.IsHermitian) (hY : Y.IsHermitian) :
    |(E * Y).trace.re| ≤ ‖E‖ * (CFC.abs Y).trace.re := by
  have hp := hermitian_trace_pairing_le_norm hE hY
  have hn := hermitian_trace_pairing_le_norm hE.neg hY
  simp only [Matrix.neg_mul, Matrix.trace_neg, Complex.neg_re, norm_neg] at hn
  exact abs_le.mpr ⟨by linarith, hp⟩

theorem half_slack_pairing_saturation {X H : Matrix n n ℂ}
    (hX : X.PosSemidef) (hcap : ((1 / 2 : ℝ) • (1 : Matrix n n ℂ) - X).PosSemidef)
    (hH : H.IsHermitian)
    (hsat : (X * H).trace.re + H⁻.trace.re = 0) :
    H.PosSemidef ∧ H * X = 0 := by
  have hpos : H⁺.PosSemidef := (CFC.posPart_nonneg H).posSemidef
  have hneg : H⁻.PosSemidef := (CFC.negPart_nonneg H).posSemidef
  have hp0 := trace_mul_re_nonneg hX hpos
  have hn1 := trace_mul_re_nonneg hcap hneg
  simp only [Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul, Matrix.trace_sub,
    Matrix.trace_smul, Complex.sub_re] at hn1
  have hn0 : 0 ≤ H⁻.trace.re := (Complex.nonneg_iff.mp hneg.trace_nonneg).1
  have hparts : (X * H).trace.re = (X * H⁺).trace.re - (X * H⁻).trace.re := by
    nth_rw 1 [← CFC.posPart_sub_negPart H hH.isSelfAdjoint]
    simp only [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re]
  have htrneg : H⁻.trace.re = 0 := by
    simp only [Complex.smul_re, smul_eq_mul] at hn1
    linarith
  have hzneg : H⁻ = 0 := posSemidef_eq_zero_of_trace_re_eq_zero hneg htrneg
  have hHpos : H.PosSemidef := by
    have heq := (CFC.posPart_sub_negPart H hH.isSelfAdjoint).symm
    rw [hzneg, sub_zero] at heq
    rw [heq]
    exact hpos
  have htr : (H * X).trace.re = 0 := by
    rw [Matrix.trace_mul_comm]
    simpa only [hzneg, Matrix.trace_zero, Complex.zero_re, add_zero] using hsat
  exact ⟨hHpos, mul_eq_zero_of_posSemidef_trace_re_eq_zero hHpos hX htr⟩

end QuantumProver.PPTSupport.SupportBounds

open scoped BigOperators
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false

namespace QuantumProver.PPTSupport.SupportBounds

variable {n : Type*} [Fintype n] [DecidableEq n]

def effectSet (P : Matrix n n ℂ) : Set (Matrix n n ℂ) :=
  {E | (E - P).PosSemidef ∧ (1 - E).PosSemidef}

theorem effectSet_isClosed (P : Matrix n n ℂ) : IsClosed (effectSet P) := by
  change IsClosed ((fun E : Matrix n n ℂ => E - P) ⁻¹'
      {M : Matrix n n ℂ | M.PosSemidef} ∩
    (fun E : Matrix n n ℂ => 1 - E) ⁻¹' {M : Matrix n n ℂ | M.PosSemidef})
  exact (Matrix.posSemidef_is_closed.preimage (by fun_prop)).inter
    (Matrix.posSemidef_is_closed.preimage (by fun_prop))

theorem effectSet_norm_le_one {P E : Matrix n n ℂ}
    (hP : P.PosSemidef) (hE : E ∈ effectSet P) : ‖E‖ ≤ 1 := by
  have hEpos : E.PosSemidef := by
    simpa only [sub_add_cancel] using hE.1.add hP
  apply (CStarAlgebra.norm_le_iff_le_algebraMap E zero_le_one hEpos.nonneg).mpr
  simpa only [map_one] using (Matrix.le_iff.mpr hE.2 : E ≤ 1)

theorem effectSet_isCompact {P : Matrix n n ℂ} (hP : P.PosSemidef) :
    IsCompact (effectSet P) := by
  apply (isCompact_closedBall (0 : Matrix n n ℂ) 1).of_isClosed_subset (effectSet_isClosed P)
  intro E hE
  rw [Metric.mem_closedBall, dist_zero_right]
  exact effectSet_norm_le_one hP hE

theorem effectSet_convex (P : Matrix n n ℂ) : Convex ℝ (effectSet P) := by
  intro E hE F hF a b ha hb hab
  constructor
  · have hp : (a • (E - P) + b • (F - P)).PosSemidef :=
      (hE.1.smul ha).add (hF.1.smul hb)
    have heq : a • (E - P) + b • (F - P) = a • E + b • F - P := by
      simp only [smul_sub]
      calc
        (a • E - a • P) + (b • F - b • P) =
            a • E + b • F - (a • P + b • P) := by abel
        _ = a • E + b • F - P := by rw [← add_smul, hab, one_smul]
    rwa [heq] at hp
  · have hp : (a • (1 - E) + b • (1 - F)).PosSemidef :=
      (hE.2.smul ha).add (hF.2.smul hb)
    have heq : a • (1 - E) + b • (1 - F) = 1 - (a • E + b • F) := by
      simp only [smul_sub]
      calc
        (a • (1 : Matrix n n ℂ) - a • E) + (b • 1 - b • F) =
            (a • 1 + b • 1) - (a • E + b • F) := by abel
        _ = 1 - (a • E + b • F) := by rw [← add_smul, hab, one_smul]
    rwa [heq] at hp

theorem effectSet_nonempty_of_projection {P : Matrix n n ℂ}
    (hP : P.IsHermitian) (hPP : P * P = P) : (effectSet P).Nonempty := by
  have hQ : (1 - P).IsHermitian := Matrix.isHermitian_one.sub hP
  have hQQ : (1 - P) * (1 - P) = 1 - P := by
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, hPP]
    abel
  exact ⟨1, projection_posSemidef hQ hQQ, by simpa using (Matrix.PosSemidef.zero (n := n))⟩

end QuantumProver.PPTSupport.SupportBounds

namespace QuantumProver.PPTSupport.SupportBounds

variable {n : Type*} [Fintype n] [DecidableEq n]

 theorem posSemidef_norm_le_trace_re {M : Matrix n n ℂ} (hM : M.PosSemidef) :
    ‖M‖ ≤ M.trace.re := by
  have hn : ‖M‖ = ‖(fun i : n => (hM.1.eigenvalues i : ℂ))‖ := by
    conv_lhs => rw [hM.1.spectral_theorem]
    simp only [Unitary.conjStarAlgAut_apply, ← Unitary.coe_star,
      CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul,
      Matrix.l2_opNorm_diagonal]
    rfl
  rw [hn, hM.1.trace_eq_sum_eigenvalues]
  simp only [Complex.re_sum, Complex.ofReal_re]
  apply (pi_norm_le_iff_of_nonneg
    (Finset.sum_nonneg fun i _ => hM.eigenvalues_nonneg i)).mpr
  intro i
  simp only [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (hM.eigenvalues_nonneg i)]
  exact Finset.single_le_sum (fun j _ => hM.eigenvalues_nonneg j) (Finset.mem_univ i)

 theorem norm_le_trace_abs (M : Matrix n n ℂ) : ‖M‖ ≤ (CFC.abs M).trace.re := by
  rw [← CFC.norm_abs (a := M)]
  exact posSemidef_norm_le_trace_re (Matrix.nonneg_iff_posSemidef.mp (CFC.abs_nonneg M))

 def hermitianTraceBall : Set (Matrix n n ℂ) :=
  {Y | Y.IsHermitian ∧ (CFC.abs Y).trace.re ≤ 1}

 theorem continuous_trace_abs : Continuous (fun M : Matrix n n ℂ => (CFC.abs M).trace.re) :=
  Complex.continuous_re.comp
    ((Matrix.traceLinearMap n ℂ (α := ℝ)).continuous_of_finiteDimensional.comp CFC.continuous_abs)

 theorem hermitianTraceBall_isClosed : IsClosed (hermitianTraceBall (n := n)) := by
  have hh : IsClosed {M : Matrix n n ℂ | M.IsHermitian} := by
    change IsClosed {M : Matrix n n ℂ | star M = M}
    exact isClosed_eq continuous_star continuous_id
  exact hh.inter (isClosed_le continuous_trace_abs continuous_const)

 theorem hermitianTraceBall_isCompact : IsCompact (hermitianTraceBall (n := n)) := by
  apply (isCompact_closedBall (0 : Matrix n n ℂ) 1).of_isClosed_subset hermitianTraceBall_isClosed
  intro Y hY
  rw [Metric.mem_closedBall, dist_zero_right]
  exact (norm_le_trace_abs Y).trans hY.2

 theorem hermitianTraceBall_nonempty : (hermitianTraceBall (n := n)).Nonempty := by
  exact ⟨0, Matrix.isHermitian_zero, by simp⟩

end QuantumProver.PPTSupport.SupportBounds

namespace QuantumProver.PPTSupport.SupportBounds

variable {n : Type*} [Fintype n] [DecidableEq n]

 theorem trace_unitary_conj (U : unitary (Matrix n n ℂ)) (M : Matrix n n ℂ) :
    (Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) U M).trace = M.trace := by
  simp only [Unitary.conjStarAlgAut_apply]
  rw [Matrix.trace_mul_cycle, Unitary.coe_star_mul_self, Matrix.one_mul]

 theorem hermitian_trace_abs_eq_sum {M : Matrix n n ℂ} (hM : M.IsHermitian) :
    (CFC.abs M).trace.re = ∑ i : n, |hM.eigenvalues i| := by
  rw [CFC.abs_eq_cfc_norm M hM.isSelfAdjoint, hM.cfc_eq, Matrix.IsHermitian.cfc,
    trace_unitary_conj, Matrix.trace_diagonal]
  simp only [Complex.re_sum, Function.comp_apply, Real.norm_eq_abs]
  change (∑ i : n, (Complex.ofReal |hM.eigenvalues i|).re) = _
  simp only [Complex.ofReal_re]

 def spectralSign (x : ℝ) : ℝ := if 0 ≤ x then 1 else -1

 theorem spectralSign_mul (x : ℝ) : spectralSign x * x = |x| := by
  unfold spectralSign
  split_ifs with hx
  · rw [one_mul, abs_of_nonneg hx]
  · rw [neg_one_mul, abs_of_neg (lt_of_not_ge hx)]

 theorem hermitian_sign_witness {M : Matrix n n ℂ} (hM : M.IsHermitian) :
    ∃ K : Matrix n n ℂ, K.IsHermitian ∧ ‖K‖ ≤ 1 ∧
      (K * M).trace.re = (CFC.abs M).trace.re := by
  refine ⟨hM.cfc spectralSign, ?_, ?_, ?_⟩
  · rw [← hM.cfc_eq]
    exact Matrix.isHermitian_iff_isSelfAdjoint.mpr (cfc_predicate spectralSign M)
  · simp only [Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, ← Unitary.coe_star,
      CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul,
      Matrix.l2_opNorm_diagonal]
    apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
    intro i
    simp only [Function.comp_apply]
    unfold spectralSign
    split_ifs <;> norm_num
  · calc
      (hM.cfc spectralSign * M).trace.re =
          (hM.cfc spectralSign *
            Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) hM.eigenvectorUnitary
              (Matrix.diagonal (RCLike.ofReal ∘ hM.eigenvalues))).trace.re :=
        congrArg (fun N : Matrix n n ℂ => (hM.cfc spectralSign * N).trace.re)
          hM.spectral_theorem
      _ = ∑ i : n, spectralSign (hM.eigenvalues i) * hM.eigenvalues i := by
        change ((Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) hM.eigenvectorUnitary
            (Matrix.diagonal (RCLike.ofReal ∘ spectralSign ∘ hM.eigenvalues))) *
          (Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) hM.eigenvectorUnitary
            (Matrix.diagonal (RCLike.ofReal ∘ hM.eigenvalues)))).trace.re = _
        rw [← map_mul, trace_unitary_conj, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]
        simp only [Complex.re_sum, Function.comp_apply]
        change (∑ i : n, (Complex.ofReal (spectralSign (hM.eigenvalues i)) *
          Complex.ofReal (hM.eigenvalues i)).re) = _
        simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
          mul_zero, sub_zero]
      _ = (CFC.abs M).trace.re := by
        rw [hermitian_trace_abs_eq_sum hM]
        exact Finset.sum_congr rfl (fun i _ => spectralSign_mul _)

 theorem hermitian_trace_abs_convex {M N : Matrix n n ℂ}
    (hM : M.IsHermitian) (hN : N.IsHermitian) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (CFC.abs (a • M + b • N)).trace.re ≤
      a * (CFC.abs M).trace.re + b * (CFC.abs N).trace.re := by
  have hH : (a • M + b • N).IsHermitian :=
    (hM.smul (IsSelfAdjoint.all a)).add (hN.smul (IsSelfAdjoint.all b))
  obtain ⟨K, hK, hKn, hsat⟩ := hermitian_sign_witness hH
  have hKM : (K * M).trace.re ≤ (CFC.abs M).trace.re := by
    calc
      _ ≤ ‖K‖ * (CFC.abs M).trace.re := hermitian_trace_pairing_le_norm hK hM
      _ ≤ (CFC.abs M).trace.re := mul_le_of_le_one_left
        (Complex.nonneg_iff.mp (Matrix.PosSemidef.trace_nonneg
          (Matrix.nonneg_iff_posSemidef.mp (CFC.abs_nonneg M)))).1 hKn
  have hKN : (K * N).trace.re ≤ (CFC.abs N).trace.re := by
    calc
      _ ≤ ‖K‖ * (CFC.abs N).trace.re := hermitian_trace_pairing_le_norm hK hN
      _ ≤ (CFC.abs N).trace.re := mul_le_of_le_one_left
        (Complex.nonneg_iff.mp (Matrix.PosSemidef.trace_nonneg
          (Matrix.nonneg_iff_posSemidef.mp (CFC.abs_nonneg N)))).1 hKn
  rw [← hsat]
  simp only [Matrix.mul_add, Matrix.mul_smul, Matrix.trace_add, Matrix.trace_smul,
    Complex.add_re, Complex.smul_re, smul_eq_mul]
  exact add_le_add (mul_le_mul_of_nonneg_left hKM ha) (mul_le_mul_of_nonneg_left hKN hb)

 theorem hermitianTraceBall_convex : Convex ℝ (hermitianTraceBall (n := n)) := by
  intro M hM N hN a b ha hb hab
  refine ⟨(hM.1.smul (IsSelfAdjoint.all a)).add (hN.1.smul (IsSelfAdjoint.all b)), ?_⟩
  calc
    _ ≤ a * (CFC.abs M).trace.re + b * (CFC.abs N).trace.re :=
      hermitian_trace_abs_convex hM.1 hN.1 ha hb
    _ ≤ a * 1 + b * 1 := add_le_add
      (mul_le_mul_of_nonneg_left hM.2 ha) (mul_le_mul_of_nonneg_left hN.2 hb)
    _ = 1 := by simpa only [mul_one] using hab

end QuantumProver.PPTSupport.SupportBounds

namespace QuantumProver.PPTSupport.SupportBounds

variable {n : Type*} [Fintype n] [DecidableEq n]

 theorem hermitian_norm_eq_eigenvalues {M : Matrix n n ℂ} (hM : M.IsHermitian) :
    ‖M‖ = ‖(fun i : n => (hM.eigenvalues i : ℂ))‖ := by
  conv_lhs => rw [hM.spectral_theorem]
  simp only [Unitary.conjStarAlgAut_apply, ← Unitary.coe_star,
    CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul,
    Matrix.l2_opNorm_diagonal]
  rfl

 theorem hermitian_operator_norm_witness {M : Matrix n n ℂ} (hM : M.IsHermitian) :
    ∃ Y : Matrix n n ℂ, Y ∈ hermitianTraceBall ∧ (M * Y).trace.re = ‖M‖ := by
  by_cases hn : Nonempty n
  · letI : Nonempty n := hn
    obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ
      (fun j : n => |hM.eigenvalues j|) Finset.univ_nonempty
    have hnorm : ‖M‖ = |hM.eigenvalues i| := by
      rw [hermitian_norm_eq_eigenvalues hM]
      apply le_antisymm
      · apply (pi_norm_le_iff_of_nonneg (abs_nonneg _)).mpr
        intro j
        simpa only [Complex.norm_real, Real.norm_eq_abs] using hi j (Finset.mem_univ j)
      · simpa only [Complex.norm_real, Real.norm_eq_abs] using
          norm_le_pi_norm (fun j : n => (hM.eigenvalues j : ℂ)) i
    let D : Matrix n n ℂ := Matrix.diagonal (fun j : n => if j = i then 1 else 0)
    let P : Matrix n n ℂ :=
      Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) hM.eigenvectorUnitary D
    have hD : D.PosSemidef := by
      apply Matrix.posSemidef_diagonal_iff.mpr
      intro j
      split_ifs <;> simp
    have hP : P.PosSemidef := by
      simpa only [P, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose] using
        hD.mul_mul_conjTranspose_same (hM.eigenvectorUnitary : Matrix n n ℂ)
    have htr : P.trace = 1 := by
      dsimp only [P]
      rw [trace_unitary_conj]
      simp [D]
    have hPM : (P * M).trace = (hM.eigenvalues i : ℂ) := by
      calc
        _ = (P * Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) hM.eigenvectorUnitary
            (Matrix.diagonal (RCLike.ofReal ∘ hM.eigenvalues))).trace :=
          congrArg (fun N : Matrix n n ℂ => (P * N).trace) hM.spectral_theorem
        _ = (D * Matrix.diagonal (RCLike.ofReal ∘ hM.eigenvalues)).trace := by
          dsimp only [P]
          rw [← map_mul, trace_unitary_conj]
        _ = (hM.eigenvalues i : ℂ) := by
          simp [D, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]
    refine ⟨spectralSign (hM.eigenvalues i) • P, ⟨hP.1.smul (IsSelfAdjoint.all _), ?_⟩, ?_⟩
    · rw [CFC.abs_smul, CFC.abs_of_nonneg P hP.nonneg, Matrix.trace_smul,
        Complex.smul_re, htr]
      unfold spectralSign
      split_ifs <;> norm_num
    · rw [Matrix.trace_mul_comm, Matrix.smul_mul, Matrix.trace_smul, hPM,
        Complex.smul_re, Complex.ofReal_re, smul_eq_mul,
        spectralSign_mul, hnorm]
  · letI : IsEmpty n := not_nonempty_iff.mp hn
    have hz : M = 0 := Subsingleton.elim _ _
    subst M
    refine ⟨0, ⟨Matrix.isHermitian_zero, by simp⟩, by simp⟩

end QuantumProver.PPTSupport.SupportBounds

namespace QuantumProver.PPTSupport.SupportBounds

variable {n : Type*} [Fintype n] [DecidableEq n]

 theorem effect_trace_lower_negPart {X H : Matrix n n ℂ}
    (hX : X.PosSemidef) (hIX : (1 - X).PosSemidef) (hH : H.IsHermitian) :
    -H⁻.trace.re ≤ (X * H).trace.re := by
  have hp := trace_mul_re_nonneg hX (CFC.posPart_nonneg H).posSemidef
  have hn := trace_mul_re_nonneg hIX (CFC.negPart_nonneg H).posSemidef
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub, Complex.sub_re] at hn
  have hpair : (X * H).trace.re = (X * H⁺).trace.re - (X * H⁻).trace.re := by
    conv_lhs => rw [← CFC.posPart_sub_negPart H hH.isSelfAdjoint]
    simp only [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re]
  rw [hpair]
  linarith

 theorem effectSet_compressed_effect {P X : Matrix n n ℂ}
    (hP : P.IsHermitian) (hPP : P * P = P)
    (hX : X.PosSemidef) (hIX : (1 - X).PosSemidef) :
    P + (1 - P) * X * (1 - P) ∈ effectSet P := by
  have hQ : (1 - P).IsHermitian := Matrix.isHermitian_one.sub hP
  have hQQ : (1 - P) * (1 - P) = 1 - P := by
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, hPP]
    abel
  constructor
  · have hc := hX.mul_mul_conjTranspose_same ((1 : Matrix n n ℂ) - P)
    rw [hQ.eq] at hc
    simpa only [add_sub_cancel_left] using hc
  · have heq : 1 - (P + (1 - P) * X * (1 - P)) =
        (1 - P) * (1 - X) * (1 - P) := by
      calc
        _ = (1 - P) - (1 - P) * X * (1 - P) := by abel
        _ = (1 - P) * (1 - P) - (1 - P) * X * (1 - P) := by rw [hQQ]
        _ = (1 - P) * (1 - X) * (1 - P) := by noncomm_ring
    rw [heq]
    have hc := hIX.mul_mul_conjTranspose_same ((1 : Matrix n n ℂ) - P)
    rw [hQ.eq] at hc
    exact hc

 def spectralNegative (x : ℝ) : ℝ := if x < 0 then 1 else 0

 theorem spectralNegative_mul (x : ℝ) : spectralNegative x * x = -x⁻ := by
  by_cases hx : x < 0
  · rw [negPart_eq_neg.mpr hx.le]
    simp [spectralNegative, hx]
  · rw [negPart_eq_zero.mpr (le_of_not_gt hx)]
    simp [spectralNegative, hx]

 theorem hermitian_trace_negPart_eq_sum {M : Matrix n n ℂ} (hM : M.IsHermitian) :
    M⁻.trace.re = ∑ i : n, (hM.eigenvalues i)⁻ := by
  rw [CFC.negPart_def, cfcₙ_eq_cfc, hM.cfc_eq, Matrix.IsHermitian.cfc,
    trace_unitary_conj, Matrix.trace_diagonal]
  simp only [Complex.re_sum, Function.comp_apply]
  change (∑ i : n, (Complex.ofReal ((hM.eigenvalues i)⁻)).re) = _
  simp only [Complex.ofReal_re]

 theorem hermitian_negative_part_minimizer {H : Matrix n n ℂ} (hH : H.IsHermitian) :
    ∃ X : Matrix n n ℂ, X.PosSemidef ∧ (1 - X).PosSemidef ∧
      (X * H).trace.re = -H⁻.trace.re := by
  let D : Matrix n n ℂ :=
    Matrix.diagonal (RCLike.ofReal ∘ spectralNegative ∘ hH.eigenvalues)
  let X : Matrix n n ℂ :=
    Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) hH.eigenvectorUnitary D
  have hD : D.PosSemidef := by
    apply Matrix.posSemidef_diagonal_iff.mpr
    intro i
    simp only [Function.comp_apply, spectralNegative]
    split_ifs <;> norm_num
  have hID : (1 - D).PosSemidef := by
    have hd : 1 - D = Matrix.diagonal
        (fun i : n => 1 - (spectralNegative (hH.eigenvalues i) : ℂ)) := by
      ext i j
      by_cases hij : i = j <;>
        simp [D, Matrix.diagonal_apply, Matrix.one_apply, hij, Function.comp_def]
    rw [hd]
    apply Matrix.posSemidef_diagonal_iff.mpr
    intro i
    unfold spectralNegative
    split_ifs <;> norm_num
  have hX : X.PosSemidef := by
    simpa only [X, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose] using
      hD.mul_mul_conjTranspose_same (hH.eigenvectorUnitary : Matrix n n ℂ)
  have hIX : (1 - X).PosSemidef := by
    have hx : (Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) hH.eigenvectorUnitary
        (1 - D)).PosSemidef := by
      simpa only [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose] using
        hID.mul_mul_conjTranspose_same (hH.eigenvectorUnitary : Matrix n n ℂ)
    simpa only [map_sub, map_one, X] using hx
  refine ⟨X, hX, hIX, ?_⟩
  calc
    (X * H).trace.re = (X *
        Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) hH.eigenvectorUnitary
          (Matrix.diagonal (RCLike.ofReal ∘ hH.eigenvalues))).trace.re :=
      congrArg (fun M : Matrix n n ℂ => (X * M).trace.re) hH.spectral_theorem
    _ = ∑ i : n, spectralNegative (hH.eigenvalues i) * hH.eigenvalues i := by
      dsimp only [X]
      rw [← map_mul, trace_unitary_conj, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]
      simp only [D, Complex.re_sum, Function.comp_apply]
      change (∑ i : n, (Complex.ofReal (spectralNegative (hH.eigenvalues i)) *
        Complex.ofReal (hH.eigenvalues i)).re) = _
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        mul_zero, sub_zero]
    _ = -H⁻.trace.re := by
      rw [hermitian_trace_negPart_eq_sum hH, ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl (fun i _ => spectralNegative_mul _)

end QuantumProver.PPTSupport.SupportBounds

namespace QuantumProver.PPTSupport.SupportBounds

variable {n : Type*} [Fintype n] [DecidableEq n]

 def tracePairingRight (Y : Matrix n n ℂ) : Matrix n n ℂ →ₗ[ℝ] ℝ where
  toFun E := (E * Y).trace.re
  map_add' E F := by simp [Matrix.add_mul, Matrix.trace_add]
  map_smul' a E := by simp [Matrix.smul_mul, Matrix.trace_smul, Complex.smul_re]

 def tracePairingLeft (E : Matrix n n ℂ) : Matrix n n ℂ →ₗ[ℝ] ℝ where
  toFun Y := (E * Y).trace.re
  map_add' Y Z := by simp [Matrix.mul_add, Matrix.trace_add]
  map_smul' a Y := by simp [Matrix.mul_smul, Matrix.trace_smul, Complex.smul_re]

 theorem matrixRealLinear_convexOn (l : Matrix n n ℂ →ₗ[ℝ] ℝ)
    {S : Set (Matrix n n ℂ)} (hS : Convex ℝ S) : ConvexOn ℝ S l := by
  refine ⟨hS, ?_⟩
  intro E hE F hF a b ha hb hab
  simp only [map_add, map_smul]
  exact le_rfl

 theorem matrixRealLinear_concaveOn (l : Matrix n n ℂ →ₗ[ℝ] ℝ)
    {S : Set (Matrix n n ℂ)} (hS : Convex ℝ S) : ConcaveOn ℝ S l := by
  refine ⟨hS, ?_⟩
  intro E hE F hF a b ha hb hab
  simp only [map_add, map_smul]
  exact le_rfl

 theorem exists_effect_trace_saddle {P : Matrix n n ℂ}
    (hP : P.IsHermitian) (hPP : P * P = P)
    (T : Matrix n n ℂ →ₗ[ℝ] Matrix n n ℂ) :
    ∃ E ∈ effectSet P, ∃ Y ∈ hermitianTraceBall,
      IsSaddlePointOn (effectSet P) hermitianTraceBall
        (fun E Y : Matrix n n ℂ => (T E * Y).trace.re) E Y := by
  apply Sion.exists_isSaddlePointOn
    (effectSet_nonempty_of_projection hP hPP) (effectSet_convex P)
    (effectSet_isCompact (projection_posSemidef hP hPP))
  · intro Y hY
    exact ((tracePairingRight Y).comp T).continuous_of_finiteDimensional.continuousOn.lowerSemicontinuousOn
  · intro Y hY
    exact (matrixRealLinear_convexOn ((tracePairingRight Y).comp T)
      (effectSet_convex P)).quasiconvexOn
  · exact hermitianTraceBall_convex
  · exact hermitianTraceBall_nonempty
  · exact hermitianTraceBall_isCompact
  · intro E hE
    exact (tracePairingLeft (T E)).continuous_of_finiteDimensional.continuousOn.upperSemicontinuousOn
  · intro E hE
    exact (matrixRealLinear_concaveOn (tracePairingLeft (T E))
      hermitianTraceBall_convex).quasiconcaveOn

 theorem exists_effect_norm_dual {P : Matrix n n ℂ}
    (hP : P.IsHermitian) (hPP : P * P = P)
    (T : Matrix n n ℂ →ₗ[ℝ] Matrix n n ℂ)
    (hT : ∀ E : Matrix n n ℂ, E.IsHermitian → (T E).IsHermitian) :
    ∃ E ∈ effectSet P, ∃ Y ∈ hermitianTraceBall,
      (T E * Y).trace.re = ‖T E‖ ∧
        (∀ F ∈ effectSet P, ‖T E‖ ≤ ‖T F‖) ∧
        IsSaddlePointOn (effectSet P) hermitianTraceBall
          (fun E Y : Matrix n n ℂ => (T E * Y).trace.re) E Y := by
  obtain ⟨E, hE, Y, hY, hs⟩ := exists_effect_trace_saddle hP hPP T
  have hEH : E.IsHermitian := by
    simpa only [sub_add_cancel] using hE.1.1.add hP
  have hTE := hT E hEH
  obtain ⟨Z, hZ, hZtr⟩ := hermitian_operator_norm_witness hTE
  have hlow : ‖T E‖ ≤ (T E * Y).trace.re := by
    simpa only [hZtr] using hs E hE Z hZ
  have hupp : (T E * Y).trace.re ≤ ‖T E‖ := by
    calc
      _ ≤ ‖T E‖ * (CFC.abs Y).trace.re := hermitian_trace_pairing_le_norm hTE hY.1
      _ ≤ ‖T E‖ := mul_le_of_le_one_right (norm_nonneg _) hY.2
  have heq := le_antisymm hupp hlow
  refine ⟨E, hE, Y, hY, heq, ?_, hs⟩
  intro F hF
  have hFH : F.IsHermitian := by
    simpa only [sub_add_cancel] using hF.1.1.add hP
  calc
    ‖T E‖ = (T E * Y).trace.re := heq.symm
    _ ≤ (T F * Y).trace.re := hs F hF Y hY
    _ ≤ ‖T F‖ * (CFC.abs Y).trace.re := hermitian_trace_pairing_le_norm (hT F hFH) hY.1
    _ ≤ ‖T F‖ := mul_le_of_le_one_right (norm_nonneg _) hY.2

end QuantumProver.PPTSupport.SupportBounds

namespace QuantumProver.PPTSupport.SupportBounds

variable {n : Type*} [Fintype n] [DecidableEq n]

 theorem compressed_trace_pairing (Q X Z : Matrix n n ℂ) :
    ((Q * X * Q) * Z).trace = (X * (Q * Z * Q)).trace := by
  calc
    _ = (Q * X * (Q * Z)).trace := by simp only [Matrix.mul_assoc]
    _ = ((Q * Z) * Q * X).trace := Matrix.trace_mul_cycle Q X (Q * Z)
    _ = ((Q * Z * Q) * X).trace := rfl
    _ = (X * (Q * Z * Q)).trace := Matrix.trace_mul_comm _ _

 theorem effectSet_trace_minimum {P Z : Matrix n n ℂ}
    (hP : P.IsHermitian) (hPP : P * P = P) (hZ : Z.IsHermitian) :
    ∃ E ∈ effectSet P,
      (E * Z).trace.re = (P * Z).trace.re - ((1 - P) * Z * (1 - P))⁻.trace.re ∧
        ∀ F ∈ effectSet P, (E * Z).trace.re ≤ (F * Z).trace.re := by
  let H := (1 - P) * Z * (1 - P)
  have hQ : (1 - P).IsHermitian := Matrix.isHermitian_one.sub hP
  have hH : H.IsHermitian := by
    change ((1 - P) * Z * (1 - P))ᴴ = (1 - P) * Z * (1 - P)
    simp only [Matrix.conjTranspose_mul, hQ.eq, hZ.eq, Matrix.mul_assoc]
  obtain ⟨X, hX, hIX, hXpair⟩ := hermitian_negative_part_minimizer hH
  have hE := effectSet_compressed_effect hP hPP hX hIX
  have heq : ((P + (1 - P) * X * (1 - P)) * Z).trace.re =
      (P * Z).trace.re - H⁻.trace.re := by
    rw [Matrix.add_mul, Matrix.trace_add, Complex.add_re, compressed_trace_pairing]
    change (P * Z).trace.re + (X * H).trace.re = _
    rw [hXpair]
    ring
  refine ⟨P + (1 - P) * X * (1 - P), hE, heq, ?_⟩
  intro F hF
  rw [heq]
  have hIFP : (1 - (F - P)).PosSemidef := by
    have hp := hF.2.add (projection_posSemidef hP hPP)
    convert hp using 1 <;> abel
  have hlower := effect_trace_lower_negPart hF.1 hIFP hH
  have hcomp := feasible_complement_supported hP hPP hF.1 hF.2
  have htrace : ((F - P) * H).trace = (F * Z).trace - (P * Z).trace := by
    calc
      _ = (H * (F - P)).trace := Matrix.trace_mul_comm _ _
      _ = (Z * (F - P)).trace := complement_compression_trace_pairing hcomp
      _ = ((F - P) * Z).trace := Matrix.trace_mul_comm _ _
      _ = (F * Z).trace - (P * Z).trace := by rw [Matrix.sub_mul, Matrix.trace_sub]
  rw [htrace, Complex.sub_re] at hlower
  linarith

end QuantumProver.PPTSupport.SupportBounds

namespace QuantumProver.PPTSupport.SupportBounds

variable {n j : Type*} [Fintype n] [DecidableEq n] [Fintype j]

def matrixPinch (projs : j → Matrix n n ℂ) (H : Matrix n n ℂ) : Matrix n n ℂ :=
  ∑ i, projs i * H * projs i

theorem matrixPinch_add (projs : j → Matrix n n ℂ) (H K : Matrix n n ℂ) :
    matrixPinch projs (H + K) = matrixPinch projs H + matrixPinch projs K := by
  simp [matrixPinch, Matrix.mul_add, Matrix.add_mul, Finset.sum_add_distrib]

theorem matrixPinch_sub (projs : j → Matrix n n ℂ) (H K : Matrix n n ℂ) :
    matrixPinch projs (H - K) = matrixPinch projs H - matrixPinch projs K := by
  simp [matrixPinch, Matrix.mul_sub, Matrix.sub_mul, Finset.sum_sub_distrib]

theorem matrixPinch_one (projs : j → Matrix n n ℂ)
    (hprojssq : ∀ i, projs i * projs i = projs i) (hprojssum : ∑ i, projs i = 1) :
    matrixPinch projs 1 = 1 := by
  simpa only [matrixPinch, Matrix.mul_one, hprojssq] using hprojssum

theorem matrixPinch_isHermitian (projs : j → Matrix n n ℂ)
    (hprojs : ∀ i, (projs i).IsHermitian) {H : Matrix n n ℂ} (hH : H.IsHermitian) :
    (matrixPinch projs H).IsHermitian := by
  have hprojsstar : ∀ i, (projs i)ᴴ = projs i := fun i => (hprojs i).eq
  change (matrixPinch projs H)ᴴ = matrixPinch projs H
  simp_rw [matrixPinch, Matrix.conjTranspose_sum, Matrix.conjTranspose_mul,
    hprojsstar, hH.eq, Matrix.mul_assoc]

theorem matrixPinch_posSemidef (projs : j → Matrix n n ℂ)
    (hprojs : ∀ i, (projs i).IsHermitian) {H : Matrix n n ℂ} (hH : H.PosSemidef) :
    (matrixPinch projs H).PosSemidef := by
  unfold matrixPinch
  exact Matrix.posSemidef_sum _ fun i _ => by
    simpa only [(hprojs i).eq] using hH.mul_mul_conjTranspose_same (projs i)

theorem norm_matrix_one_le_one : ‖(1 : Matrix n n ℂ)‖ ≤ 1 := by
  by_cases hn : Nonempty n
  · letI : Nonempty n := hn
    simp
  · letI : IsEmpty n := not_nonempty_iff.mp hn
    have hzero : (1 : Matrix n n ℂ) = 0 := Subsingleton.elim _ _
    rw [hzero, norm_zero]
    norm_num

theorem matrixPinch_norm_le_one (projs : j → Matrix n n ℂ)
    (hprojs : ∀ i, (projs i).IsHermitian)
    (hprojssq : ∀ i, projs i * projs i = projs i) (hprojssum : ∑ i, projs i = 1)
    {K : Matrix n n ℂ} (hK : K.IsHermitian) (hKn : ‖K‖ ≤ 1) :
    ‖matrixPinch projs K‖ ≤ 1 := by
  have hupper0 : (algebraMap ℝ (Matrix n n ℂ) ‖K‖ - K).PosSemidef :=
    Matrix.le_iff.mp (IsSelfAdjoint.le_algebraMap_norm_self K hK.isSelfAdjoint)
  have hlower0 : (K + algebraMap ℝ (Matrix n n ℂ) ‖K‖).PosSemidef := by
    have h := Matrix.le_iff.mp
      (IsSelfAdjoint.neg_algebraMap_norm_le_self K hK.isSelfAdjoint)
    simpa only [sub_neg_eq_add] using h
  have hgap : (1 - algebraMap ℝ (Matrix n n ℂ) ‖K‖).PosSemidef := by
    have h := (Matrix.PosSemidef.one : (1 : Matrix n n ℂ).PosSemidef).smul
      (sub_nonneg.mpr hKn)
    simpa only [sub_smul, one_smul, Algebra.algebraMap_eq_smul_one] using h
  have hupper : (1 - K).PosSemidef := by
    convert hgap.add hupper0 using 1 <;> abel
  have hlower : (K + 1).PosSemidef := by
    convert hlower0.add hgap using 1 <;> abel
  have hPupper : (1 - matrixPinch projs K).PosSemidef := by
    have h := matrixPinch_posSemidef projs hprojs hupper
    simpa only [matrixPinch_sub, matrixPinch_one projs hprojssq hprojssum] using h
  have hPlower : (matrixPinch projs K + 1).PosSemidef := by
    have h := matrixPinch_posSemidef projs hprojs hlower
    simpa only [matrixPinch_add, matrixPinch_one projs hprojssq hprojssum] using h
  have hle : matrixPinch projs K ≤ 1 := Matrix.le_iff.mpr hPupper
  have hge : -(1 : Matrix n n ℂ) ≤ matrixPinch projs K := by
    apply Matrix.le_iff.mpr
    simpa only [sub_neg_eq_add] using hPlower
  calc
    _ ≤ max ‖(-1 : Matrix n n ℂ)‖ ‖(1 : Matrix n n ℂ)‖ :=
      IsSelfAdjoint.norm_le_max_of_le_of_le hge hle
        (matrixPinch_isHermitian projs hprojs hK).isSelfAdjoint
    _ ≤ 1 := max_le (by simpa only [norm_neg] using (norm_matrix_one_le_one (n := n)))
      (norm_matrix_one_le_one (n := n))

theorem matrixPinch_trace_adjoint (projs : j → Matrix n n ℂ)
    (K H : Matrix n n ℂ) :
    (K * matrixPinch projs H).trace = (matrixPinch projs K * H).trace := by
  unfold matrixPinch
  simp_rw [Matrix.mul_sum, Matrix.sum_mul, Matrix.trace_sum]
  apply Finset.sum_congr rfl
  intro i _
  calc
    _ = (K * (projs i * H) * projs i).trace := by simp only [Matrix.mul_assoc]
    _ = (projs i * K * (projs i * H)).trace := Matrix.trace_mul_cycle _ _ _
    _ = _ := by simp only [Matrix.mul_assoc]

theorem matrixPinch_trace_abs_le (projs : j → Matrix n n ℂ)
    (hprojs : ∀ i, (projs i).IsHermitian)
    (hprojssq : ∀ i, projs i * projs i = projs i) (hprojssum : ∑ i, projs i = 1)
    {H : Matrix n n ℂ} (hH : H.IsHermitian) :
    (CFC.abs (matrixPinch projs H)).trace.re ≤ (CFC.abs H).trace.re := by
  obtain ⟨K, hK, hKn, hsat⟩ :=
    hermitian_sign_witness (matrixPinch_isHermitian projs hprojs hH)
  rw [← hsat, matrixPinch_trace_adjoint]
  calc
    _ ≤ ‖matrixPinch projs K‖ * (CFC.abs H).trace.re :=
      hermitian_trace_pairing_le_norm (matrixPinch_isHermitian projs hprojs hK) hH
    _ ≤ (CFC.abs H).trace.re := mul_le_of_le_one_left
      (Complex.nonneg_iff.mp (Matrix.PosSemidef.trace_nonneg
        (Matrix.nonneg_iff_posSemidef.mp (CFC.abs_nonneg H)))).1
      (matrixPinch_norm_le_one projs hprojs hprojssq hprojssum hK hKn)

end QuantumProver.PPTSupport.SupportBounds

namespace QuantumProver.PPTSupport.SupportBounds

variable {n j : Type*} [Fintype n] [DecidableEq n] [Fintype j]

theorem matrixPinch_trace (projs : j → Matrix n n ℂ)
    (hprojssq : ∀ i, projs i * projs i = projs i) (hprojssum : ∑ i, projs i = 1)
    (H : Matrix n n ℂ) : (matrixPinch projs H).trace = H.trace := by
  have h := matrixPinch_trace_adjoint projs (1 : Matrix n n ℂ) H
  simpa only [Matrix.one_mul, matrixPinch_one projs hprojssq hprojssum] using h

theorem negPart_trace_from_abs {H : Matrix n n ℂ} (hH : H.IsHermitian) :
    2 * H⁻.trace.re = (CFC.abs H).trace.re - H.trace.re := by
  have habs : (CFC.abs H).trace.re = H⁺.trace.re + H⁻.trace.re := by
    rw [← CFC.posPart_add_negPart H hH.isSelfAdjoint, Matrix.trace_add, Complex.add_re]
  have hdiff : H.trace.re = H⁺.trace.re - H⁻.trace.re := by
    nth_rw 1 [← CFC.posPart_sub_negPart H hH.isSelfAdjoint]
    rw [Matrix.trace_sub, Complex.sub_re]
  linarith

theorem matrixPinch_negPart_trace_le (projs : j → Matrix n n ℂ)
    (hprojs : ∀ i, (projs i).IsHermitian)
    (hprojssq : ∀ i, projs i * projs i = projs i) (hprojssum : ∑ i, projs i = 1)
    {H : Matrix n n ℂ} (hH : H.IsHermitian) :
    (matrixPinch projs H)⁻.trace.re ≤ H⁻.trace.re := by
  have ha := matrixPinch_trace_abs_le projs hprojs hprojssq hprojssum hH
  have ht := congrArg Complex.re (matrixPinch_trace projs hprojssq hprojssum H)
  have hn := negPart_trace_from_abs (matrixPinch_isHermitian projs hprojs hH)
  have hHn := negPart_trace_from_abs hH
  linarith

theorem matrixPinch_fixed_of_commute (projs : j → Matrix n n ℂ)
    (hprojssq : ∀ i, projs i * projs i = projs i) (hprojssum : ∑ i, projs i = 1)
    (P : Matrix n n ℂ) (hcomm : ∀ i, P * projs i = projs i * P) :
    matrixPinch projs P = P := by
  calc
    _ = ∑ i, projs i * (P * projs i) := by simp only [matrixPinch, Matrix.mul_assoc]
    _ = ∑ i, projs i * (projs i * P) := by simp_rw [hcomm]
    _ = ∑ i, projs i * P := by simp_rw [← Matrix.mul_assoc, hprojssq]
    _ = (∑ i, projs i) * P := by rw [Matrix.sum_mul]
    _ = P := by rw [hprojssum, Matrix.one_mul]

theorem matrixPinch_trace_pairing_fixed (projs : j → Matrix n n ℂ)
    (hprojssq : ∀ i, projs i * projs i = projs i) (hprojssum : ∑ i, projs i = 1)
    (P H : Matrix n n ℂ) (hcomm : ∀ i, P * projs i = projs i * P) :
    (P * matrixPinch projs H).trace = (P * H).trace := by
  rw [matrixPinch_trace_adjoint, matrixPinch_fixed_of_commute projs hprojssq hprojssum P hcomm]

theorem matrixPinch_compression (projs : j → Matrix n n ℂ)
    (Q H : Matrix n n ℂ) (hcomm : ∀ i, Q * projs i = projs i * Q) :
    matrixPinch projs (Q * H * Q) = Q * matrixPinch projs H * Q := by
  simp only [matrixPinch, Matrix.mul_sum, Matrix.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  calc
    _ = (projs i * Q) * H * (Q * projs i) := by noncomm_ring
    _ = (Q * projs i) * H * (projs i * Q) :=
      congrArg₂ (fun X Y : Matrix n n ℂ => X * H * Y) (hcomm i).symm (hcomm i)
    _ = _ := by noncomm_ring

theorem matrixPinch_compressed_negPart_trace_le (projs : j → Matrix n n ℂ)
    (hprojs : ∀ i, (projs i).IsHermitian)
    (hprojssq : ∀ i, projs i * projs i = projs i) (hprojssum : ∑ i, projs i = 1)
    {Q H : Matrix n n ℂ} (hQ : Q.IsHermitian) (hH : H.IsHermitian)
    (hcomm : ∀ i, Q * projs i = projs i * Q) :
    (Q * matrixPinch projs H * Q)⁻.trace.re ≤ (Q * H * Q)⁻.trace.re := by
  have hC : (Q * H * Q).IsHermitian := by
    change (Q * H * Q)ᴴ = Q * H * Q
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hQ.eq, hH.eq]
    simp only [Matrix.mul_assoc]
  have h := matrixPinch_negPart_trace_le projs hprojs hprojssq hprojssum hC
  simpa only [matrixPinch_compression projs Q H hcomm] using h

end QuantumProver.PPTSupport.SupportBounds

namespace QuantumProver.PPTSupport.SupportBounds

variable {n j : Type*} [Fintype n] [DecidableEq n] [Fintype j]

theorem matrixUnitaryConj_isHermitian (U : unitary (Matrix n n ℂ))
    {H : Matrix n n ℂ} (hH : H.IsHermitian) :
    (Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) U H).IsHermitian := by
  let φ := Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) U
  change star (φ H) = φ H
  rw [← map_star, hH.isSelfAdjoint.star_eq]

theorem matrixUnitaryConj_norm (U : unitary (Matrix n n ℂ)) (H : Matrix n n ℂ) :
    ‖Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) U H‖ = ‖H‖ := by
  simp only [Unitary.conjStarAlgAut_apply, ← Unitary.coe_star,
    CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul]

theorem matrixUnitaryConj_trace_pullback (U : unitary (Matrix n n ℂ))
    (K H : Matrix n n ℂ) :
    (K * Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) U H).trace =
      (Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) (star U) K * H).trace := by
  simp only [Unitary.conjStarAlgAut_apply, ← Unitary.coe_star, star_star]
  calc
    _ = (K * (U : Matrix n n ℂ) * H *
        ((star U : unitary (Matrix n n ℂ)) : Matrix n n ℂ)).trace := by
      simp only [Matrix.mul_assoc]
    _ = (((star U : unitary (Matrix n n ℂ)) : Matrix n n ℂ) *
        (K * (U : Matrix n n ℂ)) * H).trace := Matrix.trace_mul_cycle _ _ _
    _ = _ := by simp only [Matrix.mul_assoc]

def matrixUnitaryAverage (w : j → ℝ) (U : j → unitary (Matrix n n ℂ))
    (H : Matrix n n ℂ) : Matrix n n ℂ :=
  ∑ i, w i • Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) (U i) H

theorem matrixUnitaryAverage_isHermitian (w : j → ℝ)
    (U : j → unitary (Matrix n n ℂ)) {H : Matrix n n ℂ} (hH : H.IsHermitian) :
    (matrixUnitaryAverage w U H).IsHermitian := by
  apply Matrix.isHermitian_iff_isSelfAdjoint.mpr
  exact isSelfAdjoint_sum _ fun i _ =>
    ((matrixUnitaryConj_isHermitian (U i) hH).smul (IsSelfAdjoint.all (w i))).isSelfAdjoint

theorem matrixUnitaryAverage_trace (w : j → ℝ)
    (U : j → unitary (Matrix n n ℂ)) (hw : ∑ i, w i = 1) (H : Matrix n n ℂ) :
    (matrixUnitaryAverage w U H).trace = H.trace := by
  simp only [matrixUnitaryAverage, Matrix.trace_sum, Matrix.trace_smul, trace_unitary_conj]
  rw [← Finset.sum_smul, hw, one_smul]

theorem matrixUnitaryAverage_trace_abs_le (w : j → ℝ)
    (U : j → unitary (Matrix n n ℂ)) (hw : ∀ i, 0 ≤ w i) (hws : ∑ i, w i = 1)
    {H : Matrix n n ℂ} (hH : H.IsHermitian) :
    (CFC.abs (matrixUnitaryAverage w U H)).trace.re ≤ (CFC.abs H).trace.re := by
  obtain ⟨K, hK, hKn, hsat⟩ :=
    hermitian_sign_witness (matrixUnitaryAverage_isHermitian w U hH)
  have hterm (i : j) :
      (K * Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) (U i) H).trace.re ≤
        (CFC.abs H).trace.re := by
    rw [matrixUnitaryConj_trace_pullback]
    calc
      _ ≤ ‖Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) (star (U i)) K‖ *
          (CFC.abs H).trace.re :=
        hermitian_trace_pairing_le_norm (matrixUnitaryConj_isHermitian (star (U i)) hK) hH
      _ ≤ (CFC.abs H).trace.re := by
        rw [matrixUnitaryConj_norm]
        exact mul_le_of_le_one_left
          (Complex.nonneg_iff.mp (Matrix.PosSemidef.trace_nonneg
            (Matrix.nonneg_iff_posSemidef.mp (CFC.abs_nonneg H)))).1 hKn
  rw [← hsat]
  simp only [matrixUnitaryAverage, Matrix.mul_sum, Matrix.mul_smul, Matrix.trace_sum,
    Matrix.trace_smul, Complex.re_sum, Complex.smul_re, smul_eq_mul]
  calc
    _ ≤ ∑ i, w i * (CFC.abs H).trace.re :=
      Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hterm i) (hw i)
    _ = (∑ i, w i) * (CFC.abs H).trace.re := by rw [Finset.sum_mul]
    _ = _ := by rw [hws, one_mul]

theorem matrixUnitaryAverage_negPart_trace_le (w : j → ℝ)
    (U : j → unitary (Matrix n n ℂ)) (hw : ∀ i, 0 ≤ w i) (hws : ∑ i, w i = 1)
    {H : Matrix n n ℂ} (hH : H.IsHermitian) :
    (matrixUnitaryAverage w U H)⁻.trace.re ≤ H⁻.trace.re := by
  have ha := matrixUnitaryAverage_trace_abs_le w U hw hws hH
  have ht := congrArg Complex.re (matrixUnitaryAverage_trace w U hws H)
  have hn := negPart_trace_from_abs (matrixUnitaryAverage_isHermitian w U hH)
  have hHn := negPart_trace_from_abs hH
  linarith

end QuantumProver.PPTSupport.SupportBounds

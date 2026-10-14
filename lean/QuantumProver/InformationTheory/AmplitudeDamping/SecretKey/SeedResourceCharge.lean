import QuantumProver.InformationTheory.AmplitudeDamping.SecretKey.PurificationBounds
import QuantumProver.InformationTheory.AmplitudeDamping.SecretKey.ScalarBounds
import QuantumProver.LinearAlgebra.MatrixTracePower.Order

set_option autoImplicit false

noncomputable section

open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix Kronecker

namespace QuantumProver.AmplitudeDamping.SecretKey.SeedResource

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem rankOne_square (v : I → ℂ) :
    let P := Matrix.vecMulVec v (star v)
    P * P = P.trace • P := by
  dsimp
  rw [Matrix.vecMulVec_mul_vecMulVec, Matrix.trace_vecMulVec,
    dotProduct_comm (star v) v, Matrix.vecMulVec_smul]

theorem rpow_projection {P : Matrix I I ℂ} (hP : P.PosSemidef)
    (hid : IsIdempotentElem P) {α : ℝ} (hα : 0 < α) :
    CFC.rpow P α = P := by
  have hpow : CFC.rpow P α = cfc (fun x : ℝ => x ^ α) P :=
    CFC.rpow_eq_cfc_real (A := Matrix I I ℂ) (a := P) (y := α) hP.nonneg
  rw [hpow]
  calc
    cfc (fun x : ℝ => x ^ α) P = cfc (fun x : ℝ => x) P := by
      apply cfc_congr
      intro x hx
      have hx' := (isIdempotentElem_iff_spectrum_subset ℝ P hP.1).mp hid hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx'
      rcases hx' with rfl | rfl
      · exact Real.zero_rpow hα.ne'
      · exact Real.one_rpow α
    _ = P := cfc_id ℝ P

theorem trace_rpow_rankOne (v : I → ℂ) {α : ℝ} (hα : 1 ≤ α)
    (ht : 0 < (Matrix.vecMulVec v (star v)).trace.re) :
    (CFC.rpow (Matrix.vecMulVec v (star v)) α).trace.re =
      (Matrix.vecMulVec v (star v)).trace.re ^ α := by
  let P := Matrix.vecMulVec v (star v)
  let c := P.trace.re
  have hP : P.PosSemidef := Matrix.posSemidef_vecMulVec_self_star v
  have hc : 0 < c := ht
  have htrace : P.trace = (c : ℂ) := by
    apply Complex.ext
    · rfl
    · exact (Complex.nonneg_iff.mp hP.trace_nonneg).2.symm
  have hsq : P * P = c • P := by
    rw [rankOne_square, htrace]
    rfl
  let R := c⁻¹ • P
  have hR : R.PosSemidef := hP.smul (inv_nonneg.mpr hc.le)
  have hid : IsIdempotentElem R := by
    change (c⁻¹ • P) * (c⁻¹ • P) = c⁻¹ • P
    rw [Matrix.smul_mul, Matrix.mul_smul, hsq, smul_smul, smul_smul]
    congr 1
    field_simp
  have hscale : P = c • R := by
    simp [R, smul_smul, hc.ne']
  have hRt : R.trace.re = 1 := by
    change (c⁻¹ • P).trace.re = 1
    simpa only [Matrix.trace_smul, Complex.real_smul, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] using
      (inv_mul_cancel₀ hc.ne' : c⁻¹ * c = 1)
  calc
    (CFC.rpow P α).trace.re = c ^ α * (CFC.rpow R α).trace.re := by
      conv_lhs => rw [hscale]
      exact QuantumProver.MatrixTracePower.trace_rpow_smul_nonneg hR hc.le hα
    _ = c ^ α := by
      rw [rpow_projection hR hid (lt_of_lt_of_le zero_lt_one hα), hRt, mul_one]

end QuantumProver.AmplitudeDamping.SecretKey.SeedResource

namespace QuantumProver.AmplitudeDamping.SecretKey.ProbabilityLaw

variable {J : Type*} [Fintype J] [DecidableEq J]

def seedPowerSum (a : ProbabilityLaw J) (z : ℝ) : ℝ :=
  ∑ j, a.weight j ^ (1 / (1 + z))

theorem seedPowerSum_pos (a : ProbabilityLaw J) (z : ℝ) :
    0 < a.seedPowerSum z :=
  Scalar.probability_power_sum_pos a.weight a.nonnegative a.normalized _

def optimizedSeedLaw (a : ProbabilityLaw J) (z : ℝ) : ProbabilityLaw J where
  weight := Scalar.normalizedFlags (fun j => a.weight j ^ (1 / (1 + z)))
  nonnegative := Scalar.normalizedFlags_nonneg _
    (fun j => Real.rpow_nonneg (a.nonnegative j) _) (a.seedPowerSum_pos z)
  normalized := Scalar.normalizedFlags_sum _ (a.seedPowerSum_pos z)

theorem optimizedSeedLaw_weight (a : ProbabilityLaw J) (z : ℝ) (j : J) :
    (a.optimizedSeedLaw z).weight j =
      a.weight j ^ (1 / (1 + z)) / a.seedPowerSum z := rfl

theorem optimizedSeedLaw_support (a : ProbabilityLaw J) {z : ℝ} (hz : 0 < z)
    (j : J) (hzero : (a.optimizedSeedLaw z).weight j = 0) :
    a.weight j = 0 := by
  have hp := Scalar.normalizedFlags_support
    (fun j => a.weight j ^ (1 / (1 + z))) (a.seedPowerSum_pos z) j hzero
  by_contra hne
  have hpos : 0 < a.weight j := lt_of_le_of_ne (a.nonnegative j) (Ne.symm hne)
  exact (Real.rpow_pos_of_pos hpos _).ne' hp

theorem optimizedSeedLaw_zero (a : ProbabilityLaw J) {z : ℝ} (hz : 0 < z)
    (j : J) (hzero : a.weight j = 0) :
    (a.optimizedSeedLaw z).weight j = 0 := by
  rw [optimizedSeedLaw_weight, hzero,
    Real.zero_rpow (one_div_pos.mpr (by linarith : 0 < 1 + z)).ne', zero_div]

theorem optimizedSeedLaw_cost (a : ProbabilityLaw J) {z : ℝ} (hz : 0 < z) :
    (∑ j, a.weight j * (a.optimizedSeedLaw z).weight j ^ (-z)) =
      a.seedPowerSum z ^ (1 + z) := by
  let β : ℝ := 1 / (1 + z)
  have hβ : 0 < β := one_div_pos.mpr (by linarith)
  have hZ := a.seedPowerSum_pos z
  have hpoint (j : J) :
      a.weight j * (a.optimizedSeedLaw z).weight j ^ (-z) =
        a.weight j ^ β * a.seedPowerSum z ^ z := by
    rw [optimizedSeedLaw_weight]
    by_cases ha0 : a.weight j = 0
    · simp [ha0, Real.zero_rpow hβ.ne']
    have ha : 0 < a.weight j := lt_of_le_of_ne (a.nonnegative j) (Ne.symm ha0)
    rw [Real.div_rpow (Real.rpow_nonneg ha.le _) hZ.le,
      Real.rpow_neg hZ.le, div_inv_eq_mul, ← Real.rpow_mul ha.le]
    have hexp : 1 + β * (-z) = β := by
      dsimp [β]
      field_simp
      ring
    have hpow : a.weight j * a.weight j ^ (β * (-z)) = a.weight j ^ β := by
      calc
        a.weight j * a.weight j ^ (β * (-z)) =
            a.weight j ^ (1 : ℝ) * a.weight j ^ (β * (-z)) := by
          rw [Real.rpow_one]
        _ = a.weight j ^ (1 + β * (-z)) := (Real.rpow_add ha _ _).symm
        _ = a.weight j ^ β := by rw [hexp]
    change a.weight j * (a.weight j ^ (β * (-z)) * a.seedPowerSum z ^ z) = _
    rw [← mul_assoc, hpow]
  calc
    (∑ j, a.weight j * (a.optimizedSeedLaw z).weight j ^ (-z)) =
        ∑ j, a.weight j ^ β * a.seedPowerSum z ^ z :=
      Finset.sum_congr rfl (fun j _ => hpoint j)
    _ = a.seedPowerSum z * a.seedPowerSum z ^ z := by
      rw [← Finset.sum_mul]
      rfl
    _ = a.seedPowerSum z ^ (1 + z) := by
      rw [Real.rpow_add hZ, Real.rpow_one]

end QuantumProver.AmplitudeDamping.SecretKey.ProbabilityLaw

namespace QuantumProver.AmplitudeDamping.SecretKey.SeedResource

variable {J : Type*} [Fintype J] [DecidableEq J]

theorem copiedMatrix_rpow (b : ProbabilityLaw J) {t : ℝ} (ht : t ≠ 0) :
    CFC.rpow b.copiedMatrix t =
      Matrix.diagonal (fun x : J × J =>
        if x.1 = x.2 then ((b.weight x.1 ^ t : ℝ) : ℂ) else 0) := by
  have heq : b.copiedMatrix = Matrix.diagonal
      (fun x : J × J => ((if x.1 = x.2 then b.weight x.1 else 0 : ℝ) : ℂ)) := by
    ext x y
    simp only [ProbabilityLaw.copiedMatrix, Matrix.diagonal_apply]
    split_ifs <;> rfl
  have hpow : CFC.rpow b.copiedMatrix t =
      cfc (fun u : ℝ => u ^ t) b.copiedMatrix :=
    CFC.rpow_eq_cfc_real (A := Matrix (J × J) (J × J) ℂ)
      (a := b.copiedMatrix) (y := t) b.copiedMatrix_posSemidef.nonneg
  rw [hpow, heq, QuantumProver.AmplitudeDamping.TensorPower.cfc_diagonal_real]
  congr 1
  funext x
  split_ifs <;> simp [Real.zero_rpow ht]

def weightedSeedVector (a b : ProbabilityLaw J) (z : ℝ) : J × J → ℂ :=
  fun x => if x.1 = x.2 then
    ((b.weight x.1 ^ (-z / 2) * Real.sqrt (a.weight x.1) : ℝ) : ℂ) else 0

theorem diagonal_seed_mulVec (a b : ProbabilityLaw J) (z : ℝ) :
    (Matrix.diagonal (fun x : J × J =>
      if x.1 = x.2 then ((b.weight x.1 ^ (-z / 2) : ℝ) : ℂ) else 0)) *ᵥ
        a.coherentSeedVector = weightedSeedVector a b z := by
  funext x
  simp only [Matrix.mulVec_diagonal, ProbabilityLaw.coherentSeedVector,
    weightedSeedVector]
  split_ifs <;> simp [Complex.ofReal_mul]

theorem hermitian_rankOne_sandwich {I : Type*} [Fintype I] [DecidableEq I]
    (W : Matrix I I ℂ) (hW : W.IsHermitian) (v : I → ℂ) :
    W * Matrix.vecMulVec v (star v) * W =
      Matrix.vecMulVec (W *ᵥ v) (star (W *ᵥ v)) := by
  rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.star_mulVec, hW]

theorem seed_sandwich (a b : ProbabilityLaw J) {z : ℝ} (hz : 0 < z) (hz1 : z < 1) :
    let α := 1 / (1 - z)
    let W := CFC.rpow b.copiedMatrix ((1 - α) / (2 * α))
    W * a.coherentSeedMatrix * W =
      Matrix.vecMulVec (weightedSeedVector a b z) (star (weightedSeedVector a b z)) := by
  dsimp only
  have hαz : (1 - 1 / (1 - z)) / (2 * (1 / (1 - z))) = -z / 2 := by
    field_simp [(sub_pos.mpr hz1).ne']
    ring
  rw [hαz, copiedMatrix_rpow b (by linarith : -z / 2 ≠ 0)]
  let W : Matrix (J × J) (J × J) ℂ := Matrix.diagonal (fun x : J × J =>
    if x.1 = x.2 then ((b.weight x.1 ^ (-z / 2) : ℝ) : ℂ) else 0)
  have hW : W.IsHermitian := by
    simp only [W, Matrix.IsHermitian, Matrix.diagonal_conjTranspose]
    congr 1
    funext x
    by_cases hx : x.1 = x.2 <;> simp [hx]
  rw [ProbabilityLaw.coherentSeedMatrix, hermitian_rankOne_sandwich W hW,
    diagonal_seed_mulVec]

theorem weightedSeedVector_trace (a b : ProbabilityLaw J) (z : ℝ) :
    (Matrix.vecMulVec (weightedSeedVector a b z)
      (star (weightedSeedVector a b z))).trace.re =
        ∑ j, a.weight j * b.weight j ^ (-z) := by
  have hpoint (j : J) :
      (b.weight j ^ (-z / 2) * Real.sqrt (a.weight j)) ^ (2 : ℕ) =
        a.weight j * b.weight j ^ (-z) := by
    rw [mul_pow, Real.sq_sqrt (a.nonnegative j), ← Real.rpow_natCast,
      ← Real.rpow_mul (b.nonnegative j)]
    norm_num only [Nat.cast_ofNat]
    have hexp : (-z / 2) * (2 : ℝ) = -z := by ring
    rw [hexp, mul_comm]
  have hdiag (x : J × J) :
      (Matrix.vecMulVec (weightedSeedVector a b z)
        (star (weightedSeedVector a b z))) x x =
          if x.1 = x.2 then ((a.weight x.1 * b.weight x.1 ^ (-z) : ℝ) : ℂ) else 0 := by
    by_cases hx : x.1 = x.2
    · simp only [Matrix.vecMulVec_apply, Pi.star_apply, weightedSeedVector,
        if_pos hx, Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul]
      congr 1
      simpa only [pow_two] using hpoint x.1
    · simp [Matrix.vecMulVec_apply, weightedSeedVector, hx]
  have htrace :
      (Matrix.vecMulVec (weightedSeedVector a b z)
        (star (weightedSeedVector a b z))).trace =
          ((∑ j, a.weight j * b.weight j ^ (-z) : ℝ) : ℂ) := by
    simp only [Matrix.trace, Matrix.diag, hdiag, Fintype.sum_prod_type]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    exact (map_sum Complex.ofRealHom _ _).symm
  rw [htrace, Complex.ofReal_re]

theorem seed_support (a b : ProbabilityLaw J)
    (hs : ∀ j, b.weight j = 0 → a.weight j = 0) :
    QuantumProver.AmplitudeDamping.FiniteModel.SupportLE a.coherentSeedMatrix b.copiedMatrix := by
  apply QuantumProver.AmplitudeDamping.FiniteModel.supportLE_of_eq_mul
    (F := Matrix.diagonal (fun x : J × J =>
      if x.1 = x.2 then ((b.weight x.1)⁻¹ : ℂ) else 0) * a.coherentSeedMatrix)
  rw [← Matrix.mul_assoc]
  ext x y
  simp only [ProbabilityLaw.copiedMatrix, Matrix.diagonal_mul_diagonal,
    Matrix.diagonal_mul, ProbabilityLaw.coherentSeedMatrix,
    Matrix.vecMulVec_apply, ProbabilityLaw.coherentSeedVector, Pi.star_apply]
  by_cases hx : x.1 = x.2
  · by_cases hb : b.weight x.1 = 0
    · have ha := hs x.1 hb
      simp [← hx, hb, ha]
    · simp [← hx, hb]
  · simp [hx]

end QuantumProver.AmplitudeDamping.SecretKey.SeedResource

namespace QuantumProver.AmplitudeDamping.SecretKey.ProbabilityLaw

variable {J : Type*} [Fintype J] [DecidableEq J]

theorem seed_cost_pos (a b : ProbabilityLaw J)
    (hs : ∀ j, b.weight j = 0 → a.weight j = 0) (z : ℝ) :
    0 < ∑ j, a.weight j * b.weight j ^ (-z) := by
  have hex : ∃ j, 0 < a.weight j := by
    by_contra! hn
    have h : (∑ j, a.weight j) ≤ 0 := Finset.sum_nonpos (fun j _ => hn j)
    rw [a.normalized] at h
    linarith
  obtain ⟨j, hj⟩ := hex
  have hb : 0 < b.weight j := by
    by_contra! h
    have hb0 : b.weight j = 0 := le_antisymm h (b.nonnegative j)
    exact hj.ne' (hs j hb0)
  have hsingle : a.weight j * b.weight j ^ (-z) ≤
      ∑ i, a.weight i * b.weight i ^ (-z) :=
    Finset.single_le_sum (fun i _ => mul_nonneg (a.nonnegative i)
      (Real.rpow_nonneg (b.nonnegative i) _)) (Finset.mem_univ j)
  exact lt_of_lt_of_le (mul_pos hj (Real.rpow_pos_of_pos hb _)) hsingle

theorem coherentSeed_sandwichedTrace (a b : ProbabilityLaw J)
    {z : ℝ} (hz : 0 < z) (hz1 : z < 1)
    (hs : ∀ j, b.weight j = 0 → a.weight j = 0) :
    QuantumProver.AmplitudeDamping.FiniteModel.sandwichedTrace (1 / (1 - z))
      a.coherentSeedMatrix b.copiedMatrix =
        (∑ j, a.weight j * b.weight j ^ (-z)) ^ (1 / (1 - z)) := by
  have hα : 1 ≤ 1 / (1 - z) :=
    (le_div_iff₀ (sub_pos.mpr hz1)).mpr (by linarith)
  have ht : 0 < (Matrix.vecMulVec (SeedResource.weightedSeedVector a b z)
      (star (SeedResource.weightedSeedVector a b z))).trace.re := by
    rw [SeedResource.weightedSeedVector_trace]
    exact a.seed_cost_pos b hs z
  unfold QuantumProver.AmplitudeDamping.FiniteModel.sandwichedTrace
  dsimp only
  rw [SeedResource.seed_sandwich a b hz hz1,
    SeedResource.trace_rpow_rankOne _ hα ht, SeedResource.weightedSeedVector_trace]

theorem coherentSeed_sandwichedDivergence (a b : ProbabilityLaw J)
    {z : ℝ} (hz : 0 < z) (hz1 : z < 1)
    (hs : ∀ j, b.weight j = 0 → a.weight j = 0) :
    QuantumProver.AmplitudeDamping.FiniteModel.sandwichedDivergence (1 / (1 - z))
      a.coherentSeedMatrix b.copiedMatrix =
        ((log2 (∑ j, a.weight j * b.weight j ^ (-z)) / z : ℝ) : EReal) := by
  have hsup := SeedResource.seed_support a b hs
  simp only [QuantumProver.AmplitudeDamping.FiniteModel.sandwichedDivergence, if_pos hsup]
  rw [a.coherentSeed_sandwichedTrace b hz hz1 hs,
    Real.log_rpow (a.seed_cost_pos b hs z)]
  congr 1
  unfold log2
  have h2 : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  field_simp [hz.ne', (sub_pos.mpr hz1).ne', h2]
  ring

theorem coherentSeed_optimized_divergence (a : ProbabilityLaw J)
    {z : ℝ} (hz : 0 < z) (hz1 : z < 1) :
    QuantumProver.AmplitudeDamping.FiniteModel.sandwichedDivergence (1 / (1 - z))
      a.coherentSeedMatrix (a.optimizedSeedLaw z).copiedMatrix =
        (a.renyiSeedCharge z : EReal) := by
  rw [a.coherentSeed_sandwichedDivergence _ hz hz1
    (fun j => a.optimizedSeedLaw_support hz j), a.optimizedSeedLaw_cost hz]
  congr 1
  unfold renyiSeedCharge log2
  rw [Real.log_rpow (a.seedPowerSum_pos z)]
  dsimp only [seedPowerSum]
  ring

theorem optimizedSeedComparison_separable (a : ProbabilityLaw J) (z : ℝ) :
    IsSeparable (a.optimizedSeedLaw z).copiedDensity :=
  (a.optimizedSeedLaw z).copiedDensity_separable_B

theorem copiedMatrix_quantum_separable {d : ℕ} (b : ProbabilityLaw (Fin d)) :
    QuantumProver.AmplitudeDamping.FiniteModel.IsSeparable d d b.copiedMatrix := by
  let P (j : Fin d) : Matrix (Fin d) (Fin d) ℂ :=
    Matrix.diagonal (fun i => if i = j then 1 else 0)
  have hp (j : Fin d) : QuantumProver.AmplitudeDamping.FiniteModel.IsDensity (P j) := by
    constructor
    · apply Matrix.PosSemidef.diagonal
      intro i
      dsimp
      split_ifs <;> norm_num
    · simp [P, Matrix.trace_diagonal]
  refine ⟨d, b.weight, P, P, b.nonnegative, b.normalized,
    (fun j => ⟨hp j, hp j⟩), ?_⟩
  ext x y
  simp only [copiedMatrix, P, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul, Matrix.kroneckerMap_apply, Matrix.diagonal_apply]
  rw [Finset.sum_eq_single x.1]
  · by_cases hxy : x = y
    · subst y
      by_cases hx : x.1 = x.2 <;> simp [hx, eq_comm]
    · have hn : ¬(x.1 = y.1 ∧ x.2 = y.2) := by
        intro h
        exact hxy (Prod.ext h.1 h.2)
      by_cases h₁ : x.1 = y.1 <;> by_cases h₂ : x.2 = y.2 <;>
        simp_all
  · intro j _ hj
    simp [Ne.symm hj]
  · simp

theorem coherentSeed_entanglement_le {d : ℕ} (a : ProbabilityLaw (Fin d))
    {z : ℝ} (hz : 0 < z) (hz1 : z < 1) :
    QuantumProver.AmplitudeDamping.FiniteModel.sandwichedEntanglement (1 / (1 - z)) d d
      a.coherentSeedMatrix ≤ (a.renyiSeedCharge z : EReal) := by
  rw [← a.coherentSeed_optimized_divergence hz hz1]
  apply sInf_le
  refine ⟨(a.optimizedSeedLaw z).copiedMatrix, ?_, rfl⟩
  exact ⟨⟨(a.optimizedSeedLaw z).copiedMatrix_posSemidef,
    (a.optimizedSeedLaw z).copiedMatrix_trace⟩,
    (a.optimizedSeedLaw z).copiedMatrix_quantum_separable⟩

end QuantumProver.AmplitudeDamping.SecretKey.ProbabilityLaw

namespace QuantumProver.AmplitudeDamping.SecretKey.SeedResource

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem sandwichedTrace_self (ρ : Density I) {z : ℝ} (hz : 0 < z) (hz1 : z < 1) :
    QuantumProver.AmplitudeDamping.FiniteModel.sandwichedTrace (1 / (1 - z)) ρ.mat ρ.mat = 1 := by
  let α : ℝ := 1 / (1 - z)
  let t : ℝ := -z / 2
  let f : ℝ → ℝ := fun x => x ^ t
  let g : ℝ → ℝ := fun x => f x * x * f x
  let W := CFC.rpow ρ.mat t
  have hα : 0 < α := one_div_pos.mpr (sub_pos.mpr hz1)
  have hExp : (1 - α) / (2 * α) = t := by
    dsimp [α, t]
    field_simp [(sub_pos.mpr hz1).ne']
    ring
  have hW : W = cfc f ρ.mat :=
    CFC.rpow_eq_cfc_real (A := Matrix I I ℂ) (a := ρ.mat) (y := t) ρ.positive.nonneg
  have hf : ContinuousOn f (spectrum ℝ ρ.mat) := ρ.mat.finite_real_spectrum.continuousOn _
  have hg : ContinuousOn g (spectrum ℝ ρ.mat) := ρ.mat.finite_real_spectrum.continuousOn _
  have hself : IsSelfAdjoint ρ.mat := ρ.positive.1
  have hsand : W * ρ.mat * W = cfc g ρ.mat := by
    calc
      W * ρ.mat * W = cfc f ρ.mat * cfc (fun x : ℝ => x) ρ.mat * cfc f ρ.mat := by
        rw [hW, cfc_id' ℝ ρ.mat hself]
      _ = cfc g ρ.mat := by
        rw [← cfc_mul f (fun x : ℝ => x) ρ.mat hf continuous_id.continuousOn,
          ← cfc_mul (fun x : ℝ => f x * x) f ρ.mat
            (ρ.mat.finite_real_spectrum.continuousOn _) hf]
  have hSandPSD : (W * ρ.mat * W).PosSemidef := by
    have hWs : Wᴴ = W := (Matrix.nonneg_iff_posSemidef.mp
      (CFC.rpow_nonneg (a := ρ.mat) (y := t))).1
    simpa only [hWs] using ρ.positive.mul_mul_conjTranspose_same W
  have hpower : CFC.rpow (W * ρ.mat * W) α = ρ.mat := by
    have hpow : CFC.rpow (W * ρ.mat * W) α =
        cfc (fun x : ℝ => x ^ α) (W * ρ.mat * W) :=
      CFC.rpow_eq_cfc_real (A := Matrix I I ℂ)
        (a := W * ρ.mat * W) (y := α) hSandPSD.nonneg
    rw [hpow, hsand]
    have hcomp : cfc (fun x : ℝ => x ^ α) (cfc g ρ.mat) =
        cfc ((fun x : ℝ => x ^ α) ∘ g) ρ.mat :=
      (cfc_comp (fun x : ℝ => x ^ α) g ρ.mat hself
        (Real.continuous_rpow_const hα.le).continuousOn hg).symm
    rw [hcomp]
    calc
      cfc ((fun x : ℝ => x ^ α) ∘ g) ρ.mat = cfc (fun x : ℝ => x) ρ.mat := by
        apply cfc_congr
        intro x hx
        have hx0 : 0 ≤ x := spectrum_nonneg_of_nonneg ρ.positive.nonneg hx
        change (x ^ t * x * x ^ t) ^ α = x
        by_cases hxZ : x = 0
        · subst x
          simp [Real.zero_rpow hα.ne']
        have hxP : 0 < x := lt_of_le_of_ne hx0 (Ne.symm hxZ)
        have hlin : t + 1 + t = 1 - z := by dsimp [t]; ring
        have hinv : (1 - z) * α = 1 := by
          dsimp [α]
          field_simp [(sub_pos.mpr hz1).ne']
        calc
          (x ^ t * x * x ^ t) ^ α = (x ^ (t + 1 + t)) ^ α := by
            congr 1
            rw [Real.rpow_add hxP, Real.rpow_add hxP, Real.rpow_one]
          _ = x := by
            rw [hlin, ← Real.rpow_mul hx0, hinv, Real.rpow_one]
      _ = ρ.mat := cfc_id ℝ ρ.mat
  change (CFC.rpow (CFC.rpow ρ.mat ((1 - α) / (2 * α)) * ρ.mat *
    CFC.rpow ρ.mat ((1 - α) / (2 * α))) α).trace.re = 1
  rw [hExp, hpower, ρ.normalized]
  rfl

theorem coherentSeed_optimized_divergence_independent_Eve
    {J E : Type*} [Fintype J] [Fintype E] [DecidableEq J] [DecidableEq E]
    (a : ProbabilityLaw J) (ξ : Density E) {z : ℝ} (hz : 0 < z) (hz1 : z < 1) :
    QuantumProver.AmplitudeDamping.FiniteModel.sandwichedDivergence (1 / (1 - z))
      (a.coherentSeedDensity.tensor ξ).mat
      ((a.optimizedSeedLaw z).copiedDensity.tensor ξ).mat =
        (a.renyiSeedCharge z : EReal) := by
  have hs := seed_support a (a.optimizedSeedLaw z)
    (fun j => a.optimizedSeedLaw_support hz j)
  have hξs : QuantumProver.AmplitudeDamping.FiniteModel.SupportLE ξ.mat ξ.mat := le_refl _
  have ht := hs.kronecker hξs
  have hQ := QuantumProver.AmplitudeDamping.TensorPower.sandwichedTrace_kronecker
    a.coherentSeedMatrix_posSemidef (a.optimizedSeedLaw z).copiedMatrix_posSemidef
    ξ.positive ξ.positive (1 / (1 - z))
  rw [sandwichedTrace_self ξ hz hz1, mul_one] at hQ
  change QuantumProver.AmplitudeDamping.FiniteModel.sandwichedDivergence (1 / (1 - z))
    (a.coherentSeedMatrix ⊗ₖ ξ.mat) ((a.optimizedSeedLaw z).copiedMatrix ⊗ₖ ξ.mat) = _
  calc
    _ = QuantumProver.AmplitudeDamping.FiniteModel.sandwichedDivergence (1 / (1 - z))
        a.coherentSeedMatrix (a.optimizedSeedLaw z).copiedMatrix := by
      simp only [QuantumProver.AmplitudeDamping.FiniteModel.sandwichedDivergence, if_pos ht,
        if_pos hs, hQ]
    _ = (a.renyiSeedCharge z : EReal) := a.coherentSeed_optimized_divergence hz hz1

end QuantumProver.AmplitudeDamping.SecretKey.SeedResource

namespace QuantumProver.AmplitudeDamping.SecretKey.ProbabilityLaw

variable {J K : Type*} [Fintype J] [Fintype K] [DecidableEq J] [DecidableEq K]

def seedRelabelLaw (a : ProbabilityLaw J) (e : K ≃ J) : ProbabilityLaw K where
  weight k := a.weight (e k)
  nonnegative k := a.nonnegative (e k)
  normalized := by
    calc
      (∑ k, a.weight (e k)) = ∑ j, a.weight j := e.sum_comp a.weight
      _ = 1 := a.normalized

theorem seedRelabelLaw_copiedMatrix (a : ProbabilityLaw J) (e : K ≃ J) :
    (a.seedRelabelLaw e).copiedMatrix =
      a.copiedMatrix.submatrix (e.prodCongr e) (e.prodCongr e) := by
  ext x y
  simp only [copiedMatrix, Matrix.diagonal_apply, Matrix.submatrix_apply,
    Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd, seedRelabelLaw]
  have hmap : Prod.map (⇑e) (⇑e) x = Prod.map (⇑e) (⇑e) y ↔ x = y :=
    (e.prodCongr e).injective.eq_iff
  simp only [e.injective.eq_iff, hmap]

theorem seedRelabelLaw_coherentSeedMatrix (a : ProbabilityLaw J) (e : K ≃ J) :
    (a.seedRelabelLaw e).coherentSeedMatrix =
      a.coherentSeedMatrix.submatrix (e.prodCongr e) (e.prodCongr e) := by
  ext x y
  simp only [coherentSeedMatrix, Matrix.vecMulVec_apply, Pi.star_apply,
    Matrix.submatrix_apply, coherentSeedVector, Equiv.prodCongr_apply,
    Prod.map_fst, Prod.map_snd, seedRelabelLaw, e.injective.eq_iff]

theorem seedRelabelLaw_renyiSeedCharge (a : ProbabilityLaw J) (e : K ≃ J) (z : ℝ) :
    (a.seedRelabelLaw e).renyiSeedCharge z = a.renyiSeedCharge z := by
  unfold renyiSeedCharge
  congr 2
  exact e.sum_comp (fun j => a.weight j ^ (1 / (1 + z)))

theorem coherentSeed_entanglement_le_after_local_relabel
    {d : ℕ} (a : ProbabilityLaw J) (e : Fin d ≃ J)
    {z : ℝ} (hz : 0 < z) (hz1 : z < 1) :
    QuantumProver.AmplitudeDamping.FiniteModel.sandwichedEntanglement (1 / (1 - z)) d d
      (a.coherentSeedMatrix.submatrix (e.prodCongr e) (e.prodCongr e)) ≤
        (a.renyiSeedCharge z : EReal) := by
  rw [← seedRelabelLaw_coherentSeedMatrix a e,
    ← seedRelabelLaw_renyiSeedCharge a e z]
  exact (a.seedRelabelLaw e).coherentSeed_entanglement_le hz hz1

theorem coherentSeed_entanglement_le_bits_after_local_relabel
    [Nonempty J] {d : ℕ} (a : ProbabilityLaw J) (e : Fin d ≃ J)
    {z k : ℝ} (hz : 0 < z) (hz1 : z < 1)
    (hk : (Fintype.card J : ℝ) ≤ 2 ^ k) :
    QuantumProver.AmplitudeDamping.FiniteModel.sandwichedEntanglement (1 / (1 - z)) d d
      (a.coherentSeedMatrix.submatrix (e.prodCongr e) (e.prodCongr e)) ≤ (k : EReal) := by
  apply (a.coherentSeed_entanglement_le_after_local_relabel e hz hz1).trans
  exact_mod_cast a.renyiSeedCharge_le_bits z k hz hk

end QuantumProver.AmplitudeDamping.SecretKey.ProbabilityLaw

namespace QuantumProver.AmplitudeDamping.SecretKey.SeedResource

variable {I E : Type*} [Fintype I] [Fintype E] [DecidableEq I] [DecidableEq E]

theorem sandwichedDivergence_self (ρ : Density I)
    {z : ℝ} (hz : 0 < z) (hz1 : z < 1) :
    QuantumProver.AmplitudeDamping.FiniteModel.sandwichedDivergence (1 / (1 - z))
      ρ.mat ρ.mat = 0 := by
  have hs : QuantumProver.AmplitudeDamping.FiniteModel.SupportLE ρ.mat ρ.mat := le_refl _
  simp only [QuantumProver.AmplitudeDamping.FiniteModel.sandwichedDivergence, if_pos hs]
  rw [sandwichedTrace_self ρ hz hz1]
  norm_num

theorem honest_marginal_tensor_independent_Eve (ρ : Density I) (ξ : Density E) :
    partialTraceRight (ρ.tensor ξ).mat = ρ.mat := by
  ext i j
  change (∑ e, ρ.mat i j * ξ.mat e e) = ρ.mat i j
  rw [← Finset.mul_sum]
  change ρ.mat i j * ξ.mat.trace = ρ.mat i j
  rw [ξ.normalized, mul_one]

end QuantumProver.AmplitudeDamping.SecretKey.SeedResource

namespace QuantumProver.AmplitudeDamping.SecretKey.ProbabilityLaw

open QuantumProver.AmplitudeDamping.FiniteModel

theorem coherentSeed_entanglement_le_with_local_ancillas
    {d c e : ℕ} (a : ProbabilityLaw (Fin d))
    (ρA : Density (Fin c)) (ρB : Density (Fin e))
    {z : ℝ} (hz : 0 < z) (hz1 : z < 1) :
    sandwichedEntanglement (1 / (1 - z)) (d * c) (d * e)
      (tensorOnLabCut a.coherentSeedMatrix (ρA.tensor ρB).mat) ≤
        (a.renyiSeedCharge z : EReal) := by
  let b := a.optimizedSeedLaw z
  let ν := ρA.tensor ρB
  have hρ : IsDensity a.coherentSeedMatrix :=
    ⟨a.coherentSeedMatrix_posSemidef, a.coherentSeedMatrix_trace⟩
  have hσ : IsDensity b.copiedMatrix := ⟨b.copiedMatrix_posSemidef, b.copiedMatrix_trace⟩
  have hν : IsDensity ν.mat := ⟨ν.positive, ν.normalized⟩
  have hνsep : QuantumProver.AmplitudeDamping.FiniteModel.IsSeparable c e ν.mat := by
    refine ⟨1, (fun _ => 1), (fun _ => ρA.mat), (fun _ => ρB.mat),
      (fun _ => zero_le_one), by simp,
      (fun _ => ⟨⟨ρA.positive, ρA.normalized⟩, ⟨ρB.positive, ρB.normalized⟩⟩), ?_⟩
    simp [ν, Density.tensor]
  have hsup := SeedResource.seed_support a b (fun j => a.optimizedSeedLaw_support hz j)
  have hνsup : SupportLE ν.mat ν.mat := le_refl _
  have hQ : 0 < sandwichedTrace (1 / (1 - z)) a.coherentSeedMatrix b.copiedMatrix := by
    rw [a.coherentSeed_sandwichedTrace b hz hz1
      (fun j => a.optimizedSeedLaw_support hz j)]
    exact Real.rpow_pos_of_pos (a.seed_cost_pos b
      (fun j => a.optimizedSeedLaw_support hz j) z) _
  have hQν : 0 < sandwichedTrace (1 / (1 - z)) ν.mat ν.mat := by
    rw [SeedResource.sandwichedTrace_self ν hz hz1]
    norm_num
  have hD : sandwichedDivergence (1 / (1 - z))
      (tensorOnLabCut a.coherentSeedMatrix ν.mat) (tensorOnLabCut b.copiedMatrix ν.mat) =
        (a.renyiSeedCharge z : EReal) := by
    rw [QuantumProver.AmplitudeDamping.TensorPower.sandwichedDivergence_tensorOnLabCut_of_support
      hρ hσ hν hν hsup hνsup _ hQ hQν,
      SeedResource.sandwichedDivergence_self ν hz hz1, add_zero]
    exact a.coherentSeed_optimized_divergence hz hz1
  rw [← hD]
  apply sInf_le
  refine ⟨tensorOnLabCut b.copiedMatrix ν.mat, ?_, rfl⟩
  exact ⟨hσ.tensorOnLabCut hν, b.copiedMatrix_quantum_separable.tensorOnLabCut hνsep⟩

end QuantumProver.AmplitudeDamping.SecretKey.ProbabilityLaw

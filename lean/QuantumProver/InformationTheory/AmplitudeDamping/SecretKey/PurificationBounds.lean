import QuantumProver.InformationTheory.AmplitudeDamping.SecretKey.Definitions
import QuantumProver.InformationTheory.AmplitudeDamping.SecretKey.EntropyBounds
import QuantumProver.InformationTheory.AmplitudeDamping.QuantumCapacity.TracePowerBounds

open scoped BigOperators Topology ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace QuantumProver.AmplitudeDamping.SecretKey.Scalar

theorem binomial_term_le_one (n r : ℕ) (hrn : r ≤ n) (x : ℝ)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    (n.choose r : ℝ) * x ^ r * (1 - x) ^ (n - r) ≤ 1 := by
  have hsum : (∑ j ∈ Finset.range (n + 1),
      x ^ j * (1 - x) ^ (n - j) * (n.choose j : ℝ)) = 1 := by
    rw [← add_pow]
    simp
  have hsingle := Finset.single_le_sum
    (s := Finset.range (n + 1))
    (f := fun j ↦ x ^ j * (1 - x) ^ (n - j) * (n.choose j : ℝ))
    (fun j _ ↦ by positivity)
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hrn))
  rw [hsum] at hsingle
  simpa only [mul_comm, mul_left_comm, mul_assoc] using hsingle

theorem log_choose_le_binEntropy (n r : ℕ) (hrn : r ≤ n) :
    Real.log (n.choose r : ℝ) ≤
      (n : ℝ) * Real.binEntropy ((r : ℝ) / (n : ℝ)) := by
  by_cases hr0 : r = 0
  · simp [hr0]
  have hrpos : 0 < r := Nat.pos_of_ne_zero hr0
  have hnpos : 0 < n := lt_of_lt_of_le hrpos hrn
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hnpos
  by_cases hrfull : r = n
  · subst r
    simp [hnR.ne']
  have hrlt : r < n := lt_of_le_of_ne hrn hrfull
  have hrR : 0 < (r : ℝ) := by exact_mod_cast hrpos
  have hrnR : (r : ℝ) < (n : ℝ) := by exact_mod_cast hrlt
  let x : ℝ := (r : ℝ) / (n : ℝ)
  have hx0 : 0 < x := div_pos hrR hnR
  have hx1 : x < 1 := (div_lt_one hnR).mpr hrnR
  have hcomp : 0 < 1 - x := sub_pos.mpr hx1
  have hc : 0 < (n.choose r : ℝ) := by
    exact_mod_cast (Nat.choose_pos hrn)
  have hterm : 0 < (n.choose r : ℝ) * x ^ r * (1 - x) ^ (n - r) := by
    positivity
  have hlog := Real.log_le_log hterm
    (binomial_term_le_one n r hrn x hx0.le hx1.le)
  rw [Real.log_one, Real.log_mul (mul_pos hc (pow_pos hx0 r)).ne'
    (pow_pos hcomp (n - r)).ne',
    Real.log_mul hc.ne' (pow_pos hx0 r).ne',
    Real.log_pow, Real.log_pow] at hlog
  have hnr : (n : ℝ) * x = (r : ℝ) := by
    dsimp [x]
    field_simp [hnR.ne']
  have hnsub : ((n - r : ℕ) : ℝ) = (n : ℝ) - (r : ℝ) :=
    Nat.cast_sub hrn
  have hnc : (n : ℝ) * (1 - x) = ((n - r : ℕ) : ℝ) := by
    rw [hnsub]
    nlinarith [hnr]
  change Real.log (n.choose r : ℝ) ≤ (n : ℝ) * Real.binEntropy x
  have hE : (n : ℝ) * Real.binEntropy x =
      -(r : ℝ) * Real.log x - ((n - r : ℕ) : ℝ) * Real.log (1 - x) := by
    rw [Real.binEntropy, Real.log_inv, Real.log_inv]
    calc
      _ = -((n : ℝ) * x) * Real.log x -
          ((n : ℝ) * (1 - x)) * Real.log (1 - x) := by ring
      _ = _ := by rw [hnr, hnc]
  rw [hE]
  linarith [hlog]

theorem log2_choose_le_binaryEntropyBits (n r : ℕ) (hrn : r ≤ n) :
    QuantumProver.AmplitudeDamping.SecretKey.log2 (n.choose r : ℝ) ≤
      (n : ℝ) * QuantumProver.AmplitudeDamping.SecretKey.binaryEntropyBits ((r : ℝ) / (n : ℝ)) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h := div_le_div_of_nonneg_right
    (log_choose_le_binEntropy n r hrn) hlog2.le
  simpa only [QuantumProver.AmplitudeDamping.SecretKey.log2, QuantumProver.AmplitudeDamping.SecretKey.binaryEntropyBits,
    mul_div_assoc] using h

noncomputable def dampingTypePenaltyNats (v p : ℝ) : ℝ :=
  -Real.binEntropy v - v * Real.log (1 - p) - (1 - v) * Real.log p

noncomputable def dampingTypeObjectiveNats (p z u v : ℝ) : ℝ :=
  Real.binEntropy (u * v) - u * Real.binEntropy v -
    (u / z) * dampingTypePenaltyNats v p

noncomputable def dampingTypeObjectiveBits (p z u v : ℝ) : ℝ :=
  dampingTypeObjectiveNats p z u v / Real.log 2

theorem dampingTypeObjectiveNats_le_closed (p z u v : ℝ)
    (hp0 : 0 < p) (hp1 : p < 1) (hz0 : 0 < z) (hz1 : z < 1)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    dampingTypeObjectiveNats p z u v ≤
      Real.log (1 + ((1 - p) /
        (1 - p ^ (1 / (1 - z))) ^ (1 - z)) ^ (1 / z)) := by
  have hq : 0 < 1 - p := sub_pos.mpr hp1
  have hzcomp : 0 < 1 - z := sub_pos.mpr hz1
  have halpha : 0 < 1 / (1 - z) := div_pos zero_lt_one hzcomp
  have ht0 : 0 < p ^ (1 / (1 - z)) := Real.rpow_pos_of_pos hp0 _
  have ht1 : p ^ (1 / (1 - z)) < 1 := Real.rpow_lt_one hp0.le hp1 halpha
  let V : ℝ := 1 - p ^ (1 / (1 - z))
  have hV0 : 0 < V := sub_pos.mpr ht1
  have hV1 : V < 1 := by dsimp [V]; linarith
  let A : ℝ := ((1 - p) / V ^ (1 - z)) ^ (1 / z)
  have hVpow : 0 < V ^ (1 - z) := Real.rpow_pos_of_pos hV0 _
  have hA : 0 < A := Real.rpow_pos_of_pos (div_pos hq hVpow) _
  have hlogA : Real.log A =
      (Real.log (1 - p) - (1 - z) * Real.log V) / z := by
    dsimp [A]
    rw [Real.log_rpow (div_pos hq hVpow),
      Real.log_div hq.ne' hVpow.ne', Real.log_rpow hV0]
    ring
  have hlogP : Real.log (1 - V) = (1 / (1 - z)) * Real.log p := by
    have hcomp : 1 - V = p ^ (1 / (1 - z)) := by dsimp [V]; ring
    rw [hcomp, Real.log_rpow hp0]
  have hG := mul_nonpos_of_nonneg_of_nonpos hzcomp.le
    (binary_entropy_cross_entropy_le hv0 hv1 hV0 hV1)
  rw [hlogP] at hG
  have hGexpand :
      (1 - z) * (Real.binEntropy v + v * Real.log V +
        (1 - v) * ((1 / (1 - z)) * Real.log p)) =
      (1 - z) * Real.binEntropy v + v * (1 - z) * Real.log V +
        (1 - v) * Real.log p := by
    field_simp [hzcomp.ne'] <;> ring
  rw [hGexpand] at hG
  have hinner : z * (Real.binEntropy v + dampingTypePenaltyNats v p / z +
      v * Real.log A) =
      -((1 - z) * Real.binEntropy v + v * (1 - z) * Real.log V +
        (1 - v) * Real.log p) := by
    rw [hlogA]
    unfold dampingTypePenaltyNats
    field_simp [hz0.ne'] <;> ring
  have hprod : 0 ≤ z * (Real.binEntropy v + dampingTypePenaltyNats v p / z +
      v * Real.log A) := by
    rw [hinner]
    linarith
  have hcombined : 0 ≤ Real.binEntropy v + dampingTypePenaltyNats v p / z +
      v * Real.log A := (mul_nonneg_iff_of_pos_left hz0).mp hprod
  have hmult := mul_nonneg hu0 hcombined
  have hratio : (u / z) * dampingTypePenaltyNats v p =
      u * (dampingTypePenaltyNats v p / z) := by ring
  have hobj : dampingTypeObjectiveNats p z u v ≤
      Real.binEntropy (u * v) + (u * v) * Real.log A := by
    unfold dampingTypeObjectiveNats
    rw [hratio]
    nlinarith [hmult]
  have hx0 : 0 ≤ u * v := mul_nonneg hu0 hv0
  have hx1 : u * v ≤ 1 := by
    calc
      u * v ≤ 1 * v := mul_le_mul_of_nonneg_right hu1 hv0
      _ = v := one_mul v
      _ ≤ 1 := hv1
  have hconj := binary_entropy_conjugate hx0 hx1 hA
  simpa only [A, V] using hobj.trans hconj

theorem dampingTypeObjectiveBits_le_channelBz (p z u v : ℝ)
    (hp0 : 0 < p) (hp1 : p < 1) (hz0 : 0 < z) (hz1 : z < 1)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    dampingTypeObjectiveBits p z u v ≤ QuantumProver.AmplitudeDamping.SecretKey.channelBz p z := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h := div_le_div_of_nonneg_right
    (dampingTypeObjectiveNats_le_closed p z u v hp0 hp1 hz0 hz1 hu0 hu1 hv0 hv1)
    hlog2.le
  simpa only [dampingTypeObjectiveBits, QuantumProver.AmplitudeDamping.SecretKey.channelBz,
    QuantumProver.AmplitudeDamping.SecretKey.log2] using h

theorem channelBz_eq_scalarBudget {p z : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) (hz1 : z < 1) :
    QuantumProver.AmplitudeDamping.SecretKey.channelBz p z =
      QuantumProver.AmplitudeDamping.Scalar.scalarBudget p z := by
  rw [QuantumProver.AmplitudeDamping.Scalar.scalarBudget_eq_closed hp0 hp1 hz1]
  rfl

theorem tendsto_channelBz_zero_right {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    Filter.Tendsto (QuantumProver.AmplitudeDamping.SecretKey.channelBz p) (𝓝[>] (0 : ℝ))
      (𝓝 (QuantumProver.AmplitudeDamping.SecretKey.channelCZ p)) := by
  have hlim := QuantumProver.AmplitudeDamping.Scalar.tendsto_scalarBudget_zero_right hp0 hp1
  have hlt : ∀ᶠ z : ℝ in 𝓝[>] (0 : ℝ), z < 1 :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds (eventually_lt_nhds (by norm_num))
  have heq : QuantumProver.AmplitudeDamping.Scalar.scalarBudget p =ᶠ[𝓝[>] (0 : ℝ)]
      QuantumProver.AmplitudeDamping.SecretKey.channelBz p := by
    filter_upwards [hlt] with z hz
    exact (channelBz_eq_scalarBudget hp0 hp1 hz).symm
  exact hlim.congr' heq

theorem survivor_log_moment_le (n w : ℕ) {p z : ℝ}
    (hn : 0 < n) (hwn : w ≤ n) (hp0 : 0 < p) (hp1 : p < 1)
    (hz0 : 0 < z) (hz1 : z < 1) :
    QuantumProver.AmplitudeDamping.SecretKey.log2 (QuantumProver.AmplitudeDamping.Scalar.survivorMoment n w p z) / z ≤
      (n : ℝ) * QuantumProver.AmplitudeDamping.SecretKey.channelBz p z +
        QuantumProver.AmplitudeDamping.SecretKey.log2 ((n : ℝ) + 1) / z := by
  rw [channelBz_eq_scalarBudget hp0 hp1 hz1]
  exact QuantumProver.AmplitudeDamping.Scalar.log2Moment_div_le n w hn hwn hp0 hp1 hz0 hz1

theorem normalized_type_increment_le (n w : ℕ) {p z : ℝ}
    (hn : 0 < n) (hwn : w ≤ n) (hp0 : 0 < p) (hp1 : p < 1)
    (hz0 : 0 < z) (hz1 : z < 1) :
    QuantumProver.AmplitudeDamping.SecretKey.log2 ((n : ℝ) + 1) / z +
        QuantumProver.AmplitudeDamping.SecretKey.log2 (QuantumProver.AmplitudeDamping.Scalar.survivorMoment n w p z) / z ≤
      (n : ℝ) * QuantumProver.AmplitudeDamping.SecretKey.channelBz p z +
        (2 / z) * QuantumProver.AmplitudeDamping.SecretKey.log2 ((n : ℝ) + 1) := by
  have h := survivor_log_moment_le n w hn hwn hp0 hp1 hz0 hz1
  have hcombine : QuantumProver.AmplitudeDamping.SecretKey.log2 ((n : ℝ) + 1) / z +
      ((n : ℝ) * QuantumProver.AmplitudeDamping.SecretKey.channelBz p z +
        QuantumProver.AmplitudeDamping.SecretKey.log2 ((n : ℝ) + 1) / z) =
      (n : ℝ) * QuantumProver.AmplitudeDamping.SecretKey.channelBz p z +
        (2 / z) * QuantumProver.AmplitudeDamping.SecretKey.log2 ((n : ℝ) + 1) := by ring
  rw [← hcombine]
  linarith

noncomputable def normalizedBlockBudget (n : ℕ) (p z : ℝ) : ℝ :=
  (Finset.range (n + 1)).sup' (by exact ⟨0, by simp⟩)
    (fun w => QuantumProver.AmplitudeDamping.SecretKey.log2 ((n : ℝ) + 1) / z +
      QuantumProver.AmplitudeDamping.SecretKey.log2 (QuantumProver.AmplitudeDamping.Scalar.survivorMoment n w p z) / z)

theorem normalizedBlockBudget_le (n : ℕ) {p z : ℝ}
    (hn : 0 < n) (hp0 : 0 < p) (hp1 : p < 1)
    (hz0 : 0 < z) (hz1 : z < 1) :
    normalizedBlockBudget n p z ≤ (n : ℝ) * QuantumProver.AmplitudeDamping.SecretKey.channelBz p z +
      (2 / z) * QuantumProver.AmplitudeDamping.SecretKey.log2 ((n : ℝ) + 1) := by
  unfold normalizedBlockBudget
  apply Finset.sup'_le
  intro w hw
  exact normalized_type_increment_le n w hn
    (Nat.le_of_lt_succ (Finset.mem_range.mp hw)) hp0 hp1 hz0 hz1

theorem normalizedBlockBudget_per_use_le (n : ℕ) {p z : ℝ}
    (hn : 0 < n) (hp0 : 0 < p) (hp1 : p < 1)
    (hz0 : 0 < z) (hz1 : z < 1) :
    normalizedBlockBudget n p z / n ≤ QuantumProver.AmplitudeDamping.SecretKey.channelBz p z +
      (2 / z) * QuantumProver.AmplitudeDamping.SecretKey.log2 ((n : ℝ) + 1) / n := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  apply (div_le_iff₀ hnR).mpr
  have heq : (QuantumProver.AmplitudeDamping.SecretKey.channelBz p z +
      (2 / z) * QuantumProver.AmplitudeDamping.SecretKey.log2 ((n : ℝ) + 1) / n) * n =
      (n : ℝ) * QuantumProver.AmplitudeDamping.SecretKey.channelBz p z +
        (2 / z) * QuantumProver.AmplitudeDamping.SecretKey.log2 ((n : ℝ) + 1) := by
    field_simp [hnR.ne']
    <;> ring
  rw [heq]
  exact normalizedBlockBudget_le n hn hp0 hp1 hz0 hz1

theorem tendsto_normalized_type_overhead_zero {z : ℝ} (hz : 0 < z) :
    Filter.Tendsto
      (fun n : ℕ => (2 / z) * QuantumProver.AmplitudeDamping.SecretKey.log2 ((n : ℝ) + 1) / n)
      Filter.atTop (𝓝 0) := by
  have hplus : 0 < 2 + z := by linarith
  have hcoeff : (2 / (2 + z)) * ((2 + z) / z) = 2 / z := by
    field_simp [hz.ne', hplus.ne']
  have h := (QuantumProver.AmplitudeDamping.Scalar.tendsto_typeOverhead_zero z).const_mul
    (2 / (2 + z))
  convert h using 1
  · ext n
    change (2 / z) * QuantumProver.AmplitudeDamping.SecretKey.log2 ((n : ℝ) + 1) / (n : ℝ) =
      (2 / (2 + z)) * (((2 + z) / z) *
        QuantumProver.AmplitudeDamping.SecretKey.log2 ((n : ℝ) + 1) / (n : ℝ))
    rw [← mul_div_assoc, ← mul_assoc, hcoeff]
  · simp

noncomputable def seedRenyiChargeBits {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (z : ℝ) : ℝ :=
  ((1 + z) / z) * QuantumProver.AmplitudeDamping.SecretKey.log2 (∑ i, (a i) ^ (1 / (1 + z)))

theorem seedRenyiChargeBits_le_alphabet {ι : Type*} [Fintype ι] [Nonempty ι]
    (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (haSum : ∑ i, a i = 1)
    (z : ℝ) (hz : 0 < z) :
    seedRenyiChargeBits a z ≤ QuantumProver.AmplitudeDamping.SecretKey.log2 (Fintype.card ι : ℝ) := by
  have hplus : 0 < 1 + z := by positivity
  have hβ0 : 0 ≤ 1 / (1 + z) := (div_pos zero_lt_one hplus).le
  have hβ1 : 1 / (1 + z) ≤ 1 := (div_le_one hplus).mpr (by linarith)
  have hD : 0 < (Fintype.card ι : ℝ) := by
    exact_mod_cast (Fintype.card_pos (α := ι))
  have hsum := probability_power_sum_le_card a ha haSum (1 / (1 + z)) hβ0 hβ1
  have hlog := Real.log_le_log (probability_power_sum_pos a ha haSum _) hsum
  rw [Real.log_rpow hD] at hlog
  have hcoeff : ((1 + z) / z) * (1 - 1 / (1 + z)) = 1 := by
    field_simp [hz.ne', hplus.ne'] <;> ring
  have hmult := mul_le_mul_of_nonneg_left hlog (div_pos hplus hz).le
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hbound : ((1 + z) / z) *
      Real.log (∑ i, (a i) ^ (1 / (1 + z))) ≤
      Real.log (Fintype.card ι : ℝ) := by
    simpa only [← mul_assoc, hcoeff, one_mul] using hmult
  unfold seedRenyiChargeBits QuantumProver.AmplitudeDamping.SecretKey.log2
  rw [← mul_div_assoc]
  apply (div_le_div_iff_of_pos_right hlog2).mpr
  exact hbound

end QuantumProver.AmplitudeDamping.SecretKey.Scalar

namespace QuantumProver.AmplitudeDamping.SecretKey

theorem traceNorm_nonneg {I : Type*} [Fintype I] [DecidableEq I]
    (M : Matrix I I ℂ) : 0 ≤ traceNorm M := by
  have hpsd : (CFC.abs M).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp (CFC.abs_nonneg M)
  exact (RCLike.nonneg_iff.mp hpsd.trace_nonneg).1

theorem traceNorm_of_posSemidef {I : Type*} [Fintype I] [DecidableEq I]
    (M : Matrix I I ℂ) (hM : M.PosSemidef) : traceNorm M = M.trace.re := by
  rw [traceNorm, CFC.abs_of_nonneg M hM.nonneg]

theorem rootFidelity_nonneg {I : Type*} [Fintype I] [DecidableEq I]
    (ρ σ : Density I) : 0 ≤ rootFidelity ρ σ :=
  traceNorm_nonneg _

theorem squaredFidelity_nonneg {I : Type*} [Fintype I] [DecidableEq I]
    (ρ σ : Density I) : 0 ≤ squaredFidelity ρ σ :=
  sq_nonneg _

theorem rootFidelity_self {I : Type*} [Fintype I] [DecidableEq I]
    (ρ : Density I) : rootFidelity ρ ρ = 1 := by
  unfold rootFidelity
  rw [CFC.sqrt_mul_sqrt_self ρ.mat ρ.positive.nonneg,
    traceNorm_of_posSemidef ρ.mat ρ.positive, ρ.normalized]
  rfl

theorem squaredFidelity_self {I : Type*} [Fintype I] [DecidableEq I]
    (ρ : Density I) : squaredFidelity ρ ρ = 1 := by
  simp [squaredFidelity, rootFidelity_self]

theorem cfcSqrt_kronecker
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (M : Matrix I I ℂ) (N : Matrix J J ℂ)
    (hM : M.PosSemidef) (hN : N.PosSemidef) :
    CFC.sqrt (Matrix.kronecker M N) =
      Matrix.kronecker (CFC.sqrt M) (CFC.sqrt N) := by
  have hSM : (CFC.sqrt M).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg M)
  have hSN : (CFC.sqrt N).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg N)
  apply CFC.sqrt_unique ?_ (hSM.kronecker hSN).nonneg
  rw [← Matrix.mul_kronecker_mul,
    CFC.sqrt_mul_sqrt_self M hM.nonneg,
    CFC.sqrt_mul_sqrt_self N hN.nonneg]
  rfl

theorem cfcAbs_kronecker
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (M : Matrix I I ℂ) (N : Matrix J J ℂ) :
    CFC.abs (Matrix.kronecker M N) =
      Matrix.kronecker (CFC.abs M) (CFC.abs N) := by
  unfold CFC.abs
  simp only [Matrix.kronecker, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul]
  exact cfcSqrt_kronecker (M.conjTranspose * M) (N.conjTranspose * N)
    (Matrix.posSemidef_conjTranspose_mul_self M)
    (Matrix.posSemidef_conjTranspose_mul_self N)

theorem traceNorm_kronecker
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (M : Matrix I I ℂ) (N : Matrix J J ℂ) :
    traceNorm (Matrix.kronecker M N) = traceNorm M * traceNorm N := by
  have hM : (CFC.abs M).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp (CFC.abs_nonneg M)
  have hMim : (CFC.abs M).trace.im = 0 :=
    (RCLike.nonneg_iff.mp hM.trace_nonneg).2
  unfold traceNorm
  rw [cfcAbs_kronecker]
  simp only [Matrix.kronecker, Matrix.trace_kronecker,
    Complex.mul_re, hMim, zero_mul, sub_zero]

theorem rootFidelity_tensor
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (ρ σ : Density I) (τ υ : Density J) :
    rootFidelity (ρ.tensor τ) (σ.tensor υ) =
      rootFidelity ρ σ * rootFidelity τ υ := by
  change traceNorm (CFC.sqrt (Matrix.kronecker ρ.mat τ.mat) *
    CFC.sqrt (Matrix.kronecker σ.mat υ.mat)) =
      traceNorm (CFC.sqrt ρ.mat * CFC.sqrt σ.mat) *
      traceNorm (CFC.sqrt τ.mat * CFC.sqrt υ.mat)
  rw [cfcSqrt_kronecker ρ.mat τ.mat ρ.positive τ.positive,
    cfcSqrt_kronecker σ.mat υ.mat σ.positive υ.positive]
  simp only [Matrix.kronecker]
  rw [← Matrix.mul_kronecker_mul]
  exact traceNorm_kronecker _ _

theorem squaredFidelity_tensor
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (ρ σ : Density I) (τ υ : Density J) :
    squaredFidelity (ρ.tensor τ) (σ.tensor υ) =
      squaredFidelity ρ σ * squaredFidelity τ υ := by
  simp only [squaredFidelity, rootFidelity_tensor, mul_pow]

theorem trace_submatrix_equiv
    {I J : Type*} [Fintype I] [Fintype J]
    (M : Matrix I I ℂ) (e : J ≃ I) :
    (M.submatrix e e).trace = M.trace := by
  change (∑ j, M (e j) (e j)) = ∑ i, M i i
  exact e.sum_comp (fun i => M i i)

theorem cfcSqrt_submatrix_equiv
    {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    (M : Matrix I I ℂ) (hM : M.PosSemidef) (e : J ≃ I) :
    CFC.sqrt (M.submatrix e e) = (CFC.sqrt M).submatrix e e := by
  have hS : (CFC.sqrt M).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg M)
  apply CFC.sqrt_unique ?_ (hS.submatrix e).nonneg
  rw [Matrix.submatrix_mul_equiv,
    CFC.sqrt_mul_sqrt_self M hM.nonneg]

theorem cfcAbs_submatrix_equiv
    {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    (M : Matrix I I ℂ) (e : J ≃ I) :
    CFC.abs (M.submatrix e e) = (CFC.abs M).submatrix e e := by
  simpa only [CFC.abs, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv] using
    cfcSqrt_submatrix_equiv (M.conjTranspose * M)
      (Matrix.posSemidef_conjTranspose_mul_self M) e

theorem traceNorm_submatrix_equiv
    {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    (M : Matrix I I ℂ) (e : J ≃ I) :
    traceNorm (M.submatrix e e) = traceNorm M := by
  unfold traceNorm
  rw [cfcAbs_submatrix_equiv, trace_submatrix_equiv]

def Density.relabel
    {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    (e : J ≃ I) (ρ : Density I) : Density J where
  mat := ρ.mat.submatrix e e
  positive := ρ.positive.submatrix e
  normalized := (trace_submatrix_equiv ρ.mat e).trans ρ.normalized

theorem rootFidelity_relabel
    {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    (e : J ≃ I) (ρ σ : Density I) :
    rootFidelity (ρ.relabel e) (σ.relabel e) = rootFidelity ρ σ := by
  change traceNorm (CFC.sqrt (ρ.mat.submatrix e e) *
    CFC.sqrt (σ.mat.submatrix e e)) =
      traceNorm (CFC.sqrt ρ.mat * CFC.sqrt σ.mat)
  rw [cfcSqrt_submatrix_equiv ρ.mat ρ.positive e,
    cfcSqrt_submatrix_equiv σ.mat σ.positive e,
    Matrix.submatrix_mul_equiv, traceNorm_submatrix_equiv]

theorem squaredFidelity_relabel
    {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    (e : J ≃ I) (ρ σ : Density I) :
    squaredFidelity (ρ.relabel e) (σ.relabel e) = squaredFidelity ρ σ := by
  simp only [squaredFidelity, rootFidelity_relabel]

theorem eval_withRightMemory_apply
    {I O J E : Type*} [Fintype I] [Fintype O] [Fintype J] [Fintype E]
    [DecidableEq I] [DecidableEq O] [DecidableEq E]
    (C : KrausChannel I O J) (ρ : Matrix (I × E) (I × E) ℂ)
    (o o' : O) (e e' : E) :
    ((C.withRightMemory E).eval ρ) (o, e) (o', e') =
      (C.eval (fun i j ↦ ρ (i, e) (j, e'))) o o' := by
  classical
  change ((C.withRightMemory E).eval ρ) (o, e) (o', e') =
    (C.eval (Matrix.of (fun i j ↦ ρ (i, e) (j, e')))) o o'
  simp only [KrausChannel.eval, Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro j hj
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply,
    KrausChannel.withRightMemory, Matrix.kroneckerMap_apply, Matrix.one_apply,
    Fintype.sum_prod_type, Finset.sum_mul, Finset.mul_sum, Matrix.of_apply,
    apply_ite, ite_mul, mul_ite, mul_assoc]

theorem partialTraceLeft_eval_withRightMemory
    {I O J E : Type*} [Fintype I] [Fintype O] [Fintype J] [Fintype E]
    [DecidableEq I] [DecidableEq O] [DecidableEq E]
    (C : KrausChannel I O J) (ρ : Matrix (I × E) (I × E) ℂ) :
    partialTraceLeft ((C.withRightMemory E).eval ρ) = partialTraceLeft ρ := by
  ext e e'
  change (∑ o, ((C.withRightMemory E).eval ρ) (o, e) (o, e')) =
    ∑ i, ρ (i, e) (i, e')
  simp_rw [eval_withRightMemory_apply]
  simpa only [Matrix.trace, Matrix.diag] using C.trace_eval (fun i j ↦ ρ (i, e) (j, e'))

theorem basisReadoutChannel_offdiagonal
    {I O : Type*} [Fintype I] [Fintype O] [DecidableEq I] [DecidableEq O]
    (label : I → O) (ρ : Matrix I I ℂ) (x y : O) (hxy : x ≠ y) :
    ((basisReadoutChannel label).eval ρ) x y = 0 := by
  rw [basisReadoutChannel_eval]
  simp only [Matrix.sum_apply]
  apply Finset.sum_eq_zero
  intro i hi
  apply Matrix.single_apply_of_ne
  rintro ⟨hix, hiy⟩
  exact hxy (hix.symm.trans hiy)

theorem privateLabelReadout_isCCQ
    {I E : Type*} [Fintype I] [Fintype E] [DecidableEq I] [DecidableEq E]
    {d : ℕ} (label : I → Fin d × Fin d) (ρ : Density (I × E)) :
    IsCCQ (((basisReadoutChannel label).withRightMemory E).onDensity ρ) := by
  intro x y e e' hxy
  change (((basisReadoutChannel label).withRightMemory E).eval ρ.mat)
    (x, e) (y, e') = 0
  rw [eval_withRightMemory_apply]
  exact basisReadoutChannel_offdiagonal label
    (fun i j => ρ.mat (i, e) (j, e')) x y hxy

theorem privateLabelReadout_preserves_Eve
    {I E : Type*} [Fintype I] [Fintype E] [DecidableEq I] [DecidableEq E]
    {d : ℕ} (label : I → Fin d × Fin d) (ρ : Density (I × E)) :
    (((basisReadoutChannel label).withRightMemory E).onDensity ρ).marginalRight.mat =
      ρ.marginalRight.mat := by
  exact partialTraceLeft_eval_withRightMemory (basisReadoutChannel label) ρ.mat

theorem privateProductReadoutKraus_local
    {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {d : ℕ} (labelA : A → Fin d) (labelB : B → Fin d) (i : A × B) :
    (basisReadoutChannel (fun j : A × B => (labelA j.1, labelB j.2))).op i =
      Matrix.kronecker
        (Matrix.single (labelA i.1) i.1 (1 : ℂ))
        (Matrix.single (labelB i.2) i.2 (1 : ℂ)) := by
  simp [basisReadoutChannel, Matrix.single_kronecker_single]

theorem privateKeyReadout_isCCQ {E : Type*} [Fintype E] [DecidableEq E]
    (d a b : ℕ) (ρ : Density ((Fin (d * a) × Fin (d * b)) × E)) :
    IsCCQ (privateKeyReadout d a b ρ) := by
  exact privateLabelReadout_isCCQ (keyLabels d a b) ρ

theorem privateKeyReadout_preserves_Eve {E : Type*} [Fintype E] [DecidableEq E]
    (d a b : ℕ) (ρ : Density ((Fin (d * a) × Fin (d * b)) × E)) :
    (privateKeyReadout d a b ρ).marginalRight.mat = ρ.marginalRight.mat := by
  exact privateLabelReadout_preserves_Eve (keyLabels d a b) ρ

theorem ProbabilityLaw.renyiSeedCharge_le_alphabet
    {J : Type*} [Fintype J] [DecidableEq J] [Nonempty J]
    (a : ProbabilityLaw J) (z : ℝ) (hz : 0 < z) :
    a.renyiSeedCharge z ≤ log2 (Fintype.card J : ℝ) := by
  exact Scalar.seedRenyiChargeBits_le_alphabet a.weight a.nonnegative a.normalized z hz

theorem Density.eq_of_mat_eq
    {I : Type*} [Fintype I] {ρ σ : Density I} (h : ρ.mat = σ.mat) :
    ρ = σ := by
  cases ρ
  cases σ
  cases h
  rfl

def pairKeyEquiv (d₁ d₂ : ℕ) :
    (Fin (d₁ * d₂) × Fin (d₁ * d₂)) ≃
      ((Fin d₁ × Fin d₁) × (Fin d₂ × Fin d₂)) :=
  (Equiv.prodCongr (splitKeyRegister d₁ d₂) (splitKeyRegister d₁ d₂)).trans
    (Equiv.prodProdProdComm (Fin d₁) (Fin d₂) (Fin d₁) (Fin d₂))

def laneKeyEquiv (d₁ d₂ : ℕ) (E₁ E₂ : Type*) :
    ((Fin (d₁ * d₂) × Fin (d₁ * d₂)) × (E₁ × E₂)) ≃
      (((Fin d₁ × Fin d₁) × E₁) × ((Fin d₂ × Fin d₂) × E₂)) :=
  (Equiv.prodCongr (pairKeyEquiv d₁ d₂) (Equiv.refl (E₁ × E₂))).trans
    (Equiv.prodProdProdComm (Fin d₁ × Fin d₁) (Fin d₂ × Fin d₂) E₁ E₂)

theorem uniformCopiedKey_tensor_relabel
    (d₁ d₂ : ℕ) (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) :
    (((uniformKeyLaw d₁ hd₁).copiedDensity).tensor
      ((uniformKeyLaw d₂ hd₂).copiedDensity)).relabel (pairKeyEquiv d₁ d₂) =
        (uniformKeyLaw (d₁ * d₂) (Nat.mul_pos hd₁ hd₂)).copiedDensity := by
  apply Density.eq_of_mat_eq
  change (Matrix.kronecker
    (Matrix.diagonal (fun i : Fin d₁ × Fin d₁ =>
      if i.1 = i.2 then Complex.ofReal (1 / (d₁ : ℝ)) else 0))
    (Matrix.diagonal (fun i : Fin d₂ × Fin d₂ =>
      if i.1 = i.2 then Complex.ofReal (1 / (d₂ : ℝ)) else 0))).submatrix
      (pairKeyEquiv d₁ d₂) (pairKeyEquiv d₁ d₂) =
    Matrix.diagonal (fun i : Fin (d₁ * d₂) × Fin (d₁ * d₂) =>
      if i.1 = i.2 then Complex.ofReal (1 / ((d₁ * d₂ : ℕ) : ℝ)) else 0)
  simp only [Matrix.kronecker, Matrix.diagonal_kronecker_diagonal,
    Matrix.submatrix_diagonal_equiv]
  congr 1
  funext x
  have hc : Complex.ofReal (1 / (d₁ : ℝ)) *
      Complex.ofReal (1 / (d₂ : ℝ)) =
        Complex.ofReal (1 / ((d₁ * d₂ : ℕ) : ℝ)) := by
    rw [← Complex.ofReal_mul, one_div_mul_one_div, Nat.cast_mul]
  change ((if (splitKeyRegister d₁ d₂ x.1).1 =
      (splitKeyRegister d₁ d₂ x.2).1 then
        Complex.ofReal (1 / (d₁ : ℝ)) else 0) *
    (if (splitKeyRegister d₁ d₂ x.1).2 =
      (splitKeyRegister d₁ d₂ x.2).2 then
        Complex.ofReal (1 / (d₂ : ℝ)) else 0)) =
      if x.1 = x.2 then Complex.ofReal (1 / ((d₁ * d₂ : ℕ) : ℝ)) else 0
  by_cases hx : x.1 = x.2
  · simp only [hx, eq_self_iff_true, ite_true]
    exact hc
  · have hs : splitKeyRegister d₁ d₂ x.1 ≠ splitKeyRegister d₁ d₂ x.2 :=
      fun h => hx ((splitKeyRegister d₁ d₂).injective h)
    by_cases h₁ : (splitKeyRegister d₁ d₂ x.1).1 =
        (splitKeyRegister d₁ d₂ x.2).1
    · have h₂ : (splitKeyRegister d₁ d₂ x.1).2 ≠
          (splitKeyRegister d₁ d₂ x.2).2 :=
        fun h => hs (Prod.ext h₁ h)
      simp only [h₁, h₂, hx, eq_self_iff_true, ite_true, ite_false, mul_zero]
    · simp only [h₁, hx, eq_self_iff_true, ite_false, zero_mul]

theorem tensor_relabel_interleave
    {K K₁ K₂ E₁ E₂ : Type*}
    [Fintype K] [Fintype K₁] [Fintype K₂] [Fintype E₁] [Fintype E₂]
    [DecidableEq K] [DecidableEq K₁] [DecidableEq K₂]
    [DecidableEq E₁] [DecidableEq E₂]
    (e : K ≃ K₁ × K₂) (κ₁ : Density K₁) (κ₂ : Density K₂)
    (ξ₁ : Density E₁) (ξ₂ : Density E₂) :
    ((κ₁.tensor ξ₁).tensor (κ₂.tensor ξ₂)).relabel
      ((Equiv.prodCongr e (Equiv.refl (E₁ × E₂))).trans
        (Equiv.prodProdProdComm K₁ K₂ E₁ E₂)) =
      ((κ₁.tensor κ₂).relabel e).tensor (ξ₁.tensor ξ₂) := by
  apply Density.eq_of_mat_eq
  ext x y
  rcases x with ⟨k, e₁, e₂⟩
  rcases y with ⟨k', e₁', e₂'⟩
  change (κ₁.mat (e k).1 (e k').1 * ξ₁.mat e₁ e₁') *
      (κ₂.mat (e k).2 (e k').2 * ξ₂.mat e₂ e₂') =
    (κ₁.mat (e k).1 (e k').1 * κ₂.mat (e k).2 (e k').2) *
      (ξ₁.mat e₁ e₁' * ξ₂.mat e₂ e₂')
  ring

theorem idealKeyStateAgainst_tensor_relabel
    {E₁ E₂ : Type*} [Fintype E₁] [Fintype E₂]
    [DecidableEq E₁] [DecidableEq E₂]
    (d₁ d₂ : ℕ) (hd₁ : 0 < d₁) (hd₂ : 0 < d₂)
    (ξ₁ : Density E₁) (ξ₂ : Density E₂) :
    ((idealKeyStateAgainst d₁ hd₁ ξ₁).tensor
      (idealKeyStateAgainst d₂ hd₂ ξ₂)).relabel (laneKeyEquiv d₁ d₂ E₁ E₂) =
      idealKeyStateAgainst (d₁ * d₂) (Nat.mul_pos hd₁ hd₂) (ξ₁.tensor ξ₂) := by
  unfold idealKeyStateAgainst laneKeyEquiv
  rw [tensor_relabel_interleave, uniformCopiedKey_tensor_relabel]

theorem rootFidelity_lane_candidate
    {E₁ E₂ : Type*} [Fintype E₁] [Fintype E₂]
    [DecidableEq E₁] [DecidableEq E₂]
    (d₁ d₂ : ℕ) (hd₁ : 0 < d₁) (hd₂ : 0 < d₂)
    (ρ₁ : Density ((Fin d₁ × Fin d₁) × E₁))
    (ρ₂ : Density ((Fin d₂ × Fin d₂) × E₂))
    (ξ₁ : Density E₁) (ξ₂ : Density E₂) :
    rootFidelity ((ρ₁.tensor ρ₂).relabel (laneKeyEquiv d₁ d₂ E₁ E₂))
      (idealKeyStateAgainst (d₁ * d₂) (Nat.mul_pos hd₁ hd₂) (ξ₁.tensor ξ₂)) =
      rootFidelity ρ₁ (idealKeyStateAgainst d₁ hd₁ ξ₁) *
        rootFidelity ρ₂ (idealKeyStateAgainst d₂ hd₂ ξ₂) := by
  rw [← idealKeyStateAgainst_tensor_relabel d₁ d₂ hd₁ hd₂ ξ₁ ξ₂,
    rootFidelity_relabel, rootFidelity_tensor]

theorem squaredFidelity_lane_candidate
    {E₁ E₂ : Type*} [Fintype E₁] [Fintype E₂]
    [DecidableEq E₁] [DecidableEq E₂]
    (d₁ d₂ : ℕ) (hd₁ : 0 < d₁) (hd₂ : 0 < d₂)
    (ρ₁ : Density ((Fin d₁ × Fin d₁) × E₁))
    (ρ₂ : Density ((Fin d₂ × Fin d₂) × E₂))
    (ξ₁ : Density E₁) (ξ₂ : Density E₂) :
    squaredFidelity ((ρ₁.tensor ρ₂).relabel (laneKeyEquiv d₁ d₂ E₁ E₂))
      (idealKeyStateAgainst (d₁ * d₂) (Nat.mul_pos hd₁ hd₂) (ξ₁.tensor ξ₂)) =
      squaredFidelity ρ₁ (idealKeyStateAgainst d₁ hd₁ ξ₁) *
        squaredFidelity ρ₂ (idealKeyStateAgainst d₂ hd₂ ξ₂) := by
  unfold squaredFidelity
  rw [rootFidelity_lane_candidate d₁ d₂ hd₁ hd₂ ρ₁ ρ₂ ξ₁ ξ₂, mul_pow]

end QuantumProver.AmplitudeDamping.SecretKey

noncomputable section

open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix

namespace QuantumProver.AmplitudeDamping.SecretKey

theorem unitary_adjoint_left {I : Type*} [Fintype I] [DecidableEq I]
    (U : Matrix I I ℂ) (hU : U ∈ Matrix.unitaryGroup I ℂ) :
    U.conjTranspose * U = 1 := by
  simpa only [Matrix.star_eq_conjTranspose] using
    (Matrix.mem_unitaryGroup_iff'.mp hU)

theorem unitary_adjoint_right {I : Type*} [Fintype I] [DecidableEq I]
    (U : Matrix I I ℂ) (hU : U ∈ Matrix.unitaryGroup I ℂ) :
    U * U.conjTranspose = 1 := by
  simpa only [Matrix.star_eq_conjTranspose] using
    (Matrix.mem_unitaryGroup_iff.mp hU)

theorem unitary_adjoint_mem {I : Type*} [Fintype I] [DecidableEq I]
    (U : Matrix I I ℂ) (hU : U ∈ Matrix.unitaryGroup I ℂ) :
    U.conjTranspose ∈ Matrix.unitaryGroup I ℂ := by
  apply Matrix.mem_unitaryGroup_iff'.mpr
  simpa only [Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_conjTranspose] using unitary_adjoint_right U hU

theorem unitary_congruence_mul {I : Type*} [Fintype I] [DecidableEq I]
    (U : Matrix I I ℂ) (hU : U ∈ Matrix.unitaryGroup I ℂ)
    (M N : Matrix I I ℂ) :
    (U * M * U.conjTranspose) * (U * N * U.conjTranspose) =
      U * (M * N) * U.conjTranspose := by
  calc
    _ = U * M * (U.conjTranspose * U) * N * U.conjTranspose := by
      simp only [Matrix.mul_assoc]
    _ = _ := by
      rw [unitary_adjoint_left U hU]
      simp only [Matrix.mul_one, Matrix.mul_assoc]

theorem trace_unitary_congruence {I : Type*} [Fintype I] [DecidableEq I]
    (U : Matrix I I ℂ) (hU : U ∈ Matrix.unitaryGroup I ℂ)
    (M : Matrix I I ℂ) :
    (U * M * U.conjTranspose).trace = M.trace := by
  rw [Matrix.trace_mul_cycle, unitary_adjoint_left U hU, Matrix.one_mul]

theorem cfcSqrt_unitary_congruence
    {I : Type*} [Fintype I] [DecidableEq I]
    (U : Matrix I I ℂ) (hU : U ∈ Matrix.unitaryGroup I ℂ)
    (M : Matrix I I ℂ) (hM : M.PosSemidef) :
    CFC.sqrt (U * M * U.conjTranspose) =
      U * CFC.sqrt M * U.conjTranspose := by
  have hSM : (CFC.sqrt M).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg M)
  apply CFC.sqrt_unique ?_ (hSM.mul_mul_conjTranspose_same U).nonneg
  rw [unitary_congruence_mul U hU,
    CFC.sqrt_mul_sqrt_self M hM.nonneg]

theorem cfcAbs_unitary_congruence
    {I : Type*} [Fintype I] [DecidableEq I]
    (U : Matrix I I ℂ) (hU : U ∈ Matrix.unitaryGroup I ℂ)
    (M : Matrix I I ℂ) :
    CFC.abs (U * M * U.conjTranspose) =
      U * CFC.abs M * U.conjTranspose := by
  have hadj : (U * M * U.conjTranspose).conjTranspose =
      U * M.conjTranspose * U.conjTranspose := by
    simp only [Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  change CFC.sqrt ((U * M * U.conjTranspose).conjTranspose *
      (U * M * U.conjTranspose)) =
    U * CFC.sqrt (M.conjTranspose * M) * U.conjTranspose
  rw [hadj, unitary_congruence_mul U hU]
  exact cfcSqrt_unitary_congruence U hU (M.conjTranspose * M)
    (Matrix.posSemidef_conjTranspose_mul_self M)

theorem traceNorm_unitary_congruence
    {I : Type*} [Fintype I] [DecidableEq I]
    (U : Matrix I I ℂ) (hU : U ∈ Matrix.unitaryGroup I ℂ)
    (M : Matrix I I ℂ) :
    traceNorm (U * M * U.conjTranspose) = traceNorm M := by
  unfold traceNorm
  rw [cfcAbs_unitary_congruence U hU, trace_unitary_congruence U hU]

namespace Density

def unitaryConjugate {I : Type*} [Fintype I] [DecidableEq I]
    (U : Matrix I I ℂ) (hU : U ∈ Matrix.unitaryGroup I ℂ)
    (ρ : Density I) : Density I where
  mat := U * ρ.mat * U.conjTranspose
  positive := ρ.positive.mul_mul_conjTranspose_same U
  normalized := (trace_unitary_congruence U hU ρ.mat).trans ρ.normalized

theorem unitaryConjugate_inv
    {I : Type*} [Fintype I] [DecidableEq I]
    (U : Matrix I I ℂ) (hU : U ∈ Matrix.unitaryGroup I ℂ)
    (ρ : Density I) :
    (ρ.unitaryConjugate U hU).unitaryConjugate U.conjTranspose
      (unitary_adjoint_mem U hU) = ρ := by
  apply Density.eq_of_mat_eq
  change U.conjTranspose * (U * ρ.mat * U.conjTranspose) *
    U.conjTranspose.conjTranspose = ρ.mat
  rw [Matrix.conjTranspose_conjTranspose]
  calc
    _ = (U.conjTranspose * U) * ρ.mat * (U.conjTranspose * U) := by
      simp only [Matrix.mul_assoc]
    _ = _ := by rw [unitary_adjoint_left U hU]; simp

theorem unitaryConjugate_apply_inv
    {I : Type*} [Fintype I] [DecidableEq I]
    (U : Matrix I I ℂ) (hU : U ∈ Matrix.unitaryGroup I ℂ)
    (ρ : Density I) :
    (ρ.unitaryConjugate U.conjTranspose (unitary_adjoint_mem U hU)).unitaryConjugate
      U hU = ρ := by
  apply Density.eq_of_mat_eq
  change U * (U.conjTranspose * ρ.mat * U.conjTranspose.conjTranspose) *
    U.conjTranspose = ρ.mat
  rw [Matrix.conjTranspose_conjTranspose]
  calc
    _ = (U * U.conjTranspose) * ρ.mat * (U * U.conjTranspose) := by
      simp only [Matrix.mul_assoc]
    _ = _ := by rw [unitary_adjoint_right U hU]; simp

theorem unitaryConjugate_surjective
    {I : Type*} [Fintype I] [DecidableEq I]
    (U : Matrix I I ℂ) (hU : U ∈ Matrix.unitaryGroup I ℂ) :
    Function.Surjective (fun ρ : Density I => ρ.unitaryConjugate U hU) := by
  intro ρ
  exact ⟨ρ.unitaryConjugate U.conjTranspose (unitary_adjoint_mem U hU),
    unitaryConjugate_apply_inv U hU ρ⟩

end Density

theorem rootFidelity_unitaryConjugate
    {I : Type*} [Fintype I] [DecidableEq I]
    (U : Matrix I I ℂ) (hU : U ∈ Matrix.unitaryGroup I ℂ)
    (ρ σ : Density I) :
    rootFidelity (ρ.unitaryConjugate U hU) (σ.unitaryConjugate U hU) =
      rootFidelity ρ σ := by
  unfold rootFidelity
  change traceNorm (CFC.sqrt (U * ρ.mat * U.conjTranspose) *
    CFC.sqrt (U * σ.mat * U.conjTranspose)) =
      traceNorm (CFC.sqrt ρ.mat * CFC.sqrt σ.mat)
  rw [cfcSqrt_unitary_congruence U hU ρ.mat ρ.positive,
    cfcSqrt_unitary_congruence U hU σ.mat σ.positive,
    unitary_congruence_mul U hU, traceNorm_unitary_congruence U hU]

theorem squaredFidelity_unitaryConjugate
    {I : Type*} [Fintype I] [DecidableEq I]
    (U : Matrix I I ℂ) (hU : U ∈ Matrix.unitaryGroup I ℂ)
    (ρ σ : Density I) :
    squaredFidelity (ρ.unitaryConjugate U hU) (σ.unitaryConjugate U hU) =
      squaredFidelity ρ σ := by
  unfold squaredFidelity
  rw [rootFidelity_unitaryConjugate U hU]

def eveUnitaryMatrix (K : Type*) {E : Type*}
    [Fintype K] [DecidableEq K] [Fintype E] [DecidableEq E]
    (U : Matrix E E ℂ) : Matrix (K × E) (K × E) ℂ :=
  Matrix.kronecker (1 : Matrix K K ℂ) U

theorem eveUnitaryMatrix_mem (K : Type*) {E : Type*}
    [Fintype K] [DecidableEq K] [Fintype E] [DecidableEq E]
    (U : Matrix E E ℂ) (hU : U ∈ Matrix.unitaryGroup E ℂ) :
    eveUnitaryMatrix K U ∈ Matrix.unitaryGroup (K × E) ℂ := by
  apply Matrix.mem_unitaryGroup_iff'.mpr
  change (eveUnitaryMatrix K U).conjTranspose * eveUnitaryMatrix K U = 1
  unfold eveUnitaryMatrix Matrix.kronecker
  rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
    Matrix.conjTranspose_one, Matrix.one_mul, unitary_adjoint_left U hU,
    Matrix.one_kronecker_one]

theorem Density.unitaryConjugate_tensor_right
    {K E : Type*} [Fintype K] [Fintype E] [DecidableEq K] [DecidableEq E]
    (U : Matrix E E ℂ) (hU : U ∈ Matrix.unitaryGroup E ℂ)
    (κ : Density K) (ξ : Density E) :
    (κ.tensor ξ).unitaryConjugate (eveUnitaryMatrix K U) (eveUnitaryMatrix_mem K U hU) =
      κ.tensor (ξ.unitaryConjugate U hU) := by
  apply Density.eq_of_mat_eq
  change (Matrix.kronecker (1 : Matrix K K ℂ) U) *
    (Matrix.kronecker κ.mat ξ.mat) *
      (Matrix.kronecker (1 : Matrix K K ℂ) U).conjTranspose =
        Matrix.kronecker κ.mat (U * ξ.mat * U.conjTranspose)
  simp only [Matrix.kronecker, Matrix.conjTranspose_kronecker,
    ← Matrix.mul_kronecker_mul, Matrix.conjTranspose_one,
    Matrix.one_mul, Matrix.mul_one]

theorem idealKeyStateAgainst_eveUnitary
    {E : Type*} [Fintype E] [DecidableEq E]
    (d : ℕ) (hd : 0 < d) (U : Matrix E E ℂ)
    (hU : U ∈ Matrix.unitaryGroup E ℂ) (ξ : Density E) :
    (idealKeyStateAgainst d hd ξ).unitaryConjugate
      (eveUnitaryMatrix (Fin d × Fin d) U)
        (eveUnitaryMatrix_mem (Fin d × Fin d) U hU) =
      idealKeyStateAgainst d hd (ξ.unitaryConjugate U hU) := by
  exact Density.unitaryConjugate_tensor_right U hU
    ((uniformKeyLaw d hd).copiedDensity) ξ

theorem squaredFidelity_eveUnitary_candidate
    {E : Type*} [Fintype E] [DecidableEq E]
    (d : ℕ) (hd : 0 < d) (U : Matrix E E ℂ)
    (hU : U ∈ Matrix.unitaryGroup E ℂ)
    (ρ : Density ((Fin d × Fin d) × E)) (ξ : Density E) :
    squaredFidelity (ρ.unitaryConjugate
      (eveUnitaryMatrix (Fin d × Fin d) U)
        (eveUnitaryMatrix_mem (Fin d × Fin d) U hU))
      (idealKeyStateAgainst d hd (ξ.unitaryConjugate U hU)) =
        squaredFidelity ρ (idealKeyStateAgainst d hd ξ) := by
  rw [← idealKeyStateAgainst_eveUnitary d hd U hU ξ]
  exact squaredFidelity_unitaryConjugate
    (eveUnitaryMatrix (Fin d × Fin d) U)
      (eveUnitaryMatrix_mem (Fin d × Fin d) U hU) ρ (idealKeyStateAgainst d hd ξ)

theorem wholeKey_candidate_range_eveUnitary
    {E : Type*} [Fintype E] [DecidableEq E]
    (d : ℕ) (hd : 0 < d) (U : Matrix E E ℂ)
    (hU : U ∈ Matrix.unitaryGroup E ℂ)
    (ρ : Density ((Fin d × Fin d) × E)) :
    Set.range (fun ξ : Density E => squaredFidelity
      (ρ.unitaryConjugate (eveUnitaryMatrix (Fin d × Fin d) U)
        (eveUnitaryMatrix_mem (Fin d × Fin d) U hU)) (idealKeyStateAgainst d hd ξ)) =
      Set.range (fun ξ : Density E => squaredFidelity ρ (idealKeyStateAgainst d hd ξ)) := by
  ext v
  constructor
  · rintro ⟨ξ, hξ⟩
    obtain ⟨η, rfl⟩ := Density.unitaryConjugate_surjective U hU ξ
    exact ⟨η, (squaredFidelity_eveUnitary_candidate d hd U hU ρ η).symm.trans hξ⟩
  · rintro ⟨ξ, hξ⟩
    exact ⟨ξ.unitaryConjugate U hU,
      (squaredFidelity_eveUnitary_candidate d hd U hU ρ ξ).trans hξ⟩

theorem optimalWholeKeySquaredFidelity_eveUnitary
    {E : Type*} [Fintype E] [DecidableEq E]
    (d : ℕ) (hd : 0 < d) (U : Matrix E E ℂ)
    (hU : U ∈ Matrix.unitaryGroup E ℂ)
    (ρ : Density ((Fin d × Fin d) × E)) :
    optimalWholeKeySquaredFidelity d hd
      (ρ.unitaryConjugate (eveUnitaryMatrix (Fin d × Fin d) U)
        (eveUnitaryMatrix_mem (Fin d × Fin d) U hU)) =
      optimalWholeKeySquaredFidelity d hd ρ := by
  unfold optimalWholeKeySquaredFidelity
  rw [wholeKey_candidate_range_eveUnitary d hd U hU ρ]

end QuantumProver.AmplitudeDamping.SecretKey

noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix

namespace QuantumProver.AmplitudeDamping.SecretKey

theorem blockDiagonal_posSemidef_C
    {K E : Type*} [Fintype K] [Fintype E] [DecidableEq K] [DecidableEq E]
    (M : K → Matrix E E ℂ) (hM : ∀ k, (M k).PosSemidef) :
    (Matrix.blockDiagonal M).PosSemidef := by
  have hrepr : Matrix.blockDiagonal M =
      (Matrix.blockDiagonal (fun k => CFC.sqrt (M k))).conjTranspose *
        Matrix.blockDiagonal (fun k => CFC.sqrt (M k)) := by
    rw [Matrix.blockDiagonal_conjTranspose, ← Matrix.blockDiagonal_mul]
    congr 1
    funext k
    have hS : (CFC.sqrt (M k)).PosSemidef :=
      Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (M k))
    rw [hS.isHermitian.eq, CFC.sqrt_mul_sqrt_self (M k) (hM k).nonneg]
  rw [hrepr]
  exact Matrix.posSemidef_conjTranspose_mul_self _

theorem cfcSqrt_blockDiagonal
    {K E : Type*} [Fintype K] [Fintype E] [DecidableEq K] [DecidableEq E]
    (M : K → Matrix E E ℂ) (hM : ∀ k, (M k).PosSemidef) :
    CFC.sqrt (Matrix.blockDiagonal M) =
      Matrix.blockDiagonal (fun k => CFC.sqrt (M k)) := by
  apply CFC.sqrt_unique ?_
    (blockDiagonal_posSemidef_C _ (fun k =>
      Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (M k)))).nonneg
  rw [← Matrix.blockDiagonal_mul]
  congr 1
  funext k
  exact CFC.sqrt_mul_sqrt_self (M k) (hM k).nonneg

theorem cfcAbs_blockDiagonal
    {K E : Type*} [Fintype K] [Fintype E] [DecidableEq K] [DecidableEq E]
    (M : K → Matrix E E ℂ) :
    CFC.abs (Matrix.blockDiagonal M) =
      Matrix.blockDiagonal (fun k => CFC.abs (M k)) := by
  change CFC.sqrt ((Matrix.blockDiagonal M).conjTranspose * Matrix.blockDiagonal M) =
    Matrix.blockDiagonal (fun k => CFC.sqrt ((M k).conjTranspose * M k))
  rw [Matrix.blockDiagonal_conjTranspose, ← Matrix.blockDiagonal_mul]
  exact cfcSqrt_blockDiagonal _ (fun k => Matrix.posSemidef_conjTranspose_mul_self (M k))

theorem traceNorm_blockDiagonal
    {K E : Type*} [Fintype K] [Fintype E] [DecidableEq K] [DecidableEq E]
    (M : K → Matrix E E ℂ) :
    traceNorm (Matrix.blockDiagonal M) = ∑ k, traceNorm (M k) := by
  unfold traceNorm
  rw [cfcAbs_blockDiagonal, Matrix.trace_blockDiagonal, Complex.re_sum]

def keyBlockDiagonal {K E : Type*} [DecidableEq K]
    (M : K → Matrix E E ℂ) : Matrix (K × E) (K × E) ℂ :=
  (Matrix.blockDiagonal M).submatrix (Equiv.prodComm K E) (Equiv.prodComm K E)

theorem keyBlockDiagonal_apply {K E : Type*} [DecidableEq K]
    (M : K → Matrix E E ℂ) (x y : K × E) :
    keyBlockDiagonal M x y = if x.1 = y.1 then M x.1 x.2 y.2 else 0 := rfl

theorem keyBlockDiagonal_mul
    {K E : Type*} [Fintype K] [Fintype E] [DecidableEq K] [DecidableEq E]
    (M N : K → Matrix E E ℂ) :
    keyBlockDiagonal M * keyBlockDiagonal N = keyBlockDiagonal (fun k => M k * N k) := by
  unfold keyBlockDiagonal
  rw [Matrix.submatrix_mul_equiv, ← Matrix.blockDiagonal_mul]

theorem cfcSqrt_keyBlockDiagonal
    {K E : Type*} [Fintype K] [Fintype E] [DecidableEq K] [DecidableEq E]
    (M : K → Matrix E E ℂ) (hM : ∀ k, (M k).PosSemidef) :
    CFC.sqrt (keyBlockDiagonal M) = keyBlockDiagonal (fun k => CFC.sqrt (M k)) := by
  unfold keyBlockDiagonal
  rw [cfcSqrt_submatrix_equiv (Matrix.blockDiagonal M)
    (blockDiagonal_posSemidef_C M hM) (Equiv.prodComm K E), cfcSqrt_blockDiagonal M hM]

theorem traceNorm_keyBlockDiagonal
    {K E : Type*} [Fintype K] [Fintype E] [DecidableEq K] [DecidableEq E]
    (M : K → Matrix E E ℂ) :
    traceNorm (keyBlockDiagonal M) = ∑ k, traceNorm (M k) := by
  unfold keyBlockDiagonal
  rw [traceNorm_submatrix_equiv, traceNorm_blockDiagonal]

theorem cfcSqrt_real_smul
    {E : Type*} [Fintype E] [DecidableEq E]
    (r : ℝ) (hr : 0 ≤ r) (M : Matrix E E ℂ) (hM : M.PosSemidef) :
    CFC.sqrt (r • M) = Real.sqrt r • CFC.sqrt M := by
  have hS : (CFC.sqrt M).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg M)
  apply CFC.sqrt_unique ?_ (hS.smul (Real.sqrt_nonneg r)).nonneg
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    CFC.sqrt_mul_sqrt_self M hM.nonneg, Real.mul_self_sqrt hr]

theorem cfcAbs_real_smul
    {E : Type*} [Fintype E] [DecidableEq E]
    (r : ℝ) (hr : 0 ≤ r) (M : Matrix E E ℂ) :
    CFC.abs (r • M) = r • CFC.abs M := by
  change CFC.sqrt ((r • M).conjTranspose * (r • M)) =
    r • CFC.sqrt (M.conjTranspose * M)
  have hprod : (r • M).conjTranspose * (r • M) =
      (r * r) • (M.conjTranspose * M) := by
    simp only [Matrix.conjTranspose_smul, star_trivial, Matrix.smul_mul,
      Matrix.mul_smul, smul_smul]
  rw [hprod, cfcSqrt_real_smul (r * r) (mul_nonneg hr hr)
    (M.conjTranspose * M) (Matrix.posSemidef_conjTranspose_mul_self M)]
  rw [Real.sqrt_mul_self hr]

theorem traceNorm_real_smul
    {E : Type*} [Fintype E] [DecidableEq E]
    (r : ℝ) (hr : 0 ≤ r) (M : Matrix E E ℂ) :
    traceNorm (r • M) = r * traceNorm M := by
  unfold traceNorm
  rw [cfcAbs_real_smul r hr, Matrix.trace_smul, Complex.smul_re, smul_eq_mul]

def classicalKeyBlock {K E : Type*} [Fintype K] [Fintype E]
    (ρ : Density (K × E)) (k : K) : Matrix E E ℂ :=
  ρ.mat.submatrix (fun e => (k, e)) (fun e => (k, e))

theorem classicalKeyBlock_posSemidef
    {K E : Type*} [Fintype K] [Fintype E]
    (ρ : Density (K × E)) (k : K) : (classicalKeyBlock ρ k).PosSemidef :=
  ρ.positive.submatrix (fun e => (k, e))

theorem sum_classicalKeyBlock_eq_marginalRight
    {K E : Type*} [Fintype K] [Fintype E]
    (ρ : Density (K × E)) :
    (∑ k, classicalKeyBlock ρ k) = ρ.marginalRight.mat := by
  ext e e'
  simp only [classicalKeyBlock, Matrix.sum_apply, Matrix.submatrix_apply,
    Density.marginalRight, partialTraceLeft]

theorem sum_trace_classicalKeyBlock
    {K E : Type*} [Fintype K] [Fintype E]
    (ρ : Density (K × E)) :
    (∑ k, (classicalKeyBlock ρ k).trace) = 1 := by
  rw [← Matrix.trace_sum, sum_classicalKeyBlock_eq_marginalRight ρ,
    ρ.marginalRight.normalized]

theorem isCCQ_matrix_eq_keyBlockDiagonal
    {d : ℕ} {E : Type*} [Fintype E] [DecidableEq E]
    (ρ : Density ((Fin d × Fin d) × E)) (hρ : IsCCQ ρ) :
    ρ.mat = keyBlockDiagonal (classicalKeyBlock ρ) := by
  ext x y
  rcases x with ⟨k, e⟩
  rcases y with ⟨k', e'⟩
  rw [keyBlockDiagonal_apply]
  by_cases h : k = k'
  · subst k'
    simp only [ite_true, classicalKeyBlock, Matrix.submatrix_apply]
  · rw [if_neg h]
    exact hρ k k' e e' h

def idealKeyBlockWeight (d : ℕ) (k : Fin d × Fin d) : ℝ :=
  if k.1 = k.2 then 1 / (d : ℝ) else 0

theorem idealKeyBlockWeight_nonneg (d : ℕ) (k : Fin d × Fin d) :
    0 ≤ idealKeyBlockWeight d k := by
  unfold idealKeyBlockWeight
  split_ifs <;> positivity

theorem idealKeyStateAgainst_matrix_eq_keyBlockDiagonal
    {E : Type*} [Fintype E] [DecidableEq E]
    (d : ℕ) (hd : 0 < d) (ξ : Density E) :
    (idealKeyStateAgainst d hd ξ).mat =
      keyBlockDiagonal (fun k => idealKeyBlockWeight d k • ξ.mat) := by
  ext x y
  rw [keyBlockDiagonal_apply]
  change ((if x.1 = y.1 then
      (if x.1.1 = x.1.2 then Complex.ofReal (1 / (d : ℝ)) else 0) else 0) *
      ξ.mat x.2 y.2) =
    if x.1 = y.1 then (idealKeyBlockWeight d x.1 • ξ.mat) x.2 y.2 else 0
  by_cases hxy : x.1 = y.1 <;>
    by_cases hmatch : x.1.1 = x.1.2 <;>
      simp [idealKeyBlockWeight, Matrix.smul_apply, Complex.real_smul, hxy, hmatch]

theorem rootFidelity_isCCQ_ideal_directSum
    {E : Type*} [Fintype E] [DecidableEq E]
    (d : ℕ) (hd : 0 < d)
    (ρ : Density ((Fin d × Fin d) × E)) (hρ : IsCCQ ρ) (ξ : Density E) :
    rootFidelity ρ (idealKeyStateAgainst d hd ξ) =
      (1 / Real.sqrt (d : ℝ)) * ∑ i : Fin d,
        traceNorm (CFC.sqrt (classicalKeyBlock ρ (i, i)) * CFC.sqrt ξ.mat) := by
  have hξ : ∀ k : Fin d × Fin d,
      (idealKeyBlockWeight d k • ξ.mat).PosSemidef :=
    fun k => ξ.positive.smul (idealKeyBlockWeight_nonneg d k)
  unfold rootFidelity
  rw [isCCQ_matrix_eq_keyBlockDiagonal ρ hρ,
    idealKeyStateAgainst_matrix_eq_keyBlockDiagonal d hd ξ,
    cfcSqrt_keyBlockDiagonal (classicalKeyBlock ρ)
      (classicalKeyBlock_posSemidef ρ),
    cfcSqrt_keyBlockDiagonal (fun k => idealKeyBlockWeight d k • ξ.mat) hξ,
    keyBlockDiagonal_mul, traceNorm_keyBlockDiagonal]
  calc
    _ = ∑ k : Fin d × Fin d, Real.sqrt (idealKeyBlockWeight d k) *
        traceNorm (CFC.sqrt (classicalKeyBlock ρ k) * CFC.sqrt ξ.mat) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [cfcSqrt_real_smul (idealKeyBlockWeight d k)
        (idealKeyBlockWeight_nonneg d k) ξ.mat ξ.positive,
        Matrix.mul_smul, traceNorm_real_smul _ (Real.sqrt_nonneg _)]
    _ = _ := by
      rw [Fintype.sum_prod_type]
      simp only [idealKeyBlockWeight, apply_ite, Real.sqrt_zero,
        ite_mul, zero_mul]
      simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
      rw [← Finset.mul_sum]
      simp only [one_div, Real.sqrt_inv]

theorem squaredFidelity_isCCQ_ideal_directSum
    {E : Type*} [Fintype E] [DecidableEq E]
    (d : ℕ) (hd : 0 < d)
    (ρ : Density ((Fin d × Fin d) × E)) (hρ : IsCCQ ρ) (ξ : Density E) :
    squaredFidelity ρ (idealKeyStateAgainst d hd ξ) =
      (1 / (d : ℝ)) * (∑ i : Fin d,
        traceNorm (CFC.sqrt (classicalKeyBlock ρ (i, i)) * CFC.sqrt ξ.mat)) ^ 2 := by
  unfold squaredFidelity
  rw [rootFidelity_isCCQ_ideal_directSum d hd ρ hρ ξ, mul_pow,
    _root_.one_div_pow, Real.sq_sqrt (Nat.cast_nonneg d)]

theorem wholeKeySquaredFidelity_isCCQ_directSum
    {E : Type*} [Fintype E] [DecidableEq E]
    (d : ℕ) (hd : 0 < d)
    (ρ : Density ((Fin d × Fin d) × E)) (hρ : IsCCQ ρ) :
    wholeKeySquaredFidelity d hd ρ =
      (1 / (d : ℝ)) * (∑ i : Fin d,
        traceNorm (CFC.sqrt (classicalKeyBlock ρ (i, i)) *
          CFC.sqrt ρ.marginalRight.mat)) ^ 2 := by
  exact squaredFidelity_isCCQ_ideal_directSum d hd ρ hρ ρ.marginalRight

end QuantumProver.AmplitudeDamping.SecretKey

namespace QuantumProver.AmplitudeDamping.SecretKey

namespace ProbabilityLaw

variable {J : Type*} [Fintype J] [DecidableEq J]

theorem weight_le_one (a : ProbabilityLaw J) (j : J) : a.weight j ≤ 1 := by
  have h := Finset.single_le_sum (fun i (_ : i ∈ Finset.univ) => a.nonnegative i)
    (Finset.mem_univ j)
  simpa only [a.normalized] using h

theorem entropyBits_nonneg (a : ProbabilityLaw J) : 0 ≤ a.entropyBits := by
  apply div_nonneg
  · exact Finset.sum_nonneg fun j _ =>
      Real.negMulLog_nonneg (a.nonnegative j) (a.weight_le_one j)
  · exact (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le

theorem entropyBits_le_alphabet [Nonempty J] (a : ProbabilityLaw J) :
    a.entropyBits ≤ log2 (Fintype.card J : ℝ) := by
  let N : ℝ := Fintype.card J
  have hN : 0 < N := by
    dsimp [N]
    exact_mod_cast (Fintype.card_pos (α := J))
  have hsum : (∑ j, Real.negMulLog (N * a.weight j)) ≤ 0 := by
    calc
      _ ≤ ∑ j, (1 - N * a.weight j) :=
        Finset.sum_le_sum fun j _ =>
          Real.negMulLog_le_one_sub_self (mul_nonneg hN.le (a.nonnegative j))
      _ = 0 := by
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum, a.normalized]
        simp [N]
  have hExpand : (∑ j, Real.negMulLog (N * a.weight j)) =
      -N * Real.log N + N * ∑ j, Real.negMulLog (a.weight j) := by
    simp_rw [Real.negMulLog_mul]
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum,
      a.normalized, one_mul]
    rfl
  rw [hExpand] at hsum
  have hEntropy : (∑ j, Real.negMulLog (a.weight j)) ≤ Real.log N := by
    nlinarith
  exact (div_le_div_iff_of_pos_right (Real.log_pos (by norm_num))).mpr hEntropy

theorem entropyBits_le_bits [Nonempty J] (a : ProbabilityLaw J) (k : ℝ)
    (hAlphabet : (Fintype.card J : ℝ) ≤ (2 : ℝ) ^ k) :
    a.entropyBits ≤ k := by
  have hN : 0 < (Fintype.card J : ℝ) := by
    exact_mod_cast (Fintype.card_pos (α := J))
  have hlog := Real.log_le_log hN hAlphabet
  rw [Real.log_rpow (by norm_num : (0 : ℝ) < 2)] at hlog
  have hbits : log2 (Fintype.card J : ℝ) ≤ k := by
    exact (div_le_iff₀ (Real.log_pos (by norm_num))).mpr hlog
  exact (a.entropyBits_le_alphabet).trans hbits

theorem renyiSeedCharge_le_bits [Nonempty J] (a : ProbabilityLaw J)
    (z k : ℝ) (hz : 0 < z)
    (hAlphabet : (Fintype.card J : ℝ) ≤ (2 : ℝ) ^ k) :
    a.renyiSeedCharge z ≤ k := by
  have hN : 0 < (Fintype.card J : ℝ) := by
    exact_mod_cast (Fintype.card_pos (α := J))
  have hlog := Real.log_le_log hN hAlphabet
  rw [Real.log_rpow (by norm_num : (0 : ℝ) < 2)] at hlog
  have hbits : log2 (Fintype.card J : ℝ) ≤ k := by
    exact (div_le_iff₀ (Real.log_pos (by norm_num))).mpr hlog
  exact (a.renyiSeedCharge_le_alphabet z hz).trans hbits

theorem coherentSeedMatrix_diagonal (a : ProbabilityLaw J) (x : J × J) :
    a.coherentSeedMatrix x x =
      if x.1 = x.2 then (a.weight x.1 : ℂ) else 0 := by
  have hsqrt (j : J) : (Real.sqrt (a.weight j) : ℂ) *
      (Real.sqrt (a.weight j) : ℂ) = (a.weight j : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (a.nonnegative j)]
  by_cases hx : x.1 = x.2 <;>
    simp [coherentSeedMatrix, coherentSeedVector, Matrix.vecMulVec_apply, hx, hsqrt]

theorem coherentSeed_localDephase_matrix (a : ProbabilityLaw J) :
    (((basisReadoutChannel (id : J → J)).withRightMemory J).eval
      a.coherentSeedMatrix) = a.copiedMatrix := by
  ext x y
  rcases x with ⟨i, b⟩
  rcases y with ⟨i', b'⟩
  rw [eval_withRightMemory_apply]
  change ((basisReadoutChannel (id : J → J)).eval
    (Matrix.of fun j k => a.coherentSeedMatrix (j, b) (k, b'))) i i' = _
  by_cases hA : i = i'
  · subst i'
    simp only [basisReadoutChannel_eval, Matrix.sum_apply, Matrix.single_apply,
      id_eq, and_self, Finset.sum_ite_eq, Finset.mem_univ, if_true, Matrix.of_apply]
    by_cases hb : i = b
    · subst b
      by_cases hb' : i = b'
      · subst b'
        simpa [copiedMatrix, Matrix.diagonal_apply] using
          a.coherentSeedMatrix_diagonal (i, i)
      · simp [copiedMatrix, coherentSeedMatrix, coherentSeedVector,
          Matrix.vecMulVec_apply, Matrix.diagonal_apply, hb', Prod.mk.injEq]
    · simp [copiedMatrix, coherentSeedMatrix, coherentSeedVector,
        Matrix.vecMulVec_apply, Matrix.diagonal_apply, hb, Prod.mk.injEq]
  · rw [basisReadoutChannel_offdiagonal id _ i i' hA]
    have hxy : (i, b) ≠ (i', b') := by
      intro h
      exact hA (congrArg Prod.fst h)
    simp [copiedMatrix, Matrix.diagonal_apply, hxy]

theorem coherentSeed_localDephase_density (a : ProbabilityLaw J) :
    (((basisReadoutChannel (id : J → J)).withRightMemory J).onDensity
      a.coherentSeedDensity) = a.copiedDensity := by
  apply Density.eq_of_mat_eq
  exact a.coherentSeed_localDephase_matrix

end ProbabilityLaw

open Matrix Kronecker

theorem eval_withRightMemory_kronecker
    {I O J E : Type*} [Fintype I] [Fintype O] [Fintype J] [Fintype E]
    [DecidableEq I] [DecidableEq O] [DecidableEq E]
    (C : KrausChannel I O J) (M : Matrix I I ℂ) (N : Matrix E E ℂ) :
    (C.withRightMemory E).eval (M ⊗ₖ N) = C.eval M ⊗ₖ N := by
  simp only [KrausChannel.eval, KrausChannel.withRightMemory,
    Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
    ← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one]
  ext x y
  simp only [Matrix.sum_apply, Matrix.kroneckerMap_apply, Finset.sum_mul]

theorem onDensity_withRightMemory_tensor
    {I O J E : Type*} [Fintype I] [Fintype O] [Fintype J] [Fintype E]
    [DecidableEq I] [DecidableEq O] [DecidableEq E]
    (C : KrausChannel I O J) (ρ : Density I) (ξ : Density E) :
    (C.withRightMemory E).onDensity (ρ.tensor ξ) = (C.onDensity ρ).tensor ξ := by
  apply Density.eq_of_mat_eq
  exact eval_withRightMemory_kronecker C ρ.mat ξ.mat

theorem ProbabilityLaw.coherentSeed_localDephase_independent_Eve
    {J E : Type*} [Fintype J] [Fintype E] [DecidableEq J] [DecidableEq E]
    (a : ProbabilityLaw J) (ξ : Density E) :
    (((basisReadoutChannel (id : J → J)).withRightMemory J).withRightMemory E).onDensity
      (a.coherentSeedDensity.tensor ξ) = a.copiedDensity.tensor ξ := by
  rw [onDensity_withRightMemory_tensor, a.coherentSeed_localDephase_density]

end QuantumProver.AmplitudeDamping.SecretKey

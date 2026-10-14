import QuantumProver.InformationTheory.DepolarizingSquashedEntanglement.SquashingIdentities

set_option autoImplicit false

noncomputable section

open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder Matrix Kronecker
  Matrix.Norms.L2Operator ContinuousFunctionalCalculus

namespace QuantumProver.DepolarizingSquashedEntanglement.Fixed16Flags

open Identities

def symmetricX (a b d z : ℝ) : QMatrix Fixed16.CoreIndex := fun p q =>
  if p = q then
    if p = (0, 0) then (a : ℂ) else if p = (1, 1) then (d : ℂ) else (b : ℂ)
  else if (p = (0, 0) ∧ q = (1, 1)) ∨ (p = (1, 1) ∧ q = (0, 0)) then (z : ℂ)
  else 0

def tetraTwirl (ρ : QMatrix Fixed16.CoreIndex) : QMatrix Fixed16.CoreIndex :=
  (1 / 4 : ℂ) • ∑ j : Fin 4, Fixed16.tetraBranchMatrix j * ρ *
    (Fixed16.tetraBranchMatrix j)ᴴ

set_option maxHeartbeats 2000000 in
theorem tetraTwirl_symmetricX (a b d z : ℝ) :
    tetraTwirl (symmetricX a b d z) =
      symmetricX ((a + d + z + b) / 3) ((a + d + 4 * b - 2 * z) / 6)
        ((a + d + z + b) / 3) ((a + d + 4 * z - 2 * b) / 6) := by
  have hc2 := Fixed16.tetraCos_sq
  have hh2 := Fixed16.tetraOff_sq
  have hs : Real.sqrt (3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hc4 : Fixed16.tetraCos ^ 4 = (2 + Real.sqrt 3) / 6 := by
    calc
      _ = (Fixed16.tetraCos ^ 2) ^ 2 := by ring
      _ = (2 + Real.sqrt 3) / 6 := by rw [hc2]; nlinarith
  have hh4 : Fixed16.tetraOff ^ 4 = (2 - Real.sqrt 3) / 24 := by
    calc
      _ = (Fixed16.tetraOff ^ 2) ^ 2 := by ring
      _ = (2 - Real.sqrt 3) / 24 := by rw [hh2]; nlinarith
  have hch : Fixed16.tetraCos ^ 2 * Fixed16.tetraOff ^ 2 = 1 / 12 := by
    rw [hc2, hh2]
    nlinarith
  ext p q
  rcases p with ⟨a', b'⟩
  rcases q with ⟨c', d'⟩
  fin_cases a' <;> fin_cases b' <;> fin_cases c' <;> fin_cases d' <;>
    apply Complex.ext <;>
    norm_num [tetraTwirl, symmetricX, Fixed16.tetraBranchMatrix,
      Fixed16.pairedPauli, Fixed16.tetraCoreMatrix, Fixed16.tetraUnitary,
      pauli, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.transpose_apply, Matrix.map_apply, Matrix.kroneckerMap_apply,
      Matrix.sum_apply, Matrix.smul_apply, Matrix.one_apply,
      Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_succ,
      Complex.mul_re, Complex.mul_im, Complex.star_def] <;>
    ring_nf <;> simp only [hc4, hh4, hc2, hh2] <;> ring_nf <;> simp [hs] <;> ring

theorem environmentKraus_one_sub_eq_retained (r : ℝ) :
    Fixed16.environmentKraus (1 - r) = Fixed16.retainedKraus r := by
  rw [Fixed16.environmentKraus_eq_survival, Fixed16.retainedKraus_eq_survival]
  congr 1
  ring

theorem seedDensity_AB_marginal (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    partialTraceRight (partialTraceRight (seedDensity r hr hr1).matrix) =
      tensorEnvironment (1 - r) (1 - r) Fixed16.coreXi := by
  rw [seedDensity_ABE_marginal, pairedDensity_core_marginal, Matrix.reindex_apply]
  ext p q
  rcases p with ⟨a, b⟩
  rcases q with ⟨c, d⟩
  simp [partialTraceRight, QuantumProver.WernerEndpoint.partialTraceLeft, Matrix.submatrix,
    collectPair, tensorEnvironment, tensorEnvironmentKraus,
    environmentKraus_one_sub_eq_retained, Fixed16.retainedKraus,
    weakPair, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.kroneckerMap_apply, Fintype.sum_prod_type, Fin.sum_univ_two]

theorem seedDensity_AB_eq_symmetricX (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    partialTraceRight (partialTraceRight (seedDensity r hr hr1).matrix) =
      symmetricX ((160 - 76 * r + 33 * r ^ 2) / 160)
        (r * (38 - 33 * r) / 160) (33 * r ^ 2 / 160) (7 * r / 20) := by
  rw [seedDensity_AB_marginal,
    tensorEnvironment_coreXi_eq_X (by linarith : 0 ≤ 1 - r)
      (by linarith : 1 - r ≤ 1) (by linarith : 0 ≤ 1 - r)
      (by linarith : 1 - r ≤ 1)]
  have hroot : (1 : ℝ) - (1 - r) = r := by ring
  have hsq : Real.sqrt r ^ 2 = r := Real.sq_sqrt hr
  ext p q
  rcases p with ⟨a, b⟩
  rcases q with ⟨c, d⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    apply Complex.ext <;> norm_num [dampedCoreX, symmetricX, hroot,
      Complex.mul_re, Complex.mul_im] <;> try ring_nf
  all_goals norm_num [← Complex.ofReal_pow, hsq]
  all_goals ring

def boundaryIsotropic (δ : ℝ) : QMatrix Fixed16.CoreIndex :=
  symmetricX ((1 + δ) / 3) ((1 / 2 - δ) / 3)
    ((1 + δ) / 3) ((1 / 2 + 2 * δ) / 3)

theorem tetraTwirl_seed_AB (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    tetraTwirl (partialTraceRight (partialTraceRight (seedDensity r hr hr1).matrix)) =
      boundaryIsotropic (Scalar.boundaryDelta r) := by
  rw [seedDensity_AB_eq_symmetricX, tetraTwirl_symmetricX]
  unfold boundaryIsotropic Scalar.boundaryDelta
  congr 1 <;> ring

theorem omegaKet_apply (r : ℝ) (ab e : Fixed16.CoreIndex) (j k g : Fin 4) :
    omegaKet r ((ab, (j, e)), (k, g)) =
      if j = k then (1 / 2 : ℂ) * seedBranchKet r j ((ab, e), g) else 0 := rfl

theorem omegaDensity_ABE_apply (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (ab cd e f : Fixed16.CoreIndex) (j l : Fin 4) :
    partialTraceRight (omegaDensity r hr hr1).matrix (ab, (j, e)) (cd, (l, f)) =
      if j = l then (1 / 4 : ℂ) *
        partialTraceRight (pureDensity (seedBranchKet r j)) (ab, e) (cd, f) else 0 := by
  have hs2 : (starRingEnd ℂ) (2 : ℂ) = 2 := by
    simpa using map_natCast (starRingEnd ℂ) 2
  by_cases h : j = l
  · subst l
    simp [omegaDensity, partialTraceRight, QuantumProver.WernerEndpoint.partialTraceLeft,
      pureDensity, QuantumProver.WernerEndpoint.pureDensity, QuantumProver.WernerEndpoint.crossDensity,
      omegaKet_apply, Fintype.sum_prod_type, mul_assoc, Finset.mul_sum, hs2]
    apply Finset.sum_congr rfl
    intro g hg
    ring
  · simp [omegaDensity, partialTraceRight, QuantumProver.WernerEndpoint.partialTraceLeft,
      pureDensity, QuantumProver.WernerEndpoint.pureDensity, QuantumProver.WernerEndpoint.crossDensity,
      omegaKet_apply, Fintype.sum_prod_type, h, Ne.symm h, mul_ite, ite_mul]

theorem seedBranchKet_pureDensity (r : ℝ) (j : Fin 4) :
    pureDensity (seedBranchKet r j) =
      seedBranchLift j * pureDensity (seedKet r) * (seedBranchLift j)ᴴ := by
  exact (QuantumProver.WernerEndpoint.sandwich_crossDensity (seedBranchLift j) (seedKet r) (seedKet r)).symm

theorem seedBranchKet_AB_marginal (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1) (j : Fin 4) :
    partialTraceRight (partialTraceRight (pureDensity (seedBranchKet r j))) =
      Fixed16.tetraBranchMatrix j *
        partialTraceRight (partialTraceRight (seedDensity r hr hr1).matrix) *
          (Fixed16.tetraBranchMatrix j)ᴴ := by
  rw [seedBranchKet_pureDensity, seedBranchLift,
    partialTraceRight_tensor_sandwich, partialTraceRight_tensor_sandwich]
  rfl

theorem omegaDensity_AB_twirl (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    partialTraceRight (partialTraceRight (omegaDensity r hr hr1).matrix) =
      tetraTwirl (partialTraceRight (partialTraceRight (seedDensity r hr hr1).matrix)) := by
  ext ab cd
  calc
    _ = ∑ j : Fin 4, (1 / 4 : ℂ) *
        partialTraceRight (partialTraceRight (pureDensity (seedBranchKet r j))) ab cd := by
      change (∑ u : FixedEnvironment,
        partialTraceRight (omegaDensity r hr hr1).matrix (ab, u) (cd, u)) = _
      rw [Fintype.sum_prod_type]
      simp_rw [omegaDensity_ABE_apply r hr hr1]
      simp only [ite_true, ← Finset.mul_sum]
      rfl
    _ = _ := by
      simp_rw [seedBranchKet_AB_marginal r hr hr1]
      simp [tetraTwirl, Matrix.sum_apply, Matrix.smul_apply, Finset.mul_sum]

theorem omegaDensity_AB_exact (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    partialTraceRight (partialTraceRight (omegaDensity r hr hr1).matrix) =
      boundaryIsotropic (Scalar.boundaryDelta r) := by
  rw [omegaDensity_AB_twirl, tetraTwirl_seed_AB]

end QuantumProver.DepolarizingSquashedEntanglement.Fixed16Flags

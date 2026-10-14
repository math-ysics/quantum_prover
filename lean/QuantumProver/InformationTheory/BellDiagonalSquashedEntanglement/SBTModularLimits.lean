import QuantumProver.InformationTheory.BellDiagonalSquashedEntanglement.ExtensionIdentities

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

noncomputable section

open Filter Set
open scoped Topology BigOperators ComplexConjugate ComplexOrder MatrixOrder Matrix
  Matrix.Norms.L2Operator

namespace QuantumProver.BellDiagonalSquashedEntanglement.SBTModularLimits

open RecoveryGeometry.PetzSupportMap
open QuantumProver.SuperchannelDiscrimination.TensorEntropy

variable {I : Type*} [Fintype I] [DecidableEq I]

local instance : NormedAlgebra ℚ (Mat I) :=
  NormedAlgebra.restrictScalars ℚ ℂ (Mat I)

def phaseScalar (t x : ℝ) : ℂ :=
  Complex.exp (Complex.I * (((t / 2) * Real.log x : ℝ) : ℂ))

def rootScalar (t x : ℝ) : ℂ := phaseScalar t x * (Real.sqrt x : ℂ)

def inverseScalar (t x : ℝ) : ℂ := (Real.sqrt x : ℂ)⁻¹ * phaseScalar t x

@[simp] theorem norm_phaseScalar (t x : ℝ) : ‖phaseScalar t x‖ = 1 := by
  exact Complex.norm_exp_I_mul_ofReal ((t / 2) * Real.log x)

@[simp] theorem rootScalar_zero (t : ℝ) : rootScalar t 0 = 0 := by
  simp [rootScalar]

@[simp] theorem norm_rootScalar (t x : ℝ) : ‖rootScalar t x‖ = Real.sqrt x := by
  simp [rootScalar, norm_mul, Complex.norm_real, Real.sqrt_nonneg]

theorem phaseScalar_continuousAt (t : ℝ) {x : ℝ} (hx : x ≠ 0) :
    ContinuousAt (phaseScalar t) x := by
  unfold phaseScalar
  exact Complex.continuous_exp.continuousAt.comp
    (continuousAt_const.mul (Complex.continuous_ofReal.continuousAt.comp
      (continuousAt_const.mul (Real.continuousAt_log hx))))

theorem rootScalar_continuous (t : ℝ) : Continuous (rootScalar t) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  by_cases hx : x = 0
  · subst x
    change Tendsto (rootScalar t) (𝓝 0) (𝓝 (rootScalar t 0))
    rw [rootScalar_zero]
    apply squeeze_zero_norm (fun y => (norm_rootScalar t y).le)
    simpa using Real.continuous_sqrt.tendsto (0 : ℝ)
  · exact (phaseScalar_continuousAt t hx).mul
      (Complex.continuous_ofReal.comp Real.continuous_sqrt).continuousAt

theorem inverseScalar_continuousAt (t : ℝ) {x : ℝ} (hx : 0 < x) :
    ContinuousAt (inverseScalar t) x := by
  unfold inverseScalar
  exact ((Complex.continuous_ofReal.comp Real.continuous_sqrt).continuousAt.inv₀
    (Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr hx)))).mul
      (phaseScalar_continuousAt t hx.ne')

def affineMatrix (A : Mat I) (c d : ℝ) : Mat I := c • A + d • (1 : Mat I)

theorem cfc_affine_eq {A : Mat I} (hA : A.IsHermitian) (c d : ℝ) :
    cfc (fun x : ℝ => c * x + d) A = affineMatrix A c d := by
  rw [cfc_add (p := IsSelfAdjoint) A (fun x : ℝ => c * x) (fun _ => d)
    (A.finite_real_spectrum.continuousOn _) (A.finite_real_spectrum.continuousOn _),
    cfc_const_mul_id (p := IsSelfAdjoint) c A hA,
    cfc_const (p := IsSelfAdjoint) d A hA, Algebra.algebraMap_eq_smul_one]
  rfl

theorem cfc_affine_spectral {A : Mat I} (hA : A.IsHermitian) (c d : ℝ)
    (f : ℝ → ℝ) :
    cfc f (affineMatrix A c d) =
      Unitary.conjStarAlgAut ℂ (Mat I) hA.eigenvectorUnitary
        (Matrix.diagonal (fun i => (f (c * hA.eigenvalues i + d) : ℂ))) := by
  rw [← cfc_affine_eq hA c d,
    ← cfc_comp (p := IsSelfAdjoint) f (fun x : ℝ => c * x + d) A hA
      ((A.finite_real_spectrum.image (fun x : ℝ => c * x + d)).continuousOn _)
      (A.finite_real_spectrum.continuousOn _)]
  simpa only [Function.comp_apply, Unitary.conjStarAlgAut_apply] using
    cfc_spectral (f ∘ (fun x : ℝ => c * x + d)) hA

theorem sqrt_affine_spectral {A : Mat I} (hA : A.IsHermitian) (c d : ℝ)
    (hAff : (affineMatrix A c d).PosSemidef) :
    CFC.sqrt (affineMatrix A c d) =
      Unitary.conjStarAlgAut ℂ (Mat I) hA.eigenvectorUnitary
        (Matrix.diagonal (fun i => (Real.sqrt (c * hA.eigenvalues i + d) : ℂ))) := by
  rw [CFC.sqrt_eq_real_sqrt _ hAff.nonneg, cfcₙ_eq_cfc]
  exact cfc_affine_spectral hA c d Real.sqrt

theorem modularPhase_affine_spectral {A : Mat I} (hA : A.IsHermitian)
    (c d t : ℝ) :
    (modularPhase (affineMatrix A c d) t : Mat I) =
      Unitary.conjStarAlgAut ℂ (Mat I) hA.eigenvectorUnitary
        (Matrix.diagonal (fun i => phaseScalar t (c * hA.eigenvalues i + d))) := by
  let F := Unitary.conjStarAlgAut ℂ (Mat I) hA.eigenvectorUnitary
  have hF : Continuous F := by
    change Continuous (fun X : Mat I => (hA.eigenvectorUnitary : Mat I) * X *
      (star hA.eigenvectorUnitary : Mat I))
    exact (continuous_const.mul continuous_id).mul continuous_const
  have hDiag : Matrix.diagonal (fun i =>
      Complex.I * (((t / 2) * Real.log (c * hA.eigenvalues i + d) : ℝ) : ℂ)) =
      Complex.I • ((t / 2 : ℝ) • Matrix.diagonal
        (fun i => (Real.log (c * hA.eigenvalues i + d) : ℂ))) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [Matrix.diagonal_apply, smul_eq_mul, Complex.ofReal_mul]
    · simp [Matrix.diagonal_apply, hij, smul_eq_mul]
  have hArg : Complex.I • ((t / 2 : ℝ) • cfc Real.log (affineMatrix A c d)) =
      F (Matrix.diagonal (fun i =>
        Complex.I * (((t / 2) * Real.log (c * hA.eigenvalues i + d) : ℝ) : ℂ))) := by
    rw [cfc_affine_spectral hA c d Real.log, hDiag]
    simp only [F, Unitary.conjStarAlgAut_apply, Matrix.smul_mul, Matrix.mul_smul]
  change NormedSpace.exp
    (Complex.I • ((t / 2 : ℝ) • cfc Real.log (affineMatrix A c d))) = _
  rw [hArg, ← NormedSpace.map_exp F hF, Matrix.exp_diagonal]
  congr 1
  ext i j
  simp [Pi.exp_def, phaseScalar, ← Complex.exp_eq_exp_ℂ]

theorem modularRoot_affine_spectral {A : Mat I} (hA : A.IsHermitian)
    (c d t : ℝ) (hAff : (affineMatrix A c d).PosSemidef) :
    (modularPhase (affineMatrix A c d) t : Mat I) * CFC.sqrt (affineMatrix A c d) =
      Unitary.conjStarAlgAut ℂ (Mat I) hA.eigenvectorUnitary
        (Matrix.diagonal (fun i => rootScalar t (c * hA.eigenvalues i + d))) := by
  rw [modularPhase_affine_spectral hA c d t, sqrt_affine_spectral hA c d hAff,
    ← map_mul, Matrix.diagonal_mul_diagonal']
  rfl

def normalizedIdentity (A : Mat I) (m n δ : ℝ) : Mat I :=
  (1 + δ * m)⁻¹ • (A + (δ * n) • (1 : Mat I))

theorem normalizedIdentity_eq_affine (A : Mat I) (m n δ : ℝ) :
    normalizedIdentity A m n δ =
      affineMatrix A (1 + δ * m)⁻¹ ((1 + δ * m)⁻¹ * (δ * n)) := by
  simp [normalizedIdentity, affineMatrix, smul_add, smul_smul]

theorem normalizedIdentity_posSemidef {A : Mat I} (hA : A.PosSemidef)
    {m n δ : ℝ} (hm : 0 ≤ m) (hn : 0 < n) (hδ : 0 < δ) :
    (normalizedIdentity A m n δ).PosSemidef := by
  apply (hA.add (Matrix.PosSemidef.one.smul (show 0 ≤ δ * n by positivity))).smul
  exact inv_nonneg.mpr (show 0 ≤ 1 + δ * m by positivity)

theorem normalizedEigenvalue_tendsto (x m n : ℝ) :
    Tendsto (fun δ : ℝ => (1 + δ * m)⁻¹ * x + (1 + δ * m)⁻¹ * (δ * n))
      (nhdsWithin 0 (Ioi 0)) (𝓝 x) := by
  have hi : Tendsto (fun δ : ℝ => (1 + δ * m)⁻¹) (𝓝 0) (𝓝 1) := by
    simpa using (tendsto_const_nhds.add (tendsto_id.mul tendsto_const_nhds)).inv₀
      (show (1 + 0 * m : ℝ) ≠ 0 by simp)
  have hz : Tendsto (fun δ : ℝ => δ * n) (𝓝 0) (𝓝 0) := by
    simpa using (tendsto_id : Tendsto (fun δ : ℝ => δ) (𝓝 0) (𝓝 0)).mul
      (tendsto_const_nhds (x := n))
  simpa using ((hi.mul tendsto_const_nhds).add (hi.mul hz)).mono_left nhdsWithin_le_nhds

theorem modularRoot_normalizedIdentity_tendsto {A : Mat I} (hA : A.PosSemidef)
    (m n t : ℝ) (hm : 0 ≤ m) (hn : 0 < n) :
    Tendsto (fun δ : ℝ => (modularPhase (normalizedIdentity A m n δ) t : Mat I) *
      CFC.sqrt (normalizedIdentity A m n δ)) (nhdsWithin 0 (Ioi 0))
      (𝓝 ((modularPhase A t : Mat I) * CFC.sqrt A)) := by
  let F := Unitary.conjStarAlgAut ℂ (Mat I) hA.isHermitian.eigenvectorUnitary
  have hF : Continuous F := by
    change Continuous (fun X : Mat I => (hA.isHermitian.eigenvectorUnitary : Mat I) * X *
      (star hA.isHermitian.eigenvectorUnitary : Mat I))
    exact (continuous_const.mul continuous_id).mul continuous_const
  have hd : Tendsto (fun δ : ℝ => Matrix.diagonal (fun i =>
      rootScalar t ((1 + δ * m)⁻¹ * hA.isHermitian.eigenvalues i +
        (1 + δ * m)⁻¹ * (δ * n)))) (nhdsWithin 0 (Ioi 0))
      (𝓝 (Matrix.diagonal (fun i => rootScalar t (hA.isHermitian.eigenvalues i)))) := by
    apply tendsto_pi_nhds.mpr
    intro i
    apply tendsto_pi_nhds.mpr
    intro j
    by_cases hij : i = j
    · subst j
      simp only [Matrix.diagonal_apply_eq]
      exact (rootScalar_continuous t).continuousAt.tendsto.comp
        (normalizedEigenvalue_tendsto _ m n)
    · simp only [Matrix.diagonal_apply_ne _ hij]
      exact tendsto_const_nhds
  have hLimit := (hF.tendsto _).comp hd
  have hAt : (modularPhase A t : Mat I) * CFC.sqrt A =
      F (Matrix.diagonal (fun i => rootScalar t (hA.isHermitian.eigenvalues i))) := by
    simpa [affineMatrix, F] using modularRoot_affine_spectral hA.isHermitian 1 0 t
      (by simpa [affineMatrix] using hA)
  rw [← hAt] at hLimit
  apply hLimit.congr'
  filter_upwards [eventually_mem_nhdsWithin] with δ hδ
  have hp := normalizedIdentity_posSemidef hA hm hn hδ
  rw [normalizedIdentity_eq_affine] at hp ⊢
  exact (modularRoot_affine_spectral hA.isHermitian _ _ t hp).symm

theorem compressedInverse_affine_spectral {A : Mat I} (hA : A.IsHermitian)
    (c d t : ℝ) :
    inverseRoot (affineMatrix A c d) * (modularPhase (affineMatrix A c d) t : Mat I) *
      supportProjection A =
      Unitary.conjStarAlgAut ℂ (Mat I) hA.eigenvectorUnitary
        (Matrix.diagonal (fun i => inverseScalar t (c * hA.eigenvalues i + d) *
          (nonzeroWeight (hA.eigenvalues i) : ℂ))) := by
  have hs : supportProjection A =
      Unitary.conjStarAlgAut ℂ (Mat I) hA.eigenvectorUnitary
        (Matrix.diagonal (fun i => (nonzeroWeight (hA.eigenvalues i) : ℂ))) := by
    simpa only [supportProjection, Unitary.conjStarAlgAut_apply] using
      cfc_spectral nonzeroWeight hA
  rw [hs, inverseRoot, cfc_affine_spectral hA c d (fun x : ℝ => (Real.sqrt x)⁻¹),
    modularPhase_affine_spectral hA c d t,
    ← map_mul, ← map_mul, Matrix.diagonal_mul_diagonal', Matrix.diagonal_mul_diagonal']
  simp only [inverseScalar, Complex.ofReal_inv]

theorem compressedInverse_normalizedIdentity_tendsto {A : Mat I}
    (hA : A.PosSemidef) (m n t : ℝ) :
    Tendsto (fun δ : ℝ => inverseRoot (normalizedIdentity A m n δ) *
      (modularPhase (normalizedIdentity A m n δ) t : Mat I) * supportProjection A)
      (nhdsWithin 0 (Ioi 0))
      (𝓝 (inverseRoot A * (modularPhase A t : Mat I) * supportProjection A)) := by
  let F := Unitary.conjStarAlgAut ℂ (Mat I) hA.isHermitian.eigenvectorUnitary
  have hF : Continuous F := by
    change Continuous (fun X : Mat I => (hA.isHermitian.eigenvectorUnitary : Mat I) * X *
      (star hA.isHermitian.eigenvectorUnitary : Mat I))
    exact (continuous_const.mul continuous_id).mul continuous_const
  have hd : Tendsto (fun δ : ℝ => Matrix.diagonal (fun i =>
      inverseScalar t ((1 + δ * m)⁻¹ * hA.isHermitian.eigenvalues i +
        (1 + δ * m)⁻¹ * (δ * n)) * (nonzeroWeight (hA.isHermitian.eigenvalues i) : ℂ)))
      (nhdsWithin 0 (Ioi 0)) (𝓝 (Matrix.diagonal (fun i =>
        inverseScalar t (hA.isHermitian.eigenvalues i) *
          (nonzeroWeight (hA.isHermitian.eigenvalues i) : ℂ)))) := by
    apply tendsto_pi_nhds.mpr
    intro i
    apply tendsto_pi_nhds.mpr
    intro j
    by_cases hij : i = j
    · subst j
      simp only [Matrix.diagonal_apply_eq]
      by_cases hz : hA.isHermitian.eigenvalues i = 0
      · simp only [nonzeroWeight, hz, if_pos, Complex.ofReal_zero, mul_zero]
        exact tendsto_const_nhds
      · have hp : 0 < hA.isHermitian.eigenvalues i :=
          lt_of_le_of_ne (hA.eigenvalues_nonneg i) (Ne.symm hz)
        exact ((inverseScalar_continuousAt t hp).tendsto.comp
          (normalizedEigenvalue_tendsto _ m n)).mul tendsto_const_nhds
    · simp only [Matrix.diagonal_apply_ne _ hij]
      exact tendsto_const_nhds
  have hLimit := (hF.tendsto _).comp hd
  have hAt : inverseRoot A * (modularPhase A t : Mat I) * supportProjection A =
      F (Matrix.diagonal (fun i => inverseScalar t (hA.isHermitian.eigenvalues i) *
        (nonzeroWeight (hA.isHermitian.eigenvalues i) : ℂ))) := by
    simpa [affineMatrix, F] using compressedInverse_affine_spectral hA.isHermitian 1 0 t
  rw [← hAt] at hLimit
  apply hLimit.congr'
  exact Eventually.of_forall fun δ => by
    dsimp only [Function.comp_apply]
    rw [normalizedIdentity_eq_affine]
    exact (compressedInverse_affine_spectral hA.isHermitian _ _ t).symm

end QuantumProver.BellDiagonalSquashedEntanglement.SBTModularLimits

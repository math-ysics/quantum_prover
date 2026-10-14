import QuantumProver.InformationTheory.Equipartition.PermutationMeasuredDPIC

noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace QuantumProver.Equipartition.FiniteModel.PinchingUmegaki
open Testing PermutationSpectrum PermutationMeasured

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem pinchingSandwich_fixed_of_commute {κ : Type*} [Fintype κ]
    (P : κ → CMat ι) (hsum : ∑ k, P k = 1)
    (hidem : ∀ k, P k * P k = P k) {X : CMat ι}
    (hc : ∀ k, Commute X (P k)) : pinchingSandwich P X = X := by
  have ht (k : κ) : P k * X * P k = X * P k := by
    rw [← (hc k).eq, Matrix.mul_assoc, hidem]
  simp only [pinchingSandwich, ht]
  rw [← Finset.mul_sum, hsum, Matrix.mul_one]

theorem tracePair_pinching_fixed {κ : Type*} [Fintype κ]
    (P : κ → CMat ι) (hsum : ∑ k, P k = 1)
    (hidem : ∀ k, P k * P k = P k) (A : CMat ι) {X : CMat ι}
    (hc : ∀ k, Commute X (P k)) :
    tracePair (pinchingSandwich P A) X = tracePair A X := by
  calc
    _ = tracePair X (pinchingSandwich P A) := tracePair_comm _ _
    _ = tracePair (pinchingSandwich P X) A := tracePair_pinchingSandwich P A X
    _ = tracePair X A := by rw [pinchingSandwich_fixed_of_commute P hsum hidem hc]
    _ = _ := tracePair_comm _ _

theorem tracePair_spectralPinching_matrixLog_self {ρ σ : CMat ι}
    (hσ : σ.IsHermitian) :
    tracePair (spectralPinching hσ ρ) (matrixLog (spectralPinching hσ ρ)) =
      tracePair ρ (matrixLog (spectralPinching hσ ρ)) := by
  apply tracePair_pinching_fixed (spectralPinchingProjection hσ)
    (sum_spectralPinchingProjection hσ) (spectralPinchingProjection_idempotent hσ)
  intro k
  exact (show Commute (spectralPinching hσ ρ) (spectralPinchingProjection hσ k) from
    pinchingSandwich_commutes_projection _ (spectralPinchingProjection_mul hσ) ρ k).cfc_real Real.log

theorem tracePair_spectralPinching_matrixLog_reference {ρ σ : CMat ι}
    (hσ : σ.IsHermitian) :
    tracePair (spectralPinching hσ ρ) (matrixLog σ) = tracePair ρ (matrixLog σ) := by
  apply tracePair_pinching_fixed (spectralPinchingProjection hσ)
    (sum_spectralPinchingProjection hσ) (spectralPinchingProjection_idempotent hσ)
  intro k
  exact (show Commute σ (spectralPinchingProjection hσ k) from
    spectralPinchingProjection_commutes hσ k).cfc_real Real.log

theorem tracePair_sub_right (A B C : CMat ι) :
    tracePair A (B - C) = tracePair A B - tracePair A C := by
  simp only [tracePair, Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re]

theorem umegakiReal_sub_pinching_eq {ρ σ : CMat ι} (hσ : σ.IsHermitian) :
    umegakiReal ρ σ - umegakiReal (spectralPinching hσ ρ) σ =
      umegakiReal ρ (spectralPinching hσ ρ) := by
  unfold umegakiReal
  rw [tracePair_sub_right, tracePair_sub_right, tracePair_sub_right,
    tracePair_spectralPinching_matrixLog_reference,
    tracePair_spectralPinching_matrixLog_self]
  ring

theorem umegakiReal_sub_pinching_le_log {ρ σ : CMat ι}
    (hρ : IsState ρ) (hσ : σ.IsHermitian) :
    umegakiReal ρ σ - umegakiReal (spectralPinching hσ ρ) σ ≤
      logTwo (spectralBlockCount hσ : ℝ) := by
  letI := isState_nonempty_index hρ
  rw [umegakiReal_sub_pinching_eq hσ]
  apply umegakiReal_le_log_of_domination hρ (spectralPinching_posSemidef hσ hρ.1)
    (by exact_mod_cast spectralBlockCount_pos hσ)
  simpa only [← real_complex_smul_matrix, Complex.ofReal_natCast] using
    spectralPinching_domination hσ hρ.1

theorem spectralPinching_smul {σ : CMat ι} (hσ : σ.IsHermitian)
    (a : ℂ) (A : CMat ι) : spectralPinching hσ (a • A) = a • spectralPinching hσ A := by
  simp only [spectralPinching, pinchingSandwich, Matrix.mul_smul, Matrix.smul_mul,
    Finset.smul_sum]

theorem spectralPinching_sub {σ : CMat ι} (hσ : σ.IsHermitian)
    (A B : CMat ι) : spectralPinching hσ (A - B) =
      spectralPinching hσ A - spectralPinching hσ B := by
  simp only [spectralPinching, pinchingSandwich, Matrix.mul_sub, Matrix.sub_mul,
    Finset.sum_sub_distrib]

theorem spectralPinching_preserves_domination {ρ σ : CMat ι}
    (hσ : σ.IsHermitian) {a : ℂ} (hdom : LoewnerLE ρ (a • σ)) :
    LoewnerLE (spectralPinching hσ ρ) (a • σ) := by
  have h := spectralPinching_posSemidef hσ hdom
  change (a • σ - spectralPinching hσ ρ).PosSemidef
  simpa only [spectralPinching_sub, spectralPinching_smul, spectralPinching_fixed] using h

theorem cfc_eq_sum_singleton (A : CMat ι) (hA : A.IsHermitian) (f : ℝ → ℝ) :
    cfc f A = ∑ j, (f (hA.eigenvalues j) : ℂ) •
      unitaryPartitionProjection hA.eigenvectorUnitary id j := by
  rw [Spectral.cfc_eq_conjugate _ hA]
  exact unitary_partition_diagonal_sum hA.eigenvectorUnitary (id : ι → ι)
    (fun j => f (hA.eigenvalues j))

theorem cfc_eq_sum_spectralPinchingProjection {σ : CMat ι}
    (hσ : σ.IsHermitian) (f : ℝ → ℝ) :
    cfc f σ = ∑ k : SpectralLabels hσ,
      (f (k : ℝ) : ℂ) • spectralPinchingProjection hσ k :=
  cfc_eq_sum_of_eigenmatrix_resolution hσ (spectralPinchingProjection hσ)
    (fun k : SpectralLabels hσ => (k : ℝ))
    (sum_spectralPinchingProjection hσ) (spectralPinchingProjection_mul_left hσ) f

theorem trace_singletonEigenProjection (U : Matrix.unitaryGroup ι ℂ) (j : ι) :
    (Matrix.trace (unitaryPartitionProjection U id j)).re = 1 := by
  have ht := Spectral.trace_unitary_conjugate U (diagonalSelector (id : ι → ι) j)
  change Matrix.trace (unitaryPartitionProjection U id j) =
    Matrix.trace (diagonalSelector (id : ι → ι) j) at ht
  rw [ht]
  simp [diagonalSelector, Matrix.trace_diagonal, Complex.re_sum]

theorem compressedSpectralOverlap_sum {ρ σ : CMat ι}
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) (j : ι) :
    ∑ k : SpectralLabels hσ.1, compressedSpectralOverlap hρ hσ (k, j) = 1 := by
  change (∑ k, tracePair
    (unitaryPartitionProjection (spectralPinching_posSemidef hσ.1 hρ).1.eigenvectorUnitary id j)
    (spectralPinchingProjection hσ.1 k)) = 1
  rw [← tracePair_sum_right, sum_spectralPinchingProjection, tracePair_one_right]
  exact trace_singletonEigenProjection _ j

theorem tracePair_cfc_reference_eq_compressed_sum {ρ σ : CMat ι}
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) (f : ℝ → ℝ) :
    tracePair (spectralPinching hσ.1 ρ) (cfc f σ) =
      ∑ z : SpectralLabels hσ.1 × ι,
        (spectralPinching_posSemidef hσ.1 hρ).1.eigenvalues z.2 *
          f (z.1 : ℝ) * compressedSpectralOverlap hρ hσ z := by
  classical
  conv_lhs => rw [← cfc_id' (p := IsSelfAdjoint) ℝ (spectralPinching hσ.1 ρ)
    (spectralPinching_posSemidef hσ.1 hρ).1]
  rw [cfc_eq_sum_singleton _ (spectralPinching_posSemidef hσ.1 hρ).1,
    cfc_eq_sum_spectralPinchingProjection hσ.1 f]
  simp only [id_eq, tracePair_sum_left, tracePair_smul_left, tracePair_sum_right,
    tracePair_smul_right, Finset.mul_sum]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro j _
  dsimp only [compressedSpectralOverlap]
  ring

theorem umegakiReal_spectralPinching_eq_sum {ρ σ : CMat ι}
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) :
    umegakiReal (spectralPinching hσ.1 ρ) σ =
      ∑ z : SpectralLabels hσ.1 × ι,
        (spectralPinching_posSemidef hσ.1 hρ).1.eigenvalues z.2 *
          (logTwo ((spectralPinching_posSemidef hσ.1 hρ).1.eigenvalues z.2) -
            logTwo (z.1 : ℝ)) * compressedSpectralOverlap hρ hσ z := by
  classical
  let A := spectralPinching hσ.1 ρ
  let hA := spectralPinching_posSemidef hσ.1 hρ
  have hself : tracePair A (matrixLog A) = ∑ z : SpectralLabels hσ.1 × ι,
      hA.1.eigenvalues z.2 * Real.log (hA.1.eigenvalues z.2) *
        compressedSpectralOverlap hρ hσ z := by
    change (A * cfc Real.log A).trace.re = _
    rw [Spectral.trace_mul_cfc_self_eq_sum Real.log hA.1, Fintype.sum_prod_type,
      Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    change hA.1.eigenvalues j * Real.log (hA.1.eigenvalues j) =
      ∑ k : SpectralLabels hσ.1, (hA.1.eigenvalues j * Real.log (hA.1.eigenvalues j)) *
        compressedSpectralOverlap hρ hσ (k, j)
    rw [← Finset.mul_sum, compressedSpectralOverlap_sum, mul_one]
  unfold umegakiReal
  rw [tracePair_sub_right, hself, matrixLog,
    tracePair_cfc_reference_eq_compressed_sum hρ hσ Real.log,
    ← Finset.sum_sub_distrib, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro z _
  unfold logTwo
  ring

theorem scaled_umegaki_term {p q a : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (ha : 0 ≤ a)
    (hs : q = 0 → p * a = 0) :
    p * a * (logTwo (p * a) - logTwo (q * a)) = p * (logTwo p - logTwo q) * a := by
  by_cases hp0 : p = 0
  · simp [hp0]
  by_cases ha0 : a = 0
  · simp [ha0]
  have hp' : 0 < p := lt_of_le_of_ne hp (Ne.symm hp0)
  have ha' : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
  have hq' : 0 < q := by
    apply lt_of_le_of_ne hq
    intro he
    exact (mul_pos hp' ha').ne' (hs he.symm)
  rw [logTwo_mul_pos hp' ha', logTwo_mul_pos hq' ha']
  ring

theorem classicalSupportLE_measurement_of_domination {L : ℕ}
    (M : FinitePOVM ι L) {ρ σ : CMat ι} (hρ : ρ.PosSemidef) {a : ℝ}
    (hdom : LoewnerLE ρ ((a : ℂ) • σ)) :
    classicalSupportLE (measurementMass M ρ) (measurementMass M σ) := by
  intro i hi
  have hb := measurementMass_domination M hdom i
  rw [hi, mul_zero] at hb
  exact le_antisymm hb (measurementMass_nonneg M hρ i)

theorem classicalUmegaki_compressedSpectralPOVM {ρ σ : CMat ι}
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) {a : ℝ}
    (hdom : LoewnerLE ρ ((a : ℂ) • σ)) :
    classicalUmegaki (measurementMass (compressedSpectralPOVM hρ hσ) ρ)
        (measurementMass (compressedSpectralPOVM hρ hσ) σ) =
      umegaki (spectralPinching hσ.1 ρ) σ := by
  classical
  have hs := classicalSupportLE_measurement_of_domination (compressedSpectralPOVM hρ hσ) hρ hdom
  have hp := supportLE_of_psd_domination (spectralPinching_posSemidef hσ.1 hρ)
    (spectralPinching_preserves_domination hσ.1 hdom)
  rw [classicalUmegaki, if_pos hs, umegaki_of_support hp]
  apply congrArg (fun x : ℝ => (x : EReal))
  rw [umegakiReal_spectralPinching_eq_sum hρ hσ]
  calc
    _ = ∑ z : SpectralLabels hσ.1 × ι,
        measurementMass (compressedSpectralPOVM hρ hσ) ρ
          ((Fintype.equivFin (SpectralLabels hσ.1 × ι)) z) *
          (logTwo (measurementMass (compressedSpectralPOVM hρ hσ) ρ
            ((Fintype.equivFin (SpectralLabels hσ.1 × ι)) z)) -
          logTwo (measurementMass (compressedSpectralPOVM hρ hσ) σ
            ((Fintype.equivFin (SpectralLabels hσ.1 × ι)) z))) :=
      (Equiv.sum_comp (Fintype.equivFin (SpectralLabels hσ.1 × ι)) _).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro z _
      rw [compressedSpectralPOVM_null_mass, compressedSpectralPOVM_alternative_mass]
      apply scaled_umegaki_term ((spectralPinching_posSemidef hσ.1 hρ).eigenvalues_nonneg z.2)
        (spectralLabel_value_nonneg hσ z.1) (compressedSpectralOverlap_nonneg hρ hσ z)
      intro hz
      have hh := hs ((Fintype.equivFin (SpectralLabels hσ.1 × ι)) z)
        (by rw [compressedSpectralPOVM_alternative_mass, hz]; simp)
      rwa [compressedSpectralPOVM_null_mass] at hh

theorem umegaki_spectralPinching_le_measured {ρ σ : CMat ι}
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) {a : ℝ}
    (hdom : LoewnerLE ρ ((a : ℂ) • σ)) :
    umegaki (spectralPinching hσ.1 ρ) σ ≤ measuredDivergence ρ σ 1 := by
  rw [← classicalUmegaki_compressedSpectralPOVM hρ hσ hdom]
  exact le_sSup ⟨_, compressedSpectralPOVM hρ hσ, by simp [classicalRenyiDivergence]⟩

theorem umegaki_sub_log_spectralCount_le_measured {ρ σ : CMat ι}
    (hρ : IsState ρ) (hσ : σ.PosSemidef) {a : ℝ}
    (hdom : LoewnerLE ρ ((a : ℂ) • σ)) :
    umegaki ρ σ - (logTwo (spectralBlockCount hσ.1 : ℝ) : EReal) ≤
      measuredDivergence ρ σ 1 := by
  have hs := supportLE_of_psd_domination hρ.1 hdom
  have hp := supportLE_of_psd_domination (spectralPinching_posSemidef hσ.1 hρ.1)
    (spectralPinching_preserves_domination hσ.1 hdom)
  have hb := umegakiReal_sub_pinching_le_log hρ hσ.1
  have hr : umegakiReal ρ σ - logTwo (spectralBlockCount hσ.1 : ℝ) ≤
      umegakiReal (spectralPinching hσ.1 ρ) σ := by linarith
  calc
    _ = ((umegakiReal ρ σ - logTwo (spectralBlockCount hσ.1 : ℝ) : ℝ) : EReal) := by
      rw [umegaki_of_support hs, EReal.coe_sub]
    _ ≤ (umegakiReal (spectralPinching hσ.1 ρ) σ : EReal) := EReal.coe_le_coe hr
    _ = umegaki (spectralPinching hσ.1 ρ) σ := (umegaki_of_support hp).symm
    _ ≤ measuredDivergence ρ σ 1 := umegaki_spectralPinching_le_measured hρ.1 hσ hdom

theorem physical_set_umegaki_sub_pinchingOverhead_le_measured {d n : ℕ}
    {F : QuantumFamilies d} (hF : PhysicalAssumptions F) (hn : 0 < n) :
    setUmegaki F n - (pinchingOverhead d n : EReal) ≤ setMeasuredDivergence F n 1 := by
  unfold setMeasuredDivergence
  apply le_sInf
  rintro z ⟨ρ, hρ, σ, hσ, rfl⟩
  have hr := siteAverage_mem_null hF hn hρ
  have hs := siteAverage_mem_alternative hF hn hσ
  have hstate := hF.null_states n hn _ hr
  have hpos := hF.alternative_positive n hn _ hs
  obtain ⟨C, hC⟩ := hF.linear_growth
  have hdom := (hC n hn _ hr _ hs).1
  have hi : setUmegaki F n ≤ umegaki (siteAverage ρ) (siteAverage σ) :=
    sInf_le ⟨siteAverage ρ, hr, siteAverage σ, hs, rfl⟩
  have hp := umegaki_sub_log_spectralCount_le_measured hstate hpos hdom
  have hg : (logTwo (spectralBlockCount hpos.1 : ℝ) : EReal) ≤
      (pinchingOverhead d n : EReal) := EReal.coe_le_coe
    ((log_spectralBlockCount_le hpos.1 (siteAverage_invariant σ)).trans
      (polynomialLog_le_pinchingOverhead (physical_dimension_pos hF hn)))
  exact (EReal.sub_le_sub hi hg).trans (hp.trans (measuredDivergence_siteAverage_le ρ σ 1))

end QuantumProver.Equipartition.FiniteModel.PinchingUmegaki

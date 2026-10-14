import QuantumProver.InformationTheory.Equipartition.TestingBounds
import QuantumProver.InformationTheory.SuperchannelDiscrimination.TestingTheorems
import QuantumProver.InformationTheory.PetzPowerCompression

set_option autoImplicit false

noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Matrix Kronecker Topology
open Matrix Filter
open QuantumProver.Equipartition.FiniteModel
open QuantumProver.SuperchannelDiscrimination
open QuantumProver.SuperchannelDiscrimination.KrausCompletion
open QuantumProver.SuperchannelDiscrimination.MatrixLog
open QuantumProver.SuperchannelDiscrimination.ModularMatrix

namespace QuantumProver.PetzModularPower

variable {I O : Type*} [Fintype I] [Fintype O] [DecidableEq I] [DecidableEq O]

set_option maxHeartbeats 800000 in
theorem matrixRpow_kronecker {A : CMat I} {B : CMat O}
    (hA : A.PosSemidef) (hB : B.PosSemidef) (q : ℝ) :
    matrixRpow (A ⊗ₖ B) q = matrixRpow A q ⊗ₖ matrixRpow B q := by
  have hd : Matrix.diagonal (fun z : I × O =>
      (Real.rpow (hA.1.eigenvalues z.1 * hB.1.eigenvalues z.2) q : ℂ)) =
      Matrix.diagonal (fun z : I × O =>
        (Real.rpow (hA.1.eigenvalues z.1) q : ℂ) *
          (Real.rpow (hB.1.eigenvalues z.2) q : ℂ)) := by
    apply congrArg Matrix.diagonal
    funext z
    have hxy : (hA.1.eigenvalues z.1 * hB.1.eigenvalues z.2) ^ q =
        hA.1.eigenvalues z.1 ^ q * hB.1.eigenvalues z.2 ^ q :=
      Real.mul_rpow (hA.eigenvalues_nonneg z.1) (hB.eigenvalues_nonneg z.2)
    simpa only [Real.rpow_eq_pow, Complex.ofReal_mul] using
      congrArg Complex.ofReal hxy
  simp only [matrixRpow, TensorEntropy.cfc_kronecker_spectral _ hA.1 hB.1,
    TensorEntropy.cfc_spectral _ hA.1, TensorEntropy.cfc_spectral _ hB.1]
  rw [← TensorEntropy.unitaryKronecker_conjugate, Matrix.diagonal_kronecker_diagonal]
  rw [hd]

theorem matrixRpow_transpose {A : CMat I} (hA : A.IsHermitian) (q : ℝ) :
    matrixRpow Aᵀ q = (matrixRpow A q)ᵀ :=
  ModularMatrix.cfc_transpose (fun x : ℝ => Real.rpow x q) hA

theorem matrixRpow_inverse {A : CMat I} (hA : A.PosDef) (q : ℝ) :
    matrixRpow A⁻¹ q = matrixRpow A (-q) := by
  have hinv : A⁻¹ = cfc (fun x : ℝ => x⁻¹) A := by
    simpa using MatrixLog.shifted_inverse_cfc hA (t := 0) (by simp)
  have hc := cfc_comp (p := IsSelfAdjoint) (fun x : ℝ => Real.rpow x q)
    (fun x : ℝ => x⁻¹) A hA.1
    ((A.finite_real_spectrum.image _).continuousOn _)
    (A.finite_real_spectrum.continuousOn _)
  unfold matrixRpow
  rw [hinv, ← hc]
  congr 1
  funext x
  exact (Real.rpow_neg_eq_inv_rpow x q).symm

theorem matrixRpow_mul {A : CMat I} (hA : A.PosDef) (x y : ℝ) :
    matrixRpow A x * matrixRpow A y = matrixRpow A (x + y) := by
  simp only [matrixRpow_eq_cfc_rpow hA.posSemidef, CFC.rpow_eq_pow]
  exact (CFC.rpow_add (x := x) (y := y) hA.isUnit).symm

theorem sqrt_matrixRpow_sandwich {A : CMat I} (hA : A.PosDef) (q : ℝ) :
    CFC.sqrt A * matrixRpow A (-q) * CFC.sqrt A = matrixRpow A (1 - q) := by
  have hs : CFC.sqrt A = matrixRpow A (1 / 2 : ℝ) := by
    rw [matrixRpow_eq_cfc_rpow hA.posSemidef]
    exact CFC.sqrt_eq_rpow
  rw [hs, matrixRpow_mul hA, matrixRpow_mul hA]
  congr 1
  ring

theorem modular_power_quadratic {A B : CMat I}
    (hA : A.PosDef) (hB : B.PosSemidef) (q : ℝ) :
    quadraticValue (matrixRpow (delta B A) q) (flatten (CFC.sqrt A)) =
      petzTrace A B (1 - q) := by
  rw [delta, matrixRpow_kronecker hB hA.inv.posSemidef.transpose,
    matrixRpow_transpose hA.inv.1, matrixRpow_inverse hA,
    kronecker_transpose_quadratic]
  have hs : (CFC.sqrt A).IsHermitian := (CFC.sqrt_nonneg A).posSemidef.1
  rw [hs.eq]
  have hcycle : (CFC.sqrt A * matrixRpow B q * CFC.sqrt A * matrixRpow A (-q)).trace =
      ((CFC.sqrt A * matrixRpow A (-q) * CFC.sqrt A) * matrixRpow B q).trace := by
    simpa only [Matrix.mul_assoc] using
      Matrix.trace_mul_cycle (CFC.sqrt A) (matrixRpow B q)
        (CFC.sqrt A * matrixRpow A (-q))
  rw [hcycle, sqrt_matrixRpow_sandwich hA]
  have hq : 1 - (1 - q) = q := by ring
  simp only [petzTrace, tracePair, hq]

theorem petzTrace_extend {J : Type*} [Fintype J] [DecidableEq J]
    (U : Matrix O J ℂ) (hU : Uᴴ * U = 1) {A B : CMat J}
    (hA : A.IsHermitian) (hB : B.IsHermitian) {alpha : ℝ}
    (hAlpha0 : 0 < alpha) (hAlpha1 : alpha < 1) :
    petzTrace (ZeroExtension.extend U A) (ZeroExtension.extend U B) alpha =
      petzTrace A B alpha := by
  unfold petzTrace tracePair matrixRpow
  rw [ZeroExtension.cfc_extend U hU (fun x : ℝ => Real.rpow x alpha)
      (Real.zero_rpow (ne_of_gt hAlpha0)) hA,
    ZeroExtension.cfc_extend U hU (fun x : ℝ => Real.rpow x (1 - alpha))
      (Real.zero_rpow (ne_of_gt (sub_pos.mpr hAlpha1))) hB,
    ZeroExtension.extend_mul U hU, ZeroExtension.extend_trace U hU]

theorem krausAction_posDef_of_one {Kappa : Type*} [Fintype Kappa]
    (K : Kappa → Matrix O I ℂ) (hOne : (krausAction K 1).PosDef)
    {A : CMat I} (hA : A.PosDef) : (krausAction K A).PosDef := by
  classical
  by_cases hI : Nonempty I
  · letI : Nonempty I := hI
    obtain ⟨r, hr, hrA⟩ :=
      (CFC.exists_pos_algebraMap_le_iff A hA.1).mpr
        (fun x hx => hA.isStrictlyPositive.spectrum_pos hx)
    rw [Algebra.algebraMap_eq_smul_one] at hrA
    have hpos := krausAction_posSemidef K
      (Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr hrA))
    have heq : krausAction K (A - r • (1 : CMat I)) =
        krausAction K A - r • krausAction K 1 := by
      simp [krausAction, Matrix.mul_sub, Matrix.sub_mul,
        Matrix.mul_smul, Matrix.smul_mul, Finset.sum_sub_distrib, Finset.smul_sum]
    rw [heq] at hpos
    exact Matrix.isStrictlyPositive_iff_posDef.mp
      ((hOne.smul hr).isStrictlyPositive.of_le (sub_nonneg.mp hpos.nonneg))
  · have hAone : A = 1 := by
      ext i j
      exact (hI ⟨i⟩).elim
    simpa only [hAone] using hOne

theorem continuousOn_matrixRpow {q : ℝ} (hq : 0 < q) :
    ContinuousOn (fun A : CMat I => matrixRpow A q) {A | A.PosSemidef} := by
  let qn : NNReal := ⟨q, hq.le⟩
  have h := (CFC.continuousOn_nnrpow (A := CMat I) qn).mono
    (fun A (hA : A.PosSemidef) => hA.nonneg)
  refine h.congr ?_
  intro A hA
  dsimp only
  rw [matrixRpow_eq_cfc_rpow hA, CFC.rpow_eq_pow]
  exact (CFC.nnrpow_eq_rpow (a := A) (x := qn) hq).symm

theorem matrixRpow_tendsto_of_psd {T : Type*} {l : Filter T}
    {Aseq : T → CMat I} {A : CMat I} (hA : A.PosSemidef)
    (hSeq : ∀ᶠ t in l, (Aseq t).PosSemidef)
    (hLim : Tendsto Aseq l (𝓝 A)) {q : ℝ} (hq : 0 < q) :
    Tendsto (fun t => matrixRpow (Aseq t) q) l (𝓝 (matrixRpow A q)) := by
  exact ((continuousOn_matrixRpow hq) A hA).tendsto.comp
    (tendsto_nhdsWithin_iff.mpr ⟨hLim, hSeq⟩)

theorem petzTrace_tendsto_of_psd {T : Type*} {l : Filter T}
    {Aseq Bseq : T → CMat I} {A B : CMat I}
    (hA : A.PosSemidef) (hB : B.PosSemidef)
    (hASeq : ∀ᶠ t in l, (Aseq t).PosSemidef)
    (hBSeq : ∀ᶠ t in l, (Bseq t).PosSemidef)
    (hALim : Tendsto Aseq l (𝓝 A)) (hBLim : Tendsto Bseq l (𝓝 B))
    {alpha : ℝ} (hAlpha0 : 0 < alpha) (hAlpha1 : alpha < 1) :
    Tendsto (fun t => petzTrace (Aseq t) (Bseq t) alpha) l (𝓝 (petzTrace A B alpha)) := by
  have htr : Continuous (fun X : CMat I => X.trace.re) := by
    unfold Matrix.trace
    fun_prop
  exact (htr.tendsto _).comp
    ((matrixRpow_tendsto_of_psd hA hASeq hALim hAlpha0).mul
      (matrixRpow_tendsto_of_psd hB hBSeq hBLim (sub_pos.mpr hAlpha1)))

theorem petzTrace_le_kraus_of_posDef {Kappa : Type*} [Fintype Kappa]
    (K : Kappa → Matrix O I ℂ) (hK : krausGram K = 1)
    {A B : CMat I} (hA : A.PosDef) (hB : B.PosSemidef)
    (hOutA : (krausAction K A).PosDef) {alpha : ℝ}
    (hAlpha0 : 0 < alpha) (hAlpha1 : alpha < 1) :
    petzTrace A B alpha ≤ petzTrace (krausAction K A) (krausAction K B) alpha := by
  have hq0 : 0 < 1 - alpha := sub_pos.mpr hAlpha1
  have hq1 : 1 - alpha ≤ 1 := by linarith
  have hOrder := PetzPowerCompression.matrixRpow_contraction_mono
    (pullbackMatrix K A) (pullbackMatrix_contraction K hK hA.posSemidef hOutA)
    (delta_posSemidef hA hB)
    (delta_posSemidef hOutA (krausAction_posSemidef K hB))
    (pullbackMatrix_modular_order K hK hA hB hOutA) hq0 hq1
  have h := quadraticValue_nonneg hOrder (flatten (CFC.sqrt (krausAction K A)))
  rw [quadraticValue_sub, quadratic_congruence, pullbackMatrix_sqrt K hK hOutA,
    modular_power_quadratic hOutA (krausAction_posSemidef K hB),
    modular_power_quadratic hA hB] at h
  simpa only [sub_sub_cancel] using sub_nonneg.mp h

theorem petzTrace_le_kraus_of_posDef_input {Kappa : Type*} [Fintype Kappa]
    (K : Kappa → Matrix O I ℂ) (hK : krausGram K = 1)
    {A B : CMat I} (hA : A.PosDef) (hB : B.PosSemidef) {alpha : ℝ}
    (hAlpha0 : 0 < alpha) (hAlpha1 : alpha < 1) :
    petzTrace A B alpha ≤ petzTrace (krausAction K A) (krausAction K B) alpha := by
  classical
  let L := OutputSupport.compressedKraus K (Matrix.PosDef.one : (1 : CMat I).PosDef)
  have hL : krausGram L = 1 := OutputSupport.compressedKraus_gram K hK Matrix.PosDef.one
  have hOne : (krausAction L (1 : CMat I)).PosDef :=
    OutputSupport.compressedKraus_comparator_posDef K Matrix.PosDef.one
  have hOutA : (krausAction L A).PosDef := krausAction_posDef_of_one L hOne hA
  have h := petzTrace_le_kraus_of_posDef L hL hA hB hOutA hAlpha0 hAlpha1
  have heq : petzTrace (krausAction K A) (krausAction K B) alpha =
      petzTrace (krausAction L A) (krausAction L B) alpha := by
    rw [OutputSupport.krausAction_reconstruct K Matrix.PosDef.one A,
      OutputSupport.krausAction_reconstruct K Matrix.PosDef.one B]
    exact petzTrace_extend _ (OutputSupport.krausSupportIsometry_gram K Matrix.PosDef.one)
      (krausAction_posSemidef L hA.posSemidef).1 (krausAction_posSemidef L hB).1 hAlpha0 hAlpha1
  exact h.trans heq.ge

theorem petzTrace_le_kraus {Kappa : Type*} [Fintype Kappa]
    (K : Kappa → Matrix O I ℂ) (hK : krausGram K = 1)
    {A B : CMat I} (hA : A.PosSemidef) (hB : B.PosSemidef) {alpha : ℝ}
    (hAlpha0 : 0 < alpha) (hAlpha1 : alpha < 1) :
    petzTrace A B alpha ≤ petzTrace (krausAction K A) (krausAction K B) alpha := by
  let Ae : ℝ → CMat I := fun eps => A + eps • (1 : CMat I)
  have hAe (eps : ℝ) (heps : 0 < eps) : (Ae eps).PosDef := by
    have hle : eps • (1 : CMat I) ≤ A + eps • (1 : CMat I) :=
      le_add_of_nonneg_left hA.nonneg
    exact Matrix.isStrictlyPositive_iff_posDef.mp
      ((Matrix.PosDef.one.smul heps).isStrictlyPositive.of_le hle)
  have hASeq : ∀ᶠ eps : ℝ in 𝓝[>] 0, (Ae eps).PosSemidef := by
    filter_upwards [self_mem_nhdsWithin] with eps heps
    exact (hAe eps heps).posSemidef
  have hALim : Tendsto Ae (𝓝[>] (0 : ℝ)) (𝓝 A) := by
    have hc : Continuous Ae := by dsimp [Ae]; fun_prop
    have h0 : Tendsto Ae (𝓝 (0 : ℝ)) (𝓝 A) := by
      simpa only [Ae, zero_smul, add_zero] using hc.tendsto 0
    exact h0.mono_left nhdsWithin_le_nhds
  have hInput := petzTrace_tendsto_of_psd hA hB hASeq
    (Eventually.of_forall fun _ : ℝ => hB) hALim tendsto_const_nhds hAlpha0 hAlpha1
  have hMap : Continuous (krausAction K) := by
    unfold krausAction
    fun_prop
  have hOutput := petzTrace_tendsto_of_psd (krausAction_posSemidef K hA)
    (krausAction_posSemidef K hB)
    (hASeq.mono fun eps h => krausAction_posSemidef K h)
    (Eventually.of_forall fun _ : ℝ => krausAction_posSemidef K hB)
    ((hMap.tendsto A).comp hALim) tendsto_const_nhds hAlpha0 hAlpha1
  apply le_of_tendsto_of_tendsto hInput hOutput
  filter_upwards [self_mem_nhdsWithin] with eps heps
  exact petzTrace_le_kraus_of_posDef_input K hK (hAe eps heps) hB hAlpha0 hAlpha1

end QuantumProver.PetzModularPower

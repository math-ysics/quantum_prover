import Mathlib
import QuantumProver.LinearAlgebra.SandwichedDPI.OperatorNorm
import QuantumProver.InformationTheory.QuantumEntropy.PartialTraceKraus

set_option autoImplicit false
noncomputable section
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix Matrix.Norms.L2Operator

namespace QuantumProver.SandwichedDPI

open QuantumProver.SuperchannelDiscrimination
open KrausCompletion CPSchwarz

def traceNorm {I : Type*} [Fintype I] [DecidableEq I]
    (X : Matrix I I ℂ) : ℝ := (CFC.abs X).trace.re

theorem traceNorm_eq_singularValueTrace {I : Type*} [Fintype I] [DecidableEq I]
    (X : Matrix I I ℂ) : traceNorm X = (CFC.sqrt (Xᴴ * X)).trace.re := by
  simp only [traceNorm, CFC.abs, Matrix.star_eq_conjTranspose]

theorem traceNorm_nonneg {I : Type*} [Fintype I] [DecidableEq I]
    (X : Matrix I I ℂ) : 0 ≤ traceNorm X :=
  (Complex.nonneg_iff.mp (CFC.abs_nonneg X).posSemidef.trace_nonneg).1
def polarUnitaryMatrix {S : Type*} [Fintype S] [DecidableEq S]
    (U : EuclideanSpace ℂ S ≃ₗᵢ[ℂ] EuclideanSpace ℂ S) : Matrix S S ℂ :=
  Matrix.toEuclideanLin.symm U.toLinearEquiv.toLinearMap

theorem polarUnitaryMatrix_action {S : Type*} [Fintype S] [DecidableEq S]
    (U : EuclideanSpace ℂ S ≃ₗᵢ[ℂ] EuclideanSpace ℂ S)
    (v : EuclideanSpace ℂ S) : (polarUnitaryMatrix U).toEuclideanLin v = U v := by
  simp only [polarUnitaryMatrix, LinearEquiv.apply_symm_apply] <;> rfl

theorem polarUnitaryMatrix_mem_unitary {S : Type*} [Fintype S] [DecidableEq S]
    (U : EuclideanSpace ℂ S ≃ₗᵢ[ℂ] EuclideanSpace ℂ S) :
    polarUnitaryMatrix U ∈ Matrix.unitaryGroup S ℂ := by
  change U.toMatrix (EuclideanSpace.basisFun S ℂ).toBasis
    (EuclideanSpace.basisFun S ℂ).toBasis ∈ Matrix.unitaryGroup S ℂ
  exact U.toMatrix_mem_unitaryGroup (EuclideanSpace.basisFun S ℂ)
    (EuclideanSpace.basisFun S ℂ)

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]

theorem norm_eq_of_gram (f g : E →ₗ[ℂ] F)
    (hGram : f.adjoint.comp f = g.adjoint.comp g) (v : E) : ‖f v‖ = ‖g v‖ := by
  have hInner : inner ℂ (f v) (f v) = inner ℂ (g v) (g v) := by
    calc
      _ = inner ℂ v ((f.adjoint.comp f) v) :=
        (LinearMap.adjoint_inner_right f v (f v)).symm
      _ = inner ℂ v ((g.adjoint.comp g) v) := by rw [hGram]
      _ = _ := LinearMap.adjoint_inner_right g v (g v)
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), norm_eq_sqrt_re_inner (𝕜 := ℂ), hInner]

theorem ker_le_of_norm_eq (f g : E →ₗ[ℂ] F)
    (hNorm : ∀ v, ‖f v‖ = ‖g v‖) : f.ker ≤ g.ker := by
  intro v hv
  rw [LinearMap.mem_ker] at hv ⊢
  have h := hNorm v
  rw [hv, norm_zero] at h
  exact norm_eq_zero.mp h.symm

def rangeFactor (f g : E →ₗ[ℂ] F) (hKer : f.ker ≤ g.ker) : f.range →ₗ[ℂ] F :=
  (f.ker.liftQ g hKer).comp f.quotKerEquivRange.symm.toLinearMap

theorem rangeFactor_apply (f g : E →ₗ[ℂ] F) (hKer : f.ker ≤ g.ker) (v : E) :
    rangeFactor f g hKer (f.rangeRestrict v) = g v := by
  change f.ker.liftQ g hKer
    (f.quotKerEquivRange.symm ⟨f v, LinearMap.mem_range_self f v⟩) = g v
  rw [LinearMap.quotKerEquivRange_symm_apply_image]
  rfl

def rangeIsometry (f g : E →ₗ[ℂ] F) (hNorm : ∀ v, ‖f v‖ = ‖g v‖) :
    f.range →ₗᵢ[ℂ] F where
  toLinearMap := rangeFactor f g (ker_le_of_norm_eq f g hNorm)
  norm_map' u := by
    rcases u with ⟨u, hu⟩
    rcases hu with ⟨v, rfl⟩
    change ‖rangeFactor f g (ker_le_of_norm_eq f g hNorm) (f.rangeRestrict v)‖ = ‖f v‖
    rw [rangeFactor_apply]
    exact (hNorm v).symm

theorem rangeIsometry_apply (f g : E →ₗ[ℂ] F)
    (hNorm : ∀ v, ‖f v‖ = ‖g v‖) (v : E) :
    rangeIsometry f g hNorm (f.rangeRestrict v) = g v :=
  rangeFactor_apply f g (ker_le_of_norm_eq f g hNorm) v

theorem exists_shield_unitary_of_norm_eq (f g : E →ₗ[ℂ] F)
    (hNorm : ∀ v, ‖f v‖ = ‖g v‖) :
    ∃ U : F ≃ₗᵢ[ℂ] F, ∀ v : E, U (f v) = g v := by
  let L := rangeIsometry f g hNorm
  let V := L.extend
  have hSurj : Function.Surjective V :=
    LinearMap.injective_iff_surjective.mp V.injective
  let U := LinearIsometryEquiv.ofSurjective V hSurj
  refine ⟨U, ?_⟩
  intro v
  change V (f v) = g v
  calc
    _ = L (f.rangeRestrict v) := L.extend_apply (f.rangeRestrict v)
    _ = g v := rangeIsometry_apply f g hNorm v

theorem exists_shield_unitary_of_gram (f g : E →ₗ[ℂ] F)
    (hGram : f.adjoint.comp f = g.adjoint.comp g) :
    ∃ U : F ≃ₗᵢ[ℂ] F, ∀ v : E, U (f v) = g v :=
  exists_shield_unitary_of_norm_eq f g (norm_eq_of_gram f g hGram)

section Matrix

variable {S J : Type*} [Fintype S] [Fintype J] [DecidableEq S] [DecidableEq J]

theorem toEuclideanLin_mul (A : Matrix S S ℂ) (B : Matrix S J ℂ) :
    (A * B).toEuclideanLin = A.toEuclideanLin.comp B.toEuclideanLin := by
  change (A * B).toLin (EuclideanSpace.basisFun J ℂ).toBasis
      (EuclideanSpace.basisFun S ℂ).toBasis =
    (A.toLin (EuclideanSpace.basisFun S ℂ).toBasis
      (EuclideanSpace.basisFun S ℂ).toBasis).comp
    (B.toLin (EuclideanSpace.basisFun J ℂ).toBasis
      (EuclideanSpace.basisFun S ℂ).toBasis)
  exact Matrix.toLin_mul _ _ _ A B

theorem toEuclideanLin_gram (A : Matrix S J ℂ) :
    (Aᴴ * A).toEuclideanLin = A.toEuclideanLin.adjoint.comp A.toEuclideanLin := by
  rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
  exact Matrix.toLin_mul (EuclideanSpace.basisFun J ℂ).toBasis
    (EuclideanSpace.basisFun S ℂ).toBasis (EuclideanSpace.basisFun J ℂ).toBasis Aᴴ A

theorem exists_unitary_matrix_of_equal_gram (A B : Matrix S J ℂ)
    (hGram : Aᴴ * A = Bᴴ * B) :
    ∃ U : Matrix S S ℂ, U ∈ Matrix.unitaryGroup S ℂ ∧ U * A = B := by
  have hLin : A.toEuclideanLin.adjoint.comp A.toEuclideanLin =
      B.toEuclideanLin.adjoint.comp B.toEuclideanLin := by
    rw [← toEuclideanLin_gram, ← toEuclideanLin_gram, hGram]
  obtain ⟨W, hW⟩ := exists_shield_unitary_of_gram A.toEuclideanLin B.toEuclideanLin hLin
  refine ⟨polarUnitaryMatrix W, polarUnitaryMatrix_mem_unitary W, ?_⟩
  apply Matrix.toEuclideanLin.injective
  rw [toEuclideanLin_mul]
  apply LinearMap.ext
  intro v
  change (polarUnitaryMatrix W).toEuclideanLin (A.toEuclideanLin v) = B.toEuclideanLin v
  rw [polarUnitaryMatrix_action]
  exact hW v

end Matrix

section Polar

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem exists_unitary_polar (M : Matrix I I ℂ) :
    ∃ U : Matrix I I ℂ, U ∈ Matrix.unitaryGroup I ℂ ∧ U * M = CFC.abs M := by
  have hAbs : (CFC.abs M)ᴴ = CFC.abs M := (CFC.abs_nonneg M).posSemidef.isHermitian
  have hGram : Mᴴ * M = (CFC.abs M)ᴴ * CFC.abs M := by
    rw [hAbs]
    simpa only [star_eq_conjTranspose] using (CFC.abs_mul_abs M).symm
  exact exists_unitary_matrix_of_equal_gram M (CFC.abs M) hGram

theorem exists_unitary_traceNorm_attainer (M : Matrix I I ℂ) :
    ∃ U : Matrix I I ℂ, U ∈ Matrix.unitaryGroup I ℂ ∧
      (U * M).trace.re = traceNorm M := by
  obtain ⟨U, hU, hUM⟩ := exists_unitary_polar M
  exact ⟨U, hU, by rw [hUM]; rfl⟩

theorem re_trace_isometry_mul_le {S H : Matrix I I ℂ}
    (hS : Sᴴ * S = 1) (hH : H.PosSemidef) :
    (S * H).trace.re ≤ H.trace.re := by
  let R := CFC.sqrt H
  have hR : Rᴴ = R := (CFC.sqrt_nonneg H).posSemidef.isHermitian
  have hRR : R * R = H := CFC.sqrt_mul_sqrt_self H hH.nonneg
  have hHH : Hᴴ = H := hH.isHermitian
  have hExpand : (1 - S)ᴴ * (1 - S) = 1 + 1 - Sᴴ - S := by
    simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_one,
      Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hS]
    noncomm_ring
  let Z := (1 - S) * R
  have hGram : Zᴴ * Z = H + H - R * Sᴴ * R - R * S * R := by
    calc
      _ = R * ((1 - S)ᴴ * (1 - S)) * R := by
        simp only [Z, Matrix.conjTranspose_mul, hR, Matrix.mul_assoc]
      _ = _ := by
        rw [hExpand]
        simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_add,
          Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, hRR]
  have hCycle (A : Matrix I I ℂ) : (R * A * R).trace = (A * H).trace := by
    rw [Matrix.trace_mul_cycle, hRR, Matrix.trace_mul_comm]
  have hStar : (Sᴴ * H).trace.re = (S * H).trace.re := by
    have ht : (Sᴴ * H).trace = star (S * H).trace := by
      rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, hHH]
      exact Matrix.trace_mul_comm _ _
    rw [ht]
    simp
  have hp : 0 ≤ (Zᴴ * Z).trace.re :=
    (Complex.nonneg_iff.mp (Matrix.posSemidef_conjTranspose_mul_self Z).trace_nonneg).1
  rw [hGram, Matrix.trace_sub, Matrix.trace_sub, Matrix.trace_add,
    hCycle Sᴴ, hCycle S] at hp
  simp only [Complex.sub_re, Complex.add_re, hStar] at hp
  linarith

theorem re_trace_unitary_mul_le_traceNorm (M V : Matrix I I ℂ)
    (hV : V ∈ Matrix.unitaryGroup I ℂ) : (V * M).trace.re ≤ traceNorm M := by
  obtain ⟨U, hU, hUM⟩ := exists_unitary_polar M
  have hU1 : Uᴴ * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hU
  have hU2 : U * Uᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hU
  have hV1 : Vᴴ * V = 1 := Matrix.mem_unitaryGroup_iff'.mp hV
  have hM : M = Uᴴ * CFC.abs M := by
    rw [← hUM, ← Matrix.mul_assoc, hU1, Matrix.one_mul]
  have hS : (V * Uᴴ)ᴴ * (V * Uᴴ) = 1 := by
    calc
      _ = U * (Vᴴ * V) * Uᴴ := by
        simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
          Matrix.mul_assoc]
      _ = 1 := by rw [hV1, Matrix.mul_one, hU2]
  have hBound := re_trace_isometry_mul_le hS (CFC.abs_nonneg M).posSemidef
  change (V * M).trace.re ≤ (CFC.abs M).trace.re
  calc
    _ = (V * (Uᴴ * CFC.abs M)).trace.re :=
      congrArg (fun N : Matrix I I ℂ => (V * N).trace.re) hM
    _ ≤ _ := by simpa only [Matrix.mul_assoc] using hBound

end Polar

section Contraction

variable {I O Z : Type*} [Fintype I] [DecidableEq I]
  [Fintype O] [DecidableEq O] [Fintype Z]

theorem re_trace_contraction_mul_le {S H : Matrix I I ℂ}
    (hS : (1 - Sᴴ * S).PosSemidef) (hH : H.PosSemidef) :
    (S * H).trace.re ≤ H.trace.re := by
  let R := CFC.sqrt H
  let W := (1 - S) * R
  have hR : Rᴴ = R := (CFC.sqrt_nonneg H).posSemidef.1.eq
  have hRR : R * R = H := CFC.sqrt_mul_sqrt_self H hH.nonneg
  have hp := (Matrix.posSemidef_conjTranspose_mul_self W).add
    (hS.mul_mul_conjTranspose_same R)
  have he : Wᴴ * W + R * (1 - Sᴴ * S) * Rᴴ =
      H + H - R * Sᴴ * R - R * S * R := by
    simp only [W, Matrix.conjTranspose_mul, hR, Matrix.conjTranspose_sub,
      Matrix.conjTranspose_one]
    rw [← hRR]
    noncomm_ring
  rw [he] at hp
  have htrace : 0 ≤ (H + H - R * Sᴴ * R - R * S * R).trace.re :=
    (Complex.nonneg_iff.mp hp.trace_nonneg).1
  have hcycle (A : Matrix I I ℂ) : (R * A * R).trace = (A * H).trace := by
    rw [Matrix.trace_mul_cycle, hRR, Matrix.trace_mul_comm]
  have hstar : (Sᴴ * H).trace.re = (S * H).trace.re := by
    have ht : (Sᴴ * H).trace = star (S * H).trace := by
      rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, hH.1.eq]
      exact Matrix.trace_mul_comm _ _
    rw [ht]
    simp
  rw [Matrix.trace_sub, Matrix.trace_sub, Matrix.trace_add,
    hcycle Sᴴ, hcycle S] at htrace
  simp only [Complex.sub_re, Complex.add_re, hstar] at htrace
  linarith

theorem re_trace_mul_le_traceNorm_of_contraction (M S : Matrix I I ℂ)
    (hS : (1 - Sᴴ * S).PosSemidef) : (S * M).trace.re ≤ traceNorm M := by
  obtain ⟨U, hU, hUM⟩ := exists_unitary_polar M
  have hU1 : Uᴴ * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hU
  have hU2 : U * Uᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hU
  have hM : M = Uᴴ * CFC.abs M := by
    rw [← hUM, ← Matrix.mul_assoc, hU1, Matrix.one_mul]
  have hT : (1 - (S * Uᴴ)ᴴ * (S * Uᴴ)).PosSemidef := by
    have h := hS.mul_mul_conjTranspose_same U
    have he : U * (1 - Sᴴ * S) * Uᴴ = 1 - (S * Uᴴ)ᴴ * (S * Uᴴ) := by
      simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one,
        Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
      rw [hU2]
      noncomm_ring
    rwa [he] at h
  calc
    (S * M).trace.re = (S * (Uᴴ * CFC.abs M)).trace.re :=
      congrArg (fun N : Matrix I I ℂ => (S * N).trace.re) hM
    _ = ((S * Uᴴ) * CFC.abs M).trace.re := by rw [Matrix.mul_assoc]
    _ ≤ (CFC.abs M).trace.re :=
      re_trace_contraction_mul_le hT (CFC.abs_nonneg M).posSemidef

theorem traceNorm_krausAction_le (K : Z → Matrix O I ℂ)
    (hK : krausGram K = 1) (X : Matrix I I ℂ) :
    traceNorm (krausAction K X) ≤ traceNorm X := by
  obtain ⟨V, hV, htrace⟩ := exists_unitary_traceNorm_attainer (krausAction K X)
  have hV1 : Vᴴ * V = 1 := Matrix.mem_unitaryGroup_iff'.mp hV
  have hS := adjointKrausMap_schwarz K hK V
  rw [hV1, adjointKrausMap_unital K hK] at hS
  calc
    traceNorm (krausAction K X) = (V * krausAction K X).trace.re := htrace.symm
    _ = (adjointKrausMap K V * X).trace.re := by
      rw [Matrix.trace_mul_comm V, trace_kraus_adjoint K X V,
        Matrix.trace_mul_comm X]
    _ ≤ traceNorm X := re_trace_mul_le_traceNorm_of_contraction X _ hS

theorem traceNorm_map_le_of_cp_tracePreserving
    {Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ}
    (hΦ : CPWrappers.CompletelyPositive Φ) (htrace : CPTPKraus.TracePreserving Φ)
    (X : Matrix I I ℂ) : traceNorm (Φ X) ≤ traceNorm X := by
  have hK : krausGram (CPTPKraus.canonicalKraus Φ) = 1 :=
    CPTPKraus.canonicalKraus_gram Φ hΦ htrace
  have hact : Φ X = krausAction (CPTPKraus.canonicalKraus Φ) X :=
    CPTPKraus.canonicalKraus_reconstruct Φ hΦ X
  rw [hact]
  exact traceNorm_krausAction_le (CPTPKraus.canonicalKraus Φ) hK X

theorem contraction_deficit_of_norm_le_one {S : Matrix I I ℂ} (hS : ‖S‖ ≤ 1) :
    (1 - Sᴴ * S).PosSemidef := by
  have hnorm : ‖Sᴴ * S‖ ≤ 1 := by
    rw [← Matrix.star_eq_conjTranspose, CStarRing.norm_star_mul_self]
    nlinarith [norm_nonneg S]
  exact Matrix.le_iff.mp
    ((CStarAlgebra.norm_le_one_iff_of_nonneg (Sᴴ * S)
      (Matrix.posSemidef_conjTranspose_mul_self S).nonneg).mp hnorm)

private theorem exists_complex_phase (z : ℂ) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ (c * z).re = ‖z‖ := by
  by_cases hz : z = 0
  · exact ⟨1, by simp, by simp [hz]⟩
  · have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
    let c : ℂ := star z / (‖z‖ : ℂ)
    refine ⟨c, ?_, ?_⟩
    · simp only [c, norm_div, norm_star, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (norm_nonneg z), div_self hn]
    · change ((star z / (‖z‖ : ℂ)) * z).re = ‖z‖
      rw [div_mul_eq_mul_div]
      have hs : star z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
        simpa only [Complex.star_def, Complex.normSq_eq_norm_sq] using
          (Complex.normSq_eq_conj_mul_self (z := z)).symm
      rw [hs, ← Complex.ofReal_div, Complex.ofReal_re]
      rw [pow_two, mul_div_cancel_right₀ _ hn]

theorem norm_trace_mul_le_traceNorm (S X : Matrix I I ℂ) (hS : ‖S‖ ≤ 1) :
    ‖(S * X).trace‖ ≤ traceNorm X := by
  obtain ⟨c, hc, hphase⟩ := exists_complex_phase (S * X).trace
  have hn : ‖c • S‖ ≤ 1 := by simpa only [norm_smul, hc, one_mul] using hS
  have h := re_trace_mul_le_traceNorm_of_contraction X (c • S)
    (contraction_deficit_of_norm_le_one hn)
  simpa only [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, hphase] using h

theorem traceNorm_mul_left_le (S X : Matrix I I ℂ) (hS : ‖S‖ ≤ 1) :
    traceNorm (S * X) ≤ traceNorm X := by
  obtain ⟨V, hV, htrace⟩ := exists_unitary_traceNorm_attainer (S * X)
  have hV1 : Vᴴ * V = 1 := Matrix.mem_unitaryGroup_iff'.mp hV
  have he : 1 - (V * S)ᴴ * (V * S) = 1 - Sᴴ * S := by
    simp only [Matrix.conjTranspose_mul]
    calc
      _ = 1 - Sᴴ * (Vᴴ * V) * S := by noncomm_ring
      _ = _ := by rw [hV1, Matrix.mul_one]
  have hVS : (1 - (V * S)ᴴ * (V * S)).PosSemidef := by
    rw [he]
    exact contraction_deficit_of_norm_le_one hS
  calc
    traceNorm (S * X) = (V * (S * X)).trace.re := htrace.symm
    _ = ((V * S) * X).trace.re := by rw [Matrix.mul_assoc]
    _ ≤ traceNorm X := re_trace_mul_le_traceNorm_of_contraction X _ hVS

theorem traceNorm_mul_right_le (X S : Matrix I I ℂ) (hS : ‖S‖ ≤ 1) :
    traceNorm (X * S) ≤ traceNorm X := by
  obtain ⟨V, hV, htrace⟩ := exists_unitary_traceNorm_attainer (X * S)
  have hV1 : Vᴴ * V = 1 := Matrix.mem_unitaryGroup_iff'.mp hV
  have h := (contraction_deficit_of_norm_le_one hS).conjTranspose_mul_mul_same V
  have he : Vᴴ * (1 - Sᴴ * S) * V = 1 - (S * V)ᴴ * (S * V) := by
    simp only [Matrix.conjTranspose_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one]
    rw [hV1]
    noncomm_ring
  rw [he] at h
  calc
    traceNorm (X * S) = (V * (X * S)).trace.re := htrace.symm
    _ = ((S * V) * X).trace.re := by
      rw [← Matrix.mul_assoc, Matrix.trace_mul_cycle, Matrix.mul_assoc]
    _ ≤ traceNorm X := re_trace_mul_le_traceNorm_of_contraction X _ h

def weightedTraceNorm (σ X : Matrix I I ℂ) : ℝ :=
  traceNorm (CFC.sqrt σ * X * CFC.sqrt σ)

end Contraction

section SingularWeighted

open FlaggedStates TensorEntropy OutputSupport

variable {I O Z : Type*} [Fintype I] [DecidableEq I]
  [Fintype O] [DecidableEq O] [Fintype Z]

theorem sqrt_mul_inverse_sqrt_eq_supportProjection {A : Matrix O O ℂ}
    (hA : A.PosSemidef) :
    CFC.sqrt A * CFC.rpow A (-1 / 2 : ℝ) = supportProjection A := by
  have hroot : CFC.sqrt A = cfc (fun x : ℝ => x ^ (1 / 2 : ℝ)) A := by
    calc
      CFC.sqrt A = CFC.rpow A (1 / 2 : ℝ) := CFC.sqrt_eq_rpow
      _ = _ := CFC.rpow_eq_cfc_real (A := Matrix O O ℂ) (a := A)
        (y := (1 / 2 : ℝ)) hA.nonneg
  have hinv : CFC.rpow A (-1 / 2 : ℝ) =
      cfc (fun x : ℝ => x ^ (-1 / 2 : ℝ)) A :=
    CFC.rpow_eq_cfc_real (A := Matrix O O ℂ) (a := A) (y := (-1 / 2 : ℝ)) hA.nonneg
  rw [hroot, hinv]
  rw [← cfc_mul (p := IsSelfAdjoint) _ _ A
    (A.finite_real_spectrum.continuousOn _) (A.finite_real_spectrum.continuousOn _)]
  unfold supportProjection
  apply cfc_congr
  intro x hx
  have hx0 : 0 ≤ x := by
    obtain ⟨i, rfl⟩ := hA.1.spectrum_real_eq_range_eigenvalues ▸ hx
    exact hA.eigenvalues_nonneg i
  by_cases hz : x = 0
  · norm_num [hz, nonzeroWeight]
  · have hxpos : 0 < x := lt_of_le_of_ne hx0 (Ne.symm hz)
    change x ^ (1 / 2 : ℝ) * x ^ (-1 / 2 : ℝ) = nonzeroWeight x
    rw [← Real.rpow_add hxpos]
    norm_num [nonzeroWeight, hz]

theorem inverse_sqrt_mul_sqrt_eq_supportProjection {A : Matrix O O ℂ}
    (hA : A.PosSemidef) :
    CFC.rpow A (-1 / 2 : ℝ) * CFC.sqrt A = supportProjection A := by
  have h := congrArg Matrix.conjTranspose (sqrt_mul_inverse_sqrt_eq_supportProjection hA)
  have hroot : (CFC.sqrt A)ᴴ = CFC.sqrt A := (CFC.sqrt_nonneg A).posSemidef.isHermitian
  have hinv : (CFC.rpow A (-1 / 2 : ℝ))ᴴ = CFC.rpow A (-1 / 2 : ℝ) :=
    (CFC.rpow_nonneg : 0 ≤ CFC.rpow A (-1 / 2 : ℝ)).posSemidef.isHermitian
  simpa only [Matrix.conjTranspose_mul, hroot, hinv,
    (supportProjection_isHermitian hA.1).eq] using h

theorem sqrt_mulVec_eq_zero_of_mulVec_eq_zero {σ : Matrix I I ℂ}
    (hσ : σ.PosSemidef) (v : I → ℂ) (hv : σ *ᵥ v = 0) :
    CFC.sqrt σ *ᵥ v = 0 := by
  apply (Matrix.conjTranspose_mul_self_mulVec_eq_zero (CFC.sqrt σ) v).mp
  rw [(CFC.sqrt_nonneg σ).posSemidef.1.eq, CFC.sqrt_mul_sqrt_self σ hσ.nonneg]
  exact hv

theorem supportProjection_mul_kraus_sqrt (K : Z → Matrix O I ℂ)
    {σ : Matrix I I ℂ} (hσ : σ.PosSemidef) (z : Z) :
    supportProjection (krausAction K σ) * (K z * CFC.sqrt σ) = K z * CFC.sqrt σ := by
  let τ := krausAction K σ
  let Q := 1 - supportProjection τ
  have hτ : τ.PosSemidef := krausAction_posSemidef K hσ
  have hQ : Qᴴ = Q := by
    simp only [Q, Matrix.conjTranspose_sub, Matrix.conjTranspose_one,
      (supportProjection_isHermitian hτ.1).eq]
  have hτQ : τ * Q = 0 := by
    change τ * (1 - supportProjection τ) = 0
    rw [Matrix.mul_sub, Matrix.mul_one, supportProjection_mul τ hτ.1, sub_self]
  have hz : (K z * CFC.sqrt σ)ᴴ * Q = 0 := by
    apply Matrix.ext_iff_mulVec.mpr
    intro v
    have hv : τ *ᵥ (Q *ᵥ v) = 0 := by
      rw [Matrix.mulVec_mulVec, hτQ, Matrix.zero_mulVec]
    have hkernel := QuantumProver.QuantumEntropy.kraus_lift_kernel K hσ (Q *ᵥ v) hv z
    have hroot := sqrt_mulVec_eq_zero_of_mulVec_eq_zero hσ _ hkernel
    simpa only [Matrix.conjTranspose_mul, (CFC.sqrt_nonneg σ).posSemidef.1.eq,
      ← Matrix.mulVec_mulVec, Matrix.zero_mulVec] using hroot
  have hleft := congrArg Matrix.conjTranspose hz
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hQ,
    Matrix.conjTranspose_zero] at hleft
  change (1 - supportProjection τ) * (K z * CFC.sqrt σ) = 0 at hleft
  rw [Matrix.sub_mul, Matrix.one_mul] at hleft
  exact (sub_eq_zero.mp hleft).symm

theorem kraus_sandwich_support (K : Z → Matrix O I ℂ)
    {σ : Matrix I I ℂ} (hσ : σ.PosSemidef) (X : Matrix I I ℂ) :
    supportProjection (krausAction K σ) *
      krausAction K (CFC.sqrt σ * X * CFC.sqrt σ) *
        supportProjection (krausAction K σ) =
      krausAction K (CFC.sqrt σ * X * CFC.sqrt σ) := by
  let P := supportProjection (krausAction K σ)
  have hP : Pᴴ = P :=
    (supportProjection_isHermitian (krausAction_posSemidef K hσ).1).eq
  have hL (z : Z) : P * (K z * CFC.sqrt σ) = K z * CFC.sqrt σ :=
    supportProjection_mul_kraus_sqrt K hσ z
  have hR (z : Z) : (K z * CFC.sqrt σ)ᴴ * P = (K z * CFC.sqrt σ)ᴴ := by
    have h := congrArg Matrix.conjTranspose (hL z)
    simpa only [Matrix.conjTranspose_mul, hP] using h
  change P * (∑ z, K z * (CFC.sqrt σ * X * CFC.sqrt σ) * (K z)ᴴ) * P = _
  simp only [krausAction, Matrix.mul_sum, Matrix.sum_mul]
  apply Finset.sum_congr rfl
  intro z _
  have he : K z * (CFC.sqrt σ * X * CFC.sqrt σ) * (K z)ᴴ =
      (K z * CFC.sqrt σ) * X * (K z * CFC.sqrt σ)ᴴ := by
    simp only [Matrix.conjTranspose_mul, (CFC.sqrt_nonneg σ).posSemidef.1.eq,
      Matrix.mul_assoc]
  rw [he]
  calc
    P * ((K z * CFC.sqrt σ) * X * (K z * CFC.sqrt σ)ᴴ) * P =
        (P * (K z * CFC.sqrt σ)) * X * ((K z * CFC.sqrt σ)ᴴ * P) := by
      simp only [Matrix.mul_assoc]
    _ = _ := by rw [hL z, hR z]

theorem sqrt_normalizedKraus_action_sqrt (K : Z → Matrix O I ℂ)
    {σ : Matrix I I ℂ} (hσ : σ.PosSemidef) (X : Matrix I I ℂ) :
    CFC.sqrt (krausAction K σ) * krausAction (normalizedKraus K σ) X *
        CFC.sqrt (krausAction K σ) =
      krausAction K (CFC.sqrt σ * X * CFC.sqrt σ) := by
  rw [normalizedKraus_action]
  calc
    _ = (CFC.sqrt (krausAction K σ) * CFC.rpow (krausAction K σ) (-1 / 2 : ℝ)) *
        krausAction K (CFC.sqrt σ * X * CFC.sqrt σ) *
          (CFC.rpow (krausAction K σ) (-1 / 2 : ℝ) * CFC.sqrt (krausAction K σ)) := by
      noncomm_ring
    _ = _ := by
      rw [sqrt_mul_inverse_sqrt_eq_supportProjection (krausAction_posSemidef K hσ),
        inverse_sqrt_mul_sqrt_eq_supportProjection (krausAction_posSemidef K hσ)]
      exact kraus_sandwich_support K hσ X

theorem weightedTraceNorm_normalizedKraus_action_le (K : Z → Matrix O I ℂ)
    (hK : krausGram K = 1) {σ : Matrix I I ℂ} (hσ : σ.PosSemidef)
    (X : Matrix I I ℂ) :
    weightedTraceNorm (krausAction K σ) (krausAction (normalizedKraus K σ) X) ≤
      weightedTraceNorm σ X := by
  unfold weightedTraceNorm
  rw [sqrt_normalizedKraus_action_sqrt K hσ X]
  exact traceNorm_krausAction_le K hK _

end SingularWeighted

end QuantumProver.SandwichedDPI

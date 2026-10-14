import QuantumProver.LinearAlgebra.SandwichedDPI.TraceNorm
import QuantumProver.LinearAlgebra.MatrixSqrt.Derivatives
import QuantumProver.LinearAlgebra.UnitarySecondMoment

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

noncomputable section
open Matrix MeasureTheory Filter Set
open scoped Topology BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker

namespace QuantumProver.QuantumDecoupling

open QuantumProver.MatrixAnalysis.MatrixSqrt
open QuantumProver.SandwichedDPI (traceNorm)
open QuantumProver.SuperchannelDiscrimination.FlaggedStates (HasSupportIn IsDensity)
open QuantumProver.SuperchannelDiscrimination.TensorEntropy

variable {I J R : Type*} [Fintype I] [Fintype J] [Fintype R]
  [DecidableEq I] [DecidableEq J] [DecidableEq R]

def hsSq (X : Matrix I I ℂ) : ℝ := (Xᴴ * X).trace.re

omit [DecidableEq I] in
theorem hsSq_nonneg (X : Matrix I I ℂ) : 0 ≤ hsSq X :=
  (Complex.nonneg_iff.mp (Matrix.posSemidef_conjTranspose_mul_self X).trace_nonneg).1

theorem hsNorm_isometry_mul (U X : Matrix I I ℂ) (hU : Uᴴ * U = 1) :
    hsNorm (U * X) = hsNorm X := by
  have hGram : (U*X)ᴴ*(U*X) = Xᴴ*X := by
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Uᴴ U X, hU, Matrix.one_mul]
  unfold hsNorm
  rw [hGram]

theorem traceNorm_mul_le_hs (X Y : Matrix I I ℂ) :
    traceNorm (X*Y) ≤ hsNorm X * hsNorm Y := by
  obtain ⟨U, hU, hTrace⟩ := QuantumProver.SandwichedDPI.exists_unitary_traceNorm_attainer (X*Y)
  have hGram : Uᴴ*U = 1 := Matrix.mem_unitaryGroup_iff'.mp hU
  calc
    _ = (U*(X*Y)).trace.re := hTrace.symm
    _ ≤ hsNorm (U*X) * hsNorm Y := by
      simpa only [Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc, hsNorm_conjTranspose]
        using hs_trace_pair_le (U*X)ᴴ Y
    _ = _ := by rw [hsNorm_isometry_mul U X hGram]

theorem projection_trace_eq_rank {P : Matrix I I ℂ} (hP : P*P = P) :
    P.trace = (P.rank : ℂ) := by
  have hIdem : IsIdempotentElem P.toLin' := by
    change P.toLin'.comp P.toLin' = P.toLin'
    rw [← Matrix.toLin'_mul, hP]
  have hRank : P.rank = Module.finrank ℂ (LinearMap.range P.toLin') := by
    simpa only [Matrix.toLin_eq_toLin'] using
      P.rank_eq_finrank_range_toLin (Pi.basisFun ℂ I) (Pi.basisFun ℂ I)
  rw [hRank, ← Matrix.trace_toLin'_eq]
  exact ((LinearMap.isProj_range_iff_isIdempotentElem P.toLin').mpr hIdem).trace

theorem supportProjection_rank {S : Matrix I I ℂ} (hS : S.IsHermitian) :
    (supportProjection S).rank = S.rank := by
  apply le_antisymm
  · rw [supportProjection_eq_inverse_mul S hS]
    exact Matrix.rank_mul_le_right _ _
  · conv_lhs => rw [← supportProjection_mul S hS]
    exact Matrix.rank_mul_le_right _ _

theorem traceNorm_supported_sq_le {X P : Matrix I I ℂ}
    (hPH : P.IsHermitian) (hPP : P*P = P) (hXP : X*P = X) :
    traceNorm X ^ 2 ≤ (P.rank : ℝ) * hsSq X := by
  have h := traceNorm_mul_le_hs X P
  rw [hXP] at h
  have hPN : hsNorm P ^ 2 = (P.rank : ℝ) := by
    rw [hsNorm_sq, hPH.eq, hPP, projection_trace_eq_rank hPP]
    simp
  have hX : hsNorm X ^ 2 = hsSq X := hsNorm_sq X
  have hSq := pow_le_pow_left₀ (QuantumProver.SandwichedDPI.traceNorm_nonneg X) h 2
  rw [mul_pow, hPN, hX] at hSq
  simpa only [mul_comm] using hSq

theorem traceNorm_support_rank_sq_le {X S : Matrix I I ℂ}
    (hS : S.IsHermitian) (hs : HasSupportIn X S) :
    traceNorm X ^ 2 ≤ (S.rank : ℝ) * hsSq X := by
  have h := traceNorm_supported_sq_le
    (QuantumProver.SuperchannelDiscrimination.OutputSupport.supportProjection_isHermitian hS)
    (QuantumProver.SuperchannelDiscrimination.OutputSupport.supportProjection_idempotent hS)
    ((hasSupportIn_iff_mul_supportProjection hS).mp hs)
  simpa only [supportProjection_rank hS] using h

theorem traceNorm_weighted_sq_le {X S : Matrix I I ℂ}
    (hS : S.PosSemidef) (hs : HasSupportIn X S) :
    traceNorm X ^ 2 ≤ S.trace.re * hsSq (X*CFC.rpow S (-1/2 : ℝ)) := by
  have hFactor : (X*CFC.rpow S (-1/2 : ℝ))*CFC.sqrt S = X := by
    rw [Matrix.mul_assoc, QuantumProver.SandwichedDPI.inverse_sqrt_mul_sqrt_eq_supportProjection hS]
    exact (hasSupportIn_iff_mul_supportProjection hS.1).mp hs
  have h := traceNorm_mul_le_hs (X*CFC.rpow S (-1/2 : ℝ)) (CFC.sqrt S)
  rw [hFactor] at h
  have hRoot : hsNorm (CFC.sqrt S)^2 = S.trace.re := by
    rw [hsNorm_sq, (CFC.sqrt_nonneg S).posSemidef.isHermitian.eq,
      CFC.sqrt_mul_sqrt_self S hS.nonneg]
  have hSq := pow_le_pow_left₀ (QuantumProver.SandwichedDPI.traceNorm_nonneg X) h 2
  rw [mul_pow, hRoot, hsNorm_sq] at hSq
  simpa only [hsSq, mul_comm] using hSq

section RegisterCharts

variable {K : Type*} [Fintype K] [DecidableEq K]

def partialRetain (e : I ≃ J × K) (X : Matrix I I ℂ) : Matrix K K ℂ :=
  fun k l => ∑ j : J, X (e.symm (j,k)) (e.symm (j,l))

def registerPartialSwap : Matrix ((J × K) × (J × K)) ((J × K) × (J × K)) ℂ :=
  fun x y =>
    (1 : Matrix J J ℂ) x.1.1 y.1.1 * (1 : Matrix J J ℂ) x.2.1 y.2.1 *
      (1 : Matrix K K ℂ) x.1.2 y.2.2 * (1 : Matrix K K ℂ) x.2.2 y.1.2

def partialSwap (e : I ≃ J × K) : Matrix (I × I) (I × I) ℂ :=
  registerPartialSwap.submatrix (fun x => (e x.1,e x.2)) (fun y => (e y.1,e y.2))

theorem registerPartialSwap_trace :
    (registerPartialSwap (J := J) (K := K)).trace =
      ((Fintype.card J : ℂ)^2 * (Fintype.card K : ℂ)) := by
  have hd (j j' : J) (k k' : K) :
      registerPartialSwap ((j,k),(j',k')) ((j,k),(j',k')) =
        if k = k' then (1 : ℂ) else 0 := by
    by_cases hk : k = k'
    · subst k'; simp [registerPartialSwap]
    · simp [registerPartialSwap, hk, Ne.symm hk]
  simp only [Matrix.trace, Matrix.diag, Fintype.sum_prod_type]
  simp_rw [hd]
  simp [pow_two, mul_assoc, mul_comm]

theorem registerPartialSwap_mixed_trace (X Y : Matrix (J × K) (J × K) ℂ) :
    ((X ⊗ₖ Y)*registerPartialSwap).trace =
      (QuantumProver.QuantumEntropy.partialTrace_left X * QuantumProver.QuantumEntropy.partialTrace_left Y).trace := by
  simp only [registerPartialSwap, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Fintype.sum_prod_type, Matrix.kroneckerMap_apply, QuantumProver.QuantumEntropy.partialTrace_left]
  simp only [Matrix.one_apply, mul_ite, mul_zero, mul_one]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_eq_left]
  simp only [Finset.sum_mul, Finset.mul_sum]
  conv_lhs =>
    rw [Finset.sum_comm]
    arg 2; ext k
    arg 2; ext j
    rw [Finset.sum_comm]
  conv_lhs =>
    arg 2; ext k
    rw [Finset.sum_comm]
  conv_lhs =>
    arg 2; ext k
    arg 2; ext l
    rw [Finset.sum_comm]

theorem replicaSwap_mul_left (M : Matrix (I × I) (I × I) ℂ)
    (ij kl : I × I) :
    (QuantumProver.WernerEndpoint.replicaSwap I * M) ij kl = M (ij.2,ij.1) kl :=
  QuantumProver.WernerEndpoint.replicaSwap_mulVec (fun x => M x kl) ij

theorem replicaSwap_mul_right (M : Matrix (I × I) (I × I) ℂ)
    (ij kl : I × I) :
    (M * QuantumProver.WernerEndpoint.replicaSwap I) ij kl = M ij (kl.2,kl.1) := by
  simp [Matrix.mul_apply, QuantumProver.WernerEndpoint.replicaSwap, mul_ite]

theorem kronecker_swap_trace (X Y : Matrix I I ℂ) :
    ((X ⊗ₖ Y) * QuantumProver.WernerEndpoint.replicaSwap I).trace = (X*Y).trace := by
  simp only [Matrix.trace, Matrix.diag, replicaSwap_mul_right]
  simp only [Fintype.sum_prod_type, Matrix.kroneckerMap_apply, Matrix.mul_apply]

theorem registerPartialSwap_swap_trace :
    (QuantumProver.WernerEndpoint.replicaSwap (J × K) * registerPartialSwap).trace =
      ((Fintype.card J : ℂ) * (Fintype.card K : ℂ)^2) := by
  have hd (j j' : J) (k k' : K) :
      registerPartialSwap ((j',k'),(j,k)) ((j,k),(j',k')) =
        if j = j' then (1 : ℂ) else 0 := by
    by_cases hj : j = j'
    · subst j'; simp [registerPartialSwap]
    · simp [registerPartialSwap, hj, Ne.symm hj]
  simp only [Matrix.trace, Matrix.diag, replicaSwap_mul_left, Fintype.sum_prod_type]
  simp_rw [hd]
  simp [Finset.sum_ite_irrel, pow_two]

omit [Fintype I] [DecidableEq I] [DecidableEq J] [Fintype K] [DecidableEq K] in
theorem partialRetain_eq_chart (e : I ≃ J × K) (X : Matrix I I ℂ) :
    partialRetain e X = QuantumProver.QuantumEntropy.partialTrace_left (Matrix.reindex e e X) := rfl

theorem partialSwap_trace (e : I ≃ J × K) :
    (partialSwap e).trace = ((Fintype.card J : ℂ)^2 * (Fintype.card K : ℂ)) := by
  have ht := QuantumProver.QuantumEntropy.trace_reindex
    (Equiv.prodCongr e.symm e.symm) (registerPartialSwap (J := J) (K := K))
  exact ht.trans registerPartialSwap_trace

omit [Fintype I] [Fintype J] in
theorem replicaSwap_chart (e : I ≃ J) :
    Matrix.reindex (Equiv.prodCongr e e) (Equiv.prodCongr e e)
      (QuantumProver.WernerEndpoint.replicaSwap I) = QuantumProver.WernerEndpoint.replicaSwap J := by
  ext x y
  simp [Matrix.reindex_apply, QuantumProver.WernerEndpoint.replicaSwap, Prod.ext_iff,
    e.symm.injective.eq_iff]

omit [Fintype I] [Fintype J] [DecidableEq I] [Fintype K] in
theorem partialSwap_chart (e : I ≃ J × K) :
    Matrix.reindex (Equiv.prodCongr e e) (Equiv.prodCongr e e) (partialSwap e) =
      registerPartialSwap := by
  ext x y
  simp [Matrix.reindex_apply, partialSwap]

theorem partialSwap_mixed_trace (e : I ≃ J × K) (X Y : Matrix I I ℂ) :
    ((X ⊗ₖ Y)*partialSwap e).trace = (partialRetain e X * partialRetain e Y).trace := by
  let ec := Equiv.prodCongr e e
  have hm : Matrix.reindex ec ec ((X ⊗ₖ Y)*partialSwap e) =
      (Matrix.reindex e e X ⊗ₖ Matrix.reindex e e Y)*registerPartialSwap := by
    change (Matrix.reindexAlgEquiv ℂ ℂ ec) ((X ⊗ₖ Y)*partialSwap e) = _
    rw [map_mul]
    change Matrix.reindex ec ec (X ⊗ₖ Y) * Matrix.reindex ec ec (partialSwap e) = _
    rw [← Matrix.kroneckerMap_reindex, partialSwap_chart]
  calc
    _ = (Matrix.reindex ec ec ((X ⊗ₖ Y)*partialSwap e)).trace :=
      (QuantumProver.QuantumEntropy.trace_reindex ec _).symm
    _ = _ := by rw [hm, registerPartialSwap_mixed_trace]; rfl

theorem partialSwap_swap_trace (e : I ≃ J × K) :
    (QuantumProver.WernerEndpoint.replicaSwap I * partialSwap e).trace =
      ((Fintype.card J : ℂ) * (Fintype.card K : ℂ)^2) := by
  let ec := Equiv.prodCongr e e
  calc
    _ = (Matrix.reindex ec ec (QuantumProver.WernerEndpoint.replicaSwap I * partialSwap e)).trace :=
      (QuantumProver.QuantumEntropy.trace_reindex ec _).symm
    _ = _ := by
      change ((Matrix.reindexAlgEquiv ℂ ℂ ec)
        (QuantumProver.WernerEndpoint.replicaSwap I * partialSwap e)).trace = _
      rw [map_mul]
      change (Matrix.reindex ec ec (QuantumProver.WernerEndpoint.replicaSwap I) *
        Matrix.reindex ec ec (partialSwap e)).trace = _
      rw [replicaSwap_chart, partialSwap_chart, registerPartialSwap_swap_trace]

end RegisterCharts

section HaarMoment

open QuantumProver.UnitarySecondMoment
variable {d : ℕ} {K : Type*} [Fintype K] [DecidableEq K]

theorem inverseTensor_entry_integral (W : RepMat d) (ij kl : Fin d × Fin d) :
    (∫ U : UGroup d, ((tensorUnitary U)ᴴ*W*tensorUnitary U) ij kl
      ∂unitaryHaar d) = twirl W ij kl := by
  have h := integral_inv_eq_self (fun U : UGroup d => tensorOrbit W U ij kl)
    (unitaryHaar d)
  simpa only [tensorOrbit, tensorUnitary_inv, Matrix.conjTranspose_conjTranspose]
    using h.trans (twirl_entry W ij kl).symm

theorem inverseTensor_entry_integrable (W : RepMat d) (ij kl : Fin d × Fin d) :
    Integrable (fun U : UGroup d => ((tensorUnitary U)ᴴ*W*tensorUnitary U) ij kl)
      (unitaryHaar d) := by
  have hc : Continuous (fun U : UGroup d => (tensorUnitary U)ᴴ*W*tensorUnitary U) :=
    (((tensorUnitary_continuous d).matrix_conjTranspose).matrix_mul continuous_const).matrix_mul
      (tensorUnitary_continuous d)
  simpa [MeasureTheory.IntegrableOn] using
    (hc.matrix_elem ij kl).continuousOn.integrableOn_compact
      (μ := unitaryHaar d) isCompact_univ

theorem inverseTensor_trace_integral (A W : RepMat d) :
    (∫ U : UGroup d, (A*((tensorUnitary U)ᴴ*W*tensorUnitary U)).trace
      ∂unitaryHaar d) = (A*twirl W).trace := by
  have hi (i j : Fin d × Fin d) :
      Integrable (fun U : UGroup d => A i j * ((tensorUnitary U)ᴴ*W*tensorUnitary U) j i)
        (unitaryHaar d) := (inverseTensor_entry_integrable W j i).const_mul (A i j)
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro j _
      rw [integral_const_mul]
      change A i j * (∫ U : UGroup d, ((tensorUnitary U)ᴴ*W*tensorUnitary U) j i
        ∂unitaryHaar d) = A i j * twirl W j i
      rw [inverseTensor_entry_integral]
    · intro j _; exact hi i j
  · intro i _
    exact integrable_finsetSum _ (fun j _ => hi i j)

theorem inverseTensor_trace_integrable (A W : RepMat d) :
    Integrable (fun U : UGroup d => (A*((tensorUnitary U)ᴴ*W*tensorUnitary U)).trace)
      (unitaryHaar d) := by
  have hi (i j : Fin d × Fin d) :
      Integrable (fun U : UGroup d => A i j * ((tensorUnitary U)ᴴ*W*tensorUnitary U) j i)
        (unitaryHaar d) := (inverseTensor_entry_integrable W j i).const_mul (A i j)
  simpa only [Matrix.trace, Matrix.diag, Matrix.mul_apply] using
    (integrable_finsetSum Finset.univ (fun i _ =>
      integrable_finsetSum Finset.univ (fun j _ => hi i j)))

theorem partialSwap_twirl (hd : 2 ≤ d) (e : Fin d ≃ J × K) :
    twirl (partialSwap e) =
      ((Fintype.card K : ℂ)*((Fintype.card J : ℂ)^2-1)/((d : ℂ)^2-1)) • (1 : RepMat d) +
      ((Fintype.card J : ℂ)*((Fintype.card K : ℂ)^2-1)/((d : ℂ)^2-1)) • swap d := by
  have hc : (d : ℂ) = (Fintype.card J : ℂ)*(Fintype.card K : ℂ) := by
    exact_mod_cast (show d = Fintype.card J * Fintype.card K from by
      simpa using Fintype.card_congr e)
  have hD : (d : ℂ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
  have hJ : (Fintype.card J : ℂ) ≠ 0 := (mul_ne_zero_iff.mp (hc ▸ hD)).1
  have hK : (Fintype.card K : ℂ) ≠ 0 := (mul_ne_zero_iff.mp (hc ▸ hD)).2
  have hq₁ : (Fintype.card J : ℂ)*(Fintype.card K : ℂ)^2/(d : ℂ) =
      (Fintype.card K : ℂ) := by rw [hc]; field_simp
  have hq₂ : (Fintype.card J : ℂ)^2*(Fintype.card K : ℂ)/(d : ℂ) =
      (Fintype.card J : ℂ) := by rw [hc]; field_simp
  rw [twirl_eq_identity_swap hd, partialSwap_trace, partialSwap_swap_trace, hq₁, hq₂]
  congr 2 <;> ring

theorem partialRetain_unitary_mixed_trace (e : Fin d ≃ J × K)
    (X Y : CMat d) (U : UGroup d) :
    (partialRetain e ((U : CMat d)*X*(U : CMat d)ᴴ) *
      partialRetain e ((U : CMat d)*Y*(U : CMat d)ᴴ)).trace =
      ((X ⊗ₖ Y)*((tensorUnitary U)ᴴ*partialSwap e*tensorUnitary U)).trace := by
  rw [← partialSwap_mixed_trace]
  simp only [Matrix.mul_kronecker_mul, ← Matrix.conjTranspose_kronecker, tensorUnitary,
    Matrix.mul_assoc]
  rw [Matrix.trace_mul_comm ((U : CMat d) ⊗ₖ (U : CMat d))]
  simp only [Matrix.mul_assoc]

theorem haar_partialRetain_mixed_trace (hd : 2 ≤ d) (e : Fin d ≃ J × K)
    (X Y : CMat d) :
    (∫ U : UGroup d, (partialRetain e ((U : CMat d)*X*(U : CMat d)ᴴ) *
      partialRetain e ((U : CMat d)*Y*(U : CMat d)ᴴ)).trace ∂unitaryHaar d) =
      ((Fintype.card K : ℂ)*((Fintype.card J : ℂ)^2-1)/((d : ℂ)^2-1))*X.trace*Y.trace +
      ((Fintype.card J : ℂ)*((Fintype.card K : ℂ)^2-1)/((d : ℂ)^2-1))*(X*Y).trace := by
  simp_rw [partialRetain_unitary_mixed_trace]
  rw [inverseTensor_trace_integral, partialSwap_twirl hd]
  simp only [Matrix.mul_add, Matrix.mul_smul, Matrix.trace_add, Matrix.trace_smul,
    Matrix.mul_one, Matrix.trace_kronecker, kronecker_swap_trace]
  simp [smul_eq_mul, mul_assoc]

theorem partialRetain_mixed_trace_integrable (e : Fin d ≃ J × K) (X Y : CMat d) :
    Integrable (fun U : UGroup d =>
      (partialRetain e ((U : CMat d)*X*(U : CMat d)ᴴ) *
        partialRetain e ((U : CMat d)*Y*(U : CMat d)ᴴ)).trace) (unitaryHaar d) := by
  simp_rw [partialRetain_unitary_mixed_trace]
  exact inverseTensor_trace_integrable (X ⊗ₖ Y) (partialSwap e)

end HaarMoment

section Spectator

open QuantumProver.UnitarySecondMoment QuantumProver.QuantumEntropy
variable {d : ℕ} {K : Type*} [Fintype K] [DecidableEq K]

def matrixBlock (ρ : Matrix (I × R) (I × R) ℂ) (r s : R) : Matrix I I ℂ :=
  fun a b => ρ (a,r) (b,s)

def spectatorChart (e : Fin d ≃ J × K) : Fin d × R ≃ J × (K × R) :=
  (Equiv.prodCongr e (Equiv.refl R)).trans (Equiv.prodAssoc J K R)

def decoupledMarginal (e : Fin d ≃ J × K)
    (ρ : Matrix (Fin d × R) (Fin d × R) ℂ) (U : UGroup d) : Matrix (K × R) (K × R) ℂ :=
  partialTrace_left (Matrix.reindex (spectatorChart e) (spectatorChart e)
    (((U : CMat d) ⊗ₖ (1 : Matrix R R ℂ))*ρ*((U : CMat d) ⊗ₖ (1 : Matrix R R ℂ))ᴴ))

def uniformReference (ρ : Matrix (Fin d × R) (Fin d × R) ℂ) : Matrix (K × R) (K × R) ℂ :=
  (((Fintype.card K : ℂ)⁻¹) • (1 : Matrix K K ℂ)) ⊗ₖ partialTrace_left ρ

def decouplingError (e : Fin d ≃ J × K)
    (ρ : Matrix (Fin d × R) (Fin d × R) ℂ) (U : UGroup d) : Matrix (K × R) (K × R) ℂ :=
  decoupledMarginal e ρ U - uniformReference ρ

theorem matrixBlock_localUnitary (ρ : Matrix (Fin d × R) (Fin d × R) ℂ)
    (U : UGroup d) (r s : R) :
    matrixBlock (((U : CMat d) ⊗ₖ (1 : Matrix R R ℂ))*ρ*
      ((U : CMat d) ⊗ₖ (1 : Matrix R R ℂ))ᴴ) r s =
      (U : CMat d)*matrixBlock ρ r s*(U : CMat d)ᴴ := by
  ext a b
  simp only [matrixBlock, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
    Matrix.mul_apply, Fintype.sum_prod_type, Matrix.kroneckerMap_apply, Matrix.one_apply,
    mul_ite, ite_mul, mul_one, mul_zero, zero_mul]
  simp only [Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, ite_eq_left]

omit [DecidableEq J] [Fintype K] [DecidableEq K] in
theorem matrixBlock_decoupledMarginal (e : Fin d ≃ J × K)
    (ρ : Matrix (Fin d × R) (Fin d × R) ℂ) (U : UGroup d) (r s : R) :
    matrixBlock (decoupledMarginal e ρ U) r s =
      partialRetain e ((U : CMat d)*matrixBlock ρ r s*(U : CMat d)ᴴ) := by
  ext k l
  change (∑ j : J, matrixBlock (((U : CMat d) ⊗ₖ (1 : Matrix R R ℂ))*ρ*
    ((U : CMat d) ⊗ₖ (1 : Matrix R R ℂ))ᴴ) r s (e.symm (j,k)) (e.symm (j,l))) = _
  rw [matrixBlock_localUnitary]
  rfl

omit [Fintype R] [DecidableEq I] [DecidableEq R] in
theorem matrixBlock_trace (ρ : Matrix (I × R) (I × R) ℂ) (r s : R) :
    (matrixBlock ρ r s).trace = partialTrace_left ρ r s := rfl

theorem partialRetain_trace (e : I ≃ J × K) (X : Matrix I I ℂ) :
    (partialRetain e X).trace = X.trace := by
  rw [partialRetain_eq_chart, trace_partialTraceLeft, trace_reindex]

theorem decoupledMarginal_spectator (e : Fin d ≃ J × K)
    (ρ : Matrix (Fin d × R) (Fin d × R) ℂ) (U : UGroup d) :
    partialTrace_left (decoupledMarginal e ρ U) = partialTrace_left ρ := by
  ext r s
  have hU : (U : CMat d)ᴴ*(U : CMat d) = 1 := Matrix.mem_unitaryGroup_iff'.mp U.property
  rw [← matrixBlock_trace, matrixBlock_decoupledMarginal, partialRetain_trace,
    Matrix.trace_mul_cycle, hU, Matrix.one_mul,
    matrixBlock_trace]

theorem localUnitary_gram (U : UGroup d) :
    ((U : CMat d) ⊗ₖ (1 : Matrix R R ℂ))ᴴ*
      ((U : CMat d) ⊗ₖ (1 : Matrix R R ℂ)) = 1 := by
  have hU : (U : CMat d)ᴴ*(U : CMat d) = 1 := Matrix.mem_unitaryGroup_iff'.mp U.property
  rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
    hU]
  simp

theorem decoupledMarginal_isDensity (e : Fin d ≃ J × K)
    {ρ : Matrix (Fin d × R) (Fin d × R) ℂ}
    (hρ : QuantumProver.SuperchannelDiscrimination.FlaggedStates.IsDensity ρ) (U : UGroup d) :
    QuantumProver.SuperchannelDiscrimination.FlaggedStates.IsDensity (decoupledMarginal e ρ U) := by
  apply partialTraceLeft_isDensity
  refine ⟨(hρ.1.mul_mul_conjTranspose_same _).submatrix (spectatorChart e).symm, ?_⟩
  rw [trace_reindex, Matrix.trace_mul_cycle, localUnitary_gram, Matrix.one_mul, hρ.2]

omit [DecidableEq I] [DecidableEq R] in

theorem purity_as_blocks (ρ : Matrix (I × R) (I × R) ℂ) :
    (ρ*ρ).trace = ∑ r : R, ∑ s : R, (matrixBlock ρ r s * matrixBlock ρ s r).trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Fintype.sum_prod_type, matrixBlock]
  conv_lhs =>
    rw [Finset.sum_comm]
    arg 2; ext r
    arg 2; ext a
    rw [Finset.sum_comm]
  conv_lhs =>
    arg 2; ext r
    rw [Finset.sum_comm]

theorem decoupledMarginal_purity_integrable (e : Fin d ≃ J × K)
    (ρ : Matrix (Fin d × R) (Fin d × R) ℂ) :
    Integrable (fun U : UGroup d =>
      (decoupledMarginal e ρ U * decoupledMarginal e ρ U).trace) (unitaryHaar d) := by
  simp_rw [purity_as_blocks, matrixBlock_decoupledMarginal]
  exact integrable_finsetSum Finset.univ (fun r _ =>
    integrable_finsetSum Finset.univ (fun s _ =>
      partialRetain_mixed_trace_integrable e (matrixBlock ρ r s) (matrixBlock ρ s r)))

theorem haar_decoupledMarginal_purity (hd : 2 ≤ d) (e : Fin d ≃ J × K)
    (ρ : Matrix (Fin d × R) (Fin d × R) ℂ) :
    (∫ U : UGroup d, (decoupledMarginal e ρ U * decoupledMarginal e ρ U).trace
      ∂unitaryHaar d) =
      ((Fintype.card K : ℂ)*((Fintype.card J : ℂ)^2-1)/((d : ℂ)^2-1))*
        (partialTrace_left ρ * partialTrace_left ρ).trace +
      ((Fintype.card J : ℂ)*((Fintype.card K : ℂ)^2-1)/((d : ℂ)^2-1))*(ρ*ρ).trace := by
  have hi (r s : R) := partialRetain_mixed_trace_integrable e
    (matrixBlock ρ r s) (matrixBlock ρ s r)
  have hp : (∫ U : UGroup d, (decoupledMarginal e ρ U * decoupledMarginal e ρ U).trace
      ∂unitaryHaar d) =
      ∑ r : R, ∑ s : R, (∫ U : UGroup d,
        (partialRetain e ((U : CMat d)*matrixBlock ρ r s*(U : CMat d)ᴴ) *
          partialRetain e ((U : CMat d)*matrixBlock ρ s r*(U : CMat d)ᴴ)).trace
            ∂unitaryHaar d) := by
    simp_rw [purity_as_blocks, matrixBlock_decoupledMarginal]
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro r _
      exact integral_finsetSum _ (fun s _ => hi r s)
    · intro r _
      exact integrable_finsetSum _ (fun s _ => hi r s)
  rw [hp]
  simp_rw [haar_partialRetain_mixed_trace hd, mul_assoc]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  have hpy : (∑ r : R, ∑ s : R, (matrixBlock ρ r s).trace*(matrixBlock ρ s r).trace) =
      (partialTrace_left ρ * partialTrace_left ρ).trace := by
    simp_rw [matrixBlock_trace]
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  rw [hpy, ← purity_as_blocks]

theorem decoupledMarginal_posSemidef (e : Fin d ≃ J × K)
    {ρ : Matrix (Fin d × R) (Fin d × R) ℂ} (hρ : ρ.PosSemidef) (U : UGroup d) :
    (decoupledMarginal e ρ U).PosSemidef :=
  partialTraceLeft_posSemidef ((hρ.mul_mul_conjTranspose_same _).submatrix (spectatorChart e).symm)

theorem uniformReference_isHermitian {ρ : Matrix (Fin d × R) (Fin d × R) ℂ}
    (hρ : ρ.PosSemidef) : (uniformReference (K := K) ρ).IsHermitian := by
  have hc : IsSelfAdjoint ((Fintype.card K : ℂ)⁻¹) := by simp [IsSelfAdjoint]
  have hI : (1 : Matrix K K ℂ).IsHermitian := Matrix.isHermitian_one
  exact isHermitian_kronecker (hI.smul hc) (partialTraceLeft_posSemidef hρ).isHermitian

theorem decouplingError_isHermitian (e : Fin d ≃ J × K)
    {ρ : Matrix (Fin d × R) (Fin d × R) ℂ} (hρ : ρ.PosSemidef) (U : UGroup d) :
    (decouplingError e ρ U).IsHermitian :=
  (decoupledMarginal_posSemidef e hρ U).isHermitian.sub (uniformReference_isHermitian hρ)

theorem decoupledMarginal_uniform_cross_trace (e : Fin d ≃ J × K)
    (ρ : Matrix (Fin d × R) (Fin d × R) ℂ) (U : UGroup d) :
    (decoupledMarginal e ρ U * uniformReference ρ).trace =
      (Fintype.card K : ℂ)⁻¹*(partialTrace_left ρ * partialTrace_left ρ).trace := by
  rw [uniformReference, Matrix.smul_kronecker, Matrix.mul_smul, Matrix.trace_smul,
    partialTrace_left_mul_trace, decoupledMarginal_spectator]
  rfl

omit [DecidableEq R] in
theorem uniformReference_square_trace (ρ : Matrix (Fin d × R) (Fin d × R) ℂ)
    (hK : (Fintype.card K : ℂ) ≠ 0) :
    (uniformReference (K := K) ρ * uniformReference ρ).trace =
      (Fintype.card K : ℂ)⁻¹*(partialTrace_left ρ * partialTrace_left ρ).trace := by
  rw [uniformReference, ← Matrix.mul_kronecker_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    Matrix.one_mul, Matrix.trace_kronecker, Matrix.trace_smul, Matrix.trace_one]
  simp only [smul_eq_mul]
  field_simp

theorem decouplingError_square_trace (e : Fin d ≃ J × K)
    (ρ : Matrix (Fin d × R) (Fin d × R) ℂ) (U : UGroup d)
    (hK : (Fintype.card K : ℂ) ≠ 0) :
    (decouplingError e ρ U * decouplingError e ρ U).trace =
      (decoupledMarginal e ρ U * decoupledMarginal e ρ U).trace -
        (Fintype.card K : ℂ)⁻¹*(partialTrace_left ρ * partialTrace_left ρ).trace := by
  rw [decouplingError, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub]
  simp only [Matrix.trace_sub]
  rw [Matrix.trace_mul_comm (uniformReference ρ) (decoupledMarginal e ρ U),
    decoupledMarginal_uniform_cross_trace, uniformReference_square_trace ρ hK]
  ring

theorem decouplingError_square_integrable (e : Fin d ≃ J × K)
    (ρ : Matrix (Fin d × R) (Fin d × R) ℂ) (hK : (Fintype.card K : ℂ) ≠ 0) :
    Integrable (fun U : UGroup d => (decouplingError e ρ U * decouplingError e ρ U).trace)
      (unitaryHaar d) := by
  simp_rw [decouplingError_square_trace e ρ _ hK]
  exact (decoupledMarginal_purity_integrable e ρ).sub (integrable_const _)

theorem haar_decouplingError_square (hd : 2 ≤ d) (e : Fin d ≃ J × K)
    (ρ : Matrix (Fin d × R) (Fin d × R) ℂ) :
    (∫ U : UGroup d, (decouplingError e ρ U * decouplingError e ρ U).trace
      ∂unitaryHaar d) =
      ((Fintype.card J : ℂ)*((Fintype.card K : ℂ)^2-1)/((d : ℂ)^2-1))*
        ((ρ*ρ).trace - (partialTrace_left ρ * partialTrace_left ρ).trace/(d : ℂ)) := by
  have hc : (d : ℂ) = (Fintype.card J : ℂ)*(Fintype.card K : ℂ) := by
    exact_mod_cast (show d = Fintype.card J * Fintype.card K from by
      simpa using Fintype.card_congr e)
  have hD : (d : ℂ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
  have hK : (Fintype.card K : ℂ) ≠ 0 := (mul_ne_zero_iff.mp (hc ▸ hD)).2
  have hden : (d : ℂ)^2-1 ≠ 0 := by
    have hdr : 2 ≤ (d : ℝ) := by exact_mod_cast hd
    exact_mod_cast (show (d : ℝ)^2-1 ≠ 0 by nlinarith)
  have ha : (Fintype.card K : ℂ)*((Fintype.card J : ℂ)^2-1)/((d : ℂ)^2-1) -
      (Fintype.card K : ℂ)⁻¹ =
      -((Fintype.card J : ℂ)*((Fintype.card K : ℂ)^2-1)/((d : ℂ)^2-1))/(d : ℂ) := by
    field_simp [hD, hK, hden]
    rw [hc]
    ring
  simp_rw [decouplingError_square_trace e ρ _ hK]
  rw [integral_sub (decoupledMarginal_purity_integrable e ρ) (integrable_const _),
    haar_decoupledMarginal_purity hd]
  simp only [integral_const, probReal_univ, one_smul]
  calc
    _ = ((Fintype.card K : ℂ)*((Fintype.card J : ℂ)^2-1)/((d : ℂ)^2-1) -
        (Fintype.card K : ℂ)⁻¹)*(partialTrace_left ρ * partialTrace_left ρ).trace +
        ((Fintype.card J : ℂ)*((Fintype.card K : ℂ)^2-1)/((d : ℂ)^2-1))*(ρ*ρ).trace := by ring
    _ = _ := by rw [ha]; ring

theorem haar_decoupling_hsSq (hd : 2 ≤ d) (e : Fin d ≃ J × K)
    {ρ : Matrix (Fin d × R) (Fin d × R) ℂ} (hρ : ρ.PosSemidef) :
    (∫ U : UGroup d, hsSq (decouplingError e ρ U) ∂unitaryHaar d) =
      ((Fintype.card J : ℝ)*((Fintype.card K : ℝ)^2-1)/((d : ℝ)^2-1))*
        ((ρ*ρ).trace.re - (partialTrace_left ρ * partialTrace_left ρ).trace.re/(d : ℝ)) := by
  have hc : d = Fintype.card J * Fintype.card K := by simpa using Fintype.card_congr e
  have hK : (Fintype.card K : ℂ) ≠ 0 := by
    exact_mod_cast (show Fintype.card K ≠ 0 from by intro h; rw [h, mul_zero] at hc; omega)
  have hH (U : UGroup d) : hsSq (decouplingError e ρ U) =
      (decouplingError e ρ U * decouplingError e ρ U).trace.re := by
    rw [hsSq, (decouplingError_isHermitian e hρ U).eq]
  simp_rw [hH]
  have hRe : (∫ U : UGroup d,
      (decouplingError e ρ U * decouplingError e ρ U).trace.re ∂unitaryHaar d) =
      (∫ U : UGroup d, (decouplingError e ρ U * decouplingError e ρ U).trace
        ∂unitaryHaar d).re := by
    simpa only [RCLike.re_eq_complex_re] using
      integral_re (decouplingError_square_integrable e ρ hK)
  rw [hRe, haar_decouplingError_square hd]
  have hb : (Fintype.card J : ℂ)*((Fintype.card K : ℂ)^2-1)/((d : ℂ)^2-1) =
      (((Fintype.card J : ℝ)*((Fintype.card K : ℝ)^2-1)/((d : ℝ)^2-1) : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [hb]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, Complex.sub_re]
  change ((Fintype.card J : ℝ)*((Fintype.card K : ℝ)^2-1)/((d : ℝ)^2-1))*
    ((ρ*ρ).trace.re - ((partialTrace_left ρ * partialTrace_left ρ).trace/((d : ℝ) : ℂ)).re) = _
  rw [Complex.div_ofReal_re]

theorem haar_decoupling_hsSq_le (hd : 2 ≤ d) (e : Fin d ≃ J × K)
    {ρ : Matrix (Fin d × R) (Fin d × R) ℂ} (hρ : ρ.PosSemidef) :
    (∫ U : UGroup d, hsSq (decouplingError e ρ U) ∂unitaryHaar d) ≤
      (ρ*ρ).trace.re/(Fintype.card J : ℝ) := by
  have hcN : d = Fintype.card J * Fintype.card K := by simpa using Fintype.card_congr e
  have hc : (d : ℝ) = (Fintype.card J : ℝ)*(Fintype.card K : ℝ) := by exact_mod_cast hcN
  have hJNat : 0 < Fintype.card J := by
    by_contra h; have hz : Fintype.card J = 0 := Nat.eq_zero_of_not_pos h
    rw [hz, zero_mul] at hcN; omega
  have hKNat : 0 < Fintype.card K := by
    by_contra h; have hz : Fintype.card K = 0 := Nat.eq_zero_of_not_pos h
    rw [hz, mul_zero] at hcN; omega
  have hj : 0 < (Fintype.card J : ℝ) := by exact_mod_cast hJNat
  have hj₁ : 1 ≤ (Fintype.card J : ℝ) := by exact_mod_cast hJNat
  have hk₁ : 1 ≤ (Fintype.card K : ℝ) := by exact_mod_cast hKNat
  have hdr : 2 ≤ (d : ℝ) := by exact_mod_cast hd
  have hden : 0 < (d : ℝ)^2-1 := by nlinarith
  have hb0 : 0 ≤ (Fintype.card J : ℝ)*((Fintype.card K : ℝ)^2-1)/((d : ℝ)^2-1) := by
    apply div_nonneg
    · apply mul_nonneg hj.le; nlinarith
    · exact hden.le
  have hble : (Fintype.card J : ℝ)*((Fintype.card K : ℝ)^2-1)/((d : ℝ)^2-1) ≤
      1/(Fintype.card J : ℝ) := by
    apply (div_le_div_iff₀ hden hj).mpr
    rw [hc]
    nlinarith [show 1 ≤ (Fintype.card J : ℝ)^2 by nlinarith]
  have hp : 0 ≤ (ρ*ρ).trace.re := by
    simpa only [hsSq, hρ.isHermitian.eq] using hsSq_nonneg ρ
  have hy : 0 ≤ (partialTrace_left ρ * partialTrace_left ρ).trace.re := by
    simpa only [hsSq, (partialTraceLeft_posSemidef hρ).isHermitian.eq] using
      hsSq_nonneg (partialTrace_left ρ)
  rw [haar_decoupling_hsSq hd e hρ]
  calc
    _ ≤ ((Fintype.card J : ℝ)*((Fintype.card K : ℝ)^2-1)/((d : ℝ)^2-1))*(ρ*ρ).trace.re :=
      mul_le_mul_of_nonneg_left (sub_le_self _ (div_nonneg hy (by positivity))) hb0
    _ ≤ (1/(Fintype.card J : ℝ))*(ρ*ρ).trace.re := mul_le_mul_of_nonneg_right hble hp
    _ = _ := by ring

theorem decouplingError_traceNorm_sq_le (e : Fin d ≃ J × K)
    {ρ : Matrix (Fin d × R) (Fin d × R) ℂ} (hρ : ρ.PosSemidef) (U : UGroup d) :
    traceNorm (decouplingError e ρ U)^2 ≤
      ((Fintype.card K : ℝ)*(partialTrace_left ρ).rank)*hsSq (decouplingError e ρ U) := by
  let S := partialTrace_left ρ
  let P := supportProjection S
  let Q : Matrix (K × R) (K × R) ℂ := (1 : Matrix K K ℂ) ⊗ₖ P
  have hS : S.IsHermitian := (partialTraceLeft_posSemidef hρ).isHermitian
  have hP : P.IsHermitian := QuantumProver.SuperchannelDiscrimination.OutputSupport.supportProjection_isHermitian hS
  have hPP : P*P = P := QuantumProver.SuperchannelDiscrimination.OutputSupport.supportProjection_idempotent hS
  have hQ : Q.IsHermitian := isHermitian_kronecker Matrix.isHermitian_one hP
  have hQQ : Q*Q = Q := by
    change ((1 : Matrix K K ℂ) ⊗ₖ P)*((1 : Matrix K K ℂ) ⊗ₖ P) = _
    rw [← Matrix.mul_kronecker_mul, Matrix.one_mul, hPP]
  have hσ : decoupledMarginal e ρ U * Q = decoupledMarginal e ρ U := by
    have h := mul_right_marginal_supportProjection (decoupledMarginal_posSemidef e hρ U)
    rw [decoupledMarginal_spectator] at h
    exact h
  have hr : uniformReference (K := K) ρ * Q = uniformReference ρ := by
    change ((((Fintype.card K : ℂ)⁻¹) • (1 : Matrix K K ℂ)) ⊗ₖ S)*
      ((1 : Matrix K K ℂ) ⊗ₖ P) = _
    rw [← Matrix.mul_kronecker_mul, Matrix.mul_one, supportProjection_mul S hS]
    rfl
  have hX : decouplingError e ρ U * Q = decouplingError e ρ U := by
    rw [decouplingError, Matrix.sub_mul, hσ, hr]
  have hRank : (Q.rank : ℝ) = (Fintype.card K : ℝ)*S.rank := by
    have ht := congrArg Complex.re (projection_trace_eq_rank hQQ)
    change (((1 : Matrix K K ℂ) ⊗ₖ P).trace).re = (Q.rank : ℝ) at ht
    rw [Matrix.trace_kronecker, Matrix.trace_one, projection_trace_eq_rank hPP,
      supportProjection_rank hS] at ht
    simpa [Complex.mul_re] using ht.symm
  have h := traceNorm_supported_sq_le hQ hQQ hX
  rw [hRank] at h
  exact h

theorem traceNorm_continuous : Continuous (traceNorm (I := I)) := by
  apply continuous_iff_continuousAt.mpr
  intro X
  have hG : Tendsto (fun Y : Matrix I I ℂ => Yᴴ*Y) (𝓝 X) (𝓝 (Xᴴ*X)) :=
    (continuous_id.matrix_conjTranspose.matrix_mul continuous_id).continuousAt
  have hw : Tendsto (fun Y : Matrix I I ℂ => Yᴴ*Y) (𝓝 X)
      (𝓝[Set.Ici (0 : Matrix I I ℂ)] (Xᴴ*X)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hG, Eventually.of_forall (fun Y =>
      (Matrix.posSemidef_conjTranspose_mul_self Y).nonneg)⟩
  have hRoot := (CFC.continuousOn_sqrt (Xᴴ*X)
    (Matrix.posSemidef_conjTranspose_mul_self X).nonneg).tendsto.comp hw
  have hTrace : Continuous (fun Y : Matrix I I ℂ => Y.trace.re) :=
    Complex.continuous_re.comp continuous_id.matrix_trace
  change Tendsto (fun Y : Matrix I I ℂ => traceNorm Y) (𝓝 X) (𝓝 (traceNorm X))
  simp_rw [QuantumProver.SandwichedDPI.traceNorm_eq_singularValueTrace]
  exact hTrace.continuousAt.tendsto.comp hRoot

omit [DecidableEq J] [Fintype K] [DecidableEq K] in
theorem decoupledMarginal_apply (e : Fin d ≃ J × K)
    (ρ : Matrix (Fin d × R) (Fin d × R) ℂ) (U : UGroup d) (kr ls : K × R) :
    decoupledMarginal e ρ U kr ls =
      partialRetain e ((U : CMat d)*matrixBlock ρ kr.2 ls.2*(U : CMat d)ᴴ) kr.1 ls.1 :=
  congrFun (congrFun (matrixBlock_decoupledMarginal e ρ U kr.2 ls.2) kr.1) ls.1

omit [DecidableEq J] [Fintype K] [DecidableEq K] in
theorem decoupledMarginal_continuous (e : Fin d ≃ J × K)
    (ρ : Matrix (Fin d × R) (Fin d × R) ℂ) : Continuous (decoupledMarginal e ρ) := by
  apply continuous_matrix
  intro kr ls
  simp_rw [decoupledMarginal_apply, partialRetain]
  have hC : Continuous (fun U : UGroup d =>
      (U : CMat d)*matrixBlock ρ kr.2 ls.2*(U : CMat d)ᴴ) :=
    (continuous_subtype_val.matrix_mul continuous_const).matrix_mul
      continuous_subtype_val.matrix_conjTranspose
  exact continuous_finsetSum _ (fun j _ => hC.matrix_elem _ _)

omit [DecidableEq J] in
theorem decouplingError_continuous (e : Fin d ≃ J × K)
    (ρ : Matrix (Fin d × R) (Fin d × R) ℂ) : Continuous (decouplingError e ρ) :=
  (decoupledMarginal_continuous e ρ).sub continuous_const

theorem decoupling_traceNorm_sq_integrable (e : Fin d ≃ J × K)
    (ρ : Matrix (Fin d × R) (Fin d × R) ℂ) :
    Integrable (fun U : UGroup d => traceNorm (decouplingError e ρ U)^2) (unitaryHaar d) := by
  have hC := (traceNorm_continuous.comp (decouplingError_continuous e ρ)).pow 2
  have hi : Integrable ((traceNorm ∘ decouplingError e ρ)^2) (unitaryHaar d) := by
    simpa [MeasureTheory.IntegrableOn] using
      hC.continuousOn.integrableOn_compact (μ := unitaryHaar d) isCompact_univ
  exact hi.congr (Eventually.of_forall (fun U => rfl))

theorem decoupling_hsSq_integrable (e : Fin d ≃ J × K)
    (ρ : Matrix (Fin d × R) (Fin d × R) ℂ) :
    Integrable (fun U : UGroup d => hsSq (decouplingError e ρ U)) (unitaryHaar d) := by
  have hC : Continuous (fun U : UGroup d => hsSq (decouplingError e ρ U)) :=
    Complex.continuous_re.comp (((decouplingError_continuous e ρ).matrix_conjTranspose.matrix_mul
      (decouplingError_continuous e ρ)).matrix_trace)
  simpa [MeasureTheory.IntegrableOn] using
    hC.continuousOn.integrableOn_compact (μ := unitaryHaar d) isCompact_univ

theorem haar_decoupling_traceNorm_sq_le (hd : 2 ≤ d) (e : Fin d ≃ J × K)
    {ρ : Matrix (Fin d × R) (Fin d × R) ℂ} (hρ : ρ.PosSemidef) :
    (∫ U : UGroup d, traceNorm (decouplingError e ρ U)^2 ∂unitaryHaar d) ≤
      (Fintype.card K : ℝ)^2*(partialTrace_left ρ).rank*(ρ*ρ).trace.re/(d : ℝ) := by
  have hcN : d = Fintype.card J * Fintype.card K := by simpa using Fintype.card_congr e
  have hc : (d : ℝ) = (Fintype.card J : ℝ)*(Fintype.card K : ℝ) := by exact_mod_cast hcN
  have hjN : 0 < Fintype.card J := by
    by_contra h; have hz := Nat.eq_zero_of_not_pos h
    rw [hz, zero_mul] at hcN; omega
  have hkN : 0 < Fintype.card K := by
    by_contra h; have hz := Nat.eq_zero_of_not_pos h
    rw [hz, mul_zero] at hcN; omega
  have hj : (Fintype.card J : ℝ) ≠ 0 := by exact_mod_cast hjN.ne'
  have hk : (Fintype.card K : ℝ) ≠ 0 := by exact_mod_cast hkN.ne'
  calc
    _ ≤ ∫ U : UGroup d,
        ((Fintype.card K : ℝ)*(partialTrace_left ρ).rank)*hsSq (decouplingError e ρ U)
          ∂unitaryHaar d :=
      integral_mono (decoupling_traceNorm_sq_integrable e ρ)
        ((decoupling_hsSq_integrable e ρ).const_mul _)
          (fun U => decouplingError_traceNorm_sq_le e hρ U)
    _ = ((Fintype.card K : ℝ)*(partialTrace_left ρ).rank)*
        (∫ U : UGroup d, hsSq (decouplingError e ρ U) ∂unitaryHaar d) := integral_const_mul _ _
    _ ≤ ((Fintype.card K : ℝ)*(partialTrace_left ρ).rank)*
        ((ρ*ρ).trace.re/(Fintype.card J : ℝ)) :=
      mul_le_mul_of_nonneg_left (haar_decoupling_hsSq_le hd e hρ) (by positivity)
    _ = _ := by rw [hc]; field_simp

theorem decouplingError_unique [Unique K] (e : Fin d ≃ J × K)
    (ρ : Matrix (Fin d × R) (Fin d × R) ℂ) (U : UGroup d) :
    decouplingError e ρ U = 0 := by
  ext ⟨k,r⟩ ⟨l,s⟩
  have hk : k = default := Subsingleton.elim _ _
  have hl : l = default := Subsingleton.elim _ _
  subst k; subst l
  have h := congrFun (congrFun (decoupledMarginal_spectator e ρ U) r) s
  change (∑ a : K, decoupledMarginal e ρ U (a,r) (a,s)) = partialTrace_left ρ r s at h
  have hs : decoupledMarginal e ρ U (default,r) (default,s) = partialTrace_left ρ r s := by
    simpa only [Fintype.sum_unique] using h
  simpa [decouplingError, uniformReference, Matrix.kronecker_apply] using sub_eq_zero.mpr hs

theorem decouplingError_card_one (e : Fin d ≃ J × K)
    (ρ : Matrix (Fin d × R) (Fin d × R) ℂ) (hK : Fintype.card K = 1) (U : UGroup d) :
    decouplingError e ρ U = 0 := by
  let : Unique K := Classical.choice (Fintype.card_eq_one_iff_nonempty_unique.mp hK)
  exact decouplingError_unique e ρ U

def decouplingCost (ρ : Matrix (Fin d × R) (Fin d × R) ℂ) : ℝ :=
  if Fintype.card K = 1 then 0 else
    (Fintype.card K : ℝ)^2*(partialTrace_left ρ).rank*(ρ*ρ).trace.re/(d : ℝ)

omit [DecidableEq R] [DecidableEq K] in
theorem decouplingCost_nonneg {ρ : Matrix (Fin d × R) (Fin d × R) ℂ}
    (hρ : ρ.PosSemidef) : 0 ≤ decouplingCost (K := K) ρ := by
  have hp : 0 ≤ (ρ*ρ).trace.re := by
    simpa only [hsSq, hρ.isHermitian.eq] using hsSq_nonneg ρ
  unfold decouplingCost
  split_ifs <;> positivity

theorem haar_decoupling_clippedCost (hd : 2 ≤ d) (e : Fin d ≃ J × K)
    {ρ : Matrix (Fin d × R) (Fin d × R) ℂ} (hρ : ρ.PosSemidef) :
    (∫ U : UGroup d, traceNorm (decouplingError e ρ U)^2 ∂unitaryHaar d) ≤
      decouplingCost (K := K) ρ := by
  unfold decouplingCost
  split_ifs with hk
  · simp_rw [decouplingError_card_one e ρ hk]
    simp [QuantumProver.SandwichedDPI.traceNorm]
  · exact haar_decoupling_traceNorm_sq_le hd e hρ

omit [DecidableEq J] in
theorem decouplingError_carrier_zero (e : Fin 0 ≃ J × K)
    (ρ : Matrix (Fin 0 × R) (Fin 0 × R) ℂ) (U : UGroup 0) : decouplingError e ρ U = 0 := by
  have hρ : ρ = 0 := by ext x y; exact Fin.elim0 x.1
  ext kr ls
  simp [decouplingError, decoupledMarginal, uniformReference, hρ,
    Matrix.reindex_apply, partialTrace_left]

theorem haar_decouplingCost_bound (e : Fin d ≃ J × K)
    {ρ : Matrix (Fin d × R) (Fin d × R) ℂ} (hρ : ρ.PosSemidef) :
    (∫ U : UGroup d, traceNorm (decouplingError e ρ U)^2 ∂unitaryHaar d) ≤
      decouplingCost (K := K) ρ := by
  by_cases hd₀ : d = 0
  · subst d
    simp_rw [decouplingError_carrier_zero]
    simpa [QuantumProver.SandwichedDPI.traceNorm] using decouplingCost_nonneg (K := K) hρ
  by_cases hd₁ : d = 1
  · subst d
    have hc : 1 = Fintype.card J * Fintype.card K := by simpa using Fintype.card_congr e
    have hk : Fintype.card K = 1 :=
      Nat.dvd_one.mp ⟨Fintype.card J, by simpa only [mul_comm] using hc⟩
    simp_rw [decouplingError_card_one e ρ hk]
    simpa [QuantumProver.SandwichedDPI.traceNorm] using decouplingCost_nonneg (K := K) hρ
  exact haar_decoupling_clippedCost (by omega) e hρ

end Spectator

section CommonUnitary

theorem exists_two_square_bounds {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f g : Ω → ℝ) (c₁ c₂ : ℝ)
    (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂)
    (hf : Integrable (fun x => f x^2) μ) (hg : Integrable (fun x => g x^2) μ)
    (hbf : (∫ x, f x^2 ∂μ) ≤ c₁) (hbg : (∫ x, g x^2 ∂μ) ≤ c₂) :
    ∃ x, f x^2 ≤ 3*c₁ ∧ g x^2 ≤ 3*c₂ := by
  have hz₁ : ∀ᵐ x ∂μ, c₁ = 0 → f x^2 = 0 := by
    by_cases hc : c₁ = 0
    · have hi : (∫ x, f x^2 ∂μ) = 0 := le_antisymm (hc ▸ hbf)
        (integral_nonneg (fun x => sq_nonneg (f x)))
      have hz := (integral_eq_zero_iff_of_nonneg_ae
        (Eventually.of_forall (fun x => sq_nonneg (f x))) hf).mp hi
      exact hz.mono (fun x h _ => h)
    · exact Eventually.of_forall (fun x h => (hc h).elim)
  have hz₂ : ∀ᵐ x ∂μ, c₂ = 0 → g x^2 = 0 := by
    by_cases hc : c₂ = 0
    · have hi : (∫ x, g x^2 ∂μ) = 0 := le_antisymm (hc ▸ hbg)
        (integral_nonneg (fun x => sq_nonneg (g x)))
      have hz := (integral_eq_zero_iff_of_nonneg_ae
        (Eventually.of_forall (fun x => sq_nonneg (g x))) hg).mp hi
      exact hz.mono (fun x h _ => h)
    · exact Eventually.of_forall (fun x h => (hc h).elim)
  have hb₁ : (∫ x, f x^2/c₁ ∂μ) ≤ 1 := by
    rw [integral_div]
    by_cases hc : c₁ = 0
    · simp [hc]
    · exact (div_le_iff₀ (lt_of_le_of_ne hc₁ (Ne.symm hc))).mpr (by simpa using hbf)
  have hb₂ : (∫ x, g x^2/c₂ ∂μ) ≤ 1 := by
    rw [integral_div]
    by_cases hc : c₂ = 0
    · simp [hc]
    · exact (div_le_iff₀ (lt_of_le_of_ne hc₂ (Ne.symm hc))).mpr (by simpa using hbg)
  have hi : Integrable (fun x => f x^2/c₁ + g x^2/c₂) μ :=
    (hf.div_const c₁).add (hg.div_const c₂)
  have hb : (∫ x, f x^2/c₁ + g x^2/c₂ ∂μ) ≤ 2 := by
    rw [integral_add (hf.div_const c₁) (hg.div_const c₂)]
    linarith
  by_contra hn
  push Not at hn
  have hlo : ∀ᵐ x ∂μ, (3 : ℝ) ≤ f x^2/c₁ + g x^2/c₂ := by
    filter_upwards [hz₁, hz₂] with x hx₁ hx₂
    have hnf : 0 ≤ f x^2/c₁ := div_nonneg (sq_nonneg _) hc₁
    have hng : 0 ≤ g x^2/c₂ := div_nonneg (sq_nonneg _) hc₂
    by_cases hfx : f x^2 ≤ 3*c₁
    · have hgx : 3*c₂ < g x^2 := hn x hfx
      have hc : 0 < c₂ := by
        by_contra h
        have he : c₂ = 0 := le_antisymm (le_of_not_gt h) hc₂
        rw [he, hx₂ he] at hgx; norm_num at hgx
      have hr : 3 ≤ g x^2/c₂ := (le_div_iff₀ hc).mpr hgx.le
      linarith
    · have hfx' : 3*c₁ < f x^2 := lt_of_not_ge hfx
      have hc : 0 < c₁ := by
        by_contra h
        have he : c₁ = 0 := le_antisymm (le_of_not_gt h) hc₁
        rw [he, hx₁ he] at hfx'; norm_num at hfx'
      have hr : 3 ≤ f x^2/c₁ := (le_div_iff₀ hc).mpr hfx'.le
      linarith
  have hlow : (3 : ℝ) ≤ ∫ x, f x^2/c₁ + g x^2/c₂ ∂μ := by
    calc
      _ = ∫ _ : Ω, (3 : ℝ) ∂μ := by simp
      _ ≤ _ := integral_mono_ae (integrable_const _) hi hlo
  linarith

open QuantumProver.UnitarySecondMoment
variable {d : ℕ} {J₁ K₁ Y₁ J₂ K₂ Y₂ : Type*}
  [Fintype J₁] [Fintype K₁] [Fintype Y₁] [Fintype J₂] [Fintype K₂] [Fintype Y₂]
  [DecidableEq J₁] [DecidableEq K₁] [DecidableEq Y₁]
  [DecidableEq J₂] [DecidableEq K₂] [DecidableEq Y₂]

theorem exists_common_decoupling_unitary
    (e₁ : Fin d ≃ J₁ × K₁) (e₂ : Fin d ≃ J₂ × K₂)
    {ρ₁ : Matrix (Fin d × Y₁) (Fin d × Y₁) ℂ}
    {ρ₂ : Matrix (Fin d × Y₂) (Fin d × Y₂) ℂ}
    (hρ₁ : ρ₁.PosSemidef) (hρ₂ : ρ₂.PosSemidef) :
    ∃ U : UGroup d,
      traceNorm (decouplingError e₁ ρ₁ U)^2 ≤ 3*decouplingCost (K := K₁) ρ₁ ∧
      traceNorm (decouplingError e₂ ρ₂ U)^2 ≤ 3*decouplingCost (K := K₂) ρ₂ :=
  exists_two_square_bounds (unitaryHaar d)
    (fun U => traceNorm (decouplingError e₁ ρ₁ U))
    (fun U => traceNorm (decouplingError e₂ ρ₂ U))
    (decouplingCost (K := K₁) ρ₁) (decouplingCost (K := K₂) ρ₂)
    (decouplingCost_nonneg hρ₁) (decouplingCost_nonneg hρ₂)
    (decoupling_traceNorm_sq_integrable e₁ ρ₁) (decoupling_traceNorm_sq_integrable e₂ ρ₂)
    (haar_decouplingCost_bound e₁ hρ₁) (haar_decouplingCost_bound e₂ hρ₂)

theorem exists_common_decoupling_unitary_bound
    (e₁ : Fin d ≃ J₁ × K₁) (e₂ : Fin d ≃ J₂ × K₂)
    {ρ₁ : Matrix (Fin d × Y₁) (Fin d × Y₁) ℂ}
    {ρ₂ : Matrix (Fin d × Y₂) (Fin d × Y₂) ℂ}
    (hρ₁ : ρ₁.PosSemidef) (hρ₂ : ρ₂.PosSemidef) :
    ∃ U : UGroup d,
      traceNorm (decouplingError e₁ ρ₁ U) ≤ Real.sqrt (3*decouplingCost (K := K₁) ρ₁) ∧
      traceNorm (decouplingError e₂ ρ₂ U) ≤ Real.sqrt (3*decouplingCost (K := K₂) ρ₂) := by
  obtain ⟨U, hU₁, hU₂⟩ := exists_common_decoupling_unitary e₁ e₂ hρ₁ hρ₂
  have hc₁ : 0 ≤ decouplingCost (K := K₁) ρ₁ := decouplingCost_nonneg hρ₁
  have hc₂ : 0 ≤ decouplingCost (K := K₂) ρ₂ := decouplingCost_nonneg hρ₂
  refine ⟨U, ?_, ?_⟩
  · apply (sq_le_sq₀ (QuantumProver.SandwichedDPI.traceNorm_nonneg _) (Real.sqrt_nonneg _)).mp
    simpa only [Real.sq_sqrt (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) hc₁)] using hU₁
  · apply (sq_le_sq₀ (QuantumProver.SandwichedDPI.traceNorm_nonneg _) (Real.sqrt_nonneg _)).mp
    simpa only [Real.sq_sqrt (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) hc₂)] using hU₂

end CommonUnitary

end QuantumProver.QuantumDecoupling

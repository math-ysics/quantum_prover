import Mathlib
import QuantumProver.LinearAlgebra.Affinity

noncomputable section

open scoped BigOperators ComplexOrder MatrixOrder Matrix Matrix.Norms.L2Operator

namespace QuantumProver.MatrixAnalysis.AbsoluteHS

open QuantumProver.SuperchannelDiscrimination

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

def hsSq (M : Matrix I J ℂ) : ℝ := (Matrix.trace (Mᴴ * M)).re

theorem abs_posSemidef (X : Matrix I I ℂ) : (CFC.abs X).PosSemidef :=
  Matrix.nonneg_iff_posSemidef.mp (CFC.abs_nonneg X)

theorem abs_isHermitian (X : Matrix I I ℂ) : (CFC.abs X).IsHermitian :=
  (abs_posSemidef X).isHermitian

theorem abs_add_self_posSemidef {X : Matrix I I ℂ} (hX : X.IsHermitian) :
    (CFC.abs X + X).PosSemidef := by
  apply Matrix.nonneg_iff_posSemidef.mp
  rw [CFC.abs_add_self X hX.isSelfAdjoint, two_smul]
  exact add_nonneg (CFC.posPart_nonneg X) (CFC.posPart_nonneg X)

theorem abs_sub_self_posSemidef {X : Matrix I I ℂ} (hX : X.IsHermitian) :
    (CFC.abs X - X).PosSemidef := by
  apply Matrix.nonneg_iff_posSemidef.mp
  rw [CFC.abs_sub_self X hX.isSelfAdjoint, two_smul]
  exact add_nonneg (CFC.negPart_nonneg X) (CFC.negPart_nonneg X)

private theorem abs_trace_product_ge {X Y : Matrix I I ℂ}
    (hX : X.IsHermitian) (hY : Y.IsHermitian) :
    (X * Y).trace.re ≤ (CFC.abs X * CFC.abs Y).trace.re := by
  have hp := FlaggedStates.trace_mul_re_nonneg
    (abs_add_self_posSemidef hX) (abs_sub_self_posSemidef hY)
  have hn := FlaggedStates.trace_mul_re_nonneg
    (abs_sub_self_posSemidef hX) (abs_add_self_posSemidef hY)
  simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.mul_add, Matrix.mul_sub,
    Matrix.trace_add, Matrix.trace_sub, Complex.add_re, Complex.sub_re] at hp hn
  linarith

theorem hsSq_sub_hermitian {X Y : Matrix I I ℂ}
    (hX : X.IsHermitian) (hY : Y.IsHermitian) :
    hsSq (X - Y) = (X * X).trace.re + (Y * Y).trace.re - 2 * (X * Y).trace.re := by
  unfold hsSq
  rw [Matrix.conjTranspose_sub, hX.eq, hY.eq]
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re]
  rw [Matrix.trace_mul_comm Y X]
  ring

theorem abs_square {X : Matrix I I ℂ} (hX : X.IsHermitian) :
    CFC.abs X * CFC.abs X = X * X := by
  rw [CFC.abs_mul_abs]
  change Xᴴ * X = X * X
  rw [hX.eq]

theorem abs_hs_contraction {X Y : Matrix I I ℂ}
    (hX : X.IsHermitian) (hY : Y.IsHermitian) :
    hsSq (CFC.abs X - CFC.abs Y) ≤ hsSq (X - Y) := by
  rw [hsSq_sub_hermitian (abs_isHermitian X) (abs_isHermitian Y),
    hsSq_sub_hermitian hX hY, abs_square hX, abs_square hY]
  have h := abs_trace_product_ge hX hY
  linarith

theorem abs_trace_pairing {X Y : Matrix I I ℂ}
    (hX : X.IsHermitian) (hY : Y.IsHermitian) :
    (X * Y).trace.re ≤ (CFC.abs X * CFC.abs Y).trace.re := by
  have h := abs_hs_contraction hX hY
  rw [hsSq_sub_hermitian (abs_isHermitian X) (abs_isHermitian Y),
    hsSq_sub_hermitian hX hY, abs_square hX, abs_square hY] at h
  linarith

def hermitianDilation (M : Matrix I J ℂ) : Matrix (I ⊕ J) (I ⊕ J) ℂ :=
  Matrix.fromBlocks 0 M Mᴴ 0

theorem hermitianDilation_isHermitian (M : Matrix I J ℂ) :
    (hermitianDilation M).IsHermitian :=
  Matrix.IsHermitian.fromBlocks (by simp) rfl (by simp)

theorem hermitianDilation_mul (M N : Matrix I J ℂ) :
    hermitianDilation M * hermitianDilation N =
      FlaggedStates.flagBlock (M * Nᴴ) (Mᴴ * N) := by
  simp [hermitianDilation, FlaggedStates.flagBlock, Matrix.fromBlocks_multiply]

theorem hermitianDilation_abs (M : Matrix I J ℂ) :
    CFC.abs (hermitianDilation M) = FlaggedStates.flagBlock
      (Affinity.sqrtPSD (M * Mᴴ)) (Affinity.sqrtPSD (Mᴴ * M)) := by
  unfold CFC.abs
  change CFC.sqrt ((hermitianDilation M)ᴴ * hermitianDilation M) = _
  rw [(hermitianDilation_isHermitian M).eq, hermitianDilation_mul]
  apply CFC.sqrt_unique
  · rw [FlaggedStates.flagBlock_mul,
      Affinity.sqrtPSD_square _ (Matrix.posSemidef_self_mul_conjTranspose M),
      Affinity.sqrtPSD_square _ (Matrix.posSemidef_conjTranspose_mul_self M)]
  · exact (FlaggedStates.flagBlock_posSemidef
      (Affinity.sqrtPSD_posSemidef _) (Affinity.sqrtPSD_posSemidef _)).nonneg

theorem rectangular_trace_pairing_re_symm (M N : Matrix I J ℂ) :
    (N * Mᴴ).trace.re = (M * Nᴴ).trace.re := by
  have h := congrArg Complex.re (Matrix.trace_conjTranspose (M * Nᴴ))
  simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    Complex.star_def, Complex.conj_re] using h

theorem rectangular_marginal_affinity (M N : Matrix I J ℂ) :
    2 * (M * Nᴴ).trace.re ≤
      Affinity.affinity (M * Mᴴ) (N * Nᴴ) +
      Affinity.affinity (Mᴴ * M) (Nᴴ * N) := by
  have h := abs_trace_pairing
    (hermitianDilation_isHermitian M) (hermitianDilation_isHermitian N)
  rw [hermitianDilation_mul, hermitianDilation_abs, hermitianDilation_abs,
    FlaggedStates.flagBlock_mul, FlaggedStates.flagBlock_trace,
    FlaggedStates.flagBlock_trace] at h
  simp only [Complex.add_re] at h
  have hr : (Mᴴ * N).trace.re = (M * Nᴴ).trace.re := by
    rw [Matrix.trace_mul_comm Mᴴ N]
    exact rectangular_trace_pairing_re_symm M N
  rw [hr] at h
  simpa only [Affinity.affinity, two_mul] using h

theorem sqrtPSD_smul_nonneg (r : ℝ) (hr : 0 ≤ r) {A : Matrix I I ℂ}
    (hA : A.PosSemidef) :
    Affinity.sqrtPSD (r • A) = Real.sqrt r • Affinity.sqrtPSD A := by
  apply CFC.sqrt_unique
  · simp only [smul_mul_assoc, mul_smul_comm, smul_smul,
      Real.mul_self_sqrt hr, Affinity.sqrtPSD_square A hA]
  · exact smul_nonneg (Real.sqrt_nonneg r) (CFC.sqrt_nonneg A)

theorem affinity_smul_nonneg (r : ℝ) (hr : 0 ≤ r) {A B : Matrix I I ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    Affinity.affinity (r • A) (r • B) = r * Affinity.affinity A B := by
  unfold Affinity.affinity
  rw [sqrtPSD_smul_nonneg r hr hA, sqrtPSD_smul_nonneg r hr hB]
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul, Real.mul_self_sqrt hr,
    Matrix.trace_smul]
  simp [Complex.real_smul]

theorem affinity_two_smul {A B : Matrix I I ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    Affinity.affinity (2 • A) (2 • B) = 2 * Affinity.affinity A B := by
  have h := affinity_smul_nonneg (2 : ℝ) (by norm_num) hA hB
  simpa only [two_smul] using h

theorem two_marginal_affinity_ge (M N : Matrix I J ℂ) :
    4 * (M * Nᴴ).trace.re ≤
      Affinity.affinity (2 • (M * Mᴴ)) (2 • (N * Nᴴ)) +
      Affinity.affinity (2 • (Mᴴ * M)) (2 • (Nᴴ * N)) := by
  rw [affinity_two_smul (Matrix.posSemidef_self_mul_conjTranspose M)
      (Matrix.posSemidef_self_mul_conjTranspose N),
    affinity_two_smul (Matrix.posSemidef_conjTranspose_mul_self M)
      (Matrix.posSemidef_conjTranspose_mul_self N)]
  have h := rectangular_marginal_affinity M N
  linarith

theorem conditional_marginal_affinity (M N : Matrix I J ℂ) (c : ℝ)
    (hoverlap : 2 * (N * Mᴴ).trace = (c : ℂ)) :
    2 * c ≤ Affinity.affinity (2 • (M * Mᴴ)) (2 • (N * Nᴴ)) +
      Affinity.affinity (2 • (Mᴴ * M)) (2 • (Nᴴ * N)) := by
  have ho := congrArg Complex.re hoverlap
  have hr := rectangular_trace_pairing_re_symm M N
  have h := two_marginal_affinity_ge M N
  norm_num at ho
  linarith

end QuantumProver.MatrixAnalysis.AbsoluteHS

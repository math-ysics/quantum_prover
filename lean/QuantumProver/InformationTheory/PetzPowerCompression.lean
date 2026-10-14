import QuantumProver.InformationTheory.Equipartition.MeasuredRenyiTensorization
import QuantumProver.InformationTheory.SuperchannelDiscrimination.TestingTheorems

set_option autoImplicit false

noncomputable section

open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix
open QuantumProver.Equipartition.FiniteModel
open QuantumProver.Equipartition.FiniteModel.PolarTensor
open QuantumProver.SuperchannelDiscrimination

namespace QuantumProver.PetzPowerCompression

variable {I O : Type*} [Fintype I] [Fintype O] [DecidableEq I] [DecidableEq O]

theorem matrixRpow_loewner_mono {X Y : CMat I} (hX : X.PosSemidef)
    (hY : Y.PosSemidef) (hXY : (Y - X).PosSemidef) {q : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    (matrixRpow Y q - matrixRpow X q).PosSemidef := by
  have hle : X ≤ Y := sub_nonneg.mp hXY.nonneg
  have h := CFC.rpow_le_rpow (A := CMat I) ⟨hq0, hq1⟩ hle
  rw [CFC.rpow_eq_cfc_real hX.nonneg, CFC.rpow_eq_cfc_real hY.nonneg] at h
  exact Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr h)

theorem matrixRpow_isometry_compression_ge {X : CMat I} (hX : X.PosSemidef)
    {V : Matrix I O ℂ} (hV : Vᴴ * V = 1) {q : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    (matrixRpow (Vᴴ * X * V) q - Vᴴ * matrixRpow X q * V).PosSemidef := by
  classical
  let P : CMat I := V * Vᴴ
  let J : CMat I := P + P - 1
  let W : CMat O := Vᴴ * X * V
  let B : CMat I := (1 / 2 : ℝ) • X + (1 / 2 : ℝ) • (J * X * J)
  have hPV : P * V = V := by
    dsimp [P]
    rw [Matrix.mul_assoc, hV, Matrix.mul_one]
  have hPP : P * P = P := by
    dsimp [P]
    calc
      (V * Vᴴ) * (V * Vᴴ) = V * (Vᴴ * V) * Vᴴ := by simp only [Matrix.mul_assoc]
      _ = V * Vᴴ := by rw [hV, Matrix.mul_one]
  have hPstar : Pᴴ = P := by simp [P]
  have hJstar : Jᴴ = J := by simp [J, hPstar]
  have hJV : J * V = V := by simp [J, Matrix.add_mul, Matrix.sub_mul, hPV]
  have hVJ : Vᴴ * J = Vᴴ := by
    simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hJstar] using
      congrArg Matrix.conjTranspose hJV
  have hJJ : J * J = 1 := by
    calc
      J * J = P * P + P * P + P * P + P * P - P - P - P - P + 1 := by
        dsimp [J]
        noncomm_ring
      _ = 1 := by rw [hPP]; abel
  have hJX : (J * X * J).PosSemidef := by
    simpa only [hJstar] using hX.conjTranspose_mul_mul_same J
  have hB : B.PosSemidef :=
    (hX.smul (show (0 : ℝ) ≤ 1 / 2 by norm_num)).add
      (hJX.smul (show (0 : ℝ) ≤ 1 / 2 by norm_num))
  have hW : W.PosSemidef := hX.conjTranspose_mul_mul_same V
  have hBV : B * V = V * W := by
    dsimp [B]
    simp only [Matrix.add_mul, Matrix.smul_mul, Matrix.mul_assoc, hJV]
    dsimp [J, P, W]
    simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc]
    module
  have hcomp : Vᴴ * matrixRpow B q * V = matrixRpow W q :=
    cfc_compression_of_intertwining hB.1 hW.1 hV hBV (fun x => Real.rpow x q)
  let U : Matrix.unitaryGroup I ℂ := ⟨J, Matrix.mem_unitaryGroup_iff.mpr
    (by rw [Matrix.star_eq_conjTranspose, hJstar, hJJ])⟩
  have hpowJ : matrixRpow (J * X * J) q = J * matrixRpow X q * J := by
    have hh := matrixRpow_unitary_conjugate U hX q
    change matrixRpow (J * X * Jᴴ) q = J * matrixRpow X q * Jᴴ at hh
    simpa only [hJstar] using hh
  have hbound : (1 / 2 : ℝ) • matrixRpow X q +
      (1 / 2 : ℝ) • matrixRpow (J * X * J) q ≤ matrixRpow B q := by
    have hh : (1 / 2 : ℝ) • CFC.rpow X q +
        (1 / 2 : ℝ) • CFC.rpow (J * X * J) q ≤ CFC.rpow B q :=
      (CFC.concaveOn_rpow (A := CMat I) ⟨hq0, hq1⟩).2
        hX.nonneg hJX.nonneg (by norm_num) (by norm_num) (by norm_num)
    simp only [CFC.rpow_eq_pow] at hh
    rw [CFC.rpow_eq_cfc_real hX.nonneg, CFC.rpow_eq_cfc_real hJX.nonneg,
      CFC.rpow_eq_cfc_real hB.nonneg] at hh
    exact hh
  have he : Vᴴ * ((1 / 2 : ℝ) • matrixRpow X q +
      (1 / 2 : ℝ) • matrixRpow (J * X * J) q) * V = Vᴴ * matrixRpow X q * V := by
    rw [hpowJ]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
    have hj : Vᴴ * (J * matrixRpow X q * J) * V = Vᴴ * matrixRpow X q * V := by
      calc
        _ = (Vᴴ * J) * matrixRpow X q * (J * V) := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [hVJ, hJV]
    rw [hj]
    module
  have hs := (Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr hbound)).conjTranspose_mul_mul_same V
  simp only [Matrix.mul_sub, Matrix.sub_mul, he, hcomp] at hs
  exact hs

theorem matrixRpow_zero {q : ℝ} (hq : q ≠ 0) :
    matrixRpow (0 : CMat I) q = 0 := by
  have h := CFC.zero_rpow (A := CMat I) hq
  rw [CFC.rpow_eq_pow, CFC.rpow_eq_cfc_real (le_refl (0 : CMat I))] at h
  exact h

theorem matrixRpow_contraction_jensen (V : Matrix I O ℂ)
    (hV : (1 - Vᴴ * V).PosSemidef) {X : CMat I} (hX : X.PosSemidef)
    {q : ℝ} (hq0 : 0 < q) (hq1 : q ≤ 1) :
    (matrixRpow (Vᴴ * X * V) q - Vᴴ * matrixRpow X q * V).PosSemidef := by
  classical
  let W := LogCompression.dilation V
  let B : CMat (I ⊕ O) := FlaggedStates.flagBlock X (0 : CMat O)
  have hB : B.PosSemidef := FlaggedStates.flagBlock_posSemidef hX Matrix.PosSemidef.zero
  have hW : Wᴴ * W = 1 := LogCompression.dilation_isometry V hV
  have haction (Z : CMat I) :
      Wᴴ * FlaggedStates.flagBlock Z (0 : CMat O) * W = Vᴴ * Z * V := by
    have hh := LogCompression.dilation_block_action V Z (0 : CMat O)
    simpa only [LogCompression.compression_apply, Matrix.mul_zero, Matrix.zero_mul,
      add_zero] using hh
  have hblock : matrixRpow B q =
      FlaggedStates.flagBlock (matrixRpow X q) (0 : CMat O) := by
    change cfc (fun x : ℝ => Real.rpow x q) (FlaggedStates.flagBlock X (0 : CMat O)) = _
    rw [FlaggedStates.cfc_flagBlock _ hX.1 Matrix.isHermitian_zero]
    change FlaggedStates.flagBlock (matrixRpow X q) (matrixRpow (0 : CMat O) q) = _
    rw [matrixRpow_zero (ne_of_gt hq0)]
  have hJ := matrixRpow_isometry_compression_ge hB hW hq0.le hq1
  change (matrixRpow (Wᴴ * B * W) q - Wᴴ * matrixRpow B q * W).PosSemidef at hJ
  have hBX : Wᴴ * B * W = Vᴴ * X * V := haction X
  rw [hBX, hblock, haction] at hJ
  exact hJ

theorem matrixRpow_contraction_mono (V : Matrix I O ℂ)
    (hV : (1 - Vᴴ * V).PosSemidef) {X : CMat I} {Y : CMat O}
    (hX : X.PosSemidef) (hY : Y.PosSemidef)
    (hXY : (Y - Vᴴ * X * V).PosSemidef) {q : ℝ}
    (hq0 : 0 < q) (hq1 : q ≤ 1) :
    (matrixRpow Y q - Vᴴ * matrixRpow X q * V).PosSemidef := by
  have hJ := matrixRpow_contraction_jensen V hV hX hq0 hq1
  have hM := matrixRpow_loewner_mono (hX.conjTranspose_mul_mul_same V) hY hXY hq0.le hq1
  have hs := hM.add hJ
  simpa only [sub_add_sub_cancel] using hs

end QuantumProver.PetzPowerCompression

import QuantumProver.InformationTheory.BellDiagonalSquashedEntanglement.ExtensionIdentities
import QuantumProver.InformationTheory.SuperchannelDiscrimination.TestingTheorems
import QuantumProver.LinearAlgebra.SandwichedDPI.TraceNorm
import QuantumProver.InformationTheory.DepolarizingSquashedEntanglement.Definitions
import QuantumProver.InformationTheory.SuperchannelDiscrimination.QuantumTestingPowerBound
import QuantumProver.InformationTheory.DepolarizingSquashedEntanglement.BCYRedistributionCode
import QuantumProver.InformationTheory.DepolarizingSquashedEntanglement.BCYRedistributionResources
import QuantumProver.InformationTheory.ConditionalTypicalSmoothing

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

noncomputable section

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker

namespace QuantumProver.QuantumRedistributionRealization

open QuantumProver.SuperchannelDiscrimination
open QuantumProver.BellDiagonalSquashedEntanglement

variable {I O J K R : Type*}
  [Fintype I] [Fintype O] [Fintype J] [Fintype K] [Fintype R]
  [DecidableEq I] [DecidableEq O] [DecidableEq J] [DecidableEq K]
  [DecidableEq R]

def krausChannel {κ : Type*} [Fintype κ] (L : κ → Matrix O I ℂ)
    (hL : KrausCompletion.krausGram L = 1) : QuantumProver.DepolarizingSquashedEntanglement.CPTP I O where
  map := KrausCompletion.krausMap L
  completelyPositive := by
    intro n A hA
    have h := KrausCompletion.krausMap_completelyPositive L (Fin n)
      (hA.submatrix (Equiv.prodComm I (Fin n)))
    convert h.submatrix (Equiv.prodComm (Fin n) O) using 1
    ext i j
    rfl
  tracePreserving := KrausCompletion.krausAction_tracePreserving L hL

def isometryChannel (V : Matrix O I ℂ) (hV : Vᴴ * V = 1) : QuantumProver.DepolarizingSquashedEntanglement.CPTP I O :=
  krausChannel (fun _ : Unit => V) (by simpa [KrausCompletion.krausGram] using hV)

theorem isometryChannel_action (V : Matrix O I ℂ) (hV : Vᴴ * V = 1)
    (A : Matrix I I ℂ) : (isometryChannel V hV).map A = V * A * Vᴴ := by
  simp [isometryChannel, krausChannel, KrausCompletion.krausMap, KrausCompletion.krausAction]

theorem image_deficit_posSemidef (V : Matrix O I ℂ) (hV : Vᴴ * V = 1) :
    (1 - V * Vᴴ).PosSemidef := by
  have hP : (V * Vᴴ) * (V * Vᴴ) = V * Vᴴ := by
    calc
      _ = V * (Vᴴ * V) * Vᴴ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hV, Matrix.mul_one]
  have hH : (1 - V * Vᴴ)ᴴ * (1 - V * Vᴴ) = 1 - V * Vᴴ := by
    simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_one,
      Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hP]
    abel
  rw [← hH]
  exact Matrix.posSemidef_conjTranspose_mul_self _

def imageRetractionKraus (V : Matrix O I ℂ) (i₀ : I) :
    Unit ⊕ O → Matrix I O ℂ :=
  Sum.elim (fun _ => Vᴴ) (KrausCompletion.repairKraus i₀ (1 - V * Vᴴ))

theorem imageRetractionKraus_complete (V : Matrix O I ℂ)
    (hV : Vᴴ * V = 1) (i₀ : I) :
    KrausCompletion.krausGram (imageRetractionKraus V i₀) = 1 := by
  have h := KrausCompletion.repairKraus_gram i₀ (image_deficit_posSemidef V hV)
  change (∑ k : Unit ⊕ O, (imageRetractionKraus V i₀ k)ᴴ *
      imageRetractionKraus V i₀ k) = 1
  simp only [Fintype.sum_sum_type, imageRetractionKraus, Sum.elim_inl,
    Sum.elim_inr, Fintype.sum_unique, Matrix.conjTranspose_conjTranspose]
  change V * Vᴴ + KrausCompletion.krausGram (KrausCompletion.repairKraus i₀ (1 - V * Vᴴ)) = 1
  rw [h]
  abel

def imageRetraction (V : Matrix O I ℂ) (hV : Vᴴ * V = 1)
    (i₀ : I) : QuantumProver.DepolarizingSquashedEntanglement.CPTP O I :=
  krausChannel (imageRetractionKraus V i₀) (imageRetractionKraus_complete V hV i₀)

theorem imageRetraction_action (V : Matrix O I ℂ) (hV : Vᴴ * V = 1)
    (i₀ : I) (A : Matrix O O ℂ) :
    (imageRetraction V hV i₀).map A = Vᴴ * A * V +
      ((1 - V * Vᴴ) * A).trace • Matrix.single i₀ i₀ (1 : ℂ) := by
  change KrausCompletion.krausAction (imageRetractionKraus V i₀) A = _
  simp only [KrausCompletion.krausAction, imageRetractionKraus, Fintype.sum_sum_type,
    Sum.elim_inl, Sum.elim_inr, Fintype.sum_unique,
    Matrix.conjTranspose_conjTranspose]
  rw [← KrausCompletion.krausAction, KrausCompletion.repairKraus_action i₀ (image_deficit_posSemidef V hV)]

theorem imageRetraction_left_inverse (V : Matrix O I ℂ) (hV : Vᴴ * V = 1)
    (i₀ : I) (A : Matrix I I ℂ) :
    (imageRetraction V hV i₀).map (V * A * Vᴴ) = A := by
  have hz : (1 - V * Vᴴ) * V = 0 := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hV, Matrix.mul_one]
    exact sub_self _
  rw [imageRetraction_action]
  have hgood : Vᴴ * (V * A * Vᴴ) * V = A := by
    calc
      _ = (Vᴴ * V) * A * (Vᴴ * V) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hV, Matrix.one_mul, Matrix.mul_one]
  have hbad : (1 - V * Vᴴ) * (V * A * Vᴴ) = 0 := by
    calc
      _ = ((1 - V * Vᴴ) * V) * A * Vᴴ := by simp only [Matrix.mul_assoc]
      _ = 0 := by rw [hz, Matrix.zero_mul, Matrix.zero_mul]
  rw [hgood, hbad, Matrix.trace_zero, zero_smul, add_zero]

def embeddingMatrix (e : I ↪ O) : Matrix O I ℂ :=
  fun o i => if e i = o then 1 else 0

theorem embeddingMatrix_isometry (e : I ↪ O) :
    (embeddingMatrix e)ᴴ * embeddingMatrix e = 1 := by
  ext i j
  simp [Matrix.mul_apply, embeddingMatrix, Matrix.conjTranspose_apply,
    apply_ite, ite_mul, eq_comm, e.injective.eq_iff, Matrix.one_apply]

theorem exists_rectangular_polar_isometry (M : Matrix O I ℂ)
    (hcard : Fintype.card I ≤ Fintype.card O) :
    ∃ V : Matrix O I ℂ, Vᴴ * V = 1 ∧ M = V * CFC.sqrt (Mᴴ * M) := by
  obtain ⟨e : I ↪ O⟩ := Function.Embedding.nonempty_of_card_le hcard
  let J : Matrix O I ℂ := embeddingMatrix e
  let S := CFC.sqrt (Mᴴ * M)
  have hJ : Jᴴ * J = 1 := embeddingMatrix_isometry e
  have hS : Sᴴ = S := (CFC.sqrt_nonneg (Mᴴ * M)).posSemidef.isHermitian.eq
  have hG : (J * S)ᴴ * (J * S) = Mᴴ * M := by
    rw [Matrix.conjTranspose_mul, hS]
    calc
      _ = S * (Jᴴ * J) * S := by simp only [Matrix.mul_assoc]
      _ = _ := by
        rw [hJ, Matrix.mul_one]
        exact CFC.sqrt_mul_sqrt_self _ (Matrix.posSemidef_conjTranspose_mul_self M).nonneg
  obtain ⟨U, hU, hM⟩ := Geometry.exists_unitary_mul_of_gram_eq (J * S) M hG
  have hUnit : Uᴴ * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hU
  refine ⟨U * J, ?_, ?_⟩
  · rw [Matrix.conjTranspose_mul]
    calc
      _ = Jᴴ * (Uᴴ * U) * J := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hUnit, Matrix.mul_one, hJ]
  · simpa only [Matrix.mul_assoc] using hM

def completedContractionKraus (V : Matrix O I ℂ) (o₀ : O) :
    Unit ⊕ I → Matrix O I ℂ :=
  Sum.elim (fun _ => V) (KrausCompletion.repairKraus o₀ (1 - Vᴴ * V))

theorem completedContractionKraus_complete (V : Matrix O I ℂ)
    (hV : (1 - Vᴴ * V).PosSemidef) (o₀ : O) :
    KrausCompletion.krausGram (completedContractionKraus V o₀) = 1 := by
  have h := KrausCompletion.repairKraus_gram o₀ hV
  change (∑ k : Unit ⊕ I, (completedContractionKraus V o₀ k)ᴴ *
      completedContractionKraus V o₀ k) = 1
  simp only [Fintype.sum_sum_type, completedContractionKraus, Sum.elim_inl,
    Sum.elim_inr, Fintype.sum_unique]
  change Vᴴ * V + KrausCompletion.krausGram
    (KrausCompletion.repairKraus o₀ (1 - Vᴴ * V)) = 1
  rw [h]
  abel

def completedContraction (V : Matrix O I ℂ)
    (hV : (1 - Vᴴ * V).PosSemidef) (o₀ : O) : QuantumProver.DepolarizingSquashedEntanglement.CPTP I O :=
  krausChannel (completedContractionKraus V o₀)
    (completedContractionKraus_complete V hV o₀)

theorem completedContraction_action (V : Matrix O I ℂ)
    (hV : (1 - Vᴴ * V).PosSemidef) (o₀ : O) (A : Matrix I I ℂ) :
    (completedContraction V hV o₀).map A = V * A * Vᴴ +
      ((1 - Vᴴ * V) * A).trace • Matrix.single o₀ o₀ (1 : ℂ) := by
  change KrausCompletion.krausAction (completedContractionKraus V o₀) A = _
  simp only [KrausCompletion.krausAction, completedContractionKraus,
    Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Fintype.sum_unique]
  rw [← KrausCompletion.krausAction, KrausCompletion.repairKraus_action o₀ hV]

theorem traceNorm_unitary_left (U X : Matrix I I ℂ)
    (hU : U ∈ Matrix.unitaryGroup I ℂ) : traceNorm (U * X) = traceNorm X := by
  have hu : Uᴴ * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hU
  have hg : (U * X)ᴴ * (U * X) = Xᴴ * X := by
    rw [Matrix.conjTranspose_mul]
    calc
      _ = Xᴴ * (Uᴴ * U) * X := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hu, Matrix.mul_one]
  simp only [traceNorm, hg]

theorem traceNorm_unitary_right (X U : Matrix I I ℂ)
    (hU : U ∈ Matrix.unitaryGroup I ℂ) : traceNorm (X * U) = traceNorm X := by
  have hu : U * Uᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hU
  have hg : (X * U) * (X * U)ᴴ = X * Xᴴ := by
    rw [Matrix.conjTranspose_mul]
    calc
      _ = X * (U * Uᴴ) * Xᴴ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hu, Matrix.mul_one]
  change (CFC.sqrt ((X * U)ᴴ * (X * U))).trace.re = _
  rw [Geometry.absolute_trace_left_right_gram, hg]
  exact (Geometry.absolute_trace_left_right_gram X).symm

theorem traceNorm_factor_overlap (C D : Matrix I O ℂ) :
    traceNorm (Cᴴ * D) = rootFidelity (C * Cᴴ) (D * Dᴴ) := by
  let A := C * Cᴴ
  let B := D * Dᴴ
  let P : Matrix (I ⊕ O) I ℂ :=
    RecoveryGeometry.UhlmannGeometry.leftEmbedding
  let Q : Matrix (I ⊕ O) O ℂ :=
    RecoveryGeometry.UhlmannGeometry.rightEmbedding
  let M := CFC.sqrt A * CFC.sqrt B
  have hP : Pᴴ * P = 1 :=
    RecoveryGeometry.UhlmannGeometry.leftEmbedding_isometry
  have hQ : Qᴴ * Q = 1 :=
    RecoveryGeometry.UhlmannGeometry.rightEmbedding_isometry
  have hA : A.PosSemidef := Matrix.posSemidef_self_mul_conjTranspose C
  have hB : B.PosSemidef := Matrix.posSemidef_self_mul_conjTranspose D
  have hsA : (CFC.sqrt A)ᴴ = CFC.sqrt A := (CFC.sqrt_nonneg A).posSemidef.isHermitian.eq
  have hsB : (CFC.sqrt B)ᴴ = CFC.sqrt B := (CFC.sqrt_nonneg B).posSemidef.isHermitian.eq
  have hSA : (P * CFC.sqrt A)ᴴ * (P * CFC.sqrt A) = A := by
    rw [Matrix.conjTranspose_mul, hsA]
    calc
      _ = CFC.sqrt A * (Pᴴ * P) * CFC.sqrt A := by simp only [Matrix.mul_assoc]
      _ = A := by rw [hP, Matrix.mul_one, CFC.sqrt_mul_sqrt_self A hA.nonneg]
  have hSB : (P * CFC.sqrt B)ᴴ * (P * CFC.sqrt B) = B := by
    rw [Matrix.conjTranspose_mul, hsB]
    calc
      _ = CFC.sqrt B * (Pᴴ * P) * CFC.sqrt B := by simp only [Matrix.mul_assoc]
      _ = B := by rw [hP, Matrix.mul_one, CFC.sqrt_mul_sqrt_self B hB.nonneg]
  have hC : (Q * Cᴴ)ᴴ * (Q * Cᴴ) = A := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    calc
      _ = C * (Qᴴ * Q) * Cᴴ := by simp only [Matrix.mul_assoc]
      _ = A := by rw [hQ, Matrix.mul_one]
  have hD : (Q * Dᴴ)ᴴ * (Q * Dᴴ) = B := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    calc
      _ = D * (Qᴴ * Q) * Dᴴ := by simp only [Matrix.mul_assoc]
      _ = B := by rw [hQ, Matrix.mul_one]
  obtain ⟨U, hU, hCU⟩ := Geometry.exists_unitary_mul_of_gram_eq
    (P * CFC.sqrt A) (Q * Cᴴ) (hSA.trans hC.symm)
  obtain ⟨W, hW, hDW⟩ := Geometry.exists_unitary_mul_of_gram_eq
    (P * CFC.sqrt B) (Q * Dᴴ) (hSB.trans hD.symm)
  have hWs : Wᴴ ∈ Matrix.unitaryGroup (I ⊕ O) ℂ := by
    apply Matrix.mem_unitaryGroup_iff'.mpr
    simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose] using
      Matrix.mem_unitaryGroup_iff.mp hW
  have hf : Q * (Cᴴ * D) * Qᴴ = U * (P * M * Pᴴ) * Wᴴ := by
    calc
      _ = (Q * Cᴴ) * (Q * Dᴴ)ᴴ := by
        simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
          Matrix.mul_assoc]
      _ = _ := by
        rw [hCU, hDW, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hsB]
        simp only [M, Matrix.mul_assoc]
  calc
    _ = traceNorm (Q * (Cᴴ * D) * Qᴴ) :=
      (RecoveryGeometry.UhlmannGeometry.traceNorm_isometry Q hQ _).symm
    _ = traceNorm (U * (P * M * Pᴴ) * Wᴴ) := by rw [hf]
    _ = traceNorm (P * M * Pᴴ) := by
      rw [traceNorm_unitary_right _ _ hWs, traceNorm_unitary_left _ _ hU]
    _ = traceNorm M := RecoveryGeometry.UhlmannGeometry.traceNorm_isometry P hP M
    _ = _ := rfl

theorem exists_unitary_factor_alignment (C D : Matrix I O ℂ) :
    ∃ U : Matrix O O ℂ, U ∈ Matrix.unitaryGroup O ℂ ∧
      ((C * U)ᴴ * D).trace.re = rootFidelity (C * Cᴴ) (D * Dᴴ) := by
  obtain ⟨U, hU, htrace⟩ := Geometry.exists_unitary_trace_alignment (Cᴴ * D)
  refine ⟨U, hU, ?_⟩
  rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, htrace]
  exact traceNorm_factor_overlap C D

theorem rootFidelity_ge_one_sub_half_traceNorm (A B : Matrix I I ℂ)
    (hA : A.PosSemidef) (hB : B.PosSemidef)
    (htA : A.trace = 1) (htB : B.trace = 1) :
    1 - traceNorm (A - B) / 2 ≤ rootFidelity A B := by
  have ha := QuantumTestingPowerBound.audenaert_trace_power
    hA hB (1 / 2) (by norm_num) (by norm_num)
  have hhalf : (1 : ℝ) - 1 / 2 = 1 / 2 := by norm_num
  rw [hhalf, ← CFC.sqrt_eq_rpow, ← CFC.sqrt_eq_rpow, htA, Complex.one_re] at ha
  have hp := congrArg (fun X : Matrix I I ℂ => X.trace.re)
    (CFC.abs_add_self (A - B) (hA.isHermitian.sub hB.isHermitian).isSelfAdjoint)
  simp only [two_smul, Matrix.trace_add, Matrix.trace_sub, Complex.add_re,
    Complex.sub_re, htA, htB, Complex.one_re] at hp
  have hn : ‖(CFC.sqrt A * CFC.sqrt B).trace‖ ≤
      traceNorm (CFC.sqrt A * CFC.sqrt B) := by
    change ‖(CFC.sqrt A * CFC.sqrt B).trace‖ ≤
      (CFC.sqrt ((CFC.sqrt A * CFC.sqrt B)ᴴ *
        (CFC.sqrt A * CFC.sqrt B))).trace.re
    simpa only [Matrix.one_mul] using
      Geometry.norm_trace_unitary_mul_le_absolute_trace (CFC.sqrt A * CFC.sqrt B)
        (1 : Matrix I I ℂ) (by simp)
  have hr := (Complex.re_le_norm (CFC.sqrt A * CFC.sqrt B).trace).trans hn
  simp only [sub_self, add_zero, CFC.abs, Matrix.star_eq_conjTranspose] at hp
  change 1 - traceNorm (A - B) / 2 ≤ traceNorm (CFC.sqrt A * CFC.sqrt B)
  change traceNorm (A - B) = (A - B)⁺.trace.re + (A - B)⁺.trace.re at hp
  linarith

theorem norm_matrixVector_sq (C : Matrix I O ℂ) :
    ‖WithLp.toLp 2 (Geometry.matrixVector C)‖ ^ 2 = (C * Cᴴ).trace.re := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), Geometry.inner_matrixVector,
    Matrix.trace_mul_comm]
  rfl

theorem exists_unitary_factor_alignment_distance (C D : Matrix I O ℂ)
    (hC : (C * Cᴴ).trace = 1) (hD : (D * Dᴴ).trace = 1) :
    ∃ U : Matrix O O ℂ, U ∈ Matrix.unitaryGroup O ℂ ∧
      ‖WithLp.toLp 2 (Geometry.matrixVector (C * U)) -
        WithLp.toLp 2 (Geometry.matrixVector D)‖ ^ 2 ≤
          traceNorm (C * Cᴴ - D * Dᴴ) := by
  obtain ⟨U, hU, hi⟩ := exists_unitary_factor_alignment C D
  have hu : U * Uᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hU
  have ht : (C * U) * (C * U)ᴴ = C * Cᴴ := by
    rw [Matrix.conjTranspose_mul]
    calc
      _ = C * (U * Uᴴ) * Cᴴ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hu, Matrix.mul_one]
  have hnC : ‖WithLp.toLp 2 (Geometry.matrixVector (C * U))‖ ^ 2 = 1 := by
    rw [norm_matrixVector_sq, ht, hC, Complex.one_re]
  have hnD : ‖WithLp.toLp 2 (Geometry.matrixVector D)‖ ^ 2 = 1 := by
    rw [norm_matrixVector_sq, hD, Complex.one_re]
  have hn := norm_sub_sq (𝕜 := ℂ)
    (WithLp.toLp 2 (Geometry.matrixVector (C * U)))
    (WithLp.toLp 2 (Geometry.matrixVector D))
  rw [hnC, hnD, Geometry.inner_matrixVector] at hn
  change ‖WithLp.toLp 2 (Geometry.matrixVector (C * U)) -
    WithLp.toLp 2 (Geometry.matrixVector D)‖ ^ 2 =
      1 - 2 * ((C * U)ᴴ * D).trace.re + 1 at hn
  rw [hi] at hn
  have hf := rootFidelity_ge_one_sub_half_traceNorm (C * Cᴴ) (D * Dᴴ)
    (Matrix.posSemidef_self_mul_conjTranspose C)
    (Matrix.posSemidef_self_mul_conjTranspose D) hC hD
  refine ⟨U, hU, ?_⟩
  linarith

theorem unitary_corner_deficits (P : Matrix K O ℂ) (Q : Matrix K J ℂ)
    (hP : Pᴴ * P = 1) (hQ : Qᴴ * Q = 1)
    (U : Matrix K K ℂ) (hU : U ∈ Matrix.unitaryGroup K ℂ) :
    (1 - (Pᴴ * U * Q) * (Pᴴ * U * Q)ᴴ).PosSemidef ∧
      (1 - (Pᴴ * U * Q)ᴴ * (Pᴴ * U * Q)).PosSemidef := by
  have hu : U * Uᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hU
  have hus : Uᴴ * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hU
  have he₁ : 1 - (Pᴴ * U * Q) * (Pᴴ * U * Q)ᴴ =
      (Pᴴ * U) * (1 - Q * Qᴴ) * (Pᴴ * U)ᴴ := by
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one]
    calc
      _ = Pᴴ * (U * Uᴴ) * P -
          (Pᴴ * U * Q) * (Qᴴ * Uᴴ * P) := by
            rw [hu, Matrix.mul_one, hP]
            simp only [Matrix.mul_assoc]
      _ = _ := by simp only [Matrix.mul_assoc]
  have he₂ : 1 - (Pᴴ * U * Q)ᴴ * (Pᴴ * U * Q) =
      (Qᴴ * Uᴴ) * (1 - P * Pᴴ) * (Qᴴ * Uᴴ)ᴴ := by
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one]
    calc
      _ = Qᴴ * (Uᴴ * U) * Q -
          (Qᴴ * Uᴴ * P) * (Pᴴ * U * Q) := by
            rw [hus, Matrix.mul_one, hQ]
            simp only [Matrix.mul_assoc]
      _ = _ := by simp only [Matrix.mul_assoc]
  exact ⟨he₁ ▸ (image_deficit_posSemidef Q hQ).mul_mul_conjTranspose_same (Pᴴ * U),
    he₂ ▸ (image_deficit_posSemidef P hP).mul_mul_conjTranspose_same (Qᴴ * Uᴴ)⟩

theorem exists_cross_factor_alignment (C : Matrix I O ℂ) (D : Matrix I J ℂ) :
    ∃ V : Matrix J O ℂ,
      (1 - Vᴴ * V).PosSemidef ∧ (1 - V * Vᴴ).PosSemidef ∧
      ((C * Vᵀ)ᴴ * D).trace.re = rootFidelity (C * Cᴴ) (D * Dᴴ) := by
  let P : Matrix (O ⊕ J) O ℂ :=
    RecoveryGeometry.UhlmannGeometry.leftEmbedding
  let Q : Matrix (O ⊕ J) J ℂ :=
    RecoveryGeometry.UhlmannGeometry.rightEmbedding
  have hP : Pᴴ * P = 1 :=
    RecoveryGeometry.UhlmannGeometry.leftEmbedding_isometry
  have hQ : Qᴴ * Q = 1 :=
    RecoveryGeometry.UhlmannGeometry.rightEmbedding_isometry
  let C₀ := C * Pᴴ
  let D₀ := D * Qᴴ
  have hgC : C₀ * C₀ᴴ = C * Cᴴ := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    calc
      _ = C * (Pᴴ * P) * Cᴴ := by simp only [C₀, Matrix.mul_assoc]
      _ = _ := by rw [hP, Matrix.mul_one]
  have hgD : D₀ * D₀ᴴ = D * Dᴴ := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    calc
      _ = D * (Qᴴ * Q) * Dᴴ := by simp only [D₀, Matrix.mul_assoc]
      _ = _ := by rw [hQ, Matrix.mul_one]
  obtain ⟨U, hU, hi⟩ := exists_unitary_factor_alignment C₀ D₀
  rw [hgC, hgD] at hi
  let L := Pᴴ * U * Q
  have hL := unitary_corner_deficits P Q hP hQ U hU
  have ht₁ : 1 - (Lᵀ)ᴴ * Lᵀ = (1 - L * Lᴴ)ᵀ := by
    simp only [Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_mul,
      Matrix.conjTranspose_transpose_eq_transpose_conjTranspose]
  have ht₂ : 1 - Lᵀ * (Lᵀ)ᴴ = (1 - Lᴴ * L)ᵀ := by
    simp only [Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_mul,
      Matrix.conjTranspose_transpose_eq_transpose_conjTranspose]
  have heq : ((C * L)ᴴ * D).trace = ((C₀ * U)ᴴ * D₀).trace := by
    simp only [C₀, D₀, L, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose]
    calc
      _ = (Qᴴ * (Uᴴ * P * Cᴴ * D)).trace := by simp only [Matrix.mul_assoc]
      _ = ((Uᴴ * P * Cᴴ * D) * Qᴴ).trace := Matrix.trace_mul_comm _ _
      _ = _ := by simp only [Matrix.mul_assoc]
  refine ⟨Lᵀ, ?_, ?_, ?_⟩
  · rw [ht₁]
    exact hL.1.transpose
  · rw [ht₂]
    exact hL.2.transpose
  · rw [Matrix.transpose_transpose, heq]
    exact hi

theorem factor_corner_norm_sq_le (C : Matrix I O ℂ) (L : Matrix O J ℂ)
    (hL : (1 - L * Lᴴ).PosSemidef) :
    ‖WithLp.toLp 2 (Geometry.matrixVector (C * L))‖ ^ 2 ≤
      ‖WithLp.toLp 2 (Geometry.matrixVector C)‖ ^ 2 := by
  have h := Complex.re_le_re ((hL.mul_mul_conjTranspose_same C).trace_nonneg)
  have heq : C * (1 - L * Lᴴ) * Cᴴ = C * Cᴴ - (C * L) * (C * L)ᴴ := by
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one,
      Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [heq, Matrix.trace_sub, Complex.sub_re] at h
  simp only [Complex.zero_re] at h
  rw [norm_matrixVector_sq, norm_matrixVector_sq]
  linarith

theorem cross_factor_alignment_distance (C : Matrix I O ℂ) (D : Matrix I J ℂ)
    (hC : (C * Cᴴ).trace = 1) (hD : (D * Dᴴ).trace = 1)
    (V : Matrix J O ℂ) (hV : (1 - Vᴴ * V).PosSemidef)
    (hi : ((C * Vᵀ)ᴴ * D).trace.re = rootFidelity (C * Cᴴ) (D * Dᴴ)) :
    ‖WithLp.toLp 2 (Geometry.matrixVector (C * Vᵀ)) -
      WithLp.toLp 2 (Geometry.matrixVector D)‖ ≤
        Real.sqrt (traceNorm (C * Cᴴ - D * Dᴴ)) := by
  have hLt : (1 - Vᵀ * (Vᵀ)ᴴ).PosSemidef := by
    convert hV.transpose using 1
    simp only [Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_mul,
      Matrix.conjTranspose_transpose_eq_transpose_conjTranspose]
  have hnorm := factor_corner_norm_sq_le C Vᵀ hLt
  rw [norm_matrixVector_sq C, hC, Complex.one_re] at hnorm
  have hnD : ‖WithLp.toLp 2 (Geometry.matrixVector D)‖ ^ 2 = 1 := by
    rw [norm_matrixVector_sq, hD, Complex.one_re]
  have hn := norm_sub_sq (𝕜 := ℂ)
    (WithLp.toLp 2 (Geometry.matrixVector (C * Vᵀ)))
    (WithLp.toLp 2 (Geometry.matrixVector D))
  rw [hnD, Geometry.inner_matrixVector] at hn
  change ‖WithLp.toLp 2 (Geometry.matrixVector (C * Vᵀ)) -
    WithLp.toLp 2 (Geometry.matrixVector D)‖ ^ 2 =
      ‖WithLp.toLp 2 (Geometry.matrixVector (C * Vᵀ))‖ ^ 2 -
        2 * ((C * Vᵀ)ᴴ * D).trace.re + 1 at hn
  rw [hi] at hn
  have hf := rootFidelity_ge_one_sub_half_traceNorm (C * Cᴴ) (D * Dᴴ)
    (Matrix.posSemidef_self_mul_conjTranspose C)
    (Matrix.posSemidef_self_mul_conjTranspose D) hC hD
  have hδ : 0 ≤ traceNorm (C * Cᴴ - D * Dᴴ) := by
    exact (Complex.nonneg_iff.mp (CFC.sqrt_nonneg _).posSemidef.trace_nonneg).1
  have hs := Real.sq_sqrt hδ
  have hs0 := Real.sqrt_nonneg (traceNorm (C * Cᴴ - D * Dᴴ))
  nlinarith [norm_nonneg (WithLp.toLp 2 (Geometry.matrixVector (C * Vᵀ)) -
    WithLp.toLp 2 (Geometry.matrixVector D))]

theorem traceNorm_add_le (X Y : Matrix I I ℂ) :
    traceNorm (X + Y) ≤ traceNorm X + traceNorm Y := by
  obtain ⟨U, hU, hu⟩ := QuantumProver.SandwichedDPI.exists_unitary_traceNorm_attainer (X + Y)
  have hx := QuantumProver.SandwichedDPI.re_trace_unitary_mul_le_traceNorm X U hU
  have hy := QuantumProver.SandwichedDPI.re_trace_unitary_mul_le_traceNorm Y U hU
  simp only [QuantumProver.SandwichedDPI.traceNorm, CFC.abs, Matrix.star_eq_conjTranspose] at hu hx hy
  rw [Matrix.mul_add, Matrix.trace_add, Complex.add_re] at hu
  dsimp only [traceNorm]
  linarith

theorem traceNorm_neg (X : Matrix I I ℂ) : traceNorm (-X) = traceNorm X := by
  change (CFC.abs (-X)).trace.re = (CFC.abs X).trace.re
  rw [CFC.abs_neg]

theorem traceNorm_triangle (X Y Z : Matrix I I ℂ) :
    traceNorm (X - Z) ≤ traceNorm (X - Y) + traceNorm (Y - Z) := by
  simpa only [sub_add_sub_cancel] using traceNorm_add_le (X - Y) (Y - Z)

theorem norm_unitary_mulVec (U : Matrix I I ℂ)
    (hU : U ∈ Matrix.unitaryGroup I ℂ) (v : I → ℂ) :
    ‖WithLp.toLp 2 (U *ᵥ v)‖ = ‖WithLp.toLp 2 v‖ := by
  have hu : Uᴴ * U = (1 : Matrix I I ℂ)ᴴ * 1 := by
    simpa only [Matrix.conjTranspose_one, Matrix.one_mul, Matrix.star_eq_conjTranspose] using
      Matrix.mem_unitaryGroup_iff'.mp hU
  have h := Geometry.norm_toEuclideanLin_eq_of_gram_eq U 1 hu (WithLp.toLp 2 v)
  simpa only [Matrix.toLpLin_apply, WithLp.ofLp_toLp, Matrix.toLpLin_one,
    LinearMap.id_apply] using h

theorem traceNorm_rankOne_le (v w : I → ℂ) :
    traceNorm (Matrix.vecMulVec v (star w)) ≤
      ‖WithLp.toLp 2 v‖ * ‖WithLp.toLp 2 w‖ := by
  obtain ⟨U, hU, hu⟩ := QuantumProver.SandwichedDPI.exists_unitary_traceNorm_attainer
    (Matrix.vecMulVec v (star w))
  simp only [QuantumProver.SandwichedDPI.traceNorm, CFC.abs, Matrix.star_eq_conjTranspose] at hu
  have hi : (U * Matrix.vecMulVec v (star w)).trace =
      inner ℂ (WithLp.toLp 2 w) (WithLp.toLp 2 (U *ᵥ v)) := by
    rw [Matrix.mul_vecMulVec, Matrix.trace_vecMulVec]
    simp only [EuclideanSpace.inner_toLp_toLp]
  calc
    _ = (U * Matrix.vecMulVec v (star w)).trace.re := hu.symm
    _ ≤ ‖(U * Matrix.vecMulVec v (star w)).trace‖ := Complex.re_le_norm _
    _ = ‖inner ℂ (WithLp.toLp 2 w) (WithLp.toLp 2 (U *ᵥ v))‖ := by rw [hi]
    _ ≤ ‖WithLp.toLp 2 w‖ * ‖WithLp.toLp 2 (U *ᵥ v)‖ := norm_inner_le_norm _ _
    _ = _ := by rw [norm_unitary_mulVec U hU, mul_comm]

theorem traceNorm_pure_difference_le (v w : I → ℂ) :
    traceNorm (Geometry.pureMatrix v - Geometry.pureMatrix w) ≤
      (‖WithLp.toLp 2 v‖ + ‖WithLp.toLp 2 w‖) *
        ‖WithLp.toLp 2 v - WithLp.toLp 2 w‖ := by
  have heq : Geometry.pureMatrix v - Geometry.pureMatrix w =
      Matrix.vecMulVec (v - w) (star v) + Matrix.vecMulVec w (star (v - w)) := by
    ext i j
    simp only [Geometry.pureMatrix, Matrix.sub_apply,
      Matrix.add_apply, Matrix.vecMulVec_apply, Pi.sub_apply, Pi.star_apply, star_sub]
    ring
  rw [heq]
  have h₁ := traceNorm_rankOne_le (v - w) v
  have h₂ := traceNorm_rankOne_le w (v - w)
  have ht := traceNorm_add_le (Matrix.vecMulVec (v - w) (star v))
    (Matrix.vecMulVec w (star (v - w)))
  rw [WithLp.toLp_sub] at h₁ h₂
  nlinarith

theorem norm_isometry_mulVec (V : Matrix O I ℂ) (hV : Vᴴ * V = 1)
    (v : I → ℂ) : ‖WithLp.toLp 2 (V *ᵥ v)‖ = ‖WithLp.toLp 2 v‖ := by
  have hi := Geometry.inner_toEuclideanLin_self V (WithLp.toLp 2 v)
  rw [hV, Matrix.one_mulVec] at hi
  have hn : ‖WithLp.toLp 2 (V *ᵥ v)‖ ^ 2 = ‖WithLp.toLp 2 v‖ ^ 2 := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ), norm_sq_eq_re_inner (𝕜 := ℂ)]
    change (inner ℂ (WithLp.toLp 2 (V *ᵥ v)) (WithLp.toLp 2 (V *ᵥ v))).re =
      (inner ℂ (WithLp.toLp 2 v) (WithLp.toLp 2 v)).re
    simpa only [Matrix.toLpLin_apply, WithLp.ofLp_toLp,
      EuclideanSpace.inner_toLp_toLp, dotProduct_comm] using congrArg Complex.re hi
  nlinarith [norm_nonneg (WithLp.toLp 2 (V *ᵥ v)), norm_nonneg (WithLp.toLp 2 v)]

theorem pureMatrix_conjugation (V : Matrix O I ℂ) (v : I → ℂ) :
    Geometry.pureMatrix (V *ᵥ v) = V * Geometry.pureMatrix v * Vᴴ := by
  simp only [Geometry.pureMatrix, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul,
    ← Matrix.star_mulVec]

theorem traceNorm_traceRight_sub_le {κ : Type*} [Fintype κ] [DecidableEq κ]
    (A B : Matrix (O × κ) (O × κ) ℂ) (hA : A.PosSemidef) (hB : B.PosSemidef) :
    traceNorm (Geometry.traceRight A - Geometry.traceRight B) ≤ traceNorm (A - B) := by
  have h := EffectPerturbation.traceNorm_difference_contracts
    (partialTraceRightLM (I := O) (E := κ))
    (fun _ hp => partialTraceRight_posSemidef hp) partialTraceRight_trace
    hA.isHermitian hB.isHermitian
  change EffectPerturbation.traceNorm (partialTraceRight A - partialTraceRight B) ≤
    EffectPerturbation.traceNorm (A - B) at h
  change traceNorm (partialTraceRight A - partialTraceRight B) ≤ traceNorm (A - B)
  simpa only [traceNorm, EffectPerturbation.traceNorm, CFC.abs,
    Matrix.star_eq_conjTranspose] using h

section Instrument

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

def appendEmbedding (k₀ : κ) : O ↪ O × κ where
  toFun o := (o, k₀)
  inj' := by intro o p h; exact congrArg Prod.fst h

def basisAppendMatrix (k₀ : κ) : Matrix (O × κ) O ℂ :=
  fun q o => if q = (o, k₀) then 1 else 0

theorem basisAppendMatrix_isometry (k₀ : κ) :
    (basisAppendMatrix (O := O) k₀)ᴴ * basisAppendMatrix (O := O) k₀ = 1 := by
  have heq : basisAppendMatrix (O := O) k₀ = embeddingMatrix (appendEmbedding k₀) := by
    ext q o
    change (if q = (o, k₀) then (1 : ℂ) else 0) =
      (if (o, k₀) = q then 1 else 0)
    simp only [eq_comm]
  rw [heq]
  exact embeddingMatrix_isometry _

theorem basisAppendMatrix_krausDilation (L : κ → Matrix O I ℂ) (k₀ : κ) :
    (basisAppendMatrix (O := O) k₀)ᴴ * Geometry.krausDilation L = L k₀ := by
  ext o i
  simp [basisAppendMatrix, appendEmbedding, embeddingMatrix, Geometry.krausDilation,
    Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type,
    apply_ite, ite_mul, Prod.mk.injEq, eq_comm, Function.Embedding.coeFn_mk]

theorem traceRight_basisAppend (k₀ : κ) (A : Matrix O O ℂ) :
    Geometry.traceRight (basisAppendMatrix (O := O) k₀ * A *
      (basisAppendMatrix (O := O) k₀)ᴴ) = A := by
  apply Matrix.ext
  intro o p
  simp [Geometry.traceRight, basisAppendMatrix, appendEmbedding, embeddingMatrix,
    Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type,
    apply_ite, ite_mul, mul_ite, Prod.mk.injEq, eq_comm, Function.Embedding.coeFn_mk]
  symm
  calc
    _ = ∑ e : κ, if e = k₀ then A o p else 0 := by
      apply Finset.sum_congr rfl
      intro e he
      by_cases h : e = k₀
      · subst e
        simp [eq_comm]
      · simp [h, Ne.symm h]
    _ = A o p := by simp

theorem krausDilation_basis_overlap (L : κ → Matrix O I ℂ) (k₀ : κ)
    (v : I → ℂ) (w : O → ℂ) :
    inner ℂ (WithLp.toLp 2 (Geometry.krausDilation L *ᵥ v))
      (WithLp.toLp 2 (basisAppendMatrix k₀ *ᵥ w)) =
        inner ℂ (WithLp.toLp 2 (L k₀ *ᵥ v)) (WithLp.toLp 2 w) := by
  let T := Geometry.krausDilation L
  let E := basisAppendMatrix (O := O) k₀
  have hm : E.toEuclideanLin.adjoint.comp T.toEuclideanLin = (L k₀).toEuclideanLin := by
    rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint, ← Matrix.toLpLin_mul_same]
    exact congrArg (fun M => M.toEuclideanLin) (basisAppendMatrix_krausDilation L k₀)
  have hv := congrArg (fun f : EuclideanSpace ℂ I →ₗ[ℂ] EuclideanSpace ℂ O =>
    f (WithLp.toLp 2 v)) hm
  change E.toEuclideanLin.adjoint (T.toEuclideanLin (WithLp.toLp 2 v)) =
    (L k₀).toEuclideanLin (WithLp.toLp 2 v) at hv
  have hi := LinearMap.adjoint_inner_left E.toEuclideanLin
    (WithLp.toLp 2 w) (T.toEuclideanLin (WithLp.toLp 2 v))
  rw [hv] at hi
  simpa only [T, E, Matrix.toLpLin_apply, WithLp.ofLp_toLp] using hi.symm

theorem instrument_pure_error_le (L : κ → Matrix O I ℂ)
    (hL : KrausCompletion.krausGram L = 1) (k₀ : κ)
    (v : I → ℂ) (w : O → ℂ)
    (hv : ‖WithLp.toLp 2 v‖ = 1) (hw : ‖WithLp.toLp 2 w‖ = 1)
    (δ : ℝ) (hδ : 2 - 2 * (inner ℂ (WithLp.toLp 2 (L k₀ *ᵥ v))
      (WithLp.toLp 2 w)).re ≤ δ) :
    traceNorm (KrausCompletion.krausAction L (Geometry.pureMatrix v) -
      Geometry.pureMatrix w) ≤ 2 * Real.sqrt δ := by
  let T := Geometry.krausDilation L
  let E := basisAppendMatrix (O := O) k₀
  have hT : Tᴴ * T = 1 := Geometry.krausDilation_isometry L hL
  have hE : Eᴴ * E = 1 := basisAppendMatrix_isometry k₀
  have hTv : ‖WithLp.toLp 2 (T *ᵥ v)‖ = 1 := (norm_isometry_mulVec T hT v).trans hv
  have hEw : ‖WithLp.toLp 2 (E *ᵥ w)‖ = 1 := (norm_isometry_mulVec E hE w).trans hw
  have hn := Geometry.unit_norm_sub_sq (WithLp.toLp 2 (T *ᵥ v))
    (WithLp.toLp 2 (E *ᵥ w)) hTv hEw
  have hi := krausDilation_basis_overlap L k₀ v w
  change inner ℂ (WithLp.toLp 2 (T *ᵥ v)) (WithLp.toLp 2 (E *ᵥ w)) = _ at hi
  rw [hi] at hn
  have hsq : ‖WithLp.toLp 2 (T *ᵥ v) - WithLp.toLp 2 (E *ᵥ w)‖ ^ 2 ≤ δ := by
    rw [hn]
    exact hδ
  have hδ0 : 0 ≤ δ := (sq_nonneg _).trans hsq
  have hd : ‖WithLp.toLp 2 (T *ᵥ v) - WithLp.toLp 2 (E *ᵥ w)‖ ≤ Real.sqrt δ := by
    nlinarith [Real.sq_sqrt hδ0, Real.sqrt_nonneg δ,
      norm_nonneg (WithLp.toLp 2 (T *ᵥ v) - WithLp.toLp 2 (E *ᵥ w))]
  have hp := traceNorm_pure_difference_le (T *ᵥ v) (E *ᵥ w)
  rw [hTv, hEw] at hp
  have ht := traceNorm_traceRight_sub_le
    (Geometry.pureMatrix (T *ᵥ v)) (Geometry.pureMatrix (E *ᵥ w))
    (Geometry.pureMatrix_posSemidef _) (Geometry.pureMatrix_posSemidef _)
  rw [pureMatrix_conjugation, pureMatrix_conjugation,
    Geometry.traceRight_krausDilation, traceRight_basisAppend] at ht
  rw [← pureMatrix_conjugation T v, ← pureMatrix_conjugation E w] at ht
  exact ht.trans (hp.trans (by nlinarith))

end Instrument

section References

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

def referenceKraus (L : κ → Matrix O I ℂ) (R : Type*) [Fintype R] [DecidableEq R] :
    κ → Matrix (R × O) (R × I) ℂ := fun k => (1 : Matrix R R ℂ) ⊗ₖ L k

theorem referenceKraus_gram (L : κ → Matrix O I ℂ) :
    KrausCompletion.krausGram (referenceKraus L R) =
      (1 : Matrix R R ℂ) ⊗ₖ KrausCompletion.krausGram L := by
  simp only [KrausCompletion.krausGram, referenceKraus, Matrix.conjTranspose_kronecker,
    Matrix.conjTranspose_one, ← Matrix.mul_kronecker_mul, Matrix.one_mul]
  ext i j
  simp [Matrix.sum_apply, Matrix.kronecker_apply, Finset.mul_sum]

theorem referenceKraus_block (L : κ → Matrix O I ℂ) (k : κ)
    (A : Matrix (R × I) (R × I) ℂ) (r s : R) (o p : O) :
    (referenceKraus L R k * A * (referenceKraus L R k)ᴴ) (r,o) (s,p) =
      (L k * Matrix.of (fun i j => A (r,i) (s,j)) * (L k)ᴴ) o p := by
  simp [referenceKraus, Matrix.mul_apply, Matrix.kronecker_apply,
    Matrix.one_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type,
    apply_ite, mul_ite, ite_mul]

theorem referenceAmplify_kraus (L : κ → Matrix O I ℂ)
    (A : Matrix (R × I) (R × I) ℂ) :
    QuantumProver.DepolarizingSquashedEntanglement.amplify (KrausCompletion.krausMap L) A =
      KrausCompletion.krausAction (referenceKraus L R) A := by
  ext ⟨r,o⟩ ⟨s,p⟩
  change (∑ k, L k * Matrix.of (fun i j => A (r,i) (s,j)) * (L k)ᴴ) o p = _
  simp only [KrausCompletion.krausAction, Matrix.sum_apply, referenceKraus_block]

theorem referenceKraus_mulVec (L : κ → Matrix O I ℂ) (k : κ) (C : Matrix R I ℂ) :
    referenceKraus L R k *ᵥ Geometry.matrixVector C =
      Geometry.matrixVector (C * (L k)ᵀ) := by
  ext ⟨r,o⟩
  simp [referenceKraus, Geometry.matrixVector, Matrix.mulVec, dotProduct, Matrix.kronecker_apply,
    Matrix.one_apply, Fintype.sum_prod_type, Matrix.mul_apply, Matrix.transpose_apply,
    apply_ite, ite_mul, mul_ite, mul_comm]

end References

theorem completedContraction_pure_error_of_overlap (C : Matrix I O ℂ)
    (D : Matrix I J ℂ) (hC : (C * Cᴴ).trace = 1) (hD : (D * Dᴴ).trace = 1)
    (V : Matrix J O ℂ) (hV : (1 - Vᴴ * V).PosSemidef) (j₀ : J)
    (δ : ℝ) (hb : 2 - 2 * ((C * Vᵀ)ᴴ * D).trace.re ≤ δ) :
    traceNorm (QuantumProver.DepolarizingSquashedEntanglement.amplify (completedContraction V hV j₀).map
      (Geometry.pureMatrix (Geometry.matrixVector C)) -
        Geometry.pureMatrix (Geometry.matrixVector D)) ≤ 2 * Real.sqrt δ := by
  let L := referenceKraus (completedContractionKraus V j₀) I
  have hL : KrausCompletion.krausGram L = 1 := by
    rw [referenceKraus_gram, completedContractionKraus_complete V hV j₀,
      Matrix.one_kronecker_one]
  have hnC : ‖WithLp.toLp 2 (Geometry.matrixVector C)‖ = 1 := by
    have hs : ‖WithLp.toLp 2 (Geometry.matrixVector C)‖ ^ 2 = 1 := by
      rw [norm_matrixVector_sq, hC, Complex.one_re]
    nlinarith [norm_nonneg (WithLp.toLp 2 (Geometry.matrixVector C))]
  have hnD : ‖WithLp.toLp 2 (Geometry.matrixVector D)‖ = 1 := by
    have hs : ‖WithLp.toLp 2 (Geometry.matrixVector D)‖ ^ 2 = 1 := by
      rw [norm_matrixVector_sq, hD, Complex.one_re]
    nlinarith [norm_nonneg (WithLp.toLp 2 (Geometry.matrixVector D))]
  have hg : L (Sum.inl ()) *ᵥ Geometry.matrixVector C = Geometry.matrixVector (C * Vᵀ) :=
    referenceKraus_mulVec (completedContractionKraus V j₀) (Sum.inl ()) C
  have hbudget : 2 - 2 * (inner ℂ
      (WithLp.toLp 2 (L (Sum.inl ()) *ᵥ Geometry.matrixVector C))
      (WithLp.toLp 2 (Geometry.matrixVector D))).re ≤ δ := by
    rw [hg, Geometry.inner_matrixVector]
    exact hb
  have h := instrument_pure_error_le L hL (Sum.inl ())
    (Geometry.matrixVector C) (Geometry.matrixVector D) hnC hnD δ hbudget
  rw [← referenceAmplify_kraus] at h
  exact h

theorem reverse_factor_overlap_re (C : Matrix I O ℂ) (D : Matrix I J ℂ)
    (V : Matrix J O ℂ) :
    ((D * (Vᴴ)ᵀ)ᴴ * C).trace.re = ((C * Vᵀ)ᴴ * D).trace.re := by
  have hs : ((D * (Vᴴ)ᵀ)ᴴ * C).trace = star (((C * Vᵀ)ᴴ * D).trace) := by
    rw [← Matrix.trace_conjTranspose]
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.conjTranspose_transpose_eq_transpose_conjTranspose]
    calc
      _ = (Vᵀ * (Dᴴ * C)).trace := by simp only [Matrix.mul_assoc]
      _ = ((Dᴴ * C) * Vᵀ).trace := Matrix.trace_mul_comm _ _
      _ = _ := by simp only [Matrix.mul_assoc]
  rw [hs]
  rfl

theorem exists_uhlmann_completed_channels [Nonempty O] [Nonempty J]
    (C : Matrix I O ℂ) (D : Matrix I J ℂ)
    (hC : (C * Cᴴ).trace = 1) (hD : (D * Dᴴ).trace = 1) :
    ∃ forward : QuantumProver.DepolarizingSquashedEntanglement.CPTP O J,
      ∃ backward : QuantumProver.DepolarizingSquashedEntanglement.CPTP J O,
        traceNorm (QuantumProver.DepolarizingSquashedEntanglement.amplify forward.map
          (Geometry.pureMatrix (Geometry.matrixVector C)) -
            Geometry.pureMatrix (Geometry.matrixVector D)) ≤
          2 * Real.sqrt (traceNorm (C * Cᴴ - D * Dᴴ)) ∧
        traceNorm (QuantumProver.DepolarizingSquashedEntanglement.amplify backward.map
          (Geometry.pureMatrix (Geometry.matrixVector D)) -
            Geometry.pureMatrix (Geometry.matrixVector C)) ≤
          2 * Real.sqrt (traceNorm (C * Cᴴ - D * Dᴴ)) := by
  obtain ⟨V, hV, hVs, hi⟩ := exists_cross_factor_alignment C D
  let j₀ : J := Classical.arbitrary J
  let o₀ : O := Classical.arbitrary O
  have hvh : (1 - (Vᴴ)ᴴ * Vᴴ).PosSemidef := by
    simpa only [Matrix.conjTranspose_conjTranspose] using hVs
  have hb : 2 - 2 * ((C * Vᵀ)ᴴ * D).trace.re ≤ traceNorm (C * Cᴴ - D * Dᴴ) := by
    rw [hi]
    have h := rootFidelity_ge_one_sub_half_traceNorm (C * Cᴴ) (D * Dᴴ)
      (Matrix.posSemidef_self_mul_conjTranspose C)
      (Matrix.posSemidef_self_mul_conjTranspose D) hC hD
    linarith
  refine ⟨completedContraction V hV j₀, completedContraction Vᴴ hvh o₀, ?_, ?_⟩
  · exact completedContraction_pure_error_of_overlap C D hC hD V hV j₀ _ hb
  · apply completedContraction_pure_error_of_overlap D C hD hC Vᴴ hvh o₀
    rw [reverse_factor_overlap_re]
    exact hb

theorem channel_completelyPositive_matrix (Φ : QuantumProver.DepolarizingSquashedEntanglement.CPTP I O) :
    CPWrappers.CompletelyPositive Φ.map := by
  intro n A hA
  have h := Φ.completelyPositive n
    (A.submatrix (Equiv.prodComm (Fin n) I) (Equiv.prodComm (Fin n) I))
    (hA.submatrix (Equiv.prodComm (Fin n) I))
  convert h.submatrix (Equiv.prodComm O (Fin n)) using 1
  ext x y
  rfl

theorem traceNorm_channel_sub_le (Φ : QuantumProver.DepolarizingSquashedEntanglement.CPTP I O)
    (A B : Matrix I I ℂ) :
    traceNorm (Φ.map A - Φ.map B) ≤ traceNorm (A - B) := by
  rw [← map_sub]
  exact QuantumProver.SandwichedDPI.traceNorm_map_le_of_cp_tracePreserving
    (channel_completelyPositive_matrix Φ) Φ.tracePreserving (A - B)

theorem traceNorm_amplify_sub_le (Φ : QuantumProver.DepolarizingSquashedEntanglement.CPTP I O)
    (A B : Matrix (R × I) (R × I) ℂ) :
    traceNorm (QuantumProver.DepolarizingSquashedEntanglement.amplify Φ.map A -
      QuantumProver.DepolarizingSquashedEntanglement.amplify Φ.map B) ≤ traceNorm (A - B) :=
  traceNorm_channel_sub_le (QuantumProver.DepolarizingSquashedEntanglement.BCYRelativeEntropy.localRightChannel Φ) A B

def composeChannel (Φ : QuantumProver.DepolarizingSquashedEntanglement.CPTP I O)
    (Ψ : QuantumProver.DepolarizingSquashedEntanglement.CPTP O J) : QuantumProver.DepolarizingSquashedEntanglement.CPTP I J where
  map := Ψ.map.comp Φ.map
  completelyPositive := by
    intro n A hA
    have h := Ψ.completelyPositive n _ (Φ.completelyPositive n A hA)
    convert h using 1
    ext x y
    rfl
  tracePreserving := by
    intro A
    exact (Ψ.tracePreserving (Φ.map A)).trans (Φ.tracePreserving A)

theorem amplify_composeChannel (Φ : QuantumProver.DepolarizingSquashedEntanglement.CPTP I O)
    (Ψ : QuantumProver.DepolarizingSquashedEntanglement.CPTP O J) (A : Matrix (R × I) (R × I) ℂ) :
    QuantumProver.DepolarizingSquashedEntanglement.amplify (composeChannel Φ Ψ).map A =
      QuantumProver.DepolarizingSquashedEntanglement.amplify Ψ.map (QuantumProver.DepolarizingSquashedEntanglement.amplify Φ.map A) := by
  ext x y
  rfl

theorem exists_uhlmann_completed_roundtrip [Nonempty O] [Nonempty J]
    (C : Matrix I O ℂ) (D : Matrix I J ℂ)
    (hC : (C * Cᴴ).trace = 1) (hD : (D * Dᴴ).trace = 1) :
    ∃ forward : QuantumProver.DepolarizingSquashedEntanglement.CPTP O J,
      ∃ backward : QuantumProver.DepolarizingSquashedEntanglement.CPTP J O,
        traceNorm (QuantumProver.DepolarizingSquashedEntanglement.amplify forward.map
          (Geometry.pureMatrix (Geometry.matrixVector C)) -
            Geometry.pureMatrix (Geometry.matrixVector D)) ≤
          2 * Real.sqrt (traceNorm (C * Cᴴ - D * Dᴴ)) ∧
        traceNorm (QuantumProver.DepolarizingSquashedEntanglement.amplify (composeChannel forward backward).map
          (Geometry.pureMatrix (Geometry.matrixVector C)) -
            Geometry.pureMatrix (Geometry.matrixVector C)) ≤
          4 * Real.sqrt (traceNorm (C * Cᴴ - D * Dᴴ)) := by
  obtain ⟨forward, backward, hf, hb⟩ := exists_uhlmann_completed_channels C D hC hD
  refine ⟨forward, backward, hf, ?_⟩
  rw [amplify_composeChannel]
  have ht := traceNorm_triangle
    (QuantumProver.DepolarizingSquashedEntanglement.amplify backward.map
      (QuantumProver.DepolarizingSquashedEntanglement.amplify forward.map (Geometry.pureMatrix (Geometry.matrixVector C))))
    (QuantumProver.DepolarizingSquashedEntanglement.amplify backward.map (Geometry.pureMatrix (Geometry.matrixVector D)))
    (Geometry.pureMatrix (Geometry.matrixVector C))
  have hc := traceNorm_amplify_sub_le backward
    (QuantumProver.DepolarizingSquashedEntanglement.amplify forward.map (Geometry.pureMatrix (Geometry.matrixVector C)))
    (Geometry.pureMatrix (Geometry.matrixVector D))
  exact ht.trans (by linarith)

theorem traceNorm_partialTraceRight_sub_le
    (A B : Matrix (I × O) (I × O) ℂ) :
    traceNorm (QuantumProver.DepolarizingSquashedEntanglement.partialTraceRight A -
      QuantumProver.DepolarizingSquashedEntanglement.partialTraceRight B) ≤ traceNorm (A - B) :=
  traceNorm_channel_sub_le
    (QuantumProver.DepolarizingSquashedEntanglement.BCYRedistributionCode.discardRightChannel I O) A B

theorem traceNorm_reindex (e : I ≃ O) (A : Matrix I I ℂ) :
    traceNorm (Matrix.reindex e e A) = traceNorm A :=
  DiamondControl.nuclearNorm_submatrix_equiv e.symm A

def pureFactor (ψ : I × O → ℂ) : Matrix I O ℂ := Matrix.of fun i o => ψ (i,o)

theorem pureFactor_vector (ψ : I × O → ℂ) :
    Geometry.matrixVector (pureFactor ψ) = ψ := by
  ext ⟨i,o⟩
  rfl

theorem pureFactor_gram (ψ : I × O → ℂ) :
    pureFactor ψ * (pureFactor ψ)ᴴ =
      QuantumProver.DepolarizingSquashedEntanglement.partialTraceRight (QuantumProver.DepolarizingSquashedEntanglement.pureDensity ψ) := by
  ext i j
  simp [pureFactor, Matrix.mul_apply, Matrix.conjTranspose_apply,
    QuantumProver.DepolarizingSquashedEntanglement.partialTraceRight, QuantumProver.WernerEndpoint.partialTraceLeft,
    QuantumProver.DepolarizingSquashedEntanglement.pureDensity, QuantumProver.WernerEndpoint.pureDensity,
    QuantumProver.WernerEndpoint.crossDensity]

theorem pureFactor_normalized (ψ : I × O → ℂ)
    (hψ : QuantumProver.DepolarizingSquashedEntanglement.IsNormalized ψ) :
    (pureFactor ψ * (pureFactor ψ)ᴴ).trace = 1 := by
  rw [pureFactor_gram, QuantumProver.DepolarizingSquashedEntanglement.partialTraceRight_trace,
    QuantumProver.DepolarizingSquashedEntanglement.pureDensity, QuantumProver.WernerEndpoint.pureDensity_trace]
  change (QuantumProver.DepolarizingSquashedEntanglement.vectorNormSq ψ : ℂ) = 1
  rw [hψ]
  rfl

theorem pureMatrix_eq_pureDensity (ψ : I → ℂ) :
    Geometry.pureMatrix ψ = QuantumProver.DepolarizingSquashedEntanglement.pureDensity ψ := by
  ext x y
  rfl

theorem exists_pure_uhlmann_roundtrip [Nonempty O] [Nonempty J]
    (ψ : I × O → ℂ) (φ : I × J → ℂ)
    (hψ : QuantumProver.DepolarizingSquashedEntanglement.IsNormalized ψ) (hφ : QuantumProver.DepolarizingSquashedEntanglement.IsNormalized φ) :
    ∃ forward : QuantumProver.DepolarizingSquashedEntanglement.CPTP O J,
      ∃ backward : QuantumProver.DepolarizingSquashedEntanglement.CPTP J O,
        traceNorm (QuantumProver.DepolarizingSquashedEntanglement.amplify forward.map (QuantumProver.DepolarizingSquashedEntanglement.pureDensity ψ) -
          QuantumProver.DepolarizingSquashedEntanglement.pureDensity φ) ≤ 2 * Real.sqrt (traceNorm
          (QuantumProver.DepolarizingSquashedEntanglement.partialTraceRight (QuantumProver.DepolarizingSquashedEntanglement.pureDensity ψ) -
            QuantumProver.DepolarizingSquashedEntanglement.partialTraceRight (QuantumProver.DepolarizingSquashedEntanglement.pureDensity φ))) ∧
        traceNorm (QuantumProver.DepolarizingSquashedEntanglement.amplify (composeChannel forward backward).map
          (QuantumProver.DepolarizingSquashedEntanglement.pureDensity ψ) - QuantumProver.DepolarizingSquashedEntanglement.pureDensity ψ) ≤
          4 * Real.sqrt (traceNorm
          (QuantumProver.DepolarizingSquashedEntanglement.partialTraceRight (QuantumProver.DepolarizingSquashedEntanglement.pureDensity ψ) -
            QuantumProver.DepolarizingSquashedEntanglement.partialTraceRight (QuantumProver.DepolarizingSquashedEntanglement.pureDensity φ))) := by
  have h := exists_uhlmann_completed_roundtrip (pureFactor ψ) (pureFactor φ)
    (pureFactor_normalized ψ hψ) (pureFactor_normalized φ hφ)
  simpa only [pureFactor_vector, pureFactor_gram, pureMatrix_eq_pureDensity] using h

section CodeRealization

open QuantumProver.DepolarizingSquashedEntanglement
open QuantumProver.DepolarizingSquashedEntanglement.BCYRedistributionResources
open QuantumProver.DepolarizingSquashedEntanglement.BCYRedistributionCode
open QuantumProver.DepolarizingSquashedEntanglement.BCYRelativeEntropy
open QuantumProver.DepolarizingSquashedEntanglement.BCYNonlockability

variable {A B E C D F G T : Type*}
  [Fintype A] [Fintype B] [Fintype E] [Fintype C]
  [Fintype D] [Fintype F] [Fintype G] [Fintype T]
  [DecidableEq A] [DecidableEq B] [DecidableEq E] [DecidableEq C]
  [DecidableEq D] [DecidableEq F] [DecidableEq G] [DecidableEq T]

theorem traceNorm_discardReferenceLast_sub_le
    (M N : QMatrix ((R × D) × T)) :
    traceNorm (discardReferenceLast M - discardReferenceLast N) ≤ traceNorm (M - N) := by
  rw [discardReferenceLast_eq_partialTrace, discardReferenceLast_eq_partialTrace]
  have h := traceNorm_partialTraceRight_sub_le
    (Matrix.reindex (discardReferenceEquiv R D T) (discardReferenceEquiv R D T) M)
    (Matrix.reindex (discardReferenceEquiv R D T) (discardReferenceEquiv R D T) N)
  convert h using 1
  change traceNorm (M - N) = traceNorm (Matrix.reindex (discardReferenceEquiv R D T)
    (discardReferenceEquiv R D T) (M - N))
  exact (traceNorm_reindex _ _).symm

def discardCodeReferences (M : QMatrix (((A × C) × D) × T)) : QMatrix (A × T) :=
  discardReferenceLast (discardReferenceLast M)

theorem discardCodeReferences_amplify (Φ : QMatrix I →ₗ[ℂ] QMatrix O)
    (M : QMatrix (((A × C) × D) × I)) :
    discardCodeReferences (QuantumProver.DepolarizingSquashedEntanglement.amplify Φ M) =
      QuantumProver.DepolarizingSquashedEntanglement.amplify Φ (discardCodeReferences M) := by
  simp only [discardCodeReferences, discardReferenceLast_amplify]

theorem traceNorm_discardCodeReferences_sub_le
    (M N : QMatrix (((A × C) × D) × T)) :
    traceNorm (discardCodeReferences M - discardCodeReferences N) ≤ traceNorm (M - N) :=
  (traceNorm_discardReferenceLast_sub_le (discardReferenceLast M)
    (discardReferenceLast N)).trans (traceNorm_discardReferenceLast_sub_le M N)

def codeSourceDensity (ψ : (A × C) × (B × E) → ℂ) (hψ : IsNormalized ψ) :
    QuantumProver.DepolarizingSquashedEntanglement.Density (A × (B × E)) :=
  discardReferenceDensity (pureSourceDensity ψ hψ)

def codeTargetOutput (φ : ((A × C) × D) × ((E × F) × G) → ℂ) :
    QMatrix (A × ((E × F) × G)) := discardCodeReferences (pureDensity φ)

def codeTargetRetained (φ : ((A × C) × D) × ((E × F) × G) → ℂ) :
    QMatrix (A × (E × F)) :=
  QuantumProver.DepolarizingSquashedEntanglement.amplify (discardRightChannel (E × F) G).map (codeTargetOutput φ)

def codeFirstMarginalError [Nonempty D]
    (ψ : (A × C) × (B × E) → ℂ)
    (φ : ((A × C) × D) × ((E × F) × G) → ℂ) : ℝ :=
  traceNorm (QuantumProver.DepolarizingSquashedEntanglement.partialTraceRight (pureDensity ψ) ⊗ₖ (uniformDensity D).matrix -
    QuantumProver.DepolarizingSquashedEntanglement.partialTraceRight (pureDensity φ))

def codeRetainedTargetError [Nonempty F]
    (ψ : (A × C) × (B × E) → ℂ) (hψ : IsNormalized ψ)
    (φ : ((A × C) × D) × ((E × F) × G) → ℂ) : ℝ :=
  traceNorm (codeTargetRetained φ -
    (FiniteCode.reference (F := F) (codeSourceDensity ψ hψ)).matrix)

theorem codeSourceEPR_marginal [Nonempty D]
    (ψ : (A × C) × (B × E) → ℂ) (hψ : IsNormalized ψ) :
    discardCodeReferences (pureDensity (eprLift ψ D)) =
      (appendLocalDensity (codeSourceDensity ψ hψ) (uniformDensity D)).matrix := by
  rw [discardCodeReferences, eprLift_discardReference_amplify,
    discardReferenceLast_amplify]
  rfl

theorem exists_finiteCode_from_pure_target
    [Nonempty B] [Nonempty E] [Nonempty D] [Nonempty F] [Nonempty G]
    (ψ : (A × C) × (B × E) → ℂ) (hψ : IsNormalized ψ)
    (φ : ((A × C) × D) × ((E × F) × G) → ℂ) (hφ : IsNormalized φ) :
    ∃ code : FiniteCode B E D F G,
      traceNorm ((code.encoded (codeSourceDensity ψ hψ)).matrix - codeTargetOutput φ) ≤
          2 * Real.sqrt (codeFirstMarginalError ψ φ) ∧
        code.recoveryError (codeSourceDensity ψ hψ) ≤
          2 * Real.sqrt (codeFirstMarginalError ψ φ) ∧
        code.sideError (codeSourceDensity ψ hψ) ≤
          Real.sqrt (codeFirstMarginalError ψ φ) + codeRetainedTargetError ψ hψ φ / 2 := by
  let ρ := codeSourceDensity ψ hψ
  let ξ := eprLift ψ D
  obtain ⟨forward, backward, hf, hr⟩ := exists_pure_uhlmann_roundtrip ξ φ
    (eprLift_normalized ψ hψ) hφ
  rw [eprLift_leftMarginal] at hf hr
  change traceNorm (QuantumProver.DepolarizingSquashedEntanglement.amplify forward.map (pureDensity ξ) - pureDensity φ) ≤
    2 * Real.sqrt (codeFirstMarginalError ψ φ) at hf
  change traceNorm (QuantumProver.DepolarizingSquashedEntanglement.amplify (composeChannel forward backward).map
    (pureDensity ξ) - pureDensity ξ) ≤
    4 * Real.sqrt (codeFirstMarginalError ψ φ) at hr
  let discard := discardRightChannel (B × E) D
  let code : FiniteCode B E D F G :=
    ⟨forward, composeChannel backward discard⟩
  have hin : discardCodeReferences (pureDensity ξ) =
      (appendLocalDensity ρ (uniformDensity D)).matrix := codeSourceEPR_marginal ψ hψ
  have henc : (code.encoded ρ).matrix =
      discardCodeReferences (QuantumProver.DepolarizingSquashedEntanglement.amplify forward.map (pureDensity ξ)) := by
    rw [discardCodeReferences_amplify, hin]
    rfl
  have hfsmall : traceNorm ((code.encoded ρ).matrix - codeTargetOutput φ) ≤
      2 * Real.sqrt (codeFirstMarginalError ψ φ) := by
    rw [henc]
    exact (traceNorm_discardCodeReferences_sub_le _ _).trans hf
  have hrsmall : traceNorm (QuantumProver.DepolarizingSquashedEntanglement.amplify backward.map (code.encoded ρ).matrix -
      (appendLocalDensity ρ (uniformDensity D)).matrix) ≤
      4 * Real.sqrt (codeFirstMarginalError ψ φ) := by
    have h := traceNorm_discardCodeReferences_sub_le
      (QuantumProver.DepolarizingSquashedEntanglement.amplify (composeChannel forward backward).map (pureDensity ξ))
      (pureDensity ξ)
    rw [amplify_composeChannel, discardCodeReferences_amplify, ← henc, hin] at h
    exact h.trans hr
  have hdrop : QuantumProver.DepolarizingSquashedEntanglement.amplify discard.map
      (appendLocalDensity ρ (uniformDensity D)).matrix = ρ.matrix := by
    have h := local_discard_density (appendLocalDensity ρ (uniformDensity D))
    rw [discard_append_density] at h
    exact congrArg QuantumProver.DepolarizingSquashedEntanglement.Density.matrix h
  have hrec : traceNorm ((code.recovered ρ).matrix - ρ.matrix) ≤
      4 * Real.sqrt (codeFirstMarginalError ψ φ) := by
    change traceNorm (QuantumProver.DepolarizingSquashedEntanglement.amplify (composeChannel backward discard).map
      (code.encoded ρ).matrix - ρ.matrix) ≤ _
    rw [amplify_composeChannel, ← hdrop]
    exact (traceNorm_amplify_sub_le discard _ _).trans hrsmall
  have hretain : traceNorm ((code.retained ρ).matrix - codeTargetRetained φ) ≤
      2 * Real.sqrt (codeFirstMarginalError ψ φ) :=
    (traceNorm_amplify_sub_le (discardRightChannel (E × F) G)
      (code.encoded ρ).matrix (codeTargetOutput φ)).trans hfsmall
  have hside := traceNorm_triangle (code.retained ρ).matrix (codeTargetRetained φ)
    (FiniteCode.reference (F := F) ρ).matrix
  change _ ≤ _ + codeRetainedTargetError ψ hψ φ at hside
  refine ⟨code, hfsmall, ?_, ?_⟩
  · change traceNorm ((code.recovered ρ).matrix - ρ.matrix) / 2 ≤ _
    linarith
  · change traceNorm ((code.retained ρ).matrix -
      (FiniteCode.reference (F := F) ρ).matrix) / 2 ≤ _
    linarith

theorem codeSourceDensity_sourceWireKet
    (ρ : QuantumProver.DepolarizingSquashedEntanglement.Density (A × (B × E))) :
    codeSourceDensity (BCYPurification.sourceWireKet ρ)
      (BCYPurification.sourceWireKet_normalized ρ) = ρ := by
  apply density_ext
  exact sourceWire_discardPurifier ρ

theorem codeSourceDensity_sourceCopiesWireKet
    (ρ : QuantumProver.DepolarizingSquashedEntanglement.Density (A × (B × E))) (n : ℕ) :
    codeSourceDensity (BCYPurification.sourceCopiesWireKet ρ n)
      (BCYPurification.sourceCopiesWireKet_normalized ρ n) = tripleCopies ρ n := by
  classical
  apply density_ext
  exact sourceCopiesWire_discardPurifier ρ n

end CodeRealization

section PureCarrier

theorem norm_toLp_sq (v : I → ℂ) :
    ‖WithLp.toLp 2 v‖ ^ 2 = QuantumProver.DepolarizingSquashedEntanglement.vectorNormSq v := by
  simpa only [QuantumProver.DepolarizingSquashedEntanglement.vectorNormSq, QuantumProver.WernerEndpoint.vectorNormSq,
    Complex.sq_norm] using EuclideanSpace.norm_sq_eq (WithLp.toLp 2 v)

theorem norm_toLp_eq_one_of_normalized (v : I → ℂ)
    (hv : QuantumProver.DepolarizingSquashedEntanglement.IsNormalized v) : ‖WithLp.toLp 2 v‖ = 1 := by
  have hs : ‖WithLp.toLp 2 v‖ ^ 2 = 1 := (norm_toLp_sq v).trans hv
  nlinarith [norm_nonneg (WithLp.toLp 2 v)]

theorem normalized_of_norm_toLp_eq_one (v : I → ℂ) (hv : ‖WithLp.toLp 2 v‖ = 1) :
    QuantumProver.DepolarizingSquashedEntanglement.IsNormalized v := by
  change QuantumProver.DepolarizingSquashedEntanglement.vectorNormSq v = 1
  rw [← norm_toLp_sq, hv]
  norm_num

theorem pureMatrix_smul (c : ℂ) (v : I → ℂ) :
    Geometry.pureMatrix (c • v) = (c * star c) • Geometry.pureMatrix v := by
  ext i j
  simp only [Geometry.pureMatrix, Matrix.vecMulVec_apply, Pi.star_apply,
    Pi.smul_apply, smul_eq_mul, star_mul, Matrix.smul_apply]
  ring

theorem sqrt_inverse_mul_star {t : ℝ} (ht : 0 ≤ t) :
    (Real.sqrt t : ℂ)⁻¹ * star ((Real.sqrt t : ℂ)⁻¹) = (t⁻¹ : ℂ) := by
  rw [Complex.star_def, Complex.mul_conj, Complex.normSq_inv,
    Complex.normSq_ofReal, Real.mul_self_sqrt ht]
  simp only [Complex.ofReal_inv]

theorem pureMatrix_trace_normalized (v : I → ℂ)
    (hv : QuantumProver.DepolarizingSquashedEntanglement.IsNormalized v) : (Geometry.pureMatrix v).trace = 1 := by
  rw [pureMatrix_eq_pureDensity, QuantumProver.DepolarizingSquashedEntanglement.pureDensity,
    QuantumProver.WernerEndpoint.pureDensity_trace]
  change (QuantumProver.DepolarizingSquashedEntanglement.vectorNormSq v : ℂ) = 1
  rw [hv]
  rfl

def normalizedPureCrop (P : Matrix I I ℂ) (v : I → ℂ) : I → ℂ :=
  let t := (PetzSmoothing.cropMap P (Geometry.pureMatrix v)).trace.re
  if 0 < t then (Real.sqrt t : ℂ)⁻¹ • (P *ᵥ v) else v

theorem normalizedPureCrop_matrix (P : Matrix I I ℂ) (v : I → ℂ) :
    Geometry.pureMatrix (normalizedPureCrop P v) =
      ConditionalTypicalSmoothing.normalizedDoubleCrop 1 P (Geometry.pureMatrix v) := by
  have hd : ConditionalTypicalSmoothing.doubleCrop 1 P (Geometry.pureMatrix v) =
      PetzSmoothing.cropMap P (Geometry.pureMatrix v) := by
    simp [ConditionalTypicalSmoothing.doubleCrop, PetzSmoothing.cropMap_apply]
  rw [ConditionalTypicalSmoothing.normalizedDoubleCrop, hd, normalizedPureCrop]
  split_ifs with ht
  · rw [pureMatrix_smul, pureMatrix_conjugation, sqrt_inverse_mul_star ht.le]
    ext i j
    simp [Corollaries.positiveNormalize, PetzSmoothing.cropMap_apply, smul_eq_mul]
  · rfl

theorem normalizedPureCrop_isNormalized (P : Matrix I I ℂ) (v : I → ℂ)
    (hv : QuantumProver.DepolarizingSquashedEntanglement.IsNormalized v) :
    QuantumProver.DepolarizingSquashedEntanglement.IsNormalized (normalizedPureCrop P v) := by
  have hρ : FlaggedStates.IsDensity (Geometry.pureMatrix v) :=
    ⟨Geometry.pureMatrix_posSemidef v, pureMatrix_trace_normalized v hv⟩
  have h := ConditionalTypicalSmoothing.normalizedDoubleCrop_isDensity
    (P := (1 : Matrix I I ℂ)) (Q := P) hρ
  have ht : (Geometry.pureMatrix (normalizedPureCrop P v)).trace = 1 := by
    rw [normalizedPureCrop_matrix]
    exact h.2
  rw [pureMatrix_eq_pureDensity, QuantumProver.DepolarizingSquashedEntanglement.pureDensity,
    QuantumProver.WernerEndpoint.pureDensity_trace] at ht
  change QuantumProver.WernerEndpoint.vectorNormSq (normalizedPureCrop P v) = 1
  simpa only [Complex.ofReal_re, Complex.one_re] using congrArg Complex.re ht

theorem normalizedPureCrop_supported (P : Matrix I I ℂ)
    (hP : PetzSmoothing.IsProjection P) (v : I → ℂ)
    (ht : 0 < (PetzSmoothing.cropMap P (Geometry.pureMatrix v)).trace.re) :
    P *ᵥ normalizedPureCrop P v = normalizedPureCrop P v := by
  rw [normalizedPureCrop, if_pos ht, Matrix.mulVec_smul, Matrix.mulVec_mulVec,
    hP.idempotent]

theorem normalizedPureCrop_error (P : Matrix I I ℂ)
    (hP : PetzSmoothing.IsProjection P) (v : I → ℂ)
    (hv : QuantumProver.DepolarizingSquashedEntanglement.IsNormalized v) :
    traceNorm (Geometry.pureMatrix v - Geometry.pureMatrix (normalizedPureCrop P v)) ≤
      4 * Real.sqrt (1 - (Geometry.pureMatrix v * P).trace.re) := by
  have hρ : FlaggedStates.IsDensity (Geometry.pureMatrix v) :=
    ⟨Geometry.pureMatrix_posSemidef v, pureMatrix_trace_normalized v hv⟩
  have h1 : PetzSmoothing.IsProjection (1 : Matrix I I ℂ) := ⟨by simp, by simp⟩
  have hn := ConditionalTypicalSmoothing.normalizedDoubleCrop_error_le hρ h1 hP
  have hg := ConditionalTypicalSmoothing.crop_gentle hρ hP
  have hd : ConditionalTypicalSmoothing.doubleCrop 1 P (Geometry.pureMatrix v) =
      PetzSmoothing.cropMap P (Geometry.pureMatrix v) := by
    simp [ConditionalTypicalSmoothing.doubleCrop, PetzSmoothing.cropMap_apply]
  rw [← normalizedPureCrop_matrix, hd] at hn
  have h := hn.trans (mul_le_mul_of_nonneg_left hg (by norm_num : (0 : ℝ) ≤ 2))
  simpa only [traceNorm, ConditionalTypicalSmoothing.traceNorm, EffectPerturbation.traceNorm,
    CFC.abs, Matrix.star_eq_conjTranspose, ← mul_assoc,
    show (2 : ℝ) * 2 = 4 by norm_num] using h

theorem norm_mulVec_of_gram_support (M : Matrix O I ℂ) (v : I → ℂ)
    (hfix : (Mᴴ * M) *ᵥ v = v) :
    ‖WithLp.toLp 2 (M *ᵥ v)‖ = ‖WithLp.toLp 2 v‖ := by
  have hi := Geometry.inner_toEuclideanLin_self M (WithLp.toLp 2 v)
  simp only [WithLp.ofLp_toLp] at hi
  rw [hfix] at hi
  have hn : ‖WithLp.toLp 2 (M *ᵥ v)‖ ^ 2 = ‖WithLp.toLp 2 v‖ ^ 2 := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ), norm_sq_eq_re_inner (𝕜 := ℂ)]
    change (inner ℂ (WithLp.toLp 2 (M *ᵥ v)) (WithLp.toLp 2 (M *ᵥ v))).re =
      (inner ℂ (WithLp.toLp 2 v) (WithLp.toLp 2 v)).re
    simpa only [Matrix.toLpLin_apply, WithLp.ofLp_toLp,
      EuclideanSpace.inner_toLp_toLp, dotProduct_comm] using congrArg Complex.re hi
  nlinarith [norm_nonneg (WithLp.toLp 2 (M *ᵥ v)), norm_nonneg (WithLp.toLp 2 v)]

def compressedPureCrop (M : Matrix O I ℂ) (P : Matrix I I ℂ) (v : I → ℂ) : O → ℂ :=
  M *ᵥ normalizedPureCrop P v

theorem compressedPureCrop_isNormalized (M : Matrix O I ℂ) (P : Matrix I I ℂ)
    (hP : PetzSmoothing.IsProjection P) (hM : Mᴴ * M = P) (v : I → ℂ)
    (hv : QuantumProver.DepolarizingSquashedEntanglement.IsNormalized v)
    (ht : 0 < (PetzSmoothing.cropMap P (Geometry.pureMatrix v)).trace.re) :
    QuantumProver.DepolarizingSquashedEntanglement.IsNormalized (compressedPureCrop M P v) := by
  have hfix : (Mᴴ * M) *ᵥ normalizedPureCrop P v = normalizedPureCrop P v := by
    rw [hM]
    exact normalizedPureCrop_supported P hP v ht
  apply normalized_of_norm_toLp_eq_one
  change ‖WithLp.toLp 2 (M *ᵥ normalizedPureCrop P v)‖ = 1
  rw [norm_mulVec_of_gram_support M _ hfix]
  exact norm_toLp_eq_one_of_normalized _ (normalizedPureCrop_isNormalized P v hv)

theorem compressedPureCrop_uncompress (M : Matrix O I ℂ) (P : Matrix I I ℂ)
    (hP : PetzSmoothing.IsProjection P) (hM : Mᴴ * M = P) (v : I → ℂ)
    (ht : 0 < (PetzSmoothing.cropMap P (Geometry.pureMatrix v)).trace.re) :
    Mᴴ *ᵥ compressedPureCrop M P v = normalizedPureCrop P v := by
  rw [compressedPureCrop, Matrix.mulVec_mulVec, hM]
  exact normalizedPureCrop_supported P hP v ht

theorem completedContraction_supported_action (M : Matrix O I ℂ)
    (hM : (1 - Mᴴ * M).PosSemidef) (o₀ : O) (A : Matrix I I ℂ)
    (hA : (Mᴴ * M) * A = A) :
    (completedContraction M hM o₀).map A = M * A * Mᴴ := by
  have hz : (1 - Mᴴ * M) * A = 0 := by
    rw [Matrix.sub_mul, Matrix.one_mul, hA, sub_self]
  rw [completedContraction_action, hz, Matrix.trace_zero, zero_smul, add_zero]

theorem compressedPureCrop_channel_action (M : Matrix O I ℂ) (P : Matrix I I ℂ)
    (hP : PetzSmoothing.IsProjection P) (hM : Mᴴ * M = P) (o₀ : O) (v : I → ℂ)
    (ht : 0 < (PetzSmoothing.cropMap P (Geometry.pureMatrix v)).trace.re) :
    (completedContraction M (by rw [hM]; exact hP.complement.posSemidef) o₀).map
      (Geometry.pureMatrix (normalizedPureCrop P v)) =
        Geometry.pureMatrix (compressedPureCrop M P v) := by
  rw [completedContraction_supported_action, ← pureMatrix_conjugation]
  · rfl
  rw [hM, Geometry.pureMatrix, Matrix.mul_vecMulVec,
    normalizedPureCrop_supported P hP v ht]

end PureCarrier

section SenderPorts

variable {E : Type*} [Fintype E] [DecidableEq E]

def senderOperator (R : Type*) [Fintype R] [DecidableEq R]
    (M : Matrix O I ℂ) (E : Type*) [Fintype E] [DecidableEq E] :
    Matrix (R × (O × E)) (R × (I × E)) ℂ :=
  (1 : Matrix R R ℂ) ⊗ₖ (M ⊗ₖ (1 : Matrix E E ℂ))

def senderProjection (R : Type*) [Fintype R] [DecidableEq R]
    (P : Matrix I I ℂ) (E : Type*) [Fintype E] [DecidableEq E] :
    Matrix (R × (I × E)) (R × (I × E)) ℂ := senderOperator R P E

theorem senderProjection_isProjection (P : Matrix I I ℂ)
    (hP : PetzSmoothing.IsProjection P) :
    PetzSmoothing.IsProjection (senderProjection R P E) := by
  have hR : PetzSmoothing.IsProjection (1 : Matrix R R ℂ) := ⟨by simp, by simp⟩
  have hE : PetzSmoothing.IsProjection (1 : Matrix E E ℂ) := ⟨by simp, by simp⟩
  exact ConditionalTypicalSmoothing.localProjection_isProjection hR
    (ConditionalTypicalSmoothing.localProjection_isProjection hP hE)

theorem senderOperator_gram (M : Matrix O I ℂ) :
    (senderOperator R M E)ᴴ * senderOperator R M E =
      senderOperator R (Mᴴ * M) E := by
  simp only [senderOperator, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
    ← Matrix.mul_kronecker_mul, Matrix.one_mul]

theorem senderOperator_component (M : Matrix O I ℂ) (v : R × (I × E) → ℂ)
    (r : R) (o : O) (e : E) :
    (senderOperator R M E *ᵥ v) (r,(o,e)) = ∑ i, M o i * v (r,(i,e)) := by
  simp [senderOperator, Matrix.mulVec, dotProduct, Matrix.kronecker_apply,
    Matrix.one_apply, Fintype.sum_prod_type, apply_ite, ite_mul, mul_ite, eq_comm]

theorem senderCompression_gram (V : Matrix I O ℂ) (P : Matrix I I ℂ)
    (hV : V * Vᴴ = P) :
    (senderOperator R Vᴴ E)ᴴ * senderOperator R Vᴴ E = senderProjection R P E := by
  rw [senderOperator_gram, Matrix.conjTranspose_conjTranspose, hV]
  rfl

theorem senderCompressedCrop_isNormalized (V : Matrix I O ℂ) (P : Matrix I I ℂ)
    (hP : PetzSmoothing.IsProjection P) (hV : V * Vᴴ = P)
    (v : R × (I × E) → ℂ) (hv : QuantumProver.DepolarizingSquashedEntanglement.IsNormalized v)
    (ht : 0 < (PetzSmoothing.cropMap (senderProjection R P E)
      (Geometry.pureMatrix v)).trace.re) :
    QuantumProver.DepolarizingSquashedEntanglement.IsNormalized
      (compressedPureCrop (senderOperator R Vᴴ E) (senderProjection R P E) v) :=
  compressedPureCrop_isNormalized _ _ (senderProjection_isProjection P hP)
    (senderCompression_gram V P hV) v hv ht

theorem senderCompressedCrop_uncompress (V : Matrix I O ℂ) (P : Matrix I I ℂ)
    (hP : PetzSmoothing.IsProjection P) (hV : V * Vᴴ = P)
    (v : R × (I × E) → ℂ)
    (ht : 0 < (PetzSmoothing.cropMap (senderProjection R P E)
      (Geometry.pureMatrix v)).trace.re) :
    (senderOperator R Vᴴ E)ᴴ *ᵥ
      compressedPureCrop (senderOperator R Vᴴ E) (senderProjection R P E) v =
        normalizedPureCrop (senderProjection R P E) v :=
  compressedPureCrop_uncompress _ _ (senderProjection_isProjection P hP)
    (senderCompression_gram V P hV) v ht

def senderMarginal (v : R × (I × E) → ℂ) : Matrix I I ℂ :=
  QuantumProver.QuantumEntropy.partialTrace_right
    (QuantumProver.QuantumEntropy.partialTrace_left (Geometry.pureMatrix v))

theorem senderProjection_acceptance (P : Matrix I I ℂ) (v : R × (I × E) → ℂ) :
    (Geometry.pureMatrix v * senderProjection R P E).trace =
      (senderMarginal v * P).trace := by
  rw [senderProjection, senderOperator,
    QuantumProver.QuantumEntropy.partialTrace_left_mul_trace,
    QuantumProver.QuantumEntropy.partialTrace_right_mul_trace]
  rfl

theorem senderPureCrop_fixed (P : Matrix I I ℂ) (hP : PetzSmoothing.IsProjection P)
    (v : R × (I × E) → ℂ)
    (ht : 0 < (PetzSmoothing.cropMap (senderProjection R P E)
      (Geometry.pureMatrix v)).trace.re) :
    senderOperator R P E *ᵥ normalizedPureCrop (senderProjection R P E) v =
      normalizedPureCrop (senderProjection R P E) v :=
  normalizedPureCrop_supported _ (senderProjection_isProjection P hP) v ht

theorem senderPureCrop_error (P : Matrix I I ℂ) (hP : PetzSmoothing.IsProjection P)
    (v : R × (I × E) → ℂ) (hv : QuantumProver.DepolarizingSquashedEntanglement.IsNormalized v) :
    traceNorm (Geometry.pureMatrix v -
      Geometry.pureMatrix (normalizedPureCrop (senderProjection R P E) v)) ≤
      4 * Real.sqrt (1 - (senderMarginal v * P).trace.re) := by
  have h := normalizedPureCrop_error _ (senderProjection_isProjection P hP) v hv
  rw [senderProjection_acceptance] at h
  exact h

end SenderPorts

section PureCarrierLimits

open Filter
open scoped Topology

variable {ι : ℕ → Type*} [∀ n, Fintype (ι n)] [∀ n, DecidableEq (ι n)]

theorem normalizedPureCrop_error_tendsto_zero
    (P : (n : ℕ) → Matrix (ι n) (ι n) ℂ) (v : (n : ℕ) → ι n → ℂ)
    (hP : ∀ n, PetzSmoothing.IsProjection (P n))
    (hv : ∀ n, QuantumProver.DepolarizingSquashedEntanglement.IsNormalized (v n))
    (haccept : Tendsto (fun n => (Geometry.pureMatrix (v n) * P n).trace.re)
      atTop (𝓝 1)) :
    Tendsto (fun n => traceNorm (Geometry.pureMatrix (v n) -
      Geometry.pureMatrix (normalizedPureCrop (P n) (v n)))) atTop (𝓝 0) := by
  have h0 : Tendsto (fun n => 1 - (Geometry.pureMatrix (v n) * P n).trace.re)
      atTop (𝓝 0) := by
    simpa only [sub_self] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub haccept
  have hlim : Tendsto (fun n =>
      4 * Real.sqrt (1 - (Geometry.pureMatrix (v n) * P n).trace.re)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.sqrt_zero, mul_zero] using
      (Real.continuous_sqrt.continuousAt.tendsto.comp h0).const_mul 4
  exact squeeze_zero
    (fun n => (Complex.nonneg_iff.mp (CFC.sqrt_nonneg _).posSemidef.trace_nonneg).1)
    (fun n => normalizedPureCrop_error (P n) (hP n) (v n) (hv n)) hlim

theorem normalizedPureCrop_eventually_positive_mass
    (P : (n : ℕ) → Matrix (ι n) (ι n) ℂ) (v : (n : ℕ) → ι n → ℂ)
    (hP : ∀ n, PetzSmoothing.IsProjection (P n))
    (haccept : Tendsto (fun n => (Geometry.pureMatrix (v n) * P n).trace.re)
      atTop (𝓝 1)) :
    ∀ᶠ n in atTop, 0 < (PetzSmoothing.cropMap (P n) (Geometry.pureMatrix (v n))).trace.re := by
  have hpos := haccept.eventually (isOpen_Ioi.mem_nhds (show (0 : ℝ) < 1 by norm_num))
  filter_upwards [hpos] with n hn
  rw [PetzSmoothing.cropMap_trace (hP n)]
  exact hn

end PureCarrierLimits

def basisResetChannel (I O : Type*) [Fintype I] [Fintype O]
    [DecidableEq I] [DecidableEq O] [Nonempty O] : QuantumProver.DepolarizingSquashedEntanglement.CPTP I O :=
  completedContraction (0 : Matrix O I ℂ)
    (by simpa only [Matrix.conjTranspose_zero, Matrix.zero_mul, sub_zero] using
      (Matrix.PosSemidef.one (n := I) (R := ℂ))) (Classical.arbitrary O)

def fallbackFiniteCode (B E D F G : Type*)
    [Fintype B] [Fintype E] [Fintype D] [Fintype F] [Fintype G]
    [DecidableEq B] [DecidableEq E] [DecidableEq D] [DecidableEq F] [DecidableEq G]
    [Nonempty B] [Nonempty E] [Nonempty F] [Nonempty G] :
    QuantumProver.DepolarizingSquashedEntanglement.BCYRedistributionCode.FiniteCode B E D F G :=
  ⟨basisResetChannel ((B × E) × D) ((E × F) × G),
    basisResetChannel ((E × F) × G) (B × E)⟩

end QuantumProver.QuantumRedistributionRealization

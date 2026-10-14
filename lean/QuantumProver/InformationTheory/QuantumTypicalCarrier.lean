import QuantumProver.InformationTheory.QuantumTypicalProjectors
import QuantumProver.InformationTheory.QuantumRedistributionDimensions
import QuantumProver.LinearAlgebra.SandwichedDPI.TraceNorm

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option maxRecDepth 4000

noncomputable section

namespace QuantumProver.QuantumTypicalCarrier

open Matrix
open QuantumProver.SuperchannelDiscrimination
open FlaggedStates TensorEntropy
open scoped BigOperators ComplexOrder MatrixOrder Matrix Kronecker

variable {B D Y : Type*} [Fintype B] [Fintype D] [Fintype Y]
  [DecidableEq B] [DecidableEq D] [DecidableEq Y]

theorem supportProjection_eq_of_isProjection {P : Matrix B B ℂ}
    (hP : PetzSmoothing.IsProjection P) : supportProjection P = P := by
  classical
  let values := hP.selfAdjoint.eigenvalues
  let U := hP.selfAdjoint.eigenvectorUnitary
  let F := Unitary.conjStarAlgAut ℝ (Matrix B B ℂ) U
  let A := Matrix.diagonal (fun i => (values i : ℂ))
  have hs : P = F A := hP.selfAdjoint.spectral_theorem
  have hAA : A * A = A := by
    apply F.injective
    calc
      F (A * A) = F A * F A := map_mul F A A
      _ = P * P := congrArg₂ (fun X Z : Matrix B B ℂ => X * Z) hs.symm hs.symm
      _ = P := hP.idempotent
      _ = F A := hs
  have hEigen (i : B) : values i * values i = values i := by
    have hc : (values i : ℂ) * (values i : ℂ) = (values i : ℂ) := by
      simpa [A, Matrix.diagonal_mul_diagonal] using congrArg (fun M : Matrix B B ℂ => M i i) hAA
    have h := congrArg Complex.re hc
    simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero] using h
  have hf (i : B) : nonzeroWeight (values i) = values i := by
    have hz : values i * (values i - 1) = 0 := by nlinarith [hEigen i]
    rcases mul_eq_zero.mp hz with h0 | h1
    · simp [nonzeroWeight, h0]
    · have h1' : values i = 1 := by linarith
      simp [nonzeroWeight, h1']
  rw [supportProjection, PetzMoments.cfc_spectral _ hP.selfAdjoint]
  change F (Matrix.diagonal (fun i => (nonzeroWeight (values i) : ℂ))) = P
  simp only [hf]
  exact hs.symm

theorem projectionSupport_card {P : Matrix B B ℂ} (hP : PetzSmoothing.IsProjection P) :
    Fintype.card (OutputSupport.supportIndex hP.posSemidef) = P.rank := by
  let J := OutputSupport.supportIsometry hP.posSemidef
  have hgram : Jᴴ * J = 1 := OutputSupport.supportIsometry_gram hP.posSemidef
  have hproj : J * Jᴴ = P := by
    change OutputSupport.supportIsometry hP.posSemidef *
      (OutputSupport.supportIsometry hP.posSemidef)ᴴ = P
    rw [OutputSupport.supportIsometry_projection, supportProjection_eq_of_isProjection hP]
  calc
    Fintype.card (OutputSupport.supportIndex hP.posSemidef) = (Jᴴ * J).rank := by rw [hgram, Matrix.rank_one]
    _ = J.rank := Matrix.rank_conjTranspose_mul_self J
    _ = (J * Jᴴ).rank := (Matrix.rank_self_mul_conjTranspose J).symm
    _ = P.rank := congrArg Matrix.rank hproj

def projectionSupportChart (P : Matrix B B ℂ) (hP : PetzSmoothing.IsProjection P) :
    Fin P.rank ≃ OutputSupport.supportIndex hP.posSemidef :=
  (Fintype.equivFinOfCardEq (projectionSupport_card hP)).symm

def rankCarrier (P : Matrix B B ℂ) (hP : PetzSmoothing.IsProjection P) :
    Matrix B (Fin P.rank) ℂ :=
  (OutputSupport.supportIsometry hP.posSemidef).submatrix id (projectionSupportChart P hP)

theorem rankCarrier_gram (P : Matrix B B ℂ) (hP : PetzSmoothing.IsProjection P) :
    (rankCarrier P hP)ᴴ * rankCarrier P hP = 1 := by
  have h := OutputSupport.supportIsometry_gram hP.posSemidef
  ext i j
  have hx := congrArg (fun M => M (projectionSupportChart P hP i) (projectionSupportChart P hP j)) h
  simpa [rankCarrier, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply,
    (projectionSupportChart P hP).injective.eq_iff] using hx

theorem rankCarrier_projection (P : Matrix B B ℂ) (hP : PetzSmoothing.IsProjection P) :
    rankCarrier P hP * (rankCarrier P hP)ᴴ = P := by
  rw [rankCarrier, Matrix.conjTranspose_submatrix,
    Matrix.submatrix_mul_equiv, Matrix.submatrix_id_id,
    OutputSupport.supportIsometry_projection, supportProjection_eq_of_isProjection hP]

def coordinateEmbedding (e : B ↪ D) : Matrix D B ℂ :=
  fun d b => if e b = d then 1 else 0

theorem coordinateEmbedding_gram (e : B ↪ D) :
    (coordinateEmbedding e)ᴴ * coordinateEmbedding e = 1 := by
  ext i j
  simp [Matrix.mul_apply, coordinateEmbedding, Matrix.conjTranspose_apply,
    apply_ite, ite_mul, eq_comm, e.injective.eq_iff, Matrix.one_apply]

def paddingEmbedding (r d : ℕ) (hr : r ≤ d) : Matrix (Fin d) (Fin r) ℂ :=
  coordinateEmbedding (Fin.castLEEmb hr)

theorem paddingEmbedding_gram (r d : ℕ) (hr : r ≤ d) :
    (paddingEmbedding r d hr)ᴴ * paddingEmbedding r d hr = 1 :=
  coordinateEmbedding_gram _

def paddedCarrier (P : Matrix B B ℂ) (hP : PetzSmoothing.IsProjection P)
    (d : ℕ) (hr : P.rank ≤ d) : Matrix B (Fin d) ℂ :=
  rankCarrier P hP * (paddingEmbedding P.rank d hr)ᴴ

theorem paddedCarrier_projection (P : Matrix B B ℂ) (hP : PetzSmoothing.IsProjection P)
    (d : ℕ) (hr : P.rank ≤ d) :
    paddedCarrier P hP d hr * (paddedCarrier P hP d hr)ᴴ = P := by
  unfold paddedCarrier
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  calc
    (rankCarrier P hP * (paddingEmbedding P.rank d hr)ᴴ) *
        (paddingEmbedding P.rank d hr * (rankCarrier P hP)ᴴ) =
      rankCarrier P hP * ((paddingEmbedding P.rank d hr)ᴴ * paddingEmbedding P.rank d hr) *
        (rankCarrier P hP)ᴴ := by simp only [Matrix.mul_assoc]
    _ = P := by rw [paddingEmbedding_gram, Matrix.mul_one, rankCarrier_projection]

theorem paddedCarrier_gram (P : Matrix B B ℂ) (hP : PetzSmoothing.IsProjection P)
    (d : ℕ) (hr : P.rank ≤ d) :
    (paddedCarrier P hP d hr)ᴴ * paddedCarrier P hP d hr =
      paddingEmbedding P.rank d hr * (paddingEmbedding P.rank d hr)ᴴ := by
  unfold paddedCarrier
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  calc
    (paddingEmbedding P.rank d hr * (rankCarrier P hP)ᴴ) *
        (rankCarrier P hP * (paddingEmbedding P.rank d hr)ᴴ) =
      paddingEmbedding P.rank d hr * ((rankCarrier P hP)ᴴ * rankCarrier P hP) *
        (paddingEmbedding P.rank d hr)ᴴ := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [rankCarrier_gram, Matrix.mul_one]

theorem image_isProjection (U : Matrix B D ℂ) (hU : Uᴴ * U = 1) :
    PetzSmoothing.IsProjection (U * Uᴴ) := by
  constructor
  · change (U * Uᴴ)ᴴ = U * Uᴴ
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  · calc
      (U * Uᴴ) * (U * Uᴴ) = U * (Uᴴ * U) * Uᴴ := by simp only [Matrix.mul_assoc]
      _ = U * Uᴴ := by rw [hU, Matrix.mul_one]

theorem paddedCarrier_gram_isProjection (P : Matrix B B ℂ) (hP : PetzSmoothing.IsProjection P)
    (d : ℕ) (hr : P.rank ≤ d) :
    PetzSmoothing.IsProjection ((paddedCarrier P hP d hr)ᴴ * paddedCarrier P hP d hr) := by
  rw [paddedCarrier_gram]
  exact image_isProjection _ (paddingEmbedding_gram _ _ _)

theorem paddedCarrier_deficits (P : Matrix B B ℂ) (hP : PetzSmoothing.IsProjection P)
    (d : ℕ) (hr : P.rank ≤ d) :
    (1 - paddedCarrier P hP d hr * (paddedCarrier P hP d hr)ᴴ).PosSemidef ∧
    (1 - (paddedCarrier P hP d hr)ᴴ * paddedCarrier P hP d hr).PosSemidef := by
  constructor
  · rw [paddedCarrier_projection]
    exact hP.complement.posSemidef
  · exact (paddedCarrier_gram_isProjection P hP d hr).complement.posSemidef

def carrierLift (V : Matrix B D ℂ) (Y : Type*) [Fintype Y] [DecidableEq Y] :
    Matrix (B × Y) (D × Y) ℂ := V ⊗ₖ (1 : Matrix Y Y ℂ)

def carrierCompression (V : Matrix B D ℂ) (Y : Type*) [Fintype Y] [DecidableEq Y]
    (A : Matrix (B × Y) (B × Y) ℂ) : Matrix (D × Y) (D × Y) ℂ :=
  (carrierLift V Y)ᴴ * A * carrierLift V Y

def carrierUncompression (V : Matrix B D ℂ) (Y : Type*) [Fintype Y] [DecidableEq Y]
    (X : Matrix (D × Y) (D × Y) ℂ) : Matrix (B × Y) (B × Y) ℂ :=
  carrierLift V Y * X * (carrierLift V Y)ᴴ

def carrierSupport (P : Matrix B B ℂ) (A : Matrix (B × Y) (B × Y) ℂ) : Prop :=
  ((P ⊗ₖ (1 : Matrix Y Y ℂ)) * A = A) ∧ (A * (P ⊗ₖ (1 : Matrix Y Y ℂ)) = A)

theorem carrierLift_adjoint (V : Matrix B D ℂ) :
    (carrierLift V Y)ᴴ = Vᴴ ⊗ₖ (1 : Matrix Y Y ℂ) := by
  rw [carrierLift, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one]

theorem carrierLift_projection {V : Matrix B D ℂ} {P : Matrix B B ℂ}
    (hV : V * Vᴴ = P) :
    carrierLift V Y * (carrierLift V Y)ᴴ = P ⊗ₖ (1 : Matrix Y Y ℂ) := by
  rw [carrierLift, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
    ← Matrix.mul_kronecker_mul, hV, Matrix.one_mul]

theorem carrierLift_gram {V : Matrix B D ℂ} (hV : Vᴴ * V = 1) :
    (carrierLift V Y)ᴴ * carrierLift V Y = 1 := by
  rw [carrierLift, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
    ← Matrix.mul_kronecker_mul, hV, Matrix.one_mul, Matrix.one_kronecker_one]

theorem carrierSupport_of_left {P : Matrix B B ℂ} {A : Matrix (B × Y) (B × Y) ℂ}
    (hP : P.IsHermitian) (hA : A.IsHermitian)
    (hs : (P ⊗ₖ (1 : Matrix Y Y ℂ)) * A = A) : carrierSupport P A := by
  refine ⟨hs, ?_⟩
  have h := congrArg Matrix.conjTranspose hs
  simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_kronecker,
    Matrix.conjTranspose_one, hP.eq, hA.eq] using h

theorem carrierSupport_sub {P : Matrix B B ℂ} {A C : Matrix (B × Y) (B × Y) ℂ}
    (hA : carrierSupport P A) (hC : carrierSupport P C) : carrierSupport P (A - C) := by
  constructor
  · rw [Matrix.mul_sub, hA.1, hC.1]
  · rw [Matrix.sub_mul, hA.2, hC.2]

theorem carrierSupport_mul {P : Matrix B B ℂ} {A C : Matrix (B × Y) (B × Y) ℂ}
    (hA : carrierSupport P A) (hC : carrierSupport P C) : carrierSupport P (A * C) := by
  constructor
  · rw [← Matrix.mul_assoc, hA.1]
  · rw [Matrix.mul_assoc, hC.2]

theorem carrierUncompression_compression {V : Matrix B D ℂ} {P : Matrix B B ℂ}
    (hV : V * Vᴴ = P) {A : Matrix (B × Y) (B × Y) ℂ} (hs : carrierSupport P A) :
    carrierUncompression V Y (carrierCompression V Y A) = A := by
  unfold carrierUncompression carrierCompression
  calc
    carrierLift V Y * ((carrierLift V Y)ᴴ * A * carrierLift V Y) * (carrierLift V Y)ᴴ =
      (carrierLift V Y * (carrierLift V Y)ᴴ) * A *
        (carrierLift V Y * (carrierLift V Y)ᴴ) := by simp only [Matrix.mul_assoc]
    _ = A := by rw [carrierLift_projection hV, hs.1, hs.2]

theorem carrierCompression_output_supported {V : Matrix B D ℂ} {P : Matrix B B ℂ}
    (hV : V * Vᴴ = P) {A : Matrix (B × Y) (B × Y) ℂ} (hs : carrierSupport P A) :
    carrierSupport (Vᴴ * V) (carrierCompression V Y A) := by
  have hg : (Vᴴ * V) ⊗ₖ (1 : Matrix Y Y ℂ) =
      (carrierLift V Y)ᴴ * carrierLift V Y := by
    rw [carrierLift, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
      ← Matrix.mul_kronecker_mul, Matrix.one_mul]
  constructor
  · change ((Vᴴ * V) ⊗ₖ (1 : Matrix Y Y ℂ)) *
      ((carrierLift V Y)ᴴ * A * carrierLift V Y) = _
    rw [hg]
    calc
      ((carrierLift V Y)ᴴ * carrierLift V Y) * ((carrierLift V Y)ᴴ * A * carrierLift V Y) =
        (carrierLift V Y)ᴴ * (carrierLift V Y * (carrierLift V Y)ᴴ) * A * carrierLift V Y := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [carrierLift_projection hV, Matrix.mul_assoc _ _ A, hs.1] <;> rfl
  · change ((carrierLift V Y)ᴴ * A * carrierLift V Y) *
      ((Vᴴ * V) ⊗ₖ (1 : Matrix Y Y ℂ)) = _
    rw [hg]
    calc
      ((carrierLift V Y)ᴴ * A * carrierLift V Y) * ((carrierLift V Y)ᴴ * carrierLift V Y) =
        (carrierLift V Y)ᴴ * (A * (carrierLift V Y * (carrierLift V Y)ᴴ)) * carrierLift V Y := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [carrierLift_projection hV, hs.2] <;> rfl

theorem carrierCompression_posSemidef (V : Matrix B D ℂ)
    {A : Matrix (B × Y) (B × Y) ℂ} (hA : A.PosSemidef) :
    (carrierCompression V Y A).PosSemidef := hA.conjTranspose_mul_mul_same _

theorem carrierUncompression_posSemidef (V : Matrix B D ℂ)
    {X : Matrix (D × Y) (D × Y) ℂ} (hX : X.PosSemidef) :
    (carrierUncompression V Y X).PosSemidef := hX.mul_mul_conjTranspose_same _

theorem sandwich_trace_of_right_support {V : Matrix B D ℂ} {P A : Matrix B B ℂ}
    (hV : V * Vᴴ = P) (hs : A * P = A) : (Vᴴ * A * V).trace = A.trace := by
  calc
    (Vᴴ * A * V).trace = ((V * Vᴴ) * A).trace := Matrix.trace_mul_cycle Vᴴ A V
    _ = (A * (V * Vᴴ)).trace := Matrix.trace_mul_comm _ A
    _ = A.trace := by rw [hV, hs]

theorem carrierCompression_trace {V : Matrix B D ℂ} {P : Matrix B B ℂ}
    (hV : V * Vᴴ = P) {A : Matrix (B × Y) (B × Y) ℂ} (hs : carrierSupport P A) :
    (carrierCompression V Y A).trace = A.trace :=
  sandwich_trace_of_right_support (carrierLift_projection hV) hs.2

theorem carrierCompression_isDensity {V : Matrix B D ℂ} {P : Matrix B B ℂ}
    (hV : V * Vᴴ = P) {A : Matrix (B × Y) (B × Y) ℂ}
    (hA : IsDensity A) (hs : carrierSupport P A) : IsDensity (carrierCompression V Y A) :=
  ⟨carrierCompression_posSemidef V hA.1, (carrierCompression_trace hV hs).trans hA.2⟩

def matrixBlock (A : Matrix (B × Y) (B × Y) ℂ) (r s : Y) : Matrix B B ℂ :=
  fun b c => A (b, r) (c, s)

theorem matrixBlock_lift_right (P : Matrix B B ℂ) (A : Matrix (B × Y) (B × Y) ℂ)
    (r s : Y) : matrixBlock (A * (P ⊗ₖ (1 : Matrix Y Y ℂ))) r s = matrixBlock A r s * P := by
  ext b c
  simp only [matrixBlock, Matrix.mul_apply, Fintype.sum_prod_type,
    Matrix.kroneckerMap_apply, Matrix.one_apply, mul_ite, ite_mul, mul_one, mul_zero, zero_mul]
  simp only [Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, ite_eq_left]

theorem matrixBlock_carrierCompression (V : Matrix B D ℂ)
    (A : Matrix (B × Y) (B × Y) ℂ) (r s : Y) :
    matrixBlock (carrierCompression V Y A) r s = Vᴴ * matrixBlock A r s * V := by
  ext d e
  simp only [matrixBlock, carrierCompression, carrierLift, Matrix.conjTranspose_kronecker,
    Matrix.conjTranspose_one, Matrix.mul_apply, Fintype.sum_prod_type,
    Matrix.kroneckerMap_apply, Matrix.one_apply, mul_ite, ite_mul, mul_one, mul_zero, zero_mul]
  simp only [Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, ite_eq_left]

theorem carrierCompression_partialTrace_left {V : Matrix B D ℂ} {P : Matrix B B ℂ}
    (hV : V * Vᴴ = P) {A : Matrix (B × Y) (B × Y) ℂ} (hs : carrierSupport P A) :
    QuantumProver.QuantumEntropy.partialTrace_left (carrierCompression V Y A) =
      QuantumProver.QuantumEntropy.partialTrace_left A := by
  ext r s
  change (matrixBlock (carrierCompression V Y A) r s).trace = (matrixBlock A r s).trace
  rw [matrixBlock_carrierCompression]
  have hb : matrixBlock A r s * P = matrixBlock A r s := by
    have h := congrArg (fun X : Matrix (B × Y) (B × Y) ℂ => matrixBlock X r s) hs.2
    rwa [matrixBlock_lift_right] at h
  exact sandwich_trace_of_right_support hV hb

theorem carrierCompression_mul {V : Matrix B D ℂ} {P : Matrix B B ℂ}
    (hV : V * Vᴴ = P) (A : Matrix (B × Y) (B × Y) ℂ)
    {C : Matrix (B × Y) (B × Y) ℂ} (hC : carrierSupport P C) :
    carrierCompression V Y A * carrierCompression V Y C = carrierCompression V Y (A * C) := by
  unfold carrierCompression
  calc
    ((carrierLift V Y)ᴴ * A * carrierLift V Y) * ((carrierLift V Y)ᴴ * C * carrierLift V Y) =
      (carrierLift V Y)ᴴ * A * ((carrierLift V Y * (carrierLift V Y)ᴴ) * C) * carrierLift V Y := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [carrierLift_projection hV, hC.1]; simp only [Matrix.mul_assoc]

theorem carrierCompression_square_trace {V : Matrix B D ℂ} {P : Matrix B B ℂ}
    (hV : V * Vᴴ = P) {A : Matrix (B × Y) (B × Y) ℂ} (hs : carrierSupport P A) :
    (carrierCompression V Y A * carrierCompression V Y A).trace = (A * A).trace := by
  rw [carrierCompression_mul hV A hs]
  exact carrierCompression_trace hV (carrierSupport_mul hs hs)

theorem carrierCompression_purity {V : Matrix B D ℂ} {P : Matrix B B ℂ}
    (hV : V * Vᴴ = P) {A : Matrix (B × Y) (B × Y) ℂ} (hs : carrierSupport P A) :
    (carrierCompression V Y A * carrierCompression V Y A).trace.re = (A * A).trace.re :=
  congrArg Complex.re (carrierCompression_square_trace hV hs)

theorem carrierLift_star (V : Matrix B D ℂ) :
    carrierLift Vᴴ Y = (carrierLift V Y)ᴴ := (carrierLift_adjoint V).symm

theorem carrierLift_mul {K : Type*} [Fintype K] [DecidableEq K]
    (V : Matrix B D ℂ) (W : Matrix D K ℂ) :
    carrierLift (V * W) Y = carrierLift V Y * carrierLift W Y := by
  rw [carrierLift, carrierLift, carrierLift, ← Matrix.mul_kronecker_mul, Matrix.one_mul]

theorem carrierCompression_comp {K : Type*} [Fintype K] [DecidableEq K]
    (V : Matrix B D ℂ) (W : Matrix D K ℂ) (A : Matrix (B × Y) (B × Y) ℂ) :
    carrierCompression (V * W) Y A = carrierCompression W Y (carrierCompression V Y A) := by
  unfold carrierCompression
  rw [carrierLift_mul, Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]

theorem carrierCompression_adjoint_eq_uncompression (V : Matrix B D ℂ)
    (A : Matrix (B × Y) (B × Y) ℂ) :
    carrierCompression V Y A = carrierUncompression Vᴴ Y A := by
  unfold carrierCompression carrierUncompression
  rw [carrierLift_star, Matrix.conjTranspose_conjTranspose]

theorem projection_fixes_carrier {V : Matrix B D ℂ} {P : Matrix B B ℂ}
    (hP : PetzSmoothing.IsProjection P) (hV : V * Vᴴ = P) : P * V = V := by
  have hQ : (1 - P)ᴴ = 1 - P := hP.complement.selfAdjoint.eq
  have hz : ((1 - P) * V) * ((1 - P) * V)ᴴ = 0 := by
    rw [Matrix.conjTranspose_mul, hQ]
    calc
      ((1 - P) * V) * (Vᴴ * (1 - P)) = (1 - P) * (V * Vᴴ) * (1 - P) := by
        simp only [Matrix.mul_assoc]
      _ = 0 := by rw [hV, Matrix.sub_mul, Matrix.one_mul, hP.idempotent,
        sub_self, Matrix.zero_mul]
  have hz' := Matrix.self_mul_conjTranspose_eq_zero.mp hz
  have h : V - P * V = 0 := by simpa only [Matrix.sub_mul, Matrix.one_mul] using hz'
  exact (sub_eq_zero.mp h).symm

theorem abs_zeroExtension (U : Matrix B D ℂ) (hU : Uᴴ * U = 1) (X : Matrix D D ℂ) :
    CFC.abs (ZeroExtension.extend U X) = ZeroExtension.extend U (CFC.abs X) := by
  have hs : (ZeroExtension.extend U X)ᴴ = ZeroExtension.extend U Xᴴ := by
    simp only [ZeroExtension.extend, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  have hm : ZeroExtension.extend U (CFC.abs X) * ZeroExtension.extend U (CFC.abs X) =
      (ZeroExtension.extend U X)ᴴ * ZeroExtension.extend U X := by
    rw [ZeroExtension.extend_mul U hU, CFC.abs_mul_abs, Matrix.star_eq_conjTranspose,
      hs, ZeroExtension.extend_mul U hU]
  rw [CFC.abs, Matrix.star_eq_conjTranspose]
  exact CFC.sqrt_unique hm (ZeroExtension.extend_posSemidef U
    (CFC.abs_nonneg X).posSemidef).nonneg

theorem traceNorm_zeroExtension (U : Matrix B D ℂ) (hU : Uᴴ * U = 1) (X : Matrix D D ℂ) :
    QuantumProver.SandwichedDPI.traceNorm (ZeroExtension.extend U X) =
      QuantumProver.SandwichedDPI.traceNorm X := by
  unfold QuantumProver.SandwichedDPI.traceNorm
  rw [abs_zeroExtension U hU, ZeroExtension.extend_trace U hU]

theorem carrierUncompression_traceNorm (V : Matrix B D ℂ) (hV : Vᴴ * V = 1)
    (X : Matrix (D × Y) (D × Y) ℂ) :
    QuantumProver.SandwichedDPI.traceNorm (carrierUncompression V Y X) =
      QuantumProver.SandwichedDPI.traceNorm X :=
  traceNorm_zeroExtension (carrierLift V Y) (carrierLift_gram hV) X

theorem isometry_carrierCompression_traceNorm {V : Matrix B D ℂ} {P : Matrix B B ℂ}
    (hGram : Vᴴ * V = 1) (hV : V * Vᴴ = P)
    {A : Matrix (B × Y) (B × Y) ℂ} (hs : carrierSupport P A) :
    QuantumProver.SandwichedDPI.traceNorm (carrierCompression V Y A) = QuantumProver.SandwichedDPI.traceNorm A := by
  have h := carrierUncompression_traceNorm V hGram (carrierCompression V Y A)
  rw [carrierUncompression_compression hV hs] at h
  exact h.symm

theorem carrierCompression_traceNorm {V : Matrix B D ℂ} {P : Matrix B B ℂ}
    (hP : PetzSmoothing.IsProjection P) (hV : V * Vᴴ = P)
    {A : Matrix (B × Y) (B × Y) ℂ} (hs : carrierSupport P A) :
    QuantumProver.SandwichedDPI.traceNorm (carrierCompression V Y A) = QuantumProver.SandwichedDPI.traceNorm A := by
  let J := rankCarrier P hP
  let C := Jᴴ * V
  have hJ : Jᴴ * J = 1 := rankCarrier_gram P hP
  have hJP : J * Jᴴ = P := rankCarrier_projection P hP
  have hfactor : J * C = V := by
    change J * (Jᴴ * V) = V
    rw [← Matrix.mul_assoc, hJP, projection_fixes_carrier hP hV]
  have hC : C * Cᴴ = 1 := by
    change (Jᴴ * V) * (Jᴴ * V)ᴴ = 1
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    calc
      (Jᴴ * V) * (Vᴴ * J) = Jᴴ * (V * Vᴴ) * J := by simp only [Matrix.mul_assoc]
      _ = Jᴴ * P * J := congrArg (fun X : Matrix B B ℂ => Jᴴ * X * J) hV
      _ = Jᴴ * (J * Jᴴ) * J :=
        congrArg (fun X : Matrix B B ℂ => Jᴴ * X * J) hJP.symm
      _ = (Jᴴ * J) * (Jᴴ * J) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hJ, Matrix.one_mul]
  have hCs : (Cᴴ)ᴴ * Cᴴ = 1 := by rw [Matrix.conjTranspose_conjTranspose, hC]
  calc
    QuantumProver.SandwichedDPI.traceNorm (carrierCompression V Y A) =
        QuantumProver.SandwichedDPI.traceNorm (carrierUncompression Cᴴ Y (carrierCompression J Y A)) := by
      rw [← hfactor, carrierCompression_comp, carrierCompression_adjoint_eq_uncompression]
    _ = QuantumProver.SandwichedDPI.traceNorm (carrierCompression J Y A) :=
      carrierUncompression_traceNorm Cᴴ hCs _
    _ = QuantumProver.SandwichedDPI.traceNorm A := isometry_carrierCompression_traceNorm hJ hJP hs

theorem carrierCompression_sub (V : Matrix B D ℂ)
    (A C : Matrix (B × Y) (B × Y) ℂ) :
    carrierCompression V Y (A - C) = carrierCompression V Y A - carrierCompression V Y C := by
  simp only [carrierCompression, Matrix.mul_sub, Matrix.sub_mul]

theorem carrierCompression_difference_traceNorm {V : Matrix B D ℂ} {P : Matrix B B ℂ}
    (hP : PetzSmoothing.IsProjection P) (hV : V * Vᴴ = P)
    {A C : Matrix (B × Y) (B × Y) ℂ} (hA : carrierSupport P A) (hC : carrierSupport P C) :
    QuantumProver.SandwichedDPI.traceNorm (carrierCompression V Y A - carrierCompression V Y C) =
      QuantumProver.SandwichedDPI.traceNorm (A - C) := by
  rw [← carrierCompression_sub]
  exact carrierCompression_traceNorm hP hV (carrierSupport_sub hA hC)

theorem paddedCarrier_zero_rank (P : Matrix B B ℂ) (hP : PetzSmoothing.IsProjection P)
    (d : ℕ) (hr : P.rank ≤ d) (hz : P.rank = 0) : paddedCarrier P hP d hr = 0 := by
  have hc : Fintype.card (Fin P.rank) = 0 := by simpa only [Fintype.card_fin] using hz
  letI : IsEmpty (Fin P.rank) := Fintype.card_eq_zero_iff.mp hc
  ext b j
  simp [paddedCarrier, Matrix.mul_apply]

theorem entropyNats_nonneg {ρ : Matrix B B ℂ} (hρ : IsDensity ρ) :
    0 ≤ QuantumProver.QuantumEntropy.entropyNats ρ := by
  rw [QuantumProver.QuantumTypicalProjectors.entropyNats_eq_eigenWeight_sum hρ]
  apply neg_nonneg.mpr
  apply Finset.sum_nonpos
  intro i hi
  have hp := QuantumProver.QuantumTypicalProjectors.eigenWeight_nonneg hρ i
  have hp1 : QuantumProver.QuantumTypicalProjectors.eigenWeight hρ i ≤ 1 := by
    have h := Finset.single_le_sum
      (fun j hj => QuantumProver.QuantumTypicalProjectors.eigenWeight_nonneg hρ j) (Finset.mem_univ i)
    simpa only [QuantumProver.QuantumTypicalProjectors.eigenWeight_sum hρ] using h
  exact mul_nonpos_of_nonneg_of_nonpos hp (Real.log_nonpos hp hp1)

theorem typicalProjector_rank_le_totalDimension {ρ : Matrix B B ℂ} (hρ : IsDensity ρ)
    {δ : ℝ} (hδ : 0 ≤ δ) (n : ℕ) :
    (QuantumProver.QuantumTypicalProjectors.typicalProjector hρ δ n).rank ≤
      QuantumProver.QuantumRedistributionDimensions.totalDimension (QuantumProver.QuantumEntropy.entropyNats ρ) δ n :=
  QuantumProver.QuantumRedistributionDimensions.rank_le_totalDimension (entropyNats_nonneg hρ) hδ n _
    (QuantumProver.QuantumTypicalProjectors.typicalProjector_rank_le_exp hρ δ n)

def typicalCarrier {ρ : Matrix B B ℂ} (hρ : IsDensity ρ)
    (δ : ℝ) (hδ : 0 ≤ δ) (n : ℕ) :
    Matrix (TensorIndex B n)
      (Fin (QuantumProver.QuantumRedistributionDimensions.totalDimension (QuantumProver.QuantumEntropy.entropyNats ρ) δ n)) ℂ :=
  paddedCarrier (QuantumProver.QuantumTypicalProjectors.typicalProjector hρ δ n)
    (QuantumProver.QuantumTypicalProjectors.typicalProjector_isProjection hρ δ n) _
    (typicalProjector_rank_le_totalDimension hρ hδ n)

theorem typicalCarrier_projection {ρ : Matrix B B ℂ} (hρ : IsDensity ρ)
    (δ : ℝ) (hδ : 0 ≤ δ) (n : ℕ) :
    typicalCarrier hρ δ hδ n * (typicalCarrier hρ δ hδ n)ᴴ =
      QuantumProver.QuantumTypicalProjectors.typicalProjector hρ δ n :=
  paddedCarrier_projection _ _ _ _

theorem typicalCarrier_deficits {ρ : Matrix B B ℂ} (hρ : IsDensity ρ)
    (δ : ℝ) (hδ : 0 ≤ δ) (n : ℕ) :
    (1 - typicalCarrier hρ δ hδ n * (typicalCarrier hρ δ hδ n)ᴴ).PosSemidef ∧
    (1 - (typicalCarrier hρ δ hδ n)ᴴ * typicalCarrier hρ δ hδ n).PosSemidef :=
  paddedCarrier_deficits _ _ _ _

end QuantumProver.QuantumTypicalCarrier

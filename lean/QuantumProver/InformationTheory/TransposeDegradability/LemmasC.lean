import QuantumProver.InformationTheory.TransposeDegradability.Definitions
import QuantumProver.InformationTheory.TransposeDegradability.FoundationC

/-! PSD extension support and whole-output Choi reconstruction, derived
from the literal original marginal rather than supplied as a closure axiom. -/

open scoped ComplexConjugate ComplexOrder BigOperators Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator

namespace TransposeDegradability

noncomputable section

set_option maxHeartbeats 1000000

variable {I J E F : Type} [Fintype I] [Fintype J] [Fintype E] [Fintype F]
variable [DecidableEq I] [DecidableEq J] [DecidableEq E]

omit [Fintype I] [Fintype F] [DecidableEq I] [DecidableEq J] in
theorem tensor_identity_left_mul_apply
    (A : Matrix I J ℂ) (X : Matrix (J × E) (F × E) ℂ)
    (i : I) (e : E) (f : F) (g : E) :
    ((A ⊗ₖ (1 : Matrix E E ℂ)) * X) (i, e) (f, g) =
      ∑ j, A i j * X (j, e) (f, g) := by
  simp [Matrix.mul_apply, Matrix.kroneckerMap_apply, Matrix.one_apply, Fintype.sum_prod_type]

omit [Fintype I] [Fintype F] [DecidableEq I] [DecidableEq J] in
theorem tensor_identity_right_adjoint_mul_apply
    (A : Matrix I J ℂ) (X : Matrix (F × E) (J × E) ℂ)
    (f : F) (e : E) (i : I) (g : E) :
    (X * (A ⊗ₖ (1 : Matrix E E ℂ))ᴴ) (f, e) (i, g) =
      ∑ j, X (f, e) (j, g) * star (A i j) := by
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.kroneckerMap_apply,
    Matrix.one_apply, Fintype.sum_prod_type, apply_ite]

omit [Fintype I] [DecidableEq I] [DecidableEq J] in
set_option backward.isDefEq.respectTransparency false in
theorem partialTraceRight_local_sandwich (A : Matrix I J ℂ)
    (X : Matrix (J × E) (J × E) ℂ) :
    partialTraceRight ((A ⊗ₖ (1 : Matrix E E ℂ)) * X *
      (A ⊗ₖ (1 : Matrix E E ℂ))ᴴ) = A * partialTraceRight X * Aᴴ := by
  ext i j
  unfold partialTraceRight
  simp_rw [tensor_identity_right_adjoint_mul_apply, tensor_identity_left_mul_apply]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply,
    Finset.sum_mul, Finset.mul_sum, mul_assoc]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  exact Finset.sum_comm

omit [DecidableEq I] [DecidableEq E] in
theorem trace_partialTraceRight (X : Matrix (I × E) (I × E) ℂ) :
    (partialTraceRight X).trace = X.trace := by
  simp [Matrix.trace, partialTraceRight, Fintype.sum_prod_type]

/-- Vanishing marginal weight outside the actual purification range forces
every PSD factor column into that range, including singular original states. -/
theorem purification_factor_supported
    (Z : Matrix I J ℂ) (hZ : (purificationGram Z).PosDef)
    (K : Matrix (I × E) F ℂ)
    (hMarginal : partialTraceRight (K * Kᴴ) = Z * Zᴴ) :
    (purificationProjection Z ⊗ₖ (1 : Matrix E E ℂ)) * K = K := by
  let Q : Matrix I I ℂ := 1 - purificationProjection Z
  let A := Q ⊗ₖ (1 : Matrix E E ℂ)
  have hQZ : Q * Z = 0 := purificationComplement_mul Z hZ
  have hGram : (A * K) * (A * K)ᴴ = A * (K * Kᴴ) * Aᴴ := by
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  have hZero : ((A * K) * (A * K)ᴴ).trace = 0 := by
    rw [hGram, ← trace_partialTraceRight, partialTraceRight_local_sandwich, hMarginal]
    have heq : Q * (Z * Zᴴ) * Qᴴ = (Q * Z) * (Q * Z)ᴴ := by
      simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    rw [heq, hQZ]
    simp
  have hAK : A * K = 0 := Matrix.trace_mul_conjTranspose_self_eq_zero_iff.mp hZero
  have hA : A = ((1 : Matrix I I ℂ) ⊗ₖ (1 : Matrix E E ℂ)) -
      (purificationProjection Z ⊗ₖ (1 : Matrix E E ℂ)) := by
    ext p q
    simp only [A, Q, Matrix.kroneckerMap_apply, Matrix.sub_apply, sub_mul]
  have hDiff : K - (purificationProjection Z ⊗ₖ (1 : Matrix E E ℂ)) * K = 0 := by
    simpa only [hA, Matrix.one_kronecker_one,
      Matrix.sub_mul, Matrix.one_mul] using hAK
  exact (sub_eq_zero.mp hDiff).symm

theorem choi_posSemidef_factor (X : Matrix I I ℂ) (hX : X.PosSemidef) :
    ∃ K : Matrix I I ℂ, X = K * Kᴴ := by
  refine ⟨CFC.sqrt X, ?_⟩
  have hRoot : (CFC.sqrt X).IsHermitian :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg X)).isHermitian
  rw [hRoot.eq, CFC.sqrt_mul_sqrt_self X hX.nonneg]

theorem purification_extension_supported
    (Z : Matrix I J ℂ) (hZ : (purificationGram Z).PosDef)
    (sigma : Matrix (I × E) (I × E) ℂ) (hSigma : sigma.PosSemidef)
    (hMarginal : partialTraceRight sigma = Z * Zᴴ) :
    (purificationProjection Z ⊗ₖ (1 : Matrix E E ℂ)) * sigma *
      (purificationProjection Z ⊗ₖ (1 : Matrix E E ℂ))ᴴ = sigma := by
  obtain ⟨K, hK⟩ := choi_posSemidef_factor sigma hSigma
  have hSupported := purification_factor_supported Z hZ K (hK ▸ hMarginal)
  rw [hK]
  calc
    _ = ((purificationProjection Z ⊗ₖ (1 : Matrix E E ℂ)) * K) *
      ((purificationProjection Z ⊗ₖ (1 : Matrix E E ℂ)) * K)ᴴ := by
      simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = K * Kᴴ := by rw [hSupported]

omit [DecidableEq I] in
theorem reconstructedChoi_partialTrace
    (Z : Matrix I J ℂ) (hZ : (purificationGram Z).PosDef)
    (sigma : Matrix (I × E) (I × E) ℂ)
    (hMarginal : partialTraceRight sigma = Z * Zᴴ) :
    partialTraceRight (reconstructedChoi Z sigma) = 1 := by
  unfold reconstructedChoi
  rw [partialTraceRight_local_sandwich, hMarginal, purificationLeftInverse_marginal Z hZ]

/-- Actual whole-output unnormalized Choi, with positivity, literal TP
marginal and exact reproduction of the original extension all derived. -/
theorem reconstructedChoi_properties
    (Z : Matrix I J ℂ) (hZ : (purificationGram Z).PosDef)
    (sigma : Matrix (I × E) (I × E) ℂ) (hSigma : sigma.PosSemidef)
    (hMarginal : partialTraceRight sigma = Z * Zᴴ) :
    (reconstructedChoi Z sigma).PosSemidef ∧
      partialTraceRight (reconstructedChoi Z sigma) = 1 ∧
      (Z ⊗ₖ (1 : Matrix E E ℂ)) * reconstructedChoi Z sigma *
        (Z ⊗ₖ (1 : Matrix E E ℂ))ᴴ = sigma := by
  exact ⟨reconstructedChoi_posSemidef Z sigma hSigma,
    reconstructedChoi_partialTrace Z hZ sigma hMarginal,
    reconstructedChoi_reproduce_of_support Z sigma
      (purification_extension_supported Z hZ sigma hSigma hMarginal)⟩

end
end TransposeDegradability

/-! ## Register all-complex Choi channel and semantic CPTP reconstruction -/

namespace TransposeDegradability

noncomputable section

set_option maxHeartbeats 1000000

variable {I O Q : Type} [Fintype I] [Fintype O] [Fintype Q]
variable [DecidableEq I] [DecidableEq O]

set_option backward.isDefEq.respectTransparency false in
def channelOfChoi (C : Matrix (I × O) (I × O) ℂ) :
    Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ where
  toFun X := Matrix.of (fun e f => ∑ i, ∑ j, X i j * C (i, e) (j, f))
  map_add' X Y := by
    ext e f
    simp only [Matrix.of_apply, Matrix.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' z X := by
    ext e f
    simp only [Matrix.of_apply, Matrix.smul_apply, RingHom.id_apply,
      smul_eq_mul, Finset.mul_sum, mul_assoc]

omit [Fintype O] [DecidableEq I] [DecidableEq O] in
@[simp] theorem channelOfChoi_apply (C : Matrix (I × O) (I × O) ℂ)
    (X : Matrix I I ℂ) (e f : O) :
    channelOfChoi C X e f = ∑ i, ∑ j, X i j * C (i, e) (j, f) := rfl

def krausChannel (K : Q → Matrix O I ℂ) : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ :=
  ∑ q, sandwichLinear (K q)

def choiFactorColumn (H : Matrix (I × O) Q ℂ) (q : Q) : Matrix O I ℂ :=
  fun e i => H (i, e) q

omit [Fintype O] [DecidableEq O] in
theorem choi_channelOfChoi (C : Matrix (I × O) (I × O) ℂ) :
    choi (channelOfChoi C) = C := by
  ext p q
  rcases p with ⟨i, e⟩
  rcases q with ⟨j, f⟩
  simp [choi, channelOfChoi_apply, Matrix.single_apply, ite_and]

omit [DecidableEq O] in
theorem krausChannel_matrix_unit (K : Q → Matrix O I ℂ) (i j : I) (e f : O) :
    krausChannel K (Matrix.single i j 1) e f = ∑ q, K q e i * star (K q f j) := by
  simp [krausChannel, sandwichLinear, Matrix.sum_apply, Matrix.mul_apply,
    Matrix.single_apply, Matrix.conjTranspose_apply, ite_and]

omit [DecidableEq O] in
theorem choi_krausChannel_factor (H : Matrix (I × O) Q ℂ) :
    choi (krausChannel (choiFactorColumn H)) = H * Hᴴ := by
  ext p q
  rcases p with ⟨i, e⟩
  rcases q with ⟨j, f⟩
  simp only [choi_apply, krausChannel_matrix_unit, choiFactorColumn,
    Matrix.mul_apply, Matrix.conjTranspose_apply]

omit [DecidableEq O] in
theorem channelOfChoi_factor_eq_kraus (H : Matrix (I × O) Q ℂ) :
    channelOfChoi (H * Hᴴ) = krausChannel (choiFactorColumn H) := by
  apply choi_injective
  rw [choi_channelOfChoi, choi_krausChannel_factor]

omit [DecidableEq I] [DecidableEq O] in
set_option backward.isDefEq.respectTransparency false in
theorem amplify_sandwichLinear (A : Matrix O I ℂ) (R : Type) [Fintype R] [DecidableEq R]
    (X : Matrix (R × I) (R × I) ℂ) :
    amplify (sandwichLinear A) R X =
      ((1 : Matrix R R ℂ) ⊗ₖ A) * X * ((1 : Matrix R R ℂ) ⊗ₖ A)ᴴ := by
  classical
  ext p q
  rcases p with ⟨r, e⟩
  rcases q with ⟨s, f⟩
  simp [amplify, sandwichLinear, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.kroneckerMap_apply, Matrix.one_apply, Fintype.sum_prod_type, apply_ite,
    ite_mul]

omit [DecidableEq I] [DecidableEq O] in
set_option backward.isDefEq.respectTransparency false in
theorem amplify_krausChannel (K : Q → Matrix O I ℂ) (R : Type) [Fintype R] [DecidableEq R]
    (X : Matrix (R × I) (R × I) ℂ) :
    amplify (krausChannel K) R X = ∑ q,
      ((1 : Matrix R R ℂ) ⊗ₖ K q) * X * ((1 : Matrix R R ℂ) ⊗ₖ K q)ᴴ := by
  classical
  have h : amplify (krausChannel K) R X = ∑ q, amplify (sandwichLinear (K q)) R X := by
    ext p q
    simp [amplify, krausChannel, LinearMap.sum_apply, Matrix.sum_apply]
  rw [h]
  simp_rw [amplify_sandwichLinear]

omit [DecidableEq I] [DecidableEq O] in
theorem krausChannel_completelyPositive (K : Q → Matrix O I ℂ) :
    CompletelyPositive (krausChannel K) := by
  intro R _ X hX
  classical
  rw [amplify_krausChannel]
  exact Matrix.posSemidef_sum _ fun q _ => hX.mul_mul_conjTranspose_same _

theorem channelOfChoi_completelyPositive
    (C : Matrix (I × O) (I × O) ℂ) (hC : C.PosSemidef) :
    CompletelyPositive (channelOfChoi C) := by
  obtain ⟨H, hH⟩ := choi_posSemidef_factor C hC
  rw [hH, channelOfChoi_factor_eq_kraus]
  exact krausChannel_completelyPositive _

omit [DecidableEq O] in
theorem channelOfChoi_tracePreserving (C : Matrix (I × O) (I × O) ℂ)
    (hC : partialTraceRight C = 1) : TracePreserving (channelOfChoi C) := by
  have hUnits (i j : I) :
      (channelOfChoi C (Matrix.single i j 1)).trace = (Matrix.single i j (1 : ℂ)).trace := by
    have h := congrArg (fun M : Matrix I I ℂ => M i j) hC
    simpa [partialTraceRight, channelOfChoi_apply, Matrix.trace, Matrix.single_apply,
      Matrix.one_apply, ite_and, eq_comm] using h
  have hMaps : (Matrix.traceLinearMap O ℂ ℂ).comp (channelOfChoi C) =
      Matrix.traceLinearMap I ℂ ℂ := by
    apply Matrix.ext_linearMap
    intro i j
    apply LinearMap.ext
    intro z
    have hz : Matrix.single i j z = z • Matrix.single i j (1 : ℂ) := by
      simp [Matrix.smul_single]
    change ((Matrix.traceLinearMap O ℂ ℂ).comp (channelOfChoi C)) (Matrix.single i j z) =
      (Matrix.traceLinearMap I ℂ ℂ) (Matrix.single i j z)
    rw [hz, map_smul, map_smul]
    exact congrArg (fun t : ℂ => z • t) (hUnits i j)
  intro X
  exact congrArg (fun phi => phi X) hMaps

theorem channelOfChoi_CPTP (C : Matrix (I × O) (I × O) ℂ)
    (hC : C.PosSemidef) (hTrace : partialTraceRight C = 1) : CPTP (channelOfChoi C) :=
  ⟨channelOfChoi_completelyPositive C hC, channelOfChoi_tracePreserving C hTrace⟩

variable {R : Type} [Fintype R] [DecidableEq R]

omit [Fintype R] [DecidableEq I] [DecidableEq R] in
theorem channelOfChoi_amplify_purification
    (Z : Matrix R I ℂ) (C : Matrix (I × O) (I × O) ℂ) :
    amplify (channelOfChoi C) R (purificationState Z) =
      (Z ⊗ₖ (1 : Matrix O O ℂ)) * C * (Z ⊗ₖ (1 : Matrix O O ℂ))ᴴ := by
  ext p q
  rcases p with ⟨r, e⟩
  rcases q with ⟨s, f⟩
  simp only [amplify, purificationState_apply,
    tensor_identity_right_adjoint_mul_apply, tensor_identity_left_mul_apply,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- A literal PSD extension with the original purification marginal yields
an actual semantic CPTP map on the WHOLE output algebra and reproduces the
extension under actual finite amplification. No extension/closure axiom. -/
theorem exists_CPTP_from_extension (Z : Matrix R I ℂ)
    (hZ : (purificationGram Z).PosDef)
    (sigma : Matrix (R × O) (R × O) ℂ) (hSigma : sigma.PosSemidef)
    (hMarginal : partialTraceRight sigma = Z * Zᴴ) :
    ∃ D : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ,
      CPTP D ∧ amplify D R (purificationState Z) = sigma := by
  have h := reconstructedChoi_properties Z hZ sigma hSigma hMarginal
  refine ⟨channelOfChoi (reconstructedChoi Z sigma), channelOfChoi_CPTP _ h.1 h.2.1, ?_⟩
  rw [channelOfChoi_amplify_purification]
  exact h.2.2

end
end TransposeDegradability

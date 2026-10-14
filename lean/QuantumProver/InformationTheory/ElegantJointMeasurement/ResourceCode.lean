import QuantumProver.InformationTheory.ElegantJointMeasurement.RankOneEffects
import QuantumProver.InformationTheory.ElegantJointMeasurement.ConcurrenceBounds
import QuantumProver.InformationTheory.ElegantJointMeasurement.MeasurementStates

open scoped BigOperators ComplexConjugate
open InnerProductSpace

namespace QuantumProver.ElegantJointMeasurement.ResourceCode

noncomputable section

variable {a b κ : Type*} [Fintype a] [Fintype b] [Fintype κ] [DecidableEq κ]

abbrev InputSpace (a b : Type*) := EuclideanSpace ℂ (a × b)
abbrev ExtendedSpace (a b κ : Type*) := EuclideanSpace ℂ ((a × κ) × (b × κ))

def coefficientMatrix (E : InputSpace a b) : Matrix a b ℂ := fun i j => E (i, j)

def codeLinear (β : κ → ℝ) : InputSpace a b →ₗ[ℂ] ExtendedSpace a b κ where
  toFun E := WithLp.toLp 2 (fun z =>
    if z.1.2 = z.2.2 then (β z.1.2 : ℂ) * E (z.1.1, z.2.1) else 0)
  map_add' E F := by
    ext z
    simp only [PiLp.add_apply]
    split_ifs <;> simp [mul_add]
  map_smul' c E := by
    ext z
    simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> ring

@[simp] theorem codeLinear_apply (β : κ → ℝ) (E : InputSpace a b)
    (i : a) (j : b) (k l : κ) :
    codeLinear β E ((i, k), (j, l)) =
      if k = l then (β k : ℂ) * E (i, j) else 0 := rfl

def codeContinuous (β : κ → ℝ) : InputSpace a b →L[ℂ] ExtendedSpace a b κ :=
  (codeLinear β).toContinuousLinearMap

@[simp] theorem codeContinuous_apply (β : κ → ℝ) (E : InputSpace a b) :
    codeContinuous β E = codeLinear β E := rfl

theorem code_norm_sq (β : κ → ℝ) (E : InputSpace a b) :
    ‖codeLinear β E‖ ^ 2 = (∑ k, β k ^ 2) * ‖E‖ ^ 2 := by
  calc
    ‖codeLinear β E‖ ^ 2 =
        ∑ i : a, ∑ k : κ, ∑ j : b, β k ^ 2 * ‖E (i, j)‖ ^ 2 := by
      simp [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type, apply_ite,
        mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    _ = ∑ i : a, ∑ j : b, (∑ k : κ, β k ^ 2) * ‖E (i, j)‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.sum_mul]
    _ = (∑ k, β k ^ 2) * ‖E‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
      simp only [Finset.mul_sum]

theorem code_norm (β : κ → ℝ) (hβ : ∑ k, β k ^ 2 = 1) (E : InputSpace a b) :
    ‖codeContinuous β E‖ = ‖E‖ := by
  have h := code_norm_sq β E
  rw [hβ, one_mul] at h
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h

def contraction (β : κ → ℝ) (z : ExtendedSpace a b κ) : InputSpace a b :=
  WithLp.toLp 2 (fun ij => ∑ k, (β k : ℂ) * z ((ij.1, k), (ij.2, k)))

@[simp] theorem contraction_apply (β : κ → ℝ) (z : ExtendedSpace a b κ)
    (i : a) (j : b) :
    contraction β z (i, j) = ∑ k, (β k : ℂ) * z ((i, k), (j, k)) := rfl

theorem code_inner_contraction (β : κ → ℝ) (E : InputSpace a b)
    (z : ExtendedSpace a b κ) :
    inner ℂ (codeContinuous β E) z = inner ℂ E (contraction β z) := by
  calc
    inner ℂ (codeContinuous β E) z =
        ∑ i : a, ∑ k : κ, ∑ j : b,
          (β k : ℂ) * conj (E (i, j)) * z ((i, k), (j, k)) := by
      simp only [PiLp.inner_apply, Fintype.sum_prod_type, RCLike.inner_apply',
        codeContinuous_apply, codeLinear_apply]
      simp [apply_ite, map_mul, mul_assoc]
    _ = ∑ i : a, ∑ j : b, ∑ k : κ,
          conj (E (i, j)) * ((β k : ℂ) * z ((i, k), (j, k))) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ = inner ℂ E (contraction β z) := by
      simp only [PiLp.inner_apply, Fintype.sum_prod_type, RCLike.inner_apply',
        contraction_apply, Finset.mul_sum]

theorem code_adjoint_apply (β : κ → ℝ) (z : ExtendedSpace a b κ) :
    (codeContinuous β).adjoint z = contraction β z := by
  apply ext_inner_left ℂ
  intro E
  rw [ContinuousLinearMap.adjoint_inner_right]
  exact code_inner_contraction β E z

def productKet (A : Matrix a κ ℂ) (B : Matrix b κ ℂ) : ExtendedSpace a b κ :=
  WithLp.toLp 2 (fun z => A z.1.1 z.1.2 * B z.2.1 z.2.2)

@[simp] theorem productKet_apply (A : Matrix a κ ℂ) (B : Matrix b κ ℂ)
    (i : a) (j : b) (k l : κ) :
    productKet A B ((i, k), (j, l)) = A i k * B j l := rfl

theorem code_adjoint_product (β : κ → ℝ) (A : Matrix a κ ℂ) (B : Matrix b κ ℂ)
    (i : a) (j : b) :
    (codeContinuous β).adjoint (productKet A B) (i, j) =
      ∑ k, (β k : ℂ) * A i k * B j k := by
  rw [code_adjoint_apply, contraction_apply]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [productKet_apply]
  ring

def columnProjection (k : κ) : ExtendedSpace a b κ →ₗ[ℂ] Matrix a b ℂ where
  toFun z i j := z ((i, k), (j, k))
  map_add' z w := by ext i j; rfl
  map_smul' c z := by ext i j; rfl

theorem columnProjection_code (β : κ → ℝ) (E : InputSpace a b) (k : κ) :
    columnProjection k (codeContinuous β E) =
      (β k : ℂ) • coefficientMatrix E := by
  ext i j
  change codeContinuous β E ((i, k), (j, k)) = (β k : ℂ) * E (i, j)
  rw [codeContinuous_apply, codeLinear_apply, if_pos rfl]

theorem columnProjection_product (A : Matrix a κ ℂ) (B : Matrix b κ ℂ) (k : κ) :
    columnProjection k (productKet A B) =
      Matrix.vecMulVec (fun i => A i k) (fun j => B j k) := by
  ext i j
  rfl

def tailContraction (β : κ → ℝ) (A : Matrix a κ ℂ) (B : Matrix b κ ℂ)
    (k : κ) : Matrix a b ℂ :=
  ∑ t ∈ Finset.univ.erase k,
    (β t : ℂ) • Matrix.vecMulVec (fun i => A i t) (fun j => B j t)

theorem tailContraction_apply (β : κ → ℝ) (A : Matrix a κ ℂ) (B : Matrix b κ ℂ)
    (k : κ) (i : a) (j : b) :
    tailContraction β A B k i j =
      ∑ t ∈ Finset.univ.erase k, (β t : ℂ) * A i t * B j t := by
  simp only [tailContraction, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.vecMulVec_apply, mul_assoc]

def ejmKet (u v w : ℝ) : InputSpace (Fin 2) (Fin 2) :=
  WithLp.toLp 2 (fun ij => QuantumProver.ElegantJointMeasurement.States.ejmCoefficient u v w ij.1 ij.2)

theorem coefficientMatrix_ejmKet (u v w : ℝ) :
    coefficientMatrix (ejmKet u v w) = QuantumProver.ElegantJointMeasurement.States.ejmCoefficient u v w := by
  ext i j
  rfl

theorem norm_sq_coefficientMatrix (E : InputSpace (Fin 2) (Fin 2)) :
    ‖E‖ ^ 2 = QuantumProver.ElegantJointMeasurement.States.frobeniusNormSq (coefficientMatrix E) := by
  simp only [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type,
    QuantumProver.ElegantJointMeasurement.States.frobeniusNormSq, coefficientMatrix, Complex.normSq_eq_norm_sq]

theorem norm_ejmKet (u v w : ℝ) (hsphere : u ^ 2 + v ^ 2 + w ^ 2 = 3) :
    ‖ejmKet u v w‖ = 1 := by
  have hsq : ‖ejmKet u v w‖ ^ 2 = (1 : ℝ) ^ 2 := by
    rw [norm_sq_coefficientMatrix, coefficientMatrix_ejmKet,
      QuantumProver.ElegantJointMeasurement.States.frobeniusNormSq_ejmCoefficient u v w hsphere]
    norm_num
  exact (sq_eq_sq₀ (norm_nonneg _) (by norm_num)).mp hsq

theorem code_saturation (β : κ → ℝ) (hβ : ∑ k, β k ^ 2 = 1)
    (F : ExtendedSpace a b κ →L[ℂ] ExtendedSpace a b κ)
    (E : InputSpace a b) (hE : ‖E‖ = 1)
    (hupper : (ContinuousLinearMap.id ℂ (ExtendedSpace a b κ) - F).IsPositive)
    (hcompression : (codeContinuous β).adjoint ∘L (F ∘L codeContinuous β) =
      rankOne ℂ E E) :
    F (codeContinuous β E) = codeContinuous β E := by
  have heinner : inner ℂ E E = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hE]
    norm_num
  have hexpect : inner ℂ (codeContinuous β E) (F (codeContinuous β E)) = 1 := by
    calc
      inner ℂ (codeContinuous β E) (F (codeContinuous β E)) =
          inner ℂ E (((codeContinuous β).adjoint ∘L (F ∘L codeContinuous β)) E) := by
        simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right]
      _ = inner ℂ E (rankOne ℂ E E E) := by rw [hcompression]
      _ = 1 := by rw [inner_right_rankOne_apply, heinner, one_mul]
  exact QuantumProver.ElegantJointMeasurement.RankOne.saturation_eigenvector F (codeContinuous β E) hupper
    ((code_norm β hβ E).trans hE) hexpect

section ProductEffects

variable {ι : Type*}

theorem exact_product_normalization (s : Finset ι) (β : κ → ℝ)
    (A : ι → Matrix a κ ℂ) (B : ι → Matrix b κ ℂ)
    (E : InputSpace a b) (hE : ‖E‖ = 1)
    (hcompression : (codeContinuous β).adjoint ∘L
      ((∑ v ∈ s, rankOne ℂ (productKet (A v) (B v)) (productKet (A v) (B v))) ∘L
        codeContinuous β) = rankOne ℂ E E) :
    ∑ v ∈ s, ‖inner ℂ (codeContinuous β E) (productKet (A v) (B v))‖ ^ 2 = 1 := by
  exact QuantumProver.ElegantJointMeasurement.RankOne.compressed_branch_normalization s
    (fun v => productKet (A v) (B v)) (codeContinuous β) E hE hcompression

theorem exact_product_contraction (s : Finset ι) (β : κ → ℝ)
    (A : ι → Matrix a κ ℂ) (B : ι → Matrix b κ ℂ)
    (E : InputSpace a b) (hE : ‖E‖ = 1)
    (hcompression : (codeContinuous β).adjoint ∘L
      ((∑ v ∈ s, rankOne ℂ (productKet (A v) (B v)) (productKet (A v) (B v))) ∘L
        codeContinuous β) = rankOne ℂ E E) :
    ∀ v ∈ s, ∀ i : a, ∀ j : b,
      (∑ k, (β k : ℂ) * A v i k * B v j k) =
        inner ℂ (codeContinuous β E) (productKet (A v) (B v)) * E (i, j) := by
  have h := QuantumProver.ElegantJointMeasurement.RankOne.compressed_branch_collinear s
    (fun v => productKet (A v) (B v)) (codeContinuous β) E hE hcompression
  intro v hv i j
  have hcoord := congrArg (fun z : InputSpace a b => z (i, j)) (h v hv)
  simpa only [code_adjoint_product, PiLp.smul_apply, smul_eq_mul] using hcoord

theorem exact_product_column_moment (s : Finset ι) (β : κ → ℝ)
    (hβ : ∑ k, β k ^ 2 = 1)
    (A : ι → Matrix a κ ℂ) (B : ι → Matrix b κ ℂ)
    (E : InputSpace a b) (hE : ‖E‖ = 1) (k : κ)
    (hupper : (ContinuousLinearMap.id ℂ (ExtendedSpace a b κ) -
      ∑ v ∈ s, rankOne ℂ (productKet (A v) (B v)) (productKet (A v) (B v))).IsPositive)
    (hcompression : (codeContinuous β).adjoint ∘L
      ((∑ v ∈ s, rankOne ℂ (productKet (A v) (B v)) (productKet (A v) (B v))) ∘L
        codeContinuous β) = rankOne ℂ E E) :
    ∑ v ∈ s,
      conj (inner ℂ (codeContinuous β E) (productKet (A v) (B v))) •
        Matrix.vecMulVec (fun i => A v i k) (fun j => B v j k) =
      (β k : ℂ) • coefficientMatrix E := by
  have hfix := code_saturation β hβ
    (∑ v ∈ s, rankOne ℂ (productKet (A v) (B v)) (productKet (A v) (B v)))
    E hE hupper hcompression
  have h := QuantumProver.ElegantJointMeasurement.RankOne.eigenvector_projected_moment s
    (fun v => productKet (A v) (B v)) (codeContinuous β E) (columnProjection k) hfix
  simpa only [columnProjection_product, columnProjection_code] using h

theorem exact_product_tail_det_lower_bound (s : Finset ι) (β : κ → ℝ)
    (hβ : ∑ k, β k ^ 2 = 1)
    (A B : ι → Matrix (Fin 2) κ ℂ)
    (E : InputSpace (Fin 2) (Fin 2)) (hE : ‖E‖ = 1) (k : κ) (x : ℝ)
    (hx : β k ^ 2 = x)
    (hupper : (ContinuousLinearMap.id ℂ (ExtendedSpace (Fin 2) (Fin 2) κ) -
      ∑ v ∈ s, rankOne ℂ (productKet (A v) (B v)) (productKet (A v) (B v))).IsPositive)
    (hcompression : (codeContinuous β).adjoint ∘L
      ((∑ v ∈ s, rankOne ℂ (productKet (A v) (B v)) (productKet (A v) (B v))) ∘L
        codeContinuous β) = rankOne ℂ E E)
    (hdet : ‖Matrix.det (coefficientMatrix E)‖ = (1 / 4 : ℝ)) :
    (1 / 4 : ℝ) * |1 - 2 * x| ≤
      ∑ v ∈ s,
        ‖Matrix.det (QuantumProver.ElegantJointMeasurement.Determinant.tailMatrix (coefficientMatrix E)
          (fun i => A v i k) (fun j => B v j k) (β k : ℂ)
          (inner ℂ (codeContinuous β E) (productKet (A v) (B v))))‖ := by
  exact QuantumProver.ElegantJointMeasurement.Determinant.tail_det_sum_lower_bound_real s (coefficientMatrix E)
    (fun v i => A v i k) (fun v j => B v j k)
    (fun v => inner ℂ (codeContinuous β E) (productKet (A v) (B v))) (β k) x
    (exact_product_normalization s β A B E hE hcompression)
    (exact_product_column_moment s β hβ A B E hE k hupper hcompression) hx hdet

theorem exact_tailContraction_eq_tailMatrix (s : Finset ι) (β : κ → ℝ)
    (A B : ι → Matrix (Fin 2) κ ℂ)
    (E : InputSpace (Fin 2) (Fin 2)) (hE : ‖E‖ = 1) (k : κ)
    (hcompression : (codeContinuous β).adjoint ∘L
      ((∑ v ∈ s, rankOne ℂ (productKet (A v) (B v)) (productKet (A v) (B v))) ∘L
        codeContinuous β) = rankOne ℂ E E)
    (v : ι) (hv : v ∈ s) :
    tailContraction β (A v) (B v) k =
      QuantumProver.ElegantJointMeasurement.Determinant.tailMatrix (coefficientMatrix E)
        (fun i => A v i k) (fun j => B v j k) (β k : ℂ)
        (inner ℂ (codeContinuous β E) (productKet (A v) (B v))) := by
  ext i j
  rw [tailContraction_apply]
  change (∑ t ∈ Finset.univ.erase k, (β t : ℂ) * A v i t * B v j t) =
    inner ℂ (codeContinuous β E) (productKet (A v) (B v)) * E (i, j) -
      (β k : ℂ) * A v i k * B v j k
  apply (eq_sub_iff_add_eq).2
  exact (Finset.sum_erase_add Finset.univ
    (fun t => (β t : ℂ) * A v i t * B v j t) (Finset.mem_univ k)).trans
      (exact_product_contraction s β A B E hE hcompression v hv i j)

theorem exact_product_physical_tail_det_lower_bound (s : Finset ι) (β : κ → ℝ)
    (hβ : ∑ k, β k ^ 2 = 1)
    (A B : ι → Matrix (Fin 2) κ ℂ)
    (E : InputSpace (Fin 2) (Fin 2)) (hE : ‖E‖ = 1) (k : κ) (x : ℝ)
    (hx : β k ^ 2 = x)
    (hupper : (ContinuousLinearMap.id ℂ (ExtendedSpace (Fin 2) (Fin 2) κ) -
      ∑ v ∈ s, rankOne ℂ (productKet (A v) (B v)) (productKet (A v) (B v))).IsPositive)
    (hcompression : (codeContinuous β).adjoint ∘L
      ((∑ v ∈ s, rankOne ℂ (productKet (A v) (B v)) (productKet (A v) (B v))) ∘L
        codeContinuous β) = rankOne ℂ E E)
    (hdet : ‖Matrix.det (coefficientMatrix E)‖ = (1 / 4 : ℝ)) :
    (1 / 4 : ℝ) * |1 - 2 * x| ≤
      ∑ v ∈ s, ‖Matrix.det (tailContraction β (A v) (B v) k)‖ := by
  calc
    (1 / 4 : ℝ) * |1 - 2 * x| ≤
        ∑ v ∈ s,
          ‖Matrix.det (QuantumProver.ElegantJointMeasurement.Determinant.tailMatrix (coefficientMatrix E)
            (fun i => A v i k) (fun j => B v j k) (β k : ℂ)
            (inner ℂ (codeContinuous β E) (productKet (A v) (B v))))‖ :=
      exact_product_tail_det_lower_bound s β hβ A B E hE k x hx hupper hcompression hdet
    _ = ∑ v ∈ s, ‖Matrix.det (tailContraction β (A v) (B v) k)‖ := by
      apply Finset.sum_congr rfl
      intro v hv
      rw [← exact_tailContraction_eq_tailMatrix s β A B E hE k hcompression v hv]

theorem ejm_physical_tail_det_lower_bound (s : Finset ι) (β : κ → ℝ)
    (hβ : ∑ k, β k ^ 2 = 1) (A B : ι → Matrix (Fin 2) κ ℂ)
    (u v w : ℝ) (hsphere : u ^ 2 + v ^ 2 + w ^ 2 = 3)
    (k : κ) (x : ℝ) (hx : β k ^ 2 = x)
    (hupper : (ContinuousLinearMap.id ℂ (ExtendedSpace (Fin 2) (Fin 2) κ) -
      ∑ z ∈ s, rankOne ℂ (productKet (A z) (B z)) (productKet (A z) (B z))).IsPositive)
    (hcompression : (codeContinuous β).adjoint ∘L
      ((∑ z ∈ s, rankOne ℂ (productKet (A z) (B z)) (productKet (A z) (B z))) ∘L
        codeContinuous β) = rankOne ℂ (ejmKet u v w) (ejmKet u v w)) :
    (1 / 4 : ℝ) * |1 - 2 * x| ≤
      ∑ z ∈ s, ‖Matrix.det (tailContraction β (A z) (B z) k)‖ := by
  apply exact_product_physical_tail_det_lower_bound s β hβ A B
    (ejmKet u v w) (norm_ejmKet u v w hsphere) k x hx hupper hcompression
  rw [coefficientMatrix_ejmKet]
  exact QuantumProver.ElegantJointMeasurement.States.norm_det_ejmCoefficient u v w hsphere

end ProductEffects

end

end QuantumProver.ElegantJointMeasurement.ResourceCode

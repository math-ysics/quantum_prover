import QuantumProver.InformationTheory.WernerEndpoint.SlaterSquareMoment
import QuantumProver.InformationTheory.SuperchannelDiscrimination.CPTPKraus

noncomputable section

namespace QuantumProver.WernerEndpoint.SlaterMoments

open QuantumProver.WernerEndpoint MeasureTheory
open scoped BigOperators ComplexOrder Kronecker

abbrev TwoSet (d : ℕ) := {S : Finset (Fin d) // S.card = 2}

def edgeToTwoSet {d : ℕ} (e : Edge d) : TwoSet d :=
  ⟨{e.val.1, e.val.2}, by simp [ne_of_lt e.property]⟩

def twoSetToEdge {d : ℕ} (S : TwoSet d) : Edge d :=
  ⟨((S.val.orderEmbOfFin S.property) 0, (S.val.orderEmbOfFin S.property) 1),
    (S.val.orderEmbOfFin S.property).strictMono (by decide)⟩

def edgeTwoSetEquiv (d : ℕ) : Edge d ≃ TwoSet d where
  toFun := edgeToTwoSet
  invFun := twoSetToEdge
  left_inv e := by
    let S := edgeToTwoSet e
    let g : Fin 2 → Fin d := ![e.val.1, e.val.2]
    have he := e.property
    have hmem : ∀ k, g k ∈ S.val := by
      intro k
      fin_cases k <;> simp [g, S, edgeToTwoSet]
    have hmono : StrictMono g := by
      intro k l hkl
      fin_cases k <;> fin_cases l <;> simp_all [g]
    have hg : g = S.val.orderEmbOfFin S.property :=
      Finset.orderEmbOfFin_unique S.property hmem hmono
    apply Subtype.ext
    change ((S.val.orderEmbOfFin S.property) 0, (S.val.orderEmbOfFin S.property) 1) = e.val
    rw [← hg]
    rfl
  right_inv S := by
    apply Subtype.ext
    change {(S.val.orderEmbOfFin S.property) 0, (S.val.orderEmbOfFin S.property) 1} = S.val
    let g := S.val.orderEmbOfFin S.property
    have hfin : (Finset.univ : Finset (Fin 2)) = {0, 1} := by decide
    calc
      {g 0, g 1} = Finset.image g Finset.univ := by rw [hfin]; simp
      _ = S.val := Finset.image_orderEmbOfFin_univ S.val S.property

theorem fixedSizeFinset_card (d k : ℕ) :
    Fintype.card {S : Finset (Fin d) // S.card = k} = d.choose k := by
  classical
  calc
    Fintype.card {S : Finset (Fin d) // S.card = k} =
        (Finset.univ.powersetCard k : Finset (Finset (Fin d))).card :=
      Fintype.card_of_subtype _ (by intro S; simp)
    _ = d.choose k := by rw [Finset.card_powersetCard]; simp

theorem edge_card_choose (d : ℕ) : Fintype.card (Edge d) = d.choose 2 := by
  rw [Fintype.card_congr (edgeTwoSetEquiv d)]
  exact fixedSizeFinset_card d 2

theorem fourSet_card_choose (d : ℕ) : Fintype.card (FourSet d) = d.choose 4 :=
  fixedSizeFinset_card d 4

theorem edge_card_complex (d : ℕ) :
    (Fintype.card (Edge d) : ℂ) = (d : ℂ) * ((d : ℂ) - 1) / 2 := by
  rw [edge_card_choose, Nat.cast_choose_two ℂ]

theorem fourSet_card_complex (d : ℕ) (hd : 2 ≤ d) :
    (Fintype.card (FourSet d) : ℂ) =
      (d : ℂ) * ((d : ℂ) - 1) * ((d : ℂ) - 2) * ((d : ℂ) - 3) / 24 := by
  rw [fourSet_card_choose]
  by_cases h4 : 4 ≤ d
  · have h := congrArg (fun n : ℕ => (n : ℂ))
      (Nat.descFactorial_eq_factorial_mul_choose d 4)
    simp only [Nat.descFactorial_succ, Nat.descFactorial_zero,
      Nat.cast_mul, Nat.cast_sub (by omega : 3 ≤ d),
      Nat.cast_sub (by omega : 2 ≤ d), Nat.cast_sub (by omega : 1 ≤ d)] at h
    norm_num at h
    apply (eq_div_iff (by norm_num : (24 : ℂ) ≠ 0)).mpr
    linear_combination -h
  · have hsmall : d = 2 ∨ d = 3 := by omega
    rcases hsmall with rfl | rfl <;>
      rw [Nat.choose_eq_zero_of_lt (by decide)] <;> norm_num

theorem coordinatePositiveProjector_trace (d : ℕ) (hd : 2 ≤ d) :
    Matrix.trace (coordinatePositiveProjector d) =
      (d : ℂ)^2 * ((d : ℂ)^2 - 1) / 12 := by
  rw [coordinatePositiveProjector_trace_card, edge_card_complex, fourSet_card_complex d hd]
  ring

theorem normalizedSlaterMoment_coordinate_formula (d : ℕ) (hd : 2 ≤ d) :
    normalizedSlaterMoment d hd =
      ((12 : ℂ) / ((d : ℂ)^2 * ((d : ℂ)^2 - 1))) • coordinatePositiveProjector d := by
  rw [normalizedSlaterMoment_eq_inv_trace_coordinatePositiveProjector,
    coordinatePositiveProjector_trace d hd]
  congr 1
  exact inv_div _ _

theorem coordinatePositiveProjector_trace_d2 : Matrix.trace (coordinatePositiveProjector 2) = 1 := by
  norm_num [coordinatePositiveProjector_trace]

theorem coordinatePositiveProjector_trace_d3 : Matrix.trace (coordinatePositiveProjector 3) = 6 := by
  norm_num [coordinatePositiveProjector_trace]

theorem coordinatePositiveProjector_trace_d4 : Matrix.trace (coordinatePositiveProjector 4) = 20 := by
  norm_num [coordinatePositiveProjector_trace]

def fourFormColumns (d : ℕ) : Matrix (Edge d × Edge d) (FourSet d) ℂ :=
  fun ef S => fourFormOmega S ef

theorem fourFormColumns_gram (d : ℕ) :
    (fourFormColumns d).conjTranspose * fourFormColumns d =
      (6 : ℂ) • (1 : Matrix (FourSet d) (FourSet d) ℂ) := by
  classical
  ext S T
  change star (fourFormOmega S) ⬝ᵥ fourFormOmega T =
    (6 : ℂ) * (if S = T then 1 else 0)
  rw [fourFormOmega_gram]
  by_cases h : S = T <;> simp [h]

theorem fourFormColumns_outer (d : ℕ) :
    fourFormColumns d * (fourFormColumns d).conjTranspose =
      ∑ S : FourSet d, pureDensity (fourFormOmega S) := by
  ext ef gh
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, fourFormColumns,
    Matrix.sum_apply, pureDensity, crossDensity]

theorem pureDensity_transpose_conjugate {I : Type*} (u : I → ℂ) :
    (pureDensity u).transpose = pureDensity (star u) := by
  ext a b
  simp [pureDensity, crossDensity, Matrix.transpose_apply, mul_comm]

theorem kronecker_tensorVector_mulVec {I O : Type*} [Fintype I]
    (A : Matrix O I ℂ) (u v : I → ℂ) :
    (A ⊗ₖ A).mulVec (tensorVector u v) = tensorVector (A.mulVec u) (A.mulVec v) := by
  ext ⟨a, b⟩
  simp only [Matrix.mulVec, dotProduct, tensorVector, Matrix.kroneckerMap_apply,
    Fintype.sum_prod_type, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem tensorVector_normSq {I : Type*} [Fintype I] (u v : I → ℂ) :
    vectorNormSq (tensorVector u v) = vectorNormSq u * vectorNormSq v := by
  simp only [vectorNormSq, tensorVector, Fintype.sum_prod_type, Complex.normSq_mul,
    ← Finset.mul_sum, ← Finset.sum_mul]

theorem trace_mul_pureDensity {I : Type*} [Fintype I] (K : Matrix I I ℂ) (u : I → ℂ) :
    Matrix.trace (K * pureDensity u) = star u ⬝ᵥ K.mulVec u := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, pureDensity, crossDensity,
    dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem slaterSquare_conjugate {d : ℕ} (U : PhysicalUnitary d) (i j : Fin d) :
    star (slaterSquare U i j) =
      tensorVector (star (slaterVector U i j)) (star (slaterVector U i j)) := by
  ext ef
  simp [slaterSquare, tensorVector]

def slaterFrameVector {d : ℕ} {Y : Type*} (A : Matrix Y (Edge d) ℂ)
    (U : PhysicalUnitary d) (i j : Fin d) : Y → ℂ :=
  A.mulVec (star (slaterVector U i j))

theorem slaterSquareDensity_frame {d : ℕ} {Y : Type*} (A : Matrix Y (Edge d) ℂ)
    (U : PhysicalUnitary d) (i j : Fin d) :
    (A ⊗ₖ A) * (slaterSquareDensity U i j).transpose * (A ⊗ₖ A).conjTranspose =
      pureDensity (tensorVector (slaterFrameVector A U i j) (slaterFrameVector A U i j)) := by
  change (A ⊗ₖ A) * (pureDensity (slaterSquare U i j)).transpose *
    (A ⊗ₖ A).conjTranspose = _
  rw [pureDensity_transpose_conjugate]
  simpa only [pureDensity, slaterSquare_conjugate, kronecker_tensorVector_mulVec,
    slaterFrameVector] using
    sandwich_crossDensity (A ⊗ₖ A) (star (slaterSquare U i j)) (star (slaterSquare U i j))

theorem slaterSquareDensity_companion_contraction {d : ℕ} {Y B E : Type*}
    [Fintype Y] [Fintype B] [Fintype E] [DecidableEq Y]
    (N : Stinespring Y B E) (A : Matrix Y (Edge d) ℂ) (U : PhysicalUnitary d) (i j : Fin d) :
    (Matrix.trace (N.replicaKernel * (A ⊗ₖ A) * (slaterSquareDensity U i j).transpose *
      (A ⊗ₖ A).conjTranspose)).re =
      purity (N.apply (pureDensity (slaterFrameVector A U i j))) := by
  calc
    _ = (Matrix.trace (N.replicaKernel * ((A ⊗ₖ A) *
        (slaterSquareDensity U i j).transpose * (A ⊗ₖ A).conjTranspose))).re := by
      simp only [Matrix.mul_assoc]
    _ = (Matrix.trace (N.replicaKernel * pureDensity
        (tensorVector (slaterFrameVector A U i j) (slaterFrameVector A U i j)))).re := by
      rw [slaterSquareDensity_frame]
    _ = _ := by
      rw [trace_mul_pureDensity]
      simpa only [purity, pureDensity] using congrArg Complex.re
        (N.replicaKernel_pair (slaterFrameVector A U i j) (slaterFrameVector A U i j)
          (slaterFrameVector A U i j) (slaterFrameVector A U i j))

theorem slaterSquareDensity_companion_mass {d : ℕ} {Y : Type*} [Fintype Y]
    (A : Matrix Y (Edge d) ℂ) (U : PhysicalUnitary d) (i j : Fin d) :
    (Matrix.trace ((A ⊗ₖ A) * (slaterSquareDensity U i j).transpose *
      (A ⊗ₖ A).conjTranspose)).re = (vectorNormSq (slaterFrameVector A U i j)) ^ 2 := by
  rw [slaterSquareDensity_frame, pureDensity_trace, tensorVector_normSq, Complex.ofReal_re]
  ring

theorem slaterSquareDensity_companion_bound {d : ℕ} {Y B E : Type*}
    [Fintype Y] [Fintype B] [Fintype E] [DecidableEq Y]
    (N : Stinespring Y B E) (A : Matrix Y (Edge d) ℂ) (β : ℝ)
    (hbound : ∀ v : Y → ℂ, purity (N.apply (pureDensity v)) ≤ β * (vectorNormSq v)^2)
    (U : PhysicalUnitary d) (i j : Fin d) :
    (Matrix.trace (N.replicaKernel * (A ⊗ₖ A) * (slaterSquareDensity U i j).transpose *
      (A ⊗ₖ A).conjTranspose)).re ≤
      β * (Matrix.trace ((A ⊗ₖ A) * (slaterSquareDensity U i j).transpose *
        (A ⊗ₖ A).conjTranspose)).re := by
  rw [slaterSquareDensity_companion_contraction, slaterSquareDensity_companion_mass]
  exact hbound _

def frameTraceLinearMap {I O : Type*} [Fintype I] [Fintype O]
    (K : Matrix O O ℂ) (T : Matrix O I ℂ) : Matrix I I ℂ →ₗ[ℂ] ℂ where
  toFun P := Matrix.trace (K * T * P.transpose * T.conjTranspose)
  map_add' P Q := by
    simp only [Matrix.transpose_add, Matrix.mul_add, Matrix.add_mul, Matrix.trace_add]
  map_smul' z P := by
    simp only [Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul,
      RingHom.id_apply]

def frameTraceCLM {I O : Type*} [Fintype I] [Fintype O]
    (K : Matrix O O ℂ) (T : Matrix O I ℂ) : (I → I → ℂ) →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap
    ((frameTraceLinearMap K T).comp (Matrix.ofLinearEquiv ℂ).toLinearMap)

theorem frameTraceCLM_apply {I O : Type*} [Fintype I] [Fintype O]
    (K : Matrix O O ℂ) (T : Matrix O I ℂ) (P : I → I → ℂ) :
    frameTraceCLM K T P = Matrix.trace (K * T * (Matrix.of P).transpose * T.conjTranspose) := rfl

theorem frameTrace_slaterMoment_integral {d : ℕ} {O : Type*} [Fintype O]
    (K : Matrix O O ℂ) (T : Matrix O (Edge d × Edge d) ℂ) (i j : Fin d) :
    (∫ U : PhysicalUnitary d,
      Matrix.trace (K * T * (slaterSquareDensity U i j).transpose * T.conjTranspose)
      ∂normalizedHaar d) = Matrix.trace (K * T * (slaterMoment i j).transpose *
        T.conjTranspose) :=
  (frameTraceCLM K T).integral_comp_comm (slaterSquareDensity_function_integrable i j)

theorem frameTrace_slaterDensity_integrable {d : ℕ} {O : Type*} [Fintype O]
    (K : Matrix O O ℂ) (T : Matrix O (Edge d × Edge d) ℂ) (i j : Fin d) :
    Integrable (fun U : PhysicalUnitary d =>
      Matrix.trace (K * T * (slaterSquareDensity U i j).transpose * T.conjTranspose))
      (normalizedHaar d) :=
  (frameTraceCLM K T).integrable_comp (slaterSquareDensity_function_integrable i j)

theorem frameTrace_slaterMoment_integral_re {d : ℕ} {O : Type*} [Fintype O]
    (K : Matrix O O ℂ) (T : Matrix O (Edge d × Edge d) ℂ) (i j : Fin d) :
    (∫ U : PhysicalUnitary d,
      (Matrix.trace (K * T * (slaterSquareDensity U i j).transpose * T.conjTranspose)).re
      ∂normalizedHaar d) = (Matrix.trace (K * T * (slaterMoment i j).transpose *
        T.conjTranspose)).re := by
  calc
    _ = (∫ U : PhysicalUnitary d,
        Matrix.trace (K * T * (slaterSquareDensity U i j).transpose * T.conjTranspose)
        ∂normalizedHaar d).re :=
      Complex.reCLM.integral_comp_comm (frameTrace_slaterDensity_integrable K T i j)
    _ = _ := congrArg Complex.re (frameTrace_slaterMoment_integral K T i j)

theorem slaterMoment_companion_bound {d : ℕ} {Y B E : Type*}
    [Fintype Y] [Fintype B] [Fintype E] [DecidableEq Y]
    (N : Stinespring Y B E) (A : Matrix Y (Edge d) ℂ) (β : ℝ)
    (hbound : ∀ v : Y → ℂ, purity (N.apply (pureDensity v)) ≤ β * (vectorNormSq v)^2)
    (i j : Fin d) :
    (Matrix.trace (N.replicaKernel * (A ⊗ₖ A) * (slaterMoment i j).transpose *
      (A ⊗ₖ A).conjTranspose)).re ≤
      β * (Matrix.trace ((A ⊗ₖ A) * (slaterMoment i j).transpose *
        (A ⊗ₖ A).conjTranspose)).re := by
  have hK := (frameTrace_slaterDensity_integrable N.replicaKernel (A ⊗ₖ A) i j).re
  have hI := (frameTrace_slaterDensity_integrable
    (1 : Matrix (Y × Y) (Y × Y) ℂ) (A ⊗ₖ A) i j).re
  simp only [RCLike.re_eq_complex_re] at hK hI
  simp only [Matrix.one_mul] at hI
  have h := integral_mono hK (hI.const_mul β)
    (fun U => slaterSquareDensity_companion_bound N A β hbound U i j)
  rw [integral_const_mul, frameTrace_slaterMoment_integral_re] at h
  have hm := frameTrace_slaterMoment_integral_re
    (1 : Matrix (Y × Y) (Y × Y) ℂ) (A ⊗ₖ A) i j
  simp only [Matrix.one_mul] at hm
  rwa [hm] at h

theorem exteriorReplicaProjector_mul_fourFormColumns (d : ℕ) :
    exteriorReplicaProjector d * fourFormColumns d = fourFormColumns d := by
  ext ef S
  change (exteriorReplicaProjector d).mulVec (fourFormOmega S) ef = fourFormOmega S ef
  exact congrFun (exteriorReplicaProjector_fourFormOmega S) ef

theorem exteriorReplicaProjector_trace_card (d : ℕ) (hd : 2 ≤ d) :
    Matrix.trace (exteriorReplicaProjector d) = (Fintype.card (FourSet d) : ℂ) := by
  rw [exteriorReplicaProjector_trace, fourSet_card_complex d hd]
  ring

theorem exteriorReplicaProjector_eq_coordinateFourProjector (d : ℕ) (hd : 2 ≤ d) :
    exteriorReplicaProjector d = coordinateFourProjector d := by
  have h := orthogonalProjector_eq_six_scaled_columns
    (exteriorReplicaProjector d) (fourFormColumns d)
    (exteriorReplicaProjector_hermitian d) (exteriorReplicaProjector_idempotent d)
    (exteriorReplicaProjector_mul_fourFormColumns d) (fourFormColumns_gram d)
    (exteriorReplicaProjector_trace_card d hd)
  rw [fourFormColumns_outer] at h
  exact h

theorem edgeReplicaSwap_eq_replicaSwap (d : ℕ) : edgeReplicaSwap d = replicaSwap (Edge d) := by
  ext ef gh
  have heq : gh = (ef.2, ef.1) ↔ ef = (gh.2, gh.1) := by
    constructor <;> intro h <;> rw [h]
  simp only [edgeReplicaSwap, replicaSwap, heq]

theorem positiveSector_eq_positiveReplicaProjector (d : ℕ) :
    positiveSector d = positiveReplicaProjector d := by
  unfold positiveSector positiveReplicaProjector symmetricReplicaProjector exteriorReplicaProjector
  rw [edgeReplicaSwap_eq_replicaSwap]

theorem coordinatePositiveProjector_eq_positiveSector (d : ℕ) (hd : 2 ≤ d) :
    coordinatePositiveProjector d = positiveSector d := by
  change (1 / 2 : ℂ) • (1 + edgeReplicaSwap d) - coordinateFourProjector d =
    (1 / 2 : ℂ) • (1 + edgeReplicaSwap d) - exteriorReplicaProjector d
  rw [exteriorReplicaProjector_eq_coordinateFourProjector d hd]

theorem normalizedSlaterMoment_physical_formula (d : ℕ) (hd : 2 ≤ d) :
    normalizedSlaterMoment d hd =
      ((12 : ℂ) / ((d : ℂ)^2 * ((d : ℂ)^2 - 1))) • positiveSector d := by
  rw [normalizedSlaterMoment_coordinate_formula d hd,
    coordinatePositiveProjector_eq_positiveSector d hd]

theorem positiveSector_trace (d : ℕ) (hd : 2 ≤ d) :
    Matrix.trace (positiveSector d) = (d : ℂ)^2 * ((d : ℂ)^2 - 1) / 12 := by
  rw [← coordinatePositiveProjector_eq_positiveSector d hd]
  exact coordinatePositiveProjector_trace d hd

theorem positiveSector_posSemidef (d : ℕ) (hd : 2 ≤ d) :
    (positiveSector d).PosSemidef := by
  rw [← coordinatePositiveProjector_eq_positiveSector d hd]
  exact coordinatePositiveProjector_posSemidef d

theorem positiveSector_idempotent (d : ℕ) (hd : 2 ≤ d) :
    positiveSector d * positiveSector d = positiveSector d := by
  rw [← coordinatePositiveProjector_eq_positiveSector d hd]
  exact coordinatePositiveProjector_idempotent d

def slaterMomentCoefficient (d : ℕ) : ℝ :=
  12 / ((d : ℝ)^2 * ((d : ℝ)^2 - 1))

theorem slaterMomentCoefficient_complex (d : ℕ) :
    (slaterMomentCoefficient d : ℂ) = (12 : ℂ) / ((d : ℂ)^2 * ((d : ℂ)^2 - 1)) := by
  simp [slaterMomentCoefficient]

theorem slaterMomentCoefficient_pos (d : ℕ) (hd : 2 ≤ d) : 0 < slaterMomentCoefficient d := by
  have hreal : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hsq : 0 < (d : ℝ)^2 := by nlinarith
  have hgap : 0 < (d : ℝ)^2 - 1 := by nlinarith
  exact div_pos (by norm_num) (mul_pos hsq hgap)

theorem normalizedSlaterMoment_physical_formula_ofReal (d : ℕ) (hd : 2 ≤ d) :
    normalizedSlaterMoment d hd = (slaterMomentCoefficient d : ℂ) • positiveSector d := by
  rw [slaterMomentCoefficient_complex]
  exact normalizedSlaterMoment_physical_formula d hd

theorem positiveSector_companion_bound_homogeneous {d : ℕ} (hd : 2 ≤ d) {Y B E : Type*}
    [Fintype Y] [Fintype B] [Fintype E] [DecidableEq Y]
    (N : Stinespring Y B E) (A : Matrix Y (Edge d) ℂ) (β : ℝ)
    (hbound : ∀ v : Y → ℂ, purity (N.apply (pureDensity v)) ≤ β * (vectorNormSq v)^2) :
    replicaSectorContraction N A (positiveSector d) ≤ β * replicaSectorMass A (positiveSector d) := by
  have h := slaterMoment_companion_bound N A β hbound (columnZero d hd) (columnOne d hd)
  change (Matrix.trace (N.replicaKernel * (A ⊗ₖ A) *
      (normalizedSlaterMoment d hd).transpose * (A ⊗ₖ A).conjTranspose)).re ≤
      β * (Matrix.trace ((A ⊗ₖ A) * (normalizedSlaterMoment d hd).transpose *
        (A ⊗ₖ A).conjTranspose)).re at h
  rw [normalizedSlaterMoment_physical_formula_ofReal] at h
  simp only [Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul,
    smul_eq_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at h
  change (Matrix.trace (N.replicaKernel * (A ⊗ₖ A) * (positiveSector d).transpose *
      (A ⊗ₖ A).conjTranspose)).re ≤
      β * (Matrix.trace ((A ⊗ₖ A) * (positiveSector d).transpose *
        (A ⊗ₖ A).conjTranspose)).re
  apply le_of_mul_le_mul_left (a := slaterMomentCoefficient d) ?_
    (slaterMomentCoefficient_pos d hd)
  convert h using 1; ring

theorem positiveSector_companion_bound {d : ℕ} (hd : 2 ≤ d) {Y B E : Type*}
    [Fintype Y] [Fintype B] [Fintype E] [DecidableEq Y]
    (N : Stinespring Y B E) (A : Matrix Y (Edge d) ℂ) (β : ℝ)
    (hbound : ∀ v : Y → ℂ, vectorNormSq v = 1 → purity (N.apply (pureDensity v)) ≤ β) :
    replicaSectorContraction N A (positiveReplicaProjector d) ≤
      β * replicaSectorMass A (positiveReplicaProjector d) := by
  rw [← positiveSector_eq_positiveReplicaProjector]
  exact positiveSector_companion_bound_homogeneous hd N A β
    (N.pure_purity_homogeneous β hbound)

theorem kronecker_replicaSwap_commutes {X : Type*} [Fintype X] [DecidableEq X]
    (R : Matrix X X ℂ) :
    (R ⊗ₖ R) * replicaSwap X = replicaSwap X * (R ⊗ₖ R) := by
  ext ij kl
  have heq (ef : X × X) : ij = (ef.2, ef.1) ↔ ef = (ij.2, ij.1) := by
    simp [Prod.ext_iff, eq_comm, and_comm]
  simp [Matrix.mul_apply, replicaSwap, heq, Matrix.kroneckerMap_apply,
    mul_ite, mul_comm]

theorem kronecker_symmetricReplicaProjector_commutes {X : Type*}
    [Fintype X] [DecidableEq X] (R : Matrix X X ℂ) :
    (R ⊗ₖ R) * symmetricReplicaProjector X =
      symmetricReplicaProjector X * (R ⊗ₖ R) := by
  unfold symmetricReplicaProjector
  rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_one, Matrix.one_mul, kronecker_replicaSwap_commutes]

theorem symmetricReplicaProjector_wedgeSquareAction_commutes (d : ℕ)
    (V : PhysicalUnitary d) :
    wedgeSquareAction V * symmetricReplicaProjector (Edge d) =
      symmetricReplicaProjector (Edge d) * wedgeSquareAction V :=
  kronecker_symmetricReplicaProjector_commutes (wedgeAction V)

theorem positiveSector_wedgeSquareAction_commutes (d : ℕ) (hd : 2 ≤ d)
    (V : PhysicalUnitary d) :
    wedgeSquareAction V * positiveSector d = positiveSector d * wedgeSquareAction V := by
  have hk : (slaterMomentCoefficient d : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (slaterMomentCoefficient_pos d hd))
  have h := slaterMoment_commutes (columnZero d hd) (columnOne d hd) V
  change wedgeSquareAction V * normalizedSlaterMoment d hd =
    normalizedSlaterMoment d hd * wedgeSquareAction V at h
  rw [normalizedSlaterMoment_physical_formula_ofReal, Matrix.mul_smul, Matrix.smul_mul] at h
  have h' := congrArg (fun M : Matrix (Edge d × Edge d) (Edge d × Edge d) ℂ =>
    (slaterMomentCoefficient d : ℂ)⁻¹ • M) h
  simpa only [smul_smul, inv_mul_cancel₀ hk, one_smul] using h'

theorem positiveReplicaProjector_wedgeSquareAction_commutes (d : ℕ) (hd : 2 ≤ d)
    (V : PhysicalUnitary d) :
    wedgeSquareAction V * positiveReplicaProjector d =
      positiveReplicaProjector d * wedgeSquareAction V := by
  rw [← positiveSector_eq_positiveReplicaProjector]
  exact positiveSector_wedgeSquareAction_commutes d hd V

theorem exteriorReplicaProjector_wedgeSquareAction_commutes (d : ℕ) (hd : 2 ≤ d)
    (V : PhysicalUnitary d) :
    wedgeSquareAction V * exteriorReplicaProjector d =
      exteriorReplicaProjector d * wedgeSquareAction V := by
  have h := positiveReplicaProjector_wedgeSquareAction_commutes d hd V
  unfold positiveReplicaProjector at h
  rw [Matrix.mul_sub, Matrix.sub_mul,
    symmetricReplicaProjector_wedgeSquareAction_commutes] at h
  exact sub_right_inj.mp h

theorem exteriorReplicaProjector_wedgeSquareAction_covariance (d : ℕ) (hd : 2 ≤ d)
    (V : PhysicalUnitary d) :
    wedgeSquareAction V * exteriorReplicaProjector d *
      (wedgeSquareAction V).conjTranspose = exteriorReplicaProjector d := by
  have hu : wedgeSquareAction V * (wedgeSquareAction V).conjTranspose = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using (wedgeSquareAction_mem_unitary V).2
  rw [exteriorReplicaProjector_wedgeSquareAction_commutes d hd V,
    Matrix.mul_assoc, hu, Matrix.mul_one]

theorem coordinateFourProjector_wedgeSquareAction_commutes (d : ℕ) (hd : 2 ≤ d)
    (V : PhysicalUnitary d) :
    wedgeSquareAction V * coordinateFourProjector d =
      coordinateFourProjector d * wedgeSquareAction V := by
  rw [← exteriorReplicaProjector_eq_coordinateFourProjector d hd]
  exact exteriorReplicaProjector_wedgeSquareAction_commutes d hd V

theorem coordinateFourProjector_wedgeSquareAction_covariance (d : ℕ) (hd : 2 ≤ d)
    (V : PhysicalUnitary d) :
    wedgeSquareAction V * coordinateFourProjector d *
      (wedgeSquareAction V).conjTranspose = coordinateFourProjector d := by
  rw [← exteriorReplicaProjector_eq_coordinateFourProjector d hd]
  exact exteriorReplicaProjector_wedgeSquareAction_covariance d hd V

theorem exteriorReplicaProjector_transpose_wedgeSquareAction_covariance
    (d : ℕ) (hd : 2 ≤ d) (V : PhysicalUnitary d) :
    (wedgeSquareAction V).conjTranspose.transpose * (exteriorReplicaProjector d).transpose *
      (wedgeSquareAction V).transpose = (exteriorReplicaProjector d).transpose := by
  have h := congrArg Matrix.transpose (exteriorReplicaProjector_wedgeSquareAction_covariance d hd V)
  simpa only [Matrix.transpose_mul, Matrix.mul_assoc] using h

theorem fourFormOmega_entry_star {d : ℕ} (S : FourSet d) (ef : Edge d × Edge d) :
    star (fourFormOmega S ef) = fourFormOmega S ef := by
  simp [fourFormOmega, Pi.single_apply]

theorem coordinateFourProjector_entry_star (d : ℕ) (ef gh : Edge d × Edge d) :
    star (coordinateFourProjector d ef gh) = coordinateFourProjector d ef gh := by
  simp [coordinateFourProjector, Matrix.smul_apply, Matrix.sum_apply, pureDensity,
    crossDensity, star_sum, fourFormOmega_entry_star]

theorem exteriorReplicaProjector_entry_star (d : ℕ) (hd : 2 ≤ d)
    (ef gh : Edge d × Edge d) :
    star (exteriorReplicaProjector d ef gh) = exteriorReplicaProjector d ef gh := by
  rw [exteriorReplicaProjector_eq_coordinateFourProjector d hd]
  exact coordinateFourProjector_entry_star d ef gh

theorem exteriorReplicaProjector_transpose_eq (d : ℕ) (hd : 2 ≤ d) :
    (exteriorReplicaProjector d).transpose = exteriorReplicaProjector d := by
  ext ef gh
  have h := congrArg (fun M : Matrix (Edge d × Edge d) (Edge d × Edge d) ℂ => M ef gh)
    (exteriorReplicaProjector_hermitian d)
  change star (exteriorReplicaProjector d gh ef) = exteriorReplicaProjector d ef gh at h
  rw [exteriorReplicaProjector_entry_star d hd] at h
  exact h

theorem exteriorReplicaProjector_conjugate_wedgeSquareAction_covariance
    (d : ℕ) (hd : 2 ≤ d) (V : PhysicalUnitary d) :
    (wedgeSquareAction V).conjTranspose.transpose * exteriorReplicaProjector d *
      (wedgeSquareAction V).transpose = exteriorReplicaProjector d := by
  have h := exteriorReplicaProjector_transpose_wedgeSquareAction_covariance d hd V
  rwa [exteriorReplicaProjector_transpose_eq d hd] at h

theorem physicalPermutation_column {d : ℕ} (σ : Equiv.Perm (Fin d)) (a : Fin d) :
    (fun r => physicalPermutation σ r a) = Pi.single (σ.symm a) 1 := by
  ext r
  have h := physicalPermutation_mul_entry σ (1 : PhysicalUnitary d) r a
  simpa [Matrix.UnitaryGroup.one_apply, Matrix.one_apply, Pi.single_apply,
    Equiv.eq_symm_apply] using h

theorem physicalPermutation_orderedWedge {d : ℕ} (σ : Equiv.Perm (Fin d))
    (a b : Fin d) :
    (wedgeAction (physicalPermutation σ)).mulVec (orderedWedge a b) =
      orderedWedge (σ.symm a) (σ.symm b) := by
  rw [wedgeAction_orderedWedge, physicalPermutation_column, physicalPermutation_column]
  rfl

theorem physicalPermutation_replicaProduct {d : ℕ} (σ : Equiv.Perm (Fin d))
    (a b c f : Fin d) :
    (wedgeSquareAction (physicalPermutation σ)).mulVec
      (replicaProduct (orderedWedge a b) (orderedWedge c f)) =
      replicaProduct (orderedWedge (σ.symm a) (σ.symm b))
        (orderedWedge (σ.symm c) (σ.symm f)) := by
  rw [wedgeSquareAction_replicaProduct, physicalPermutation_orderedWedge,
    physicalPermutation_orderedWedge]

theorem physicalPermutation_replica_difference {d : ℕ} (σ : Equiv.Perm (Fin d))
    (a b c f : Fin d) :
    (wedgeSquareAction (physicalPermutation σ)).mulVec
      (replicaProduct (orderedWedge a b) (orderedWedge c f) -
        replicaProduct (orderedWedge c f) (orderedWedge a b)) =
      replicaProduct (orderedWedge (σ.symm a) (σ.symm b))
        (orderedWedge (σ.symm c) (σ.symm f)) -
      replicaProduct (orderedWedge (σ.symm c) (σ.symm f))
        (orderedWedge (σ.symm a) (σ.symm b)) := by
  rw [Matrix.mulVec_sub, physicalPermutation_replicaProduct,
    physicalPermutation_replicaProduct]

def canonicalTripleEmbedding {d : ℕ} (hd : 3 ≤ d) : Fin 3 ↪ Fin d :=
  Fin.castLEEmb hd

def distinctTripleEmbedding {d : ℕ} (x0 x1 x2 : Fin d)
    (h01 : x0 ≠ x1) (h02 : x0 ≠ x2) (h12 : x1 ≠ x2) : Fin 3 ↪ Fin d where
  toFun := ![x0, x1, x2]
  inj' := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all

@[simp] theorem distinctTripleEmbedding_zero {d : ℕ} (x0 x1 x2 : Fin d)
    (h01 : x0 ≠ x1) (h02 : x0 ≠ x2) (h12 : x1 ≠ x2) :
    distinctTripleEmbedding x0 x1 x2 h01 h02 h12 0 = x0 := rfl

@[simp] theorem distinctTripleEmbedding_one {d : ℕ} (x0 x1 x2 : Fin d)
    (h01 : x0 ≠ x1) (h02 : x0 ≠ x2) (h12 : x1 ≠ x2) :
    distinctTripleEmbedding x0 x1 x2 h01 h02 h12 1 = x1 := rfl

@[simp] theorem distinctTripleEmbedding_two {d : ℕ} (x0 x1 x2 : Fin d)
    (h01 : x0 ≠ x1) (h02 : x0 ≠ x2) (h12 : x1 ≠ x2) :
    distinctTripleEmbedding x0 x1 x2 h01 h02 h12 2 = x2 := rfl

theorem exists_physicalPermutation_triple_embedding {d : ℕ} (hd : 3 ≤ d)
    (x : Fin 3 ↪ Fin d) :
    ∃ σ : Equiv.Perm (Fin d), ∀ i : Fin 3,
      σ.symm (canonicalTripleEmbedding hd i) = x i := by
  obtain ⟨τ, hτ⟩ := Equiv.Perm.exists_extending_pair
    (canonicalTripleEmbedding hd) x (canonicalTripleEmbedding hd).injective x.injective
  exact ⟨τ.symm, fun i => by simpa using hτ i⟩

def triplePermutation {d : ℕ} (hd : 3 ≤ d) (x : Fin 3 ↪ Fin d) :
    Equiv.Perm (Fin d) :=
  Classical.choose (exists_physicalPermutation_triple_embedding hd x)

theorem triplePermutation_symm_apply {d : ℕ} (hd : 3 ≤ d) (x : Fin 3 ↪ Fin d)
    (i : Fin 3) :
    (triplePermutation hd x).symm (canonicalTripleEmbedding hd i) = x i :=
  Classical.choose_spec (exists_physicalPermutation_triple_embedding hd x) i

def triplePhysicalUnitary {d : ℕ} (hd : 3 ≤ d) (x : Fin 3 ↪ Fin d) :
    PhysicalUnitary d :=
  physicalPermutation (triplePermutation hd x)

theorem triplePhysicalUnitary_column {d : ℕ} (hd : 3 ≤ d) (x : Fin 3 ↪ Fin d)
    (i : Fin 3) :
    (fun r => triplePhysicalUnitary hd x r (canonicalTripleEmbedding hd i)) =
      Pi.single (x i) 1 := by
  rw [triplePhysicalUnitary, physicalPermutation_column, triplePermutation_symm_apply]

theorem triplePhysicalUnitary_orderedWedge {d : ℕ} (hd : 3 ≤ d) (x : Fin 3 ↪ Fin d)
    (i j : Fin 3) :
    (wedgeAction (triplePhysicalUnitary hd x)).mulVec
      (orderedWedge (canonicalTripleEmbedding hd i) (canonicalTripleEmbedding hd j)) =
      orderedWedge (x i) (x j) := by
  rw [triplePhysicalUnitary, physicalPermutation_orderedWedge,
    triplePermutation_symm_apply, triplePermutation_symm_apply]

theorem triplePhysicalUnitary_replicaProduct {d : ℕ} (hd : 3 ≤ d) (x : Fin 3 ↪ Fin d)
    (i j k l : Fin 3) :
    (wedgeSquareAction (triplePhysicalUnitary hd x)).mulVec
      (replicaProduct
        (orderedWedge (canonicalTripleEmbedding hd i) (canonicalTripleEmbedding hd j))
        (orderedWedge (canonicalTripleEmbedding hd k) (canonicalTripleEmbedding hd l))) =
      replicaProduct (orderedWedge (x i) (x j)) (orderedWedge (x k) (x l)) := by
  rw [wedgeSquareAction_replicaProduct, triplePhysicalUnitary_orderedWedge,
    triplePhysicalUnitary_orderedWedge]

theorem triplePhysicalUnitary_common_difference {d : ℕ} (hd : 3 ≤ d)
    (x : Fin 3 ↪ Fin d) :
    (wedgeSquareAction (triplePhysicalUnitary hd x)).mulVec
      (replicaProduct
        (orderedWedge (canonicalTripleEmbedding hd 0) (canonicalTripleEmbedding hd 1))
        (orderedWedge (canonicalTripleEmbedding hd 0) (canonicalTripleEmbedding hd 2)) -
       replicaProduct
        (orderedWedge (canonicalTripleEmbedding hd 0) (canonicalTripleEmbedding hd 2))
        (orderedWedge (canonicalTripleEmbedding hd 0) (canonicalTripleEmbedding hd 1))) =
      replicaProduct (orderedWedge (x 0) (x 1)) (orderedWedge (x 0) (x 2)) -
      replicaProduct (orderedWedge (x 0) (x 2)) (orderedWedge (x 0) (x 1)) := by
  rw [Matrix.mulVec_sub, triplePhysicalUnitary_replicaProduct,
    triplePhysicalUnitary_replicaProduct]

theorem exists_physicalUnitary_distinct_triple {d : ℕ} (hd : 3 ≤ d)
    (x0 x1 x2 : Fin d) (h01 : x0 ≠ x1) (h02 : x0 ≠ x2) (h12 : x1 ≠ x2) :
    ∃ V : PhysicalUnitary d,
      (∀ i : Fin 3, (fun r => V r (canonicalTripleEmbedding hd i)) =
        Pi.single (distinctTripleEmbedding x0 x1 x2 h01 h02 h12 i) 1) ∧
      (wedgeSquareAction V).mulVec
        (replicaProduct
          (orderedWedge (canonicalTripleEmbedding hd 0) (canonicalTripleEmbedding hd 1))
          (orderedWedge (canonicalTripleEmbedding hd 0) (canonicalTripleEmbedding hd 2)) -
         replicaProduct
          (orderedWedge (canonicalTripleEmbedding hd 0) (canonicalTripleEmbedding hd 2))
          (orderedWedge (canonicalTripleEmbedding hd 0) (canonicalTripleEmbedding hd 1))) =
        replicaProduct (orderedWedge x0 x1) (orderedWedge x0 x2) -
          replicaProduct (orderedWedge x0 x2) (orderedWedge x0 x1) := by
  let x := distinctTripleEmbedding x0 x1 x2 h01 h02 h12
  refine ⟨triplePhysicalUnitary hd x, triplePhysicalUnitary_column hd x, ?_⟩
  simpa only [x, distinctTripleEmbedding_zero, distinctTripleEmbedding_one,
    distinctTripleEmbedding_two] using triplePhysicalUnitary_common_difference hd x

end QuantumProver.WernerEndpoint.SlaterMoments

namespace QuantumProver.WernerEndpoint

open scoped BigOperators Kronecker

variable {Y B E : Type*} [Fintype Y] [Fintype B] [Fintype E] [DecidableEq Y]

def krausCoeff (K : E → Matrix B Y ℂ) : Matrix (B × E) Y ℂ :=
  fun be y => K be.2 be.1 y

omit [Fintype Y] [DecidableEq Y] in

theorem krausCoeff_gram (K : E → Matrix B Y ℂ) :
    (krausCoeff K).conjTranspose * krausCoeff K =
      ∑ e : E, (K e).conjTranspose * K e := by
  ext y z
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, krausCoeff,
    Fintype.sum_prod_type, Matrix.sum_apply]
  exact Finset.sum_comm

omit [Fintype B] [DecidableEq Y] in

theorem krausCoeff_apply (K : E → Matrix B Y ℂ) (ρ : Matrix Y Y ℂ) :
    partialTraceLeft (krausCoeff K * ρ * (krausCoeff K).conjTranspose) =
      ∑ e : E, K e * ρ * (K e).conjTranspose := by
  ext b c
  simp only [partialTraceLeft, Matrix.mul_apply, Matrix.conjTranspose_apply,
    krausCoeff, Matrix.sum_apply]

def stinespringOfKraus (K : E → Matrix B Y ℂ)
    (hcomplete : (∑ e : E, (K e).conjTranspose * K e) = 1) : Stinespring Y B E :=
  ⟨krausCoeff K, by rw [krausCoeff_gram, hcomplete]⟩

@[simp] theorem stinespringOfKraus_coeff (K : E → Matrix B Y ℂ)
    (hcomplete : (∑ e : E, (K e).conjTranspose * K e) = 1) (b : B) (e : E) (y : Y) :
    (stinespringOfKraus K hcomplete).coeff (b, e) y = K e b y := rfl

theorem stinespringOfKraus_apply (K : E → Matrix B Y ℂ)
    (hcomplete : (∑ e : E, (K e).conjTranspose * K e) = 1) (ρ : Matrix Y Y ℂ) :
    (stinespringOfKraus K hcomplete).apply ρ =
      ∑ e : E, K e * ρ * (K e).conjTranspose :=
  krausCoeff_apply K ρ

theorem stinespringOfKraus_apply_map (K : E → Matrix B Y ℂ)
    (hcomplete : (∑ e : E, (K e).conjTranspose * K e) = 1) :
    (stinespringOfKraus K hcomplete).apply =
      fun ρ : Matrix Y Y ℂ => ∑ e : E, K e * ρ * (K e).conjTranspose := by
  funext ρ
  exact stinespringOfKraus_apply K hcomplete ρ

namespace Stinespring

def krausSlice (N : Stinespring Y B E) (e : E) : Matrix B Y ℂ :=
  fun b y => N.coeff (b, e) y

theorem coeff_eq_krausCoeff_slice (N : Stinespring Y B E) :
    N.coeff = krausCoeff N.krausSlice := by
  ext ⟨b, e⟩ y
  rfl

theorem krausSlice_complete (N : Stinespring Y B E) :
    (∑ e : E, (N.krausSlice e).conjTranspose * N.krausSlice e) = 1 := by
  calc
    _ = N.coeff.conjTranspose * N.coeff := by
      simpa only [← coeff_eq_krausCoeff_slice] using (krausCoeff_gram N.krausSlice).symm
    _ = 1 := N.gram_eq_one

theorem apply_eq_sum_krausSlice (N : Stinespring Y B E) (ρ : Matrix Y Y ℂ) :
    N.apply ρ = ∑ e : E, N.krausSlice e * ρ * (N.krausSlice e).conjTranspose := by
  simpa only [apply, ← coeff_eq_krausCoeff_slice] using krausCoeff_apply N.krausSlice ρ

@[simp] theorem krausSlice_stinespringOfKraus (K : E → Matrix B Y ℂ)
    (hcomplete : (∑ e : E, (K e).conjTranspose * K e) = 1) :
    (stinespringOfKraus K hcomplete).krausSlice = K := by
  funext e b y
  rfl

theorem stinespringOfKraus_krausSlice (N : Stinespring Y B E) :
    stinespringOfKraus N.krausSlice N.krausSlice_complete = N := by
  cases N
  rfl

theorem stinespringOfKraus_krausSlice_apply_map (N : Stinespring Y B E) :
    (stinespringOfKraus N.krausSlice N.krausSlice_complete).apply = N.apply := by
  rw [stinespringOfKraus_krausSlice]

theorem krausSlice_withReference (N : Stinespring Y B E) (R : Type*)
    [Fintype R] [DecidableEq R] (e : E) :
    (N.withReference R).krausSlice e =
      (1 : Matrix R R ℂ) ⊗ₖ N.krausSlice e := by
  ext ⟨r, b⟩ ⟨s, y⟩
  simp [krausSlice, withReference, referenceCoeff, Matrix.kroneckerMap_apply,
    Matrix.one_apply, ite_mul]

theorem krausSlice_withReference_complete (N : Stinespring Y B E) (R : Type*)
    [Fintype R] [DecidableEq R] :
    (∑ e : E, ((1 : Matrix R R ℂ) ⊗ₖ N.krausSlice e).conjTranspose *
      ((1 : Matrix R R ℂ) ⊗ₖ N.krausSlice e)) = 1 := by
  simpa only [krausSlice_withReference] using (N.withReference R).krausSlice_complete

theorem withReference_apply_eq_sum_krausSlice (N : Stinespring Y B E) (R : Type*)
    [Fintype R] [DecidableEq R] (ρ : Matrix (R × Y) (R × Y) ℂ) :
    (N.withReference R).apply ρ =
      ∑ e : E, ((1 : Matrix R R ℂ) ⊗ₖ N.krausSlice e) * ρ *
        ((1 : Matrix R R ℂ) ⊗ₖ N.krausSlice e).conjTranspose := by
  rw [apply_eq_sum_krausSlice]
  simp only [krausSlice_withReference]

end Stinespring

theorem stinespringOfKraus_withReference_coeff (K : E → Matrix B Y ℂ)
    (hcomplete : (∑ e : E, (K e).conjTranspose * K e) = 1)
    (R : Type*) [Fintype R] [DecidableEq R] (r s : R) (b : B) (e : E) (y : Y) :
    ((stinespringOfKraus K hcomplete).withReference R).coeff ((r, b), e) (s, y) =
      (1 : Matrix R R ℂ) r s * K e b y := by
  simp [Stinespring.withReference, Stinespring.referenceCoeff, stinespringOfKraus,
    krausCoeff, Matrix.one_apply, ite_mul]

theorem stinespringOfKraus_withReference_apply (K : E → Matrix B Y ℂ)
    (hcomplete : (∑ e : E, (K e).conjTranspose * K e) = 1)
    (R : Type*) [Fintype R] [DecidableEq R] (ρ : Matrix (R × Y) (R × Y) ℂ) :
    ((stinespringOfKraus K hcomplete).withReference R).apply ρ =
      ∑ e : E, ((1 : Matrix R R ℂ) ⊗ₖ K e) * ρ *
        ((1 : Matrix R R ℂ) ⊗ₖ K e).conjTranspose := by
  simpa only [Stinespring.krausSlice_stinespringOfKraus] using
    (stinespringOfKraus K hcomplete).withReference_apply_eq_sum_krausSlice R ρ

end QuantumProver.WernerEndpoint

namespace QuantumProver.WernerEndpoint

open scoped BigOperators Kronecker

theorem referenceKraus_prodComm {Y B : Type*} (K : Matrix B Y ℂ)
    (R : Type*) [DecidableEq R] :
    (((1 : Matrix R R ℂ) ⊗ₖ K).submatrix
      (Equiv.prodComm B R) (Equiv.prodComm Y R)) =
      K ⊗ₖ (1 : Matrix R R ℂ) := by
  ext ⟨b, r⟩ ⟨y, s⟩
  change (1 : Matrix R R ℂ) r s * K b y =
    K b y * (1 : Matrix R R ℂ) r s
  exact mul_comm _ _

namespace Stinespring

variable {Y B E : Type*} [Fintype Y] [Fintype B] [Fintype E] [DecidableEq Y]

theorem withReference_apply_eq_outputFirst_of_apply_eq
    (N : Stinespring Y B E) (Φ : Matrix Y Y ℂ →ₗ[ℂ] Matrix B B ℂ)
    (hmap : N.apply = (Φ : Matrix Y Y ℂ → Matrix B B ℂ))
    (R : Type*) [Fintype R] [DecidableEq R]
    (ρ : Matrix (R × Y) (R × Y) ℂ) :
    (N.withReference R).apply ρ =
      (QuantumProver.SuperchannelDiscrimination.CPTPKraus.amplify Φ R
        (ρ.submatrix (Equiv.prodComm Y R) (Equiv.prodComm Y R))).submatrix
          (Equiv.prodComm R B) (Equiv.prodComm R B) := by
  ext ⟨r, b⟩ ⟨s, c⟩
  change N.amplify ρ (r, b) (s, c) =
    Φ (fun y z => ρ (r, y) (s, z)) b c
  rw [N.amplify_block, hmap]

theorem withReference_apply_prodComm_of_apply_eq
    (N : Stinespring Y B E) (Φ : Matrix Y Y ℂ →ₗ[ℂ] Matrix B B ℂ)
    (hmap : N.apply = (Φ : Matrix Y Y ℂ → Matrix B B ℂ))
    (R : Type*) [Fintype R] [DecidableEq R]
    (ρ : Matrix (R × Y) (R × Y) ℂ) :
    ((N.withReference R).apply ρ).submatrix
      (Equiv.prodComm B R) (Equiv.prodComm B R) =
      QuantumProver.SuperchannelDiscrimination.CPTPKraus.amplify Φ R
        (ρ.submatrix (Equiv.prodComm Y R) (Equiv.prodComm Y R)) := by
  ext ⟨b, r⟩ ⟨c, s⟩
  change N.amplify ρ (r, b) (s, c) =
    Φ (fun y z => ρ (r, y) (s, z)) b c
  rw [N.amplify_block, hmap]

end Stinespring

variable {Y B : Type*} [Fintype Y] [Fintype B] [DecidableEq Y] [DecidableEq B]

def stinespringOfCPTP (Φ : Matrix Y Y ℂ →ₗ[ℂ] Matrix B B ℂ)
    (hCP : QuantumProver.SuperchannelDiscrimination.CPTPKraus.CompletelyPositive Φ)
    (hTP : QuantumProver.SuperchannelDiscrimination.CPTPKraus.TracePreserving Φ) :
    Stinespring Y B (Y × B) :=
  stinespringOfKraus (QuantumProver.SuperchannelDiscrimination.CPTPKraus.canonicalKraus Φ)
    (QuantumProver.SuperchannelDiscrimination.CPTPKraus.canonicalKraus_gram Φ hCP hTP)

@[simp] theorem stinespringOfCPTP_coeff
    (Φ : Matrix Y Y ℂ →ₗ[ℂ] Matrix B B ℂ)
    (hCP : QuantumProver.SuperchannelDiscrimination.CPTPKraus.CompletelyPositive Φ)
    (hTP : QuantumProver.SuperchannelDiscrimination.CPTPKraus.TracePreserving Φ)
    (b : B) (q : Y × B) (y : Y) :
    (stinespringOfCPTP Φ hCP hTP).coeff (b, q) y =
      QuantumProver.SuperchannelDiscrimination.CPTPKraus.canonicalKraus Φ q b y := rfl

theorem stinespringOfCPTP_apply
    (Φ : Matrix Y Y ℂ →ₗ[ℂ] Matrix B B ℂ)
    (hCP : QuantumProver.SuperchannelDiscrimination.CPTPKraus.CompletelyPositive Φ)
    (hTP : QuantumProver.SuperchannelDiscrimination.CPTPKraus.TracePreserving Φ)
    (ρ : Matrix Y Y ℂ) : (stinespringOfCPTP Φ hCP hTP).apply ρ = Φ ρ := by
  rw [stinespringOfCPTP, stinespringOfKraus_apply]
  exact (QuantumProver.SuperchannelDiscrimination.CPTPKraus.canonicalKraus_reconstruct Φ hCP ρ).symm

theorem stinespringOfCPTP_apply_map
    (Φ : Matrix Y Y ℂ →ₗ[ℂ] Matrix B B ℂ)
    (hCP : QuantumProver.SuperchannelDiscrimination.CPTPKraus.CompletelyPositive Φ)
    (hTP : QuantumProver.SuperchannelDiscrimination.CPTPKraus.TracePreserving Φ) :
    (stinespringOfCPTP Φ hCP hTP).apply =
      (Φ : Matrix Y Y ℂ → Matrix B B ℂ) := by
  funext ρ
  exact stinespringOfCPTP_apply Φ hCP hTP ρ

@[simp] theorem stinespringOfCPTP_krausSlice
    (Φ : Matrix Y Y ℂ →ₗ[ℂ] Matrix B B ℂ)
    (hCP : QuantumProver.SuperchannelDiscrimination.CPTPKraus.CompletelyPositive Φ)
    (hTP : QuantumProver.SuperchannelDiscrimination.CPTPKraus.TracePreserving Φ) :
    (stinespringOfCPTP Φ hCP hTP).krausSlice =
      QuantumProver.SuperchannelDiscrimination.CPTPKraus.canonicalKraus Φ :=
  Stinespring.krausSlice_stinespringOfKraus _ _

theorem stinespringOfCPTP_withReference_krausSlice
    (Φ : Matrix Y Y ℂ →ₗ[ℂ] Matrix B B ℂ)
    (hCP : QuantumProver.SuperchannelDiscrimination.CPTPKraus.CompletelyPositive Φ)
    (hTP : QuantumProver.SuperchannelDiscrimination.CPTPKraus.TracePreserving Φ)
    (R : Type*) [Fintype R] [DecidableEq R] (q : Y × B) :
    ((stinespringOfCPTP Φ hCP hTP).withReference R).krausSlice q =
      (1 : Matrix R R ℂ) ⊗ₖ
        QuantumProver.SuperchannelDiscrimination.CPTPKraus.canonicalKraus Φ q := by
  rw [Stinespring.krausSlice_withReference, stinespringOfCPTP_krausSlice]

theorem stinespringOfCPTP_withReference_krausSlice_prodComm
    (Φ : Matrix Y Y ℂ →ₗ[ℂ] Matrix B B ℂ)
    (hCP : QuantumProver.SuperchannelDiscrimination.CPTPKraus.CompletelyPositive Φ)
    (hTP : QuantumProver.SuperchannelDiscrimination.CPTPKraus.TracePreserving Φ)
    (R : Type*) [Fintype R] [DecidableEq R] (q : Y × B) :
    (((stinespringOfCPTP Φ hCP hTP).withReference R).krausSlice q).submatrix
      (Equiv.prodComm B R) (Equiv.prodComm Y R) =
      QuantumProver.SuperchannelDiscrimination.CPTPKraus.stabilizedKraus Φ R q := by
  rw [stinespringOfCPTP_withReference_krausSlice]
  exact referenceKraus_prodComm _ R

theorem stinespringOfCPTP_withReference_apply_kraus
    (Φ : Matrix Y Y ℂ →ₗ[ℂ] Matrix B B ℂ)
    (hCP : QuantumProver.SuperchannelDiscrimination.CPTPKraus.CompletelyPositive Φ)
    (hTP : QuantumProver.SuperchannelDiscrimination.CPTPKraus.TracePreserving Φ)
    (R : Type*) [Fintype R] [DecidableEq R]
    (ρ : Matrix (R × Y) (R × Y) ℂ) :
    ((stinespringOfCPTP Φ hCP hTP).withReference R).apply ρ =
      ∑ q : Y × B,
        ((1 : Matrix R R ℂ) ⊗ₖ
          QuantumProver.SuperchannelDiscrimination.CPTPKraus.canonicalKraus Φ q) * ρ *
        ((1 : Matrix R R ℂ) ⊗ₖ
          QuantumProver.SuperchannelDiscrimination.CPTPKraus.canonicalKraus Φ q).conjTranspose := by
  simpa only [stinespringOfCPTP] using
    stinespringOfKraus_withReference_apply
      (QuantumProver.SuperchannelDiscrimination.CPTPKraus.canonicalKraus Φ)
      (QuantumProver.SuperchannelDiscrimination.CPTPKraus.canonicalKraus_gram Φ hCP hTP) R ρ

theorem stinespringOfCPTP_withReference_apply
    (Φ : Matrix Y Y ℂ →ₗ[ℂ] Matrix B B ℂ)
    (hCP : QuantumProver.SuperchannelDiscrimination.CPTPKraus.CompletelyPositive Φ)
    (hTP : QuantumProver.SuperchannelDiscrimination.CPTPKraus.TracePreserving Φ)
    (R : Type*) [Fintype R] [DecidableEq R]
    (ρ : Matrix (R × Y) (R × Y) ℂ) :
    ((stinespringOfCPTP Φ hCP hTP).withReference R).apply ρ =
      (QuantumProver.SuperchannelDiscrimination.CPTPKraus.amplify Φ R
        (ρ.submatrix (Equiv.prodComm Y R) (Equiv.prodComm Y R))).submatrix
          (Equiv.prodComm R B) (Equiv.prodComm R B) :=
  Stinespring.withReference_apply_eq_outputFirst_of_apply_eq _ Φ
    (stinespringOfCPTP_apply_map Φ hCP hTP) R ρ

theorem stinespringOfCPTP_withReference_apply_prodComm
    (Φ : Matrix Y Y ℂ →ₗ[ℂ] Matrix B B ℂ)
    (hCP : QuantumProver.SuperchannelDiscrimination.CPTPKraus.CompletelyPositive Φ)
    (hTP : QuantumProver.SuperchannelDiscrimination.CPTPKraus.TracePreserving Φ)
    (R : Type*) [Fintype R] [DecidableEq R]
    (ρ : Matrix (R × Y) (R × Y) ℂ) :
    (((stinespringOfCPTP Φ hCP hTP).withReference R).apply ρ).submatrix
      (Equiv.prodComm B R) (Equiv.prodComm B R) =
      QuantumProver.SuperchannelDiscrimination.CPTPKraus.amplify Φ R
        (ρ.submatrix (Equiv.prodComm Y R) (Equiv.prodComm Y R)) :=
  Stinespring.withReference_apply_prodComm_of_apply_eq _ Φ
    (stinespringOfCPTP_apply_map Φ hCP hTP) R ρ

theorem exists_stinespring_of_cptp
    (Φ : Matrix Y Y ℂ →ₗ[ℂ] Matrix B B ℂ)
    (hCP : QuantumProver.SuperchannelDiscrimination.CPTPKraus.CompletelyPositive Φ)
    (hTP : QuantumProver.SuperchannelDiscrimination.CPTPKraus.TracePreserving Φ) :
    ∃ N : Stinespring Y B (Y × B),
      N.apply = (Φ : Matrix Y Y ℂ → Matrix B B ℂ) ∧
      ∀ (R : Type*) [Fintype R] [DecidableEq R]
        (ρ : Matrix (R × Y) (R × Y) ℂ),
        (N.withReference R).apply ρ =
          (QuantumProver.SuperchannelDiscrimination.CPTPKraus.amplify Φ R
            (ρ.submatrix (Equiv.prodComm Y R) (Equiv.prodComm Y R))).submatrix
              (Equiv.prodComm R B) (Equiv.prodComm R B) := by
  obtain ⟨K, hK, hΦ⟩ :=
    QuantumProver.SuperchannelDiscrimination.CPTPKraus.exists_complete_kraus Φ hCP hTP
  let N := stinespringOfKraus K hK
  have hmap : N.apply = (Φ : Matrix Y Y ℂ → Matrix B B ℂ) := by
    funext ρ
    exact (stinespringOfKraus_apply K hK ρ).trans (hΦ ρ).symm
  refine ⟨N, hmap, ?_⟩
  intro R _ _ ρ
  exact N.withReference_apply_eq_outputFirst_of_apply_eq Φ hmap R ρ

end QuantumProver.WernerEndpoint

namespace QuantumProver.WernerEndpoint.CPInstrument

open scoped BigOperators Kronecker
open QuantumProver.SuperchannelDiscrimination.CPTPKraus

variable {H Y B : Type*} [Fintype H] [Fintype Y] [Fintype B]
  [DecidableEq H] [DecidableEq Y] [DecidableEq B]

def selectiveKraus (Φ : H → Matrix Y Y ℂ →ₗ[ℂ] Matrix B B ℂ) :
    H × (Y × B) → Matrix B Y ℂ :=
  fun he => canonicalKraus (Φ he.1) he.2

omit [Fintype H] [DecidableEq H] in

theorem selectiveKraus_branch
    (Φ : H → Matrix Y Y ℂ →ₗ[ℂ] Matrix B B ℂ)
    (hCP : ∀ h, CompletelyPositive (Φ h)) (h : H) (ρ : Matrix Y Y ℂ) :
    Φ h ρ = ∑ e : Y × B,
      selectiveKraus Φ (h, e) * ρ * (selectiveKraus Φ (h, e)).conjTranspose := by
  simpa only [selectiveKraus] using canonicalKraus_reconstruct (Φ h) (hCP h) ρ

omit [DecidableEq H] in

theorem selectiveKraus_totalGram
    (Φ : H → Matrix Y Y ℂ →ₗ[ℂ] Matrix B B ℂ)
    (hCP : ∀ h, CompletelyPositive (Φ h))
    (hTotal : ∀ ρ : Matrix Y Y ℂ, ∑ h : H, (Φ h ρ).trace = ρ.trace) :
    (∑ he : H × (Y × B),
      (selectiveKraus Φ he).conjTranspose * selectiveKraus Φ he) = 1 := by
  have hsplit :
      (∑ he : H × (Y × B),
        (selectiveKraus Φ he).conjTranspose * selectiveKraus Φ he) =
      ∑ h : H, canonicalGram (Φ h) := by
    simp only [selectiveKraus, Fintype.sum_prod_type, canonicalGram]
  rw [hsplit]
  apply Matrix.ext_iff_trace_mul_right.mpr
  intro ρ
  rw [Matrix.one_mul, Matrix.sum_mul, Matrix.trace_sum]
  calc
    (∑ h : H, (canonicalGram (Φ h) * ρ).trace) =
        ∑ h : H, (Φ h ρ).trace := by
      apply Finset.sum_congr rfl
      intro h _
      exact (canonicalKraus_trace (Φ h) (hCP h) ρ).symm
    _ = ρ.trace := hTotal ρ

def flaggedKraus (Φ : H → Matrix Y Y ℂ →ₗ[ℂ] Matrix B B ℂ) :
    H × (Y × B) → Matrix (H × B) Y ℂ :=
  fun he hb y => if hb.1 = he.1 then selectiveKraus Φ he hb.2 y else 0

theorem flaggedKraus_gram
    (Φ : H → Matrix Y Y ℂ →ₗ[ℂ] Matrix B B ℂ) (he : H × (Y × B)) :
    (flaggedKraus Φ he).conjTranspose * flaggedKraus Φ he =
      (selectiveKraus Φ he).conjTranspose * selectiveKraus Φ he := by
  ext y z
  simp [flaggedKraus, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fintype.sum_prod_type, apply_ite, mul_ite, ite_mul]

theorem flaggedKraus_complete
    (Φ : H → Matrix Y Y ℂ →ₗ[ℂ] Matrix B B ℂ)
    (hCP : ∀ h, CompletelyPositive (Φ h))
    (hTotal : ∀ ρ : Matrix Y Y ℂ, ∑ h : H, (Φ h ρ).trace = ρ.trace) :
    (∑ he : H × (Y × B),
      (flaggedKraus Φ he).conjTranspose * flaggedKraus Φ he) = 1 := by
  simpa only [flaggedKraus_gram] using selectiveKraus_totalGram Φ hCP hTotal

omit [Fintype H] in

theorem flaggedKraus_sandwich_entry
    (Φ : H → Matrix Y Y ℂ →ₗ[ℂ] Matrix B B ℂ) (he : H × (Y × B))
    (ρ : Matrix Y Y ℂ) (h k : H) (b c : B) :
    (flaggedKraus Φ he * ρ * (flaggedKraus Φ he).conjTranspose) (h, b) (k, c) =
      if h = he.1 ∧ k = he.1 then
        (selectiveKraus Φ he * ρ * (selectiveKraus Φ he).conjTranspose) b c else 0 := by
  by_cases hh : h = he.1 <;> by_cases hk : k = he.1 <;>
    simp [flaggedKraus, Matrix.mul_apply, Matrix.conjTranspose_apply,
      hh, hk, apply_ite, mul_ite, ite_mul]

def flaggedMap (Φ : H → Matrix Y Y ℂ →ₗ[ℂ] Matrix B B ℂ) :
    Matrix Y Y ℂ →ₗ[ℂ] Matrix (H × B) (H × B) ℂ :=
  QuantumProver.ElegantJointMeasurement.CP.krausMap (flaggedKraus Φ)

theorem flaggedMap_block
    (Φ : H → Matrix Y Y ℂ →ₗ[ℂ] Matrix B B ℂ)
    (hCP : ∀ h, CompletelyPositive (Φ h))
    (ρ : Matrix Y Y ℂ) (h k : H) (b c : B) :
    flaggedMap Φ ρ (h, b) (k, c) = if h = k then Φ h ρ b c else 0 := by
  change (∑ he : H × (Y × B),
    flaggedKraus Φ he * ρ * (flaggedKraus Φ he).conjTranspose) (h, b) (k, c) = _
  simp only [Matrix.sum_apply, Fintype.sum_prod_type]
  simp_rw [flaggedKraus_sandwich_entry]
  by_cases hk : h = k
  · subst k
    have hentry := congrArg (fun M : Matrix B B ℂ => M b c)
      (selectiveKraus_branch Φ hCP h ρ)
    simp only [Matrix.sum_apply] at hentry
    simpa [Finset.sum_ite_irrel, Fintype.sum_prod_type] using hentry.symm
  · have hcross : ∀ j : H, ¬ (h = j ∧ k = j) := by
      intro j hj
      exact hk (hj.1.trans hj.2.symm)
    simp [hk, hcross]

theorem flaggedMap_completelyPositive
    (Φ : H → Matrix Y Y ℂ →ₗ[ℂ] Matrix B B ℂ) :
    CompletelyPositive (flaggedMap Φ) :=
  (completelyPositive_iff_EJMCP _).mpr (QuantumProver.ElegantJointMeasurement.CP.krausMap_completelyPositive (flaggedKraus Φ))

theorem flaggedMap_tracePreserving
    (Φ : H → Matrix Y Y ℂ →ₗ[ℂ] Matrix B B ℂ)
    (hCP : ∀ h, CompletelyPositive (Φ h))
    (hTotal : ∀ ρ : Matrix Y Y ℂ, ∑ h : H, (Φ h ρ).trace = ρ.trace) :
    TracePreserving (flaggedMap Φ) :=
  (QuantumProver.ElegantJointMeasurement.CP.krausMap_trace_preserving_iff (flaggedKraus Φ)).mpr
    (flaggedKraus_complete Φ hCP hTotal)

def flaggedStinespring
    (Φ : H → Matrix Y Y ℂ →ₗ[ℂ] Matrix B B ℂ)
    (hCP : ∀ h, CompletelyPositive (Φ h))
    (hTotal : ∀ ρ : Matrix Y Y ℂ, ∑ h : H, (Φ h ρ).trace = ρ.trace) :
    Stinespring Y (H × B) (H × (Y × B)) :=
  stinespringOfKraus (flaggedKraus Φ) (flaggedKraus_complete Φ hCP hTotal)

@[simp] theorem flaggedStinespring_coeff
    (Φ : H → Matrix Y Y ℂ →ₗ[ℂ] Matrix B B ℂ)
    (hCP : ∀ h, CompletelyPositive (Φ h))
    (hTotal : ∀ ρ : Matrix Y Y ℂ, ∑ h : H, (Φ h ρ).trace = ρ.trace)
    (h j : H) (b : B) (e : Y × B) (y : Y) :
    (flaggedStinespring Φ hCP hTotal).coeff ((h, b), (j, e)) y =
      if h = j then canonicalKraus (Φ j) e b y else 0 := rfl

theorem flaggedStinespring_apply
    (Φ : H → Matrix Y Y ℂ →ₗ[ℂ] Matrix B B ℂ)
    (hCP : ∀ h, CompletelyPositive (Φ h))
    (hTotal : ∀ ρ : Matrix Y Y ℂ, ∑ h : H, (Φ h ρ).trace = ρ.trace)
    (ρ : Matrix Y Y ℂ) :
    (flaggedStinespring Φ hCP hTotal).apply ρ = flaggedMap Φ ρ :=
  stinespringOfKraus_apply (flaggedKraus Φ) (flaggedKraus_complete Φ hCP hTotal) ρ

theorem flaggedStinespring_apply_map
    (Φ : H → Matrix Y Y ℂ →ₗ[ℂ] Matrix B B ℂ)
    (hCP : ∀ h, CompletelyPositive (Φ h))
    (hTotal : ∀ ρ : Matrix Y Y ℂ, ∑ h : H, (Φ h ρ).trace = ρ.trace) :
    (flaggedStinespring Φ hCP hTotal).apply =
      (flaggedMap Φ : Matrix Y Y ℂ → Matrix (H × B) (H × B) ℂ) := by
  funext ρ
  exact flaggedStinespring_apply Φ hCP hTotal ρ

theorem flaggedStinespring_apply_block
    (Φ : H → Matrix Y Y ℂ →ₗ[ℂ] Matrix B B ℂ)
    (hCP : ∀ h, CompletelyPositive (Φ h))
    (hTotal : ∀ ρ : Matrix Y Y ℂ, ∑ h : H, (Φ h ρ).trace = ρ.trace)
    (ρ : Matrix Y Y ℂ) (h k : H) (b c : B) :
    (flaggedStinespring Φ hCP hTotal).apply ρ (h, b) (k, c) =
      if h = k then Φ h ρ b c else 0 := by
  rw [flaggedStinespring_apply, flaggedMap_block Φ hCP]

theorem flaggedStinespring_withReference_krausSlice
    (Φ : H → Matrix Y Y ℂ →ₗ[ℂ] Matrix B B ℂ)
    (hCP : ∀ h, CompletelyPositive (Φ h))
    (hTotal : ∀ ρ : Matrix Y Y ℂ, ∑ h : H, (Φ h ρ).trace = ρ.trace)
    (R : Type*) [Fintype R] [DecidableEq R] (he : H × (Y × B)) :
    ((flaggedStinespring Φ hCP hTotal).withReference R).krausSlice he =
      (1 : Matrix R R ℂ) ⊗ₖ flaggedKraus Φ he := by
  rw [Stinespring.krausSlice_withReference]
  simp only [flaggedStinespring, Stinespring.krausSlice_stinespringOfKraus]

theorem flaggedStinespring_withReference_krausSlice_prodComm
    (Φ : H → Matrix Y Y ℂ →ₗ[ℂ] Matrix B B ℂ)
    (hCP : ∀ h, CompletelyPositive (Φ h))
    (hTotal : ∀ ρ : Matrix Y Y ℂ, ∑ h : H, (Φ h ρ).trace = ρ.trace)
    (R : Type*) [Fintype R] [DecidableEq R] (he : H × (Y × B)) :
    (((flaggedStinespring Φ hCP hTotal).withReference R).krausSlice he).submatrix
      (Equiv.prodComm (H × B) R) (Equiv.prodComm Y R) =
      flaggedKraus Φ he ⊗ₖ (1 : Matrix R R ℂ) := by
  rw [flaggedStinespring_withReference_krausSlice]
  exact referenceKraus_prodComm _ R

theorem flaggedStinespring_withReference_apply_kraus
    (Φ : H → Matrix Y Y ℂ →ₗ[ℂ] Matrix B B ℂ)
    (hCP : ∀ h, CompletelyPositive (Φ h))
    (hTotal : ∀ ρ : Matrix Y Y ℂ, ∑ h : H, (Φ h ρ).trace = ρ.trace)
    (R : Type*) [Fintype R] [DecidableEq R]
    (ρ : Matrix (R × Y) (R × Y) ℂ) :
    ((flaggedStinespring Φ hCP hTotal).withReference R).apply ρ =
      ∑ he : H × (Y × B), ((1 : Matrix R R ℂ) ⊗ₖ flaggedKraus Φ he) * ρ *
        ((1 : Matrix R R ℂ) ⊗ₖ flaggedKraus Φ he).conjTranspose :=
  stinespringOfKraus_withReference_apply (flaggedKraus Φ)
    (flaggedKraus_complete Φ hCP hTotal) R ρ

theorem flaggedStinespring_withReference_apply_block
    (Φ : H → Matrix Y Y ℂ →ₗ[ℂ] Matrix B B ℂ)
    (hCP : ∀ h, CompletelyPositive (Φ h))
    (hTotal : ∀ ρ : Matrix Y Y ℂ, ∑ h : H, (Φ h ρ).trace = ρ.trace)
    (R : Type*) [Fintype R] [DecidableEq R]
    (ρ : Matrix (R × Y) (R × Y) ℂ) (r s : R) (h k : H) (b c : B) :
    ((flaggedStinespring Φ hCP hTotal).withReference R).apply ρ
      (r, (h, b)) (s, (k, c)) =
      if h = k then Φ h (fun y z => ρ (r, y) (s, z)) b c else 0 := by
  exact (Stinespring.amplify_block (flaggedStinespring Φ hCP hTotal)
    ρ r s (h, b) (k, c)).trans
      (flaggedStinespring_apply_block Φ hCP hTotal
        (Matrix.of (fun y z => ρ (r, y) (s, z))) h k b c)

theorem flaggedStinespring_withReference_apply
    (Φ : H → Matrix Y Y ℂ →ₗ[ℂ] Matrix B B ℂ)
    (hCP : ∀ h, CompletelyPositive (Φ h))
    (hTotal : ∀ ρ : Matrix Y Y ℂ, ∑ h : H, (Φ h ρ).trace = ρ.trace)
    (R : Type*) [Fintype R] [DecidableEq R]
    (ρ : Matrix (R × Y) (R × Y) ℂ) :
    ((flaggedStinespring Φ hCP hTotal).withReference R).apply ρ =
      (amplify (flaggedMap Φ) R
        (ρ.submatrix (Equiv.prodComm Y R) (Equiv.prodComm Y R))).submatrix
          (Equiv.prodComm R (H × B)) (Equiv.prodComm R (H × B)) :=
  Stinespring.withReference_apply_eq_outputFirst_of_apply_eq _ _
    (flaggedStinespring_apply_map Φ hCP hTotal) R ρ

end QuantumProver.WernerEndpoint.CPInstrument

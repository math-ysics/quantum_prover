import QuantumProver.InformationTheory.WernerEndpoint.D5SupportFactor
import QuantumProver.InformationTheory.WernerEndpoint.SlaterSquareMoment
import QuantumProver.InformationTheory.WernerEndpoint.AllDimensionalMoment

noncomputable section

namespace QuantumProver.WernerEndpoint.D5NuclearControl

open scoped BigOperators
open Matrix ExteriorSupport ExteriorSchatten RealSymmetricFactor SchattenSupport D5SupportFactor

theorem fourSetEdge_vertices_subset {d : ℕ} (S : FourSet d)
    (i j : Fin 4) (hij : i < j) : edgeVertices (fourSetEdge S i j hij) ⊆ S.val := by
  simp [edgeVertices, fourSetEdge, Finset.insert_subset_iff]

theorem edge_subset_fourSet_iff {d : ℕ} (S : FourSet d) (e : Edge d) :
    edgeVertices e ⊆ S.val ↔
      e = fourSetEdge S 0 1 (by decide) ∨ e = fourSetEdge S 2 3 (by decide) ∨
      e = fourSetEdge S 0 2 (by decide) ∨ e = fourSetEdge S 1 3 (by decide) ∨
      e = fourSetEdge S 0 3 (by decide) ∨ e = fourSetEdge S 1 2 (by decide) := by
  constructor
  · intro hsub
    have h1 : e.val.1 ∈ S.val := hsub (by simp [edgeVertices])
    have h2 : e.val.2 ∈ S.val := hsub (by simp [edgeVertices])
    let Q := S.val.orderIsoOfFin S.property
    let i : Fin 4 := Q.symm ⟨e.val.1, h1⟩
    let j : Fin 4 := Q.symm ⟨e.val.2, h2⟩
    have hi : (S.val.orderEmbOfFin S.property) i = e.val.1 := by
      exact congrArg Subtype.val (Q.apply_symm_apply ⟨e.val.1, h1⟩)
    have hj : (S.val.orderEmbOfFin S.property) j = e.val.2 := by
      exact congrArg Subtype.val (Q.apply_symm_apply ⟨e.val.2, h2⟩)
    have hij : i < j := Q.symm.strictMono e.property
    have he : e = fourSetEdge S i j hij := by
      exact Subtype.ext (Prod.ext hi.symm hj.symm)
    have hp : (i = 0 ∧ j = 1) ∨ (i = 2 ∧ j = 3) ∨ (i = 0 ∧ j = 2) ∨
        (i = 1 ∧ j = 3) ∨ (i = 0 ∧ j = 3) ∨ (i = 1 ∧ j = 2) := by omega
    rcases hp with ⟨hi', hj'⟩ | ⟨hi', hj'⟩ | ⟨hi', hj'⟩ |
      ⟨hi', hj'⟩ | ⟨hi', hj'⟩ | ⟨hi', hj'⟩ <;>
      simp only [hi', hj'] at he <;> simp [he]
  · intro h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact fourSetEdge_vertices_subset S _ _ _

theorem fourSupportMatrix_diagonal {d : ℕ} (S : FourSet d) :
    fourSupportMatrix S = Matrix.diagonal
      (fun e : Edge d => if edgeVertices e ⊆ S.val then (1 : ℝ) else 0) := by
  have hd (e : Edge d) : fourSupportMatrix S e e =
      if edgeVertices e ⊆ S.val then (1 : ℝ) else 0 := by
    by_cases hsub : edgeVertices e ⊆ S.val
    · rw [if_pos hsub]
      rcases (edge_subset_fourSet_iff S e).mp hsub with rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [fourSupportMatrix, Matrix.single_apply, fourSetEdge_eq_iff]
    · rw [if_neg hsub]
      have hn := mt (edge_subset_fourSet_iff S e).mpr hsub
      push_neg at hn
      simp [fourSupportMatrix, Matrix.single_apply, eq_comm, hn.1, hn.2.1,
        hn.2.2.1, hn.2.2.2.1, hn.2.2.2.2.1, hn.2.2.2.2.2]
  ext e f
  by_cases hef : e = f
  · subst f
    simpa only [Matrix.diagonal_apply_eq] using hd e
  · have hz (a : Edge d) : Matrix.single a a (1 : ℝ) e f = 0 := by
      rw [Matrix.single_apply, if_neg]
      rintro ⟨he, hf⟩
      exact hef (he.symm.trans hf)
    simp only [fourSupportMatrix, Matrix.add_apply, hz, add_zero, zero_add]
    simp [Matrix.diagonal_apply, hef]

theorem complexify_fourSupport_omitted (t : Fin 5) :
    complexify (fourSupportMatrix (omittedFourSet t)) = d5SupportMask t := by
  rw [fourSupportMatrix_diagonal, complexify_diagonal]
  unfold d5SupportMask
  congr 1
  funext e
  have hp : edgeVertices e ⊆ (omittedFourSet t).val ↔ t ∉ edgeVertices e := by
    simp only [omittedFourSet, Finset.subset_iff, Finset.mem_erase, Finset.mem_univ,
      and_true, ne_eq]
    constructor
    · intro h ht
      exact h ht rfl
    · intro h x hx he
      subst x
      exact h hx
  by_cases ht : t ∈ edgeVertices e <;> simp [hp, ht]

def d5CovarianceFactor (t : Fin 5) : Matrix (Edge 5) (Edge 5) ℂ :=
  covarianceFactor (realFourFormMatrix (omittedFourSet t))
    (realFourFormMatrix_hermitian (omittedFourSet t))

theorem d5CovarianceFactor_covariance (t : Fin 5) :
    d5CovarianceFactor t * (d5CovarianceFactor t)ᵀ = d5FourFormMatrix t := by
  rw [d5CovarianceFactor, covarianceFactor_covariance, complexify_realFourFormMatrix]
  rfl

theorem d5CovarianceFactor_gram (t : Fin 5) :
    d5CovarianceFactor t * (d5CovarianceFactor t)ᴴ = d5SupportMask t := by
  rw [d5CovarianceFactor, covarianceFactor_gram_of_cube _ _ (realFourFormMatrix_cube _),
    realFourFormMatrix_square, complexify_fourSupport_omitted]

theorem actual_d5_exterior_nuclear_control {Y : Type*} [Fintype Y] [DecidableEq Y]
    (A : Matrix Y (Edge 5) ℂ) (hA : hsNormSq A = 1) :
    (∑ t : Fin 5, schattenOne (orderedExterior (A * d5FourFormMatrix t * Aᵀ))) ≤
      1 - purity (reducedLeft A) := by
  exact d5_exterior_schatten_sum_of_normalized A d5FourFormMatrix d5CovarianceFactor
    d5CovarianceFactor_covariance d5CovarianceFactor_gram hA

end QuantumProver.WernerEndpoint.D5NuclearControl

namespace QuantumProver.WernerEndpoint.ExteriorHaar

open scoped BigOperators Kronecker
open Matrix MeasureTheory QuantumProver.WernerEndpoint.SlaterMoments

def literalExteriorSupportSum (d : ℕ) :
    Matrix (Edge d × Edge d) (Edge d × Edge d) ℂ :=
  ∑ S : FourSet d, ExteriorSupport.orderedExterior
    (RealSymmetricFactor.complexify (D5SupportFactor.fourSupportMatrix S))

def exteriorSupportOrbit {d : ℕ} (U : PhysicalUnitary d) :
    Matrix (Edge d × Edge d) (Edge d × Edge d) ℂ :=
  wedgeSquareAction U * literalExteriorSupportSum d * (wedgeSquareAction U).conjTranspose

theorem wedgeSquareAction_mul_matrix {d : ℕ} (V U : PhysicalUnitary d) :
    wedgeSquareAction (V * U) = wedgeSquareAction V * wedgeSquareAction U := by
  simp only [wedgeSquareAction, wedgeAction_mul, Matrix.mul_kronecker_mul]

theorem exteriorSupportOrbit_mul {d : ℕ} (V U : PhysicalUnitary d) :
    exteriorSupportOrbit (V * U) =
      wedgeSquareAction V * exteriorSupportOrbit U * (wedgeSquareAction V).conjTranspose := by
  simp only [exteriorSupportOrbit, wedgeSquareAction_mul_matrix,
    Matrix.conjTranspose_mul, Matrix.mul_assoc]

theorem wedgeSquareAction_continuous (d : ℕ) :
    Continuous (fun U : PhysicalUnitary d => wedgeSquareAction U) := by
  apply continuous_matrix
  intro ef gh
  exact (columnMinor_continuous gh.1.val.1 gh.1.val.2 ef.1.val.1 ef.1.val.2).mul
    (columnMinor_continuous gh.2.val.1 gh.2.val.2 ef.2.val.1 ef.2.val.2)

theorem exteriorSupportOrbit_continuous (d : ℕ) :
    Continuous (fun U : PhysicalUnitary d => exteriorSupportOrbit U) := by
  exact ((wedgeSquareAction_continuous d).matrix_mul continuous_const).matrix_mul
    (wedgeSquareAction_continuous d).matrix_conjTranspose

theorem exteriorSupportOrbit_function_integrable (d : ℕ) :
    Integrable (fun U : PhysicalUnitary d =>
      fun ef gh : Edge d × Edge d => exteriorSupportOrbit U ef gh) (normalizedHaar d) := by
  have hc : Continuous (fun U : PhysicalUnitary d =>
      fun ef gh : Edge d × Edge d => exteriorSupportOrbit U ef gh) :=
    continuous_pi fun ef => continuous_pi fun gh =>
      (exteriorSupportOrbit_continuous d).matrix_elem ef gh
  simpa [MeasureTheory.IntegrableOn] using hc.continuousOn.integrableOn_compact
    (μ := normalizedHaar d) isCompact_univ

def exteriorSupportHaar (d : ℕ) :
    Matrix (Edge d × Edge d) (Edge d × Edge d) ℂ :=
  Matrix.of (∫ U : PhysicalUnitary d,
    (fun ef gh : Edge d × Edge d => exteriorSupportOrbit U ef gh) ∂normalizedHaar d)

theorem exteriorSupportHaar_covariance {d : ℕ} (V : PhysicalUnitary d) :
    wedgeSquareAction V * exteriorSupportHaar d * (wedgeSquareAction V).conjTranspose =
      exteriorSupportHaar d := by
  have hi := (matrixSandwichCLM (wedgeSquareAction V)).integral_comp_comm
    (exteriorSupportOrbit_function_integrable d)
  have hi' : wedgeSquareAction V * exteriorSupportHaar d *
      (wedgeSquareAction V).conjTranspose = Matrix.of (∫ U : PhysicalUnitary d,
        (fun ef gh : Edge d × Edge d =>
          (wedgeSquareAction V * exteriorSupportOrbit U * (wedgeSquareAction V).conjTranspose) ef gh)
        ∂normalizedHaar d) := hi.symm
  simp_rw [← exteriorSupportOrbit_mul] at hi'
  exact hi'.trans (congrArg Matrix.of (integral_mul_left_eq_self (μ := normalizedHaar d)
    (fun U : PhysicalUnitary d => fun ef gh : Edge d × Edge d => exteriorSupportOrbit U ef gh) V))

theorem exteriorSupportHaar_commutes {d : ℕ} (V : PhysicalUnitary d) :
    wedgeSquareAction V * exteriorSupportHaar d = exteriorSupportHaar d * wedgeSquareAction V := by
  have hr : (wedgeSquareAction V).conjTranspose * wedgeSquareAction V = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using (wedgeSquareAction_mem_unitary V).1
  have h := congrArg (fun A : Matrix (Edge d × Edge d) (Edge d × Edge d) ℂ =>
    A * wedgeSquareAction V) (exteriorSupportHaar_covariance V)
  simpa only [Matrix.mul_assoc, hr, Matrix.mul_one] using h

theorem exteriorSupportOrbit_trace {d : ℕ} (U : PhysicalUnitary d) :
    Matrix.trace (exteriorSupportOrbit U) = Matrix.trace (literalExteriorSupportSum d) := by
  have hr : (wedgeSquareAction U).conjTranspose * wedgeSquareAction U = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using (wedgeSquareAction_mem_unitary U).1
  rw [exteriorSupportOrbit, Matrix.trace_mul_cycle, hr, Matrix.one_mul]

def replicaTraceCLM (d : ℕ) :
    ((Edge d × Edge d) → (Edge d × Edge d) → ℂ) →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap
    ((Matrix.traceLinearMap (Edge d × Edge d) ℂ ℂ).comp (Matrix.ofLinearEquiv ℂ).toLinearMap)

theorem exteriorSupportHaar_trace (d : ℕ) :
    Matrix.trace (exteriorSupportHaar d) = Matrix.trace (literalExteriorSupportSum d) := by
  have hi := (replicaTraceCLM d).integral_comp_comm
    (exteriorSupportOrbit_function_integrable d)
  have hi' : Matrix.trace (exteriorSupportHaar d) =
      ∫ U : PhysicalUnitary d, Matrix.trace (exteriorSupportOrbit U) ∂normalizedHaar d := hi.symm
  rw [hi']
  simp_rw [exteriorSupportOrbit_trace]
  simp

theorem wedgeAction_physicalPhase {d : ℕ} (z : Fin d → ℂ)
    (hz : ∀ a, star (z a) * z a = 1) :
    wedgeAction (physicalPhase z hz) =
      Matrix.diagonal (fun e : Edge d => z e.val.1 * z e.val.2) := by
  ext e f
  have hp := physicalPhase_columnMinor z hz (1 : PhysicalUnitary d)
    f.val.1 f.val.2 e.val.1 e.val.2
  simp only [mul_one] at hp
  calc
    wedgeAction (physicalPhase z hz) e f =
        (z e.val.1 * z e.val.2) * wedgeAction (1 : PhysicalUnitary d) e f := hp
    _ = _ := by rw [wedgeAction_one]; simp [Matrix.one_apply, Matrix.diagonal_apply, mul_ite]

theorem wedgeSquareAction_physicalPhase {d : ℕ} (z : Fin d → ℂ)
    (hz : ∀ a, star (z a) * z a = 1) :
    wedgeSquareAction (physicalPhase z hz) = Matrix.diagonal (phaseCharacter z) := by
  rw [wedgeSquareAction, wedgeAction_physicalPhase, Matrix.diagonal_kronecker_diagonal]
  congr 1
  funext ef
  simp only [phaseCharacter]
  ring

theorem exteriorSupportHaar_entry_eq_zero_of_weight {d : ℕ}
    (a : Fin d) (ef gh : Edge d × Edge d)
    (hweight : weightMultiplicity ef a ≠ weightMultiplicity gh a) :
    exteriorSupportHaar d ef gh = 0 := by
  let z := coordinatePhase a
  have hc := congrArg (fun M : Matrix (Edge d × Edge d) (Edge d × Edge d) ℂ => M ef gh)
    (exteriorSupportHaar_commutes (physicalPhase z (coordinatePhase_unitary a)))
  rw [wedgeSquareAction_physicalPhase] at hc
  have hc' : phaseCharacter z ef * exteriorSupportHaar d ef gh =
      exteriorSupportHaar d ef gh * phaseCharacter z gh := by
    simpa [Matrix.mul_apply, Matrix.diagonal] using hc
  have hne : phaseCharacter z ef ≠ phaseCharacter z gh := by
    intro he
    change phaseCharacter (coordinatePhase a) ef = phaseCharacter (coordinatePhase a) gh at he
    rw [coordinatePhase_character, coordinatePhase_character] at he
    exact hweight (I_pow_injective_le_two (weightMultiplicity_le_two ef a)
      (weightMultiplicity_le_two gh a) he)
  have hzero : (phaseCharacter z ef - phaseCharacter z gh) * exteriorSupportHaar d ef gh = 0 := by
    linear_combination hc'
  exact (mul_eq_zero.mp hzero).resolve_left (sub_ne_zero.mpr hne)

def commonZero (d : ℕ) (hd : 3 ≤ d) : Fin d := ⟨0, by omega⟩
def commonOne (d : ℕ) (hd : 3 ≤ d) : Fin d := ⟨1, by omega⟩
def commonTwo (d : ℕ) (hd : 3 ≤ d) : Fin d := ⟨2, by omega⟩
def firstCommonEdge (d : ℕ) (hd : 3 ≤ d) : Edge d :=
  ⟨(commonZero d hd, commonOne d hd), by norm_num [commonZero, commonOne]⟩
def secondCommonEdge (d : ℕ) (hd : 3 ≤ d) : Edge d :=
  ⟨(commonZero d hd, commonTwo d hd), by norm_num [commonZero, commonTwo]⟩

theorem weight_eq_first_common_rigid (d : ℕ) (hd : 3 ≤ d) (ef : Edge d × Edge d)
    (h : ∀ a : Fin d, weightMultiplicity ef a =
      weightMultiplicity (firstCommonEdge d hd, secondCommonEdge d hd) a) :
    ef = (firstCommonEdge d hd, secondCommonEdge d hd) ∨
      ef = (secondCommonEdge d hd, firstCommonEdge d hd) := by
  let z := commonZero d hd
  let o := commonOne d hd
  let t := commonTwo d hd
  let e₁ := firstCommonEdge d hd
  let e₂ := secondCommonEdge d hd
  have hz : edgeMultiplicity ef.1 z + edgeMultiplicity ef.2 z = 2 := by
    simpa [z, firstCommonEdge, secondCommonEdge, commonZero, commonOne, commonTwo,
      weightMultiplicity, edgeMultiplicity] using h z
  have hz₁ : 0 < edgeMultiplicity ef.1 z := by
    have h₁ := edgeMultiplicity_le_one ef.1 z
    have h₂ := edgeMultiplicity_le_one ef.2 z
    omega
  have hz₂ : 0 < edgeMultiplicity ef.2 z := by
    have h₁ := edgeMultiplicity_le_one ef.1 z
    have h₂ := edgeMultiplicity_le_one ef.2 z
    omega
  have hfirst (e : Edge d) (he : 0 < edgeMultiplicity e z) : e.val.1 = z := by
    rcases (edgeMultiplicity_pos_iff e z).mp he with he | he
    · exact he
    · have hv : e.val.2.val = 0 := congrArg Fin.val he
      have ho : e.val.1.val < e.val.2.val := e.property
      omega
  have hsupport (e : Edge d) (he : e = ef.1 ∨ e = ef.2)
      (a : Fin d) (ha : 0 < edgeMultiplicity e a) :
      0 < weightMultiplicity (e₁, e₂) a := by
    rw [← h a]
    unfold weightMultiplicity
    rcases he with he | he <;> subst e <;> omega
  have hclass (e : Edge d) (he : e = ef.1 ∨ e = ef.2)
      (hzero : e.val.1 = z) : e = e₁ ∨ e = e₂ := by
    have hp := hsupport e he e.val.2
      ((edgeMultiplicity_pos_iff e e.val.2).mpr (Or.inr rfl))
    have hother : e.val.2 = z ∨ e.val.2 = o ∨ e.val.2 = t := by
      by_contra hn
      push_neg at hn
      rcases hn with ⟨hz', ho', ht'⟩
      change e.val.2 ≠ commonZero d hd at hz'
      change e.val.2 ≠ commonOne d hd at ho'
      change e.val.2 ≠ commonTwo d hd at ht'
      simp [e₁, e₂, firstCommonEdge, secondCommonEdge,
        weightMultiplicity, edgeMultiplicity, hz'.symm, ho'.symm, ht'.symm] at hp
    rcases hother with hother | hother | hother
    · have hne : e.val.2 ≠ z := by
        rw [← hzero]
        exact (ne_of_lt e.property).symm
      exact False.elim (hne hother)
    · exact Or.inl (Subtype.ext (Prod.ext hzero hother))
    · exact Or.inr (Subtype.ext (Prod.ext hzero hother))
  have he := hclass ef.1 (Or.inl rfl) (hfirst ef.1 hz₁)
  have hf := hclass ef.2 (Or.inr rfl) (hfirst ef.2 hz₂)
  rcases he with he | he <;> rcases hf with hf | hf
  · have hh := h o
    have heq : ef = (e₁, e₁) := Prod.ext he hf
    rw [heq] at hh
    norm_num [e₁, e₂, o, firstCommonEdge, secondCommonEdge,
      commonZero, commonOne, commonTwo, weightMultiplicity, edgeMultiplicity] at hh
  · exact Or.inl (Prod.ext he hf)
  · exact Or.inr (Prod.ext he hf)
  · have hh := h t
    have heq : ef = (e₂, e₂) := Prod.ext he hf
    rw [heq] at hh
    norm_num [e₁, e₂, t, firstCommonEdge, secondCommonEdge,
      commonZero, commonOne, commonTwo, weightMultiplicity, edgeMultiplicity] at hh

theorem exteriorSupportHaar_entry (d : ℕ) (ef gh : Edge d × Edge d) :
    exteriorSupportHaar d ef gh =
      ∫ U : PhysicalUnitary d, exteriorSupportOrbit U ef gh ∂normalizedHaar d := by
  let L : ((Edge d × Edge d) → (Edge d × Edge d) → ℂ) →L[ℂ] ℂ :=
    (ContinuousLinearMap.proj gh : ((Edge d × Edge d) → ℂ) →L[ℂ] ℂ).comp
      (ContinuousLinearMap.proj ef :
        ((Edge d × Edge d) → (Edge d × Edge d) → ℂ) →L[ℂ] ((Edge d × Edge d) → ℂ))
  exact (L.integral_comp_comm (exteriorSupportOrbit_function_integrable d)).symm

theorem replicaSwap_mul_entry_matrix {I : Type*} [Fintype I] [DecidableEq I]
    (M : Matrix (I × I) (I × I) ℂ) (ij kl : I × I) :
    (replicaSwap I * M) ij kl = M (ij.2, ij.1) kl := by
  simpa only [Matrix.mul_apply, Matrix.mulVec, dotProduct] using
    replicaSwap_mulVec (fun ab => M ab kl) ij

theorem mul_replicaSwap_entry_matrix {I : Type*} [Fintype I] [DecidableEq I]
    (M : Matrix (I × I) (I × I) ℂ) (ij kl : I × I) :
    (M * replicaSwap I) ij kl = M ij (kl.2, kl.1) := by
  have heq (ab : I × I) : kl = (ab.2, ab.1) ↔ ab = (kl.2, kl.1) := by
    simp [Prod.ext_iff, eq_comm, and_comm]
  simp [Matrix.mul_apply, replicaSwap, heq, mul_ite]

theorem literalExteriorSupportSum_left_skew (d : ℕ) :
    replicaSwap (Edge d) * literalExteriorSupportSum d = -literalExteriorSupportSum d := by
  ext ⟨e, f⟩ gh
  rw [replicaSwap_mul_entry_matrix]
  simp only [literalExteriorSupportSum, Matrix.sum_apply, Matrix.neg_apply]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro S _
  simp only [ExteriorSupport.orderedExterior]
  ring

theorem literalExteriorSupportSum_right_skew (d : ℕ) :
    literalExteriorSupportSum d * replicaSwap (Edge d) = -literalExteriorSupportSum d := by
  ext ef ⟨g, h⟩
  rw [mul_replicaSwap_entry_matrix]
  simp only [literalExteriorSupportSum, Matrix.sum_apply, Matrix.neg_apply]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro S _
  simp only [ExteriorSupport.orderedExterior]
  ring

theorem exteriorSupportOrbit_left_skew {d : ℕ} (U : PhysicalUnitary d) :
    replicaSwap (Edge d) * exteriorSupportOrbit U = -exteriorSupportOrbit U := by
  have hc : replicaSwap (Edge d) * wedgeSquareAction U =
      wedgeSquareAction U * replicaSwap (Edge d) :=
    (kronecker_replicaSwap_commutes (wedgeAction U)).symm
  calc
    _ = (replicaSwap (Edge d) * wedgeSquareAction U) *
        literalExteriorSupportSum d * (wedgeSquareAction U).conjTranspose := by
      simp only [exteriorSupportOrbit, Matrix.mul_assoc]
    _ = wedgeSquareAction U * (replicaSwap (Edge d) * literalExteriorSupportSum d) *
        (wedgeSquareAction U).conjTranspose := by rw [hc]; simp only [Matrix.mul_assoc]
    _ = _ := by rw [literalExteriorSupportSum_left_skew]; simp [exteriorSupportOrbit]

theorem exteriorSupportOrbit_right_skew {d : ℕ} (U : PhysicalUnitary d) :
    exteriorSupportOrbit U * replicaSwap (Edge d) = -exteriorSupportOrbit U := by
  have hc : (wedgeSquareAction U).conjTranspose * replicaSwap (Edge d) =
      replicaSwap (Edge d) * (wedgeSquareAction U).conjTranspose := by
    simpa only [wedgeSquareAction, Matrix.conjTranspose_kronecker] using
      kronecker_replicaSwap_commutes (wedgeAction U).conjTranspose
  calc
    _ = wedgeSquareAction U * literalExteriorSupportSum d *
        ((wedgeSquareAction U).conjTranspose * replicaSwap (Edge d)) := by
      simp only [exteriorSupportOrbit, Matrix.mul_assoc]
    _ = wedgeSquareAction U * (literalExteriorSupportSum d * replicaSwap (Edge d)) *
        (wedgeSquareAction U).conjTranspose := by rw [hc]; simp only [Matrix.mul_assoc]
    _ = _ := by rw [literalExteriorSupportSum_right_skew]; simp [exteriorSupportOrbit]

theorem exteriorSupportHaar_row_skew (d : ℕ) (e f : Edge d) (gh : Edge d × Edge d) :
    exteriorSupportHaar d (f, e) gh = -exteriorSupportHaar d (e, f) gh := by
  simp only [exteriorSupportHaar_entry]
  have hp (U : PhysicalUnitary d) : exteriorSupportOrbit U (f, e) gh =
      -exteriorSupportOrbit U (e, f) gh := by
    have h := congrArg (fun M : Matrix (Edge d × Edge d) (Edge d × Edge d) ℂ =>
      M (e, f) gh) (exteriorSupportOrbit_left_skew U)
    simpa only [replicaSwap_mul_entry_matrix, Matrix.neg_apply] using h
  simp_rw [hp]
  rw [integral_neg]

theorem exteriorSupportHaar_column_skew (d : ℕ) (ef : Edge d × Edge d) (g h : Edge d) :
    exteriorSupportHaar d ef (h, g) = -exteriorSupportHaar d ef (g, h) := by
  simp only [exteriorSupportHaar_entry]
  have hp (U : PhysicalUnitary d) : exteriorSupportOrbit U ef (h, g) =
      -exteriorSupportOrbit U ef (g, h) := by
    have hk := congrArg (fun M : Matrix (Edge d × Edge d) (Edge d × Edge d) ℂ =>
      M ef (g, h)) (exteriorSupportOrbit_right_skew U)
    simpa only [mul_replicaSwap_entry_matrix, Matrix.neg_apply] using hk
  simp_rw [hp]
  rw [integral_neg]

theorem commonEdges_ne (d : ℕ) (hd : 3 ≤ d) : firstCommonEdge d hd ≠ secondCommonEdge d hd := by
  intro h
  have hv := congrArg (fun e : Edge d => e.val.2.val) h
  norm_num [firstCommonEdge, secondCommonEdge, commonOne, commonTwo] at hv

theorem exteriorSupportHaar_first_common_column_zero (d : ℕ) (hd : 3 ≤ d)
    (ef : Edge d × Edge d)
    (hn : ef ≠ (firstCommonEdge d hd, secondCommonEdge d hd))
    (hs : ef ≠ (secondCommonEdge d hd, firstCommonEdge d hd)) :
    exteriorSupportHaar d ef (firstCommonEdge d hd, secondCommonEdge d hd) = 0 := by
  classical
  by_cases hw : ∀ a : Fin d, weightMultiplicity ef a =
      weightMultiplicity (firstCommonEdge d hd, secondCommonEdge d hd) a
  · exact False.elim ((weight_eq_first_common_rigid d hd ef hw).elim hn hs)
  · push_neg at hw
    obtain ⟨a, ha⟩ := hw
    exact exteriorSupportHaar_entry_eq_zero_of_weight a ef _ ha

theorem exteriorSupportHaar_first_common_eigenvector (d : ℕ) (hd : 3 ≤ d) :
    (exteriorSupportHaar d).mulVec
        (Pi.single (firstCommonEdge d hd, secondCommonEdge d hd) 1 -
          Pi.single (secondCommonEdge d hd, firstCommonEdge d hd) 1) =
      (2 * exteriorSupportHaar d (firstCommonEdge d hd, secondCommonEdge d hd)
        (firstCommonEdge d hd, secondCommonEdge d hd)) •
        (Pi.single (firstCommonEdge d hd, secondCommonEdge d hd) 1 -
          Pi.single (secondCommonEdge d hd, firstCommonEdge d hd) 1) := by
  classical
  let e := firstCommonEdge d hd
  let f := secondCommonEdge d hd
  have hef : e ≠ f := commonEdges_ne d hd
  ext ef
  simp only [Matrix.mulVec_sub, Matrix.mulVec_single_one, Matrix.col, Pi.sub_apply,
    Pi.smul_apply, smul_eq_mul]
  change exteriorSupportHaar d ef (e, f) - exteriorSupportHaar d ef (f, e) =
    (2 * exteriorSupportHaar d (e, f) (e, f)) *
      ((Pi.single (e, f) (1 : ℂ) : Edge d × Edge d → ℂ) ef -
        (Pi.single (f, e) (1 : ℂ) : Edge d × Edge d → ℂ) ef)
  rw [exteriorSupportHaar_column_skew d ef e f]
  by_cases hp : ef = (e, f)
  · subst ef
    simp [Pi.single_apply, hef, hef.symm]
    ring
  by_cases hs : ef = (f, e)
  · subst ef
    rw [exteriorSupportHaar_row_skew d e f (e, f)]
    simp [Pi.single_apply, hef, hef.symm]
    ring
  · have hz := exteriorSupportHaar_first_common_column_zero d hd ef hp hs
    change exteriorSupportHaar d ef (e, f) = 0 at hz
    rw [hz]
    simp [Pi.single_apply, hp, hs, Ne.symm hp, Ne.symm hs]

def exteriorHaarScalar (d : ℕ) (hd : 3 ≤ d) : ℂ :=
  2 * exteriorSupportHaar d (firstCommonEdge d hd, secondCommonEdge d hd)
    (firstCommonEdge d hd, secondCommonEdge d hd)

def exteriorHaarEigenspace (d : ℕ) (hd : 3 ≤ d) :
    Submodule ℂ (Edge d × Edge d → ℂ) :=
  Module.End.eigenspace (Matrix.mulVecLin (exteriorSupportHaar d)) (exteriorHaarScalar d hd)

theorem exteriorHaarEigenspace_mem (d : ℕ) (hd : 3 ≤ d) (v : Edge d × Edge d → ℂ) :
    v ∈ exteriorHaarEigenspace d hd ↔
      (exteriorSupportHaar d).mulVec v = exteriorHaarScalar d hd • v :=
  Module.End.mem_eigenspace_iff

theorem exteriorHaarEigenspace_first_common (d : ℕ) (hd : 3 ≤ d) :
    Pi.single (firstCommonEdge d hd, secondCommonEdge d hd) 1 -
      Pi.single (secondCommonEdge d hd, firstCommonEdge d hd) 1 ∈
        exteriorHaarEigenspace d hd :=
  (exteriorHaarEigenspace_mem d hd _).mpr (exteriorSupportHaar_first_common_eigenvector d hd)

theorem exteriorHaarEigenspace_rotated (d : ℕ) (hd : 3 ≤ d)
    (V : PhysicalUnitary d) (v : Edge d × Edge d → ℂ)
    (hv : v ∈ exteriorHaarEigenspace d hd) :
    (wedgeSquareAction V).mulVec v ∈ exteriorHaarEigenspace d hd := by
  rw [exteriorHaarEigenspace_mem] at hv ⊢
  rw [Matrix.mulVec_mulVec, ← exteriorSupportHaar_commutes, ← Matrix.mulVec_mulVec,
    hv, Matrix.mulVec_smul]

theorem orderedExterior_trace_matrix {I : Type*} [Fintype I] (P : Matrix I I ℂ) :
    Matrix.trace (ExteriorSupport.orderedExterior P) =
      ((Matrix.trace P) ^ 2 - Matrix.trace (P * P)) / 2 := by
  simp only [Matrix.trace, Matrix.diag, ExteriorSupport.orderedExterior,
    Fintype.sum_prod_type, Matrix.mul_apply]
  simp_rw [← Finset.sum_div, Finset.sum_sub_distrib]
  rw [ExteriorSupport.sum_separated_complex]
  ring

theorem literal_fourSupport_idempotent {d : ℕ} (S : FourSet d) :
    (RealSymmetricFactor.complexify (D5SupportFactor.fourSupportMatrix S)) *
        (RealSymmetricFactor.complexify (D5SupportFactor.fourSupportMatrix S)) =
      RealSymmetricFactor.complexify (D5SupportFactor.fourSupportMatrix S) := by
  rw [← RealSymmetricFactor.complexify_mul]
  congr 1
  simp_rw [D5NuclearControl.fourSupportMatrix_diagonal]
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext e
  by_cases h : ExteriorSupport.edgeVertices e ⊆ S.val <;> simp [h]

theorem literal_fourSupport_trace {d : ℕ} (S : FourSet d) :
    Matrix.trace (RealSymmetricFactor.complexify (D5SupportFactor.fourSupportMatrix S)) = 6 := by
  have ht (P : Matrix (Edge d) (Edge d) ℝ) :
      Matrix.trace (RealSymmetricFactor.complexify P) = ((Matrix.trace P : ℝ) : ℂ) := by
    simp [RealSymmetricFactor.complexify, Matrix.trace, Matrix.diag]
  rw [ht]
  norm_num [D5SupportFactor.fourSupportMatrix, Matrix.trace_add,
    Matrix.trace_single_eq_same]

theorem literal_exterior_fourSupport_trace {d : ℕ} (S : FourSet d) :
    Matrix.trace (ExteriorSupport.orderedExterior
      (RealSymmetricFactor.complexify (D5SupportFactor.fourSupportMatrix S))) = 15 := by
  rw [orderedExterior_trace_matrix, literal_fourSupport_idempotent, literal_fourSupport_trace]
  norm_num

theorem literalExteriorSupportSum_trace (d : ℕ) :
    Matrix.trace (literalExteriorSupportSum d) = 15 * (Fintype.card (FourSet d) : ℂ) := by
  rw [literalExteriorSupportSum, Matrix.trace_sum]
  simp only [literal_exterior_fourSupport_trace, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul]
  ring

theorem orderedExterior_identity_trace (d : ℕ) :
    Matrix.trace (ExteriorSupport.orderedExterior (1 : Matrix (Edge d) (Edge d) ℂ)) =
      ((Fintype.card (Edge d) : ℂ) ^ 2 - (Fintype.card (Edge d) : ℂ)) / 2 := by
  rw [orderedExterior_trace_matrix, Matrix.one_mul, Matrix.trace_one]

theorem exteriorSupportHaar_trace_ratio (d : ℕ) (hd : 4 ≤ d) :
    Matrix.trace (exteriorSupportHaar d) =
      (5 * ((d : ℂ) - 3) / ((d : ℂ) + 1)) *
        Matrix.trace (ExteriorSupport.orderedExterior (1 : Matrix (Edge d) (Edge d) ℂ)) := by
  rw [exteriorSupportHaar_trace, literalExteriorSupportSum_trace,
    fourSet_card_complex d (by omega), orderedExterior_identity_trace, edge_card_complex]
  have hn : (d : ℂ) + 1 ≠ 0 := by
    exact_mod_cast (by omega : d + 1 ≠ 0)
  field_simp
  ring

theorem orderedExterior_identity_eq (I : Type*) [Fintype I] [DecidableEq I] :
    ExteriorSupport.orderedExterior (1 : Matrix I I ℂ) =
      (1 / 2 : ℂ) • (1 - replicaSwap I) := by
  classical
  ext ⟨a, b⟩ ⟨c, f⟩
  by_cases hac : a = c <;> by_cases haf : a = f <;>
    by_cases hbc : b = c <;> by_cases hbf : b = f <;>
    simp_all [ExteriorSupport.orderedExterior, Matrix.one_apply, replicaSwap,
      Prod.mk.injEq, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul] <;> ring

theorem orderedExterior_identity_mulVec (I : Type*) [Fintype I] [DecidableEq I]
    (v : I × I → ℂ) (ij : I × I) :
    (ExteriorSupport.orderedExterior (1 : Matrix I I ℂ)).mulVec v ij =
      (v ij - v (ij.2, ij.1)) / 2 := by
  rw [orderedExterior_identity_eq, Matrix.smul_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec]
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, replicaSwap_mulVec]
  ring

theorem exteriorSupportHaar_right_projector (d : ℕ) :
    exteriorSupportHaar d * ExteriorSupport.orderedExterior (1 : Matrix (Edge d) (Edge d) ℂ) =
      exteriorSupportHaar d := by
  have hs : exteriorSupportHaar d * replicaSwap (Edge d) = -exteriorSupportHaar d := by
    ext ef ⟨g, h⟩
    rw [mul_replicaSwap_entry_matrix, Matrix.neg_apply]
    exact exteriorSupportHaar_column_skew d ef g h
  rw [orderedExterior_identity_eq, Matrix.mul_smul, Matrix.mul_sub, Matrix.mul_one, hs]
  ext ef gh
  simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.neg_apply, smul_eq_mul]
  ring

theorem exteriorSupportHaar_left_projector (d : ℕ) :
    ExteriorSupport.orderedExterior (1 : Matrix (Edge d) (Edge d) ℂ) * exteriorSupportHaar d =
      exteriorSupportHaar d := by
  have hs : replicaSwap (Edge d) * exteriorSupportHaar d = -exteriorSupportHaar d := by
    ext ⟨e, f⟩ gh
    rw [replicaSwap_mul_entry_matrix, Matrix.neg_apply]
    exact exteriorSupportHaar_row_skew d e f gh
  rw [orderedExterior_identity_eq, Matrix.smul_mul, Matrix.sub_mul, Matrix.one_mul, hs]
  ext ef gh
  simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.neg_apply, smul_eq_mul]
  ring

theorem exteriorSupportHaar_mulVec_skew (d : ℕ) (v : Edge d × Edge d → ℂ) (e f : Edge d) :
    (exteriorSupportHaar d).mulVec v (f, e) =
      -(exteriorSupportHaar d).mulVec v (e, f) := by
  simp only [Matrix.mulVec, dotProduct]
  simp_rw [exteriorSupportHaar_row_skew d e f]
  simp_rw [neg_mul]
  rw [Finset.sum_neg_distrib]

def supportTraceLinearMap {I O : Type*} [Fintype I] [Fintype O]
    (T : Matrix O I ℂ) : Matrix I I ℂ →ₗ[ℂ] ℂ where
  toFun P := Matrix.trace (T * P * T.conjTranspose)
  map_add' P Q := by
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.trace_add]
  map_smul' z P := by
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul, RingHom.id_apply]

def supportTraceCLM {I O : Type*} [Fintype I] [Fintype O]
    (T : Matrix O I ℂ) : (I → I → ℂ) →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap
    ((supportTraceLinearMap T).comp (Matrix.ofLinearEquiv ℂ).toLinearMap)

theorem supportTraceHaar_integral {d : ℕ} {O : Type*} [Fintype O]
    (T : Matrix O (Edge d × Edge d) ℂ) :
    (∫ U : PhysicalUnitary d, Matrix.trace (T * exteriorSupportOrbit U * T.conjTranspose)
      ∂normalizedHaar d) = Matrix.trace (T * exteriorSupportHaar d * T.conjTranspose) :=
  (supportTraceCLM T).integral_comp_comm (exteriorSupportOrbit_function_integrable d)

theorem supportTraceHaar_integrable {d : ℕ} {O : Type*} [Fintype O]
    (T : Matrix O (Edge d × Edge d) ℂ) :
    Integrable (fun U : PhysicalUnitary d =>
      Matrix.trace (T * exteriorSupportOrbit U * T.conjTranspose)) (normalizedHaar d) :=
  (supportTraceCLM T).integrable_comp (exteriorSupportOrbit_function_integrable d)

theorem supportTraceHaar_integral_re {d : ℕ} {O : Type*} [Fintype O]
    (T : Matrix O (Edge d × Edge d) ℂ) :
    (∫ U : PhysicalUnitary d,
      (Matrix.trace (T * exteriorSupportOrbit U * T.conjTranspose)).re ∂normalizedHaar d) =
      (Matrix.trace (T * exteriorSupportHaar d * T.conjTranspose)).re := by
  calc
    _ = (∫ U : PhysicalUnitary d,
        Matrix.trace (T * exteriorSupportOrbit U * T.conjTranspose) ∂normalizedHaar d).re :=
      Complex.reCLM.integral_comp_comm (supportTraceHaar_integrable T)
    _ = _ := congrArg Complex.re (supportTraceHaar_integral T)

theorem hsNormSq_mul_projection_matrix {I O : Type*} [Fintype I] [Fintype O]
    (T : Matrix O I ℂ) (P : Matrix I I ℂ) (hP : P.conjTranspose = P) (hid : P * P = P) :
    hsNormSq (T * P) = (Matrix.trace (T * P * T.conjTranspose)).re := by
  rw [hsNormSq_eq_trace, Matrix.conjTranspose_mul, hP]
  have hm : (T * P) * (P * T.conjTranspose) = T * P * T.conjTranspose := by
    calc
      _ = T * (P * P) * T.conjTranspose := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hid]
  exact congrArg (fun M => (Matrix.trace M).re) hm

end QuantumProver.WernerEndpoint.ExteriorHaar

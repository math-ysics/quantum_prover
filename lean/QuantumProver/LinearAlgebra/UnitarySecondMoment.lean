import QuantumProver.InformationTheory.WernerEndpoint.AllDimensionalMoment

set_option autoImplicit false

noncomputable section
open MeasureTheory Matrix TopologicalSpace
open scoped BigOperators Kronecker Matrix.Norms.Elementwise

namespace QuantumProver.UnitarySecondMoment

local instance matrixContinuousENorm {I J : Type*} [Fintype I] [Fintype J] :
    ContinuousENorm (Matrix I J ℂ) :=
  inferInstanceAs (ContinuousENorm (I → J → ℂ))

local instance matrixPseudoMetrizableSpace {I J : Type*} [Fintype I] [Fintype J] :
    PseudoMetrizableSpace (Matrix I J ℂ) :=
  inferInstanceAs (PseudoMetrizableSpace (I → J → ℂ))

local instance matrixSecondCountableTopology {I J : Type*} [Fintype I] [Fintype J] :
    SecondCountableTopology (Matrix I J ℂ) :=
  inferInstanceAs (SecondCountableTopology (I → J → ℂ))

abbrev CMat (d : ℕ) := Matrix (Fin d) (Fin d) ℂ
abbrev RepMat (d : ℕ) := Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ
abbrev UGroup (d : ℕ) := Matrix.unitaryGroup (Fin d) ℂ

abbrev unitaryHaar (d : ℕ) : Measure (UGroup d) :=
  QuantumProver.WernerEndpoint.SlaterMoments.normalizedHaar d

theorem unitaryHaar_univ (d : ℕ) : unitaryHaar d Set.univ = 1 :=
  QuantumProver.WernerEndpoint.SlaterMoments.normalizedHaar_univ d

instance unitaryHaar_rightInvariant (d : ℕ) : (unitaryHaar d).IsMulRightInvariant where
  map_mul_right_eq_self g := by
    letI : IsProbabilityMeasure (Measure.map (fun U : UGroup d => U * g) (unitaryHaar d)) :=
      ⟨by rw [Measure.map_apply (measurable_mul_const g) MeasurableSet.univ,
        Set.preimage_univ, unitaryHaar_univ]⟩
    exact Measure.isHaarMeasure_eq_of_isProbabilityMeasure
      (Measure.map (fun U : UGroup d => U * g) (unitaryHaar d)) (unitaryHaar d)

instance unitaryHaar_invInvariant (d : ℕ) : (unitaryHaar d).IsInvInvariant where
  inv_eq_self := by
    letI : (unitaryHaar d).inv.IsHaarMeasure := {
      toIsFiniteMeasureOnCompacts := inferInstance
      toIsMulLeftInvariant := inferInstance
      toIsOpenPosMeasure := inferInstance }
    letI : IsProbabilityMeasure (unitaryHaar d).inv := ⟨by simp⟩
    exact Measure.isHaarMeasure_eq_of_isProbabilityMeasure (unitaryHaar d).inv (unitaryHaar d)

theorem unitaryGroup_compact (d : ℕ) :
    IsCompact (Matrix.unitaryGroup (Fin d) ℂ : Set (CMat d)) :=
  QuantumProver.WernerEndpoint.SlaterMoments.unitary_isCompact d

def tensorUnitary {d : ℕ} (U : UGroup d) : RepMat d :=
  (U : CMat d) ⊗ₖ (U : CMat d)

theorem tensorUnitary_mem_unitary {d : ℕ} (U : UGroup d) :
    tensorUnitary U ∈ Matrix.unitaryGroup (Fin d × Fin d) ℂ :=
  Matrix.kronecker_mem_unitary U.property U.property

theorem tensorUnitary_mul {d : ℕ} (V U : UGroup d) :
    tensorUnitary (V * U) = tensorUnitary V * tensorUnitary U := by
  simp only [tensorUnitary, Matrix.UnitaryGroup.mul_val, Matrix.mul_kronecker_mul]

def tensorOrbit {d : ℕ} (X : RepMat d) (U : UGroup d) : RepMat d :=
  tensorUnitary U * X * (tensorUnitary U)ᴴ

theorem tensorOrbit_mul {d : ℕ} (X : RepMat d) (V U : UGroup d) :
    tensorOrbit X (V * U) =
      tensorUnitary V * tensorOrbit X U * (tensorUnitary V)ᴴ := by
  simp only [tensorOrbit, tensorUnitary_mul, Matrix.conjTranspose_mul,
    Matrix.mul_assoc]

theorem tensorUnitary_continuous (d : ℕ) :
    Continuous (fun U : UGroup d => tensorUnitary U) := by
  apply continuous_matrix
  intro ij kl
  exact (continuous_subtype_val.matrix_elem ij.1 kl.1).mul
    (continuous_subtype_val.matrix_elem ij.2 kl.2)

theorem tensorOrbit_continuous {d : ℕ} (X : RepMat d) :
    Continuous (tensorOrbit X) :=
  ((tensorUnitary_continuous d).matrix_mul continuous_const).matrix_mul
    (tensorUnitary_continuous d).matrix_conjTranspose

theorem tensorOrbit_integrable {d : ℕ} (X : RepMat d) :
    Integrable (tensorOrbit X) (unitaryHaar d) := by
  have hint := (tensorOrbit_continuous X).continuousOn.integrableOn_compact
    (μ := unitaryHaar d) isCompact_univ
  refine ⟨(tensorOrbit_continuous X).aestronglyMeasurable, ?_⟩
  simpa only [Measure.restrict_univ] using hint.2

theorem tensorOrbit_entry_integrable {d : ℕ} (X : RepMat d)
    (ij kl : Fin d × Fin d) :
    Integrable (fun U : UGroup d => tensorOrbit X U ij kl) (unitaryHaar d) := by
  simpa [MeasureTheory.IntegrableOn] using
    ((tensorOrbit_continuous X).matrix_elem ij kl).continuousOn.integrableOn_compact
      (μ := unitaryHaar d) isCompact_univ

def twirl {d : ℕ} (X : RepMat d) : RepMat d :=
  ∫ U : UGroup d, tensorOrbit X U ∂unitaryHaar d

theorem twirl_entry {d : ℕ} (X : RepMat d) (ij kl : Fin d × Fin d) :
    twirl X ij kl = ∫ U : UGroup d, tensorOrbit X U ij kl ∂unitaryHaar d := by
  let L : ((Fin d × Fin d) → (Fin d × Fin d) → ℂ) →L[ℂ] ℂ :=
    (ContinuousLinearMap.proj kl : ((Fin d × Fin d) → ℂ) →L[ℂ] ℂ).comp
      (ContinuousLinearMap.proj ij :
        ((Fin d × Fin d) → (Fin d × Fin d) → ℂ) →L[ℂ] ((Fin d × Fin d) → ℂ))
  exact (L.integral_comp_comm (tensorOrbit_integrable X)).symm

theorem twirl_covariance {d : ℕ} (X : RepMat d) (V : UGroup d) :
    tensorUnitary V * twirl X * (tensorUnitary V)ᴴ = twirl X := by
  have hi := (QuantumProver.WernerEndpoint.SlaterMoments.matrixSandwichCLM (tensorUnitary V)).integral_comp_comm
    (tensorOrbit_integrable X)
  have hi' : tensorUnitary V * twirl X * (tensorUnitary V)ᴴ =
      ∫ U : UGroup d,
        tensorUnitary V * tensorOrbit X U * (tensorUnitary V)ᴴ ∂unitaryHaar d := hi.symm
  simp_rw [← tensorOrbit_mul] at hi'
  exact hi'.trans (integral_mul_left_eq_self (μ := unitaryHaar d) (tensorOrbit X) V)

theorem twirl_commutes {d : ℕ} (X : RepMat d) (V : UGroup d) :
    tensorUnitary V * twirl X = twirl X * tensorUnitary V := by
  have hr : (tensorUnitary V)ᴴ * tensorUnitary V = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using (tensorUnitary_mem_unitary V).1
  have h := congrArg (fun A : RepMat d => A * tensorUnitary V) (twirl_covariance X V)
  simpa only [Matrix.mul_assoc, hr, Matrix.mul_one] using h

theorem tensorOrbit_trace {d : ℕ} (X : RepMat d) (U : UGroup d) :
    (tensorOrbit X U).trace = X.trace := by
  have hr : (tensorUnitary U)ᴴ * tensorUnitary U = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using (tensorUnitary_mem_unitary U).1
  rw [tensorOrbit, Matrix.trace_mul_cycle, hr, Matrix.one_mul]

theorem twirl_trace {d : ℕ} (X : RepMat d) : (twirl X).trace = X.trace := by
  simp only [Matrix.trace, Matrix.diag, twirl_entry]
  rw [← integral_finsetSum]
  · have ht : (fun U : UGroup d => ∑ ij, tensorOrbit X U ij ij) =
        fun _ => X.trace := by
      funext U
      exact tensorOrbit_trace X U
    rw [ht]
    simp [Matrix.trace, Matrix.diag]
  · intro ij _
    exact tensorOrbit_entry_integrable X ij ij

theorem twirl_zero_dimension (X : RepMat 0) : twirl X = X := by
  ext ij kl
  exact Fin.elim0 ij.1

theorem tensorOrbit_one_dimension (X : RepMat 1) (U : UGroup 1) :
    tensorOrbit X U = X := by
  have hc : tensorUnitary U * X = X * tensorUnitary U := by
    ext ⟨a, b⟩ ⟨c, e⟩
    fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases e
    simp [Matrix.mul_apply, Fintype.sum_prod_type, mul_comm]
  have hr : tensorUnitary U * (tensorUnitary U)ᴴ = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using (tensorUnitary_mem_unitary U).2
  rw [tensorOrbit, hc, Matrix.mul_assoc, hr, Matrix.mul_one]

theorem twirl_one_dimension (X : RepMat 1) : twirl X = X := by
  simp [twirl, tensorOrbit_one_dimension]

abbrev swap (d : ℕ) : RepMat d := QuantumProver.WernerEndpoint.replicaSwap (Fin d)

theorem tensorUnitary_swap_commutes {d : ℕ} (U : UGroup d) :
    tensorUnitary U * swap d = swap d * tensorUnitary U :=
  QuantumProver.WernerEndpoint.SlaterMoments.kronecker_replicaSwap_commutes (U : CMat d)

def CommutesTensor {d : ℕ} (M : RepMat d) : Prop :=
  ∀ U : UGroup d, tensorUnitary U * M = M * tensorUnitary U

theorem twirl_commutesTensor {d : ℕ} (X : RepMat d) : CommutesTensor (twirl X) :=
  twirl_commutes X

def pairMultiplicity {d : ℕ} (p : Fin d × Fin d) (a : Fin d) : ℕ :=
  (if p.1 = a then 1 else 0) + (if p.2 = a then 1 else 0)

theorem pairMultiplicity_le_two {d : ℕ} (p : Fin d × Fin d) (a : Fin d) :
    pairMultiplicity p a ≤ 2 := by
  by_cases h₁ : p.1 = a <;> by_cases h₂ : p.2 = a <;>
    simp [pairMultiplicity, h₁, h₂]

theorem pairMultiplicity_rigid {d : ℕ} (p q : Fin d × Fin d)
    (h : ∀ a, pairMultiplicity p a = pairMultiplicity q a) :
    p = q ∨ p = (q.2, q.1) := by
  rcases p with ⟨a, b⟩
  rcases q with ⟨c, e⟩
  have ha := h a
  have hb := h b
  have hc := h c
  have he := h e
  by_cases hac : a = c <;> by_cases hbe : b = e <;>
    by_cases hae : a = e <;> by_cases hbc : b = c <;>
    by_cases hab : a = b <;> by_cases hce : c = e <;>
    simp_all [pairMultiplicity, Prod.ext_iff, eq_comm] <;> omega

theorem coordinatePhase_pair_character {d : ℕ} (a : Fin d) (p : Fin d × Fin d) :
    QuantumProver.WernerEndpoint.SlaterMoments.coordinatePhase a p.1 *
      QuantumProver.WernerEndpoint.SlaterMoments.coordinatePhase a p.2 = Complex.I ^ pairMultiplicity p a := by
  rw [pairMultiplicity, pow_add]
  by_cases h₁ : p.1 = a <;> by_cases h₂ : p.2 = a <;>
    simp [QuantumProver.WernerEndpoint.SlaterMoments.coordinatePhase, h₁, h₂]

theorem commutant_phase_entry {d : ℕ} {M : RepMat d} (hM : CommutesTensor M)
    (z : Fin d → ℂ) (hz : ∀ a, star (z a) * z a = 1) (p q : Fin d × Fin d) :
    (z p.1 * z p.2) * M p q = M p q * (z q.1 * z q.2) := by
  have h := congrFun (congrFun (hM (QuantumProver.WernerEndpoint.SlaterMoments.physicalPhase z hz)) p) q
  simpa only [tensorUnitary, QuantumProver.WernerEndpoint.SlaterMoments.physicalPhase,
    Matrix.diagonal_kronecker_diagonal, Matrix.diagonal_mul, Matrix.mul_diagonal] using h

theorem commutant_entry_zero_of_weight {d : ℕ} {M : RepMat d}
    (hM : CommutesTensor M) (p q : Fin d × Fin d) (a : Fin d)
    (hw : pairMultiplicity p a ≠ pairMultiplicity q a) : M p q = 0 := by
  have hp : Complex.I ^ pairMultiplicity p a ≠ Complex.I ^ pairMultiplicity q a := by
    intro hh
    exact hw (QuantumProver.WernerEndpoint.SlaterMoments.I_pow_injective_le_two
      (pairMultiplicity_le_two p a) (pairMultiplicity_le_two q a) hh)
  have h := commutant_phase_entry hM (QuantumProver.WernerEndpoint.SlaterMoments.coordinatePhase a)
    (QuantumProver.WernerEndpoint.SlaterMoments.coordinatePhase_unitary a) p q
  rw [coordinatePhase_pair_character, coordinatePhase_pair_character] at h
  have hz : (Complex.I ^ pairMultiplicity p a - Complex.I ^ pairMultiplicity q a) *
      M p q = 0 := by
    linear_combination h
  exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hp)

theorem commutant_entry_zero {d : ℕ} {M : RepMat d} (hM : CommutesTensor M)
    (p q : Fin d × Fin d) (hp : p ≠ q) (hs : p ≠ (q.2, q.1)) : M p q = 0 := by
  have hw : ∃ a, pairMultiplicity p a ≠ pairMultiplicity q a := by
    by_contra hh
    push Not at hh
    rcases pairMultiplicity_rigid p q hh with h | h
    · exact hp h
    · exact hs h
  obtain ⟨a, ha⟩ := hw
  exact commutant_entry_zero_of_weight hM p q a ha

theorem tensorUnitary_permutation {d : ℕ} (σ : Equiv.Perm (Fin d)) :
    tensorUnitary (QuantumProver.WernerEndpoint.SlaterMoments.physicalPermutation σ) =
      Equiv.Perm.permMatrix ℂ (Equiv.prodCongr σ σ) := by
  ext p q
  by_cases h₁ : σ p.1 = q.1 <;> by_cases h₂ : σ p.2 = q.2 <;>
    simp_all [tensorUnitary, QuantumProver.WernerEndpoint.SlaterMoments.physicalPermutation,
      Equiv.Perm.permMatrix, PEquiv.toMatrix, Matrix.kroneckerMap_apply,
      Prod.ext_iff, eq_comm]

theorem commutant_permutation_entry {d : ℕ} {M : RepMat d}
    (hM : CommutesTensor M) (σ : Equiv.Perm (Fin d)) (p q : Fin d × Fin d) :
    M (σ p.1, σ p.2) (σ q.1, σ q.2) = M p q := by
  let ρ : Equiv.Perm (Fin d × Fin d) := Equiv.prodCongr σ σ
  have h := congrFun (congrFun (hM (QuantumProver.WernerEndpoint.SlaterMoments.physicalPermutation σ)) p) (ρ q)
  rw [tensorUnitary_permutation] at h
  have hl : (ρ.permMatrix ℂ * M) p (ρ q) = M (ρ p) (ρ q) :=
    congrFun (Matrix.permMatrix_mulVec ρ (v := fun r => M r (ρ q))) p
  have hr : (M * ρ.permMatrix ℂ) p (ρ q) = M p q := by
    simpa only [Matrix.mul_apply, Matrix.vecMul, dotProduct,
      Function.comp_apply, Equiv.symm_apply_apply] using
      congrFun (Matrix.vecMul_permMatrix ρ (v := M p)) (ρ q)
  exact hl.symm.trans (h.trans hr)

theorem commutant_square_diagonal_eq {d : ℕ} {M : RepMat d}
    (hM : CommutesTensor M) (a c : Fin d) : M (a, a) (a, a) = M (c, c) (c, c) := by
  have h := commutant_permutation_entry hM (Equiv.swap a c) (a, a) (a, a)
  simpa only [Equiv.swap_apply_left] using h.symm

theorem commutant_off_diagonal_eq {d : ℕ} {M : RepMat d}
    (hM : CommutesTensor M) (a b c e : Fin d) (hab : a ≠ b) (hce : c ≠ e) :
    M (a, b) (a, b) = M (c, e) (c, e) := by
  obtain ⟨σ, ha, hb⟩ := QuantumProver.WernerEndpoint.SlaterMoments.exists_physicalPermutation_pair a b c e hab hce
  have h := commutant_permutation_entry hM σ (a, b) (a, b)
  simpa only [ha, hb] using h.symm

theorem commutant_swap_entry_eq {d : ℕ} {M : RepMat d}
    (hM : CommutesTensor M) (a b c e : Fin d) (hab : a ≠ b) (hce : c ≠ e) :
    M (a, b) (b, a) = M (c, e) (e, c) := by
  obtain ⟨σ, ha, hb⟩ := QuantumProver.WernerEndpoint.SlaterMoments.exists_physicalPermutation_pair a b c e hab hce
  have h := commutant_permutation_entry hM σ (a, b) (b, a)
  simpa only [ha, hb] using h.symm

theorem commutant_square_eigenvector {d : ℕ} {M : RepMat d}
    (hM : CommutesTensor M) (a : Fin d) :
    M *ᵥ Pi.single (a, a) 1 = M (a, a) (a, a) • Pi.single (a, a) 1 := by
  rw [Matrix.mulVec_single_one]
  ext p
  by_cases hp : p = (a, a)
  · subst p
    simp
  · have hz := commutant_entry_zero hM p (a, a) hp hp
    simp [hp, hz, Pi.single_apply]

theorem tensorRotation_square {d : ℕ} (a b : Fin d) (hab : a ≠ b) :
    tensorUnitary (QuantumProver.WernerEndpoint.SlaterMoments.physicalPlaneRotation a b hab) *ᵥ
      Pi.single (a, a) 1 =
      (9 / 25 : ℂ) • Pi.single (a, a) 1 + (16 / 25 : ℂ) • Pi.single (b, b) 1 +
      (12 / 25 : ℂ) • Pi.single (a, b) 1 + (12 / 25 : ℂ) • Pi.single (b, a) 1 := by
  rw [Matrix.mulVec_single_one]
  ext p
  by_cases h₁ : p.1 = a <;> by_cases h₂ : p.1 = b <;>
    by_cases h₃ : p.2 = a <;> by_cases h₄ : p.2 = b <;>
    simp_all [tensorUnitary, Matrix.kroneckerMap_apply,
      QuantumProver.WernerEndpoint.SlaterMoments.physicalPlaneRotation, QuantumProver.WernerEndpoint.SlaterMoments.planeRotationMatrix,
      QuantumProver.WernerEndpoint.SlaterMoments.planeRotationColumn, Pi.single_apply, Prod.ext_iff,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul] <;> norm_num

theorem commutant_diagonal_relation {d : ℕ} {M : RepMat d}
    (hM : CommutesTensor M) (a b : Fin d) (hab : a ≠ b) :
    M (a, a) (a, a) = M (a, b) (a, b) + M (a, b) (b, a) := by
  let R := QuantumProver.WernerEndpoint.SlaterMoments.physicalPlaneRotation a b hab
  have hv : M *ᵥ (tensorUnitary R *ᵥ Pi.single (a, a) 1) =
      M (a, a) (a, a) • (tensorUnitary R *ᵥ Pi.single (a, a) 1) := by
    rw [Matrix.mulVec_mulVec, ← hM R, ← Matrix.mulVec_mulVec,
      commutant_square_eigenvector hM a, Matrix.mulVec_smul]
  have hAA : M (a, b) (a, a) = 0 := by
    apply commutant_entry_zero hM <;> simp [Prod.ext_iff, hab, Ne.symm hab]
  have hBB : M (a, b) (b, b) = 0 := by
    apply commutant_entry_zero hM <;> simp [Prod.ext_iff, hab, Ne.symm hab]
  dsimp only [R] at hv
  rw [tensorRotation_square] at hv
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul] at hv
  have h := congrFun hv (a, b)
  simp [Matrix.mulVec_single_one, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Pi.single_apply, Prod.ext_iff, hab, Ne.symm hab, hAA, hBB] at h
  linear_combination (-25 / 12 : ℂ) * h

theorem commutant_identity_swap {d : ℕ} {M : RepMat d} (hM : CommutesTensor M)
    (a b : Fin d) (hab : a ≠ b) :
    M = M (a, b) (a, b) • (1 : RepMat d) + M (a, b) (b, a) • swap d := by
  ext p q
  by_cases hp : p = q
  · subst q
    rcases p with ⟨i, j⟩
    by_cases hij : i = j
    · subst j
      have h := (commutant_square_diagonal_eq hM i a).trans
        (commutant_diagonal_relation hM a b hab)
      simpa [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply,
        swap, QuantumProver.WernerEndpoint.replicaSwap] using h
    · have h := commutant_off_diagonal_eq hM i j a b hij hab
      simpa [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply,
        swap, QuantumProver.WernerEndpoint.replicaSwap, Prod.ext_iff, hij] using h
  · by_cases hs : p = (q.2, q.1)
    · rcases q with ⟨k, l⟩
      subst p
      have hkl : k ≠ l := by
        intro hh
        subst l
        exact hp rfl
      have h := commutant_swap_entry_eq hM l k a b hkl.symm hab
      simpa [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply,
        swap, QuantumProver.WernerEndpoint.replicaSwap, Prod.ext_iff, hkl, Ne.symm hkl] using h
    · have h := commutant_entry_zero hM p q hp hs
      simpa [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply,
        swap, QuantumProver.WernerEndpoint.replicaSwap, hp, hs] using h

theorem swap_mul_swap (d : ℕ) : swap d * swap d = (1 : RepMat d) := by
  apply Matrix.ext_iff_mulVec.mpr
  intro w
  ext p
  simp only [← Matrix.mulVec_mulVec, swap, QuantumProver.WernerEndpoint.replicaSwap_mulVec,
    Matrix.one_mulVec]

theorem swap_trace (d : ℕ) : (swap d).trace = (d : ℂ) := by
  simp only [swap, QuantumProver.WernerEndpoint.replicaSwap, Matrix.trace, Matrix.diag,
    Fintype.sum_prod_type]
  simp [Prod.ext_iff, eq_comm]

theorem replica_identity_trace (d : ℕ) : (1 : RepMat d).trace = (d : ℂ) ^ 2 := by
  simp [Matrix.trace_one, Fintype.card_prod, pow_two, Nat.cast_mul]

theorem tensorOrbit_swap_trace {d : ℕ} (X : RepMat d) (U : UGroup d) :
    (swap d * tensorOrbit X U).trace = (swap d * X).trace := by
  have hr : (tensorUnitary U)ᴴ * tensorUnitary U = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using (tensorUnitary_mem_unitary U).1
  rw [tensorOrbit, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.trace_mul_cycle,
    ← tensorUnitary_swap_commutes U, ← Matrix.mul_assoc, hr, Matrix.one_mul]

def traceLeftCLM {d : ℕ} (C : RepMat d) :
    ((Fin d × Fin d) → (Fin d × Fin d) → ℂ) →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap
    ((Matrix.traceLinearMap (Fin d × Fin d) ℂ ℂ).comp
      (mulLeftLinearMap (Fin d × Fin d) ℂ C))

theorem traceLeftCLM_apply {d : ℕ} (C X : RepMat d) :
    traceLeftCLM C X = (C * X).trace := rfl

theorem twirl_swap_trace {d : ℕ} (X : RepMat d) :
    (swap d * twirl X).trace = (swap d * X).trace := by
  have hi := (traceLeftCLM (swap d)).integral_comp_comm (tensorOrbit_integrable X)
  have hi' : (swap d * twirl X).trace =
      ∫ U : UGroup d, (swap d * tensorOrbit X U).trace ∂unitaryHaar d := hi.symm
  simp only [tensorOrbit_swap_trace] at hi'
  simpa using hi'

theorem twirl_eq_identity_swap {d : ℕ} (hd : 2 ≤ d) (X : RepMat d) :
    twirl X =
      ((X.trace - (swap d * X).trace / (d : ℂ)) / ((d : ℂ) ^ 2 - 1)) •
        (1 : RepMat d) +
      (((swap d * X).trace - X.trace / (d : ℂ)) / ((d : ℂ) ^ 2 - 1)) • swap d := by
  let a : Fin d := ⟨0, by omega⟩
  let b : Fin d := ⟨1, by omega⟩
  have hab : a ≠ b := by
    intro hh
    have hv := congrArg Fin.val hh
    norm_num [a, b] at hv
  let α := twirl X (a, b) (a, b)
  let β := twirl X (a, b) (b, a)
  have hm : twirl X = α • (1 : RepMat d) + β • swap d :=
    commutant_identity_swap (twirl_commutesTensor X) a b hab
  have ht : (d : ℂ) ^ 2 * α + (d : ℂ) * β = X.trace := by
    have hh := congrArg Matrix.trace hm
    rw [twirl_trace, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul,
      replica_identity_trace, swap_trace] at hh
    simpa [smul_eq_mul, mul_comm] using hh.symm
  have hs : (d : ℂ) * α + (d : ℂ) ^ 2 * β = (swap d * X).trace := by
    have hh := congrArg (fun A : RepMat d => (swap d * A).trace) hm
    rw [twirl_swap_trace, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul,
      Matrix.mul_one, swap_mul_swap, Matrix.trace_add, Matrix.trace_smul,
      Matrix.trace_smul, swap_trace, replica_identity_trace] at hh
    simpa [smul_eq_mul, mul_comm] using hh.symm
  have hn : (d : ℂ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
  have hden : (d : ℂ) ^ 2 - 1 ≠ 0 := by
    apply sub_ne_zero.mpr
    exact_mod_cast (by nlinarith : d ^ 2 ≠ 1)
  have hα : α = (X.trace - (swap d * X).trace / (d : ℂ)) / ((d : ℂ) ^ 2 - 1) := by
    field_simp [hn, hden]
    linear_combination (d : ℂ) * ht - hs
  have hβ : β = ((swap d * X).trace - X.trace / (d : ℂ)) / ((d : ℂ) ^ 2 - 1) := by
    field_simp [hn, hden]
    linear_combination (d : ℂ) * hs - ht
  rw [hm, hα, hβ]

theorem tensorUnitary_inv {d : ℕ} (U : UGroup d) :
    tensorUnitary U⁻¹ = (tensorUnitary U)ᴴ := by
  simp only [tensorUnitary, Matrix.UnitaryGroup.inv_val,
    Matrix.star_eq_conjTranspose, Matrix.conjTranspose_kronecker]

theorem twirl_inverse_integral {d : ℕ} (X : RepMat d) :
    (∫ U : UGroup d, (tensorUnitary U)ᴴ * X * tensorUnitary U ∂unitaryHaar d) =
      twirl X := by
  have h := integral_inv_eq_self (tensorOrbit X) (unitaryHaar d)
  simpa only [tensorOrbit, tensorUnitary_inv, Matrix.conjTranspose_conjTranspose,
    twirl] using h

def twirlFormula {d : ℕ} (X : RepMat d) : RepMat d :=
  if d = 0 then X else if d = 1 then X else
    ((X.trace - (swap d * X).trace / (d : ℂ)) / ((d : ℂ) ^ 2 - 1)) •
      (1 : RepMat d) +
    (((swap d * X).trace - X.trace / (d : ℂ)) / ((d : ℂ) ^ 2 - 1)) • swap d

theorem twirl_eq_formula {d : ℕ} (X : RepMat d) : twirl X = twirlFormula X := by
  by_cases hd₀ : d = 0
  · subst d
    simpa [twirlFormula] using twirl_zero_dimension X
  by_cases hd₁ : d = 1
  · subst d
    simpa [twirlFormula] using twirl_one_dimension X
  simpa [twirlFormula, hd₀, hd₁] using twirl_eq_identity_swap (by omega : 2 ≤ d) X

theorem twirl_inverse_eq_formula {d : ℕ} (X : RepMat d) :
    (∫ U : UGroup d, (tensorUnitary U)ᴴ * X * tensorUnitary U ∂unitaryHaar d) =
      twirlFormula X :=
  (twirl_inverse_integral X).trans (twirl_eq_formula X)

end QuantumProver.UnitarySecondMoment

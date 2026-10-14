import QuantumProver.InformationTheory.AmplitudeDamping.QuantumCapacity.Definitions
import QuantumProver.InformationTheory.AmplitudeDamping.SecretKey.Definitions
import QuantumProver.InformationTheory.AmplitudeDamping.QuantumCapacity.LaneLimitBounds
import QuantumProver.InformationTheory.AmplitudeDamping.QuantumCapacity.ProtocolIdentities
import QuantumProver.LinearAlgebra.MatrixTracePower.Order
import QuantumProver.LinearAlgebra.SandwichedDPI.Support
import QuantumProver.InformationTheory.SuperchannelDiscrimination.Pinching

set_option autoImplicit false

noncomputable section

open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder Matrix Kronecker

namespace QuantumProver.AmplitudeDamping.FiniteModel

theorem dampingKraus_eq_key (p : ℝ) (z : Qubit) :
    dampingKraus p z = QuantumProver.AmplitudeDamping.SecretKey.amplitudeDampingKraus p z := by
  fin_cases z <;> rfl

theorem dampingKraus_complete {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ∑ z : Qubit, (dampingKraus p z)ᴴ * dampingKraus p z = 1 := by
  simp_rw [dampingKraus_eq_key]
  exact QuantumProver.AmplitudeDamping.SecretKey.amplitudeDamping_complete hp0 hp1

theorem dampingOutput_eq_sum (p : ℝ) (ρ : Matrix Qubit Qubit ℂ) :
    dampingOutput p ρ = ∑ z : Qubit, dampingKraus p z * ρ *
      (dampingKraus p z)ᴴ := by
  simp [dampingOutput, dampingKraus, Fin.sum_univ_two]

theorem dampingOutput_posSemidef (p : ℝ) {ρ : Matrix Qubit Qubit ℂ}
    (hρ : ρ.PosSemidef) : (dampingOutput p ρ).PosSemidef := by
  exact (hρ.mul_mul_conjTranspose_same (dampingNoLoss p)).add
    (hρ.mul_mul_conjTranspose_same (dampingLoss p))

theorem dampingOutput_trace {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (ρ : Matrix Qubit Qubit ℂ) : (dampingOutput p ρ).trace = ρ.trace := by
  rw [dampingOutput_eq_sum]
  calc
    (∑ z : Qubit, dampingKraus p z * ρ * (dampingKraus p z)ᴴ).trace =
        ∑ z : Qubit, ((dampingKraus p z)ᴴ * dampingKraus p z * ρ).trace := by
      rw [Matrix.trace_sum]
      apply Finset.sum_congr rfl
      intro z _
      exact Matrix.trace_mul_cycle _ _ _
    _ = ((∑ z : Qubit, (dampingKraus p z)ᴴ * dampingKraus p z) * ρ).trace := by
      rw [Matrix.sum_mul, Matrix.trace_sum]
    _ = ρ.trace := by rw [dampingKraus_complete hp0 hp1, Matrix.one_mul]

theorem dampingOutput_isDensity {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {ρ : Matrix Qubit Qubit ℂ} (hρ : IsDensity ρ) :
    IsDensity (dampingOutput p ρ) :=
  ⟨dampingOutput_posSemidef p hρ.1, (dampingOutput_trace hp0 hp1 ρ).trans hρ.2⟩

theorem aliceOperator_gram {a ao b k : ℕ} (K : KrausInstrument a ao k) :
    ∑ z, (aliceOperator (b := b) (K.operator z))ᴴ *
      aliceOperator (b := b) (K.operator z) = 1 := by
  simp only [aliceOperator, Matrix.conjTranspose_kronecker,
    Matrix.conjTranspose_one, ← Matrix.mul_kronecker_mul, Matrix.one_mul]
  have hs : (∑ z, ((K.operator z)ᴴ * K.operator z) ⊗ₖ
      (1 : Matrix (Fin b) (Fin b) ℂ)) =
      (∑ z, (K.operator z)ᴴ * K.operator z) ⊗ₖ
        (1 : Matrix (Fin b) (Fin b) ℂ) := by
    ext x y
    simp only [Matrix.sum_apply, Matrix.kroneckerMap_apply, Finset.sum_mul]
  rw [hs, K.complete, Matrix.one_kronecker_one]

theorem bobOperator_gram {a b bo k : ℕ} (K : KrausInstrument b bo k) :
    ∑ z, (bobOperator (a := a) (K.operator z))ᴴ *
      bobOperator (a := a) (K.operator z) = 1 := by
  simp only [bobOperator, Matrix.conjTranspose_kronecker,
    Matrix.conjTranspose_one, ← Matrix.mul_kronecker_mul, Matrix.one_mul]
  have hs : (∑ z, (1 : Matrix (Fin a) (Fin a) ℂ) ⊗ₖ
      ((K.operator z)ᴴ * K.operator z)) =
      (1 : Matrix (Fin a) (Fin a) ℂ) ⊗ₖ
        (∑ z, (K.operator z)ᴴ * K.operator z) := by
    ext x y
    simp only [Matrix.sum_apply, Matrix.kroneckerMap_apply, Finset.mul_sum]
  rw [hs, K.complete, Matrix.one_kronecker_one]

theorem callOperator_eq_reindex (p : ℝ) (a b : ℕ) (z : Qubit) :
    callOperator p a b z =
      ((1 : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) ⊗ₖ dampingKraus p z).submatrix
        (callOutputEquiv a b) (callInputEquiv a b) := by
  ext x y
  simp [callOperator, callOutputEquiv, callInputEquiv, Matrix.kroneckerMap_apply,
    Matrix.one_apply, Prod.mk.injEq, mul_comm]

theorem callOperator_gram {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (a b : ℕ) :
    ∑ z : Qubit, (callOperator p a b z)ᴴ * callOperator p a b z = 1 := by
  have hg : (∑ z : Qubit,
      ((1 : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) ⊗ₖ dampingKraus p z)ᴴ *
        ((1 : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) ⊗ₖ dampingKraus p z)) = 1 := by
    simp only [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
      ← Matrix.mul_kronecker_mul, Matrix.one_mul]
    have hs : (∑ z : Qubit,
        (1 : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) ⊗ₖ
          ((dampingKraus p z)ᴴ * dampingKraus p z)) =
        (1 : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) ⊗ₖ
          (∑ z : Qubit, (dampingKraus p z)ᴴ * dampingKraus p z) := by
      ext x y
      simp only [Matrix.sum_apply, Matrix.kroneckerMap_apply, Finset.mul_sum]
    rw [hs, dampingKraus_complete hp0 hp1, Matrix.one_kronecker_one]
  simp only [callOperator_eq_reindex, Matrix.conjTranspose_submatrix,
    Matrix.submatrix_mul_equiv]
  have hs : (∑ z : Qubit,
      (((1 : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) ⊗ₖ dampingKraus p z)ᴴ *
        ((1 : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) ⊗ₖ dampingKraus p z)).submatrix
          (callInputEquiv a b) (callInputEquiv a b)) =
      (∑ z : Qubit,
        ((1 : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) ⊗ₖ dampingKraus p z)ᴴ *
          ((1 : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) ⊗ₖ dampingKraus p z)).submatrix
            (callInputEquiv a b) (callInputEquiv a b) := by
    ext x y
    simp
  rw [hs, hg, Matrix.submatrix_one_equiv]

theorem krausSum_trace {I O Z : Type*} [Fintype I] [Fintype O] [Fintype Z]
    [DecidableEq I] (K : Z → Matrix O I ℂ) (hK : ∑ z, (K z)ᴴ * K z = 1)
    (ρ : Matrix I I ℂ) : (∑ z, K z * ρ * (K z)ᴴ).trace = ρ.trace := by
  calc
    (∑ z, K z * ρ * (K z)ᴴ).trace = ∑ z, ((K z)ᴴ * K z * ρ).trace := by
      rw [Matrix.trace_sum]
      apply Finset.sum_congr rfl
      intro z _
      exact Matrix.trace_mul_cycle _ _ _
    _ = ((∑ z, (K z)ᴴ * K z) * ρ).trace := by
      rw [Matrix.sum_mul, Matrix.trace_sum]
    _ = ρ.trace := by rw [hK, Matrix.one_mul]

theorem FiniteProtocol.output_trace {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {a b af bf : ℕ} (P : FiniteProtocol p a b af bf) :
    ∀ ρ : BipartiteMatrix a b, (P.output ρ).trace = ρ.trace := by
  induction P with
  | done a b =>
      intro ρ
      rfl
  | @alice a b ao af bf k K next ih =>
      intro ρ
      simp only [FiniteProtocol.output, Matrix.trace_sum]
      calc
        (∑ z, ((next z).output
          (aliceOperator (b := b) (K.operator z) * ρ *
            (aliceOperator (b := b) (K.operator z))ᴴ)).trace) =
            ∑ z, (aliceOperator (b := b) (K.operator z) * ρ *
              (aliceOperator (b := b) (K.operator z))ᴴ).trace := by
          apply Finset.sum_congr rfl
          intro z _
          exact ih z _
        _ = ρ.trace := by
          simpa only [Matrix.trace_sum] using
            krausSum_trace _ (aliceOperator_gram (b := b) K) ρ
  | @bob a b bo af bf k K next ih =>
      intro ρ
      simp only [FiniteProtocol.output, Matrix.trace_sum]
      calc
        (∑ z, ((next z).output
          (bobOperator (a := a) (K.operator z) * ρ *
            (bobOperator (a := a) (K.operator z))ᴴ)).trace) =
            ∑ z, (bobOperator (a := a) (K.operator z) * ρ *
              (bobOperator (a := a) (K.operator z))ᴴ).trace := by
          apply Finset.sum_congr rfl
          intro z _
          exact ih z _
        _ = ρ.trace := by
          simpa only [Matrix.trace_sum] using
            krausSum_trace _ (bobOperator_gram (a := a) K) ρ
  | call next ih =>
      intro ρ
      rw [FiniteProtocol.output, ih]
      exact krausSum_trace _ (callOperator_gram hp0 hp1 _ _) ρ

theorem FiniteProtocol.output_posSemidef {p : ℝ} {a b af bf : ℕ}
    (P : FiniteProtocol p a b af bf) :
    ∀ ρ : BipartiteMatrix a b, ρ.PosSemidef → (P.output ρ).PosSemidef := by
  induction P with
  | done a b =>
      intro ρ hρ
      exact hρ
  | alice K next ih =>
      intro ρ hρ
      apply Matrix.posSemidef_sum
      intro z _
      exact ih z _ (hρ.mul_mul_conjTranspose_same (aliceOperator (K.operator z)))
  | bob K next ih =>
      intro ρ hρ
      apply Matrix.posSemidef_sum
      intro z _
      exact ih z _ (hρ.mul_mul_conjTranspose_same (bobOperator (K.operator z)))
  | call next ih =>
      intro ρ hρ
      apply ih
      apply Matrix.posSemidef_sum
      intro z _
      exact hρ.mul_mul_conjTranspose_same (callOperator p _ _ z)

theorem FiniteProtocol.output_isDensity {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {a b af bf : ℕ} (P : FiniteProtocol p a b af bf)
    {ρ : BipartiteMatrix a b} (hρ : IsDensity ρ) : IsDensity (P.output ρ) :=
  ⟨P.output_posSemidef ρ hρ.1, (P.output_trace hp0 hp1 ρ).trans hρ.2⟩

theorem FiniteProtocol.output_add {p : ℝ} {a b af bf : ℕ}
    (P : FiniteProtocol p a b af bf) :
    ∀ ρ σ : BipartiteMatrix a b, P.output (ρ + σ) = P.output ρ + P.output σ := by
  induction P with
  | done a b => intro ρ σ; rfl
  | alice K next ih =>
      intro ρ σ
      simp only [FiniteProtocol.output, Matrix.mul_add, Matrix.add_mul,
        ih, Finset.sum_add_distrib]
  | bob K next ih =>
      intro ρ σ
      simp only [FiniteProtocol.output, Matrix.mul_add, Matrix.add_mul,
        ih, Finset.sum_add_distrib]
  | call next ih =>
      intro ρ σ
      simp only [FiniteProtocol.output, Matrix.mul_add, Matrix.add_mul,
        Finset.sum_add_distrib, ih]

theorem FiniteProtocol.output_smul {p : ℝ} {a b af bf : ℕ}
    (P : FiniteProtocol p a b af bf) :
    ∀ (c : ℂ) (ρ : BipartiteMatrix a b), P.output (c • ρ) = c • P.output ρ := by
  induction P with
  | done a b => intro c ρ; rfl
  | alice K next ih =>
      intro c ρ
      simp only [FiniteProtocol.output, Matrix.mul_smul, Matrix.smul_mul,
        ih, Finset.smul_sum]
  | bob K next ih =>
      intro c ρ
      simp only [FiniteProtocol.output, Matrix.mul_smul, Matrix.smul_mul,
        ih, Finset.smul_sum]
  | call next ih =>
      intro c ρ
      simp only [FiniteProtocol.output, Matrix.mul_smul, Matrix.smul_mul,
        ← Finset.smul_sum, ih]

def FiniteProtocol.outputLinearMap {p : ℝ} {a b af bf : ℕ}
    (P : FiniteProtocol p a b af bf) : BipartiteMatrix a b →ₗ[ℂ] BipartiteMatrix af bf where
  toFun := P.output
  map_add' := P.output_add
  map_smul' c ρ := by simpa only [RingHom.id_apply] using P.output_smul c ρ

@[simp] theorem done_output (p : ℝ) (a b : ℕ) (ρ : BipartiteMatrix a b) :
    (FiniteProtocol.done (p := p) a b).output ρ = ρ := rfl

@[simp] theorem done_calls (p : ℝ) (a b : ℕ) :
    (FiniteProtocol.done (p := p) a b).calls = 0 := rfl

theorem bellProjector_eq_vecMulVec (d : ℕ) :
    bellProjector d = Matrix.vecMulVec (bellVector d) (star (bellVector d)) := by
  have hs : (Real.sqrt (d : ℝ) : ℂ) * (Real.sqrt (d : ℝ) : ℂ) = (d : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg d)]
    simp
  have hi : (d : ℂ)⁻¹ = (Real.sqrt (d : ℝ) : ℂ)⁻¹ * (Real.sqrt (d : ℝ) : ℂ)⁻¹ := by
    rw [← hs, mul_inv_rev]
  ext x y
  by_cases hx : x.1 = x.2 <;> by_cases hy : y.1 = y.2 <;>
    simp [bellProjector, bellVector, Matrix.vecMulVec_apply, hx, hy,
      hi]

theorem bellProjector_posSemidef (d : ℕ) : (bellProjector d).PosSemidef := by
  rw [bellProjector_eq_vecMulVec]
  exact Matrix.posSemidef_vecMulVec_self_star _

theorem bellProjector_trace {d : ℕ} (hd : 0 < d) : (bellProjector d).trace = 1 := by
  have hdz : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
  simp [bellProjector, Matrix.trace, Fintype.sum_prod_type, hdz]

theorem bellProjector_isDensity {d : ℕ} (hd : 0 < d) : IsDensity (bellProjector d) :=
  ⟨bellProjector_posSemidef d, bellProjector_trace hd⟩

theorem complexSum_mul_normSq_le {I : Type*} [Fintype I] (u v : I → ℂ) :
    Complex.normSq (∑ i, u i * v i) ≤
      (∑ i, Complex.normSq (u i)) * ∑ i, Complex.normSq (v i) := by
  have ht : ‖∑ i, u i * v i‖ ≤ ∑ i, ‖u i‖ * ‖v i‖ := by
    simpa only [norm_mul] using norm_sum_le Finset.univ (fun i => u i * v i)
  have hc := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun i => ‖u i‖) (fun i => ‖v i‖)
  simp only [Complex.normSq_eq_norm_sq]
  have hn : 0 ≤ ∑ i, ‖u i‖ * ‖v i‖ := by positivity
  nlinarith [norm_nonneg (∑ i, u i * v i)]

theorem bellOverlap_vecMulVec (d : ℕ) (v : Fin d × Fin d → ℂ) :
    bellOverlap d (Matrix.vecMulVec v (star v)) =
      Complex.normSq (∑ i : Fin d, v (i, i)) / (d : ℝ) := by
  have ht : (bellProjector d * Matrix.vecMulVec v (star v)).trace =
      ((1 / (d : ℝ) : ℝ) : ℂ) *
        star (∑ i : Fin d, v (i, i)) * (∑ i : Fin d, v (i, i)) := by
    simp [bellProjector, Matrix.trace, Matrix.mul_apply, Matrix.vecMulVec_apply,
      Fintype.sum_prod_type, Finset.mul_sum, Finset.sum_mul, ite_and,
      mul_assoc, mul_comm, mul_left_comm]
  rw [bellOverlap, ht]
  simp [Complex.mul_re, Complex.mul_im, Complex.normSq_apply, pow_two]
  ring

theorem bellOverlap_pure_product_le {d : ℕ} (u v : Fin d → ℂ) :
    bellOverlap d (Matrix.vecMulVec (fun x : Fin d × Fin d => u x.1 * v x.2)
      (star (fun x : Fin d × Fin d => u x.1 * v x.2))) ≤
        ((∑ i, Complex.normSq (u i)) * ∑ i, Complex.normSq (v i)) / (d : ℝ) := by
  rw [bellOverlap_vecMulVec]
  exact div_le_div_of_nonneg_right (complexSum_mul_normSq_le u v) (Nat.cast_nonneg d)

theorem bellOverlap_sum {Z : Type*} [Fintype Z] (d : ℕ)
    (ρ : Z → BipartiteMatrix d d) : bellOverlap d (∑ z, ρ z) = ∑ z, bellOverlap d (ρ z) := by
  simp [bellOverlap, Matrix.mul_sum, Matrix.trace_sum]

theorem bellOverlap_real_smul (d : ℕ) (t : ℝ) (ρ : BipartiteMatrix d d) :
    bellOverlap d ((t : ℂ) • ρ) = t * bellOverlap d ρ := by
  simp [bellOverlap, Matrix.mul_smul, Matrix.trace_smul, Complex.mul_re]

theorem trace_vecMulVec_re {I : Type*} [Fintype I] (v : I → ℂ) :
    (Matrix.vecMulVec v (star v)).trace.re = ∑ i, Complex.normSq (v i) := by
  simp [Matrix.trace, Matrix.vecMulVec_apply, Complex.mul_re, Complex.normSq_apply, pow_two]

theorem pure_product_matrix_eq (d : ℕ) (u v : Fin d → ℂ) :
    Matrix.vecMulVec u (star u) ⊗ₖ Matrix.vecMulVec v (star v) =
      Matrix.vecMulVec (fun x : Fin d × Fin d => u x.1 * v x.2)
        (star (fun x : Fin d × Fin d => u x.1 * v x.2)) := by
  ext x y
  simp [Matrix.kroneckerMap_apply, Matrix.vecMulVec_apply, mul_assoc, mul_comm, mul_left_comm]

theorem bellOverlap_product_density_le {d : ℕ}
    {A B : Matrix (Fin d) (Fin d) ℂ} (hA : IsDensity A) (hB : IsDensity B) :
    bellOverlap d (A ⊗ₖ B) ≤ 1 / (d : ℝ) := by
  obtain ⟨m, u, hu⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp hA.1
  obtain ⟨n, v, hv⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp hB.1
  have hnu : (∑ i : Fin m, ∑ k : Fin d, Complex.normSq (u i k)) = 1 := by
    have hh := congrArg Complex.re hA.2
    rw [hu, Matrix.trace_sum, Complex.re_sum] at hh
    simpa only [trace_vecMulVec_re, Complex.one_re] using hh
  have hnv : (∑ j : Fin n, ∑ k : Fin d, Complex.normSq (v j k)) = 1 := by
    have hh := congrArg Complex.re hB.2
    rw [hv, Matrix.trace_sum, Complex.re_sum] at hh
    simpa only [trace_vecMulVec_re, Complex.one_re] using hh
  have hp : A ⊗ₖ B = ∑ i : Fin m, ∑ j : Fin n,
      Matrix.vecMulVec (fun x : Fin d × Fin d => u i x.1 * v j x.2)
        (star (fun x : Fin d × Fin d => u i x.1 * v j x.2)) := by
    rw [hu, hv]
    ext x y
    simp [Matrix.sum_apply, Matrix.kroneckerMap_apply, Matrix.vecMulVec_apply,
      Finset.mul_sum, Finset.sum_mul, mul_assoc, mul_comm, mul_left_comm]
    exact Finset.sum_comm
  rw [hp, bellOverlap_sum]
  simp_rw [bellOverlap_sum]
  calc
    (∑ i : Fin m, ∑ j : Fin n, bellOverlap d
      (Matrix.vecMulVec (fun x : Fin d × Fin d => u i x.1 * v j x.2)
        (star (fun x : Fin d × Fin d => u i x.1 * v j x.2)))) ≤
        ∑ i : Fin m, ∑ j : Fin n,
          ((∑ k, Complex.normSq (u i k)) * ∑ k, Complex.normSq (v j k)) / (d : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      exact bellOverlap_pure_product_le (u i) (v j)
    _ = 1 / (d : ℝ) := by
      simp only [← Finset.sum_div, ← Finset.mul_sum, ← Finset.sum_mul, hnu, hnv, one_mul]

theorem bellOverlap_separable_le {d : ℕ} {ρ : BipartiteMatrix d d}
    (hρ : IsSeparable d d ρ) : bellOverlap d ρ ≤ 1 / (d : ℝ) := by
  obtain ⟨k, t, A, B, ht, hsum, hden, rfl⟩ := hρ
  rw [bellOverlap_sum]
  simp_rw [bellOverlap_real_smul]
  calc
    (∑ z, t z * bellOverlap d (A z ⊗ₖ B z)) ≤ ∑ z, t z * (1 / (d : ℝ)) := by
      apply Finset.sum_le_sum
      intro z _
      exact mul_le_mul_of_nonneg_left
        (bellOverlap_product_density_le (hden z).1 (hden z).2) (ht z)
    _ = 1 / (d : ℝ) := by rw [← Finset.sum_mul, hsum, one_mul]

theorem bellOverlap_nonneg {d : ℕ} {ρ : BipartiteMatrix d d}
    (hρ : ρ.PosSemidef) : 0 ≤ bellOverlap d ρ := by
  obtain ⟨m, v, rfl⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp hρ
  rw [bellOverlap_sum]
  apply Finset.sum_nonneg
  intro i _
  rw [bellOverlap_vecMulVec]
  exact div_nonneg (Complex.normSq_nonneg _) (Nat.cast_nonneg d)

theorem bellOverlap_vecMulVec_le_trace {d : ℕ} (hd : 0 < d)
    (v : Fin d × Fin d → ℂ) :
    bellOverlap d (Matrix.vecMulVec v (star v)) ≤
      (Matrix.vecMulVec v (star v)).trace.re := by
  have hc := complexSum_mul_normSq_le (fun i : Fin d => v (i, i)) (fun _ => (1 : ℂ))
  simp only [mul_one, Complex.normSq_one, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] at hc
  have hdiag : (∑ i : Fin d, Complex.normSq (v (i, i))) ≤
      ∑ x : Fin d × Fin d, Complex.normSq (v x) := by
    rw [Fintype.sum_prod_type]
    apply Finset.sum_le_sum
    intro i _
    exact Finset.single_le_sum (fun j _ => Complex.normSq_nonneg (v (i, j)))
      (Finset.mem_univ i)
  rw [bellOverlap_vecMulVec, trace_vecMulVec_re]
  exact (div_le_iff₀ (Nat.cast_pos.mpr hd)).mpr hc |>.trans hdiag

theorem bellOverlap_le_one {d : ℕ} (hd : 0 < d) {ρ : BipartiteMatrix d d}
    (hρ : IsDensity ρ) : bellOverlap d ρ ≤ 1 := by
  obtain ⟨m, v, hv⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp hρ.1
  have ht : (∑ i : Fin m, (Matrix.vecMulVec (v i) (star (v i))).trace.re) = 1 := by
    have hh := congrArg Complex.re hρ.2
    rw [hv, Matrix.trace_sum, Complex.re_sum] at hh
    simpa only [Complex.one_re] using hh
  rw [hv, bellOverlap_sum]
  calc
    _ ≤ ∑ i : Fin m, (Matrix.vecMulVec (v i) (star (v i))).trace.re :=
      Finset.sum_le_sum fun i _ => bellOverlap_vecMulVec_le_trace hd (v i)
    _ = 1 := ht

theorem FiniteProtocol.output_continuous {p : ℝ} {a b af bf : ℕ}
    (P : FiniteProtocol p a b af bf) : Continuous P.output :=
  P.outputLinearMap.continuous_of_finiteDimensional

theorem bellOverlap_continuous (d : ℕ) : Continuous (bellOverlap d) := by
  unfold bellOverlap
  exact Complex.continuous_re.comp
    ((continuous_const.mul continuous_id).matrix_trace)

theorem isDensity_isClosed {I : Type*} [Fintype I] [DecidableEq I] :
    IsClosed {ρ : Matrix I I ℂ | IsDensity ρ} :=
  Matrix.posSemidef_is_closed.inter
    (isClosed_eq continuous_id.matrix_trace continuous_const)

theorem isDensity_of_mem_closure_attainable {p s e : ℝ} {m d : ℕ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {σ : BipartiteMatrix d d}
    (hσ : σ ∈ closure (attainableOutputs p s m d e)) : IsDensity σ := by
  have hsub : attainableOutputs p s m d e ⊆ {ρ | IsDensity ρ} := by
    rintro τ ⟨a, b, ρ, P, hρ, _, _, rfl⟩
    exact P.output_isDensity hp0 hp1 hρ
  exact (isDensity_isClosed.closure_subset_iff.mpr hsub) hσ

theorem bellOverlap_le_on_closure {d : ℕ} {S : Set (BipartiteMatrix d d)} {c : ℝ}
    (hS : ∀ σ ∈ S, bellOverlap d σ ≤ c) :
    ∀ σ ∈ closure S, bellOverlap d σ ≤ c := by
  have hclosed : IsClosed {σ : BipartiteMatrix d d | bellOverlap d σ ≤ c} :=
    isClosed_le (bellOverlap_continuous d) continuous_const
  exact hclosed.closure_subset_iff.mpr hS

theorem bellOverlap_separable_closure_le {d : ℕ} {ρ : BipartiteMatrix d d}
    (hρ : ρ ∈ closure {σ : BipartiteMatrix d d | IsSeparable d d σ}) :
    bellOverlap d ρ ≤ 1 / (d : ℝ) :=
  bellOverlap_le_on_closure (fun _ h => bellOverlap_separable_le h) ρ hρ

theorem finiteAdaptiveStrongConverse_iff_finite : FiniteAdaptiveStrongConverse ↔
    ∀ (p s : ℝ) (m d : ℕ) (e : ℝ),
      0 ≤ p → p ≤ 1 → 0 < s → s ≤ 1 → 2 ≤ d →
      ∀ σ ∈ attainableOutputs p s m d e,
        bellOverlap d σ ≤ bellConverseBound p s m d e := by
  constructor
  · intro h p s m d e hp0 hp1 hs0 hs1 hd σ hσ
    exact h p s m d e hp0 hp1 hs0 hs1 hd σ (subset_closure hσ)
  · intro h p s m d e hp0 hp1 hs0 hs1 hd
    exact bellOverlap_le_on_closure (h p s m d e hp0 hp1 hs0 hs1 hd)

end QuantumProver.AmplitudeDamping.FiniteModel

namespace QuantumProver.AmplitudeDamping.ComparisonOrder

open scoped ComplexOrder MatrixOrder Matrix Matrix.Norms.L2Operator

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem negative_rpow_antitone {σ τ : Matrix I I ℂ}
    (hσ : σ.PosDef) (hστ : σ ≤ τ) {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) :
    CFC.rpow τ (-β) ≤ CFC.rpow σ (-β) := by
  have hτ : IsStrictlyPositive τ := hσ.isStrictlyPositive.of_le hστ
  have hi := CStarAlgebra.rpow_neg_one_le_rpow_neg_one hστ hσ.isStrictlyPositive
  have hp := CFC.rpow_le_rpow ⟨hβ0, hβ1⟩ hi
  rw [CFC.rpow_rpow τ (-1 : ℝ) β (by norm_num) hτ,
    CFC.rpow_rpow σ (-1 : ℝ) β (by norm_num) hσ.isStrictlyPositive,
    neg_one_mul] at hp
  exact hp

theorem right_gram_le_one {C : Matrix I I ℂ} (hC : Cᴴ * C ≤ 1) : C * Cᴴ ≤ 1 := by
  have hn : ‖Cᴴ * C‖ ≤ 1 :=
    (CStarAlgebra.norm_le_one_iff_of_nonneg (Cᴴ * C)
      (Matrix.posSemidef_conjTranspose_mul_self C).nonneg).mpr hC
  have heq : ‖C * Cᴴ‖ = ‖Cᴴ * C‖ := by
    change ‖C * star C‖ = ‖star C * C‖
    rw [CStarRing.norm_self_mul_star, CStarRing.norm_star_mul_self]
  exact (CStarAlgebra.norm_le_one_iff_of_nonneg (C * Cᴴ)
    (Matrix.posSemidef_self_mul_conjTranspose C).nonneg).mp (heq.trans_le hn)

def comparisonContraction (σ τ : Matrix I I ℂ) (β : ℝ) : Matrix I I ℂ :=
  CFC.rpow τ (-(β / 2)) * CFC.rpow σ (β / 2)

theorem rpow_mul_eq_add {X : Matrix I I ℂ} (hX : IsUnit X) (x y : ℝ) :
    CFC.rpow X x * CFC.rpow X y = CFC.rpow X (x + y) :=
  (CFC.rpow_add (a := X) (x := x) (y := y) hX).symm

theorem comparisonContraction_left_gram {σ τ : Matrix I I ℂ}
    (hσ : σ.PosDef) (hστ : σ ≤ τ) {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) :
    (comparisonContraction σ τ β)ᴴ * comparisonContraction σ τ β ≤ 1 := by
  have hτ : IsStrictlyPositive τ := hσ.isStrictlyPositive.of_le hστ
  let S := CFC.rpow σ (β / 2)
  let T := CFC.rpow τ (-(β / 2))
  have hS : Sᴴ = S :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.rpow_nonneg (a := σ) (y := β / 2))).1
  have hT : Tᴴ = T :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.rpow_nonneg (a := τ) (y := -(β / 2)))).1
  have hTT : T * T = CFC.rpow τ (-β) := by
    dsimp only [T]
    rw [rpow_mul_eq_add hτ.isUnit]
    congr 1
    ring
  have hSidentity : S * CFC.rpow σ (-β) * S = 1 := by
    dsimp only [S]
    rw [rpow_mul_eq_add hσ.isUnit, rpow_mul_eq_add hσ.isUnit]
    convert CFC.rpow_zero σ hσ.posSemidef.nonneg using 1 <;> congr 1 <;> ring
  have hinner : S * CFC.rpow τ (-β) * S ≤ S * CFC.rpow σ (-β) * S :=
    conjugate_le_conjugate_of_nonneg
      (negative_rpow_antitone hσ hστ hβ0 hβ1) (CFC.rpow_nonneg (a := σ) (y := β / 2))
  calc
    (comparisonContraction σ τ β)ᴴ * comparisonContraction σ τ β =
        S * (T * T) * S := by
      change (T * S)ᴴ * (T * S) = _
      rw [Matrix.conjTranspose_mul, hS, hT]
      noncomm_ring
    _ = S * CFC.rpow τ (-β) * S := by rw [hTT]
    _ ≤ S * CFC.rpow σ (-β) * S := hinner
    _ = 1 := hSidentity

theorem comparisonContraction_right_gram {σ τ : Matrix I I ℂ}
    (hσ : σ.PosDef) (hστ : σ ≤ τ) {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) :
    comparisonContraction σ τ β * (comparisonContraction σ τ β)ᴴ ≤ 1 :=
  right_gram_le_one (comparisonContraction_left_gram hσ hστ hβ0 hβ1)

theorem comparisonContraction_sandwich (ρ σ τ : Matrix I I ℂ)
    (hσ : σ.PosDef) (β : ℝ) :
    comparisonContraction σ τ β *
        (CFC.rpow σ (-(β / 2)) * ρ * CFC.rpow σ (-(β / 2))) *
          (comparisonContraction σ τ β)ᴴ =
      CFC.rpow τ (-(β / 2)) * ρ * CFC.rpow τ (-(β / 2)) := by
  let S := CFC.rpow σ (β / 2)
  let H := CFC.rpow σ (-(β / 2))
  let T := CFC.rpow τ (-(β / 2))
  have hS : Sᴴ = S :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.rpow_nonneg (a := σ) (y := β / 2))).1
  have hT : Tᴴ = T :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.rpow_nonneg (a := τ) (y := -(β / 2)))).1
  have hSH : S * H = 1 := CFC.rpow_mul_rpow_neg (β / 2) hσ.isStrictlyPositive
  have hHS : H * S = 1 := CFC.rpow_neg_mul_rpow (β / 2) hσ.isStrictlyPositive
  change (T * S) * (H * ρ * H) * (T * S)ᴴ = T * ρ * T
  rw [Matrix.conjTranspose_mul, hS, hT]
  calc
    _ = T * (S * H) * ρ * (H * S) * T := by noncomm_ring
    _ = T * ρ * T := by rw [hSH, hHS]; simp

end QuantumProver.AmplitudeDamping.ComparisonOrder

namespace QuantumProver.AmplitudeDamping.FiniteModel

def maximallyMixed (a : ℕ) : Matrix (Fin a) (Fin a) ℂ :=
  ((a : ℝ)⁻¹) • (1 : Matrix (Fin a) (Fin a) ℂ)

theorem maximallyMixed_posDef {a : ℕ} (ha : 0 < a) :
    (maximallyMixed a).PosDef :=
  Matrix.PosDef.one.smul (inv_pos.mpr (Nat.cast_pos.mpr ha))

theorem maximallyMixed_isDensity {a : ℕ} (ha : 0 < a) :
    IsDensity (maximallyMixed a) := by
  refine ⟨(maximallyMixed_posDef ha).posSemidef, ?_⟩
  have haz : (a : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr ha.ne'
  simp [maximallyMixed, Matrix.trace_smul, Matrix.trace_one, Complex.real_smul, haz]

theorem product_isSeparable {a b : ℕ}
    {A : Matrix (Fin a) (Fin a) ℂ} {B : Matrix (Fin b) (Fin b) ℂ}
    (hA : IsDensity A) (hB : IsDensity B) : IsSeparable a b (A ⊗ₖ B) := by
  refine ⟨1, fun _ => 1, fun _ => A, fun _ => B, ?_, ?_, ?_, ?_⟩
  · intro z; norm_num
  · simp
  · intro z; exact ⟨hA, hB⟩
  · simp

theorem IsSeparable.isDensity {a b : ℕ} {ρ : BipartiteMatrix a b}
    (hρ : IsSeparable a b ρ) : IsDensity ρ := by
  obtain ⟨k, t, A, B, ht, hsum, hden, rfl⟩ := hρ
  refine ⟨?_, ?_⟩
  · apply Matrix.posSemidef_sum Finset.univ
    intro z _
    rw [Complex.coe_smul]
    exact ((hden z).1.1.kronecker (hden z).2.1).smul (ht z)
  · have htr (z : Fin k) : (A z ⊗ₖ B z).trace = 1 := by
      rw [Matrix.trace_kronecker, (hden z).1.2, (hden z).2.2, mul_one]
    rw [Matrix.trace_sum]
    simp_rw [Matrix.trace_smul, htr, smul_eq_mul, mul_one]
    simpa using congrArg Complex.ofReal hsum

def regularizedComparison {a b : ℕ} (ε : ℝ) (σ : BipartiteMatrix a b) :
    BipartiteMatrix a b :=
  (1 - ε) • σ + ε • (maximallyMixed a ⊗ₖ maximallyMixed b)

theorem regularizedComparison_posDef {a b : ℕ}
    {σ : BipartiteMatrix a b} (hσ : σ.PosSemidef) (ha : 0 < a) (hb : 0 < b)
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    (regularizedComparison ε σ).PosDef := by
  exact Matrix.PosDef.posSemidef_add (hσ.smul (sub_nonneg.mpr hε1))
    (((maximallyMixed_posDef ha).kronecker (maximallyMixed_posDef hb)).smul hε0)

theorem regularizedComparison_isSeparable {a b : ℕ} {σ : BipartiteMatrix a b}
    (hσ : IsSeparable a b σ) (ha : 0 < a) (hb : 0 < b)
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    IsSeparable a b (regularizedComparison ε σ) := by
  obtain ⟨k, t, A, B, ht, hsum, hden, rfl⟩ := hσ
  refine ⟨k + 1, Fin.cases ε (fun z => (1 - ε) * t z),
    Fin.cases (maximallyMixed a) A, Fin.cases (maximallyMixed b) B, ?_, ?_, ?_, ?_⟩
  · intro z
    exact Fin.cases hε0 (fun j => mul_nonneg (sub_nonneg.mpr hε1) (ht j)) z
  · rw [Fin.sum_univ_succ]
    simp only [Fin.cases_zero, Fin.cases_succ, ← Finset.mul_sum, hsum]
    ring
  · intro z
    exact Fin.cases ⟨maximallyMixed_isDensity ha, maximallyMixed_isDensity hb⟩ hden z
  · rw [Fin.sum_univ_succ]
    simp only [Fin.cases_zero, Fin.cases_succ, regularizedComparison,
      Complex.coe_smul, mul_smul]
    rw [← Finset.smul_sum]
    exact add_comm _ _

theorem regularizedComparison_isDensity {a b : ℕ} {σ : BipartiteMatrix a b}
    (hσ : IsSeparable a b σ) (ha : 0 < a) (hb : 0 < b)
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    IsDensity (regularizedComparison ε σ) :=
  (regularizedComparison_isSeparable hσ ha hb hε0 hε1).isDensity

theorem regularizedComparison_continuous {a b : ℕ} (σ : BipartiteMatrix a b) :
    Continuous (fun ε : ℝ => regularizedComparison ε σ) := by
  unfold regularizedComparison
  exact ((continuous_const.sub continuous_id).smul continuous_const).add
    (continuous_id.smul continuous_const)

theorem regularizedComparison_tendsto {a b : ℕ} (σ : BipartiteMatrix a b) :
    Filter.Tendsto (fun ε : ℝ => regularizedComparison ε σ) (nhds 0) (nhds σ) := by
  have hzero : regularizedComparison 0 σ = σ := by simp [regularizedComparison]
  simpa only [hzero] using (regularizedComparison_continuous σ).tendsto 0

theorem maximallyMixed_kronecker_eq (a b : ℕ) :
    maximallyMixed a ⊗ₖ maximallyMixed b =
      (((a : ℝ) * (b : ℝ))⁻¹) • (1 : BipartiteMatrix a b) := by
  unfold maximallyMixed
  rw [Matrix.smul_kronecker, Matrix.kronecker_smul, Matrix.one_kronecker_one,
    smul_smul]
  congr 1
  rw [mul_inv_rev]
  exact mul_comm _ _

theorem regularizedComparison_eq_smul_add_scalar {a b : ℕ}
    (ε : ℝ) (σ : BipartiteMatrix a b) :
    regularizedComparison ε σ = (1 - ε) • σ +
      (ε / ((a : ℝ) * (b : ℝ))) • (1 : BipartiteMatrix a b) := by
  rw [regularizedComparison, maximallyMixed_kronecker_eq, smul_smul]
  rfl

theorem regularizedComparison_commute {a b : ℕ}
    (ε : ℝ) (σ : BipartiteMatrix a b) : Commute σ (regularizedComparison ε σ) := by
  change σ * regularizedComparison ε σ = regularizedComparison ε σ * σ
  simp [regularizedComparison_eq_smul_add_scalar, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_smul, Matrix.smul_mul]

theorem supportLE_of_posDef {I : Type*} [Fintype I] [DecidableEq I]
    (ρ : Matrix I I ℂ) {σ : Matrix I I ℂ} (hσ : σ.PosDef) : SupportLE ρ σ := by
  unfold SupportLE
  have hr : LinearMap.range σ.mulVecLin = ⊤ :=
    LinearMap.range_eq_top.mpr (Matrix.mulVec_surjective_iff_isUnit.mpr hσ.isUnit)
  rw [hr]
  exact le_top

theorem regularizedComparison_supportLE {a b : ℕ}
    (ρ : BipartiteMatrix a b) {σ : BipartiteMatrix a b}
    (hσ : σ.PosSemidef) (ha : 0 < a) (hb : 0 < b)
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    SupportLE ρ (regularizedComparison ε σ) :=
  supportLE_of_posDef ρ (regularizedComparison_posDef hσ ha hb hε0 hε1)

theorem supportLE_kernel_le {I : Type*} [Fintype I] [DecidableEq I]
    {ρ σ : Matrix I I ℂ} (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian)
    (hSupport : SupportLE ρ σ) :
    LinearMap.ker σ.mulVecLin ≤ LinearMap.ker ρ.mulVecLin := by
  unfold SupportLE at hSupport
  intro v hv
  change σ *ᵥ v = 0 at hv
  change ρ *ᵥ v = 0
  have hinner (x : I → ℂ) : star v ⬝ᵥ ρ *ᵥ x = 0 := by
    have hr : ρ *ᵥ x ∈ LinearMap.range σ.mulVecLin :=
      hSupport (show ρ *ᵥ x ∈ LinearMap.range ρ.mulVecLin from ⟨x, rfl⟩)
    obtain ⟨y, hy⟩ := hr
    change σ *ᵥ y = ρ *ᵥ x at hy
    have hi := congrArg star (hσ.star_dotProduct_mulVec_comm v y)
    have hz : star v ⬝ᵥ σ *ᵥ y = 0 := by simpa [hv] using hi
    simpa only [hy] using hz
  funext j
  have hstar : star (Pi.single j (1 : ℂ) : I → ℂ) =
      (Pi.single j (1 : ℂ) : I → ℂ) := by
    ext i
    by_cases hi : i = j <;> simp [Pi.single_apply, Pi.star_def, hi]
  have hj := hρ.star_dotProduct_mulVec_comm v (Pi.single j (1 : ℂ))
  rw [hinner, star_zero, hstar, single_dotProduct, one_mul] at hj
  exact hj.symm

open scoped Matrix.Norms.L2Operator

theorem sandwichedTrace_antitone_comparison {I : Type*} [Fintype I] [DecidableEq I]
    {ρ σ τ : Matrix I I ℂ} (hρ : ρ.PosSemidef) (hσ : σ.PosDef)
    (hστ : σ ≤ τ) {α : ℝ} (hα : 1 ≤ α) :
    sandwichedTrace α ρ τ ≤ sandwichedTrace α ρ σ := by
  let β : ℝ := (α - 1) / α
  have hα0 : 0 < α := lt_of_lt_of_le zero_lt_one hα
  have hβ0 : 0 ≤ β := div_nonneg (sub_nonneg.mpr hα) hα0.le
  have hβ1 : β ≤ 1 := by
    dsimp only [β]
    apply (div_le_iff₀ hα0).mpr
    linarith
  have he : (1 - α) / (2 * α) = -(β / 2) := by
    dsimp only [β]
    field_simp [hα0.ne']
    <;> ring
  let W := CFC.rpow σ (-(β / 2))
  have hW : Wᴴ = W :=
    (Matrix.nonneg_iff_posSemidef.mp
      (CFC.rpow_nonneg (a := σ) (y := -(β / 2)))).1
  have hX : (W * ρ * W).PosSemidef := by
    simpa only [hW] using hρ.mul_mul_conjTranspose_same W
  have ht := QuantumProver.AmplitudeDamping.TracePower.trace_rpow_contraction hX
    (QuantumProver.AmplitudeDamping.ComparisonOrder.comparisonContraction_left_gram
      hσ hστ hβ0 hβ1)
    (QuantumProver.AmplitudeDamping.ComparisonOrder.comparisonContraction_right_gram
      hσ hστ hβ0 hβ1) hα
  dsimp only [W] at ht
  rw [QuantumProver.AmplitudeDamping.ComparisonOrder.comparisonContraction_sandwich
    ρ σ τ hσ β] at ht
  simpa only [sandwichedTrace, he] using ht

theorem left_identity_of_supportLE {I : Type*} [Fintype I] [DecidableEq I]
    {P ρ σ : Matrix I I ℂ} (hPσ : P * σ = σ) (hSupport : SupportLE ρ σ) :
    P * ρ = ρ := by
  unfold SupportLE at hSupport
  ext i j
  let e : I → ℂ := Pi.single j (1 : ℂ)
  have hr : ρ *ᵥ e ∈ LinearMap.range σ.mulVecLin :=
    hSupport (show ρ *ᵥ e ∈ LinearMap.range ρ.mulVecLin from ⟨e, rfl⟩)
  obtain ⟨y, hy⟩ := hr
  change σ *ᵥ y = ρ *ᵥ e at hy
  have hv : P *ᵥ (ρ *ᵥ e) = ρ *ᵥ e := by
    rw [← hy, Matrix.mulVec_mulVec, hPσ]
  rw [Matrix.mulVec_mulVec] at hv
  have hi := congrArg (fun x : I → ℂ => x i) hv
  simpa only [e, Matrix.mulVec_single_one, Matrix.col_apply] using hi

def supportProjector {I : Type*} [Fintype I] [DecidableEq I]
    (σ : Matrix I I ℂ) (hσ : σ.IsHermitian) : Matrix I I ℂ :=
  (hσ.eigenvectorUnitary : Matrix I I ℂ) *
    Matrix.diagonal (fun i => if hσ.eigenvalues i = 0 then (0 : ℂ) else 1) *
      (hσ.eigenvectorUnitary : Matrix I I ℂ)ᴴ

theorem supportProjector_mul_self {I : Type*} [Fintype I] [DecidableEq I]
    {σ : Matrix I I ℂ} (hσ : σ.IsHermitian) : supportProjector σ hσ * σ = σ := by
  let U := hσ.eigenvectorUnitary
  let d : I → ℂ := fun i => if hσ.eigenvalues i = 0 then 0 else 1
  have hs : σ = (U : Matrix I I ℂ) *
      Matrix.diagonal (fun i => (hσ.eigenvalues i : ℂ)) * (U : Matrix I I ℂ)ᴴ :=
    hσ.spectral_theorem
  have hU : (U : Matrix I I ℂ)ᴴ * (U : Matrix I I ℂ) = 1 :=
    Unitary.coe_star_mul_self U
  have hd : Matrix.diagonal d * Matrix.diagonal (fun i => (hσ.eigenvalues i : ℂ)) =
      Matrix.diagonal (fun i => (hσ.eigenvalues i : ℂ)) := by
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    by_cases hi : hσ.eigenvalues i = 0 <;> simp [d, hi]
  change ((U : Matrix I I ℂ) * Matrix.diagonal d * (U : Matrix I I ℂ)ᴴ) * σ = σ
  calc
    _ = (U : Matrix I I ℂ) * Matrix.diagonal d *
        ((U : Matrix I I ℂ)ᴴ * (U : Matrix I I ℂ)) *
          Matrix.diagonal (fun i => (hσ.eigenvalues i : ℂ)) *
            (U : Matrix I I ℂ)ᴴ := by
      conv_lhs => rw [hs]
      noncomm_ring
    _ = (U : Matrix I I ℂ) *
        (Matrix.diagonal d * Matrix.diagonal (fun i => (hσ.eigenvalues i : ℂ))) *
          (U : Matrix I I ℂ)ᴴ := by rw [hU]; noncomm_ring
    _ = σ := by rw [hd]; exact hs.symm

theorem supportProjector_mul_of_supportLE {I : Type*} [Fintype I] [DecidableEq I]
    {ρ σ : Matrix I I ℂ} (hσ : σ.IsHermitian) (hSupport : SupportLE ρ σ) :
    supportProjector σ hσ * ρ = ρ :=
  left_identity_of_supportLE (supportProjector_mul_self hσ) hSupport

theorem supported_rpow_cancel {I : Type*} [Fintype I] [DecidableEq I]
    {σ : Matrix I I ℂ} (hσ : σ.PosSemidef) {β : ℝ} (hβ : 0 < β) :
    CFC.rpow σ (-(β / 2)) * CFC.rpow σ β * CFC.rpow σ (-(β / 2)) =
      supportProjector σ hσ.1 := by
  let U := hσ.1.eigenvectorUnitary
  let F := Unitary.conjStarAlgAut ℝ (Matrix I I ℂ) U
  let ev := hσ.1.eigenvalues
  have hp (t : ℝ) : CFC.rpow σ t =
      F (Matrix.diagonal (fun i => (((ev i) ^ t : ℝ) : ℂ))) := by
    have heq : CFC.rpow σ t = cfc (fun x : ℝ => x ^ t) σ :=
      CFC.rpow_eq_cfc_real (A := Matrix I I ℂ) (a := σ) (y := t) hσ.nonneg
    rw [heq, QuantumProver.AmplitudeDamping.TracePower.cfc_spectral _ hσ.1]
  have hd : Matrix.diagonal (fun i => (((ev i) ^ (-(β / 2)) : ℝ) : ℂ)) *
      Matrix.diagonal (fun i => (((ev i) ^ β : ℝ) : ℂ)) *
        Matrix.diagonal (fun i => (((ev i) ^ (-(β / 2)) : ℝ) : ℂ)) =
          Matrix.diagonal (fun i => if ev i = 0 then (0 : ℂ) else 1) := by
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    change (((ev i) ^ (-(β / 2)) : ℝ) : ℂ) * (((ev i) ^ β : ℝ) : ℂ) *
      (((ev i) ^ (-(β / 2)) : ℝ) : ℂ) = if ev i = 0 then 0 else 1
    by_cases hi : ev i = 0
    · simp [hi, Real.zero_rpow hβ.ne']
    · have hx : 0 < ev i := lt_of_le_of_ne (hσ.eigenvalues_nonneg i) (Ne.symm hi)
      have he : -(β / 2) + β + -(β / 2) = 0 := by ring
      rw [← Complex.ofReal_mul, ← Complex.ofReal_mul,
        ← Real.rpow_add hx, ← Real.rpow_add hx, he]
      simp [hi]
  calc
    _ = F (Matrix.diagonal (fun i => (((ev i) ^ (-(β / 2)) : ℝ) : ℂ))) *
        F (Matrix.diagonal (fun i => (((ev i) ^ β : ℝ) : ℂ))) *
          F (Matrix.diagonal (fun i => (((ev i) ^ (-(β / 2)) : ℝ) : ℂ))) := by
      simp_rw [hp]
    _ = F (Matrix.diagonal (fun i => (((ev i) ^ (-(β / 2)) : ℝ) : ℂ)) *
        Matrix.diagonal (fun i => (((ev i) ^ β : ℝ) : ℂ)) *
          Matrix.diagonal (fun i => (((ev i) ^ (-(β / 2)) : ℝ) : ℂ))) := by
      rw [map_mul, map_mul]
    _ = F (Matrix.diagonal (fun i => if ev i = 0 then (0 : ℂ) else 1)) := by rw [hd]
    _ = supportProjector σ hσ.1 := rfl

theorem supported_weighted_trace {I : Type*} [Fintype I] [DecidableEq I]
    {ρ σ : Matrix I I ℂ} (hσ : σ.PosSemidef) (hSupport : SupportLE ρ σ)
    {β : ℝ} (hβ : 0 < β) :
    (CFC.rpow σ β *
      (CFC.rpow σ (-(β / 2)) * ρ * CFC.rpow σ (-(β / 2)))).trace = ρ.trace := by
  let A := CFC.rpow σ β
  let W := CFC.rpow σ (-(β / 2))
  change (A * (W * ρ * W)).trace = ρ.trace
  calc
    _ = (A * W * ρ * W).trace := by congr 1; noncomm_ring
    _ = (W * (A * W * ρ)).trace := Matrix.trace_mul_comm _ _
    _ = ((W * A * W) * ρ).trace := by congr 1; noncomm_ring
    _ = ρ.trace := by
      change ((CFC.rpow σ (-(β / 2)) * CFC.rpow σ β *
        CFC.rpow σ (-(β / 2))) * ρ).trace = ρ.trace
      rw [supported_rpow_cancel hσ hβ,
        supportProjector_mul_of_supportLE hσ.1 hSupport]

theorem supported_weighted_trace_eq_one {I : Type*} [Fintype I] [DecidableEq I]
    {ρ σ : Matrix I I ℂ} (hρ : IsDensity ρ) (hσ : σ.PosSemidef)
    (hSupport : SupportLE ρ σ) {β : ℝ} (hβ : 0 < β) :
    (CFC.rpow σ β *
      (CFC.rpow σ (-(β / 2)) * ρ * CFC.rpow σ (-(β / 2)))).trace.re = 1 := by
  rw [supported_weighted_trace hσ hSupport hβ, hρ.2]
  rfl

theorem sandwichedTrace_ge_one {I : Type*} [Fintype I] [DecidableEq I]
    {ρ σ : Matrix I I ℂ} (hρ : IsDensity ρ) (hσ : IsDensity σ)
    (hSupport : SupportLE ρ σ) {α : ℝ} (hα : 1 < α) :
    1 ≤ sandwichedTrace α ρ σ := by
  let β : ℝ := (α - 1) / α
  let W := CFC.rpow σ (-(β / 2))
  have hα0 : α ≠ 0 := by linarith
  have hβ : 0 < β := div_pos (sub_pos.mpr hα) (by linarith)
  have he : (1 - α) / (2 * α) = -(β / 2) := by
    dsimp only [β]
    field_simp [hα0] <;> ring
  have hW : Wᴴ = W :=
    (Matrix.nonneg_iff_posSemidef.mp
      (CFC.rpow_nonneg (a := σ) (y := -(β / 2)))).1
  have hX : (W * ρ * W).PosSemidef := by
    simpa only [hW] using hρ.1.mul_mul_conjTranspose_same W
  have ht := QuantumProver.AmplitudeDamping.PositiveTrace.density_weighted_trace_rpow_le
    hσ hX hα
  have hc : (CFC.rpow σ ((α - 1) / α) * (W * ρ * W)).trace.re = 1 :=
    supported_weighted_trace_eq_one hρ hσ.1 hSupport hβ
  rw [hc, Real.one_rpow] at ht
  simpa only [sandwichedTrace, he, W] using ht

theorem sandwichedDivergence_nonneg {I : Type*} [Fintype I] [DecidableEq I]
    {ρ σ : Matrix I I ℂ} (hρ : IsDensity ρ) (hσ : IsDensity σ)
    {α : ℝ} (hα : 1 < α) : 0 ≤ sandwichedDivergence α ρ σ := by
  classical
  unfold sandwichedDivergence
  split_ifs with hSupport
  · exact EReal.coe_nonneg.mpr
      (div_nonneg (Real.log_nonneg (sandwichedTrace_ge_one hρ hσ hSupport hα))
        (mul_nonneg (sub_pos.mpr hα).le (Real.log_pos (by norm_num : 1 < (2 : ℝ))).le))
  · exact le_top

theorem sandwichedEntanglement_nonneg {a b : ℕ} {ρ : BipartiteMatrix a b}
    (hρ : IsDensity ρ) {α : ℝ} (hα : 1 < α) :
    0 ≤ sandwichedEntanglement α a b ρ := by
  unfold sandwichedEntanglement
  refine le_sInf ?_
  rintro x ⟨σ, hσ, rfl⟩
  exact sandwichedDivergence_nonneg hρ hσ.1 hα

theorem bellVector_mass_one {d : ℕ} (hd : 0 < d) :
    QuantumProver.AmplitudeDamping.Testing.vectorMass (bellVector d) = 1 := by
  have h := congrArg Complex.re (bellProjector_trace hd)
  rw [bellProjector_eq_vecMulVec, trace_vecMulVec_re] at h
  simpa only [QuantumProver.AmplitudeDamping.Testing.vectorMass, Complex.one_re] using h

theorem bellOverlap_eq_expectation (d : ℕ) (ρ : BipartiteMatrix d d) :
    bellOverlap d ρ = QuantumProver.AmplitudeDamping.Testing.expectation ρ (bellVector d) := by
  unfold bellOverlap QuantumProver.AmplitudeDamping.Testing.expectation
  rw [bellProjector_eq_vecMulVec, Matrix.vecMulVec_mul, Matrix.trace_vecMulVec,
    dotProduct_comm, ← Matrix.dotProduct_mulVec]

theorem sandwichedTrace_nonneg {I : Type*} [Fintype I] [DecidableEq I]
    {ρ σ : Matrix I I ℂ} (hρ : ρ.PosSemidef) (α : ℝ) :
    0 ≤ sandwichedTrace α ρ σ := by
  let W := CFC.rpow σ ((1 - α) / (2 * α))
  have hW : Wᴴ = W :=
    (Matrix.nonneg_iff_posSemidef.mp
      (CFC.rpow_nonneg (a := σ) (y := (1 - α) / (2 * α)))).1
  have hX : (W * ρ * W).PosSemidef := by
    simpa only [hW] using hρ.mul_mul_conjTranspose_same W
  change 0 ≤ (CFC.rpow (W * ρ * W) α).trace.re
  rw [QuantumProver.AmplitudeDamping.TracePower.trace_rpow_eq_sum hX]
  exact Finset.sum_nonneg (fun i _ => Real.rpow_nonneg (hX.eigenvalues_nonneg i) α)

theorem bell_pureProbe_fullRank {d : ℕ} {ρ σ : BipartiteMatrix d d}
    (hd : 0 < d) (hρ : ρ.PosSemidef) (hσ : σ.PosDef)
    {α : ℝ} (hα : 1 < α) :
    (bellOverlap d ρ) ^ α ≤ (bellOverlap d σ) ^ (α - 1) *
      sandwichedTrace α ρ σ := by
  have ht := QuantumProver.AmplitudeDamping.Testing.fullRank_pureProbe
    hρ hσ (bellVector d) (bellVector_mass_one hd) hα
  simpa only [← bellOverlap_eq_expectation] using ht

theorem bell_fullRank_separable_trace_bound {d : ℕ} {ρ σ : BipartiteMatrix d d}
    (hd : 0 < d) (hρ : ρ.PosSemidef) (hσ : σ.PosDef)
    (hsep : IsSeparable d d σ) {α : ℝ} (hα : 1 < α) :
    (d : ℝ) ^ (α - 1) * (bellOverlap d ρ) ^ α ≤ sandwichedTrace α ρ σ := by
  have hdpos : 0 < (d : ℝ) := by exact_mod_cast hd
  have hpower : (bellOverlap d σ) ^ (α - 1) ≤ (1 / (d : ℝ)) ^ (α - 1) :=
    Real.rpow_le_rpow (bellOverlap_nonneg hsep.isDensity.1)
      (bellOverlap_separable_le hsep) (by linarith)
  have ht : (bellOverlap d ρ) ^ α ≤ (1 / (d : ℝ)) ^ (α - 1) *
      sandwichedTrace α ρ σ :=
    (bell_pureProbe_fullRank hd hρ hσ hα).trans
      (mul_le_mul_of_nonneg_right hpower (sandwichedTrace_nonneg hρ α))
  have hc : (d : ℝ) ^ (α - 1) * (1 / (d : ℝ)) ^ (α - 1) = 1 := by
    rw [one_div, Real.inv_rpow hdpos.le,
      mul_inv_cancel₀ (Real.rpow_pos_of_pos hdpos (α - 1)).ne']
  calc
    _ ≤ (d : ℝ) ^ (α - 1) * ((1 / (d : ℝ)) ^ (α - 1) *
        sandwichedTrace α ρ σ) :=
      mul_le_mul_of_nonneg_left ht (Real.rpow_nonneg hdpos.le (α - 1))
    _ = sandwichedTrace α ρ σ := by rw [← mul_assoc, hc, one_mul]

def supportBasis {I : Type*} [Fintype I] [DecidableEq I]
    (σ : Matrix I I ℂ) (hσ : σ.IsHermitian) (ρ : Matrix I I ℂ) : Matrix I I ℂ :=
  (hσ.eigenvectorUnitary : Matrix I I ℂ)ᴴ * ρ *
    (hσ.eigenvectorUnitary : Matrix I I ℂ)

theorem supportBasis_diagonal_fix {I : Type*} [Fintype I] [DecidableEq I]
    {ρ σ : Matrix I I ℂ} (hσ : σ.IsHermitian) (hSupport : SupportLE ρ σ) :
    Matrix.diagonal (fun i => if hσ.eigenvalues i = 0 then (0 : ℂ) else 1) *
      supportBasis σ hσ ρ = supportBasis σ hσ ρ := by
  let U := hσ.eigenvectorUnitary
  let D : Matrix I I ℂ := Matrix.diagonal
    (fun i => if hσ.eigenvalues i = 0 then (0 : ℂ) else 1)
  have hU : (U : Matrix I I ℂ)ᴴ * (U : Matrix I I ℂ) = 1 :=
    Unitary.coe_star_mul_self U
  have hh := congrArg
    (fun M : Matrix I I ℂ => (U : Matrix I I ℂ)ᴴ * M * (U : Matrix I I ℂ))
    (supportProjector_mul_of_supportLE hσ hSupport)
  change (U : Matrix I I ℂ)ᴴ *
    (((U : Matrix I I ℂ) * D * (U : Matrix I I ℂ)ᴴ) * ρ) *
      (U : Matrix I I ℂ) = supportBasis σ hσ ρ at hh
  have he : (U : Matrix I I ℂ)ᴴ *
      (((U : Matrix I I ℂ) * D * (U : Matrix I I ℂ)ᴴ) * ρ) *
        (U : Matrix I I ℂ) = D * supportBasis σ hσ ρ := by
    calc
      _ = ((U : Matrix I I ℂ)ᴴ * (U : Matrix I I ℂ)) * D *
          ((U : Matrix I I ℂ)ᴴ * ρ * (U : Matrix I I ℂ)) := by noncomm_ring
      _ = D * supportBasis σ hσ ρ := by
        rw [hU, Matrix.one_mul]
        rfl
  rw [he] at hh
  exact hh

theorem supportBasis_zero_row {I : Type*} [Fintype I] [DecidableEq I]
    {ρ σ : Matrix I I ℂ} (hσ : σ.IsHermitian) (hSupport : SupportLE ρ σ)
    (i j : I) (hi : hσ.eigenvalues i = 0) : supportBasis σ hσ ρ i j = 0 := by
  have he := congrArg (fun M : Matrix I I ℂ => M i j)
    (supportBasis_diagonal_fix hσ hSupport)
  simpa [Matrix.diagonal_mul, hi] using he.symm

theorem supportBasis_zero_column {I : Type*} [Fintype I] [DecidableEq I]
    {ρ σ : Matrix I I ℂ} (hρ : ρ.PosSemidef) (hσ : σ.IsHermitian)
    (hSupport : SupportLE ρ σ) (i j : I) (hj : hσ.eigenvalues j = 0) :
    supportBasis σ hσ ρ i j = 0 := by
  have hR : (supportBasis σ hσ ρ)ᴴ = supportBasis σ hσ ρ := by
    simpa only [supportBasis, Matrix.conjTranspose_conjTranspose] using
      (hρ.mul_mul_conjTranspose_same
        (hσ.eigenvectorUnitary : Matrix I I ℂ)ᴴ).1.eq
  have he := congrArg (fun M : Matrix I I ℂ => M i j) hR
  have hz := supportBasis_zero_row hσ hSupport j i hj
  simpa only [Matrix.conjTranspose_apply, hz, star_zero] using he.symm

theorem supportBasis_self {I : Type*} [Fintype I] [DecidableEq I]
    {σ : Matrix I I ℂ} (hσ : σ.IsHermitian) :
    supportBasis σ hσ σ = Matrix.diagonal (fun i => (hσ.eigenvalues i : ℂ)) := by
  let U := hσ.eigenvectorUnitary
  let ev := hσ.eigenvalues
  have hs : σ = (U : Matrix I I ℂ) * Matrix.diagonal (fun i => (ev i : ℂ)) *
      (U : Matrix I I ℂ)ᴴ := hσ.spectral_theorem
  have hU : (U : Matrix I I ℂ)ᴴ * (U : Matrix I I ℂ) = 1 :=
    Unitary.coe_star_mul_self U
  change (U : Matrix I I ℂ)ᴴ * σ * (U : Matrix I I ℂ) =
    Matrix.diagonal (fun i => (ev i : ℂ))
  calc
    _ = ((U : Matrix I I ℂ)ᴴ * (U : Matrix I I ℂ)) *
        Matrix.diagonal (fun i => (ev i : ℂ)) *
          ((U : Matrix I I ℂ)ᴴ * (U : Matrix I I ℂ)) := by
      conv_lhs => rw [hs]
      noncomm_ring
    _ = Matrix.diagonal (fun i => (ev i : ℂ)) := by rw [hU]; simp

theorem supportBasis_add {I : Type*} [Fintype I] [DecidableEq I]
    {σ : Matrix I I ℂ} (hσ : σ.IsHermitian) (ρ τ : Matrix I I ℂ) :
    supportBasis σ hσ (ρ + τ) = supportBasis σ hσ ρ + supportBasis σ hσ τ := by
  simp only [supportBasis, Matrix.mul_add, Matrix.add_mul]

theorem supportBasis_smul {I : Type*} [Fintype I] [DecidableEq I]
    {σ : Matrix I I ℂ} (hσ : σ.IsHermitian) (t : ℝ) (ρ : Matrix I I ℂ) :
    supportBasis σ hσ (t • ρ) = t • supportBasis σ hσ ρ := by
  simp only [supportBasis, Matrix.mul_smul, Matrix.smul_mul]

theorem supportBasis_one {I : Type*} [Fintype I] [DecidableEq I]
    {σ : Matrix I I ℂ} (hσ : σ.IsHermitian) :
    supportBasis σ hσ (1 : Matrix I I ℂ) = 1 := by
  unfold supportBasis
  rw [Matrix.mul_one]
  exact Unitary.coe_star_mul_self hσ.eigenvectorUnitary

theorem supportBasis_affine {I : Type*} [Fintype I] [DecidableEq I]
    {σ : Matrix I I ℂ} (hσ : σ.IsHermitian) (c d : ℝ) :
    supportBasis σ hσ (c • σ + d • (1 : Matrix I I ℂ)) =
      Matrix.diagonal (fun i => (((c * hσ.eigenvalues i + d : ℝ)) : ℂ)) := by
  rw [supportBasis_add, supportBasis_smul, supportBasis_smul,
    supportBasis_self, supportBasis_one]
  ext i j
  by_cases hij : i = j
  · subst j
    simp [RCLike.real_smul_eq_coe_mul, RCLike.ofReal_eq_complex_ofReal,
      Matrix.diagonal_apply, Complex.ofReal_add, Complex.ofReal_mul]
  · simp [Matrix.diagonal_apply, Matrix.one_apply, hij]

theorem supportBasis_regularizedComparison {a b : ℕ}
    {σ : BipartiteMatrix a b} (hσ : σ.IsHermitian) (ε : ℝ) :
    supportBasis σ hσ (regularizedComparison ε σ) =
      Matrix.diagonal (fun i =>
        ((((1 - ε) * hσ.eigenvalues i + ε / ((a : ℝ) * (b : ℝ))) : ℝ) : ℂ)) := by
  rw [regularizedComparison_eq_smul_add_scalar]
  exact supportBasis_affine hσ _ _

theorem regularizedEigenvalue_pos {a b : ℕ} {σ : BipartiteMatrix a b}
    (hσ : σ.PosSemidef) (ha : 0 < a) (hb : 0 < b)
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) (i : Fin a × Fin b) :
    0 < (1 - ε) * hσ.1.eigenvalues i + ε / ((a : ℝ) * (b : ℝ)) := by
  have ha' : 0 < (a : ℝ) := by exact_mod_cast ha
  have hb' : 0 < (b : ℝ) := by exact_mod_cast hb
  exact add_pos_of_nonneg_of_pos
    (mul_nonneg (sub_nonneg.mpr hε1) (hσ.eigenvalues_nonneg i))
    (div_pos hε0 (mul_pos ha' hb'))

open Filter Topology

theorem supportBasis_eq_conjStarAlgAut_symm {I : Type*} [Fintype I] [DecidableEq I]
    {σ : Matrix I I ℂ} (hσ : σ.IsHermitian) (M : Matrix I I ℂ) :
    supportBasis σ hσ M =
      (Unitary.conjStarAlgAut ℝ (Matrix I I ℂ) hσ.eigenvectorUnitary).symm M := by
  simp only [supportBasis, Unitary.conjStarAlgAut_symm_apply,
    Unitary.coe_star, Matrix.star_eq_conjTranspose]

theorem supportBasis_mul {I : Type*} [Fintype I] [DecidableEq I]
    {σ : Matrix I I ℂ} (hσ : σ.IsHermitian) (M N : Matrix I I ℂ) :
    supportBasis σ hσ (M * N) = supportBasis σ hσ M * supportBasis σ hσ N := by
  simp only [supportBasis_eq_conjStarAlgAut_symm]
  exact (Unitary.conjStarAlgAut ℝ (Matrix I I ℂ) hσ.eigenvectorUnitary).symm.map_mul M N

theorem cfc_affine_eq {I : Type*} [Fintype I] [DecidableEq I]
    {σ : Matrix I I ℂ} (hσ : σ.IsHermitian) (c d : ℝ) :
    cfc (fun x : ℝ => c * x + d) σ = c • σ + d • (1 : Matrix I I ℂ) := by
  let F := Unitary.conjStarAlgAut ℝ (Matrix I I ℂ) hσ.eigenvectorUnitary
  have hF (M : Matrix I I ℂ) : F.symm M = supportBasis σ hσ M :=
    (supportBasis_eq_conjStarAlgAut_symm hσ M).symm
  have hs := TracePower.cfc_spectral (fun x : ℝ => c * x + d) hσ
  change cfc (fun x : ℝ => c * x + d) σ =
    F (Matrix.diagonal (fun i => ((c * hσ.eigenvalues i + d : ℝ) : ℂ))) at hs
  apply F.symm.injective
  calc
    F.symm (cfc (fun x : ℝ => c * x + d) σ) =
        Matrix.diagonal (fun i => ((c * hσ.eigenvalues i + d : ℝ) : ℂ)) := by
      rw [hs]
      exact F.symm_apply_apply _
    _ = F.symm (c • σ + d • (1 : Matrix I I ℂ)) := by
      rw [hF]
      exact (supportBasis_affine hσ c d).symm

theorem affine_rpow_spectral {I : Type*} [Fintype I] [DecidableEq I]
    {σ : Matrix I I ℂ} (hσ : σ.IsHermitian) (c d t : ℝ)
    (hA : (c • σ + d • (1 : Matrix I I ℂ)).PosSemidef) :
    CFC.rpow (c • σ + d • (1 : Matrix I I ℂ)) t =
      Unitary.conjStarAlgAut ℝ (Matrix I I ℂ) hσ.eigenvectorUnitary
        (Matrix.diagonal (fun i => (((c * hσ.eigenvalues i + d) ^ t : ℝ) : ℂ))) := by
  have hp : CFC.rpow (c • σ + d • (1 : Matrix I I ℂ)) t =
      cfc (fun x : ℝ => x ^ t) (c • σ + d • (1 : Matrix I I ℂ)) :=
    CFC.rpow_eq_cfc_real (A := Matrix I I ℂ)
      (a := c • σ + d • (1 : Matrix I I ℂ)) (y := t) hA.nonneg
  have hc := cfc_comp (fun x : ℝ => x ^ t) (fun x : ℝ => c * x + d) σ
    (Matrix.isHermitian_iff_isSelfAdjoint.mp hσ)
    ((σ.finite_real_spectrum.image (fun x : ℝ => c * x + d)).continuousOn _)
    (σ.finite_real_spectrum.continuousOn _)
  rw [hp, ← cfc_affine_eq hσ c d, ← hc]
  simpa only [Function.comp_apply] using
    TracePower.cfc_spectral ((fun x : ℝ => x ^ t) ∘ (fun x : ℝ => c * x + d)) hσ

theorem supportBasis_regularizedComparison_rpow {a b : ℕ}
    {σ : BipartiteMatrix a b} (hσ : σ.PosSemidef) (ha : 0 < a) (hb : 0 < b)
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) (t : ℝ) :
    supportBasis σ hσ.1 (CFC.rpow (regularizedComparison ε σ) t) =
      Matrix.diagonal (fun i =>
        ((((1 - ε) * hσ.1.eigenvalues i + ε / ((a : ℝ) * (b : ℝ))) ^ t : ℝ) : ℂ)) := by
  have hA := (regularizedComparison_posDef hσ ha hb hε0 hε1).posSemidef
  rw [regularizedComparison_eq_smul_add_scalar] at hA ⊢
  rw [affine_rpow_spectral hσ.1 _ _ _ hA, supportBasis_eq_conjStarAlgAut_symm]
  exact (Unitary.conjStarAlgAut ℝ (BipartiteMatrix a b) hσ.1.eigenvectorUnitary).symm_apply_apply _

theorem supportBasis_regularized_sandwich_entry {a b : ℕ}
    {ρ σ : BipartiteMatrix a b} (hσ : σ.PosSemidef) (ha : 0 < a) (hb : 0 < b)
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) (t : ℝ) (i j : Fin a × Fin b) :
    supportBasis σ hσ.1
      (CFC.rpow (regularizedComparison ε σ) t * ρ *
        CFC.rpow (regularizedComparison ε σ) t) i j =
      ((((1 - ε) * hσ.1.eigenvalues i + ε / ((a : ℝ) * (b : ℝ))) ^ t : ℝ) : ℂ) *
        supportBasis σ hσ.1 ρ i j *
          ((((1 - ε) * hσ.1.eigenvalues j + ε / ((a : ℝ) * (b : ℝ))) ^ t : ℝ) : ℂ) := by
  simp only [supportBasis_mul,
    supportBasis_regularizedComparison_rpow hσ ha hb hε0 hε1,
    Matrix.diagonal_mul, Matrix.mul_diagonal]

theorem supportBasis_rpow {I : Type*} [Fintype I] [DecidableEq I]
    {σ : Matrix I I ℂ} (hσ : σ.PosSemidef) (t : ℝ) :
    supportBasis σ hσ.1 (CFC.rpow σ t) =
      Matrix.diagonal (fun i => (((hσ.1.eigenvalues i) ^ t : ℝ) : ℂ)) := by
  have hp : CFC.rpow σ t = cfc (fun x : ℝ => x ^ t) σ :=
    CFC.rpow_eq_cfc_real (A := Matrix I I ℂ) (a := σ) (y := t) hσ.nonneg
  rw [hp, TracePower.cfc_spectral _ hσ.1, supportBasis_eq_conjStarAlgAut_symm]
  exact (Unitary.conjStarAlgAut ℝ (Matrix I I ℂ) hσ.1.eigenvectorUnitary).symm_apply_apply _

theorem supportBasis_sandwich_entry {I : Type*} [Fintype I] [DecidableEq I]
    {σ : Matrix I I ℂ} (hσ : σ.PosSemidef) (t : ℝ) (ρ : Matrix I I ℂ) (i j : I) :
    supportBasis σ hσ.1 (CFC.rpow σ t * ρ * CFC.rpow σ t) i j =
      (((hσ.1.eigenvalues i) ^ t : ℝ) : ℂ) * supportBasis σ hσ.1 ρ i j *
        (((hσ.1.eigenvalues j) ^ t : ℝ) : ℂ) := by
  simp only [supportBasis_mul, supportBasis_rpow hσ, Matrix.diagonal_mul,
    Matrix.mul_diagonal]

theorem supportBasis_reconstruct {I : Type*} [Fintype I] [DecidableEq I]
    {σ : Matrix I I ℂ} (hσ : σ.IsHermitian) (M : Matrix I I ℂ) :
    (hσ.eigenvectorUnitary : Matrix I I ℂ) * supportBasis σ hσ M *
      (hσ.eigenvectorUnitary : Matrix I I ℂ)ᴴ = M := by
  let U := hσ.eigenvectorUnitary
  have hU : (U : Matrix I I ℂ) * (U : Matrix I I ℂ)ᴴ = 1 :=
    Unitary.coe_mul_star_self U
  change (U : Matrix I I ℂ) * ((U : Matrix I I ℂ)ᴴ * M * (U : Matrix I I ℂ)) *
    (U : Matrix I I ℂ)ᴴ = M
  calc
    _ = ((U : Matrix I I ℂ) * (U : Matrix I I ℂ)ᴴ) * M *
        ((U : Matrix I I ℂ) * (U : Matrix I I ℂ)ᴴ) := by noncomm_ring
    _ = M := by rw [hU]; simp

theorem regularized_sandwich_tendsto {a b : ℕ} {ρ σ : BipartiteMatrix a b}
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) (hSupport : SupportLE ρ σ)
    (ha : 0 < a) (hb : 0 < b) (t : ℝ) :
    Filter.Tendsto
      (fun ε : ℝ => CFC.rpow (regularizedComparison ε σ) t * ρ *
        CFC.rpow (regularizedComparison ε σ) t)
      (nhdsWithin 0 (Set.Ioo 0 1))
      (nhds (CFC.rpow σ t * ρ * CFC.rpow σ t)) := by
  let l := nhdsWithin (0 : ℝ) (Set.Ioo 0 1)
  let X (ε : ℝ) := CFC.rpow (regularizedComparison ε σ) t * ρ *
    CFC.rpow (regularizedComparison ε σ) t
  let X0 := CFC.rpow σ t * ρ * CFC.rpow σ t
  have hB : Filter.Tendsto (fun ε => supportBasis σ hσ.1 (X ε)) l
      (nhds (supportBasis σ hσ.1 X0)) := by
    apply tendsto_pi_nhds.2
    intro i
    apply tendsto_pi_nhds.2
    intro j
    change Filter.Tendsto (fun ε => supportBasis σ hσ.1 (X ε) i j) l
      (nhds (supportBasis σ hσ.1 (CFC.rpow σ t * ρ * CFC.rpow σ t) i j))
    rw [supportBasis_sandwich_entry hσ]
    by_cases hi : hσ.1.eigenvalues i = 0
    · have hz := supportBasis_zero_row hσ.1 hSupport i j hi
      rw [hz, mul_zero, zero_mul]
      have he : (fun _ : ℝ => (0 : ℂ)) =ᶠ[l]
          (fun ε => supportBasis σ hσ.1 (X ε) i j) := by
        filter_upwards [self_mem_nhdsWithin] with ε hε
        change 0 = supportBasis σ hσ.1
          (CFC.rpow (regularizedComparison ε σ) t * ρ *
            CFC.rpow (regularizedComparison ε σ) t) i j
        rw [supportBasis_regularized_sandwich_entry hσ ha hb hε.1 hε.2.le, hz]
        simp
      exact Filter.Tendsto.congr' he tendsto_const_nhds
    · by_cases hj : hσ.1.eigenvalues j = 0
      · have hz := supportBasis_zero_column hρ hσ.1 hSupport i j hj
        rw [hz, mul_zero, zero_mul]
        have he : (fun _ : ℝ => (0 : ℂ)) =ᶠ[l]
            (fun ε => supportBasis σ hσ.1 (X ε) i j) := by
          filter_upwards [self_mem_nhdsWithin] with ε hε
          change 0 = supportBasis σ hσ.1
            (CFC.rpow (regularizedComparison ε σ) t * ρ *
              CFC.rpow (regularizedComparison ε σ) t) i j
          rw [supportBasis_regularized_sandwich_entry hσ ha hb hε.1 hε.2.le, hz]
          simp
        exact Filter.Tendsto.congr' he tendsto_const_nhds
      · have hm (k : Fin a × Fin b) :
            Filter.Tendsto
              (fun ε : ℝ => (1 - ε) * hσ.1.eigenvalues k +
                ε / ((a : ℝ) * (b : ℝ))) l (nhds (hσ.1.eigenvalues k)) := by
          have hc : Continuous (fun ε : ℝ => (1 - ε) * hσ.1.eigenvalues k +
              ε / ((a : ℝ) * (b : ℝ))) := by fun_prop
          simpa only [sub_zero, one_mul, zero_div, add_zero] using
            (hc.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
        have hci := (Complex.continuous_ofReal.tendsto ((hσ.1.eigenvalues i) ^ t)).comp
          ((hm i).rpow_const (Or.inl hi))
        have hcj := (Complex.continuous_ofReal.tendsto ((hσ.1.eigenvalues j) ^ t)).comp
          ((hm j).rpow_const (Or.inl hj))
        have hg := (hci.mul (tendsto_const_nhds (x := supportBasis σ hσ.1 ρ i j))).mul hcj
        apply Filter.Tendsto.congr' (h := hg)
        filter_upwards [self_mem_nhdsWithin] with ε hε
        exact (supportBasis_regularized_sandwich_entry hσ ha hb hε.1 hε.2.le t i j).symm
  have hR := (tendsto_const_nhds (x := (hσ.1.eigenvectorUnitary : BipartiteMatrix a b))).mul hB
  have hR' := hR.mul (tendsto_const_nhds
    (x := (hσ.1.eigenvectorUnitary : BipartiteMatrix a b)ᴴ))
  simpa only [supportBasis_reconstruct] using hR'

theorem regularized_sandwichedTrace_tendsto {a b : ℕ} {ρ σ : BipartiteMatrix a b}
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) (hSupport : SupportLE ρ σ)
    (ha : 0 < a) (hb : 0 < b) {α : ℝ} (hα : 0 < α) :
    Filter.Tendsto (fun ε : ℝ => sandwichedTrace α ρ (regularizedComparison ε σ))
      (nhdsWithin 0 (Set.Ioo 0 1)) (nhds (sandwichedTrace α ρ σ)) := by
  let t := (1 - α) / (2 * α)
  have hp (A : BipartiteMatrix a b) :
      (CFC.rpow A t * ρ * CFC.rpow A t).PosSemidef := by
    have hW : (CFC.rpow A t)ᴴ = CFC.rpow A t :=
      (Matrix.nonneg_iff_posSemidef.mp (CFC.rpow_nonneg (a := A) (y := t))).1
    simpa only [hW] using hρ.mul_mul_conjTranspose_same (CFC.rpow A t)
  exact PowerContinuity.tendsto_real_trace_rpow_of_posSemidef (hp σ)
    (Filter.Eventually.of_forall (fun ε => hp (regularizedComparison ε σ)))
    (regularized_sandwich_tendsto hρ hσ hSupport ha hb t) hα

theorem bell_separable_trace_bound {d : ℕ} {ρ σ : BipartiteMatrix d d}
    (hd : 0 < d) (hρ : ρ.PosSemidef) (hsep : IsSeparable d d σ)
    (hSupport : SupportLE ρ σ) {α : ℝ} (hα : 1 < α) :
    (d : ℝ) ^ (α - 1) * (bellOverlap d ρ) ^ α ≤ sandwichedTrace α ρ σ := by
  letI : NeBot (nhdsWithin (0 : ℝ) (Set.Ioo 0 1)) :=
    left_nhdsWithin_Ioo_neBot (by norm_num : (0 : ℝ) < 1)
  apply le_of_tendsto_of_tendsto tendsto_const_nhds
    (regularized_sandwichedTrace_tendsto hρ hsep.isDensity.1 hSupport hd hd (by linarith : 0 < α))
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact bell_fullRank_separable_trace_bound hd hρ
    (regularizedComparison_posDef hsep.isDensity.1 hd hd hε.1 hε.2.le)
    (regularizedComparison_isSeparable hsep hd hd hε.1.le hε.2.le) hα

theorem bell_separable_divergence_log_bound {d : ℕ} {ρ σ : BipartiteMatrix d d}
    (hd : 0 < d) (hρ : ρ.PosSemidef) (hF : 0 < bellOverlap d ρ)
    (hsep : IsSeparable d d σ) {α : ℝ} (hα : 1 < α) :
    ((logTwo (d : ℝ) + (α / (α - 1)) * logTwo (bellOverlap d ρ) : ℝ) : EReal) ≤
      sandwichedDivergence α ρ σ := by
  classical
  unfold sandwichedDivergence
  split_ifs with hSupport
  · apply EReal.coe_le_coe_iff.mpr
    have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
    have hα1 : 0 < α - 1 := sub_pos.mpr hα
    have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num : 1 < (2 : ℝ))
    have hpowD : 0 < (d : ℝ) ^ (α - 1) := Real.rpow_pos_of_pos hdR _
    have hpowF : 0 < (bellOverlap d ρ) ^ α := Real.rpow_pos_of_pos hF _
    have hbound := bell_separable_trace_bound hd hρ hsep hSupport hα
    have hlog := Real.log_le_log (mul_pos hpowD hpowF) hbound
    rw [Real.log_mul hpowD.ne' hpowF.ne', Real.log_rpow hdR (α - 1),
      Real.log_rpow hF α] at hlog
    calc
      logTwo (d : ℝ) + (α / (α - 1)) * logTwo (bellOverlap d ρ) =
          ((α - 1) * Real.log (d : ℝ) + α * Real.log (bellOverlap d ρ)) /
            ((α - 1) * Real.log 2) := by
        unfold logTwo
        field_simp [hα1.ne', h2.ne']
      _ ≤ Real.log (sandwichedTrace α ρ σ) / ((α - 1) * Real.log 2) :=
        (div_le_div_iff_of_pos_right (mul_pos hα1 h2)).mpr hlog
  · exact le_top

theorem bell_sandwichedEntanglement_log_bound {d : ℕ} {ρ : BipartiteMatrix d d}
    (hd : 0 < d) (hρ : ρ.PosSemidef) (hF : 0 < bellOverlap d ρ)
    {α : ℝ} (hα : 1 < α) :
    ((logTwo (d : ℝ) + (α / (α - 1)) * logTwo (bellOverlap d ρ) : ℝ) : EReal) ≤
      sandwichedEntanglement α d d ρ := by
  unfold sandwichedEntanglement
  refine le_sInf ?_
  rintro x ⟨σ, hσ, rfl⟩
  exact bell_separable_divergence_log_bound hd hρ hF hσ.2 hα

theorem bellOverlap_le_of_sandwichedEntanglement_le {d : ℕ}
    {ρ : BipartiteMatrix d d} (hd : 0 < d) (hρ : IsDensity ρ)
    {α e : ℝ} (hα : 1 < α)
    (hE : sandwichedEntanglement α d d ρ ≤ (e : EReal)) :
    bellOverlap d ρ ≤ min 1 (2 ^ (((α - 1) / α) * (e - logTwo (d : ℝ)))) := by
  refine le_min (bellOverlap_le_one hd hρ) ?_
  by_cases hF : 0 < bellOverlap d ρ
  · have hα0 : 0 < α := by linarith
    have hα1 : 0 < α - 1 := sub_pos.mpr hα
    have hlog : logTwo (d : ℝ) + (α / (α - 1)) * logTwo (bellOverlap d ρ) ≤ e :=
      EReal.coe_le_coe_iff.mp
        ((bell_sandwichedEntanglement_log_bound hd hρ.1 hF hα).trans hE)
    have hlogF : logTwo (bellOverlap d ρ) ≤ ((α - 1) / α) * (e - logTwo (d : ℝ)) := by
      apply (mul_le_mul_iff_of_pos_left (div_pos hα0 hα1)).mp
      have hcancel : (α / (α - 1)) * (((α - 1) / α) * (e - logTwo (d : ℝ))) =
          e - logTwo (d : ℝ) := by
        field_simp [hα0.ne', hα1.ne']
      rw [hcancel]
      linarith
    have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num : 1 < (2 : ℝ))
    have hlogF' : Real.log (bellOverlap d ρ) ≤
        (((α - 1) / α) * (e - logTwo (d : ℝ))) * Real.log 2 := by
      exact (div_le_iff₀ h2).mp hlogF
    calc
      bellOverlap d ρ = Real.exp (Real.log (bellOverlap d ρ)) := (Real.exp_log hF).symm
      _ ≤ Real.exp ((((α - 1) / α) * (e - logTwo (d : ℝ))) * Real.log 2) :=
        Real.exp_le_exp.mpr hlogF'
      _ = 2 ^ (((α - 1) / α) * (e - logTwo (d : ℝ))) := by
        rw [Real.rpow_def_of_pos (by norm_num : 0 < (2 : ℝ)), mul_comm]
  · exact (le_of_not_gt hF).trans (Real.rpow_nonneg (by norm_num : 0 ≤ (2 : ℝ)) _)

theorem sandwichedTrace_mono_input {I : Type*} [Fintype I] [DecidableEq I]
    {ρ τ : Matrix I I ℂ} (hρ : ρ.PosSemidef) (hτ : τ.PosSemidef)
    (hρτ : ρ ≤ τ) (σ : Matrix I I ℂ) {α : ℝ} (hα : 1 ≤ α) :
    sandwichedTrace α ρ σ ≤ sandwichedTrace α τ σ := by
  let W := CFC.rpow σ ((1 - α) / (2 * α))
  have hW : Wᴴ = W :=
    (Matrix.nonneg_iff_posSemidef.mp
      (CFC.rpow_nonneg (a := σ) (y := (1 - α) / (2 * α)))).1
  have hX : (W * ρ * W).PosSemidef := by
    simpa only [hW] using hρ.mul_mul_conjTranspose_same W
  have hY : (W * τ * W).PosSemidef := by
    simpa only [hW] using hτ.mul_mul_conjTranspose_same W
  have hgap : (W * τ * W - W * ρ * W).PosSemidef := by
    have h := (Matrix.le_iff.mp hρτ).mul_mul_conjTranspose_same W
    simpa only [hW, Matrix.mul_sub, Matrix.sub_mul] using h
  exact QuantumProver.MatrixTracePower.trace_rpow_mono_of_posSemidef_sub hX hY hgap hα

theorem sandwichedTrace_smul_input {I : Type*} [Fintype I] [DecidableEq I]
    {ρ : Matrix I I ℂ} (hρ : ρ.PosSemidef) (σ : Matrix I I ℂ)
    {c α : ℝ} (hc : 0 ≤ c) (hα : 1 ≤ α) :
    sandwichedTrace α (c • ρ) σ = c ^ α * sandwichedTrace α ρ σ := by
  let W := CFC.rpow σ ((1 - α) / (2 * α))
  have hW : Wᴴ = W :=
    (Matrix.nonneg_iff_posSemidef.mp
      (CFC.rpow_nonneg (a := σ) (y := (1 - α) / (2 * α)))).1
  have hX : (W * ρ * W).PosSemidef := by
    simpa only [hW] using hρ.mul_mul_conjTranspose_same W
  change (CFC.rpow (W * (c • ρ) * W) α).trace.re =
    c ^ α * (CFC.rpow (W * ρ * W) α).trace.re
  rw [Matrix.mul_smul, Matrix.smul_mul]
  exact QuantumProver.MatrixTracePower.trace_rpow_smul_nonneg hX hc hα

theorem sandwichedTrace_pinching_bound {I K : Type*} [Fintype I] [Fintype K]
    [DecidableEq I] {P : K → Matrix I I ℂ}
    (hP : QuantumProver.SuperchannelDiscrimination.Pinching.IsProjectionFamily P)
    {ρ : Matrix I I ℂ} (hρ : ρ.PosSemidef) (σ : Matrix I I ℂ)
    {α : ℝ} (hα : 1 ≤ α) :
    sandwichedTrace α ρ σ ≤ (Fintype.card K : ℝ) ^ α *
      sandwichedTrace α (QuantumProver.SuperchannelDiscrimination.Pinching.pinchingMap P ρ) σ := by
  have hpin := QuantumProver.SuperchannelDiscrimination.Pinching.pinchingMap_posSemidef P hρ
  have hcard : 0 ≤ (Fintype.card K : ℝ) := Nat.cast_nonneg _
  have horder := QuantumProver.SuperchannelDiscrimination.Pinching.le_card_smul_pinching hP hρ
  calc
    sandwichedTrace α ρ σ ≤ sandwichedTrace α
        ((Fintype.card K : ℝ) • QuantumProver.SuperchannelDiscrimination.Pinching.pinchingMap P ρ) σ :=
      sandwichedTrace_mono_input hρ (hpin.smul hcard) horder σ hα
    _ = (Fintype.card K : ℝ) ^ α *
        sandwichedTrace α (QuantumProver.SuperchannelDiscrimination.Pinching.pinchingMap P ρ) σ :=
      sandwichedTrace_smul_input hpin σ hcard hα

theorem sandwichedEntanglement_le_comparison {a b : ℕ}
    (ρ : BipartiteMatrix a b) {σ : BipartiteMatrix a b}
    (hσ : IsDensity σ) (hsep : IsSeparable a b σ) (α : ℝ) :
    sandwichedEntanglement α a b ρ ≤ sandwichedDivergence α ρ σ := by
  unfold sandwichedEntanglement
  exact sInf_le ⟨σ, ⟨hσ, hsep⟩, rfl⟩

theorem exists_separable_comparison_divergence_lt {a b : ℕ}
    (ρ : BipartiteMatrix a b) {α u : ℝ}
    (hE : sandwichedEntanglement α a b ρ < (u : EReal)) :
    ∃ σ : BipartiteMatrix a b, IsDensity σ ∧ IsSeparable a b σ ∧
      SupportLE ρ σ ∧ sandwichedDivergence α ρ σ < (u : EReal) := by
  classical
  unfold sandwichedEntanglement at hE
  obtain ⟨x, ⟨σ, hσ, rfl⟩, hD⟩ := sInf_lt_iff.mp hE
  refine ⟨σ, hσ.1, hσ.2, ?_, hD⟩
  by_contra hSupport
  simp only [sandwichedDivergence, if_neg hSupport] at hD
  exact not_top_lt hD

theorem sandwichedEntanglement_tensor_le_of_le {a b c d : ℕ}
    {ρ : BipartiteMatrix a b} {τ : BipartiteMatrix c d}
    (hρ : IsDensity ρ) (hτ : IsDensity τ) {α e f : ℝ} (hα : 1 < α)
    (hEρ : sandwichedEntanglement α a b ρ ≤ (e : EReal))
    (hEτ : sandwichedEntanglement α c d τ ≤ (f : EReal)) :
    sandwichedEntanglement α (a * c) (b * d) (tensorOnLabCut ρ τ) ≤
      ((e + f : ℝ) : EReal) := by
  apply EReal.le_of_forall_lt_iff_le.mp
  intro z hz
  have hzR : e + f < z := EReal.coe_lt_coe_iff.mp hz
  let ε : ℝ := (z - (e + f)) / 2
  have hε : 0 < ε := div_pos (sub_pos.mpr hzR) (by norm_num)
  have hρlt : sandwichedEntanglement α a b ρ < ((e + ε : ℝ) : EReal) :=
    hEρ.trans_lt (EReal.coe_lt_coe_iff.mpr (by linarith))
  have hτlt : sandwichedEntanglement α c d τ < ((f + ε : ℝ) : EReal) :=
    hEτ.trans_lt (EReal.coe_lt_coe_iff.mpr (by linarith))
  obtain ⟨σ, hσ, hsepσ, hSupportρ, hDρ⟩ :=
    exists_separable_comparison_divergence_lt ρ hρlt
  obtain ⟨υ, hυ, hsepυ, hSupportτ, hDτ⟩ :=
    exists_separable_comparison_divergence_lt τ hτlt
  have hQρ : 0 < sandwichedTrace α ρ σ :=
    lt_of_lt_of_le zero_lt_one (sandwichedTrace_ge_one hρ hσ hSupportρ hα)
  have hQτ : 0 < sandwichedTrace α τ υ :=
    lt_of_lt_of_le zero_lt_one (sandwichedTrace_ge_one hτ hυ hSupportτ hα)
  have hTensor := QuantumProver.AmplitudeDamping.TensorPower.sandwichedDivergence_tensorOnLabCut_of_support
    hρ hσ hτ hυ hSupportρ hSupportτ α hQρ hQτ
  calc
    _ ≤ sandwichedDivergence α (tensorOnLabCut ρ τ) (tensorOnLabCut σ υ) :=
      sandwichedEntanglement_le_comparison _ (hσ.tensorOnLabCut hυ)
        (hsepσ.tensorOnLabCut hsepυ) α
    _ = sandwichedDivergence α ρ σ + sandwichedDivergence α τ υ := hTensor
    _ ≤ ((e + ε : ℝ) : EReal) + ((f + ε : ℝ) : EReal) :=
      (EReal.add_lt_add hDρ hDτ).le
    _ = (z : EReal) := by
      rw [← EReal.coe_add]
      congr 1
      dsimp only [ε]
      ring

theorem IsDensity.laboratory_dimensions_pos {a b : ℕ} {ρ : BipartiteMatrix a b}
    (hρ : IsDensity ρ) : 0 < a ∧ 0 < b := by
  constructor
  · by_contra ha
    have ha0 : a = 0 := Nat.eq_zero_of_not_pos ha
    subst a
    have ht := hρ.2
    simp [Matrix.trace] at ht
  · by_contra hb
    have hb0 : b = 0 := Nat.eq_zero_of_not_pos hb
    subst b
    have ht := hρ.2
    simp [Matrix.trace] at ht

theorem sandwichedEntanglement_ne_top {a b : ℕ} {ρ : BipartiteMatrix a b}
    (hρ : IsDensity ρ) (α : ℝ) : sandwichedEntanglement α a b ρ ≠ ⊤ := by
  classical
  obtain ⟨ha, hb⟩ := hρ.laboratory_dimensions_pos
  let σ := maximallyMixed a ⊗ₖ maximallyMixed b
  have hsep : IsSeparable a b σ :=
    product_isSeparable (maximallyMixed_isDensity ha) (maximallyMixed_isDensity hb)
  have hSupport : SupportLE ρ σ :=
    supportLE_of_posDef ρ ((maximallyMixed_posDef ha).kronecker (maximallyMixed_posDef hb))
  have hE := sandwichedEntanglement_le_comparison ρ hsep.isDensity hsep α
  simp only [sandwichedDivergence, if_pos hSupport] at hE
  exact ne_top_of_le_ne_top (EReal.coe_ne_top _) hE

theorem sandwichedEntanglement_tensor_subadditive {a b c d : ℕ}
    {ρ : BipartiteMatrix a b} {τ : BipartiteMatrix c d}
    (hρ : IsDensity ρ) (hτ : IsDensity τ) {α : ℝ} (hα : 1 < α) :
    sandwichedEntanglement α (a * c) (b * d) (tensorOnLabCut ρ τ) ≤
      sandwichedEntanglement α a b ρ + sandwichedEntanglement α c d τ := by
  have hρbot : sandwichedEntanglement α a b ρ ≠ ⊥ :=
    ne_bot_of_le_ne_bot (by exact EReal.zero_ne_bot) (sandwichedEntanglement_nonneg hρ hα)
  have hτbot : sandwichedEntanglement α c d τ ≠ ⊥ :=
    ne_bot_of_le_ne_bot (by exact EReal.zero_ne_bot) (sandwichedEntanglement_nonneg hτ hα)
  have hρeq := EReal.coe_toReal (sandwichedEntanglement_ne_top hρ α) hρbot
  have hτeq := EReal.coe_toReal (sandwichedEntanglement_ne_top hτ α) hτbot
  have h := sandwichedEntanglement_tensor_le_of_le hρ hτ hα hρeq.symm.le hτeq.symm.le
  simpa only [EReal.coe_add, hρeq, hτeq] using h

theorem scalarProduct_isDensity : IsDensity (1 : BipartiteMatrix 1 1) := by
  refine ⟨Matrix.PosSemidef.one, ?_⟩
  simp [Matrix.trace]

theorem scalarProduct_isSeparable : IsSeparable 1 1 (1 : BipartiteMatrix 1 1) := by
  have hlocal : IsDensity (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
    refine ⟨Matrix.PosSemidef.one, ?_⟩
    simp [Matrix.trace]
  simpa only [Matrix.one_kronecker_one] using product_isSeparable hlocal hlocal

theorem scalarProduct_sandwichedEntanglement {α : ℝ} (hα : 1 < α) :
    sandwichedEntanglement α 1 1 (1 : BipartiteMatrix 1 1) = 0 := by
  apply le_antisymm
  · have h := sandwichedEntanglement_le_comparison
      (1 : BipartiteMatrix 1 1) scalarProduct_isDensity scalarProduct_isSeparable α
    have hSupport : SupportLE (1 : BipartiteMatrix 1 1) 1 := le_refl _
    simpa [sandwichedDivergence, hSupport, sandwichedTrace, Matrix.trace] using h
  · exact sandwichedEntanglement_nonneg scalarProduct_isDensity hα

def tensorCopyDim (a : ℕ) : ℕ → ℕ
  | 0 => 1
  | n + 1 => tensorCopyDim a n * a

theorem tensorCopyDim_eq_pow (a n : ℕ) : tensorCopyDim a n = a ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [tensorCopyDim, ih, Nat.pow_succ]

def tensorCopiesOnLabCut {a b : ℕ} (ρ : BipartiteMatrix a b) :
    (n : ℕ) → BipartiteMatrix (tensorCopyDim a n) (tensorCopyDim b n)
  | 0 => 1
  | n + 1 => tensorOnLabCut (tensorCopiesOnLabCut ρ n) ρ

theorem tensorCopiesOnLabCut_isDensity {a b : ℕ} {ρ : BipartiteMatrix a b}
    (hρ : IsDensity ρ) (n : ℕ) : IsDensity (tensorCopiesOnLabCut ρ n) := by
  induction n with
  | zero => exact scalarProduct_isDensity
  | succ n ih => exact ih.tensorOnLabCut hρ

theorem tensorCopiesOnLabCut_entanglement_le {a b : ℕ} {ρ : BipartiteMatrix a b}
    (hρ : IsDensity ρ) {α e : ℝ} (hα : 1 < α)
    (hE : sandwichedEntanglement α a b ρ ≤ (e : EReal)) (n : ℕ) :
    sandwichedEntanglement α (tensorCopyDim a n) (tensorCopyDim b n)
      (tensorCopiesOnLabCut ρ n) ≤ (((n : ℝ) * e : ℝ) : EReal) := by
  induction n with
  | zero =>
    rw [Nat.cast_zero, zero_mul, EReal.coe_zero]
    exact (scalarProduct_sandwichedEntanglement hα).le
  | succ n ih =>
    have h := sandwichedEntanglement_tensor_le_of_le
      (tensorCopiesOnLabCut_isDensity hρ n) hρ hα ih hE
    simpa only [tensorCopiesOnLabCut, tensorCopyDim, Nat.cast_add, Nat.cast_one,
      add_mul, one_mul] using h

theorem tensorCopiesOnLabCut_bellOverlap {d : ℕ} {ρ : BipartiteMatrix d d}
    (hρ : IsDensity ρ) (n : ℕ) :
    bellOverlap (tensorCopyDim d n) (tensorCopiesOnLabCut ρ n) = (bellOverlap d ρ) ^ n := by
  induction n with
  | zero =>
    change bellOverlap 1 (1 : BipartiteMatrix 1 1) = 1
    simp only [bellOverlap, Matrix.mul_one,
      bellProjector_trace (by norm_num : 0 < (1 : ℕ)), Complex.one_re]
  | succ n ih =>
    change bellOverlap (tensorCopyDim d n * d)
      (tensorOnLabCut (tensorCopiesOnLabCut ρ n) ρ) = _
    rw [bellOverlap_tensorOnLabCut (tensorCopiesOnLabCut_isDensity hρ n).1 hρ.1,
      ih, pow_succ]

theorem logTwo_tensorCopyDim (d n : ℕ) :
    logTwo (tensorCopyDim d n : ℝ) = (n : ℝ) * logTwo (d : ℝ) := by
  rw [tensorCopyDim_eq_pow, Nat.cast_pow]
  unfold logTwo
  rw [Real.log_pow]
  ring

theorem tensorCopiesOnLabCut_bell_log_bound {d : ℕ} {ρ : BipartiteMatrix d d}
    (hρ : IsDensity ρ) (hF : 0 < bellOverlap d ρ) {α : ℝ} (hα : 1 < α) (n : ℕ) :
    (((n : ℝ) * (logTwo (d : ℝ) + (α / (α - 1)) * logTwo (bellOverlap d ρ)) : ℝ) : EReal) ≤
      sandwichedEntanglement α (tensorCopyDim d n) (tensorCopyDim d n)
        (tensorCopiesOnLabCut ρ n) := by
  have hcopies := tensorCopiesOnLabCut_isDensity hρ n
  have hFn : 0 < bellOverlap (tensorCopyDim d n) (tensorCopiesOnLabCut ρ n) := by
    rw [tensorCopiesOnLabCut_bellOverlap hρ n]
    exact pow_pos hF n
  have ht := bell_sandwichedEntanglement_log_bound
    hcopies.laboratory_dimensions_pos.1 hcopies.1 hFn hα
  have hlogpow : logTwo ((bellOverlap d ρ) ^ n) = (n : ℝ) * logTwo (bellOverlap d ρ) := by
    unfold logTwo
    rw [Real.log_pow]
    ring
  rw [tensorCopiesOnLabCut_bellOverlap hρ n, logTwo_tensorCopyDim, hlogpow] at ht
  convert ht using 1 <;> congr 1 <;> ring

theorem supportLE_of_loewner {I : Type*} [Fintype I] [DecidableEq I]
    {ρ σ : Matrix I I ℂ} (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef)
    (hρσ : ρ ≤ σ) : SupportLE ρ σ := by
  apply (QuantumProver.SandwichedDPI.supportLE_iff_kernel hρ.1 hσ.1).mpr
  intro v hv
  apply hρ.dotProduct_mulVec_zero_iff.mp
  have hpos : 0 ≤ star v ⬝ᵥ ρ *ᵥ v := hρ.dotProduct_mulVec_nonneg v
  have hneg : 0 ≤ -(star v ⬝ᵥ ρ *ᵥ v) := by
    simpa only [Matrix.sub_mulVec, hv, dotProduct_sub, dotProduct_zero, zero_sub,
      dotProduct_neg] using
      (Matrix.le_iff.mp hρσ).dotProduct_mulVec_nonneg v
  exact le_antisymm (neg_nonneg.mp hneg) hpos

theorem regularizedComparison_mono {a b : ℕ} {σ τ : BipartiteMatrix a b}
    (hστ : σ ≤ τ) {ε : ℝ} (hε : ε ≤ 1) :
    regularizedComparison ε σ ≤ regularizedComparison ε τ := by
  apply Matrix.le_iff.mpr
  have heq : regularizedComparison ε τ - regularizedComparison ε σ =
      (1 - ε) • (τ - σ) := by
    unfold regularizedComparison
    module
  rw [heq]
  exact (Matrix.le_iff.mp hστ).smul (sub_nonneg.mpr hε)

theorem sandwichedTrace_antitone_comparison_of_support {a b : ℕ}
    {ρ σ τ : BipartiteMatrix a b} (hρ : ρ.PosSemidef)
    (hσ : σ.PosSemidef) (hτ : τ.PosSemidef) (hστ : σ ≤ τ)
    (hSupport : SupportLE ρ σ) (ha : 0 < a) (hb : 0 < b)
    {α : ℝ} (hα : 1 ≤ α) : sandwichedTrace α ρ τ ≤ sandwichedTrace α ρ σ := by
  have hSupportτ : SupportLE ρ τ := le_trans hSupport (supportLE_of_loewner hσ hτ hστ)
  have hα0 : 0 < α := lt_of_lt_of_le zero_lt_one hα
  letI : NeBot (nhdsWithin (0 : ℝ) (Set.Ioo 0 1)) :=
    left_nhdsWithin_Ioo_neBot (by norm_num : (0 : ℝ) < 1)
  apply le_of_tendsto_of_tendsto
    (regularized_sandwichedTrace_tendsto hρ hτ hSupportτ ha hb hα0)
    (regularized_sandwichedTrace_tendsto hρ hσ hSupport ha hb hα0)
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact sandwichedTrace_antitone_comparison hρ
    (regularizedComparison_posDef hσ ha hb hε.1 hε.2.le)
    (regularizedComparison_mono hστ hε.2.le) hα

theorem rpow_smul_positive {I : Type*} [Fintype I] [DecidableEq I]
    {σ : Matrix I I ℂ} (hσ : σ.PosSemidef) {c : ℝ} (hc : 0 < c) (t : ℝ) :
    CFC.rpow (c • σ) t = (c ^ t) • CFC.rpow σ t := by
  have hcσ : (c • σ).PosSemidef := hσ.smul hc.le
  calc
    CFC.rpow (c • σ) t = cfc (fun x : ℝ => x ^ t) (c • σ) :=
      CFC.rpow_eq_cfc_real hcσ.nonneg
    _ = cfc (fun x : ℝ => (c * x) ^ t) σ :=
      (cfc_comp_const_mul c (fun x : ℝ => x ^ t) σ
        ((σ.finite_real_spectrum.image (fun x : ℝ => c * x)).continuousOn _) hσ.1).symm
    _ = cfc (fun x : ℝ => c ^ t * x ^ t) σ := by
      apply cfc_congr
      intro x hx
      rw [hσ.1.spectrum_real_eq_range_eigenvalues] at hx
      obtain ⟨i, rfl⟩ := hx
      exact Real.mul_rpow hc.le (hσ.eigenvalues_nonneg i)
    _ = (c ^ t) • cfc (fun x : ℝ => x ^ t) σ :=
      cfc_const_mul (c ^ t) (fun x : ℝ => x ^ t) σ (σ.finite_real_spectrum.continuousOn _)
    _ = (c ^ t) • CFC.rpow σ t := by
      exact congrArg (fun X : Matrix I I ℂ => (c ^ t) • X)
        (CFC.rpow_eq_cfc_real (A := Matrix I I ℂ) (a := σ) (y := t) hσ.nonneg).symm

theorem sandwichedTrace_smul_comparison {I : Type*} [Fintype I] [DecidableEq I]
    {ρ σ : Matrix I I ℂ} (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef)
    {c α : ℝ} (hc : 0 < c) (hα : 1 ≤ α) :
    sandwichedTrace α ρ (c • σ) = c ^ (1 - α) * sandwichedTrace α ρ σ := by
  let t := (1 - α) / (2 * α)
  let W := CFC.rpow σ t
  have hW : Wᴴ = W :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.rpow_nonneg (a := σ) (y := t))).1
  have hX : (W * ρ * W).PosSemidef := by
    simpa only [hW] using hρ.mul_mul_conjTranspose_same W
  have hα0 : 0 < α := lt_of_lt_of_le zero_lt_one hα
  have hexp : (t + t) * α = 1 - α := by
    dsimp only [t]
    field_simp [hα0.ne']
    <;> ring
  have hscale : ((c ^ t) * (c ^ t)) ^ α = c ^ (1 - α) := by
    rw [← Real.rpow_add hc t t, ← Real.rpow_mul hc.le, hexp]
  change (CFC.rpow (CFC.rpow (c • σ) t * ρ * CFC.rpow (c • σ) t) α).trace.re =
    c ^ (1 - α) * (CFC.rpow (W * ρ * W) α).trace.re
  rw [rpow_smul_positive hσ hc t]
  change (CFC.rpow (((c ^ t) • W) * ρ * ((c ^ t) • W)) α).trace.re = _
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [QuantumProver.MatrixTracePower.trace_rpow_smul_nonneg hX
      (mul_nonneg (Real.rpow_nonneg hc.le t) (Real.rpow_nonneg hc.le t)) hα, hscale]

theorem supportLE_smul_comparison_iff {I : Type*} [Fintype I] [DecidableEq I]
    {ρ σ : Matrix I I ℂ} (hρ : ρ.IsHermitian) (hσ : σ.PosSemidef)
    {c : ℝ} (hc : 0 < c) : SupportLE ρ (c • σ) ↔ SupportLE ρ σ := by
  rw [QuantumProver.SandwichedDPI.supportLE_iff_kernel hρ (hσ.smul hc.le).1,
    QuantumProver.SandwichedDPI.supportLE_iff_kernel hρ hσ.1]
  simp only [Matrix.smul_mulVec, smul_eq_zero, hc.ne', false_or]

theorem sandwichedDivergence_comparison_order {a b : ℕ}
    {ρ σ τ : BipartiteMatrix a b} (hρ : IsDensity ρ)
    (hσ : IsDensity σ) (hτ : IsDensity τ)
    (hSupport : SupportLE ρ σ) {c α : ℝ} (hc : 0 < c)
    (hστ : σ ≤ c • τ) (hα : 1 < α) :
    sandwichedDivergence α ρ τ ≤ sandwichedDivergence α ρ σ + (logTwo c : EReal) := by
  classical
  have hSupportC : SupportLE ρ (c • τ) :=
    le_trans hSupport (supportLE_of_loewner hσ.1 (hτ.1.smul hc.le) hστ)
  have hSupportτ := (supportLE_smul_comparison_iff hρ.1.1 hτ.1 hc).mp hSupportC
  obtain ⟨ha, hb⟩ := hρ.laboratory_dimensions_pos
  have htrace := sandwichedTrace_antitone_comparison_of_support
    hρ.1 hσ.1 (hτ.1.smul hc.le) hστ hSupport ha hb hα.le
  rw [sandwichedTrace_smul_comparison hρ.1 hτ.1 hc hα.le] at htrace
  have hQτ : 0 < sandwichedTrace α ρ τ :=
    lt_of_lt_of_le zero_lt_one (sandwichedTrace_ge_one hρ hτ hSupportτ hα)
  have hlog := Real.log_le_log (mul_pos (Real.rpow_pos_of_pos hc (1 - α)) hQτ) htrace
  rw [Real.log_mul (Real.rpow_pos_of_pos hc (1 - α)).ne' hQτ.ne',
    Real.log_rpow hc (1 - α)] at hlog
  have hα1 : 0 < α - 1 := sub_pos.mpr hα
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num : 1 < (2 : ℝ))
  have heq : (Real.log (sandwichedTrace α ρ σ) / ((α - 1) * Real.log 2) + logTwo c) *
      ((α - 1) * Real.log 2) = Real.log (sandwichedTrace α ρ σ) + (α - 1) * Real.log c := by
    unfold logTwo
    field_simp [hα1.ne', h2.ne']
    <;> ring
  simp only [sandwichedDivergence, if_pos hSupportτ, if_pos hSupport, ← EReal.coe_add]
  apply EReal.coe_le_coe_iff.mpr
  apply (div_le_iff₀ (mul_pos hα1 h2)).mpr
  rw [heq]
  linarith

end QuantumProver.AmplitudeDamping.FiniteModel

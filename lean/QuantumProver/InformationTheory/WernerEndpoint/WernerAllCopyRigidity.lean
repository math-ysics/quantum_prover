import QuantumProver.InformationTheory.WernerEndpoint.WernerCompanionRigidity

set_option autoImplicit false

noncomputable section

namespace QuantumProver.WernerEndpoint

open scoped BigOperators ComplexOrder Matrix Kronecker

def slaterProductInput {d : ℕ} :
    (n : ℕ) → (Fin n → Edge d → ℂ) → EdgePower d n → ℂ
  | 0, _, _ => 1
  | n + 1, f, xy => f 0 xy.1 * slaterProductInput n (fun i => f i.succ) xy.2

def NormalizedSlaterFactors {d n : ℕ} (f : Fin n → Edge d → ℂ) : Prop :=
  ∀ i, vectorNormSq (f i) = 1 ∧ IsNormalizedSlater (f i)

def IsSlaterTensorProduct (d n : ℕ) (u : EdgePower d n → ℂ) : Prop :=
  ∃ z : ℂ, Complex.normSq z = 1 ∧
    ∃ f : Fin n → Edge d → ℂ, NormalizedSlaterFactors f ∧
      u = z • slaterProductInput n f

theorem slaterProductInput_normSq {d n : ℕ} (f : Fin n → Edge d → ℂ)
    (hf : NormalizedSlaterFactors f) : vectorNormSq (slaterProductInput n f) = 1 := by
  induction n with
  | zero => simp [slaterProductInput, vectorNormSq]
  | succ n ih =>
      change vectorNormSq (fun xy : Edge d × EdgePower d n =>
        f 0 xy.1 * slaterProductInput n (fun i => f i.succ) xy.2) = 1
      rw [product_vectorNormSq, (hf 0).1, ih (fun i => f i.succ) (fun i => hf i.succ)]
      norm_num

theorem IsSlaterTensorProduct.normSq {d n : ℕ} {u : EdgePower d n → ℂ}
    (hu : IsSlaterTensorProduct d n u) : vectorNormSq u = 1 := by
  rcases hu with ⟨z, hz, f, hf, rfl⟩
  rw [matrix_vectorNormSq_scalar, hz, slaterProductInput_normSq f hf, one_mul]

theorem antisymmetricPower_slaterProduct_purity {d n : ℕ}
    (f : Fin n → Edge d → ℂ) (hf : NormalizedSlaterFactors f) :
    purity ((antisymmetricPowerStinespring d n).apply (pureDensity (slaterProductInput n f))) =
      (1 / 2 : ℝ) ^ n := by
  induction n with
  | zero =>
      rw [antisymmetricPower_zero_output _ _ (slaterProductInput_normSq f hf)]
      simp [purity]
  | succ n ih =>
      change purity (((antisymmetricStinespring d).tensor (antisymmetricPowerStinespring d n)).apply
        (pureDensity (fun xy => f 0 xy.1 * slaterProductInput n (fun i => f i.succ) xy.2))) = _
      rw [Stinespring.tensor_product_purity, ← antisymmetricChannel_eq_stinespring,
        (antisymmetric_purity_half_iff_slater (f 0) (hf 0).1).mpr (hf 0).2,
        ih (fun i => f i.succ) (fun i => hf i.succ)]
      rw [pow_succ, mul_comm]

theorem IsSlaterTensorProduct.purity {d n : ℕ} {u : EdgePower d n → ℂ}
    (hu : IsSlaterTensorProduct d n u) :
    purity ((antisymmetricPowerStinespring d n).apply (pureDensity u)) = (1 / 2 : ℝ) ^ n := by
  rcases hu with ⟨z, hz, f, hf, rfl⟩
  rw [Stinespring.pure_purity_scalar, hz, one_pow, one_mul,
    antisymmetricPower_slaterProduct_purity f hf]

theorem antisymmetricPower_maximizer_isSlaterTensorProduct (d : ℕ) (hd : 2 ≤ d)
    (n : ℕ) (u : EdgePower d n → ℂ) (hu : vectorNormSq u = 1)
    (hmax : purity ((antisymmetricPowerStinespring d n).apply (pureDensity u)) =
      (1 / 2 : ℝ) ^ n) : IsSlaterTensorProduct d n u := by
  induction n with
  | zero =>
      refine ⟨u (), ?_, (fun i => Fin.elim0 i), ?_, ?_⟩
      · simpa [vectorNormSq] using hu
      · intro i
        exact Fin.elim0 i
      · funext x
        cases x
        simp [slaterProductInput]
  | succ n ih =>
      have hmax' :
          purity (((antisymmetricStinespring d).tensor (antisymmetricPowerStinespring d n)).apply
            (pureDensity u)) = ((1 / 2 : ℝ) ^ n) / 2 := by
        simpa [antisymmetricPowerStinespring, pow_succ, div_eq_mul_inv, mul_comm] using hmax
      have hβ : 0 < (1 / 2 : ℝ) ^ n := pow_pos (by norm_num) n
      obtain ⟨x, y, hx, hy, hslater, hpure, hproduct⟩ :=
        (antisymmetric_companion_maximizer_iff_product hd (antisymmetricPowerStinespring d n)
          ((1 / 2 : ℝ) ^ n) hβ (antisymmetricPower_purity_upper d hd n) u hu).mp hmax'
      obtain ⟨z, hz, f, hf, hyf⟩ := ih y hy hpure
      let g : Fin (n + 1) → Edge d → ℂ := Fin.cons x f
      refine ⟨z, hz, g, ?_, ?_⟩
      · intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · simpa [g] using And.intro hx hslater
        · simpa [g] using hf j
      · have htail : (fun i : Fin n => g i.succ) = f := by
          funext i
          simp [g]
        funext xy
        change u xy = z * (g 0 xy.1 * slaterProductInput n (fun i => g i.succ) xy.2)
        rw [hproduct xy, hyf, htail]
        simp only [Pi.smul_apply, smul_eq_mul]
        simp only [g, Fin.cons_zero]
        ring

theorem antisymmetricPower_maximal_purity_iff_slaterTensorProduct (d : ℕ) (hd : 2 ≤ d)
    (n : ℕ) (u : EdgePower d n → ℂ) (hu : vectorNormSq u = 1) :
    purity ((antisymmetricPowerStinespring d n).apply (pureDensity u)) = (1 / 2 : ℝ) ^ n ↔
      IsSlaterTensorProduct d n u := by
  constructor
  · exact antisymmetricPower_maximizer_isSlaterTensorProduct d hd n u hu
  · exact IsSlaterTensorProduct.purity

theorem antisymmetricPower_maximal_purity_iff_actual_product (d : ℕ) (hd : 2 ≤ d)
    (n : ℕ) (u : EdgePower d n → ℂ) (hu : vectorNormSq u = 1) :
    purity ((antisymmetricPowerStinespring d n).apply (pureDensity u)) = (1 / 2 : ℝ) ^ n ↔
      ∃ z : ℂ, Complex.normSq z = 1 ∧
        ∃ f : Fin n → Edge d → ℂ,
          (∀ i, vectorNormSq (f i) = 1 ∧ IsNormalizedSlater (f i)) ∧
            ∀ word, u word = z * slaterProductInput n f word := by
  rw [antisymmetricPower_maximal_purity_iff_slaterTensorProduct d hd n u hu]
  constructor
  · rintro ⟨z, hz, f, hf, huf⟩
    refine ⟨z, hz, f, hf, ?_⟩
    intro word
    simpa only [Pi.smul_apply, smul_eq_mul] using congrFun huf word
  · rintro ⟨z, hz, f, hf, huf⟩
    refine ⟨z, hz, f, hf, ?_⟩
    funext word
    exact huf word

def physicalSlaterProductAmplitude {d : ℕ} : (n : ℕ) → (Fin n → Edge d → ℂ) →
    Matrix (PhysicalPower d n) (PhysicalPower d n) ℂ
  | 0, _ => fun _ _ => 1
  | n + 1, f =>
      (antisymmetricStinespring d).amplitudes (f 0) ⊗ₖ
        physicalSlaterProductAmplitude n (fun i => f i.succ)

def physicalSlaterProductVector {d n : ℕ} (f : Fin n → Edge d → ℂ) :
    PhysicalPower d n × PhysicalPower d n → ℂ :=
  fun ab => physicalSlaterProductAmplitude n f ab.1 ab.2

def IsPhysicalSlaterTensorProduct (d n : ℕ)
    (ψ : PhysicalPower d n × PhysicalPower d n → ℂ) : Prop :=
  ∃ z : ℂ, Complex.normSq z = 1 ∧
    ∃ f : Fin n → Edge d → ℂ, NormalizedSlaterFactors f ∧
      ψ = z • physicalSlaterProductVector f

theorem antisymmetricPower_slaterProduct_amplitudes {d n : ℕ}
    (f : Fin n → Edge d → ℂ) :
    (antisymmetricPowerStinespring d n).amplitudes (slaterProductInput n f) =
      physicalSlaterProductAmplitude n f := by
  induction n with
  | zero =>
      ext a b
      cases a
      cases b
      simp [antisymmetricPowerStinespring, Stinespring.amplitudes,
        slaterProductInput, physicalSlaterProductAmplitude]
  | succ n ih =>
      change ((antisymmetricStinespring d).tensor (antisymmetricPowerStinespring d n)).amplitudes
        (fun xy => f 0 xy.1 * slaterProductInput n (fun i => f i.succ) xy.2) = _
      rw [Stinespring.tensor_product_amplitudes, ih (fun i => f i.succ)]
      rfl

theorem physicalTensorIsometry_slaterProduct {d n : ℕ}
    (f : Fin n → Edge d → ℂ) :
    (physicalTensorIsometry d n).mulVec (slaterProductInput n f) =
      physicalSlaterProductVector f := by
  rw [physicalTensorIsometry_mulVec_eq_amplitudes, antisymmetricPower_slaterProduct_amplitudes]
  rfl

theorem physicalSlaterProductVector_normSq {d n : ℕ} (f : Fin n → Edge d → ℂ)
    (hf : NormalizedSlaterFactors f) : vectorNormSq (physicalSlaterProductVector f) = 1 := by
  rw [← physicalTensorIsometry_slaterProduct, physicalTensorIsometry_mulVec_eq_amplitudes,
    Stinespring.amplitudes_normSq, slaterProductInput_normSq f hf]

theorem physicalSlaterProductVector_support {d n : ℕ} (f : Fin n → Edge d → ℂ) :
    HasAntisymmetricSupport d n (fun a b => physicalSlaterProductVector f (a, b)) := by
  apply (physicalTensorIsometry_range_iff_support d n _).mp
  exact ⟨slaterProductInput n f, physicalTensorIsometry_slaterProduct f⟩

theorem physicalSlaterProductVector_purity {d n : ℕ} (f : Fin n → Edge d → ℂ)
    (hf : NormalizedSlaterFactors f) :
    purity (partialTraceLeft (pureDensity (physicalSlaterProductVector f))) = (1 / 2 : ℝ) ^ n := by
  rw [← physicalTensorIsometry_slaterProduct, physicalTensor_partialTrace_forward,
    antisymmetricPower_slaterProduct_purity f hf]

theorem IsPhysicalSlaterTensorProduct.purity {d n : ℕ}
    {ψ : PhysicalPower d n × PhysicalPower d n → ℂ}
    (hψ : IsPhysicalSlaterTensorProduct d n ψ) :
    purity (partialTraceLeft (pureDensity ψ)) = (1 / 2 : ℝ) ^ n := by
  rcases hψ with ⟨z, hz, f, hf, rfl⟩
  rw [matrix_pureDensity_scalar, hz]
  simp only [Complex.ofReal_one, one_smul]
  exact physicalSlaterProductVector_purity f hf

theorem antisymmetric_physical_maximal_purity_iff_slaterTensorProduct (d : ℕ) (hd : 2 ≤ d)
    (n : ℕ) (ψ : PhysicalPower d n × PhysicalPower d n → ℂ)
    (hunit : vectorNormSq ψ = 1)
    (hψ : HasAntisymmetricSupport d n (fun a b => ψ (a, b))) :
    purity (partialTraceLeft (pureDensity ψ)) = (1 / 2 : ℝ) ^ n ↔
      IsPhysicalSlaterTensorProduct d n ψ := by
  constructor
  · intro hmax
    obtain ⟨u, hu, hreconstruct, houtput⟩ := physical_normalized_preimage d n ψ hunit hψ
    have hmax' : purity ((antisymmetricPowerStinespring d n).apply (pureDensity u)) =
        (1 / 2 : ℝ) ^ n := by
      rw [← houtput]
      exact hmax
    obtain ⟨z, hz, f, hf, huf⟩ :=
      antisymmetricPower_maximizer_isSlaterTensorProduct d hd n u hu hmax'
    refine ⟨z, hz, f, hf, ?_⟩
    rw [← hreconstruct, huf, Matrix.mulVec_smul, physicalTensorIsometry_slaterProduct]
  · exact IsPhysicalSlaterTensorProduct.purity

end QuantumProver.WernerEndpoint

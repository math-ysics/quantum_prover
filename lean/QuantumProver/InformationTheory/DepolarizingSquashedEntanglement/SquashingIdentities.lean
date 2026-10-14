import QuantumProver.InformationTheory.DepolarizingSquashedEntanglement.Definitions
import QuantumProver.InformationTheory.DepolarizingSquashedEntanglement.BoundaryConstruction
import QuantumProver.InformationTheory.SuperchannelDiscrimination.TestingTheorems

set_option autoImplicit false

noncomputable section

open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder Matrix Kronecker
  Matrix.Norms.L2Operator ContinuousFunctionalCalculus

namespace QuantumProver.DepolarizingSquashedEntanglement.Identities

theorem cfc_trace_eq_eigenvalue_sum {I : Type*} [Fintype I] [DecidableEq I]
    {ρ : QMatrix I} (hρ : ρ.IsHermitian) (f : ℝ → ℝ) :
    (Matrix.trace (cfc f ρ)).re = ∑ i : I, f (hρ.eigenvalues i) := by
  rw [hρ.cfc_eq f, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply,
    Matrix.trace_mul_cycle]
  simp [Unitary.coe_star_mul_self, Matrix.trace_diagonal, Function.comp_def]

theorem entropyNat_eq_of_charpoly_eq {I : Type*} [Fintype I] [DecidableEq I]
    {ρ σ : QMatrix I} (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian)
    (hp : ρ.charpoly = σ.charpoly) : entropyNat ρ = entropyNat σ := by
  unfold entropyNat
  rw [cfc_trace_eq_eigenvalue_sum hρ, cfc_trace_eq_eigenvalue_sum hσ]
  rw [(hρ.eigenvalues_eq_eigenvalues_iff hσ).mpr hp]

theorem entropyNat_diagonal {I : Type*} [Fintype I] [DecidableEq I]
    (eigen : I → ℝ) :
    entropyNat (Matrix.diagonal (fun i => (eigen i : ℂ))) =
      ∑ i : I, Real.negMulLog (eigen i) := by
  unfold entropyNat
  rw [QuantumProver.SuperchannelDiscrimination.TensorEntropy.cfc_diagonal_real]
  simp [Matrix.trace_diagonal]

def realTwo (a b c : ℝ) : QMatrix Qubit := !![(a : ℂ), (c : ℂ); (c : ℂ), (b : ℂ)]

def twoEigenPlus (a b c : ℝ) : ℝ :=
  (a + b + Real.sqrt ((a - b) ^ 2 + 4 * c ^ 2)) / 2

def twoEigenMinus (a b c : ℝ) : ℝ :=
  (a + b - Real.sqrt ((a - b) ^ 2 + 4 * c ^ 2)) / 2

def twoEigenvalues (a b c : ℝ) (i : Qubit) : ℝ :=
  if i = 0 then twoEigenPlus a b c else twoEigenMinus a b c

theorem realTwo_isHermitian (a b c : ℝ) : (realTwo a b c).IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [realTwo, Matrix.conjTranspose_apply]

theorem twoEigen_sum (a b c : ℝ) :
    twoEigenPlus a b c + twoEigenMinus a b c = a + b := by
  dsimp [twoEigenPlus, twoEigenMinus]
  ring

theorem twoEigen_product (a b c : ℝ) :
    twoEigenPlus a b c * twoEigenMinus a b c = a * b - c ^ 2 := by
  have hnonneg : 0 ≤ (a - b) ^ 2 + 4 * c ^ 2 := by positivity
  have hs := Real.sq_sqrt hnonneg
  dsimp [twoEigenPlus, twoEigenMinus]
  nlinarith

theorem realTwo_charpoly (a b c : ℝ) :
    (realTwo a b c).charpoly =
      (Matrix.diagonal (fun i : Qubit => (twoEigenvalues a b c i : ℂ))).charpoly := by
  have ht : (realTwo a b c).trace =
      (Matrix.diagonal (fun i : Qubit => (twoEigenvalues a b c i : ℂ))).trace := by
    simp only [realTwo, Matrix.trace, Matrix.diag, Fin.sum_univ_two,
      Matrix.diagonal_apply, twoEigenvalues]
    norm_num
    exact_mod_cast (twoEigen_sum a b c).symm
  have hd : (realTwo a b c).det =
      (Matrix.diagonal (fun i : Qubit => (twoEigenvalues a b c i : ℂ))).det := by
    rw [Matrix.det_fin_two, Matrix.det_fin_two]
    norm_num [realTwo, Matrix.diagonal_apply, twoEigenvalues]
    have hprod := (twoEigen_product a b c).symm
    simp only [pow_two] at hprod
    exact_mod_cast hprod
  rw [Matrix.charpoly_fin_two, Matrix.charpoly_fin_two, ht, hd]

theorem entropyNat_realTwo (a b c : ℝ) :
    entropyNat (realTwo a b c) = Real.negMulLog (twoEigenPlus a b c) +
      Real.negMulLog (twoEigenMinus a b c) := by
  have hdiag : (Matrix.diagonal
      (fun i : Qubit => (twoEigenvalues a b c i : ℂ))).IsHermitian := by
    simp [Matrix.IsHermitian, Matrix.diagonal_conjTranspose]
  rw [entropyNat_eq_of_charpoly_eq (realTwo_isHermitian a b c) hdiag
    (realTwo_charpoly a b c), entropyNat_diagonal]
  simp [Fin.sum_univ_two, twoEigenvalues]

def coreDensity : Density Fixed16.CoreIndex where
  matrix := Fixed16.coreXi
  positive := Fixed16.coreXi_posSemidef
  trace_one := Fixed16.coreXi_trace_one

theorem corePurifier_IsNormalized : IsNormalized Fixed16.corePurifier := by
  exact Fixed16.corePurifier_normalized

def corePurifierDensity : Density (Fixed16.CoreIndex × Fin 4) where
  matrix := pureDensity Fixed16.corePurifier
  positive := QuantumProver.WernerEndpoint.pureDensity_posSemidef Fixed16.corePurifier
  trace_one := by
    rw [show pureDensity Fixed16.corePurifier =
      QuantumProver.WernerEndpoint.pureDensity Fixed16.corePurifier from rfl,
      QuantumProver.WernerEndpoint.pureDensity_trace]
    change ((∑ pg, Complex.normSq (Fixed16.corePurifier pg) : ℝ) : ℂ) = 1
    rw [Fixed16.corePurifier_normalized]
    norm_num

theorem corePurifierDensity_marginal :
    partialTraceRight corePurifierDensity.matrix = coreDensity.matrix := by
  exact Fixed16.corePurifierReduced_eq_coreXi

theorem weakIsometry_IsIsometry {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    IsIsometry (Fixed16.weakIsometry r) := Fixed16.weakIsometry_gram hr hr1

def environmentFamily (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1) : KrausFamily Qubit Qubit where
  count := 2
  operator := Fixed16.environmentKraus r
  complete := Fixed16.environmentKraus_gram hr hr1

def retainedFamily (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1) : KrausFamily Qubit Qubit where
  count := 2
  operator := Fixed16.retainedKraus r
  complete := Fixed16.retainedKraus_gram hr hr1

theorem environmentFamily_actual_partialTrace (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (ρ : QMatrix Qubit) :
    (environmentFamily r hr hr1).apply ρ =
      partialTraceLeft (Fixed16.weakState r ρ) := by
  exact (Fixed16.weakEnvironment_eq_kraus r ρ).symm

theorem retainedFamily_actual_partialTrace (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (ρ : QMatrix Qubit) :
    (retainedFamily r hr hr1).apply ρ =
      partialTraceRight (Fixed16.weakState r ρ) := by
  exact (Fixed16.weakRetained_eq_kraus r ρ).symm

theorem weakEnvironment_trace (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1) (ρ : QMatrix Qubit) :
    (Fixed16.weakEnvironment r ρ).trace = ρ.trace := by
  rw [Fixed16.weakEnvironment_eq_kraus]
  exact (environmentFamily r hr hr1).trace_apply ρ

theorem weakRetained_trace (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1) (ρ : QMatrix Qubit) :
    (Fixed16.weakRetained r ρ).trace = ρ.trace := by
  rw [Fixed16.weakRetained_eq_kraus]
  exact (retainedFamily r hr hr1).trace_apply ρ

theorem weakEnvironment_positive (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    {ρ : QMatrix Qubit} (hρ : ρ.PosSemidef) :
    (Fixed16.weakEnvironment r ρ).PosSemidef := by
  rw [Fixed16.weakEnvironment_eq_kraus]
  exact (environmentFamily r hr hr1).apply_positive hρ

theorem weakRetained_positive (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    {ρ : QMatrix Qubit} (hρ : ρ.PosSemidef) :
    (Fixed16.weakRetained r ρ).PosSemidef := by
  rw [Fixed16.weakRetained_eq_kraus]
  exact (retainedFamily r hr hr1).apply_positive hρ

abbrev PairOutput := ((Qubit × Qubit) × (Qubit × Qubit)) × Fin 4
abbrev SeedIndex := ((Qubit × Qubit) × Fixed16.CoreIndex) × Fin 4

def weakPair (r : ℝ) : Matrix ((Qubit × Qubit) × (Qubit × Qubit)) Fixed16.CoreIndex ℂ :=
  Fixed16.weakIsometry r ⊗ₖ Fixed16.weakIsometry r

theorem weakPair_gram {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    (weakPair r)ᴴ * weakPair r = 1 := by
  simp only [weakPair, Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
    Fixed16.weakIsometry_gram hr hr1, Matrix.one_kronecker_one]

def pairedLift (r : ℝ) : Matrix PairOutput (Fixed16.CoreIndex × Fin 4) ℂ :=
  weakPair r ⊗ₖ (1 : Matrix (Fin 4) (Fin 4) ℂ)

theorem pairedLift_gram {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    (pairedLift r)ᴴ * pairedLift r = 1 := by
  simp only [pairedLift, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
    ← Matrix.mul_kronecker_mul, weakPair_gram hr hr1, Matrix.one_mul,
    Matrix.one_kronecker_one]

def pairedKet (r : ℝ) : PairOutput → ℂ :=
  (pairedLift r).mulVec Fixed16.corePurifier

def pairedDensity (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1) : Density PairOutput where
  matrix := pairedLift r * corePurifierDensity.matrix * (pairedLift r)ᴴ
  positive := corePurifierDensity.positive.mul_mul_conjTranspose_same (pairedLift r)
  trace_one := by
    rw [Matrix.trace_mul_cycle, pairedLift_gram hr hr1, Matrix.one_mul]
    exact corePurifierDensity.trace_one

theorem pairedDensity_eq_pure (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    (pairedDensity r hr hr1).matrix = pureDensity (pairedKet r) := by
  exact QuantumProver.WernerEndpoint.sandwich_crossDensity (pairedLift r)
    Fixed16.corePurifier Fixed16.corePurifier

theorem pairedKet_IsNormalized (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    IsNormalized (pairedKet r) := by
  have ht := (pairedDensity r hr hr1).trace_one
  rw [pairedDensity_eq_pure r hr hr1] at ht
  change Matrix.trace (QuantumProver.WernerEndpoint.pureDensity (pairedKet r)) = 1 at ht
  rw [QuantumProver.WernerEndpoint.pureDensity_trace] at ht
  have hre := congrArg Complex.re ht
  exact hre

def collectRegisters : PairOutput ≃ SeedIndex where
  toFun := fun x => (((x.1.1.1, x.1.2.1), (x.1.1.2, x.1.2.2)), x.2)
  invFun := fun x => (((x.1.1.1, x.1.2.1), (x.1.1.2, x.1.2.2)), x.2)
  left_inv := by rintro ⟨⟨⟨a, l⟩, ⟨b, e⟩⟩, g⟩; rfl
  right_inv := by rintro ⟨⟨⟨a, b⟩, ⟨l, e⟩⟩, g⟩; rfl

def seedKet (r : ℝ) : SeedIndex → ℂ := fun x => pairedKet r (collectRegisters.symm x)

theorem seedKet_eq_sum (r : ℝ) (a b l e : Qubit) (g : Fin 4) :
    seedKet r (((a, b), (l, e)), g) =
      ∑ p : Fixed16.CoreIndex, Fixed16.weakIsometry r (a, l) p.1 *
        Fixed16.weakIsometry r (b, e) p.2 * Fixed16.corePurifier (p, g) := by
  simp [seedKet, pairedKet, pairedLift, weakPair, collectRegisters,
    Matrix.mulVec, dotProduct, Matrix.kroneckerMap_apply, Matrix.one_apply,
    Fintype.sum_prod_type, apply_ite, mul_ite, ite_mul, mul_assoc]

def seedDiagonalPhase (d : Qubit → ℂ) (x : SeedIndex) : ℂ :=
  Fixed16.coreEnvironmentPhase d x.1.1 * Fixed16.coreEnvironmentPhase d x.1.2 *
    Fixed16.corePurifierPhase d x.2

theorem seedKet_diagonal_phase (d : Qubit → ℂ)
    (hd0 : star (d 0) * d 0 = 1) (hd1 : star (d 1) * d 1 = 1)
    (r : ℝ) (x : SeedIndex) :
    seedDiagonalPhase d x * seedKet r x = seedKet r x := by
  rcases x with ⟨⟨⟨a, b⟩, ⟨l, e⟩⟩, g⟩
  simp only [seedKet_eq_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  have hl := Fixed16.weakIsometry_diagonal_phase (fun i => star (d i)) r a l p.1
  have hr := Fixed16.weakIsometry_diagonal_phase d r b e p.2
  have hz := Fixed16.corePurifier_diagonal_phase d hd0 hd1 p g
  calc
    _ = ((star (d a) * star (d l)) * Fixed16.weakIsometry r (a, l) p.1) *
        ((d b * d e) * Fixed16.weakIsometry r (b, e) p.2) *
        (Fixed16.corePurifierPhase d g * Fixed16.corePurifier (p, g)) := by
          dsimp [seedDiagonalPhase, Fixed16.coreEnvironmentPhase]
          ring
    _ = (star (d 0) * d 0) *
        (Fixed16.weakIsometry r (a, l) p.1 * Fixed16.weakIsometry r (b, e) p.2) *
        (Fixed16.coreEnvironmentPhase d p * Fixed16.corePurifierPhase d g *
          Fixed16.corePurifier (p, g)) := by
          rw [hl, hr]
          dsimp [Fixed16.coreEnvironmentPhase]
          ring
    _ = _ := by rw [hd0, hz]; ring

theorem seedKet_IsNormalized (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    IsNormalized (seedKet r) := by
  change (∑ x : SeedIndex, Complex.normSq (pairedKet r (collectRegisters.symm x))) = 1
  have hs := collectRegisters.symm.sum_comp
    (fun p : PairOutput => Complex.normSq (pairedKet r p))
  exact hs.trans (pairedKet_IsNormalized r hr hr1)

def seedDensity (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1) : Density SeedIndex where
  matrix := pureDensity (seedKet r)
  positive := QuantumProver.WernerEndpoint.pureDensity_posSemidef (seedKet r)
  trace_one := by
    change Matrix.trace (QuantumProver.WernerEndpoint.pureDensity (seedKet r)) = 1
    rw [QuantumProver.WernerEndpoint.pureDensity_trace]
    have h := seedKet_IsNormalized r hr hr1
    change QuantumProver.WernerEndpoint.vectorNormSq (seedKet r) = 1 at h
    rw [h]
    norm_num

theorem partialTraceRight_tensor_sandwich {I O G : Type*}
    [Fintype I] [Fintype O] [Fintype G]
    [DecidableEq I] [DecidableEq O] [DecidableEq G]
    (U : Matrix O I ℂ) (ρ : QMatrix (I × G)) :
    partialTraceRight ((U ⊗ₖ (1 : QMatrix G)) * ρ *
      (U ⊗ₖ (1 : QMatrix G))ᴴ) = U * partialTraceRight ρ * Uᴴ := by
  ext a b
  simp [partialTraceRight, QuantumProver.WernerEndpoint.partialTraceLeft,
    Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.kroneckerMap_apply,
    Matrix.one_apply, Fintype.sum_prod_type, apply_ite, mul_ite, ite_mul,
    Finset.sum_mul, Finset.mul_sum, mul_assoc]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  exact Finset.sum_comm

theorem pairedDensity_core_marginal (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    partialTraceRight (pairedDensity r hr hr1).matrix =
      weakPair r * Fixed16.coreXi * (weakPair r)ᴴ := by
  change partialTraceRight ((weakPair r ⊗ₖ (1 : QMatrix (Fin 4))) *
    corePurifierDensity.matrix * (weakPair r ⊗ₖ (1 : QMatrix (Fin 4)))ᴴ) = _
  rw [partialTraceRight_tensor_sandwich, corePurifierDensity_marginal]
  rfl

def tensorEnvironmentKraus (x y : ℝ) (kl : Qubit × Qubit) :
    QMatrix Fixed16.CoreIndex :=
  Fixed16.environmentKraus x kl.1 ⊗ₖ Fixed16.environmentKraus y kl.2

theorem tensorEnvironmentKraus_complete {x y : ℝ}
    (hx : 0 ≤ x) (hx1 : x ≤ 1) (hy : 0 ≤ y) (hy1 : y ≤ 1) :
    (∑ kl : Qubit × Qubit,
      (tensorEnvironmentKraus x y kl)ᴴ * tensorEnvironmentKraus x y kl) = 1 := by
  calc
    _ = (∑ k : Qubit, (Fixed16.environmentKraus x k)ᴴ * Fixed16.environmentKraus x k) ⊗ₖ
        (∑ l : Qubit, (Fixed16.environmentKraus y l)ᴴ * Fixed16.environmentKraus y l) := by
      simp only [tensorEnvironmentKraus, Matrix.conjTranspose_kronecker,
        ← Matrix.mul_kronecker_mul]
      ext p q
      simp [Matrix.sum_apply, Matrix.kroneckerMap_apply, Fintype.sum_prod_type,
        Finset.sum_mul, Finset.mul_sum]
      ring
    _ = 1 := by
      rw [Fixed16.environmentKraus_gram hx hx1, Fixed16.environmentKraus_gram hy hy1,
        Matrix.one_kronecker_one]

def tensorEnvironmentFamily (x y : ℝ)
    (hx : 0 ≤ x) (hx1 : x ≤ 1) (hy : 0 ≤ y) (hy1 : y ≤ 1) :
    KrausFamily Fixed16.CoreIndex Fixed16.CoreIndex where
  count := 4
  operator := fun k => tensorEnvironmentKraus x y
    ((finProdFinEquiv (m := 2) (n := 2)).symm k)
  complete := by
    have hs := (finProdFinEquiv (m := 2) (n := 2)).symm.sum_comp
      (fun kl : Qubit × Qubit =>
        (tensorEnvironmentKraus x y kl)ᴴ * tensorEnvironmentKraus x y kl)
    exact hs.trans (tensorEnvironmentKraus_complete hx hx1 hy hy1)

def tensorEnvironment (x y : ℝ) (ρ : QMatrix Fixed16.CoreIndex) :
    QMatrix Fixed16.CoreIndex :=
  ∑ kl : Qubit × Qubit,
    tensorEnvironmentKraus x y kl * ρ * (tensorEnvironmentKraus x y kl)ᴴ

theorem tensorEnvironmentFamily_apply (x y : ℝ)
    (hx : 0 ≤ x) (hx1 : x ≤ 1) (hy : 0 ≤ y) (hy1 : y ≤ 1)
    (ρ : QMatrix Fixed16.CoreIndex) :
    (tensorEnvironmentFamily x y hx hx1 hy hy1).apply ρ = tensorEnvironment x y ρ := by
  exact (finProdFinEquiv (m := 2) (n := 2)).symm.sum_comp
    (fun kl : Qubit × Qubit =>
      tensorEnvironmentKraus x y kl * ρ * (tensorEnvironmentKraus x y kl)ᴴ)

def dampedCoreDensity (x y : ℝ)
    (hx : 0 ≤ x) (hx1 : x ≤ 1) (hy : 0 ≤ y) (hy1 : y ≤ 1) : Density Fixed16.CoreIndex where
  matrix := (tensorEnvironmentFamily x y hx hx1 hy hy1).apply Fixed16.coreXi
  positive := (tensorEnvironmentFamily x y hx hx1 hy hy1).apply_positive Fixed16.coreXi_posSemidef
  trace_one := ((tensorEnvironmentFamily x y hx hx1 hy hy1).trace_apply
    Fixed16.coreXi).trans Fixed16.coreXi_trace_one

def dampedCoreX (x y : ℝ) : QMatrix Fixed16.CoreIndex := fun p q =>
  if p = q then
    if p = (0, 0) then ((117 + 5 * x + 5 * y + 33 * x * y) / 160 : ℝ)
    else if p = (0, 1) then ((1 - y) * (5 + 33 * x) / 160 : ℝ)
    else if p = (1, 0) then ((1 - x) * (5 + 33 * y) / 160 : ℝ)
    else (33 * (1 - x) * (1 - y) / 160 : ℝ)
  else if (p = (0, 0) ∧ q = (1, 1)) ∨ (p = (1, 1) ∧ q = (0, 0)) then
    (7 / 20 * Real.sqrt (1 - x) * Real.sqrt (1 - y) : ℝ)
  else 0

set_option maxHeartbeats 1000000 in

theorem tensorEnvironment_coreXi_eq_X {x y : ℝ}
    (hx : 0 ≤ x) (hx1 : x ≤ 1) (hy : 0 ≤ y) (hy1 : y ≤ 1) :
    tensorEnvironment x y Fixed16.coreXi = dampedCoreX x y := by
  have hsx : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx
  have hsy : Real.sqrt y ^ 2 = y := Real.sq_sqrt hy
  have hsxc : Real.sqrt (1 - x) ^ 2 = 1 - x := Real.sq_sqrt (sub_nonneg.mpr hx1)
  have hsyc : Real.sqrt (1 - y) ^ 2 = 1 - y := Real.sq_sqrt (sub_nonneg.mpr hy1)
  ext p q
  rcases p with ⟨a, b⟩
  rcases q with ⟨c, d⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    apply Complex.ext <;>
    norm_num [tensorEnvironment, tensorEnvironmentKraus, dampedCoreX,
      Fixed16.environmentKraus, Fixed16.weakIsometry, Fixed16.coreXi,
      Fixed16.coreVector, Matrix.sum_apply, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Matrix.kroneckerMap_apply, Matrix.vecMulVec_apply,
      Matrix.one_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
      RCLike.real_smul_eq_coe_mul, Complex.mul_re, Complex.mul_im] <;>
    ring_nf <;> norm_num [hsx, hsy, hsxc, hsyc] <;> ring

theorem dampedCoreDensity_matrix_eq_X {x y : ℝ}
    (hx : 0 ≤ x) (hx1 : x ≤ 1) (hy : 0 ≤ y) (hy1 : y ≤ 1) :
    (dampedCoreDensity x y hx hx1 hy hy1).matrix = dampedCoreX x y := by
  exact (tensorEnvironmentFamily_apply x y hx hx1 hy hy1 Fixed16.coreXi).trans
    (tensorEnvironment_coreXi_eq_X hx hx1 hy hy1)

def xEvenA (x y : ℝ) : ℝ := (117 + 5 * x + 5 * y + 33 * x * y) / 160
def xEvenB (x y : ℝ) : ℝ := 33 * (1 - x) * (1 - y) / 160
def xEvenC (x y : ℝ) : ℝ := 7 / 20 * Real.sqrt (1 - x) * Real.sqrt (1 - y)
def xOddZero (x y : ℝ) : ℝ := (1 - y) * (5 + 33 * x) / 160
def xOddOne (x y : ℝ) : ℝ := (1 - x) * (5 + 33 * y) / 160

def evenOddOrder : (Qubit ⊕ Qubit) ≃ Fixed16.CoreIndex where
  toFun := Sum.elim (fun i => if i = 0 then (0, 0) else (1, 1))
    (fun i => if i = 0 then (0, 1) else (1, 0))
  invFun := fun p => if p.1 = p.2 then Sum.inl p.1 else Sum.inr p.1
  left_inv := by
    intro i
    rcases i with i | i <;> fin_cases i <;> simp
  right_inv := by
    rintro ⟨a, b⟩
    fin_cases a <;> fin_cases b <;> simp

def xOddDiagonal (x y : ℝ) : QMatrix Qubit :=
  Matrix.diagonal (fun i => (((if i = 0 then xOddZero x y else xOddOne x y) : ℝ) : ℂ))

def xEvenDiagonal (x y : ℝ) : QMatrix Qubit :=
  Matrix.diagonal (fun i => (twoEigenvalues (xEvenA x y) (xEvenB x y) (xEvenC x y) i : ℂ))

def xSpectrum (x y : ℝ) (p : Fixed16.CoreIndex) : ℝ :=
  if p = (0, 0) then twoEigenPlus (xEvenA x y) (xEvenB x y) (xEvenC x y)
  else if p = (1, 1) then twoEigenMinus (xEvenA x y) (xEvenB x y) (xEvenC x y)
  else if p = (0, 1) then xOddZero x y else xOddOne x y

theorem dampedCoreX_reindex (x y : ℝ) :
    Matrix.reindex evenOddOrder.symm evenOddOrder.symm (dampedCoreX x y) =
      Matrix.fromBlocks (realTwo (xEvenA x y) (xEvenB x y) (xEvenC x y)) 0 0
        (xOddDiagonal x y) := by
  rw [Matrix.reindex_apply]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    fin_cases i <;> fin_cases j <;>
    simp [Matrix.submatrix, evenOddOrder, dampedCoreX, Matrix.fromBlocks,
      realTwo, xEvenA, xEvenB, xEvenC, xOddZero, xOddOne, xOddDiagonal,
      Matrix.diagonal_apply]

theorem xSpectrum_diagonal_reindex (x y : ℝ) :
    Matrix.reindex evenOddOrder.symm evenOddOrder.symm
      (Matrix.diagonal (fun p => (xSpectrum x y p : ℂ))) =
      Matrix.fromBlocks (xEvenDiagonal x y) 0 0 (xOddDiagonal x y) := by
  rw [Matrix.reindex_apply]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    fin_cases i <;> fin_cases j <;>
    simp [Matrix.submatrix, evenOddOrder, Matrix.fromBlocks,
      Matrix.diagonal_apply, xSpectrum, xEvenDiagonal, xOddDiagonal, twoEigenvalues]

theorem dampedCoreX_charpoly (x y : ℝ) :
    (dampedCoreX x y).charpoly =
      (Matrix.diagonal (fun p => (xSpectrum x y p : ℂ))).charpoly := by
  rw [← Matrix.charpoly_reindex evenOddOrder.symm (dampedCoreX x y),
    ← Matrix.charpoly_reindex evenOddOrder.symm
      (Matrix.diagonal (fun p => (xSpectrum x y p : ℂ))),
    dampedCoreX_reindex, xSpectrum_diagonal_reindex]
  simp only [Matrix.charpoly_fromBlocks_zero₁₂, xEvenDiagonal, realTwo_charpoly]

theorem dampedCoreX_isHermitian (x y : ℝ) : (dampedCoreX x y).IsHermitian := by
  ext p q
  rcases p with ⟨a, b⟩
  rcases q with ⟨c, d⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp [dampedCoreX, Matrix.conjTranspose_apply]

theorem entropyNat_dampedCore_spectrum {x y : ℝ}
    (hx : 0 ≤ x) (hx1 : x ≤ 1) (hy : 0 ≤ y) (hy1 : y ≤ 1) :
    entropyNat (dampedCoreDensity x y hx hx1 hy hy1).matrix =
      Real.negMulLog (twoEigenPlus (xEvenA x y) (xEvenB x y) (xEvenC x y)) +
      Real.negMulLog (twoEigenMinus (xEvenA x y) (xEvenB x y) (xEvenC x y)) +
      Real.negMulLog (xOddZero x y) + Real.negMulLog (xOddOne x y) := by
  have hd : (Matrix.diagonal (fun p => (xSpectrum x y p : ℂ))).IsHermitian := by
    simp [Matrix.IsHermitian, Matrix.diagonal_conjTranspose]
  rw [dampedCoreDensity_matrix_eq_X hx hx1 hy hy1,
    entropyNat_eq_of_charpoly_eq (dampedCoreX_isHermitian x y) hd (dampedCoreX_charpoly x y),
    entropyNat_diagonal]
  simp [Fintype.sum_prod_type, Fin.sum_univ_two, xSpectrum]
  ring

theorem xEvenC_one_square {r : ℝ} (hr1 : r ≤ 1) :
    xEvenC 0 r ^ 2 = (49 / 400) * (1 - r) := by
  simp only [xEvenC, sub_zero, Real.sqrt_one, mul_one]
  rw [mul_pow, Real.sq_sqrt (sub_nonneg.mpr hr1)]
  norm_num

theorem xEven_discriminant_one {r : ℝ} (hr1 : r ≤ 1) :
    (xEvenA 0 r - xEvenB 0 r) ^ 2 + 4 * xEvenC 0 r ^ 2 =
      (19600 - 6160 * r + 1444 * r ^ 2) / 25600 := by
  rw [xEvenC_one_square hr1]
  dsimp [xEvenA, xEvenB]
  ring

theorem xEvenC_both {r : ℝ} (hr1 : r ≤ 1) :
    xEvenC r r = (7 / 20) * (1 - r) := by
  unfold xEvenC
  rw [mul_assoc, Real.mul_self_sqrt (sub_nonneg.mpr hr1)]

theorem xEven_discriminant_both {r : ℝ} (hr1 : r ≤ 1) :
    (xEvenA r r - xEvenB r r) ^ 2 + 4 * xEvenC r r ^ 2 =
      (19600 - 12320 * r + 18320 * r ^ 2) / 25600 := by
  rw [xEvenC_both hr1]
  dsimp [xEvenA, xEvenB]
  ring

theorem xEven_root_one {r : ℝ} (hr1 : r ≤ 1) :
    Real.sqrt ((xEvenA 0 r - xEvenB 0 r) ^ 2 + 4 * xEvenC 0 r ^ 2) =
      Fixed16Calculus.oneRoot r / 160 := by
  rw [xEven_discriminant_one hr1,
    Real.sqrt_div' _ (by norm_num : 0 ≤ (25600 : ℝ))]
  norm_num
  congr 1
  ring

theorem xEven_root_both {r : ℝ} (hr1 : r ≤ 1) :
    Real.sqrt ((xEvenA r r - xEvenB r r) ^ 2 + 4 * xEvenC r r ^ 2) =
      Fixed16Calculus.bothRoot r / 160 := by
  rw [xEven_discriminant_both hr1,
    Real.sqrt_div' _ (by norm_num : 0 ≤ (25600 : ℝ))]
  norm_num
  congr 1
  ring

theorem xEven_eigenvalues_one {r : ℝ} (hr1 : r ≤ 1) :
    twoEigenPlus (xEvenA 0 r) (xEvenB 0 r) (xEvenC 0 r) = Fixed16Calculus.onePlus r ∧
    twoEigenMinus (xEvenA 0 r) (xEvenB 0 r) (xEvenC 0 r) = Fixed16Calculus.oneMinus r := by
  constructor <;> simp only [twoEigenPlus, twoEigenMinus] <;> rw [xEven_root_one hr1] <;>
    dsimp [xEvenA, xEvenB, Fixed16Calculus.onePlus, Fixed16Calculus.oneMinus] <;> ring

theorem xEven_eigenvalues_both {r : ℝ} (hr1 : r ≤ 1) :
    twoEigenPlus (xEvenA r r) (xEvenB r r) (xEvenC r r) = Fixed16Calculus.bothPlus r ∧
    twoEigenMinus (xEvenA r r) (xEvenB r r) (xEvenC r r) = Fixed16Calculus.bothMinus r := by
  constructor <;> simp only [twoEigenPlus, twoEigenMinus] <;> rw [xEven_root_both hr1] <;>
    dsimp [xEvenA, xEvenB, Fixed16Calculus.bothPlus, Fixed16Calculus.bothMinus] <;> ring

theorem entropyNat_dampedCore_one {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    entropyNat (dampedCoreDensity 0 r (by norm_num) (by norm_num) hr hr1).matrix =
      Fixed16Calculus.oneEntropy r := by
  rw [entropyNat_dampedCore_spectrum, (xEven_eigenvalues_one hr1).1,
    (xEven_eigenvalues_one hr1).2]
  have h0 : xOddZero 0 r = Fixed16Calculus.oneOddLeft r := by
    dsimp [xOddZero, Fixed16Calculus.oneOddLeft]
    ring
  have h1 : xOddOne 0 r = Fixed16Calculus.oneOddRight r := by
    dsimp [xOddOne, Fixed16Calculus.oneOddRight]
    ring
  rw [h0, h1]
  rfl

theorem entropyNat_dampedCore_both {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    entropyNat (dampedCoreDensity r r hr hr1 hr hr1).matrix =
      Fixed16Calculus.bothEntropy r := by
  rw [entropyNat_dampedCore_spectrum, (xEven_eigenvalues_both hr1).1,
    (xEven_eigenvalues_both hr1).2]
  have h0 : xOddZero r r = Fixed16Calculus.bothOdd r := by
    dsimp [xOddZero, Fixed16Calculus.bothOdd]
    ring
  have h1 : xOddOne r r = Fixed16Calculus.bothOdd r := by
    dsimp [xOddOne, Fixed16Calculus.bothOdd]
    ring
  rw [h0, h1]
  unfold Fixed16Calculus.bothEntropy
  ring

theorem entropyNat_dampedCore_swap {x y : ℝ}
    (hx : 0 ≤ x) (hx1 : x ≤ 1) (hy : 0 ≤ y) (hy1 : y ≤ 1) :
    entropyNat (dampedCoreDensity y x hy hy1 hx hx1).matrix =
      entropyNat (dampedCoreDensity x y hx hx1 hy hy1).matrix := by
  rw [entropyNat_dampedCore_spectrum, entropyNat_dampedCore_spectrum]
  have ha : xEvenA y x = xEvenA x y := by unfold xEvenA; ring
  have hb : xEvenB y x = xEvenB x y := by unfold xEvenB; ring
  have hc : xEvenC y x = xEvenC x y := by unfold xEvenC; ring
  rw [ha, hb, hc]
  dsimp [xOddZero, xOddOne]
  ring

theorem matrixCoreEntropyCombination_eq {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    entropyNat (dampedCoreDensity 0 r (by norm_num) (by norm_num) hr hr1).matrix +
      entropyNat (dampedCoreDensity r 0 hr hr1 (by norm_num) (by norm_num)).matrix -
      entropyNat (dampedCoreDensity r r hr hr1 hr hr1).matrix -
      entropyNat (dampedCoreDensity 0 0 (by norm_num) (by norm_num)
        (by norm_num) (by norm_num)).matrix = Fixed16Calculus.entropyCombination r := by
  rw [entropyNat_dampedCore_swap (by norm_num : (0 : ℝ) ≤ 0)
    (by norm_num : (0 : ℝ) ≤ 1) hr hr1]
  simp only [entropyNat_dampedCore_one hr hr1, entropyNat_dampedCore_both hr hr1,
    entropyNat_dampedCore_one (by norm_num : (0 : ℝ) ≤ 0) (by norm_num : (0 : ℝ) ≤ 1)]
  unfold Fixed16Calculus.entropyCombination
  ring

def matrixCoreEntropyCombination (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1) : ℝ :=
  entropyNat (dampedCoreDensity 0 r (by norm_num) (by norm_num) hr hr1).matrix +
    entropyNat (dampedCoreDensity r 0 hr hr1 (by norm_num) (by norm_num)).matrix -
    entropyNat (dampedCoreDensity r r hr hr1 hr hr1).matrix -
    entropyNat (dampedCoreDensity 0 0 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)).matrix

theorem matrixCoreEntropyCombination_eq_scalar (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    matrixCoreEntropyCombination r hr hr1 = Fixed16Calculus.entropyCombination r :=
  matrixCoreEntropyCombination_eq hr hr1

def matrixCoreBoundaryEntropy (δ : ℝ) (hδ : 0 ≤ δ) (hmax : δ ≤ 21 / 512) : ℝ :=
  matrixCoreEntropyCombination (Scalar.boundaryR δ) (Scalar.boundaryR_nonneg hδ)
    (le_trans (Scalar.boundaryR_le_quarter hδ hmax) (by norm_num)) / (2 * Real.log 2)

theorem matrixCoreBoundaryEntropy_eq_scalar (δ : ℝ)
    (hδ : 0 ≤ δ) (hmax : δ ≤ 21 / 512) :
    matrixCoreBoundaryEntropy δ hδ hmax = Fixed16Calculus.spectralBoundaryCost δ := by
  unfold matrixCoreBoundaryEntropy Fixed16Calculus.spectralBoundaryCost
  rw [matrixCoreEntropyCombination_eq_scalar]

theorem matrixCoreBoundaryEntropy_uniform_remainder :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (δ : ℝ) (hδ : 0 ≤ δ) (hmax : δ ≤ 21 / 512),
      |matrixCoreBoundaryEntropy δ hδ hmax -
        (3200 * Scalar.boundaryKappa / (81 * Real.log 2)) * δ ^ 2| ≤ C * δ ^ 3 := by
  obtain ⟨C, hC, hb⟩ := Fixed16Calculus.spectralBoundaryCost_uniform_remainder
  refine ⟨C, hC, ?_⟩
  intro δ hδ hmax
  rw [matrixCoreBoundaryEntropy_eq_scalar]
  exact hb δ hδ hmax

theorem matrixCoreBoundaryEntropy_quadratic_upper :
    ∃ C : ℝ, 0 < C ∧ ∀ (δ : ℝ) (hδ : 0 ≤ δ) (hmax : δ ≤ 21 / 512),
      matrixCoreBoundaryEntropy δ hδ hmax ≤ C * δ ^ 2 := by
  obtain ⟨C, hC, hb⟩ := matrixCoreBoundaryEntropy_uniform_remainder
  let a : ℝ := 3200 * Scalar.boundaryKappa / (81 * Real.log 2)
  have ha : 0 < a := by
    dsimp [a]
    exact div_pos (mul_pos (by norm_num) Scalar.boundaryKappa_pos)
      (mul_pos (by norm_num) Scalar.log_two_pos)
  refine ⟨a + C * (21 / 512) + 1, by positivity, ?_⟩
  intro δ hδ hmax
  have he := hb δ hδ hmax
  have he' := (le_abs_self (matrixCoreBoundaryEntropy δ hδ hmax - a * δ ^ 2)).trans he
  have hp : δ ^ 3 ≤ (21 / 512) * δ ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hmax) (sq_nonneg δ)]
  have hc : C * δ ^ 3 ≤ C * (21 / 512) * δ ^ 2 := by
    calc
      C * δ ^ 3 ≤ C * ((21 / 512) * δ ^ 2) := mul_le_mul_of_nonneg_left hp hC
      _ = C * (21 / 512) * δ ^ 2 := by ring
  nlinarith [sq_nonneg δ]

def collectPair : (Fixed16.CoreIndex × Fixed16.CoreIndex) ≃
    (Fixed16.CoreIndex × Fixed16.CoreIndex) where
  toFun := fun x => ((x.1.1, x.2.1), (x.1.2, x.2.2))
  invFun := fun x => ((x.1.1, x.2.1), (x.1.2, x.2.2))
  left_inv := by rintro ⟨⟨a, l⟩, ⟨b, e⟩⟩; rfl
  right_inv := by rintro ⟨⟨a, b⟩, ⟨l, e⟩⟩; rfl

private theorem entropyNat_reindex_self {I : Type*} [Fintype I] [DecidableEq I]
    (e : I ≃ I) {ρ : QMatrix I} (hρ : ρ.IsHermitian) :
    entropyNat (Matrix.reindex e e ρ) = entropyNat ρ :=
  entropyNat_eq_of_charpoly_eq (hρ.reindex e) hρ (Matrix.charpoly_reindex e ρ)

private theorem entropyNat_isometric_local {I O : Type*} [Fintype I] [Fintype O]
    [DecidableEq I] [DecidableEq O] (V : Matrix O I ℂ)
    (hV : IsIsometry V) {ρ : QMatrix I} (hρ : ρ.IsHermitian) :
    entropyNat (V * ρ * Vᴴ) = entropyNat ρ := by
  change (Matrix.trace (cfc Real.negMulLog
    (QuantumProver.SuperchannelDiscrimination.ZeroExtension.extend V ρ))).re = _
  rw [QuantumProver.SuperchannelDiscrimination.ZeroExtension.cfc_extend V hV
    Real.negMulLog Real.negMulLog_zero hρ,
    QuantumProver.SuperchannelDiscrimination.ZeroExtension.extend_trace V hV]
  rfl

theorem seedDensity_ABE_marginal (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    partialTraceRight (seedDensity r hr hr1).matrix =
      Matrix.reindex collectPair collectPair
        (partialTraceRight (pairedDensity r hr hr1).matrix) := by
  rw [Matrix.reindex_apply, pairedDensity_eq_pure]
  ext p q
  simp [partialTraceRight, QuantumProver.WernerEndpoint.partialTraceLeft, seedDensity,
    seedKet, collectRegisters, collectPair, Matrix.submatrix, pureDensity,
    QuantumProver.WernerEndpoint.pureDensity, QuantumProver.WernerEndpoint.crossDensity]

theorem entropyNat_seed_ABE (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    entropyNat (partialTraceRight (seedDensity r hr hr1).matrix) =
      entropyNat Fixed16.coreXi := by
  rw [seedDensity_ABE_marginal,
    entropyNat_reindex_self collectPair
      (partialTraceRight_positive (pairedDensity r hr hr1).positive).1,
    pairedDensity_core_marginal,
    entropyNat_isometric_local (weakPair r) (weakPair_gram hr hr1)
      Fixed16.coreXi_posSemidef.1]

theorem dampedCoreDensity_zero_zero :
    (dampedCoreDensity 0 0 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)).matrix = Fixed16.coreXi := by
  rw [dampedCoreDensity_matrix_eq_X]
  ext p q
  rcases p with ⟨a, b⟩
  rcases q with ⟨c, d⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    norm_num [dampedCoreX, Fixed16.coreXi, Fixed16.coreVector,
      Matrix.vecMulVec_apply, Matrix.one_apply, RCLike.real_smul_eq_coe_mul]

theorem entropyNat_seed_ABE_eq_H00 (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    entropyNat (partialTraceRight (seedDensity r hr hr1).matrix) =
      entropyNat (dampedCoreDensity 0 0 (by norm_num) (by norm_num)
        (by norm_num) (by norm_num)).matrix := by
  rw [entropyNat_seed_ABE, dampedCoreDensity_zero_zero]

set_option maxHeartbeats 2000000 in

theorem seedDensity_E_marginal (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    partialTraceLeft (partialTraceRight (seedDensity r hr hr1).matrix) =
      tensorEnvironment r r Fixed16.coreXi := by
  rw [seedDensity_ABE_marginal, pairedDensity_core_marginal, Matrix.reindex_apply]
  ext p q
  rcases p with ⟨l, e⟩
  rcases q with ⟨m, f⟩
  simp [partialTraceLeft, QuantumProver.WernerEndpoint.partialTraceRight, Matrix.submatrix,
    collectPair, tensorEnvironment, tensorEnvironmentKraus,
    Fixed16.environmentKraus, weakPair, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.kroneckerMap_apply,
    Fintype.sum_prod_type, Fin.sum_univ_two]

theorem entropyNat_seed_E_eq_Hrr (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    entropyNat (partialTraceLeft (partialTraceRight (seedDensity r hr hr1).matrix)) =
      entropyNat (dampedCoreDensity r r hr hr1 hr hr1).matrix := by
  rw [seedDensity_E_marginal,
    ← tensorEnvironmentFamily_apply r r hr hr1 hr hr1 Fixed16.coreXi]
  rfl

theorem boundaryMixing_physical {δ : ℝ} (hδ : 0 ≤ δ) (hmax : δ ≤ 21 / 512) :
    0 ≤ boundaryMixing δ ∧ boundaryMixing δ ≤ 1 := by
  dsimp [boundaryMixing]
  constructor <;> linarith

theorem pauliWeight_boundary_zero (δ : ℝ) :
    pauliWeight (boundaryMixing δ) 0 = 1 / 2 + δ := by
  simp [pauliWeight, boundaryMixing]
  ring

theorem pauliWeight_boundary_other (δ : ℝ) {j : Fin 4} (hj : j ≠ 0) :
    pauliWeight (boundaryMixing δ) j = (1 / 2 - δ) / 3 := by
  simp [pauliWeight, boundaryMixing, hj]
  ring

theorem pauliWeights_boundary_positive {δ : ℝ} (hδ : 0 ≤ δ) (hmax : δ ≤ 21 / 512)
    (j : Fin 4) : 0 < pauliWeight (boundaryMixing δ) j := by
  by_cases hj : j = 0
  · subst j
    rw [pauliWeight_boundary_zero]
    linarith
  · rw [pauliWeight_boundary_other δ hj]
    linarith

def seedSupportA (r : ℝ) : Matrix (Qubit × Fixed16.CoreIndex) Fixed16.CoreIndex ℂ :=
  Matrix.reindex (Equiv.prodAssoc Qubit Qubit Qubit) (Equiv.refl _)
    (Fixed16.weakIsometry r ⊗ₖ (1 : QMatrix Qubit))

def collectSeedB : (Qubit × (Qubit × Qubit)) ≃ (Qubit × Fixed16.CoreIndex) where
  toFun := fun x => (x.2.1, (x.1, x.2.2))
  invFun := fun x => (x.2.1, (x.1, x.2.2))
  left_inv := by rintro ⟨l, b, e⟩; rfl
  right_inv := by rintro ⟨b, l, e⟩; rfl

def seedSupportB (r : ℝ) : Matrix (Qubit × Fixed16.CoreIndex) Fixed16.CoreIndex ℂ :=
  Matrix.reindex collectSeedB (Equiv.refl _)
    ((1 : QMatrix Qubit) ⊗ₖ Fixed16.weakIsometry r)

theorem seedSupportA_gram (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    (seedSupportA r)ᴴ * seedSupportA r = 1 := by
  unfold seedSupportA
  rw [Matrix.conjTranspose_reindex]
  simp only [Matrix.reindex_apply]
  rw [Matrix.submatrix_mul_equiv, Matrix.conjTranspose_kronecker,
    Matrix.conjTranspose_one, ← Matrix.mul_kronecker_mul,
    Fixed16.weakIsometry_gram hr hr1, Matrix.one_mul, Matrix.one_kronecker_one]
  simp

theorem seedSupportB_gram (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    (seedSupportB r)ᴴ * seedSupportB r = 1 := by
  unfold seedSupportB
  rw [Matrix.conjTranspose_reindex]
  simp only [Matrix.reindex_apply]
  rw [Matrix.submatrix_mul_equiv, Matrix.conjTranspose_kronecker,
    Matrix.conjTranspose_one, ← Matrix.mul_kronecker_mul,
    Fixed16.weakIsometry_gram hr hr1, Matrix.one_mul, Matrix.one_kronecker_one]
  simp

set_option maxHeartbeats 4000000 in

theorem seedDensity_AE_marginal (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    traceMiddle (partialTraceRight (seedDensity r hr hr1).matrix) =
      seedSupportA r *
        (dampedCoreDensity 0 r (by norm_num) (by norm_num) hr hr1).matrix *
        (seedSupportA r)ᴴ := by
  have hsr : Real.sqrt r ^ 2 = r := Real.sq_sqrt hr
  have hsc : Real.sqrt (1-r) ^ 2 = 1-r := Real.sq_sqrt (sub_nonneg.mpr hr1)
  have hsr3 : Real.sqrt r ^ 3 = r * Real.sqrt r := by
    rw [pow_succ, hsr]
  have hsc3 : Real.sqrt (1-r) ^ 3 = (1-r) * Real.sqrt (1-r) := by
    rw [pow_succ, hsc]
  have hsr4 : Real.sqrt r ^ 4 = r ^ 2 := by
    calc
      Real.sqrt r ^ 4 = (Real.sqrt r ^ 2) ^ 2 := by ring
      _ = r ^ 2 := by rw [hsr]
  have hsc4 : Real.sqrt (1-r) ^ 4 = (1-r) ^ 2 := by
    calc
      Real.sqrt (1-r) ^ 4 = (Real.sqrt (1-r) ^ 2) ^ 2 := by ring
      _ = (1-r) ^ 2 := by rw [hsc]
  rw [seedDensity_ABE_marginal, pairedDensity_core_marginal,
    dampedCoreDensity_matrix_eq_X, Matrix.reindex_apply]
  ext p q
  rcases p with ⟨a, l, e⟩
  rcases q with ⟨c, m, f⟩
  fin_cases a <;> fin_cases l <;> fin_cases e <;>
    fin_cases c <;> fin_cases m <;> fin_cases f <;>
    apply Complex.ext <;>
    norm_num [traceMiddle, collectPair, Matrix.submatrix, weakPair,
      seedSupportA, Matrix.reindex_apply, dampedCoreX,
      Fixed16.weakIsometry, Fixed16.coreXi, Fixed16.coreVector,
      Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.kroneckerMap_apply,
      Matrix.vecMulVec_apply, Matrix.one_apply, Fintype.sum_prod_type,
      Fin.sum_univ_two, RCLike.real_smul_eq_coe_mul, Complex.mul_re, Complex.mul_im] <;>
    ring_nf <;> norm_num [hsr, hsc, hsr3, hsc3, hsr4, hsc4] <;> ring

set_option maxHeartbeats 4000000 in

theorem seedDensity_BE_marginal (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    traceFirst (partialTraceRight (seedDensity r hr hr1).matrix) =
      seedSupportB r *
        (dampedCoreDensity r 0 hr hr1 (by norm_num) (by norm_num)).matrix *
        (seedSupportB r)ᴴ := by
  have hsr : Real.sqrt r ^ 2 = r := Real.sq_sqrt hr
  have hsc : Real.sqrt (1-r) ^ 2 = 1-r := Real.sq_sqrt (sub_nonneg.mpr hr1)
  have hsr3 : Real.sqrt r ^ 3 = r * Real.sqrt r := by
    rw [pow_succ, hsr]
  have hsc3 : Real.sqrt (1-r) ^ 3 = (1-r) * Real.sqrt (1-r) := by
    rw [pow_succ, hsc]
  have hsr4 : Real.sqrt r ^ 4 = r ^ 2 := by
    calc
      Real.sqrt r ^ 4 = (Real.sqrt r ^ 2) ^ 2 := by ring
      _ = r ^ 2 := by rw [hsr]
  have hsc4 : Real.sqrt (1-r) ^ 4 = (1-r) ^ 2 := by
    calc
      Real.sqrt (1-r) ^ 4 = (Real.sqrt (1-r) ^ 2) ^ 2 := by ring
      _ = (1-r) ^ 2 := by rw [hsc]
  rw [seedDensity_ABE_marginal, pairedDensity_core_marginal,
    dampedCoreDensity_matrix_eq_X, Matrix.reindex_apply]
  ext p q
  rcases p with ⟨b, l, e⟩
  rcases q with ⟨d, m, f⟩
  fin_cases b <;> fin_cases l <;> fin_cases e <;>
    fin_cases d <;> fin_cases m <;> fin_cases f <;>
    apply Complex.ext <;>
    norm_num [traceFirst, collectPair, Matrix.submatrix, weakPair,
      seedSupportB, collectSeedB, Matrix.reindex_apply, dampedCoreX,
      Fixed16.weakIsometry, Fixed16.coreXi, Fixed16.coreVector,
      Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.kroneckerMap_apply,
      Matrix.vecMulVec_apply, Matrix.one_apply, Fintype.sum_prod_type,
      Fin.sum_univ_two, RCLike.real_smul_eq_coe_mul, Complex.mul_re, Complex.mul_im] <;>
    ring_nf <;> norm_num [hsr, hsc, hsr3, hsc3, hsr4, hsc4] <;> ring

theorem entropyNat_seed_AE_eq_H0r (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    entropyNat (traceMiddle (partialTraceRight (seedDensity r hr hr1).matrix)) =
      entropyNat (dampedCoreDensity 0 r (by norm_num) (by norm_num) hr hr1).matrix := by
  rw [seedDensity_AE_marginal,
    entropyNat_isometric_local (seedSupportA r) (seedSupportA_gram r hr hr1)
      (dampedCoreDensity 0 r (by norm_num) (by norm_num) hr hr1).positive.1]

theorem entropyNat_seed_BE_eq_Hr0 (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    entropyNat (traceFirst (partialTraceRight (seedDensity r hr hr1).matrix)) =
      entropyNat (dampedCoreDensity r 0 hr hr1 (by norm_num) (by norm_num)).matrix := by
  rw [seedDensity_BE_marginal,
    entropyNat_isometric_local (seedSupportB r) (seedSupportB_gram r hr hr1)
      (dampedCoreDensity r 0 hr hr1 (by norm_num) (by norm_num)).positive.1]

theorem seed_cmiNat_eq_matrixCoreEntropyCombination (r : ℝ)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    cmiNat (partialTraceRight (seedDensity r hr hr1).matrix) =
      matrixCoreEntropyCombination r hr hr1 := by
  unfold cmiNat matrixCoreEntropyCombination
  rw [entropyNat_seed_AE_eq_H0r, entropyNat_seed_BE_eq_Hr0,
    entropyNat_seed_E_eq_Hrr, entropyNat_seed_ABE_eq_H00]

theorem seed_cmiBits_eq_matrixCoreEntropyCombination (r : ℝ)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    cmiBits (partialTraceRight (seedDensity r hr hr1).matrix) / 2 =
      matrixCoreEntropyCombination r hr hr1 / (2 * Real.log 2) := by
  unfold cmiBits
  rw [seed_cmiNat_eq_matrixCoreEntropyCombination, div_div, mul_comm]

theorem seed_boundary_cmiBits_eq_matrixCoreBoundaryEntropy (δ : ℝ)
    (hδ : 0 ≤ δ) (hmax : δ ≤ 21 / 512) :
    cmiBits (partialTraceRight (seedDensity (Scalar.boundaryR δ)
      (Scalar.boundaryR_nonneg hδ)
      ((Scalar.boundaryR_le_quarter hδ hmax).trans (by norm_num))).matrix) / 2 =
      matrixCoreBoundaryEntropy δ hδ hmax :=
  seed_cmiBits_eq_matrixCoreEntropyCombination _ _ _

theorem vectorNormSq_isometry {I O : Type*} [Fintype I] [Fintype O]
    [DecidableEq I] (V : Matrix O I ℂ) (hV : IsIsometry V) (v : I → ℂ) :
    vectorNormSq (V.mulVec v) = vectorNormSq v := by
  have hs := QuantumProver.WernerEndpoint.sandwich_crossDensity V v v
  change V * QuantumProver.WernerEndpoint.pureDensity v * Vᴴ =
    QuantumProver.WernerEndpoint.pureDensity (V.mulVec v) at hs
  have ht : Matrix.trace (QuantumProver.WernerEndpoint.pureDensity (V.mulVec v)) =
      Matrix.trace (QuantumProver.WernerEndpoint.pureDensity v) := by
    rw [← hs, Matrix.trace_mul_cycle, hV, Matrix.one_mul]
  rw [QuantumProver.WernerEndpoint.pureDensity_trace, QuantumProver.WernerEndpoint.pureDensity_trace] at ht
  exact congrArg Complex.re ht

def seedBranchLift (j : Fin 4) : QMatrix SeedIndex :=
  (Fixed16.tetraBranchMatrix j ⊗ₖ (1 : QMatrix Fixed16.CoreIndex)) ⊗ₖ
    (1 : QMatrix (Fin 4))

theorem seedBranchLift_gram (j : Fin 4) : (seedBranchLift j)ᴴ * seedBranchLift j = 1 := by
  simp only [seedBranchLift, Matrix.conjTranspose_kronecker,
    Matrix.conjTranspose_one, ← Matrix.mul_kronecker_mul,
    Fixed16.tetraBranchMatrix_gram, Matrix.one_mul, Matrix.one_kronecker_one]

def seedPauliLift (k : Fin 4) : QMatrix SeedIndex :=
  (Fixed16.pairedPauli k ⊗ₖ (1 : QMatrix Fixed16.CoreIndex)) ⊗ₖ
    (1 : QMatrix (Fin 4))

theorem seedPauliLift_gram (k : Fin 4) : (seedPauliLift k)ᴴ * seedPauliLift k = 1 := by
  simp only [seedPauliLift, Matrix.conjTranspose_kronecker,
    Matrix.conjTranspose_one, ← Matrix.mul_kronecker_mul,
    Fixed16.pairedPauli_gram, Matrix.one_mul, Matrix.one_kronecker_one]

theorem seedBranchLift_pauli_covariance (k j : Fin 4) :
    seedPauliLift k * seedBranchLift j =
      seedBranchLift (Fixed16.pauliBranchPermutation k j) := by
  simp only [seedPauliLift, seedBranchLift, ← Matrix.mul_kronecker_mul,
    Matrix.one_mul, Fixed16.tetraBranchMatrix_pauli_covariance]

def seedBranchKet (r : ℝ) (j : Fin 4) : SeedIndex → ℂ :=
  (seedBranchLift j).mulVec (seedKet r)

theorem seedBranchKet_IsNormalized (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1) (j : Fin 4) :
    IsNormalized (seedBranchKet r j) := by
  change vectorNormSq ((seedBranchLift j).mulVec (seedKet r)) = 1
  rw [vectorNormSq_isometry (seedBranchLift j) (seedBranchLift_gram j)]
  exact seedKet_IsNormalized r hr hr1

theorem seedBranchKet_pauli_covariance (k j : Fin 4) (r : ℝ) :
    (seedPauliLift k).mulVec (seedBranchKet r j) =
      seedBranchKet r (Fixed16.pauliBranchPermutation k j) := by
  unfold seedBranchKet
  rw [Matrix.mulVec_mulVec, seedBranchLift_pauli_covariance]

abbrev FixedEnvironment := Fin 4 × Fixed16.CoreIndex
abbrev FixedPurifier := Fin 4 × Fin 4
abbrev OmegaIndex := (Fixed16.CoreIndex × FixedEnvironment) × FixedPurifier
abbrev OmegaPreIndex := Fin 4 × (SeedIndex × Fin 4)

def omegaPreKet (r : ℝ) (x : OmegaPreIndex) : ℂ :=
  if x.1 = x.2.2 then (1 / 2 : ℂ) * seedBranchKet r x.1 x.2.1 else 0

theorem omegaPreKet_IsNormalized (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    IsNormalized (omegaPreKet r) := by
  have hb (j : Fin 4) : (∑ s : SeedIndex, Complex.normSq (seedBranchKet r j s)) = 1 :=
    seedBranchKet_IsNormalized r hr hr1 j
  change (∑ x : OmegaPreIndex, Complex.normSq (omegaPreKet r x)) = 1
  norm_num [omegaPreKet, Fintype.sum_prod_type, apply_ite,
    Complex.normSq_mul, ← Finset.mul_sum, hb]

def collectFlags : OmegaPreIndex ≃ OmegaIndex where
  toFun := fun x => ((x.2.1.1.1, (x.1, x.2.1.1.2)), (x.2.2, x.2.1.2))
  invFun := fun x => (x.1.2.1, (((x.1.1, x.1.2.2), x.2.2), x.2.1))
  left_inv := by rintro ⟨j, ⟨⟨⟨ab, e⟩, g⟩, k⟩⟩; rfl
  right_inv := by rintro ⟨⟨ab, ⟨j, e⟩⟩, ⟨k, g⟩⟩; rfl

def omegaKet (r : ℝ) : OmegaIndex → ℂ :=
  fun x => omegaPreKet r (collectFlags.symm x)

theorem omegaKet_IsNormalized (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    IsNormalized (omegaKet r) := by
  change (∑ x : OmegaIndex, Complex.normSq (omegaPreKet r (collectFlags.symm x))) = 1
  exact (collectFlags.symm.sum_comp (fun x => Complex.normSq (omegaPreKet r x))).trans
    (omegaPreKet_IsNormalized r hr hr1)

def omegaDensity (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1) : Density OmegaIndex where
  matrix := pureDensity (omegaKet r)
  positive := QuantumProver.WernerEndpoint.pureDensity_posSemidef (omegaKet r)
  trace_one := by
    change Matrix.trace (QuantumProver.WernerEndpoint.pureDensity (omegaKet r)) = 1
    rw [QuantumProver.WernerEndpoint.pureDensity_trace]
    have h := omegaKet_IsNormalized r hr hr1
    change QuantumProver.WernerEndpoint.vectorNormSq (omegaKet r) = 1 at h
    rw [h]
    norm_num

theorem fixedEnvironment_card : Fintype.card FixedEnvironment = 16 := by decide
theorem fixedPurifier_card : Fintype.card FixedPurifier = 16 := by decide

def flagPermutationMatrix (k : Fin 4) : QMatrix (Fin 4) :=
  fun i j => if Fixed16.pauliBranchPermutation k i = j then 1 else 0

theorem flagPermutationMatrix_gram (k : Fin 4) :
    (flagPermutationMatrix k)ᴴ * flagPermutationMatrix k = 1 := by
  fin_cases k <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [flagPermutationMatrix, Fixed16.pauliBranchPermutation,
      Fixed16.pauliBranchIndex, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.one_apply, Fin.sum_univ_succ]

def omegaPrePauli (k : Fin 4) : QMatrix OmegaPreIndex :=
  flagPermutationMatrix k ⊗ₖ (seedPauliLift k ⊗ₖ flagPermutationMatrix k)

theorem omegaPrePauli_apply (k : Fin 4) (v : OmegaPreIndex → ℂ)
    (j q : Fin 4) (s : SeedIndex) :
    (omegaPrePauli k).mulVec v (j, (s, q)) =
      ∑ t : SeedIndex, seedPauliLift k s t *
        v (Fixed16.pauliBranchPermutation k j, (t, Fixed16.pauliBranchPermutation k q)) := by
  simp [omegaPrePauli, flagPermutationMatrix, Matrix.mulVec, dotProduct,
    Matrix.kroneckerMap_apply, Fintype.sum_prod_type]

theorem omegaPreKet_pauli_covariance (k : Fin 4) (r : ℝ) :
    (omegaPrePauli k).mulVec (omegaPreKet r) = omegaPreKet r := by
  funext x
  rcases x with ⟨j, ⟨s, q⟩⟩
  rw [omegaPrePauli_apply]
  have heq : Fixed16.pauliBranchPermutation k j = Fixed16.pauliBranchPermutation k q ↔
      j = q := (Fixed16.pauliBranchPermutation k).injective.eq_iff
  by_cases hjq : j = q
  · subst q
    simp only [omegaPreKet, if_pos rfl]
    have hc := congrFun
      (seedBranchKet_pauli_covariance k (Fixed16.pauliBranchPermutation k j) r) s
    have hi : Fixed16.pauliBranchPermutation k (Fixed16.pauliBranchPermutation k j) = j :=
      (Fixed16.pauliBranchPermutation k).left_inv j
    rw [hi] at hc
    change (∑ t : SeedIndex, seedPauliLift k s t *
      ((1 / 2 : ℂ) * seedBranchKet r (Fixed16.pauliBranchPermutation k j) t)) = _
    calc
      _ = (1 / 2 : ℂ) * (seedPauliLift k).mulVec
          (seedBranchKet r (Fixed16.pauliBranchPermutation k j)) s := by
        simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_left_comm]
      _ = _ := by rw [hc]; simp
  · simp [omegaPreKet, heq, hjq]

def environmentFlagPauli (k : Fin 4) : QMatrix FixedEnvironment :=
  flagPermutationMatrix k ⊗ₖ (1 : QMatrix Fixed16.CoreIndex)

def purifierFlagPauli (k : Fin 4) : QMatrix FixedPurifier :=
  flagPermutationMatrix k ⊗ₖ (1 : QMatrix (Fin 4))

theorem environmentFlagPauli_gram (k : Fin 4) :
    (environmentFlagPauli k)ᴴ * environmentFlagPauli k = 1 := by
  simp only [environmentFlagPauli, Matrix.conjTranspose_kronecker,
    Matrix.conjTranspose_one, ← Matrix.mul_kronecker_mul,
    flagPermutationMatrix_gram, Matrix.one_mul, Matrix.one_kronecker_one]

theorem purifierFlagPauli_gram (k : Fin 4) :
    (purifierFlagPauli k)ᴴ * purifierFlagPauli k = 1 := by
  simp only [purifierFlagPauli, Matrix.conjTranspose_kronecker,
    Matrix.conjTranspose_one, ← Matrix.mul_kronecker_mul,
    flagPermutationMatrix_gram, Matrix.one_mul, Matrix.one_kronecker_one]

def omegaPauli (k : Fin 4) : QMatrix OmegaIndex :=
  (Fixed16.pairedPauli k ⊗ₖ environmentFlagPauli k) ⊗ₖ purifierFlagPauli k

theorem omegaPauli_gram (k : Fin 4) : (omegaPauli k)ᴴ * omegaPauli k = 1 := by
  simp only [omegaPauli, Matrix.conjTranspose_kronecker,
    ← Matrix.mul_kronecker_mul, Fixed16.pairedPauli_gram,
    environmentFlagPauli_gram, purifierFlagPauli_gram, Matrix.one_kronecker_one]

theorem omegaPauli_eq_reindex (k : Fin 4) :
    omegaPauli k = Matrix.reindex collectFlags collectFlags (omegaPrePauli k) := by
  ext x y
  simp [omegaPauli, omegaPrePauli, seedPauliLift, environmentFlagPauli,
    purifierFlagPauli, Matrix.reindex_apply, Matrix.submatrix,
    Matrix.kroneckerMap_apply, collectFlags]
  ring

theorem omegaKet_pauli_covariance (k : Fin 4) (r : ℝ) :
    (omegaPauli k).mulVec (omegaKet r) = omegaKet r := by
  rw [omegaPauli_eq_reindex, Matrix.reindex_apply]
  rw [Matrix.submatrix_mulVec_equiv]
  simp only [Equiv.symm_symm]
  have hv : omegaKet r ∘ collectFlags = omegaPreKet r := by
    funext x
    simp [omegaKet]
  rw [hv, omegaPreKet_pauli_covariance]
  rfl

end QuantumProver.DepolarizingSquashedEntanglement.Identities

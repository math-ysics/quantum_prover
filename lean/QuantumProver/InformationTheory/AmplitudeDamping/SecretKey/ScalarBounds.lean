import QuantumProver.InformationTheory.AmplitudeDamping.SecretKey.Definitions
import QuantumProver.InformationTheory.AmplitudeDamping.SecretKey.KrausBounds
import QuantumProver.InformationTheory.AmplitudeDamping.QuantumCapacity.ComparisonInequalities

noncomputable section

open scoped BigOperators ComplexOrder Kronecker
open Matrix

namespace QuantumProver.AmplitudeDamping.SecretKey

variable {I O J : Type*} [Fintype I] [Fintype O] [Fintype J] [DecidableEq I]

def measurePrepareChannel (v : J → I → ℂ) (b : J → O → ℂ)
    (hv : ∑ j, Matrix.vecMulVec (v j) (star (v j)) = 1)
    (hb : ∀ j, ∑ o, star (b j o) * b j o = 1) : KrausChannel I O J where
  op j := KrausAlgebra.rankOneKraus (v j) (b j)
  complete := KrausAlgebra.rankOneKraus_complete v b hv hb

theorem measurePrepareChannel_eval (v : J → I → ℂ) (b : J → O → ℂ)
    (hv : ∑ j, Matrix.vecMulVec (v j) (star (v j)) = 1)
    (hb : ∀ j, ∑ o, star (b j o) * b j o = 1) (ρ : Matrix I I ℂ) :
    (measurePrepareChannel v b hv hb).eval ρ =
      ∑ j, KrausAlgebra.outcomeWeight (v j) ρ • Matrix.vecMulVec (b j) (star (b j)) := by
  unfold KrausChannel.eval
  apply Finset.sum_congr rfl
  intro j _
  exact KrausAlgebra.rankOneKraus_eval _ _ _

theorem sum_kronecker_mem_separableCone {A B : Type*} [Fintype A] [Fintype B]
    (left : J → Matrix A A ℂ) (right : J → Matrix B B ℂ)
    (hl : ∀ j, (left j).PosSemidef) (hr : ∀ j, (right j).PosSemidef) :
    InSeparableCone (∑ j, left j ⊗ₖ right j) := by
  classical
  let e := Fintype.equivFin J
  refine ⟨Fintype.card J, (fun i => left (e.symm i)),
    (fun i => right (e.symm i)), (fun i => hl _), (fun i => hr _), ?_⟩
  exact (Equiv.sum_comp e.symm (fun j => left j ⊗ₖ right j)).symm

theorem separableCone_finite_sum_B {A B : Type*} [Fintype A] [Fintype B]
    (ρ : J → Matrix (A × B) (A × B) ℂ)
    (hρ : ∀ j, InSeparableCone (ρ j)) : InSeparableCone (∑ j, ρ j) := by
  classical
  simp only [InSeparableCone] at hρ
  choose k left right hleft hright heq using hρ
  have hsum : (∑ j, ρ j) =
      ∑ p : (j : J) × Fin (k j), left p.1 p.2 ⊗ₖ right p.1 p.2 := by
    rw [Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro j _
    exact heq j
  rw [hsum]
  apply sum_kronecker_mem_separableCone
  · intro p
    exact hleft p.1 p.2
  · intro p
    exact hright p.1 p.2

theorem measurePrepareChannel_withMemory_eval {A : Type*}
    [Fintype A] [DecidableEq A] (v : J → I → ℂ) (b : J → O → ℂ)
    (hv : ∑ j, Matrix.vecMulVec (v j) (star (v j)) = 1)
    (hb : ∀ j, ∑ o, star (b j o) * b j o = 1)
    (ρ : Matrix (A × I) (A × I) ℂ) :
    ((measurePrepareChannel v b hv hb).withMemory A).eval ρ =
      ∑ j, (KrausAlgebra.memoryCompression (A := A) (v j) * ρ *
        (KrausAlgebra.memoryCompression (A := A) (v j))ᴴ) ⊗ₖ
          Matrix.vecMulVec (b j) (star (b j)) := by
  unfold KrausChannel.eval
  apply Finset.sum_congr rfl
  intro j _
  exact KrausAlgebra.rankOneKraus_withMemory_eval (A := A) (v j) (b j) ρ

theorem measurePrepareChannel_withMemory_mem_separableCone {A : Type*}
    [Fintype A] [DecidableEq A] (v : J → I → ℂ) (b : J → O → ℂ)
    (hv : ∑ j, Matrix.vecMulVec (v j) (star (v j)) = 1)
    (hb : ∀ j, ∑ o, star (b j o) * b j o = 1)
    {ρ : Matrix (A × I) (A × I) ℂ} (hρ : ρ.PosSemidef) :
    InSeparableCone (((measurePrepareChannel v b hv hb).withMemory A).eval ρ) := by
  rw [measurePrepareChannel_withMemory_eval]
  apply sum_kronecker_mem_separableCone
  · intro j
    exact KrausAlgebra.memoryCompression_posSemidef (A := A) (v j) hρ
  · intro j
    exact Matrix.posSemidef_vecMulVec_self_star _

theorem measurePrepareChannel_onDensity_separable {A : Type*}
    [Fintype A] [DecidableEq A] (v : J → I → ℂ) (b : J → O → ℂ)
    (hv : ∑ j, Matrix.vecMulVec (v j) (star (v j)) = 1)
    (hb : ∀ j, ∑ o, star (b j o) * b j o = 1) (ρ : Density (A × I)) :
    IsSeparable (((measurePrepareChannel v b hv hb).withMemory A).onDensity ρ) := by
  exact measurePrepareChannel_withMemory_mem_separableCone v b hv hb ρ.positive

namespace KrausChannel

theorem eval_finite_sum_B {L : Type*} [Fintype L] (C : KrausChannel I O J)
    (ρ : L → Matrix I I ℂ) : C.eval (∑ l, ρ l) = ∑ l, C.eval (ρ l) := by
  simp only [eval, Matrix.mul_sum, Matrix.sum_mul]
  exact Finset.sum_comm

theorem eval_withRightMemory_kronecker_B {B : Type*} [Fintype B]
    [DecidableEq B] (C : KrausChannel I O J)
    (ρ : Matrix I I ℂ) (β : Matrix B B ℂ) :
    (C.withRightMemory B).eval (ρ ⊗ₖ β) = C.eval ρ ⊗ₖ β := by
  simp only [eval, withRightMemory, Matrix.conjTranspose_kronecker,
    Matrix.conjTranspose_one, ← Matrix.mul_kronecker_mul,
    Matrix.one_mul, Matrix.mul_one]
  ext x y
  simp [Matrix.sum_apply, Matrix.kroneckerMap_apply, Finset.sum_mul]

end KrausChannel

theorem reindex_finite_sum_B {L A B : Type*} [Fintype L]
    (e : A ≃ B) (ρ : L → Matrix A A ℂ) :
    Matrix.reindex e e (∑ l, ρ l) = ∑ l, Matrix.reindex e e (ρ l) := by
  ext x y
  simp [Matrix.reindex_apply, Matrix.submatrix, Matrix.sum_apply]

theorem local_product_sandwich_B {A B A' B' : Type*} [Fintype A] [Fintype B]
    (K : Matrix A' A ℂ) (L : Matrix B' B ℂ)
    (α : Matrix A A ℂ) (β : Matrix B B ℂ) :
    (K ⊗ₖ L) * (α ⊗ₖ β) * (K ⊗ₖ L)ᴴ =
      (K * α * Kᴴ) ⊗ₖ (L * β * Lᴴ) := by
  rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
    ← Matrix.mul_kronecker_mul]

theorem separableCone_local_product_B {A B A' B' : Type*}
    [Fintype A] [Fintype B] [Fintype A'] [Fintype B']
    (K : Matrix A' A ℂ) (L : Matrix B' B ℂ)
    {σ : Matrix (A × B) (A × B) ℂ} (hσ : InSeparableCone σ) :
    InSeparableCone ((K ⊗ₖ L) * σ * (K ⊗ₖ L)ᴴ) := by
  obtain ⟨k, left, right, hleft, hright, rfl⟩ := hσ
  have heval : (K ⊗ₖ L) * (∑ j, left j ⊗ₖ right j) * (K ⊗ₖ L)ᴴ =
      ∑ j, (K * left j * Kᴴ) ⊗ₖ (L * right j * Lᴴ) := by
    rw [Matrix.mul_sum, Matrix.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    exact local_product_sandwich_B _ _ _ _
  rw [heval]
  apply sum_kronecker_mem_separableCone
  · intro j
    exact (hleft j).mul_mul_conjTranspose_same K
  · intro j
    exact (hright j).mul_mul_conjTranspose_same L

theorem measurePrepareChannel_transfer_product {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (v : J → I → ℂ) (b : J → O → ℂ)
    (hv : ∑ j, Matrix.vecMulVec (v j) (star (v j)) = 1)
    (hb : ∀ j, ∑ o, star (b j o) * b j o = 1)
    (ρ : Matrix (A × I) (A × I) ℂ) (β : Matrix B B ℂ) :
    Matrix.reindex (Equiv.prodAssoc A O B) (Equiv.prodAssoc A O B)
      ((((measurePrepareChannel v b hv hb).withMemory A).withRightMemory B).eval
        (ρ ⊗ₖ β)) =
      ∑ j, (KrausAlgebra.memoryCompression (A := A) (v j) * ρ *
        (KrausAlgebra.memoryCompression (A := A) (v j))ᴴ) ⊗ₖ
          (Matrix.vecMulVec (b j) (star (b j)) ⊗ₖ β) := by
  rw [KrausChannel.eval_withRightMemory_kronecker_B,
    measurePrepareChannel_withMemory_eval]
  ext x y
  simp [Matrix.reindex_apply, Matrix.submatrix, Matrix.kroneckerMap_apply,
    Matrix.sum_apply, Finset.sum_mul, mul_assoc]

theorem measurePrepareChannel_transfer_mem_separableCone {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] [DecidableEq O]
    (v : J → I → ℂ) (b : J → O → ℂ)
    (hv : ∑ j, Matrix.vecMulVec (v j) (star (v j)) = 1)
    (hb : ∀ j, ∑ o, star (b j o) * b j o = 1)
    {σ : Matrix ((A × I) × B) ((A × I) × B) ℂ}
    (hσ : InSeparableCone σ) :
    InSeparableCone (Matrix.reindex (Equiv.prodAssoc A O B) (Equiv.prodAssoc A O B)
      ((((measurePrepareChannel v b hv hb).withMemory A).withRightMemory B).eval σ)) := by
  obtain ⟨k, left, right, hleft, hright, rfl⟩ := hσ
  have heval : Matrix.reindex (Equiv.prodAssoc A O B) (Equiv.prodAssoc A O B)
      ((((measurePrepareChannel v b hv hb).withMemory A).withRightMemory B).eval
        (∑ l, left l ⊗ₖ right l)) =
      ∑ p : Fin k × J,
        (KrausAlgebra.memoryCompression (A := A) (v p.2) * left p.1 *
          (KrausAlgebra.memoryCompression (A := A) (v p.2))ᴴ) ⊗ₖ
          (Matrix.vecMulVec (b p.2) (star (b p.2)) ⊗ₖ right p.1) := by
    rw [KrausChannel.eval_finite_sum_B, reindex_finite_sum_B,
      Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro l _
    exact measurePrepareChannel_transfer_product v b hv hb (left l) (right l)
  rw [heval]
  apply sum_kronecker_mem_separableCone
  · intro p
    exact KrausAlgebra.memoryCompression_posSemidef (A := A) (v p.2) (hleft p.1)
  · intro p
    exact (Matrix.posSemidef_vecMulVec_self_star _).kronecker (hright p.1)

namespace ProbabilityLaw

theorem copiedMatrix_mem_separableCone_B [DecidableEq J] (a : ProbabilityLaw J) :
    InSeparableCone a.copiedMatrix := by
  classical
  let left (j : J) : Matrix J J ℂ :=
    Matrix.diagonal fun i => if i = j then (a.weight j : ℂ) else 0
  let right (j : J) : Matrix J J ℂ :=
    Matrix.diagonal fun i => if i = j then 1 else 0
  have heq : a.copiedMatrix = ∑ j, left j ⊗ₖ right j := by
    ext x y
    rcases x with ⟨i, j⟩
    rcases y with ⟨k, l⟩
    simp only [copiedMatrix, left, right, Matrix.diagonal_apply,
      Matrix.sum_apply, Matrix.kroneckerMap_apply]
    rw [Finset.sum_eq_single i]
    · by_cases h₁ : i = k <;> by_cases h₂ : j = l <;>
        by_cases h₃ : i = j <;> simp [h₁, h₂, h₃, eq_comm]
    · intro s _ hs
      simp [hs, Ne.symm hs]
    · simp
  rw [heq]
  apply sum_kronecker_mem_separableCone
  · intro j
    apply Matrix.PosSemidef.diagonal
    intro i
    dsimp [left]
    split_ifs
    · exact_mod_cast a.nonnegative j
    · exact le_refl 0
  · intro j
    apply Matrix.PosSemidef.diagonal
    intro i
    dsimp [right]
    split_ifs
    · exact zero_le_one
    · exact le_refl 0

theorem copiedDensity_separable_B [DecidableEq J] (a : ProbabilityLaw J) :
    IsSeparable a.copiedDensity := copiedMatrix_mem_separableCone_B a

end ProbabilityLaw

namespace FixedWeight

open QuantumProver.AmplitudeDamping.FiniteModel

def lossChannel_B (n w r : ℕ) (hrw : r ≤ w) :
    KrausChannel (WeightBasisB n w) (Finset (Fin n)) (Finset (Fin n)) where
  op := lossKrausB n w r
  complete := lossKrausB_complete n w r hrw

def phaseChannel_B (n w r : ℕ) (hrn : r ≤ n) :
    KrausChannel (WeightBasisB n w) (Finset (Fin n)) (Fin n → ZMod 3) :=
  measurePrepareChannel (phaseInputVectorB n w) (phaseOutputVectorB n r)
    (phaseInputVectorB_complete n w) (phaseOutputVectorB_normalized n r hrn)

theorem phaseChannel_B_op (n w r : ℕ) (hrn : r ≤ n) (z : Fin n → ZMod 3) :
    (phaseChannel_B n w r hrn).op z = measurePhaseKrausB n w r z :=
  (measurePhaseKrausB_rankOne n w r z).symm

theorem phaseChannel_B_reference_eval (n w r : ℕ) (hrn : r ≤ n)
    (R : Type*) [Fintype R] [DecidableEq R]
    (ρ : Matrix (WeightBasisB n w × R) (WeightBasisB n w × R) ℂ) :
    ((phaseChannel_B n w r hrn).withRightMemory R).eval ρ =
      krausSumB (referenceKrausB (measurePhaseKrausB n w r) R) ρ := by
  simp only [KrausChannel.eval, KrausChannel.withRightMemory]
  simp_rw [phaseChannel_B_op]
  rfl

theorem lossChannel_B_reference_eval (n w r : ℕ) (hrw : r ≤ w)
    (R : Type*) [Fintype R] [DecidableEq R]
    (ρ : Matrix (WeightBasisB n w × R) (WeightBasisB n w × R) ℂ) :
    ((lossChannel_B n w r hrw).withRightMemory R).eval ρ =
      krausSumB (referenceKrausB (lossKrausB n w r) R) ρ := rfl

theorem loss_phase_reference_domination_B (n w r : ℕ) (hrw : r ≤ w) (hrn : r ≤ n)
    (R : Type*) [Fintype R] [DecidableEq R]
    {ρ : Matrix (WeightBasisB n w × R) (WeightBasisB n w × R) ℂ}
    (hρ : ρ.PosSemidef) :
    ((phaseComparisonConstantB n w r) •
      ((phaseChannel_B n w r hrn).withRightMemory R).eval ρ -
        ((lossChannel_B n w r hrw).withRightMemory R).eval ρ).PosSemidef := by
  rw [phaseChannel_B_reference_eval, lossChannel_B_reference_eval]
  exact measurePhaseChannelB_reference_loss_domination n w r hrw hrn R hρ

theorem phaseChannel_transfer_separable_B (n w r : ℕ) (hrn : r ≤ n)
    {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {σ : Matrix ((A × WeightBasisB n w) × B) ((A × WeightBasisB n w) × B) ℂ}
    (hσ : InSeparableCone σ) :
    InSeparableCone
      (Matrix.reindex (Equiv.prodAssoc A (Finset (Fin n)) B)
        (Equiv.prodAssoc A (Finset (Fin n)) B)
        ((((phaseChannel_B n w r hrn).withMemory A).withRightMemory B).eval σ)) := by
  exact measurePrepareChannel_transfer_mem_separableCone
    (phaseInputVectorB n w) (phaseOutputVectorB n r)
    (phaseInputVectorB_complete n w) (phaseOutputVectorB_normalized n r hrn) hσ

def weightedPhaseChannel_B (n w : ℕ) (hwn : w ≤ n)
    (mu : Fin (w + 1) → ℝ) (hmu : ∀ r, 0 ≤ mu r) (hsum : ∑ r, mu r = 1) :
    KrausChannel (WeightBasisB n w) (Finset (Fin n)) (survivorPhaseLabelB n w) :=
  measurePrepareChannel (weightedPhaseInputVectorB n w mu)
    (weightedPhaseOutputVectorB n w)
    (weightedPhaseInputVectorB_complete n w mu hmu hsum)
    (weightedPhaseOutputVectorB_normalized n w hwn)

theorem weightedPhaseChannel_B_op (n w : ℕ) (hwn : w ≤ n)
    (mu : Fin (w + 1) → ℝ) (hmu : ∀ r, 0 ≤ mu r) (hsum : ∑ r, mu r = 1)
    (j : survivorPhaseLabelB n w) :
    (weightedPhaseChannel_B n w hwn mu hmu hsum).op j = weightedPhaseKrausB n w mu j :=
  rfl

theorem weightedPhaseChannel_B_reference_eval (n w : ℕ) (hwn : w ≤ n)
    (mu : Fin (w + 1) → ℝ) (hmu : ∀ r, 0 ≤ mu r) (hsum : ∑ r, mu r = 1)
    (R : Type*) [Fintype R] [DecidableEq R]
    (ρ : Matrix (WeightBasisB n w × R) (WeightBasisB n w × R) ℂ) :
    ((weightedPhaseChannel_B n w hwn mu hmu hsum).withRightMemory R).eval ρ =
      ∑ r : Fin (w + 1), mu r •
        krausSumB (referenceKrausB (measurePhaseKrausB n w r.val) R) ρ := by
  change krausSumB (referenceKrausB (weightedPhaseKrausB n w mu) R) ρ = _
  exact weightedPhaseChannelB_reference_eq n w mu hmu R ρ

theorem weightedPhaseChannel_transfer_separable_B (n w : ℕ) (hwn : w ≤ n)
    (mu : Fin (w + 1) → ℝ) (hmu : ∀ r, 0 ≤ mu r) (hsum : ∑ r, mu r = 1)
    {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {σ : Matrix ((A × WeightBasisB n w) × B) ((A × WeightBasisB n w) × B) ℂ}
    (hσ : InSeparableCone σ) :
    InSeparableCone
      (Matrix.reindex (Equiv.prodAssoc A (Finset (Fin n)) B)
        (Equiv.prodAssoc A (Finset (Fin n)) B)
        ((((weightedPhaseChannel_B n w hwn mu hmu hsum).withMemory A).withRightMemory B).eval σ)) := by
  exact measurePrepareChannel_transfer_mem_separableCone
    (weightedPhaseInputVectorB n w mu) (weightedPhaseOutputVectorB n w)
    (weightedPhaseInputVectorB_complete n w mu hmu hsum)
    (weightedPhaseOutputVectorB_normalized n w hwn) hσ

def physicalPhaseChannel_B (n w : ℕ) (hwn : w ≤ n)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    KrausChannel (WeightBasisB n w) (Finset (Fin n)) (survivorPhaseLabelB n w) :=
  weightedPhaseChannel_B n w hwn (physicalPhaseLawB p w)
    (physicalPhaseLawB_nonneg p hp0 hp1 w) (physicalPhaseLawB_sum p w)

def optimizedPhaseChannel_B (n w : ℕ) (hwn : w ≤ n)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (z : ℝ) :
    KrausChannel (WeightBasisB n w) (Finset (Fin n)) (survivorPhaseLabelB n w) :=
  weightedPhaseChannel_B n w hwn (optimizedPhaseLawB n w p z)
    (optimizedPhaseLawB_nonneg n w hwn p hp0 hp1 z)
    (optimizedPhaseLawB_sum n w hwn p hp0 hp1 z)

theorem optimizedPhaseChannel_B_op (n w : ℕ) (hwn : w ≤ n)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (z : ℝ)
    (j : survivorPhaseLabelB n w) :
    (optimizedPhaseChannel_B n w hwn p hp0 hp1 z).op j =
      optimizedPhaseKrausB n w p z j := rfl

theorem optimizedPhaseChannel_B_reference_eval (n w : ℕ) (hwn : w ≤ n)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (z : ℝ)
    (R : Type*) [Fintype R] [DecidableEq R]
    (ρ : Matrix (WeightBasisB n w × R) (WeightBasisB n w × R) ℂ) :
    ((optimizedPhaseChannel_B n w hwn p hp0 hp1 z).withRightMemory R).eval ρ =
      ∑ r : Fin (w + 1), optimizedPhaseLawB n w p z r •
        krausSumB (referenceKrausB (measurePhaseKrausB n w r.val) R) ρ := by
  exact weightedPhaseChannel_B_reference_eval n w hwn (optimizedPhaseLawB n w p z)
    (optimizedPhaseLawB_nonneg n w hwn p hp0 hp1 z)
    (optimizedPhaseLawB_sum n w hwn p hp0 hp1 z) R ρ

theorem optimizedPhaseChannel_transfer_separable_B (n w : ℕ) (hwn : w ≤ n)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (z : ℝ)
    {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {σ : Matrix ((A × WeightBasisB n w) × B) ((A × WeightBasisB n w) × B) ℂ}
    (hσ : InSeparableCone σ) :
    InSeparableCone
      (Matrix.reindex (Equiv.prodAssoc A (Finset (Fin n)) B)
        (Equiv.prodAssoc A (Finset (Fin n)) B)
        ((((optimizedPhaseChannel_B n w hwn p hp0 hp1 z).withMemory A).withRightMemory B).eval σ)) := by
  exact weightedPhaseChannel_transfer_separable_B n w hwn
    (optimizedPhaseLawB n w p z)
    (optimizedPhaseLawB_nonneg n w hwn p hp0 hp1 z)
    (optimizedPhaseLawB_sum n w hwn p hp0 hp1 z) hσ

end FixedWeight

end QuantumProver.AmplitudeDamping.SecretKey

namespace QuantumProver.AmplitudeDamping.SecretKey.Operator

open scoped MatrixOrder Matrix.Norms.L2Operator

variable {I : Type*} [Fintype I] [DecidableEq I]

def positivePower (M : Matrix I I ℂ) (t : ℝ) : Matrix I I ℂ := CFC.rpow M t

theorem positivePower_mono {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    {M N : Matrix I I ℂ} (hMN : M ≤ N) : positivePower M t ≤ positivePower N t := by
  exact CFC.rpow_le_rpow ⟨ht0, ht1⟩ hMN

theorem positivePower_neg_antitone {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (M N : (Matrix I I ℂ)ˣ) (hM : 0 ≤ (M : Matrix I I ℂ))
    (hMN : (M : Matrix I I ℂ) ≤ (N : Matrix I I ℂ)) :
    positivePower (N : Matrix I I ℂ) (-t) ≤ positivePower (M : Matrix I I ℂ) (-t) := by
  unfold positivePower
  calc
    CFC.rpow (N : Matrix I I ℂ) (-t) = CFC.rpow (↑N⁻¹ : Matrix I I ℂ) t := by
      simpa only [CFC.rpow_eq_pow] using
        (CFC.rpow_neg (A := Matrix I I ℂ) N t (le_trans hM hMN))
    _ ≤ CFC.rpow (↑M⁻¹ : Matrix I I ℂ) t :=
      CFC.rpow_le_rpow ⟨ht0, ht1⟩ (CStarAlgebra.inv_le_inv hM hMN)
    _ = CFC.rpow (M : Matrix I I ℂ) (-t) := by
      simpa only [CFC.rpow_eq_pow] using
        (CFC.rpow_neg (A := Matrix I I ℂ) M t hM).symm

end QuantumProver.AmplitudeDamping.SecretKey.Operator

namespace QuantumProver.AmplitudeDamping.SecretKey.PublicHistory

variable {F A B : Type*} [Fintype F] [Fintype A] [Fintype B]
  [DecidableEq F] [DecidableEq A] [DecidableEq B]

def attachFlag_B (j : F) : Matrix (F × A) A ℂ :=
  fun x a => if x.1 = j then (1 : Matrix A A ℂ) x.2 a else 0

theorem attachFlag_complete_B (j : F) :
    (attachFlag_B (A := A) j)ᴴ * attachFlag_B (A := A) j = 1 := by
  classical
  ext a a'
  simp [attachFlag_B, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fintype.sum_prod_type, Matrix.one_apply, ite_mul, mul_ite, eq_comm]

def publicBranch_B (j : F) (σ : Matrix (A × B) (A × B) ℂ) :
    Matrix ((F × A) × (F × B)) ((F × A) × (F × B)) ℂ :=
  (attachFlag_B (A := A) j ⊗ₖ attachFlag_B (A := B) j) * σ *
    (attachFlag_B (A := A) j ⊗ₖ attachFlag_B (A := B) j)ᴴ

theorem attachFlag_pair_complete_B (j : F) :
    (attachFlag_B (A := A) j ⊗ₖ attachFlag_B (A := B) j)ᴴ *
      (attachFlag_B (A := A) j ⊗ₖ attachFlag_B (A := B) j) = 1 := by
  rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
    attachFlag_complete_B, attachFlag_complete_B, Matrix.one_kronecker_one]

theorem publicBranch_apply_B (j i k i' k' : F)
    (σ : Matrix (A × B) (A × B) ℂ) (a a' : A) (b b' : B) :
    publicBranch_B j σ ((i, a), (k, b)) ((i', a'), (k', b')) =
      if i = j ∧ k = j ∧ i' = j ∧ k' = j then σ (a, b) (a', b') else 0 := by
  classical
  by_cases hi : i = j <;> by_cases hk : k = j <;>
    by_cases hi' : i' = j <;> by_cases hk' : k' = j <;>
    simp [publicBranch_B, attachFlag_B, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Matrix.kroneckerMap_apply,
      Fintype.sum_prod_type, Matrix.one_apply, hi, hk, hi', hk', ite_mul, mul_ite, apply_ite]

theorem publicBranch_trace_B (j : F) (σ : Matrix (A × B) (A × B) ℂ) :
    (publicBranch_B j σ).trace = σ.trace := by
  rw [publicBranch_B, Matrix.trace_mul_cycle, attachFlag_pair_complete_B,
    Matrix.one_mul]

theorem publicBranch_mem_separableCone_B (j : F)
    {σ : Matrix (A × B) (A × B) ℂ} (hσ : QuantumProver.AmplitudeDamping.SecretKey.InSeparableCone σ) :
    QuantumProver.AmplitudeDamping.SecretKey.InSeparableCone (publicBranch_B j σ) := by
  exact QuantumProver.AmplitudeDamping.SecretKey.separableCone_local_product_B
    (attachFlag_B (A := A) j) (attachFlag_B (A := B) j) hσ

def copyPublicHistory_B (σ : F → Matrix (A × B) (A × B) ℂ) :
    Matrix ((F × A) × (F × B)) ((F × A) × (F × B)) ℂ :=
  ∑ j, publicBranch_B j (σ j)

theorem copyPublicHistory_apply_B (σ : F → Matrix (A × B) (A × B) ℂ)
    (i k i' k' : F) (a a' : A) (b b' : B) :
    copyPublicHistory_B σ ((i, a), (k, b)) ((i', a'), (k', b')) =
      if i = k ∧ i = i' ∧ i = k' then σ i (a, b) (a', b') else 0 := by
  classical
  simp only [copyPublicHistory_B, Matrix.sum_apply, publicBranch_apply_B]
  rw [Finset.sum_eq_single i]
  · simp [eq_comm]
  · intro j _ hj
    simp [Ne.symm hj]
  · simp

theorem copyPublicHistory_trace_B (σ : F → Matrix (A × B) (A × B) ℂ) :
    (copyPublicHistory_B σ).trace = ∑ j, (σ j).trace := by
  simp only [copyPublicHistory_B, Matrix.trace_sum, publicBranch_trace_B]

theorem copyPublicHistory_mem_separableCone_B
    (σ : F → Matrix (A × B) (A × B) ℂ)
    (hσ : ∀ j, QuantumProver.AmplitudeDamping.SecretKey.InSeparableCone (σ j)) :
    QuantumProver.AmplitudeDamping.SecretKey.InSeparableCone (copyPublicHistory_B σ) := by
  exact QuantumProver.AmplitudeDamping.SecretKey.separableCone_finite_sum_B
    (fun j => publicBranch_B j (σ j))
    (fun j => publicBranch_mem_separableCone_B j (hσ j))

theorem isometry_left_gram_B {I O P : Type*} [Fintype O] [Fintype P]
    [DecidableEq O] (V : Matrix P O ℂ) (K : Matrix O I ℂ)
    (hV : Vᴴ * V = 1) : (V * K)ᴴ * (V * K) = Kᴴ * K := by
  calc
    _ = Kᴴ * (Vᴴ * V) * K := by
      simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = _ := by rw [hV, Matrix.mul_one]

variable {A' B' J K : Type*} [Fintype A'] [Fintype B'] [Fintype J] [Fintype K]
  [DecidableEq A'] [DecidableEq B'] [DecidableEq J] [DecidableEq K]

def publicProductOperator_B (C : QuantumProver.AmplitudeDamping.SecretKey.KrausChannel A A' J)
    (D : J → QuantumProver.AmplitudeDamping.SecretKey.KrausChannel B B' K) (f : J × K) :
    Matrix (((J × K) × A') × ((J × K) × B')) (A × B) ℂ :=
  (attachFlag_B (A := A') f ⊗ₖ attachFlag_B (A := B') f) *
    (C.op f.1 ⊗ₖ (D f.1).op f.2)

theorem publicProductOperator_gram_B (C : QuantumProver.AmplitudeDamping.SecretKey.KrausChannel A A' J)
    (D : J → QuantumProver.AmplitudeDamping.SecretKey.KrausChannel B B' K) (f : J × K) :
    (publicProductOperator_B C D f)ᴴ * publicProductOperator_B C D f =
      ((C.op f.1)ᴴ * C.op f.1) ⊗ₖ (((D f.1).op f.2)ᴴ * (D f.1).op f.2) := by
  calc
    _ = (C.op f.1 ⊗ₖ (D f.1).op f.2)ᴴ *
        (C.op f.1 ⊗ₖ (D f.1).op f.2) :=
      isometry_left_gram_B _ _ (attachFlag_pair_complete_B f)
    _ = _ := by
      rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul]

def copiedLocalInstrument_B (C : QuantumProver.AmplitudeDamping.SecretKey.KrausChannel A A' J)
    (D : J → QuantumProver.AmplitudeDamping.SecretKey.KrausChannel B B' K) :
    QuantumProver.AmplitudeDamping.SecretKey.KrausChannel (A × B)
      (((J × K) × A') × ((J × K) × B')) (J × K) where
  op := publicProductOperator_B C D
  complete := by
    calc
      _ = ∑ j : J, ((C.op j)ᴴ * C.op j) ⊗ₖ (1 : Matrix B B ℂ) := by
        simp_rw [publicProductOperator_gram_B]
        rw [Fintype.sum_prod_type]
        apply Finset.sum_congr rfl
        intro j _
        ext x y
        simp only [Matrix.sum_apply, Matrix.kroneckerMap_apply]
        rw [← Finset.mul_sum, ← Matrix.sum_apply, (D j).complete]
      _ = (1 : Matrix A A ℂ) ⊗ₖ (1 : Matrix B B ℂ) := by
        ext x y
        simp only [Matrix.sum_apply, Matrix.kroneckerMap_apply]
        rw [← Finset.sum_mul, ← Matrix.sum_apply, C.complete]
      _ = 1 := Matrix.one_kronecker_one

theorem copiedLocalInstrument_eval_B (C : QuantumProver.AmplitudeDamping.SecretKey.KrausChannel A A' J)
    (D : J → QuantumProver.AmplitudeDamping.SecretKey.KrausChannel B B' K)
    (ρ : Matrix (A × B) (A × B) ℂ) :
    (copiedLocalInstrument_B C D).eval ρ =
      copyPublicHistory_B (fun f : J × K =>
        (C.op f.1 ⊗ₖ (D f.1).op f.2) * ρ *
          (C.op f.1 ⊗ₖ (D f.1).op f.2)ᴴ) := by
  unfold QuantumProver.AmplitudeDamping.SecretKey.KrausChannel.eval copyPublicHistory_B
  apply Finset.sum_congr rfl
  intro f _
  simp only [copiedLocalInstrument_B, publicProductOperator_B, publicBranch_B,
    Matrix.conjTranspose_mul, Matrix.mul_assoc]

theorem copiedLocalInstrument_trace_B (C : QuantumProver.AmplitudeDamping.SecretKey.KrausChannel A A' J)
    (D : J → QuantumProver.AmplitudeDamping.SecretKey.KrausChannel B B' K)
    (ρ : Matrix (A × B) (A × B) ℂ) :
    ((copiedLocalInstrument_B C D).eval ρ).trace = ρ.trace :=
  (copiedLocalInstrument_B C D).trace_eval ρ

theorem copiedLocalInstrument_mem_separableCone_B
    (C : QuantumProver.AmplitudeDamping.SecretKey.KrausChannel A A' J)
    (D : J → QuantumProver.AmplitudeDamping.SecretKey.KrausChannel B B' K)
    {σ : Matrix (A × B) (A × B) ℂ} (hσ : QuantumProver.AmplitudeDamping.SecretKey.InSeparableCone σ) :
    QuantumProver.AmplitudeDamping.SecretKey.InSeparableCone ((copiedLocalInstrument_B C D).eval σ) := by
  rw [copiedLocalInstrument_eval_B]
  apply copyPublicHistory_mem_separableCone_B
  intro f
  exact QuantumProver.AmplitudeDamping.SecretKey.separableCone_local_product_B
    (C.op f.1) ((D f.1).op f.2) hσ

end QuantumProver.AmplitudeDamping.SecretKey.PublicHistory

namespace QuantumProver.AmplitudeDamping.SecretKey.PhaseRecovery

variable {I O J : Type*} [Fintype I] [Fintype O] [Fintype J]
  [DecidableEq I] [DecidableEq O] [DecidableEq J]

def retainedKrausMatrix_B (K : J → Matrix O I ℂ) : Matrix (O × J) I ℂ :=
  fun oj i => K oj.2 oj.1 i

theorem retainedKrausMatrix_eq_stinespring_B (C : QuantumProver.AmplitudeDamping.SecretKey.KrausChannel I O J) :
    retainedKrausMatrix_B C.op = C.stinespring := rfl

theorem retainedKrausMatrix_environment_action_B (K : J → Matrix O I ℂ)
    (Dout : Matrix O O ℂ) (χ : J → ℂ) :
    (Dout ⊗ₖ Matrix.diagonal χ) * retainedKrausMatrix_B K =
      fun oj i => χ oj.2 * (Dout * K oj.2) oj.1 i := by
  classical
  ext ⟨o, j⟩ i
  simp [Matrix.mul_apply, Matrix.kroneckerMap_apply, Matrix.diagonal_apply,
    retainedKrausMatrix_B, Fintype.sum_prod_type, mul_ite, ite_mul,
    Finset.mul_sum, mul_assoc, mul_comm, mul_left_comm]

theorem retainedKrausMatrix_intertwining_B (K : J → Matrix O I ℂ)
    (Din : Matrix I I ℂ) (Dout : Matrix O O ℂ) (χ : J → ℂ)
    (hK : ∀ j, K j * Din = χ j • (Dout * K j)) :
    retainedKrausMatrix_B K * Din =
      (Dout ⊗ₖ Matrix.diagonal χ) * retainedKrausMatrix_B K := by
  rw [retainedKrausMatrix_environment_action_B]
  ext ⟨o, j⟩ i
  change (K j * Din) o i = χ j * (Dout * K j) o i
  simpa only [Matrix.smul_apply, smul_eq_mul] using
    congrArg (fun M : Matrix O I ℂ => M o i) (hK j)

theorem retainedKrausMatrix_phase_correction_B (K : J → Matrix O I ℂ)
    (Din : Matrix I I ℂ) (Dout : Matrix O O ℂ) (χ : J → ℂ)
    (hK : ∀ j, K j * Din = χ j • (Dout * K j)) (hDin : Din * Dinᴴ = 1) :
    (Dout ⊗ₖ Matrix.diagonal χ) * retainedKrausMatrix_B K * Dinᴴ =
      retainedKrausMatrix_B K := by
  rw [← retainedKrausMatrix_intertwining_B K Din Dout χ hK,
    Matrix.mul_assoc, hDin, Matrix.mul_one]

theorem stinespring_phase_correction_B (C : QuantumProver.AmplitudeDamping.SecretKey.KrausChannel I O J)
    (Din : Matrix I I ℂ) (Dout : Matrix O O ℂ) (χ : J → ℂ)
    (hK : ∀ j, C.op j * Din = χ j • (Dout * C.op j)) (hDin : Din * Dinᴴ = 1) :
    (Dout ⊗ₖ Matrix.diagonal χ) * C.stinespring * Dinᴴ = C.stinespring :=
  retainedKrausMatrix_phase_correction_B C.op Din Dout χ hK hDin

theorem retainedKrausMatrix_joint_phase_correction_B (K : J → Matrix O I ℂ)
    (Din : Matrix I I ℂ) (Dout : Matrix O O ℂ) (χ : J → ℂ)
    (hK : ∀ j, K j * Din = χ j • (Dout * K j)) (hDin : Din * Dinᴴ = 1)
    (ρ : Matrix I I ℂ) :
    (Dout ⊗ₖ Matrix.diagonal χ) *
      (retainedKrausMatrix_B K * (Dinᴴ * ρ * Din) * (retainedKrausMatrix_B K)ᴴ) *
        (Dout ⊗ₖ Matrix.diagonal χ)ᴴ =
          retainedKrausMatrix_B K * ρ * (retainedKrausMatrix_B K)ᴴ := by
  have hc := retainedKrausMatrix_phase_correction_B K Din Dout χ hK hDin
  have ha : Din * (retainedKrausMatrix_B K)ᴴ * (Dout ⊗ₖ Matrix.diagonal χ)ᴴ =
      (retainedKrausMatrix_B K)ᴴ := by
    simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.mul_assoc] using congrArg Matrix.conjTranspose hc
  calc
    _ = ((Dout ⊗ₖ Matrix.diagonal χ) * retainedKrausMatrix_B K * Dinᴴ) * ρ *
        (Din * (retainedKrausMatrix_B K)ᴴ * (Dout ⊗ₖ Matrix.diagonal χ)ᴴ) := by
      simp only [Matrix.mul_assoc]
    _ = _ := by rw [hc, ha]

theorem stinespring_joint_phase_correction_B (C : QuantumProver.AmplitudeDamping.SecretKey.KrausChannel I O J)
    (Din : Matrix I I ℂ) (Dout : Matrix O O ℂ) (χ : J → ℂ)
    (hK : ∀ j, C.op j * Din = χ j • (Dout * C.op j)) (hDin : Din * Dinᴴ = 1)
    (ρ : Matrix I I ℂ) :
    (Dout ⊗ₖ Matrix.diagonal χ) * C.jointOutput (Dinᴴ * ρ * Din) *
      (Dout ⊗ₖ Matrix.diagonal χ)ᴴ = C.jointOutput ρ := by
  have hc := stinespring_phase_correction_B C Din Dout χ hK hDin
  have ha : Din * C.stinespringᴴ * (Dout ⊗ₖ Matrix.diagonal χ)ᴴ = C.stinespringᴴ := by
    simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.mul_assoc] using congrArg Matrix.conjTranspose hc
  unfold QuantumProver.AmplitudeDamping.SecretKey.KrausChannel.jointOutput
  calc
    _ = ((Dout ⊗ₖ Matrix.diagonal χ) * C.stinespring * Dinᴴ) * ρ *
        (Din * C.stinespringᴴ * (Dout ⊗ₖ Matrix.diagonal χ)ᴴ) := by
      simp only [Matrix.mul_assoc]
    _ = _ := by rw [hc, ha]

theorem diagonalPhase_isometry_B (χ : J → ℂ) (hχ : ∀ j, star (χ j) * χ j = 1) :
    (Matrix.diagonal χ)ᴴ * Matrix.diagonal χ = 1 := by
  rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
  calc
    _ = Matrix.diagonal (fun _ : J => (1 : ℂ)) := by
      congr 1
      funext j
      exact hχ j
    _ = 1 := Matrix.diagonal_one

theorem phaseCorrection_isometry_B (Dout : Matrix O O ℂ) (χ : J → ℂ)
    (hDout : Doutᴴ * Dout = 1) (hχ : ∀ j, star (χ j) * χ j = 1) :
    (Dout ⊗ₖ Matrix.diagonal χ)ᴴ * (Dout ⊗ₖ Matrix.diagonal χ) = 1 := by
  rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
    hDout, diagonalPhase_isometry_B χ hχ, Matrix.one_kronecker_one]

theorem diagonalPhase_coisometry_B (χ : J → ℂ) (hχ : ∀ j, star (χ j) * χ j = 1) :
    Matrix.diagonal χ * (Matrix.diagonal χ)ᴴ = 1 := by
  rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
  calc
    _ = Matrix.diagonal (fun _ : J => (1 : ℂ)) := by
      congr 1
      funext j
      simpa only [Pi.star_apply, mul_comm] using hχ j
    _ = 1 := Matrix.diagonal_one

theorem phaseCorrection_coisometry_B (Dout : Matrix O O ℂ) (χ : J → ℂ)
    (hDout : Dout * Doutᴴ = 1) (hχ : ∀ j, star (χ j) * χ j = 1) :
    (Dout ⊗ₖ Matrix.diagonal χ) * (Dout ⊗ₖ Matrix.diagonal χ)ᴴ = 1 := by
  rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
    hDout, diagonalPhase_coisometry_B χ hχ, Matrix.one_kronecker_one]

open QuantumProver.AmplitudeDamping.FiniteModel QuantumProver.AmplitudeDamping.SecretKey.Phase

def fullLossRetainedMatrix_B (n : ℕ) (p : ℝ) :
    Matrix (Finset (Fin n) × Finset (Fin n)) (Finset (Fin n)) ℂ :=
  retainedKrausMatrix_B (physicalTensorKrausB n p)

theorem fullLossRetained_phase_correction_B (n : ℕ) (p : ℝ)
    (phase : Fin n → ZMod 3) :
    (fullPhaseDiagonalB n phase ⊗ₖ fullPhaseDiagonalB n phase) *
      fullLossRetainedMatrix_B n p * (fullPhaseDiagonalB n phase)ᴴ =
        fullLossRetainedMatrix_B n p := by
  exact retainedKrausMatrix_phase_correction_B (physicalTensorKrausB n p)
    (fullPhaseDiagonalB n phase) (fullPhaseDiagonalB n phase)
    (fun L => wordCharacter (positiveSignatureB L) phase)
    (fun L => physicalTensorKrausB_phase_intertwining n p L phase)
    (fullPhaseDiagonalB_mul_conjTranspose n phase)

theorem fullLossRetained_reference_phase_correction_B (n : ℕ) (p : ℝ)
    (phase : Fin n → ZMod 3) (R : Type*) [Fintype R] [DecidableEq R] :
    (fullPhaseReferenceB n phase R ⊗ₖ fullPhaseDiagonalB n phase) *
      retainedKrausMatrix_B (referenceKrausB (physicalTensorKrausB n p) R) *
        (fullPhaseReferenceB n phase R)ᴴ =
          retainedKrausMatrix_B (referenceKrausB (physicalTensorKrausB n p) R) := by
  exact retainedKrausMatrix_phase_correction_B
    (referenceKrausB (physicalTensorKrausB n p) R)
    (fullPhaseReferenceB n phase R) (fullPhaseReferenceB n phase R)
    (fun L => wordCharacter (positiveSignatureB L) phase)
    (fun L => physicalTensorKrausB_reference_phase_intertwining n p L phase R)
    (fullPhaseReferenceB_mul_conjTranspose n phase R)

theorem fullLossCorrection_reference_isometry_B (n : ℕ)
    (phase : Fin n → ZMod 3) (R : Type*) [Fintype R] [DecidableEq R] :
    (fullPhaseReferenceB n phase R ⊗ₖ fullPhaseDiagonalB n phase)ᴴ *
      (fullPhaseReferenceB n phase R ⊗ₖ fullPhaseDiagonalB n phase) = 1 := by
  rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
    fullPhaseReferenceB_conjTranspose_mul, fullPhaseDiagonalB_conjTranspose_mul,
    Matrix.one_kronecker_one]

theorem fullLossCorrection_reference_coisometry_B (n : ℕ)
    (phase : Fin n → ZMod 3) (R : Type*) [Fintype R] [DecidableEq R] :
    (fullPhaseReferenceB n phase R ⊗ₖ fullPhaseDiagonalB n phase) *
      (fullPhaseReferenceB n phase R ⊗ₖ fullPhaseDiagonalB n phase)ᴴ = 1 := by
  rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
    fullPhaseReferenceB_mul_conjTranspose, fullPhaseDiagonalB_mul_conjTranspose,
    Matrix.one_kronecker_one]

end QuantumProver.AmplitudeDamping.SecretKey.PhaseRecovery

namespace QuantumProver.AmplitudeDamping.SecretKey.PublicHistory

variable {F A B E : Type*} [Fintype F] [Fintype A] [Fintype B] [Fintype E]
  [DecidableEq F] [DecidableEq A] [DecidableEq B] [DecidableEq E]

theorem congruence_rightMemory_apply_B {I O : Type*} [Fintype I]
    (K : Matrix O I ℂ) (ρ : Matrix (I × E) (I × E) ℂ)
    (o o' : O) (e e' : E) :
    ((K ⊗ₖ (1 : Matrix E E ℂ)) * ρ *
      (K ⊗ₖ (1 : Matrix E E ℂ))ᴴ) (o, e) (o', e') =
      (K * Matrix.of (fun i k => ρ (i, e) (k, e')) * Kᴴ) o o' := by
  classical
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.kroneckerMap_apply, Matrix.one_apply, Fintype.sum_prod_type,
    Finset.sum_mul, Finset.mul_sum, Matrix.of_apply,
    apply_ite, ite_mul, mul_ite, mul_assoc]

theorem congruence_flagReference_apply_B {I O : Type*} [Fintype I]
    (K : Matrix O I ℂ) (j h h' : F)
    (ρ : Matrix (I × E) (I × E) ℂ) (o o' : O) (e e' : E) :
    ((K ⊗ₖ attachFlag_B (A := E) j) * ρ *
      (K ⊗ₖ attachFlag_B (A := E) j)ᴴ) (o, (h, e)) (o', (h', e')) =
      if h = j ∧ h' = j then
        (K * Matrix.of (fun i k => ρ (i, e) (k, e')) * Kᴴ) o o'
      else 0 := by
  classical
  by_cases hh : h = j <;> by_cases hh' : h' = j <;>
    simp [attachFlag_B, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.kroneckerMap_apply, Matrix.one_apply, Fintype.sum_prod_type,
      Finset.sum_mul, Finset.mul_sum, Matrix.of_apply, hh, hh',
      apply_ite, ite_mul, mul_ite, mul_assoc]

theorem partialTraceRight_sum_B {I Z : Type*} [Fintype Z]
    (σ : Z → Matrix (I × E) (I × E) ℂ) :
    partialTraceRight (∑ z, σ z) = ∑ z, partialTraceRight (σ z) := by
  ext i k
  simp only [partialTraceRight, Matrix.sum_apply]
  exact Finset.sum_comm

theorem partialTraceRight_congruence_rightMemory_B {I O : Type*}
    [Fintype I] (K : Matrix O I ℂ) (ρ : Matrix (I × E) (I × E) ℂ) :
    partialTraceRight ((K ⊗ₖ (1 : Matrix E E ℂ)) * ρ *
      (K ⊗ₖ (1 : Matrix E E ℂ))ᴴ) = K * partialTraceRight ρ * Kᴴ := by
  have hblocks : partialTraceRight ((K ⊗ₖ (1 : Matrix E E ℂ)) * ρ *
        (K ⊗ₖ (1 : Matrix E E ℂ))ᴴ) =
      ∑ e, K * Matrix.of (fun i k => ρ (i, e) (k, e)) * Kᴴ := by
    ext o o'
    simp only [partialTraceRight, Matrix.sum_apply, congruence_rightMemory_apply_B]
  have hslices : (∑ e, Matrix.of (fun i k => ρ (i, e) (k, e))) =
      partialTraceRight ρ := by
    ext i k
    simp only [Matrix.sum_apply, Matrix.of_apply, partialTraceRight]
  rw [hblocks, ← Matrix.sum_mul, ← Matrix.mul_sum, hslices]

def publicBranchWithEve_B (j : F)
    (σ : Matrix ((A × B) × E) ((A × B) × E) ℂ) :
    Matrix (((F × A) × (F × B)) × (F × E))
      (((F × A) × (F × B)) × (F × E)) ℂ :=
  ((attachFlag_B (A := A) j ⊗ₖ attachFlag_B (A := B) j) ⊗ₖ
      attachFlag_B (A := E) j) * σ *
    ((attachFlag_B (A := A) j ⊗ₖ attachFlag_B (A := B) j) ⊗ₖ
      attachFlag_B (A := E) j)ᴴ

theorem publicBranchWithEve_apply_B (j i k h i' k' h' : F)
    (σ : Matrix ((A × B) × E) ((A × B) × E) ℂ)
    (a a' : A) (b b' : B) (e e' : E) :
    publicBranchWithEve_B j σ (((i, a), (k, b)), (h, e))
      (((i', a'), (k', b')), (h', e')) =
      if i = j ∧ k = j ∧ h = j ∧ i' = j ∧ k' = j ∧ h' = j then
        σ ((a, b), e) ((a', b'), e') else 0 := by
  classical
  unfold publicBranchWithEve_B
  rw [congruence_flagReference_apply_B]
  change (if h = j ∧ h' = j then
    publicBranch_B j (Matrix.of (fun x y => σ (x, e) (y, e')))
      ((i, a), (k, b)) ((i', a'), (k', b')) else 0) = _
  rw [publicBranch_apply_B]
  simp only [Matrix.of_apply]
  split_ifs <;> simp_all

theorem publicBranchWithEve_gram_B (j : F) :
    ((attachFlag_B (A := A) j ⊗ₖ attachFlag_B (A := B) j) ⊗ₖ
      attachFlag_B (A := E) j)ᴴ *
      ((attachFlag_B (A := A) j ⊗ₖ attachFlag_B (A := B) j) ⊗ₖ
        attachFlag_B (A := E) j) = 1 := by
  rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
    attachFlag_pair_complete_B, attachFlag_complete_B, Matrix.one_kronecker_one]

theorem publicBranchWithEve_trace_B (j : F)
    (σ : Matrix ((A × B) × E) ((A × B) × E) ℂ) :
    (publicBranchWithEve_B j σ).trace = σ.trace := by
  rw [publicBranchWithEve_B, Matrix.trace_mul_cycle, publicBranchWithEve_gram_B,
    Matrix.one_mul]

theorem publicBranchWithEve_honestMarginal_B (j : F)
    (σ : Matrix ((A × B) × E) ((A × B) × E) ℂ) :
    partialTraceRight (publicBranchWithEve_B j σ) =
      publicBranch_B j (partialTraceRight σ) := by
  classical
  ext x y
  rcases x with ⟨⟨i, a⟩, ⟨k, b⟩⟩
  rcases y with ⟨⟨i', a'⟩, ⟨k', b'⟩⟩
  simp only [partialTraceRight, Fintype.sum_prod_type, publicBranchWithEve_apply_B,
    publicBranch_apply_B]
  by_cases hi : i = j <;> by_cases hk : k = j <;>
    by_cases hi' : i' = j <;> by_cases hk' : k' = j <;>
    simp [hi, hk, hi', hk']

def copyPublicHistoryWithEve_B
    (σ : F → Matrix ((A × B) × E) ((A × B) × E) ℂ) :
    Matrix (((F × A) × (F × B)) × (F × E))
      (((F × A) × (F × B)) × (F × E)) ℂ :=
  ∑ j, publicBranchWithEve_B j (σ j)

theorem copyPublicHistoryWithEve_apply_B
    (σ : F → Matrix ((A × B) × E) ((A × B) × E) ℂ)
    (i k h i' k' h' : F) (a a' : A) (b b' : B) (e e' : E) :
    copyPublicHistoryWithEve_B σ (((i, a), (k, b)), (h, e))
      (((i', a'), (k', b')), (h', e')) =
      if i = k ∧ i = h ∧ i = i' ∧ i = k' ∧ i = h' then
        σ i ((a, b), e) ((a', b'), e') else 0 := by
  classical
  simp only [copyPublicHistoryWithEve_B, Matrix.sum_apply, publicBranchWithEve_apply_B]
  rw [Finset.sum_eq_single i]
  · simp [eq_comm]
  · intro j _ hj
    simp [Ne.symm hj]
  · simp

theorem copyPublicHistoryWithEve_trace_B
    (σ : F → Matrix ((A × B) × E) ((A × B) × E) ℂ) :
    (copyPublicHistoryWithEve_B σ).trace = ∑ j, (σ j).trace := by
  simp only [copyPublicHistoryWithEve_B, Matrix.trace_sum, publicBranchWithEve_trace_B]

theorem copyPublicHistoryWithEve_honestMarginal_B
    (σ : F → Matrix ((A × B) × E) ((A × B) × E) ℂ) :
    partialTraceRight (copyPublicHistoryWithEve_B σ) =
      copyPublicHistory_B (fun j => partialTraceRight (σ j)) := by
  unfold copyPublicHistoryWithEve_B copyPublicHistory_B
  rw [partialTraceRight_sum_B]
  simp_rw [publicBranchWithEve_honestMarginal_B]

variable {A' B' J K : Type*} [Fintype A'] [Fintype B'] [Fintype J] [Fintype K]
  [DecidableEq A'] [DecidableEq B'] [DecidableEq J] [DecidableEq K]

def copiedLocalInstrumentWithEve_B (C : KrausChannel A A' J)
    (D : J → KrausChannel B B' K) :
    KrausChannel ((A × B) × E)
      ((((J × K) × A') × ((J × K) × B')) × ((J × K) × E)) (J × K) where
  op f := publicProductOperator_B C D f ⊗ₖ attachFlag_B (A := E) f
  complete := by
    simp_rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
      attachFlag_complete_B]
    calc
      _ = (∑ f : J × K, (publicProductOperator_B C D f)ᴴ *
          publicProductOperator_B C D f) ⊗ₖ (1 : Matrix E E ℂ) := by
        ext x y
        simp only [Matrix.sum_apply, Matrix.kroneckerMap_apply, Finset.sum_mul]
      _ = (1 : Matrix (A × B) (A × B) ℂ) ⊗ₖ (1 : Matrix E E ℂ) := by
        have hc : (∑ f : J × K, (publicProductOperator_B C D f)ᴴ *
            publicProductOperator_B C D f) = 1 :=
          (copiedLocalInstrument_B C D).complete
        rw [hc]
      _ = 1 := Matrix.one_kronecker_one

theorem copiedLocalInstrumentWithEve_eval_B (C : KrausChannel A A' J)
    (D : J → KrausChannel B B' K)
    (ρ : Matrix ((A × B) × E) ((A × B) × E) ℂ) :
    (copiedLocalInstrumentWithEve_B (E := E) C D).eval ρ =
      copyPublicHistoryWithEve_B (fun f : J × K =>
        ((C.op f.1 ⊗ₖ (D f.1).op f.2) ⊗ₖ (1 : Matrix E E ℂ)) * ρ *
          ((C.op f.1 ⊗ₖ (D f.1).op f.2) ⊗ₖ (1 : Matrix E E ℂ))ᴴ) := by
  unfold KrausChannel.eval copyPublicHistoryWithEve_B
  apply Finset.sum_congr rfl
  intro f _
  have hop : publicProductOperator_B C D f ⊗ₖ attachFlag_B (A := E) f =
      ((attachFlag_B (A := A') f ⊗ₖ attachFlag_B (A := B') f) ⊗ₖ
        attachFlag_B (A := E) f) *
        ((C.op f.1 ⊗ₖ (D f.1).op f.2) ⊗ₖ (1 : Matrix E E ℂ)) := by
    rw [← Matrix.mul_kronecker_mul, Matrix.mul_one]
    rfl
  change ((publicProductOperator_B C D f ⊗ₖ attachFlag_B (A := E) f) * ρ *
    (publicProductOperator_B C D f ⊗ₖ attachFlag_B (A := E) f)ᴴ) = _
  simp_rw [hop]
  simp only [publicBranchWithEve_B, Matrix.conjTranspose_mul, Matrix.mul_assoc]

theorem copiedLocalInstrumentWithEve_eval_apply_B (C : KrausChannel A A' J)
    (D : J → KrausChannel B B' K)
    (ρ : Matrix ((A × B) × E) ((A × B) × E) ℂ)
    (i k h i' k' h' : J × K) (a a' : A') (b b' : B') (e e' : E) :
    (copiedLocalInstrumentWithEve_B (E := E) C D).eval ρ
      (((i, a), (k, b)), (h, e)) (((i', a'), (k', b')), (h', e')) =
      if i = k ∧ i = h ∧ i = i' ∧ i = k' ∧ i = h' then
        ((C.op i.1 ⊗ₖ (D i.1).op i.2) *
          Matrix.of (fun x y => ρ (x, e) (y, e')) *
          (C.op i.1 ⊗ₖ (D i.1).op i.2)ᴴ) (a, b) (a', b') else 0 := by
  rw [copiedLocalInstrumentWithEve_eval_B, copyPublicHistoryWithEve_apply_B,
    congruence_rightMemory_apply_B]

theorem copiedLocalInstrumentWithEve_trace_B (C : KrausChannel A A' J)
    (D : J → KrausChannel B B' K)
    (ρ : Matrix ((A × B) × E) ((A × B) × E) ℂ) :
    ((copiedLocalInstrumentWithEve_B (E := E) C D).eval ρ).trace = ρ.trace :=
  (copiedLocalInstrumentWithEve_B (E := E) C D).trace_eval ρ

theorem copiedLocalInstrumentWithEve_reference_posSemidef_B
    (C : KrausChannel A A' J) (D : J → KrausChannel B B' K)
    (R : Type*) [Fintype R] [DecidableEq R]
    {ρ : Matrix (((A × B) × E) × R) (((A × B) × E) × R) ℂ}
    (hρ : ρ.PosSemidef) :
    (((copiedLocalInstrumentWithEve_B (E := E) C D).withRightMemory R).eval ρ).PosSemidef :=
  ((copiedLocalInstrumentWithEve_B (E := E) C D).withRightMemory R).eval_posSemidef hρ

theorem copiedLocalInstrumentWithEve_honestMarginal_B
    (C : KrausChannel A A' J) (D : J → KrausChannel B B' K)
    (ρ : Matrix ((A × B) × E) ((A × B) × E) ℂ) :
    partialTraceRight ((copiedLocalInstrumentWithEve_B (E := E) C D).eval ρ) =
      (copiedLocalInstrument_B C D).eval (partialTraceRight ρ) := by
  rw [copiedLocalInstrumentWithEve_eval_B, copyPublicHistoryWithEve_honestMarginal_B]
  simp_rw [partialTraceRight_congruence_rightMemory_B]
  exact (copiedLocalInstrument_eval_B C D (partialTraceRight ρ)).symm

def retainPrivateLocalKraus_B {I O Z U : Type*}
    [Fintype I] [Fintype O] [Fintype Z] [Fintype U] [DecidableEq I]
    (C : KrausChannel I O (Z × U)) : KrausChannel I (O × U) Z where
  op z := fun ou i => C.op (z, ou.2) ou.1 i
  complete := by
    calc
      _ = ∑ z : Z, ∑ u : U, (C.op (z, u))ᴴ * C.op (z, u) := by
        apply Finset.sum_congr rfl
        intro z _
        ext i k
        simp only [Matrix.sum_apply]
        change (∑ ou : O × U, star (C.op (z, ou.2) ou.1 i) *
          C.op (z, ou.2) ou.1 k) =
          ∑ u : U, ∑ o : O, star (C.op (z, u) o i) * C.op (z, u) o k
        rw [Fintype.sum_prod_type, Finset.sum_comm]
      _ = 1 := by
        simpa only [Fintype.sum_prod_type] using C.complete

theorem retainPrivateLocalKraus_apply_B {I O Z U : Type*}
    [Fintype I] [Fintype O] [Fintype Z] [Fintype U] [DecidableEq I]
    (C : KrausChannel I O (Z × U)) (z : Z) (o : O) (u : U) (i : I) :
    (retainPrivateLocalKraus_B C).op z (o, u) i = C.op (z, u) o i := rfl

theorem retainPrivateLocalKraus_offDiagonal_B {I O Z U : Type*}
    [Fintype I] [Fintype O] [Fintype Z] [Fintype U] [DecidableEq I]
    (C : KrausChannel I O (Z × U)) (z : Z)
    (ρ : Matrix (I × E) (I × E) ℂ)
    (o o' : O) (u u' : U) (e e' : E) :
    (((retainPrivateLocalKraus_B C).op z ⊗ₖ (1 : Matrix E E ℂ)) * ρ *
      ((retainPrivateLocalKraus_B C).op z ⊗ₖ (1 : Matrix E E ℂ))ᴴ)
      ((o, u), e) ((o', u'), e') =
      (C.op (z, u) * Matrix.of (fun i k => ρ (i, e) (k, e')) *
        (C.op (z, u'))ᴴ) o o' := by
  rw [congruence_rightMemory_apply_B]
  rfl

end QuantumProver.AmplitudeDamping.SecretKey.PublicHistory

namespace QuantumProver.AmplitudeDamping.SecretKey.PublicHistory

def basisEmbedding_B {I O : Type*} [DecidableEq O] (f : I → O) : Matrix O I ℂ :=
  fun o i => if o = f i then 1 else 0

theorem basisEmbedding_gram_B {I O : Type*} [Fintype O]
    [DecidableEq I] [DecidableEq O] (f : I → O) (hf : Function.Injective f) :
    (basisEmbedding_B f)ᴴ * basisEmbedding_B f = 1 := by
  classical
  ext i k
  by_cases hik : i = k <;>
    simp [basisEmbedding_B, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.one_apply, ite_mul, mul_ite, apply_ite, hf.eq_iff, hik, eq_comm]

theorem basisEmbedding_entry_decoder_B {I O : Type*}
    [DecidableEq I] [DecidableEq O]
    (f : I → O) (g : O → I) (hgf : Function.LeftInverse g f) (o : O) (i : I) :
    basisEmbedding_B f o i =
      if f (g o) = o then (1 : Matrix I I ℂ) (g o) i else 0 := by
  classical
  by_cases himage : f (g o) = o
  · have hmatch : o = f i ↔ g o = i := by
      constructor
      · intro h
        simpa only [hgf i] using congrArg g h
      · intro h
        exact himage.symm.trans (congrArg f h)
    simp only [basisEmbedding_B, hmatch, if_pos himage, Matrix.one_apply]
  · have hneq : o ≠ f i := by
      intro h
      apply himage
      rw [h, hgf i]
    simp only [basisEmbedding_B, if_neg hneq, if_neg himage]

theorem basisEmbedding_sandwich_apply_B {I O : Type*} [Fintype I]
    [DecidableEq I] [DecidableEq O]
    (f : I → O) (g : O → I) (hgf : Function.LeftInverse g f)
    (σ : Matrix I I ℂ) (o o' : O) :
    (basisEmbedding_B f * σ * (basisEmbedding_B f)ᴴ) o o' =
      if f (g o) = o ∧ f (g o') = o' then σ (g o) (g o') else 0 := by
  classical
  by_cases ho : f (g o) = o <;> by_cases ho' : f (g o') = o' <;>
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply,
      basisEmbedding_entry_decoder_B f g hgf, ho, ho', Matrix.one_apply,
      ite_mul, mul_ite, apply_ite]

variable {F A B E : Type*} [Fintype F] [Fintype A] [Fintype B] [Fintype E]
  [DecidableEq F] [DecidableEq A] [DecidableEq B] [DecidableEq E]

def historyCopyCoordinates_B (x : (A × B) × (F × E)) :
    ((F × A) × (F × B)) × (F × E) :=
  (((x.2.1, x.1.1), (x.2.1, x.1.2)), x.2)

def historyDecodeCoordinates_B (x : ((F × A) × (F × B)) × (F × E)) :
    (A × B) × (F × E) :=
  ((x.1.1.2, x.1.2.2), x.2)

theorem historyCopy_leftInverse_B : Function.LeftInverse
    (historyDecodeCoordinates_B (F := F) (A := A) (B := B) (E := E))
    historyCopyCoordinates_B := by
  intro x
  rfl

def historyCopyEmbedding_B :
    Matrix (((F × A) × (F × B)) × (F × E)) ((A × B) × (F × E)) ℂ :=
  basisEmbedding_B historyCopyCoordinates_B

theorem historyCopyEmbedding_gram_B :
    (historyCopyEmbedding_B (F := F) (A := A) (B := B) (E := E))ᴴ *
      historyCopyEmbedding_B (F := F) (A := A) (B := B) (E := E) = 1 := by
  exact basisEmbedding_gram_B
    (historyCopyCoordinates_B (F := F) (A := A) (B := B) (E := E))
    (historyCopy_leftInverse_B (F := F) (A := A) (B := B) (E := E)).injective

theorem historyCopyEmbedding_sandwich_apply_B
    (σ : Matrix ((A × B) × (F × E)) ((A × B) × (F × E)) ℂ)
    (i k h i' k' h' : F) (a a' : A) (b b' : B) (e e' : E) :
    (historyCopyEmbedding_B (F := F) (A := A) (B := B) (E := E) * σ *
      (historyCopyEmbedding_B (F := F) (A := A) (B := B) (E := E))ᴴ)
      (((i, a), (k, b)), (h, e)) (((i', a'), (k', b')), (h', e')) =
      if i = h ∧ k = h ∧ i' = h' ∧ k' = h' then
        σ ((a, b), (h, e)) ((a', b'), (h', e')) else 0 := by
  unfold historyCopyEmbedding_B
  rw [basisEmbedding_sandwich_apply_B
    (historyCopyCoordinates_B (F := F) (A := A) (B := B) (E := E))
    (historyDecodeCoordinates_B (F := F) (A := A) (B := B) (E := E))
    (historyCopy_leftInverse_B (F := F) (A := A) (B := B) (E := E))]
  simp [historyCopyCoordinates_B, historyDecodeCoordinates_B, Prod.mk.injEq,
    eq_comm, and_assoc]

end QuantumProver.AmplitudeDamping.SecretKey.PublicHistory

namespace QuantumProver.AmplitudeDamping.SecretKey.PublicHistory

def twoRoundProtocol_B (p : ℝ) {a b ao bo j k : ℕ}
    (C : KrausChannel (Fin a) (Fin ao) (Fin j))
    (D : Fin j → KrausChannel (Fin b) (Fin bo) (Fin k)) :
    PhysicalProtocol.FiniteKeyProtocol p a b ao bo :=
  .alice C (fun z => .bob (D z) (fun _ => .done ao bo))

theorem twoRoundProtocol_fullOutput_apply_B (p : ℝ) {a b ao bo m n : ℕ}
    (C : KrausChannel (Fin a) (Fin ao) (Fin m))
    (D : Fin m → KrausChannel (Fin b) (Fin bo) (Fin n))
    (ρ : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ)
    (j j' : Fin m) (k k' : Fin n)
    (a' a'' : Fin ao) (b' b'' : Fin bo) :
    (twoRoundProtocol_B p C D).fullOutput ρ
      ((a', b'), ⟨j, ⟨k, ()⟩⟩) ((a'', b''), ⟨j', ⟨k', ()⟩⟩) =
      if j = j' ∧ k = k' then
        ((C.op j ⊗ₖ (D j).op k) * ρ * (C.op j ⊗ₖ (D j).op k)ᴴ)
          (a', b') (a'', b'') else 0 := by
  classical
  have hcomp : ((1 : Matrix (Fin ao) (Fin ao) ℂ) ⊗ₖ (D j).op k) *
      (C.op j ⊗ₖ (1 : Matrix (Fin b) (Fin b) ℂ)) =
        C.op j ⊗ₖ (D j).op k := by
    rw [← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one]
  have hmatrix : ((1 : Matrix (Fin ao) (Fin ao) ℂ) ⊗ₖ (D j).op k) *
      ((C.op j ⊗ₖ (1 : Matrix (Fin b) (Fin b) ℂ)) * ρ *
        (C.op j ⊗ₖ (1 : Matrix (Fin b) (Fin b) ℂ))ᴴ) *
      ((1 : Matrix (Fin ao) (Fin ao) ℂ) ⊗ₖ (D j).op k)ᴴ =
      (C.op j ⊗ₖ (D j).op k) * ρ * (C.op j ⊗ₖ (D j).op k)ᴴ := by
    simp_rw [← hcomp]
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  by_cases hj : j = j'
  · subst j'
    by_cases hk : k = k'
    · subst k'
      simpa [twoRoundProtocol_B, PhysicalProtocol.FiniteKeyProtocol.fullOutput] using
        congrArg (fun M => M (a', b') (a'', b'')) hmatrix
    · simp [twoRoundProtocol_B, PhysicalProtocol.FiniteKeyProtocol.fullOutput, hk]
  · simp [twoRoundProtocol_B, PhysicalProtocol.FiniteKeyProtocol.fullOutput, hj]

def twoRoundHistoryEquiv_B (p : ℝ) {a b ao bo m n : ℕ}
    (C : KrausChannel (Fin a) (Fin ao) (Fin m))
    (D : Fin m → KrausChannel (Fin b) (Fin bo) (Fin n)) :
    (Fin m × Fin n) ≃ (twoRoundProtocol_B p C D).Environment where
  toFun f := ⟨f.1, ⟨f.2, ()⟩⟩
  invFun h := (h.1, h.2.1)
  left_inv f := by
    rcases f with ⟨j, k⟩
    rfl
  right_inv h := by
    rcases h with ⟨j, ⟨k, u⟩⟩
    cases u
    rfl

def twoRoundHistoryMatrix_B (p : ℝ) {a b ao bo m n : ℕ} {E : Type*}
    (C : KrausChannel (Fin a) (Fin ao) (Fin m))
    (D : Fin m → KrausChannel (Fin b) (Fin bo) (Fin n))
    (ρ : Matrix ((Fin a × Fin b) × E) ((Fin a × Fin b) × E) ℂ) :
    Matrix ((Fin ao × Fin bo) × ((Fin m × Fin n) × E))
      ((Fin ao × Fin bo) × ((Fin m × Fin n) × E)) ℂ :=
  fun x y => (twoRoundProtocol_B p C D).fullOutput
    (Matrix.of (fun i j => ρ (i, x.2.2) (j, y.2.2)))
    (x.1, twoRoundHistoryEquiv_B p C D x.2.1)
    (y.1, twoRoundHistoryEquiv_B p C D y.2.1)

theorem twoRoundHistoryMatrix_apply_B (p : ℝ) {a b ao bo m n : ℕ} {E : Type*}
    (C : KrausChannel (Fin a) (Fin ao) (Fin m))
    (D : Fin m → KrausChannel (Fin b) (Fin bo) (Fin n))
    (ρ : Matrix ((Fin a × Fin b) × E) ((Fin a × Fin b) × E) ℂ)
    (f f' : Fin m × Fin n) (a' a'' : Fin ao) (b' b'' : Fin bo) (e e' : E) :
    twoRoundHistoryMatrix_B p C D ρ ((a', b'), (f, e)) ((a'', b''), (f', e')) =
      if f = f' then
        ((C.op f.1 ⊗ₖ (D f.1).op f.2) *
          Matrix.of (fun x y => ρ (x, e) (y, e')) *
          (C.op f.1 ⊗ₖ (D f.1).op f.2)ᴴ) (a', b') (a'', b'') else 0 := by
  unfold twoRoundHistoryMatrix_B
  change (twoRoundProtocol_B p C D).fullOutput _
    ((a', b'), ⟨f.1, ⟨f.2, ()⟩⟩) ((a'', b''), ⟨f'.1, ⟨f'.2, ()⟩⟩) = _
  rw [twoRoundProtocol_fullOutput_apply_B]
  rcases f with ⟨j, k⟩
  rcases f' with ⟨j', k'⟩
  simp only [Prod.mk.injEq, Prod.fst, Prod.snd]

theorem copiedLocalInstrumentWithEve_twoRound_isometric_alignment_B (p : ℝ)
    {a b ao bo m n : ℕ} {E : Type*} [Fintype E] [DecidableEq E]
    (C : KrausChannel (Fin a) (Fin ao) (Fin m))
    (D : Fin m → KrausChannel (Fin b) (Fin bo) (Fin n))
    (ρ : Matrix ((Fin a × Fin b) × E) ((Fin a × Fin b) × E) ℂ) :
    (copiedLocalInstrumentWithEve_B (E := E) C D).eval ρ =
      historyCopyEmbedding_B (F := Fin m × Fin n) (A := Fin ao) (B := Fin bo)
        (E := E) * twoRoundHistoryMatrix_B p C D ρ *
        (historyCopyEmbedding_B (F := Fin m × Fin n) (A := Fin ao) (B := Fin bo)
          (E := E))ᴴ := by
  classical
  ext x y
  rcases x with ⟨⟨⟨i, a'⟩, ⟨k, b'⟩⟩, ⟨h, e⟩⟩
  rcases y with ⟨⟨⟨i', a''⟩, ⟨k', b''⟩⟩, ⟨h', e'⟩⟩
  rw [copiedLocalInstrumentWithEve_eval_apply_B, historyCopyEmbedding_sandwich_apply_B]
  simp only [twoRoundHistoryMatrix_apply_B]
  by_cases hi : i = h <;> by_cases hk : k = h <;>
    by_cases hi' : i' = h' <;> by_cases hk' : k' = h' <;> by_cases hh : h = h' <;>
    simp_all [eq_comm]

end QuantumProver.AmplitudeDamping.SecretKey.PublicHistory

namespace QuantumProver.AmplitudeDamping.SecretKey.KrausChannel

def relabel_B {I O J I' O' : Type*}
    [Fintype I] [Fintype O] [Fintype J] [Fintype I'] [Fintype O']
    [DecidableEq I] [DecidableEq I'] (C : KrausChannel I O J)
    (eI : I' ≃ I) (eO : O' ≃ O) : KrausChannel I' O' J where
  op j := (C.op j).submatrix eO eI
  complete := by
    simp only [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv]
    have hs : (∑ j, ((C.op j)ᴴ * C.op j).submatrix eI eI) =
        (∑ j, (C.op j)ᴴ * C.op j).submatrix eI eI := by
      ext x y
      simp only [Matrix.sum_apply, Matrix.submatrix_apply]
    rw [hs, C.complete, Matrix.submatrix_one_equiv]

theorem relabel_eval_B {I O J I' O' : Type*}
    [Fintype I] [Fintype O] [Fintype J] [Fintype I'] [Fintype O']
    [DecidableEq I] [DecidableEq I'] (C : KrausChannel I O J)
    (eI : I' ≃ I) (eO : O' ≃ O) (ρ : Matrix I' I' ℂ) :
    (C.relabel_B eI eO).eval ρ =
      (C.eval (ρ.submatrix eI.symm eI.symm)).submatrix eO eO := by
  have hρ : ρ = (ρ.submatrix eI.symm eI.symm).submatrix eI eI := by
    ext x y
    simp
  calc
    _ = (C.relabel_B eI eO).eval
        ((ρ.submatrix eI.symm eI.symm).submatrix eI eI) := congrArg _ hρ
    _ = _ := by
      simp only [eval, relabel_B, Matrix.conjTranspose_submatrix,
        Matrix.submatrix_mul_equiv]
      ext x y
      simp only [Matrix.sum_apply, Matrix.submatrix_apply]

end QuantumProver.AmplitudeDamping.SecretKey.KrausChannel

namespace QuantumProver.AmplitudeDamping.SecretKey

theorem separableCone_submatrix_product_B {A B A' B' : Type*}
    [Fintype A] [Fintype B] [Fintype A'] [Fintype B']
    (eA : A' → A) (eB : B' → B)
    {ρ : Matrix (A × B) (A × B) ℂ} (hρ : InSeparableCone ρ) :
    InSeparableCone (ρ.submatrix (fun x => (eA x.1, eB x.2))
      (fun x => (eA x.1, eB x.2))) := by
  obtain ⟨k, left, right, hl, hr, rfl⟩ := hρ
  refine ⟨k, (fun j => (left j).submatrix eA eA),
    (fun j => (right j).submatrix eB eB),
    (fun j => (hl j).submatrix eA), (fun j => (hr j).submatrix eB), ?_⟩
  ext x y
  simp only [Matrix.submatrix_apply, Matrix.sum_apply, Matrix.kroneckerMap_apply]

namespace PhysicalProtocol

def comparisonInputLocalEquiv_B (a : ℕ) : Fin (2 * a) ≃ Fin a × Fin 2 :=
  (splitQubit a).trans (Equiv.prodComm (Fin 2) (Fin a))

def transferComparisonChannel_B {J : Type*} [Fintype J]
    (C : KrausChannel (Fin 2) (Fin 2) J) (a b : ℕ) :
    KrausChannel (Fin (2 * a) × Fin b) (Fin a × Fin (2 * b)) J :=
  ((C.withMemory (Fin a)).withRightMemory (Fin b)).relabel_B
    ((comparisonInputLocalEquiv_B a).prodCongr (Equiv.refl (Fin b)))
    (((Equiv.refl (Fin a)).prodCongr (splitQubit b)).trans
      (Equiv.prodAssoc (Fin a) (Fin 2) (Fin b)).symm)

theorem transferComparisonChannel_separable_B {J : Type*} [Fintype J]
    (v bvec : J → Fin 2 → ℂ)
    (hv : ∑ j, Matrix.vecMulVec (v j) (star (v j)) = 1)
    (hb : ∀ j, ∑ o, star (bvec j o) * bvec j o = 1) (a b : ℕ)
    {ρ : BipartiteMatrix (2 * a) b} (hρ : InSeparableCone ρ) :
    InSeparableCone ((transferComparisonChannel_B
      (measurePrepareChannel v bvec hv hb) a b).eval ρ) := by
  classical
  let eA := comparisonInputLocalEquiv_B a
  let ρ' : Matrix ((Fin a × Fin 2) × Fin b) ((Fin a × Fin 2) × Fin b) ℂ :=
    ρ.submatrix (fun x => (eA.symm x.1, x.2))
      (fun x => (eA.symm x.1, x.2))
  have hρ' : InSeparableCone ρ' :=
    separableCone_submatrix_product_B eA.symm id hρ
  have h := measurePrepareChannel_transfer_mem_separableCone v bvec hv hb hρ'
  have hout := separableCone_submatrix_product_B
    (id : Fin a → Fin a) (splitQubit b) h
  rw [transferComparisonChannel_B, KrausChannel.relabel_eval_B]
  convert hout using 1
  ext x y
  rfl

namespace FiniteKeyProtocol

def comparisonPublicHistory_B {p : ℝ} {a b af bf : ℕ}
    (P : FiniteKeyProtocol p a b af bf) : Type :=
  match P with
  | .done _ _ => Unit
  | .alice _ next => (z : _) × (next z).comparisonPublicHistory_B
  | .bob _ next => (z : _) × (next z).comparisonPublicHistory_B
  | .call next => next.comparisonPublicHistory_B

instance comparisonPublicHistoryFintype_B {p : ℝ} {a b af bf : ℕ}
    (P : FiniteKeyProtocol p a b af bf) : Fintype P.comparisonPublicHistory_B :=
  match P with
  | .done _ _ => inferInstanceAs (Fintype Unit)
  | .alice (k := k) _ next =>
      letI : ∀ z, Fintype (next z).comparisonPublicHistory_B :=
        fun z => comparisonPublicHistoryFintype_B (next z)
      inferInstanceAs (Fintype ((z : Fin k) × (next z).comparisonPublicHistory_B))
  | .bob (k := k) _ next =>
      letI : ∀ z, Fintype (next z).comparisonPublicHistory_B :=
        fun z => comparisonPublicHistoryFintype_B (next z)
      inferInstanceAs (Fintype ((z : Fin k) × (next z).comparisonPublicHistory_B))
  | .call next => comparisonPublicHistoryFintype_B next

def comparisonBranch_B {J : Type*} [Fintype J]
    (C : KrausChannel (Fin 2) (Fin 2) J) {p : ℝ} {a b af bf : ℕ}
    (P : FiniteKeyProtocol p a b af bf) :
    BipartiteMatrix a b → P.comparisonPublicHistory_B → BipartiteMatrix af bf :=
  match P with
  | .done _ _ => fun ρ _ => ρ
  | .alice (b := b₀) D next => fun ρ h =>
      (next h.1).comparisonBranch_B C
        ((D.op h.1 ⊗ₖ (1 : Matrix (Fin b₀) (Fin b₀) ℂ)) * ρ *
          (D.op h.1 ⊗ₖ (1 : Matrix (Fin b₀) (Fin b₀) ℂ))ᴴ) h.2
  | .bob (a := a₀) D next => fun ρ h =>
      (next h.1).comparisonBranch_B C
        (((1 : Matrix (Fin a₀) (Fin a₀) ℂ) ⊗ₖ D.op h.1) * ρ *
          ((1 : Matrix (Fin a₀) (Fin a₀) ℂ) ⊗ₖ D.op h.1)ᴴ) h.2
  | .call (a := a₀) (b := b₀) next => fun ρ h =>
      next.comparisonBranch_B C ((transferComparisonChannel_B C a₀ b₀).eval ρ) h

theorem comparisonBranch_posSemidef_B {J : Type*} [Fintype J]
    (C : KrausChannel (Fin 2) (Fin 2) J) {p : ℝ} {a b af bf : ℕ}
    (P : FiniteKeyProtocol p a b af bf) :
    ∀ (ρ : BipartiteMatrix a b), ρ.PosSemidef →
      ∀ h, (P.comparisonBranch_B C ρ h).PosSemidef := by
  induction P with
  | done a b => intro ρ hρ h; exact hρ
  | @alice a b ao af bf k D next ih =>
      intro ρ hρ h
      exact ih h.1 _ (hρ.mul_mul_conjTranspose_same _) h.2
  | @bob a b bo af bf k D next ih =>
      intro ρ hρ h
      exact ih h.1 _ (hρ.mul_mul_conjTranspose_same _) h.2
  | @call a b af bf next ih =>
      intro ρ hρ h
      exact ih _ ((transferComparisonChannel_B C a b).eval_posSemidef hρ) h

theorem comparisonBranch_trace_sum_B {J : Type*} [Fintype J]
    (C : KrausChannel (Fin 2) (Fin 2) J) {p : ℝ} {a b af bf : ℕ}
    (P : FiniteKeyProtocol p a b af bf) :
    ∀ ρ : BipartiteMatrix a b,
      (∑ h, (P.comparisonBranch_B C ρ h).trace) = ρ.trace := by
  induction P with
  | done a b =>
      intro ρ
      change (∑ _ : Unit, ρ.trace) = ρ.trace
      simp
  | @alice a b ao af bf k D next ih =>
      intro ρ
      change (∑ h : (z : Fin k) × (next z).comparisonPublicHistory_B,
        ((next h.1).comparisonBranch_B C
          ((D.op h.1 ⊗ₖ (1 : Matrix (Fin b) (Fin b) ℂ)) * ρ *
            (D.op h.1 ⊗ₖ (1 : Matrix (Fin b) (Fin b) ℂ))ᴴ) h.2).trace) = _
      rw [Fintype.sum_sigma]
      simp_rw [ih]
      simpa [KrausChannel.eval, KrausChannel.withRightMemory, Matrix.trace_sum] using
        (D.withRightMemory (Fin b)).trace_eval ρ
  | @bob a b bo af bf k D next ih =>
      intro ρ
      change (∑ h : (z : Fin k) × (next z).comparisonPublicHistory_B,
        ((next h.1).comparisonBranch_B C
          (((1 : Matrix (Fin a) (Fin a) ℂ) ⊗ₖ D.op h.1) * ρ *
            ((1 : Matrix (Fin a) (Fin a) ℂ) ⊗ₖ D.op h.1)ᴴ) h.2).trace) = _
      rw [Fintype.sum_sigma]
      simp_rw [ih]
      simpa [KrausChannel.eval, KrausChannel.withMemory, Matrix.trace_sum] using
        (D.withMemory (Fin a)).trace_eval ρ
  | @call a b af bf next ih =>
      intro ρ
      change (∑ h, (next.comparisonBranch_B C
        ((transferComparisonChannel_B C a b).eval ρ) h).trace) = _
      rw [ih, (transferComparisonChannel_B C a b).trace_eval]

theorem comparisonBranch_separable_B {J : Type*} [Fintype J]
    (v bvec : J → Fin 2 → ℂ)
    (hv : ∑ j, Matrix.vecMulVec (v j) (star (v j)) = 1)
    (hb : ∀ j, ∑ o, star (bvec j o) * bvec j o = 1)
    {p : ℝ} {a b af bf : ℕ} (P : FiniteKeyProtocol p a b af bf) :
    ∀ (ρ : BipartiteMatrix a b), InSeparableCone ρ →
      ∀ h, InSeparableCone
        (P.comparisonBranch_B (measurePrepareChannel v bvec hv hb) ρ h) := by
  induction P with
  | done a b => intro ρ hρ h; exact hρ
  | @alice a b ao af bf k D next ih =>
      intro ρ hρ h
      exact ih h.1 _ (separableCone_local_product_B (D.op h.1) 1 hρ) h.2
  | @bob a b bo af bf k D next ih =>
      intro ρ hρ h
      exact ih h.1 _ (separableCone_local_product_B 1 (D.op h.1) hρ) h.2
  | @call a b af bf next ih =>
      intro ρ hρ h
      exact ih _ (transferComparisonChannel_separable_B v bvec hv hb a b hρ) h

def comparisonCopiedMatrix_B {J : Type*} [Fintype J]
    (C : KrausChannel (Fin 2) (Fin 2) J) {p : ℝ} {a b af bf : ℕ}
    (P : FiniteKeyProtocol p a b af bf) (ρ : BipartiteMatrix a b) :
    Matrix ((P.comparisonPublicHistory_B × Fin af) ×
      (P.comparisonPublicHistory_B × Fin bf))
      ((P.comparisonPublicHistory_B × Fin af) ×
      (P.comparisonPublicHistory_B × Fin bf)) ℂ := by
  classical
  exact PublicHistory.copyPublicHistory_B (P.comparisonBranch_B C ρ)

theorem comparisonCopiedMatrix_trace_B {J : Type*} [Fintype J]
    (C : KrausChannel (Fin 2) (Fin 2) J) {p : ℝ} {a b af bf : ℕ}
    (P : FiniteKeyProtocol p a b af bf) (ρ : BipartiteMatrix a b) :
    (P.comparisonCopiedMatrix_B C ρ).trace = ρ.trace := by
  classical
  rw [comparisonCopiedMatrix_B, PublicHistory.copyPublicHistory_trace_B,
    comparisonBranch_trace_sum_B]

theorem comparisonCopiedMatrix_separable_B {J : Type*} [Fintype J]
    (v bvec : J → Fin 2 → ℂ)
    (hv : ∑ j, Matrix.vecMulVec (v j) (star (v j)) = 1)
    (hb : ∀ j, ∑ o, star (bvec j o) * bvec j o = 1)
    {p : ℝ} {a b af bf : ℕ} (P : FiniteKeyProtocol p a b af bf)
    {ρ : BipartiteMatrix a b} (hρ : InSeparableCone ρ) :
    InSeparableCone
      (P.comparisonCopiedMatrix_B (measurePrepareChannel v bvec hv hb) ρ) := by
  classical
  exact PublicHistory.copyPublicHistory_mem_separableCone_B _
    (P.comparisonBranch_separable_B v bvec hv hb ρ hρ)

theorem comparisonCopiedMatrix_posSemidef_B {J : Type*} [Fintype J]
    (C : KrausChannel (Fin 2) (Fin 2) J) {p : ℝ} {a b af bf : ℕ}
    (P : FiniteKeyProtocol p a b af bf) {ρ : BipartiteMatrix a b}
    (hρ : ρ.PosSemidef) : (P.comparisonCopiedMatrix_B C ρ).PosSemidef := by
  classical
  unfold comparisonCopiedMatrix_B PublicHistory.copyPublicHistory_B
  apply Matrix.posSemidef_sum
  intro h _
  exact (P.comparisonBranch_posSemidef_B C ρ hρ h).mul_mul_conjTranspose_same _

def comparisonCopiedDensity_B {J : Type*} [Fintype J]
    (C : KrausChannel (Fin 2) (Fin 2) J) {p : ℝ} {a b af bf : ℕ}
    (P : FiniteKeyProtocol p a b af bf) (ρ : Density (Fin a × Fin b)) :
    Density ((P.comparisonPublicHistory_B × Fin af) ×
      (P.comparisonPublicHistory_B × Fin bf)) where
  mat := P.comparisonCopiedMatrix_B C ρ.mat
  positive := P.comparisonCopiedMatrix_posSemidef_B C ρ.positive
  normalized := (P.comparisonCopiedMatrix_trace_B C ρ.mat).trans ρ.normalized

theorem comparisonCopiedDensity_separable_B {J : Type*} [Fintype J]
    (v bvec : J → Fin 2 → ℂ)
    (hv : ∑ j, Matrix.vecMulVec (v j) (star (v j)) = 1)
    (hb : ∀ j, ∑ o, star (bvec j o) * bvec j o = 1)
    {p : ℝ} {a b af bf : ℕ} (P : FiniteKeyProtocol p a b af bf)
    {ρ : Density (Fin a × Fin b)} (hρ : IsSeparable ρ) :
    IsSeparable
      (P.comparisonCopiedDensity_B (measurePrepareChannel v bvec hv hb) ρ) :=
  P.comparisonCopiedMatrix_separable_B v bvec hv hb hρ

end FiniteKeyProtocol
end PhysicalProtocol
end QuantumProver.AmplitudeDamping.SecretKey

namespace QuantumProver.AmplitudeDamping.SecretKey.KrausChannel

theorem completeAdaptiveFamily_B {I O P Z : Type*} {T : Z → Type*}
    [Fintype I] [Fintype O] [Fintype P] [Fintype Z]
    [∀ z, Fintype (T z)] [DecidableEq I] [DecidableEq O]
    (C : KrausChannel I O Z) (K : ∀ z, T z → Matrix P O ℂ)
    (hK : ∀ z, ∑ t, (K z t)ᴴ * K z t = 1) :
    (∑ h : Sigma T, (K h.1 h.2 * C.op h.1)ᴴ *
      (K h.1 h.2 * C.op h.1)) = 1 := by
  rw [Fintype.sum_sigma]
  simp only [Matrix.conjTranspose_mul]
  calc
    _ = ∑ z, (C.op z)ᴴ * (∑ t, (K z t)ᴴ * K z t) * C.op z := by
      apply Finset.sum_congr rfl
      intro z _
      simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_assoc]
    _ = ∑ z, (C.op z)ᴴ * C.op z := by
      simp only [hK, Matrix.mul_one]
    _ = 1 := C.complete

end QuantumProver.AmplitudeDamping.SecretKey.KrausChannel

namespace QuantumProver.AmplitudeDamping.SecretKey.PhysicalProtocol.FiniteKeyProtocol

noncomputable instance environmentDecidableEq_B {p : ℝ} {a b af bf : ℕ}
    (P : FiniteKeyProtocol p a b af bf) : DecidableEq P.Environment :=
  Classical.decEq _

def LocalOnly_B {p : ℝ} {a b af bf : ℕ} (P : FiniteKeyProtocol p a b af bf) : Prop :=
  match P with
  | .done _ _ => True
  | .alice _ next => ∀ z, (next z).LocalOnly_B
  | .bob _ next => ∀ z, (next z).LocalOnly_B
  | .call _ => False

def localAliceOperator_B {p : ℝ} {a b af bf : ℕ}
    (P : FiniteKeyProtocol p a b af bf) : P.Environment → Matrix (Fin af) (Fin a) ℂ :=
  match P with
  | .done _ _ => fun _ => 1
  | .alice C next => fun h => (next h.1).localAliceOperator_B h.2 * C.op h.1
  | .bob _ next => fun h => (next h.1).localAliceOperator_B h.2
  | .call _ => fun _ => 0

def localBobOperator_B {p : ℝ} {a b af bf : ℕ}
    (P : FiniteKeyProtocol p a b af bf) : P.Environment → Matrix (Fin bf) (Fin b) ℂ :=
  match P with
  | .done _ _ => fun _ => 1
  | .alice _ next => fun h => (next h.1).localBobOperator_B h.2
  | .bob C next => fun h => (next h.1).localBobOperator_B h.2 * C.op h.1
  | .call _ => fun _ => 0

def localHistoryOperator_B {p : ℝ} {a b af bf : ℕ}
    (P : FiniteKeyProtocol p a b af bf) (h : P.Environment) :
    Matrix (Fin af × Fin bf) (Fin a × Fin b) ℂ :=
  P.localAliceOperator_B h ⊗ₖ P.localBobOperator_B h

theorem localHistoryOperator_alice_B {p : ℝ} {a b ao af bf k : ℕ}
    (C : KrausChannel (Fin a) (Fin ao) (Fin k))
    (next : Fin k → FiniteKeyProtocol p ao b af bf)
    (z : Fin k) (t : (next z).Environment) :
    (FiniteKeyProtocol.alice C next).localHistoryOperator_B ⟨z, t⟩ =
      (next z).localHistoryOperator_B t *
        (C.op z ⊗ₖ (1 : Matrix (Fin b) (Fin b) ℂ)) := by
  change ((next z).localAliceOperator_B t * C.op z) ⊗ₖ
      (next z).localBobOperator_B t = _
  unfold localHistoryOperator_B
  rw [← Matrix.mul_kronecker_mul, Matrix.mul_one]

theorem localHistoryOperator_bob_B {p : ℝ} {a b bo af bf k : ℕ}
    (C : KrausChannel (Fin b) (Fin bo) (Fin k))
    (next : Fin k → FiniteKeyProtocol p a bo af bf)
    (z : Fin k) (t : (next z).Environment) :
    (FiniteKeyProtocol.bob C next).localHistoryOperator_B ⟨z, t⟩ =
      (next z).localHistoryOperator_B t *
        ((1 : Matrix (Fin a) (Fin a) ℂ) ⊗ₖ C.op z) := by
  change (next z).localAliceOperator_B t ⊗ₖ
      ((next z).localBobOperator_B t * C.op z) = _
  unfold localHistoryOperator_B
  rw [← Matrix.mul_kronecker_mul, Matrix.mul_one]

theorem localHistoryOperator_complete_B {p : ℝ} {a b af bf : ℕ}
    (P : FiniteKeyProtocol p a b af bf) : P.LocalOnly_B →
    (∑ h, (P.localHistoryOperator_B h)ᴴ * P.localHistoryOperator_B h) = 1 := by
  induction P with
  | done a b =>
      intro _
      change (∑ _ : Unit, ((1 : Matrix (Fin a) (Fin a) ℂ) ⊗ₖ
        (1 : Matrix (Fin b) (Fin b) ℂ))ᴴ *
        ((1 : Matrix (Fin a) (Fin a) ℂ) ⊗ₖ (1 : Matrix (Fin b) (Fin b) ℂ))) = _
      simp [Matrix.one_kronecker_one]
  | @alice a b ao af bf k C next ih =>
      intro hP
      have hc := KrausChannel.completeAdaptiveFamily_B (C.withRightMemory (Fin b))
        (fun z t => (next z).localHistoryOperator_B t) (fun z => ih z (hP z))
      calc
        _ = ∑ h : (z : Fin k) × (next z).Environment,
            ((next h.1).localHistoryOperator_B h.2 * (C.withRightMemory (Fin b)).op h.1)ᴴ *
              ((next h.1).localHistoryOperator_B h.2 * (C.withRightMemory (Fin b)).op h.1) := by
          apply Finset.sum_congr rfl
          intro h _
          rcases h with ⟨z, t⟩
          rw [localHistoryOperator_alice_B]
          rfl
        _ = 1 := hc
  | @bob a b bo af bf k C next ih =>
      intro hP
      have hc := KrausChannel.completeAdaptiveFamily_B (C.withMemory (Fin a))
        (fun z t => (next z).localHistoryOperator_B t) (fun z => ih z (hP z))
      calc
        _ = ∑ h : (z : Fin k) × (next z).Environment,
            ((next h.1).localHistoryOperator_B h.2 * (C.withMemory (Fin a)).op h.1)ᴴ *
              ((next h.1).localHistoryOperator_B h.2 * (C.withMemory (Fin a)).op h.1) := by
          apply Finset.sum_congr rfl
          intro h _
          rcases h with ⟨z, t⟩
          rw [localHistoryOperator_bob_B]
          rfl
        _ = 1 := hc
  | @call a b af bf next ih => intro hP; exact False.elim hP

theorem localOnly_fullOutput_apply_B {p : ℝ} {a b af bf : ℕ}
    (P : FiniteKeyProtocol p a b af bf) : P.LocalOnly_B →
    ∀ (ρ : PhysicalProtocol.BipartiteMatrix a b)
      (x y : Fin af × Fin bf) (h h' : P.Environment),
      P.fullOutput ρ (x, h) (y, h') =
        if h = h' then
          (P.localHistoryOperator_B h * ρ * (P.localHistoryOperator_B h)ᴴ) x y else 0 := by
  classical
  induction P with
  | done a b =>
      intro _ ρ x y h h'
      cases h
      cases h'
      split_ifs with hh
      · simp [fullOutput, localHistoryOperator_B, localAliceOperator_B, localBobOperator_B,
          Matrix.one_kronecker_one]
      · exact (hh rfl).elim
  | @alice a b ao af bf k C next ih =>
      intro hP ρ x y h h'
      rcases h with ⟨z, t⟩
      rcases h' with ⟨z', t'⟩
      by_cases hz : z = z'
      · subst z'
        simp only [fullOutput, dif_pos rfl]
        rw [ih z (hP z)]
        by_cases ht : t = t'
        · subst t'
          split_ifs <;> first
            | contradiction
            | (rw [localHistoryOperator_alice_B]
               simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc])
        · have hh : (Sigma.mk z t : (FiniteKeyProtocol.alice C next).Environment) ≠
              Sigma.mk z t' := by simpa using ht
          split_ifs <;> first | contradiction | rfl
      · have hh : (Sigma.mk z t : (FiniteKeyProtocol.alice C next).Environment) ≠
            Sigma.mk z' t' := fun h => hz (Sigma.mk.inj_iff.mp h).1
        simp only [fullOutput, dif_neg hz]
        split_ifs <;> first | contradiction | rfl
  | @bob a b bo af bf k C next ih =>
      intro hP ρ x y h h'
      rcases h with ⟨z, t⟩
      rcases h' with ⟨z', t'⟩
      by_cases hz : z = z'
      · subst z'
        simp only [fullOutput, dif_pos rfl]
        rw [ih z (hP z)]
        by_cases ht : t = t'
        · subst t'
          split_ifs <;> first
            | contradiction
            | (rw [localHistoryOperator_bob_B]
               simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc])
        · have hh : (Sigma.mk z t : (FiniteKeyProtocol.bob C next).Environment) ≠
              Sigma.mk z t' := by simpa using ht
          split_ifs <;> first | contradiction | rfl
      · have hh : (Sigma.mk z t : (FiniteKeyProtocol.bob C next).Environment) ≠
            Sigma.mk z' t' := fun h => hz (Sigma.mk.inj_iff.mp h).1
        simp only [fullOutput, dif_neg hz]
        split_ifs <;> first | contradiction | rfl
  | @call a b af bf next ih => intro hP; exact False.elim hP

end QuantumProver.AmplitudeDamping.SecretKey.PhysicalProtocol.FiniteKeyProtocol

namespace QuantumProver.AmplitudeDamping.SecretKey.PublicHistory

open PhysicalProtocol PhysicalProtocol.FiniteKeyProtocol

def localCopiedHonestOperator_B {p : ℝ} {a b af bf : ℕ}
    (P : FiniteKeyProtocol p a b af bf) (h : P.Environment) :
    Matrix ((P.Environment × Fin af) × (P.Environment × Fin bf)) (Fin a × Fin b) ℂ := by
  classical
  exact (attachFlag_B (A := Fin af) h ⊗ₖ attachFlag_B (A := Fin bf) h) *
    P.localHistoryOperator_B h

def localCopiedInstrumentWithEve_B {p : ℝ} {a b af bf : ℕ}
    (P : FiniteKeyProtocol p a b af bf) (hP : P.LocalOnly_B)
    (E : Type*) [Fintype E] [DecidableEq E] :
    KrausChannel ((Fin a × Fin b) × E)
      (((P.Environment × Fin af) × (P.Environment × Fin bf)) ×
        (P.Environment × E)) P.Environment := by
  classical
  refine ⟨(fun h => localCopiedHonestOperator_B P h ⊗ₖ attachFlag_B (A := E) h), ?_⟩
  simp_rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
    attachFlag_complete_B]
  have hgram (h : P.Environment) :
      (localCopiedHonestOperator_B P h)ᴴ * localCopiedHonestOperator_B P h =
        (P.localHistoryOperator_B h)ᴴ * P.localHistoryOperator_B h :=
    isometry_left_gram_B _ _ (attachFlag_pair_complete_B h)
  simp_rw [hgram]
  calc
    _ = (∑ h, (P.localHistoryOperator_B h)ᴴ * P.localHistoryOperator_B h) ⊗ₖ
        (1 : Matrix E E ℂ) := by
      ext x y
      simp only [Matrix.sum_apply, Matrix.kroneckerMap_apply, Finset.sum_mul]
    _ = (1 : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) ⊗ₖ
        (1 : Matrix E E ℂ) := by rw [P.localHistoryOperator_complete_B hP]
    _ = 1 := Matrix.one_kronecker_one

def localPriorEveMatrix_B {p : ℝ} {a b af bf : ℕ}
    (P : FiniteKeyProtocol p a b af bf) {E : Type*}
    (ρ : Matrix ((Fin a × Fin b) × E) ((Fin a × Fin b) × E) ℂ) :
    Matrix ((Fin af × Fin bf) × (P.Environment × E))
      ((Fin af × Fin bf) × (P.Environment × E)) ℂ :=
  fun x y => P.fullOutput (Matrix.of (fun i j => ρ (i, x.2.2) (j, y.2.2)))
    (x.1, x.2.1) (y.1, y.2.1)

theorem localCopiedInstrumentWithEve_eval_apply_B {p : ℝ} {a b af bf : ℕ}
    (P : FiniteKeyProtocol p a b af bf) (hP : P.LocalOnly_B)
    {E : Type*} [Fintype E] [DecidableEq E]
    (ρ : Matrix ((Fin a × Fin b) × E) ((Fin a × Fin b) × E) ℂ)
    (i k h i' k' h' : P.Environment) (a' a'' : Fin af) (b' b'' : Fin bf) (e e' : E) :
    (localCopiedInstrumentWithEve_B P hP E).eval ρ
      (((i, a'), (k, b')), (h, e)) (((i', a''), (k', b'')), (h', e')) =
      if i = k ∧ i = h ∧ i = i' ∧ i = k' ∧ i = h' then
        (P.localHistoryOperator_B i * Matrix.of (fun x y => ρ (x, e) (y, e')) *
          (P.localHistoryOperator_B i)ᴴ) (a', b') (a'', b'') else 0 := by
  classical
  have heval : (localCopiedInstrumentWithEve_B P hP E).eval ρ =
      copyPublicHistoryWithEve_B (fun h =>
        ((P.localHistoryOperator_B h ⊗ₖ (1 : Matrix E E ℂ)) * ρ *
          (P.localHistoryOperator_B h ⊗ₖ (1 : Matrix E E ℂ))ᴴ)) := by
    unfold KrausChannel.eval copyPublicHistoryWithEve_B
    apply Finset.sum_congr rfl
    intro h _
    have hop : localCopiedHonestOperator_B P h ⊗ₖ attachFlag_B (A := E) h =
        ((attachFlag_B (A := Fin af) h ⊗ₖ attachFlag_B (A := Fin bf) h) ⊗ₖ
          attachFlag_B (A := E) h) *
          (P.localHistoryOperator_B h ⊗ₖ (1 : Matrix E E ℂ)) := by
      rw [← Matrix.mul_kronecker_mul, Matrix.mul_one]
      rfl
    change ((localCopiedHonestOperator_B P h ⊗ₖ attachFlag_B (A := E) h) * ρ *
      (localCopiedHonestOperator_B P h ⊗ₖ attachFlag_B (A := E) h)ᴴ) = _
    simp_rw [hop]
    simp only [publicBranchWithEve_B, Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [heval, copyPublicHistoryWithEve_apply_B, congruence_rightMemory_apply_B]

theorem localCopiedInstrumentWithEve_isometric_alignment_B {p : ℝ} {a b af bf : ℕ}
    (P : FiniteKeyProtocol p a b af bf) (hP : P.LocalOnly_B)
    {E : Type*} [Fintype E] [DecidableEq E]
    (ρ : Matrix ((Fin a × Fin b) × E) ((Fin a × Fin b) × E) ℂ) :
    (localCopiedInstrumentWithEve_B P hP E).eval ρ =
      historyCopyEmbedding_B (F := P.Environment) (A := Fin af) (B := Fin bf) (E := E) *
        localPriorEveMatrix_B P ρ *
        (historyCopyEmbedding_B (F := P.Environment) (A := Fin af) (B := Fin bf) (E := E))ᴴ := by
  classical
  ext x y
  rcases x with ⟨⟨⟨i, a'⟩, ⟨k, b'⟩⟩, ⟨h, e⟩⟩
  rcases y with ⟨⟨⟨i', a''⟩, ⟨k', b''⟩⟩, ⟨h', e'⟩⟩
  rw [localCopiedInstrumentWithEve_eval_apply_B, historyCopyEmbedding_sandwich_apply_B]
  simp only [localPriorEveMatrix_B, P.localOnly_fullOutput_apply_B hP]
  by_cases hi : i = h <;> by_cases hk : k = h <;>
    by_cases hi' : i' = h' <;> by_cases hk' : k' = h' <;> by_cases hh : h = h' <;>
    simp_all [eq_comm]

end QuantumProver.AmplitudeDamping.SecretKey.PublicHistory

namespace QuantumProver.AmplitudeDamping.SecretKey.PhysicalProtocol

theorem transferComparisonChannel_op_B {J : Type*} [Fintype J]
    (C : KrausChannel (Fin 2) (Fin 2) J) (a b : ℕ) (z : J)
    (x : Fin a × Fin (2 * b)) (y : Fin (2 * a) × Fin b) :
    (transferComparisonChannel_B C a b).op z x y =
      C.op z (splitQubit b x.2).1 (splitQubit a y.1).1 *
        if x.1 = (splitQubit a y.1).2 ∧ (splitQubit b x.2).2 = y.2 then 1 else 0 := by
  by_cases ha : x.1 = (splitQubit a y.1).2 <;>
    by_cases hb : (splitQubit b x.2).2 = y.2 <;>
    simp [transferComparisonChannel_B, KrausChannel.relabel_B,
      KrausChannel.withMemory, KrausChannel.withRightMemory,
      comparisonInputLocalEquiv_B, Matrix.submatrix_apply,
      Matrix.kroneckerMap_apply, Matrix.one_apply, ha, hb]

theorem transferKraus_complete_B {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (a b : ℕ) :
    (∑ z, (transferKraus p a b z)ᴴ * transferKraus p a b z) = 1 := by
  have hop (z : Fin 2) :
      (transferComparisonChannel_B (amplitudeDamping p hp0 hp1) a b).op z =
        transferKraus p a b z := by
    ext x y
    rw [transferComparisonChannel_op_B]
    rfl
  have hc := (transferComparisonChannel_B (amplitudeDamping p hp0 hp1) a b).complete
  simpa only [hop] using hc

namespace FiniteKeyProtocol

noncomputable instance comparisonPublicHistoryDecidableEq_B {p : ℝ} {a b af bf : ℕ}
    (P : FiniteKeyProtocol p a b af bf) : DecidableEq P.comparisonPublicHistory_B :=
  Classical.decEq _

def publicTranscript_B {p : ℝ} {a b af bf : ℕ}
    (P : FiniteKeyProtocol p a b af bf) : P.Environment → P.comparisonPublicHistory_B :=
  match P with
  | .done _ _ => fun _ => ()
  | .alice _ next => fun h => ⟨h.1, (next h.1).publicTranscript_B h.2⟩
  | .bob _ next => fun h => ⟨h.1, (next h.1).publicTranscript_B h.2⟩
  | .call next => fun h => next.publicTranscript_B h.2

def historyKraus_B {p : ℝ} {a b af bf : ℕ}
    (P : FiniteKeyProtocol p a b af bf) :
    P.Environment → Matrix (Fin af × Fin bf) (Fin a × Fin b) ℂ :=
  match P with
  | .done _ _ => fun _ => 1
  | .alice (b := b₀) C next => fun h =>
      (next h.1).historyKraus_B h.2 * (C.op h.1 ⊗ₖ (1 : Matrix (Fin b₀) (Fin b₀) ℂ))
  | .bob (a := a₀) C next => fun h =>
      (next h.1).historyKraus_B h.2 * ((1 : Matrix (Fin a₀) (Fin a₀) ℂ) ⊗ₖ C.op h.1)
  | .call (a := a₀) (b := b₀) next => fun h =>
      next.historyKraus_B h.2 * transferKraus p a₀ b₀ h.1

theorem historyKraus_complete_B {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {a b af bf : ℕ} (P : FiniteKeyProtocol p a b af bf) :
    (∑ h, (P.historyKraus_B h)ᴴ * P.historyKraus_B h) = 1 := by
  induction P with
  | done a b =>
      change (∑ _ : Unit, (1 : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ)ᴴ * 1) = _
      simp
  | @alice a b ao af bf k C next ih =>
      exact (by
        change (∑ h : (z : Fin k) × (next z).Environment,
          ((next h.1).historyKraus_B h.2 * (C.withRightMemory (Fin b)).op h.1)ᴴ *
            ((next h.1).historyKraus_B h.2 * (C.withRightMemory (Fin b)).op h.1)) = 1
        exact KrausChannel.completeAdaptiveFamily_B (C.withRightMemory (Fin b))
          (fun z t => (next z).historyKraus_B t) ih)
  | @bob a b bo af bf k C next ih =>
      exact (by
        change (∑ h : (z : Fin k) × (next z).Environment,
          ((next h.1).historyKraus_B h.2 * (C.withMemory (Fin a)).op h.1)ᴴ *
            ((next h.1).historyKraus_B h.2 * (C.withMemory (Fin a)).op h.1)) = 1
        exact KrausChannel.completeAdaptiveFamily_B (C.withMemory (Fin a))
          (fun z t => (next z).historyKraus_B t) ih)
  | @call a b af bf next ih =>
      change (∑ h : Fin 2 × next.Environment,
        (next.historyKraus_B h.2 * transferKraus p a b h.1)ᴴ *
          (next.historyKraus_B h.2 * transferKraus p a b h.1)) = 1
      rw [Fintype.sum_prod_type]
      simp only [Matrix.conjTranspose_mul]
      calc
        _ = ∑ z, (transferKraus p a b z)ᴴ *
            (∑ t, (next.historyKraus_B t)ᴴ * next.historyKraus_B t) *
              transferKraus p a b z := by
          apply Finset.sum_congr rfl
          intro z _
          simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_assoc]
        _ = ∑ z, (transferKraus p a b z)ᴴ * transferKraus p a b z := by
          rw [ih]
          simp only [Matrix.mul_one]
        _ = 1 := transferKraus_complete_B hp0 hp1 a b

theorem fullOutput_historyKraus_apply_B {p : ℝ} {a b af bf : ℕ}
    (P : FiniteKeyProtocol p a b af bf) :
    ∀ (ρ : BipartiteMatrix a b) (x y : Fin af × Fin bf) (h h' : P.Environment),
      P.fullOutput ρ (x, h) (y, h') =
        if P.publicTranscript_B h = P.publicTranscript_B h' then
          (P.historyKraus_B h * ρ * (P.historyKraus_B h')ᴴ) x y else 0 := by
  classical
  induction P with
  | done a b =>
      intro ρ x y h h'
      cases h
      cases h'
      split_ifs with hh
      · simp [fullOutput, historyKraus_B]
      · exact (hh rfl).elim
  | @alice a b ao af bf k C next ih =>
      intro ρ x y h h'
      rcases h with ⟨z,t⟩
      rcases h' with ⟨z',t'⟩
      by_cases hz : z = z'
      · subst z'
        simp only [fullOutput]
        rw [ih z]
        have hhist : (FiniteKeyProtocol.alice C next).publicTranscript_B ⟨z,t⟩ =
            (FiniteKeyProtocol.alice C next).publicTranscript_B ⟨z,t'⟩ ↔
            (next z).publicTranscript_B t = (next z).publicTranscript_B t' := by
          change (@Sigma.mk (Fin k) (fun u => (next u).comparisonPublicHistory_B) z
            ((next z).publicTranscript_B t) =
            @Sigma.mk (Fin k) (fun u => (next u).comparisonPublicHistory_B) z
            ((next z).publicTranscript_B t')) ↔ _
          constructor
          · intro h
            exact eq_of_heq (Sigma.mk.inj_iff.mp h).2
          · intro h
            exact congrArg (fun v : (next z).comparisonPublicHistory_B =>
              @Sigma.mk (Fin k) (fun u => (next u).comparisonPublicHistory_B) z v) h
        simp only [hhist, historyKraus_B]
        split_ifs <;> first | contradiction |
          (simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc])
      · have hh : (FiniteKeyProtocol.alice C next).publicTranscript_B ⟨z,t⟩ ≠
            (FiniteKeyProtocol.alice C next).publicTranscript_B ⟨z',t'⟩ := by
          intro h
          exact hz (Sigma.mk.inj_iff.mp h).1
        simp only [fullOutput, dif_neg hz]
        split_ifs <;> first | contradiction | rfl
  | @bob a b bo af bf k C next ih =>
      intro ρ x y h h'
      rcases h with ⟨z,t⟩
      rcases h' with ⟨z',t'⟩
      by_cases hz : z = z'
      · subst z'
        simp only [fullOutput]
        rw [ih z]
        have hhist : (FiniteKeyProtocol.bob C next).publicTranscript_B ⟨z,t⟩ =
            (FiniteKeyProtocol.bob C next).publicTranscript_B ⟨z,t'⟩ ↔
            (next z).publicTranscript_B t = (next z).publicTranscript_B t' := by
          change (@Sigma.mk (Fin k) (fun u => (next u).comparisonPublicHistory_B) z
            ((next z).publicTranscript_B t) =
            @Sigma.mk (Fin k) (fun u => (next u).comparisonPublicHistory_B) z
            ((next z).publicTranscript_B t')) ↔ _
          constructor
          · intro h
            exact eq_of_heq (Sigma.mk.inj_iff.mp h).2
          · intro h
            exact congrArg (fun v : (next z).comparisonPublicHistory_B =>
              @Sigma.mk (Fin k) (fun u => (next u).comparisonPublicHistory_B) z v) h
        simp only [hhist, historyKraus_B]
        split_ifs <;> first | contradiction |
          (simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc])
      · have hh : (FiniteKeyProtocol.bob C next).publicTranscript_B ⟨z,t⟩ ≠
            (FiniteKeyProtocol.bob C next).publicTranscript_B ⟨z',t'⟩ := by
          intro h
          exact hz (Sigma.mk.inj_iff.mp h).1
        simp only [fullOutput, dif_neg hz]
        split_ifs <;> first | contradiction | rfl
  | @call a b af bf next ih =>
      intro ρ x y h h'
      rcases h with ⟨z,t⟩
      rcases h' with ⟨z',t'⟩
      simp only [fullOutput, publicTranscript_B]
      rw [ih]
      simp only [historyKraus_B, Matrix.conjTranspose_mul, Matrix.mul_assoc]
      split_ifs <;> first | contradiction | rfl

end FiniteKeyProtocol
end QuantumProver.AmplitudeDamping.SecretKey.PhysicalProtocol

namespace QuantumProver.AmplitudeDamping.SecretKey.PublicHistory

open PhysicalProtocol PhysicalProtocol.FiniteKeyProtocol

def wholePublicCopiedOperator_B {p : ℝ} {a b af bf : ℕ}
    (P : FiniteKeyProtocol p a b af bf) (h : P.Environment) :
    Matrix ((P.comparisonPublicHistory_B × Fin af) ×
      (P.comparisonPublicHistory_B × Fin bf)) (Fin a × Fin b) ℂ :=
  (attachFlag_B (A := Fin af) (P.publicTranscript_B h) ⊗ₖ
    attachFlag_B (A := Fin bf) (P.publicTranscript_B h)) * P.historyKraus_B h

def wholePublicCopiedChannel_B {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {a b af bf : ℕ} (P : FiniteKeyProtocol p a b af bf) :
    KrausChannel (Fin a × Fin b)
      ((P.comparisonPublicHistory_B × Fin af) ×
        (P.comparisonPublicHistory_B × Fin bf)) P.Environment where
  op := wholePublicCopiedOperator_B P
  complete := by
    have hg (h : P.Environment) :
        (wholePublicCopiedOperator_B P h)ᴴ * wholePublicCopiedOperator_B P h =
          (P.historyKraus_B h)ᴴ * P.historyKraus_B h :=
      isometry_left_gram_B _ _ (attachFlag_pair_complete_B (P.publicTranscript_B h))
    simp_rw [hg]
    exact P.historyKraus_complete_B hp0 hp1

end QuantumProver.AmplitudeDamping.SecretKey.PublicHistory

namespace QuantumProver.AmplitudeDamping.SecretKey.PublicHistory

variable {I O J E : Type*} [Fintype I] [Fintype O] [Fintype J] [Fintype E]
  [DecidableEq I] [DecidableEq E]

def retainedWithPriorEveOperator_B (C : KrausChannel I O J) :
    Matrix (O × (J × E)) (I × E) ℂ :=
  (C.stinespring ⊗ₖ (1 : Matrix E E ℂ)).submatrix
    (Equiv.prodAssoc O J E).symm (Equiv.refl (I × E))

theorem retainedWithPriorEveOperator_isometry_B (C : KrausChannel I O J) :
    (retainedWithPriorEveOperator_B (E := E) C)ᴴ *
      retainedWithPriorEveOperator_B (E := E) C = 1 := by
  simp only [retainedWithPriorEveOperator_B, Matrix.conjTranspose_submatrix,
    Matrix.submatrix_mul_equiv, Matrix.conjTranspose_kronecker,
    Matrix.conjTranspose_one, ← Matrix.mul_kronecker_mul,
    C.stinespring_isometry, Matrix.one_mul, Matrix.one_kronecker_one,
    Matrix.submatrix_one_equiv]

def retainedWithPriorEveChannel_B (C : KrausChannel I O J) :
    KrausChannel (I × E) (O × (J × E)) Unit where
  op := fun _ => retainedWithPriorEveOperator_B C
  complete := by
    simp only [Fintype.sum_unique]
    exact retainedWithPriorEveOperator_isometry_B C

theorem retainedWithPriorEve_eval_apply_B (C : KrausChannel I O J)
    (ρ : Matrix (I × E) (I × E) ℂ) (o o' : O) (h h' : J) (e e' : E) :
    (retainedWithPriorEveChannel_B (E := E) C).eval ρ
      (o,(h,e)) (o',(h',e')) =
      (C.op h * Matrix.of (fun i j => ρ (i,e) (j,e')) * (C.op h')ᴴ) o o' := by
  classical
  simp [KrausChannel.eval, retainedWithPriorEveChannel_B,
    retainedWithPriorEveOperator_B, KrausChannel.stinespring,
    Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.kroneckerMap_apply,
    Matrix.submatrix_apply, Matrix.one_apply, Fintype.sum_prod_type,
    Finset.sum_mul, Finset.mul_sum, Matrix.of_apply, apply_ite, ite_mul, mul_ite, mul_assoc]

theorem reference_basisReadout_apply_B {K : Type*} [Fintype K] [DecidableEq K]
    (label : I → K) (ρ : Matrix (I × E) (I × E) ℂ)
    (k k' : K) (e e' : E) :
    ((basisReadoutChannel label).withRightMemory E).eval ρ (k,e) (k',e') =
      ∑ i, if k = label i ∧ k' = label i then ρ (i,e) (i,e') else 0 := by
  simp only [KrausChannel.eval, KrausChannel.withRightMemory,
    Matrix.sum_apply, congruence_rightMemory_apply_B]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hk : k = label i <;> by_cases hk' : k' = label i <;>
    simp [basisReadoutChannel, Matrix.single_apply, Matrix.mul_apply,
      Matrix.conjTranspose_apply, hk, hk', Matrix.of_apply, eq_comm, ite_mul, mul_ite]

end QuantumProver.AmplitudeDamping.SecretKey.PublicHistory

namespace QuantumProver.AmplitudeDamping.SecretKey.PublicHistory

variable {F A B K : Type*} [Fintype F] [Fintype A] [Fintype B] [Fintype K]
  [DecidableEq F] [DecidableEq A] [DecidableEq B] [DecidableEq K]

def crossPublicBranch_B (j j' : F) (σ : Matrix (A × B) (A × B) ℂ) :
    Matrix ((F × A) × (F × B)) ((F × A) × (F × B)) ℂ :=
  (attachFlag_B (A := A) j ⊗ₖ attachFlag_B (A := B) j) * σ *
    (attachFlag_B (A := A) j' ⊗ₖ attachFlag_B (A := B) j')ᴴ

theorem crossPublicBranch_diagonal_B (j j' i k : F)
    (σ : Matrix (A × B) (A × B) ℂ) (a : A) (b : B) :
    crossPublicBranch_B j j' σ ((i,a),(k,b)) ((i,a),(k,b)) =
      if i = j ∧ k = j ∧ i = j' ∧ k = j' then σ (a,b) (a,b) else 0 := by
  by_cases hj : j = j'
  · subst j'
    simpa only [crossPublicBranch_B, publicBranch_B] using
      publicBranch_apply_B j i k i k σ a a b b
  · by_cases hi : i = j <;> by_cases hk : k = j <;>
      by_cases hi' : i = j' <;> by_cases hk' : k = j' <;>
      simp_all [crossPublicBranch_B, attachFlag_B, Matrix.mul_apply,
        Matrix.conjTranspose_apply, Matrix.kroneckerMap_apply,
        Fintype.sum_prod_type, Matrix.one_apply, ite_mul, mul_ite, apply_ite]

theorem sum_two_copied_registers_B (f : F → A → F → B → ℂ) :
    (∑ x : (F × A) × (F × B), f x.1.1 x.1.2 x.2.1 x.2.2) =
      ∑ a : A, ∑ b : B, ∑ i : F, ∑ k : F, f i a k b := by
  simp only [Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  calc
    _ = ∑ i : F, ∑ b : B, ∑ k : F, f i a k b := by
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm
    _ = _ := Finset.sum_comm

theorem sum_crossPublicBranch_readout_B (label : A × B → K)
    (j j' : F) (σ : Matrix (A × B) (A × B) ℂ) (k k' : K) :
    (∑ x : (F × A) × (F × B),
      if k = label (x.1.2,x.2.2) ∧ k' = label (x.1.2,x.2.2) then
        crossPublicBranch_B j j' σ x x else 0) =
      if j = j' then
        ∑ x : A × B, if k = label x ∧ k' = label x then σ x x else 0
      else 0 := by
  let f : F → A → F → B → ℂ := fun i a l b =>
    if k = label (a,b) ∧ k' = label (a,b) then
      crossPublicBranch_B j j' σ ((i,a),(l,b)) ((i,a),(l,b)) else 0
  change (∑ x : (F × A) × (F × B), f x.1.1 x.1.2 x.2.1 x.2.2) = _
  rw [sum_two_copied_registers_B]
  simp only [f, crossPublicBranch_diagonal_B]
  by_cases hj : j = j'
  · subst j'
    rw [if_pos rfl, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    by_cases hk : k = label (a,b) <;> by_cases hk' : k' = label (a,b) <;>
      simp [hk,hk',eq_comm]
    all_goals
      symm
      rw [Finset.sum_eq_single j]
      · rw [Finset.sum_eq_single j]
        · simp
        · intro l _ hl
          simp [hl, Ne.symm hl]
        · simp
      · intro i _ hi
        simp [hi, Ne.symm hi]
      · simp
  · have himpossible (i l : F) : ¬(i = j ∧ l = j ∧ i = j' ∧ l = j') := by
      intro h
      exact hj (h.1.symm.trans h.2.2.1)
    simp [hj,himpossible]

end QuantumProver.AmplitudeDamping.SecretKey.PublicHistory

namespace QuantumProver.AmplitudeDamping.SecretKey.PublicHistory

open PhysicalProtocol PhysicalProtocol.FiniteKeyProtocol

def wholeRetainedChannelWithEve_B {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {a b af bf : ℕ} (P : FiniteKeyProtocol p a b af bf)
    (E : Type*) [Fintype E] [DecidableEq E] :
    KrausChannel ((Fin a × Fin b) × E)
      (((P.comparisonPublicHistory_B × Fin af) ×
        (P.comparisonPublicHistory_B × Fin bf)) × (P.Environment × E)) Unit :=
  retainedWithPriorEveChannel_B (E := E) (wholePublicCopiedChannel_B hp0 hp1 P)

theorem wholeRetainedChannelWithEve_apply_B {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {a b af bf : ℕ} (P : FiniteKeyProtocol p a b af bf)
    {E : Type*} [Fintype E] [DecidableEq E]
    (ρ : Matrix ((Fin a × Fin b) × E) ((Fin a × Fin b) × E) ℂ)
    (x : (P.comparisonPublicHistory_B × Fin af) × (P.comparisonPublicHistory_B × Fin bf))
    (h h' : P.Environment) (e e' : E) :
    (wholeRetainedChannelWithEve_B hp0 hp1 P E).eval ρ (x,(h,e)) (x,(h',e')) =
      crossPublicBranch_B (P.publicTranscript_B h) (P.publicTranscript_B h')
        (P.historyKraus_B h * Matrix.of (fun i j => ρ (i,e) (j,e')) *
          (P.historyKraus_B h')ᴴ) x x := by
  rw [wholeRetainedChannelWithEve_B, retainedWithPriorEve_eval_apply_B]
  simp only [wholePublicCopiedChannel_B, wholePublicCopiedOperator_B,
    crossPublicBranch_B, Matrix.conjTranspose_mul, Matrix.mul_assoc]

theorem wholeRetainedChannelWithEve_readout_B {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {a b af bf : ℕ} (P : FiniteKeyProtocol p a b af bf)
    {E K : Type*} [Fintype E] [DecidableEq E] [Fintype K] [DecidableEq K]
    (label : Fin af × Fin bf → K)
    (ρ : Matrix ((Fin a × Fin b) × E) ((Fin a × Fin b) × E) ℂ) :
    ((basisReadoutChannel (fun x :
      (P.comparisonPublicHistory_B × Fin af) × (P.comparisonPublicHistory_B × Fin bf) =>
        label (x.1.2,x.2.2))).withRightMemory (P.Environment × E)).eval
        ((wholeRetainedChannelWithEve_B hp0 hp1 P E).eval ρ) =
      ((basisReadoutChannel label).withRightMemory (P.Environment × E)).eval
        (localPriorEveMatrix_B P ρ) := by
  classical
  ext x y
  rcases x with ⟨k,⟨h,e⟩⟩
  rcases y with ⟨k',⟨h',e'⟩⟩
  rw [reference_basisReadout_apply_B, reference_basisReadout_apply_B]
  simp only [wholeRetainedChannelWithEve_apply_B, localPriorEveMatrix_B,
    P.fullOutput_historyKraus_apply_B]
  have hs := sum_crossPublicBranch_readout_B label
    (P.publicTranscript_B h) (P.publicTranscript_B h')
    (P.historyKraus_B h * Matrix.of (fun i j => ρ (i,e) (j,e')) *
      (P.historyKraus_B h')ᴴ) k k'
  by_cases hpub : P.publicTranscript_B h = P.publicTranscript_B h'
  · simpa [hpub] using hs
  · simpa [hpub] using hs

end QuantumProver.AmplitudeDamping.SecretKey.PublicHistory

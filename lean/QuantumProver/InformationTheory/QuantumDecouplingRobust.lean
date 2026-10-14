import QuantumProver.InformationTheory.QuantumDecoupling

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

noncomputable section

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker

namespace QuantumProver.QuantumDecouplingRobust

open QuantumProver.QuantumDecoupling QuantumProver.QuantumEntropy QuantumProver.UnitarySecondMoment
open QuantumProver.SandwichedDPI
open QuantumProver.SuperchannelDiscrimination
open KrausCompletion

variable {I O J K R : Type*} [Fintype I] [DecidableEq I]
  [Fintype O] [DecidableEq O] [Fintype J] [DecidableEq J]
  [Fintype K] [DecidableEq K] [Fintype R] [DecidableEq R]
variable {d : ℕ}

private theorem traceNorm_add_le (X Y : Matrix I I ℂ) :
    traceNorm (X + Y) ≤ traceNorm X + traceNorm Y := by
  obtain ⟨U, hU, htrace⟩ := exists_unitary_traceNorm_attainer (X + Y)
  rw [← htrace, Matrix.mul_add, Matrix.trace_add, Complex.add_re]
  exact add_le_add (re_trace_unitary_mul_le_traceNorm X U hU)
    (re_trace_unitary_mul_le_traceNorm Y U hU)

private theorem traceNorm_sub_le (X Y : Matrix I I ℂ) :
    traceNorm (X - Y) ≤ traceNorm X + traceNorm Y := by
  have h := traceNorm_add_le X (-Y)
  simpa only [sub_eq_add_neg, traceNorm, CFC.abs_neg] using h

theorem partialTrace_left_traceNorm_le (X : Matrix (I × R) (I × R) ℂ) :
    traceNorm (partialTrace_left X) ≤ traceNorm X := by
  rw [← leftTraceKraus_action]
  exact traceNorm_krausAction_le leftTraceKraus leftTraceKraus_complete X

theorem reindex_traceNorm_le (e : I ≃ O) (X : Matrix I I ℂ) :
    traceNorm (Matrix.reindex e e X) ≤ traceNorm X := by
  exact traceNorm_map_le_of_cp_tracePreserving
    (CPWrappers.completelyPositive_reindexMap e)
    (CPWrappers.reindexMap_tracePreserving e) X

theorem localUnitary_traceNorm_le (U : UGroup d)
    (X : Matrix (Fin d × R) (Fin d × R) ℂ) :
    traceNorm (((U : CMat d) ⊗ₖ (1 : Matrix R R ℂ)) * X *
      ((U : CMat d) ⊗ₖ (1 : Matrix R R ℂ))ᴴ) ≤ traceNorm X := by
  let V := (U : CMat d) ⊗ₖ (1 : Matrix R R ℂ)
  have hcomplete : krausGram (fun _ : Unit => V) = 1 := by
    simpa only [krausGram, Fintype.sum_unique] using localUnitary_gram (R := R) U
  simpa only [krausAction, Fintype.sum_unique] using
    traceNorm_krausAction_le (fun _ : Unit => V) hcomplete X

theorem decoupledMarginal_traceNorm_le (e : Fin d ≃ J × K)
    (X : Matrix (Fin d × R) (Fin d × R) ℂ) (U : UGroup d) :
    traceNorm (decoupledMarginal e X U) ≤ traceNorm X := by
  exact (partialTrace_left_traceNorm_le _).trans
    ((reindex_traceNorm_le (spectatorChart e) _).trans (localUnitary_traceNorm_le U X))

def uniformInsertionKraus (k : K) : Matrix (K × R) R ℂ :=
  (((Real.sqrt (Fintype.card K : ℝ))⁻¹ : ℝ) : ℂ) •
    (fun x r => if x.1 = k then (1 : Matrix R R ℂ) x.2 r else 0)

omit [DecidableEq K] in
private theorem uniformInsertionWeight_square :
    (Real.sqrt (Fintype.card K : ℝ) : ℂ)⁻¹ *
      (Real.sqrt (Fintype.card K : ℝ) : ℂ)⁻¹ = (Fintype.card K : ℂ)⁻¹ := by
  have hs : ((Real.sqrt (Fintype.card K : ℝ))⁻¹ : ℝ)^2 =
      (Fintype.card K : ℝ)⁻¹ := by
    rw [inv_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  calc
    _ = ((((Real.sqrt (Fintype.card K : ℝ))⁻¹ : ℝ)^2 : ℝ) : ℂ) := by
      simp [pow_two]
    _ = (((Fintype.card K : ℝ)⁻¹ : ℝ) : ℂ) := congrArg Complex.ofReal hs
    _ = _ := by simp

theorem uniformInsertionKraus_gram (k : K) :
    (uniformInsertionKraus (R := R) k)ᴴ * uniformInsertionKraus k =
      (Fintype.card K : ℂ)⁻¹ • (1 : Matrix R R ℂ) := by
  ext r s
  by_cases h : r = s
  all_goals simp [uniformInsertionKraus, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fintype.sum_prod_type, Matrix.one_apply, apply_ite, ite_mul,
    h, eq_comm]
  exact (uniformInsertionWeight_square (K := K)).symm

theorem uniformInsertionKraus_complete [Nonempty K] :
    krausGram (uniformInsertionKraus (K := K) (R := R)) = 1 := by
  have hk : (Fintype.card K : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [krausGram, uniformInsertionKraus_gram, ← Finset.sum_smul,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_inv_cancel₀ hk, one_smul]

theorem uniformInsertionKraus_action (X : Matrix R R ℂ) :
    krausAction (uniformInsertionKraus (K := K) (R := R)) X =
      (((Fintype.card K : ℂ)⁻¹) • (1 : Matrix K K ℂ)) ⊗ₖ X := by
  ext ⟨k, r⟩ ⟨l, s⟩
  by_cases h : k = l
  all_goals simp [krausAction, uniformInsertionKraus, Matrix.sum_apply,
    Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul, Matrix.conjTranspose_apply,
    Matrix.one_apply, apply_ite, ite_mul, h, eq_comm]
  rw [← uniformInsertionWeight_square (K := K)]
  ring

theorem uniformReference_traceNorm_le
    (X : Matrix (Fin d × R) (Fin d × R) ℂ) :
    traceNorm (uniformReference (K := K) X) ≤ traceNorm X := by
  by_cases hk : Fintype.card K = 0
  · have : IsEmpty K := Fintype.card_eq_zero_iff.mp hk
    have hz : uniformReference (K := K) X = 0 := by
      ext x y
      exact isEmptyElim x.1
    rw [hz]
    simpa [traceNorm, CFC.abs] using traceNorm_nonneg X
  · have : Nonempty K := Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hk)
    change traceNorm ((((Fintype.card K : ℂ)⁻¹) • (1 : Matrix K K ℂ)) ⊗ₖ
      partialTrace_left X) ≤ traceNorm X
    rw [← uniformInsertionKraus_action]
    exact (traceNorm_krausAction_le uniformInsertionKraus uniformInsertionKraus_complete
      (partialTrace_left X)).trans (partialTrace_left_traceNorm_le X)

omit [DecidableEq J] [Fintype K] [DecidableEq K] in
theorem decoupledMarginal_sub (e : Fin d ≃ J × K)
    (ρ ν : Matrix (Fin d × R) (Fin d × R) ℂ) (U : UGroup d) :
    decoupledMarginal e (ρ - ν) U =
      decoupledMarginal e ρ U - decoupledMarginal e ν U := by
  ext x y
  simp [decoupledMarginal, partialTrace_left, Matrix.mul_sub, Matrix.sub_mul,
    Matrix.reindex_apply, Finset.sum_sub_distrib]

omit [Fintype R] [DecidableEq R] in
theorem uniformReference_sub (ρ ν : Matrix (Fin d × R) (Fin d × R) ℂ) :
    uniformReference (K := K) (ρ - ν) =
      uniformReference (K := K) ρ - uniformReference ν := by
  ext x y
  simp [uniformReference, Matrix.kroneckerMap_apply, partialTrace_left,
    Finset.sum_sub_distrib, mul_sub]

theorem decouplingError_difference_traceNorm_le (e : Fin d ≃ J × K)
    (ρ ν : Matrix (Fin d × R) (Fin d × R) ℂ) (U : UGroup d) :
    traceNorm (decouplingError e ρ U - decouplingError e ν U) ≤
      2 * traceNorm (ρ - ν) := by
  have he : decouplingError e ρ U - decouplingError e ν U =
      decoupledMarginal e (ρ - ν) U - uniformReference (K := K) (ρ - ν) := by
    rw [decoupledMarginal_sub, uniformReference_sub]
    unfold decouplingError
    abel
  rw [he]
  exact (traceNorm_sub_le _ _).trans (by
    have hm := decoupledMarginal_traceNorm_le e (ρ - ν) U
    have hr := uniformReference_traceNorm_le (K := K) (ρ - ν)
    linarith)

theorem decouplingError_traceNorm_le_perturbation (e : Fin d ≃ J × K)
    (ρ ν : Matrix (Fin d × R) (Fin d × R) ℂ) (U : UGroup d) :
    traceNorm (decouplingError e ρ U) ≤
      traceNorm (decouplingError e ν U) + 2 * traceNorm (ρ - ν) := by
  have he : decouplingError e ρ U = decouplingError e ν U +
      (decouplingError e ρ U - decouplingError e ν U) := by abel
  calc
    _ = traceNorm (decouplingError e ν U +
        (decouplingError e ρ U - decouplingError e ν U)) := congrArg traceNorm he
    _ ≤ _ := traceNorm_add_le _ _
    _ ≤ _ := add_le_add le_rfl (decouplingError_difference_traceNorm_le e ρ ν U)

theorem decouplingError_traceNorm_le_robust_bound (e : Fin d ≃ J × K)
    (ρ ν : Matrix (Fin d × R) (Fin d × R) ℂ) (U : UGroup d) {ε : ℝ}
    (hclose : traceNorm (ρ - ν) ≤ ε)
    (hU : traceNorm (decouplingError e ν U) ≤
      Real.sqrt (3 * decouplingCost (K := K) ν)) :
    traceNorm (decouplingError e ρ U) ≤
      Real.sqrt (3 * decouplingCost (K := K) ν) + 2 * ε := by
  have h := decouplingError_traceNorm_le_perturbation e ρ ν U
  linarith

section CommonUnitary

variable {J₁ K₁ Y₁ J₂ K₂ Y₂ : Type*}
  [Fintype J₁] [DecidableEq J₁] [Fintype K₁] [DecidableEq K₁]
  [Fintype Y₁] [DecidableEq Y₁]
  [Fintype J₂] [DecidableEq J₂] [Fintype K₂] [DecidableEq K₂]
  [Fintype Y₂] [DecidableEq Y₂]

theorem exists_common_decoupling_unitary_robust
    (e₁ : Fin d ≃ J₁ × K₁) (e₂ : Fin d ≃ J₂ × K₂)
    (ρ₁ ν₁ : Matrix (Fin d × Y₁) (Fin d × Y₁) ℂ)
    (ρ₂ ν₂ : Matrix (Fin d × Y₂) (Fin d × Y₂) ℂ)
    (hν₁ : ν₁.PosSemidef) (hν₂ : ν₂.PosSemidef) {ε₁ ε₂ : ℝ}
    (hclose₁ : traceNorm (ρ₁ - ν₁) ≤ ε₁)
    (hclose₂ : traceNorm (ρ₂ - ν₂) ≤ ε₂) :
    ∃ U : UGroup d,
      traceNorm (decouplingError e₁ ρ₁ U) ≤
        Real.sqrt (3 * decouplingCost (K := K₁) ν₁) + 2 * ε₁ ∧
      traceNorm (decouplingError e₂ ρ₂ U) ≤
        Real.sqrt (3 * decouplingCost (K := K₂) ν₂) + 2 * ε₂ := by
  obtain ⟨U, hU₁, hU₂⟩ := exists_common_decoupling_unitary_bound e₁ e₂ hν₁ hν₂
  exact ⟨U, decouplingError_traceNorm_le_robust_bound e₁ ρ₁ ν₁ U hclose₁ hU₁,
    decouplingError_traceNorm_le_robust_bound e₂ ρ₂ ν₂ U hclose₂ hU₂⟩

end CommonUnitary

end QuantumProver.QuantumDecouplingRobust

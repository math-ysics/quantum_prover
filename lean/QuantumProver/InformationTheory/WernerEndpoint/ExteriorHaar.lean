import QuantumProver.InformationTheory.WernerEndpoint.D5NuclearControl
import QuantumProver.InformationTheory.WernerEndpoint.SlaterSquareMoment
import QuantumProver.InformationTheory.WernerEndpoint.ActualContractionLower

noncomputable section
namespace QuantumProver.WernerEndpoint.ExteriorHaar

open scoped BigOperators
open Matrix QuantumProver.WernerEndpoint.SlaterMoments

theorem orderedExterior_trace {I : Type*} [Fintype I] (P : Matrix I I ℂ) :
    Matrix.trace (ExteriorSupport.orderedExterior P) =
      ((Matrix.trace P) ^ 2 - Matrix.trace (P * P)) / 2 := by
  simp only [Matrix.trace, Matrix.diag, ExteriorSupport.orderedExterior,
    Fintype.sum_prod_type, Matrix.mul_apply]
  simp_rw [← Finset.sum_div, Finset.sum_sub_distrib]
  rw [ExteriorSupport.sum_separated_complex]
  ring

theorem fourSupportProjector_trace {d : ℕ} (S : FourSet d) :
    Matrix.trace (ActualContractionLower.fourSupportProjector S) = 6 := by
  have ht (P : Matrix (Edge d) (Edge d) ℝ) :
      Matrix.trace (RealSymmetricFactor.complexify P) = ((Matrix.trace P : ℝ) : ℂ) := by
    simp [RealSymmetricFactor.complexify, Matrix.trace, Matrix.diag]
  unfold ActualContractionLower.fourSupportProjector
  rw [ht]
  norm_num [D5SupportFactor.fourSupportMatrix, Matrix.trace_add,
    Matrix.trace_single_eq_same]

theorem exterior_fourSupportProjector_trace {d : ℕ} (S : FourSet d) :
    Matrix.trace (ExteriorSupport.orderedExterior
      (ActualContractionLower.fourSupportProjector S)) = 15 := by
  rw [orderedExterior_trace, ActualContractionLower.fourSupportProjector_idempotent,
    fourSupportProjector_trace]
  norm_num

def replicaAlt {d : ℕ} (u v : Edge d → ℂ) : Edge d × Edge d → ℂ :=
  replicaProduct u v - replicaProduct v u

theorem replicaAlt_swap {d : ℕ} (u v : Edge d → ℂ) :
    replicaAlt v u = -replicaAlt u v := by
  ext ef
  simp only [replicaAlt, Pi.sub_apply, Pi.neg_apply]
  ring

theorem replicaAlt_neg_left {d : ℕ} (u v : Edge d → ℂ) :
    replicaAlt (-u) v = -replicaAlt u v := by
  ext ef
  simp only [replicaAlt, replicaProduct, Pi.sub_apply, Pi.neg_apply]
  ring

theorem replicaAlt_neg_right {d : ℕ} (u v : Edge d → ℂ) :
    replicaAlt u (-v) = -replicaAlt u v := by
  ext ef
  simp only [replicaAlt, replicaProduct, Pi.sub_apply, Pi.neg_apply]
  ring

theorem replicaAlt_expansion {d : ℕ} (u v w z : Edge d → ℂ) (c s : ℂ) :
    replicaAlt (c • u + s • v) (c • w + s • z) =
      c ^ 2 • replicaAlt u w + (c * s) • (replicaAlt u z + replicaAlt v w) +
        s ^ 2 • replicaAlt v z := by
  ext ef
  simp only [replicaAlt, replicaProduct, Pi.sub_apply, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul]
  ring

theorem wedgeSquareAction_replicaAlt {d : ℕ} (V : PhysicalUnitary d)
    (u v : Edge d → ℂ) :
    (wedgeSquareAction V).mulVec (replicaAlt u v) =
      replicaAlt ((wedgeAction V).mulVec u) ((wedgeAction V).mulVec v) := by
  unfold replicaAlt
  rw [Matrix.mulVec_sub, wedgeSquareAction_replicaProduct,
    wedgeSquareAction_replicaProduct]

theorem common_rotation_mixed_mem {d : ℕ}
    (S : Submodule ℂ (Edge d × Edge d → ℂ))
    (hcommon : ∀ a b c : Fin d,
      replicaAlt (orderedWedge a b) (orderedWedge a c) ∈ S)
    (hrot : ∀ (V : PhysicalUnitary d) (v : Edge d × Edge d → ℂ),
      v ∈ S → (wedgeSquareAction V).mulVec v ∈ S)
    (a b c f : Fin d) (haf : a ≠ f) (hba : b ≠ a) (hbf : b ≠ f)
    (hca : c ≠ a) (hcf : c ≠ f) :
    replicaAlt (orderedWedge a b) (orderedWedge f c) +
      replicaAlt (orderedWedge f b) (orderedWedge a c) ∈ S := by
  have h := hrot (physicalPlaneRotation a f haf)
    (replicaAlt (orderedWedge a b) (orderedWedge a c)) (hcommon a b c)
  rw [wedgeSquareAction_replicaAlt,
    physicalPlaneRotation_wedge_first a f haf b hba hbf,
    physicalPlaneRotation_wedge_first a f haf c hca hcf,
    replicaAlt_expansion] at h
  have h' : (3 / 5 : ℂ) ^ 2 • replicaAlt (orderedWedge a b) (orderedWedge a c) +
      (4 / 5 : ℂ) ^ 2 • replicaAlt (orderedWedge f b) (orderedWedge f c) +
      ((3 / 5 : ℂ) * (4 / 5 : ℂ)) •
        (replicaAlt (orderedWedge a b) (orderedWedge f c) +
          replicaAlt (orderedWedge f b) (orderedWedge a c)) ∈ S := by
    convert h using 1 <;> abel
  exact submodule_extract_scaled_sum S (hcommon a b c) (hcommon f b c) h' (by norm_num)

theorem disjoint_replicaAlt_mem {d : ℕ}
    (S : Submodule ℂ (Edge d × Edge d → ℂ))
    (hcommon : ∀ a b c : Fin d,
      replicaAlt (orderedWedge a b) (orderedWedge a c) ∈ S)
    (hrot : ∀ (V : PhysicalUnitary d) (v : Edge d × Edge d → ℂ),
      v ∈ S → (wedgeSquareAction V).mulVec v ∈ S)
    (a b c f : Fin d) (hab : a ≠ b) (hac : a ≠ c) (haf : a ≠ f)
    (hbc : b ≠ c) (hbf : b ≠ f) (hcf : c ≠ f) :
    replicaAlt (orderedWedge a b) (orderedWedge c f) ∈ S := by
  let X := replicaAlt (orderedWedge a b) (orderedWedge c f)
  let Y := replicaAlt (orderedWedge a c) (orderedWedge b f)
  let Z := replicaAlt (orderedWedge a f) (orderedWedge b c)
  have h1 : -X + Y ∈ S := by
    have h := common_rotation_mixed_mem S hcommon hrot a b c f haf hab.symm hbf hac.symm hcf
    rw [orderedWedge_swap c f, orderedWedge_swap b f,
      replicaAlt_neg_right, replicaAlt_neg_left,
      replicaAlt_swap (orderedWedge a c) (orderedWedge b f)] at h
    simpa only [neg_neg] using h
  have h2 : X + Z ∈ S := by
    have h := common_rotation_mixed_mem S hcommon hrot a b f c hac hab.symm hbc haf.symm hcf.symm
    rw [orderedWedge_swap b c, replicaAlt_neg_left,
      replicaAlt_swap (orderedWedge a f) (orderedWedge b c)] at h
    simpa only [neg_neg] using h
  have h3 : Y - Z ∈ S := by
    have h := common_rotation_mixed_mem S hcommon hrot a c f b hab hac.symm hbc.symm haf.symm hbf.symm
    rw [replicaAlt_swap (orderedWedge a f) (orderedWedge b c)] at h
    simpa only [sub_eq_add_neg] using h
  have h := S.smul_mem (1 / 2 : ℂ) (S.sub_mem (S.add_mem h2 h3) h1)
  convert h using 1
  ext ef
  simp only [X, Y, Z, Pi.smul_apply, Pi.add_apply, Pi.sub_apply, Pi.neg_apply,
    smul_eq_mul]
  ring

theorem ordered_replicaAlt_mem {d : ℕ}
    (S : Submodule ℂ (Edge d × Edge d → ℂ))
    (hcommon : ∀ a b c : Fin d,
      replicaAlt (orderedWedge a b) (orderedWedge a c) ∈ S)
    (hrot : ∀ (V : PhysicalUnitary d) (v : Edge d × Edge d → ℂ),
      v ∈ S → (wedgeSquareAction V).mulVec v ∈ S)
    (a b c f : Fin d) (hab : a ≠ b) (hcf : c ≠ f) :
    replicaAlt (orderedWedge a b) (orderedWedge c f) ∈ S := by
  by_cases hac : a = c
  · subst c
    exact hcommon a b f
  by_cases haf : a = f
  · subst f
    rw [orderedWedge_swap a c, replicaAlt_neg_right]
    exact S.neg_mem (hcommon a b c)
  by_cases hbc : b = c
  · subst c
    rw [orderedWedge_swap b a, replicaAlt_neg_left]
    exact S.neg_mem (hcommon b a f)
  by_cases hbf : b = f
  · subst f
    rw [orderedWedge_swap b a, orderedWedge_swap b c,
      replicaAlt_neg_left, replicaAlt_neg_right, neg_neg]
    exact hcommon b a c
  exact disjoint_replicaAlt_mem S hcommon hrot a b c f hab hac haf hbc hbf hcf

theorem basis_replicaAlt_mem {d : ℕ}
    (S : Submodule ℂ (Edge d × Edge d → ℂ))
    (hcommon : ∀ a b c : Fin d,
      replicaAlt (orderedWedge a b) (orderedWedge a c) ∈ S)
    (hrot : ∀ (V : PhysicalUnitary d) (v : Edge d × Edge d → ℂ),
      v ∈ S → (wedgeSquareAction V).mulVec v ∈ S)
    (e f : Edge d) : replicaAlt (Pi.single e 1) (Pi.single f 1) ∈ S := by
  rw [← orderedWedge_edge e, ← orderedWedge_edge f]
  exact ordered_replicaAlt_mem S hcommon hrot e.val.1 e.val.2 f.val.1 f.val.2
    (ne_of_lt e.property) (ne_of_lt f.property)

theorem skew_mem_of_common_and_rotations {d : ℕ}
    (S : Submodule ℂ (Edge d × Edge d → ℂ))
    (hcommon : ∀ a b c : Fin d,
      replicaAlt (orderedWedge a b) (orderedWedge a c) ∈ S)
    (hrot : ∀ (V : PhysicalUnitary d) (v : Edge d × Edge d → ℂ),
      v ∈ S → (wedgeSquareAction V).mulVec v ∈ S)
    (v : Edge d × Edge d → ℂ) (hv : ∀ e f, v (f, e) = -v (e, f)) : v ∈ S := by
  classical
  have ha (e f : Edge d) : replicaAlt (Pi.single e 1) (Pi.single f 1) =
      Pi.single (e, f) 1 - Pi.single (f, e) 1 := by
    unfold replicaAlt
    rw [replicaProduct_basis, replicaProduct_basis]
  have he : (∑ e : Edge d, ∑ f : Edge d,
      (v (e, f) / 2) • replicaAlt (Pi.single e 1) (Pi.single f 1)) = v := by
    ext ⟨e, f⟩
    have hs (a b : Edge d) (g : Edge d → Edge d → ℂ) :
        (∑ x : Edge d, ∑ y : Edge d,
          if a = x ∧ b = y then g x y else 0) = g a b := by
      have hi (x y : Edge d) : (if a = x ∧ b = y then g x y else 0) =
          (if x = a then (if y = b then g x y else 0) else 0) := by
        by_cases hxa : x = a <;> by_cases hyb : y = b
        · subst x; subst y; simp
        · subst x; simp [hyb, Ne.symm hyb]
        · subst y; simp [hxa, Ne.symm hxa]
        · simp [hxa, Ne.symm hxa, hyb, Ne.symm hyb]
      simp_rw [hi]
      simp
    have ht : (∑ x : Edge d, ∑ y : Edge d,
        if e = y ∧ f = x then v (x, y) / 2 else 0) = v (f, e) / 2 := by
      rw [Finset.sum_comm]
      exact hs e f (fun y x => v (x, y) / 2)
    simp only [ha, Finset.sum_apply, Pi.smul_apply, Pi.sub_apply,
      smul_eq_mul, mul_sub, Pi.single_apply, Prod.mk.injEq,
      mul_ite, mul_one, mul_zero, Finset.sum_sub_distrib]
    rw [hs e f (fun x y => v (x, y) / 2), ht, hv e f]
    ring
  rw [← he]
  apply S.sum_mem
  intro e _
  apply S.sum_mem
  intro f _
  exact S.smul_mem _ (basis_replicaAlt_mem S hcommon hrot e f)

end QuantumProver.WernerEndpoint.ExteriorHaar

namespace QuantumProver.WernerEndpoint.ExteriorHaar

open Matrix QuantumProver.WernerEndpoint.SlaterMoments
open scoped BigOperators

theorem exteriorHaarEigenspace_common (d : ℕ) (hd : 3 ≤ d) (a b c : Fin d) :
    replicaAlt (orderedWedge a b) (orderedWedge a c) ∈ exteriorHaarEigenspace d hd := by
  by_cases hab : a = b
  · subst b
    simp [replicaAlt, orderedWedge_self, replicaProduct]
  by_cases hac : a = c
  · subst c
    simp [replicaAlt, orderedWedge_self, replicaProduct]
  by_cases hbc : b = c
  · subst c
    simp [replicaAlt]
  have hw₁ : orderedWedge (canonicalTripleEmbedding hd 0) (canonicalTripleEmbedding hd 1) =
      Pi.single (firstCommonEdge d hd) 1 := orderedWedge_edge (firstCommonEdge d hd)
  have hw₂ : orderedWedge (canonicalTripleEmbedding hd 0) (canonicalTripleEmbedding hd 2) =
      Pi.single (secondCommonEdge d hd) 1 := orderedWedge_edge (secondCommonEdge d hd)
  have hbase :
      replicaProduct
          (orderedWedge (canonicalTripleEmbedding hd 0) (canonicalTripleEmbedding hd 1))
          (orderedWedge (canonicalTripleEmbedding hd 0) (canonicalTripleEmbedding hd 2)) -
        replicaProduct
          (orderedWedge (canonicalTripleEmbedding hd 0) (canonicalTripleEmbedding hd 2))
          (orderedWedge (canonicalTripleEmbedding hd 0) (canonicalTripleEmbedding hd 1)) ∈
        exteriorHaarEigenspace d hd := by
    rw [hw₁, hw₂, replicaProduct_basis, replicaProduct_basis]
    exact exteriorHaarEigenspace_first_common d hd
  obtain ⟨V, _, hV⟩ := exists_physicalUnitary_distinct_triple hd a b c hab hac hbc
  have h := exteriorHaarEigenspace_rotated d hd V _ hbase
  rw [hV] at h
  exact h

theorem exteriorHaarEigenspace_all_skew (d : ℕ) (hd : 3 ≤ d)
    (v : Edge d × Edge d → ℂ) (hv : ∀ e f, v (f, e) = -v (e, f)) :
    v ∈ exteriorHaarEigenspace d hd :=
  skew_mem_of_common_and_rotations (exteriorHaarEigenspace d hd)
    (exteriorHaarEigenspace_common d hd)
    (fun V w hw => exteriorHaarEigenspace_rotated d hd V w hw) v hv

theorem exteriorSupportHaar_eq_scalar_projector (d : ℕ) (hd : 3 ≤ d) :
    exteriorSupportHaar d = exteriorHaarScalar d hd •
      ExteriorSupport.orderedExterior (1 : Matrix (Edge d) (Edge d) ℂ) := by
  classical
  ext ef gh
  let P := ExteriorSupport.orderedExterior (1 : Matrix (Edge d) (Edge d) ℂ)
  let v := P.mulVec (Pi.single gh 1)
  have hv : ∀ e f, v (f, e) = -v (e, f) := by
    intro e f
    dsimp [v, P]
    rw [orderedExterior_identity_mulVec, orderedExterior_identity_mulVec]
    ring
  have h := (exteriorHaarEigenspace_mem d hd v).mp
    (exteriorHaarEigenspace_all_skew d hd v hv)
  change (exteriorSupportHaar d).mulVec (P.mulVec (Pi.single gh 1)) =
    exteriorHaarScalar d hd • P.mulVec (Pi.single gh 1) at h
  rw [Matrix.mulVec_mulVec, exteriorSupportHaar_right_projector] at h
  have hh := congrArg (fun w : Edge d × Edge d → ℂ => w ef) h
  simpa only [Matrix.mulVec_single_one, Matrix.col, Matrix.transpose_apply, Pi.smul_apply,
    smul_eq_mul, Matrix.smul_apply, P] using hh

theorem orderedExterior_identity_trace_ne_zero (d : ℕ) (hd : 3 ≤ d) :
    Matrix.trace (ExteriorSupport.orderedExterior (1 : Matrix (Edge d) (Edge d) ℂ)) ≠ 0 := by
  classical
  let f : Fin 2 → Edge d := ![firstCommonEdge d hd, secondCommonEdge d hd]
  have hf : Function.Injective f := by
    intro i j hij
    have he := commonEdges_ne d hd
    fin_cases i <;> fin_cases j <;> simp_all [f]
  have hcard : 2 ≤ Fintype.card (Edge d) := by
    simpa using Fintype.card_le_of_injective f hf
  have hzero : (Fintype.card (Edge d) : ℂ) ≠ 0 := by
    exact_mod_cast (by omega : Fintype.card (Edge d) ≠ 0)
  have hone : (Fintype.card (Edge d) : ℂ) - 1 ≠ 0 := by
    intro h
    have hc : (Fintype.card (Edge d) : ℂ) = 1 := sub_eq_zero.mp h
    have hn : Fintype.card (Edge d) = 1 := by exact_mod_cast hc
    omega
  rw [orderedExterior_identity_trace]
  have he : (Fintype.card (Edge d) : ℂ) ^ 2 - Fintype.card (Edge d) =
      (Fintype.card (Edge d) : ℂ) * ((Fintype.card (Edge d) : ℂ) - 1) := by ring
  rw [he]
  exact div_ne_zero (mul_ne_zero hzero hone) (by norm_num)

theorem exteriorSupportHaar_eq (d : ℕ) (hd : 4 ≤ d) :
    exteriorSupportHaar d = (5 * ((d : ℂ) - 3) / ((d : ℂ) + 1)) •
      ExteriorSupport.orderedExterior (1 : Matrix (Edge d) (Edge d) ℂ) := by
  have hd₃ : 3 ≤ d := by omega
  have ht := congrArg Matrix.trace (exteriorSupportHaar_eq_scalar_projector d hd₃)
  rw [exteriorSupportHaar_trace_ratio d hd, Matrix.trace_smul] at ht
  have ht' : exteriorHaarScalar d hd₃ *
      Matrix.trace (ExteriorSupport.orderedExterior (1 : Matrix (Edge d) (Edge d) ℂ)) =
      (5 * ((d : ℂ) - 3) / ((d : ℂ) + 1)) *
      Matrix.trace (ExteriorSupport.orderedExterior (1 : Matrix (Edge d) (Edge d) ℂ)) := by
    simpa only [smul_eq_mul] using ht.symm
  have hz : (exteriorHaarScalar d hd₃ - (5 * ((d : ℂ) - 3) / ((d : ℂ) + 1))) *
      Matrix.trace (ExteriorSupport.orderedExterior (1 : Matrix (Edge d) (Edge d) ℂ)) = 0 := by
    linear_combination ht'
  have hs := sub_eq_zero.mp
    ((mul_eq_zero.mp hz).resolve_right (orderedExterior_identity_trace_ne_zero d hd₃))
  rw [exteriorSupportHaar_eq_scalar_projector d hd₃, hs]

end QuantumProver.WernerEndpoint.ExteriorHaar

namespace QuantumProver.WernerEndpoint.ExteriorHaar

open Matrix MeasureTheory QuantumProver.WernerEndpoint.SlaterMoments
open scoped BigOperators Kronecker

theorem orderedExterior_square_kronecker {I : Type*} [Fintype I] [DecidableEq I]
    (R : Matrix I I ℂ) :
    ExteriorSupport.orderedExterior R = (R ⊗ₖ R) *
      ExteriorSupport.orderedExterior (1 : Matrix I I ℂ) := by
  rw [orderedExterior_identity_eq, Matrix.mul_smul, Matrix.mul_sub, Matrix.mul_one]
  ext ⟨i, j⟩ ⟨a, b⟩
  simp only [Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
  rw [mul_replicaSwap_entry_matrix]
  simp only [ExteriorSupport.orderedExterior, Matrix.kroneckerMap_apply,
    Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
  ring

theorem orderedExterior_left_projector {I O : Type*} [Fintype I] [Fintype O]
    [DecidableEq O] (T : Matrix O I ℂ) :
    ExteriorSupport.orderedExterior (1 : Matrix O O ℂ) *
      ExteriorSupport.orderedExterior T = ExteriorSupport.orderedExterior T := by
  rw [← ExteriorSupport.orderedExterior_mul, Matrix.one_mul]

theorem orderedExterior_right_projector {I O : Type*} [Fintype I] [Fintype O]
    [DecidableEq I] (T : Matrix O I ℂ) :
    ExteriorSupport.orderedExterior T * ExteriorSupport.orderedExterior (1 : Matrix I I ℂ) =
      ExteriorSupport.orderedExterior T := by
  rw [← ExteriorSupport.orderedExterior_mul, Matrix.mul_one]

theorem orderedExterior_conjugate_square {I : Type*} [Fintype I] [DecidableEq I]
    (R P : Matrix I I ℂ) :
    ExteriorSupport.orderedExterior (R * P * R.conjTranspose) =
      (R ⊗ₖ R) * ExteriorSupport.orderedExterior P * (R ⊗ₖ R).conjTranspose := by
  let E₀ := ExteriorSupport.orderedExterior (1 : Matrix I I ℂ)
  have hE : E₀.conjTranspose = E₀ := by
    rw [← ExteriorSchatten.orderedExterior_conjTranspose, Matrix.conjTranspose_one]
  rw [ExteriorSupport.orderedExterior_mul, ExteriorSupport.orderedExterior_mul,
    ExteriorSchatten.orderedExterior_conjTranspose, orderedExterior_square_kronecker R,
    Matrix.conjTranspose_mul]
  change ((R ⊗ₖ R) * E₀ * ExteriorSupport.orderedExterior P) *
    (E₀.conjTranspose * (R ⊗ₖ R).conjTranspose) = _
  rw [hE]
  calc
    _ = (R ⊗ₖ R) *
        (E₀ * ExteriorSupport.orderedExterior P * E₀) * (R ⊗ₖ R).conjTranspose := by
      simp only [Matrix.mul_assoc]
    _ = _ := by rw [orderedExterior_left_projector, orderedExterior_right_projector]

theorem hsNormSq_mul_gram_matrix {I J O : Type*} [Fintype I] [Fintype J] [Fintype O]
    (T : Matrix O I ℂ) (W : Matrix I J ℂ) :
    hsNormSq (T * W) = (Matrix.trace (T * (W * W.conjTranspose) * T.conjTranspose)).re := by
  rw [hsNormSq_eq_trace, Matrix.conjTranspose_mul]
  congr 1
  congr 1
  simp only [Matrix.mul_assoc]

theorem supportTraceHaar_integral_exact {d : ℕ} (hd : 4 ≤ d) {O : Type*} [Fintype O]
    (T : Matrix O (Edge d × Edge d) ℂ) :
    (∫ U : PhysicalUnitary d,
      (Matrix.trace (T * exteriorSupportOrbit U * T.conjTranspose)).re ∂normalizedHaar d) =
      (5 * ((d : ℝ) - 3) / ((d : ℝ) + 1)) *
        hsNormSq (T * ExteriorSupport.orderedExterior (1 : Matrix (Edge d) (Edge d) ℂ)) := by
  let P := ExteriorSupport.orderedExterior (1 : Matrix (Edge d) (Edge d) ℂ)
  have hP : P.conjTranspose = P := by
    rw [← ExteriorSchatten.orderedExterior_conjTranspose, Matrix.conjTranspose_one]
  have hi : P * P = P := by
    rw [← ExteriorSupport.orderedExterior_mul, Matrix.one_mul]
  have hc : (((5 * ((d : ℝ) - 3) / ((d : ℝ) + 1)) : ℝ) : ℂ) =
      5 * ((d : ℂ) - 3) / ((d : ℂ) + 1) := by push_cast; rfl
  rw [supportTraceHaar_integral_re, exteriorSupportHaar_eq d hd]
  rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul]
  change ((5 * ((d : ℂ) - 3) / ((d : ℂ) + 1)) *
    Matrix.trace (T * P * T.conjTranspose)).re = _
  rw [← hc, Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [hsNormSq_mul_projection_matrix T P hP hi]

theorem rotated_fourSupport_hs_trace {d : ℕ} {Y : Type*} [Fintype Y]
    (A : Matrix Y (Edge d) ℂ) (U : PhysicalUnitary d) (S : FourSet d) :
    hsNormSq (ExteriorSupport.orderedExterior
      (A * wedgeAction U * ActualContractionLower.fourSupportProjector S)) =
      (Matrix.trace (ExteriorSupport.orderedExterior A *
        (wedgeSquareAction U * ExteriorSupport.orderedExterior
          (ActualContractionLower.fourSupportProjector S) * (wedgeSquareAction U).conjTranspose) *
        (ExteriorSupport.orderedExterior A).conjTranspose)).re := by
  let R := wedgeAction U
  let P := ActualContractionLower.fourSupportProjector S
  have hg : ExteriorSupport.orderedExterior (R * P) *
      (ExteriorSupport.orderedExterior (R * P)).conjTranspose =
      ExteriorSupport.orderedExterior (R * P * R.conjTranspose) := by
    rw [← ExteriorSchatten.orderedExterior_conjTranspose,
      ← ExteriorSupport.orderedExterior_mul, Matrix.conjTranspose_mul,
      ActualContractionLower.fourSupportProjector_hermitian]
    congr 1
    calc
      _ = R * (P * P) * R.conjTranspose := by simp only [Matrix.mul_assoc, P]
      _ = _ := by rw [ActualContractionLower.fourSupportProjector_idempotent]
  have ht : ExteriorSupport.orderedExterior (A * R * P) =
      ExteriorSupport.orderedExterior A * ExteriorSupport.orderedExterior (R * P) := by
    rw [Matrix.mul_assoc, ExteriorSupport.orderedExterior_mul]
  change hsNormSq (ExteriorSupport.orderedExterior (A * R * P)) = _
  rw [ht, hsNormSq_mul_gram_matrix, hg, orderedExterior_conjugate_square]
  rfl

theorem rotated_fourSupport_sum_trace {d : ℕ} {Y : Type*} [Fintype Y]
    (A : Matrix Y (Edge d) ℂ) (U : PhysicalUnitary d) :
    (∑ S : FourSet d, hsNormSq (ExteriorSupport.orderedExterior
      (A * wedgeAction U * ActualContractionLower.fourSupportProjector S))) =
      (Matrix.trace (ExteriorSupport.orderedExterior A * exteriorSupportOrbit U *
        (ExteriorSupport.orderedExterior A).conjTranspose)).re := by
  simp_rw [rotated_fourSupport_hs_trace]
  simp only [exteriorSupportOrbit, literalExteriorSupportSum,
    ActualContractionLower.fourSupportProjector, Matrix.mul_sum, Matrix.sum_mul,
    Matrix.trace_sum, Complex.re_sum, Matrix.mul_assoc]

theorem actual_fourSupport_sum_haar_hs {d : ℕ} (hd : 4 ≤ d)
    {Y : Type*} [Fintype Y] (A : Matrix Y (Edge d) ℂ) :
    (∫ U : PhysicalUnitary d,
      (∑ S : FourSet d, hsNormSq (ExteriorSupport.orderedExterior
        (A * wedgeAction U * ActualContractionLower.fourSupportProjector S)))
      ∂normalizedHaar d) =
      (5 * ((d : ℝ) - 3) / ((d : ℝ) + 1)) * hsNormSq (ExteriorSupport.orderedExterior A) := by
  simp_rw [rotated_fourSupport_sum_trace]
  rw [supportTraceHaar_integral_exact hd, orderedExterior_right_projector]

end QuantumProver.WernerEndpoint.ExteriorHaar

namespace QuantumProver.WernerEndpoint.ExteriorHaar

open Matrix MeasureTheory QuantumProver.WernerEndpoint.SlaterMoments
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

def actualFourCorrection {d : ℕ} {Y B E : Type*}
    [Fintype Y] [Fintype B] [Fintype E] [DecidableEq Y]
    (N : Stinespring Y B E) (A : Matrix Y (Edge d) ℂ) (S : FourSet d) : ℂ :=
  let z : Y × Y → ℂ := fun ij => (A * fourFormMatrix S * A.transpose) ij.1 ij.2
  dotProduct (star z) (N.replicaKernel.mulVec z)

def actualFourCorrectionSum {d : ℕ} {Y B E : Type*}
    [Fintype Y] [Fintype B] [Fintype E] [DecidableEq Y]
    (N : Stinespring Y B E) (A : Matrix Y (Edge d) ℂ) : ℝ :=
  ∑ S : FourSet d, (actualFourCorrection N A S).re

theorem kronecker_mulVec_coefficients_matrix {X Y : Type*} [Fintype X]
    (A : Matrix Y X ℂ) (D : Matrix X X ℂ) :
    (A ⊗ₖ A).mulVec (fun ij : X × X => D ij.1 ij.2) =
      (fun uv : Y × Y => (A * D * A.transpose) uv.1 uv.2) := by
  ext ⟨u, v⟩
  simp only [Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.kroneckerMap_apply, Fintype.sum_prod_type, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem actualFourCorrection_trace {d : ℕ} {Y B E : Type*}
    [Fintype Y] [Fintype B] [Fintype E] [DecidableEq Y]
    (N : Stinespring Y B E) (A : Matrix Y (Edge d) ℂ) (S : FourSet d) :
    Matrix.trace (N.replicaKernel * (A ⊗ₖ A) * pureDensity (fourFormOmega S) *
      (A ⊗ₖ A).conjTranspose) = actualFourCorrection N A S := by
  rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (A ⊗ₖ A)]
  have hs := sandwich_crossDensity (A ⊗ₖ A) (fourFormOmega S) (fourFormOmega S)
  change (A ⊗ₖ A) * pureDensity (fourFormOmega S) * (A ⊗ₖ A).conjTranspose = _ at hs
  rw [hs]
  change Matrix.trace (N.replicaKernel *
    pureDensity ((A ⊗ₖ A).mulVec (fourFormOmega S))) = actualFourCorrection N A S
  rw [trace_mul_pureDensity]
  have hv : fourFormOmega S = (fun ij : Edge d × Edge d => fourFormMatrix S ij.1 ij.2) := rfl
  rw [hv, kronecker_mulVec_coefficients_matrix]
  rfl

theorem fourForm_density_sum_projector (d : ℕ) (hd : 2 ≤ d) :
    (∑ S : FourSet d, pureDensity (fourFormOmega S)) =
      (6 : ℂ) • exteriorReplicaProjector d := by
  rw [exteriorReplicaProjector_eq_coordinateFourProjector d hd, coordinateFourProjector]
  rw [smul_smul]
  norm_num

theorem actualFourCorrectionSum_trace {d : ℕ} (hd : 2 ≤ d) {Y B E : Type*}
    [Fintype Y] [Fintype B] [Fintype E] [DecidableEq Y]
    (N : Stinespring Y B E) (A : Matrix Y (Edge d) ℂ) :
    actualFourCorrectionSum N A =
      (6 * Matrix.trace (N.replicaKernel * (A ⊗ₖ A) * exteriorReplicaProjector d *
        (A ⊗ₖ A).conjTranspose)).re := by
  have ht : (∑ S : FourSet d, actualFourCorrection N A S) =
      6 * Matrix.trace (N.replicaKernel * (A ⊗ₖ A) * exteriorReplicaProjector d *
        (A ⊗ₖ A).conjTranspose) := by
    simp_rw [← actualFourCorrection_trace]
    rw [← Matrix.trace_sum]
    rw [← Matrix.sum_mul, ← Matrix.mul_sum, fourForm_density_sum_projector d hd]
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
  rw [actualFourCorrectionSum, ← Complex.re_sum, ht]

theorem actualFourCorrectionSum_physical_invariant {d : ℕ} (hd : 2 ≤ d) {Y B E : Type*}
    [Fintype Y] [Fintype B] [Fintype E] [DecidableEq Y]
    (N : Stinespring Y B E) (A : Matrix Y (Edge d) ℂ) (U : PhysicalUnitary d) :
    actualFourCorrectionSum N (A * wedgeAction U) = actualFourCorrectionSum N A := by
  rw [actualFourCorrectionSum_trace hd, actualFourCorrectionSum_trace hd]
  have hf : ((A * wedgeAction U) ⊗ₖ (A * wedgeAction U)) =
      (A ⊗ₖ A) * wedgeSquareAction U := by
    simp only [wedgeSquareAction, Matrix.mul_kronecker_mul]
  rw [hf, Matrix.conjTranspose_mul]
  have hm : N.replicaKernel * ((A ⊗ₖ A) * wedgeSquareAction U) *
      exteriorReplicaProjector d *
      ((wedgeSquareAction U).conjTranspose * (A ⊗ₖ A).conjTranspose) =
      N.replicaKernel * (A ⊗ₖ A) *
        (wedgeSquareAction U * exteriorReplicaProjector d * (wedgeSquareAction U).conjTranspose) *
        (A ⊗ₖ A).conjTranspose := by simp only [Matrix.mul_assoc]
  rw [hm, exteriorReplicaProjector_wedgeSquareAction_covariance d hd U]

theorem normalized_companion_bound_nonneg {Y B E : Type*}
    [Fintype Y] [Fintype B] [Fintype E] [DecidableEq Y] [Nonempty Y]
    (N : Stinespring Y B E) (β : ℝ)
    (hbound : ∀ w : Y → ℂ, vectorNormSq w = 1 → purity (N.apply (pureDensity w)) ≤ β) :
    0 ≤ β := by
  classical
  let y : Y := Classical.choice inferInstance
  have hv : vectorNormSq (Pi.single y (1 : ℂ)) = 1 := by
    simp [vectorNormSq, Pi.single_apply]
  have hp := N.apply_posSemidef (pureDensity (Pi.single y (1 : ℂ)))
    (pureDensity_posSemidef _)
  exact (purity_nonneg_of_hermitian _ hp.isHermitian.eq).trans (hbound _ hv)

theorem actualFourCorrectionSum_rotated_lower {d : ℕ} (hd : 4 ≤ d) {Y B E : Type*}
    [Fintype Y] [Fintype B] [Fintype E] [DecidableEq Y]
    (N : Stinespring Y B E) (β : ℝ) (hβ : 0 ≤ β)
    (hbound : ∀ w : Y → ℂ, vectorNormSq w = 1 → purity (N.apply (pureDensity w)) ≤ β)
    (A : Matrix Y (Edge d) ℂ) (U : PhysicalUnitary d) :
    -(4 * β / 5) *
      (∑ S : FourSet d, hsNormSq (ExteriorSupport.orderedExterior
        (A * wedgeAction U * ActualContractionLower.fourSupportProjector S))) ≤
      actualFourCorrectionSum N A := by
  rw [← actualFourCorrectionSum_physical_invariant (by omega : 2 ≤ d) N A U]
  rw [actualFourCorrectionSum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro S _
  have hn := ActualContractionLower.actual_fourForm_exterior_nuclear_support_bound
    (A * wedgeAction U) S
  have hl := ActualContractionLower.actual_fourForm_replica_retained_lower
    N β hbound (A * wedgeAction U) S
  have hcoef : -(4 * β / 5) ≤ 0 :=
    neg_nonpos.mpr (div_nonneg (mul_nonneg (by norm_num) hβ) (by norm_num))
  exact (mul_le_mul_of_nonpos_left hn hcoef).trans hl

theorem actual_fourSupport_sum_haar_integrable {d : ℕ} {Y : Type*} [Fintype Y]
    (A : Matrix Y (Edge d) ℂ) :
    Integrable (fun U : PhysicalUnitary d =>
      ∑ S : FourSet d, hsNormSq (ExteriorSupport.orderedExterior
        (A * wedgeAction U * ActualContractionLower.fourSupportProjector S))) (normalizedHaar d) := by
  simp_rw [rotated_fourSupport_sum_trace]
  exact Complex.reCLM.integrable_comp (supportTraceHaar_integrable (ExteriorSupport.orderedExterior A))

theorem actual_fourForm_sum_haar_lower {d : ℕ} (hd : 4 ≤ d) {Y B E : Type*}
    [Fintype Y] [Fintype B] [Fintype E] [DecidableEq Y]
    (N : Stinespring Y B E) (β : ℝ)
    (hbound : ∀ w : Y → ℂ, vectorNormSq w = 1 → purity (N.apply (pureDensity w)) ≤ β)
    (A : Matrix Y (Edge d) ℂ) (hA : hsNormSq A = 1) :
    -2 * β * (((d : ℝ) - 3) / ((d : ℝ) + 1)) * (1 - purity (reducedLeft A)) ≤
      ∑ S : FourSet d,
        (dotProduct (star (fun ij : Y × Y => (A * fourFormMatrix S * A.transpose) ij.1 ij.2))
          (N.replicaKernel.mulVec
            (fun ij : Y × Y => (A * fourFormMatrix S * A.transpose) ij.1 ij.2))).re := by
  classical
  have hY : Nonempty Y := by
    by_contra hn
    letI : IsEmpty Y := not_nonempty_iff.mp hn
    have hz : hsNormSq A = 0 := by simp [hsNormSq]
    rw [hz] at hA
    norm_num at hA
  letI : Nonempty Y := hY
  have hβ := normalized_companion_bound_nonneg N β hbound
  have hi := (actual_fourSupport_sum_haar_integrable A).const_mul (-(4 * β / 5))
  have hc : (∫ _U : PhysicalUnitary d, actualFourCorrectionSum N A ∂normalizedHaar d) =
      actualFourCorrectionSum N A := by simp [normalizedHaar_univ]
  have h := integral_mono hi (integrable_const (actualFourCorrectionSum N A))
    (fun U => actualFourCorrectionSum_rotated_lower hd N β hβ hbound A U)
  rw [integral_const_mul, actual_fourSupport_sum_haar_hs hd A, hc,
    ExteriorSupport.orderedExterior_hsNormSq_of_normalized A hA] at h
  change _ ≤ actualFourCorrectionSum N A
  convert h using 1 <;> ring

end QuantumProver.WernerEndpoint.ExteriorHaar

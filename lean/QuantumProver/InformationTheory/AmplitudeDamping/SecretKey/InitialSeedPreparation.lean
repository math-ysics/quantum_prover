import QuantumProver.InformationTheory.AmplitudeDamping.SecretKey.SeedResourceCharge
import QuantumProver.InformationTheory.AmplitudeDamping.SecretKey.LaneHistoryTransport
import QuantumProver.InformationTheory.AmplitudeDamping.QuantumCapacity.ParallelLanes

set_option autoImplicit false

noncomputable section

open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix Kronecker

namespace QuantumProver.AmplitudeDamping.SecretKey.InitialSeed

variable {I O : Type*} [Fintype I] [Fintype O] [DecidableEq I] [DecidableEq O]

def isometryHom (V : Matrix O I ℂ) (hV : Vᴴ * V = 1) :
    Matrix I I ℂ →⋆ₙₐ[ℝ] Matrix O O ℂ where
  toFun X := V * X * Vᴴ
  map_zero' := by simp
  map_add' X Y := by simp [Matrix.mul_add, Matrix.add_mul]
  map_smul' r X := by simp [Matrix.mul_smul, Matrix.smul_mul]
  map_mul' X Y := by
    calc
      V * (X * Y) * Vᴴ = V * X * (Vᴴ * V) * Y * Vᴴ := by
        rw [hV]
        simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = (V * X * Vᴴ) * (V * Y * Vᴴ) := by simp only [Matrix.mul_assoc]
  map_star' X := by
    simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]

theorem isometryHom_continuous (V : Matrix O I ℂ) (hV : Vᴴ * V = 1) :
    Continuous (isometryHom V hV) := by
  change Continuous (fun X : Matrix I I ℂ => V * X * Vᴴ)
  fun_prop

theorem finite_quasispectrum_continuous (X : Matrix I I ℂ) (f : ℝ → ℝ) :
    ContinuousOn f (quasispectrum ℝ X) := by
  rw [quasispectrum_eq_spectrum_union_zero]
  exact (X.finite_real_spectrum.union (Set.finite_singleton 0)).continuousOn f

theorem rpow_isometry (V : Matrix O I ℂ) (hV : Vᴴ * V = 1)
    {X : Matrix I I ℂ} (hX : X.PosSemidef) {t : ℝ} (ht : t ≠ 0) :
    CFC.rpow (V * X * Vᴴ) t = V * CFC.rpow X t * Vᴴ := by
  let φ := isometryHom V hV
  let f : ℝ → ℝ := fun x => x ^ t
  have hVX : (V * X * Vᴴ).PosSemidef := hX.mul_mul_conjTranspose_same V
  have hf0 : f 0 = 0 := Real.zero_rpow ht
  have hf := finite_quasispectrum_continuous X f
  have hfV := finite_quasispectrum_continuous (V * X * Vᴴ) f
  have hm := φ.map_cfcₙ f X hf hf0 (isometryHom_continuous V hV) hX.1 hVX.1
  change V * cfcₙ f X * Vᴴ = cfcₙ f (V * X * Vᴴ) at hm
  rw [cfcₙ_eq_cfc hf hf0, cfcₙ_eq_cfc hfV hf0] at hm
  have hleft : CFC.rpow (V * X * Vᴴ) t = cfc f (V * X * Vᴴ) :=
    CFC.rpow_eq_cfc_real (A := Matrix O O ℂ) (a := V * X * Vᴴ) (y := t) hVX.nonneg
  have hright : CFC.rpow X t = cfc f X :=
    CFC.rpow_eq_cfc_real (A := Matrix I I ℂ) (a := X) (y := t) hX.nonneg
  rw [hleft, hright]
  exact hm.symm

theorem isometry_mul (V : Matrix O I ℂ) (hV : Vᴴ * V = 1)
    (X Y : Matrix I I ℂ) :
    (V * X * Vᴴ) * (V * Y * Vᴴ) = V * (X * Y) * Vᴴ :=
  (isometryHom V hV).map_mul X Y |>.symm

theorem trace_isometry (V : Matrix O I ℂ) (hV : Vᴴ * V = 1)
    (X : Matrix I I ℂ) : (V * X * Vᴴ).trace = X.trace := by
  rw [Matrix.trace_mul_cycle, hV, Matrix.one_mul]

theorem support_isometry (V : Matrix O I ℂ) (hV : Vᴴ * V = 1)
    {ρ σ : Matrix I I ℂ} (hs : QuantumProver.AmplitudeDamping.FiniteModel.SupportLE ρ σ) :
    QuantumProver.AmplitudeDamping.FiniteModel.SupportLE (V * ρ * Vᴴ) (V * σ * Vᴴ) := by
  obtain ⟨F, hF⟩ := hs.exists_right_factor
  apply QuantumProver.AmplitudeDamping.FiniteModel.supportLE_of_eq_mul (F := V * F * Vᴴ)
  rw [isometry_mul V hV, hF]

theorem sandwichedTrace_isometry (V : Matrix O I ℂ) (hV : Vᴴ * V = 1)
    {ρ σ : Matrix I I ℂ} (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef)
    {α : ℝ} (hα : 1 < α) :
    QuantumProver.AmplitudeDamping.FiniteModel.sandwichedTrace α (V * ρ * Vᴴ) (V * σ * Vᴴ) =
      QuantumProver.AmplitudeDamping.FiniteModel.sandwichedTrace α ρ σ := by
  let t : ℝ := (1 - α) / (2 * α)
  have hα0 : α ≠ 0 := by linarith
  have ht : t ≠ 0 := div_ne_zero (sub_ne_zero.mpr hα.ne)
    (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) hα0)
  let W := CFC.rpow σ t
  have hW : Wᴴ = W := (Matrix.nonneg_iff_posSemidef.mp
    (CFC.rpow_nonneg (a := σ) (y := t))).1
  have hX : (W * ρ * W).PosSemidef := by
    simpa only [hW] using hρ.mul_mul_conjTranspose_same W
  unfold QuantumProver.AmplitudeDamping.FiniteModel.sandwichedTrace
  dsimp only
  rw [rpow_isometry V hV hσ ht, isometry_mul V hV, isometry_mul V hV]
  change (CFC.rpow (V * (W * ρ * W) * Vᴴ) α).trace.re = (CFC.rpow (W * ρ * W) α).trace.re
  rw [rpow_isometry V hV hX hα0, trace_isometry V hV]

theorem sandwichedDivergence_isometry (V : Matrix O I ℂ) (hV : Vᴴ * V = 1)
    {ρ σ : Matrix I I ℂ} (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef)
    (hs : QuantumProver.AmplitudeDamping.FiniteModel.SupportLE ρ σ) {α : ℝ} (hα : 1 < α) :
    QuantumProver.AmplitudeDamping.FiniteModel.sandwichedDivergence α (V * ρ * Vᴴ) (V * σ * Vᴴ) =
      QuantumProver.AmplitudeDamping.FiniteModel.sandwichedDivergence α ρ σ := by
  have hVs := support_isometry V hV hs
  simp only [QuantumProver.AmplitudeDamping.FiniteModel.sandwichedDivergence, if_pos hVs, if_pos hs,
    sandwichedTrace_isometry V hV hρ hσ hα]

variable {J : Type*} [Fintype J] [DecidableEq J]

def privateCopyMatrix : Matrix (J × J) J ℂ :=
  PublicHistory.basisEmbedding_B (fun j : J => (j,j))

theorem privateCopyMatrix_isometry :
    (privateCopyMatrix (J := J))ᴴ * privateCopyMatrix (J := J) = 1 :=
  PublicHistory.basisEmbedding_gram_B (fun j : J => (j,j))
    (fun _ _ h => congrArg Prod.fst h)

def privateCopyChannel : KrausChannel J (J × J) Unit where
  op _ := privateCopyMatrix (J := J)
  complete := by simpa only [Fintype.sum_unique] using privateCopyMatrix_isometry (J := J)

def retainedSeedDensity (a : ProbabilityLaw J) : Density ((J × J) × J) :=
  ((privateCopyChannel (J := J)).withRightMemory J).onDensity a.coherentSeedDensity

def retainedSeedComparison (b : ProbabilityLaw J) : Density ((J × J) × J) :=
  ((privateCopyChannel (J := J)).withRightMemory J).onDensity b.copiedDensity

theorem privateCopy_withBob_isometry :
    (privateCopyMatrix (J := J) ⊗ₖ (1 : Matrix J J ℂ))ᴴ *
      (privateCopyMatrix (J := J) ⊗ₖ (1 : Matrix J J ℂ)) = 1 := by
  rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
    ← Matrix.mul_kronecker_mul, privateCopyMatrix_isometry, Matrix.one_mul,
    Matrix.one_kronecker_one]

theorem retainedSeedDensity_matrix (a : ProbabilityLaw J) :
    (retainedSeedDensity a).mat =
      (privateCopyMatrix (J := J) ⊗ₖ (1 : Matrix J J ℂ)) * a.coherentSeedMatrix *
        (privateCopyMatrix (J := J) ⊗ₖ (1 : Matrix J J ℂ))ᴴ := by
  simp only [retainedSeedDensity, KrausChannel.onDensity, KrausChannel.eval,
    KrausChannel.withRightMemory, privateCopyChannel, Fintype.sum_unique,
    ProbabilityLaw.coherentSeedDensity]

theorem retainedSeedComparison_matrix (b : ProbabilityLaw J) :
    (retainedSeedComparison b).mat =
      (privateCopyMatrix (J := J) ⊗ₖ (1 : Matrix J J ℂ)) * b.copiedMatrix *
        (privateCopyMatrix (J := J) ⊗ₖ (1 : Matrix J J ℂ))ᴴ := by
  simp only [retainedSeedComparison, KrausChannel.onDensity, KrausChannel.eval,
    KrausChannel.withRightMemory, privateCopyChannel, Fintype.sum_unique,
    ProbabilityLaw.copiedDensity]

theorem retainedSeed_optimized_divergence (a : ProbabilityLaw J)
    {z : ℝ} (hz : 0 < z) (hz1 : z < 1) :
    QuantumProver.AmplitudeDamping.FiniteModel.sandwichedDivergence (1 / (1 - z))
      (retainedSeedDensity a).mat (retainedSeedComparison (a.optimizedSeedLaw z)).mat =
        (a.renyiSeedCharge z : EReal) := by
  have hα : 1 < 1 / (1 - z) :=
    (lt_div_iff₀ (sub_pos.mpr hz1)).mpr (by linarith)
  rw [retainedSeedDensity_matrix, retainedSeedComparison_matrix,
    sandwichedDivergence_isometry _ privateCopy_withBob_isometry
      a.coherentSeedMatrix_posSemidef (a.optimizedSeedLaw z).copiedMatrix_posSemidef
      (SeedResource.seed_support a _ (fun j => a.optimizedSeedLaw_support hz j)) hα]
  exact a.coherentSeed_optimized_divergence hz hz1

theorem normalizedSeparable_local_isometry {a ao b : ℕ}
    (V : Matrix (Fin ao) (Fin a) ℂ) (hV : Vᴴ * V = 1)
    {σ : PhysicalProtocol.BipartiteMatrix a b}
    (hσ : QuantumProver.AmplitudeDamping.FiniteModel.IsSeparable a b σ) :
    QuantumProver.AmplitudeDamping.FiniteModel.IsSeparable ao b
      ((V ⊗ₖ (1 : Matrix (Fin b) (Fin b) ℂ)) * σ *
        (V ⊗ₖ (1 : Matrix (Fin b) (Fin b) ℂ))ᴴ) := by
  obtain ⟨k, t, A, B, ht, hsum, hAB, rfl⟩ := hσ
  refine ⟨k, t, (fun j => V * A j * Vᴴ), B, ht, hsum, ?_, ?_⟩
  · intro j
    exact ⟨⟨(hAB j).1.1.mul_mul_conjTranspose_same V,
      (trace_isometry V hV (A j)).trans (hAB j).1.2⟩, (hAB j).2⟩
  · simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one]
    apply Finset.sum_congr rfl
    intro j hj
    rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
      Matrix.one_mul, Matrix.mul_one]

def privateCopyFinChannel (d : ℕ) :
    KrausChannel (Fin d) (Fin (d * d)) Unit :=
  (privateCopyChannel (J := Fin d)).relabel_B (Equiv.refl (Fin d))
    (finProdFinEquiv : Fin d × Fin d ≃ Fin (d * d)).symm

def retainedSeedFinDensity {d : ℕ} (a : ProbabilityLaw (Fin d)) :
    Density (Fin (d * d) × Fin d) :=
  ((privateCopyFinChannel d).withRightMemory (Fin d)).onDensity a.coherentSeedDensity

def retainedSeedFinComparison {d : ℕ} (b : ProbabilityLaw (Fin d)) :
    Density (Fin (d * d) × Fin d) :=
  ((privateCopyFinChannel d).withRightMemory (Fin d)).onDensity b.copiedDensity

theorem privateCopyFin_isometry (d : ℕ) :
    ((privateCopyFinChannel d).op ())ᴴ * (privateCopyFinChannel d).op () = 1 := by
  simpa only [Fintype.sum_unique] using (privateCopyFinChannel d).complete

theorem privateCopyFin_withBob_isometry (d : ℕ) :
    ((privateCopyFinChannel d).op () ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ))ᴴ *
      ((privateCopyFinChannel d).op () ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ)) = 1 := by
  rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
    ← Matrix.mul_kronecker_mul, privateCopyFin_isometry, Matrix.one_mul,
    Matrix.one_kronecker_one]

theorem retainedSeedFinDensity_matrix {d : ℕ} (a : ProbabilityLaw (Fin d)) :
    (retainedSeedFinDensity a).mat =
      ((privateCopyFinChannel d).op () ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ)) *
        a.coherentSeedMatrix *
      ((privateCopyFinChannel d).op () ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ))ᴴ := by
  simp only [retainedSeedFinDensity, KrausChannel.onDensity, KrausChannel.eval,
    KrausChannel.withRightMemory, Fintype.sum_unique, ProbabilityLaw.coherentSeedDensity]

theorem retainedSeedFinComparison_matrix {d : ℕ} (b : ProbabilityLaw (Fin d)) :
    (retainedSeedFinComparison b).mat =
      ((privateCopyFinChannel d).op () ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ)) *
        b.copiedMatrix *
      ((privateCopyFinChannel d).op () ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ))ᴴ := by
  simp only [retainedSeedFinComparison, KrausChannel.onDensity, KrausChannel.eval,
    KrausChannel.withRightMemory, Fintype.sum_unique, ProbabilityLaw.copiedDensity]

theorem retainedSeedFinComparison_separable {d : ℕ} (b : ProbabilityLaw (Fin d)) :
    QuantumProver.AmplitudeDamping.FiniteModel.IsSeparable (d * d) d
      (retainedSeedFinComparison b).mat := by
  rw [retainedSeedFinComparison_matrix]
  exact normalizedSeparable_local_isometry _ (privateCopyFin_isometry d)
    b.copiedMatrix_quantum_separable

theorem retainedSeedFin_optimized_divergence {d : ℕ} (a : ProbabilityLaw (Fin d))
    {z : ℝ} (hz : 0 < z) (hz1 : z < 1) :
    QuantumProver.AmplitudeDamping.FiniteModel.sandwichedDivergence (1 / (1 - z))
      (retainedSeedFinDensity a).mat
      (retainedSeedFinComparison (a.optimizedSeedLaw z)).mat =
        (a.renyiSeedCharge z : EReal) := by
  have hα : 1 < 1 / (1 - z) :=
    (lt_div_iff₀ (sub_pos.mpr hz1)).mpr (by linarith)
  rw [retainedSeedFinDensity_matrix, retainedSeedFinComparison_matrix,
    sandwichedDivergence_isometry _ (privateCopyFin_withBob_isometry d)
      a.coherentSeedMatrix_posSemidef (a.optimizedSeedLaw z).copiedMatrix_posSemidef
      (SeedResource.seed_support a _ (fun j => a.optimizedSeedLaw_support hz j)) hα]
  exact a.coherentSeed_optimized_divergence hz hz1

theorem retainedSeedFin_entanglement_le {d : ℕ} (a : ProbabilityLaw (Fin d))
    {z : ℝ} (hz : 0 < z) (hz1 : z < 1) :
    QuantumProver.AmplitudeDamping.FiniteModel.sandwichedEntanglement (1 / (1 - z)) (d * d) d
      (retainedSeedFinDensity a).mat ≤ (a.renyiSeedCharge z : EReal) := by
  rw [← retainedSeedFin_optimized_divergence a hz hz1]
  apply sInf_le
  refine ⟨(retainedSeedFinComparison (a.optimizedSeedLaw z)).mat, ?_, rfl⟩
  exact ⟨⟨(retainedSeedFinComparison _).positive,
    (retainedSeedFinComparison _).normalized⟩, retainedSeedFinComparison_separable _⟩

theorem retainedSeedFin_entanglement_le_bits {d : ℕ} [Nonempty (Fin d)]
    (a : ProbabilityLaw (Fin d)) {z k : ℝ} (hz : 0 < z) (hz1 : z < 1)
    (hk : (d : ℝ) ≤ 2 ^ k) :
    QuantumProver.AmplitudeDamping.FiniteModel.sandwichedEntanglement (1 / (1 - z)) (d * d) d
      (retainedSeedFinDensity a).mat ≤ (k : EReal) := by
  apply (retainedSeedFin_entanglement_le a hz hz1).trans
  exact_mod_cast a.renyiSeedCharge_le_bits z k hz (by simpa using hk)

theorem privateCopy_tensor_basis :
    privateCopyMatrix (J := J) ⊗ₖ (1 : Matrix J J ℂ) =
      PublicHistory.basisEmbedding_B (fun x : J × J => ((x.1,x.1),x.2)) := by
  ext x y
  rcases x with ⟨⟨r,j⟩,b⟩
  rcases y with ⟨j',b'⟩
  by_cases hb : b = b' <;>
    simp [privateCopyMatrix, PublicHistory.basisEmbedding_B, Matrix.kroneckerMap_apply,
      Matrix.one_apply, Prod.mk.injEq, hb, and_assoc, and_left_comm, and_comm]

theorem retainedSeedDensity_apply (a : ProbabilityLaw J) (r j b r' j' b' : J) :
    (retainedSeedDensity a).mat ((r,j),b) ((r',j'),b') =
      if r = j ∧ r' = j' then a.coherentSeedMatrix (j,b) (j',b') else 0 := by
  rw [retainedSeedDensity_matrix, privateCopy_tensor_basis,
    PublicHistory.basisEmbedding_sandwich_apply_B
      (fun x : J × J => ((x.1,x.1),x.2))
      (fun x : (J × J) × J => (x.1.2,x.2)) (fun _ => rfl)]
  simp only [Prod.mk.injEq, and_true, eq_comm]

def forgetAliceRecord (σ : Matrix ((J × J) × J) ((J × J) × J) ℂ) :
    Matrix (J × J) (J × J) ℂ :=
  partialTraceLeft (σ.submatrix (Equiv.prodAssoc J J J).symm
    (Equiv.prodAssoc J J J).symm)

theorem forgetAliceRecord_retainedSeed (a : ProbabilityLaw J) :
    forgetAliceRecord (retainedSeedDensity a).mat = a.copiedMatrix := by
  ext x y
  rcases x with ⟨j,b⟩
  rcases y with ⟨j',b'⟩
  change (∑ r, (retainedSeedDensity a).mat ((r,j),b) ((r,j'),b')) = _
  simp only [retainedSeedDensity_apply]
  by_cases hj : j = j'
  · subst j'
    simp only [and_self, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    by_cases hb : j = b
    · subst b
      by_cases hb' : j = b'
      · subst b'
        simpa [ProbabilityLaw.copiedMatrix, Matrix.diagonal_apply] using
          a.coherentSeedMatrix_diagonal (j,j)
      · simp [ProbabilityLaw.coherentSeedMatrix, ProbabilityLaw.coherentSeedVector,
          ProbabilityLaw.copiedMatrix, Matrix.vecMulVec_apply, Matrix.diagonal_apply,
          hb', Prod.mk.injEq]
    · simp [ProbabilityLaw.coherentSeedMatrix, ProbabilityLaw.coherentSeedVector,
        ProbabilityLaw.copiedMatrix, Matrix.vecMulVec_apply, Matrix.diagonal_apply,
        hb, Prod.mk.injEq]
  · have hzero : ∀ r : J, ¬(r = j ∧ r = j') := by
      intro r h
      exact hj (h.1.symm.trans h.2)
    simp only [if_neg (hzero _), Finset.sum_const_zero]
    simp [ProbabilityLaw.copiedMatrix, Matrix.diagonal_apply, Prod.mk.injEq, hj]

variable {E : Type*} [Fintype E] [DecidableEq E]

def forgetAliceRecordWithEve
    (σ : Matrix (((J × J) × J) × E) (((J × J) × J) × E) ℂ) :
    Matrix ((J × J) × E) ((J × J) × E) ℂ :=
  fun x y => ∑ r, σ (((r,x.1.1),x.1.2),x.2) (((r,y.1.1),y.1.2),y.2)

theorem forgetAliceRecordWithEve_tensor
    (ρ : Density ((J × J) × J)) (ξ : Density E) :
    forgetAliceRecordWithEve (ρ.tensor ξ).mat = forgetAliceRecord ρ.mat ⊗ₖ ξ.mat := by
  ext x y
  simp only [forgetAliceRecordWithEve, Density.tensor, Matrix.kroneckerMap_apply,
    ← Finset.sum_mul]
  rfl

theorem retainedSeed_dephase_same_Eve (a : ProbabilityLaw J) (ξ : Density E) :
    forgetAliceRecordWithEve ((retainedSeedDensity a).tensor ξ).mat =
      (a.copiedDensity.tensor ξ).mat := by
  rw [forgetAliceRecordWithEve_tensor, forgetAliceRecord_retainedSeed]
  rfl

theorem retainedSeed_preparation_same_Eve (a : ProbabilityLaw J) (ξ : Density E) :
    ((((privateCopyChannel (J := J)).withRightMemory J).withRightMemory E).onDensity
      (a.coherentSeedDensity.tensor ξ)) = (retainedSeedDensity a).tensor ξ :=
  onDensity_withRightMemory_tensor _ _ _

theorem retainedSeedFin_honest_charge_same_Eve {d : ℕ}
    (a : ProbabilityLaw (Fin d)) (ξ : Density E) {z : ℝ} (hz : 0 < z) (hz1 : z < 1) :
    QuantumProver.AmplitudeDamping.FiniteModel.sandwichedEntanglement (1 / (1 - z)) (d * d) d
      (partialTraceRight ((retainedSeedFinDensity a).tensor ξ).mat) ≤
        (a.renyiSeedCharge z : EReal) := by
  rw [SeedResource.honest_marginal_tensor_independent_Eve]
  exact retainedSeedFin_entanglement_le a hz hz1

open PhysicalProtocol PhysicalProtocol.FiniteKeyProtocol

def privateAliceLocalEquiv (c a : ℕ) : Fin (c * a) ≃ (Fin c × Fin a) :=
  (finProdFinEquiv : Fin c × Fin a ≃ Fin (c * a)).symm

def privateAliceJointEquiv (c a b : ℕ) :
    (Fin (c * a) × Fin b) ≃ (Fin c × (Fin a × Fin b)) :=
  ((privateAliceLocalEquiv c a).prodCongr (Equiv.refl (Fin b))).trans
    (Equiv.prodAssoc (Fin c) (Fin a) (Fin b))

def privateAliceInstrument {a ao k : ℕ}
    (c : ℕ) (C : KrausChannel (Fin a) (Fin ao) (Fin k)) :
    KrausChannel (Fin (c * a)) (Fin (c * ao)) (Fin k) :=
  (C.withMemory (Fin c)).relabel_B
    (privateAliceLocalEquiv c a) (privateAliceLocalEquiv c ao)

def privateAliceCallChartEquiv (c a : ℕ) :
    Fin (c * (2 * a)) ≃ Fin (2 * (c * a)) :=
  (privateAliceLocalEquiv c (2 * a)).trans
    (QuantumProver.AmplitudeDamping.FiniteModel.aliceSpectatorPortEquivB c a).symm

def privateAliceCallChart (c a : ℕ) :
    KrausChannel (Fin (c * (2 * a))) (Fin (2 * (c * a))) (Fin 1) where
  op _ := PublicHistory.basisEmbedding_B (privateAliceCallChartEquiv c a)
  complete := by
    simpa only [Fin.sum_univ_one] using
      PublicHistory.basisEmbedding_gram_B (privateAliceCallChartEquiv c a)
        (privateAliceCallChartEquiv c a).injective

def withPrivateAlice {p : ℝ} {a b af bf : ℕ} (c : ℕ)
    (P : FiniteKeyProtocol p a b af bf) :
    FiniteKeyProtocol p (c * a) b (c * af) bf :=
  match P with
  | .done a b => .done (c * a) b
  | .alice C next => .alice (privateAliceInstrument c C) fun z => withPrivateAlice c (next z)
  | .bob C next => .bob C fun z => withPrivateAlice c (next z)
  | .call (a := a₀) next => .alice (privateAliceCallChart c a₀)
      fun _ => .call (withPrivateAlice c next)

theorem withPrivateAlice_calls {p : ℝ} {a b af bf : ℕ} (c : ℕ)
    (P : FiniteKeyProtocol p a b af bf) : (withPrivateAlice c P).calls = P.calls := by
  induction P with
  | done a b => rfl
  | alice C next ih => simp only [withPrivateAlice, calls, ih]
  | bob C next ih => simp only [withPrivateAlice, calls, ih]
  | call next ih => simp [withPrivateAlice, calls, ih]

def privateAliceEnvironmentEquiv {p : ℝ} {a b af bf : ℕ} (c : ℕ)
    (P : FiniteKeyProtocol p a b af bf) : (withPrivateAlice c P).Environment ≃ P.Environment :=
  match P with
  | .done _ _ => Equiv.refl Unit
  | .alice _ next => Equiv.sigmaCongrRight fun z => privateAliceEnvironmentEquiv c (next z)
  | .bob _ next => Equiv.sigmaCongrRight fun z => privateAliceEnvironmentEquiv c (next z)
  | .call next =>
      { toFun := fun h => (h.2.1, privateAliceEnvironmentEquiv c next h.2.2)
        invFun := fun h => ⟨0, (h.1, (privateAliceEnvironmentEquiv c next).symm h.2)⟩
        left_inv := by
          intro h
          rcases h with ⟨z,q,t⟩
          have hz : z = (0 : Fin 1) := Subsingleton.elim _ _
          subst z
          simp only [Equiv.symm_apply_apply]
          rfl
        right_inv := by
          intro h
          rcases h with ⟨q,t⟩
          change (q, privateAliceEnvironmentEquiv c next
            ((privateAliceEnvironmentEquiv c next).symm t)) = (q,t)
          rw [Equiv.apply_symm_apply] }

def privateAlicePublicEquiv {p : ℝ} {a b af bf : ℕ} (c : ℕ)
    (P : FiniteKeyProtocol p a b af bf) :
    (withPrivateAlice c P).comparisonPublicHistory_B ≃ P.comparisonPublicHistory_B :=
  match P with
  | .done _ _ => Equiv.refl Unit
  | .alice _ next => Equiv.sigmaCongrRight fun z => privateAlicePublicEquiv c (next z)
  | .bob _ next => Equiv.sigmaCongrRight fun z => privateAlicePublicEquiv c (next z)
  | .call next =>
      { toFun := fun h => privateAlicePublicEquiv c next h.2
        invFun := fun h => ⟨0, (privateAlicePublicEquiv c next).symm h⟩
        left_inv := by
          intro h
          rcases h with ⟨z,t⟩
          have hz : z = (0 : Fin 1) := Subsingleton.elim _ _
          subst z
          exact congrArg (fun u : (withPrivateAlice c next).comparisonPublicHistory_B =>
            (⟨0,u⟩ : (z : Fin 1) × (withPrivateAlice c next).comparisonPublicHistory_B))
              ((privateAlicePublicEquiv c next).symm_apply_apply t)
        right_inv := by intro h; exact (privateAlicePublicEquiv c next).apply_symm_apply h }

theorem privateAlice_publicTranscript {p : ℝ} {a b af bf : ℕ} (c : ℕ)
    (P : FiniteKeyProtocol p a b af bf) : ∀ h,
    privateAlicePublicEquiv c P ((withPrivateAlice c P).publicTranscript_B h) =
      P.publicTranscript_B (privateAliceEnvironmentEquiv c P h) := by
  induction P with
  | done a b => intro h; rfl
  | @alice a b ao af bf k C next ih =>
      intro h
      rcases h with ⟨z,t⟩
      change Sigma.mk (β := fun w : Fin k => (next w).comparisonPublicHistory_B) z
        (privateAlicePublicEquiv c (next z)
        ((withPrivateAlice c (next z)).publicTranscript_B t)) =
          Sigma.mk (β := fun w : Fin k => (next w).comparisonPublicHistory_B) z
            ((next z).publicTranscript_B (privateAliceEnvironmentEquiv c (next z) t))
      rw [ih z t]
  | @bob a b bo af bf k C next ih =>
      intro h
      rcases h with ⟨z,t⟩
      change Sigma.mk (β := fun w : Fin k => (next w).comparisonPublicHistory_B) z
        (privateAlicePublicEquiv c (next z)
        ((withPrivateAlice c (next z)).publicTranscript_B t)) =
          Sigma.mk (β := fun w : Fin k => (next w).comparisonPublicHistory_B) z
            ((next z).publicTranscript_B (privateAliceEnvironmentEquiv c (next z) t))
      rw [ih z t]
  | call next ih =>
      intro h
      rcases h with ⟨z,q,t⟩
      exact ih t

theorem privateAlice_public_eq_iff {p : ℝ} {a b af bf : ℕ} (c : ℕ)
    (P : FiniteKeyProtocol p a b af bf) (h h' : (withPrivateAlice c P).Environment) :
    (withPrivateAlice c P).publicTranscript_B h = (withPrivateAlice c P).publicTranscript_B h' ↔
      P.publicTranscript_B (privateAliceEnvironmentEquiv c P h) =
        P.publicTranscript_B (privateAliceEnvironmentEquiv c P h') := by
  rw [← (privateAlicePublicEquiv c P).injective.eq_iff,
    privateAlice_publicTranscript, privateAlice_publicTranscript]

theorem privateAlice_alice_step {a ao b k : ℕ} (c : ℕ)
    (C : KrausChannel (Fin a) (Fin ao) (Fin k)) (z : Fin k) :
    (privateAliceInstrument c C).op z ⊗ₖ (1 : Matrix (Fin b) (Fin b) ℂ) =
      ((1 : Matrix (Fin c) (Fin c) ℂ) ⊗ₖ
        (C.op z ⊗ₖ (1 : Matrix (Fin b) (Fin b) ℂ))).submatrix
          (privateAliceJointEquiv c ao b) (privateAliceJointEquiv c a b) := by
  ext x y
  simp only [privateAliceInstrument, KrausChannel.relabel_B, KrausChannel.withMemory,
    Matrix.submatrix_apply, Matrix.kroneckerMap_apply, privateAliceJointEquiv,
    Equiv.trans_apply, Equiv.prodCongr_apply, Equiv.prodAssoc_apply,
    Prod.map_fst, Prod.map_snd, Equiv.refl_apply, mul_assoc]

theorem privateAlice_bob_step {a b bo k : ℕ} (c : ℕ)
    (C : KrausChannel (Fin b) (Fin bo) (Fin k)) (z : Fin k) :
    (1 : Matrix (Fin (c * a)) (Fin (c * a)) ℂ) ⊗ₖ C.op z =
      ((1 : Matrix (Fin c) (Fin c) ℂ) ⊗ₖ
        ((1 : Matrix (Fin a) (Fin a) ℂ) ⊗ₖ C.op z)).submatrix
          (privateAliceJointEquiv c a bo) (privateAliceJointEquiv c a b) := by
  have hI : ((1 : Matrix (Fin c) (Fin c) ℂ) ⊗ₖ
      (1 : Matrix (Fin a) (Fin a) ℂ)).submatrix
        (privateAliceLocalEquiv c a) (privateAliceLocalEquiv c a) = 1 := by
    rw [Matrix.one_kronecker_one, Matrix.submatrix_one_equiv]
  rw [← hI]
  ext x y
  simp only [Matrix.submatrix_apply, Matrix.kroneckerMap_apply, privateAliceJointEquiv,
    Equiv.trans_apply, Equiv.prodCongr_apply, Equiv.prodAssoc_apply,
    Prod.map_fst, Prod.map_snd, Equiv.refl_apply, mul_assoc]

theorem basisEmbedding_tensor_identity {R S B : Type*}
    [Fintype R] [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    (f : R → S) :
    PublicHistory.basisEmbedding_B f ⊗ₖ (1 : Matrix B B ℂ) =
      PublicHistory.basisEmbedding_B (fun x : R × B => (f x.1,x.2)) := by
  ext x y
  rcases x with ⟨s,b⟩
  rcases y with ⟨r,b'⟩
  by_cases hb : b = b' <;>
    simp [PublicHistory.basisEmbedding_B, Matrix.kroneckerMap_apply,
      Matrix.one_apply, Prod.mk.injEq, hb, and_comm]

theorem mul_basisEmbedding {R S T : Type*} [Fintype S] [DecidableEq S]
    (K : Matrix T S ℂ) (f : R → S) :
    K * PublicHistory.basisEmbedding_B f = K.submatrix id f := by
  ext t r
  simp [Matrix.mul_apply, PublicHistory.basisEmbedding_B, Matrix.submatrix_apply, mul_ite]

theorem privateAlice_transfer_spectator (p : ℝ) (c a b : ℕ) (z : Fin 2) :
    transferKraus p (c * a) b z =
      ((1 : Matrix (Fin c) (Fin c) ℂ) ⊗ₖ transferKraus p a b z).submatrix
        (privateAliceJointEquiv c a (2 * b))
        (QuantumProver.AmplitudeDamping.FiniteModel.aliceSpectatorInputEquivB c a b) := by
  rw [← IndependentLanes.quantum_callOperator_eq_key_B,
    QuantumProver.AmplitudeDamping.FiniteModel.callOperator_aliceSpectatorB,
    IndependentLanes.quantum_callOperator_eq_key_B]
  rfl

theorem privateAlice_call_step (p : ℝ) (c a b : ℕ) (z : Fin 2) :
    transferKraus p (c * a) b z *
      ((privateAliceCallChart c a).op 0 ⊗ₖ (1 : Matrix (Fin b) (Fin b) ℂ)) =
      ((1 : Matrix (Fin c) (Fin c) ℂ) ⊗ₖ transferKraus p a b z).submatrix
        (privateAliceJointEquiv c a (2 * b)) (privateAliceJointEquiv c (2 * a) b) := by
  rw [privateAlice_transfer_spectator]
  simp only [privateAliceCallChart]
  rw [basisEmbedding_tensor_identity, mul_basisEmbedding]
  ext x y
  simp only [Matrix.submatrix_apply, id_eq,
    QuantumProver.AmplitudeDamping.FiniteModel.aliceSpectatorInputEquivB,
    privateAliceCallChartEquiv, privateAliceJointEquiv,
    Equiv.trans_apply, Equiv.prodCongr_apply, Equiv.prodAssoc_apply,
    Prod.map_fst, Prod.map_snd, Equiv.refl_apply, Equiv.apply_symm_apply]

theorem withPrivateAlice_historyKraus {p : ℝ} {a b af bf : ℕ} (c : ℕ)
    (P : FiniteKeyProtocol p a b af bf) : ∀ h,
    (withPrivateAlice c P).historyKraus_B h =
      ((1 : Matrix (Fin c) (Fin c) ℂ) ⊗ₖ
        P.historyKraus_B (privateAliceEnvironmentEquiv c P h)).submatrix
          (privateAliceJointEquiv c af bf) (privateAliceJointEquiv c a b) := by
  induction P with
  | done a b =>
      intro h
      change 1 = ((1 : Matrix (Fin c) (Fin c) ℂ) ⊗ₖ
        (1 : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ)).submatrix _ _
      rw [Matrix.one_kronecker_one, Matrix.submatrix_one_equiv]
  | @alice a b ao af bf k C next ih =>
      intro h
      rcases h with ⟨z,t⟩
      change (withPrivateAlice c (next z)).historyKraus_B t *
        ((privateAliceInstrument c C).op z ⊗ₖ (1 : Matrix (Fin b) (Fin b) ℂ)) =
          ((1 : Matrix (Fin c) (Fin c) ℂ) ⊗ₖ
            ((next z).historyKraus_B (privateAliceEnvironmentEquiv c (next z) t) *
              (C.op z ⊗ₖ (1 : Matrix (Fin b) (Fin b) ℂ)))).submatrix _ _
      rw [ih z t, privateAlice_alice_step, Matrix.submatrix_mul_equiv,
        ← Matrix.mul_kronecker_mul, Matrix.one_mul]
  | @bob a b bo af bf k C next ih =>
      intro h
      rcases h with ⟨z,t⟩
      change (withPrivateAlice c (next z)).historyKraus_B t *
        ((1 : Matrix (Fin (c * a)) (Fin (c * a)) ℂ) ⊗ₖ C.op z) =
          ((1 : Matrix (Fin c) (Fin c) ℂ) ⊗ₖ
            ((next z).historyKraus_B (privateAliceEnvironmentEquiv c (next z) t) *
              ((1 : Matrix (Fin a) (Fin a) ℂ) ⊗ₖ C.op z))).submatrix _ _
      rw [ih z t, privateAlice_bob_step, Matrix.submatrix_mul_equiv,
        ← Matrix.mul_kronecker_mul, Matrix.one_mul]
  | @call a b af bf next ih =>
      intro h
      rcases h with ⟨u,z,t⟩
      change ((withPrivateAlice c next).historyKraus_B t * transferKraus p (c * a) b z) *
        ((privateAliceCallChart c a).op 0 ⊗ₖ (1 : Matrix (Fin b) (Fin b) ℂ)) =
          ((1 : Matrix (Fin c) (Fin c) ℂ) ⊗ₖ
            (next.historyKraus_B (privateAliceEnvironmentEquiv c next t) *
              transferKraus p a b z)).submatrix _ _
      rw [Matrix.mul_assoc, privateAlice_call_step, ih t, Matrix.submatrix_mul_equiv,
        ← Matrix.mul_kronecker_mul, Matrix.one_mul]

theorem withPrivateAlice_fullOutput {p : ℝ} {a b af bf : ℕ} (c : ℕ)
    (P : FiniteKeyProtocol p a b af bf)
    (ρ : Matrix (Fin c × (Fin a × Fin b)) (Fin c × (Fin a × Fin b)) ℂ) :
    (withPrivateAlice c P).fullOutput
      (ρ.submatrix (privateAliceJointEquiv c a b) (privateAliceJointEquiv c a b)) =
      (LaneHistoryTransport.fullOutputWithPrivateMemory_B P ρ).submatrix
        ((privateAliceJointEquiv c af bf).prodCongr (privateAliceEnvironmentEquiv c P))
        ((privateAliceJointEquiv c af bf).prodCongr (privateAliceEnvironmentEquiv c P)) :=
  LaneHistoryTransport.fullOutput_privateMemory_transport_B P (withPrivateAlice c P)
    (privateAliceJointEquiv c a b) (privateAliceJointEquiv c af bf)
    (privateAliceEnvironmentEquiv c P) (withPrivateAlice_historyKraus c P)
    (privateAlice_public_eq_iff c P) ρ

theorem withPrivateAlice_priorEve {p : ℝ} {a b af bf : ℕ} (c : ℕ)
    (P : FiniteKeyProtocol p a b af bf)
    (ρ : Matrix ((Fin c × (Fin a × Fin b)) × E)
      ((Fin c × (Fin a × Fin b)) × E) ℂ) :
    PublicHistory.localPriorEveMatrix_B (withPrivateAlice c P)
      (ρ.submatrix ((privateAliceJointEquiv c a b).prodCongr (Equiv.refl E))
        ((privateAliceJointEquiv c a b).prodCongr (Equiv.refl E))) =
      (LaneHistoryTransport.fullOutputWithPrivateMemoryAndEve_B P ρ).submatrix
        ((privateAliceJointEquiv c af bf).prodCongr
          ((privateAliceEnvironmentEquiv c P).prodCongr (Equiv.refl E)))
        ((privateAliceJointEquiv c af bf).prodCongr
          ((privateAliceEnvironmentEquiv c P).prodCongr (Equiv.refl E))) :=
  LaneHistoryTransport.priorEve_privateMemory_transport_B P (withPrivateAlice c P)
    (privateAliceJointEquiv c a b) (privateAliceJointEquiv c af bf)
    (privateAliceEnvironmentEquiv c P) (withPrivateAlice_historyKraus c P)
    (privateAlice_public_eq_iff c P) ρ

def forgetPrivateAliceInput (c a b : ℕ)
    (ρ : Matrix ((Fin c × (Fin a × Fin b)) × E)
      ((Fin c × (Fin a × Fin b)) × E) ℂ) :
    Matrix ((Fin a × Fin b) × E) ((Fin a × Fin b) × E) ℂ :=
  partialTraceLeft (ρ.submatrix (Equiv.prodAssoc (Fin c) (Fin a × Fin b) E).symm
    (Equiv.prodAssoc (Fin c) (Fin a × Fin b) E).symm)

def privateAliceOutputEquiv {p : ℝ} {a b af bf : ℕ} (c : ℕ)
    (P : FiniteKeyProtocol p a b af bf) :
    ((Fin (c * af) × Fin bf) × ((withPrivateAlice c P).Environment × E)) ≃
      (Fin c × ((Fin af × Fin bf) × (P.Environment × E))) :=
  (((privateAliceJointEquiv c af bf).prodCongr
      ((privateAliceEnvironmentEquiv c P).prodCongr (Equiv.refl E))).trans
    (Equiv.prodAssoc (Fin c) (Fin af × Fin bf) (P.Environment × E)))

def forgetPrivateAliceOutput {p : ℝ} {a b af bf : ℕ} (c : ℕ)
    (P : FiniteKeyProtocol p a b af bf)
    (σ : Matrix ((Fin (c * af) × Fin bf) × ((withPrivateAlice c P).Environment × E))
      ((Fin (c * af) × Fin bf) × ((withPrivateAlice c P).Environment × E)) ℂ) :
    Matrix ((Fin af × Fin bf) × (P.Environment × E))
      ((Fin af × Fin bf) × (P.Environment × E)) ℂ :=
  partialTraceLeft (σ.submatrix (privateAliceOutputEquiv (E := E) c P).symm
    (privateAliceOutputEquiv (E := E) c P).symm)

theorem fullOutput_sum {p : ℝ} {a b af bf : ℕ}
    (P : FiniteKeyProtocol p a b af bf) {R : Type*} [Fintype R]
    (ρ : R → BipartiteMatrix a b) :
    P.fullOutput (∑ r, ρ r) = ∑ r, P.fullOutput (ρ r) := by
  ext x y
  rcases x with ⟨x,h⟩
  rcases y with ⟨y,h'⟩
  simp only [Matrix.sum_apply, P.fullOutput_historyKraus_apply_B]
  by_cases hh : P.publicTranscript_B h = P.publicTranscript_B h'
  · simp only [if_pos hh, Matrix.mul_sum, Matrix.sum_mul, Matrix.sum_apply]
  · simp only [if_neg hh, Finset.sum_const_zero]

theorem localPriorEveMatrix_sum {p : ℝ} {a b af bf : ℕ}
    (P : FiniteKeyProtocol p a b af bf) {R : Type*} [Fintype R]
    (ρ : R → Matrix ((Fin a × Fin b) × E) ((Fin a × Fin b) × E) ℂ) :
    PublicHistory.localPriorEveMatrix_B P (∑ r, ρ r) =
      ∑ r, PublicHistory.localPriorEveMatrix_B P (ρ r) := by
  ext x y
  have ht := congrArg (fun M => M (x.1,x.2.1) (y.1,y.2.1))
    (fullOutput_sum P (fun r => Matrix.of fun i j => ρ r (i,x.2.2) (j,y.2.2)))
  have hblock : (Matrix.of fun i j => ∑ r, ρ r (i,x.2.2) (j,y.2.2)) =
      ∑ r, Matrix.of (fun i j => ρ r (i,x.2.2) (j,y.2.2)) := by
    ext i j
    simp only [Matrix.of_apply, Matrix.sum_apply]
  simp only [PublicHistory.localPriorEveMatrix_B, Matrix.sum_apply]
  rw [hblock]
  simpa only [Matrix.sum_apply] using ht

theorem withPrivateAlice_forget_same_Eve {p : ℝ} {a b af bf : ℕ} (c : ℕ)
    (P : FiniteKeyProtocol p a b af bf)
    (ρ : Matrix ((Fin c × (Fin a × Fin b)) × E)
      ((Fin c × (Fin a × Fin b)) × E) ℂ) :
    forgetPrivateAliceOutput c P
      (PublicHistory.localPriorEveMatrix_B (withPrivateAlice c P)
        (ρ.submatrix ((privateAliceJointEquiv c a b).prodCongr (Equiv.refl E))
          ((privateAliceJointEquiv c a b).prodCongr (Equiv.refl E)))) =
      PublicHistory.localPriorEveMatrix_B P (forgetPrivateAliceInput c a b ρ) := by
  rw [withPrivateAlice_priorEve]
  have hin : forgetPrivateAliceInput c a b ρ =
      ∑ r : Fin c, Matrix.of (fun x y => ρ ((r,x.1),x.2) ((r,y.1),y.2)) := by
    ext x y
    simp only [forgetPrivateAliceInput, partialTraceLeft, Matrix.submatrix_apply,
      Equiv.prodAssoc_symm_apply, Matrix.sum_apply, Matrix.of_apply]
  rw [hin, localPriorEveMatrix_sum]
  ext x y
  simp only [forgetPrivateAliceOutput, partialTraceLeft, Matrix.submatrix_apply,
    privateAliceOutputEquiv, Equiv.symm_trans_apply, Equiv.prodAssoc_symm_apply,
    Equiv.prodCongr_apply, Equiv.prodCongr_symm, Equiv.apply_symm_apply,
    Equiv.refl_symm, Equiv.refl_apply, Prod.map_fst, Prod.map_snd,
    LaneHistoryTransport.fullOutputWithPrivateMemoryAndEve_B,
    Matrix.sum_apply, PublicHistory.localPriorEveMatrix_B, Matrix.of_apply]

theorem retainedSeedFinDensity_relabel {d : ℕ} (a : ProbabilityLaw (Fin d)) :
    retainedSeedFinDensity a = (retainedSeedDensity a).relabel
      ((privateAliceLocalEquiv d d).prodCongr (Equiv.refl (Fin d))) := by
  apply Density.eq_of_mat_eq
  rw [retainedSeedFinDensity_matrix]
  change _ = (retainedSeedDensity a).mat.submatrix _ _
  rw [retainedSeedDensity_matrix]
  let W := privateCopyMatrix (J := Fin d) ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ)
  let eO := (privateAliceLocalEquiv d d).prodCongr (Equiv.refl (Fin d))
  have hW : (privateCopyFinChannel d).op () ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ) =
      W.submatrix eO (Equiv.refl (Fin d × Fin d)) := by
    ext x y
    rfl
  rw [hW, Matrix.conjTranspose_submatrix]
  change W.submatrix eO (Equiv.refl _) *
    (a.coherentSeedMatrix.submatrix (Equiv.refl _) (Equiv.refl _)) *
      Wᴴ.submatrix (Equiv.refl _) eO = (W * a.coherentSeedMatrix * Wᴴ).submatrix eO eO
  rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]

def retainedSeedMemoryMatrix {d : ℕ} (a : ProbabilityLaw (Fin d)) (ξ : Density E) :
    Matrix ((Fin d × (Fin d × Fin d)) × E) ((Fin d × (Fin d × Fin d)) × E) ℂ :=
  ((retainedSeedDensity a).tensor ξ).mat.submatrix
    ((Equiv.prodAssoc (Fin d) (Fin d) (Fin d)).symm.prodCongr (Equiv.refl E))
    ((Equiv.prodAssoc (Fin d) (Fin d) (Fin d)).symm.prodCongr (Equiv.refl E))

theorem retainedSeedMemoryMatrix_matrix {d : ℕ} (a : ProbabilityLaw (Fin d)) (ξ : Density E) :
    (retainedSeedMemoryMatrix a ξ).submatrix
      ((privateAliceJointEquiv d d d).prodCongr (Equiv.refl E))
      ((privateAliceJointEquiv d d d).prodCongr (Equiv.refl E)) =
        ((retainedSeedFinDensity a).tensor ξ).mat := by
  rw [retainedSeedFinDensity_relabel]
  ext x y
  rfl

theorem retainedSeedMemoryMatrix_forget {d : ℕ} (a : ProbabilityLaw (Fin d)) (ξ : Density E) :
    forgetPrivateAliceInput d d d (retainedSeedMemoryMatrix a ξ) =
      (a.copiedDensity.tensor ξ).mat := by
  exact retainedSeed_dephase_same_Eve a ξ

theorem retainedSeed_physical_protocol_same_Eve {p : ℝ} {d af bf : ℕ}
    (P : FiniteKeyProtocol p d d af bf) (a : ProbabilityLaw (Fin d)) (ξ : Density E) :
    forgetPrivateAliceOutput d P
      (PublicHistory.localPriorEveMatrix_B (withPrivateAlice d P)
        ((retainedSeedFinDensity a).tensor ξ).mat) =
      PublicHistory.localPriorEveMatrix_B P (a.copiedDensity.tensor ξ).mat := by
  rw [← retainedSeedMemoryMatrix_matrix a ξ, withPrivateAlice_forget_same_Eve,
    retainedSeedMemoryMatrix_forget]

end QuantumProver.AmplitudeDamping.SecretKey.InitialSeed

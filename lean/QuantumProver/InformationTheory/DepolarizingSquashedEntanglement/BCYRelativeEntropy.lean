import QuantumProver.InformationTheory.DepolarizingSquashedEntanglement.Definitions
import QuantumProver.InformationTheory.QuantumEntropy.TensorLogTrace
import QuantumProver.InformationTheory.QuantumEntropy.EntropyReindex

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

open Matrix Set Filter
open scoped Topology BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
  Kronecker

namespace QuantumProver.DepolarizingSquashedEntanglement.BCYRelativeEntropy

variable {A B C D I J : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
  [Fintype I] [Fintype J] [DecidableEq A] [DecidableEq B] [DecidableEq C]
  [DecidableEq D] [DecidableEq I] [DecidableEq J]

theorem density_matrix (ρ : Density I) : QuantumProver.SuperchannelDiscrimination.FlaggedStates.IsDensity ρ.matrix :=
  ⟨ρ.positive, ρ.trace_one⟩

def umegakiNats (R S : QMatrix I) : EReal :=
  QuantumProver.SuperchannelDiscrimination.FlaggedStates.relativeEntropyBits R S * (Real.log 2 : EReal)

theorem umegakiNats_of_support (R S : QMatrix I) (hs : QuantumProver.SuperchannelDiscrimination.FlaggedStates.HasSupportIn R S) :
    umegakiNats R S = ((R * (cfc Real.log R - cfc Real.log S)).trace.re : EReal) := by
  rw [umegakiNats, QuantumProver.SuperchannelDiscrimination.FlaggedStates.relativeEntropyBits, if_pos hs]
  change ((QuantumProver.SuperchannelDiscrimination.FlaggedStates.finiteRelativeEntropyBits R S * Real.log 2 : ℝ) : EReal) = _
  rw [QuantumProver.SuperchannelDiscrimination.FlaggedStates.finiteRelativeEntropyBits, div_mul_cancel₀ _ (ne_of_gt (Real.log_pos (by norm_num)))]

theorem umegakiNats_eq_top_iff (R S : QMatrix I) :
    umegakiNats R S = ⊤ ↔ ¬ QuantumProver.SuperchannelDiscrimination.FlaggedStates.HasSupportIn R S := by
  classical
  by_cases hs : QuantumProver.SuperchannelDiscrimination.FlaggedStates.HasSupportIn R S
  · rw [umegakiNats_of_support R S hs]
    simp [hs]
  · simp only [umegakiNats, QuantumProver.SuperchannelDiscrimination.FlaggedStates.relativeEntropyBits, if_neg hs,
      EReal.top_mul_coe_of_pos (Real.log_pos (show (1 : ℝ) < 2 by norm_num))]
    simp [hs]

theorem umegakiNats_nonneg (ρ σ : Density I) : 0 ≤ umegakiNats ρ.matrix σ.matrix :=
  EReal.mul_nonneg
    (QuantumProver.SuperchannelDiscrimination.Klein.relativeEntropyBits_nonneg
      (density_matrix ρ) (density_matrix σ))
    (EReal.coe_nonneg.mpr (le_of_lt (Real.log_pos (by norm_num))))

theorem umegakiNats_self (R : QMatrix I) : umegakiNats R R = 0 := by
  rw [umegakiNats_of_support R R (QuantumProver.SuperchannelDiscrimination.FlaggedStates.hasSupportIn_self R)]
  simp

def productDensity (a : Density A) (b : Density B) : Density (A × B) where
  matrix := a.matrix ⊗ₖ b.matrix
  positive := a.positive.kronecker b.positive
  trace_one := by rw [Matrix.trace_kronecker, a.trace_one, b.trace_one, one_mul]

theorem productDensity_separable (a : Density A) (b : Density B) :
    IsSeparable (productDensity a b).matrix :=
  subset_convexHull ℝ _ ⟨a, b, rfl⟩

def leftMarginal (ρ : Density (A × B)) : Density A where
  matrix := partialTraceRight ρ.matrix
  positive := partialTraceRight_positive ρ.positive
  trace_one := (partialTraceRight_trace ρ.matrix).trans ρ.trace_one

def rightMarginal (ρ : Density (A × B)) : Density B where
  matrix := partialTraceLeft ρ.matrix
  positive := partialTraceLeft_positive ρ.positive
  trace_one := (partialTraceLeft_trace ρ.matrix).trans ρ.trace_one

theorem entropyNat_eq_shared (R : QMatrix I) : entropyNat R = QuantumProver.QuantumEntropy.entropyNats R :=
  (QuantumProver.QuantumEntropy.entropyNats_eq_trace_cfc_negMulLog R).symm

theorem umegakiNats_marginal_product (ρ : Density (A × B)) :
    umegakiNats ρ.matrix (productDensity (leftMarginal ρ) (rightMarginal ρ)).matrix =
      ((entropyNat (leftMarginal ρ).matrix + entropyNat (rightMarginal ρ).matrix -
        entropyNat ρ.matrix : ℝ) : EReal) := by
  have h := QuantumProver.QuantumEntropy.relativeEntropyBits_marginal_tensor ρ.positive
  change QuantumProver.SuperchannelDiscrimination.FlaggedStates.relativeEntropyBits ρ.matrix
    (partialTraceRight ρ.matrix ⊗ₖ partialTraceLeft ρ.matrix) = _ at h
  change QuantumProver.SuperchannelDiscrimination.FlaggedStates.relativeEntropyBits ρ.matrix
      (partialTraceRight ρ.matrix ⊗ₖ partialTraceLeft ρ.matrix) * (Real.log 2 : EReal) = _
  rw [h]
  change (((QuantumProver.QuantumEntropy.entropyBits (partialTraceRight ρ.matrix) +
    QuantumProver.QuantumEntropy.entropyBits (partialTraceLeft ρ.matrix) - QuantumProver.QuantumEntropy.entropyBits ρ.matrix) *
      Real.log 2 : ℝ) : EReal) = _
  apply congrArg (fun x : ℝ => (x : EReal))
  simp only [entropyNat_eq_shared, QuantumProver.QuantumEntropy.entropyNats_eq_entropyBits_mul_log_two,
    leftMarginal, rightMarginal]
  ring

abbrev SeparableDensity (A B : Type*) [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] :=
  {σ : Density (A × B) // IsSeparable σ.matrix}

def relativeEntropyEntanglementNat (ρ : Density (A × B)) : EReal :=
  ⨅ σ : SeparableDensity A B, umegakiNats ρ.matrix σ.val.matrix

theorem relativeEntropyEntanglementNat_nonneg (ρ : Density (A × B)) :
    0 ≤ relativeEntropyEntanglementNat ρ :=
  le_iInf fun σ => umegakiNats_nonneg ρ σ.val

theorem relativeEntropyEntanglementNat_le (ρ : Density (A × B))
    (σ : Density (A × B)) (hσ : IsSeparable σ.matrix) :
    relativeEntropyEntanglementNat ρ ≤ umegakiNats ρ.matrix σ.matrix :=
  iInf_le_of_le ⟨σ, hσ⟩ le_rfl

theorem relativeEntropyEntanglementNat_le_product (ρ : Density (A × B))
    (a : Density A) (b : Density B) :
    relativeEntropyEntanglementNat ρ ≤ umegakiNats ρ.matrix (productDensity a b).matrix :=
  relativeEntropyEntanglementNat_le ρ _ (productDensity_separable a b)

theorem relativeEntropyEntanglementNat_le_mutualInformation (ρ : Density (A × B)) :
    relativeEntropyEntanglementNat ρ ≤
      ((entropyNat (leftMarginal ρ).matrix + entropyNat (rightMarginal ρ).matrix -
        entropyNat ρ.matrix : ℝ) : EReal) := by
  rw [← umegakiNats_marginal_product]
  exact relativeEntropyEntanglementNat_le_product ρ _ _

theorem relativeEntropyEntanglementNat_ne_top (ρ : Density (A × B)) :
    relativeEntropyEntanglementNat ρ ≠ ⊤ :=
  ne_of_lt (lt_of_le_of_lt (relativeEntropyEntanglementNat_le_mutualInformation ρ)
    (EReal.coe_lt_top _))

theorem relativeEntropyEntanglementNat_ne_bot (ρ : Density (A × B)) :
    relativeEntropyEntanglementNat ρ ≠ ⊥ :=
  ne_of_gt (lt_of_lt_of_le (EReal.bot_lt_coe 0)
    (relativeEntropyEntanglementNat_nonneg ρ))

def relativeEntropyEntanglementReal (ρ : Density (A × B)) : ℝ :=
  (relativeEntropyEntanglementNat ρ).toReal

theorem coe_relativeEntropyEntanglementReal (ρ : Density (A × B)) :
    (relativeEntropyEntanglementReal ρ : EReal) = relativeEntropyEntanglementNat ρ :=
  EReal.coe_toReal (relativeEntropyEntanglementNat_ne_top ρ)
    (relativeEntropyEntanglementNat_ne_bot ρ)

theorem relativeEntropyEntanglementReal_nonneg (ρ : Density (A × B)) :
    0 ≤ relativeEntropyEntanglementReal ρ :=
  EReal.toReal_nonneg (relativeEntropyEntanglementNat_nonneg ρ)

theorem relativeEntropyEntanglementNat_eq_zero_of_separable (ρ : Density (A × B))
    (hρ : IsSeparable ρ.matrix) : relativeEntropyEntanglementNat ρ = 0 := by
  apply le_antisymm
  · simpa only [umegakiNats_self] using relativeEntropyEntanglementNat_le ρ ρ hρ
  · exact relativeEntropyEntanglementNat_nonneg ρ

theorem exists_separable_near (ρ : Density (A × B)) {ε : ℝ} (hε : 0 < ε) :
    ∃ σ : SeparableDensity A B,
      umegakiNats ρ.matrix σ.val.matrix < (relativeEntropyEntanglementReal ρ + ε : ℝ) := by
  have hlt : relativeEntropyEntanglementNat ρ <
      (relativeEntropyEntanglementReal ρ + ε : ℝ) := by
    rw [← coe_relativeEntropyEntanglementReal]
    exact_mod_cast (lt_add_of_pos_right (relativeEntropyEntanglementReal ρ) hε)
  exact iInf_lt_iff.mp hlt

def densityReindex (e : I ≃ J) (ρ : Density I) : Density J where
  matrix := Matrix.reindex e e ρ.matrix
  positive := ρ.positive.submatrix e.symm
  trace_one := (QuantumProver.QuantumEntropy.trace_reindex e ρ.matrix).trans ρ.trace_one

abbrev CopyIndex (A : Type*) (n : ℕ) := QuantumProver.SuperchannelDiscrimination.TensorEntropy.TensorIndex A n

def copyGrouping (A B : Type*) : (n : ℕ) →
    QuantumProver.SuperchannelDiscrimination.TensorEntropy.TensorIndex (A × B) n ≃ CopyIndex A n × CopyIndex B n
  | 0 => {
      toFun := fun _ => (PUnit.unit, PUnit.unit)
      invFun := fun _ => PUnit.unit
      left_inv := by intro x; cases x; rfl
      right_inv := by rintro ⟨x,y⟩; cases x; cases y; rfl }
  | n + 1 => (Equiv.prodCongr (copyGrouping A B n) (Equiv.refl (A × B))).trans
      (Equiv.prodProdProdComm (CopyIndex A n) (CopyIndex B n) A B)

def matrixTensorPowerDensity (ρ : Density I) (n : ℕ) : Density (QuantumProver.SuperchannelDiscrimination.TensorEntropy.TensorIndex I n) where
  matrix := QuantumProver.SuperchannelDiscrimination.TensorEntropy.tensorPower ρ.matrix n
  positive := (QuantumProver.SuperchannelDiscrimination.TensorEntropy.tensorPower_isDensity (density_matrix ρ) n).1
  trace_one := (QuantumProver.SuperchannelDiscrimination.TensorEntropy.tensorPower_isDensity (density_matrix ρ) n).2

def tensorCopies (ρ : Density (A × B)) (n : ℕ) : Density (CopyIndex A n × CopyIndex B n) :=
  densityReindex (copyGrouping A B n) (matrixTensorPowerDensity ρ n)

theorem tensorCopies_matrix (ρ : Density (A × B)) (n : ℕ) :
    (tensorCopies ρ n).matrix = Matrix.reindex (copyGrouping A B n)
      (copyGrouping A B n) (QuantumProver.SuperchannelDiscrimination.TensorEntropy.tensorPower ρ.matrix n) := rfl

theorem umegakiNats_reindex (e : I ≃ J) {R S : QMatrix I}
    (hR : R.PosSemidef) (hS : S.PosSemidef) :
    umegakiNats (Matrix.reindex e e R) (Matrix.reindex e e S) = umegakiNats R S := by
  have inv (X : QMatrix I) :
      (QuantumProver.SuperchannelDiscrimination.CPWrappers.reindexChannel e.symm).map
        ((QuantumProver.SuperchannelDiscrimination.CPWrappers.reindexChannel e).map X) = X := by
    ext i j
    change X (e.symm (e i)) (e.symm (e j)) = X i j
    simp only [Equiv.symm_apply_apply]
  have heq : QuantumProver.SuperchannelDiscrimination.FlaggedStates.relativeEntropyBits
      (Matrix.reindex e e R) (Matrix.reindex e e S) =
      QuantumProver.SuperchannelDiscrimination.FlaggedStates.relativeEntropyBits R S := by
    apply le_antisymm
    · exact QuantumProver.SuperchannelDiscrimination.AbstractDPI.relativeEntropyBits_cptp_dpi
        (QuantumProver.SuperchannelDiscrimination.CPWrappers.reindexChannel e) hR hS
    · have h := QuantumProver.SuperchannelDiscrimination.AbstractDPI.relativeEntropyBits_cptp_dpi
        (QuantumProver.SuperchannelDiscrimination.CPWrappers.reindexChannel e.symm)
        (hR.submatrix e.symm) (hS.submatrix e.symm)
      change QuantumProver.SuperchannelDiscrimination.FlaggedStates.relativeEntropyBits
        ((QuantumProver.SuperchannelDiscrimination.CPWrappers.reindexChannel e.symm).map
          ((QuantumProver.SuperchannelDiscrimination.CPWrappers.reindexChannel e).map R))
        ((QuantumProver.SuperchannelDiscrimination.CPWrappers.reindexChannel e.symm).map
          ((QuantumProver.SuperchannelDiscrimination.CPWrappers.reindexChannel e).map S)) ≤ _ at h
      rw [inv, inv] at h
      exact h
  exact congrArg (fun x : EReal => x * (Real.log 2 : EReal)) heq

theorem isSeparable_map_of_products
    (L : QMatrix (A × B) →ₗ[ℝ] QMatrix (C × D))
    (hL : ∀ a : Density A, ∀ b : Density B,
      IsSeparable (L (a.matrix ⊗ₖ b.matrix)))
    {R : QMatrix (A × B)} (hR : IsSeparable R) : IsSeparable (L R) := by
  let T : Set (QMatrix (A × B)) := {R | IsSeparable (L R)}
  have hconv : Convex ℝ T := by
    exact (convex_convexHull ℝ _).linear_preimage L
  have hbase : {R : QMatrix (A × B) |
      ∃ a : Density A, ∃ b : Density B, R = a.matrix ⊗ₖ b.matrix} ⊆ T := by
    rintro R ⟨a,b,rfl⟩
    exact hL a b
  exact (convexHull_min hbase hconv) hR

def bipartiteTensorMatrix (R : QMatrix (A × B)) (S : QMatrix (C × D)) :
    QMatrix ((A × C) × (B × D)) :=
  Matrix.reindex (Equiv.prodProdProdComm A B C D)
    (Equiv.prodProdProdComm A B C D) (R ⊗ₖ S)

def bipartiteTensorDensity (ρ : Density (A × B)) (τ : Density (C × D)) :
    Density ((A × C) × (B × D)) :=
  densityReindex (Equiv.prodProdProdComm A B C D) (productDensity ρ τ)

private def tensorWithRight (S : QMatrix (C × D)) :
    QMatrix (A × B) →ₗ[ℝ] QMatrix ((A × C) × (B × D)) :=
  (Matrix.reindexLinearEquiv ℝ ℂ (Equiv.prodProdProdComm A B C D)
    (Equiv.prodProdProdComm A B C D)).toLinearMap.comp
      ((Matrix.kroneckerBilinear : QMatrix (A × B) →ₗ[ℝ]
        QMatrix (C × D) →ₗ[ℝ] QMatrix ((A × B) × (C × D))).flip S)

private def tensorWithLeft (R : QMatrix (A × B)) :
    QMatrix (C × D) →ₗ[ℝ] QMatrix ((A × C) × (B × D)) :=
  (Matrix.reindexLinearEquiv ℝ ℂ (Equiv.prodProdProdComm A B C D)
    (Equiv.prodProdProdComm A B C D)).toLinearMap.comp
      ((Matrix.kroneckerBilinear : QMatrix (A × B) →ₗ[ℝ]
        QMatrix (C × D) →ₗ[ℝ] QMatrix ((A × B) × (C × D))) R)

theorem bipartiteTensorMatrix_products (a : QMatrix A) (b : QMatrix B)
    (c : QMatrix C) (d : QMatrix D) :
    bipartiteTensorMatrix (a ⊗ₖ b) (c ⊗ₖ d) = (a ⊗ₖ c) ⊗ₖ (b ⊗ₖ d) := by
  ext i j
  change (a i.1.1 j.1.1 * b i.2.1 j.2.1) *
    (c i.1.2 j.1.2 * d i.2.2 j.2.2) =
    (a i.1.1 j.1.1 * c i.1.2 j.1.2) * (b i.2.1 j.2.1 * d i.2.2 j.2.2)
  ring

theorem bipartiteTensorMatrix_separable {R : QMatrix (A × B)} {S : QMatrix (C × D)}
    (hR : IsSeparable R) (hS : IsSeparable S) :
    IsSeparable (bipartiteTensorMatrix R S) := by
  apply isSeparable_map_of_products (tensorWithRight S) _ hR
  intro a b
  apply isSeparable_map_of_products (tensorWithLeft (a.matrix ⊗ₖ b.matrix)) _ hS
  intro c d
  change IsSeparable (bipartiteTensorMatrix (a.matrix ⊗ₖ b.matrix) (c.matrix ⊗ₖ d.matrix))
  rw [bipartiteTensorMatrix_products]
  exact productDensity_separable (productDensity a c) (productDensity b d)

theorem umegakiNats_bipartiteTensor (ρ σ : Density (A × B))
    (τ γ : Density (C × D)) :
    umegakiNats (bipartiteTensorDensity ρ τ).matrix
      (bipartiteTensorDensity σ γ).matrix =
      umegakiNats ρ.matrix σ.matrix + umegakiNats τ.matrix γ.matrix := by
  change umegakiNats
    (Matrix.reindex (Equiv.prodProdProdComm A B C D) _ (ρ.matrix ⊗ₖ τ.matrix))
    (Matrix.reindex (Equiv.prodProdProdComm A B C D) _ (σ.matrix ⊗ₖ γ.matrix)) = _
  rw [umegakiNats_reindex _ (ρ.positive.kronecker τ.positive)
    (σ.positive.kronecker γ.positive), umegakiNats,
    QuantumProver.SuperchannelDiscrimination.TensorEntropy.relativeEntropyBits_kronecker
      (density_matrix ρ) σ.positive (density_matrix τ) γ.positive]
  exact EReal.right_distrib_of_nonneg
    (QuantumProver.SuperchannelDiscrimination.Klein.relativeEntropyBits_nonneg
      (density_matrix ρ) (density_matrix σ))
    (QuantumProver.SuperchannelDiscrimination.Klein.relativeEntropyBits_nonneg
      (density_matrix τ) (density_matrix γ))

theorem relativeEntropyEntanglementReal_tensor_subadditive
    (ρ : Density (A × B)) (τ : Density (C × D)) :
    relativeEntropyEntanglementReal (bipartiteTensorDensity ρ τ) ≤
      relativeEntropyEntanglementReal ρ + relativeEntropyEntanglementReal τ := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨σ,hσ⟩ := exists_separable_near ρ (half_pos hε)
  obtain ⟨γ,hγ⟩ := exists_separable_near τ (half_pos hε)
  have hle := relativeEntropyEntanglementNat_le (bipartiteTensorDensity ρ τ)
    (bipartiteTensorDensity σ.val γ.val)
    (bipartiteTensorMatrix_separable σ.property γ.property)
  rw [umegakiNats_bipartiteTensor] at hle
  have hlt := hle.trans_lt (EReal.add_lt_add hσ hγ)
  rw [← coe_relativeEntropyEntanglementReal, ← EReal.coe_add] at hlt
  have h : relativeEntropyEntanglementReal (bipartiteTensorDensity ρ τ) <
      (relativeEntropyEntanglementReal ρ + ε / 2) +
        (relativeEntropyEntanglementReal τ + ε / 2) := by exact_mod_cast hlt
  linarith

private def matrixChannel (Φ : CPTP I J) :
    QuantumProver.SuperchannelDiscrimination.KrausCompletion.FiniteCPTP I J where
  map := Φ.map
  completelyPositive :=
    (QuantumProver.SuperchannelDiscrimination.CPTPKraus.completelyPositive_iff_EJMCP _).mpr
      Φ.completelyPositive
  tracePreserving := Φ.tracePreserving

private def fromMatrixChannel
    (Φ : QuantumProver.SuperchannelDiscrimination.KrausCompletion.FiniteCPTP I J) : CPTP I J where
  map := Φ.map
  completelyPositive :=
    (QuantumProver.SuperchannelDiscrimination.CPTPKraus.completelyPositive_iff_EJMCP _).mp
      Φ.completelyPositive
  tracePreserving := Φ.tracePreserving

theorem umegakiNats_channel_mono (Φ : CPTP I J) (ρ σ : Density I) :
    umegakiNats (Φ.onDensity ρ).matrix (Φ.onDensity σ).matrix ≤
      umegakiNats ρ.matrix σ.matrix :=
  mul_le_mul_of_nonneg_right
    (QuantumProver.SuperchannelDiscrimination.AbstractDPI.relativeEntropyBits_cptp_dpi
      (matrixChannel Φ) ρ.positive σ.positive)
    (EReal.coe_nonneg.mpr (le_of_lt (Real.log_pos (by norm_num))))

theorem relativeEntropyEntanglementNat_channel_mono
    (Φ : CPTP (A × B) (C × D))
    (hsep : ∀ σ : SeparableDensity A B, IsSeparable (Φ.onDensity σ.val).matrix)
    (ρ : Density (A × B)) :
    relativeEntropyEntanglementNat (Φ.onDensity ρ) ≤ relativeEntropyEntanglementNat ρ := by
  apply le_iInf
  intro σ
  exact (relativeEntropyEntanglementNat_le _ _ (hsep σ)).trans
    (umegakiNats_channel_mono Φ ρ σ.val)

theorem relativeEntropyEntanglementReal_channel_mono
    (Φ : CPTP (A × B) (C × D))
    (hsep : ∀ σ : SeparableDensity A B, IsSeparable (Φ.onDensity σ.val).matrix)
    (ρ : Density (A × B)) :
    relativeEntropyEntanglementReal (Φ.onDensity ρ) ≤ relativeEntropyEntanglementReal ρ := by
  have h := relativeEntropyEntanglementNat_channel_mono Φ hsep ρ
  rw [← coe_relativeEntropyEntanglementReal, ← coe_relativeEntropyEntanglementReal] at h
  exact_mod_cast h

def localRightChannel (Φ : CPTP B D) : CPTP (A × B) (A × D) :=
  fromMatrixChannel
    (QuantumProver.SuperchannelDiscrimination.CPWrappers.amplifiedLeftChannel (matrixChannel Φ) A)

def localLeftChannel (Φ : CPTP A C) : CPTP (A × B) (C × B) :=
  fromMatrixChannel
    (QuantumProver.SuperchannelDiscrimination.CPWrappers.amplifiedChannel (matrixChannel Φ) B)

theorem localRightChannel_product (Φ : CPTP B D) (a : Density A) (b : Density B) :
    (localRightChannel (A := A) Φ).map (a.matrix ⊗ₖ b.matrix) =
      a.matrix ⊗ₖ (Φ.onDensity b).matrix := by
  ext i j
  change (Φ.map ((a.matrix i.1 j.1 : ℂ) • b.matrix)) i.2 j.2 =
    a.matrix i.1 j.1 * (Φ.map b.matrix) i.2 j.2
  rw [map_smul]
  rfl

theorem localLeftChannel_product (Φ : CPTP A C) (a : Density A) (b : Density B) :
    (localLeftChannel (B := B) Φ).map (a.matrix ⊗ₖ b.matrix) =
      (Φ.onDensity a).matrix ⊗ₖ b.matrix := by
  ext i j
  have hslice : (fun a₁ a₂ : A => a.matrix a₁ a₂ * b.matrix i.2 j.2) =
      (b.matrix i.2 j.2 : ℂ) • a.matrix := by
    ext a₁ a₂
    exact mul_comm _ _
  change (Φ.map (fun a₁ a₂ : A => a.matrix a₁ a₂ * b.matrix i.2 j.2)) i.1 j.1 =
    (Φ.map a.matrix) i.1 j.1 * b.matrix i.2 j.2
  rw [hslice, map_smul]
  exact mul_comm _ _

theorem localRightChannel_preserves_separable (Φ : CPTP B D) {R : QMatrix (A × B)}
    (hR : IsSeparable R) : IsSeparable ((localRightChannel (A := A) Φ).map R) := by
  apply isSeparable_map_of_products
    ((localRightChannel (A := A) Φ).map.restrictScalars ℝ) _ hR
  intro a b
  change IsSeparable ((localRightChannel (A := A) Φ).map (a.matrix ⊗ₖ b.matrix))
  rw [localRightChannel_product]
  exact productDensity_separable a (Φ.onDensity b)

theorem localLeftChannel_preserves_separable (Φ : CPTP A C) {R : QMatrix (A × B)}
    (hR : IsSeparable R) : IsSeparable ((localLeftChannel (B := B) Φ).map R) := by
  apply isSeparable_map_of_products
    ((localLeftChannel (B := B) Φ).map.restrictScalars ℝ) _ hR
  intro a b
  change IsSeparable ((localLeftChannel (B := B) Φ).map (a.matrix ⊗ₖ b.matrix))
  rw [localLeftChannel_product]
  exact productDensity_separable (Φ.onDensity a) b

theorem relativeEntropyEntanglementNat_localRight_mono (Φ : CPTP B D)
    (ρ : Density (A × B)) :
    relativeEntropyEntanglementNat ((localRightChannel (A := A) Φ).onDensity ρ) ≤
      relativeEntropyEntanglementNat ρ :=
  relativeEntropyEntanglementNat_channel_mono _
    (fun σ => localRightChannel_preserves_separable Φ σ.property) ρ

theorem relativeEntropyEntanglementNat_localLeft_mono (Φ : CPTP A C)
    (ρ : Density (A × B)) :
    relativeEntropyEntanglementNat ((localLeftChannel (B := B) Φ).onDensity ρ) ≤
      relativeEntropyEntanglementNat ρ :=
  relativeEntropyEntanglementNat_channel_mono _
    (fun σ => localLeftChannel_preserves_separable Φ σ.property) ρ

theorem isSeparable_reindex (eA : A ≃ C) (eB : B ≃ D) {R : QMatrix (A × B)}
    (hR : IsSeparable R) :
    IsSeparable (Matrix.reindex (Equiv.prodCongr eA eB) (Equiv.prodCongr eA eB) R) := by
  apply isSeparable_map_of_products
    (Matrix.reindexLinearEquiv ℝ ℂ (Equiv.prodCongr eA eB)
      (Equiv.prodCongr eA eB)).toLinearMap _ hR
  intro a b
  exact productDensity_separable (densityReindex eA a) (densityReindex eB b)

theorem density_ext (ρ σ : Density I) (h : ρ.matrix = σ.matrix) : ρ = σ := by
  cases ρ
  cases σ
  cases h
  rfl

theorem densityReindex_symm (e : I ≃ J) (ρ : Density I) :
    densityReindex e.symm (densityReindex e ρ) = ρ := by
  apply density_ext
  ext i j
  change ρ.matrix (e.symm (e i)) (e.symm (e j)) = ρ.matrix i j
  simp only [Equiv.symm_apply_apply]

private theorem relativeEntropyEntanglementNat_reindex_le
    (eA : A ≃ C) (eB : B ≃ D) (ρ : Density (A × B)) :
    relativeEntropyEntanglementNat (densityReindex (Equiv.prodCongr eA eB) ρ) ≤
      relativeEntropyEntanglementNat ρ := by
  apply le_iInf
  intro σ
  refine (relativeEntropyEntanglementNat_le _
    (densityReindex (Equiv.prodCongr eA eB) σ.val)
    (isSeparable_reindex eA eB σ.property)).trans ?_
  exact (umegakiNats_reindex _ ρ.positive σ.val.positive).le

theorem relativeEntropyEntanglementNat_reindex
    (eA : A ≃ C) (eB : B ≃ D) (ρ : Density (A × B)) :
    relativeEntropyEntanglementNat (densityReindex (Equiv.prodCongr eA eB) ρ) =
      relativeEntropyEntanglementNat ρ := by
  apply le_antisymm (relativeEntropyEntanglementNat_reindex_le eA eB ρ)
  have h := relativeEntropyEntanglementNat_reindex_le eA.symm eB.symm
    (densityReindex (Equiv.prodCongr eA eB) ρ)
  have he : Equiv.prodCongr eA.symm eB.symm = (Equiv.prodCongr eA eB).symm := rfl
  rw [he, densityReindex_symm] at h
  exact h

theorem relativeEntropyEntanglementReal_reindex
    (eA : A ≃ C) (eB : B ≃ D) (ρ : Density (A × B)) :
    relativeEntropyEntanglementReal (densityReindex (Equiv.prodCongr eA eB) ρ) =
      relativeEntropyEntanglementReal ρ :=
  congrArg EReal.toReal (relativeEntropyEntanglementNat_reindex eA eB ρ)

end QuantumProver.DepolarizingSquashedEntanglement.BCYRelativeEntropy

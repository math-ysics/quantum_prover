import QuantumProver.InformationTheory.SuperchannelDiscrimination.ChannelEntropyChain

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
open Matrix Filter
open scoped BigOperators Topology ComplexOrder MatrixOrder Matrix Kronecker

namespace QuantumProver.SuperchannelDiscrimination.ChannelAmortization

open FlaggedStates TensorEntropy ChannelRegularization KrausCompletion CPWrappers

universe u
variable {I O R A B : Type u} [Fintype I] [Fintype O] [Fintype R] [Fintype A] [Fintype B]
  [DecidableEq I] [DecidableEq O] [DecidableEq R] [DecidableEq A] [DecidableEq B]

def exchangeReference (A B R : Type*) : A × (B × R) ≃ B × (A × R) where
  toFun x := (x.2.1, (x.1, x.2.2))
  invFun x := (x.2.1, (x.1, x.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

def outputOrder (A B R : Type*) : ((A × B) × R) ≃ B × (A × R) :=
  (Equiv.prodAssoc A B R).trans (exchangeReference A B R)

theorem associate_product (X : Matrix A A ℂ) (Y : Matrix I I ℂ) (Z : Matrix R R ℂ) :
    reindexMap (Equiv.prodAssoc A I R) ((X ⊗ₖ Y) ⊗ₖ Z) = X ⊗ₖ (Y ⊗ₖ Z) := by
  ext ⟨a, i, r⟩ ⟨b, j, s⟩
  simp only [reindexMap_apply, Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.prodAssoc_symm_apply, Matrix.kronecker_apply]
  ring

theorem exchange_product (X : Matrix A A ℂ) (Y : Matrix I I ℂ) (Z : Matrix R R ℂ) :
    reindexMap (exchangeReference A I R) (X ⊗ₖ (Y ⊗ₖ Z)) = Y ⊗ₖ (X ⊗ₖ Z) := by
  ext ⟨i, a, r⟩ ⟨j, b, s⟩
  change X a b * (Y i j * Z r s) = Y i j * (X a b * Z r s)
  ring

theorem outputOrder_product (X : Matrix A A ℂ) (Y : Matrix I I ℂ) (Z : Matrix R R ℂ) :
    reindexMap (outputOrder A I R) ((X ⊗ₖ Y) ⊗ₖ Z) = Y ⊗ₖ (X ⊗ₖ Z) := by
  change reindexMap (exchangeReference A I R)
    (reindexMap (Equiv.prodAssoc A I R) ((X ⊗ₖ Y) ⊗ₖ Z)) = _
  rw [associate_product, exchange_product]

theorem amplifyMap_product_action (Φ : FiniteCPTP I O)
    (X : Matrix I I ℂ) (Y : Matrix R R ℂ) :
    amplifyMap Φ.map R (X ⊗ₖ Y) = Φ.map X ⊗ₖ Y := amplify_product_action Φ X Y

theorem tensor_reference_sequential (Φ : FiniteCPTP A B) (Ψ : FiniteCPTP I O)
    (R : Type u) [Fintype R] [DecidableEq R]
    (X : Matrix ((A × I) × R) ((A × I) × R) ℂ) :
    CPTPKraus.amplify Ψ.map (B × R)
      (reindexMap (exchangeReference B I R)
        (CPTPKraus.amplify Φ.map (I × R)
          (reindexMap (Equiv.prodAssoc A I R) X))) =
      reindexMap (outputOrder B O R)
        (CPTPKraus.amplify (tensorChannel Φ Ψ).map R X) := by
  let L := (amplifyMap Ψ.map (B × R)).comp
    ((reindexMap (exchangeReference B I R)).comp
      ((amplifyMap Φ.map (I × R)).comp (reindexMap (Equiv.prodAssoc A I R))))
  let G := (reindexMap (outputOrder B O R)).comp
    (amplifyMap (tensorChannel Φ Ψ).map R)
  have h : L = G := by
    apply matrixMap_ext_units
    intro ⟨⟨a, i⟩, r⟩ ⟨⟨a', i'⟩, r'⟩
    have hunit : Matrix.single ((a, i), r) ((a', i'), r') (1 : ℂ) =
        (Matrix.single a a' 1 ⊗ₖ Matrix.single i i' 1) ⊗ₖ Matrix.single r r' 1 := by
      simp only [Matrix.single_kronecker_single, one_mul]
    simp only [L, G, LinearMap.comp_apply]
    rw [hunit, associate_product, amplifyMap_product_action Φ,
      exchange_product, amplifyMap_product_action Ψ,
      amplifyMap_product_action (tensorChannel Φ Ψ), tensorChannel_map_product,
      outputOrder_product]
  exact congrArg (fun F => F X) h

theorem reference_increment_from_fin (Φ Ψ : FiniteCPTP I O) (budget : ℝ)
    (hstep : ∀ (k : ℕ) (ρ σ : Matrix (I × Fin k) (I × Fin k) ℂ),
      IsDensity ρ → IsDensity σ → ∀ cost : ℝ,
      relativeEntropyBits ρ σ ≤ (cost : EReal) →
      relativeEntropyBits (CPTPKraus.amplify Φ.map (Fin k) ρ)
        (CPTPKraus.amplify Ψ.map (Fin k) σ) ≤ ((budget + cost : ℝ) : EReal))
    (R : Type u) [Fintype R] [DecidableEq R]
    {ρ σ : Matrix (I × R) (I × R) ℂ} (hρ : IsDensity ρ) (hσ : IsDensity σ)
    {cost : ℝ} (hInput : relativeEntropyBits ρ σ ≤ (cost : EReal)) :
    relativeEntropyBits (CPTPKraus.amplify Φ.map R ρ) (CPTPKraus.amplify Ψ.map R σ) ≤
      ((budget + cost : ℝ) : EReal) := by
  let e : R ≃ Fin (Fintype.card R) := Fintype.equivFin R
  let ei := Equiv.prodCongr (Equiv.refl I) e
  let eo := Equiv.prodCongr (Equiv.refl O) e
  let ρf := reindexMap ei ρ
  let σf := reindexMap ei σ
  have hρf : IsDensity ρf := channel_density (reindexChannel ei) hρ.1 hρ.2
  have hσf : IsDensity σf := channel_density (reindexChannel ei) hσ.1 hσ.2
  have hcost : relativeEntropyBits ρf σf ≤ (cost : EReal) := by
    change relativeEntropyBits (Matrix.reindex ei ei ρ) (Matrix.reindex ei ei σ) ≤ _
    rw [relativeEntropyBits_reindex ei hρ.1 hσ.1]
    exact hInput
  have h := hstep (Fintype.card R) ρf σf hρf hσf cost hcost
  change relativeEntropyBits
    (amplify Φ.map (Fin (Fintype.card R)) (Matrix.reindex ei ei ρ))
    (amplify Ψ.map (Fin (Fintype.card R)) (Matrix.reindex ei ei σ)) ≤ _ at h
  rw [amplify_reindex_reference, amplify_reindex_reference] at h
  have hΦ : (amplify Φ.map R ρ).PosSemidef :=
    (channel_density (amplifiedChannel Φ R) hρ.1 hρ.2).1
  have hΨ : (amplify Ψ.map R σ).PosSemidef :=
    (channel_density (amplifiedChannel Ψ R) hσ.1 hσ.2).1
  rw [relativeEntropyBits_reindex eo hΦ hΨ] at h
  exact h

theorem channelPower_increment_le (Φ Ψ : FiniteCPTP I O) (budget : ℝ)
    (hstep : ∀ (k : ℕ) (ρ σ : Matrix (I × Fin k) (I × Fin k) ℂ),
      IsDensity ρ → IsDensity σ → ∀ cost : ℝ,
      relativeEntropyBits ρ σ ≤ (cost : EReal) →
      relativeEntropyBits (CPTPKraus.amplify Φ.map (Fin k) ρ)
        (CPTPKraus.amplify Ψ.map (Fin k) σ) ≤ ((budget + cost : ℝ) : EReal)) :
    ∀ (n : ℕ) (R : Type u) [Fintype R] [DecidableEq R]
      (ρ σ : Matrix (TensorIndex I n × R) (TensorIndex I n × R) ℂ),
      IsDensity ρ → IsDensity σ → ∀ cost : ℝ,
      relativeEntropyBits ρ σ ≤ (cost : EReal) →
      relativeEntropyBits (CPTPKraus.amplify (channelPower Φ n).map R ρ)
        (CPTPKraus.amplify (channelPower Ψ n).map R σ) ≤
          (((n : ℝ) * budget + cost : ℝ) : EReal) := by
  intro n
  induction n with
  | zero =>
      intro R _ _ ρ σ hρ hσ cost hInput
      have h := AbstractDPI.relativeEntropyBits_cptp_dpi
        (amplifiedChannel (channelPower Φ 0) R) hρ.1 hσ.1
      exact h.trans (by simpa only [Nat.cast_zero, zero_mul, zero_add] using hInput)
  | succ n ih =>
      intro R _ _ ρ σ hρ hσ cost hInput
      let ei := Equiv.prodAssoc (TensorIndex I n) I R
      let em := exchangeReference (TensorIndex O n) I R
      let eo := outputOrder (TensorIndex O n) O R
      let ρ₀ := reindexMap ei ρ
      let σ₀ := reindexMap ei σ
      have hρ₀ : IsDensity ρ₀ := channel_density (reindexChannel ei) hρ.1 hρ.2
      have hσ₀ : IsDensity σ₀ := channel_density (reindexChannel ei) hσ.1 hσ.2
      have hc₀ : relativeEntropyBits ρ₀ σ₀ ≤ (cost : EReal) := by
        change relativeEntropyBits (Matrix.reindex ei ei ρ) (Matrix.reindex ei ei σ) ≤ _
        rw [relativeEntropyBits_reindex ei hρ.1 hσ.1]
        exact hInput
      let ρ₁ := CPTPKraus.amplify (channelPower Φ n).map (I × R) ρ₀
      let σ₁ := CPTPKraus.amplify (channelPower Ψ n).map (I × R) σ₀
      have hρ₁ : IsDensity ρ₁ := channel_density
        (amplifiedChannel (channelPower Φ n) (I × R)) hρ₀.1 hρ₀.2
      have hσ₁ : IsDensity σ₁ := channel_density
        (amplifiedChannel (channelPower Ψ n) (I × R)) hσ₀.1 hσ₀.2
      have hc₁ : relativeEntropyBits ρ₁ σ₁ ≤ (((n : ℝ) * budget + cost : ℝ) : EReal) :=
        ih (I × R) ρ₀ σ₀ hρ₀ hσ₀ cost hc₀
      let ρ₂ := reindexMap em ρ₁
      let σ₂ := reindexMap em σ₁
      have hρ₂ : IsDensity ρ₂ := channel_density (reindexChannel em) hρ₁.1 hρ₁.2
      have hσ₂ : IsDensity σ₂ := channel_density (reindexChannel em) hσ₁.1 hσ₁.2
      have hc₂ : relativeEntropyBits ρ₂ σ₂ ≤ (((n : ℝ) * budget + cost : ℝ) : EReal) := by
        change relativeEntropyBits (Matrix.reindex em em ρ₁) (Matrix.reindex em em σ₁) ≤ _
        rw [relativeEntropyBits_reindex em hρ₁.1 hσ₁.1]
        exact hc₁
      have hout := reference_increment_from_fin Φ Ψ budget hstep (TensorIndex O n × R)
        hρ₂ hσ₂ hc₂
      have hΦseq := tensor_reference_sequential (channelPower Φ n) Φ R ρ
      have hΨseq := tensor_reference_sequential (channelPower Ψ n) Ψ R σ
      change relativeEntropyBits
        (CPTPKraus.amplify Φ.map (TensorIndex O n × R)
          (reindexMap em (CPTPKraus.amplify (channelPower Φ n).map (I × R) (reindexMap ei ρ))))
        (CPTPKraus.amplify Ψ.map (TensorIndex O n × R)
          (reindexMap em (CPTPKraus.amplify (channelPower Ψ n).map (I × R) (reindexMap ei σ)))) ≤ _ at hout
      rw [hΦseq, hΨseq] at hout
      have hΦout : (CPTPKraus.amplify (tensorChannel (channelPower Φ n) Φ).map R ρ).PosSemidef :=
        (channel_density (amplifiedChannel (tensorChannel (channelPower Φ n) Φ) R) hρ.1 hρ.2).1
      have hΨout : (CPTPKraus.amplify (tensorChannel (channelPower Ψ n) Ψ).map R σ).PosSemidef :=
        (channel_density (amplifiedChannel (tensorChannel (channelPower Ψ n) Ψ) R) hσ.1 hσ.2).1
      change relativeEntropyBits
        (Matrix.reindex eo eo (CPTPKraus.amplify (tensorChannel (channelPower Φ n) Φ).map R ρ))
        (Matrix.reindex eo eo (CPTPKraus.amplify (tensorChannel (channelPower Ψ n) Ψ).map R σ)) ≤ _ at hout
      rw [relativeEntropyBits_reindex eo hΦout hΨout] at hout
      have hs : budget + ((n : ℝ) * budget + cost) = ((n + 1 : ℕ) : ℝ) * budget + cost := by
        push_cast
        ring
      rwa [hs] at hout

theorem powerValue_le_of_reference_increment (Φ Ψ : FiniteCPTP I O) (budget : ℝ)
    (hstep : ∀ (k : ℕ) (ρ σ : Matrix (I × Fin k) (I × Fin k) ℂ),
      IsDensity ρ → IsDensity σ → ∀ cost : ℝ,
      relativeEntropyBits ρ σ ≤ (cost : EReal) →
      relativeEntropyBits (CPTPKraus.amplify Φ.map (Fin k) ρ)
        (CPTPKraus.amplify Ψ.map (Fin k) σ) ≤ ((budget + cost : ℝ) : EReal))
    (n : ℕ) : powerValue Φ Ψ n ≤ (((n : ℝ) * budget : ℝ) : EReal) := by
  refine iSup_le fun k => iSup_le fun ρ => iSup_le fun hρ => ?_
  let e : Fin k ≃ ULift.{u} (Fin k) := Equiv.ulift.symm
  let ei := Equiv.prodCongr (Equiv.refl (TensorIndex I n)) e
  let eo := Equiv.prodCongr (Equiv.refl (TensorIndex O n)) e
  let ρl := reindexMap ei ρ
  have hρl : IsDensity ρl := channel_density (reindexChannel ei) hρ.1 hρ.2
  have h := channelPower_increment_le Φ Ψ budget hstep n (ULift.{u} (Fin k)) ρl ρl hρl hρl 0
    (by simp only [ChannelRegularization.relativeEntropyBits_self, EReal.coe_zero, le_rfl])
  rw [add_zero] at h
  change relativeEntropyBits
    (amplify (channelPower Φ n).map (ULift.{u} (Fin k)) (Matrix.reindex ei ei ρ))
    (amplify (channelPower Ψ n).map (ULift.{u} (Fin k)) (Matrix.reindex ei ei ρ)) ≤ _ at h
  rw [amplify_reindex_reference, amplify_reindex_reference] at h
  have hΦ : (amplify (channelPower Φ n).map (Fin k) ρ).PosSemidef :=
    (channel_density (amplifiedChannel (channelPower Φ n) (Fin k)) hρ.1 hρ.2).1
  have hΨ : (amplify (channelPower Ψ n).map (Fin k) ρ).PosSemidef :=
    (channel_density (amplifiedChannel (channelPower Ψ n) (Fin k)) hρ.1 hρ.2).1
  rw [relativeEntropyBits_reindex eo hΦ hΨ] at h
  exact h

theorem regularized_le_of_reference_increment (Φ Ψ : FiniteCPTP I O) (budget : ℝ)
    (hstep : ∀ (k : ℕ) (ρ σ : Matrix (I × Fin k) (I × Fin k) ℂ),
      IsDensity ρ → IsDensity σ → ∀ cost : ℝ,
      relativeEntropyBits ρ σ ≤ (cost : EReal) →
      relativeEntropyBits (CPTPKraus.amplify Φ.map (Fin k) ρ)
        (CPTPKraus.amplify Ψ.map (Fin k) σ) ≤ ((budget + cost : ℝ) : EReal)) :
    regularizedRelativeEntropyBits Φ Ψ ≤ (budget : EReal) := by
  refine iSup_le fun n => ?_
  have hpower := powerValue_le_of_reference_increment Φ Ψ budget hstep (n + 1)
  have h := mul_le_mul_of_nonneg_left hpower
    (EReal.coe_nonneg.mpr (inv_nonneg.mpr (Nat.cast_nonneg (n + 1) : (0 : ℝ) ≤ _)))
  have hn : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  change normalizedPowerValue Φ Ψ (n + 1) ≤ _
  change (((((n + 1 : ℕ) : ℝ)⁻¹ : ℝ) : EReal) * powerValue Φ Ψ (n + 1)) ≤ _
  calc
    _ ≤ (((((n + 1 : ℕ) : ℝ)⁻¹ : ℝ) : EReal) *
        (((((n + 1 : ℕ) : ℝ) * budget) : ℝ) : EReal)) := h
    _ = (budget : EReal) := by
      rw [← EReal.coe_mul]
      congr 1
      rw [← mul_assoc, inv_mul_cancel₀ hn, one_mul]

theorem regularized_le_of_state_increment (Φ Ψ : FiniteCPTP I O) (budget : ℝ)
    (hstep : ∀ (k : ℕ) (ρ σ : Matrix (I × Fin k) (I × Fin k) ℂ),
      IsDensity ρ → IsDensity σ →
      relativeEntropyBits (CPTPKraus.amplify Φ.map (Fin k) ρ)
        (CPTPKraus.amplify Ψ.map (Fin k) σ) ≤
          (budget : EReal) + relativeEntropyBits ρ σ) :
    regularizedRelativeEntropyBits Φ Ψ ≤ (budget : EReal) := by
  apply regularized_le_of_reference_increment Φ Ψ budget
  intro k ρ σ hρ hσ cost hInput
  have h := (hstep k ρ σ hρ hσ).trans (add_le_add le_rfl hInput)
  simpa only [← EReal.coe_add] using h

def amortizedRelativeEntropyBits (Φ Ψ : FiniteCPTP I O) : EReal :=
  ⨆ (k : ℕ) (ρ : Matrix (I × Fin k) (I × Fin k) ℂ)
    (σ : Matrix (I × Fin k) (I × Fin k) ℂ)
    (_hρ : IsDensity ρ) (_hσ : IsDensity σ) (_hs : HasSupportIn ρ σ),
    relativeEntropyBits (CPTPKraus.amplify Φ.map (Fin k) ρ)
      (CPTPKraus.amplify Ψ.map (Fin k) σ) - (finiteRelativeEntropyBits ρ σ : EReal)

theorem amortized_witness_le (Φ Ψ : FiniteCPTP I O) (k : ℕ)
    {ρ σ : Matrix (I × Fin k) (I × Fin k) ℂ} (hρ : IsDensity ρ) (hσ : IsDensity σ)
    (hs : HasSupportIn ρ σ) :
    relativeEntropyBits (CPTPKraus.amplify Φ.map (Fin k) ρ)
      (CPTPKraus.amplify Ψ.map (Fin k) σ) - (finiteRelativeEntropyBits ρ σ : EReal) ≤
        amortizedRelativeEntropyBits Φ Ψ :=
  le_iSup_of_le k (le_iSup_of_le ρ (le_iSup_of_le σ
    (le_iSup_of_le hρ (le_iSup_of_le hσ (le_iSup_of_le hs le_rfl)))))

theorem amortized_nonneg (Φ Ψ : FiniteCPTP I O) [Nonempty I] :
    0 ≤ amortizedRelativeEntropyBits Φ Ψ := by
  classical
  let i : I := Classical.choice inferInstance
  let ρ : Matrix (I × Fin 1) (I × Fin 1) ℂ := Matrix.single (i, 0) (i, 0) 1
  have hρ : IsDensity ρ := single_isDensity _
  have hs : HasSupportIn ρ ρ := hasSupportIn_self _
  have hcost : finiteRelativeEntropyBits ρ ρ = 0 := by simp [finiteRelativeEntropyBits]
  have h := amortized_witness_le Φ Ψ 1 hρ hρ hs
  rw [hcost, EReal.coe_zero, sub_zero] at h
  exact (Klein.relativeEntropyBits_nonneg
    (channel_density (amplifiedChannel Φ (Fin 1)) hρ.1 hρ.2)
    (channel_density (amplifiedChannel Ψ (Fin 1)) hρ.1 hρ.2)).trans h

theorem amortized_le_regularized (Φ Ψ : FiniteCPTP I O) :
    amortizedRelativeEntropyBits Φ Ψ ≤ regularizedRelativeEntropyBits Φ Ψ := by
  refine iSup_le fun k => iSup_le fun ρ => iSup_le fun σ =>
    iSup_le fun hρ => iSup_le fun hσ => iSup_le fun hs => ?_
  have h := ChannelEntropyChain.channel_reference_relativeEntropy_chain Φ Ψ (Fin k) hρ hσ
  have hcost : relativeEntropyBits ρ σ = (finiteRelativeEntropyBits ρ σ : EReal) := by
    simp only [relativeEntropyBits, hs, ite_true]
  rw [hcost] at h
  exact EReal.sub_le_of_le_add h

theorem regularized_le_amortized (Φ Ψ : FiniteCPTP I O) [Nonempty I] :
    regularizedRelativeEntropyBits Φ Ψ ≤ amortizedRelativeEntropyBits Φ Ψ := by
  have hnb : amortizedRelativeEntropyBits Φ Ψ ≠ ⊥ :=
    ne_of_gt (EReal.bot_lt_zero.trans_le (amortized_nonneg Φ Ψ))
  cases hAm : amortizedRelativeEntropyBits Φ Ψ with
  | bot => exact False.elim (hnb hAm)
  | top => exact le_top
  | coe budget =>
      apply regularized_le_of_reference_increment Φ Ψ budget
      intro k ρ σ hρ hσ cost hInput
      have hs : HasSupportIn ρ σ := by
        by_contra hn
        have htop : (⊤ : EReal) ≤ (cost : EReal) := by
          simpa only [relativeEntropyBits, hn, ite_false] using hInput
        exact not_le_of_gt (EReal.coe_lt_top cost) htop
      have hcost : relativeEntropyBits ρ σ = (finiteRelativeEntropyBits ρ σ : EReal) := by
        simp only [relativeEntropyBits, hs, ite_true]
      have hg := (amortized_witness_le Φ Ψ k hρ hσ hs).trans (show
        amortizedRelativeEntropyBits Φ Ψ ≤ (budget : EReal) by rw [hAm])
      have hout := (EReal.sub_le_iff_le_add
        (.inl (EReal.coe_ne_bot (finiteRelativeEntropyBits ρ σ)))
        (.inl (EReal.coe_ne_top (finiteRelativeEntropyBits ρ σ)))).mp hg
      rw [← hcost] at hout
      have h := hout.trans (add_le_add le_rfl hInput)
      simpa only [← EReal.coe_add] using h

theorem amortized_eq_regularized (Φ Ψ : FiniteCPTP I O) [Nonempty I] :
    amortizedRelativeEntropyBits Φ Ψ = regularizedRelativeEntropyBits Φ Ψ :=
  le_antisymm (amortized_le_regularized Φ Ψ) (regularized_le_amortized Φ Ψ)

end QuantumProver.SuperchannelDiscrimination.ChannelAmortization

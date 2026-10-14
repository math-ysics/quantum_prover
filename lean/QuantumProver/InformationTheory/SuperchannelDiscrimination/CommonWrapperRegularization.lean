import QuantumProver.InformationTheory.SuperchannelDiscrimination.DiamondControl

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace QuantumProver.SuperchannelDiscrimination.ChannelRegularization

open Matrix KrausCompletion CPWrappers FlaggedStates TensorEntropy
open scoped BigOperators ComplexOrder MatrixOrder Matrix Kronecker Topology

variable {I O P C D J : Type*}
  [Fintype I] [Fintype O] [Fintype P] [Fintype C] [Fintype D] [Fintype J]
  [DecidableEq I] [DecidableEq O] [DecidableEq P]
  [DecidableEq C] [DecidableEq D] [DecidableEq J]

theorem stabilizedRelativeEntropyBits_postcompose (Φ Ψ : FiniteCPTP I O)
    (M : FiniteCPTP O P) :
    stabilizedRelativeEntropyBits (composeChannel M Φ) (composeChannel M Ψ) ≤
      stabilizedRelativeEntropyBits Φ Ψ := by
  refine iSup_le fun r => iSup_le fun ρ => iSup_le fun hρ => ?_
  have hΦρ := channel_density (amplifiedChannel Φ (Fin r)) hρ.1 hρ.2
  have hΨρ := channel_density (amplifiedChannel Ψ (Fin r)) hρ.1 hρ.2
  change relativeEntropyBits
      ((amplifiedChannel M (Fin r)).map (amplify Φ.map (Fin r) ρ))
      ((amplifiedChannel M (Fin r)).map (amplify Ψ.map (Fin r) ρ)) ≤ _
  exact (AbstractDPI.relativeEntropyBits_cptp_dpi
    (amplifiedChannel M (Fin r)) hΦρ.1 hΨρ.1).trans
      (stabilizedRelativeEntropyBits_witness_fin_le Φ Ψ r hρ)

theorem stabilizedRelativeEntropyBits_precompose (Φ Ψ : FiniteCPTP I O)
    (K : FiniteCPTP C I) :
    stabilizedRelativeEntropyBits (composeChannel Φ K) (composeChannel Ψ K) ≤
      stabilizedRelativeEntropyBits Φ Ψ := by
  refine iSup_le fun r => iSup_le fun ρ => iSup_le fun hρ => ?_
  change relativeEntropyBits (amplify Φ.map (Fin r) (amplify K.map (Fin r) ρ))
      (amplify Ψ.map (Fin r) (amplify K.map (Fin r) ρ)) ≤ _
  exact stabilizedRelativeEntropyBits_witness_fin_le Φ Ψ r
    (channel_density (amplifiedChannel K (Fin r)) hρ.1 hρ.2)

theorem stabilizedRelativeEntropyBits_sandwich (Φ Ψ : FiniteCPTP I O)
    (K : FiniteCPTP C I) (M : FiniteCPTP O P) :
    stabilizedRelativeEntropyBits (composeChannel M (composeChannel Φ K))
      (composeChannel M (composeChannel Ψ K)) ≤ stabilizedRelativeEntropyBits Φ Ψ :=
  (stabilizedRelativeEntropyBits_postcompose _ _ M).trans
    (stabilizedRelativeEntropyBits_precompose Φ Ψ K)

theorem tensorChannel_comp_map (Φ : FiniteCPTP I O) (Ψ : FiniteCPTP J P)
    (K : FiniteCPTP C I) (L : FiniteCPTP D J) :
    (tensorChannel (composeChannel Φ K) (composeChannel Ψ L)).map =
      (tensorChannel Φ Ψ).map.comp (tensorChannel K L).map := by
  apply matrixMap_ext_units
  intro ⟨c, d⟩ ⟨c', d'⟩
  have hs : Matrix.single (c, d) (c', d') (1 : ℂ) =
      Matrix.single c c' (1 : ℂ) ⊗ₖ Matrix.single d d' (1 : ℂ) := by
    rw [Matrix.single_kronecker_single, one_mul]
  rw [hs, tensorChannel_map_product, LinearMap.comp_apply,
    tensorChannel_map_product, tensorChannel_map_product]
  rfl

theorem channelPower_comp_map (Φ : FiniteCPTP I O) (M : FiniteCPTP O P)
    (n : ℕ) :
    (channelPower (composeChannel M Φ) n).map =
      (channelPower M n).map.comp (channelPower Φ n).map := by
  induction n with
  | zero =>
      apply matrixMap_ext_units
      intro i j
      ext a b
      rfl
  | succ n ih =>
      apply matrixMap_ext_units
      intro ⟨i, j⟩ ⟨i', j'⟩
      have hs : Matrix.single (i, j) (i', j') (1 : ℂ) =
          Matrix.single i i' (1 : ℂ) ⊗ₖ Matrix.single j j' (1 : ℂ) := by
        rw [Matrix.single_kronecker_single, one_mul]
      change (tensorChannel (channelPower (composeChannel M Φ) n)
        (composeChannel M Φ)).map (Matrix.single (i, j) (i', j') (1 : ℂ)) =
        (tensorChannel (channelPower M n) M).map
          ((tensorChannel (channelPower Φ n) Φ).map
            (Matrix.single (i, j) (i', j') (1 : ℂ)))
      rw [hs, tensorChannel_map_product, tensorChannel_map_product,
        tensorChannel_map_product]
      rw [ih]
      rfl

theorem powerValue_sandwich_le (Φ Ψ : FiniteCPTP I O)
    (K : FiniteCPTP C I) (M : FiniteCPTP O P) (n : ℕ) :
    powerValue (composeChannel M (composeChannel Φ K))
      (composeChannel M (composeChannel Ψ K)) n ≤ powerValue Φ Ψ n := by
  unfold powerValue stabilizedRelativeEntropyBits
  simp only [channelPower_comp_map]
  change stabilizedRelativeEntropyBits
      (composeChannel (channelPower M n)
        (composeChannel (channelPower Φ n) (channelPower K n)))
      (composeChannel (channelPower M n)
        (composeChannel (channelPower Ψ n) (channelPower K n))) ≤
    stabilizedRelativeEntropyBits (channelPower Φ n) (channelPower Ψ n)
  exact stabilizedRelativeEntropyBits_sandwich _ _ _ _

theorem normalizedPowerValue_sandwich_le (Φ Ψ : FiniteCPTP I O)
    (K : FiniteCPTP C I) (M : FiniteCPTP O P) (n : ℕ) :
    normalizedPowerValue (composeChannel M (composeChannel Φ K))
      (composeChannel M (composeChannel Ψ K)) n ≤ normalizedPowerValue Φ Ψ n := by
  exact mul_le_mul_of_nonneg_left (powerValue_sandwich_le Φ Ψ K M n)
    (EReal.coe_nonneg.mpr (inv_nonneg.mpr (by positivity : (0 : ℝ) ≤ n)))

theorem regularizedRelativeEntropyBits_sandwich_le (Φ Ψ : FiniteCPTP I O)
    (K : FiniteCPTP C I) (M : FiniteCPTP O P) :
    regularizedRelativeEntropyBits (composeChannel M (composeChannel Φ K))
      (composeChannel M (composeChannel Ψ K)) ≤ regularizedRelativeEntropyBits Φ Ψ := by
  refine iSup_le fun n => ?_
  exact (normalizedPowerValue_sandwich_le Φ Ψ K M (n + 1)).trans
    (normalizedPowerValue_le_regularized Φ Ψ (Nat.succ_pos n))

section ProtectedMemory

variable {R : Type*} [Fintype R] [DecidableEq R]

theorem stabilizedRelativeEntropyBits_amplified_le (Φ Ψ : FiniteCPTP I O) :
    stabilizedRelativeEntropyBits (amplifiedChannel Φ R) (amplifiedChannel Ψ R) ≤
      stabilizedRelativeEntropyBits Φ Ψ := by
  refine iSup_le fun r => iSup_le fun ρ => iSup_le fun hρ => ?_
  let ei := Equiv.prodAssoc I R (Fin r)
  let eo := Equiv.prodAssoc O R (Fin r)
  let ρ' := Matrix.reindex ei ei ρ
  have hρ' : IsDensity ρ' := channel_density (reindexChannel ei) hρ.1 hρ.2
  have hΦρ := channel_density (amplifiedChannel (amplifiedChannel Φ R) (Fin r))
    hρ.1 hρ.2
  have hΨρ := channel_density (amplifiedChannel (amplifiedChannel Ψ R) (Fin r))
    hρ.1 hρ.2
  have heq : relativeEntropyBits (amplify Φ.map (R × Fin r) ρ')
      (amplify Ψ.map (R × Fin r) ρ') =
      relativeEntropyBits (amplify (amplifiedChannel Φ R).map (Fin r) ρ)
        (amplify (amplifiedChannel Ψ R).map (Fin r) ρ) := by
    change relativeEntropyBits
      (DiamondControl.amplifyMap Φ.map (R × Fin r)
        (ρ.submatrix ei.symm ei.symm))
      (DiamondControl.amplifyMap Ψ.map (R × Fin r)
        (ρ.submatrix ei.symm ei.symm)) = _
    rw [DiamondControl.amplifyMap_assoc, DiamondControl.amplifyMap_assoc]
    exact relativeEntropyBits_reindex eo hΦρ.1 hΨρ.1
  rw [← heq]
  exact stabilizedRelativeEntropyBits_witness_le Φ Ψ (R × Fin r) hρ'

theorem stabilizedRelativeEntropyBits_reindex_channels
    (Φ Ψ : FiniteCPTP I O) (eI : C ≃ I) (eO : O ≃ P) :
    stabilizedRelativeEntropyBits
      (composeChannel (reindexChannel eO) (composeChannel Φ (reindexChannel eI)))
      (composeChannel (reindexChannel eO) (composeChannel Ψ (reindexChannel eI))) =
      stabilizedRelativeEntropyBits Φ Ψ := by
  apply stabilizedRelativeEntropyBits_eq_of_intertwine eI eO.symm _ _ Φ Ψ
  · intro X
    change Φ.map (Matrix.reindex eI eI X) =
      Matrix.reindex eO.symm eO.symm
        (Matrix.reindex eO eO (Φ.map (Matrix.reindex eI eI X)))
    rw [reindex_roundtrip]
  · intro X
    change Ψ.map (Matrix.reindex eI eI X) =
      Matrix.reindex eO.symm eO.symm
        (Matrix.reindex eO eO (Ψ.map (Matrix.reindex eI eI X)))
    rw [reindex_roundtrip]

theorem stabilizedRelativeEntropyBits_amplifiedLeft_le (Φ Ψ : FiniteCPTP I O) :
    stabilizedRelativeEntropyBits (amplifiedLeftChannel Φ R)
      (amplifiedLeftChannel Ψ R) ≤ stabilizedRelativeEntropyBits Φ Ψ := by
  change stabilizedRelativeEntropyBits
      (composeChannel (reindexChannel (Equiv.prodComm O R))
        (composeChannel (amplifiedChannel Φ R) (reindexChannel (Equiv.prodComm R I))))
      (composeChannel (reindexChannel (Equiv.prodComm O R))
        (composeChannel (amplifiedChannel Ψ R) (reindexChannel (Equiv.prodComm R I)))) ≤ _
  exact (stabilizedRelativeEntropyBits_sandwich _ _ _ _).trans
    (stabilizedRelativeEntropyBits_amplified_le Φ Ψ)

theorem stabilizedRelativeEntropyBits_superchannel_le (Φ Ψ : FiniteCPTP I O)
    (Γ : FiniteSuperchannel I O C D R) :
    stabilizedRelativeEntropyBits (Γ.applyChannel Φ) (Γ.applyChannel Ψ) ≤
      stabilizedRelativeEntropyBits Φ Ψ :=
  (stabilizedRelativeEntropyBits_sandwich
    (amplifiedLeftChannel Φ R) (amplifiedLeftChannel Ψ R) Γ.pre Γ.post).trans
      (stabilizedRelativeEntropyBits_amplifiedLeft_le Φ Ψ)

end ProtectedMemory

end QuantumProver.SuperchannelDiscrimination.ChannelRegularization

namespace QuantumProver.SuperchannelDiscrimination.ChannelRegularization

open Matrix KrausCompletion CPWrappers FlaggedStates TensorEntropy
open scoped BigOperators ComplexOrder MatrixOrder Matrix Kronecker Topology

variable {I O J P R : Type*}
  [Fintype I] [Fintype O] [Fintype J] [Fintype P] [Fintype R]
  [DecidableEq I] [DecidableEq O] [DecidableEq J] [DecidableEq P] [DecidableEq R]

theorem finiteCPTP_eq_of_map_eq (Φ Ψ : FiniteCPTP I O) (h : Φ.map = Ψ.map) :
    Φ = Ψ := by
  cases Φ
  cases Ψ
  cases h
  rfl

theorem amplify_product_action (Φ : FiniteCPTP I O)
    (A : Matrix I I ℂ) (B : Matrix R R ℂ) :
    amplify Φ.map R (A ⊗ₖ B) = Φ.map A ⊗ₖ B := by
  ext ⟨o, r⟩ ⟨p, s⟩
  have hslice : (fun i j => (A ⊗ₖ B) (i, r) (j, s)) = B r s • A := by
    ext i j
    simp [Matrix.kronecker_apply, Matrix.smul_apply, mul_comm]
  change Φ.map (fun i j => (A ⊗ₖ B) (i, r) (j, s)) o p = _
  rw [hslice, map_smul]
  simp [Matrix.smul_apply, Matrix.kronecker_apply, smul_eq_mul, mul_comm]

theorem tensorChannel_identity (Φ : FiniteCPTP I O) :
    tensorChannel Φ (reindexChannel (Equiv.refl R)) = amplifiedChannel Φ R := by
  apply finiteCPTP_eq_of_map_eq
  apply matrixMap_ext_units
  intro ⟨i, r⟩ ⟨j, s⟩
  have hs : Matrix.single (i, r) (j, s) (1 : ℂ) =
      Matrix.single i j (1 : ℂ) ⊗ₖ Matrix.single r s (1 : ℂ) := by
    rw [Matrix.single_kronecker_single, one_mul]
  rw [hs, tensorChannel_map_product]
  change Φ.map (Matrix.single i j 1) ⊗ₖ Matrix.single r s 1 =
    amplify Φ.map R (Matrix.single i j 1 ⊗ₖ Matrix.single r s 1)
  exact (amplify_product_action Φ _ _).symm

def powerPairIndex (A B : Type*) : (n : ℕ) →
    TensorIndex (A × B) n ≃ TensorIndex A n × TensorIndex B n
  | 0 =>
      { toFun := fun _ => (PUnit.unit, PUnit.unit)
        invFun := fun _ => PUnit.unit
        left_inv _ := Subsingleton.elim _ _
        right_inv _ := by apply Prod.ext <;> exact Subsingleton.elim _ _ }
  | n + 1 =>
      (Equiv.prodCongr (powerPairIndex A B n) (Equiv.refl (A × B))).trans
        (groupReference (TensorIndex A n) A (TensorIndex B n) B)

theorem tensorUnitOutput_pair (Φ : FiniteCPTP I O) (Ψ : FiniteCPTP J P)
    (n : ℕ) (i j : TensorIndex (I × J) n) :
    Matrix.reindex (powerPairIndex O P n) (powerPairIndex O P n)
        (tensorUnitOutput (tensorChannel Φ Ψ) n i j) =
      tensorUnitOutput Φ n ((powerPairIndex I J n) i).1
          ((powerPairIndex I J n) j).1 ⊗ₖ
        tensorUnitOutput Ψ n ((powerPairIndex I J n) i).2
          ((powerPairIndex I J n) j).2 := by
  induction n with
  | zero =>
      ext ⟨a, b⟩ ⟨a', b'⟩
      cases a
      cases b
      cases a'
      cases b'
      simp [tensorUnitOutput, powerPairIndex, Matrix.reindex_apply,
        Matrix.submatrix_apply, Matrix.kronecker_apply]
  | succ n ih =>
      ext ⟨⟨a, o⟩, ⟨b, p⟩⟩ ⟨⟨a', o'⟩, ⟨b', p'⟩⟩
      have h := congrArg
        (fun Z : Matrix (TensorIndex O n × TensorIndex P n)
          (TensorIndex O n × TensorIndex P n) ℂ => Z (a, b) (a', b'))
        (ih i.1 j.1)
      change tensorUnitOutput (tensorChannel Φ Ψ) n i.1 j.1
          ((powerPairIndex O P n).symm (a, b))
          ((powerPairIndex O P n).symm (a', b')) =
        tensorUnitOutput Φ n ((powerPairIndex I J n) i.1).1
            ((powerPairIndex I J n) j.1).1 a a' *
          tensorUnitOutput Ψ n ((powerPairIndex I J n) i.1).2
            ((powerPairIndex I J n) j.1).2 b b' at h
      have hs : Matrix.single i.2 j.2 (1 : ℂ) =
          Matrix.single i.2.1 j.2.1 (1 : ℂ) ⊗ₖ
            Matrix.single i.2.2 j.2.2 (1 : ℂ) := by
        rw [Matrix.single_kronecker_single, one_mul]
      have ht : (tensorChannel Φ Ψ).map (Matrix.single i.2 j.2 1)
          (o, p) (o', p') =
          Φ.map (Matrix.single i.2.1 j.2.1 1) o o' *
            Ψ.map (Matrix.single i.2.2 j.2.2 1) p p' := by
        rw [hs, tensorChannel_map_product]
        rfl
      change tensorUnitOutput (tensorChannel Φ Ψ) n i.1 j.1
          ((powerPairIndex O P n).symm (a, b))
          ((powerPairIndex O P n).symm (a', b')) *
          (tensorChannel Φ Ψ).map (Matrix.single i.2 j.2 1) (o, p) (o', p') =
        (tensorUnitOutput Φ n ((powerPairIndex I J n) i.1).1
            ((powerPairIndex I J n) j.1).1 a a' *
          Φ.map (Matrix.single i.2.1 j.2.1 1) o o') *
        (tensorUnitOutput Ψ n ((powerPairIndex I J n) i.1).2
            ((powerPairIndex I J n) j.1).2 b b' *
          Ψ.map (Matrix.single i.2.2 j.2.2 1) p p')
      rw [h, ht]
      ring

theorem channelPower_tensor_intertwine_map (Φ : FiniteCPTP I O)
    (Ψ : FiniteCPTP J P) (n : ℕ)
    (X : Matrix (TensorIndex (I × J) n) (TensorIndex (I × J) n) ℂ) :
    Matrix.reindex (powerPairIndex O P n) (powerPairIndex O P n)
        ((channelPower (tensorChannel Φ Ψ) n).map X) =
      (tensorChannel (channelPower Φ n) (channelPower Ψ n)).map
        (Matrix.reindex (powerPairIndex I J n) (powerPairIndex I J n) X) := by
  have hmap : (reindexMap (powerPairIndex O P n)).comp
        (channelPower (tensorChannel Φ Ψ) n).map =
      (tensorChannel (channelPower Φ n) (channelPower Ψ n)).map.comp
        (reindexMap (powerPairIndex I J n)) := by
    apply matrixMap_ext_units
    intro i j
    simp only [LinearMap.comp_apply, reindexMap_apply, channelPower_map_single,
      reindex_single]
    have hs : Matrix.single ((powerPairIndex I J n) i)
        ((powerPairIndex I J n) j) (1 : ℂ) =
      Matrix.single ((powerPairIndex I J n) i).1
          ((powerPairIndex I J n) j).1 1 ⊗ₖ
        Matrix.single ((powerPairIndex I J n) i).2
          ((powerPairIndex I J n) j).2 1 := by
      rw [Matrix.single_kronecker_single, one_mul]
    rw [hs, tensorChannel_map_product, channelPower_map_single, channelPower_map_single]
    exact tensorUnitOutput_pair Φ Ψ n i j
  exact congrArg (fun F : Matrix (TensorIndex (I × J) n)
    (TensorIndex (I × J) n) ℂ →ₗ[ℂ]
      Matrix (TensorIndex O n × TensorIndex P n)
        (TensorIndex O n × TensorIndex P n) ℂ => F X) hmap

theorem channelPower_identity_map (n : ℕ) :
    (channelPower (reindexChannel (Equiv.refl R)) n).map =
      LinearMap.id (R := ℂ) (M := Matrix (TensorIndex R n) (TensorIndex R n) ℂ) := by
  induction n with
  | zero =>
      apply matrixMap_ext_units
      intro i j
      ext a b
      rfl
  | succ n ih =>
      apply matrixMap_ext_units
      intro ⟨i, r⟩ ⟨j, s⟩
      have hs : Matrix.single (i, r) (j, s) (1 : ℂ) =
          Matrix.single i j (1 : ℂ) ⊗ₖ Matrix.single r s (1 : ℂ) := by
        rw [Matrix.single_kronecker_single, one_mul]
      change (tensorChannel (channelPower (reindexChannel (Equiv.refl R)) n)
        (reindexChannel (Equiv.refl R))).map (Matrix.single (i, r) (j, s) 1) = _
      rw [hs, tensorChannel_map_product, ih]
      rfl

theorem channelPower_identity (n : ℕ) :
    channelPower (reindexChannel (Equiv.refl R)) n =
      reindexChannel (Equiv.refl (TensorIndex R n)) := by
  apply finiteCPTP_eq_of_map_eq
  exact channelPower_identity_map n

theorem channelPower_amplified_intertwine (Φ : FiniteCPTP I O) (n : ℕ)
    (X : Matrix (TensorIndex (I × R) n) (TensorIndex (I × R) n) ℂ) :
    (amplifiedChannel (channelPower Φ n) (TensorIndex R n)).map
        (Matrix.reindex (powerPairIndex I R n) (powerPairIndex I R n) X) =
      Matrix.reindex (powerPairIndex O R n) (powerPairIndex O R n)
        ((channelPower (amplifiedChannel Φ R) n).map X) := by
  have h := channelPower_tensor_intertwine_map Φ (reindexChannel (Equiv.refl R)) n X
  rw [tensorChannel_identity, channelPower_identity, tensorChannel_identity] at h
  exact h.symm

theorem powerValue_amplified_le (Φ Ψ : FiniteCPTP I O) (n : ℕ) :
    powerValue (amplifiedChannel Φ R) (amplifiedChannel Ψ R) n ≤ powerValue Φ Ψ n := by
  change stabilizedRelativeEntropyBits (channelPower (amplifiedChannel Φ R) n)
      (channelPower (amplifiedChannel Ψ R) n) ≤ _
  rw [stabilizedRelativeEntropyBits_eq_of_intertwine (powerPairIndex I R n)
    (powerPairIndex O R n) _ _
    (amplifiedChannel (channelPower Φ n) (TensorIndex R n))
    (amplifiedChannel (channelPower Ψ n) (TensorIndex R n))
    (channelPower_amplified_intertwine Φ n) (channelPower_amplified_intertwine Ψ n)]
  exact stabilizedRelativeEntropyBits_amplified_le _ _

theorem regularizedRelativeEntropyBits_amplified_le (Φ Ψ : FiniteCPTP I O) :
    regularizedRelativeEntropyBits (amplifiedChannel Φ R) (amplifiedChannel Ψ R) ≤
      regularizedRelativeEntropyBits Φ Ψ := by
  refine iSup_le fun n => ?_
  have h : normalizedPowerValue (amplifiedChannel Φ R) (amplifiedChannel Ψ R) (n + 1) ≤
      normalizedPowerValue Φ Ψ (n + 1) :=
    mul_le_mul_of_nonneg_left (powerValue_amplified_le Φ Ψ (n + 1))
      (EReal.coe_nonneg.mpr
        (inv_nonneg.mpr (show (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) by positivity)))
  exact h.trans (normalizedPowerValue_le_regularized Φ Ψ (Nat.succ_pos n))

theorem regularizedRelativeEntropyBits_amplifiedLeft_le (Φ Ψ : FiniteCPTP I O) :
    regularizedRelativeEntropyBits (amplifiedLeftChannel Φ R)
      (amplifiedLeftChannel Ψ R) ≤ regularizedRelativeEntropyBits Φ Ψ := by
  exact (regularizedRelativeEntropyBits_sandwich_le
    (amplifiedChannel Φ R) (amplifiedChannel Ψ R)
    (reindexChannel (Equiv.prodComm R I)) (reindexChannel (Equiv.prodComm O R))).trans
      (regularizedRelativeEntropyBits_amplified_le Φ Ψ)

theorem stabilizedRelativeEntropyBits_amplified_eq (Φ Ψ : FiniteCPTP I O)
    [Nonempty R] :
    stabilizedRelativeEntropyBits (amplifiedChannel Φ R) (amplifiedChannel Ψ R) =
      stabilizedRelativeEntropyBits Φ Ψ := by
  apply le_antisymm
  · exact stabilizedRelativeEntropyBits_amplified_le Φ Ψ
  · have h := stabilizedRelativeEntropyBits_tensor_lower Φ Ψ
      (reindexChannel (Equiv.refl R)) (reindexChannel (Equiv.refl R))
    simpa only [stabilizedRelativeEntropyBits_self, add_zero, tensorChannel_identity] using h

theorem powerValue_amplified_eq (Φ Ψ : FiniteCPTP I O) [Nonempty R] (n : ℕ) :
    powerValue (amplifiedChannel Φ R) (amplifiedChannel Ψ R) n = powerValue Φ Ψ n := by
  change stabilizedRelativeEntropyBits (channelPower (amplifiedChannel Φ R) n)
      (channelPower (amplifiedChannel Ψ R) n) = _
  rw [stabilizedRelativeEntropyBits_eq_of_intertwine (powerPairIndex I R n)
    (powerPairIndex O R n) _ _
    (amplifiedChannel (channelPower Φ n) (TensorIndex R n))
    (amplifiedChannel (channelPower Ψ n) (TensorIndex R n))
    (channelPower_amplified_intertwine Φ n) (channelPower_amplified_intertwine Ψ n)]
  exact stabilizedRelativeEntropyBits_amplified_eq _ _

theorem regularizedRelativeEntropyBits_amplified_eq (Φ Ψ : FiniteCPTP I O)
    [Nonempty R] :
    regularizedRelativeEntropyBits (amplifiedChannel Φ R) (amplifiedChannel Ψ R) =
      regularizedRelativeEntropyBits Φ Ψ := by
  unfold regularizedRelativeEntropyBits
  congr 1
  funext n
  exact powerValue_amplified_eq Φ Ψ n

variable {C D : Type*} [Fintype C] [Fintype D] [DecidableEq C] [DecidableEq D]

theorem regularizedRelativeEntropyBits_superchannel_le (Φ Ψ : FiniteCPTP I O)
    (Γ : FiniteSuperchannel I O C D R) :
    regularizedRelativeEntropyBits (Γ.applyChannel Φ) (Γ.applyChannel Ψ) ≤
      regularizedRelativeEntropyBits Φ Ψ :=
  (regularizedRelativeEntropyBits_sandwich_le
    (amplifiedLeftChannel Φ R) (amplifiedLeftChannel Ψ R) Γ.pre Γ.post).trans
      (regularizedRelativeEntropyBits_amplifiedLeft_le Φ Ψ)

end QuantumProver.SuperchannelDiscrimination.ChannelRegularization

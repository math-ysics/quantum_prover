import QuantumProver.InformationTheory.SuperchannelDiscrimination.CPTPKraus
import QuantumProver.InformationTheory.SuperchannelDiscrimination.FlaggedStates
import QuantumProver.InformationTheory.SuperchannelDiscrimination.TestingTheorems
import QuantumProver.InformationTheory.SuperchannelDiscrimination.QuantumTestingPowerBound

set_option autoImplicit false

noncomputable section

open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder Matrix Kronecker

namespace QuantumProver.SuperchannelDiscrimination.MatrixStrategyAssembly

variable {I O : Type*} [Fintype I] [Fintype O]
  [DecidableEq I] [DecidableEq O]

def flagIndex (o₀ : O) : O ⊕ Unit → O × Fin 2 :=
  Sum.elim (fun o => (o, 0)) (fun _ => (o₀, 1))

omit [Fintype O] [DecidableEq O] in
theorem flagIndex_injective (o₀ : O) : Function.Injective (flagIndex o₀) := by
  intro a b h
  cases a with
  | inl a =>
      cases b with
      | inl b => simpa [flagIndex] using h
      | inr b => simp [flagIndex] at h
  | inr a =>
      cases b with
      | inl b => simp [flagIndex] at h
      | inr b => rfl

def flagIsometry (o₀ : O) : Matrix (O × Fin 2) (O ⊕ Unit) ℂ :=
  fun x a => if x = flagIndex o₀ a then 1 else 0

theorem flagIsometry_gram (o₀ : O) :
    (flagIsometry o₀)ᴴ * flagIsometry o₀ = 1 := by
  ext a b
  by_cases h : a = b <;>
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, flagIsometry,
      (flagIndex_injective o₀).eq_iff, Matrix.one_apply, h, eq_comm]

def encodeFlag (o₀ : O) :
    Matrix (O ⊕ Unit) (O ⊕ Unit) ℂ →ₗ[ℂ] Matrix (O × Fin 2) (O × Fin 2) ℂ :=
  QuantumProver.ElegantJointMeasurement.CP.krausMap (fun _ : Unit => flagIsometry o₀)

theorem encodeFlag_apply (o₀ : O) (X : Matrix (O ⊕ Unit) (O ⊕ Unit) ℂ) :
    encodeFlag o₀ X = flagIsometry o₀ * X * (flagIsometry o₀)ᴴ := by
  simp [encodeFlag, QuantumProver.ElegantJointMeasurement.CP.krausMap]

theorem encodeFlag_completelyPositive (o₀ : O) :
    CPTPKraus.CompletelyPositive (encodeFlag o₀) :=
  (CPTPKraus.completelyPositive_iff_EJMCP _).mpr
    (QuantumProver.ElegantJointMeasurement.CP.krausMap_completelyPositive _)

theorem encodeFlag_tracePreserving (o₀ : O) :
    CPTPKraus.TracePreserving (encodeFlag o₀) := by
  apply (QuantumProver.ElegantJointMeasurement.CP.krausMap_trace_preserving_iff _).mpr
  simpa using flagIsometry_gram o₀

theorem encodeFlag_success (o₀ o p : O)
    (X : Matrix (O ⊕ Unit) (O ⊕ Unit) ℂ) :
    encodeFlag o₀ X (o, 0) (p, 0) = X (Sum.inl o) (Sum.inl p) := by
  simp [encodeFlag_apply, flagIsometry, flagIndex, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Fintype.sum_sum_type]

theorem encodeFlag_failure (o₀ o p : O)
    (X : Matrix (O ⊕ Unit) (O ⊕ Unit) ℂ) :
    encodeFlag o₀ X (o, 1) (p, 1) =
      if o = o₀ ∧ p = o₀ then X (Sum.inr ()) (Sum.inr ()) else 0 := by
  by_cases ho : o = o₀ <;> by_cases hp : p = o₀ <;>
    simp [encodeFlag_apply, flagIsometry, flagIndex, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Fintype.sum_sum_type, ho, hp]

def physicalCompletion (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) (o₀ : O) :
    Matrix I I ℂ →ₗ[ℂ] Matrix (O × Fin 2) (O × Fin 2) ℂ :=
  (encodeFlag o₀).comp (CPTPKraus.canonicalCompletion Φ)

theorem physicalCompletion_completelyPositive
    (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) (o₀ : O) :
    CPTPKraus.CompletelyPositive (physicalCompletion Φ o₀) := by
  apply (CPTPKraus.completelyPositive_iff_EJMCP _).mpr
  exact ((CPTPKraus.completelyPositive_iff_EJMCP _).mp
    (encodeFlag_completelyPositive o₀)).comp
    ((CPTPKraus.completelyPositive_iff_EJMCP _).mp
      (CPTPKraus.canonicalCompletion_completelyPositive Φ))

theorem physicalCompletion_tracePreserving
    (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) (o₀ : O)
    (hΦ : CPTPKraus.CompletelyPositive Φ) (htrace : CPTPKraus.TraceNonincreasing Φ) :
    CPTPKraus.TracePreserving (physicalCompletion Φ o₀) := by
  intro X
  change (encodeFlag o₀ (CPTPKraus.canonicalCompletion Φ X)).trace = X.trace
  rw [encodeFlag_tracePreserving o₀,
    CPTPKraus.canonicalCompletion_tracePreserving Φ hΦ htrace]

theorem physicalCompletion_success
    (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) (o₀ o p : O)
    (hΦ : CPTPKraus.CompletelyPositive Φ) (htrace : CPTPKraus.TraceNonincreasing Φ)
    (X : Matrix I I ℂ) :
    physicalCompletion Φ o₀ X (o, 0) (p, 0) = Φ X o p := by
  change encodeFlag o₀ (CPTPKraus.canonicalCompletion Φ X) (o, 0) (p, 0) = _
  rw [encodeFlag_success, CPTPKraus.canonicalCompletion_action Φ hΦ htrace]
  rfl

theorem physicalCompletion_failure
    (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) (o₀ o p : O)
    (hΦ : CPTPKraus.CompletelyPositive Φ) (htrace : CPTPKraus.TraceNonincreasing Φ)
    (X : Matrix I I ℂ) :
    physicalCompletion Φ o₀ X (o, 1) (p, 1) =
      if o = o₀ ∧ p = o₀ then (CPTPKraus.canonicalResidual Φ * X).trace else 0 := by
  change encodeFlag o₀ (CPTPKraus.canonicalCompletion Φ X) (o, 1) (p, 1) = _
  rw [encodeFlag_failure, CPTPKraus.canonicalCompletion_action Φ hΦ htrace]
  simp

theorem physicalCompletion_amplify_success
    (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) (o₀ : O)
    (hΦ : CPTPKraus.CompletelyPositive Φ) (htrace : CPTPKraus.TraceNonincreasing Φ)
    (R : Type*) [Fintype R] (X : Matrix (I × R) (I × R) ℂ) :
    (CPTPKraus.amplify (physicalCompletion Φ o₀) R X).submatrix
      (fun x : O × R => ((x.1, 0), x.2))
      (fun x : O × R => ((x.1, 0), x.2)) = CPTPKraus.amplify Φ R X := by
  ext ⟨o, r⟩ ⟨p, s⟩
  exact physicalCompletion_success Φ o₀ o p hΦ htrace _

theorem physicalCompletion_amplify_failure
    (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) (o₀ : O)
    (hΦ : CPTPKraus.CompletelyPositive Φ) (htrace : CPTPKraus.TraceNonincreasing Φ)
    (R : Type*) [Fintype R] (X : Matrix (I × R) (I × R) ℂ) :
    (CPTPKraus.amplify (physicalCompletion Φ o₀) R X).submatrix
      (fun r : R => ((o₀, 1), r)) (fun r : R => ((o₀, 1), r)) =
      Matrix.of (fun r s => (CPTPKraus.canonicalResidual Φ *
        Matrix.of (fun i j => X (i, r) (j, s))).trace) := by
  ext r s
  change physicalCompletion Φ o₀ (Matrix.of (fun i j => X (i, r) (j, s)))
    (o₀, 1) (o₀, 1) = _
  simpa using physicalCompletion_failure Φ o₀ o₀ o₀ hΦ htrace
    (Matrix.of (fun i j => X (i, r) (j, s)))

def discardInputFlag :
    Matrix (I × Fin 2) (I × Fin 2) ℂ →ₗ[ℂ] Matrix I I ℂ where
  toFun X := fun i j => X (i, 0) (j, 0) + X (i, 1) (j, 1)
  map_add' X Y := by
    ext i j
    change (X (i, 0) (j, 0) + Y (i, 0) (j, 0)) +
      (X (i, 1) (j, 1) + Y (i, 1) (j, 1)) =
      (X (i, 0) (j, 0) + X (i, 1) (j, 1)) +
      (Y (i, 0) (j, 0) + Y (i, 1) (j, 1))
    abel
  map_smul' c X := by
    ext i j
    change c * X (i, 0) (j, 0) + c * X (i, 1) (j, 1) =
      c * (X (i, 0) (j, 0) + X (i, 1) (j, 1))
    ring

omit [Fintype I] [DecidableEq I] in
theorem discardInputFlag_completelyPositive :
    CPTPKraus.CompletelyPositive (discardInputFlag (I := I)) := by
  intro r X hX
  have hzero := hX.submatrix (fun x : I × Fin r => ((x.1, (0 : Fin 2)), x.2))
  have hone := hX.submatrix (fun x : I × Fin r => ((x.1, (1 : Fin 2)), x.2))
  exact hzero.add hone

theorem discardInputFlag_tracePreserving :
    CPTPKraus.TracePreserving (discardInputFlag (I := I)) := by
  intro X
  change (∑ i : I, (X (i, 0) (i, 0) + X (i, 1) (i, 1))) = X.trace
  simp [Matrix.trace, Matrix.diag,
    Fintype.sum_prod_type, Fin.sum_univ_two, Finset.sum_add_distrib]

def flaggedInsertedMap (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) (o₀ : O) :
    Matrix (I × Fin 2) (I × Fin 2) ℂ →ₗ[ℂ] Matrix (O × Fin 2) (O × Fin 2) ℂ :=
  (physicalCompletion Φ o₀).comp discardInputFlag

theorem flaggedInsertedMap_completelyPositive
    (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) (o₀ : O) :
    CPTPKraus.CompletelyPositive (flaggedInsertedMap Φ o₀) := by
  apply (CPTPKraus.completelyPositive_iff_EJMCP _).mpr
  exact ((CPTPKraus.completelyPositive_iff_EJMCP _).mp
    (physicalCompletion_completelyPositive Φ o₀)).comp
    ((CPTPKraus.completelyPositive_iff_EJMCP _).mp discardInputFlag_completelyPositive)

theorem flaggedInsertedMap_tracePreserving
    (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) (o₀ : O)
    (hΦ : CPTPKraus.CompletelyPositive Φ) (htrace : CPTPKraus.TraceNonincreasing Φ) :
    CPTPKraus.TracePreserving (flaggedInsertedMap Φ o₀) := by
  intro X
  change (physicalCompletion Φ o₀ (discardInputFlag X)).trace = X.trace
  rw [physicalCompletion_tracePreserving Φ o₀ hΦ htrace,
    discardInputFlag_tracePreserving]

theorem flaggedInsertedMap_amplify_success
    (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) (o₀ : O)
    (hΦ : CPTPKraus.CompletelyPositive Φ) (htrace : CPTPKraus.TraceNonincreasing Φ)
    (R : Type*) [Fintype R]
    (X : Matrix ((I × Fin 2) × R) ((I × Fin 2) × R) ℂ) :
    (CPTPKraus.amplify (flaggedInsertedMap Φ o₀) R X).submatrix
      (fun x : O × R => ((x.1, 0), x.2))
      (fun x : O × R => ((x.1, 0), x.2)) =
      CPTPKraus.amplify Φ R (CPTPKraus.amplify discardInputFlag R X) := by
  ext ⟨o, r⟩ ⟨p, s⟩
  exact physicalCompletion_success Φ o₀ o p hΦ htrace _

theorem flaggedInsertedMap_amplify_failure
    (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) (o₀ : O)
    (hΦ : CPTPKraus.CompletelyPositive Φ) (htrace : CPTPKraus.TraceNonincreasing Φ)
    (R : Type*) [Fintype R]
    (X : Matrix ((I × Fin 2) × R) ((I × Fin 2) × R) ℂ) :
    (CPTPKraus.amplify (flaggedInsertedMap Φ o₀) R X).submatrix
      (fun r : R => ((o₀, 1), r)) (fun r : R => ((o₀, 1), r)) =
      Matrix.of (fun r s => (CPTPKraus.canonicalResidual Φ *
        discardInputFlag (Matrix.of (fun i j => X (i, r) (j, s)))).trace) := by
  ext r s
  change physicalCompletion Φ o₀
    (discardInputFlag (Matrix.of (fun i j => X (i, r) (j, s))))
    (o₀, 1) (o₀, 1) = _
  simpa using physicalCompletion_failure Φ o₀ o₀ o₀ hΦ htrace _

theorem flaggedInsertedMap_amplify_posSemidef
    (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) (o₀ : O)
    (R : Type*) [Fintype R] [DecidableEq R]
    {X : Matrix ((I × Fin 2) × R) ((I × Fin 2) × R) ℂ} (hX : X.PosSemidef) :
    (CPTPKraus.amplify (flaggedInsertedMap Φ o₀) R X).PosSemidef :=
  CPTPKraus.amplify_posSemidef _ (flaggedInsertedMap_completelyPositive Φ o₀) R hX

theorem flaggedInsertedMap_amplify_tracePreserving
    (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) (o₀ : O)
    (hΦ : CPTPKraus.CompletelyPositive Φ) (htrace : CPTPKraus.TraceNonincreasing Φ)
    (R : Type*) [Fintype R] [DecidableEq R]
    (X : Matrix ((I × Fin 2) × R) ((I × Fin 2) × R) ℂ) :
    (CPTPKraus.amplify (flaggedInsertedMap Φ o₀) R X).trace = X.trace :=
  CPTPKraus.amplify_tracePreserving _ (flaggedInsertedMap_completelyPositive Φ o₀)
    (flaggedInsertedMap_tracePreserving Φ o₀ hΦ htrace) R X

end QuantumProver.SuperchannelDiscrimination.MatrixStrategyAssembly

namespace QuantumProver.SuperchannelDiscrimination.MatrixStrategyAssembly

open KrausCompletion CPWrappers

variable {I O C D R : Type*}
  [Fintype I] [Fintype O] [Fintype C] [Fintype D] [Fintype R]
  [DecidableEq I] [DecidableEq O] [DecidableEq C] [DecidableEq D] [DecidableEq R]

def flagBlock (A B : Matrix O O ℂ) : Matrix (O × Fin 2) (O × Fin 2) ℂ :=
  fun x y => if x.2 = 0 then (if y.2 = 0 then A x.1 y.1 else 0)
    else (if y.2 = 0 then 0 else B x.1 y.1)

def physicalRepair (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) (o₀ : O) :
    Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ where
  toFun X := (CPTPKraus.canonicalResidual Φ * X).trace • Matrix.single o₀ o₀ (1 : ℂ)
  map_add' X Y := by
    simp [Matrix.mul_add, Matrix.trace_add, add_smul]
  map_smul' c X := by
    simp [Matrix.mul_smul, Matrix.trace_smul, smul_smul]

theorem encodeFlag_cross (o₀ o p : O) (X : Matrix (O ⊕ Unit) (O ⊕ Unit) ℂ) :
    encodeFlag o₀ X (o, 0) (p, 1) =
      if p = o₀ then X (Sum.inl o) (Sum.inr ()) else 0 := by
  by_cases hp : p = o₀ <;>
    simp [encodeFlag_apply, flagIsometry, flagIndex, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Fintype.sum_sum_type, hp]

theorem encodeFlag_cross_reverse (o₀ o p : O)
    (X : Matrix (O ⊕ Unit) (O ⊕ Unit) ℂ) :
    encodeFlag o₀ X (o, 1) (p, 0) =
      if o = o₀ then X (Sum.inr ()) (Sum.inl p) else 0 := by
  by_cases ho : o = o₀ <;>
    simp [encodeFlag_apply, flagIsometry, flagIndex, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Fintype.sum_sum_type, ho]

theorem physicalCompletion_cross
    (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) (o₀ o p : O)
    (hΦ : CPTPKraus.CompletelyPositive Φ) (htrace : CPTPKraus.TraceNonincreasing Φ)
    (X : Matrix I I ℂ) :
    physicalCompletion Φ o₀ X (o, 0) (p, 1) = 0 ∧
      physicalCompletion Φ o₀ X (o, 1) (p, 0) = 0 := by
  change encodeFlag o₀ (CPTPKraus.canonicalCompletion Φ X) (o, 0) (p, 1) = 0 ∧
    encodeFlag o₀ (CPTPKraus.canonicalCompletion Φ X) (o, 1) (p, 0) = 0
  rw [encodeFlag_cross, encodeFlag_cross_reverse,
    CPTPKraus.canonicalCompletion_action Φ hΦ htrace]
  simp

theorem physicalCompletion_action
    (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) (o₀ : O)
    (hΦ : CPTPKraus.CompletelyPositive Φ) (htrace : CPTPKraus.TraceNonincreasing Φ)
    (X : Matrix I I ℂ) :
    physicalCompletion Φ o₀ X = flagBlock (Φ X) (physicalRepair Φ o₀ X) := by
  ext ⟨o, f⟩ ⟨p, g⟩
  fin_cases f <;> fin_cases g
  · simpa [flagBlock] using physicalCompletion_success Φ o₀ o p hΦ htrace X
  · simpa [flagBlock] using (physicalCompletion_cross Φ o₀ o p hΦ htrace X).1
  · simpa [flagBlock] using (physicalCompletion_cross Φ o₀ o p hΦ htrace X).2
  · simpa [flagBlock, physicalRepair, Matrix.single, Matrix.smul_apply,
      smul_eq_mul, eq_comm] using physicalCompletion_failure Φ o₀ o p hΦ htrace X

def physicalCompletionChannel
    (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) (o₀ : O)
    (hΦ : CPTPKraus.CompletelyPositive Φ) (htrace : CPTPKraus.TraceNonincreasing Φ) :
    FiniteCPTP I (O × Fin 2) where
  map := physicalCompletion Φ o₀
  completelyPositive := physicalCompletion_completelyPositive Φ o₀
  tracePreserving := physicalCompletion_tracePreserving Φ o₀ hΦ htrace

theorem amplifyMap_flagBlock (Ψ : Matrix O O ℂ →ₗ[ℂ] Matrix D D ℂ)
    (A B : Matrix O O ℂ) :
    amplifyMap Ψ (Fin 2) (flagBlock A B) = flagBlock (Ψ A) (Ψ B) := by
  ext ⟨d, f⟩ ⟨e, g⟩
  fin_cases f <;> fin_cases g
  · rfl
  · change Ψ (0 : Matrix O O ℂ) d e = 0
    rw [map_zero]
    rfl
  · change Ψ (0 : Matrix O O ℂ) d e = 0
    rw [map_zero]
    rfl
  · rfl

def wrapPhysicalFlaggedLinear (Γ : FiniteSuperchannel I O C D R)
    (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix (O × Fin 2) (O × Fin 2) ℂ) :
    Matrix C C ℂ →ₗ[ℂ] Matrix (D × Fin 2) (D × Fin 2) ℂ :=
  (amplifyMap Γ.post.map (Fin 2)).comp
    ((reindexMap (Equiv.prodAssoc R O (Fin 2)).symm).comp
      ((amplifyLeftMap Φ R).comp Γ.pre.map))

def wrapPhysicalFlaggedChannel (Γ : FiniteSuperchannel I O C D R)
    (Φ : FiniteCPTP I (O × Fin 2)) : FiniteCPTP C (D × Fin 2) :=
  composeChannel (amplifiedChannel Γ.post (Fin 2))
    (composeChannel (reindexChannel (Equiv.prodAssoc R O (Fin 2)).symm)
      (composeChannel (amplifiedLeftChannel Φ R) Γ.pre))

theorem wrapPhysicalFlaggedChannel_map (Γ : FiniteSuperchannel I O C D R)
    (Φ : FiniteCPTP I (O × Fin 2)) :
    (wrapPhysicalFlaggedChannel Γ Φ).map = wrapPhysicalFlaggedLinear Γ Φ.map := rfl

theorem amplifyLeft_physicalCompletion_flagBlock
    (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) (o₀ : O)
    (hΦ : CPTPKraus.CompletelyPositive Φ) (htrace : CPTPKraus.TraceNonincreasing Φ)
    (X : Matrix (R × I) (R × I) ℂ) :
    reindexMap (Equiv.prodAssoc R O (Fin 2)).symm
      (amplifyLeftMap (physicalCompletion Φ o₀) R X) =
      flagBlock (amplifyLeftMap Φ R X) (amplifyLeftMap (physicalRepair Φ o₀) R X) := by
  ext ⟨⟨r, o⟩, f⟩ ⟨⟨s, p⟩, g⟩
  change physicalCompletion Φ o₀ (Matrix.of (fun i j => X (r, i) (s, j)))
    (o, f) (p, g) = _
  exact congrArg (fun M : Matrix (O × Fin 2) (O × Fin 2) ℂ => M (o, f) (p, g))
    (physicalCompletion_action Φ o₀ hΦ htrace (Matrix.of (fun i j => X (r, i) (s, j))))

theorem wrapPhysicalCompletion_action (Γ : FiniteSuperchannel I O C D R)
    (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) (o₀ : O)
    (hΦ : CPTPKraus.CompletelyPositive Φ) (htrace : CPTPKraus.TraceNonincreasing Φ)
    (X : Matrix C C ℂ) :
    wrapPhysicalFlaggedLinear Γ (physicalCompletion Φ o₀) X =
      flagBlock (Γ.applyLinear Φ X) (Γ.applyLinear (physicalRepair Φ o₀) X) := by
  change amplifyMap Γ.post.map (Fin 2)
    (reindexMap (Equiv.prodAssoc R O (Fin 2)).symm
      (amplifyLeftMap (physicalCompletion Φ o₀) R (Γ.pre.map X))) = _
  rw [amplifyLeft_physicalCompletion_flagBlock Φ o₀ hΦ htrace,
    amplifyMap_flagBlock]
  rfl

theorem flagBlock_success_trace (A B E : Matrix D D ℂ) :
    (flagBlock A B * flagBlock E 0).trace = (A * E).trace := by
  simp [Matrix.trace, Matrix.diag, Matrix.mul_apply, flagBlock,
    Fintype.sum_prod_type, Fin.sum_univ_two]

theorem wrapPhysicalCompletion_success_acceptance (Γ : FiniteSuperchannel I O C D R)
    (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) (o₀ : O)
    (hΦ : CPTPKraus.CompletelyPositive Φ) (htrace : CPTPKraus.TraceNonincreasing Φ)
    (X : Matrix C C ℂ) (E : Matrix D D ℂ) :
    acceptance (wrapPhysicalFlaggedLinear Γ (physicalCompletion Φ o₀) X)
      (flagBlock E 0) = acceptance (Γ.applyLinear Φ X) E := by
  rw [wrapPhysicalCompletion_action Γ Φ o₀ hΦ htrace]
  exact congrArg Complex.re (flagBlock_success_trace _ _ E)

theorem wrapPhysicalCompletion_density (Γ : FiniteSuperchannel I O C D R)
    (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) (o₀ : O)
    (hΦ : CPTPKraus.CompletelyPositive Φ) (htrace : CPTPKraus.TraceNonincreasing Φ)
    {X : Matrix C C ℂ} (hX : X.PosSemidef) (hunit : X.trace = 1) :
    (wrapPhysicalFlaggedLinear Γ (physicalCompletion Φ o₀) X).PosSemidef ∧
      (wrapPhysicalFlaggedLinear Γ (physicalCompletion Φ o₀) X).trace = 1 :=
  channel_density
    (wrapPhysicalFlaggedChannel Γ (physicalCompletionChannel Φ o₀ hΦ htrace)) hX hunit

theorem wrapPhysicalCompletion_acceptance_domination
    (Γ : FiniteSuperchannel I O C D R)
    (Φ Ψ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) (o₀ : O) {b c : ℝ}
    (hΦ : CPTPKraus.CompletelyPositive Φ) (htrace : CPTPKraus.TraceNonincreasing Φ)
    (hdom : CPTPKraus.CPDom Φ Ψ c) (hb : 0 ≤ b)
    {A B : Matrix C C ℂ} (hB : B.PosSemidef)
    (hAB : ((b : ℂ) • B - A).PosSemidef)
    {E : Matrix D D ℂ} (hE : E.PosSemidef) :
    acceptance (wrapPhysicalFlaggedLinear Γ (physicalCompletion Φ o₀) A)
      (flagBlock E 0) ≤ (b * c) * acceptance (Γ.applyLinear Ψ B) E := by
  rw [wrapPhysicalCompletion_success_acceptance Γ Φ o₀ hΦ htrace]
  exact cpDom_superchannel_state_acceptance Γ hΦ hdom hb hB hAB hE

end QuantumProver.SuperchannelDiscrimination.MatrixStrategyAssembly

namespace QuantumProver.SuperchannelDiscrimination.MatrixStrategyAssembly

open KrausCompletion CPWrappers

variable {I O P C D R : Type*}
  [Fintype I] [Fintype O] [Fintype P] [Fintype C] [Fintype D] [Fintype R]
  [DecidableEq I] [DecidableEq O] [DecidableEq P]
  [DecidableEq C] [DecidableEq D] [DecidableEq R]

def flaggedInsertedChannel
    (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) (o₀ : O)
    (hΦ : CPTPKraus.CompletelyPositive Φ) (htrace : CPTPKraus.TraceNonincreasing Φ) :
    FiniteCPTP (I × Fin 2) (O × Fin 2) where
  map := flaggedInsertedMap Φ o₀
  completelyPositive := flaggedInsertedMap_completelyPositive Φ o₀
  tracePreserving := flaggedInsertedMap_tracePreserving Φ o₀ hΦ htrace

def extendFlagSuperchannel (Γ : FiniteSuperchannel I O C D R) :
    FiniteSuperchannel (I × Fin 2) (O × Fin 2) (C × Fin 2) (D × Fin 2) R where
  pre := composeChannel (reindexChannel (Equiv.prodAssoc R I (Fin 2)))
    (amplifiedChannel Γ.pre (Fin 2))
  post := composeChannel (amplifiedChannel Γ.post (Fin 2))
    (reindexChannel (Equiv.prodAssoc R O (Fin 2)).symm)

theorem amplifyLeftMap_comp_matrix
    (Φ : Matrix O O ℂ →ₗ[ℂ] Matrix P P ℂ)
    (Ψ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) :
    amplifyLeftMap (Φ.comp Ψ) R =
      (amplifyLeftMap Φ R).comp (amplifyLeftMap Ψ R) := by
  ext X ⟨r, o⟩ ⟨s, p⟩
  rfl

theorem extendFlag_pre_discard (Γ : FiniteSuperchannel I O C D R)
    (X : Matrix (C × Fin 2) (C × Fin 2) ℂ) :
    amplifyLeftMap (discardInputFlag (I := I)) R
      ((extendFlagSuperchannel Γ).pre.map X) = Γ.pre.map (discardInputFlag X) := by
  ext ⟨r, i⟩ ⟨s, j⟩
  exact (congrArg (fun Y : Matrix (R × I) (R × I) ℂ => Y (r, i) (s, j))
    (Γ.pre.map.map_add
      (Matrix.of (fun c d => X (c, 0) (d, 0)))
      (Matrix.of (fun c d => X (c, 1) (d, 1))))).symm

theorem extendFlag_apply_flaggedInserted (Γ : FiniteSuperchannel I O C D R)
    (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) (o₀ : O)
    (X : Matrix (C × Fin 2) (C × Fin 2) ℂ) :
    (extendFlagSuperchannel Γ).applyLinear (flaggedInsertedMap Φ o₀) X =
      wrapPhysicalFlaggedLinear Γ (physicalCompletion Φ o₀) (discardInputFlag X) := by
  change amplifyMap Γ.post.map (Fin 2)
    (reindexMap (Equiv.prodAssoc R O (Fin 2)).symm
      (amplifyLeftMap (flaggedInsertedMap Φ o₀) R
        ((extendFlagSuperchannel Γ).pre.map X))) = _
  rw [flaggedInsertedMap, amplifyLeftMap_comp_matrix]
  change amplifyMap Γ.post.map (Fin 2)
    (reindexMap (Equiv.prodAssoc R O (Fin 2)).symm
      (amplifyLeftMap (physicalCompletion Φ o₀) R
        (amplifyLeftMap discardInputFlag R ((extendFlagSuperchannel Γ).pre.map X)))) = _
  rw [extendFlag_pre_discard]
  rfl

theorem extendedFlaggedCompletion_action (Γ : FiniteSuperchannel I O C D R)
    (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) (o₀ : O)
    (hΦ : CPTPKraus.CompletelyPositive Φ) (htrace : CPTPKraus.TraceNonincreasing Φ)
    (X : Matrix (C × Fin 2) (C × Fin 2) ℂ) :
    ((extendFlagSuperchannel Γ).applyChannel (flaggedInsertedChannel Φ o₀ hΦ htrace)).map X =
      flagBlock (Γ.applyLinear Φ (discardInputFlag X))
        (Γ.applyLinear (physicalRepair Φ o₀) (discardInputFlag X)) := by
  change (extendFlagSuperchannel Γ).applyLinear (flaggedInsertedMap Φ o₀) X = _
  rw [extendFlag_apply_flaggedInserted]
  exact wrapPhysicalCompletion_action Γ Φ o₀ hΦ htrace _

theorem extendedFlaggedCompletion_success_acceptance
    (Γ : FiniteSuperchannel I O C D R)
    (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) (o₀ : O)
    (hΦ : CPTPKraus.CompletelyPositive Φ) (htrace : CPTPKraus.TraceNonincreasing Φ)
    (X : Matrix (C × Fin 2) (C × Fin 2) ℂ) (E : Matrix D D ℂ) :
    acceptance
      (((extendFlagSuperchannel Γ).applyChannel (flaggedInsertedChannel Φ o₀ hΦ htrace)).map X)
      (flagBlock E 0) = acceptance (Γ.applyLinear Φ (discardInputFlag X)) E := by
  rw [extendedFlaggedCompletion_action]
  exact congrArg Complex.re (flagBlock_success_trace _ _ E)

end QuantumProver.SuperchannelDiscrimination.MatrixStrategyAssembly

namespace QuantumProver.SuperchannelDiscrimination.MatrixStrategyAssembly

open KrausCompletion CPWrappers

variable {I O C D R S : Type*}
  [Fintype I] [Fintype O] [Fintype C] [Fintype D] [Fintype R] [Fintype S]
  [DecidableEq I] [DecidableEq O] [DecidableEq C] [DecidableEq D]
  [DecidableEq R] [DecidableEq S]

theorem physicalFlagBlock_posSemidef {A B : Matrix O O ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) : (flagBlock A B).PosSemidef := by
  have h := (FlaggedStates.flagBlock_posSemidef hA hB).submatrix
    (fun x : O × Fin 2 => if x.2 = 0 then Sum.inl x.1 else Sum.inr x.1)
  convert h using 1
  ext ⟨o, f⟩ ⟨p, g⟩
  fin_cases f <;> fin_cases g <;> rfl

theorem physicalFlag_success_isEffect {E : Matrix O O ℂ}
    (hE : FlaggedStates.IsEffect E) : FlaggedStates.IsEffect (flagBlock E 0) := by
  constructor
  · exact physicalFlagBlock_posSemidef hE.1 Matrix.PosSemidef.zero
  · have hcomp : 1 - flagBlock E (0 : Matrix O O ℂ) = flagBlock (1 - E) 1 := by
      ext ⟨o, f⟩ ⟨p, g⟩
      fin_cases f <;> fin_cases g <;>
        simp [flagBlock, Matrix.one_apply, Matrix.sub_apply]
    rw [hcomp]
    exact physicalFlagBlock_posSemidef hE.2 Matrix.PosSemidef.one

theorem extendedFlaggedCompletion_reference_success
    (Γ : FiniteSuperchannel I O C D R)
    (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) (o₀ : O)
    (hΦ : CPTPKraus.CompletelyPositive Φ) (htrace : CPTPKraus.TraceNonincreasing Φ)
    (X : Matrix ((C × Fin 2) × S) ((C × Fin 2) × S) ℂ) :
    (CPTPKraus.amplify
      ((extendFlagSuperchannel Γ).applyChannel (flaggedInsertedChannel Φ o₀ hΦ htrace)).map
      S X).submatrix (fun x : D × S => ((x.1, 0), x.2))
        (fun x : D × S => ((x.1, 0), x.2)) =
      CPTPKraus.amplify (Γ.applyLinear Φ) S
        (CPTPKraus.amplify (discardInputFlag (I := C)) S X) := by
  ext ⟨d, s⟩ ⟨e, t⟩
  change ((extendFlagSuperchannel Γ).applyChannel
    (flaggedInsertedChannel Φ o₀ hΦ htrace)).map
      (Matrix.of (fun a b => X (a, s) (b, t))) (d, 0) (e, 0) =
    (Γ.applyLinear Φ) (discardInputFlag (Matrix.of (fun a b => X (a, s) (b, t)))) d e
  have h := congrArg (fun M : Matrix (D × Fin 2) (D × Fin 2) ℂ => M (d, 0) (e, 0))
    (extendedFlaggedCompletion_action Γ Φ o₀ hΦ htrace
      (Matrix.of (fun a b => X (a, s) (b, t))))
  simpa only [flagBlock, ite_true] using h

theorem extendedFlaggedCompletion_reference_failure
    (Γ : FiniteSuperchannel I O C D R)
    (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) (o₀ : O)
    (hΦ : CPTPKraus.CompletelyPositive Φ) (htrace : CPTPKraus.TraceNonincreasing Φ)
    (X : Matrix ((C × Fin 2) × S) ((C × Fin 2) × S) ℂ) :
    (CPTPKraus.amplify
      ((extendFlagSuperchannel Γ).applyChannel (flaggedInsertedChannel Φ o₀ hΦ htrace)).map
      S X).submatrix (fun x : D × S => ((x.1, 1), x.2))
        (fun x : D × S => ((x.1, 1), x.2)) =
      CPTPKraus.amplify (Γ.applyLinear (physicalRepair Φ o₀)) S
        (CPTPKraus.amplify (discardInputFlag (I := C)) S X) := by
  ext ⟨d, s⟩ ⟨e, t⟩
  change ((extendFlagSuperchannel Γ).applyChannel
    (flaggedInsertedChannel Φ o₀ hΦ htrace)).map
      (Matrix.of (fun a b => X (a, s) (b, t))) (d, 1) (e, 1) =
    (Γ.applyLinear (physicalRepair Φ o₀))
      (discardInputFlag (Matrix.of (fun a b => X (a, s) (b, t)))) d e
  have h := congrArg (fun M : Matrix (D × Fin 2) (D × Fin 2) ℂ => M (d, 1) (e, 1))
    (extendedFlaggedCompletion_action Γ Φ o₀ hΦ htrace
      (Matrix.of (fun a b => X (a, s) (b, t))))
  simpa [flagBlock] using h

theorem extendedFlaggedCompletion_reference_density
    (Γ : FiniteSuperchannel I O C D R)
    (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) (o₀ : O)
    (hΦ : CPTPKraus.CompletelyPositive Φ) (htrace : CPTPKraus.TraceNonincreasing Φ)
    {X : Matrix ((C × Fin 2) × S) ((C × Fin 2) × S) ℂ}
    (hX : FlaggedStates.IsDensity X) :
    FlaggedStates.IsDensity (CPTPKraus.amplify
      ((extendFlagSuperchannel Γ).applyChannel (flaggedInsertedChannel Φ o₀ hΦ htrace)).map
      S X) := by
  let T := (extendFlagSuperchannel Γ).applyChannel (flaggedInsertedChannel Φ o₀ hΦ htrace)
  refine ⟨CPTPKraus.amplify_posSemidef T.map T.completelyPositive S hX.1, ?_⟩
  rw [CPTPKraus.amplify_tracePreserving T.map T.completelyPositive T.tracePreserving S]
  exact hX.2

end QuantumProver.SuperchannelDiscrimination.MatrixStrategyAssembly

namespace QuantumProver.SuperchannelDiscrimination.MatrixStrategyAssembly.MatrixStrategies

open KrausCompletion CPWrappers

structure FiniteSystem where
  basis : Type
  finite : Fintype basis
  decidableEq : DecidableEq basis
  nonempty : Nonempty basis

attribute [instance] FiniteSystem.finite FiniteSystem.decidableEq FiniteSystem.nonempty

def FiniteSystem.prod (X Y : FiniteSystem) : FiniteSystem where
  basis := X.basis × Y.basis
  finite := inferInstance
  decidableEq := inferInstance
  nonempty := inferInstance

def extendSidePorts {I O C D R : FiniteSystem}
    (Θ : FiniteSuperchannel I.basis O.basis C.basis D.basis R.basis)
    (X Y : FiniteSystem) :
    FiniteSuperchannel (I.prod X).basis (O.prod Y).basis
      (C.prod X).basis (D.prod Y).basis R.basis where
  pre := composeChannel (reindexChannel (Equiv.prodAssoc R.basis I.basis X.basis))
    (amplifiedChannel Θ.pre X.basis)
  post := composeChannel (amplifiedChannel Θ.post Y.basis)
    (reindexChannel (Equiv.prodAssoc R.basis O.basis Y.basis).symm)

inductive NestedCircuit (I O C D : FiniteSystem) :
    FiniteSystem → FiniteSystem → ℕ → Type 1 where
  | known {X Y : FiniteSystem} (K : FiniteCPTP X.basis Y.basis) :
      NestedCircuit I O C D X Y 0
  | knownWrap {X Y U V M : FiniteSystem} {n : ℕ}
      (Γ : FiniteSuperchannel X.basis Y.basis U.basis V.basis M.basis)
      (inner : NestedCircuit I O C D X Y n) : NestedCircuit I O C D U V n
  | testedUse {X Y : FiniteSystem} {n : ℕ}
      (inner : NestedCircuit I O C D (I.prod X) (O.prod Y) n) :
      NestedCircuit I O C D (C.prod X) (D.prod Y) (n + 1)

def NestedCircuit.evaluate {I O C D R X Y : FiniteSystem} {n : ℕ}
    (Θ : FiniteSuperchannel I.basis O.basis C.basis D.basis R.basis) :
    NestedCircuit I O C D X Y n → FiniteCPTP X.basis Y.basis
  | .known K => K
  | .knownWrap Γ inner => Γ.applyChannel (inner.evaluate Θ)
  | @NestedCircuit.testedUse _ _ _ _ X Y _ inner =>
      (extendSidePorts Θ X Y).applyChannel (inner.evaluate Θ)

theorem NestedCircuit.evaluate_known {I O C D R X Y : FiniteSystem}
    (Θ : FiniteSuperchannel I.basis O.basis C.basis D.basis R.basis)
    (K : FiniteCPTP X.basis Y.basis) :
    (NestedCircuit.known (I := I) (O := O) (C := C) (D := D) K).evaluate Θ = K := rfl

theorem NestedCircuit.evaluate_knownWrap {I O C D R X Y U V M : FiniteSystem} {n : ℕ}
    (Θ : FiniteSuperchannel I.basis O.basis C.basis D.basis R.basis)
    (Γ : FiniteSuperchannel X.basis Y.basis U.basis V.basis M.basis)
    (inner : NestedCircuit I O C D X Y n) :
    (NestedCircuit.knownWrap Γ inner).evaluate Θ = Γ.applyChannel (inner.evaluate Θ) := rfl

theorem NestedCircuit.evaluate_testedUse {I O C D R X Y : FiniteSystem} {n : ℕ}
    (Θ : FiniteSuperchannel I.basis O.basis C.basis D.basis R.basis)
    (inner : NestedCircuit I O C D (I.prod X) (O.prod Y) n) :
    (NestedCircuit.testedUse inner).evaluate Θ =
      (extendSidePorts Θ X Y).applyChannel (inner.evaluate Θ) := rfl

theorem NestedCircuit.evaluate_density {I O C D R X Y : FiniteSystem} {n : ℕ}
    (Θ : FiniteSuperchannel I.basis O.basis C.basis D.basis R.basis)
    (inner : NestedCircuit I O C D X Y n) {ρ : Matrix X.basis X.basis ℂ}
    (hρ : FlaggedStates.IsDensity ρ) :
    FlaggedStates.IsDensity ((inner.evaluate Θ).map ρ) :=
  channel_density (inner.evaluate Θ) hρ.1 hρ.2

def NestedCircuit.binaryTest {I O C D R₁ R₂ X Y : FiniteSystem} {n : ℕ}
    (Θ₁ : FiniteSuperchannel I.basis O.basis C.basis D.basis R₁.basis)
    (Θ₂ : FiniteSuperchannel I.basis O.basis C.basis D.basis R₂.basis)
    (inner : NestedCircuit I O C D X Y n)
    (ρ : Matrix X.basis X.basis ℂ) (E : Matrix Y.basis Y.basis ℂ)
    (hρ : FlaggedStates.IsDensity ρ) (hE : FlaggedStates.IsEffect E) : BinaryTest where
  alpha := 1 - FlaggedStates.acceptanceProbability ((inner.evaluate Θ₁).map ρ) E
  beta := FlaggedStates.acceptanceProbability ((inner.evaluate Θ₂).map ρ) E
  alpha_nonneg := sub_nonneg.mpr
    (FlaggedStates.acceptanceProbability_bounds (inner.evaluate_density Θ₁ hρ) hE).2
  alpha_le_one := by
    linarith [(FlaggedStates.acceptanceProbability_bounds (inner.evaluate_density Θ₁ hρ) hE).1]
  beta_nonneg :=
    (FlaggedStates.acceptanceProbability_bounds (inner.evaluate_density Θ₂ hρ) hE).1
  beta_le_one :=
    (FlaggedStates.acceptanceProbability_bounds (inner.evaluate_density Θ₂ hρ) hE).2

def nestedStrategyFamily {I O C D R₁ R₂ : FiniteSystem}
    (Θ₁ : FiniteSuperchannel I.basis O.basis C.basis D.basis R₁.basis)
    (Θ₂ : FiniteSuperchannel I.basis O.basis C.basis D.basis R₂.basis) : StrategyFamily :=
  fun n => {T | ∃ (X Y : FiniteSystem) (inner : NestedCircuit I O C D X Y n)
    (ρ : Matrix X.basis X.basis ℂ) (E : Matrix Y.basis Y.basis ℂ)
    (hρ : FlaggedStates.IsDensity ρ) (hE : FlaggedStates.IsEffect E),
    T = inner.binaryTest Θ₁ Θ₂ ρ E hρ hE}

theorem nested_binaryTest_mem {I O C D R₁ R₂ X Y : FiniteSystem} {n : ℕ}
    (Θ₁ : FiniteSuperchannel I.basis O.basis C.basis D.basis R₁.basis)
    (Θ₂ : FiniteSuperchannel I.basis O.basis C.basis D.basis R₂.basis)
    (inner : NestedCircuit I O C D X Y n)
    (ρ : Matrix X.basis X.basis ℂ) (E : Matrix Y.basis Y.basis ℂ)
    (hρ : FlaggedStates.IsDensity ρ) (hE : FlaggedStates.IsEffect E) :
    inner.binaryTest Θ₁ Θ₂ ρ E hρ hE ∈ nestedStrategyFamily Θ₁ Θ₂ n :=
  ⟨X, Y, inner, ρ, E, hρ, hE, rfl⟩

end QuantumProver.SuperchannelDiscrimination.MatrixStrategyAssembly.MatrixStrategies

set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder Matrix Kronecker

namespace QuantumProver.SuperchannelDiscrimination.MatrixStrategyAssembly.MatrixStrategies

open KrausCompletion CPWrappers

def FiniteSystem.unit : FiniteSystem where
  basis := Unit
  finite := inferInstance
  decidableEq := inferInstance
  nonempty := inferInstance

def FiniteSystem.tensorPower (X : FiniteSystem) : ℕ → FiniteSystem
  | 0 => FiniteSystem.unit
  | n + 1 => X.prod (X.tensorPower n)

variable {I O J P : Type*} [Fintype I] [Fintype O] [Fintype J] [Fintype P]
  [DecidableEq I] [DecidableEq O] [DecidableEq J] [DecidableEq P]

def productChannel (Φ : FiniteCPTP I O) (Ψ : FiniteCPTP J P) :
    FiniteCPTP (I × J) (O × P) :=
  composeChannel (amplifiedLeftChannel Ψ O) (amplifiedChannel Φ J)

theorem amplifyMap_kronecker_matrix
    (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ)
    (A : Matrix I I ℂ) (B : Matrix J J ℂ) :
    amplifyMap Φ J (A ⊗ₖ B) = Φ A ⊗ₖ B := by
  ext ⟨o, j⟩ ⟨p, k⟩
  have hslice : Matrix.of (fun i l => (A ⊗ₖ B) (i, j) (l, k)) = B j k • A := by
    ext i l
    simp [Matrix.kronecker_apply, Matrix.smul_apply, mul_comm]
  change Φ (Matrix.of (fun i l => (A ⊗ₖ B) (i, j) (l, k))) o p = _
  rw [hslice, map_smul]
  simp [Matrix.smul_apply, Matrix.kronecker_apply, smul_eq_mul, mul_comm]

theorem amplifyLeftMap_kronecker_matrix
    (Ψ : Matrix J J ℂ →ₗ[ℂ] Matrix P P ℂ)
    (A : Matrix O O ℂ) (B : Matrix J J ℂ) :
    amplifyLeftMap Ψ O (A ⊗ₖ B) = A ⊗ₖ Ψ B := by
  ext ⟨o, j⟩ ⟨p, k⟩
  have hslice : Matrix.of (fun i l => (A ⊗ₖ B) (o, i) (p, l)) = A o p • B := by
    ext i l
    rfl
  change Ψ (Matrix.of (fun i l => (A ⊗ₖ B) (o, i) (p, l))) j k = _
  rw [hslice, map_smul]
  rfl

def productLinear (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ)
    (Ψ : Matrix J J ℂ →ₗ[ℂ] Matrix P P ℂ) :
    Matrix (I × J) (I × J) ℂ →ₗ[ℂ] Matrix (O × P) (O × P) ℂ :=
  (amplifyLeftMap Ψ O).comp (amplifyMap Φ J)

theorem productLinear_kronecker_matrix
    (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ)
    (Ψ : Matrix J J ℂ →ₗ[ℂ] Matrix P P ℂ)
    (A : Matrix I I ℂ) (B : Matrix J J ℂ) :
    productLinear Φ Ψ (A ⊗ₖ B) = Φ A ⊗ₖ Ψ B := by
  change amplifyLeftMap Ψ O (amplifyMap Φ J (A ⊗ₖ B)) = _
  rw [amplifyMap_kronecker_matrix, amplifyLeftMap_kronecker_matrix]

theorem disjoint_factor_maps_commute
    (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ)
    (Ψ : Matrix J J ℂ →ₗ[ℂ] Matrix P P ℂ) :
    productLinear Φ Ψ = (amplifyMap Φ P).comp (amplifyLeftMap Ψ I) := by
  apply QuantumProver.ElegantJointMeasurement.CP.linearMap_eq_of_matrix_units
  intro ⟨i, j⟩ ⟨i', j'⟩
  have hs : Matrix.single (i, j) (i', j') (1 : ℂ) =
      Matrix.single i i' (1 : ℂ) ⊗ₖ Matrix.single j j' (1 : ℂ) := by
    simpa only [one_mul] using (Matrix.single_kronecker_single i i' j j' (1 : ℂ) 1).symm
  rw [hs, productLinear_kronecker_matrix]
  change _ = amplifyMap Φ P
    (amplifyLeftMap Ψ I (Matrix.single i i' (1 : ℂ) ⊗ₖ Matrix.single j j' (1 : ℂ)))
  rw [amplifyLeftMap_kronecker_matrix, amplifyMap_kronecker_matrix]

theorem productLinear_comp_matrix
    {U V : Type*} [Fintype U] [Fintype V] [DecidableEq U] [DecidableEq V]
    (Φ₁ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ)
    (Φ₂ : Matrix O O ℂ →ₗ[ℂ] Matrix U U ℂ)
    (Ψ₁ : Matrix J J ℂ →ₗ[ℂ] Matrix P P ℂ)
    (Ψ₂ : Matrix P P ℂ →ₗ[ℂ] Matrix V V ℂ) :
    productLinear (Φ₂.comp Φ₁) (Ψ₂.comp Ψ₁) =
      (productLinear Φ₂ Ψ₂).comp (productLinear Φ₁ Ψ₁) := by
  apply QuantumProver.ElegantJointMeasurement.CP.linearMap_eq_of_matrix_units
  intro ⟨i, j⟩ ⟨i', j'⟩
  have hs : Matrix.single (i, j) (i', j') (1 : ℂ) =
      Matrix.single i i' (1 : ℂ) ⊗ₖ Matrix.single j j' (1 : ℂ) := by
    simpa only [one_mul] using (Matrix.single_kronecker_single i i' j j' (1 : ℂ) 1).symm
  rw [hs]
  simp only [LinearMap.comp_apply, productLinear_kronecker_matrix]

theorem productChannel_kronecker (Φ : FiniteCPTP I O) (Ψ : FiniteCPTP J P)
    (A : Matrix I I ℂ) (B : Matrix J J ℂ) :
    (productChannel Φ Ψ).map (A ⊗ₖ B) = Φ.map A ⊗ₖ Ψ.map B := by
  change amplifyLeftMap Ψ.map O (amplifyMap Φ.map J (A ⊗ₖ B)) = _
  rw [amplifyMap_kronecker_matrix, amplifyLeftMap_kronecker_matrix]

def pairShuffle (A B C D : Type*) : ((A × B) × (C × D)) ≃ ((A × C) × (B × D)) where
  toFun x := ((x.1.1, x.2.1), (x.1.2, x.2.2))
  invFun x := ((x.1.1, x.2.1), (x.1.2, x.2.2))
  left_inv x := by rcases x with ⟨⟨a, b⟩, ⟨c, d⟩⟩; rfl
  right_inv x := by rcases x with ⟨⟨a, c⟩, ⟨b, d⟩⟩; rfl

def unitPair : Unit ≃ Unit × Unit where
  toFun _ := ((), ())
  invFun _ := ()
  left_inv x := by cases x; rfl
  right_inv x := by rcases x with ⟨x, y⟩; cases x; cases y; rfl

def zeroParallelSuperchannel : FiniteSuperchannel Unit Unit Unit Unit Unit where
  pre := reindexChannel unitPair
  post := reindexChannel unitPair.symm

def productSuperchannel {I O C D R I' O' C' D' R' : FiniteSystem}
    (Θ : FiniteSuperchannel I.basis O.basis C.basis D.basis R.basis)
    (Ψ : FiniteSuperchannel I'.basis O'.basis C'.basis D'.basis R'.basis) :
    FiniteSuperchannel (I.prod I').basis (O.prod O').basis
      (C.prod C').basis (D.prod D').basis (R.prod R').basis where
  pre := composeChannel (reindexChannel (pairShuffle R.basis I.basis R'.basis I'.basis))
    (productChannel Θ.pre Ψ.pre)
  post := composeChannel (productChannel Θ.post Ψ.post)
    (reindexChannel (pairShuffle R.basis O.basis R'.basis O'.basis).symm)

def parallelPower {I O C D R : FiniteSystem}
    (Θ : FiniteSuperchannel I.basis O.basis C.basis D.basis R.basis) :
    (n : ℕ) → FiniteSuperchannel (I.tensorPower n).basis (O.tensorPower n).basis
      (C.tensorPower n).basis (D.tensorPower n).basis (R.tensorPower n).basis
  | 0 => zeroParallelSuperchannel
  | n + 1 => productSuperchannel Θ (parallelPower Θ n)

def parallelChannel {I O C D R : FiniteSystem}
    (Θ : FiniteSuperchannel I.basis O.basis C.basis D.basis R.basis)
    (n : ℕ) (X Y : FiniteSystem)
    (K : FiniteCPTP ((I.tensorPower n).prod X).basis ((O.tensorPower n).prod Y).basis) :
    FiniteCPTP ((C.tensorPower n).prod X).basis ((D.tensorPower n).prod Y).basis :=
  (extendSidePorts (parallelPower Θ n) X Y).applyChannel K

theorem parallelChannel_density {I O C D R : FiniteSystem}
    (Θ : FiniteSuperchannel I.basis O.basis C.basis D.basis R.basis)
    (n : ℕ) (X Y : FiniteSystem)
    (K : FiniteCPTP ((I.tensorPower n).prod X).basis ((O.tensorPower n).prod Y).basis)
    {ρ : Matrix ((C.tensorPower n).prod X).basis ((C.tensorPower n).prod X).basis ℂ}
    (hρ : FlaggedStates.IsDensity ρ) :
    FlaggedStates.IsDensity ((parallelChannel Θ n X Y K).map ρ) :=
  channel_density (parallelChannel Θ n X Y K) hρ.1 hρ.2

def physicalBinaryTest {X Y : FiniteSystem}
    (K₁ K₂ : FiniteCPTP X.basis Y.basis)
    (ρ : Matrix X.basis X.basis ℂ) (E : Matrix Y.basis Y.basis ℂ)
    (hρ : FlaggedStates.IsDensity ρ) (hE : FlaggedStates.IsEffect E) : BinaryTest where
  alpha := 1 - FlaggedStates.acceptanceProbability (K₁.map ρ) E
  beta := FlaggedStates.acceptanceProbability (K₂.map ρ) E
  alpha_nonneg := sub_nonneg.mpr
    (FlaggedStates.acceptanceProbability_bounds (channel_density K₁ hρ.1 hρ.2) hE).2
  alpha_le_one := by
    linarith [(FlaggedStates.acceptanceProbability_bounds (channel_density K₁ hρ.1 hρ.2) hE).1]
  beta_nonneg :=
    (FlaggedStates.acceptanceProbability_bounds (channel_density K₂ hρ.1 hρ.2) hE).1
  beta_le_one :=
    (FlaggedStates.acceptanceProbability_bounds (channel_density K₂ hρ.1 hρ.2) hE).2

def parallelBinaryTest {I O C D R₁ R₂ : FiniteSystem}
    (Θ₁ : FiniteSuperchannel I.basis O.basis C.basis D.basis R₁.basis)
    (Θ₂ : FiniteSuperchannel I.basis O.basis C.basis D.basis R₂.basis)
    (n : ℕ) (X Y : FiniteSystem)
    (K : FiniteCPTP ((I.tensorPower n).prod X).basis ((O.tensorPower n).prod Y).basis)
    (ρ : Matrix ((C.tensorPower n).prod X).basis ((C.tensorPower n).prod X).basis ℂ)
    (E : Matrix ((D.tensorPower n).prod Y).basis ((D.tensorPower n).prod Y).basis ℂ)
    (hρ : FlaggedStates.IsDensity ρ) (hE : FlaggedStates.IsEffect E) : BinaryTest :=
  physicalBinaryTest (parallelChannel Θ₁ n X Y K) (parallelChannel Θ₂ n X Y K) ρ E hρ hE

def parallelStrategyFamily {I O C D R₁ R₂ : FiniteSystem}
    (Θ₁ : FiniteSuperchannel I.basis O.basis C.basis D.basis R₁.basis)
    (Θ₂ : FiniteSuperchannel I.basis O.basis C.basis D.basis R₂.basis) : StrategyFamily :=
  fun n => {T | ∃ (X Y : FiniteSystem)
    (K : FiniteCPTP ((I.tensorPower n).prod X).basis ((O.tensorPower n).prod Y).basis)
    (ρ : Matrix ((C.tensorPower n).prod X).basis ((C.tensorPower n).prod X).basis ℂ)
    (E : Matrix ((D.tensorPower n).prod Y).basis ((D.tensorPower n).prod Y).basis ℂ)
    (hρ : FlaggedStates.IsDensity ρ) (hE : FlaggedStates.IsEffect E),
    T = parallelBinaryTest Θ₁ Θ₂ n X Y K ρ E hρ hE}

theorem parallel_binaryTest_mem {I O C D R₁ R₂ : FiniteSystem}
    (Θ₁ : FiniteSuperchannel I.basis O.basis C.basis D.basis R₁.basis)
    (Θ₂ : FiniteSuperchannel I.basis O.basis C.basis D.basis R₂.basis)
    (n : ℕ) (X Y : FiniteSystem)
    (K : FiniteCPTP ((I.tensorPower n).prod X).basis ((O.tensorPower n).prod Y).basis)
    (ρ : Matrix ((C.tensorPower n).prod X).basis ((C.tensorPower n).prod X).basis ℂ)
    (E : Matrix ((D.tensorPower n).prod Y).basis ((D.tensorPower n).prod Y).basis ℂ)
    (hρ : FlaggedStates.IsDensity ρ) (hE : FlaggedStates.IsEffect E) :
    parallelBinaryTest Θ₁ Θ₂ n X Y K ρ E hρ hE ∈ parallelStrategyFamily Θ₁ Θ₂ n :=
  ⟨X, Y, K, ρ, E, hρ, hE, rfl⟩

end QuantumProver.SuperchannelDiscrimination.MatrixStrategyAssembly.MatrixStrategies

namespace QuantumProver.SuperchannelDiscrimination.MatrixStrategyAssembly.MatrixBinaryTesting

open Matrix FlaggedStates KrausCompletion CPWrappers MatrixStrategies
open scoped BigOperators ComplexOrder MatrixOrder Matrix

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem measurement_entropy_dpi {ρ σ E : Matrix I I ℂ}
    (hρ : IsDensity ρ) (hσ : IsDensity σ) (hE : IsEffect E) :
    relativeEntropyBits (BinaryMeasurement.measurement E ρ)
      (BinaryMeasurement.measurement E σ) ≤ relativeEntropyBits ρ σ :=
  AbstractDPI.relativeEntropyBits_map_dpi (BinaryMeasurement.measurement E)
    ((AbstractDPI.completelyPositive_iff _).mpr
      (BinaryMeasurement.measurement_completelyPositive hE))
    (BinaryMeasurement.measurement_tracePreserving E) hρ.1 hσ.1

theorem binary_errors_entropy_dpi {ρ σ E : Matrix I I ℂ}
    (hρ : IsDensity ρ) (hσ : IsDensity σ) (hE : IsEffect E) :
    extendedBinaryRelativeEntropyBits
      (acceptanceProbability ρ E) (acceptanceProbability σ E) ≤
      relativeEntropyBits ρ σ := by
  rw [← BinaryMeasurement.measurement_relativeEntropyBits hρ hσ hE]
  exact measurement_entropy_dpi hρ hσ hE

theorem measurement_reference_entropy_dpi {E : Matrix I I ℂ}
    (hE : IsEffect E) (S : Type*) [Fintype S] [DecidableEq S]
    {ρ σ : Matrix (I × S) (I × S) ℂ}
    (hρ : IsDensity ρ) (hσ : IsDensity σ) :
    relativeEntropyBits (CPTPKraus.amplify (BinaryMeasurement.measurement E) S ρ)
      (CPTPKraus.amplify (BinaryMeasurement.measurement E) S σ) ≤
      relativeEntropyBits ρ σ := by
  exact AbstractDPI.relativeEntropyBits_map_amplify_dpi
    (BinaryMeasurement.measurement E)
    ((AbstractDPI.completelyPositive_iff _).mpr
      (BinaryMeasurement.measurement_completelyPositive hE))
    (BinaryMeasurement.measurement_tracePreserving E) S hρ.1 hσ.1

theorem typeII_floor_of_output_divergence {ρ σ E : Matrix I I ℂ}
    (hρ : IsDensity ρ) (hσ : IsDensity σ) (hE : IsEffect E)
    {ε B : ℝ} {n : ℕ} (hε : ε < 1) (hB : 0 ≤ B)
    (hα : 1 - acceptanceProbability ρ E ≤ ε)
    (hD : relativeEntropyBits ρ σ ≤ (((n : ℝ) * B : ℝ) : EReal)) :
    (2 : ℝ) ^ (-((n : ℝ) * B + 1) / (1 - ε)) ≤
      acceptanceProbability σ E := by
  have hp := acceptanceProbability_bounds hρ hE
  have hq := acceptanceProbability_bounds hσ hE
  exact typeII_lower_bound_of_extended_divergence hp.2 (by linarith) hq.1 hq.2
    hε hB ((binary_errors_entropy_dpi hρ hσ hE).trans hD)

theorem typeII_floor_of_support {ρ σ E : Matrix I I ℂ}
    (hρ : IsDensity ρ) (hσ : IsDensity σ) (hE : IsEffect E)
    (hSupport : HasSupportIn ρ σ) {ε : ℝ} (hε : ε < 1)
    (hα : 1 - acceptanceProbability ρ E ≤ ε) :
    (2 : ℝ) ^ (-(finiteRelativeEntropyBits ρ σ + 1) / (1 - ε)) ≤
      acceptanceProbability σ E := by
  have hB := Klein.finiteRelativeEntropyBits_nonneg_of_support hρ hσ hSupport
  have hD : relativeEntropyBits ρ σ ≤
      ((((1 : ℕ) : ℝ) * finiteRelativeEntropyBits ρ σ : ℝ) : EReal) := by
    simp [relativeEntropyBits, hSupport]
  simpa only [Nat.cast_one, one_mul] using
    (typeII_floor_of_output_divergence (n := 1) hρ hσ hE hε hB hα hD)

theorem physical_pair_typeII_floor {X Y : FiniteSystem}
    (Φ Ψ : FiniteCPTP X.basis Y.basis)
    (ρ : Matrix X.basis X.basis ℂ) (E : Matrix Y.basis Y.basis ℂ)
    (hρ : IsDensity ρ) (hE : IsEffect E) {ε B : ℝ} {n : ℕ}
    (hε : ε < 1) (hB : 0 ≤ B)
    (hα : (physicalBinaryTest Φ Ψ ρ E hρ hE).alpha ≤ ε)
    (hD : relativeEntropyBits (Φ.map ρ) (Ψ.map ρ) ≤
      (((n : ℝ) * B : ℝ) : EReal)) :
    (2 : ℝ) ^ (-((n : ℝ) * B + 1) / (1 - ε)) ≤
      (physicalBinaryTest Φ Ψ ρ E hρ hE).beta := by
  exact typeII_floor_of_output_divergence
    (channel_density Φ hρ.1 hρ.2) (channel_density Ψ hρ.1 hρ.2) hE hε hB hα hD

theorem nested_typeII_floor {I O C D R₁ R₂ X Y : FiniteSystem} {n : ℕ}
    (Θ₁ : FiniteSuperchannel I.basis O.basis C.basis D.basis R₁.basis)
    (Θ₂ : FiniteSuperchannel I.basis O.basis C.basis D.basis R₂.basis)
    (inner : NestedCircuit I O C D X Y n)
    (ρ : Matrix X.basis X.basis ℂ) (E : Matrix Y.basis Y.basis ℂ)
    (hρ : IsDensity ρ) (hE : IsEffect E) {ε B : ℝ}
    (hε : ε < 1) (hB : 0 ≤ B)
    (hα : (inner.binaryTest Θ₁ Θ₂ ρ E hρ hE).alpha ≤ ε)
    (hD : relativeEntropyBits ((inner.evaluate Θ₁).map ρ)
      ((inner.evaluate Θ₂).map ρ) ≤ (((n : ℝ) * B : ℝ) : EReal)) :
    (2 : ℝ) ^ (-((n : ℝ) * B + 1) / (1 - ε)) ≤
      (inner.binaryTest Θ₁ Θ₂ ρ E hρ hE).beta := by
  exact typeII_floor_of_output_divergence
    (inner.evaluate_density Θ₁ hρ) (inner.evaluate_density Θ₂ hρ) hE hε hB hα hD

theorem parallel_typeII_floor {I O C D R₁ R₂ X Y : FiniteSystem}
    (Θ₁ : FiniteSuperchannel I.basis O.basis C.basis D.basis R₁.basis)
    (Θ₂ : FiniteSuperchannel I.basis O.basis C.basis D.basis R₂.basis) (n : ℕ)
    (K : FiniteCPTP ((I.tensorPower n).basis × X.basis)
      ((O.tensorPower n).basis × Y.basis))
    (ρ : Matrix ((C.tensorPower n).basis × X.basis)
      ((C.tensorPower n).basis × X.basis) ℂ)
    (E : Matrix ((D.tensorPower n).basis × Y.basis)
      ((D.tensorPower n).basis × Y.basis) ℂ)
    (hρ : IsDensity ρ) (hE : IsEffect E) {ε B : ℝ}
    (hε : ε < 1) (hB : 0 ≤ B)
    (hα : (parallelBinaryTest Θ₁ Θ₂ n X Y K ρ E hρ hE).alpha ≤ ε)
    (hD : relativeEntropyBits ((parallelChannel Θ₁ n X Y K).map ρ)
      ((parallelChannel Θ₂ n X Y K).map ρ) ≤ (((n : ℝ) * B : ℝ) : EReal)) :
    (2 : ℝ) ^ (-((n : ℝ) * B + 1) / (1 - ε)) ≤
      (parallelBinaryTest Θ₁ Θ₂ n X Y K ρ E hρ hE).beta := by
  exact physical_pair_typeII_floor
    (X := (C.tensorPower n).prod X) (Y := (D.tensorPower n).prod Y)
    _ _ ρ E hρ hE hε hB hα hD

end QuantumProver.SuperchannelDiscrimination.MatrixStrategyAssembly.MatrixBinaryTesting

namespace QuantumProver.SuperchannelDiscrimination.MatrixStrategyAssembly

open Matrix FlaggedStates CPWrappers
open scoped BigOperators ComplexOrder MatrixOrder Matrix

variable {I O C D R : Type*}
  [Fintype I] [Fintype O] [Fintype C] [Fintype D] [Fintype R]
  [DecidableEq I] [DecidableEq O] [DecidableEq C]
  [DecidableEq D] [DecidableEq R]

theorem discardInputFlag_successFlag (A : Matrix C C ℂ) :
    discardInputFlag (flagBlock A (0 : Matrix C C ℂ)) = A := by
  ext i j
  change A i j + 0 = A i j
  exact add_zero _

theorem successFlag_isDensity {A : Matrix C C ℂ}
    (hA : IsDensity A) : IsDensity (flagBlock A (0 : Matrix C C ℂ)) := by
  constructor
  · exact physicalFlagBlock_posSemidef hA.1 Matrix.PosSemidef.zero
  · calc
      (flagBlock A (0 : Matrix C C ℂ)).trace =
          (discardInputFlag (flagBlock A (0 : Matrix C C ℂ))).trace :=
        (discardInputFlag_tracePreserving _).symm
      _ = A.trace := congrArg Matrix.trace (discardInputFlag_successFlag A)
      _ = 1 := hA.2

theorem extendedFlaggedCompletion_success_input_density
    (Γ : FiniteSuperchannel I O C D R)
    (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) (o₀ : O)
    (hΦ : CPTPKraus.CompletelyPositive Φ)
    (htrace : CPTPKraus.TraceNonincreasing Φ)
    {A : Matrix C C ℂ} (hA : IsDensity A) :
    IsDensity
      (((extendFlagSuperchannel Γ).applyChannel
        (flaggedInsertedChannel Φ o₀ hΦ htrace)).map
        (flagBlock A (0 : Matrix C C ℂ))) := by
  have hflag := successFlag_isDensity hA
  exact CPWrappers.channel_density
    ((extendFlagSuperchannel Γ).applyChannel
      (flaggedInsertedChannel Φ o₀ hΦ htrace)) hflag.1 hflag.2

theorem extendedFlaggedCompletion_acceptance_domination
    (Γ : FiniteSuperchannel I O C D R)
    (Φ Ψ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) (o₀ : O) {b c : ℝ}
    (hΦ : CPTPKraus.CompletelyPositive Φ)
    (htrace : CPTPKraus.TraceNonincreasing Φ)
    (hdom : CPTPKraus.CPDom Φ Ψ c) (hb : 0 ≤ b)
    {X : Matrix (C × Fin 2) (C × Fin 2) ℂ} {B : Matrix C C ℂ}
    (hB : B.PosSemidef)
    (hXB : ((b : ℂ) • B - discardInputFlag X).PosSemidef)
    {E : Matrix D D ℂ} (hE : E.PosSemidef) :
    acceptance
      (((extendFlagSuperchannel Γ).applyChannel
        (flaggedInsertedChannel Φ o₀ hΦ htrace)).map X)
      (flagBlock E (0 : Matrix D D ℂ)) ≤
      (b * c) * acceptance (Γ.applyLinear Ψ B) E := by
  rw [extendedFlaggedCompletion_success_acceptance Γ Φ o₀ hΦ htrace]
  exact cpDom_superchannel_state_acceptance Γ hΦ hdom hb hB hXB hE

theorem extendedFlaggedCompletion_legal_ordered_test
    (Γ : FiniteSuperchannel I O C D R)
    (Φ Ψ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) (o₀ : O) {b c : ℝ}
    (hΦ : CPTPKraus.CompletelyPositive Φ)
    (htrace : CPTPKraus.TraceNonincreasing Φ)
    (hdom : CPTPKraus.CPDom Φ Ψ c) (hb : 0 ≤ b)
    {A B : Matrix C C ℂ} (hA : IsDensity A) (hB : B.PosSemidef)
    (hAB : ((b : ℂ) • B - A).PosSemidef)
    {E : Matrix D D ℂ} (hE : IsEffect E) :
    let ρ := ((extendFlagSuperchannel Γ).applyChannel
      (flaggedInsertedChannel Φ o₀ hΦ htrace)).map
      (flagBlock A (0 : Matrix C C ℂ))
    IsDensity ρ ∧ IsEffect (flagBlock E (0 : Matrix D D ℂ)) ∧
      acceptance ρ (flagBlock E (0 : Matrix D D ℂ)) ≤
        (b * c) * acceptance (Γ.applyLinear Ψ B) E := by
  dsimp only
  refine ⟨extendedFlaggedCompletion_success_input_density Γ Φ o₀ hΦ htrace hA,
    physicalFlag_success_isEffect hE, ?_⟩
  apply extendedFlaggedCompletion_acceptance_domination Γ Φ Ψ o₀
    hΦ htrace hdom hb hB
  · simpa only [discardInputFlag_successFlag] using hAB
  · exact hE.1

end QuantumProver.SuperchannelDiscrimination.MatrixStrategyAssembly

noncomputable section

namespace QuantumProver.SuperchannelDiscrimination.MatrixStrategyAssembly.MatrixBinaryTesting

open Matrix KrausCompletion CPWrappers FlaggedStates TensorEntropy ChannelRegularization
open scoped BigOperators ComplexOrder MatrixOrder Matrix Kronecker Topology

variable {I O : Type*} [Fintype I] [Fintype O]
  [DecidableEq I] [DecidableEq O]

theorem ordinary_power_binary_entropy_le_regularized (Φ Ψ : FiniteCPTP I O)
    (n : ℕ) (R : Type*) [Fintype R] [DecidableEq R]
    {ρ : Matrix (TensorIndex I n × R) (TensorIndex I n × R) ℂ}
    {E : Matrix (TensorIndex O n × R) (TensorIndex O n × R) ℂ}
    (hρ : IsDensity ρ) (hE : IsEffect E) :
    extendedBinaryRelativeEntropyBits
      (acceptanceProbability (amplify (channelPower Φ n).map R ρ) E)
      (acceptanceProbability (amplify (channelPower Ψ n).map R ρ) E) ≤
        ((n : ℝ) : EReal) * regularizedRelativeEntropyBits Φ Ψ :=
  (binary_errors_entropy_dpi (channelPower_reference_isDensity Φ n R hρ)
    (channelPower_reference_isDensity Ψ n R hρ) hE).trans
      (channelPower_reference_entropy_le_regularized Φ Ψ n R hρ)

theorem ordinary_power_typeII_floor (Φ Ψ : FiniteCPTP I O) [Nonempty I]
    (n : ℕ) (R : Type*) [Fintype R] [DecidableEq R]
    {ρ : Matrix (TensorIndex I n × R) (TensorIndex I n × R) ℂ}
    {E : Matrix (TensorIndex O n × R) (TensorIndex O n × R) ℂ}
    (hρ : IsDensity ρ) (hE : IsEffect E) {ε B : ℝ} (hε : ε < 1)
    (hReg : regularizedRelativeEntropyBits Φ Ψ ≤ (B : EReal))
    (hα : 1 - acceptanceProbability (amplify (channelPower Φ n).map R ρ) E ≤ ε) :
    (2 : ℝ) ^ (-((n : ℝ) * B + 1) / (1 - ε)) ≤
      acceptanceProbability (amplify (channelPower Ψ n).map R ρ) E := by
  have hB : 0 ≤ B := EReal.coe_nonneg.mp
    ((regularizedRelativeEntropyBits_nonneg Φ Ψ).trans hReg)
  exact typeII_floor_of_output_divergence
    (channelPower_reference_isDensity Φ n R hρ)
    (channelPower_reference_isDensity Ψ n R hρ) hE hε hB hα
    (channelPower_reference_entropy_le_real_bound Φ Ψ n R hρ hReg)

def ordinaryPowerStrategyFamily (Φ Ψ : FiniteCPTP I O) : StrategyFamily := fun n =>
  {T | ∃ (r : ℕ)
      (ρ : Matrix (TensorIndex I n × Fin r) (TensorIndex I n × Fin r) ℂ)
      (E : Matrix (TensorIndex O n × Fin r) (TensorIndex O n × Fin r) ℂ),
    IsDensity ρ ∧ IsEffect E ∧
      T.alpha = 1 - acceptanceProbability (amplify (channelPower Φ n).map (Fin r) ρ) E ∧
      T.beta = acceptanceProbability (amplify (channelPower Ψ n).map (Fin r) ρ) E}

theorem ordinaryPowerStrategyFamily_uniformBinaryConverse (Φ Ψ : FiniteCPTP I O)
    {B : ℝ} (hReg : regularizedRelativeEntropyBits Φ Ψ ≤ (B : EReal)) :
    UniformBinaryConverse (ordinaryPowerStrategyFamily Φ Ψ) B := by
  intro n hn T hT
  rcases hT with ⟨r, ρ, E, hρ, hE, hα, hβ⟩
  rw [hα, hβ]
  simp only [sub_sub_cancel]
  exact (binary_errors_entropy_dpi (channelPower_reference_isDensity Φ n (Fin r) hρ)
    (channelPower_reference_isDensity Ψ n (Fin r) hρ) hE).trans
      (channelPower_reference_entropy_le_real_bound Φ Ψ n (Fin r) hρ hReg)

theorem ordinaryPowerStrategyFamily_orderedSteinExponent_le
    (Φ Ψ : FiniteCPTP I O) [Nonempty I] :
    orderedSteinExponent (ordinaryPowerStrategyFamily Φ Ψ) ≤
      regularizedRelativeEntropyBits Φ Ψ := by
  cases hReg : regularizedRelativeEntropyBits Φ Ψ with
  | bot => exact False.elim ((regularizedRelativeEntropyBits_ne_bot Φ Ψ) hReg)
  | top => exact le_top
  | coe B =>
      have hB : 0 ≤ B := EReal.coe_nonneg.mp (by
        simpa only [hReg] using regularizedRelativeEntropyBits_nonneg Φ Ψ)
      have hBound : regularizedRelativeEntropyBits Φ Ψ ≤ (B : EReal) := by rw [hReg]
      exact orderedSteinExponent_le_of_uniformBinaryConverse hB
        (ordinaryPowerStrategyFamily_uniformBinaryConverse Φ Ψ hBound)

end QuantumProver.SuperchannelDiscrimination.MatrixStrategyAssembly.MatrixBinaryTesting

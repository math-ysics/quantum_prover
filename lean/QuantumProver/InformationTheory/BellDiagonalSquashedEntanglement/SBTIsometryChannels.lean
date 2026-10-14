import QuantumProver.InformationTheory.BellDiagonalSquashedEntanglement.ExtensionIdentities

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open scoped Matrix ComplexOrder

namespace QuantumProver.BellDiagonalSquashedEntanglement.SBTIsometryChannels

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

def isometryExtensionChannel (V : Matrix J I ℂ) (hV : Vᴴ * V = 1) : Channel I J where
  map := QuantumProver.ElegantJointMeasurement.CP.sandwichMap V
  completelyPositive :=
    (QuantumProver.SuperchannelDiscrimination.CPTPKraus.completelyPositive_iff_EJMCP _).mpr
      (QuantumProver.ElegantJointMeasurement.CP.sandwichMap_completelyPositive V)
  tracePreserving := by
    apply (QuantumProver.ElegantJointMeasurement.CP.krausMap_trace_preserving_iff (fun _ : Unit => V)).mpr
    simpa using hV

theorem isometryExtensionChannel_action (V : Matrix J I ℂ) (hV : Vᴴ * V = 1)
    (A : Mat I) : (isometryExtensionChannel V hV).map A = V * A * Vᴴ :=
  QuantumProver.ElegantJointMeasurement.CP.sandwichMap_apply V A

theorem isometryProjection_isHermitian (V : Matrix J I ℂ) :
    (V * Vᴴ)ᴴ = V * Vᴴ := by
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]

theorem isometryProjection_idempotent (V : Matrix J I ℂ) (hV : Vᴴ * V = 1) :
    (V * Vᴴ) * (V * Vᴴ) = V * Vᴴ := by
  calc
    _ = V * (Vᴴ * V) * Vᴴ := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hV, Matrix.mul_one]

private theorem compression_completelyPositive (V : Matrix J I ℂ) :
    CompletelyPositive (QuantumProver.ElegantJointMeasurement.CP.sandwichMap Vᴴ) :=
  (QuantumProver.SuperchannelDiscrimination.CPTPKraus.completelyPositive_iff_EJMCP _).mpr
    (QuantumProver.ElegantJointMeasurement.CP.sandwichMap_completelyPositive Vᴴ)

private theorem compression_trace (V : Matrix J I ℂ) (X : Mat J) :
    (QuantumProver.ElegantJointMeasurement.CP.sandwichMap Vᴴ X).trace = ((V * Vᴴ) * X).trace := by
  rw [QuantumProver.ElegantJointMeasurement.CP.sandwichMap_apply, Matrix.conjTranspose_conjTranspose]
  exact Matrix.trace_mul_cycle Vᴴ X V

def completedCompressionChannel (V : Matrix J I ℂ) (hV : Vᴴ * V = 1)
    (o₀ : I) : Channel J I :=
  RecoveryGeometry.supportCompletionChannel (QuantumProver.ElegantJointMeasurement.CP.sandwichMap Vᴴ)
    (compression_completelyPositive V) (V * Vᴴ) (isometryProjection_isHermitian V)
    (isometryProjection_idempotent V hV) (compression_trace V) o₀

theorem completedCompressionChannel_action (V : Matrix J I ℂ) (hV : Vᴴ * V = 1)
    (o₀ : I) (X : Mat J) :
    (completedCompressionChannel V hV o₀).map X =
      Vᴴ * X * V + Matrix.single o₀ o₀ (((1 - V * Vᴴ) * X).trace) := by
  rw [completedCompressionChannel,
    RecoveryGeometry.supportCompletionChannel_action,
    QuantumProver.ElegantJointMeasurement.CP.sandwichMap_apply, Matrix.conjTranspose_conjTranspose]

theorem isometryProjection_extension (V : Matrix J I ℂ) (hV : Vᴴ * V = 1)
    (A : Mat I) : (V * Vᴴ) * (V * A * Vᴴ) = V * A * Vᴴ := by
  calc
    _ = V * (Vᴴ * V) * A * Vᴴ := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hV, Matrix.mul_one]

theorem completedCompressionChannel_extension (V : Matrix J I ℂ)
    (hV : Vᴴ * V = 1) (o₀ : I) (A : Mat I) :
    (completedCompressionChannel V hV o₀).map
      ((isometryExtensionChannel V hV).map A) = A := by
  rw [isometryExtensionChannel_action, completedCompressionChannel,
    RecoveryGeometry.supportCompletionChannel_on_supported _ _ _ _ _ _ _ _
      (isometryProjection_extension V hV A),
    QuantumProver.ElegantJointMeasurement.CP.sandwichMap_apply, Matrix.conjTranspose_conjTranspose]
  calc
    _ = (Vᴴ * V) * A * (Vᴴ * V) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hV, Matrix.one_mul, Matrix.mul_one]

theorem completedCompressionChannel_reference (V : Matrix J I ℂ)
    (hV : Vᴴ * V = 1) (o₀ : I) (σ : Mat I) :
    (completedCompressionChannel V hV o₀).map (V * σ * Vᴴ) = σ := by
  simpa only [isometryExtensionChannel_action] using
    completedCompressionChannel_extension V hV o₀ σ

theorem isometryChannels_posSemidef (V : Matrix J I ℂ) (hV : Vᴴ * V = 1)
    (o₀ : I) {A : Mat I} {X : Mat J} (hA : A.PosSemidef) (hX : X.PosSemidef) :
    ((isometryExtensionChannel V hV).map A).PosSemidef ∧
      ((completedCompressionChannel V hV o₀).map X).PosSemidef :=
  ⟨(isometryExtensionChannel V hV).posSemidef hA,
    (completedCompressionChannel V hV o₀).posSemidef hX⟩

theorem isometryChannels_trace (V : Matrix J I ℂ) (hV : Vᴴ * V = 1)
    (o₀ : I) (A : Mat I) (X : Mat J) :
    ((isometryExtensionChannel V hV).map A).trace = A.trace ∧
      ((completedCompressionChannel V hV o₀).map X).trace = X.trace :=
  ⟨(isometryExtensionChannel V hV).tracePreserving A,
    (completedCompressionChannel V hV o₀).tracePreserving X⟩

theorem rootFidelity_isometry_with_index (V : Matrix J I ℂ) (hV : Vᴴ * V = 1)
    (o₀ : I) (A B : Mat I) (hA : A.PosSemidef) (hB : B.PosSemidef) :
    rootFidelity (V * A * Vᴴ) (V * B * Vᴴ) = rootFidelity A B := by
  have hforward := RecoveryGeometry.UhlmannGeometry.rootFidelity_channel_mono
    (isometryExtensionChannel V hV) A B hA hB
  have hback := RecoveryGeometry.UhlmannGeometry.rootFidelity_channel_mono
    (completedCompressionChannel V hV o₀)
    ((isometryExtensionChannel V hV).map A) ((isometryExtensionChannel V hV).map B)
    ((isometryExtensionChannel V hV).posSemidef hA)
    ((isometryExtensionChannel V hV).posSemidef hB)
  rw [completedCompressionChannel_extension, completedCompressionChannel_extension] at hback
  exact le_antisymm (by simpa only [isometryExtensionChannel_action] using hback)
    (by simpa only [isometryExtensionChannel_action] using hforward)

theorem rootFidelity_isometry (V : Matrix J I ℂ) (hV : Vᴴ * V = 1)
    (A B : Mat I) (hA : A.PosSemidef) (hB : B.PosSemidef) :
    rootFidelity (V * A * Vᴴ) (V * B * Vᴴ) = rootFidelity A B := by
  classical
  by_cases hI : Nonempty I
  · obtain ⟨o₀⟩ := hI
    exact rootFidelity_isometry_with_index V hV o₀ A B hA hB
  · have hA0 : A = 0 := by
      ext i j
      exact False.elim (hI ⟨i⟩)
    have hB0 : B = 0 := by
      ext i j
      exact False.elim (hI ⟨i⟩)
    rw [hA0, hB0]
    simp [rootFidelity, traceNorm, sqrtPSD]

theorem rootFidelity_isometry_of_density (V : Matrix J I ℂ) (hV : Vᴴ * V = 1)
    (A B : Density I) :
    rootFidelity (V * A.val * Vᴴ) (V * B.val * Vᴴ) = rootFidelity A.val B.val := by
  obtain ⟨o₀⟩ := RecoveryGeometry.density_index_nonempty A
  exact rootFidelity_isometry_with_index V hV o₀ A.val B.val A.property.1 B.property.1

end QuantumProver.BellDiagonalSquashedEntanglement.SBTIsometryChannels

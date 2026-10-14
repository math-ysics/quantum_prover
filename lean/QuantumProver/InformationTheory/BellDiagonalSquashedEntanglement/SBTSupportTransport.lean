import QuantumProver.InformationTheory.BellDiagonalSquashedEntanglement.ExtensionIdentities

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

noncomputable section

open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Matrix

namespace QuantumProver.BellDiagonalSquashedEntanglement.SBTSupportTransport

open QuantumProver.SuperchannelDiscrimination
open QuantumProver.SuperchannelDiscrimination.FlaggedStates

variable {I O : Type*} [Fintype I] [Fintype O] [DecidableEq I] [DecidableEq O]

theorem channel_hasSupportIn (N : Channel I O) (A B : Mat I)
    (hA : A.PosSemidef) (hB : B.PosSemidef) (hs : HasSupportIn A B) :
    HasSupportIn (N.map A) (N.map B) := by
  classical
  let K := CPTPKraus.canonicalKraus N.map
  have hGram : KrausCompletion.krausGram K = 1 :=
    CPTPKraus.canonicalKraus_gram N.map N.completelyPositive N.tracePreserving
  have hRec (X : Mat I) : KrausCompletion.krausAction K X = N.map X :=
    (CPTPKraus.canonicalKraus_reconstruct N.map N.completelyPositive X).symm
  have hDPI := InputSupport.relativeEntropyBits_kraus_dpi K hGram hA hB
  rw [hRec A, hRec B] at hDPI
  by_contra hOut
  rw [(relativeEntropyBits_eq_top_iff (N.map A) (N.map B)).mpr hOut] at hDPI
  have hIn : relativeEntropyBits A B = (finiteRelativeEntropyBits A B : EReal) := by
    simp only [relativeEntropyBits, if_pos hs]
  rw [hIn] at hDPI
  exact (not_le_of_gt (EReal.coe_lt_top (finiteRelativeEntropyBits A B))) hDPI

theorem channel_supportProjection_mul_left (N : Channel I O) (A B : Mat I)
    (hA : A.PosSemidef) (hB : B.PosSemidef) (hs : HasSupportIn A B) :
    TensorEntropy.supportProjection (N.map B) * N.map A = N.map A :=
  InputSupport.supportProjection_mul_left_of_hasSupportIn
    (N.posSemidef hA).isHermitian (N.posSemidef hB).isHermitian
    (channel_hasSupportIn N A B hA hB hs)

theorem channel_supportProjection_mul_right (N : Channel I O) (A B : Mat I)
    (hA : A.PosSemidef) (hB : B.PosSemidef) (hs : HasSupportIn A B) :
    N.map A * TensorEntropy.supportProjection (N.map B) = N.map A :=
  InputSupport.supportProjection_mul_right_of_hasSupportIn
    (N.posSemidef hB).isHermitian (channel_hasSupportIn N A B hA hB hs)

theorem isDensity_isometry (V : Matrix O I ℂ) (hV : Vᴴ * V = 1)
    (A : Mat I) (hA : IsDensity A) : IsDensity (V * A * Vᴴ) := by
  exact ⟨hA.1.mul_mul_conjTranspose_same V,
    (ZeroExtension.extend_trace V hV A).trans hA.2⟩

theorem entropyBits_isometry (V : Matrix O I ℂ) (hV : Vᴴ * V = 1)
    (A : Mat I) (hA : A.IsHermitian) :
    QuantumProver.BellDiagonalSquashedEntanglement.entropyBits (V * A * Vᴴ) = QuantumProver.BellDiagonalSquashedEntanglement.entropyBits A := by
  change -EntropyContinuity.entropyTrace (ZeroExtension.extend V A) / Real.log 2 =
    -EntropyContinuity.entropyTrace A / Real.log 2
  rw [ZeroExtension.entropyTrace_extend V hV hA]

theorem finiteRelativeEntropyBits_isometry (V : Matrix O I ℂ) (hV : Vᴴ * V = 1)
    (A B : Mat I) (hA : A.IsHermitian) (hB : B.IsHermitian) :
    finiteRelativeEntropyBits (V * A * Vᴴ) (V * B * Vᴴ) =
      finiteRelativeEntropyBits A B :=
  ZeroExtension.finiteRelativeEntropyBits_extend V hV hA hB

theorem hasSupportIn_isometry_iff (V : Matrix O I ℂ) (hV : Vᴴ * V = 1)
    (A B : Mat I) :
    HasSupportIn (V * A * Vᴴ) (V * B * Vᴴ) ↔ HasSupportIn A B :=
  ZeroExtension.hasSupportIn_extend_iff V hV A B

theorem relativeEntropyBits_isometry (V : Matrix O I ℂ) (hV : Vᴴ * V = 1)
    (A B : Mat I) (hA : A.IsHermitian) (hB : B.IsHermitian) :
    relativeEntropyBits (V * A * Vᴴ) (V * B * Vᴴ) = relativeEntropyBits A B :=
  ZeroExtension.relativeEntropyBits_extend V hV hA hB

end QuantumProver.BellDiagonalSquashedEntanglement.SBTSupportTransport

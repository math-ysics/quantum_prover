import QuantumProver.InformationTheory.SuperchannelDiscrimination.ParallelPowerJoins
import QuantumProver.InformationTheory.SuperchannelDiscrimination.CommonWrapperRegularization

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace QuantumProver.SuperchannelDiscrimination.SuperchannelReferenceTransport

open Matrix KrausCompletion CPWrappers ChannelRegularization
open MatrixStrategyAssembly.MatrixStrategies

def associatedReferenceChannel {I O X Y : FiniteSystem}
    (Φ : FiniteCPTP (I.prod X).basis (O.prod Y).basis) (T : FiniteSystem) :
    FiniteCPTP (I.prod (X.prod T)).basis (O.prod (Y.prod T)).basis :=
  composeChannel (reindexChannel (Equiv.prodAssoc O.basis Y.basis T.basis))
    (composeChannel (amplifiedChannel Φ T.basis)
      (reindexChannel (Equiv.prodAssoc I.basis X.basis T.basis).symm))

theorem associatedReferenceChannel_action {I O X Y : FiniteSystem}
    (Φ : FiniteCPTP (I.prod X).basis (O.prod Y).basis) (T : FiniteSystem)
    (A : Matrix ((I.prod X).prod T).basis ((I.prod X).prod T).basis ℂ) :
    (associatedReferenceChannel Φ T).map
        (reindexMap (Equiv.prodAssoc I.basis X.basis T.basis) A) =
      reindexMap (Equiv.prodAssoc O.basis Y.basis T.basis)
        (CPTPKraus.amplify Φ.map T.basis A) := by
  ext ⟨o, ⟨y, t⟩⟩ ⟨p, ⟨z, u⟩⟩
  rfl

theorem regularized_associatedReferenceChannel_le {I O X Y : FiniteSystem}
    (Φ Ψ : FiniteCPTP (I.prod X).basis (O.prod Y).basis) (T : FiniteSystem) :
    regularizedRelativeEntropyBits (associatedReferenceChannel Φ T)
        (associatedReferenceChannel Ψ T) ≤ regularizedRelativeEntropyBits Φ Ψ := by
  exact (regularizedRelativeEntropyBits_sandwich_le
    (amplifiedChannel Φ T.basis) (amplifiedChannel Ψ T.basis)
    (reindexChannel (Equiv.prodAssoc I.basis X.basis T.basis).symm)
    (reindexChannel (Equiv.prodAssoc O.basis Y.basis T.basis))).trans
      (regularizedRelativeEntropyBits_amplified_le Φ Ψ)

theorem matrix_slot_reference_intertwine {I O C D R X Y : FiniteSystem}
    (Θ : FiniteSuperchannel I.basis O.basis C.basis D.basis R.basis)
    (Φ : FiniteCPTP (I.prod X).basis (O.prod Y).basis) (T : FiniteSystem)
    (A : Matrix ((C.prod X).prod T).basis ((C.prod X).prod T).basis ℂ) :
    ((extendSidePorts Θ (X.prod T) (Y.prod T)).applyChannel
        (associatedReferenceChannel Φ T)).map
      (reindexMap (Equiv.prodAssoc C.basis X.basis T.basis) A) =
      reindexMap (Equiv.prodAssoc D.basis Y.basis T.basis)
        (CPTPKraus.amplify ((extendSidePorts Θ X Y).applyChannel Φ).map T.basis A) := by
  ext ⟨d, ⟨y, t⟩⟩ ⟨e, ⟨z, u⟩⟩
  rfl

end QuantumProver.SuperchannelDiscrimination.SuperchannelReferenceTransport

import QuantumProver.InformationTheory.AmplitudeDamping.SecretKey.InitialSeedAncillas
import QuantumProver.InformationTheory.AmplitudeDamping.SecretKey.ProtocolReadout

set_option autoImplicit false

noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix Kronecker

namespace QuantumProver.AmplitudeDamping.SecretKey.SeedKeyReadoutTransport

open InitialSeed InitialSeedAncillas PhysicalProtocol PhysicalProtocol.FiniteKeyProtocol

section GenericReadout

variable {H I R K E F : Type*}
  [Fintype H] [Fintype I] [Fintype R] [Fintype K] [Fintype E] [Fintype F]
  [DecidableEq H] [DecidableEq I] [DecidableEq R] [DecidableEq K]
  [DecidableEq E] [DecidableEq F]

def forgetHonestMemory (eH : H ≃ R × I) (eE : E ≃ F)
    (σ : Matrix (H × E) (H × E) ℂ) : Matrix (I × F) (I × F) ℂ :=
  partialTraceLeft (σ.submatrix
    ((eH.prodCongr eE).trans (Equiv.prodAssoc R I F)).symm
    ((eH.prodCongr eE).trans (Equiv.prodAssoc R I F)).symm)

theorem basisReadout_forgetHonestMemory (eH : H ≃ R × I) (eE : E ≃ F)
    (label : I → K) (σ : Matrix (H × E) (H × E) ℂ) :
    ((basisReadoutChannel (fun h => label (eH h).2)).withRightMemory E).eval σ =
      (((basisReadoutChannel label).withRightMemory F).eval
        (forgetHonestMemory eH eE σ)).submatrix
          ((Equiv.refl K).prodCongr eE) ((Equiv.refl K).prodCongr eE) := by
  ext x y
  rcases x with ⟨k,u⟩
  rcases y with ⟨k',u'⟩
  rw [PublicHistory.reference_basisReadout_apply_B]
  change (∑ h, if k = label (eH h).2 ∧ k' = label (eH h).2
    then σ (h,u) (h,u') else 0) =
      ((basisReadoutChannel label).withRightMemory F).eval
        (forgetHonestMemory eH eE σ) (k,eE u) (k',eE u')
  rw [PublicHistory.reference_basisReadout_apply_B]
  rw [← eH.symm.sum_comp
    (fun h => if k = label (eH h).2 ∧ k' = label (eH h).2
      then σ (h,u) (h,u') else 0), Fintype.sum_prod_type]
  simp only [Equiv.apply_symm_apply, forgetHonestMemory, partialTraceLeft,
    Matrix.submatrix_apply, Equiv.symm_trans_apply, Equiv.prodAssoc_symm_apply,
    Equiv.prodCongr_symm, Equiv.prodCongr_apply, Prod.map_apply, Equiv.symm_apply_apply]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero]

end GenericReadout

variable {E K : Type*} [Fintype E] [Fintype K] [DecidableEq E] [DecidableEq K]

def aliceReadoutLabel (c a b : ℕ) (label : Fin a × Fin b → K) :
    Fin (c * a) × Fin b → K :=
  fun x => label (privateAliceJointEquiv c a b x).2

def bobReadoutLabel (c a b : ℕ) (label : Fin a × Fin b → K) :
    Fin a × Fin (c * b) → K :=
  fun x => label (privateBobJointEquiv c a b x).2

theorem aliceReadout_forget {p : ℝ} {a b af bf : ℕ} (c : ℕ)
    (P : FiniteKeyProtocol p a b af bf) (label : Fin af × Fin bf → K)
    (σ : Matrix ((Fin (c * af) × Fin bf) × ((withPrivateAlice c P).Environment × E))
      ((Fin (c * af) × Fin bf) × ((withPrivateAlice c P).Environment × E)) ℂ) :
    ((basisReadoutChannel (aliceReadoutLabel c af bf label)).withRightMemory
      ((withPrivateAlice c P).Environment × E)).eval σ =
      (((basisReadoutChannel label).withRightMemory (P.Environment × E)).eval
        (forgetPrivateAliceOutput c P σ)).submatrix
          ((Equiv.refl K).prodCongr ((privateAliceEnvironmentEquiv c P).prodCongr (Equiv.refl E)))
          ((Equiv.refl K).prodCongr ((privateAliceEnvironmentEquiv c P).prodCongr (Equiv.refl E))) :=
  basisReadout_forgetHonestMemory (privateAliceJointEquiv c af bf)
    ((privateAliceEnvironmentEquiv c P).prodCongr (Equiv.refl E)) label σ

theorem bobReadout_forget {p : ℝ} {a b af bf : ℕ} (c : ℕ)
    (P : FiniteKeyProtocol p a b af bf) (label : Fin af × Fin bf → K)
    (σ : Matrix ((Fin af × Fin (c * bf)) × ((withPrivateBob c P).Environment × E))
      ((Fin af × Fin (c * bf)) × ((withPrivateBob c P).Environment × E)) ℂ) :
    ((basisReadoutChannel (bobReadoutLabel c af bf label)).withRightMemory
      ((withPrivateBob c P).Environment × E)).eval σ =
      (((basisReadoutChannel label).withRightMemory (P.Environment × E)).eval
        (forgetPrivateBobOutput c P σ)).submatrix
          ((Equiv.refl K).prodCongr ((privateBobEnvironmentEquiv c P).prodCongr (Equiv.refl E)))
          ((Equiv.refl K).prodCongr ((privateBobEnvironmentEquiv c P).prodCongr (Equiv.refl E))) :=
  basisReadout_forgetHonestMemory (privateBobJointEquiv c af bf)
    ((privateBobEnvironmentEquiv c P).prodCongr (Equiv.refl E)) label σ

def seedPureEnvironmentEquiv {p : ℝ} {s c e f af bf : ℕ}
    (P : FiniteKeyProtocol p (s * c) (s * e) af bf) :
    (seedPureProtocol (f := f) P).Environment ≃ P.Environment :=
  (privateAliceEnvironmentEquiv s (withPrivateAlice (c * f) (withPrivateBob e P))).trans
    ((privateAliceEnvironmentEquiv (c * f) (withPrivateBob e P)).trans
      (privateBobEnvironmentEquiv e P))

def seedPureEveEquiv {p : ℝ} {s c e f af bf : ℕ}
    (P : FiniteKeyProtocol p (s * c) (s * e) af bf) :
    ((seedPureProtocol (f := f) P).Environment × Fin f) ≃ (P.Environment × Fin f) :=
  (seedPureEnvironmentEquiv P).prodCongr (Equiv.refl (Fin f))

def seedAliceKeyLabel {s c f af k : ℕ} (label : Fin af → Fin k) :
    Fin (s * ((c * f) * af)) → Fin k :=
  fun x => label (privateAliceLocalEquiv (c * f) af
    (privateAliceLocalEquiv s ((c * f) * af) x).2).2

def seedBobKeyLabel {e bf k : ℕ} (label : Fin bf → Fin k) :
    Fin (e * bf) → Fin k := fun x => label (privateAliceLocalEquiv e bf x).2

theorem seedReadout_forget {p : ℝ} {s c e f af bf k : ℕ}
    (P : FiniteKeyProtocol p (s * c) (s * e) af bf)
    (labelA : Fin af → Fin k) (labelB : Fin bf → Fin k)
    (σ : Matrix ((Fin (s * ((c * f) * af)) × Fin (e * bf)) ×
      ((seedPureProtocol (f := f) P).Environment × Fin f))
      ((Fin (s * ((c * f) * af)) × Fin (e * bf)) ×
      ((seedPureProtocol (f := f) P).Environment × Fin f)) ℂ) :
    ((basisReadoutChannel (fun x =>
      (seedAliceKeyLabel labelA x.1, seedBobKeyLabel labelB x.2))).withRightMemory
      ((seedPureProtocol (f := f) P).Environment × Fin f)).eval σ =
      (((basisReadoutChannel (fun x : Fin af × Fin bf => (labelA x.1,labelB x.2))).withRightMemory
        (P.Environment × Fin f)).eval
        (forgetPrivateBobOutput e P
          (forgetPrivateAliceOutput (c * f) (withPrivateBob e P)
            (forgetPrivateAliceOutput s (withPrivateAlice (c * f) (withPrivateBob e P)) σ)))).submatrix
        ((Equiv.refl (Fin k × Fin k)).prodCongr (seedPureEveEquiv P))
        ((Equiv.refl (Fin k × Fin k)).prodCongr (seedPureEveEquiv P)) := by
  dsimp only [seedPureProtocol] at σ ⊢
  change ((basisReadoutChannel
    (aliceReadoutLabel s ((c * f) * af) (e * bf)
      (aliceReadoutLabel (c * f) af (e * bf)
        (bobReadoutLabel e af bf (fun x => (labelA x.1,labelB x.2)))))).withRightMemory
          ((withPrivateAlice s (withPrivateAlice (c * f) (withPrivateBob e P))).Environment × Fin f)).eval σ = _
  rw [aliceReadout_forget, aliceReadout_forget, bobReadout_forget]
  ext x y
  rfl

theorem seedPureProtocol_finalKeyState {p : ℝ} {s c e f af bf k : ℕ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (P : FiniteKeyProtocol p (s * c) (s * e) af bf)
    (labelA : Fin af → Fin k) (labelB : Fin bf → Fin k)
    (a : ProbabilityLaw (Fin s)) (ρA : Density (Fin c)) (ρB : Density (Fin e))
    (ξ : Density (Fin f)) :
    (seedPureProtocol (f := f) P).finalKeyStateWithPriorEveLabels hp0 hp1
      (seedAliceKeyLabel labelA) (seedBobKeyLabel labelB) (Fin f)
        (seedPureMatrixInput a ρA ρB ξ) =
      (P.finalKeyStateWithPriorEveLabels hp0 hp1 labelA labelB (Fin f)
        ((copiedSeedAncillas a ρA ρB).tensor ξ)).relabel
          ((Equiv.refl (Fin k × Fin k)).prodCongr (seedPureEveEquiv P)) := by
  apply Density.eq_of_mat_eq
  change ((basisReadoutChannel (fun x =>
    (seedAliceKeyLabel labelA x.1,seedBobKeyLabel labelB x.2))).withRightMemory
      ((seedPureProtocol (f := f) P).Environment × Fin f)).eval
      (PublicHistory.localPriorEveMatrix_B (seedPureProtocol (f := f) P)
        (seedPureMatrixInput a ρA ρB ξ).mat) = _
  rw [seedReadout_forget, seedPureProtocol_physical_output]
  rfl

end QuantumProver.AmplitudeDamping.SecretKey.SeedKeyReadoutTransport

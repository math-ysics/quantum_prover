import QuantumProver.InformationTheory.DepolarizingSquashedEntanglement.BCYNonlockability
import QuantumProver.InformationTheory.DepolarizingSquashedEntanglement.BCYERContinuity
import QuantumProver.InformationTheory.DepolarizingSquashedEntanglement.BCYTensorRegularization

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

noncomputable section

open Matrix Set Filter
open scoped Topology BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker

namespace QuantumProver.DepolarizingSquashedEntanglement.BCYRedistributionCode

open BCYRelativeEntropy BCYNonlockability BCYERContinuity

variable {A B E D F G I J : Type*}
  [Fintype A] [Fintype B] [Fintype E] [Fintype D] [Fintype F] [Fintype G]
  [Fintype I] [Fintype J]
  [DecidableEq A] [DecidableEq B] [DecidableEq E] [DecidableEq D]
  [DecidableEq F] [DecidableEq G] [DecidableEq I] [DecidableEq J]

def appendRightChannel (τ : Density J) : CPTP I (I × J) where
  map := (Matrix.kroneckerBilinear : QMatrix I →ₗ[ℂ]
    QMatrix J →ₗ[ℂ] QMatrix (I × J)).flip τ.matrix
  completelyPositive := by
    intro n R hR
    exact (hR.kronecker τ.positive).submatrix (Equiv.prodAssoc (Fin n) I J).symm
  tracePreserving := by
    intro R
    change Matrix.trace (R ⊗ₖ τ.matrix) = Matrix.trace R
    rw [Matrix.trace_kronecker, τ.trace_one, mul_one]

def discardRightChannel (I J : Type*) [Fintype I] [Fintype J] : CPTP (I × J) I where
  map := {
    toFun := partialTraceRight
    map_add' := by
      intro R S
      ext i j
      simp [partialTraceRight, QuantumProver.WernerEndpoint.partialTraceLeft, Finset.sum_add_distrib]
    map_smul' := by
      intro z R
      ext i j
      simp [partialTraceRight, QuantumProver.WernerEndpoint.partialTraceLeft, Finset.mul_sum] }
  completelyPositive := by
    intro n R hR
    exact partialTraceRight_positive
      (hR.submatrix (Equiv.prodAssoc (Fin n) I J))
  tracePreserving := partialTraceRight_trace

theorem local_append_density (ρ : Density (A × E)) (τ : Density B) :
    (localRightChannel (appendRightChannel (I := E) τ)).onDensity ρ =
      appendLocalDensity ρ τ := by
  apply density_ext
  ext i j
  rfl

theorem local_discard_density (ρ : Density (A × (E × B))) :
    (localRightChannel (discardRightChannel E B)).onDensity ρ =
      discardLastDensity ρ := by
  apply density_ext
  ext i j
  rfl

theorem discard_append_density (ρ : Density (A × E)) (τ : Density B) :
    discardLastDensity (appendLocalDensity ρ τ) = ρ := by
  apply density_ext
  ext i j
  change (∑ b, ρ.matrix i j * τ.matrix b b) = ρ.matrix i j
  rw [← Finset.mul_sum]
  change ρ.matrix i j * Matrix.trace τ.matrix = ρ.matrix i j
  rw [τ.trace_one, mul_one]

theorem erReal_localRight_mono (Φ : CPTP I J) (ρ : Density (A × I)) :
    relativeEntropyEntanglementReal ((localRightChannel Φ).onDensity ρ) ≤
      relativeEntropyEntanglementReal ρ := by
  have h := relativeEntropyEntanglementNat_localRight_mono Φ ρ
  rw [← coe_relativeEntropyEntanglementReal, ← coe_relativeEntropyEntanglementReal] at h
  exact_mod_cast h

theorem erReal_append_local (ρ : Density (A × E)) (τ : Density B) :
    relativeEntropyEntanglementReal (appendLocalDensity ρ τ) =
      relativeEntropyEntanglementReal ρ := by
  apply le_antisymm
  · have h := erReal_localRight_mono (appendRightChannel (I := E) τ) ρ
    rw [local_append_density] at h
    exact h
  · have h := erReal_localRight_mono (discardRightChannel E B)
      (appendLocalDensity ρ τ)
    rw [local_discard_density, discard_append_density] at h
    exact h

structure FiniteCode (B E D F G : Type*)
    [Fintype B] [Fintype E] [Fintype D] [Fintype F] [Fintype G] where
  encoder : CPTP ((B × E) × D) ((E × F) × G)
  recovery : CPTP ((E × F) × G) (B × E)

namespace FiniteCode

variable [Nonempty D] [Nonempty F]

def encoded (C : FiniteCode B E D F G) (ρ : Density (A × (B × E))) :
    Density (A × ((E × F) × G)) :=
  (localRightChannel C.encoder).onDensity (appendLocalDensity ρ (uniformDensity D))

def recovered (C : FiniteCode B E D F G) (ρ : Density (A × (B × E))) :
    Density (A × (B × E)) :=
  (localRightChannel C.recovery).onDensity (C.encoded ρ)

def retained (C : FiniteCode B E D F G) (ρ : Density (A × (B × E))) :
    Density (A × (E × F)) := discardLastDensity (C.encoded ρ)

def reference (ρ : Density (A × (B × E))) : Density (A × (E × F)) :=
  appendLocalDensity (discardMiddleDensity ρ) (uniformDensity F)

def recoveryError (C : FiniteCode B E D F G) (ρ : Density (A × (B × E))) : ℝ :=
  QuantumProver.ConditionalEntropy.traceDistance (C.recovered ρ).matrix ρ.matrix

def sideError (C : FiniteCode B E D F G) (ρ : Density (A × (B × E))) : ℝ :=
  QuantumProver.ConditionalEntropy.traceDistance (C.retained ρ).matrix
    (reference (F := F) ρ).matrix

def communicationCost (_C : FiniteCode B E D F G) : ℝ := Real.log (Fintype.card G : ℝ)

def inputResourceCost (_C : FiniteCode B E D F G) : ℝ := Real.log (Fintype.card D : ℝ)

def outputResourceCost (_C : FiniteCode B E D F G) : ℝ := Real.log (Fintype.card F : ℝ)

omit [Nonempty F] in
theorem encoded_er_le (C : FiniteCode B E D F G) (ρ : Density (A × (B × E))) :
    relativeEntropyEntanglementReal (C.encoded ρ) ≤ relativeEntropyEntanglementReal ρ := by
  have h := erReal_localRight_mono C.encoder (appendLocalDensity ρ (uniformDensity D))
  rw [erReal_append_local] at h
  exact h

omit [Nonempty F] in
theorem recovered_er_le (C : FiniteCode B E D F G) (ρ : Density (A × (B × E))) :
    relativeEntropyEntanglementReal (C.recovered ρ) ≤
      relativeEntropyEntanglementReal (C.encoded ρ) :=
  erReal_localRight_mono C.recovery (C.encoded ρ)

theorem erReal_difference_le_signed_errors (C : FiniteCode B E D F G)
    (ρ : Density (A × (B × E))) :
    relativeEntropyEntanglementReal ρ -
        relativeEntropyEntanglementReal (discardMiddleDensity ρ) ≤
      2*C.communicationCost +
        (relativeEntropyEntanglementReal ρ - relativeEntropyEntanglementReal (C.recovered ρ)) +
        (relativeEntropyEntanglementReal (C.retained ρ) -
          relativeEntropyEntanglementReal (reference (F := F) ρ)) := by
  have hm := C.recovered_er_le ρ
  have hg := relativeEntropyEntanglementReal_nonlockability_last (C.encoded ρ)
  have he : relativeEntropyEntanglementReal (reference (F := F) ρ) =
      relativeEntropyEntanglementReal (discardMiddleDensity ρ) :=
    erReal_append_local _ _
  change relativeEntropyEntanglementReal (C.encoded ρ) ≤
    relativeEntropyEntanglementReal (C.retained ρ) +
      2*Real.log (Fintype.card G : ℝ) at hg
  rw [he]
  unfold communicationCost
  linarith

theorem erReal_difference_le (C : FiniteCode B E D F G)
    (ρ : Density (A × (B × E))) :
    relativeEntropyEntanglementReal ρ -
        relativeEntropyEntanglementReal (discardMiddleDensity ρ) ≤
      2*C.communicationCost + continuityBound A (C.recoveryError ρ) +
        continuityBound A (C.sideError ρ) := by
  have hr := erReal_continuity (C.recovered ρ) ρ (le_refl (C.recoveryError ρ))
  have hs := erReal_continuity (C.retained ρ) (reference (F := F) ρ)
    (le_refl (C.sideError ρ))
  have hm := C.recovered_er_le ρ
  have hg := relativeEntropyEntanglementReal_nonlockability_last (C.encoded ρ)
  have he : relativeEntropyEntanglementReal (reference (F := F) ρ) =
      relativeEntropyEntanglementReal (discardMiddleDensity ρ) :=
    erReal_append_local _ _
  have hr' := (abs_le.mp hr).1
  have hs' := (abs_le.mp hs).2
  change relativeEntropyEntanglementReal (C.encoded ρ) ≤
    relativeEntropyEntanglementReal (C.retained ρ) +
      2*Real.log (Fintype.card G : ℝ) at hg
  rw [he] at hs'
  unfold communicationCost
  linarith

end FiniteCode

def tripleCopies (ρ : Density (A × (B × E))) (n : ℕ) :
    Density (CopyIndex A n × (CopyIndex B n × CopyIndex E n)) :=
  densityReindex (Equiv.prodCongr (Equiv.refl (CopyIndex A n)) (copyGrouping B E n))
    (tensorCopies ρ n)

theorem tripleCopies_succ_apply (ρ : Density (A × (B × E))) (n : ℕ)
    (a a' : CopyIndex A n) (b b' : CopyIndex B n) (e e' : CopyIndex E n)
    (i i' : A) (j j' : B) (k k' : E) :
    (tripleCopies ρ (n+1)).matrix ((a,i),((b,j),(e,k))) ((a',i'),((b',j'),(e',k'))) =
      (tripleCopies ρ n).matrix (a,(b,e)) (a',(b',e')) * ρ.matrix (i,(j,k)) (i',(j',k')) := rfl

theorem erReal_tripleCopies (ρ : Density (A × (B × E))) (n : ℕ) :
    relativeEntropyEntanglementReal (tripleCopies ρ n) =
      relativeEntropyEntanglementReal (tensorCopies ρ n) :=
  relativeEntropyEntanglementReal_reindex _ _ _

theorem discardMiddle_tripleCopies (ρ : Density (A × (B × E))) (n : ℕ) :
    discardMiddleDensity (tripleCopies ρ n) = tensorCopies (discardMiddleDensity ρ) n := by
  induction n with
  | zero =>
      apply density_ext
      ext i j
      rcases i with ⟨a,e⟩
      rcases j with ⟨a',e'⟩
      cases a
      cases a'
      cases e
      cases e'
      change (∑ _ : PUnit, (1 : ℂ)) = 1
      simp
  | succ n ih =>
      apply density_ext
      ext x y
      rcases x with ⟨⟨a,i⟩,⟨e,k⟩⟩
      rcases y with ⟨⟨a',i'⟩,⟨e',k'⟩⟩
      have hi := congrArg (fun R : Density (CopyIndex A n × CopyIndex E n) =>
        R.matrix (a,e) (a',e')) ih
      rw [discardMiddleDensity_matrix] at hi
      rw [discardMiddleDensity_matrix, tensorCopies_succ_apply]
      change (∑ b : CopyIndex B n × B,
        (tripleCopies ρ (n+1)).matrix ((a,i),(b,(e,k))) ((a',i'),(b,(e',k')))) =
        (tensorCopies (discardMiddleDensity ρ) n).matrix (a,e) (a',e') *
          (∑ j : B, ρ.matrix (i,(j,k)) (i',(j,k')))
      simp only [Fintype.sum_prod_type, tripleCopies_succ_apply, ← Finset.mul_sum,
        ← Finset.sum_mul]
      change (∑ b : CopyIndex B n,
        (tripleCopies ρ n).matrix (a,(b,e)) (a',(b,e'))) =
          (tensorCopies (discardMiddleDensity ρ) n).matrix (a,e) (a',e') at hi
      exact congrArg (fun z : ℂ => z * ∑ j : B, ρ.matrix (i,(j,k)) (i',(j,k'))) hi

theorem tendsto_erReal_tripleCopies_rate (ρ : Density (A × (B × E))) :
    Tendsto (fun n => relativeEntropyEntanglementReal (tripleCopies ρ n)/(n : ℝ))
      atTop (𝓝 (regularizedRelativeEntropyEntanglementNat ρ)) := by
  simpa only [erReal_tripleCopies] using tendsto_relativeEntropyEntanglement_rate ρ

section CodeRates

variable {Dreg Freg Greg : ℕ → Type*}
  [∀ n, Fintype (Dreg n)] [∀ n, Fintype (Freg n)] [∀ n, Fintype (Greg n)]
  [∀ n, DecidableEq (Dreg n)] [∀ n, DecidableEq (Freg n)] [∀ n, DecidableEq (Greg n)]
  [∀ n, Nonempty (Dreg n)] [∀ n, Nonempty (Freg n)]

theorem encoded_er_rate
    (ρ : Density (A × (B × E)))
    (C : ∀ n, FiniteCode (CopyIndex B n) (CopyIndex E n) (Dreg n) (Freg n) (Greg n))
    (hRecovery : Tendsto (fun n => (C n).recoveryError (tripleCopies ρ n)) atTop (𝓝 0)) :
    Tendsto (fun n => relativeEntropyEntanglementReal ((C n).encoded (tripleCopies ρ n))/(n : ℝ))
      atTop (𝓝 (regularizedRelativeEntropyEntanglementNat ρ)) := by
  have hr := erReal_continuity_copy_rate (A := A)
    (fun n => (C n).recovered (tripleCopies ρ n)) (fun n => tripleCopies ρ n) hRecovery
  have hInverse : Tendsto (fun n =>
      (relativeEntropyEntanglementReal (tripleCopies ρ n) -
        relativeEntropyEntanglementReal ((C n).recovered (tripleCopies ρ n)))/(n : ℝ))
        atTop (𝓝 0) := by
    simpa only [← neg_div, neg_sub, neg_zero] using hr.neg
  have hDifference : Tendsto (fun n =>
      (relativeEntropyEntanglementReal (tripleCopies ρ n) -
        relativeEntropyEntanglementReal ((C n).encoded (tripleCopies ρ n)))/(n : ℝ))
        atTop (𝓝 0) := by
    apply squeeze_zero' ?_ ?_ hInverse
    · exact Filter.Eventually.of_forall (fun n => div_nonneg
        (sub_nonneg.mpr ((C n).encoded_er_le _)) (Nat.cast_nonneg n))
    · exact Filter.Eventually.of_forall (fun n => div_le_div_of_nonneg_right
        (sub_le_sub_left ((C n).recovered_er_le _) _) (Nat.cast_nonneg n))
  have h := (tendsto_erReal_tripleCopies_rate ρ).sub hDifference
  simp only [sub_zero] at h
  convert h using 1
  ext n
  ring

theorem retained_er_rate
    (ρ : Density (A × (B × E)))
    (C : ∀ n, FiniteCode (CopyIndex B n) (CopyIndex E n) (Dreg n) (Freg n) (Greg n))
    (hSide : Tendsto (fun n => (C n).sideError (tripleCopies ρ n)) atTop (𝓝 0)) :
    Tendsto (fun n => relativeEntropyEntanglementReal ((C n).retained (tripleCopies ρ n))/(n : ℝ))
      atTop (𝓝 (regularizedRelativeEntropyEntanglementNat (discardMiddleDensity ρ))) := by
  have hs := erReal_continuity_copy_rate (A := A)
    (fun n => (C n).retained (tripleCopies ρ n))
    (fun n => FiniteCode.reference (F := Freg n) (tripleCopies ρ n)) hSide
  have hReference : Tendsto (fun n =>
      relativeEntropyEntanglementReal
        (FiniteCode.reference (F := Freg n) (tripleCopies ρ n))/(n : ℝ))
      atTop (𝓝 (regularizedRelativeEntropyEntanglementNat (discardMiddleDensity ρ))) := by
    simpa only [FiniteCode.reference, erReal_append_local, discardMiddle_tripleCopies] using
      tendsto_relativeEntropyEntanglement_rate (discardMiddleDensity ρ)
  have h := hReference.add hs
  simp only [add_zero] at h
  convert h using 1
  ext n
  ring

end CodeRates

theorem regularized_difference_le_communication_rate
    {Dreg Freg Greg : ℕ → Type*}
    [∀ n, Fintype (Dreg n)] [∀ n, Fintype (Freg n)] [∀ n, Fintype (Greg n)]
    [∀ n, DecidableEq (Dreg n)] [∀ n, DecidableEq (Freg n)] [∀ n, DecidableEq (Greg n)]
    [∀ n, Nonempty (Dreg n)] [∀ n, Nonempty (Freg n)]
    (ρ : Density (A × (B × E)))
    (C : ∀ n, FiniteCode (CopyIndex B n) (CopyIndex E n) (Dreg n) (Freg n) (Greg n))
    {q : ℝ}
    (hRecovery : Tendsto (fun n => (C n).recoveryError (tripleCopies ρ n)) atTop (𝓝 0))
    (hSide : Tendsto (fun n => (C n).sideError (tripleCopies ρ n)) atTop (𝓝 0))
    (hCommunication : Tendsto (fun n => (C n).communicationCost/(n : ℝ)) atTop (𝓝 q)) :
    regularizedRelativeEntropyEntanglementNat ρ -
        regularizedRelativeEntropyEntanglementNat (discardMiddleDensity ρ) ≤ 2*q := by
  have hRecoveryRate := erReal_continuity_copy_rate (A := A)
    (fun n => (C n).recovered (tripleCopies ρ n)) (fun n => tripleCopies ρ n) hRecovery
  have hInverseRate : Tendsto (fun n =>
      (relativeEntropyEntanglementReal (tripleCopies ρ n) -
        relativeEntropyEntanglementReal ((C n).recovered (tripleCopies ρ n)))/(n : ℝ))
        atTop (𝓝 0) := by
    simpa only [← neg_div, neg_sub, neg_zero] using hRecoveryRate.neg
  have hSideRate := erReal_continuity_copy_rate (A := A)
    (fun n => (C n).retained (tripleCopies ρ n))
    (fun n => FiniteCode.reference (F := Freg n) (tripleCopies ρ n)) hSide
  have hCommunicationRate : Tendsto (fun n => 2*(C n).communicationCost/(n : ℝ))
      atTop (𝓝 (2*q)) := by
    simpa only [mul_div_assoc] using hCommunication.const_mul 2
  have hBound := (hCommunicationRate.add hInverseRate).add hSideRate
  simp only [add_zero] at hBound
  have hLeft : Tendsto (fun n =>
      (relativeEntropyEntanglementReal (tripleCopies ρ n) -
        relativeEntropyEntanglementReal (discardMiddleDensity (tripleCopies ρ n)))/(n : ℝ))
      atTop (𝓝 (regularizedRelativeEntropyEntanglementNat ρ -
        regularizedRelativeEntropyEntanglementNat (discardMiddleDensity ρ))) := by
    simpa only [sub_div, discardMiddle_tripleCopies] using
      (tendsto_erReal_tripleCopies_rate ρ).sub
        (tendsto_relativeEntropyEntanglement_rate (discardMiddleDensity ρ))
  apply le_of_tendsto_of_tendsto hLeft hBound
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have h := (C n).erReal_difference_le_signed_errors (tripleCopies ρ n)
  simpa only [add_div] using div_le_div_of_nonneg_right h hnR.le

end QuantumProver.DepolarizingSquashedEntanglement.BCYRedistributionCode

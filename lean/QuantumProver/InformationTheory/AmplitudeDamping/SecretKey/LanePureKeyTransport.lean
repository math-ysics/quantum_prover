import QuantumProver.InformationTheory.AmplitudeDamping.SecretKey.SeedKeyReadoutTransport
import QuantumProver.InformationTheory.AmplitudeDamping.SecretKey.LaneFidelity
import QuantumProver.InformationTheory.AmplitudeDamping.SecretKey.LaneMergeHistory
import QuantumProver.InformationTheory.AmplitudeDamping.SecretKey.LaneRetainedOutput

set_option autoImplicit false

noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix Kronecker

namespace QuantumProver.AmplitudeDamping.SecretKey.LanePureKeyTransport

open IndependentLanes PhysicalPurification

def productVector {I : Type*} (ψ : I → ℂ) : (n : ℕ) → Register I n → ℂ
  | 0, _ => 1
  | n + 1, x => ψ x.1 * productVector ψ n x.2

theorem matrix_outer_product {I : Type*} [Fintype I] [DecidableEq I]
    (ψ : I → ℂ) (n : ℕ) :
    matrix (Matrix.vecMulVec ψ (star ψ)) n =
      Matrix.vecMulVec (productVector ψ n) (star (productVector ψ n)) := by
  induction n with
  | zero =>
      ext x y
      cases x
      cases y
      simp [matrix, productVector, Matrix.one_apply, Matrix.vecMulVec_apply, Pi.star_apply]
  | succ n ih =>
      ext x y
      simp only [matrix, Matrix.kroneckerMap_apply, ih, Matrix.vecMulVec_apply,
        productVector, Pi.star_apply, star_mul]
      ring

section PureCoefficient

variable {S E T F : Type*} [Fintype S] [Fintype E] [Fintype T] [Fintype F]
  [DecidableEq S] [DecidableEq E] [DecidableEq T] [DecidableEq F]

def coefficientOnChart (C : Matrix S E ℂ) (N : ℕ)
    (eI : (T × F) ≃ Register (S × E) N) : Matrix T F ℂ :=
  fun t f => star (productVector (vector C) N (eI (t,f)))

theorem coefficientOnChart_pureMatrix (C : Matrix S E ℂ) (N : ℕ)
    (eI : (T × F) ≃ Register (S × E) N) :
    pureMatrix (coefficientOnChart C N eI) =
      (matrix (pureMatrix C) N).submatrix eI eI := by
  simp only [pureMatrix]
  rw [matrix_outer_product]
  ext x y
  simp only [Matrix.vecMulVec_apply, vector, coefficientOnChart, Matrix.submatrix_apply,
    Pi.star_apply, star_star]

theorem coefficientOnChart_normalized (C : Matrix S E ℂ)
    (hC : (Cᴴ * C).trace = 1) (N : ℕ)
    (eI : (T × F) ≃ Register (S × E) N) :
    ((coefficientOnChart C N eI)ᴴ * coefficientOnChart C N eI).trace = 1 := by
  rw [← trace_pureMatrix, coefficientOnChart_pureMatrix]
  have hTrace : ((matrix (pureMatrix C) N).submatrix eI eI).trace =
      (matrix (pureMatrix C) N).trace := by
    change (∑ x, matrix (pureMatrix C) N (eI x) (eI x)) =
      ∑ x, matrix (pureMatrix C) N x x
    exact eI.sum_comp (fun x : Register (S × E) N => matrix (pureMatrix C) N x x)
  rw [hTrace, matrix_trace, trace_pureMatrix, hC, one_pow]

theorem coefficientOnChart_density (C : Matrix S E ℂ)
    (hC : (Cᴴ * C).trace = 1) (N : ℕ)
    (eI : (T × F) ≃ Register (S × E) N) :
    PhysicalPurification.density (coefficientOnChart C N eI)
        (coefficientOnChart_normalized C hC N eI) =
      (IndependentLanes.density (PhysicalPurification.density C hC) N).relabel eI := by
  apply Density.eq_of_mat_eq
  change pureMatrix (coefficientOnChart C N eI) =
    ((IndependentLanes.density (PhysicalPurification.density C hC) N).mat).submatrix eI eI
  rw [coefficientOnChart_pureMatrix, density_mat]
  rfl

end PureCoefficient

def laboratoryInputEquiv (A B E : Type*) (N : ℕ) :
    ((Register A N × Register B N) × Register E N) ≃ Register ((A × B) × E) N :=
  (((pairEquiv A B N).symm).prodCongr (Equiv.refl _)).trans (pairEquiv (A × B) E N).symm

def localInputEquiv {A B A' B' E : Type*} (N : ℕ)
    (eA : A' ≃ Register A N) (eB : B' ≃ Register B N) :
    ((A' × B') × Register E N) ≃ Register ((A × B) × E) N :=
  ((eA.prodCongr eB).prodCongr (Equiv.refl _)).trans (laboratoryInputEquiv A B E N)

def localTensorCoefficient {a b an bn : ℕ} {E : Type*} [Fintype E]
    (C : Matrix (Fin a × Fin b) E ℂ) (N : ℕ)
    (eA : Fin an ≃ Register (Fin a) N) (eB : Fin bn ≃ Register (Fin b) N) :
    Matrix (Fin an × Fin bn) (Register E N) ℂ :=
  coefficientOnChart C N (localInputEquiv (E := E) N eA eB)

theorem localTensorCoefficient_normalized {a b an bn : ℕ} {E : Type*}
    [Fintype E] [DecidableEq E] (C : Matrix (Fin a × Fin b) E ℂ)
    (hC : (Cᴴ * C).trace = 1) (N : ℕ)
    (eA : Fin an ≃ Register (Fin a) N) (eB : Fin bn ≃ Register (Fin b) N) :
    ((localTensorCoefficient C N eA eB)ᴴ * localTensorCoefficient C N eA eB).trace = 1 :=
  coefficientOnChart_normalized C hC N _

open LaneMergeHistory LaneRetainedOutput QuantumProver.AmplitudeDamping.FiniteModel

def schedulerCoefficient {a b : ℕ} {E : Type*} [Fintype E]
    (C : Matrix (Fin a × Fin b) E ℂ) (n : ℕ) :
    Matrix (Fin (lanePowerDimB n a) × Fin (lanePowerDimB n b)) (LaneEveRegister_B E n) ℂ :=
  coefficientOnChart C (n + 1) (laneInputEquiv_B a b E n)

theorem schedulerCoefficient_normalized {a b : ℕ} {E : Type*}
    [Fintype E] [DecidableEq E] (C : Matrix (Fin a × Fin b) E ℂ)
    (hC : (Cᴴ * C).trace = 1) (n : ℕ) :
    ((schedulerCoefficient C n)ᴴ * schedulerCoefficient C n).trace = 1 :=
  coefficientOnChart_normalized C hC (n + 1) _

theorem schedulerCoefficient_density_mat {a b : ℕ} {E : Type*}
    [Fintype E] [DecidableEq E] (C : Matrix (Fin a × Fin b) E ℂ)
    (hC : (Cᴴ * C).trace = 1) (n : ℕ) :
    (PhysicalPurification.density (schedulerCoefficient C n)
      (schedulerCoefficient_normalized C hC n)).mat =
      lanePriorMatrix_B (PhysicalPurification.density C hC).mat n := by
  rw [lanePriorMatrix_eq_tensor_B]
  exact coefficientOnChart_pureMatrix C (n + 1) _

section ReadoutNaturality

variable {I I' K K' E E' : Type*}
  [Fintype I] [Fintype I'] [Fintype K] [Fintype K'] [Fintype E] [Fintype E']
  [DecidableEq I] [DecidableEq I'] [DecidableEq K] [DecidableEq K']
  [DecidableEq E] [DecidableEq E']

theorem basisReadout_reindex (eI : I' ≃ I) (eK : K' ≃ K) (eE : E' ≃ E)
    (label : I → K) (M : Matrix (I × E) (I × E) ℂ) :
    ((basisReadoutChannel (fun i => eK.symm (label (eI i)))).withRightMemory E').eval
      (M.submatrix (eI.prodCongr eE) (eI.prodCongr eE)) =
    (((basisReadoutChannel label).withRightMemory E).eval M).submatrix
      (eK.prodCongr eE) (eK.prodCongr eE) := by
  ext x y
  rw [PublicHistory.reference_basisReadout_apply_B]
  change (∑ i : I', if x.1 = eK.symm (label (eI i)) ∧ y.1 = eK.symm (label (eI i))
    then M (eI i,eE x.2) (eI i,eE y.2) else 0) =
    ((basisReadoutChannel label).withRightMemory E).eval M (eK x.1,eE x.2) (eK y.1,eE y.2)
  rw [PublicHistory.reference_basisReadout_apply_B]
  rw [← eI.symm.sum_comp (fun i => if x.1 = eK.symm (label (eI i)) ∧
      y.1 = eK.symm (label (eI i)) then M (eI i,eE x.2) (eI i,eE y.2) else 0)]
  simp only [Equiv.apply_symm_apply, Equiv.eq_symm_apply]

end ReadoutNaturality

def tupleLabel {I K : Type*} (label : I → K) : (N : ℕ) → Register I N → Register K N
  | 0, _ => PUnit.unit
  | N + 1, x => (label x.1, tupleLabel label N x.2)

section ReadoutTensor

variable {I K E : Type*} [Fintype I] [Fintype K] [Fintype E]
  [DecidableEq I] [DecidableEq K] [DecidableEq E]

theorem basisReadout_tensor_tuple (label : I → K)
    (M : Matrix (I × E) (I × E) ℂ) (N : ℕ) :
    ((basisReadoutChannel (tupleLabel label N)).withRightMemory (Register E N)).eval
      ((matrix M N).submatrix (pairEquiv I E N).symm (pairEquiv I E N).symm) =
    (matrix (((basisReadoutChannel label).withRightMemory E).eval M) N).submatrix
      (pairEquiv K E N).symm (pairEquiv K E N).symm := by
  induction N with
  | zero =>
      ext x y
      rcases x with ⟨x₁,x₂⟩
      rcases y with ⟨y₁,y₂⟩
      cases x₁; cases x₂; cases y₁; cases y₂
      rw [PublicHistory.reference_basisReadout_apply_B]
      simp [tupleLabel, matrix, pairEquiv, Matrix.one_apply]
  | succ N ih =>
      ext x y
      rw [PublicHistory.reference_basisReadout_apply_B, Fintype.sum_prod_type]
      change (∑ i : I, ∑ is : Register I N,
        if x.1 = (label i, tupleLabel label N is) ∧ y.1 = (label i, tupleLabel label N is)
        then M (i,x.2.1) (i,y.2.1) *
          (matrix M N).submatrix (pairEquiv I E N).symm (pairEquiv I E N).symm
            (is,x.2.2) (is,y.2.2) else 0) =
        ((basisReadoutChannel label).withRightMemory E).eval M
          (x.1.1,x.2.1) (y.1.1,y.2.1) *
        (matrix (((basisReadoutChannel label).withRightMemory E).eval M) N).submatrix
          (pairEquiv K E N).symm (pairEquiv K E N).symm (x.1.2,x.2.2) (y.1.2,y.2.2)
      rw [← ih, PublicHistory.reference_basisReadout_apply_B,
        PublicHistory.reference_basisReadout_apply_B]
      simp only [Finset.sum_mul, Finset.mul_sum]
      conv_rhs => rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro is _
      by_cases hx : x.1.1 = label i <;> by_cases hy : y.1.1 = label i <;>
        by_cases hxs : x.1.2 = tupleLabel label N is <;>
        by_cases hys : y.1.2 = tupleLabel label N is <;>
        simp [Prod.ext_iff, hx, hy, hxs, hys]

end ReadoutTensor

def keyAlphabetEquiv (d : ℕ) : (N : ℕ) → Fin (LaneFidelity.laneAlphabet d N) ≃ Register (Fin d) N
  | 0 =>
      { toFun := fun _ => PUnit.unit
        invFun := fun _ => 0
        left_inv := fun _ => Subsingleton.elim _ _
        right_inv := fun _ => Subsingleton.elim _ _ }
  | N + 1 => (splitKeyRegister d (LaneFidelity.laneAlphabet d N)).trans
      ((Equiv.refl (Fin d)).prodCongr (keyAlphabetEquiv d N))

def keyPairEquiv (d N : ℕ) :
    (Fin (LaneFidelity.laneAlphabet d N) × Fin (LaneFidelity.laneAlphabet d N)) ≃
      Register (Fin d × Fin d) N :=
  ((keyAlphabetEquiv d N).prodCongr (keyAlphabetEquiv d N)).trans (pairEquiv (Fin d) (Fin d) N).symm

theorem keyLaneTensorEquiv_eq (d : ℕ) (E : Type*) (N : ℕ) :
    LaneFidelity.keyLaneTensorEquiv d E N =
      ((keyPairEquiv d N).prodCongr (Equiv.refl (Register E N))).trans
        (pairEquiv (Fin d × Fin d) E N).symm := by
  induction N with
  | zero =>
      apply Equiv.ext
      intro x
      rfl
  | succ N ih =>
      apply Equiv.ext
      intro x
      let ka := splitKeyRegister d (LaneFidelity.laneAlphabet d N) x.1.1
      let kb := splitKeyRegister d (LaneFidelity.laneAlphabet d N) x.1.2
      change (((ka.1,kb.1),x.2.1),
        LaneFidelity.keyLaneTensorEquiv d E N ((ka.2,kb.2),x.2.2)) = _
      rw [ih]
      rfl

theorem tupleLabel_pair {A B K L : Type*} (f : A → K) (g : B → L)
    (N : ℕ) (x : Register (A × B) N) :
    pairEquiv K L N (tupleLabel (fun ab : A × B => (f ab.1,g ab.2)) N x) =
      (tupleLabel f N (pairEquiv A B N x).1, tupleLabel g N (pairEquiv A B N x).2) := by
  induction N with
  | zero => cases x; rfl
  | succ N ih =>
      change ((f x.1.1,(pairEquiv K L N (tupleLabel (fun ab : A × B =>
        (f ab.1,g ab.2)) N x.2)).1),
        (g x.1.2,(pairEquiv K L N (tupleLabel (fun ab : A × B =>
        (f ab.1,g ab.2)) N x.2)).2)) = _
      rw [ih]
      rfl

def packedPrivateLabel {A A' : Type*} {d : ℕ} (label : A → Fin d)
    (N : ℕ) (eA : A' ≃ Register A N) : A' → Fin (LaneFidelity.laneAlphabet d N) :=
  fun a => (keyAlphabetEquiv d N).symm (tupleLabel label N (eA a))

theorem packedPrivateLabel_pair {A B A' B' : Type*} {d : ℕ}
    (labelA : A → Fin d) (labelB : B → Fin d) (N : ℕ)
    (eA : A' ≃ Register A N) (eB : B' ≃ Register B N) (x : A' × B') :
    (packedPrivateLabel labelA N eA x.1,packedPrivateLabel labelB N eB x.2) =
      (keyPairEquiv d N).symm
        (tupleLabel (fun ab : A × B => (labelA ab.1,labelB ab.2)) N
          ((pairEquiv A B N).symm (eA x.1,eB x.2))) := by
  apply (keyPairEquiv d N).injective
  apply (pairEquiv (Fin d) (Fin d) N).injective
  rw [Equiv.apply_symm_apply, tupleLabel_pair]
  simp only [keyPairEquiv, packedPrivateLabel, Equiv.trans_apply,
    Equiv.prodCongr_apply, Prod.map_apply, Equiv.apply_symm_apply]

section PackedReadout

variable {A B A' B' E F : Type*} [Fintype A] [Fintype B] [Fintype A'] [Fintype B']
  [Fintype E] [Fintype F] [DecidableEq A] [DecidableEq B] [DecidableEq A']
  [DecidableEq B'] [DecidableEq E] [DecidableEq F] {d : ℕ}

def packedWholeEquiv (N : ℕ) (eA : A' ≃ Register A N) (eB : B' ≃ Register B N)
    (eE : F ≃ Register E N) : ((A' × B') × F) ≃ Register ((A × B) × E) N :=
  ((eA.prodCongr eB).prodCongr eE).trans (laboratoryInputEquiv A B E N)

theorem packedReadout_tensor_matrix (labelA : A → Fin d) (labelB : B → Fin d)
    (M : Matrix ((A × B) × E) ((A × B) × E) ℂ) (N : ℕ)
    (eA : A' ≃ Register A N) (eB : B' ≃ Register B N) (eE : F ≃ Register E N) :
    ((basisReadoutChannel (fun x : A' × B' =>
        (packedPrivateLabel labelA N eA x.1, packedPrivateLabel labelB N eB x.2))).withRightMemory F).eval
      ((matrix M N).submatrix (packedWholeEquiv N eA eB eE) (packedWholeEquiv N eA eB eE)) =
    (matrix (((basisReadoutChannel (fun x : A × B => (labelA x.1,labelB x.2))).withRightMemory E).eval M) N).submatrix
      (((Equiv.refl _).prodCongr eE).trans (LaneFidelity.keyLaneTensorEquiv d E N))
      (((Equiv.refl _).prodCongr eE).trans (LaneFidelity.keyLaneTensorEquiv d E N)) := by
  let eI := (eA.prodCongr eB).trans (pairEquiv A B N).symm
  let eK := keyPairEquiv d N
  let label := tupleLabel (fun x : A × B => (labelA x.1,labelB x.2)) N
  let Z := (matrix M N).submatrix (pairEquiv (A × B) E N).symm (pairEquiv (A × B) E N).symm
  have h := basisReadout_reindex eI eK eE label Z
  have hlabel : (fun x : A' × B' =>
      (packedPrivateLabel labelA N eA x.1, packedPrivateLabel labelB N eB x.2)) =
      (fun x => eK.symm (label (eI x))) := by
    funext x
    exact packedPrivateLabel_pair labelA labelB N eA eB x
  rw [hlabel]
  change ((basisReadoutChannel (fun i => eK.symm (label (eI i)))).withRightMemory F).eval
    (Z.submatrix (eI.prodCongr eE) (eI.prodCongr eE)) = _
  rw [h]
  dsimp only [Z, label]
  rw [basisReadout_tensor_tuple, keyLaneTensorEquiv_eq]
  rfl

theorem packedReadout_tensor_density (labelA : A → Fin d) (labelB : B → Fin d)
    (ρ : Density ((A × B) × E)) (N : ℕ)
    (eA : A' ≃ Register A N) (eB : B' ≃ Register B N) (eE : F ≃ Register E N) :
    ((basisReadoutChannel (fun x : A' × B' =>
      (packedPrivateLabel labelA N eA x.1,packedPrivateLabel labelB N eB x.2))).withRightMemory F).onDensity
        ((IndependentLanes.density ρ N).relabel (packedWholeEquiv N eA eB eE)) =
      (LaneFidelity.keyLaneDensity
        (((basisReadoutChannel (fun x : A × B => (labelA x.1,labelB x.2))).withRightMemory E).onDensity ρ) N).relabel
          ((Equiv.refl _).prodCongr eE) := by
  apply Density.eq_of_mat_eq
  change ((basisReadoutChannel _).withRightMemory F).eval
    ((IndependentLanes.density ρ N).mat.submatrix _ _) = _
  rw [density_mat, packedReadout_tensor_matrix]
  dsimp only [Density.relabel]
  rw [LaneFidelity.keyLaneDensity_mat]
  rfl

end PackedReadout

section MatrixScheduler

open PhysicalProtocol PhysicalProtocol.FiniteKeyProtocol

theorem laneInputEquiv_local (a b : ℕ) (E : Type*) (n : ℕ) :
    laneInputEquiv_B a b E n =
      packedWholeEquiv (n + 1) (laneLocalEquiv_B a n) (laneLocalEquiv_B b n)
        (laneEveTupleEquiv_B E n) := by
  induction n with
  | zero => apply Equiv.ext; intro x; rfl
  | succ n ih =>
      apply Equiv.ext
      intro x
      let y := pairLabEquivB (lanePowerDimB n a) (lanePowerDimB n b) a b x.1
      change ((y.2,x.2.2),laneInputEquiv_B a b E n (y.1,x.2.1)) = _
      rw [ih]
      rfl

variable {p : ℝ} {a b af bf d n : ℕ} {E : Type*} [Fintype E] [DecidableEq E]
  {P : FiniteProtocol p a b af bf}
  {R : FiniteBlockProtocolB p (n + 1) (lanePowerDimB n a) (lanePowerDimB n b)
    (lanePowerDimB n af) (lanePowerDimB n bf)}

theorem laneOutputEveEquiv_local
    (eH : (blockExpansion_B R).Environment ≃ Register (fromQuantum_B P).Environment (n + 1)) :
    laneOutputEveEquiv_B E eH =
      packedWholeEquiv (n + 1) (laneLocalEquiv_B af n) (laneLocalEquiv_B bf n)
        (retainedEveOutputEquiv_B (E := E) n eH) := by
  rw [laneOutputEveEquiv_B, laneInputEquiv_local]
  rfl

def schedulerLabelA (label : Fin af → Fin d) :
    Fin (lanePowerDimB n af) → Fin (LaneFidelity.laneAlphabet d (n + 1)) :=
  packedPrivateLabel label (n + 1) (laneLocalEquiv_B af n)

def schedulerLabelB (label : Fin bf → Fin d) :
    Fin (lanePowerDimB n bf) → Fin (LaneFidelity.laneAlphabet d (n + 1)) :=
  packedPrivateLabel label (n + 1) (laneLocalEquiv_B bf n)

theorem independentLanes_pure_finalKeyState (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hR : IndependentLanesDerivationB p P n R)
    (labelA : Fin af → Fin d) (labelB : Fin bf → Fin d) :
    ∃ eH : (blockExpansion_B R).Environment ≃ Register (fromQuantum_B P).Environment (n + 1),
    ∃ eT : (blockExpansion_B R).comparisonPublicHistory_B ≃
        Register (fromQuantum_B P).comparisonPublicHistory_B (n + 1),
      (∀ t, (blockExpansion_B R).historyKraus_B t = laneHistoryKraus_B P n (eH t)) ∧
      (∀ t, eT ((blockExpansion_B R).publicTranscript_B t) = lanePublicTranscript_B P n (eH t)) ∧
    ∀ (C : Matrix (Fin a × Fin b) E ℂ) (hC : (Cᴴ * C).trace = 1),
      (blockExpansion_B R).finalKeyStateWithPriorEveLabels hp0 hp1
        (schedulerLabelA (n := n) labelA) (schedulerLabelB (n := n) labelB)
        (LaneEveRegister_B E n)
        (PhysicalPurification.density (schedulerCoefficient C n)
          (schedulerCoefficient_normalized C hC n)) =
      (LaneFidelity.keyLaneDensity
        ((fromQuantum_B P).finalKeyStateWithPriorEveLabels hp0 hp1 labelA labelB E
          (PhysicalPurification.density C hC)) (n + 1)).relabel
        ((Equiv.refl _).prodCongr (retainedEveOutputEquiv_B (E := E) n eH)) := by
  rcases independentLanes_priorEve_tensor_B (E := E) hR with ⟨eH,eT,hK,hT,hO⟩
  refine ⟨eH,eT,hK,hT,?_⟩
  intro C hC
  apply Density.eq_of_mat_eq
  change ((basisReadoutChannel (fun x : Fin (lanePowerDimB n af) × Fin (lanePowerDimB n bf) =>
      (schedulerLabelA (n := n) labelA x.1,schedulerLabelB (n := n) labelB x.2))).withRightMemory
        ((blockExpansion_B R).Environment × LaneEveRegister_B E n)).eval
      (PublicHistory.localPriorEveMatrix_B (blockExpansion_B R)
        (PhysicalPurification.density (schedulerCoefficient C n)
          (schedulerCoefficient_normalized C hC n)).mat) = _
  rw [schedulerCoefficient_density_mat C hC n, hO, laneOutputEveEquiv_local]
  dsimp only [schedulerLabelA, schedulerLabelB]
  rw [packedReadout_tensor_matrix]
  dsimp only [Density.relabel]
  rw [LaneFidelity.keyLaneDensity_mat]
  rfl

end MatrixScheduler

end QuantumProver.AmplitudeDamping.SecretKey.LanePureKeyTransport

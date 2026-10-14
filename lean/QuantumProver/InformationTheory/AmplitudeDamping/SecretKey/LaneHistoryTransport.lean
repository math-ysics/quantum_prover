import QuantumProver.InformationTheory.AmplitudeDamping.SecretKey.ParallelLanes

set_option autoImplicit false

noncomputable section

open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix Kronecker

namespace QuantumProver.AmplitudeDamping.SecretKey.LaneHistoryTransport

open PhysicalProtocol PhysicalProtocol.FiniteKeyProtocol PublicHistory

variable {I O S : Type*} [Fintype I] [Fintype O] [Fintype S] [DecidableEq S]

theorem privateMemoryCross_apply_B (K L : Matrix O I ℂ)
    (ρ : Matrix (S × I) (S × I) ℂ) (s s' : S) (x y : O) :
    (((1 : Matrix S S ℂ) ⊗ₖ K) * ρ * ((1 : Matrix S S ℂ) ⊗ₖ L)ᴴ)
      (s,x) (s',y) =
        (K * Matrix.of (fun i j => ρ (s,i) (s',j)) * Lᴴ) x y := by
  classical
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.kroneckerMap_apply, Matrix.one_apply, Fintype.sum_prod_type,
    Finset.sum_mul, Finset.mul_sum, Matrix.of_apply,
    apply_ite, ite_mul, mul_ite, mul_assoc]

variable {p : ℝ} {a b af bf c d cf df : ℕ}

def fullOutputWithPrivateMemory_B (P : FiniteKeyProtocol p a b af bf)
    (ρ : Matrix (S × (Fin a × Fin b)) (S × (Fin a × Fin b)) ℂ) :
    Matrix ((S × (Fin af × Fin bf)) × P.Environment)
      ((S × (Fin af × Fin bf)) × P.Environment) ℂ :=
  fun x y => P.fullOutput
    (Matrix.of (fun i j => ρ (x.1.1,i) (y.1.1,j)))
      (x.1.2,x.2) (y.1.2,y.2)

theorem fullOutput_privateMemory_transport_B
    (P : FiniteKeyProtocol p a b af bf) (Q : FiniteKeyProtocol p c d cf df)
    (eI : (Fin c × Fin d) ≃ (S × (Fin a × Fin b)))
    (eO : (Fin cf × Fin df) ≃ (S × (Fin af × Fin bf)))
    (eE : Q.Environment ≃ P.Environment)
    (hK : ∀ h, Q.historyKraus_B h =
      ((1 : Matrix S S ℂ) ⊗ₖ P.historyKraus_B (eE h)).submatrix eO eI)
    (hpublic : ∀ h h', Q.publicTranscript_B h = Q.publicTranscript_B h' ↔
      P.publicTranscript_B (eE h) = P.publicTranscript_B (eE h'))
    (ρ : Matrix (S × (Fin a × Fin b)) (S × (Fin a × Fin b)) ℂ) :
    Q.fullOutput (ρ.submatrix eI eI) =
      (fullOutputWithPrivateMemory_B P ρ).submatrix
        (eO.prodCongr eE) (eO.prodCongr eE) := by
  ext x y
  rcases x with ⟨x,h⟩
  rcases y with ⟨y,h'⟩
  simp only [fullOutputWithPrivateMemory_B, Matrix.submatrix_apply,
    Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd]
  rw [Q.fullOutput_historyKraus_apply_B, P.fullOutput_historyKraus_apply_B]
  by_cases hh : Q.publicTranscript_B h = Q.publicTranscript_B h'
  · have hp := (hpublic h h').mp hh
    simp only [if_pos hh, if_pos hp]
    rw [hK h, hK h', Matrix.conjTranspose_submatrix,
      Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]
    exact privateMemoryCross_apply_B _ _ ρ (eO x).1 (eO y).1 (eO x).2 (eO y).2
  · have hp : P.publicTranscript_B (eE h) ≠ P.publicTranscript_B (eE h') :=
      fun hp => hh ((hpublic h h').mpr hp)
    simp only [if_neg hh, if_neg hp]

variable {E : Type*} [Fintype E] [DecidableEq E]

def fullOutputWithPrivateMemoryAndEve_B (P : FiniteKeyProtocol p a b af bf)
    (ρ : Matrix ((S × (Fin a × Fin b)) × E) ((S × (Fin a × Fin b)) × E) ℂ) :
    Matrix ((S × (Fin af × Fin bf)) × (P.Environment × E))
      ((S × (Fin af × Fin bf)) × (P.Environment × E)) ℂ :=
  fun x y => P.fullOutput
    (Matrix.of (fun i j => ρ ((x.1.1,i),x.2.2) ((y.1.1,j),y.2.2)))
      (x.1.2,x.2.1) (y.1.2,y.2.1)

theorem priorEve_privateMemory_transport_B
    (P : FiniteKeyProtocol p a b af bf) (Q : FiniteKeyProtocol p c d cf df)
    (eI : (Fin c × Fin d) ≃ (S × (Fin a × Fin b)))
    (eO : (Fin cf × Fin df) ≃ (S × (Fin af × Fin bf)))
    (eE : Q.Environment ≃ P.Environment)
    (hK : ∀ h, Q.historyKraus_B h =
      ((1 : Matrix S S ℂ) ⊗ₖ P.historyKraus_B (eE h)).submatrix eO eI)
    (hpublic : ∀ h h', Q.publicTranscript_B h = Q.publicTranscript_B h' ↔
      P.publicTranscript_B (eE h) = P.publicTranscript_B (eE h'))
    (ρ : Matrix ((S × (Fin a × Fin b)) × E) ((S × (Fin a × Fin b)) × E) ℂ) :
    localPriorEveMatrix_B Q
      (ρ.submatrix (eI.prodCongr (Equiv.refl E)) (eI.prodCongr (Equiv.refl E))) =
      (fullOutputWithPrivateMemoryAndEve_B P ρ).submatrix
        (eO.prodCongr (eE.prodCongr (Equiv.refl E)))
        (eO.prodCongr (eE.prodCongr (Equiv.refl E))) := by
  ext x y
  rcases x with ⟨x,h,e⟩
  rcases y with ⟨y,h',e'⟩
  have ht := congrArg (fun M => M (x,h) (y,h'))
    (fullOutput_privateMemory_transport_B P Q eI eO eE hK hpublic
      (Matrix.of (fun i j => ρ (i,e) (j,e'))))
  exact ht

end QuantumProver.AmplitudeDamping.SecretKey.LaneHistoryTransport

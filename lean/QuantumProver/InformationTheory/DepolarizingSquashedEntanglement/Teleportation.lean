import QuantumProver.InformationTheory.DepolarizingSquashedEntanglement.SquashingBounds

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix Kronecker
  Matrix.Norms.L2Operator ContinuousFunctionalCalculus

namespace QuantumProver.DepolarizingSquashedEntanglement.Teleportation

def aliceBellKet (k : CanonicalEnvironment) : (Qubit×Qubit) → ℂ :=
  fun ia => (splitterScale : ℂ)*pauli k ia.1 ia.2

def aliceBellBra (k : CanonicalEnvironment) : Matrix (Fin 1) (Qubit×Qubit) ℂ :=
  fun _ ia => star (aliceBellKet k ia)

theorem aliceBellBra_effect (k : CanonicalEnvironment) :
    (aliceBellBra k).conjTranspose*aliceBellBra k=pureDensity (aliceBellKet k) := by
  ext ia jc
  simp [aliceBellBra,Matrix.mul_apply,Matrix.conjTranspose_apply,
    pureDensity,QuantumProver.WernerEndpoint.pureDensity,QuantumProver.WernerEndpoint.crossDensity]

theorem aliceBellBra_complete :
    ∑ k : CanonicalEnvironment,(aliceBellBra k).conjTranspose*aliceBellBra k=
      (1 : QMatrix (Qubit×Qubit)) := by
  calc
    _ = (canonicalBellBasis*canonicalBellBasis.conjTranspose).submatrix
        Prod.swap Prod.swap := by
      ext ⟨i,a⟩ ⟨j,c⟩
      simp only [Matrix.sum_apply,aliceBellBra_effect,pureDensity,
        QuantumProver.WernerEndpoint.pureDensity,QuantumProver.WernerEndpoint.crossDensity,
        Matrix.submatrix_apply,Matrix.mul_apply,Matrix.conjTranspose_apply,
        aliceBellKet,canonicalBellBasis,Prod.swap_prod_mk]
    _ = _ := by
      rw [canonicalBellBasis_right_gram]
      ext ⟨i,a⟩ ⟨j,c⟩
      simp [Matrix.submatrix_apply,Matrix.one_apply,and_comm]

def bobCorrection (k : CanonicalEnvironment) : QMatrix Qubit := pauli k

theorem bobCorrection_isometry (k : CanonicalEnvironment) : IsIsometry (bobCorrection k) :=
  pauli_unitary k

def teleportationKraus (k : CanonicalEnvironment) :
    Matrix Qubit ((Qubit×Qubit)×Qubit) ℂ :=
  fun b x => aliceBellBra k 0 x.1*bobCorrection k b x.2

theorem teleportationKraus_gram (k : CanonicalEnvironment) :
    (teleportationKraus k).conjTranspose*teleportationKraus k=
      ((aliceBellBra k).conjTranspose*aliceBellBra k) ⊗ₖ (1 : QMatrix Qubit) := by
  ext ⟨ia,b⟩ ⟨jc,d⟩
  simp only [teleportationKraus,bobCorrection,Matrix.mul_apply,
    Matrix.conjTranspose_apply,Matrix.kronecker_apply,Fin.sum_univ_one,star_mul]
  calc
    _ = (star (aliceBellBra k 0 ia)*aliceBellBra k 0 jc)*
        (∑ q : Qubit,star (pauli k q b)*pauli k q d) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q hq
      ring
    _ = _ := by
      have h := congrArg (fun M : QMatrix Qubit => M b d) (pauli_unitary k)
      change (∑ q : Qubit,star (pauli k q b)*pauli k q d)=(1 : QMatrix Qubit) b d at h
      rw [h]

theorem teleportationKraus_complete :
    ∑ k : CanonicalEnvironment,(teleportationKraus k).conjTranspose*teleportationKraus k=
      (1 : QMatrix ((Qubit×Qubit)×Qubit)) := by
  simp_rw [teleportationKraus_gram]
  calc
    _ = (∑ k : CanonicalEnvironment,(aliceBellBra k).conjTranspose*aliceBellBra k) ⊗ₖ
        (1 : QMatrix Qubit) := by
      ext x y
      simp [Matrix.sum_apply,Matrix.kronecker_apply,Finset.sum_mul]
    _ = _ := by rw [aliceBellBra_complete,Matrix.one_kronecker_one]

def teleportationChannel : CPTP ((Qubit×Qubit)×Qubit) Qubit :=
  CPTP.ofCompleteKraus teleportationKraus teleportationKraus_complete

def physicalChoiBranch {R : Type*} (p : ℝ) (k : CanonicalEnvironment)
    (ψ : (R×Qubit) → ℂ) : ((R×Qubit)×CanonicalEnvironment) → ℂ :=
  fun x => ∑ i : Qubit,∑ a : Qubit,∑ b : Qubit,
    star (aliceBellKet k (i,a))*pauli k x.1.2 b*ψ (x.1.1,i)*
      extendedInputKet p bellKet ((a,b),x.2)

theorem physicalChoiBranch_eq {R : Type*} (p : ℝ) (k : CanonicalEnvironment)
    (ψ : (R×Qubit) → ℂ) :
    physicalChoiBranch p k ψ = fun x =>
      (1/2 : ℂ)*(pauliSign k x.2 : ℂ)*extendedInputKet p ψ x := by
  funext x
  rcases x with ⟨⟨r,b⟩,j⟩
  fin_cases k <;> fin_cases j <;> fin_cases b <;>
    apply Complex.ext <;>
    norm_num [physicalChoiBranch,aliceBellKet,extendedInputKet,canonicalIsometry,
      bellKet,pauli,pauliSign,pauliWeight,Fin.sum_univ_two,
      Matrix.one_apply,Complex.star_def,Complex.mul_re,Complex.mul_im] <;>
    ring_nf <;> simp [splitterScale_sq] <;> ring

theorem flagEmbedding_sandwich {E : Type*} [Fintype E] [DecidableEq E]
    (k j l : CanonicalEnvironment) (A : QMatrix E) (e f : E) :
    (pauliFlagEmbedding (E:=E) k*A*(pauliFlagEmbedding (E:=E) k).conjTranspose)
      (j,e) (l,f)=if j=k ∧ l=k then A e f else 0 := by
  by_cases hj : j=k <;> by_cases hl : l=k <;>
    simp_all [pauliFlagEmbedding,Matrix.mul_apply,Matrix.conjTranspose_apply,
      Prod.mk.injEq,ite_mul,mul_ite,apply_ite]

theorem pauliFlagKraus_sandwich {E : Type*} [Fintype E] [DecidableEq E]
    (S : CPTP CanonicalEnvironment E) (k : CanonicalEnvironment)
    (g : CanonicalEnvironment×E) (ρ : QMatrix CanonicalEnvironment) :
    pauliFlagKraus S (k,g)*ρ*(pauliFlagKraus S (k,g)).conjTranspose=
      (1/4 : ℂ) •
        (pauliFlagEmbedding (E:=E) k*
          (S.canonicalKraus g*(pauliEnvironmentUnitary k*ρ*(pauliEnvironmentUnitary k).conjTranspose)*
            (S.canonicalKraus g).conjTranspose)*
          (pauliFlagEmbedding (E:=E) k).conjTranspose) := by
  simp only [pauliFlagKraus,Matrix.conjTranspose_smul,Matrix.smul_mul,
    Matrix.mul_smul,smul_smul,Matrix.conjTranspose_mul]
  norm_num
  simp only [Matrix.mul_assoc]

theorem pauliFlagSquashing_apply_block {E : Type*} [Fintype E] [DecidableEq E]
    (S : CPTP CanonicalEnvironment E) (ρ : QMatrix CanonicalEnvironment)
    (j l : CanonicalEnvironment) (e f : E) :
    (pauliFlagSquashing S).map ρ (j,e) (l,f)=
      if j=l then (1/4 : ℂ)*
        S.map (pauliEnvironmentUnitary j*ρ*(pauliEnvironmentUnitary j).conjTranspose) e f else 0 := by
  have hentry (k : CanonicalEnvironment) (g : CanonicalEnvironment×E) :
      (pauliFlagKraus S (k,g)*ρ*(pauliFlagKraus S (k,g)).conjTranspose)
        (j,e) (l,f)=if j=k ∧ l=k then (1/4 : ℂ)*
          (S.canonicalKraus g*
            (pauliEnvironmentUnitary k*ρ*(pauliEnvironmentUnitary k).conjTranspose)*
            (S.canonicalKraus g).conjTranspose) e f else 0 := by
    rw [pauliFlagKraus_sandwich]
    change (1/4 : ℂ)*
      (pauliFlagEmbedding (E:=E) k*
        (S.canonicalKraus g*
          (pauliEnvironmentUnitary k*ρ*(pauliEnvironmentUnitary k).conjTranspose)*
          (S.canonicalKraus g).conjTranspose)*
        (pauliFlagEmbedding (E:=E) k).conjTranspose) (j,e) (l,f)=_
    rw [flagEmbedding_sandwich]
    split_ifs <;> simp
  rw [pauliFlagSquashing,CPTP.ofCompleteKraus_apply]
  simp only [Matrix.sum_apply,Fintype.sum_prod_type]
  simp_rw [hentry]
  by_cases h : j=l
  · subst l
    simp only [and_self,ite_mul,mul_ite,mul_zero]
    simp only [Finset.sum_ite_irrel,Finset.sum_const_zero]
    simp only [Finset.sum_ite_eq',Finset.sum_ite_eq,Finset.mem_univ,ite_true]
    simp only [Finset.mem_univ,ite_true,← Finset.mul_sum]
    have hr := congrArg (fun M : QMatrix E => M e f)
      (S.canonicalKraus_reconstruct
        (pauliEnvironmentUnitary j*ρ*(pauliEnvironmentUnitary j).conjTranspose))
    simpa only [Matrix.sum_apply,Fintype.sum_prod_type] using
      congrArg (fun z : ℂ => (1/4 : ℂ)*z) hr.symm
  · have hz (k : CanonicalEnvironment) : ¬ (j=k ∧ l=k) := by
      rintro ⟨hj,hl⟩
      exact h (hj.trans hl.symm)
    simp [hz,h]

theorem pauliEnvironmentUnitary_selfAdjoint (k : CanonicalEnvironment) :
    (pauliEnvironmentUnitary k).conjTranspose=pauliEnvironmentUnitary k := by
  simp [pauliEnvironmentUnitary,Matrix.diagonal_conjTranspose,Complex.star_def]

theorem physicalChoiBranch_density_block {R : Type*} (p : ℝ) (k : CanonicalEnvironment)
    (ψ : (R×Qubit) → ℂ) (rb sc : R×Qubit) :
    (fun i j : CanonicalEnvironment => pureDensity (physicalChoiBranch p k ψ)
      (rb,i) (sc,j))=
      (1/4 : ℂ) •
        (pauliEnvironmentUnitary k*
          (show QMatrix CanonicalEnvironment from
            fun i j => pureDensity (extendedInputKet p ψ) (rb,i) (sc,j))*
          (pauliEnvironmentUnitary k).conjTranspose) := by
  ext i j
  rw [pauliEnvironmentUnitary_selfAdjoint]
  simp only [pauliEnvironmentUnitary,Matrix.diagonal_mul,Matrix.mul_diagonal,
    Matrix.smul_apply,pureDensity,QuantumProver.WernerEndpoint.pureDensity,QuantumProver.WernerEndpoint.crossDensity,
    physicalChoiBranch_eq,star_mul,Complex.star_def,map_div₀,map_ofNat,
    Complex.conj_ofReal]
  norm_num
  ring

def flaggedTeleportationOutput {R E : Type*} [Fintype R] [Fintype E]
    (p : ℝ) (S : CPTP CanonicalEnvironment E) (ψ : (R×Qubit) → ℂ) :
    QMatrix ((R×Qubit)×(CanonicalEnvironment×E)) :=
  fun x y => if x.2.1=y.2.1 then
    amplify S.map (pureDensity (physicalChoiBranch p x.2.1 ψ))
      (x.1,x.2.2) (y.1,y.2.2) else 0

theorem flaggedTeleportationOutput_eq_postSquashing {R E : Type*}
    [Fintype R] [Fintype E] [DecidableEq E]
    (p : ℝ) (S : CPTP CanonicalEnvironment E) (ψ : (R×Qubit) → ℂ) :
    flaggedTeleportationOutput p S ψ=postSquashing p ψ (pauliFlagSquashing S) := by
  ext ⟨rb,⟨j,e⟩⟩ ⟨sc,⟨l,f⟩⟩
  change (if j=l then S.map (fun i k => pureDensity (physicalChoiBranch p j ψ)
      (rb,i) (sc,k)) e f else 0)=
    (pauliFlagSquashing S).map (fun i k => pureDensity (extendedInputKet p ψ)
      (rb,i) (sc,k)) (j,e) (l,f)
  rw [pauliFlagSquashing_apply_block]
  split_ifs with h
  · rw [physicalChoiBranch_density_block,map_smul]
    rfl
  · rfl

def flagShift (k j : CanonicalEnvironment) : CanonicalEnvironment :=
  if k=0 then j else if k=1 then ![1,0,3,2] j else
    if k=2 then ![2,3,0,1] j else ![3,2,1,0] j

theorem flagShift_involutive (k : CanonicalEnvironment) :
    Function.Involutive (flagShift k) := by
  intro j
  fin_cases k <;> fin_cases j <;> norm_num [flagShift]

theorem pauliSign_flagShift (k j i : CanonicalEnvironment) :
    pauliSign (flagShift k j) i=pauliSign j i*pauliSign k i := by
  fin_cases k <;> fin_cases j <;> fin_cases i <;> norm_num [flagShift,pauliSign]

def flagPermutation (k : CanonicalEnvironment) : QMatrix CanonicalEnvironment :=
  fun j l => if j=flagShift k l then 1 else 0

theorem flagPermutation_isometry (k : CanonicalEnvironment) :
    IsIsometry (flagPermutation k) := by
  ext i j
  fin_cases k <;> fin_cases i <;> fin_cases j <;>
    norm_num [flagPermutation,flagShift,Matrix.mul_apply,
      Matrix.conjTranspose_apply,Matrix.one_apply,Fin.sum_univ_succ]

def flagStinespringCoefficients {E : Type*} [Fintype E] [DecidableEq E]
    (S : CPTP CanonicalEnvironment E) :
    Matrix ((CanonicalEnvironment×E)×(CanonicalEnvironment×(CanonicalEnvironment×E)))
      CanonicalEnvironment ℂ :=
  fun x i => pauliFlagKraus S x.2 x.1 i

theorem flagStinespringCoefficients_isometry {E : Type*}
    [Fintype E] [DecidableEq E] (S : CPTP CanonicalEnvironment E) :
    IsIsometry (flagStinespringCoefficients S) := by
  ext i j
  have h := congrArg (fun M : QMatrix CanonicalEnvironment => M i j)
    (pauliFlagKraus_complete S)
  simp only [Matrix.sum_apply,Matrix.mul_apply,Matrix.conjTranspose_apply] at h
  change (∑ x : (CanonicalEnvironment×E)×(CanonicalEnvironment×(CanonicalEnvironment×E)),
    star (pauliFlagKraus S x.2 x.1 i)*pauliFlagKraus S x.2 x.1 j)=_
  rw [Fintype.sum_prod_type,Finset.sum_comm]
  exact h

def flagStinespring {E : Type*} [Fintype E] [DecidableEq E]
    (S : CPTP CanonicalEnvironment E) :
    QuantumProver.WernerEndpoint.Stinespring CanonicalEnvironment (CanonicalEnvironment×E)
      (CanonicalEnvironment×(CanonicalEnvironment×E)) where
  coeff := flagStinespringCoefficients S
  gram_eq_one := flagStinespringCoefficients_isometry S

theorem flagStinespring_apply {E : Type*} [Fintype E] [DecidableEq E]
    (S : CPTP CanonicalEnvironment E) (ρ : QMatrix CanonicalEnvironment) :
    (flagStinespring S).apply ρ=(pauliFlagSquashing S).map ρ := by
  rw [pauliFlagSquashing,CPTP.ofCompleteKraus_apply]
  ext o p
  simp [flagStinespring,flagStinespringCoefficients,QuantumProver.WernerEndpoint.Stinespring.apply,
    QuantumProver.WernerEndpoint.partialTraceLeft,Matrix.mul_apply,Matrix.conjTranspose_apply,
    Fintype.sum_prod_type,Matrix.sum_apply,Finset.sum_mul]

theorem flagStinespring_coeff_apply {E : Type*} [Fintype E] [DecidableEq E]
    (S : CPTP CanonicalEnvironment E) (j l i : CanonicalEnvironment)
    (e : E) (g : CanonicalEnvironment×E) :
    (flagStinespring S).coeff ((j,e),(l,g)) i=
      if j=l then (1/2 : ℂ)*S.canonicalKraus g e i*(pauliSign j i : ℂ) else 0 := by
  by_cases h : j=l
  · subst l
    simp [flagStinespring,flagStinespringCoefficients,pauliFlagKraus,
      pauliFlagEmbedding,pauliEnvironmentUnitary,Matrix.diagonal_apply,
      Matrix.smul_apply,Matrix.mul_apply,Prod.mk.injEq,ite_mul,mul_ite,mul_assoc]
  · simp [flagStinespring,flagStinespringCoefficients,pauliFlagKraus,
      pauliFlagEmbedding,pauliEnvironmentUnitary,Matrix.diagonal_apply,
      Matrix.smul_apply,Matrix.mul_apply,Prod.mk.injEq,ite_mul,mul_ite,h]

theorem flagPermutation_pair_mul {E : Type*} [Fintype E] [DecidableEq E]
    (S : CPTP CanonicalEnvironment E) (k j l i : CanonicalEnvironment)
    (e : E) (g : CanonicalEnvironment×E) :
    (((flagPermutation k ⊗ₖ (1 : QMatrix E)) ⊗ₖ
      (flagPermutation k ⊗ₖ (1 : QMatrix (CanonicalEnvironment×E))))*
        (flagStinespring S).coeff) ((j,e),(l,g)) i=
      (flagStinespring S).coeff ((flagShift k j,e),(flagShift k l,g)) i := by
  fin_cases k <;> fin_cases j <;> fin_cases l <;>
    simp [flagPermutation,flagShift,Matrix.mul_apply,Matrix.kronecker_apply,
      Matrix.one_apply,Fintype.sum_prod_type,Fin.sum_univ_succ,ite_mul,mul_ite]

theorem flagStinespring_covariance {E : Type*} [Fintype E] [DecidableEq E]
    (S : CPTP CanonicalEnvironment E) (k : CanonicalEnvironment) :
    (flagStinespring S).coeff*pauliEnvironmentUnitary k=
      ((flagPermutation k ⊗ₖ (1 : QMatrix E)) ⊗ₖ
        (flagPermutation k ⊗ₖ (1 : QMatrix (CanonicalEnvironment×E))))*
          (flagStinespring S).coeff := by
  ext ⟨⟨j,e⟩,⟨l,g⟩⟩ i
  rw [flagPermutation_pair_mul]
  simp only [pauliEnvironmentUnitary,Matrix.mul_diagonal,flagStinespring_coeff_apply]
  by_cases h : j=l
  · subst l
    simp only [ite_true,pauliSign_flagShift,Complex.ofReal_mul]
    ring
  · have hs : flagShift k j≠flagShift k l := by
      intro hshift
      exact h ((flagShift_involutive k j).symm.trans
        ((congrArg (flagShift k) hshift).trans (flagShift_involutive k l)))
    simp [h,hs]

theorem postSquashing_pauliFlag_cmiNat_le_bell {R E : Type*}
    [Fintype R] [Fintype E] [DecidableEq R] [DecidableEq E]
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (S : CPTP CanonicalEnvironment E) (ψ : (R×Qubit) → ℂ)
    (hψ : IsNormalized ψ) :
    cmiNat (postSquashing p ψ (pauliFlagSquashing S)) ≤
      cmiNat (postSquashing p bellKet (pauliFlagSquashing S)) := by
  apply postSquashing_cmiNat_le_bell_of_chosenCovariance hp0 hp1
    (pauliFlagSquashing S) (flagStinespring S) (flagStinespring_apply S)
    (fun k => flagPermutation k ⊗ₖ (1 : QMatrix E))
    (fun k => flagPermutation k ⊗ₖ (1 : QMatrix (CanonicalEnvironment×E)))
    (fun k => isometry_kronecker (flagPermutation_isometry k) (by simp [IsIsometry]))
    (fun k => isometry_kronecker (flagPermutation_isometry k) (by simp [IsIsometry]))
    _ ψ hψ
  intro k
  exact chosenJointCoefficient_covariance p (flagStinespring S) k _ _
    (flagStinespring_covariance S k)

theorem amplify_reference_sandwich {R I O : Type*}
    [Fintype R] [Fintype I] [Fintype O]
    [DecidableEq I] [DecidableEq O]
    (Φ : QMatrix I →ₗ[ℂ] QMatrix O) (U : QMatrix R) (ρ : QMatrix (R×I)) :
    amplify Φ ((U ⊗ₖ (1 : QMatrix I))*ρ*(U ⊗ₖ (1 : QMatrix I)).conjTranspose)=
      (U ⊗ₖ (1 : QMatrix O))*amplify Φ ρ*(U ⊗ₖ (1 : QMatrix O)).conjTranspose := by
  ext ⟨r,o⟩ ⟨s,p⟩
  have hblock : (show QMatrix I from fun i j =>
      ((U ⊗ₖ (1 : QMatrix I))*ρ*(U ⊗ₖ (1 : QMatrix I)).conjTranspose)
        (r,i) (s,j))=
      ∑ a : R,∑ b : R,(U r a*star (U s b)) •
        (show QMatrix I from fun i j => ρ (a,i) (b,j)) := by
    ext i j
    simp [Matrix.mul_apply,Matrix.kronecker_apply,Matrix.one_apply,
      Matrix.conjTranspose_apply,Fintype.sum_prod_type,Matrix.sum_apply,
      Matrix.smul_apply,star_mul,apply_ite,Finset.sum_mul,Finset.mul_sum,
      mul_assoc,mul_left_comm,mul_comm] <;> rw [Finset.sum_comm]
  change Φ (fun i j =>
    ((U ⊗ₖ (1 : QMatrix I))*ρ*(U ⊗ₖ (1 : QMatrix I)).conjTranspose)
      (r,i) (s,j)) o p=_
  rw [hblock]
  simp [map_sum,map_smul,Matrix.sum_apply,Matrix.smul_apply,
    amplify,Matrix.mul_apply,Matrix.kronecker_apply,Matrix.one_apply,
    Matrix.conjTranspose_apply,Fintype.sum_prod_type,star_mul,apply_ite,
    Finset.sum_mul,Finset.mul_sum,mul_assoc,mul_left_comm,mul_comm] <;>
      rw [Finset.sum_comm]

def bellPair (k : CanonicalEnvironment) : QMatrix (Qubit×Qubit) :=
  (pauli k).transpose ⊗ₖ pauli k

theorem pauliTranspose_isometry (k : CanonicalEnvironment) :
    IsIsometry (pauli k).transpose := by
  ext i j
  fin_cases k <;> fin_cases i <;> fin_cases j <;>
    norm_num [pauli,Matrix.mul_apply,Matrix.transpose_apply,
      Matrix.conjTranspose_apply,Matrix.one_apply,Fin.sum_univ_two]

theorem bellPair_isometry (k : CanonicalEnvironment) : IsIsometry (bellPair k) :=
  isometry_kronecker (pauliTranspose_isometry k) (pauli_unitary k)

theorem bellSignedKet_eq_pair (p : ℝ) (k : CanonicalEnvironment) :
    (fun x : (Qubit×Qubit)×CanonicalEnvironment =>
      (pauliSign k x.2 : ℂ)*extendedInputKet p bellKet x)=
      (bellPair k ⊗ₖ (1 : QMatrix CanonicalEnvironment)).mulVec
        (extendedInputKet p bellKet) := by
  funext x
  rcases x with ⟨⟨a,b⟩,j⟩
  fin_cases k <;> fin_cases a <;> fin_cases b <;> fin_cases j <;>
    apply Complex.ext <;>
    norm_num [bellPair,Matrix.mulVec,dotProduct,Matrix.kronecker_apply,
      Matrix.transpose_apply,Matrix.one_apply,Fintype.sum_prod_type,
      Fin.sum_univ_succ,extendedInputKet,canonicalIsometry,bellKet,pauli,
      pauliSign,pauliWeight,Complex.mul_re,Complex.mul_im] <;> ring

theorem bellSignedDensity_eq_pair (p : ℝ) (k : CanonicalEnvironment) :
    pureDensity (fun x : (Qubit×Qubit)×CanonicalEnvironment =>
      (pauliSign k x.2 : ℂ)*extendedInputKet p bellKet x)=
      (bellPair k ⊗ₖ (1 : QMatrix CanonicalEnvironment))*
        pureDensity (extendedInputKet p bellKet)*
          (bellPair k ⊗ₖ (1 : QMatrix CanonicalEnvironment)).conjTranspose := by
  rw [bellSignedKet_eq_pair]
  exact (QuantumProver.WernerEndpoint.sandwich_crossDensity _ _ _).symm

theorem postSquashing_pauliFlag_bell_controlled {E : Type*}
    [Fintype E] [DecidableEq E] (p : ℝ) (S : CPTP CanonicalEnvironment E) :
    postSquashing p bellKet (pauliFlagSquashing S)=
      Fixed16FlagEntropy.controlledFlagState bellPair (postSquashing p bellKet S) := by
  ext ⟨ab,⟨j,e⟩⟩ ⟨cd,⟨l,f⟩⟩
  change (pauliFlagSquashing S).map
    (fun i k => pureDensity (extendedInputKet p bellKet) (ab,i) (cd,k))
      (j,e) (l,f)=_
  rw [pauliFlagSquashing_apply_block,Fixed16FlagEntropy.controlledFlagState_apply]
  by_cases h : j=l
  · subst l
    simp only [ite_true]
    have hblock : pauliEnvironmentUnitary j*
        (show QMatrix CanonicalEnvironment from
          fun i k => pureDensity (extendedInputKet p bellKet) (ab,i) (cd,k))*
          (pauliEnvironmentUnitary j).conjTranspose=
        (show QMatrix CanonicalEnvironment from
          fun i k => pureDensity
            (fun x : (Qubit×Qubit)×CanonicalEnvironment =>
              (pauliSign j x.2 : ℂ)*extendedInputKet p bellKet x) (ab,i) (cd,k)) := by
      ext i k
      rw [pauliEnvironmentUnitary_selfAdjoint]
      simp [pauliEnvironmentUnitary,Matrix.diagonal_mul,Matrix.mul_diagonal,
        pureDensity,QuantumProver.WernerEndpoint.pureDensity,QuantumProver.WernerEndpoint.crossDensity,
        star_mul,Complex.star_def,mul_assoc,mul_left_comm,mul_comm]
    rw [hblock]
    change (1/4 : ℂ)*amplify S.map (pureDensity
      (fun x : (Qubit×Qubit)×CanonicalEnvironment =>
        (pauliSign j x.2 : ℂ)*extendedInputKet p bellKet x))
          (ab,e) (cd,f)=_
    rw [bellSignedDensity_eq_pair,amplify_reference_sandwich]
    rfl
  · simp [h]

theorem traceMiddle_controlledPair {A B E : Type*}
    [Fintype A] [Fintype B] [Fintype E]
    [DecidableEq A] [DecidableEq B] [DecidableEq E]
    (U : CanonicalEnvironment → QMatrix A) (W : CanonicalEnvironment → QMatrix B)
    (hW : ∀ j,IsIsometry (W j)) (ρ : QMatrix ((A×B)×E)) :
    traceMiddle (Fixed16FlagEntropy.controlledFlagState (fun j => U j ⊗ₖ W j) ρ)=
      Fixed16FlagEntropy.controlledFlagState U (traceMiddle ρ) := by
  ext ⟨a,⟨j,e⟩⟩ ⟨c,⟨l,f⟩⟩
  rw [Fixed16FlagEntropy.controlledFlagState_apply]
  change (∑ b : B,Fixed16FlagEntropy.controlledFlagState
    (fun j => U j ⊗ₖ W j) ρ ((a,b),(j,e)) ((c,b),(l,f)))=_
  simp_rw [Fixed16FlagEntropy.controlledFlagState_apply]
  by_cases h : j=l
  · subst l
    simp only [ite_true,← Finset.mul_sum]
    change (1/4 : ℂ)*traceMiddle
      (((U j ⊗ₖ W j) ⊗ₖ (1 : QMatrix E))*ρ*
        ((U j ⊗ₖ W j) ⊗ₖ (1 : QMatrix E)).conjTranspose) (a,e) (c,f)=_
    rw [Fixed16FlagEntropy.traceMiddle_localPair _ _ (hW j)]
  · simp [h]

theorem traceFirst_controlledPair {A B E : Type*}
    [Fintype A] [Fintype B] [Fintype E]
    [DecidableEq A] [DecidableEq B] [DecidableEq E]
    (U : CanonicalEnvironment → QMatrix A) (W : CanonicalEnvironment → QMatrix B)
    (hU : ∀ j,IsIsometry (U j)) (ρ : QMatrix ((A×B)×E)) :
    traceFirst (Fixed16FlagEntropy.controlledFlagState (fun j => U j ⊗ₖ W j) ρ)=
      Fixed16FlagEntropy.controlledFlagState W (traceFirst ρ) := by
  ext ⟨b,⟨j,e⟩⟩ ⟨d,⟨l,f⟩⟩
  rw [Fixed16FlagEntropy.controlledFlagState_apply]
  change (∑ a : A,Fixed16FlagEntropy.controlledFlagState
    (fun j => U j ⊗ₖ W j) ρ ((a,b),(j,e)) ((a,d),(l,f)))=_
  simp_rw [Fixed16FlagEntropy.controlledFlagState_apply]
  by_cases h : j=l
  · subst l
    simp only [ite_true,← Finset.mul_sum]
    change (1/4 : ℂ)*traceFirst
      (((U j ⊗ₖ W j) ⊗ₖ (1 : QMatrix E))*ρ*
        ((U j ⊗ₖ W j) ⊗ₖ (1 : QMatrix E)).conjTranspose) (b,e) (d,f)=_
    rw [Fixed16FlagEntropy.traceFirst_localPair _ _ (hU j)]
  · simp [h]

theorem partialTraceLeft_controlledPair {A B E : Type*}
    [Fintype A] [Fintype B] [Fintype E]
    [DecidableEq A] [DecidableEq B] [DecidableEq E]
    (U : CanonicalEnvironment → QMatrix A) (W : CanonicalEnvironment → QMatrix B)
    (hU : ∀ j,IsIsometry (U j)) (hW : ∀ j,IsIsometry (W j))
    (ρ : QMatrix ((A×B)×E)) :
    partialTraceLeft (Fixed16FlagEntropy.controlledFlagState (fun j => U j ⊗ₖ W j) ρ)=
      Fixed16FlagEntropy.uniformFlag ⊗ₖ partialTraceLeft ρ := by
  ext ⟨j,e⟩ ⟨l,f⟩
  change (∑ ab : A×B,Fixed16FlagEntropy.controlledFlagState
    (fun j => U j ⊗ₖ W j) ρ (ab,(j,e)) (ab,(l,f)))=_
  simp_rw [Fixed16FlagEntropy.controlledFlagState_apply]
  by_cases h : j=l
  · subst l
    simp only [ite_true,← Finset.mul_sum]
    change (1/4 : ℂ)*partialTraceLeft
      (((U j ⊗ₖ W j) ⊗ₖ (1 : QMatrix E))*ρ*
        ((U j ⊗ₖ W j) ⊗ₖ (1 : QMatrix E)).conjTranspose) e f=_
    rw [partialTraceLeft_localUnitary _ _ (isometry_kronecker (hU j) (hW j))]
    simp [Fixed16FlagEntropy.uniformFlag,Matrix.kronecker_apply]
  · simp [h,Fixed16FlagEntropy.uniformFlag,Matrix.kronecker_apply]

theorem cmiNat_controlledPair {A B E : Type*}
    [Fintype A] [Fintype B] [Fintype E]
    [DecidableEq A] [DecidableEq B] [DecidableEq E]
    (U : CanonicalEnvironment → QMatrix A) (W : CanonicalEnvironment → QMatrix B)
    (hU : ∀ j,IsIsometry (U j)) (hW : ∀ j,IsIsometry (W j))
    {ρ : QMatrix ((A×B)×E)} (hρ : ρ.PosSemidef) (hρT : Matrix.trace ρ=1) :
    cmiNat (Fixed16FlagEntropy.controlledFlagState (fun j => U j ⊗ₖ W j) ρ)=cmiNat ρ := by
  unfold cmiNat
  rw [traceMiddle_controlledPair U W hW,traceFirst_controlledPair U W hU,
    partialTraceLeft_controlledPair U W hU hW,
    Fixed16FlagEntropy.controlledFlagState_entropy U hU
      (traceMiddle_positive hρ) (by rw [Fixed16FlagEntropy.traceMiddle_trace,hρT]),
    Fixed16FlagEntropy.controlledFlagState_entropy W hW
      (traceFirst_positive hρ) (by rw [Fixed16FlagEntropy.traceFirst_trace,hρT]),
    Fixed16FlagEntropy.entropyNat_tensor Fixed16FlagEntropy.uniformFlag_positive
      Fixed16FlagEntropy.uniformFlag_trace (partialTraceLeft_positive hρ)
      (by rw [partialTraceLeft_trace,hρT]),
    Fixed16FlagEntropy.controlledFlagState_entropy (fun j => U j ⊗ₖ W j)
      (fun j => isometry_kronecker (hU j) (hW j)) hρ hρT]
  ring

theorem postSquashing_pauliFlag_bell_cmiNat {E : Type*}
    [Fintype E] [DecidableEq E] {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (S : CPTP CanonicalEnvironment E) :
    cmiNat (postSquashing p bellKet (pauliFlagSquashing S))=
      cmiNat (postSquashing p bellKet S) := by
  rw [postSquashing_pauliFlag_bell_controlled]
  exact cmiNat_controlledPair (fun k => (pauli k).transpose) pauli
    pauliTranspose_isometry pauli_unitary (postSquashing_positive p bellKet S)
    (postSquashingDensity hp0 hp1 bellKet bellKet_normalized S).trace_one

theorem teleportation_allInput_cmiNat_le_physicalBell {R E : Type*}
    [Fintype R] [Fintype E] [DecidableEq R] [DecidableEq E]
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (S : CPTP CanonicalEnvironment E) (ψ : (R×Qubit) → ℂ)
    (hψ : IsNormalized ψ) :
    cmiNat (postSquashing p ψ (pauliFlagSquashing S)) ≤
      cmiNat (postSquashing p bellKet S) := by
  rw [← postSquashing_pauliFlag_bell_cmiNat hp0 hp1 S]
  exact postSquashing_pauliFlag_cmiNat_le_bell hp0 hp1 S ψ hψ

theorem channelSquashed_eq_bell {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    channelSquashed p=squashedInputValue p bellKet := by
  apply channelSquashed_eq_of_cost_dominance p bellKet bellKet_normalized
    (fun r ψ hψ => inputCosts_bddBelow p ψ)
  intro r ψ hψ b hb
  rcases hb with ⟨e,S,rfl⟩
  let ef : (CanonicalEnvironment×Fin e) ≃
      Fin (Fintype.card (CanonicalEnvironment×Fin e)) := Fintype.equivFin _
  let Sf := (pauliFlagSquashing S).reindexOutput ef
  refine ⟨cmiBits (postSquashing p ψ Sf),⟨_,Sf,rfl⟩,?_⟩
  have heq : cmiBits (postSquashing p ψ Sf)=
      cmiBits (postSquashing p ψ (pauliFlagSquashing S)) := by
    dsimp [Sf]
    rw [postSquashing_reindexOutput]
    exact cmiBits_reindexEnvironment ef
      (postSquashing_positive p ψ (pauliFlagSquashing S))
  rw [heq]
  exact div_le_div_of_nonneg_right
    (teleportation_allInput_cmiNat_le_physicalBell hp0 hp1 S ψ hψ)
    (Real.log_nonneg (by norm_num))

theorem physicalTeleportation_cmiNat_le_resource {R E : Type*}
    [Fintype R] [Fintype E] [DecidableEq R] [DecidableEq E]
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (S : CPTP CanonicalEnvironment E) (ψ : (R×Qubit) → ℂ)
    (hψ : IsNormalized ψ) :
    cmiNat (flaggedTeleportationOutput p S ψ) ≤
      cmiNat (postSquashing p bellKet S) := by
  rw [flaggedTeleportationOutput_eq_postSquashing]
  exact teleportation_allInput_cmiNat_le_physicalBell hp0 hp1 S ψ hψ

end QuantumProver.DepolarizingSquashedEntanglement.Teleportation

import QuantumProver.InformationTheory.DepolarizingPrivateInformation.CorrelatedInputs

noncomputable section
namespace QuantumProver.DepolarizingPrivateInformation
open scoped BigOperators ComplexOrder
open Matrix

def wordTensor {ι κ : Type*} [Fintype ι] (A : ι → CMat κ) : CMat (ι → κ) :=
  fun x y => ∏ i, A i (x i) (y i)

theorem wordTensor_conjTranspose {ι κ : Type*} [Fintype ι]
    (A : ι → CMat κ) :
    (wordTensor A)ᴴ = wordTensor (fun i => (A i)ᴴ) := by
  ext x y
  simp [wordTensor, Matrix.conjTranspose_apply]

theorem wordTensor_mul {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] (A B : ι → CMat κ) :
    wordTensor A * wordTensor B = wordTensor (fun i => A i * B i) := by
  ext x y
  simp only [wordTensor, Matrix.mul_apply, ← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i z => A i (x i) z * B i z (y i))).symm

theorem wordTensor_one {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [DecidableEq κ] : wordTensor (fun (_ : ι) => (1 : CMat κ)) = 1 := by
  classical
  ext x y
  by_cases hxy : x=y
  · subst y
    simp [wordTensor]
  · have hn : ∃ i, x i ≠ y i := by
      by_contra h
      push_neg at h
      exact hxy (funext h)
    obtain ⟨i,hi⟩ := hn
    have hp : (∏ i, (1 : CMat κ) (x i) (y i)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) (by simp [Matrix.one_apply, hi])
    change (∏ i, (1 : CMat κ) (x i) (y i)) = (1 : CMat (ι → κ)) x y
    rw [hp]
    simp [Matrix.one_apply, hxy]

theorem wordTensor_sum {ι κ α : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype α] (A : ι → α → CMat κ) :
    (∑ f : ι → α, wordTensor (fun i => A i (f i))) =
      wordTensor (fun i => ∑ a, A i a) := by
  ext x y
  simp only [Matrix.sum_apply, wordTensor]
  exact (Fintype.prod_sum (fun i a => A i a (x i) (y i))).symm

theorem tensorKraus_eq_wordTensor (p : ℝ) (n : ℕ) (e : ErrorWord n) :
    tensorKraus p n e = wordTensor (fun i => kraus p (e i)) := rfl

theorem tensorKraus_gram (p : ℝ) (n : ℕ) (e : ErrorWord n) :
    (tensorKraus p n e)ᴴ * tensorKraus p n e =
      wordTensor (fun i => (kraus p (e i))ᴴ * kraus p (e i)) := by
  rw [tensorKraus_eq_wordTensor, wordTensor_conjTranspose, wordTensor_mul]

theorem tensorKraus_complete {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (n : ℕ) :
    ∑ e : ErrorWord n, (tensorKraus p n e)ᴴ * tensorKraus p n e =
      (1 : CMat (QubitWord n)) := by
  simp_rw [tensorKraus_gram]
  rw [wordTensor_sum (fun (_ : Fin n) (e : PauliIndex) =>
    (kraus p e)ᴴ * kraus p e)]
  have h : (fun (_ : Fin n) => ∑ e : PauliIndex, (kraus p e)ᴴ * kraus p e) =
      (fun (_ : Fin n) => (1 : QubitMatrix)) :=
    funext (fun _ => kraus_complete hp0 hp1)
  rw [h, wordTensor_one]

def tensorStinespring (p : ℝ) (n : ℕ) :
    Matrix (QubitWord n × ErrorWord n) (QubitWord n) ℂ :=
  fun be x => tensorKraus p n be.2 be.1 x

def jointTensorChannel (p : ℝ) (n : ℕ) (ρ : CMat (QubitWord n)) :
    CMat (QubitWord n × ErrorWord n) :=
  tensorStinespring p n * ρ * (tensorStinespring p n)ᴴ

theorem partialTraceRight_jointTensor (p : ℝ) (n : ℕ) (ρ : CMat (QubitWord n)) :
    partialTraceRight (jointTensorChannel p n ρ) = bobTensorChannel p n ρ := by
  ext x y
  simp [partialTraceRight, jointTensorChannel, tensorStinespring, bobTensorChannel,
    Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.sum_apply, Finset.sum_mul]

theorem partialTraceLeft_jointTensor (p : ℝ) (n : ℕ) (ρ : CMat (QubitWord n)) :
    partialTraceLeft (jointTensorChannel p n ρ) = eveTensorChannel p n ρ := by
  ext e f
  simp [partialTraceLeft, jointTensorChannel, tensorStinespring, eveTensorChannel,
    Matrix.trace, Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul]

theorem tensorStinespring_complete {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (n : ℕ) :
    (tensorStinespring p n)ᴴ * tensorStinespring p n =
      (1 : CMat (QubitWord n)) := by
  calc
    _ = ∑ e : ErrorWord n, (tensorKraus p n e)ᴴ * tensorKraus p n e := by
      ext x y
      simp only [tensorStinespring, Matrix.mul_apply, Matrix.conjTranspose_apply,
        Fintype.sum_prod_type, Matrix.sum_apply]
      exact Finset.sum_comm
    _ = 1 := tensorKraus_complete hp0 hp1 n

theorem trace_jointTensorChannel {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (n : ℕ) (ρ : CMat (QubitWord n)) :
    Matrix.trace (jointTensorChannel p n ρ) = Matrix.trace ρ := by
  rw [jointTensorChannel, Matrix.trace_mul_comm, ← Matrix.mul_assoc,
    tensorStinespring_complete hp0 hp1 n, Matrix.one_mul]

theorem jointTensorChannel_posSemidef (p : ℝ) (n : ℕ)
    {ρ : CMat (QubitWord n)} (hρ : ρ.PosSemidef) :
    (jointTensorChannel p n ρ).PosSemidef :=
  hρ.mul_mul_conjTranspose_same (tensorStinespring p n)

theorem bobTensorChannel_isDensity {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (n : ℕ) {ρ : CMat (QubitWord n)} (hρ : IsDensity ρ) :
    IsDensity (bobTensorChannel p n ρ) := by
  rw [← partialTraceRight_jointTensor]
  exact ⟨partialTraceRight_posSemidef (jointTensorChannel_posSemidef p n hρ.1), by
    rw [trace_partialTraceRight, trace_jointTensorChannel hp0 hp1 n, hρ.2]⟩

theorem eveTensorChannel_isDensity {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (n : ℕ) {ρ : CMat (QubitWord n)} (hρ : IsDensity ρ) :
    IsDensity (eveTensorChannel p n ρ) := by
  rw [← partialTraceLeft_jointTensor]
  exact ⟨partialTraceLeft_posSemidef (jointTensorChannel_posSemidef p n hρ.1), by
    rw [trace_partialTraceLeft, trace_jointTensorChannel hp0 hp1 n, hρ.2]⟩

def evenOddEquiv (m : ℕ) : Fin m × Fin 2 ≃ Fin (2*m) where
  toFun := fun jb => ⟨2*jb.1.val+jb.2.val, by omega⟩
  invFun := fun i => (⟨i.val/2, by omega⟩, ⟨i.val%2, by omega⟩)
  left_inv := by
    rintro ⟨j,b⟩
    apply Prod.ext
    · apply Fin.ext
      change (2*j.val+b.val)/2=j.val
      omega
    · apply Fin.ext
      change (2*j.val+b.val)%2=b.val
      omega
  right_inv := by
    intro i
    apply Fin.ext
    change 2*(i.val/2)+i.val%2=i.val
    omega

def bitPairEquiv (m : ℕ) : ((Fin m × Fin 2) → Qubit) ≃ (Fin m → PairQubit) where
  toFun := fun x j => (x (j,0), x (j,1))
  invFun := fun x jb => if jb.2 = 0 then (x jb.1).1 else (x jb.1).2
  left_inv := by
    intro x
    funext jb
    rcases jb with ⟨j,b⟩
    fin_cases b <;> rfl
  right_inv := by
    intro x
    funext j
    exact Prod.ext rfl rfl

def pairedWordEquiv (m : ℕ) : QubitWord (2*m) ≃ (Fin m → PairQubit) :=
  (Equiv.arrowCongr (evenOddEquiv m).symm (Equiv.refl Qubit)).trans (bitPairEquiv m)

@[simp] theorem pairedWordEquiv_apply (m : ℕ) (x : QubitWord (2*m)) (j : Fin m) :
    pairedWordEquiv m x j = (x (evenSite m j), x (oddSite m j)) := by
  rfl

theorem repeatedMass_sum (u v : ℝ) (m : ℕ) :
    ∑ x : QubitWord (2*m), ∏ j,
      correlatedMass u v (x (evenSite m j),x (oddSite m j)) = 1 := by
  calc
    _ = ∑ x : QubitWord (2*m), ∏ j, correlatedMass u v (pairedWordEquiv m x j) := by
      simp only [pairedWordEquiv_apply]
    _ = ∑ z : Fin m → PairQubit, ∏ j, correlatedMass u v (z j) :=
      (pairedWordEquiv m).sum_comp (fun z => ∏ j, correlatedMass u v (z j))
    _ = ∏ j : Fin m, ∑ z : PairQubit, correlatedMass u v z :=
      (Fintype.prod_sum (fun (_ : Fin m) (z : PairQubit) => correlatedMass u v z)).symm
    _ = 1 := by simp [correlatedMass_sum]

theorem repeatedTwoUseRho_eq_diagonal (u v : ℝ) (m : ℕ) :
    repeatedTwoUseRho u v m = Matrix.diagonal (fun x : QubitWord (2*m) =>
      ((∏ j, correlatedMass u v (x (evenSite m j),x (oddSite m j)) : ℝ) : ℂ)) := by
  classical
  ext x y
  by_cases hxy : x=y
  · subst y
    simp [repeatedTwoUseRho, twoUseRho, Matrix.diagonal]
  · have hne : ¬ ∀ j : Fin m,
        (x (evenSite m j),x (oddSite m j)) =
        (y (evenSite m j),y (oddSite m j)) := by
      intro h
      apply hxy
      apply (pairedWordEquiv m).injective
      funext j
      simpa only [pairedWordEquiv_apply] using h j
    push_neg at hne
    obtain ⟨j,hj⟩ := hne
    have hz : twoUseRho u v (x (evenSite m j),x (oddSite m j))
        (y (evenSite m j),y (oddSite m j)) = 0 := by
      simp [twoUseRho, Matrix.diagonal, hj]
    have hp : (∏ j, twoUseRho u v
        (x (evenSite m j),x (oddSite m j))
        (y (evenSite m j),y (oddSite m j))) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ j) hz
    simp [repeatedTwoUseRho, Matrix.diagonal, hxy, hp]

theorem repeatedTwoUseRho_trace (u v : ℝ) (m : ℕ) :
    Matrix.trace (repeatedTwoUseRho u v m) = 1 := by
  rw [repeatedTwoUseRho_eq_diagonal, Matrix.trace_diagonal]
  exact_mod_cast repeatedMass_sum u v m

theorem repeatedTwoUseRho_psd {u v : ℝ} (m : ℕ)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hv : 2*|v| ≤ 1-u) :
    (repeatedTwoUseRho u v m).PosSemidef := by
  rw [repeatedTwoUseRho_eq_diagonal]
  apply Matrix.PosSemidef.diagonal
  intro x
  apply Complex.zero_le_real.mpr
  exact Finset.prod_nonneg (fun j _ => correlatedMass_nonneg hu0 hu1 hv _)

def repeatedTwoUseDensity (u v : ℝ) (m : ℕ)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hv : 2*|v| ≤ 1-u) :
    Density (QubitWord (2*m)) where
  mat := repeatedTwoUseRho u v m
  psd := repeatedTwoUseRho_psd m hu0 hu1 hv
  trace_one := repeatedTwoUseRho_trace u v m

def savedBinaryEnsemble (u v : ℝ) (m : ℕ)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hv : 2*|v| ≤ 1-u) :
    FiniteEnsemble (QubitWord (2*m)) 2 where
  weight := fun _ => 1/2
  weight_nonneg := by intro x; norm_num
  weight_sum := by norm_num [Fin.sum_univ_two]
  state := fun x => repeatedTwoUseDensity u (if x=0 then v else -v) m hu0 hu1 (by
    split_ifs <;> simpa only [abs_neg] using hv)

theorem savedBinaryEnsemble_state (u v : ℝ) (m : ℕ)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hv : 2*|v| ≤ 1-u) (x : Fin 2) :
    ((savedBinaryEnsemble u v m hu0 hu1 hv).state x).mat =
      signedRepeatedInput u v m x := rfl

theorem savedBinaryEnsemble_privateInformation (p u v : ℝ) (m : ℕ)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hv : 2*|v| ≤ 1-u) :
    privateInformation p (2*m) (savedBinaryEnsemble u v m hu0 hu1 hv) =
      savedBinaryPrivateInformation p u v m := by
  have hm : ensembleMean (savedBinaryEnsemble u v m hu0 hu1 hv) =
      (1/2 : ℂ) • (repeatedTwoUseRho u v m + repeatedTwoUseRho u (-v) m) := by
    simp [ensembleMean, savedBinaryEnsemble, repeatedTwoUseDensity,
      Fin.sum_univ_two, smul_add]
  unfold privateInformation channelHolevo savedBinaryPrivateInformation
  rw [hm]
  simp [savedBinaryEnsemble, repeatedTwoUseDensity, Fin.sum_univ_two]
  ring

theorem wordTensor_trace {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] (A : ι → CMat κ) :
    Matrix.trace (wordTensor A) = ∏ i, Matrix.trace (A i) := by
  simp only [wordTensor, Matrix.trace]
  exact (Fintype.prod_sum (fun i x => A i x x)).symm

theorem bobTensorChannel_wordTensor (p : ℝ) (n : ℕ)
    (ρ : Fin n → QubitMatrix) :
    bobTensorChannel p n (wordTensor ρ) =
      wordTensor (fun i => bobChannel p (ρ i)) := by
  unfold bobTensorChannel
  simp_rw [tensorKraus_eq_wordTensor, wordTensor_conjTranspose, wordTensor_mul]
  exact wordTensor_sum (fun i e => kraus p e * ρ i * (kraus p e)ᴴ)

theorem eveTensorChannel_wordTensor (p : ℝ) (n : ℕ)
    (ρ : Fin n → QubitMatrix) :
    eveTensorChannel p n (wordTensor ρ) =
      wordTensor (fun i => eveChannel p (ρ i)) := by
  ext e f
  simp only [eveTensorChannel, tensorKraus_eq_wordTensor, wordTensor_conjTranspose,
    wordTensor_mul, wordTensor_trace]
  rfl

theorem trace_submatrix_equiv {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (A : CMat κ) :
    Matrix.trace (A.submatrix e e) = Matrix.trace A := by
  exact e.sum_comp (fun i => A i i)

abbrev PairError := PauliIndex × PauliIndex

def pairKraus (p : ℝ) (e : PairError) : CMat PairQubit :=
  fun x y => kraus p e.1 x.1 y.1 * kraus p e.2 x.2 y.2

def pairBobChannel (p : ℝ) (ρ : CMat PairQubit) : CMat PairQubit :=
  ∑ e : PairError, pairKraus p e * ρ * (pairKraus p e)ᴴ

def pairEveChannel (p : ℝ) (ρ : CMat PairQubit) : CMat PairError :=
  fun e f => Matrix.trace (pairKraus p e * ρ * (pairKraus p f)ᴴ)

def errorPairEquiv (m : ℕ) :
    ((Fin m × Fin 2) → PauliIndex) ≃ (Fin m → PairError) where
  toFun := fun x j => (x (j,0), x (j,1))
  invFun := fun x jb => if jb.2 = 0 then (x jb.1).1 else (x jb.1).2
  left_inv := by
    intro x
    funext jb
    rcases jb with ⟨j,b⟩
    fin_cases b <;> rfl
  right_inv := by
    intro x
    funext j
    exact Prod.ext rfl rfl

def pairedErrorEquiv (m : ℕ) : ErrorWord (2*m) ≃ (Fin m → PairError) :=
  (Equiv.arrowCongr (evenOddEquiv m).symm (Equiv.refl PauliIndex)).trans
    (errorPairEquiv m)

@[simp] theorem pairedErrorEquiv_apply (m : ℕ) (e : ErrorWord (2*m)) (j : Fin m) :
    pairedErrorEquiv m e j = (e (evenSite m j), e (oddSite m j)) := by
  rfl

theorem tensorKraus_eq_pairedTensor (p : ℝ) (m : ℕ) (e : ErrorWord (2*m)) :
    tensorKraus p (2*m) e =
      (wordTensor (fun j => pairKraus p (pairedErrorEquiv m e j))).submatrix
        (pairedWordEquiv m) (pairedWordEquiv m) := by
  ext x y
  change (∏ i, kraus p (e i) (x i) (y i)) =
    ∏ j, pairKraus p (pairedErrorEquiv m e j)
      (pairedWordEquiv m x j) (pairedWordEquiv m y j)
  calc
    _ = ∏ jb : Fin m × Fin 2, kraus p (e (evenOddEquiv m jb))
        (x (evenOddEquiv m jb)) (y (evenOddEquiv m jb)) :=
      ((evenOddEquiv m).prod_comp (fun i => kraus p (e i) (x i) (y i))).symm
    _ = _ := by
      rw [Fintype.prod_prod_type]
      apply Finset.prod_congr rfl
      intro j _
      simp [Fin.prod_univ_two, pairKraus, evenOddEquiv, evenSite, oddSite]

theorem repeatedTwoUseRho_eq_pairedTensor (u v : ℝ) (m : ℕ) :
    repeatedTwoUseRho u v m =
      (wordTensor (fun (_ : Fin m) => twoUseRho u v)).submatrix
        (pairedWordEquiv m) (pairedWordEquiv m) := by
  ext x y
  rfl

theorem bobTensorChannel_repeatedTwoUseRho (p u v : ℝ) (m : ℕ) :
    bobTensorChannel p (2*m) (repeatedTwoUseRho u v m) =
      (wordTensor (fun (_ : Fin m) => pairBobChannel p (twoUseRho u v))).submatrix
        (pairedWordEquiv m) (pairedWordEquiv m) := by
  unfold bobTensorChannel
  calc
    _ = ∑ e : ErrorWord (2*m),
        (wordTensor (fun j => pairKraus p (pairedErrorEquiv m e j) *
          twoUseRho u v * (pairKraus p (pairedErrorEquiv m e j))ᴴ)).submatrix
            (pairedWordEquiv m) (pairedWordEquiv m) := by
      apply Finset.sum_congr rfl
      intro e _
      rw [tensorKraus_eq_pairedTensor, repeatedTwoUseRho_eq_pairedTensor,
        Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv,
        Matrix.submatrix_mul_equiv, wordTensor_conjTranspose,
        wordTensor_mul, wordTensor_mul]
    _ = (∑ e : ErrorWord (2*m),
        wordTensor (fun j => pairKraus p (pairedErrorEquiv m e j) *
          twoUseRho u v * (pairKraus p (pairedErrorEquiv m e j))ᴴ)).submatrix
            (pairedWordEquiv m) (pairedWordEquiv m) := by
      ext x y
      simp only [Matrix.sum_apply, Matrix.submatrix_apply]
    _ = (∑ e : Fin m → PairError,
        wordTensor (fun j => pairKraus p (e j) *
          twoUseRho u v * (pairKraus p (e j))ᴴ)).submatrix
            (pairedWordEquiv m) (pairedWordEquiv m) := by
      rw [(pairedErrorEquiv m).sum_comp
        (fun e => wordTensor (fun j => pairKraus p (e j) *
          twoUseRho u v * (pairKraus p (e j))ᴴ))]
    _ = _ := by
      rw [wordTensor_sum (fun (_ : Fin m) (e : PairError) =>
        pairKraus p e * twoUseRho u v * (pairKraus p e)ᴴ)]
      rfl

theorem eveTensorChannel_repeatedTwoUseRho (p u v : ℝ) (m : ℕ) :
    eveTensorChannel p (2*m) (repeatedTwoUseRho u v m) =
      (wordTensor (fun (_ : Fin m) => pairEveChannel p (twoUseRho u v))).submatrix
        (pairedErrorEquiv m) (pairedErrorEquiv m) := by
  ext e f
  simp only [eveTensorChannel, tensorKraus_eq_pairedTensor,
    repeatedTwoUseRho_eq_pairedTensor, Matrix.conjTranspose_submatrix,
    Matrix.submatrix_mul_equiv, trace_submatrix_equiv, wordTensor_conjTranspose,
    wordTensor_mul, wordTensor_trace]
  rfl

open scoped Kronecker

theorem pairKraus_eq_kronecker (p : ℝ) (e : PairError) :
    pairKraus p e = kraus p e.1 ⊗ₖ kraus p e.2 := rfl

theorem pairKraus_complete {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ∑ e : PairError, (pairKraus p e)ᴴ * pairKraus p e = (1 : CMat PairQubit) := by
  simp_rw [pairKraus_eq_kronecker, Matrix.conjTranspose_kronecker,
    ← Matrix.mul_kronecker_mul]
  calc
    _ = (∑ e : PauliIndex, (kraus p e)ᴴ * kraus p e) ⊗ₖ
        (∑ e : PauliIndex, (kraus p e)ᴴ * kraus p e) := by
      ext x y
      rcases x with ⟨x₁,x₂⟩
      rcases y with ⟨y₁,y₂⟩
      simp only [Matrix.sum_apply, Matrix.kronecker_apply, Fintype.sum_prod_type,
        Finset.sum_mul, Finset.mul_sum]
      exact Finset.sum_comm
    _ = 1 := by rw [kraus_complete hp0 hp1, Matrix.one_kronecker_one]

def pairStinespring (p : ℝ) :
    Matrix (PairQubit × PairError) PairQubit ℂ :=
  fun be x => pairKraus p be.2 be.1 x

def pairJointChannel (p : ℝ) (ρ : CMat PairQubit) : CMat (PairQubit × PairError) :=
  pairStinespring p * ρ * (pairStinespring p)ᴴ

theorem partialTraceRight_pairJoint (p : ℝ) (ρ : CMat PairQubit) :
    partialTraceRight (pairJointChannel p ρ) = pairBobChannel p ρ := by
  ext x y
  simp [partialTraceRight, pairJointChannel, pairStinespring, pairBobChannel,
    Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.sum_apply]

theorem partialTraceLeft_pairJoint (p : ℝ) (ρ : CMat PairQubit) :
    partialTraceLeft (pairJointChannel p ρ) = pairEveChannel p ρ := by
  ext e f
  simp [partialTraceLeft, pairJointChannel, pairStinespring, pairEveChannel,
    Matrix.trace, Matrix.mul_apply, Matrix.conjTranspose_apply]

theorem pairStinespring_complete {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (pairStinespring p)ᴴ * pairStinespring p = (1 : CMat PairQubit) := by
  calc
    _ = ∑ e : PairError, (pairKraus p e)ᴴ * pairKraus p e := by
      ext x y
      simp only [pairStinespring, Matrix.mul_apply, Matrix.conjTranspose_apply,
        Matrix.sum_apply]
      rw [Fintype.sum_prod_type]
      exact Finset.sum_comm
    _ = 1 := pairKraus_complete hp0 hp1

theorem trace_pairJointChannel {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (ρ : CMat PairQubit) : Matrix.trace (pairJointChannel p ρ) = Matrix.trace ρ := by
  rw [pairJointChannel, Matrix.trace_mul_comm, ← Matrix.mul_assoc,
    pairStinespring_complete hp0 hp1, Matrix.one_mul]

theorem pairJointChannel_posSemidef (p : ℝ) {ρ : CMat PairQubit}
    (hρ : ρ.PosSemidef) : (pairJointChannel p ρ).PosSemidef :=
  hρ.mul_mul_conjTranspose_same (pairStinespring p)

theorem pairBobChannel_isDensity {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {ρ : CMat PairQubit} (hρ : IsDensity ρ) : IsDensity (pairBobChannel p ρ) := by
  rw [← partialTraceRight_pairJoint]
  exact ⟨partialTraceRight_posSemidef (pairJointChannel_posSemidef p hρ.1), by
    rw [trace_partialTraceRight, trace_pairJointChannel hp0 hp1, hρ.2]⟩

theorem pairEveChannel_isDensity {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {ρ : CMat PairQubit} (hρ : IsDensity ρ) : IsDensity (pairEveChannel p ρ) := by
  rw [← partialTraceLeft_pairJoint]
  exact ⟨partialTraceLeft_posSemidef (pairJointChannel_posSemidef p hρ.1), by
    rw [trace_partialTraceLeft, trace_pairJointChannel hp0 hp1, hρ.2]⟩

open scoped MatrixOrder Matrix.Norms.L2Operator

theorem wordTensor_posSemidef {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (A : ι → CMat κ)
    (hA : ∀ i, (A i).PosSemidef) : (wordTensor A).PosSemidef := by
  let B : ι → CMat κ := fun i => CFC.sqrt (A i)
  have hB : ∀ i, (B i)ᴴ = B i :=
    fun i => (CFC.sqrt_nonneg (A i)).posSemidef.1
  have hsq : ∀ i, (B i)ᴴ * B i = A i := by
    intro i
    rw [hB i]
    exact CFC.sqrt_mul_sqrt_self (A i) (hA i).nonneg
  have hgram : (wordTensor B)ᴴ * wordTensor B = wordTensor A := by
    rw [wordTensor_conjTranspose, wordTensor_mul]
    congr 1
    funext i
    exact hsq i
  rw [← hgram]
  exact Matrix.posSemidef_conjTranspose_mul_self (wordTensor B)

theorem wordTensor_isDensity {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (A : ι → CMat κ)
    (hA : ∀ i, IsDensity (A i)) : IsDensity (wordTensor A) := by
  constructor
  · exact wordTensor_posSemidef A (fun i => (hA i).1)
  · rw [wordTensor_trace]
    have ht : ∀ i, Matrix.trace (A i) = 1 := fun i => (hA i).2
    simp_rw [ht]
    simp

theorem wordTensor_sqrt {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (A : ι → CMat κ)
    (hA : ∀ i, (A i).PosSemidef) :
    CFC.sqrt (wordTensor A) = wordTensor (fun i => CFC.sqrt (A i)) := by
  have hsq : wordTensor (fun i => CFC.sqrt (A i)) *
      wordTensor (fun i => CFC.sqrt (A i)) = wordTensor A := by
    rw [wordTensor_mul]
    congr 1
    funext i
    exact CFC.sqrt_mul_sqrt_self (A i) (hA i).nonneg
  exact CFC.sqrt_unique hsq
    (wordTensor_posSemidef (fun i => CFC.sqrt (A i))
      (fun i => (CFC.sqrt_nonneg (A i)).posSemidef)).nonneg

theorem sqrt_submatrix_equiv {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (e : ι ≃ κ) {A : CMat κ}
    (hA : A.PosSemidef) :
    CFC.sqrt (A.submatrix e e) = (CFC.sqrt A).submatrix e e := by
  have hs : 0 ≤ (CFC.sqrt A).submatrix e e :=
    ((CFC.sqrt_nonneg A).posSemidef.submatrix e).nonneg
  apply (CFC.sqrt_eq_iff _ _ (hA.submatrix e).nonneg hs).mpr
  rw [Matrix.submatrix_mul_equiv, CFC.sqrt_mul_sqrt_self A hA.nonneg]

theorem trace_wordTensor_sqrt_product {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (A B : ι → CMat κ) (hA : ∀ i, (A i).PosSemidef)
    (hB : ∀ i, (B i).PosSemidef) :
    Matrix.trace (CFC.sqrt (wordTensor A) * CFC.sqrt (wordTensor B)) =
      ∏ i, Matrix.trace (CFC.sqrt (A i) * CFC.sqrt (B i)) := by
  rw [wordTensor_sqrt A hA, wordTensor_sqrt B hB, wordTensor_mul,
    wordTensor_trace]

theorem correlatedMass_ge_eighth {u v : ℝ} (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1/4) (hv : |v| ≤ 1/8) (x : PairQubit) :
    1/8 ≤ correlatedMass u v x := by
  have hvp : v ≤ |v| := le_abs_self v
  have hvn : -v ≤ |v| := neg_le_abs v
  rcases x with ⟨x,y⟩
  fin_cases x <;> fin_cases y <;>
    norm_num [correlatedMass, spinSign] <;> linarith

theorem twoUseRho_sub_eighth_psd {u v : ℝ} (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1/4) (hv : |v| ≤ 1/8) :
    (twoUseRho u v - (1/8 : ℂ) • (1 : CMat PairQubit)).PosSemidef := by
  have hdiag : twoUseRho u v - (1/8 : ℂ) • (1 : CMat PairQubit) =
      Matrix.diagonal (fun x => ((correlatedMass u v x - 1/8 : ℝ) : ℂ)) := by
    ext x y
    by_cases hxy : x=y
    · subst y
      simp [twoUseRho, Matrix.diagonal, Matrix.smul_apply, smul_eq_mul]
    · simp [twoUseRho, Matrix.diagonal, Matrix.one_apply, Matrix.smul_apply,
        smul_eq_mul, hxy]
  rw [hdiag]
  apply Matrix.PosSemidef.diagonal
  intro x
  exact Complex.zero_le_real.mpr
    (sub_nonneg.mpr (correlatedMass_ge_eighth hu0 hu1 hv x))

theorem kraus_conjTranspose (p : ℝ) (e : PauliIndex) :
    (kraus p e)ᴴ = kraus p e := by
  simp [kraus, Matrix.conjTranspose_smul]

theorem pairKraus_conjTranspose (p : ℝ) (e : PairError) :
    (pairKraus p e)ᴴ = pairKraus p e := by
  simp only [pairKraus_eq_kronecker, Matrix.conjTranspose_kronecker,
    kraus_conjTranspose]

theorem pairBobChannel_one {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    pairBobChannel p (1 : CMat PairQubit) = 1 := by
  unfold pairBobChannel
  simp_rw [Matrix.mul_one, pairKraus_conjTranspose]
  simpa only [pairKraus_conjTranspose] using pairKraus_complete hp0 hp1

theorem pairBobChannel_sub (p : ℝ) (ρ σ : CMat PairQubit) :
    pairBobChannel p (ρ-σ) = pairBobChannel p ρ - pairBobChannel p σ := by
  simp [pairBobChannel, Matrix.mul_sub, Matrix.sub_mul, Finset.sum_sub_distrib]

theorem pairEveChannel_sub (p : ℝ) (ρ σ : CMat PairQubit) :
    pairEveChannel p (ρ-σ) = pairEveChannel p ρ - pairEveChannel p σ := by
  ext e f
  simp [pairEveChannel, Matrix.mul_sub, Matrix.sub_mul, Matrix.trace_sub]

theorem pairBobChannel_smul (p : ℝ) (r : ℂ) (ρ : CMat PairQubit) :
    pairBobChannel p (r • ρ) = r • pairBobChannel p ρ := by
  simp [pairBobChannel, Matrix.smul_mul, Matrix.mul_smul, ← Finset.smul_sum]

theorem pairEveChannel_smul (p : ℝ) (r : ℂ) (ρ : CMat PairQubit) :
    pairEveChannel p (r • ρ) = r • pairEveChannel p ρ := by
  ext e f
  simp [pairEveChannel, Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul]

theorem pairBobChannel_posSemidef (p : ℝ) {ρ : CMat PairQubit}
    (hρ : ρ.PosSemidef) : (pairBobChannel p ρ).PosSemidef := by
  rw [← partialTraceRight_pairJoint]
  exact partialTraceRight_posSemidef (pairJointChannel_posSemidef p hρ)

theorem pairEveChannel_posSemidef (p : ℝ) {ρ : CMat PairQubit}
    (hρ : ρ.PosSemidef) : (pairEveChannel p ρ).PosSemidef := by
  rw [← partialTraceLeft_pairJoint]
  exact partialTraceLeft_posSemidef (pairJointChannel_posSemidef p hρ)

theorem pairBobChannel_correlated_sub_eighth_psd {p u v : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1/4) (hv : |v| ≤ 1/8) :
    (pairBobChannel p (twoUseRho u v) -
      (1/8 : ℂ) • (1 : CMat PairQubit)).PosSemidef := by
  have h := pairBobChannel_posSemidef p (twoUseRho_sub_eighth_psd hu0 hu1 hv)
  rw [pairBobChannel_sub, pairBobChannel_smul, pairBobChannel_one hp0 hp1] at h
  exact h

theorem pairEveChannel_correlated_sub_reference_psd {p u v : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1/4) (hv : |v| ≤ 1/8) :
    (pairEveChannel p (twoUseRho u v) -
      (1/8 : ℂ) • pairEveChannel p (1 : CMat PairQubit)).PosSemidef := by
  have h := pairEveChannel_posSemidef p (twoUseRho_sub_eighth_psd hu0 hu1 hv)
  rw [pairEveChannel_sub, pairEveChannel_smul] at h
  exact h

theorem pauli_trace_inner (e f : PauliIndex) :
    Matrix.trace (pauli e * (pauli f)ᴴ) = if e=f then 2 else 0 := by
  rw [pauli_conjTranspose]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_two]
  fin_cases e <;> fin_cases f <;>
    norm_num [pauli, Complex.I_mul_I]

theorem krausWeight_pos {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1)
    (e : PauliIndex) : 0 < krausWeight p e := by
  unfold krausWeight
  split_ifs <;> nlinarith

theorem kraus_trace_inner (p : ℝ) (e f : PauliIndex) :
    Matrix.trace (kraus p e * (kraus p f)ᴴ) =
      ((Real.sqrt (krausWeight p e) * Real.sqrt (krausWeight p f) : ℝ) : ℂ) *
        Matrix.trace (pauli e * (pauli f)ᴴ) := by
  simp [kraus, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.trace_smul, smul_smul, smul_eq_mul, ← Complex.ofReal_mul, mul_comm]

theorem eveChannel_one {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    eveChannel p (1 : QubitMatrix) =
      Matrix.diagonal (fun e => 2 * (krausWeight p e : ℂ)) := by
  ext e f
  simp only [eveChannel, Matrix.mul_one, kraus_trace_inner, pauli_trace_inner]
  by_cases h : e=f
  · subst f
    simp [Matrix.diagonal, Real.mul_self_sqrt (krausWeight_nonneg hp0 hp1 e),
      mul_comm]
  · simp [Matrix.diagonal, h, smul_eq_mul]

theorem wordTensor_diagonal {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [DecidableEq κ] (d : ι → κ → ℂ) :
    wordTensor (fun i => Matrix.diagonal (d i)) =
      Matrix.diagonal (fun x => ∏ i, d i (x i)) := by
  classical
  ext x y
  by_cases hxy : x=y
  · subst y
    simp [wordTensor]
  · have hn : ∃ i, x i ≠ y i := by
      by_contra h
      push Not at h
      exact hxy (funext h)
    obtain ⟨i,hi⟩ := hn
    have hp : (∏ i, Matrix.diagonal (d i) (x i) (y i)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) (by simp [Matrix.diagonal, hi])
    change (∏ i, Matrix.diagonal (d i) (x i) (y i)) =
      Matrix.diagonal (fun x => ∏ i, d i (x i)) x y
    rw [hp]
    simp [Matrix.diagonal, hxy]

theorem eveTensorChannel_one {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (n : ℕ) :
    eveTensorChannel p n (1 : CMat (QubitWord n)) =
      Matrix.diagonal (fun e : ErrorWord n => ∏ i, 2 * (krausWeight p (e i) : ℂ)) := by
  rw [← wordTensor_one (ι := Fin n) (κ := Qubit), eveTensorChannel_wordTensor]
  simp_rw [eveChannel_one hp0 hp1]
  exact wordTensor_diagonal (fun (_ : Fin n) e => 2 * (krausWeight p e : ℂ))

theorem eveTensorChannel_one_posDef {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1)
    (n : ℕ) : (eveTensorChannel p n (1 : CMat (QubitWord n))).PosDef := by
  rw [eveTensorChannel_one hp0.le hp1]
  apply Matrix.PosDef.diagonal
  intro e
  have heq : (∏ i : Fin n, 2 * (krausWeight p (e i) : ℂ)) =
      ((∏ i : Fin n, 2 * krausWeight p (e i) : ℝ) : ℂ) := by
    norm_cast
  rw [heq]
  apply Complex.zero_lt_real.mpr
  exact Finset.prod_pos (fun i _ => mul_pos (by norm_num)
    (krausWeight_pos hp0 hp1 (e i)))

theorem eveTensorChannel_sub (p : ℝ) (n : ℕ) (ρ σ : CMat (QubitWord n)) :
    eveTensorChannel p n (ρ-σ) =
      eveTensorChannel p n ρ - eveTensorChannel p n σ := by
  ext e f
  simp [eveTensorChannel, Matrix.mul_sub, Matrix.sub_mul, Matrix.trace_sub]

theorem eveTensorChannel_smul (p : ℝ) (n : ℕ) (r : ℂ)
    (ρ : CMat (QubitWord n)) :
    eveTensorChannel p n (r • ρ) = r • eveTensorChannel p n ρ := by
  ext e f
  simp [eveTensorChannel, Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul]

theorem eveTensorChannel_posSemidef (p : ℝ) (n : ℕ)
    {ρ : CMat (QubitWord n)} (hρ : ρ.PosSemidef) :
    (eveTensorChannel p n ρ).PosSemidef := by
  rw [← partialTraceLeft_jointTensor]
  exact partialTraceLeft_posSemidef (jointTensorChannel_posSemidef p n hρ)

theorem eveTensorChannel_posDef_of_input_floor {p μ : ℝ}
    (hp0 : 0 < p) (hp1 : p ≤ 1) (hμ : 0 < μ) (n : ℕ)
    {ρ : CMat (QubitWord n)}
    (hρ : (ρ - (μ : ℂ) • (1 : CMat (QubitWord n))).PosSemidef) :
    (eveTensorChannel p n ρ).PosDef := by
  have hdiff := eveTensorChannel_posSemidef p n hρ
  rw [eveTensorChannel_sub, eveTensorChannel_smul] at hdiff
  have hbase : ((μ : ℂ) • eveTensorChannel p n (1 : CMat (QubitWord n))).PosDef :=
    (eveTensorChannel_one_posDef hp0 hp1 n).smul (Complex.zero_lt_real.mpr hμ)
  have h := hbase.add_posSemidef hdiff
  convert h using 1 <;> abel

theorem pairEveChannel_one {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    pairEveChannel p (1 : CMat PairQubit) =
      Matrix.diagonal (fun e : PairError => 4 *
        ((krausWeight p e.1 * krausWeight p e.2 : ℝ) : ℂ)) := by
  have hpairs (ρ σ : QubitMatrix) : pairEveChannel p (ρ ⊗ₖ σ) =
      eveChannel p ρ ⊗ₖ eveChannel p σ := by
    ext e f
    rcases e with ⟨e₁,e₂⟩
    rcases f with ⟨f₁,f₂⟩
    simp only [pairEveChannel, pairKraus_eq_kronecker,
      Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
      Matrix.trace_kronecker, Matrix.kronecker_apply, eveChannel]
  rw [← Matrix.one_kronecker_one, hpairs, eveChannel_one hp0 hp1,
    Matrix.diagonal_kronecker_diagonal]
  congr 1
  funext e
  push_cast
  ring

theorem real_diagonal_sub_floor_posSemidef {ι : Type*} [DecidableEq ι]
    (d : ι → ℝ) (μ : ℝ) (h : ∀ x, μ ≤ d x) :
    (Matrix.diagonal (fun x => (d x : ℂ)) -
      (μ : ℂ) • (1 : CMat ι)).PosSemidef := by
  have heq : Matrix.diagonal (fun x => (d x : ℂ)) - (μ : ℂ) • (1 : CMat ι) =
      Matrix.diagonal (fun x => ((d x - μ : ℝ) : ℂ)) := by
    ext x y
    by_cases hxy : x=y
    · subst y
      simp [Matrix.diagonal, Matrix.smul_apply, smul_eq_mul]
    · simp [Matrix.diagonal, Matrix.one_apply, Matrix.smul_apply, smul_eq_mul, hxy]
  rw [heq]
  exact Matrix.PosSemidef.diagonal (fun x =>
    Complex.zero_le_real.mpr (sub_nonneg.mpr (h x)))

theorem repeatedTwoUseRho_sub_eighth_power_psd {u v : ℝ} (m : ℕ)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1/4) (hv : |v| ≤ 1/8) :
    (repeatedTwoUseRho u v m -
      (((1/8 : ℝ)^m : ℝ) : ℂ) • (1 : CMat (QubitWord (2*m)))).PosSemidef := by
  rw [repeatedTwoUseRho_eq_diagonal]
  apply real_diagonal_sub_floor_posSemidef
  intro x
  have hprod : (∏ j : Fin m, (1/8 : ℝ)) ≤
      ∏ j : Fin m, correlatedMass u v (x (evenSite m j),x (oddSite m j)) :=
    Finset.prod_le_prod₀ (fun _ _ => by norm_num)
      (fun j _ => correlatedMass_ge_eighth hu0 hu1 hv _)
  simpa using hprod

theorem eveTensorChannel_repeatedTwoUseRho_posDef {p u v : ℝ}
    (hp0 : 0 < p) (hp1 : p ≤ 1) (m : ℕ)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1/4) (hv : |v| ≤ 1/8) :
    (eveTensorChannel p (2*m) (repeatedTwoUseRho u v m)).PosDef := by
  exact eveTensorChannel_posDef_of_input_floor hp0 hp1
    (by positivity : 0 < (1/8 : ℝ)^m) (2*m)
    (repeatedTwoUseRho_sub_eighth_power_psd m hu0 hu1 hv)

theorem bobChannel_one {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    bobChannel p (1 : QubitMatrix) = 1 := by
  rw [bobChannel_eq_depolarizing hp0 hp1]
  ext i j
  by_cases h : i=j <;>
    simp [Matrix.trace, Fin.sum_univ_two, Matrix.one_apply, Matrix.smul_apply,
      smul_eq_mul, h] <;> push_cast <;> ring

theorem bobChannel_pauliZ {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    bobChannel p (pauli 3) = ((1-p : ℝ) : ℂ) • pauli 3 := by
  have hz : Matrix.trace (pauli 3) = 0 := by
    norm_num [pauli, Matrix.trace, Fin.sum_univ_two]
  rw [bobChannel_eq_depolarizing hp0 hp1, hz, mul_zero, zero_smul, add_zero]

theorem pairBobChannel_add (p : ℝ) (ρ σ : CMat PairQubit) :
    pairBobChannel p (ρ+σ) = pairBobChannel p ρ + pairBobChannel p σ := by
  simp [pairBobChannel, Matrix.mul_add, Matrix.add_mul, Finset.sum_add_distrib]

theorem pairBobChannel_kronecker (p : ℝ) (ρ σ : QubitMatrix) :
    pairBobChannel p (ρ ⊗ₖ σ) = bobChannel p ρ ⊗ₖ bobChannel p σ := by
  unfold pairBobChannel bobChannel
  simp_rw [pairKraus_eq_kronecker, Matrix.conjTranspose_kronecker,
    ← Matrix.mul_kronecker_mul]
  ext x y
  rcases x with ⟨x₁,x₂⟩
  rcases y with ⟨y₁,y₂⟩
  simp only [Matrix.sum_apply, Matrix.kronecker_apply, Fintype.sum_prod_type,
    Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_comm

theorem twoUseRho_eq_pauliExpression (u v : ℝ) :
    twoUseRho u v = (1/4 : ℂ) • ((1 : CMat PairQubit) +
      (u : ℂ) • (pauli 3 ⊗ₖ pauli 3) +
      (v : ℂ) • ((pauli 3 ⊗ₖ (1 : QubitMatrix)) +
        ((1 : QubitMatrix) ⊗ₖ pauli 3))) := by
  ext x y
  rcases x with ⟨x₁,x₂⟩
  rcases y with ⟨y₁,y₂⟩
  fin_cases x₁ <;> fin_cases x₂ <;> fin_cases y₁ <;> fin_cases y₂ <;>
    norm_num [twoUseRho, correlatedMass, spinSign, pauli, Matrix.diagonal,
      Matrix.kronecker_apply, Matrix.smul_apply, smul_eq_mul] <;>
    push_cast <;> ring

theorem pairBobChannel_correlated {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (u v : ℝ) :
    pairBobChannel p (twoUseRho u v) = twoUseRho (u*(1-p)^2) (v*(1-p)) := by
  rw [twoUseRho_eq_pauliExpression, twoUseRho_eq_pauliExpression]
  simp only [pairBobChannel_smul, pairBobChannel_add, pairBobChannel_one hp0 hp1,
    pairBobChannel_kronecker, bobChannel_one hp0 hp1, bobChannel_pauliZ hp0 hp1,
    Matrix.smul_kronecker, Matrix.kronecker_smul, smul_smul]
  ext x y
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  push_cast
  ring

theorem pairBobChannel_correlated_commute {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (u v w : ℝ) :
    Commute (pairBobChannel p (twoUseRho u v))
      (pairBobChannel p (twoUseRho u w)) := by
  rw [pairBobChannel_correlated hp0 hp1, pairBobChannel_correlated hp0 hp1]
  exact Matrix.commute_diagonal _ _

theorem wordTensor_commute {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] (A B : ι → CMat κ) (h : ∀ i, Commute (A i) (B i)) :
    Commute (wordTensor A) (wordTensor B) := by
  change wordTensor A * wordTensor B = wordTensor B * wordTensor A
  rw [wordTensor_mul, wordTensor_mul]
  congr 1
  funext i
  exact (h i).eq

theorem commute_submatrix_equiv {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) {A B : CMat κ} (h : Commute A B) :
    Commute (A.submatrix e e) (B.submatrix e e) := by
  change A.submatrix e e * B.submatrix e e = B.submatrix e e * A.submatrix e e
  rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, h.eq]

theorem bobTensorChannel_repeatedTwoUseRho_commute {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (u v w : ℝ) (m : ℕ) :
    Commute (bobTensorChannel p (2*m) (repeatedTwoUseRho u v m))
      (bobTensorChannel p (2*m) (repeatedTwoUseRho u w m)) := by
  rw [bobTensorChannel_repeatedTwoUseRho, bobTensorChannel_repeatedTwoUseRho]
  exact commute_submatrix_equiv (pairedWordEquiv m)
    (wordTensor_commute _ _ (fun _ => pairBobChannel_correlated_commute hp0 hp1 u v w))

theorem eveTensorChannel_add (p : ℝ) (n : ℕ) (ρ σ : CMat (QubitWord n)) :
    eveTensorChannel p n (ρ+σ) =
      eveTensorChannel p n ρ + eveTensorChannel p n σ := by
  ext e f
  simp [eveTensorChannel, Matrix.mul_add, Matrix.add_mul, Matrix.trace_add]

def flipSign (e : PauliIndex) : ℝ := if e=0 ∨ e=1 then 1 else -1

@[simp] theorem flipSign_mul_self (e : PauliIndex) : flipSign e * flipSign e = 1 := by
  unfold flipSign
  split_ifs <;> norm_num

theorem pauli_mul_X (e : PauliIndex) :
    pauli e * pauli 1 = (flipSign e : ℂ) • (pauli 1 * pauli e) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_two]
  fin_cases e <;> fin_cases i <;> fin_cases j <;> norm_num [pauli, flipSign]

theorem kraus_mul_X (p : ℝ) (e : PauliIndex) :
    kraus p e * pauli 1 = (flipSign e : ℂ) • (pauli 1 * kraus p e) := by
  unfold kraus
  rw [Matrix.smul_mul, pauli_mul_X, Matrix.mul_smul]
  simp [smul_smul, mul_comm]

theorem wordTensor_smul {ι κ : Type*} [Fintype ι]
    (r : ι → ℂ) (A : ι → CMat κ) :
    wordTensor (fun i => r i • A i) = (∏ i, r i) • wordTensor A := by
  ext x y
  simp only [wordTensor, Matrix.smul_apply, smul_eq_mul, Finset.prod_mul_distrib]

def physicalXWord (n : ℕ) : CMat (QubitWord n) :=
  wordTensor (fun (_ : Fin n) => pauli 1)

@[simp] theorem physicalXWord_conjTranspose (n : ℕ) :
    (physicalXWord n)ᴴ = physicalXWord n := by
  simp only [physicalXWord, wordTensor_conjTranspose, pauli_conjTranspose]

@[simp] theorem physicalXWord_mul_self (n : ℕ) :
    physicalXWord n * physicalXWord n = (1 : CMat (QubitWord n)) := by
  simp only [physicalXWord, wordTensor_mul, pauli_mul_self, wordTensor_one]

def errorFlipSign (n : ℕ) (e : ErrorWord n) : ℝ := ∏ i, flipSign (e i)

@[simp] theorem errorFlipSign_mul_self (n : ℕ) (e : ErrorWord n) :
    errorFlipSign n e * errorFlipSign n e = 1 := by
  unfold errorFlipSign
  rw [← Finset.prod_mul_distrib]
  simp only [flipSign_mul_self, Finset.prod_const_one]

def errorFlipUnitary (n : ℕ) : CMat (ErrorWord n) :=
  Matrix.diagonal (fun e => (errorFlipSign n e : ℂ))

@[simp] theorem errorFlipUnitary_conjTranspose (n : ℕ) :
    (errorFlipUnitary n)ᴴ = errorFlipUnitary n := by
  ext e f
  by_cases h : e=f
  · subst f
    simp [errorFlipUnitary, Matrix.conjTranspose_apply]
  · simp [errorFlipUnitary, Matrix.conjTranspose_apply, h, Ne.symm h]

@[simp] theorem errorFlipUnitary_mul_self (n : ℕ) :
    errorFlipUnitary n * errorFlipUnitary n = (1 : CMat (ErrorWord n)) := by
  have hs : ∀ e : ErrorWord n,
      (errorFlipSign n e : ℂ) * (errorFlipSign n e : ℂ) = 1 := by
    intro e
    exact_mod_cast errorFlipSign_mul_self n e
  simp only [errorFlipUnitary, Matrix.diagonal_mul_diagonal, hs, Matrix.diagonal_one]

theorem tensorKraus_conjTranspose (p : ℝ) (n : ℕ) (e : ErrorWord n) :
    (tensorKraus p n e)ᴴ = tensorKraus p n e := by
  simp only [tensorKraus_eq_wordTensor, wordTensor_conjTranspose, kraus_conjTranspose]

theorem tensorKraus_mul_XWord (p : ℝ) (n : ℕ) (e : ErrorWord n) :
    tensorKraus p n e * physicalXWord n =
      (errorFlipSign n e : ℂ) • (physicalXWord n * tensorKraus p n e) := by
  simp only [tensorKraus_eq_wordTensor, physicalXWord, wordTensor_mul, kraus_mul_X,
    wordTensor_smul]
  congr 1
  unfold errorFlipSign
  norm_cast

theorem XWord_mul_tensorKraus_adjoint (p : ℝ) (n : ℕ) (e : ErrorWord n) :
    physicalXWord n * (tensorKraus p n e)ᴴ =
      (errorFlipSign n e : ℂ) • ((tensorKraus p n e)ᴴ * physicalXWord n) := by
  have h := congr_arg Matrix.conjTranspose (tensorKraus_mul_XWord p n e)
  simpa [Matrix.conjTranspose_mul, Matrix.conjTranspose_smul,
    tensorKraus_conjTranspose, physicalXWord_conjTranspose] using h

theorem eveTensorChannel_XWord_covariance (p : ℝ) (n : ℕ)
    (ρ : CMat (QubitWord n)) :
    eveTensorChannel p n (physicalXWord n * ρ * (physicalXWord n)ᴴ) =
      errorFlipUnitary n * eveTensorChannel p n ρ * (errorFlipUnitary n)ᴴ := by
  rw [errorFlipUnitary_conjTranspose, physicalXWord_conjTranspose]
  ext e f
  have hm : tensorKraus p n e * (physicalXWord n * ρ * physicalXWord n) *
      (tensorKraus p n f)ᴴ =
      ((errorFlipSign n e : ℂ) * (errorFlipSign n f : ℂ)) •
        (physicalXWord n * (tensorKraus p n e * ρ * (tensorKraus p n f)ᴴ) *
          physicalXWord n) := by
    calc
      _ = (tensorKraus p n e * physicalXWord n) * ρ *
          (physicalXWord n * (tensorKraus p n f)ᴴ) := by
        simp only [Matrix.mul_assoc]
      _ = ((errorFlipSign n e : ℂ) • (physicalXWord n * tensorKraus p n e)) * ρ *
          ((errorFlipSign n f : ℂ) • ((tensorKraus p n f)ᴴ * physicalXWord n)) := by
        rw [tensorKraus_mul_XWord, XWord_mul_tensorKraus_adjoint]
      _ = _ := by
        simp [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc,
          ← Complex.ofReal_mul, mul_comm]
  have ht : Matrix.trace (physicalXWord n *
      (tensorKraus p n e * ρ * (tensorKraus p n f)ᴴ) * physicalXWord n) =
      Matrix.trace (tensorKraus p n e * ρ * (tensorKraus p n f)ᴴ) := by
    rw [Matrix.trace_mul_cycle, physicalXWord_mul_self, Matrix.one_mul]
  change Matrix.trace (tensorKraus p n e *
      (physicalXWord n * ρ * physicalXWord n) * (tensorKraus p n f)ᴴ) =
    (errorFlipUnitary n * eveTensorChannel p n ρ * errorFlipUnitary n) e f
  rw [hm, Matrix.trace_smul, ht]
  simp only [errorFlipUnitary, Matrix.mul_diagonal, Matrix.diagonal_mul,
    eveTensorChannel, smul_eq_mul]
  ring

def pairX : CMat PairQubit := pauli 1 ⊗ₖ pauli 1

@[simp] theorem pairX_conjTranspose : pairXᴴ = pairX := by
  simp only [pairX, Matrix.conjTranspose_kronecker, pauli_conjTranspose]

@[simp] theorem pairX_mul_self : pairX * pairX = (1 : CMat PairQubit) := by
  simp only [pairX, ← Matrix.mul_kronecker_mul, pauli_mul_self,
    Matrix.one_kronecker_one]

theorem physicalXWord_eq_pairedTensor (m : ℕ) :
    physicalXWord (2*m) =
      (wordTensor (fun (_ : Fin m) => pairX)).submatrix
        (pairedWordEquiv m) (pairedWordEquiv m) := by
  ext x y
  change (∏ i, pauli 1 (x i) (y i)) =
    ∏ j, pairX (pairedWordEquiv m x j) (pairedWordEquiv m y j)
  calc
    _ = ∏ jb : Fin m × Fin 2, pauli 1
        (x (evenOddEquiv m jb)) (y (evenOddEquiv m jb)) :=
      ((evenOddEquiv m).prod_comp (fun i => pauli 1 (x i) (y i))).symm
    _ = _ := by
      rw [Fintype.prod_prod_type]
      apply Finset.prod_congr rfl
      intro j _
      simp [Fin.prod_univ_two, pairX, evenOddEquiv, evenSite, oddSite,
        Matrix.kronecker_apply]

theorem pairX_twoUseRho_flip (u v : ℝ) :
    pairX * twoUseRho u v * pairXᴴ = twoUseRho u (-v) := by
  rw [pairX_conjTranspose]
  ext x y
  rcases x with ⟨x₁,x₂⟩
  rcases y with ⟨y₁,y₂⟩
  simp only [Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two]
  fin_cases x₁ <;> fin_cases x₂ <;> fin_cases y₁ <;> fin_cases y₂ <;>
    norm_num [pairX, pauli, Matrix.kronecker_apply, twoUseRho,
      Matrix.diagonal, correlatedMass, spinSign] <;> push_cast <;> ring

theorem physicalXWord_repeatedTwoUseRho_flip (u v : ℝ) (m : ℕ) :
    physicalXWord (2*m) * repeatedTwoUseRho u v m * (physicalXWord (2*m))ᴴ =
      repeatedTwoUseRho u (-v) m := by
  simp only [physicalXWord_eq_pairedTensor, repeatedTwoUseRho_eq_pairedTensor,
    Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv,
    wordTensor_conjTranspose, wordTensor_mul, pairX_twoUseRho_flip]

theorem eveTensorChannel_repeated_sign_involution (p u v : ℝ) (m : ℕ) :
    eveTensorChannel p (2*m) (repeatedTwoUseRho u (-v) m) =
      errorFlipUnitary (2*m) *
        eveTensorChannel p (2*m) (repeatedTwoUseRho u v m) *
          (errorFlipUnitary (2*m))ᴴ := by
  rw [← physicalXWord_repeatedTwoUseRho_flip u v m]
  exact eveTensorChannel_XWord_covariance p (2*m) (repeatedTwoUseRho u v m)

def eveIMatrix (p : ℝ) : EnvironmentMatrix :=
  Matrix.diagonal (fun e => 2 * (krausWeight p e : ℂ))

theorem eveChannel_eq_IMatrix {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    eveChannel p (1 : QubitMatrix) = eveIMatrix p :=
  eveChannel_one hp0 hp1

def pauliZTracePhase : EnvironmentMatrix :=
  !![0,0,0,2; 0,0,-2*Complex.I,0; 0,2*Complex.I,0,0; 2,0,0,0]

theorem pauli_trace_Z (e f : PauliIndex) :
    Matrix.trace (pauli e * pauli 3 * pauli f) = pauliZTracePhase e f := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_two]
  fin_cases e <;> fin_cases f <;>
    norm_num [pauli, pauliZTracePhase, Complex.I_mul_I] <;> ring

theorem kraus_trace_Z (p : ℝ) (e f : PauliIndex) :
    Matrix.trace (kraus p e * pauli 3 * (kraus p f)ᴴ) =
      ((Real.sqrt (krausWeight p e) * Real.sqrt (krausWeight p f) : ℝ) : ℂ) *
        pauliZTracePhase e f := by
  rw [kraus_conjTranspose]
  simp [kraus, Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul,
    smul_smul, smul_eq_mul, ← Complex.ofReal_mul, pauli_trace_Z, mul_comm]

def eveZMatrix (p : ℝ) : EnvironmentMatrix :=
  let q : ℂ := (Real.sqrt (1-3*p/4) : ℝ)
  let r : ℂ := (Real.sqrt (p/4) : ℝ)
  !![0,0,0,2*q*r;
     0,0,-2*Complex.I*r*r,0;
     0,2*Complex.I*r*r,0,0;
     2*q*r,0,0,0]

theorem eveChannel_eq_ZMatrix (p : ℝ) :
    eveChannel p (pauli 3) = eveZMatrix p := by
  ext e f
  change Matrix.trace (kraus p e * pauli 3 * (kraus p f)ᴴ) = eveZMatrix p e f
  rw [kraus_trace_Z]
  fin_cases e <;> fin_cases f <;>
    norm_num [eveZMatrix, pauliZTracePhase, krausWeight] <;>
    push_cast <;> ring

theorem eveZMatrix_eq_physical {p : ℝ} (hp0 : 0 ≤ p) :
    eveZMatrix p =
      !![0,0,0,2*((Real.sqrt (1-3*p/4)*Real.sqrt (p/4) : ℝ) : ℂ);
         0,0,-2*Complex.I*((p/4 : ℝ) : ℂ),0;
         0,2*Complex.I*((p/4 : ℝ) : ℂ),0,0;
         2*((Real.sqrt (1-3*p/4)*Real.sqrt (p/4) : ℝ) : ℂ),0,0,0] := by
  have hs : (Real.sqrt p : ℂ)^2 = (p : ℂ) := by
    rw [pow_two]
    exact_mod_cast Real.mul_self_sqrt hp0
  ext e f
  fin_cases e <;> fin_cases f <;>
    norm_num [eveZMatrix] <;> push_cast <;>
    ring_nf <;> simp only [hs] <;> ring

theorem pairEveChannel_add (p : ℝ) (ρ σ : CMat PairQubit) :
    pairEveChannel p (ρ+σ) = pairEveChannel p ρ + pairEveChannel p σ := by
  ext e f
  simp [pairEveChannel, Matrix.mul_add, Matrix.add_mul, Matrix.trace_add]

theorem pairEveChannel_kronecker (p : ℝ) (ρ σ : QubitMatrix) :
    pairEveChannel p (ρ ⊗ₖ σ) = eveChannel p ρ ⊗ₖ eveChannel p σ := by
  ext e f
  rcases e with ⟨e₁,e₂⟩
  rcases f with ⟨f₁,f₂⟩
  simp only [pairEveChannel, pairKraus_eq_kronecker,
    Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
    Matrix.trace_kronecker, Matrix.kronecker_apply, eveChannel]

theorem pairEveChannel_correlated {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (u v : ℝ) :
    pairEveChannel p (twoUseRho u v) =
      (1/4 : ℂ) • ((eveIMatrix p ⊗ₖ eveIMatrix p) +
        (u : ℂ) • (eveZMatrix p ⊗ₖ eveZMatrix p) +
        (v : ℂ) • ((eveZMatrix p ⊗ₖ eveIMatrix p) +
          (eveIMatrix p ⊗ₖ eveZMatrix p))) := by
  rw [twoUseRho_eq_pauliExpression]
  simp only [pairEveChannel_smul, pairEveChannel_add]
  rw [← Matrix.one_kronecker_one]
  simp only [pairEveChannel_kronecker, eveChannel_eq_IMatrix hp0 hp1,
    eveChannel_eq_ZMatrix]

def eveYPhase (e : PauliIndex) : ℂ := if e=2 then Complex.I else 1

def eveYGauge : EnvironmentMatrix := Matrix.diagonal eveYPhase

theorem eveYGauge_unitary :
    eveYGaugeᴴ * eveYGauge = 1 ∧ eveYGauge * eveYGaugeᴴ = 1 := by
  have hleft : ∀ e : PauliIndex, star (eveYPhase e) * eveYPhase e = 1 := by
    intro e
    by_cases he : e=2 <;> simp [eveYPhase, he, Complex.I_mul_I]
  have hright : ∀ e : PauliIndex, eveYPhase e * star (eveYPhase e) = 1 := by
    intro e
    rw [mul_comm]
    exact hleft e
  constructor <;>
    simp only [eveYGauge, Matrix.diagonal_conjTranspose,
      Matrix.diagonal_mul_diagonal, Pi.star_apply, hleft, hright,
      Matrix.diagonal_one]

theorem eveYGauge_conjugate_apply (A : EnvironmentMatrix) (e f : PauliIndex) :
    (eveYGaugeᴴ * A * eveYGauge) e f =
      star (eveYPhase e) * A e f * eveYPhase f := by
  simp only [eveYGauge, Matrix.diagonal_conjTranspose,
    Matrix.mul_diagonal, Matrix.diagonal_mul, Pi.star_apply]

def pauliSectorEquiv : (Qubit × Qubit) ≃ PauliIndex :=
  ((Equiv.prodComm Qubit Qubit).trans
    (finProdFinEquiv : (Fin 2 × Fin 2) ≃ Fin (2*2))).trans sourceToCanonical

theorem pauliSectorEquiv_apply (x s : Qubit) :
    pauliSectorEquiv (x,s) =
      if s=0 then (if x=0 then 0 else 3) else (if x=0 then 1 else 2) := by
  fin_cases x <;> fin_cases s <;> rfl

def eveD (p : ℝ) (s : Qubit) : QubitMatrix :=
  if s=0 then Matrix.diagonal ![(aScalar p : ℂ), (bScalar p : ℂ)]
  else (bScalar p : ℂ) • (1 : QubitMatrix)

def eveS (p : ℝ) (s : Qubit) : QubitMatrix :=
  (if s=0 then ((Real.sqrt (aScalar p)*Real.sqrt (bScalar p) : ℝ) : ℂ)
    else (bScalar p : ℂ)) • pauli 1

theorem eveYGauge_I_blocks (p : ℝ) :
    (eveYGaugeᴴ * eveIMatrix p * eveYGauge).submatrix
      pauliSectorEquiv pauliSectorEquiv =
        (2 : ℂ) • Matrix.blockDiagonal (eveD p) := by
  have hI : Complex.I^2 = (-1 : ℂ) := by rw [pow_two, Complex.I_mul_I]
  ext x y
  rcases x with ⟨x,s⟩
  rcases y with ⟨y,t⟩
  simp only [Matrix.submatrix_apply, eveYGauge_conjugate_apply,
    pauliSectorEquiv_apply, Matrix.smul_apply, smul_eq_mul]
  fin_cases x <;> fin_cases s <;> fin_cases y <;> fin_cases t <;>
    norm_num [eveIMatrix, eveYPhase, krausWeight, eveD, aScalar, bScalar,
      Matrix.blockDiagonal_apply, Matrix.diagonal, Matrix.one_apply,
      Matrix.smul_apply, smul_eq_mul, Complex.I_mul_I] <;>
    push_cast <;> ring_nf <;> simp only [hI] <;> ring

theorem eveYGauge_Z_blocks {p : ℝ} (hp0 : 0 ≤ p) :
    (eveYGaugeᴴ * eveZMatrix p * eveYGauge).submatrix
      pauliSectorEquiv pauliSectorEquiv =
        (2 : ℂ) • Matrix.blockDiagonal (eveS p) := by
  have hI : Complex.I^2 = (-1 : ℂ) := by rw [pow_two, Complex.I_mul_I]
  ext x y
  rcases x with ⟨x,s⟩
  rcases y with ⟨y,t⟩
  simp only [Matrix.submatrix_apply, eveYGauge_conjugate_apply,
    pauliSectorEquiv_apply, Matrix.smul_apply, smul_eq_mul]
  rw [eveZMatrix_eq_physical hp0]
  fin_cases x <;> fin_cases s <;> fin_cases y <;> fin_cases t <;>
    norm_num [eveYPhase, eveS, aScalar, bScalar, pauli,
      Matrix.blockDiagonal_apply, Matrix.smul_apply, smul_eq_mul,
      Complex.I_mul_I] <;> push_cast <;> ring_nf <;> simp only [hI] <;> ring

def pairYGauge : CMat PairError := eveYGauge ⊗ₖ eveYGauge

theorem pairYGauge_unitary :
    pairYGaugeᴴ * pairYGauge = 1 ∧ pairYGauge * pairYGaugeᴴ = 1 := by
  constructor
  · simp only [pairYGauge, Matrix.conjTranspose_kronecker,
      ← Matrix.mul_kronecker_mul, eveYGauge_unitary.1,
      Matrix.one_kronecker_one]
  · simp only [pairYGauge, Matrix.conjTranspose_kronecker,
      ← Matrix.mul_kronecker_mul, eveYGauge_unitary.2,
      Matrix.one_kronecker_one]

def pairSectorShuffle : (PairQubit × PairQubit) ≃
    ((Qubit × Qubit) × (Qubit × Qubit)) :=
  Equiv.prodProdProdComm Qubit Qubit Qubit Qubit

def pairEveSectorEquiv : (PairQubit × PairQubit) ≃ PairError :=
  pairSectorShuffle.trans (pauliSectorEquiv.prodCongr pauliSectorEquiv)

theorem kronecker_sector_reindex (A B : EnvironmentMatrix) :
    (A ⊗ₖ B).submatrix pairEveSectorEquiv pairEveSectorEquiv =
      ((A.submatrix pauliSectorEquiv pauliSectorEquiv) ⊗ₖ
        (B.submatrix pauliSectorEquiv pauliSectorEquiv)).submatrix
          pairSectorShuffle pairSectorShuffle := by
  ext x y
  rfl

theorem blockDiagonal_kronecker_shuffle (A B : Qubit → QubitMatrix) :
    ((Matrix.blockDiagonal A) ⊗ₖ (Matrix.blockDiagonal B)).submatrix
      pairSectorShuffle pairSectorShuffle =
        Matrix.blockDiagonal (fun s : PairQubit => A s.1 ⊗ₖ B s.2) := by
  ext x y
  rcases x with ⟨⟨x₁,x₂⟩,⟨s₁,s₂⟩⟩
  rcases y with ⟨⟨y₁,y₂⟩,⟨t₁,t₂⟩⟩
  by_cases h₁ : s₁=t₁ <;> by_cases h₂ : s₂=t₂ <;>
    simp [Matrix.submatrix_apply, pairSectorShuffle,
      Equiv.prodProdProdComm, Matrix.kronecker_apply,
      Matrix.blockDiagonal_apply, h₁, h₂]

def gaugePairEveMatrix (A : CMat PairError) : CMat (PairQubit × PairQubit) :=
  (pairYGaugeᴴ * A * pairYGauge).submatrix pairEveSectorEquiv pairEveSectorEquiv

theorem gaugePairEveMatrix_add (A B : CMat PairError) :
    gaugePairEveMatrix (A+B) = gaugePairEveMatrix A + gaugePairEveMatrix B := by
  simp [gaugePairEveMatrix, Matrix.mul_add, Matrix.add_mul,
    Matrix.submatrix_add, Pi.add_apply]

theorem gaugePairEveMatrix_smul (r : ℂ) (A : CMat PairError) :
    gaugePairEveMatrix (r • A) = r • gaugePairEveMatrix A := by
  simp [gaugePairEveMatrix, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.submatrix_smul, Pi.smul_apply]

theorem gaugePairEveMatrix_kronecker (A B : EnvironmentMatrix) :
    gaugePairEveMatrix (A ⊗ₖ B) =
      (((eveYGaugeᴴ * A * eveYGauge).submatrix pauliSectorEquiv pauliSectorEquiv) ⊗ₖ
        ((eveYGaugeᴴ * B * eveYGauge).submatrix pauliSectorEquiv pauliSectorEquiv)).submatrix
          pairSectorShuffle pairSectorShuffle := by
  unfold gaugePairEveMatrix
  simp only [pairYGauge, Matrix.conjTranspose_kronecker,
    ← Matrix.mul_kronecker_mul]
  exact kronecker_sector_reindex _ _

def pairEveBlock (p u v : ℝ) (s : PairQubit) : CMat PairQubit :=
  (eveD p s.1 ⊗ₖ eveD p s.2) +
    (u : ℂ) • (eveS p s.1 ⊗ₖ eveS p s.2) +
    (v : ℂ) • ((eveS p s.1 ⊗ₖ eveD p s.2) +
      (eveD p s.1 ⊗ₖ eveS p s.2))

theorem pairEveChannel_correlated_blocks {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (u v : ℝ) :
    gaugePairEveMatrix (pairEveChannel p (twoUseRho u v)) =
      Matrix.blockDiagonal (pairEveBlock p u v) := by
  rw [pairEveChannel_correlated hp0 hp1]
  simp only [gaugePairEveMatrix_smul, gaugePairEveMatrix_add,
    gaugePairEveMatrix_kronecker, eveYGauge_I_blocks, eveYGauge_Z_blocks hp0,
    Matrix.smul_kronecker, Matrix.kronecker_smul, Matrix.submatrix_smul, Pi.smul_apply,
    smul_smul, blockDiagonal_kronecker_shuffle]
  ext x y
  simp only [Matrix.smul_apply, Matrix.add_apply, smul_eq_mul,
    Matrix.blockDiagonal_apply, pairEveBlock, Matrix.kronecker_apply]
  by_cases h : x.2=y.2 <;> simp only [h, ite_true, ite_false] <;> ring

def pairErrorFlipSign (e : PairError) : ℝ := flipSign e.1 * flipSign e.2

@[simp] theorem pairErrorFlipSign_mul_self (e : PairError) :
    pairErrorFlipSign e * pairErrorFlipSign e = 1 := by
  unfold pairErrorFlipSign
  rw [mul_mul_mul_comm, flipSign_mul_self, flipSign_mul_self]
  norm_num

def pairErrorFlipUnitary : CMat PairError :=
  Matrix.diagonal (fun e => (pairErrorFlipSign e : ℂ))

@[simp] theorem pairErrorFlipUnitary_conjTranspose :
    pairErrorFlipUnitaryᴴ = pairErrorFlipUnitary := by
  ext e f
  by_cases h : e=f
  · subst f
    simp [pairErrorFlipUnitary, Matrix.conjTranspose_apply]
  · simp [pairErrorFlipUnitary, Matrix.conjTranspose_apply, h, Ne.symm h]

@[simp] theorem pairErrorFlipUnitary_mul_self :
    pairErrorFlipUnitary * pairErrorFlipUnitary = (1 : CMat PairError) := by
  have hs : ∀ e : PairError,
      (pairErrorFlipSign e : ℂ) * (pairErrorFlipSign e : ℂ) = 1 := by
    intro e
    exact_mod_cast pairErrorFlipSign_mul_self e
  simp only [pairErrorFlipUnitary, Matrix.diagonal_mul_diagonal, hs,
    Matrix.diagonal_one]

theorem pairErrorFlipUnitary_unitary :
    pairErrorFlipUnitaryᴴ * pairErrorFlipUnitary = 1 ∧
      pairErrorFlipUnitary * pairErrorFlipUnitaryᴴ = 1 := by
  simp only [pairErrorFlipUnitary_conjTranspose, pairErrorFlipUnitary_mul_self,
    and_self]

theorem pairKraus_mul_pairX (p : ℝ) (e : PairError) :
    pairKraus p e * pairX =
      (pairErrorFlipSign e : ℂ) • (pairX * pairKraus p e) := by
  simp only [pairKraus_eq_kronecker, pairX, ← Matrix.mul_kronecker_mul,
    kraus_mul_X, Matrix.smul_kronecker, Matrix.kronecker_smul,
    smul_smul, ← Complex.ofReal_mul, pairErrorFlipSign, mul_comm]

theorem pairX_mul_pairKraus_adjoint (p : ℝ) (e : PairError) :
    pairX * (pairKraus p e)ᴴ =
      (pairErrorFlipSign e : ℂ) • ((pairKraus p e)ᴴ * pairX) := by
  have h := congr_arg Matrix.conjTranspose (pairKraus_mul_pairX p e)
  simpa [Matrix.conjTranspose_mul, Matrix.conjTranspose_smul,
    pairKraus_conjTranspose, pairX_conjTranspose] using h

theorem pairEveChannel_pairX_covariance (p : ℝ) (ρ : CMat PairQubit) :
    pairEveChannel p (pairX * ρ * pairXᴴ) =
      pairErrorFlipUnitary * pairEveChannel p ρ * pairErrorFlipUnitaryᴴ := by
  rw [pairErrorFlipUnitary_conjTranspose, pairX_conjTranspose]
  ext e f
  have hm : pairKraus p e * (pairX * ρ * pairX) * (pairKraus p f)ᴴ =
      ((pairErrorFlipSign e * pairErrorFlipSign f : ℝ) : ℂ) •
        (pairX * (pairKraus p e * ρ * (pairKraus p f)ᴴ) * pairX) := by
    calc
      _ = (pairKraus p e * pairX) * ρ *
          (pairX * (pairKraus p f)ᴴ) := by simp only [Matrix.mul_assoc]
      _ = ((pairErrorFlipSign e : ℂ) • (pairX * pairKraus p e)) * ρ *
          ((pairErrorFlipSign f : ℂ) • ((pairKraus p f)ᴴ * pairX)) := by
        rw [pairKraus_mul_pairX, pairX_mul_pairKraus_adjoint]
      _ = _ := by
        simp [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc,
          ← Complex.ofReal_mul, mul_comm]
  have ht : Matrix.trace (pairX *
      (pairKraus p e * ρ * (pairKraus p f)ᴴ) * pairX) =
      Matrix.trace (pairKraus p e * ρ * (pairKraus p f)ᴴ) := by
    rw [Matrix.trace_mul_cycle, pairX_mul_self, Matrix.one_mul]
  change Matrix.trace (pairKraus p e * (pairX * ρ * pairX) * (pairKraus p f)ᴴ) =
    (pairErrorFlipUnitary * pairEveChannel p ρ * pairErrorFlipUnitary) e f
  rw [hm, Matrix.trace_smul, ht]
  simp only [pairErrorFlipUnitary, Matrix.mul_diagonal, Matrix.diagonal_mul,
    pairEveChannel, smul_eq_mul]
  push_cast
  ring

theorem pairEveChannel_correlated_sign_involution (p u v : ℝ) :
    pairEveChannel p (twoUseRho u (-v)) =
      pairErrorFlipUnitary * pairEveChannel p (twoUseRho u v) *
        pairErrorFlipUnitaryᴴ := by
  rw [← pairX_twoUseRho_flip u v]
  exact pairEveChannel_pairX_covariance p (twoUseRho u v)

theorem pairEveChannel_one_posDef {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) :
    (pairEveChannel p (1 : CMat PairQubit)).PosDef := by
  rw [pairEveChannel_one hp0.le hp1]
  apply Matrix.PosDef.diagonal
  intro e
  have heq : (4 : ℂ) * ((krausWeight p e.1 * krausWeight p e.2 : ℝ) : ℂ) =
      ((4 * (krausWeight p e.1 * krausWeight p e.2) : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [heq]
  exact Complex.zero_lt_real.mpr (mul_pos (by norm_num)
    (mul_pos (krausWeight_pos hp0 hp1 e.1) (krausWeight_pos hp0 hp1 e.2)))

theorem pairEveChannel_posDef_of_input_floor {p μ : ℝ}
    (hp0 : 0 < p) (hp1 : p ≤ 1) (hμ : 0 < μ) {ρ : CMat PairQubit}
    (hρ : (ρ - (μ : ℂ) • (1 : CMat PairQubit)).PosSemidef) :
    (pairEveChannel p ρ).PosDef := by
  have hdiff := pairEveChannel_posSemidef p hρ
  rw [pairEveChannel_sub, pairEveChannel_smul] at hdiff
  have hbase : ((μ : ℂ) • pairEveChannel p (1 : CMat PairQubit)).PosDef :=
    (pairEveChannel_one_posDef hp0 hp1).smul (Complex.zero_lt_real.mpr hμ)
  have h := hbase.add_posSemidef hdiff
  convert h using 1 <;> abel

theorem pairEveChannel_correlated_posDef {p u v : ℝ}
    (hp0 : 0 < p) (hp1 : p ≤ 1) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1/4) (hv : |v| ≤ 1/8) :
    (pairEveChannel p (twoUseRho u v)).PosDef := by
  exact pairEveChannel_posDef_of_input_floor hp0 hp1
    (by norm_num : 0 < (1/8 : ℝ)) (by
      convert twoUseRho_sub_eighth_psd hu0 hu1 hv using 1 <;> norm_num)

theorem gaugePairEveMatrix_posDef {A : CMat PairError} (hA : A.PosDef) :
    (gaugePairEveMatrix A).PosDef := by
  have hinj : Function.Injective pairYGauge.mulVec := by
    intro x y hxy
    have h := congr_arg (fun v => pairYGaugeᴴ *ᵥ v) hxy
    simpa only [Matrix.mulVec_mulVec, pairYGauge_unitary.1,
      Matrix.one_mulVec] using h
  exact (hA.conjTranspose_mul_mul_same hinj).submatrix pairEveSectorEquiv.injective

theorem pairEveBlock_posDef {p u v : ℝ}
    (hp0 : 0 < p) (hp1 : p ≤ 1) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1/4) (hv : |v| ≤ 1/8) (s : PairQubit) :
    (pairEveBlock p u v s).PosDef := by
  have h := gaugePairEveMatrix_posDef
    (pairEveChannel_correlated_posDef hp0 hp1 hu0 hu1 hv)
  rw [pairEveChannel_correlated_blocks hp0.le hp1] at h
  have hs : (Matrix.blockDiagonal (pairEveBlock p u v)).submatrix
      (fun x : PairQubit => (x,s)) (fun x : PairQubit => (x,s)) =
        pairEveBlock p u v s := by
    ext x y
    simp only [Matrix.submatrix_apply, Matrix.blockDiagonal_apply_eq]
  rw [← hs]
  exact h.submatrix (fun _ _ hxy => congr_arg Prod.fst hxy)

def eveSectorMass (p : ℝ) (s : Qubit) : ℝ :=
  if s=0 then sScalar p else 2*bScalar p

theorem eveD_trace (p : ℝ) (s : Qubit) :
    Matrix.trace (eveD p s) = (eveSectorMass p s : ℂ) := by
  fin_cases s <;>
    norm_num [eveD, eveSectorMass, sScalar, Matrix.trace, Matrix.diag,
      Matrix.diagonal, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_two] <;>
    push_cast <;> ring

theorem eveS_trace (p : ℝ) (s : Qubit) : Matrix.trace (eveS p s) = 0 := by
  have hX : Matrix.trace (pauli 1) = 0 := by
    norm_num [pauli, Matrix.trace, Matrix.diag, Fin.sum_univ_two]
  unfold eveS
  split_ifs <;> simp [Matrix.trace_smul, hX]

theorem pairEveBlock_trace (p u v : ℝ) (s : PairQubit) :
    Matrix.trace (pairEveBlock p u v s) =
      ((eveSectorMass p s.1 * eveSectorMass p s.2 : ℝ) : ℂ) := by
  simp only [pairEveBlock, Matrix.trace_add, Matrix.trace_smul,
    Matrix.trace_kronecker, eveD_trace, eveS_trace, mul_zero, zero_mul,
    smul_zero, add_zero, ← Complex.ofReal_mul]

theorem eveSectorMass_pos {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) (s : Qubit) :
    0 < eveSectorMass p s := by
  fin_cases s <;> norm_num [eveSectorMass, sScalar, aScalar, bScalar] <;> nlinarith

theorem eveSectorMass_sum (p : ℝ) : ∑ s : Qubit, eveSectorMass p s = 1 := by
  simp [Fin.sum_univ_two, eveSectorMass, sScalar, aScalar, bScalar]
  ring

def pairEveSectorMass (p : ℝ) (s : PairQubit) : ℝ :=
  eveSectorMass p s.1 * eveSectorMass p s.2

theorem pairEveSectorMass_pos {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1)
    (s : PairQubit) : 0 < pairEveSectorMass p s :=
  mul_pos (eveSectorMass_pos hp0 hp1 s.1) (eveSectorMass_pos hp0 hp1 s.2)

theorem pairEveSectorMass_sum (p : ℝ) :
    ∑ s : PairQubit, pairEveSectorMass p s = 1 := by
  unfold pairEveSectorMass
  rw [Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum, eveSectorMass_sum, mul_one]
  exact eveSectorMass_sum p

set_option backward.isDefEq.respectTransparency false in

def normalizedPairEveBlock {p u v : ℝ}
    (hp0 : 0 < p) (hp1 : p ≤ 1) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1/4) (hv : |v| ≤ 1/8) (s : PairQubit) : Density PairQubit where
  mat := ((pairEveSectorMass p s)⁻¹ : ℝ) • pairEveBlock p u v s
  psd := (pairEveBlock_posDef hp0 hp1 hu0 hu1 hv s).posSemidef.smul
    (inv_nonneg.mpr (pairEveSectorMass_pos hp0 hp1 s).le)
  trace_one := by
    rw [Matrix.trace_smul, pairEveBlock_trace]
    change ((pairEveSectorMass p s)⁻¹ : ℝ) • (pairEveSectorMass p s : ℂ) = 1
    rw [RCLike.real_smul_eq_coe_mul]
    change (Complex.ofReal ((pairEveSectorMass p s)⁻¹)) *
      Complex.ofReal (pairEveSectorMass p s) = 1
    rw [← Complex.ofReal_mul, inv_mul_cancel₀ (pairEveSectorMass_pos hp0 hp1 s).ne']
    rfl

theorem pairEveBlock_weighted_density {p u v : ℝ}
    (hp0 : 0 < p) (hp1 : p ≤ 1) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1/4) (hv : |v| ≤ 1/8) (s : PairQubit) :
    (pairEveSectorMass p s : ℝ) •
      (normalizedPairEveBlock hp0 hp1 hu0 hu1 hv s).mat = pairEveBlock p u v s := by
  change (pairEveSectorMass p s : ℝ) •
    (((pairEveSectorMass p s)⁻¹ : ℝ) • pairEveBlock p u v s) = _
  rw [smul_smul, mul_inv_cancel₀ (pairEveSectorMass_pos hp0 hp1 s).ne', one_smul]

theorem matrixBlockDiagonal_posSemidef {α κ : Type*}
    [Fintype α] [DecidableEq α] [Fintype κ] [DecidableEq κ]
    (A : α → CMat κ) (hA : ∀ s, (A s).PosSemidef) :
    (Matrix.blockDiagonal A).PosSemidef := by
  let B : α → CMat κ := fun s => CFC.sqrt (A s)
  have hB : ∀ s, (B s)ᴴ = B s :=
    fun s => (CFC.sqrt_nonneg (A s)).posSemidef.1
  have hgram : (Matrix.blockDiagonal B)ᴴ * Matrix.blockDiagonal B =
      Matrix.blockDiagonal A := by
    rw [Matrix.blockDiagonal_conjTranspose, ← Matrix.blockDiagonal_mul]
    congr 1
    funext s
    rw [hB s]
    exact CFC.sqrt_mul_sqrt_self (A s) (hA s).nonneg
  rw [← hgram]
  exact Matrix.posSemidef_conjTranspose_mul_self (Matrix.blockDiagonal B)

theorem matrixBlockDiagonal_sqrt {α κ : Type*}
    [Fintype α] [DecidableEq α] [Fintype κ] [DecidableEq κ]
    (A : α → CMat κ) (hA : ∀ s, (A s).PosSemidef) :
    CFC.sqrt (Matrix.blockDiagonal A) =
      Matrix.blockDiagonal (fun s => CFC.sqrt (A s)) := by
  have hsq : Matrix.blockDiagonal (fun s => CFC.sqrt (A s)) *
      Matrix.blockDiagonal (fun s => CFC.sqrt (A s)) = Matrix.blockDiagonal A := by
    rw [← Matrix.blockDiagonal_mul]
    congr 1
    funext s
    exact CFC.sqrt_mul_sqrt_self (A s) (hA s).nonneg
  exact CFC.sqrt_unique hsq
    (matrixBlockDiagonal_posSemidef (fun s => CFC.sqrt (A s))
      (fun s => (CFC.sqrt_nonneg (A s)).posSemidef)).nonneg

theorem trace_matrixBlockDiagonal_sqrt_product {α κ : Type*}
    [Fintype α] [DecidableEq α] [Fintype κ] [DecidableEq κ]
    (A B : α → CMat κ) (hA : ∀ s, (A s).PosSemidef)
    (hB : ∀ s, (B s).PosSemidef) :
    Matrix.trace (CFC.sqrt (Matrix.blockDiagonal A) *
      CFC.sqrt (Matrix.blockDiagonal B)) =
        ∑ s, Matrix.trace (CFC.sqrt (A s) * CFC.sqrt (B s)) := by
  rw [matrixBlockDiagonal_sqrt A hA, matrixBlockDiagonal_sqrt B hB,
    ← Matrix.blockDiagonal_mul, Matrix.trace_blockDiagonal]

theorem matrix_sqrt_unitary_conjugate {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : CMat ι) (hU : Uᴴ*U=1 ∧ U*Uᴴ=1) {A : CMat ι}
    (hA : A.PosSemidef) :
    CFC.sqrt (Uᴴ*A*U) = Uᴴ*CFC.sqrt A*U := by
  have hsq : (Uᴴ*CFC.sqrt A*U) * (Uᴴ*CFC.sqrt A*U) = Uᴴ*A*U := by
    calc
      _ = Uᴴ * (CFC.sqrt A * (U*Uᴴ) * CFC.sqrt A) * U := by
        simp only [Matrix.mul_assoc]
      _ = Uᴴ * (CFC.sqrt A * CFC.sqrt A) * U := by
        rw [hU.2, Matrix.mul_one]
      _ = _ := by rw [CFC.sqrt_mul_sqrt_self A hA.nonneg]
  exact CFC.sqrt_unique hsq
    ((CFC.sqrt_nonneg A).posSemidef.conjTranspose_mul_mul_same U).nonneg

theorem trace_sqrt_product_unitary_conjugate {ι : Type*}
    [Fintype ι] [DecidableEq ι] (U : CMat ι)
    (hU : Uᴴ*U=1 ∧ U*Uᴴ=1) {A B : CMat ι}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    Matrix.trace (CFC.sqrt (Uᴴ*A*U) * CFC.sqrt (Uᴴ*B*U)) =
      Matrix.trace (CFC.sqrt A * CFC.sqrt B) := by
  rw [matrix_sqrt_unitary_conjugate U hU hA, matrix_sqrt_unitary_conjugate U hU hB]
  have hm : (Uᴴ*CFC.sqrt A*U) * (Uᴴ*CFC.sqrt B*U) =
      Uᴴ*(CFC.sqrt A*CFC.sqrt B)*U := by
    calc
      _ = Uᴴ * (CFC.sqrt A * (U*Uᴴ) * CFC.sqrt B) * U := by
        simp only [Matrix.mul_assoc]
      _ = _ := by rw [hU.2, Matrix.mul_one]
  rw [hm, Matrix.trace_mul_cycle, hU.2, Matrix.one_mul]

theorem trace_sqrt_product_gaugePairEveMatrix {A B : CMat PairError}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    Matrix.trace (CFC.sqrt (gaugePairEveMatrix A) *
      CFC.sqrt (gaugePairEveMatrix B)) = Matrix.trace (CFC.sqrt A*CFC.sqrt B) := by
  unfold gaugePairEveMatrix
  rw [sqrt_submatrix_equiv pairEveSectorEquiv
        (hA.conjTranspose_mul_mul_same pairYGauge),
    sqrt_submatrix_equiv pairEveSectorEquiv
        (hB.conjTranspose_mul_mul_same pairYGauge),
    Matrix.submatrix_mul_equiv, trace_submatrix_equiv]
  exact trace_sqrt_product_unitary_conjugate pairYGauge pairYGauge_unitary hA hB

theorem trace_pairEveChannel_correlated_sqrt_product_blocks {p u v w : ℝ}
    (hp0 : 0 < p) (hp1 : p ≤ 1) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1/4) (hv : |v| ≤ 1/8) (hw : |w| ≤ 1/8) :
    Matrix.trace (CFC.sqrt (pairEveChannel p (twoUseRho u v)) *
      CFC.sqrt (pairEveChannel p (twoUseRho u w))) =
        ∑ s : PairQubit, Matrix.trace (CFC.sqrt (pairEveBlock p u v s) *
          CFC.sqrt (pairEveBlock p u w s)) := by
  rw [← trace_sqrt_product_gaugePairEveMatrix
      (pairEveChannel_correlated_posDef hp0 hp1 hu0 hu1 hv).posSemidef
      (pairEveChannel_correlated_posDef hp0 hp1 hu0 hu1 hw).posSemidef,
    pairEveChannel_correlated_blocks hp0.le hp1,
    pairEveChannel_correlated_blocks hp0.le hp1]
  exact trace_matrixBlockDiagonal_sqrt_product _ _
    (fun s => (pairEveBlock_posDef hp0 hp1 hu0 hu1 hv s).posSemidef)
    (fun s => (pairEveBlock_posDef hp0 hp1 hu0 hu1 hw s).posSemidef)

theorem matrix_sqrt_real_smul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (r : ℝ) (hr : 0 ≤ r) {A : CMat ι} (hA : A.PosSemidef) :
    CFC.sqrt (r • A) = Real.sqrt r • CFC.sqrt A := by
  have hs : Real.sqrt r * Real.sqrt r = r := Real.mul_self_sqrt hr
  have hsq : (Real.sqrt r • CFC.sqrt A) * (Real.sqrt r • CFC.sqrt A) = r • A := by
    simp only [Matrix.smul_mul, Matrix.mul_smul,
      smul_smul, hs, CFC.sqrt_mul_sqrt_self A hA.nonneg]
  exact CFC.sqrt_unique hsq
    ((CFC.sqrt_nonneg A).posSemidef.smul (Real.sqrt_nonneg r)).nonneg

theorem trace_sqrt_real_smul_product {ι : Type*} [Fintype ι] [DecidableEq ι]
    (r : ℝ) (hr : 0 ≤ r) {A B : CMat ι}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    Matrix.trace (CFC.sqrt (r • A)*CFC.sqrt (r • B)) =
      (r : ℂ)*Matrix.trace (CFC.sqrt A*CFC.sqrt B) := by
  have hs : Real.sqrt r * Real.sqrt r = r := Real.mul_self_sqrt hr
  rw [matrix_sqrt_real_smul r hr hA, matrix_sqrt_real_smul r hr hB,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul, hs, Matrix.trace_smul]
  exact RCLike.real_smul_eq_coe_mul r _

theorem trace_pairEveChannel_correlated_sqrt_product_weighted {p u v w : ℝ}
    (hp0 : 0 < p) (hp1 : p ≤ 1) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1/4) (hv : |v| ≤ 1/8) (hw : |w| ≤ 1/8) :
    Matrix.trace (CFC.sqrt (pairEveChannel p (twoUseRho u v)) *
      CFC.sqrt (pairEveChannel p (twoUseRho u w))) =
        ∑ s : PairQubit, (pairEveSectorMass p s : ℂ) *
          Matrix.trace
            (CFC.sqrt (normalizedPairEveBlock hp0 hp1 hu0 hu1 hv s).mat *
             CFC.sqrt (normalizedPairEveBlock hp0 hp1 hu0 hu1 hw s).mat) := by
  rw [trace_pairEveChannel_correlated_sqrt_product_blocks hp0 hp1 hu0 hu1 hv hw]
  apply Finset.sum_congr rfl
  intro s _
  rw [← pairEveBlock_weighted_density hp0 hp1 hu0 hu1 hv s,
    ← pairEveBlock_weighted_density hp0 hp1 hu0 hu1 hw s]
  exact trace_sqrt_real_smul_product _ (pairEveSectorMass_pos hp0 hp1 s).le
    (normalizedPairEveBlock hp0 hp1 hu0 hu1 hv s).psd
    (normalizedPairEveBlock hp0 hp1 hu0 hu1 hw s).psd

theorem bobTensorChannel_add (p : ℝ) (n : ℕ) (ρ σ : CMat (QubitWord n)) :
    bobTensorChannel p n (ρ+σ) = bobTensorChannel p n ρ + bobTensorChannel p n σ := by
  simp [bobTensorChannel, Matrix.mul_add, Matrix.add_mul, Finset.sum_add_distrib]

theorem bobTensorChannel_smul (p : ℝ) (n : ℕ) (r : ℂ)
    (ρ : CMat (QubitWord n)) :
    bobTensorChannel p n (r • ρ) = r • bobTensorChannel p n ρ := by
  simp [bobTensorChannel, Matrix.smul_mul, Matrix.mul_smul, ← Finset.smul_sum]

@[simp] theorem eveIMatrix_conjTranspose (p : ℝ) :
    (eveIMatrix p)ᴴ = eveIMatrix p := by
  ext e f
  by_cases hef : e=f
  · subst f
    simp [eveIMatrix, Matrix.diagonal]
  · simp [eveIMatrix, Matrix.diagonal, hef, Ne.symm hef]

@[simp] theorem eveZMatrix_conjTranspose (p : ℝ) :
    (eveZMatrix p)ᴴ = eveZMatrix p := by
  ext e f
  fin_cases e <;> fin_cases f <;>
    norm_num [eveZMatrix, Matrix.conjTranspose_apply] <;> push_cast <;> ring

theorem eveIMatrix_trace (p : ℝ) : Matrix.trace (eveIMatrix p) = 2 := by
  norm_num [eveIMatrix, Matrix.trace_diagonal, Fin.sum_univ_succ, krausWeight]
  push_cast
  ring

theorem eveZMatrix_trace (p : ℝ) : Matrix.trace (eveZMatrix p) = 0 := by
  norm_num [eveZMatrix, Matrix.trace, Matrix.diag, Fin.sum_univ_succ]

theorem eveIMatrix_square_trace (p : ℝ) :
    Matrix.trace (eveIMatrix p * eveIMatrix p) =
      ((4*((aScalar p)^2+3*(bScalar p)^2) : ℝ) : ℂ) := by
  simp only [eveIMatrix, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]
  norm_num [Fin.sum_univ_succ, krausWeight, aScalar, bScalar]
  push_cast
  ring

theorem eveIMatrix_Z_trace (p : ℝ) :
    Matrix.trace (eveIMatrix p * eveZMatrix p) = 0 := by
  norm_num [eveIMatrix, eveZMatrix, Matrix.trace, Matrix.diag,
    Matrix.mul_apply, Matrix.diagonal, Fin.sum_univ_succ]

theorem eveZMatrix_I_trace (p : ℝ) :
    Matrix.trace (eveZMatrix p * eveIMatrix p) = 0 := by
  rw [Matrix.trace_mul_comm, eveIMatrix_Z_trace]

theorem eveZMatrix_square_trace {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    Matrix.trace (eveZMatrix p * eveZMatrix p) =
      ((8*bScalar p*sScalar p : ℝ) : ℂ) := by
  have ha : 0 ≤ 1-3*p/4 := by nlinarith
  have hb : 0 ≤ p/4 := by positivity
  have hroot : (((Real.sqrt (1-3*p/4)*Real.sqrt (p/4) : ℝ) : ℂ))^2 =
      ((aScalar p*bScalar p : ℝ) : ℂ) := by
    rw [← Complex.ofReal_pow, mul_pow, Real.sq_sqrt ha, Real.sq_sqrt hb]
    rfl
  rw [eveZMatrix_eq_physical hp0]
  generalize hc : ((Real.sqrt (1-3*p/4)*Real.sqrt (p/4) : ℝ) : ℂ) = c at *
  have hI : Complex.I^2 = -1 := by norm_num
  norm_num [Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_succ]
  ring_nf
  simp only [hroot, hI]
  push_cast
  simp only [sScalar, aScalar, bScalar]
  push_cast
  ring

def eveAffineBase (p u : ℝ) : CMat PairError :=
  (1/4 : ℂ) • ((eveIMatrix p ⊗ₖ eveIMatrix p) +
    (u : ℂ) • (eveZMatrix p ⊗ₖ eveZMatrix p))

def eveSignalDirection (p : ℝ) : CMat PairError :=
  (1/4 : ℂ) • ((eveZMatrix p ⊗ₖ eveIMatrix p) +
    (eveIMatrix p ⊗ₖ eveZMatrix p))

def bobAffineBase (p u : ℝ) : CMat PairQubit :=
  twoUseRho (u*(etaScalar p)^2) 0

def bobSignalDirection (p : ℝ) : CMat PairQubit :=
  ((etaScalar p/4 : ℝ) : ℂ) •
    ((pauli 3 ⊗ₖ (1 : QubitMatrix)) + ((1 : QubitMatrix) ⊗ₖ pauli 3))

theorem pairEveChannel_correlated_affine {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (u v : ℝ) :
    pairEveChannel p (twoUseRho u v) =
      eveAffineBase p u + (v : ℂ) • eveSignalDirection p := by
  rw [pairEveChannel_correlated hp0 hp1]
  ext e f
  simp only [eveAffineBase, eveSignalDirection, Matrix.add_apply,
    Matrix.smul_apply, smul_eq_mul]
  ring

theorem pairEveChannel_correlated_affine_real {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (u v : ℝ) :
    pairEveChannel p (twoUseRho u v) =
      eveAffineBase p u + v • eveSignalDirection p := by
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
  exact pairEveChannel_correlated_affine hp0 hp1 u v

theorem pairBobChannel_correlated_affine {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (u v : ℝ) :
    pairBobChannel p (twoUseRho u v) =
      bobAffineBase p u + (v : ℂ) • bobSignalDirection p := by
  rw [pairBobChannel_correlated hp0 hp1]
  unfold bobAffineBase
  rw [twoUseRho_eq_pauliExpression, twoUseRho_eq_pauliExpression]
  ext x y
  simp only [bobSignalDirection, etaScalar, Matrix.add_apply,
    Matrix.smul_apply, smul_eq_mul]
  push_cast
  ring

theorem pairBobChannel_correlated_affine_real {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (u v : ℝ) :
    pairBobChannel p (twoUseRho u v) =
      bobAffineBase p u + v • bobSignalDirection p := by
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
  exact pairBobChannel_correlated_affine hp0 hp1 u v

theorem eveAffineBase_hermitian (p u : ℝ) : (eveAffineBase p u).IsHermitian := by
  simp [Matrix.IsHermitian, eveAffineBase, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_add, Matrix.conjTranspose_kronecker]

theorem eveSignalDirection_hermitian (p : ℝ) : (eveSignalDirection p).IsHermitian := by
  simp [Matrix.IsHermitian, eveSignalDirection, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_add, Matrix.conjTranspose_kronecker]

theorem bobAffineBase_hermitian (p u : ℝ) : (bobAffineBase p u).IsHermitian := by
  change (bobAffineBase p u)ᴴ = bobAffineBase p u
  ext x y
  by_cases hxy : x=y
  · subst y
    simp [bobAffineBase, twoUseRho, Matrix.conjTranspose_apply, Matrix.diagonal]
  · simp [bobAffineBase, twoUseRho, Matrix.conjTranspose_apply,
      Matrix.diagonal, hxy, Ne.symm hxy]

theorem bobSignalDirection_hermitian (p : ℝ) : (bobSignalDirection p).IsHermitian := by
  simp [Matrix.IsHermitian, bobSignalDirection, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_add, Matrix.conjTranspose_kronecker]

theorem eveAffineBase_trace (p u : ℝ) : Matrix.trace (eveAffineBase p u) = 1 := by
  norm_num [eveAffineBase, Matrix.trace_smul, Matrix.trace_add,
    Matrix.trace_kronecker, eveIMatrix_trace, eveZMatrix_trace, smul_eq_mul]

theorem eveSignalDirection_trace (p : ℝ) : Matrix.trace (eveSignalDirection p) = 0 := by
  simp [eveSignalDirection, Matrix.trace_smul, Matrix.trace_add,
    Matrix.trace_kronecker, eveZMatrix_trace]

theorem bobAffineBase_trace (p u : ℝ) : Matrix.trace (bobAffineBase p u) = 1 :=
  twoUseRho_trace _ _

theorem bobSignalDirection_trace (p : ℝ) : Matrix.trace (bobSignalDirection p) = 0 := by
  have hZ : Matrix.trace (pauli 3) = 0 := by
    norm_num [pauli, Matrix.trace, Matrix.diag, Fin.sum_univ_two]
  simp [bobSignalDirection, Matrix.trace_smul, Matrix.trace_add,
    Matrix.trace_kronecker, hZ]

theorem trace_quarter_symmetric_kronecker_square {ι : Type*}
    [Fintype ι] [DecidableEq ι] (D Z : CMat ι)
    (hDZ : Matrix.trace (D*Z) = 0) (hZD : Matrix.trace (Z*D) = 0) :
    Matrix.trace (((1/4 : ℂ) • (Z⊗ₖD+D⊗ₖZ)) *
      ((1/4 : ℂ) • (Z⊗ₖD+D⊗ₖZ))) =
      (1/8 : ℂ) * Matrix.trace (Z*Z) * Matrix.trace (D*D) := by
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    Matrix.mul_add, Matrix.add_mul, ← Matrix.mul_kronecker_mul,
    Matrix.trace_smul, Matrix.trace_add, Matrix.trace_kronecker,
    hDZ, hZD, mul_zero, zero_mul, add_zero, smul_eq_mul]
  ring

theorem eveSignalDirection_hs_square {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    realTrace ((eveSignalDirection p)ᴴ * eveSignalDirection p) =
      4*bScalar p*sScalar p*((aScalar p)^2+3*(bScalar p)^2) := by
  have ht : Matrix.trace ((eveSignalDirection p)ᴴ * eveSignalDirection p) =
      ((4*bScalar p*sScalar p*((aScalar p)^2+3*(bScalar p)^2) : ℝ) : ℂ) := by
    rw [(eveSignalDirection_hermitian p).eq]
    unfold eveSignalDirection
    rw [trace_quarter_symmetric_kronecker_square _ _
      (eveIMatrix_Z_trace p) (eveZMatrix_I_trace p),
      eveZMatrix_square_trace hp0 hp1, eveIMatrix_square_trace]
    push_cast
    ring
  unfold realTrace
  rw [ht, Complex.ofReal_re]

theorem bobSignalDirection_hs_square (p : ℝ) :
    realTrace ((bobSignalDirection p)ᴴ * bobSignalDirection p) = (etaScalar p)^2/2 := by
  have hZ : Matrix.trace (pauli 3) = 0 := by
    norm_num [pauli, Matrix.trace, Matrix.diag, Fin.sum_univ_two]
  have hI : Matrix.trace (1 : QubitMatrix) = 2 := by simp
  have hquarter : bobSignalDirection p = (etaScalar p : ℂ) •
      ((1/4 : ℂ) • ((pauli 3 ⊗ₖ (1 : QubitMatrix)) +
        ((1 : QubitMatrix) ⊗ₖ pauli 3))) := by
    ext x y
    simp only [bobSignalDirection, Matrix.smul_apply, smul_eq_mul]
    push_cast
    ring
  have ht : Matrix.trace ((bobSignalDirection p)ᴴ * bobSignalDirection p) =
      (((etaScalar p)^2/2 : ℝ) : ℂ) := by
    rw [(bobSignalDirection_hermitian p).eq, hquarter]
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.trace_smul,
      trace_quarter_symmetric_kronecker_square _ _
        (by simpa only [Matrix.one_mul] using hZ)
        (by simpa only [Matrix.mul_one] using hZ),
      pauli_mul_self, Matrix.one_mul, hI]
    simp only [smul_eq_mul]
    push_cast
    ring
  unfold realTrace
  rw [ht, Complex.ofReal_re]

theorem eveSignalDirection_hs_square_lt_third {p : ℝ}
    (hp0 : 0 < p) (hp1 : p ≤ 1/3) :
    realTrace ((eveSignalDirection p)ᴴ * eveSignalDirection p) < 1/3 := by
  rw [eveSignalDirection_hs_square hp0.le (by linarith)]
  have hb : 0 ≤ bScalar p := (bScalar_pos hp0).le
  have hb1 : bScalar p ≤ 1/12 := by unfold bScalar; linarith
  have ha : 0 ≤ aScalar p := (aScalar_pos hp1).le
  have ha1 : aScalar p ≤ 1 := by unfold aScalar; linarith
  have hb2 : bScalar p ≤ 1 := by linarith
  have hs : 0 ≤ sScalar p := add_nonneg ha hb
  have hs1 : sScalar p < 1 := by unfold sScalar aScalar bScalar; linarith
  have hsq : (aScalar p)^2+3*(bScalar p)^2 ≤ 1 := by
    have ha2 : (aScalar p)^2 ≤ aScalar p := by nlinarith
    have hb3 : (bScalar p)^2 ≤ bScalar p := by nlinarith
    linarith [scalar_weight_sum p]
  calc
    _ ≤ 4*bScalar p*sScalar p :=
      mul_le_of_le_one_right (mul_nonneg (by positivity) hs) hsq
    _ ≤ sScalar p/3 := by nlinarith [mul_le_mul_of_nonneg_right hb1 hs]
    _ < 1/3 := by linarith

theorem bobSignalDirection_hs_square_lt_one {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    realTrace ((bobSignalDirection p)ᴴ * bobSignalDirection p) < 1 := by
  rw [bobSignalDirection_hs_square]
  have h0 : 0 ≤ etaScalar p := by unfold etaScalar; linarith
  have h1 : etaScalar p ≤ 1 := by unfold etaScalar; linarith
  nlinarith [sq_nonneg (etaScalar p)]

theorem eveSignalDirection_sqrt_hs_le_one {p : ℝ}
    (hp0 : 0 < p) (hp1 : p ≤ 1/3) :
    Real.sqrt (realTrace ((eveSignalDirection p)ᴴ * eveSignalDirection p)) ≤ 1 := by
  apply Real.sqrt_le_one.mpr
  linarith [eveSignalDirection_hs_square_lt_third hp0 hp1]

theorem bobSignalDirection_sqrt_hs_le_one {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    Real.sqrt (realTrace ((bobSignalDirection p)ᴴ * bobSignalDirection p)) ≤ 1 := by
  exact Real.sqrt_le_one.mpr (bobSignalDirection_hs_square_lt_one hp0 hp1).le

theorem krausWeight_ge_bScalar {p : ℝ} (hp1 : p ≤ 1) (e : PauliIndex) :
    bScalar p ≤ krausWeight p e := by
  unfold bScalar krausWeight
  split_ifs <;> linarith

theorem pairEveChannel_one_sub_four_b_sq_psd {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (pairEveChannel p (1 : CMat PairQubit) -
      ((4*(bScalar p)^2 : ℝ) : ℂ) • (1 : CMat PairError)).PosSemidef := by
  have hone : pairEveChannel p (1 : CMat PairQubit) =
      Matrix.diagonal (fun e : PairError =>
        ((4*(krausWeight p e.1*krausWeight p e.2) : ℝ) : ℂ)) := by
    rw [pairEveChannel_one hp0 hp1]
    congr 1
    funext e
    push_cast
    rfl
  rw [hone]
  apply real_diagonal_sub_floor_posSemidef
  intro e
  have hb : 0 ≤ bScalar p := by unfold bScalar; positivity
  have hm := mul_le_mul (krausWeight_ge_bScalar hp1 e.1)
    (krausWeight_ge_bScalar hp1 e.2) hb (krausWeight_nonneg hp0 hp1 e.1)
  nlinarith

theorem pairEveChannel_correlated_sub_b_sq_half_psd {p u v : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1/4) (hv : |v| ≤ 1/8) :
    (pairEveChannel p (twoUseRho u v) -
      (((bScalar p)^2/2 : ℝ) : ℂ) • (1 : CMat PairError)).PosSemidef := by
  have h1 := pairEveChannel_correlated_sub_reference_psd (p := p) hu0 hu1 hv
  have h2 := (pairEveChannel_one_sub_four_b_sq_psd hp0 hp1).smul
    (by
      convert Complex.zero_le_real.mpr (by norm_num : (0 : ℝ) ≤ 1/8)
        using 1 <;> norm_num : (0 : ℂ) ≤ 1/8)
  have hm : (1/8 : ℂ) * (((4*(bScalar p)^2 : ℝ) : ℂ)) =
      (((bScalar p)^2/2 : ℝ) : ℂ) := by push_cast; ring
  rw [smul_sub, smul_smul, hm] at h2
  convert h1.add h2 using 1 <;> abel

theorem bScalar_sq_half_gt_saved_floor {p : ℝ} (hp0 : 8/27 ≤ p) :
    1/441 < (bScalar p)^2/2 := by
  have hp : 0 ≤ p := by linarith
  have hsq : (8/27 : ℝ)^2 ≤ p^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hp0) (by linarith : 0 ≤ p+8/27)]
  unfold bScalar
  nlinarith

theorem pairEveChannel_correlated_sub_saved_floor_posDef {p u v : ℝ}
    (hp0 : 8/27 ≤ p) (hp1 : p ≤ 1/3) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1/4) (hv : |v| ≤ 1/8) :
    (pairEveChannel p (twoUseRho u v) -
      (1/441 : ℝ) • (1 : CMat PairError)).PosDef := by
  have hp : 0 ≤ p := by linarith
  have hbase := pairEveChannel_correlated_sub_b_sq_half_psd hp
    (by linarith : p ≤ 1) hu0 hu1 hv
  have hδ : 0 < (bScalar p)^2/2-1/441 :=
    sub_pos.mpr (bScalar_sq_half_gt_saved_floor hp0)
  have hpos : ((((bScalar p)^2/2-1/441 : ℝ) : ℂ) •
      (1 : CMat PairError)).PosDef :=
    Matrix.PosDef.one.smul (Complex.zero_lt_real.mpr hδ)
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
  norm_num
  have hs : (((bScalar p)^2/2-1/441 : ℝ) : ℂ) =
      (((bScalar p)^2/2 : ℝ) : ℂ)-(1/441 : ℂ) := by push_cast; rfl
  rw [hs, sub_smul] at hpos
  convert hpos.add_posSemidef hbase using 1 <;> abel

theorem pairBobChannel_correlated_sub_saved_floor_posDef {p u v : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1/4) (hv : |v| ≤ 1/8) :
    (pairBobChannel p (twoUseRho u v) -
      (1/441 : ℝ) • (1 : CMat PairQubit)).PosDef := by
  have hbase := pairBobChannel_correlated_sub_eighth_psd hp0 hp1 hu0 hu1 hv
  have hpos : ((1/8-1/441 : ℂ) • (1 : CMat PairQubit)).PosDef :=
    Matrix.PosDef.one.smul (by norm_num)
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
  norm_num
  rw [sub_smul] at hpos
  convert hpos.add_posSemidef hbase using 1 <;> abel

theorem eveAffineBase_signal_sub_saved_floor_posDef {p u v : ℝ}
    (hp0 : 8/27 ≤ p) (hp1 : p ≤ 1/3) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1/4) (hv : |v| ≤ 1/8) :
    (eveAffineBase p u + v • eveSignalDirection p -
      (1/441 : ℝ) • (1 : CMat PairError)).PosDef := by
  rw [← pairEveChannel_correlated_affine_real (by linarith : 0 ≤ p)
    (by linarith : p ≤ 1)]
  exact pairEveChannel_correlated_sub_saved_floor_posDef hp0 hp1 hu0 hu1 hv

theorem bobAffineBase_signal_sub_saved_floor_posDef {p u v : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1/4) (hv : |v| ≤ 1/8) :
    (bobAffineBase p u + v • bobSignalDirection p -
      (1/441 : ℝ) • (1 : CMat PairQubit)).PosDef := by
  rw [← pairBobChannel_correlated_affine_real hp0 hp1]
  exact pairBobChannel_correlated_sub_saved_floor_posDef hp0 hp1 hu0 hu1 hv

def pairEveBlockDirection (p : ℝ) (s : PairQubit) : CMat PairQubit :=
  (eveS p s.1 ⊗ₖ eveD p s.2) + (eveD p s.1 ⊗ₖ eveS p s.2)

theorem gaugePairEveMatrix_eveAffineBase {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (u : ℝ) :
    gaugePairEveMatrix (eveAffineBase p u) =
      Matrix.blockDiagonal (pairEveBlock p u 0) := by
  have hbase : pairEveChannel p (twoUseRho u 0) = eveAffineBase p u := by
    simpa only [Complex.ofReal_zero, zero_smul, add_zero] using
      pairEveChannel_correlated_affine hp0 hp1 u 0
  rw [← hbase]
  exact pairEveChannel_correlated_blocks hp0 hp1 u 0

theorem gaugePairEveMatrix_eveSignalDirection {p : ℝ} (hp0 : 0 ≤ p) :
    gaugePairEveMatrix (eveSignalDirection p) =
      Matrix.blockDiagonal (pairEveBlockDirection p) := by
  unfold eveSignalDirection
  simp only [gaugePairEveMatrix_smul, gaugePairEveMatrix_add,
    gaugePairEveMatrix_kronecker, eveYGauge_I_blocks, eveYGauge_Z_blocks hp0,
    Matrix.smul_kronecker, Matrix.kronecker_smul, Matrix.submatrix_smul,
    Pi.smul_apply, smul_smul, blockDiagonal_kronecker_shuffle]
  ext x y
  simp only [Matrix.smul_apply, Matrix.add_apply, smul_eq_mul,
    Matrix.blockDiagonal_apply, pairEveBlockDirection, Matrix.kronecker_apply]
  by_cases h : x.2=y.2 <;> simp only [h, ite_true, ite_false] <;> ring

def ungaugePairEveMatrix (B : CMat (PairQubit × PairQubit)) : CMat PairError :=
  pairYGauge * (B.submatrix pairEveSectorEquiv.symm pairEveSectorEquiv.symm) *
    pairYGaugeᴴ

theorem gaugePairEveMatrix_ungauge (B : CMat (PairQubit × PairQubit)) :
    gaugePairEveMatrix (ungaugePairEveMatrix B) = B := by
  have hm (M : CMat PairError) :
      pairYGaugeᴴ * (pairYGauge*M*pairYGaugeᴴ) * pairYGauge = M := by
    calc
      _ = (pairYGaugeᴴ*pairYGauge)*M*(pairYGaugeᴴ*pairYGauge) := by
        simp only [Matrix.mul_assoc]
      _ = M := by rw [pairYGauge_unitary.1]; simp
  unfold gaugePairEveMatrix ungaugePairEveMatrix
  rw [hm]
  ext x y
  simp only [Matrix.submatrix_apply, Equiv.symm_apply_apply]

theorem ungaugePairEveMatrix_gauge (A : CMat PairError) :
    ungaugePairEveMatrix (gaugePairEveMatrix A) = A := by
  have hr : (gaugePairEveMatrix A).submatrix
      pairEveSectorEquiv.symm pairEveSectorEquiv.symm =
        pairYGaugeᴴ*A*pairYGauge := by
    ext e f
    simp only [gaugePairEveMatrix, Matrix.submatrix_apply, Equiv.apply_symm_apply]
  unfold ungaugePairEveMatrix
  rw [hr]
  calc
    _ = (pairYGauge*pairYGaugeᴴ)*A*(pairYGauge*pairYGaugeᴴ) := by
      simp only [Matrix.mul_assoc]
    _ = A := by rw [pairYGauge_unitary.2]; simp

theorem gaugePairEveMatrix_injective : Function.Injective gaugePairEveMatrix := by
  intro A B h
  have h' := congrArg ungaugePairEveMatrix h
  simpa only [ungaugePairEveMatrix_gauge] using h'

theorem gaugePairEveMatrix_mul (A B : CMat PairError) :
    gaugePairEveMatrix (A*B) = gaugePairEveMatrix A * gaugePairEveMatrix B := by
  have hm : (pairYGaugeᴴ*A*pairYGauge)*(pairYGaugeᴴ*B*pairYGauge) =
      pairYGaugeᴴ*(A*B)*pairYGauge := by
    calc
      _ = pairYGaugeᴴ*(A*(pairYGauge*pairYGaugeᴴ)*B)*pairYGauge := by
        simp only [Matrix.mul_assoc]
      _ = _ := by rw [pairYGauge_unitary.2]; simp only [Matrix.mul_one]
  unfold gaugePairEveMatrix
  rw [Matrix.submatrix_mul_equiv
    (pairYGaugeᴴ*A*pairYGauge) (pairYGaugeᴴ*B*pairYGauge)
    pairEveSectorEquiv pairEveSectorEquiv pairEveSectorEquiv, hm]

theorem trace_gaugePairEveMatrix (A : CMat PairError) :
    Matrix.trace (gaugePairEveMatrix A) = Matrix.trace A := by
  unfold gaugePairEveMatrix
  rw [trace_submatrix_equiv, Matrix.trace_mul_cycle,
    pairYGauge_unitary.2, Matrix.one_mul]

theorem gaugePairEveMatrix_sqrt {A : CMat PairError} (hA : A.PosSemidef) :
    gaugePairEveMatrix (CFC.sqrt A) = CFC.sqrt (gaugePairEveMatrix A) := by
  unfold gaugePairEveMatrix
  rw [sqrt_submatrix_equiv pairEveSectorEquiv
      (hA.conjTranspose_mul_mul_same pairYGauge),
    matrix_sqrt_unitary_conjugate pairYGauge pairYGauge_unitary hA]

def liftPairEveBlockSolution (X : PairQubit → CMat PairQubit) : CMat PairError :=
  ungaugePairEveMatrix (Matrix.blockDiagonal X)

theorem gaugePairEveMatrix_liftPairEveBlockSolution
    (X : PairQubit → CMat PairQubit) :
    gaugePairEveMatrix (liftPairEveBlockSolution X) = Matrix.blockDiagonal X :=
  gaugePairEveMatrix_ungauge _

theorem liftPairEveBlockSolution_hermitian
    (X : PairQubit → CMat PairQubit) (hX : ∀ s, (X s).IsHermitian) :
    (liftPairEveBlockSolution X).IsHermitian := by
  have hblock : (Matrix.blockDiagonal X).IsHermitian :=
    Matrix.isHermitian_blockDiagonal_iff.mpr hX
  unfold liftPairEveBlockSolution ungaugePairEveMatrix
  exact Matrix.isHermitian_mul_mul_conjTranspose pairYGauge
    (hblock.submatrix pairEveSectorEquiv.symm)

theorem gaugePairEveMatrix_eveAffineBase_sqrt {p u : ℝ}
    (hp0 : 0 < p) (hp1 : p ≤ 1) (hu0 : 0 ≤ u) (hu1 : u ≤ 1/4) :
    gaugePairEveMatrix (CFC.sqrt (eveAffineBase p u)) =
      Matrix.blockDiagonal (fun s => CFC.sqrt (pairEveBlock p u 0 s)) := by
  have hbase : (eveAffineBase p u).PosSemidef := by
    have h := (pairEveChannel_correlated_posDef hp0 hp1 hu0 hu1
      (by norm_num : |(0 : ℝ)| ≤ 1/8)).posSemidef
    rw [pairEveChannel_correlated_affine hp0.le hp1 u 0] at h
    simpa only [Complex.ofReal_zero, zero_smul, add_zero] using h
  rw [gaugePairEveMatrix_sqrt hbase,
    gaugePairEveMatrix_eveAffineBase hp0.le hp1]
  exact matrixBlockDiagonal_sqrt _ (fun s =>
    (pairEveBlock_posDef hp0 hp1 hu0 hu1
      (by norm_num : |(0 : ℝ)| ≤ 1/8) s).posSemidef)

theorem liftPairEveBlockSolution_sylvester {p u : ℝ}
    (hp0 : 0 < p) (hp1 : p ≤ 1) (hu0 : 0 ≤ u) (hu1 : u ≤ 1/4)
    (X : PairQubit → CMat PairQubit)
    (hX : ∀ s, CFC.sqrt (pairEveBlock p u 0 s)*X s +
      X s*CFC.sqrt (pairEveBlock p u 0 s) = pairEveBlockDirection p s) :
    CFC.sqrt (eveAffineBase p u)*liftPairEveBlockSolution X +
      liftPairEveBlockSolution X*CFC.sqrt (eveAffineBase p u) =
        eveSignalDirection p := by
  apply gaugePairEveMatrix_injective
  rw [gaugePairEveMatrix_add, gaugePairEveMatrix_mul, gaugePairEveMatrix_mul,
    gaugePairEveMatrix_eveAffineBase_sqrt hp0 hp1 hu0 hu1,
    gaugePairEveMatrix_liftPairEveBlockSolution,
    gaugePairEveMatrix_eveSignalDirection hp0.le,
    ← Matrix.blockDiagonal_mul, ← Matrix.blockDiagonal_mul,
    ← Matrix.blockDiagonal_add]
  congr 1
  funext s
  exact hX s

theorem trace_liftPairEveBlockSolution_square
    (X : PairQubit → CMat PairQubit) :
    Matrix.trace (liftPairEveBlockSolution X * liftPairEveBlockSolution X) =
      ∑ s, Matrix.trace (X s*X s) := by
  rw [← trace_gaugePairEveMatrix
      (liftPairEveBlockSolution X * liftPairEveBlockSolution X),
    gaugePairEveMatrix_mul, gaugePairEveMatrix_liftPairEveBlockSolution,
    ← Matrix.blockDiagonal_mul, Matrix.trace_blockDiagonal]

theorem two_realTrace_liftPairEveBlockSolution_square
    (X : PairQubit → CMat PairQubit) :
    2*realTrace (liftPairEveBlockSolution X * liftPairEveBlockSolution X) =
      ∑ s, 2*realTrace (X s*X s) := by
  have ht := trace_liftPairEveBlockSolution_square X
  have hr : realTrace (liftPairEveBlockSolution X * liftPairEveBlockSolution X) =
      ∑ s, realTrace (X s*X s) := by
    simpa only [realTrace, Complex.re_sum] using congrArg Complex.re ht
  rw [hr, Finset.mul_sum]

end QuantumProver.DepolarizingPrivateInformation

import QuantumProver.InformationTheory.AmplitudeDamping.SecretKey.ScalarBounds
import QuantumProver.InformationTheory.AmplitudeDamping.SecretKey.PurificationBounds
import QuantumProver.InformationTheory.AmplitudeDamping.SecretKey.SeedResourceCharge

noncomputable section

open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix Kronecker

namespace QuantumProver.AmplitudeDamping.SecretKey.IndependentLanes

universe u

@[reducible] def Register (I : Type u) : ℕ → Type u
  | 0 => PUnit
  | n + 1 => I × Register I n

@[reducible] instance registerFintype (I : Type*) [Fintype I] (n : ℕ) :
    Fintype (Register I n) :=
  match n with
  | 0 => inferInstanceAs (Fintype PUnit)
  | n + 1 =>
      letI := registerFintype I n
      inferInstanceAs (Fintype (I × Register I n))

@[reducible] instance registerDecidableEq (I : Type*) [DecidableEq I] (n : ℕ) :
    DecidableEq (Register I n) :=
  match n with
  | 0 => inferInstanceAs (DecidableEq PUnit)
  | n + 1 =>
      letI := registerDecidableEq I n
      inferInstanceAs (DecidableEq (I × Register I n))

instance registerNonempty (I : Type*) [Nonempty I] (n : ℕ) :
    Nonempty (Register I n) :=
  match n with
  | 0 => inferInstanceAs (Nonempty PUnit)
  | n + 1 =>
      letI := registerNonempty I n
      inferInstanceAs (Nonempty (I × Register I n))

theorem register_card (I : Type*) [Fintype I] (n : ℕ) :
    Fintype.card (Register I n) = (Fintype.card I) ^ n := by
  induction n with
  | zero => change Fintype.card PUnit = 1; simp
  | succ n ih =>
      change Fintype.card (I × Register I n) = _
      rw [Fintype.card_prod, ih, pow_succ, Nat.mul_comm]

def pairEquiv (A B : Type*) : (n : ℕ) →
    Register (A × B) n ≃ Register A n × Register B n
  | 0 =>
      { toFun := fun _ => (PUnit.unit, PUnit.unit)
        invFun := fun _ => PUnit.unit
        left_inv := by intro x; cases x; rfl
        right_inv := by intro x; rcases x with ⟨x,y⟩; cases x; cases y; rfl }
  | n + 1 =>
      (Equiv.prodCongr (Equiv.refl (A × B)) (pairEquiv A B n)).trans
        (Equiv.prodProdProdComm A B (Register A n) (Register B n))

end QuantumProver.AmplitudeDamping.SecretKey.IndependentLanes

namespace QuantumProver.AmplitudeDamping.SecretKey.KrausChannel

variable {I O J I' O' J' : Type*}
  [Fintype I] [Fintype O] [Fintype J] [Fintype I'] [Fintype O'] [Fintype J']
  [DecidableEq I] [DecidableEq O] [DecidableEq I'] [DecidableEq O']

def tensorLanes_B (C : KrausChannel I O J) (D : KrausChannel I' O' J') :
    KrausChannel (I × I') (O × O') (J × J') :=
  (D.withMemory O).compose (C.withRightMemory I')

theorem tensorLanes_op_B (C : KrausChannel I O J) (D : KrausChannel I' O' J')
    (h : J) (k : J') : (C.tensorLanes_B D).op (h,k) = C.op h ⊗ₖ D.op k := by
  simp only [tensorLanes_B, compose, withMemory, withRightMemory,
    ← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one]

theorem tensorLanes_eval_B (C : KrausChannel I O J) (D : KrausChannel I' O' J')
    (M : Matrix I I ℂ) (N : Matrix I' I' ℂ) :
    (C.tensorLanes_B D).eval (M ⊗ₖ N) = C.eval M ⊗ₖ D.eval N := by
  simp only [eval, Fintype.sum_prod_type, tensorLanes_op_B,
    Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul]
  ext x y
  simp only [Matrix.sum_apply, Matrix.kroneckerMap_apply,
    Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_comm

end QuantumProver.AmplitudeDamping.SecretKey.KrausChannel

namespace QuantumProver.AmplitudeDamping.SecretKey.IndependentLanes

variable {I O J : Type*} [Fintype I] [Fintype O] [Fintype J]
  [DecidableEq I] [DecidableEq O]

def matrix (M : Matrix I I ℂ) : (n : ℕ) →
    Matrix (Register I n) (Register I n) ℂ
  | 0 => 1
  | n + 1 => M ⊗ₖ matrix M n

theorem matrix_mul (M N : Matrix I I ℂ) (n : ℕ) :
    matrix M n * matrix N n = matrix (M * N) n := by
  induction n with
  | zero => simp [matrix]
  | succ n ih =>
      change (M ⊗ₖ matrix M n) * (N ⊗ₖ matrix N n) = _
      rw [← Matrix.mul_kronecker_mul, ih]
      rfl

theorem matrix_trace (M : Matrix I I ℂ) (n : ℕ) :
    (matrix M n).trace = M.trace ^ n := by
  induction n with
  | zero => simp [matrix, Register]
  | succ n ih =>
      change (M ⊗ₖ matrix M n).trace = _
      rw [Matrix.trace_kronecker, ih, pow_succ, mul_comm]

theorem productTest_trace (T M : Matrix I I ℂ) (n : ℕ) :
    (matrix T n * matrix M n).trace = (T * M).trace ^ n := by
  rw [matrix_mul, matrix_trace]

def channel (C : KrausChannel I O J) : (n : ℕ) →
    KrausChannel (Register I n) (Register O n) (Register J n)
  | 0 =>
      { op := fun _ _ _ => 1
        complete := by
          ext i j
          cases i
          cases j
          change (∑ _ : Register J 0, ∑ _ : Register O 0, star (1 : ℂ) * 1) = 1
          simp [Register, registerFintype] }
  | n + 1 => C.tensorLanes_B (channel C n)

theorem channel_eval (C : KrausChannel I O J) (M : Matrix I I ℂ) (n : ℕ) :
    (channel C n).eval (matrix M n) = matrix (C.eval M) n := by
  induction n with
  | zero =>
      ext i j; cases i; cases j
      change (∑ _ : Register J 0, ∑ _ : Register I 0,
        (∑ _ : Register I 0, (1 : ℂ) * 1) * star (1 : ℂ)) = 1
      simp [Register, registerFintype]
  | succ n ih =>
      change (C.tensorLanes_B (channel C n)).eval (M ⊗ₖ matrix M n) =
        C.eval M ⊗ₖ matrix (C.eval M) n
      rw [KrausChannel.tensorLanes_eval_B, ih]

def density (ρ : Density I) : (n : ℕ) → Density (Register I n)
  | 0 => { mat := 1, positive := Matrix.PosSemidef.one, normalized := by simp [Register] }
  | n + 1 => ρ.tensor (density ρ n)

theorem density_mat (ρ : Density I) (n : ℕ) :
    (density ρ n).mat = matrix ρ.mat n := by
  induction n with
  | zero => rfl
  | succ n ih => change ρ.mat ⊗ₖ (density ρ n).mat = _; rw [ih]; rfl

theorem channel_onDensity (C : KrausChannel I O J) (ρ : Density I) (n : ℕ) :
    (channel C n).onDensity (density ρ n) = density (C.onDensity ρ) n := by
  apply Density.eq_of_mat_eq
  change (channel C n).eval (density ρ n).mat = _
  rw [density_mat, density_mat, channel_eval]
  rfl

end QuantumProver.AmplitudeDamping.SecretKey.IndependentLanes

namespace QuantumProver.AmplitudeDamping.SecretKey.ProbabilityLaw

variable {J K : Type*} [Fintype J] [Fintype K] [DecidableEq J] [DecidableEq K]

def tensorLanes_B (a : ProbabilityLaw J) (b : ProbabilityLaw K) :
    ProbabilityLaw (J × K) where
  weight jk := a.weight jk.1 * b.weight jk.2
  nonnegative jk := mul_nonneg (a.nonnegative jk.1) (b.nonnegative jk.2)
  normalized := by
    simp only [Fintype.sum_prod_type, ← Finset.mul_sum,
      b.normalized, mul_one, a.normalized]

theorem tensorLanes_coherentSeedVector_B (a : ProbabilityLaw J) (b : ProbabilityLaw K)
    (x : (J × K) × (J × K)) :
    (a.tensorLanes_B b).coherentSeedVector x =
      a.coherentSeedVector (x.1.1,x.2.1) *
        b.coherentSeedVector (x.1.2,x.2.2) := by
  by_cases hJ : x.1.1 = x.2.1 <;> by_cases hK : x.1.2 = x.2.2
  · have h : x.1 = x.2 := Prod.ext hJ hK
    simp only [coherentSeedVector, tensorLanes_B, h, hJ, hK, ite_true]
    rw [Real.sqrt_mul (a.nonnegative _), Complex.ofReal_mul]
  · have h : x.1 ≠ x.2 := fun h => hK (congrArg Prod.snd h)
    simp [coherentSeedVector, h, hK]
  · have h : x.1 ≠ x.2 := fun h => hJ (congrArg Prod.fst h)
    simp [coherentSeedVector, h, hJ]
  · have h : x.1 ≠ x.2 := fun h => hJ (congrArg Prod.fst h)
    simp [coherentSeedVector, h, hJ]

theorem tensorLanes_coherentSeedMatrix_B (a : ProbabilityLaw J) (b : ProbabilityLaw K) :
    (a.tensorLanes_B b).coherentSeedMatrix =
      (a.coherentSeedMatrix ⊗ₖ b.coherentSeedMatrix).submatrix
        (Equiv.prodProdProdComm J K J K) (Equiv.prodProdProdComm J K J K) := by
  ext x y
  simp only [coherentSeedMatrix, Matrix.vecMulVec_apply,
    tensorLanes_coherentSeedVector_B, Pi.star_apply, star_mul,
    Matrix.submatrix_apply, Matrix.kroneckerMap_apply,
    Equiv.prodProdProdComm_apply]
  ring

theorem tensorLanes_seedPowerSum_B (a : ProbabilityLaw J) (b : ProbabilityLaw K) (z : ℝ) :
    (a.tensorLanes_B b).seedPowerSum z = a.seedPowerSum z * b.seedPowerSum z := by
  unfold seedPowerSum
  simp only [tensorLanes_B, Fintype.sum_prod_type]
  simp_rw [Real.mul_rpow (a.nonnegative _) (b.nonnegative _)]
  rw [Finset.sum_mul]
  simp only [Finset.mul_sum]

theorem tensorLanes_renyiSeedCharge_B (a : ProbabilityLaw J) (b : ProbabilityLaw K) (z : ℝ) :
    (a.tensorLanes_B b).renyiSeedCharge z = a.renyiSeedCharge z + b.renyiSeedCharge z := by
  change ((1 + z) / z) * log2 ((a.tensorLanes_B b).seedPowerSum z) =
    ((1 + z) / z) * log2 (a.seedPowerSum z) +
      ((1 + z) / z) * log2 (b.seedPowerSum z)
  rw [tensorLanes_seedPowerSum_B]
  unfold log2
  rw [Real.log_mul (a.seedPowerSum_pos z).ne' (b.seedPowerSum_pos z).ne']
  ring

def independent_B (a : ProbabilityLaw J) : (n : ℕ) →
    ProbabilityLaw (IndependentLanes.Register J n)
  | 0 =>
      { weight := fun _ => 1
        nonnegative := fun _ => zero_le_one
        normalized := by simp [IndependentLanes.Register] }
  | n + 1 => a.tensorLanes_B (independent_B a n)

theorem independent_renyiSeedCharge_B (a : ProbabilityLaw J) (n : ℕ) (z : ℝ) :
    (independent_B a n).renyiSeedCharge z = (n : ℝ) * a.renyiSeedCharge z := by
  induction n with
  | zero => simp [independent_B, renyiSeedCharge, log2, IndependentLanes.Register]
  | succ n ih =>
      change (a.tensorLanes_B (independent_B a n)).renyiSeedCharge z = _
      rw [tensorLanes_renyiSeedCharge_B, ih]
      push_cast
      ring

theorem independent_coherentSeedMatrix_B (a : ProbabilityLaw J) (n : ℕ) :
    (independent_B a n).coherentSeedMatrix =
      (IndependentLanes.matrix a.coherentSeedMatrix n).submatrix
        (IndependentLanes.pairEquiv J J n).symm
        (IndependentLanes.pairEquiv J J n).symm := by
  induction n with
  | zero =>
      ext x y
      rcases x with ⟨x₁,x₂⟩
      rcases y with ⟨y₁,y₂⟩
      cases x₁; cases x₂; cases y₁; cases y₂
      change (Real.sqrt (1 : ℝ) : ℂ) * star (Real.sqrt (1 : ℝ) : ℂ) = 1
      simp
  | succ n ih =>
      rw [independent_B, tensorLanes_coherentSeedMatrix_B, ih]
      ext x y
      simp only [IndependentLanes.matrix, IndependentLanes.pairEquiv,
        Matrix.submatrix_apply, Matrix.kroneckerMap_apply,
        Equiv.symm_trans_apply, Equiv.prodCongr_symm,
        Equiv.prodCongr_apply, Equiv.prodProdProdComm_symm,
        Equiv.prodProdProdComm_apply, Equiv.refl_symm, Equiv.refl_apply]
      rfl

theorem independent_renyiSeedCharge_le_bits_B [Nonempty J]
    (a : ProbabilityLaw J) (n : ℕ) (z k : ℝ) (hz : 0 < z)
    (hbits : log2 (Fintype.card J : ℝ) ≤ k) :
    (independent_B a n).renyiSeedCharge z ≤ (n : ℝ) * k := by
  have h := (independent_B a n).renyiSeedCharge_le_alphabet z hz
  rw [IndependentLanes.register_card, Nat.cast_pow] at h
  have hlog : log2 ((Fintype.card J : ℝ) ^ n) =
      (n : ℝ) * log2 (Fintype.card J : ℝ) := by
    unfold log2
    rw [Real.log_pow]
    ring
  rw [hlog] at h
  exact h.trans (mul_le_mul_of_nonneg_left hbits (Nat.cast_nonneg n))

theorem independent_entropyBits_le_bits_B [Nonempty J]
    (a : ProbabilityLaw J) (n : ℕ) (k : ℝ)
    (hbits : log2 (Fintype.card J : ℝ) ≤ k) :
    (independent_B a n).entropyBits ≤ (n : ℝ) * k := by
  have h := (independent_B a n).entropyBits_le_alphabet
  rw [IndependentLanes.register_card, Nat.cast_pow] at h
  have hlog : log2 ((Fintype.card J : ℝ) ^ n) =
      (n : ℝ) * log2 (Fintype.card J : ℝ) := by
    unfold log2
    rw [Real.log_pow]
    ring
  rw [hlog] at h
  exact h.trans (mul_le_mul_of_nonneg_left hbits (Nat.cast_nonneg n))

end QuantumProver.AmplitudeDamping.SecretKey.ProbabilityLaw

namespace QuantumProver.AmplitudeDamping.SecretKey.IndependentLanes

open PhysicalProtocol PhysicalProtocol.FiniteKeyProtocol PublicHistory

variable {p : ℝ} {a b af bf : ℕ} {E K : Type*}
  [Fintype E] [DecidableEq E] [Fintype K] [DecidableEq K]

def retainedChannel_B (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (P : FiniteKeyProtocol p a b af bf) (n : ℕ) :=
  channel (wholeRetainedChannelWithEve_B hp0 hp1 P E) n

theorem retainedChannel_eval_B (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (P : FiniteKeyProtocol p a b af bf)
    (ρ : Matrix ((Fin a × Fin b) × E) ((Fin a × Fin b) × E) ℂ) (n : ℕ) :
    (retainedChannel_B (E := E) hp0 hp1 P n).eval (matrix ρ n) =
      matrix ((wholeRetainedChannelWithEve_B hp0 hp1 P E).eval ρ) n :=
  channel_eval _ _ _

def retainedReadout_B (P : FiniteKeyProtocol p a b af bf)
    (label : Fin af × Fin bf → K) :=
  (basisReadoutChannel
    (fun x : ((P.comparisonPublicHistory_B × Fin af) ×
      (P.comparisonPublicHistory_B × Fin bf)) => label (x.1.2,x.2.2))).withRightMemory
        (P.Environment × E)

def measuredChannel_B (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (P : FiniteKeyProtocol p a b af bf) (label : Fin af × Fin bf → K) (n : ℕ) :=
  channel ((retainedReadout_B (E := E) P label).compose
    (wholeRetainedChannelWithEve_B hp0 hp1 P E)) n

theorem measuredChannel_eval_B (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (P : FiniteKeyProtocol p a b af bf) (label : Fin af × Fin bf → K)
    (ρ : Matrix ((Fin a × Fin b) × E) ((Fin a × Fin b) × E) ℂ) (n : ℕ) :
    (measuredChannel_B (E := E) hp0 hp1 P label n).eval (matrix ρ n) =
      matrix (((basisReadoutChannel label).withRightMemory (P.Environment × E)).eval
        (localPriorEveMatrix_B P ρ)) n := by
  rw [measuredChannel_B, channel_eval, KrausChannel.eval_compose]
  congr 1
  exact wholeRetainedChannelWithEve_readout_B hp0 hp1 P label ρ

end QuantumProver.AmplitudeDamping.SecretKey.IndependentLanes

namespace QuantumProver.AmplitudeDamping.SecretKey.ProbabilityLaw

variable {J : Type*} [Fintype J] [DecidableEq J] [Nonempty J]

theorem independent_coherentSeed_entanglement_le_B
    (a : ProbabilityLaw J) (n : ℕ) {d : ℕ}
    (e : Fin d ≃ IndependentLanes.Register J n)
    {z : ℝ} (hz : 0 < z) (hz1 : z < 1) :
    QuantumProver.AmplitudeDamping.FiniteModel.sandwichedEntanglement (1 / (1 - z)) d d
      ((a.independent_B n).coherentSeedMatrix.submatrix
        (e.prodCongr e) (e.prodCongr e)) ≤
          ((n : ℝ) * a.renyiSeedCharge z : EReal) := by
  have h := (a.independent_B n).coherentSeed_entanglement_le_after_local_relabel e hz hz1
  rw [a.independent_renyiSeedCharge_B n z] at h
  exact h

theorem independent_coherentSeed_entanglement_le_bits_B
    (a : ProbabilityLaw J) (n : ℕ) {d : ℕ}
    (e : Fin d ≃ IndependentLanes.Register J n)
    {z k : ℝ} (hz : 0 < z) (hz1 : z < 1)
    (hbits : log2 (Fintype.card J : ℝ) ≤ k) :
    QuantumProver.AmplitudeDamping.FiniteModel.sandwichedEntanglement (1 / (1 - z)) d d
      ((a.independent_B n).coherentSeedMatrix.submatrix
        (e.prodCongr e) (e.prodCongr e)) ≤ ((n : ℝ) * k : EReal) := by
  apply ((a.independent_B n).coherentSeed_entanglement_le_after_local_relabel
    e hz hz1).trans
  exact_mod_cast a.independent_renyiSeedCharge_le_bits_B n z k hz hbits

end QuantumProver.AmplitudeDamping.SecretKey.ProbabilityLaw

namespace QuantumProver.AmplitudeDamping.SecretKey.IndependentLanes

open PhysicalProtocol

theorem quantum_dampingKraus_eq_key_B (p : ℝ) (z : Fin 2) :
    QuantumProver.AmplitudeDamping.FiniteModel.dampingKraus p z = amplitudeDampingKraus p z := by
  fin_cases z <;>
    simp [QuantumProver.AmplitudeDamping.FiniteModel.dampingKraus,
      QuantumProver.AmplitudeDamping.FiniteModel.dampingNoLoss,
      QuantumProver.AmplitudeDamping.FiniteModel.dampingLoss,
      amplitudeDampingKraus, noJumpKraus, jumpKraus]

theorem quantum_callOperator_eq_key_B (p : ℝ) (a b : ℕ) (z : Fin 2) :
    QuantumProver.AmplitudeDamping.FiniteModel.callOperator p a b z = transferKraus p a b z := by
  unfold QuantumProver.AmplitudeDamping.FiniteModel.callOperator transferKraus
  rw [quantum_dampingKraus_eq_key_B]
  rfl

def toQuantum_B {p : ℝ} {a b af bf : ℕ}
    (P : FiniteKeyProtocol p a b af bf) :
    QuantumProver.AmplitudeDamping.FiniteModel.FiniteProtocol p a b af bf :=
  match P with
  | .done a b => .done a b
  | .alice C next =>
      .alice { operator := C.op, complete := C.complete } fun z => toQuantum_B (next z)
  | .bob C next =>
      .bob { operator := C.op, complete := C.complete } fun z => toQuantum_B (next z)
  | .call next => .call (toQuantum_B next)

def fromQuantum_B {p : ℝ} {a b af bf : ℕ}
    (P : QuantumProver.AmplitudeDamping.FiniteModel.FiniteProtocol p a b af bf) :
    FiniteKeyProtocol p a b af bf :=
  match P with
  | .done a b => .done a b
  | .alice C next =>
      .alice { op := C.operator, complete := C.complete } fun z => fromQuantum_B (next z)
  | .bob C next =>
      .bob { op := C.operator, complete := C.complete } fun z => fromQuantum_B (next z)
  | .call next => .call (fromQuantum_B next)

theorem toQuantum_calls_B {p : ℝ} {a b af bf : ℕ}
    (P : FiniteKeyProtocol p a b af bf) : (toQuantum_B P).calls = P.calls := by
  induction P with
  | done a b => rfl
  | alice C next ih =>
      simp only [toQuantum_B, QuantumProver.AmplitudeDamping.FiniteModel.FiniteProtocol.calls,
        FiniteKeyProtocol.calls, ih]
  | bob C next ih =>
      simp only [toQuantum_B, QuantumProver.AmplitudeDamping.FiniteModel.FiniteProtocol.calls,
        FiniteKeyProtocol.calls, ih]
  | call next ih =>
      simp only [toQuantum_B, QuantumProver.AmplitudeDamping.FiniteModel.FiniteProtocol.calls,
        FiniteKeyProtocol.calls, ih]

theorem fromQuantum_calls_B {p : ℝ} {a b af bf : ℕ}
    (P : QuantumProver.AmplitudeDamping.FiniteModel.FiniteProtocol p a b af bf) :
    (fromQuantum_B P).calls = P.calls := by
  induction P with
  | done a b => rfl
  | alice C next ih =>
      simp only [fromQuantum_B, QuantumProver.AmplitudeDamping.FiniteModel.FiniteProtocol.calls,
        FiniteKeyProtocol.calls, ih]
  | bob C next ih =>
      simp only [fromQuantum_B, QuantumProver.AmplitudeDamping.FiniteModel.FiniteProtocol.calls,
        FiniteKeyProtocol.calls, ih]
  | call next ih =>
      simp only [fromQuantum_B, QuantumProver.AmplitudeDamping.FiniteModel.FiniteProtocol.calls,
        FiniteKeyProtocol.calls, ih]

theorem fromQuantum_toQuantum_B {p : ℝ} {a b af bf : ℕ}
    (P : FiniteKeyProtocol p a b af bf) : fromQuantum_B (toQuantum_B P) = P := by
  induction P with
  | done a b => rfl
  | alice C next ih =>
      change FiniteKeyProtocol.alice C (fun z => fromQuantum_B (toQuantum_B (next z))) =
        FiniteKeyProtocol.alice C next
      congr 1
      funext z
      exact ih z
  | bob C next ih =>
      change FiniteKeyProtocol.bob C (fun z => fromQuantum_B (toQuantum_B (next z))) =
        FiniteKeyProtocol.bob C next
      congr 1
      funext z
      exact ih z
  | call next ih =>
      change FiniteKeyProtocol.call (fromQuantum_B (toQuantum_B next)) = _
      rw [ih]

def blockExpansion_B {p : ℝ} {n a b af bf : ℕ}
    (P : QuantumProver.AmplitudeDamping.FiniteModel.FiniteBlockProtocolB p n a b af bf) :
    FiniteKeyProtocol p a b af bf := fromQuantum_B P.represented_toMatrix

theorem blockExpansion_calls_le_B {p : ℝ} {n a b af bf : ℕ}
    (P : QuantumProver.AmplitudeDamping.FiniteModel.FiniteBlockProtocolB p n a b af bf) :
    (blockExpansion_B P).calls ≤ n * P.calls := by
  rw [blockExpansion_B, fromQuantum_calls_B]
  exact P.toMatrix_calls_le

end QuantumProver.AmplitudeDamping.SecretKey.IndependentLanes

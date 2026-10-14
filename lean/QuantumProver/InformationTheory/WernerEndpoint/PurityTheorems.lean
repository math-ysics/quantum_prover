import QuantumProver.InformationTheory.WernerEndpoint.ContinuousStateProtocol
import QuantumProver.InformationTheory.WernerEndpoint.SingletResource
import QuantumProver.InformationTheory.WernerEndpoint.FidelityError
import QuantumProver.InformationTheory.WernerEndpoint.AntisymmetricStates
import QuantumProver.InformationTheory.WernerEndpoint.PurityBounds
import QuantumProver.InformationTheory.WernerEndpoint.ChannelCoherence
import QuantumProver.InformationTheory.WernerEndpoint.EnsemblePhase
import QuantumProver.InformationTheory.WernerEndpoint.D5SupportFactor
import QuantumProver.InformationTheory.WernerEndpoint.D5NuclearControl
import QuantumProver.InformationTheory.WernerEndpoint.ActualContractionLower
import QuantumProver.InformationTheory.WernerEndpoint.AntisymmetricEntropyCost
import QuantumProver.InformationTheory.WernerEndpoint.AntisymmetricEnsembleCost
import QuantumProver.InformationTheory.WernerEndpoint.DensityEnsembleExistence
import QuantumProver.InformationTheory.WernerEndpoint.AllDimensionalMoment
import QuantumProver.InformationTheory.WernerEndpoint.ExteriorHaar
import QuantumProver.InformationTheory.WernerEndpoint.OperationalEndpointCost
import QuantumProver.InformationTheory.WernerEndpoint.LocalProtocolReindex
import QuantumProver.InformationTheory.WernerEndpoint.EntropyCostCertificate
import QuantumProver.InformationTheory.WernerEndpoint.EndpointProtocolClosure
import QuantumProver.InformationTheory.ConditionalEntropy.WeightedContinuity

noncomputable section

namespace QuantumProver.WernerEndpoint

open scoped BigOperators ComplexOrder Matrix Kronecker

theorem antisymmetricChannel_eq_stinespring (d : ℕ)
    (ρ : Matrix (Edge d) (Edge d) ℂ) :
    antisymmetricChannel d ρ = (antisymmetricStinespring d).apply ρ := rfl

theorem antisymmetricChannel_trace (d : ℕ) (ρ : Matrix (Edge d) (Edge d) ℂ) :
    Matrix.trace (antisymmetricChannel d ρ) = Matrix.trace ρ :=
  (antisymmetricStinespring d).apply_trace ρ

theorem antisymmetricChannel_completelyPositive (d : ℕ) {R : Type*}
    [Fintype R] [DecidableEq R] (ρ : Matrix (R × Edge d) (R × Edge d) ℂ)
    (hρ : ρ.PosSemidef) : ((antisymmetricStinespring d).amplify ρ).PosSemidef :=
  (antisymmetricStinespring d).apply_completelyPositive ρ hρ

theorem wedge_sandwich_swap (d : ℕ) (ρ : Matrix (Edge d) (Edge d) ℂ)
    (a b c f : Fin d) :
    (wedgeInclusion d * ρ * (wedgeInclusion d).conjTranspose) (b, a) (f, c) =
    (wedgeInclusion d * ρ * (wedgeInclusion d).conjTranspose) (a, b) (c, f) := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
  simp_rw [wedgeInclusion_swap d a b, wedgeInclusion_swap d c f]
  simp

theorem antisymmetricChannel_eq_complement (d : ℕ)
    (ρ : Matrix (Edge d) (Edge d) ℂ) :
    antisymmetricChannel d ρ = antisymmetricComplement d ρ := by
  ext a c
  simp only [antisymmetricChannel, antisymmetricComplement,
    partialTraceLeft, partialTraceRight]
  apply Finset.sum_congr rfl
  intro b _
  exact (wedge_sandwich_swap d ρ a b c b).symm

def coordinateSlater {d : ℕ} (e : Edge d) : Edge d → ℂ := Pi.single e 1

def slaterAmplitude {d : ℕ} (e : Edge d) : Matrix (Fin d) (Fin d) ℂ :=
  fun a b => wedgeInclusion d (a, b) e

def slaterOutput {d : ℕ} (e : Edge d) : Matrix (Fin d) (Fin d) ℂ :=
  (1 / 2 : ℂ) • (Matrix.single e.val.1 e.val.1 1 + Matrix.single e.val.2 e.val.2 1)

theorem coordinateSlater_normSq {d : ℕ} (e : Edge d) :
    vectorNormSq (coordinateSlater e) = 1 := by
  simp [coordinateSlater, vectorNormSq, Pi.single_apply]

theorem slaterAmplitude_reducedLeft {d : ℕ} (e : Edge d) :
    reducedLeft (slaterAmplitude e) = slaterOutput e := by
  have he : e.val.1 ≠ e.val.2 := ne_of_lt e.property
  ext a c
  simp [slaterAmplitude, reducedLeft, crossLeft, wedgeInclusion, slaterOutput,
    endpointConj_ite, mul_sub, sub_mul, Finset.sum_sub_distrib,
    mul_ite, ite_mul, ite_and, Matrix.single_apply, he, Ne.symm he,
    wedgeScale_square, eq_comm]
  all_goals split_ifs <;> norm_num

theorem antisymmetricChannel_coordinateSlater {d : ℕ} (e : Edge d) :
    antisymmetricChannel d (pureDensity (coordinateSlater e)) = slaterOutput e := by
  unfold antisymmetricChannel pureDensity
  rw [sandwich_crossDensity]
  simp only [coordinateSlater, Matrix.mulVec_single_one]
  have hleft : partialTraceLeft (crossDensity ((wedgeInclusion d).col e)
      ((wedgeInclusion d).col e)) = reducedLeft (slaterAmplitude e) := by
    ext a c
    rfl
  rw [hleft, slaterAmplitude_reducedLeft]

theorem slaterOutput_purity {d : ℕ} (e : Edge d) :
    purity (slaterOutput e) = 1 / 2 := by
  have he : e.val.1 ≠ e.val.2 := ne_of_lt e.property
  norm_num [purity, slaterOutput, smul_mul_assoc, mul_smul_comm, smul_smul,
    Matrix.add_mul, Matrix.mul_add, Matrix.single_mul_single_same,
    Matrix.single_mul_single_of_ne,
    Matrix.trace_add, Matrix.trace_smul, he, Ne.symm he]

theorem slaterOutput_trace {d : ℕ} (e : Edge d) : Matrix.trace (slaterOutput e) = 1 := by
  norm_num [slaterOutput, Matrix.trace_add, Matrix.trace_smul]

theorem antisymmetricChannel_slater_purity {d : ℕ} (e : Edge d) :
    purity (antisymmetricChannel d (pureDensity (coordinateSlater e))) = 1 / 2 := by
  rw [antisymmetricChannel_coordinateSlater, slaterOutput_purity]

theorem trace_square_kronecker {I J : Type*} [Fintype I] [Fintype J]
    (ρ : Matrix I I ℂ) (σ : Matrix J J ℂ) :
    Matrix.trace ((ρ ⊗ₖ σ) * (ρ ⊗ₖ σ)) =
      Matrix.trace (ρ * ρ) * Matrix.trace (σ * σ) := by
  rw [← Matrix.mul_kronecker_mul, Matrix.trace_kronecker]

theorem trace_square_im_zero {I : Type*} [Fintype I] (ρ : Matrix I I ℂ)
    (hρ : ρ.conjTranspose = ρ) : (Matrix.trace (ρ * ρ)).im = 0 := by
  have hs : star (Matrix.trace (ρ * ρ)) = Matrix.trace (ρ * ρ) := by
    rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, hρ]
  have hi := congrArg Complex.im hs
  simp only [Complex.star_def, Complex.conj_im] at hi
  linarith

theorem purity_kronecker {I J : Type*} [Fintype I] [Fintype J]
    (ρ : Matrix I I ℂ) (σ : Matrix J J ℂ)
    (hρ : ρ.conjTranspose = ρ) (hσ : σ.conjTranspose = σ) :
    purity (ρ ⊗ₖ σ) = purity ρ * purity σ := by
  simp only [purity, trace_square_kronecker, Complex.mul_re,
    trace_square_im_zero ρ hρ, trace_square_im_zero σ hσ, mul_zero, sub_zero]

theorem reducedLeft_kronecker {B E C F : Type*} [Fintype E] [Fintype F]
    (U : Matrix B E ℂ) (W : Matrix C F ℂ) :
    reducedLeft (U ⊗ₖ W) = reducedLeft U ⊗ₖ reducedLeft W := by
  ext ⟨b, c⟩ ⟨b', c'⟩
  simp only [reducedLeft, crossLeft, Matrix.kronecker_apply,
    Fintype.sum_prod_type, star_mul]
  rw [Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  apply Finset.sum_congr rfl
  intro f _
  ring

abbrev PhysicalPower (d : ℕ) : ℕ → Type
  | 0 => Unit
  | n + 1 => Fin d × PhysicalPower d n

instance physicalPowerFintype (d n : ℕ) : Fintype (PhysicalPower d n) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype Unit)
  | succ n ih =>
    letI := ih
    exact inferInstanceAs (Fintype (Fin d × PhysicalPower d n))

instance physicalPowerDecidableEq (d n : ℕ) : DecidableEq (PhysicalPower d n) := by
  induction n with
  | zero => exact inferInstanceAs (DecidableEq Unit)
  | succ n ih =>
    letI := ih
    exact inferInstanceAs (DecidableEq (Fin d × PhysicalPower d n))

def HasAntisymmetricSupport (d : ℕ) :
    (n : ℕ) → Matrix (PhysicalPower d n) (PhysicalPower d n) ℂ → Prop
  | 0, _ => True
  | n + 1, U =>
      (∀ a b r s, U (b, r) (a, s) = -U (a, r) (b, s)) ∧
        ∀ a b, HasAntisymmetricSupport d n (fun r s => U (a, r) (b, s))

theorem antisymmetricSupport_smul (d n : ℕ) (z : ℂ)
    (U : Matrix (PhysicalPower d n) (PhysicalPower d n) ℂ)
    (hU : HasAntisymmetricSupport d n U) : HasAntisymmetricSupport d n (z • U) := by
  induction n with
  | zero => trivial
  | succ n ih =>
    rcases hU with ⟨hs, ht⟩
    constructor
    · intro a b r s
      change z * U (b, r) (a, s) = -(z * U (a, r) (b, s))
      rw [hs, mul_neg]
    · intro a b
      exact ih (fun r s => U (a, r) (b, s)) (ht a b)

def slaterTensorAmplitude {d : ℕ} (e : Edge d) :
    (n : ℕ) → Matrix (PhysicalPower d n) (PhysicalPower d n) ℂ
  | 0 => fun _ _ => 1
  | n + 1 => slaterAmplitude e ⊗ₖ slaterTensorAmplitude e n

theorem slaterTensor_antisymmetricSupport {d : ℕ} (e : Edge d) (n : ℕ) :
    HasAntisymmetricSupport d n (slaterTensorAmplitude e n) := by
  induction n with
  | zero => trivial
  | succ n ih =>
    constructor
    · intro a b r s
      change wedgeInclusion d (b, a) e * slaterTensorAmplitude e n r s =
        -(wedgeInclusion d (a, b) e * slaterTensorAmplitude e n r s)
      rw [wedgeInclusion_swap, neg_mul]
    · intro a b
      exact antisymmetricSupport_smul d n (slaterAmplitude e a b)
        (slaterTensorAmplitude e n) ih

theorem slaterTensor_purity {d : ℕ} (e : Edge d) (n : ℕ) :
    purity (reducedLeft (slaterTensorAmplitude e n)) = (1 / 2 : ℝ) ^ n := by
  induction n with
  | zero =>
    change purity (reducedLeft (fun _ _ : Unit => (1 : ℂ))) = 1
    norm_num [purity, reducedLeft, crossLeft, Matrix.trace, Matrix.mul_apply]
  | succ n ih =>
    rw [slaterTensorAmplitude, reducedLeft_kronecker,
      purity_kronecker _ _ (reducedLeft_conjTranspose _) (reducedLeft_conjTranspose _),
      slaterAmplitude_reducedLeft, slaterOutput_purity, ih]
    simp [pow_succ, mul_comm]

theorem reducedLeft_trace_normSq {B E : Type*} [Fintype B] [Fintype E]
    (U : Matrix B E ℂ) :
    Matrix.trace (reducedLeft U) =
      (vectorNormSq (fun be : B × E => U be.1 be.2) : ℂ) := by
  have heq : reducedLeft U = partialTraceLeft (pureDensity (fun be : B × E => U be.1 be.2)) := by
    ext b c
    rfl
  rw [heq, partialTraceLeft_trace, pureDensity_trace]

theorem slaterTensor_trace {d : ℕ} (e : Edge d) (n : ℕ) :
    Matrix.trace (reducedLeft (slaterTensorAmplitude e n)) = 1 := by
  induction n with
  | zero =>
    change Matrix.trace (reducedLeft (fun _ _ : Unit => (1 : ℂ))) = 1
    norm_num [reducedLeft, crossLeft, Matrix.trace]
  | succ n ih =>
    rw [slaterTensorAmplitude, reducedLeft_kronecker, Matrix.trace_kronecker,
      slaterAmplitude_reducedLeft, slaterOutput_trace, ih]
    simp

theorem slaterTensor_normSq {d : ℕ} (e : Edge d) (n : ℕ) :
    vectorNormSq (fun be : PhysicalPower d n × PhysicalPower d n =>
      slaterTensorAmplitude e n be.1 be.2) = 1 := by
  have h := congrArg Complex.re (slaterTensor_trace e n)
  rw [reducedLeft_trace_normSq] at h
  simpa using h

theorem slaterTensor_physical_state {d : ℕ} (e : Edge d) (n : ℕ) :
    let u : PhysicalPower d n × PhysicalPower d n → ℂ :=
      fun be => slaterTensorAmplitude e n be.1 be.2
    (pureDensity u).PosSemidef ∧ Matrix.trace (pureDensity u) = 1 ∧
      purity (partialTraceLeft (pureDensity u)) = (1 / 2 : ℝ) ^ n := by
  dsimp only
  refine ⟨pureDensity_posSemidef _, ?_, ?_⟩
  · rw [pureDensity_trace, slaterTensor_normSq]
    norm_num
  · have heq : partialTraceLeft (pureDensity (fun be : PhysicalPower d n × PhysicalPower d n =>
        slaterTensorAmplitude e n be.1 be.2)) = reducedLeft (slaterTensorAmplitude e n) := by
      ext a b
      rfl
    rw [heq, slaterTensor_purity]

theorem antisymmetric_productSlater_attainment (d : ℕ) (hd : 2 ≤ d) (n : ℕ) :
    ∃ u : PhysicalPower d n × PhysicalPower d n → ℂ,
      vectorNormSq u = 1 ∧ HasAntisymmetricSupport d n (fun a b => u (a, b)) ∧
        purity (partialTraceLeft (pureDensity u)) = (1 / 2 : ℝ) ^ n := by
  have h₀ : 0 < d := lt_of_lt_of_le (by decide : 0 < 2) hd
  have h₁ : 1 < d := lt_of_lt_of_le (by decide : 1 < 2) hd
  let e : Edge d := ⟨(⟨0, h₀⟩, ⟨1, h₁⟩), by change (0 : ℕ) < 1; decide⟩
  refine ⟨fun be => slaterTensorAmplitude e n be.1 be.2, slaterTensor_normSq e n,
    slaterTensor_antisymmetricSupport e n, ?_⟩
  exact (slaterTensor_physical_state e n).2.2

theorem cross_product_trace_complement_swap {B E : Type*} [Fintype B] [Fintype E]
    (U V W Z : Matrix B E ℂ) :
    Matrix.trace (crossLeft U V * crossLeft W Z) =
      Matrix.trace (crossRight W V * crossRight U Z) := by
  rw [crossLeft_eq_mul, crossLeft_eq_mul, crossRight_eq_mul_transpose,
    crossRight_eq_mul_transpose, ← Matrix.transpose_mul, Matrix.trace_transpose]
  simpa only [Matrix.mul_assoc] using Matrix.trace_mul_cycle (U * V.conjTranspose) W Z.conjTranspose

theorem crossDensity_single {Y : Type*} [DecidableEq Y] (i j : Y) :
    crossDensity (Pi.single i 1) (Pi.single j 1) = (Matrix.single i j 1 : Matrix Y Y ℂ) := by
  ext k l
  by_cases hik : i = k <;> by_cases hjl : j = l <;>
    simp [crossDensity, Pi.single_apply, Matrix.single_apply, hik, hjl, eq_comm]

namespace Stinespring

variable {Y B E : Type*} [Fintype Y] [Fintype B] [Fintype E] [DecidableEq Y]

theorem amplitudes_single (N : Stinespring Y B E) (y : Y) :
    N.amplitudes (Pi.single y 1) = N.columnAmplitude y := by
  ext b e
  simp [amplitudes, columnAmplitude, Pi.single_apply, mul_ite]

theorem replicaKernel_entry (N : Stinespring Y B E) (i j k l : Y) :
    N.replicaKernel (i, j) (k, l) = Matrix.trace
      (N.apply (Matrix.single k i 1) * N.apply (Matrix.single l j 1)) := by
  rw [← crossDensity_single k i, ← crossDensity_single l j,
    apply_crossDensity, apply_crossDensity, amplitudes_single, amplitudes_single,
    amplitudes_single, amplitudes_single]
  rfl

theorem replicaKernel_hermitian (N : Stinespring Y B E) :
    N.replicaKernel.conjTranspose = N.replicaKernel := by
  ext ⟨i, j⟩ ⟨k, l⟩
  change star (Matrix.trace
    (crossLeft (N.columnAmplitude i) (N.columnAmplitude k) *
     crossLeft (N.columnAmplitude j) (N.columnAmplitude l))) = _
  rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul,
    crossLeft_conjTranspose, crossLeft_conjTranspose]
  exact Matrix.trace_mul_comm _ _

theorem replicaKernel_mul_swap (N : Stinespring Y B E) :
    N.replicaKernel * replicaSwap Y = N.replicaComplementKernel := by
  ext ⟨i, j⟩ ⟨k, l⟩
  simp only [Matrix.mul_apply, replicaSwap, mul_ite, mul_one, mul_zero]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  exact cross_product_trace_complement_swap _ _ _ _

end Stinespring

theorem antisymmetric_column_cross (d : ℕ) (e f : Edge d) :
    crossLeft ((antisymmetricStinespring d).columnAmplitude e)
      ((antisymmetricStinespring d).columnAmplitude f) =
    crossRight ((antisymmetricStinespring d).columnAmplitude e)
      ((antisymmetricStinespring d).columnAmplitude f) := by
  have h := antisymmetricChannel_eq_complement d
    (crossDensity (Pi.single e 1) (Pi.single f 1))
  change (antisymmetricStinespring d).apply _ = (antisymmetricStinespring d).complement _ at h
  rw [Stinespring.apply_crossDensity, Stinespring.complement_crossDensity,
    Stinespring.amplitudes_single, Stinespring.amplitudes_single] at h
  exact h

theorem antisymmetric_replicaKernel_mul_swap (d : ℕ) :
    (antisymmetricStinespring d).replicaKernel * replicaSwap (Edge d) =
      (antisymmetricStinespring d).replicaKernel := by
  rw [Stinespring.replicaKernel_mul_swap]
  ext ij kl
  simp only [Stinespring.replicaComplementKernel, Stinespring.replicaKernel,
    antisymmetric_column_cross]

theorem antisymmetric_replicaKernel_annihilates_difference (d : ℕ)
    (w : Edge d × Edge d → ℂ) :
    (antisymmetricStinespring d).replicaKernel.mulVec
      (w - (replicaSwap (Edge d)).mulVec w) = 0 := by
  rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, antisymmetric_replicaKernel_mul_swap, sub_self]

theorem antisymmetric_replicaKernel_physical (d : ℕ) :
    (antisymmetricStinespring d).replicaKernel =
      (pairWedgeInclusion d).conjTranspose * quadS13 d * pairWedgeInclusion d := by
  have hm : quadS13 d * pairWedgeInclusion d =
      (fun q ij => pairWedgeInclusion d (quadSwap13 q) ij) := by
    ext q ij
    exact quadPermMatrix_mul_matrix d _ _ q ij
  ext ⟨i, j⟩ ⟨k, l⟩
  rw [Matrix.mul_assoc, hm]
  change Matrix.trace
    (crossLeft ((antisymmetricStinespring d).columnAmplitude k)
      ((antisymmetricStinespring d).columnAmplitude i) *
     crossLeft ((antisymmetricStinespring d).columnAmplitude l)
      ((antisymmetricStinespring d).columnAmplitude j)) =
    ∑ q : Quad d, star (pairWedgeInclusion d q (i, j)) *
      pairWedgeInclusion d (quadSwap13 q) (k, l)
  simp only [Stinespring.replicaKernel, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    crossLeft, Stinespring.columnAmplitude, antisymmetricStinespring,
    pairWedgeInclusion, Matrix.kroneckerMap_apply, Matrix.conjTranspose_apply, quadSwap13,
    Fintype.sum_prod_type, star_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  conv_lhs =>
    enter [2, c]
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro c hc
  apply Finset.sum_congr rfl
  intro e he
  ring

theorem antisymmetric_replicaKernel_coset (d : ℕ) :
    (antisymmetricStinespring d).replicaKernel =
      (1 / 4 : ℂ) • (1 + replicaSwap (Edge d)) -
        (3 / 2 : ℂ) • exteriorReplicaProjector d := by
  have hcross := compressed_crossSwap_eq d
  have hC : (pairWedgeInclusion d).conjTranspose * sixCosetOperator d * pairWedgeInclusion d =
      1 + replicaSwap (Edge d) - (antisymmetricStinespring d).replicaKernel -
      (antisymmetricStinespring d).replicaKernel - (antisymmetricStinespring d).replicaKernel -
      (antisymmetricStinespring d).replicaKernel := by
    simp only [sixCosetOperator, Matrix.mul_add, Matrix.mul_sub, Matrix.add_mul,
      Matrix.sub_mul, Matrix.mul_one, pairWedgeInclusion_isometry,
      compressed_pairExchange, hcross.1, hcross.2.1, hcross.2.2,
      ← antisymmetric_replicaKernel_physical]
  have hA : exteriorReplicaProjector d = (1 / 6 : ℂ) •
      (1 + replicaSwap (Edge d) - (antisymmetricStinespring d).replicaKernel -
      (antisymmetricStinespring d).replicaKernel - (antisymmetricStinespring d).replicaKernel -
      (antisymmetricStinespring d).replicaKernel) := by
    simp only [exteriorReplicaProjector, fourAntisymmetrizer, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.mul_assoc, pairAntisymmetrizer_pairWedge,
      ]
    rw [← Matrix.mul_assoc, hC]
  rw [hA]
  ext ij kl
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  ring

theorem antisymmetric_replicaKernel_fourFormOmega {d : ℕ} (S : FourSet d) :
    (antisymmetricStinespring d).replicaKernel.mulVec (fourFormOmega S) =
      -fourFormOmega S := by
  rw [antisymmetric_replicaKernel_coset, Matrix.sub_mulVec, Matrix.smul_mulVec,
    Matrix.smul_mulVec, Matrix.add_mulVec, Matrix.one_mulVec,
    fourFormOmega_replicaSwap, exteriorReplicaProjector_fourFormOmega]
  ext ij
  simp only [Pi.sub_apply, Pi.smul_apply, Pi.add_apply, Pi.neg_apply, smul_eq_mul]
  ring

def d5FourFormColumns : Matrix (Edge 5 × Edge 5) (Fin 5) ℂ :=
  fun ij t => d5FourFormOmega t ij

theorem exteriorReplicaProjector_d5FourFormColumns :
    exteriorReplicaProjector 5 * d5FourFormColumns = d5FourFormColumns := by
  ext ij t
  change (exteriorReplicaProjector 5).mulVec (d5FourFormOmega t) ij = _
  exact congrFun (exteriorReplicaProjector_fourFormOmega (omittedFourSet t)) ij

def replicaVector {Y : Type*} (u : Y → ℂ) : Y × Y → ℂ :=
  fun ij => u ij.1 * u ij.2

theorem pureDensity_matrixUnits {Y : Type*} [Fintype Y] [DecidableEq Y] (u : Y → ℂ) :
    pureDensity u = ∑ i, ∑ j, (u i * star (u j)) • (Matrix.single i j 1 : Matrix Y Y ℂ) := by
  ext a b
  simp [pureDensity, crossDensity, Matrix.sum_apply, Matrix.smul_apply,
    Matrix.single_apply, smul_eq_mul, ite_mul, mul_ite, ite_and]

theorem matrixUnits_expansion {Y : Type*} [Fintype Y] [DecidableEq Y]
    (ρ : Matrix Y Y ℂ) :
    ρ = ∑ i, ∑ j, ρ i j • (Matrix.single i j 1 : Matrix Y Y ℂ) := by
  ext a b
  simp [Matrix.sum_apply, Matrix.smul_apply, Matrix.single_apply, smul_eq_mul,
    ite_mul, mul_ite, ite_and]

def companionCoefficient {X Y : Type*} (Ψ : X × Y → ℂ) : Matrix Y X ℂ :=
  fun y x => Ψ (x, y)

def companionReplicaEquiv (X Y : Type*) :
    (((X × Y) × (X × Y)) × ((X × Y) × (X × Y))) ≃
      ((Y × Y) × ((Y × Y) × ((X × X) × (X × X)))) where
  toFun := fun ⟨⟨⟨i, u⟩, ⟨j, v⟩⟩, ⟨⟨k, w⟩, ⟨l, z⟩⟩⟩ =>
    ((u, v), ((w, z), ((k, l), (i, j))))
  invFun := fun ⟨⟨u, v⟩, ⟨⟨w, z⟩, ⟨⟨k, l⟩, ⟨i, j⟩⟩⟩⟩ =>
    (((i, u), (j, v)), ((k, w), (l, z)))
  left_inv := by rintro ⟨⟨⟨i, u⟩, ⟨j, v⟩⟩, ⟨⟨k, w⟩, ⟨l, z⟩⟩⟩; rfl
  right_inv := by rintro ⟨⟨u, v⟩, ⟨⟨w, z⟩, ⟨⟨k, l⟩, ⟨i, j⟩⟩⟩⟩; rfl

theorem crossLeft_kronecker {A B E F : Type*} [Fintype E] [Fintype F]
    (U W : Matrix A E ℂ) (V Z : Matrix B F ℂ) :
    crossLeft (U ⊗ₖ V) (W ⊗ₖ Z) = crossLeft U W ⊗ₖ crossLeft V Z := by
  ext ⟨a, b⟩ ⟨c, d⟩
  simp only [crossLeft, Matrix.kroneckerMap_apply, Fintype.sum_prod_type, star_mul]
  simp only [Finset.sum_mul]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  apply Finset.sum_congr rfl
  intro f hf
  ring

namespace Stinespring

theorem replicaKernel_swap_both {Y B E : Type*}
    [Fintype Y] [Fintype B] [Fintype E] [DecidableEq Y]
    (N : Stinespring Y B E) (i j k l : Y) :
    N.replicaKernel (j, i) (l, k) = N.replicaKernel (i, j) (k, l) :=
  Matrix.trace_mul_comm _ _

theorem tensor_replicaKernel {X Y A B F E : Type*}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B] [Fintype F] [Fintype E]
    [DecidableEq X] [DecidableEq Y]
    (M : Stinespring X A F) (N : Stinespring Y B E)
    (x x' z z' : X) (y y' w w' : Y) :
    (M.tensor N).replicaKernel ((x, y), (x', y')) ((z, w), (z', w')) =
      M.replicaKernel (x, x') (z, z') * N.replicaKernel (y, y') (w, w') := by
  simp only [replicaKernel, tensor_columnAmplitude, crossLeft_kronecker,
    ← Matrix.mul_kronecker_mul, Matrix.trace_kronecker]

theorem pure_output_trace_eq_replica {Y B E : Type*}
    [Fintype Y] [Fintype B] [Fintype E] [DecidableEq Y]
    (N : Stinespring Y B E) (u : Y → ℂ) :
    Matrix.trace (N.apply (pureDensity u) * N.apply (pureDensity u)) =
      dotProduct (star (replicaVector u)) (N.replicaKernel.mulVec (replicaVector u)) := by
  rw [pureDensity_matrixUnits]
  simp only [EnsemblePhase.apply_sum, EnsemblePhase.apply_smul,
    Finset.sum_mul, Finset.mul_sum, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, Matrix.trace_sum, Matrix.trace_smul, smul_eq_mul,
    ← replicaKernel_entry]
  simp only [dotProduct, Matrix.mulVec, replicaVector, Pi.star_apply,
    Fintype.sum_prod_type, star_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  conv_lhs =>
    enter [2, k]
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro l hl
  rw [replicaKernel_swap_both]
  ring

theorem pure_output_purity_eq_replica {Y B E : Type*}
    [Fintype Y] [Fintype B] [Fintype E] [DecidableEq Y]
    (N : Stinespring Y B E) (u : Y → ℂ) :
    purity (N.apply (pureDensity u)) =
      (dotProduct (star (replicaVector u)) (N.replicaKernel.mulVec (replicaVector u))).re := by
  exact congrArg Complex.re (pure_output_trace_eq_replica N u)

theorem output_trace_eq_replicaMatrix {Y B E : Type*}
    [Fintype Y] [Fintype B] [Fintype E] [DecidableEq Y]
    (N : Stinespring Y B E) (ρ : Matrix Y Y ℂ) :
    Matrix.trace (N.apply ρ * N.apply ρ) = Matrix.trace (N.replicaKernel * (ρ ⊗ₖ ρ)) := by
  have happly : N.apply ρ = ∑ i, ∑ j, ρ i j • N.apply (Matrix.single i j 1) := by
    conv_lhs => rw [matrixUnits_expansion ρ]
    simp only [EnsemblePhase.apply_sum, EnsemblePhase.apply_smul]
  rw [happly]
  simp only [Finset.sum_mul, Finset.mul_sum, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, Matrix.trace_sum, Matrix.trace_smul, smul_eq_mul, ← replicaKernel_entry]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.kroneckerMap_apply,
    Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  conv_lhs =>
    enter [2, k]
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro l hl
  rw [replicaKernel_swap_both]
  ring

theorem tensor_pure_trace_companion {X Y A B F E : Type*}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B] [Fintype F] [Fintype E]
    [DecidableEq X] [DecidableEq Y]
    (M : Stinespring X A F) (N : Stinespring Y B E) (Ψ : X × Y → ℂ) :
    Matrix.trace ((M.tensor N).apply (pureDensity Ψ) * (M.tensor N).apply (pureDensity Ψ)) =
      Matrix.trace (N.replicaKernel *
        (companionCoefficient Ψ ⊗ₖ companionCoefficient Ψ) * M.replicaKernel.transpose *
        (companionCoefficient Ψ ⊗ₖ companionCoefficient Ψ).conjTranspose) := by
  let C := companionCoefficient Ψ ⊗ₖ companionCoefficient Ψ
  let f : (((X × Y) × (X × Y)) × ((X × Y) × (X × Y))) → ℂ := fun pq =>
    star (replicaVector Ψ pq.1) *
      ((M.replicaKernel (pq.1.1.1, pq.1.2.1) (pq.2.1.1, pq.2.2.1) *
        N.replicaKernel (pq.1.1.2, pq.1.2.2) (pq.2.1.2, pq.2.2.2)) *
        replicaVector Ψ pq.2)
  let g : ((Y × Y) × ((Y × Y) × ((X × X) × (X × X)))) → ℂ := fun t =>
    N.replicaKernel t.1 t.2.1 *
      (C t.2.1 t.2.2.1 * (M.replicaKernel t.2.2.2 t.2.2.1 * star (C t.1 t.2.2.2)))
  calc
    _ = ∑ p, f p := by
      rw [pure_output_trace_eq_replica]
      simp only [f, Fintype.sum_prod_type, dotProduct, Matrix.mulVec, Pi.star_apply,
        tensor_replicaKernel, Finset.mul_sum]
    _ = ∑ t, g t := by
      apply Fintype.sum_equiv (companionReplicaEquiv X Y) f g
      rintro ⟨⟨⟨i, u⟩, ⟨j, v⟩⟩, ⟨⟨k, w⟩, ⟨l, z⟩⟩⟩
      change star (Ψ (i, u) * Ψ (j, v)) *
        ((M.replicaKernel (i, j) (k, l) * N.replicaKernel (u, v) (w, z)) *
          (Ψ (k, w) * Ψ (l, z))) =
        N.replicaKernel (u, v) (w, z) *
          ((Ψ (k, w) * Ψ (l, z)) *
            (M.replicaKernel (i, j) (k, l) * star (Ψ (i, u) * Ψ (j, v))))
      simp only [star_mul]
      ring
    _ = _ := by
      rw [Matrix.mul_assoc, Matrix.mul_assoc]
      simp only [g, C, Matrix.trace, Matrix.diag, Matrix.mul_apply,
        Matrix.transpose_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type,
        Finset.mul_sum]

end Stinespring

theorem replicaVector_normSq {Y : Type*} [Fintype Y] (u : Y → ℂ) :
    vectorNormSq (replicaVector u) = vectorNormSq u ^ 2 := by
  simp [vectorNormSq, replicaVector, Complex.normSq_mul, Fintype.sum_prod_type,
    pow_two, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  exact mul_comm _ _

theorem replicaVector_inner {Y : Type*} [Fintype Y] (u : Y → ℂ) :
    dotProduct (star (replicaVector u)) (replicaVector u) = (vectorNormSq u : ℂ) ^ 2 := by
  have h : dotProduct (star (replicaVector u)) (replicaVector u) =
      (vectorNormSq (replicaVector u) : ℂ) := by
    simpa [pureDensity, crossDensity, Matrix.trace, Matrix.diag, dotProduct,
      Pi.star_apply, mul_comm] using pureDensity_trace (replicaVector u)
  rw [h, replicaVector_normSq, Complex.ofReal_pow]

theorem replicaVector_replicaSwap {Y : Type*} [Fintype Y] [DecidableEq Y] (u : Y → ℂ) :
    (replicaSwap Y).mulVec (replicaVector u) = replicaVector u := by
  ext ij
  rw [replicaSwap_mulVec]
  simp [replicaVector, mul_comm]

theorem antisymmetric_pure_trace_coset (d : ℕ) (u : Edge d → ℂ) :
    Matrix.trace ((antisymmetricStinespring d).apply (pureDensity u) *
      (antisymmetricStinespring d).apply (pureDensity u)) =
    (1 / 2 : ℂ) * (vectorNormSq u : ℂ) ^ 2 - (3 / 2 : ℂ) *
      dotProduct (star (replicaVector u))
        ((exteriorReplicaProjector d).mulVec (replicaVector u)) := by
  rw [Stinespring.pure_output_trace_eq_replica, antisymmetric_replicaKernel_coset,
    Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec,
    Matrix.add_mulVec, Matrix.one_mulVec, replicaVector_replicaSwap,
    dotProduct_sub, dotProduct_smul, dotProduct_smul, dotProduct_add,
    replicaVector_inner]
  ring

theorem antisymmetric_oneCopy_purity_le_half (d : ℕ) (u : Edge d → ℂ)
    (hu : vectorNormSq u = 1) :
    purity ((antisymmetricStinespring d).apply (pureDensity u)) ≤ 1 / 2 := by
  have hp := (Complex.nonneg_iff.mp
    ((exteriorReplicaProjector_posSemidef d).dotProduct_mulVec_nonneg (replicaVector u))).1
  have ht := congrArg Complex.re (antisymmetric_pure_trace_coset d u)
  change purity ((antisymmetricStinespring d).apply (pureDensity u)) = _ at ht
  norm_num [hu, Complex.sub_re, Complex.mul_re] at ht
  linarith

theorem d5FourFormColumns_gram :
    d5FourFormColumns.conjTranspose * d5FourFormColumns =
      (6 : ℂ) • (1 : Matrix (Fin 5) (Fin 5) ℂ) := by
  ext t u
  change (∑ ij : Edge 5 × Edge 5, star (d5FourFormOmega t ij) * d5FourFormOmega u ij) =
    (6 : ℂ) * (if t = u then 1 else 0)
  rw [D5SupportFactor.d5FourFormOmega_gram]
  split_ifs <;> norm_num

theorem d5FourFormColumns_outer_sum :
    d5FourFormColumns * d5FourFormColumns.conjTranspose =
      ∑ t : Fin 5, pureDensity (d5FourFormOmega t) := by
  ext ij kl
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply, d5FourFormColumns,
    pureDensity, crossDensity, Matrix.sum_apply]

theorem exteriorReplicaProjector_d5_eq_fourFormSum :
    exteriorReplicaProjector 5 = (1 / 6 : ℂ) •
      ∑ t : Fin 5, pureDensity (d5FourFormOmega t) := by
  have h := orthogonalProjector_eq_six_scaled_columns
    (exteriorReplicaProjector 5) d5FourFormColumns
    (exteriorReplicaProjector_hermitian 5) (exteriorReplicaProjector_idempotent 5)
    exteriorReplicaProjector_d5FourFormColumns d5FourFormColumns_gram
    (by simpa using exteriorReplicaProjector_trace_d5)
  rwa [d5FourFormColumns_outer_sum] at h

theorem antisymmetric_replicaKernel_d5_full :
    (antisymmetricStinespring 5).replicaKernel = (1 / 4 : ℂ) •
      (1 + replicaSwap (Edge 5) - ∑ t : Fin 5, pureDensity (d5FourFormOmega t)) := by
  rw [antisymmetric_replicaKernel_coset, exteriorReplicaProjector_d5_eq_fourFormSum]
  ext ij kl
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  ring

def d4FourFormOmega : Edge 4 × Edge 4 → ℂ := fourFormOmega ⟨Finset.univ, by simp⟩

def d4FourFormColumns : Matrix (Edge 4 × Edge 4) Unit ℂ := fun ij _ => d4FourFormOmega ij

theorem d4FourFormColumns_gram :
    d4FourFormColumns.conjTranspose * d4FourFormColumns =
      (6 : ℂ) • (1 : Matrix Unit Unit ℂ) := by
  ext t u
  change (∑ ij : Edge 4 × Edge 4, star (d4FourFormOmega ij) * d4FourFormOmega ij) =
    (6 : ℂ) * (if t = u then 1 else 0)
  rw [if_pos (Subsingleton.elim t u), mul_one]
  have hs : (∑ ij : Edge 4 × Edge 4, star (d4FourFormOmega ij) * d4FourFormOmega ij) =
      (vectorNormSq d4FourFormOmega : ℂ) := by
    simp [vectorNormSq, mul_comm, Complex.mul_conj]
  rw [hs]
  change (vectorNormSq (fourFormOmega ⟨Finset.univ, by simp⟩) : ℂ) = 6
  rw [D5SupportFactor.fourFormOmega_normSq]
  norm_num

theorem exteriorReplicaProjector_d4FourFormColumns :
    exteriorReplicaProjector 4 * d4FourFormColumns = d4FourFormColumns := by
  ext ij t
  change (exteriorReplicaProjector 4).mulVec d4FourFormOmega ij = _
  exact congrFun (exteriorReplicaProjector_fourFormOmega ⟨Finset.univ, by simp⟩) ij

theorem exteriorReplicaProjector_d4_eq_fourForm :
    exteriorReplicaProjector 4 = (1 / 6 : ℂ) • pureDensity d4FourFormOmega := by
  have h := orthogonalProjector_eq_six_scaled_columns
    (exteriorReplicaProjector 4) d4FourFormColumns
    (exteriorReplicaProjector_hermitian 4) (exteriorReplicaProjector_idempotent 4)
    exteriorReplicaProjector_d4FourFormColumns d4FourFormColumns_gram
    (by simpa using exteriorReplicaProjector_trace_d4)
  have heq : d4FourFormColumns * d4FourFormColumns.conjTranspose =
      pureDensity d4FourFormOmega := by
    ext ij kl
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, d4FourFormColumns,
      pureDensity, crossDensity]
  rwa [heq] at h

theorem antisymmetric_replicaKernel_d4_full :
    (antisymmetricStinespring 4).replicaKernel = (1 / 4 : ℂ) •
      (1 + replicaSwap (Edge 4) - pureDensity d4FourFormOmega) := by
  rw [antisymmetric_replicaKernel_coset, exteriorReplicaProjector_d4_eq_fourForm]
  ext ij kl
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  ring

theorem trace_kernel_pureDensity {Y : Type*} [Fintype Y]
    (K : Matrix Y Y ℂ) (v : Y → ℂ) :
    Matrix.trace (K * pureDensity v) = dotProduct (star v) (K.mulVec v) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, pureDensity, crossDensity,
    dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem replicaSwap_transpose {Y : Type*} [DecidableEq Y] :
    (replicaSwap Y).transpose = replicaSwap Y := by
  ext ⟨i, j⟩ ⟨k, l⟩
  simp [replicaSwap, Matrix.transpose_apply, Prod.ext_iff, eq_comm, and_comm]

theorem replicaSwap_mul_matrix {Y Z : Type*} [Fintype Y] [DecidableEq Y]
    (M : Matrix (Y × Y) Z ℂ) (ij : Y × Y) (z : Z) :
    (replicaSwap Y * M) ij z = M (ij.2, ij.1) z := by
  have heq (kl : Y × Y) : ij = (kl.2, kl.1) ↔ kl = (ij.2, ij.1) := by
    simp [Prod.ext_iff, eq_comm, and_comm]
  simp [replicaSwap, Matrix.mul_apply, heq, ite_mul]

theorem matrix_mul_replicaSwap {Y Z : Type*} [Fintype Y] [DecidableEq Y]
    (M : Matrix Z (Y × Y) ℂ) (z : Z) (ij : Y × Y) :
    (M * replicaSwap Y) z ij = M z (ij.2, ij.1) := by
  simp [replicaSwap, Matrix.mul_apply, mul_ite]

theorem kronecker_replicaSwap {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y] (A : Matrix Y X ℂ) :
    (A ⊗ₖ A) * replicaSwap X = replicaSwap Y * (A ⊗ₖ A) := by
  ext uv ij
  rw [matrix_mul_replicaSwap, replicaSwap_mul_matrix]
  simp only [Matrix.kroneckerMap_apply]
  ring

theorem kronecker_mulVec_matrix {X Y : Type*} [Fintype X]
    (A : Matrix Y X ℂ) (B : Matrix X X ℂ) :
    (A ⊗ₖ A).mulVec (fun ij : X × X => B ij.1 ij.2) =
      (fun uv : Y × Y => (A * B * A.transpose) uv.1 uv.2) := by
  ext ⟨u, v⟩
  simp only [Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.kroneckerMap_apply, Fintype.sum_prod_type, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem fourFormOmega_star {d : ℕ} (S : FourSet d) (ij : Edge d × Edge d) :
    star (fourFormOmega S ij) = fourFormOmega S ij := by
  simp [fourFormOmega, Pi.single_apply]

theorem pureDensity_transpose_of_star_eq {Y : Type*} (v : Y → ℂ)
    (hv : ∀ i, star (v i) = v i) : (pureDensity v).transpose = pureDensity v := by
  ext i j
  simp [Matrix.transpose_apply, pureDensity, crossDensity, hv, mul_comm]

def companionMarginal {X Y : Type*} [Fintype X] (Ψ : X × Y → ℂ) : Matrix Y Y ℂ :=
  reducedLeft (companionCoefficient Ψ)

def companionCorrection {X Y B E : Type*} [Fintype X] [Fintype Y]
    [Fintype B] [Fintype E] [DecidableEq Y]
    (N : Stinespring Y B E) (A : Matrix Y X ℂ) (D : Matrix X X ℂ) : ℂ :=
  let ζ : Y × Y → ℂ := fun uv => (A * D * A.transpose) uv.1 uv.2
  dotProduct (star ζ) (N.replicaKernel.mulVec ζ)

namespace Stinespring

theorem replicaComplementKernel_entry {Y B E : Type*}
    [Fintype Y] [Fintype B] [Fintype E] [DecidableEq Y]
    (N : Stinespring Y B E) (i j k l : Y) :
    N.replicaComplementKernel (i, j) (k, l) = Matrix.trace
      (N.complement (Matrix.single k i 1) * N.complement (Matrix.single l j 1)) := by
  rw [← crossDensity_single k i, ← crossDensity_single l j, complement_crossDensity,
    complement_crossDensity, amplitudes_single, amplitudes_single, amplitudes_single,
    amplitudes_single]
  rfl

theorem replicaComplementKernel_swap_both {Y B E : Type*}
    [Fintype Y] [Fintype B] [Fintype E] [DecidableEq Y]
    (N : Stinespring Y B E) (i j k l : Y) :
    N.replicaComplementKernel (j, i) (l, k) = N.replicaComplementKernel (i, j) (k, l) :=
  Matrix.trace_mul_comm _ _

theorem complement_trace_eq_replicaMatrix {Y B E : Type*}
    [Fintype Y] [Fintype B] [Fintype E] [DecidableEq Y]
    (N : Stinespring Y B E) (ρ : Matrix Y Y ℂ) :
    Matrix.trace (N.complement ρ * N.complement ρ) =
      Matrix.trace (N.replicaComplementKernel * (ρ ⊗ₖ ρ)) := by
  have happly : N.complement ρ = ∑ i, ∑ j, ρ i j • N.complement (Matrix.single i j 1) := by
    conv_lhs => rw [matrixUnits_expansion ρ]
    simp only [EnsemblePhase.complement_sum, EnsemblePhase.complement_smul]
  rw [happly]
  simp only [Finset.sum_mul, Finset.mul_sum, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, Matrix.trace_sum, Matrix.trace_smul, smul_eq_mul, ← replicaComplementKernel_entry]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.kroneckerMap_apply,
    Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  conv_lhs =>
    enter [2, k]
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro l hl
  rw [replicaComplementKernel_swap_both]
  ring

theorem companion_identity_trace {X Y B E : Type*} [Fintype X] [Fintype Y]
    [Fintype B] [Fintype E] [DecidableEq Y]
    (N : Stinespring Y B E) (A : Matrix Y X ℂ) :
    Matrix.trace (N.replicaKernel * (A ⊗ₖ A) * (A ⊗ₖ A).conjTranspose) =
      Matrix.trace (N.apply (reducedLeft A) * N.apply (reducedLeft A)) := by
  rw [output_trace_eq_replicaMatrix, Matrix.mul_assoc, Matrix.conjTranspose_kronecker,
    ← Matrix.mul_kronecker_mul]
  simp only [reducedLeft, crossLeft_eq_mul]

theorem companion_swap_trace {X Y B E : Type*} [Fintype X] [Fintype Y]
    [Fintype B] [Fintype E] [DecidableEq X] [DecidableEq Y]
    (N : Stinespring Y B E) (A : Matrix Y X ℂ) :
    Matrix.trace (N.replicaKernel * (A ⊗ₖ A) * replicaSwap X * (A ⊗ₖ A).conjTranspose) =
      Matrix.trace (N.complement (reducedLeft A) * N.complement (reducedLeft A)) := by
  calc
    _ = Matrix.trace (N.replicaKernel * ((A ⊗ₖ A) * replicaSwap X) *
        (A ⊗ₖ A).conjTranspose) := by simp only [Matrix.mul_assoc]
    _ = Matrix.trace ((N.replicaKernel * replicaSwap Y) *
        ((A ⊗ₖ A) * (A ⊗ₖ A).conjTranspose)) := by
      rw [kronecker_replicaSwap]
      simp only [Matrix.mul_assoc]
    _ = _ := by
      rw [replicaKernel_mul_swap, Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
        complement_trace_eq_replicaMatrix]
      simp only [reducedLeft, crossLeft_eq_mul]

theorem companion_correction_trace {X Y B E : Type*} [Fintype X] [Fintype Y]
    [Fintype B] [Fintype E] [DecidableEq Y]
    (N : Stinespring Y B E) (A : Matrix Y X ℂ) (D : Matrix X X ℂ) :
    Matrix.trace (N.replicaKernel * (A ⊗ₖ A) * pureDensity (fun ij : X × X => D ij.1 ij.2) *
      (A ⊗ₖ A).conjTranspose) = companionCorrection N A D := by
  rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (A ⊗ₖ A)]
  have hs := sandwich_crossDensity (A ⊗ₖ A) (fun ij : X × X => D ij.1 ij.2)
    (fun ij : X × X => D ij.1 ij.2)
  change (A ⊗ₖ A) * pureDensity (fun ij : X × X => D ij.1 ij.2) * (A ⊗ₖ A).conjTranspose = _ at hs
  rw [hs]
  change Matrix.trace (N.replicaKernel * pureDensity
    ((A ⊗ₖ A).mulVec (fun ij : X × X => D ij.1 ij.2))) = _
  rw [trace_kernel_pureDensity, kronecker_mulVec_matrix]
  rfl

end Stinespring

def d4FourFormMatrix : Matrix (Edge 4) (Edge 4) ℂ :=
  fourFormMatrix ⟨Finset.univ, by simp⟩

theorem antisymmetric_d5_companion_trace {Y B E : Type*}
    [Fintype Y] [Fintype B] [Fintype E] [DecidableEq Y]
    (N : Stinespring Y B E) (Ψ : Edge 5 × Y → ℂ) :
    Matrix.trace (((antisymmetricStinespring 5).tensor N).apply (pureDensity Ψ) *
      ((antisymmetricStinespring 5).tensor N).apply (pureDensity Ψ)) =
      (1 / 4 : ℂ) *
        (Matrix.trace (N.apply (companionMarginal Ψ) * N.apply (companionMarginal Ψ)) +
         Matrix.trace (N.complement (companionMarginal Ψ) * N.complement (companionMarginal Ψ)) -
         ∑ t : Fin 5, companionCorrection N (companionCoefficient Ψ) (d5FourFormMatrix t)) := by
  let A := companionCoefficient Ψ
  let C := A ⊗ₖ A
  have hr (t : Fin 5) : (pureDensity (d5FourFormOmega t)).transpose =
      pureDensity (d5FourFormOmega t) :=
    pureDensity_transpose_of_star_eq _ (fourFormOmega_star (omittedFourSet t))
  have hc (t : Fin 5) : Matrix.trace
      (N.replicaKernel * C * pureDensity (d5FourFormOmega t) * C.conjTranspose) =
      companionCorrection N A (d5FourFormMatrix t) := by
    exact N.companion_correction_trace A (d5FourFormMatrix t)
  rw [Stinespring.tensor_pure_trace_companion, antisymmetric_replicaKernel_d5_full,
    Matrix.transpose_smul, Matrix.transpose_sub, Matrix.transpose_add,
    Matrix.transpose_one, replicaSwap_transpose, Matrix.transpose_sum]
  simp only [hr, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.mul_sub,
    Matrix.add_mul, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_sum, Matrix.sum_mul,
    Matrix.trace_smul, Matrix.trace_add, Matrix.trace_sub, Matrix.trace_sum, smul_eq_mul]
  change (1 / 4 : ℂ) *
    (Matrix.trace (N.replicaKernel * C * C.conjTranspose) +
      Matrix.trace (N.replicaKernel * C * replicaSwap (Edge 5) * C.conjTranspose) -
      ∑ t : Fin 5, Matrix.trace (N.replicaKernel * C * pureDensity (d5FourFormOmega t) *
        C.conjTranspose)) = _
  simp only [C, hc, Stinespring.companion_identity_trace, Stinespring.companion_swap_trace]
  rfl

theorem antisymmetric_d4_companion_trace {Y B E : Type*}
    [Fintype Y] [Fintype B] [Fintype E] [DecidableEq Y]
    (N : Stinespring Y B E) (Ψ : Edge 4 × Y → ℂ) :
    Matrix.trace (((antisymmetricStinespring 4).tensor N).apply (pureDensity Ψ) *
      ((antisymmetricStinespring 4).tensor N).apply (pureDensity Ψ)) =
      (1 / 4 : ℂ) *
        (Matrix.trace (N.apply (companionMarginal Ψ) * N.apply (companionMarginal Ψ)) +
         Matrix.trace (N.complement (companionMarginal Ψ) * N.complement (companionMarginal Ψ)) -
         companionCorrection N (companionCoefficient Ψ) d4FourFormMatrix) := by
  have hr : (pureDensity d4FourFormOmega).transpose = pureDensity d4FourFormOmega :=
    pureDensity_transpose_of_star_eq _ (fourFormOmega_star ⟨Finset.univ, by simp⟩)
  have hc : Matrix.trace (N.replicaKernel * (companionCoefficient Ψ ⊗ₖ companionCoefficient Ψ) *
      pureDensity d4FourFormOmega * (companionCoefficient Ψ ⊗ₖ companionCoefficient Ψ).conjTranspose) =
      companionCorrection N (companionCoefficient Ψ) d4FourFormMatrix :=
    N.companion_correction_trace _ d4FourFormMatrix
  rw [Stinespring.tensor_pure_trace_companion, antisymmetric_replicaKernel_d4_full,
    Matrix.transpose_smul, Matrix.transpose_sub, Matrix.transpose_add,
    Matrix.transpose_one, replicaSwap_transpose, hr]
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.mul_sub,
    Matrix.add_mul, Matrix.sub_mul, Matrix.mul_one, Matrix.trace_smul,
    Matrix.trace_add, Matrix.trace_sub, smul_eq_mul, hc,
    Stinespring.companion_identity_trace, Stinespring.companion_swap_trace]
  rfl

theorem antisymmetric_d5_companion_purity {Y B E : Type*}
    [Fintype Y] [Fintype B] [Fintype E] [DecidableEq Y]
    (N : Stinespring Y B E) (Ψ : Edge 5 × Y → ℂ) :
    purity (((antisymmetricStinespring 5).tensor N).apply (pureDensity Ψ)) =
      (purity (N.apply (companionMarginal Ψ)) + purity (N.complement (companionMarginal Ψ)) -
        ∑ t : Fin 5, (companionCorrection N (companionCoefficient Ψ) (d5FourFormMatrix t)).re) / 4 := by
  have h := congrArg Complex.re (antisymmetric_d5_companion_trace N Ψ)
  norm_num [Complex.mul_re, Complex.sub_re, Complex.add_re, map_sum, purity] at h
  unfold purity
  convert h using 1 <;> ring

theorem antisymmetric_d4_companion_purity {Y B E : Type*}
    [Fintype Y] [Fintype B] [Fintype E] [DecidableEq Y]
    (N : Stinespring Y B E) (Ψ : Edge 4 × Y → ℂ) :
    purity (((antisymmetricStinespring 4).tensor N).apply (pureDensity Ψ)) =
      (purity (N.apply (companionMarginal Ψ)) + purity (N.complement (companionMarginal Ψ)) -
        (companionCorrection N (companionCoefficient Ψ) d4FourFormMatrix).re) / 4 := by
  have h := congrArg Complex.re (antisymmetric_d4_companion_trace N Ψ)
  norm_num [Complex.mul_re, Complex.sub_re, Complex.add_re, purity] at h
  unfold purity
  convert h using 1 <;> ring

theorem companionCoefficient_hsNormSq {X Y : Type*} [Fintype X] [Fintype Y]
    (Ψ : X × Y → ℂ) : hsNormSq (companionCoefficient Ψ) = vectorNormSq Ψ := by
  simp only [hsNormSq, companionCoefficient, vectorNormSq, Fintype.sum_prod_type,
    Complex.sq_norm]
  rw [Finset.sum_comm]

theorem companion_marginal_purity_bound {X Y B E : Type*} [Fintype X] [Fintype Y]
    [Fintype B] [Fintype E] [DecidableEq Y]
    (N : Stinespring Y B E) (β : ℝ)
    (hbound : ∀ u, vectorNormSq u = 1 → purity (N.apply (pureDensity u)) ≤ β)
    (Ψ : X × Y → ℂ) (hΨ : vectorNormSq Ψ = 1) :
    purity (N.apply (companionMarginal Ψ)) + purity (N.complement (companionMarginal Ψ)) ≤
      β * (1 + purity (companionMarginal Ψ)) := by
  exact MixedPurity.actual_purification_purity N β hbound (companionCoefficient Ψ)
    (by rw [companionCoefficient_hsNormSq, hΨ])

theorem companion_actual_d5_exterior_nuclear_bound {Y : Type*} [Fintype Y] [DecidableEq Y]
    (Ψ : Edge 5 × Y → ℂ) (hΨ : vectorNormSq Ψ = 1) :
    (∑ t : Fin 5, SchattenSupport.schattenOne (ExteriorSupport.orderedExterior
      (companionCoefficient Ψ * d5FourFormMatrix t * (companionCoefficient Ψ).transpose))) ≤
      1 - purity (companionMarginal Ψ) := by
  exact D5NuclearControl.actual_d5_exterior_nuclear_control (companionCoefficient Ψ)
    (by rw [companionCoefficient_hsNormSq, hΨ])

theorem normalized_coefficient_purity_le_one {X Y : Type*} [Fintype X] [Fintype Y]
    (A : Matrix Y X ℂ) (hA : hsNormSq A = 1) : purity (reducedLeft A) ≤ 1 := by
  have hn := hsNormSq_nonneg (ExteriorSupport.orderedExterior A)
  rw [ExteriorSupport.orderedExterior_hsNormSq_of_normalized A hA] at hn
  linarith

theorem actual_d4_exterior_nuclear_control {Y : Type*} [Fintype Y] [DecidableEq Y]
    (A : Matrix Y (Edge 4) ℂ) (hA : hsNormSq A = 1) :
    SchattenSupport.schattenOne (ExteriorSupport.orderedExterior
      (A * d4FourFormMatrix * A.transpose)) ≤ 1 - purity (reducedLeft A) := by
  let S : FourSet 4 := ⟨Finset.univ, by simp⟩
  let W := RealSymmetricFactor.covarianceFactor (D5SupportFactor.realFourFormMatrix S)
    (D5SupportFactor.realFourFormMatrix_hermitian S)
  have hcov : W * W.transpose = d4FourFormMatrix := by
    dsimp only [W]
    rw [RealSymmetricFactor.covarianceFactor_covariance,
      D5SupportFactor.complexify_realFourFormMatrix]
    rfl
  have hsupport : RealSymmetricFactor.complexify (D5SupportFactor.fourSupportMatrix S) =
      (1 : Matrix (Edge 4) (Edge 4) ℂ) := by
    rw [D5NuclearControl.fourSupportMatrix_diagonal, RealSymmetricFactor.complexify_diagonal]
    ext e f
    simp [S, Matrix.diagonal_apply, Matrix.one_apply]
  have hgram : W * W.conjTranspose = (1 : Matrix (Edge 4) (Edge 4) ℂ) := by
    dsimp only [W]
    rw [RealSymmetricFactor.covarianceFactor_gram_of_cube _ _
      (D5SupportFactor.realFourFormMatrix_cube S), D5SupportFactor.realFourFormMatrix_square,
      hsupport]
  have hn := ExteriorSchatten.exterior_covariance_support A W d4FourFormMatrix
    (1 : Matrix (Edge 4) (Edge 4) ℂ) hcov hgram (by simp) (by simp)
  simp only [Matrix.mul_one, ExteriorSupport.orderedExterior_hsNormSq_of_normalized A hA] at hn
  have hp := normalized_coefficient_purity_le_one A hA
  linarith

theorem companion_actual_d4_exterior_nuclear_bound {Y : Type*} [Fintype Y] [DecidableEq Y]
    (Ψ : Edge 4 × Y → ℂ) (hΨ : vectorNormSq Ψ = 1) :
    SchattenSupport.schattenOne (ExteriorSupport.orderedExterior
      (companionCoefficient Ψ * d4FourFormMatrix * (companionCoefficient Ψ).transpose)) ≤
      1 - purity (companionMarginal Ψ) := by
  exact actual_d4_exterior_nuclear_control (companionCoefficient Ψ)
    (by rw [companionCoefficient_hsNormSq, hΨ])

theorem companion_fourForm_symmetric {Y : Type*} [Fintype Y] {d : ℕ}
    (A : Matrix Y (Edge d) ℂ) (S : FourSet d) :
    (A * fourFormMatrix S * A.transpose).transpose = A * fourFormMatrix S * A.transpose := by
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
    D5SupportFactor.fourFormMatrix_symmetric]
  simp only [Matrix.mul_assoc]

theorem companion_purity_bound_nonneg {X Y B E : Type*} [Fintype X] [Fintype Y]
    [Fintype B] [Fintype E] [DecidableEq Y]
    (N : Stinespring Y B E) (β : ℝ)
    (hbound : ∀ u, vectorNormSq u = 1 → purity (N.apply (pureDensity u)) ≤ β)
    (Ψ : X × Y → ℂ) (hΨ : vectorNormSq Ψ = 1) : 0 ≤ β := by
  classical
  have hY : Nonempty Y := by
    by_contra h
    letI : IsEmpty Y := not_nonempty_iff.mp h
    simp [vectorNormSq] at hΨ
  let y : Y := Classical.choice hY
  have hy : vectorNormSq (Pi.single y (1 : ℂ)) = 1 := by
    simp [vectorNormSq, Pi.single_apply, apply_ite]
  have hp := purity_nonneg_of_hermitian _
    (N.apply_posSemidef _ (pureDensity_posSemidef (Pi.single y (1 : ℂ)))).1
  exact hp.trans (hbound _ hy)

namespace Stinespring

theorem tensor_product_amplitudes {X Y A B F E : Type*}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B] [Fintype F] [Fintype E]
    [DecidableEq X] [DecidableEq Y]
    (M : Stinespring X A F) (N : Stinespring Y B E) (u : X → ℂ) (v : Y → ℂ) :
    (M.tensor N).amplitudes (fun xy => u xy.1 * v xy.2) = M.amplitudes u ⊗ₖ N.amplitudes v := by
  ext ab fe
  rw [tensor_amplitudes]
  simp only [amplitudes, Matrix.kroneckerMap_apply, Finset.sum_mul]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  ring

theorem tensor_product_output {X Y A B F E : Type*}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B] [Fintype F] [Fintype E]
    [DecidableEq X] [DecidableEq Y]
    (M : Stinespring X A F) (N : Stinespring Y B E) (u : X → ℂ) (v : Y → ℂ) :
    (M.tensor N).apply (pureDensity (fun xy => u xy.1 * v xy.2)) =
      M.apply (pureDensity u) ⊗ₖ N.apply (pureDensity v) := by
  simp only [apply_pureDensity, tensor_product_amplitudes, reducedLeft, crossLeft_kronecker]

theorem tensor_product_purity {X Y A B F E : Type*}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B] [Fintype F] [Fintype E]
    [DecidableEq X] [DecidableEq Y]
    (M : Stinespring X A F) (N : Stinespring Y B E) (u : X → ℂ) (v : Y → ℂ) :
    purity ((M.tensor N).apply (pureDensity (fun xy => u xy.1 * v xy.2))) =
      purity (M.apply (pureDensity u)) * purity (N.apply (pureDensity v)) := by
  rw [tensor_product_output]
  exact purity_kronecker _ _
    (M.apply_posSemidef _ (pureDensity_posSemidef u)).1
    (N.apply_posSemidef _ (pureDensity_posSemidef v)).1

end Stinespring

theorem product_vectorNormSq {X Y : Type*} [Fintype X] [Fintype Y]
    (u : X → ℂ) (v : Y → ℂ) :
    vectorNormSq (fun xy : X × Y => u xy.1 * v xy.2) = vectorNormSq u * vectorNormSq v := by
  simp only [vectorNormSq, Complex.normSq_mul, Fintype.sum_prod_type,
    Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_comm

abbrev EdgePower (d : ℕ) : ℕ → Type
  | 0 => Unit
  | n + 1 => Edge d × EdgePower d n

instance edgePowerFintype (d n : ℕ) : Fintype (EdgePower d n) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype Unit)
  | succ n ih =>
      letI := ih
      exact inferInstanceAs (Fintype (Edge d × EdgePower d n))

instance edgePowerDecidableEq (d n : ℕ) : DecidableEq (EdgePower d n) := by
  induction n with
  | zero => exact inferInstanceAs (DecidableEq Unit)
  | succ n ih =>
      letI := ih
      exact inferInstanceAs (DecidableEq (Edge d × EdgePower d n))

def antisymmetricPowerStinespring (d : ℕ) : (n : ℕ) →
    Stinespring (EdgePower d n) (PhysicalPower d n) (PhysicalPower d n)
  | 0 =>
      { coeff := fun _ _ => 1
        gram_eq_one := by
          ext i j
          cases i
          cases j
          change (∑ be : Unit × Unit, star (1 : ℂ) * 1) = 1
          simp }
  | n + 1 => (antisymmetricStinespring d).tensor (antisymmetricPowerStinespring d n)

def tensorSlaterInput {d : ℕ} (e : Edge d) : (n : ℕ) → EdgePower d n → ℂ
  | 0 => fun _ => 1
  | n + 1 => fun xy => coordinateSlater e xy.1 * tensorSlaterInput e n xy.2

theorem antisymmetricPower_amplitudes_fiber (d n : ℕ)
    (Ψ : EdgePower d (n + 1) → ℂ) (a b : Fin d) (r s : PhysicalPower d n) :
    (antisymmetricPowerStinespring d (n + 1)).amplitudes Ψ (a, r) (b, s) =
      (antisymmetricPowerStinespring d n).amplitudes
        (fun x => ∑ e : Edge d, wedgeInclusion d (a, b) e * Ψ (e, x)) r s := by
  change ((antisymmetricStinespring d).tensor (antisymmetricPowerStinespring d n)).amplitudes
    Ψ (a, r) (b, s) = _
  rw [Stinespring.tensor_amplitudes]
  change (∑ e : Edge d, ∑ x : EdgePower d n, wedgeInclusion d (a, b) e *
    (antisymmetricPowerStinespring d n).coeff (r, s) x * Ψ (e, x)) =
    ∑ x : EdgePower d n, (antisymmetricPowerStinespring d n).coeff (r, s) x *
      (∑ e : Edge d, wedgeInclusion d (a, b) e * Ψ (e, x))
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro e he
  ring

theorem antisymmetricPower_amplitudes_support (d n : ℕ) (u : EdgePower d n → ℂ) :
    HasAntisymmetricSupport d n ((antisymmetricPowerStinespring d n).amplitudes u) := by
  induction n with
  | zero => trivial
  | succ n ih =>
      constructor
      · intro a b r s
        rw [antisymmetricPower_amplitudes_fiber, antisymmetricPower_amplitudes_fiber]
        have hinput : (fun x => ∑ e : Edge d, wedgeInclusion d (b, a) e * u (e, x)) =
            (-1 : ℂ) • (fun x => ∑ e : Edge d, wedgeInclusion d (a, b) e * u (e, x)) := by
          ext x
          simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro e he
          rw [wedgeInclusion_swap]
          ring
        rw [hinput, Stinespring.amplitudes_smul]
        simp [Matrix.smul_apply, smul_eq_mul]
      · intro a b
        have hf : (fun r s => (antisymmetricPowerStinespring d (n + 1)).amplitudes
            u (a, r) (b, s)) = (antisymmetricPowerStinespring d n).amplitudes
              (fun x => ∑ e : Edge d, wedgeInclusion d (a, b) e * u (e, x)) := by
          ext r s
          exact antisymmetricPower_amplitudes_fiber d n u a b r s
        rw [hf]
        exact ih (fun x => ∑ e : Edge d, wedgeInclusion d (a, b) e * u (e, x))

theorem tensorSlaterInput_normSq {d : ℕ} (e : Edge d) (n : ℕ) :
    vectorNormSq (tensorSlaterInput e n) = 1 := by
  induction n with
  | zero => simp [tensorSlaterInput, vectorNormSq]
  | succ n ih =>
      change vectorNormSq (fun xy : Edge d × EdgePower d n =>
        coordinateSlater e xy.1 * tensorSlaterInput e n xy.2) = 1
      rw [product_vectorNormSq, coordinateSlater_normSq, ih, mul_one]

theorem antisymmetricPower_zero_output (d : ℕ) (u : EdgePower d 0 → ℂ)
    (hu : vectorNormSq u = 1) :
    (antisymmetricPowerStinespring d 0).apply (pureDensity u) = 1 := by
  have ht : Matrix.trace ((antisymmetricPowerStinespring d 0).apply (pureDensity u)) =
      (1 : ℂ) := by
    rw [Stinespring.apply_trace, pureDensity_trace, hu]
    norm_num
  ext i j
  cases i
  cases j
  simpa [Matrix.trace, Matrix.diag, Matrix.one_apply] using ht

theorem antisymmetricPower_tensorSlater_purity {d : ℕ} (e : Edge d) (n : ℕ) :
    purity ((antisymmetricPowerStinespring d n).apply (pureDensity (tensorSlaterInput e n))) =
      (1 / 2 : ℝ) ^ n := by
  induction n with
  | zero =>
      rw [antisymmetricPower_zero_output _ _ (tensorSlaterInput_normSq e 0)]
      simp [purity]
  | succ n ih =>
      change purity (((antisymmetricStinespring d).tensor (antisymmetricPowerStinespring d n)).apply
        (pureDensity (fun xy => coordinateSlater e xy.1 * tensorSlaterInput e n xy.2))) = _
      rw [Stinespring.tensor_product_purity, ← antisymmetricChannel_eq_stinespring,
        antisymmetricChannel_slater_purity, ih]
      rw [pow_succ, mul_comm]

theorem companion_fourForm_correction_lower {Y B E : Type*}
    [Fintype Y] [Fintype B] [Fintype E] [DecidableEq Y] {d : ℕ}
    (N : Stinespring Y B E) (β : ℝ)
    (hbound : ∀ u, vectorNormSq u = 1 → purity (N.apply (pureDensity u)) ≤ β)
    (A : Matrix Y (Edge d) ℂ) (S : FourSet d) :
    -β * SchattenSupport.schattenOne (ExteriorSupport.orderedExterior
      (A * fourFormMatrix S * A.transpose)) ≤ (companionCorrection N A (fourFormMatrix S)).re := by
  exact ActualContractionLower.actual_symmetric_replica_lower N β hbound
    (A * fourFormMatrix S * A.transpose) (companion_fourForm_symmetric A S)

theorem antisymmetric_d5_companion_purity_le {Y B E : Type*}
    [Fintype Y] [Fintype B] [Fintype E] [DecidableEq Y]
    (N : Stinespring Y B E) (β : ℝ)
    (hbound : ∀ u, vectorNormSq u = 1 → purity (N.apply (pureDensity u)) ≤ β)
    (Ψ : Edge 5 × Y → ℂ) (hΨ : vectorNormSq Ψ = 1) :
    purity (((antisymmetricStinespring 5).tensor N).apply (pureDensity Ψ)) ≤ β / 2 := by
  have hb := companion_purity_bound_nonneg N β hbound Ψ hΨ
  have hq := companion_marginal_purity_bound N β hbound Ψ hΨ
  have hn := companion_actual_d5_exterior_nuclear_bound Ψ hΨ
  have hbn := mul_le_mul_of_nonneg_left hn hb
  have hc : -β * (∑ t : Fin 5, SchattenSupport.schattenOne (ExteriorSupport.orderedExterior
      (companionCoefficient Ψ * d5FourFormMatrix t * (companionCoefficient Ψ).transpose))) ≤
      ∑ t : Fin 5, (companionCorrection N (companionCoefficient Ψ) (d5FourFormMatrix t)).re := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro t ht
    exact companion_fourForm_correction_lower N β hbound (companionCoefficient Ψ) (omittedFourSet t)
  rw [antisymmetric_d5_companion_purity]
  nlinarith

theorem antisymmetric_d4_companion_purity_le {Y B E : Type*}
    [Fintype Y] [Fintype B] [Fintype E] [DecidableEq Y]
    (N : Stinespring Y B E) (β : ℝ)
    (hbound : ∀ u, vectorNormSq u = 1 → purity (N.apply (pureDensity u)) ≤ β)
    (Ψ : Edge 4 × Y → ℂ) (hΨ : vectorNormSq Ψ = 1) :
    purity (((antisymmetricStinespring 4).tensor N).apply (pureDensity Ψ)) ≤ β / 2 := by
  have hb := companion_purity_bound_nonneg N β hbound Ψ hΨ
  have hq := companion_marginal_purity_bound N β hbound Ψ hΨ
  have hn := companion_actual_d4_exterior_nuclear_bound Ψ hΨ
  have hbn := mul_le_mul_of_nonneg_left hn hb
  have hc := companion_fourForm_correction_lower N β hbound (companionCoefficient Ψ)
    (⟨Finset.univ, by simp⟩ : FourSet 4)
  change -β * SchattenSupport.schattenOne (ExteriorSupport.orderedExterior
      (companionCoefficient Ψ * d4FourFormMatrix * (companionCoefficient Ψ).transpose)) ≤
    (companionCorrection N (companionCoefficient Ψ) d4FourFormMatrix).re at hc
  rw [antisymmetric_d4_companion_purity]
  nlinarith

theorem antisymmetricPower_d5_purity_upper (n : ℕ) (u : EdgePower 5 n → ℂ)
    (hu : vectorNormSq u = 1) :
    purity ((antisymmetricPowerStinespring 5 n).apply (pureDensity u)) ≤ (1 / 2 : ℝ) ^ n := by
  induction n with
  | zero =>
      rw [antisymmetricPower_zero_output _ _ hu]
      norm_num [purity]
  | succ n ih =>
      change purity (((antisymmetricStinespring 5).tensor (antisymmetricPowerStinespring 5 n)).apply
        (pureDensity u)) ≤ _
      have h := antisymmetric_d5_companion_purity_le (antisymmetricPowerStinespring 5 n)
        ((1 / 2 : ℝ) ^ n) (fun w hw => ih w hw) u hu
      calc
        _ ≤ (1 / 2 : ℝ) ^ n / 2 := h
        _ = (1 / 2 : ℝ) ^ (n + 1) := by rw [pow_succ]; ring

theorem antisymmetricPower_d4_purity_upper (n : ℕ) (u : EdgePower 4 n → ℂ)
    (hu : vectorNormSq u = 1) :
    purity ((antisymmetricPowerStinespring 4 n).apply (pureDensity u)) ≤ (1 / 2 : ℝ) ^ n := by
  induction n with
  | zero =>
      rw [antisymmetricPower_zero_output _ _ hu]
      norm_num [purity]
  | succ n ih =>
      change purity (((antisymmetricStinespring 4).tensor (antisymmetricPowerStinespring 4 n)).apply
        (pureDensity u)) ≤ _
      have h := antisymmetric_d4_companion_purity_le (antisymmetricPowerStinespring 4 n)
        ((1 / 2 : ℝ) ^ n) (fun w hw => ih w hw) u hu
      calc
        _ ≤ (1 / 2 : ℝ) ^ n / 2 := h
        _ = (1 / 2 : ℝ) ^ (n + 1) := by rw [pow_succ]; ring

theorem antisymmetricPower_d5_purity_optimum (n : ℕ) :
    (∀ u : EdgePower 5 n → ℂ, vectorNormSq u = 1 →
      purity ((antisymmetricPowerStinespring 5 n).apply (pureDensity u)) ≤ (1 / 2 : ℝ) ^ n) ∧
    ∃ u : EdgePower 5 n → ℂ, vectorNormSq u = 1 ∧
      purity ((antisymmetricPowerStinespring 5 n).apply (pureDensity u)) = (1 / 2 : ℝ) ^ n := by
  constructor
  · exact antisymmetricPower_d5_purity_upper n
  · let e : Edge 5 := ⟨(0, 1), by decide⟩
    exact ⟨tensorSlaterInput e n, tensorSlaterInput_normSq e n,
      antisymmetricPower_tensorSlater_purity e n⟩

theorem antisymmetricPower_d4_purity_optimum (n : ℕ) :
    (∀ u : EdgePower 4 n → ℂ, vectorNormSq u = 1 →
      purity ((antisymmetricPowerStinespring 4 n).apply (pureDensity u)) ≤ (1 / 2 : ℝ) ^ n) ∧
    ∃ u : EdgePower 4 n → ℂ, vectorNormSq u = 1 ∧
      purity ((antisymmetricPowerStinespring 4 n).apply (pureDensity u)) = (1 / 2 : ℝ) ^ n := by
  constructor
  · exact antisymmetricPower_d4_purity_upper n
  · let e : Edge 4 := ⟨(0, 1), by decide⟩
    exact ⟨tensorSlaterInput e n, tensorSlaterInput_normSq e n,
      antisymmetricPower_tensorSlater_purity e n⟩

def physicalRegroupEquiv (d n : ℕ) :
    (PhysicalPower d (n + 1) × PhysicalPower d (n + 1)) ≃
      ((Fin d × Fin d) × (PhysicalPower d n × PhysicalPower d n)) where
  toFun := fun ⟨⟨a, r⟩, ⟨b, s⟩⟩ => ((a, b), (r, s))
  invFun := fun ⟨⟨a, b⟩, ⟨r, s⟩⟩ => ((a, r), (b, s))
  left_inv := by rintro ⟨⟨a, r⟩, ⟨b, s⟩⟩; rfl
  right_inv := by rintro ⟨⟨a, b⟩, ⟨r, s⟩⟩; rfl

def physicalTensorIsometry (d : ℕ) : (n : ℕ) →
    Matrix (PhysicalPower d n × PhysicalPower d n) (EdgePower d n) ℂ
  | 0 => fun _ _ => 1
  | n + 1 => fun uv ex => wedgeInclusion d (uv.1.1, uv.2.1) ex.1 *
      physicalTensorIsometry d n (uv.1.2, uv.2.2) ex.2

def localPhysicalAntisymmetrizer (d : ℕ) : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  (1 / 2 : ℂ) • (1 - physicalSwap d)

def physicalTensorAntisymmetrizer (d : ℕ) : (n : ℕ) →
    Matrix (PhysicalPower d n × PhysicalPower d n) (PhysicalPower d n × PhysicalPower d n) ℂ
  | 0 => 1
  | n + 1 => fun uv wz => localPhysicalAntisymmetrizer d (uv.1.1, uv.2.1) (wz.1.1, wz.2.1) *
      physicalTensorAntisymmetrizer d n (uv.1.2, uv.2.2) (wz.1.2, wz.2.2)

theorem physicalTensorIsometry_succ_regroup (d n : ℕ) :
    physicalTensorIsometry d (n + 1) =
      (wedgeInclusion d ⊗ₖ physicalTensorIsometry d n).submatrix
        (physicalRegroupEquiv d n) id := by
  ext uv ex
  rfl

theorem physicalTensorAntisymmetrizer_succ_regroup (d n : ℕ) :
    physicalTensorAntisymmetrizer d (n + 1) =
      (localPhysicalAntisymmetrizer d ⊗ₖ physicalTensorAntisymmetrizer d n).submatrix
        (physicalRegroupEquiv d n) (physicalRegroupEquiv d n) := by
  ext uv wz
  rfl

theorem physicalTensorIsometry_eq_coeff (d n : ℕ) :
    physicalTensorIsometry d n = (antisymmetricPowerStinespring d n).coeff := by
  induction n with
  | zero => rfl
  | succ n ih =>
      ext uv ex
      simp only [physicalTensorIsometry, antisymmetricPowerStinespring,
        Stinespring.tensor, Stinespring.tensorCoeff, antisymmetricStinespring]
      rw [ih]

theorem physicalTensorIsometry_gram (d n : ℕ) :
    (physicalTensorIsometry d n).conjTranspose * physicalTensorIsometry d n = 1 := by
  rw [physicalTensorIsometry_eq_coeff]
  exact (antisymmetricPowerStinespring d n).gram_eq_one

theorem physicalTensorIsometry_range_projector (d n : ℕ) :
    physicalTensorIsometry d n * (physicalTensorIsometry d n).conjTranspose =
      physicalTensorAntisymmetrizer d n := by
  induction n with
  | zero =>
      ext uv wz
      rcases uv with ⟨⟨⟩, ⟨⟩⟩
      rcases wz with ⟨⟨⟩, ⟨⟩⟩
      change (∑ x : Unit, (1 : ℂ) * star (1 : ℂ)) = 1
      simp
  | succ n ih =>
      ext ⟨⟨a, r⟩, ⟨b, s⟩⟩ ⟨⟨c, t⟩, ⟨f, v⟩⟩
      calc
        _ = wedgeProjector d (a, b) (c, f) *
            (physicalTensorIsometry d n * (physicalTensorIsometry d n).conjTranspose)
              (r, s) (t, v) := by
          simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, wedgeProjector]
          simp only [physicalTensorIsometry, Fintype.sum_prod_type, star_mul]
          simp only [Finset.sum_mul]
          simp only [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro e he
          apply Finset.sum_congr rfl
          intro x hx
          ring
        _ = _ := by
          rw [ih, wedgeProjector_eq_antisymmetrizer]
          rfl

theorem physicalTensorAntisymmetrizer_hermitian (d n : ℕ) :
    (physicalTensorAntisymmetrizer d n).conjTranspose = physicalTensorAntisymmetrizer d n := by
  rw [← physicalTensorIsometry_range_projector]
  simp

theorem physicalTensorAntisymmetrizer_idempotent (d n : ℕ) :
    physicalTensorAntisymmetrizer d n * physicalTensorAntisymmetrizer d n =
      physicalTensorAntisymmetrizer d n := by
  rw [← physicalTensorIsometry_range_projector]
  calc
    _ = physicalTensorIsometry d n *
        ((physicalTensorIsometry d n).conjTranspose * physicalTensorIsometry d n) *
        (physicalTensorIsometry d n).conjTranspose := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [physicalTensorIsometry_gram, Matrix.mul_one]

theorem physicalTensorAntisymmetrizer_posSemidef (d n : ℕ) :
    (physicalTensorAntisymmetrizer d n).PosSemidef := by
  rw [← physicalTensorIsometry_range_projector]
  exact Matrix.posSemidef_self_mul_conjTranspose _

theorem localPhysicalAntisymmetrizer_mulVec (d : ℕ) (w : Fin d × Fin d → ℂ) :
    (localPhysicalAntisymmetrizer d).mulVec w =
      fun ab => (1 / 2 : ℂ) * (w ab - w (ab.2, ab.1)) := by
  rw [localPhysicalAntisymmetrizer, ← wedgeProjector_eq_antisymmetrizer,
    wedgeProjector_mulVec]

theorem physicalTensorAntisymmetrizer_mulVec_fiber (d n : ℕ)
    (ψ : PhysicalPower d (n + 1) × PhysicalPower d (n + 1) → ℂ)
    (a b : Fin d) (r s : PhysicalPower d n) :
    (physicalTensorAntisymmetrizer d (n + 1)).mulVec ψ ((a, r), (b, s)) =
      (localPhysicalAntisymmetrizer d).mulVec
        (fun cf => (physicalTensorAntisymmetrizer d n).mulVec
          (fun tv => ψ ((cf.1, tv.1), (cf.2, tv.2))) (r, s)) (a, b) := by
  simp only [Matrix.mulVec, dotProduct]
  simp only [physicalTensorAntisymmetrizer, Fintype.sum_prod_type, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c hc
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro f hf
  apply Finset.sum_congr rfl
  intro t ht
  apply Finset.sum_congr rfl
  intro v hv
  ring

theorem physicalTensorAntisymmetrizer_fixes (d n : ℕ)
    (U : Matrix (PhysicalPower d n) (PhysicalPower d n) ℂ)
    (hU : HasAntisymmetricSupport d n U) :
    (physicalTensorAntisymmetrizer d n).mulVec (fun ab => U ab.1 ab.2) =
      (fun ab => U ab.1 ab.2) := by
  induction n with
  | zero => simp [physicalTensorAntisymmetrizer]
  | succ n ih =>
      rcases hU with ⟨hs, ht⟩
      ext ⟨⟨a, r⟩, ⟨b, s⟩⟩
      rw [physicalTensorAntisymmetrizer_mulVec_fiber]
      have hf : (fun cf : Fin d × Fin d => (physicalTensorAntisymmetrizer d n).mulVec
          (fun tv => U (cf.1, tv.1) (cf.2, tv.2)) (r, s)) =
          (fun cf => U (cf.1, r) (cf.2, s)) := by
        ext cf
        rw [ih _ (ht cf.1 cf.2)]
      rw [hf, localPhysicalAntisymmetrizer_mulVec]
      change (1 / 2 : ℂ) * (U (a, r) (b, s) - U (b, r) (a, s)) = U (a, r) (b, s)
      rw [hs]
      ring

theorem physicalTensorIsometry_mulVec_eq_amplitudes (d n : ℕ) (u : EdgePower d n → ℂ) :
    (physicalTensorIsometry d n).mulVec u =
      (fun ab => (antisymmetricPowerStinespring d n).amplitudes u ab.1 ab.2) := by
  rw [physicalTensorIsometry_eq_coeff]
  rfl

theorem physicalTensorAntisymmetrizer_image_support (d n : ℕ)
    (ψ : PhysicalPower d n × PhysicalPower d n → ℂ) :
    HasAntisymmetricSupport d n
      (fun a b => (physicalTensorAntisymmetrizer d n).mulVec ψ (a, b)) := by
  rw [← physicalTensorIsometry_range_projector, ← Matrix.mulVec_mulVec,
    physicalTensorIsometry_mulVec_eq_amplitudes]
  exact antisymmetricPower_amplitudes_support d n
    ((physicalTensorIsometry d n).conjTranspose.mulVec ψ)

theorem physicalTensorAntisymmetrizer_fix_iff_support (d n : ℕ)
    (ψ : PhysicalPower d n × PhysicalPower d n → ℂ) :
    (physicalTensorAntisymmetrizer d n).mulVec ψ = ψ ↔
      HasAntisymmetricSupport d n (fun a b => ψ (a, b)) := by
  constructor
  · intro h
    have hs := physicalTensorAntisymmetrizer_image_support d n ψ
    rw [h] at hs
    exact hs
  · intro h
    exact physicalTensorAntisymmetrizer_fixes d n (fun a b => ψ (a, b)) h

def physicalCoefficientPreimage (d n : ℕ)
    (ψ : PhysicalPower d n × PhysicalPower d n → ℂ) : EdgePower d n → ℂ :=
  (physicalTensorIsometry d n).conjTranspose.mulVec ψ

theorem physicalTensorIsometry_reconstruct (d n : ℕ)
    (ψ : PhysicalPower d n × PhysicalPower d n → ℂ)
    (hψ : HasAntisymmetricSupport d n (fun a b => ψ (a, b))) :
    (physicalTensorIsometry d n).mulVec (physicalCoefficientPreimage d n ψ) = ψ := by
  rw [physicalCoefficientPreimage, Matrix.mulVec_mulVec, physicalTensorIsometry_range_projector]
  exact (physicalTensorAntisymmetrizer_fix_iff_support d n ψ).mpr hψ

theorem physicalCoefficientPreimage_normSq (d n : ℕ)
    (ψ : PhysicalPower d n × PhysicalPower d n → ℂ)
    (hψ : HasAntisymmetricSupport d n (fun a b => ψ (a, b))) :
    vectorNormSq (physicalCoefficientPreimage d n ψ) = vectorNormSq ψ := by
  have ha := physicalTensorIsometry_reconstruct d n ψ hψ
  rw [physicalTensorIsometry_mulVec_eq_amplitudes] at ha
  have hn := (antisymmetricPowerStinespring d n).amplitudes_normSq
    (physicalCoefficientPreimage d n ψ)
  rw [ha] at hn
  exact hn.symm

theorem physical_partialTrace_eq_channel (d n : ℕ)
    (ψ : PhysicalPower d n × PhysicalPower d n → ℂ)
    (hψ : HasAntisymmetricSupport d n (fun a b => ψ (a, b))) :
    partialTraceLeft (pureDensity ψ) =
      (antisymmetricPowerStinespring d n).apply (pureDensity (physicalCoefficientPreimage d n ψ)) := by
  have ha := physicalTensorIsometry_reconstruct d n ψ hψ
  rw [physicalTensorIsometry_mulVec_eq_amplitudes] at ha
  rw [Stinespring.apply_pureDensity]
  have hA : (antisymmetricPowerStinespring d n).amplitudes (physicalCoefficientPreimage d n ψ) =
      (fun a b => ψ (a, b)) := by
    ext a b
    exact congrFun ha (a, b)
  rw [hA]
  rfl

theorem physicalTensorIsometry_range_iff_support (d n : ℕ)
    (ψ : PhysicalPower d n × PhysicalPower d n → ℂ) :
    (∃ u : EdgePower d n → ℂ, (physicalTensorIsometry d n).mulVec u = ψ) ↔
      HasAntisymmetricSupport d n (fun a b => ψ (a, b)) := by
  constructor
  · rintro ⟨u, hu⟩
    have hs := antisymmetricPower_amplitudes_support d n u
    rw [physicalTensorIsometry_mulVec_eq_amplitudes] at hu
    have hA : (antisymmetricPowerStinespring d n).amplitudes u = (fun a b => ψ (a, b)) := by
      ext a b
      exact congrFun hu (a, b)
    rw [hA] at hs
    exact hs
  · intro hs
    exact ⟨physicalCoefficientPreimage d n ψ, physicalTensorIsometry_reconstruct d n ψ hs⟩

theorem physical_normalized_preimage (d n : ℕ)
    (ψ : PhysicalPower d n × PhysicalPower d n → ℂ) (hunit : vectorNormSq ψ = 1)
    (hψ : HasAntisymmetricSupport d n (fun a b => ψ (a, b))) :
    ∃ u : EdgePower d n → ℂ, vectorNormSq u = 1 ∧
      (physicalTensorIsometry d n).mulVec u = ψ ∧
      partialTraceLeft (pureDensity ψ) = (antisymmetricPowerStinespring d n).apply (pureDensity u) := by
  refine ⟨physicalCoefficientPreimage d n ψ, ?_, physicalTensorIsometry_reconstruct d n ψ hψ,
    physical_partialTrace_eq_channel d n ψ hψ⟩
  rw [physicalCoefficientPreimage_normSq d n ψ hψ, hunit]

theorem antisymmetric_physical_d5_purity_upper (n : ℕ)
    (ψ : PhysicalPower 5 n × PhysicalPower 5 n → ℂ) (hunit : vectorNormSq ψ = 1)
    (hψ : HasAntisymmetricSupport 5 n (fun a b => ψ (a, b))) :
    purity (partialTraceLeft (pureDensity ψ)) ≤ (1 / 2 : ℝ) ^ n := by
  rw [physical_partialTrace_eq_channel 5 n ψ hψ]
  apply antisymmetricPower_d5_purity_upper
  rw [physicalCoefficientPreimage_normSq 5 n ψ hψ, hunit]

theorem antisymmetric_physical_d4_purity_upper (n : ℕ)
    (ψ : PhysicalPower 4 n × PhysicalPower 4 n → ℂ) (hunit : vectorNormSq ψ = 1)
    (hψ : HasAntisymmetricSupport 4 n (fun a b => ψ (a, b))) :
    purity (partialTraceLeft (pureDensity ψ)) ≤ (1 / 2 : ℝ) ^ n := by
  rw [physical_partialTrace_eq_channel 4 n ψ hψ]
  apply antisymmetricPower_d4_purity_upper
  rw [physicalCoefficientPreimage_normSq 4 n ψ hψ, hunit]

theorem antisymmetric_physical_d5_projector_purity_upper (n : ℕ)
    (ψ : PhysicalPower 5 n × PhysicalPower 5 n → ℂ) (hunit : vectorNormSq ψ = 1)
    (hψ : (physicalTensorAntisymmetrizer 5 n).mulVec ψ = ψ) :
    purity (partialTraceLeft (pureDensity ψ)) ≤ (1 / 2 : ℝ) ^ n :=
  antisymmetric_physical_d5_purity_upper n ψ hunit
    ((physicalTensorAntisymmetrizer_fix_iff_support 5 n ψ).mp hψ)

theorem antisymmetric_physical_d4_projector_purity_upper (n : ℕ)
    (ψ : PhysicalPower 4 n × PhysicalPower 4 n → ℂ) (hunit : vectorNormSq ψ = 1)
    (hψ : (physicalTensorAntisymmetrizer 4 n).mulVec ψ = ψ) :
    purity (partialTraceLeft (pureDensity ψ)) ≤ (1 / 2 : ℝ) ^ n :=
  antisymmetric_physical_d4_purity_upper n ψ hunit
    ((physicalTensorAntisymmetrizer_fix_iff_support 4 n ψ).mp hψ)

def physicalTensorSlaterVector {d : ℕ} (e : Edge d) (n : ℕ) :
    PhysicalPower d n × PhysicalPower d n → ℂ :=
  (physicalTensorIsometry d n).mulVec (tensorSlaterInput e n)

theorem antisymmetricPower_tensorSlater_amplitudes {d : ℕ} (e : Edge d) (n : ℕ) :
    (antisymmetricPowerStinespring d n).amplitudes (tensorSlaterInput e n) =
      slaterTensorAmplitude e n := by
  induction n with
  | zero =>
      ext a b
      rcases a with ⟨⟩
      rcases b with ⟨⟩
      simp [antisymmetricPowerStinespring, Stinespring.amplitudes,
        tensorSlaterInput, slaterTensorAmplitude]
  | succ n ih =>
      change ((antisymmetricStinespring d).tensor (antisymmetricPowerStinespring d n)).amplitudes
        (fun xy => coordinateSlater e xy.1 * tensorSlaterInput e n xy.2) =
          slaterAmplitude e ⊗ₖ slaterTensorAmplitude e n
      rw [Stinespring.tensor_product_amplitudes, ih]
      congr 1
      ext a b
      simp [Stinespring.amplitudes, coordinateSlater, antisymmetricStinespring,
        slaterAmplitude, Pi.single_apply]

theorem physicalTensorSlaterVector_eq_product {d : ℕ} (e : Edge d) (n : ℕ) :
    physicalTensorSlaterVector e n = (fun ab => slaterTensorAmplitude e n ab.1 ab.2) := by
  rw [physicalTensorSlaterVector, physicalTensorIsometry_mulVec_eq_amplitudes,
    antisymmetricPower_tensorSlater_amplitudes]

theorem physicalTensorSlaterVector_normSq {d : ℕ} (e : Edge d) (n : ℕ) :
    vectorNormSq (physicalTensorSlaterVector e n) = 1 := by
  rw [physicalTensorSlaterVector, physicalTensorIsometry_mulVec_eq_amplitudes,
    Stinespring.amplitudes_normSq, tensorSlaterInput_normSq]

theorem physicalTensorSlaterVector_support {d : ℕ} (e : Edge d) (n : ℕ) :
    HasAntisymmetricSupport d n (fun a b => physicalTensorSlaterVector e n (a, b)) := by
  rw [physicalTensorSlaterVector_eq_product]
  exact slaterTensor_antisymmetricSupport e n

theorem physicalTensor_partialTrace_forward (d n : ℕ) (u : EdgePower d n → ℂ) :
    partialTraceLeft (pureDensity ((physicalTensorIsometry d n).mulVec u)) =
      (antisymmetricPowerStinespring d n).apply (pureDensity u) := by
  rw [physicalTensorIsometry_mulVec_eq_amplitudes, Stinespring.apply_pureDensity]
  rfl

theorem physicalTensorSlaterVector_purity {d : ℕ} (e : Edge d) (n : ℕ) :
    purity (partialTraceLeft (pureDensity (physicalTensorSlaterVector e n))) = (1 / 2 : ℝ) ^ n := by
  rw [physicalTensorSlaterVector, physicalTensor_partialTrace_forward,
    antisymmetricPower_tensorSlater_purity]

theorem antisymmetric_physical_d5_purity_optimum (n : ℕ) :
    (∀ ψ : PhysicalPower 5 n × PhysicalPower 5 n → ℂ, vectorNormSq ψ = 1 →
      HasAntisymmetricSupport 5 n (fun a b => ψ (a, b)) →
      purity (partialTraceLeft (pureDensity ψ)) ≤ (1 / 2 : ℝ) ^ n) ∧
    ∃ ψ : PhysicalPower 5 n × PhysicalPower 5 n → ℂ, vectorNormSq ψ = 1 ∧
      HasAntisymmetricSupport 5 n (fun a b => ψ (a, b)) ∧
      purity (partialTraceLeft (pureDensity ψ)) = (1 / 2 : ℝ) ^ n := by
  constructor
  · exact antisymmetric_physical_d5_purity_upper n
  · let e : Edge 5 := ⟨(0, 1), by decide⟩
    exact ⟨physicalTensorSlaterVector e n, physicalTensorSlaterVector_normSq e n,
      physicalTensorSlaterVector_support e n, physicalTensorSlaterVector_purity e n⟩

theorem antisymmetric_physical_d4_purity_optimum (n : ℕ) :
    (∀ ψ : PhysicalPower 4 n × PhysicalPower 4 n → ℂ, vectorNormSq ψ = 1 →
      HasAntisymmetricSupport 4 n (fun a b => ψ (a, b)) →
      purity (partialTraceLeft (pureDensity ψ)) ≤ (1 / 2 : ℝ) ^ n) ∧
    ∃ ψ : PhysicalPower 4 n × PhysicalPower 4 n → ℂ, vectorNormSq ψ = 1 ∧
      HasAntisymmetricSupport 4 n (fun a b => ψ (a, b)) ∧
      purity (partialTraceLeft (pureDensity ψ)) = (1 / 2 : ℝ) ^ n := by
  constructor
  · exact antisymmetric_physical_d4_purity_upper n
  · let e : Edge 4 := ⟨(0, 1), by decide⟩
    exact ⟨physicalTensorSlaterVector e n, physicalTensorSlaterVector_normSq e n,
      physicalTensorSlaterVector_support e n, physicalTensorSlaterVector_purity e n⟩

def physicalAliceEntropy (d n : ℕ)
    (ψ : PhysicalPower d n × PhysicalPower d n → ℂ) : ℝ :=
  AntisymmetricEntropyCost.vonNeumannEntropyBits (partialTraceLeft (pureDensity ψ))

theorem physical_entropy_ge_nat_of_purity (d n : ℕ)
    (ψ : PhysicalPower d n × PhysicalPower d n → ℂ) (hunit : vectorNormSq ψ = 1)
    (hcap : purity (partialTraceLeft (pureDensity ψ)) ≤ (1 / 2 : ℝ) ^ n) :
    (n : ℝ) ≤ physicalAliceEntropy d n ψ :=
  AntisymmetricEnsembleCost.alice_entropy_ge_nat_of_purity ψ hunit n hcap

theorem antisymmetric_physical_d5_entropy_lower (n : ℕ)
    (ψ : PhysicalPower 5 n × PhysicalPower 5 n → ℂ) (hunit : vectorNormSq ψ = 1)
    (hψ : HasAntisymmetricSupport 5 n (fun a b => ψ (a, b))) :
    (n : ℝ) ≤ physicalAliceEntropy 5 n ψ :=
  physical_entropy_ge_nat_of_purity 5 n ψ hunit
    (antisymmetric_physical_d5_purity_upper n ψ hunit hψ)

theorem antisymmetric_physical_d4_entropy_lower (n : ℕ)
    (ψ : PhysicalPower 4 n × PhysicalPower 4 n → ℂ) (hunit : vectorNormSq ψ = 1)
    (hψ : HasAntisymmetricSupport 4 n (fun a b => ψ (a, b))) :
    (n : ℝ) ≤ physicalAliceEntropy 4 n ψ :=
  physical_entropy_ge_nat_of_purity 4 n ψ hunit
    (antisymmetric_physical_d4_purity_upper n ψ hunit hψ)

def slaterProbability {d : ℕ} (e : Edge d) (a : Fin d) : ℝ :=
  (if a = e.val.1 then 1 / 2 else 0) + (if a = e.val.2 then 1 / 2 else 0)

theorem slaterProbability_sum {d : ℕ} (e : Edge d) :
    ∑ a, slaterProbability e a = 1 := by
  norm_num [slaterProbability, Finset.sum_add_distrib]

theorem slaterOutput_eq_diagonal {d : ℕ} (e : Edge d) :
    slaterOutput e = Matrix.diagonal (fun a => (slaterProbability e a : ℂ)) := by
  have he : e.val.1 ≠ e.val.2 := ne_of_lt e.property
  ext a b
  by_cases hab : a = b
  · subst b
    by_cases h1 : a = e.val.1 <;> by_cases h2 : a = e.val.2
    all_goals norm_num [slaterOutput, Matrix.single_apply, slaterProbability,
      h1, h2, he, Ne.symm he, eq_comm]
  · have h1 : ¬(e.val.1 = a ∧ e.val.1 = b) := by
      rintro ⟨ha, hb⟩
      exact hab (ha.symm.trans hb)
    have h2 : ¬(e.val.2 = a ∧ e.val.2 = b) := by
      rintro ⟨ha, hb⟩
      exact hab (ha.symm.trans hb)
    simp [slaterOutput, Matrix.single_apply, h1, h2, hab]

def physicalSlaterProbability {d : ℕ} (e : Edge d) :
    (n : ℕ) → PhysicalPower d n → ℝ
  | 0 => fun _ => 1
  | n + 1 => fun ar => slaterProbability e ar.1 * physicalSlaterProbability e n ar.2

theorem slaterTensor_reducedLeft_diagonal {d : ℕ} (e : Edge d) (n : ℕ) :
    reducedLeft (slaterTensorAmplitude e n) =
      Matrix.diagonal (fun a => (physicalSlaterProbability e n a : ℂ)) := by
  induction n with
  | zero =>
      ext ⟨⟩ ⟨⟩
      simp [slaterTensorAmplitude, reducedLeft, crossLeft, physicalSlaterProbability]
  | succ n ih =>
      rw [slaterTensorAmplitude, reducedLeft_kronecker, slaterAmplitude_reducedLeft,
        slaterOutput_eq_diagonal, ih, Matrix.diagonal_kronecker_diagonal]
      congr 1
      funext ⟨a, r⟩
      simp [physicalSlaterProbability]

theorem physicalSlaterProbability_sum {d : ℕ} (e : Edge d) (n : ℕ) :
    ∑ a, physicalSlaterProbability e n a = 1 := by
  induction n with
  | zero => simp [physicalSlaterProbability]
  | succ n ih =>
      simp only [physicalSlaterProbability, Fintype.sum_prod_type, ← Finset.mul_sum,
        ih, mul_one, slaterProbability_sum]

theorem slaterProbability_negMulLog_sum {d : ℕ} (e : Edge d) :
    ∑ a, Real.negMulLog (slaterProbability e a) = Real.log 2 := by
  have he : e.val.1 ≠ e.val.2 := ne_of_lt e.property
  have hentry (a : Fin d) : Real.negMulLog (slaterProbability e a) =
      (if a = e.val.1 then Real.negMulLog (1 / 2) else 0) +
        (if a = e.val.2 then Real.negMulLog (1 / 2) else 0) := by
    by_cases h1 : a = e.val.1 <;> by_cases h2 : a = e.val.2
    · exact (he (h1.symm.trans h2)).elim
    all_goals simp [slaterProbability, h1, h2, he, Ne.symm he]
  simp only [hentry, Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp only [Real.negMulLog_eq_neg]
  rw [Real.log_div (by norm_num) (by norm_num), Real.log_one]
  ring

theorem physicalSlaterProbability_negMulLog_sum {d : ℕ} (e : Edge d) (n : ℕ) :
    ∑ a, Real.negMulLog (physicalSlaterProbability e n a) = (n : ℝ) * Real.log 2 := by
  induction n with
  | zero => simp [physicalSlaterProbability]
  | succ n ih =>
      simp only [physicalSlaterProbability, Fintype.sum_prod_type, Real.negMulLog_mul,
        Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum,
        physicalSlaterProbability_sum, one_mul, ih, slaterProbability_sum,
        slaterProbability_negMulLog_sum, mul_one]
      push_cast
      ring

theorem physicalTensorSlaterVector_entropy {d : ℕ} (e : Edge d) (n : ℕ) :
    physicalAliceEntropy d n (physicalTensorSlaterVector e n) = (n : ℝ) := by
  rw [physicalAliceEntropy, physicalTensorSlaterVector_eq_product]
  have hred : partialTraceLeft (pureDensity (fun ab => slaterTensorAmplitude e n ab.1 ab.2)) =
      reducedLeft (slaterTensorAmplitude e n) := by ext a b; rfl
  rw [hred, slaterTensor_reducedLeft_diagonal,
    AntisymmetricEntropyCost.entropy_type_identity,
    QuantumProver.ElegantJointMeasurement.TailReference.cfc_real_diagonal _ _ Real.continuous_negMulLog, Matrix.trace_diagonal]
  simp only [Complex.re_sum, Complex.ofReal_re, physicalSlaterProbability_negMulLog_sum]
  exact mul_div_cancel_right₀ _ (ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 2)))

theorem antisymmetric_physical_d5_entropy_optimum (n : ℕ) :
    (∀ ψ : PhysicalPower 5 n × PhysicalPower 5 n → ℂ, vectorNormSq ψ = 1 →
      HasAntisymmetricSupport 5 n (fun a b => ψ (a, b)) →
      (n : ℝ) ≤ physicalAliceEntropy 5 n ψ) ∧
    ∃ ψ : PhysicalPower 5 n × PhysicalPower 5 n → ℂ, vectorNormSq ψ = 1 ∧
      HasAntisymmetricSupport 5 n (fun a b => ψ (a, b)) ∧
      physicalAliceEntropy 5 n ψ = (n : ℝ) := by
  constructor
  · exact antisymmetric_physical_d5_entropy_lower n
  · let e : Edge 5 := ⟨(0, 1), by decide⟩
    exact ⟨physicalTensorSlaterVector e n, physicalTensorSlaterVector_normSq e n,
      physicalTensorSlaterVector_support e n, physicalTensorSlaterVector_entropy e n⟩

theorem antisymmetric_physical_d4_entropy_optimum (n : ℕ) :
    (∀ ψ : PhysicalPower 4 n × PhysicalPower 4 n → ℂ, vectorNormSq ψ = 1 →
      HasAntisymmetricSupport 4 n (fun a b => ψ (a, b)) →
      (n : ℝ) ≤ physicalAliceEntropy 4 n ψ) ∧
    ∃ ψ : PhysicalPower 4 n × PhysicalPower 4 n → ℂ, vectorNormSq ψ = 1 ∧
      HasAntisymmetricSupport 4 n (fun a b => ψ (a, b)) ∧
      physicalAliceEntropy 4 n ψ = (n : ℝ) := by
  constructor
  · exact antisymmetric_physical_d4_entropy_lower n
  · let e : Edge 4 := ⟨(0, 1), by decide⟩
    exact ⟨physicalTensorSlaterVector e n, physicalTensorSlaterVector_normSq e n,
      physicalTensorSlaterVector_support e n, physicalTensorSlaterVector_entropy e n⟩

theorem antisymmetric_physical_d5_ensemble_entropy_lower (n : ℕ)
    (ρ : Matrix (PhysicalPower 5 n × PhysicalPower 5 n)
      (PhysicalPower 5 n × PhysicalPower 5 n) ℂ)
    (E : AntisymmetricEnsembleCost.FinitePureEnsemble ρ)
    (hsupp : ρ = physicalTensorAntisymmetrizer 5 n * ρ * physicalTensorAntisymmetrizer 5 n) :
    (n : ℝ) ≤ E.averageAliceEntropy :=
  E.average_entropy_lower_from_range_purity (physicalTensorAntisymmetrizer 5 n)
    (physicalTensorAntisymmetrizer_idempotent 5 n) hsupp n
    (antisymmetric_physical_d5_projector_purity_upper n)

theorem antisymmetric_physical_d4_ensemble_entropy_lower (n : ℕ)
    (ρ : Matrix (PhysicalPower 4 n × PhysicalPower 4 n)
      (PhysicalPower 4 n × PhysicalPower 4 n) ℂ)
    (E : AntisymmetricEnsembleCost.FinitePureEnsemble ρ)
    (hsupp : ρ = physicalTensorAntisymmetrizer 4 n * ρ * physicalTensorAntisymmetrizer 4 n) :
    (n : ℝ) ≤ E.averageAliceEntropy :=
  E.average_entropy_lower_from_range_purity (physicalTensorAntisymmetrizer 4 n)
    (physicalTensorAntisymmetrizer_idempotent 4 n) hsupp n
    (antisymmetric_physical_d4_projector_purity_upper n)

theorem antisymmetric_physical_d5_finiteConvexRoof_lower (n : ℕ)
    (ρ : Matrix (PhysicalPower 5 n × PhysicalPower 5 n)
      (PhysicalPower 5 n × PhysicalPower 5 n) ℂ)
    (hsupp : ρ = physicalTensorAntisymmetrizer 5 n * ρ * physicalTensorAntisymmetrizer 5 n) :
    (n : EReal) ≤ AntisymmetricEnsembleCost.finiteConvexRoof ρ :=
  AntisymmetricEnsembleCost.finiteConvexRoof_lower_from_range_purity ρ
    (physicalTensorAntisymmetrizer 5 n) (physicalTensorAntisymmetrizer_idempotent 5 n)
    hsupp n (antisymmetric_physical_d5_projector_purity_upper n)

theorem antisymmetric_physical_d4_finiteConvexRoof_lower (n : ℕ)
    (ρ : Matrix (PhysicalPower 4 n × PhysicalPower 4 n)
      (PhysicalPower 4 n × PhysicalPower 4 n) ℂ)
    (hsupp : ρ = physicalTensorAntisymmetrizer 4 n * ρ * physicalTensorAntisymmetrizer 4 n) :
    (n : EReal) ≤ AntisymmetricEnsembleCost.finiteConvexRoof ρ :=
  AntisymmetricEnsembleCost.finiteConvexRoof_lower_from_range_purity ρ
    (physicalTensorAntisymmetrizer 4 n) (physicalTensorAntisymmetrizer_idempotent 4 n)
    hsupp n (antisymmetric_physical_d4_projector_purity_upper n)

theorem antisymmetric_physical_d5_finiteConvexRoof_real (n : ℕ)
    (ρ : Matrix (PhysicalPower 5 n × PhysicalPower 5 n)
      (PhysicalPower 5 n × PhysicalPower 5 n) ℂ)
    (hρ : ρ.PosSemidef) (htrace : Matrix.trace ρ = 1)
    (hsupp : ρ = physicalTensorAntisymmetrizer 5 n * ρ * physicalTensorAntisymmetrizer 5 n) :
    ∃ c : ℝ, (n : ℝ) ≤ c ∧ AntisymmetricEnsembleCost.finiteConvexRoof ρ = (c : EReal) :=
  DensityEnsembleExistence.density_supported_finiteConvexRoof_lower ρ hρ htrace
    (physicalTensorAntisymmetrizer 5 n) (physicalTensorAntisymmetrizer_idempotent 5 n)
    hsupp n (antisymmetric_physical_d5_projector_purity_upper n)

theorem antisymmetric_physical_d4_finiteConvexRoof_real (n : ℕ)
    (ρ : Matrix (PhysicalPower 4 n × PhysicalPower 4 n)
      (PhysicalPower 4 n × PhysicalPower 4 n) ℂ)
    (hρ : ρ.PosSemidef) (htrace : Matrix.trace ρ = 1)
    (hsupp : ρ = physicalTensorAntisymmetrizer 4 n * ρ * physicalTensorAntisymmetrizer 4 n) :
    ∃ c : ℝ, (n : ℝ) ≤ c ∧ AntisymmetricEnsembleCost.finiteConvexRoof ρ = (c : EReal) :=
  DensityEnsembleExistence.density_supported_finiteConvexRoof_lower ρ hρ htrace
    (physicalTensorAntisymmetrizer 4 n) (physicalTensorAntisymmetrizer_idempotent 4 n)
    hsupp n (antisymmetric_physical_d4_projector_purity_upper n)

theorem physicalTensorAntisymmetrizer_trace (d n : ℕ) :
    Matrix.trace (physicalTensorAntisymmetrizer d n) = (Fintype.card (EdgePower d n) : ℂ) := by
  rw [← physicalTensorIsometry_range_projector, Matrix.trace_mul_comm,
    physicalTensorIsometry_gram, Matrix.trace_one]

theorem physicalTensorAntisymmetrizer_rank (d n : ℕ) :
    Matrix.rank (physicalTensorAntisymmetrizer d n) = Fintype.card (EdgePower d n) := by
  rw [← physicalTensorIsometry_range_projector, Matrix.rank_self_mul_conjTranspose,
    ← Matrix.rank_conjTranspose_mul_self (physicalTensorIsometry d n),
    physicalTensorIsometry_gram, Matrix.rank_one]

def physicalAntisymmetricState (d n : ℕ) :
    Matrix (PhysicalPower d n × PhysicalPower d n) (PhysicalPower d n × PhysicalPower d n) ℂ :=
  (Fintype.card (EdgePower d n) : ℝ)⁻¹ • physicalTensorAntisymmetrizer d n

theorem physicalAntisymmetricState_posSemidef (d n : ℕ) :
    (physicalAntisymmetricState d n).PosSemidef :=
  (physicalTensorAntisymmetrizer_posSemidef d n).smul (inv_nonneg.mpr (Nat.cast_nonneg _))

theorem physicalAntisymmetricState_trace (d n : ℕ)
    (hcard : 0 < Fintype.card (EdgePower d n)) :
    Matrix.trace (physicalAntisymmetricState d n) = 1 := by
  rw [physicalAntisymmetricState, Matrix.trace_smul, physicalTensorAntisymmetrizer_trace]
  simp only [RCLike.real_smul_eq_coe_mul]
  have hc : (Fintype.card (EdgePower d n) : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hcard)
  exact_mod_cast inv_mul_cancel₀ hc

theorem physicalAntisymmetricState_support (d n : ℕ) :
    physicalAntisymmetricState d n = physicalTensorAntisymmetrizer d n *
      physicalAntisymmetricState d n * physicalTensorAntisymmetrizer d n := by
  simp only [physicalAntisymmetricState, Matrix.mul_smul, Matrix.smul_mul,
    physicalTensorAntisymmetrizer_idempotent]

def repeatedEdgeWord {d : ℕ} (e : Edge d) : (n : ℕ) → EdgePower d n
  | 0 => ()
  | n + 1 => (e, repeatedEdgeWord e n)

theorem edgePower_card_pos {d : ℕ} (e : Edge d) (n : ℕ) :
    0 < Fintype.card (EdgePower d n) :=
  Fintype.card_pos_iff.mpr ⟨repeatedEdgeWord e n⟩

theorem physicalAntisymmetricState_d5_density (n : ℕ) :
    (physicalAntisymmetricState 5 n).PosSemidef ∧ Matrix.trace (physicalAntisymmetricState 5 n) = 1 := by
  let e : Edge 5 := ⟨(0, 1), by decide⟩
  exact ⟨physicalAntisymmetricState_posSemidef 5 n,
    physicalAntisymmetricState_trace 5 n (edgePower_card_pos e n)⟩

theorem physicalAntisymmetricState_d4_density (n : ℕ) :
    (physicalAntisymmetricState 4 n).PosSemidef ∧ Matrix.trace (physicalAntisymmetricState 4 n) = 1 := by
  let e : Edge 4 := ⟨(0, 1), by decide⟩
  exact ⟨physicalAntisymmetricState_posSemidef 4 n,
    physicalAntisymmetricState_trace 4 n (edgePower_card_pos e n)⟩

def physicalAntisymmetricLocalState (d : ℕ) : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  (Fintype.card (Edge d) : ℝ)⁻¹ • localPhysicalAntisymmetrizer d

theorem physicalAntisymmetricState_zero (d : ℕ) : physicalAntisymmetricState d 0 = 1 := by
  simp [physicalAntisymmetricState, physicalTensorAntisymmetrizer, EdgePower]

theorem physicalAntisymmetricState_succ (d n : ℕ) :
    physicalAntisymmetricState d (n + 1) =
      (physicalAntisymmetricLocalState d ⊗ₖ physicalAntisymmetricState d n).submatrix
        (physicalRegroupEquiv d n) (physicalRegroupEquiv d n) := by
  have hc : Fintype.card (EdgePower d (n + 1)) =
      Fintype.card (Edge d) * Fintype.card (EdgePower d n) := Fintype.card_prod _ _
  ext uv wz
  change (Fintype.card (EdgePower d (n + 1)) : ℝ)⁻¹ •
      (localPhysicalAntisymmetrizer d (uv.1.1, uv.2.1) (wz.1.1, wz.2.1) *
        physicalTensorAntisymmetrizer d n (uv.1.2, uv.2.2) (wz.1.2, wz.2.2)) =
    ((Fintype.card (Edge d) : ℝ)⁻¹ •
      localPhysicalAntisymmetrizer d (uv.1.1, uv.2.1) (wz.1.1, wz.2.1)) *
    ((Fintype.card (EdgePower d n) : ℝ)⁻¹ •
      physicalTensorAntisymmetrizer d n (uv.1.2, uv.2.2) (wz.1.2, wz.2.2))
  rw [hc]
  simp only [RCLike.real_smul_eq_coe_mul, Nat.cast_mul, mul_inv_rev,
    AntisymmetricEntropyCost.rclike_complex_cast, Complex.ofReal_mul]
  push_cast
  ring

theorem physicalAntisymmetricState_d5_finiteConvexRoof_real (n : ℕ) :
    ∃ c : ℝ, (n : ℝ) ≤ c ∧
      AntisymmetricEnsembleCost.finiteConvexRoof (physicalAntisymmetricState 5 n) = (c : EReal) :=
  antisymmetric_physical_d5_finiteConvexRoof_real n _
    (physicalAntisymmetricState_d5_density n).1 (physicalAntisymmetricState_d5_density n).2
    (physicalAntisymmetricState_support 5 n)

theorem physicalAntisymmetricState_d4_finiteConvexRoof_real (n : ℕ) :
    ∃ c : ℝ, (n : ℝ) ≤ c ∧
      AntisymmetricEnsembleCost.finiteConvexRoof (physicalAntisymmetricState 4 n) = (c : EReal) :=
  antisymmetric_physical_d4_finiteConvexRoof_real n _
    (physicalAntisymmetricState_d4_density n).1 (physicalAntisymmetricState_d4_density n).2
    (physicalAntisymmetricState_support 4 n)

def physicalSlaterColumn (d n : ℕ) (x : EdgePower d n) :
    PhysicalPower d n × PhysicalPower d n → ℂ :=
  fun ab => physicalTensorIsometry d n ab x

def physicalSlaterColumnAmplitude (d n : ℕ) (x : EdgePower d n) :
    Matrix (PhysicalPower d n) (PhysicalPower d n) ℂ :=
  fun a b => physicalSlaterColumn d n x (a, b)

def physicalSlaterWordProbability (d : ℕ) :
    (n : ℕ) → EdgePower d n → PhysicalPower d n → ℝ
  | 0, _, _ => 1
  | n + 1, x, ar => slaterProbability x.1 ar.1 * physicalSlaterWordProbability d n x.2 ar.2

theorem physicalSlaterColumn_reducedLeft_diagonal (d n : ℕ) (x : EdgePower d n) :
    reducedLeft (physicalSlaterColumnAmplitude d n x) =
      Matrix.diagonal (fun a => (physicalSlaterWordProbability d n x a : ℂ)) := by
  induction n with
  | zero =>
      ext ⟨⟩ ⟨⟩
      simp [physicalSlaterColumnAmplitude, physicalSlaterColumn, physicalTensorIsometry, reducedLeft, crossLeft,
        physicalSlaterWordProbability]
  | succ n ih =>
      change reducedLeft (slaterAmplitude x.1 ⊗ₖ
        physicalSlaterColumnAmplitude d n x.2) = _
      rw [reducedLeft_kronecker, slaterAmplitude_reducedLeft, slaterOutput_eq_diagonal,
        ih x.2, Matrix.diagonal_kronecker_diagonal]
      congr 1
      funext ⟨a, r⟩
      simp [physicalSlaterWordProbability]

theorem physicalSlaterWordProbability_sum (d n : ℕ) (x : EdgePower d n) :
    ∑ a, physicalSlaterWordProbability d n x a = 1 := by
  induction n with
  | zero => simp [physicalSlaterWordProbability]
  | succ n ih =>
      simp only [physicalSlaterWordProbability, Fintype.sum_prod_type, ← Finset.mul_sum,
        ih x.2, mul_one, slaterProbability_sum]

theorem physicalSlaterWordProbability_negMulLog_sum (d n : ℕ) (x : EdgePower d n) :
    ∑ a, Real.negMulLog (physicalSlaterWordProbability d n x a) =
      (n : ℝ) * Real.log 2 := by
  induction n with
  | zero => simp [physicalSlaterWordProbability]
  | succ n ih =>
      simp only [physicalSlaterWordProbability, Fintype.sum_prod_type, Real.negMulLog_mul,
        Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum,
        physicalSlaterWordProbability_sum, one_mul, ih x.2, slaterProbability_sum,
        slaterProbability_negMulLog_sum]
      push_cast
      ring

theorem physicalSlaterColumn_normSq (d n : ℕ) (x : EdgePower d n) :
    vectorNormSq (physicalSlaterColumn d n x) = 1 := by
  have hred : partialTraceLeft (pureDensity (physicalSlaterColumn d n x)) =
      reducedLeft (physicalSlaterColumnAmplitude d n x) := by ext a b; rfl
  have ht : Matrix.trace (partialTraceLeft (pureDensity (physicalSlaterColumn d n x))) = 1 := by
    rw [hred, physicalSlaterColumn_reducedLeft_diagonal, Matrix.trace_diagonal,
      ← Complex.ofReal_sum, physicalSlaterWordProbability_sum]
    rfl
  have h := congrArg Complex.re ht
  rw [partialTraceLeft_trace, pureDensity_trace] at h
  simpa using h

theorem physicalSlaterColumn_entropy (d n : ℕ) (x : EdgePower d n) :
    physicalAliceEntropy d n (physicalSlaterColumn d n x) = (n : ℝ) := by
  have hred : partialTraceLeft (pureDensity (physicalSlaterColumn d n x)) =
      reducedLeft (physicalSlaterColumnAmplitude d n x) := by ext a b; rfl
  rw [physicalAliceEntropy, hred, physicalSlaterColumn_reducedLeft_diagonal,
    AntisymmetricEntropyCost.entropy_type_identity,
    QuantumProver.ElegantJointMeasurement.TailReference.cfc_real_diagonal _ _ Real.continuous_negMulLog, Matrix.trace_diagonal]
  simp only [Complex.re_sum, Complex.ofReal_re, physicalSlaterWordProbability_negMulLog_sum]
  exact mul_div_cancel_right₀ _ (ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 2)))

theorem physicalTensorAntisymmetrizer_eq_column_sum (d n : ℕ) :
    physicalTensorAntisymmetrizer d n =
      ∑ x, pureDensity (physicalSlaterColumn d n x) := by
  rw [← physicalTensorIsometry_range_projector]
  ext ab cd
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.sum_apply,
    pureDensity, crossDensity, physicalSlaterColumn]

def physicalEndpointEnsemble (d n : ℕ) (hcard : 0 < Fintype.card (EdgePower d n)) :
    AntisymmetricEnsembleCost.FinitePureEnsemble (physicalAntisymmetricState d n) := by
  let e : Fin (Fintype.card (EdgePower d n)) ≃ EdgePower d n :=
    (Fintype.equivFin (EdgePower d n)).symm
  let r : ℝ := (Fintype.card (EdgePower d n) : ℝ)⁻¹
  have hc : (Fintype.card (EdgePower d n) : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hcard)
  refine {
    count := Fintype.card (EdgePower d n)
    weight := fun _ => r
    weight_nonneg := fun _ => inv_nonneg.mpr (Nat.cast_nonneg _)
    weight_sum := ?_
    vector := fun j => physicalSlaterColumn d n (e j)
    normalized := fun j => physicalSlaterColumn_normSq d n (e j)
    barycenter := ?_ }
  · simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact mul_inv_cancel₀ hc
  · calc
      physicalAntisymmetricState d n =
          ∑ x, (r : ℂ) • pureDensity (physicalSlaterColumn d n x) := by
        rw [physicalAntisymmetricState, physicalTensorAntisymmetrizer_eq_column_sum,
          Finset.smul_sum]
        apply Finset.sum_congr rfl
        intro x _
        ext ab cd
        simp only [Matrix.smul_apply, RCLike.real_smul_eq_coe_mul, smul_eq_mul,
          AntisymmetricEntropyCost.rclike_complex_cast]
        rfl
      _ = _ := (e.sum_comp _).symm

theorem physicalEndpointEnsemble_average (d n : ℕ) (hcard : 0 < Fintype.card (EdgePower d n)) :
    (physicalEndpointEnsemble d n hcard).averageAliceEntropy = (n : ℝ) := by
  let E := physicalEndpointEnsemble d n hcard
  have hj (j : Fin E.count) : AntisymmetricEnsembleCost.aliceEntropy (E.vector j) = (n : ℝ) := by
    change physicalAliceEntropy d n
      (physicalSlaterColumn d n ((Fintype.equivFin (EdgePower d n)).symm j)) = (n : ℝ)
    exact physicalSlaterColumn_entropy d n _
  change (∑ j, E.weight j * AntisymmetricEnsembleCost.aliceEntropy (E.vector j)) = (n : ℝ)
  simp_rw [hj]
  rw [← Finset.sum_mul, E.weight_sum, one_mul]

theorem physicalAntisymmetricState_finiteConvexRoof_upper (d n : ℕ)
    (hcard : 0 < Fintype.card (EdgePower d n)) :
    AntisymmetricEnsembleCost.finiteConvexRoof (physicalAntisymmetricState d n) ≤ (n : EReal) := by
  let E := physicalEndpointEnsemble d n hcard
  have h := iInf_le (fun E : AntisymmetricEnsembleCost.FinitePureEnsemble
    (physicalAntisymmetricState d n) => (E.averageAliceEntropy : EReal)) E
  rw [show E.averageAliceEntropy = (n : ℝ) from physicalEndpointEnsemble_average d n hcard] at h
  exact_mod_cast h

theorem physicalAntisymmetricState_d5_finiteConvexRoof_eq (n : ℕ) :
    AntisymmetricEnsembleCost.finiteConvexRoof (physicalAntisymmetricState 5 n) = (n : EReal) := by
  let e : Edge 5 := ⟨(0, 1), by decide⟩
  exact le_antisymm (physicalAntisymmetricState_finiteConvexRoof_upper 5 n (edgePower_card_pos e n))
    (antisymmetric_physical_d5_finiteConvexRoof_lower n _ (physicalAntisymmetricState_support 5 n))

theorem physicalAntisymmetricState_d4_finiteConvexRoof_eq (n : ℕ) :
    AntisymmetricEnsembleCost.finiteConvexRoof (physicalAntisymmetricState 4 n) = (n : EReal) := by
  let e : Edge 4 := ⟨(0, 1), by decide⟩
  exact le_antisymm (physicalAntisymmetricState_finiteConvexRoof_upper 4 n (edgePower_card_pos e n))
    (antisymmetric_physical_d4_finiteConvexRoof_lower n _ (physicalAntisymmetricState_support 4 n))

theorem antisymmetric_replicaKernel_sectors (d : ℕ) :
    (antisymmetricStinespring d).replicaKernel =
      (1 / 2 : ℂ) • positiveReplicaProjector d - exteriorReplicaProjector d := by
  rw [antisymmetric_replicaKernel_coset]
  ext ij kl
  simp only [positiveReplicaProjector, symmetricReplicaProjector, Matrix.sub_apply,
    Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  ring

theorem replicaSectorContraction_add {X Y B E : Type*} [Fintype X] [Fintype Y]
    [Fintype B] [Fintype E] [DecidableEq Y]
    (N : Stinespring Y B E) (A : Matrix Y X ℂ)
    (P Q : Matrix (X × X) (X × X) ℂ) :
    replicaSectorContraction N A (P + Q) =
      replicaSectorContraction N A P + replicaSectorContraction N A Q := by
  simp [replicaSectorContraction, Matrix.transpose_add, Matrix.mul_add, Matrix.add_mul,
    Matrix.trace_add]

theorem replicaSectorContraction_sub {X Y B E : Type*} [Fintype X] [Fintype Y]
    [Fintype B] [Fintype E] [DecidableEq Y]
    (N : Stinespring Y B E) (A : Matrix Y X ℂ)
    (P Q : Matrix (X × X) (X × X) ℂ) :
    replicaSectorContraction N A (P - Q) =
      replicaSectorContraction N A P - replicaSectorContraction N A Q := by
  simp [replicaSectorContraction, Matrix.transpose_sub, Matrix.mul_sub, Matrix.sub_mul,
    Matrix.trace_sub]

theorem replicaSectorContraction_sum {K X Y B E : Type*} [Fintype K]
    [Fintype X] [Fintype Y] [Fintype B] [Fintype E] [DecidableEq Y]
    (N : Stinespring Y B E) (A : Matrix Y X ℂ)
    (P : K → Matrix (X × X) (X × X) ℂ) :
    replicaSectorContraction N A (∑ k, P k) = ∑ k, replicaSectorContraction N A (P k) := by
  simp [replicaSectorContraction, Matrix.transpose_sum, Matrix.mul_sum, Matrix.sum_mul,
    Matrix.trace_sum, Complex.re_sum]

theorem replicaSectorContraction_real_scalar {X Y B E : Type*} [Fintype X] [Fintype Y]
    [Fintype B] [Fintype E] [DecidableEq Y]
    (N : Stinespring Y B E) (A : Matrix Y X ℂ)
    (P : Matrix (X × X) (X × X) ℂ) (r : ℝ) :
    replicaSectorContraction N A ((r : ℂ) • P) = r * replicaSectorContraction N A P := by
  simp [replicaSectorContraction, Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.trace_smul, smul_eq_mul, Complex.mul_re]

theorem replicaSectorMass_add {X Y : Type*} [Fintype X] [Fintype Y]
    (A : Matrix Y X ℂ) (P Q : Matrix (X × X) (X × X) ℂ) :
    replicaSectorMass A (P + Q) = replicaSectorMass A P + replicaSectorMass A Q := by
  simp [replicaSectorMass, Matrix.transpose_add, Matrix.mul_add, Matrix.add_mul,
    Matrix.trace_add]

theorem replicaSectorMass_sub {X Y : Type*} [Fintype X] [Fintype Y]
    (A : Matrix Y X ℂ) (P Q : Matrix (X × X) (X × X) ℂ) :
    replicaSectorMass A (P - Q) = replicaSectorMass A P - replicaSectorMass A Q := by
  simp [replicaSectorMass, Matrix.transpose_sub, Matrix.mul_sub, Matrix.sub_mul,
    Matrix.trace_sub]

theorem replicaSectorMass_sum {K X Y : Type*} [Fintype K] [Fintype X] [Fintype Y]
    (A : Matrix Y X ℂ) (P : K → Matrix (X × X) (X × X) ℂ) :
    replicaSectorMass A (∑ k, P k) = ∑ k, replicaSectorMass A (P k) := by
  simp [replicaSectorMass, Matrix.transpose_sum, Matrix.mul_sum, Matrix.sum_mul,
    Matrix.trace_sum, Complex.re_sum]

theorem replicaSectorMass_real_scalar {X Y : Type*} [Fintype X] [Fintype Y]
    (A : Matrix Y X ℂ) (P : Matrix (X × X) (X × X) ℂ) (r : ℝ) :
    replicaSectorMass A ((r : ℂ) • P) = r * replicaSectorMass A P := by
  simp [replicaSectorMass, Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.trace_smul, smul_eq_mul, Complex.mul_re]

theorem antisymmetric_companion_purity_sectors (d : ℕ) {Y B E : Type*}
    [Fintype Y] [Fintype B] [Fintype E] [DecidableEq Y]
    (N : Stinespring Y B E) (Ψ : Edge d × Y → ℂ) :
    purity (((antisymmetricStinespring d).tensor N).apply (pureDensity Ψ)) =
      replicaSectorContraction N (companionCoefficient Ψ) (positiveReplicaProjector d) / 2 -
      replicaSectorContraction N (companionCoefficient Ψ) (exteriorReplicaProjector d) := by
  unfold purity
  rw [Stinespring.tensor_pure_trace_companion, antisymmetric_replicaKernel_sectors]
  change replicaSectorContraction N (companionCoefficient Ψ)
    ((1 / 2 : ℂ) • positiveReplicaProjector d - exteriorReplicaProjector d) = _
  rw [replicaSectorContraction_sub]
  have h := replicaSectorContraction_real_scalar N (companionCoefficient Ψ)
    (positiveReplicaProjector d) (1 / 2)
  norm_num at h
  rw [h]
  ring

theorem companion_symmetric_sector_contraction {X Y B E : Type*} [Fintype X]
    [Fintype Y] [Fintype B] [Fintype E] [DecidableEq X] [DecidableEq Y]
    (N : Stinespring Y B E) (A : Matrix Y X ℂ) :
    replicaSectorContraction N A (symmetricReplicaProjector X) =
      (purity (N.apply (reducedLeft A)) + purity (N.complement (reducedLeft A))) / 2 := by
  have hscale := replicaSectorContraction_real_scalar N A
    (1 + replicaSwap X) (1 / 2)
  norm_num at hscale
  rw [symmetricReplicaProjector, smul_add, hscale, replicaSectorContraction_add]
  simp only [replicaSectorContraction, Matrix.transpose_one, Matrix.mul_one,
    replicaSwap_transpose, Stinespring.companion_identity_trace,
    Stinespring.companion_swap_trace, purity]
  ring

theorem trace_kronecker_replicaSwap {X : Type*} [Fintype X] [DecidableEq X]
    (R : Matrix X X ℂ) : Matrix.trace ((R ⊗ₖ R) * replicaSwap X) = Matrix.trace (R * R) := by
  calc
    _ = ∑ ij : X × X, R ij.1 ij.2 * R ij.2 ij.1 := by
      apply Finset.sum_congr rfl
      intro ij _
      change ((R ⊗ₖ R) * replicaSwap X) ij ij = R ij.1 ij.2 * R ij.2 ij.1
      exact (matrix_mul_replicaSwap (R ⊗ₖ R) ij ij).trans (by rfl)
    _ = _ := by simp only [Fintype.sum_prod_type, Matrix.trace, Matrix.diag, Matrix.mul_apply]

theorem trace_covariance_eq_hsNormSq {X Y : Type*} [Fintype X] [Fintype Y]
    (A : Matrix Y X ℂ) : Matrix.trace (A * A.conjTranspose) = (hsNormSq A : ℂ) := by
  classical
  simpa only [reducedLeft, crossLeft_eq_mul] using MixedPurity.reducedLeft_trace A

theorem replicaSectorMass_identity {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X]
    (A : Matrix Y X ℂ) : replicaSectorMass A 1 = hsNormSq A ^ 2 := by
  simp only [replicaSectorMass, Matrix.transpose_one, Matrix.mul_one,
    Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul, Matrix.trace_kronecker,
    trace_covariance_eq_hsNormSq, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  ring

theorem replicaSectorMass_swap {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y] (A : Matrix Y X ℂ) :
    replicaSectorMass A (replicaSwap X) = purity (reducedLeft A) := by
  have hM : (A ⊗ₖ A) * replicaSwap X * (A ⊗ₖ A).conjTranspose =
      replicaSwap Y * ((A * A.conjTranspose) ⊗ₖ (A * A.conjTranspose)) := by
    rw [kronecker_replicaSwap, Matrix.mul_assoc, Matrix.conjTranspose_kronecker,
      ← Matrix.mul_kronecker_mul]
  rw [replicaSectorMass, replicaSwap_transpose, hM, Matrix.trace_mul_comm,
    trace_kronecker_replicaSwap]
  simp only [purity, reducedLeft, crossLeft_eq_mul]

theorem companion_symmetric_sector_mass {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y] (A : Matrix Y X ℂ) :
    replicaSectorMass A (symmetricReplicaProjector X) =
      (hsNormSq A ^ 2 + purity (reducedLeft A)) / 2 := by
  have hscale := replicaSectorMass_real_scalar A (1 + replicaSwap X) (1 / 2)
  norm_num at hscale
  rw [symmetricReplicaProjector, smul_add, hscale, replicaSectorMass_add,
    replicaSectorMass_identity, replicaSectorMass_swap]
  ring

theorem companion_sector_contraction_sum (d : ℕ) {Y B E : Type*}
    [Fintype Y] [Fintype B] [Fintype E] [DecidableEq Y]
    (N : Stinespring Y B E) (A : Matrix Y (Edge d) ℂ) :
    replicaSectorContraction N A (positiveReplicaProjector d) +
        replicaSectorContraction N A (exteriorReplicaProjector d) =
      (purity (N.apply (reducedLeft A)) + purity (N.complement (reducedLeft A))) / 2 := by
  rw [positiveReplicaProjector, replicaSectorContraction_sub]
  have h := companion_symmetric_sector_contraction N A
  linarith

theorem companion_sector_mass_sum (d : ℕ) {Y : Type*} [Fintype Y] [DecidableEq Y]
    (A : Matrix Y (Edge d) ℂ) :
    replicaSectorMass A (positiveReplicaProjector d) +
        replicaSectorMass A (exteriorReplicaProjector d) =
      (hsNormSq A ^ 2 + purity (reducedLeft A)) / 2 := by
  rw [positiveReplicaProjector, replicaSectorMass_sub]
  have h := companion_symmetric_sector_mass A
  linarith

def companionPuritySlack {X Y B E : Type*} [Fintype X] [Fintype Y]
    [Fintype B] [Fintype E] [DecidableEq Y]
    (N : Stinespring Y B E) (β : ℝ) (A : Matrix Y X ℂ) : ℝ :=
  β * (hsNormSq A ^ 2 + purity (reducedLeft A)) -
    (purity (N.apply (reducedLeft A)) + purity (N.complement (reducedLeft A)))

theorem companionPuritySlack_nonneg {X Y B E : Type*} [Fintype X] [Fintype Y]
    [Fintype B] [Fintype E] [DecidableEq Y]
    (N : Stinespring Y B E) (β : ℝ)
    (hbound : ∀ v : Y → ℂ, vectorNormSq v = 1 → purity (N.apply (pureDensity v)) ≤ β)
    (A : Matrix Y X ℂ) (hA : hsNormSq A = 1) : 0 ≤ companionPuritySlack N β A := by
  have h := MixedPurity.actual_purification_purity N β hbound A hA
  unfold companionPuritySlack
  rw [hA]
  norm_num
  linarith

theorem companion_sector_slack_identity (d : ℕ) {Y B E : Type*}
    [Fintype Y] [Fintype B] [Fintype E] [DecidableEq Y]
    (N : Stinespring Y B E) (β : ℝ) (A : Matrix Y (Edge d) ℂ) :
    6 * replicaSectorContraction N A (exteriorReplicaProjector d) +
        2 * companionPuritySlack N β A =
      4 * (β * replicaSectorMass A (positiveReplicaProjector d) -
        replicaSectorContraction N A (positiveReplicaProjector d)) +
      2 * (replicaSectorContraction N A (exteriorReplicaProjector d) +
        2 * β * replicaSectorMass A (exteriorReplicaProjector d)) := by
  have hc := companion_sector_contraction_sum d N A
  have hm := companion_sector_mass_sum d A
  unfold companionPuritySlack
  linear_combination 4 * hc - 4 * β * hm

theorem replicaSectorMass_fourForm {Y : Type*} [Fintype Y] {d : ℕ}
    (A : Matrix Y (Edge d) ℂ) (S : FourSet d) :
    replicaSectorMass A (pureDensity (fourFormOmega S)) =
      hsNormSq (A * fourFormMatrix S * A.transpose) := by
  have hreal : (pureDensity (fourFormOmega S)).transpose = pureDensity (fourFormOmega S) :=
    pureDensity_transpose_of_star_eq _ (fourFormOmega_star S)
  rw [replicaSectorMass, hreal]
  have hs := sandwich_crossDensity (A ⊗ₖ A) (fourFormOmega S) (fourFormOmega S)
  change (A ⊗ₖ A) * pureDensity (fourFormOmega S) * (A ⊗ₖ A).conjTranspose =
    pureDensity ((A ⊗ₖ A).mulVec (fourFormOmega S)) at hs
  rw [hs, pureDensity_trace]
  change vectorNormSq ((A ⊗ₖ A).mulVec (fun ij => fourFormMatrix S ij.1 ij.2)) = _
  rw [kronecker_mulVec_matrix]
  simp only [vectorNormSq, hsNormSq, Fintype.sum_prod_type, Complex.sq_norm]

theorem replicaSectorContraction_fourForm {Y B E : Type*} [Fintype Y]
    [Fintype B] [Fintype E] [DecidableEq Y] {d : ℕ}
    (N : Stinespring Y B E) (A : Matrix Y (Edge d) ℂ) (S : FourSet d) :
    replicaSectorContraction N A (pureDensity (fourFormOmega S)) =
      (companionCorrection N A (fourFormMatrix S)).re := by
  have hreal : (pureDensity (fourFormOmega S)).transpose = pureDensity (fourFormOmega S) :=
    pureDensity_transpose_of_star_eq _ (fourFormOmega_star S)
  rw [replicaSectorContraction, hreal]
  exact congrArg Complex.re (N.companion_correction_trace A (fourFormMatrix S))

theorem companion_fourForm_correction_retained_lower {Y B E : Type*}
    [Fintype Y] [Fintype B] [Fintype E] [DecidableEq Y]
    (N : Stinespring Y B E) (β : ℝ)
    (hbound : ∀ v : Y → ℂ, vectorNormSq v = 1 → purity (N.apply (pureDensity v)) ≤ β)
    {d : ℕ} (A : Matrix Y (Edge d) ℂ) (S : FourSet d) :
    -(4 * β / 5) * SchattenSupport.schattenOne (ExteriorSupport.orderedExterior
      (A * fourFormMatrix S * A.transpose)) ≤
      (companionCorrection N A (fourFormMatrix S)).re :=
  ActualContractionLower.actual_fourForm_replica_retained_lower N β hbound A S

theorem companion_fourForm_correction_hs_lower {Y B E : Type*}
    [Fintype Y] [Fintype B] [Fintype E] [DecidableEq Y]
    (N : Stinespring Y B E) (β : ℝ)
    (hbound : ∀ v : Y → ℂ, vectorNormSq v = 1 → purity (N.apply (pureDensity v)) ≤ β)
    {d : ℕ} (A : Matrix Y (Edge d) ℂ) (S : FourSet d) :
    -2 * β * hsNormSq (A * fourFormMatrix S * A.transpose) ≤
      (companionCorrection N A (fourFormMatrix S)).re :=
  ActualContractionLower.actual_fourForm_replica_hs_lower N β hbound A S

theorem exteriorReplicaProjector_eq_fourFormSum (d : ℕ) (hd : 2 ≤ d) :
    exteriorReplicaProjector d = (1 / 6 : ℂ) •
      ∑ S : FourSet d, pureDensity (fourFormOmega S) := by
  rw [QuantumProver.WernerEndpoint.SlaterMoments.exteriorReplicaProjector_eq_coordinateFourProjector d hd]
  rfl

theorem companion_exterior_sector_contraction (d : ℕ) (hd : 2 ≤ d) {Y B E : Type*}
    [Fintype Y] [Fintype B] [Fintype E] [DecidableEq Y]
    (N : Stinespring Y B E) (A : Matrix Y (Edge d) ℂ) :
    replicaSectorContraction N A (exteriorReplicaProjector d) =
      (1 / 6 : ℝ) * ∑ S : FourSet d, (companionCorrection N A (fourFormMatrix S)).re := by
  rw [exteriorReplicaProjector_eq_fourFormSum d hd]
  have h := replicaSectorContraction_real_scalar N A
    (∑ S : FourSet d, pureDensity (fourFormOmega S)) (1 / 6)
  simp only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] at h
  rw [h, replicaSectorContraction_sum]
  simp only [replicaSectorContraction_fourForm]

theorem companion_exterior_sector_mass (d : ℕ) (hd : 2 ≤ d) {Y : Type*} [Fintype Y]
    (A : Matrix Y (Edge d) ℂ) :
    replicaSectorMass A (exteriorReplicaProjector d) = (1 / 6 : ℝ) *
      ∑ S : FourSet d, hsNormSq (A * fourFormMatrix S * A.transpose) := by
  rw [exteriorReplicaProjector_eq_fourFormSum d hd]
  have h := replicaSectorMass_real_scalar A
    (∑ S : FourSet d, pureDensity (fourFormOmega S)) (1 / 6)
  simp only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] at h
  rw [h, replicaSectorMass_sum]
  simp only [replicaSectorMass_fourForm]

theorem companion_exterior_sector_raw_lower (d : ℕ) (hd : 2 ≤ d) {Y B E : Type*}
    [Fintype Y] [Fintype B] [Fintype E] [DecidableEq Y]
    (N : Stinespring Y B E) (β : ℝ)
    (hbound : ∀ v : Y → ℂ, vectorNormSq v = 1 → purity (N.apply (pureDensity v)) ≤ β)
    (A : Matrix Y (Edge d) ℂ) :
    -2 * β * replicaSectorMass A (exteriorReplicaProjector d) ≤
      replicaSectorContraction N A (exteriorReplicaProjector d) := by
  have hsum : (∑ S : FourSet d, -2 * β * hsNormSq (A * fourFormMatrix S * A.transpose)) ≤
      ∑ S : FourSet d, (companionCorrection N A (fourFormMatrix S)).re := by
    apply Finset.sum_le_sum
    intro S _
    exact companion_fourForm_correction_hs_lower N β hbound A S
  rw [← Finset.mul_sum] at hsum
  rw [companion_exterior_sector_mass d hd, companion_exterior_sector_contraction d hd]
  nlinarith

theorem companion_six_exterior_plus_twice_slack_nonneg (d : ℕ) (hd : 2 ≤ d)
    {Y B E : Type*} [Fintype Y] [Fintype B] [Fintype E] [DecidableEq Y]
    (N : Stinespring Y B E) (β : ℝ)
    (hbound : ∀ v : Y → ℂ, vectorNormSq v = 1 → purity (N.apply (pureDensity v)) ≤ β)
    (A : Matrix Y (Edge d) ℂ) :
    0 ≤ 6 * replicaSectorContraction N A (exteriorReplicaProjector d) +
      2 * companionPuritySlack N β A := by
  have hp := QuantumProver.WernerEndpoint.SlaterMoments.positiveSector_companion_bound hd N A β hbound
  have hw := companion_exterior_sector_raw_lower d hd N β hbound A
  rw [companion_sector_slack_identity]
  linarith

theorem companion_total_correction_slack_lower (d : ℕ) (hd : 2 ≤ d)
    {Y B E : Type*} [Fintype Y] [Fintype B] [Fintype E] [DecidableEq Y]
    (N : Stinespring Y B E) (β : ℝ)
    (hbound : ∀ v : Y → ℂ, vectorNormSq v = 1 → purity (N.apply (pureDensity v)) ≤ β)
    (A : Matrix Y (Edge d) ℂ) :
    (∑ S : FourSet d, (companionCorrection N A (fourFormMatrix S)).re) / 2 ≤
      (∑ S : FourSet d, (companionCorrection N A (fourFormMatrix S)).re) +
        companionPuritySlack N β A := by
  have h := companion_six_exterior_plus_twice_slack_nonneg d hd N β hbound A
  rw [companion_exterior_sector_contraction d hd] at h
  nlinarith

theorem exteriorReplicaProjector_eq_zero_of_small (d : ℕ) (hd : d ≤ 3) :
    exteriorReplicaProjector d = 0 := by
  have ht : Matrix.trace (exteriorReplicaProjector d) = 0 := by
    rw [exteriorReplicaProjector_trace]
    interval_cases d <;> norm_num
  apply Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp
  rw [exteriorReplicaProjector_hermitian, exteriorReplicaProjector_idempotent, ht]

theorem covariance_purity_of_subsingleton_columns {X Y : Type*}
    [Fintype X] [Fintype Y] [Subsingleton X] (A : Matrix Y X ℂ) :
    purity (reducedLeft A) = hsNormSq A ^ 2 := by
  have he : ExteriorSupport.orderedExterior A = 0 := by
    ext ij ef
    have hef : ef.1 = ef.2 := Subsingleton.elim _ _
    simp [ExteriorSupport.orderedExterior, hef]
  have hz : hsNormSq (0 : Matrix (Y × Y) (X × X) ℂ) = 0 := by
    simp [hsNormSq]
  have h := ExteriorSupport.orderedExterior_hsNormSq A
  rw [he, hz] at h
  linarith

theorem companionCoefficient_d2_marginal_purity {Y : Type*} [Fintype Y]
    (Ψ : Edge 2 × Y → ℂ) (hΨ : vectorNormSq Ψ = 1) :
    purity (reducedLeft (companionCoefficient Ψ)) = 1 := by
  letI : Subsingleton (Edge 2) := Fintype.card_le_one_iff_subsingleton.mp (by
    rw [QuantumProver.WernerEndpoint.SlaterMoments.edge_card_choose]
    norm_num)
  rw [covariance_purity_of_subsingleton_columns, companionCoefficient_hsNormSq, hΨ]
  norm_num

theorem antisymmetric_small_companion_purity_le {d : ℕ} (hd : 2 ≤ d) (hsmall : d ≤ 3)
    {Y B E : Type*} [Fintype Y] [Fintype B] [Fintype E] [DecidableEq Y]
    (N : Stinespring Y B E) (β : ℝ)
    (hbound : ∀ v : Y → ℂ, vectorNormSq v = 1 → purity (N.apply (pureDensity v)) ≤ β)
    (Ψ : Edge d × Y → ℂ) (hΨ : vectorNormSq Ψ = 1) :
    purity (((antisymmetricStinespring d).tensor N).apply (pureDensity Ψ)) ≤
      β * (1 + purity (reducedLeft (companionCoefficient Ψ))) / 4 := by
  have hΓ := exteriorReplicaProjector_eq_zero_of_small d hsmall
  have hw : replicaSectorContraction N (companionCoefficient Ψ)
      (exteriorReplicaProjector d) = 0 := by
    rw [hΓ]
    simp [replicaSectorContraction]
  have hp := QuantumProver.WernerEndpoint.SlaterMoments.positiveSector_companion_bound hd N
    (companionCoefficient Ψ) β hbound
  rw [positiveReplicaProjector, hΓ, sub_zero,
    companion_symmetric_sector_mass, companionCoefficient_hsNormSq, hΨ] at hp
  rw [antisymmetric_companion_purity_sectors, hw, sub_zero,
    positiveReplicaProjector, hΓ, sub_zero]
  nlinarith

theorem antisymmetric_d3_companion_purity_strong {Y B E : Type*}
    [Fintype Y] [Fintype B] [Fintype E] [DecidableEq Y]
    (N : Stinespring Y B E) (β : ℝ)
    (hbound : ∀ v : Y → ℂ, vectorNormSq v = 1 → purity (N.apply (pureDensity v)) ≤ β)
    (Ψ : Edge 3 × Y → ℂ) (hΨ : vectorNormSq Ψ = 1) :
    purity (((antisymmetricStinespring 3).tensor N).apply (pureDensity Ψ)) ≤
      β / 2 - β / 4 * (1 - purity (reducedLeft (companionCoefficient Ψ))) := by
  have h := antisymmetric_small_companion_purity_le (by norm_num : 2 ≤ 3)
    (by norm_num : 3 ≤ 3) N β hbound Ψ hΨ
  nlinarith

theorem antisymmetric_d2_companion_purity_strong {Y B E : Type*}
    [Fintype Y] [Fintype B] [Fintype E] [DecidableEq Y]
    (N : Stinespring Y B E) (β : ℝ)
    (hbound : ∀ v : Y → ℂ, vectorNormSq v = 1 → purity (N.apply (pureDensity v)) ≤ β)
    (Ψ : Edge 2 × Y → ℂ) (hΨ : vectorNormSq Ψ = 1) :
    purity (((antisymmetricStinespring 2).tensor N).apply (pureDensity Ψ)) ≤
      β / 2 - β / 3 * (1 - purity (reducedLeft (companionCoefficient Ψ))) := by
  have h := antisymmetric_small_companion_purity_le (by norm_num : 2 ≤ 2)
    (by norm_num : 2 ≤ 3) N β hbound Ψ hΨ
  rw [companionCoefficient_d2_marginal_purity Ψ hΨ] at h ⊢
  nlinarith

theorem antisymmetric_small_companion_purity_le_half {d : ℕ}
    (hd : 2 ≤ d) (hsmall : d ≤ 3) {Y B E : Type*}
    [Fintype Y] [Fintype B] [Fintype E] [DecidableEq Y]
    (N : Stinespring Y B E) (β : ℝ)
    (hbound : ∀ v : Y → ℂ, vectorNormSq v = 1 → purity (N.apply (pureDensity v)) ≤ β)
    (Ψ : Edge d × Y → ℂ) (hΨ : vectorNormSq Ψ = 1) :
    purity (((antisymmetricStinespring d).tensor N).apply (pureDensity Ψ)) ≤ β / 2 := by
  have h := antisymmetric_small_companion_purity_le hd hsmall N β hbound Ψ hΨ
  have hb := companion_purity_bound_nonneg N β hbound Ψ hΨ
  have hs := normalized_coefficient_purity_le_one (companionCoefficient Ψ)
    (by rw [companionCoefficient_hsNormSq, hΨ])
  have hbs := mul_le_mul_of_nonneg_left hs hb
  nlinarith

theorem endpoint_join_arithmetic (d : ℕ) (β s q C Δ P : ℝ)
    (hpur : 4 * P = q - C)
    (hslack : Δ = β * (1 + s) - q)
    (hphase : 0 ≤ C + 2 * Δ)
    (hretained : -2 * β * (((d : ℝ) - 3) / ((d : ℝ) + 1)) * (1 - s) ≤ C) :
    P ≤ β / 2 - β / ((d : ℝ) + 1) * (1 - s) := by
  have hd : (d : ℝ) + 1 ≠ 0 := ne_of_gt (by positivity)
  calc
    P ≤ β * (1 + s) / 4 - C / 8 := by linarith
    _ ≤ β * (1 + s) / 4 +
        β * (((d : ℝ) - 3) / ((d : ℝ) + 1)) * (1 - s) / 4 := by nlinarith
    _ = β / 2 - β / ((d : ℝ) + 1) * (1 - s) := by field_simp; ring

abbrev CompanionHalfStep (d : ℕ) : Prop :=
  ∀ {Y B E : Type} [Fintype Y] [Fintype B] [Fintype E] [DecidableEq Y],
    ∀ (N : Stinespring Y B E) (β : ℝ),
      (∀ v : Y → ℂ, vectorNormSq v = 1 → purity (N.apply (pureDensity v)) ≤ β) →
      ∀ Ψ : Edge d × Y → ℂ, vectorNormSq Ψ = 1 →
        purity (((antisymmetricStinespring d).tensor N).apply (pureDensity Ψ)) ≤ β / 2

theorem companionHalfStep_small (d : ℕ) (hd : 2 ≤ d) (hsmall : d ≤ 3) :
    CompanionHalfStep d := by
  intro Y B E _ _ _ _ N β hbound Ψ hΨ
  exact antisymmetric_small_companion_purity_le_half hd hsmall N β hbound Ψ hΨ

theorem antisymmetricPower_purity_upper_of_companion (d : ℕ)
    (hstep : CompanionHalfStep d) (n : ℕ) (u : EdgePower d n → ℂ)
    (hu : vectorNormSq u = 1) :
    purity ((antisymmetricPowerStinespring d n).apply (pureDensity u)) ≤ (1 / 2 : ℝ) ^ n := by
  induction n with
  | zero =>
      rw [antisymmetricPower_zero_output _ _ hu]
      norm_num [purity]
  | succ n ih =>
      change purity (((antisymmetricStinespring d).tensor (antisymmetricPowerStinespring d n)).apply
        (pureDensity u)) ≤ _
      have h := hstep (antisymmetricPowerStinespring d n) ((1 / 2 : ℝ) ^ n)
        (fun w hw => ih w hw) u hu
      calc
        _ ≤ (1 / 2 : ℝ) ^ n / 2 := h
        _ = (1 / 2 : ℝ) ^ (n + 1) := by rw [pow_succ]; ring

theorem antisymmetricPower_purity_optimum_of_companion (d : ℕ)
    (hstep : CompanionHalfStep d) (e : Edge d) (n : ℕ) :
    (∀ u : EdgePower d n → ℂ, vectorNormSq u = 1 →
      purity ((antisymmetricPowerStinespring d n).apply (pureDensity u)) ≤ (1 / 2 : ℝ) ^ n) ∧
    ∃ u : EdgePower d n → ℂ, vectorNormSq u = 1 ∧
      purity ((antisymmetricPowerStinespring d n).apply (pureDensity u)) = (1 / 2 : ℝ) ^ n := by
  constructor
  · exact antisymmetricPower_purity_upper_of_companion d hstep n
  · exact ⟨tensorSlaterInput e n, tensorSlaterInput_normSq e n,
      antisymmetricPower_tensorSlater_purity e n⟩

theorem antisymmetric_physical_purity_upper_of_companion (d : ℕ)
    (hstep : CompanionHalfStep d) (n : ℕ)
    (ψ : PhysicalPower d n × PhysicalPower d n → ℂ) (hunit : vectorNormSq ψ = 1)
    (hψ : HasAntisymmetricSupport d n (fun a b => ψ (a, b))) :
    purity (partialTraceLeft (pureDensity ψ)) ≤ (1 / 2 : ℝ) ^ n := by
  rw [physical_partialTrace_eq_channel d n ψ hψ]
  apply antisymmetricPower_purity_upper_of_companion d hstep
  rw [physicalCoefficientPreimage_normSq d n ψ hψ, hunit]

theorem antisymmetric_physical_projector_purity_upper_of_companion (d : ℕ)
    (hstep : CompanionHalfStep d) (n : ℕ)
    (ψ : PhysicalPower d n × PhysicalPower d n → ℂ) (hunit : vectorNormSq ψ = 1)
    (hψ : (physicalTensorAntisymmetrizer d n).mulVec ψ = ψ) :
    purity (partialTraceLeft (pureDensity ψ)) ≤ (1 / 2 : ℝ) ^ n :=
  antisymmetric_physical_purity_upper_of_companion d hstep n ψ hunit
    ((physicalTensorAntisymmetrizer_fix_iff_support d n ψ).mp hψ)

theorem antisymmetric_physical_purity_optimum_of_companion (d : ℕ)
    (hstep : CompanionHalfStep d) (e : Edge d) (n : ℕ) :
    (∀ ψ : PhysicalPower d n × PhysicalPower d n → ℂ, vectorNormSq ψ = 1 →
      HasAntisymmetricSupport d n (fun a b => ψ (a, b)) →
      purity (partialTraceLeft (pureDensity ψ)) ≤ (1 / 2 : ℝ) ^ n) ∧
    ∃ ψ : PhysicalPower d n × PhysicalPower d n → ℂ, vectorNormSq ψ = 1 ∧
      HasAntisymmetricSupport d n (fun a b => ψ (a, b)) ∧
      purity (partialTraceLeft (pureDensity ψ)) = (1 / 2 : ℝ) ^ n := by
  constructor
  · exact antisymmetric_physical_purity_upper_of_companion d hstep n
  · exact ⟨physicalTensorSlaterVector e n, physicalTensorSlaterVector_normSq e n,
      physicalTensorSlaterVector_support e n, physicalTensorSlaterVector_purity e n⟩

theorem antisymmetric_physical_entropy_lower_of_companion (d : ℕ)
    (hstep : CompanionHalfStep d) (n : ℕ)
    (ψ : PhysicalPower d n × PhysicalPower d n → ℂ) (hunit : vectorNormSq ψ = 1)
    (hψ : HasAntisymmetricSupport d n (fun a b => ψ (a, b))) :
    (n : ℝ) ≤ physicalAliceEntropy d n ψ :=
  physical_entropy_ge_nat_of_purity d n ψ hunit
    (antisymmetric_physical_purity_upper_of_companion d hstep n ψ hunit hψ)

theorem antisymmetric_physical_entropy_optimum_of_companion (d : ℕ)
    (hstep : CompanionHalfStep d) (e : Edge d) (n : ℕ) :
    (∀ ψ : PhysicalPower d n × PhysicalPower d n → ℂ, vectorNormSq ψ = 1 →
      HasAntisymmetricSupport d n (fun a b => ψ (a, b)) →
      (n : ℝ) ≤ physicalAliceEntropy d n ψ) ∧
    ∃ ψ : PhysicalPower d n × PhysicalPower d n → ℂ, vectorNormSq ψ = 1 ∧
      HasAntisymmetricSupport d n (fun a b => ψ (a, b)) ∧
      physicalAliceEntropy d n ψ = (n : ℝ) := by
  constructor
  · exact antisymmetric_physical_entropy_lower_of_companion d hstep n
  · exact ⟨physicalTensorSlaterVector e n, physicalTensorSlaterVector_normSq e n,
      physicalTensorSlaterVector_support e n, physicalTensorSlaterVector_entropy e n⟩

theorem antisymmetric_physical_ensemble_entropy_lower_of_companion (d : ℕ)
    (hstep : CompanionHalfStep d) (n : ℕ)
    (ρ : Matrix (PhysicalPower d n × PhysicalPower d n)
      (PhysicalPower d n × PhysicalPower d n) ℂ)
    (E : AntisymmetricEnsembleCost.FinitePureEnsemble ρ)
    (hsupp : ρ = physicalTensorAntisymmetrizer d n * ρ * physicalTensorAntisymmetrizer d n) :
    (n : ℝ) ≤ E.averageAliceEntropy :=
  E.average_entropy_lower_from_range_purity (physicalTensorAntisymmetrizer d n)
    (physicalTensorAntisymmetrizer_idempotent d n) hsupp n
    (antisymmetric_physical_projector_purity_upper_of_companion d hstep n)

theorem antisymmetric_physical_finiteConvexRoof_lower_of_companion (d : ℕ)
    (hstep : CompanionHalfStep d) (n : ℕ)
    (ρ : Matrix (PhysicalPower d n × PhysicalPower d n)
      (PhysicalPower d n × PhysicalPower d n) ℂ)
    (hsupp : ρ = physicalTensorAntisymmetrizer d n * ρ * physicalTensorAntisymmetrizer d n) :
    (n : EReal) ≤ AntisymmetricEnsembleCost.finiteConvexRoof ρ :=
  AntisymmetricEnsembleCost.finiteConvexRoof_lower_from_range_purity ρ
    (physicalTensorAntisymmetrizer d n) (physicalTensorAntisymmetrizer_idempotent d n)
    hsupp n (antisymmetric_physical_projector_purity_upper_of_companion d hstep n)

theorem antisymmetric_physical_finiteConvexRoof_real_of_companion (d : ℕ)
    (hstep : CompanionHalfStep d) (n : ℕ)
    (ρ : Matrix (PhysicalPower d n × PhysicalPower d n)
      (PhysicalPower d n × PhysicalPower d n) ℂ)
    (hρ : ρ.PosSemidef) (htrace : Matrix.trace ρ = 1)
    (hsupp : ρ = physicalTensorAntisymmetrizer d n * ρ * physicalTensorAntisymmetrizer d n) :
    ∃ c : ℝ, (n : ℝ) ≤ c ∧ AntisymmetricEnsembleCost.finiteConvexRoof ρ = (c : EReal) :=
  DensityEnsembleExistence.density_supported_finiteConvexRoof_lower ρ hρ htrace
    (physicalTensorAntisymmetrizer d n) (physicalTensorAntisymmetrizer_idempotent d n)
    hsupp n (antisymmetric_physical_projector_purity_upper_of_companion d hstep n)

theorem physicalAntisymmetricState_finiteConvexRoof_eq_of_companion (d : ℕ)
    (hstep : CompanionHalfStep d) (e : Edge d) (n : ℕ) :
    AntisymmetricEnsembleCost.finiteConvexRoof (physicalAntisymmetricState d n) = (n : EReal) := by
  exact le_antisymm (physicalAntisymmetricState_finiteConvexRoof_upper d n (edgePower_card_pos e n))
    (antisymmetric_physical_finiteConvexRoof_lower_of_companion d hstep n _
      (physicalAntisymmetricState_support d n))

def firstEndpointEdge (d : ℕ) (hd : 2 ≤ d) : Edge d :=
  ⟨(⟨0, by omega⟩, ⟨1, by omega⟩), by change (0 : ℕ) < 1; omega⟩

theorem physicalAntisymmetricState_density (d : ℕ) (hd : 2 ≤ d) (n : ℕ) :
    (physicalAntisymmetricState d n).PosSemidef ∧ Matrix.trace (physicalAntisymmetricState d n) = 1 :=
  ⟨physicalAntisymmetricState_posSemidef d n,
    physicalAntisymmetricState_trace d n (edgePower_card_pos (firstEndpointEdge d hd) n)⟩

theorem antisymmetricPower_d2_purity_upper (n : ℕ) (u : EdgePower 2 n → ℂ)
    (hu : vectorNormSq u = 1) :
    purity ((antisymmetricPowerStinespring 2 n).apply (pureDensity u)) ≤ (1 / 2 : ℝ) ^ n :=
  antisymmetricPower_purity_upper_of_companion 2 (companionHalfStep_small 2 (by omega) (by omega)) n u hu

theorem antisymmetricPower_d3_purity_upper (n : ℕ) (u : EdgePower 3 n → ℂ)
    (hu : vectorNormSq u = 1) :
    purity ((antisymmetricPowerStinespring 3 n).apply (pureDensity u)) ≤ (1 / 2 : ℝ) ^ n :=
  antisymmetricPower_purity_upper_of_companion 3 (companionHalfStep_small 3 (by omega) (by omega)) n u hu

theorem antisymmetric_physical_d2_purity_optimum (n : ℕ) :
    (∀ ψ : PhysicalPower 2 n × PhysicalPower 2 n → ℂ, vectorNormSq ψ = 1 →
      HasAntisymmetricSupport 2 n (fun a b => ψ (a, b)) →
      purity (partialTraceLeft (pureDensity ψ)) ≤ (1 / 2 : ℝ) ^ n) ∧
    ∃ ψ : PhysicalPower 2 n × PhysicalPower 2 n → ℂ, vectorNormSq ψ = 1 ∧
      HasAntisymmetricSupport 2 n (fun a b => ψ (a, b)) ∧
      purity (partialTraceLeft (pureDensity ψ)) = (1 / 2 : ℝ) ^ n :=
  antisymmetric_physical_purity_optimum_of_companion 2
    (companionHalfStep_small 2 (by omega) (by omega)) (firstEndpointEdge 2 (by omega)) n

theorem antisymmetric_physical_d3_purity_optimum (n : ℕ) :
    (∀ ψ : PhysicalPower 3 n × PhysicalPower 3 n → ℂ, vectorNormSq ψ = 1 →
      HasAntisymmetricSupport 3 n (fun a b => ψ (a, b)) →
      purity (partialTraceLeft (pureDensity ψ)) ≤ (1 / 2 : ℝ) ^ n) ∧
    ∃ ψ : PhysicalPower 3 n × PhysicalPower 3 n → ℂ, vectorNormSq ψ = 1 ∧
      HasAntisymmetricSupport 3 n (fun a b => ψ (a, b)) ∧
      purity (partialTraceLeft (pureDensity ψ)) = (1 / 2 : ℝ) ^ n :=
  antisymmetric_physical_purity_optimum_of_companion 3
    (companionHalfStep_small 3 (by omega) (by omega)) (firstEndpointEdge 3 (by omega)) n

theorem antisymmetric_physical_d2_entropy_optimum (n : ℕ) :
    (∀ ψ : PhysicalPower 2 n × PhysicalPower 2 n → ℂ, vectorNormSq ψ = 1 →
      HasAntisymmetricSupport 2 n (fun a b => ψ (a, b)) →
      (n : ℝ) ≤ physicalAliceEntropy 2 n ψ) ∧
    ∃ ψ : PhysicalPower 2 n × PhysicalPower 2 n → ℂ, vectorNormSq ψ = 1 ∧
      HasAntisymmetricSupport 2 n (fun a b => ψ (a, b)) ∧
      physicalAliceEntropy 2 n ψ = (n : ℝ) :=
  antisymmetric_physical_entropy_optimum_of_companion 2
    (companionHalfStep_small 2 (by omega) (by omega)) (firstEndpointEdge 2 (by omega)) n

theorem antisymmetric_physical_d3_entropy_optimum (n : ℕ) :
    (∀ ψ : PhysicalPower 3 n × PhysicalPower 3 n → ℂ, vectorNormSq ψ = 1 →
      HasAntisymmetricSupport 3 n (fun a b => ψ (a, b)) →
      (n : ℝ) ≤ physicalAliceEntropy 3 n ψ) ∧
    ∃ ψ : PhysicalPower 3 n × PhysicalPower 3 n → ℂ, vectorNormSq ψ = 1 ∧
      HasAntisymmetricSupport 3 n (fun a b => ψ (a, b)) ∧
      physicalAliceEntropy 3 n ψ = (n : ℝ) :=
  antisymmetric_physical_entropy_optimum_of_companion 3
    (companionHalfStep_small 3 (by omega) (by omega)) (firstEndpointEdge 3 (by omega)) n

theorem physicalAntisymmetricState_d2_finiteConvexRoof_eq (n : ℕ) :
    AntisymmetricEnsembleCost.finiteConvexRoof (physicalAntisymmetricState 2 n) = (n : EReal) :=
  physicalAntisymmetricState_finiteConvexRoof_eq_of_companion 2
    (companionHalfStep_small 2 (by omega) (by omega)) (firstEndpointEdge 2 (by omega)) n

theorem physicalAntisymmetricState_d3_finiteConvexRoof_eq (n : ℕ) :
    AntisymmetricEnsembleCost.finiteConvexRoof (physicalAntisymmetricState 3 n) = (n : EReal) :=
  physicalAntisymmetricState_finiteConvexRoof_eq_of_companion 3
    (companionHalfStep_small 3 (by omega) (by omega)) (firstEndpointEdge 3 (by omega)) n

theorem physicalPower_card (d n : ℕ) : Fintype.card (PhysicalPower d n) = d ^ n := by
  induction n with
  | zero => simp [PhysicalPower]
  | succ n ih =>
      change Fintype.card (Fin d × PhysicalPower d n) = d ^ (n + 1)
      rw [Fintype.card_prod, Fintype.card_fin, ih, pow_succ]
      ring

def bellPairPowerVector (n : ℕ) : PhysicalPower 2 n × PhysicalPower 2 n → ℂ :=
  fun ab => wedgeScale ^ n * (if ab.1 = ab.2 then 1 else 0)

theorem bellPairPowerVector_zero : bellPairPowerVector 0 = fun _ => 1 := by
  ext ⟨a, b⟩
  cases a
  cases b
  simp [bellPairPowerVector]

theorem bellPairPowerVector_succ (n : ℕ) (a b : Fin 2)
    (r s : PhysicalPower 2 n) :
    bellPairPowerVector (n + 1) ((a, r), (b, s)) =
      (wedgeScale * (if a = b then 1 else 0)) * bellPairPowerVector n (r, s) := by
  simp only [bellPairPowerVector, Prod.mk.injEq, endpointIndicator_and, pow_succ]
  ring

theorem equalLabel_partialTrace {X : Type*} [Fintype X] [DecidableEq X] (c : ℂ) :
    partialTraceLeft (pureDensity (fun ab : X × X => c * (if ab.1 = ab.2 then 1 else 0))) =
      Matrix.diagonal (fun _ => c * star c) := by
  ext a b
  by_cases hab : a = b
  · subst b
    simp [partialTraceLeft, pureDensity, crossDensity, mul_ite, ite_mul]
  · simp [partialTraceLeft, pureDensity, crossDensity, mul_ite, ite_mul, hab, Ne.symm hab]

theorem bellPairPowerVector_partialTrace (n : ℕ) :
    partialTraceLeft (pureDensity (bellPairPowerVector n)) =
      Matrix.diagonal (fun _ => ((1 / 2 : ℝ) ^ n : ℂ)) := by
  change partialTraceLeft (pureDensity
    (fun ab : PhysicalPower 2 n × PhysicalPower 2 n =>
      wedgeScale ^ n * (if ab.1 = ab.2 then 1 else 0))) = _
  rw [equalLabel_partialTrace]
  have hstar : star wedgeScale = wedgeScale := by simp [wedgeScale]
  have hscalar : wedgeScale ^ n * star (wedgeScale ^ n) = ((1 / 2 : ℝ) ^ n : ℂ) := by
    rw [star_pow, hstar, ← mul_pow, wedgeScale_square]
    push_cast
    rfl
  simp only [hscalar]

theorem slaterProbability_firstEndpointEdge_two (a : Fin 2) :
    slaterProbability (firstEndpointEdge 2 (by omega)) a = 1 / 2 := by
  by_cases ha : a = 0
  · subst a
    norm_num [slaterProbability, firstEndpointEdge]
  · have hb : a = 1 := by
      apply Fin.ext
      have hne : a.val ≠ 0 := by
        intro h
        exact ha (Fin.ext h)
      omega
    subst a
    norm_num [slaterProbability, firstEndpointEdge]

theorem physicalSlaterWordProbability_two_repeat (n : ℕ) (a : PhysicalPower 2 n) :
    physicalSlaterWordProbability 2 n
      (repeatedEdgeWord (firstEndpointEdge 2 (by omega)) n) a = (1 / 2 : ℝ) ^ n := by
  induction n with
  | zero => simp [physicalSlaterWordProbability]
  | succ n ih =>
      rcases a with ⟨a, ar⟩
      simp only [physicalSlaterWordProbability, repeatedEdgeWord,
        slaterProbability_firstEndpointEdge_two, ih ar]
      rw [pow_succ]
      ring

theorem bellPairPowerVector_partialTrace_eq_slater (n : ℕ) :
    partialTraceLeft (pureDensity (bellPairPowerVector n)) =
      partialTraceLeft (pureDensity (physicalSlaterColumn 2 n
        (repeatedEdgeWord (firstEndpointEdge 2 (by omega)) n))) := by
  have hred : partialTraceLeft (pureDensity (physicalSlaterColumn 2 n
      (repeatedEdgeWord (firstEndpointEdge 2 (by omega)) n))) =
      reducedLeft (physicalSlaterColumnAmplitude 2 n
        (repeatedEdgeWord (firstEndpointEdge 2 (by omega)) n)) := by
    ext a b
    rfl
  rw [bellPairPowerVector_partialTrace, hred, physicalSlaterColumn_reducedLeft_diagonal]
  simp only [physicalSlaterWordProbability_two_repeat, Complex.ofReal_pow]

theorem bellPairPowerVector_normSq (n : ℕ) : vectorNormSq (bellPairPowerVector n) = 1 := by
  have ht := congrArg Matrix.trace (bellPairPowerVector_partialTrace_eq_slater n)
  rw [partialTraceLeft_trace, partialTraceLeft_trace, pureDensity_trace, pureDensity_trace,
    physicalSlaterColumn_normSq] at ht
  exact_mod_cast ht

theorem bellPairPowerVector_alice_entropy (n : ℕ) :
    AntisymmetricEntropyCost.vonNeumannEntropyBits
      (partialTraceLeft (pureDensity (bellPairPowerVector n))) = (n : ℝ) := by
  rw [bellPairPowerVector_partialTrace_eq_slater]
  exact physicalSlaterColumn_entropy 2 n
    (repeatedEdgeWord (firstEndpointEdge 2 (by omega)) n)

theorem antisymmetric_companion_purity_fourForm (d : ℕ) (hd : 2 ≤ d)
    {Y B E : Type*} [Fintype Y] [Fintype B] [Fintype E] [DecidableEq Y]
    (N : Stinespring Y B E) (Ψ : Edge d × Y → ℂ) :
    4 * purity (((antisymmetricStinespring d).tensor N).apply (pureDensity Ψ)) =
      purity (N.apply (companionMarginal Ψ)) + purity (N.complement (companionMarginal Ψ)) -
        ∑ S : FourSet d, (companionCorrection N (companionCoefficient Ψ) (fourFormMatrix S)).re := by
  have hp := antisymmetric_companion_purity_sectors d N Ψ
  have hs := companion_sector_contraction_sum d N (companionCoefficient Ψ)
  have hΓ := companion_exterior_sector_contraction d hd N (companionCoefficient Ψ)
  change 4 * purity (((antisymmetricStinespring d).tensor N).apply (pureDensity Ψ)) =
    purity (N.apply (reducedLeft (companionCoefficient Ψ))) +
      purity (N.complement (reducedLeft (companionCoefficient Ψ))) - _
  linarith

theorem companion_fourForm_sum_haar_lower {d : ℕ} (hd : 4 ≤ d)
    {Y B E : Type*} [Fintype Y] [Fintype B] [Fintype E] [DecidableEq Y]
    (N : Stinespring Y B E) (β : ℝ)
    (hbound : ∀ v : Y → ℂ, vectorNormSq v = 1 → purity (N.apply (pureDensity v)) ≤ β)
    (Ψ : Edge d × Y → ℂ) (hΨ : vectorNormSq Ψ = 1) :
    -2 * β * (((d : ℝ) - 3) / ((d : ℝ) + 1)) * (1 - purity (companionMarginal Ψ)) ≤
      ∑ S : FourSet d, (companionCorrection N (companionCoefficient Ψ) (fourFormMatrix S)).re := by
  simpa only [companionCorrection, companionMarginal] using
    ExteriorHaar.actual_fourForm_sum_haar_lower hd N β hbound (companionCoefficient Ψ)
      (by rw [companionCoefficient_hsNormSq, hΨ])

theorem antisymmetric_large_companion_purity_strong {d : ℕ} (hd : 4 ≤ d)
    {Y B E : Type*} [Fintype Y] [Fintype B] [Fintype E] [DecidableEq Y]
    (N : Stinespring Y B E) (β : ℝ)
    (hbound : ∀ v : Y → ℂ, vectorNormSq v = 1 → purity (N.apply (pureDensity v)) ≤ β)
    (Ψ : Edge d × Y → ℂ) (hΨ : vectorNormSq Ψ = 1) :
    purity (((antisymmetricStinespring d).tensor N).apply (pureDensity Ψ)) ≤
      β / 2 - β / ((d : ℝ) + 1) * (1 - purity (companionMarginal Ψ)) := by
  have hd2 : 2 ≤ d := by omega
  let A := companionCoefficient Ψ
  have hA : hsNormSq A = 1 := by
    dsimp only [A]
    rw [companionCoefficient_hsNormSq, hΨ]
  have hphase : 0 ≤ (∑ S : FourSet d, (companionCorrection N A (fourFormMatrix S)).re) +
      2 * companionPuritySlack N β A := by
    have h := companion_six_exterior_plus_twice_slack_nonneg d hd2 N β hbound A
    rw [companion_exterior_sector_contraction d hd2] at h
    linarith
  exact endpoint_join_arithmetic d β (purity (companionMarginal Ψ))
    (purity (N.apply (companionMarginal Ψ)) + purity (N.complement (companionMarginal Ψ)))
    (∑ S : FourSet d, (companionCorrection N A (fourFormMatrix S)).re)
    (companionPuritySlack N β A)
    (purity (((antisymmetricStinespring d).tensor N).apply (pureDensity Ψ)))
    (antisymmetric_companion_purity_fourForm d hd2 N Ψ)
    (by simp only [companionPuritySlack, hA, one_pow, companionMarginal, A])
    hphase (companion_fourForm_sum_haar_lower hd N β hbound Ψ hΨ)

theorem antisymmetric_companion_purity_strong {d : ℕ} (hd : 2 ≤ d)
    {Y B E : Type*} [Fintype Y] [Fintype B] [Fintype E] [DecidableEq Y]
    (N : Stinespring Y B E) (β : ℝ)
    (hbound : ∀ v : Y → ℂ, vectorNormSq v = 1 → purity (N.apply (pureDensity v)) ≤ β)
    (Ψ : Edge d × Y → ℂ) (hΨ : vectorNormSq Ψ = 1) :
    purity (((antisymmetricStinespring d).tensor N).apply (pureDensity Ψ)) ≤
      β / 2 - β / ((d : ℝ) + 1) * (1 - purity (companionMarginal Ψ)) := by
  by_cases hd4 : 4 ≤ d
  · exact antisymmetric_large_companion_purity_strong hd4 N β hbound Ψ hΨ
  · have hcases : d = 2 ∨ d = 3 := by omega
    rcases hcases with rfl | rfl
    · norm_num
      exact antisymmetric_d2_companion_purity_strong N β hbound Ψ hΨ
    · norm_num
      exact antisymmetric_d3_companion_purity_strong N β hbound Ψ hΨ

theorem antisymmetric_companion_purity_le_half {d : ℕ} (hd : 2 ≤ d)
    {Y B E : Type*} [Fintype Y] [Fintype B] [Fintype E] [DecidableEq Y]
    (N : Stinespring Y B E) (β : ℝ)
    (hbound : ∀ v : Y → ℂ, vectorNormSq v = 1 → purity (N.apply (pureDensity v)) ≤ β)
    (Ψ : Edge d × Y → ℂ) (hΨ : vectorNormSq Ψ = 1) :
    purity (((antisymmetricStinespring d).tensor N).apply (pureDensity Ψ)) ≤ β / 2 := by
  have hp := antisymmetric_companion_purity_strong hd N β hbound Ψ hΨ
  have hβ := companion_purity_bound_nonneg N β hbound Ψ hΨ
  have hs := normalized_coefficient_purity_le_one (companionCoefficient Ψ)
    (by rw [companionCoefficient_hsNormSq, hΨ])
  have hz : 0 ≤ β / ((d : ℝ) + 1) * (1 - purity (companionMarginal Ψ)) :=
    mul_nonneg (div_nonneg hβ (by positivity)) (sub_nonneg.mpr hs)
  linarith

theorem companionHalfStep {d : ℕ} (hd : 2 ≤ d) : CompanionHalfStep d := by
  intro Y B E _ _ _ _ N β hbound Ψ hΨ
  exact antisymmetric_companion_purity_le_half hd N β hbound Ψ hΨ

theorem antisymmetricPower_purity_upper (d : ℕ) (hd : 2 ≤ d) (n : ℕ)
    (u : EdgePower d n → ℂ) (hu : vectorNormSq u = 1) :
    purity ((antisymmetricPowerStinespring d n).apply (pureDensity u)) ≤ (1 / 2 : ℝ) ^ n :=
  antisymmetricPower_purity_upper_of_companion d (companionHalfStep hd) n u hu

theorem antisymmetricPower_purity_optimum (d : ℕ) (hd : 2 ≤ d) (n : ℕ) :
    (∀ u : EdgePower d n → ℂ, vectorNormSq u = 1 →
      purity ((antisymmetricPowerStinespring d n).apply (pureDensity u)) ≤ (1 / 2 : ℝ) ^ n) ∧
    ∃ u : EdgePower d n → ℂ, vectorNormSq u = 1 ∧
      purity ((antisymmetricPowerStinespring d n).apply (pureDensity u)) = (1 / 2 : ℝ) ^ n :=
  antisymmetricPower_purity_optimum_of_companion d (companionHalfStep hd)
    (firstEndpointEdge d hd) n

theorem antisymmetric_physical_purity_upper (d : ℕ) (hd : 2 ≤ d) (n : ℕ)
    (ψ : PhysicalPower d n × PhysicalPower d n → ℂ) (hunit : vectorNormSq ψ = 1)
    (hψ : HasAntisymmetricSupport d n (fun a b => ψ (a,b))) :
    purity (partialTraceLeft (pureDensity ψ)) ≤ (1 / 2 : ℝ) ^ n :=
  antisymmetric_physical_purity_upper_of_companion d (companionHalfStep hd) n ψ hunit hψ

theorem antisymmetric_physical_projector_purity_upper (d : ℕ) (hd : 2 ≤ d) (n : ℕ)
    (ψ : PhysicalPower d n × PhysicalPower d n → ℂ) (hunit : vectorNormSq ψ = 1)
    (hψ : (physicalTensorAntisymmetrizer d n).mulVec ψ = ψ) :
    purity (partialTraceLeft (pureDensity ψ)) ≤ (1 / 2 : ℝ) ^ n :=
  antisymmetric_physical_projector_purity_upper_of_companion d (companionHalfStep hd) n ψ hunit hψ

theorem antisymmetric_physical_purity_optimum (d : ℕ) (hd : 2 ≤ d) (n : ℕ) :
    (∀ ψ : PhysicalPower d n × PhysicalPower d n → ℂ, vectorNormSq ψ = 1 →
      HasAntisymmetricSupport d n (fun a b => ψ (a,b)) →
      purity (partialTraceLeft (pureDensity ψ)) ≤ (1 / 2 : ℝ) ^ n) ∧
    ∃ ψ : PhysicalPower d n × PhysicalPower d n → ℂ, vectorNormSq ψ = 1 ∧
      HasAntisymmetricSupport d n (fun a b => ψ (a,b)) ∧
      purity (partialTraceLeft (pureDensity ψ)) = (1 / 2 : ℝ) ^ n :=
  antisymmetric_physical_purity_optimum_of_companion d (companionHalfStep hd)
    (firstEndpointEdge d hd) n

theorem antisymmetric_physical_entropy_lower (d : ℕ) (hd : 2 ≤ d) (n : ℕ)
    (ψ : PhysicalPower d n × PhysicalPower d n → ℂ) (hunit : vectorNormSq ψ = 1)
    (hψ : HasAntisymmetricSupport d n (fun a b => ψ (a,b))) :
    (n : ℝ) ≤ physicalAliceEntropy d n ψ :=
  antisymmetric_physical_entropy_lower_of_companion d (companionHalfStep hd) n ψ hunit hψ

theorem antisymmetric_physical_entropy_optimum (d : ℕ) (hd : 2 ≤ d) (n : ℕ) :
    (∀ ψ : PhysicalPower d n × PhysicalPower d n → ℂ, vectorNormSq ψ = 1 →
      HasAntisymmetricSupport d n (fun a b => ψ (a,b)) →
      (n : ℝ) ≤ physicalAliceEntropy d n ψ) ∧
    ∃ ψ : PhysicalPower d n × PhysicalPower d n → ℂ, vectorNormSq ψ = 1 ∧
      HasAntisymmetricSupport d n (fun a b => ψ (a,b)) ∧ physicalAliceEntropy d n ψ = (n : ℝ) :=
  antisymmetric_physical_entropy_optimum_of_companion d (companionHalfStep hd)
    (firstEndpointEdge d hd) n

theorem antisymmetric_physical_ensemble_entropy_lower (d : ℕ) (hd : 2 ≤ d) (n : ℕ)
    (ρ : Matrix (PhysicalPower d n × PhysicalPower d n) (PhysicalPower d n × PhysicalPower d n) ℂ)
    (E : AntisymmetricEnsembleCost.FinitePureEnsemble ρ)
    (hsupp : ρ = physicalTensorAntisymmetrizer d n * ρ * physicalTensorAntisymmetrizer d n) :
    (n : ℝ) ≤ E.averageAliceEntropy :=
  antisymmetric_physical_ensemble_entropy_lower_of_companion d (companionHalfStep hd) n ρ E hsupp

theorem antisymmetric_physical_finiteConvexRoof_lower (d : ℕ) (hd : 2 ≤ d) (n : ℕ)
    (ρ : Matrix (PhysicalPower d n × PhysicalPower d n) (PhysicalPower d n × PhysicalPower d n) ℂ)
    (hsupp : ρ = physicalTensorAntisymmetrizer d n * ρ * physicalTensorAntisymmetrizer d n) :
    (n : EReal) ≤ AntisymmetricEnsembleCost.finiteConvexRoof ρ :=
  antisymmetric_physical_finiteConvexRoof_lower_of_companion d (companionHalfStep hd) n ρ hsupp

theorem antisymmetric_physical_finiteConvexRoof_real (d : ℕ) (hd : 2 ≤ d) (n : ℕ)
    (ρ : Matrix (PhysicalPower d n × PhysicalPower d n) (PhysicalPower d n × PhysicalPower d n) ℂ)
    (hρ : ρ.PosSemidef) (htrace : Matrix.trace ρ = 1)
    (hsupp : ρ = physicalTensorAntisymmetrizer d n * ρ * physicalTensorAntisymmetrizer d n) :
    ∃ c : ℝ, (n : ℝ) ≤ c ∧ AntisymmetricEnsembleCost.finiteConvexRoof ρ = (c : EReal) :=
  antisymmetric_physical_finiteConvexRoof_real_of_companion d (companionHalfStep hd)
    n ρ hρ htrace hsupp

theorem physicalAntisymmetricState_finiteConvexRoof_eq (d : ℕ) (hd : 2 ≤ d) (n : ℕ) :
    AntisymmetricEnsembleCost.finiteConvexRoof (physicalAntisymmetricState d n) = (n : EReal) :=
  physicalAntisymmetricState_finiteConvexRoof_eq_of_companion d (companionHalfStep hd)
    (firstEndpointEdge d hd) n

theorem antisymmetric_cptp_companion_purity_strong {d : ℕ} (hd : 2 ≤ d)
    {Y B : Type*} [Fintype Y] [Fintype B] [DecidableEq Y] [DecidableEq B]
    (Φ : Matrix Y Y ℂ →ₗ[ℂ] Matrix B B ℂ)
    (hCP : QuantumProver.SuperchannelDiscrimination.CPTPKraus.CompletelyPositive Φ)
    (hTP : QuantumProver.SuperchannelDiscrimination.CPTPKraus.TracePreserving Φ) (β : ℝ)
    (hbound : ∀ v : Y → ℂ, vectorNormSq v = 1 → purity (Φ (pureDensity v)) ≤ β)
    (Ψ : Edge d × Y → ℂ) (hΨ : vectorNormSq Ψ = 1) :
    purity (((antisymmetricStinespring d).tensor (stinespringOfCPTP Φ hCP hTP)).apply (pureDensity Ψ)) ≤
      β / 2 - β / ((d : ℝ) + 1) * (1 - purity (companionMarginal Ψ)) := by
  apply antisymmetric_companion_purity_strong hd (stinespringOfCPTP Φ hCP hTP) β _ Ψ hΨ
  intro v hv
  rw [stinespringOfCPTP_apply]
  exact hbound v hv

theorem antisymmetric_cptp_companion_purity_le_half {d : ℕ} (hd : 2 ≤ d)
    {Y B : Type*} [Fintype Y] [Fintype B] [DecidableEq Y] [DecidableEq B]
    (Φ : Matrix Y Y ℂ →ₗ[ℂ] Matrix B B ℂ)
    (hCP : QuantumProver.SuperchannelDiscrimination.CPTPKraus.CompletelyPositive Φ)
    (hTP : QuantumProver.SuperchannelDiscrimination.CPTPKraus.TracePreserving Φ) (β : ℝ)
    (hbound : ∀ v : Y → ℂ, vectorNormSq v = 1 → purity (Φ (pureDensity v)) ≤ β)
    (Ψ : Edge d × Y → ℂ) (hΨ : vectorNormSq Ψ = 1) :
    purity (((antisymmetricStinespring d).tensor (stinespringOfCPTP Φ hCP hTP)).apply (pureDensity Ψ)) ≤
      β / 2 := by
  apply antisymmetric_companion_purity_le_half hd (stinespringOfCPTP Φ hCP hTP) β _ Ψ hΨ
  intro v hv
  rw [stinespringOfCPTP_apply]
  exact hbound v hv

open OperationalEndpointCost

def unitEndpointPreparation : OneWayLocalInstrument Unit Unit Unit Unit Unit where
  alice := fun _ => 1
  bob := fun _ => 1
  alice_complete := by simp
  bob_isometry := by simp

def endpointAlicePower (d : ℕ) (hd : 2 ≤ d) : (n : ℕ) → EdgePower d n →
    Matrix (PhysicalPower d n) (PhysicalPower 2 n) ℂ
  | 0, _ => 1
  | n + 1, x => (uniformEdgeInstrument d hd).alice x.1 ⊗ₖ
      endpointAlicePower d hd n x.2

def endpointBobPower (d : ℕ) (hd : 2 ≤ d) : (n : ℕ) → EdgePower d n →
    Matrix (PhysicalPower d n) (PhysicalPower 2 n) ℂ
  | 0, _ => 1
  | n + 1, x => (uniformEdgeInstrument d hd).bob x.1 ⊗ₖ
      endpointBobPower d hd n x.2

theorem endpointAlicePower_complete (d : ℕ) (hd : 2 ≤ d) (n : ℕ) :
    ∑ x, (endpointAlicePower d hd n x).conjTranspose * endpointAlicePower d hd n x = 1 := by
  induction n with
  | zero => simp [endpointAlicePower]
  | succ n ih =>
      simp only [endpointAlicePower, Fintype.sum_prod_type,
        Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul]
      have hs :
          (∑ e : Edge d, ∑ x : EdgePower d n,
            (((uniformEdgeInstrument d hd).alice e).conjTranspose *
                (uniformEdgeInstrument d hd).alice e) ⊗ₖ
              ((endpointAlicePower d hd n x).conjTranspose * endpointAlicePower d hd n x)) =
          (∑ e : Edge d,
            ((uniformEdgeInstrument d hd).alice e).conjTranspose *
                (uniformEdgeInstrument d hd).alice e) ⊗ₖ
          (∑ x : EdgePower d n,
            (endpointAlicePower d hd n x).conjTranspose * endpointAlicePower d hd n x) := by
        ext p q
        simp only [Matrix.sum_apply, Matrix.kroneckerMap_apply]
        rw [Finset.sum_mul]
        simp only [Finset.mul_sum]
      rw [hs, (uniformEdgeInstrument d hd).alice_complete, ih, Matrix.one_kronecker_one]

theorem endpointBobPower_isometry (d : ℕ) (hd : 2 ≤ d) (n : ℕ)
    (x : EdgePower d n) :
    (endpointBobPower d hd n x).conjTranspose * endpointBobPower d hd n x = 1 := by
  induction n with
  | zero => simp [endpointBobPower]
  | succ n ih =>
      simp only [endpointBobPower, Matrix.conjTranspose_kronecker,
        ← Matrix.mul_kronecker_mul, (uniformEdgeInstrument d hd).bob_isometry,
        ih, Matrix.one_kronecker_one]

def endpointOneWayPower (d : ℕ) (hd : 2 ≤ d) (n : ℕ) :
    OneWayLocalInstrument (EdgePower d n) (PhysicalPower 2 n) (PhysicalPower 2 n)
      (PhysicalPower d n) (PhysicalPower d n) where
  alice := endpointAlicePower d hd n
  bob := endpointBobPower d hd n
  alice_complete := endpointAlicePower_complete d hd n
  bob_isometry := endpointBobPower_isometry d hd n

theorem localTensorBranch_mulVec
    {A₀ B₀ A₁ B₁ C₀ D₀ C₁ D₁ : Type*}
    [Fintype A₀] [Fintype B₀] [Fintype C₀] [Fintype D₀]
    (U : Matrix A₁ A₀ ℂ) (V : Matrix B₁ B₀ ℂ)
    (C : Matrix C₁ C₀ ℂ) (D : Matrix D₁ D₀ ℂ)
    (u : A₀ × B₀ → ℂ) (v : C₀ × D₀ → ℂ) :
    ((U ⊗ₖ C) ⊗ₖ (V ⊗ₖ D)).mulVec
        (fun pq => u (pq.1.1, pq.2.1) * v (pq.1.2, pq.2.2)) =
      fun pq => (U ⊗ₖ V).mulVec u (pq.1.1, pq.2.1) *
        (C ⊗ₖ D).mulVec v (pq.1.2, pq.2.2) := by
  classical
  ext ⟨⟨a, r⟩, ⟨b, s⟩⟩
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Matrix.kronecker_apply]
  calc
    (∑ p : A₀, ∑ t : C₀, ∑ q : B₀, ∑ z : D₀,
      (U a p * C r t) * (V b q * D s z) * (u (p,q) * v (t,z))) =
        ∑ p : A₀, ∑ q : B₀, ∑ t : C₀, ∑ z : D₀,
          (U a p * V b q * u (p,q)) * (C r t * D s z * v (t,z)) := by
      apply Finset.sum_congr rfl
      intro p _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro q _
      apply Finset.sum_congr rfl
      intro t _
      apply Finset.sum_congr rfl
      intro z _
      ring
    _ = _ := by simp only [← Finset.mul_sum, ← Finset.sum_mul]

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1500000 in
theorem endpointOneWayPower_branch_bell (d : ℕ) (hd : 2 ≤ d) (n : ℕ)
    (x : EdgePower d n) :
    ((endpointOneWayPower d hd n).branch x).mulVec (bellPairPowerVector n) =
      edgeAmplitude d ^ n • physicalSlaterColumn d n x := by
  induction n with
  | zero =>
      ext ab
      rcases ab with ⟨⟨⟩, ⟨⟩⟩
      simp [endpointOneWayPower, endpointAlicePower, endpointBobPower,
        OneWayLocalInstrument.branch, bellPairPowerVector,
        physicalSlaterColumn, physicalTensorIsometry,
        Matrix.mulVec, dotProduct, Matrix.kronecker_apply]
  | succ n ih =>
      have hv : bellPairPowerVector (n+1) =
          fun pq => bellVector (pq.1.1,pq.2.1) *
            bellPairPowerVector n (pq.1.2,pq.2.2) := by
        ext pq
        exact bellPairPowerVector_succ n pq.1.1 pq.2.1 pq.1.2 pq.2.2
      simp only [OneWayLocalInstrument.branch, endpointOneWayPower,
        endpointAlicePower, endpointBobPower]
      rw [hv, localTensorBranch_mulVec]
      have hfirst := uniformEdgeInstrument_branch_bell d hd x.1
      have hrest := ih x.2
      simp only [OneWayLocalInstrument.branch] at hfirst
      simp only [OneWayLocalInstrument.branch, endpointOneWayPower] at hrest
      rw [hfirst, hrest]
      ext pq
      simp only [Pi.smul_apply, smul_eq_mul, physicalSlaterColumn,
        physicalTensorIsometry, pow_succ]
      ring

theorem edgePower_card (d n : ℕ) :
    Fintype.card (EdgePower d n) = Fintype.card (Edge d) ^ n := by
  induction n with
  | zero => simp [EdgePower]
  | succ n ih =>
      change Fintype.card (Edge d × EdgePower d n) = _
      simp only [Fintype.card_prod, ih, pow_succ, Nat.mul_comm]

theorem endpointOneWayPower_bell_output (d : ℕ) (hd : 2 ≤ d) (n : ℕ) :
    (endpointOneWayPower d hd n).apply (pureDensity (bellPairPowerVector n)) =
      physicalAntisymmetricState d n := by
  rw [OneWayLocalInstrument.apply_pureDensity]
  simp_rw [endpointOneWayPower_branch_bell, matrix_pureDensity_scalar,
    map_pow, edgeAmplitude_normSq]
  have hc : ((Fintype.card (Edge d) : ℝ)⁻¹)^n =
      (Fintype.card (EdgePower d n) : ℝ)⁻¹ := by
    rw [edgePower_card]
    simp [inv_pow]
  simp_rw [hc]
  rw [← Finset.smul_sum, ← physicalTensorAntisymmetrizer_eq_column_sum]
  ext ab cd
  simp only [physicalAntisymmetricState, Matrix.smul_apply,
    RCLike.real_smul_eq_coe_mul, smul_eq_mul,
    AntisymmetricEntropyCost.rclike_complex_cast]

theorem physicalAntisymmetricState_exact_oneWay_preparation
    (d : ℕ) (hd : 2 ≤ d) (n : ℕ) :
    ∃ I : OneWayLocalInstrument (EdgePower d n)
        (PhysicalPower 2 n) (PhysicalPower 2 n)
        (PhysicalPower d n) (PhysicalPower d n),
      I.apply (pureDensity (bellPairPowerVector n)) = physicalAntisymmetricState d n :=
  ⟨endpointOneWayPower d hd n, endpointOneWayPower_bell_output d hd n⟩

def physicalPairFiniteEquiv (d n : ℕ) :
    (Fin (Fintype.card (PhysicalPower d n)) × Fin (Fintype.card (PhysicalPower d n))) ≃
      PhysicalPower d n × PhysicalPower d n :=
  (Fintype.equivFin (PhysicalPower d n)).symm.prodCongr
    (Fintype.equivFin (PhysicalPower d n)).symm

def finiteBellPairPowerVector (n : ℕ) :
    Fin (Fintype.card (PhysicalPower 2 n)) × Fin (Fintype.card (PhysicalPower 2 n)) → ℂ :=
  bellPairPowerVector n ∘ physicalPairFiniteEquiv 2 n

theorem finiteBellPairPowerVector_normSq (n : ℕ) :
    vectorNormSq (finiteBellPairPowerVector n) = 1 := by
  rw [finiteBellPairPowerVector, OneWayLocalInstrument.vectorNormSq_equiv,
    bellPairPowerVector_normSq]

def finitePhysicalAntisymmetricState (d n : ℕ) :
    Matrix (Fin (Fintype.card (PhysicalPower d n)) × Fin (Fintype.card (PhysicalPower d n)))
      (Fin (Fintype.card (PhysicalPower d n)) × Fin (Fintype.card (PhysicalPower d n))) ℂ :=
  (physicalAntisymmetricState d n).submatrix
    (physicalPairFiniteEquiv d n) (physicalPairFiniteEquiv d n)

def endpointFiniteLocalProtocol (d : ℕ) (hd : 2 ≤ d) (n : ℕ) :
    FiniteLocalProtocol (Fintype.card (PhysicalPower d n)) (Fintype.card (PhysicalPower d n))
      (Fintype.card (PhysicalPower 2 n)) (Fintype.card (PhysicalPower 2 n)) :=
  (endpointOneWayPower d hd n).toFiniteLocalProtocolOfFintype

theorem endpointFiniteLocalProtocol_bell_output (d : ℕ) (hd : 2 ≤ d) (n : ℕ) :
    (endpointFiniteLocalProtocol d hd n).apply (pureDensity (finiteBellPairPowerVector n)) =
      finitePhysicalAntisymmetricState d n := by
  change (endpointOneWayPower d hd n).toFiniteLocalProtocolOfFintype.apply
    (pureDensity (bellPairPowerVector n ∘
      ((Fintype.equivFin (PhysicalPower 2 n)).symm.prodCongr
        (Fintype.equivFin (PhysicalPower 2 n)).symm))) = _
  rw [OneWayLocalInstrument.toFiniteLocalProtocolOfFintype_apply_pureDensity,
    endpointOneWayPower_bell_output]
  rfl

theorem physicalAntisymmetricState_exact_finiteLocalProtocol_preparation
    (d : ℕ) (hd : 2 ≤ d) (n : ℕ) :
    ∃ T : FiniteLocalProtocol (Fintype.card (PhysicalPower d n))
        (Fintype.card (PhysicalPower d n)) (Fintype.card (PhysicalPower 2 n))
        (Fintype.card (PhysicalPower 2 n)),
      vectorNormSq (finiteBellPairPowerVector n) = 1 ∧
        T.apply (pureDensity (finiteBellPairPowerVector n)) =
          finitePhysicalAntisymmetricState d n :=
  ⟨endpointFiniteLocalProtocol d hd n, finiteBellPairPowerVector_normSq n,
    endpointFiniteLocalProtocol_bell_output d hd n⟩

def physicalNearbyVector (d : ℕ) (hd : 2 ≤ d) (n : ℕ)
    (ψ : PhysicalPower d n × PhysicalPower d n → ℂ) :=
  AntisymmetricEnsembleCost.supportedProjectionOr (physicalTensorAntisymmetrizer d n)
    ψ (physicalTensorSlaterVector (firstEndpointEdge d hd) n)

theorem physicalNearbyVector_norm_support_distance (d : ℕ) (hd : 2 ≤ d) (n : ℕ)
    (ψ : PhysicalPower d n × PhysicalPower d n → ℂ) (hψ : vectorNormSq ψ = 1) :
    vectorNormSq (physicalNearbyVector d hd n ψ) = 1 ∧
    HasAntisymmetricSupport d n (fun a b => physicalNearbyVector d hd n ψ (a,b)) ∧
    SchattenSupport.schattenOne (pureDensity ψ - pureDensity (physicalNearbyVector d hd n ψ)) ≤
      2 * Real.sqrt (1-vectorNormSq ((physicalTensorAntisymmetrizer d n).mulVec ψ)) := by
  let φ := physicalTensorSlaterVector (firstEndpointEdge d hd) n
  have hφ : vectorNormSq φ = 1 := physicalTensorSlaterVector_normSq _ n
  have hφr : (physicalTensorAntisymmetrizer d n).mulVec φ = φ :=
    (physicalTensorAntisymmetrizer_fix_iff_support d n φ).mpr
      (physicalTensorSlaterVector_support _ n)
  refine ⟨AntisymmetricEnsembleCost.supportedProjectionOr_normSq _ ψ φ hφ, ?_, ?_⟩
  · exact (physicalTensorAntisymmetrizer_fix_iff_support d n _).mp
      (AntisymmetricEnsembleCost.supportedProjectionOr_range _
        (physicalTensorAntisymmetrizer_idempotent d n) ψ φ hφr)
  · exact AntisymmetricEnsembleCost.supportedProjectionOr_schatten_distance _
      (physicalTensorAntisymmetrizer_hermitian d n)
      (physicalTensorAntisymmetrizer_idempotent d n) ψ φ hψ hφ

theorem physicalNearbyVector_normalized_preimage (d : ℕ) (hd : 2 ≤ d) (n : ℕ)
    (ψ : PhysicalPower d n × PhysicalPower d n → ℂ) (hψ : vectorNormSq ψ = 1) :
    ∃ u : EdgePower d n → ℂ, vectorNormSq u = 1 ∧
      (physicalTensorIsometry d n).mulVec u = physicalNearbyVector d hd n ψ ∧
      partialTraceLeft (pureDensity (physicalNearbyVector d hd n ψ)) =
        (antisymmetricPowerStinespring d n).apply (pureDensity u) := by
  have h := physicalNearbyVector_norm_support_distance d hd n ψ hψ
  exact physical_normalized_preimage d n _ h.1 h.2.1

theorem physicalNearbyVector_entropy_lower (d : ℕ) (hd : 2 ≤ d) (n : ℕ)
    (ψ : PhysicalPower d n × PhysicalPower d n → ℂ) (hψ : vectorNormSq ψ = 1) :
    (n : ℝ) ≤ physicalAliceEntropy d n (physicalNearbyVector d hd n ψ) := by
  have h := physicalNearbyVector_norm_support_distance d hd n ψ hψ
  exact antisymmetric_physical_entropy_lower d hd n _ h.1 h.2.1

theorem physicalAntisymmetricState_projector_expectation_one
    (d : ℕ) (hd : 2 ≤ d) (n : ℕ) :
    (Matrix.trace (physicalTensorAntisymmetrizer d n *
      physicalAntisymmetricState d n)).re = 1 := by
  have hp : physicalTensorAntisymmetrizer d n * physicalAntisymmetricState d n =
      physicalAntisymmetricState d n := by
    rw [physicalAntisymmetricState, Matrix.mul_smul,
      physicalTensorAntisymmetrizer_idempotent]
  rw [hp, (physicalAntisymmetricState_density d hd n).2, Complex.one_re]

theorem physicalAntisymmetricState_ensemble_leakage_le
    (d : ℕ) (hd : 2 ≤ d) (n : ℕ)
    (ρ : Matrix (PhysicalPower d n × PhysicalPower d n)
      (PhysicalPower d n × PhysicalPower d n) ℂ)
    (E : AntisymmetricEnsembleCost.FinitePureEnsemble ρ) (epsilon : ℝ)
    (hDistance : SchattenSupport.schattenOne (ρ - physicalAntisymmetricState d n) / 2 ≤ epsilon) :
    1 - (Matrix.trace (physicalTensorAntisymmetrizer d n * ρ)).re ≤ epsilon := by
  have hP : (physicalTensorAntisymmetrizer d n).IsHermitian :=
    physicalTensorAntisymmetrizer_hermitian d n
  have hEffect := OperationalEndpointCost.projector_isEffect _ hP
    (physicalTensorAntisymmetrizer_idempotent d n)
  have hTrace : Matrix.trace ρ = Matrix.trace (physicalAntisymmetricState d n) := by
    rw [E.trace_one, (physicalAntisymmetricState_density d hd n).2]
  have h := OperationalEndpointCost.effect_expectation_schatten_distance
    (physicalTensorAntisymmetrizer d n) ρ (physicalAntisymmetricState d n)
    hEffect E.posSemidef.isHermitian
    (physicalAntisymmetricState_posSemidef d n).isHermitian hTrace
  rw [physicalAntisymmetricState_projector_expectation_one d hd n] at h
  have hlower := (abs_le.mp h).1
  linarith

theorem physicalAntisymmetricState_ensemble_replacement_distance_le
    (d : ℕ) (hd : 2 ≤ d) (n : ℕ)
    (ρ : Matrix (PhysicalPower d n × PhysicalPower d n)
      (PhysicalPower d n × PhysicalPower d n) ℂ)
    (E : AntisymmetricEnsembleCost.FinitePureEnsemble ρ) (epsilon : ℝ)
    (hDistance : SchattenSupport.schattenOne (ρ - physicalAntisymmetricState d n) / 2 ≤ epsilon) :
    (∑ j, E.weight j * SchattenSupport.schattenOne
      (pureDensity (E.vector j) - pureDensity (physicalNearbyVector d hd n (E.vector j)))) ≤
      2 * Real.sqrt epsilon := by
  have hLeak := physicalAntisymmetricState_ensemble_leakage_le d hd n ρ E epsilon hDistance
  exact (E.supportedReplacement_average_distance_le (physicalTensorAntisymmetrizer d n)
    (physicalTensorAntisymmetrizer_hermitian d n)
    (physicalTensorAntisymmetrizer_idempotent d n)
    (physicalTensorSlaterVector (firstEndpointEdge d hd) n)
    (physicalTensorSlaterVector_normSq _ n)).trans
      (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hLeak) (by norm_num))

theorem finiteBellPairPowerVector_alice_entropy (n : ℕ) :
    AntisymmetricEnsembleCost.aliceEntropy (finiteBellPairPowerVector n) = (n : ℝ) := by
  unfold AntisymmetricEnsembleCost.aliceEntropy AntisymmetricEnsembleCost.aliceDensity
    finiteBellPairPowerVector physicalPairFiniteEquiv
  rw [OneWayLocalInstrument.pure_marginalLeft_entropy_prodEquiv,
    bellPairPowerVector_alice_entropy]

def reindexFinitePureEnsemble {X X' : Type*} [Fintype X] [Fintype X']
    [DecidableEq X] [DecidableEq X'] (e : X' ≃ X)
    {ρ : Matrix X X ℂ} (E : AntisymmetricEnsembleCost.FinitePureEnsemble ρ) :
    AntisymmetricEnsembleCost.FinitePureEnsemble (ρ.submatrix e e) where
  count := E.count
  weight := E.weight
  weight_nonneg := E.weight_nonneg
  weight_sum := E.weight_sum
  vector := fun j => E.vector j ∘ e
  normalized := fun j => by
    rw [OneWayLocalInstrument.vectorNormSq_equiv]
    exact E.normalized j
  barycenter := by
    conv_lhs => rw [E.barycenter]
    ext x y
    simp [Matrix.submatrix_apply, Matrix.sum_apply, Matrix.smul_apply,
      pureDensity, crossDensity, Function.comp_def]

theorem reindexFinitePureEnsemble_averageAliceEntropy {A B A' B' : Type*}
    [Fintype A] [Fintype B] [Fintype A'] [Fintype B']
    [DecidableEq A] [DecidableEq B] [DecidableEq A'] [DecidableEq B']
    (eA : A' ≃ A) (eB : B' ≃ B)
    {ρ : Matrix (A × B) (A × B) ℂ}
    (E : AntisymmetricEnsembleCost.FinitePureEnsemble ρ) :
    (reindexFinitePureEnsemble (eA.prodCongr eB) E).averageAliceEntropy =
      E.averageAliceEntropy := by
  unfold AntisymmetricEnsembleCost.FinitePureEnsemble.averageAliceEntropy
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  exact OneWayLocalInstrument.pure_marginalLeft_entropy_prodEquiv eA eB (E.vector j)

def physicalFiniteProtocolOutput (d n m : ℕ)
    (T : FiniteLocalProtocol (Fintype.card (PhysicalPower d n))
      (Fintype.card (PhysicalPower d n)) (Fintype.card (PhysicalPower 2 m))
      (Fintype.card (PhysicalPower 2 m))) :
    Matrix (PhysicalPower d n × PhysicalPower d n)
      (PhysicalPower d n × PhysicalPower d n) ℂ :=
  (T.apply (pureDensity (finiteBellPairPowerVector m))).submatrix
    (physicalPairFiniteEquiv d n).symm (physicalPairFiniteEquiv d n).symm

theorem physicalFiniteProtocolOutput_entropyEnsemble (d n m : ℕ)
    (T : FiniteLocalProtocol (Fintype.card (PhysicalPower d n))
      (Fintype.card (PhysicalPower d n)) (Fintype.card (PhysicalPower 2 m))
      (Fintype.card (PhysicalPower 2 m))) :
    ∃ E : AntisymmetricEnsembleCost.FinitePureEnsemble (physicalFiniteProtocolOutput d n m T),
      E.averageAliceEntropy ≤ (m : ℝ) := by
  obtain ⟨E, hE⟩ := LocalEntropy.finiteLocalProtocol_output_entropyEnsemble T
    (finiteBellPairPowerVector m) (finiteBellPairPowerVector_normSq m)
  rw [finiteBellPairPowerVector_alice_entropy] at hE
  refine ⟨reindexFinitePureEnsemble (physicalPairFiniteEquiv d n).symm E, ?_⟩
  change (reindexFinitePureEnsemble
    ((Fintype.equivFin (PhysicalPower d n)).prodCongr
      (Fintype.equivFin (PhysicalPower d n))) E).averageAliceEntropy ≤ (m : ℝ)
  rw [reindexFinitePureEnsemble_averageAliceEntropy]
  exact hE

theorem pureAliceDensity_isDensity {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (ψ : A × B → ℂ) (hψ : vectorNormSq ψ = 1) :
    QuantumProver.ConditionalEntropy.IsDensity (partialTraceLeft (pureDensity ψ)) := by
  refine ⟨partialTraceLeft_posSemidef _ (pureDensity_posSemidef ψ), ?_⟩
  rw [partialTraceLeft_trace, pureDensity_trace, hψ]
  rfl

theorem pureAliceDensity_traceDistance_le {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (ψ φ : A × B → ℂ) :
    QuantumProver.ConditionalEntropy.traceDistance (partialTraceLeft (pureDensity ψ))
      (partialTraceLeft (pureDensity φ)) ≤
      SchattenSupport.schattenOne (pureDensity ψ - pureDensity φ) / 2 := by
  rw [QuantumProver.ConditionalEntropy.traceDistance, QuantumProver.ConditionalEntropy.traceNorm,
    OperationalEndpointCost.traceNorm_eq_schattenOne]
  exact div_le_div_of_nonneg_right
    (OperationalEndpointCost.partialTraceLeft_schatten_distance_le _ _
      (pureDensity_posSemidef ψ).isHermitian (pureDensity_posSemidef φ).isHermitian)
    (by norm_num)

theorem physicalAntisymmetricState_replacement_ensemble_entropy_lower
    (d : ℕ) (hd : 2 ≤ d) (n : ℕ)
    (ρ : Matrix (PhysicalPower d n × PhysicalPower d n)
      (PhysicalPower d n × PhysicalPower d n) ℂ)
    (E : AntisymmetricEnsembleCost.FinitePureEnsemble ρ) (epsilon : ℝ)
    (hEpsilon0 : 0 ≤ epsilon) (hEpsilon1 : epsilon ≤ 1)
    (hReplacement : (∑ j, E.weight j * SchattenSupport.schattenOne
      (pureDensity (E.vector j) - pureDensity (physicalNearbyVector d hd n (E.vector j)))) ≤
      2 * Real.sqrt epsilon) :
    (n : ℝ) - QuantumProver.ConditionalEntropy.winterBound (PhysicalPower d n) (Real.sqrt epsilon) ≤
      E.averageAliceEntropy := by
  let φ : Fin E.count → PhysicalPower d n × PhysicalPower d n → ℂ :=
    fun j => physicalNearbyVector d hd n (E.vector j)
  let R := fun j => partialTraceLeft (pureDensity (E.vector j))
  let S := fun j => partialTraceLeft (pureDensity (φ j))
  have hφ : ∀ j, vectorNormSq (φ j) = 1 := fun j =>
    (physicalNearbyVector_norm_support_distance d hd n (E.vector j) (E.normalized j)).1
  have hR : ∀ j, QuantumProver.ConditionalEntropy.IsDensity (R j) := fun j =>
    pureAliceDensity_isDensity _ (E.normalized j)
  have hS : ∀ j, QuantumProver.ConditionalEntropy.IsDensity (S j) := fun j =>
    pureAliceDensity_isDensity _ (hφ j)
  have hMarginalDistance : ∑ j, E.weight j * QuantumProver.ConditionalEntropy.traceDistance (R j) (S j) ≤
      Real.sqrt epsilon := by
    calc
      _ ≤ ∑ j, E.weight j * (SchattenSupport.schattenOne
          (pureDensity (E.vector j) - pureDensity (φ j)) / 2) :=
        Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left
          (pureAliceDensity_traceDistance_le _ _) (E.weight_nonneg j))
      _ = (∑ j, E.weight j * SchattenSupport.schattenOne
          (pureDensity (E.vector j) - pureDensity (φ j))) / 2 := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ ≤ Real.sqrt epsilon := by linarith
  have hSqrt : Real.sqrt epsilon ≤ 1 := by
    nlinarith [Real.sq_sqrt hEpsilon0, Real.sqrt_nonneg epsilon]
  have hContinuity := QuantumProver.ConditionalEntropy.WeightedContinuity.weighted_entropyBits_continuity
    E.weight R S E.weight_nonneg E.weight_sum hR hS hMarginalDistance hSqrt
  have hReplacementEntropy : (n : ℝ) ≤ ∑ j, E.weight j *
      QuantumProver.ConditionalEntropy.entropyBits (S j) := by
    have hEach : ∀ j, (n : ℝ) ≤ QuantumProver.ConditionalEntropy.entropyBits (S j) := by
      intro j
      have h := physicalNearbyVector_entropy_lower d hd n (E.vector j) (E.normalized j)
      change (n : ℝ) ≤ AntisymmetricEntropyCost.vonNeumannEntropyBits (S j) at h
      rw [AntisymmetricEntropyCost.vonNeumannEntropyBits_eq_quantumEntropyBits] at h
      exact h
    have hSum := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) =>
      mul_le_mul_of_nonneg_left (hEach j) (E.weight_nonneg j))
    simpa only [← Finset.sum_mul, E.weight_sum, one_mul] using hSum
  have represented_hPhysical : (∑ j, E.weight j * QuantumProver.ConditionalEntropy.entropyBits (R j)) =
      E.averageAliceEntropy := by
    unfold AntisymmetricEnsembleCost.FinitePureEnsemble.averageAliceEntropy
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    exact (AntisymmetricEntropyCost.vonNeumannEntropyBits_eq_quantumEntropyBits _).symm
  rw [represented_hPhysical] at hContinuity
  have hLower := (abs_le.mp hContinuity).1
  linarith

theorem physicalAntisymmetricState_nearby_ensemble_entropy_lower
    (d : ℕ) (hd : 2 ≤ d) (n : ℕ)
    (ρ : Matrix (PhysicalPower d n × PhysicalPower d n)
      (PhysicalPower d n × PhysicalPower d n) ℂ)
    (E : AntisymmetricEnsembleCost.FinitePureEnsemble ρ) (epsilon : ℝ)
    (hEpsilon0 : 0 ≤ epsilon) (hEpsilon1 : epsilon ≤ 1)
    (hDistance : SchattenSupport.schattenOne (ρ - physicalAntisymmetricState d n) / 2 ≤ epsilon) :
    (n : ℝ) - QuantumProver.ConditionalEntropy.winterBound (PhysicalPower d n) (Real.sqrt epsilon) ≤
      E.averageAliceEntropy :=
  physicalAntisymmetricState_replacement_ensemble_entropy_lower d hd n ρ E epsilon
    hEpsilon0 hEpsilon1
    (physicalAntisymmetricState_ensemble_replacement_distance_le d hd n ρ E epsilon hDistance)

theorem physicalAntisymmetricState_projector_ensemble_entropy_lower
    (d : ℕ) (hd : 2 ≤ d) (n : ℕ)
    (ρ : Matrix (PhysicalPower d n × PhysicalPower d n)
      (PhysicalPower d n × PhysicalPower d n) ℂ)
    (E : AntisymmetricEnsembleCost.FinitePureEnsemble ρ) :
    (n : ℝ) - QuantumProver.ConditionalEntropy.winterBound (PhysicalPower d n)
      (Real.sqrt (1 - (Matrix.trace (physicalTensorAntisymmetrizer d n * ρ)).re)) ≤
      E.averageAliceEntropy := by
  have hBounds := E.projector_leakage_bounds (physicalTensorAntisymmetrizer d n)
    (physicalTensorAntisymmetrizer_hermitian d n)
    (physicalTensorAntisymmetrizer_idempotent d n)
  apply physicalAntisymmetricState_replacement_ensemble_entropy_lower d hd n ρ E _
    hBounds.1 hBounds.2
  exact E.supportedReplacement_average_distance_le (physicalTensorAntisymmetrizer d n)
    (physicalTensorAntisymmetrizer_hermitian d n)
    (physicalTensorAntisymmetrizer_idempotent d n)
    (physicalTensorSlaterVector (firstEndpointEdge d hd) n)
    (physicalTensorSlaterVector_normSq _ n)

theorem physicalAntisymmetricState_finiteProtocol_resource_lower
    (d : ℕ) (hd : 2 ≤ d) (n m : ℕ)
    (T : FiniteLocalProtocol (Fintype.card (PhysicalPower d n))
      (Fintype.card (PhysicalPower d n)) (Fintype.card (PhysicalPower 2 m))
      (Fintype.card (PhysicalPower 2 m)))
    (epsilon : ℝ) (hEpsilon0 : 0 ≤ epsilon) (hEpsilon1 : epsilon ≤ 1)
    (hDistance : SchattenSupport.schattenOne
      (physicalFiniteProtocolOutput d n m T - physicalAntisymmetricState d n) / 2 ≤ epsilon) :
    (n : ℝ) - QuantumProver.ConditionalEntropy.winterBound (PhysicalPower d n) (Real.sqrt epsilon) ≤
      (m : ℝ) := by
  obtain ⟨E, hE⟩ := physicalFiniteProtocolOutput_entropyEnsemble d n m T
  exact (physicalAntisymmetricState_nearby_ensemble_entropy_lower d hd n _ E epsilon
    hEpsilon0 hEpsilon1 hDistance).trans hE

theorem physicalAntisymmetricState_finiteProtocol_projector_lower
    (d : ℕ) (hd : 2 ≤ d) (n m : ℕ)
    (T : FiniteLocalProtocol (Fintype.card (PhysicalPower d n))
      (Fintype.card (PhysicalPower d n)) (Fintype.card (PhysicalPower 2 m))
      (Fintype.card (PhysicalPower 2 m))) :
    (n : ℝ) - QuantumProver.ConditionalEntropy.winterBound (PhysicalPower d n)
      (Real.sqrt (1 - (Matrix.trace (physicalTensorAntisymmetrizer d n *
        physicalFiniteProtocolOutput d n m T)).re)) ≤ (m : ℝ) := by
  obtain ⟨E, hE⟩ := physicalFiniteProtocolOutput_entropyEnsemble d n m T
  exact (physicalAntisymmetricState_projector_ensemble_entropy_lower d hd n _ E).trans hE

theorem winterBound_sqrt_continuous (I : Type*) [Fintype I] :
    Continuous (fun x : ℝ => QuantumProver.ConditionalEntropy.winterBound I (Real.sqrt x)) := by
  have hDen : ∀ x : ℝ, 1 + Real.sqrt x ≠ 0 := fun x => ne_of_gt (by positivity)
  unfold QuantumProver.ConditionalEntropy.winterBound
  exact ((continuous_const.mul Real.continuous_sqrt).mul continuous_const).add
    ((continuous_const.add Real.continuous_sqrt).mul
      (QuantumProver.ConditionalEntropy.binaryEntropy_continuous.comp
        (Real.continuous_sqrt.div (continuous_const.add Real.continuous_sqrt) hDen)))

theorem physicalAntisymmetricState_finiteOutputClosure_projector_lower
    (d : ℕ) (hd : 2 ≤ d) (n m : ℕ)
    (σ : Matrix (Fin (Fintype.card (PhysicalPower d n)) ×
      Fin (Fintype.card (PhysicalPower d n)))
      (Fin (Fintype.card (PhysicalPower d n)) ×
      Fin (Fintype.card (PhysicalPower d n))) ℂ)
    (hσ : σ ∈ EndpointProtocolClosure.outputClosure (finiteBellPairPowerVector m)) :
    (n : ℝ) - QuantumProver.ConditionalEntropy.winterBound (PhysicalPower d n)
      (Real.sqrt (1 - (Matrix.trace (physicalTensorAntisymmetrizer d n *
        σ.submatrix (physicalPairFiniteEquiv d n).symm
          (physicalPairFiniteEquiv d n).symm)).re)) ≤ (m : ℝ) := by
  let e := (physicalPairFiniteEquiv d n).symm
  let f := fun τ : Matrix (Fin (Fintype.card (PhysicalPower d n)) ×
      Fin (Fintype.card (PhysicalPower d n)))
      (Fin (Fintype.card (PhysicalPower d n)) ×
      Fin (Fintype.card (PhysicalPower d n))) ℂ =>
    (n : ℝ) - QuantumProver.ConditionalEntropy.winterBound (PhysicalPower d n)
      (Real.sqrt (1 - (Matrix.trace (physicalTensorAntisymmetrizer d n *
        τ.submatrix e e)).re))
  have hBasis : Continuous (fun τ : Matrix (Fin (Fintype.card (PhysicalPower d n)) ×
      Fin (Fintype.card (PhysicalPower d n)))
      (Fin (Fintype.card (PhysicalPower d n)) ×
      Fin (Fintype.card (PhysicalPower d n))) ℂ => τ.submatrix e e) :=
    continuous_id.matrix_submatrix e e
  have hExp : Continuous (fun τ : Matrix (Fin (Fintype.card (PhysicalPower d n)) ×
      Fin (Fintype.card (PhysicalPower d n)))
      (Fin (Fintype.card (PhysicalPower d n)) ×
      Fin (Fintype.card (PhysicalPower d n))) ℂ =>
    (Matrix.trace (physicalTensorAntisymmetrizer d n * τ.submatrix e e)).re) :=
    Complex.continuous_re.comp
    ((continuous_const.matrix_mul hBasis).matrix_trace)
  have hF : Continuous f := continuous_const.sub
    ((winterBound_sqrt_continuous (PhysicalPower d n)).comp
      (continuous_const.sub hExp))
  have hClosed : IsClosed {τ | f τ ≤ (m : ℝ)} :=
    isClosed_le hF continuous_const
  apply closure_minimal (t := {τ | f τ ≤ (m : ℝ)}) ?_ hClosed hσ
  rintro τ ⟨T, rfl⟩
  exact physicalAntisymmetricState_finiteProtocol_projector_lower d hd n m T

theorem perCopy_physicalWinterBound_sqrt_tendsto_zero (d : ℕ) (epsilon : ℕ → ℝ)
    (hEpsilon : Filter.Tendsto epsilon Filter.atTop (nhds (0 : ℝ))) :
    Filter.Tendsto (fun n => QuantumProver.ConditionalEntropy.winterBound
      (PhysicalPower d n) (Real.sqrt (epsilon n)) / (n : ℝ))
      Filter.atTop (nhds (0 : ℝ)) := by
  simpa only [QuantumProver.ConditionalEntropy.winterBound, QuantumProver.ConditionalEntropy.logDimA,
    physicalPower_card, Fintype.card_fin] using
    QuantumProver.ConditionalEntropy.WeightedContinuity.perCopy_winterBound_sqrt_tendsto_zero
      d epsilon hEpsilon

theorem physicalAntisymmetricState_finiteProtocol_rate_lower
    (d : ℕ) (hd : 2 ≤ d) (m : ℕ → ℕ)
    (T : ∀ n : ℕ, FiniteLocalProtocol (Fintype.card (PhysicalPower d n))
      (Fintype.card (PhysicalPower d n)) (Fintype.card (PhysicalPower 2 (m n)))
      (Fintype.card (PhysicalPower 2 (m n))))
    (epsilon : ℕ → ℝ) (hEpsilon0 : ∀ n, 0 ≤ epsilon n) (hEpsilon1 : ∀ n, epsilon n ≤ 1)
    (hDistance : ∀ n, SchattenSupport.schattenOne
      (physicalFiniteProtocolOutput d n (m n) (T n) - physicalAntisymmetricState d n) / 2 ≤
        epsilon n)
    (hEpsilon : Filter.Tendsto epsilon Filter.atTop (nhds (0 : ℝ)))
    (r : ℝ) (hRate : Filter.Tendsto (fun n => (m n : ℝ) / (n : ℝ))
      Filter.atTop (nhds r)) : 1 ≤ r := by
  have hCorrection := perCopy_physicalWinterBound_sqrt_tendsto_zero d epsilon hEpsilon
  have hLowerLimit : Filter.Tendsto (fun n => 1 -
      QuantumProver.ConditionalEntropy.winterBound (PhysicalPower d n) (Real.sqrt (epsilon n)) /
        (n : ℝ)) Filter.atTop (nhds (1 : ℝ)) := by
    simpa only [sub_zero] using (tendsto_const_nhds (x := (1 : ℝ))).sub hCorrection
  apply le_of_tendsto_of_tendsto hLowerLimit hRate
  filter_upwards [Filter.eventually_gt_atTop (0 : ℕ)] with n hn
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hResource := physicalAntisymmetricState_finiteProtocol_resource_lower d hd n (m n)
    (T n) (epsilon n) (hEpsilon0 n) (hEpsilon1 n) (hDistance n)
  have hDiv := (div_le_div_iff_of_pos_right hnR).mpr hResource
  simpa only [sub_div, div_self (ne_of_gt hnR)] using hDiv

theorem physicalAntisymmetricState_finiteProtocol_rate_one (d : ℕ) (hd : 2 ≤ d) :
    ∃ m : ℕ → ℕ,
      (∀ n : ℕ, ∃ T : FiniteLocalProtocol (Fintype.card (PhysicalPower d n))
        (Fintype.card (PhysicalPower d n)) (Fintype.card (PhysicalPower 2 (m n)))
        (Fintype.card (PhysicalPower 2 (m n))),
        T.apply (pureDensity (finiteBellPairPowerVector (m n))) =
          finitePhysicalAntisymmetricState d n) ∧
      Filter.Tendsto (fun n => (m n : ℝ) / (n : ℝ)) Filter.atTop (nhds (1 : ℝ)) := by
  refine ⟨fun n => n, fun n => ⟨endpointFiniteLocalProtocol d hd n,
    endpointFiniteLocalProtocol_bell_output d hd n⟩, ?_⟩
  have hEqual : (fun _ : ℕ => (1 : ℝ)) =ᶠ[Filter.atTop]
      (fun n : ℕ => (n : ℝ) / (n : ℝ)) := by
    filter_upwards [Filter.eventually_gt_atTop (0 : ℕ)] with n hn
    exact (div_self (by exact_mod_cast (Nat.ne_of_gt hn))).symm
  exact tendsto_const_nhds.congr' hEqual

theorem physicalFiniteProtocolOutput_density (d n m : ℕ)
    (T : FiniteLocalProtocol (Fintype.card (PhysicalPower d n))
      (Fintype.card (PhysicalPower d n)) (Fintype.card (PhysicalPower 2 m))
      (Fintype.card (PhysicalPower 2 m))) :
    (physicalFiniteProtocolOutput d n m T).PosSemidef ∧
      (physicalFiniteProtocolOutput d n m T).trace = 1 := by
  obtain ⟨E, _⟩ := physicalFiniteProtocolOutput_entropyEnsemble d n m T
  exact ⟨E.posSemidef, E.trace_one⟩

theorem endpoint_binaryEntropy_nonneg (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    0 ≤ QuantumProver.ConditionalEntropy.binaryEntropy p := by
  unfold QuantumProver.ConditionalEntropy.binaryEntropy
    QuantumProver.SuperchannelDiscrimination.FlaggedStates.flagEntropyBits
  exact div_nonneg (neg_nonneg.mpr (add_nonpos
    (Real.mul_log_nonpos hp0 hp1)
    (Real.mul_log_nonpos (sub_nonneg.mpr hp1) (by linarith))))
    (le_of_lt (Real.log_pos (by norm_num : (1 : ℝ) < 2)))

theorem perCopy_physicalWinterBound_le (d n : ℕ) (hn : 0 < n)
    (delta : ℝ) (hDelta : 0 ≤ delta) :
    QuantumProver.ConditionalEntropy.winterBound (PhysicalPower d n) delta / (n : ℝ) ≤
      QuantumProver.ConditionalEntropy.winterBound (Fin d) delta := by
  let L := Real.log (d : ℝ) / Real.log 2
  let noise := (1 + delta) *
    QuantumProver.ConditionalEntropy.binaryEntropy (delta / (1 + delta))
  have hDen : 0 < 1 + delta := by linarith
  have hp0 : 0 ≤ delta / (1 + delta) := div_nonneg hDelta (le_of_lt hDen)
  have hp1 : delta / (1 + delta) ≤ 1 := by
    exact (div_le_one hDen).mpr (by linarith)
  have hNoise : 0 ≤ noise := mul_nonneg (le_of_lt hDen)
    (endpoint_binaryEntropy_nonneg _ hp0 hp1)
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Nat.succ_le_of_lt hn)
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hFormula : QuantumProver.ConditionalEntropy.winterBound (PhysicalPower d n) delta =
      (n : ℝ) * (2 * delta * L) + noise := by
    simp only [QuantumProver.ConditionalEntropy.winterBound, QuantumProver.ConditionalEntropy.logDimA,
      physicalPower_card, Fintype.card_fin, Nat.cast_pow, Real.log_pow]
    dsimp only [L, noise]
    ring
  have hOne : QuantumProver.ConditionalEntropy.winterBound (Fin d) delta =
      2 * delta * L + noise := by
    simp only [QuantumProver.ConditionalEntropy.winterBound, QuantumProver.ConditionalEntropy.logDimA,
      Fintype.card_fin]
    rfl
  apply (div_le_iff₀ hnR).mpr
  rw [hFormula, hOne]
  nlinarith [mul_le_mul_of_nonneg_right hn1 hNoise]

theorem physicalAntisymmetricState_finiteProtocol_bures_resource_lower
    (d : ℕ) (hd : 2 ≤ d) (n m : ℕ)
    (T : FiniteLocalProtocol (Fintype.card (PhysicalPower d n))
      (Fintype.card (PhysicalPower d n)) (Fintype.card (PhysicalPower 2 m))
      (Fintype.card (PhysicalPower 2 m)))
    (epsilon : ℝ) (hEpsilon0 : 0 ≤ epsilon) (hEpsilon1 : epsilon ≤ 1)
    (hBures : FidelityError.buresDistance (physicalFiniteProtocolOutput d n m T)
      (physicalAntisymmetricState d n) ≤ epsilon) :
    (n : ℝ) - QuantumProver.ConditionalEntropy.winterBound (PhysicalPower d n)
      (Real.sqrt epsilon) ≤ (m : ℝ) := by
  apply physicalAntisymmetricState_finiteProtocol_resource_lower d hd n m T epsilon
    hEpsilon0 hEpsilon1
  exact FidelityError.halfTraceDistance_le_of_buresDistance_le _ _
    (physicalFiniteProtocolOutput_density d n m T)
    (physicalAntisymmetricState_density d hd n) epsilon hBures

theorem physicalAntisymmetricState_finiteProtocol_bures_uniform_rate_lower
    (d : ℕ) (hd : 2 ≤ d) (n m : ℕ) (hn : 0 < n)
    (T : FiniteLocalProtocol (Fintype.card (PhysicalPower d n))
      (Fintype.card (PhysicalPower d n)) (Fintype.card (PhysicalPower 2 m))
      (Fintype.card (PhysicalPower 2 m)))
    (epsilon : ℝ) (hEpsilon0 : 0 ≤ epsilon) (hEpsilon1 : epsilon ≤ 1)
    (hBures : FidelityError.buresDistance (physicalFiniteProtocolOutput d n m T)
      (physicalAntisymmetricState d n) ≤ epsilon) :
    1 - QuantumProver.ConditionalEntropy.winterBound (Fin d) (Real.sqrt epsilon) ≤
      (m : ℝ) / (n : ℝ) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hResource := physicalAntisymmetricState_finiteProtocol_bures_resource_lower
    d hd n m T epsilon hEpsilon0 hEpsilon1 hBures
  have hDiv := (div_le_div_iff_of_pos_right hnR).mpr hResource
  rw [sub_div, div_self (ne_of_gt hnR)] at hDiv
  have hUniform := perCopy_physicalWinterBound_le d n hn
    (Real.sqrt epsilon) (Real.sqrt_nonneg epsilon)
  linarith

def finiteHHTAchievableRate (d : ℕ) (r : ℝ) : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon → ∀ delta : ℝ, 0 < delta →
    ∃ n m : ℕ, 0 < n ∧
      ∃ T : FiniteLocalProtocol (Fintype.card (PhysicalPower d n))
        (Fintype.card (PhysicalPower d n)) (Fintype.card (PhysicalPower 2 m))
        (Fintype.card (PhysicalPower 2 m)),
        |r - (m : ℝ) / (n : ℝ)| ≤ delta ∧
        FidelityError.buresDistance (physicalFiniteProtocolOutput d n m T)
          (physicalAntisymmetricState d n) ≤ epsilon

def finiteHHTCost (d : ℕ) : ℝ := sInf {r : ℝ | finiteHHTAchievableRate d r}

theorem physicalFiniteProtocolOutput_endpoint (d : ℕ) (hd : 2 ≤ d) (n : ℕ) :
    physicalFiniteProtocolOutput d n n (endpointFiniteLocalProtocol d hd n) =
      physicalAntisymmetricState d n := by
  unfold physicalFiniteProtocolOutput
  rw [endpointFiniteLocalProtocol_bell_output]
  simp [finitePhysicalAntisymmetricState, Matrix.submatrix_submatrix, Function.comp_def]
  rfl

theorem finiteHHTAchievableRate_one (d : ℕ) (hd : 2 ≤ d) :
    finiteHHTAchievableRate d 1 := by
  intro epsilon hEpsilon delta hDelta
  refine ⟨1, 1, by norm_num, endpointFiniteLocalProtocol d hd 1, ?_, ?_⟩
  · norm_num
    exact le_of_lt hDelta
  · rw [physicalFiniteProtocolOutput_endpoint,
      FidelityError.buresDistance_self _ (physicalAntisymmetricState_density d hd 1)]
    exact le_of_lt hEpsilon

theorem finiteHHTAchievableRate_lower (d : ℕ) (hd : 2 ≤ d) (r : ℝ)
    (hRate : finiteHHTAchievableRate d r) : 1 ≤ r := by
  let epsilon : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
  have hPositive : ∀ k, 0 < epsilon k := fun k =>
    one_div_pos.mpr (by positivity)
  have hSmall : ∀ k, epsilon k ≤ 1 := by
    intro k
    exact (div_le_one (by positivity : 0 < (k : ℝ) + 1)).mpr
      (by linarith [Nat.cast_nonneg (α := ℝ) k])
  have hEpsilon : Filter.Tendsto epsilon Filter.atTop (nhds (0 : ℝ)) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hSqrt : Filter.Tendsto (fun k => Real.sqrt (epsilon k))
      Filter.atTop (nhds (0 : ℝ)) := by
    simpa only [Function.comp_def, Real.sqrt_zero] using
      Real.continuous_sqrt.continuousAt.tendsto.comp hEpsilon
  have hCorrection : Filter.Tendsto
      (fun k => QuantumProver.ConditionalEntropy.winterBound (Fin d) (Real.sqrt (epsilon k)))
      Filter.atTop (nhds (0 : ℝ)) :=
    (QuantumProver.ConditionalEntropy.winterBound_tendsto_zero (Fin d)).comp hSqrt
  have hBound : ∀ k, 1 -
      QuantumProver.ConditionalEntropy.winterBound (Fin d) (Real.sqrt (epsilon k)) - epsilon k ≤ r := by
    intro k
    obtain ⟨n, m, hn, T, hApprox, hBures⟩ :=
      hRate (epsilon k) (hPositive k) (epsilon k) (hPositive k)
    have hResource := physicalAntisymmetricState_finiteProtocol_bures_uniform_rate_lower
      d hd n m hn T (epsilon k) (le_of_lt (hPositive k)) (hSmall k) hBures
    have hRatio := (abs_le.mp hApprox).1
    linarith
  have hLimit : Filter.Tendsto (fun k => 1 -
      QuantumProver.ConditionalEntropy.winterBound (Fin d) (Real.sqrt (epsilon k)) - epsilon k)
      Filter.atTop (nhds (1 : ℝ)) := by
    simpa only [sub_zero] using
      ((tendsto_const_nhds (x := (1 : ℝ))).sub hCorrection).sub hEpsilon
  exact le_of_tendsto_of_tendsto hLimit tendsto_const_nhds (Filter.Eventually.of_forall hBound)

theorem finiteHHTCost_eq_one (d : ℕ) (hd : 2 ≤ d) : finiteHHTCost d = 1 := by
  unfold finiteHHTCost
  have hOne : (1 : ℝ) ∈ {r : ℝ | finiteHHTAchievableRate d r} :=
    finiteHHTAchievableRate_one d hd
  have hLower : ∀ r ∈ {r : ℝ | finiteHHTAchievableRate d r}, (1 : ℝ) ≤ r :=
    fun r hr => finiteHHTAchievableRate_lower d hd r hr
  exact le_antisymm (csInf_le ⟨1, hLower⟩ hOne) (le_csInf ⟨1, hOne⟩ hLower)

def physicalQubitEquiv : (n : ℕ) → PhysicalPower 2 n ≃ SingletResource.QubitPower n
  | 0 => Equiv.refl Unit
  | n + 1 => (Equiv.refl (Fin 2)).prodCongr (physicalQubitEquiv n)

def finiteQubitEquiv (n : ℕ) :
    Fin (Fintype.card (PhysicalPower 2 n)) ≃ SingletResource.QubitPower n :=
  (Fintype.equivFin (PhysicalPower 2 n)).symm.trans (physicalQubitEquiv n)

theorem bellPairPowerVector_eq_singletProvider (n : ℕ) :
    bellPairPowerVector n = SingletResource.bellPowerVector n ∘
      ((physicalQubitEquiv n).prodCongr (physicalQubitEquiv n)) := by
  induction n with
  | zero =>
      rw [bellPairPowerVector_zero]
      rfl
  | succ n ih =>
      ext ⟨⟨a, r⟩, ⟨b, s⟩⟩
      rw [bellPairPowerVector_succ]
      rw [ih]
      rfl

theorem finiteBellPairPowerVector_eq_singletProvider (n : ℕ) :
    finiteBellPairPowerVector n =
      SingletResource.bellVectorIn n (finiteQubitEquiv n) := by
  unfold finiteBellPairPowerVector
  rw [bellPairPowerVector_eq_singletProvider]
  rfl

def finiteSingletPairPowerVector (n : ℕ) :
    Fin (Fintype.card (PhysicalPower 2 n)) × Fin (Fintype.card (PhysicalPower 2 n)) → ℂ :=
  SingletResource.singletVectorIn n (finiteQubitEquiv n)

theorem finiteSingletPairPowerVector_normSq (n : ℕ) :
    vectorNormSq (finiteSingletPairPowerVector n) = 1 :=
  SingletResource.singletVectorIn_normSq n (finiteQubitEquiv n)

def physicalFiniteSingletProtocolOutput (d n m : ℕ)
    (T : FiniteLocalProtocol (Fintype.card (PhysicalPower d n))
      (Fintype.card (PhysicalPower d n)) (Fintype.card (PhysicalPower 2 m))
      (Fintype.card (PhysicalPower 2 m))) :
    Matrix (PhysicalPower d n × PhysicalPower d n)
      (PhysicalPower d n × PhysicalPower d n) ℂ :=
  (T.apply (pureDensity (finiteSingletPairPowerVector m))).submatrix
    (physicalPairFiniteEquiv d n).symm (physicalPairFiniteEquiv d n).symm

theorem physicalFiniteSingletProtocolOutput_toBell (d n m : ℕ)
    (T : FiniteLocalProtocol (Fintype.card (PhysicalPower d n))
      (Fintype.card (PhysicalPower d n)) (Fintype.card (PhysicalPower 2 m))
      (Fintype.card (PhysicalPower 2 m))) :
    physicalFiniteSingletProtocolOutput d n m
      (SingletResource.singletToBellProtocol m (finiteQubitEquiv m) T) =
      physicalFiniteProtocolOutput d n m T := by
  unfold physicalFiniteSingletProtocolOutput finiteSingletPairPowerVector
  rw [SingletResource.singletToBellProtocol_output]
  unfold physicalFiniteProtocolOutput
  rw [finiteBellPairPowerVector_eq_singletProvider]

theorem physicalFiniteProtocolOutput_toSinglet (d n m : ℕ)
    (T : FiniteLocalProtocol (Fintype.card (PhysicalPower d n))
      (Fintype.card (PhysicalPower d n)) (Fintype.card (PhysicalPower 2 m))
      (Fintype.card (PhysicalPower 2 m))) :
    physicalFiniteProtocolOutput d n m
      (SingletResource.bellToSingletProtocol m (finiteQubitEquiv m) T) =
      physicalFiniteSingletProtocolOutput d n m T := by
  unfold physicalFiniteProtocolOutput
  rw [finiteBellPairPowerVector_eq_singletProvider,
    SingletResource.bellToSingletProtocol_output]
  rfl

def finiteSingletHHTAchievableRate (d : ℕ) (r : ℝ) : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon → ∀ delta : ℝ, 0 < delta →
    ∃ n m : ℕ, 0 < n ∧
      ∃ T : FiniteLocalProtocol (Fintype.card (PhysicalPower d n))
        (Fintype.card (PhysicalPower d n)) (Fintype.card (PhysicalPower 2 m))
        (Fintype.card (PhysicalPower 2 m)),
        |r - (m : ℝ) / (n : ℝ)| ≤ delta ∧
        FidelityError.buresDistance (physicalFiniteSingletProtocolOutput d n m T)
          (physicalAntisymmetricState d n) ≤ epsilon

def finiteSingletHHTCost (d : ℕ) : ℝ :=
  sInf {r : ℝ | finiteSingletHHTAchievableRate d r}

theorem finiteSingletHHTAchievableRate_iff (d : ℕ) (r : ℝ) :
    finiteSingletHHTAchievableRate d r ↔ finiteHHTAchievableRate d r := by
  constructor
  · intro h epsilon hEpsilon delta hDelta
    obtain ⟨n, m, hn, T, hRatio, hError⟩ := h epsilon hEpsilon delta hDelta
    refine ⟨n, m, hn, SingletResource.bellToSingletProtocol m (finiteQubitEquiv m) T,
      hRatio, ?_⟩
    rw [physicalFiniteProtocolOutput_toSinglet]
    exact hError
  · intro h epsilon hEpsilon delta hDelta
    obtain ⟨n, m, hn, T, hRatio, hError⟩ := h epsilon hEpsilon delta hDelta
    refine ⟨n, m, hn, SingletResource.singletToBellProtocol m (finiteQubitEquiv m) T,
      hRatio, ?_⟩
    rw [physicalFiniteSingletProtocolOutput_toBell]
    exact hError

theorem finiteSingletHHTCost_eq_finiteHHTCost (d : ℕ) :
    finiteSingletHHTCost d = finiteHHTCost d := by
  unfold finiteSingletHHTCost finiteHHTCost
  congr 1
  exact Set.ext (fun r => finiteSingletHHTAchievableRate_iff d r)

theorem finiteSingletHHTCost_eq_one (d : ℕ) (hd : 2 ≤ d) :
    finiteSingletHHTCost d = 1 := by
  rw [finiteSingletHHTCost_eq_finiteHHTCost, finiteHHTCost_eq_one d hd]

theorem finiteOutputs_singlet_eq_bell (m c d : ℕ) :
    EndpointProtocolClosure.finiteOutputs (c := c) (d := d)
      (finiteSingletPairPowerVector m) =
      EndpointProtocolClosure.finiteOutputs (c := c) (d := d)
        (finiteBellPairPowerVector m) := by
  ext rho
  constructor
  · rintro ⟨T, hT⟩
    refine ⟨SingletResource.bellToSingletProtocol m (finiteQubitEquiv m) T, ?_⟩
    rw [finiteBellPairPowerVector_eq_singletProvider,
      SingletResource.bellToSingletProtocol_output]
    exact hT
  · rintro ⟨T, hT⟩
    refine ⟨SingletResource.singletToBellProtocol m (finiteQubitEquiv m) T, ?_⟩
    unfold finiteSingletPairPowerVector
    rw [SingletResource.singletToBellProtocol_output,
      ← finiteBellPairPowerVector_eq_singletProvider]
    exact hT

theorem outputClosure_singlet_eq_bell (m c d : ℕ) :
    EndpointProtocolClosure.outputClosure (c := c) (d := d)
      (finiteSingletPairPowerVector m) =
      EndpointProtocolClosure.outputClosure (c := c) (d := d)
        (finiteBellPairPowerVector m) := by
  unfold EndpointProtocolClosure.outputClosure
  rw [finiteOutputs_singlet_eq_bell]

universe u

def physicalContinuousSingletProtocolOutput (d n m height : ℕ)
    (T : MatrixContinuousStateProtocol.Tree.{u}
      (Fintype.card (PhysicalPower d n)) (Fintype.card (PhysicalPower d n))
      (Fintype.card (PhysicalPower 2 m)) (Fintype.card (PhysicalPower 2 m)) height) :
    Matrix (PhysicalPower d n × PhysicalPower d n)
      (PhysicalPower d n × PhysicalPower d n) ℂ :=
  (MatrixContinuousStateProtocol.channel T (pureDensity (finiteSingletPairPowerVector m))).submatrix
    (physicalPairFiniteEquiv d n).symm (physicalPairFiniteEquiv d n).symm

@[simp] theorem physicalContinuousSingletProtocolOutput_finite (d n m height : ℕ)
    (T : FiniteLocalProtocol (Fintype.card (PhysicalPower d n))
      (Fintype.card (PhysicalPower d n)) (Fintype.card (PhysicalPower 2 m))
      (Fintype.card (PhysicalPower 2 m))) :
    physicalContinuousSingletProtocolOutput d n m height
      (MatrixContinuousStateProtocol.Tree.finite height T) =
      physicalFiniteSingletProtocolOutput d n m T := rfl

theorem physicalContinuousSingletProtocolOutput_density (d n m height : ℕ)
    (T : MatrixContinuousStateProtocol.Tree.{u}
      (Fintype.card (PhysicalPower d n)) (Fintype.card (PhysicalPower d n))
      (Fintype.card (PhysicalPower 2 m)) (Fintype.card (PhysicalPower 2 m)) height)
    (hT : MatrixContinuousStateProtocol.WellFormed T) :
    (physicalContinuousSingletProtocolOutput d n m height T).PosSemidef ∧
      (physicalContinuousSingletProtocolOutput d n m height T).trace = 1 := by
  have hDensity := MatrixContinuousStateProtocol.channel_pureOutput_isDensity
    T hT (finiteSingletPairPowerVector m) (finiteSingletPairPowerVector_normSq m)
  refine ⟨hDensity.1.submatrix _, ?_⟩
  unfold physicalContinuousSingletProtocolOutput
  have hTrace := (physicalPairFiniteEquiv d n).symm.sum_comp
    (fun i => MatrixContinuousStateProtocol.channel T
      (pureDensity (finiteSingletPairPowerVector m)) i i)
  exact hTrace.trans hDensity.2

theorem physicalAntisymmetricState_continuousSingletProtocol_projector_lower
    (d : ℕ) (hd : 2 ≤ d) (n m height : ℕ)
    (T : MatrixContinuousStateProtocol.Tree.{u}
      (Fintype.card (PhysicalPower d n)) (Fintype.card (PhysicalPower d n))
      (Fintype.card (PhysicalPower 2 m)) (Fintype.card (PhysicalPower 2 m)) height)
    (hT : MatrixContinuousStateProtocol.WellFormed T) :
    (n : ℝ) - QuantumProver.ConditionalEntropy.winterBound (PhysicalPower d n)
      (Real.sqrt (1 - (Matrix.trace (physicalTensorAntisymmetrizer d n *
        physicalContinuousSingletProtocolOutput d n m height T)).re)) ≤ (m : ℝ) := by
  have hClosure := MatrixContinuousStateProtocol.channel_pureOutput_mem_outputClosure
    T hT (finiteSingletPairPowerVector m)
  rw [outputClosure_singlet_eq_bell] at hClosure
  exact physicalAntisymmetricState_finiteOutputClosure_projector_lower d hd n m _ hClosure

theorem physicalAntisymmetricState_continuousSingletProtocol_leakage_bounds
    (d : ℕ) (hd : 2 ≤ d) (n m height : ℕ)
    (T : MatrixContinuousStateProtocol.Tree.{u}
      (Fintype.card (PhysicalPower d n)) (Fintype.card (PhysicalPower d n))
      (Fintype.card (PhysicalPower 2 m)) (Fintype.card (PhysicalPower 2 m)) height)
    (hT : MatrixContinuousStateProtocol.WellFormed T) (epsilon : ℝ)
    (hBures : FidelityError.buresDistance
      (physicalContinuousSingletProtocolOutput d n m height T)
      (physicalAntisymmetricState d n) ≤ epsilon) :
    0 ≤ 1 - (Matrix.trace (physicalTensorAntisymmetrizer d n *
      physicalContinuousSingletProtocolOutput d n m height T)).re ∧
    1 - (Matrix.trace (physicalTensorAntisymmetrizer d n *
      physicalContinuousSingletProtocolOutput d n m height T)).re ≤ epsilon := by
  let rho := physicalContinuousSingletProtocolOutput d n m height T
  have hRho := physicalContinuousSingletProtocolOutput_density d n m height T hT
  have hEffect := projector_isEffect (physicalTensorAntisymmetrizer d n)
    (physicalTensorAntisymmetrizer_hermitian d n)
    (physicalTensorAntisymmetrizer_idempotent d n)
  have hAccept := QuantumProver.SuperchannelDiscrimination.FlaggedStates.acceptanceProbability_bounds
    hRho hEffect
  rw [QuantumProver.SuperchannelDiscrimination.FlaggedStates.acceptanceProbability,
    Matrix.trace_mul_comm] at hAccept
  have hDistance := FidelityError.halfTraceDistance_le_of_buresDistance_le
    rho (physicalAntisymmetricState d n) hRho
    (physicalAntisymmetricState_density d hd n) epsilon hBures
  unfold FidelityError.halfTraceDistance at hDistance
  have hTrace : rho.trace = (physicalAntisymmetricState d n).trace := by
    rw [hRho.2, (physicalAntisymmetricState_density d hd n).2]
  have hExp := effect_expectation_schatten_distance
    (physicalTensorAntisymmetrizer d n) rho (physicalAntisymmetricState d n)
    hEffect hRho.1.isHermitian (physicalAntisymmetricState_posSemidef d n).isHermitian hTrace
  rw [physicalAntisymmetricState_projector_expectation_one d hd n] at hExp
  have hLow := (abs_le.mp hExp).1
  constructor <;> dsimp only [rho] at * <;> linarith

theorem physicalAntisymmetricState_continuousSingletProtocol_uniform_rate_lower
    (d : ℕ) (hd : 2 ≤ d) (n m height : ℕ) (hn : 0 < n)
    (T : MatrixContinuousStateProtocol.Tree.{u}
      (Fintype.card (PhysicalPower d n)) (Fintype.card (PhysicalPower d n))
      (Fintype.card (PhysicalPower 2 m)) (Fintype.card (PhysicalPower 2 m)) height)
    (hT : MatrixContinuousStateProtocol.WellFormed T) :
    1 - QuantumProver.ConditionalEntropy.winterBound (Fin d)
      (Real.sqrt (1 - (Matrix.trace (physicalTensorAntisymmetrizer d n *
        physicalContinuousSingletProtocolOutput d n m height T)).re)) ≤
      (m : ℝ) / (n : ℝ) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hResource := physicalAntisymmetricState_continuousSingletProtocol_projector_lower
    d hd n m height T hT
  have hDiv := (div_le_div_iff_of_pos_right hnR).mpr hResource
  rw [sub_div, div_self (ne_of_gt hnR)] at hDiv
  have hUniform := perCopy_physicalWinterBound_le d n hn
    (Real.sqrt (1 - (Matrix.trace (physicalTensorAntisymmetrizer d n *
      physicalContinuousSingletProtocolOutput d n m height T)).re)) (Real.sqrt_nonneg _)
  linarith

def finiteHeightSingletHHTAchievableRate (d : ℕ) (r : ℝ) : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon → ∀ delta : ℝ, 0 < delta →
    ∃ n m : ℕ, 0 < n ∧ ∃ height : ℕ,
      ∃ T : MatrixContinuousStateProtocol.Tree.{u}
        (Fintype.card (PhysicalPower d n)) (Fintype.card (PhysicalPower d n))
        (Fintype.card (PhysicalPower 2 m)) (Fintype.card (PhysicalPower 2 m)) height,
        MatrixContinuousStateProtocol.WellFormed T ∧
        |r - (m : ℝ) / (n : ℝ)| ≤ delta ∧
        FidelityError.buresDistance (physicalContinuousSingletProtocolOutput d n m height T)
          (physicalAntisymmetricState d n) ≤ epsilon

def finiteHeightSingletHHTCost (d : ℕ) : ℝ :=
  sInf {r : ℝ | finiteHeightSingletHHTAchievableRate.{u} d r}

theorem finiteHeightSingletHHTAchievableRate_one (d : ℕ) (hd : 2 ≤ d) :
    finiteHeightSingletHHTAchievableRate.{u} d 1 := by
  intro epsilon hEpsilon delta hDelta
  obtain ⟨n, m, hn, T, hRatio, hError⟩ :=
    (finiteSingletHHTAchievableRate_iff d 1).mpr
      (finiteHHTAchievableRate_one d hd) epsilon hEpsilon delta hDelta
  exact ⟨n, m, hn, 0, MatrixContinuousStateProtocol.Tree.finite 0 T,
    trivial, hRatio, hError⟩

theorem finiteHeightSingletHHTAchievableRate_lower (d : ℕ) (hd : 2 ≤ d) (r : ℝ)
    (hRate : finiteHeightSingletHHTAchievableRate.{u} d r) : 1 ≤ r := by
  classical
  let epsilon : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
  have hPositive : ∀ k, 0 < epsilon k := fun k => one_div_pos.mpr (by positivity)
  have hEpsilon : Filter.Tendsto epsilon Filter.atTop (nhds (0 : ℝ)) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  choose n m hn height T hT hApprox hBures using
    fun k : ℕ => hRate (epsilon k) (hPositive k) (epsilon k) (hPositive k)
  let leakage : ℕ → ℝ := fun k => 1 - (Matrix.trace (physicalTensorAntisymmetrizer d (n k) *
    physicalContinuousSingletProtocolOutput d (n k) (m k) (height k) (T k))).re
  have hLeak : ∀ k, 0 ≤ leakage k ∧ leakage k ≤ epsilon k := fun k =>
    physicalAntisymmetricState_continuousSingletProtocol_leakage_bounds
      d hd (n k) (m k) (height k) (T k) (hT k) (epsilon k) (hBures k)
  have hLeakLimit : Filter.Tendsto leakage Filter.atTop (nhds (0 : ℝ)) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hEpsilon
      (fun k => (hLeak k).1) (fun k => (hLeak k).2)
  have hSqrt : Filter.Tendsto (fun k => Real.sqrt (leakage k))
      Filter.atTop (nhds (0 : ℝ)) := by
    simpa only [Function.comp_def, Real.sqrt_zero] using
      Real.continuous_sqrt.continuousAt.tendsto.comp hLeakLimit
  have hCorrection : Filter.Tendsto
      (fun k => QuantumProver.ConditionalEntropy.winterBound (Fin d) (Real.sqrt (leakage k)))
      Filter.atTop (nhds (0 : ℝ)) :=
    (QuantumProver.ConditionalEntropy.winterBound_tendsto_zero (Fin d)).comp hSqrt
  have hBound : ∀ k, 1 -
      QuantumProver.ConditionalEntropy.winterBound (Fin d) (Real.sqrt (leakage k)) - epsilon k ≤ r := by
    intro k
    have hResource := physicalAntisymmetricState_continuousSingletProtocol_uniform_rate_lower
      d hd (n k) (m k) (height k) (hn k) (T k) (hT k)
    have hRatio := (abs_le.mp (hApprox k)).1
    change 1 - QuantumProver.ConditionalEntropy.winterBound (Fin d) (Real.sqrt (leakage k)) ≤
      (m k : ℝ) / (n k : ℝ) at hResource
    linarith
  have hLimit : Filter.Tendsto (fun k => 1 -
      QuantumProver.ConditionalEntropy.winterBound (Fin d) (Real.sqrt (leakage k)) - epsilon k)
      Filter.atTop (nhds (1 : ℝ)) := by
    simpa only [sub_zero] using
      ((tendsto_const_nhds (x := (1 : ℝ))).sub hCorrection).sub hEpsilon
  exact le_of_tendsto_of_tendsto hLimit tendsto_const_nhds (Filter.Eventually.of_forall hBound)

theorem finiteHeightSingletHHTCost_eq_one (d : ℕ) (hd : 2 ≤ d) :
    finiteHeightSingletHHTCost.{u} d = 1 := by
  unfold finiteHeightSingletHHTCost
  have hOne : (1 : ℝ) ∈ {r : ℝ | finiteHeightSingletHHTAchievableRate.{u} d r} :=
    finiteHeightSingletHHTAchievableRate_one d hd
  have hLower : ∀ r ∈ {r : ℝ | finiteHeightSingletHHTAchievableRate.{u} d r}, (1 : ℝ) ≤ r :=
    fun r hr => finiteHeightSingletHHTAchievableRate_lower d hd r hr
  exact le_antisymm (csInf_le ⟨1, hLower⟩ hOne) (le_csInf ⟨1, hOne⟩ hLower)

end QuantumProver.WernerEndpoint

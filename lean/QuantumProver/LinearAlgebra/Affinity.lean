import Mathlib
import QuantumProver.InformationTheory.SuperchannelDiscrimination.CPTPKraus
import QuantumProver.InformationTheory.SuperchannelDiscrimination.TestingTheorems

noncomputable section

open scoped BigOperators ComplexOrder MatrixOrder Matrix Matrix.Norms.L2Operator Kronecker
open Filter Topology

namespace QuantumProver.MatrixAnalysis.Affinity

open QuantumProver.SuperchannelDiscrimination

variable {I J K : Type*} [Fintype I] [Fintype J] [Fintype K]
  [DecidableEq I] [DecidableEq J] [DecidableEq K]

abbrev sqrtPSD (A : Matrix I I ℂ) : Matrix I I ℂ := CFC.sqrt A

def affinity (A B : Matrix I I ℂ) : ℝ := (Matrix.trace (sqrtPSD A * sqrtPSD B)).re

theorem sqrtPSD_posSemidef (A : Matrix I I ℂ) : (sqrtPSD A).PosSemidef :=
  Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)

theorem sqrtPSD_hermitian (A : Matrix I I ℂ) : (sqrtPSD A).IsHermitian :=
  (sqrtPSD_posSemidef A).isHermitian

theorem sqrtPSD_square (A : Matrix I I ℂ) (hA : A.PosSemidef) :
    sqrtPSD A * sqrtPSD A = A :=
  CFC.sqrt_mul_sqrt_self A hA.nonneg

theorem affinity_symm (A B : Matrix I I ℂ) : affinity A B = affinity B A := by
  unfold affinity
  rw [Matrix.trace_mul_comm]

theorem affinity_self (A : Matrix I I ℂ) (hA : A.PosSemidef) :
    affinity A A = A.trace.re := by
  unfold affinity
  rw [sqrtPSD_square A hA]

theorem affinity_nonneg (A B : Matrix I I ℂ) : 0 ≤ affinity A B := by
  let T := sqrtPSD (sqrtPSD A)
  have hT : Tᴴ = T := (sqrtPSD_hermitian (sqrtPSD A)).eq
  have hp : (T * sqrtPSD B * T).PosSemidef := by
    simpa only [hT] using (sqrtPSD_posSemidef B).conjTranspose_mul_mul_same T
  have heq : (T * sqrtPSD B * T).trace = (sqrtPSD A * sqrtPSD B).trace := by
    rw [Matrix.trace_mul_cycle]
    rw [show T * T = sqrtPSD A from sqrtPSD_square (sqrtPSD A) (sqrtPSD_posSemidef A)]
  have hn := (Complex.nonneg_iff.mp hp.trace_nonneg).1
  simpa only [heq, affinity] using hn

theorem tendsto_sqrtPSD {α : Type*} {l : Filter α}
    {X : α → Matrix I I ℂ} {A : Matrix I I ℂ}
    (hX : Tendsto X l (𝓝 A)) (hPSD : ∀ᶠ x in l, (X x).PosSemidef)
    (hA : A.PosSemidef) :
    Tendsto (fun x => sqrtPSD (X x)) l (𝓝 (sqrtPSD A)) := by
  have hwithin : Tendsto X l (𝓝[Set.Ici (0 : Matrix I I ℂ)] A) :=
    tendsto_nhdsWithin_iff.mpr ⟨hX, hPSD.mono (fun _ h => h.nonneg)⟩
  exact (CFC.continuousOn_sqrt A hA.nonneg).tendsto.comp hwithin

theorem tendsto_affinity {α : Type*} {l : Filter α}
    {X Y : α → Matrix I I ℂ} {A B : Matrix I I ℂ}
    (hX : Tendsto X l (𝓝 A)) (hY : Tendsto Y l (𝓝 B))
    (hPX : ∀ᶠ x in l, (X x).PosSemidef) (hPY : ∀ᶠ x in l, (Y x).PosSemidef)
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    Tendsto (fun x => affinity (X x) (Y x)) l (𝓝 (affinity A B)) := by
  have ht : Continuous (fun M : Matrix I I ℂ => M.trace.re) := by fun_prop
  exact ht.continuousAt.tendsto.comp
    ((tendsto_sqrtPSD hX hPX hA).mul (tendsto_sqrtPSD hY hPY hB))

theorem trace_re_mono {A B : Matrix I I ℂ} (h : A ≤ B) : A.trace.re ≤ B.trace.re := by
  have hp : (B - A).PosSemidef := Matrix.le_iff.mp h
  have hn := (Complex.nonneg_iff.mp hp.trace_nonneg).1
  simpa only [Matrix.trace_sub, Complex.sub_re, sub_nonneg] using hn

theorem isometry_mulVec_injective (V : Matrix J I ℂ) (hV : Vᴴ * V = 1) :
    Function.Injective V.mulVec := by
  intro x y h
  have h' := congrArg (fun z => Vᴴ.mulVec z) h
  simpa only [Matrix.mulVec_mulVec, hV, Matrix.one_mulVec] using h'

theorem isometry_complement_posSemidef (V : Matrix J I ℂ) (hV : Vᴴ * V = 1) :
    (1 - V * Vᴴ).PosSemidef := by
  have heq : (1 - V * Vᴴ)ᴴ * (1 - V * Vᴴ) = 1 - V * Vᴴ := by
    simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_one,
      Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    have hp : (V * Vᴴ) * (V * Vᴴ) = V * Vᴴ := by
      calc
        (V * Vᴴ) * (V * Vᴴ) = V * (Vᴴ * V) * Vᴴ := by simp only [Matrix.mul_assoc]
        _ = V * Vᴴ := by rw [hV, Matrix.mul_one]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hp]
    abel
  rw [← heq]
  exact Matrix.posSemidef_conjTranspose_mul_self _

theorem sqrtPSD_isometry (V : Matrix J I ℂ) (hV : Vᴴ * V = 1)
    (A : Matrix I I ℂ) (hA : A.PosSemidef) :
    sqrtPSD (V * A * Vᴴ) = V * sqrtPSD A * Vᴴ := by
  apply CFC.sqrt_unique
  · calc
      (V * sqrtPSD A * Vᴴ) * (V * sqrtPSD A * Vᴴ) =
          V * sqrtPSD A * (Vᴴ * V) * sqrtPSD A * Vᴴ := by
            simp only [Matrix.mul_assoc]
      _ = V * (sqrtPSD A * sqrtPSD A) * Vᴴ := by
        rw [hV, Matrix.mul_one]
        simp only [Matrix.mul_assoc]
      _ = V * A * Vᴴ := by rw [sqrtPSD_square A hA]
  · exact ((sqrtPSD_posSemidef A).mul_mul_conjTranspose_same V).nonneg

theorem affinity_isometry (V : Matrix J I ℂ) (hV : Vᴴ * V = 1)
    (A B : Matrix I I ℂ) (hA : A.PosSemidef) (hB : B.PosSemidef) :
    affinity (V * A * Vᴴ) (V * B * Vᴴ) = affinity A B := by
  unfold affinity
  rw [sqrtPSD_isometry V hV A hA, sqrtPSD_isometry V hV B hB]
  have heq : (V * sqrtPSD A * Vᴴ) * (V * sqrtPSD B * Vᴴ) =
      V * (sqrtPSD A * sqrtPSD B) * Vᴴ := by
    calc
      _ = V * sqrtPSD A * (Vᴴ * V) * sqrtPSD B * Vᴴ := by
        simp only [Matrix.mul_assoc]
      _ = _ := by rw [hV, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  rw [heq, Matrix.trace_mul_cycle, hV, Matrix.one_mul]

theorem sqrtPSD_compression (V : Matrix J I ℂ) (hV : Vᴴ * V = 1)
    (A : Matrix J J ℂ) (hA : A.PosSemidef) :
    Vᴴ * sqrtPSD A * V ≤ sqrtPSD (Vᴴ * A * V) := by
  let S := sqrtPSD A
  let B := Vᴴ * S * V
  have hS : Sᴴ = S := (sqrtPSD_hermitian A).eq
  have hB : B.PosSemidef := (sqrtPSD_posSemidef A).conjTranspose_mul_mul_same V
  have hgram : Vᴴ * A * V - B * B = (S * V)ᴴ * (1 - V * Vᴴ) * (S * V) := by
    dsimp [B]
    simp only [Matrix.conjTranspose_mul, hS, Matrix.mul_sub,
      Matrix.sub_mul, Matrix.mul_one]
    have hsquare : S * S = A := sqrtPSD_square A hA
    rw [← hsquare]
    simp only [Matrix.mul_assoc]
  have hle : B * B ≤ Vᴴ * A * V := by
    apply Matrix.le_iff.mpr
    rw [hgram]
    exact (isometry_complement_posSemidef V hV).conjTranspose_mul_mul_same (S * V)
  have hm := CFC.sqrt_le_sqrt (B * B) (Vᴴ * A * V) hle
  rw [CFC.sqrt_mul_self B hB.nonneg] at hm
  exact hm

theorem sqrtPSD_transpose (A : Matrix I I ℂ) (hA : A.PosSemidef) :
    sqrtPSD Aᵀ = (sqrtPSD A)ᵀ := by
  apply CFC.sqrt_unique
  · rw [← Matrix.transpose_mul, sqrtPSD_square A hA]
  · exact (sqrtPSD_posSemidef A).transpose.nonneg

theorem sqrtPSD_inverse (A : Matrix I I ℂ) (hA : A.PosSemidef) :
    sqrtPSD A⁻¹ = (sqrtPSD A)⁻¹ := by
  apply CFC.sqrt_unique
  · rw [← Matrix.mul_inv_rev, sqrtPSD_square A hA]
  · exact (sqrtPSD_posSemidef A).inv.nonneg

theorem sqrtPSD_kronecker (A : Matrix I I ℂ) (B : Matrix J J ℂ)
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    sqrtPSD (A ⊗ₖ B) = sqrtPSD A ⊗ₖ sqrtPSD B := by
  apply CFC.sqrt_unique
  · rw [← Matrix.mul_kronecker_mul, sqrtPSD_square A hA, sqrtPSD_square B hB]
  · exact ((sqrtPSD_posSemidef A).kronecker (sqrtPSD_posSemidef B)).nonneg

theorem sqrtPSD_flagBlock_zero (A : Matrix J J ℂ) (hA : A.PosSemidef) :
    sqrtPSD (FlaggedStates.flagBlock A (0 : Matrix I I ℂ)) =
      FlaggedStates.flagBlock (sqrtPSD A) (0 : Matrix I I ℂ) := by
  apply CFC.sqrt_unique
  · rw [FlaggedStates.flagBlock_mul, sqrtPSD_square A hA, Matrix.zero_mul]
  · exact (FlaggedStates.flagBlock_posSemidef (sqrtPSD_posSemidef A)
      Matrix.PosSemidef.zero).nonneg

theorem sqrtPSD_contraction (V : Matrix J I ℂ)
    (hV : (1 - Vᴴ * V).PosSemidef) (A : Matrix J J ℂ) (hA : A.PosSemidef) :
    Vᴴ * sqrtPSD A * V ≤ sqrtPSD (Vᴴ * A * V) := by
  have hiso := LogCompression.dilation_isometry V hV
  have h := sqrtPSD_compression (LogCompression.dilation V) hiso
    (FlaggedStates.flagBlock A (0 : Matrix I I ℂ))
    (FlaggedStates.flagBlock_posSemidef hA Matrix.PosSemidef.zero)
  rw [sqrtPSD_flagBlock_zero A hA] at h
  have heq (X : Matrix J J ℂ) :
      (LogCompression.dilation V)ᴴ *
          FlaggedStates.flagBlock X (0 : Matrix I I ℂ) * LogCompression.dilation V =
        Vᴴ * X * V := by
    simpa only [LogCompression.compression_apply, Matrix.mul_zero, Matrix.zero_mul,
      add_zero] using LogCompression.dilation_block_action V X (0 : Matrix I I ℂ)
  rw [heq, heq] at h
  exact h

theorem quadraticValue_mono {A B : Matrix I I ℂ} (h : A ≤ B) (v : I → ℂ) :
    MatrixLog.quadraticValue A v ≤ MatrixLog.quadraticValue B v := by
  have hz := MatrixLog.quadraticValue_nonneg (Matrix.le_iff.mp h) v
  rw [MatrixLog.quadraticValue_sub] at hz
  exact sub_nonneg.mp hz

theorem sqrtPSD_delta {A B : Matrix I I ℂ}
    (hA : A.PosDef) (hB : B.PosSemidef) :
    sqrtPSD (ModularMatrix.delta B A) =
      sqrtPSD B ⊗ₖ (sqrtPSD A⁻¹)ᵀ := by
  rw [ModularMatrix.delta, sqrtPSD_kronecker B A⁻¹ᵀ hB hA.inv.posSemidef.transpose,
    sqrtPSD_transpose A⁻¹ hA.inv.posSemidef]

theorem modular_sqrt_quadratic {A B : Matrix I I ℂ}
    (hA : A.PosDef) (hB : B.PosSemidef) :
    MatrixLog.quadraticValue (sqrtPSD (ModularMatrix.delta B A))
      (ModularMatrix.flatten (sqrtPSD A)) = affinity A B := by
  rw [sqrtPSD_delta hA hB, ModularMatrix.kronecker_transpose_quadratic]
  have hroot : (sqrtPSD A)ᴴ = sqrtPSD A := (sqrtPSD_hermitian A).eq
  letI : Invertible (sqrtPSD A) := (CPSchwarz.sqrt_posDef hA).isUnit.invertible
  rw [hroot, sqrtPSD_inverse A hA.posSemidef]
  rw [Matrix.mul_inv_cancel_right_of_invertible]
  rfl

theorem affinity_kraus_of_posDef {κ : Type*} [Fintype κ]
    (ops : κ → Matrix J I ℂ) (hops : KrausCompletion.krausGram ops = 1)
    {A B : Matrix I I ℂ} (hA : A.PosDef) (hB : B.PosSemidef)
    (hOut : (KrausCompletion.krausAction ops A).PosDef) :
    affinity A B ≤ affinity (KrausCompletion.krausAction ops A)
      (KrausCompletion.krausAction ops B) := by
  let V := ModularMatrix.pullbackMatrix ops A
  let X := ModularMatrix.delta B A
  let Y := ModularMatrix.delta (KrausCompletion.krausAction ops B)
    (KrausCompletion.krausAction ops A)
  have hc : (1 - Vᴴ * V).PosSemidef :=
    ModularMatrix.pullbackMatrix_contraction ops hops hA.posSemidef hOut
  have hX : X.PosSemidef := ModularMatrix.delta_posSemidef hA hB
  have hcomp : Vᴴ * X * V ≤ Y := Matrix.le_iff.mpr
    (ModularMatrix.pullbackMatrix_modular_order ops hops hA hB hOut)
  have hroot : Vᴴ * sqrtPSD X * V ≤ sqrtPSD Y :=
    (sqrtPSD_contraction V hc X hX).trans (CFC.sqrt_le_sqrt _ _ hcomp)
  have hq := quadraticValue_mono hroot
    (ModularMatrix.flatten (sqrtPSD (KrausCompletion.krausAction ops A)))
  rw [ModularMatrix.quadratic_congruence] at hq
  dsimp [V, X, Y] at hq
  rw [ModularMatrix.pullbackMatrix_sqrt ops hops hOut,
    modular_sqrt_quadratic hA hB,
    modular_sqrt_quadratic hOut (KrausCompletion.krausAction_posSemidef ops hB)] at hq
  exact hq

theorem affinity_kraus_of_faithful_identity {κ : Type*} [Fintype κ]
    (ops : κ → Matrix J I ℂ) (hops : KrausCompletion.krausGram ops = 1)
    (hOutOne : (KrausCompletion.krausAction ops (1 : Matrix I I ℂ)).PosDef)
    {A B : Matrix I I ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    affinity A B ≤ affinity (KrausCompletion.krausAction ops A)
      (KrausCompletion.krausAction ops B) := by
  let R := EntropyContinuity.regularizedNull A (1 : Matrix I I ℂ)
  have hR : Tendsto R (𝓝[>] (0 : ℝ)) (𝓝 A) :=
    (EntropyContinuity.regularizedNull_tendsto A 1).mono_left nhdsWithin_le_nhds
  have hPR : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), (R t).PosSemidef :=
    EntropyContinuity.eventually_regularizedNull_posSemidef hA Matrix.PosSemidef.one
  have hin := tendsto_affinity hR tendsto_const_nhds hPR
    (Eventually.of_forall (fun _ => hB)) hA hB
  have hc : Continuous (fun M : Matrix I I ℂ => KrausCompletion.krausAction ops M) := by
    unfold KrausCompletion.krausAction
    fun_prop
  have hPRout : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ),
      (KrausCompletion.krausAction ops (R t)).PosSemidef :=
    hPR.mono (fun _ h => KrausCompletion.krausAction_posSemidef ops h)
  have hout := tendsto_affinity (hc.continuousAt.tendsto.comp hR) tendsto_const_nhds
    hPRout (Eventually.of_forall (fun _ => KrausCompletion.krausAction_posSemidef ops hB))
    (KrausCompletion.krausAction_posSemidef ops hA)
    (KrausCompletion.krausAction_posSemidef ops hB)
  have hi : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), affinity (R t) B ≤
      affinity (KrausCompletion.krausAction ops (R t))
        (KrausCompletion.krausAction ops B) := by
    filter_upwards [EntropyContinuity.eventually_delta_unit] with t ht
    exact affinity_kraus_of_posDef ops hops
      (EntropyContinuity.regularizedNull_posDef hA Matrix.PosDef.one ht.1 ht.2.le) hB
      (EntropyContinuity.krausAction_regularizedNull_posDef ops hA hOutOne ht.1 ht.2.le)
  exact le_of_tendsto_of_tendsto hin hout hi

theorem affinity_kraus {κ : Type*} [Fintype κ]
    (ops : κ → Matrix J I ℂ) (hops : KrausCompletion.krausGram ops = 1)
    {A B : Matrix I I ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    affinity A B ≤ affinity (KrausCompletion.krausAction ops A)
      (KrausCompletion.krausAction ops B) := by
  classical
  let L := OutputSupport.compressedKraus ops (Matrix.PosDef.one (n := I) (R := ℂ))
  let U := OutputSupport.krausSupportIsometry ops (Matrix.PosDef.one (n := I) (R := ℂ))
  have hL : KrausCompletion.krausGram L = 1 :=
    OutputSupport.compressedKraus_gram ops hops Matrix.PosDef.one
  have hLI : (KrausCompletion.krausAction L (1 : Matrix I I ℂ)).PosDef :=
    OutputSupport.compressedKraus_comparator_posDef ops Matrix.PosDef.one
  have h := affinity_kraus_of_faithful_identity L hL hLI hA hB
  have hU : Uᴴ * U = 1 := OutputSupport.krausSupportIsometry_gram ops Matrix.PosDef.one
  have hr (X : Matrix I I ℂ) : KrausCompletion.krausAction ops X =
      U * KrausCompletion.krausAction L X * Uᴴ :=
    OutputSupport.krausAction_reconstruct ops Matrix.PosDef.one X
  rw [hr A, hr B, affinity_isometry U hU _ _
    (KrausCompletion.krausAction_posSemidef L hA)
    (KrausCompletion.krausAction_posSemidef L hB)]
  exact h

theorem affinity_cptp (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix J J ℂ)
    (hCP : CPTPKraus.CompletelyPositive Φ) (hTP : CPTPKraus.TracePreserving Φ)
    {A B : Matrix I I ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    affinity A B ≤ affinity (Φ A) (Φ B) := by
  let ops := CPTPKraus.canonicalKraus Φ
  have hgram : KrausCompletion.krausGram ops = 1 := CPTPKraus.canonicalKraus_gram Φ hCP hTP
  have haction (X : Matrix I I ℂ) : KrausCompletion.krausAction ops X = Φ X :=
    (CPTPKraus.canonicalKraus_reconstruct Φ hCP X).symm
  have h := affinity_kraus ops hgram hA hB
  simpa only [haction] using h

def partialTraceRight (R : Matrix (I × K) (I × K) ℂ) : Matrix I I ℂ :=
  fun i j => ∑ k, R (i, k) (j, k)

def partialTraceKraus (k : K) : Matrix I (I × K) ℂ :=
  fun i x => if x.2 = k then (1 : Matrix I I ℂ) i x.1 else 0

theorem partialTraceKraus_gram :
    KrausCompletion.krausGram (partialTraceKraus (I := I) (K := K)) = 1 := by
  ext ⟨i, k⟩ ⟨j, l⟩
  by_cases hij : i = j <;> by_cases hkl : k = l <;>
    simp [KrausCompletion.krausGram, Matrix.sum_apply, partialTraceKraus, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Matrix.one_apply, hij, hkl, Prod.ext_iff,
      mul_ite, ite_mul, eq_comm]

theorem partialTraceKraus_action (R : Matrix (I × K) (I × K) ℂ) :
    KrausCompletion.krausAction (partialTraceKraus (I := I) (K := K)) R =
      partialTraceRight R := by
  ext i j
  simp [KrausCompletion.krausAction, Matrix.sum_apply, partialTraceKraus, partialTraceRight,
    Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply,
    Fintype.sum_prod_type, mul_ite, ite_mul, apply_ite, eq_comm]

theorem affinity_partialTraceRight (A B : Matrix (I × K) (I × K) ℂ)
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    affinity A B ≤ affinity (partialTraceRight A) (partialTraceRight B) := by
  have h := affinity_kraus (partialTraceKraus (I := I) (K := K))
    partialTraceKraus_gram hA hB
  simpa only [partialTraceKraus_action] using h

end QuantumProver.MatrixAnalysis.Affinity

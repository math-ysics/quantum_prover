import QuantumProver.InformationTheory.AmplitudeDamping.SecretKey.OutputContinuity
import QuantumProver.InformationTheory.AmplitudeDamping.SecretKey.KeyEveIsometry

set_option autoImplicit false
set_option maxHeartbeats 600000

noncomputable section

open Matrix Kronecker
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace QuantumProver.AmplitudeDamping.SecretKey.KeyErrorConversion

open MatrixTraceNorm OutputContinuity KeyEveIsometry

def halfTraceDistance {I : Type*} [Fintype I] [DecidableEq I]
    (ρ σ : Density I) : ℝ := traceNorm (ρ.mat - σ.mat) / 2

theorem halfTraceDistance_isometry
    {I O : Type*} [Fintype I] [Fintype O] [DecidableEq I] [DecidableEq O]
    (V : Matrix O I ℂ) (hV : Vᴴ * V = 1) (ρ σ : Density I) :
    halfTraceDistance (isometryDensity V hV ρ) (isometryDensity V hV σ) =
      halfTraceDistance ρ σ := by
  unfold halfTraceDistance
  change traceNorm (V * ρ.mat * Vᴴ - V * σ.mat * Vᴴ) / 2 = _
  rw [← Matrix.sub_mul, ← Matrix.mul_sub, KeyEveIsometry.traceNorm_isometry V hV]

theorem one_sub_halfTraceDistance_le_rootFidelity
    {I : Type*} [Fintype I] [DecidableEq I] (ρ σ : Density I) :
    1 - halfTraceDistance ρ σ ≤ rootFidelity ρ σ := by
  have hPS := powers_stormer ρ.positive σ.positive
  rw [hsNorm_sqrt_sub_sq ρ.positive σ.positive] at hPS
  simp only [ρ.normalized, σ.normalized, Complex.one_re] at hPS
  have hTr := PurificationOrbit.re_trace_unitary_mul_le_traceNorm
    (CFC.sqrt ρ.mat * CFC.sqrt σ.mat) 1 (by simp)
  simp only [Matrix.one_mul] at hTr
  unfold halfTraceDistance rootFidelity
  linarith

section ActualKey

variable {d : ℕ} {E : Type*} [Fintype E] [DecidableEq E]

def bobAliceEveEquiv : (Fin d × (Fin d × E)) ≃ ((Fin d × Fin d) × E) where
  toFun x := ((x.2.1,x.1),x.2.2)
  invFun x := (x.1.2,(x.1.1,x.2))
  left_inv := by rintro ⟨b,a,e⟩; rfl
  right_inv := by rintro ⟨⟨a,b⟩,e⟩; rfl

def aliceKeyState (ρ : Density ((Fin d × Fin d) × E)) : Density (Fin d × E) :=
  (ρ.relabel (bobAliceEveEquiv (d := d) (E := E))).marginalRight

theorem aliceKeyState_apply (ρ : Density ((Fin d × Fin d) × E))
    (i i' : Fin d) (e e' : E) :
    (aliceKeyState ρ).mat (i,e) (i',e') =
      ∑ j : Fin d, ρ.mat ((i,j),e) ((i',j),e') := rfl

theorem aliceKeyState_offdiagonal (ρ : Density ((Fin d × Fin d) × E))
    (hρ : IsCCQ ρ) (i i' : Fin d) (e e' : E) (hii' : i ≠ i') :
    (aliceKeyState ρ).mat (i,e) (i',e') = 0 := by
  rw [aliceKeyState_apply]
  apply Finset.sum_eq_zero
  intro j hj
  exact hρ (i,j) (i',j) e e' (fun h => hii' (congrArg Prod.fst h))

def uniformAliceState (hd : 0 < d) : Density (Fin d) :=
  ((uniformKeyLaw d hd).copiedDensity).marginalRight

theorem uniformAliceState_apply (hd : 0 < d) (i i' : Fin d) :
    (uniformAliceState hd).mat i i' =
      if i = i' then (1 / (d : ℝ) : ℂ) else 0 := by
  by_cases h : i = i'
  · subst i'
    simp [uniformAliceState, Density.marginalRight, partialTraceLeft,
      ProbabilityLaw.copiedDensity, ProbabilityLaw.copiedMatrix, uniformKeyLaw]
  · simp [uniformAliceState, Density.marginalRight, partialTraceLeft,
      ProbabilityLaw.copiedDensity, ProbabilityLaw.copiedMatrix, uniformKeyLaw,
      Prod.mk.injEq, h]

def copyAliceEve (x : Fin d × E) : (Fin d × Fin d) × E := ((x.1,x.1),x.2)

def copyAliceEveMatrix : Matrix ((Fin d × Fin d) × E) (Fin d × E) ℂ :=
  PublicHistory.basisEmbedding_B copyAliceEve

theorem copyAliceEveMatrix_isometry :
    (copyAliceEveMatrix (d := d) (E := E))ᴴ *
      copyAliceEveMatrix (d := d) (E := E) = 1 :=
  PublicHistory.basisEmbedding_gram_B _ (fun _x _y h =>
    congrArg (fun z : (Fin d × Fin d) × E => (z.1.1,z.2)) h)

def correctedKeyState (ρ : Density ((Fin d × Fin d) × E)) :
    Density ((Fin d × Fin d) × E) :=
  isometryDensity (copyAliceEveMatrix (d := d) (E := E))
    (copyAliceEveMatrix_isometry (d := d) (E := E)) (aliceKeyState ρ)

theorem correctedKeyState_apply (ρ : Density ((Fin d × Fin d) × E))
    (i j i' j' : Fin d) (e e' : E) :
    (correctedKeyState ρ).mat ((i,j),e) ((i',j'),e') =
      if i = j ∧ i' = j' then (aliceKeyState ρ).mat (i,e) (i',e') else 0 := by
  change (((PublicHistory.basisEmbedding_B copyAliceEve * (aliceKeyState ρ).mat :
    Matrix ((Fin d × Fin d) × E) (Fin d × E) ℂ) *
    (PublicHistory.basisEmbedding_B (copyAliceEve (d := d) (E := E)))ᴴ) :
    Matrix ((Fin d × Fin d) × E) ((Fin d × Fin d) × E) ℂ) _ _ = _
  rw [PublicHistory.basisEmbedding_sandwich_apply_B copyAliceEve
    (fun x : (Fin d × Fin d) × E => (x.1.1,x.2)) (fun _ => rfl)]
  simp only [copyAliceEve, Prod.mk.injEq, true_and, and_true]

theorem correctedKeyState_matrix (ρ : Density ((Fin d × Fin d) × E))
    (hρ : IsCCQ ρ) :
    (correctedKeyState ρ).mat = keyBlockDiagonal (fun k : Fin d × Fin d =>
      if k.1 = k.2 then ∑ j : Fin d, classicalKeyBlock ρ (k.1,j) else 0) := by
  ext x y
  rcases x with ⟨⟨i,j⟩,e⟩
  rcases y with ⟨⟨i',j'⟩,e'⟩
  rw [correctedKeyState_apply, keyBlockDiagonal_apply]
  by_cases hxy : (i,j) = (i',j')
  · obtain ⟨hi,hj⟩ := Prod.mk.inj hxy
    subst i'
    subst j'
    by_cases hij : i = j
    · simp only [hij, and_self, ite_true, aliceKeyState_apply,
        Matrix.sum_apply, classicalKeyBlock, Matrix.submatrix_apply]
    · simp [hij]
  · rw [ite_eq_right hxy]
    by_cases hij : i = j
    · by_cases hi'j' : i' = j'
      · have hii' : i ≠ i' := by
          intro hi
          apply hxy
          exact Prod.ext hi (hij.symm.trans (hi.trans hi'j'))
        rw [ite_eq_left ⟨hij,hi'j'⟩, aliceKeyState_offdiagonal ρ hρ i i' e e' hii']
      · simp [hi'j']
    · simp [hij]

def aliceSecrecyError (hd : 0 < d) (ρ : Density ((Fin d × Fin d) × E)) : ℝ :=
  halfTraceDistance (aliceKeyState ρ) ((uniformAliceState hd).tensor ρ.marginalRight)

def disagreementError (ρ : Density ((Fin d × Fin d) × E)) : ℝ :=
  ∑ k : Fin d × Fin d, if k.1 = k.2 then 0 else (classicalKeyBlock ρ k).trace.re

private def offRowBlock (ρ : Density ((Fin d × Fin d) × E)) (i : Fin d) :
    Matrix E E ℂ := ∑ j : Fin d, if i = j then 0 else classicalKeyBlock ρ (i,j)

omit [DecidableEq E] in
private theorem offRowBlock_posSemidef
    (ρ : Density ((Fin d × Fin d) × E)) (i : Fin d) :
    (offRowBlock ρ i).PosSemidef := by
  apply Matrix.posSemidef_sum
  intro j hj
  by_cases hij : i = j
  · simpa only [ite_eq_left hij] using (Matrix.PosSemidef.zero : (0 : Matrix E E ℂ).PosSemidef)
  · simpa only [ite_eq_right hij] using classicalKeyBlock_posSemidef ρ (i,j)

omit [DecidableEq E] in
private theorem keyRow_split (ρ : Density ((Fin d × Fin d) × E)) (i : Fin d) :
    (∑ j : Fin d, classicalKeyBlock ρ (i,j)) = classicalKeyBlock ρ (i,i) + offRowBlock ρ i := by
  calc
    _ = ∑ j : Fin d, ((if i = j then classicalKeyBlock ρ (i,i) else 0) +
        (if i = j then 0 else classicalKeyBlock ρ (i,j))) := by
      apply Finset.sum_congr rfl
      intro j hj
      by_cases hij : i = j
      · subst j; simp
      · simp [hij]
    _ = _ := by rw [Finset.sum_add_distrib]; simp [offRowBlock]

omit [DecidableEq E] in
private theorem offRowBlock_trace (ρ : Density ((Fin d × Fin d) × E)) (i : Fin d) :
    (offRowBlock ρ i).trace.re =
      ∑ j : Fin d, if i = j then 0 else (classicalKeyBlock ρ (i,j)).trace.re := by
  rw [offRowBlock, Matrix.trace_sum, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hij : i = j <;> simp [hij]

omit [DecidableEq E] in
private theorem sum_offRowBlock_trace (ρ : Density ((Fin d × Fin d) × E)) :
    (∑ i : Fin d, (offRowBlock ρ i).trace.re) = disagreementError ρ := by
  simp only [disagreementError, Fintype.sum_prod_type, offRowBlock_trace]

omit [Fintype E] [DecidableEq E] in
private theorem keyBlockDiagonal_sub
    {K : Type*} [Fintype K] [DecidableEq K] (M N : K → Matrix E E ℂ) :
    keyBlockDiagonal M - keyBlockDiagonal N = keyBlockDiagonal (fun k => M k - N k) := by
  ext x y
  simp only [Matrix.sub_apply, keyBlockDiagonal_apply]
  by_cases h : x.1 = y.1 <;> simp [h]

private theorem correction_difference_matrix (ρ : Density ((Fin d × Fin d) × E))
    (hρ : IsCCQ ρ) :
    ρ.mat - (correctedKeyState ρ).mat = keyBlockDiagonal (fun k : Fin d × Fin d =>
      if k.1 = k.2 then -offRowBlock ρ k.1 else classicalKeyBlock ρ k) := by
  rw [isCCQ_matrix_eq_keyBlockDiagonal ρ hρ, correctedKeyState_matrix ρ hρ,
    keyBlockDiagonal_sub]
  apply congrArg keyBlockDiagonal
  funext k
  rcases k with ⟨i,j⟩
  by_cases hij : i = j
  · subst j
    simp only [ite_true]
    rw [keyRow_split]
    abel
  · simp [hij]

theorem correctedKeyState_distance (ρ : Density ((Fin d × Fin d) × E))
    (hρ : IsCCQ ρ) : halfTraceDistance ρ (correctedKeyState ρ) = disagreementError ρ := by
  unfold halfTraceDistance
  rw [correction_difference_matrix ρ hρ, traceNorm_keyBlockDiagonal]
  have hvalue (k : Fin d × Fin d) :
      traceNorm (if k.1 = k.2 then -offRowBlock ρ k.1 else classicalKeyBlock ρ k) =
        if k.1 = k.2 then (offRowBlock ρ k.1).trace.re else (classicalKeyBlock ρ k).trace.re := by
    by_cases hk : k.1 = k.2
    · rw [ite_eq_left hk, ite_eq_left hk, traceNorm_neg,
        traceNorm_of_posSemidef _ (offRowBlock_posSemidef ρ k.1)]
    · rw [ite_eq_right hk, ite_eq_right hk,
        traceNorm_of_posSemidef _ (classicalKeyBlock_posSemidef ρ k)]
  simp_rw [hvalue]
  have hsum : (∑ k : Fin d × Fin d,
      if k.1 = k.2 then (offRowBlock ρ k.1).trace.re else (classicalKeyBlock ρ k).trace.re) =
      2 * disagreementError ρ := by
    calc
      _ = (∑ k : Fin d × Fin d, if k.1 = k.2 then (offRowBlock ρ k.1).trace.re else 0) +
          ∑ k : Fin d × Fin d, if k.1 = k.2 then 0 else (classicalKeyBlock ρ k).trace.re := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro k hk
        by_cases h : k.1 = k.2 <;> simp [h]
      _ = (∑ i : Fin d, (offRowBlock ρ i).trace.re) + disagreementError ρ := by
        simp only [disagreementError, Fintype.sum_prod_type]
        simp
      _ = _ := by rw [sum_offRowBlock_trace]; ring
  rw [hsum]
  ring

theorem copy_uniformAliceState (hd : 0 < d) (ξ : Density E) :
    (((copyAliceEveMatrix * ((uniformAliceState hd).tensor ξ).mat :
      Matrix ((Fin d × Fin d) × E) (Fin d × E) ℂ) *
      (copyAliceEveMatrix (d := d) (E := E))ᴴ) :
      Matrix ((Fin d × Fin d) × E) ((Fin d × Fin d) × E) ℂ) =
      (idealKeyStateAgainst d hd ξ).mat := by
  ext x y
  rcases x with ⟨⟨i,j⟩,e⟩
  rcases y with ⟨⟨i',j'⟩,e'⟩
  change (((PublicHistory.basisEmbedding_B copyAliceEve * ((uniformAliceState hd).tensor ξ).mat :
    Matrix ((Fin d × Fin d) × E) (Fin d × E) ℂ) *
    (PublicHistory.basisEmbedding_B (copyAliceEve (d := d) (E := E)))ᴴ) :
    Matrix ((Fin d × Fin d) × E) ((Fin d × Fin d) × E) ℂ) _ _ = _
  erw [PublicHistory.basisEmbedding_sandwich_apply_B copyAliceEve
    (fun x : (Fin d × Fin d) × E => (x.1.1,x.2)) (fun _ => rfl)]
  change (if copyAliceEve (i,e) = ((i,j),e) ∧ copyAliceEve (i',e') = ((i',j'),e') then
    (uniformAliceState hd).mat i i' * ξ.mat e e' else 0) =
    ((uniformKeyLaw d hd).copiedMatrix ⊗ₖ ξ.mat) ((i,j),e) ((i',j'),e')
  rw [uniformAliceState_apply]
  by_cases hij : i = j <;> by_cases hi'j' : i' = j' <;> by_cases hii' : i = i' <;>
    simp [copyAliceEve, Matrix.kroneckerMap_apply, ProbabilityLaw.copiedMatrix,
      uniformKeyLaw, Matrix.diagonal_apply, Prod.mk.injEq, hij, hi'j', hii'] <;> aesop

theorem correctedKeyState_ideal_distance (hd : 0 < d)
    (ρ : Density ((Fin d × Fin d) × E)) :
    halfTraceDistance (correctedKeyState ρ) (idealKeyStateAgainst d hd ρ.marginalRight) =
      aliceSecrecyError hd ρ := by
  have hIdeal : idealKeyStateAgainst d hd ρ.marginalRight =
      isometryDensity copyAliceEveMatrix copyAliceEveMatrix_isometry
        ((uniformAliceState hd).tensor ρ.marginalRight) :=
    Density.eq_of_mat_eq (copy_uniformAliceState hd ρ.marginalRight).symm
  unfold aliceSecrecyError
  rw [hIdeal]
  exact halfTraceDistance_isometry _ copyAliceEveMatrix_isometry _ _

theorem correctedKeyState_preserves_wholeEve (ρ : Density ((Fin d × Fin d) × E)) :
    (correctedKeyState ρ).marginalRight = ρ.marginalRight := by
  apply Density.eq_of_mat_eq
  ext e e'
  change (∑ k : Fin d × Fin d, (correctedKeyState ρ).mat (k,e) (k,e')) =
    ∑ k : Fin d × Fin d, ρ.mat (k,e) (k,e')
  simp only [Fintype.sum_prod_type, correctedKeyState_apply, and_self]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true, aliceKeyState_apply]

theorem physicalKey_ideal_distance_le_error (hd : 0 < d)
    (ρ : Density ((Fin d × Fin d) × E)) (hρ : IsCCQ ρ) :
    halfTraceDistance ρ (idealKeyStateAgainst d hd ρ.marginalRight) ≤
      disagreementError ρ + aliceSecrecyError hd ρ := by
  have h := traceNorm_add_le (ρ.mat - (correctedKeyState ρ).mat)
    ((correctedKeyState ρ).mat - (idealKeyStateAgainst d hd ρ.marginalRight).mat)
  rw [sub_add_sub_cancel] at h
  have hc := correctedKeyState_distance ρ hρ
  have hs := correctedKeyState_ideal_distance hd ρ
  unfold halfTraceDistance at hc hs ⊢
  linarith

theorem positivePart_error_sq_le_keyG (hd : 0 < d)
    (ρ : Density ((Fin d × Fin d) × E)) (hρ : IsCCQ ρ) :
    (max 0 (1 - disagreementError ρ - aliceSecrecyError hd ρ)) ^ 2 ≤
      optimalWholeKeySquaredFidelity d hd ρ := by
  have hD := physicalKey_ideal_distance_le_error hd ρ hρ
  have hF := one_sub_halfTraceDistance_le_rootFidelity ρ
    (idealKeyStateAgainst d hd ρ.marginalRight)
  have hF0 := rootFidelity_nonneg ρ (idealKeyStateAgainst d hd ρ.marginalRight)
  have hm : max 0 (1 - disagreementError ρ - aliceSecrecyError hd ρ) ≤
      rootFidelity ρ (idealKeyStateAgainst d hd ρ.marginalRight) := by
    apply max_le hF0
    linarith
  have hs : (max 0 (1 - disagreementError ρ - aliceSecrecyError hd ρ)) ^ 2 ≤
      squaredFidelity ρ (idealKeyStateAgainst d hd ρ.marginalRight) := by
    unfold squaredFidelity
    nlinarith [le_max_left (0 : ℝ) (1 - disagreementError ρ - aliceSecrecyError hd ρ)]
  exact hs.trans (squaredFidelity_candidate_le_keyG d hd ρ ρ.marginalRight)

theorem error_ge_one_sub_sqrt_keyG (hd : 0 < d)
    (ρ : Density ((Fin d × Fin d) × E)) (hρ : IsCCQ ρ) :
    1 - Real.sqrt (optimalWholeKeySquaredFidelity d hd ρ) ≤
      disagreementError ρ + aliceSecrecyError hd ρ := by
  have hD := physicalKey_ideal_distance_le_error hd ρ hρ
  have hF := one_sub_halfTraceDistance_le_rootFidelity ρ
    (idealKeyStateAgainst d hd ρ.marginalRight)
  have hF0 := rootFidelity_nonneg ρ (idealKeyStateAgainst d hd ρ.marginalRight)
  have hG0 := (optimalWholeKeySquaredFidelity_mem_Icc d hd ρ).1
  have hc := squaredFidelity_candidate_le_keyG d hd ρ ρ.marginalRight
  have hsq := Real.sq_sqrt hG0
  have hs0 := Real.sqrt_nonneg (optimalWholeKeySquaredFidelity d hd ρ)
  unfold squaredFidelity at hc
  have hroot : rootFidelity ρ (idealKeyStateAgainst d hd ρ.marginalRight) ≤
      Real.sqrt (optimalWholeKeySquaredFidelity d hd ρ) := by nlinarith
  linarith

end ActualKey

section WholeEveRelabel

variable {I J E F : Type*} [Fintype I] [Fintype J] [Fintype E] [Fintype F]
  [DecidableEq I] [DecidableEq J] [DecidableEq E] [DecidableEq F]

theorem halfTraceDistance_relabel (e : J ≃ I) (ρ σ : Density I) :
    halfTraceDistance (ρ.relabel e) (σ.relabel e) = halfTraceDistance ρ σ := by
  unfold halfTraceDistance
  change traceNorm ((ρ.mat - σ.mat).submatrix e e) / 2 = _
  rw [traceNorm_submatrix_equiv]

theorem isCCQ_Eve_relabel {d : ℕ} (e : F ≃ E)
    (ρ : Density ((Fin d × Fin d) × E)) (hρ : IsCCQ ρ) :
    IsCCQ (ρ.relabel ((Equiv.refl (Fin d × Fin d)).prodCongr e)) := by
  intro k k' f f' hkk'
  exact hρ k k' (e f) (e f') hkk'

theorem aliceKeyState_Eve_relabel {d : ℕ} (e : F ≃ E)
    (ρ : Density ((Fin d × Fin d) × E)) :
    aliceKeyState (ρ.relabel ((Equiv.refl (Fin d × Fin d)).prodCongr e)) =
      (aliceKeyState ρ).relabel ((Equiv.refl (Fin d)).prodCongr e) := by
  apply Density.eq_of_mat_eq
  rfl

theorem wholeEveMarginal_Eve_relabel {d : ℕ} (e : F ≃ E)
    (ρ : Density ((Fin d × Fin d) × E)) :
    (ρ.relabel ((Equiv.refl (Fin d × Fin d)).prodCongr e)).marginalRight =
      ρ.marginalRight.relabel e := by
  apply Density.eq_of_mat_eq
  rfl

theorem uniformAlice_tensor_Eve_relabel {d : ℕ} (hd : 0 < d) (e : F ≃ E)
    (ξ : Density E) :
    (uniformAliceState hd).tensor (ξ.relabel e) =
      ((uniformAliceState hd).tensor ξ).relabel ((Equiv.refl (Fin d)).prodCongr e) := by
  apply Density.eq_of_mat_eq
  rfl

theorem disagreementError_Eve_relabel {d : ℕ} (e : F ≃ E)
    (ρ : Density ((Fin d × Fin d) × E)) :
    disagreementError (ρ.relabel ((Equiv.refl (Fin d × Fin d)).prodCongr e)) =
      disagreementError ρ := by
  unfold disagreementError
  apply Finset.sum_congr rfl
  intro k hk
  have hBlock :
      classicalKeyBlock (ρ.relabel ((Equiv.refl (Fin d × Fin d)).prodCongr e)) k =
        (classicalKeyBlock ρ k).submatrix e e := rfl
  rw [hBlock, trace_submatrix_equiv]

theorem aliceSecrecyError_Eve_relabel {d : ℕ} (hd : 0 < d) (e : F ≃ E)
    (ρ : Density ((Fin d × Fin d) × E)) :
    aliceSecrecyError hd (ρ.relabel ((Equiv.refl (Fin d × Fin d)).prodCongr e)) =
      aliceSecrecyError hd ρ := by
  unfold aliceSecrecyError
  rw [aliceKeyState_Eve_relabel, wholeEveMarginal_Eve_relabel,
    uniformAlice_tensor_Eve_relabel, halfTraceDistance_relabel]

end WholeEveRelabel

end QuantumProver.AmplitudeDamping.SecretKey.KeyErrorConversion

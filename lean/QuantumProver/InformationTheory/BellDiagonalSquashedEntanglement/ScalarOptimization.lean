import QuantumProver.InformationTheory.BellDiagonalSquashedEntanglement.RecoveryInequalities

set_option autoImplicit false

noncomputable section

open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder Matrix
  Matrix.Norms.L2Operator

namespace QuantumProver.BellDiagonalSquashedEntanglement.Geometry

variable {I O J : Type*} [Fintype I] [Fintype O] [Fintype J]
  [DecidableEq I] [DecidableEq O] [DecidableEq J]

def krausDilation (K : J → Matrix O I ℂ) : Matrix (O × J) I ℂ :=
  fun oj i => K oj.2 oj.1 i

theorem krausDilation_gram (K : J → Matrix O I ℂ) :
    (krausDilation K)ᴴ * krausDilation K = ∑ j : J, (K j)ᴴ * K j := by
  ext i k
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, krausDilation,
    Fintype.sum_prod_type, Matrix.sum_apply]
  exact Finset.sum_comm

theorem krausDilation_isometry (K : J → Matrix O I ℂ)
    (hK : ∑ j : J, (K j)ᴴ * K j = 1) :
    (krausDilation K)ᴴ * krausDilation K = 1 :=
  (krausDilation_gram K).trans hK

def krausAction (K : J → Matrix O I ℂ) (A : Matrix I I ℂ) : Matrix O O ℂ :=
  ∑ j : J, K j * A * (K j)ᴴ

theorem trace_krausAction (K : J → Matrix O I ℂ) (A : Matrix I I ℂ) :
    (krausAction K A).trace = ((∑ j : J, (K j)ᴴ * K j) * A).trace := by
  calc
    (krausAction K A).trace = ∑ j : J, (K j * A * (K j)ᴴ).trace := by
      rw [krausAction, Matrix.trace_sum]
    _ = ∑ j : J, ((K j)ᴴ * K j * A).trace := by
      apply Finset.sum_congr rfl
      intro j hj
      exact Matrix.trace_mul_cycle (K j) A (K j)ᴴ
    _ = ((∑ j : J, (K j)ᴴ * K j) * A).trace := by
      rw [Finset.sum_mul, Matrix.trace_sum]

theorem traceRight_krausDilation (K : J → Matrix O I ℂ)
    (A : Matrix I I ℂ) :
    traceRight (krausDilation K * A * (krausDilation K)ᴴ) =
      ∑ j : J, K j * A * (K j)ᴴ := by
  ext o p
  simp [traceRight, krausDilation, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.sum_apply]

theorem krausDilation_posSemidef (K : J → Matrix O I ℂ)
    {A : Matrix I I ℂ} (hA : A.PosSemidef) :
    (krausDilation K * A * (krausDilation K)ᴴ).PosSemidef :=
  hA.mul_mul_conjTranspose_same (krausDilation K)

theorem krausDilation_trace (K : J → Matrix O I ℂ)
    (hK : ∑ j : J, (K j)ᴴ * K j = 1) (A : Matrix I I ℂ) :
    (krausDilation K * A * (krausDilation K)ᴴ).trace = A.trace := by
  rw [Matrix.trace_mul_cycle, krausDilation_isometry K hK, Matrix.one_mul]

theorem krausDilation_isDensity (K : J → Matrix O I ℂ)
    (hK : ∑ j : J, (K j)ᴴ * K j = 1)
    (A : Matrix I I ℂ) (hA : A.PosSemidef) (htrace : A.trace = 1) :
    (krausDilation K * A * (krausDilation K)ᴴ).PosSemidef ∧
      (krausDilation K * A * (krausDilation K)ᴴ).trace = 1 ∧
      traceRight (krausDilation K * A * (krausDilation K)ᴴ) =
        ∑ j : J, K j * A * (K j)ᴴ := by
  exact ⟨krausDilation_posSemidef K hA,
    (krausDilation_trace K hK A).trans htrace, traceRight_krausDilation K A⟩

def pureRepairKraus (Q : Matrix I I ℂ) (o₀ : O) : I → Matrix O I ℂ :=
  fun q o i => if o = o₀ then CFC.sqrt Q q i else 0

theorem pureRepairKraus_factorGram (Q : Matrix I I ℂ) (o₀ : O) :
    (∑ q : I, (pureRepairKraus Q o₀ q)ᴴ * pureRepairKraus Q o₀ q) =
      (CFC.sqrt Q)ᴴ * CFC.sqrt Q := by
  ext i j
  simp [pureRepairKraus, Matrix.sum_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, apply_ite, mul_ite, ite_mul]

theorem pureRepairKraus_gram (Q : Matrix I I ℂ) (hQ : Q.PosSemidef)
    (o₀ : O) :
    (∑ q : I, (pureRepairKraus Q o₀ q)ᴴ * pureRepairKraus Q o₀ q) = Q := by
  have hsqrt : (CFC.sqrt Q).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg Q)
  have hs : (CFC.sqrt Q)ᴴ = CFC.sqrt Q := hsqrt.isHermitian.eq
  rw [pureRepairKraus_factorGram, hs]
  exact CFC.sqrt_mul_sqrt_self Q hQ.nonneg

theorem pureRepairKraus_action (Q : Matrix I I ℂ) (hQ : Q.PosSemidef)
    (o₀ : O) (A : Matrix I I ℂ) :
    krausAction (pureRepairKraus Q o₀) A = Matrix.single o₀ o₀ ((Q * A).trace) := by
  have hs : krausAction (pureRepairKraus Q o₀) A =
      Matrix.single o₀ o₀ (krausAction (pureRepairKraus Q o₀) A o₀ o₀) := by
    ext o p
    by_cases ho : o = o₀ <;> by_cases hp : p = o₀
    · subst o
      subst p
      simp
    · simp [krausAction, pureRepairKraus, Matrix.mul_apply,
        Matrix.conjTranspose_apply, Matrix.sum_apply, Matrix.single_apply, ho, hp,
        Ne.symm hp]
    · simp [krausAction, pureRepairKraus, Matrix.mul_apply,
        Matrix.conjTranspose_apply, Matrix.sum_apply, Matrix.single_apply, ho, hp,
        Ne.symm ho]
    · simp [krausAction, pureRepairKraus, Matrix.mul_apply,
        Matrix.conjTranspose_apply, Matrix.sum_apply, Matrix.single_apply, ho, hp,
        Ne.symm ho, Ne.symm hp]
  have ht := trace_krausAction (pureRepairKraus Q o₀) A
  rw [pureRepairKraus_gram Q hQ o₀, hs, Matrix.trace_single_eq_same] at ht
  rw [hs, ht]

def completedKraus (K : J → Matrix O I ℂ) (Q : Matrix I I ℂ) (o₀ : O) :
    J ⊕ I → Matrix O I ℂ :=
  Sum.elim K (pureRepairKraus Q o₀)

theorem completedKraus_gram (K : J → Matrix O I ℂ)
    (Q : Matrix I I ℂ) (hQ : Q.PosSemidef) (o₀ : O)
    (hK : ∑ j : J, (K j)ᴴ * K j = 1 - Q) :
    (∑ q : J ⊕ I, (completedKraus K Q o₀ q)ᴴ *
      completedKraus K Q o₀ q) = 1 := by
  simp only [Fintype.sum_sum_type, completedKraus, Sum.elim_inl, Sum.elim_inr]
  rw [hK, pureRepairKraus_gram Q hQ o₀]
  exact sub_add_cancel 1 Q

theorem completedKraus_action (K : J → Matrix O I ℂ)
    (Q : Matrix I I ℂ) (hQ : Q.PosSemidef) (o₀ : O) (A : Matrix I I ℂ) :
    krausAction (completedKraus K Q o₀) A =
      krausAction K A + Matrix.single o₀ o₀ ((Q * A).trace) := by
  unfold krausAction
  rw [Fintype.sum_sum_type]
  simp only [completedKraus, Sum.elim_inl, Sum.elim_inr]
  change krausAction K A + krausAction (pureRepairKraus Q o₀) A = _
  rw [pureRepairKraus_action Q hQ o₀ A]
  rfl

theorem completedKraus_on_supported (K : J → Matrix O I ℂ)
    (P : Matrix I I ℂ) (hQ : (1 - P).PosSemidef) (o₀ : O)
    (A : Matrix I I ℂ) (hPA : P * A = A) :
    krausAction (completedKraus K (1 - P) o₀) A = krausAction K A := by
  rw [completedKraus_action K (1 - P) hQ o₀ A]
  have hz : (1 - P) * A = 0 := by
    rw [Matrix.sub_mul, Matrix.one_mul, hPA, sub_self]
  simp [hz]

theorem completedKraus_dilation_isDensity
    (K : J → Matrix O I ℂ) (Q : Matrix I I ℂ) (hQ : Q.PosSemidef)
    (o₀ : O) (hK : ∑ j : J, (K j)ᴴ * K j = 1 - Q)
    (A : Matrix I I ℂ) (hA : A.PosSemidef) (htrace : A.trace = 1) :
    (krausDilation (completedKraus K Q o₀) * A *
      (krausDilation (completedKraus K Q o₀))ᴴ).PosSemidef ∧
      (krausDilation (completedKraus K Q o₀) * A *
        (krausDilation (completedKraus K Q o₀))ᴴ).trace = 1 ∧
      traceRight (krausDilation (completedKraus K Q o₀) * A *
        (krausDilation (completedKraus K Q o₀))ᴴ) =
        ∑ q : J ⊕ I, completedKraus K Q o₀ q * A *
          (completedKraus K Q o₀ q)ᴴ := by
  exact krausDilation_isDensity _
    (completedKraus_gram K Q hQ o₀ hK) A hA htrace

theorem complement_posSemidef (P : Matrix I I ℂ)
    (hHerm : Pᴴ = P) (hIdem : P * P = P) :
    (1 - P).PosSemidef := by
  have hComp : (1 - P)ᴴ = 1 - P := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hHerm]
  have hSquare : (1 - P) * (1 - P) = 1 - P := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one,
      hIdem, sub_self, sub_zero]
  have h := Matrix.posSemidef_self_mul_conjTranspose (1 - P)
  rwa [hComp, hSquare] at h

theorem unit_overlap_lipschitz
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (u u' v : H) (hv : ‖v‖ = 1) :
    |‖inner ℂ u v‖ - ‖inner ℂ u' v‖| ≤ ‖u - u'‖ := by
  calc
    |‖inner ℂ u v‖ - ‖inner ℂ u' v‖| ≤
        ‖inner ℂ u v - inner ℂ u' v‖ := abs_norm_sub_norm_le _ _
    _ = ‖inner ℂ (u - u') v‖ := by rw [inner_sub_left]
    _ ≤ ‖u - u'‖ * ‖v‖ := norm_inner_le_norm _ _
    _ = ‖u - u'‖ := by rw [hv, mul_one]

theorem unit_norm_sub_sq
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    ‖u - v‖ ^ 2 = 2 - 2 * (inner ℂ u v).re := by
  have h := norm_sub_sq (𝕜 := ℂ) u v
  rw [hu, hv] at h
  norm_num at h
  linarith

theorem two_unit_overlap_difference_le
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (u₀ u₁ v₀ v₁ : H) (hu₁ : ‖u₁‖ = 1) (hv₀ : ‖v₀‖ = 1) :
    |‖inner ℂ u₀ u₁‖ - ‖inner ℂ v₀ v₁‖| ≤ ‖u₀ - v₀‖ + ‖u₁ - v₁‖ := by
  have h₀ := unit_overlap_lipschitz u₀ v₀ u₁ hu₁
  have h₁ : |‖inner ℂ v₀ u₁‖ - ‖inner ℂ v₀ v₁‖| ≤ ‖u₁ - v₁‖ := by
    simpa only [norm_inner_symm] using unit_overlap_lipschitz u₁ v₁ v₀ hv₀
  exact (abs_sub_le ‖inner ℂ u₀ u₁‖ ‖inner ℂ v₀ u₁‖
    ‖inner ℂ v₀ v₁‖).trans (add_le_add h₀ h₁)

theorem exists_isometry_comp_eq_of_norm_eq
    {W H : Type*} [AddCommGroup W] [Module ℂ W]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    (A B : W →ₗ[ℂ] H) (hNorm : ∀ x : W, ‖A x‖ = ‖B x‖) :
    ∃ U : H →ₗᵢ[ℂ] H, ∀ x : W, U (A x) = B x := by
  have hker : A.ker ≤ B.ker := by
    intro x hx
    change A x = 0 at hx
    change B x = 0
    apply norm_eq_zero.mp
    rw [← hNorm, hx, norm_zero]
  let f : A.range →ₗ[ℂ] H :=
    (A.ker.liftQ B hker).comp A.quotKerEquivRange.symm.toLinearMap
  have hf : ∀ x : W, f ⟨A x, LinearMap.mem_range_self A x⟩ = B x := by
    intro x
    simp only [f, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
      LinearMap.quotKerEquivRange_symm_apply_image, Submodule.mkQ_apply,
      Submodule.liftQ_apply]
  have hfnorm : ∀ v : A.range, ‖f v‖ = ‖v‖ := by
    intro v
    obtain ⟨x, hx⟩ := v.property
    have hv : v = ⟨A x, LinearMap.mem_range_self A x⟩ := Subtype.ext hx.symm
    rw [hv, hf]
    exact (hNorm x).symm
  let L : A.range →ₗᵢ[ℂ] H := ⟨f, hfnorm⟩
  refine ⟨L.extend, ?_⟩
  intro x
  have h := LinearIsometry.extend_apply L ⟨A x, LinearMap.mem_range_self A x⟩
  exact h.trans (hf x)

theorem inner_toEuclideanLin_self (M : Matrix O I ℂ)
    (x : EuclideanSpace ℂ I) :
    inner ℂ (Matrix.toEuclideanLin M x) (Matrix.toEuclideanLin M x) =
      star (WithLp.ofLp x) ⬝ᵥ (Mᴴ * M) *ᵥ WithLp.ofLp x := by
  simp only [Matrix.toLpLin_apply, EuclideanSpace.inner_toLp_toLp]
  rw [dotProduct_comm, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec,
    Matrix.mulVec_mulVec]

theorem norm_toEuclideanLin_eq_of_gram_eq
    (A B : Matrix O I ℂ) (hGram : Aᴴ * A = Bᴴ * B)
    (x : EuclideanSpace ℂ I) :
    ‖Matrix.toEuclideanLin A x‖ = ‖Matrix.toEuclideanLin B x‖ := by
  have hinner : inner ℂ (Matrix.toEuclideanLin A x) (Matrix.toEuclideanLin A x) =
      inner ℂ (Matrix.toEuclideanLin B x) (Matrix.toEuclideanLin B x) := by
    rw [inner_toEuclideanLin_self, inner_toEuclideanLin_self, hGram]
  have hsq : ‖Matrix.toEuclideanLin A x‖ ^ 2 =
      ‖Matrix.toEuclideanLin B x‖ ^ 2 := by
    calc
      _ = (inner ℂ (Matrix.toEuclideanLin A x) (Matrix.toEuclideanLin A x)).re :=
        norm_sq_eq_re_inner (𝕜 := ℂ) _
      _ = (inner ℂ (Matrix.toEuclideanLin B x) (Matrix.toEuclideanLin B x)).re :=
        congrArg Complex.re hinner
      _ = _ := (norm_sq_eq_re_inner (𝕜 := ℂ) _).symm
  nlinarith [norm_nonneg (Matrix.toEuclideanLin A x),
    norm_nonneg (Matrix.toEuclideanLin B x)]

theorem exists_unitary_mul_of_gram_eq (A B : Matrix O I ℂ)
    (hGram : Aᴴ * A = Bᴴ * B) :
    ∃ U : Matrix O O ℂ, U ∈ Matrix.unitaryGroup O ℂ ∧ B = U * A := by
  obtain ⟨L, hL⟩ := exists_isometry_comp_eq_of_norm_eq
    (Matrix.toEuclideanLin A) (Matrix.toEuclideanLin B)
    (norm_toEuclideanLin_eq_of_gram_eq A B hGram)
  have hsurj : Function.Surjective L :=
    LinearMap.surjective_of_injective (f := L.toLinearMap) L.injective
  let e := LinearIsometryEquiv.ofSurjective L hsurj
  let U : Matrix O O ℂ := Matrix.toEuclideanLin.symm L.toLinearMap
  have hU : U ∈ Matrix.unitaryGroup O ℂ := by
    change e.toMatrix (EuclideanSpace.basisFun O ℂ).toBasis
      (EuclideanSpace.basisFun O ℂ).toBasis ∈ Matrix.unitaryGroup O ℂ
    exact e.toMatrix_mem_unitaryGroup _ _
  refine ⟨U, hU, ?_⟩
  apply Matrix.toEuclideanLin.injective
  apply LinearMap.ext
  intro x
  simpa only [U, Matrix.toLpLin_mul_same, LinearMap.comp_apply,
    LinearEquiv.apply_symm_apply, LinearIsometry.coe_toLinearMap] using (hL x).symm

theorem exists_polar_isometry (M : Matrix I I ℂ) :
    ∃ U : EuclideanSpace ℂ I →ₗᵢ[ℂ] EuclideanSpace ℂ I,
      ∀ x : EuclideanSpace ℂ I,
        U (Matrix.toEuclideanLin (CFC.sqrt (Mᴴ * M)) x) =
          Matrix.toEuclideanLin M x := by
  have hG : (Mᴴ * M).PosSemidef := Matrix.posSemidef_conjTranspose_mul_self M
  have hS : (CFC.sqrt (Mᴴ * M)).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg _)
  have hGram : (CFC.sqrt (Mᴴ * M))ᴴ * CFC.sqrt (Mᴴ * M) = Mᴴ * M := by
    rw [hS.isHermitian.eq]
    exact CFC.sqrt_mul_sqrt_self _ hG.nonneg
  exact exists_isometry_comp_eq_of_norm_eq
    (Matrix.toEuclideanLin (CFC.sqrt (Mᴴ * M))) (Matrix.toEuclideanLin M)
    (norm_toEuclideanLin_eq_of_gram_eq _ _ hGram)

theorem exists_polar_unitary (M : Matrix I I ℂ) :
    ∃ U : Matrix I I ℂ, U ∈ Matrix.unitaryGroup I ℂ ∧
      M = U * CFC.sqrt (Mᴴ * M) := by
  obtain ⟨L, hL⟩ := exists_polar_isometry M
  have hsurj : Function.Surjective L :=
    LinearMap.surjective_of_injective (f := L.toLinearMap) L.injective
  let e := LinearIsometryEquiv.ofSurjective L hsurj
  let U : Matrix I I ℂ := Matrix.toEuclideanLin.symm L.toLinearMap
  have hU : U ∈ Matrix.unitaryGroup I ℂ := by
    change e.toMatrix (EuclideanSpace.basisFun I ℂ).toBasis
      (EuclideanSpace.basisFun I ℂ).toBasis ∈ Matrix.unitaryGroup I ℂ
    exact e.toMatrix_mem_unitaryGroup _ _
  refine ⟨U, hU, ?_⟩
  apply Matrix.toEuclideanLin.injective
  apply LinearMap.ext
  intro x
  simpa only [U, Matrix.toLpLin_mul_same, LinearMap.comp_apply,
    LinearEquiv.apply_symm_apply, LinearIsometry.coe_toLinearMap] using (hL x).symm

theorem exists_unitary_trace_alignment (M : Matrix I I ℂ) :
    ∃ U : Matrix I I ℂ, U ∈ Matrix.unitaryGroup I ℂ ∧
      (Uᴴ * M).trace = (CFC.sqrt (Mᴴ * M)).trace := by
  obtain ⟨U, hU, hM⟩ := exists_polar_unitary M
  refine ⟨U, hU, ?_⟩
  have hGram : Uᴴ * U = 1 := (Matrix.mem_unitaryGroup_iff').mp hU
  calc
    _ = (Uᴴ * (U * CFC.sqrt (Mᴴ * M))).trace :=
      congrArg (fun X : Matrix I I ℂ => (Uᴴ * X).trace) hM
    _ = _ := by rw [← Matrix.mul_assoc, hGram, Matrix.one_mul]

theorem norm_unitary_entry_le_one (V : Matrix I I ℂ)
    (hV : V ∈ Matrix.unitaryGroup I ℂ) (i j : I) : ‖V i j‖ ≤ 1 := by
  let v : EuclideanSpace ℂ I := WithLp.toLp 2 (Vᵀ j)
  have hin : inner ℂ v v = 1 := by
    have hGram : Vᴴ * V = 1 := Matrix.mem_unitaryGroup_iff'.mp hV
    have hjj := congrArg (fun X : Matrix I I ℂ => X j j) hGram
    have hi : inner ℂ v v = (Vᴴ * V) j j := inner_matrix_col_col V V j j
    exact hi.trans (by simpa only [Matrix.one_apply_eq] using hjj)
  have hn : ‖v‖ = 1 := by
    have hsq := norm_sq_eq_re_inner (𝕜 := ℂ) v
    rw [hin] at hsq
    change ‖v‖ ^ 2 = 1 at hsq
    nlinarith [norm_nonneg v]
  have h := PiLp.norm_apply_le v i
  simpa only [v, PiLp.toLp_apply, Matrix.transpose_apply, hn] using h

theorem norm_trace_posSemidef_mul_unitary_le (A V : Matrix I I ℂ)
    (hA : A.PosSemidef) (hV : V ∈ Matrix.unitaryGroup I ℂ) :
    ‖(A * V).trace‖ ≤ A.trace.re := by
  let S := hA.isHermitian.eigenvectorUnitary
  let D : Matrix I I ℂ := Matrix.diagonal (fun i => (hA.isHermitian.eigenvalues i : ℂ))
  let W : Matrix.unitaryGroup I ℂ := star S * ⟨V, hV⟩ * S
  have hspec : A = (S : Matrix I I ℂ) * D * (S : Matrix I I ℂ)ᴴ := by
    exact hA.isHermitian.spectral_theorem
  have htr : (A * V).trace = (D * (W : Matrix I I ℂ)).trace := by
    rw [hspec]
    change (((S : Matrix I I ℂ) * D * (S : Matrix I I ℂ)ᴴ) * V).trace =
      (D * ((S : Matrix I I ℂ)ᴴ * V * (S : Matrix I I ℂ))).trace
    calc
      _ = ((S : Matrix I I ℂ) * (D * ((S : Matrix I I ℂ)ᴴ * V))).trace := by
        simp only [Matrix.mul_assoc]
      _ = ((D * ((S : Matrix I I ℂ)ᴴ * V)) * (S : Matrix I I ℂ)).trace :=
        Matrix.trace_mul_comm _ _
      _ = _ := by rw [Matrix.mul_assoc]
  have hdiag : (D * (W : Matrix I I ℂ)).trace =
      ∑ i : I, (hA.isHermitian.eigenvalues i : ℂ) * (W : Matrix I I ℂ) i i := by
    simp [D, Matrix.trace, Matrix.diagonal_mul]
  have hAtr : A.trace.re = ∑ i : I, hA.isHermitian.eigenvalues i := by
    rw [hA.isHermitian.trace_eq_sum_eigenvalues]
    simp
  rw [htr, hdiag, hAtr]
  calc
    ‖∑ i : I, (hA.isHermitian.eigenvalues i : ℂ) * (W : Matrix I I ℂ) i i‖ ≤
        ∑ i : I, ‖(hA.isHermitian.eigenvalues i : ℂ) * (W : Matrix I I ℂ) i i‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i : I, hA.isHermitian.eigenvalues i := by
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (hA.eigenvalues_nonneg i)]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left
        (norm_unitary_entry_le_one W.val W.property i i) (hA.eigenvalues_nonneg i)

theorem norm_trace_unitary_mul_le_absolute_trace (M V : Matrix I I ℂ)
    (hV : V ∈ Matrix.unitaryGroup I ℂ) :
    ‖(V * M).trace‖ ≤ (CFC.sqrt (Mᴴ * M)).trace.re := by
  obtain ⟨U, hU, hM⟩ := exists_polar_unitary M
  have hS : (CFC.sqrt (Mᴴ * M)).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg _)
  have hVU : V * U ∈ Matrix.unitaryGroup I ℂ :=
    (Matrix.unitaryGroup I ℂ).mul_mem hV hU
  calc
    _ = ‖(V * (U * CFC.sqrt (Mᴴ * M))).trace‖ :=
      congrArg (fun X : Matrix I I ℂ => ‖(V * X).trace‖) hM
    _ = ‖(CFC.sqrt (Mᴴ * M) * (V * U)).trace‖ := by
      rw [← Matrix.mul_assoc, Matrix.trace_mul_comm]
    _ ≤ _ := norm_trace_posSemidef_mul_unitary_le _ (V * U) hS hVU

theorem norm_absolute_trace_eq_real_trace (M : Matrix I I ℂ) :
    ‖(CFC.sqrt (Mᴴ * M)).trace‖ = (CFC.sqrt (Mᴴ * M)).trace.re := by
  have hS : (CFC.sqrt (Mᴴ * M)).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg _)
  have h := congrArg Complex.re (Complex.eq_coe_norm_of_nonneg hS.trace_nonneg)
  simpa only [Complex.ofReal_re] using h.symm

theorem absolute_trace_le_conjTranspose (M : Matrix I I ℂ) :
    (CFC.sqrt (Mᴴ * M)).trace.re ≤ (CFC.sqrt (Mᴴᴴ * Mᴴ)).trace.re := by
  obtain ⟨U, hU, hAlign⟩ := exists_unitary_trace_alignment M
  have hnorm : ‖(Uᴴ * M).trace‖ = ‖(U * Mᴴ).trace‖ := by
    calc
      _ = ‖star (Uᴴ * M).trace‖ := (norm_star _).symm
      _ = ‖((Uᴴ * M)ᴴ).trace‖ := by rw [Matrix.trace_conjTranspose]
      _ = ‖(Mᴴ * U).trace‖ := by
        rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
      _ = _ := by rw [Matrix.trace_mul_comm]
  calc
    _ = ‖(Uᴴ * M).trace‖ := by rw [hAlign, norm_absolute_trace_eq_real_trace]
    _ = ‖(U * Mᴴ).trace‖ := hnorm
    _ ≤ _ := norm_trace_unitary_mul_le_absolute_trace Mᴴ U hU

theorem absolute_trace_left_right_gram (M : Matrix I I ℂ) :
    (CFC.sqrt (Mᴴ * M)).trace.re = (CFC.sqrt (M * Mᴴ)).trace.re := by
  apply le_antisymm
  · simpa only [Matrix.conjTranspose_conjTranspose] using absolute_trace_le_conjTranspose M
  · simpa only [Matrix.conjTranspose_conjTranspose] using absolute_trace_le_conjTranspose Mᴴ

theorem sqrt_product_absolute_trace_sandwich
    (A B : Matrix I I ℂ) (hA : A.PosSemidef) (hB : B.PosSemidef) :
    (CFC.sqrt ((CFC.sqrt A * CFC.sqrt B)ᴴ * (CFC.sqrt A * CFC.sqrt B))).trace.re =
      (CFC.sqrt (CFC.sqrt A * B * CFC.sqrt A)).trace.re := by
  have hRootA : (CFC.sqrt A).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)
  have hRootB : (CFC.sqrt B).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg B)
  have hFactor : (CFC.sqrt A * CFC.sqrt B) * (CFC.sqrt A * CFC.sqrt B)ᴴ =
      CFC.sqrt A * B * CFC.sqrt A := by
    calc
      _ = CFC.sqrt A * (CFC.sqrt B * CFC.sqrt B) * CFC.sqrt A := by
        rw [Matrix.conjTranspose_mul, hRootA.isHermitian.eq, hRootB.isHermitian.eq]
        noncomm_ring
      _ = _ := by rw [CFC.sqrt_mul_sqrt_self B hB.nonneg]
  rw [absolute_trace_left_right_gram, hFactor]

def matrixVector (M : Matrix I O ℂ) : I × O → ℂ := fun p => M p.1 p.2

theorem columns_matrixVector (M : Matrix I O ℂ) : columns (matrixVector M) = M := rfl

theorem inner_matrixVector (A B : Matrix I O ℂ) :
    inner ℂ (WithLp.toLp 2 (matrixVector A)) (WithLp.toLp 2 (matrixVector B)) =
      (Aᴴ * B).trace := by
  simp only [EuclideanSpace.inner_toLp_toLp, dotProduct, matrixVector,
    Fintype.sum_prod_type, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.conjTranspose_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  exact mul_comm _ _

theorem traceRight_pureMatrix_matrixVector (M : Matrix I O ℂ) :
    traceRight (pureMatrix (matrixVector M)) = M * Mᴴ := by
  rw [traceRight_pureMatrix, columns_matrixVector]

theorem exists_ancillary_unitary_of_same_marginal (v w : I × O → ℂ)
    (hMarg : traceRight (pureMatrix v) = traceRight (pureMatrix w)) :
    ∃ U : Matrix O O ℂ, U ∈ Matrix.unitaryGroup O ℂ ∧
      columns w = columns v * U := by
  have hGram : (columns v)ᴴᴴ * (columns v)ᴴ =
      (columns w)ᴴᴴ * (columns w)ᴴ := by
    simpa only [Matrix.conjTranspose_conjTranspose, traceRight_pureMatrix] using hMarg
  obtain ⟨U, hU, hFactor⟩ :=
    exists_unitary_mul_of_gram_eq (columns v)ᴴ (columns w)ᴴ hGram
  have hUstar : Uᴴ ∈ Matrix.unitaryGroup O ℂ := by
    apply Matrix.mem_unitaryGroup_iff'.mpr
    simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose] using
      (Matrix.mem_unitaryGroup_iff.mp hU)
  refine ⟨Uᴴ, hUstar, ?_⟩
  have h := congrArg Matrix.conjTranspose hFactor
  simpa only [Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_mul] using h

theorem exists_aligned_squareRoot_purifications (A B : Matrix I I ℂ)
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    ∃ v w : I × I → ℂ,
      traceRight (pureMatrix v) = A ∧ traceRight (pureMatrix w) = B ∧
      inner ℂ (WithLp.toLp 2 v) (WithLp.toLp 2 w) =
        (CFC.sqrt ((CFC.sqrt A * CFC.sqrt B)ᴴ *
          (CFC.sqrt A * CFC.sqrt B))).trace := by
  let M := CFC.sqrt A * CFC.sqrt B
  obtain ⟨U, hU, hAlign⟩ := exists_unitary_trace_alignment M
  let v := matrixVector (CFC.sqrt A)
  let w := matrixVector (CFC.sqrt B * Uᴴ)
  have hRootA : (CFC.sqrt A).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)
  have hRootB : (CFC.sqrt B).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg B)
  refine ⟨v, w, ?_, ?_, ?_⟩
  · exact traceRight_pureMatrix_sqrtColumns A hA
  · rw [traceRight_pureMatrix_matrixVector, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, hRootB.isHermitian.eq]
    have hUU : Uᴴ * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hU
    calc
      _ = CFC.sqrt B * (Uᴴ * U) * CFC.sqrt B := by simp only [Matrix.mul_assoc]
      _ = B := by rw [hUU, Matrix.mul_one]; exact CFC.sqrt_mul_sqrt_self B hB.nonneg
  · rw [inner_matrixVector, hRootA.isHermitian.eq]
    change (CFC.sqrt A * (CFC.sqrt B * Uᴴ)).trace = (CFC.sqrt (Mᴴ * M)).trace
    rw [← Matrix.mul_assoc, Matrix.trace_mul_comm]
    exact hAlign

end QuantumProver.BellDiagonalSquashedEntanglement.Geometry

import QuantumProver.QuantumGates.ControlledCliffordHierarchy.SignedAffineProfiles

noncomputable section
set_option maxHeartbeats 1200000
open scoped Matrix BigOperators

namespace QuantumProver.ControlledCliffordHierarchy

theorem matrixZpow_signed_involution {n : ℕ} {U : MatrixUnitary n}
    (s : ZMod 2) (p : PauliLabel n)
    (hp : (U : QuantumMatrix n) = signedOrderedPauli s p)
    (hHerm : dot p.2 p.1 = 0) (k : ℤ) :
    matrixZpow U k = signedOrderedPauli ((k : ZMod 2) * s) ((k : ZMod 2) • p) := by
  have hU2 : U ^ (2 : ℕ) = 1 := by
    apply Subtype.ext
    change (U : QuantumMatrix n) ^ 2 = 1
    rw [hp, pow_two, signedOrderedPauli_mul]
    simp only [module_charTwo_add_self, hHerm, zero_add, signedOrderedPauli,
      bitSign_zero, one_smul]
    change orderedPauli (0 : BitString n) 0 = 1
    exact orderedPauli_zero
  have hrem : U ^ k = U ^ (k % 2) := zpow_eq_zpow_emod' k hU2
  rcases Int.emod_two_eq_zero_or_one k with h0 | h1
  · have hk : (k : ZMod 2) = 0 := by
      simpa only [Nat.cast_ofNat, h0, Int.cast_zero] using (ZMod.intCast_mod k 2).symm
    rw [matrixZpow, hrem, h0]
    simp [hk, signedOrderedPauli]
  · have hk : (k : ZMod 2) = 1 := by
      simpa only [Nat.cast_ofNat, h1, Int.cast_one] using (ZMod.intCast_mod k 2).symm
    rw [matrixZpow, hrem, h1]
    simpa only [zpow_one, hk, one_mul, one_smul] using hp

theorem matrixZpow_absorb_q {n q : ℕ} {T : MatrixUnitary n}
    (s : ZMod 2) (p : PauliLabel n)
    (hp : ((T ^ q : MatrixUnitary n) : QuantumMatrix n) = signedOrderedPauli s p)
    (hHerm : dot p.2 p.1 = 0) (t : ℤ) :
    matrixZpow T t =
      signedOrderedPauli (((t / (q : ℤ) : ℤ) : ZMod 2) * s)
        (((t / (q : ℤ) : ℤ) : ZMod 2) • p) * matrixZpow T (t % (q : ℤ)) := by
  have hsplit : T ^ t = (T ^ q) ^ (t / (q : ℤ)) * T ^ (t % (q : ℤ)) := by
    calc
      T ^ t = T ^ (t % (q : ℤ) + (q : ℤ) * (t / (q : ℤ))) :=
        congrArg (fun a : ℤ => T ^ a) (Int.emod_add_mul_ediv t (q : ℤ)).symm
      _ = T ^ ((q : ℤ) * (t / (q : ℤ)) + t % (q : ℤ)) := by rw [add_comm]
      _ = _ := by rw [zpow_add, zpow_mul, zpow_natCast]
  have hm := congrArg (fun U : MatrixUnitary n => (U : QuantumMatrix n)) hsplit
  change matrixZpow T t = matrixZpow (T ^ q) (t / (q : ℤ)) *
    matrixZpow T (t % (q : ℤ)) at hm
  rw [hm, matrixZpow_signed_involution s p hp hHerm]

theorem matrixZpow_absorb_label_mem {n q : ℕ} (W : Submodule (ZMod 2) (PauliLabel n))
    (p : PauliLabel n) (hp : p ∈ W) (t : ℤ) :
    (((t / (q : ℤ) : ℤ) : ZMod 2) • p) ∈ W := W.smul_mem _ hp

theorem signed_profile_absorb {n : ℕ}
    (s k : ZMod 2 → ZMod 2 → ZMod 2)
    (y p : ZMod 2 → ZMod 2 → PauliLabel n)
    (F Fstar : ZMod 2 → ZMod 2 → QuantumMatrix n)
    (hF : ∀ c b, F c b = signedOrderedPauli (k c b) (p c b) * Fstar c b)
    (c b : ZMod 2) :
    signedOrderedPauli (s c b) (y c b) * F c b =
      signedOrderedPauli (s c b + k c b + dot (y c b).2 (p c b).1)
        (y c b + p c b) * Fstar c b := by
  rw [hF c b, ← mul_assoc, signedOrderedPauli_mul]

theorem controlQuad_absorbed_mem {n : ℕ}
    (W : Submodule (ZMod 2) (PauliLabel n))
    (y p : ZMod 2 → ZMod 2 → PauliLabel n)
    (hy : controlQuad y ∈ W) (hp : ∀ c b, p c b ∈ W) :
    controlQuad (fun c b => y c b + p c b) ∈ W := by
  rw [controlQuad_add]
  exact W.add_mem hy (controlQuad_mem W p hp)

end QuantumProver.ControlledCliffordHierarchy

open scoped BigOperators

namespace QuantumProver.ControlledCliffordHierarchy

section AugmentationImage

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

theorem labelEnd_add_self (L : Module.End (ZMod 2) V) : L + L = 0 := by
  ext v
  exact module_charTwo_add_self (L v)

theorem labelEnd_neg_eq_self (L : Module.End (ZMod 2) V) : -L = L := by
  rw [neg_eq_iff_add_eq_zero]
  exact labelEnd_add_self L

theorem labelEnd_one_add_pow_two_pow (N : Module.End (ZMod 2) V) (j : ℕ) :
    (1 + N) ^ (2 ^ j) = 1 + N ^ (2 ^ j) := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hsquare (D : Module.End (ZMod 2) V) : (1 + D) ^ 2 = 1 + D ^ 2 := by
      calc
        (1 + D) ^ 2 = 1 + (D + D) + D ^ 2 := by noncomm_ring
        _ = 1 + D ^ 2 := by rw [labelEnd_add_self, add_zero]
    rw [Nat.pow_succ, pow_mul, ih, hsquare, ← pow_mul]

def augmentationImage (N : Module.End (ZMod 2) V) (a : ℕ) : Submodule (ZMod 2) V :=
  LinearMap.range (N ^ a)

theorem augmentationImage_antitone (N : Module.End (ZMod 2) V)
    {a b : ℕ} (hab : a ≤ b) : augmentationImage N b ≤ augmentationImage N a := by
  rintro v ⟨w, hw⟩
  refine ⟨(N ^ (b - a)) w, ?_⟩
  have he : a + (b - a) = b := by omega
  calc
    (N ^ a) ((N ^ (b - a)) w) = (N ^ (a + (b - a))) w := by
      rw [pow_add]
      rfl
    _ = v := by rw [he, hw]

theorem augmentationImage_commute (N L : Module.End (ZMod 2) V)
    (h : Commute L N) (a : ℕ) {v : V} (hv : v ∈ augmentationImage N a) :
    L v ∈ augmentationImage N a := by
  obtain ⟨w, rfl⟩ := hv
  refine ⟨L w, ?_⟩
  simpa only [Module.End.mul_apply] using
    congrArg (fun A : Module.End (ZMod 2) V => A w) (h.pow_right a).eq.symm

theorem augmentationImage_factor_raise (N L C : Module.End (ZMod 2) V)
    (a d : ℕ) (hL : L = N ^ d * C) (hC : Commute C N)
    {v : V} (hv : v ∈ augmentationImage N a) :
    L v ∈ augmentationImage N (a + d) := by
  obtain ⟨w, rfl⟩ := hv
  refine ⟨C w, ?_⟩
  calc
    (N ^ (a + d)) (C w) = (N ^ (d + a)) (C w) := by rw [Nat.add_comm]
    _ = (N ^ d) ((N ^ a) (C w)) := by rw [pow_add]; rfl
    _ = (N ^ d) (C ((N ^ a) w)) := by
      congr 1
      simpa only [Module.End.mul_apply] using
        congrArg (fun A : Module.End (ZMod 2) V => A w) (hC.pow_right a).eq.symm
    _ = L ((N ^ a) w) := by rw [hL]; rfl

theorem augmentationImage_zero (N : Module.End (ZMod 2) V) (a : ℕ)
    (hN : N ^ a = 0) : augmentationImage N a = ⊥ := by
  simp only [augmentationImage, hN, LinearMap.range_zero]

def dyadicShiftRemainder (N : Module.End (ZMod 2) V) (j k : ℕ) :
    Module.End (ZMod 2) V := ∑ i ∈ Finset.range k, (1 + N ^ (2 ^ j)) ^ i

theorem dyadicShiftRemainder_commute (N : Module.End (ZMod 2) V) (j k : ℕ) :
    Commute (dyadicShiftRemainder N j k) N := by
  have hbase : Commute (1 + N ^ (2 ^ j)) N :=
    (Commute.one_left N).add_left ((Commute.refl N).pow_left (2 ^ j))
  exact Commute.sum_left (Finset.range k) (fun i => (1 + N ^ (2 ^ j)) ^ i) N
    (fun i _ => hbase.pow_left i)

theorem dyadicShift_difference_factor (N : Module.End (ZMod 2) V) (j k : ℕ) :
    (1 + N) ^ (2 ^ j * k) - 1 = N ^ (2 ^ j) * dyadicShiftRemainder N j k := by
  rw [pow_mul, labelEnd_one_add_pow_two_pow]
  change (1 + N ^ (2 ^ j)) ^ k - 1 =
    N ^ (2 ^ j) * ∑ i ∈ Finset.range k, (1 + N ^ (2 ^ j)) ^ i
  calc
    _ = (1 + N ^ (2 ^ j) - 1) * ∑ i ∈ Finset.range k, (1 + N ^ (2 ^ j)) ^ i :=
      (mul_geom_sum (1 + N ^ (2 ^ j)) k).symm
    _ = _ := by congr 1; abel

theorem dyadicShift_difference_raise (N : Module.End (ZMod 2) V) (a j k : ℕ)
    {v : V} (hv : v ∈ augmentationImage N a) :
    (((1 + N) ^ (2 ^ j * k) - 1) v) ∈ augmentationImage N (a + 2 ^ j) :=
  augmentationImage_factor_raise N _ (dyadicShiftRemainder N j k) a (2 ^ j)
    (dyadicShift_difference_factor N j k) (dyadicShiftRemainder_commute N j k) hv

theorem dyadicShift_difference_full_image (N : Module.End (ZMod 2) V)
    (j k : ℕ) (v : V) :
    (((1 + N) ^ (2 ^ j * k) - 1) v) ∈ augmentationImage N (2 ^ j) := by
  have hv : v ∈ augmentationImage N 0 := ⟨v, by simp⟩
  simpa only [zero_add] using dyadicShift_difference_raise N 0 j k hv

theorem labelEnd_quadratic_coefficient (C B D : Module.End (ZMod 2) V) :
    1 + B + C + C * B * D = (C - 1) * (B - 1) + C * B * (D - 1) := by
  calc
    1 + B + C + C * B * D = 1 - C - B + C * B * D := by
      simp only [sub_eq_add_neg, labelEnd_neg_eq_self]
      abel
    _ = _ := by noncomm_ring

theorem labelEnd_quadratic_mem
    (W Wnext : Submodule (ZMod 2) V) (C B D : Module.End (ZMod 2) V)
    (hB : ∀ z, (B - 1) z ∈ W)
    (hC : ∀ z ∈ W, (C - 1) z ∈ Wnext)
    (hD : ∀ z, (D - 1) z ∈ Wnext)
    (hPresC : ∀ z ∈ Wnext, C z ∈ Wnext)
    (hPresB : ∀ z ∈ Wnext, B z ∈ Wnext) (z : V) :
    ((1 + B + C + C * B * D) z) ∈ Wnext := by
  rw [labelEnd_quadratic_coefficient]
  simp only [LinearMap.add_apply, Module.End.mul_apply]
  exact Wnext.add_mem (hC _ (hB z)) (hPresC _ (hPresB _ (hD z)))

theorem controlQuad_labelEnd_profile_mem
    (W Wnext : Submodule (ZMod 2) V)
    (F : ZMod 2 → ZMod 2 → Module.End (ZMod 2) V)
    (C B D : Module.End (ZMod 2) V)
    (h00 : F 0 0 = 1) (h01 : F 0 1 = B) (h10 : F 1 0 = C)
    (h11 : F 1 1 = C * B * D)
    (hB : ∀ z, (B - 1) z ∈ W)
    (hC : ∀ z ∈ W, (C - 1) z ∈ Wnext)
    (hD : ∀ z, (D - 1) z ∈ Wnext)
    (hPresC : ∀ z ∈ Wnext, C z ∈ Wnext)
    (hPresB : ∀ z ∈ Wnext, B z ∈ Wnext) (z : V) :
    controlQuad (fun c b => F c b z) ∈ Wnext := by
  have heq : controlQuad (fun c b => F c b z) = (1 + B + C + C * B * D) z := by
    simp only [controlQuad, h00, h01, h10, h11, LinearMap.add_apply]
  rw [heq]
  exact labelEnd_quadratic_mem W Wnext C B D hB hC hD hPresC hPresB z

end AugmentationImage

end QuantumProver.ControlledCliffordHierarchy

open scoped Matrix BigOperators

namespace QuantumProver.ControlledCliffordHierarchy

def matrixProfileDifference {n : ℕ} (F : ZMod 2 → ZMod 2 → QuantumMatrix n)
    (ac ab : ZMod 2) : ZMod 2 → ZMod 2 → QuantumMatrix n :=
  fun c b => F c b * (F (c + ac) (b + ab)).conjTranspose

def signedMatrixProfileWord {n : ℕ} (s : ZMod 2 → ZMod 2 → ZMod 2)
    (y : ZMod 2 → ZMod 2 → PauliLabel n)
    (F : ZMod 2 → ZMod 2 → QuantumMatrix n) : ZMod 2 → ZMod 2 → QuantumMatrix n :=
  fun c b => signedOrderedPauli (s c b) (y c b) * F c b

def orderedProfileCocycle {n : ℕ} (y yf yg yp : PauliLabel n)
    (tf tg tp : ZMod 2) : ZMod 2 :=
  tf + tg + tp + dot yg.2 yg.1 + dot yp.2 yp.1 +
    (dot y.2 yf.1 + dot (y.2 + yf.2) yg.1 + dot (y.2 + yf.2 + yg.2) yp.1)

def matrixProfileNextSign {n : ℕ}
    (s : ZMod 2 → ZMod 2 → ZMod 2) (y : ZMod 2 → ZMod 2 → PauliLabel n)
    (LF LG : ZMod 2 → ZMod 2 → Module.End (ZMod 2) (PauliLabel n))
    (fSign gSign : ZMod 2 → ZMod 2 → PauliLabel n → ZMod 2)
    (ac ab : ZMod 2) (p : PauliLabel n) : ZMod 2 → ZMod 2 → ZMod 2 :=
  fun c b => s c b + s (c + ac) (b + ab) +
    orderedProfileCocycle (y c b) (LF c b p) (LG c b (y (c + ac) (b + ab)))
      (LG c b p) (fSign c b p) (gSign c b (y (c + ac) (b + ab))) (gSign c b p)

theorem signedMatrixProfile_correction {n : ℕ}
    (s : ZMod 2 → ZMod 2 → ZMod 2) (y : ZMod 2 → ZMod 2 → PauliLabel n)
    (F : ZMod 2 → ZMod 2 → QuantumMatrix n)
    (LF LG : ZMod 2 → ZMod 2 → Module.End (ZMod 2) (PauliLabel n))
    (fSign gSign : ZMod 2 → ZMod 2 → PauliLabel n → ZMod 2)
    (ac ab : ZMod 2)
    (hunit : ∀ c b, unitaryMatrix (F c b))
    (hF : ∀ c b p, conjugate (F c b) (orderedPauli p.1 p.2) =
      bitSign (fSign c b p) • orderedPauli (LF c b p).1 (LF c b p).2)
    (hG : ∀ c b p, conjugate (matrixProfileDifference F ac ab c b)
        (orderedPauli p.1 p.2) =
      bitSign (gSign c b p) • orderedPauli (LG c b p).1 (LG c b p).2)
    (p : PauliLabel n) :
    twoControlCorrectionProfile (signedMatrixProfileWord s y F) ac ab
        (orderedPauli p.1 p.2) =
      signedMatrixProfileWord (matrixProfileNextSign s y LF LG fSign gSign ac ab p)
        (labelProfileStep y LF LG ac ab p) (matrixProfileDifference F ac ab) := by
  funext c b
  have h := branchProfileStep_signed_ordered (hunit c b) (hunit (c + ac) (b + ab))
    (y c b).1 (y c b).2 (y (c + ac) (b + ab)).1 (y (c + ac) (b + ab)).2
    p.1 p.2 (LF c b p).1 (LF c b p).2
    (LG c b (y (c + ac) (b + ab))).1 (LG c b (y (c + ac) (b + ab))).2
    (LG c b p).1 (LG c b p).2
    (fSign c b p) (gSign c b (y (c + ac) (b + ab))) (gSign c b p)
    (bitSign (s c b)) (bitSign (s (c + ac) (b + ab)))
    (hF c b p) (hG c b (y (c + ac) (b + ab))) (hG c b p)
  have hlabel : labelProfileStep y LF LG ac ab p c b =
      y c b + LF c b p + LG c b (y (c + ac) (b + ab)) + LG c b p := by
    unfold labelProfileStep
    abel
  simpa only [twoControlCorrectionProfile, signedMatrixProfileWord, signedOrderedPauli,
    matrixProfileDifference, branchProfileStep, matrixProfileNextSign,
    orderedProfileCocycle, hlabel, Prod.fst_add, Prod.snd_add, bitSign_star, bitSign_add,
    smul_mul_assoc] using h

theorem signedMatrixProfile_endpoint {n : ℕ}
    (s : ZMod 2 → ZMod 2 → ZMod 2) (y : ZMod 2 → ZMod 2 → PauliLabel n)
    (F : ZMod 2 → ZMod 2 → QuantumMatrix n)
    (LF : ZMod 2 → ZMod 2 → Module.End (ZMod 2) (PauliLabel n))
    (fSign : ZMod 2 → ZMod 2 → PauliLabel n → ZMod 2)
    (E : ZMod 2 → ZMod 2 → Module.End (ZMod 2) (PauliLabel n))
    (gSign : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2 → PauliLabel n → ZMod 2)
    (gPhase : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2)
    (gLabel : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2 → PauliLabel n)
    (C : ZMod 2 → ZMod 2 → QuantumMatrix n)
    (hunit : ∀ c b, unitaryMatrix (F c b))
    (hF : ∀ c b p, conjugate (F c b) (orderedPauli p.1 p.2) =
      bitSign (fSign c b p) • orderedPauli (LF c b p).1 (LF c b p).2)
    (hG : ∀ ac ab c b p, conjugate (matrixProfileDifference F ac ab c b)
        (orderedPauli p.1 p.2) =
      bitSign (gSign ac ab c b p) • orderedPauli (E ac ab p).1 (E ac ab p).2)
    (hGword : ∀ ac ab c b, matrixProfileDifference F ac ab c b =
      signedOrderedPauli (gPhase ac ab c b) (gLabel ac ab c b) * C ac ab)
    (hC : ∀ ac ab, hierarchy n 2 (C ac ab))
    (hFaffine : ∀ p, controlQuad (fun c b => LF c b p) = 0)
    (hGaffine : ∀ ac ab, controlQuad (gLabel ac ab) = 0)
    (hAnnihilate : ∀ ac ab, controlQuad y + E ac ab (controlQuad y) = 0) :
    hierarchy ((n + 1) + 1) 3 (twoControlMatrix (signedMatrixProfileWord s y F)) := by
  apply (hierarchy_iff_pauliCorrections _).mpr
  refine ⟨twoControlMatrix_unitary _ (fun c b =>
    unitaryMatrix_mul (actualPauli_unitary (signedOrderedPauli_actual _ _))
      (hunit c b)), ?_⟩
  intro P hP
  rcases hP with ⟨v, x, z, hv, rfl⟩
  obtain ⟨⟨ac, x⟩, rfl⟩ := (controlBasisEquiv (n + 1)).symm.surjective x
  obtain ⟨⟨ab, x⟩, rfl⟩ := (controlBasisEquiv n).symm.surjective x
  obtain ⟨⟨zc, z⟩, rfl⟩ := (controlBasisEquiv (n + 1)).symm.surjective z
  obtain ⟨⟨zb, z⟩, rfl⟩ := (controlBasisEquiv n).symm.surjective z
  change hierarchy ((n + 1) + 1) 2
    (pauliCorrection (twoControlMatrix (signedMatrixProfileWord s y F))
      (v • orderedPauli (basisCons ac (basisCons ab x)) (basisCons zc (basisCons zb z))))
  rw [twoControlMatrix_actualPauli_correction (signedMatrixProfileWord s y F)
    ac ab zc zb x z hv]
  let p : PauliLabel n := (x, z)
  let yg := labelProfileStep y LF (fun _ _ => E ac ab) ac ab p
  let sg := matrixProfileNextSign s y LF (fun _ _ => E ac ab) fSign
    (gSign ac ab) ac ab p
  let yFinal : ZMod 2 → ZMod 2 → PauliLabel n :=
    fun c b => yg c b + gLabel ac ab c b
  let sFinal : ZMod 2 → ZMod 2 → ZMod 2 :=
    fun c b => sg c b + gPhase ac ab c b + dot (yg c b).2 (gLabel ac ab c b).1
  have hYg : controlQuad yg = 0 :=
    labelProfileStep_quad_zero y LF (E ac ab) (hAnnihilate ac ab) hFaffine ac ab p
  have hYFinal : controlQuad yFinal = 0 := by
    change controlQuad (fun c b => yg c b + gLabel ac ab c b) = 0
    rw [controlQuad_add, hYg, hGaffine ac ab, zero_add]
  have hword :
      twoControlCorrectionProfile (signedMatrixProfileWord s y F) ac ab
        (orderedPauli p.1 p.2) =
      (fun c b => signedOrderedPauli (sFinal c b) (yFinal c b) * C ac ab) := by
    rw [signedMatrixProfile_correction s y F LF (fun _ _ => E ac ab) fSign
      (gSign ac ab) ac ab hunit hF (hG ac ab) p]
    funext c b
    exact signed_profile_absorb sg (gPhase ac ab) yg (gLabel ac ab)
      (matrixProfileDifference F ac ab) (fun _ _ => C ac ab) (hGword ac ab) c b
  rw [hword]
  exact twoControlMatrix_signed_affine_dressed_clifford sFinal yFinal hYFinal (hC ac ab)

end QuantumProver.ControlledCliffordHierarchy

open scoped Matrix BigOperators

namespace QuantumProver.ControlledCliffordHierarchy

@[simp] theorem controlExponentBit_zero : controlExponentBit 0 = 0 := by
  rfl

@[simp] theorem controlExponentBit_one : controlExponentBit 1 = 1 := by
  rfl

theorem controlExponentBit_cast (c : ZMod 2) :
    (controlExponentBit c : ZMod 2) = c := by
  rcases physical_control_bit_cases c with rfl | rfl <;> norm_num

theorem controlExponentBit_difference (c a : ZMod 2) :
    controlExponentBit c - controlExponentBit (c + a) =
      2 * (controlExponentBit c * controlExponentBit a) - controlExponentBit a := by
  rw [controlExponentBit_add, controlExponentXor]
  ring

def halfCycleBinaryAction {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (A : Module.End (ZMod 2) V) (c : ZMod 2) : Module.End (ZMod 2) V :=
  if c = 0 then 1 else A

def halfCycleLabelAction {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (A B : Module.End (ZMod 2) V) (c b : ZMod 2) : Module.End (ZMod 2) V :=
  halfCycleBinaryAction A c * halfCycleBinaryAction B b

def halfCyclePairSign {n : ℕ} (A B : Module.End (ZMod 2) (PauliLabel n))
    (ka kb : PauliLabel n → ZMod 2) (c b : ZMod 2) (p : PauliLabel n) : ZMod 2 :=
  (if b = 0 then 0 else kb p) +
    (if c = 0 then 0 else ka (halfCycleBinaryAction B b p))

def matrixHalfCycleProfile {n : ℕ} (S0 S1 : MatrixUnitary n) :
    ZMod 2 → ZMod 2 → QuantumMatrix n :=
  matrixShiftProfile S0 S1 (fun c _ => controlExponentBit c)
    (fun _ b => controlExponentBit b)

def matrixHalfCycleConstant {n : ℕ} (S0 S1 : MatrixUnitary n)
    (ac ab : ZMod 2) : QuantumMatrix n :=
  matrixZpow S0 (-controlExponentBit ac) * matrixZpow S1 (-controlExponentBit ab)

def halfCycleSquareLabel {n : ℕ} (p0 p1 : PauliLabel n)
    (ac ab c b : ZMod 2) : PauliLabel n := (c * ac) • p0 + (b * ab) • p1

def halfCycleSquareSign {n : ℕ} (s0 s1 : ZMod 2) (p0 p1 : PauliLabel n)
    (ac ab c b : ZMod 2) : ZMod 2 :=
  (c * ac) * s0 + (b * ab) * s1 + dot ((c * ac) • p0).2 ((b * ab) • p1).1

theorem matrixUnitary_halfCycle_difference {n : ℕ} {S0 S1 : MatrixUnitary n}
    (h : Commute S0 S1) (ac ab c b : ZMod 2) :
    (S0 ^ controlExponentBit c * S1 ^ controlExponentBit b) *
        (S0 ^ controlExponentBit (c + ac) * S1 ^ controlExponentBit (b + ab))⁻¹ =
      (S0 ^ (2 : ℕ)) ^ (controlExponentBit c * controlExponentBit ac) *
        (S1 ^ (2 : ℕ)) ^ (controlExponentBit b * controlExponentBit ab) *
        (S0 ^ (-controlExponentBit ac) * S1 ^ (-controlExponentBit ab)) := by
  rw [matrixUnitary_shift_difference h, controlExponentBit_difference,
    controlExponentBit_difference, sub_eq_add_neg, sub_eq_add_neg, zpow_add, zpow_add]
  let k0 := controlExponentBit c * controlExponentBit ac
  let k1 := controlExponentBit b * controlExponentBit ab
  change (S0 ^ (2 * k0) * S0 ^ (-controlExponentBit ac)) *
      (S1 ^ (2 * k1) * S1 ^ (-controlExponentBit ab)) = _
  calc
    (S0 ^ (2 * k0) * S0 ^ (-controlExponentBit ac)) *
        (S1 ^ (2 * k1) * S1 ^ (-controlExponentBit ab)) =
      S0 ^ (2 * k0) * (S0 ^ (-controlExponentBit ac) * S1 ^ (2 * k1)) *
        S1 ^ (-controlExponentBit ab) := by simp only [mul_assoc]
    _ = S0 ^ (2 * k0) * (S1 ^ (2 * k1) * S0 ^ (-controlExponentBit ac)) *
        S1 ^ (-controlExponentBit ab) := by
      rw [(h.zpow_zpow (-controlExponentBit ac) (2 * k1)).eq]
    _ = (S0 ^ (2 : ℕ)) ^ k0 * (S1 ^ (2 : ℕ)) ^ k1 *
        (S0 ^ (-controlExponentBit ac) * S1 ^ (-controlExponentBit ab)) := by
      have hpow (S : MatrixUnitary n) (k : ℤ) :
          S ^ (2 * k) = (S ^ (2 : ℕ)) ^ k := by
        rw [zpow_mul]
        rfl
      rw [hpow S0 k0, hpow S1 k1]
      simp only [mul_assoc]

theorem matrixHalfCycle_difference_word {n : ℕ} {S0 S1 : MatrixUnitary n}
    (h : Commute S0 S1) (s0 s1 : ZMod 2) (p0 p1 : PauliLabel n)
    (hp0 : ((S0 ^ (2 : ℕ) : MatrixUnitary n) : QuantumMatrix n) = signedOrderedPauli s0 p0)
    (hp1 : ((S1 ^ (2 : ℕ) : MatrixUnitary n) : QuantumMatrix n) = signedOrderedPauli s1 p1)
    (hh0 : dot p0.2 p0.1 = 0) (hh1 : dot p1.2 p1.1 = 0)
    (ac ab c b : ZMod 2) :
    matrixProfileDifference (matrixHalfCycleProfile S0 S1) ac ab c b =
      signedOrderedPauli (halfCycleSquareSign s0 s1 p0 p1 ac ab c b)
        (halfCycleSquareLabel p0 p1 ac ab c b) * matrixHalfCycleConstant S0 S1 ac ab := by
  have hm := congrArg (fun U : MatrixUnitary n => (U : QuantumMatrix n))
    (matrixUnitary_halfCycle_difference h ac ab c b)
  have he : matrixProfileDifference (matrixHalfCycleProfile S0 S1) ac ab c b =
      matrixZpow (S0 ^ (2 : ℕ)) (controlExponentBit c * controlExponentBit ac) *
        matrixZpow (S1 ^ (2 : ℕ)) (controlExponentBit b * controlExponentBit ab) *
        matrixHalfCycleConstant S0 S1 ac ab := by
    simpa only [matrixProfileDifference, matrixHalfCycleProfile, matrixShiftProfile,
      matrixHalfCycleConstant, matrixZpow, Submonoid.coe_mul, matrixUnitary_inv_coe] using hm
  rw [he, matrixZpow_signed_involution s0 p0 hp0 hh0,
    matrixZpow_signed_involution s1 p1 hp1 hh1]
  simp only [Int.cast_mul, controlExponentBit_cast, signedOrderedPauli_mul,
    halfCycleSquareSign, halfCycleSquareLabel]

theorem signedAction_inverse_of_involution {n : ℕ} {U : QuantumMatrix n}
    (hU : unitaryMatrix U) (A : Module.End (ZMod 2) (PauliLabel n))
    (k : PauliLabel n → ZMod 2) (hA2 : A ^ 2 = 1)
    (hA : ∀ p, conjugate U (orderedPauli p.1 p.2) =
      bitSign (k p) • orderedPauli (A p).1 (A p).2) (p : PauliLabel n) :
    conjugate U.conjTranspose (orderedPauli p.1 p.2) =
      bitSign (k (A p)) • orderedPauli (A p).1 (A p).2 := by
  have haa : A (A p) = p := by
    simpa only [pow_two, Module.End.mul_apply, Module.End.one_apply] using
      congrArg (fun L : Module.End (ZMod 2) (PauliLabel n) => L p) hA2
  have hi := congrArg (conjugate U.conjTranspose) (hA (A p))
  rw [conjugate_inverse_left hU, haa, conjugate_smul_right] at hi
  calc
    conjugate U.conjTranspose (orderedPauli p.1 p.2) =
        bitSign (k (A p)) • (bitSign (k (A p)) •
          conjugate U.conjTranspose (orderedPauli p.1 p.2)) := by
      rw [smul_smul, bitSign_mul_self, one_smul]
    _ = bitSign (k (A p)) • orderedPauli (A p).1 (A p).2 := by rw [← hi]

theorem matrixZpow_bit_signed_action {n : ℕ} {S : MatrixUnitary n}
    (A : Module.End (ZMod 2) (PauliLabel n)) (k : PauliLabel n → ZMod 2)
    (hA : ∀ p, conjugate (S : QuantumMatrix n) (orderedPauli p.1 p.2) =
      bitSign (k p) • orderedPauli (A p).1 (A p).2) (c : ZMod 2) (p : PauliLabel n) :
    conjugate (matrixZpow S (controlExponentBit c)) (orderedPauli p.1 p.2) =
      bitSign (if c = 0 then 0 else k p) •
        orderedPauli (halfCycleBinaryAction A c p).1 (halfCycleBinaryAction A c p).2 := by
  rcases physical_control_bit_cases c with rfl | rfl
  · simp [matrixZpow, halfCycleBinaryAction]
  · simpa only [controlExponentBit_one, matrixZpow, zpow_one, halfCycleBinaryAction,
      one_ne_zero, if_false] using hA p

theorem matrixZpow_neg_bit_signed_action {n : ℕ} {S : MatrixUnitary n}
    (A : Module.End (ZMod 2) (PauliLabel n)) (k : PauliLabel n → ZMod 2)
    (hA2 : A ^ 2 = 1)
    (hA : ∀ p, conjugate (S : QuantumMatrix n) (orderedPauli p.1 p.2) =
      bitSign (k p) • orderedPauli (A p).1 (A p).2) (c : ZMod 2) (p : PauliLabel n) :
    conjugate (matrixZpow S (-controlExponentBit c)) (orderedPauli p.1 p.2) =
      bitSign (if c = 0 then 0 else k (A p)) •
        orderedPauli (halfCycleBinaryAction A c p).1 (halfCycleBinaryAction A c p).2 := by
  rcases physical_control_bit_cases c with rfl | rfl
  · simp [matrixZpow, halfCycleBinaryAction]
  · rw [controlExponentBit_one, matrixZpow_neg]
    have hi := signedAction_inverse_of_involution (matrixUnitary_unitary S) A k hA2 hA p
    simpa only [matrixZpow, zpow_one, halfCycleBinaryAction, one_ne_zero, if_false] using hi

theorem matrixHalfCycle_full_signed_action {n : ℕ} {S0 S1 : MatrixUnitary n}
    (A B : Module.End (ZMod 2) (PauliLabel n)) (ka kb : PauliLabel n → ZMod 2)
    (hA : ∀ p, conjugate (S0 : QuantumMatrix n) (orderedPauli p.1 p.2) =
      bitSign (ka p) • orderedPauli (A p).1 (A p).2)
    (hB : ∀ p, conjugate (S1 : QuantumMatrix n) (orderedPauli p.1 p.2) =
      bitSign (kb p) • orderedPauli (B p).1 (B p).2)
    (c b : ZMod 2) (p : PauliLabel n) :
    conjugate (matrixHalfCycleProfile S0 S1 c b) (orderedPauli p.1 p.2) =
      bitSign (halfCyclePairSign A B ka kb c b p) •
        orderedPauli (halfCycleLabelAction A B c b p).1 (halfCycleLabelAction A B c b p).2 := by
  rw [matrixHalfCycleProfile, matrixShiftProfile, conjugate_comp,
    matrixZpow_bit_signed_action B kb hB, conjugate_smul_right,
    matrixZpow_bit_signed_action A ka hA, smul_smul, ← bitSign_add]
  rfl

theorem matrixHalfCycleConstant_signed_action {n : ℕ} {S0 S1 : MatrixUnitary n}
    (A B : Module.End (ZMod 2) (PauliLabel n)) (ka kb : PauliLabel n → ZMod 2)
    (hA2 : A ^ 2 = 1) (hB2 : B ^ 2 = 1)
    (hA : ∀ p, conjugate (S0 : QuantumMatrix n) (orderedPauli p.1 p.2) =
      bitSign (ka p) • orderedPauli (A p).1 (A p).2)
    (hB : ∀ p, conjugate (S1 : QuantumMatrix n) (orderedPauli p.1 p.2) =
      bitSign (kb p) • orderedPauli (B p).1 (B p).2)
    (ac ab : ZMod 2) (p : PauliLabel n) :
    conjugate (matrixHalfCycleConstant S0 S1 ac ab) (orderedPauli p.1 p.2) =
      bitSign (halfCyclePairSign A B (fun p => ka (A p)) (fun p => kb (B p)) ac ab p) •
        orderedPauli (halfCycleLabelAction A B ac ab p).1
          (halfCycleLabelAction A B ac ab p).2 := by
  rw [matrixHalfCycleConstant, conjugate_comp,
    matrixZpow_neg_bit_signed_action B kb hB2 hB, conjugate_smul_right,
    matrixZpow_neg_bit_signed_action A ka hA2 hA, smul_smul, ← bitSign_add]
  rfl

theorem signedOrderedPauli_conjugate_ordered {n : ℕ} (s : ZMod 2) (p q : PauliLabel n) :
    conjugate (signedOrderedPauli s p) (orderedPauli q.1 q.2) =
      bitSign (dot p.2 q.1 + dot q.2 p.1) • orderedPauli q.1 q.2 := by
  rw [signedOrderedPauli, conjugate_smul_left _ _ (pauliPhase_star_mul (bitSign_phase s))]
  rw [conjugate, orderedPauli_commute p.1 p.2 q.1 q.2, smul_mul_assoc,
    mul_assoc, (orderedPauli_unitary p.1 p.2).2, mul_one]
  simp only [character, ← bitSign_add]

theorem matrixZpow_neg_bit_clifford {n : ℕ} {S : MatrixUnitary n}
    (hS : hierarchy n 2 (S : QuantumMatrix n)) (c : ZMod 2) :
    hierarchy n 2 (matrixZpow S (-controlExponentBit c)) := by
  rcases physical_control_bit_cases c with rfl | rfl
  · simpa only [controlExponentBit_zero, neg_zero, matrixZpow, zpow_zero,
      Submonoid.coe_one] using actualPauli_hierarchy (by omega) (actualPauli_one n)
  · rw [controlExponentBit_one, matrixZpow_neg]
    simpa only [matrixZpow, zpow_one] using clifford_conjTranspose hS

theorem matrixHalfCycleConstant_clifford {n : ℕ} {S0 S1 : MatrixUnitary n}
    (hS0 : hierarchy n 2 (S0 : QuantumMatrix n)) (hS1 : hierarchy n 2 (S1 : QuantumMatrix n))
    (ac ab : ZMod 2) : hierarchy n 2 (matrixHalfCycleConstant S0 S1 ac ab) :=
  hierarchy_clifford_mul_left (by omega) (matrixZpow_neg_bit_clifford hS0 ac)
    (matrixZpow_neg_bit_clifford hS1 ab)

theorem halfCycleSquareLabel_affine {n : ℕ} (p0 p1 : PauliLabel n) (ac ab : ZMod 2) :
    controlQuad (halfCycleSquareLabel p0 p1 ac ab) = 0 := by
  simp only [controlQuad, halfCycleSquareLabel, zero_mul, one_mul, zero_smul,
    zero_add, add_zero]
  calc
    ab • p1 + ac • p0 + (ac • p0 + ab • p1) =
        (ab • p1 + ab • p1) + (ac • p0 + ac • p0) := by abel
    _ = 0 := by rw [module_charTwo_add_self, module_charTwo_add_self, zero_add]

theorem halfCycleLabelAction_affine {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (A B : Module.End (ZMod 2) V) (hcross : (A - 1) * (B - 1) = 0) (v : V) :
    controlQuad (fun c b => halfCycleLabelAction A B c b v) = 0 := by
  have he : 1 + B + A + A * B = (A - 1) * (B - 1) := by
    simpa only [mul_one, sub_self, mul_zero, add_zero] using
      labelEnd_quadratic_coefficient A B 1
  have hz : 1 + B + A + A * B = 0 := he.trans hcross
  simpa [controlQuad, halfCycleLabelAction, halfCycleBinaryAction] using
      congrArg (fun L : Module.End (ZMod 2) V => L v) hz

theorem halfCycleLabelAction_fix {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (W : Submodule (ZMod 2) V) (A B : Module.End (ZMod 2) V)
    (hA : ∀ v ∈ W, A v = v) (hB : ∀ v ∈ W, B v = v)
    (ac ab : ZMod 2) {v : V} (hv : v ∈ W) : halfCycleLabelAction A B ac ab v = v := by
  have hb : halfCycleBinaryAction B ab v = v := by
    unfold halfCycleBinaryAction
    split_ifs
    · rfl
    · exact hB v hv
  change halfCycleBinaryAction A ac (halfCycleBinaryAction B ab v) = v
  rw [hb]
  unfold halfCycleBinaryAction
  split_ifs
  · rfl
  · exact hA v hv

theorem matrixHalfCycle_endpoint {n : ℕ} {S0 S1 : MatrixUnitary n}
    (hcomm : Commute S0 S1)
    (hS0 : hierarchy n 2 (S0 : QuantumMatrix n)) (hS1 : hierarchy n 2 (S1 : QuantumMatrix n))
    (A B : Module.End (ZMod 2) (PauliLabel n)) (ka kb : PauliLabel n → ZMod 2)
    (hA2 : A ^ 2 = 1) (hB2 : B ^ 2 = 1) (hcross : (A - 1) * (B - 1) = 0)
    (hA : ∀ p, conjugate (S0 : QuantumMatrix n) (orderedPauli p.1 p.2) =
      bitSign (ka p) • orderedPauli (A p).1 (A p).2)
    (hB : ∀ p, conjugate (S1 : QuantumMatrix n) (orderedPauli p.1 p.2) =
      bitSign (kb p) • orderedPauli (B p).1 (B p).2)
    (s0 s1 : ZMod 2) (p0 p1 : PauliLabel n)
    (hp0 : ((S0 ^ (2 : ℕ) : MatrixUnitary n) : QuantumMatrix n) = signedOrderedPauli s0 p0)
    (hp1 : ((S1 ^ (2 : ℕ) : MatrixUnitary n) : QuantumMatrix n) = signedOrderedPauli s1 p1)
    (hh0 : dot p0.2 p0.1 = 0) (hh1 : dot p1.2 p1.1 = 0)
    (W : Submodule (ZMod 2) (PauliLabel n))
    (hFixA : ∀ v ∈ W, A v = v) (hFixB : ∀ v ∈ W, B v = v)
    (s : ZMod 2 → ZMod 2 → ZMod 2) (y : ZMod 2 → ZMod 2 → PauliLabel n)
    (hy : controlQuad y ∈ W) :
    hierarchy ((n + 1) + 1) 3
      (twoControlMatrix (signedMatrixProfileWord s y (matrixHalfCycleProfile S0 S1))) := by
  let LF := halfCycleLabelAction A B
  let sf := halfCyclePairSign A B ka kb
  let sg := halfCycleSquareSign s0 s1 p0 p1
  let yg := halfCycleSquareLabel p0 p1
  let sk := halfCyclePairSign A B (fun p => ka (A p)) (fun p => kb (B p))
  let kg : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2 → PauliLabel n → ZMod 2 :=
    fun ac ab c b p => sk ac ab p + dot (yg ac ab c b).2 (LF ac ab p).1 +
      dot (LF ac ab p).2 (yg ac ab c b).1
  apply signedMatrixProfile_endpoint s y (matrixHalfCycleProfile S0 S1) LF sf LF kg sg yg
    (matrixHalfCycleConstant S0 S1)
  · intro c b
    exact matrixShiftProfile_unitary _ _ _ _ c b
  · exact matrixHalfCycle_full_signed_action A B ka kb hA hB
  · intro ac ab c b p
    rw [matrixHalfCycle_difference_word hcomm s0 s1 p0 p1 hp0 hp1 hh0 hh1,
      conjugate_comp, matrixHalfCycleConstant_signed_action A B ka kb hA2 hB2 hA hB,
      conjugate_smul_right, signedOrderedPauli_conjugate_ordered, smul_smul, ← bitSign_add]
    simp only [kg, sk, LF, yg, add_assoc]
  · exact matrixHalfCycle_difference_word hcomm s0 s1 p0 p1 hp0 hp1 hh0 hh1
  · exact matrixHalfCycleConstant_clifford hS0 hS1
  · exact halfCycleLabelAction_affine A B hcross
  · exact halfCycleSquareLabel_affine p0 p1
  · intro ac ab
    rw [halfCycleLabelAction_fix W A B hFixA hFixB ac ab hy,
      module_charTwo_add_self]

end QuantumProver.ControlledCliffordHierarchy

open scoped Matrix BigOperators

namespace QuantumProver.ControlledCliffordHierarchy

def matrixPowerResidual (q : ℕ) (t : ℤ) : ℕ := (t % (q : ℤ)).toNat

theorem matrixPowerResidual_cast {q : ℕ} (hq : 0 < q) (t : ℤ) :
    ((matrixPowerResidual q t : ℕ) : ℤ) = t % (q : ℤ) := by
  exact Int.toNat_of_nonneg (Int.emod_nonneg t (by exact_mod_cast hq.ne'))

theorem matrixPowerResidual_lt {q : ℕ} (hq : 0 < q) (t : ℤ) :
    matrixPowerResidual q t < q := by
  have hnonneg := Int.emod_nonneg t (show (q : ℤ) ≠ 0 by exact_mod_cast hq.ne')
  have hlt := Int.emod_lt_of_pos t (show (0 : ℤ) < q by exact_mod_cast hq)
  unfold matrixPowerResidual
  omega

theorem matrixPowerResidual_dvd {q d : ℕ} (hq : 0 < q) (t : ℤ)
    (ht : (d : ℤ) ∣ t) (hdq : (d : ℤ) ∣ (q : ℤ)) :
    d ∣ matrixPowerResidual q t := by
  have hd : (d : ℤ) ∣ t % (q : ℤ) := by
    rw [Int.emod_def]
    exact ht.sub (hdq.mul_right (t / (q : ℤ)))
  rw [← matrixPowerResidual_cast hq t] at hd
  exact_mod_cast hd

theorem matrixPowerResidual_dyadic {h j : ℕ} (hj : j ≤ h) (t : ℤ)
    (ht : ((2 ^ j : ℕ) : ℤ) ∣ t) :
    2 ^ j ∣ matrixPowerResidual (2 ^ h) t := by
  have hdq : ((2 ^ j : ℕ) : ℤ) ∣ ((2 ^ h : ℕ) : ℤ) := by
    have hn : 2 ^ j ∣ 2 ^ h := by
      refine ⟨2 ^ (h - j), ?_⟩
      rw [← Nat.pow_add, Nat.add_sub_of_le hj]
    exact_mod_cast hn
  exact matrixPowerResidual_dvd (by positivity) t ht hdq

theorem matrixZpow_absorb_natResidual {n q : ℕ} {T : MatrixUnitary n}
    (hq : 0 < q) (s : ZMod 2) (p : PauliLabel n)
    (hp : ((T ^ q : MatrixUnitary n) : QuantumMatrix n) = signedOrderedPauli s p)
    (hHerm : dot p.2 p.1 = 0) (t : ℤ) :
    matrixZpow T t =
      signedOrderedPauli (((t / (q : ℤ) : ℤ) : ZMod 2) * s)
        (((t / (q : ℤ) : ℤ) : ZMod 2) • p) *
          (T : QuantumMatrix n) ^ matrixPowerResidual q t := by
  rw [matrixZpow_absorb_q s p hp hHerm t,
    ← matrixPowerResidual_cast hq t, matrixZpow_nat]

theorem matrixUnitary_two_q_pow_one {n q : ℕ} {T : MatrixUnitary n}
    (s : ZMod 2) (p : PauliLabel n)
    (hp : ((T ^ q : MatrixUnitary n) : QuantumMatrix n) = signedOrderedPauli s p)
    (hHerm : dot p.2 p.1 = 0) : T ^ (2 * q) = 1 := by
  have hsquare : (T ^ q) ^ (2 : ℕ) = 1 := by
    apply Subtype.ext
    have hm := matrixZpow_signed_involution s p hp hHerm (2 : ℤ)
    simpa [matrixZpow, signedOrderedPauli, show (2 : ZMod 2) = 0 by decide] using hm
  rw [Nat.mul_comm, pow_mul, hsquare]

theorem matrixZpow_actual_two_q_period {n q : ℕ} {T : MatrixUnitary n}
    (s : ZMod 2) (p : PauliLabel n)
    (hp : ((T ^ q : MatrixUnitary n) : QuantumMatrix n) = signedOrderedPauli s p)
    (hHerm : dot p.2 p.1 = 0) (t : ℤ) :
    matrixZpow T t = matrixZpow T (t % ((2 * q : ℕ) : ℤ)) := by
  exact congrArg (fun U : MatrixUnitary n => (U : QuantumMatrix n))
    (zpow_eq_zpow_emod' t (matrixUnitary_two_q_pow_one s p hp hHerm))

section ResidualImage

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

def matrixResidualLabelAction (N : Module.End (ZMod 2) V) (h : ℕ) (t : ℤ) :
    Module.End (ZMod 2) V := (1 + N) ^ matrixPowerResidual (2 ^ h) t

theorem matrixResidualLabelAction_commute (N : Module.End (ZMod 2) V)
    (h : ℕ) (t : ℤ) : Commute (matrixResidualLabelAction N h t) N := by
  exact ((Commute.one_left N).add_left (Commute.refl N)).pow_left _

theorem matrixResidualLabelAction_preserves (N : Module.End (ZMod 2) V)
    (h a : ℕ) (t : ℤ) {v : V} (hv : v ∈ augmentationImage N a) :
    matrixResidualLabelAction N h t v ∈ augmentationImage N a :=
  augmentationImage_commute N _ (matrixResidualLabelAction_commute N h t) a hv

theorem matrixResidualLabelAction_difference_factor (N : Module.End (ZMod 2) V)
    {h j : ℕ} (hj : j ≤ h) (t : ℤ) (ht : ((2 ^ j : ℕ) : ℤ) ∣ t) :
    ∃ C : Module.End (ZMod 2) V,
      Commute C N ∧ matrixResidualLabelAction N h t - 1 = N ^ (2 ^ j) * C := by
  obtain ⟨k, hk⟩ := matrixPowerResidual_dyadic hj t ht
  refine ⟨dyadicShiftRemainder N j k, dyadicShiftRemainder_commute N j k, ?_⟩
  unfold matrixResidualLabelAction
  rw [hk]
  exact dyadicShift_difference_factor N j k

theorem matrixResidualLabelAction_difference_raise (N : Module.End (ZMod 2) V)
    {h j : ℕ} (hj : j ≤ h) (a : ℕ) (t : ℤ)
    (ht : ((2 ^ j : ℕ) : ℤ) ∣ t) {v : V} (hv : v ∈ augmentationImage N a) :
    (matrixResidualLabelAction N h t - 1) v ∈ augmentationImage N (a + 2 ^ j) := by
  obtain ⟨C, hC, he⟩ := matrixResidualLabelAction_difference_factor N hj t ht
  exact augmentationImage_factor_raise N _ C a (2 ^ j) he hC hv

theorem matrixResidualLabelAction_difference_full_image (N : Module.End (ZMod 2) V)
    {h j : ℕ} (hj : j ≤ h) (t : ℤ) (ht : ((2 ^ j : ℕ) : ℤ) ∣ t) (v : V) :
    (matrixResidualLabelAction N h t - 1) v ∈ augmentationImage N (2 ^ j) := by
  have hv : v ∈ augmentationImage N 0 := ⟨v, by simp⟩
  simpa only [zero_add] using matrixResidualLabelAction_difference_raise N hj 0 t ht hv

end ResidualImage

end QuantumProver.ControlledCliffordHierarchy

open scoped Matrix BigOperators

namespace QuantumProver.ControlledCliffordHierarchy

theorem matrixPowerResidual_add {q : ℕ} (hq : 0 < q) (t u : ℤ) :
    matrixPowerResidual q (t + u) = (matrixPowerResidual q t + matrixPowerResidual q u) % q := by
  apply Int.ofNat_inj.mp
  rw [matrixPowerResidual_cast hq, Int.natCast_mod, Int.natCast_add,
    matrixPowerResidual_cast hq, matrixPowerResidual_cast hq]
  exact Int.add_emod t u (q : ℤ)

theorem matrixLabel_pow_mod {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    {F : Module.End (ZMod 2) V} {q : ℕ} (hF : F ^ q = 1) (r : ℕ) :
    F ^ (r % q) = F ^ r := by
  symm
  calc
    F ^ r = F ^ (r % q + q * (r / q)) := congrArg (fun a : ℕ => F ^ a) (Nat.mod_add_div r q).symm
    _ = F ^ (r % q) * (F ^ q) ^ (r / q) := by rw [pow_add, pow_mul]
    _ = F ^ (r % q) := by rw [hF, one_pow, mul_one]

theorem matrixCoefficient_depth_value {j : ℕ} {t : ControlExponentCoefficients}
    (ht : controlExponentDepth j t) (u : ControlExponentShift) :
    ((2 ^ j : ℕ) : ℤ) ∣ controlExponentFunction t u := by
  have hlow : (2 : ℤ) ^ j ∣ t.2.2 := by
    apply dvd_trans _ ht.2.2
    exact ⟨2, by rw [pow_succ]⟩
  have hdiv : (2 : ℤ) ^ j ∣ controlExponentFunction t u := by
    unfold controlExponentFunction controlExponentPolynomial
    exact ((ht.1.mul_right (controlExponentBit u.1)).add
      (ht.2.1.mul_right (controlExponentBit u.2))).add
      ((hlow.mul_right (controlExponentBit u.1)).mul_right (controlExponentBit u.2))
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using hdiv

section PairedMatrixImage

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

theorem matrixResidualLabelAction_add (N : Module.End (ZMod 2) V) (h : ℕ)
    (hN : N ^ (2 ^ h) = 0) (t u : ℤ) :
    matrixResidualLabelAction N h (t + u) =
      matrixResidualLabelAction N h t * matrixResidualLabelAction N h u := by
  have hperiod : (1 + N) ^ (2 ^ h) = 1 := by
    rw [labelEnd_one_add_pow_two_pow, hN, add_zero]
  unfold matrixResidualLabelAction
  rw [matrixPowerResidual_add (by positivity), matrixLabel_pow_mod hperiod, pow_add]

@[simp] theorem matrixResidualLabelAction_zero (N : Module.End (ZMod 2) V) (h : ℕ) :
    matrixResidualLabelAction N h 0 = 1 := by
  simp [matrixResidualLabelAction, matrixPowerResidual]

def matrixCoefficientAction (N : Module.End (ZMod 2) V) (h : ℕ)
    (t : ControlExponentCoefficients) (c b : ZMod 2) : Module.End (ZMod 2) V :=
  matrixResidualLabelAction N h (controlExponentFunction t (c, b))

theorem matrixCoefficientAction_quadratic_mem (N : Module.End (ZMod 2) V)
    {h j : ℕ} (hj : j + 1 ≤ h) (hN : N ^ (2 ^ h) = 0)
    (t : ControlExponentCoefficients) (ht : controlExponentDepth j t) (v : V) :
    controlQuad (fun c b => matrixCoefficientAction N h t c b v) ∈
      augmentationImage N (2 ^ (j + 1)) := by
  let B := matrixResidualLabelAction N h t.2.1
  let C := matrixResidualLabelAction N h t.1
  let D := matrixResidualLabelAction N h t.2.2
  have h00 : matrixCoefficientAction N h t 0 0 = 1 := by
    simp [matrixCoefficientAction, controlExponentFunction, controlExponentPolynomial]
  have h01 : matrixCoefficientAction N h t 0 1 = B := by
    simp [matrixCoefficientAction, controlExponentFunction, controlExponentPolynomial, B]
  have h10 : matrixCoefficientAction N h t 1 0 = C := by
    simp [matrixCoefficientAction, controlExponentFunction, controlExponentPolynomial, C]
  have h11 : matrixCoefficientAction N h t 1 1 = C * B * D := by
    simp only [matrixCoefficientAction, controlExponentFunction, controlExponentPolynomial,
      controlExponentBit_one, mul_one, matrixResidualLabelAction_add N h hN, C, B, D]
  have hlin : j ≤ h := by omega
  have hc : ((2 ^ j : ℕ) : ℤ) ∣ t.1 := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using ht.1
  have hb : ((2 ^ j : ℕ) : ℤ) ∣ t.2.1 := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using ht.2.1
  have hd : ((2 ^ (j + 1) : ℕ) : ℤ) ∣ t.2.2 := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using ht.2.2
  have he : 2 ^ j + 2 ^ j = 2 ^ (j + 1) := by
    simp only [Nat.pow_succ, Nat.mul_comm, two_mul]
  apply controlQuad_labelEnd_profile_mem (augmentationImage N (2 ^ j))
    (augmentationImage N (2 ^ (j + 1))) (matrixCoefficientAction N h t) C B D
    h00 h01 h10 h11
  · exact fun z => matrixResidualLabelAction_difference_full_image N hlin t.2.1 hb z
  · intro z hz
    simpa only [he] using matrixResidualLabelAction_difference_raise N hlin
      (2 ^ j) t.1 hc hz
  · exact fun z => matrixResidualLabelAction_difference_full_image N hj t.2.2 hd z
  · exact fun z hz => matrixResidualLabelAction_preserves N h (2 ^ (j + 1)) t.1 hz
  · exact fun z hz => matrixResidualLabelAction_preserves N h (2 ^ (j + 1)) t.2.1 hz

def pairedAugmentation (N : Module.End (ZMod 2) V) : Module.End (ZMod 2) (V × V) :=
  N.prodMap N

theorem pairedAugmentation_pow (N : Module.End (ZMod 2) V) (a : ℕ) :
    pairedAugmentation N ^ a = (N ^ a).prodMap (N ^ a) := by
  induction a with
  | zero => simp only [pow_zero, LinearMap.prodMap_one]
  | succ a ih =>
    rw [pow_succ, ih]
    change (N ^ a).prodMap (N ^ a) * N.prodMap N = _
    rw [LinearMap.prodMap_mul]
    simp only [pow_succ]

theorem pairedAugmentationImage_iff (N : Module.End (ZMod 2) V) (a : ℕ) (v : V × V) :
    v ∈ augmentationImage (pairedAugmentation N) a ↔
      v.1 ∈ augmentationImage N a ∧ v.2 ∈ augmentationImage N a := by
  rw [augmentationImage, pairedAugmentation_pow, LinearMap.range_prodMap]
  rfl

def pairedResidualLabelAction (N : Module.End (ZMod 2) V) (h : ℕ) (t0 t1 : ℤ) :
    Module.End (ZMod 2) (V × V) :=
  (matrixResidualLabelAction N h t0).prodMap (matrixResidualLabelAction N h t1)

theorem pairedResidualLabelAction_add (N : Module.End (ZMod 2) V) (h : ℕ)
    (hN : N ^ (2 ^ h) = 0) (t0 t1 u0 u1 : ℤ) :
    pairedResidualLabelAction N h (t0 + u0) (t1 + u1) =
      pairedResidualLabelAction N h t0 t1 * pairedResidualLabelAction N h u0 u1 := by
  simp only [pairedResidualLabelAction, matrixResidualLabelAction_add N h hN,
    LinearMap.prodMap_mul]

theorem pairedResidualLabelAction_preserves (N : Module.End (ZMod 2) V)
    (h a : ℕ) (t0 t1 : ℤ) {v : V × V}
    (hv : v ∈ augmentationImage (pairedAugmentation N) a) :
    pairedResidualLabelAction N h t0 t1 v ∈ augmentationImage (pairedAugmentation N) a := by
  obtain ⟨hv0, hv1⟩ := (pairedAugmentationImage_iff N a v).mp hv
  apply (pairedAugmentationImage_iff N a _).mpr
  exact ⟨matrixResidualLabelAction_preserves N h a t0 hv0,
    matrixResidualLabelAction_preserves N h a t1 hv1⟩

theorem pairedResidualLabelAction_difference_raise (N : Module.End (ZMod 2) V)
    {h j : ℕ} (hj : j ≤ h) (a : ℕ) (t0 t1 : ℤ)
    (ht0 : ((2 ^ j : ℕ) : ℤ) ∣ t0) (ht1 : ((2 ^ j : ℕ) : ℤ) ∣ t1)
    {v : V × V} (hv : v ∈ augmentationImage (pairedAugmentation N) a) :
    (pairedResidualLabelAction N h t0 t1 - 1) v ∈
      augmentationImage (pairedAugmentation N) (a + 2 ^ j) := by
  obtain ⟨hv0, hv1⟩ := (pairedAugmentationImage_iff N a v).mp hv
  apply (pairedAugmentationImage_iff N (a + 2 ^ j) _).mpr
  change (matrixResidualLabelAction N h t0 - 1) v.1 ∈ augmentationImage N (a + 2 ^ j) ∧
    (matrixResidualLabelAction N h t1 - 1) v.2 ∈ augmentationImage N (a + 2 ^ j)
  exact ⟨matrixResidualLabelAction_difference_raise N hj a t0 ht0 hv0,
    matrixResidualLabelAction_difference_raise N hj a t1 ht1 hv1⟩

theorem pairedResidualLabelAction_difference_full_image (N : Module.End (ZMod 2) V)
    {h j : ℕ} (hj : j ≤ h) (t0 t1 : ℤ)
    (ht0 : ((2 ^ j : ℕ) : ℤ) ∣ t0) (ht1 : ((2 ^ j : ℕ) : ℤ) ∣ t1) (v : V × V) :
    (pairedResidualLabelAction N h t0 t1 - 1) v ∈
      augmentationImage (pairedAugmentation N) (2 ^ j) := by
  have hv : v ∈ augmentationImage (pairedAugmentation N) 0 := ⟨v, by simp⟩
  simpa only [zero_add] using pairedResidualLabelAction_difference_raise N hj 0 t0 t1 ht0 ht1 hv

def pairedCoefficientAction (N : Module.End (ZMod 2) V) (h : ℕ)
    (t0 t1 : ControlExponentCoefficients) (c b : ZMod 2) : Module.End (ZMod 2) (V × V) :=
  (matrixCoefficientAction N h t0 c b).prodMap (matrixCoefficientAction N h t1 c b)

theorem pairedCoefficientAction_quadratic_mem (N : Module.End (ZMod 2) V)
    {h j : ℕ} (hj : j + 1 ≤ h) (hN : N ^ (2 ^ h) = 0)
    (t0 t1 : ControlExponentCoefficients)
    (ht0 : controlExponentDepth j t0) (ht1 : controlExponentDepth j t1) (v : V × V) :
    controlQuad (fun c b => pairedCoefficientAction N h t0 t1 c b v) ∈
      augmentationImage (pairedAugmentation N) (2 ^ (j + 1)) := by
  apply (pairedAugmentationImage_iff N (2 ^ (j + 1)) _).mpr
  constructor
  · simpa only [controlQuad, pairedCoefficientAction, LinearMap.prodMap_apply,
      Prod.fst_add] using matrixCoefficientAction_quadratic_mem N hj hN t0 ht0 v.1
  · simpa only [controlQuad, pairedCoefficientAction, LinearMap.prodMap_apply,
      Prod.snd_add] using matrixCoefficientAction_quadratic_mem N hj hN t1 ht1 v.2

end PairedMatrixImage

end QuantumProver.ControlledCliffordHierarchy

open scoped Matrix BigOperators

namespace QuantumProver.ControlledCliffordHierarchy

section MatrixFullLabelStep

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

theorem labelVector_neg_eq_self (v : V) : -v = v := by
  rw [neg_eq_iff_add_eq_zero]
  exact module_charTwo_add_self v

def pairedCoefficientConstantAction (N : Module.End (ZMod 2) V) (h : ℕ)
    (t0 t1 : ControlExponentCoefficients) (a : ControlExponentShift) :
    Module.End (ZMod 2) (V × V) :=
  pairedResidualLabelAction N h (-controlExponentFunction t0 a) (-controlExponentFunction t1 a)

def pairedCoefficientDifference (N : Module.End (ZMod 2) V) (h : ℕ)
    (t0 t1 : ControlExponentCoefficients) (a : ControlExponentShift)
    (c b : ZMod 2) : Module.End (ZMod 2) (V × V) :=
  pairedResidualLabelAction N h
    (controlExponentFunction t0 (c, b) - controlExponentFunction t0 ((c, b) + a))
    (controlExponentFunction t1 (c, b) - controlExponentFunction t1 ((c, b) + a))

theorem pairedCoefficientDifference_factor (N : Module.End (ZMod 2) V) (h : ℕ)
    (hN : N ^ (2 ^ h) = 0) (t0 t1 : ControlExponentCoefficients)
    (a : ControlExponentShift) (c b : ZMod 2) :
    pairedCoefficientDifference N h t0 t1 a c b =
      pairedCoefficientAction N h (controlExponentStep t0 a) (controlExponentStep t1 a) c b *
        pairedCoefficientConstantAction N h t0 t1 a := by
  have hdiff (t : ControlExponentCoefficients) :
      controlExponentFunction t (c, b) - controlExponentFunction t ((c, b) + a) =
        controlExponentFunction (controlExponentStep t a) (c, b) - controlExponentFunction t a := by
    have hs := congrFun (controlExponentStep_function t a) (c, b)
    dsimp only [controlExponentFunctionStep] at hs
    omega
  unfold pairedCoefficientDifference
  rw [hdiff t0, hdiff t1, sub_eq_add_neg, sub_eq_add_neg,
    pairedResidualLabelAction_add N h hN]
  rfl

theorem pairedCoefficientDifference_delta (N : Module.End (ZMod 2) V) (h : ℕ)
    (hN : N ^ (2 ^ h) = 0) (t0 t1 : ControlExponentCoefficients)
    (a : ControlExponentShift) (c b : ZMod 2) :
    pairedCoefficientDifference N h t0 t1 a c b - pairedCoefficientConstantAction N h t0 t1 a =
      (pairedCoefficientAction N h (controlExponentStep t0 a) (controlExponentStep t1 a) c b - 1) *
        pairedCoefficientConstantAction N h t0 t1 a := by
  rw [pairedCoefficientDifference_factor N h hN]
  rw [sub_mul, one_mul]

theorem pairedCoefficientConstantAction_raises (N : Module.End (ZMod 2) V)
    {h j : ℕ} (hj : j + 1 ≤ h) (t0 t1 : ControlExponentCoefficients)
    (ht0 : controlExponentDepth j t0) (ht1 : controlExponentDepth j t1)
    (a : ControlExponentShift) {v : V × V}
    (hv : v ∈ augmentationImage (pairedAugmentation N) (2 ^ j)) :
    v + pairedCoefficientConstantAction N h t0 t1 a v ∈
      augmentationImage (pairedAugmentation N) (2 ^ (j + 1)) := by
  have hd0 : ((2 ^ j : ℕ) : ℤ) ∣ -controlExponentFunction t0 a :=
    dvd_neg.mpr (matrixCoefficient_depth_value ht0 a)
  have hd1 : ((2 ^ j : ℕ) : ℤ) ∣ -controlExponentFunction t1 a :=
    dvd_neg.mpr (matrixCoefficient_depth_value ht1 a)
  have he : 2 ^ j + 2 ^ j = 2 ^ (j + 1) := by
    simp only [Nat.pow_succ, Nat.mul_comm, two_mul]
  have hr := pairedResidualLabelAction_difference_raise N (show j ≤ h by omega)
    (2 ^ j) (-controlExponentFunction t0 a) (-controlExponentFunction t1 a) hd0 hd1 hv
  simpa only [he, LinearMap.sub_apply, LinearMap.add_apply, Module.End.one_apply, sub_eq_add_neg,
    labelVector_neg_eq_self, add_comm, pairedCoefficientConstantAction] using hr

theorem pairedCoefficientDifference_delta_mem (N : Module.End (ZMod 2) V)
    {h j : ℕ} (hj : j + 1 ≤ h) (hN : N ^ (2 ^ h) = 0)
    (t0 t1 : ControlExponentCoefficients)
    (ht0 : controlExponentDepth j t0) (ht1 : controlExponentDepth j t1)
    (a : ControlExponentShift) (c b : ZMod 2) (v : V × V) :
    (pairedCoefficientDifference N h t0 t1 a c b -
      pairedCoefficientConstantAction N h t0 t1 a) v ∈
        augmentationImage (pairedAugmentation N) (2 ^ (j + 1)) := by
  rw [pairedCoefficientDifference_delta N h hN]
  have hn0 := controlExponentStep_depth j t0 a ht0
  have hn1 := controlExponentStep_depth j t1 a ht1
  have hd0 := matrixCoefficient_depth_value hn0 (c, b)
  have hd1 := matrixCoefficient_depth_value hn1 (c, b)
  exact pairedResidualLabelAction_difference_full_image N hj
    (controlExponentFunction (controlExponentStep t0 a) (c, b))
    (controlExponentFunction (controlExponentStep t1 a) (c, b)) hd0 hd1
    (pairedCoefficientConstantAction N h t0 t1 a v)

theorem pairedCoefficient_labelProfileStep_mem (N : Module.End (ZMod 2) V)
    {h j : ℕ} (hj : j + 1 ≤ h) (hN : N ^ (2 ^ h) = 0)
    (t0 t1 : ControlExponentCoefficients)
    (ht0 : controlExponentDepth j t0) (ht1 : controlExponentDepth j t1)
    (y : ZMod 2 → ZMod 2 → V × V)
    (hy : controlQuad y ∈ augmentationImage (pairedAugmentation N) (2 ^ j))
    (ac ab : ZMod 2) (p : V × V) :
    controlQuad (labelProfileStep y (pairedCoefficientAction N h t0 t1)
      (pairedCoefficientDifference N h t0 t1 (ac, ab)) ac ab p) ∈
        augmentationImage (pairedAugmentation N) (2 ^ (j + 1)) := by
  apply labelProfileStep_quad_mem (augmentationImage (pairedAugmentation N) (2 ^ j))
    (augmentationImage (pairedAugmentation N) (2 ^ (j + 1))) y
    (pairedCoefficientAction N h t0 t1) (pairedCoefficientDifference N h t0 t1 (ac, ab))
    (pairedCoefficientConstantAction N h t0 t1 (ac, ab)) hy
  · intro v hv
    exact pairedCoefficientConstantAction_raises N hj t0 t1 ht0 ht1 (ac, ab) hv
  · intro c b v
    exact pairedCoefficientDifference_delta_mem N hj hN t0 t1 ht0 ht1 (ac, ab) c b v
  · exact pairedCoefficientAction_quadratic_mem N hj hN t0 t1 ht0 ht1

end MatrixFullLabelStep

end QuantumProver.ControlledCliffordHierarchy

open scoped Matrix BigOperators

namespace QuantumProver.ControlledCliffordHierarchy

def matrixIntegerPowerLabel {n : ℕ} (F : Module.End (ZMod 2) (PauliLabel n))
    (q : ℕ) (t : ℤ) : Module.End (ZMod 2) (PauliLabel n) :=
  F ^ matrixPowerResidual q t

def matrixIntegerAbsorbedLabel {n : ℕ} (p : PauliLabel n) (q : ℕ) (t : ℤ) :
    PauliLabel n := ((t / (q : ℤ) : ℤ) : ZMod 2) • p

def matrixIntegerPowerSign {n : ℕ} (F : Module.End (ZMod 2) (PauliLabel n))
    (k : ℕ → PauliLabel n → ZMod 2) (pq : PauliLabel n) (q : ℕ) (t : ℤ)
    (p : PauliLabel n) : ZMod 2 :=
  k (matrixPowerResidual q t) p +
    dot (matrixIntegerAbsorbedLabel pq q t).2 (matrixIntegerPowerLabel F q t p).1 +
    dot (matrixIntegerPowerLabel F q t p).2 (matrixIntegerAbsorbedLabel pq q t).1

theorem matrixZpow_full_signed_action {n q : ℕ} {T : MatrixUnitary n}
    (hq : 0 < q) (sq : ZMod 2) (pq : PauliLabel n)
    (hp : ((T ^ q : MatrixUnitary n) : QuantumMatrix n) = signedOrderedPauli sq pq)
    (hHerm : dot pq.2 pq.1 = 0)
    (F : Module.End (ZMod 2) (PauliLabel n)) (k : ℕ → PauliLabel n → ZMod 2)
    (hNat : ∀ r p, conjugate ((T : QuantumMatrix n) ^ r) (orderedPauli p.1 p.2) =
      bitSign (k r p) • orderedPauli ((F ^ r) p).1 ((F ^ r) p).2)
    (t : ℤ) (p : PauliLabel n) :
    conjugate (matrixZpow T t) (orderedPauli p.1 p.2) =
      bitSign (matrixIntegerPowerSign F k pq q t p) •
        orderedPauli (matrixIntegerPowerLabel F q t p).1 (matrixIntegerPowerLabel F q t p).2 := by
  rw [matrixZpow_absorb_natResidual hq sq pq hp hHerm, conjugate_comp, hNat,
    conjugate_smul_right, signedOrderedPauli_conjugate_ordered, smul_smul, ← bitSign_add]
  simp only [matrixIntegerPowerSign, matrixIntegerPowerLabel, matrixIntegerAbsorbedLabel,
    add_assoc]

theorem matrixZpow_full_phased_action {n q : ℕ} {T : MatrixUnitary n}
    (hq : 0 < q) (sq : ZMod 2) (pq : PauliLabel n)
    (hp : ((T ^ q : MatrixUnitary n) : QuantumMatrix n) = signedOrderedPauli sq pq)
    (hHerm : dot pq.2 pq.1 = 0)
    (F : Module.End (ZMod 2) (PauliLabel n)) (k : ℕ → PauliLabel n → ZMod 2)
    (hNat : ∀ r p, conjugate ((T : QuantumMatrix n) ^ r) (orderedPauli p.1 p.2) =
      bitSign (k r p) • orderedPauli ((F ^ r) p).1 ((F ^ r) p).2)
    (t : ℤ) (p : PauliLabel n) (a : ℂ) :
    conjugate (matrixZpow T t) (a • orderedPauli p.1 p.2) =
      (a * bitSign (matrixIntegerPowerSign F k pq q t p)) •
        orderedPauli (matrixIntegerPowerLabel F q t p).1 (matrixIntegerPowerLabel F q t p).2 := by
  rw [conjugate_smul_right, matrixZpow_full_signed_action hq sq pq hp hHerm F k hNat, smul_smul]

def matrixIntegerPairSign {n : ℕ}
    (L0 L1 : ℤ → Module.End (ZMod 2) (PauliLabel n))
    (k0 k1 : ℤ → PauliLabel n → ZMod 2) (t0 t1 : ℤ) (p : PauliLabel n) : ZMod 2 :=
  k1 t1 p + k0 t0 (L1 t1 p)

theorem matrixZpow_pair_full_signed_action {n : ℕ} (T0 T1 : MatrixUnitary n)
    (L0 L1 : ℤ → Module.End (ZMod 2) (PauliLabel n))
    (k0 k1 : ℤ → PauliLabel n → ZMod 2)
    (h0 : ∀ t p, conjugate (matrixZpow T0 t) (orderedPauli p.1 p.2) =
      bitSign (k0 t p) • orderedPauli (L0 t p).1 (L0 t p).2)
    (h1 : ∀ t p, conjugate (matrixZpow T1 t) (orderedPauli p.1 p.2) =
      bitSign (k1 t p) • orderedPauli (L1 t p).1 (L1 t p).2)
    (t0 t1 : ℤ) (p : PauliLabel n) :
    conjugate (matrixZpow T0 t0 * matrixZpow T1 t1) (orderedPauli p.1 p.2) =
      bitSign (matrixIntegerPairSign L0 L1 k0 k1 t0 t1 p) •
        orderedPauli ((L0 t0 * L1 t1) p).1 ((L0 t0 * L1 t1) p).2 := by
  rw [conjugate_comp, h1, conjugate_smul_right, h0, smul_smul, ← bitSign_add]
  rfl

theorem matrixShiftProfile_full_signed_action {n : ℕ} (T0 T1 : MatrixUnitary n)
    (L0 L1 : ℤ → Module.End (ZMod 2) (PauliLabel n))
    (k0 k1 : ℤ → PauliLabel n → ZMod 2)
    (h0 : ∀ t p, conjugate (matrixZpow T0 t) (orderedPauli p.1 p.2) =
      bitSign (k0 t p) • orderedPauli (L0 t p).1 (L0 t p).2)
    (h1 : ∀ t p, conjugate (matrixZpow T1 t) (orderedPauli p.1 p.2) =
      bitSign (k1 t p) • orderedPauli (L1 t p).1 (L1 t p).2)
    (t0 t1 : ZMod 2 → ZMod 2 → ℤ) (c b : ZMod 2) (p : PauliLabel n) :
    conjugate (matrixShiftProfile T0 T1 t0 t1 c b) (orderedPauli p.1 p.2) =
      bitSign (matrixIntegerPairSign L0 L1 k0 k1 (t0 c b) (t1 c b) p) •
        orderedPauli ((L0 (t0 c b) * L1 (t1 c b)) p).1
          ((L0 (t0 c b) * L1 (t1 c b)) p).2 :=
  matrixZpow_pair_full_signed_action T0 T1 L0 L1 k0 k1 h0 h1 (t0 c b) (t1 c b) p

theorem matrixShiftProfile_difference_full_signed_action {n : ℕ} {T0 T1 : MatrixUnitary n}
    (hcomm : Commute T0 T1)
    (L0 L1 : ℤ → Module.End (ZMod 2) (PauliLabel n))
    (k0 k1 : ℤ → PauliLabel n → ZMod 2)
    (h0 : ∀ t p, conjugate (matrixZpow T0 t) (orderedPauli p.1 p.2) =
      bitSign (k0 t p) • orderedPauli (L0 t p).1 (L0 t p).2)
    (h1 : ∀ t p, conjugate (matrixZpow T1 t) (orderedPauli p.1 p.2) =
      bitSign (k1 t p) • orderedPauli (L1 t p).1 (L1 t p).2)
    (t0 t1 : ZMod 2 → ZMod 2 → ℤ) (ac ab c b : ZMod 2) (p : PauliLabel n) :
    conjugate (matrixProfileDifference (matrixShiftProfile T0 T1 t0 t1) ac ab c b)
      (orderedPauli p.1 p.2) =
      bitSign (matrixIntegerPairSign L0 L1 k0 k1
        (t0 c b - t0 (c + ac) (b + ab)) (t1 c b - t1 (c + ac) (b + ab)) p) •
        orderedPauli
          ((L0 (t0 c b - t0 (c + ac) (b + ab)) * L1 (t1 c b - t1 (c + ac) (b + ab))) p).1
          ((L0 (t0 c b - t0 (c + ac) (b + ab)) * L1 (t1 c b - t1 (c + ac) (b + ab))) p).2 := by
  rw [matrixProfileDifference, matrixShiftProfile_difference hcomm]
  exact matrixZpow_pair_full_signed_action T0 T1 L0 L1 k0 k1 h0 h1 _ _ p

theorem hierarchy_clifford_matrixZpow {n : ℕ} {T : MatrixUnitary n}
    (hT : hierarchy n 2 (T : QuantumMatrix n)) (t : ℤ) : hierarchy n 2 (matrixZpow T t) := by
  have hn (r : ℕ) : hierarchy n 2 ((T : QuantumMatrix n) ^ r) := by
    induction r with
    | zero => simpa only [pow_zero] using actualPauli_hierarchy (by omega) (actualPauli_one n)
    | succ r ih =>
      rw [pow_succ]
      exact hierarchy_clifford_mul_right (by omega) hT ih
  cases t with
  | ofNat r =>
    change hierarchy n 2 (matrixZpow T (r : ℤ))
    rw [matrixZpow_nat]
    exact hn r
  | negSucc r =>
    change hierarchy n 2 (matrixZpow T (-((r + 1 : ℕ) : ℤ)))
    rw [matrixZpow_neg, matrixZpow_nat]
    exact clifford_conjTranspose (hn (r + 1))

theorem matrixShiftProfile_constant_clifford {n : ℕ} {T0 T1 : MatrixUnitary n}
    (hT0 : hierarchy n 2 (T0 : QuantumMatrix n)) (hT1 : hierarchy n 2 (T1 : QuantumMatrix n))
    (a b : ℤ) : hierarchy n 2 (matrixZpow T0 a * matrixZpow T1 b) :=
  hierarchy_clifford_mul_left (by omega) (hierarchy_clifford_matrixZpow hT0 a)
    (hierarchy_clifford_matrixZpow hT1 b)

end QuantumProver.ControlledCliffordHierarchy

open scoped Matrix BigOperators

namespace QuantumProver.ControlledCliffordHierarchy

def matrixCoefficientProfile {n : ℕ} (T0 T1 : MatrixUnitary n)
    (t0 t1 : ControlExponentCoefficients) : ZMod 2 → ZMod 2 → QuantumMatrix n :=
  matrixShiftProfile T0 T1 (fun c b => controlExponentFunction t0 (c, b))
    (fun c b => controlExponentFunction t1 (c, b))

def matrixCoefficientPauliAction {n : ℕ}
    (L0 L1 : ℤ → Module.End (ZMod 2) (PauliLabel n))
    (t0 t1 : ControlExponentCoefficients) (c b : ZMod 2) : Module.End (ZMod 2) (PauliLabel n) :=
  L0 (controlExponentFunction t0 (c, b)) * L1 (controlExponentFunction t1 (c, b))

def matrixCoefficientPauliSign {n : ℕ}
    (L0 L1 : ℤ → Module.End (ZMod 2) (PauliLabel n))
    (k0 k1 : ℤ → PauliLabel n → ZMod 2)
    (t0 t1 : ControlExponentCoefficients) (c b : ZMod 2) (p : PauliLabel n) : ZMod 2 :=
  matrixIntegerPairSign L0 L1 k0 k1 (controlExponentFunction t0 (c, b))
    (controlExponentFunction t1 (c, b)) p

def matrixCoefficientDifferencePauliAction {n : ℕ}
    (L0 L1 : ℤ → Module.End (ZMod 2) (PauliLabel n))
    (t0 t1 : ControlExponentCoefficients) (ac ab c b : ZMod 2) :
    Module.End (ZMod 2) (PauliLabel n) :=
  L0 (controlExponentFunction t0 (c, b) - controlExponentFunction t0 (c + ac, b + ab)) *
    L1 (controlExponentFunction t1 (c, b) - controlExponentFunction t1 (c + ac, b + ab))

def matrixCoefficientDifferencePauliSign {n : ℕ}
    (L0 L1 : ℤ → Module.End (ZMod 2) (PauliLabel n))
    (k0 k1 : ℤ → PauliLabel n → ZMod 2)
    (t0 t1 : ControlExponentCoefficients) (ac ab c b : ZMod 2) (p : PauliLabel n) : ZMod 2 :=
  matrixIntegerPairSign L0 L1 k0 k1
    (controlExponentFunction t0 (c, b) - controlExponentFunction t0 (c + ac, b + ab))
    (controlExponentFunction t1 (c, b) - controlExponentFunction t1 (c + ac, b + ab)) p

def matrixCoefficientNextLabel {n : ℕ}
    (y : ZMod 2 → ZMod 2 → PauliLabel n)
    (L0 L1 : ℤ → Module.End (ZMod 2) (PauliLabel n))
    (t0 t1 : ControlExponentCoefficients) (ac ab : ZMod 2) (p : PauliLabel n) :=
  labelProfileStep y (matrixCoefficientPauliAction L0 L1 t0 t1)
    (matrixCoefficientDifferencePauliAction L0 L1 t0 t1 ac ab) ac ab p

def matrixCoefficientNextSign {n : ℕ}
    (s : ZMod 2 → ZMod 2 → ZMod 2) (y : ZMod 2 → ZMod 2 → PauliLabel n)
    (L0 L1 : ℤ → Module.End (ZMod 2) (PauliLabel n))
    (k0 k1 : ℤ → PauliLabel n → ZMod 2)
    (t0 t1 : ControlExponentCoefficients) (ac ab : ZMod 2) (p : PauliLabel n) :=
  matrixProfileNextSign s y (matrixCoefficientPauliAction L0 L1 t0 t1)
    (matrixCoefficientDifferencePauliAction L0 L1 t0 t1 ac ab)
    (matrixCoefficientPauliSign L0 L1 k0 k1 t0 t1)
    (matrixCoefficientDifferencePauliSign L0 L1 k0 k1 t0 t1 ac ab) ac ab p

theorem matrixCoefficientProfile_difference_normalized {n : ℕ} {T0 T1 : MatrixUnitary n}
    (hcomm : Commute T0 T1) (t0 t1 : ControlExponentCoefficients)
    (ac ab c b : ZMod 2) :
    matrixProfileDifference (matrixCoefficientProfile T0 T1 t0 t1) ac ab c b =
      matrixCoefficientProfile T0 T1 (controlExponentStep t0 (ac, ab))
        (controlExponentStep t1 (ac, ab)) c b *
          (matrixCoefficientProfile T0 T1 t0 t1 ac ab).conjTranspose := by
  have hu : unitaryMatrix (matrixCoefficientProfile T0 T1 t0 t1 ac ab) :=
    matrixShiftProfile_unitary _ _ _ _ ac ab
  have hn : matrixProfileDifference (matrixCoefficientProfile T0 T1 t0 t1) ac ab c b *
      matrixCoefficientProfile T0 T1 t0 t1 ac ab =
        matrixCoefficientProfile T0 T1 (controlExponentStep t0 (ac, ab))
          (controlExponentStep t1 (ac, ab)) c b := by
    simpa only [matrixCoefficientProfile, matrixProfileDifference] using
      matrixShiftProfile_coefficient_step hcomm t0 t1 ac ab c b
  calc
    matrixProfileDifference (matrixCoefficientProfile T0 T1 t0 t1) ac ab c b =
        matrixProfileDifference (matrixCoefficientProfile T0 T1 t0 t1) ac ab c b *
          (matrixCoefficientProfile T0 T1 t0 t1 ac ab *
            (matrixCoefficientProfile T0 T1 t0 t1 ac ab).conjTranspose) := by
      rw [hu.2, mul_one]
    _ = _ := by rw [← mul_assoc, hn]

theorem matrixCoefficientProfile_signed_correction {n : ℕ} {T0 T1 : MatrixUnitary n}
    (hcomm : Commute T0 T1)
    (L0 L1 : ℤ → Module.End (ZMod 2) (PauliLabel n))
    (k0 k1 : ℤ → PauliLabel n → ZMod 2)
    (h0 : ∀ t p, conjugate (matrixZpow T0 t) (orderedPauli p.1 p.2) =
      bitSign (k0 t p) • orderedPauli (L0 t p).1 (L0 t p).2)
    (h1 : ∀ t p, conjugate (matrixZpow T1 t) (orderedPauli p.1 p.2) =
      bitSign (k1 t p) • orderedPauli (L1 t p).1 (L1 t p).2)
    (s : ZMod 2 → ZMod 2 → ZMod 2) (y : ZMod 2 → ZMod 2 → PauliLabel n)
    (t0 t1 : ControlExponentCoefficients) (ac ab : ZMod 2) (p : PauliLabel n) :
    twoControlCorrectionProfile (signedMatrixProfileWord s y (matrixCoefficientProfile T0 T1 t0 t1))
      ac ab (orderedPauli p.1 p.2) =
      (fun c b => signedMatrixProfileWord
        (matrixCoefficientNextSign s y L0 L1 k0 k1 t0 t1 ac ab p)
        (matrixCoefficientNextLabel y L0 L1 t0 t1 ac ab p)
        (matrixCoefficientProfile T0 T1 (controlExponentStep t0 (ac, ab))
          (controlExponentStep t1 (ac, ab))) c b *
            (matrixCoefficientProfile T0 T1 t0 t1 ac ab).conjTranspose) := by
  have hF : ∀ c b p, conjugate (matrixCoefficientProfile T0 T1 t0 t1 c b)
      (orderedPauli p.1 p.2) = bitSign (matrixCoefficientPauliSign L0 L1 k0 k1 t0 t1 c b p) •
        orderedPauli (matrixCoefficientPauliAction L0 L1 t0 t1 c b p).1
          (matrixCoefficientPauliAction L0 L1 t0 t1 c b p).2 :=
    matrixShiftProfile_full_signed_action T0 T1 L0 L1 k0 k1 h0 h1 _ _
  have hG : ∀ c b p, conjugate
      (matrixProfileDifference (matrixCoefficientProfile T0 T1 t0 t1) ac ab c b)
      (orderedPauli p.1 p.2) =
      bitSign (matrixCoefficientDifferencePauliSign L0 L1 k0 k1 t0 t1 ac ab c b p) •
        orderedPauli (matrixCoefficientDifferencePauliAction L0 L1 t0 t1 ac ab c b p).1
          (matrixCoefficientDifferencePauliAction L0 L1 t0 t1 ac ab c b p).2 :=
    matrixShiftProfile_difference_full_signed_action hcomm L0 L1 k0 k1 h0 h1 _ _ ac ab
  rw [signedMatrixProfile_correction s y (matrixCoefficientProfile T0 T1 t0 t1)
    (matrixCoefficientPauliAction L0 L1 t0 t1)
    (matrixCoefficientDifferencePauliAction L0 L1 t0 t1 ac ab)
    (matrixCoefficientPauliSign L0 L1 k0 k1 t0 t1)
    (matrixCoefficientDifferencePauliSign L0 L1 k0 k1 t0 t1 ac ab) ac ab
    (matrixShiftProfile_unitary _ _ _ _) hF hG p]
  funext c b
  change signedOrderedPauli _ _ *
    matrixProfileDifference (matrixCoefficientProfile T0 T1 t0 t1) ac ab c b = _
  rw [matrixCoefficientProfile_difference_normalized hcomm t0 t1 ac ab c b, ← mul_assoc]
  rfl

theorem matrixCoefficientProfile_actualPauli_correction {n : ℕ} {T0 T1 : MatrixUnitary n}
    (hcomm : Commute T0 T1)
    (L0 L1 : ℤ → Module.End (ZMod 2) (PauliLabel n))
    (k0 k1 : ℤ → PauliLabel n → ZMod 2)
    (h0 : ∀ t p, conjugate (matrixZpow T0 t) (orderedPauli p.1 p.2) =
      bitSign (k0 t p) • orderedPauli (L0 t p).1 (L0 t p).2)
    (h1 : ∀ t p, conjugate (matrixZpow T1 t) (orderedPauli p.1 p.2) =
      bitSign (k1 t p) • orderedPauli (L1 t p).1 (L1 t p).2)
    (s : ZMod 2 → ZMod 2 → ZMod 2) (y : ZMod 2 → ZMod 2 → PauliLabel n)
    (t0 t1 : ControlExponentCoefficients) (ac ab zc zb : ZMod 2) (x z : BitString n)
    {a : ℂ} (ha : PauliPhase a) :
    pauliCorrection (twoControlMatrix (signedMatrixProfileWord s y (matrixCoefficientProfile T0 T1 t0 t1)))
      (a • orderedPauli (basisCons ac (basisCons ab x)) (basisCons zc (basisCons zb z))) =
      twoControlMatrix (signedMatrixProfileWord
        (matrixCoefficientNextSign s y L0 L1 k0 k1 t0 t1 ac ab (x, z))
        (matrixCoefficientNextLabel y L0 L1 t0 t1 ac ab (x, z))
        (matrixCoefficientProfile T0 T1 (controlExponentStep t0 (ac, ab))
          (controlExponentStep t1 (ac, ab)))) *
        twoControlMatrix (fun _ _ => (matrixCoefficientProfile T0 T1 t0 t1 ac ab).conjTranspose) := by
  rw [twoControlMatrix_actualPauli_correction _ ac ab zc zb x z ha,
    matrixCoefficientProfile_signed_correction hcomm L0 L1 k0 k1 h0 h1 s y t0 t1 ac ab (x, z),
    ← twoControlMatrix_mul]

theorem matrixCoefficientProfile_normalization_clifford {n : ℕ} {T0 T1 : MatrixUnitary n}
    (hT0 : hierarchy n 2 (T0 : QuantumMatrix n)) (hT1 : hierarchy n 2 (T1 : QuantumMatrix n))
    (t0 t1 : ControlExponentCoefficients) (ac ab : ZMod 2) :
    hierarchy ((n + 1) + 1) 2
      (twoControlMatrix (fun _ _ => (matrixCoefficientProfile T0 T1 t0 t1 ac ab).conjTranspose)) := by
  have hC : hierarchy n 2 (matrixCoefficientProfile T0 T1 t0 t1 ac ab) :=
    matrixShiftProfile_constant_clifford hT0 hT1
      (controlExponentFunction t0 (ac, ab)) (controlExponentFunction t1 (ac, ab))
  exact hierarchy_lift (by omega) (hierarchy_lift (by omega) (clifford_conjTranspose hC))

end QuantumProver.ControlledCliffordHierarchy

open scoped Matrix BigOperators

namespace QuantumProver.ControlledCliffordHierarchy

def matrixGroupProfileNormalized {n : ℕ}
    (F : ZMod 2 → ZMod 2 → MatrixUnitary n) (ac ab c b : ZMod 2) : MatrixUnitary n :=
  F c b * (F (c + ac) (b + ab))⁻¹ * F ac ab

def matrixSelectorWord {n : ℕ} (S T1 : MatrixUnitary n) (c b : ZMod 2) : MatrixUnitary n :=
  if c = 0 then 1 else if b = 0 then S else T1 * S⁻¹

theorem matrixQuarterTurn_cube {n : ℕ} {S : MatrixUnitary n} (hS4 : S ^ (4 : ℕ) = 1) :
    S ^ (3 : ℕ) = S⁻¹ := by
  calc
    S ^ (3 : ℕ) = (S ^ (3 : ℕ) * S) * S⁻¹ := by first | (simp only [pow_two] <;> group) | group
    _ = S ^ (4 : ℕ) * S⁻¹ := by rw [← pow_succ]
    _ = S⁻¹ := by rw [hS4, one_mul]

theorem matrixSelectorWord_unreduced {n : ℕ} {S : MatrixUnitary n}
    (T1 : MatrixUnitary n) (hS4 : S ^ (4 : ℕ) = 1) (c b : ZMod 2) :
    matrixSelectorWord S T1 c b =
      (if c = 0 then 1 else if b = 0 then S else T1 * S ^ (3 : ℕ)) := by
  rw [matrixQuarterTurn_cube hS4]
  rfl

theorem matrixQuarterTurn_square_inv {n : ℕ} {S : MatrixUnitary n}
    (hS4 : S ^ (4 : ℕ) = 1) : (S ^ (2 : ℕ))⁻¹ = S ^ (2 : ℕ) := by
  have hsq : S ^ (2 : ℕ) * S ^ (2 : ℕ) = 1 := by
    simpa only [← pow_add] using hS4
  calc
    (S ^ (2 : ℕ))⁻¹ = (S ^ (2 : ℕ))⁻¹ * 1 := by rw [mul_one]
    _ = (S ^ (2 : ℕ))⁻¹ * (S ^ (2 : ℕ) * S ^ (2 : ℕ)) := by rw [hsq]
    _ = S ^ (2 : ℕ) := by rw [← mul_assoc, inv_mul_cancel, one_mul]

theorem matrixQuarterTurn_relations {n : ℕ} {S T0 T1 : MatrixUnitary n}
    (h0 : S * T0 * S⁻¹ = T1) (h1 : S * T1 * S⁻¹ = T0⁻¹) :
    S⁻¹ * T1 = T0 * S⁻¹ ∧ S * T1⁻¹ = T0 * S ∧
      S ^ (2 : ℕ) * T1⁻¹ = T1 * S ^ (2 : ℕ) := by
  have hi : S * T1⁻¹ * S⁻¹ = T0 := by
    simpa only [mul_inv_rev, inv_inv, mul_assoc] using congrArg (fun U : MatrixUnitary n => U⁻¹) h1
  refine ⟨?_, ?_, ?_⟩
  · calc
      S⁻¹ * T1 = S⁻¹ * (S * T0 * S⁻¹) := by rw [h0]
      _ = T0 * S⁻¹ := by first | (simp only [pow_two] <;> group) | group
  · calc
      S * T1⁻¹ = (S * T1⁻¹ * S⁻¹) * S := by first | (simp only [pow_two] <;> group) | group
      _ = T0 * S := by rw [hi]
  · calc
      S ^ (2 : ℕ) * T1⁻¹ = (S * (S * T1⁻¹ * S⁻¹) * S⁻¹) * S ^ (2 : ℕ) := by first | (simp only [pow_two] <;> group) | group
      _ = (S * T0 * S⁻¹) * S ^ (2 : ℕ) := by rw [hi]
      _ = T1 * S ^ (2 : ℕ) := by rw [h0]

theorem matrixSelectorFirst_00 {n : ℕ} (S T1 : MatrixUnitary n) (c b : ZMod 2) :
    matrixGroupProfileNormalized (matrixSelectorWord S T1) 0 0 c b = 1 := by
  simp [matrixGroupProfileNormalized, matrixSelectorWord]

theorem matrixSelectorFirst_01 {n : ℕ} {S T0 T1 : MatrixUnitary n}
    (hS4 : S ^ (4 : ℕ) = 1)
    (h0 : S * T0 * S⁻¹ = T1) (h1 : S * T1 * S⁻¹ = T0⁻¹)
    (c b : ZMod 2) :
    matrixGroupProfileNormalized (matrixSelectorWord S T1) 0 1 c b =
      (if c = 0 then 1 else T1 * S ^ (2 : ℕ)) := by
  obtain ⟨_, _, hS2⟩ := matrixQuarterTurn_relations h0 h1
  rcases physical_control_bit_cases c with rfl | rfl
  · rcases physical_control_bit_cases b with rfl | rfl <;>
      simp [matrixGroupProfileNormalized, matrixSelectorWord]
  · rcases physical_control_bit_cases b with rfl | rfl
    · change S * (T1 * S⁻¹)⁻¹ * 1 = T1 * S ^ (2 : ℕ)
      calc
        S * (T1 * S⁻¹)⁻¹ * 1 = S ^ (2 : ℕ) * T1⁻¹ := by first | (simp only [pow_two] <;> group) | group
        _ = T1 * S ^ (2 : ℕ) := hS2
    · change (T1 * S⁻¹) * S⁻¹ * 1 = T1 * S ^ (2 : ℕ)
      calc
        (T1 * S⁻¹) * S⁻¹ * 1 = T1 * (S ^ (2 : ℕ))⁻¹ := by first | (simp only [pow_two] <;> group) | group
        _ = T1 * S ^ (2 : ℕ) := by rw [matrixQuarterTurn_square_inv hS4]

theorem matrixSelectorFirst_10 {n : ℕ} {S T0 T1 : MatrixUnitary n}
    (h0 : S * T0 * S⁻¹ = T1) (h1 : S * T1 * S⁻¹ = T0⁻¹)
    (c b : ZMod 2) :
    matrixGroupProfileNormalized (matrixSelectorWord S T1) 1 0 c b =
      (if c = 0 then if b = 0 then 1 else T0 * S ^ (2 : ℕ)
        else if b = 0 then S ^ (2 : ℕ) else T1) := by
  obtain ⟨_, hSinv, _⟩ := matrixQuarterTurn_relations h0 h1
  rcases physical_control_bit_cases c with rfl | rfl <;>
    rcases physical_control_bit_cases b with rfl | rfl
  · change 1 * S⁻¹ * S = 1
    first | (simp only [pow_two] <;> group) | group
  · change 1 * (T1 * S⁻¹)⁻¹ * S = T0 * S ^ (2 : ℕ)
    calc
      1 * (T1 * S⁻¹)⁻¹ * S = (S * T1⁻¹) * S := by first | (simp only [pow_two] <;> group) | group
      _ = T0 * S ^ (2 : ℕ) := by rw [hSinv]; first | (simp only [pow_two] <;> group) | group
  · change S * 1⁻¹ * S = S ^ (2 : ℕ)
    first | (simp only [pow_two] <;> group) | group
  · change (T1 * S⁻¹) * 1⁻¹ * S = T1
    first | (simp only [pow_two] <;> group) | group

theorem matrixSelectorFirst_11 {n : ℕ} {S T0 T1 : MatrixUnitary n}
    (hS4 : S ^ (4 : ℕ) = 1) (hcomm : Commute T0 T1)
    (h0 : S * T0 * S⁻¹ = T1) (h1 : S * T1 * S⁻¹ = T0⁻¹)
    (c b : ZMod 2) :
    matrixGroupProfileNormalized (matrixSelectorWord S T1) 1 1 c b =
      (if c = 0 then if b = 0 then 1 else T0 * S ^ (2 : ℕ)
        else if b = 0 then T0⁻¹ else T0 * T1 * S ^ (2 : ℕ)) := by
  obtain ⟨hSinv, _, _⟩ := matrixQuarterTurn_relations h0 h1
  rcases physical_control_bit_cases c with rfl | rfl <;>
    rcases physical_control_bit_cases b with rfl | rfl
  · change 1 * (T1 * S⁻¹)⁻¹ * (T1 * S⁻¹) = 1
    first | (simp only [pow_two] <;> group) | group
  · change 1 * S⁻¹ * (T1 * S⁻¹) = T0 * S ^ (2 : ℕ)
    calc
      1 * S⁻¹ * (T1 * S⁻¹) = (S⁻¹ * T1) * S⁻¹ := by first | (simp only [pow_two] <;> group) | group
      _ = T0 * (S ^ (2 : ℕ))⁻¹ := by rw [hSinv]; first | (simp only [pow_two] <;> group) | group
      _ = T0 * S ^ (2 : ℕ) := by rw [matrixQuarterTurn_square_inv hS4]
  · change S * 1⁻¹ * (T1 * S⁻¹) = T0⁻¹
    simpa only [inv_one, mul_one, mul_assoc] using h1
  · change (T1 * S⁻¹) * 1⁻¹ * (T1 * S⁻¹) = T0 * T1 * S ^ (2 : ℕ)
    calc
      (T1 * S⁻¹) * 1⁻¹ * (T1 * S⁻¹) = T1 * (S⁻¹ * T1) * S⁻¹ := by first | (simp only [pow_two] <;> group) | group
      _ = (T1 * T0) * (S ^ (2 : ℕ))⁻¹ := by rw [hSinv]; first | (simp only [pow_two] <;> group) | group
      _ = T0 * T1 * S ^ (2 : ℕ) := by
        rw [hcomm.eq.symm, matrixQuarterTurn_square_inv hS4]

theorem matrixGroupProfileNormalized_coe {n : ℕ}
    (F : ZMod 2 → ZMod 2 → MatrixUnitary n) (ac ab c b : ZMod 2) :
    ((matrixGroupProfileNormalized F ac ab c b : MatrixUnitary n) : QuantumMatrix n) =
      (F c b : QuantumMatrix n) * (F (c + ac) (b + ab) : QuantumMatrix n).conjTranspose *
        (F ac ab : QuantumMatrix n) := by
  simp only [matrixGroupProfileNormalized, Submonoid.coe_mul, matrixUnitary_inv_coe]

end QuantumProver.ControlledCliffordHierarchy

open scoped Matrix BigOperators

namespace QuantumProver.ControlledCliffordHierarchy

def matrixInversionSign (e : ZMod 2) : ℤ := if e = 0 then 1 else -1

def matrixInvolutionBit {n : ℕ} (K : MatrixUnitary n) (e : ZMod 2) : MatrixUnitary n :=
  K ^ controlExponentBit e

theorem matrixInvolutionBit_add {n : ℕ} {K : MatrixUnitary n}
    (hK : K ^ (2 : ℕ) = 1) (e f : ZMod 2) :
    matrixInvolutionBit K (e + f) = matrixInvolutionBit K e * matrixInvolutionBit K f := by
  rcases physical_control_bit_cases e with rfl | rfl <;>
    rcases physical_control_bit_cases f with rfl | rfl <;>
    simp only [matrixInvolutionBit, add_zero, zero_add,
      show (1 + 1 : ZMod 2) = 0 by decide, controlExponentBit_zero,
      controlExponentBit_one, zpow_zero, zpow_one, one_mul, mul_one]
  simpa only [pow_two] using hK.symm

theorem matrixInvolutionBit_inv {n : ℕ} {K : MatrixUnitary n}
    (hK : K ^ (2 : ℕ) = 1) (e : ZMod 2) :
    (matrixInvolutionBit K e)⁻¹ = matrixInvolutionBit K e := by
  have hs : matrixInvolutionBit K e * matrixInvolutionBit K e = 1 := by
    rw [← matrixInvolutionBit_add hK, CharTwo.add_self_eq_zero]
    simp [matrixInvolutionBit]
  calc
    (matrixInvolutionBit K e)⁻¹ = (matrixInvolutionBit K e)⁻¹ * 1 := by rw [mul_one]
    _ = (matrixInvolutionBit K e)⁻¹ *
        (matrixInvolutionBit K e * matrixInvolutionBit K e) := by rw [hs]
    _ = matrixInvolutionBit K e := by first | (simp only [pow_two] <;> group) | group

private theorem matrixConjugation_zpow {n : ℕ} (K T : MatrixUnitary n) (r : ℤ) :
    K * T ^ r * K⁻¹ = (K * T * K⁻¹) ^ r := by
  let C : MatrixUnitary n →* MatrixUnitary n :=
    { toFun := fun U => K * U * K⁻¹
      map_one' := by first | (simp only [pow_two] <;> group) | group
      map_mul' := by intro U V; first | (simp only [pow_two] <;> group) | group }
  exact map_zpow C T r

theorem matrixInversion_shuffle {n : ℕ} {K T0 T1 : MatrixUnitary n}
    (h0 : K * T0 * K⁻¹ = T0⁻¹) (h1 : K * T1 * K⁻¹ = T1⁻¹) (a b : ℤ) :
    K * (T0 ^ a * T1 ^ b) = (T0 ^ (-a) * T1 ^ (-b)) * K := by
  calc
    K * (T0 ^ a * T1 ^ b) = (K * T0 ^ a * K⁻¹) * (K * T1 ^ b * K⁻¹) * K := by first | (simp only [pow_two] <;> group) | group
    _ = (T0 ^ (-a) * T1 ^ (-b)) * K := by
      rw [matrixConjugation_zpow, matrixConjugation_zpow, h0, h1, inv_zpow', inv_zpow']

theorem matrixInvolutionBit_shuffle {n : ℕ} {K T0 T1 : MatrixUnitary n}
    (h0 : K * T0 * K⁻¹ = T0⁻¹) (h1 : K * T1 * K⁻¹ = T1⁻¹)
    (e : ZMod 2) (a b : ℤ) :
    matrixInvolutionBit K e * (T0 ^ a * T1 ^ b) =
      (T0 ^ (matrixInversionSign e * a) * T1 ^ (matrixInversionSign e * b)) * matrixInvolutionBit K e := by
  rcases physical_control_bit_cases e with rfl | rfl
  · simp [matrixInvolutionBit, matrixInversionSign]
  · simpa only [matrixInvolutionBit, controlExponentBit_one, zpow_one,
      matrixInversionSign, one_ne_zero, ite_false, neg_one_mul] using matrixInversion_shuffle h0 h1 a b

def matrixInversionControl (rc rb c b : ZMod 2) : ZMod 2 := rc * c + rb * b

def matrixInversionProfile {n : ℕ} (T0 T1 K : MatrixUnitary n)
    (t0 t1 : ControlExponentCoefficients) (rc rb c b : ZMod 2) : MatrixUnitary n :=
  (T0 ^ controlExponentFunction t0 (c, b) * T1 ^ controlExponentFunction t1 (c, b)) *
    matrixInvolutionBit K (matrixInversionControl rc rb c b)

theorem matrixInversionProfile_normalized {n : ℕ} {T0 T1 K : MatrixUnitary n}
    (hcomm : Commute T0 T1) (hK : K ^ (2 : ℕ) = 1)
    (h0 : K * T0 * K⁻¹ = T0⁻¹) (h1 : K * T1 * K⁻¹ = T1⁻¹)
    (t0 t1 : ControlExponentCoefficients) (rc rb ac ab c b : ZMod 2) :
    matrixGroupProfileNormalized (matrixInversionProfile T0 T1 K t0 t1 rc rb) ac ab c b =
      T0 ^ (controlExponentFunction t0 (c, b) -
        matrixInversionSign (matrixInversionControl rc rb ac ab) * controlExponentFunction t0 (c + ac, b + ab) +
        matrixInversionSign (matrixInversionControl rc rb ac ab) * controlExponentFunction t0 (ac, ab)) *
      T1 ^ (controlExponentFunction t1 (c, b) -
        matrixInversionSign (matrixInversionControl rc rb ac ab) * controlExponentFunction t1 (c + ac, b + ab) +
        matrixInversionSign (matrixInversionControl rc rb ac ab) * controlExponentFunction t1 (ac, ab)) := by
  let A := fun c b => T0 ^ controlExponentFunction t0 (c, b) * T1 ^ controlExponentFunction t1 (c, b)
  let R := fun c b => matrixInvolutionBit K (matrixInversionControl rc rb c b)
  let delta := matrixInversionSign (matrixInversionControl rc rb ac ab)
  have hlin : matrixInversionControl rc rb (c + ac) (b + ab) =
      matrixInversionControl rc rb c b + matrixInversionControl rc rb ac ab := by
    unfold matrixInversionControl
    ring
  have hr : R c b * (R (c + ac) (b + ab))⁻¹ = R ac ab := by
    dsimp only [R]
    rw [matrixInvolutionBit_inv hK, ← matrixInvolutionBit_add hK, hlin,
      ← add_assoc, CharTwo.add_self_eq_zero, zero_add]
  have hRsq : R ac ab * R ac ab = 1 := by
    dsimp only [R]
    rw [← matrixInvolutionBit_add hK, CharTwo.add_self_eq_zero]
    simp [matrixInvolutionBit]
  have hinv : (A (c + ac) (b + ab))⁻¹ * A ac ab =
      T0 ^ (controlExponentFunction t0 (ac, ab) - controlExponentFunction t0 (c + ac, b + ab)) *
      T1 ^ (controlExponentFunction t1 (ac, ab) - controlExponentFunction t1 (c + ac, b + ab)) := by
    have hi := matrixUnitary_shift_difference hcomm (0 : ℤ) (0 : ℤ)
      (controlExponentFunction t0 (c + ac, b + ab)) (controlExponentFunction t1 (c + ac, b + ab))
    dsimp only [A]
    simp only [zpow_zero, one_mul, zero_sub] at hi
    rw [hi, matrixUnitary_shift_mul hcomm]
    congr 1 <;> ring
  calc
    matrixGroupProfileNormalized (matrixInversionProfile T0 T1 K t0 t1 rc rb) ac ab c b =
        A c b * (R c b * (R (c + ac) (b + ab))⁻¹) *
          ((A (c + ac) (b + ab))⁻¹ * A ac ab) * R ac ab := by
      dsimp only [matrixGroupProfileNormalized, matrixInversionProfile, A, R]
      group
    _ = A c b * (R ac ab *
          (T0 ^ (controlExponentFunction t0 (ac, ab) - controlExponentFunction t0 (c + ac, b + ab)) *
           T1 ^ (controlExponentFunction t1 (ac, ab) - controlExponentFunction t1 (c + ac, b + ab)))) * R ac ab := by
      rw [hr, hinv]
      simp only [mul_assoc]
    _ = A c b *
        (T0 ^ (delta * (controlExponentFunction t0 (ac, ab) - controlExponentFunction t0 (c + ac, b + ab))) *
         T1 ^ (delta * (controlExponentFunction t1 (ac, ab) - controlExponentFunction t1 (c + ac, b + ab)))) := by
      rw [matrixInvolutionBit_shuffle h0 h1]
      simp only [mul_assoc, R, delta] at hRsq ⊢
      rw [hRsq, mul_one]
    _ = _ := by
      rw [matrixUnitary_shift_mul hcomm]
      congr 1 <;> dsimp only [delta] <;> ring

def matrixInversionCoefficientStep (t : ControlExponentCoefficients) (delta ac ab : ℤ) :
    ControlExponentCoefficients :=
  ((1 - delta * (1 - 2 * ac)) * t.1 - delta * ab * (1 - 2 * ac) * t.2.2,
   (1 - delta * (1 - 2 * ab)) * t.2.1 - delta * ac * (1 - 2 * ab) * t.2.2,
   (1 - delta * (1 - 2 * ac) * (1 - 2 * ab)) * t.2.2)

theorem matrixInversionCoefficient_polynomial (t : ControlExponentCoefficients)
    (delta ac ab c b : ℤ) :
    controlExponentPolynomial t.1 t.2.1 t.2.2 c b -
      delta * controlExponentPolynomial t.1 t.2.1 t.2.2
        (controlExponentXor c ac) (controlExponentXor b ab) +
      delta * controlExponentPolynomial t.1 t.2.1 t.2.2 ac ab =
      controlExponentPolynomial (matrixInversionCoefficientStep t delta ac ab).1
        (matrixInversionCoefficientStep t delta ac ab).2.1
        (matrixInversionCoefficientStep t delta ac ab).2.2 c b := by
  simp only [controlExponentPolynomial, controlExponentXor, matrixInversionCoefficientStep]
  ring

theorem matrixInversionCoefficient_bit_function (t : ControlExponentCoefficients)
    (delta : ℤ) (ac ab c b : ZMod 2) :
    controlExponentFunction t (c, b) - delta * controlExponentFunction t (c + ac, b + ab) +
      delta * controlExponentFunction t (ac, ab) =
    controlExponentFunction (matrixInversionCoefficientStep t delta
      (controlExponentBit ac) (controlExponentBit ab)) (c, b) := by
  unfold controlExponentFunction
  rw [controlExponentBit_add, controlExponentBit_add]
  exact matrixInversionCoefficient_polynomial t delta _ _ _ _

theorem matrixInversionCoefficient_depth_zero (t : ControlExponentCoefficients)
    (e : ZMod 2) (ac ab : ℤ) :
    controlExponentDepth 0 (matrixInversionCoefficientStep t (matrixInversionSign e) ac ab) := by
  have hd : (2 : ℤ) ∣ 1 - matrixInversionSign e := by
    rcases physical_control_bit_cases e with rfl | rfl <;> norm_num [matrixInversionSign]
  change (1 : ℤ) ∣ _ ∧ (1 : ℤ) ∣ _ ∧ (2 : ℤ) ∣ _
  refine ⟨one_dvd _, one_dvd _, ?_⟩
  have he : (1 - matrixInversionSign e * (1 - 2 * ac) * (1 - 2 * ab)) * t.2.2 =
      (1 - matrixInversionSign e) * t.2.2 +
        2 * (matrixInversionSign e * (ac + ab - 2 * ac * ab) * t.2.2) := by ring
  change (2 : ℤ) ∣ (1 - matrixInversionSign e * (1 - 2 * ac) * (1 - 2 * ab)) * t.2.2
  rw [he]
  exact (hd.mul_right t.2.2).add ⟨_, rfl⟩

theorem matrixQuarterTurn_square_inverts {n : ℕ} {S T0 T1 : MatrixUnitary n}
    (h0 : S * T0 * S⁻¹ = T1) (h1 : S * T1 * S⁻¹ = T0⁻¹) :
    S ^ (2 : ℕ) * T0 * (S ^ (2 : ℕ))⁻¹ = T0⁻¹ ∧
      S ^ (2 : ℕ) * T1 * (S ^ (2 : ℕ))⁻¹ = T1⁻¹ := by
  have hi : S * T0⁻¹ * S⁻¹ = T1⁻¹ := by
    simpa only [mul_inv_rev, inv_inv, mul_assoc] using congrArg (fun U : MatrixUnitary n => U⁻¹) h0
  constructor
  · calc
      S ^ (2 : ℕ) * T0 * (S ^ (2 : ℕ))⁻¹ = S * (S * T0 * S⁻¹) * S⁻¹ := by first | (simp only [pow_two] <;> group) | group
      _ = S * T1 * S⁻¹ := by rw [h0]
      _ = T0⁻¹ := h1
  · calc
      S ^ (2 : ℕ) * T1 * (S ^ (2 : ℕ))⁻¹ = S * (S * T1 * S⁻¹) * S⁻¹ := by first | (simp only [pow_two] <;> group) | group
      _ = S * T0⁻¹ * S⁻¹ := by rw [h1]
      _ = T1⁻¹ := hi

end QuantumProver.ControlledCliffordHierarchy

open scoped Matrix BigOperators
namespace QuantumProver.ControlledCliffordHierarchy

def matrixSelectorFirstCoefficient0 (ac ab : ZMod 2) : ControlExponentCoefficients :=
  (-controlExponentBit ac * controlExponentBit ab,
   controlExponentBit ac,
   controlExponentBit ac * (2 * controlExponentBit ab - 1))

def matrixSelectorFirstCoefficient1 (ac ab : ZMod 2) : ControlExponentCoefficients :=
  ((1 - controlExponentBit ac) * controlExponentBit ab, 0, controlExponentBit ac)

theorem matrixSelectorFirst_inversion_profile {n : ℕ} {S T0 T1 : MatrixUnitary n}
    (hS4 : S ^ (4 : ℕ) = 1) (hcomm : Commute T0 T1)
    (h0 : S * T0 * S⁻¹ = T1) (h1 : S * T1 * S⁻¹ = T0⁻¹)
    (ac ab c b : ZMod 2) :
    matrixGroupProfileNormalized (matrixSelectorWord S T1) ac ab c b =
      matrixInversionProfile T0 T1 (S ^ (2 : ℕ))
        (matrixSelectorFirstCoefficient0 ac ab) (matrixSelectorFirstCoefficient1 ac ab)
        (ac + ab) ac c b := by
  rcases physical_control_bit_cases ac with rfl | rfl <;>
    rcases physical_control_bit_cases ab with rfl | rfl
  · rw [matrixSelectorFirst_00]
    rcases physical_control_bit_cases c with rfl | rfl <;>
      rcases physical_control_bit_cases b with rfl | rfl <;>
      norm_num [matrixInversionProfile, matrixInvolutionBit, matrixInversionControl,
        matrixSelectorFirstCoefficient0, matrixSelectorFirstCoefficient1,
        controlExponentFunction, controlExponentPolynomial, controlExponentBit_zero, controlExponentBit_one,
        show (2 : ZMod 2) = 0 by decide]
  · rw [matrixSelectorFirst_01 hS4 h0 h1]
    rcases physical_control_bit_cases c with rfl | rfl <;>
      rcases physical_control_bit_cases b with rfl | rfl <;>
      norm_num [matrixInversionProfile, matrixInvolutionBit, matrixInversionControl,
        matrixSelectorFirstCoefficient0, matrixSelectorFirstCoefficient1,
        controlExponentFunction, controlExponentPolynomial, controlExponentBit_zero, controlExponentBit_one,
        show (2 : ZMod 2) = 0 by decide]
  · rw [matrixSelectorFirst_10 h0 h1]
    rcases physical_control_bit_cases c with rfl | rfl <;>
      rcases physical_control_bit_cases b with rfl | rfl <;>
      norm_num [matrixInversionProfile, matrixInvolutionBit, matrixInversionControl,
        matrixSelectorFirstCoefficient0, matrixSelectorFirstCoefficient1,
        controlExponentFunction, controlExponentPolynomial, controlExponentBit_zero, controlExponentBit_one,
        show (2 : ZMod 2) = 0 by decide] <;>
      first | rfl | (group <;> simp [pow_two,
        show (3 : ZMod 2) = 1 by decide, controlExponentBit_one])
  · rw [matrixSelectorFirst_11 hS4 hcomm h0 h1]
    rcases physical_control_bit_cases c with rfl | rfl <;>
      rcases physical_control_bit_cases b with rfl | rfl <;>
      norm_num [matrixInversionProfile, matrixInvolutionBit, matrixInversionControl,
        matrixSelectorFirstCoefficient0, matrixSelectorFirstCoefficient1,
        controlExponentFunction, controlExponentPolynomial, controlExponentBit_zero, controlExponentBit_one,
        show (2 : ZMod 2) = 0 by decide] <;>
      first | rfl | (group <;> simp [pow_two,
        show (3 : ZMod 2) = 1 by decide, controlExponentBit_one])

def matrixSelectorSecondCoefficient (t : ControlExponentCoefficients)
    (ac0 ab0 ac1 ab1 : ZMod 2) : ControlExponentCoefficients :=
  matrixInversionCoefficientStep t
    (matrixInversionSign (matrixInversionControl (ac0 + ab0) ac0 ac1 ab1))
    (controlExponentBit ac1) (controlExponentBit ab1)

theorem matrixSelectorSecondCoefficient_depth_zero (t : ControlExponentCoefficients)
    (ac0 ab0 ac1 ab1 : ZMod 2) :
    controlExponentDepth 0 (matrixSelectorSecondCoefficient t ac0 ab0 ac1 ab1) :=
  matrixInversionCoefficient_depth_zero t _ _ _

theorem matrixSelectorSecond_shift_profile {n : ℕ} {S T0 T1 : MatrixUnitary n}
    (hS4 : S ^ (4 : ℕ) = 1) (hcomm : Commute T0 T1)
    (h0 : S * T0 * S⁻¹ = T1) (h1 : S * T1 * S⁻¹ = T0⁻¹)
    (ac0 ab0 ac1 ab1 c b : ZMod 2) :
    matrixGroupProfileNormalized
        (fun c b => matrixGroupProfileNormalized (matrixSelectorWord S T1) ac0 ab0 c b)
        ac1 ab1 c b =
      T0 ^ controlExponentFunction
        (matrixSelectorSecondCoefficient (matrixSelectorFirstCoefficient0 ac0 ab0) ac0 ab0 ac1 ab1) (c, b) *
      T1 ^ controlExponentFunction
        (matrixSelectorSecondCoefficient (matrixSelectorFirstCoefficient1 ac0 ab0) ac0 ab0 ac1 ab1) (c, b) := by
  have hfirst : (fun c b => matrixGroupProfileNormalized (matrixSelectorWord S T1) ac0 ab0 c b) =
      matrixInversionProfile T0 T1 (S ^ (2 : ℕ))
        (matrixSelectorFirstCoefficient0 ac0 ab0) (matrixSelectorFirstCoefficient1 ac0 ab0)
        (ac0 + ab0) ac0 := by
    funext c b
    exact matrixSelectorFirst_inversion_profile hS4 hcomm h0 h1 ac0 ab0 c b
  have hK : (S ^ (2 : ℕ)) ^ (2 : ℕ) = 1 := by
    simpa only [← pow_mul] using hS4
  obtain ⟨hK0, hK1⟩ := matrixQuarterTurn_square_inverts h0 h1
  rw [hfirst, matrixInversionProfile_normalized hcomm hK hK0 hK1,
    matrixInversionCoefficient_bit_function, matrixInversionCoefficient_bit_function]
  rfl

end QuantumProver.ControlledCliffordHierarchy

open scoped Matrix BigOperators
namespace QuantumProver.ControlledCliffordHierarchy
section MatrixSecondLabelEntry
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

def labelMapTrivialModulo (W : Submodule (ZMod 2) V)
    (L : Module.End (ZMod 2) V) : Prop := ∀ v, (L - 1) v ∈ W

theorem labelMapTrivialModulo_one (W : Submodule (ZMod 2) V) :
    labelMapTrivialModulo W 1 := by
  intro v
  simp only [sub_self, LinearMap.zero_apply]
  exact W.zero_mem

theorem labelMapTrivialModulo_mul (W : Submodule (ZMod 2) V)
    {L M : Module.End (ZMod 2) V}
    (hL : labelMapTrivialModulo W L) (hM : labelMapTrivialModulo W M) :
    labelMapTrivialModulo W (L * M) := by
  intro v
  have he : (L * M - 1) v = (L - 1) (M v) + (M - 1) v := by
    simp only [Module.End.mul_apply, LinearMap.sub_apply, Module.End.one_apply]
    abel
  rw [he]
  exact W.add_mem (hL (M v)) (hM v)

theorem labelMapTrivialModulo_pow (W : Submodule (ZMod 2) V)
    {L : Module.End (ZMod 2) V} (hL : labelMapTrivialModulo W L) (k : ℕ) :
    labelMapTrivialModulo W (L ^ k) := by
  induction k with
  | zero => exact labelMapTrivialModulo_one W
  | succ k ih =>
    rw [pow_succ]
    exact labelMapTrivialModulo_mul W ih hL

theorem labelMapTrivialModulo_right_inverse (W : Submodule (ZMod 2) V)
    {L M : Module.End (ZMod 2) V}
    (hL : labelMapTrivialModulo W L) (hLM : L * M = 1) :
    labelMapTrivialModulo W M := by
  intro v
  have hinv : L (M v) = v := by
    simpa only [Module.End.mul_apply, Module.End.one_apply] using
      congrArg (fun A : Module.End (ZMod 2) V => A v) hLM
  have he : (M - 1) v = -((L - 1) (M v)) := by
    simp only [LinearMap.sub_apply, Module.End.one_apply]
    rw [hinv]
    abel
  rw [he]
  exact W.neg_mem (hL (M v))

theorem labelMapTrivialModulo_profile_quad (W : Submodule (ZMod 2) V)
    (F : ZMod 2 → ZMod 2 → Module.End (ZMod 2) V)
    (hF : ∀ c b, labelMapTrivialModulo W (F c b)) (v : V) :
    controlQuad (fun c b => F c b v) ∈ W := by
  have he : (fun c b => F c b v) = (fun c b => v + (F c b - 1) v) := by
    funext c b
    simp only [LinearMap.sub_apply, Module.End.one_apply]
    abel
  rw [he, controlQuad_add, controlQuad_const, zero_add]
  exact controlQuad_mem W _ (fun c b => hF c b v)

theorem labelProfileStep_identity_mod_quad_mem (W : Submodule (ZMod 2) V)
    (y : ZMod 2 → ZMod 2 → V)
    (F G : ZMod 2 → ZMod 2 → Module.End (ZMod 2) V)
    (hF : ∀ c b, labelMapTrivialModulo W (F c b))
    (hG : ∀ c b, labelMapTrivialModulo W (G c b))
    (ac ab : ZMod 2) (z : V) :
    controlQuad (labelProfileStep y F G ac ab z) ∈ W := by
  apply labelProfileStep_quad_mem (⊤ : Submodule (ZMod 2) V) W y F G 1
    (Submodule.mem_top)
  · intro v hv
    simpa only [Module.End.one_apply, module_charTwo_add_self] using W.zero_mem
  · intro c b v
    exact hG c b v
  · exact labelMapTrivialModulo_profile_quad W F hF

theorem pairedResidualLabelAction_trivialModulo (N : Module.End (ZMod 2) V)
    (h : ℕ) (t0 t1 : ℤ) :
    labelMapTrivialModulo (augmentationImage (pairedAugmentation N) 1)
      (pairedResidualLabelAction N h t0 t1) := by
  intro v
  have hd0 : ((2 ^ (0 : ℕ) : ℕ) : ℤ) ∣ t0 := by simp
  have hd1 : ((2 ^ (0 : ℕ) : ℕ) : ℤ) ∣ t1 := by simp
  simpa only [Nat.pow_zero] using pairedResidualLabelAction_difference_full_image N
    (h := h) (j := 0) (by omega) t0 t1 hd0 hd1 v

def pairedInversionLabelProfile (N : Module.End (ZMod 2) V) (h : ℕ)
    (K : Module.End (ZMod 2) (V × V)) (t0 t1 : ControlExponentCoefficients)
    (rc rb c b : ZMod 2) : Module.End (ZMod 2) (V × V) :=
  pairedResidualLabelAction N h (controlExponentFunction t0 (c, b))
    (controlExponentFunction t1 (c, b)) * K ^ (matrixInversionControl rc rb c b).val

theorem pairedInversionLabelProfile_trivialModulo (N : Module.End (ZMod 2) V)
    (h : ℕ) (K : Module.End (ZMod 2) (V × V))
    (hK : labelMapTrivialModulo (augmentationImage (pairedAugmentation N) 1) K)
    (t0 t1 : ControlExponentCoefficients) (rc rb c b : ZMod 2) :
    labelMapTrivialModulo (augmentationImage (pairedAugmentation N) 1)
      (pairedInversionLabelProfile N h K t0 t1 rc rb c b) := by
  exact labelMapTrivialModulo_mul _ (pairedResidualLabelAction_trivialModulo N h _ _)
    (labelMapTrivialModulo_pow _ hK _)

theorem pairedInversion_labelProfileStep_entry (N : Module.End (ZMod 2) V)
    (h : ℕ) (K : Module.End (ZMod 2) (V × V))
    (hK : labelMapTrivialModulo (augmentationImage (pairedAugmentation N) 1) K)
    (t0 t1 : ControlExponentCoefficients) (rc rb ac ab : ZMod 2)
    (H : ZMod 2 → ZMod 2 → Module.End (ZMod 2) (V × V))
    (hInv : ∀ c b, pairedInversionLabelProfile N h K t0 t1 rc rb (c + ac) (b + ab) * H c b = 1)
    (y : ZMod 2 → ZMod 2 → V × V) (z : V × V) :
    controlQuad (labelProfileStep y (pairedInversionLabelProfile N h K t0 t1 rc rb)
      (fun c b => pairedInversionLabelProfile N h K t0 t1 rc rb c b * H c b) ac ab z) ∈
        augmentationImage (pairedAugmentation N) 1 := by
  have hF : ∀ c b, labelMapTrivialModulo (augmentationImage (pairedAugmentation N) 1)
      (pairedInversionLabelProfile N h K t0 t1 rc rb c b) :=
    pairedInversionLabelProfile_trivialModulo N h K hK t0 t1 rc rb
  apply labelProfileStep_identity_mod_quad_mem _ y _ _ hF
  intro c b
  exact labelMapTrivialModulo_mul _ (hF c b)
    (labelMapTrivialModulo_right_inverse _ (hF (c + ac) (b + ab)) (hInv c b))

end MatrixSecondLabelEntry
end QuantumProver.ControlledCliffordHierarchy

open scoped Matrix BigOperators
namespace QuantumProver.ControlledCliffordHierarchy

def matrixCoefficientGroupProfile {n : ℕ} (T0 T1 : MatrixUnitary n)
    (t0 t1 : ControlExponentCoefficients) (c b : ZMod 2) : MatrixUnitary n :=
  T0 ^ controlExponentFunction t0 (c, b) * T1 ^ controlExponentFunction t1 (c, b)

def matrixCoefficientLinearC {n : ℕ} (T0 T1 : MatrixUnitary n)
    (t0 t1 : ControlExponentCoefficients) : MatrixUnitary n := T0 ^ t0.1 * T1 ^ t1.1

def matrixCoefficientLinearB {n : ℕ} (T0 T1 : MatrixUnitary n)
    (t0 t1 : ControlExponentCoefficients) : MatrixUnitary n := T0 ^ t0.2.1 * T1 ^ t1.2.1

def matrixCoefficientQuadratic {n : ℕ} (T0 T1 : MatrixUnitary n)
    (t0 t1 : ControlExponentCoefficients) : MatrixUnitary n := T0 ^ t0.2.2 * T1 ^ t1.2.2

theorem matrixCoefficientGroupProfile_split {n : ℕ} {T0 T1 : MatrixUnitary n}
    (hcomm : Commute T0 T1) (t0 t1 : ControlExponentCoefficients) (c b : ZMod 2) :
    matrixCoefficientGroupProfile T0 T1 t0 t1 c b =
      matrixCoefficientQuadratic T0 T1 t0 t1 ^ controlExponentBit (c * b) *
        (matrixCoefficientLinearC T0 T1 t0 t1 ^ controlExponentBit c *
         matrixCoefficientLinearB T0 T1 t0 t1 ^ controlExponentBit b) := by
  rcases physical_control_bit_cases c with rfl | rfl <;>
    rcases physical_control_bit_cases b with rfl | rfl
  all_goals simp only [matrixCoefficientGroupProfile, matrixCoefficientQuadratic,
    matrixCoefficientLinearC, matrixCoefficientLinearB, controlExponentFunction,
    controlExponentPolynomial, controlExponentBit_zero, controlExponentBit_one,
    zero_mul, mul_zero, one_mul, mul_one, zero_add, add_zero, zpow_zero, zpow_one]
  rw [matrixUnitary_shift_mul hcomm, matrixUnitary_shift_mul hcomm]
  congr 1 <;> ring

theorem matrixZpow_bit_signed_pauli {n : ℕ} {U : MatrixUnitary n}
    (s : ZMod 2) (p : PauliLabel n) (hp : (U : QuantumMatrix n) = signedOrderedPauli s p)
    (e : ZMod 2) :
    matrixZpow U (controlExponentBit e) = signedOrderedPauli (e * s) (e • p) := by
  rcases physical_control_bit_cases e with rfl | rfl
  · simp only [controlExponentBit_zero, matrixZpow, zpow_zero, Submonoid.coe_one,
      zero_mul, zero_smul, signedOrderedPauli, bitSign_zero, orderedPauli_zero, one_smul]
    change 1 = orderedPauli (0 : BitString n) 0
    exact orderedPauli_zero.symm
  · simpa only [controlExponentBit_one, matrixZpow, zpow_one, one_mul, one_smul] using hp

def matrixTerminalQuadLabel {n : ℕ} (p0 p1 : PauliLabel n) (q : ℕ)
    (t0 t1 : ControlExponentCoefficients) : PauliLabel n :=
  (((t0.2.2 / (q : ℤ) : ℤ) : ZMod 2) • p0) +
  (((t1.2.2 / (q : ℤ) : ℤ) : ZMod 2) • p1)

def matrixTerminalQuadSign {n : ℕ} (s0 s1 : ZMod 2) (p0 p1 : PauliLabel n) (q : ℕ)
    (t0 t1 : ControlExponentCoefficients) : ZMod 2 :=
  ((t0.2.2 / (q : ℤ) : ℤ) : ZMod 2) * s0 +
  ((t1.2.2 / (q : ℤ) : ℤ) : ZMod 2) * s1 +
  dot ((((t0.2.2 / (q : ℤ) : ℤ) : ZMod 2) • p0).2)
    ((((t1.2.2 / (q : ℤ) : ℤ) : ZMod 2) • p1).1)

theorem matrixZpow_divisible_signed_pauli {n q : ℕ} {T : MatrixUnitary n}
    (s : ZMod 2) (p : PauliLabel n)
    (hp : ((T ^ q : MatrixUnitary n) : QuantumMatrix n) = signedOrderedPauli s p)
    (hHerm : dot p.2 p.1 = 0) (t : ℤ) (ht : (q : ℤ) ∣ t) :
    matrixZpow T t = signedOrderedPauli (((t / (q : ℤ) : ℤ) : ZMod 2) * s)
      (((t / (q : ℤ) : ℤ) : ZMod 2) • p) := by
  rw [matrixZpow_absorb_q s p hp hHerm, Int.emod_eq_zero_of_dvd ht]
  simp only [matrixZpow, zpow_zero, Submonoid.coe_one, mul_one]

theorem matrixCoefficientQuadratic_signed_pauli {n q : ℕ} {T0 T1 : MatrixUnitary n}
    (s0 s1 : ZMod 2) (p0 p1 : PauliLabel n)
    (hp0 : ((T0 ^ q : MatrixUnitary n) : QuantumMatrix n) = signedOrderedPauli s0 p0)
    (hp1 : ((T1 ^ q : MatrixUnitary n) : QuantumMatrix n) = signedOrderedPauli s1 p1)
    (hh0 : dot p0.2 p0.1 = 0) (hh1 : dot p1.2 p1.1 = 0)
    (t0 t1 : ControlExponentCoefficients)
    (ht0 : (q : ℤ) ∣ t0.2.2) (ht1 : (q : ℤ) ∣ t1.2.2) :
    ((matrixCoefficientQuadratic T0 T1 t0 t1 : MatrixUnitary n) : QuantumMatrix n) =
      signedOrderedPauli (matrixTerminalQuadSign s0 s1 p0 p1 q t0 t1)
        (matrixTerminalQuadLabel p0 p1 q t0 t1) := by
  change matrixZpow T0 t0.2.2 * matrixZpow T1 t1.2.2 = _
  rw [matrixZpow_divisible_signed_pauli s0 p0 hp0 hh0 _ ht0,
    matrixZpow_divisible_signed_pauli s1 p1 hp1 hh1 _ ht1, signedOrderedPauli_mul]
  rfl

theorem matrixTerminalQuadLabel_mem {n : ℕ}
    (W : Submodule (ZMod 2) (PauliLabel n)) (p0 p1 : PauliLabel n)
    (hp0 : p0 ∈ W) (hp1 : p1 ∈ W) (q : ℕ) (t0 t1 : ControlExponentCoefficients) :
    matrixTerminalQuadLabel p0 p1 q t0 t1 ∈ W :=
  W.add_mem (W.smul_mem _ hp0) (W.smul_mem _ hp1)

theorem matrixTerminal_depth_quad_dvd {h : ℕ} (hh : 1 ≤ h)
    (t : ControlExponentCoefficients) (ht : controlExponentDepth (h - 1) t) :
    ((2 ^ h : ℕ) : ℤ) ∣ t.2.2 := by
  have he : h - 1 + 1 = h := by omega
  simpa only [he, Nat.cast_pow, Nat.cast_ofNat] using ht.2.2

theorem matrixCoefficientProfile_terminal_absorb {n q : ℕ} {T0 T1 : MatrixUnitary n}
    (hcomm : Commute T0 T1) (s0 s1 : ZMod 2) (p0 p1 : PauliLabel n)
    (hp0 : ((T0 ^ q : MatrixUnitary n) : QuantumMatrix n) = signedOrderedPauli s0 p0)
    (hp1 : ((T1 ^ q : MatrixUnitary n) : QuantumMatrix n) = signedOrderedPauli s1 p1)
    (hh0 : dot p0.2 p0.1 = 0) (hh1 : dot p1.2 p1.1 = 0)
    (t0 t1 : ControlExponentCoefficients)
    (ht0 : (q : ℤ) ∣ t0.2.2) (ht1 : (q : ℤ) ∣ t1.2.2) (c b : ZMod 2) :
    matrixShiftProfile T0 T1 (fun c b => controlExponentFunction t0 (c, b))
        (fun c b => controlExponentFunction t1 (c, b)) c b =
      signedOrderedPauli ((c * b) * matrixTerminalQuadSign s0 s1 p0 p1 q t0 t1)
        ((c * b) • matrixTerminalQuadLabel p0 p1 q t0 t1) *
        matrixHalfCycleProfile (matrixCoefficientLinearC T0 T1 t0 t1)
          (matrixCoefficientLinearB T0 T1 t0 t1) c b := by
  have hm := congrArg (fun U : MatrixUnitary n => (U : QuantumMatrix n))
    (matrixCoefficientGroupProfile_split hcomm t0 t1 c b)
  have he : matrixShiftProfile T0 T1 (fun c b => controlExponentFunction t0 (c, b))
      (fun c b => controlExponentFunction t1 (c, b)) c b =
      matrixZpow (matrixCoefficientQuadratic T0 T1 t0 t1) (controlExponentBit (c * b)) *
        matrixHalfCycleProfile (matrixCoefficientLinearC T0 T1 t0 t1)
          (matrixCoefficientLinearB T0 T1 t0 t1) c b := by
    simpa only [matrixCoefficientGroupProfile, matrixZpow, matrixShiftProfile,
      matrixHalfCycleProfile, Submonoid.coe_mul] using hm
  rw [he, matrixZpow_bit_signed_pauli _ _
    (matrixCoefficientQuadratic_signed_pauli s0 s1 p0 p1 hp0 hp1 hh0 hh1 t0 t1 ht0 ht1)]

theorem matrixCoefficientProfile_terminal_signed_image {n : ℕ}
    (W : Submodule (ZMod 2) (PauliLabel n)) (r : PauliLabel n) (hr : r ∈ W)
    (y : ZMod 2 → ZMod 2 → PauliLabel n) (hy : controlQuad y ∈ W) :
    controlQuad (fun c b => y c b + (c * b) • r) ∈ W :=
  controlQuad_absorbed_mem W y (fun c b => (c * b) • r) hy (fun c b => W.smul_mem _ hr)

end QuantumProver.ControlledCliffordHierarchy

open scoped Matrix BigOperators
namespace QuantumProver.ControlledCliffordHierarchy
section MatrixHalfDepthMaps
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

theorem pairedAugmentation_power_zero (N : Module.End (ZMod 2) V)
    (q : ℕ) (hN : N ^ q = 0) : pairedAugmentation N ^ q = 0 := by
  rw [pairedAugmentation_pow, hN]
  ext v <;> rfl

theorem matrixHalfDepth_add_self {h : ℕ} (hh : 1 ≤ h) :
    2 ^ (h - 1) + 2 ^ (h - 1) = 2 ^ h := by
  have he : h - 1 + 1 = h := by omega
  have hp : 2 ^ (h - 1 + 1) = 2 ^ (h - 1) * 2 := by
    simpa only [Nat.succ_eq_add_one] using Nat.pow_succ 2 (h - 1)
  rw [he] at hp
  omega

theorem pairedHalfDepthAction_fixes (N : Module.End (ZMod 2) V)
    {h : ℕ} (hh : 1 ≤ h) (hN : N ^ (2 ^ h) = 0) (a0 a1 : ℤ)
    (ha0 : ((2 ^ (h - 1) : ℕ) : ℤ) ∣ a0)
    (ha1 : ((2 ^ (h - 1) : ℕ) : ℤ) ∣ a1)
    {v : V × V} (hv : v ∈ augmentationImage (pairedAugmentation N) (2 ^ (h - 1))) :
    pairedResidualLabelAction N h a0 a1 v = v := by
  have hd := pairedResidualLabelAction_difference_raise N (h := h) (j := h - 1)
    (by omega) (2 ^ (h - 1)) a0 a1 ha0 ha1 hv
  rw [matrixHalfDepth_add_self hh,
    augmentationImage_zero _ _ (pairedAugmentation_power_zero N _ hN), Submodule.mem_bot] at hd
  exact sub_eq_zero.mp (by
    simpa only [LinearMap.sub_apply, Module.End.one_apply] using hd)

theorem pairedHalfDepthAction_cross_zero (N : Module.End (ZMod 2) V)
    {h : ℕ} (hh : 1 ≤ h) (hN : N ^ (2 ^ h) = 0) (a0 a1 b0 b1 : ℤ)
    (ha0 : ((2 ^ (h - 1) : ℕ) : ℤ) ∣ a0)
    (ha1 : ((2 ^ (h - 1) : ℕ) : ℤ) ∣ a1)
    (hb0 : ((2 ^ (h - 1) : ℕ) : ℤ) ∣ b0)
    (hb1 : ((2 ^ (h - 1) : ℕ) : ℤ) ∣ b1) :
    (pairedResidualLabelAction N h a0 a1 - 1) *
      (pairedResidualLabelAction N h b0 b1 - 1) = 0 := by
  apply LinearMap.ext
  intro v
  have hv := pairedResidualLabelAction_difference_full_image N (h := h) (j := h - 1)
    (by omega) b0 b1 hb0 hb1 v
  have hf := pairedHalfDepthAction_fixes N hh hN a0 a1 ha0 ha1 hv
  change (pairedResidualLabelAction N h a0 a1 - 1)
    ((pairedResidualLabelAction N h b0 b1 - 1) v) = 0
  rw [LinearMap.sub_apply, Module.End.one_apply, hf, sub_self]

theorem pairedHalfDepthAction_sq (N : Module.End (ZMod 2) V)
    {h : ℕ} (hh : 1 ≤ h) (hN : N ^ (2 ^ h) = 0) (a0 a1 : ℤ)
    (ha0 : ((2 ^ (h - 1) : ℕ) : ℤ) ∣ a0)
    (ha1 : ((2 ^ (h - 1) : ℕ) : ℤ) ∣ a1) :
    pairedResidualLabelAction N h a0 a1 ^ (2 : ℕ) = 1 := by
  let A := pairedResidualLabelAction N h a0 a1
  have hs : (A - 1) ^ (2 : ℕ) = 0 := by
    simpa only [A, pow_two] using pairedHalfDepthAction_cross_zero N hh hN
      a0 a1 a0 a1 ha0 ha1 ha0 ha1
  have ha : 1 + (A - 1) = A := by abel
  have hp := labelEnd_one_add_pow_two_pow (A - 1) 1
  simpa only [ha, Nat.pow_one, hs, add_zero, A] using hp

theorem controlExponentDepth_half_linears {h : ℕ} (t : ControlExponentCoefficients)
    (ht : controlExponentDepth (h - 1) t) :
    ((2 ^ (h - 1) : ℕ) : ℤ) ∣ t.1 ∧ ((2 ^ (h - 1) : ℕ) : ℤ) ∣ t.2.1 := by
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using And.intro ht.1 ht.2.1

end MatrixHalfDepthMaps

section MatrixLabelTransport
variable {V W : Type*} [AddCommGroup V] [AddCommGroup W]
  [Module (ZMod 2) V] [Module (ZMod 2) W]

def matrixLabelTransport (E : V ≃ₗ[ZMod 2] W)
    (L : Module.End (ZMod 2) V) : Module.End (ZMod 2) W :=
  E.toLinearMap.comp (L.comp E.symm.toLinearMap)

theorem matrixLabelTransport_apply (E : V ≃ₗ[ZMod 2] W)
    (L : Module.End (ZMod 2) V) (v : W) :
    matrixLabelTransport E L v = E (L (E.symm v)) := rfl

theorem matrixLabelTransport_one (E : V ≃ₗ[ZMod 2] W) : matrixLabelTransport E 1 = 1 := by
  ext v
  simp only [matrixLabelTransport_apply, Module.End.one_apply, LinearEquiv.apply_symm_apply]

theorem matrixLabelTransport_zero (E : V ≃ₗ[ZMod 2] W) : matrixLabelTransport E 0 = 0 := by
  ext v
  simp only [matrixLabelTransport_apply, LinearMap.zero_apply, map_zero]

theorem matrixLabelTransport_mul (E : V ≃ₗ[ZMod 2] W)
    (L M : Module.End (ZMod 2) V) :
    matrixLabelTransport E (L * M) = matrixLabelTransport E L * matrixLabelTransport E M := by
  ext v
  simp only [matrixLabelTransport_apply, Module.End.mul_apply, LinearEquiv.symm_apply_apply]

theorem matrixLabelTransport_sub (E : V ≃ₗ[ZMod 2] W)
    (L M : Module.End (ZMod 2) V) :
    matrixLabelTransport E (L - M) = matrixLabelTransport E L - matrixLabelTransport E M := by
  ext v
  simp only [matrixLabelTransport_apply, LinearMap.sub_apply, map_sub]

theorem matrixLabelTransport_pow (E : V ≃ₗ[ZMod 2] W)
    (L : Module.End (ZMod 2) V) (k : ℕ) :
    matrixLabelTransport E (L ^ k) = matrixLabelTransport E L ^ k := by
  induction k with
  | zero => simp only [pow_zero, matrixLabelTransport_one]
  | succ k ih => rw [pow_succ, matrixLabelTransport_mul, ih, pow_succ]

theorem matrixLabelTransport_cross_zero (E : V ≃ₗ[ZMod 2] W)
    {L M : Module.End (ZMod 2) V} (hLM : (L - 1) * (M - 1) = 0) :
    (matrixLabelTransport E L - 1) * (matrixLabelTransport E M - 1) = 0 := by
  have he := congrArg (matrixLabelTransport E) hLM
  simpa only [matrixLabelTransport_mul, matrixLabelTransport_sub,
    matrixLabelTransport_one, matrixLabelTransport_zero] using he

theorem matrixLabelTransport_sq (E : V ≃ₗ[ZMod 2] W)
    {L : Module.End (ZMod 2) V} (hL : L ^ (2 : ℕ) = 1) :
    matrixLabelTransport E L ^ (2 : ℕ) = 1 := by
  have he := congrArg (matrixLabelTransport E) hL
  simpa only [matrixLabelTransport_pow, matrixLabelTransport_one] using he

theorem matrixLabelTransport_fixes_image (E : V ≃ₗ[ZMod 2] W)
    (S : Submodule (ZMod 2) V) (L : Module.End (ZMod 2) V)
    (hL : ∀ v ∈ S, L v = v) :
    ∀ w ∈ S.map E.toLinearMap, matrixLabelTransport E L w = w := by
  rintro w ⟨v, hv, rfl⟩
  change E (L (E.symm (E v))) = E v
  rw [LinearEquiv.symm_apply_apply, hL v hv]

end MatrixLabelTransport
end QuantumProver.ControlledCliffordHierarchy

open scoped Matrix BigOperators
namespace QuantumProver.ControlledCliffordHierarchy

theorem signedOrderedPauli_dot_zero_of_sq_one {n : ℕ} (s : ZMod 2) (p : PauliLabel n)
    (hs : signedOrderedPauli s p ^ (2 : ℕ) = 1) : dot p.2 p.1 = 0 := by
  have heq : signedOrderedPauli s p ^ (2 : ℕ) =
      bitSign (dot p.2 p.1) • (1 : QuantumMatrix n) := by
    rw [pow_two, signedOrderedPauli_mul]
    simp only [CharTwo.add_self_eq_zero, module_charTwo_add_self, zero_add,
      signedOrderedPauli, orderedPauli_zero]
    change bitSign (dot p.2 p.1) • orderedPauli (0 : BitString n) 0 = _
    rw [orderedPauli_zero]
  rw [heq] at hs
  have he := congrArg (fun M : QuantumMatrix n => M 0 0) hs
  have hb : bitSign (dot p.2 p.1) = 1 := by
    simpa only [Matrix.smul_apply, Matrix.one_apply, if_pos rfl, ite_true,
      smul_eq_mul, mul_one] using he
  rcases physical_control_bit_cases (dot p.2 p.1) with h0 | h1
  · exact h0
  · rw [h1, bitSign_one] at hb
    norm_num at hb

theorem matrixHalfDepth_int_cast {h : ℕ} (hh : 1 ≤ h) :
    ((2 ^ h : ℕ) : ℤ) = 2 * ((2 ^ (h - 1) : ℕ) : ℤ) := by
  have he := congrArg (fun k : ℕ => (k : ℤ)) (matrixHalfDepth_add_self hh)
  simpa only [Nat.cast_add, two_mul] using he.symm

theorem matrixHalfDepth_two_dvd {h : ℕ} (hh : 1 ≤ h) {a : ℤ}
    (ha : ((2 ^ (h - 1) : ℕ) : ℤ) ∣ a) : ((2 ^ h : ℕ) : ℤ) ∣ 2 * a := by
  rcases ha with ⟨u, hu⟩
  refine ⟨u, ?_⟩
  rw [hu, matrixHalfDepth_int_cast hh]
  ring

theorem matrixHalfDepth_four_dvd {h : ℕ} (hh : 1 ≤ h) {a : ℤ}
    (ha : ((2 ^ (h - 1) : ℕ) : ℤ) ∣ a) : ((2 * 2 ^ h : ℕ) : ℤ) ∣ 4 * a := by
  rcases ha with ⟨u, hu⟩
  refine ⟨u, ?_⟩
  simp only [Nat.cast_mul, Nat.cast_ofNat]
  rw [hu, matrixHalfDepth_int_cast hh]
  ring

theorem matrixUnitary_shift_square {n : ℕ} {T0 T1 : MatrixUnitary n}
    (hcomm : Commute T0 T1) (a0 a1 : ℤ) :
    (T0 ^ a0 * T1 ^ a1) ^ (2 : ℕ) = T0 ^ (2 * a0) * T1 ^ (2 * a1) := by
  rw [pow_two, matrixUnitary_shift_mul hcomm]
  congr 1 <;> ring

theorem matrixHalfDepth_word_four_one {n h : ℕ} {T0 T1 : MatrixUnitary n}
    (hh : 1 ≤ h) (hcomm : Commute T0 T1) (s0 s1 : ZMod 2) (p0 p1 : PauliLabel n)
    (hp0 : ((T0 ^ (2 ^ h) : MatrixUnitary n) : QuantumMatrix n) = signedOrderedPauli s0 p0)
    (hp1 : ((T1 ^ (2 ^ h) : MatrixUnitary n) : QuantumMatrix n) = signedOrderedPauli s1 p1)
    (hh0 : dot p0.2 p0.1 = 0) (hh1 : dot p1.2 p1.1 = 0) (a0 a1 : ℤ)
    (ha0 : ((2 ^ (h - 1) : ℕ) : ℤ) ∣ a0)
    (ha1 : ((2 ^ (h - 1) : ℕ) : ℤ) ∣ a1) :
    (T0 ^ a0 * T1 ^ a1) ^ (4 : ℕ) = 1 := by
  have hT0 := matrixUnitary_two_q_pow_one s0 p0 hp0 hh0
  have hT1 := matrixUnitary_two_q_pow_one s1 p1 hp1 hh1
  have ht0 : T0 ^ (4 * a0) = 1 := by
    rw [zpow_eq_zpow_emod' (4 * a0) hT0,
      Int.emod_eq_zero_of_dvd (matrixHalfDepth_four_dvd hh ha0), zpow_zero]
  have ht1 : T1 ^ (4 * a1) = 1 := by
    rw [zpow_eq_zpow_emod' (4 * a1) hT1,
      Int.emod_eq_zero_of_dvd (matrixHalfDepth_four_dvd hh ha1), zpow_zero]
  calc
    (T0 ^ a0 * T1 ^ a1) ^ (4 : ℕ) = ((T0 ^ a0 * T1 ^ a1) ^ (2 : ℕ)) ^ (2 : ℕ) := by
      rw [← pow_mul]
    _ = (T0 ^ (2 * a0) * T1 ^ (2 * a1)) ^ (2 : ℕ) := by
      rw [matrixUnitary_shift_square hcomm]
    _ = T0 ^ (2 * (2 * a0)) * T1 ^ (2 * (2 * a1)) := matrixUnitary_shift_square hcomm _ _
    _ = T0 ^ (4 * a0) * T1 ^ (4 * a1) := by congr 1 <;> ring
    _ = 1 := by rw [ht0, ht1, one_mul]

theorem matrixHalfDepth_word_square_signed {n h : ℕ} {T0 T1 : MatrixUnitary n}
    (hh : 1 ≤ h) (hcomm : Commute T0 T1) (s0 s1 : ZMod 2) (p0 p1 : PauliLabel n)
    (hp0 : ((T0 ^ (2 ^ h) : MatrixUnitary n) : QuantumMatrix n) = signedOrderedPauli s0 p0)
    (hp1 : ((T1 ^ (2 ^ h) : MatrixUnitary n) : QuantumMatrix n) = signedOrderedPauli s1 p1)
    (hh0 : dot p0.2 p0.1 = 0) (hh1 : dot p1.2 p1.1 = 0) (a0 a1 : ℤ)
    (ha0 : ((2 ^ (h - 1) : ℕ) : ℤ) ∣ a0)
    (ha1 : ((2 ^ (h - 1) : ℕ) : ℤ) ∣ a1) :
    (((T0 ^ a0 * T1 ^ a1) ^ (2 : ℕ) : MatrixUnitary n) : QuantumMatrix n) =
      signedOrderedPauli
        (matrixTerminalQuadSign s0 s1 p0 p1 (2 ^ h) (0, 0, 2 * a0) (0, 0, 2 * a1))
        (matrixTerminalQuadLabel p0 p1 (2 ^ h) (0, 0, 2 * a0) (0, 0, 2 * a1)) := by
  rw [matrixUnitary_shift_square hcomm]
  simpa only [matrixCoefficientQuadratic] using matrixCoefficientQuadratic_signed_pauli
    s0 s1 p0 p1 hp0 hp1 hh0 hh1 (0, 0, 2 * a0) (0, 0, 2 * a1)
    (matrixHalfDepth_two_dvd hh ha0) (matrixHalfDepth_two_dvd hh ha1)

theorem matrixHalfDepth_word_square_hermitian {n h : ℕ} {T0 T1 : MatrixUnitary n}
    (hh : 1 ≤ h) (hcomm : Commute T0 T1) (s0 s1 : ZMod 2) (p0 p1 : PauliLabel n)
    (hp0 : ((T0 ^ (2 ^ h) : MatrixUnitary n) : QuantumMatrix n) = signedOrderedPauli s0 p0)
    (hp1 : ((T1 ^ (2 ^ h) : MatrixUnitary n) : QuantumMatrix n) = signedOrderedPauli s1 p1)
    (hh0 : dot p0.2 p0.1 = 0) (hh1 : dot p1.2 p1.1 = 0) (a0 a1 : ℤ)
    (ha0 : ((2 ^ (h - 1) : ℕ) : ℤ) ∣ a0)
    (ha1 : ((2 ^ (h - 1) : ℕ) : ℤ) ∣ a1) :
    dot (matrixTerminalQuadLabel p0 p1 (2 ^ h) (0, 0, 2 * a0) (0, 0, 2 * a1)).2
      (matrixTerminalQuadLabel p0 p1 (2 ^ h) (0, 0, 2 * a0) (0, 0, 2 * a1)).1 = 0 := by
  apply signedOrderedPauli_dot_zero_of_sq_one
    (matrixTerminalQuadSign s0 s1 p0 p1 (2 ^ h) (0, 0, 2 * a0) (0, 0, 2 * a1))
  rw [← matrixHalfDepth_word_square_signed hh hcomm s0 s1 p0 p1 hp0 hp1 hh0 hh1 a0 a1 ha0 ha1]
  have hg : ((T0 ^ a0 * T1 ^ a1) ^ (2 : ℕ)) ^ (2 : ℕ) = 1 := by
    simpa only [← pow_mul] using
      matrixHalfDepth_word_four_one hh hcomm s0 s1 p0 p1 hp0 hp1 hh0 hh1 a0 a1 ha0 ha1
  simpa only [SubmonoidClass.coe_pow, Submonoid.coe_one] using
    congrArg (fun U : MatrixUnitary n => (U : QuantumMatrix n)) hg

theorem matrixHalfDepth_word_square_label_mem {n : ℕ}
    (W : Submodule (ZMod 2) (PauliLabel n)) (p0 p1 : PauliLabel n)
    (hp0 : p0 ∈ W) (hp1 : p1 ∈ W) (h : ℕ) (a0 a1 : ℤ) :
    matrixTerminalQuadLabel p0 p1 (2 ^ h) (0, 0, 2 * a0) (0, 0, 2 * a1) ∈ W :=
  matrixTerminalQuadLabel_mem W p0 p1 hp0 hp1 _ _ _

end QuantumProver.ControlledCliffordHierarchy

open scoped Matrix BigOperators
namespace QuantumProver.ControlledCliffordHierarchy
section MatrixPairedPhysicalTerminal
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {n : ℕ}

def matrixPairedIntAction0 (E : (V × V) ≃ₗ[ZMod 2] PauliLabel n)
    (N : Module.End (ZMod 2) V) (h : ℕ) (t : ℤ) : Module.End (ZMod 2) (PauliLabel n) :=
  matrixLabelTransport E ((matrixResidualLabelAction N h t).prodMap (1 : Module.End (ZMod 2) V))

def matrixPairedIntAction1 (E : (V × V) ≃ₗ[ZMod 2] PauliLabel n)
    (N : Module.End (ZMod 2) V) (h : ℕ) (t : ℤ) : Module.End (ZMod 2) (PauliLabel n) :=
  matrixLabelTransport E ((1 : Module.End (ZMod 2) V).prodMap (matrixResidualLabelAction N h t))

def matrixPairedImage (E : (V × V) ≃ₗ[ZMod 2] PauliLabel n)
    (N : Module.End (ZMod 2) V) (a : ℕ) : Submodule (ZMod 2) (PauliLabel n) :=
  (augmentationImage (pairedAugmentation N) a).map E.toLinearMap

theorem matrixPairedIntAction_pair (E : (V × V) ≃ₗ[ZMod 2] PauliLabel n)
    (N : Module.End (ZMod 2) V) (h : ℕ) (t0 t1 : ℤ) :
    matrixPairedIntAction0 E N h t0 * matrixPairedIntAction1 E N h t1 =
      matrixLabelTransport E (pairedResidualLabelAction N h t0 t1) := by
  unfold matrixPairedIntAction0 matrixPairedIntAction1
  rw [← matrixLabelTransport_mul]
  congr 1

theorem matrixPaired_word_commute {T0 T1 : MatrixUnitary n} (hcomm : Commute T0 T1)
    (a0 a1 b0 b1 : ℤ) : Commute (T0 ^ a0 * T1 ^ a1) (T0 ^ b0 * T1 ^ b1) := by
  change (T0 ^ a0 * T1 ^ a1) * (T0 ^ b0 * T1 ^ b1) =
    (T0 ^ b0 * T1 ^ b1) * (T0 ^ a0 * T1 ^ a1)
  rw [matrixUnitary_shift_mul hcomm, matrixUnitary_shift_mul hcomm]
  congr 1 <;> ring

theorem matrixPairedCoefficient_terminal {h : ℕ} (hh : 1 ≤ h)
    (E : (V × V) ≃ₗ[ZMod 2] PauliLabel n) (N : Module.End (ZMod 2) V)
    (hN : N ^ (2 ^ h) = 0) (T0 T1 : MatrixUnitary n) (hcomm : Commute T0 T1)
    (hT0 : hierarchy n 2 (T0 : QuantumMatrix n)) (hT1 : hierarchy n 2 (T1 : QuantumMatrix n))
    (k0 k1 : ℤ → PauliLabel n → ZMod 2)
    (h0 : ∀ t p, conjugate (matrixZpow T0 t) (orderedPauli p.1 p.2) =
      bitSign (k0 t p) • orderedPauli (matrixPairedIntAction0 E N h t p).1
        (matrixPairedIntAction0 E N h t p).2)
    (h1 : ∀ t p, conjugate (matrixZpow T1 t) (orderedPauli p.1 p.2) =
      bitSign (k1 t p) • orderedPauli (matrixPairedIntAction1 E N h t p).1
        (matrixPairedIntAction1 E N h t p).2)
    (sq0 sq1 : ZMod 2) (pq0 pq1 : PauliLabel n)
    (hp0 : ((T0 ^ (2 ^ h) : MatrixUnitary n) : QuantumMatrix n) = signedOrderedPauli sq0 pq0)
    (hp1 : ((T1 ^ (2 ^ h) : MatrixUnitary n) : QuantumMatrix n) = signedOrderedPauli sq1 pq1)
    (hh0 : dot pq0.2 pq0.1 = 0) (hh1 : dot pq1.2 pq1.1 = 0)
    (hpW0 : pq0 ∈ matrixPairedImage E N (2 ^ (h - 1)))
    (hpW1 : pq1 ∈ matrixPairedImage E N (2 ^ (h - 1)))
    (t0 t1 : ControlExponentCoefficients)
    (ht0 : controlExponentDepth (h - 1) t0) (ht1 : controlExponentDepth (h - 1) t1)
    (s : ZMod 2 → ZMod 2 → ZMod 2) (y : ZMod 2 → ZMod 2 → PauliLabel n)
    (hy : controlQuad y ∈ matrixPairedImage E N (2 ^ (h - 1))) :
    hierarchy ((n + 1) + 1) 3
      (twoControlMatrix (signedMatrixProfileWord s y (matrixCoefficientProfile T0 T1 t0 t1))) := by
  let L0 := matrixPairedIntAction0 E N h
  let L1 := matrixPairedIntAction1 E N h
  let W := matrixPairedImage E N (2 ^ (h - 1))
  let S0 := matrixCoefficientLinearC T0 T1 t0 t1
  let S1 := matrixCoefficientLinearB T0 T1 t0 t1
  let A := matrixLabelTransport E (pairedResidualLabelAction N h t0.1 t1.1)
  let B := matrixLabelTransport E (pairedResidualLabelAction N h t0.2.1 t1.2.1)
  let ka := matrixIntegerPairSign L0 L1 k0 k1 t0.1 t1.1
  let kb := matrixIntegerPairSign L0 L1 k0 k1 t0.2.1 t1.2.1
  have hlin0 := controlExponentDepth_half_linears t0 ht0
  have hlin1 := controlExponentDepth_half_linears t1 ht1
  have hquad0 := matrixTerminal_depth_quad_dvd hh t0 ht0
  have hquad1 := matrixTerminal_depth_quad_dvd hh t1 ht1
  have hScomm : Commute S0 S1 := matrixPaired_word_commute hcomm _ _ _ _
  have hS0 : hierarchy n 2 (S0 : QuantumMatrix n) := by
    change hierarchy n 2 (matrixZpow T0 t0.1 * matrixZpow T1 t1.1)
    exact matrixShiftProfile_constant_clifford hT0 hT1 _ _
  have hS1 : hierarchy n 2 (S1 : QuantumMatrix n) := by
    change hierarchy n 2 (matrixZpow T0 t0.2.1 * matrixZpow T1 t1.2.1)
    exact matrixShiftProfile_constant_clifford hT0 hT1 _ _
  have hA : ∀ p, conjugate (S0 : QuantumMatrix n) (orderedPauli p.1 p.2) =
      bitSign (ka p) • orderedPauli (A p).1 (A p).2 := by
    intro p
    have he := matrixZpow_pair_full_signed_action T0 T1 L0 L1 k0 k1 h0 h1 t0.1 t1.1 p
    simpa only [S0, matrixCoefficientLinearC, matrixZpow, Submonoid.coe_mul,
      L0, L1, matrixPairedIntAction_pair, A, ka] using he
  have hB : ∀ p, conjugate (S1 : QuantumMatrix n) (orderedPauli p.1 p.2) =
      bitSign (kb p) • orderedPauli (B p).1 (B p).2 := by
    intro p
    have he := matrixZpow_pair_full_signed_action T0 T1 L0 L1 k0 k1 h0 h1 t0.2.1 t1.2.1 p
    simpa only [S1, matrixCoefficientLinearB, matrixZpow, Submonoid.coe_mul,
      L0, L1, matrixPairedIntAction_pair, B, kb] using he
  have hA2 : A ^ (2 : ℕ) = 1 := matrixLabelTransport_sq E
    (pairedHalfDepthAction_sq N hh hN _ _ hlin0.1 hlin1.1)
  have hB2 : B ^ (2 : ℕ) = 1 := matrixLabelTransport_sq E
    (pairedHalfDepthAction_sq N hh hN _ _ hlin0.2 hlin1.2)
  have hcross : (A - 1) * (B - 1) = 0 := matrixLabelTransport_cross_zero E
    (pairedHalfDepthAction_cross_zero N hh hN _ _ _ _ hlin0.1 hlin1.1 hlin0.2 hlin1.2)
  have hFixA : ∀ v ∈ W, A v = v := matrixLabelTransport_fixes_image E
    (augmentationImage (pairedAugmentation N) (2 ^ (h - 1))) _
    (fun v hv => pairedHalfDepthAction_fixes N hh hN _ _ hlin0.1 hlin1.1 hv)
  have hFixB : ∀ v ∈ W, B v = v := matrixLabelTransport_fixes_image E
    (augmentationImage (pairedAugmentation N) (2 ^ (h - 1))) _
    (fun v hv => pairedHalfDepthAction_fixes N hh hN _ _ hlin0.2 hlin1.2 hv)
  let sa := matrixTerminalQuadSign sq0 sq1 pq0 pq1 (2 ^ h)
    (0, 0, 2 * t0.1) (0, 0, 2 * t1.1)
  let sb := matrixTerminalQuadSign sq0 sq1 pq0 pq1 (2 ^ h)
    (0, 0, 2 * t0.2.1) (0, 0, 2 * t1.2.1)
  let pa := matrixTerminalQuadLabel pq0 pq1 (2 ^ h)
    (0, 0, 2 * t0.1) (0, 0, 2 * t1.1)
  let pb := matrixTerminalQuadLabel pq0 pq1 (2 ^ h)
    (0, 0, 2 * t0.2.1) (0, 0, 2 * t1.2.1)
  have hpa : ((S0 ^ (2 : ℕ) : MatrixUnitary n) : QuantumMatrix n) = signedOrderedPauli sa pa :=
    matrixHalfDepth_word_square_signed hh hcomm sq0 sq1 pq0 pq1 hp0 hp1 hh0 hh1
      _ _ hlin0.1 hlin1.1
  have hpb : ((S1 ^ (2 : ℕ) : MatrixUnitary n) : QuantumMatrix n) = signedOrderedPauli sb pb :=
    matrixHalfDepth_word_square_signed hh hcomm sq0 sq1 pq0 pq1 hp0 hp1 hh0 hh1
      _ _ hlin0.2 hlin1.2
  have hHermA : dot pa.2 pa.1 = 0 :=
    matrixHalfDepth_word_square_hermitian hh hcomm sq0 sq1 pq0 pq1 hp0 hp1 hh0 hh1
      _ _ hlin0.1 hlin1.1
  have hHermB : dot pb.2 pb.1 = 0 :=
    matrixHalfDepth_word_square_hermitian hh hcomm sq0 sq1 pq0 pq1 hp0 hp1 hh0 hh1
      _ _ hlin0.2 hlin1.2
  let qs := matrixTerminalQuadSign sq0 sq1 pq0 pq1 (2 ^ h) t0 t1
  let qp := matrixTerminalQuadLabel pq0 pq1 (2 ^ h) t0 t1
  have hqp : qp ∈ W := matrixTerminalQuadLabel_mem W pq0 pq1 hpW0 hpW1 _ _ _
  let s' := fun c b => s c b + (c * b) * qs + dot (y c b).2 ((c * b) • qp).1
  let y' := fun c b => y c b + (c * b) • qp
  have hy' : controlQuad y' ∈ W := matrixCoefficientProfile_terminal_signed_image W qp hqp y hy
  have hRaw : ∀ c b, matrixCoefficientProfile T0 T1 t0 t1 c b =
      signedOrderedPauli ((c * b) * qs) ((c * b) • qp) * matrixHalfCycleProfile S0 S1 c b :=
    matrixCoefficientProfile_terminal_absorb hcomm sq0 sq1 pq0 pq1 hp0 hp1 hh0 hh1
      t0 t1 hquad0 hquad1
  have hf : signedMatrixProfileWord s y (matrixCoefficientProfile T0 T1 t0 t1) =
      signedMatrixProfileWord s' y' (matrixHalfCycleProfile S0 S1) := by
    funext c b
    change signedOrderedPauli (s c b) (y c b) * matrixCoefficientProfile T0 T1 t0 t1 c b =
      signedOrderedPauli (s' c b) (y' c b) * matrixHalfCycleProfile S0 S1 c b
    rw [hRaw c b, ← mul_assoc, signedOrderedPauli_mul]
  rw [hf]
  exact matrixHalfCycle_endpoint hScomm hS0 hS1 A B ka kb hA2 hB2 hcross hA hB
    sa sb pa pb hpa hpb hHermA hHermB W hFixA hFixB s' y' hy'

end MatrixPairedPhysicalTerminal
end QuantumProver.ControlledCliffordHierarchy

open scoped Matrix BigOperators
namespace QuantumProver.ControlledCliffordHierarchy

section MatrixCoefficientUpperInduction
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {n : ℕ}

theorem controlQuad_linear_map {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (L : V →ₗ[ZMod 2] W) (y : ZMod 2 → ZMod 2 → V) :
    controlQuad (fun c b => L (y c b)) = L (controlQuad y) := by
  simp only [controlQuad, map_add]

theorem matrixPairedCoefficientNextLabel_pair
    (E : (V × V) ≃ₗ[ZMod 2] PauliLabel n) (N : Module.End (ZMod 2) V)
    (h : ℕ) (t0 t1 : ControlExponentCoefficients)
    (y : ZMod 2 → ZMod 2 → PauliLabel n) (ac ab : ZMod 2) (p : PauliLabel n) :
    matrixCoefficientNextLabel y (matrixPairedIntAction0 E N h)
      (matrixPairedIntAction1 E N h) t0 t1 ac ab p =
      (fun c b => E (labelProfileStep (fun c b => E.symm (y c b))
        (pairedCoefficientAction N h t0 t1)
        (pairedCoefficientDifference N h t0 t1 (ac, ab)) ac ab (E.symm p) c b)) := by
  have hF (c b : ZMod 2) :
      matrixCoefficientPauliAction (matrixPairedIntAction0 E N h)
        (matrixPairedIntAction1 E N h) t0 t1 c b =
          matrixLabelTransport E (pairedCoefficientAction N h t0 t1 c b) := by
    exact matrixPairedIntAction_pair E N h _ _
  have hG (c b : ZMod 2) :
      matrixCoefficientDifferencePauliAction (matrixPairedIntAction0 E N h)
        (matrixPairedIntAction1 E N h) t0 t1 ac ab c b =
          matrixLabelTransport E (pairedCoefficientDifference N h t0 t1 (ac, ab) c b) := by
    exact matrixPairedIntAction_pair E N h _ _
  funext c b
  simp only [matrixCoefficientNextLabel, labelProfileStep, hF, hG,
    matrixLabelTransport_apply, map_add, LinearEquiv.apply_symm_apply]

theorem matrixPairedCoefficientNextLabel_quad_mem
    (E : (V × V) ≃ₗ[ZMod 2] PauliLabel n) (N : Module.End (ZMod 2) V)
    {h j : ℕ} (hj : j + 1 ≤ h) (hN : N ^ (2 ^ h) = 0)
    (t0 t1 : ControlExponentCoefficients)
    (ht0 : controlExponentDepth j t0) (ht1 : controlExponentDepth j t1)
    (y : ZMod 2 → ZMod 2 → PauliLabel n)
    (hy : controlQuad y ∈ matrixPairedImage E N (2 ^ j))
    (ac ab : ZMod 2) (p : PauliLabel n) :
    controlQuad (matrixCoefficientNextLabel y (matrixPairedIntAction0 E N h)
      (matrixPairedIntAction1 E N h) t0 t1 ac ab p) ∈
        matrixPairedImage E N (2 ^ (j + 1)) := by
  obtain ⟨v, hv, he⟩ := hy
  have hyp : controlQuad (fun c b => E.symm (y c b)) ∈
      augmentationImage (pairedAugmentation N) (2 ^ j) := by
    change controlQuad (fun c b => E.symm.toLinearMap (y c b)) ∈ _
    rw [controlQuad_linear_map E.symm.toLinearMap y]
    change E.symm (controlQuad y) ∈ _
    change E v = controlQuad y at he
    rw [← he, LinearEquiv.symm_apply_apply]
    exact hv
  let yp := labelProfileStep (fun c b => E.symm (y c b))
    (pairedCoefficientAction N h t0 t1)
    (pairedCoefficientDifference N h t0 t1 (ac, ab)) ac ab (E.symm p)
  have hqp : controlQuad yp ∈ augmentationImage (pairedAugmentation N) (2 ^ (j + 1)) :=
    pairedCoefficient_labelProfileStep_mem N hj hN t0 t1 ht0 ht1
      (fun c b => E.symm (y c b)) hyp ac ab (E.symm p)
  refine ⟨controlQuad yp, hqp, ?_⟩
  rw [matrixPairedCoefficientNextLabel_pair E N h t0 t1 y ac ab p]
  exact (controlQuad_linear_map E.toLinearMap yp).symm

theorem matrixPairedCoefficient_upper_by_depth {h : ℕ} (hh : 1 ≤ h)
    (E : (V × V) ≃ₗ[ZMod 2] PauliLabel n) (N : Module.End (ZMod 2) V)
    (hN : N ^ (2 ^ h) = 0) (T0 T1 : MatrixUnitary n) (hcomm : Commute T0 T1)
    (hT0 : hierarchy n 2 (T0 : QuantumMatrix n)) (hT1 : hierarchy n 2 (T1 : QuantumMatrix n))
    (k0 k1 : ℤ → PauliLabel n → ZMod 2)
    (h0 : ∀ t p, conjugate (matrixZpow T0 t) (orderedPauli p.1 p.2) =
      bitSign (k0 t p) • orderedPauli (matrixPairedIntAction0 E N h t p).1
        (matrixPairedIntAction0 E N h t p).2)
    (h1 : ∀ t p, conjugate (matrixZpow T1 t) (orderedPauli p.1 p.2) =
      bitSign (k1 t p) • orderedPauli (matrixPairedIntAction1 E N h t p).1
        (matrixPairedIntAction1 E N h t p).2)
    (sq0 sq1 : ZMod 2) (pq0 pq1 : PauliLabel n)
    (hp0 : ((T0 ^ (2 ^ h) : MatrixUnitary n) : QuantumMatrix n) = signedOrderedPauli sq0 pq0)
    (hp1 : ((T1 ^ (2 ^ h) : MatrixUnitary n) : QuantumMatrix n) = signedOrderedPauli sq1 pq1)
    (hh0 : dot pq0.2 pq0.1 = 0) (hh1 : dot pq1.2 pq1.1 = 0)
    (hpW0 : pq0 ∈ matrixPairedImage E N (2 ^ (h - 1)))
    (hpW1 : pq1 ∈ matrixPairedImage E N (2 ^ (h - 1)))
    (j : ℕ) (hj : j ≤ h - 1) (t0 t1 : ControlExponentCoefficients)
    (ht0 : controlExponentDepth j t0) (ht1 : controlExponentDepth j t1)
    (s : ZMod 2 → ZMod 2 → ZMod 2) (y : ZMod 2 → ZMod 2 → PauliLabel n)
    (hy : controlQuad y ∈ matrixPairedImage E N (2 ^ j)) :
    hierarchy ((n + 1) + 1) (h - j + 2)
      (twoControlMatrix (signedMatrixProfileWord s y (matrixCoefficientProfile T0 T1 t0 t1))) := by
  have bound : ∀ d j : ℕ, h = j + d + 1 →
      ∀ t0 t1 : ControlExponentCoefficients,
      controlExponentDepth j t0 → controlExponentDepth j t1 →
      ∀ (s : ZMod 2 → ZMod 2 → ZMod 2) (y : ZMod 2 → ZMod 2 → PauliLabel n),
      controlQuad y ∈ matrixPairedImage E N (2 ^ j) →
      hierarchy ((n + 1) + 1) (d + 3)
        (twoControlMatrix (signedMatrixProfileWord s y (matrixCoefficientProfile T0 T1 t0 t1))) := by
    intro d
    induction d with
    | zero =>
      intro j he t0 t1 ht0 ht1 s y hy
      have hj' : j = h - 1 := by omega
      subst j
      simpa only [zero_add] using matrixPairedCoefficient_terminal hh E N hN T0 T1 hcomm
        hT0 hT1 k0 k1 h0 h1 sq0 sq1 pq0 pq1 hp0 hp1 hh0 hh1 hpW0 hpW1
        t0 t1 ht0 ht1 s y hy
    | succ d ih =>
      intro j he t0 t1 ht0 ht1 s y hy
      have hstep : j + 1 ≤ h := by omega
      change hierarchy ((n + 1) + 1) ((d + 2) + 2) _
      apply (hierarchy_iff_pauliCorrections _).mpr
      refine ⟨twoControlMatrix_unitary _ (fun c b =>
        unitaryMatrix_mul (actualPauli_unitary (signedOrderedPauli_actual _ _))
          (matrixShiftProfile_unitary _ _ _ _ c b)), ?_⟩
      intro P hP
      rcases hP with ⟨v, x, z, hv, rfl⟩
      obtain ⟨⟨ac, x⟩, rfl⟩ := (controlBasisEquiv (n + 1)).symm.surjective x
      obtain ⟨⟨ab, x⟩, rfl⟩ := (controlBasisEquiv n).symm.surjective x
      obtain ⟨⟨zc, z⟩, rfl⟩ := (controlBasisEquiv (n + 1)).symm.surjective z
      obtain ⟨⟨zb, z⟩, rfl⟩ := (controlBasisEquiv n).symm.surjective z
      change hierarchy ((n + 1) + 1) (d + 3)
        (pauliCorrection (twoControlMatrix
          (signedMatrixProfileWord s y (matrixCoefficientProfile T0 T1 t0 t1)))
          (v • orderedPauli (basisCons ac (basisCons ab x))
            (basisCons zc (basisCons zb z))))
      rw [matrixCoefficientProfile_actualPauli_correction hcomm
        (matrixPairedIntAction0 E N h) (matrixPairedIntAction1 E N h)
        k0 k1 h0 h1 s y t0 t1 ac ab zc zb x z hv]
      apply hierarchy_clifford_mul_right (by omega)
        (matrixCoefficientProfile_normalization_clifford hT0 hT1 t0 t1 ac ab)
      have hyn := matrixPairedCoefficientNextLabel_quad_mem E N hstep hN t0 t1
        ht0 ht1 y hy ac ab (x, z)
      exact ih (j + 1) (by omega)
        (controlExponentStep t0 (ac, ab)) (controlExponentStep t1 (ac, ab))
        (controlExponentStep_depth j t0 (ac, ab) ht0)
        (controlExponentStep_depth j t1 (ac, ab) ht1)
        (matrixCoefficientNextSign s y (matrixPairedIntAction0 E N h)
          (matrixPairedIntAction1 E N h) k0 k1 t0 t1 ac ab (x, z))
        (matrixCoefficientNextLabel y (matrixPairedIntAction0 E N h)
          (matrixPairedIntAction1 E N h) t0 t1 ac ab (x, z)) hyn
  have he : h = j + (h - 1 - j) + 1 := by omega
  have hr : h - 1 - j + 3 = h - j + 2 := by omega
  simpa only [hr] using bound (h - 1 - j) j he t0 t1 ht0 ht1 s y hy

end MatrixCoefficientUpperInduction
end QuantumProver.ControlledCliffordHierarchy

namespace QuantumProver.ControlledCliffordHierarchy

structure MatrixFullSignedActionB {n : ℕ} (U : MatrixUnitary n) where
  label : Module.End (ZMod 2) (PauliLabel n)
  sign : PauliLabel n → ZMod 2
  act : ∀ p, conjugate (U : QuantumMatrix n) (orderedPauli p.1 p.2) =
    bitSign (sign p) • orderedPauli (label p).1 (label p).2

namespace MatrixFullSignedActionB

def one (n : ℕ) : MatrixFullSignedActionB (1 : MatrixUnitary n) where
  label := 1
  sign := fun _ => 0
  act := by
    intro p
    simp only [Submonoid.coe_one, conjugate, Matrix.conjTranspose_one,
      one_mul, mul_one, bitSign_zero, one_smul, Module.End.one_apply]

def mul {n : ℕ} {U V : MatrixUnitary n}
    (D : MatrixFullSignedActionB U) (E : MatrixFullSignedActionB V) :
    MatrixFullSignedActionB (U * V) where
  label := D.label * E.label
  sign := fun p => E.sign p + D.sign (E.label p)
  act := by
    intro p
    simp only [Submonoid.coe_mul, conjugate_comp, E.act, conjugate_smul_right,
      D.act, smul_smul, bitSign_add, Module.End.mul_apply]

theorem label_injective {n : ℕ} {U : MatrixUnitary n}
    (D : MatrixFullSignedActionB U) : Function.Injective D.label := by
  intro p q hpq
  have he : conjugate (U : QuantumMatrix n) (orderedPauli p.1 p.2) =
      (bitSign (D.sign p) * bitSign (D.sign q)) •
        conjugate (U : QuantumMatrix n) (orderedPauli q.1 q.2) := by
    rw [D.act p, D.act q, hpq, smul_smul]
    simp only [mul_assoc, bitSign_mul_self, mul_one]
  have hi := congrArg (conjugate (U : QuantumMatrix n).conjTranspose) he
  rw [conjugate_inverse_left (matrixUnitary_unitary U), conjugate_smul_right,
    conjugate_inverse_left (matrixUnitary_unitary U)] at hi
  exact orderedPauli_projective_label_eq hi

def labelEquiv {n : ℕ} {U : MatrixUnitary n}
    (D : MatrixFullSignedActionB U) : PauliLabel n ≃ₗ[ZMod 2] PauliLabel n :=
  LinearEquiv.ofBijective D.label
    ⟨D.label_injective, Finite.surjective_of_injective D.label_injective⟩

def inv {n : ℕ} {U : MatrixUnitary n}
    (D : MatrixFullSignedActionB U) : MatrixFullSignedActionB U⁻¹ where
  label := D.labelEquiv.symm.toLinearMap
  sign := fun p => D.sign (D.labelEquiv.symm p)
  act := by
    intro p
    have hlabel : D.label (D.labelEquiv.symm p) = p :=
      D.labelEquiv.apply_symm_apply p
    have hi := congrArg (conjugate (U : QuantumMatrix n).conjTranspose)
      (D.act (D.labelEquiv.symm p))
    rw [conjugate_inverse_left (matrixUnitary_unitary U), hlabel,
      conjugate_smul_right] at hi
    rw [matrixUnitary_inv_coe]
    change conjugate (U : QuantumMatrix n).conjTranspose (orderedPauli p.1 p.2) =
      bitSign (D.sign (D.labelEquiv.symm p)) •
        orderedPauli (D.labelEquiv.symm p).1 (D.labelEquiv.symm p).2
    calc
      _ = bitSign (D.sign (D.labelEquiv.symm p)) •
          (bitSign (D.sign (D.labelEquiv.symm p)) •
            conjugate (U : QuantumMatrix n).conjTranspose (orderedPauli p.1 p.2)) := by
        rw [smul_smul, bitSign_mul_self, one_smul]
      _ = _ := by rw [← hi]

theorem label_inv_mul {n : ℕ} {U : MatrixUnitary n}
    (D : MatrixFullSignedActionB U) : D.label * D.inv.label = 1 := by
  apply LinearMap.ext
  intro p
  change D.label (D.labelEquiv.symm p) = p
  exact D.labelEquiv.apply_symm_apply p

def bit {n : ℕ} {U : MatrixUnitary n}
    (D : MatrixFullSignedActionB U) (e : ZMod 2) :
    MatrixFullSignedActionB (matrixInvolutionBit U e) where
  label := halfCycleBinaryAction D.label e
  sign := fun p => if e = 0 then 0 else D.sign p
  act := by
    intro p
    exact matrixZpow_bit_signed_action D.label D.sign D.act e p

end MatrixFullSignedActionB

def matrixGroupDifferenceActionB {n : ℕ}
    {F : ZMod 2 → ZMod 2 → MatrixUnitary n}
    (D : ∀ c b, MatrixFullSignedActionB (F c b)) (ac ab c b : ZMod 2) :
    MatrixFullSignedActionB (F c b * (F (c + ac) (b + ab))⁻¹) :=
  (D c b).mul (D (c + ac) (b + ab)).inv

def matrixGroupNextSignB {n : ℕ}
    {F : ZMod 2 → ZMod 2 → MatrixUnitary n}
    (D : ∀ c b, MatrixFullSignedActionB (F c b))
    (s : ZMod 2 → ZMod 2 → ZMod 2) (y : ZMod 2 → ZMod 2 → PauliLabel n)
    (ac ab : ZMod 2) (p : PauliLabel n) :=
  matrixProfileNextSign s y (fun c b => (D c b).label)
    (fun c b => (matrixGroupDifferenceActionB D ac ab c b).label)
    (fun c b => (D c b).sign)
    (fun c b => (matrixGroupDifferenceActionB D ac ab c b).sign) ac ab p

def matrixGroupNextLabelB {n : ℕ}
    {F : ZMod 2 → ZMod 2 → MatrixUnitary n}
    (D : ∀ c b, MatrixFullSignedActionB (F c b))
    (y : ZMod 2 → ZMod 2 → PauliLabel n) (ac ab : ZMod 2) (p : PauliLabel n) :=
  labelProfileStep y (fun c b => (D c b).label)
    (fun c b => (matrixGroupDifferenceActionB D ac ab c b).label) ac ab p

theorem matrixGroupProfile_actualPauli_normalizedB {n : ℕ}
    (F : ZMod 2 → ZMod 2 → MatrixUnitary n)
    (D : ∀ c b, MatrixFullSignedActionB (F c b))
    (s : ZMod 2 → ZMod 2 → ZMod 2) (y : ZMod 2 → ZMod 2 → PauliLabel n)
    (ac ab zc zb : ZMod 2) (x z : BitString n) {a : ℂ} (ha : PauliPhase a) :
    pauliCorrection (twoControlMatrix
        (signedMatrixProfileWord s y (fun c b => (F c b : QuantumMatrix n))))
      (a • orderedPauli (basisCons ac (basisCons ab x)) (basisCons zc (basisCons zb z))) =
      twoControlMatrix (signedMatrixProfileWord
        (matrixGroupNextSignB D s y ac ab (x, z))
        (matrixGroupNextLabelB D y ac ab (x, z))
        (fun c b => (matrixGroupProfileNormalized F ac ab c b : QuantumMatrix n))) *
        twoControlMatrix (fun _ _ => (F ac ab : QuantumMatrix n).conjTranspose) := by
  have hG : ∀ c b p, conjugate
      (matrixProfileDifference (fun c b => (F c b : QuantumMatrix n)) ac ab c b)
        (orderedPauli p.1 p.2) =
      bitSign ((matrixGroupDifferenceActionB D ac ab c b).sign p) •
        orderedPauli ((matrixGroupDifferenceActionB D ac ab c b).label p).1
          ((matrixGroupDifferenceActionB D ac ab c b).label p).2 := by
    intro c b p
    simpa only [matrixProfileDifference, Submonoid.coe_mul, matrixUnitary_inv_coe]
      using (matrixGroupDifferenceActionB D ac ab c b).act p
  rw [twoControlMatrix_actualPauli_correction _ ac ab zc zb x z ha,
    signedMatrixProfile_correction s y (fun c b => (F c b : QuantumMatrix n))
      (fun c b => (D c b).label)
      (fun c b => (matrixGroupDifferenceActionB D ac ab c b).label)
      (fun c b => (D c b).sign)
      (fun c b => (matrixGroupDifferenceActionB D ac ab c b).sign) ac ab
      (fun c b => matrixUnitary_unitary (F c b))
      (fun c b => (D c b).act) hG (x, z), twoControlMatrix_mul]
  congr 1
  funext c b
  change signedOrderedPauli _ _ *
      ((F c b : QuantumMatrix n) * (F (c + ac) (b + ab) : QuantumMatrix n).conjTranspose) =
    (signedOrderedPauli _ _ *
      (matrixGroupProfileNormalized F ac ab c b : QuantumMatrix n)) *
        (F ac ab : QuantumMatrix n).conjTranspose
  rw [matrixGroupProfileNormalized_coe]
  simp only [matrixGroupNextSignB, matrixGroupNextLabelB, mul_assoc,
    (matrixUnitary_unitary (F ac ab)).2, mul_one]

theorem matrixGroupProfile_normalization_cliffordB {n : ℕ}
    (F : ZMod 2 → ZMod 2 → MatrixUnitary n)
    (hF : ∀ c b, hierarchy n 2 (F c b : QuantumMatrix n)) (ac ab : ZMod 2) :
    hierarchy ((n + 1) + 1) 2
      (twoControlMatrix (fun _ _ => (F ac ab : QuantumMatrix n).conjTranspose)) :=
  hierarchy_lift (by omega) (hierarchy_lift (by omega) (clifford_conjTranspose (hF ac ab)))

theorem matrixGroupNextLabel_quad_memB {n : ℕ}
    (W : Submodule (ZMod 2) (PauliLabel n))
    {F : ZMod 2 → ZMod 2 → MatrixUnitary n}
    (D : ∀ c b, MatrixFullSignedActionB (F c b))
    (hD : ∀ c b, labelMapTrivialModulo W (D c b).label)
    (y : ZMod 2 → ZMod 2 → PauliLabel n) (ac ab : ZMod 2) (p : PauliLabel n) :
    controlQuad (matrixGroupNextLabelB D y ac ab p) ∈ W := by
  apply labelProfileStep_identity_mod_quad_mem W y _ _ hD
  intro c b
  exact labelMapTrivialModulo_mul W (hD c b)
    (labelMapTrivialModulo_right_inverse W (hD (c + ac) (b + ab))
      (D (c + ac) (b + ab)).label_inv_mul)

end QuantumProver.ControlledCliffordHierarchy

namespace QuantumProver.ControlledCliffordHierarchy
section MatrixFullSelectorUpperB
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {n : ℕ}

def matrixPairedSignedAction0B (E : (V × V) ≃ₗ[ZMod 2] PauliLabel n)
    (N : Module.End (ZMod 2) V) (h : ℕ) (T : MatrixUnitary n)
    (k : ℤ → PauliLabel n → ZMod 2)
    (hk : ∀ t p, conjugate (matrixZpow T t) (orderedPauli p.1 p.2) =
      bitSign (k t p) • orderedPauli (matrixPairedIntAction0 E N h t p).1
        (matrixPairedIntAction0 E N h t p).2) (t : ℤ) :
    MatrixFullSignedActionB (T ^ t) where
  label := matrixPairedIntAction0 E N h t
  sign := k t
  act := hk t

def matrixPairedSignedAction1B (E : (V × V) ≃ₗ[ZMod 2] PauliLabel n)
    (N : Module.End (ZMod 2) V) (h : ℕ) (T : MatrixUnitary n)
    (k : ℤ → PauliLabel n → ZMod 2)
    (hk : ∀ t p, conjugate (matrixZpow T t) (orderedPauli p.1 p.2) =
      bitSign (k t p) • orderedPauli (matrixPairedIntAction1 E N h t p).1
        (matrixPairedIntAction1 E N h t p).2) (t : ℤ) :
    MatrixFullSignedActionB (T ^ t) where
  label := matrixPairedIntAction1 E N h t
  sign := k t
  act := hk t

theorem matrixLabelTransport_trivialModuloB {W : Type*} [AddCommGroup W]
    [Module (ZMod 2) W] (E : V ≃ₗ[ZMod 2] W)
    (S : Submodule (ZMod 2) V) (L : Module.End (ZMod 2) V)
    (hL : labelMapTrivialModulo S L) :
    labelMapTrivialModulo (S.map E.toLinearMap) (matrixLabelTransport E L) := by
  intro p
  refine ⟨(L - 1) (E.symm p), hL (E.symm p), ?_⟩
  change E ((L - 1) (E.symm p)) = (matrixLabelTransport E L - 1) p
  simp only [LinearMap.sub_apply, Module.End.one_apply,
    matrixLabelTransport_apply, map_sub, LinearEquiv.apply_symm_apply]

def matrixInversionProfile_fullActionB
    (E : (V × V) ≃ₗ[ZMod 2] PauliLabel n) (N : Module.End (ZMod 2) V)
    (h : ℕ) (T0 T1 K : MatrixUnitary n)
    (k0 k1 : ℤ → PauliLabel n → ZMod 2)
    (h0 : ∀ t p, conjugate (matrixZpow T0 t) (orderedPauli p.1 p.2) =
      bitSign (k0 t p) • orderedPauli (matrixPairedIntAction0 E N h t p).1
        (matrixPairedIntAction0 E N h t p).2)
    (h1 : ∀ t p, conjugate (matrixZpow T1 t) (orderedPauli p.1 p.2) =
      bitSign (k1 t p) • orderedPauli (matrixPairedIntAction1 E N h t p).1
        (matrixPairedIntAction1 E N h t p).2)
    (DK : MatrixFullSignedActionB K) (t0 t1 : ControlExponentCoefficients)
    (rc rb c b : ZMod 2) :
    MatrixFullSignedActionB (matrixInversionProfile T0 T1 K t0 t1 rc rb c b) :=
  ((matrixPairedSignedAction0B E N h T0 k0 h0 (controlExponentFunction t0 (c, b))).mul
    (matrixPairedSignedAction1B E N h T1 k1 h1 (controlExponentFunction t1 (c, b)))).mul
    (DK.bit (matrixInversionControl rc rb c b))

theorem matrixInversionProfile_fullAction_trivialB
    (E : (V × V) ≃ₗ[ZMod 2] PauliLabel n) (N : Module.End (ZMod 2) V)
    (h : ℕ) (T0 T1 K : MatrixUnitary n)
    (k0 k1 : ℤ → PauliLabel n → ZMod 2)
    (h0 : ∀ t p, conjugate (matrixZpow T0 t) (orderedPauli p.1 p.2) =
      bitSign (k0 t p) • orderedPauli (matrixPairedIntAction0 E N h t p).1
        (matrixPairedIntAction0 E N h t p).2)
    (h1 : ∀ t p, conjugate (matrixZpow T1 t) (orderedPauli p.1 p.2) =
      bitSign (k1 t p) • orderedPauli (matrixPairedIntAction1 E N h t p).1
        (matrixPairedIntAction1 E N h t p).2)
    (DK : MatrixFullSignedActionB K)
    (hDK : labelMapTrivialModulo (matrixPairedImage E N 1) DK.label)
    (t0 t1 : ControlExponentCoefficients) (rc rb c b : ZMod 2) :
    labelMapTrivialModulo (matrixPairedImage E N 1)
      (matrixInversionProfile_fullActionB E N h T0 T1 K k0 k1 h0 h1 DK t0 t1 rc rb c b).label := by
  change labelMapTrivialModulo (matrixPairedImage E N 1)
    ((matrixPairedIntAction0 E N h (controlExponentFunction t0 (c, b)) *
      matrixPairedIntAction1 E N h (controlExponentFunction t1 (c, b))) *
        halfCycleBinaryAction DK.label (matrixInversionControl rc rb c b))
  rw [matrixPairedIntAction_pair]
  apply labelMapTrivialModulo_mul
  · exact matrixLabelTransport_trivialModuloB E _ _
      (pairedResidualLabelAction_trivialModulo N h _ _)
  · unfold halfCycleBinaryAction
    split
    · exact labelMapTrivialModulo_one _
    · exact hDK

theorem matrixInversionProfile_cliffordB
    (T0 T1 K : MatrixUnitary n)
    (hT0 : hierarchy n 2 (T0 : QuantumMatrix n))
    (hT1 : hierarchy n 2 (T1 : QuantumMatrix n))
    (hK : hierarchy n 2 (K : QuantumMatrix n))
    (t0 t1 : ControlExponentCoefficients) (rc rb c b : ZMod 2) :
    hierarchy n 2 (matrixInversionProfile T0 T1 K t0 t1 rc rb c b : QuantumMatrix n) := by
  change hierarchy n 2
    ((matrixZpow T0 (controlExponentFunction t0 (c, b)) *
      matrixZpow T1 (controlExponentFunction t1 (c, b))) *
        matrixZpow K (controlExponentBit (matrixInversionControl rc rb c b)))
  exact hierarchy_clifford_mul_right (by omega) (hierarchy_clifford_matrixZpow hK _)
    (matrixShiftProfile_constant_clifford hT0 hT1 _ _)

theorem matrixInversionProfile_twoControl_upperB {h : ℕ} (hh : 1 ≤ h)
    (E : (V × V) ≃ₗ[ZMod 2] PauliLabel n) (N : Module.End (ZMod 2) V)
    (hN : N ^ (2 ^ h) = 0) (T0 T1 K : MatrixUnitary n)
    (hcomm : Commute T0 T1) (hKsq : K ^ (2 : ℕ) = 1)
    (hK0 : K * T0 * K⁻¹ = T0⁻¹) (hK1 : K * T1 * K⁻¹ = T1⁻¹)
    (hT0 : hierarchy n 2 (T0 : QuantumMatrix n))
    (hT1 : hierarchy n 2 (T1 : QuantumMatrix n)) (hK : hierarchy n 2 (K : QuantumMatrix n))
    (k0 k1 : ℤ → PauliLabel n → ZMod 2)
    (h0 : ∀ t p, conjugate (matrixZpow T0 t) (orderedPauli p.1 p.2) =
      bitSign (k0 t p) • orderedPauli (matrixPairedIntAction0 E N h t p).1
        (matrixPairedIntAction0 E N h t p).2)
    (h1 : ∀ t p, conjugate (matrixZpow T1 t) (orderedPauli p.1 p.2) =
      bitSign (k1 t p) • orderedPauli (matrixPairedIntAction1 E N h t p).1
        (matrixPairedIntAction1 E N h t p).2)
    (sq0 sq1 : ZMod 2) (pq0 pq1 : PauliLabel n)
    (hp0 : ((T0 ^ (2 ^ h) : MatrixUnitary n) : QuantumMatrix n) = signedOrderedPauli sq0 pq0)
    (hp1 : ((T1 ^ (2 ^ h) : MatrixUnitary n) : QuantumMatrix n) = signedOrderedPauli sq1 pq1)
    (hh0 : dot pq0.2 pq0.1 = 0) (hh1 : dot pq1.2 pq1.1 = 0)
    (hpW0 : pq0 ∈ matrixPairedImage E N (2 ^ (h - 1)))
    (hpW1 : pq1 ∈ matrixPairedImage E N (2 ^ (h - 1)))
    (DK : MatrixFullSignedActionB K)
    (hDK : labelMapTrivialModulo (matrixPairedImage E N 1) DK.label)
    (t0 t1 : ControlExponentCoefficients) (rc rb : ZMod 2)
    (s : ZMod 2 → ZMod 2 → ZMod 2) (y : ZMod 2 → ZMod 2 → PauliLabel n) :
    hierarchy ((n + 1) + 1) (h + 3)
      (twoControlMatrix (signedMatrixProfileWord s y
        (fun c b => (matrixInversionProfile T0 T1 K t0 t1 rc rb c b : QuantumMatrix n)))) := by
  let F := matrixInversionProfile T0 T1 K t0 t1 rc rb
  let D := matrixInversionProfile_fullActionB E N h T0 T1 K k0 k1 h0 h1 DK t0 t1 rc rb
  have hF := matrixInversionProfile_cliffordB T0 T1 K hT0 hT1 hK t0 t1 rc rb
  have hD := matrixInversionProfile_fullAction_trivialB E N h T0 T1 K
    k0 k1 h0 h1 DK hDK t0 t1 rc rb
  change hierarchy ((n + 1) + 1) ((h + 1) + 2) _
  apply (hierarchy_iff_pauliCorrections _).mpr
  refine ⟨twoControlMatrix_unitary _ (fun c b =>
    unitaryMatrix_mul (actualPauli_unitary (signedOrderedPauli_actual _ _))
      (matrixUnitary_unitary (F c b))), ?_⟩
  intro P hP
  rcases hP with ⟨v, x, z, hv, rfl⟩
  obtain ⟨⟨ac, x⟩, rfl⟩ := (controlBasisEquiv (n + 1)).symm.surjective x
  obtain ⟨⟨ab, x⟩, rfl⟩ := (controlBasisEquiv n).symm.surjective x
  obtain ⟨⟨zc, z⟩, rfl⟩ := (controlBasisEquiv (n + 1)).symm.surjective z
  obtain ⟨⟨zb, z⟩, rfl⟩ := (controlBasisEquiv n).symm.surjective z
  change hierarchy ((n + 1) + 1) (h + 2)
    (pauliCorrection (twoControlMatrix (signedMatrixProfileWord s y (fun c b => (F c b : QuantumMatrix n))))
      (v • orderedPauli (basisCons ac (basisCons ab x)) (basisCons zc (basisCons zb z))))
  rw [matrixGroupProfile_actualPauli_normalizedB F D s y ac ab zc zb x z hv]
  apply hierarchy_clifford_mul_right (by omega)
    (matrixGroupProfile_normalization_cliffordB F hF ac ab)
  let delta := matrixInversionSign (matrixInversionControl rc rb ac ab)
  let t0' := matrixInversionCoefficientStep t0 delta (controlExponentBit ac) (controlExponentBit ab)
  let t1' := matrixInversionCoefficientStep t1 delta (controlExponentBit ac) (controlExponentBit ab)
  have hFn : (fun c b => (matrixGroupProfileNormalized F ac ab c b : QuantumMatrix n)) =
      matrixCoefficientProfile T0 T1 t0' t1' := by
    funext c b
    dsimp only [F]
    rw [matrixInversionProfile_normalized hcomm hKsq hK0 hK1,
      matrixInversionCoefficient_bit_function, matrixInversionCoefficient_bit_function]
    rfl
  rw [hFn]
  have hy := matrixGroupNextLabel_quad_memB (matrixPairedImage E N 1) D hD y ac ab (x, z)
  have ht0 := matrixInversionCoefficient_depth_zero t0
    (matrixInversionControl rc rb ac ab) (controlExponentBit ac) (controlExponentBit ab)
  have ht1 := matrixInversionCoefficient_depth_zero t1
    (matrixInversionControl rc rb ac ab) (controlExponentBit ac) (controlExponentBit ab)
  simpa only [Nat.sub_zero, Nat.pow_zero] using
    matrixPairedCoefficient_upper_by_depth hh E N hN T0 T1 hcomm hT0 hT1 k0 k1 h0 h1
      sq0 sq1 pq0 pq1 hp0 hp1 hh0 hh1 hpW0 hpW1 0 (by omega) t0' t1' ht0 ht1
      (matrixGroupNextSignB D s y ac ab (x, z)) (matrixGroupNextLabelB D y ac ab (x, z)) hy

def matrixSquareSignedActionB {U : MatrixUnitary n} (D : MatrixFullSignedActionB U) :
    MatrixFullSignedActionB (U ^ (2 : ℕ)) where
  label := D.label ^ (2 : ℕ)
  sign := fun p => D.sign p + D.sign (D.label p)
  act := by
    intro p
    simpa only [pow_two, Submonoid.coe_mul, MatrixFullSignedActionB.mul,
      Module.End.mul_apply] using (D.mul D).act p

def matrixSelectorSignedActionB {S T1 : MatrixUnitary n}
    (DS : MatrixFullSignedActionB S) (D1 : MatrixFullSignedActionB T1) (c b : ZMod 2) :
    MatrixFullSignedActionB (matrixSelectorWord S T1 c b) := by
  classical
  by_cases hc : c = 0
  · simp only [matrixSelectorWord, hc, ite_true]
    exact MatrixFullSignedActionB.one n
  · by_cases hb : b = 0
    · simp only [matrixSelectorWord, hc, hb, ite_false, ite_true]
      exact DS
    · simp only [matrixSelectorWord, hc, hb, ite_false]
      exact D1.mul DS.inv

theorem matrixSelectorWord_cliffordB (S T1 : MatrixUnitary n)
    (hS : hierarchy n 2 (S : QuantumMatrix n)) (hT1 : hierarchy n 2 (T1 : QuantumMatrix n))
    (c b : ZMod 2) : hierarchy n 2 (matrixSelectorWord S T1 c b : QuantumMatrix n) := by
  classical
  by_cases hc : c = 0
  · simp only [matrixSelectorWord, hc, ite_true, Submonoid.coe_one]
    exact actualPauli_hierarchy (by omega) (actualPauli_one n)
  · by_cases hb : b = 0
    · simpa only [matrixSelectorWord, hc, hb, ite_false, ite_true] using hS
    · simp only [matrixSelectorWord, hc, hb, ite_false, Submonoid.coe_mul,
        matrixUnitary_inv_coe]
      exact hierarchy_clifford_mul_left (by omega) hT1 (clifford_conjTranspose hS)

theorem matrixSelectorWord_twoControl_upper {h : ℕ} (hh : 1 ≤ h)
    (E : (V × V) ≃ₗ[ZMod 2] PauliLabel n) (N : Module.End (ZMod 2) V)
    (hN : N ^ (2 ^ h) = 0) (S T0 T1 : MatrixUnitary n)
    (hcomm : Commute T0 T1) (hS4 : S ^ (4 : ℕ) = 1)
    (hST0 : S * T0 * S⁻¹ = T1) (hST1 : S * T1 * S⁻¹ = T0⁻¹)
    (hS : hierarchy n 2 (S : QuantumMatrix n))
    (hT0 : hierarchy n 2 (T0 : QuantumMatrix n)) (hT1 : hierarchy n 2 (T1 : QuantumMatrix n))
    (k0 k1 : ℤ → PauliLabel n → ZMod 2)
    (h0 : ∀ t p, conjugate (matrixZpow T0 t) (orderedPauli p.1 p.2) =
      bitSign (k0 t p) • orderedPauli (matrixPairedIntAction0 E N h t p).1
        (matrixPairedIntAction0 E N h t p).2)
    (h1 : ∀ t p, conjugate (matrixZpow T1 t) (orderedPauli p.1 p.2) =
      bitSign (k1 t p) • orderedPauli (matrixPairedIntAction1 E N h t p).1
        (matrixPairedIntAction1 E N h t p).2)
    (sq0 sq1 : ZMod 2) (pq0 pq1 : PauliLabel n)
    (hp0 : ((T0 ^ (2 ^ h) : MatrixUnitary n) : QuantumMatrix n) = signedOrderedPauli sq0 pq0)
    (hp1 : ((T1 ^ (2 ^ h) : MatrixUnitary n) : QuantumMatrix n) = signedOrderedPauli sq1 pq1)
    (hh0 : dot pq0.2 pq0.1 = 0) (hh1 : dot pq1.2 pq1.1 = 0)
    (hpW0 : pq0 ∈ matrixPairedImage E N (2 ^ (h - 1)))
    (hpW1 : pq1 ∈ matrixPairedImage E N (2 ^ (h - 1)))
    (LS : Module.End (ZMod 2) (PauliLabel n)) (kS : PauliLabel n → ZMod 2)
    (hSact : ∀ p, conjugate (S : QuantumMatrix n) (orderedPauli p.1 p.2) =
      bitSign (kS p) • orderedPauli (LS p).1 (LS p).2)
    (hKimage : ∀ p, (LS ^ (2 : ℕ) - 1) p ∈ matrixPairedImage E N 1) :
    hierarchy ((n + 1) + 1) (h + 4)
      (twoControlMatrix (fun c b => (matrixSelectorWord S T1 c b : QuantumMatrix n))) := by
  let DS : MatrixFullSignedActionB S := ⟨LS, kS, hSact⟩
  let DK := matrixSquareSignedActionB DS
  let D1 : MatrixFullSignedActionB T1 :=
    { label := matrixPairedIntAction1 E N h (1 : ℤ)
      sign := k1 (1 : ℤ)
      act := by intro p; simpa only [matrixZpow, zpow_one] using h1 (1 : ℤ) p }
  let F := matrixSelectorWord S T1
  let D := matrixSelectorSignedActionB DS D1
  have hF := matrixSelectorWord_cliffordB S T1 hS hT1
  have hK : hierarchy n 2 ((S ^ (2 : ℕ) : MatrixUnitary n) : QuantumMatrix n) := by
    simpa only [pow_two, Submonoid.coe_mul] using
      hierarchy_clifford_mul_left (by omega) hS hS
  have hKsq : (S ^ (2 : ℕ)) ^ (2 : ℕ) = 1 := by
    simpa only [← pow_mul] using hS4
  obtain ⟨hK0, hK1⟩ := matrixQuarterTurn_square_inverts hST0 hST1
  let s := fun (_ _ : ZMod 2) => (0 : ZMod 2)
  let y := fun (_ _ : ZMod 2) => (0 : PauliLabel n)
  have hword : signedMatrixProfileWord s y (fun c b => (F c b : QuantumMatrix n)) =
      (fun c b => (F c b : QuantumMatrix n)) := by
    funext c b
    simp only [signedMatrixProfileWord, s, y, signedOrderedPauli, bitSign_zero, one_smul]
    change orderedPauli (0 : BitString n) 0 * _ = _
    rw [orderedPauli_zero, one_mul]
  rw [← hword]
  change hierarchy ((n + 1) + 1) ((h + 2) + 2) _
  apply (hierarchy_iff_pauliCorrections _).mpr
  refine ⟨twoControlMatrix_unitary _ (fun c b =>
    unitaryMatrix_mul (actualPauli_unitary (signedOrderedPauli_actual _ _))
      (matrixUnitary_unitary (F c b))), ?_⟩
  intro P hP
  rcases hP with ⟨v, x, z, hv, rfl⟩
  obtain ⟨⟨ac, x⟩, rfl⟩ := (controlBasisEquiv (n + 1)).symm.surjective x
  obtain ⟨⟨ab, x⟩, rfl⟩ := (controlBasisEquiv n).symm.surjective x
  obtain ⟨⟨zc, z⟩, rfl⟩ := (controlBasisEquiv (n + 1)).symm.surjective z
  obtain ⟨⟨zb, z⟩, rfl⟩ := (controlBasisEquiv n).symm.surjective z
  change hierarchy ((n + 1) + 1) (h + 3)
    (pauliCorrection (twoControlMatrix (signedMatrixProfileWord s y (fun c b => (F c b : QuantumMatrix n))))
      (v • orderedPauli (basisCons ac (basisCons ab x)) (basisCons zc (basisCons zb z))))
  rw [matrixGroupProfile_actualPauli_normalizedB F D s y ac ab zc zb x z hv]
  apply hierarchy_clifford_mul_right (by omega)
    (matrixGroupProfile_normalization_cliffordB F hF ac ab)
  have hFn : (fun c b => (matrixGroupProfileNormalized F ac ab c b : QuantumMatrix n)) =
      (fun c b => (matrixInversionProfile T0 T1 (S ^ (2 : ℕ))
        (matrixSelectorFirstCoefficient0 ac ab) (matrixSelectorFirstCoefficient1 ac ab)
          (ac + ab) ac c b : QuantumMatrix n)) := by
    funext c b
    exact congrArg (fun U : MatrixUnitary n => (U : QuantumMatrix n))
      (matrixSelectorFirst_inversion_profile hS4 hcomm hST0 hST1 ac ab c b)
  rw [hFn]
  exact matrixInversionProfile_twoControl_upperB hh E N hN T0 T1 (S ^ (2 : ℕ))
    hcomm hKsq hK0 hK1 hT0 hT1 hK k0 k1 h0 h1 sq0 sq1 pq0 pq1 hp0 hp1
    hh0 hh1 hpW0 hpW1 DK hKimage
    (matrixSelectorFirstCoefficient0 ac ab) (matrixSelectorFirstCoefficient1 ac ab) (ac + ab) ac
    (matrixGroupNextSignB D s y ac ab (x, z)) (matrixGroupNextLabelB D y ac ab (x, z))

end MatrixFullSelectorUpperB
end QuantumProver.ControlledCliffordHierarchy

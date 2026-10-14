import QuantumProver.QuantumGates.ControlledCliffordHierarchy.PairedHierarchyUpper
import QuantumProver.QuantumGates.ControlledCliffordHierarchy.ControlledFamily
import QuantumProver.QuantumGates.ControlledCliffordHierarchy.HierarchyBounds
import QuantumProver.QuantumGates.ControlledCliffordHierarchy.DyadicCycle

noncomputable section

open scoped Matrix BigOperators

namespace QuantumProver.ControlledCliffordHierarchy

theorem hierarchy_two_of_implementsPauliLabels {n : ℕ} {U : QuantumMatrix n}
    {F : PauliLabel n → PauliLabel n} (hU : unitaryMatrix U)
    (hF : implementsPauliLabels U F) : hierarchy n 2 U := by
  refine ⟨hU, ?_⟩
  intro P hP
  rcases hP with ⟨a, x, z, ha, rfl⟩
  obtain ⟨b, hb, heq⟩ := hF x z
  change actualPauli (conjugate U (a • orderedPauli x z))
  rw [conjugate_smul_right, heq, smul_smul]
  exact actualPauli_smul (pauliPhase_mul ha hb) (orderedPauli_actual _ _)

theorem hierarchy_two_of_realPauli_action {n : ℕ} {U : QuantumMatrix n}
    {F : PauliLabel n → PauliLabel n} (hU : unitaryMatrix U)
    (hF : ∀ x z : BitString n, ∃ t : ZMod 2,
      conjugate U (orderedPauli x z) =
        bitSign t • orderedPauli (F (x, z)).1 (F (x, z)).2) :
    hierarchy n 2 U := by
  apply hierarchy_two_of_implementsPauliLabels hU
  intro x z
  obtain ⟨t, ht⟩ := hF x z
  exact ⟨bitSign t, bitSign_phase t, ht⟩

theorem pauliPhase_iff_fourth_power (z : ℂ) : PauliPhase z ↔ z ^ 4 = 1 := by
  constructor
  · intro hz
    rcases hz with rfl | rfl | rfl | rfl <;> norm_num [Complex.I_sq]
  · intro hz
    have hfactor : (z - 1) * (z + 1) * (z - Complex.I) * (z + Complex.I) = 0 := by
      calc
        (z - 1) * (z + 1) * (z - Complex.I) * (z + Complex.I) =
            (z ^ 2 - 1) * (z ^ 2 - Complex.I ^ 2) := by ring
        _ = (z ^ 2 - 1) * (z ^ 2 + 1) := by simp [Complex.I_sq]
        _ = z ^ 4 - 1 := by ring
        _ = 0 := by rw [hz]; ring
    rcases mul_eq_zero.mp hfactor with habc | hd
    · rcases mul_eq_zero.mp habc with hab | hc
      · rcases mul_eq_zero.mp hab with ha | hb
        · exact Or.inl (sub_eq_zero.mp ha)
        · exact Or.inr (Or.inl (by linear_combination hb))
      · exact Or.inr (Or.inr (Or.inl (sub_eq_zero.mp hc)))
    · exact Or.inr (Or.inr (Or.inr (by linear_combination hd)))

theorem scalarPhase_primitiveRoot (m : ℕ) :
    IsPrimitiveRoot (scalarPhase m) (2 ^ (m + 2)) := by
  have hnonzero : (2 ^ (m + 2) : ℕ) ≠ 0 := pow_ne_zero _ (by decide)
  have hroot := Complex.isPrimitiveRoot_exp (2 ^ (m + 2)) hnonzero
  have hangle : Complex.I * (Real.pi : ℂ) / (2 : ℂ) ^ (m + 1) =
      2 * (Real.pi : ℂ) * Complex.I / (2 ^ (m + 2) : ℕ) := by
    push_cast
    rw [show m + 2 = (m + 1) + 1 by omega, pow_succ]
    field_simp
    ring
  simpa only [scalarPhase, hangle] using hroot

theorem scalarPhase_dyadic_actualPhase_iff (m a : ℕ) :
    PauliPhase ((scalarPhase m) ^ (2 ^ a)) ↔ m ≤ a := by
  rw [pauliPhase_iff_fourth_power, ← pow_mul,
    (scalarPhase_primitiveRoot m).pow_eq_one_iff_dvd]
  have hexponent : (2 ^ a : ℕ) * 4 = 2 ^ (a + 2) := by rw [pow_add]; norm_num
  rw [hexponent, Nat.pow_dvd_pow_iff_le_right (by decide : (1 : ℕ) < 2)]
  omega

theorem scalarPhase_period_power (m : ℕ) : (scalarPhase m) ^ (2 ^ m) = Complex.I := by
  unfold scalarPhase
  rw [← Complex.exp_nat_mul]
  have hnonzero : (2 : ℂ) ^ m ≠ 0 := pow_ne_zero _ (by norm_num)
  have hangle : (2 ^ m : ℕ) *
      (Complex.I * (Real.pi : ℂ) / (2 : ℂ) ^ (m + 1)) =
      (Real.pi : ℂ) / 2 * Complex.I := by
    push_cast
    rw [pow_succ]
    field_simp [hnonzero]
  rw [hangle]
  exact Complex.exp_pi_div_two_mul_I

theorem scalarPhase_star_mul (m : ℕ) : star (scalarPhase m) * scalarPhase m = 1 := by
  have hnonzero : (2 ^ (m + 2) : ℕ) ≠ 0 := pow_ne_zero _ (by decide)
  have hnorm : ‖scalarPhase m‖ = 1 :=
    (scalarPhase_primitiveRoot m).norm'_eq_one hnonzero
  simpa only [RCLike.star_def, hnorm, one_pow, RCLike.ofReal_one] using
    RCLike.conj_mul (scalarPhase m)

theorem scalar_adjusted_unitary {n : ℕ} (m : ℕ) {U : QuantumMatrix n}
    (hU : unitaryMatrix U) : unitaryMatrix (scalarPhase m • U) :=
  unitaryMatrix_smul (scalarPhase_star_mul m) hU

theorem orderedPauli_zero_zero {n : ℕ} (x z : BitString n) :
    orderedPauli x z 0 0 = if x = 0 then 1 else 0 := by
  classical
  have hentry := congrFun
    (orderedPauli_mulVec x z (Pi.single (0 : BitString n) (1 : ℂ))) 0
  simp only [Matrix.mulVec_single_one, Matrix.col_apply, zero_add] at hentry
  by_cases hx : x = 0
  · subst x
    simpa using hentry
  · simpa [Pi.single_apply, hx, Ne.symm hx] using hentry

theorem actualPauli_scalar_identity_iff {n : ℕ} (a : ℂ) :
    actualPauli (a • (1 : QuantumMatrix n)) ↔ PauliPhase a := by
  classical
  constructor
  · intro hPauli
    have ha : a ≠ 0 := by
      intro ha0
      have hunit := (actualPauli_unitary hPauli).1
      have hzero : (0 : QuantumMatrix n) = 1 := by simpa [ha0] using hunit
      have hentry := congrArg (fun M : QuantumMatrix n => M 0 0) hzero
      simpa using hentry
    rcases hPauli with ⟨b, x, z, hb, heq⟩
    have hentry := congrArg (fun M : QuantumMatrix n => M 0 0) heq
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.one_apply_eq,
      orderedPauli_zero_zero] at hentry
    by_cases hx : x = 0
    · have hab : a = b := by simpa [hx] using hentry
      exact hab.symm ▸ hb
    · have ha0 : a = 0 := by simpa [hx] using hentry
      exact False.elim (ha ha0)
  · intro ha
    exact ⟨a, 0, 0, ha, by simp⟩

theorem dyadic_power_eq_one_of_fourth_power {n a : ℕ} {U : QuantumMatrix n}
    (hU : U ^ 4 = 1) (ha : 2 ≤ a) : U ^ (2 ^ a) = 1 := by
  have hasub : a = 2 + (a - 2) := by omega
  have hexponent : (2 ^ a : ℕ) = 4 * 2 ^ (a - 2) := by
    calc
      2 ^ a = 2 ^ (2 + (a - 2)) := congrArg (fun t : ℕ => 2 ^ t) hasub
      _ = 4 * 2 ^ (a - 2) := by rw [pow_add]; norm_num
  rw [hexponent, pow_mul, hU, one_pow]

theorem scalar_adjusted_later_dyadic_power_iff {n m a : ℕ} {U : QuantumMatrix n}
    (hU : U ^ 4 = 1) (ha : 2 ≤ a) :
    actualPauli ((scalarPhase m • U) ^ (2 ^ a)) ↔ m ≤ a := by
  rw [smul_pow, dyadic_power_eq_one_of_fourth_power hU ha,
    actualPauli_scalar_identity_iff, scalarPhase_dyadic_actualPhase_iff]

theorem scalar_adjusted_period_power {n m : ℕ} {U : QuantumMatrix n}
    (hU : U ^ 4 = 1) (hm : 2 ≤ m) :
    (scalarPhase m • U) ^ (2 ^ m) = Complex.I • (1 : QuantumMatrix n) := by
  rw [smul_pow, dyadic_power_eq_one_of_fourth_power hU hm, scalarPhase_period_power]

theorem actualPauliPeriod_scalar_adjusted_quartic {n m : ℕ} {U : QuantumMatrix n}
    (hm : 2 ≤ m) (hU : U ^ 4 = 1)
    (hearly : ∀ a : ℕ, a < 2 → ∀ b : ℂ, ¬ actualPauli (b • U ^ (2 ^ a))) :
    actualPauliPeriod m (scalarPhase m • U) := by
  constructor
  · exact (scalar_adjusted_later_dyadic_power_iff hU hm).mpr (le_refl m)
  · intro a ham hPauli
    by_cases ha : 2 ≤ a
    · have hma := (scalar_adjusted_later_dyadic_power_iff hU ha).mp hPauli
      omega
    · rw [smul_pow] at hPauli
      exact hearly a (by omega) ((scalarPhase m) ^ (2 ^ a)) hPauli

theorem early_scalar_nonpauli_of_square {n : ℕ} {U : QuantumMatrix n}
    (hsquare : ∀ b : ℂ, ¬ actualPauli (b • U ^ 2)) :
    ∀ a : ℕ, a < 2 → ∀ b : ℂ, ¬ actualPauli (b • U ^ (2 ^ a)) := by
  intro a ha b hPauli
  have ha01 : a = 0 ∨ a = 1 := by omega
  rcases ha01 with rfl | rfl
  · have hPauli' : actualPauli (b • U) := by simpa using hPauli
    have hPauliSquare : actualPauli ((b • U) ^ 2) := by
      rw [pow_two]
      exact actualPauli_mul hPauli' hPauli'
    rw [smul_pow] at hPauliSquare
    exact hsquare (b ^ 2) hPauliSquare
  · exact hsquare b (by simpa using hPauli)

theorem actualPauliPeriod_scalar_adjusted_of_nonscalar_square
    {n m : ℕ} {U : QuantumMatrix n} (hm : 2 ≤ m) (hU : U ^ 4 = 1)
    (hsquare : ∀ b : ℂ, ¬ actualPauli (b • U ^ 2)) :
    actualPauliPeriod m (scalarPhase m • U) :=
  actualPauliPeriod_scalar_adjusted_quartic hm hU (early_scalar_nonpauli_of_square hsquare)

theorem actualPauli_column_unique {n : ℕ} {P : QuantumMatrix n}
    (hP : actualPauli P) (row other col : BitString n)
    (hrow : P row col ≠ 0) (hother : P other col ≠ 0) : row = other := by
  classical
  rcases hP with ⟨a, x, z, ha, rfl⟩
  have hr : col = row + x := by
    by_contra hn
    exact hrow (by simp [Matrix.smul_apply, orderedPauli_apply, hn])
  have hs : col = other + x := by
    by_contra hn
    exact hother (by simp [Matrix.smul_apply, orderedPauli_apply, hn])
  exact add_right_cancel (hr.symm.trans hs)

theorem scalar_nonpauli_of_two_column_entries {n : ℕ} (U : QuantumMatrix n)
    (row other col : BitString n) (hdistinct : row ≠ other)
    (hrow : U row col ≠ 0) (hother : U other col ≠ 0) :
    ∀ a : ℂ, ¬ actualPauli (a • U) := by
  intro a hP
  have ha : a ≠ 0 := by
    intro ha0
    have hzero : actualPauli ((0 : ℂ) • (1 : QuantumMatrix n)) := by
      simpa only [ha0, zero_smul] using hP
    have hzeroPhase : PauliPhase (0 : ℂ) :=
      (actualPauli_scalar_identity_iff 0).mp hzero
    have hzeroPow := (pauliPhase_iff_fourth_power 0).mp hzeroPhase
    norm_num at hzeroPow
  have hr : (a • U) row col ≠ 0 := by
    simpa only [Matrix.smul_apply, smul_eq_mul] using mul_ne_zero ha hrow
  have hs : (a • U) other col ≠ 0 := by
    simpa only [Matrix.smul_apply, smul_eq_mul] using mul_ne_zero ha hother
  exact hdistinct (actualPauli_column_unique hP row other col hr hs)

theorem exactLevel_smul_unit_scalar_of_three_le {n r : ℕ} {a : ℂ}
    {U : QuantumMatrix n} (hr : 3 ≤ r) (ha : star a * a = 1)
    (hU : exactLevel r U) : exactLevel r (a • U) := by
  refine ⟨hU.1, hierarchy_smul_unit_scalar (by omega) ha hU.2.1, ?_⟩
  intro t ht htr hsmall
  have hprevious : hierarchy n (r - 1) (a • U) :=
    hierarchy_mono ht (by omega) hsmall
  have hbase : hierarchy n (r - 1) U :=
    (hierarchy_smul_unit_scalar_iff (by omega) ha).mp hprevious
  exact hU.2.2 (r - 1) (by omega) (by omega) hbase

theorem exactLevel_smul_unit_scalar_iff_of_three_le {n r : ℕ} {a : ℂ}
    {U : QuantumMatrix n} (hr : 3 ≤ r) (ha : star a * a = 1) :
    exactLevel r (a • U) ↔ exactLevel r U := by
  constructor
  · intro hU
    have ha' : star (star a) * star a = 1 := by simpa only [star_star, mul_comm] using ha
    have hbase := exactLevel_smul_unit_scalar_of_three_le hr ha' hU
    simpa only [smul_smul, ha, one_smul] using hbase
  · exact exactLevel_smul_unit_scalar_of_three_le hr ha

theorem exactLevel_scalarPhase {n : ℕ} {U : QuantumMatrix n}
    (hU : exactLevel 3 U) (m : ℕ) : exactLevel 3 (scalarPhase m • U) :=
  exactLevel_smul_unit_scalar_of_three_le (le_refl 3) (scalarPhase_star_mul m) hU

theorem selector_involution_adjoint {n : ℕ} {D : QuantumMatrix n}
    (hD : unitaryMatrix D) (hsq : D ^ 2 = 1) : D.conjTranspose = D := by
  calc
    D.conjTranspose = D.conjTranspose * 1 := by rw [mul_one]
    _ = D.conjTranspose * (D * D) := by rw [← pow_two, hsq]
    _ = D := by rw [← mul_assoc, hD.1, one_mul]

theorem selector_pauliCorrection_smul_left {n : ℕ} (U P : QuantumMatrix n)
    {a : ℂ} (ha : star a * a = 1) :
    pauliCorrection (a • U) P = pauliCorrection U P := by
  simp only [pauliCorrection, conjugate_smul_left U P ha]

theorem selector_branch_headX_positive {n : ℕ} (B D : QuantumMatrix n)
    (hD : unitaryMatrix D) (hsq : D ^ 2 = 1) :
    pauliCorrection (branchMatrix B (B * D)) (physicalHeadX n) =
      branchMatrix (conjugate B D) (conjugate B D) := by
  rw [pauliCorrection_branch_headX]
  simp only [Matrix.conjTranspose_mul, selector_involution_adjoint hD hsq,
    conjugate, mul_assoc]

theorem selector_branch_headX_negative {n : ℕ} (B D : QuantumMatrix n)
    (hB : unitaryMatrix B) (hD : unitaryMatrix D) (hsq : D ^ 2 = 1) :
    pauliCorrection (branchMatrix B (B * D)).conjTranspose (physicalHeadX n) =
      branchMatrix D D := by
  rw [branchMatrix_conjTranspose, pauliCorrection_branch_headX]
  simp only [Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_mul,
    selector_involution_adjoint hD hsq]
  have hleft : B.conjTranspose * (B * D) = D := by
    rw [← mul_assoc, hB.1, one_mul]
  have hright : D * B.conjTranspose * B = D := by
    rw [mul_assoc, hB.1, mul_one]
  rw [hleft, hright]

theorem selector_controlled_two_corrections {n : ℕ} (B D : QuantumMatrix n)
    {a : ℂ} (ha : star a * a = 1) (hB : unitaryMatrix B)
    (hD : unitaryMatrix D) (hsq : D ^ 2 = 1) :
    pauliCorrection
      (pauliCorrection (controlled (a • branchMatrix B (B * D)))
        (physicalHeadX (n + 1)))
      (branchMatrix (physicalHeadX n) (physicalHeadX n)) =
        branchMatrix (branchMatrix D D)
          (branchMatrix (conjugate B D) (conjugate B D)) := by
  have ha' : star (star a) * star a = 1 := by
    simpa only [star_star, mul_comm] using ha
  rw [pauliCorrection_controlled_headX, pauliCorrection_branchMatrix,
    Matrix.conjTranspose_smul,
    selector_pauliCorrection_smul_left _ _ ha',
    selector_pauliCorrection_smul_left _ _ ha,
    selector_branch_headX_negative B D hB hD hsq,
    selector_branch_headX_positive B D hD hsq]

theorem selector_controlled_exposure_factor {n : ℕ} (B D : QuantumMatrix n)
    {a : ℂ} (ha : star a * a = 1) (hB : unitaryMatrix B)
    (hD : unitaryMatrix D) (hsq : D ^ 2 = 1) :
    branchMatrix (branchMatrix D D).conjTranspose (branchMatrix D D).conjTranspose *
      pauliCorrection
        (pauliCorrection (controlled (a • branchMatrix B (B * D)))
          (physicalHeadX (n + 1)))
        (branchMatrix (physicalHeadX n) (physicalHeadX n)) =
      controlled (branchMatrix (D * conjugate B D) (D * conjugate B D)) := by
  rw [selector_controlled_two_corrections B D ha hB hD hsq]
  have hDD : D * D = 1 := by simpa only [pow_two] using hsq
  simp only [branchMatrix_conjTranspose, branchMatrix_mul, hDD,
    branchMatrix_one_one, selector_involution_adjoint hD hsq, controlled]

theorem selector_controlled_level_lower {n h r : ℕ} {a : ℂ}
    {B D : QuantumMatrix n} (hh : 1 ≤ h) (hr : 1 ≤ r)
    (ha : star a * a = 1) (hB : unitaryMatrix B)
    (hD : hierarchy n 2 D) (hsq : D ^ 2 = 1)
    (hperiod : actualPauliPeriod h (D * conjugate B D))
    (hW : hierarchy (n + 2) r (controlled (a • branchMatrix B (B * D)))) :
    h + 4 ≤ r := by
  let R := max r 4
  let t := R - 4
  have hR : 4 ≤ R := le_max_right _ _
  have hWR : hierarchy (n + 2) (t + 4)
      (controlled (a • branchMatrix B (B * D))) := by
    have ht : t + 4 = R := by dsimp [t]; omega
    rw [ht]
    exact hierarchy_mono hr (le_max_left r 4) hW
  have hc0 := ((hierarchy_iff_pauliCorrections _).mp hWR).2 _
    (physicalHeadX_actual (n + 1))
  have hc1 := ((hierarchy_iff_pauliCorrections _).mp hc0).2 _
    (actualPauli_lift (physicalHeadX_actual n))
  have hfactor : hierarchy (n + 2) 2
      (branchMatrix (branchMatrix D D).conjTranspose
        (branchMatrix D D).conjTranspose) :=
    hierarchy_lift (by omega) (clifford_conjTranspose (hierarchy_lift (by omega) hD))
  have hexposed : hierarchy (n + 2) (t + 2)
      (controlled (branchMatrix (D * conjugate B D) (D * conjugate B D))) := by
    rw [← selector_controlled_exposure_factor B D ha hB hD.1 hsq]
    exact hierarchy_clifford_mul_left (by omega) hfactor hc1
  have hpLift : actualPauliPeriod h
      (branchMatrix (D * conjugate B D) (D * conjugate B D)) :=
    actualPauliPeriod_lift_iff.mpr hperiod
  have hht : h ≤ t := controlled_period_lower hpLift hexposed
  by_cases hr4 : 4 ≤ r
  · dsimp [t, R] at hht
    rw [max_eq_left hr4] at hht
    omega
  · have hrle : r ≤ 4 := by omega
    dsimp [t, R] at hht
    rw [max_eq_right hrle] at hht
    omega

theorem selector_target_three {n : ℕ} {B D : QuantumMatrix n}
    (hB : hierarchy n 2 B) (hD : hierarchy n 2 D) (hsq : D ^ 2 = 1) :
    hierarchy (n + 1) 3 (branchMatrix B (B * D)) := by
  have hrelative : B.conjTranspose * (B * D) = D := by
    rw [← mul_assoc, hB.1.1, one_mul]
  rw [branchMatrix_clifford_factor hB.1 (B * D), hrelative]
  have hpower : actualPauli (D ^ (2 ^ 1)) := by
    simpa only [pow_one, hsq] using actualPauli_one n
  have hcontrolled : hierarchy (n + 1) 3 (controlled D) :=
    controlled_clifford_upper hD hpower
  exact hierarchy_clifford_mul_left (by omega) (hierarchy_lift (by omega) hB) hcontrolled

theorem selector_target_exact_three {n : ℕ} {B D : QuantumMatrix n}
    (hB : hierarchy n 2 B) (hD : hierarchy n 2 D) (hsq : D ^ 2 = 1)
    (hnot : ¬ actualPauli D) : exactLevel 3 (branchMatrix B (B * D)) := by
  apply exactLevel_of_previous_not (by omega) (selector_target_three hB hD hsq)
  intro hsmall
  have hfactor : hierarchy (n + 1) 2 (branchMatrix B.conjTranspose B.conjTranspose) :=
    hierarchy_lift (by omega) (clifford_conjTranspose hB)
  have hextract : branchMatrix B.conjTranspose B.conjTranspose *
      branchMatrix B (B * D) = controlled D := by
    simp only [branchMatrix_mul, ← mul_assoc, hB.1.1, one_mul, controlled]
  have hcontrolled : hierarchy (n + 1) 2 (controlled D) := by
    rw [← hextract]
    exact hierarchy_clifford_mul_left (by omega) hfactor hsmall
  have hPauli : actualPauli (D ^ (2 ^ 0)) := controlled_dyadic_power_pauli hcontrolled
  exact hnot (by simpa using hPauli)

theorem selector_scalar_target_properties {n m : ℕ} {B D : QuantumMatrix n}
    (hm : 2 ≤ m) (hB : hierarchy n 2 B) (hD : hierarchy n 2 D)
    (hsq : D ^ 2 = 1) (hnot : ¬ actualPauli D)
    (hquartic : (branchMatrix B (B * D)) ^ 4 = 1)
    (hsquare : ∀ b : ℂ, ¬ actualPauli (b • (branchMatrix B (B * D)) ^ 2)) :
    unitaryMatrix (scalarPhase m • branchMatrix B (B * D)) ∧
    exactLevel 3 (scalarPhase m • branchMatrix B (B * D)) ∧
    actualPauliPeriod m (scalarPhase m • branchMatrix B (B * D)) := by
  have hlevel := selector_target_exact_three hB hD hsq hnot
  refine ⟨scalar_adjusted_unitary m (hierarchy_unitary (by omega) hlevel.2.1),
    exactLevel_scalarPhase hlevel m, ?_⟩
  exact actualPauliPeriod_scalar_adjusted_of_nonscalar_square hm hquartic hsquare

theorem selector_scalar_controlled_level_lower {n h m r : ℕ}
    {B D : QuantumMatrix n} (hh : 1 ≤ h) (hm : 2 ≤ m) (hr : 1 ≤ r)
    (hB : unitaryMatrix B) (hD : hierarchy n 2 D) (hsq : D ^ 2 = 1)
    (hperiod : actualPauliPeriod h (D * conjugate B D))
    (hquartic : (branchMatrix B (B * D)) ^ 4 = 1)
    (hsquare : ∀ b : ℂ, ¬ actualPauli (b • (branchMatrix B (B * D)) ^ 2))
    (hW : hierarchy (n + 2) r
      (controlled (scalarPhase m • branchMatrix B (B * D)))) :
    max (h + 4) (m + 2) ≤ r := by
  have hratio : h + 4 ≤ r := selector_controlled_level_lower hh hr
    (scalarPhase_star_mul m) hB hD hsq hperiod hW
  have hp : actualPauliPeriod m (scalarPhase m • branchMatrix B (B * D)) :=
    actualPauliPeriod_scalar_adjusted_of_nonscalar_square hm hquartic hsquare
  have hW' : hierarchy (n + 2) ((r - 2) + 2)
      (controlled (scalarPhase m • branchMatrix B (B * D))) := by
    convert hW using 1 <;> omega
  have hscalar : m ≤ r - 2 := controlled_period_lower hp hW'
  exact max_le hratio (by omega)

theorem compact_target_qubit_count (h : ℕ) (hh : 1 ≤ h) :
    targetSize h = if h = 1 then 3 else 2 ^ (h - 1) + 3 := by
  split_ifs with h1
  · subst h
    exact targetSize_one
  · exact targetSize_of_two_le (by omega)

theorem matrix_dot_append {n m : ℕ} (z b : BitString n) (w c : BitString m) :
    dot (Fin.append z w) (Fin.append b c) = dot z b + dot w c := by
  unfold dot
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right]

theorem matrix_character_append {n m : ℕ} (z b : BitString n) (w c : BitString m) :
    character (Fin.append z w) (Fin.append b c) = character z b * character w c := by
  rw [character, matrix_dot_append, bitSign_add]
  rfl

theorem matrix_append_add {n m : ℕ} (r x : BitString n) (s y : BitString m) :
    Fin.append r s + Fin.append x y = Fin.append (r + x) (s + y) := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp

theorem matrix_append_eq_iff {n m : ℕ} (r c : BitString n) (s t : BitString m) :
    Fin.append r s = Fin.append c t ↔ r = c ∧ s = t := by
  constructor
  · intro h
    have hpair := congrArg (tensorBasisEquiv n m) h
    have hp : (r, s) = (c, t) := by simpa [tensorBasisEquiv] using hpair
    exact Prod.mk.inj hp
  · rintro ⟨rfl, rfl⟩
    rfl

theorem matrix_orderedPauli_tensor {n m : ℕ}
    (x z : BitString n) (y w : BitString m) :
    orderedPauli (Fin.append x y) (Fin.append z w) =
      tensorMatrix (orderedPauli x z) (orderedPauli y w) := by
  classical
  ext row col
  obtain ⟨⟨r, s⟩, rfl⟩ := (tensorBasisEquiv n m).symm.surjective row
  obtain ⟨⟨c, t⟩, rfl⟩ := (tensorBasisEquiv n m).symm.surjective col
  change orderedPauli (Fin.append x y) (Fin.append z w)
      (Fin.append r s) (Fin.append c t) =
    tensorMatrix (orderedPauli x z) (orderedPauli y w)
      (Fin.append r s) (Fin.append c t)
  rw [orderedPauli_apply, tensorMatrix_apply_append, orderedPauli_apply,
    orderedPauli_apply, matrix_append_add]
  by_cases hc : c = r + x <;> by_cases ht : t = s + y <;>
    simp [matrix_append_eq_iff, matrix_character_append, hc, ht]

theorem matrix_tensorMatrix_smul {n m : ℕ} (U : QuantumMatrix n) (V : QuantumMatrix m)
    (a b : ℂ) : tensorMatrix (a • U) (b • V) = (a * b) • tensorMatrix U V := by
  ext row col
  simp only [tensorMatrix, Matrix.smul_apply, smul_eq_mul]
  ring

theorem matrix_actualPauli_tensor {n m : ℕ} {P : QuantumMatrix n} {Q : QuantumMatrix m}
    (hP : actualPauli P) (hQ : actualPauli Q) : actualPauli (tensorMatrix P Q) := by
  rcases hP with ⟨a, x, z, ha, rfl⟩
  rcases hQ with ⟨b, y, w, hb, rfl⟩
  rw [matrix_tensorMatrix_smul, ← matrix_orderedPauli_tensor]
  exact actualPauli_smul (pauliPhase_mul ha hb) (orderedPauli_actual _ _)

theorem matrix_conjugate_tensor {n m : ℕ} (U P : QuantumMatrix n)
    (V Q : QuantumMatrix m) :
    conjugate (tensorMatrix U V) (tensorMatrix P Q) =
      tensorMatrix (conjugate U P) (conjugate V Q) := by
  simp only [conjugate, tensorMatrix_conjTranspose, tensorMatrix_mul]

theorem matrix_tensor_clifford {n m : ℕ} {U : QuantumMatrix n} {V : QuantumMatrix m}
    (hU : hierarchy n 2 U) (hV : hierarchy m 2 V) :
    hierarchy (n + m) 2 (tensorMatrix U V) := by
  refine ⟨tensorMatrix_unitary hU.1 hV.1, ?_⟩
  intro P hP
  rcases hP with ⟨a, x, z, ha, rfl⟩
  obtain ⟨⟨x1, x2⟩, rfl⟩ := (tensorBasisEquiv n m).symm.surjective x
  obtain ⟨⟨z1, z2⟩, rfl⟩ := (tensorBasisEquiv n m).symm.surjective z
  change actualPauli (conjugate (tensorMatrix U V)
    (a • orderedPauli (Fin.append x1 x2) (Fin.append z1 z2)))
  rw [conjugate_smul_right, matrix_orderedPauli_tensor, matrix_conjugate_tensor]
  exact actualPauli_smul ha (matrix_actualPauli_tensor
    (hU.2 _ (orderedPauli_actual x1 z1)) (hV.2 _ (orderedPauli_actual x2 z2)))

theorem matrix_swapBlocks_clifford (s : ℕ) :
    hierarchy (s + s) 2 (swapBlocksMatrix s) := by
  refine ⟨swapBlocksMatrix_unitary s, ?_⟩
  intro P hP
  rcases hP with ⟨a, x, z, ha, rfl⟩
  obtain ⟨⟨x1, x2⟩, rfl⟩ := (tensorBasisEquiv s s).symm.surjective x
  obtain ⟨⟨z1, z2⟩, rfl⟩ := (tensorBasisEquiv s s).symm.surjective z
  change actualPauli (conjugate (swapBlocksMatrix s)
    (a • orderedPauli (Fin.append x1 x2) (Fin.append z1 z2)))
  rw [conjugate_smul_right, matrix_orderedPauli_tensor,
    swapBlocksMatrix_tensor_conjugate]
  exact actualPauli_smul ha
    (matrix_actualPauli_tensor (orderedPauli_actual x2 z2) (orderedPauli_actual x1 z1))

theorem matrix_layerC1_clifford (s : ℕ) : hierarchy s 2 (layerC1 s) :=
  hierarchy_two_of_realPauli_action (layerC1_unitary s) (layerC1_realPauliLabels s)

theorem matrix_layerC2_clifford (s : ℕ) : hierarchy s 2 (layerC2 s) :=
  hierarchy_two_of_realPauli_action (layerC2_unitary s) (layerC2_realPauliLabels s)

theorem matrix_selectorB_clifford (s : ℕ) : hierarchy (s+s) 2 (selectorB s) := by
  unfold selectorB
  exact hierarchy_clifford_mul_right (by omega) (matrix_swapBlocks_clifford s)
    (matrix_tensor_clifford (matrix_layerC1_clifford s)
      (actualPauli_hierarchy (by omega) (actualPauli_one s)))

theorem matrix_selectorD_clifford (s : ℕ) : hierarchy (s+s) 2 (selectorD s) :=
  matrix_tensor_clifford (matrix_layerC2_clifford s) (matrix_layerC1_clifford s)

theorem matrix_selectorD_square (s : ℕ) : (selectorD s) ^ 2 = 1 := by
  rw [selectorD, pow_two, tensorMatrix_mul, layerC2_square, layerC1_square,
    tensorMatrix_one_one]

theorem matrix_unitary_column_nonzero {n : ℕ} {U : QuantumMatrix n}
    (hU : unitaryMatrix U) (col : BitString n) : ∃ row, U row col ≠ 0 := by
  classical
  by_contra! hn
  have hzero : (U.conjTranspose * U) col col = 0 := by
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, hn]
  have hone : (U.conjTranspose * U) col col = 1 := by
    simpa only [Matrix.one_apply_eq] using
      congrArg (fun M : QuantumMatrix n => M col col) hU.1
  rw [hzero] at hone
  exact zero_ne_one hone

theorem matrix_hadamard_coefficient_ne_zero :
    (((Real.sqrt 2 : ℝ) : ℂ)⁻¹) ≠ 0 := by
  intro hzero
  have hnormal := hadamard_normalization
  rw [hzero] at hnormal
  norm_num at hnormal

theorem matrix_selectorD_not_projectivePauli {s : ℕ} (hs : 0 < s) :
    ∀ a : ℂ, ¬ actualPauli (a • selectorD s) := by
  classical
  let e : BitString s := Pi.single (⟨0,hs⟩ : Fin s) 1
  obtain ⟨row, hrow⟩ := matrix_unitary_column_nonzero (layerC2_unitary s) 0
  have hzero : layerC1 s 0 0 ≠ 0 := by
    rw [layerC1_zero_zero hs]
    exact matrix_hadamard_coefficient_ne_zero
  have hone : layerC1 s e 0 ≠ 0 := by
    rw [layerC1_single_zero hs]
    exact matrix_hadamard_coefficient_ne_zero
  have hdistinct : Fin.append row (0 : BitString s) ≠ Fin.append row e := by
    intro heq
    have hsecond := (matrix_append_eq_iff row row (0 : BitString s) e).mp heq
    have hwire := congrFun hsecond.2 (⟨0,hs⟩ : Fin s)
    have hz : (0 : ZMod 2) = 1 := by simpa [e] using hwire
    exact zero_ne_one hz
  have hentry0 : selectorD s (Fin.append row (0 : BitString s))
      (Fin.append (0 : BitString s) (0 : BitString s)) ≠ 0 := by
    rw [selectorD, tensorMatrix_apply_append]
    exact mul_ne_zero hrow hzero
  have hentry1 : selectorD s (Fin.append row e)
      (Fin.append (0 : BitString s) (0 : BitString s)) ≠ 0 := by
    rw [selectorD, tensorMatrix_apply_append]
    exact mul_ne_zero hrow hone
  exact scalar_nonpauli_of_two_column_entries (selectorD s)
    (Fin.append row 0) (Fin.append row e) (Fin.append 0 0) hdistinct hentry0 hentry1

theorem matrix_selectorTarget_exact_three {s : ℕ} (hs : 0 < s) :
    exactLevel 3 (selectorTarget s) := by
  have hnot : ¬ actualPauli (selectorD s) := by
    simpa only [one_smul] using matrix_selectorD_not_projectivePauli hs 1
  simpa only [selectorTarget, selectorA] using selector_target_exact_three
    (matrix_selectorB_clifford s) (matrix_selectorD_clifford s)
    (matrix_selectorD_square s) hnot

theorem matrix_selectorTarget_actual_period_two {s : ℕ} (hs : 0 < s) :
    actualPauliPeriod 2 (selectorTarget s) := by
  refine ⟨?_, ?_⟩
  · have hexp : (2 : ℕ) ^ 2 = 4 := by norm_num
    rw [hexp, selectorTarget_fourth_power]
    exact actualPauli_one _
  · intro a ha hP
    exact early_scalar_nonpauli_of_square
      (selectorTarget_square_not_projectivePauli hs) a ha 1 (by simpa using hP)

theorem matrix_compact_target_properties (h m : ℕ) (hm : 2 ≤ m) :
    unitaryMatrix (compactTarget h m) ∧ exactLevel 3 (compactTarget h m) ∧
      actualPauliPeriod m (compactTarget h m) := by
  dsimp only [compactTarget, targetSize]
  change unitaryMatrix (scalarPhase m • selectorTarget (blockSize h)) ∧
    exactLevel 3 (scalarPhase m • selectorTarget (blockSize h)) ∧
    actualPauliPeriod m (scalarPhase m • selectorTarget (blockSize h))
  have hlevel := matrix_selectorTarget_exact_three (blockSize_pos h)
  refine ⟨scalar_adjusted_unitary m (hierarchy_unitary (by omega) hlevel.2.1),
    exactLevel_scalarPhase hlevel m, ?_⟩
  exact actualPauliPeriod_scalar_adjusted_of_nonscalar_square hm
    (selectorTarget_fourth_power (blockSize h))
    (selectorTarget_square_not_projectivePauli (blockSize_pos h))

theorem matrix_tensor_actualPauli_left_projective {n m : ℕ}
    {U : QuantumMatrix n} {V : QuantumMatrix m}
    (hU : unitaryMatrix U) (hV : unitaryMatrix V)
    (hP : actualPauli (tensorMatrix U V)) :
    ∃ (a : ℂ) (x z : BitString n), a ≠ 0 ∧ U = a • orderedPauli x z := by
  classical
  rcases hP with ⟨a, x, z, ha, hP⟩
  obtain ⟨⟨x1, x2⟩, rfl⟩ := (tensorBasisEquiv n m).symm.surjective x
  obtain ⟨⟨z1, z2⟩, rfl⟩ := (tensorBasisEquiv n m).symm.surjective z
  change tensorMatrix U V =
    a • orderedPauli (Fin.append x1 x2) (Fin.append z1 z2) at hP
  rw [matrix_orderedPauli_tensor] at hP
  obtain ⟨s, hVs⟩ := matrix_unitary_column_nonzero hV 0
  let b : ℂ := (a * orderedPauli x2 z2 s 0) / V s 0
  have hUeq : U = b • orderedPauli x1 z1 := by
    ext r c
    have hentry := congrArg (fun M : QuantumMatrix (n+m) =>
      M (Fin.append r s) (Fin.append c 0)) hP
    simp only [Matrix.smul_apply, smul_eq_mul,
      tensorMatrix_apply_append] at hentry
    simp only [Matrix.smul_apply, smul_eq_mul]
    calc
      U r c = (a * orderedPauli x2 z2 s 0 * orderedPauli x1 z1 r c) /
          V s 0 := (eq_div_iff hVs).2 (by
            simpa only [mul_assoc, mul_comm, mul_left_comm] using hentry)
      _ = b * orderedPauli x1 z1 r c := by dsimp [b]; ring
  have hb : b ≠ 0 := by
    intro hb
    obtain ⟨r, hUr⟩ := matrix_unitary_column_nonzero hU 0
    have hzero := congrArg (fun M : QuantumMatrix n => M r 0) hUeq
    simp only [hb, zero_smul, Matrix.zero_apply] at hzero
    exact hUr hzero
  exact ⟨b, x1, z1, hb, hUeq⟩

theorem matrix_tensor_nonpauli_of_projective_left {n m : ℕ}
    {U : QuantumMatrix n} {V : QuantumMatrix m}
    (hU : unitaryMatrix U) (hV : unitaryMatrix V)
    (hnot : ∀ a : ℂ, ¬ actualPauli (a • U)) :
    ¬ actualPauli (tensorMatrix U V) := by
  intro hP
  obtain ⟨a, x, z, ha, hUeq⟩ :=
    matrix_tensor_actualPauli_left_projective hU hV hP
  apply hnot a⁻¹
  rw [hUeq, smul_smul, inv_mul_cancel₀ ha, one_smul]
  exact orderedPauli_actual x z

theorem matrix_tensorMatrix_pow {n m : ℕ} (U : QuantumMatrix n)
    (V : QuantumMatrix m) (k : ℕ) :
    (tensorMatrix U V) ^ k = tensorMatrix (U ^ k) (V ^ k) := by
  induction k with
  | zero => simp only [pow_zero, tensorMatrix_one_one]
  | succ k ih => rw [pow_succ, ih, tensorMatrix_mul, ← pow_succ, ← pow_succ]

theorem matrix_tensor_adjoint_actualPeriod {n h : ℕ} {R : QuantumMatrix n}
    (hR : unitaryMatrix R) (hendpoint : actualPauli (R ^ (2 ^ h)))
    (hearly : ∀ a : ℕ, a < h →
      ∀ b : ℂ, ¬ actualPauli (b • (R ^ (2 ^ a)))) :
    actualPauliPeriod h (tensorMatrix R R.conjTranspose) := by
  refine ⟨?_, ?_⟩
  · rw [matrix_tensorMatrix_pow, ← Matrix.conjTranspose_pow]
    exact matrix_actualPauli_tensor hendpoint (actualPauli_conjTranspose hendpoint)
  · intro a ha hP
    rw [matrix_tensorMatrix_pow] at hP
    exact matrix_tensor_nonpauli_of_projective_left
      (unitaryMatrix_pow hR _) (unitaryMatrix_pow (unitaryMatrix_conjTranspose hR) _)
      (hearly a ha) hP

theorem matrix_selector_ratio_actualPeriod {s h : ℕ}
    (hendpoint : actualPauli ((regularClifford s) ^ (2 ^ h)))
    (hearly : ∀ a : ℕ, a < h → ∀ b : ℂ,
      ¬ actualPauli (b • ((regularClifford s) ^ (2 ^ a)))) :
    actualPauliPeriod h (selectorD s * conjugate (selectorB s) (selectorD s)) := by
  rw [selectorD_mul_conjugate_D]
  exact matrix_tensor_adjoint_actualPeriod (regularClifford_unitary s) hendpoint hearly

theorem matrix_compact_controlled_level_lower {h m r : ℕ}
    (hh : 1 ≤ h) (hm : 2 ≤ m) (hr : 1 ≤ r)
    (hendpoint : actualPauli ((regularClifford (blockSize h)) ^ (2 ^ h)))
    (hearly : ∀ a : ℕ, a < h → ∀ b : ℂ,
      ¬ actualPauli (b • ((regularClifford (blockSize h)) ^ (2 ^ a))))
    (hW : hierarchy (targetSize h + 1) r (compactControlled h m)) :
    max (h + 4) (m + 2) ≤ r := by
  let s := blockSize h
  have hperiod : actualPauliPeriod h
      (selectorD s * conjugate (selectorB s) (selectorD s)) :=
    matrix_selector_ratio_actualPeriod hendpoint hearly
  have hquartic : (branchMatrix (selectorB s) (selectorB s * selectorD s)) ^ 4 = 1 := by
    simpa only [selectorTarget, selectorA] using selectorTarget_fourth_power s
  have hsquare : ∀ b : ℂ,
      ¬ actualPauli (b • (branchMatrix (selectorB s) (selectorB s * selectorD s)) ^ 2) := by
    intro b
    simpa only [selectorTarget, selectorA] using
      selectorTarget_square_not_projectivePauli (blockSize_pos h) b
  apply selector_scalar_controlled_level_lower hh hm hr
    (matrix_selectorB_clifford s).1 (matrix_selectorD_clifford s)
    (matrix_selectorD_square s) hperiod hquartic hsquare
  simpa only [compactControlled, compactTarget, selectorTarget, selectorA, targetSize] using hW

theorem controlled_level_lower_from_actual_period {n m r : ℕ}
    {U : QuantumMatrix n} (hm : 1 ≤ m) (hr : 1 ≤ r)
    (hperiod : actualPauliPeriod m U)
    (hW : hierarchy (n+1) r (controlled U)) : m + 2 ≤ r := by
  let R := max r 2
  let a := R - 2
  have hR : 2 ≤ R := le_max_right _ _
  have hWR : hierarchy (n+1) (a+2) (controlled U) := by
    have ha : a+2 = R := by dsimp [a]; omega
    rw [ha]
    exact hierarchy_mono hr (le_max_left r 2) hW
  have hma : m ≤ a := controlled_period_lower hperiod hWR
  by_cases hr2 : 2 ≤ r
  · dsimp [a, R] at hma
    rw [max_eq_left hr2] at hma
    omega
  · have hrle : r ≤ 2 := by omega
    dsimp [a, R] at hma
    rw [max_eq_right hrle] at hma
    omega

theorem matrix_compact_scalar_controlled_level_lower {h m r : ℕ}
    (hm : 2 ≤ m) (hr : 1 ≤ r)
    (hW : hierarchy (targetSize h + 1) r (compactControlled h m)) : m+2 ≤ r := by
  have hperiod : actualPauliPeriod m (compactTarget h m) :=
    (matrix_compact_target_properties h m hm).2.2
  apply controlled_level_lower_from_actual_period (by omega) hr hperiod
  exact hW

theorem matrix_regular_power_actual_of_linear_identity {s q : ℕ}
    (hF : regularCliffordLinear s ^ q = 1) :
    actualPauli (regularClifford s ^ q) := by
  obtain ⟨e, p, he⟩ := regularClifford_pow_sign_of_linear_identity hF
  rw [he]
  exact actualPauli_smul (bitSign_phase e) (orderedPauli_actual p.1 p.2)

theorem matrix_regular_power_sign_fixed_of_linear_identity {s q : ℕ}
    (hF : regularCliffordLinear s ^ q = 1) :
    ∃ (e : ZMod 2) (p : PauliLabel s),
      regularClifford s ^ q = bitSign e • orderedPauli p.1 p.2 ∧
        regularCliffordLinear s p = p := by
  exact regularClifford_pow_sign_fixed_of_linear_identity
    (fun _ _ _ he => orderedPauli_projective_label_eq he) hF

theorem matrix_regular_power_nonpauli_of_linear_nonidentity {s k : ℕ}
    (hF : regularCliffordLinear s ^ k ≠ 1) :
    ∀ b : ℂ, ¬ actualPauli (b • (regularClifford s ^ k)) := by
  intro b hP
  have hb : b ≠ 0 := by
    intro hb
    have hz : actualPauli ((0 : ℂ) • (1 : QuantumMatrix s)) := by
      simpa only [hb, zero_smul] using hP
    exact pauliPhase_ne_zero ((actualPauli_scalar_identity_iff 0).mp hz) rfl
  rcases hP with ⟨a, x, z, ha, he⟩
  have hproj : regularClifford s ^ k = (b⁻¹ * a) • orderedPauli x z := by
    calc
      regularClifford s ^ k = b⁻¹ • (b • (regularClifford s ^ k)) := by
        rw [smul_smul, inv_mul_cancel₀ hb, one_smul]
      _ = (b⁻¹ * a) • orderedPauli x z := by rw [he, smul_smul]
  exact regularClifford_pow_not_projective
    (fun _ _ _ he => orderedPauli_projective_label_eq he) hF
    (b⁻¹ * a) x z hproj

theorem matrix_regular_actual_period_of_label_cycle {s h : ℕ}
    (hlate : regularCliffordLinear s ^ (2 ^ h) = 1)
    (hearly : ∀ a : ℕ, a < h → regularCliffordLinear s ^ (2 ^ a) ≠ 1) :
    actualPauliPeriod h (regularClifford s) := by
  refine ⟨matrix_regular_power_actual_of_linear_identity hlate, ?_⟩
  intro a ha hP
  exact matrix_regular_power_nonpauli_of_linear_nonidentity (hearly a ha) 1
    (by simpa only [one_smul] using hP)

theorem matrix_selector_ratio_period_of_label_cycle {s h : ℕ}
    (hlate : regularCliffordLinear s ^ (2 ^ h) = 1)
    (hearly : ∀ a : ℕ, a < h → regularCliffordLinear s ^ (2 ^ a) ≠ 1) :
    actualPauliPeriod h (selectorD s * conjugate (selectorB s) (selectorD s)) := by
  exact matrix_selector_ratio_actualPeriod
    (matrix_regular_power_actual_of_linear_identity hlate)
    (fun a ha => matrix_regular_power_nonpauli_of_linear_nonidentity (hearly a ha))

theorem matrix_compact_controlled_level_lower_of_label_cycle {h m r : ℕ}
    (hh : 1 ≤ h) (hm : 2 ≤ m) (hr : 1 ≤ r)
    (hlate : regularCliffordLinear (blockSize h) ^ (2 ^ h) = 1)
    (hearly : ∀ a : ℕ, a < h →
      regularCliffordLinear (blockSize h) ^ (2 ^ a) ≠ 1)
    (hW : hierarchy (targetSize h + 1) r (compactControlled h m)) :
    max (h + 4) (m + 2) ≤ r := by
  exact matrix_compact_controlled_level_lower hh hm hr
    (matrix_regular_power_actual_of_linear_identity hlate)
    (fun a ha => matrix_regular_power_nonpauli_of_linear_nonidentity (hearly a ha)) hW

theorem matrix_blockSize_label_cycle {h : ℕ} (hh : 1 ≤ h) :
    regularCliffordLinear (blockSize h) ^ (2 ^ h) = 1 ∧
      ∀ a : ℕ, a < h → regularCliffordLinear (blockSize h) ^ (2 ^ a) ≠ 1 := by
  obtain ⟨hlower, hupper⟩ := blockSize_cycle_bounds hh
  refine ⟨regularCliffordLinear_pow_two_pow_eq_one (blockSize_pos h) h hupper, ?_⟩
  intro a ha
  apply regularCliffordLinear_pow_two_pow_ne_one (blockSize_pos h)
  have hpow : 2 ^ a ≤ 2 ^ (h - 1) :=
    pow_le_pow_right' (by decide : (1 : ℕ) ≤ 2) (by omega)
  omega

theorem matrix_blockSize_nilpotent {h : ℕ} (hh : 1 ≤ h) :
    regularNilpotentLinear (blockSize h) ^ (2 ^ h) = 0 := by
  have hbound := (blockSize_cycle_bounds hh).2
  have hn := (regularNilpotentLinear_nilpotency (blockSize_pos h)).1
  have he : 2 ^ h = (blockSize h + blockSize h) +
      (2 ^ h - (blockSize h + blockSize h)) := by omega
  rw [he, pow_add, hn, zero_mul]

theorem matrix_blockSize_signed_endpoint {h : ℕ} (hh : 1 ≤ h) :
    ∃ (e : ZMod 2) (p : PauliLabel (blockSize h)),
      regularClifford (blockSize h) ^ (2 ^ h) = bitSign e • orderedPauli p.1 p.2 ∧
      dot p.2 p.1 = 0 ∧
      p ∈ LinearMap.range (regularNilpotentLinear (blockSize h) ^ (2 ^ (h - 1))) ∧
      regularClifford (blockSize h) ^ (2 ^ (h + 1)) = 1 := by
  exact regularClifford_blockSize_signed_endpoint hh
    (fun _ _ _ he => orderedPauli_projective_label_eq he)

theorem matrix_compact_controlled_level_lower_actual {h m r : ℕ}
    (hh : 1 ≤ h) (hm : 2 ≤ m) (hr : 1 ≤ r)
    (hW : hierarchy (targetSize h + 1) r (compactControlled h m)) :
    max (h + 4) (m + 2) ≤ r := by
  obtain ⟨hlate, hearly⟩ := matrix_blockSize_label_cycle hh
  exact matrix_compact_controlled_level_lower_of_label_cycle hh hm hr hlate hearly hW

theorem matrix_compact_controlled_exact_of_membership {h m : ℕ}
    (hh : 1 ≤ h) (hm : 2 ≤ m)
    (hW : hierarchy (targetSize h + 1) (max (h + 4) (m + 2))
      (compactControlled h m)) :
    exactLevel (max (h + 4) (m + 2)) (compactControlled h m) := by
  refine ⟨by omega, hW, ?_⟩
  intro r hr hlt hmem
  have hle := matrix_compact_controlled_level_lower_actual hh hm hr hmem
  omega

def matrixPhysicalPairedEquiv (s : ℕ) :
    (PauliLabel s × PauliLabel s) ≃ₗ[ZMod 2] PauliLabel (s + s) :=
  (tensorPauliLabelLinearEquiv s s).symm

@[simp] theorem matrixPhysicalPairedEquiv_apply (s : ℕ) (v : PauliLabel s × PauliLabel s) :
    matrixPhysicalPairedEquiv s v =
      (Fin.append v.1.1 v.2.1, Fin.append v.1.2 v.2.2) := rfl

def matrixPhysicalShift0 (s : ℕ) : MatrixUnitary (s + s) :=
  matrixUnitaryOf (regularShiftT0 s) (regularShiftT0_unitary s)

def matrixPhysicalShift1 (s : ℕ) : MatrixUnitary (s + s) :=
  matrixUnitaryOf (regularShiftT1 s) (regularShiftT1_unitary s)

@[simp] theorem matrixPhysicalShift0_coe (s : ℕ) :
    (matrixPhysicalShift0 s : QuantumMatrix (s + s)) = regularShiftT0 s := rfl

@[simp] theorem matrixPhysicalShift1_coe (s : ℕ) :
    (matrixPhysicalShift1 s : QuantumMatrix (s + s)) = regularShiftT1 s := rfl

theorem matrixPhysicalShifts_commute (s : ℕ) :
    Commute (matrixPhysicalShift0 s) (matrixPhysicalShift1 s) :=
  (matrixUnitary_commute_iff _ _).mpr (regularShiftT0_T1_commute s)

theorem matrix_regularClifford_clifford (s : ℕ) :
    hierarchy s 2 (regularClifford s) :=
  hierarchy_clifford_mul_right (by omega) (matrix_layerC1_clifford s) (matrix_layerC2_clifford s)

theorem matrixPhysicalShift0_clifford (s : ℕ) :
    hierarchy (s + s) 2 (matrixPhysicalShift0 s : QuantumMatrix (s + s)) :=
  matrix_tensor_clifford (matrix_regularClifford_clifford s)
    (actualPauli_hierarchy (by omega) (actualPauli_one s))

theorem matrixPhysicalShift1_clifford (s : ℕ) :
    hierarchy (s + s) 2 (matrixPhysicalShift1 s : QuantumMatrix (s + s)) :=
  matrix_tensor_clifford (actualPauli_hierarchy (by omega) (actualPauli_one s))
    (matrix_regularClifford_clifford s)

def matrixPhysicalPairedStep0 (s : ℕ) : Module.End (ZMod 2) (PauliLabel (s + s)) :=
  (matrixPhysicalPairedEquiv s).toLinearMap.comp
    (((regularCliffordLinear s).prodMap (1 : Module.End (ZMod 2) (PauliLabel s))).comp
      (matrixPhysicalPairedEquiv s).symm.toLinearMap)

def matrixPhysicalPairedStep1 (s : ℕ) : Module.End (ZMod 2) (PauliLabel (s + s)) :=
  (matrixPhysicalPairedEquiv s).toLinearMap.comp
    (((1 : Module.End (ZMod 2) (PauliLabel s)).prodMap (regularCliffordLinear s)).comp
      (matrixPhysicalPairedEquiv s).symm.toLinearMap)

theorem matrixPhysicalPairedStep0_pow_apply (s k : ℕ) (v : PauliLabel s × PauliLabel s) :
    (matrixPhysicalPairedStep0 s ^ k) (matrixPhysicalPairedEquiv s v) =
      matrixPhysicalPairedEquiv s ((regularCliffordLinear s ^ k) v.1, v.2) := by
  induction k with
  | zero => simp only [pow_zero, Module.End.one_apply]
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, ih]
    simp only [matrixPhysicalPairedStep0, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply, LinearMap.prodMap_apply, Module.End.one_apply,
      pow_succ', Module.End.mul_apply]

theorem matrixPhysicalPairedStep1_pow_apply (s k : ℕ) (v : PauliLabel s × PauliLabel s) :
    (matrixPhysicalPairedStep1 s ^ k) (matrixPhysicalPairedEquiv s v) =
      matrixPhysicalPairedEquiv s (v.1, (regularCliffordLinear s ^ k) v.2) := by
  induction k with
  | zero => simp only [pow_zero, Module.End.one_apply]
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, ih]
    simp only [matrixPhysicalPairedStep1, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply, LinearMap.prodMap_apply, Module.End.one_apply,
      pow_succ', Module.End.mul_apply]

def matrixPhysicalShiftSign0 (s k : ℕ) (p : PauliLabel (s + s)) : ZMod 2 :=
  regularCliffordPowerSign s k ((matrixPhysicalPairedEquiv s).symm p).1

def matrixPhysicalShiftSign1 (s k : ℕ) (p : PauliLabel (s + s)) : ZMod 2 :=
  regularCliffordPowerSign s k ((matrixPhysicalPairedEquiv s).symm p).2

theorem matrixPhysicalShift0_pow_signed (s k : ℕ) (p : PauliLabel (s + s)) :
    conjugate ((matrixPhysicalShift0 s : QuantumMatrix (s + s)) ^ k)
      (orderedPauli p.1 p.2) =
      bitSign (matrixPhysicalShiftSign0 s k p) •
        orderedPauli ((matrixPhysicalPairedStep0 s ^ k) p).1
          ((matrixPhysicalPairedStep0 s ^ k) p).2 := by
  obtain ⟨⟨p0, p1⟩, rfl⟩ := (matrixPhysicalPairedEquiv s).surjective p
  rw [matrixPhysicalPairedStep0_pow_apply]
  simp only [matrixPhysicalShiftSign0, LinearEquiv.symm_apply_apply]
  simp only [matrixPhysicalPairedEquiv_apply, matrixPhysicalShift0_coe, regularShiftT0,
    matrix_tensorMatrix_pow, one_pow]
  rw [matrix_orderedPauli_tensor, matrix_orderedPauli_tensor, matrix_conjugate_tensor,
    regularClifford_pow_signed_action]
  simp only [conjugate, one_mul, Matrix.conjTranspose_one, mul_one]
  simpa only [one_smul, mul_one] using
    matrix_tensorMatrix_smul (orderedPauli ((regularCliffordLinear s ^ k) p0).1
      ((regularCliffordLinear s ^ k) p0).2) (orderedPauli p1.1 p1.2)
      (bitSign (regularCliffordPowerSign s k p0)) 1

theorem matrixPhysicalShift1_pow_signed (s k : ℕ) (p : PauliLabel (s + s)) :
    conjugate ((matrixPhysicalShift1 s : QuantumMatrix (s + s)) ^ k)
      (orderedPauli p.1 p.2) =
      bitSign (matrixPhysicalShiftSign1 s k p) •
        orderedPauli ((matrixPhysicalPairedStep1 s ^ k) p).1
          ((matrixPhysicalPairedStep1 s ^ k) p).2 := by
  obtain ⟨⟨p0, p1⟩, rfl⟩ := (matrixPhysicalPairedEquiv s).surjective p
  rw [matrixPhysicalPairedStep1_pow_apply]
  simp only [matrixPhysicalShiftSign1, LinearEquiv.symm_apply_apply]
  simp only [matrixPhysicalPairedEquiv_apply, matrixPhysicalShift1_coe, regularShiftT1,
    matrix_tensorMatrix_pow, one_pow]
  rw [matrix_orderedPauli_tensor, matrix_orderedPauli_tensor, matrix_conjugate_tensor,
    regularClifford_pow_signed_action]
  simp only [conjugate, one_mul, Matrix.conjTranspose_one, mul_one]
  simpa only [one_smul, one_mul] using
    matrix_tensorMatrix_smul (orderedPauli p0.1 p0.2)
      (orderedPauli ((regularCliffordLinear s ^ k) p1).1 ((regularCliffordLinear s ^ k) p1).2)
      1 (bitSign (regularCliffordPowerSign s k p1))

def matrixPhysicalHeadSign (s : ℕ) (p : PauliLabel s) : ZMod 2 :=
  Classical.choose (layerC1_realPauliLabels s p.1 p.2)

theorem matrixPhysicalHead_signed (s : ℕ) (p : PauliLabel s) :
    conjugate (layerC1 s) (orderedPauli p.1 p.2) =
      bitSign (matrixPhysicalHeadSign s p) •
        orderedPauli (layerC1Linear s p).1 (layerC1Linear s p).2 := by
  simpa only [layerC1Linear_apply, Prod.mk.eta, matrixPhysicalHeadSign] using
    Classical.choose_spec (layerC1_realPauliLabels s p.1 p.2)

theorem matrixPhysicalSelectorB_signed (s : ℕ) (v : PauliLabel s × PauliLabel s) :
    conjugate (selectorB s)
      (orderedPauli (matrixPhysicalPairedEquiv s v).1 (matrixPhysicalPairedEquiv s v).2) =
      bitSign (matrixPhysicalHeadSign s v.2) •
        orderedPauli (matrixPhysicalPairedEquiv s (layerC1Linear s v.2, v.1)).1
          (matrixPhysicalPairedEquiv s (layerC1Linear s v.2, v.1)).2 := by
  simp only [matrixPhysicalPairedEquiv_apply]
  rw [matrix_orderedPauli_tensor, matrix_orderedPauli_tensor, selectorB,
    physical_conjugate_mul, swapBlocksMatrix_tensor_conjugate, matrix_conjugate_tensor,
    matrixPhysicalHead_signed]
  simp only [conjugate, one_mul, Matrix.conjTranspose_one, mul_one]
  simpa only [one_smul, mul_one] using matrix_tensorMatrix_smul
    (orderedPauli (layerC1Linear s v.2).1 (layerC1Linear s v.2).2)
      (orderedPauli v.1.1 v.1.2) (bitSign (matrixPhysicalHeadSign s v.2)) 1

theorem matrixPhysicalShifts_signed_endpoint {h : ℕ} (hh : 1 ≤ h) :
    ∃ (e : ZMod 2) (p : PauliLabel (blockSize h)),
      dot p.2 p.1 = 0 ∧
      p ∈ LinearMap.range (regularNilpotentLinear (blockSize h) ^ (2 ^ (h - 1))) ∧
      ((matrixPhysicalShift0 (blockSize h) ^ (2 ^ h) : MatrixUnitary _)
          : QuantumMatrix _) =
        bitSign e • orderedPauli (matrixPhysicalPairedEquiv (blockSize h) (p, 0)).1
          (matrixPhysicalPairedEquiv (blockSize h) (p, 0)).2 ∧
      ((matrixPhysicalShift1 (blockSize h) ^ (2 ^ h) : MatrixUnitary _)
          : QuantumMatrix _) =
        bitSign e • orderedPauli (matrixPhysicalPairedEquiv (blockSize h) (0, p)).1
          (matrixPhysicalPairedEquiv (blockSize h) (0, p)).2 := by
  obtain ⟨e, p, hp, hHerm, hImage, _⟩ := matrix_blockSize_signed_endpoint hh
  refine ⟨e, p, hHerm, hImage, ?_, ?_⟩
  · simp only [SubmonoidClass.coe_pow, matrixPhysicalShift0_coe, regularShiftT0,
      matrix_tensorMatrix_pow, one_pow, hp, matrixPhysicalPairedEquiv_apply, Prod.fst_zero,
      Prod.snd_zero, matrix_orderedPauli_tensor, orderedPauli_zero]
    simpa only [one_smul, mul_one] using matrix_tensorMatrix_smul
      (orderedPauli p.1 p.2) (1 : QuantumMatrix (blockSize h)) (bitSign e) 1
  · simp only [SubmonoidClass.coe_pow, matrixPhysicalShift1_coe, regularShiftT1,
      matrix_tensorMatrix_pow, one_pow, hp, matrixPhysicalPairedEquiv_apply, Prod.fst_zero,
      Prod.snd_zero, matrix_orderedPauli_tensor, orderedPauli_zero]
    simpa only [one_smul, one_mul] using matrix_tensorMatrix_smul
      (1 : QuantumMatrix (blockSize h)) (orderedPauli p.1 p.2) 1 (bitSign e)

theorem matrixPhysicalPairedLeft_hermitian (s : ℕ) (p : PauliLabel s)
    (hp : dot p.2 p.1 = 0) :
    dot (matrixPhysicalPairedEquiv s (p, 0)).2
      (matrixPhysicalPairedEquiv s (p, 0)).1 = 0 := by
  simp only [matrixPhysicalPairedEquiv_apply, Prod.fst_zero, Prod.snd_zero,
    matrix_dot_append, hp, dot_zero_right, add_zero]

theorem matrixPhysicalPairedRight_hermitian (s : ℕ) (p : PauliLabel s)
    (hp : dot p.2 p.1 = 0) :
    dot (matrixPhysicalPairedEquiv s (0, p)).2
      (matrixPhysicalPairedEquiv s (0, p)).1 = 0 := by
  simp only [matrixPhysicalPairedEquiv_apply, Prod.fst_zero, Prod.snd_zero,
    matrix_dot_append, hp, dot_zero_left, zero_add]

def matrixPhysicalSelectorSquareLabel (s : ℕ) :
    Module.End (ZMod 2) (PauliLabel s × PauliLabel s) :=
  (layerC1Linear s).prodMap (layerC1Linear s)

theorem matrixPhysicalSelectorSquare_signed (s : ℕ) (v : PauliLabel s × PauliLabel s) :
    conjugate (selectorB s ^ 2)
      (orderedPauli (matrixPhysicalPairedEquiv s v).1 (matrixPhysicalPairedEquiv s v).2) =
      bitSign (matrixPhysicalHeadSign s v.1 + matrixPhysicalHeadSign s v.2) •
        orderedPauli (matrixPhysicalPairedEquiv s (matrixPhysicalSelectorSquareLabel s v)).1
          (matrixPhysicalPairedEquiv s (matrixPhysicalSelectorSquareLabel s v)).2 := by
  simp only [matrixPhysicalSelectorSquareLabel, LinearMap.prodMap_apply,
    matrixPhysicalPairedEquiv_apply]
  rw [matrix_orderedPauli_tensor, matrix_orderedPauli_tensor, selectorB_square,
    matrix_conjugate_tensor, matrixPhysicalHead_signed, matrixPhysicalHead_signed,
    matrix_tensorMatrix_smul, ← bitSign_add]

theorem matrixPhysicalSelectorSquare_difference_range {s : ℕ} (hs : 0 < s)
    (v : PauliLabel s × PauliLabel s) :
    ∃ w : PauliLabel s × PauliLabel s,
      (regularNilpotentLinear s w.1, regularNilpotentLinear s w.2) =
        (matrixPhysicalSelectorSquareLabel s - 1) v := by
  obtain ⟨w0, hw0⟩ := layerC1Linear_difference_mem_range hs v.1
  obtain ⟨w1, hw1⟩ := layerC1Linear_difference_mem_range hs v.2
  refine ⟨(w0, w1), ?_⟩
  simp only [matrixPhysicalSelectorSquareLabel, LinearMap.sub_apply,
    LinearMap.prodMap_apply, Module.End.one_apply]
  exact Prod.ext hw0 hw1

def matrixPhysicalSelector (s : ℕ) : MatrixUnitary (s + s) :=
  matrixUnitaryOf (selectorB s) (selectorB_unitary s)

@[simp] theorem matrixPhysicalSelector_coe (s : ℕ) :
    (matrixPhysicalSelector s : QuantumMatrix (s + s)) = selectorB s := rfl

theorem matrixPhysicalSelector_clifford (s : ℕ) :
    hierarchy (s + s) 2 (matrixPhysicalSelector s : QuantumMatrix (s + s)) :=
  matrix_selectorB_clifford s

theorem matrixPhysicalSelector_fourth (s : ℕ) :
    matrixPhysicalSelector s ^ (4 : ℕ) = 1 := by
  apply Subtype.ext
  simpa only [SubmonoidClass.coe_pow, matrixPhysicalSelector_coe, Submonoid.coe_one] using
    selectorB_fourth_power s

theorem matrixPhysicalSelector_shift_relations (s : ℕ) :
    matrixPhysicalSelector s * matrixPhysicalShift0 s * (matrixPhysicalSelector s)⁻¹ =
      matrixPhysicalShift1 s ∧
    matrixPhysicalSelector s * matrixPhysicalShift1 s * (matrixPhysicalSelector s)⁻¹ =
      (matrixPhysicalShift0 s)⁻¹ := by
  constructor
  · apply Subtype.ext
    simpa only [Submonoid.coe_mul, matrixUnitary_inv_coe, matrixPhysicalSelector_coe,
      matrixPhysicalShift0_coe, matrixPhysicalShift1_coe, conjugate] using
      selectorB_conjugate_shiftT0 s
  · apply Subtype.ext
    simpa only [Submonoid.coe_mul, matrixUnitary_inv_coe, matrixPhysicalSelector_coe,
      matrixPhysicalShift0_coe, matrixPhysicalShift1_coe, conjugate] using
      selectorB_conjugate_shiftT1 s

theorem matrix_regularCliffordLinear_one_add_N (s : ℕ) :
    regularCliffordLinear s = 1 + regularNilpotentLinear s := by
  unfold regularNilpotentLinear
  abel

theorem matrix_layerC1Linear_square (s : ℕ) : layerC1Linear s ^ 2 = 1 := by
  apply LinearMap.ext
  intro p
  have hconj : conjugate (layerC1 s)
      (conjugate (layerC1 s) (orderedPauli p.1 p.2)) = orderedPauli p.1 p.2 := by
    rw [← physical_conjugate_mul, layerC1_square]
    simp only [conjugate, one_mul, Matrix.conjTranspose_one, mul_one]
  rw [matrixPhysicalHead_signed, conjugate_smul_right, matrixPhysicalHead_signed,
    smul_smul] at hconj
  have hp : p = (layerC1Linear s) ((layerC1Linear s) p) :=
    orderedPauli_projective_label_eq hconj.symm
  simpa only [pow_two, Module.End.mul_apply, Module.End.one_apply] using hp.symm

def matrixPhysicalSelectorBlockAction (s : ℕ) :
    Module.End (ZMod 2) (PauliLabel s × PauliLabel s) :=
  ((layerC1Linear s).comp (LinearMap.snd (ZMod 2) (PauliLabel s) (PauliLabel s))).prod
    (LinearMap.fst (ZMod 2) (PauliLabel s) (PauliLabel s))

@[simp] theorem matrixPhysicalSelectorBlockAction_apply (s : ℕ)
    (v : PauliLabel s × PauliLabel s) :
    matrixPhysicalSelectorBlockAction s v = (layerC1Linear s v.2, v.1) := rfl

def matrixPhysicalSelectorLabel (s : ℕ) : Module.End (ZMod 2) (PauliLabel (s + s)) :=
  (matrixPhysicalPairedEquiv s).toLinearMap.comp
    ((matrixPhysicalSelectorBlockAction s).comp (matrixPhysicalPairedEquiv s).symm.toLinearMap)

theorem matrixPhysicalSelectorLabel_apply (s : ℕ) (v : PauliLabel s × PauliLabel s) :
    matrixPhysicalSelectorLabel s (matrixPhysicalPairedEquiv s v) =
      matrixPhysicalPairedEquiv s (layerC1Linear s v.2, v.1) := by
  simp only [matrixPhysicalSelectorLabel, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply, matrixPhysicalSelectorBlockAction_apply]

theorem matrixPhysicalSelectorLabel_square_apply (s : ℕ) (v : PauliLabel s × PauliLabel s) :
    (matrixPhysicalSelectorLabel s ^ 2) (matrixPhysicalPairedEquiv s v) =
      matrixPhysicalPairedEquiv s (matrixPhysicalSelectorSquareLabel s v) := by
  rw [pow_two, Module.End.mul_apply, matrixPhysicalSelectorLabel_apply,
    matrixPhysicalSelectorLabel_apply]
  rfl

def matrixPhysicalSelectorSign (s : ℕ) (p : PauliLabel (s + s)) : ZMod 2 :=
  matrixPhysicalHeadSign s ((matrixPhysicalPairedEquiv s).symm p).2

theorem matrixPhysicalSelector_full_signed (s : ℕ) (p : PauliLabel (s + s)) :
    conjugate (matrixPhysicalSelector s : QuantumMatrix (s + s)) (orderedPauli p.1 p.2) =
      bitSign (matrixPhysicalSelectorSign s p) •
        orderedPauli (matrixPhysicalSelectorLabel s p).1 (matrixPhysicalSelectorLabel s p).2 := by
  obtain ⟨v, rfl⟩ := (matrixPhysicalPairedEquiv s).surjective p
  simp only [matrixPhysicalSelectorSign, LinearEquiv.symm_apply_apply,
    matrixPhysicalSelectorLabel_apply, matrixPhysicalSelector_coe]
  exact matrixPhysicalSelectorB_signed s v

theorem matrixPhysicalSelectorLabel_square_difference {s : ℕ} (hs : 0 < s)
    (p : PauliLabel (s + s)) :
    ∃ w : PauliLabel s × PauliLabel s,
      matrixPhysicalPairedEquiv s
          (regularNilpotentLinear s w.1, regularNilpotentLinear s w.2) =
        ((matrixPhysicalSelectorLabel s ^ (2 : ℕ) - 1) :
          Module.End (ZMod 2) (PauliLabel (s + s))) p := by
  obtain ⟨v, rfl⟩ := (matrixPhysicalPairedEquiv s).surjective p
  obtain ⟨w, hw⟩ := matrixPhysicalSelectorSquare_difference_range hs v
  refine ⟨w, ?_⟩
  rw [hw]
  simp only [LinearMap.sub_apply, Module.End.one_apply,
    matrixPhysicalSelectorLabel_square_apply, map_sub]

theorem matrixPhysicalSelector_cube_inverse (s : ℕ) :
    matrixPhysicalSelector s ^ (3 : ℕ) = (matrixPhysicalSelector s)⁻¹ := by
  calc
    matrixPhysicalSelector s ^ (3 : ℕ) =
        (matrixPhysicalSelector s ^ (3 : ℕ) * matrixPhysicalSelector s) *
          (matrixPhysicalSelector s)⁻¹ := by group
    _ = matrixPhysicalSelector s ^ (4 : ℕ) * (matrixPhysicalSelector s)⁻¹ := by
      rw [← pow_succ]
    _ = (matrixPhysicalSelector s)⁻¹ := by rw [matrixPhysicalSelector_fourth, one_mul]

theorem matrixPhysicalSelector_branchA (s : ℕ) :
    ((matrixPhysicalShift1 s * (matrixPhysicalSelector s)⁻¹ : MatrixUnitary (s + s))
      : QuantumMatrix (s + s)) = selectorA s := by
  rw [← matrixPhysicalSelector_cube_inverse]
  simpa only [Submonoid.coe_mul, SubmonoidClass.coe_pow, matrixPhysicalShift1_coe,
    matrixPhysicalSelector_coe] using (selectorA_eq_shiftT1_cube s).symm

def matrixPhysicalSelectorProfile (s : ℕ) (c b : ZMod 2) : MatrixUnitary (s + s) :=
  if c = 0 then 1 else if b = 0 then matrixPhysicalSelector s
    else matrixPhysicalShift1 s * (matrixPhysicalSelector s)⁻¹

theorem matrixPhysicalSelectorProfile_matrix (s : ℕ) :
    twoControlMatrix (fun c b =>
      (matrixPhysicalSelectorProfile s c b : QuantumMatrix (s + s))) =
      controlled (selectorTarget s) := by
  simp only [twoControlMatrix, matrixPhysicalSelectorProfile,
    if_pos rfl, if_neg (by decide : (1 : ZMod 2) ≠ 0), ite_true, ite_false,
    Submonoid.coe_one, matrixPhysicalSelector_coe, matrixPhysicalSelector_branchA,
    branchMatrix_one_one, controlled, selectorTarget]

theorem matrixPhysicalShift0_residual_label (s h : ℕ) (t : ℤ) :
    matrixIntegerPowerLabel (matrixPhysicalPairedStep0 s) (2 ^ h) t =
      matrixPairedIntAction0 (matrixPhysicalPairedEquiv s) (regularNilpotentLinear s) h t := by
  apply LinearMap.ext
  intro p
  obtain ⟨v, rfl⟩ := (matrixPhysicalPairedEquiv s).surjective p
  rw [matrixIntegerPowerLabel, matrixPhysicalPairedStep0_pow_apply]
  simp only [matrixPairedIntAction0, matrixLabelTransport_apply,
    LinearEquiv.symm_apply_apply, LinearMap.prodMap_apply, Module.End.one_apply,
    matrixResidualLabelAction]
  rw [matrix_regularCliffordLinear_one_add_N]

theorem matrixPhysicalShift1_residual_label (s h : ℕ) (t : ℤ) :
    matrixIntegerPowerLabel (matrixPhysicalPairedStep1 s) (2 ^ h) t =
      matrixPairedIntAction1 (matrixPhysicalPairedEquiv s) (regularNilpotentLinear s) h t := by
  apply LinearMap.ext
  intro p
  obtain ⟨v, rfl⟩ := (matrixPhysicalPairedEquiv s).surjective p
  rw [matrixIntegerPowerLabel, matrixPhysicalPairedStep1_pow_apply]
  simp only [matrixPairedIntAction1, matrixLabelTransport_apply,
    LinearEquiv.symm_apply_apply, LinearMap.prodMap_apply, Module.End.one_apply,
    matrixResidualLabelAction]
  rw [matrix_regularCliffordLinear_one_add_N]

theorem matrixPhysicalShift0_int_signed {s h : ℕ} (e : ZMod 2) (pq : PauliLabel (s + s))
    (hp : ((matrixPhysicalShift0 s ^ (2 ^ h) : MatrixUnitary (s + s))
      : QuantumMatrix (s + s)) = signedOrderedPauli e pq)
    (hHerm : dot pq.2 pq.1 = 0) (t : ℤ) (p : PauliLabel (s + s)) :
    conjugate (matrixZpow (matrixPhysicalShift0 s) t) (orderedPauli p.1 p.2) =
      bitSign (matrixIntegerPowerSign (matrixPhysicalPairedStep0 s)
        (matrixPhysicalShiftSign0 s) pq (2 ^ h) t p) •
          orderedPauli
            (matrixPairedIntAction0 (matrixPhysicalPairedEquiv s) (regularNilpotentLinear s) h t p).1
            (matrixPairedIntAction0 (matrixPhysicalPairedEquiv s) (regularNilpotentLinear s) h t p).2 := by
  have hAct := matrixZpow_full_signed_action (by positivity : 0 < 2 ^ h) e pq hp hHerm
    (matrixPhysicalPairedStep0 s) (matrixPhysicalShiftSign0 s)
      (matrixPhysicalShift0_pow_signed s) t p
  rw [matrixPhysicalShift0_residual_label] at hAct
  exact hAct

theorem matrixPhysicalShift1_int_signed {s h : ℕ} (e : ZMod 2) (pq : PauliLabel (s + s))
    (hp : ((matrixPhysicalShift1 s ^ (2 ^ h) : MatrixUnitary (s + s))
      : QuantumMatrix (s + s)) = signedOrderedPauli e pq)
    (hHerm : dot pq.2 pq.1 = 0) (t : ℤ) (p : PauliLabel (s + s)) :
    conjugate (matrixZpow (matrixPhysicalShift1 s) t) (orderedPauli p.1 p.2) =
      bitSign (matrixIntegerPowerSign (matrixPhysicalPairedStep1 s)
        (matrixPhysicalShiftSign1 s) pq (2 ^ h) t p) •
          orderedPauli
            (matrixPairedIntAction1 (matrixPhysicalPairedEquiv s) (regularNilpotentLinear s) h t p).1
            (matrixPairedIntAction1 (matrixPhysicalPairedEquiv s) (regularNilpotentLinear s) h t p).2 := by
  have hAct := matrixZpow_full_signed_action (by positivity : 0 < 2 ^ h) e pq hp hHerm
    (matrixPhysicalPairedStep1 s) (matrixPhysicalShiftSign1 s)
      (matrixPhysicalShift1_pow_signed s) t p
  rw [matrixPhysicalShift1_residual_label] at hAct
  exact hAct

theorem matrixPhysicalPairedLeft_mem_image (s a : ℕ) (p : PauliLabel s)
    (hp : p ∈ LinearMap.range (regularNilpotentLinear s ^ a)) :
    matrixPhysicalPairedEquiv s (p, 0) ∈
      matrixPairedImage (matrixPhysicalPairedEquiv s) (regularNilpotentLinear s) a := by
  apply Submodule.mem_map.mpr
  refine ⟨(p, 0), ?_, rfl⟩
  exact (pairedAugmentationImage_iff (regularNilpotentLinear s) a (p, 0)).mpr
    ⟨hp, Submodule.zero_mem _⟩

theorem matrixPhysicalPairedRight_mem_image (s a : ℕ) (p : PauliLabel s)
    (hp : p ∈ LinearMap.range (regularNilpotentLinear s ^ a)) :
    matrixPhysicalPairedEquiv s (0, p) ∈
      matrixPairedImage (matrixPhysicalPairedEquiv s) (regularNilpotentLinear s) a := by
  apply Submodule.mem_map.mpr
  refine ⟨(0, p), ?_, rfl⟩
  exact (pairedAugmentationImage_iff (regularNilpotentLinear s) a (0, p)).mpr
    ⟨Submodule.zero_mem _, hp⟩

theorem matrixPhysicalSelectorLabel_square_mem_image {s : ℕ} (hs : 0 < s)
    (p : PauliLabel (s + s)) :
    ((matrixPhysicalSelectorLabel s ^ (2 : ℕ) - 1) :
      Module.End (ZMod 2) (PauliLabel (s + s))) p ∈
        matrixPairedImage (matrixPhysicalPairedEquiv s) (regularNilpotentLinear s) 1 := by
  obtain ⟨w, hw⟩ := matrixPhysicalSelectorLabel_square_difference hs p
  apply Submodule.mem_map.mpr
  refine ⟨(regularNilpotentLinear s w.1, regularNilpotentLinear s w.2), ?_, hw⟩
  change (regularNilpotentLinear s w.1, regularNilpotentLinear s w.2) ∈
    LinearMap.range (pairedAugmentation (regularNilpotentLinear s) ^ 1)
  refine ⟨w, ?_⟩
  simp only [pow_one, pairedAugmentation, LinearMap.prodMap_apply]

theorem matrix_compact_unphased_controlled_upper {h : ℕ} (hh : 1 ≤ h) :
    hierarchy (targetSize h + 1) (h + 4)
      (controlled (selectorTarget (blockSize h))) := by
  let s := blockSize h
  let E := matrixPhysicalPairedEquiv s
  let N := regularNilpotentLinear s
  let S := matrixPhysicalSelector s
  let T0 := matrixPhysicalShift0 s
  let T1 := matrixPhysicalShift1 s
  obtain ⟨e, p, hHerm, hImage, hp0raw, hp1raw⟩ := matrixPhysicalShifts_signed_endpoint hh
  let p0 := E (p, 0)
  let p1 := E (0, p)
  have hp0 : ((T0 ^ (2 ^ h) : MatrixUnitary (s + s)) : QuantumMatrix (s + s)) =
      signedOrderedPauli e p0 := by
    simpa only [signedOrderedPauli] using hp0raw
  have hp1 : ((T1 ^ (2 ^ h) : MatrixUnitary (s + s)) : QuantumMatrix (s + s)) =
      signedOrderedPauli e p1 := by
    simpa only [signedOrderedPauli] using hp1raw
  have hHerm0 : dot p0.2 p0.1 = 0 := matrixPhysicalPairedLeft_hermitian s p hHerm
  have hHerm1 : dot p1.2 p1.1 = 0 := matrixPhysicalPairedRight_hermitian s p hHerm
  have hImage0 : p0 ∈ matrixPairedImage E N (2 ^ (h - 1)) :=
    matrixPhysicalPairedLeft_mem_image s (2 ^ (h - 1)) p hImage
  have hImage1 : p1 ∈ matrixPairedImage E N (2 ^ (h - 1)) :=
    matrixPhysicalPairedRight_mem_image s (2 ^ (h - 1)) p hImage
  let k0 := matrixIntegerPowerSign (matrixPhysicalPairedStep0 s)
    (matrixPhysicalShiftSign0 s) p0 (2 ^ h)
  let k1 := matrixIntegerPowerSign (matrixPhysicalPairedStep1 s)
    (matrixPhysicalShiftSign1 s) p1 (2 ^ h)
  have h0 : ∀ t w, conjugate (matrixZpow T0 t) (orderedPauli w.1 w.2) =
      bitSign (k0 t w) • orderedPauli (matrixPairedIntAction0 E N h t w).1
        (matrixPairedIntAction0 E N h t w).2 :=
    matrixPhysicalShift0_int_signed e p0 hp0 hHerm0
  have h1 : ∀ t w, conjugate (matrixZpow T1 t) (orderedPauli w.1 w.2) =
      bitSign (k1 t w) • orderedPauli (matrixPairedIntAction1 E N h t w).1
        (matrixPairedIntAction1 E N h t w).2 :=
    matrixPhysicalShift1_int_signed e p1 hp1 hHerm1
  obtain ⟨hST0, hST1⟩ := matrixPhysicalSelector_shift_relations s
  have hUpper := matrixSelectorWord_twoControl_upper hh E N
    (matrix_blockSize_nilpotent hh) S T0 T1 (matrixPhysicalShifts_commute s)
    (matrixPhysicalSelector_fourth s) hST0 hST1
    (matrixPhysicalSelector_clifford s) (matrixPhysicalShift0_clifford s)
    (matrixPhysicalShift1_clifford s) k0 k1 h0 h1 e e p0 p1 hp0 hp1 hHerm0 hHerm1
    hImage0 hImage1 (matrixPhysicalSelectorLabel s) (matrixPhysicalSelectorSign s)
    (matrixPhysicalSelector_full_signed s)
    (matrixPhysicalSelectorLabel_square_mem_image (blockSize_pos h))
  change hierarchy (((s + s) + 1) + 1) (h + 4) (controlled (selectorTarget s))
  rw [← matrixPhysicalSelectorProfile_matrix]
  simpa only [matrixSelectorWord, matrixPhysicalSelectorProfile] using hUpper

theorem matrix_compact_controlled_upper {h : ℕ} (hh : 1 ≤ h) (m : ℕ) :
    hierarchy (targetSize h + 1) (max (h + 4) (m + 2)) (compactControlled h m) := by
  have hphase : PauliPhase ((scalarPhase m) ^ (2 ^ m)) := by
    rw [scalarPhase_period_power]
    exact Or.inr (Or.inr (Or.inl rfl))
  unfold compactControlled compactTarget
  exact controlled_scalar_phase_upper (by omega) (matrix_compact_unphased_controlled_upper hh)
    (scalarPhase_star_mul m) hphase

theorem compact_family_hierarchy_levels : compactFamilyStatement := by
  intro h m hh hm
  obtain ⟨hU, hThree, hPeriod⟩ := matrix_compact_target_properties h m hm
  exact ⟨hU, hThree, hPeriod, matrix_compact_controlled_exact_of_membership hh hm
    (matrix_compact_controlled_upper hh m)⟩

theorem compact_fixed_period_hierarchy_unbounded (r : ℕ) (hr : 5 ≤ r) :
    ∃ (n : ℕ) (U : QuantumMatrix n), unitaryMatrix U ∧ exactLevel 3 U ∧
      actualPauliPeriod 2 U ∧ exactLevel r (controlled U) := by
  refine ⟨targetSize (r - 4), compactTarget (r - 4) 2, ?_⟩
  have hfamily := compact_family_hierarchy_levels (r - 4) 2 (by omega) (by omega)
  have hmax : max ((r - 4) + 4) (2 + 2) = r := by omega
  simpa only [compactControlled, hmax] using hfamily

end QuantumProver.ControlledCliffordHierarchy

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section5.Localization.Identities

/-!
# The deterministic identities of the localization lemma

For a constant offset `P` with minimizer `S` (`S_z`), an offset `F` with `L²` components and
minimizer `St` (`S̃_z`) on one set `U`, writing `⟪X, Y⟫ = ⨍_U X · A_m Y`
(`Homogenization.blockPairingAverage`), the displays of `lem.localization` are

* `cross_identity_left`, `cross_identity_right`: `P · ⨍ A St = ⟪S, St⟫ = ⟪S, F⟫`,
* `quad_identity`: `⟪St, St⟫ = ⟪F, St⟫`,
* `quad_by_F`: `⟪St, St⟫ ≤ ⟪F, F⟫`,
* `cross_by_F`: `|P · ⨍ A St| ≤ ⟪S, S⟫^{1/2} ⟪F, F⟫^{1/2}`,
* `error_step1`: `|2 P · ⨍ A St| + ⟪St, St⟫ ≤ ⟪F,F⟫^{1/2} (2 ⟪S,S⟫^{1/2} + ⟪F,F⟫^{1/2})`.

Only the first variation is used. The energy identity `⟪S, S⟫ = P · A(Q) P` (needed only for the
crude bound on `S_z`) is `blockPairingAverage_self_eq_coarseBlockMatrix`, valid because the
offset of `S_z` is constant; `F_z` and `S̃_z` have no such closed form and none is used.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section5

open Homogenization

variable {d : ℕ} {U : Set (Vec d)} {a : CoeffField d} {lam Lam : ℝ}

theorem isBlockL2_constBlockState [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (P : BlockVec d) : IsBlockL2 U (constBlockState P) :=
  ⟨memVectorL2_const _, memVectorL2_const _⟩

theorem blockPairingAverage_sub_right [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hEll : IsEllipticFieldOn lam Lam U a) {X Y Z : BlockState d} (hX : IsBlockL2 U X)
    (hY : IsBlockL2 U Y) (hZ : IsBlockL2 U Z) :
    blockPairingAverage U a X (Y + (-1 : ℝ) • Z) =
      blockPairingAverage U a X Y - blockPairingAverage U a X Z := by
  rw [blockPairingAverage_add_right_of_isBlockL2 hEll hX hY (hZ.smul _),
    blockPairingAverage_smul_right]
  ring

section Identities

variable [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
  (hEll : IsEllipticFieldOn lam Lam U a) {P : BlockVec d} {F S St : BlockState d}
  (hF : IsBlockL2 U F) (hS : IsBlockOffsetMinimizer a U (constBlockState P) S)
  (hSt : IsBlockOffsetMinimizer a U F St)

omit [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)] in
theorem isBlockL2_of_minimizer_const [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hS : IsBlockOffsetMinimizer a U (constBlockState P) S) : IsBlockL2 U S :=
  ⟨hS.1.memVectorL2_potential (memVectorL2_const _),
    hS.1.memVectorL2_flux (memVectorL2_const _)⟩

omit [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)] in
theorem isBlockL2_of_minimizer (hF : IsBlockL2 U F) (hSt : IsBlockOffsetMinimizer a U F St) :
    IsBlockL2 U St :=
  ⟨hSt.1.memVectorL2_potential hF.1, hSt.1.memVectorL2_flux hF.2⟩

include hF hS hSt
include hEll

/-- `e.localization.cross.identity`, first equality. -/
theorem cross_identity_left :
    blockPairingAverage U a (constBlockState P) St = blockPairingAverage U a S St := by
  have hS2 := isBlockL2_of_minimizer_const hS
  have hSt2 := isBlockL2_of_minimizer hF hSt
  have h := blockPairingAverage_eq_zero_of_isBlockOffsetMinimizer hEll hF hSt
    (isBlockTestField_of_isBlockOffsetAdmissible hS.1)
  rw [blockPairingAverage_sub_right hEll hSt2 hS2 (isBlockL2_constBlockState P)] at h
  rw [blockPairingAverage_comm U a (constBlockState P) St, blockPairingAverage_comm U a S St]
  linarith only [h]

/-- `e.localization.cross.identity`, second equality. -/
theorem cross_identity_right :
    blockPairingAverage U a S St = blockPairingAverage U a S F := by
  have hS2 := isBlockL2_of_minimizer_const hS
  have hSt2 := isBlockL2_of_minimizer hF hSt
  have h := blockPairingAverage_eq_zero_of_isBlockOffsetMinimizer hEll
    (isBlockL2_constBlockState P) hS (isBlockTestField_of_isBlockOffsetAdmissible hSt.1)
  rw [blockPairingAverage_sub_right hEll hS2 hSt2 hF] at h
  linarith only [h]

omit hS in
/-- `e.localization.quad.identity`. -/
theorem quad_identity :
    blockPairingAverage U a St St = blockPairingAverage U a F St := by
  have hSt2 := isBlockL2_of_minimizer hF hSt
  have h := blockPairingAverage_eq_zero_of_isBlockOffsetMinimizer hEll hF hSt
    (isBlockTestField_of_isBlockOffsetAdmissible hSt.1)
  rw [blockPairingAverage_sub_right hEll hSt2 hSt2 hF] at h
  rw [blockPairingAverage_comm U a F St]
  linarith only [h]

omit hS in
/-- `e.localization.quad.by.F`. -/
theorem quad_by_F : blockPairingAverage U a St St ≤ blockPairingAverage U a F F := by
  have hSt2 := isBlockL2_of_minimizer hF hSt
  have h := blockPairingAverage_self_nonneg (a := a) hEll (F + (-1 : ℝ) • St)
  rw [blockPairingAverage_line hEll hF hSt2 (-1)] at h
  have hq := quad_identity hEll hF hSt
  rw [blockPairingAverage_comm U a F St] at h
  rw [blockPairingAverage_comm U a F St] at hq
  linarith only [h, hq]

/-- `e.localization.cross.by.F`. -/
theorem cross_by_F :
    |blockPairingAverage U a (constBlockState P) St| ≤
      Real.sqrt (blockPairingAverage U a S S) * Real.sqrt (blockPairingAverage U a F F) := by
  rw [cross_identity_left hEll hF hS hSt, cross_identity_right hEll hF hS hSt]
  exact abs_blockPairingAverage_le hEll (isBlockL2_of_minimizer_const hS) hF

/-- `e.localization.error.step1`. -/
theorem error_step1 :
    |2 * blockPairingAverage U a (constBlockState P) St| + blockPairingAverage U a St St ≤
      Real.sqrt (blockPairingAverage U a F F) *
        (2 * Real.sqrt (blockPairingAverage U a S S) + Real.sqrt (blockPairingAverage U a F F)) := by
  have h1 := cross_by_F hEll hF hS hSt
  have h2 := quad_by_F hEll hF hSt
  have h3 := Real.mul_self_sqrt (blockPairingAverage_self_nonneg (a := a) hEll F)
  rw [abs_mul, abs_two]
  nlinarith only [h1, h2, h3]

omit hS in
/-- The integrand of `lem.localization` splits as `2 P · A St + St · A St`. -/
theorem volumeAverage_slope_add_eq :
    volumeAverage U (fun x => blockVecDot ((2 : ℝ) • P + St.eval x)
        (blockMatVecMul (blockCoeffField a x) (St.eval x))) =
      2 * blockPairingAverage U a (constBlockState P) St + blockPairingAverage U a St St := by
  have hSt2 := isBlockL2_of_minimizer hF hSt
  have hi1 := (isBlockL2_constBlockState (U := U) P).integrableOn_pair (a := a) hEll hSt2
  have hi2 := hSt2.integrableOn_pair (a := a) hEll hSt2
  have e : (fun x => blockVecDot ((2 : ℝ) • P + St.eval x)
        (blockMatVecMul (blockCoeffField a x) (St.eval x))) =
      fun x => 2 * blockPairingIntegrand a (constBlockState P) St x +
        blockPairingIntegrand a St St x := by
    funext x
    simp [blockPairingIntegrand, blockVecDot_add_left, blockVecDot_smul_left, constBlockState,
      BlockState.eval]
  unfold volumeAverage
  rw [e, MeasureTheory.integral_add (hi1.const_mul 2) hi2, MeasureTheory.integral_const_mul]
  unfold blockPairingAverage volumeAverage
  ring

/-- The bound of `lem.localization`, Step 1, for the averaged integrand. -/
theorem abs_volumeAverage_slope_add_le :
    |volumeAverage U (fun x => blockVecDot ((2 : ℝ) • P + St.eval x)
        (blockMatVecMul (blockCoeffField a x) (St.eval x)))| ≤
      Real.sqrt (blockPairingAverage U a F F) *
        (2 * Real.sqrt (blockPairingAverage U a S S) + Real.sqrt (blockPairingAverage U a F F)) := by
  rw [volumeAverage_slope_add_eq hEll hF hSt]
  have h := error_step1 hEll hF hS hSt
  have h0 := blockPairingAverage_self_nonneg (a := a) hEll St
  refine le_trans (abs_add_le _ _) ?_
  rw [abs_of_nonneg h0]
  exact h

end Identities

/-- The energy identity for the constant offset of `S_z`: `⟪S, S⟫ = P · A(Q) P`. -/
theorem blockPairingAverage_self_eq_coarseBlockMatrix [NeZero d] (Q : TriadicCube d)
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a) (P : BlockVec d) {S : BlockState d}
    (hS : IsBlockOffsetMinimizer a (cubeSet Q) (constBlockState P) S) :
    blockPairingAverage (cubeSet Q) a S S =
      blockVecDot P (blockMatVecMul (coarseBlockMatrix (cubeSet Q) a) P) := by
  have h := volumeAverage_blockEnergyDensity_eq_half_coarseBlockMatrix Q hEll P hS
  have h2 := blockEnergyAverage_eq_half_blockPairingAverage_self (cubeSet Q) a S
  have h3 : blockEnergyAverage (cubeSet Q) a S =
      volumeAverage (cubeSet Q) (blockEnergyDensity a S) := rfl
  linarith only [h, h2, h3]

/-! ## Witness -/

/-- Satisfiability: with the identity coefficient on the unit cube, any constant offset `P` and
any `L²` offset `F` (here a second constant), both minimizers exist, and the hypotheses of
`error_step1` and `abs_volumeAverage_slope_add_le` hold. -/
example [NeZero d] (P P' : BlockVec d) :
    ∃ S St : BlockState d,
      IsBlockOffsetMinimizer (fun _ => (1 : Mat d)) (cubeSet (originCube d 0))
        (constBlockState P) S ∧
      IsBlockOffsetMinimizer (fun _ => (1 : Mat d)) (cubeSet (originCube d 0))
        (constBlockState P') St ∧
      |volumeAverage (cubeSet (originCube d 0)) (fun x => blockVecDot ((2 : ℝ) • P + St.eval x)
        (blockMatVecMul (blockCoeffField (fun _ => (1 : Mat d)) x) (St.eval x)))| ≤
      Real.sqrt (blockPairingAverage (cubeSet (originCube d 0)) (fun _ => (1 : Mat d))
          (constBlockState P') (constBlockState P')) *
        (2 * Real.sqrt (blockPairingAverage (cubeSet (originCube d 0)) (fun _ => (1 : Mat d)) S S) +
          Real.sqrt (blockPairingAverage (cubeSet (originCube d 0)) (fun _ => (1 : Mat d))
            (constBlockState P') (constBlockState P'))) := by
  have hE := isEllipticFieldOn_one (d := d) (measurableSet_cubeSet (originCube d 0))
  obtain ⟨S, hS, -⟩ := exists_isBlockOffsetMinimizer_cubeSet (a := fun _ => (1 : Mat d))
    (lam := 1) (Lam := 1) (originCube d 0) hE (F := constBlockState P)
    (memVectorL2_const _) (memVectorL2_const _)
  obtain ⟨St, hSt, -⟩ := exists_isBlockOffsetMinimizer_cubeSet (a := fun _ => (1 : Mat d))
    (lam := 1) (Lam := 1) (originCube d 0) hE (F := constBlockState P')
    (memVectorL2_const _) (memVectorL2_const _)
  exact ⟨S, St, hS, hSt,
    abs_volumeAverage_slope_add_le hE (isBlockL2_constBlockState P') hS hSt⟩

end SuperdiffusionCLT.Section5

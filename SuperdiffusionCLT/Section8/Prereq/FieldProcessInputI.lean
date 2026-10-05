/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Prereq.FieldProcessInputH
public import SuperdiffusionCLT.Section8.DivergenceForm.WholeSpace.LocalizedConservativity
public import SuperdiffusionCLT.Section8.DivergenceForm.WholeSpace.LocalizedBoundaryAsymptotics
public import SuperdiffusionCLT.Section8.DivergenceForm.WholeSpace.ResolventIdentity

/-!
# Conservativity of the analytic minimal resolvent

The rough and smooth-divergence constants of the split datum on the active support of the cubic
boundary cutoff are linear in the exhaustion index.  Together with the localized boundary defect
bound and the elementary asymptotic of `LocalizedBoundaryAsymptotics`, this shows that the
analytic boundary defect of the constant-one resolvent tends to zero along the cubic exhaustion,
hence that `mu` times the analytic minimal resolvent of one is one.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section8

open Homogenization Homogenization.Book.Ch02 MeasureTheory Set
open Filter Topology
open SuperdiffusionCLT.Section8.DivergenceForm
open SuperdiffusionCLT.Section8.DivergenceForm.Decay
open SuperdiffusionCLT.Section8.DivergenceForm.WholeSpaceAnalyticData
open SuperdiffusionCLT.Section8.Common.Regularity.Ported
open MarkovProcess.Semigroup
open scoped ENNReal

noncomputable section

variable {d : ℕ} [NeZero d] {A : WholeSpaceAnalyticData d} {Sp : WholeSpaceLocalizedSplitData A}

namespace LogGrowthBounds

/-- Linear-in-scale envelope for the rough active-support constant. -/
def boundaryRoughConst (T : LogGrowthBounds Sp) : ℝ :=
  2 * T.cs

/-- Linear-in-scale envelope for the smooth-divergence active-support
constant. -/
def boundarySmoothDivConst (T : LogGrowthBounds Sp) : ℝ :=
  2 * (Real.sqrt d * (d : ℝ) * T.cg)

theorem boundaryRoughConst_nonneg (T : LogGrowthBounds Sp) :
    0 ≤ boundaryRoughConst T := by
  unfold boundaryRoughConst
  exact mul_nonneg (by norm_num) (T.cs_nonneg)

theorem boundarySmoothDivConst_nonneg (T : LogGrowthBounds Sp) :
    0 ≤ boundarySmoothDivConst T := by
  unfold boundarySmoothDivConst
  exact mul_nonneg (by norm_num)
    (mul_nonneg
      (mul_nonneg (Real.sqrt_nonneg d) (Nat.cast_nonneg d))
      (T.cg_nonneg))

private theorem fieldInput_logWeight_one_add_triadic_le (m : ℕ) :
    fieldInput_logWeight (1 + (3 : ℝ) ^ m) ≤ 2 * ((m : ℝ) + 1) := by
  have hp : 1 ≤ (3 : ℝ) ^ m := one_le_pow₀ (by norm_num)
  have harg : 1 + (3 : ℝ) ^ m ≤ 2 * (3 : ℝ) ^ m := by
    linarith only [hp]
  have hlog := Real.strictMonoOn_log.monotoneOn
    (by positivity : 0 < 1 + (3 : ℝ) ^ m)
    (by positivity : 0 < 2 * (3 : ℝ) ^ m) harg
  have hlog2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    norm_num at h ⊢
    exact h
  have hlog3 : Real.log 3 ≤ 2 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 by norm_num)
    norm_num at h ⊢
    exact h
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
      (ne_of_gt (pow_pos (by norm_num) m)), Real.log_pow] at hlog
  unfold fieldInput_logWeight
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hmul := mul_le_mul_of_nonneg_left hlog3 hm0
  linarith only [hlog, hlog2, hmul]

/-- The rough constant on the active cutoff support is at most linear in the
exhaustion index. -/
theorem roughBound_zero_triadic_le (T : LogGrowthBounds Sp) (m : ℕ) :
    Sp.roughBound 0 ((3 : ℝ) ^ m) ≤
      boundaryRoughConst T * ((m : ℝ) + 1) := by
  have hlog := fieldInput_logWeight_one_add_triadic_le m
  have hC := T.cs_nonneg
  rw [T.rough_eq 0 ((3 : ℝ) ^ m)]
  unfold fieldInput_obsRadius boundaryRoughConst
  simp only [euclideanNorm_zero, add_zero]
  convert mul_le_mul_of_nonneg_left hlog hC using 1
  ring

/-- The smooth-divergence constant on the active cutoff support is at most
linear in the exhaustion index. -/
theorem smoothDivBound_zero_triadic_le (T : LogGrowthBounds Sp) (m : ℕ) :
    Sp.smoothDivBound 0 ((3 : ℝ) ^ m) ≤
      boundarySmoothDivConst T * ((m : ℝ) + 1) := by
  have hlog := fieldInput_logWeight_one_add_triadic_le m
  have hC : 0 ≤ Real.sqrt d * (d : ℝ) *
      T.cg :=
    mul_nonneg
      (mul_nonneg (Real.sqrt_nonneg d) (Nat.cast_nonneg d))
      (T.cg_nonneg)
  rw [T.smooth_eq 0 ((3 : ℝ) ^ m)]
  unfold fieldInput_obsRadius boundarySmoothDivConst
  simp only [euclideanNorm_zero, add_zero]
  convert mul_le_mul_of_nonneg_left hlog hC using 1
  ring


/-- A scale-independent upper coefficient for the localized Agmon constant
on the active support of the cubic boundary cutoff. -/
def boundaryLocalizedUpperConst (T : LogGrowthBounds Sp) (mu : PositiveShift) : ℝ :=
  Real.sqrt 2 * (A.nu + boundaryRoughConst T +
    2 * boundarySmoothDivConst T * Real.sqrt (A.nu / (mu : ℝ)))

theorem boundaryLocalizedUpperConst_pos (T : LogGrowthBounds Sp) (mu : PositiveShift) :
    0 < boundaryLocalizedUpperConst T mu := by
  unfold boundaryLocalizedUpperConst
  have hrest : 0 ≤ boundaryRoughConst T +
      2 * boundarySmoothDivConst T * Real.sqrt (A.nu / (mu : ℝ)) :=
    add_nonneg (boundaryRoughConst_nonneg T)
      (mul_nonneg
        (mul_nonneg (by norm_num) (boundarySmoothDivConst_nonneg T))
        (Real.sqrt_nonneg _))
  exact mul_pos (Real.sqrt_pos.2 (by norm_num)) (by
    linarith only [A.hnu, hrest])

/-- The effective localized upper constant grows at most linearly in the
exhaustion index. -/
theorem localizedInteriorUpper_boundary_le (T : LogGrowthBounds Sp) (mu : PositiveShift) (m : ℕ) :
    localizedInteriorUpper A.nu (mu : ℝ)
        (Sp.roughBound 0 ((3 : ℝ) ^ m))
        (Sp.smoothDivBound 0 ((3 : ℝ) ^ m)) ≤
      boundaryLocalizedUpperConst T mu * ((m : ℝ) + 1) := by
  let Ks := Sp.roughBound 0 ((3 : ℝ) ^ m)
  let Kl := Sp.smoothDivBound 0 ((3 : ℝ) ^ m)
  let Cs := boundaryRoughConst T
  let Cl := boundarySmoothDivConst T
  have hm : 1 ≤ (m : ℝ) + 1 := by
    exact le_add_of_nonneg_left (Nat.cast_nonneg m)
  have hKs : Ks ≤ Cs * ((m : ℝ) + 1) :=
    roughBound_zero_triadic_le T m
  have hKl : Kl ≤ Cl * ((m : ℝ) + 1) :=
    smoothDivBound_zero_triadic_le T m
  have hCs : 0 ≤ Cs := boundaryRoughConst_nonneg T
  have hCl : 0 ≤ Cl := boundarySmoothDivConst_nonneg T
  have hsqrt : 0 ≤ Real.sqrt (A.nu / (mu : ℝ)) := Real.sqrt_nonneg _
  have hsqrtTwo : 1 ≤ Real.sqrt 2 := by norm_num
  unfold localizedInteriorUpper
  split_ifs with hzero
  · have hnu : A.nu ≤ A.nu * ((m : ℝ) + 1) := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hm A.hnu.le
    calc
      A.nu + Ks ≤ (A.nu + Cs) * ((m : ℝ) + 1) := by
        calc
          A.nu + Ks ≤ A.nu * ((m : ℝ) + 1) + Cs * ((m : ℝ) + 1) :=
            add_le_add hnu hKs
          _ = _ := by ring
      _ ≤ Real.sqrt 2 * (A.nu + Cs + 2 * Cl * Real.sqrt (A.nu / (mu : ℝ))) *
          ((m : ℝ) + 1) := by
        have hinside : A.nu + Cs ≤
            Real.sqrt 2 * (A.nu + Cs + 2 * Cl * Real.sqrt (A.nu / (mu : ℝ))) := by
          have hbase : 0 ≤ A.nu + Cs := add_nonneg A.hnu.le hCs
          have hsmooth : 0 ≤ 2 * Cl * Real.sqrt (A.nu / (mu : ℝ)) :=
            mul_nonneg (mul_nonneg (by norm_num) hCl) hsqrt
          calc
            A.nu + Cs ≤ A.nu + Cs + 2 * Cl * Real.sqrt (A.nu / (mu : ℝ)) :=
              le_add_of_nonneg_right hsmooth
            _ ≤ Real.sqrt 2 *
                (A.nu + Cs + 2 * Cl * Real.sqrt (A.nu / (mu : ℝ))) := by
              simpa only [one_mul] using mul_le_mul_of_nonneg_right hsqrtTwo
                (add_nonneg hbase hsmooth)
        exact mul_le_mul_of_nonneg_right hinside (by positivity)
      _ = boundaryLocalizedUpperConst T mu * ((m : ℝ) + 1) := rfl
  · unfold localizedAgmonUpper
    have hnu : A.nu ≤ A.nu * ((m : ℝ) + 1) := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hm A.hnu.le
    have hsmooth : 2 * Kl * Real.sqrt (A.nu / (mu : ℝ)) ≤
        (2 * Cl * Real.sqrt (A.nu / (mu : ℝ))) * ((m : ℝ) + 1) := by
      calc
        2 * Kl * Real.sqrt (A.nu / (mu : ℝ)) ≤
            2 * (Cl * ((m : ℝ) + 1)) * Real.sqrt (A.nu / (mu : ℝ)) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hKl (by norm_num)) hsqrt
        _ = _ := by ring
    have hinside : A.nu + Ks + 2 * Kl * Real.sqrt (A.nu / (mu : ℝ)) ≤
        (A.nu + Cs + 2 * Cl * Real.sqrt (A.nu / (mu : ℝ))) *
          ((m : ℝ) + 1) := by
      calc
        _ ≤ A.nu * ((m : ℝ) + 1) + Cs * ((m : ℝ) + 1) +
            (2 * Cl * Real.sqrt (A.nu / (mu : ℝ))) * ((m : ℝ) + 1) :=
          add_le_add (add_le_add hnu hKs) hsmooth
        _ = _ := by ring
    simpa only [Ks, Kl, Cs, Cl, boundaryLocalizedUpperConst, mul_assoc] using
      mul_le_mul_of_nonneg_left hinside (Real.sqrt_nonneg 2)

omit [NeZero d] in
private theorem euclideanNorm_add_le (x y : Vec d) :
    euclideanNorm (x + y) ≤ euclideanNorm x + euclideanNorm y := by
  have hnorm : ∀ w : Vec d, euclideanNorm w = ‖HilbertVec.ofVecL d w‖ := by
    intro w
    rw [HilbertVec.ofVecL_apply, euclideanNorm_eq_norm_ofVec]
  rw [hnorm, hnorm x, hnorm y, map_add]
  exact norm_add_le _ _

private theorem natCast_add_one_le_three_pow (m : ℕ) :
    (m : ℝ) + 1 ≤ (3 : ℝ) ^ m := by
  induction m with
  | zero => norm_num
  | succ m ih =>
      rw [pow_succ]
      norm_num only [Nat.cast_add, Nat.cast_one]
      have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      calc
        (m : ℝ) + 1 + 1 ≤ 3 * ((m : ℝ) + 1) := by
          linarith only [hm]
        _ ≤ 3 * (3 : ℝ) ^ m :=
          mul_le_mul_of_nonneg_left ih (by norm_num)
        _ = (3 : ℝ) ^ m * 3 := by ring

/-- The analytic boundary defect for the stream coefficient tends pointwise
to zero along the cubic exhaustion. -/
theorem tendsto_abs_analyticCubeBoundaryRemainder
    (T : LogGrowthBounds Sp)
    (mu : PositiveShift) (x : Vec d) :
    Tendsto (fun m ↦ |1 - (mu : ℝ) *
        A.analyticCubeResolvent mu
          (fun _ : Vec d ↦ (1 : ℝ)) measurable_const
          (D := 1) (fun _ ↦ by norm_num) m x|) atTop (nhds 0) := by
  let L := Sp
  let r₀ := L.freezingRadius x
  let U := boundaryLocalizedUpperConst T mu
  let alpha : ℝ := 1 / 2
  let q : ℝ := alpha / (alpha + (d : ℝ) / 2)
  let c : ℝ := Real.sqrt (A.nu * (mu : ℝ)) / (2 * Real.sqrt 2 * U) * q / 4
  have hU : 0 < U := boundaryLocalizedUpperConst_pos T mu
  have hr₀ : 0 < r₀ := L.freezingRadius_pos x
  have hq : 0 < q := by unfold q alpha; positivity
  have hc : 0 < c := by
    unfold c
    exact div_pos
      (mul_pos
        (div_pos (Real.sqrt_pos.2 (mul_pos A.hnu mu.property)) (by positivity)) hq)
      (by norm_num)
  let P : ℕ → ℝ := fun m : ℕ ↦
    localizedInteriorDecayConstant d A.nu (mu : ℝ)
      (L.roughBound 0 ((3 : ℝ) ^ m)) (L.smoothDivBound 0 ((3 : ℝ) ^ m)) 1
      (cubeBoundaryCutoffUniformGradientBudget (d := d))
      (volume (wholeSpaceCube d m)).toReal alpha
      ((mu : ℝ) * (min (mu : ℝ) A.nu)⁻¹ *
        (volume (wholeSpaceCube d m)).toReal) r₀
  have hPexists : ∃ C : ℝ, 0 ≤ C ∧ ∀ m : ℕ,
      P m ≤ C * ((m : ℝ) + 1) * ((3 : ℝ) ^ (d + 1)) ^ m := by
    let Ceta := cubeBoundaryCutoffUniformGradientBudget (d := d)
    let V0 : ℝ := (2 : ℝ) ^ d
    let Q : ℝ := 8 * U ^ 2 / (A.nu * (mu : ℝ)) * Ceta * V0
    let den : ℝ := Real.sqrt ((volume (smallContrastUnitBall d)).toReal) *
      Real.sqrt ((r₀ / 2) ^ d)
    let e : ℝ := (mu : ℝ) * (min (mu : ℝ) A.nu)⁻¹
    let C2 : ℝ := smallContrastZerothSchauderConstant d *
      (r₀ ^ (1 - alpha - (d : ℝ) / 2) * e * V0 +
        r₀ ^ (2 - alpha) * ((mu : ℝ) / A.nu)) * (r₀ / 2) ^ alpha
    let C : ℝ := (Q + 1) / den + C2
    have hCeta : 0 ≤ Ceta := by
      unfold Ceta cubeBoundaryCutoffUniformGradientBudget
      positivity
    have hV0 : 0 ≤ V0 := by unfold V0; positivity
    have hQ : 0 ≤ Q := by
      unfold Q
      exact mul_nonneg
        (mul_nonneg
          (div_nonneg (mul_nonneg (by norm_num) (sq_nonneg U))
            (mul_nonneg A.hnu.le mu.property.le)) hCeta) hV0
    have hden : 0 < den := by
      unfold den
      exact mul_pos (Real.sqrt_pos.2 unitBallVolume_pos)
        (Real.sqrt_pos.2 (pow_pos (half_pos hr₀) d))
    have he : 0 ≤ e := by
      unfold e
      exact mul_nonneg mu.property.le
        (inv_nonneg.mpr (le_of_lt (lt_min mu.property A.hnu)))
    have hC2 : 0 ≤ C2 := by
      unfold C2
      exact mul_nonneg
        (mul_nonneg (smallContrastZerothSchauderConstant_nonneg d)
          (add_nonneg
            (mul_nonneg
              (mul_nonneg (Real.rpow_nonneg hr₀.le _) he) hV0)
            (mul_nonneg (Real.rpow_nonneg hr₀.le _)
              (div_nonneg mu.property.le A.hnu.le))))
        (Real.rpow_nonneg (half_pos hr₀).le _)
    have hC : 0 ≤ C := by
      unfold C
      exact add_nonneg (div_nonneg (by linarith only [hQ]) hden.le) hC2
    refine ⟨C, hC, fun m ↦ ?_⟩
    let t : ℝ := (m : ℝ) + 1
    let B : ℝ := ((3 : ℝ) ^ d) ^ m
    let V : ℝ := (volume (wholeSpaceCube d m)).toReal
    let Lm := localizedInteriorUpper A.nu (mu : ℝ)
      (L.roughBound 0 ((3 : ℝ) ^ m)) (L.smoothDivBound 0 ((3 : ℝ) ^ m))
    let X : ℝ := 8 * Lm ^ 2 / (A.nu * (mu : ℝ)) * Ceta * V
    have ht : 1 ≤ t := by
      unfold t
      exact le_add_of_nonneg_left (Nat.cast_nonneg m)
    have hB : 1 ≤ B := by
      unfold B
      exact one_le_pow₀ (one_le_pow₀ (by norm_num))
    have hV : V = V0 * B := by
      unfold V V0 B
      rw [volume_wholeSpaceCube_toReal, mul_pow]
      congr 1
      rw [← pow_mul, Nat.mul_comm m d, pow_mul]
    have hLm : Lm ≤ U * t := by
      simpa only [Lm, U, t, L] using
        localizedInteriorUpper_boundary_le T mu m
    have hLm0 : 0 < Lm := localizedInteriorUpper_pos A.hnu
      (L.roughBound_nonneg 0 ((3 : ℝ) ^ m) (pow_nonneg (by norm_num) m))
      (L.smoothDivBound_nonneg 0 ((3 : ℝ) ^ m) (pow_nonneg (by norm_num) m))
    have hX : 0 ≤ X := by
      unfold X
      exact mul_nonneg
        (mul_nonneg
          (div_nonneg (mul_nonneg (by norm_num) (sq_nonneg Lm))
            (mul_nonneg A.hnu.le mu.property.le)) hCeta) ENNReal.toReal_nonneg
    have hXbound : X ≤ Q * t ^ 2 * B := by
      have hsq : Lm ^ 2 ≤ (U * t) ^ 2 :=
        pow_le_pow_left₀ hLm0.le hLm 2
      have hK : 0 ≤ 8 / (A.nu * (mu : ℝ)) * Ceta * V0 := by
        exact mul_nonneg
          (mul_nonneg (div_nonneg (by norm_num : (0 : ℝ) ≤ 8)
            (mul_nonneg A.hnu.le mu.property.le)) hCeta) hV0
      have hB0 : 0 ≤ B := zero_le_one.trans hB
      unfold X
      rw [hV]
      unfold Q
      calc
        8 * Lm ^ 2 / (A.nu * (mu : ℝ)) * Ceta * (V0 * B) =
            (8 / (A.nu * (mu : ℝ)) * Ceta * V0) * Lm ^ 2 * B := by ring
        _ ≤ (8 / (A.nu * (mu : ℝ)) * Ceta * V0) * (U * t) ^ 2 * B :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsq hK) hB0
        _ = (8 * U ^ 2 / (A.nu * (mu : ℝ)) * Ceta * V0) * t ^ 2 * B := by ring
    have hsqrtX : Real.sqrt X ≤ X + 1 := by
      have hs := Real.sqrt_nonneg X
      have hs2 := Real.sq_sqrt hX
      nlinarith only [hs, hs2, sq_nonneg (Real.sqrt X - 1)]
    have hXone : X + 1 ≤ (Q + 1) * t ^ 2 * B := by
      have htb : 1 ≤ t ^ 2 * B := by
        calc
          (1 : ℝ) = 1 * 1 := by ring
          _ ≤ t ^ 2 * B := mul_le_mul (one_le_pow₀ ht) hB (by norm_num)
            (pow_nonneg (zero_le_one.trans ht) 2)
      calc
        X + 1 ≤ Q * t ^ 2 * B + 1 := by linarith only [hXbound]
        _ ≤ Q * t ^ 2 * B + 1 * (t ^ 2 * B) :=
          by simp only [one_mul]; linarith only [htb]
        _ = (Q + 1) * t ^ 2 * B := by ring
    have hfirst : Real.sqrt X /
          Real.sqrt ((volume (smallContrastUnitBall d)).toReal) /
          Real.sqrt ((r₀ / 2) ^ d) ≤
        ((Q + 1) / den) * t ^ 2 * B := by
      calc
        _ ≤ (X + 1) /
            Real.sqrt ((volume (smallContrastUnitBall d)).toReal) /
            Real.sqrt ((r₀ / 2) ^ d) := by gcongr
        _ ≤ ((Q + 1) * t ^ 2 * B) /
            Real.sqrt ((volume (smallContrastUnitBall d)).toReal) /
            Real.sqrt ((r₀ / 2) ^ d) := by gcongr
        _ = ((Q + 1) / den) * t ^ 2 * B := by
          unfold den
          field_simp
    have hsecond : smallContrastZerothSchauderConstant d *
          (r₀ ^ (1 - alpha - (d : ℝ) / 2) * (e * V) +
            r₀ ^ (2 - alpha) * ((mu : ℝ) / A.nu)) *
          (r₀ / 2) ^ alpha ≤ C2 * t ^ 2 * B := by
      have htb : 1 ≤ t ^ 2 * B :=
        calc
          (1 : ℝ) = 1 * 1 := by ring
          _ ≤ t ^ 2 * B := mul_le_mul (one_le_pow₀ ht) hB (by norm_num)
            (pow_nonneg (zero_le_one.trans ht) 2)
      rw [hV]
      unfold C2
      have hleft0 : 0 ≤ smallContrastZerothSchauderConstant d :=
        smallContrastZerothSchauderConstant_nonneg d
      have hrpow1 : 0 ≤ r₀ ^ (1 - alpha - (d : ℝ) / 2) :=
        Real.rpow_nonneg hr₀.le _
      have hrpow2 : 0 ≤ r₀ ^ (2 - alpha) := Real.rpow_nonneg hr₀.le _
      have hrpow3 : 0 ≤ (r₀ / 2) ^ alpha :=
        Real.rpow_nonneg (half_pos hr₀).le _
      have hmain :
          r₀ ^ (1 - alpha - (d : ℝ) / 2) * (e * (V0 * B)) +
              r₀ ^ (2 - alpha) * ((mu : ℝ) / A.nu) ≤
            (r₀ ^ (1 - alpha - (d : ℝ) / 2) * e * V0 +
              r₀ ^ (2 - alpha) * ((mu : ℝ) / A.nu)) * (t ^ 2 * B) := by
        have hterm1 :
            r₀ ^ (1 - alpha - (d : ℝ) / 2) * (e * (V0 * B)) ≤
              (r₀ ^ (1 - alpha - (d : ℝ) / 2) * e * V0) * (t ^ 2 * B) := by
          have ht2 : 1 ≤ t ^ 2 := one_le_pow₀ ht
          have hBscale : B ≤ t ^ 2 * B := by
            simpa only [one_mul] using
              mul_le_mul_of_nonneg_right ht2 (zero_le_one.trans hB)
          have hcoef : 0 ≤ r₀ ^ (1 - alpha - (d : ℝ) / 2) * e * V0 :=
            mul_nonneg (mul_nonneg hrpow1 he) hV0
          calc
            _ = (r₀ ^ (1 - alpha - (d : ℝ) / 2) * e * V0) * B := by ring
            _ ≤ (r₀ ^ (1 - alpha - (d : ℝ) / 2) * e * V0) * (t ^ 2 * B) :=
              mul_le_mul_of_nonneg_left hBscale hcoef
        have hterm2 := mul_le_mul_of_nonneg_left htb
          (mul_nonneg hrpow2 (div_nonneg mu.property.le A.hnu.le))
        calc
          _ ≤ (r₀ ^ (1 - alpha - (d : ℝ) / 2) * e * V0) * (t ^ 2 * B) +
              (r₀ ^ (2 - alpha) * ((mu : ℝ) / A.nu)) * (t ^ 2 * B) :=
            add_le_add hterm1 (by simpa only [mul_one] using hterm2)
          _ = _ := by ring
      convert mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hmain hleft0) hrpow3 using 1
      ring
    have hPquad : P m ≤ C * t ^ 2 * B := by
      calc
        P m ≤ ((Q + 1) / den) * t ^ 2 * B + C2 * t ^ 2 * B := by
          convert add_le_add hfirst hsecond using 1
          dsimp only [P, localizedInteriorDecayConstant, X, e, V, Lm, Ceta]
          simp only [one_mul, mul_one]
        _ = ((Q + 1) / den + C2) * t ^ 2 * B := by ring
        _ = C * t ^ 2 * B := by rfl
    have htThree : t ≤ (3 : ℝ) ^ m := by
      simpa only [t] using natCast_add_one_le_three_pow m
    calc
      P m ≤ C * t ^ 2 * B := hPquad
      _ ≤ C * t * ((3 : ℝ) ^ m) * B := by
        have hCt : 0 ≤ C * t := mul_nonneg hC (zero_le_one.trans ht)
        calc
          C * t ^ 2 * B = (C * t) * t * B := by ring
          _ ≤ (C * t) * ((3 : ℝ) ^ m) * B := by gcongr
      _ = C * ((m : ℝ) + 1) * ((3 : ℝ) ^ (d + 1)) ^ m := by
        unfold t B
        rw [pow_add, mul_pow]
        ring
  obtain ⟨C, hC, hPC⟩ := hPexists
  have hmajor := tendsto_triadicVolume_mul_exp_neg_triadic_div_linear
    (d + 1) hC hc
  refine squeeze_zero' (Filter.Eventually.of_forall fun m ↦ abs_nonneg _) ?_ hmajor
  filter_upwards [((tendsto_pow_atTop_atTop_of_one_lt
    (by norm_num : (1 : ℝ) < 3)).eventually_gt_atTop
      (4 * (euclideanNorm x + r₀ / 2 + 1)))] with m hm
  have hball : euclideanBall x r₀ ⊆ wholeSpaceCube d m := by
    intro y hy
    rw [mem_wholeSpaceCube_iff]
    have hdist := euclideanNorm_sub_lt_of_mem_euclideanBall hr₀.le hy
    have hnormy : euclideanNorm y ≤ euclideanNorm (y - x) + euclideanNorm x := by
      convert euclideanNorm_add_le (d := d) (y - x) x using 1
      ring_nf
    have hnormlt : euclideanNorm y < (3 : ℝ) ^ m := by
      exact lt_of_le_of_lt hnormy
        (by linarith only [hdist, hm, hr₀, euclideanNorm_nonneg x])
    intro i
    exact abs_lt.mp ((abs_coordinate_le_euclideanNorm y i).trans_lt hnormlt)
  have hinner : euclideanBall x (r₀ / 2) ⊆
      euclideanBall 0 (cubeBoundaryCutoffInnerRadius m) := by
    intro y hy
    have hdist := euclideanNorm_sub_lt_of_mem_euclideanBall
      (half_pos hr₀).le hy
    have hnormy : euclideanNorm y ≤ euclideanNorm (y - x) + euclideanNorm x := by
      convert euclideanNorm_add_le (d := d) (y - x) x using 1
      ring_nf
    have hhalf : euclideanNorm x + r₀ / 2 < (3 : ℝ) ^ m / 2 := by
      linarith only [hm, euclideanNorm_nonneg x, hr₀]
    have hnormlt : euclideanNorm (y - 0) < cubeBoundaryCutoffInnerRadius m := by
      simp only [sub_zero]
      unfold cubeBoundaryCutoffInnerRadius
      linarith only [hdist, hnormy, hhalf]
    change euclideanSqDist y 0 < cubeBoundaryCutoffInnerRadius m ^ 2
    rw [show euclideanSqDist y 0 = euclideanNorm (y - 0) ^ 2 by
      rw [euclideanNorm_sq]; rfl]
    exact (sq_lt_sq₀ (euclideanNorm_nonneg _)
      (by unfold cubeBoundaryCutoffInnerRadius; positivity)).2 hnormlt
  have hlayer : -cubeBoundaryCutoffInnerRadius m + 1 ≤
      -(euclideanNorm (x - 0) + r₀ / 2) := by
    simp only [sub_zero]
    unfold cubeBoundaryCutoffInnerRadius
    have hhalf : euclideanNorm x + r₀ / 2 + 1 ≤ (3 : ℝ) ^ m / 2 := by
      linarith only [hm, euclideanNorm_nonneg x, hr₀]
    linarith only [hhalf]
  have hdecay := A.abs_analyticCubeBoundaryRemainder_le_localized L mu m
    (x := x) hball hinner hlayer
  have hLupper := localizedInteriorUpper_boundary_le T mu m
  have hLpos := localizedInteriorUpper_pos (mass := (mu : ℝ)) A.hnu
    (L.roughBound_nonneg 0 ((3 : ℝ) ^ m) (pow_nonneg (by norm_num) m))
    (L.smoothDivBound_nonneg 0 ((3 : ℝ) ^ m) (pow_nonneg (by norm_num) m))
  have hrate : c * 4 / ((m : ℝ) + 1) ≤
      agmonRate A.nu
        (localizedInteriorUpper A.nu (mu : ℝ)
          (L.roughBound 0 ((3 : ℝ) ^ m))
          (L.smoothDivBound 0 ((3 : ℝ) ^ m))) (mu : ℝ) * q := by
    unfold c agmonRate
    have hmpos : 0 < (m : ℝ) + 1 := by positivity
    have hden : 0 < 2 * Real.sqrt 2 *
        localizedInteriorUpper A.nu (mu : ℝ)
          (L.roughBound 0 ((3 : ℝ) ^ m))
          (L.smoothDivBound 0 ((3 : ℝ) ^ m)) := by positivity
    have hdenU : 2 * Real.sqrt 2 *
        localizedInteriorUpper A.nu (mu : ℝ)
          (L.roughBound 0 ((3 : ℝ) ^ m))
          (L.smoothDivBound 0 ((3 : ℝ) ^ m)) ≤
        (2 * Real.sqrt 2 * U) * ((m : ℝ) + 1) := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hLupper
        (mul_nonneg (by norm_num) (Real.sqrt_nonneg 2))
    have hnum : 0 ≤ Real.sqrt (A.nu * (mu : ℝ)) := Real.sqrt_nonneg _
    have hdiv := div_le_div_of_nonneg_left hnum hden hdenU
    have hq0 : 0 ≤ q := hq.le
    calc
      c * 4 / ((m : ℝ) + 1) =
          (Real.sqrt (A.nu * (mu : ℝ)) /
            ((2 * Real.sqrt 2 * U) * ((m : ℝ) + 1))) * q := by
        dsimp only [c]
        field_simp
      _ ≤ (Real.sqrt (A.nu * (mu : ℝ)) /
            (2 * Real.sqrt 2 *
              localizedInteriorUpper A.nu (mu : ℝ)
                (L.roughBound 0 ((3 : ℝ) ^ m))
                (L.smoothDivBound 0 ((3 : ℝ) ^ m)))) * q :=
        mul_le_mul_of_nonneg_right hdiv hq0
      _ = _ := by ring
  have hgap : (3 : ℝ) ^ m / 4 ≤
      -(euclideanNorm (x - 0) + r₀ / 2) -
        (-cubeBoundaryCutoffInnerRadius m + 1) := by
    simp only [sub_zero]
    unfold cubeBoundaryCutoffInnerRadius
    linarith only [hm]
  have hexp : Real.exp (-((agmonRate A.nu
      (localizedInteriorUpper A.nu (mu : ℝ)
        (L.roughBound 0 ((3 : ℝ) ^ m))
        (L.smoothDivBound 0 ((3 : ℝ) ^ m))) (mu : ℝ) * q) *
      (-(euclideanNorm (x - 0) + r₀ / 2) -
        (-cubeBoundaryCutoffInnerRadius m + 1)))) ≤
      Real.exp (-(c * (3 : ℝ) ^ m / ((m : ℝ) + 1))) := by
    apply Real.exp_le_exp.2
    apply neg_le_neg
    have hgap0 : 0 ≤ (3 : ℝ) ^ m / 4 := by positivity
    have hrate0 : 0 ≤ agmonRate A.nu
        (localizedInteriorUpper A.nu (mu : ℝ)
          (L.roughBound 0 ((3 : ℝ) ^ m))
          (L.smoothDivBound 0 ((3 : ℝ) ^ m))) (mu : ℝ) * q :=
      mul_nonneg (agmonRate_nonneg hLpos) hq.le
    have hmul := mul_le_mul hrate hgap hgap0 hrate0
    calc
      c * (3 : ℝ) ^ m / ((m : ℝ) + 1) =
          (c * 4 / ((m : ℝ) + 1)) * ((3 : ℝ) ^ m / 4) := by ring
      _ ≤ _ := hmul
  calc
    _ ≤ P m * Real.exp (-((agmonRate A.nu
          (localizedInteriorUpper A.nu (mu : ℝ)
            (L.roughBound 0 ((3 : ℝ) ^ m))
            (L.smoothDivBound 0 ((3 : ℝ) ^ m))) (mu : ℝ) * q) *
        (-(euclideanNorm (x - 0) + r₀ / 2) -
          (-cubeBoundaryCutoffInnerRadius m + 1)))) := by
      convert hdecay using 1
      simp only [L, r₀, P, alpha, q, T.holder_eq]
      ring_nf
    _ ≤ (C * ((m : ℝ) + 1) * ((3 : ℝ) ^ (d + 1)) ^ m) *
          Real.exp (-(c * (3 : ℝ) ^ m / ((m : ℝ) + 1))) := by
      exact mul_le_mul (hPC m) hexp (Real.exp_pos _).le
        (mul_nonneg (mul_nonneg hC (by positivity)) (pow_nonneg (by norm_num) m))

/-- The analytic minimal resolvent of the stream coefficient has the exact
constant-one normalization. -/
theorem ofReal_mul_minimalResolvent_one_eq
    (T : LogGrowthBounds Sp)
    (mu : PositiveShift) (x : Vec d) :
    ENNReal.ofReal (mu : ℝ) *
        A.analyticMinimalResolvent mu
          (fun _ : Vec d ↦ (1 : ℝ)) measurable_const
          (D := 1) (fun _ ↦ by norm_num) x = 1 := by
  have ht := A.tendsto_analyticCubeResolvent mu
    (f := fun _ : Vec d ↦ (1 : ℝ)) measurable_const
    (fun _ ↦ by norm_num) (D := 1) (by norm_num) (fun _ ↦ by norm_num) x
  have htMul : Tendsto (fun m ↦ (mu : ℝ) *
      A.analyticCubeResolvent mu (fun _ : Vec d ↦ (1 : ℝ))
        measurable_const (D := 1) (fun _ ↦ by norm_num) m x) atTop
      (nhds ((mu : ℝ) *
        (A.analyticMinimalResolvent mu (fun _ : Vec d ↦ (1 : ℝ))
          measurable_const (D := 1) (fun _ ↦ by norm_num) x).toReal)) :=
    tendsto_const_nhds.mul ht
  have htSub : Tendsto (fun m ↦ 1 - (mu : ℝ) *
      A.analyticCubeResolvent mu (fun _ : Vec d ↦ (1 : ℝ))
        measurable_const (D := 1) (fun _ ↦ by norm_num) m x) atTop
      (nhds (1 - (mu : ℝ) *
        (A.analyticMinimalResolvent mu (fun _ : Vec d ↦ (1 : ℝ))
          measurable_const (D := 1) (fun _ ↦ by norm_num) x).toReal)) :=
    tendsto_const_nhds.sub htMul
  have htAbs := htSub.abs
  have hzero := tendsto_abs_analyticCubeBoundaryRemainder T mu x
  have habs : |1 - (mu : ℝ) *
      (A.analyticMinimalResolvent mu (fun _ : Vec d ↦ (1 : ℝ))
        measurable_const (D := 1) (fun _ ↦ by norm_num) x).toReal| = 0 :=
    tendsto_nhds_unique htAbs hzero
  have hreal : (mu : ℝ) *
      (A.analyticMinimalResolvent mu (fun _ : Vec d ↦ (1 : ℝ))
        measurable_const (D := 1) (fun _ ↦ by norm_num) x).toReal = 1 :=
    (sub_eq_zero.mp (abs_eq_zero.mp habs)).symm
  have hmin := A.analyticMinimalResolvent_ne_top mu
    (f := fun _ : Vec d ↦ (1 : ℝ)) measurable_const
    (fun _ ↦ by norm_num) (D := 1) (by norm_num) (fun _ ↦ by norm_num) x
  have hlhs : ENNReal.ofReal (mu : ℝ) *
      A.analyticMinimalResolvent mu (fun _ : Vec d ↦ (1 : ℝ))
        measurable_const (D := 1) (fun _ ↦ by norm_num) x ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hmin
  apply (ENNReal.toReal_eq_toReal_iff' hlhs ENNReal.one_ne_top).mp
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal mu.property.le,
    ENNReal.toReal_one]
  exact hreal

end LogGrowthBounds

/-! ## Satisfiability witnesses -/

/-- The constant-one normalization holds for the marginal analytic datum of every admissible
field. -/
example {nu : ℝ} {k : Vec d → Mat d} (D : FieldInputData d nu k) (mu : PositiveShift) (x : Vec d) :
    ENNReal.ofReal (mu : ℝ) *
      D.analyticData.analyticMinimalResolvent mu (fun _ : Vec d => (1 : ℝ))
        measurable_const (D := 1) (fun _ => by norm_num) x = 1 :=
  D.logGrowthBounds.ofReal_mul_minimalResolvent_one_eq mu x

end

end SuperdiffusionCLT.Section8

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section5.Principal.AverageMomentE

/-!
# `e.principal.Phat.moment`

From the identity `e.principal.Phat` and the eighth-moment display `e.principal.uz`:
`(avsum_z E|bfAhom^{1/2} P̂_z|⁴)^{1/4} ≤ 2 U²` when `(avsum_z E[|e_D|⁸ + |e_N|⁸ + |shom⁻¹ hbar|⁸])^{1/8} ≤ U`
and `U ≥ 1`. The product term `hbar e_D` is bounded by Young's inequality `x⁴y⁴ ≤ (x⁸ + y⁸)/2`, so no
Hölder inequality, hence no measurability, is needed.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section5

open Homogenization Homogenization.Book.Ch02 MeasureTheory
open SuperdiffusionCLT.Section2.Annealed (sigmaBarInfinite)
open scoped ENNReal

variable {d : ℕ}

/-- The real inequality: `(a² + (b + ca)²)² ≤ 8 (1 + a⁸ + b⁸ + c⁸)`. -/
theorem phat_len_sq_sq_le {a b c : ℝ} :
    (a ^ 2 + (b + c * a) ^ 2) ^ 2 ≤ 8 * (1 + (a ^ 8 + b ^ 8 + c ^ 8)) := by
  have s1 : (b + c * a) ^ 2 ≤ 2 * b ^ 2 + 2 * (c * a) ^ 2 := by
    nlinarith only [sq_nonneg (b - c * a)]
  set M : ℝ := a ^ 2 + (2 * b ^ 2 + 2 * (c * a) ^ 2) with hM
  have hL0 : 0 ≤ a ^ 2 + (b + c * a) ^ 2 := by positivity
  have hLM : a ^ 2 + (b + c * a) ^ 2 ≤ M := by rw [hM]; linarith only [s1]
  have hLM2 : (a ^ 2 + (b + c * a) ^ 2) ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ hL0 hLM 2
  have s2 : M ^ 2 ≤ 3 * (a ^ 4 + 4 * b ^ 4 + 4 * (c * a) ^ 4) := by
    rw [hM]
    nlinarith only [sq_nonneg (a ^ 2 - 2 * b ^ 2), sq_nonneg (a ^ 2 - 2 * (c * a) ^ 2),
      sq_nonneg (2 * b ^ 2 - 2 * (c * a) ^ 2)]
  have t1 : a ^ 4 ≤ (1 + a ^ 8) / 2 := by nlinarith only [sq_nonneg (a ^ 4 - 1)]
  have t2 : b ^ 4 ≤ (1 + b ^ 8) / 2 := by nlinarith only [sq_nonneg (b ^ 4 - 1)]
  have t3 : (c * a) ^ 4 ≤ (c ^ 8 + a ^ 8) / 2 := by
    rw [mul_pow]; nlinarith only [sq_nonneg (c ^ 4 - a ^ 4)]
  have ha8 : 0 ≤ a ^ 8 := by positivity
  have hb8 : 0 ≤ b ^ 8 := by positivity
  have hc8 : 0 ≤ c ^ 8 := by positivity
  linarith only [hLM2, s2, t1, t2, t3, ha8, hb8, hc8]

theorem matVecMul_smul_left_pm (c : ℝ) (g : Mat d) (x : Vec d) :
    matVecMul (c • g) x = c • matVecMul g x := by
  funext i
  simp only [matVecMul, Pi.smul_apply, smul_eq_mul, Matrix.smul_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

section MatNormF

open scoped Matrix.Norms.L2Operator

/-- `|bfAhom^{1/2} P̂|⁴ ≤ 8 (1 + a⁸ + b⁸ + c⁸)` with `a = |e_D|`, `b = |e_N|`, `c = |shom⁻¹ hbar|`. -/
theorem blockLenSq_sq_le (eD eN : Vec d) (g : Mat d) (σi : ℝ) :
    blockLenSq (eD, eN - σi • matVecMul g eD) ^ 2 ≤
      8 * (1 + (vecNorm eD ^ 8 + vecNorm eN ^ 8 + matrixOperatorNorm (σi • g) ^ 8)) := by
  have hw : σi • matVecMul g eD = matVecMul (σi • g) eD := (matVecMul_smul_left_pm σi g eD).symm
  have h1 : vecNorm (eN - σi • matVecMul g eD) ≤ vecNorm eN + matrixOperatorNorm (σi • g) * vecNorm eD := by
    refine (SuperdiffusionCLT.Section3.ResponseFields.vecNorm_sub_le_add _ _).trans ?_
    rw [hw]
    exact add_le_add le_rfl (vecNorm_matVecMul_le_matrixOperatorNorm_mul_vecNorm _ _)
  have h2 : blockLenSq (eD, eN - σi • matVecMul g eD) ≤
      vecNorm eD ^ 2 + (vecNorm eN + matrixOperatorNorm (σi • g) * vecNorm eD) ^ 2 := by
    unfold blockLenSq
    rw [← vecNorm_sq_eq_vecNormSq, ← vecNorm_sq_eq_vecNormSq]
    exact add_le_add le_rfl (pow_le_pow_left₀ (vecNorm_nonneg _) h1 2)
  have h0 : 0 ≤ blockLenSq (eD, eN - σi • matVecMul g eD) := by
    unfold blockLenSq
    rw [← vecNorm_sq_eq_vecNormSq, ← vecNorm_sq_eq_vecNormSq]
    positivity
  exact (pow_le_pow_left₀ h0 h2 2).trans phat_len_sq_sq_le

/-- **`e.principal.Phat.moment`**: from `e.principal.Phat` and the eighth-moment
display `e.principal.uz` (hypothesis `hUz`, printed shape, with `1 ≤ U`),
`(avsum_z E|bfAhom^{1/2} P̂_z|⁴)^{1/4} ≤ 2 U²`. -/
theorem principal_Phat_moment [NeZero d] {nu : ℝ}
    (P : MeasureTheory.ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
    (m h : ℕ) {Kc n : ℕ} (hn : n ≤ Kc) (hσ : 0 < sigmaBarInfinite nu (m - h) P) (e e' : Vec d)
    (gD gN : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → Vec d → Vec d) {U : ℝ}
    (hU1 : 1 ≤ U)
    (hUz : (subcubeAvg Kc n (fun Q => ∫⁻ omega, ENNReal.ofReal
        (vecNorm (principalED Q e' (gD omega)) ^ 8 + vecNorm (principalEN Q e (gN omega)) ^ 8 +
          matrixOperatorNorm ((sigmaBarInfinite nu (m - h) P)⁻¹ • principalGauge m h Q omega) ^ 8)
        ∂P.toMeasure)) ^ ((1 : ℝ) / 8) ≤ ENNReal.ofReal U) :
    (subcubeAvg Kc n (fun Q => ∫⁻ omega, ENNReal.ofReal
        (blockLenSq (ahomSqrtApply nu (m - h) P (principalPhat m h Q omega
          (blockSlope nu (m - h) P Q e e' (gD omega) (gN omega)))) ^ 2) ∂P.toMeasure)) ^
        ((1 : ℝ) / 4) ≤ ENNReal.ofReal (2 * U ^ 2) := by
  set S : ℝ≥0∞ := subcubeAvg Kc n (fun Q => ∫⁻ omega, ENNReal.ofReal
        (vecNorm (principalED Q e' (gD omega)) ^ 8 + vecNorm (principalEN Q e (gN omega)) ^ 8 +
          matrixOperatorNorm ((sigmaBarInfinite nu (m - h) P)⁻¹ • principalGauge m h Q omega) ^ 8)
        ∂P.toMeasure) with hS
  have hSle : S ≤ ENNReal.ofReal U ^ (8 : ℕ) := by
    have h8 := ENNReal.rpow_le_rpow hUz (show (0 : ℝ) ≤ 8 by norm_num)
    rw [← ENNReal.rpow_mul, show (1 : ℝ) / 8 * 8 = 1 by norm_num, ENNReal.rpow_one] at h8
    simpa using h8
  have hpt : ∀ (Q : TriadicCube d) omega, ENNReal.ofReal
      (blockLenSq (ahomSqrtApply nu (m - h) P (principalPhat m h Q omega
        (blockSlope nu (m - h) P Q e e' (gD omega) (gN omega)))) ^ 2) ≤
      8 * (1 + ENNReal.ofReal
        (vecNorm (principalED Q e' (gD omega)) ^ 8 + vecNorm (principalEN Q e (gN omega)) ^ 8 +
          matrixOperatorNorm ((sigmaBarInfinite nu (m - h) P)⁻¹ • principalGauge m h Q omega) ^ 8)) := by
    intro Q omega
    rw [ahomSqrtApply_principalPhat nu m h P hσ Q omega e e' (gD omega) (gN omega)]
    have := blockLenSq_sq_le (principalED Q e' (gD omega)) (principalEN Q e (gN omega))
      (principalGauge m h Q omega) (sigmaBarInfinite nu (m - h) P)⁻¹
    refine (ENNReal.ofReal_le_ofReal this).trans ?_
    rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_add (by norm_num) (by positivity),
      ENNReal.ofReal_one]
    norm_num
  have hinner : subcubeAvg Kc n (fun Q => ∫⁻ omega, ENNReal.ofReal
        (blockLenSq (ahomSqrtApply nu (m - h) P (principalPhat m h Q omega
          (blockSlope nu (m - h) P Q e e' (gD omega) (gN omega)))) ^ 2) ∂P.toMeasure) ≤
      8 * (1 + S) := by
    have h1 : subcubeAvg Kc n (fun Q => ∫⁻ omega, ENNReal.ofReal
        (blockLenSq (ahomSqrtApply nu (m - h) P (principalPhat m h Q omega
          (blockSlope nu (m - h) P Q e e' (gD omega) (gN omega)))) ^ 2) ∂P.toMeasure) ≤
        subcubeAvg Kc n (fun Q => 8 * (1 + ∫⁻ omega, ENNReal.ofReal
        (vecNorm (principalED Q e' (gD omega)) ^ 8 + vecNorm (principalEN Q e (gN omega)) ^ 8 +
          matrixOperatorNorm ((sigmaBarInfinite nu (m - h) P)⁻¹ • principalGauge m h Q omega) ^ 8)
        ∂P.toMeasure)) := by
      refine subcubeAvg_mono fun Q => ?_
      refine (lintegral_mono (hpt Q)).trans (le_of_eq ?_)
      rw [lintegral_const_mul' _ _ (by norm_num), lintegral_add_left measurable_const,
        lintegral_const, MeasureTheory.measure_univ, mul_one]
    refine h1.trans (le_of_eq ?_)
    rw [subcubeAvg_const_mul, subcubeAvg_add, subcubeAvg_const_pm hn]
  have hUge : (1 : ℝ≥0∞) ≤ ENNReal.ofReal U := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hU1
  have h16 : 8 * (1 + S) ≤ ENNReal.ofReal ((2 * U ^ 2) ^ 4) := by
    have hp : (1 : ℝ≥0∞) ≤ ENNReal.ofReal U ^ (8 : ℕ) := one_le_pow₀ hUge
    calc 8 * (1 + S) ≤ 8 * (ENNReal.ofReal U ^ (8 : ℕ) + ENNReal.ofReal U ^ (8 : ℕ)) :=
          mul_le_mul' le_rfl (add_le_add hp hSle)
      _ = ENNReal.ofReal ((2 * U ^ 2) ^ 4) := by
          have hU0 : 0 ≤ U := by linarith only [hU1]
          rw [← ENNReal.ofReal_pow hU0, ← ENNReal.ofReal_add (by positivity) (by positivity),
            ← ENNReal.ofReal_ofNat 8, ← ENNReal.ofReal_mul (by norm_num)]
          congr 1
          ring
  refine (ENNReal.rpow_le_rpow (hinner.trans h16) (by norm_num)).trans (le_of_eq ?_)
  rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num), ← Real.rpow_natCast,
    ← Real.rpow_mul (by positivity)]
  norm_num

end MatNormF

end SuperdiffusionCLT.Section5

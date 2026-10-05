/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section5.Coupled.Remainder
public import SuperdiffusionCLT.Section5.Response.Assembly
public import SuperdiffusionCLT.Section5.Principal.LocalizeSwitch
public import SuperdiffusionCLT.Section5.Neumann.NeumannInput

@[expose] public section

namespace SuperdiffusionCLT.Section5
open Homogenization Homogenization.Book.Ch02 MeasureTheory
open SuperdiffusionCLT.Section2.Annealed (sigmaBarInfinite)
variable {d : ℕ}

/-- `Ahom^{1/2} G_{-hbar_z} Ahom^{-1/2} (e_{D,z}, e)`. -/
noncomputable def coupledVec [NeZero d] (nu : ℝ)
    (P : MeasureTheory.ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
    (m h : ℕ) (Q : TriadicCube d) (omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d)
    (e : Vec d) (gD : Vec d → Vec d) : BlockVec d :=
  ahomSqrtApply nu (m - h) P
    (principalPhat m h Q omega (blockSlope nu (m - h) P Q e 0 gD (fun _ => 0)))

theorem coupled3_vec_eq [NeZero d] (nu : ℝ)
    (P : MeasureTheory.ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
    (m h : ℕ) (Q : TriadicCube d) (omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d)
    (hs : 0 < sigmaBarInfinite nu (m - h) P) (e : Vec d) (gD : Vec d → Vec d) :
    coupledVec nu P m h Q omega e gD =
      (coupledE Q gD, e - (sigmaBarInfinite nu (m - h) P)⁻¹ •
        matVecMul (principalGauge m h Q omega) (coupledE Q gD)) := by
  have h0 : volumeAverageVec (cubeSet Q) (fun _ : Vec d => (0 : Vec d)) = 0 := by
    funext i
    exact volumeAverage_zero (cubeSet Q)
  have hp : (sigmaBarInfinite nu (m - h) P) ^ ((1 : ℝ) / 2) *
      (sigmaBarInfinite nu (m - h) P) ^ (-(1 : ℝ) / 2) = 1 := by
    rw [← Real.rpow_add hs]; norm_num
  have hq : (sigmaBarInfinite nu (m - h) P) ^ (-(1 : ℝ) / 2) *
      (sigmaBarInfinite nu (m - h) P) ^ (-(1 : ℝ) / 2) = (sigmaBarInfinite nu (m - h) P)⁻¹ := by
    rw [← Real.rpow_add hs, ← Real.rpow_neg_one]; norm_num
  have hr : (sigmaBarInfinite nu (m - h) P) ^ (-(1 : ℝ) / 2) *
      (sigmaBarInfinite nu (m - h) P) ^ ((1 : ℝ) / 2) = 1 := by
    rw [mul_comm]; exact hp
  unfold coupledVec ahomSqrtApply principalPhat blockSlope
    SuperdiffusionCLT.Section5.ahomInvSqrtApply
  generalize (sigmaBarInfinite nu (m - h) P) ^ ((1 : ℝ) / 2) = a at hp hr ⊢
  generalize (sigmaBarInfinite nu (m - h) P) ^ (-(1 : ℝ) / 2) = b at hp hq hr ⊢
  refine Prod.ext ?_ ?_
  · funext i
    simp [h0, blockMatVecMul, gaugeMat, matVecMul, Matrix.one_apply, coupledE, ← mul_assoc, hp]
  · funext i
    simp [h0, blockMatVecMul, gaugeMat, matVecMul, Matrix.one_apply, coupledE,
      Finset.mul_sum, mul_add, ← mul_assoc, hr, sub_eq_add_neg]
    rw [add_comm]
    congr 2
    apply Finset.sum_congr rfl
    intro x _
    rw [← hq]
    ring

/-- Expansion of `|e - c v|^2`. -/
theorem coupled3_vecNormSq_sub_smul (c : ℝ) (e v : Vec d) :
    vecNormSq (e - c • v) = vecNormSq e + c ^ 2 * vecNormSq v - 2 * c * ∑ i, e i * v i := by
  have key : ∀ i, (e - c • v) i * (e - c • v) i =
      e i * e i + c ^ 2 * (v i * v i) - 2 * c * (e i * v i) := by
    intro i; simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
  unfold vecNormSq vecDot
  rw [Finset.sum_congr rfl (fun i _ => key i), Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum]

/-- `e.coupled.pointwise`: the identity `e.principal.Phat` at `e' = 0`, `|e| = 1`. -/
theorem coupled_pointwise [NeZero d] (nu : ℝ)
    (P : MeasureTheory.ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
    (m h : ℕ) (Q : TriadicCube d) (omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d)
    (hs : 0 < sigmaBarInfinite nu (m - h) P) (e : Vec d) (he : vecNormSq e = 1)
    (gD : Vec d → Vec d) :
    blockVecDot (coupledVec nu P m h Q omega e gD) (coupledVec nu P m h Q omega e gD) =
      1 + vecNormSq (coupledE Q gD) +
        (sigmaBarInfinite nu (m - h) P)⁻¹ ^ 2 *
          vecNormSq (matVecMul (principalGauge m h Q omega) (coupledE Q gD)) -
        2 * (sigmaBarInfinite nu (m - h) P)⁻¹ *
          (∑ i, e i * matVecMul (principalGauge m h Q omega) (coupledE Q gD) i) := by
  rw [coupled3_vec_eq nu P m h Q omega hs e gD]
  unfold blockVecDot
  have h1 := coupled3_vecNormSq_sub_smul (sigmaBarInfinite nu (m - h) P)⁻¹ e
    (matVecMul (principalGauge m h Q omega) (coupledE Q gD))
  change vecNormSq (coupledE Q gD) + vecNormSq _ = _
  rw [h1, he]
  ring

theorem coupled3_vecDot_le_vecNorm_mul (x y : Vec d) :
    |∑ i, x i * y i| ≤ vecNorm x * vecNorm y := by
  have h1 : (∑ i, x i * y i) ^ 2 ≤ (vecNorm x * vecNorm y) ^ 2 := by
    rw [mul_pow, vecNorm_sq_eq_vecNormSq, vecNorm_sq_eq_vecNormSq]
    exact sq_vecDot_le_vecNormSq_mul_vecNormSq x y
  exact abs_le_of_sq_le_sq h1 (mul_nonneg (vecNorm_nonneg x) (vecNorm_nonneg y))

theorem coupled3_gauge_apply_eq [NeZero d] (m h : ℕ) (Q : TriadicCube d)
    (omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d) (gD : Vec d → Vec d) :
    matVecMul (principalGauge m h Q omega) (coupledE Q gD) =
      coupledB m h Q omega gD - coupledR m h Q omega gD := by
  unfold coupledR
  abel

/-- `e.coupled.pointwise.split`. -/
theorem coupled_pointwise_split [NeZero d] (nu : ℝ)
    (P : MeasureTheory.ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
    (m h : ℕ) (Q : TriadicCube d) (omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d)
    (hs : 0 < sigmaBarInfinite nu (m - h) P) (e : Vec d) (he : vecNormSq e = 1)
    (gD : Vec d → Vec d) :
    blockVecDot (coupledVec nu P m h Q omega e gD) (coupledVec nu P m h Q omega e gD) ≤
      1 + vecNormSq (coupledE Q gD) +
        (sigmaBarInfinite nu (m - h) P)⁻¹ ^ 2 * vecNormSq (coupledB m h Q omega gD) -
        2 * (sigmaBarInfinite nu (m - h) P)⁻¹ * (∑ i, e i * coupledB m h Q omega gD i) +
        (sigmaBarInfinite nu (m - h) P)⁻¹ ^ 2 * vecNormSq (coupledR m h Q omega gD) +
        2 * (sigmaBarInfinite nu (m - h) P)⁻¹ ^ 2 *
          (vecNorm (coupledB m h Q omega gD) * vecNorm (coupledR m h Q omega gD)) +
        2 * (sigmaBarInfinite nu (m - h) P)⁻¹ * vecNorm (coupledR m h Q omega gD) := by
  rw [coupled_pointwise nu P m h Q omega hs e he gD, coupled3_gauge_apply_eq]
  set c := (sigmaBarInfinite nu (m - h) P)⁻¹ with hc
  set B := coupledB m h Q omega gD
  set R := coupledR m h Q omega gD
  have hc0 : 0 ≤ c := inv_nonneg.mpr hs.le
  have h1 := coupled3_vecNormSq_sub_smul 1 B R
  rw [one_smul] at h1
  have h2 : ∑ i, e i * (B - R) i = ∑ i, e i * B i - ∑ i, e i * R i := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun i _ => by simp only [Pi.sub_apply]; ring)
  have h3 : ∑ i, e i * R i ≤ vecNorm R := by
    have := coupled3_vecDot_le_vecNorm_mul e R
    have hn : vecNorm e = 1 :=
      (sq_eq_sq₀ (vecNorm_nonneg e) zero_le_one).1 (by rw [vecNorm_sq_eq_vecNormSq, he]; simp)
    rw [hn, one_mul] at this
    exact le_trans (le_abs_self _) this
  have h4 : -(vecNorm B * vecNorm R) ≤ ∑ i, B i * R i :=
    (abs_le.1 (coupled3_vecDot_le_vecNorm_mul B R)).1
  rw [h1, h2]
  have hc2 : 0 ≤ c ^ 2 := sq_nonneg c
  linarith only [mul_le_mul_of_nonneg_left h3 hc0, mul_le_mul_of_nonneg_left h4 hc2]

end SuperdiffusionCLT.Section5

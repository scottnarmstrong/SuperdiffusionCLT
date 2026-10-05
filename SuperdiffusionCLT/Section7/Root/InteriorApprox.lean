/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.CZ.GlobalC
public import SuperdiffusionCLT.Section7.Analytic.Morrey.ZeroTraceB
public import SuperdiffusionCLT.Section7.Analytic.DeGiorgi.IterationE
public import SuperdiffusionCLT.Section7.Prereq.LinftyReductionC

/-!
# Interior approximation: the Calderon-Zygmund and Morrey step on a uniform domain

For a uniformly `C^{1,1}` domain `U` inside an axis cube of side `L` the zero-trace solution `φ`
of `Δφ = h + ∇·F` satisfies `‖φ‖_{L^∞(U)} ≤ C L (‖F‖_{L̲^{2d}(U)} + ‖h‖_{W̲^{-1,2d}(U)})`
(CZ at `p = 2d`, then Morrey): the step used in `e.Dir.new.interior.Linfty.f.moll` and
`e.Dir.new.interior.Linfty.ueta.bar`.
-/

@[expose] public section

open Homogenization MeasureTheory
open scoped ENNReal

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

/-- Normalized norm against the plain norm. -/
theorem ia_lpBar_eq_mul {U : Set (Vec d)} {E : Type*} [NormedAddCommGroup E] {p : ℝ≥0∞}
    (hp0 : p ≠ 0) (hpt : p ≠ ⊤) (hUt : volume U ≠ ⊤) (G : Vec d → E)
    (hG : AEStronglyMeasurable G (volume.restrict U)) :
    eLpNorm G p (volume.restrict U) = (volume U) ^ (1 / p.toReal) * lpBar U p G := by
  unfold lpBar
  rw [eLpNorm_smul_measure_of_ne_top hpt G ((volume U)⁻¹) hG, smul_eq_mul]
  have hP : 0 < p.toReal := ENNReal.toReal_pos hp0 hpt
  have he : ((1 : ℝ≥0∞) / p).toReal = 1 / p.toReal := by
    rw [one_div, ENNReal.toReal_inv, one_div]
  rw [he]
  by_cases hU0 : volume U = 0
  · rw [Measure.restrict_eq_zero.2 hU0, eLpNorm_measure_zero]; simp
  rw [← mul_assoc, ← ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ENNReal.mul_inv_cancel hU0 hUt,
    ENNReal.one_rpow, one_mul]

/-- The volume of a subset of an axis cube. -/
theorem ia_volume_le_axisCube {U : Set (Vec d)} {z : Vec d} {L : ℝ} (hL : 0 < L)
    (hU : U ⊆ axisCube z L) : volume U ≤ ENNReal.ofReal (L ^ d) := by
  have hvol : volume (axisCube z L) = ENNReal.ofReal (L ^ d) := by
    rw [axisCube, Real.volume_pi_Ioo]
    simp only [add_sub_cancel_left, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [ENNReal.ofReal_pow hL.le]
  exact hvol ▸ measure_mono hU

/-- **CZ at `p = 2d` followed by Morrey.** -/
theorem ia_linfty_cz_morrey (hd : 2 ≤ d) (M₁ κ ρ : ℝ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {U : Set (Vec d)} {r M₂ D : ℝ} {z : Vec d} {L : ℝ}, IsUniformC11Domain U r M₁ M₂ D →
        r * M₂ ≤ κ → D ≤ ρ * r → 0 < L → U ⊆ axisCube z L →
        ∀ (F : Vec d → Vec d) (h : Vec d → ℝ) (φ : H10Function U), MemVectorL2 U F →
          MemScalarL2 U h → IsWeakSolutionOn (fun _ => 1) U φ.toH1Function h F →
          eLpNorm φ.toFun ⊤ (volume.restrict U) ≤
            ENNReal.ofReal (C * L) *
              (lpBar U (ENNReal.ofReal (2 * d)) F + wMinusOneBar U (ENNReal.ofReal (2 * d)) h) := by
  have hd0 : 0 < d := by omega
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hp1 : (1 : ℝ≥0∞) < ENNReal.ofReal (2 * d) := by
    rw [← ENNReal.ofReal_one]
    exact (ENNReal.ofReal_lt_ofReal_iff (by linarith only [hdR])).2 (by linarith only [hdR])
  obtain ⟨Cz, hCz, Hz⟩ := cz_unif hd (ENNReal.ofReal (2 * d)) hp1 ENNReal.ofReal_lt_top M₁ κ ρ
  refine ⟨8 * d * Cz, by positivity, ?_⟩
  intro U r M₂ D z L hU hκ hρ hL hUL F h φ hF hh hφ
  have hUb := p14g_isBoundedDomain hU
  have hUt : volume U ≠ ⊤ := (hUb.isBounded.measure_lt_top).ne
  have hcz := Hz hU hκ hρ F h φ hF hh hφ
  have hmor := h10_essSup_le_morrey hd0 hU.1 hUL φ (p := 2 * d) (by linarith only [hdR])
  have hdp : 1 - (d : ℝ) / (2 * d) = 1 / 2 := by field_simp; ring
  rw [hdp] at hmor
  have hgm := li1_grad_aesm φ
  have hpt : (ENNReal.ofReal (2 * d)).toReal = 2 * d := ENNReal.toReal_ofReal (by positivity)
  have hnorm : eLpNorm (fun x => ‖φ.toH1Function.grad x‖) (ENNReal.ofReal (2 * d))
      (volume.restrict U) = eLpNorm φ.toH1Function.grad (ENNReal.ofReal (2 * d))
        (volume.restrict U) := eLpNorm_norm _ hgm
  have hE := ia_lpBar_eq_mul (U := U) (p := ENNReal.ofReal (2 * d))
    (ENNReal.ofReal_pos.2 (by positivity)).ne' ENNReal.ofReal_ne_top hUt φ.toH1Function.grad hgm
  have hvol : volume U ^ (1 / (ENNReal.ofReal (2 * d)).toReal) ≤ ENNReal.ofReal (L ^ (1 / 2 : ℝ)) := by
    rw [hpt]
    have := ENNReal.rpow_le_rpow (ia_volume_le_axisCube hL hUL) (z := 1 / (2 * d))
      (by positivity)
    refine this.trans_eq ?_
    rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity), ← Real.rpow_natCast,
      ← Real.rpow_mul hL.le]
    congr 2
    field_simp
  have hmul : ENNReal.ofReal (4 * (d : ℝ) * (1 / (1 / 2)) * L ^ (1 / 2 : ℝ)) *
      ENNReal.ofReal (L ^ (1 / 2 : ℝ)) = ENNReal.ofReal (8 * d * L) := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    have : L ^ (1 / 2 : ℝ) * L ^ (1 / 2 : ℝ) = L := by
      rw [← Real.rpow_add hL]; norm_num
    calc 4 * (d : ℝ) * (1 / (1 / 2)) * L ^ (1 / 2 : ℝ) * L ^ (1 / 2 : ℝ)
        = 8 * d * (L ^ (1 / 2 : ℝ) * L ^ (1 / 2 : ℝ)) := by ring
      _ = 8 * d * L := by rw [this]
  calc eLpNorm φ.toFun ⊤ (volume.restrict U)
      ≤ ENNReal.ofReal (4 * (d : ℝ) * (1 / (1 / 2)) * L ^ (1 / 2 : ℝ)) *
        eLpNorm (fun x => ‖φ.toH1Function.grad x‖) (ENNReal.ofReal (2 * d))
          (volume.restrict U) := hmor
    _ = ENNReal.ofReal (4 * (d : ℝ) * (1 / (1 / 2)) * L ^ (1 / 2 : ℝ)) *
        (volume U ^ (1 / (ENNReal.ofReal (2 * d)).toReal) *
          lpBar U (ENNReal.ofReal (2 * d)) φ.toH1Function.grad) := by rw [hnorm, hE]
    _ ≤ ENNReal.ofReal (4 * (d : ℝ) * (1 / (1 / 2)) * L ^ (1 / 2 : ℝ)) *
        (ENNReal.ofReal (L ^ (1 / 2 : ℝ)) *
          lpBar U (ENNReal.ofReal (2 * d)) φ.toH1Function.grad) := by gcongr
    _ = ENNReal.ofReal (8 * d * L) *
          lpBar U (ENNReal.ofReal (2 * d)) φ.toH1Function.grad := by rw [← mul_assoc, hmul]
    _ ≤ ENNReal.ofReal (8 * d * L) *
          (ENNReal.ofReal Cz * (lpBar U (ENNReal.ofReal (2 * d)) F +
            wMinusOneBar U (ENNReal.ofReal (2 * d)) h)) := by gcongr
    _ = ENNReal.ofReal (8 * d * Cz * L) *
          (lpBar U (ENNReal.ofReal (2 * d)) F + wMinusOneBar U (ENNReal.ofReal (2 * d)) h) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
        congr 2
        ring

/-- The Euclidean unit ball lies in an axis cube. -/
theorem ia_euclidBall_subset_axisCube :
    Section6.euclidBall (d := d) 1 ⊆ axisCube (fun _ => (-1 : ℝ)) 2 := by
  intro x hx j _
  have hx' : vecNormSq x < 1 ^ 2 := hx
  have hj : x j ^ 2 ≤ vecNormSq x := by
    unfold vecNormSq vecDot
    simp only [← sq]
    exact Finset.single_le_sum (f := fun i => x i ^ 2) (fun i _ => sq_nonneg _) (Finset.mem_univ j)
  have h1 : |x j| < 1 := by
    have : x j ^ 2 < 1 := by linarith only [hj, hx']
    exact abs_lt_of_sq_lt_sq (by simpa using this) (by norm_num)
  rw [abs_lt] at h1
  simp only [Set.mem_Ioo]
  constructor <;> linarith only [h1.1, h1.2]

end SuperdiffusionCLT.Section7

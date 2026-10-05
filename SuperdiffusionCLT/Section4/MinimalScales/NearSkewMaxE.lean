/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section4.MinimalScales.NearSkewMaxD
public import SuperdiffusionCLT.Section4.MinimalScales.DeepCrudePolyB
public import SuperdiffusionCLT.Probability.GammaSigmaHelpers
public import SuperdiffusionCLT.Probability.OrliczPower

/-!
# The maximal skew-average bound

`srootNS_skewMax`: uniformly in the cutoff `q ≤ m + ⌈K log m⌉`, the squared operator
norm of the coarse average `(k_q)_{cu_m}` is at most
`A K log m · log (2 ⌈K log m⌉)` plus a nonnegative variable that is
`O_{Γ₁}(A s⁻¹ K log m)`.

The factor `log (2 ⌈K log m⌉)` is the cost of the centered maximum over the window
(`gammaSigma_centered_Icc`); it is kept in raw form. The bound is pointwise in `ω`,
and does not use the lower end of the window.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section4.MinimalScales

open MeasureTheory ProbabilityTheory
open Homogenization Homogenization.IndependentSums Homogenization.Book.Ch02
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section2.Cutoff (ShellSeq)
open SuperdiffusionCLT.Section2.Estimates.Stream
  (spatialAverageColorConst spatialAverageColorConst_nonneg)

noncomputable section

/-- The window scale is at least `3`: from the `lNaught` threshold. -/
theorem srootNS_three_le_of_lNaught {C1 M cStar nondeg nu : ℝ} (hC1 : 1 ≤ C1) (hM : 0 ≤ M)
    (hK : 0 ≤ nondeg) (hc : 0 < cStar) (hc2 : cStar ≤ 2) (hnu : 0 < nu) (hnu1 : nu ≤ 1)
    {m : ℕ}
    (hm : SuperdiffusionCLT.Frozen.Section4.lNaught C1 M (1 / 2) cStar nu nondeg ≤
      (m : ℝ)) : (3 : ℝ) ≤ m := by
  have h1 := srootD4_lNaught_ge_nu_inv hC1 hM hK hc hc2 hnu hnu1
  have hnuinv : (1 : ℝ) ≤ nu⁻¹ := one_le_inv₀ hnu |>.2 hnu1
  have hn4 : (1 : ℝ) ≤ (nu⁻¹) ^ 4 := one_le_pow₀ hnuinv
  have hl2 : (0.69 : ℝ) < Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith only [this]
  have hp : (0.69 : ℝ) ^ 12 ≤ Real.log 2 ^ 12 :=
    pow_le_pow_left₀ (by norm_num) hl2.le 12
  have hp2 : (5 : ℝ) ≤ 512 * Real.log 2 ^ 12 := by
    have : (0.01 : ℝ) ≤ (0.69 : ℝ) ^ 12 := by norm_num
    linarith only [hp, this]
  have h3 : (25 : ℝ) ≤ (512 * Real.log 2 ^ 12) ^ 2 := by nlinarith only [hp2]
  have h4 : (25 : ℝ) ≤ (512 * Real.log 2 ^ 12) ^ 2 * (nu⁻¹) ^ 4 := by
    nlinarith only [h3, hn4]
  linarith only [h1, h4, hm]

/-- The squares: `(x ^ (1/2)) ^ 2 = x` for `x ≥ 0`. -/
theorem srootNS_rpow_half_sq {x : ℝ} (hx : 0 ≤ x) : (x ^ ((2 : ℝ)⁻¹)) ^ 2 = x := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
  norm_num

/-- Squaring a nonnegative `Γ₂` variable gives a `Γ₁` variable. -/
theorem srootNS_sq_isBigO {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {U : Ω → ℝ} {a : ℝ} (ha : 0 ≤ a) (hU0 : ∀ ω, 0 ≤ U ω)
    (hU : IsBigO μ (gammaSigma 2) U a) :
    IsBigO μ (gammaSigma 1) (fun ω => 2 * U ω ^ 2) (2 * a ^ 2) := by
  have h := SuperdiffusionCLT.Probability.isBigO_gammaSigma_rpow_fwd (p := 2)
    (by norm_num) ha hU0 hU
  rw [show (2 : ℝ) / 2 = 1 by norm_num] at h
  simp only [Real.rpow_two] at h
  exact h.const_mul (by norm_num)

theorem srootNS_skewMax (d : ℕ) [NeZero d] :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ C1 : ℝ, A ≤ C1 → ∀ nu cStar nondeg : ℝ, 0 < nu → nu ≤ 1 →
      ∀ (P : ProbabilityMeasure (ShellSeq d)) (hPrefix : ShellLawPrefix d P)
        (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P),
        ShellLawJ1 d P → ShellLawJ4 d P →
        ShellLawJ5 d P cStar nondeg hPrefix hJ2 hJ3 →
        ∀ s : ℝ, 0 < s → s ≤ 1 → ∀ K : ℝ, C1 ≤ K → ∀ m : ℕ,
          SuperdiffusionCLT.Frozen.Section4.lNaught C1 (C1 * s⁻¹ * K) (1 / 2) cStar nu
              nondeg ≤ (m : ℝ) →
          ∃ W : ShellSeq d → ℝ, Measurable W ∧ (∀ ω, 0 ≤ W ω) ∧
            IsBigO P.toMeasure (gammaSigma 1) W (A * (s⁻¹ * K * Real.log (m : ℝ))) ∧
            ∀ ω, ∀ q : ℕ, q ≤ m + ⌈K * Real.log (m : ℝ)⌉₊ →
              matrixOperatorNorm (volumeAverageMat (cubeSet (originCube d (m : ℤ)))
                  (SuperdiffusionCLT.Frozen.Section2.streamCutoff ω q)) ^ 2 ≤
                A * (K * Real.log (m : ℝ) *
                  Real.log (2 * ((⌈K * Real.log (m : ℝ)⌉₊ : ℕ) : ℝ))) + W ω := by
  set g2 : ℝ := gammaTriangleConst 2 with hg2
  set n : ℝ := ((d * d : ℕ) : ℝ) with hn
  set c : ℝ := 1 + spatialAverageColorConst d with hc
  set C0 : ℝ := Book.Ch04.gammaSigmaIndependentSumConst 2 with hC0
  set aH : ℝ := g2 * (n * (g2 * (4 * c))) with haH
  set E1 : ℝ := g2 * (aH + g2 * n) with hE1
  set E2 : ℝ := g2 * g2 * n * |C0| * c with hE2
  have hAnn : 0 ≤ 4 * E1 ^ 2 + 8 * E2 ^ 2 := by positivity
  have hBnn : 0 ≤ 4 * n ^ 2 * |C0| ^ 2 * c ^ 2 := by positivity
  refine ⟨1 + (4 * E1 ^ 2 + 8 * E2 ^ 2) + 4 * n ^ 2 * |C0| ^ 2 * c ^ 2, ?_, ?_⟩
  · linarith only [hAnn, hBnn]
  intro C1 hC1 nu cStar nondeg hnu hnu1 P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5 s hs0 hs1 K hK m hm
  set A : ℝ := 1 + (4 * E1 ^ 2 + 8 * E2 ^ 2) + 4 * n ^ 2 * |C0| ^ 2 * c ^ 2 with hA
  have hA1 : (1 : ℝ) ≤ A := by
    linarith only [hAnn, hBnn]
  have hC11 : 1 ≤ C1 := le_trans hA1 hC1
  have hK1 : 1 ≤ K := le_trans hC11 hK
  have hm3 : (3 : ℝ) ≤ m := by
    refine srootNS_three_le_of_lNaught hC11 ?_ hJ5.K_pos.le hJ5.cStar_pos hJ5.cStar_le_two
      hnu hnu1 hm
    have : 0 ≤ K := by linarith only [hK1]
    positivity
  have hlog1 : 1 ≤ Real.log (m : ℝ) := by
    rw [Real.le_log_iff_exp_le (by linarith only [hm3])]
    have := Real.exp_one_lt_d9
    linarith only [this, hm3]
  set x : ℝ := K * Real.log (m : ℝ) with hx
  have hx1 : 1 ≤ x := one_le_mul_of_one_le_of_one_le hK1 hlog1
  set h : ℕ := ⌈x⌉₊ with hh
  have hh1 : 1 ≤ h := Nat.one_le_iff_ne_zero.2 (Nat.pos_iff_ne_zero.1
    (Nat.ceil_pos.2 (by linarith only [hx1])))
  have hhx : (h : ℝ) ≤ 2 * x := by
    have := Nat.ceil_lt_add_one (show 0 ≤ x by linarith only [hx1])
    linarith only [this, hx1]
  have hh1r : (1 : ℝ) ≤ h := by exact_mod_cast hh1
  obtain ⟨hC0nn, Hs, Ys, hHm, hYm, hH0, hY0, hHO, hYO, hpt⟩ :=
    srootNS_core hPrefix hJ1 hJ2 hJ3 hJ4 m h hh1
  have habs : |C0| = C0 := abs_of_nonneg hC0nn
  have hd0 : 0 < d := lt_of_lt_of_le (by norm_num) hPrefix.dimension
  have hcol : 0 ≤ spatialAverageColorConst d := spatialAverageColorConst_nonneg d
  have hcpos : 0 < c := by rw [hc]; linarith only [hcol]
  have hg2pos : 0 < g2 := IndependentSums.gammaTriangleConst_pos
  have hnpos : 0 < n := by rw [hn]; exact_mod_cast Nat.mul_pos hd0 hd0
  have haHpos : 0 < aH := by
    rw [haH]
    exact mul_pos hg2pos (mul_pos hnpos (mul_pos hg2pos (mul_pos (by norm_num) hcpos)))
  set Kc : ℝ := C0 * Real.sqrt (h : ℝ) * c with hKc
  have hKc0 : 0 ≤ Kc := mul_nonneg (mul_nonneg hC0nn (Real.sqrt_nonneg _)) hcpos.le
  set aY : ℝ := g2 * (n * (Kc + 1)) with haY
  have haYpos : 0 < aY := mul_pos hg2pos (mul_pos hnpos (by linarith only [hKc0]))
  have hU : IsBigO P.toMeasure (gammaSigma 2) (fun ω => Hs ω + Ys ω) (g2 * (aH + aY)) :=
    SuperdiffusionCLT.Probability.isBigO_gammaSigma_add_of_isBigO (by norm_num) haHpos
      haYpos hHO hYO hHm hYm
  have haU0 : 0 ≤ g2 * (aH + aY) := mul_nonneg hg2pos.le (add_nonneg haHpos.le haYpos.le)
  have hW := srootNS_sq_isBigO haU0 (fun ω => add_nonneg (hH0 ω) (hY0 ω)) hU
  refine ⟨fun ω => 2 * (Hs ω + Ys ω) ^ 2, ?_, ?_, ?_, ?_⟩
  · exact measurable_const.mul ((hHm.add hYm).pow_const 2)
  · intro ω
    exact mul_nonneg (by norm_num) (sq_nonneg _)
  · refine hW.mono_scale ?_
    have hsq : Real.sqrt (h : ℝ) ^ 2 = h := Real.sq_sqrt (Nat.cast_nonneg _)
    have hsqrt0 : 0 ≤ Real.sqrt (h : ℝ) := Real.sqrt_nonneg _
    have haU : g2 * (aH + aY) = E1 + E2 * Real.sqrt (h : ℝ) := by
      rw [haY, hKc, hE1, hE2, habs]
      ring
    have hE10 : 0 ≤ E1 := by
      rw [hE1]
      exact mul_nonneg hg2pos.le (add_nonneg haHpos.le (mul_nonneg hg2pos.le hnpos.le))
    have hE20 : 0 ≤ E2 := by
      rw [hE2]
      exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hg2pos.le hg2pos.le) hnpos.le) (abs_nonneg _)) hcpos.le
    have h1 : (E1 + E2 * Real.sqrt (h : ℝ)) ^ 2 ≤ 2 * E1 ^ 2 + 2 * (E2 ^ 2 * h) := by
      have : (E2 * Real.sqrt (h : ℝ)) ^ 2 = E2 ^ 2 * h := by rw [mul_pow, hsq]
      linarith only [sq_nonneg (E1 - E2 * Real.sqrt (h : ℝ)), this]
    have h2 : 2 * E1 ^ 2 + 2 * (E2 ^ 2 * h) ≤ (2 * E1 ^ 2 + 4 * E2 ^ 2) * x := by
      have e1 : E1 ^ 2 ≤ E1 ^ 2 * x := by
        have := mul_le_mul_of_nonneg_left hx1 (sq_nonneg E1)
        linarith only [this]
      have e2 : E2 ^ 2 * h ≤ E2 ^ 2 * (2 * x) :=
        mul_le_mul_of_nonneg_left hhx (sq_nonneg E2)
      linarith only [e1, e2]
    have h3 : 2 * (g2 * (aH + aY)) ^ 2 ≤ A * x := by
      rw [haU]
      have hxpos : 0 ≤ x := by linarith only [hx1]
      have hAx : (4 * E1 ^ 2 + 8 * E2 ^ 2) * x ≤ A * x :=
        mul_le_mul_of_nonneg_right (by rw [hA]; linarith only [sq_nonneg (n * |C0| * c)])
          hxpos
      linarith only [h1, h2, hAx]
    have hsinv : 1 ≤ s⁻¹ := one_le_inv₀ hs0 |>.2 hs1
    have hA0 : 0 ≤ A := by linarith only [hA1]
    calc 2 * (g2 * (aH + aY)) ^ 2 ≤ A * x := h3
      _ ≤ A * (s⁻¹ * x) := mul_le_mul_of_nonneg_left (by
        have := mul_le_mul_of_nonneg_right hsinv (by linarith only [hx1] : (0 : ℝ) ≤ x)
        linarith only [this]) hA0
      _ = A * (s⁻¹ * K * Real.log (m : ℝ)) := by rw [hx]; ring
  · intro ω q hq
    have hq' : q ≤ m + h := hq
    have h1 := hpt ω q hq'
    set L : ℝ := Real.log (2 * (h : ℝ)) ^ ((2 : ℝ)⁻¹) with hL
    have hlog0 : 0 ≤ Real.log (2 * (h : ℝ)) :=
      Real.log_nonneg (by linarith only [hh1r])
    have hL2 : L ^ 2 = Real.log (2 * (h : ℝ)) := srootNS_rpow_half_sq hlog0
    set U : ℝ := Hs ω + Ys ω with hUdef
    have hU0 : 0 ≤ U := add_nonneg (hH0 ω) (hY0 ω)
    set D : ℝ := n * (Kc * L) with hD
    have hnorm := pow_le_pow_left₀ (matrixOperatorNorm_nonneg _) h1 2
    have h2 : (U + D) ^ 2 ≤ 2 * U ^ 2 + 2 * D ^ 2 := by linarith only [sq_nonneg (U - D)]
    have hD2 : D ^ 2 = n ^ 2 * (C0 ^ 2 * c ^ 2) * (h * Real.log (2 * (h : ℝ))) := by
      have hsq : Real.sqrt (h : ℝ) ^ 2 = h := Real.sq_sqrt (Nat.cast_nonneg _)
      have hexp : D ^ 2 = n ^ 2 * (C0 ^ 2 * c ^ 2) * (Real.sqrt (h : ℝ) ^ 2 * L ^ 2) := by
        rw [hD, hKc]
        ring
      rw [hexp, hsq, hL2]
    have h3 : 2 * D ^ 2 ≤ A * (x * Real.log (2 * (h : ℝ))) := by
      rw [hD2]
      have hhl : h * Real.log (2 * (h : ℝ)) ≤ (2 * x) * Real.log (2 * (h : ℝ)) :=
        mul_le_mul_of_nonneg_right hhx hlog0
      have hc2 : 0 ≤ n ^ 2 * (C0 ^ 2 * c ^ 2) :=
        mul_nonneg (sq_nonneg n) (mul_nonneg (sq_nonneg C0) (sq_nonneg c))
      have e1 := mul_le_mul_of_nonneg_left hhl hc2
      have hxl : 0 ≤ x * Real.log (2 * (h : ℝ)) := by
        have : 0 ≤ x := by linarith only [hx1]
        exact mul_nonneg this hlog0
      have hAc : 4 * (n ^ 2 * (C0 ^ 2 * c ^ 2)) ≤ A := by
        have hA' : A = 1 + (4 * E1 ^ 2 + 8 * E2 ^ 2) + 4 * n ^ 2 * C0 ^ 2 * c ^ 2 := by
          rw [hA, sq_abs]
        have h1' := hAnn
        linarith only [h1', hA']
      have e2 := mul_le_mul_of_nonneg_right hAc hxl
      linarith only [e1, e2]
    show matrixOperatorNorm _ ^ 2 ≤ A * (x * Real.log (2 * (h : ℝ))) + 2 * (Hs ω + Ys ω) ^ 2
    linarith only [hnorm, h2, h3]

/-- Satisfiability of the non-law hypotheses (the threshold on `m`, the constants
`nu = s = 1`, `K = C1`): for every `C1`, `cStar`, `nondeg` there is an admissible `m`. -/
example (C1 cStar nondeg : ℝ) :
    ∃ m : ℕ, SuperdiffusionCLT.Frozen.Section4.lNaught C1 (C1 * (1 : ℝ)⁻¹ * C1) (1 / 2)
      cStar 1 nondeg ≤ (m : ℝ) :=
  ⟨⌈SuperdiffusionCLT.Frozen.Section4.lNaught C1 (C1 * (1 : ℝ)⁻¹ * C1) (1 / 2)
      cStar 1 nondeg⌉₊, Nat.le_ceil _⟩

end

end SuperdiffusionCLT.Section4.MinimalScales

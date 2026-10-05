/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section4.HomogBelow.ThetaLmM3Headroom
public import SuperdiffusionCLT.Section4.HomogBelow.ThetaLmOmegaSeq
public import SuperdiffusionCLT.Section4.HomogBelow.RatsToInfty

/-!
The "sharp" `omegaSeq(m̃')²` bound, the display
`\omega_{\tilde m'}^2 \leq C(L-\tilde m')_+ \shom_L^{-2} +
\tilde m'^{-6000}` in the proof of `p.homog.below`.

The naive route squares `ω_h = K₃(T₁+T₂+T₃)` via the same "3 thirds" split
used for the coarse smallness bound (`ThetaLmFinalSmallness.lean`) and gets
a `T₂²` term quadratic in `(L-h)_+`, which cannot be absorbed into an
`M`-independent prefactor. The fix: once `S(h) ≥ σ∞/2` (`e.rats.to.infty` at the
output scale of the FIRST application of [AK, Theorem 6.1], combined with monotonicity of
`S`) AND `(L-h)_+ ≤ σ∞²/Cmix` (the SAME `m₃`-headroom fact used to bound
`(L-h)_+` also controls `σ∞` from below via `e.L.vs.Lnaught`, so both facts
trace back to the one inequality `homogBelow_headroom_sq_le` packages), one
power of `(L-h)_+` inside `T₂²` can be traded for a `σ∞²` factor, turning the
quadratic bound linear. The exact constant obtained here (`Cmix⁻¹` on the
headroom side, giving prefactors `4Cmix²+16Cmix` and `9Cmix²`) is simpler
than a `Kappa3/c`-based estimate but proves the identical
qualitative fact; the caller instantiates `h := m̃'` once the two applications of
[AK, Theorem 6.1] and `e.rats.to.infty` are wired up. -/

@[expose] public section

namespace SuperdiffusionCLT.Section4.HomogBelow

open Homogenization MeasureTheory

/-- **The headroom-controls-`σ∞`-from-below bridge**: given the `S(L)²`
lower bound at `(c, Mthr, Lr)` (`homogBelow_m3_headroom`'s `hFact2` at
`h := L`), `S(L) ≤ σ∞` (unconditional,
`homogBelow_sigmaBarStarScalar_le_sigmaBarInfinite`), and the `m₃`-headroom
upper bound on `(L-m₃)` (`hm3ge`), every `h` with `m₃ ≤ h ≤ L` satisfies
`(L-h) ≤ σ∞²/Cmix`. Stated at the pure-algebra level (no measure-theoretic
carrier) so it is reusable regardless of which `h` (`m̃` or `m̃'`) the caller
plugs in. -/
theorem homogBelow_headroom_sq_le
    {c Cmix Mthr Lr SL sInf L m3 h : ℝ}
    (hCmixpos : 0 < Cmix)
    (hFact2L : c * (Cmix * Mthr) * Lr ≤ SL ^ (2 : ℝ))
    (hSLle : SL ≤ sInf)
    (hm3ge : L - m3 ≤ c * Mthr * Lr)
    (hSLnonneg : 0 ≤ SL)
    (hm3h : m3 ≤ h) :
    L - h ≤ sInf ^ (2 : ℝ) / Cmix := by
  have hSL2 : SL ^ (2 : ℝ) ≤ sInf ^ (2 : ℝ) :=
    Real.rpow_le_rpow hSLnonneg hSLle (by norm_num)
  have hstep1 : c * (Cmix * Mthr) * Lr ≤ sInf ^ (2 : ℝ) := le_trans hFact2L hSL2
  have hcMthrLr_le : c * Mthr * Lr ≤ sInf ^ (2 : ℝ) / Cmix := by
    rw [le_div_iff₀ hCmixpos]
    have heq : c * Mthr * Lr * Cmix = c * (Cmix * Mthr) * Lr := by ring
    rw [heq]; exact hstep1
  linarith only [hm3ge, hm3h, hcMthrLr_le]

/-- `S^{-2} ≤ 4·σ∞^{-2}` once `S ≥ σ∞/2 > 0`. -/
private theorem homogBelow_qb_sq_inv_le
    {S sInf : ℝ} (hSpos : 0 < S) (hsInfpos : 0 < sInf) (hSge : sInf / 2 ≤ S) :
    S ^ (-(2 : ℝ)) ≤ 4 * sInf ^ (-(2 : ℝ)) := by
  have hsInf2nonneg : (0 : ℝ) ≤ sInf / 2 := by positivity
  have hsq : (sInf / 2) ^ 2 ≤ S ^ 2 := pow_le_pow_left₀ hsInf2nonneg hSge 2
  have heq : (sInf / 2) ^ 2 = sInf ^ 2 / 4 := by ring
  have hSsq_ge : sInf ^ 2 / 4 ≤ S ^ 2 := heq ▸ hsq
  have hS2pos : (0 : ℝ) < S ^ 2 := by positivity
  have hsInf2pos : (0 : ℝ) < sInf ^ 2 := by positivity
  have hrpowS : S ^ (-(2 : ℝ)) = (S ^ 2)⁻¹ := by
    rw [Real.rpow_neg hSpos.le, Real.rpow_two]
  have hrpowSInf : sInf ^ (-(2 : ℝ)) = (sInf ^ 2)⁻¹ := by
    rw [Real.rpow_neg hsInfpos.le, Real.rpow_two]
  have hinv : (S ^ 2)⁻¹ ≤ (sInf ^ 2 / 4)⁻¹ := (inv_le_inv₀ hS2pos (by positivity)).2 hSsq_ge
  have heq2 : (sInf ^ 2 / 4)⁻¹ = 4 * (sInf ^ 2)⁻¹ := by field_simp
  rw [hrpowS, hrpowSInf]
  linarith only [hinv, heq2.le, heq2.ge]

/-- `x^{1/2}·x^{1/2} = x` for `x ≥ 0`. -/
private theorem homogBelow_qb_rpow_half_sq {x : ℝ} (hx : 0 ≤ x) :
    x ^ ((1 : ℝ) / 2) * x ^ ((1 : ℝ) / 2) = x := by
  rcases hx.eq_or_lt with h0 | hpos
  · rw [← h0, Real.zero_rpow (by norm_num : (1 : ℝ) / 2 ≠ 0)]; ring
  · rw [← Real.rpow_add hpos]; norm_num

/-- `x^{-1}·x^{-1} = x^{-2}` for `x > 0`. -/
private theorem homogBelow_qb_rpow_neg_one_sq {x : ℝ} (hx : 0 < x) :
    x ^ (-(1 : ℝ)) * x ^ (-(1 : ℝ)) = x ^ (-(2 : ℝ)) := by
  rw [← Real.rpow_add hx]; norm_num

/-- `x^{-3000}·x^{-3000} = x^{-6000}` for `x > 0`. -/
private theorem homogBelow_qb_rpow_T3_sq {x : ℝ} (hx : 0 < x) :
    x ^ (-(3000 : ℝ)) * x ^ (-(3000 : ℝ)) = x ^ (-(6000 : ℝ)) := by
  rw [← Real.rpow_add hx]; norm_num

/-- **The sharp `T₁²` bound**: `(Cmix·A^{1/2}·S^{-1})² ≤ 4Cmix²·A·σ∞^{-2}`,
directly from `S ≥ σ∞/2`, no headroom trick needed. -/
private theorem homogBelow_qb_T1_sq_le
    {Cmix A S sInf : ℝ} (hCmix1 : 1 ≤ Cmix) (hA0 : 0 ≤ A) (hSpos : 0 < S)
    (hsInfpos : 0 < sInf) (hSge : sInf / 2 ≤ S) :
    (Cmix * A ^ ((1 : ℝ) / 2) * S ^ (-(1 : ℝ))) ^ 2 ≤ 4 * Cmix ^ 2 * A * sInf ^ (-(2 : ℝ)) := by
  have hexpand : (Cmix * A ^ ((1 : ℝ) / 2) * S ^ (-(1 : ℝ))) ^ 2 =
      Cmix ^ 2 * (A ^ ((1 : ℝ) / 2) * A ^ ((1 : ℝ) / 2)) * (S ^ (-(1 : ℝ)) * S ^ (-(1 : ℝ))) := by
    ring
  rw [hexpand, homogBelow_qb_rpow_half_sq hA0, homogBelow_qb_rpow_neg_one_sq hSpos]
  have hbound := homogBelow_qb_sq_inv_le hSpos hsInfpos hSge
  have hCmix2A_nonneg : (0 : ℝ) ≤ Cmix ^ 2 * A := by positivity
  calc Cmix ^ 2 * A * S ^ (-(2 : ℝ)) ≤ Cmix ^ 2 * A * (4 * sInf ^ (-(2 : ℝ))) :=
        mul_le_mul_of_nonneg_left hbound hCmix2A_nonneg
    _ = 4 * Cmix ^ 2 * A * sInf ^ (-(2 : ℝ)) := by ring

/-- **The sharp `T₂²` bound**: `(Cmix·A·S^{-2})² ≤ 16Cmix·A·σ∞^{-2}`, using
both `S ≥ σ∞/2` (to bound `S^{-2}` in terms of `σ∞^{-2}`) AND the headroom
fact `A ≤ σ∞²/Cmix` (to trade one factor of `A` for a `σ∞²`, turning the
naive quadratic-in-`A` bound linear). -/
private theorem homogBelow_qb_T2_sq_le
    {Cmix A S sInf : ℝ} (hCmixpos : 0 < Cmix) (hA0 : 0 ≤ A) (hSpos : 0 < S)
    (hsInfpos : 0 < sInf) (hSge : sInf / 2 ≤ S) (hAbound : A ≤ sInf ^ (2 : ℝ) / Cmix) :
    (Cmix * A * S ^ (-(2 : ℝ))) ^ 2 ≤ 16 * Cmix * A * sInf ^ (-(2 : ℝ)) := by
  set x : ℝ := S ^ (-(2 : ℝ)) with hxdef
  set y : ℝ := sInf ^ (-(2 : ℝ)) with hydef
  have hx0 : (0 : ℝ) ≤ x := (Real.rpow_pos_of_pos hSpos _).le
  have hypos : (0 : ℝ) < y := Real.rpow_pos_of_pos hsInfpos _
  have hb : x ≤ 4 * y := homogBelow_qb_sq_inv_le hSpos hsInfpos hSge
  have hAy : Cmix * A * y ≤ 1 := by
    have hyeq : sInf ^ (2 : ℝ) = y⁻¹ := by
      rw [hydef, Real.rpow_neg hsInfpos.le, inv_inv]
    have hAbound' : A ≤ y⁻¹ / Cmix := hyeq ▸ hAbound
    rw [le_div_iff₀ hCmixpos] at hAbound'
    have hAyCmix : A * y * Cmix ≤ y⁻¹ * y := by
      have := mul_le_mul_of_nonneg_right hAbound' hypos.le
      linarith only [this]
    have hyinv : y⁻¹ * y = 1 := inv_mul_cancel₀ hypos.ne'
    rw [hyinv] at hAyCmix
    nlinarith only [hAyCmix]
  have hCmixAy_nonneg : (0 : ℝ) ≤ Cmix * A * y := by positivity
  have hxsq : x ^ 2 ≤ (4 * y) ^ 2 := pow_le_pow_left₀ hx0 hb 2
  have hexpand : (Cmix * A * x) ^ 2 = Cmix ^ 2 * A ^ 2 * x ^ 2 := by ring
  calc (Cmix * A * x) ^ 2 = Cmix ^ 2 * A ^ 2 * x ^ 2 := hexpand
    _ ≤ Cmix ^ 2 * A ^ 2 * (4 * y) ^ 2 :=
        mul_le_mul_of_nonneg_left hxsq (by positivity)
    _ = 16 * (Cmix * A * y) * (Cmix * A * y) := by ring
    _ ≤ 16 * 1 * (Cmix * A * y) := by
        have := mul_le_mul_of_nonneg_right hAy hCmixAy_nonneg
        linarith only [this]
    _ = 16 * Cmix * A * y := by ring

/-- **The T3-term identity**: `(3Cmix·(max 1 h)^{-3000})² = 9Cmix²·(max 1 h)^{-6000}`. -/
private theorem homogBelow_qb_T3_sq_eq (Cmix : ℝ) {h : ℝ} (hh : 0 < h) :
    (3 * Cmix * h ^ (-(3000 : ℝ))) ^ 2 = 9 * Cmix ^ 2 * h ^ (-(6000 : ℝ)) := by
  have hexpand : (3 * Cmix * h ^ (-(3000 : ℝ))) ^ 2 =
      9 * Cmix ^ 2 * (h ^ (-(3000 : ℝ)) * h ^ (-(3000 : ℝ))) := by ring
  rw [hexpand, homogBelow_qb_rpow_T3_sq hh]

/-- **The generic "3 thirds" square combination**, valid for arbitrary reals
(no sign hypotheses needed): `(T1+T2+T3)² ≤ 3(a+b+c)` from `T1²≤a`, `T2²≤b`,
`T3²≤c`. -/
private theorem homogBelow_qb_three_sq_combo
    {T1 T2 T3 a b c : ℝ} (h1 : T1 ^ 2 ≤ a) (h2 : T2 ^ 2 ≤ b) (h3 : T3 ^ 2 ≤ c) :
    (T1 + T2 + T3) ^ 2 ≤ 3 * (a + b + c) := by
  nlinarith only [h1, h2, h3, sq_nonneg (T1 - T2), sq_nonneg (T2 - T3), sq_nonneg (T1 - T3)]

variable {d : ℕ} [NeZero d] (nu : ℝ) (hnu : 0 < nu) (L : ℕ) (Cmix : ℝ)
  (P : MeasureTheory.ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
  (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
  (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P)
  (hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P)
  (hJ4 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P)

include hnu hPrefix hJ2 hJ3 hJ4 in
/-- **The sharp `omegaSeq(h)²` bound** (the caller instantiates `h := m̃'`):
given `S(h) ≥ σ∞/2` (from
`e.rats.to.infty` plus monotonicity of `S`, at the output scale of the FIRST
application of [AK, Theorem 6.1]) and the headroom fact `(L-h) ≤ σ∞²/Cmix`
(`homogBelow_headroom_sq_le`), `ω_h²` is bounded LINEARLY in `(L-h)_+`, with
an `M`-independent prefactor, matching `hThetaLm`'s target shape after the
caller converts `h`-scale quantities to the final scale `m`. -/
theorem homogBelow_omegaSeq_sharp_bound
    (hCmix1 : 1 ≤ Cmix)
    (h : ℕ)
    (hSge : (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu L P) / 2 ≤
      SuperdiffusionCLT.Section2.Annealed.sigmaBarStarScalar nu L P
        (Homogenization.cubeSet (Homogenization.originCube d (h : ℤ))))
    (hAbound : ((L - h : ℕ) : ℝ) ≤
      (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu L P) ^ (2 : ℝ) / Cmix) :
    homogBelow_omegaSeq nu L Cmix P h ^ 2 ≤
      3 * (Homogenization.IndependentSums.gammaTriangleConst ((1 : ℝ) / 3)) ^ 2 *
          (4 * Cmix ^ 2 + 16 * Cmix) * ((L - h : ℕ) : ℝ) *
          (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu L P) ^ (-(2 : ℝ)) +
        3 * (Homogenization.IndependentSums.gammaTriangleConst ((1 : ℝ) / 3)) ^ 2 * 9 * Cmix ^ 2 *
          (max 1 (h : ℝ)) ^ (-(6000 : ℝ)) := by
  have hCmixpos : (0 : ℝ) < Cmix := lt_of_lt_of_le zero_lt_one hCmix1
  have hSpos := homogBelow_sigmaBarStarScalar_pos nu hnu L P hPrefix hJ2 hJ3 hJ4 h
  have hsInfpos : (0 : ℝ) < SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu L P :=
    SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite_pos hnu L hPrefix hJ2 hJ3 hJ4
  have hA0 : (0 : ℝ) ≤ ((L - h : ℕ) : ℝ) := by positivity
  have hmax1hpos : (0 : ℝ) < max 1 (h : ℝ) := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hT1sq := homogBelow_qb_T1_sq_le (Cmix := Cmix) (A := ((L - h : ℕ) : ℝ))
    (S := SuperdiffusionCLT.Section2.Annealed.sigmaBarStarScalar nu L P
      (Homogenization.cubeSet (Homogenization.originCube d (h : ℤ))))
    (sInf := SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu L P)
    hCmix1 hA0 hSpos hsInfpos hSge
  have hT2sq := homogBelow_qb_T2_sq_le (Cmix := Cmix) (A := ((L - h : ℕ) : ℝ))
    (S := SuperdiffusionCLT.Section2.Annealed.sigmaBarStarScalar nu L P
      (Homogenization.cubeSet (Homogenization.originCube d (h : ℤ))))
    (sInf := SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu L P)
    hCmixpos hA0 hSpos hsInfpos hSge hAbound
  have hT3sq := homogBelow_qb_T3_sq_eq Cmix hmax1hpos
  have hcombo := homogBelow_qb_three_sq_combo hT1sq hT2sq hT3sq.le
  have hK3sq_nonneg : (0 : ℝ) ≤
      (Homogenization.IndependentSums.gammaTriangleConst ((1 : ℝ) / 3)) ^ 2 := sq_nonneg _
  have hscaled := mul_le_mul_of_nonneg_left hcombo hK3sq_nonneg
  have hrw : homogBelow_omegaSeq nu L Cmix P h =
      Homogenization.IndependentSums.gammaTriangleConst ((1 : ℝ) / 3) *
        (Cmix * ((L - h : ℕ) : ℝ) ^ ((1 : ℝ) / 2) *
            SuperdiffusionCLT.Section2.Annealed.sigmaBarStarScalar nu L P
              (Homogenization.cubeSet (Homogenization.originCube d (h : ℤ))) ^ (-(1 : ℝ)) +
          Cmix * ((L - h : ℕ) : ℝ) *
              SuperdiffusionCLT.Section2.Annealed.sigmaBarStarScalar nu L P
                (Homogenization.cubeSet (Homogenization.originCube d (h : ℤ))) ^ (-(2 : ℝ)) +
            3 * Cmix * (max 1 (h : ℝ)) ^ (-(3000 : ℝ))) := by
    unfold homogBelow_omegaSeq; ring
  rw [hrw]
  have hsq : (Homogenization.IndependentSums.gammaTriangleConst ((1 : ℝ) / 3) *
      (Cmix * ((L - h : ℕ) : ℝ) ^ ((1 : ℝ) / 2) *
          SuperdiffusionCLT.Section2.Annealed.sigmaBarStarScalar nu L P
            (Homogenization.cubeSet (Homogenization.originCube d (h : ℤ))) ^ (-(1 : ℝ)) +
        Cmix * ((L - h : ℕ) : ℝ) *
            SuperdiffusionCLT.Section2.Annealed.sigmaBarStarScalar nu L P
              (Homogenization.cubeSet (Homogenization.originCube d (h : ℤ))) ^ (-(2 : ℝ)) +
          3 * Cmix * (max 1 (h : ℝ)) ^ (-(3000 : ℝ)))) ^ 2 =
      (Homogenization.IndependentSums.gammaTriangleConst ((1 : ℝ) / 3)) ^ 2 *
        ((Cmix * ((L - h : ℕ) : ℝ) ^ ((1 : ℝ) / 2) *
              SuperdiffusionCLT.Section2.Annealed.sigmaBarStarScalar nu L P
                (Homogenization.cubeSet (Homogenization.originCube d (h : ℤ))) ^ (-(1 : ℝ))) +
            (Cmix * ((L - h : ℕ) : ℝ) *
                SuperdiffusionCLT.Section2.Annealed.sigmaBarStarScalar nu L P
                  (Homogenization.cubeSet (Homogenization.originCube d (h : ℤ))) ^ (-(2 : ℝ))) +
              3 * Cmix * (max 1 (h : ℝ)) ^ (-(3000 : ℝ))) ^ 2 := by ring
  rw [hsq]
  nlinarith only [hscaled]

end SuperdiffusionCLT.Section4.HomogBelow

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section4.Mixing.MixMainTerm1B
public import SuperdiffusionCLT.Section4.Mixing.MixMainAbsorb

/-!
# mixMain: the `hLocBound`-shaped witness, at the literal `TermsCombined.lean`
bare amplitude

The absorption step in the proof of `p.mixing.P.three.prime`:
`MixMainTerm1B.lean`'s `mixMain_term1BoundB` gives an *explicit* amplitude
(`ellipBelow_crudeConst d · ν^{-3} · ell` times `Term1UniformBound.lean`'s own
explicit witness amplitude, itself built from `mixTerms_stuffFactor`'s two
decay terms `L · 3^{-(ell-n)}` and `ell · L · (m-n) · 3^{-(d/2)(m-ell)}`).
This file converts that explicit amplitude into the literal bare
`C · m^{-5000}` form `TermsCombined.lean`'s `mixTerms_combineTermsBound` (and
hence `AnnealedFinal.lean`'s `mixFin_annealedComparison`) actually consumes as
`hLocBound`, using exactly the mixing-gap margins
supplied by the choice of the auxiliary scale
(`ell - n ≥ (K/10) log(ν⁻¹L)`, `m - ell ≥ (K/10) log(ν⁻¹L)`) together with the
case guard `m ≤ L + (K/2) log(ν⁻¹L)`, fixing the canonical threshold
`K₀ := 50100 / log 3` (a pure numeral, independent of `d, ν, L, m, n`, so the
resulting bare-form witness constant is `∃ C(d)` uniform in `ν, P, L, m, n,
ell`, matching the `∃ C` quantifier order of the statement).

## Main results

* `mixMain_term1_amplitude_bound`: the pure real-analysis absorption core --
  for any `K ≥ 50100/log 3`, `∃ C'(d, K, C)` (uniform in `ν, L, m, n, ell`)
  such that whenever the two mixing-gap margins and the case guard hold,
  `mixMain_term1BoundB`'s explicit amplitude is `≤ C' · m^{-5000}`. Proof:
  `Y := ν⁻¹L ≥ 1` dominates `ell, L, ν⁻¹` linearly and `m` up to the factor
  `1 + K/2` (`mixMain_m_le_mul_nuInvL`); both decay factors `3^{-(ell-n)}`,
  `3^{-(d/2)(m-ell)}` are `≤ Y^{-c'}` for `c' := K log 3 / 10 ≥ 5010`
  (`mixMain_gammaLog_eq_rpow`, using `d ≥ 2` for the second); `gcongr`
  assembles the two decay terms directly into `Y^{8-c'}` and `Bm · Y^{10-c'}`
  (exponents `≤ -5000`), absorbed into `m^{-5000}` by
  `mixMain_rpow_le_of_le_mul`.
* `mixMain_term1BoundBare`: the assembled `hLocBound`-shaped witness at the
  canonical threshold `K₀ := 50100/log 3`, `∃ C` uniform in `ν, P, L, m, n,
  ell`. -/

@[expose] public section

namespace SuperdiffusionCLT.Section4.Mixing

open Homogenization
open Homogenization.IndependentSums
open MeasureTheory
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Cutoff (ShellSeq)
open SuperdiffusionCLT.Section4.Ellipticity

noncomputable section

variable {d : ℕ}

/-- **The absorption core.** For `K ≥ 50100/log 3`, `∃ C'(d, K, C)`, uniform
in `ν, L, m, n, ell`, such that under the mixing-gap margins `(K/10)
log(ν⁻¹L) ≤ ell - n`, `(K/10) log(ν⁻¹L) ≤ m - ell` (both as reals, from
the choice of the auxiliary scale) together with the case guard `m ≤ L + (K/2)
log(ν⁻¹L)`, `mixMain_term1BoundB`'s explicit amplitude is bounded by
`C' · m^{-5000}`. -/
theorem mixMain_term1_amplitude_bound (d : ℕ) [NeZero d] (hd : 2 ≤ d) (K : ℝ)
    (hK : 50100 / Real.log 3 ≤ K) (C : ℝ) :
    ∃ C' : ℝ, 0 ≤ C' ∧
      ∀ (nu : ℝ) (L m n ell : ℕ), 0 < nu → nu ≤ 1 → 1 ≤ L → 1 ≤ m → ell ≤ L →
        (K / 10 * Real.log (nu⁻¹ * (L:ℝ)) ≤ ((ell - n : ℕ):ℝ)) →
        (K / 10 * Real.log (nu⁻¹ * (L:ℝ)) ≤ ((m - ell : ℕ):ℝ)) →
        ((m:ℝ) ≤ (L:ℝ) + K / 2 * Real.log (nu⁻¹ * (L:ℝ))) →
        ellipBelow_crudeConst d * nu ^ (-(3:ℝ)) * (ell:ℝ) *
          (gammaTriangleConst (1/3) * ((Fintype.card (BlockCoord d × BlockCoord d):ℝ) *
            mixTerms_pairFinalAmp C nu d ell L n m)) ≤
        C' * (m:ℝ) ^ (-(5000:ℝ)) := by
  have hlog3_pos : (0:ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  have hK0 : 0 ≤ K := le_trans (by positivity) hK
  set Bm : ℝ := 1 + K/2 with hBmdef
  have hBm1 : (1:ℝ) ≤ Bm := by rw [hBmdef]; linarith only [hK0]
  have hBm_pos : (0:ℝ) < Bm := lt_of_lt_of_le (by norm_num) hBm1
  set c' : ℝ := K * Real.log 3 / 10 with hc'def
  have hc'_ge : (5010:ℝ) ≤ c' := by
    rw [hc'def]
    have hK' : (50100:ℝ) ≤ K * Real.log 3 := (div_le_iff₀ hlog3_pos).1 hK
    linarith only [hK']
  set Mfac : ℝ := 2 * (gammaTriangleConst (1/3))^2 * (2 * gammaTriangleConst (1/3) + 1) with hMfacdef
  set Mconst : ℝ := ellipBelow_crudeConst d * gammaTriangleConst (1/3) *
      (Fintype.card (BlockCoord d × BlockCoord d):ℝ) * Mfac * 4 * (|C| + 1) with hMconstdef
  have hMconst_nn : (0:ℝ) ≤ Mconst := by
    have hcrude_nn : (0:ℝ) ≤ ellipBelow_crudeConst d :=
      le_trans zero_le_one (ellipBelow_one_le_crudeConst d)
    have hTri_nn : (0:ℝ) ≤ gammaTriangleConst (1/3) := gammaTriangleConst_pos.le
    have hMfac_nn : (0:ℝ) ≤ Mfac := by rw [hMfacdef]; positivity
    have hcard_nn : (0:ℝ) ≤ (Fintype.card (BlockCoord d × BlockCoord d):ℝ) := by positivity
    have hCabs_nn : (0:ℝ) ≤ |C| + 1 := by positivity
    rw [hMconstdef]
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hcrude_nn hTri_nn) hcard_nn)
      hMfac_nn) (by norm_num)) hCabs_nn
  have ha8 : (8 - c' : ℝ) ≤ 0 := by linarith only [hc'_ge]
  have ha8' : (8 - c' : ℝ) ≤ -(5000:ℝ) := by linarith only [hc'_ge]
  have ha10 : (10 - c' : ℝ) ≤ 0 := by linarith only [hc'_ge]
  have ha10' : (10 - c' : ℝ) ≤ -(5000:ℝ) := by linarith only [hc'_ge]
  have hBmpow8_nn : (0:ℝ) ≤ Bm ^ (-(8 - c')) := Real.rpow_nonneg hBm_pos.le _
  have hBmpow10_nn : (0:ℝ) ≤ Bm ^ (-(10 - c')) := Real.rpow_nonneg hBm_pos.le _
  refine ⟨Mconst * (Bm ^ (-(8 - c')) + Bm * Bm ^ (-(10 - c'))), ?_, ?_⟩
  · have : (0:ℝ) ≤ Bm * Bm ^ (-(10 - c')) := mul_nonneg hBm_pos.le hBmpow10_nn
    exact mul_nonneg hMconst_nn (by linarith only [hBmpow8_nn, this])
  · intro nu L m n ell hnu hnu1 hL hm1 hlL hgap1 hgap2 hcase
    set Y : ℝ := nu⁻¹ * (L:ℝ) with hYdef
    have hnuinv1 : (1:ℝ) ≤ nu⁻¹ := (one_le_inv₀ hnu).2 hnu1
    have hLcast : (1:ℝ) ≤ (L:ℝ) := by exact_mod_cast hL
    have hY1 : (1:ℝ) ≤ Y := by
      rw [hYdef]
      calc (1:ℝ) = 1*1 := by ring
        _ ≤ nu⁻¹ * (L:ℝ) := mul_le_mul hnuinv1 hLcast (by norm_num) (by linarith only [hnuinv1])
    have hY_pos : (0:ℝ) < Y := lt_of_lt_of_le (by norm_num) hY1
    have hnuinv_le_Y : nu⁻¹ ≤ Y := by
      rw [hYdef]; calc nu⁻¹ = nu⁻¹ * 1 := by ring
        _ ≤ nu⁻¹ * (L:ℝ) := mul_le_mul_of_nonneg_left hLcast (by positivity)
    have hL_le_Y : (L:ℝ) ≤ Y := by
      rw [hYdef]; calc (L:ℝ) = 1 * (L:ℝ) := by ring
        _ ≤ nu⁻¹ * (L:ℝ) := mul_le_mul_of_nonneg_right hnuinv1 (by linarith only [hLcast])
    have hellcast : (ell:ℝ) ≤ (L:ℝ) := by exact_mod_cast hlL
    have hell_le_Y : (ell:ℝ) ≤ Y := hellcast.trans hL_le_Y
    have hm_le_BmY : (m:ℝ) ≤ Bm * Y := by
      have := mixMain_m_le_mul_nuInvL hnu hnu1 hK0 hL hcase
      rw [hYdef]; exact this
    have hmaxell : max 1 (ell:ℝ) ≤ Y := max_le hY1 hell_le_Y
    have hmaxL : max 1 (L:ℝ) ≤ Y := max_le hY1 hL_le_Y
    have hmn_le_m : ((m - n : ℕ):ℝ) ≤ (m:ℝ) := by exact_mod_cast Nat.sub_le m n
    have hmaxmn : max 1 ((m - n : ℕ):ℝ) ≤ Bm * Y := by
      refine max_le ?_ (hmn_le_m.trans hm_le_BmY)
      nlinarith only [hBm1, hY1]
    have hlogY_nonneg : 0 ≤ Real.log Y := Real.log_nonneg hY1
    have hexp1 : (3:ℝ) ^ (-(((ell - n : ℕ):ℕ):ℝ)) ≤ Y ^ (-c') := by
      have hstep : (3:ℝ) ^ (-(((ell - n : ℕ):ℕ):ℝ)) ≤ (3:ℝ) ^ (-(K/10 * Real.log Y)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith only [hgap1])
      have heq : (3:ℝ) ^ (-(K/10 * Real.log Y)) = Y ^ (-c') := by
        rw [hc'def]; exact mixMain_gammaLog_eq_rpow (c := K) hY_pos
      linarith only [hstep, heq.le, heq.ge]
    have hdhalf1 : (1:ℝ) ≤ (d:ℝ)/2 := by
      have : (2:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
      linarith only [this]
    have hmellnn : (0:ℝ) ≤ ((m - ell : ℕ):ℝ) := by positivity
    have hgap2' : K/10 * Real.log Y ≤ (d:ℝ)/2 * ((m - ell : ℕ):ℝ) := by
      have h1 : K/10 * Real.log Y ≤ ((m-ell:ℕ):ℝ) := hgap2
      nlinarith only [h1, hdhalf1, hmellnn]
    have hexp2 : (3:ℝ) ^ (-((d:ℝ)/2 * ((m - ell : ℕ):ℝ))) ≤ Y ^ (-c') := by
      have hstep : (3:ℝ) ^ (-((d:ℝ)/2 * ((m - ell : ℕ):ℝ))) ≤ (3:ℝ) ^ (-(K/10 * Real.log Y)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith only [hgap2'])
      have heq : (3:ℝ) ^ (-(K/10 * Real.log Y)) = Y ^ (-c') := by
        rw [hc'def]; exact mixMain_gammaLog_eq_rpow (c := K) hY_pos
      linarith only [hstep, heq.le, heq.ge]
    have hnu3_le : nu ^ (-(3:ℝ)) ≤ Y ^ (3:ℝ) := by
      have hnu3eq : nu ^ (-(3:ℝ)) = (nu⁻¹) ^ (3:ℝ) := by
        rw [Real.rpow_neg hnu.le, ← Real.inv_rpow hnu.le]
      rw [hnu3eq]
      exact Real.rpow_le_rpow (by positivity) hnuinv_le_Y (by norm_num)
    have hnu3_nn : (0:ℝ) ≤ nu ^ (-(3:ℝ)) := by positivity
    have hYaddc : ∀ a b : ℝ, Y ^ a * Y ^ b = Y ^ (a + b) := fun a b => (Real.rpow_add hY_pos a b).symm
    -- Stuff-factor bound (drop the `if`).
    have hStuffLe : mixTerms_stuffFactor d ell L n m ≤
        (L:ℝ) * (3:ℝ) ^ (-(((ell - n : ℕ):ℕ):ℝ)) +
          max 1 (ell:ℝ) * max 1 (L:ℝ) * max 1 ((m - n : ℕ):ℝ) *
            (3:ℝ) ^ (-((d:ℝ)/2 * ((m - ell : ℕ):ℕ):ℝ)) := by
      unfold mixTerms_stuffFactor
      have hnn : (0:ℝ) ≤ (L:ℝ) * (3:ℝ) ^ (-(((ell - n : ℕ):ℕ):ℝ)) := by positivity
      split_ifs with h
      · exact le_refl _
      · linarith only [hnn]
    have hellnn : (0:ℝ) ≤ (ell:ℝ) := by positivity
    have hStuffNN : (0:ℝ) ≤ mixTerms_stuffFactor d ell L n m := by
      unfold mixTerms_stuffFactor
      have h1 : (0:ℝ) ≤ if ell < L then (L:ℝ) * (3:ℝ) ^ (-(((ell - n : ℕ):ℕ):ℝ)) else 0 := by
        split_ifs <;> positivity
      positivity
    -- T1: `nu^{-3} nu^{-3} ell L 3^{-(ell-n)} ≤ Y^{8-c'}`.
    have hT1raw : nu ^ (-(3:ℝ)) * nu ^ (-(3:ℝ)) * (ell:ℝ) * (L:ℝ) *
        (3:ℝ) ^ (-(((ell - n : ℕ):ℕ):ℝ)) ≤
        Y ^ (3:ℝ) * Y ^ (3:ℝ) * Y * Y * Y ^ (-c') := by
      gcongr
    have hY8mc : Y ^ (3:ℝ) * Y ^ (3:ℝ) * Y * Y * Y ^ (-c') = Y ^ (8 - c') := by
      rw [show Y ^ (3:ℝ) * Y ^ (3:ℝ) * Y * Y * Y ^ (-c') =
          Y ^ (3:ℝ) * Y ^ (3:ℝ) * Y ^ (1:ℝ) * Y ^ (1:ℝ) * Y ^ (-c') by rw [Real.rpow_one]]
      simp only [← Real.rpow_add hY_pos]
      congr 1; ring
    have hT1 : nu ^ (-(3:ℝ)) * nu ^ (-(3:ℝ)) * (ell:ℝ) * (L:ℝ) *
        (3:ℝ) ^ (-(((ell - n : ℕ):ℕ):ℝ)) ≤ Y ^ (8 - c') := hY8mc ▸ hT1raw
    -- T2: `nu^{-3} nu^{-3} ell max(1,ell) max(1,L) max(1,m-n) 3^{-(d/2)(m-ell)} ≤ Bm·Y^{10-c'}`.
    have hT2raw : nu ^ (-(3:ℝ)) * nu ^ (-(3:ℝ)) * (ell:ℝ) * max 1 (ell:ℝ) * max 1 (L:ℝ) *
        max 1 ((m - n : ℕ):ℝ) * (3:ℝ) ^ (-((d:ℝ)/2 * ((m - ell : ℕ):ℕ):ℝ)) ≤
        Y ^ (3:ℝ) * Y ^ (3:ℝ) * Y * Y * Y * (Bm * Y) * Y ^ (-c') := by
      gcongr
    have hY10mc : Y ^ (3:ℝ) * Y ^ (3:ℝ) * Y * Y * Y * (Bm * Y) * Y ^ (-c') = Bm * Y ^ (10 - c') := by
      rw [show Y ^ (3:ℝ) * Y ^ (3:ℝ) * Y * Y * Y * (Bm * Y) * Y ^ (-c') =
          Bm * (Y ^ (3:ℝ) * Y ^ (3:ℝ) * Y ^ (1:ℝ) * Y ^ (1:ℝ) * Y ^ (1:ℝ) * Y ^ (1:ℝ) * Y ^ (-c'))
          by rw [Real.rpow_one]; ring]
      simp only [← Real.rpow_add hY_pos]
      rw [show (3 + 3 + 1 + 1 + 1 + 1 + -c' : ℝ) = 10 - c' by ring]
    have hT2 : nu ^ (-(3:ℝ)) * nu ^ (-(3:ℝ)) * (ell:ℝ) * max 1 (ell:ℝ) * max 1 (L:ℝ) *
        max 1 ((m - n : ℕ):ℝ) * (3:ℝ) ^ (-((d:ℝ)/2 * ((m - ell : ℕ):ℕ):ℝ)) ≤
        Bm * Y ^ (10 - c') := hY10mc ▸ hT2raw
    -- Assemble: full amplitude ≤ Mconst · (Y^{8-c'} + Bm·Y^{10-c'}).
    set Mfac : ℝ := 2 * (gammaTriangleConst (1/3))^2 * (2 * gammaTriangleConst (1/3) + 1) with hMfacdef2
    have hPairFinalEq : mixTerms_pairFinalAmp C nu d ell L n m =
        Mfac * mixTerms_pairCommonAmp C nu d ell L n m := by
      rw [hMfacdef2]; unfold mixTerms_pairFinalAmp; ring
    have hCommonEq : mixTerms_pairCommonAmp C nu d ell L n m =
        (|C| + 1) * nu ^ (-(3:ℝ)) * 4 * mixTerms_stuffFactor d ell L n m := by
      unfold mixTerms_pairCommonAmp; ring
    have hEq : ellipBelow_crudeConst d * nu ^ (-(3:ℝ)) * (ell:ℝ) *
        (gammaTriangleConst (1/3) * ((Fintype.card (BlockCoord d × BlockCoord d):ℝ) *
          mixTerms_pairFinalAmp C nu d ell L n m)) =
        Mconst * ((nu ^ (-(3:ℝ)) * nu ^ (-(3:ℝ)) * (ell:ℝ)) * mixTerms_stuffFactor d ell L n m) := by
      rw [hPairFinalEq, hCommonEq, hMconstdef, hMfacdef2]; ring
    have hAmp_le : (nu ^ (-(3:ℝ)) * nu ^ (-(3:ℝ)) * (ell:ℝ)) * mixTerms_stuffFactor d ell L n m ≤
        Y ^ (8 - c') + Bm * Y ^ (10 - c') := by
      have hdistrib : (nu ^ (-(3:ℝ)) * nu ^ (-(3:ℝ)) * (ell:ℝ)) * ((L:ℝ) *
            (3:ℝ) ^ (-(((ell - n : ℕ):ℕ):ℝ)) +
          max 1 (ell:ℝ) * max 1 (L:ℝ) * max 1 ((m - n : ℕ):ℝ) *
            (3:ℝ) ^ (-((d:ℝ)/2 * ((m - ell : ℕ):ℕ):ℝ))) =
          nu ^ (-(3:ℝ)) * nu ^ (-(3:ℝ)) * (ell:ℝ) * (L:ℝ) * (3:ℝ) ^ (-(((ell - n : ℕ):ℕ):ℝ)) +
            nu ^ (-(3:ℝ)) * nu ^ (-(3:ℝ)) * (ell:ℝ) * max 1 (ell:ℝ) * max 1 (L:ℝ) *
              max 1 ((m - n : ℕ):ℝ) * (3:ℝ) ^ (-((d:ℝ)/2 * ((m - ell : ℕ):ℕ):ℝ)) := by ring
      have hmul := mul_le_mul_of_nonneg_left hStuffLe
        (show (0:ℝ) ≤ nu ^ (-(3:ℝ)) * nu ^ (-(3:ℝ)) * (ell:ℝ) by positivity)
      rw [hdistrib] at hmul
      linarith only [hmul, hT1, hT2]
    -- Absorb `Y^{8-c'}`, `Y^{10-c'}` into `m^{-5000}`.
    have hm_pos : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm1
    have hm1' : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm1
    have hYa1 : Y ^ (8 - c') ≤ Bm ^ (-(8 - c')) * (m:ℝ) ^ (8 - c') :=
      mixMain_rpow_le_of_le_mul hBm_pos hm_pos ha8 hm_le_BmY
    have hYa2 : Y ^ (10 - c') ≤ Bm ^ (-(10 - c')) * (m:ℝ) ^ (10 - c') :=
      mixMain_rpow_le_of_le_mul hBm_pos hm_pos ha10 hm_le_BmY
    have hma1 : (m:ℝ) ^ (8 - c') ≤ (m:ℝ) ^ (-(5000:ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hm1' ha8'
    have hma2 : (m:ℝ) ^ (10 - c') ≤ (m:ℝ) ^ (-(5000:ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hm1' ha10'
    have hpart1 : Y ^ (8 - c') ≤ Bm ^ (-(8 - c')) * (m:ℝ) ^ (-(5000:ℝ)) :=
      hYa1.trans (mul_le_mul_of_nonneg_left hma1 hBmpow8_nn)
    have hpart2 : Bm * Y ^ (10 - c') ≤ (Bm * Bm ^ (-(10 - c'))) * (m:ℝ) ^ (-(5000:ℝ)) := by
      have h1 : Bm * Y ^ (10 - c') ≤ Bm * (Bm ^ (-(10 - c')) * (m:ℝ) ^ (10 - c')) :=
        mul_le_mul_of_nonneg_left hYa2 hBm_pos.le
      have h2 : Bm * (Bm ^ (-(10 - c')) * (m:ℝ) ^ (10 - c')) ≤
          Bm * (Bm ^ (-(10 - c')) * (m:ℝ) ^ (-(5000:ℝ))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hma2 hBmpow10_nn) hBm_pos.le
      calc Bm * Y ^ (10 - c') ≤ Bm * (Bm ^ (-(10 - c')) * (m:ℝ) ^ (10 - c')) := h1
        _ ≤ Bm * (Bm ^ (-(10 - c')) * (m:ℝ) ^ (-(5000:ℝ))) := h2
        _ = (Bm * Bm ^ (-(10 - c'))) * (m:ℝ) ^ (-(5000:ℝ)) := by ring
    have hFin : Y ^ (8 - c') + Bm * Y ^ (10 - c') ≤
        (Bm ^ (-(8 - c')) + Bm * Bm ^ (-(10 - c'))) * (m:ℝ) ^ (-(5000:ℝ)) := by
      nlinarith only [hpart1, hpart2]
    rw [hEq]
    calc Mconst * ((nu ^ (-(3:ℝ)) * nu ^ (-(3:ℝ)) * (ell:ℝ)) * mixTerms_stuffFactor d ell L n m)
        ≤ Mconst * (Y ^ (8 - c') + Bm * Y ^ (10 - c')) :=
          mul_le_mul_of_nonneg_left hAmp_le hMconst_nn
      _ ≤ Mconst * ((Bm ^ (-(8 - c')) + Bm * Bm ^ (-(10 - c'))) * (m:ℝ) ^ (-(5000:ℝ))) :=
          mul_le_mul_of_nonneg_left hFin hMconst_nn
      _ = Mconst * (Bm ^ (-(8 - c')) + Bm * Bm ^ (-(10 - c'))) * (m:ℝ) ^ (-(5000:ℝ)) := by ring

/-- **`hLocBound`, at `TermsCombined.lean`'s literal bare `C · m^{-5000}`
amplitude**, `∃ C(d)` uniform in `ν, P, L, m, n, ell`, at the canonical
threshold `K₀ := 50100 / log 3`. Combines `mixMain_term1BoundB` with
`mixMain_term1_amplitude_bound` (at `K := K₀`) via `IsBigO.mono_scale`. -/
theorem mixMain_term1BoundBare (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (nu : ℝ), 0 < nu → nu ≤ 1 →
        ∀ (P : ProbabilityMeasure (ShellSeq d)),
          ShellLawPrefix d P → ShellLawJ1Restriction d P → ShellLawJ2 d P → ShellLawJ3 d P → ShellLawJ4 d P →
            ∀ m n ell L : ℕ, n ≤ ell → ell ≤ m → ell ≤ L → 1 ≤ ell → 1 ≤ L → 1 ≤ m →
              ((50100 / Real.log 3) / 10 * Real.log (nu⁻¹ * (L:ℝ)) ≤ ((ell - n : ℕ):ℝ)) →
              ((50100 / Real.log 3) / 10 * Real.log (nu⁻¹ * (L:ℝ)) ≤ ((m - ell : ℕ):ℝ)) →
              ((m:ℝ) ≤ (L:ℝ) + (50100 / Real.log 3) / 2 * Real.log (nu⁻¹ * (L:ℝ))) →
              ∃ X3loc : ShellSeq d → ℝ,
                Measurable X3loc ∧
                  IsBigO P.toMeasure (gammaSigma ((1:ℝ)/3)) X3loc (C * (m:ℝ) ^ (-(5000:ℝ))) ∧
                  ∀ (omega : ShellSeq d) (p q : BlockVec d),
                    2 *
                        (((descendantsAtDepth (originCube d (m : ℤ)) (m - n)).card : ℝ)⁻¹ *
                          ∑ R ∈ descendantsAtDepth (originCube d (m : ℤ)) (m - n),
                            blockVecDot p
                              (blockMatVecMul (mixTerms_localizationTermMatrix nu omega ell L P (n : ℤ) R) q)) ≤
                      X3loc omega *
                        (blockVecDot p (blockMatVecMul (mixTerms_Aell nu ell P (n : ℤ)) p) +
                          blockVecDot q (blockMatVecMul (mixTerms_Aell nu ell P (n : ℤ)) q)) := by
  obtain ⟨C0, hC0⟩ := mixMain_term1BoundB d
  obtain ⟨C', hC'nn, hC'⟩ :=
    mixMain_term1_amplitude_bound d hd (50100 / Real.log 3) (le_refl _) C0
  refine ⟨max 1 C', le_max_left _ _, ?_⟩
  intro nu hnu hnu1 P hPrefix hJ1 hJ2 hJ3 hJ4 m n ell L hnl hlm hlL hell1 hL1 hm1 hgap1 hgap2 hcase
  obtain ⟨X, hXm, hXO, hXbd⟩ := hC0 nu hnu hnu1 P hPrefix hJ1 hJ2 hJ3 hJ4 m n ell L hnl hlm hlL hell1
  have hAmpLe := hC' nu L m n ell hnu hnu1 hL1 hm1 hlL hgap1 hgap2 hcase
  have hmp : (0:ℝ) ≤ (m:ℝ) ^ (-(5000:ℝ)) := by positivity
  have hfin : C' * (m:ℝ) ^ (-(5000:ℝ)) ≤ max 1 C' * (m:ℝ) ^ (-(5000:ℝ)) :=
    mul_le_mul_of_nonneg_right (le_max_right _ _) hmp
  exact ⟨X, hXm, hXO.mono_scale (hAmpLe.trans hfin), hXbd⟩

end

end SuperdiffusionCLT.Section4.Mixing

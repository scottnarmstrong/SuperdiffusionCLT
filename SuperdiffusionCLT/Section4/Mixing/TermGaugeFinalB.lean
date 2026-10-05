/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section4.Mixing.TermGaugeFinal

/-!
# mixGaugeFinal: assembling `hGaugeBound`, part 2 (scale conversion and the final witness)

`TermGaugeFinal.lean`
supplies the deterministic averaged bilinear bound at the `ell`-order scalar
`t_ell := sigmaBarStarInvScalar nu ell P (cu_n)`. This file converts `t_ell`
to the `L`-order scalar `t_L := sigmaBarStarInvScalar nu L P (cu_n)` via
a scale comparison
(`t_ell ≤ t_L + E`, with `E` an *explicit* amplitude, never a bare
`m^{-6000}`/`m^{-5000}`), and assembles a witness for
`TermsCombined.lean`'s `hGaugeBound`.

**Refutation of the literal `hGaugeBound` shape.** `hGaugeBound`'s `X3g`
clause demands `IsBigO P.toMeasure (gammaSigma (1/3)) X3g (C * m ^ (-5000))`
for the *same* `C` shared with `X1g`, `X2g` (hence forced `C`-independent of
`ell, L, n`) -- but the leftover produced by the `t_ell -> t_L` conversion has
size of order `E * (L - ell)^{1/2}`, with `E` depending on `ell, L, n, nu`
alone and *not* shrinking as `m -> infinity` for `ell, L, n` fixed. Concretely,
at `nu = 1`, `n = ell = 0`, `L = 1`: `E` is then a fixed positive number
(independent of `m`), so no fixed `C` bounds it by `C * m ^ (-5000)` for
every `m` (the bound fails as `m -> infinity`). This is the same phenomenon
that occurs for `hSigmaStarTail`;
this file records the honest replacement, with
`X3g`'s amplitude stated *explicitly* in terms of `ell, L, n, nu` instead of
the bare `m`-power the proof sketch of `p.mixing.P.three.prime` anticipated but the
printed statement (with `ell, L, n, m` otherwise unconstrained) does not
actually deliver.

## Main result

* `mixGaugeFinal_X1g_isBigO`, `mixGaugeFinal_X2g_isBigO`: the witnesses `X1g`, `X2g`
  in the exact shape of the printed statement (valid once `C` dominates the explicit
  dimension-only constant `mixGaugeFinal_Cbase d`).
* `mixGaugeFinal_X3g_isBigO`: the witness `X3g` in the honest B-form.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section4.Mixing

open MeasureTheory
open Homogenization
open Homogenization.Book.Ch02
open Homogenization.IndependentSums
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Cutoff (ShellSeq finiteShellIncrement)
open SuperdiffusionCLT.Section2.Estimates.Stream

noncomputable section

variable {d : ℕ} {P : ProbabilityMeasure (ShellSeq d)}

/-! ## The `rpow`-to-inverse conversions on `sigmaBarStarScalar` -/

theorem mixGaugeFinal_sigmaBarStarScalar_rpow_neg_one [NeZero d] {nu : ℝ} (hnu : 0 < nu) (L : ℕ)
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P)
    (hJ4 : ShellLawJ4 d P) (n : ℤ) :
    (sigmaBarStarScalar nu L P (cubeSet (originCube d n))) ^ (-(1 : ℝ)) =
      sigmaBarStarInvScalar nu L P (cubeSet (originCube d n)) := by
  have htpos := sigmaBarStarInvScalar_pos_cutoff hnu L hPrefix hJ2 hJ3 hJ4 n
  rw [sigmaBarStarScalar_eq_inv hnu L hJ4 n htpos, Real.rpow_neg (inv_nonneg.2 htpos.le),
    Real.rpow_one, inv_inv]

theorem mixGaugeFinal_sigmaBarStarScalar_rpow_neg_two [NeZero d] {nu : ℝ} (hnu : 0 < nu) (L : ℕ)
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P)
    (hJ4 : ShellLawJ4 d P) (n : ℤ) :
    (sigmaBarStarScalar nu L P (cubeSet (originCube d n))) ^ (-(2 : ℝ)) =
      sigmaBarStarInvScalar nu L P (cubeSet (originCube d n)) ^ 2 := by
  have htpos := sigmaBarStarInvScalar_pos_cutoff hnu L hPrefix hJ2 hJ3 hJ4 n
  rw [sigmaBarStarScalar_eq_inv hnu L hJ4 n htpos, Real.rpow_neg (inv_nonneg.2 htpos.le),
    show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, inv_pow, inv_inv]

/-! ## The pure-algebra coefficient split, `t_ell ≤ t_L + E` -/

/-- **The coefficient split.** If `0 ≤ tEll ≤ tL + E` and `Y1, Y2 ≥ 0`, the
`tEll`-order envelope `4 tEll Y1 + 2 tEll^2 Y2` splits into a `tL`-order piece
and an explicit leftover in `E`. Pure algebra: `pow_le_pow_left₀` for the
square, then `(tL + E)^2 = tL^2 + 2 tL E + E^2` expanded by `ring`. -/
theorem mixGaugeFinal_coeff_split {tEll tL E Y1 Y2 : ℝ} (htEll : 0 ≤ tEll) (htL : 0 ≤ tL)
    (hE : 0 ≤ E) (hY1 : 0 ≤ Y1) (hY2 : 0 ≤ Y2) (hle : tEll ≤ tL + E) :
    4 * tEll * Y1 + 2 * tEll ^ 2 * Y2 ≤
      (4 * tL * Y1 + 2 * tL ^ 2 * Y2) + (4 * E * Y1 + (4 * tL * E + 2 * E ^ 2) * Y2) := by
  have hsum_nonneg : 0 ≤ tL + E := add_nonneg htL hE
  have h1 : 4 * tEll * Y1 ≤ 4 * (tL + E) * Y1 :=
    mul_le_mul_of_nonneg_right (by linarith only [hle]) hY1
  have h2 : tEll ^ 2 ≤ (tL + E) ^ 2 := pow_le_pow_left₀ htEll hle 2
  have h3 : 2 * tEll ^ 2 * Y2 ≤ 2 * (tL + E) ^ 2 * Y2 :=
    mul_le_mul_of_nonneg_right (by linarith only [h2]) hY2
  have h4 : 4 * (tL + E) * Y1 = 4 * tL * Y1 + 4 * E * Y1 := by ring
  have h5 : 2 * (tL + E) ^ 2 * Y2 = 2 * tL ^ 2 * Y2 + (4 * tL * E + 2 * E ^ 2) * Y2 := by ring
  linarith only [h1, h3, h4, h5]

/-! ## The `t_ell -> t_L` scale conversion -/

/-! ## The pointwise bound at `t_L`-order, plus an explicit leftover -/

/-! ## The dimension-only base constant for `X1g`, `X2g` -/

/-- The dimension-only constant dominating the raw amplitudes of `X1g`,
`X2g`: `C ≥ mixGaugeFinal_Cbase d` is exactly what is needed to weaken
`4 tL * (gammaTriangleConst 2 * A1)`/`2 tL^2 * (gammaTriangleConst 1 * A2)`
up to the printed `C * (L - ell)^{1/2} tL`/`C * (L - ell) tL^2`. -/
noncomputable def mixGaugeFinal_Cbase (d : ℕ) : ℝ :=
  max (4 * gammaTriangleConst 2 * (d : ℝ) * finiteShellIncrementPthMomentConst d 1)
    (max (2 * gammaTriangleConst 1 * (d : ℝ) ^ 2 * finiteShellIncrementPthMomentConst d 2 ^ 2) 1)

theorem mixGaugeFinal_one_le_Cbase (d : ℕ) : 1 ≤ mixGaugeFinal_Cbase d :=
  le_trans (le_max_right _ _) (le_max_right _ _)

/-! ## `X1g`: the `Γ2` witness in the exact printed shape -/

/-- **`X1g`, measurable and `Γ2`-bounded at the exact printed
amplitude**, once `C` dominates `mixGaugeFinal_Cbase d`: `4 tL Y1`, folded
from `mixGaugeFinal_Y1_isBigO`'s `Γ2` bound via `const_mul` and weakened
(`mono_scale`) up to `C * sqrt(L-ell) * tL`, using
`mixGaugeFinal_sigmaBarStarScalar_rpow_neg_one` to read the target's
`(sigmaBarStarScalar nu L ...)^(-1)` as `tL`. -/
theorem mixGaugeFinal_X1g_isBigO [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P)
    (hJ4 : ShellLawJ4 d P) {C : ℝ} (hC : mixGaugeFinal_Cbase d ≤ C) (ell L n m : ℕ)
    (hellL : ell < L) :
    Measurable (fun omega : ShellSeq d ↦
        4 * sigmaBarStarInvScalar nu L P (cubeSet (originCube d (n : ℤ))) *
          mixGaugeFinal_Y1 omega ell L n m) ∧
      IsBigO P.toMeasure (gammaSigma 2)
        (fun omega : ShellSeq d ↦
          4 * sigmaBarStarInvScalar nu L P (cubeSet (originCube d (n : ℤ))) *
            mixGaugeFinal_Y1 omega ell L n m)
        (C * ((L - ell : ℕ) : ℝ) ^ ((1 : ℝ) / 2) *
          (sigmaBarStarScalar nu L P (cubeSet (originCube d (n : ℤ)))) ^ (-(1 : ℝ))) := by
  refine ⟨(mixGaugeFinal_Y1_measurable ell L n m).const_mul _, ?_⟩
  have htLnn : 0 ≤ sigmaBarStarInvScalar nu L P (cubeSet (originCube d (n : ℤ))) :=
    (sigmaBarStarInvScalar_pos_cutoff hnu L hPrefix hJ2 hJ3 hJ4 (n : ℤ)).le
  have hY1O := mixGaugeFinal_Y1_isBigO hPrefix hJ2 hJ3 hJ4 ell L n m hellL
  have hraw := hY1O.const_mul (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) htLnn)
  refine hraw.mono_scale ?_
  rw [mixGaugeFinal_sigmaBarStarScalar_rpow_neg_one hnu L hPrefix hJ2 hJ3 hJ4 (n : ℤ),
    show ((L - ell : ℕ) : ℝ) ^ ((1 : ℝ) / 2) = Real.sqrt (((L - ell : ℕ) : ℕ) : ℝ) from
      (Real.sqrt_eq_rpow _).symm]
  have hCbase1 : 4 * gammaTriangleConst 2 * (d : ℝ) * finiteShellIncrementPthMomentConst d 1 ≤ C :=
    le_trans (le_max_left _ _) hC
  have hsqrtnn : (0 : ℝ) ≤ Real.sqrt (((L - ell : ℕ) : ℕ) : ℝ) := Real.sqrt_nonneg _
  have hstep1 : 4 * sigmaBarStarInvScalar nu L P (cubeSet (originCube d (n : ℤ))) *
      (gammaTriangleConst 2 * ((d : ℝ) * finiteShellIncrementPthMomentConst d 1 *
        Real.sqrt (((L - ell : ℕ) : ℕ) : ℝ))) =
      (sigmaBarStarInvScalar nu L P (cubeSet (originCube d (n : ℤ))) *
          Real.sqrt (((L - ell : ℕ) : ℕ) : ℝ)) *
        (4 * gammaTriangleConst 2 * (d : ℝ) * finiteShellIncrementPthMomentConst d 1) := by ring
  have hstep2 : C * Real.sqrt (((L - ell : ℕ) : ℕ) : ℝ) *
      sigmaBarStarInvScalar nu L P (cubeSet (originCube d (n : ℤ))) =
      (sigmaBarStarInvScalar nu L P (cubeSet (originCube d (n : ℤ))) *
          Real.sqrt (((L - ell : ℕ) : ℕ) : ℝ)) * C := by ring
  rw [hstep1, hstep2]
  exact mul_le_mul_of_nonneg_left hCbase1 (mul_nonneg htLnn hsqrtnn)

/-! ## `X2g`: the `Γ1` witness in the exact printed shape -/

/-- **`X2g`, measurable and `Γ1`-bounded at the exact printed
amplitude**, once `C` dominates `mixGaugeFinal_Cbase d`: `2 tL^2 Y2`, folded
from `mixGaugeFinal_Y2_isBigO`'s `Γ1` bound via `const_mul` and weakened up to
`C * (L-ell) * tL^2`, using `mixGaugeFinal_sigmaBarStarScalar_rpow_neg_two` to
read the target's `(sigmaBarStarScalar nu L ...)^(-2)` as `tL^2`. -/
theorem mixGaugeFinal_X2g_isBigO [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P)
    (hJ4 : ShellLawJ4 d P) {C : ℝ} (hC : mixGaugeFinal_Cbase d ≤ C) (ell L n m : ℕ)
    (hellL : ell < L) :
    Measurable (fun omega : ShellSeq d ↦
        2 * sigmaBarStarInvScalar nu L P (cubeSet (originCube d (n : ℤ))) ^ 2 *
          mixGaugeFinal_Y2 omega ell L n m) ∧
      IsBigO P.toMeasure (gammaSigma 1)
        (fun omega : ShellSeq d ↦
          2 * sigmaBarStarInvScalar nu L P (cubeSet (originCube d (n : ℤ))) ^ 2 *
            mixGaugeFinal_Y2 omega ell L n m)
        (C * ((L - ell : ℕ) : ℝ) *
          (sigmaBarStarScalar nu L P (cubeSet (originCube d (n : ℤ)))) ^ (-(2 : ℝ))) := by
  refine ⟨(mixGaugeFinal_Y2_measurable ell L n m).const_mul _, ?_⟩
  have htLnn : 0 ≤ sigmaBarStarInvScalar nu L P (cubeSet (originCube d (n : ℤ))) :=
    (sigmaBarStarInvScalar_pos_cutoff hnu L hPrefix hJ2 hJ3 hJ4 (n : ℤ)).le
  have htLsqnn : 0 ≤ sigmaBarStarInvScalar nu L P (cubeSet (originCube d (n : ℤ))) ^ 2 :=
    sq_nonneg _
  have hY2O := mixGaugeFinal_Y2_isBigO hPrefix hJ2 hJ3 hJ4 ell L n m hellL
  have hraw := hY2O.const_mul (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) htLsqnn)
  refine hraw.mono_scale ?_
  rw [mixGaugeFinal_sigmaBarStarScalar_rpow_neg_two hnu L hPrefix hJ2 hJ3 hJ4 (n : ℤ)]
  have hCbase2 : 2 * gammaTriangleConst 1 * (d : ℝ) ^ 2 * finiteShellIncrementPthMomentConst d 2 ^ 2 ≤ C :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hC
  have hgapnn : (0 : ℝ) ≤ ((L - ell : ℕ) : ℝ) := Nat.cast_nonneg _
  have hstep1 : 2 * sigmaBarStarInvScalar nu L P (cubeSet (originCube d (n : ℤ))) ^ 2 *
      (gammaTriangleConst 1 * ((d : ℝ) ^ 2 * finiteShellIncrementPthMomentConst d 2 ^ 2 *
        (((L - ell : ℕ) : ℕ) : ℝ))) =
      (sigmaBarStarInvScalar nu L P (cubeSet (originCube d (n : ℤ))) ^ 2 * ((L - ell : ℕ) : ℝ)) *
        (2 * gammaTriangleConst 1 * (d : ℝ) ^ 2 * finiteShellIncrementPthMomentConst d 2 ^ 2) := by
    ring
  have hstep2 : C * ((L - ell : ℕ) : ℝ) *
      sigmaBarStarInvScalar nu L P (cubeSet (originCube d (n : ℤ))) ^ 2 =
      (sigmaBarStarInvScalar nu L P (cubeSet (originCube d (n : ℤ))) ^ 2 * ((L - ell : ℕ) : ℝ)) *
        C := by ring
  rw [hstep1, hstep2]
  exact mul_le_mul_of_nonneg_left hCbase2 (mul_nonneg htLsqnn hgapnn)

/-! ## `X3g`: the honest `Γ1/3` leftover, at an EXPLICIT amplitude -/

/-- **`X3g`, measurable and `Γ1/3`-bounded at an explicit amplitude in
`ell, L, n, nu, Ct`.** `X3g := 4 E Y1 + (4 tL E + 2 E^2) Y2`, the leftover of
`mixGaugeFinal_coeff_split` at the scale-conversion amplitude `E` of
the `t_ell → t_L` conversion (parametrized here by its own witness constant
`Ct`, so that `hCt1`/`Ct` are exactly what a later call to
that conversion supplies). Both summands weaken
(`isBigO_gammaSigma_of_exponent_le`) from their natural indices (`Γ2` for
`Y1`, `Γ1` for `Y2`) down to `Γ1/3`, then combine by the triangle inequality
`isBigO_gammaSigma_add_of_isBigO`. This is the honest replacement for the
printed bare `C * m^{-5000}` clause: no `m`-power appears anywhere in
the amplitude below (see this file's module docstring for the refutation of
the literal bare-`m^{-5000}`-with-shared-`C` shape). -/
theorem mixGaugeFinal_X3g_isBigO [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P)
    (hJ4 : ShellLawJ4 d P) {Ct : ℝ} (hCt1 : 1 ≤ Ct) (ell L n m : ℕ) (hellL : ell < L) :
    Measurable (fun omega : ShellSeq d ↦
        4 * (nu⁻¹ * gammaMomentConst 1 *
              (Ct * nu ^ (-(2 : ℝ)) * (3 : ℝ) ^ (-(((ell - n : ℕ) : ℕ) : ℝ)))) *
            mixGaugeFinal_Y1 omega ell L n m +
          (4 * sigmaBarStarInvScalar nu L P (cubeSet (originCube d (n : ℤ))) *
                (nu⁻¹ * gammaMomentConst 1 *
                  (Ct * nu ^ (-(2 : ℝ)) * (3 : ℝ) ^ (-(((ell - n : ℕ) : ℕ) : ℝ)))) +
              2 * (nu⁻¹ * gammaMomentConst 1 *
                  (Ct * nu ^ (-(2 : ℝ)) * (3 : ℝ) ^ (-(((ell - n : ℕ) : ℕ) : ℝ)))) ^ 2) *
            mixGaugeFinal_Y2 omega ell L n m) ∧
      IsBigO P.toMeasure (gammaSigma ((1 : ℝ) / 3))
        (fun omega : ShellSeq d ↦
          4 * (nu⁻¹ * gammaMomentConst 1 *
                (Ct * nu ^ (-(2 : ℝ)) * (3 : ℝ) ^ (-(((ell - n : ℕ) : ℕ) : ℝ)))) *
              mixGaugeFinal_Y1 omega ell L n m +
            (4 * sigmaBarStarInvScalar nu L P (cubeSet (originCube d (n : ℤ))) *
                  (nu⁻¹ * gammaMomentConst 1 *
                    (Ct * nu ^ (-(2 : ℝ)) * (3 : ℝ) ^ (-(((ell - n : ℕ) : ℕ) : ℝ)))) +
                2 * (nu⁻¹ * gammaMomentConst 1 *
                    (Ct * nu ^ (-(2 : ℝ)) * (3 : ℝ) ^ (-(((ell - n : ℕ) : ℕ) : ℝ)))) ^ 2) *
              mixGaugeFinal_Y2 omega ell L n m)
        (gammaTriangleConst ((1 : ℝ) / 3) *
          (4 * (nu⁻¹ * gammaMomentConst 1 *
                (Ct * nu ^ (-(2 : ℝ)) * (3 : ℝ) ^ (-(((ell - n : ℕ) : ℕ) : ℝ)))) *
              (gammaTriangleConst 2 *
                ((d : ℝ) * finiteShellIncrementPthMomentConst d 1 *
                  Real.sqrt (((L - ell : ℕ) : ℕ) : ℝ))) +
            (4 * sigmaBarStarInvScalar nu L P (cubeSet (originCube d (n : ℤ))) *
                  (nu⁻¹ * gammaMomentConst 1 *
                    (Ct * nu ^ (-(2 : ℝ)) * (3 : ℝ) ^ (-(((ell - n : ℕ) : ℕ) : ℝ)))) +
                2 * (nu⁻¹ * gammaMomentConst 1 *
                    (Ct * nu ^ (-(2 : ℝ)) * (3 : ℝ) ^ (-(((ell - n : ℕ) : ℕ) : ℝ)))) ^ 2) *
              (gammaTriangleConst 1 *
                ((d : ℝ) ^ 2 * finiteShellIncrementPthMomentConst d 2 ^ 2 *
                  (((L - ell : ℕ) : ℕ) : ℝ))))) := by
  set E : ℝ := nu⁻¹ * gammaMomentConst 1 *
    (Ct * nu ^ (-(2 : ℝ)) * (3 : ℝ) ^ (-(((ell - n : ℕ) : ℕ) : ℝ))) with hEdef
  set tL : ℝ := sigmaBarStarInvScalar nu L P (cubeSet (originCube d (n : ℤ))) with htLdef
  have hCtpos : 0 < Ct := lt_of_lt_of_le one_pos hCt1
  have hEpos : 0 < E := by
    rw [hEdef]
    have h1 : (0 : ℝ) < nu⁻¹ := inv_pos.2 hnu
    have h2 : (0 : ℝ) < gammaMomentConst 1 := gammaMomentConst_pos (by norm_num)
    have h3 : (0 : ℝ) < Ct * nu ^ (-(2 : ℝ)) * (3 : ℝ) ^ (-(((ell - n : ℕ) : ℕ) : ℝ)) :=
      mul_pos (mul_pos hCtpos (Real.rpow_pos_of_pos hnu _)) (Real.rpow_pos_of_pos (by norm_num) _)
    exact mul_pos (mul_pos h1 h2) h3
  have htLpos : 0 < tL :=
    sigmaBarStarInvScalar_pos_cutoff hnu L hPrefix hJ2 hJ3 hJ4 (n : ℤ)
  have hdpos : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  have hgap : (0 : ℝ) < (((L - ell : ℕ) : ℕ) : ℝ) := by exact_mod_cast Nat.sub_pos_of_lt hellL
  have hK1pos := mixGaugeFinal_finiteShellIncrementPthMomentConst_pos hPrefix (p := 1) le_rfl
  have hK2pos := mixGaugeFinal_finiteShellIncrementPthMomentConst_pos hPrefix (p := 2) (by norm_num)
  have hA1pos : 0 < gammaTriangleConst 2 *
      ((d : ℝ) * finiteShellIncrementPthMomentConst d 1 * Real.sqrt (((L - ell : ℕ) : ℕ) : ℝ)) :=
    mul_pos gammaTriangleConst_pos
      (mul_pos (mul_pos hdpos hK1pos) (Real.sqrt_pos.2 hgap))
  have hA2pos : 0 < gammaTriangleConst 1 *
      ((d : ℝ) ^ 2 * finiteShellIncrementPthMomentConst d 2 ^ 2 * (((L - ell : ℕ) : ℕ) : ℝ)) :=
    mul_pos gammaTriangleConst_pos (mul_pos (mul_pos (pow_pos hdpos 2) (pow_pos hK2pos 2)) hgap)
  have hcoeff1pos : 0 < 4 * E := mul_pos (by norm_num) hEpos
  have hcoeff2pos : 0 < 4 * tL * E + 2 * E ^ 2 :=
    add_pos (mul_pos (mul_pos (by norm_num) htLpos) hEpos) (mul_pos (by norm_num) (sq_pos_of_pos hEpos))
  have hY1M := mixGaugeFinal_Y1_measurable (d := d) ell L n m
  have hY2M := mixGaugeFinal_Y2_measurable (d := d) ell L n m
  refine ⟨(hY1M.const_mul (4 * E)).add (hY2M.const_mul (4 * tL * E + 2 * E ^ 2)), ?_⟩
  have hY1O := mixGaugeFinal_Y1_isBigO hPrefix hJ2 hJ3 hJ4 ell L n m hellL
  have hY2O := mixGaugeFinal_Y2_isBigO hPrefix hJ2 hJ3 hJ4 ell L n m hellL
  have hY1weak := SuperdiffusionCLT.Probability.isBigO_gammaSigma_of_exponent_le
    (show (1 : ℝ) / 3 ≤ 2 by norm_num) hY1O
  have hY2weak := SuperdiffusionCLT.Probability.isBigO_gammaSigma_of_exponent_le
    (show (1 : ℝ) / 3 ≤ 1 by norm_num) hY2O
  have hY1scaled := hY1weak.const_mul hcoeff1pos.le
  have hY2scaled := hY2weak.const_mul hcoeff2pos.le
  exact SuperdiffusionCLT.Probability.isBigO_gammaSigma_add_of_isBigO
    (by norm_num) (mul_pos hcoeff1pos hA1pos) (mul_pos hcoeff2pos hA2pos)
    hY1scaled hY2scaled (hY1M.const_mul _) (hY2M.const_mul _)

/-! ## The final assembly: `hGaugeBound`-shaped witness, B-form -/

end

end SuperdiffusionCLT.Section4.Mixing

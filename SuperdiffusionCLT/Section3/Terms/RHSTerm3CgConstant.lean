/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.RHSTerm3CgCerr

/-!
# `hCgConstant` of the final term-3 statements: a windowed bound

`hCgConstant`, exactly as it appears as a binder of the final term-3 statements
(see `RHSTerm3Statement.lean`), asks for a single `d`-only constant `Cerr` with

`cgBoundConst (cgBoundAmpP d P S w) (cgBoundAmpW nu S) (bEllipConst d) ≤ Cerr`

for *every* admissible `nu, P, S, e, delta, etaL, w` (the end of the proof of
`e.RHS.term3.A` in the paper). Unfolding the definition of `cgBoundConst`,

`cgBoundConst (cgBoundAmpP d P S w) (cgBoundAmpW nu S) (bEllipConst d)
  = 3 * (cgPoincareCarrier d P S w)^(1/4) * 3^(S.ellPrime - coarseBlockScale d S)
      * nu^(1/2) * bEllipConst d`,

where `cgPoincareCarrier` is the coarse-pair average of `E|Δ(cube-mean ∇w)|⁴`
and `bEllipConst d` is a genuine `d`-only, scale-free scalar.

The only available bound on `cgPoincareCarrier` is `cgCerr_fourth_root_window`, which
carries the regularity-window loss `(1 + S.h)^(1/2)` (see
`Frozen/Section3/WBasicRegbounds.lean`: the honest amplitude loses the window factor
`√(1+h)`, because the printed proof's route to the Hessian clause of `e.nablaw.Lt` is a
union bound over the `S.h` intermediate shells; this is a correction of the printed text,
see `ERRATA.md`). No window-free alternative is available anywhere in the tree, and no
genuine unboundedness witness for the raw `hCgConstant` statement is available either
(the window factor above only shows that the *current proof
technique's* upper bound is unbounded in `S.h`, not that the true quantity is). So
neither `hCgConstant` verbatim nor its negation is proved here; instead this file
proves it with the loss made explicit.

## Main results

* `cgConstant_windowed`: `hCgConstant` with `Cerr` replaced by
  `Cerr * (S.LPrime)^2 * nu^(-3/2)` — the shape the right side has slack
  for, since `1 + S.h ≤ S.LPrime` (`S.ellPrime_add_h`, `ScalesOrdering.m_lt_LPrime`)
  and `nu ≤ 1` absorb the window loss into already-present polynomial room.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Terms

/-- The window factor `(1 + S.h)^(1/2)` fits inside the polynomial envelope
`S.LPrime^2 * nu^(-3/2)`: `1 + S.h ≤ S.LPrime` (from `S.ellPrime_add_h` and
`S.m < S.LPrime`), so `(1+S.h)^(1/2) ≤ S.LPrime^(1/2) ≤ S.LPrime ≤ S.LPrime^2`,
and `nu^(-3/2) ≥ 1` since `0 < nu ≤ 1`. -/
private theorem cgConstant_window_poly_bound {nu : ℝ} (hnu : 0 < nu) (hnu1 : nu ≤ 1)
    (S : SuperdiffusionCLT.Section3.Setup.ScaleSelection)
    (hS : SuperdiffusionCLT.Section3.Setup.ScalesOrdering S) :
    (1 + (S.h : ℝ)) ^ ((1 : ℝ) / 2) ≤
      ((S.LPrime : ℕ) : ℝ) ^ (2 : ℕ) * nu ^ (-((3 : ℝ) / 2)) := by
  have hnat : 1 + S.h ≤ S.LPrime := by
    have h1 := S.ellPrime_add_h
    have h2 := hS.m_lt_LPrime
    omega
  have hLP1 : (1 : ℝ) ≤ ((S.LPrime : ℕ) : ℝ) := by
    exact_mod_cast (show 1 ≤ S.LPrime by omega)
  have hcast : 1 + (S.h : ℝ) ≤ ((S.LPrime : ℕ) : ℝ) := by exact_mod_cast hnat
  have step1 : (1 + (S.h : ℝ)) ^ ((1 : ℝ) / 2) ≤ ((S.LPrime : ℕ) : ℝ) ^ ((1 : ℝ) / 2) :=
    Real.rpow_le_rpow (by positivity) hcast (by norm_num)
  have step2 : ((S.LPrime : ℕ) : ℝ) ^ ((1 : ℝ) / 2) ≤ ((S.LPrime : ℕ) : ℝ) := by
    calc ((S.LPrime : ℕ) : ℝ) ^ ((1 : ℝ) / 2) ≤ ((S.LPrime : ℕ) : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hLP1 (by norm_num)
      _ = ((S.LPrime : ℕ) : ℝ) := Real.rpow_one _
  have step3 : ((S.LPrime : ℕ) : ℝ) ≤ ((S.LPrime : ℕ) : ℝ) ^ (2 : ℕ) := by
    have hLnn : (0 : ℝ) ≤ ((S.LPrime : ℕ) : ℝ) := by linarith only [hLP1]
    have h := mul_le_mul_of_nonneg_left hLP1 hLnn
    calc ((S.LPrime : ℕ) : ℝ) = ((S.LPrime : ℕ) : ℝ) * 1 := (mul_one _).symm
      _ ≤ ((S.LPrime : ℕ) : ℝ) * ((S.LPrime : ℕ) : ℝ) := h
      _ = ((S.LPrime : ℕ) : ℝ) ^ (2 : ℕ) := by ring
  have step4 : (1 : ℝ) ≤ nu ^ (-((3 : ℝ) / 2)) := by
    have h := Real.rpow_le_rpow_of_exponent_ge hnu hnu1 (show -((3 : ℝ) / 2) ≤ 0 by norm_num)
    rwa [Real.rpow_zero] at h
  have hLsq_nonneg : (0 : ℝ) ≤ ((S.LPrime : ℕ) : ℝ) ^ (2 : ℕ) := by positivity
  calc (1 + (S.h : ℝ)) ^ ((1 : ℝ) / 2)
      ≤ ((S.LPrime : ℕ) : ℝ) ^ ((1 : ℝ) / 2) := step1
    _ ≤ ((S.LPrime : ℕ) : ℝ) := step2
    _ ≤ ((S.LPrime : ℕ) : ℝ) ^ (2 : ℕ) := step3
    _ = ((S.LPrime : ℕ) : ℝ) ^ (2 : ℕ) * 1 := (mul_one _).symm
    _ ≤ ((S.LPrime : ℕ) : ℝ) ^ (2 : ℕ) * nu ^ (-((3 : ℝ) / 2)) :=
        mul_le_mul_of_nonneg_left step4 hLsq_nonneg

/-- **`hCgConstant` with an explicit polynomial window loss.** Exactly the
binder `hCgConstant` of the final term-3 statements, with `Cerr`
replaced by `Cerr * S.LPrime^2 * nu^(-3/2)`: the polynomial envelope the right side
has slack for (`2 * S.h ≤ S.m < S.LPrime`), so this closes any argument built on the
same telescope with a windowed consumer in place of the window-free `hCgConstant`. -/
theorem cgConstant_windowed (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    ∃ Cerr : ℝ, ∀ (nu : ℝ) (_hnu : 0 < nu) (_hnu1 : nu ≤ 1)
        (P : MeasureTheory.ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
        (_hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
        (_hJ1V2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P)
        (_hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P)
        (_hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P)
        (_hJ4 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P)
        (S : SuperdiffusionCLT.Section3.Setup.ScaleSelection)
        (_hSorder : SuperdiffusionCLT.Section3.Setup.ScalesOrdering S)
        (_hTwoHLeM : 2 * S.h ≤ S.m) (_hHundredALeH : 100 * S.a ≤ S.h)
        (_hWindowVsOffset : S.h + 1 ≤ 3 ^ S.a)
        (_hOffsetLower :
          (8056 / Real.log 3) * Real.log (nu⁻¹ * ((S.L : ℕ) : ℝ)) ≤ ((S.a : ℕ) : ℝ))
        (e : Homogenization.Vec d) (_he : Homogenization.vecNormSq e = 1)
        (delta etaL : ℝ) (_hdelta : 0 ≤ delta) (_hetaL : 0 ≤ etaL)
        (w : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d →
          Homogenization.H10Function (Homogenization.openCubeSet (Homogenization.originCube d (S.m : ℤ))))
        (_hw : ∀ omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d,
          SuperdiffusionCLT.Section3.Setup.IsDirichletResponse
            omega S.LPrime S.ellPrime S.m
            (SuperdiffusionCLT.Section3.Setup.testVector nu S.LPrime P S.n e) (w omega)),
      cgBoundConst (cgBoundAmpP d P S w) (cgBoundAmpW nu S) (bEllipConst d) ≤
        Cerr * ((S.LPrime : ℕ) : ℝ) ^ (2 : ℕ) * nu ^ (-((3 : ℝ) / 2)) := by
  obtain ⟨C, _hC, hbound⟩ := cgCerr_fourth_root_window d hd
  have hbE := bEllipConst_nonneg d
  refine ⟨3 * C * bEllipConst d, ?_⟩
  intro nu hnu hnu1 P hPrefix hJ1V2 hJ2 hJ3 hJ4 S hSorder _hTwoHLeM _hHundredALeH
    _hWindowVsOffset _hOffsetLower e he _delta _etaL _hdelta _hetaL w hw
  have hpoin := hbound hnu hnu1 hPrefix hJ1V2 hJ2 hJ3 hJ4 S hSorder he w hw
  -- hpoin : cgPoincareCarrier d P S w ^ (1/4) ≤
  --   C * (1 + S.h)^(1/2) * 3^(coarseBlockScale d S - S.ellPrime) * nu^(-(1/2))
  have h3pos : (0 : ℝ) < 3 := by norm_num
  have hfac_nonneg : (0 : ℝ) ≤ (3 : ℝ) ^ (-((coarseBlockScale d S : ℕ) : ℝ)) *
      ((3 : ℝ) ^ ((S.ellPrime : ℕ) : ℝ) * nu ^ ((1 : ℝ) / 2)) :=
    mul_nonneg (Real.rpow_nonneg (by norm_num) _)
      (mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg hnu.le _))
  have hstep := mul_le_mul_of_nonneg_right hpoin hfac_nonneg
  have hcombine3 : (3 : ℝ) ^ (((coarseBlockScale d S : ℕ) : ℝ) - ((S.ellPrime : ℕ) : ℝ)) *
      (3 : ℝ) ^ (-((coarseBlockScale d S : ℕ) : ℝ)) * (3 : ℝ) ^ ((S.ellPrime : ℕ) : ℝ) = 1 := by
    rw [← Real.rpow_add h3pos, ← Real.rpow_add h3pos,
      show (((coarseBlockScale d S : ℕ) : ℝ) - ((S.ellPrime : ℕ) : ℝ)) +
          (-((coarseBlockScale d S : ℕ) : ℝ)) + ((S.ellPrime : ℕ) : ℝ) = 0 by ring,
      Real.rpow_zero]
  have hnucombine : nu ^ (-(1 / 2 : ℝ)) * nu ^ ((1 : ℝ) / 2) = 1 := by
    rw [← Real.rpow_add hnu]; norm_num
  have hrhs_eq : C * (1 + (S.h : ℝ)) ^ ((1 : ℝ) / 2) *
      (3 : ℝ) ^ (((coarseBlockScale d S : ℕ) : ℝ) - ((S.ellPrime : ℕ) : ℝ)) *
      nu ^ (-(1 / 2 : ℝ)) *
      ((3 : ℝ) ^ (-((coarseBlockScale d S : ℕ) : ℝ)) *
        ((3 : ℝ) ^ ((S.ellPrime : ℕ) : ℝ) * nu ^ ((1 : ℝ) / 2))) =
      C * (1 + (S.h : ℝ)) ^ ((1 : ℝ) / 2) := by
    have e1 : C * (1 + (S.h : ℝ)) ^ ((1 : ℝ) / 2) *
        (3 : ℝ) ^ (((coarseBlockScale d S : ℕ) : ℝ) - ((S.ellPrime : ℕ) : ℝ)) *
        nu ^ (-(1 / 2 : ℝ)) *
        ((3 : ℝ) ^ (-((coarseBlockScale d S : ℕ) : ℝ)) *
          ((3 : ℝ) ^ ((S.ellPrime : ℕ) : ℝ) * nu ^ ((1 : ℝ) / 2))) =
        C * (1 + (S.h : ℝ)) ^ ((1 : ℝ) / 2) *
          ((3 : ℝ) ^ (((coarseBlockScale d S : ℕ) : ℝ) - ((S.ellPrime : ℕ) : ℝ)) *
            (3 : ℝ) ^ (-((coarseBlockScale d S : ℕ) : ℝ)) * (3 : ℝ) ^ ((S.ellPrime : ℕ) : ℝ)) *
          (nu ^ (-(1 / 2 : ℝ)) * nu ^ ((1 : ℝ) / 2)) := by ring
    rw [e1, hcombine3, hnucombine]
    ring
  rw [show C * (1 + (S.h : ℝ)) ^ ((1 : ℝ) / 2) *
        (3 : ℝ) ^ (((coarseBlockScale d S : ℕ) : ℝ) - ((S.ellPrime : ℕ) : ℝ)) *
        nu ^ (-(1 / 2 : ℝ)) *
        ((3 : ℝ) ^ (-((coarseBlockScale d S : ℕ) : ℝ)) *
          ((3 : ℝ) ^ ((S.ellPrime : ℕ) : ℝ) * nu ^ ((1 : ℝ) / 2))) =
      C * (1 + (S.h : ℝ)) ^ ((1 : ℝ) / 2) from hrhs_eq] at hstep
  -- hstep : cgPoincareCarrier d P S w ^ (1/4) *
  --   (3^(-(coarseBlockScale d S)) * (3^(S.ellPrime) * nu^(1/2))) ≤ C * (1+S.h)^(1/2)
  have hpoly := cgConstant_window_poly_bound hnu hnu1 S hSorder
  have hCb_nonneg : (0 : ℝ) ≤ 3 * bEllipConst d := by positivity
  have hfinal1 : 3 * bEllipConst d *
      (cgPoincareCarrier d P S w ^ ((1 : ℝ) / 4) *
        ((3 : ℝ) ^ (-((coarseBlockScale d S : ℕ) : ℝ)) *
          ((3 : ℝ) ^ ((S.ellPrime : ℕ) : ℝ) * nu ^ ((1 : ℝ) / 2)))) ≤
      3 * bEllipConst d * (C * (1 + (S.h : ℝ)) ^ ((1 : ℝ) / 2)) :=
    mul_le_mul_of_nonneg_left hstep hCb_nonneg
  have hC3b_nonneg : (0 : ℝ) ≤ 3 * bEllipConst d * C := by positivity
  have hfinal2 : 3 * bEllipConst d * (C * (1 + (S.h : ℝ)) ^ ((1 : ℝ) / 2)) ≤
      3 * bEllipConst d * (C * (((S.LPrime : ℕ) : ℝ) ^ (2 : ℕ) * nu ^ (-((3 : ℝ) / 2)))) := by
    have h := mul_le_mul_of_nonneg_left hpoly hC3b_nonneg
    calc 3 * bEllipConst d * (C * (1 + (S.h : ℝ)) ^ ((1 : ℝ) / 2))
        = 3 * bEllipConst d * C * (1 + (S.h : ℝ)) ^ ((1 : ℝ) / 2) := by ring
      _ ≤ 3 * bEllipConst d * C * (((S.LPrime : ℕ) : ℝ) ^ (2 : ℕ) * nu ^ (-((3 : ℝ) / 2))) := h
      _ = 3 * bEllipConst d * (C * (((S.LPrime : ℕ) : ℝ) ^ (2 : ℕ) * nu ^ (-((3 : ℝ) / 2)))) := by
          ring
  have hgoal_eq : cgBoundConst (cgBoundAmpP d P S w) (cgBoundAmpW nu S) (bEllipConst d) =
      3 * bEllipConst d *
        (cgPoincareCarrier d P S w ^ ((1 : ℝ) / 4) *
          ((3 : ℝ) ^ (-((coarseBlockScale d S : ℕ) : ℝ)) *
            ((3 : ℝ) ^ ((S.ellPrime : ℕ) : ℝ) * nu ^ ((1 : ℝ) / 2)))) := by
    unfold cgBoundConst cgBoundAmpP cgBoundAmpW
    ring
  have hgoal_eq2 : 3 * C * bEllipConst d * ((S.LPrime : ℕ) : ℝ) ^ (2 : ℕ) *
      nu ^ (-((3 : ℝ) / 2)) =
      3 * bEllipConst d * (C * (((S.LPrime : ℕ) : ℝ) ^ (2 : ℕ) * nu ^ (-((3 : ℝ) / 2)))) := by
    ring
  rw [hgoal_eq, hgoal_eq2]
  exact hfinal1.trans hfinal2

end SuperdiffusionCLT.Section3.Terms

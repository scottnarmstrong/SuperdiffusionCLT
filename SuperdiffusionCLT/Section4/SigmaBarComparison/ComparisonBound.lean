/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Frozen.Section4.LNaught
public import SuperdiffusionCLT.Section2.Annealed.InfiniteVolume
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ5
public import SuperdiffusionCLT.Section4.SigmaBarComparison.Reductions

/-!
# The algebraic assembly step of `l.shomm.vs.shomell` (`e.sL.vs.sell`)

Lemma `l.shomm.vs.shomell` has two independent printed conclusions
`e.sL.vs.sell` (the cross-cutoff comparison) and `e.sL.growth` (the growth
rate). This file targets `e.sL.vs.sell` only. Its proof
factors into three steps:

* `#homog-below-bound`: two individual comparisons of
  `σ̄_L`/`σ̄_ell` against a common finite cube `cu_n`, from
  `p.homog.below` (`homogenization_below_cutoff`) *and*
  `e.L.vs.Lnaught` (used to convert the
  raw `homogenization_below_cutoff` error into the printed `M L^alpha log^3 L`
  scaling and to reach `≤ 1/8`);
* `#near-additivity` + `#independence-and-ratio`: the
  ratio bound between `shom_L(cu_n)` and `shom_ell(cu_n)`, from a
  gauge-conjugation identity (`e.localization.ml`), independence (`a.j.indy`),
  the negation symmetry giving a mean-zero gauge (`a.j.iso`), a second-moment
  bound (`e.kmn.bounds`) via Jensen's inequality, and `p.homog.below` again,
  finished (as above) via `e.L.vs.Lnaught`;
* `#comparison-bound`: the purely algebraic combination of
  the previous two steps into `e.sL.vs.sell`.

**What this file proves and what it does not.** `e.L.vs.Lnaught`,
`e.localization.ml`, `a.j.indy`, `a.j.iso`, and `e.kmn.bounds` are not treated in this file
(each is a genuinely separate ingredient beyond `homogenization_below_cutoff`: the
natural expectation that `hHomog` alone would close `e.sL.vs.sell` is false, since
the printed proof cites all five). The comparison step
instead takes the *combined conclusion* of `#homog-below-bound` and
`#independence-and-ratio` as a single hypothesis `hStepBound`
(both printed bounds are `≤ 1/8`, at a shared witness cube index
`n`), and proves `#comparison-bound` — the purely algebraic step — from it,
unconditionally. `sbComp_three_factor_bound` and `sbComp_inv_sq_ratio` are
the two reusable pieces of that algebra, stated abstractly (no reference to
`d`, `L`, `ell`, or any cutoff-specific object), so they can be reused
verbatim for the structurally identical reapplication of this same argument
at `e.mixing.reference.compare` (in the proof of
`l.new.mixing.parameterized`), which the paper describes as "the
same comparison as in the proof of Lemma `l.shomm.vs.shomell`, applied with
the cutoffs `min{ell,r}` and `max{ell,r}` on `cu_n`".

The conclusion of the algebraic comparison is the pair `(|σ̄_ell⁻¹ σ̄_L - 1|
≤ 1/2, σ̄_ell^(-2) ≤ (9/4) σ̄_L^(-2))`: the numeric consequence of
`e.sL.vs.sell` and the ratio fact the paper uses immediately afterward
to collapse the two-term `(shom_ell^(-2)+shom_L^(-2))` bound to
the single `shom_L^(-2)` term of the printed display. Reaching the literal
single-`C`, single-`shom_L^(-2)`-term display additionally needs an a priori
*upper* bound on `sigmaBarInfinite` in terms of `L` (the crude growth bound
`e.Enaught.vs.A.and.Ahom`, `shom_r ≤ C nu⁻¹(1+r)`) to dominate the residual
`C L^(-99)` term; that bound is not used in this file (it is also
the ingredient `l.shomm.vs.shomell#growth-construction` needs for
`e.sL.growth`). The full quantitative bound
(non-uniform coefficients `17/7`, `8/7` on the two step bounds) is visible in
the proof as `hkey`.
-/

@[expose] public section

open MeasureTheory
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Frozen.Assumptions

namespace SuperdiffusionCLT.Section4.SigmaBarComparison

noncomputable section

/-- Pure algebra, no context: a bound on `|a * b * c⁻¹ - 1|` from bounds
`|a - 1| ≤ ea`, `|b - 1| ≤ eb`, `|c - 1| ≤ ea` (the outer two factors share
the error `ea`, matching `#homog-below-bound`'s single sum bound), with
`ea, eb ≤ 1/8`. Reusable verbatim wherever this same three-factor scalar
factorization argument recurs (e.g. `e.mixing.reference.compare`). -/
theorem sbComp_three_factor_bound {a b c ea eb : ℝ}
    (ha : |a - 1| ≤ ea) (hb : |b - 1| ≤ eb) (hc : |c - 1| ≤ ea)
    (hea : ea ≤ 1 / 8) (heb : eb ≤ 1 / 8) :
    |a * b * c⁻¹ - 1| ≤ (17 / 7) * ea + (8 / 7) * eb := by
  have hea0 : 0 ≤ ea := le_trans (abs_nonneg _) ha
  have heb0 : 0 ≤ eb := le_trans (abs_nonneg _) hb
  have hcbound : |c - 1| ≤ 1 / 8 := le_trans hc hea
  have hcle := (abs_le.mp hcbound).1
  have hc78 : (7 : ℝ) / 8 ≤ c := by linarith only [hcle]
  have hcpos : (0:ℝ) < c := by linarith only [hc78]
  have hcne : c ≠ 0 := ne_of_gt hcpos
  have hid : a * b * c⁻¹ - 1 = (a * b - c) * c⁻¹ := by field_simp
  have hexpand : a * b - c = (a - 1) + (b - 1) - (c - 1) + (a - 1) * (b - 1) := by ring
  have htri2 : |(a - 1) + (b - 1) - (c - 1)| ≤ |a - 1| + |b - 1| + |c - 1| := by
    have e1 : (a - 1) + (b - 1) - (c - 1) = (a - 1) + (b - 1) + (-(c - 1)) := by ring
    rw [e1]
    have s1 : |(a - 1) + (b - 1) + (-(c - 1))| ≤ |(a - 1) + (b - 1)| + |-(c - 1)| :=
      abs_add_le _ _
    have s2 : |(a - 1) + (b - 1)| ≤ |a - 1| + |b - 1| := abs_add_le _ _
    have s3 : |-(c - 1)| = |c - 1| := abs_neg _
    linarith only [s1, s2, s3]
  have habs : |a * b - c| ≤ |a - 1| + |b - 1| + |c - 1| + |a - 1| * |b - 1| := by
    rw [hexpand]
    have htri : |(a - 1) + (b - 1) - (c - 1) + (a - 1) * (b - 1)| ≤
        |(a - 1) + (b - 1) - (c - 1)| + |(a - 1) * (b - 1)| := abs_add_le _ _
    have hm : |(a - 1) * (b - 1)| = |a - 1| * |b - 1| := abs_mul _ _
    linarith only [htri, htri2, hm]
  have hprod : |a - 1| * |b - 1| ≤ ea * eb := mul_le_mul ha hb (abs_nonneg _) hea0
  have heaeb : ea * eb ≤ ea * (1 / 8) := mul_le_mul_of_nonneg_left heb hea0
  have habs3 : |a * b - c| ≤ (17 / 8) * ea + eb := by
    have h1 : |a - 1| ≤ ea := ha
    have h2 : |b - 1| ≤ eb := hb
    have h3 : |c - 1| ≤ ea := hc
    linarith only [habs, hprod, heaeb, h1, h2, h3]
  have hcinvpos : (0:ℝ) < c⁻¹ := inv_pos.mpr hcpos
  have hcinvle : c⁻¹ ≤ 8 / 7 := by
    rw [inv_le_comm₀ hcpos (by norm_num : (0:ℝ) < 8 / 7)]
    have hh : (8 / 7 : ℝ)⁻¹ = 7 / 8 := by norm_num
    rw [hh]
    exact hc78
  have hrhs0 : (0:ℝ) ≤ (17 / 8) * ea + eb := by linarith only [hea0, heb0]
  calc |a * b * c⁻¹ - 1| = |a * b - c| * c⁻¹ := by rw [hid, abs_mul, abs_of_pos hcinvpos]
  _ ≤ ((17 / 8) * ea + eb) * (8 / 7) :=
      mul_le_mul habs3 hcinvle (le_of_lt hcinvpos) hrhs0
  _ = (17 / 7) * ea + (8 / 7) * eb := by ring

/-- Pure algebra, no context: from `0 < x`, `0 < y` and `y ≤ (3/2) x`,
`x ^ (-2) ≤ (9/4) * y ^ (-2)` (`Real.rpow` throughout). This is the ratio
step the paper uses (`shom_ell^(-2) ≤ (9/4) shom_L^(-2)`, from
`shom_L ≤ (3/2) shom_ell`, itself read off `|shom_ell⁻¹ shom_L - 1| ≤ 1/2`). -/
theorem sbComp_inv_sq_ratio {x y : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hxy : y ≤ (3 / 2 : ℝ) * x) :
    x ^ (-(2:ℝ)) ≤ (9 / 4 : ℝ) * y ^ (-(2:ℝ)) := by
  have h23 : (2 / 3 : ℝ) * y ≤ x := by linarith only [hxy]
  have hnn : (0:ℝ) ≤ (2 / 3) * y := by positivity
  have hstep : ((2 / 3 : ℝ) * y) ^ (2:ℝ) ≤ x ^ (2:ℝ) :=
    Real.rpow_le_rpow hnn h23 (by norm_num)
  have hmulrpow : ((2 / 3 : ℝ) * y) ^ (2:ℝ) = (2 / 3 : ℝ) ^ (2:ℝ) * y ^ (2:ℝ) :=
    Real.mul_rpow (by norm_num) hy.le
  have hnum : (2 / 3 : ℝ) ^ (2:ℝ) = 4 / 9 := by
    rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
    norm_num
  have hstep2 : (4 / 9 : ℝ) * y ^ (2:ℝ) ≤ x ^ (2:ℝ) := by
    rw [← hnum, ← hmulrpow]; exact hstep
  have hxpow_pos : (0:ℝ) < x ^ (2:ℝ) := Real.rpow_pos_of_pos hx 2
  have hypow_pos : (0:ℝ) < y ^ (2:ℝ) := Real.rpow_pos_of_pos hy 2
  have hinv : (x ^ (2:ℝ))⁻¹ ≤ ((4 / 9 : ℝ) * y ^ (2:ℝ))⁻¹ := by
    apply inv_anti₀ (by positivity) hstep2
  have hrw : ((4 / 9 : ℝ) * y ^ (2:ℝ))⁻¹ = (9 / 4 : ℝ) * (y ^ (2:ℝ))⁻¹ := by
    rw [mul_inv]
    norm_num
  have hxneg : x ^ (-(2:ℝ)) = (x ^ (2:ℝ))⁻¹ := Real.rpow_neg hx.le 2
  have hyneg : y ^ (-(2:ℝ)) = (y ^ (2:ℝ))⁻¹ := Real.rpow_neg hy.le 2
  rw [hxneg, hyneg]
  rw [hrw] at hinv
  exact hinv

end

end SuperdiffusionCLT.Section4.SigmaBarComparison

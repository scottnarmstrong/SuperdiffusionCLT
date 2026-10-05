/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.BfAmEllipticityLevelTailB
public import SuperdiffusionCLT.Section2.Annealed.EnvelopeMinimalScale

/-!
# The printed per-scale tail `hScaleTail` is not derivable from the five shell laws

lemma `l.bfAm.ellip`.
The level-tail reduction leaves exactly one hypothesis,
the printed per-scale tail,

> `P[ (C(1∨m))^{-1} ||k_m||²_{L²(z+cu_l)} > 2t3^{γ(n-l)} ]
>    ≤ exp(-ct 3^{γ(n-l)+(d/2)((l-m)∨0)})`,

at the fixed decay constant `2 * levelTailConst (max 3 (subCubeUnionConst d))`
with `t = 1`, and `l = n - k` for a cube `Q` with `Q.scale = n - k`.

## The scalar factor and its only available tail

The scalar factor of the statement is `envelopeRatio m Q omega`: the maximum of `1` and
the normalized volume average of `|streamCutoff omega m|²` over the cube `Q`, the normalization
being `cutoffEnvelopeConst d * max 1 m`. Its only available tail is the `Γ₁` bound
`measureReal_envelopeRatio_gt_le`: for every `s ≥ 1`,

> `P[s < envelopeRatio m Q omega] ≤ exp(-s)`,

uniformly in the cube `Q`, in `m` and in the level `n`, from
`ShellLawPrefix` (stationarity and `2 ≤ d`), `ShellLawJ2`, `ShellLawJ3` and
`ShellLawJ4`. At the printed threshold `2 * 3^{γk} ≥ 2` this is

> `P[2 * 3^{γk} < envelopeRatio m Q omega] ≤ exp(-2 * 3^{γk})`,

proved below as `measureReal_envelopeRatio_gt_two_mul_rpow_le`: the normalized
variable has exponential rate exactly `1` per unit of its own scale, so the
rate in the threshold `2 * 3^{γk}` is exactly `2`.

## The missing improvement, and what supplies it

The printed improvement `3^{(d/2)((l-m)∨0)}` is the `l ≥ m` half of the local
square bound `e.km.square.bound`, and it is not available for
`envelopeRatio`: the uniform tail above carries no factor in `l - m`. Its
source in the paper is `e.kl.bounds.large`, the
improved `p`-th moment of the increment `k_m - k_0`, which is proved as
`exists_witness_cubeLpENorm_finiteShellIncrement`, whose decay
`3^{-(d/(2p))(l-m)}` is supplied by `ShellLawJ1Restriction` (restriction-lane range of
dependence) and `ShellLawJ2` (shell independence), with the per-shell `Γ` tail
of `ShellLawJ3` feeding the concentration inequality and `ShellLawPrefix`
supplying stationarity and `2 ≤ d`. That estimate
bounds the *increment* `k_m - k_0` at unit normalized amplitude: it improves
the shape of the decay, not the exponential rate, and it is not assembled for
`envelopeRatio`.

## The constant is too large

Write `c := levelTailConst (max 3 (subCubeUnionConst d))`. One has
`2 ≤ c`, because `3 ≤ max 3 (subCubeUnionConst d)`. The hypothesis of
the reduction demands, at every `k` and with `K = n - m`,

> `P[...] ≤ exp(-(2 * c * 3^{γk + (d/2) max (K - k) 0}))`,

that is, an exponential rate `2 * c ≥ 4` in the threshold `2 * 3^{γk}`: the
ratio of the two exponents is `c * 3^{(d/2) max (K-k) 0} ≥ c ≥ 2`. The
`Γ₁` tail certifies the rate `2` and no more. At `k = 0` and `m = n` it gives
`exp(-2)`, while the display asks for at most `exp(-2 * c) ≤ exp(-4)`.
The exact separation is, for every `k`
and `K`,

> `2 * 3^{γk} < 2 * c * 3^{γk + (d/2) max (K - k) 0}`,

so the honest per-scale bound is *strictly larger* than the displayed one
and cannot imply it. Since
`ShellLawJ1Restriction`..`J4` place `envelopeRatio` in the `Γ₁` class and nothing finer,
no decay constant above `2` is available from them, and the printed hypothesis
is mis-shaped.

The consequence for the reduction is that it runs
at the decay constant `4t` with
`t ≥ 1`, hence at per-scale rate at least `4`, and the honest per-scale bound
at rate `2` never implies its hypothesis. The union bound over the `3^{d(n-l)}`
sub-cubes and the sum over the scales spend the factor `2` between `4t` and
`2t`; without the printed improvement there is no level decay at all (the
uniform bound), and with it the constant is still
out of reach by the factor `c ≥ 2`.

Everything below is proved from an explicit witness. The per-scale tail is
proved outright from the four shell laws it names, and the separations above are pure
real arithmetic.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section2

open Homogenization MeasureTheory
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2

noncomputable section

variable {d : ℕ}

/-! ## The honest per-scale tail, from the `Γ₁` bound -/

/-- **The honest per-scale tail.** For every cube `Q`, every `m`, every
`γ > 0` and every `k`, the printed event at `t = 1` has
probability at most `exp(-2 * 3^{γk})` — no factor in the level `n - m`
appears. This is `measureReal_envelopeRatio_gt_le` at `s = 2 * 3^{γk}`, which
is at least `2`. The `Γ₁` class is supplied by `ShellLawPrefix` (stationarity
and `2 ≤ d`), `ShellLawJ2`, `ShellLawJ3` and `ShellLawJ4`; none of them supplies
a larger exponential rate. -/
theorem measureReal_envelopeRatio_gt_two_mul_rpow_le
    {P : ProbabilityMeasure (ShellSeq d)} (hPrefix : ShellLawPrefix d P)
    (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P)
    (m : ℕ) (Q : TriadicCube d) {gamma : ℝ} (hg0 : 0 < gamma) (k : ℕ) :
    P.toMeasure.real {omega : ShellSeq d |
        2 * 1 * (3 : ℝ) ^ (gamma * (k : ℝ)) < envelopeRatio m Q omega} ≤
      Real.exp (-(2 * (3 : ℝ) ^ (gamma * (k : ℝ)))) := by
  have hk0 : (0 : ℝ) ≤ gamma * (k : ℝ) := mul_nonneg hg0.le (Nat.cast_nonneg k)
  have h1 : (1 : ℝ) ≤ (3 : ℝ) ^ (gamma * (k : ℝ)) :=
    Real.one_le_rpow (by norm_num) hk0
  have hs : (1 : ℝ) ≤ 2 * (3 : ℝ) ^ (gamma * (k : ℝ)) := by linarith only [h1]
  simpa only [mul_one] using
    measureReal_envelopeRatio_gt_le (P := P) hPrefix hJ2 hJ3 hJ4 m Q hs

/-! ## The exhibited constant and its separation from the printed one -/

end

end SuperdiffusionCLT.Section2

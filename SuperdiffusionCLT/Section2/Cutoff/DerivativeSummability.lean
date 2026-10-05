/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.Asymptotics.Lemmas
public import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
public import SuperdiffusionCLT.Section2.Carriers.ShellDerivLinftyNorm
public import SuperdiffusionCLT.Section2.Estimates.Stream.DerivativeConcentration

/-!
# Almost-sure summability of the shell derivative norms

The cutoff approximation lemma `l.cutoff.approximation` has as hypothesis the
pointwise `L∞` summability

> `∑_{k=0}^∞ ‖∇ j_k‖_{L∞(U)} < ∞`

and a remark in its proof records that, for every fixed bounded `U`,
this hypothesis holds almost surely by the local regularity assumption
`e.k(n).reg` (part of the marginal assumption J3) together with Borel-Cantelli.

This module proves that remark. The scale is the natural one. The J3
assumption gives, for every shell `k` and every `t ≥ 1`,

`P[‖∇ j_k‖_{L∞(cu_k)} > 3^{-k} t] ≤ exp(-t²)`,

because the weighted norm `3^k ‖∇ j_k‖_{L∞(cu_k)}` is dominated by the complete
J3 observable (`pow_mul_shellCubeDerivNorm_le_j3Observable`). Choosing
`t = 3^{k/2}` turns this into

`P[‖∇ j_k‖_{L∞(cu_k)} > 3^{-k/2}] ≤ exp(-3^k)`,

and `∑_k exp(-3^k)` converges, since `3^k ≥ k` and `∑_k exp(-k)` is a
geometric series with ratio `exp(-1) < 1`. The first Borel-Cantelli lemma
(`MeasureTheory.ae_eventually_notMem`) then says that almost surely
`‖∇ j_k‖_{L∞(cu_k)} ≤ 3^{-k/2}` for all large `k`. On a set `U` contained in
the cube `cu_m` the carrier `shellDerivLinftyNorm` is monotone in the set and
agrees with the cube carrier on `cu_k` for `k ≥ m`, so the almost-sure tail is
dominated by the geometric series `∑_k 3^{-k/2}` of ratio `3^{-1/2} < 1`, and
the finite initial segment is irrelevant to summability. This gives the final
statement `eventually_summable_shellDerivLinftyNorm`:

`∀ᵐ omega ∂P.toMeasure, Summable (fun k => shellDerivLinftyNorm U (omega k))`.

The scale `3^{-1/2}` is carried by the constant `shellDerivTailScale`, so that
the threshold `shellDerivTailScale ^ k = 3^{-k/2}` is a plain natural power of
a real constant and the comparison with the geometric series needs no real
exponent arithmetic. The remark states its claim for every fixed
bounded `U`, covering `U` by a bounded number of translates of the natural
scale `3^k` cubes, and separately records a random scale `L_U` tail bound.
The covering argument that passes from boundedness of `U` to a cube
containment is not carried out here, so the statement is phrased with the
cube-containment hypothesis `U ⊆ cu_m`; the random scale `L_U` bound is not
proved either.

## Main definitions

* `shellDerivTailScale`: the constant `3^{-1/2}` of the Borel-Cantelli
  threshold.

## Main results

* `measure_shellCubeDerivNorm_gaussian_tail`: the Gaussian tail at scale
  `3^{-k}`, the instance of the J3 tail used throughout.
* `measure_shellCubeDerivNorm_scale`: the tail at scale `3^{-k/2}`, that is
  `P[‖∇ j_k‖_{L∞(cu_k)} > 3^{-k/2}] ≤ exp(-3^k)`.
* `summable_shellDerivTailScale`, `summable_exp_neg_three_pow`: the two
  summable series of the argument.
* `eventually_shellCubeDerivNorm_le_scale`: the Borel-Cantelli conclusion.
* `openCubeSet_originCube_subset`,
  `shellDerivLinftyNorm_le_shellCubeDerivNorm_of_le`: the transport from the
  cube carrier to the `L∞(U)` carrier.
* `eventually_summable_shellDerivLinftyNorm`: the summability of
  `‖∇ j_k‖_{L∞(U)}` almost surely.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section2.Cutoff

open MeasureTheory Filter Homogenization
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Assumptions.ShellField
open SuperdiffusionCLT.Section2.Carriers
open SuperdiffusionCLT.Section2.Estimates.Stream
open scoped ENNReal

noncomputable section

variable {d : ℕ}
variable {P : ProbabilityMeasure (ShellSeq d)}

/-! ## The Gaussian tail of the cube derivative norm -/

/-- **The Gaussian tail at scale `3^{-k}`.** For every shell `k` and every
`t ≥ 1`, the marginal J3 assumption of the paper bounds the strict upper tail of the cube
derivative norm:

`P[‖∇ j_k‖_{L∞(cu_k)} > 3^{-k} t] ≤ exp(-t²)`.

Indeed the weighted norm `3^k ‖∇ j_k‖_{L∞(cu_k)}` is dominated by the complete
J3 observable (`pow_mul_shellCubeDerivNorm_le_j3Observable`), so the event on
the left is contained in the J3 tail event, whose measure is bounded by
`ShellLawJ3.gaussian_tail`. -/
theorem measure_shellCubeDerivNorm_gaussian_tail
    (hJ3 : ShellLawJ3 d P) (k : ℕ) {t : ℝ} (ht : 1 ≤ t) :
    P.toMeasure {omega : ShellSeq d |
        ((3 : ℝ) ^ k)⁻¹ * t < ShellField.shellCubeDerivNorm k (omega k)} ≤
      ENNReal.ofReal (Real.exp (-(t ^ 2))) := by
  have hpow : 0 < (3 : ℝ) ^ k := pow_pos (by norm_num) k
  have hsub : {omega : ShellSeq d |
      ((3 : ℝ) ^ k)⁻¹ * t < ShellField.shellCubeDerivNorm k (omega k)} ⊆
      {F : ShellSeq d | t < ShellField.j3Observable d k (F k)} := by
    intro omega homega
    have hk0 : (3 : ℝ) ^ k ≠ 0 := pow_ne_zero k (by norm_num)
    have h1 : (3 : ℝ) ^ k * (((3 : ℝ) ^ k)⁻¹ * t) <
        (3 : ℝ) ^ k * ShellField.shellCubeDerivNorm k (omega k) :=
      mul_lt_mul_of_pos_left homega hpow
    have h2 : t < (3 : ℝ) ^ k * ShellField.shellCubeDerivNorm k (omega k) := by
      rw [← mul_assoc, mul_inv_cancel₀ hk0, one_mul] at h1
      exact h1
    calc t < (3 : ℝ) ^ k * ShellField.shellCubeDerivNorm k (omega k) := h2
      _ ≤ ShellField.j3Observable d k (omega k) :=
        pow_mul_shellCubeDerivNorm_le_j3Observable k (omega k)
  exact (measure_mono hsub).trans (hJ3.gaussian_tail k t ht)

/-! ## The scale `3^{-1/2}` -/

/-- The scale of the almost-sure eventual bound on the cube derivative norms:
`shellDerivTailScale = 3^{-1/2}`, in manuscript notation. It is written as the
plain product `(3 : ℝ)⁻¹ * √3` so that its `k`-th power is the threshold
`3^{-k/2}` of the tail estimate `measure_shellCubeDerivNorm_scale` without real
exponent arithmetic, and the series of thresholds is a geometric series. -/
def shellDerivTailScale : ℝ := (3 : ℝ)⁻¹ * Real.sqrt 3

/-- The scale is nonnegative. -/
theorem shellDerivTailScale_nonneg : 0 ≤ shellDerivTailScale :=
  mul_nonneg (by positivity) (Real.sqrt_nonneg 3)

/-- The scale is below one, so the thresholds form a summable geometric
series. -/
theorem shellDerivTailScale_lt_one : shellDerivTailScale < 1 := by
  have h3 : Real.sqrt (3 : ℝ) < 3 :=
    (Real.sqrt_lt' (by norm_num : (0 : ℝ) < 3)).mpr (by norm_num)
  exact (inv_mul_lt_iff₀ (by norm_num : (0 : ℝ) < 3)).mpr (by linarith only [h3])

/-- The `k`-th threshold of the tail estimate `measure_shellCubeDerivNorm_scale`
is the plain power `3^{-k/2}` of the scale. -/
theorem shellDerivTailScale_pow_eq (k : ℕ) :
    shellDerivTailScale ^ k = ((3 : ℝ) ^ k)⁻¹ * (Real.sqrt 3) ^ k := by
  show ((3 : ℝ)⁻¹ * Real.sqrt 3) ^ k = _
  rw [mul_pow, inv_pow]

/-- The thresholds `3^{-k/2}` form a summable geometric series of ratio
`3^{-1/2} < 1`. -/
theorem summable_shellDerivTailScale :
    Summable (fun k : ℕ => shellDerivTailScale ^ k) :=
  summable_geometric_of_lt_one shellDerivTailScale_nonneg shellDerivTailScale_lt_one

/-- Every power of the scale is nonnegative. -/
theorem shellDerivTailScale_pow_nonneg (k : ℕ) : 0 ≤ shellDerivTailScale ^ k :=
  pow_nonneg shellDerivTailScale_nonneg k

/-- The natural powers of the base `3`, in the form needed by
`summable_exp_neg_three_pow`: the index is dominated by the power. -/
private theorem nat_cast_le_three_pow (k : ℕ) : (k : ℝ) ≤ (3 : ℝ) ^ k := by
  induction k with
  | zero => norm_num
  | succ k ih =>
      have h1 : 1 ≤ (3 : ℝ) ^ k := one_le_pow₀ (by norm_num)
      rw [Nat.cast_add_one, pow_succ]
      linarith only [ih, h1]

/-- The series `∑_k exp(-3^k)` of tail probabilities is summable: `3^k ≥ k`,
so the terms are dominated by the geometric series of ratio `exp(-1) < 1`. -/
theorem summable_exp_neg_three_pow :
    Summable (fun k : ℕ => Real.exp (-((3 : ℝ) ^ k))) := by
  have hgeo : Summable (fun k : ℕ => (Real.exp (-1 : ℝ)) ^ k) :=
    summable_geometric_of_lt_one (Real.exp_nonneg _)
      (Real.exp_lt_one_iff.mpr (by norm_num))
  refine summable_of_isBigO_nat hgeo ?_
  refine Asymptotics.IsBigO.of_bound' (Filter.Eventually.of_forall fun k => ?_)
  have hle := nat_cast_le_three_pow k
  have hkey : Real.exp (-(k : ℝ)) = (Real.exp (-1 : ℝ)) ^ k := by
    have hmul : (k : ℝ) * (-1) = -(k : ℝ) := by ring
    rw [← Real.exp_nat_mul, hmul]
  have hstep : -((3 : ℝ) ^ k) ≤ -(k : ℝ) := by linarith only [hle]
  have h1 : Real.exp (-((3 : ℝ) ^ k)) ≤ Real.exp (-(k : ℝ)) := Real.exp_le_exp.2 hstep
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _), Real.norm_eq_abs,
    abs_of_nonneg (pow_nonneg (Real.exp_nonneg _) k)]
  exact h1.trans hkey.le

/-! ## The tail at scale `3^{-k/2}` -/

/-- **The tail at scale `3^{-k/2}`.** Specializing
`measure_shellCubeDerivNorm_gaussian_tail` to `t = 3^{k/2}`, whose square is
the `k`-th power of the base `3`:

`P[‖∇ j_k‖_{L∞(cu_k)} > 3^{-k/2}] ≤ exp(-3^k)`,

the term of the summable series `∑_k exp(-3^k)`. -/
theorem measure_shellCubeDerivNorm_scale (hJ3 : ShellLawJ3 d P) (k : ℕ) :
    P.toMeasure {omega : ShellSeq d |
        shellDerivTailScale ^ k < ShellField.shellCubeDerivNorm k (omega k)} ≤
      ENNReal.ofReal (Real.exp (-((3 : ℝ) ^ k))) := by
  have h1 : 1 ≤ (Real.sqrt 3) ^ k := one_le_pow₀ (by norm_num)
  have h2 : (Real.sqrt 3) ^ k * (Real.sqrt 3) ^ k = (3 : ℝ) ^ k := by
    rw [← pow_add, ← two_mul, pow_mul, Real.sq_sqrt (by norm_num)]
  have hsq : ((Real.sqrt 3) ^ k) ^ 2 = (3 : ℝ) ^ k := by
    rw [pow_two]
    exact h2
  have hb : P.toMeasure {omega : ShellSeq d |
      ((3 : ℝ) ^ k)⁻¹ * (Real.sqrt 3) ^ k <
        ShellField.shellCubeDerivNorm k (omega k)} ≤
      ENNReal.ofReal (Real.exp (-(((Real.sqrt 3) ^ k) ^ 2))) :=
    measure_shellCubeDerivNorm_gaussian_tail hJ3 k (t := (Real.sqrt 3) ^ k) h1
  rw [hsq] at hb
  rw [shellDerivTailScale_pow_eq]
  exact hb

/-- The total measure of the tail events is finite, since it is bounded by the
real sum `∑_k exp(-3^k)`, which is finite by `summable_exp_neg_three_pow`. -/
private theorem tsum_measure_shellCubeDerivNorm_ne_top (hJ3 : ShellLawJ3 d P) :
    (∑' k : ℕ, P.toMeasure {omega : ShellSeq d |
        shellDerivTailScale ^ k < ShellField.shellCubeDerivNorm k (omega k)}) ≠ ⊤ := by
  have hle : (∑' k : ℕ, P.toMeasure {omega : ShellSeq d |
      shellDerivTailScale ^ k < ShellField.shellCubeDerivNorm k (omega k)}) ≤
      ENNReal.ofReal (∑' k : ℕ, Real.exp (-((3 : ℝ) ^ k))) := by
    calc (∑' k : ℕ, P.toMeasure {omega : ShellSeq d |
        shellDerivTailScale ^ k < ShellField.shellCubeDerivNorm k (omega k)}) ≤
        ∑' k : ℕ, ENNReal.ofReal (Real.exp (-((3 : ℝ) ^ k))) :=
          ENNReal.tsum_le_tsum fun k => measure_shellCubeDerivNorm_scale hJ3 k
      _ = ENNReal.ofReal (∑' k : ℕ, Real.exp (-((3 : ℝ) ^ k))) :=
          (ENNReal.ofReal_tsum_of_nonneg (fun _ => Real.exp_nonneg _)
            summable_exp_neg_three_pow).symm
  exact ne_of_lt (lt_of_le_of_lt hle ENNReal.ofReal_lt_top)

/-- **Borel-Cantelli: the cube derivative norms are eventually small.** Under
the J3 assumption, almost surely `‖∇ j_k‖_{L∞(cu_k)} ≤ 3^{-k/2}` for
all sufficiently large `k`. This is the first half of the remark in the proof of
`l.cutoff.approximation`. -/
theorem eventually_shellCubeDerivNorm_le_scale (hJ3 : ShellLawJ3 d P) :
    ∀ᵐ omega : ShellSeq d ∂P.toMeasure,
      ∀ᶠ k in atTop, ShellField.shellCubeDerivNorm k (omega k) ≤ shellDerivTailScale ^ k := by
  have hmem := MeasureTheory.ae_eventually_notMem
    (μ := P.toMeasure)
    (s := fun k : ℕ => {omega : ShellSeq d |
      shellDerivTailScale ^ k < ShellField.shellCubeDerivNorm k (omega k)})
    (tsum_measure_shellCubeDerivNorm_ne_top hJ3)
  filter_upwards [hmem] with omega homega
  filter_upwards [homega] with k hk
  exact le_of_not_gt hk

/-! ## From the cube carrier to the `L∞(U)` carrier -/

/-- The natural open cubes are nested: `cu_m ⊆ cu_k` whenever `m ≤ k`, because
the side length `3^m` of the smaller cube does not exceed `3^k`. -/
theorem openCubeSet_originCube_subset {m k : ℕ} (hmk : m ≤ k) :
    openCubeSet (originCube d (m : ℤ)) ⊆ openCubeSet (originCube d (k : ℤ)) := by
  intro x hx
  rw [mem_openCubeSet_originCube_iff] at hx ⊢
  have hnk : (m : ℤ) ≤ (k : ℤ) := by exact_mod_cast hmk
  have hpow : (3 : ℝ) ^ (m : ℤ) ≤ (3 : ℝ) ^ (k : ℤ) :=
    zpow_le_zpow_right₀ (by norm_num) hnk
  intro i
  obtain ⟨hlo, hhi⟩ := hx i
  constructor
  · exact lt_of_le_of_lt
      (mul_le_mul_of_nonpos_left hpow (by norm_num : -(1 / 2 : ℝ) ≤ 0)) hlo
  · exact lt_of_lt_of_le hhi
      (mul_le_mul_of_nonneg_left hpow (by norm_num : (0 : ℝ) ≤ 1 / 2))

/-- **The `L∞(U)` carrier is dominated by the cube carrier at a coarser
scale.** If `U ⊆ cu_m` and `m ≤ k`, then `‖∇ j‖_{L∞(U)} ≤ ‖∇ j‖_{L∞(cu_k)}`:
the carrier is monotone in the set (`shellDerivLinftyNorm_mono`), it agrees
with the cube carrier on the cube (`shellDerivLinftyNorm_openCubeSet`), and
the cube carrier is monotone in the scale (`shellCubeDerivNorm_mono`). -/
theorem shellDerivLinftyNorm_le_shellCubeDerivNorm_of_le
    {m k : ℕ} (hmk : m ≤ k) {U : Set (Vec d)}
    (hU : U ⊆ openCubeSet (originCube d (m : ℤ))) (j : ShellField d) :
    shellDerivLinftyNorm U j ≤ ShellField.shellCubeDerivNorm k j := by
  calc shellDerivLinftyNorm U j ≤
      shellDerivLinftyNorm (openCubeSet (originCube d (m : ℤ))) j :=
    shellDerivLinftyNorm_mono (isBounded_openCubeSet_originCube (m : ℤ)) hU j
  _ = ShellField.shellCubeDerivNorm m j := shellDerivLinftyNorm_openCubeSet m j
  _ ≤ ShellField.shellCubeDerivNorm k j := ShellField.shellCubeDerivNorm_mono hmk j

/-! ## Almost-sure summability -/

/-- **Almost-sure summability of the shell derivative norms** — the remark in
the proof of `l.cutoff.approximation`. Under the J3
assumption, if `U` is contained in a natural open cube
`cu_m`, then almost surely the series of the cutoff approximation lemma
converges:

`∀ᵐ omega ∂P.toMeasure, Summable (fun k => shellDerivLinftyNorm U (omega k))`.

Indeed, by Borel-Cantelli (`eventually_shellCubeDerivNorm_le_scale`) the cube
carriers `‖∇ j_k‖_{L∞(cu_k)}` are eventually at most `3^{-k/2}`, by
`shellDerivLinftyNorm_le_shellCubeDerivNorm_of_le` the same bound holds for
the `L∞(U)` carrier from scale `m` on, and the dominating series
`∑_k 3^{-k/2}` is geometric of ratio `3^{-1/2} < 1`
(`summable_shellDerivTailScale`); a series is unaffected by its finitely many
initial terms, which is read here through the big-O comparison
`summable_of_isBigO_nat`. -/
theorem eventually_summable_shellDerivLinftyNorm
    (hJ3 : ShellLawJ3 d P) {m : ℕ} {U : Set (Vec d)}
    (hU : U ⊆ openCubeSet (originCube d (m : ℤ))) :
    ∀ᵐ omega : ShellSeq d ∂P.toMeasure,
      Summable (fun k : ℕ => shellDerivLinftyNorm U (omega k)) := by
  have hbc := eventually_shellCubeDerivNorm_le_scale hJ3
  filter_upwards [hbc] with omega homega
  have hlin : ∀ᶠ k in atTop,
      shellDerivLinftyNorm U (omega k) ≤ ShellField.shellCubeDerivNorm k (omega k) := by
    filter_upwards [Filter.eventually_ge_atTop m] with k hk
    exact shellDerivLinftyNorm_le_shellCubeDerivNorm_of_le hk hU (omega k)
  have hbound : ∀ᶠ k in atTop,
      ‖shellDerivLinftyNorm U (omega k)‖ ≤ ‖shellDerivTailScale ^ k‖ := by
    filter_upwards [hlin, homega] with k hk1 hk2
    rw [Real.norm_eq_abs, abs_of_nonneg (shellDerivLinftyNorm_nonneg U (omega k)),
      Real.norm_eq_abs, abs_of_nonneg (shellDerivTailScale_pow_nonneg k)]
    exact hk1.trans hk2
  exact summable_of_isBigO_nat summable_shellDerivTailScale
    (Asymptotics.IsBigO.of_bound' hbound)

end

end SuperdiffusionCLT.Section2.Cutoff
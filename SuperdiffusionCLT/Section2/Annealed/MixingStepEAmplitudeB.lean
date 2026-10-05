/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Estimates.Stream.IncrementCubeMomentLocality
public import SuperdiffusionCLT.Section2.Annealed.DescendantColouring
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Step E: the residue colouring admits no `m`-free constant — the printed scale does

The Step-E amplitude bookkeeping `hAmpl` of `DescendantColouring` can be discharged in two
forms, but the constants they produce are *not* `m`-free: the realised-count form carries
`(3^m * d + 1)^(1/4)` and the explicit-count form `(3^m * d + 1)^(d/2)`.  The consumer
`MixingAnchorAssembly` binds its constant `CFluc` before `h`, `n` and the cutoff `m` of `hStepE`,
so an `m`-dependent constant cannot be absorbed there.  This module shows that the union bound
reorganised over the *colours* instead of over the descendant cubes does not remove the
`m`-dependence, and that the printed fixed scale does.

## The residue colouring gives no `m`-free constant; the union bound is not the obstruction

Every class of a Step-E partition must be pairwise **`m`**-shell-separated (`ShellField.AreShellSeparated m`,
the `hsep` of the entry-level estimate
`isBigO_gammaSigma_descendantAverage_entry_of_colorPartition`).  At `m = n` the depth-`(n - h)`
descendants of `cu_n` all lie in
the half-open `cu_n`, so two of their points are at distance `< 3^n * sqrt d = 3^m * sqrt d`
(`vecNorm_sub_lt_of_mem_cubeSet_originCube`); hence no two descendants are `m`-separated
(`not_areShellSeparated_of_mem_descendantsAtDepth_originCube`), every class is a singleton, the realised
count equals the descendant count `N = 3^(d (n - h))` (`card_descendantColorSet_at_self`), and the
union-bound factor is exactly `1` (`amplitude_factor_eq_one_at_self`).  Since `hAmpl` is quantified over
*all* `h < m ≤ n`, its `ν = 1` instance at `m = n`, `h = 0` forces `CFluc ≥ c(d) * 3^(n/4)` for the positive
`c(d) = gammaTriangleConst 2 * d^2 * (gammaTriangleConst 2 * gammaSigmaIndependentSumConst 2) * 2`, and
letting `n` grow refutes every single `CFluc`.  The explicit-count
form is refuted the same way: its factor is `≥ 1` because
`K = 3^m * d + 1 ≥ 3^m` forces `K^d ≥ N` (`one_le_modulus_factor_at_self`).  The obstruction is the *upper*
end `m ≤ n` of the `m`-quantifier, not the union bound.

## The printed scale: an `m`-free constant *does* exist

The printed Step E never runs at `m = n`: it **fixes** the intermediate scale at
`n' = ceil((n + h)/2)`, so `n' = n` only when `n - h = 1`, and colours the descendants by their
residue class at level `n' - h`, i.e. with the `h`-scaled modulus `3^(n' - h) * d + 1`.  That colouring has
`O(3^(d (n' - h)))` classes and spacing `C * 3^(n')` (`stepEColorModulus_scale_le`,
`areShellSeparated_of_stepEColor_eq`), so the union bound over the colour classes leaves a constant
depending on `d` alone: `stepEColorFactor d = sqrt((d + 1)^d) * 3^(1/4)` and `stepEAmplitudeConstMFree d =
2 * gammaTriangleConst 2 * d^2 * gammaTriangleConst 2 * gammaSigmaIndependentSumConst 2 *
stepEColorFactor d`, both `m`-, `h`-, `n`- and `nu`-free.  The restated bookkeeping is `hAmpl_printedScale`
(with `stepEColorK_pow_le` and `stepEColorSet_amplitude_le` the printed union-bound factor, valid for
**every** `d ≥ 1`) and the printed partition `hpart` is `stepEColorPartition_printed`.  The fixed scale, not
the window `h < m ≤ n - 1`, is forced by the consumers: the printed range is `h < n` and the sole
downstream consumer `MixingAnchorAssembly` calls `hStepE` only at `mm = (n + h + 1) / 2`; the window
`h < m ≤ n - 1` admits **no** `m`-free constant, for the same Archimedean reason as `m = n`.

## Main results

The refutation ingredients: `vecNorm_sub_lt_of_mem_cubeSet_originCube`,
`not_areShellSeparated_of_mem_descendantsAtDepth_originCube`, `card_descendantColorSet_at_self`,
`amplitude_factor_eq_one_at_self`, `one_le_modulus_factor_at_self`.  The printed-scale positive
results: `stepEColorFactor`, `stepEAmplitudeConstMFree`, `stepEColorModulus_scale_le`,
`areShellSeparated_of_stepEColor_eq`, `stepEColorK_pow_le`, `stepEColorSet_amplitude_le`,
`hAmpl_printedScale`, `stepEColorPartition_printed`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section2.Annealed

open Homogenization MeasureTheory
open Homogenization.IndependentSums
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Estimates.Stream

noncomputable section

variable {d : ℕ}

/-! ## The geometry at the top of the range: `m = n` -/

/-- **Two points of `cu_n` are strictly nearer than `3^n * sqrt d`.**  The
half-open realisation of `cu_n = originCube d n` has coordinate range
`[-3^n / 2, 3^n / 2)`, so every coordinate difference of two of its points is
strictly smaller than `3^n` in absolute value; summing the `d` squares gives
`vecNorm (x - y) < 3^n * sqrt d`.  The `[NeZero d]` supplies the strictness (at
least one coordinate contributes). -/
theorem vecNorm_sub_lt_of_mem_cubeSet_originCube [NeZero d] {n : ℕ} {x y : Vec d}
    (hx : x ∈ cubeSet (originCube d (n : ℤ))) (hy : y ∈ cubeSet (originCube d (n : ℤ))) :
    Homogenization.Book.Ch02.vecNorm (x - y) < (3 : ℝ) ^ n * Real.sqrt (d : ℝ) := by
  rw [mem_cubeSet_originCube_iff] at hx hy
  simp only [zpow_natCast] at hx hy
  have hposd : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have hcoord : ∀ i : Fin d, ((x - y) i) ^ 2 < ((3 : ℝ) ^ n) ^ 2 := by
    intro i
    have hlt : |(x - y) i| < (3 : ℝ) ^ n := by
      rw [abs_lt]
      exact ⟨by simp only [Pi.sub_apply]; linarith only [(hx i).1, (hy i).2],
        by simp only [Pi.sub_apply]; linarith only [(hx i).2, (hy i).1]⟩
    exact sq_lt_sq' (abs_lt.mp hlt).1 (abs_lt.mp hlt).2
  have hsum : Homogenization.vecNormSq (x - y) < (d : ℝ) * ((3 : ℝ) ^ n) ^ 2 := by
    have hs := Finset.sum_lt_sum (s := (Finset.univ : Finset (Fin d)))
      (f := fun i : Fin d => ((x - y) i) ^ 2) (g := fun _ : Fin d => ((3 : ℝ) ^ n) ^ 2)
      (fun i _ => le_of_lt (hcoord i))
      ⟨⟨0, hposd⟩, Finset.mem_univ _, hcoord ⟨0, hposd⟩⟩
    rw [Homogenization.vecNormSq, Homogenization.vecDot]
    calc ∑ i : Fin d, (x - y) i * (x - y) i
        = ∑ i : Fin d, ((x - y) i) ^ 2 :=
          Finset.sum_congr rfl (fun i _ => by ring)
      _ < ∑ _i : Fin d, ((3 : ℝ) ^ n) ^ 2 := hs
      _ = (d : ℝ) * ((3 : ℝ) ^ n) ^ 2 := by rw [Finset.sum_const]; simp
  have hsq : (Homogenization.Book.Ch02.vecNorm (x - y)) ^ 2 <
      ((3 : ℝ) ^ n * Real.sqrt (d : ℝ)) ^ 2 := by
    rw [Homogenization.Book.Ch02.vecNorm_sq_eq_vecNormSq]
    have hrhs : ((3 : ℝ) ^ n * Real.sqrt (d : ℝ)) ^ 2 = (d : ℝ) * ((3 : ℝ) ^ n) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by positivity)]
      ring
    rw [hrhs]
    exact hsum
  have habs := sq_lt_sq.mp hsq
  rwa [abs_of_nonneg (Homogenization.Book.Ch02.vecNorm_nonneg (x - y)),
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ (3 : ℝ) ^ n * Real.sqrt (d : ℝ))] at habs

/-- **Distinct descendants of `cu_n` are never `n`-separated.**  Both cubes lie
in the half-open `cu_n`, so their points are strictly nearer than `3^n * sqrt d`;
`ShellField.AreShellSeparated n` asks for the reverse non-strict inequality.
The statement needs no distinctness of `R` and `S`: separation already fails at
the common centre. -/
theorem not_areShellSeparated_of_mem_descendantsAtDepth_originCube [NeZero d]
    {n h : ℕ} {R S : TriadicCube d}
    (hR : R ∈ descendantsAtDepth (originCube d (n : ℤ)) (n - h))
    (hS : S ∈ descendantsAtDepth (originCube d (n : ℤ)) (n - h)) :
    ¬ ShellField.AreShellSeparated n (cubeSet R) (cubeSet S) := by
  intro hsep
  have hsubR : cubeSet R ⊆ cubeSet (originCube d (n : ℤ)) :=
    cubeSet_subset_of_mem_descendantsAtDepth hR
  have hsubS : cubeSet S ⊆ cubeSet (originCube d (n : ℤ)) :=
    cubeSet_subset_of_mem_descendantsAtDepth hS
  have hx : cubeCenter R ∈ cubeSet (originCube d (n : ℤ)) := hsubR (cubeCenter_mem_cubeSet R)
  have hy : cubeCenter S ∈ cubeSet (originCube d (n : ℤ)) := hsubS (cubeCenter_mem_cubeSet S)
  have hlt := vecNorm_sub_lt_of_mem_cubeSet_originCube hx hy
  have hle : (3 : ℝ) ^ n * Real.sqrt (d : ℝ) ≤
      Homogenization.Book.Ch02.vecNorm (cubeCenter R - cubeCenter S) :=
    hsep (cubeCenter_mem_cubeSet R) (cubeCenter_mem_cubeSet S)
  exact absurd hle (not_le.mpr hlt)

/-! ## The class count and the union-bound factor at `m = n` -/

/-- **A partition whose classes are singletons has exactly `N` classes.**  The
classes are disjoint and cover the `N` descendants, and each is a singleton. -/
theorem card_colors_eq_of_singleton_classes {ι : Type*} [DecidableEq ι]
    {h n : ℕ} (colors : Finset ι) (cls : ι → Finset (TriadicCube d))
    (hdisj : (colors : Set ι).PairwiseDisjoint cls)
    (hcover : colors.biUnion cls = descendantsAtDepth (originCube d (n : ℤ)) (n - h))
    (hnonempty : ∀ c ∈ colors, (cls c).Nonempty)
    (hsingle : ∀ c ∈ colors, ∀ R ∈ cls c, ∀ S ∈ cls c, R = S) :
    colors.card = (descendantsAtDepth (originCube d (n : ℤ)) (n - h)).card := by
  have hcard1 : ∀ c ∈ colors, (cls c).card = 1 := by
    intro c hc
    have hle : (cls c).card ≤ 1 :=
      Finset.card_le_one.mpr (fun R hR S hS => hsingle c hc R hR S hS)
    have hge : 1 ≤ (cls c).card := Finset.card_pos.mpr (hnonempty c hc)
    omega
  have hsum : ∑ c ∈ colors, (cls c).card =
      (descendantsAtDepth (originCube d (n : ℤ)) (n - h)).card := by
    rw [← Finset.card_biUnion (s := colors) (t := cls) hdisj, hcover]
  rw [Finset.sum_congr rfl (fun c hc => hcard1 c hc), Finset.sum_const, nsmul_eq_mul,
    mul_one] at hsum
  exact hsum

/-- **The residue colouring has all classes singletons at `m = n`, so exactly `N`
of them.**  The separation conjunct of `descendantColorPartition` at `m = n`
demands `n`-separation of every class, which the geometry above makes impossible
for two distinct descendants. -/
theorem card_descendantColorSet_at_self [NeZero d] {N h : ℕ} (hhN : h < N) :
    (descendantColorSet d N N h).card =
      (descendantsAtDepth (originCube d (N : ℤ)) (N - h)).card := by
  obtain ⟨-, hdisj, hcover, hnonempty, hsep, -⟩ :=
    descendantColorPartition (d := d) (m := N) (n := N) (h := h) hhN le_rfl
  refine card_colors_eq_of_singleton_classes (d := d) (h := h) (n := N)
    (descendantColorSet d N N h) (descendantColorClass d N N h) hdisj hcover hnonempty ?_
  intro c hc R hR S hS
  by_contra hne
  exact not_areShellSeparated_of_mem_descendantsAtDepth_originCube
    (mem_descendantColorClass_iff.mp hR).1 (mem_descendantColorClass_iff.mp hS).1
    (hsep c hc R hR S hS hne)

/-- **The union-bound factor of a partition with `N` classes is exactly `1`.** -/
theorem amplitude_factor_eq_one_at_self {ι : Type*} {h n : ℕ} (colors : Finset ι)
    (hcard : colors.card = (descendantsAtDepth (originCube d (n : ℤ)) (n - h)).card) :
    Real.sqrt (colors.card : ℝ) *
        (Real.sqrt ((descendantsAtDepth (originCube d (n : ℤ)) (n - h)).card : ℝ) /
          ((descendantsAtDepth (originCube d (n : ℤ)) (n - h)).card : ℝ)) = 1 := by
  have hN : (descendantsAtDepth (originCube d (n : ℤ)) (n - h)).card = (3 ^ d) ^ (n - h) :=
    SuperdiffusionCLT.Section2.Localization.card_descendantsAtDepth_originCube d
  have hNpos : (0 : ℝ) <
      ((descendantsAtDepth (originCube d (n : ℤ)) (n - h)).card : ℝ) := by
    rw [hN]
    positivity
  rw [hcard, ← mul_div_assoc, ← sq, Real.sq_sqrt hNpos.le, div_self (ne_of_gt hNpos)]

/-! ## The explicit-count factor is also at least `1` at `m = n` -/

/-- **The explicit-class-count factor is at least `1` at `m = n`.**  Since
`3^m ≤ 3^m * d + 1` for `d ≥ 1`, the modulus `K = descendantColorModulus d N`
satisfies `K^d ≥ (3^N)^d = N`, so `sqrt(K^d) ≥ sqrt N` and the factor
`sqrt(K^d) * sqrt(N) / N` is at least `sqrt(N)^2 / N = 1`. -/
theorem one_le_modulus_factor_at_self [NeZero d] {N : ℕ} (_hN : 0 < N) :
    1 ≤ Real.sqrt ((((descendantColorModulus d N) ^ d : ℕ) : ℝ)) *
        (Real.sqrt ((descendantsAtDepth (originCube d (N : ℤ)) N).card : ℝ) /
          ((descendantsAtDepth (originCube d (N : ℤ)) N).card : ℝ)) := by
  have hdle : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)
  have hcardN : (descendantsAtDepth (originCube d (N : ℤ)) N).card = (3 ^ d) ^ N := by
    simpa only [Nat.sub_zero] using
      SuperdiffusionCLT.Section2.Localization.card_descendantsAtDepth_originCube d
        (n := N) (h := 0)
  have hmod : (descendantsAtDepth (originCube d (N : ℤ)) N).card ≤
      (descendantColorModulus d N) ^ d := by
    have hleK : 3 ^ N ≤ descendantColorModulus d N := by
      have hmul : 3 ^ N * 1 ≤ 3 ^ N * d := Nat.mul_le_mul_left (3 ^ N) hdle
      rw [Nat.mul_one] at hmul
      show 3 ^ N ≤ 3 ^ N * d + 1
      omega
    calc (descendantsAtDepth (originCube d (N : ℤ)) N).card = (3 ^ N) ^ d := by
          rw [hcardN]
          exact (pow_mul 3 d N).symm.trans (pow_mul' 3 d N)
      _ ≤ (descendantColorModulus d N) ^ d := Nat.pow_le_pow_left hleK d
  have hNpos : (0 : ℝ) < ((descendantsAtDepth (originCube d (N : ℤ)) N).card : ℝ) := by
    rw [hcardN]
    positivity
  have hsqrt : Real.sqrt ((descendantsAtDepth (originCube d (N : ℤ)) N).card : ℝ) ≤
      Real.sqrt ((((descendantColorModulus d N) ^ d : ℕ) : ℝ)) :=
    Real.sqrt_le_sqrt (by exact_mod_cast hmod)
  calc (1 : ℝ) = Real.sqrt ((descendantsAtDepth (originCube d (N : ℤ)) N).card : ℝ) *
        (Real.sqrt ((descendantsAtDepth (originCube d (N : ℤ)) N).card : ℝ) /
          ((descendantsAtDepth (originCube d (N : ℤ)) N).card : ℝ)) := by
        rw [← mul_div_assoc, ← sq, Real.sq_sqrt hNpos.le, div_self (ne_of_gt hNpos)]
    _ ≤ Real.sqrt ((((descendantColorModulus d N) ^ d : ℕ) : ℝ)) *
        (Real.sqrt ((descendantsAtDepth (originCube d (N : ℤ)) N).card : ℝ) /
          ((descendantsAtDepth (originCube d (N : ℤ)) N).card : ℝ)) :=
        mul_le_mul_of_nonneg_right hsqrt (by positivity)

/-! ## No `m`-free constant -/

/-! ## Witnesses: the degeneration is non-vacuous -/

/-- Witness at `d = 2`, `m = n = 3`, `h = 0`: the residue colouring has
`3^(2 * 3) = 729` singleton classes, so the realised union-bound factor is
exactly `1`, not merely bounded by `1`. -/
example : Real.sqrt ((descendantColorSet 2 3 3 0).card : ℝ) *
    (Real.sqrt ((descendantsAtDepth (originCube 2 (3 : ℤ)) (3 - 0)).card : ℝ) /
      ((descendantsAtDepth (originCube 2 (3 : ℤ)) (3 - 0)).card : ℝ)) = 1 :=
  amplitude_factor_eq_one_at_self (d := 2) (h := 0) (n := 3) (descendantColorSet 2 3 3 0)
    (card_descendantColorSet_at_self (d := 2) (N := 3) (h := 0) (by norm_num))

/-- Witness at `d = 2`, `m = n = 3`: the explicit-count factor is at least `1`.
Here `descendantColorModulus 2 3 = 55` and the descendant count is `729`, so the
bound reads `1 ≤ 55 * 27 / 729 = 55/27`. -/
example : (1 : ℝ) ≤ Real.sqrt ((((descendantColorModulus 2 3) ^ 2 : ℕ) : ℝ)) *
    (Real.sqrt ((descendantsAtDepth (originCube 2 (3 : ℤ)) 3).card : ℝ) /
      ((descendantsAtDepth (originCube 2 (3 : ℤ)) 3).card : ℝ)) :=
  one_le_modulus_factor_at_self (d := 2) (N := 3) (by norm_num)

/-! ## The printed scale: the `m`-free amplitude constant

The refutations above use the residue colouring, whose modulus `3^m * d + 1` is
`h`-independent and whose `m`-quantifier is unrestricted.  The printed Step E
does neither: it *fixes* the intermediate scale at `n' = ceil((n + h) / 2)` and
colours the depth-`(n - h)` descendants by their residue class at level `n' - h`,
i.e. with the `h`-*scaled* modulus `3^(n' - h) * d + 1`.  The class count is then
`O(3^(d (n' - h)))` and the classes are `n'`-shell-separated, so the union bound
over the colour classes has a constant that depends on `d` alone.

Choosing the fixed printed scale (rather than quantifying `h < m ≤ n - 1`) is
forced by the consumers: the printed range is `h < n`, the printed proof uses the fixed
`n' = ceil((n + h)/2)`, and the sole downstream consumer
`MixingAnchorAssembly` calls its `hStepE` only at the midpoint
`mm = (n + h + 1) / 2`.  The alternative `h < m ≤ n - 1` admits **no** `m`-free
constant: for `m` near `n - 1` the factor stays of order `1` while the printed
right side still decays, so Archimedes rules a single constant out exactly as at
`m = n`.

`n'` equals `n` only in the degenerate case `n - h = 1`; there the realised class
count is at most the descendant count, so the factor is at most `1`, and the
`3^(1/4)` built into `stepEColorFactor` pays the printed exponent `1/4`.  That
case is handled explicitly in `stepEColorSet_amplitude_le_degenerate`. -/

/-- The `m`-free union-bound factor of the printed-scale Step-E colouring:
`sqrt((d + 1)^d) * 3^(1/4)`.  The `3^(1/4)` absorbs the degenerate `n - h = 1`
case, where the printed-decay exponent is `1/4`; for `d ≥ 2` this factor bounds
the union bound over the `O(3^(d (n' - h)))` colour classes. -/
def stepEColorFactor (d : ℕ) : ℝ :=
  Real.sqrt ((((d + 1) ^ d : ℕ) : ℝ)) * (3 : ℝ) ^ ((1 : ℝ) / 4)

/-- The `m`-free Step-E amplitude constant of the printed scale:
`2 * gammaTriangleConst 2 * d^2 * gammaTriangleConst 2 *
gammaSigmaIndependentSumConst 2 * stepEColorFactor d`.  **It depends on `d`
alone** — no cutoff `m`, no `h`, no `n`, no `nu`. -/
def stepEAmplitudeConstMFree (d : ℕ) : ℝ :=
  2 * gammaTriangleConst 2 * ((d : ℝ) * (d : ℝ)) * gammaTriangleConst 2 *
    Homogenization.Book.Ch04.gammaSigmaIndependentSumConst 2 * stepEColorFactor d

private theorem three_quarter_mul :
    (3 : ℝ) ^ ((1 : ℝ) / 4) * (3 : ℝ) ^ (-((1 : ℝ) / 4)) = 1 := by
  rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
  have h : (1 : ℝ) / 4 + (-((1 : ℝ) / 4)) = 0 := by norm_num
  rw [h, Real.rpow_zero]

private theorem one_le_three_quarter : (1 : ℝ) ≤ (3 : ℝ) ^ ((1 : ℝ) / 4) :=
  Real.one_le_rpow (by norm_num : (1 : ℝ) ≤ 3) (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 4)

private theorem one_le_static (d : ℕ) : (1 : ℝ) ≤ (((d + 1) ^ d : ℕ) : ℝ) := by
  have hnat : 1 ≤ (d + 1) ^ d := one_le_pow₀ (show (1 : ℕ) ≤ d + 1 by omega)
  exact_mod_cast hnat

private theorem cast_static (d : ℕ) : (((d + 1) ^ d : ℕ) : ℝ) = ((d : ℝ) + 1) ^ d := by
  push_cast
  ring

private theorem stepEColorFactor_nonneg (d : ℕ) : 0 ≤ stepEColorFactor d := by
  unfold stepEColorFactor
  exact mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg (by norm_num) _)

/-! ### The `h`-scaled modulus separates the classes at the printed scale -/

/-- **The `h`-scaled modulus separates at scale `m`.**  The modulus of the
colouring at level `m - h` is `K = 3^(m - h) * d + 1`, so
`(K - 1) * 3^h = d * 3^m ≥ 3^m * sqrt d`.  This is the spacing `C * 3^(n')` of the
printed partition, and it is what the `h`-independent proved modulus `3^m * d + 1`
cannot supply. -/
theorem stepEColorModulus_scale_le {d m h : ℕ} (hhm : h ≤ m) :
    (3 : ℝ) ^ m * Real.sqrt (d : ℝ) ≤
      ((descendantColorModulus d (m - h) : ℝ) - 1) * (3 : ℝ) ^ h := by
  have hK : (descendantColorModulus d (m - h) : ℝ) - 1 = (3 : ℝ) ^ (m - h) * (d : ℝ) := by
    unfold descendantColorModulus
    push_cast
    ring
  rw [hK]
  have hpow : (3 : ℝ) ^ m = (3 : ℝ) ^ (m - h) * (3 : ℝ) ^ h := by
    rw [← pow_add, Nat.sub_add_cancel hhm]
  rw [hpow]
  calc (3 : ℝ) ^ (m - h) * (3 : ℝ) ^ h * Real.sqrt (d : ℝ)
      ≤ (3 : ℝ) ^ (m - h) * (3 : ℝ) ^ h * (d : ℝ) :=
        mul_le_mul_of_nonneg_left (sqrt_natCast_le_self d) (by positivity)
    _ = (3 : ℝ) ^ (m - h) * (d : ℝ) * (3 : ℝ) ^ h := by ring

/-- **Two cubes with the same `(m - h)`-level colour are `m`-separated.**  Both
cubes sit at scale `h`; a differing coordinate is divisible by
`K = 3^(m - h) * d + 1`, so its absolute difference is at least `(K - 1) * 3^h`,
which `stepEColorModulus_scale_le` dominates by `3^m * sqrt d`. -/
theorem areShellSeparated_of_stepEColor_eq {d m h : ℕ} (hhm : h ≤ m) {R S : TriadicCube d}
    (hRscale : R.scale = (h : ℤ)) (hSscale : S.scale = (h : ℤ)) (hne : R ≠ S)
    (hcolor : descendantColor d (m - h) R = descendantColor d (m - h) S) :
    ShellField.AreShellSeparated m (cubeSet R) (cubeSet S) := by
  intro x y hx hy
  have hKpos : 0 < descendantColorModulus d (m - h) := descendantColorModulus_pos d (m - h)
  have hidx : ∃ i, R.index i ≠ S.index i := by
    by_contra h
    push Not at h
    apply hne
    have hidxeq : R.index = S.index := funext h
    rcases R with ⟨sR, iR⟩
    rcases S with ⟨sS, iS⟩
    have hscale : sR = sS := hRscale.trans hSscale.symm
    simp only [TriadicCube.mk.injEq]
    exact ⟨hscale, hidxeq⟩
  rcases hidx with ⟨i, hi⟩
  have hcoord := modulus_sub_one_mul_scale_le_abs_coord (d := d) (m := m - h) (h := h)
    hRscale hSscale
    (le_or_le_neg_of_dvd_sub hKpos
      (dvd_index_sub_of_descendantColor_eq (m := m - h) hcolor i) hi) hx hy
  have hnorm : |x i - y i| ≤ Homogenization.Book.Ch02.vecNorm (x - y) := by
    simpa only [Pi.sub_apply] using abs_apply_le_vecNorm (x - y) i
  exact le_trans (stepEColorModulus_scale_le (d := d) (m := m) (h := h) hhm)
    (le_trans hcoord hnorm)

/-! ### The printed amplitude bound -/

/-- `10/9 ≤ 2 * 3^(-1/2)`: the slack that pays the exceptional odd case `d = 1`. -/
private theorem ten_ninths_le_two_rpow : (10 : ℝ) / 9 ≤ 2 * (3 : ℝ) ^ (-(1 / 2 : ℝ)) := by
  have hval : (3 : ℝ) ^ (-(1 / 2 : ℝ)) = (Real.sqrt 3)⁻¹ := by
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3), ← Real.sqrt_eq_rpow]
  rw [hval, ← div_eq_mul_inv]
  rw [le_div_iff₀ (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 3))]
  have hle : Real.sqrt 3 ≤ 9 / 5 := by
    rw [Real.sqrt_le_iff]
    exact ⟨by norm_num, by norm_num⟩
  nlinarith only [hle]

/-- **Reduced colour-count estimate.**  With `K = 3^p d + 1 = 3^p (d + 3^{-p})`,
the factor `3^{dp}` cancels from both sides of `stepEColorK_pow_le`, leaving this
form.  The crude exponent comparison `(p + q)/2 ≤ d q` fails exactly when `d = 1`
and `p = q + 1` (`p + q` odd); there `d + 3^{-p} = 1 + 3^{-p} ≤ 10/9 ≤ 2 · 3^{-1/2}`
supplies the missing factor `3^{-1/2}`, while for `d ≥ 2` the exponent is already
nonnegative, since `(d - 1) q - 1/2 ≥ 1/2 > 0`. -/
private theorem stepEColorK_pow_le_reduced {d p q : ℕ} (hd : 1 ≤ d) (hq : 1 ≤ q)
    (hpq : q ≤ p) (hpq' : p ≤ q + 1) :
    ((d : ℝ) + (3 : ℝ) ^ (-(p : ℝ))) ^ d ≤ ((d : ℝ) + 1) ^ d *
      (3 : ℝ) ^ ((d : ℝ) * (q : ℝ) - (((p + q : ℕ) : ℝ) / 2)) := by
  have h3 : (0 : ℝ) < 3 := by norm_num
  have hle1 : (3 : ℝ) ^ (-(p : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num : (1 : ℝ) ≤ 3)
      (neg_nonpos.mpr (Nat.cast_nonneg p))
  have hd0 : (0 : ℝ) ≤ (d : ℝ) := by positivity
  have hpow : ((d : ℝ) + (3 : ℝ) ^ (-(p : ℝ))) ^ d ≤ ((d : ℝ) + 1) ^ d :=
    pow_le_pow_left₀ (by linarith only [Real.rpow_nonneg h3.le (-(p : ℝ)), hd0])
      (by linarith only [hle1]) d
  rcases le_or_gt 2 d with hd2 | hd2
  · have hqR : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    have h2 : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd2
    have hpqR : (((p + q : ℕ) : ℝ)) ≤ 2 * (q : ℝ) + 1 := by
      exact_mod_cast (show p + q ≤ 2 * q + 1 by omega)
    have he : 0 ≤ (d : ℝ) * (q : ℝ) - (((p + q : ℕ) : ℝ) / 2) := by
      nlinarith only [h2, hqR, hpqR]
    exact le_trans hpow (le_mul_of_one_le_right (pow_nonneg (by positivity) d)
      (Real.one_le_rpow (by norm_num : (1 : ℝ) ≤ 3) he))
  · have hd1 : d = 1 := by omega
    subst hd1
    rcases (show p = q ∨ p = q + 1 by omega) with h | h
    · have he : ((1 : ℕ) : ℝ) * (q : ℝ) - (((p + q : ℕ) : ℝ) / 2) = 0 := by
        rw [h]; push_cast; ring
      rw [he, Real.rpow_zero, mul_one, Nat.cast_one, pow_one, pow_one]
      linarith only [hle1]
    · have he : ((1 : ℕ) : ℝ) * (q : ℝ) - (((p + q : ℕ) : ℝ) / 2) = -(1 / 2 : ℝ) := by
        rw [h]; push_cast; ring
      rw [he, Nat.cast_one, pow_one, pow_one, show ((1 : ℝ) + 1) = 2 by norm_num]
      have hp2 : 2 ≤ p := by omega
      have hT : (9 : ℝ) ≤ (3 : ℝ) ^ (p : ℝ) := by
        rw [Real.rpow_natCast]
        calc (9 : ℝ) = (3 : ℝ) ^ (2 : ℕ) := by norm_num
          _ ≤ (3 : ℝ) ^ p := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 3) hp2
      have hinv : (3 : ℝ) ^ (-(p : ℝ)) ≤ 1 / 9 := by
        rw [Real.rpow_neg h3.le]
        calc ((3 : ℝ) ^ (p : ℝ))⁻¹ ≤ (9 : ℝ)⁻¹ := inv_anti₀ (by norm_num : (0 : ℝ) < 9) hT
          _ = 1 / 9 := by norm_num
      calc (1 : ℝ) + (3 : ℝ) ^ (-(p : ℝ)) ≤ 1 + 1 / 9 := by linarith only [hinv]
        _ = 10 / 9 := by norm_num
        _ ≤ 2 * (3 : ℝ) ^ (-(1 / 2 : ℝ)) := ten_ninths_le_two_rpow

/-- **Sharper colour-count estimate.**  For `d ≥ 1` and `1 ≤ q ≤ p ≤ q + 1` (with
`p = ceil((p + q)/2)`, `q = floor((p + q)/2)`) the `d`-th power of the colour
modulus at level `p` is dominated by `(d + 1)^d · 3^(d (p + q) - (p + q)/2)`.
This is the sharpened form of the crude bound `K ≤ (d + 1) 3^p`: it holds for
**every** `d ≥ 1` (`stepEColorK_pow_le_reduced`). -/
theorem stepEColorK_pow_le {d p q : ℕ} (hd : 1 ≤ d) (hq : 1 ≤ q)
    (hpq : q ≤ p) (hpq' : p ≤ q + 1) :
    ((3 : ℝ) ^ p * (d : ℝ) + 1) ^ d ≤ ((d : ℝ) + 1) ^ d *
      (3 : ℝ) ^ ((d : ℝ) * ((p + q : ℕ) : ℝ) - (((p + q : ℕ) : ℝ) / 2)) := by
  have h3 : (0 : ℝ) < 3 := by norm_num
  have hfac : (3 : ℝ) ^ p * (d : ℝ) + 1 =
      (3 : ℝ) ^ p * ((d : ℝ) + (3 : ℝ) ^ (-(p : ℝ))) := by
    rw [mul_add]
    congr 1
    rw [← Real.rpow_natCast (3 : ℝ) p, ← Real.rpow_add h3, add_neg_cancel, Real.rpow_zero]
  rw [hfac, mul_pow, ← Real.rpow_natCast (3 : ℝ) p,
    ← Real.rpow_natCast ((3 : ℝ) ^ (p : ℝ)) d, ← Real.rpow_mul h3.le]
  have hred := stepEColorK_pow_le_reduced (d := d) (p := p) (q := q) hd hq hpq hpq'
  have hexp : (p : ℝ) * (d : ℝ) + ((d : ℝ) * (q : ℝ) - (((p + q : ℕ) : ℝ) / 2)) =
      (d : ℝ) * ((p + q : ℕ) : ℝ) - (((p + q : ℕ) : ℝ) / 2) := by push_cast; ring
  calc (3 : ℝ) ^ ((p : ℝ) * (d : ℝ)) * ((d : ℝ) + (3 : ℝ) ^ (-(p : ℝ))) ^ d
      ≤ (3 : ℝ) ^ ((p : ℝ) * (d : ℝ)) * (((d : ℝ) + 1) ^ d *
          (3 : ℝ) ^ ((d : ℝ) * (q : ℝ) - (((p + q : ℕ) : ℝ) / 2))) :=
        mul_le_mul_of_nonneg_left hred (Real.rpow_nonneg h3.le _)
    _ = ((d : ℝ) + 1) ^ d * ((3 : ℝ) ^ ((p : ℝ) * (d : ℝ)) *
          (3 : ℝ) ^ ((d : ℝ) * (q : ℝ) - (((p + q : ℕ) : ℝ) / 2))) := by ring
    _ = ((d : ℝ) + 1) ^ d *
          (3 : ℝ) ^ ((d : ℝ) * ((p + q : ℕ) : ℝ) - (((p + q : ℕ) : ℝ) / 2)) := by
        rw [← Real.rpow_add h3, hexp]

/-- **Non-degenerate printed amplitude bound.**  With `n' = (n + h + 1) / 2` and
`m = n'` the class count is at most `K^d`, the descendant count is `3^(d (n - h))`,
so `P^2 ≤ K^d / 3^(d (n - h))`.  Writing `p = m - h = ceil((n - h)/2)` and
`q = n - m = floor((n - h)/2)`, the sharper count `stepEColorK_pow_le` gives
`K^d ≤ (d + 1)^d * 3^(d (n - h) - (n - h)/2)` for **every** `d ≥ 1`.  The crude
exponent comparison `(n - h)/2 ≤ d (n - m)`, which fails exactly at `d = 1` with
`n - h` odd, is not needed: there the exact form `K = 3^p (d + 3^{-p})` supplies
the factor `3^{-1/2}` via `10/9 ≤ 2 · 3^{-1/2}`. -/
private theorem stepEColorSet_amplitude_le_nondeg [NeZero d] {n h : ℕ}
    (hhn : h < n) (hgap : 2 ≤ n - h) :
    Real.sqrt ((descendantColorSet d ((n + h + 1) / 2 - h) n h).card : ℝ) *
      (Real.sqrt ((descendantsAtDepth (originCube d (n : ℤ)) (n - h)).card : ℝ) /
        ((descendantsAtDepth (originCube d (n : ℤ)) (n - h)).card : ℝ))
    ≤ Real.sqrt ((((d + 1) ^ d : ℕ) : ℝ)) *
        (3 : ℝ) ^ (-(((n - h : ℕ) : ℝ) / 4)) := by
  set m : ℕ := (n + h + 1) / 2 with hm
  set Q : ℕ := (descendantColorSet d (m - h) n h).card with hQ
  set Nc : ℕ := (descendantsAtDepth (originCube d (n : ℤ)) (n - h)).card with hNc
  set K : ℝ := (descendantColorModulus d (m - h) : ℝ) with hK
  set P : ℝ := Real.sqrt (Q : ℝ) * (Real.sqrt (Nc : ℝ) / (Nc : ℝ)) with hP
  have hQnn : (0 : ℝ) ≤ (Q : ℝ) := by positivity
  have hNcnn : (0 : ℝ) ≤ (Nc : ℝ) := by positivity
  have hnat : Nc = (3 ^ d) ^ (n - h) := by
    rw [hNc]
    exact SuperdiffusionCLT.Section2.Localization.card_descendantsAtDepth_originCube d
  have hNceq : (Nc : ℝ) = (3 : ℝ) ^ (d * (n - h)) := by
    rw [hnat]
    push_cast
    rw [← pow_mul]
  have hQle : (Q : ℝ) ≤ K ^ d := by
    have h := card_descendantColorSet_le d (m - h) n h
    rw [← hQ] at h
    rw [hK]
    exact_mod_cast h
  have hP_sq : P ^ 2 = (Q : ℝ) / (Nc : ℝ) := by
    rw [hP, mul_pow, Real.sq_sqrt hQnn]
    have h2 : (Real.sqrt (Nc : ℝ) / (Nc : ℝ)) ^ 2 = ((Nc : ℝ))⁻¹ := by
      rw [div_pow, Real.sq_sqrt hNcnn]
      field_simp
    rw [h2, div_eq_mul_inv]
  have hPnn : 0 ≤ P := by
    rw [hP]
    exact mul_nonneg (Real.sqrt_nonneg _) (div_nonneg (Real.sqrt_nonneg _) hNcnn)
  have hKform : K = (3 : ℝ) ^ (m - h) * (d : ℝ) + 1 := by
    rw [hK]
    unfold descendantColorModulus
    push_cast
    ring
  have hq1 : 1 ≤ n - m := by rw [hm]; omega
  have hqp : n - m ≤ m - h := by rw [hm]; omega
  have hqp' : m - h ≤ n - m + 1 := by rw [hm]; omega
  have hpq : (m - h) + (n - m) = n - h := by omega
  have hd1 : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)
  have hKd_sharp : K ^ d ≤ (((d + 1) ^ d : ℕ) : ℝ) *
      (3 : ℝ) ^ ((d : ℝ) * ((n - h : ℕ) : ℝ) - (((n - h : ℕ) : ℝ) / 2)) := by
    have h := stepEColorK_pow_le (d := d) (p := m - h) (q := n - m) hd1 hq1 hqp hqp'
    rw [← hKform] at h
    rw [hpq, ← cast_static d] at h
    exact h
  have hPsq_sharp : P ^ 2 ≤ (((d + 1) ^ d : ℕ) : ℝ) *
      (3 : ℝ) ^ (-(((n - h : ℕ) : ℝ) / 2)) := by
    calc P ^ 2 = (Q : ℝ) / (Nc : ℝ) := hP_sq
      _ ≤ K ^ d / (Nc : ℝ) := div_le_div_of_nonneg_right hQle hNcnn
      _ ≤ ((((d + 1) ^ d : ℕ) : ℝ) *
            (3 : ℝ) ^ ((d : ℝ) * ((n - h : ℕ) : ℝ) - (((n - h : ℕ) : ℝ) / 2))) / (Nc : ℝ) :=
          div_le_div_of_nonneg_right hKd_sharp hNcnn
      _ = (((d + 1) ^ d : ℕ) : ℝ) * (3 : ℝ) ^ (-(((n - h : ℕ) : ℝ) / 2)) := by
          rw [hNceq, ← Real.rpow_natCast (3 : ℝ) (d * (n - h))]
          rw [mul_div_assoc, ← Real.rpow_sub (by norm_num : (0 : ℝ) < 3)]
          congr 1
          push_cast
          ring_nf
  have hSquareEq : (3 : ℝ) ^ (-(((n - h : ℕ) : ℝ) / 2)) =
      ((3 : ℝ) ^ (-(((n - h : ℕ) : ℝ) / 4))) ^ 2 := by
    rw [← Real.rpow_natCast ((3 : ℝ) ^ (-(((n - h : ℕ) : ℝ) / 4))) 2,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    congr 1
    ring
  have hPsq_final : P ^ 2 ≤ (((d + 1) ^ d : ℕ) : ℝ) *
      ((3 : ℝ) ^ (-(((n - h : ℕ) : ℝ) / 4))) ^ 2 := by
    rw [← hSquareEq]
    exact hPsq_sharp
  calc P = Real.sqrt (P ^ 2) := (Real.sqrt_sq hPnn).symm
    _ ≤ Real.sqrt ((((d + 1) ^ d : ℕ) : ℝ) * ((3 : ℝ) ^ (-(((n - h : ℕ) : ℝ) / 4))) ^ 2) :=
        Real.sqrt_le_sqrt hPsq_final
    _ = Real.sqrt ((((d + 1) ^ d : ℕ) : ℝ)) * (3 : ℝ) ^ (-(((n - h : ℕ) : ℝ) / 4)) := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]

/-- **Degenerate printed amplitude bound, `n - h = 1`.**  Here `n' = n` and the
realised class count is at most the descendant count, so the factor is at most
`1`; the `3^(1/4)` inside `stepEColorFactor` cancels the printed exponent `1/4`,
leaving `1 ≤ sqrt((d + 1)^d)`. -/
private theorem stepEColorSet_amplitude_le_degenerate {n h : ℕ} (hgap : n - h = 1) :
    Real.sqrt ((descendantColorSet d ((n + h + 1) / 2 - h) n h).card : ℝ) *
      (Real.sqrt ((descendantsAtDepth (originCube d (n : ℤ)) (n - h)).card : ℝ) /
        ((descendantsAtDepth (originCube d (n : ℤ)) (n - h)).card : ℝ))
    ≤ stepEColorFactor d * (3 : ℝ) ^ (-(((n - h : ℕ) : ℝ) / 4)) := by
  set Q : ℕ := (descendantColorSet d ((n + h + 1) / 2 - h) n h).card with hQ
  set Nc : ℕ := (descendantsAtDepth (originCube d (n : ℤ)) (n - h)).card with hNc
  have hQle : Q ≤ Nc := by
    rw [hQ, hNc]
    exact Finset.card_image_le
  have hNcpos : (0 : ℝ) < (Nc : ℝ) := by
    rw [hNc]
    have hnat : (descendantsAtDepth (originCube d (n : ℤ)) (n - h)).card = (3 ^ d) ^ (n - h) :=
      SuperdiffusionCLT.Section2.Localization.card_descendantsAtDepth_originCube d
    rw [hnat]
    positivity
  have hfactor : Real.sqrt (Q : ℝ) * (Real.sqrt (Nc : ℝ) / (Nc : ℝ)) ≤ 1 := by
    have hsqrt : Real.sqrt (Q : ℝ) ≤ Real.sqrt (Nc : ℝ) :=
      Real.sqrt_le_sqrt (by exact_mod_cast hQle)
    have hnn : 0 ≤ Real.sqrt (Nc : ℝ) / (Nc : ℝ) := div_nonneg (Real.sqrt_nonneg _) hNcpos.le
    calc Real.sqrt (Q : ℝ) * (Real.sqrt (Nc : ℝ) / (Nc : ℝ))
        ≤ Real.sqrt (Nc : ℝ) * (Real.sqrt (Nc : ℝ) / (Nc : ℝ)) :=
          mul_le_mul_of_nonneg_right hsqrt hnn
      _ = 1 := by rw [← mul_div_assoc, ← sq, Real.sq_sqrt hNcpos.le, div_self (ne_of_gt hNcpos)]
  have hone : (1 : ℝ) ≤ stepEColorFactor d * (3 : ℝ) ^ (-(((n - h : ℕ) : ℝ) / 4)) := by
    rw [hgap]
    simp only [Nat.cast_one]
    unfold stepEColorFactor
    rw [mul_assoc, three_quarter_mul, mul_one]
    exact Real.one_le_sqrt.mpr (one_le_static d)
  exact le_trans hfactor hone

/-- **The printed-scale amplitude factor is bounded by `stepEColorFactor d`.**  The
case split is explicit: `n - h = 1` is the degenerate printed scale `n' = n`, and
`n - h ≥ 2` is the non-degenerate one; both are `m`-free. -/
theorem stepEColorSet_amplitude_le [NeZero d] {n h : ℕ} (hhn : h < n) :
    Real.sqrt ((descendantColorSet d ((n + h + 1) / 2 - h) n h).card : ℝ) *
      (Real.sqrt ((descendantsAtDepth (originCube d (n : ℤ)) (n - h)).card : ℝ) /
        ((descendantsAtDepth (originCube d (n : ℤ)) (n - h)).card : ℝ))
    ≤ stepEColorFactor d * (3 : ℝ) ^ (-(((n - h : ℕ) : ℝ) / 4)) := by
  rcases lt_or_ge (n - h) 2 with _ | hge
  · exact stepEColorSet_amplitude_le_degenerate (d := d) (by omega)
  · exact le_trans (stepEColorSet_amplitude_le_nondeg (d := d) hhn hge)
      (mul_le_mul_of_nonneg_right
        (by
          unfold stepEColorFactor
          simpa only [mul_one] using
            mul_le_mul_of_nonneg_left one_le_three_quarter (Real.sqrt_nonneg _))
        (by positivity))

/-- The `nu`-bookkeeping `nu⁻¹ + nu⁻¹ ≤ 2 * nu⁻²` on `nu ≤ 1`. -/
private theorem nu_bookkeeping {nu : ℝ} (hnu : 0 < nu) (hnu1 : nu ≤ 1) :
    nu⁻¹ + nu⁻¹ ≤ 2 * nu ^ (-(2 : ℝ)) := by
  have hpow : nu ^ (-(2 : ℝ)) = nu⁻¹ * nu⁻¹ := by
    rw [Real.rpow_neg hnu.le, Real.rpow_two, sq, mul_inv]
  rw [hpow]
  have hle1 : (1 : ℝ) ≤ nu⁻¹ := (one_le_inv₀ hnu).mpr hnu1
  calc nu⁻¹ + nu⁻¹ = 2 * nu⁻¹ * 1 := by ring
    _ ≤ 2 * nu⁻¹ * nu⁻¹ := mul_le_mul_of_nonneg_left hle1 (by positivity)
    _ = 2 * (nu⁻¹ * nu⁻¹) := by ring

/-- **The restated `hAmpl` at the printed fixed scale — with an `m`-free
constant.**  The intermediate scale is *fixed* at the printed
`n' = ceil((n + h) / 2) = (n + h + 1) / 2` (the manuscript fixes it;
no quantifier over an intermediate scale), and the colouring is the `h`-scaled
residue colouring at level `n' - h`, with classes `O(3^(d (n' - h)))` and
spacing `d * 3^(n')`.  The hypothesis `h < n` is exactly the range
`h < n' ∧ n' ≤ n` evaluated at `m = n'`, and it matches the printed range.
The constant **`stepEAmplitudeConstMFree d` depends on `d` alone**. -/
theorem hAmpl_printedScale [NeZero d] {nu : ℝ} (hnu : 0 < nu) (hnu1 : nu ≤ 1) :
    ∀ h n : ℕ, h < n →
      gammaTriangleConst 2 * ((d : ℝ) * (d : ℝ)) *
        (gammaTriangleConst 2 * Homogenization.Book.Ch04.gammaSigmaIndependentSumConst 2 *
          (Real.sqrt ((descendantColorSet d ((n + h + 1) / 2 - h) n h).card : ℝ) *
            (Real.sqrt ((descendantsAtDepth (originCube d (n : ℤ)) (n - h)).card : ℝ) /
              ((descendantsAtDepth (originCube d (n : ℤ)) (n - h)).card : ℝ))) *
          (nu⁻¹ + nu⁻¹))
        ≤ stepEAmplitudeConstMFree d * nu ^ (-(2 : ℝ)) *
            (3 : ℝ) ^ (-(((n - h : ℕ) : ℝ) / 4)) := by
  intro h n hhn
  have hPle := stepEColorSet_amplitude_le (d := d) hhn
  have hnu2 := nu_bookkeeping hnu hnu1
  have hcore : (Real.sqrt ((descendantColorSet d ((n + h + 1) / 2 - h) n h).card : ℝ) *
        (Real.sqrt ((descendantsAtDepth (originCube d (n : ℤ)) (n - h)).card : ℝ) /
          ((descendantsAtDepth (originCube d (n : ℤ)) (n - h)).card : ℝ))) * (nu⁻¹ + nu⁻¹)
      ≤ 2 * stepEColorFactor d * nu ^ (-(2 : ℝ)) *
          (3 : ℝ) ^ (-(((n - h : ℕ) : ℝ) / 4)) := by
    calc _ ≤ (stepEColorFactor d * (3 : ℝ) ^ (-(((n - h : ℕ) : ℝ) / 4))) * (nu⁻¹ + nu⁻¹) :=
          mul_le_mul_of_nonneg_right hPle (by positivity)
      _ ≤ (stepEColorFactor d * (3 : ℝ) ^ (-(((n - h : ℕ) : ℝ) / 4))) *
            (2 * nu ^ (-(2 : ℝ))) :=
          mul_le_mul_of_nonneg_left hnu2
            (mul_nonneg (stepEColorFactor_nonneg d) (Real.rpow_nonneg (by norm_num) _))
      _ = 2 * stepEColorFactor d * nu ^ (-(2 : ℝ)) *
            (3 : ℝ) ^ (-(((n - h : ℕ) : ℝ) / 4)) := by ring
  have hB : 0 ≤ gammaTriangleConst 2 * ((d : ℝ) * (d : ℝ)) *
      (gammaTriangleConst 2 * Homogenization.Book.Ch04.gammaSigmaIndependentSumConst 2) :=
    mul_nonneg (mul_nonneg (le_of_lt Homogenization.IndependentSums.gammaTriangleConst_pos)
        (by positivity))
      (mul_nonneg (le_of_lt Homogenization.IndependentSums.gammaTriangleConst_pos)
        (le_of_lt SuperdiffusionCLT.Probability.gammaSigmaIndependentSumConst_two_pos))
  calc gammaTriangleConst 2 * ((d : ℝ) * (d : ℝ)) *
        (gammaTriangleConst 2 * Homogenization.Book.Ch04.gammaSigmaIndependentSumConst 2 *
          (Real.sqrt ((descendantColorSet d ((n + h + 1) / 2 - h) n h).card : ℝ) *
            (Real.sqrt ((descendantsAtDepth (originCube d (n : ℤ)) (n - h)).card : ℝ) /
              ((descendantsAtDepth (originCube d (n : ℤ)) (n - h)).card : ℝ))) *
          (nu⁻¹ + nu⁻¹))
      = (gammaTriangleConst 2 * ((d : ℝ) * (d : ℝ)) *
          (gammaTriangleConst 2 * Homogenization.Book.Ch04.gammaSigmaIndependentSumConst 2)) *
          ((Real.sqrt ((descendantColorSet d ((n + h + 1) / 2 - h) n h).card : ℝ) *
            (Real.sqrt ((descendantsAtDepth (originCube d (n : ℤ)) (n - h)).card : ℝ) /
              ((descendantsAtDepth (originCube d (n : ℤ)) (n - h)).card : ℝ))) * (nu⁻¹ + nu⁻¹)) := by
        ring
    _ ≤ (gammaTriangleConst 2 * ((d : ℝ) * (d : ℝ)) *
          (gammaTriangleConst 2 * Homogenization.Book.Ch04.gammaSigmaIndependentSumConst 2)) *
          (2 * stepEColorFactor d * nu ^ (-(2 : ℝ)) *
            (3 : ℝ) ^ (-(((n - h : ℕ) : ℝ) / 4))) :=
        mul_le_mul_of_nonneg_left hcore hB
    _ = stepEAmplitudeConstMFree d * nu ^ (-(2 : ℝ)) *
          (3 : ℝ) ^ (-(((n - h : ℕ) : ℝ) / 4)) := by
        rw [stepEAmplitudeConstMFree]
        ring

/-- **The printed-scale colour partition, the `hpart` of the entry-level Step-E estimate.**
The `h`-scaled colouring at level `n' - h` has nonempty, pairwise disjoint classes
that cover the depth-`(n - h)` descendants of `cu_n`, are `n'`-shell-separated, and
number at most `(descendantColorModulus d (n' - h))^d`.  The separation conjunct is
the printed-scale one (`areShellSeparated_of_stepEColor_eq`), not the
scale-`(n' - h)` one; the other five conjuncts are the lemmas of `DescendantColouring` at level
`n' - h`. -/
theorem stepEColorPartition_printed {d : ℕ} {n h : ℕ} (hhn : h < n) :
    (descendantColorSet d ((n + h + 1) / 2 - h) n h).Nonempty ∧
    ((descendantColorSet d ((n + h + 1) / 2 - h) n h :
        Set (Fin d → Fin (descendantColorModulus d ((n + h + 1) / 2 - h))))).PairwiseDisjoint
      (descendantColorClass d ((n + h + 1) / 2 - h) n h) ∧
    (descendantColorSet d ((n + h + 1) / 2 - h) n h).biUnion
        (descendantColorClass d ((n + h + 1) / 2 - h) n h) =
      descendantsAtDepth (originCube d (n : ℤ)) (n - h) ∧
    (∀ c ∈ descendantColorSet d ((n + h + 1) / 2 - h) n h,
      (descendantColorClass d ((n + h + 1) / 2 - h) n h c).Nonempty) ∧
    (∀ c ∈ descendantColorSet d ((n + h + 1) / 2 - h) n h,
      ∀ R ∈ descendantColorClass d ((n + h + 1) / 2 - h) n h c,
      ∀ S ∈ descendantColorClass d ((n + h + 1) / 2 - h) n h c, R ≠ S →
        ShellField.AreShellSeparated ((n + h + 1) / 2) (cubeSet R) (cubeSet S)) ∧
    (descendantColorSet d ((n + h + 1) / 2 - h) n h).card ≤
      (descendantColorModulus d ((n + h + 1) / 2 - h)) ^ d := by
  have hle : h ≤ n := le_of_lt hhn
  have hhm : h ≤ (n + h + 1) / 2 := by omega
  refine ⟨descendantColorSet_nonempty d ((n + h + 1) / 2 - h) n h,
    pairwiseDisjoint_descendantColorClass d ((n + h + 1) / 2 - h) n h,
    biUnion_descendantColorClass d ((n + h + 1) / 2 - h) n h,
    fun _ hc => exists_mem_of_mem_descendantColorSet hc, ?_,
    card_descendantColorSet_le d ((n + h + 1) / 2 - h) n h⟩
  intro c _ R hR S hS hne
  rw [mem_descendantColorClass_iff] at hR hS
  exact areShellSeparated_of_stepEColor_eq (d := d) (m := (n + h + 1) / 2) (h := h) hhm
    (scale_eq_of_mem_descendantsAtDepth_originCube hle hR.1)
    (scale_eq_of_mem_descendantsAtDepth_originCube hle hS.1) hne (hR.2.trans hS.2.symm)

end

end SuperdiffusionCLT.Section2.Annealed

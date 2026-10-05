/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Norms.MultiscalePoincareFullGradient
public import SuperdiffusionCLT.Section2.Cutoff.Finite
public import SuperdiffusionCLT.Probability.OrliczTriangle

/-!
# The hatted negative-norm estimate for a finite shell increment

The printed display `e.kmn.Wminussp`: for `n < m ≤ l`,

> `‖k_m - k_n‖_{Ŵ̲^{-s,p}(cu_l)} ≤ O_{Γ₂}(C 3^{s m})`.

The printed proof runs
`e.jk.spatialavg` → `e.apply.multiscale.Poincare` → the triangle inequality
over the shells `k ∈ (n, m]`, and this module realizes exactly that route.

## The route

1. `Section2.Norms.matHatNegENorm_finset_sum_le`: the amended norm is
   subadditive on finite sums of continuous matrix fields, so
   `k_m - k_n = ∑_{k ∈ (n,m]} j_k` splits into the shells.
2. `matHatNegENorm_le_cubeMultiscaleDepthSum`
   (in `MultiscalePoincareFullGradient`) bounds each shell by its
   printed depth sum `∑_j 3^{-sj} ((j_k)_j)^{1/p}` times `3^{s l}`.
3. `Section2.Norms.cubeMultiscaleDepthSumReal` is that depth sum as a real
   random variable; `Section2.Norms.summable_cubeMultiscaleDepthTerm` proves
   the defining series converges at every sample, so the `ℝ≥0∞` depth sum is
   its `ENNReal.ofReal`.
4. `isBigO_gammaSigma_cubeMultiscaleDepthSumReal_shell`: the depth sum of one
   shell has a `Γ₂` tail at amplitude `C(d,s,p) 3^{-s(l-k)}`. Every partial sum
   is a finite sum of the one-shell depth tails
   `isBigO_gammaSigma_rpow_cubeDepthPthMoment_shell`, and the amplitudes are
   summable with the geometric bound `tsum_depthWeight_le`; the passage from
   the partial sums to the series is `isBigOWith_of_tendsto_monotone`, the
   monotone-limit step of the printed proof, which is an increasing
   union of tail events and does not need the general infinite triangle
   inequality.
5. The shells are summed by the finite triangle inequality
   `isBigO_gammaSigma_finset_sum_of_one_le` and the geometric bound
   `sum_shellWeight_le`, producing the witness at amplitude
   `C(d,s,p) 3^{s m}` after the factor `3^{s l} · 3^{-s(l-m)} = 3^{s m}`.

## The constant

`incrementNegNormConst d s p` is explicit:

`(matHatNegBridgeConstant d).toReal * 16384 ^ 2 * cubeDepthMomentTailConst d p
  * depthGeomConst d s * shellGeomConst s`.

It depends on `d`, `s` and `p` only — never on `l`, `m`, `n` or on the law `P`
— which is what the scoping of the constant in
the statement of `l.ellip.k.scales.estimates` allows: there `C` is
introduced after `s` and after `p` and before `P` and before `l, m, n`.

## The exponent range

The bridge of step 2 needs `1 < p`, because the amended test class is indexed
by the conjugate exponent and the library chain is stated for a
`FiniteLpExponent`. The printed clause quantifies over `1 ≤ p`; the endpoint
`p = 1` is not covered here.

## Main definitions

* `depthGeomRatio`, `depthGeomConst`: the geometric data of the depth sum.
* `shellDepthTailConst`: the constant of the one-shell depth tail.
* `shellGeomConst`: the geometric constant of the shell sum.
* `incrementNegNormConst`: the constant of the clause.

## Main results

* `tsum_depthWeight_le`: `∑_j 3^{-sj} 3^{-(d/2)((r-j) ∨ 0)} ≤ C(d,s) 3^{-sr}`.
* `isBigOWith_of_tendsto_monotone`: an increasing pointwise limit of random
  variables with a common one-sided tail bound keeps that bound.
* `isBigO_gammaSigma_cubeMultiscaleDepthSumReal_shell`: the `Γ₂` tail of one
  shell's depth sum.
* `sum_shellWeight_le`: the geometric bound on the shell weights.
* `exists_witness_matHatNegENorm_finiteShellIncrement`: clause (a).
-/

@[expose] public section

namespace SuperdiffusionCLT
namespace Section2
namespace Estimates
namespace Stream

open Homogenization MeasureTheory Filter Topology
open Homogenization.Book.Ch02
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Norms
open scoped ENNReal
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}
variable {P : ProbabilityMeasure (ℕ → ShellField d)}

/-! ## The geometric data of the depth sum -/

/-- The geometric ratio of the depth sum: the larger of the two decay rates
which appear on the two sides of the shell scale, `3^{s - d/2}` below it and
`3^{-s}` above it. -/
def depthGeomRatio (d : ℕ) (s : ℝ) : ℝ :=
  max ((3 : ℝ) ^ (s - (d : ℝ) / 2)) ((3 : ℝ) ^ (-s))

theorem depthGeomRatio_pos (d : ℕ) (s : ℝ) : 0 < depthGeomRatio d s :=
  lt_of_lt_of_le (Real.rpow_pos_of_pos (by norm_num) _) (le_max_left _ _)

theorem depthGeomRatio_lt_one {s : ℝ} (hd : 2 ≤ d) (hs0 : 0 < s) (hs1 : s < 1) :
    depthGeomRatio d s < 1 := by
  have hdR : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have h1 : (3 : ℝ) ^ (s - (d : ℝ) / 2) < 1 := by
    refine Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) ?_
    linarith only [hdR, hs1]
  have h2 : (3 : ℝ) ^ (-s) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith only [hs0])
  exact max_lt h1 h2

/-- The constant of the depth sum: twice the sum of the geometric series with
ratio `depthGeomRatio d s`. -/
def depthGeomConst (d : ℕ) (s : ℝ) : ℝ :=
  2 * (1 - depthGeomRatio d s)⁻¹

theorem depthGeomConst_pos {s : ℝ} (hd : 2 ≤ d) (hs0 : 0 < s) (hs1 : s < 1) :
    0 < depthGeomConst d s := by
  have h := depthGeomRatio_lt_one (d := d) hd hs0 hs1
  have hpos : (0 : ℝ) < 1 - depthGeomRatio d s := by linarith only [h]
  simp only [depthGeomConst]
  positivity

private theorem depthWeight_eq_pow {s : ℝ} (r j : ℕ) :
    (3 : ℝ) ^ (-(s * (j : ℝ))) *
        (3 : ℝ) ^ (-((d : ℝ) / 2) * ((max ((r : ℤ) - (j : ℤ)) 0 : ℤ) : ℝ)) =
      ((3 : ℝ) ^ (-s)) ^ j * ((3 : ℝ) ^ (-((d : ℝ) / 2))) ^ (r - j) := by
  have hmax : ((max ((r : ℤ) - (j : ℤ)) 0 : ℤ) : ℝ) = (((r - j : ℕ) : ℕ) : ℝ) := by
    rcases le_or_gt j r with hjr | hjr
    · have h1 : (0 : ℤ) ≤ (r : ℤ) - (j : ℤ) := by
        have : (j : ℤ) ≤ (r : ℤ) := by exact_mod_cast hjr
        omega
      rw [max_eq_left h1]
      have : ((r - j : ℕ) : ℤ) = (r : ℤ) - (j : ℤ) := by omega
      exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) this.symm
    · have h1 : (r : ℤ) - (j : ℤ) ≤ 0 := by
        have : (r : ℤ) < (j : ℤ) := by exact_mod_cast hjr
        omega
      rw [max_eq_right h1]
      have : r - j = 0 := by omega
      rw [this]
      norm_num
  rw [hmax, neg_mul_eq_neg_mul, rpow_three_mul_natCast, rpow_three_mul_natCast]

/-- **The geometric bound on the depth weights.** The printed depth weights
`3^{-sj}` against the one-shell amplitudes
`3^{-(d/2)((r-j) ∨ 0)}` sum to `C(d,s) 3^{-sr}`: the decay below the shell
scale is `3^{-(d/2 - s)}` per depth and above it `3^{-s}` per depth. -/
theorem tsum_depthWeight_le {s : ℝ} (hd : 2 ≤ d) (hs0 : 0 < s) (hs1 : s < 1)
    (r : ℕ) :
    ∑' j : ℕ, (3 : ℝ) ^ (-(s * (j : ℝ))) *
        (3 : ℝ) ^ (-((d : ℝ) / 2) * ((max ((r : ℤ) - (j : ℤ)) 0 : ℤ) : ℝ)) ≤
      depthGeomConst d s * (3 : ℝ) ^ (-(s * (r : ℝ))) := by
  classical
  set alpha : ℝ := (3 : ℝ) ^ (-s) with halphadef
  set beta : ℝ := (3 : ℝ) ^ (-((d : ℝ) / 2)) with hbetadef
  set rho : ℝ := depthGeomRatio d s with hrhodef
  have halpha0 : 0 < alpha := Real.rpow_pos_of_pos (by norm_num) _
  have hbeta0 : 0 < beta := Real.rpow_pos_of_pos (by norm_num) _
  have hrho0 : 0 < rho := depthGeomRatio_pos d s
  have hrho1 : rho < 1 := depthGeomRatio_lt_one (d := d) hd hs0 hs1
  have halphaRho : alpha ≤ rho := le_max_right _ _
  have hbetaRho : beta ≤ alpha * rho := by
    have hstep : alpha * (3 : ℝ) ^ (s - (d : ℝ) / 2) = beta := by
      rw [halphadef, hbetadef, ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
      ring_nf
    calc beta = alpha * (3 : ℝ) ^ (s - (d : ℝ) / 2) := hstep.symm
      _ ≤ alpha * rho := by
          exact mul_le_mul_of_nonneg_left (le_max_left _ _) halpha0.le
  set f : ℕ → ℝ := fun j => alpha ^ j * beta ^ (r - j) with hfdef
  have hfnonneg : ∀ j, 0 ≤ f j := fun j => by positivity
  have hfle : ∀ j, f j ≤ alpha ^ j := by
    intro j
    have hb : beta ^ (r - j) ≤ 1 := by
      refine pow_le_one₀ hbeta0.le ?_
      rw [hbetadef]
      refine Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) ?_
      have : (0 : ℝ) ≤ (d : ℝ) / 2 := by positivity
      linarith only [this]
    calc f j = alpha ^ j * beta ^ (r - j) := rfl
      _ ≤ alpha ^ j * 1 := by
          exact mul_le_mul_of_nonneg_left hb (by positivity)
      _ = alpha ^ j := mul_one _
  have halphaSummable : Summable (fun j : ℕ => alpha ^ j) := by
    refine summable_geometric_of_lt_one halpha0.le ?_
    exact lt_of_le_of_lt halphaRho hrho1
  have hrhoSummable : Summable (fun j : ℕ => rho ^ j) :=
    summable_geometric_of_lt_one hrho0.le hrho1
  have hfSummable : Summable f :=
    Summable.of_nonneg_of_le hfnonneg hfle halphaSummable
  have hgeom : ∑' j : ℕ, rho ^ j = (1 - rho)⁻¹ :=
    tsum_geometric_of_lt_one hrho0.le hrho1
  have hhead : ∑ j ∈ Finset.range r, f j ≤ alpha ^ r * (1 - rho)⁻¹ := by
    have hterm : ∀ j ∈ Finset.range r, f j ≤ alpha ^ r * rho ^ (r - j) := by
      intro j hj
      have hjr : j ≤ r := le_of_lt (Finset.mem_range.mp hj)
      have hsplit : alpha ^ r = alpha ^ j * alpha ^ (r - j) := by
        rw [← pow_add]
        congr 1
        omega
      have hbpow : beta ^ (r - j) ≤ (alpha * rho) ^ (r - j) :=
        pow_le_pow_left₀ hbeta0.le hbetaRho _
      calc f j = alpha ^ j * beta ^ (r - j) := rfl
        _ ≤ alpha ^ j * (alpha * rho) ^ (r - j) := by
            exact mul_le_mul_of_nonneg_left hbpow (by positivity)
        _ = alpha ^ r * rho ^ (r - j) := by
            rw [mul_pow, hsplit]
            ring
    have hrefl : ∑ j ∈ Finset.range r, rho ^ (r - j) =
        ∑ j ∈ Finset.range r, rho ^ (j + 1) := by
      have := Finset.sum_range_reflect (fun j => rho ^ (r - j)) r
      rw [← this]
      refine Finset.sum_congr rfl fun j hj => ?_
      have hjr : j < r := Finset.mem_range.mp hj
      congr 1
      omega
    have hbound : ∑ j ∈ Finset.range r, rho ^ (j + 1) ≤ (1 - rho)⁻¹ := by
      have hle : ∑ j ∈ Finset.range r, rho ^ (j + 1) ≤
          ∑ j ∈ Finset.range r, rho ^ j := by
        refine Finset.sum_le_sum fun j _ => ?_
        exact pow_le_pow_of_le_one hrho0.le hrho1.le (by omega)
      refine le_trans hle ?_
      rw [← hgeom]
      exact hrhoSummable.sum_le_tsum _ (fun i _ => by positivity)
    calc ∑ j ∈ Finset.range r, f j
        ≤ ∑ j ∈ Finset.range r, alpha ^ r * rho ^ (r - j) :=
          Finset.sum_le_sum hterm
      _ = alpha ^ r * ∑ j ∈ Finset.range r, rho ^ (r - j) := by
          rw [Finset.mul_sum]
      _ = alpha ^ r * ∑ j ∈ Finset.range r, rho ^ (j + 1) := by rw [hrefl]
      _ ≤ alpha ^ r * (1 - rho)⁻¹ := by
          exact mul_le_mul_of_nonneg_left hbound (by positivity)
  have htail : ∑' i : ℕ, f (i + r) ≤ alpha ^ r * (1 - rho)⁻¹ := by
    have hterm : ∀ i : ℕ, f (i + r) ≤ alpha ^ r * rho ^ i := by
      intro i
      have hzero : r - (i + r) = 0 := by omega
      have hsplit : alpha ^ (i + r) = alpha ^ r * alpha ^ i := by
        rw [pow_add]
        ring
      have hpow : alpha ^ i ≤ rho ^ i := pow_le_pow_left₀ halpha0.le halphaRho i
      calc f (i + r) = alpha ^ (i + r) * beta ^ (r - (i + r)) := rfl
        _ = alpha ^ r * alpha ^ i := by rw [hzero, pow_zero, mul_one, hsplit]
        _ ≤ alpha ^ r * rho ^ i := by
            exact mul_le_mul_of_nonneg_left hpow (by positivity)
    have hshift : Summable (fun i : ℕ => f (i + r)) :=
      (summable_nat_add_iff r).2 hfSummable
    calc ∑' i : ℕ, f (i + r)
        ≤ ∑' i : ℕ, alpha ^ r * rho ^ i :=
          hshift.tsum_le_tsum hterm (hrhoSummable.mul_left _)
      _ = alpha ^ r * (1 - rho)⁻¹ := by rw [tsum_mul_left, hgeom]
  have hsplit := hfSummable.sum_add_tsum_nat_add r
  have hfeq : ∀ j : ℕ, (3 : ℝ) ^ (-(s * (j : ℝ))) *
      (3 : ℝ) ^ (-((d : ℝ) / 2) * ((max ((r : ℤ) - (j : ℤ)) 0 : ℤ) : ℝ)) = f j := by
    intro j
    rw [hfdef]
    exact depthWeight_eq_pow (d := d) (s := s) r j
  have halphar : alpha ^ r = (3 : ℝ) ^ (-(s * (r : ℝ))) := by
    rw [halphadef, ← rpow_three_mul_natCast, neg_mul_eq_neg_mul]
  calc ∑' j : ℕ, (3 : ℝ) ^ (-(s * (j : ℝ))) *
        (3 : ℝ) ^ (-((d : ℝ) / 2) * ((max ((r : ℤ) - (j : ℤ)) 0 : ℤ) : ℝ))
      = ∑' j : ℕ, f j := tsum_congr hfeq
    _ = (∑ j ∈ Finset.range r, f j) + ∑' i : ℕ, f (i + r) := hsplit.symm
    _ ≤ alpha ^ r * (1 - rho)⁻¹ + alpha ^ r * (1 - rho)⁻¹ :=
        add_le_add hhead htail
    _ = depthGeomConst d s * (3 : ℝ) ^ (-(s * (r : ℝ))) := by
        rw [depthGeomConst, ← hrhodef, ← halphar]
        ring

/-! ## The monotone limit of a one-sided tail bound -/

/-- **The monotone-limit step of the printed proof**. If `X n`
increases pointwise to `X` and every `X n` obeys the same one-sided tail bound,
then so does `X`: the tail event of `X` is the increasing union of the tail
events of the `X n`, and the measure of an increasing union is the limit of the
measures. This replaces the passage to the limit over partial sums in the
generalized triangle inequality, and needs no infinite-family triangle
inequality. -/
theorem isBigOWith_of_tendsto_monotone {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} [IsFiniteMeasure mu] {Psi : ℝ → ℝ}
    {Xn : ℕ → Omega → ℝ} {X : Omega → ℝ} {A : ℝ}
    (hmono : ∀ omega : Omega, Monotone fun n : ℕ => Xn n omega)
    (hlim : ∀ omega : Omega,
      Tendsto (fun n : ℕ => Xn n omega) atTop (nhds (X omega)))
    (hbig : ∀ n : ℕ, IndependentSums.IsBigOWith mu Psi (Xn n) A) :
    IndependentSums.IsBigOWith mu Psi X A := by
  intro t ht
  have hle : ∀ (n : ℕ) (omega : Omega), Xn n omega ≤ X omega := by
    intro n omega
    refine ge_of_tendsto (hlim omega) ?_
    filter_upwards [eventually_ge_atTop n] with m hm
    exact hmono omega hm
  have hmonoSet : Monotone fun n : ℕ =>
      IndependentSums.upperTailEvent (Xn n) (A * t) := by
    intro n m hnm omega homega
    exact lt_of_lt_of_le homega (hmono omega hnm)
  have hunion : IndependentSums.upperTailEvent X (A * t) =
      ⋃ n : ℕ, IndependentSums.upperTailEvent (Xn n) (A * t) := by
    ext omega
    simp only [Set.mem_iUnion, IndependentSums.mem_upperTailEvent]
    constructor
    · intro homega
      exact ((hlim omega).eventually (lt_mem_nhds homega)).exists
    · rintro ⟨n, hn⟩
      exact lt_of_lt_of_le hn (hle n omega)
  have htend := tendsto_measure_iUnion_atTop (μ := mu) hmonoSet
  have htendReal : Tendsto
      (fun n : ℕ =>
        (mu (IndependentSums.upperTailEvent (Xn n) (A * t))).toReal) atTop
      (nhds (mu (⋃ n : ℕ,
        IndependentSums.upperTailEvent (Xn n) (A * t))).toReal) :=
    (ENNReal.tendsto_toReal (measure_ne_top mu _)).comp htend
  show (mu (IndependentSums.upperTailEvent X (A * t))).toReal ≤ (Psi t)⁻¹
  rw [hunion]
  refine le_of_tendsto htendReal ?_
  filter_upwards with n
  exact hbig n ht

/-! ## The `Γ₂` tail of the depth sum of one shell -/

theorem summable_depthWeight {s : ℝ} (hs0 : 0 < s) (r : ℕ) :
    Summable (fun j : ℕ => (3 : ℝ) ^ (-(s * (j : ℝ))) *
      (3 : ℝ) ^ (-((d : ℝ) / 2) * ((max ((r : ℤ) - (j : ℤ)) 0 : ℤ) : ℝ))) := by
  have hle : ∀ j : ℕ, (3 : ℝ) ^ (-(s * (j : ℝ))) *
      (3 : ℝ) ^ (-((d : ℝ) / 2) * ((max ((r : ℤ) - (j : ℤ)) 0 : ℤ) : ℝ)) ≤
        ((3 : ℝ) ^ (-s)) ^ j := by
    intro j
    rw [depthWeight_eq_pow (d := d) (s := s) r j]
    have hb : ((3 : ℝ) ^ (-((d : ℝ) / 2))) ^ (r - j) ≤ 1 := by
      refine pow_le_one₀ (le_of_lt (Real.rpow_pos_of_pos (by norm_num) _)) ?_
      refine Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) ?_
      have : (0 : ℝ) ≤ (d : ℝ) / 2 := by positivity
      linarith only [this]
    calc ((3 : ℝ) ^ (-s)) ^ j * ((3 : ℝ) ^ (-((d : ℝ) / 2))) ^ (r - j)
        ≤ ((3 : ℝ) ^ (-s)) ^ j * 1 :=
          mul_le_mul_of_nonneg_left hb (by positivity)
      _ = ((3 : ℝ) ^ (-s)) ^ j := mul_one _
  refine Summable.of_nonneg_of_le (fun j => by positivity) hle ?_
  refine summable_geometric_of_lt_one (le_of_lt (Real.rpow_pos_of_pos (by norm_num) _)) ?_
  exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith only [hs0])

/-- The constant of the `Γ₂` tail of the depth sum of one shell: the finite
triangle prefactor `16384` times the constant of the one-shell depth
tail and the geometric constant of the depth weights. -/
def shellDepthTailConst (d : ℕ) (s p : ℝ) : ℝ :=
  16384 * (cubeDepthMomentTailConst d p * depthGeomConst d s)

theorem shellDepthTailConst_pos {s : ℝ} (hd : 2 ≤ d) (hs0 : 0 < s) (hs1 : s < 1)
    (p : ℝ) : 0 < shellDepthTailConst d s p := by
  have h1 : 0 < cubeDepthMomentTailConst d p :=
    cubeDepthMomentTailConst_pos (lt_of_lt_of_le (by norm_num) hd) p
  have h2 : 0 < depthGeomConst d s := depthGeomConst_pos (d := d) hd hs0 hs1
  simp only [shellDepthTailConst]
  positivity

/-- **The `Γ₂` tail of the depth sum of one shell.** The printed depth sum of
`j_k` on `cu_l` has a symmetric `Γ₂` tail at amplitude
`shellDepthTailConst d s p * 3^{-s(l-k)}`, the right-hand side of
`e.apply.multiscale.Poincare` after the prefactor `3^{-sl}`. -/
theorem isBigO_gammaSigma_cubeMultiscaleDepthSumReal_shell
    (hPrefix : ShellLawPrefix d P) (hJ1 : ShellLawJ1 d P) (hJ3 : ShellLawJ3 d P)
    (hJ4 : ShellLawJ4 d P) (k l : ℕ) (hkl : k ≤ l) {s p : ℝ}
    (hs0 : 0 < s) (hs1 : s < 1) (hp : 1 ≤ p) :
    IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma 2)
      (fun omega : ℕ → ShellField d =>
        cubeMultiscaleDepthSumReal (originCube d (l : ℤ)) s p
          (fun x => omega k x))
      (shellDepthTailConst d s p * (3 : ℝ) ^ (-(s * ((l - k : ℕ) : ℝ)))) := by
  classical
  have hd : 2 ≤ d := hPrefix.dimension
  have hd0 : 0 < d := lt_of_lt_of_le (by norm_num) hd
  have hp0 : (0 : ℝ) < p := lt_of_lt_of_le zero_lt_one hp
  set Q : TriadicCube d := originCube d (l : ℤ) with hQdef
  set r : ℕ := l - k with hrdef
  have hmaxeq : ∀ j : ℕ,
      ((max (Q.scale - (j : ℤ) - (k : ℤ)) 0 : ℤ) : ℝ) =
        ((max ((r : ℤ) - (j : ℤ)) 0 : ℤ) : ℝ) := by
    intro j
    have hQ : Q.scale = (l : ℤ) := rfl
    have hr : (r : ℤ) = (l : ℤ) - (k : ℤ) := by
      rw [hrdef]
      omega
    rw [hQ, hr]
    congr 2
    omega
  set weight : ℕ → ℝ := fun j =>
    (3 : ℝ) ^ (-(s * (j : ℝ))) *
      (3 : ℝ) ^ (-((d : ℝ) / 2) * ((max ((r : ℤ) - (j : ℤ)) 0 : ℤ) : ℝ)) with hwdef
  set amp : ℕ → ℝ := fun j => cubeDepthMomentTailConst d p * weight j with hampdef
  set term : ℕ → (ℕ → ShellField d) → ℝ := fun j omega =>
    (3 : ℝ) ^ (-(s * (j : ℝ))) *
      cubeDepthPthMoment Q j p (fun x => omega k x) ^ p⁻¹ with htermdef
  have hCtail : 0 < cubeDepthMomentTailConst d p :=
    cubeDepthMomentTailConst_pos hd0 p
  have hweightpos : ∀ j, 0 < weight j := by
    intro j
    rw [hwdef]
    exact mul_pos (Real.rpow_pos_of_pos (by norm_num) _)
      (Real.rpow_pos_of_pos (by norm_num) _)
  have hamppos : ∀ j, 0 < amp j := fun j => mul_pos hCtail (hweightpos j)
  have hbig : ∀ j : ℕ, IndependentSums.IsBigO P.toMeasure
      (IndependentSums.gammaSigma 2) (term j) (amp j) := by
    intro j
    have hbase := isBigO_gammaSigma_rpow_cubeDepthPthMoment_shell
      hPrefix hJ1 hJ3 hJ4 k Q j hp
    have hscaled := IndependentSums.IsBigO.const_mul
      (μ := P.toMeasure) (Ψ := IndependentSums.gammaSigma 2)
      (X := fun omega : ℕ → ShellField d =>
        cubeDepthPthMoment Q j p (fun x => omega k x) ^ p⁻¹)
      (A := cubeDepthMomentTailConst d p *
        (3 : ℝ) ^ (-((d : ℝ) / 2) *
          ((max (Q.scale - (j : ℤ) - (k : ℤ)) 0 : ℤ) : ℝ)))
      (c := (3 : ℝ) ^ (-(s * (j : ℝ))))
      (le_of_lt (Real.rpow_pos_of_pos (by norm_num) _)) hbase
    have hamp : (3 : ℝ) ^ (-(s * (j : ℝ))) *
        (cubeDepthMomentTailConst d p *
          (3 : ℝ) ^ (-((d : ℝ) / 2) *
            ((max (Q.scale - (j : ℤ) - (k : ℤ)) 0 : ℤ) : ℝ))) = amp j := by
      rw [hampdef, hwdef, hmaxeq j]
      ring
    rw [hamp] at hscaled
    exact hscaled
  have hmeas : ∀ j : ℕ, Measurable (term j) := by
    intro j
    rw [htermdef]
    exact measurable_const.mul
      ((Real.continuous_rpow_const (le_of_lt (inv_pos.2 hp0))).measurable.comp
        (measurable_cubeDepthPthMoment_shell Q j k hp0.le))
  have hampSummable : Summable amp := by
    rw [hampdef]
    exact (summable_depthWeight (d := d) hs0 r).mul_left _
  have hampBound : ∀ n : ℕ, ∑ j ∈ Finset.range (n + 1), amp j ≤
      cubeDepthMomentTailConst d p *
        (depthGeomConst d s * (3 : ℝ) ^ (-(s * (r : ℝ)))) := by
    intro n
    have hpart : ∑ j ∈ Finset.range (n + 1), amp j ≤ ∑' j : ℕ, amp j :=
      hampSummable.sum_le_tsum _ (fun j _ => (hamppos j).le)
    have htsum : ∑' j : ℕ, amp j =
        cubeDepthMomentTailConst d p * ∑' j : ℕ, weight j := by
      rw [hampdef, tsum_mul_left]
    refine le_trans hpart ?_
    rw [htsum]
    exact mul_le_mul_of_nonneg_left
      (tsum_depthWeight_le (d := d) hd hs0 hs1 r) hCtail.le
  have hpartial : ∀ n : ℕ, IndependentSums.IsBigOWith P.toMeasure
      (IndependentSums.gammaSigma 2)
      (fun omega : ℕ → ShellField d => ∑ j ∈ Finset.range (n + 1), term j omega)
      (shellDepthTailConst d s p * (3 : ℝ) ^ (-(s * (r : ℝ)))) := by
    intro n
    have htri := SuperdiffusionCLT.Probability.isBigO_gammaSigma_finset_sum_of_one_le
      (mu := P.toMeasure) (Finset.range (n + 1)) (X := term) (a := amp)
      (sigma := 2) (by norm_num) (Finset.nonempty_range_iff.mpr (by omega))
      (fun j _ => hamppos j) (fun j _ => hbig j) (fun j _ => hmeas j)
    have hmono := IndependentSums.IsBigO.mono_scale (μ := P.toMeasure)
      (Ψ := IndependentSums.gammaSigma 2)
      (X := fun omega : ℕ → ShellField d =>
        ∑ j ∈ Finset.range (n + 1), term j omega)
      (A := 16384 * ∑ j ∈ Finset.range (n + 1), amp j)
      (B := shellDepthTailConst d s p * (3 : ℝ) ^ (-(s * (r : ℝ)))) htri ?_
    · refine (SuperdiffusionCLT.Probability.isBigOWith_iff_isBigO_of_nonneg
        (fun omega => Finset.sum_nonneg fun j _ => ?_)).2 hmono
      rw [htermdef]
      exact cubeMultiscaleDepthTerm_nonneg Q s p (fun x => omega k x) j
    · rw [shellDepthTailConst]
      have := hampBound n
      have h16 : (0 : ℝ) ≤ 16384 := by norm_num
      calc 16384 * ∑ j ∈ Finset.range (n + 1), amp j
          ≤ 16384 * (cubeDepthMomentTailConst d p *
              (depthGeomConst d s * (3 : ℝ) ^ (-(s * (r : ℝ))))) :=
            mul_le_mul_of_nonneg_left this h16
        _ = 16384 * (cubeDepthMomentTailConst d p * depthGeomConst d s) *
              (3 : ℝ) ^ (-(s * (r : ℝ))) := by ring
  have hsummable : ∀ omega : ℕ → ShellField d,
      Summable (fun j : ℕ => term j omega) := by
    intro omega
    rw [htermdef]
    exact summable_cubeMultiscaleDepthTerm Q hs0 hp0 (omega k).1.1.continuous
  have hlim : ∀ omega : ℕ → ShellField d,
      Tendsto (fun n : ℕ => ∑ j ∈ Finset.range (n + 1), term j omega) atTop
        (nhds (cubeMultiscaleDepthSumReal Q s p (fun x => omega k x))) := by
    intro omega
    have h := (hsummable omega).hasSum.tendsto_sum_nat
    have h2 := h.comp (tendsto_add_atTop_nat 1)
    exact h2
  have hmonoPartial : ∀ omega : ℕ → ShellField d,
      Monotone fun n : ℕ => ∑ j ∈ Finset.range (n + 1), term j omega := by
    intro omega n m hnm
    have hsub : Finset.range (n + 1) ⊆ Finset.range (m + 1) := by
      intro x hx
      exact Finset.mem_range.mpr
        (lt_of_lt_of_le (Finset.mem_range.mp hx) (Nat.succ_le_succ hnm))
    refine Finset.sum_le_sum_of_subset_of_nonneg hsub ?_
    intro j _ _
    rw [htermdef]
    exact cubeMultiscaleDepthTerm_nonneg Q s p (fun x => omega k x) j
  have hlimit := isBigOWith_of_tendsto_monotone (mu := P.toMeasure)
    (Psi := IndependentSums.gammaSigma 2)
    (Xn := fun n omega => ∑ j ∈ Finset.range (n + 1), term j omega)
    (X := fun omega : ℕ → ShellField d =>
      cubeMultiscaleDepthSumReal Q s p (fun x => omega k x))
    (A := shellDepthTailConst d s p * (3 : ℝ) ^ (-(s * (r : ℝ))))
    hmonoPartial hlim hpartial
  exact (SuperdiffusionCLT.Probability.isBigOWith_iff_isBigO_of_nonneg
    (fun omega => cubeMultiscaleDepthSumReal_nonneg Q s p _)).1 hlimit

/-- The depth sum of one shell is measurable in the sample. -/
theorem measurable_cubeMultiscaleDepthSumReal_shell (Q : TriadicCube d) (k : ℕ)
    {s p : ℝ} (hs0 : 0 < s) (hp : 0 < p) :
    Measurable (fun omega : ℕ → ShellField d =>
      cubeMultiscaleDepthSumReal Q s p (fun x => omega k x)) := by
  refine measurable_of_tendsto_metrizable
    (f := fun n (omega : ℕ → ShellField d) =>
      ∑ j ∈ Finset.range (n + 1), (3 : ℝ) ^ (-(s * (j : ℝ))) *
        cubeDepthPthMoment Q j p (fun x => omega k x) ^ p⁻¹)
    (fun n => Finset.measurable_sum _ fun j _ =>
      measurable_const.mul
        ((Real.continuous_rpow_const (le_of_lt (inv_pos.2 hp))).measurable.comp
          (measurable_cubeDepthPthMoment_shell Q j k hp.le))) ?_
  refine tendsto_pi_nhds.2 fun omega => ?_
  have hsum := summable_cubeMultiscaleDepthTerm Q hs0 hp (omega k).1.1.continuous
  exact hsum.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)

/-! ## The shell weights -/

/-- The geometric constant of the shell sum. -/
def shellGeomConst (s : ℝ) : ℝ := (1 - (3 : ℝ) ^ (-s))⁻¹

/-- The shell weights of the printed sum `∑_{k = n+1}^{m}` are geometric in
`m - k`, so they sum to `C(s) 3^{-s(l-m)}`. -/
theorem sum_shellWeight_le {s : ℝ} (hs0 : 0 < s) (n m l : ℕ) (hml : m ≤ l) :
    ∑ k ∈ Finset.Ioc n m, (3 : ℝ) ^ (-(s * ((l - k : ℕ) : ℝ))) ≤
      shellGeomConst s * (3 : ℝ) ^ (-(s * ((l - m : ℕ) : ℝ))) := by
  classical
  set alpha : ℝ := (3 : ℝ) ^ (-s) with halphadef
  have halpha0 : 0 < alpha := Real.rpow_pos_of_pos (by norm_num) _
  have halpha1 : alpha < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith only [hs0])
  have hpow : ∀ j : ℕ, (3 : ℝ) ^ (-(s * (j : ℝ))) = alpha ^ j := by
    intro j
    rw [halphadef, ← rpow_three_mul_natCast, neg_mul_eq_neg_mul]
  have hstep : ∀ k ∈ Finset.Ioc n m,
      (3 : ℝ) ^ (-(s * ((l - k : ℕ) : ℝ))) = alpha ^ (l - m) * alpha ^ (m - k) := by
    intro k hk
    have hkm : k ≤ m := (Finset.mem_Ioc.mp hk).2
    have hsplit : l - k = (l - m) + (m - k) := by omega
    rw [hpow, hsplit, pow_add]
  have hsub : Finset.Ioc n m ⊆ Finset.range (m + 1) := by
    intro k hk
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.mem_Ioc.mp hk).2)
  have hrefl : ∑ k ∈ Finset.range (m + 1), alpha ^ (m - k) =
      ∑ k ∈ Finset.range (m + 1), alpha ^ k := by
    have := Finset.sum_range_reflect (fun j => alpha ^ (m - j)) (m + 1)
    rw [← this]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjm : j < m + 1 := Finset.mem_range.mp hj
    congr 1
    omega
  have hgeom : ∑ k ∈ Finset.range (m + 1), alpha ^ k ≤ shellGeomConst s := by
    have hsummable : Summable (fun k : ℕ => alpha ^ k) :=
      summable_geometric_of_lt_one halpha0.le halpha1
    have h := hsummable.sum_le_tsum (Finset.range (m + 1))
      (fun i _ => by positivity)
    rw [tsum_geometric_of_lt_one halpha0.le halpha1] at h
    exact h
  calc ∑ k ∈ Finset.Ioc n m, (3 : ℝ) ^ (-(s * ((l - k : ℕ) : ℝ)))
      = ∑ k ∈ Finset.Ioc n m, alpha ^ (l - m) * alpha ^ (m - k) :=
        Finset.sum_congr rfl hstep
    _ = alpha ^ (l - m) * ∑ k ∈ Finset.Ioc n m, alpha ^ (m - k) := by
        rw [Finset.mul_sum]
    _ ≤ alpha ^ (l - m) * ∑ k ∈ Finset.range (m + 1), alpha ^ (m - k) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun i _ _ => by positivity)
    _ = alpha ^ (l - m) * ∑ k ∈ Finset.range (m + 1), alpha ^ k := by rw [hrefl]
    _ ≤ alpha ^ (l - m) * shellGeomConst s := by
        exact mul_le_mul_of_nonneg_left hgeom (by positivity)
    _ = shellGeomConst s * (3 : ℝ) ^ (-(s * ((l - m : ℕ) : ℝ))) := by
        rw [hpow]
        ring

/-! ## Clause (a) -/

/-- The constant of the hatted negative-norm clause: the bridge constant of
`Section2/Norms/MultiscalePoincareFullGradient.lean`, the finite triangle prefactor of
the shell sum, the one-shell depth constant (which itself carries the depth
triangle prefactor) and the geometric constant of the shell weights. It depends
only on `d`, `s` and `p`. -/
def incrementNegNormConst (d : ℕ) (s p : ℝ) : ℝ :=
  (matHatNegBridgeConstant d).toReal *
    (16384 * (shellDepthTailConst d s p * shellGeomConst s))

/-- **The hatted negative-norm estimate on `k_m - k_n`**, display
`e.kmn.Wminussp`: for `n < m ≤ l` there is a measurable
witness with a symmetric `Γ₂` tail at amplitude
`incrementNegNormConst d s p * 3^{s m}` which dominates the amended hatted
negative norm of the increment on `cu_l` at every sample. -/
theorem exists_witness_matHatNegENorm_finiteShellIncrement
    (hPrefix : ShellLawPrefix d P) (hJ1 : ShellLawJ1 d P) (hJ3 : ShellLawJ3 d P)
    (hJ4 : ShellLawJ4 d P) {s p : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (hp : 1 < p)
    {l m n : ℕ} (hnm : n < m) (hml : m ≤ l) :
    ∃ X : (ℕ → ShellField d) → ℝ, Measurable X ∧
      IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma 2) X
        (incrementNegNormConst d s p * (3 : ℝ) ^ (s * (m : ℝ))) ∧
      ∀ omega : ℕ → ShellField d,
        matHatNegENorm (originCube d (l : ℤ)) s (ENNReal.ofReal p)
          (fun x => Cutoff.finiteShellIncrement omega n m x) ≤
          ENNReal.ofReal (X omega) := by
  classical
  have hd : 2 ≤ d := hPrefix.dimension
  have hp0 : (0 : ℝ) < p := lt_trans zero_lt_one hp
  have hp1 : (1 : ℝ) ≤ p := hp.le
  set Q : TriadicCube d := originCube d (l : ℤ) with hQdef
  set Cb : ℝ := (matHatNegBridgeConstant d).toReal with hCbdef
  have hCb0 : 0 ≤ Cb := ENNReal.toReal_nonneg
  have hCbEq : ENNReal.ofReal Cb = matHatNegBridgeConstant d :=
    ENNReal.ofReal_toReal (ne_of_lt (matHatNegBridgeConstant_lt_top d))
  set Y : ℕ → (ℕ → ShellField d) → ℝ := fun k omega =>
    cubeMultiscaleDepthSumReal Q s p (fun x => omega k x) with hYdef
  set scale : ℝ := Cb * (3 : ℝ) ^ (s * (l : ℝ)) with hscaledef
  have hscale0 : 0 ≤ scale := by
    rw [hscaledef]
    have : (0 : ℝ) < (3 : ℝ) ^ (s * (l : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
    positivity
  refine ⟨fun omega => scale * ∑ k ∈ Finset.Ioc n m, Y k omega, ?_, ?_, ?_⟩
  · refine measurable_const.mul (Finset.measurable_sum _ fun k _ => ?_)
    exact measurable_cubeMultiscaleDepthSumReal_shell Q k hs0 hp0
  · have hamp : ∀ k ∈ Finset.Ioc n m, (0 : ℝ) <
        shellDepthTailConst d s p * (3 : ℝ) ^ (-(s * ((l - k : ℕ) : ℝ))) := by
      intro k _
      have h1 : 0 < shellDepthTailConst d s p :=
        shellDepthTailConst_pos (d := d) hd hs0 hs1 p
      have h2 : (0 : ℝ) < (3 : ℝ) ^ (-(s * ((l - k : ℕ) : ℝ))) :=
        Real.rpow_pos_of_pos (by norm_num) _
      positivity
    have hbig : ∀ k ∈ Finset.Ioc n m,
        IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma 2) (Y k)
          (shellDepthTailConst d s p * (3 : ℝ) ^ (-(s * ((l - k : ℕ) : ℝ)))) := by
      intro k hk
      have hkl : k ≤ l := le_trans (Finset.mem_Ioc.mp hk).2 hml
      exact isBigO_gammaSigma_cubeMultiscaleDepthSumReal_shell hPrefix hJ1 hJ3
        hJ4 k l hkl hs0 hs1 hp1
    have hmeas : ∀ k ∈ Finset.Ioc n m, Measurable (Y k) := fun k _ =>
      measurable_cubeMultiscaleDepthSumReal_shell Q k hs0 hp0
    have htri := SuperdiffusionCLT.Probability.isBigO_gammaSigma_finset_sum_of_one_le
      (mu := P.toMeasure) (Finset.Ioc n m) (X := Y)
      (a := fun k => shellDepthTailConst d s p *
        (3 : ℝ) ^ (-(s * ((l - k : ℕ) : ℝ)))) (sigma := 2) (by norm_num)
      ⟨m, Finset.mem_Ioc.mpr ⟨hnm, le_rfl⟩⟩ hamp hbig hmeas
    have hscaled := IndependentSums.IsBigO.const_mul
      (μ := P.toMeasure) (Ψ := IndependentSums.gammaSigma 2)
      (X := fun omega => ∑ k ∈ Finset.Ioc n m, Y k omega)
      (A := 16384 * ∑ k ∈ Finset.Ioc n m, shellDepthTailConst d s p *
        (3 : ℝ) ^ (-(s * ((l - k : ℕ) : ℝ))))
      (c := scale) hscale0 htri
    refine IndependentSums.IsBigO.mono_scale (μ := P.toMeasure) hscaled ?_
    have hsumle : ∑ k ∈ Finset.Ioc n m, shellDepthTailConst d s p *
        (3 : ℝ) ^ (-(s * ((l - k : ℕ) : ℝ))) ≤
        shellDepthTailConst d s p *
          (shellGeomConst s * (3 : ℝ) ^ (-(s * ((l - m : ℕ) : ℝ)))) := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (sum_shellWeight_le hs0 n m l hml)
        (shellDepthTailConst_pos (d := d) hd hs0 hs1 p).le
    have hprod : (3 : ℝ) ^ (s * (l : ℝ)) * (3 : ℝ) ^ (-(s * ((l - m : ℕ) : ℝ))) =
        (3 : ℝ) ^ (s * (m : ℝ)) := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
      congr 1
      have hcast : ((l - m : ℕ) : ℝ) = (l : ℝ) - (m : ℝ) := by
        have : (m : ℝ) ≤ (l : ℝ) := by exact_mod_cast hml
        rw [Nat.cast_sub hml]
      rw [hcast]
      ring
    calc scale * (16384 * ∑ k ∈ Finset.Ioc n m, shellDepthTailConst d s p *
          (3 : ℝ) ^ (-(s * ((l - k : ℕ) : ℝ))))
        ≤ scale * (16384 * (shellDepthTailConst d s p *
            (shellGeomConst s * (3 : ℝ) ^ (-(s * ((l - m : ℕ) : ℝ)))))) := by
          refine mul_le_mul_of_nonneg_left ?_ hscale0
          exact mul_le_mul_of_nonneg_left hsumle (by norm_num)
      _ = incrementNegNormConst d s p * (3 : ℝ) ^ (s * (m : ℝ)) := by
          rw [incrementNegNormConst, hscaledef, ← hprod, ← hCbdef]
          ring
  · intro omega
    have hcont : ∀ k : ℕ, Continuous (fun x : Vec d => omega k x) :=
      fun k => (omega k).1.1.continuous
    have hfield : (fun x : Vec d => Cutoff.finiteShellIncrement omega n m x) =
        fun x : Vec d => ∑ k ∈ Finset.Ioc n m, (fun y : Vec d => omega k y) x := by
      funext x
      rw [Cutoff.finiteShellIncrement_apply]
      rfl
    have hsub := matHatNegENorm_finset_sum_le (Q := Q) (s := s)
      (p := ENNReal.ofReal p) (Finset.Ioc n m)
      (fun k => fun x : Vec d => omega k x) (fun k _ => hcont k)
    have hbridge : ∀ k : ℕ,
        matHatNegENorm Q s (ENNReal.ofReal p) (fun x : Vec d => omega k x) ≤
          ENNReal.ofReal (scale * Y k omega) := by
      intro k
      have h := matHatNegENorm_le_cubeMultiscaleDepthSum Q hs0 hs1 hp (hcont k)
      have hQscale : ((Q.scale : ℤ) : ℝ) = (l : ℝ) := by
        have hs : Q.scale = (l : ℤ) := rfl
        rw [hs, Int.cast_natCast]
      rw [hQscale] at h
      refine le_trans h (le_of_eq ?_)
      rw [hscaledef, hYdef,
        ← ofReal_cubeMultiscaleDepthSumReal Q hs0 hp0 (hcont k),
        ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul hCb0, hCbEq]
    calc matHatNegENorm Q s (ENNReal.ofReal p)
          (fun x => Cutoff.finiteShellIncrement omega n m x)
        = matHatNegENorm Q s (ENNReal.ofReal p)
            (fun x => ∑ k ∈ Finset.Ioc n m, (fun y : Vec d => omega k y) x) := by
          rw [hfield]
      _ ≤ ∑ k ∈ Finset.Ioc n m,
            matHatNegENorm Q s (ENNReal.ofReal p)
              (fun x : Vec d => omega k x) := hsub
      _ ≤ ∑ k ∈ Finset.Ioc n m, ENNReal.ofReal (scale * Y k omega) :=
          Finset.sum_le_sum fun k _ => hbridge k
      _ = ENNReal.ofReal (∑ k ∈ Finset.Ioc n m, scale * Y k omega) := by
          rw [ENNReal.ofReal_sum_of_nonneg]
          intro k _
          exact mul_nonneg hscale0 (cubeMultiscaleDepthSumReal_nonneg Q s p _)
      _ = ENNReal.ofReal (scale * ∑ k ∈ Finset.Ioc n m, Y k omega) := by
          rw [Finset.mul_sum]

end

end Stream
end Estimates
end Section2
end SuperdiffusionCLT

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Norms.FractionalHs
public import Homogenization.Sobolev.Fractional.ContinuousInterpolation.UnitCubeGeometry

/-!
# The oscillation kernel estimate behind the `H^s` clause

The paper bounds the Gagliardo
part of the normalized fractional norm of one shell by the kernel integral

> `[j_k]²_{H̲^s(cu_l)} ≤ C ⨍_{cu_l} ∫_{cu_l} |j_k(x) − j_k(y)|² |x−y|^{−d−2s} dx dy`
> `                    ≤ C ⨍_{cu_l} ∫_{cu_l} min{1, 3^{−k}|x−y|}² |x−y|^{−d−2s} dx dy`
> `                    ≤ C 3^{−2sk}`,

the last inequality being the deterministic content: for a field whose
oscillation on the cube is at most `2A` and which is Lipschitz on the cube with
constant `B`, the two branches of `min{2A, B|x−y|}` cross at the radius
`|x−y| = 2A/B`, and integrating the kernel `|x−y|^{−d−2s}` against the two
branches gives `C(d,s) A^{2−2s} B^{2s}`; with `A = O(1)` and `B = O(3^{−k})`
this is the printed `C 3^{−2sk}`.

This module supplies that deterministic estimate for the carrier
`Section2.Norms.cubeEuclideanGagliardoESeminorm` at exponent `2`, with an
explicit constant.

## What is proved and what is not

The estimate proved here is
`cubeEuclideanGagliardoESeminorm_le_of_oscillation_lipschitz`: the seminorm of
a field with oscillation `≤ 2A` and Lipschitz constant `B` on the cube is at
most `√(gagliardoOscillationConst d s) (2A)^{1−s} ((d+1)B)^s`. It is the
`k`-uniform and `l`-uniform deterministic input of the `H^s` clause of
`Frozen.Section2.streamIncrement_scale_estimates`; the probabilistic
one-shell display and the shell sum of that clause are not proved here.

The constant keeps track of two dimensional losses that the print suppresses.
First, the paper's `|·|` is the Euclidean magnitude
`Homogenization.euclideanDist`, while `Vec d` carries the ambient sup norm; the
comparison used is `‖x−y‖ ≤ euclideanDist x y ≤ d ‖x−y‖` (the lemmas
`Homogenization.norm_le_euclideanNorm` and
`Homogenization.euclideanDist_le_dimension_mul_dist`), so the Lipschitz
constant enters as `(d+1)B` — `d+1` rather than `d` only so that the factor is
positive in dimension zero, where the seminorm vanishes anyway. Second, the
region decomposition is by sup-norm annuli, whose Lebesgue volume
`(2r)^d` is exact (`Real.volume_pi_closedBall`), rather than by Euclidean
spheres; this contributes the factor `2^{2d}` of the constant.

## The shape of the argument

* `gagliardoOscillationConst`: the explicit constant, the sum of the two
  geometric series of the annulus decomposition.
* the near annuli `T/2^{j+1} < ‖z‖ ≤ T/2^j` carry the Lipschitz branch of the
  `min`, and their contributions form a geometric series of ratio `2^{2s−2}`,
  summable because `s < 1`;
* the far annuli `T 2^j < ‖z‖ ≤ T 2^{j+1}` carry the oscillation branch, and
  their contributions form a geometric series of ratio `2^{−2s}`, summable
  because `s > 0`;
* the diagonal `‖z‖ = 0` contributes nothing: `Real.rpow` sends `0` to `0` at
  a nonzero exponent, so the Gagliardo kernel vanishes there rather than being
  undefined.

## Main definitions

* `gagliardoOscillationConst`.

## Main results

* `cubeEuclideanGagliardoESeminorm_le_of_oscillation_lipschitz`: the kernel
  estimate for the Gagliardo carrier.
* `cubeEuclideanGagliardoESeminorm_le_of_sup_lipschitz`: the same, read off a
  sup bound instead of an oscillation bound.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section2.Estimates.Stream

open MeasureTheory
open Homogenization
open SuperdiffusionCLT.Section2.Norms
open scoped ENNReal

noncomputable section

/-- The explicit dimensional constant of the kernel estimate below: the value
of the two geometric series produced by the triadic-free dyadic decomposition
of `ℝ^d` into the annuli `2^j T < ‖z‖ ≤ 2^{j+1} T`, `T` the crossing radius of
the two branches of `min`. Both denominators are positive for `s ∈ (0,1)`. -/
noncomputable def gagliardoOscillationConst (d : ℕ) (s : ℝ) : ℝ :=
  (2 : ℝ) ^ (2 * (d : ℝ)) *
    ((2 : ℝ) ^ (2 * s) * (1 - (2 : ℝ) ^ (2 * s - 2))⁻¹ +
      (1 - (2 : ℝ) ^ (-(2 * s)))⁻¹)

private theorem two_rpow_lt_one {c : ℝ} (hc : c < 0) : (2 : ℝ) ^ c < 1 :=
  Real.rpow_lt_one_of_one_lt_of_neg one_lt_two hc

private theorem rpow_two_eq_sq (t : ℝ) : t ^ (2 : ℝ) = t ^ (2 : ℕ) := by
  rw [← Real.rpow_natCast t 2]
  norm_num

private theorem rpow_natCast_eq_pow (t : ℝ) (n : ℕ) : t ^ ((n : ℕ) : ℝ) = t ^ n :=
  Real.rpow_natCast t n

/-- The scaling identity for one near annulus. -/
private theorem near_annulus_value (d : ℕ) {s b t : ℝ} (ht : 0 < t) :
    (b * t) ^ 2 * (t / 2) ^ (-(2 * s + (d : ℝ))) * ((2 : ℝ) * t) ^ d
      = b ^ 2 * (2 : ℝ) ^ (2 * s + 2 * (d : ℝ)) * t ^ (2 - 2 * s) := by
  have h2 : (0 : ℝ) < 2 := two_pos
  have e1 : ((2 : ℝ) * t) ^ d = (2 : ℝ) ^ ((d : ℝ)) * t ^ ((d : ℝ)) := by
    rw [rpow_natCast_eq_pow, rpow_natCast_eq_pow, mul_pow]
  have e2 : (t / 2) ^ (-(2 * s + (d : ℝ)))
      = t ^ (-(2 * s + (d : ℝ))) * (2 : ℝ) ^ (2 * s + (d : ℝ)) := by
    rw [Real.div_rpow ht.le h2.le, Real.rpow_neg h2.le, div_inv_eq_mul]
  have e3 : (b * t) ^ 2 = b ^ 2 * t ^ (2 : ℝ) := by
    rw [rpow_two_eq_sq, mul_pow]
  have hcollect : t ^ (2 : ℝ) * (t ^ (-(2 * s + (d : ℝ))) * t ^ ((d : ℝ)))
      = t ^ (2 - 2 * s) := by
    rw [← Real.rpow_add ht, ← Real.rpow_add ht]
    ring_nf
  have h2collect : (2 : ℝ) ^ (2 * s + (d : ℝ)) * (2 : ℝ) ^ ((d : ℝ))
      = (2 : ℝ) ^ (2 * s + 2 * (d : ℝ)) := by
    rw [← Real.rpow_add h2]
    ring_nf
  rw [e1, e2, e3]
  calc
    b ^ 2 * t ^ (2 : ℝ) *
        (t ^ (-(2 * s + (d : ℝ))) * (2 : ℝ) ^ (2 * s + (d : ℝ))) *
        ((2 : ℝ) ^ ((d : ℝ)) * t ^ ((d : ℝ)))
        = b ^ 2 *
            ((2 : ℝ) ^ (2 * s + (d : ℝ)) * (2 : ℝ) ^ ((d : ℝ))) *
            (t ^ (2 : ℝ) * (t ^ (-(2 * s + (d : ℝ))) * t ^ ((d : ℝ)))) := by
          ring
    _ = b ^ 2 * (2 : ℝ) ^ (2 * s + 2 * (d : ℝ)) * t ^ (2 - 2 * s) := by
          rw [hcollect, h2collect]

/-- The scaling identity for one far annulus. -/
private theorem far_annulus_value (d : ℕ) {s a t : ℝ} (ht : 0 < t) :
    a ^ 2 * t ^ (-(2 * s + (d : ℝ))) * ((2 : ℝ) * (2 * t)) ^ d
      = a ^ 2 * (2 : ℝ) ^ (2 * (d : ℝ)) * t ^ (-(2 * s)) := by
  have h2 : (0 : ℝ) < 2 := two_pos
  have hfour : ((2 : ℝ) * (2 * t)) ^ d
      = ((2 : ℝ) ^ (2 * (d : ℝ))) * t ^ ((d : ℝ)) := by
    have h4 : ((2 : ℝ) * (2 * t)) ^ d = ((2 : ℝ) ^ (2 : ℕ)) ^ d * t ^ d := by
      rw [show (2 : ℝ) * (2 * t) = (2 : ℝ) ^ (2 : ℕ) * t by ring, mul_pow]
    rw [h4, ← pow_mul, rpow_natCast_eq_pow t d, ← rpow_natCast_eq_pow (2 : ℝ) (2 * d)]
    congr 2
    push_cast
    ring
  rw [hfour]
  have hcollect : t ^ (-(2 * s + (d : ℝ))) * t ^ ((d : ℝ)) = t ^ (-(2 * s)) := by
    rw [← Real.rpow_add ht]
    ring_nf
  calc
    a ^ 2 * t ^ (-(2 * s + (d : ℝ))) * ((2 : ℝ) ^ (2 * (d : ℝ)) * t ^ ((d : ℝ)))
        = a ^ 2 * (2 : ℝ) ^ (2 * (d : ℝ)) *
            (t ^ (-(2 * s + (d : ℝ))) * t ^ ((d : ℝ))) := by ring
    _ = a ^ 2 * (2 : ℝ) ^ (2 * (d : ℝ)) * t ^ (-(2 * s)) := by rw [hcollect]

private theorem pow_two_rpow (c : ℝ) (j : ℕ) : ((2 : ℝ) ^ j) ^ c = ((2 : ℝ) ^ c) ^ j := by
  rw [← rpow_natCast_eq_pow (2 : ℝ) j, ← Real.rpow_mul (by norm_num), mul_comm,
    Real.rpow_mul (by norm_num), rpow_natCast_eq_pow]

private theorem near_radius_rpow {T : ℝ} (hT : 0 < T) (s : ℝ) (j : ℕ) :
    (T / 2 ^ j) ^ (2 - 2 * s) = T ^ (2 - 2 * s) * ((2 : ℝ) ^ (2 * s - 2)) ^ j := by
  have hexp : -(2 - 2 * s) = 2 * s - 2 := by ring
  rw [Real.div_rpow hT.le (by positivity), div_eq_mul_inv,
    ← Real.rpow_neg (by positivity), pow_two_rpow, hexp]

private theorem far_radius_rpow {T : ℝ} (hT : 0 < T) (s : ℝ) (j : ℕ) :
    (T * 2 ^ j) ^ (-(2 * s)) = T ^ (-(2 * s)) * ((2 : ℝ) ^ (-(2 * s))) ^ j := by
  rw [Real.mul_rpow hT.le (by positivity), pow_two_rpow]

private theorem coeff_near {a b s : ℝ} (ha : 0 < a) (hb : 0 < b) :
    b ^ 2 * (a / b) ^ (2 - 2 * s) = a ^ (2 - 2 * s) * b ^ (2 * s) := by
  have h1 : (a / b) ^ (2 - 2 * s) = a ^ (2 - 2 * s) * b ^ (-(2 - 2 * s)) := by
    rw [Real.div_rpow ha.le hb.le, Real.rpow_neg hb.le, div_eq_mul_inv]
  have hexp : (2 : ℝ) + -(2 - 2 * s) = 2 * s := by ring
  rw [h1, ← rpow_two_eq_sq b,
    show b ^ (2 : ℝ) * (a ^ (2 - 2 * s) * b ^ (-(2 - 2 * s)))
      = a ^ (2 - 2 * s) * (b ^ (2 : ℝ) * b ^ (-(2 - 2 * s))) by ring,
    ← Real.rpow_add hb, hexp]

private theorem coeff_far {a b s : ℝ} (ha : 0 < a) (hb : 0 < b) :
    a ^ 2 * (a / b) ^ (-(2 * s)) = a ^ (2 - 2 * s) * b ^ (2 * s) := by
  have h1 : (a / b) ^ (-(2 * s)) = a ^ (-(2 * s)) * b ^ (2 * s) := by
    rw [Real.div_rpow ha.le hb.le, Real.rpow_neg ha.le, Real.rpow_neg hb.le,
      div_eq_mul_inv, inv_inv]
  have hexp : (2 : ℝ) + -(2 * s) = 2 - 2 * s := by ring
  rw [h1, ← rpow_two_eq_sq a,
    show a ^ (2 : ℝ) * (a ^ (-(2 * s)) * b ^ (2 * s))
      = a ^ (2 : ℝ) * a ^ (-(2 * s)) * b ^ (2 * s) by ring,
    ← Real.rpow_add ha, hexp]

/-- The radial majorant integrand. -/
noncomputable def radialIntegrand (d : ℕ) (s a b : ℝ) (z : Vec d) : ℝ≥0∞ :=
  ENNReal.ofReal (min a (b * ‖z‖) ^ 2 * ‖z‖ ^ (-(2 * s + (d : ℝ))))

private def nearAnnulus (d : ℕ) (T : ℝ) (j : ℕ) : Set (Vec d) :=
  {z : Vec d | T / 2 ^ (j + 1) < ‖z‖ ∧ ‖z‖ ≤ T / 2 ^ j}

private def farAnnulus (d : ℕ) (T : ℝ) (j : ℕ) : Set (Vec d) :=
  {z : Vec d | T * 2 ^ j < ‖z‖ ∧ ‖z‖ ≤ T * 2 ^ (j + 1)}

private theorem volume_closedBall_vec (d : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    MeasureTheory.volume (Metric.closedBall (0 : Vec d) r)
      = ENNReal.ofReal ((2 * r) ^ d) := by
  rw [Real.volume_pi_closedBall (0 : Vec d) hr, Fintype.card_fin]

private theorem lintegral_nearAnnulus_le (d : ℕ) {s a b : ℝ} (hs : 0 < s)
    (ha : 0 < a) (hb : 0 < b) (j : ℕ) :
    ∫⁻ z : Vec d in nearAnnulus d (a / b) j, radialIntegrand d s a b z
      ≤ ENNReal.ofReal (a ^ (2 - 2 * s) * b ^ (2 * s) *
          (2 : ℝ) ^ (2 * s + 2 * (d : ℝ)) * ((2 : ℝ) ^ (2 * s - 2)) ^ j) := by
  have hTpos : (0 : ℝ) < a / b := div_pos ha hb
  have htpos : (0 : ℝ) < a / b / 2 ^ j := by positivity
  have hhalf : a / b / 2 ^ (j + 1) = (a / b / 2 ^ j) / 2 := by
    rw [pow_succ]
    ring
  have hexpnp : -(2 * s + (d : ℝ)) ≤ 0 := by
    have : (0 : ℝ) ≤ 2 * s + (d : ℝ) := by positivity
    linarith only [this]
  have hbound : ∀ z ∈ nearAnnulus d (a / b) j, radialIntegrand d s a b z ≤
      ENNReal.ofReal ((b * (a / b / 2 ^ j)) ^ 2 *
        ((a / b / 2 ^ j) / 2) ^ (-(2 * s + (d : ℝ)))) := by
    rintro z ⟨hz1, hz2⟩
    rw [hhalf] at hz1
    refine ENNReal.ofReal_le_ofReal (mul_le_mul ?_ ?_ ?_ ?_)
    · refine pow_le_pow_left₀ (le_min ha.le (by positivity)) ?_ 2
      exact (min_le_right _ _).trans (by nlinarith only [hz2, hb.le, norm_nonneg z])
    · exact Real.rpow_le_rpow_of_nonpos (by positivity) hz1.le hexpnp
    · exact Real.rpow_nonneg (norm_nonneg z) _
    · positivity
  calc ∫⁻ z : Vec d in nearAnnulus d (a / b) j, radialIntegrand d s a b z
      ≤ ∫⁻ _z : Vec d in nearAnnulus d (a / b) j,
          ENNReal.ofReal ((b * (a / b / 2 ^ j)) ^ 2 *
            ((a / b / 2 ^ j) / 2) ^ (-(2 * s + (d : ℝ)))) :=
        setLIntegral_mono measurable_const hbound
    _ = ENNReal.ofReal ((b * (a / b / 2 ^ j)) ^ 2 *
            ((a / b / 2 ^ j) / 2) ^ (-(2 * s + (d : ℝ)))) *
          MeasureTheory.volume (nearAnnulus d (a / b) j) := setLIntegral_const _ _
    _ ≤ ENNReal.ofReal ((b * (a / b / 2 ^ j)) ^ 2 *
            ((a / b / 2 ^ j) / 2) ^ (-(2 * s + (d : ℝ)))) *
          MeasureTheory.volume (Metric.closedBall (0 : Vec d) (a / b / 2 ^ j)) := by
        refine mul_le_mul_right (measure_mono ?_) _
        rintro z ⟨_, hz2⟩
        simpa only [Metric.mem_closedBall, dist_zero_right] using hz2
    _ = ENNReal.ofReal ((b * (a / b / 2 ^ j)) ^ 2 *
            ((a / b / 2 ^ j) / 2) ^ (-(2 * s + (d : ℝ)))) *
          ENNReal.ofReal ((2 * (a / b / 2 ^ j)) ^ d) := by
        rw [volume_closedBall_vec d htpos.le]
    _ = ENNReal.ofReal ((b * (a / b / 2 ^ j)) ^ 2 *
            ((a / b / 2 ^ j) / 2) ^ (-(2 * s + (d : ℝ))) *
            (2 * (a / b / 2 ^ j)) ^ d) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
    _ = ENNReal.ofReal (a ^ (2 - 2 * s) * b ^ (2 * s) *
          (2 : ℝ) ^ (2 * s + 2 * (d : ℝ)) * ((2 : ℝ) ^ (2 * s - 2)) ^ j) := by
        rw [near_annulus_value d htpos, near_radius_rpow hTpos s j]
        congr 1
        rw [← coeff_near ha hb]
        ring

private theorem lintegral_farAnnulus_le (d : ℕ) {s a b : ℝ} (hs : 0 < s)
    (ha : 0 < a) (hb : 0 < b) (j : ℕ) :
    ∫⁻ z : Vec d in farAnnulus d (a / b) j, radialIntegrand d s a b z
      ≤ ENNReal.ofReal (a ^ (2 - 2 * s) * b ^ (2 * s) *
          (2 : ℝ) ^ (2 * (d : ℝ)) * ((2 : ℝ) ^ (-(2 * s))) ^ j) := by
  have hTpos : (0 : ℝ) < a / b := div_pos ha hb
  have htpos : (0 : ℝ) < a / b * 2 ^ j := by positivity
  have hstep : a / b * 2 ^ (j + 1) = 2 * (a / b * 2 ^ j) := by
    rw [pow_succ]
    ring
  have hexpnp : -(2 * s + (d : ℝ)) ≤ 0 := by
    have : (0 : ℝ) ≤ 2 * s + (d : ℝ) := by positivity
    linarith only [this]
  have hbound : ∀ z ∈ farAnnulus d (a / b) j, radialIntegrand d s a b z ≤
      ENNReal.ofReal (a ^ 2 * (a / b * 2 ^ j) ^ (-(2 * s + (d : ℝ)))) := by
    rintro z ⟨hz1, _hz2⟩
    refine ENNReal.ofReal_le_ofReal (mul_le_mul ?_ ?_ ?_ ?_)
    · exact pow_le_pow_left₀ (le_min ha.le (by positivity)) (min_le_left _ _) 2
    · exact Real.rpow_le_rpow_of_nonpos htpos hz1.le hexpnp
    · exact Real.rpow_nonneg (norm_nonneg z) _
    · positivity
  calc ∫⁻ z : Vec d in farAnnulus d (a / b) j, radialIntegrand d s a b z
      ≤ ∫⁻ _z : Vec d in farAnnulus d (a / b) j,
          ENNReal.ofReal (a ^ 2 * (a / b * 2 ^ j) ^ (-(2 * s + (d : ℝ)))) :=
        setLIntegral_mono measurable_const hbound
    _ = ENNReal.ofReal (a ^ 2 * (a / b * 2 ^ j) ^ (-(2 * s + (d : ℝ)))) *
          MeasureTheory.volume (farAnnulus d (a / b) j) := setLIntegral_const _ _
    _ ≤ ENNReal.ofReal (a ^ 2 * (a / b * 2 ^ j) ^ (-(2 * s + (d : ℝ)))) *
          MeasureTheory.volume
            (Metric.closedBall (0 : Vec d) (2 * (a / b * 2 ^ j))) := by
        refine mul_le_mul_right (measure_mono ?_) _
        rintro z ⟨_, hz2⟩
        rw [hstep] at hz2
        simpa only [Metric.mem_closedBall, dist_zero_right] using hz2
    _ = ENNReal.ofReal (a ^ 2 * (a / b * 2 ^ j) ^ (-(2 * s + (d : ℝ)))) *
          ENNReal.ofReal ((2 * (2 * (a / b * 2 ^ j))) ^ d) := by
        rw [volume_closedBall_vec d (by positivity)]
    _ = ENNReal.ofReal (a ^ 2 * (a / b * 2 ^ j) ^ (-(2 * s + (d : ℝ))) *
            (2 * (2 * (a / b * 2 ^ j))) ^ d) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
    _ = ENNReal.ofReal (a ^ (2 - 2 * s) * b ^ (2 * s) *
          (2 : ℝ) ^ (2 * (d : ℝ)) * ((2 : ℝ) ^ (-(2 * s))) ^ j) := by
        rw [far_annulus_value d htpos, far_radius_rpow hTpos s j]
        congr 1
        rw [← coeff_far ha hb]
        ring

private theorem radial_cover (d : ℕ) {T : ℝ} (hT : 0 < T) :
    (Set.univ : Set (Vec d)) ⊆
      {z : Vec d | ‖z‖ = 0} ∪
        ((⋃ j : ℕ, nearAnnulus d T j) ∪ (⋃ j : ℕ, farAnnulus d T j)) := by
  classical
  intro z _
  rcases eq_or_lt_of_le (norm_nonneg z) with h0 | hpos
  · exact Or.inl h0.symm
  by_cases hle : ‖z‖ ≤ T
  · refine Or.inr (Or.inl ?_)
    have hex : ∃ j : ℕ, T / 2 ^ (j + 1) < ‖z‖ := by
      obtain ⟨n, hn⟩ :=
        exists_pow_lt_of_lt_one (div_pos hpos hT) (by norm_num : (1 : ℝ) / 2 < 1)
      refine ⟨n, ?_⟩
      have hnn : T / 2 ^ n < ‖z‖ := by
        have hrw : ((1 : ℝ) / 2) ^ n = 1 / 2 ^ n := by
          rw [div_pow, one_pow]
        rw [hrw, div_lt_div_iff₀ (by positivity) hT] at hn
        rw [div_lt_iff₀ (by positivity)]
        linarith only [hn]
      refine lt_of_le_of_lt ?_ hnn
      apply div_le_div_of_nonneg_left hT.le (by positivity)
      exact pow_le_pow_right₀ (by norm_num) (Nat.le_succ n)
    refine Set.mem_iUnion.2 ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
    rcases Nat.eq_zero_or_pos (Nat.find hex) with hz | hz
    · rw [hz]
      simpa using hle
    · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hz.ne'
      have hmin := Nat.find_min hex (m := k) (by omega)
      rw [hk]
      exact not_lt.1 hmin
  · refine Or.inr (Or.inr ?_)
    have hex : ∃ j : ℕ, ‖z‖ ≤ T * 2 ^ (j + 1) := by
      obtain ⟨n, hn⟩ :=
        exists_pow_lt_of_lt_one (div_pos hT hpos) (by norm_num : (1 : ℝ) / 2 < 1)
      refine ⟨n, ?_⟩
      have hnn : ‖z‖ < T * 2 ^ n := by
        have hrw : ((1 : ℝ) / 2) ^ n = 1 / 2 ^ n := by
          rw [div_pow, one_pow]
        rw [hrw, div_lt_div_iff₀ (by positivity) hpos] at hn
        nlinarith only [hn]
      refine hnn.le.trans ?_
      have h2 : (2 : ℝ) ^ n ≤ 2 ^ (n + 1) :=
        pow_le_pow_right₀ (by norm_num) (Nat.le_succ n)
      exact mul_le_mul_of_nonneg_left h2 hT.le
    refine Set.mem_iUnion.2 ⟨Nat.find hex, ?_, Nat.find_spec hex⟩
    rcases Nat.eq_zero_or_pos (Nat.find hex) with hz | hz
    · rw [hz]
      simpa using not_le.1 hle
    · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hz.ne'
      have hmin := Nat.find_min hex (m := k) (by omega)
      rw [hk]
      exact not_le.1 hmin

private theorem tsum_ofReal_geometric {C r : ℝ} (hC : 0 ≤ C) (hr0 : 0 ≤ r)
    (hr1 : r < 1) :
    ∑' j : ℕ, ENNReal.ofReal (C * r ^ j) = ENNReal.ofReal (C * (1 - r)⁻¹) := by
  have hsummable : Summable fun j : ℕ => C * r ^ j :=
    (summable_geometric_of_lt_one hr0 hr1).mul_left C
  have hvalue : ∑' j : ℕ, C * r ^ j = C * (1 - r)⁻¹ := by
    rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1]
  rw [← hvalue, ENNReal.ofReal_tsum_of_nonneg (fun j => by positivity) hsummable]

theorem lintegral_radialIntegrand_le (d : ℕ) {s a b : ℝ} (hs : 0 < s)
    (hs1 : s < 1) (ha : 0 < a) (hb : 0 < b) :
    ∫⁻ z : Vec d, radialIntegrand d s a b z
      ≤ ENNReal.ofReal
          (gagliardoOscillationConst d s * (a ^ (2 - 2 * s) * b ^ (2 * s))) := by
  have hrnear : (2 : ℝ) ^ (2 * s - 2) < 1 :=
    two_rpow_lt_one (by linarith only [hs1])
  have hrfar : (2 : ℝ) ^ (-(2 * s)) < 1 := two_rpow_lt_one (by linarith only [hs])
  have hnear1 : (0 : ℝ) < 1 - (2 : ℝ) ^ (2 * s - 2) := by linarith only [hrnear]
  have hfar1 : (0 : ℝ) < 1 - (2 : ℝ) ^ (-(2 * s)) := by linarith only [hrfar]
  have hCnear : (0 : ℝ) ≤
      a ^ (2 - 2 * s) * b ^ (2 * s) * (2 : ℝ) ^ (2 * s + 2 * (d : ℝ)) :=
    mul_nonneg (mul_nonneg (Real.rpow_nonneg ha.le _) (Real.rpow_nonneg hb.le _))
      (Real.rpow_nonneg (by norm_num) _)
  have hCfar : (0 : ℝ) ≤
      a ^ (2 - 2 * s) * b ^ (2 * s) * (2 : ℝ) ^ (2 * (d : ℝ)) :=
    mul_nonneg (mul_nonneg (Real.rpow_nonneg ha.le _) (Real.rpow_nonneg hb.le _))
      (Real.rpow_nonneg (by norm_num) _)
  have hzero :
      ∫⁻ z : Vec d in {z : Vec d | ‖z‖ = 0}, radialIntegrand d s a b z = 0 := by
    refine le_antisymm ?_ zero_le
    calc ∫⁻ z : Vec d in {z : Vec d | ‖z‖ = 0}, radialIntegrand d s a b z
        ≤ ∫⁻ _z : Vec d in {z : Vec d | ‖z‖ = 0}, (0 : ℝ≥0∞) := by
          refine setLIntegral_mono measurable_const ?_
          intro z hz
          have hz0 : ‖z‖ = 0 := hz
          have hval : min a (b * ‖z‖) ^ 2 * ‖z‖ ^ (-(2 * s + (d : ℝ))) = 0 := by
            rw [hz0, mul_zero, min_eq_right ha.le]
            norm_num
          show ENNReal.ofReal
            (min a (b * ‖z‖) ^ 2 * ‖z‖ ^ (-(2 * s + (d : ℝ)))) ≤ 0
          rw [hval, ENNReal.ofReal_zero]
      _ = 0 := lintegral_zero
  have hnear :
      ∫⁻ z : Vec d in (⋃ j : ℕ, nearAnnulus d (a / b) j), radialIntegrand d s a b z
        ≤ ENNReal.ofReal (a ^ (2 - 2 * s) * b ^ (2 * s) *
            (2 : ℝ) ^ (2 * s + 2 * (d : ℝ)) * (1 - (2 : ℝ) ^ (2 * s - 2))⁻¹) := by
    refine le_trans (lintegral_iUnion_le _ _) ?_
    refine le_trans
      (ENNReal.tsum_le_tsum fun j => lintegral_nearAnnulus_le d hs ha hb j) ?_
    exact le_of_eq
      (tsum_ofReal_geometric hCnear (Real.rpow_nonneg (by norm_num) _) hrnear)
  have hfar :
      ∫⁻ z : Vec d in (⋃ j : ℕ, farAnnulus d (a / b) j), radialIntegrand d s a b z
        ≤ ENNReal.ofReal (a ^ (2 - 2 * s) * b ^ (2 * s) *
            (2 : ℝ) ^ (2 * (d : ℝ)) * (1 - (2 : ℝ) ^ (-(2 * s)))⁻¹) := by
    refine le_trans (lintegral_iUnion_le _ _) ?_
    refine le_trans
      (ENNReal.tsum_le_tsum fun j => lintegral_farAnnulus_le d hs ha hb j) ?_
    exact le_of_eq
      (tsum_ofReal_geometric hCfar (Real.rpow_nonneg (by norm_num) _) hrfar)
  have hcomb : a ^ (2 - 2 * s) * b ^ (2 * s) * (2 : ℝ) ^ (2 * s + 2 * (d : ℝ)) *
        (1 - (2 : ℝ) ^ (2 * s - 2))⁻¹ +
      a ^ (2 - 2 * s) * b ^ (2 * s) * (2 : ℝ) ^ (2 * (d : ℝ)) *
        (1 - (2 : ℝ) ^ (-(2 * s)))⁻¹
      = gagliardoOscillationConst d s * (a ^ (2 - 2 * s) * b ^ (2 * s)) := by
    rw [gagliardoOscillationConst, Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    ring
  rw [← setLIntegral_univ]
  refine le_trans (lintegral_mono_set (radial_cover d (div_pos ha hb))) ?_
  refine le_trans (lintegral_union_le _ _ _) ?_
  rw [hzero, zero_add]
  refine le_trans (lintegral_union_le _ _ _) ?_
  refine le_trans (add_le_add hnear hfar) ?_
  rw [← ENNReal.ofReal_add (mul_nonneg hCnear (inv_nonneg.2 hnear1.le))
    (mul_nonneg hCfar (inv_nonneg.2 hfar1.le)), hcomb]

private theorem radialIntegrand_sub_comm (d : ℕ) (s a b : ℝ) (x y : Vec d) :
    radialIntegrand d s a b (x - y) = radialIntegrand d s a b (y - x) := by
  show ENNReal.ofReal
      (min a (b * ‖x - y‖) ^ 2 * ‖x - y‖ ^ (-(2 * s + (d : ℝ))))
    = ENNReal.ofReal
      (min a (b * ‖y - x‖) ^ 2 * ‖y - x‖ ^ (-(2 * s + (d : ℝ))))
  rw [norm_sub_rev]

theorem lintegral_shifted_le (d : ℕ) {s a b : ℝ} (hs : 0 < s) (hs1 : s < 1)
    (ha : 0 < a) (hb : 0 < b) (x : Vec d) (U : Set (Vec d)) :
    ∫⁻ y : Vec d in U, radialIntegrand d s a b (x - y)
      ≤ ENNReal.ofReal
          (gagliardoOscillationConst d s * (a ^ (2 - 2 * s) * b ^ (2 * s))) := by
  refine le_trans (lintegral_mono_set (Set.subset_univ U)) ?_
  rw [setLIntegral_univ,
    lintegral_congr fun y => radialIntegrand_sub_comm d s a b x y,
    lintegral_sub_right_eq_self (radialIntegrand d s a b) x]
  exact lintegral_radialIntegrand_le d hs hs1 ha hb

private theorem gagliardoOscillationConst_nonneg (d : ℕ) {s : ℝ} (hs : 0 < s)
    (hs1 : s < 1) : 0 ≤ gagliardoOscillationConst d s := by
  have hnear1 : (0 : ℝ) < 1 - (2 : ℝ) ^ (2 * s - 2) := by
    have := two_rpow_lt_one (c := 2 * s - 2) (by linarith only [hs1])
    linarith only [this]
  have hfar1 : (0 : ℝ) < 1 - (2 : ℝ) ^ (-(2 * s)) := by
    have := two_rpow_lt_one (c := -(2 * s)) (by linarith only [hs])
    linarith only [this]
  refine mul_nonneg (Real.rpow_nonneg (by norm_num) _) (add_nonneg ?_ ?_)
  · exact mul_nonneg (Real.rpow_nonneg (by norm_num) _) (inv_nonneg.2 hnear1.le)
  · exact inv_nonneg.2 hfar1.le

/-- The Gagliardo measure of a cube is carried by the product of the cube with
itself, so a bound valid on the cube holds almost everywhere for it. -/
private theorem ae_mem_cubeSet_prod_gagliardoCubeMeasure {d : ℕ}
    (Q : TriadicCube d) :
    ∀ᵐ z : Vec d × Vec d ∂(Gagliardo.gagliardoCubeMeasure Q),
      z.1 ∈ cubeSet Q ∧ z.2 ∈ cubeSet Q := by
  have : SFinite (cubeMeasure Q) := by rw [cubeMeasure]; infer_instance
  have hmeasS : MeasurableSet (cubeSet Q ×ˢ cubeSet Q) :=
    (measurableSet_cubeSet Q).prod (measurableSet_cubeSet Q)
  have hrestr : Gagliardo.gagliardoCubeMeasure Q
      = ENNReal.ofReal (cubeVolume Q)⁻¹ •
        ((MeasureTheory.volume.prod MeasureTheory.volume).restrict
          (cubeSet Q ×ˢ cubeSet Q)) := by
    rw [Gagliardo.gagliardoCubeMeasure, normalizedCubeMeasure, cubeMeasure,
      Measure.prod_smul_left, Measure.prod_restrict]
  rw [hrestr]
  refine Measure.ae_smul_measure ?_ _
  filter_upwards [ae_restrict_mem hmeasS] with z hz
  exact ⟨hz.1, hz.2⟩

/-- A field with vanishing oscillation on the cube has vanishing Gagliardo
seminorm there, the degenerate branch of the kernel estimate. -/
private theorem cubeEuclideanGagliardoESeminorm_eq_zero_of_osc_le_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {d : ℕ}
    {Q : TriadicCube d} {s : ℝ} {f : Vec d → E}
    (hosc : ∀ x ∈ cubeSet Q, ∀ y ∈ cubeSet Q, ‖f x - f y‖ ≤ 0) :
    cubeEuclideanGagliardoESeminorm Q s 2 f = 0 := by
  unfold cubeEuclideanGagliardoESeminorm
  have hae : euclideanGagliardoKernel s 2 f =ᵐ[Gagliardo.gagliardoCubeMeasure Q]
      fun _ : Vec d × Vec d => (0 : E) := by
    filter_upwards [ae_mem_cubeSet_prod_gagliardoCubeMeasure Q] with z hz
    have hval : ‖f z.1 - f z.2‖ = 0 :=
      le_antisymm (hosc z.1 hz.1 z.2 hz.2) (norm_nonneg _)
    have hk := norm_euclideanGagliardoKernel s 2 f z
    rw [hval, mul_zero] at hk
    exact norm_eq_zero.mp hk
  rw [eLpNorm_congr_ae hae]
  exact eLpNorm_zero

/-- A field Lipschitz on the cube is a.e. strongly measurable for the normalized cube
measure. -/
private theorem aestronglyMeasurable_normalizedCubeMeasure_of_lip
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {d : ℕ}
    {Q : TriadicCube d} {f : Vec d → E} {B : ℝ} (hB : 0 < B)
    (hlip : ∀ x ∈ cubeSet Q, ∀ y ∈ cubeSet Q,
      ‖f x - f y‖ ≤ B * euclideanDist x y) :
    AEStronglyMeasurable f (normalizedCubeMeasure Q) := by
  have hcont : ContinuousOn f (cubeSet Q) := by
    rw [Metric.continuousOn_iff]
    intro b hb ε hε
    have hK : 0 < B * (d : ℝ) + 1 := by positivity
    refine ⟨ε / (B * (d : ℝ) + 1), by positivity, fun a ha hab => ?_⟩
    rw [dist_eq_norm]
    have h1 := hlip a ha b hb
    have h2 := euclideanDist_le_dimension_mul_dist a b
    have h3 : dist a b * (B * (d : ℝ) + 1) < ε := by
      rwa [lt_div_iff₀ hK] at hab
    have h4 : B * euclideanDist a b ≤ B * ((d : ℝ) * dist a b) :=
      mul_le_mul_of_nonneg_left h2 hB.le
    have h5 : 0 ≤ dist a b := dist_nonneg
    linarith only [h1, h3, h4, h5]
  have hm : AEStronglyMeasurable f (cubeMeasure Q) :=
    hcont.aestronglyMeasurable (measurableSet_cubeSet Q)
  exact hm.smul_measure _

private theorem cubeEuclideanGagliardoESeminorm_le_of_pos
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {d : ℕ}
    {Q : TriadicCube d} {s : ℝ} (hs : 0 < s) (hs1 : s < 1) {f : Vec d → E}
    {A B : ℝ} (hA : 0 < A) (hB : 0 < B)
    (hosc : ∀ x ∈ cubeSet Q, ∀ y ∈ cubeSet Q, ‖f x - f y‖ ≤ 2 * A)
    (hlip : ∀ x ∈ cubeSet Q, ∀ y ∈ cubeSet Q,
      ‖f x - f y‖ ≤ B * euclideanDist x y) :
    cubeEuclideanGagliardoESeminorm Q s 2 f ≤
      ENNReal.ofReal (Real.sqrt (gagliardoOscillationConst d s) *
        (2 * A) ^ (1 - s) * (((d : ℝ) + 1) * B) ^ s) := by
  have : SFinite (cubeMeasure Q) := by rw [cubeMeasure]; infer_instance
  set a : ℝ := 2 * A with ha_def
  set b : ℝ := ((d : ℝ) + 1) * B with hb_def
  have hapos : 0 < a := by rw [ha_def]; linarith only [hA]
  have hbpos : 0 < b := by rw [hb_def]; positivity
  have h2toReal : ((2 : ℝ≥0∞)).toReal = 2 := by norm_num
  have hexp2 : -(s + (d : ℝ) / ((2 : ℝ≥0∞)).toReal) = -(s + (d : ℝ) / 2) := by
    rw [h2toReal]
  set m : Vec d × Vec d → ℝ := fun z =>
    min a (b * ‖z.1 - z.2‖) * ‖z.1 - z.2‖ ^ (-(s + (d : ℝ) / 2)) with hm_def
  have hmval : ∀ z : Vec d × Vec d, m z =
      min a (b * ‖z.1 - z.2‖) * ‖z.1 - z.2‖ ^ (-(s + (d : ℝ) / 2)) := fun _ => rfl
  have hm_nonneg : ∀ z : Vec d × Vec d, 0 ≤ m z := by
    intro z
    rw [hmval z]
    exact mul_nonneg (le_min hapos.le (by positivity))
      (Real.rpow_nonneg (norm_nonneg _) _)
  have hnp : -(s + (d : ℝ) / 2) ≤ 0 := by
    have : (0 : ℝ) ≤ s + (d : ℝ) / 2 := by positivity
    linarith only [this]
  have hae := ae_mem_cubeSet_prod_gagliardoCubeMeasure Q
  have hstep1 : cubeEuclideanGagliardoESeminorm Q s 2 f
      ≤ eLpNorm m 2 (Gagliardo.gagliardoCubeMeasure Q) := by
    refine eLpNorm_mono_enorm_ae
      (aestronglyMeasurable_euclideanGagliardoKernel
        (aestronglyMeasurable_normalizedCubeMeasure_of_lip hB hlip)) ?_
    filter_upwards [hae] with z hz
    rw [← ofReal_norm, ← ofReal_norm,
      norm_euclideanGagliardoKernel, hexp2,
      Real.norm_eq_abs, abs_of_nonneg (hm_nonneg z)]
    rcases eq_or_lt_of_le (norm_nonneg (z.1 - z.2)) with hr0 | hrpos
    · have hed : euclideanDist z.1 z.2 = 0 := by
        have h1 := euclideanDist_le_dimension_mul_dist z.1 z.2
        rw [dist_eq_norm, ← hr0, mul_zero] at h1
        exact le_antisymm h1 (euclideanDist_nonneg _ _)
      have hne : -(s + (d : ℝ) / 2) ≠ 0 := by
        have hpos : (0 : ℝ) < s + (d : ℝ) / 2 := by positivity
        exact ne_of_lt (by linarith only [hpos])
      rw [hed, Real.zero_rpow hne, zero_mul]
      exact ENNReal.ofReal_le_ofReal (hm_nonneg z)
    · refine ENNReal.ofReal_le_ofReal ?_
      have hge : ‖z.1 - z.2‖ ≤ euclideanDist z.1 z.2 := by
        simpa only [dist_eq_norm] using dist_le_euclideanDist z.1 z.2
      have hpow : euclideanDist z.1 z.2 ^ (-(s + (d : ℝ) / 2))
          ≤ ‖z.1 - z.2‖ ^ (-(s + (d : ℝ) / 2)) :=
        Real.rpow_le_rpow_of_nonpos hrpos hge hnp
      have hval : ‖f z.1 - f z.2‖ ≤ min a (b * ‖z.1 - z.2‖) := by
        refine le_min (hosc z.1 hz.1 z.2 hz.2) ?_
        refine (hlip z.1 hz.1 z.2 hz.2).trans ?_
        have h1 := euclideanDist_le_dimension_mul_dist z.1 z.2
        rw [dist_eq_norm] at h1
        have h2 : B * euclideanDist z.1 z.2 ≤ B * ((d : ℝ) * ‖z.1 - z.2‖) :=
          mul_le_mul_of_nonneg_left h1 hB.le
        refine h2.trans ?_
        rw [hb_def]
        nlinarith only [hB.le, norm_nonneg (z.1 - z.2)]
      rw [hmval z, mul_comm (min a (b * ‖z.1 - z.2‖))]
      exact mul_le_mul hpow hval (norm_nonneg _)
        (Real.rpow_nonneg (norm_nonneg _) _)
  have hK : ∀ z : Vec d × Vec d,
      ‖m z‖ₑ ^ (2 : ℝ) = radialIntegrand d s a b (z.1 - z.2) := by
    intro z
    rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg (hm_nonneg z),
      ENNReal.ofReal_rpow_of_nonneg (hm_nonneg z) (by norm_num)]
    show ENNReal.ofReal (m z ^ (2 : ℝ)) =
      ENNReal.ofReal (min a (b * ‖z.1 - z.2‖) ^ 2 *
        ‖z.1 - z.2‖ ^ (-(2 * s + (d : ℝ))))
    congr 1
    rw [hmval z, Real.mul_rpow (le_min hapos.le (by positivity))
        (Real.rpow_nonneg (norm_nonneg _) _),
      rpow_two_eq_sq, ← Real.rpow_mul (norm_nonneg _)]
    congr 2
    ring
  have hmeas : Measurable
      (fun z : Vec d × Vec d => radialIntegrand d s a b (z.1 - z.2)) := by
    show Measurable (fun z : Vec d × Vec d =>
      ENNReal.ofReal (min a (b * ‖z.1 - z.2‖) ^ 2 *
        ‖z.1 - z.2‖ ^ (-(2 * s + (d : ℝ)))))
    fun_prop
  have hconstNonneg : (0 : ℝ) ≤
      gagliardoOscillationConst d s * (a ^ (2 - 2 * s) * b ^ (2 * s)) :=
    mul_nonneg (gagliardoOscillationConst_nonneg d hs hs1)
      (mul_nonneg (Real.rpow_nonneg hapos.le _) (Real.rpow_nonneg hbpos.le _))
  have hmmeas : Measurable m := by rw [hm_def]; fun_prop
  have hstep2 : eLpNorm m 2 (Gagliardo.gagliardoCubeMeasure Q)
      ≤ ENNReal.ofReal (Real.sqrt
          (gagliardoOscillationConst d s * (a ^ (2 - 2 * s) * b ^ (2 * s)))) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hmmeas.aestronglyMeasurable, h2toReal]
    have hrewrite : ∫⁻ z : Vec d × Vec d, ‖m z‖ₑ ^ (2 : ℝ)
          ∂(Gagliardo.gagliardoCubeMeasure Q)
        = ∫⁻ z : Vec d × Vec d, radialIntegrand d s a b (z.1 - z.2)
          ∂(Gagliardo.gagliardoCubeMeasure Q) := by
      exact lintegral_congr fun z => hK z
    rw [hrewrite, Gagliardo.gagliardoCubeMeasure, lintegral_prod _ hmeas.aemeasurable]
    have hinner : ∀ x : Vec d,
        ∫⁻ y : Vec d, radialIntegrand d s a b (x - y) ∂(cubeMeasure Q)
          ≤ ENNReal.ofReal
              (gagliardoOscillationConst d s * (a ^ (2 - 2 * s) * b ^ (2 * s))) := by
      intro x
      rw [cubeMeasure]
      exact lintegral_shifted_le d hs hs1 hapos hbpos x _
    calc (∫⁻ x : Vec d, ∫⁻ y : Vec d, radialIntegrand d s a b (x - y)
            ∂(cubeMeasure Q) ∂(normalizedCubeMeasure Q)) ^ (1 / (2 : ℝ))
        ≤ (∫⁻ _x : Vec d, ENNReal.ofReal
              (gagliardoOscillationConst d s * (a ^ (2 - 2 * s) * b ^ (2 * s)))
              ∂(normalizedCubeMeasure Q)) ^ (1 / (2 : ℝ)) :=
          ENNReal.rpow_le_rpow (lintegral_mono hinner) (by norm_num)
      _ = ENNReal.ofReal
            (gagliardoOscillationConst d s * (a ^ (2 - 2 * s) * b ^ (2 * s)))
            ^ (1 / (2 : ℝ)) := by
          rw [lintegral_const, normalizedCubeMeasure_apply_univ, mul_one]
      _ = ENNReal.ofReal (Real.sqrt
            (gagliardoOscillationConst d s * (a ^ (2 - 2 * s) * b ^ (2 * s)))) := by
          rw [ENNReal.ofReal_rpow_of_nonneg hconstNonneg (by norm_num),
            Real.sqrt_eq_rpow]
  refine hstep1.trans (hstep2.trans (le_of_eq ?_))
  congr 1
  have hsplit : Real.sqrt
      (gagliardoOscillationConst d s * (a ^ (2 - 2 * s) * b ^ (2 * s)))
      = Real.sqrt (gagliardoOscillationConst d s) *
        (Real.sqrt (a ^ (2 - 2 * s)) * Real.sqrt (b ^ (2 * s))) := by
    rw [Real.sqrt_mul (gagliardoOscillationConst_nonneg d hs hs1),
      Real.sqrt_mul (Real.rpow_nonneg hapos.le _)]
  have hsa : Real.sqrt (a ^ (2 - 2 * s)) = a ^ (1 - s) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hapos.le]
    congr 1
    ring
  have hsb : Real.sqrt (b ^ (2 * s)) = b ^ s := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hbpos.le]
    congr 1
    ring
  rw [hsplit, hsa, hsb, ← mul_assoc]

/-- **The kernel estimate.** If the oscillation of `f` on the cube `Q` is at most `2A` and `f`
is Lipschitz on `Q` with constant `B` for the Euclidean magnitude, then

`[f]_{W̲^{s,2}(Q)} ≤ √(gagliardoOscillationConst d s) (2A)^{1−s} ((d+1)B)^s`.

The exponents are the printed ones: the two branches of `min{2A, B|x−y|}`
cross at `|x−y| = 2A/B`, the near region contributes
`B² (2A/B)^{2−2s}` and the far region `4A² (2A/B)^{−2s}`, both equal to
`A^{2−2s} B^{2s}` up to the dimensional constant. Applied to a shell `j_k`
with `A = O(1)` and `B = O(3^{−k})` it produces the printed amplitude
`3^{−sk}`, uniformly in the cube `Q`; the estimate is uniform in the scale of
`Q` because the far branch is integrable at infinity for `s > 0` and the near
branch at the origin for `s < 1`.

Both `A` and `B` may vanish: in that case the hypotheses force `f` to be
constant on the cube and both sides vanish. -/
theorem cubeEuclideanGagliardoESeminorm_le_of_oscillation_lipschitz
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {d : ℕ}
    {Q : TriadicCube d} {s : ℝ} (hs : 0 < s) (hs1 : s < 1) {f : Vec d → E}
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hosc : ∀ x ∈ cubeSet Q, ∀ y ∈ cubeSet Q, ‖f x - f y‖ ≤ 2 * A)
    (hlip : ∀ x ∈ cubeSet Q, ∀ y ∈ cubeSet Q,
      ‖f x - f y‖ ≤ B * euclideanDist x y) :
    cubeEuclideanGagliardoESeminorm Q s 2 f ≤
      ENNReal.ofReal (Real.sqrt (gagliardoOscillationConst d s) *
        (2 * A) ^ (1 - s) * (((d : ℝ) + 1) * B) ^ s) := by
  rcases eq_or_lt_of_le hA with hA0 | hApos
  · rw [cubeEuclideanGagliardoESeminorm_eq_zero_of_osc_le_zero
      (fun x hx y hy => by
        have := hosc x hx y hy
        rw [← hA0, mul_zero] at this
        exact this)]
    exact zero_le
  rcases eq_or_lt_of_le hB with hB0 | hBpos
  · rw [cubeEuclideanGagliardoESeminorm_eq_zero_of_osc_le_zero
      (fun x hx y hy => by
        have := hlip x hx y hy
        rw [← hB0, zero_mul] at this
        exact this)]
    exact zero_le
  exact cubeEuclideanGagliardoESeminorm_le_of_pos hs hs1 hApos hBpos hosc hlip

/-- The form the shell application uses: a uniform bound `A` on the size of
`f` on the cube gives the oscillation bound `2A` by the triangle inequality, so
the kernel estimate reads directly off a sup bound and a Lipschitz bound. -/
theorem cubeEuclideanGagliardoESeminorm_le_of_sup_lipschitz
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {d : ℕ}
    {Q : TriadicCube d} {s : ℝ} (hs : 0 < s) (hs1 : s < 1) {f : Vec d → E}
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hsup : ∀ x ∈ cubeSet Q, ‖f x‖ ≤ A)
    (hlip : ∀ x ∈ cubeSet Q, ∀ y ∈ cubeSet Q,
      ‖f x - f y‖ ≤ B * euclideanDist x y) :
    cubeEuclideanGagliardoESeminorm Q s 2 f ≤
      ENNReal.ofReal (Real.sqrt (gagliardoOscillationConst d s) *
        (2 * A) ^ (1 - s) * (((d : ℝ) + 1) * B) ^ s) :=
  cubeEuclideanGagliardoESeminorm_le_of_oscillation_lipschitz hs hs1 hA hB
    (fun x hx y hy =>
      (norm_sub_le (f x) (f y)).trans
        (by linarith only [hsup x hx, hsup y hy])) hlip

end

end SuperdiffusionCLT.Section2.Estimates.Stream

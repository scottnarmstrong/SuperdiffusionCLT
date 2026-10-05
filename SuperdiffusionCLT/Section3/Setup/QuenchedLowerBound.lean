/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Annealed.InfiniteVolume

/-!
# The quenched lower bound, annealed half

The paper closes the proof of
Proposition `p.sstar.lower.bound` with the quenched estimate
`e.sstar.lower.bound.quenched`.  Its first two steps are annealed and
deterministic, and they are what this file proves.

The print sets `n₀ := ⌊m/2⌋` and `R := 2n₀`, so that `n₀` sits in the top half
of `[0, R]` exactly as the prescribed scale of the annealed bound does; that
bound, applied *with cutoff `R` and spatial scale `n₀`*, gives

`σ̄_{R,*}^{-1}(cu_{n₀}) ≤ C ν^{-2} c⋆^{-3/2} n₀^{-1/2} log^{9/2}(ν^{-1} n₀)`.

Because `R - n₀ = n₀`, the balanced localization comparison
`e.localization.s.star` at the cutoff pair `(R, L)` on `cu_{n₀}`, read after
taking expectations in the associated Loewner inequalities and converting the
additive inverse-block comparison to the scalar ratio as in
`e.localization.s.star.annealed.applied`, gives
`|σ̄_{R,*}(cu_{n₀}) σ̄_{L,*}^{-1}(cu_{n₀}) - 1| ≤ C ν^{-5} L 3^{-n₀}`, and once
that error is below `1` the deterministic bound transfers from cutoff `R` to
cutoff `L` at the cost of a factor `2`.

## What is proved here

* `quenchedInnerScale`, `quenchedCutoffScale` — the print's `n₀ = ⌊m/2⌋` and
  `R = 2n₀`, with the arithmetic of the two scales.
* `sigmaBarStarInvScalar_le_of_annealed_lower_bound` — the inversion of the
  annealed lower bound `e.sstar.lower.bound` into an upper bound on
  `σ̄_{R,*}^{-1}(cu_{n₀})`.  The hypothesis is the second conjunct of
  the root theorem `Frozen.Section3.sigmaBarStar_lower_bound` read at `L := R`
  and `m̄ := n₀`.
* `localization_error_le_one` — the print's "after increasing the lower
  threshold in `e.L.vs.nu`, this factor is absorbed into the constant", in the
  explicit form `C ν^{-5} L 3^{-k} ≤ 1` under `6 log(ν^{-1}L) ≤ k log 3`.
* `sigmaBarStarInvScalar_transfer_cutoff` — the transfer `R → L` from the
  annealed localization comparison.
* `sigmaBarStarInvScalar_le_quenchedConst` — the composition, in the scale `m`
  and with the constant `quenchedConst c = 2√3/c`.

## What is not proved here

The annealed comparison
`|σ̄_{R,*}(cu_{n₀}) σ̄_{L,*}^{-1}(cu_{n₀}) - 1| ≤ C ν^{-5} L 3^{-n₀}` is carried
as an explicit hypothesis: its source is
`Frozen.Section2.cutoff_localization` (the third and
fourth Loewner conjuncts of `e.localization.s.star`) together with the passage
to expectations, neither of which is proved here.  The annealed
lower bound at cutoff `R` is likewise an explicit hypothesis, supplied by
the root theorem `Frozen.Section3.sigmaBarStar_lower_bound`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Setup

open Homogenization MeasureTheory
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Cutoff

/-! ## The two scales of the proof -/

/-- **`n₀ := ⌊m/2⌋`**. -/
def quenchedInnerScale (m : ℕ) : ℕ := m / 2

/-- **`R := 2n₀`**. -/
def quenchedCutoffScale (m : ℕ) : ℕ := 2 * quenchedInnerScale m

theorem quenchedInnerScale_le (m : ℕ) : quenchedInnerScale m ≤ m := by
  simp only [quenchedInnerScale]; omega

theorem quenchedInnerScale_le_quenchedCutoffScale (m : ℕ) :
    quenchedInnerScale m ≤ quenchedCutoffScale m := by
  simp only [quenchedCutoffScale]; omega

theorem one_le_quenchedInnerScale {m : ℕ} (hm : 2 ≤ m) : 1 ≤ quenchedInnerScale m := by
  simp only [quenchedInnerScale]; omega

theorem quenchedInnerScale_lt {m : ℕ} (hm : 1 ≤ m) : quenchedInnerScale m < m := by
  simp only [quenchedInnerScale]; omega

/-- `m ≤ 3⌊m/2⌋` for `m ≥ 2`: the comparability of `n₀^{1/2}` and `m^{1/2}`. -/
theorem le_three_mul_quenchedInnerScale {m : ℕ} (hm : 2 ≤ m) :
    m ≤ 3 * quenchedInnerScale m := by
  simp only [quenchedInnerScale]; omega

/-- `m - n₀ ≥ m/2`, the print's "as `m - n₀ ≥ m/2`". -/
theorem le_two_mul_sub_quenchedInnerScale (m : ℕ) :
    m ≤ 2 * (m - quenchedInnerScale m) := by
  simp only [quenchedInnerScale]; omega

/-! ## The constant -/

/-- The constant of the quenched deterministic bound: the annealed constant `c`
is inverted, the transfer from cutoff `R` to cutoff `L` costs a factor `2`, and
the passage from `n₀^{-1/2}` to `m^{-1/2}` costs a factor `√3`. -/
noncomputable def quenchedConst (c : ℝ) : ℝ := 2 * Real.sqrt 3 / c

/-! ## Inverting the annealed lower bound -/

/-- The elementary inversion: from `A ≤ S⁻¹` and `1 ≤ A T` with `A, S > 0` we
get `S ≤ T`. -/
private theorem le_of_le_inv_of_one_le_mul {A S T : ℝ} (hA : 0 < A) (hS : 0 < S)
    (hAS : A ≤ S⁻¹) (hAT : 1 ≤ A * T) : S ≤ T := by
  have h1 : A * S ≤ S⁻¹ * S := mul_le_mul_of_nonneg_right hAS hS.le
  rw [inv_mul_cancel₀ hS.ne'] at h1
  exact le_of_mul_le_mul_left (le_trans h1 hAT) hA

/-- **The deterministic bound at the cutoff `R`**: the annealed
lower bound `e.sstar.lower.bound` at cutoff `R` and spatial scale `n₀`,
inverted.  The hypothesis `hAnn` is the annealed lower bound of
`Frozen.Section3.sigmaBarStar_lower_bound` read at `L := R`, `m̄ := n₀`. -/
theorem sigmaBarStarInvScalar_le_of_annealed_lower_bound {d : ℕ} [NeZero d]
    {nu cStar c : ℝ} {P : ProbabilityMeasure (ShellSeq d)} {R n0 : ℕ}
    (hnu : 0 < nu) (hcStar : 0 < cStar) (hc : 0 < c)
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P)
    (hJ4 : ShellLawJ4 d P) (hn0 : 1 ≤ n0)
    (hlog : 0 < Real.log (nu⁻¹ * (n0 : ℝ)))
    (hAnn : c * cStar ^ ((3 : ℝ) / 2) * nu ^ (2 : ℝ) * (n0 : ℝ) ^ ((1 : ℝ) / 2) *
        Real.log (nu⁻¹ * (n0 : ℝ)) ^ (-((9 : ℝ) / 2)) ≤
      sigmaBarStarScalar nu R P (cubeSet (originCube d (n0 : ℤ)))) :
    sigmaBarStarInvScalar nu R P (cubeSet (originCube d (n0 : ℤ))) ≤
      c⁻¹ * nu ^ (-(2 : ℝ)) * cStar ^ (-((3 : ℝ) / 2)) * (n0 : ℝ) ^ (-((1 : ℝ) / 2)) *
        Real.log (nu⁻¹ * (n0 : ℝ)) ^ ((9 : ℝ) / 2) := by
  have hn0R : (0 : ℝ) < (n0 : ℝ) := by exact_mod_cast hn0
  have hS : 0 < sigmaBarStarInvScalar nu R P (cubeSet (originCube d (n0 : ℤ))) :=
    sigmaBarStarInvScalar_pos_cutoff hnu R hPrefix hJ2 hJ3 hJ4 (n0 : ℤ)
  rw [sigmaBarStarScalar_eq_inv hnu R hJ4 (n0 : ℤ) hS] at hAnn
  refine le_of_le_inv_of_one_le_mul ?_ hS hAnn ?_
  · exact mul_pos (mul_pos (mul_pos (mul_pos hc (Real.rpow_pos_of_pos hcStar _))
      (Real.rpow_pos_of_pos hnu _)) (Real.rpow_pos_of_pos hn0R _))
      (Real.rpow_pos_of_pos hlog _)
  · have e0 : c * c⁻¹ = 1 := mul_inv_cancel₀ hc.ne'
    have e1 : cStar ^ ((3 : ℝ) / 2) * cStar ^ (-((3 : ℝ) / 2)) = 1 := by
      rw [← Real.rpow_add hcStar]; norm_num
    have e2 : nu ^ (2 : ℝ) * nu ^ (-(2 : ℝ)) = 1 := by
      rw [← Real.rpow_add hnu]; norm_num
    have e3 : (n0 : ℝ) ^ ((1 : ℝ) / 2) * (n0 : ℝ) ^ (-((1 : ℝ) / 2)) = 1 := by
      rw [← Real.rpow_add hn0R]; norm_num
    have e4 : Real.log (nu⁻¹ * (n0 : ℝ)) ^ (-((9 : ℝ) / 2)) *
        Real.log (nu⁻¹ * (n0 : ℝ)) ^ ((9 : ℝ) / 2) = 1 := by
      rw [← Real.rpow_add hlog]; norm_num
    have key : (c * cStar ^ ((3 : ℝ) / 2) * nu ^ (2 : ℝ) * (n0 : ℝ) ^ ((1 : ℝ) / 2) *
          Real.log (nu⁻¹ * (n0 : ℝ)) ^ (-((9 : ℝ) / 2))) *
        (c⁻¹ * nu ^ (-(2 : ℝ)) * cStar ^ (-((3 : ℝ) / 2)) * (n0 : ℝ) ^ (-((1 : ℝ) / 2)) *
          Real.log (nu⁻¹ * (n0 : ℝ)) ^ ((9 : ℝ) / 2)) =
        (c * c⁻¹) * (cStar ^ ((3 : ℝ) / 2) * cStar ^ (-((3 : ℝ) / 2))) *
          (nu ^ (2 : ℝ) * nu ^ (-(2 : ℝ))) *
          ((n0 : ℝ) ^ ((1 : ℝ) / 2) * (n0 : ℝ) ^ (-((1 : ℝ) / 2))) *
          (Real.log (nu⁻¹ * (n0 : ℝ)) ^ (-((9 : ℝ) / 2)) *
            Real.log (nu⁻¹ * (n0 : ℝ)) ^ ((9 : ℝ) / 2)) := by ring
    rw [key, e0, e1, e2, e3, e4]
    norm_num

/-! ## The localization error at the cutoff pair `(R, L)` -/

/-- **The print's "after increasing the lower threshold in `e.L.vs.nu`, this
factor is absorbed into the constant"**, made explicit: the
localization error `η = C ν^{-5} L 3^{-k}` is at most `1` as soon
as `6 log(ν^{-1}L) ≤ k log 3`.  Here `k = n₀`, and `C ≤ ν^{-1}L` is the
threshold shape used throughout the scale assembly. -/
theorem localization_error_le_one {Ceta nu : ℝ} {L k : ℕ}
    (hnu : 0 < nu) (hnu1 : nu ≤ 1) (hL : 1 ≤ L) (hCeta : 0 ≤ Ceta)
    (hCT : Ceta ≤ nu⁻¹ * (L : ℝ))
    (hk : 6 * Real.log (nu⁻¹ * (L : ℝ)) ≤ (k : ℝ) * Real.log 3) :
    Ceta * nu ^ (-(5 : ℝ)) * (L : ℝ) * (3 : ℝ) ^ (-(k : ℝ)) ≤ 1 := by
  have hL1 : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
  have hinv1 : (1 : ℝ) ≤ nu⁻¹ := (one_le_inv₀ hnu).2 hnu1
  have hinv0 : (0 : ℝ) < nu⁻¹ := lt_of_lt_of_le zero_lt_one hinv1
  have ht1 : (1 : ℝ) ≤ nu⁻¹ * (L : ℝ) := by
    have := mul_le_mul hinv1 hL1 zero_le_one hinv0.le
    linarith only [this]
  have ht0 : (0 : ℝ) < nu⁻¹ * (L : ℝ) := lt_of_lt_of_le zero_lt_one ht1
  -- `Ceta ν^{-5} L ≤ (ν^{-1}L)^6`
  have hnu5 : nu ^ (-(5 : ℝ)) = nu⁻¹ ^ (5 : ℝ) := by
    rw [Real.inv_rpow hnu.le, Real.rpow_neg hnu.le]
  have hinvpow : (0 : ℝ) ≤ nu⁻¹ ^ (5 : ℝ) := Real.rpow_nonneg hinv0.le _
  have hLpow : (L : ℝ) ≤ (L : ℝ) ^ (5 : ℝ) := by
    have h := Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num : (1 : ℝ) ≤ 5)
    rwa [Real.rpow_one] at h
  have hsplit : nu⁻¹ ^ (5 : ℝ) * (L : ℝ) ^ (5 : ℝ) = (nu⁻¹ * (L : ℝ)) ^ (5 : ℝ) :=
    (Real.mul_rpow hinv0.le (by linarith only [hL1])).symm
  have hsix : (nu⁻¹ * (L : ℝ)) ^ (1 : ℝ) * (nu⁻¹ * (L : ℝ)) ^ (5 : ℝ) =
      (nu⁻¹ * (L : ℝ)) ^ (6 : ℝ) := by
    rw [← Real.rpow_add ht0]; norm_num
  have hstep1 : Ceta * nu ^ (-(5 : ℝ)) * (L : ℝ) ≤ (nu⁻¹ * (L : ℝ)) ^ (6 : ℝ) := by
    have h1 : nu⁻¹ ^ (5 : ℝ) * (L : ℝ) ≤ (nu⁻¹ * (L : ℝ)) ^ (5 : ℝ) := by
      rw [← hsplit]
      exact mul_le_mul_of_nonneg_left hLpow hinvpow
    have h2 : Ceta * (nu⁻¹ ^ (5 : ℝ) * (L : ℝ)) ≤ Ceta * (nu⁻¹ * (L : ℝ)) ^ (5 : ℝ) :=
      mul_le_mul_of_nonneg_left h1 hCeta
    have h3 : Ceta * (nu⁻¹ * (L : ℝ)) ^ (5 : ℝ) ≤
        (nu⁻¹ * (L : ℝ)) * (nu⁻¹ * (L : ℝ)) ^ (5 : ℝ) :=
      mul_le_mul_of_nonneg_right hCT (Real.rpow_nonneg ht0.le _)
    have h4 : (nu⁻¹ * (L : ℝ)) * (nu⁻¹ * (L : ℝ)) ^ (5 : ℝ) =
        (nu⁻¹ * (L : ℝ)) ^ (6 : ℝ) := by
      rw [← hsix, Real.rpow_one]
    have h5 : Ceta * nu ^ (-(5 : ℝ)) * (L : ℝ) = Ceta * (nu⁻¹ ^ (5 : ℝ) * (L : ℝ)) := by
      rw [hnu5]; ring
    rw [h5]
    exact le_trans h2 (le_trans h3 (le_of_eq h4))
  -- `(ν^{-1}L)^6 ≤ 3^k`
  have hpow : (nu⁻¹ * (L : ℝ)) ^ (6 : ℝ) ≤ (3 : ℝ) ^ ((k : ℝ)) := by
    rw [Real.rpow_def_of_pos ht0, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3)]
    exact Real.exp_le_exp.2 (by linarith only [hk])
  have h3pos : (0 : ℝ) < (3 : ℝ) ^ ((k : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
  have hneg : (3 : ℝ) ^ (-(k : ℝ)) = ((3 : ℝ) ^ ((k : ℝ)))⁻¹ :=
    Real.rpow_neg (by norm_num) _
  rw [hneg]
  have hfinal := mul_le_mul_of_nonneg_right (le_trans hstep1 hpow) (inv_pos.2 h3pos).le
  rwa [mul_inv_cancel₀ h3pos.ne'] at hfinal

/-! ## The transfer from cutoff `R` to cutoff `L` -/

/-- **The transfer of the deterministic bound from cutoff `R` to cutoff `L`**.
The hypothesis `hLocal` is
`e.localization.s.star.annealed.applied` at the cutoff pair
`(R, L)` on `cu_{n₀}`; `hEta` is the absorption of its error into the constant.
-/
theorem sigmaBarStarInvScalar_transfer_cutoff {d : ℕ} [NeZero d]
    {nu eta : ℝ} {P : ProbabilityMeasure (ShellSeq d)} {R L n0 : ℕ}
    (hnu : 0 < nu)
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P)
    (hJ4 : ShellLawJ4 d P) (hEta : eta ≤ 1)
    (hLocal : |sigmaBarStarScalar nu R P (cubeSet (originCube d (n0 : ℤ))) *
        sigmaBarStarInvScalar nu L P (cubeSet (originCube d (n0 : ℤ))) - 1| ≤ eta) :
    sigmaBarStarInvScalar nu L P (cubeSet (originCube d (n0 : ℤ))) ≤
      2 * sigmaBarStarInvScalar nu R P (cubeSet (originCube d (n0 : ℤ))) := by
  have hSR : 0 < sigmaBarStarInvScalar nu R P (cubeSet (originCube d (n0 : ℤ))) :=
    sigmaBarStarInvScalar_pos_cutoff hnu R hPrefix hJ2 hJ3 hJ4 (n0 : ℤ)
  have hbound := (abs_le.1 hLocal).2
  have hprod : sigmaBarStarScalar nu R P (cubeSet (originCube d (n0 : ℤ))) *
      sigmaBarStarInvScalar nu L P (cubeSet (originCube d (n0 : ℤ))) ≤ 2 := by
    linarith only [hbound, hEta]
  rw [sigmaBarStarScalar_eq_inv hnu R hJ4 (n0 : ℤ) hSR] at hprod
  have hmul := mul_le_mul_of_nonneg_left hprod hSR.le
  rw [← mul_assoc, mul_inv_cancel₀ hSR.ne', one_mul] at hmul
  linarith only [hmul]

/-! ## The composition -/

/-- The comparison of the two scale factors: `n₀ = ⌊m/2⌋`
satisfies `m ≤ 3n₀`, so `n₀^{-1/2} ≤ √3 m^{-1/2}`, and `n₀ ≤ m` makes the
logarithmic factor only larger. -/
private theorem rpow_neg_half_le {n0 m : ℕ} (hn0 : 1 ≤ n0) (hm : 1 ≤ m)
    (hm3 : m ≤ 3 * n0) :
    (n0 : ℝ) ^ (-((1 : ℝ) / 2)) ≤ Real.sqrt 3 * (m : ℝ) ^ (-((1 : ℝ) / 2)) := by
  have hn0R : (0 : ℝ) < (n0 : ℝ) := by exact_mod_cast hn0
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hm3R : (m : ℝ) ≤ 3 * (n0 : ℝ) := by exact_mod_cast hm3
  have hs3 : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have hn12 : (0 : ℝ) < (n0 : ℝ) ^ ((1 : ℝ) / 2) := Real.rpow_pos_of_pos hn0R _
  have hm12 : (0 : ℝ) < (m : ℝ) ^ ((1 : ℝ) / 2) := Real.rpow_pos_of_pos hmR _
  have hstep : (m : ℝ) ^ ((1 : ℝ) / 2) ≤ Real.sqrt 3 * (n0 : ℝ) ^ ((1 : ℝ) / 2) := by
    have h := Real.rpow_le_rpow hmR.le hm3R (by norm_num : (0 : ℝ) ≤ 1 / 2)
    rw [Real.mul_rpow (by norm_num) hn0R.le] at h
    rw [Real.sqrt_eq_rpow]
    exact h
  have hprodpos : (0 : ℝ) < Real.sqrt 3 * (n0 : ℝ) ^ ((1 : ℝ) / 2) := mul_pos hs3 hn12
  have hinv := (inv_le_inv₀ hprodpos hm12).2 hstep
  have hmul := mul_le_mul_of_nonneg_left hinv hs3.le
  have hL : Real.sqrt 3 * (Real.sqrt 3 * (n0 : ℝ) ^ ((1 : ℝ) / 2))⁻¹ =
      ((n0 : ℝ) ^ ((1 : ℝ) / 2))⁻¹ := by
    rw [mul_inv, ← mul_assoc, mul_inv_cancel₀ hs3.ne', one_mul]
  rw [hL] at hmul
  rw [Real.rpow_neg hn0R.le, Real.rpow_neg hmR.le]
  exact hmul

/-- **The annealed input of the quenched estimate**: the
deterministic upper bound on `σ̄_{L,*}^{-1}(cu_{n₀})` at the prescribed scale
`m`, obtained from the annealed lower bound at cutoff `R = 2⌊m/2⌋` and the
balanced localization transfer `R → L`.

`hAnn` is the annealed lower bound of `Frozen.Section3.sigmaBarStar_lower_bound` at
`L := R`, `m̄ := n₀`; `hLocal` is `e.localization.s.star.annealed.applied` at the cutoff
pair `(R, L)` on `cu_{n₀}`, whose source is
`Frozen.Section2.cutoff_localization`; `hEta` is the print's absorption of
the localization error, for which `localization_error_le_one` gives a
sufficient threshold. -/
theorem sigmaBarStarInvScalar_le_quenchedConst {d : ℕ} [NeZero d]
    {nu cStar c Ceta : ℝ} {P : ProbabilityMeasure (ShellSeq d)} {L m : ℕ}
    (hnu : 0 < nu) (hcStar : 0 < cStar) (hc : 0 < c)
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P)
    (hJ4 : ShellLawJ4 d P) (hm : 2 ≤ m)
    (hlog : 0 < Real.log (nu⁻¹ * ((quenchedInnerScale m : ℕ) : ℝ)))
    (hAnn : c * cStar ^ ((3 : ℝ) / 2) * nu ^ (2 : ℝ) *
          ((quenchedInnerScale m : ℕ) : ℝ) ^ ((1 : ℝ) / 2) *
          Real.log (nu⁻¹ * ((quenchedInnerScale m : ℕ) : ℝ)) ^ (-((9 : ℝ) / 2)) ≤
        sigmaBarStarScalar nu (quenchedCutoffScale m) P
          (cubeSet (originCube d ((quenchedInnerScale m : ℕ) : ℤ))))
    (hLocal : |sigmaBarStarScalar nu (quenchedCutoffScale m) P
            (cubeSet (originCube d ((quenchedInnerScale m : ℕ) : ℤ))) *
          sigmaBarStarInvScalar nu L P
            (cubeSet (originCube d ((quenchedInnerScale m : ℕ) : ℤ))) - 1| ≤
        Ceta * nu ^ (-(5 : ℝ)) * (L : ℝ) *
          (3 : ℝ) ^ (-((quenchedInnerScale m : ℕ) : ℝ)))
    (hEta : Ceta * nu ^ (-(5 : ℝ)) * (L : ℝ) *
        (3 : ℝ) ^ (-((quenchedInnerScale m : ℕ) : ℝ)) ≤ 1) :
    sigmaBarStarInvScalar nu L P
        (cubeSet (originCube d ((quenchedInnerScale m : ℕ) : ℤ))) ≤
      quenchedConst c * nu ^ (-(2 : ℝ)) * cStar ^ (-((3 : ℝ) / 2)) *
        (m : ℝ) ^ (-((1 : ℝ) / 2)) * Real.log (nu⁻¹ * (m : ℝ)) ^ ((9 : ℝ) / 2) := by
  have hn0 : 1 ≤ quenchedInnerScale m := one_le_quenchedInnerScale hm
  have hn0R : (0 : ℝ) < ((quenchedInnerScale m : ℕ) : ℝ) := by exact_mod_cast hn0
  have hmR : (0 : ℝ) < (m : ℝ) := by
    have h1 : 1 ≤ m := by omega
    exact_mod_cast h1
  have hstep1 := sigmaBarStarInvScalar_le_of_annealed_lower_bound
    (R := quenchedCutoffScale m) (n0 := quenchedInnerScale m) hnu hcStar hc
    hPrefix hJ2 hJ3 hJ4 hn0 hlog hAnn
  have hstep2 := sigmaBarStarInvScalar_transfer_cutoff
    (R := quenchedCutoffScale m) (L := L) (n0 := quenchedInnerScale m) hnu
    hPrefix hJ2 hJ3 hJ4 hEta hLocal
  have hK : (0 : ℝ) ≤ c⁻¹ * nu ^ (-(2 : ℝ)) * cStar ^ (-((3 : ℝ) / 2)) :=
    mul_nonneg (mul_nonneg (inv_nonneg.2 hc.le) (Real.rpow_nonneg hnu.le _))
      (Real.rpow_nonneg hcStar.le _)
  -- the two scale factors
  have hB := rpow_neg_half_le (n0 := quenchedInnerScale m) (m := m) hn0
    (by omega) (le_three_mul_quenchedInnerScale hm)
  have hlogle : Real.log (nu⁻¹ * ((quenchedInnerScale m : ℕ) : ℝ)) ≤
      Real.log (nu⁻¹ * (m : ℝ)) := by
    have hle : ((quenchedInnerScale m : ℕ) : ℝ) ≤ (m : ℝ) := by
      exact_mod_cast quenchedInnerScale_le m
    exact Real.log_le_log (mul_pos (inv_pos.2 hnu) hn0R)
      (mul_le_mul_of_nonneg_left hle (inv_pos.2 hnu).le)
  have hG : Real.log (nu⁻¹ * ((quenchedInnerScale m : ℕ) : ℝ)) ^ ((9 : ℝ) / 2) ≤
      Real.log (nu⁻¹ * (m : ℝ)) ^ ((9 : ℝ) / 2) :=
    Real.rpow_le_rpow hlog.le hlogle (by norm_num)
  have hfactors : ((quenchedInnerScale m : ℕ) : ℝ) ^ (-((1 : ℝ) / 2)) *
      Real.log (nu⁻¹ * ((quenchedInnerScale m : ℕ) : ℝ)) ^ ((9 : ℝ) / 2) ≤
      Real.sqrt 3 * (m : ℝ) ^ (-((1 : ℝ) / 2)) *
        Real.log (nu⁻¹ * (m : ℝ)) ^ ((9 : ℝ) / 2) :=
    mul_le_mul hB hG (Real.rpow_nonneg hlog.le _)
      (mul_nonneg (Real.sqrt_nonneg 3) (Real.rpow_nonneg hmR.le _))
  have hmid := mul_le_mul_of_nonneg_left hfactors hK
  have hdouble : (2 : ℝ) * (c⁻¹ * nu ^ (-(2 : ℝ)) * cStar ^ (-((3 : ℝ) / 2)) *
        (((quenchedInnerScale m : ℕ) : ℝ) ^ (-((1 : ℝ) / 2)) *
          Real.log (nu⁻¹ * ((quenchedInnerScale m : ℕ) : ℝ)) ^ ((9 : ℝ) / 2))) ≤
      2 * (c⁻¹ * nu ^ (-(2 : ℝ)) * cStar ^ (-((3 : ℝ) / 2)) *
        (Real.sqrt 3 * (m : ℝ) ^ (-((1 : ℝ) / 2)) *
          Real.log (nu⁻¹ * (m : ℝ)) ^ ((9 : ℝ) / 2))) := by
    linarith only [hmid]
  have hrw : (2 : ℝ) * (c⁻¹ * nu ^ (-(2 : ℝ)) * cStar ^ (-((3 : ℝ) / 2)) *
        (Real.sqrt 3 * (m : ℝ) ^ (-((1 : ℝ) / 2)) *
          Real.log (nu⁻¹ * (m : ℝ)) ^ ((9 : ℝ) / 2))) =
      quenchedConst c * nu ^ (-(2 : ℝ)) * cStar ^ (-((3 : ℝ) / 2)) *
        (m : ℝ) ^ (-((1 : ℝ) / 2)) * Real.log (nu⁻¹ * (m : ℝ)) ^ ((9 : ℝ) / 2) := by
    rw [quenchedConst, div_eq_mul_inv]; ring
  have hchain : sigmaBarStarInvScalar nu L P
      (cubeSet (originCube d ((quenchedInnerScale m : ℕ) : ℤ))) ≤
      2 * (c⁻¹ * nu ^ (-(2 : ℝ)) * cStar ^ (-((3 : ℝ) / 2)) *
        (((quenchedInnerScale m : ℕ) : ℝ) ^ (-((1 : ℝ) / 2)) *
          Real.log (nu⁻¹ * ((quenchedInnerScale m : ℕ) : ℝ)) ^ ((9 : ℝ) / 2))) := by
    have hexp : c⁻¹ * nu ^ (-(2 : ℝ)) * cStar ^ (-((3 : ℝ) / 2)) *
        (((quenchedInnerScale m : ℕ) : ℝ) ^ (-((1 : ℝ) / 2)) *
          Real.log (nu⁻¹ * ((quenchedInnerScale m : ℕ) : ℝ)) ^ ((9 : ℝ) / 2)) =
        c⁻¹ * nu ^ (-(2 : ℝ)) * cStar ^ (-((3 : ℝ) / 2)) *
          ((quenchedInnerScale m : ℕ) : ℝ) ^ (-((1 : ℝ) / 2)) *
          Real.log (nu⁻¹ * ((quenchedInnerScale m : ℕ) : ℝ)) ^ ((9 : ℝ) / 2) := by
      ring
    rw [hexp]
    linarith only [hstep1, hstep2]
  rw [← hrw]
  exact le_trans hchain hdouble

end SuperdiffusionCLT.Section3.Setup

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.RHSTerm1InputsG

/-!
# `l.RHS.term1` with the energy line discharged

The Step 2 display of `l.RHS.term1` carries the explicit lines `hLocalized`,
`hJensen`, `hEnergy`, `hQTilde` and `hConc`.
`RHSTerm1InputsG` proves `hEnergy`, the printed energy line
`e.un.tilde.un.energy`, for the cube scales `S.n ≤ r ≤ S.m`.  This file carries
that through the Step 2 display and delivers it without `hEnergy`.

## Main results

* `l2_second_moment_bridge'`: the Step 2 `hL2` display with `hEnergy` **removed**, the
  glued field of `e.u.k.def` substituted for the free field `uTildeGlued`, and the energy
  line supplied internally by `RHSTerm1InputsG.energy_bridge`.

## Why the cube scale is restricted

`hEnergy` and `hLocalized` are both quantified over every `r : ℕ` in
`RHSTerm1InputsE` and `RHSTerm1InputsF`.  Neither is provable in that
form, and neither is asserted by the print: below the scale `n` of the glued
family, `cu_r` sits strictly inside the single sub-cube `cu_n` of the family,
and the printed derivations — the cube-wise energy bound of `e.v.ky.energy`,
and the cube-wise localization estimate `e.localization.minimizers` — are both
averages over the scale-`n` sub-cubes, which need `n ≤ r`.  Above `m` the glued
field vanishes outside `cu_m` and neither line is used.  Both lines are used
only at `r = S.ell` and `r = S.m`, and `ScalesOrdering` puts both in
`[S.n, S.m]`.

## What stays explicit, and why

`hLocalized`, `hJensen`, `hQTilde`, `hConc`, `hH1Dominates` and the standing
side conditions, exactly as in `RHSTerm1InputsF`.

## References

The paper: `e.v.ky.energy`, `e.un.tilde.un.energy`, `e.localization.minimizers`
and the proof of `l.RHS.term1`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Terms

open MeasureTheory
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section3.ResponseFields
open SuperdiffusionCLT.Section3.Setup
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Estimates.Stream
open Homogenization
open Homogenization.IndependentSums
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## Two `ℝ≥0∞` helpers -/

/-- `(a + b)² ≤ 4(a² + b²)` in `ℝ≥0∞`, where the linearly ordered ring form is
unavailable.  A private copy of the same helper of `RHSTerm1InputsF.lean`. -/
private theorem addSqLeH (a b : ℝ≥0∞) :
    (a + b) ^ (2 : ℕ) ≤ 4 * (a ^ (2 : ℕ) + b ^ (2 : ℕ)) := by
  rcases le_total a b with h | h
  · have hab : a + b ≤ 2 * b := by
      calc a + b ≤ b + b := add_le_add h (le_refl b)
        _ = 2 * b := by ring
    calc (a + b) ^ (2 : ℕ) ≤ (2 * b) ^ (2 : ℕ) := pow_le_pow_left' hab 2
      _ = 4 * b ^ (2 : ℕ) := by ring
      _ ≤ 4 * (a ^ (2 : ℕ) + b ^ (2 : ℕ)) :=
          mul_le_mul' le_rfl (le_add_self)
  · have hab : a + b ≤ 2 * a := by
      calc a + b ≤ a + a := add_le_add (le_refl a) h
        _ = 2 * a := by ring
    calc (a + b) ^ (2 : ℕ) ≤ (2 * a) ^ (2 : ℕ) := pow_le_pow_left' hab 2
      _ = 4 * a ^ (2 : ℕ) := by ring
      _ ≤ 4 * (a ^ (2 : ℕ) + b ^ (2 : ℕ)) :=
          mul_le_mul' le_rfl (le_self_add)

/-- The square of a `1/2` power in `ℝ≥0∞`.  A private copy of the same helper
of `RHSTerm1InputsF.lean`. -/
private theorem sqRpowHalfH (x : ℝ≥0∞) : (x ^ ((1 : ℝ) / 2)) ^ (2 : ℕ) = x := by
  rw [← ENNReal.rpow_natCast (x ^ ((1 : ℝ) / 2)) 2, ← ENNReal.rpow_mul]
  norm_num

/-! ## The first display of Step 2 without the energy line -/

/-- **`hL2` of Step 2 with the printed energy line discharged.**  This is
the Step 2 display with `hEnergy` removed: the field is
the glued field `∇ũ_n` of `e.u.k.def` at coefficient level `ℓ`, and the energy
line `e.un.tilde.un.energy` is supplied by
`RHSTerm1InputsG.energy_bridge` at the two cube scales `S.ell` and `S.m` the
proof uses.  The remaining input is the printed centering `hQTilde`,
read through Jensen and Cauchy-Schwarz. -/
theorem l2_second_moment_bridge' (d : ℕ) [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (hnu1 : nu ≤ 1) {P : ProbabilityMeasure (ShellSeq d)}
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P)
    (hJ4 : ShellLawJ4 d P) (S : ScaleSelection) (hSorder : ScalesOrdering S)
    (e : Vec d) (uTildeGlued : ShellSeq d → Vec d → Vec d) (qTilde : Vec d)
    (hMemLp : ∀ omega : ShellSeq d,
      MemLp (hilbertifyVecField (fun x =>
          matVecMul ((coefficientCutoff nu omega S.ell).toCoeffField x)
            (uTildeGlued omega x) - qTilde)) 2
        (normalizedCubeMeasure (originCube d (S.m : ℤ))))
    (huT : uTildeGlued =
      gluedGradientField hnu S.ell S.n S.m (fluxSlot nu S.LPrime P S.n e))
    (hQTilde : ENNReal.ofReal (Real.sqrt (vecNormSq qTilde)) ≤
      (∫⁻ omega : ShellSeq d,
          (vecCubeLpENorm (originCube d (S.ell : ℤ)) 2
            (fun x => matVecMul ((coefficientCutoff nu omega S.ell).toCoeffField x)
              (uTildeGlued omega x))) ^ (2 : ℕ)
        ∂P.toMeasure : ℝ≥0∞) ^ ((1 : ℝ) / 2)) :
    (∫⁻ omega : ShellSeq d,
        (vecCubeLpENorm (originCube d (S.m : ℤ)) 2
          (fun x => matVecMul ((coefficientCutoff nu omega S.ell).toCoeffField x)
            (uTildeGlued omega x) - qTilde)) ^ (2 : ℕ)
      ∂P.toMeasure : ℝ≥0∞) ≤
      ENNReal.ofReal (hminusL2Const d * nu ^ (-(2 : ℝ)) *
        ((S.ell : ℝ) * (S.m : ℝ)) *
        vecNormSq (fluxSlot nu S.LPrime P S.n e)) := by
  have hEnergy : ∀ r : ℕ, S.n ≤ r → r ≤ S.m → ∀ omega : ShellSeq d,
      (vecCubeLpENorm (originCube d (r : ℤ)) 2 (uTildeGlued omega)) ^ (2 : ℕ) ≤
        ENNReal.ofReal (2 * nu ^ (-(2 : ℝ)) *
          vecNormSq (fluxSlot nu S.LPrime P S.n e)) := by
    intro r hnr hrmS omega
    rw [huT]
    exact energy_bridge hnu P S e hnr hrmS omega
  set sig : ℝ := vecNormSq (fluxSlot nu S.LPrime P S.n e) with hsig
  set En : ℝ := 2 * nu ^ (-(2 : ℝ)) * sig with hEn
  set K : ℝ := coeffCubeLinftySecondMomentConst d with hK
  have hsig0 : (0 : ℝ) ≤ sig := vecNormSq_nonneg _
  have hnu2 : (0 : ℝ) ≤ nu ^ (-(2 : ℝ)) := Real.rpow_nonneg (le_of_lt hnu) _
  have hEn0 : (0 : ℝ) ≤ En := by rw [hEn]; positivity
  have hK1 : (1 : ℝ) ≤ K := one_le_coeffCubeLinftySecondMomentConst hPrefix
  have hK0 : (0 : ℝ) ≤ K := le_trans (by norm_num) hK1
  have hlm : S.ell ≤ S.m :=
    le_of_lt (lt_trans hSorder.ell_lt_ellPrime hSorder.ellPrime_lt_m)
  -- the flux second moment on a cube of scale `r ≥ ℓ`
  have hflux : ∀ r : ℕ, S.ell ≤ r → r ≤ S.m →
      (∫⁻ omega : ShellSeq d,
          (vecCubeLpENorm (originCube d (r : ℤ)) 2
            (fun x => matVecMul ((coefficientCutoff nu omega S.ell).toCoeffField x)
              (uTildeGlued omega x))) ^ (2 : ℕ) ∂P.toMeasure : ℝ≥0∞) ≤
        ENNReal.ofReal En *
          ENNReal.ofReal (K * ((1 + (S.ell : ℝ)) * (1 + (r : ℝ)))) := by
    intro r hr hrmS
    have hptw : ∀ omega : ShellSeq d,
        (vecCubeLpENorm (originCube d (r : ℤ)) 2
          (fun x => matVecMul ((coefficientCutoff nu omega S.ell).toCoeffField x)
            (uTildeGlued omega x))) ^ (2 : ℕ) ≤
          ENNReal.ofReal En *
            (ENNReal.ofReal (coeffLinftySupBound nu S.ell r omega)) ^ (2 : ℕ) := by
      intro omega
      have hEn' := hEnergy r (le_trans (le_of_lt hSorder.n_lt_ell) hr) hrmS omega
      have hu_meas : AEStronglyMeasurable (hilbertifyVecField (uTildeGlued omega))
          (normalizedCubeMeasure (originCube d (r : ℤ))) := by
        have hfin : (vecCubeLpENorm (originCube d (r : ℤ)) 2 (uTildeGlued omega)) ^ (2 : ℕ) < ⊤ :=
          lt_of_le_of_lt hEn' ENNReal.ofReal_lt_top
        have hne : vecCubeLpENorm (originCube d (r : ℤ)) 2 (uTildeGlued omega) ≠ ⊤ := by
          intro h
          rw [h] at hfin
          simp at hfin
        by_contra hnm
        exact hne (MeasureTheory.eLpNorm_of_not_aestronglyMeasurable hnm)
      have hmul := vecCubeLpENorm_matVecMul_le (Q := originCube d (r : ℤ)) 2
        (fun x => (coefficientCutoff nu omega S.ell).toCoeffField x)
        (uTildeGlued omega)
        (coeffLinftySupBound_nonneg nu (le_of_lt hnu) S.ell r omega)
        (aestronglyMeasurable_hilbertifyVecField_matVecMul
          (continuous_coefficientCutoff_apply nu omega S.ell) hu_meas)
        (ae_matrixOperatorNorm_coefficientCutoff_le (le_of_lt hnu) omega S.ell r)
      calc (vecCubeLpENorm (originCube d (r : ℤ)) 2
            (fun x => matVecMul ((coefficientCutoff nu omega S.ell).toCoeffField x)
              (uTildeGlued omega x))) ^ (2 : ℕ)
          ≤ (ENNReal.ofReal (coeffLinftySupBound nu S.ell r omega) *
              vecCubeLpENorm (originCube d (r : ℤ)) 2 (uTildeGlued omega)) ^ (2 : ℕ) :=
            pow_le_pow_left' hmul 2
        _ = (ENNReal.ofReal (coeffLinftySupBound nu S.ell r omega)) ^ (2 : ℕ) *
              (vecCubeLpENorm (originCube d (r : ℤ)) 2 (uTildeGlued omega)) ^ (2 : ℕ) :=
            mul_pow _ _ 2
        _ ≤ (ENNReal.ofReal (coeffLinftySupBound nu S.ell r omega)) ^ (2 : ℕ) *
              ENNReal.ofReal En := mul_le_mul' le_rfl
              (hEnergy r (le_trans (le_of_lt hSorder.n_lt_ell) hr) hrmS omega)
        _ = ENNReal.ofReal En *
              (ENNReal.ofReal (coeffLinftySupBound nu S.ell r omega)) ^ (2 : ℕ) :=
            mul_comm _ _
    calc (∫⁻ omega : ShellSeq d,
          (vecCubeLpENorm (originCube d (r : ℤ)) 2
            (fun x => matVecMul ((coefficientCutoff nu omega S.ell).toCoeffField x)
              (uTildeGlued omega x))) ^ (2 : ℕ) ∂P.toMeasure)
        ≤ ∫⁻ omega : ShellSeq d, ENNReal.ofReal En *
            (ENNReal.ofReal (coeffLinftySupBound nu S.ell r omega)) ^ (2 : ℕ)
          ∂P.toMeasure := lintegral_mono hptw
      _ = ENNReal.ofReal En * ∫⁻ omega : ShellSeq d,
            (ENNReal.ofReal (coeffLinftySupBound nu S.ell r omega)) ^ (2 : ℕ)
          ∂P.toMeasure := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal En *
            ENNReal.ofReal (K * ((1 + (S.ell : ℝ)) * (1 + (r : ℝ)))) :=
          mul_le_mul' le_rfl (second_moment_coeffLinftySupBound_le hPrefix hJ2 hJ3
            hJ4 (le_of_lt hnu) hnu1 hr)
  -- the size of `q̃`
  have hq2 : ENNReal.ofReal (vecNormSq qTilde) ≤
      ENNReal.ofReal En *
        ENNReal.ofReal (K * ((1 + (S.ell : ℝ)) * (1 + (S.ell : ℝ)))) := by
    have hsq := pow_le_pow_left' hQTilde 2
    rw [sqRpowHalfH] at hsq
    refine le_trans (le_of_eq ?_) (le_trans hsq (hflux S.ell (le_refl S.ell) hlm))
    rw [← ENNReal.ofReal_pow (Real.sqrt_nonneg _),
      Real.sq_sqrt (vecNormSq_nonneg _)]
  -- the triangle inequality on the cube `cu_m`
  have hmeasFlux : ∀ omega : ShellSeq d,
      AEStronglyMeasurable (hilbertifyVecField (fun x =>
          matVecMul ((coefficientCutoff nu omega S.ell).toCoeffField x)
            (uTildeGlued omega x)))
        (normalizedCubeMeasure (originCube d (S.m : ℤ))) := by
    intro omega
    have hbase := (hMemLp omega).aestronglyMeasurable
    have hconst : AEStronglyMeasurable
        (hilbertifyVecField (fun _ : Vec d => qTilde))
        (normalizedCubeMeasure (originCube d (S.m : ℤ))) :=
      aestronglyMeasurable_const
    have hsum := hbase.add hconst
    have hfun : hilbertifyVecField (fun x =>
        matVecMul ((coefficientCutoff nu omega S.ell).toCoeffField x)
          (uTildeGlued omega x)) =
        (fun x => hilbertifyVecField (fun y =>
            matVecMul ((coefficientCutoff nu omega S.ell).toCoeffField y)
              (uTildeGlued omega y) - qTilde) x +
          hilbertifyVecField (fun _ : Vec d => qTilde) x) := by
      funext x
      simp only [hilbertifyVecField, HilbertVec.ofVec, ← WithLp.toLp_add,
        sub_add_cancel]
    rw [hfun]
    exact hsum
  have htri : ∀ omega : ShellSeq d,
      vecCubeLpENorm (originCube d (S.m : ℤ)) 2
        (fun x => matVecMul ((coefficientCutoff nu omega S.ell).toCoeffField x)
          (uTildeGlued omega x) - qTilde) ≤
        vecCubeLpENorm (originCube d (S.m : ℤ)) 2
          (fun x => matVecMul ((coefficientCutoff nu omega S.ell).toCoeffField x)
            (uTildeGlued omega x)) +
          ENNReal.ofReal (Real.sqrt (vecNormSq qTilde)) := by
    intro omega
    have hfun : (fun x : Vec d =>
          matVecMul ((coefficientCutoff nu omega S.ell).toCoeffField x)
            (uTildeGlued omega x) - qTilde) =
        (fun x : Vec d =>
          matVecMul ((coefficientCutoff nu omega S.ell).toCoeffField x)
            (uTildeGlued omega x) + (-qTilde)) := by
      funext x; rw [sub_eq_add_neg]
    have hconst : AEStronglyMeasurable
        (hilbertifyVecField (fun _ : Vec d => -qTilde))
        (normalizedCubeMeasure (originCube d (S.m : ℤ))) :=
      aestronglyMeasurable_const
    have hadd := vecCubeLpENorm_add_le (Q := originCube d (S.m : ℤ)) (q := 2)
      (F := fun x : Vec d => matVecMul
        ((coefficientCutoff nu omega S.ell).toCoeffField x) (uTildeGlued omega x))
      (G := fun _ : Vec d => -qTilde) (by norm_num) (hmeasFlux omega) hconst
    rw [hfun]
    refine le_trans hadd (add_le_add (le_refl _) ?_)
    have hneg : vecCubeLpENorm (originCube d (S.m : ℤ)) 2
        (fun _ : Vec d => -qTilde) =
        vecCubeLpENorm (originCube d (S.m : ℤ)) 2 (fun _ : Vec d => qTilde) :=
      vecCubeLpENorm_neg _ _ (fun _ : Vec d => qTilde)
    rw [hneg]
    refine Section2.Norms.cubeLpENorm_le_of_forall_le aestronglyMeasurable_const (fun x => ?_)
    rw [← ofReal_norm, norm_hilbertifyVecField_apply]
    refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
    rw [← Book.Ch02.vecNorm_sq_eq_vecNormSq qTilde,
      Real.sqrt_sq (Book.Ch02.vecNorm_nonneg qTilde)]
  -- the closing arithmetic
  have hsqq : (ENNReal.ofReal (Real.sqrt (vecNormSq qTilde))) ^ (2 : ℕ) =
      ENNReal.ofReal (vecNormSq qTilde) := by
    rw [← ENNReal.ofReal_pow (Real.sqrt_nonneg _), Real.sq_sqrt (vecNormSq_nonneg _)]
  have hbound : ∀ omega : ShellSeq d,
      (vecCubeLpENorm (originCube d (S.m : ℤ)) 2
        (fun x => matVecMul ((coefficientCutoff nu omega S.ell).toCoeffField x)
          (uTildeGlued omega x) - qTilde)) ^ (2 : ℕ) ≤
        4 * ((vecCubeLpENorm (originCube d (S.m : ℤ)) 2
              (fun x => matVecMul ((coefficientCutoff nu omega S.ell).toCoeffField x)
                (uTildeGlued omega x))) ^ (2 : ℕ) +
            ENNReal.ofReal (vecNormSq qTilde)) := by
    intro omega
    refine le_trans (pow_le_pow_left' (htri omega) 2) ?_
    refine le_trans (addSqLeH _ _) (le_of_eq ?_)
    rw [hsqq]
  have hconstMeas : AEMeasurable
      (fun _ : ShellSeq d => ENNReal.ofReal (vecNormSq qTilde)) P.toMeasure :=
    aemeasurable_const
  have hsplit : (∫⁻ omega : ShellSeq d,
      (vecCubeLpENorm (originCube d (S.m : ℤ)) 2
        (fun x => matVecMul ((coefficientCutoff nu omega S.ell).toCoeffField x)
          (uTildeGlued omega x) - qTilde)) ^ (2 : ℕ) ∂P.toMeasure) ≤
      4 * ((∫⁻ omega : ShellSeq d,
            (vecCubeLpENorm (originCube d (S.m : ℤ)) 2
              (fun x => matVecMul ((coefficientCutoff nu omega S.ell).toCoeffField x)
                (uTildeGlued omega x))) ^ (2 : ℕ) ∂P.toMeasure) +
          ENNReal.ofReal (vecNormSq qTilde)) := by
    calc (∫⁻ omega : ShellSeq d,
        (vecCubeLpENorm (originCube d (S.m : ℤ)) 2
          (fun x => matVecMul ((coefficientCutoff nu omega S.ell).toCoeffField x)
            (uTildeGlued omega x) - qTilde)) ^ (2 : ℕ) ∂P.toMeasure)
        ≤ ∫⁻ omega : ShellSeq d,
            4 * ((vecCubeLpENorm (originCube d (S.m : ℤ)) 2
                  (fun x => matVecMul
                    ((coefficientCutoff nu omega S.ell).toCoeffField x)
                    (uTildeGlued omega x))) ^ (2 : ℕ) +
                ENNReal.ofReal (vecNormSq qTilde)) ∂P.toMeasure :=
          lintegral_mono hbound
      _ = 4 * ∫⁻ omega : ShellSeq d,
            ((vecCubeLpENorm (originCube d (S.m : ℤ)) 2
                (fun x => matVecMul
                  ((coefficientCutoff nu omega S.ell).toCoeffField x)
                  (uTildeGlued omega x))) ^ (2 : ℕ) +
              ENNReal.ofReal (vecNormSq qTilde)) ∂P.toMeasure :=
          lintegral_const_mul' _ _ (by norm_num)
      _ = 4 * ((∫⁻ omega : ShellSeq d,
              (vecCubeLpENorm (originCube d (S.m : ℤ)) 2
                (fun x => matVecMul
                  ((coefficientCutoff nu omega S.ell).toCoeffField x)
                  (uTildeGlued omega x))) ^ (2 : ℕ) ∂P.toMeasure) +
            ENNReal.ofReal (vecNormSq qTilde)) := by
          rw [lintegral_add_right' _ hconstMeas, lintegral_const, measure_univ,
            mul_one]
  -- the two annealed inputs, at the common size `(1+ℓ)(1+m)`
  have hl1 : 1 ≤ S.ell := lt_of_le_of_lt (Nat.zero_le _) hSorder.n_lt_ell
  have hm1 : 1 ≤ S.m := le_trans hl1 hlm
  have hlR : (1 : ℝ) ≤ (S.ell : ℝ) := by exact_mod_cast hl1
  have hmR : (1 : ℝ) ≤ (S.m : ℝ) := by exact_mod_cast hm1
  have hlmR : (S.ell : ℝ) ≤ (S.m : ℝ) := by exact_mod_cast hlm
  have hcommon : ENNReal.ofReal En *
      ENNReal.ofReal (K * ((1 + (S.ell : ℝ)) * (1 + (S.ell : ℝ)))) ≤
      ENNReal.ofReal En *
        ENNReal.ofReal (K * ((1 + (S.ell : ℝ)) * (1 + (S.m : ℝ)))) := by
    refine mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal ?_)
    have hone : (0 : ℝ) ≤ 1 + (S.ell : ℝ) := by linarith only [hlR]
    have hmul : (1 + (S.ell : ℝ)) * (1 + (S.ell : ℝ)) ≤
        (1 + (S.ell : ℝ)) * (1 + (S.m : ℝ)) := by
      exact mul_le_mul_of_nonneg_left (by linarith only [hlmR]) hone
    exact mul_le_mul_of_nonneg_left hmul hK0
  have htwo : (∫⁻ omega : ShellSeq d,
        (vecCubeLpENorm (originCube d (S.m : ℤ)) 2
          (fun x => matVecMul ((coefficientCutoff nu omega S.ell).toCoeffField x)
            (uTildeGlued omega x))) ^ (2 : ℕ) ∂P.toMeasure) +
      ENNReal.ofReal (vecNormSq qTilde) ≤
      2 * (ENNReal.ofReal En *
        ENNReal.ofReal (K * ((1 + (S.ell : ℝ)) * (1 + (S.m : ℝ))))) := by
    have hA := hflux S.m hlm (le_refl S.m)
    have hB := le_trans hq2 hcommon
    calc (∫⁻ omega : ShellSeq d,
          (vecCubeLpENorm (originCube d (S.m : ℤ)) 2
            (fun x => matVecMul ((coefficientCutoff nu omega S.ell).toCoeffField x)
              (uTildeGlued omega x))) ^ (2 : ℕ) ∂P.toMeasure) +
        ENNReal.ofReal (vecNormSq qTilde)
        ≤ ENNReal.ofReal En *
              ENNReal.ofReal (K * ((1 + (S.ell : ℝ)) * (1 + (S.m : ℝ)))) +
            ENNReal.ofReal En *
              ENNReal.ofReal (K * ((1 + (S.ell : ℝ)) * (1 + (S.m : ℝ)))) :=
          add_le_add hA hB
      _ = 2 * (ENNReal.ofReal En *
            ENNReal.ofReal (K * ((1 + (S.ell : ℝ)) * (1 + (S.m : ℝ))))) := by ring
  refine le_trans hsplit (le_trans (mul_le_mul' (le_refl (4 : ℝ≥0∞)) htwo) ?_)
  have hprod : ENNReal.ofReal En *
      ENNReal.ofReal (K * ((1 + (S.ell : ℝ)) * (1 + (S.m : ℝ)))) =
      ENNReal.ofReal (En * (K * ((1 + (S.ell : ℝ)) * (1 + (S.m : ℝ))))) :=
    (ENNReal.ofReal_mul hEn0).symm
  have height : (4 : ℝ≥0∞) * (2 * ENNReal.ofReal
        (En * (K * ((1 + (S.ell : ℝ)) * (1 + (S.m : ℝ)))))) =
      ENNReal.ofReal (8 * (En * (K * ((1 + (S.ell : ℝ)) * (1 + (S.m : ℝ)))))) := by
    have hnn : (0 : ℝ) ≤ En * (K * ((1 + (S.ell : ℝ)) * (1 + (S.m : ℝ)))) := by
      have h1 : (0 : ℝ) ≤ 1 + (S.ell : ℝ) := by linarith only [hlR]
      have h2 : (0 : ℝ) ≤ 1 + (S.m : ℝ) := by linarith only [hmR]
      positivity
    rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 8), ← mul_assoc]
    congr 1
    rw [show ((8 : ℝ)) = 4 * 2 by norm_num, ENNReal.ofReal_mul (by norm_num),
      ENNReal.ofReal_ofNat, ENNReal.ofReal_ofNat]
  rw [hprod, height]
  refine ENNReal.ofReal_le_ofReal ?_
  have hbig : (1 + (S.ell : ℝ)) * (1 + (S.m : ℝ)) ≤ 4 * ((S.ell : ℝ) * (S.m : ℝ)) := by
    have h1 : 1 + (S.ell : ℝ) ≤ 2 * (S.ell : ℝ) := by linarith only [hlR]
    have h2 : 1 + (S.m : ℝ) ≤ 2 * (S.m : ℝ) := by linarith only [hmR]
    have h3 : (0 : ℝ) ≤ 1 + (S.ell : ℝ) := by linarith only [hlR]
    have h4 : (0 : ℝ) ≤ 2 * (S.m : ℝ) := by linarith only [hmR]
    calc (1 + (S.ell : ℝ)) * (1 + (S.m : ℝ))
        ≤ (1 + (S.ell : ℝ)) * (2 * (S.m : ℝ)) :=
          mul_le_mul_of_nonneg_left h2 h3
      _ ≤ (2 * (S.ell : ℝ)) * (2 * (S.m : ℝ)) :=
          mul_le_mul_of_nonneg_right h1 h4
      _ = 4 * ((S.ell : ℝ) * (S.m : ℝ)) := by ring
  have hEnEq : En = 2 * nu ^ (-(2 : ℝ)) * sig := hEn
  have hlmpos : (0 : ℝ) ≤ (S.ell : ℝ) * (S.m : ℝ) := by
    have : (0 : ℝ) ≤ (S.ell : ℝ) := by linarith only [hlR]
    positivity
  have hstepR : 8 * (En * (K * ((1 + (S.ell : ℝ)) * (1 + (S.m : ℝ))))) ≤
      64 * K * (nu ^ (-(2 : ℝ)) * ((S.ell : ℝ) * (S.m : ℝ)) * sig) := by
    have hmono : K * ((1 + (S.ell : ℝ)) * (1 + (S.m : ℝ))) ≤
        K * (4 * ((S.ell : ℝ) * (S.m : ℝ))) :=
      mul_le_mul_of_nonneg_left hbig hK0
    have hEn' : 8 * (En * (K * ((1 + (S.ell : ℝ)) * (1 + (S.m : ℝ))))) ≤
        8 * (En * (K * (4 * ((S.ell : ℝ) * (S.m : ℝ))))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hmono hEn0)
        (by norm_num)
    refine le_trans hEn' (le_of_eq ?_)
    rw [hEnEq]
    ring
  refine le_trans hstepR ?_
  have hCle : 64 * K ≤ hminusL2Const d := by
    rw [hminusL2Const, hK]
    exact le_max_right _ _
  have hrest : (0 : ℝ) ≤ nu ^ (-(2 : ℝ)) * ((S.ell : ℝ) * (S.m : ℝ)) * sig := by
    positivity
  have hmul := mul_le_mul_of_nonneg_right hCle hrest
  calc 64 * K * (nu ^ (-(2 : ℝ)) * ((S.ell : ℝ) * (S.m : ℝ)) * sig)
      ≤ hminusL2Const d * (nu ^ (-(2 : ℝ)) * ((S.ell : ℝ) * (S.m : ℝ)) * sig) := hmul
    _ = hminusL2Const d * nu ^ (-(2 : ℝ)) * ((S.ell : ℝ) * (S.m : ℝ)) * sig := by ring

/-! ## Step 1 with the localization line on the honest range -/

/-! ## `l.RHS.term1` from the anchors, without the energy line -/

end

end SuperdiffusionCLT.Section3.Terms

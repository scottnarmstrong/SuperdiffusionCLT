/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section4.MinimalScales.LimitRespEntryBound
public import SuperdiffusionCLT.Section4.MinimalScales.SkeletonMathcalE

/-!
# Everywhere ellipticity of the shifted cutoff field `srootE_field`

`srootE_field nu omega L m n k` (`SkeletonMathcalE.lean`) is the centered
cutoff field `centeredCoefficientCutoff nu omega L (cubeSet (originCube d m))`
precomposed with the constant shift `x ↦ 3^{n-3} k + x`. This module transfers
the entry bound of `LimitRespEntryBound.lean` and the constant symmetric part
of `centeredCoefficientCutoff` (`symmPart_centeredCoefficientCutoff`) through
that shift, using the hypothesis that the shifted image of `cubeSet (originCube
d n)` lands inside the recentering cube `cubeSet (originCube d m)`, to get an
EVERYWHERE (not merely a.e.) `IsEllipticFieldOn` statement on
`cubeSet (originCube d n)` — uniform over every scale `l` used inside
`srootE_term`, since `IsEllipticFieldOn` is a domain-wide, not per-scale,
predicate.

## Main result

* `srootL3_isEllipticFieldOn_srootE_field`: `srootE_field nu omega L m n k` is
  `(nu, Lam)`-elliptic everywhere on `cubeSet (originCube d n)`, for an
  explicit `Lam` depending only on `nu, d`, and the entry bound of the
  recentered field on `cubeSet (originCube d m)`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section4.MinimalScales

open Homogenization MeasureTheory
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.CoarseGraining

noncomputable section

/-- **The shifted cutoff field `srootE_field` is everywhere `(nu, Lam)`-elliptic
on `cubeSet (originCube d n)`.** -/
theorem srootL3_isEllipticFieldOn_srootE_field {d : ℕ} [NeZero d] (nu : ℝ) (hnu : 0 < nu)
    (omega : ShellSeq d) (L m n : ℕ) (k : Fin d → ℤ)
    (hk : (fun x => (fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x) ''
          cubeSet (originCube d (n : ℤ)) ⊆ cubeSet (originCube d (m : ℤ))) :
    ∃ Lam : ℝ, IsEllipticFieldOn nu Lam (cubeSet (originCube d (n : ℤ)))
        (srootE_field nu omega L m n k) := by
  classical
  obtain ⟨C, hC⟩ := srootL3_exists_centeredEntryBound nu hnu.le omega L m
  refine ⟨((d : ℝ) * (d : ℝ) * C ^ 2 + nu ^ 2) / nu, ?_, ?_⟩
  · refine Measurable.of_eval fun i => Measurable.of_eval fun j => ?_
    have h1 : Measurable (fun y : Vec d =>
        (centeredCoefficientCutoff nu omega L
            (cubeSet (originCube d (m : ℤ)))).toCoeffField y i j) :=
      (centeredCoefficientCutoff nu omega L
        (cubeSet (originCube d (m : ℤ)))).entry_measurable i j
    have h2 : Measurable (fun x : Vec d =>
        (fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x) :=
      measurable_const.add measurable_id
    exact (h1.comp h2).ite (measurableSet_cubeSet _) measurable_const
  · intro x hx
    have hxU : (fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x ∈
        cubeSet (originCube d (m : ℤ)) :=
      hk ⟨x, hx, rfl⟩
    exact isEllipticMatrix_of_symmPart_eq_smul_one hnu
      (symmPart_centeredCoefficientCutoff nu omega L (cubeSet (originCube d (m : ℤ))) _)
      (hC _ hxU)

end

end SuperdiffusionCLT.Section4.MinimalScales

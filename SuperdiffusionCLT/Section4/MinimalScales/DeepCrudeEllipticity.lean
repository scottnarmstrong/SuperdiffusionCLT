/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section4.MinimalScales.SkeletonMathcalE
public import SuperdiffusionCLT.Section2.Cutoff.Size
public import SuperdiffusionCLT.Section2.CoarseGraining.CutoffCorrespondence

/-!
# srootD2: everywhere ellipticity of the centered, shifted deep-scale field

This module supplies the first of three ingredients of the deep-scale bound in the proof of
`p.new.mixing.attempt` (`e.new.mixing.attempt.deep`): the centered field `srootE_field`
(`SkeletonMathcalE.lean`) is `(nu, Lam)`-elliptic **everywhere** (not merely a.e.) on the
whole origin cube `cu_n`, for a single sample-dependent `Lam` that does not depend on which
deep-scale descendant of `cu_n` is examined. Consequently every descendant
cube inherits the *same* `Lam` (`Homogenization.IsEllipticFieldOn.mono`), so
no union bound over the growing lattice of deep-scale cubes is ever needed —
the route `Section4/Mixing/TermTailEllipticity.lean`'s
`mixTail_isEllipticFieldOn_coefficientCutoff_cubeSet` takes for the
uncentered cutoff field, here applied to the centered, shifted field
`srootE_field` at scale `n` (rather than `m`).

**What this module does not do.** It does not bound the resulting
`normalizedBlockResponseMax`/`scaleResponseAtScale` in terms of `Lam` (the
second ingredient: the response bound via
`Homogenization.blockJ_eq_half_responseJ_adjoint_sum_of_isEllipticFieldOn_of_isOpenBoundedConvexDomain`
and `Homogenization.responseJ_le_plainUpperBound_of_isEllipticFieldOn`), and it
does not give `Lam` a `Γ_1` moment bound (the third ingredient). The latter cannot
deliver a *flat* (`m`-independent) amplitude: `Lam` is a compactness bound
over the whole cube `cu_n`, and
`n` is within `K log m` of `m`, so `Lam`'s typical size grows with `m` exactly as the paper's own
crude bound `O_{Γ_1}(C ν^{-3} m)` does (Step 2 of the proof of
`p.new.mixing.attempt`).
-/

@[expose] public section

namespace SuperdiffusionCLT.Section4.MinimalScales

open Homogenization

noncomputable section

variable {d : ℕ} [NeZero d]

/-- `srootE_field` unfolds to the centered cutoff field, shifted by the
translate `3^{n-3} k`, evaluated at `x`, in the additive shape produced by
`centeredCoefficientCutoff_apply` and `centeredStreamCutoff_apply`. -/
theorem srootD2_srootE_field_eq (nu : ℝ)
    (omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d) (L m n : ℕ)
    (k : Fin d → ℤ) (x : Vec d) :
    srootE_field nu omega L m n k x =
      nu • (1 : Mat d) +
        (SuperdiffusionCLT.Frozen.Section2.streamCutoff omega L
            ((fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x) -
          Homogenization.volumeAverageMat
            (cubeSet (originCube d (m : ℤ)))
            (SuperdiffusionCLT.Frozen.Section2.streamCutoff omega L)) := by
  unfold srootE_field
  simp only [Homogenization.RegCoeffField.toCoeffField_apply,
    SuperdiffusionCLT.Section2.Cutoff.centeredCoefficientCutoff_apply,
    SuperdiffusionCLT.Section2.Cutoff.centeredStreamCutoff_apply]

/-- **Continuity in the spatial variable.** The centered, shifted field is a
continuous function of `x`: the shift is affine, the stream cutoff is
continuous (`continuous_streamCutoff_apply`), and the average subtracted is a
constant matrix. -/
theorem srootD2_continuous_srootE_field (nu : ℝ)
    (omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d) (L m n : ℕ)
    (k : Fin d → ℤ) :
    Continuous (fun x : Vec d => srootE_field nu omega L m n k x) := by
  have hfun : (fun x : Vec d => srootE_field nu omega L m n k x) =
      fun x : Vec d =>
        nu • (1 : Mat d) +
          (SuperdiffusionCLT.Frozen.Section2.streamCutoff omega L
              ((fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x) -
            Homogenization.volumeAverageMat
              (cubeSet (originCube d (m : ℤ)))
              (SuperdiffusionCLT.Frozen.Section2.streamCutoff omega L)) :=
    funext fun x => srootD2_srootE_field_eq nu omega L m n k x
  rw [hfun]
  exact continuous_const.add
    (((SuperdiffusionCLT.Section2.Cutoff.continuous_streamCutoff_apply omega L).comp
      (continuous_const.add continuous_id)).sub continuous_const)

/-- **The symmetric part is the deterministic `nu • 1`**, at every point,
directly from `symmPart_centeredCoefficientCutoff`. -/
theorem srootD2_symmPart_srootE_field (nu : ℝ)
    (omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d) (L m n : ℕ)
    (k : Fin d → ℤ) (x : Vec d) :
    Homogenization.symmPart (srootE_field nu omega L m n k x) = nu • (1 : Mat d) := by
  unfold srootE_field
  simp only [Homogenization.RegCoeffField.toCoeffField_apply]
  exact SuperdiffusionCLT.Section2.Cutoff.symmPart_centeredCoefficientCutoff nu omega L
    (cubeSet (originCube d (m : ℤ)))
    ((fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x)

end

end SuperdiffusionCLT.Section4.MinimalScales

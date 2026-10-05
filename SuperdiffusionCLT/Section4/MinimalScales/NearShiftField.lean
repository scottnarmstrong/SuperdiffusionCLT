/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section4.MinimalScales.SkeletonMathcalE
public import SuperdiffusionCLT.Section2.CoarseGraining.SkewShiftCutoff
public import SuperdiffusionCLT.Section2.Cutoff.Centered

/-!
# The centered field as a shifted cutoff field

`srootE_field nu omega L m n k`, the `cu_m`-centered cutoff field read at the shift
`z = 3^{n-3} k`, is the translate by `z` of `a_L + h_0` with the random skew shift
`h_0 = -(k_L)_{cu_m}`. This lets the near-scale argument apply the parameterized mixing lemma at
`h_0 = h0 omega L`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section4.MinimalScales

/-- The random skew shift `h_0 = -(k_L)_{cu_m}`. -/
noncomputable def srootNS_h0 {d : ℕ} (m L : ℕ)
    (omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d) : Homogenization.Mat d :=
  -Homogenization.volumeAverageMat
    (Homogenization.cubeSet (Homogenization.originCube d (m : ℤ)))
    (SuperdiffusionCLT.Frozen.Section2.streamCutoff omega L)

/-- `h0 omega L` is skew. -/
theorem srootNS_h0_skew {d : ℕ} (m L : ℕ)
    (omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d) :
    Homogenization.matTranspose (srootNS_h0 m L omega) = -srootNS_h0 m L omega :=
  SuperdiffusionCLT.Section2.CoarseGraining.matTranspose_neg_volumeAverageMat_streamCutoff
    omega L _

/-- The centered field `srootE_field` is the translate by `z = 3^{n-3} k` of
`(a_L + h_0).toCoeffField`, `h_0 = -(k_L)_{cu_m}`. The identity holds as fields on all of space,
in particular on every descendant cube of `cu_n`. -/
theorem srootNS_srootE_field_eq_aLplusH0 {d : ℕ} [NeZero d] (nu : ℝ) (hnu : 0 < nu)
    (omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d) (L m n : ℕ) (k : Fin d → ℤ) :
    srootE_field nu omega L m n k =
      Homogenization.translateCoeffField
        (fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ))
        (SuperdiffusionCLT.Section4.NewMixing.newMixParam_aLplusH0 nu hnu omega L m
          (srootNS_h0 m L omega) (srootNS_h0_skew m L omega)).toCoeffField := by
  funext x
  have h := SuperdiffusionCLT.Section2.CoarseGraining.centeredCoefficientCutoff_toCoeffField
    nu omega L (Homogenization.cubeSet (Homogenization.originCube d (m : ℤ)))
  unfold srootE_field Homogenization.translateCoeffField
  rw [h]
  simp only [SuperdiffusionCLT.Section4.NewMixing.newMixParam_aLplusH0,
    SuperdiffusionCLT.Section2.CoarseGraining.addConstSkewCoeffOn_toCoeffField,
    SuperdiffusionCLT.Section2.CoarseGraining.coefficientCutoffCoeffOn_toCoeffField,
    srootNS_h0]
  congr 2
  funext i
  exact add_comm _ _

/-- Witness: the identity is instantiated at `d = 1`, `nu = 1`, `m = 0`, `n = 3`, `k = 0`,
needing only `0 < nu`. -/
example (omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq 1) :
    ∃ f : Homogenization.CoeffField 1,
      srootE_field (d := 1) 1 omega 0 0 3 (fun _ => 0) = f :=
  ⟨_, srootNS_srootE_field_eq_aLplusH0 1 one_pos omega 0 0 3 _⟩

end SuperdiffusionCLT.Section4.MinimalScales

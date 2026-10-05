/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section4.MinimalScales.NearShiftAssemblyG
public import SuperdiffusionCLT.Section4.MinimalScales.NearLocalBridge
public import SuperdiffusionCLT.Section4.MinimalScales.DeepCrudePoly
public import SuperdiffusionCLT.Section2.Estimates.Stream.IncrementMoreoverBlockB
public import SuperdiffusionCLT.Section2.Localization.CutoffMinimizerClause

/-!
# Bridges from a translated descendant domain to the near-tail comparison

* `srootNS_volumeAverageMat_cubeSet_origin_eq_cubeDomain`: the closed-cube average equals the
  average over the open-cube domain.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section4.MinimalScales

noncomputable section

/-- The closed-cube average at scale `m` is the average over the domain `cubeDomain (cu_m)`. -/
theorem srootNS_volumeAverageMat_cubeSet_origin_eq_cubeDomain {d : ℕ} (m : ℕ)
    (f : Homogenization.Vec d → Homogenization.Mat d) :
    Homogenization.volumeAverageMat (Homogenization.cubeSet (Homogenization.originCube d (m : ℤ))) f =
      Homogenization.volumeAverageMat
        ((Homogenization.Book.Ch02.cubeDomain (Homogenization.originCube d (m : ℤ)) :
          Homogenization.Book.Ch02.Domain d) : Set (Homogenization.Vec d)) f := by
  rw [Homogenization.Book.Ch02.cubeDomain_coe]
  exact SuperdiffusionCLT.Section2.Estimates.Stream.volumeAverageMat_cubeSet_eq_openCubeSet _ f

/-- Witness for the non-bound hypotheses of G1 (`d = 1`, `z = 0`, `Q = cu_0`, `f` the field of
`a_L + 0` for `nu = 1`): a domain, a coefficient with that field, and its ellipticity. -/
example (omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq 1) :
    ∃ (U : Homogenization.Book.Ch02.Domain 1) (b : Homogenization.Book.Ch02.CoeffOn U),
      (U : Set (Homogenization.Vec 1)) =
        Homogenization.translateSet (0 : Homogenization.Vec 1)
          (Homogenization.openCubeSet (Homogenization.originCube 1 (0 : ℤ))) ∧
      Homogenization.IsEllipticFieldOn b.lam b.Lam (U : Set (Homogenization.Vec 1)) b.toCoeffField := by
  have h0 : Homogenization.matTranspose (0 : Homogenization.Mat 1) = -0 := by
    simp [Homogenization.matTranspose]
  refine ⟨Homogenization.Book.Ch02.cubeDomain (Homogenization.originCube 1 (0 : ℤ)),
    SuperdiffusionCLT.Section4.NewMixing.newMixParam_aLplusH0 1 one_pos omega 0 0 0 h0, ?_, ?_⟩
  · rw [Homogenization.Book.Ch02.cubeDomain_coe]
    ext x
    simp [Homogenization.translateSet]
  · exact SuperdiffusionCLT.Section4.NewMixing.newMixAsm_isEllipticFieldOn_aLplusH0
      one_pos omega 0 0 h0 _

end

end SuperdiffusionCLT.Section4.MinimalScales

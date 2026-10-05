/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Localization.LocalizationDisplayA
public import SuperdiffusionCLT.Section2.Localization.BlockPerturbation
public import SuperdiffusionCLT.Section2.Annealed.EnvelopeDomain
public import SuperdiffusionCLT.Section2.CoarseGraining.SkewShiftCutoff

/-!
# The deterministic per-cube localization estimate

The comparison in the proof of `l.localization.average` follows
from `coarseBlockMatrix_localization_scalar_two_sided` at the actual supremum
`localizationPerturbSize`. Continuity on a compact set containing the cube
bounds the defining range, so its supremum controls every point of the cube.
The finite shell increment and its cube average are skew-symmetric. Subtracting
that average from the upper cutoff produces exactly the gauge conjugation in
the printed display.

`localization_display_e_hpoint` requires only positive diffusivity, ordered
cutoff levels, and a nonzero dimension. It applies to every shell sequence and
every triadic cube, with no probabilistic or analytic estimate as a premise.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section2.Localization

variable {d : ℕ}

private theorem localization_display_e_size_bdd (l L : ℕ)
    (R : Homogenization.TriadicCube d)
    (omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d) :
    BddAbove (Set.range (localizationPerturbSizeAtIndex l L R omega)) := by
  have hc : Continuous (fun x : Homogenization.Vec d =>
      SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement omega l L x) := by
    have hs := continuous_finsetSum (Finset.Ioc l L)
      (fun k _ => (omega k).1.1.continuous)
    exact hs.congr (fun x =>
      (SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement_apply omega l L x).symm)
  have hn := SuperdiffusionCLT.Frozen.Assumptions.ShellField.continuous_matrixOperatorNorm.comp
    (hc.sub (continuous_const (y := localizationGaugeAverage l L R omega)))
  obtain ⟨C, hC⟩ := (isCompact_closedBall (Homogenization.cubeCenter R)
    (Homogenization.cubeRadius R)).exists_bound_of_continuousOn hn.continuousOn
  refine ⟨max 0 C, ?_⟩
  rintro _ ⟨o, rfl⟩
  cases o with
  | none => exact le_max_left _ _
  | some x =>
    exact (le_abs_self _).trans ((hC x.1
      (Homogenization.cubeSet_subset_closedBall R x.2)).trans (le_max_right _ _))

private theorem localization_display_e_cube_coarse [NeZero d] {nu : ℝ}
    (hnu : 0 < nu) (l : ℕ) (R : Homogenization.TriadicCube d)
    (omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d) :
    Homogenization.Book.Ch02.coarseBlockMatrix (Homogenization.Book.Ch02.cubeDomain R)
      (SuperdiffusionCLT.Section2.Annealed.cutoffDomainCoeffOn
        (Homogenization.Book.Ch02.cubeDomain R) hnu omega l) =
        localizationCoarseAt nu l R omega := by
  rw [← SuperdiffusionCLT.Section2.Annealed.coarseBlockMatrix_domain_eq_ch02]
  exact (Homogenization.coarseBlockMatrix_cubeSet_eq_openCubeSet_of_triadicCube R
    (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff nu omega l).toCoeffField).symm

/-- The deterministic per-cube comparison of the printed proof. -/
theorem localization_display_e_hpoint [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    {l L : ℕ} (hlL : l ≤ L) (R : Homogenization.TriadicCube d)
    (Pvec : Homogenization.BlockVec d)
    (omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d) :
    |localizationT1CubeError nu l L R Pvec omega| ≤
      localizationDz nu l L R omega * localizationB nu l L R Pvec omega := by
  let U := Homogenization.Book.Ch02.cubeDomain R
  let a := SuperdiffusionCLT.Section2.Annealed.cutoffDomainCoeffOn
        (Homogenization.Book.Ch02.cubeDomain R) hnu omega l
  let aL := SuperdiffusionCLT.Section2.Annealed.cutoffDomainCoeffOn U hnu omega L
  let g := localizationGaugeAverage l L R omega
  have hg0 : Homogenization.matTranspose g = -g := by
    apply SuperdiffusionCLT.Section2.Cutoff.matTranspose_volumeAverageMat
    intro x i j
    exact congrFun (congrFun
      (SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement_skew omega l L x) j) i
  have hg : Homogenization.matTranspose (-g) = -(-g) := by
    change -(Homogenization.matTranspose g) = -(-g)
    rw [hg0]
  let b := SuperdiffusionCLT.Section2.CoarseGraining.addConstSkewCoeffOn aL hg
  let h := fun x => SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement omega l L x - g
  have hs : ∀ᵐ x ∂(Homogenization.volumeMeasureOn (U : Set (Homogenization.Vec d))),
      Homogenization.symmPart (a.toCoeffField x) = nu • (1 : Homogenization.Mat d) :=
    Filter.Eventually.of_forall
      (SuperdiffusionCLT.Section2.Cutoff.symmPart_coefficientCutoff nu omega l)
  have hb : ∀ᵐ x ∂(Homogenization.volumeMeasureOn (U : Set (Homogenization.Vec d))),
      b.toCoeffField x = a.toCoeffField x + h x := by
    apply Filter.Eventually.of_forall
    intro x
    change (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff nu omega L).toCoeffField x
      + -g = (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff nu omega l).toCoeffField x
        + (SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement omega l L x - g)
    rw [SuperdiffusionCLT.Section2.Cutoff.coefficientCutoff_toCoeffField_apply,
      SuperdiffusionCLT.Section2.Cutoff.coefficientCutoff_toCoeffField_apply,
      SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement_apply_eq_streamCutoff_sub
        omega hlL x]
    abel
  have hk : ∀ᵐ x ∂(Homogenization.volumeMeasureOn (U : Set (Homogenization.Vec d))),
      Homogenization.matTranspose (h x) = -h x := by
    apply Filter.Eventually.of_forall
    intro x
    change Homogenization.matTranspose
      (SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement omega l L x + -g) = _
    rw [show Homogenization.matTranspose
        (SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement omega l L x + -g) =
      Homogenization.matTranspose
        (SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement omega l L x) +
      Homogenization.matTranspose (-g) from Matrix.transpose_add _ _, hg]
    rw [show Homogenization.matTranspose
        (SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement omega l L x) =
      -SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement omega l L x from
        SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement_skew omega l L x]
    dsimp [h]
    abel
  have hn : ∀ᵐ x ∂(Homogenization.volumeMeasureOn (U : Set (Homogenization.Vec d))),
      ∀ w : Homogenization.Vec d,
      Homogenization.vecNormSq (Homogenization.matVecMul (h x) w) ≤
        localizationPerturbSize l L R omega ^ 2 * Homogenization.vecNormSq w := by
    filter_upwards [MeasureTheory.ae_restrict_mem U.measurableSet] with x hx
    intro w
    have hxR : x ∈ Homogenization.cubeSet R :=
      Homogenization.openCubeSet_subset_cubeSet R hx
    have hle : Homogenization.Book.Ch02.matrixOperatorNorm (h x) ≤
        localizationPerturbSize l L R omega :=
      le_csSup (localization_display_e_size_bdd l L R omega) ⟨some ⟨x, hxR⟩, rfl⟩
    exact (Homogenization.Book.Ch02.vecNormSq_matVecMul_le_matrixOperatorNorm_sq_mul_vecNormSq
      (h x) w).trans (mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (Homogenization.Book.Ch02.matrixOperatorNorm_nonneg _) hle 2)
        (Homogenization.vecNormSq_nonneg w))
  have hmain := coarseBlockMatrix_localization_scalar_two_sided hnu
    (localizationPerturbSize_nonneg l L R omega) hs hb hk hn
  have hga := SuperdiffusionCLT.Section2.CoarseGraining.coarseBlockMatrix_addConstSkewCoeffOn
    aL hg
  simp only [neg_neg] at hga
  rw [hga, localization_display_e_cube_coarse hnu L R omega,
    localization_display_e_cube_coarse hnu l R omega] at hmain
  exact localizationT1CubeError_abs_le_Dz_mul_localizationB l L R Pvec omega
    hmain.1 hmain.2

end SuperdiffusionCLT.Section2.Localization

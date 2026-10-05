/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Localization.LocalizationAverageAssembly
public import SuperdiffusionCLT.Probability.ConditionalGammaTailShell
public import SuperdiffusionCLT.Assumptions.ShellLaw.J3Consequences
public import SuperdiffusionCLT.Section2.Estimates.Stream.IncrementMoreoverBlock

/-!
# Shell coordinates and measurability for the second summand `T2`

The second printed summand of `e.localization.average.oneshot` works with the normalized
centered variables `X_z` and the second-summand variables `Z_z`, together with the weights
`W_z := |bfE_ℓ^{1/2} G_{-h_z}P|²` and `Wbar := max_z W_z`, where `h_z` is the volume average of
the finite shell increment on `z + cu_n`.

**Both variables are functions of two complementary coordinate families.**  The gauge vectors
`G_{-h_z}P` and the maximum `M(P)` are functionals of the *upper* shells `{r | ℓ < r}`, i.e. of
`shellSigma {r | ℓ < r}` (the printed `F_> := σ(j_r : r > ℓ)`); the cutoff matrix
`bfA_ℓ(z+cu_n)` is a functional of the *lower* shells `{r | r ≤ ℓ}`.  This is the content of the
printed sentence "since `h_z` depends only on the scales `{j_r}_{r > ℓ}` while `bfA_ℓ` is
measurable with respect to `{j_r}_{r ≤ ℓ}`".  It is what the complement-measurability
hypothesis of a conditional concentration argument needs: the summands must be measurable for
the coordinate family complementary to the conditioning one.

## Main results

* `shellSigma_coordinate_measurable`: a shell coordinate is measurable for the σ-algebra of any
  coordinate family containing it.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section2.Localization

open MeasureTheory Homogenization Homogenization.Book.Ch02
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Cutoff

variable {d : ℕ}

/-! ## Measurability for a coordinate family

A function of a single shell coordinate is measurable for the σ-algebra of any
coordinate family containing that coordinate.  This is the form in which the
printed complement measurability of the lower-coordinate summands enters the
conditional chain. -/

/-- **A shell coordinate is measurable for the σ-algebra of any family
containing it.**  The σ-algebra `shellSigma S` is the supremum of the comaps of
the coordinates in `S`, so membership `n ∈ S` makes the `n`-th projection
measurable. -/
theorem shellSigma_coordinate_measurable {S : Set ℕ} {n : ℕ} (hn : n ∈ S) :
    Measurable[SuperdiffusionCLT.Probability.shellSigma (d := d) S]
      (fun F : ShellSeq d => F n) := by
  have hcomap : Measurable[MeasurableSpace.comap (fun F : ShellSeq d => F n)
      (inferInstance : MeasurableSpace (ShellField d))]
      (fun F : ShellSeq d => F n) :=
    Measurable.of_comap_le le_rfl
  refine hcomap.mono ?_ le_rfl
  unfold SuperdiffusionCLT.Probability.shellSigma
  exact le_iSup₂_of_le n hn le_rfl

end SuperdiffusionCLT.Section2.Localization

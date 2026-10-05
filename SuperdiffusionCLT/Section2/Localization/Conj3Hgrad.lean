/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Localization.CutoffMinimizerClause
public import SuperdiffusionCLT.Section2.CoarseGraining.CutoffCorrespondence
public import Homogenization.Book.Ch02.Theorems.GradientUniqueness

/-!
# The gradient identity `hgrad` of the minimizers clause is unsatisfiable when the
two fields coincide

The third conjunct of the anchor keeps the pointwise identity

`hgrad`: `∇u - ∇v = p + w x` on `U`

as a named hypothesis, where `u` maximizes the response functional of the
volume-average-centered level-`L` field `â = a_L - (k_L - k_m)_U`, `v`
maximizes the response functional of the level-`m` cutoff field `a_m`, and the
comparison slope `w` solves `s_m (w x) = q - k_m(x) p` (`hw`).  Such an identity
is **not a theorem of the remaining clause data**: as soon as `m = L` it
contradicts the maximizer premises `hu`, `hv` together with the slope equation `hw`.

The hypotheses of the statement only require `n ≤ m ≤ L`, so `m = L` is admissible.  At
`m = L` the finite increment `finiteShellIncrement omega L L` is the empty sum,
the volume average of the (anti-symmetric) increment vanishes, and the two
fields collapse to the single level-`L` cutoff field
(`centeredPairField_selfCoincident`).  Then `hu` and `hv` are two maximizer
statements for the *same* functional, so the upstream a.e. gradient uniqueness
`Book.Ch02.sameGradientAE_of_isResponseMaximizer` forces `∇u = ∇v` almost
everywhere, while `hw` at `p = 0` forces `w x = ν⁻¹ q`, which is nonzero for
`q ≠ 0`.  A pointwise identity `∇u - ∇v = w` on the positive-measure set `U`
is therefore impossible.

Consequently the printed `hgrad` cannot be proved,
and at `m = L` the clause's hypothesis list is inconsistent: the printed
identity needs an additional restriction (necessarily `m < L`, or a
reformulation of the slope identity).

## Main results

* `centeredPairField_selfCoincident`: at `m = L` the volume-average-centered
  field is the level-`L` cutoff field.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section2.Localization

open Homogenization
open MeasureTheory
open scoped BigOperators

open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.CoarseGraining

noncomputable section

variable {d : ℕ}

/-! ## The two fields at `m = L` -/

/-- The volume average of the zero matrix field vanishes. -/
private theorem volumeAverageMat_zero (U : Set (Vec d)) :
    volumeAverageMat U (0 : Vec d → Mat d) = 0 := by
  ext i j
  exact volumeAverage_zero U

/-- The finite shell increment over the empty interval `(L, L]` vanishes. -/
private theorem finiteShellIncrement_self (omega : ShellSeq d) (L : ℕ) :
    finiteShellIncrement omega L L = 0 := by
  simp [finiteShellIncrement]

/-- **The volume-average-centered field collapses at `m = L`**: the finite
increment `finiteShellIncrement omega L L` is the empty sum, so its volume
average vanishes and `centeredPairField nu omega L L U` is the level-`L`
cutoff field.  This is the coincidence that refutes the printed `hgrad`. -/
theorem centeredPairField_selfCoincident (nu : ℝ) (omega : ShellSeq d) (L : ℕ)
    (U : Set (Vec d)) :
    centeredPairField nu omega L L U = (coefficientCutoff nu omega L).toCoeffField := by
  have hzero : (fun y : Vec d => finiteShellIncrement omega L L y) = 0 := by
    rw [finiteShellIncrement_self]
    rfl
  funext x
  simp only [centeredPairField]
  rw [hzero, volumeAverageMat_zero]
  simp

end

end SuperdiffusionCLT.Section2.Localization

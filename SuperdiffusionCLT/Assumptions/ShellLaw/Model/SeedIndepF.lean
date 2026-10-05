/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Assumptions.ShellLaw.Model.SeedIndepE
public import SuperdiffusionCLT.Assumptions.ShellLaw.Model.ProductLawB

/-!
# Range of dependence of the seed shell law and of the shell laws

The seed shell law has range of dependence `√d` for the pointwise-restriction sigma-algebras, and
so every scaled shell law has range `3^n √d`, which is the J1 statement for the
product law.

## Main results

* `nv_seedShell_indep_restriction`: the seed hypothesis of `nv_shellLawJ1Restriction_productLaw`
* `nv_shellLawJ1Restriction_seedProduct`: `ShellLawJ1Restriction d (nv_productLaw (nv_seedShellLaw d ε))`
-/

@[expose] public section

namespace SuperdiffusionCLT.Assumptions.ShellLaw.Model

open Homogenization MeasureTheory ProbabilityTheory
open SuperdiffusionCLT.Frozen.Assumptions

noncomputable section

variable {d : ℕ}

/-- **Independence of the seed shell law on separated sets, value sigma-algebras.** -/
theorem nv_indep_seedShell_valSigma (ε : ℝ) (U V : Set (Vec d))
    (h : ∀ ⦃x y : Vec d⦄, x ∈ U → y ∈ V → 1 ≤ Book.Ch02.vecNorm (x - y)) :
    Indep (nv_shellValSigma U) (nv_shellValSigma V) (nv_seedShellLaw d ε).toMeasure := by
  rw [nv_seedShellLaw_toMeasure]
  refine nv_indep_map _ _ _ _ measurable_assembleSkew (nv_shellValSigma_le U)
    (nv_shellValSigma_le V) ?_
  have hp := nv_indep_pi (ι := SkewIdx d) ⟨nv_scalarValSigma U, nv_scalarValSigma_le U⟩
    ⟨nv_scalarValSigma V, nv_scalarValSigma_le V⟩ (nv_seedLaw d ε)
    (nv_indep_scalarValSigma ε U V h)
  exact indep_of_indep_of_le_right
    (indep_of_indep_of_le_left hp (nv_comap_assembleSkew_valSigma_le U))
    (nv_comap_assembleSkew_valSigma_le V)

theorem nv_one_le_vecNorm_of_sqrt_le {x : Vec d} (hd : 1 ≤ d)
    (h : Real.sqrt (d : ℝ) ≤ Book.Ch02.vecNorm x) : 1 ≤ Book.Ch02.vecNorm x := by
  have : (1 : ℝ) ≤ Real.sqrt (d : ℝ) := by
    rw [Real.one_le_sqrt]; exact_mod_cast hd
  linarith only [this, h]

theorem nv_subsingleton_shellField_zero : Subsingleton (ShellField 0) :=
  ⟨fun _ _ ↦ ShellField.ext fun _ ↦ Subsingleton.elim _ _⟩

/-- **The seed shell law has range of dependence `√d`** for the pointwise-restriction
sigma-algebras: the seed hypothesis of `nv_shellLawJ1Restriction_productLaw`. -/
theorem nv_seedShell_indep_restriction (ε : ℝ) (U V : Set (Vec d)) (hU : MeasurableSet U)
    (hV : MeasurableSet V)
    (hsep : ∀ ⦃x y : Vec d⦄, x ∈ U → y ∈ V → Real.sqrt (d : ℝ) ≤ Book.Ch02.vecNorm (x - y)) :
    Indep (ShellField.shellRestrictionSigma U hU) (ShellField.shellRestrictionSigma V hV)
      (nv_seedShellLaw d ε).toMeasure := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · have := nv_subsingleton_shellField_zero
    exact nv_indep_of_subsingleton _ _ _
  · exact indep_of_indep_of_le_right
      (indep_of_indep_of_le_left
        (nv_indep_seedShell_valSigma ε U V fun x y hx hy ↦
          nv_one_le_vecNorm_of_sqrt_le hd (hsep hx hy))
        (nv_shellRestrictionSigma_le U hU))
      (nv_shellRestrictionSigma_le V hV)

/-- **J1 version 2 for the product of dilated seed shell laws.** -/
theorem nv_shellLawJ1Restriction_seedProduct (ε : ℝ) :
    ShellLawJ1Restriction d (nv_productLaw (nv_seedShellLaw d ε)) :=
  nv_shellLawJ1Restriction_productLaw _ fun U V hU hV hsep ↦
    nv_seedShell_indep_restriction ε U V hU hV hsep

/-- Witness at `d = 2`: the seed shell law has a pair of separated measurable sets (half-spaces
`{x₀ ≤ 0}` and the point `(2, 2)`), and the separation hypothesis of the theorem is satisfiable. -/
example : ∃ U V : Set (Vec 2), MeasurableSet U ∧ MeasurableSet V ∧ U.Nonempty ∧ V.Nonempty ∧
    ∀ ⦃x y : Vec 2⦄, x ∈ U → y ∈ V →
      Real.sqrt ((2 : ℕ) : ℝ) ≤ Book.Ch02.vecNorm (x - y) := by
  refine ⟨{0}, {fun _ ↦ (2 : ℝ)}, measurableSet_singleton _, measurableSet_singleton _,
    Set.singleton_nonempty _, Set.singleton_nonempty _, ?_⟩
  rintro x y rfl rfl
  unfold Book.Ch02.vecNorm
  rw [EuclideanSpace.norm_eq]
  refine Real.sqrt_le_sqrt ?_
  simp

end

end SuperdiffusionCLT.Assumptions.ShellLaw.Model

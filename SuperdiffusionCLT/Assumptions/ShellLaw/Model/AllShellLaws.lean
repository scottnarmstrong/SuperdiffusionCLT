/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Assumptions.ShellLaw.Model.J5KoopmanB
public import SuperdiffusionCLT.Assumptions.ShellLaw.Model.GaussLawB
public import SuperdiffusionCLT.Frozen.Section4.MinimalScales

/-!
# All six shell-law conditions hold for one nondegenerate law

For every dimension `d ≥ 2`, the Gaussian cell-Fourier shell law `nv_gaussLaw d` satisfies all
six shell-law conditions together: `ShellLawPrefix`, `ShellLawJ2`,
`ShellLawJ3`, `ShellLawJ1Restriction`, `ShellLawJ4` and `ShellLawJ5`, the last with constants
`0 < cStar` and `0 < K`.  The theorem `exists_law_satisfying_all_shellLaws` supplies exactly the
data over which the main theorems quantify: a probability measure `P`, the constants `cStar`
and `K`, and the proofs `hPrefix`, `hJ2`, `hJ3` that enter the type of `ShellLawJ5`.  Thus the
hypotheses of those theorems are jointly satisfiable, and the final `example` instantiates the
minimal-scales theorem with this law.

The law is not the Dirac law at zero: `exists_nondegenerate_law_satisfying_all_shellLaws`
adds the conjunct `P ≠ diracZeroLaw d`.

## Main statements

* `exists_law_satisfying_all_shellLaws`
* `exists_nondegenerate_law_satisfying_all_shellLaws`
-/

@[expose] public section

namespace SuperdiffusionCLT.Assumptions.ShellLaw.Model

open MeasureTheory
open SuperdiffusionCLT.Frozen.Assumptions

noncomputable section

variable {d : ℕ}

/-- All six shell-law conditions hold for one law, with positive constants `cStar` and `K`. -/
theorem exists_law_satisfying_all_shellLaws (hd : 2 ≤ d) :
    ∃ (P : ProbabilityMeasure (ℕ → ShellField d)) (cStar K : ℝ)
      (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P),
      0 < cStar ∧ 0 < K ∧ ShellLawJ1Restriction d P ∧ ShellLawJ4 d P ∧
        ShellLawJ5 d P cStar K hPrefix hJ2 hJ3 := by
  obtain ⟨cStar, K, h⟩ := nv_shellLawJ5_gaussLaw hd
  exact ⟨nv_gaussLaw d, cStar, K, nv_gaussLaw_prefix hd, nv_gaussLaw_J2,
    nv_gaussLaw_J3 (by omega), h.cStar_pos, h.K_pos, nv_gaussLaw_J1Restriction, nv_gaussLaw_J4, h⟩

/-- The same law, together with the fact that it is not the Dirac law at zero. -/
theorem exists_nondegenerate_law_satisfying_all_shellLaws (hd : 2 ≤ d) :
    ∃ (P : ProbabilityMeasure (ℕ → ShellField d)) (cStar K : ℝ)
      (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P),
      P ≠ diracZeroLaw d ∧ 0 < cStar ∧ 0 < K ∧ ShellLawJ1Restriction d P ∧ ShellLawJ4 d P ∧
        ShellLawJ5 d P cStar K hPrefix hJ2 hJ3 := by
  obtain ⟨cStar, K, h⟩ := nv_shellLawJ5_gaussLaw hd
  exact ⟨nv_gaussLaw d, cStar, K, nv_gaussLaw_prefix hd, nv_gaussLaw_J2,
    nv_gaussLaw_J3 (by omega), nv_gaussLaw_ne_dirac hd, h.cStar_pos, h.K_pos, nv_gaussLaw_J1Restriction,
    nv_gaussLaw_J4, h⟩

/-- Satisfiability witness: the minimal-scales theorem applies to the law above. -/
example (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    ∃ X : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ, Measurable X := by
  obtain ⟨C, -, hC⟩ := SuperdiffusionCLT.Frozen.Section4.minimal_scales d hd
  obtain ⟨P, cStar, K, hPrefix, hJ2, hJ3, -, -, h1, h4, h5⟩ :=
    exists_law_satisfying_all_shellLaws hd
  obtain ⟨X, hX, -⟩ := hC 1 cStar K one_pos le_rfl P hPrefix hJ2 hJ3 h1 h4 h5 (1 / 4) 1 1 1
    (by norm_num) (by norm_num) one_pos le_rfl one_pos le_rfl le_rfl
  exact ⟨X, hX⟩

end

end SuperdiffusionCLT.Assumptions.ShellLaw.Model

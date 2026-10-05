/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Assumptions.ShellLaw.Nonvacuity
public import SuperdiffusionCLT.Assumptions.ShellLaw.Model.LawUniquenessB
public import SuperdiffusionCLT.Assumptions.ShellLaw.Model.ShellDilationB
public import Mathlib.Probability.Independence.InfinitePi

/-!
# The product law of a seed shell law

For a probability measure `ν₀` on shell fields, `nv_productLaw ν₀` is the law on shell sequences
under which shell `n` has law `ν_n = (D_{3^n})_* ν₀` and the shells are independent. Marginals,
independence (J2), the stationarity prefix and J4 are transferred from the seed hypotheses.
-/

@[expose] public section

namespace SuperdiffusionCLT.Assumptions.ShellLaw.Model

open Homogenization MeasureTheory ProbabilityTheory
open SuperdiffusionCLT.Frozen.Assumptions

noncomputable section

variable {d : ℕ}

/-- The product measure of the shell laws `ν_n`. -/
def nv_productMeasure (ν₀ : ProbabilityMeasure (ShellField d)) : Measure (ℕ → ShellField d) :=
  Measure.infinitePi fun n ↦ (scaledShellLaw ν₀ n).toMeasure

instance nv_productMeasure_isProbability (ν₀ : ProbabilityMeasure (ShellField d)) :
    IsProbabilityMeasure (nv_productMeasure ν₀) := by
  unfold nv_productMeasure
  infer_instance

/-- The product law: independent shells with laws `(D_{3^n})_* ν₀`. -/
def nv_productLaw (ν₀ : ProbabilityMeasure (ShellField d)) :
    ProbabilityMeasure (ℕ → ShellField d) :=
  ⟨nv_productMeasure ν₀, nv_productMeasure_isProbability ν₀⟩

@[simp]
theorem nv_productLaw_toMeasure (ν₀ : ProbabilityMeasure (ShellField d)) :
    (nv_productLaw ν₀).toMeasure = Measure.infinitePi fun n ↦ (scaledShellLaw ν₀ n).toMeasure :=
  rfl

/-- The `n`-th coordinate of the product law has law `scaledShellLaw ν₀ n`. -/
theorem nv_shellMarginalLaw_productLaw (ν₀ : ProbabilityMeasure (ShellField d)) (n : ℕ) :
    ShellField.shellMarginalLaw (nv_productLaw ν₀) n = scaledShellLaw ν₀ n := by
  apply ProbabilityMeasure.toMeasure_injective
  show Measure.map (fun F : ℕ → ShellField d ↦ F n) (nv_productLaw ν₀).toMeasure = _
  rw [nv_productLaw_toMeasure]
  exact Measure.infinitePi_map_eval _ n

theorem nv_shellMarginalLaw_productLaw_toMeasure (ν₀ : ProbabilityMeasure (ShellField d))
    (n : ℕ) :
    (ShellField.shellMarginalLaw (nv_productLaw ν₀) n).toMeasure =
      Measure.map (dilate (nv_scaleUnit n)) ν₀.toMeasure := by
  rw [nv_shellMarginalLaw_productLaw, scaledShellLaw_toMeasure]

/-- Independence of the shells (J2) holds for every seed. -/
theorem nv_shellLawJ2_productLaw (ν₀ : ProbabilityMeasure (ShellField d)) :
    ShellLawJ2 d (nv_productLaw ν₀) where
  independent := by
    rw [nv_productLaw_toMeasure]
    exact iIndepFun_infinitePi (P := fun n ↦ (scaledShellLaw ν₀ n).toMeasure)
      (X := fun _ ↦ (id : ShellField d → ShellField d)) (fun _ ↦ measurable_id)

/-- Prefix for the product law: stationarity of the seed under all translations. -/
theorem nv_shellLawPrefix_productLaw (hd : 2 ≤ d) (ν₀ : ProbabilityMeasure (ShellField d))
    (hν : ∀ z : Vec d, Measure.map (ShellField.translate z) ν₀.toMeasure = ν₀.toMeasure) :
    ShellLawPrefix d (nv_productLaw ν₀) where
  dimension := hd
  stationary n z := by
    rw [nv_shellMarginalLaw_productLaw]
    exact map_translate_scaledShellLaw ν₀ hν n z

/-- Seed negation invariance gives the whole-sequence negation invariance. -/
theorem nv_productLaw_map_negate (ν₀ : ProbabilityMeasure (ShellField d))
    (hν : Measure.map ShellField.negate ν₀.toMeasure = ν₀.toMeasure) :
    (nv_productLaw ν₀).map ShellField.negateSequence = nv_productLaw ν₀ := by
  apply ProbabilityMeasure.toMeasure_injective
  rw [ProbabilityMeasure.toMeasure_map, nv_productLaw_toMeasure]
  have h := Measure.infinitePi_map_pi
    (μ := fun n ↦ (scaledShellLaw ν₀ n).toMeasure)
    (f := fun _ ↦ (ShellField.negate : ShellField d → ShellField d))
    (fun _ ↦ ShellField.measurable_negate)
  refine h.trans ?_
  congr 1
  funext n
  exact map_negate_scaledShellLaw ν₀ hν n

/-- Seed signed-permutation invariance gives the whole-sequence invariance. -/
theorem nv_productLaw_map_rotate (ν₀ : ProbabilityMeasure (ShellField d))
    (R : Mat d) (hR : IsSignedPermutationMatrix R)
    (hν : Measure.map (ShellField.rotate R hR) ν₀.toMeasure = ν₀.toMeasure) :
    (nv_productLaw ν₀).map (ShellField.rotateSequence R hR) = nv_productLaw ν₀ := by
  apply ProbabilityMeasure.toMeasure_injective
  rw [ProbabilityMeasure.toMeasure_map, nv_productLaw_toMeasure]
  have h := Measure.infinitePi_map_pi
    (μ := fun n ↦ (scaledShellLaw ν₀ n).toMeasure)
    (f := fun _ ↦ (ShellField.rotate R hR : ShellField d → ShellField d))
    (fun _ ↦ ShellField.measurable_rotate R hR)
  refine h.trans ?_
  congr 1
  funext n
  exact map_rotate_scaledShellLaw ν₀ R hR hν n

/-- J4 for the product law from the seed invariances. -/
theorem nv_shellLawJ4_productLaw (ν₀ : ProbabilityMeasure (ShellField d))
    (hrot : ∀ (R : Mat d) (hR : IsSignedPermutationMatrix R),
      Measure.map (ShellField.rotate R hR) ν₀.toMeasure = ν₀.toMeasure)
    (hneg : Measure.map ShellField.negate ν₀.toMeasure = ν₀.toMeasure) :
    ShellLawJ4 d (nv_productLaw ν₀) where
  hyperoctahedral R hR := nv_productLaw_map_rotate ν₀ R hR (hrot R hR)
  negation := nv_productLaw_map_negate ν₀ hneg

end

end SuperdiffusionCLT.Assumptions.ShellLaw.Model

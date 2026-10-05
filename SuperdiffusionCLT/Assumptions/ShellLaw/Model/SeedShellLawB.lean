/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Assumptions.ShellLaw.Model.SeedShellLaw

/-!
# Translation and negation invariance of the seed shell law

An invariance of the seed shell law follows from a commutation `T (assembleSkew φ) =
assembleSkew (Φ φ)` with a measure-preserving `Φ` of the product of scalar seeds.
-/

@[expose] public section

namespace SuperdiffusionCLT.Assumptions.ShellLaw.Model

open Homogenization MeasureTheory ProbabilityTheory
open SuperdiffusionCLT.Frozen.Assumptions

noncomputable section

variable {d : ℕ}

/-- Reduction of an invariance of the seed shell law to the product of scalar seeds. -/
theorem nv_seedShellLaw_map_of_comm (ε : ℝ) (T : ShellField d → ShellField d)
    (hT : Measurable T) (Φ : (SkewIdx d → ScalarC2Field d) → (SkewIdx d → ScalarC2Field d))
    (hΦ : Measurable Φ)
    (hc : ∀ φ, T (assembleSkew φ) = assembleSkew (Φ φ))
    (hinv : (nv_seedProduct d ε).map Φ = nv_seedProduct d ε) :
    Measure.map T (nv_seedShellLaw d ε).toMeasure = (nv_seedShellLaw d ε).toMeasure := by
  rw [nv_seedShellLaw_map_eq d ε T hT]
  have h : (fun φ ↦ T (assembleSkew φ)) = assembleSkew ∘ Φ := funext hc
  rw [h, ← Measure.map_map measurable_assembleSkew hΦ, hinv]
  rfl

/-- Coordinatewise invariant maps preserve the product of scalar seeds. -/
theorem nv_seedProduct_map_coord (ε : ℝ) (g : SkewIdx d → ScalarC2Field d → ScalarC2Field d)
    (hg : ∀ p, Measurable (g p)) (hinv : ∀ p, (nv_seedLaw d ε).map (g p) = nv_seedLaw d ε) :
    (nv_seedProduct d ε).map (fun φ p ↦ g p (φ p)) = nv_seedProduct d ε := by
  unfold nv_seedProduct
  rw [Measure.pi_map_pi (fun p ↦ (hg p).aemeasurable)]
  congr 1
  funext p
  exact hinv p

/-- Translation commutes with the assembly, entrywise. -/
theorem translate_assembleSkew (z : Vec d) (φ : SkewIdx d → ScalarC2Field d) :
    ShellField.translate z (assembleSkew φ) =
      assembleSkew (fun p ↦ ScalarC2Field.nv_translate z (φ p)) := by
  ext x a b
  rw [ShellField.translate_apply, assembleSkew_apply, assembleSkew_apply]
  rfl

/-- **Translation invariance** of the seed shell law. -/
theorem nv_seedShellLaw_map_translate (d : ℕ) (ε : ℝ) (z : Vec d) :
    Measure.map (ShellField.translate z) (nv_seedShellLaw d ε).toMeasure =
      (nv_seedShellLaw d ε).toMeasure :=
  nv_seedShellLaw_map_of_comm ε _ (ShellField.measurable_translate z)
    (fun φ p ↦ ScalarC2Field.nv_translate z (φ p))
    (Measurable.of_eval fun p ↦
      (ScalarC2Field.measurable_nv_translate z).comp (measurable_pi_apply p))
    (translate_assembleSkew z)
    (nv_seedProduct_map_coord ε (fun _ ↦ ScalarC2Field.nv_translate z)
      (fun _ ↦ ScalarC2Field.measurable_nv_translate z) (fun _ ↦ nv_seedLaw_map_translate ε z))

/-- **Negation invariance** of the seed shell law. -/
theorem nv_seedShellLaw_map_negate (d : ℕ) (ε : ℝ) :
    Measure.map ShellField.negate (nv_seedShellLaw d ε).toMeasure =
      (nv_seedShellLaw d ε).toMeasure :=
  nv_seedShellLaw_map_of_comm ε _ ShellField.measurable_negate
    (fun φ p ↦ ScalarC2Field.smulConst (-1) (φ p))
    (Measurable.of_eval fun p ↦
      (ScalarC2Field.measurable_smulConst (-1)).comp (measurable_pi_apply p))
    negate_assembleSkew
    (nv_seedProduct_map_coord ε (fun _ ↦ ScalarC2Field.smulConst (-1))
      (fun _ ↦ ScalarC2Field.measurable_smulConst (-1)) (fun _ ↦ nv_seedLaw_map_neg ε))

/-! ## Satisfiability witnesses -/

example : Measure.map (ShellField.translate (Pi.single 0 1 : Vec 2))
    (nv_seedShellLaw 2 1).toMeasure = (nv_seedShellLaw 2 1).toMeasure :=
  nv_seedShellLaw_map_translate 2 1 _

example : Measure.map ShellField.negate (nv_seedShellLaw 2 1).toMeasure =
    (nv_seedShellLaw 2 1).toMeasure :=
  nv_seedShellLaw_map_negate 2 1

end

end SuperdiffusionCLT.Assumptions.ShellLaw.Model

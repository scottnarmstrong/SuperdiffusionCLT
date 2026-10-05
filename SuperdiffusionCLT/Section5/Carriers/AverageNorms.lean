/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.ResponseFields.Norms
public import Mathlib.Analysis.Calculus.FDeriv.Equiv

/-!
# Average `L^p` norms of gradients on cubes

`avgPowENorm Q p g` is `⨍_Q |g|^p` and `avgRootENorm Q p g` is its `p`-th root, both in
`ℝ≥0∞`, built on the normalized cube measure. `avgRootENorm_eq_cubeLpENorm` identifies the
root with `Section2.Norms.cubeLpENorm`. For gradients, the magnitude `|∇u|` is the Euclidean
one (via `vecCubeLpENorm`).

## Main results

* `avgRootENorm_eq_cubeLpENorm`, `avgPowENorm_eq_rootENorm_rpow`: consistency.
* `cubeLpENorm_mono_exponent`, `vecCubeLpENorm_mono_exponent`, `gradLpENorm_mono_exponent`:
  monotonicity in `p` on cubes (the normalized measure is a probability measure).
-/

@[expose] public section

namespace SuperdiffusionCLT
namespace Section5

open Homogenization
open MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

instance isProbabilityMeasure_normalizedCubeMeasure (Q : TriadicCube d) :
    IsProbabilityMeasure (normalizedCubeMeasure Q) :=
  ⟨normalizedCubeMeasure_apply_univ Q⟩

/-- `⨍_Q |g|^p`. -/
def avgPowENorm {E : Type*} [NormedAddCommGroup E] (Q : TriadicCube d) (p : ℝ)
    (g : Vec d → E) : ℝ≥0∞ :=
  ∫⁻ x, ‖g x‖ₑ ^ p ∂(normalizedCubeMeasure Q)

/-- `(⨍_Q |g|^p)^{1/p}`. -/
def avgRootENorm {E : Type*} [NormedAddCommGroup E] (Q : TriadicCube d) (p : ℝ)
    (g : Vec d → E) : ℝ≥0∞ :=
  avgPowENorm Q p g ^ (1 / p)

theorem avgRootENorm_eq_cubeLpENorm {E : Type*} [NormedAddCommGroup E] (Q : TriadicCube d)
    {p : ℝ} (hp : 0 < p) {g : Vec d → E}
    (hg : AEStronglyMeasurable g (normalizedCubeMeasure Q)) :
    avgRootENorm Q p g = Section2.Norms.cubeLpENorm Q (ENNReal.ofReal p) g := by
  rw [Section2.Norms.cubeLpENorm, eLpNorm_eq_lintegral_rpow_enorm_toReal
    (by simpa using hp) ENNReal.ofReal_ne_top hg, ENNReal.toReal_ofReal hp.le]
  rfl

theorem avgPowENorm_eq_rootENorm_rpow {E : Type*} [NormedAddCommGroup E] (Q : TriadicCube d)
    {p : ℝ} (hp : 0 < p) (g : Vec d → E) :
    avgPowENorm Q p g = avgRootENorm Q p g ^ p := by
  rw [avgRootENorm, ← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hp.ne', ENNReal.rpow_one]

theorem avgRootENorm_mono_exponent {E : Type*} [NormedAddCommGroup E] (Q : TriadicCube d)
    {p q : ℝ} (hp : 0 < p) (hpq : p ≤ q) {g : Vec d → E}
    (hg : AEStronglyMeasurable g (normalizedCubeMeasure Q)) :
    avgRootENorm Q p g ≤ avgRootENorm Q q g := by
  rw [avgRootENorm_eq_cubeLpENorm Q hp hg, avgRootENorm_eq_cubeLpENorm Q (hp.trans_le hpq) hg]
  exact eLpNorm_le_eLpNorm_of_exponent_le (ENNReal.ofReal_le_ofReal hpq)

/-- `L̲^p ≤ L̲^q` on a cube for `p ≤ q`. -/
theorem cubeLpENorm_mono_exponent {E : Type*} [NormedAddCommGroup E] (Q : TriadicCube d)
    {p q : ℝ≥0∞} (hpq : p ≤ q) (g : Vec d → E) :
    Section2.Norms.cubeLpENorm Q p g ≤ Section2.Norms.cubeLpENorm Q q g :=
  eLpNorm_le_eLpNorm_of_exponent_le hpq

theorem vecCubeLpENorm_mono_exponent (Q : TriadicCube d) {p q : ℝ≥0∞} (hpq : p ≤ q)
    (F : Vec d → Vec d) :
    Section3.ResponseFields.vecCubeLpENorm Q p F ≤
      Section3.ResponseFields.vecCubeLpENorm Q q F :=
  cubeLpENorm_mono_exponent Q hpq _

/-- The Euclidean gradient field `∇u`. -/
def gradField (u : Vec d → ℝ) : Vec d → Vec d :=
  fun x i => fderiv ℝ u x (basisVec i)

/-- `‖∇u‖_{L̲^p(Q)} = (⨍_Q |∇u|^p)^{1/p}`. -/
def gradLpENorm (Q : TriadicCube d) (p : ℝ≥0∞) (u : Vec d → ℝ) : ℝ≥0∞ :=
  Section3.ResponseFields.vecCubeLpENorm Q p (gradField u)

theorem gradLpENorm_mono_exponent (Q : TriadicCube d) {p q : ℝ≥0∞} (hpq : p ≤ q)
    (u : Vec d → ℝ) : gradLpENorm Q p u ≤ gradLpENorm Q q u :=
  vecCubeLpENorm_mono_exponent Q hpq _

/-! ### Scaling -/

/-! ### Witnesses -/

example : avgRootENorm (TriadicCube.mk (0 : ℤ) (0 : Fin 2 → ℤ)) 2 (fun _ : Vec 2 => (0 : ℝ)) =
    Section2.Norms.cubeLpENorm (TriadicCube.mk (0 : ℤ) (0 : Fin 2 → ℤ)) (ENNReal.ofReal 2)
      (fun _ : Vec 2 => (0 : ℝ)) :=
  avgRootENorm_eq_cubeLpENorm _ (by norm_num) aestronglyMeasurable_const

example : avgRootENorm (TriadicCube.mk (0 : ℤ) (0 : Fin 2 → ℤ)) 2 (fun _ : Vec 2 => (1 : ℝ)) ≤
    avgRootENorm (TriadicCube.mk (0 : ℤ) (0 : Fin 2 → ℤ)) 3 (fun _ : Vec 2 => (1 : ℝ)) :=
  avgRootENorm_mono_exponent _ (by norm_num) (by norm_num) aestronglyMeasurable_const

example : gradLpENorm (TriadicCube.mk (0 : ℤ) (0 : Fin 2 → ℤ)) 2 (fun x : Vec 2 => x 0) ≤
    gradLpENorm (TriadicCube.mk (0 : ℤ) (0 : Fin 2 → ℤ)) 3 (fun x : Vec 2 => x 0) :=
  gradLpENorm_mono_exponent _ (by norm_num) _

end

end Section5
end SuperdiffusionCLT

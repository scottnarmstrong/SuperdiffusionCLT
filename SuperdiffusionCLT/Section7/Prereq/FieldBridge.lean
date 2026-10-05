/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.Change.SkewShift
public import SuperdiffusionCLT.Section7.MinimalScale.Translate
public import SuperdiffusionCLT.Section6.Engine.Carriers
public import SuperdiffusionCLT.Assumptions.ShellLaw.Nonvacuity

/-!
# Field bridges on translated cubes and harmonic functions as weak solutions

* Almost surely, a weak solution with data for the centered field of the translated sample
  `translateSequence y ω` is the same as one for its recentered field
  (`w0_ae_isWeakSolutionOn_centered_iff_recentered_translate`); the centered field of the
  translated sample is the centered field of `ω` on the translated set, seen from `x + y`
  (`w0_centeredField_translateSequence`).
* `AHarmonicFunction a U` is exactly `IsWeakSolutionOn a U u 0 0`
  (`w0_isAHarmonicGradient_iff_isWeakSolutionOn`, `w0_exists_aHarmonicFunction_iff`), on cubes
  `U = openCubeSet Q`, and for the engine carrier `Section6.IsSolOn`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section7

open MeasureTheory Homogenization
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Carriers

variable {d : ℕ}

/-- **Centered versus recentered field, translated sample.** For every `y`, almost surely, for
every `m` and every open set `U` of finite measure, a weak solution with any data for
`ν Id + centeredStreamField (τ_y ω) □_m` is the same as one for the recentered field of `τ_y ω`
(for `H¹` functions with square-integrable recentered flux). -/
theorem w0_ae_isWeakSolutionOn_centered_iff_recentered_translate
    {P : ProbabilityMeasure (ShellSeq d)} (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P)
    (hJ3 : ShellLawJ3 d P) (nu : ℝ) (y : Vec d) :
    ∀ᵐ omega : ShellSeq d ∂P.toMeasure, ∀ m : ℕ, ∀ {U : Set (Vec d)},
      IsOpen U → IsFiniteMeasure (volumeMeasureOn U) → ∀ (u : H1Function U) (f : Vec d → ℝ)
        (g : Vec d → Vec d),
      MemVectorL2 U (fun x => matVecMul
        (Section6.fullCoefficientRecentered nu (ShellField.translateSequence y omega) x)
          (u.grad x)) →
      (IsWeakSolutionOn (fun x => nu • (1 : Mat d) +
          centeredStreamField (ShellField.translateSequence y omega)
            (cubeSet (originCube d (m : ℤ))) x) U u f g ↔
        IsWeakSolutionOn
          (Section6.fullCoefficientRecentered nu (ShellField.translateSequence y omega))
          U u f g) :=
  (translateSequence_measurePreserving hPrefix hJ2 y).quasiMeasurePreserving.ae
    (ae_isWeakSolutionOn_centered_iff_recentered hJ3 nu)

/-- The centered field of the translated sample is the centered field of `ω` on the translated
set, seen from `x + y`. -/
theorem w0_centeredField_translateSequence (nu : ℝ) (y : Vec d) (omega : ShellSeq d)
    (U : Set (Vec d)) :
    (fun x => nu • (1 : Mat d) +
        centeredStreamField (ShellField.translateSequence y omega) U x) =
      fun x => nu • (1 : Mat d) + centeredStreamField omega (translateSet y U) (x + y) := by
  funext x
  rw [centeredStreamField_translateSequence]

/-- The translated bridge, with the centered field written on the translated cube `y + □_m`. -/
theorem w0_ae_isWeakSolutionOn_translateSet_iff_recentered
    {P : ProbabilityMeasure (ShellSeq d)} (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P)
    (hJ3 : ShellLawJ3 d P) (nu : ℝ) (y : Vec d) :
    ∀ᵐ omega : ShellSeq d ∂P.toMeasure, ∀ m : ℕ, ∀ {U : Set (Vec d)},
      IsOpen U → IsFiniteMeasure (volumeMeasureOn U) → ∀ (u : H1Function U) (f : Vec d → ℝ)
        (g : Vec d → Vec d),
      MemVectorL2 U (fun x => matVecMul
        (Section6.fullCoefficientRecentered nu (ShellField.translateSequence y omega) x)
          (u.grad x)) →
      (IsWeakSolutionOn (fun x => nu • (1 : Mat d) +
          centeredStreamField omega (translateSet y (cubeSet (originCube d (m : ℤ)))) (x + y))
          U u f g ↔
        IsWeakSolutionOn
          (Section6.fullCoefficientRecentered nu (ShellField.translateSequence y omega))
          U u f g) := by
  filter_upwards [w0_ae_isWeakSolutionOn_centered_iff_recentered_translate hPrefix hJ2 hJ3 nu y]
    with omega h m U hU hfin u f g hflux
  rw [← w0_centeredField_translateSequence nu y omega]
  exact h m hU hfin u f g hflux

/-! ### Harmonic functions as weak solutions with zero data -/

/-- An `H¹` function is `a`-harmonic exactly when it is a weak solution with zero data. -/
theorem w0_isAHarmonicGradient_iff_isWeakSolutionOn (a : CoeffField d) (U : Set (Vec d))
    (u : H1Function U) :
    IsAHarmonicGradient a U u.grad ↔ IsWeakSolutionOn a U u (fun _ => 0) (fun _ => 0) := by
  have hzero : ∀ φ : H10Function U,
      ((∫ x in U, (fun _ : Vec d => (0 : ℝ)) x * φ.toH1Function.toFun x) +
        ∫ x in U, vecDot ((fun _ : Vec d => (0 : Vec d)) x) (φ.toH1Function.grad x)) = 0 := by
    intro φ
    simp only [zero_mul, vecDot_zero_left, integral_zero, add_zero]
  constructor
  · rintro ⟨-, hsol⟩ φ
    rw [hzero φ]
    exact hsol φ
  · intro h
    refine ⟨u.isPotentialOn, fun φ => ?_⟩
    have := h φ
    rw [hzero φ] at this
    exact this

/-- `AHarmonicFunction a U` is the same as an `H¹` weak solution with zero data. -/
theorem w0_exists_aHarmonicFunction_iff (a : CoeffField d) (U : Set (Vec d)) (u : H1Function U) :
    (∃ v : AHarmonicFunction a U, v.toH1 = u) ↔
      IsWeakSolutionOn a U u (fun _ => 0) (fun _ => 0) := by
  constructor
  · rintro ⟨v, rfl⟩
    exact (w0_isAHarmonicGradient_iff_isWeakSolutionOn a U v.toH1).1 v.isHarmonic
  · intro h
    exact ⟨⟨u, (w0_isAHarmonicGradient_iff_isWeakSolutionOn a U u).2 h⟩, rfl⟩

/-- On an open cube: `AHarmonicFunction a (openCubeSet Q)` is `IsWeakSolutionOn` with zero data. -/
theorem w0_aHarmonic_cube_iff (a : CoeffField d) (Q : TriadicCube d)
    (u : H1Function (openCubeSet Q)) :
    (∃ v : AHarmonicFunction a (openCubeSet Q), v.toH1 = u) ↔
      IsWeakSolutionOn a (openCubeSet Q) u (fun _ => 0) (fun _ => 0) :=
  w0_exists_aHarmonicFunction_iff a (openCubeSet Q) u

/-- The engine carrier `Section6.IsSolOn` is an almost everywhere representative of an `H¹` weak
solution with zero data. -/
theorem w0_isSolOn_iff (a : CoeffField d) (U : Set (Vec d)) (u : Vec d → ℝ) (g : Vec d → Vec d) :
    Section6.IsSolOn a U u g ↔
      ∃ v : H1Function U, IsWeakSolutionOn a U v (fun _ => 0) (fun _ => 0) ∧
        v.toFun =ᵐ[volume.restrict U] u ∧ v.grad =ᵐ[volume.restrict U] g := by
  constructor
  · rintro ⟨v, h1, h2⟩
    exact ⟨v.toH1, (w0_exists_aHarmonicFunction_iff a U v.toH1).1 ⟨v, rfl⟩, h1, h2⟩
  · rintro ⟨v, hv, h1, h2⟩
    obtain ⟨w, rfl⟩ := (w0_exists_aHarmonicFunction_iff a U v).2 hv
    exact ⟨w, h1, h2⟩

/-! ### Witnesses -/

/-- The Dirac zero law meets the hypotheses of the translated bridge. -/
example {nu : ℝ} (hd : 2 ≤ d) (y : Vec d) :
    ∀ᵐ omega : ShellSeq d ∂(SuperdiffusionCLT.Assumptions.ShellLaw.diracZeroLaw d).toMeasure,
      ∀ m : ℕ, ∀ {U : Set (Vec d)}, IsOpen U → IsFiniteMeasure (volumeMeasureOn U) →
        ∀ (u : H1Function U) (f : Vec d → ℝ) (g : Vec d → Vec d),
        MemVectorL2 U (fun x => matVecMul
          (Section6.fullCoefficientRecentered nu (ShellField.translateSequence y omega) x)
            (u.grad x)) →
        (IsWeakSolutionOn (fun x => nu • (1 : Mat d) +
            centeredStreamField (ShellField.translateSequence y omega)
              (cubeSet (originCube d (m : ℤ))) x) U u f g ↔
          IsWeakSolutionOn
            (Section6.fullCoefficientRecentered nu (ShellField.translateSequence y omega))
            U u f g) :=
  w0_ae_isWeakSolutionOn_centered_iff_recentered_translate
    (SuperdiffusionCLT.Assumptions.ShellLaw.shellLawPrefix_diracZeroLaw hd)
    SuperdiffusionCLT.Assumptions.ShellLaw.shellLawJ2_diracZeroLaw
    SuperdiffusionCLT.Assumptions.ShellLaw.shellLawJ3_diracZeroLaw nu y

/-- The zero function is `a`-harmonic on every cube, and a weak solution with zero data. -/
example (a : CoeffField d) (Q : TriadicCube d) :
    ∃ v : AHarmonicFunction a (openCubeSet Q), v.toH1 = 0 :=
  (w0_aHarmonic_cube_iff a Q 0).2 (fun φ => by simp [matVecMul_zero, vecDot_zero_left])

end SuperdiffusionCLT.Section7

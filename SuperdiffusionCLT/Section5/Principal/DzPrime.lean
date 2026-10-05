/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section5.Principal.FreshMeasurable
public import SuperdiffusionCLT.Section5.Principal.FiniteToInfiniteC

/-!
# `D'` in place of `D_z`

`localizationDz` is a supremum, with no measurability lemma. The bound `principal_Dz_le` gives
`D_z ≤ D' := αg + (αg)²` with `α = ν⁻¹ d √d 3^n` and `g` the derivative gauge of the translated
shell sequence, which is ambient-measurable and, because it reads only the shells `(m - h, m]`,
fresh-measurable. This file defines `D'`, proves its measurability, `D_z ≤ D'`, and (with
`DzPrimeB.lean`) the fourth moment of `D'` by the argument of `principal_Dz_moment`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section5

open MeasureTheory Homogenization
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Estimates.Stream
open SuperdiffusionCLT.Probability (shellSigma)

variable {d : ℕ}

/-- The constant `α = ν⁻¹ (d √d) 3^n` of `principal_Dz_le`. -/
noncomputable def dzpAlpha (d : ℕ) (nu : ℝ) (n : ℕ) : ℝ :=
  nu⁻¹ * ((d : ℝ) * Real.sqrt d) * (3 : ℝ) ^ n

theorem dzpAlpha_nonneg (d : ℕ) {nu : ℝ} (hnu : 0 < nu) (n : ℕ) : 0 ≤ dzpAlpha d nu n := by
  unfold dzpAlpha
  positivity

/-- The derivative gauge `g` of the shell sequence translated to the cube `R`. -/
noncomputable def dzpGauge (m h : ℕ) (R : TriadicCube d) (ω : ShellSeq d) : ℝ :=
  finiteShellDerivGauge (m - h) m (ShellField.translateSequence (cubeCenter R) ω)

theorem dzpGauge_nonneg (m h : ℕ) (R : TriadicCube d) (ω : ShellSeq d) :
    0 ≤ dzpGauge m h R ω :=
  finiteShellDerivGauge_nonneg _ _ _

/-- `D' = αg + (αg)²`, the measurable upper bound of `D_z`. -/
noncomputable def dzPrime (nu : ℝ) (n m h : ℕ) (R : TriadicCube d) (ω : ShellSeq d) : ℝ :=
  dzpAlpha d nu n * dzpGauge m h R ω + (dzpAlpha d nu n * dzpGauge m h R ω) ^ 2

theorem dzPrime_nonneg {nu : ℝ} (hnu : 0 < nu) (n m h : ℕ) (R : TriadicCube d)
    (ω : ShellSeq d) : 0 ≤ dzPrime nu n m h R ω := by
  have hx : 0 ≤ dzpAlpha d nu n * dzpGauge m h R ω :=
    mul_nonneg (dzpAlpha_nonneg d hnu n) (dzpGauge_nonneg m h R ω)
  unfold dzPrime
  positivity

/-- **`D_z ≤ D'`** for a cube `R = z + cu_n` of scale `n ≤ m - h`. -/
theorem principalDz_le_dzPrime {nu : ℝ} (hnu : 0 < nu) {n m h : ℕ} (hn : n ≤ m - h)
    (R : TriadicCube d) (hR : R.scale = (n : ℤ)) (ω : ShellSeq d) :
    principalDz nu m h R ω ≤ dzPrime nu n m h R ω := by
  refine le_trans (principal_Dz_le hnu hn R hR ω) (le_of_eq ?_)
  unfold dzPrime dzpAlpha dzpGauge
  rw [show (3 : ℝ) ^ (2 * n) = ((3 : ℝ) ^ n) ^ 2 by rw [pow_mul']]
  ring

/-! ## Measurability -/

theorem measurable_dzpGauge (m h : ℕ) (R : TriadicCube d) :
    Measurable (fun ω : ShellSeq d => dzpGauge m h R ω) :=
  measurable_finiteShellDerivGauge_translate (cubeCenter R) (m - h) m

theorem dzpGauge_congr {m h : ℕ} (R : TriadicCube d) {ω ω' : ShellSeq d}
    (hh : ∀ k ∈ Set.Ioc (m - h) m, ω k = ω' k) : dzpGauge m h R ω = dzpGauge m h R ω' := by
  unfold dzpGauge finiteShellDerivGauge
  refine Finset.sum_congr rfl fun k hk => ?_
  have := hh k (by simpa only [Set.mem_Ioc, Finset.mem_Ioc] using hk)
  simp only [ShellField.translateSequence_apply, this]

/-- `g` reads only the fresh shells `(m - h, m]`. -/
theorem measurable_dzpGauge_fresh (m h : ℕ) (R : TriadicCube d) :
    Measurable[shellSigma (d := d) (Set.Ioc (m - h) m)]
      (fun ω : ShellSeq d => dzpGauge m h R ω) :=
  pmeas_measurable_of_depends (measurable_dzpGauge m h R) (fun _ _ hh => dzpGauge_congr R hh)

theorem measurable_dzPrime (nu : ℝ) (n m h : ℕ) (R : TriadicCube d) :
    Measurable (fun ω : ShellSeq d => dzPrime nu n m h R ω) := by
  have hg := measurable_dzpGauge m h R
  exact (measurable_const.mul hg).add ((measurable_const.mul hg).pow_const 2)

/-- **`D'` is measurable for the fresh-shell `σ`-algebra** `σ(j_r : m - h < r ≤ m)`. -/
theorem measurable_dzPrime_fresh (nu : ℝ) (n m h : ℕ) (R : TriadicCube d) :
    Measurable[shellSigma (d := d) (Set.Ioc (m - h) m)]
      (fun ω : ShellSeq d => dzPrime nu n m h R ω) := by
  have hg := measurable_dzpGauge_fresh m h R
  exact (measurable_const.mul hg).add ((measurable_const.mul hg).pow_const 2)

/-! ## Satisfiability -/

/-- Witness: for `d = 2`, `ν = 1`, `n = 0`, the unit cube, `m = 5`, `h = 2` (so `n ≤ m - h`), the
bound `D_z ≤ D'` holds at every sample and `D'` is fresh-measurable. -/
example (ω : ShellSeq 2) : principalDz (1 : ℝ) 5 2 (originCube 2 (0 : ℤ)) ω ≤
      dzPrime (1 : ℝ) 0 5 2 (originCube 2 (0 : ℤ)) ω ∧
    Measurable[shellSigma (d := 2) (Set.Ioc (5 - 2) 5)]
      (fun ω : ShellSeq 2 => dzPrime (1 : ℝ) 0 5 2 (originCube 2 (0 : ℤ)) ω) :=
  ⟨principalDz_le_dzPrime one_pos (by norm_num) _ (by simp [originCube]) _,
    measurable_dzPrime_fresh _ _ _ _ _⟩

end SuperdiffusionCLT.Section5

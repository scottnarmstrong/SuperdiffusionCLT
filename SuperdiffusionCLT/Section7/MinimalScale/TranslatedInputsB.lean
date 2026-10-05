/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.MinimalScale.Translate
public import SuperdiffusionCLT.Section7.MinimalScale.GridMaxScale
public import SuperdiffusionCLT.Assumptions.ShellLaw.Nonvacuity

/-!
# Grid maxima of translated scales: bookkeeping

For a family `y ↦ X₀ ∘ τ_y` all carrying the `Γ_σ` bound of a single scale `X₀`, one measurable
scale `Xs` (from `exists_gridMax_scale` at `N + 1`) with `log Xs = O_{Γ_σ}(Θ)` satisfies, almost
surely and for every `s ≥ Θ`: `Xs ≤ 3^{n_{s+b}(N+1)}` implies `X₀ ∘ τ_y ≤ 3^{n_s(N)}` at every point
`y` of the grid `3^{n_s(N) - 3} ℤ^d ∩ {|y|_∞ ≤ 3^{s+b}}`.  Here `n_s(N) = s - ⌈N log s⌉₊`.

The grid of `exists_gridMax_scale` at level `K = s + b` and exponent `N + 1` is finer than this
grid, with a smaller threshold exponent: `n_{s+b}(N+1) ≤ n_s(N)` once `exp b ≤ s`.  This is why
the hypothesis on `Xs` is the one at `N + 1`, `s + b` (the exponents cannot all coincide).

## Main results

* `b2_nK_succ_le`, `b2_gridPts_mono`: the comparison of the two grids.
* `b2_latticePts`, `b2_ae_forall_lattice`: almost-sure statements for every point of the countable
  lattice `⋃_j 3^j ℤ^d`.
* `b2_gridMax_scale`: the scale, with `Xs ≥ 1` and the threshold `Θ ≥ exp b`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section7

open MeasureTheory Homogenization
open SuperdiffusionCLT.Frozen.Assumptions

noncomputable section

/-- The points `3^j k`, `j ∈ ℤ`, `k ∈ ℤ^d`: a countable set containing every grid. -/
def b2_latticePts (d : ℕ) : Set (Vec d) :=
  {y | ∃ (j : ℤ) (k : Fin d → ℤ), y = fun i => (3 : ℝ) ^ j * (k i : ℝ)}

theorem b2_latticePts_countable (d : ℕ) : (b2_latticePts d).Countable := by
  have h : b2_latticePts d =
      Set.range (fun p : ℤ × (Fin d → ℤ) => fun i => (3 : ℝ) ^ p.1 * (p.2 i : ℝ)) := by
    ext y
    constructor
    · rintro ⟨j, k, rfl⟩
      exact ⟨(j, k), rfl⟩
    · rintro ⟨⟨j, k⟩, rfl⟩
      exact ⟨j, k, rfl⟩
  rw [h]
  exact Set.countable_range _

theorem b2_gridPts_subset_lattice {d : ℕ} {j : ℤ} {R : ℝ} (hR : 0 ≤ R) :
    ((gridPts d j R : Finset (Vec d)) : Set (Vec d)) ⊆ b2_latticePts d := by
  intro y hy
  obtain ⟨k, hk, -⟩ := (mem_gridPts hR y).1 hy
  exact ⟨j, k, funext hk⟩

/-- A statement holding almost surely for each lattice point holds almost surely for all of them. -/
theorem b2_ae_forall_lattice {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} (d : ℕ)
    {Q : Vec d → Ω → Prop} (h : ∀ y, ∀ᵐ ω ∂μ, Q y ω) :
    ∀ᵐ ω ∂μ, ∀ y ∈ b2_latticePts d, Q y ω := by
  have h' : ∀ y ∈ b2_latticePts d, ∀ᵐ ω ∂μ, Q y ω := fun y _ => h y
  exact (ae_ball_iff (p := fun (ω : Ω) (y : Vec d) (_ : y ∈ b2_latticePts d) => Q y ω)
    (b2_latticePts_countable d)).2 h'

/-- A finer, larger grid contains a coarser, smaller one. -/
theorem b2_gridPts_mono {d : ℕ} {j j' : ℤ} {R R' : ℝ} (hj : j' ≤ j) (hR : 0 ≤ R) (hRR : R ≤ R') :
    gridPts d j R ⊆ gridPts d j' R' := by
  intro y hy
  obtain ⟨k, hk, hb⟩ := (mem_gridPts hR y).1 hy
  refine (mem_gridPts (hR.trans hRR) y).2 ⟨fun i => (3 ^ (j - j').toNat : ℤ) * k i, fun i => ?_,
    fun i => (hb i).trans hRR⟩
  have h3 : (3 : ℝ) ^ j = (3 : ℝ) ^ j' * (3 : ℝ) ^ ((j - j').toNat : ℤ) := by
    rw [← zpow_add₀ (by norm_num), Int.toNat_of_nonneg (by omega)]
    congr 1
    omega
  rw [hk i, h3]
  push_cast
  rw [zpow_natCast]
  ring

/-- The bottom scale at `(N + 1, n + b)` is below the one at `(N, n)`, for `exp b ≤ n`. -/
theorem b2_nK_succ_le {N : ℝ} (hN : 0 ≤ N) (b n : ℕ) (hn : Real.exp b ≤ (n : ℝ)) :
    nK (N + 1) (n + b) ≤ nK N n := by
  have hn1 : (1 : ℝ) ≤ n := (Real.one_le_exp (Nat.cast_nonneg b)).trans hn
  have hn0 : (0 : ℝ) < n := by linarith only [hn1]
  have hlogn : Real.log (n : ℝ) ≤ Real.log ((n : ℝ) + b) :=
    Real.log_le_log hn0 (by linarith only [(Nat.cast_nonneg b : (0 : ℝ) ≤ b)])
  have hb : (b : ℝ) ≤ Real.log ((n : ℝ) + b) :=
    (Real.le_log_iff_exp_le (by linarith only [hn0, (Nat.cast_nonneg b : (0 : ℝ) ≤ b)])).2
      (hn.trans (by linarith only [(Nat.cast_nonneg b : (0 : ℝ) ≤ b)]))
  have hlog0 : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn1
  have hc : ⌈N * Real.log (n : ℝ)⌉₊ + b ≤ ⌈(N + 1) * Real.log (((n + b : ℕ)) : ℝ)⌉₊ := by
    rw [← Nat.ceil_add_natCast (mul_nonneg hN hlog0)]
    refine Nat.ceil_mono ?_
    push_cast
    have : N * Real.log (n : ℝ) ≤ N * Real.log ((n : ℝ) + b) :=
      mul_le_mul_of_nonneg_left hlogn hN
    nlinarith only [this, hb]
  unfold nK
  omega

/-- **The scale of the grid maximum of the translates of one scale.** -/
theorem b2_gridMax_scale (d : ℕ) [NeZero d] {N σ : ℝ} (hN : 0 ≤ N) (hσ : 0 < σ) (b : ℕ) :
    ∃ Cg : ℝ, 1 ≤ Cg ∧
      ∀ (P : ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
        (_ : ShellLawPrefix d P) (_ : ShellLawJ2 d P)
        (X0 : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ) (_ : Measurable X0)
        (Lam : ℝ), 1 ≤ Lam →
        Homogenization.IndependentSums.IsBigO P.toMeasure
          (Homogenization.IndependentSums.gammaSigma σ) (fun omega => Real.log (X0 omega)) Lam →
        ∃ Xs : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ, Measurable Xs ∧
          (∀ omega, 1 ≤ Xs omega) ∧
          Homogenization.IndependentSums.IsBigO P.toMeasure
            (Homogenization.IndependentSums.gammaSigma σ) (fun omega => Real.log (Xs omega))
            (max (Cg * Lam * (1 + Real.log Lam) ^ σ⁻¹) (Real.exp b)) ∧
          ∀ᵐ omega ∂P.toMeasure, ∀ s : ℕ,
            max (Cg * Lam * (1 + Real.log Lam) ^ σ⁻¹) (Real.exp b) ≤ (s : ℝ) →
            Xs omega ≤ (3 : ℝ) ^ nK (N + 1) (s + b) →
            ∀ y ∈ gridPts d ((nK N s : ℤ) - 3) ((3 : ℝ) ^ (s + b)),
              X0 (ShellField.translateSequence y omega) ≤ (3 : ℝ) ^ nK N s := by
  obtain ⟨Cg, hCg, H⟩ := exists_gridMax_scale d (N := N + 1) (σ := σ)
    (by linarith only [hN]) hσ
  refine ⟨Cg, hCg, ?_⟩
  intro P hPrefix hJ2 X0 hX0 Lam hLam hO
  obtain ⟨Xs, hXs, hXsO, hXsae⟩ := H P.toMeasure
    (fun y omega => X0 (ShellField.translateSequence y omega))
    (fun y => hX0.comp (ShellField.measurable_translateSequence y)) Lam hLam
    (fun y => isBigO_comp_translateSequence hPrefix hJ2 y (Real.measurable_log.comp hX0) hO)
  have hlogL : 0 ≤ Real.log Lam := Real.log_nonneg hLam
  have hpow : 1 ≤ (1 + Real.log Lam) ^ σ⁻¹ :=
    Real.one_le_rpow (by linarith only [hlogL]) (inv_nonneg.2 hσ.le)
  have hTle : Cg * Lam * (1 + Real.log Lam) ^ σ⁻¹ ≤
      max (Cg * Lam * (1 + Real.log Lam) ^ σ⁻¹) (Real.exp b) := le_max_left _ _
  refine ⟨fun omega => max 1 (Xs omega), measurable_const.max hXs, fun omega => le_max_left _ _,
    ?_, ?_⟩
  · refine (hXsO.of_abs_le (Y := fun omega => Real.log (max 1 (Xs omega))) ?_).mono_scale hTle
    intro omega
    by_cases h : 1 ≤ Xs omega
    · rw [max_eq_right h]
    · rw [max_eq_left (not_le.1 h).le, Real.log_one, abs_zero]
      exact abs_nonneg _
  · filter_upwards [hXsae] with omega hω s hs hX y hy
    have hbs : Real.exp b ≤ (s : ℝ) := (le_max_right _ _).trans hs
    have hT : Cg * Lam * (1 + Real.log Lam) ^ σ⁻¹ ≤ ((s + b : ℕ) : ℝ) := by
      push_cast
      linarith only [hTle.trans hs, (Nat.cast_nonneg b : (0 : ℝ) ≤ b)]
    have hXs' : Xs omega ≤ (3 : ℝ) ^ nK (N + 1) (s + b) := (le_max_right _ _).trans hX
    have hcmp := b2_nK_succ_le hN b s hbs
    have hmax := hω (s + b) hT hXs'
    have hR : (0 : ℝ) ≤ (3 : ℝ) ^ (s + b) := by positivity
    have hy' : y ∈ gridPts d ((nK (N + 1) (s + b) : ℤ) - 3) ((3 : ℝ) ^ (s + b + 2)) :=
      b2_gridPts_mono (by omega) hR (pow_le_pow_right₀ (by norm_num) (by omega)) hy
    have h1 := (X0max_le_iff _ _ (by positivity) _).1 hmax y hy'
    exact h1.trans (pow_le_pow_right₀ (by norm_num) hcmp)

/-- Witness: the non-law hypotheses of `b2_gridMax_scale` are satisfiable (the Dirac zero law,
which satisfies the prefix and `J2`, with the constant scale `X₀ = 1`, `Λ = 1`). -/
example (d : ℕ) [NeZero d] (hd : 2 ≤ d) (σ : ℝ) :
    ∃ (P : ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
      (_ : ShellLawPrefix d P) (_ : ShellLawJ2 d P)
      (X0 : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ), Measurable X0 ∧
      Homogenization.IndependentSums.IsBigO P.toMeasure
        (Homogenization.IndependentSums.gammaSigma σ) (fun omega => Real.log (X0 omega)) 1 := by
  obtain ⟨P, hP, -, hJ2, -, -⟩ :=
    SuperdiffusionCLT.Assumptions.ShellLaw.exists_law_satisfying_prefix_J1_J4 (d := d) hd
  refine ⟨P, hP, hJ2, fun _ => 1, measurable_const, ?_⟩
  rw [Homogenization.IndependentSums.isBigO_gammaSigma_iff]
  intro t ht
  have : Homogenization.IndependentSums.absTailEvent
      (fun _ : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d =>
        Real.log ((fun _ => (1 : ℝ)) ())) (1 * t) = ∅ := by
    ext omega
    simp only [Homogenization.IndependentSums.mem_absTailEvent, Real.log_one, abs_zero,
      Set.mem_empty_iff_false, iff_false, not_lt]
    linarith only [ht]
  rw [this]
  simpa using (Real.exp_pos (-t ^ σ)).le

end

end SuperdiffusionCLT.Section7

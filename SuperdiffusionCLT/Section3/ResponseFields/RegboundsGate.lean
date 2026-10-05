/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Frozen.Section2.StreamIncrementScaleEstimates
public import SuperdiffusionCLT.Section3.ResponseFields.RegboundsB

/-!
# `l.w.basic.regbounds` with the scale-estimate hypotheses discharged

Lemma `l.w.basic.regbounds` of the paper (display `e.nablaw.Lt`).

`Section3/ResponseFields/RegboundsB.lean` carries the constants of `e.nablaw.Lt`
with five explicit inputs: the conclusion of the a priori response anchor, the
three shell-increment clauses `e.kmn.Lp` at `p = 8` and `p = 2` and
`e.kmn.Hs.osc` at `s = 1/2`, and the printed Jacobian estimate for the shells
below the cube scale.  Three of those five are conclusions of the theorem
`SuperdiffusionCLT.Frozen.Section2.streamIncrement_scale_estimates`, so
they need not be hypotheses.  This module discharges them.

## Which conjuncts of the scale estimates are consumed

The conclusion of that theorem, after `∃ C₂`, `s = 1/2`, `∃ C₀ C₁`, an exponent `p > 1`
and `∃ C`, is a conjunction of three blocks:

1. `∀ l m n, n < m → m ≤ l → (a) ∧ (b) ∧ (c) ∧ (d)`, the four norms of
   `k_m − k_n` on `cu_l`;
2. `∀ l n, …`, the oscillation clause: the `Γ₂` bound on the supremum over all
   `M > n` of the Gagliardo seminorm of `k_M − k_n` on `cu_l`;
3. the "Moreover" block of the random scale `K_σ`.

Consumed here: the **second conjunct of block 1** (the `L̲^p` clause `e.kmn.Lp`)
at the exponent `p = 8` and again at `p = 2`, both at `(l, m, n) =
(m, m − 1, ℓ')`; and **block 2** (the oscillation clause `e.kmn.Hs.osc`) at
`(l, n) = (m, ℓ')`.  Block 3 is not consumed: the regbounds chain never touches
the random scale, so the normalization of its third term is invisible here.

The three consumed clauses match the shapes `RegboundsB.lean` carries with no
reshaping whatsoever: the amplitudes and the pointwise bounds are the stated
ones with `s := 1/2`, `p := 8` respectively `2`, `l := m`, `m := m − 1`,
`n := ℓ'`.  Two bookkeeping steps are needed and are done here:

* the clause constant of the theorem is a bare `∃ C : ℝ` with no sign, while the
  oscillation input of `RegboundsB.lean` asks for a positive constant, so the
  amplitude is raised from `C` to `|C| + 1` by `IsBigO.mono_scale`; and
* block 1 of the theorem is guarded by `n < m`, i.e. by `ℓ' < m − 1`, which
  `ScalesOrdering` does not supply (it gives only `ℓ' < m`).  In the excluded
  case `m − 1 ≤ ℓ'` the increment `k_{m−1} − k_{ℓ'}` is the empty sum, so both
  `L̲^p` clauses hold with the witness `0`; that branch is discharged below in
  `exists_kmnLpClause_of_gate`, so no extra hypothesis on the window `h`
  appears in the statement.

## What remains an input

After this module the assembly of `e.nablaw.Lt` carries exactly two hypotheses beyond the
typing data: the conclusion of the a priori anchor `responseFields_apriori_orderZero`, in its
stated shape; and the printed estimate for the Jacobian of the shells below the
cube scale, which is a small-cube statement not covered by the scale estimates.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.ResponseFields

open MeasureTheory
open Homogenization
open Homogenization.Book.Ch02
open Homogenization.IndependentSums
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Norms
open SuperdiffusionCLT.Section3.Setup
open scoped ENNReal Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-! ## The empty shell increment -/

/-- An increment `k_m − k_n` with `m ≤ n` is the empty sum of shells, hence the
zero field, hence of zero size in every `L̲^q(cu_l)`. -/
theorem cubeLpENorm_finiteShellIncrement_eq_zero (omega : ShellSeq d) {n m : ℕ}
    (hmn : m ≤ n) (l : ℕ) (q : ℝ≥0∞) :
    cubeLpENorm (originCube d (l : ℤ)) q
        (fun x => (finiteShellIncrement omega n m x : Mat d)) = 0 := by
  have hfun : (fun x => (finiteShellIncrement omega n m x : Mat d)) = 0 := by
    funext x
    rw [finiteShellIncrement_apply, Finset.Ioc_eq_empty (by omega), Finset.sum_empty]
    rfl
  rw [hfun, cubeLpENorm_zero]

/-- The zero variable has every `Γ₂` tail at amplitude `0`. -/
theorem isBigO_gammaSigma_two_zero (P : ProbabilityMeasure (ShellSeq d)) :
    IsBigO P.toMeasure (gammaSigma 2) (fun _ : ShellSeq d => (0 : ℝ)) 0 := by
  intro t _ht
  have hset : upperTailEvent (fun _ : ShellSeq d => |(0 : ℝ)|) (0 * t)
      = (∅ : Set (ShellSeq d)) := by
    ext omega
    simp [upperTailEvent]
  rw [hset, measureReal_empty]
  have hpos : (0 : ℝ) < gammaSigma 2 t := Real.exp_pos _
  positivity

/-! ## The `L̲^p` clause with its guard removed -/

/-- **`e.kmn.Lp` at `(l, m, n)` with the guard `n < m` removed.** The scale estimates
state their `L̲^p` clause only for `n < m`; in the remaining case the increment
is the zero field and the clause holds with the witness `0`, the two `(m − n)`
factors being `0` as well. -/
theorem exists_kmnLpClause_of_gate {P : ProbabilityMeasure (ShellSeq d)}
    {C q : ℝ} {l m n : ℕ}
    (hgate : n < m →
      ∃ X : ShellSeq d → ℝ, Measurable X ∧
        IsBigO P.toMeasure (gammaSigma 2) X
          (C * q ^ ((1 : ℝ) / 2) * ((m - n : ℕ) : ℝ) ^ ((1 : ℝ) / 2) *
            (3 : ℝ) ^ (-((d : ℝ) / (2 * q) * ((l - m : ℕ) : ℝ)))) ∧
        ∀ omega : ShellSeq d,
          cubeLpENorm (originCube d (l : ℤ)) (ENNReal.ofReal q)
              (fun x => (finiteShellIncrement omega n m x : Mat d)) ≤
            ENNReal.ofReal (C * ((m - n : ℕ) : ℝ) ^ ((1 : ℝ) / 2) + X omega)) :
    ∃ X : ShellSeq d → ℝ, Measurable X ∧
      IsBigO P.toMeasure (gammaSigma 2) X
        (C * q ^ ((1 : ℝ) / 2) * ((m - n : ℕ) : ℝ) ^ ((1 : ℝ) / 2) *
          (3 : ℝ) ^ (-((d : ℝ) / (2 * q) * ((l - m : ℕ) : ℝ)))) ∧
      ∀ omega : ShellSeq d,
        cubeLpENorm (originCube d (l : ℤ)) (ENNReal.ofReal q)
            (fun x => (finiteShellIncrement omega n m x : Mat d)) ≤
          ENNReal.ofReal (C * ((m - n : ℕ) : ℝ) ^ ((1 : ℝ) / 2) + X omega) := by
  by_cases hlt : n < m
  · exact hgate hlt
  · have hmn : m ≤ n := by omega
    have hzero : ((m - n : ℕ) : ℝ) ^ ((1 : ℝ) / 2) = 0 := by
      rw [Nat.sub_eq_zero_of_le hmn, Nat.cast_zero]
      exact Real.zero_rpow (by norm_num)
    refine ⟨fun _ => 0, measurable_const, ?_, ?_⟩
    · have hamp : C * q ^ ((1 : ℝ) / 2) * ((m - n : ℕ) : ℝ) ^ ((1 : ℝ) / 2) *
          (3 : ℝ) ^ (-((d : ℝ) / (2 * q) * ((l - m : ℕ) : ℝ))) = 0 := by
        rw [hzero]; ring
      rw [hamp]
      exact isBigO_gammaSigma_two_zero P
    · intro omega
      rw [cubeLpENorm_finiteShellIncrement_eq_zero omega hmn l (ENNReal.ofReal q),
        hzero, mul_zero, zero_add, ENNReal.ofReal_zero]

end

end SuperdiffusionCLT.Section3.ResponseFields

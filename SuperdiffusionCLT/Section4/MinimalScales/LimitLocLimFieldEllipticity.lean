/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section4.MinimalScales.LimitLocLimFieldMeasurable
public import SuperdiffusionCLT.Section2.Cutoff.CutoffApproximationInputs
public import SuperdiffusionCLT.Section2.CoarseGraining.CutoffCorrespondence

/-!
# Everywhere ellipticity of the shifted limiting field `srootE_limField`

Mirrors `SuperdiffusionCLT.Section4.MinimalScales.srootL3_isEllipticFieldOn_srootE_field`
(`LimitRespEllipticity.lean`) for the *limiting* field: raw-`Set`-domain entry
bound of `centeredStreamField` on the recentering cube `cu_m` itself, combined
with `symmPart_smul_one_add_of_skew` and the shift-through of the measurability
result of `LimitLocLimFieldMeasurable.lean`, to give an EVERYWHERE (not merely
a.e.) `IsEllipticFieldOn` statement for `srootE_limField` on `cubeSet (originCube
d n)`, given a *global* summability hypothesis on the shell-derivative
sup-norms on `cu_m` (discharged a.s. downstream via `ShellLawJ3`, as
`LimitTermFieldUniform.lean` already does for the uniform field-convergence
result).

## Main result

* `srootL4_isEllipticFieldOn_srootE_limField`: `srootE_limField nu omega m n k`
  is `(nu, Lam)`-elliptic everywhere on `cubeSet (originCube d n)`, for an
  explicit `Lam` depending only on `nu, d`, the diameter of `cu_m`, and the
  total shell-derivative sup-norm sum on `cu_m`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section4.MinimalScales

open Homogenization MeasureTheory
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Carriers
open SuperdiffusionCLT.Section2.CoarseGraining
open scoped Matrix.Norms.Elementwise

noncomputable section

/-- The entry bound of `ν Id + K` from an entry bound of `K` (reproved here
because `SuperdiffusionCLT.Section2.Cutoff.abs_entry_smul_one_add_le` is
`private`). -/
private theorem srootL4_abs_entry_smul_one_add_le {d : ℕ} {nu C : ℝ} (hnu : 0 < nu)
    {K : Mat d} (hK : ∀ i j, |K i j| ≤ C) (i j : Fin d) :
    |(nu • (1 : Mat d) + K) i j| ≤ nu + C := by
  have h1 : |(nu • (1 : Mat d)) i j| ≤ nu := by
    rw [Matrix.smul_apply, smul_eq_mul]
    by_cases hij : i = j
    · subst hij
      rw [Matrix.one_apply_eq, mul_one, abs_of_pos hnu]
    · rw [Matrix.one_apply_ne hij, mul_zero, abs_zero]
      exact hnu.le
  calc |(nu • (1 : Mat d) + K) i j| = |(nu • (1 : Mat d)) i j + K i j| := by rw [Matrix.add_apply]
    _ ≤ |(nu • (1 : Mat d)) i j| + |K i j| := abs_add_le _ _
    _ ≤ nu + C := add_le_add h1 (hK i j)

/-- A raw-`Set`-domain entry bound for `centeredStreamField` on the recentering
cube `cu_m` itself: no `Book.Ch02.Domain` wrapper (mirrors
`SuperdiffusionCLT.Section2.Cutoff.abs_centeredStreamField_entry_le`, whose
proof this repeats with the domain supplied directly). -/
private theorem srootL4_abs_centeredStreamField_entry_le {d : ℕ} (omega : ShellSeq d)
    (m : ℕ) (hsum : Summable fun j : ℕ =>
      shellDerivLinftyNorm (cubeSet (originCube d (m : ℤ))) (omega j))
    {y : Vec d} (hy : y ∈ cubeSet (originCube d (m : ℤ))) (i j : Fin d) :
    |centeredStreamField omega (cubeSet (originCube d (m : ℤ))) y i j| ≤
      Real.sqrt d * (Metric.diam (cubeSet (originCube d (m : ℤ)))) *
        (∑' l : ℕ, shellDerivLinftyNorm (cubeSet (originCube d (m : ℤ))) (omega l)) := by
  set U : Set (Vec d) := cubeSet (originCube d (m : ℤ)) with hUdef
  have hUb : Bornology.IsBounded U := isBounded_cubeSet _
  have hUconv : Convex ℝ U := SuperdiffusionCLT.Section2.Estimates.Stream.convex_cubeSet _
  have hUpos : MeasureTheory.volume U ≠ 0 :=
    SuperdiffusionCLT.Section2.Estimates.Stream.volume_cubeSet_ne_zero _
  have hR : ∀ ⦃a : Vec d⦄, a ∈ U → ∀ ⦃b : Vec d⦄, b ∈ U → dist a b ≤ Metric.diam U :=
    fun a ha b hb => Metric.dist_le_diam_of_mem hUb ha hb
  have hbound : ∀ l : ℕ,
      ‖centeredShellTerm omega U l y‖ ≤
        Real.sqrt d * (Metric.diam U) * shellDerivLinftyNorm U (omega l) :=
    fun l => norm_centeredShellTerm_le hUb hUconv hUpos hR omega l hy
  have hNormSum : Summable fun l : ℕ => ‖centeredShellTerm omega U l y‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hbound (hsum.mul_left _)
  have hnorm : ‖centeredStreamField omega U y‖ ≤
      Real.sqrt d * (Metric.diam U) *
        (∑' l : ℕ, shellDerivLinftyNorm U (omega l)) := by
    calc ‖centeredStreamField omega U y‖
        = ‖∑' l : ℕ, centeredShellTerm omega U l y‖ := by rw [centeredStreamField_eq_tsum]
      _ ≤ ∑' l : ℕ, ‖centeredShellTerm omega U l y‖ := norm_tsum_le_tsum_norm hNormSum
      _ ≤ ∑' l : ℕ, Real.sqrt d * (Metric.diam U) * shellDerivLinftyNorm U (omega l) :=
          hNormSum.tsum_le_tsum hbound (hsum.mul_left _)
      _ = Real.sqrt d * (Metric.diam U) * (∑' l : ℕ, shellDerivLinftyNorm U (omega l)) :=
          tsum_mul_left
  calc |centeredStreamField omega U y i j| = ‖centeredStreamField omega U y i j‖ := by
        rw [Real.norm_eq_abs]
    _ ≤ ‖centeredStreamField omega U y‖ := Matrix.norm_entry_le_entrywise_sup_norm _
    _ ≤ _ := hnorm

open Classical in
/-- **The shifted limiting field `srootE_limField` is everywhere `(nu,
Lam)`-elliptic on `cubeSet (originCube d n)`.** -/
theorem srootL4_isEllipticFieldOn_srootE_limField {d : ℕ} (nu : ℝ) (hnu : 0 < nu)
    (omega : ShellSeq d) (m n : ℕ) (k : Fin d → ℤ)
    (hk : (fun x => (fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x) ''
          cubeSet (originCube d (n : ℤ)) ⊆ cubeSet (originCube d (m : ℤ)))
    (hsum : Summable fun j : ℕ =>
      shellDerivLinftyNorm (cubeSet (originCube d (m : ℤ))) (omega j)) :
    ∃ Lam : ℝ, IsEllipticFieldOn nu Lam (cubeSet (originCube d (n : ℤ)))
        (srootE_limField nu omega m n k) := by
  set C : ℝ := Real.sqrt d * (Metric.diam (cubeSet (originCube d (m : ℤ)))) *
    (∑' l : ℕ, shellDerivLinftyNorm (cubeSet (originCube d (m : ℤ))) (omega l)) with hCdef
  refine ⟨((d : ℝ) * (d : ℝ) * (nu + C) ^ 2 + nu ^ 2) / nu, ?_, ?_⟩
  · refine Measurable.of_eval fun i => Measurable.of_eval fun j => ?_
    have hmeas := srootL4_measurable_srootE_limField_entry omega m n k hk hsum i j
    have hconst : Measurable (fun x : Vec d =>
        if x ∈ cubeSet (originCube d (n : ℤ)) then (nu • (1 : Mat d)) i j else 0) :=
      Measurable.ite (measurableSet_cubeSet _) measurable_const measurable_const
    have hcomb := hconst.add hmeas
    have heq : (fun x : Vec d =>
        (if x ∈ cubeSet (originCube d (n : ℤ)) then (nu • (1 : Mat d)) i j else 0) +
          if x ∈ cubeSet (originCube d (n : ℤ))
          then centeredStreamField omega (cubeSet (originCube d (m : ℤ)))
            ((fun l => (3 : ℝ) ^ ((n : ℤ) - 3) * (k l : ℝ)) + x) i j
          else 0) =
        fun x : Vec d =>
          if x ∈ cubeSet (originCube d (n : ℤ)) then srootE_limField nu omega m n k x i j
          else 0 := by
      funext x
      by_cases hx : x ∈ cubeSet (originCube d (n : ℤ))
      · simp only [hx, ite_true, srootE_limField, Matrix.add_apply]
      · simp only [hx, ite_false, add_zero]
    rw [← heq]; exact hcomb
  · intro x hx
    have hxUm : (fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x ∈
        cubeSet (originCube d (m : ℤ)) := hk ⟨x, hx, rfl⟩
    have hentryK : ∀ i j : Fin d,
        |centeredStreamField omega (cubeSet (originCube d (m : ℤ)))
            ((fun l => (3 : ℝ) ^ ((n : ℤ) - 3) * (k l : ℝ)) + x) i j| ≤ C :=
      fun i j => srootL4_abs_centeredStreamField_entry_le omega m hsum hxUm i j
    have hentry : ∀ i j : Fin d, |srootE_limField nu omega m n k x i j| ≤ nu + C := by
      intro i j
      show |(nu • (1 : Mat d) +
        centeredStreamField omega (cubeSet (originCube d (m : ℤ)))
          ((fun l => (3 : ℝ) ^ ((n : ℤ) - 3) * (k l : ℝ)) + x)) i j| ≤ nu + C
      exact srootL4_abs_entry_smul_one_add_le hnu hentryK i j
    have hsymm : symmPart (srootE_limField nu omega m n k x) = nu • (1 : Mat d) := by
      show symmPart (nu • (1 : Mat d) +
        centeredStreamField omega (cubeSet (originCube d (m : ℤ)))
          ((fun l => (3 : ℝ) ^ ((n : ℤ) - 3) * (k l : ℝ)) + x)) = nu • (1 : Mat d)
      exact symmPart_smul_one_add_of_skew
        (centeredStreamField_skew omega (cubeSet (originCube d (m : ℤ))) _)
    exact isEllipticMatrix_of_symmPart_eq_smul_one hnu hsymm hentry

end

end SuperdiffusionCLT.Section4.MinimalScales

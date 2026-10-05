/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Carriers.CenteredStreamField
public import SuperdiffusionCLT.Section2.CoarseGraining.CutoffCorrespondence

/-!
# The limiting centered field as an elliptic coefficient field

The cutoff approximation lemma `l.cutoff.approximation` has as its first assertion
that the limiting centered coefficient field

`a^U = ν Id + k^U`,  `k^U = ∑_{k=0}^∞ (j_k - (j_k)_U)`,

is uniformly elliptic in `U` under the manuscript's own summability hypothesis
`∑_{k=0}^∞ ‖∇ j_k‖_{L∞(U)} < ∞`. This module discharges that
assertion from the summability hypothesis alone.

The argument has two steps, both hypothesis-free apart from summability:

* `norm_centeredStreamField_le`, `abs_centeredStreamField_entry_le`: the
  summability hypothesis bounds every entry of `k^U` on `U` by the *same*
  constant `√d R ∑_k ‖∇ j_k‖_{L∞(U)}`, where `R` bounds the diameter of `U`.
  This is the manuscript's printed `L^∞(U)` convergence of the recentered series
  at the level of the carrier `Carriers.centeredStreamField`;
  the averaging bound is `Carriers.norm_centeredShellTerm_le`.
* `isEllipticMatrix_smul_one_add_centeredStreamField`,
  `exists_isEllipticMatrix_smul_one_add_centeredStreamField`: because `k^U` is
  anti-symmetric (`Carriers.centeredStreamField_skew`), the symmetric part of
  `a^U` is exactly `ν Id`, and the entry bound converts to the two-sided
  `IsEllipticMatrix` condition with constants `ν` and `(d² C² + ν²)/ν`. The
  conversion is
  `Section2.CoarseGraining.isEllipticMatrix_of_symmPart_eq_smul_one`.

The second assertion of the lemma — existence of `u_L ∈ u + H¹₀(U)` harmonic for
the cutoff `a_L` with the quantitative bound — is assembled from
`Section2.Localization.CutoffComparison` together with a `CoeffOn` object for
`a^U`; the size estimate it consumes is `norm_centeredStreamField_le` here.

## Main definitions and results

* `symmPart_smul_one_add_of_skew`: the symmetric part of `ν Id + K` is `ν Id`
  for an anti-symmetric `K`.
* `norm_centeredStreamField_le`: the `L∞(U)` bound of `k^U`.
* `abs_centeredStreamField_entry_le`: the entrywise form of that bound.
* `norm_centeredStreamField_sub_centeredStreamCutoff_le`: the tail
  `k^U - (k_L - (k_L)_U)`, the perturbation whose size the energy comparison of
  `l.cutoff.approximation` consumes.
* `isEllipticMatrix_smul_one_add_centeredStreamField`: pointwise ellipticity of
  `a^U` from an entry bound.
* `exists_isEllipticMatrix_smul_one_add_centeredStreamField`: the first
  assertion of `l.cutoff.approximation`, with `lam`, `Lam` explicit and no
  hypothesis beyond `0 < ν` and the printed summability.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section2.Cutoff

open Homogenization
open Homogenization.Book.Ch02
open SuperdiffusionCLT.Section2.Carriers
open scoped Matrix.Norms.Elementwise

noncomputable section

variable {d : ℕ}

/-! ## The symmetric part of the limiting centered field -/

/-- Adding an anti-symmetric matrix to `ν Id` leaves the symmetric part `ν Id`,
the identity used in the proof of `l.cutoff.approximation` for
`a^U = ν Id + k^U`. -/
theorem symmPart_smul_one_add_of_skew {nu : ℝ} {K : Mat d}
    (hK : matTranspose K = -K) :
    symmPart (nu • (1 : Mat d) + K) = nu • (1 : Mat d) := by
  ext i j
  have hji : K j i = -K i j := congrFun (congrFun hK i) j
  have hone : (1 : Mat d) j i = (1 : Mat d) i j := by
    by_cases hij : i = j
    · subst hij
      rfl
    · have hji : ¬(j = i) := fun h => hij h.symm
      rw [Matrix.one_apply, Matrix.one_apply, ite_eq_right hji, ite_eq_right hij]
  simp only [symmPart, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, hji, hone]
  ring

/-- The entrywise bound of `ν Id + K` from an entrywise bound of the
anti-symmetric matrix `K`. -/
private theorem abs_entry_smul_one_add_le {nu C : ℝ} (hnu : 0 < nu) {K : Mat d}
    (hK : ∀ i j, |K i j| ≤ C) (i j : Fin d) :
    |(nu • (1 : Mat d) + K) i j| ≤ nu + C := by
  have h1 : |(nu • (1 : Mat d)) i j| ≤ nu := by
    rw [Matrix.smul_apply, smul_eq_mul]
    by_cases hij : i = j
    · subst hij
      rw [Matrix.one_apply, ite_eq_left rfl, mul_one, abs_of_pos hnu]
    · rw [Matrix.one_apply, ite_eq_right hij, mul_zero, abs_zero]
      exact hnu.le
  calc
    |(nu • (1 : Mat d) + K) i j|
        = |(nu • (1 : Mat d)) i j + K i j| := by rw [Matrix.add_apply]
    _ ≤ |(nu • (1 : Mat d)) i j| + |K i j| := abs_add_le _ _
    _ ≤ nu + C := add_le_add h1 (hK i j)

/-! ## The uniform `L∞(U)` bound of the recentered series -/

/-- **The recentered series `k^U` is uniformly bounded on `U`** by
`√d R ∑_k ‖∇ j_k‖_{L∞(U)}` under the manuscript's summability hypothesis. The
factor `R` bounds the diameter of `U` and `√d` is the dimensional loss of
`Carriers.norm_centeredShellTerm_le`; the bound is uniform in `x ∈ U`. -/
theorem norm_centeredStreamField_le (U : Domain d) (omega : ShellSeq d) {R : ℝ}
    (hR : ∀ ⦃a : Vec d⦄, a ∈ (U : Set (Vec d)) → ∀ ⦃b : Vec d⦄,
      b ∈ (U : Set (Vec d)) → dist a b ≤ R)
    (hsum : Summable fun k : ℕ =>
      shellDerivLinftyNorm (U : Set (Vec d)) (omega k))
    {x : Vec d} (hx : x ∈ (U : Set (Vec d))) :
    ‖centeredStreamField omega (U : Set (Vec d)) x‖ ≤
      Real.sqrt d * R * (∑' k : ℕ,
        shellDerivLinftyNorm (U : Set (Vec d)) (omega k)) := by
  have hUb : Bornology.IsBounded (U : Set (Vec d)) :=
    U.isDomain.isBoundedDomain.isBounded
  have hUconv : Convex ℝ (U : Set (Vec d)) := U.convex
  have hUpos : MeasureTheory.volume (U : Set (Vec d)) ≠ 0 :=
    (IsOpen.measure_pos MeasureTheory.volume U.isOpen U.nonempty).ne'
  have hbound : ∀ k : ℕ,
      ‖centeredShellTerm omega (U : Set (Vec d)) k x‖ ≤
        Real.sqrt d * R * shellDerivLinftyNorm (U : Set (Vec d)) (omega k) :=
    fun k => norm_centeredShellTerm_le hUb hUconv hUpos hR omega k hx
  have hNormSum : Summable fun k : ℕ =>
      ‖centeredShellTerm omega (U : Set (Vec d)) k x‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hbound (hsum.mul_left _)
  calc
    ‖centeredStreamField omega (U : Set (Vec d)) x‖
        = ‖∑' k : ℕ, centeredShellTerm omega (U : Set (Vec d)) k x‖ := by
          rw [centeredStreamField_eq_tsum]
    _ ≤ ∑' k : ℕ, ‖centeredShellTerm omega (U : Set (Vec d)) k x‖ :=
          norm_tsum_le_tsum_norm hNormSum
    _ ≤ ∑' k : ℕ, Real.sqrt d * R *
          shellDerivLinftyNorm (U : Set (Vec d)) (omega k) :=
          hNormSum.tsum_le_tsum hbound (hsum.mul_left _)
    _ = Real.sqrt d * R * (∑' k : ℕ,
          shellDerivLinftyNorm (U : Set (Vec d)) (omega k)) :=
          tsum_mul_left

/-- **Entrywise form of the uniform bound.** Every entry of `k^U` on `U` is
controlled by the same constant, which is what the ellipticity conversion
consumes. -/
theorem abs_centeredStreamField_entry_le (U : Domain d) (omega : ShellSeq d) {R : ℝ}
    (hR : ∀ ⦃a : Vec d⦄, a ∈ (U : Set (Vec d)) → ∀ ⦃b : Vec d⦄,
      b ∈ (U : Set (Vec d)) → dist a b ≤ R)
    (hsum : Summable fun k : ℕ =>
      shellDerivLinftyNorm (U : Set (Vec d)) (omega k))
    {x : Vec d} (hx : x ∈ (U : Set (Vec d))) (i j : Fin d) :
    |centeredStreamField omega (U : Set (Vec d)) x i j| ≤
      Real.sqrt d * R * (∑' k : ℕ,
        shellDerivLinftyNorm (U : Set (Vec d)) (omega k)) := by
  calc
    |centeredStreamField omega (U : Set (Vec d)) x i j|
        = ‖centeredStreamField omega (U : Set (Vec d)) x i j‖ := by
          rw [Real.norm_eq_abs]
    _ ≤ ‖centeredStreamField omega (U : Set (Vec d)) x‖ :=
          Matrix.norm_entry_le_entrywise_sup_norm _
    _ ≤ Real.sqrt d * R * (∑' k : ℕ,
          shellDerivLinftyNorm (U : Set (Vec d)) (omega k)) :=
          norm_centeredStreamField_le U omega hR hsum hx

/-! ## The tail estimate behind the comparison constant -/

/-- **The difference `k^U - (k_L - (k_L)_U)` is the tail of the recentered
series**, and the summability hypothesis bounds it on `U` by
`√d R ∑_{k > L} ‖∇ j_k‖_{L∞(U)}` (reindexed `L + 1 + k`). This is the size of
the coefficient-perturbation constant in the printed energy comparison of
`l.cutoff.approximation`: the field `k^U` differs from the level-`L` centered
representative exactly by this tail. -/
theorem norm_centeredStreamField_sub_centeredStreamCutoff_le (U : Domain d)
    (omega : ShellSeq d) {R : ℝ}
    (hR : ∀ ⦃a : Vec d⦄, a ∈ (U : Set (Vec d)) → ∀ ⦃b : Vec d⦄,
      b ∈ (U : Set (Vec d)) → dist a b ≤ R)
    (hsum : Summable fun k : ℕ =>
      shellDerivLinftyNorm (U : Set (Vec d)) (omega k))
    {x : Vec d} (hx : x ∈ (U : Set (Vec d))) (L : ℕ) :
    ‖centeredStreamField omega (U : Set (Vec d)) x -
        centeredStreamCutoff omega L (U : Set (Vec d)) x‖ ≤
      Real.sqrt d * R * (∑' k : ℕ,
        shellDerivLinftyNorm (U : Set (Vec d)) (omega (L + 1 + k))) := by
  have hUb : Bornology.IsBounded (U : Set (Vec d)) :=
    U.isDomain.isBoundedDomain.isBounded
  have hUconv : Convex ℝ (U : Set (Vec d)) := U.convex
  have hUpos : MeasureTheory.volume (U : Set (Vec d)) ≠ 0 :=
    (IsOpen.measure_pos MeasureTheory.volume U.isOpen U.nonempty).ne'
  have hhead : Summable fun k : ℕ =>
      centeredShellTerm omega (U : Set (Vec d)) k x :=
    summable_centeredShellTerm hUb hUconv hUpos omega hsum hx
  have htail : Summable fun k : ℕ =>
      centeredShellTerm omega (U : Set (Vec d)) (L + 1 + k) x :=
    hhead.comp_injective (add_right_injective (L + 1))
  have htailNorm : Summable fun k : ℕ =>
      shellDerivLinftyNorm (U : Set (Vec d)) (omega (L + 1 + k)) :=
    hsum.comp_injective (add_right_injective (L + 1))
  have hbound : ∀ k : ℕ,
      ‖centeredShellTerm omega (U : Set (Vec d)) (L + 1 + k) x‖ ≤
        Real.sqrt d * R *
          shellDerivLinftyNorm (U : Set (Vec d)) (omega (L + 1 + k)) :=
    fun k => norm_centeredShellTerm_le hUb hUconv hUpos hR omega (L + 1 + k) hx
  have hNormSum : Summable fun k : ℕ =>
      ‖centeredShellTerm omega (U : Set (Vec d)) (L + 1 + k) x‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hbound (htailNorm.mul_left _)
  calc
    ‖centeredStreamField omega (U : Set (Vec d)) x -
        centeredStreamCutoff omega L (U : Set (Vec d)) x‖
        = ‖∑' k : ℕ, centeredShellTerm omega (U : Set (Vec d)) (L + 1 + k) x‖ := by
          rw [centeredStreamField_sub_centeredStreamCutoff hUb omega hhead L]
    _ ≤ ∑' k : ℕ, ‖centeredShellTerm omega (U : Set (Vec d)) (L + 1 + k) x‖ :=
          norm_tsum_le_tsum_norm hNormSum
    _ ≤ ∑' k : ℕ, Real.sqrt d * R *
          shellDerivLinftyNorm (U : Set (Vec d)) (omega (L + 1 + k)) :=
          hNormSum.tsum_le_tsum hbound (htailNorm.mul_left _)
    _ = Real.sqrt d * R * (∑' k : ℕ,
          shellDerivLinftyNorm (U : Set (Vec d)) (omega (L + 1 + k))) :=
          tsum_mul_left

/-! ## Ellipticity of `a^U = ν Id + k^U` -/

/-- **Pointwise ellipticity of `a^U` from an entry bound.** The anti-symmetry of
`k^U` fixes the symmetric part at `ν Id`, so with entries of `k^U` bounded by
`C` the two-sided constants are `ν` and `(d² (ν + C)² + ν²)/ν`. -/
theorem isEllipticMatrix_smul_one_add_centeredStreamField (U : Domain d)
    {nu C : ℝ} (hnu : 0 < nu) (omega : ShellSeq d)
    (hentry : ∀ x ∈ (U : Set (Vec d)), ∀ i j : Fin d,
      |centeredStreamField omega (U : Set (Vec d)) x i j| ≤ C)
    (x : Vec d) (hx : x ∈ (U : Set (Vec d))) :
    IsEllipticMatrix nu (((d : ℝ) * (d : ℝ) * (nu + C) ^ 2 + nu ^ 2) / nu)
      (nu • (1 : Mat d) + centeredStreamField omega (U : Set (Vec d)) x) :=
  SuperdiffusionCLT.Section2.CoarseGraining.isEllipticMatrix_of_symmPart_eq_smul_one
    hnu (symmPart_smul_one_add_of_skew
      (centeredStreamField_skew omega (U : Set (Vec d)) x))
    (fun i j => abs_entry_smul_one_add_le hnu (hentry x hx) i j)

/-- **The first assertion of `l.cutoff.approximation`.** Under the manuscript's
summability hypothesis and `0 < ν ≤ 1`, the limiting centered field
`a^U = ν Id + k^U` is uniformly elliptic in `U`, with explicit constants
`lam = ν` and `Lam = (d² (ν + C)² + ν²)/ν` for
`C = √d R ∑_k ‖∇ j_k‖_{L∞(U)}`. No further hypothesis is carried. -/
theorem exists_isEllipticMatrix_smul_one_add_centeredStreamField (U : Domain d)
    {nu : ℝ} (hnu : 0 < nu) (omega : ShellSeq d)
    (hsum : Summable fun k : ℕ =>
      shellDerivLinftyNorm (U : Set (Vec d)) (omega k)) :
    ∃ lam Lam : ℝ, 0 < lam ∧ lam ≤ Lam ∧
      ∀ x ∈ (U : Set (Vec d)),
        IsEllipticMatrix lam Lam
          (nu • (1 : Mat d) + centeredStreamField omega (U : Set (Vec d)) x) := by
  classical
  obtain ⟨R, hR⟩ := Metric.isBounded_iff.mp U.isDomain.isBoundedDomain.isBounded
  set C : ℝ := Real.sqrt d * R * (∑' k : ℕ,
    shellDerivLinftyNorm (U : Set (Vec d)) (omega k)) with hC
  have hEll : ∀ x ∈ (U : Set (Vec d)),
      IsEllipticMatrix nu (((d : ℝ) * (d : ℝ) * (nu + C) ^ 2 + nu ^ 2) / nu)
        (nu • (1 : Mat d) + centeredStreamField omega (U : Set (Vec d)) x) := by
    intro x hx
    refine isEllipticMatrix_smul_one_add_centeredStreamField U hnu omega ?_ x hx
    intro y hy i j
    rw [hC]
    exact abs_centeredStreamField_entry_le U omega hR hsum hy i j
  obtain ⟨x₀, hx₀⟩ := U.nonempty
  exact ⟨nu, ((d : ℝ) * (d : ℝ) * (nu + C) ^ 2 + nu ^ 2) / nu, hnu,
    (hEll x₀ hx₀).2.1, hEll⟩

end

end SuperdiffusionCLT.Section2.Cutoff

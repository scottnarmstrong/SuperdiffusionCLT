/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section5.Principal.LocalizeSwitch
public import SuperdiffusionCLT.Section5.Thresholds.HomogBelowAtScales
public import SuperdiffusionCLT.AKHC61.Carrier.ScalarBlocksB

/-!
# From the finite-volume to the infinite-volume annealed matrix

Displays `e.principal.Ahom.fv` and `e.principal.fv.to.inf`.

* `principal_Ahom_fv`: for a triadic cube `R` of scale `n ≥ 0` (a translate `z + cu_n`), stationarity
  moves the annealed matrix to the origin cube, where it is `diag(shom(cu_n) Id, shom_*^{-1}(cu_n) Id)`.
* `principal_fv_to_inf`: the diagonal sandwich `Ahom^{-1/2} Ahom(z+cu_n) Ahom^{-1/2}` of
  `Ahom_{m-h} = diag(shom Id, shom^{-1} Id)` deviates from the identity by at most
  `C shom_{m-h}^{-2} log²(ν⁻¹ m)`: the two diagonal defects are the two terms of
  `homogenization_below_cutoff`, in the scale form of `homogBelow_at_scales`.
  The matrix inequality is stated in the two-sided quadratic form (as `principal_localize` is):
  `|X·(Ahom(Q) - Ahom) X| ≤ ε X·Ahom X`, equivalent for symmetric matrices to the operator-norm
  bound of the print; the upper half is the `(1 + ε)` form that `e.principal.conditional.upper` uses.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section5

open MeasureTheory Homogenization Homogenization.Book.Ch02
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Annealed

variable {d : ℕ}

/-- `bfAhom_L := diag(shom Id, shom^{-1} Id)`, the infinite-volume matrix of `e.homs.defs`, with
`shom = sigmaBarInfinite`. -/
noncomputable def ahomInfinite [NeZero d] (nu : ℝ) (L : ℕ) (P : ProbabilityMeasure (ShellSeq d)) :
    BlockMat d :=
  blockDiag (sigmaBarInfinite nu L P • (1 : Mat d)) ((sigmaBarInfinite nu L P)⁻¹ • (1 : Mat d))

/-- Stationarity: the annealed matrix of a cube of nonnegative scale is the one of the origin cube
of the same scale. -/
theorem annealedBlockMatrix_cubeSet_eq_originCube [NeZero d] {nu : ℝ} (hnu : 0 < nu) (L : ℕ)
    {P : ProbabilityMeasure (ShellSeq d)} (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P)
    (R : TriadicCube d) (hR : 0 ≤ R.scale) :
    annealedBlockMatrix nu L P (cubeSet R) =
      annealedBlockMatrix nu L P (cubeSet (originCube d R.scale)) := by
  rw [annealedBlockMatrix_eq_ch04 hnu L P R,
    annealedBlockMatrix_eq_ch04 hnu L P (originCube d R.scale)]
  have hP := Book.Ch04.RestrictionLawCarrier.integral_coarseBlockMatrix_entry_cubeSet_eq_originCube_of_stationary
    (restrictionLawCarrier_cutoffLaw hnu L P) (restrictionStationaryLaw_cutoffLaw hPrefix hJ2 nu L)
    R hR
  simp only [Book.Ch04.annealedBlockMatrix]
  congr 1
  · funext i j
    exact hP (Sum.inl i) (Sum.inl j)
  · funext i j
    exact hP (Sum.inl i) (Sum.inr j)
  · funext i j
    exact hP (Sum.inr i) (Sum.inl j)
  · funext i j
    exact hP (Sum.inr i) (Sum.inr j)

/-- **`e.principal.Ahom.fv`**: `bfAhom_L(z + cu_n) = E[bfA_L(z + cu_n)]` is the
diagonal matrix `diag(shom_L(z+cu_n) Id, shom_{L,*}^{-1}(z+cu_n) Id)`, both scalars being those of
the origin cube `cu_n` by stationarity. -/
theorem principal_Ahom_fv [NeZero d] {nu : ℝ} (hnu : 0 < nu) (L : ℕ)
    {P : ProbabilityMeasure (ShellSeq d)} (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P)
    (hJ4 : ShellLawJ4 d P) (n : ℕ) (R : TriadicCube d) (hR : R.scale = (n : ℤ)) :
    annealedBlockMatrix nu L P (cubeSet R) =
      blockDiag (sigmaBarSeq nu L P n • (1 : Mat d)) (sigmaBarStarInvSeq nu L P n • (1 : Mat d)) := by
  have h0 : 0 ≤ R.scale := by rw [hR]; exact Int.natCast_nonneg n
  rw [annealedBlockMatrix_cubeSet_eq_originCube hnu L hPrefix hJ2 R h0, hR]
  exact SuperdiffusionCLT.AKHC61.Carrier.akhc_annealedBlockMatrix_originCube_eq_blockDiag hnu L hJ4 (n : ℤ)

/-- The algebra of the diagonal sandwich: if `|σ⁻¹ a - 1| ≤ ε` and `|σ b - 1| ≤ ε`, then
`|a s + b t - (σ s + σ⁻¹ t)| ≤ ε (σ s + σ⁻¹ t)` for `s, t ≥ 0`. -/
theorem diag_defect_le {σ a b ε s t : ℝ} (hσ : 0 < σ) (ha : |σ⁻¹ * a - 1| ≤ ε)
    (hb : |σ * b - 1| ≤ ε) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    |(a * s + b * t) - (σ * s + σ⁻¹ * t)| ≤ ε * (σ * s + σ⁻¹ * t) := by
  have hσi : 0 < σ⁻¹ := inv_pos.mpr hσ
  have e : (a * s + b * t) - (σ * s + σ⁻¹ * t) =
      (σ * s) * (σ⁻¹ * a - 1) + (σ⁻¹ * t) * (σ * b - 1) := by
    field_simp
    ring
  rw [e]
  have h1 : |(σ * s) * (σ⁻¹ * a - 1)| ≤ (σ * s) * ε := by
    rw [abs_mul, abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left ha (by positivity)
  have h2 : |(σ⁻¹ * t) * (σ * b - 1)| ≤ (σ⁻¹ * t) * ε := by
    rw [abs_mul, abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left hb (by positivity)
  calc _ ≤ |(σ * s) * (σ⁻¹ * a - 1)| + |(σ⁻¹ * t) * (σ * b - 1)| := abs_add_le _ _
    _ ≤ (σ * s) * ε + (σ⁻¹ * t) * ε := add_le_add h1 h2
    _ = ε * (σ * s + σ⁻¹ * t) := by ring

/-- **`e.principal.fv.to.inf`**, in the quadratic form: for a cube `R = z + cu_n`
and every block vector `X`,
`|X·(bfAhom_{m-h}(R) - bfAhom_{m-h}) X| ≤ C shom_{m-h}^{-2} log²(ν⁻¹m) · X·bfAhom_{m-h} X`.
Since `X·bfAhom_{m-h} X = |bfAhom_{m-h}^{1/2} X|²`, this is the print's
`|Ahom^{-1/2} Ahom(R) Ahom^{-1/2} - I| ≤ C shom^{-2} log²(ν⁻¹m)`; the diagonal blocks give two scalar
defects, the two terms of `homogenization_below_cutoff` (`homogBelow_at_scales`). -/
theorem principal_fv_to_inf (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    ∃ C₀ : ℝ, 1 ≤ C₀ ∧ ∀ C : ℝ, C₀ ≤ C →
      ∀ cStar nu K : ℝ, 0 < nu → nu ≤ 1 →
      ∀ (P : ProbabilityMeasure (ShellSeq d))
        (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P),
        ShellLawJ1Restriction d P → ShellLawJ4 d P → ShellLawJ5 d P cStar K hPrefix hJ2 hJ3 →
      ∀ m h n : ℕ, 1 ≤ h → 400 * h ≤ m →
        2 * SuperdiffusionCLT.Frozen.Section4.lNaught C C (3 / 4) cStar nu K ≤ (m : ℝ) →
        n = ⌊(m : ℝ) - h - 100 * Real.logb 3 (nu⁻¹ * m)⌋₊ →
      ∀ R : TriadicCube d, R.scale = (n : ℤ) → ∀ X : BlockVec d,
        |blockVecDot X (blockMatVecMul (annealedBlockMatrix nu (m - h) P (cubeSet R)) X) -
            blockVecDot X (blockMatVecMul (ahomInfinite nu (m - h) P) X)| ≤
          (C * (sigmaBarInfinite nu (m - h) P) ^ (-(2 : ℝ)) *
              Real.log (nu⁻¹ * (m : ℝ)) ^ (2 : ℝ)) *
            blockVecDot X (blockMatVecMul (ahomInfinite nu (m - h) P) X) := by
  obtain ⟨C₀, hC₀, H⟩ := homogBelow_at_scales d hd
  refine ⟨C₀, hC₀, fun C hC cStar nu K hnu hnu1 P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5 m h n hh h400 hm hn
    R hR X => ?_⟩
  have hb := (H C hC cStar nu K hnu hnu1 P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5 m h n hh h400 hm hn).1
  set ε : ℝ := C * (sigmaBarInfinite nu (m - h) P) ^ (-(2 : ℝ)) *
    Real.log (nu⁻¹ * (m : ℝ)) ^ (2 : ℝ) with hε
  have hσ : 0 < sigmaBarInfinite nu (m - h) P :=
    sigmaBarInfinite_pos hnu (m - h) hPrefix hJ2 hJ3 hJ4
  have h1 : |(sigmaBarInfinite nu (m - h) P)⁻¹ * sigmaBarSeq nu (m - h) P n - 1| ≤ ε :=
    le_trans (le_add_of_nonneg_right (abs_nonneg _)) hb
  have h2 : |sigmaBarInfinite nu (m - h) P * sigmaBarStarInvSeq nu (m - h) P n - 1| ≤ ε :=
    le_trans (le_add_of_nonneg_left (abs_nonneg _)) hb
  rw [principal_Ahom_fv hnu (m - h) hPrefix hJ2 hJ4 n R hR]
  obtain ⟨p, q⟩ := X
  unfold ahomInfinite
  rw [blockVecDot_blockMatVecMul_blockDiag_smul_one, blockVecDot_blockMatVecMul_blockDiag_smul_one]
  exact diag_defect_le hσ h1 h2 (vecNormSq_nonneg p) (vecNormSq_nonneg q)

/-! ## Satisfiability -/

/-- `principal_Ahom_fv` is met by the Dirac law at the zero shell sequence (prefix, J2, J4), `d = 2`,
`ν = 1`, `L = 0` and the origin cube of scale `0`. -/
example :
    annealedBlockMatrix (1 : ℝ) 0 (SuperdiffusionCLT.Assumptions.ShellLaw.diracZeroLaw 2)
        (cubeSet (originCube 2 ((0 : ℕ) : ℤ))) =
      blockDiag
        (sigmaBarSeq (1 : ℝ) 0 (SuperdiffusionCLT.Assumptions.ShellLaw.diracZeroLaw 2) 0 •
          (1 : Mat 2))
        (sigmaBarStarInvSeq (1 : ℝ) 0
            (SuperdiffusionCLT.Assumptions.ShellLaw.diracZeroLaw 2) 0 • (1 : Mat 2)) :=
  principal_Ahom_fv one_pos 0
    (SuperdiffusionCLT.Assumptions.ShellLaw.shellLawPrefix_diracZeroLaw le_rfl)
    SuperdiffusionCLT.Assumptions.ShellLaw.shellLawJ2_diracZeroLaw
    SuperdiffusionCLT.Assumptions.ShellLaw.shellLawJ4_diracZeroLaw 0 _ rfl

/-- The non-law hypotheses of `principal_fv_to_inf` are met for any constants: scales `m, h, n`
with a cube `R` of scale `n`. (J5 is not met by the Dirac law, see `Assumptions.ShellLaw.Nonvacuity`;
a nondegenerate law is needed for the whole bundle.) -/
example (C cStar K nu : ℝ) (hnu : 0 < nu) (hnu1 : nu ≤ 1) :
    ∃ m h n : ℕ, 1 ≤ h ∧ 400 * h ≤ m ∧
      2 * SuperdiffusionCLT.Frozen.Section4.lNaught C C (3 / 4) cStar nu K ≤ (m : ℝ) ∧
      n = ⌊(m : ℝ) - h - 100 * Real.logb 3 (nu⁻¹ * m)⌋₊ ∧
      ∃ R : TriadicCube 2, R.scale = (n : ℤ) := by
  obtain ⟨m, h, n, h1, h2, h3, h4⟩ := homogBelow_at_scales_scale_witness C cStar K nu hnu hnu1
  exact ⟨m, h, n, h1, h2, h3, h4, originCube 2 (n : ℤ), rfl⟩

end SuperdiffusionCLT.Section5

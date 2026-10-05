/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Setup.CrudeBounds
public import SuperdiffusionCLT.Section3.Setup.QuenchedLowerBound
public import SuperdiffusionCLT.Section3.Setup.ScaleAssembly

/-!
# The annealed balanced comparison, and the root's localization bridges

The paper (Lemma `l.localization`) converts the quenched
balanced comparison `e.localization.s.star` into the
annealed scalar comparison

`|shom_{L',*}(cu_k) shom_{L,*}^{-1}(cu_k) - 1| ≤ eta_L`,   `e.localization.s.star.annealed.applied`,

with `eta_L = C nu^{-5} L 3^{-(L'-k)}`.  This file carries out that
conversion and then reads off the two localization comparisons which the
root's own proof consumes.

## The conversion

The print's route is: "Taking expectations in the corresponding Loewner
inequalities gives an additive comparison of the annealed lower-right blocks.
Using the scalar form of those blocks together with the crude bound
`shom_{L',*}(cu_k) ≤ C nu^{-2} L` ... this becomes `e.localization.s.star.annealed.applied`."

Here that is:

* the two Loewner inequalities of `e.localization.s.star` are read at the first
  coordinate vector, which gives the pointwise scalar sandwich
  `(1 - X) s_{L',*}^{-1}(cu_k) ≤ s_{L,*}^{-1}(cu_k) ≤ (1 + X) s_{L',*}^{-1}(cu_k)`
  (`diag_le_of_matLoewnerLE`);
* the quenched crude ellipticity bound `s_{L',*}^{-1}(cu_k) ≤ nu⁻¹ Id`
  (`matLoewnerLE_sigmaStarInvCoarse_cutoffCube`, the sentence before
  `e.v.ky.energy`) turns the sandwich into `|s_{L,*}^{-1} - s_{L',*}^{-1}| ≤ nu⁻¹ |X|`;
* the first absolute moment of the `Γ₁` witness costs one factor
  `gammaMomentConst 1` (`hasGammaMomentGrowthWith_of_isBigO_gammaSigma` at
  `p = 1`), so the two annealed blocks differ by at most
  `gammaMomentConst 1 * C nu^{-3} 3^{-(L'-k)}`; and
* the crude lower bound `shom_{L',*}^{-1}(cu_k) ≥ c nu^2 L^{-1}` of the paper
  (`crude_lower_bound`) divides that difference, which produces
  exactly the printed power `nu^{-5} L`.  This is the print's own remark that
  "the extra factor of `nu^{-1}` is harmless and leaves room for the conversion
  from the balanced Loewner comparison to the scalar inverse-block ratio".

## The two localization bridges

Applied at the cutoff pair `(ell, L')` on `cu_n` and at `(L', L)` on `cu_m`,
together with the monotonicity of `k ↦ shom_{L',*}^{-1}(cu_k)` (subadditivity,
`antitone_sigmaBarStarInvSeq`), the conversion gives the two comparisons

`shom_{ell,*}(cu_n) ≤ 2 shom_{L',*}(cu_n)`  and  `(1/4) shom_{L',*}(cu_n) ≤ shom_{L,*}(cu_m)`,

which are `hLocal1` and `hLocal2` of `Terms.sstar_lower_bound_of_terms`, in the
exact shapes the root theorem consumes them.

## What is carried

The conclusion of `Frozen.Section2.cutoff_localization` (`e.localization.s.star`)
is never imported; its third and fourth Loewner conjuncts are copied as the
explicit hypothesis `hLoc`, with the binders of that statement (`U : Domain d`
with `U ⊆ cu_n`) kept, so that `hLoc` is its first component with the two
`sigmaCoarse` conjuncts dropped.  The constant is required positive; the
existential constant `∃ C` there may always be enlarged to a positive one.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Setup

open Homogenization MeasureTheory
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.CoarseGraining
open SuperdiffusionCLT.Section2.Cutoff

noncomputable section

variable {d : ℕ}

/-! ## Elementary steps -/

/-- The two-sided comparison `(1-x) a ≤ b ≤ (1+x) a` with `a ≥ 0` gives
`|b - a| ≤ |x| a`.  This is the scalar content of the balanced Loewner
comparison after reading it at one coordinate vector. -/
private theorem abs_sub_le_of_sandwich {a b x : ℝ} (ha : 0 ≤ a)
    (h1 : (1 - x) * a ≤ b) (h2 : b ≤ (1 + x) * a) : |b - a| ≤ |x| * a := by
  have hx1 : x * a ≤ |x| * a := mul_le_mul_of_nonneg_right (le_abs_self x) ha
  rw [abs_le]
  exact ⟨by linarith only [h1, hx1], by linarith only [h2, hx1]⟩

/-- `nu^{-2} · nu^{-1} · (nu^2)^{-1} = nu^{-5}`: the accounting of the print's
`eta_L = C nu^{-5} L 3^{-(L'-m)}`.  The three factors are, in
order, the rate of `e.localization.s.star`, the quenched crude ellipticity
bound `s_{L',*}^{-1} ≤ nu^{-1} Id` and the crude lower bound
`shom_{L',*}^{-1} ≥ c nu^2 L^{-1}`. -/
private theorem nu_rpow_neg_five {nu : ℝ} (hnu : 0 < nu) :
    nu ^ (-(2 : ℝ)) * nu⁻¹ * (nu ^ (2 : ℕ))⁻¹ = nu ^ (-(5 : ℝ)) := by
  have h1 : nu⁻¹ = nu ^ (-(1 : ℝ)) := by
    rw [Real.rpow_neg hnu.le, Real.rpow_one]
  have h2 : (nu ^ (2 : ℕ))⁻¹ = nu ^ (-(2 : ℝ)) := by
    rw [Real.rpow_neg hnu.le, show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num,
      Real.rpow_natCast]
  rw [h1, h2, ← Real.rpow_add hnu, ← Real.rpow_add hnu]
  norm_num

/-- `eta_L ≥ 0`. -/
theorem localizationEta_nonneg {Ceta nu : ℝ} (hCeta : 0 ≤ Ceta) (hnu : 0 < nu)
    (L k : ℕ) : 0 ≤ localizationEta Ceta nu L k := by
  rw [localizationEta]
  exact mul_nonneg (mul_nonneg (mul_nonneg hCeta (Real.rpow_nonneg hnu.le _))
    (Nat.cast_nonneg _)) (Real.rpow_nonneg (by norm_num) _)

/-- `eta_L` decreases as the gap `k` grows: `3^{-k}` is antitone. -/
theorem localizationEta_mono_gap {Ceta nu : ℝ} (hCeta : 0 ≤ Ceta) (hnu : 0 < nu)
    (L : ℕ) {k k' : ℕ} (hkk : k ≤ k') :
    localizationEta Ceta nu L k' ≤ localizationEta Ceta nu L k := by
  have hkkR : (k : ℝ) ≤ (k' : ℝ) := by exact_mod_cast hkk
  have hpow : (3 : ℝ) ^ (-(k' : ℝ)) ≤ (3 : ℝ) ^ (-(k : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith only [hkkR])
  have hfac : (0 : ℝ) ≤ Ceta * nu ^ (-(5 : ℝ)) * (L : ℝ) :=
    mul_nonneg (mul_nonneg hCeta (Real.rpow_nonneg hnu.le _)) (Nat.cast_nonneg _)
  rw [localizationEta, localizationEta]
  exact mul_le_mul_of_nonneg_left hpow hfac

/-- `eta_L` is monotone in the cutoff scale `L` which appears linearly in it. -/
theorem localizationEta_mono_scale {Ceta nu : ℝ} (hCeta : 0 ≤ Ceta) (hnu : 0 < nu)
    {L N : ℕ} (hLN : L ≤ N) (k : ℕ) :
    localizationEta Ceta nu L k ≤ localizationEta Ceta nu N k := by
  have hLNR : (L : ℝ) ≤ (N : ℝ) := by exact_mod_cast hLN
  have hfac : (0 : ℝ) ≤ Ceta * nu ^ (-(5 : ℝ)) :=
    mul_nonneg hCeta (Real.rpow_nonneg hnu.le _)
  have h3 : (0 : ℝ) ≤ (3 : ℝ) ^ (-(k : ℝ)) := Real.rpow_nonneg (by norm_num) _
  rw [localizationEta, localizationEta]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hLNR hfac) h3

/-! ## The annealed conversion -/

section Conversion

variable [NeZero d] {nu CL Ceta : ℝ} {P : ProbabilityMeasure (ShellSeq d)}
  {k LPrime L : ℕ}

/-- **`e.localization.s.star.annealed.applied`**,
at the cutoff pair `(L', L)` on the cube `cu_k`:

`|shom_{L',*}(cu_k) shom_{L,*}^{-1}(cu_k) - 1| ≤ eta_L`,
`eta_L = Ceta nu^{-5} L 3^{-(L'-k)}`.

`hLoc` is the third and fourth Loewner conjunct of the first component of the
conclusion of `Frozen.Section2.cutoff_localization` at the
triple `(m, n, L) = (L', k, L)`, with its domain binders; `Ceta`
absorbs its constant, the first-moment factor of the `Γ₁` class
and the constant of the crude lower bound `crude_lower_bound`. -/
theorem annealed_cutoff_localization
    (hnu : 0 < nu) (hnu1 : nu ≤ 1) (hCL : 0 < CL) (hL : 1 ≤ L)
    (hLPL : LPrime ≤ L)
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P)
    (hJ4 : ShellLawJ4 d P)
    (hCeta : IndependentSums.gammaMomentConst 1 * CL * (crudeLowerConst d)⁻¹ ≤ Ceta)
    (hLoc : ∀ U : Book.Ch02.Domain d,
        (U : Set (Vec d)) ⊆ openCubeSet (originCube d (k : ℤ)) →
        ∃ X : ShellSeq d → ℝ,
          Measurable X ∧
          IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma 1) X
              (CL * nu ^ (-(2 : ℝ)) * (3 : ℝ) ^ (-((LPrime - k : ℕ) : ℝ))) ∧
            ∀ omega : ShellSeq d,
              MatLoewnerLE
                  ((1 - X omega) • sigmaStarInvCoarse (U : Set (Vec d))
                    (coefficientCutoff nu omega LPrime).toCoeffField)
                  (sigmaStarInvCoarse (U : Set (Vec d))
                    (coefficientCutoff nu omega L).toCoeffField) ∧
                MatLoewnerLE
                  (sigmaStarInvCoarse (U : Set (Vec d))
                    (coefficientCutoff nu omega L).toCoeffField)
                  ((1 + X omega) • sigmaStarInvCoarse (U : Set (Vec d))
                    (coefficientCutoff nu omega LPrime).toCoeffField)) :
    |sigmaBarStarScalar nu LPrime P (cubeSet (originCube d (k : ℤ))) *
        sigmaBarStarInvScalar nu L P (cubeSet (originCube d (k : ℤ))) - 1| ≤
      localizationEta Ceta nu L (LPrime - k) := by
  classical
  obtain ⟨X, hXmeas, hXO, hXLoew⟩ :=
    hLoc (Book.Ch02.cubeDomain (originCube d (k : ℤ)))
      (Book.Ch02.cubeDomain_coe _).subset
  simp only [Book.Ch02.cubeDomain_coe] at hXLoew
  have hLR : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
  have hcpos := crudeLowerConst_pos d
  -- the quenched scalars
  have hgpos : ∀ (j : ℕ) (omega : ShellSeq d),
      0 < sigmaStarInvCoarse (openCubeSet (originCube d (k : ℤ)))
        (coefficientCutoff nu omega j).toCoeffField 0 0 := by
    intro j omega
    have ha := aeLocallyUniformlyEllipticField_coefficientCutoff hnu omega j
    have h := Book.Ch02.sigmaStarInvCoarse_posDef
      (Book.Ch02.cubeDomain (originCube d (k : ℤ)))
      ((Book.Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField
        (coefficientCutoff nu omega j) ha).coeffOn (originCube d (k : ℤ)))
    rw [← sigmaStarInvCoarse_toCoeffField, Book.Ch02.cubeDomain_coe] at h
    exact Book.Ch04.matrix_posDef_diag_pos h 0
  have hgup : ∀ omega : ShellSeq d,
      sigmaStarInvCoarse (openCubeSet (originCube d (k : ℤ)))
        (coefficientCutoff nu omega LPrime).toCoeffField 0 0 ≤ nu⁻¹ := by
    intro omega
    have h := matLoewnerLE_sigmaStarInvCoarse_cutoffCube hnu omega LPrime
      (originCube d (k : ℤ))
    have h0 := diag_le_of_matLoewnerLE h 0
    simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at h0
    exact h0
  have hint : ∀ j : ℕ, Integrable (fun omega : ShellSeq d ↦
      sigmaStarInvCoarse (openCubeSet (originCube d (k : ℤ)))
        (coefficientCutoff nu omega j).toCoeffField 0 0) P.toMeasure :=
    fun j ↦ integrable_sigmaStarInvCoarse_apply hnu j hPrefix hJ2 hJ3 hJ4
      (originCube d (k : ℤ)) 0 0
  have heq : ∀ j : ℕ, sigmaBarStarInvScalar nu j P (cubeSet (originCube d (k : ℤ))) =
      ∫ omega, sigmaStarInvCoarse (openCubeSet (originCube d (k : ℤ)))
        (coefficientCutoff nu omega j).toCoeffField 0 0 ∂P.toMeasure :=
    fun j ↦ sigmaBarStarInv_eq_integral_sigmaStarInvCoarse hnu j P
      (originCube d (k : ℤ)) 0 0
  -- the first absolute moment of the `Γ₁` witness
  have hKpos : 0 < CL * nu ^ (-(2 : ℝ)) *
      (3 : ℝ) ^ (-((LPrime - k : ℕ) : ℝ)) := by positivity
  have hmom := IndependentSums.hasGammaMomentGrowthWith_of_isBigO_gammaSigma
    (μ := P.toMeasure) one_pos hKpos hXmeas.aemeasurable hXO
  have hm1 := hmom (le_refl (1 : ℝ))
  have hXint : Integrable (fun w ↦ |X w|) P.toMeasure := by
    simpa only [Real.rpow_one] using hm1.1
  have hXbd : ∫ w, |X w| ∂P.toMeasure ≤ IndependentSums.gammaMomentConst 1 *
      (CL * nu ^ (-(2 : ℝ)) * (3 : ℝ) ^ (-((LPrime - k : ℕ) : ℝ))) := by
    simpa only [Real.rpow_one, Real.one_rpow, mul_one] using hm1.2
  -- the pointwise comparison
  have hpt : ∀ omega : ShellSeq d,
      |sigmaStarInvCoarse (openCubeSet (originCube d (k : ℤ)))
            (coefficientCutoff nu omega L).toCoeffField 0 0 -
          sigmaStarInvCoarse (openCubeSet (originCube d (k : ℤ)))
            (coefficientCutoff nu omega LPrime).toCoeffField 0 0| ≤
        nu⁻¹ * |X omega| := by
    intro omega
    have h1 := diag_le_of_matLoewnerLE (hXLoew omega).1 0
    have h2 := diag_le_of_matLoewnerLE (hXLoew omega).2 0
    simp only [Matrix.smul_apply, smul_eq_mul] at h1 h2
    have hsand := abs_sub_le_of_sandwich (hgpos LPrime omega).le h1 h2
    have hmul := mul_le_mul_of_nonneg_left (hgup omega) (abs_nonneg (X omega))
    calc |sigmaStarInvCoarse (openCubeSet (originCube d (k : ℤ)))
              (coefficientCutoff nu omega L).toCoeffField 0 0 -
            sigmaStarInvCoarse (openCubeSet (originCube d (k : ℤ)))
              (coefficientCutoff nu omega LPrime).toCoeffField 0 0|
        ≤ |X omega| * sigmaStarInvCoarse (openCubeSet (originCube d (k : ℤ)))
              (coefficientCutoff nu omega LPrime).toCoeffField 0 0 := hsand
      _ ≤ |X omega| * nu⁻¹ := hmul
      _ = nu⁻¹ * |X omega| := by ring
  -- integrate
  have hdiff : |sigmaBarStarInvScalar nu L P (cubeSet (originCube d (k : ℤ))) -
      sigmaBarStarInvScalar nu LPrime P (cubeSet (originCube d (k : ℤ)))| ≤
      nu⁻¹ * (IndependentSums.gammaMomentConst 1 *
        (CL * nu ^ (-(2 : ℝ)) * (3 : ℝ) ^ (-((LPrime - k : ℕ) : ℝ)))) := by
    rw [heq L, heq LPrime, ← integral_sub (hint L) (hint LPrime)]
    have hstep1 := MeasureTheory.abs_integral_le_integral_abs
      (μ := P.toMeasure)
      (f := fun omega : ShellSeq d ↦
        sigmaStarInvCoarse (openCubeSet (originCube d (k : ℤ)))
          (coefficientCutoff nu omega L).toCoeffField 0 0 -
        sigmaStarInvCoarse (openCubeSet (originCube d (k : ℤ)))
          (coefficientCutoff nu omega LPrime).toCoeffField 0 0)
    have hstep2 : ∫ omega, |sigmaStarInvCoarse (openCubeSet (originCube d (k : ℤ)))
          (coefficientCutoff nu omega L).toCoeffField 0 0 -
        sigmaStarInvCoarse (openCubeSet (originCube d (k : ℤ)))
          (coefficientCutoff nu omega LPrime).toCoeffField 0 0| ∂P.toMeasure ≤
        ∫ omega, nu⁻¹ * |X omega| ∂P.toMeasure :=
      integral_mono ((hint L).sub (hint LPrime)).abs
        (hXint.const_mul _) hpt
    have hstep3 : ∫ omega, nu⁻¹ * |X omega| ∂P.toMeasure =
        nu⁻¹ * ∫ omega, |X omega| ∂P.toMeasure := integral_const_mul _ _
    have hstep4 := mul_le_mul_of_nonneg_left hXbd (inv_pos.2 hnu).le
    linarith only [hstep1, hstep2, hstep3, hstep4]
  -- the crude lower bound divides
  have hApos : 0 < sigmaBarStarInvScalar nu LPrime P
      (cubeSet (originCube d (k : ℤ))) :=
    sigmaBarStarInvScalar_pos_cutoff hnu LPrime hPrefix hJ2 hJ3 hJ4 (k : ℤ)
  have hcrude : crudeLowerConst d * nu ^ (2 : ℕ) * (L : ℝ)⁻¹ ≤
      sigmaBarStarInvScalar nu LPrime P (cubeSet (originCube d (k : ℤ))) := by
    have h := crude_lower_bound (d := d) hnu LPrime hPrefix hJ2 hJ3 hJ4 hnu1
      (n := k) hL hLPL
    simpa only [sigmaBarStarInvSeq] using h
  have hlowpos : (0 : ℝ) < crudeLowerConst d * nu ^ (2 : ℕ) * (L : ℝ)⁻¹ := by
    have : (0 : ℝ) < (L : ℝ)⁻¹ := by positivity
    positivity
  have hAinv : (sigmaBarStarInvScalar nu LPrime P
      (cubeSet (originCube d (k : ℤ))))⁻¹ ≤
      (crudeLowerConst d * nu ^ (2 : ℕ) * (L : ℝ)⁻¹)⁻¹ :=
    (inv_le_inv₀ hApos hlowpos).2 hcrude
  -- the ratio
  have hratio : sigmaBarStarScalar nu LPrime P (cubeSet (originCube d (k : ℤ))) *
      sigmaBarStarInvScalar nu L P (cubeSet (originCube d (k : ℤ))) - 1 =
      (sigmaBarStarInvScalar nu LPrime P (cubeSet (originCube d (k : ℤ))))⁻¹ *
        (sigmaBarStarInvScalar nu L P (cubeSet (originCube d (k : ℤ))) -
          sigmaBarStarInvScalar nu LPrime P (cubeSet (originCube d (k : ℤ)))) := by
    rw [sigmaBarStarScalar_eq_inv hnu LPrime hJ4 (k : ℤ) hApos]
    field_simp
  rw [hratio, abs_mul, abs_of_pos (inv_pos.2 hApos)]
  have hbound := mul_le_mul hAinv hdiff (abs_nonneg _) (by positivity)
  refine le_trans hbound ?_
  -- the arithmetic of `eta_L`
  have hLne : (L : ℝ) ≠ 0 := by linarith only [hLR]
  have harith : (crudeLowerConst d * nu ^ (2 : ℕ) * (L : ℝ)⁻¹)⁻¹ *
      (nu⁻¹ * (IndependentSums.gammaMomentConst 1 *
        (CL * nu ^ (-(2 : ℝ)) * (3 : ℝ) ^ (-((LPrime - k : ℕ) : ℝ))))) =
      IndependentSums.gammaMomentConst 1 * CL * (crudeLowerConst d)⁻¹ *
        nu ^ (-(5 : ℝ)) * (L : ℝ) * (3 : ℝ) ^ (-((LPrime - k : ℕ) : ℝ)) := by
    rw [← nu_rpow_neg_five hnu]
    field_simp
  rw [harith, localizationEta]
  have hnn : (0 : ℝ) ≤ nu ^ (-(5 : ℝ)) * (L : ℝ) *
      (3 : ℝ) ^ (-((LPrime - k : ℕ) : ℝ)) := by positivity
  have hstep := mul_le_mul_of_nonneg_right hCeta hnn
  linarith only [hstep]

end Conversion

/-! ## The two localization comparisons -/

section Bridges

variable [NeZero d] {nu eta : ℝ} {P : ProbabilityMeasure (ShellSeq d)}

/-- From `b ≤ 2a` with `a, b > 0` we get `a⁻¹ ≤ 2 b⁻¹`: the passage between
the annealed inverse block and the annealed running diffusivity. -/
private theorem inv_le_two_mul_inv {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (h : b ≤ 2 * a) : a⁻¹ ≤ 2 * b⁻¹ := by
  have hmul := mul_le_mul_of_nonneg_right h
    (mul_pos (inv_pos.2 ha) (inv_pos.2 hb)).le
  rw [show b * (a⁻¹ * b⁻¹) = a⁻¹ * (b * b⁻¹) by ring, mul_inv_cancel₀ hb.ne',
    mul_one, show 2 * a * (a⁻¹ * b⁻¹) = 2 * b⁻¹ * (a * a⁻¹) by ring,
    mul_inv_cancel₀ ha.ne', mul_one] at hmul
  exact hmul

/-- **The generalized transfer of a cutoff**: the annealed comparison
`|shom_{R,*}(cu_{n}) shom_{L,*}^{-1}(cu_n) - 1| ≤ eta` with `eta ≤ c - 1` gives
`shom_{L,*}^{-1}(cu_n) ≤ c shom_{R,*}^{-1}(cu_n)`.  At `c = 2` this is
`sigmaBarStarInvScalar_transfer_cutoff`; the root's own proof also uses it at
`c = 4`. -/
theorem sigmaBarStarInvScalar_le_const_mul_of_localization {c : ℝ} {R L n0 : ℕ}
    (hnu : 0 < nu) (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P)
    (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P) (hEta : eta ≤ c - 1)
    (hLocal : |sigmaBarStarScalar nu R P (cubeSet (originCube d (n0 : ℤ))) *
        sigmaBarStarInvScalar nu L P (cubeSet (originCube d (n0 : ℤ))) - 1| ≤ eta) :
    sigmaBarStarInvScalar nu L P (cubeSet (originCube d (n0 : ℤ))) ≤
      c * sigmaBarStarInvScalar nu R P (cubeSet (originCube d (n0 : ℤ))) := by
  have hSR : 0 < sigmaBarStarInvScalar nu R P (cubeSet (originCube d (n0 : ℤ))) :=
    sigmaBarStarInvScalar_pos_cutoff hnu R hPrefix hJ2 hJ3 hJ4 (n0 : ℤ)
  have hbound := (abs_le.1 hLocal).2
  have hprod : sigmaBarStarScalar nu R P (cubeSet (originCube d (n0 : ℤ))) *
      sigmaBarStarInvScalar nu L P (cubeSet (originCube d (n0 : ℤ))) ≤ c := by
    linarith only [hbound, hEta]
  rw [sigmaBarStarScalar_eq_inv hnu R hJ4 (n0 : ℤ) hSR] at hprod
  have hmul := mul_le_mul_of_nonneg_left hprod hSR.le
  rw [← mul_assoc, mul_inv_cancel₀ hSR.ne', one_mul] at hmul
  linarith only [hmul]

/-- **`hLocal1`**:
`shom_{ell,*}(cu_n) ≤ 2 shom_{L',*}(cu_n)`, in the exact shape
`Terms.sstar_lower_bound_of_terms` consumes it.

`hcomp` is `e.localization.s.star.annealed.applied` at the cutoff pair
`(ell, L')` on `cu_n`, the conclusion of `annealed_cutoff_localization`; `hEta`
is the print's "after increasing `K(d)` if necessary". -/
theorem localization_bridge_one {n ell LPrime : ℕ}
    (hnu : 0 < nu) (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P)
    (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P) (hEta : eta ≤ 1)
    (hcomp : |sigmaBarStarScalar nu ell P (cubeSet (originCube d (n : ℤ))) *
        sigmaBarStarInvScalar nu LPrime P (cubeSet (originCube d (n : ℤ))) - 1| ≤
      eta) :
    (sigmaBarStarInvSeq nu ell P n)⁻¹ ≤ 2 * (sigmaBarStarInvSeq nu LPrime P n)⁻¹ := by
  have hell : 0 < sigmaBarStarInvScalar nu ell P (cubeSet (originCube d (n : ℤ))) :=
    sigmaBarStarInvScalar_pos_cutoff hnu ell hPrefix hJ2 hJ3 hJ4 (n : ℤ)
  have hLP : 0 < sigmaBarStarInvScalar nu LPrime P
      (cubeSet (originCube d (n : ℤ))) :=
    sigmaBarStarInvScalar_pos_cutoff hnu LPrime hPrefix hJ2 hJ3 hJ4 (n : ℤ)
  have hkey := sigmaBarStarInvScalar_le_const_mul_of_localization (c := 2)
    hnu hPrefix hJ2 hJ3 hJ4 (by linarith only [hEta]) hcomp
  simpa only [sigmaBarStarInvSeq] using inv_le_two_mul_inv hell hLP hkey

/-- **`hLocal2`**:
`(1/4) shom_{L',*}(cu_n) ≤ shom_{L,*}(cu_m)`, in the exact shape
`Terms.sstar_lower_bound_of_terms` consumes it.

The print's two ingredients are the balanced comparison at the cutoff pair
`(L', L)` on `cu_m` — `hcomp`, the conclusion of
`annealed_cutoff_localization` — and the monotonicity of
`k ↦ shom_{L',*}^{-1}(cu_k)` in `k` (subadditivity,
`antitone_sigmaBarStarInvSeq`), which for `n ≤ m` gives
`shom_{L',*}^{-1}(cu_m) ≤ shom_{L',*}^{-1}(cu_n)`. -/
theorem localization_bridge_two {n m LPrime L : ℕ}
    (hnu : 0 < nu) (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P)
    (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P) (hnm : n ≤ m) (hEta : eta ≤ 3)
    (hcomp : |sigmaBarStarScalar nu LPrime P (cubeSet (originCube d (m : ℤ))) *
        sigmaBarStarInvScalar nu L P (cubeSet (originCube d (m : ℤ))) - 1| ≤
      eta) :
    (1 / 4 : ℝ) * (sigmaBarStarInvSeq nu LPrime P n)⁻¹ ≤
      sigmaBarStarScalar nu L P (cubeSet (originCube d (m : ℤ))) := by
  have hLm : 0 < sigmaBarStarInvScalar nu L P (cubeSet (originCube d (m : ℤ))) :=
    sigmaBarStarInvScalar_pos_cutoff hnu L hPrefix hJ2 hJ3 hJ4 (m : ℤ)
  have hLPn : 0 < sigmaBarStarInvScalar nu LPrime P
      (cubeSet (originCube d (n : ℤ))) :=
    sigmaBarStarInvScalar_pos_cutoff hnu LPrime hPrefix hJ2 hJ3 hJ4 (n : ℤ)
  have hkey := sigmaBarStarInvScalar_le_const_mul_of_localization (c := 4)
    hnu hPrefix hJ2 hJ3 hJ4 (by linarith only [hEta]) hcomp
  have hmono : sigmaBarStarInvSeq nu LPrime P m ≤ sigmaBarStarInvSeq nu LPrime P n :=
    antitone_sigmaBarStarInvSeq hnu LPrime hPrefix hJ2 hJ3 hJ4 hnm
  have hmono' : sigmaBarStarInvScalar nu LPrime P (cubeSet (originCube d (m : ℤ))) ≤
      sigmaBarStarInvScalar nu LPrime P (cubeSet (originCube d (n : ℤ))) := by
    simpa only [sigmaBarStarInvSeq] using hmono
  have hfour : sigmaBarStarInvScalar nu L P (cubeSet (originCube d (m : ℤ))) ≤
      4 * sigmaBarStarInvScalar nu LPrime P (cubeSet (originCube d (n : ℤ))) := by
    linarith only [hkey, hmono']
  rw [sigmaBarStarScalar_eq_inv hnu L hJ4 (m : ℤ) hLm]
  have hpos4 : (0 : ℝ) < 4 * sigmaBarStarInvScalar nu LPrime P
      (cubeSet (originCube d (n : ℤ))) := by linarith only [hLPn]
  have hinv := (inv_le_inv₀ hpos4 hLm).2 hfour
  have hval : (4 * sigmaBarStarInvScalar nu LPrime P
      (cubeSet (originCube d (n : ℤ))))⁻¹ =
      (1 / 4 : ℝ) * (sigmaBarStarInvScalar nu LPrime P
        (cubeSet (originCube d (n : ℤ))))⁻¹ := by
    rw [mul_inv]
    norm_num
  rw [hval] at hinv
  simpa only [sigmaBarStarInvSeq] using hinv

end Bridges

/-! ## The two quenched-conjunct inputs at the pair `(R, L)` -/

section Quenched

variable [NeZero d] {nu CL Ceta : ℝ} {P : ProbabilityMeasure (ShellSeq d)} {m L : ℕ}

/-- **`hLocal` of `sstar_lower_bound_quenched`**: the annealed comparison
`e.localization.s.star.annealed.applied` at the cutoff pair `(R, L)` on
`cu_{n₀}`, with `R = 2n₀` and `n₀ = ⌊m/2⌋`, so that the gap `R - n₀` is `n₀`
and the error is `Ceta nu^{-5} L 3^{-n₀}`.

`hLoc` is the third and fourth Loewner conjunct of the first component of the
conclusion of `Frozen.Section2.cutoff_localization`, at the
triple `(m, n, L) = (R, n₀, L)`. -/
theorem quenched_annealed_localization
    (hnu : 0 < nu) (hnu1 : nu ≤ 1) (hCL : 0 < CL) (hL : 1 ≤ L) (hmL : m ≤ L)
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P)
    (hJ4 : ShellLawJ4 d P)
    (hCeta : IndependentSums.gammaMomentConst 1 * CL * (crudeLowerConst d)⁻¹ ≤ Ceta)
    (hLoc : ∀ U : Book.Ch02.Domain d,
        (U : Set (Vec d)) ⊆
            openCubeSet (originCube d ((quenchedInnerScale m : ℕ) : ℤ)) →
        ∃ X : ShellSeq d → ℝ,
          Measurable X ∧
          IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma 1) X
              (CL * nu ^ (-(2 : ℝ)) *
                (3 : ℝ) ^ (-((quenchedCutoffScale m - quenchedInnerScale m : ℕ) : ℝ))) ∧
            ∀ omega : ShellSeq d,
              MatLoewnerLE
                  ((1 - X omega) • sigmaStarInvCoarse (U : Set (Vec d))
                    (coefficientCutoff nu omega (quenchedCutoffScale m)).toCoeffField)
                  (sigmaStarInvCoarse (U : Set (Vec d))
                    (coefficientCutoff nu omega L).toCoeffField) ∧
                MatLoewnerLE
                  (sigmaStarInvCoarse (U : Set (Vec d))
                    (coefficientCutoff nu omega L).toCoeffField)
                  ((1 + X omega) • sigmaStarInvCoarse (U : Set (Vec d))
                    (coefficientCutoff nu omega
                      (quenchedCutoffScale m)).toCoeffField)) :
    |sigmaBarStarScalar nu (quenchedCutoffScale m) P
          (cubeSet (originCube d ((quenchedInnerScale m : ℕ) : ℤ))) *
        sigmaBarStarInvScalar nu L P
          (cubeSet (originCube d ((quenchedInnerScale m : ℕ) : ℤ))) - 1| ≤
      Ceta * nu ^ (-(5 : ℝ)) * (L : ℝ) *
        (3 : ℝ) ^ (-((quenchedInnerScale m : ℕ) : ℝ)) := by
  have hRL : quenchedCutoffScale m ≤ L := by
    have h := quenchedInnerScale_le m
    simp only [quenchedCutoffScale, quenchedInnerScale] at h ⊢
    omega
  have hgap : quenchedCutoffScale m - quenchedInnerScale m = quenchedInnerScale m := by
    simp only [quenchedCutoffScale]
    omega
  have h := annealed_cutoff_localization (k := quenchedInnerScale m)
    (LPrime := quenchedCutoffScale m) (L := L) hnu hnu1 hCL hL hRL hPrefix hJ2 hJ3
    hJ4 hCeta hLoc
  rwa [hgap, localizationEta] at h

/-- **`hEta` of `sstar_lower_bound_quenched`**: the localization
error at the pair `(R, L)` on `cu_{n₀}` is absorbed into the constant.  This is
`localization_error_le_one` at `k = n₀`; the two thresholds are the print's
"after increasing the lower threshold in `e.L.vs.nu`". -/
theorem quenched_localization_eta_le_one
    (hnu : 0 < nu) (hnu1 : nu ≤ 1) (hL : 1 ≤ L) (hCeta : 0 ≤ Ceta)
    (hCT : Ceta ≤ nu⁻¹ * (L : ℝ))
    (hk : 6 * Real.log (nu⁻¹ * (L : ℝ)) ≤
      ((quenchedInnerScale m : ℕ) : ℝ) * Real.log 3) :
    Ceta * nu ^ (-(5 : ℝ)) * (L : ℝ) *
        (3 : ℝ) ^ (-((quenchedInnerScale m : ℕ) : ℝ)) ≤ 1 :=
  localization_error_le_one hnu hnu1 hL hCeta hCT hk

end Quenched

/-! ## `e.pigeon.scalar` at the cutoff `L'` -/

section PigeonScalar

variable [NeZero d] {nu delta eta : ℝ} {P : ProbabilityMeasure (ShellSeq d)}

/-- From `|a⁻¹ b - 1| ≤ c` with `a > 0`: the two-sided form. -/
private theorem sandwich_of_abs_inv_mul_sub_one {a b c : ℝ} (ha : 0 < a)
    (h : |a⁻¹ * b - 1| ≤ c) : (1 - c) * a ≤ b ∧ b ≤ (1 + c) * a := by
  obtain ⟨h1, h2⟩ := abs_le.1 h
  have hkey : a * (a⁻¹ * b - 1) = b - a := by field_simp
  have hA := mul_le_mul_of_nonneg_left h1 ha.le
  have hB := mul_le_mul_of_nonneg_left h2 ha.le
  rw [hkey] at hA hB
  exact ⟨by linarith only [hA], by linarith only [hB]⟩

/-- From `|a' - a| ≤ c a` with `a > 0`: the ratio form. -/
private theorem abs_inv_mul_sub_one_of_abs_sub {a a' c : ℝ} (ha : 0 < a)
    (h : |a' - a| ≤ c * a) : |a⁻¹ * a' - 1| ≤ c := by
  have hrw : a⁻¹ * a' - 1 = a⁻¹ * (a' - a) := by field_simp
  have h2 : a⁻¹ * (c * a) = c := by field_simp
  rw [hrw, abs_mul, abs_of_pos (inv_pos.2 ha)]
  calc a⁻¹ * |a' - a| ≤ a⁻¹ * (c * a) :=
        mul_le_mul_of_nonneg_left h (inv_pos.2 ha).le
    _ = c := h2

/-- The real-arithmetic core of the passage from cutoff `L` to cutoff `L'` in
`e.pigeon.scalar`: `a, a'` are the two cutoff-`L'` inverse blocks and `b, b'`
the two cutoff-`L` ones, at the scales `m` and `m − 2h`. -/
private theorem pigeon_scalar_arith {a a' b b' delta eta : ℝ}
    (ha : 0 < a) (hdelta : 0 ≤ delta) (hdelta1 : delta ≤ 1) (heta : 0 ≤ eta)
    (heta4 : eta ≤ 1 / 4)
    (hm2 : b ≤ (1 + eta) * a) (hm1 : (1 - eta) * a ≤ b)
    (hk1 : (1 - eta) * a' ≤ b') (hk2 : b' ≤ (1 + eta) * a')
    (hpig : b' ≤ (1 + delta) * b) (hmono : b ≤ b') :
    |a' - a| ≤ (delta + 6 * eta) * a := by
  have hposEtaN : (0 : ℝ) < 1 - eta := by linarith only [heta4]
  have hposEtaP : (0 : ℝ) < 1 + eta := by linarith only [heta]
  have hde : delta * eta ≤ eta := by
    have := mul_le_mul_of_nonneg_right hdelta1 heta
    linarith only [this]
  have hee : eta * eta ≤ 1 / 4 * eta := mul_le_mul_of_nonneg_right heta4 heta
  have hprod : (2 * delta * eta + 6 * (eta * eta)) * a ≤ 4 * eta * a := by
    have hlin : 2 * delta * eta + 6 * (eta * eta) ≤ 4 * eta := by
      linarith only [hde, hee, heta]
    exact mul_le_mul_of_nonneg_right hlin ha.le
  -- the upper half
  have hA : (1 - eta) * a' ≤ (1 + delta) * ((1 + eta) * a) :=
    le_trans hk1 (le_trans hpig
      (mul_le_mul_of_nonneg_left hm2 (by linarith only [hdelta])))
  have hB : (1 - eta) * (a' - a) ≤ (1 - eta) * ((delta + 6 * eta) * a) := by
    linarith only [hA, hprod]
  have hupper : a' - a ≤ (delta + 6 * eta) * a :=
    le_of_mul_le_mul_left hB hposEtaN
  -- the lower half
  have hC : (1 - eta) * a ≤ (1 + eta) * a' := le_trans hm1 (le_trans hmono hk2)
  have hnn1 : (0 : ℝ) ≤ delta * a := mul_nonneg hdelta ha.le
  have hnn2 : (0 : ℝ) ≤ delta * eta * a := by positivity
  have hnn3 : (0 : ℝ) ≤ eta * eta * a := by positivity
  have hnn4 : (0 : ℝ) ≤ eta * a := mul_nonneg heta ha.le
  have hD : (1 + eta) * ((1 - (delta + 6 * eta)) * a) ≤ (1 + eta) * a' := by
    linarith only [hC, hnn1, hnn2, hnn3, hnn4]
  have hlower : (1 - (delta + 6 * eta)) * a ≤ a' :=
    le_of_mul_le_mul_left hD hposEtaP
  rw [abs_le]
  exact ⟨by linarith only [hlower], hupper⟩

/-- **`e.pigeon.scalar`** at the cutoff `L'`:

`|shom_{L',*}(cu_m) shom_{L',*}^{-1}(cu_{m-2h}) - 1| ≤ delta + 6 eta_L`.

The print's own derivation: `e.pigeon.matrix` gives the analogue with cutoff
`L`, which in the scalar reading is `hpig` (the last conjunct of
`exists_scaleSelection_of_threshold`) together with the monotonicity of
`k ↦ shom_{L,*}^{-1}(cu_k)`; the annealed consequence
`e.localization.s.star.annealed.applied` at the two scales `m` and `m-2h`
(`hlocm`, `hlock`, the conclusion of `annealed_cutoff_localization`) then
replaces the cutoff-`L` factors by cutoff-`L'` ones.

The printed error is `delta + eta_L`.  Composing the three relative
comparisons costs a universal factor on the localization error, which is
recorded here as the explicit `6 eta`; since `eta_L` carries a free constant
(`localizationEta Ceta nu L k` is linear in `Ceta`, so `6 eta_L` is `eta_L`
with `Ceta` replaced by `6 Ceta`), this is the printed statement after the
print's own "increasing the constant". -/
theorem pigeon_scalar_at_lower_cutoff {k m LPrime L : ℕ}
    (hnu : 0 < nu) (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P)
    (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P)
    (hdelta : 0 ≤ delta) (hdelta1 : delta ≤ 1) (heta : 0 ≤ eta)
    (heta4 : eta ≤ 1 / 4) (hkm : k ≤ m)
    (hpig : sigmaBarStarInvSeq nu L P k ≤ (1 + delta) * sigmaBarStarInvSeq nu L P m)
    (hlocm : |sigmaBarStarScalar nu LPrime P (cubeSet (originCube d (m : ℤ))) *
        sigmaBarStarInvScalar nu L P (cubeSet (originCube d (m : ℤ))) - 1| ≤ eta)
    (hlock : |sigmaBarStarScalar nu LPrime P (cubeSet (originCube d (k : ℤ))) *
        sigmaBarStarInvScalar nu L P (cubeSet (originCube d (k : ℤ))) - 1| ≤ eta) :
    |sigmaBarStarScalar nu LPrime P (cubeSet (originCube d (m : ℤ))) *
        sigmaBarStarInvScalar nu LPrime P (cubeSet (originCube d (k : ℤ))) - 1| ≤
      delta + 6 * eta := by
  have ha : 0 < sigmaBarStarInvScalar nu LPrime P (cubeSet (originCube d (m : ℤ))) :=
    sigmaBarStarInvScalar_pos_cutoff hnu LPrime hPrefix hJ2 hJ3 hJ4 (m : ℤ)
  have ha' : 0 < sigmaBarStarInvScalar nu LPrime P (cubeSet (originCube d (k : ℤ))) :=
    sigmaBarStarInvScalar_pos_cutoff hnu LPrime hPrefix hJ2 hJ3 hJ4 (k : ℤ)
  rw [sigmaBarStarScalar_eq_inv hnu LPrime hJ4 (m : ℤ) ha] at hlocm ⊢
  rw [sigmaBarStarScalar_eq_inv hnu LPrime hJ4 (k : ℤ) ha'] at hlock
  obtain ⟨hm1, hm2⟩ := sandwich_of_abs_inv_mul_sub_one ha hlocm
  obtain ⟨hk1, hk2⟩ := sandwich_of_abs_inv_mul_sub_one ha' hlock
  have hmono : sigmaBarStarInvSeq nu L P m ≤ sigmaBarStarInvSeq nu L P k :=
    antitone_sigmaBarStarInvSeq hnu L hPrefix hJ2 hJ3 hJ4 hkm
  have hmono' : sigmaBarStarInvScalar nu L P (cubeSet (originCube d (m : ℤ))) ≤
      sigmaBarStarInvScalar nu L P (cubeSet (originCube d (k : ℤ))) := by
    simpa only [sigmaBarStarInvSeq] using hmono
  have hpig' : sigmaBarStarInvScalar nu L P (cubeSet (originCube d (k : ℤ))) ≤
      (1 + delta) * sigmaBarStarInvScalar nu L P
        (cubeSet (originCube d (m : ℤ))) := by
    simpa only [sigmaBarStarInvSeq] using hpig
  exact abs_inv_mul_sub_one_of_abs_sub ha
    (pigeon_scalar_arith ha hdelta hdelta1 heta heta4 hm2 hm1 hk1 hk2 hpig' hmono')

end PigeonScalar

end

end SuperdiffusionCLT.Section3.Setup

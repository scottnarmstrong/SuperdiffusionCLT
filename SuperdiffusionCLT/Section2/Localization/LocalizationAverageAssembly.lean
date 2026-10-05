/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Localization.LocalizationAverageT1
public import SuperdiffusionCLT.Probability.GammaSigmaHelpers

/-!
# The assembly of the two printed summands `T1 + T2`

`LocalizationAverageOrlicz.lean` names the single Orlicz premise

`LocalizationAverageOrliczPremise C nu P m n l L Pvec`

to which `localization_average_of_orlicz` (in `LocalizationAverageWork.lean`)
reduces the statement
`SuperdiffusionCLT.Frozen.Section2.localization_average`, the paper's
`l.localization.average`.  The premise's amplitude splits as
`localizationAverageEnvelope = localizationAverageEnvelopeT1 +
localizationAverageEnvelopeT2` (`localizationAverageEnvelope_eq_T1_add_T2`), and the
two summands are bounded by:

* `localizationAverage_T1` / `localizationAverage_T1_of_grid`
  (`LocalizationAverageT1.lean`) at amplitude
  `localizationAverageEnvelopeT1 (16 C) ν ℓ L n Pvec`;
* the conditional estimates for the second summand (`LocalizationAverageT2B.lean`)
  at amplitude `localizationAverageEnvelopeT2 C' ν ℓ L m n Pvec`, with `C'`
  determined by `C` and the weight constant of the summand.

## Main results

1. `localizationAverageOrliczPremise_of_T1_T2`: the premise itself, from the two
   summand estimates plus the pointwise splitting and the printed triangle rule,
   at the enlarged constant `orliczAssemblyConst * C` with
   `orliczAssemblyConst = 2 * gammaTriangleConst (1/3)`.
2. The printed lattice `3^nℤ^d ∩ cu_m` over which both summands are averaged,
   realized as the descendant family `localizationAverageGrid`, with its
   cardinality (`localizationAverageGrid_card`, `localizationAverageGrid_card_le`,
   `localizationAverageGrid_card_ge_two`) and nonemptiness
   (`localizationAverageGrid_nonempty`).
3. The two coordinate families `localizationUpperShells` and
   `localizationLowerShells` of the conditioning in the proof, and their
   disjointness.
4. `localizationAverageEnvelopeT2_mono_le`: the second envelope is monotone in its
   constant, which reconciles the constants of the two summands.

## The `ν` power of the second summand

The envelope `localizationAverageEnvelopeT2` carries `ν⁻³`.  The printed proof
states the second summand twice:

* in the proof of `l.localization.average` the second summand is bounded by
  `T_2 ≤ O_{Γ_{1/2}}(Cν⁻¹(1∨ℓ)(1∨L)(1∨(m-n))3^{-(d/2)(m-ℓ)}|P|²)`, i.e. `ν⁻¹`
  at the stronger index `Γ_{1/2}`; and
* in the statement `e.localization.average.oneshot` the envelope carrying the two
  summands reads `C ν⁻³ |P|² ( 1_{L>ℓ}L3^{-(ℓ-n)} + (1∨ℓ)(1∨L)(1∨(m-n))3^{-(d/2)(m-ℓ)} )`,
  i.e. `ν⁻³` at the index `Γ_{1/3}`.

The proof passes from the first to the second form: since `Γ_{1/2}`-tails are
stronger than `Γ_{1/3}`-tails, and since `ν⁻¹ ≤ ν⁻³` under the standing assumption
`ν ∈ (0,1]`, the bound for `T_2` is also valid at the `Γ_{1/3}` rate with the unified
`ν⁻³` prefactor.  So there is no discrepancy: `localizationAverageEnvelopeT2` is the
envelope of the statement, and the intermediate, strictly stronger display is
proved separately in `LocalizationAverageT2.lean`, with the passage
`localizationAverage_T2_rawAmplitude_le`.  The `ν⁻¹` of the intermediate display is
not the amplitude of the premise, and replacing `ν⁻³` by `ν⁻¹` in
`localizationAverageEnvelopeT2` would break `localizationAverageEnvelope_eq_T1_add_T2`,
whose common prefactor is `ν⁻³`.

## The finite-maximum step

The finite-maximum step `l.maximums.Gamma.s` of the proof needs a grid with at
least two points, which is why `localizationAverageGrid_card_ge_two` assumes `n < m`.
The remaining regime `ℓ = m = n`, where the grid is a single cube, is treated by
carrying the printed weight-envelope bound directly, without a maximum.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section2.Localization

open MeasureTheory Homogenization Homogenization.Book.Ch02
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Cutoff

variable {d : ℕ}

/-! ## The assembly constant -/

/-! ## The premise, assembled from the two summand bounds -/

/-- **The Orlicz premise, from the two printed summands.**  From

1. the pointwise splitting `|LHS ω| ≤ T1 ω + T2 ω` of the proof of
   `l.localization.average`,
2. `T1 = O_{Γ_{1/3}}(C ν⁻³ |P|² 1_{L>ℓ} L 3^{-(ℓ-n)})`, and
3. `T2 = O_{Γ_{1/2}}(C ν⁻³ |P|² (1∨ℓ)(1∨L)(1∨(m-n)) 3^{-(d/2)(m-ℓ)})` (the bound
   of the proof weakened to the envelope of the statement),

the premise `LocalizationAverageOrliczPremise (orliczAssemblyConst * C) nu P m n l L Pvec`
holds.  The constant is `orliczAssemblyConst * C`, i.e.
`2 * gammaTriangleConst (1/3) * C`: both summands are lifted to the common printed
amplitude `localizationAverageEnvelope C ν ℓ L m n Pvec` (which is their sum by
`localizationAverageEnvelope_eq_T1_add_T2`) and then combined by the printed
triangle rule `isBigO_gammaSigma_add_of_isBigO`; the printed proof enlarges `C(d)`
in the same way. -/
theorem localizationAverageOrliczPremise_of_T1_T2 {C nu : ℝ} (hC : 0 < C) (hnu : 0 < nu)
    (P : ProbabilityMeasure (ShellSeq d)) (m n l L : ℕ) (Pvec : BlockVec d)
    (T1 T2 : ShellSeq d → ℝ) (hT1m : Measurable T1) (hT2m : Measurable T2)
    (hT1nn : ∀ omega, 0 ≤ T1 omega) (hT2nn : ∀ omega, 0 ≤ T2 omega)
    (hdecomp : ∀ omega : ShellSeq d,
      |averagedGaugeComparison nu l L P m n Pvec omega| ≤ T1 omega + T2 omega)
    (hT1 : IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma ((1 : ℝ) / 3)) T1
      (localizationAverageEnvelopeT1 C nu l L n Pvec))
    (hT2 : IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma ((1 : ℝ) / 2)) T2
      (localizationAverageEnvelopeT2 C nu l L m n Pvec)) :
    LocalizationAverageOrliczPremise (orliczAssemblyConst * C) nu P m n l L Pvec :=
  localization_average_orlicz_of_summands hC hnu P m n l L Pvec T1 T2 hT1m hT2m hT1nn hT2nn
    hdecomp hT1 hT2

/-! ## The printed lattice grid `3^nℤ^d ∩ cu_m` -/

/-- The lattice `3^nℤ^d ∩ cu_m` over which both printed summands are averaged,
realized as the descendant family of `averagedGaugeComparison`. -/
abbrev localizationAverageGrid (d : ℕ) (m n : ℕ) : Finset (TriadicCube d) :=
  descendantsAtDepth (originCube d (m : ℤ)) (m - n)

/-- The printed lattice has exactly `3^{d(m-n)}` points, the cardinality of the
descendant family. -/
theorem localizationAverageGrid_card (m n : ℕ) :
    (localizationAverageGrid d m n).card = (3 ^ d) ^ (m - n) :=
  Homogenization.descendantsAtDepth_card _ _

/-- The printed lattice is nonempty. -/
theorem localizationAverageGrid_nonempty (m n : ℕ) :
    (localizationAverageGrid d m n).Nonempty :=
  Finset.card_pos.mp (by rw [localizationAverageGrid_card]; positivity)

/-- `3 ^ ((d : ℝ) * (k : ℝ))` is the `d`-dimensional count `(3^d)^k`. -/
private theorem three_rpow_dim_mul (d k : ℕ) :
    (3 : ℝ) ^ ((d : ℝ) * (k : ℝ)) = (((3 ^ d) ^ k : ℕ) : ℝ) := by
  rw [Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3) (d : ℝ) (k : ℝ)]
  simp only [Real.rpow_natCast]
  rw [Nat.cast_pow, Nat.cast_pow]
  simp

/-- The printed lattice has at most `3^{d(m-n)}` points: the cardinality input of
the finite-maximum step of the second summand. -/
theorem localizationAverageGrid_card_le (m n : ℕ) :
    ((localizationAverageGrid d m n).card : ℝ) ≤ (3 : ℝ) ^ ((d : ℝ) * ((m - n : ℕ) : ℝ)) := by
  rw [localizationAverageGrid_card]
  exact le_of_eq (three_rpow_dim_mul d (m - n)).symm

/-- The printed lattice has at least two points as soon as `n < m` and `0 < d`,
the hypothesis of the finite-maximum step `l.maximums.Gamma.s`. -/
theorem localizationAverageGrid_card_ge_two {m n : ℕ} (hmn : n < m) (hd : 1 ≤ d) :
    2 ≤ (localizationAverageGrid d m n).card := by
  have hmn1 : m - n ≠ 0 := by omega
  rw [localizationAverageGrid_card]
  calc (2 : ℕ) ≤ 3 ^ d := by
        calc (2 : ℕ) ≤ 3 ^ 1 := by norm_num
          _ ≤ 3 ^ d := Nat.pow_le_pow_right (by norm_num) hd
    _ ≤ (3 ^ d) ^ (m - n) := Nat.le_self_pow hmn1 _

/-! ## The two coordinate families of the printed conditioning

The conditioning field of the printed proof is `F_> = σ(j_r : r > ℓ)` and the
summands are functionals of the complementary lower coordinates `{r ≤ ℓ}`. -/

/-- The upper coordinate family `{r | ℓ < r}` generating the printed `F_>`. -/
def localizationUpperShells (l : ℕ) : Set ℕ := {r | l < r}

/-- The lower coordinate family `{r | r ≤ ℓ}` carrying the printed summands. -/
def localizationLowerShells (l : ℕ) : Set ℕ := {r | r ≤ l}

/-- The two printed coordinate families are disjoint. -/
theorem localizationUpperShells_disjoint_lowerShells (l : ℕ) :
    Disjoint (localizationUpperShells l) (localizationLowerShells l) := by
  rw [Set.disjoint_left]
  intro r hr hr'
  simp only [localizationUpperShells, localizationLowerShells, Set.mem_ofPred_eq] at hr hr'
  omega

/-! ## Constant monotonicity of the second summand's amplitudes -/

/-- The second printed envelope is monotone in its constant. -/
theorem localizationAverageEnvelopeT2_mono_le {C C' nu : ℝ} (hCC' : C ≤ C') (hnu : 0 ≤ nu)
    (l L m n : ℕ) (Pvec : BlockVec d) :
    localizationAverageEnvelopeT2 C nu l L m n Pvec ≤
      localizationAverageEnvelopeT2 C' nu l L m n Pvec := by
  unfold localizationAverageEnvelopeT2
  refine mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCC' (Real.rpow_nonneg hnu _))
      (SuperdiffusionCLT.Section2.Carriers.blockVecDot_self_nonneg Pvec)) ?_
  exact mul_nonneg (mul_nonneg (mul_nonneg (le_trans zero_le_one (le_max_left _ _))
    (le_trans zero_le_one (le_max_left _ _))) (le_trans zero_le_one (le_max_left _ _)))
    (Real.rpow_nonneg (by norm_num) _)

end SuperdiffusionCLT.Section2.Localization

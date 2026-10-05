/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Localization.LocalizationEnvelopeCarrier
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
public import SuperdiffusionCLT.Section2.Localization.LocalizationAverageT2Inputs

/-!
# `T2`'s centring: what the conditional layer can and cannot reach

## The printed statement

The second summand of `e.localization.average.oneshot` is estimated in the proof of
`l.localization.average`.  With

* `Z_z := G_{-h_z}P · (bfA_ℓ(z+cu_n) − bfAhom_ℓ(cu_n)) G_{-h_z}P` and
* `X_z := M(P)⁻¹ Z_z`,

the printed proof conditions on `F_> = σ(j_r : r > ℓ)` and uses

  `E[Z_z | F_>] = 0` for every `z ∈ 3^nℤ^d ∩ cu_m`,

*"by stationarity"*, the gauge vectors `{G_{-h_z}P}` being deterministic given
`F_>` because `h_z` depends only on the scales `{r > ℓ}` while `bfA_ℓ` is
`{r ≤ ℓ}`-measurable.

## Does the conditional layer reach it?

The conditional-centring lemma of the probability layer
derives `μ[X | shellSigma S] =ᵐ 0` from `∫ X ∂μ = 0` for `X` **measurable for the
complementary coordinate family** `T`, given `Disjoint S T` and the standing
coordinate independence.  It is applied here at `S = {r | ℓ < r}` (the printed
`F_>`) and `T = {r | r ≤ ℓ}`.

It does **not** apply to the printed centred variable `Z_z`: `Z_z` carries the
gauge factor `G_{-h_z}P`, which is a functional of the *upper* shells, so `Z_z` is
not measurable for `shellSigma T` with `T = {r | r ≤ ℓ}` or for any other family
disjoint from `F_>`.  The lemma's hypothesis (complement measurability) is exactly
what the printed variable lacks, so the lemma cannot manufacture it.

What the lemma *does* reach is the printed variable's **ingredients**.  Since
`toFullBlockMat`/`toFullBlockVec` turn the printed bilinear form into a finite sum
of products

  `Z_z = ∑_{α,β} (G_{-h_z}P)_α (G_{-h_z}P)_β (bfA_ℓ(z+cu_n) − bfAhom_ℓ(cu_n))_{αβ}`,

whose *coefficients* `(G_{-h_z}P)_α (G_{-h_z}P)_β` are `F_>`-measurable and whose
*entries* `(bfA_ℓ(z+cu_n) − bfAhom_ℓ(cu_n))_{αβ}` are lower-shell quantities, the
partial-integral step applies entrywise.  That needs one extra rule, which is what
`condExp_mul_eq_mul_integral_of_compl` supplies below: for an `S`-measurable
coefficient `c` and a `T`-measurable factor `Y`,

  `μ[c · Y | shellSigma S] =ᵐ c · ∫ Y ∂μ`,

so an entrywise vanishing mean `∫ (perturbation)_{αβ} = 0` gives `E[Z_z | F_>] = 0`.

## The two inputs that remain

Neither is a gap of the conditional layer.

1. **Lower-shell strong measurability of the perturbation entries.**
   `LocalizationEnvelopeCarrier.lean` proves only *ambient* measurability of
   `localizationPerturbationMatrix`; the lemmas
   `measurable_coarseBlockMatrix_*_apply` need `Measurable[m] (coefficientCutoff nu · l)`
   as a full `RegCoeffField`-valued function, while only the
   entrywise form is available.  The entrywise vanishing-mean input is carried as a hypothesis
   below.
2. **The entrywise vanishing means `∫ (bfA_ℓ(cube R) − bfAhom_ℓ(cu_n))_{αβ} = 0`.**
   By definition `bfAhom_ℓ(cu_n)` is the entrywise integral of `bfA_ℓ(cu_n)`
   (`annealedBlockMatrix`), so this is the annealed-mean/stationarity input: the
   translation invariance of the cutoff field's law, i.e.
   `ShellLawPrefix.stationary`.  It is *not* a conditional-centring hypothesis.

## The `h_mean` hypothesis of the carrier is not a centring

`LocalizationAverageFinal.lean` instantiates the summand family
`V` of the `T2` chain with the only scalar the carrier module attaches to the perturbation, the
operator norm `blockMatrixOperatorNorm (localizationV ·)`.  That scalar is
nonnegative, so its zero-mean hypothesis is not a centring at all: it holds exactly
when the perturbation vanishes almost everywhere --- a degeneracy, not a
cancellation.  The printed summands are the *signed* quantities `Z_z`, which the
norm is not.

## Main results

* `condExp_mul_eq_mul_integral_of_compl`: for an `S`-measurable coefficient and a
  `T`-measurable factor, the conditional expectation of the product is the coefficient
  times the integral of the factor.
* `blockVecDot_blockMatVecMul_eq_sum`: the printed bilinear form as a finite sum of products.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section2.Localization

open MeasureTheory Homogenization Homogenization.Book.Ch02
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Carriers
open SuperdiffusionCLT.Section2.Cutoff

variable {d : ℕ}

/-! ## The product form of the partial-integral step

The partial-integral step
`condExp_shellSigma_eq_integral_of_measurable` handles a factor that is itself
measurable for the complementary family.  The printed `Z_z` is not of that form:
it is a coefficient measurable for the conditioning family times a complementary
factor.  The two results below are the missing rule. -/

/-- **The product form of the partial-integral step.**  For an `S`-measurable
coefficient `c` and a `T`-measurable factor `Y` (with `S`, `T` disjoint coordinate
families), `μ[c · Y | shellSigma S]` is a.e. `c · ∫ Y ∂μ`.  This is the
pull-out property of the conditional expectation (`condExp_mul_of_stronglyMeasurable_left`)
composed with the partial-integral step for `Y`. -/
theorem condExp_mul_eq_mul_integral_of_compl {μ : Measure (ShellSeq d)} [IsFiniteMeasure μ]
    {S T : Set ℕ} (hST : Disjoint S T)
    (hJ2 : ProbabilityTheory.iIndepFun (fun r : ℕ => fun F : ShellSeq d => F r) μ)
    {c Y : ShellSeq d → ℝ}
    (hc : StronglyMeasurable[SuperdiffusionCLT.Probability.shellSigma (d := d) S] c)
    (hY : StronglyMeasurable[SuperdiffusionCLT.Probability.shellSigma (d := d) T] Y)
    (hYint : Integrable Y μ) (hcYint : Integrable (c * Y) μ) :
    μ[c * Y | SuperdiffusionCLT.Probability.shellSigma (d := d) S] =ᵐ[μ]
      fun ω => c ω * ∫ ω, Y ω ∂μ := by
  have hYce := SuperdiffusionCLT.Probability.condExp_shellSigma_eq_integral_of_measurable
    (d := d) (S := S) (T := T) hST hJ2 hY
  have hpull := MeasureTheory.condExp_mul_of_stronglyMeasurable_left (μ := μ)
    (m := SuperdiffusionCLT.Probability.shellSigma (d := d) S) hc hcYint hYint
  filter_upwards [hpull, hYce] with ω hω₁ hω₂
  rw [hω₁, Pi.mul_apply, hω₂]

/-! ## The printed bilinear form as a finite sum of products -/

/-- **The printed bilinear form entrywise.**  The doubled pairing of the gauge
vector with the perturbation applied to the gauge vector — the printed `Z_z` — is
the full-matrix double sum `∑_{α,β} (g_α g_β) M_{αβ}`: a finite sum of products of
`F_>`-measurable coefficients with lower-shell entries.  This is
`blockVecDot_blockMatVecMul_eq_toLinearMap₂'` followed by the entrywise form
`Matrix.toLinearMap₂'_apply`, packaged as an equality of functions so that the
conditional expectation of the sum splits termwise. -/
theorem blockVecDot_blockMatVecMul_eq_sum (g : ShellSeq d → BlockVec d)
    (Mf : ShellSeq d → BlockMat d) :
    (fun ω => blockVecDot (g ω) (blockMatVecMul (Mf ω) (g ω))) =
      ∑ p : BlockCoord d × BlockCoord d,
        fun ω => (toFullBlockVec (g ω) p.1 * toFullBlockVec (g ω) p.2) *
          toFullBlockMat (Mf ω) p.1 p.2 := by
  funext ω
  rw [Finset.sum_apply]
  have hpair : (∑ p : BlockCoord d × BlockCoord d,
      (toFullBlockVec (g ω) p.1 * toFullBlockVec (g ω) p.2) *
        toFullBlockMat (Mf ω) p.1 p.2) =
      ∑ α, ∑ β, (toFullBlockVec (g ω) α * toFullBlockVec (g ω) β) *
        toFullBlockMat (Mf ω) α β := by
    rw [Fintype.sum_prod_type]
  rw [Homogenization.blockVecDot_blockMatVecMul_eq_toLinearMap₂',
    Matrix.toLinearMap₂'_apply, hpair]
  refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => ?_
  simp only [smul_eq_mul]
  ring

/-! ## The conditional centring of the printed `Z_z` -/

/-! ## The centring of the printed `Z_z` at the printed carriers -/

/-! ## The `h_mean` hypothesis of the carrier is a degeneracy, not a centring -/

end SuperdiffusionCLT.Section2.Localization

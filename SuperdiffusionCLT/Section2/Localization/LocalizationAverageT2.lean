/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Localization.LocalizationAverageOrlicz
public import SuperdiffusionCLT.Probability.OrliczProduct

/-!
# The second summand `T2` of the averaged gauged comparison

The single Orlicz premise of the localization statement splits into the two printed summands
`T1 + T2`, and `localizationAverageEnvelope_eq_T1_add_T2` shows that the printed envelope is
the sum of the two amplitudes.  This module addresses the *second* summand, whose printed
amplitude is `localizationAverageEnvelopeT2`.

## What the printed proof does for `T2`

With `Z_z := G_{-h_z}P · (bfA_ℓ(z+cu_n) − bfAhom_ℓ(cu_n)) G_{-h_z}P` and
`W_z := |bfE_ℓ^{1/2} G_{-h_z}P|²`, so that `W_z` is
measurable for `F_> := σ(j_r : r > ℓ)` and `E[Z_z | F_>] = 0` by stationarity,
the printed proof proceeds in four steps.

1. **The pointwise factorisation.**  `|Z_z| ≤ W_z · |bfE_ℓ^{-1/2}(bfA_ℓ −
   bfAhom_ℓ)bfE_ℓ^{-1/2}| ≤ W_z · O_{Γ_1}(C)` conditionally on `F_>`,
   whence `T_2 := |avsum_z Z_z|` is controlled by
   `Wbar := max_z W_z` times the concentration of `Wbar^{-1}Z_z`.
2. **The conditional concentration** of the `Wbar^{-1}Z_z` on the
   `~3^{d(ℓ-n)}` sublattices, giving
   `Wbar^{-1}T_2 ≤ O_{Γ_1}(C 3^{-d/2(m-ℓ)})` conditionally on `F_>`.
3. **The envelope of the weights.**  `W_z ≤ O_{Γ_1}(Cν^{-1}(1∨ℓ)(1∨L)|P|²)`
   for each fixed `z` and `l.maximums.Gamma.s` over the
   `~3^{d(m-n)}` values gives `Wbar ≤ O_{Γ_1}(Cν^{-1}(1∨ℓ)(1∨L)(1∨(m-n))|P|²)`.
4. **The combine.**  Removing the conditioning by integration and multiplying
   the two `Γ_1` factors by the multiplication property `e.multGammasig`
   gives
   `T_2 ≤ O_{Γ_{1/2}}(Cν^{-1}(1∨ℓ)(1∨L)(1∨(m-n)) 3^{-d/2(m-ℓ)}|P|²)`, and
   since `Γ_{1/2}`-tails are stronger than `Γ_{1/3}`-tails and
   `ν^{-1} ≤ ν^{-3}` for `ν ∈ (0,1]`, the bound also holds at the unified
   `ν^{-3}` prefactor of the envelope.

## The amplitude recorded by the definition

The raw display of step 4 carries the prefactor `ν^{-1}` at the index
`Γ_{1/2}`.  The definition `localizationAverageEnvelopeT2` carries `ν^{-3}`; that
is the *weakened, unified* prefactor of the envelope display of
`e.localization.average.oneshot`, which the printed proof adopts at the end.
Passing from the raw prefactor to the unified prefactor consumes the standing hypothesis
`ν ≤ 1` (through `ν^{-1} ≤ ν^{-3}`) and the index weakening `Γ_{1/2} ↝ Γ_{1/3}`.

## Main results

* `localizationAverage_T2_of_factor_bound`: the combine of step 4 for an
  arbitrary factorisation `T2 = W · U` of two `Γ_1` quantities, through
  `isBigO_gammaSigma_mul` at `σ₁ = σ₂ = 1` (index `1/2`).
* `localizationAverage_wbar_bound_of_cube_bounds`: step 3, the finite maximum
  over the grid, from per-cube `Γ_1` bounds and the finite-maximum rule
  `isBigOWith_gammaSigma_finset_sup'`; the only bookkeeping left is the
  cardinality bound `hAmpl`.
* `localizationAverage_wbar_amplitude_le` and
  `localizationAverage_wbar_bound_of_cube_bounds'`: the bookkeeping `hAmpl`
  discharged at the per-cube printed amplitude `localizationAverageWbarCubeAmplitude`,
  the enlarged constant being `3 d log 3 C`.
* `localizationAverage_T2_rawAmplitude_le`: the amplitude bookkeeping of the final weakening
  to the amplitude `localizationAverageEnvelopeT2 (orliczProductConst 1 1 * C) ν ℓ L m n Pvec`.

Steps 1 and 2 are not proved in this module: they are the conditional
concentration of `Wbar^{-1}Z_z` given `F_>`.  For the actual descendant grid the cardinality
bound `hcardle` of `localizationAverage_wbar_bound_of_cube_bounds'` holds with
equality by `card_descendantsAtDepth_originCube`, so
the maximum step carries no bookkeeping at all once that grid is fixed.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section2.Localization

open MeasureTheory Homogenization Homogenization.Book.Ch02
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Cutoff

variable {d : ℕ}

/-! ## Step 4: the combine of two `Γ_1` factors -/

/-- **The printed combine of the two factors of `T_2`.**
If `T_2` factorises pointwise as `W · U` with `W` the weight envelope and `U` the
normalised average, and both factors are `O_{Γ_1}` at amplitudes `AW`, `AU`,
then `T_2` is `O_{Γ_{1/2}}` at the printed product amplitude
`orliczProductConst 1 1 * (AW * AU)`: the multiplication property
`e.multGammasig` at `σ₁ = σ₂ = 1`, whose product index is
`1 · 1 / (1 + 1) = 1/2`.  This is the index `Γ_{1/2}` of the printed
display. -/
theorem localizationAverage_T2_of_factor_bound (P : ProbabilityMeasure (ShellSeq d))
    (T2 W U : ShellSeq d → ℝ) (hT2 : ∀ omega, T2 omega = W omega * U omega)
    {AW AU : ℝ} (hAW : 0 ≤ AW) (hAU : 0 ≤ AU)
    (hW : IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma 1) W AW)
    (hU : IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma 1) U AU) :
    IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma ((1 : ℝ) / 2)) T2
      (SuperdiffusionCLT.Probability.orliczProductConst 1 1 * (AW * AU)) := by
  have hmul := SuperdiffusionCLT.Probability.isBigO_gammaSigma_mul
    (mu := P.toMeasure) (X₁ := W) (X₂ := U) (A₁ := AW) (A₂ := AU)
    (σ₁ := 1) (σ₂ := 1) (by norm_num) (by norm_num) hAW hAU hW hU
  have hidx : (1 : ℝ) * 1 / (1 + 1) = 1 / 2 := by norm_num
  rw [hidx] at hmul
  rw [show T2 = (fun omega : ShellSeq d => W omega * U omega) from funext hT2]
  exact hmul

/-! ## The printed amplitudes -/

/-- The printed envelope of the weights `Wbar`: the amplitude
`C ν⁻¹ (1∨ℓ)(1∨L)(1∨(m-n)) |P|²` with the `ν^{-1}` prefactor of
`e.Enaught.mixing` and `l.maximums.Gamma.s`.  The `ν^{-3}` prefactor of
`localizationAverageEnvelopeT2` is not used here: it is the weakened form
adopted only at the end of the printed proof. -/
noncomputable def localizationAverageWbarAmplitude (C nu : ℝ) (l L m n : ℕ)
    (Pvec : BlockVec d) : ℝ :=
  C * nu ^ (-(1 : ℝ)) * blockVecDot Pvec Pvec *
    (max 1 (l : ℝ) * max 1 (L : ℝ) * max 1 ((m - n : ℕ) : ℝ))

/-- The printed amplitude of the normalised average `Wbar^{-1}T_2` after the
sublattice concentration: `C 3^{-d/2(m-ℓ)}`.  The constant is
absorbed into the one of `localizationAverageWbarAmplitude`, matching the printed enlargement
of `C(d)`. -/
noncomputable def localizationAverageNormalisedAmplitude (d : ℕ) (m l : ℕ) : ℝ :=
  (3 : ℝ) ^ (-((d : ℝ) / 2 * ((m - l : ℕ) : ℝ)))

/-- The printed amplitude of `T_2`: the product of the two
factors at the `Γ_{1/2}` index, with the `ν^{-1}` prefactor. -/
noncomputable def localizationAverageT2RawAmplitude (C nu : ℝ) (l L m n : ℕ)
    (Pvec : BlockVec d) : ℝ :=
  SuperdiffusionCLT.Probability.orliczProductConst 1 1 *
    (localizationAverageWbarAmplitude C nu l L m n Pvec *
      localizationAverageNormalisedAmplitude d m l)

/-- The printed amplitude of the *single* weight `W_z`:
`C ν⁻¹ (1∨ℓ)(1∨L) |P|²`, the `z`-independent bound obtained from
`e.Enaught.mixing` and `e.jk.spatialavg` before the maximum over the grid is
taken. -/
noncomputable def localizationAverageWbarCubeAmplitude (C nu : ℝ) (l L : ℕ)
    (Pvec : BlockVec d) : ℝ :=
  C * nu ^ (-(1 : ℝ)) * (max 1 (l : ℝ) * max 1 (L : ℝ)) * blockVecDot Pvec Pvec

/-! ## Step 3: the finite maximum of the weights over the grid -/

/-- **The printed finite-maximum step** (`l.maximums.Gamma.s`).  If
every weight `W_i` of a grid `grid` is nonnegative and `O_{Γ_1}` at one common
amplitude `A`, then the maximum `Wbar = max_grid W_i` is `O_{Γ_1}` at the
printed amplitude `localizationAverageWbarAmplitude C ν ℓ L m n Pvec`, provided
the supremum constant of the finite-maximum rule,
`(3 log #grid)^{1⁻¹} A`, fits inside it.  That last inequality is the
cardinality bookkeeping `#grid = ~3^{d(m-n)}`, recorded as the named hypothesis
`hAmpl`; it is where the printed factor `(1∨(m-n))` comes from.  The
nonnegativity is what lets the one-sided finite-maximum rule
(`isBigOWith_gammaSigma_finset_sup'`) be read as an absolute-value estimate, and it also
identifies the empty-index `Finset.sup` value `0` with the maximum. -/
theorem localizationAverage_wbar_bound_of_cube_bounds {C nu A : ℝ}
    (P : ProbabilityMeasure (ShellSeq d)) (l L m n : ℕ) (Pvec : BlockVec d)
    {ι : Type*} (grid : Finset ι) (hne : grid.Nonempty) (hcard : 2 ≤ grid.card)
    (W : ι → ShellSeq d → ℝ) (Wbar : ShellSeq d → ℝ)
    (hWbar : ∀ omega, Wbar omega = grid.sup' hne (fun i => W i omega))
    (hWnn : ∀ i ∈ grid, ∀ omega, 0 ≤ W i omega)
    (hcube : ∀ i ∈ grid,
      IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma 1) (W i) A)
    (hAmpl : ((3 * Real.log (grid.card : ℝ)) ^ ((1 : ℝ)⁻¹)) * A ≤
      localizationAverageWbarAmplitude C nu l L m n Pvec) :
    IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma 1) Wbar
      (localizationAverageWbarAmplitude C nu l L m n Pvec) := by
  have hWith : ∀ i ∈ grid,
      IndependentSums.IsBigOWith P.toMeasure (IndependentSums.gammaSigma 1) (W i) A :=
    fun i hi =>
      (SuperdiffusionCLT.Probability.isBigOWith_iff_isBigO_of_nonneg (hWnn i hi)).mpr
        (hcube i hi)
  have hsup := IndependentSums.isBigOWith_gammaSigma_finset_sup' (μ := P.toMeasure)
    (s := grid) hne (X := W) (A := A) (σ := 1)
    (by norm_num) hcard hWith
  have hWbarnn : ∀ omega, 0 ≤ Wbar omega := by
    intro omega
    obtain ⟨i, hi⟩ := hne
    rw [hWbar omega]
    exact (hWnn i hi omega).trans (Finset.le_sup' (s := grid) (f := fun i => W i omega) hi)
  have hb : IndependentSums.IsBigOWith P.toMeasure (IndependentSums.gammaSigma 1) Wbar
      (((3 * Real.log (grid.card : ℝ)) ^ ((1 : ℝ)⁻¹)) * A) := by
    rw [show Wbar = fun omega => grid.sup' hne (fun i => W i omega) from funext hWbar]
    exact hsup
  exact ((SuperdiffusionCLT.Probability.isBigOWith_iff_isBigO_of_nonneg hWbarnn).1 hb).mono_scale
    hAmpl

/-- **The cardinality bookkeeping of the finite-maximum step.**  For a grid of
`g ≥ 2` weights whose cardinality is at most `3^{d(m-n)}` — the descendant
count of `card_descendantsAtDepth_originCube` — the supremum constant
`(3 log g)^{1⁻¹}` of the finite-maximum rule, multiplied by the per-cube
amplitude `localizationAverageWbarCubeAmplitude C ν ℓ L Pvec`, fits inside the
printed envelope `localizationAverageWbarAmplitude (3 d log 3 C) ν ℓ L m n Pvec`.
The enlarged constant `3 d log 3 C` is the printed enlargement of `C(d)`; the
factor `(1∨(m-n))` of the envelope absorbs the `(m-n)` of the logarithm. -/
theorem localizationAverage_wbar_amplitude_le {C nu : ℝ} (hC : 0 < C) (hnu : 0 < nu)
    {g : ℕ} (hg : 2 ≤ g) (l L m n : ℕ) (Pvec : BlockVec d)
    (hcard : (g : ℝ) ≤ (3 : ℝ) ^ ((d : ℝ) * ((m - n : ℕ) : ℝ))) :
    ((3 * Real.log (g : ℝ)) ^ ((1 : ℝ)⁻¹)) *
        localizationAverageWbarCubeAmplitude C nu l L Pvec ≤
      localizationAverageWbarAmplitude (3 * (d : ℝ) * Real.log 3 * C) nu l L m n Pvec := by
  have hgpos : (0 : ℝ) < (g : ℝ) :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) (by exact_mod_cast hg)
  have hgone : (1 : ℝ) ≤ (g : ℝ) := by exact_mod_cast (le_trans (by norm_num : 1 ≤ 2) hg)
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hlog_le : Real.log (g : ℝ) ≤ (d : ℝ) * ((m - n : ℕ) : ℝ) * Real.log 3 :=
    (Real.log_le_log hgpos hcard).trans_eq (Real.log_rpow (by norm_num) _)
  have hdnn : 0 ≤ (d : ℝ) := Nat.cast_nonneg d
  have hmn : 0 ≤ ((m - n : ℕ) : ℝ) := Nat.cast_nonneg _
  have hmaxl : (0 : ℝ) ≤ max 1 (l : ℝ) := le_trans zero_le_one (le_max_left _ _)
  have hmaxL : (0 : ℝ) ≤ max 1 (L : ℝ) := le_trans zero_le_one (le_max_left _ _)
  have hdot : 0 ≤ blockVecDot Pvec Pvec :=
    SuperdiffusionCLT.Section2.Carriers.blockVecDot_self_nonneg Pvec
  have hcubeAmp : 0 ≤ localizationAverageWbarCubeAmplitude C nu l L Pvec := by
    unfold localizationAverageWbarCubeAmplitude
    exact mul_nonneg (mul_nonneg (mul_nonneg hC.le (Real.rpow_nonneg hnu.le _))
      (mul_nonneg hmaxl hmaxL)) hdot
  have hK : 0 ≤ 3 * (d : ℝ) * Real.log 3 * C * nu ^ (-(1 : ℝ)) *
      (max 1 (l : ℝ) * max 1 (L : ℝ)) * blockVecDot Pvec Pvec :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg
      (by norm_num) hdnn) hlog3.le) hC.le) (Real.rpow_nonneg hnu.le _))
      (mul_nonneg hmaxl hmaxL)) hdot
  rw [inv_one, Real.rpow_one]
  unfold localizationAverageWbarCubeAmplitude localizationAverageWbarAmplitude
  calc 3 * Real.log (g : ℝ) * (C * nu ^ (-(1 : ℝ)) * (max 1 (l : ℝ) * max 1 (L : ℝ)) *
        blockVecDot Pvec Pvec)
      ≤ 3 * ((d : ℝ) * ((m - n : ℕ) : ℝ) * Real.log 3) *
          (C * nu ^ (-(1 : ℝ)) * (max 1 (l : ℝ) * max 1 (L : ℝ)) * blockVecDot Pvec Pvec) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hlog_le (by norm_num)) hcubeAmp
    _ = (3 * (d : ℝ) * Real.log 3 * C * nu ^ (-(1 : ℝ)) *
          (max 1 (l : ℝ) * max 1 (L : ℝ)) * blockVecDot Pvec Pvec) * ((m - n : ℕ) : ℝ) := by
        ring
    _ ≤ (3 * (d : ℝ) * Real.log 3 * C * nu ^ (-(1 : ℝ)) *
          (max 1 (l : ℝ) * max 1 (L : ℝ)) * blockVecDot Pvec Pvec) *
            max 1 ((m - n : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_left (le_max_right 1 _) hK
    _ = 3 * (d : ℝ) * Real.log 3 * C * nu ^ (-(1 : ℝ)) * blockVecDot Pvec Pvec *
          (max 1 (l : ℝ) * max 1 (L : ℝ) * max 1 ((m - n : ℕ) : ℝ)) := by
        ring

/-- **The printed finite-maximum step with its cardinality bookkeeping
discharged.**  This is `localizationAverage_wbar_bound_of_cube_bounds` applied
with the per-cube amplitude `localizationAverageWbarCubeAmplitude C ν ℓ L Pvec`:
the only remaining hypothesis on the grid is its cardinality bound
`#grid ≤ 3^{d(m-n)}`, discharged for the actual descendant grid by
`card_descendantsAtDepth_originCube`.  The enlarged constant is
`3 d log 3 C` of the finite-maximum rule. -/
theorem localizationAverage_wbar_bound_of_cube_bounds' {C nu : ℝ} (hC : 0 < C)
    (hnu : 0 < nu) (P : ProbabilityMeasure (ShellSeq d)) (l L m n : ℕ) (Pvec : BlockVec d)
    {ι : Type*} (grid : Finset ι) (hne : grid.Nonempty) (hcard : 2 ≤ grid.card)
    (W : ι → ShellSeq d → ℝ) (Wbar : ShellSeq d → ℝ)
    (hWbar : ∀ omega, Wbar omega = grid.sup' hne (fun i => W i omega))
    (hWnn : ∀ i ∈ grid, ∀ omega, 0 ≤ W i omega)
    (hcube : ∀ i ∈ grid,
      IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma 1) (W i)
        (localizationAverageWbarCubeAmplitude C nu l L Pvec))
    (hcardle : (grid.card : ℝ) ≤ (3 : ℝ) ^ ((d : ℝ) * ((m - n : ℕ) : ℝ))) :
    IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma 1) Wbar
      (localizationAverageWbarAmplitude (3 * (d : ℝ) * Real.log 3 * C) nu l L m n Pvec) :=
  localizationAverage_wbar_bound_of_cube_bounds (d := d) P l L m n Pvec grid hne hcard W Wbar
    hWbar hWnn hcube
    (localizationAverage_wbar_amplitude_le (d := d) hC hnu hcard l L m n Pvec hcardle)

/-! ## The final `ν^{-3}` form -/

/-- **The amplitude bookkeeping of the final weakening**: under the
standing assumption `ν ∈ (0,1]`, the raw `ν^{-1}` amplitude is dominated by the envelope amplitude
at the enlarged constant `orliczProductConst 1 1 * C`.  The enlargement is the
printed one — `orliczProductConst 1 1 = 2^{1 + 1} = 4` is the constant of the
multiplication rule, and `C(d)` is enlarged here as in the first summand. -/
theorem localizationAverage_T2_rawAmplitude_le {C nu : ℝ} (hC : 0 < C) (hnu : 0 < nu)
    (hnu1 : nu ≤ 1) (l L m n : ℕ) (Pvec : BlockVec d) :
    localizationAverageT2RawAmplitude C nu l L m n Pvec ≤
      localizationAverageEnvelopeT2
        (SuperdiffusionCLT.Probability.orliczProductConst 1 1 * C) nu l L m n Pvec := by
  have hdot : 0 ≤ blockVecDot Pvec Pvec :=
    SuperdiffusionCLT.Section2.Carriers.blockVecDot_self_nonneg Pvec
  have hmax : 0 ≤ max 1 (l : ℝ) * max 1 (L : ℝ) * max 1 ((m - n : ℕ) : ℝ) :=
    mul_nonneg (mul_nonneg (le_trans zero_le_one (le_max_left _ _))
      (le_trans zero_le_one (le_max_left _ _)))
      (le_trans zero_le_one (le_max_left _ _))
  have hpow : nu ^ (-(1 : ℝ)) ≤ nu ^ (-(3 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_ge hnu hnu1 (by norm_num)
  have hK : 0 ≤ (SuperdiffusionCLT.Probability.orliczProductConst 1 1 * C) *
      blockVecDot Pvec Pvec *
      (max 1 (l : ℝ) * max 1 (L : ℝ) * max 1 ((m - n : ℕ) : ℝ) *
        localizationAverageNormalisedAmplitude d m l) :=
    mul_nonneg
      (mul_nonneg
        (mul_nonneg (SuperdiffusionCLT.Probability.orliczProductConst_pos 1 1).le hC.le)
        hdot)
      (mul_nonneg hmax (by
        unfold localizationAverageNormalisedAmplitude
        exact (Real.rpow_pos_of_pos (by norm_num) _).le))
  unfold localizationAverageT2RawAmplitude localizationAverageWbarAmplitude
  unfold localizationAverageEnvelopeT2
  rw [show SuperdiffusionCLT.Probability.orliczProductConst 1 1 *
        (C * nu ^ (-(1 : ℝ)) * blockVecDot Pvec Pvec *
          (max 1 (l : ℝ) * max 1 (L : ℝ) * max 1 ((m - n : ℕ) : ℝ)) *
          localizationAverageNormalisedAmplitude d m l) =
      ((SuperdiffusionCLT.Probability.orliczProductConst 1 1 * C) *
        blockVecDot Pvec Pvec *
        (max 1 (l : ℝ) * max 1 (L : ℝ) * max 1 ((m - n : ℕ) : ℝ) *
          localizationAverageNormalisedAmplitude d m l)) * nu ^ (-(1 : ℝ)) from by ring,
    show (SuperdiffusionCLT.Probability.orliczProductConst 1 1 * C) *
        nu ^ (-(3 : ℝ)) * blockVecDot Pvec Pvec *
        (max 1 (l : ℝ) * max 1 (L : ℝ) * max 1 ((m - n : ℕ) : ℝ) *
          (3 : ℝ) ^ (-((d : ℝ) / 2 * ((m - l : ℕ) : ℝ)))) =
      ((SuperdiffusionCLT.Probability.orliczProductConst 1 1 * C) *
        blockVecDot Pvec Pvec *
        (max 1 (l : ℝ) * max 1 (L : ℝ) * max 1 ((m - n : ℕ) : ℝ) *
          (3 : ℝ) ^ (-((d : ℝ) / 2 * ((m - l : ℕ) : ℝ))))) * nu ^ (-(3 : ℝ))
      from by ring]
  exact mul_le_mul_of_nonneg_left hpow hK

end SuperdiffusionCLT.Section2.Localization

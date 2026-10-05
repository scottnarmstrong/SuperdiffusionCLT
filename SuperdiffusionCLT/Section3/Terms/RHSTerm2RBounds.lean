/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.RHSTerm2Displays
public import Mathlib.MeasureTheory.Integral.MeanInequalities
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-!
# `e.RHS.term2.R.bounds`

The display `e.RHS.term2.R.bounds` in the proof of `l.RHS.term2` reads

`E[‖R‖²_{L̲²(cu_m)}]^{1/2} + 3^ℓ E[‖∇R‖²_{L̲²(cu_m)}]^{1/2} ≤ C L' |p|`

for the transported field `R = (k_{L'} − k_ℓ)ᵗ ∇w`.  The paper obtains it as follows:
"Combining this with `e.nablaw.Lt` and the product rule gives", where "this" is the pair
of annealed `L̲⁴` bounds on the stream increment displayed just before.

The ingredients of that combination are collected here.  Its conclusion is the rendered
hypothesis `hRbounds` of `l.RHS.term2` verbatim, the form that
`l_RHS_term2_constFirst` consumes.

## The two Hölder steps

The print's "Hölder's inequality" is used twice, at the same pair of exponents.

* On the cube, `(4,4) → 2`: `cubeLpENorm_two_le_mul_four` and its product-rule
  form `cubeLpENorm_two_le_mul_four_add`.
* In the sample, `(2,2)`: `lintegral_sq_rpow_le_mul_of_le_mul`, with Minkowski
  `lintegral_sq_rpow_le_add_of_le_add` for the two summands of the product rule;
  `toReal_annealed_le_mul` and `toReal_annealed_le_mul_add` are the `.toReal`
  forms in which the annealed roots of the displays are written.

The closing arithmetic uses the scale facts
`(L' − ℓ)^{1/2} h^{1/2} ≤ L'`, `h^{1/2} ≤ L'` and `3^ℓ 3^{-ℓ'} ≤ 1`, the last
two from `ellPrime + h = m`, `L' = m + 2a` and `ℓ < ℓ'`.

## Composing with `e.nablaw.Lt`

The paper states `e.nablaw.Lt` as an `O_{Γ₂}(C|p|)` bound on `L̲⁸(cu_m)`
norms, not as an annealed `L̲⁴` bound.  Three lemmas here compose the two:

* `cubeLpENorm_vecNorm_eq_vecCubeLpENorm` rewrites the vector-field norm of
  `∇w` as the scalar-density norm of `|∇w|`;
* `cubeLpENorm_mono_exponent` passes from `L̲⁸(cu_m)` to `L̲⁴(cu_m)`, the
  normalized cube measure being a probability measure;
* `toReal_annealed_four_le_of_isBigO` turns `|Z| ≤ O_{Γ₂}(A)` into
  `E[N⁴]^{1/4} ≤ 2 γ₂ A` together with the finiteness of the annealed fourth
  moment, `γ₂` the Chapter 4 moment constant.

Applied to the first clause of `e.nablaw.Lt` at amplitude `C|p|h^{1/2}` and to
its second clause at amplitude `C|p|3^{-ℓ'}`, these three give the hypotheses
`hWa`, `hHa`, `hWGfin` and `hWHfin` of the combination.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Terms

open MeasureTheory
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section3.ResponseFields
open SuperdiffusionCLT.Section3.Setup
open Homogenization
open Homogenization.Book.Ch02
open scoped ENNReal

noncomputable section

/-! ## Hölder and Minkowski in the sample -/

/-- Cauchy-Schwarz in the sample at the annealed exponents of the display:
if a nonnegative quantity is dominated pointwise in `omega` by a product, its
annealed `L²` root is dominated by the product of the two annealed `L⁴` roots. -/
theorem lintegral_sq_rpow_le_mul_of_le_mul {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} {N A B : Omega → ℝ≥0∞} (hA : AEMeasurable A mu)
    (hB : AEMeasurable B mu) (hN : ∀ omega, N omega ≤ A omega * B omega) :
    (∫⁻ omega, N omega ^ (2 : ℕ) ∂mu) ^ ((1 : ℝ) / 2) ≤
      (∫⁻ omega, A omega ^ (4 : ℕ) ∂mu) ^ ((1 : ℝ) / 4) *
        (∫⁻ omega, B omega ^ (4 : ℕ) ∂mu) ^ ((1 : ℝ) / 4) := by
  have hpow : ∀ x : ℝ≥0∞, (x ^ (2 : ℕ)) ^ (2 : ℝ) = x ^ (4 : ℕ) := by
    intro x
    rw [← ENNReal.rpow_natCast x 2, ← ENNReal.rpow_mul]
    rw [← ENNReal.rpow_natCast x 4]
    norm_num
  have hconj : (2 : ℝ).HolderConjugate 2 := by
    rw [Real.holderConjugate_iff]
    constructor
    · norm_num
    · norm_num
  have hmono : (∫⁻ omega, N omega ^ (2 : ℕ) ∂mu) ≤
      ∫⁻ omega, ((fun o => A o ^ (2 : ℕ)) * fun o => B o ^ (2 : ℕ)) omega ∂mu := by
    refine lintegral_mono fun omega => ?_
    calc N omega ^ (2 : ℕ) ≤ (A omega * B omega) ^ (2 : ℕ) := by
          exact pow_le_pow_left' (hN omega) 2
      _ = A omega ^ (2 : ℕ) * B omega ^ (2 : ℕ) := mul_pow _ _ 2
  have hholder := ENNReal.lintegral_mul_le_Lp_mul_Lq mu hconj
    (f := fun o => A o ^ (2 : ℕ)) (g := fun o => B o ^ (2 : ℕ))
    (hA.pow_const 2) (hB.pow_const 2)
  have hstep : (∫⁻ omega, N omega ^ (2 : ℕ) ∂mu) ≤
      (∫⁻ omega, A omega ^ (4 : ℕ) ∂mu) ^ ((1 : ℝ) / 2) *
        (∫⁻ omega, B omega ^ (4 : ℕ) ∂mu) ^ ((1 : ℝ) / 2) := by
    refine le_trans hmono (le_trans hholder (le_of_eq ?_))
    simp only [hpow]
  refine le_trans (ENNReal.rpow_le_rpow hstep (by norm_num)) (le_of_eq ?_)
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2),
    ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
  norm_num

/-- Minkowski in the sample: a nonnegative quantity dominated pointwise in
`omega` by a sum has its annealed `L²` root dominated by the sum of the two
annealed `L²` roots. -/
theorem lintegral_sq_rpow_le_add_of_le_add {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} {N F G : Omega → ℝ≥0∞} (hF : AEMeasurable F mu)
    (hG : AEMeasurable G mu) (hN : ∀ omega, N omega ≤ F omega + G omega) :
    (∫⁻ omega, N omega ^ (2 : ℕ) ∂mu) ^ ((1 : ℝ) / 2) ≤
      (∫⁻ omega, F omega ^ (2 : ℕ) ∂mu) ^ ((1 : ℝ) / 2) +
        (∫⁻ omega, G omega ^ (2 : ℕ) ∂mu) ^ ((1 : ℝ) / 2) := by
  have hcast : ∀ x : ℝ≥0∞, x ^ (2 : ℝ) = x ^ (2 : ℕ) := by
    intro x
    rw [← ENNReal.rpow_natCast x 2]
    norm_num
  have hmink := ENNReal.lintegral_Lp_add_le (μ := mu) (p := 2) hF hG (by norm_num)
  simp only [Pi.add_apply, hcast] at hmink
  have hle : (∫⁻ omega, N omega ^ (2 : ℕ) ∂mu) ≤
      ∫⁻ omega, (F omega + G omega) ^ (2 : ℕ) ∂mu :=
    lintegral_mono fun omega => pow_le_pow_left' (hN omega) 2
  exact le_trans (ENNReal.rpow_le_rpow hle (by norm_num)) hmink

private theorem rpow_four_ne_top {X Y : ℝ≥0∞} (hX : X ≠ ⊤) (hY : Y ≠ ⊤) :
    X ^ ((1 : ℝ) / 4) * Y ^ ((1 : ℝ) / 4) ≠ ⊤ :=
  ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hX)
    (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hY)

/-- Finiteness of the annealed `L²` root under the hypotheses of
`lintegral_sq_rpow_le_mul_of_le_mul`. -/
theorem lintegral_sq_rpow_ne_top_of_le_mul {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} {N A B : Omega → ℝ≥0∞} (hA : AEMeasurable A mu)
    (hB : AEMeasurable B mu) (hN : ∀ omega, N omega ≤ A omega * B omega)
    (hfinA : (∫⁻ omega, A omega ^ (4 : ℕ) ∂mu) ≠ ⊤)
    (hfinB : (∫⁻ omega, B omega ^ (4 : ℕ) ∂mu) ≠ ⊤) :
    (∫⁻ omega, N omega ^ (2 : ℕ) ∂mu) ^ ((1 : ℝ) / 2) ≠ ⊤ :=
  ne_top_of_le_ne_top (rpow_four_ne_top hfinA hfinB)
    (lintegral_sq_rpow_le_mul_of_le_mul hA hB hN)

/-- The real form of `lintegral_sq_rpow_le_mul_of_le_mul`, in the `.toReal`
shape in which the annealed roots of the display are written. -/
theorem toReal_annealed_le_mul {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} {N A B : Omega → ℝ≥0∞} (hA : AEMeasurable A mu)
    (hB : AEMeasurable B mu) (hN : ∀ omega, N omega ≤ A omega * B omega)
    (hfinA : (∫⁻ omega, A omega ^ (4 : ℕ) ∂mu) ≠ ⊤)
    (hfinB : (∫⁻ omega, B omega ^ (4 : ℕ) ∂mu) ≠ ⊤) :
    (∫⁻ omega, N omega ^ (2 : ℕ) ∂mu).toReal ^ ((1 : ℝ) / 2) ≤
      (∫⁻ omega, A omega ^ (4 : ℕ) ∂mu).toReal ^ ((1 : ℝ) / 4) *
        (∫⁻ omega, B omega ^ (4 : ℕ) ∂mu).toReal ^ ((1 : ℝ) / 4) := by
  have hmono := ENNReal.toReal_mono (rpow_four_ne_top hfinA hfinB)
    (lintegral_sq_rpow_le_mul_of_le_mul hA hB hN)
  rwa [← ENNReal.toReal_rpow, ENNReal.toReal_mul, ← ENNReal.toReal_rpow,
    ← ENNReal.toReal_rpow] at hmono

/-- The two steps combined in real form: a pointwise domination by a sum of two
products gives the sum of two products of annealed `L⁴` roots.  This is the
shape in which the product rule is used for the Jacobian of `R`. -/
theorem toReal_annealed_le_mul_add {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} {N A B A' B' : Omega → ℝ≥0∞} (hA : AEMeasurable A mu)
    (hB : AEMeasurable B mu) (hA' : AEMeasurable A' mu) (hB' : AEMeasurable B' mu)
    (hN : ∀ omega, N omega ≤ A omega * B omega + A' omega * B' omega)
    (hfinA : (∫⁻ omega, A omega ^ (4 : ℕ) ∂mu) ≠ ⊤)
    (hfinB : (∫⁻ omega, B omega ^ (4 : ℕ) ∂mu) ≠ ⊤)
    (hfinA' : (∫⁻ omega, A' omega ^ (4 : ℕ) ∂mu) ≠ ⊤)
    (hfinB' : (∫⁻ omega, B' omega ^ (4 : ℕ) ∂mu) ≠ ⊤) :
    (∫⁻ omega, N omega ^ (2 : ℕ) ∂mu).toReal ^ ((1 : ℝ) / 2) ≤
      (∫⁻ omega, A omega ^ (4 : ℕ) ∂mu).toReal ^ ((1 : ℝ) / 4) *
          (∫⁻ omega, B omega ^ (4 : ℕ) ∂mu).toReal ^ ((1 : ℝ) / 4) +
        (∫⁻ omega, A' omega ^ (4 : ℕ) ∂mu).toReal ^ ((1 : ℝ) / 4) *
          (∫⁻ omega, B' omega ^ (4 : ℕ) ∂mu).toReal ^ ((1 : ℝ) / 4) := by
  have hP : (∫⁻ omega, (A omega * B omega) ^ (2 : ℕ) ∂mu) ^ ((1 : ℝ) / 2) ≠ ⊤ :=
    lintegral_sq_rpow_ne_top_of_le_mul hA hB (fun _ => le_rfl) hfinA hfinB
  have hQ : (∫⁻ omega, (A' omega * B' omega) ^ (2 : ℕ) ∂mu) ^ ((1 : ℝ) / 2) ≠ ⊤ :=
    lintegral_sq_rpow_ne_top_of_le_mul hA' hB' (fun _ => le_rfl) hfinA' hfinB'
  have hstep := lintegral_sq_rpow_le_add_of_le_add (N := N)
    (F := fun omega => A omega * B omega) (G := fun omega => A' omega * B' omega)
    (hA.mul hB) (hA'.mul hB') hN
  have hmono := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hP, hQ⟩) hstep
  rw [ENNReal.toReal_add hP hQ, ← ENNReal.toReal_rpow, ← ENNReal.toReal_rpow,
    ← ENNReal.toReal_rpow] at hmono
  refine le_trans hmono (add_le_add ?_ ?_)
  · exact toReal_annealed_le_mul hA hB (fun _ => le_rfl) hfinA hfinB
  · exact toReal_annealed_le_mul hA' hB' (fun _ => le_rfl) hfinA' hfinB'

/-! ## Hölder on the cube -/

/-- Hölder `(4,4) → 2` on the cube `Q`: a field dominated pointwise in Euclidean
magnitude by a product of two nonnegative densities has its `L̲²(Q)` norm
dominated by the product of the two `L̲⁴(Q)` norms. -/
theorem cubeLpENorm_two_le_mul_four {d : ℕ} {E : Type*} [NormedAddCommGroup E]
    {Q : TriadicCube d} {f : Vec d → E} {u v : Vec d → ℝ}
    (hu0 : ∀ x, 0 ≤ u x) (hv0 : ∀ x, 0 ≤ v x)
    (hum : AEStronglyMeasurable u (normalizedCubeMeasure Q))
    (hvm : AEStronglyMeasurable v (normalizedCubeMeasure Q))
    (hfm : AEStronglyMeasurable f (normalizedCubeMeasure Q))
    (hf : ∀ x, ‖f x‖ ≤ u x * v x) :
    SuperdiffusionCLT.Section2.Norms.cubeLpENorm Q 2 f ≤
      SuperdiffusionCLT.Section2.Norms.cubeLpENorm Q 4 u *
        SuperdiffusionCLT.Section2.Norms.cubeLpENorm Q 4 v := by
  have : ENNReal.HolderTriple 4 4 2 := ⟨by
    rw [show (4 : ℝ≥0∞) = 2 * 2 by norm_num, ENNReal.mul_inv (by norm_num) (by norm_num),
      ← two_mul, ← mul_assoc, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]⟩
  have hmono : SuperdiffusionCLT.Section2.Norms.cubeLpENorm Q 2 f ≤
      SuperdiffusionCLT.Section2.Norms.cubeLpENorm Q 2 (fun x => u x * v x) := by
    refine SuperdiffusionCLT.Section2.Norms.cubeLpENorm_mono_enorm hfm (fun x => ?_)
    rw [show ‖u x * v x‖ = u x * v x from abs_of_nonneg (mul_nonneg (hu0 x) (hv0 x))]
    exact hf x
  refine le_trans hmono ?_
  rw [SuperdiffusionCLT.Section2.Norms.cubeLpENorm,
    show (fun x => u x * v x) = u • v from rfl]
  exact eLpNorm_smul_le_mul_eLpNorm hum hvm

/-- The product-rule form of `cubeLpENorm_two_le_mul_four`: the pointwise bound
for the Jacobian of a product is a sum of two products of
densities. -/
theorem cubeLpENorm_two_le_mul_four_add {d : ℕ} {E : Type*} [NormedAddCommGroup E]
    {Q : TriadicCube d} {f : Vec d → E} {u v u' v' : Vec d → ℝ}
    (hu0 : ∀ x, 0 ≤ u x) (hv0 : ∀ x, 0 ≤ v x) (hu0' : ∀ x, 0 ≤ u' x)
    (hv0' : ∀ x, 0 ≤ v' x)
    (hum : AEStronglyMeasurable u (normalizedCubeMeasure Q))
    (hvm : AEStronglyMeasurable v (normalizedCubeMeasure Q))
    (hum' : AEStronglyMeasurable u' (normalizedCubeMeasure Q))
    (hvm' : AEStronglyMeasurable v' (normalizedCubeMeasure Q))
    (hfm : AEStronglyMeasurable f (normalizedCubeMeasure Q))
    (hf : ∀ x, ‖f x‖ ≤ u x * v x + u' x * v' x) :
    SuperdiffusionCLT.Section2.Norms.cubeLpENorm Q 2 f ≤
      SuperdiffusionCLT.Section2.Norms.cubeLpENorm Q 4 u *
          SuperdiffusionCLT.Section2.Norms.cubeLpENorm Q 4 v +
        SuperdiffusionCLT.Section2.Norms.cubeLpENorm Q 4 u' *
          SuperdiffusionCLT.Section2.Norms.cubeLpENorm Q 4 v' := by
  have hmono : SuperdiffusionCLT.Section2.Norms.cubeLpENorm Q 2 f ≤
      SuperdiffusionCLT.Section2.Norms.cubeLpENorm Q 2
        ((fun x => u x * v x) + fun x => u' x * v' x) := by
    refine SuperdiffusionCLT.Section2.Norms.cubeLpENorm_mono_enorm hfm (fun x => ?_)
    have hnn : (0 : ℝ) ≤ u x * v x + u' x * v' x :=
      add_nonneg (mul_nonneg (hu0 x) (hv0 x)) (mul_nonneg (hu0' x) (hv0' x))
    show ‖f x‖ ≤ ‖u x * v x + u' x * v' x‖
    rw [show ‖u x * v x + u' x * v' x‖ = u x * v x + u' x * v' x from abs_of_nonneg hnn]
    exact hf x
  refine le_trans hmono (le_trans (SuperdiffusionCLT.Section2.Norms.cubeLpENorm_add_le
    (by norm_num) (hum.mul hvm) (hum'.mul hvm')) (add_le_add ?_ ?_))
  · exact cubeLpENorm_two_le_mul_four hu0 hv0 hum hvm (hum.mul hvm) (fun x => le_of_eq
      (abs_of_nonneg (mul_nonneg (hu0 x) (hv0 x))))
  · exact cubeLpENorm_two_le_mul_four hu0' hv0' hum' hvm' (hum'.mul hvm') (fun x => le_of_eq
      (abs_of_nonneg (mul_nonneg (hu0' x) (hv0' x))))

/-! ## The bridge from `O_{Γ₂}` to the annealed `L̲⁴` inputs -/

/-- The scalar density form of `vecCubeLpENorm`: the `L̲^q(Q)` norm of a vector
field is the `L̲^q(Q)` norm of its Euclidean magnitude. -/
theorem cubeLpENorm_vecNorm_eq_vecCubeLpENorm {d : ℕ} (Q : TriadicCube d) (q : ℝ≥0∞)
    (F : Vec d → Vec d)
    (hF : AEStronglyMeasurable (hilbertifyVecField F)
      (normalizedCubeMeasure Q)) :
    SuperdiffusionCLT.Section2.Norms.cubeLpENorm Q q (fun x => vecNorm (F x)) =
      SuperdiffusionCLT.Section3.ResponseFields.vecCubeLpENorm Q q F := by
  have hF' : AEStronglyMeasurable (fun x => vecNorm (F x)) (normalizedCubeMeasure Q) := by
    have h := hF.norm
    refine h.congr (Filter.Eventually.of_forall fun x => ?_)
    exact SuperdiffusionCLT.Section3.ResponseFields.norm_hilbertifyVecField_apply F x
  refine le_antisymm (SuperdiffusionCLT.Section2.Norms.cubeLpENorm_mono_enorm hF'
    (fun x => ?_)) (SuperdiffusionCLT.Section2.Norms.cubeLpENorm_mono_enorm hF
    (fun x => ?_))
  · exact le_of_eq (abs_of_nonneg (vecNorm_nonneg (F x)))
  · exact le_of_eq (abs_of_nonneg (vecNorm_nonneg (F x))).symm

/-- On a cube the normalized `L̲^q` norms increase with the exponent, because
the normalized cube measure is a probability measure.  This is the step that
turns the `L̲⁸(cu_m)` clauses of `e.nablaw.Lt` into the
`L̲⁴(cu_m)` densities that the Hölder pairing consumes. -/
theorem cubeLpENorm_mono_exponent {d : ℕ} {E : Type*} [NormedAddCommGroup E]
    (Q : TriadicCube d) {q r : ℝ≥0∞} (hqr : q ≤ r) {f : Vec d → E}
    (_hf : AEStronglyMeasurable f (normalizedCubeMeasure Q)) :
    SuperdiffusionCLT.Section2.Norms.cubeLpENorm Q q f ≤
      SuperdiffusionCLT.Section2.Norms.cubeLpENorm Q r f := by
  have : IsProbabilityMeasure (normalizedCubeMeasure Q) :=
    ⟨normalizedCubeMeasure_apply_univ Q⟩
  exact eLpNorm_le_eLpNorm_of_exponent_le hqr

/-- **From `O_{Γ₂}(A)` to the annealed `L⁴` root.**  A nonnegative quantity
dominated in `omega` by a random variable `Z` with `|Z| ≤ O_{Γ₂}(A)` — the shape
in which `e.nablaw.Lt` and the clauses of the stream
increment gate are stated — has finite annealed fourth moment, with

`E[N⁴]^{1/4} ≤ 2 γ₂ A`,

`γ₂ = gammaMomentConst 2` the Chapter 4 moment constant.  The factor `2` is the
value `4^{1/2}` of the moment growth at the fourth moment.  This is the bridge
that turns a printed `O_{Γ₂}` bound into an input of
that combination. -/
theorem toReal_annealed_four_le_of_isBigO
    {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    [IsProbabilityMeasure mu] {N : Omega → ℝ≥0∞} {Z : Omega → ℝ} {A : ℝ}
    (hA : 0 < A) (hZm : AEMeasurable Z mu)
    (hZ : IndependentSums.IsBigO mu (IndependentSums.gammaSigma 2) Z A)
    (hN : ∀ omega, N omega ≤ ENNReal.ofReal (Z omega)) :
    (∫⁻ omega, N omega ^ (4 : ℕ) ∂mu) ≠ ⊤ ∧
      (∫⁻ omega, N omega ^ (4 : ℕ) ∂mu).toReal ^ ((1 : ℝ) / 4) ≤
        2 * IndependentSums.gammaMomentConst 2 * A := by
  have hgrowth := IndependentSums.hasGammaMomentGrowthWith_of_isBigO_gammaSigma
    (μ := mu) (σ := 2) (K := A) (by norm_num) hA hZm hZ
  obtain ⟨hint, hbound⟩ := hgrowth (p := 4) (by norm_num)
  have hM0 : (0 : ℝ) ≤ IndependentSums.gammaMomentConst 2 * A :=
    mul_nonneg (IndependentSums.gammaMomentConst_pos (by norm_num)).le hA.le
  have h4 : (4 : ℝ) ^ ((2 : ℝ)⁻¹) = 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, ← Real.rpow_natCast (2 : ℝ) 2,
      ← Real.rpow_mul (by norm_num)]
    norm_num
  rw [h4] at hbound
  have hle : (∫⁻ omega, N omega ^ (4 : ℕ) ∂mu) ≤
      ENNReal.ofReal (∫ omega, |Z omega| ^ (4 : ℝ) ∂mu) := by
    rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun omega => Real.rpow_nonneg (abs_nonneg _) _)]
    refine lintegral_mono fun omega => ?_
    calc N omega ^ (4 : ℕ) ≤ ENNReal.ofReal (Z omega) ^ (4 : ℕ) :=
          pow_le_pow_left' (hN omega) 4
      _ ≤ ENNReal.ofReal (|Z omega|) ^ (4 : ℕ) :=
          pow_le_pow_left' (ENNReal.ofReal_le_ofReal (le_abs_self _)) 4
      _ = ENNReal.ofReal (|Z omega| ^ (4 : ℕ)) := (ENNReal.ofReal_pow (abs_nonneg _) 4).symm
      _ = ENNReal.ofReal (|Z omega| ^ (4 : ℝ)) := by
          rw [← Real.rpow_natCast (|Z omega|) 4]
          norm_num
  refine ⟨ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle, ?_⟩
  have hreal : (∫⁻ omega, N omega ^ (4 : ℕ) ∂mu).toReal ≤
      (IndependentSums.gammaMomentConst 2 * A * 2) ^ (4 : ℝ) := by
    have h1 := ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
    rw [ENNReal.toReal_ofReal (integral_nonneg fun omega =>
      Real.rpow_nonneg (abs_nonneg _) _)] at h1
    exact le_trans h1 hbound
  refine le_trans (Real.rpow_le_rpow ENNReal.toReal_nonneg hreal
    (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 4)) (le_of_eq ?_)
  rw [← Real.rpow_mul (by linarith only [hM0] : (0 : ℝ) ≤
    IndependentSums.gammaMomentConst 2 * A * 2)]
  norm_num
  ring

/-! ## The scale arithmetic of the closing step -/

/-- **The canonical choice of the density `KN`.**  With `KN omega x` the
operator norm of `(k_{L'} − k_ℓ)(x)` and `WG omega x = |∇w(x)|`, the hypothesis
`hRpt` of that combination — the pointwise half of the print's
`R = (k_{L'} − k_ℓ)ᵗ∇w` bound — is the operator-norm
inequality of Chapter 2, with no further input. -/
theorem vecNorm_matVecMul_coefficientCutoff_sub_le {d : ℕ} (nu : ℝ) (L ell : ℕ)
    (omega : ShellSeq d) (g : Vec d → Vec d) (x : Vec d) :
    vecNorm (matVecMul ((coefficientCutoff nu omega L).toCoeffField x -
        (coefficientCutoff nu omega ell).toCoeffField x) (g x)) ≤
      matrixOperatorNorm ((coefficientCutoff nu omega L).toCoeffField x -
          (coefficientCutoff nu omega ell).toCoeffField x) * vecNorm (g x) :=
  vecNorm_matVecMul_le_matrixOperatorNorm_mul_vecNorm _ _

/-! ## `e.RHS.term2.R.bounds` -/

end

end SuperdiffusionCLT.Section3.Terms

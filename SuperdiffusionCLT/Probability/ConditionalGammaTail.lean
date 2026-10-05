/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Homogenization.Probability.IndependentSums.WeakOrlicz
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

/-!
# A conditional weak-Orlicz tail calculus for `Γ_σ`

The unconditional weak-Orlicz relation of
`Homogenization.Probability.IndependentSums.WeakOrlicz` reads

`X ≤ O_Ψ(A)` iff `μ {X > A t} ≤ (Ψ t)⁻¹` for every `t ≥ 1`,

and its symmetric form `X = O_Ψ(A)` is the same bound for `|X|`. Every available
concentration theorem for independent sums in this tree is stated for that
*unconditional* relation, on a fixed probability measure and with a deterministic
envelope `A`.

The argument of the paper instead needs a bound that
holds *conditionally on a sub-sigma-field* `m`: conditionally on `F_>`, the
variables `X_z = W_z · (…)` with `m`-measurable `W_z` are independent, and their
conditional tails are small. Unconditional independence is genuinely false for
these products, so the conditioning cannot be dropped; this file supplies the
conditional predicate and the calculus that surrounds it.

## The predicate

`CondIsBigOWith μ m Ψ X θ` is the conditional analogue of
`IndependentSums.IsBigOWith`: for every `t ≥ 1`, `μ`-almost every `ω`, the
*conditional* probability of the tail event `{X > θ t}` given `m`, i.e. the
conditional expectation of its indicator, is at most `(Ψ t)⁻¹`; here `μ` is the
measure on the ambient space and `m` the sub-sigma-field it is conditioned on. The
threshold is `θ ω * t` with `θ` an envelope, so that the product step below can
absorb a prefactor `W` by replacing `θ` with `|W| θ`. Taking the constant envelope
`θ ≡ A` recovers the unconditional relation exactly
(`isBigOEnvelopeWith_const_iff_isBigOWith`).

## Main results

* `CondIsBigOWith.mono_scale`, `CondIsBigOWith.of_le`, `CondIsBigOWith.const_mul_left`:
  the elementary monotonicity rules, mirroring the unconditional ones.
* `IsBigOEnvelopeWith.of_condIsBigOWith`: **the tower step.** A conditional bound
  at an envelope `θ` integrates, by the tower property `∫ μ[f|m] = ∫ f`, to the
  unconditional bound `IsBigOEnvelopeWith μ Ψ X θ` at the same envelope; at a
  constant envelope this is exactly `IndependentSums.IsBigOWith μ Ψ X A`
  (`isBigO_of_condIsBigO`).
* `CondIsBigO.mul_left`: **the product step.** If `Y` has a conditional bound at
  `θ` then `W · Y` has one at `|W| θ`. The key point is the pointwise tail
  inclusion `{|W Y| > |W| θ t} ⊆ {|Y| > θ t}`; measurability of `W` is assumed
  only to keep the two tail events measurable.
* `CondIsBigOWith.add`: the conditional union bound, the engine a conditional re-run of
  the triangle inequality would consume.

## The conditional concentration step is *not* obtained here

The concentration step of the paper is a conditional
independent-sum concentration: conditionally on `m`, the summands are
independent, have conditional `Γ_σ` tails, and their normalized average has a
conditional `Γ_σ` tail. It is **not** reduced to the unconditional theorem
in this file. The obstruction is not book-keeping but available API, and it is
recorded here so that no consumer mistakes an unconditional statement for the
conditional one:

1. The unconditional theorem
   `isBigO_gammaSigma_finsetAverage_of_iIndepFun_of_isBigO_of_integral_eq_zero`
   (and its exponent-regime and `σ < 1` variants) is a statement about a *fixed*
   probability measure and a *fixed* `ProbabilityTheory.iIndepFun`. To use it
   fiberwise one must first turn the conditional statement into an honest measure
   on the fibers, i.e. into the conditional kernel `condExpKernel μ m`, which
   requires `StandardBorelSpace Ω` — an instance the abstract carrier of this
   calculus does not have.
2. Even with the kernel, Mathlib's conditional independence is
   `Kernel.iIndepFun X (condExpKernel μ m) (μ.trim hm)`, whose defining
   `∀ s f, ∀ᵐ ω, …` cannot be exchanged into the per-fiber
   `∀ᵐ ω, ProbabilityTheory.iIndepFun X (condExpKernel μ m ω)` that the
   unconditional theorem needs: the exceptional null set depends on the finite
   family and on its measurable sets, and no lemma in this Mathlib performs the
   exchange (`Kernel.iIndepFun_iff_measure_inter_preimage_eq_mul` exposes exactly
   the non-exchanged form). The needed bridge is not available in the library.
3. The envelope in the conditional statement is a function, while the unconditional
   theorem takes a *single constant* envelope `K` for all summands. Passing from a
   fiberwise random envelope to that constant requires the fact that an
   `m`-measurable function is almost surely constant on the fibers of
   `condExpKernel μ m`, which is not available here.
4. The unconditional theorem's centring hypothesis `∀ i, ∫ X i ∂μ = 0` is *not* preserved
   by conditioning: it becomes the strictly stronger conditional centring
   `μ[X i | m] =ᵐ 0`, which conditional independence alone does not give.

Consequently the honest conditional concentration statement must carry the
conditional centring as an extra premise; this file proves the conditional
subadditivity step (`CondIsBigOWith.add`) that such a re-run would start from, and leaves the
moment/concentration part to a later file that first lands the per-fiber
independence bridge.
-/

@[expose] public section

namespace SuperdiffusionCLT.Probability

open MeasureTheory

open Homogenization

/- `m` is the sub-sigma-field and `mΩ` the ambient one; declaring `m` first makes
`mΩ` the instance that `Measure Ω` elaborates against (the Mathlib convention for
conditional expectation). -/
variable {Ω : Type*} {m mΩ : MeasurableSpace Ω}

/-! ## Random-threshold tail sets -/

/-- The upper-tail set `{θ t < X}` with a random threshold `θ t`. -/
def upperTailSet (X : Ω → ℝ) (θ : Ω → ℝ) (t : ℝ) : Set Ω :=
  {ω | θ ω * t < X ω}

@[simp] theorem mem_upperTailSet {X : Ω → ℝ} {θ : Ω → ℝ} {t : ℝ} {ω : Ω} :
    ω ∈ upperTailSet X θ t ↔ θ ω * t < X ω :=
  Iff.rfl

/-- At a constant envelope the random-threshold tail set is the unconditional
one: this is the sense in which the conditional predicate below mirrors
`IndependentSums.IsBigOWith`. -/
@[simp] theorem upperTailSet_const (X : Ω → ℝ) (A t : ℝ) :
    upperTailSet X (fun _ => A) t = IndependentSums.upperTailEvent X (A * t) :=
  rfl

theorem upperTailSet_mono_threshold {X : Ω → ℝ} {θ φ : Ω → ℝ} {t : ℝ}
    (h : ∀ ω, θ ω ≤ φ ω) (ht : 0 ≤ t) :
    upperTailSet X φ t ⊆ upperTailSet X θ t := by
  intro ω hω
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right (h ω) ht) hω

/-- `abs` of a measurable real function is measurable. -/
theorem measurable_abs_comp {f : Ω → ℝ} (hf : Measurable f) :
    Measurable fun ω => |f ω| :=
  continuous_abs.measurable.comp hf

/-! ## Pointwise indicator inequalities -/

/-- The inclusion `s ⊆ u`, as a pointwise inequality of indicators of a
nonnegative weight. -/
theorem indicator_le_indicator_of_subset {s u : Set Ω} (h : s ⊆ u) {f : Ω → ℝ} (hf : 0 ≤ f) :
    Set.indicator s f ≤ Set.indicator u f := by
  intro ω
  by_cases hω : ω ∈ s
  · rw [Set.indicator_of_mem hω f, Set.indicator_of_mem (h hω) f]
  · have hS : Set.indicator s f ω = (0 : ℝ) := Set.indicator_of_notMem hω f
    have hU : (0 : ℝ) ≤ Set.indicator u f ω := Set.indicator_nonneg (fun _ _ => hf _) ω
    rw [hS]
    exact hU

/-- The pointwise inequality `1_{S} ≤ 1_s + 1_u` for any `S ⊆ s ∪ u`, with a
nonnegative weight. -/
theorem indicator_le_indicator_add {S s u : Set Ω} (h : S ⊆ s ∪ u) {f : Ω → ℝ} (hf : 0 ≤ f) :
    Set.indicator S f ≤ Set.indicator s f + Set.indicator u f := by
  intro ω
  simp only [Pi.add_apply]
  by_cases hω : ω ∈ S
  · have hS : Set.indicator S f ω = f ω := Set.indicator_of_mem hω f
    rcases h hω with hmem | hmem
    · have hs : Set.indicator s f ω = f ω := Set.indicator_of_mem hmem f
      have h0 : (0 : ℝ) ≤ Set.indicator u f ω := Set.indicator_nonneg (fun _ _ => hf _) ω
      linarith only [hS, hs, h0]
    · have hu : Set.indicator u f ω = f ω := Set.indicator_of_mem hmem f
      have h0 : (0 : ℝ) ≤ Set.indicator s f ω := Set.indicator_nonneg (fun _ _ => hf _) ω
      linarith only [hS, hu, h0]
  · have hS : Set.indicator S f ω = (0 : ℝ) := Set.indicator_of_notMem hω f
    have h0 : (0 : ℝ) ≤ Set.indicator s f ω + Set.indicator u f ω :=
      add_nonneg (Set.indicator_nonneg (fun _ _ => hf _) ω)
        (Set.indicator_nonneg (fun _ _ => hf _) ω)
    linarith only [hS, h0]

/-! ## The unconditional relation at a random envelope -/

/-- The unconditional weak-Orlicz relation at a random envelope `θ`, the
one-sided form. At a constant envelope this is `IndependentSums.IsBigOWith`. -/
def IsBigOEnvelopeWith (μ : Measure Ω) (Ψ : ℝ → ℝ) (X : Ω → ℝ) (θ : Ω → ℝ) : Prop :=
  ∀ ⦃t : ℝ⦄, 1 ≤ t → μ.real (upperTailSet X θ t) ≤ (Ψ t)⁻¹

/-- The symmetric unconditional relation at a random envelope `θ`, through `|X|`:
the random-envelope form of `IndependentSums.IsBigO`. -/
def IsBigOEnvelope (μ : Measure Ω) (Ψ : ℝ → ℝ) (X : Ω → ℝ) (θ : Ω → ℝ) : Prop :=
  IsBigOEnvelopeWith μ Ψ (fun ω => |X ω|) θ

theorem isBigOEnvelopeWith_const_iff_isBigOWith (μ : Measure Ω) (Ψ : ℝ → ℝ)
    (X : Ω → ℝ) (A : ℝ) :
    IsBigOEnvelopeWith μ Ψ X (fun _ => A) ↔ IndependentSums.IsBigOWith μ Ψ X A := by
  constructor
  · intro h t ht
    simpa only [IsBigOEnvelopeWith, upperTailSet_const] using h ht
  · intro h t ht
    simpa only [IsBigOEnvelopeWith, upperTailSet_const] using h ht

theorem isBigOEnvelope_const_iff_isBigO (μ : Measure Ω) (Ψ : ℝ → ℝ) (X : Ω → ℝ)
    (A : ℝ) :
    IsBigOEnvelope μ Ψ X (fun _ => A) ↔ IndependentSums.IsBigO μ Ψ X A :=
  isBigOEnvelopeWith_const_iff_isBigOWith μ Ψ (fun ω => |X ω|) A

/-! ## The conditional predicate -/

/-- The conditional weak-Orlicz relation: for every `t ≥ 1` and `μ`-almost every
`ω`, the conditional probability given `m` of `{X > θ t}` — the conditional
expectation of the indicator of the random-threshold tail set — is at most
`(Ψ t)⁻¹`. At the constant envelope `A` this is the unconditional relation
`IndependentSums.IsBigOWith`. -/
def CondIsBigOWith (μ : Measure Ω) (m : MeasurableSpace Ω) (Ψ : ℝ → ℝ)
    (X : Ω → ℝ) (θ : Ω → ℝ) : Prop :=
  ∀ ⦃t : ℝ⦄, 1 ≤ t →
    ∀ᵐ ω ∂μ,
      (μ[Set.indicator (upperTailSet X θ t) (fun _ => (1 : ℝ))|m]) ω ≤ (Ψ t)⁻¹

/-- The symmetric conditional weak-Orlicz relation, through `|X|`: the
conditional form of `IndependentSums.IsBigO`. -/
def CondIsBigO (μ : Measure Ω) (m : MeasurableSpace Ω) (Ψ : ℝ → ℝ)
    (X : Ω → ℝ) (θ : Ω → ℝ) : Prop :=
  CondIsBigOWith μ m Ψ (fun ω => |X ω|) θ

/-! ## Elementary monotonicity -/

theorem CondIsBigOWith.mono_scale {μ : Measure Ω} [IsFiniteMeasure μ] {Ψ : ℝ → ℝ}
    {X : Ω → ℝ} {θ φ : Ω → ℝ}
    (hθ : Measurable θ) (hφ : Measurable φ) (hX : Measurable X)
    (h : CondIsBigOWith μ m Ψ X θ) (hle : ∀ ω, θ ω ≤ φ ω) :
    CondIsBigOWith μ m Ψ X φ := by
  intro t ht
  have hsetθ : MeasurableSet (upperTailSet X θ t) :=
    measurableSet_lt (hθ.mul_const t) hX
  have hsetφ : MeasurableSet (upperTailSet X φ t) :=
    measurableSet_lt (hφ.mul_const t) hX
  have hsub : upperTailSet X φ t ⊆ upperTailSet X θ t :=
    upperTailSet_mono_threshold hle (le_trans zero_le_one ht)
  have hind : Set.indicator (upperTailSet X φ t) (fun _ => (1 : ℝ)) ≤
      Set.indicator (upperTailSet X θ t) (fun _ => (1 : ℝ)) :=
    indicator_le_indicator_of_subset hsub zero_le_one
  have hmono : (μ[Set.indicator (upperTailSet X φ t) (fun _ => (1 : ℝ))|m]) ≤ᵐ[μ]
      (μ[Set.indicator (upperTailSet X θ t) (fun _ => (1 : ℝ))|m]) :=
    condExp_mono ((integrable_const (1 : ℝ)).indicator hsetφ)
      ((integrable_const (1 : ℝ)).indicator hsetθ) (Filter.Eventually.of_forall hind)
  filter_upwards [h ht, hmono] with ω hω hmonoω
  exact le_trans hmonoω hω

theorem CondIsBigOWith.of_le {μ : Measure Ω} [IsFiniteMeasure μ] {Ψ : ℝ → ℝ}
    {X Y : Ω → ℝ} {θ : Ω → ℝ}
    (hθ : Measurable θ) (hX : Measurable X) (hY : Measurable Y)
    (h : CondIsBigOWith μ m Ψ X θ) (hYX : ∀ ω, Y ω ≤ X ω) :
    CondIsBigOWith μ m Ψ Y θ := by
  intro t ht
  have hsetX : MeasurableSet (upperTailSet X θ t) :=
    measurableSet_lt (hθ.mul_const t) hX
  have hsetY : MeasurableSet (upperTailSet Y θ t) :=
    measurableSet_lt (hθ.mul_const t) hY
  have hsub : upperTailSet Y θ t ⊆ upperTailSet X θ t := by
    intro ω hω
    exact lt_of_lt_of_le hω (hYX ω)
  have hind : Set.indicator (upperTailSet Y θ t) (fun _ => (1 : ℝ)) ≤
      Set.indicator (upperTailSet X θ t) (fun _ => (1 : ℝ)) :=
    indicator_le_indicator_of_subset hsub zero_le_one
  have hmono : (μ[Set.indicator (upperTailSet Y θ t) (fun _ => (1 : ℝ))|m]) ≤ᵐ[μ]
      (μ[Set.indicator (upperTailSet X θ t) (fun _ => (1 : ℝ))|m]) :=
    condExp_mono ((integrable_const (1 : ℝ)).indicator hsetY)
      ((integrable_const (1 : ℝ)).indicator hsetX) (Filter.Eventually.of_forall hind)
  filter_upwards [h ht, hmono] with ω hω hmonoω
  exact le_trans hmonoω hω

/-! ## The tower step -/

/-- **The tower step (one-sided).** A conditional weak-Orlicz bound at an envelope
`θ` integrates up, by the tower property `∫ μ[f|m] = ∫ f` of the conditional
expectation, to the unconditional bound at the *same* envelope. At a constant
envelope this is literally `IndependentSums.IsBigOWith`, so the conditional
calculus composes with every unconditional concentration theorem. -/
theorem IsBigOEnvelopeWith.of_condIsBigOWith (hm : m ≤ mΩ) {μ : Measure Ω}
    [IsProbabilityMeasure μ] {Ψ : ℝ → ℝ} {X θ : Ω → ℝ}
    (hθ : Measurable θ) (hX : Measurable X) (h : CondIsBigOWith μ m Ψ X θ) :
    IsBigOEnvelopeWith μ Ψ X θ := by
  have hfin : IsFiniteMeasure (μ.trim hm) := isFiniteMeasure_trim hm
  intro t ht
  have hset : MeasurableSet (upperTailSet X θ t) :=
    measurableSet_lt (hθ.mul_const t) hX
  have hbound : ∀ᵐ ω ∂μ,
      (μ[Set.indicator (upperTailSet X θ t) (fun _ => (1 : ℝ))|m]) ω ≤ (Ψ t)⁻¹ :=
    h ht
  have hint := integral_mono_ae (integrable_condExp) (integrable_const (Ψ t)⁻¹) hbound
  have hL : ∫ ω, (μ[Set.indicator (upperTailSet X θ t) (fun _ => (1 : ℝ))|m]) ω ∂μ =
      μ.real (upperTailSet X θ t) := by
    rw [integral_condExp (μ := μ) hm, integral_indicator hset, setIntegral_const, smul_eq_mul,
      mul_one]
  have hR : ∫ _ω : Ω, (Ψ t)⁻¹ ∂μ = (Ψ t)⁻¹ := by
    rw [integral_const, probReal_univ, one_smul]
  rw [hL, hR] at hint
  exact hint

/-- **The tower step (symmetric).** -/
theorem IsBigOEnvelope.of_condIsBigO (hm : m ≤ mΩ) {μ : Measure Ω}
    [IsProbabilityMeasure μ] {Ψ : ℝ → ℝ} {X θ : Ω → ℝ}
    (hθ : Measurable θ) (hX : Measurable X) (h : CondIsBigO μ m Ψ X θ) :
    IsBigOEnvelope μ Ψ X θ :=
  IsBigOEnvelopeWith.of_condIsBigOWith (m := m) hm hθ (measurable_abs_comp hX) h

/-- The tower step at a constant envelope: a conditional bound at `A` integrates
to the unconditional relation `X = O_Ψ(A)`. -/
theorem isBigO_of_condIsBigO (hm : m ≤ mΩ) {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Ψ : ℝ → ℝ} {X : Ω → ℝ} {A : ℝ} (hX : Measurable X)
    (h : CondIsBigO μ m Ψ X (fun _ => A)) :
    IndependentSums.IsBigO μ Ψ X A :=
  (isBigOEnvelope_const_iff_isBigO μ Ψ X A).1
    (IsBigOEnvelope.of_condIsBigO (m := m) hm measurable_const hX h)

/-! ## The product step -/

/-! ## The conditional union bound -/

/-- **The conditional union bound for two summands**, the conditional analogue of
the triangle inequality's union step: if `X` and `Y` have conditional weak-Orlicz
bounds at envelopes `θ` and `φ`, then `X + Y` has one at envelope `θ + φ` and
profile `Ρ`, provided the two inverse tails add up to the inverse tail of `Ρ`. -/
theorem CondIsBigOWith.add {μ : Measure Ω} [IsFiniteMeasure μ] {Ψ Φ Ρ : ℝ → ℝ}
    {X Y θ φ : Ω → ℝ}
    (hθ : Measurable θ) (hφ : Measurable φ) (hX : Measurable X) (hY : Measurable Y)
    (h : CondIsBigOWith μ m Ψ X θ) (h' : CondIsBigOWith μ m Φ Y φ)
    (hΨ : ∀ ⦃t : ℝ⦄, 1 ≤ t → (Ψ t)⁻¹ + (Φ t)⁻¹ ≤ (Ρ t)⁻¹) :
    CondIsBigOWith μ m Ρ (fun ω => X ω + Y ω) (fun ω => θ ω + φ ω) := by
  intro t ht
  have hsetX : MeasurableSet (upperTailSet X θ t) :=
    measurableSet_lt (hθ.mul_const t) hX
  have hsetY : MeasurableSet (upperTailSet Y φ t) :=
    measurableSet_lt (hφ.mul_const t) hY
  have hsetS : MeasurableSet (upperTailSet (fun ω => X ω + Y ω) (fun ω => θ ω + φ ω) t) :=
    measurableSet_lt (((hθ.add hφ).mul_const t)) (hX.add hY)
  have hsub : upperTailSet (fun ω => X ω + Y ω) (fun ω => θ ω + φ ω) t ⊆
      upperTailSet X θ t ∪ upperTailSet Y φ t := by
    intro ω hω
    by_cases hXc : ω ∈ upperTailSet X θ t
    · exact Or.inl hXc
    · refine Or.inr ?_
      simp only [mem_upperTailSet] at hω hXc ⊢
      have hXle : X ω ≤ θ ω * t := le_of_not_gt hXc
      have hsum : (θ ω + φ ω) * t = θ ω * t + φ ω * t := by ring
      linarith only [hω, hXle, hsum]
  have hind : Set.indicator (upperTailSet (fun ω => X ω + Y ω) (fun ω => θ ω + φ ω) t)
        (fun _ => (1 : ℝ)) ≤
      Set.indicator (upperTailSet X θ t) (fun _ => (1 : ℝ)) +
        Set.indicator (upperTailSet Y φ t) (fun _ => (1 : ℝ)) :=
    indicator_le_indicator_add hsub zero_le_one
  have hmono : (μ[Set.indicator (upperTailSet (fun ω => X ω + Y ω) (fun ω => θ ω + φ ω) t)
        (fun _ => (1 : ℝ))|m]) ≤ᵐ[μ]
      (μ[Set.indicator (upperTailSet X θ t) (fun _ => (1 : ℝ))|m]) +
        (μ[Set.indicator (upperTailSet Y φ t) (fun _ => (1 : ℝ))|m]) :=
    (condExp_mono ((integrable_const (1 : ℝ)).indicator hsetS)
      (((integrable_const (1 : ℝ)).indicator hsetX).add
        ((integrable_const (1 : ℝ)).indicator hsetY))
      (Filter.Eventually.of_forall hind)).trans_eq
      (condExp_add ((integrable_const (1 : ℝ)).indicator hsetX)
        ((integrable_const (1 : ℝ)).indicator hsetY) m)
  have h1 : ∀ᵐ ω ∂μ,
      (μ[Set.indicator (upperTailSet X θ t) (fun _ => (1 : ℝ))|m]) ω ≤ (Ψ t)⁻¹ := h ht
  have h2 : ∀ᵐ ω ∂μ,
      (μ[Set.indicator (upperTailSet Y φ t) (fun _ => (1 : ℝ))|m]) ω ≤ (Φ t)⁻¹ := h' ht
  filter_upwards [hmono, h1, h2] with ω hmonoω h1ω h2ω
  simp only [Pi.add_apply] at hmonoω
  exact le_trans hmonoω (le_trans (add_le_add h1ω h2ω) (hΨ ht))

end SuperdiffusionCLT.Probability

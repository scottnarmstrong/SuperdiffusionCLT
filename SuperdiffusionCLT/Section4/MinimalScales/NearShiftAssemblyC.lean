/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section4.MinimalScales.GammaCenteredMax
public import SuperdiffusionCLT.Section4.MinimalScales.NearShiftCap
public import SuperdiffusionCLT.Probability.GammaSigmaHelpers
public import Homogenization.Probability.IndependentSums.Triangle
public import Mathlib.MeasureTheory.Order.Group.Lattice

/-!
# Near-scale assembly, probabilistic part (I): finite maxima

Two abstract collection lemmas, with no reference to the coefficient field:

* `srootNS_gamma_dominate`: finitely many `O_{Γ_σ}(β)` variables are dominated pathwise by one
  nonnegative measurable variable, `O_{Γ_σ}((3 log (max 2 N))^{1/σ} β)`.
* `srootNS_gamma1_collect`: for `σ = 1`, the same for the family indexed by a cutoff window
  `L ∈ [a, b]`, a depth `l < Nl` and a descendant `R ∈ S l`, with depth-dependent amplitude
  `α l`. The maximum over `(L, R)` is centered at `α l · log (2 (b+1-a) |S l|)`, and the excess
  `Y_l` is `O_{Γ₁}(α l)`. The weighted sum `Y = ∑ w_l Y_l` is `O_{Γ₁}(g ∑ w_l α_l)` by the
  triangle inequality.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section4.MinimalScales

open MeasureTheory Homogenization.IndependentSums

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Finite domination in `Γ_σ`: for nonempty `T`, `|X i| ≤ V` for all `i ∈ T`, with `V`
nonnegative, measurable, `O_{Γ_σ}((3 log (max 2 |T|))^{1/σ} β)`. -/
theorem srootNS_gamma_dominate {κ : Type*} {μ : Measure Ω} [IsFiniteMeasure μ] {σ β : ℝ}
    (hσ : 0 < σ) (hβ : 0 ≤ β) (T : Finset κ) (hT : T.Nonempty) (X : κ → Ω → ℝ)
    (hmeas : ∀ i ∈ T, Measurable (X i))
    (hX : ∀ i ∈ T, IsBigO μ (gammaSigma σ) (X i) β) :
    ∃ V : Ω → ℝ, Measurable V ∧ (∀ ω, 0 ≤ V ω) ∧
      IsBigO μ (gammaSigma σ) V ((3 * Real.log (max 2 (T.card : ℝ))) ^ σ⁻¹ * β) ∧
      ∀ i ∈ T, ∀ ω, |X i ω| ≤ V ω := by
  have hmabs : ∀ i ∈ T, Measurable (fun ω => |X i ω|) := fun i hi => (hmeas i hi).abs
  refine ⟨fun ω => T.sup' hT (fun i => |X i ω|), ?_, ?_, ?_, ?_⟩
  · have h := Finset.measurable_sup' hT (fun i hi => hmabs i hi)
    convert h using 1
    ext ω
    exact (Finset.sup'_apply hT (fun i ω => |X i ω|) ω).symm
  · intro ω
    obtain ⟨i, hi⟩ := hT
    exact le_trans (abs_nonneg _) (Finset.le_sup' (fun i => |X i ω|) hi)
  · have hnn : ∀ ω, 0 ≤ T.sup' hT (fun i => |X i ω|) := by
      intro ω
      obtain ⟨i, hi⟩ := hT
      exact le_trans (abs_nonneg _) (Finset.le_sup' (fun i => |X i ω|) hi)
    refine (SuperdiffusionCLT.Probability.isBigOWith_iff_isBigO_of_nonneg hnn).1 ?_
    rcases Nat.lt_or_ge T.card 2 with hc | hc
    · have hc1 : T.card = 1 := by
        have := hT.card_pos; omega
      obtain ⟨i0, hi0⟩ := Finset.card_eq_one.1 hc1
      have h1 := hX i0 (by simp [hi0])
      have hsup : (fun ω => T.sup' hT (fun i => |X i ω|)) = fun ω => |X i0 ω| := by
        funext ω; simp [hi0]
      rw [hsup]
      refine h1.mono_scale ?_
      have hmax : max 2 (T.card : ℝ) = 2 := by
        rw [hc1]; norm_num
      rw [hmax]
      have hl : 1 ≤ 3 * Real.log 2 := by
        have := Real.log_two_gt_d9; linarith only [this]
      have h1r : (1 : ℝ) ≤ (3 * Real.log 2) ^ σ⁻¹ :=
        Real.one_le_rpow hl (inv_nonneg.2 hσ.le)
      nlinarith only [h1r, hβ]
    · have h := isBigOWith_gammaSigma_finset_sup'_abs_of_scales (μ := μ) (s := T) (hs := hT)
        (X := X) (a := fun _ => β) (σ := σ) hσ hc hX
      have hmax : max 2 (T.card : ℝ) = (T.card : ℝ) := by
        have : (2 : ℝ) ≤ T.card := by exact_mod_cast hc
        exact max_eq_right this
      rw [hmax]
      simpa using h
  · intro i hi ω
    exact Finset.le_sup' (fun i => |X i ω|) hi

/-- Satisfiability of `srootNS_gamma_dominate`: one variable, `X = 0`. -/
example : ∃ V : ℝ → ℝ, Measurable V ∧ (∀ ω, 0 ≤ V ω) ∧
    IsBigO (volume.restrict (Set.Icc (0 : ℝ) 1)) (gammaSigma 1) V
      ((3 * Real.log (max 2 (({0} : Finset ℕ).card : ℝ))) ^ (1 : ℝ)⁻¹ * 1) ∧
    ∀ i ∈ ({0} : Finset ℕ), ∀ ω, |(fun (_ : ℕ) (_ : ℝ) => (0 : ℝ)) i ω| ≤ V ω := by
  refine srootNS_gamma_dominate (σ := 1) (β := 1) one_pos zero_le_one {0}
    (Finset.singleton_nonempty 0) (fun _ _ => (0 : ℝ)) (fun _ _ => measurable_const) ?_
  intro i _ t ht
  have h : upperTailEvent (fun ω : ℝ => |(fun _ : ℝ => (0 : ℝ)) ω|) (1 * t) = ∅ := by
    ext ω; simp [upperTailEvent]; linarith only [ht]
  rw [h]; simp; positivity

/-- **C1 (collection of the `Γ₁` witnesses).** For `σ = 1`: a family `X L l R`, `L ∈ [a, b]`,
`l < Nl`, `R ∈ S l`, with `X L l R = O_{Γ₁}(α l)` (`α l > 0`), is bounded by
`α l log (2 (b+1-a) |S l|) + Y_l`, with `Y_l ≥ 0` measurable and `O_{Γ₁}(α l)`; and for weights
`w l > 0` the sum `Y = ∑ w_l Y_l` is `O_{Γ₁}(g ∑ w_l α_l)`, `g = gammaTriangleConst 1`. -/
theorem srootNS_gamma1_collect {ι : Type*} {μ : Measure Ω} [IsFiniteMeasure μ] {a b : ℕ}
    (hab : a ≤ b) (Nl : ℕ) (hNl : 0 < Nl) (S : ℕ → Finset ι) (hS : ∀ l, (S l).Nonempty)
    (w α : ℕ → ℝ) (hw : ∀ l, 0 < w l) (hα : ∀ l, 0 < α l) (X : ℕ → ℕ → ι → Ω → ℝ)
    (hmeas : ∀ L ∈ Finset.Icc a b, ∀ l < Nl, ∀ R ∈ S l, Measurable (X L l R))
    (hX : ∀ L ∈ Finset.Icc a b, ∀ l < Nl, ∀ R ∈ S l,
      IsBigO μ (gammaSigma 1) (X L l R) (α l)) :
    ∃ Yl : ℕ → Ω → ℝ, (∀ l, Measurable (Yl l)) ∧ (∀ l ω, 0 ≤ Yl l ω) ∧
      (∀ l < Nl, IsBigO μ (gammaSigma 1) (Yl l) (α l)) ∧
      (∀ ω, ∀ L ∈ Finset.Icc a b, ∀ l < Nl, ∀ R ∈ S l,
        |X L l R ω| ≤ α l * Real.log (2 * (((b + 1 - a : ℕ) : ℝ) * ((S l).card : ℝ))) + Yl l ω) ∧
      Measurable (fun ω => ∑ l ∈ Finset.range Nl, w l * Yl l ω) ∧
      IsBigO μ (gammaSigma 1) (fun ω => ∑ l ∈ Finset.range Nl, w l * Yl l ω)
        (gammaTriangleConst 1 * ∑ l ∈ Finset.range Nl, w l * α l) := by
  have hper : ∀ l, ∃ Y : Ω → ℝ, l < Nl → Measurable Y ∧ (∀ ω, 0 ≤ Y ω) ∧
      IsBigO μ (gammaSigma 1) Y (α l) ∧
      ∀ ω, ∀ L ∈ Finset.Icc a b, ∀ R ∈ S l,
        |X L l R ω| ≤ α l * Real.log (2 * (((b + 1 - a : ℕ) : ℝ) * ((S l).card : ℝ))) + Y ω := by
    intro l
    by_cases hl : l < Nl
    · let T : Finset (ℕ × ι) := Finset.Icc a b ×ˢ S l
      have hTne : T.Nonempty := (Finset.nonempty_Icc.2 hab).product (hS l)
      have hc := gammaSigma_centered_finset_sup'_exists (μ := μ) (σ := 1) (A := α l) le_rfl
        (hα l).le T hTne (fun p ω => |X p.1 l p.2 ω|)
        (fun p hp => (hmeas p.1 (Finset.mem_product.1 hp).1 l hl p.2
          (Finset.mem_product.1 hp).2).abs)
        (fun p hp => by
          have := hX p.1 (Finset.mem_product.1 hp).1 l hl p.2 (Finset.mem_product.1 hp).2
          simpa [IsBigO] using this)
      obtain ⟨Y, hYm, hY0, hYO, hYle⟩ := hc
      refine ⟨Y, fun _ => ⟨hYm, hY0, hYO, ?_⟩⟩
      intro ω L hL R hR
      have h1 := hYle ω
      have hmem : (L, R) ∈ T := Finset.mem_product.2 ⟨hL, hR⟩
      have h2 := Finset.le_sup' (fun p : ℕ × ι => |X p.1 l p.2 ω|) hmem
      have hcard : (T.card : ℝ) = ((b + 1 - a : ℕ) : ℝ) * ((S l).card : ℝ) := by
        simp [T, Finset.card_product, Nat.card_Icc]
      rw [hcard] at h1
      simp only [inv_one, Real.rpow_one] at h1
      exact le_trans h2 h1
    · exact ⟨0, fun h => absurd h hl⟩
  choose Yl hYl using hper
  have hm : ∀ l < Nl, Measurable (Yl l) := fun l hl => (hYl l hl).1
  refine ⟨fun l => if l < Nl then Yl l else fun _ => 0, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro l; by_cases hl : l < Nl <;> simp [hl, hm, measurable_const]
  · intro l ω; by_cases hl : l < Nl
    · simp [hl, (hYl l hl).2.1 ω]
    · simp [hl]
  · intro l hl; simpa [hl] using (hYl l hl).2.2.1
  · intro ω L hL l hl R hR
    simpa [hl] using (hYl l hl).2.2.2 ω L hL R hR
  · exact Finset.measurable_sum _ (fun l hl => by
      have hl' := Finset.mem_range.1 hl
      simpa [hl'] using (hm l hl').const_mul (w l))
  · have h := isBigO_finset_sum_of_isBigO_gammaSigma (μ := μ) (Finset.range Nl)
      (X := fun l ω => w l * (if l < Nl then Yl l else fun _ => 0) ω) (a := fun l => w l * α l)
      (σ := 1) one_pos (Finset.nonempty_range_iff.2 hNl.ne')
      (fun l _ => mul_pos (hw l) (hα l))
      (fun l hl => by
        have hl' := Finset.mem_range.1 hl
        have := (IsBigO.const_mul (hw l).le (hYl l hl').2.2.1)
        simpa [hl'] using this)
      (fun l hl => by
        have hl' := Finset.mem_range.1 hl
        simpa [hl'] using (hm l hl').const_mul (w l))
    simpa using h

/-- Satisfiability of `srootNS_gamma1_collect`: the zero family, window `[0,1]`, `Nl = 1`. -/
example : ∃ Yl : ℕ → ℝ → ℝ, (∀ l, Measurable (Yl l)) ∧ (∀ l ω, 0 ≤ Yl l ω) ∧
    (∀ l < 1, IsBigO (volume.restrict (Set.Icc (0 : ℝ) 1)) (gammaSigma 1) (Yl l) 1) ∧
    (∀ ω, ∀ L ∈ Finset.Icc 0 1, ∀ l < 1, ∀ R ∈ ({0} : Finset ℕ),
      |(fun (_ _ _ : ℕ) (_ : ℝ) => (0 : ℝ)) L l R ω| ≤
        1 * Real.log (2 * (((1 + 1 - 0 : ℕ) : ℝ) * (({0} : Finset ℕ).card : ℝ))) + Yl l ω) ∧
    Measurable (fun ω => ∑ l ∈ Finset.range 1, (1 : ℝ) * Yl l ω) ∧
    IsBigO (volume.restrict (Set.Icc (0 : ℝ) 1)) (gammaSigma 1)
      (fun ω => ∑ l ∈ Finset.range 1, (1 : ℝ) * Yl l ω)
      (gammaTriangleConst 1 * ∑ _l ∈ Finset.range 1, (1 : ℝ) * 1) := by
  refine srootNS_gamma1_collect (a := 0) (b := 1) (by norm_num) 1 one_pos (fun _ => {0})
    (fun _ => Finset.singleton_nonempty 0) (fun _ => 1) (fun _ => 1) (fun _ => one_pos)
    (fun _ => one_pos) (fun _ _ _ _ => (0 : ℝ)) (fun _ _ _ _ _ _ => measurable_const)
    ?_
  intro L _ _ _ R _ t ht
  have h : upperTailEvent (fun ω : ℝ => |(fun _ : ℝ => (0 : ℝ)) ω|) (1 * t) = ∅ := by
    ext ω; simp [upperTailEvent]; linarith only [ht]
  rw [h]; simp; positivity

end

end SuperdiffusionCLT.Section4.MinimalScales

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Prereq.L2Assembly
public import SuperdiffusionCLT.Section7.Prereq.L2InteriorD

/-!
# Scale-uniform constants for the `L²` Dirichlet comparison

The layer Poincare inequality with constants independent of the scale `r₀` of the domain, and the
exponent bookkeeping for the Sobolev pairs `(2_*, 2)`, `(2, 2^*)`.
-/

@[expose] public section

open MeasureTheory Set Filter Homogenization
open scoped ENNReal NNReal

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

/-- The layer Poincaré inequality (`exists_layerPoincare`) with the explicit threshold, constants independent of the scale `r`
`t ≤ r / (3 (d + (1 + d) max(M₁, 0)) + 4)`. -/
theorem l2d_layerPoincare_unif [NeZero d] (M₁ : ℝ) :
    ∃ C K : ℝ, 0 ≤ C ∧ 1 ≤ K ∧
      ∀ {r : ℝ} {U : Set (Vec d)} {M₂ D : ℝ}, IsUniformC11Domain U r M₁ M₂ D →
        ∀ (ψ : H10Function U) {q : ℝ}, 1 ≤ q → ∀ {t : ℝ}, 0 < t →
          t ≤ r / (3 * ((d : ℝ) + (1 + d) * max M₁ 0) + 4) →
          eLpNorm ψ.toH1Function.toFun (ENNReal.ofReal q)
              (volume.restrict (boundaryLayer U t)) ≤
            ENNReal.ofReal (C * t) *
              eLpNorm (fun x => ‖ψ.toH1Function.grad x‖) (ENNReal.ofReal q)
                (volume.restrict (boundaryLayer U (K * t))) := by
  set κ₀ : ℝ := (d : ℝ) + (1 + d) * max M₁ 0 with hκ₀
  have hκ0 : 0 ≤ κ₀ := by
    have : 0 ≤ max M₁ 0 := le_max_right _ _
    positivity
  set Bn : ℕ := ⌈3 * κ₀ + 5⌉₊ with hBn
  set Nr : ℝ := (((2 * Bn + 1) ^ d : ℕ) : ℝ) with hNr
  have hNr0 : 0 ≤ Nr := Nat.cast_nonneg _
  refine ⟨3 * κ₀ * d * Nr, 3 * κ₀ + 5, by positivity, by linarith only [hκ0], ?_⟩
  intro r U M₂ D h ψ q hq t ht htt
  have hq0 : 0 < q := by linarith only [hq]
  by_cases hU0 : U = ∅
  · have hL : boundaryLayer U t = ∅ :=
      Set.eq_empty_of_forall_notMem fun x hx => by
        have := hx.1
        rw [hU0] at this
        exact this
    rw [hL, Measure.restrict_empty, eLpNorm_measure_zero]
    exact bot_le
  obtain ⟨x0, hx0⟩ := layerPoincare_frontier_nonempty h.2.2.1 hU0
  obtain ⟨e, γ, he, hγ, hb, -, -⟩ := h.2.2.2 x0 hx0
  have hM : 0 ≤ M₁ := (norm_nonneg _).trans (hb 0)
  have hκ : κ₀ = (d : ℝ) + (1 + d) * M₁ := by rw [hκ₀, max_eq_left hM]
  have hr' : (3 * ((d : ℝ) + (1 + d) * M₁) + 4) * t ≤ r := by
    have := (le_div_iff₀ (by positivity : 0 < 3 * κ₀ + 4)).1 htt
    rw [hκ] at this
    linarith only [this]
  have hint := layerPoincare_integral h ψ hq ht hr'
  rw [← hκ] at hint
  have hN1 : (1 : ℝ≥0∞) ≤ (((2 * ⌈3 * κ₀ + 5⌉₊ + 1) ^ d : ℕ) : ℝ≥0∞) := by
    have : 1 ≤ (2 * ⌈3 * κ₀ + 5⌉₊ + 1) ^ d := Nat.one_le_pow _ _ (by omega)
    exact_mod_cast this
  have hp0 : ENNReal.ofReal q ≠ 0 := (ENNReal.ofReal_pos.2 hq0).ne'
  have hmeasψ : AEStronglyMeasurable ψ.toH1Function.toFun
      (volume.restrict (boundaryLayer U t)) :=
    ψ.toH1Function.memL2.aestronglyMeasurable.mono_measure
      (Measure.restrict_mono (fun x hx => hx.1) le_rfl)
  have hmeasg : AEStronglyMeasurable (fun x => ‖ψ.toH1Function.grad x‖)
      (volume.restrict (boundaryLayer U ((3 * κ₀ + 5) * t))) := by
    have : AEStronglyMeasurable ψ.toH1Function.grad (volume.restrict U) :=
      (aemeasurable_pi_iff.2 fun i =>
        (ψ.toH1Function.gradMemL2 i).aestronglyMeasurable.aemeasurable).aestronglyMeasurable
    exact (this.mono_measure (Measure.restrict_mono (fun x hx => hx.1) le_rfl)).norm
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 ENNReal.ofReal_ne_top hmeasψ,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 ENNReal.ofReal_ne_top hmeasg,
    ENNReal.toReal_ofReal hq0.le]
  simp only [enorm_norm]
  have hfin := layerPoincare_rpow_div hq hN1 hint
  refine hfin.trans ?_
  refine mul_le_mul_left ?_ _
  have hNe : ((((2 * ⌈3 * κ₀ + 5⌉₊ + 1) ^ d : ℕ)) : ℝ≥0∞) = ENNReal.ofReal Nr := by
    rw [hNr, ENNReal.ofReal_natCast]
  rw [hNe, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
  ring

/-- **The layer Poincaré inequality in the form used by the layer terms**: for a uniformly
`C^{1,1}` domain, `‖ψ‖_{L^q(A)} ≤ CP r ‖∇ψ‖_{L^q(W)}` for `ψ ∈ H¹₀(W)`, every `A` inside the
boundary layer of thickness `3 r`, `3 r ≤ r₀ / (3 (d + (1 + d) max(M₁, 0)) + 4)`. -/
theorem l2d_hPoinc [NeZero d] (M₁ : ℝ) :
    ∃ CP : ℝ, 0 ≤ CP ∧ ∀ {r₀ : ℝ} {W : Set (Vec d)} {M₂ D : ℝ},
      IsUniformC11Domain W r₀ M₁ M₂ D → ∀ {q : ℝ}, 1 ≤ q → ∀ {r : ℝ}, 0 < r →
        3 * r ≤ r₀ / (3 * ((d : ℝ) + (1 + d) * max M₁ 0) + 4) →
        ∀ {A : Set (Vec d)}, A ⊆ boundaryLayer W (3 * r) → ∀ ψ : H10Function W,
          eLpNorm ψ.toH1Function.toFun (ENNReal.ofReal q) (volume.restrict A) ≤
            ENNReal.ofReal (CP * r) * eLpNorm (fun x => ‖ψ.toH1Function.grad x‖)
              (ENNReal.ofReal q) (volume.restrict W) := by
  obtain ⟨C, K, hC, hK, H⟩ := l2d_layerPoincare_unif (d := d) M₁
  refine ⟨3 * C, by positivity, ?_⟩
  intro r₀ W M₂ D hU q hq r hr h3r A hA ψ
  have h := H hU ψ hq (t := 3 * r) (by positivity) h3r
  calc eLpNorm ψ.toH1Function.toFun (ENNReal.ofReal q) (volume.restrict A)
      ≤ eLpNorm ψ.toH1Function.toFun (ENNReal.ofReal q) (volume.restrict (boundaryLayer W (3 * r))) :=
        eLpNorm_mono_measure _ (Measure.restrict_mono hA le_rfl)
    _ ≤ ENNReal.ofReal (C * (3 * r)) * eLpNorm (fun x => ‖ψ.toH1Function.grad x‖)
          (ENNReal.ofReal q) (volume.restrict (boundaryLayer W (K * (3 * r)))) := h
    _ ≤ ENNReal.ofReal (3 * C * r) * eLpNorm (fun x => ‖ψ.toH1Function.grad x‖)
          (ENNReal.ofReal q) (volume.restrict W) := by
        have e : C * (3 * r) = 3 * C * r := by ring
        rw [e]
        exact mul_le_mul' le_rfl (eLpNorm_mono_measure _ (Measure.restrict_mono (fun x hx => hx.1) le_rfl))


/-- The conjugate `2_*` of `2^*` and the Sobolev exponent `q` with `q⁻¹ = (2_*)⁻¹ - d⁻¹`, `q ≥ 2`. -/
theorem l2d_exponents (hd : 2 ≤ d) :
    1 < Real.conjExponent (sobStar d) ∧ Real.conjExponent (sobStar d) < 2 ∧
      Real.conjExponent (sobStar d) < d ∧
      ∃ q : ℝ, 2 ≤ q ∧ q⁻¹ = (Real.conjExponent (sobStar d))⁻¹ - (d : ℝ)⁻¹ := by
  have hs := two_lt_sobStar hd
  have hR : Real.HolderConjugate (sobStar d) (Real.conjExponent (sobStar d)) :=
    Real.HolderConjugate.conjExponent (by linarith only [hs])
  have hinv := hR.inv_add_inv_eq_one
  have hp1 : 1 < Real.conjExponent (sobStar d) := hR.symm.lt
  have hsinv : (sobStar d)⁻¹ < 2⁻¹ := inv_strictAnti₀ (by norm_num) hs
  have hp0 : 0 < Real.conjExponent (sobStar d) := by linarith only [hp1]
  have hp2 : Real.conjExponent (sobStar d) < 2 := by
    by_contra hc
    have hc' : (2 : ℝ) ≤ Real.conjExponent (sobStar d) := not_lt.1 hc
    have := inv_anti₀ (by norm_num) hc'
    linarith only [hinv, hsinv, this]
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  refine ⟨hp1, hp2, by linarith only [hp2, hdR], ?_⟩
  by_cases h2 : d = 2
  · subst h2
    refine ⟨3, by norm_num, ?_⟩
    rw [sobStar_two] at hinv ⊢
    push_cast
    linarith only [hinv]
  · have h3 : 3 ≤ d := by omega
    refine ⟨2, le_rfl, ?_⟩
    have := inv_sobStar h3
    have e : (Real.conjExponent (sobStar d))⁻¹ = 1 / 2 + 1 / d := by
      linarith only [hinv, this]
    rw [e]
    ring

/-- `H¹₀` functions of a bounded set lie in `L^{2^*}`. -/
theorem l2d_memLp_sobStar (hd : 2 ≤ d) {W : Set (Vec d)} (hWb : Bornology.IsBounded W)
    (φ : H10Function W) :
    MemLp φ.toH1Function.toFun (ENNReal.ofReal (sobStar d)) (volume.restrict W) := by
  have hd0 : 0 < d := by omega
  have hs := two_lt_sobStar hd
  have hfin : IsFiniteMeasure (volume.restrict W) := ⟨by simpa using hWb.measure_lt_top⟩
  show eLpNorm φ.toH1Function.toFun (ENNReal.ofReal (sobStar d)) (volume.restrict W) < ⊤
  by_cases h2 : d = 2
  · subst h2
    let P : FiniteLpExponent := ⟨ENNReal.ofReal (3 / 2), by
      rw [← ENNReal.ofReal_one]; exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).2 (by norm_num),
      ENNReal.ofReal_lt_top⟩
    let Q : FiniteLpExponent := ⟨ENNReal.ofReal 6, by
      rw [← ENNReal.ofReal_one]; exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).2 (by norm_num),
      ENNReal.ofReal_lt_top⟩
    have hPr : P.exponent.toReal = 3 / 2 := ENNReal.toReal_ofReal (by norm_num)
    have hQr : Q.exponent.toReal = 6 := ENNReal.toReal_ofReal (by norm_num)
    have hP2 : P.exponent ≤ 2 := by
      show ENNReal.ofReal (3 / 2) ≤ 2
      rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp]
      exact ENNReal.ofReal_le_ofReal (by norm_num)
    have h := l2d_sobolev_H10 hd0 P Q hP2 (by rw [hPr]; norm_num)
      (by rw [hPr, hQr]; norm_num) hWb φ
    rw [sobStar_two]
    refine lt_of_le_of_lt h ?_
    refine ENNReal.mul_lt_top ENNReal.coe_lt_top ?_
    refine ENNReal.sum_lt_top.2 fun i _ => ?_
    have h1 := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (p := P.exponent) (q := 2)
      (μ := volume.restrict W) hP2 (φ.toH1Function.gradMemL2 i).aestronglyMeasurable
    refine lt_of_le_of_lt h1 (ENNReal.mul_lt_top (φ.toH1Function.gradMemL2 i).eLpNorm_lt_top ?_)
    exact ENNReal.rpow_lt_top_of_nonneg (by
      rw [hPr]; norm_num) (measure_lt_top _ _).ne
  · have h3 : 3 ≤ d := by omega
    let P : FiniteLpExponent := ⟨2, by norm_num, by norm_num⟩
    let Q : FiniteLpExponent := ⟨ENNReal.ofReal (sobStar d), by
      rw [← ENNReal.ofReal_one]
      exact (ENNReal.ofReal_lt_ofReal_iff (by linarith only [hs])).2 (by linarith only [hs]),
      ENNReal.ofReal_lt_top⟩
    have hPr : P.exponent.toReal = 2 := by simp [P]
    have hQr : Q.exponent.toReal = sobStar d := ENNReal.toReal_ofReal (by linarith only [hs])
    have h3' : (3 : ℝ) ≤ d := by exact_mod_cast h3
    have h := l2d_sobolev_H10 hd0 P Q le_rfl (by rw [hPr]; linarith only [h3'])
      (by rw [hPr, hQr, inv_sobStar h3]; norm_num) hWb φ
    refine lt_of_le_of_lt h ?_
    refine ENNReal.mul_lt_top ENNReal.coe_lt_top ?_
    refine ENNReal.sum_lt_top.2 fun i _ => ?_
    exact (φ.toH1Function.gradMemL2 i).eLpNorm_lt_top

/-- **Hölder integrability**: a function in `L^{2_*}(W)` times an `H¹₀(W)` function is integrable. -/
theorem l2d_integrableOn_mul_H10 (hd : 2 ≤ d) {W : Set (Vec d)} (hWb : Bornology.IsBounded W)
    {X : Vec d → ℝ} (hX : MemLp X (ENNReal.ofReal (Real.conjExponent (sobStar d)))
      (volume.restrict W)) (φ : H10Function W) :
    IntegrableOn (fun x => X x * φ.toH1Function.toFun x) W := by
  have hs := two_lt_sobStar hd
  have hR : Real.HolderConjugate (Real.conjExponent (sobStar d)) (sobStar d) :=
    (Real.HolderConjugate.conjExponent (by linarith only [hs])).symm
  have : ENNReal.HolderConjugate (ENNReal.ofReal (Real.conjExponent (sobStar d)))
      (ENNReal.ofReal (sobStar d)) := hR.ennrealOfReal
  exact hX.integrable_mul (l2d_memLp_sobStar hd hWb φ)

/-- Satisfiability of the exponent bookkeeping in dimension `2` and `3`. -/
example : (∃ q : ℝ, 2 ≤ q ∧ q⁻¹ = (Real.conjExponent (sobStar 2))⁻¹ - ((2 : ℕ) : ℝ)⁻¹) ∧
    (∃ q : ℝ, 2 ≤ q ∧ q⁻¹ = (Real.conjExponent (sobStar 3))⁻¹ - ((3 : ℕ) : ℝ)⁻¹) :=
  ⟨(l2d_exponents (d := 2) le_rfl).2.2.2, (l2d_exponents (d := 3) (by norm_num)).2.2.2⟩

end SuperdiffusionCLT.Section7

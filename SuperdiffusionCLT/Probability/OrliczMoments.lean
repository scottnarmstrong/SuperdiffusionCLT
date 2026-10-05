/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Homogenization.Probability.IndependentSums.GammaSigma.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Moment bounds for `O_{Γ₂}` random variables

This module states the moment bound of Lemma `l.moments.gamma.psi` of the paper, display
`e.moments.OGamma2`: for `A ∈ (0, ∞)` and a random variable `X` with `|X| ≤ O_{Γ₂}(A)`,

`E[|X|^k] ≤ A^k (1 + γ(k/2 + 1))` for every `k ∈ ℕ`.

Here `X = O_Ψ(A)` is the tail relation `P[|X| > t A] ≤ Ψ(t)⁻¹` for every
`t ∈ [1, ∞)` and `Γ_σ(t) = exp(t ^ σ)`,
so `|X| ≤ O_{Γ₂}(A)` is the tail bound `P[|X| > t A] ≤ exp(-t²)` for `t ≥ 1`;
in the library this is exactly
`Homogenization.IndependentSums.IsBigO mu (gammaSigma 2) X A`.

The proof is the layer-cake computation of the paper,
carried out at unit amplitude and then rescaled: writing `E[|X|^k]` as the
layer-cake integral `k ∫_0^∞ P[|X| > t] t^{k-1} dt`, the contribution of
`t ∈ (0, 1]` is at most `1`, and on `t ∈ (1, ∞)` the tail bound is inserted;
the substitution `u = t²` turns the remaining integral into a gamma integral,
which the sharp kernel identity `∫_0^∞ t^{k-1} exp(-t²) dt = Γ(k/2)/2`
(Mathlib's `integral_rpow_mul_exp_neg_rpow`) evaluates to `Γ(k/2 + 1)` exactly.
The printed constant `1 + γ(k/2 + 1)` is therefore reached, with `γ` the gamma
function `Real.Gamma`.

The second display `e.moments.lognormal` of the same lemma —
`E[exp(NX) - 1] ≤ 3 max{AN exp(AN), A²N² exp(A²N²)}` — is
*not* proved here; it requires summing the exponential series in `N` and the
half-integer gamma values `γ(k + 1/2)`, and is left for a
follow-up module.

The module also exports the integrability behind the moment bound: under the
same hypotheses, `integrable_abs_rpow_of_isBigO_gammaSigma_two` shows that
`omega ↦ |X omega| ^ k` is integrable for every `k ∈ ℕ`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Probability

open MeasureTheory
open Homogenization

variable {Omega : Type*} [MeasurableSpace Omega]

/-- The rescaled tail bound behind the hypothesis `|X| ≤ O_{Γ₂}(A)` of the
printed lemma `l.moments.gamma.psi`: the symmetric tail
relation `|X| ≤ O_{Γ₂}(A)`, with
`Γ₂(t) = exp(t²)`, says `P[|X| > t A] ≤ exp(-t²)` for every
`t ≥ 1`; dividing by the amplitude `A` turns this into the unit-amplitude
tail bound used by the layer-cake computation below. -/
theorem gammaTwo_unit_tail_of_isBigO {mu : Measure Omega} {X : Omega → ℝ} {A : ℝ}
    (hA : 0 < A)
    (hX : IndependentSums.IsBigO mu (IndependentSums.gammaSigma 2) X A) :
    ∀ t : ℝ, 1 ≤ t →
      mu.real (IndependentSums.upperTailEvent (fun omega => |X omega| / A) t) ≤
        Real.exp (-(t ^ (2 : ℝ))) := by
  have hiff := (IndependentSums.isBigO_gammaSigma_iff (μ := mu) (X := X) (A := A)
    (σ := 2)).1 hX
  intro t ht
  have hset : IndependentSums.upperTailEvent (fun omega => |X omega| / A) t =
      IndependentSums.absTailEvent X (A * t) := by
    ext omega
    simp only [IndependentSums.upperTailEvent, IndependentSums.absTailEvent,
      Set.mem_ofPred_eq]
    rw [lt_div_iff₀ hA, mul_comm]
  rw [hset]
  exact hiff ht

/-- The layer-cake computation of the paper at unit
amplitude, in the finite-lintegral form shared by the two exported statements:
if `Y ≥ 0` satisfies the unit-scale `Γ₂` tail bound `P[Y > t] ≤ exp(-t²)` for
every `t ≥ 1`, then for every `k ∈ ℕ`,

`∫⁻ omega, ENNReal.ofReal (Y omega ^ (k : ℝ)) ∂mu ≤ ENNReal.ofReal (1 + γ(k/2 + 1))`,

with `γ` the gamma function. The right-hand side is finite; this is the fact
behind both the moment bound of display `e.moments.OGamma2`
at unit amplitude (`abs_moment_unit_le_of_gammaTwo_tail`, rescaled by the
amplitude in `abs_moment_le_of_isBigO_gammaSigma_two`) and the integrability
companion `integrable_abs_rpow_of_isBigO_gammaSigma_two`. -/
private theorem abs_moment_lintegral_le_of_gammaTwo_tail {mu : Measure Omega}
    [MeasureTheory.IsProbabilityMeasure mu] {Y : Omega → ℝ}
    (hYnn : ∀ omega, 0 ≤ Y omega) (hYm : AEMeasurable Y mu)
    (hY : ∀ t : ℝ, 1 ≤ t →
      mu.real (IndependentSums.upperTailEvent Y t) ≤ Real.exp (-(t ^ (2 : ℝ))))
    (k : ℕ) :
    ∫⁻ omega, ENNReal.ofReal (Y omega ^ (k : ℝ)) ∂mu ≤
      ENNReal.ofReal (1 + Real.Gamma ((k : ℝ) / 2 + 1)) := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    have hf0 : ∀ omega : Omega,
        ENNReal.ofReal (Y omega ^ ((0 : ℕ) : ℝ)) = (1 : ENNReal) := by
      intro omega
      simp
    have hG : ((0 : ℕ) : ℝ) / 2 + 1 = 1 := by norm_num
    rw [hG, Real.Gamma_one]
    rw [MeasureTheory.lintegral_congr hf0, MeasureTheory.lintegral_one, measure_univ,
      ← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by norm_num : (1 : ℝ) ≤ 1 + 1)
  · have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have hk0 : (0 : ℝ) ≤ (k : ℝ) := by linarith only [hk1]
    have hnn : 0 ≤ᵐ[mu] Y := Filter.Eventually.of_forall hYnn
    have hpowm : AEMeasurable (fun omega => Y omega ^ (k : ℝ)) mu :=
      hYm.pow measurable_const.aemeasurable
    have hLayer := MeasureTheory.lintegral_rpow_eq_lintegral_meas_lt_mul
      (μ := mu) hnn hYm (lt_of_lt_of_le zero_lt_one hk1)
    -- the two pointwise bounds on the measure of the layer {Y > t}
    have hTail1 : ∀ t : ℝ, mu {a | t < Y a} ≤ (1 : ENNReal) := by
      intro t
      calc mu {a | t < Y a} ≤ mu Set.univ := measure_mono (Set.subset_univ _)
        _ = 1 := measure_univ
    have hTail2 : ∀ t : ℝ, 1 ≤ t →
        mu {a | t < Y a} ≤ ENNReal.ofReal (Real.exp (-(t ^ (2 : ℝ)))) := by
      intro t ht
      have hset : IndependentSums.upperTailEvent Y t = {a | t < Y a} := rfl
      have heq : mu {a | t < Y a} =
          ENNReal.ofReal (mu.real (IndependentSums.upperTailEvent Y t)) := by
        rw [hset]
        simp [Measure.real]
      rw [heq]
      exact ENNReal.ofReal_le_ofReal (hY t ht)
    -- the contribution of t ∈ (0, 1] is the truncated part, of size 1/k
    have hf1 : IntegrableOn (fun t : ℝ => t ^ ((k : ℝ) - 1)) (Set.Ioc (0 : ℝ) 1) volume := by
      refine IntegrableOn.of_bound ?_ ?_ 1 ?_
      · rw [Real.volume_Ioc]
        exact ENNReal.ofReal_lt_top
      · exact (Real.continuous_rpow_const (by linarith only [hk1] :
          (0 : ℝ) ≤ (k : ℝ) - 1)).measurable.aestronglyMeasurable
      · filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with t ht
        rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg ht.1.le _)]
        exact Real.rpow_le_one ht.1.le ht.2 (by linarith only [hk1] :
          (0 : ℝ) ≤ (k : ℝ) - 1)
    have hnn1 : 0 ≤ᵐ[MeasureTheory.Measure.restrict volume (Set.Ioc (0 : ℝ) 1)]
        (fun t : ℝ => t ^ ((k : ℝ) - 1)) := by
      filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with t ht
      exact Real.rpow_nonneg ht.1.le _
    have hval1 : ∫ t : ℝ in Set.Ioc (0 : ℝ) 1, t ^ ((k : ℝ) - 1) = (1 : ℝ) / (k : ℝ) := by
      rw [← intervalIntegral.integral_of_le zero_le_one]
      rw [integral_rpow (r := (k : ℝ) - 1)
        (Or.inl (by linarith only [hk1] : (-1 : ℝ) < (k : ℝ) - 1))]
      rw [Real.one_rpow, Real.zero_rpow (by linarith only [hk1] : (k : ℝ) - 1 + 1 ≠ 0)]
      ring
    have hP1 : ∫⁻ t in Set.Ioc (0 : ℝ) 1,
        mu {a | t < Y a} * ENNReal.ofReal (t ^ ((k : ℝ) - 1)) ≤
          ENNReal.ofReal ((1 : ℝ) / (k : ℝ)) := by
      refine le_trans (lintegral_mono_ae
        (g := fun t : ℝ => ENNReal.ofReal (t ^ ((k : ℝ) - 1)))
        (Filter.Eventually.of_forall fun t => ?_)) ?_
      · have hpt : mu {a | t < Y a} * ENNReal.ofReal (t ^ ((k : ℝ) - 1)) ≤
            (1 : ENNReal) * ENNReal.ofReal (t ^ ((k : ℝ) - 1)) :=
          mul_le_mul_of_nonneg_right (hTail1 t)
            (by positivity : (0 : ENNReal) ≤ ENNReal.ofReal _)
        rwa [one_mul] at hpt
      · rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal
          (μ := MeasureTheory.Measure.restrict volume (Set.Ioc (0 : ℝ) 1)) hf1 hnn1]
        exact ENNReal.ofReal_le_ofReal (le_of_eq hval1)
    -- the contribution of t ∈ (1, ∞) carries the tail bound
    have hf2 : IntegrableOn
        (fun t : ℝ => t ^ ((k : ℝ) - 1) * Real.exp (-(t ^ (2 : ℝ))))
        (Set.Ioi (0 : ℝ)) volume :=
      Homogenization.IndependentSums.integrableOn_rpow_mul_exp_neg_rpow_of_pos
        (σ := 2) (p := (k : ℝ)) (by norm_num : (0 : ℝ) < 2)
        (lt_of_lt_of_le zero_lt_one hk1)
    have hf2' : IntegrableOn
        (fun t : ℝ => t ^ ((k : ℝ) - 1) * Real.exp (-(t ^ (2 : ℝ))))
        (Set.Ioi (1 : ℝ)) volume :=
      hf2.mono_set (Set.Ioi_subset_Ioi zero_le_one)
    have hnn2 : 0 ≤ᵐ[MeasureTheory.Measure.restrict volume (Set.Ioi (1 : ℝ))]
        (fun t : ℝ => t ^ ((k : ℝ) - 1) * Real.exp (-(t ^ (2 : ℝ)))) := by
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
      exact mul_nonneg
        (Real.rpow_nonneg (by linarith only [Set.mem_Ioi.mp ht] : (0 : ℝ) ≤ t) _)
        (Real.exp_nonneg _)
    have hpoint2 : ∀ t : ℝ, 1 ≤ t →
        mu {a | t < Y a} * ENNReal.ofReal (t ^ ((k : ℝ) - 1)) ≤
          ENNReal.ofReal (t ^ ((k : ℝ) - 1) * Real.exp (-(t ^ (2 : ℝ)))) := by
      intro t ht
      have h1 : mu {a | t < Y a} * ENNReal.ofReal (t ^ ((k : ℝ) - 1)) ≤
          ENNReal.ofReal (Real.exp (-(t ^ (2 : ℝ)))) *
            ENNReal.ofReal (t ^ ((k : ℝ) - 1)) :=
        mul_le_mul_of_nonneg_right (hTail2 t ht)
          (by positivity : (0 : ENNReal) ≤ ENNReal.ofReal _)
      rw [← ENNReal.ofReal_mul (Real.exp_nonneg _),
        mul_comm (Real.exp (-(t ^ (2 : ℝ)))) (t ^ ((k : ℝ) - 1))] at h1
      exact h1
    have hval2 : ∫ t : ℝ in Set.Ioi (1 : ℝ),
        t ^ ((k : ℝ) - 1) * Real.exp (-(t ^ (2 : ℝ))) ≤
          (1 : ℝ) / 2 * Real.Gamma ((k : ℝ) / 2) := by
      refine le_trans (b := ∫ t : ℝ in Set.Ioi (0 : ℝ),
        t ^ ((k : ℝ) - 1) * Real.exp (-(t ^ (2 : ℝ)))) ?_ ?_
      · refine setIntegral_mono_set hf2 ?_ ?_
        · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
          exact mul_nonneg (Real.rpow_nonneg (Set.mem_Ioi.mp ht).le _)
            (Real.exp_nonneg _)
        · exact (Set.Ioi_subset_Ioi zero_le_one).eventuallyLE
      · rw [integral_rpow_mul_exp_neg_rpow (p := 2) (q := (k : ℝ) - 1)
          (by norm_num : (0 : ℝ) < 2)
          (by linarith only [hk1] : (-1 : ℝ) < (k : ℝ) - 1)]
        have harg : ((k : ℝ) - 1 + 1) / 2 = (k : ℝ) / 2 := by ring
        rw [harg]
    have hP2 : ∫⁻ t in Set.Ioi (1 : ℝ),
        mu {a | t < Y a} * ENNReal.ofReal (t ^ ((k : ℝ) - 1)) ≤
          ENNReal.ofReal ((1 : ℝ) / 2 * Real.Gamma ((k : ℝ) / 2)) := by
      refine le_trans (lintegral_mono_ae
        (g := fun t : ℝ =>
          ENNReal.ofReal (t ^ ((k : ℝ) - 1) * Real.exp (-(t ^ (2 : ℝ))))) ?_) ?_
      · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
        exact hpoint2 t (Set.mem_Ioi.mp ht).le
      · rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal
          (μ := MeasureTheory.Measure.restrict volume (Set.Ioi (1 : ℝ))) hf2' hnn2]
        exact ENNReal.ofReal_le_ofReal hval2
    -- the split of the layer-cake integral at t = 1
    have hIoi : Set.Ioi (0 : ℝ) = Set.Ioc (0 : ℝ) 1 ∪ Set.Ioi (1 : ℝ) := by
      ext x
      simp only [Set.mem_Ioi, Set.mem_Ioc, Set.mem_union]
      constructor
      · intro hx
        by_cases h1 : x ≤ 1
        · exact Or.inl ⟨hx, h1⟩
        · exact Or.inr (lt_of_not_ge h1)
      · rintro (⟨hx, _⟩ | h)
        · exact hx
        · exact lt_trans zero_lt_one h
    have hgamma : (k : ℝ) * ((1 : ℝ) / 2 * Real.Gamma ((k : ℝ) / 2)) =
        Real.Gamma ((k : ℝ) / 2 + 1) := by
      rw [Real.Gamma_add_one (by linarith only [hk1] : (k : ℝ) / 2 ≠ 0)]
      ring
    have hprod1 : ENNReal.ofReal (k : ℝ) * ENNReal.ofReal ((1 : ℝ) / (k : ℝ)) =
        ENNReal.ofReal 1 := by
      rw [← ENNReal.ofReal_mul hk0]
      congr 1
      exact mul_one_div_cancel (ne_of_gt (lt_of_lt_of_le zero_lt_one hk1))
    have hprod2 : ENNReal.ofReal (k : ℝ) *
        ENNReal.ofReal ((1 : ℝ) / 2 * Real.Gamma ((k : ℝ) / 2)) =
        ENNReal.ofReal (Real.Gamma ((k : ℝ) / 2 + 1)) := by
      rw [← ENNReal.ofReal_mul hk0, hgamma]
    have hbound : ∫⁻ omega, ENNReal.ofReal (Y omega ^ (k : ℝ)) ∂mu ≤
        ENNReal.ofReal (1 + Real.Gamma ((k : ℝ) / 2 + 1)) := by
      calc ∫⁻ omega, ENNReal.ofReal (Y omega ^ (k : ℝ)) ∂mu
          = ENNReal.ofReal (k : ℝ) * ∫⁻ t in Set.Ioi (0 : ℝ),
              mu {a | t < Y a} * ENNReal.ofReal (t ^ ((k : ℝ) - 1)) := hLayer
        _ ≤ ENNReal.ofReal (k : ℝ) *
              (∫⁻ t in Set.Ioc (0 : ℝ) 1,
                  mu {a | t < Y a} * ENNReal.ofReal (t ^ ((k : ℝ) - 1)) ∂volume
                + ∫⁻ t in Set.Ioi (1 : ℝ),
                  mu {a | t < Y a} * ENNReal.ofReal (t ^ ((k : ℝ) - 1)) ∂volume) := by
              refine mul_le_mul' le_rfl ?_
              rw [hIoi]
              exact lintegral_union_le _ _ _
        _ ≤ ENNReal.ofReal (k : ℝ) *
              (ENNReal.ofReal ((1 : ℝ) / (k : ℝ)) +
                ENNReal.ofReal ((1 : ℝ) / 2 * Real.Gamma ((k : ℝ) / 2))) :=
              mul_le_mul' le_rfl (add_le_add hP1 hP2)
        _ = ENNReal.ofReal (1 + Real.Gamma ((k : ℝ) / 2 + 1)) := by
              rw [mul_add, hprod1, hprod2, ← ENNReal.ofReal_add zero_le_one
                (Real.Gamma_nonneg_of_nonneg
                  (by linarith only [hk1] : (0 : ℝ) ≤ (k : ℝ) / 2 + 1))]
    exact hbound

/-- The layer-cake computation of the paper at unit
amplitude: if `Y ≥ 0` satisfies the unit-scale `Γ₂` tail bound
`P[Y > t] ≤ exp(-t²)` for every `t ≥ 1`, then for every `k ∈ ℕ`,

`E[Y^k] ≤ 1 + γ(k/2 + 1)`,

with `γ` the gamma function. This is display `e.moments.OGamma2` with `A = 1`; the general
amplitude follows by rescaling in `abs_moment_le_of_isBigO_gammaSigma_two`. -/
private theorem abs_moment_unit_le_of_gammaTwo_tail {mu : Measure Omega}
    [MeasureTheory.IsProbabilityMeasure mu] {Y : Omega → ℝ}
    (hYnn : ∀ omega, 0 ≤ Y omega) (hYm : AEMeasurable Y mu)
    (hY : ∀ t : ℝ, 1 ≤ t →
      mu.real (IndependentSums.upperTailEvent Y t) ≤ Real.exp (-(t ^ (2 : ℝ))))
    (k : ℕ) :
    ∫ omega, Y omega ^ (k : ℝ) ∂mu ≤ 1 + Real.Gamma ((k : ℝ) / 2 + 1) := by
  have hnn_pow : 0 ≤ᵐ[mu] fun omega => Y omega ^ (k : ℝ) :=
    Filter.Eventually.of_forall fun omega => Real.rpow_nonneg (hYnn omega) _
  have hpowm : AEMeasurable (fun omega => Y omega ^ (k : ℝ)) mu :=
    hYm.pow measurable_const.aemeasurable
  have hbound := abs_moment_lintegral_le_of_gammaTwo_tail hYnn hYm hY k
  rw [MeasureTheory.integral_eq_lintegral_of_nonneg_ae hnn_pow
    hpowm.aestronglyMeasurable]
  have hfin : ∫⁻ omega, ENNReal.ofReal (Y omega ^ (k : ℝ)) ∂mu < (⊤ : ENNReal) :=
    lt_of_le_of_lt hbound ENNReal.ofReal_lt_top
  have hto := (ENNReal.toReal_le_toReal hfin.ne ENNReal.ofReal_ne_top).2 hbound
  have hc : 0 ≤ 1 + Real.Gamma ((k : ℝ) / 2 + 1) :=
    add_nonneg zero_le_one (Real.Gamma_nonneg_of_nonneg
      (by positivity : (0 : ℝ) ≤ (k : ℝ) / 2 + 1))
  simpa [hc] using hto

/-- The moment bound of the printed lemma `l.moments.gamma.psi`, display `e.moments.OGamma2`: for
`A ∈ (0, ∞)`, a random variable `X` with `|X| ≤ O_{Γ₂}(A)` — the tail relation
`P[|X| > t A] ≤ exp(-t²)` for every `t ≥ 1` — and every `k ∈ ℕ`,

`E[|X|^k] ≤ A^k (1 + γ(k/2 + 1))`,

with `γ` the gamma function `Real.Gamma`. This is the printed constant
`1 + γ(k/2 + 1)` exactly; the proof is the layer-cake
computation of the paper, carried out at unit amplitude
(`abs_moment_unit_le_of_gammaTwo_tail`) and rescaled by `A^k`. -/
theorem abs_moment_le_of_isBigO_gammaSigma_two {mu : Measure Omega}
    [MeasureTheory.IsProbabilityMeasure mu] {X : Omega → ℝ} {A : ℝ}
    (hA : 0 < A) (hXm : AEMeasurable X mu)
    (hX : IndependentSums.IsBigO mu (IndependentSums.gammaSigma 2) X A)
    (k : ℕ) :
    ∫ omega, |X omega| ^ (k : ℝ) ∂mu ≤
      A ^ (k : ℝ) * (1 + Real.Gamma ((k : ℝ) / 2 + 1)) := by
  have hYtail : ∀ t : ℝ, 1 ≤ t →
      mu.real (IndependentSums.upperTailEvent (fun omega => |X omega| / A) t) ≤
        Real.exp (-(t ^ (2 : ℝ))) := fun t ht => gammaTwo_unit_tail_of_isBigO hA hX t ht
  have hunit := abs_moment_unit_le_of_gammaTwo_tail (mu := mu)
    (Y := fun omega => |X omega| / A)
    (fun omega => div_nonneg (abs_nonneg _) hA.le)
    ((continuous_abs.measurable.comp_aemeasurable hXm).div_const A) hYtail k
  have hfun : (fun omega => |X omega| ^ (k : ℝ)) =
      fun omega => A ^ (k : ℝ) * (|X omega| / A) ^ (k : ℝ) := by
    funext omega
    have h1 : |X omega| ^ (k : ℝ) = (A * (|X omega| / A)) ^ (k : ℝ) := by
      congr 1
      field_simp
    rw [h1, Real.mul_rpow hA.le (div_nonneg (abs_nonneg _) hA.le)]
  rw [hfun, MeasureTheory.integral_const_mul]
  exact mul_le_mul_of_nonneg_left hunit (Real.rpow_nonneg hA.le (k : ℝ))

/-- The integrability companion of `abs_moment_le_of_isBigO_gammaSigma_two`,
under the same hypotheses as that moment bound: for `A ∈ (0, ∞)`, a random
variable `X` with `|X| ≤ O_{Γ₂}(A)` (the tail relation `P[|X| > t A] ≤
exp(-t²)` for every `t ≥ 1`) and every `k ∈ ℕ`, the function
`omega ↦ |X omega| ^ k` is integrable. The proof exports the finiteness of the
lintegral established by the layer-cake computation
(`abs_moment_lintegral_le_of_gammaTwo_tail`, at unit amplitude) through the
rescaling `|X ω| ^ k = A ^ k * (|X ω| / A) ^ k`. -/
theorem integrable_abs_rpow_of_isBigO_gammaSigma_two {mu : Measure Omega}
    [MeasureTheory.IsProbabilityMeasure mu] {X : Omega → ℝ} {A : ℝ}
    (hA : 0 < A) (hXm : AEMeasurable X mu)
    (hX : IndependentSums.IsBigO mu (IndependentSums.gammaSigma 2) X A)
    (k : ℕ) :
    MeasureTheory.Integrable (fun omega => |X omega| ^ (k : ℝ)) mu := by
  have hYtail : ∀ t : ℝ, 1 ≤ t →
      mu.real (IndependentSums.upperTailEvent (fun omega => |X omega| / A) t) ≤
        Real.exp (-(t ^ (2 : ℝ))) := fun t ht => gammaTwo_unit_tail_of_isBigO hA hX t ht
  have hbound := abs_moment_lintegral_le_of_gammaTwo_tail (mu := mu)
    (Y := fun omega => |X omega| / A)
    (fun omega => div_nonneg (abs_nonneg _) hA.le)
    ((continuous_abs.measurable.comp_aemeasurable hXm).div_const A) hYtail k
  -- the pointwise factorization `|X ω| ^ k = A ^ k * (|X ω| / A) ^ k`
  have hfun : (fun omega => |X omega| ^ (k : ℝ)) =
      fun omega => A ^ (k : ℝ) * (|X omega| / A) ^ (k : ℝ) := by
    funext omega
    have h1 : |X omega| ^ (k : ℝ) = (A * (|X omega| / A)) ^ (k : ℝ) := by
      congr 1
      field_simp
    rw [h1, Real.mul_rpow hA.le (div_nonneg (abs_nonneg _) hA.le)]
  have hApos : (0 : ℝ) ≤ A ^ (k : ℝ) := Real.rpow_nonneg hA.le (k : ℝ)
  -- the finite lintegral, pulled through the rescaling
  have hlint : ∫⁻ omega, ENNReal.ofReal (|X omega| ^ (k : ℝ)) ∂mu
      = ENNReal.ofReal (A ^ (k : ℝ)) *
        ∫⁻ omega, ENNReal.ofReal ((|X omega| / A) ^ (k : ℝ)) ∂mu := by
    have hgm : AEMeasurable
        (fun omega => ENNReal.ofReal ((|X omega| / A) ^ (k : ℝ))) mu :=
      ENNReal.measurable_ofReal.comp_aemeasurable
        ((continuous_abs.measurable.comp_aemeasurable hXm).div_const A
          |>.pow measurable_const.aemeasurable)
    have hsplit : (fun omega => ENNReal.ofReal (|X omega| ^ (k : ℝ))) =
        fun omega => ENNReal.ofReal (A ^ (k : ℝ)) *
          ENNReal.ofReal ((|X omega| / A) ^ (k : ℝ)) := by
      funext omega
      have hp := congrFun hfun omega
      rw [hp]
      exact ENNReal.ofReal_mul hApos
    rw [hsplit]
    exact MeasureTheory.lintegral_const_mul'' (ENNReal.ofReal (A ^ (k : ℝ))) hgm
  refine ⟨?_, ?_⟩
  · exact ((continuous_abs.measurable.comp_aemeasurable hXm).pow
      measurable_const.aemeasurable).aestronglyMeasurable
  · have hnn : 0 ≤ᵐ[mu] (fun omega => |X omega| ^ (k : ℝ)) :=
      Filter.Eventually.of_forall fun omega => Real.rpow_nonneg (abs_nonneg _) _
    rw [MeasureTheory.hasFiniteIntegral_iff_ofReal hnn, hlint]
    exact lt_of_le_of_lt (mul_le_mul_right hbound _)
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)

end SuperdiffusionCLT.Probability
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Estimates.Stream.IncrementMoreoverBlockG
public import Homogenization.Deterministic.MultiscaleQuantities

@[expose] public section

namespace SuperdiffusionCLT.Section4.MinimalScales

open MeasureTheory
open Homogenization.IndependentSums
open Homogenization.Book.Ch05.Section57

/-- The union bound over the scales, with a per-scale bound
`μ(Bad k) ≤ k⁻² exp(-(k/B)^η)` for every `k` at least `N ≥ 2`. -/
theorem srootMS_badTail_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] {Bad : ℕ → Set Ω} {B eta : ℝ} (hB : 0 < B) (heta : 0 ≤ eta)
    (hper : ∀ k : ℕ, μ.real (Bad k) ≤
      (((k : ℝ) ^ 2)⁻¹) * Real.exp (-(((k : ℝ) / B) ^ eta)))
    {N : ℕ} (hN : 2 ≤ N) :
    μ.real (badTailEvent Bad N) ≤ Real.exp (-(((N : ℝ) / B) ^ eta)) := by
  have hN1 : 1 ≤ N := le_trans (by norm_num) hN
  set E : ℝ := Real.exp (-(((N : ℝ) / B) ^ eta)) with hE
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  have hw : ∀ j : ℕ, μ.real (Bad (N + j)) ≤ (((N + j : ℕ) : ℝ) ^ 2)⁻¹ * E := by
    intro j
    refine le_trans (hper (N + j)) (mul_le_mul_of_nonneg_left ?_ (by positivity))
    refine Real.exp_le_exp.2 (neg_le_neg ?_)
    refine Real.rpow_le_rpow (by positivity) ?_ heta
    refine div_le_div_of_nonneg_right ?_ hB.le
    exact_mod_cast Nat.le_add_right N j
  have hsum : Summable fun j : ℕ => (((N + j : ℕ) : ℝ) ^ 2)⁻¹ * E :=
    (SuperdiffusionCLT.Section2.Estimates.Stream.summable_inv_sq_shift N).mul_right E
  have hmeas : μ (badTailEvent Bad N) ≤
      ENNReal.ofReal (∑' j : ℕ, (((N + j : ℕ) : ℝ) ^ 2)⁻¹ * E) := by
    refine le_trans (SuperdiffusionCLT.Section2.Estimates.Stream.measure_badTailEvent_le_tsum Bad N) ?_
    rw [ENNReal.ofReal_tsum_of_nonneg (fun j => by positivity) hsum]
    refine ENNReal.tsum_le_tsum fun j => ?_
    rw [← ofReal_measureReal (measure_ne_top μ _)]
    exact ENNReal.ofReal_le_ofReal (hw j)
  have htsum : ∑' j : ℕ, (((N + j : ℕ) : ℝ) ^ 2)⁻¹ * E ≤ E := by
    rw [tsum_mul_right]
    have h2 := SuperdiffusionCLT.Section2.Estimates.Stream.tsum_inv_sq_shift_le hN1
    have hNr : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have h1 : 2 / (N : ℝ) ≤ 1 := by
      rw [div_le_one (by linarith only [hNr])]; exact hNr
    calc (∑' j : ℕ, (((N + j : ℕ) : ℝ) ^ 2)⁻¹) * E ≤ 1 * E :=
          mul_le_mul_of_nonneg_right (le_trans h2 h1) hE0
      _ = E := one_mul E
  have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hmeas
  rw [ENNReal.toReal_ofReal (tsum_nonneg fun j => by positivity)] at this
  exact le_trans this htsum

/-- **The minimal scale of `p.minimal.scales`**, from a per-scale bad-event bound. The minimal
scale is the triadic scale above which no bad event occurs, with floor `0`; the per-scale
bound makes `log X` a `Γ_η` variable at amplitude exactly `A`. -/
theorem srootMS_minimalScale {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] {Bad : ℕ → Set Ω} (hBad : ∀ k, MeasurableSet (Bad k))
    {A eta : ℝ} (hA : 4 * Real.log 3 ≤ A) (heta : 0 < eta)
    (hper : ∀ k : ℕ, μ.real (Bad k) ≤
      (((k : ℝ) ^ 2)⁻¹) * Real.exp (-((2 * Real.log 3 * (k : ℝ) / A) ^ eta))) :
    ∃ X : Ω → ℝ, Measurable X ∧
      IsBigO μ (gammaSigma eta) (fun ω => Real.log (X ω)) A ∧
      ∀ᵐ ω ∂μ, ∀ m : ℕ, X ω ≤ (3 : ℝ) ^ m → ω ∉ Bad m := by
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  set B : ℝ := A / (2 * Real.log 3) with hBdef
  have hB2 : 2 ≤ B := by
    rw [hBdef, le_div_iff₀ (by positivity)]; linarith only [hA]
  have hBpos : 0 < B := lt_of_lt_of_le (by norm_num) hB2
  have hdiv : ∀ k : ℕ, (k : ℝ) / B = 2 * Real.log 3 * (k : ℝ) / A := by
    intro k
    rw [hBdef]
    field_simp
  have hper' : ∀ k : ℕ, μ.real (Bad k) ≤
      (((k : ℝ) ^ 2)⁻¹) * Real.exp (-(((k : ℝ) / B) ^ (2 * (eta / 2)))) := by
    intro k
    rw [show 2 * (eta / 2) = eta by ring, hdiv k]
    exact hper k
  have htail : ∀ N : ℕ, B ≤ (N : ℝ) →
      μ.real (badTailEvent Bad N) ≤ Real.exp (-(((N : ℝ) / B) ^ (2 * (eta / 2)))) := by
    intro N hN
    have hN2 : 2 ≤ N := by
      have : (2 : ℝ) ≤ N := le_trans hB2 hN
      exact_mod_cast this
    exact srootMS_badTail_le hBpos (by positivity) hper' hN2
  refine ⟨quenchedMinimalScale 0 Bad, SuperdiffusionCLT.Section2.Estimates.Stream.measurable_quenchedMinimalScale hBad 0, ?_, ?_⟩
  · have h := SuperdiffusionCLT.Section2.Estimates.Stream.isBigO_gammaSigma_log_quenchedMinimalScale (mu := μ) (N0 := 0)
      (Bad := Bad) (B := B) (sigma := eta / 2) (by positivity)
      (by simp only [Nat.cast_zero, zero_add]; linarith only [hB2]) htail
    have hamp : 2 * B * Real.log 3 = A := by
      rw [hBdef]; field_simp
    rw [hamp, show 2 * (eta / 2) = eta by ring] at h
    exact h
  · filter_upwards [SuperdiffusionCLT.Section2.Estimates.Stream.ae_hasGoodTailFrom_of_expTail (N0 := 0) (by positivity) hBpos
      htail] with ω hgood m hm
    have hidx := quenchedMinimalScaleIndex_le_of_scale_le_pow hm
    exact not_mem_bad_of_quenchedMinimalScaleIndex_le hgood hidx le_rfl

/-- The two-term tail bound behind the per-scale union bound of
`e.new.mixing.minscale.one.scale`: a sum of a `Γ_{σ₁}` and a
`Γ_{σ₂}` variable exceeds `thr` only if one of them exceeds `thr / 2`. -/
theorem srootMS_measureReal_lt_add_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] {f g : Ω → ℝ} {A1 A2 σ1 σ2 thr : ℝ} (hA1 : 0 < A1) (hA2 : 0 < A2)
    (hf : IsBigO μ (gammaSigma σ1) f A1) (hg : IsBigO μ (gammaSigma σ2) g A2)
    (hT1 : 1 ≤ thr / (2 * A1)) (hT2 : 1 ≤ thr / (2 * A2)) :
    μ.real {ω | thr < f ω + g ω} ≤
      Real.exp (-((thr / (2 * A1)) ^ σ1)) + Real.exp (-((thr / (2 * A2)) ^ σ2)) := by
  have h1 : A1 * (thr / (2 * A1)) = thr / 2 := by field_simp
  have h2 : A2 * (thr / (2 * A2)) = thr / 2 := by field_simp
  have hsub : {ω | thr < f ω + g ω} ⊆
      absTailEvent f (A1 * (thr / (2 * A1))) ∪ absTailEvent g (A2 * (thr / (2 * A2))) := by
    intro ω hω
    rw [h1, h2]
    simp only [Set.mem_ofPred_eq] at hω
    by_contra hcon
    simp only [Set.mem_union, mem_absTailEvent, not_or, not_lt] at hcon
    have hf' := le_abs_self (f ω)
    have hg' := le_abs_self (g ω)
    linarith only [hω, hcon.1, hcon.2, hf', hg']
  refine le_trans (measureReal_mono hsub) (le_trans (measureReal_union_le _ _) ?_)
  exact add_le_add (isBigO_gammaSigma_iff.1 hf hT1) (isBigO_gammaSigma_iff.1 hg hT2)

/-- An admissible translation index is bounded: if `3^{n-3}k + cu_n ⊆ cu_m`
with `n ≤ m`, then every `|k_i| ≤ 3^{m-n+3}`. -/
theorem srootMS_abs_index_le {d : ℕ} {m n : ℕ} (hnm : n ≤ m) {k : Fin d → ℤ}
    (hk : (fun x => (fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x) ''
        Homogenization.cubeSet (Homogenization.originCube d (n : ℤ)) ⊆
      Homogenization.cubeSet (Homogenization.originCube d (m : ℤ))) (i : Fin d) :
    |k i| ≤ (3 : ℤ) ^ (m - n + 3) := by
  have h3n : (0 : ℝ) < (3 : ℝ) ^ (n : ℤ) := zpow_pos (by norm_num) _
  have h0 : (0 : Fin d → ℝ) ∈ Homogenization.cubeSet (Homogenization.originCube d (n : ℤ)) := by
    intro j
    simp only [Homogenization.originCube, Homogenization.cubeScaleFactor, Pi.zero_apply,
      Int.cast_zero, zero_sub, zero_add]
    constructor <;> nlinarith only [h3n]
  have hmem := hk ⟨0, h0, rfl⟩
  have hi := hmem i
  simp only [Homogenization.originCube, Homogenization.cubeScaleFactor, Pi.add_apply,
    Pi.zero_apply, add_zero, Int.cast_zero, zero_sub, zero_add] at hi
  have hpos : (0 : ℝ) < (3 : ℝ) ^ ((n : ℤ) - 3) := zpow_pos (by norm_num) _
  have hm : (3 : ℝ) ^ (m : ℤ) = (3 : ℝ) ^ ((n : ℤ) - 3) * (3 : ℝ) ^ (m - n + 3) := by
    rw [← zpow_natCast, ← zpow_add₀ (by norm_num)]
    congr 1
    push_cast [hnm]
    ring
  rw [hm] at hi
  have hB : (0 : ℝ) ≤ (3 : ℝ) ^ (m - n + 3) := by positivity
  have habs : |(k i : ℝ)| ≤ (3 : ℝ) ^ (m - n + 3) := by
    rw [abs_le]
    constructor
    · by_contra hc
      push Not at hc
      have := mul_lt_mul_of_pos_left hc hpos
      nlinarith only [this, hi.1, hpos, hB]
    · by_contra hc
      push Not at hc
      have := mul_lt_mul_of_pos_left hc hpos
      nlinarith only [this, hi.2, hpos, hB]
  have : ((|k i| : ℤ) : ℝ) ≤ (((3 : ℤ) ^ (m - n + 3) : ℤ) : ℝ) := by
    push_cast
    exact habs
  exact_mod_cast this

/-- The multiscale homogenization error with `p = ∞`, `q = 2` is nonnegative. -/
theorem srootMS_homErr_nonneg {d : ℕ} (Q : Homogenization.TriadicCube d) {s : ℝ} (hs : 0 ≤ s)
    (a : Homogenization.CoeffField d) (a0 : Homogenization.Mat d) :
    0 ≤ Homogenization.HomogenizationErrorOnCube Q s Homogenization.MultiscaleExponent.infinity
      (Homogenization.MultiscaleExponent.finite 2) a a0 := by
  unfold Homogenization.HomogenizationErrorOnCube Homogenization.HomogenizationError
    Homogenization.HomogenizationErrorFinite
  refine Real.rpow_nonneg (tsum_nonneg fun l => mul_nonneg ?_ ?_) _
  · unfold Homogenization.geometricWeight Homogenization.geometricDiscount
    refine mul_nonneg ?_ (Real.rpow_nonneg (by norm_num) _)
    have : Real.rpow (3 : ℝ) (-s * 2) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith only [hs])
    linarith only [this]
  · have h := Real.rpow_two (Homogenization.scaleResponseAtScale Q (Q.scale - (l : ℤ))
      Homogenization.MultiscaleExponent.infinity a a0)
    change 0 ≤ (Homogenization.scaleResponseAtScale Q (Q.scale - (l : ℤ))
      Homogenization.MultiscaleExponent.infinity a a0) ^ (2 : ℝ)
    rw [h]
    exact sq_nonneg _

end SuperdiffusionCLT.Section4.MinimalScales

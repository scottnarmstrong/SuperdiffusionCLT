/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Prereq.CenteringB

@[expose] public section

open scoped ENNReal
open scoped Matrix.Norms.L2Operator

/-!
# Centring: the weighted sum and the conclusion

The pairing of the centred stream matrix entry against a mean-zero test function is controlled by
its martingale differences (child minus parent averages) against the corresponding increments of the
test function.  That inequality is taken here in its natural form as a hypothesis `hPair`: for every
bound `D t` on the child-minus-parent differences of the entry at depth `t`, the pairing `I` is at
most `∑ D t * W t`, where `W t` is the size of the depth-`t` increment of the test function.  The
test function has `W t ≤ Cg r^t` with `r < 1` (for the normalized indicator of a `C^{1,1}`
domain, `r = 3^{-θ}`).  The window clause then gives
`D t = (max (log m) t + max (log m) (t + 1)) δ m^σ`, and the weighted sum is of order
`(1 + log m) m^σ`; a slightly larger exponent absorbs the logarithm.

## Main results

* `Section7.kc1_weighted_sum`: the deterministic weighted sum.
* `Section7.kc1_centering_of_clause`: the conclusion at one scale, from the window clause.
* `Section7.kc1_centering_ae`: the almost-sure conclusion for all scales `3^m ≥ K`.
-/

namespace SuperdiffusionCLT.Section7

open Homogenization MeasureTheory Homogenization.Book.Ch02

variable {d : ℕ}

/-- The geometric weighted sum, in closed form. -/
theorem kc1_geom_sum_le {L r : ℝ} (hL : 0 ≤ L) (hr0 : 0 ≤ r) (hr1 : r < 1) (m : ℕ) :
    ∑ t ∈ Finset.range m, (max L (t : ℝ) + max L ((t + 1 : ℕ) : ℝ)) * r ^ t ≤
      (2 * L + 1) / (1 - r) + 2 * r / (1 - r) ^ 2 := by
  have hr : ‖r‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_nonneg hr0]
  have hs1 : Summable fun t : ℕ => r ^ t := summable_geometric_of_lt_one hr0 hr1
  have hs2 : Summable fun t : ℕ => (t : ℝ) * r ^ t := by
    simpa using summable_pow_mul_geometric_of_norm_lt_one 1 hr
  have hf : ∀ t : ℕ, (max L (t : ℝ) + max L ((t + 1 : ℕ) : ℝ)) * r ^ t ≤
      (2 * L + 1) * r ^ t + 2 * ((t : ℝ) * r ^ t) := by
    intro t
    have h1 : max L (t : ℝ) ≤ L + t := max_le (by linarith only [Nat.cast_nonneg (α := ℝ) t])
      (by linarith only [hL])
    have h2 : max L ((t + 1 : ℕ) : ℝ) ≤ L + t + 1 := by
      push_cast
      exact max_le (by linarith only [Nat.cast_nonneg (α := ℝ) t])
        (by linarith only [hL])
    have hrt : 0 ≤ r ^ t := pow_nonneg hr0 t
    nlinarith only [mul_le_mul_of_nonneg_right (add_le_add h1 h2) hrt]
  have hsum : Summable fun t : ℕ => (2 * L + 1) * r ^ t + 2 * ((t : ℝ) * r ^ t) :=
    (hs1.mul_left _).add (hs2.mul_left _)
  have hnn : ∀ t : ℕ, 0 ≤ (max L (t : ℝ) + max L ((t + 1 : ℕ) : ℝ)) * r ^ t := fun t =>
    mul_nonneg (add_nonneg (le_trans hL (le_max_left _ _)) (le_trans hL (le_max_left _ _)))
      (pow_nonneg hr0 t)
  calc ∑ t ∈ Finset.range m, (max L (t : ℝ) + max L ((t + 1 : ℕ) : ℝ)) * r ^ t
      ≤ ∑ t ∈ Finset.range m, ((2 * L + 1) * r ^ t + 2 * ((t : ℝ) * r ^ t)) :=
        Finset.sum_le_sum fun t _ => hf t
    _ ≤ ∑' t : ℕ, ((2 * L + 1) * r ^ t + 2 * ((t : ℝ) * r ^ t)) :=
        hsum.sum_le_tsum _ fun t _ => by
          have := hnn t
          nlinarith only [this, hf t]
    _ = (2 * L + 1) / (1 - r) + 2 * r / (1 - r) ^ 2 := by
        rw [(hs1.mul_left _).tsum_add (hs2.mul_left _), tsum_mul_left, tsum_mul_left,
          tsum_geometric_of_lt_one hr0 hr1, tsum_coe_mul_geometric_of_norm_lt_one hr]
        field_simp

/-- **The weighted sum.** -/
theorem kc1_weighted_sum {L r Cg δ M : ℝ} {W : ℕ → ℝ} {m : ℕ} (hL : 0 ≤ L) (hr0 : 0 ≤ r)
    (hr1 : r < 1) (hCg : 0 ≤ Cg) (hδM : 0 ≤ δ * M)
    (hW : ∀ t, 0 ≤ W t ∧ W t ≤ Cg * r ^ t) :
    ∑ t ∈ Finset.range m,
        ((max L (t : ℝ) + max L ((t + 1 : ℕ) : ℝ)) * δ * M) * W t ≤
      Cg * (δ * M) * ((2 * L + 1) / (1 - r) + 2 * r / (1 - r) ^ 2) := by
  have hgeom := kc1_geom_sum_le hL hr0 hr1 m
  calc ∑ t ∈ Finset.range m,
        ((max L (t : ℝ) + max L ((t + 1 : ℕ) : ℝ)) * δ * M) * W t
      ≤ ∑ t ∈ Finset.range m,
          (Cg * (δ * M)) * ((max L (t : ℝ) + max L ((t + 1 : ℕ) : ℝ)) * r ^ t) := by
        refine Finset.sum_le_sum fun t _ => ?_
        have hmx : 0 ≤ max L (t : ℝ) + max L ((t + 1 : ℕ) : ℝ) :=
          add_nonneg (le_trans hL (le_max_left _ _)) (le_trans hL (le_max_left _ _))
        have h1 := mul_le_mul_of_nonneg_left (hW t).2 (mul_nonneg hmx hδM)
        calc ((max L (t : ℝ) + max L ((t + 1 : ℕ) : ℝ)) * δ * M) * W t
            = ((max L (t : ℝ) + max L ((t + 1 : ℕ) : ℝ)) * (δ * M)) * W t := by ring
          _ ≤ ((max L (t : ℝ) + max L ((t + 1 : ℕ) : ℝ)) * (δ * M)) * (Cg * r ^ t) := h1
          _ = _ := by ring
    _ = (Cg * (δ * M)) * ∑ t ∈ Finset.range m,
          ((max L (t : ℝ) + max L ((t + 1 : ℕ) : ℝ)) * r ^ t) := by
        rw [Finset.mul_sum]
    _ ≤ Cg * (δ * M) * ((2 * L + 1) / (1 - r) + 2 * r / (1 - r) ^ 2) :=
        mul_le_mul_of_nonneg_left hgeom (mul_nonneg hCg hδM)

/-- **The centring bound at one scale, with the logarithm.** The window clause at scale `m ≥ 2`
(with `δ = 1/2`) and the pairing inequality `hPair` give
`|I| ≤ Cg * (1/2) m^σ * ((2 log m + 1)/(1 - r) + 2 r/(1 - r)^2)`. -/
theorem kc1_centering_of_clause {κ : Vec d → Mat d} {m : ℕ} {σ : ℝ} (hm : 2 ≤ m)
    (hwin : ∀ A B : ℝ, 1 ≤ A → 1 ≤ B → ∀ n : ℕ, (m : ℤ) - ⌈A * Real.log (B * (m : ℝ))⌉ ≤ (n : ℤ) →
      n ≤ m → ∀ Q : TriadicCube d, Q.scale = (n : ℤ) →
        cubeCenter Q ∈ cubeSet (originCube d (m : ℤ)) →
          matrixOperatorNorm (volumeAverageMat (cubeSet Q) κ) ≤
            A * Real.log (B * (m : ℝ)) * (1 / 2 : ℝ) * (m : ℝ) ^ σ)
    (i j : Fin d) {I Cg r : ℝ} {W : ℕ → ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (hCg : 0 ≤ Cg)
    (hW : ∀ t, 0 ≤ W t ∧ W t ≤ Cg * r ^ t)
    (hPair : ∀ D : ℕ → ℝ,
      (∀ t : ℕ, t + 1 ≤ m → ∀ P ∈ descendantsAtDepth (originCube d (m : ℤ)) t,
        ∀ R ∈ childCubes P,
          |volumeAverage (cubeSet R) (fun y => κ y i j) -
              volumeAverage (cubeSet P) (fun y => κ y i j)| ≤ D t) →
      |I| ≤ ∑ t ∈ Finset.range m, D t * W t) :
    |I| ≤ Cg * ((1 / 2 : ℝ) * (m : ℝ) ^ σ) *
      ((2 * Real.log (m : ℝ) + 1) / (1 - r) + 2 * r / (1 - r) ^ 2) := by
  have hmR : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hL : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg (by linarith only [hmR])
  have hM : 0 ≤ (m : ℝ) ^ σ := Real.rpow_nonneg (by linarith only [hmR]) σ
  have h1 := hPair (fun t => (max (Real.log (m : ℝ)) (t : ℝ) +
      max (Real.log (m : ℝ)) ((t + 1 : ℕ) : ℝ)) * (1 / 2 : ℝ) * (m : ℝ) ^ σ)
    (fun t ht P hP R hR => kc1_child_parent_bound hm hwin ht hP hR i j)
  exact h1.trans (kc1_weighted_sum hL hr0 hr1 hCg (by positivity) hW)

/-- Absorbing the logarithm into a larger power. -/
theorem kc1_log_absorb {m : ℕ} (hm : 2 ≤ m) {σ ε : ℝ} (hε : 0 < ε) :
    (1 + Real.log (m : ℝ)) * (m : ℝ) ^ σ ≤ (1 + ε⁻¹) * (m : ℝ) ^ (σ + ε) := by
  have hmR : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < (m : ℝ) := by linarith only [hmR]
  have hlog := Real.log_le_rpow_div hm0.le hε
  have hone : (1 : ℝ) ≤ (m : ℝ) ^ ε := Real.one_le_rpow (by linarith only [hmR]) hε.le
  have hM : 0 ≤ (m : ℝ) ^ σ := Real.rpow_nonneg hm0.le σ
  have hadd : (m : ℝ) ^ (σ + ε) = (m : ℝ) ^ σ * (m : ℝ) ^ ε := Real.rpow_add hm0 _ _
  rw [hadd]
  have h2 : Real.log (m : ℝ) ≤ ε⁻¹ * (m : ℝ) ^ ε := by
    rw [inv_mul_eq_div]; exact hlog
  have : 1 + Real.log (m : ℝ) ≤ (1 + ε⁻¹) * (m : ℝ) ^ ε := by
    nlinarith only [h2, hone, inv_pos.2 hε]
  calc (1 + Real.log (m : ℝ)) * (m : ℝ) ^ σ ≤ ((1 + ε⁻¹) * (m : ℝ) ^ ε) * (m : ℝ) ^ σ :=
        mul_le_mul_of_nonneg_right this hM
    _ = _ := by ring

/-- The constant of the centring bound. -/
theorem kc1_const_le {L r : ℝ} (hL : 0 ≤ L) (hr1 : r < 1) :
    ((2 * L + 1) / (1 - r) + 2 * r / (1 - r) ^ 2) ≤
      2 * ((1 - r)⁻¹ + (1 - r)⁻¹ ^ 2) * (1 + L) := by
  have h0 : 0 < 1 - r := by linarith only [hr1]
  have e1 : (2 * L + 1) / (1 - r) = (2 * L + 1) * (1 - r)⁻¹ := div_eq_mul_inv _ _
  have e2 : 2 * r / (1 - r) ^ 2 = 2 * r * (1 - r)⁻¹ ^ 2 := by
    rw [div_eq_mul_inv, inv_pow]
  rw [e1, e2]
  have hi : 0 ≤ (1 - r)⁻¹ := inv_nonneg.2 h0.le
  have hi2 : 0 ≤ (1 - r)⁻¹ ^ 2 := sq_nonneg _
  nlinarith only [mul_nonneg hi hL, mul_nonneg hi2 hL, hi, hi2, mul_nonneg hi2 h0.le]

/-- **Centring, almost surely.** For `σ > 0` and `ε > 0` there is a constant `Cσ` and, for every
admissible law, a measurable random scale `K ≥ 27` with `log K = O_{Γ_{2σ}}(Cσ)` such that almost
surely, for every `m` with `K ≤ 3^m` and every entry `(i, j)` of the stream matrix `κ`: if `I`
is a pairing of the entry with a test function whose martingale increments have size
`W t ≤ Cg r^t` (`0 ≤ r < 1`), and `I` obeys the martingale pairing inequality `hPair`, then
`|I| ≤ Cg ((1 - r)⁻¹ + (1 - r)⁻² )(1 + ε⁻¹) m^{σ + ε}`. -/
theorem kc1_centering_ae (d : ℕ) (σ ε : ℝ) (hσ : 0 < σ) (hε : 0 < ε)
    (hV6 :
        ∃ C₂ : ℝ,
          ∀ s : ℝ, 0 < s → s < 1 →
            ∃ C₀ C₁ : ℝ,
              ∀ p : ℝ, 1 < p →
                ∃ C : ℝ,
                  ∀ P : MeasureTheory.ProbabilityMeasure
                      (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d),
                    SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P →
                    SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P →
                    SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P →
                    SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P →
                    SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P →
                    (∀ l m n : ℕ, n < m → m ≤ l →
                        (∃ X : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ,
                          Measurable X ∧
                            Homogenization.IndependentSums.IsBigO P.toMeasure
                              (Homogenization.IndependentSums.gammaSigma 2) X
                              (C * (3 : ℝ) ^ (s * (m : ℝ))) ∧
                            ∀ omega,
                              SuperdiffusionCLT.Section2.Norms.matHatNegENorm
                                  (Homogenization.originCube d (l : ℤ)) s
                                  (ENNReal.ofReal p)
                                  (fun x =>
                                    SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement
                                      omega n m x) ≤
                                ENNReal.ofReal (X omega)) ∧
                          (∃ X : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ,
                            Measurable X ∧
                              Homogenization.IndependentSums.IsBigO P.toMeasure
                                (Homogenization.IndependentSums.gammaSigma 2) X
                                (C * p ^ ((1 : ℝ) / 2) * ((m - n : ℕ) : ℝ) ^ ((1 : ℝ) / 2) *
                                  (3 : ℝ) ^ (-((d : ℝ) / (2 * p) * ((l - m : ℕ) : ℝ)))) ∧
                              ∀ omega,
                                SuperdiffusionCLT.Section2.Norms.cubeLpENorm
                                    (Homogenization.originCube d (l : ℤ))
                                    (ENNReal.ofReal p)
                                    (fun x =>
                                      SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement
                                        omega n m x) ≤
                                  ENNReal.ofReal
                                    (C * ((m - n : ℕ) : ℝ) ^ ((1 : ℝ) / 2) + X omega)) ∧
                          (∃ X : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ,
                            Measurable X ∧
                              Homogenization.IndependentSums.IsBigO P.toMeasure
                                (Homogenization.IndependentSums.gammaSigma 2) X
                                (C * ((m - n : ℕ) : ℝ) ^ ((1 : ℝ) / 2) *
                                  ((l - n : ℕ) : ℝ) ^ ((1 : ℝ) / 2)) ∧
                              ∀ omega,
                                SuperdiffusionCLT.Section2.Norms.cubeLpENorm
                                    (Homogenization.originCube d (l : ℤ)) ∞
                                    (fun x =>
                                      SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement
                                        omega n m x) ≤
                                  ENNReal.ofReal (X omega)) ∧
                          (∃ X : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ,
                            Measurable X ∧
                              Homogenization.IndependentSums.IsBigO P.toMeasure
                                (Homogenization.IndependentSums.gammaSigma 2) X
                                (C * (3 : ℝ) ^ (-(s * (n : ℝ)))) ∧
                              ∀ omega,
                                SuperdiffusionCLT.Section2.Norms.cubeHsENorm
                                    (Homogenization.originCube d (l : ℤ)) s
                                    (fun x =>
                                      SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement
                                        omega n m x) ≤
                                  ENNReal.ofReal (X omega))) ∧
                      (∀ l n : ℕ,
                          ∃ X : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ,
                            Measurable X ∧
                              Homogenization.IndependentSums.IsBigO P.toMeasure
                                (Homogenization.IndependentSums.gammaSigma 2) X
                                (C * (3 : ℝ) ^ (-(s * (n : ℝ)))) ∧
                              ∀ᵐ omega ∂P.toMeasure,
                                (⨆ M : {M : ℕ // n < M},
                                  SuperdiffusionCLT.Section2.Norms.cubeEuclideanGagliardoESeminorm
                                    (Homogenization.originCube d (l : ℤ)) s 2
                                    (fun x =>
                                      SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement
                                        omega n M.1 x)) ≤
                                  ENNReal.ofReal (X omega)) ∧
                      (∀ delta : ℝ, 0 < delta → delta < 1 →
                          ∀ sigma : ℝ, 0 < sigma →
                            ∃ Kfun : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ,
                              Measurable Kfun ∧
                                (∀ omega, (27 : ℝ) ≤ Kfun omega) ∧
                                Homogenization.IndependentSums.IsBigO P.toMeasure
                                  (Homogenization.IndependentSums.gammaSigma (2 * sigma))
                                  (fun omega => Real.log (Kfun omega))
                                  (C₀ *
                                    (C₁ * delta⁻¹ *
                                        Real.sqrt (sigma⁻¹ *
                                          Real.log (Real.exp 1 + C₂ * delta⁻¹ * sigma⁻¹))) ^
                                      sigma⁻¹) ∧
                                ∀ᵐ omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d
                                    ∂P.toMeasure,
                                  (∀ i : ℕ,
                                      Summable fun k : ℕ =>
                                        SuperdiffusionCLT.Section2.Carriers.shellDerivLinftyNorm
                                          (Homogenization.openCubeSet
                                            (Homogenization.originCube d (i : ℤ)))
                                          (omega k)) →
                                    ((∀ m : ℕ,
                                        Kfun omega ≤ (3 : ℝ) ^ m →
                                    (ENNReal.ofReal ((m : ℝ)⁻¹) *
                                          SuperdiffusionCLT.Section2.Norms.cubeLpENorm
                                            (Homogenization.originCube d (m : ℤ)) ∞
                                            (SuperdiffusionCLT.Section2.Carriers.centeredStreamField
                                              omega
                                              (Homogenization.cubeSet
                                                (Homogenization.originCube d (m : ℤ)))) +
                                        ENNReal.ofReal ((3 : ℝ) ^ m) *
                                          (∑' k : ℕ,
                                            ENNReal.ofReal
                                              (SuperdiffusionCLT.Section2.Carriers.shellDerivLinftyNorm
                                                (Homogenization.openCubeSet
                                                  (Homogenization.originCube d (m : ℤ)))
                                                (omega (m + 1 + k)))) +
                                        ENNReal.ofReal ((3 : ℝ) ^ (-(s * (m : ℝ)))) *
                                          SuperdiffusionCLT.Section2.Norms.matHatNegENorm
                                            (Homogenization.originCube d (m : ℤ)) s 2
                                            (SuperdiffusionCLT.Section2.Carriers.centeredStreamField
                                              omega
                                              (Homogenization.cubeSet
                                                (Homogenization.originCube d (m : ℤ)))) ≤
                                      ENNReal.ofReal (delta * (m : ℝ) ^ sigma)) ∧
                                      ∀ A B : ℝ, 1 ≤ A → 1 ≤ B →
                                        ∀ n : ℕ,
                                          (m : ℤ) - ⌈A * Real.log (B * (m : ℝ))⌉ ≤ (n : ℤ) →
                                            n ≤ m →
                                              ∀ Q : Homogenization.TriadicCube d,
                                                Q.scale = (n : ℤ) →
                                                  Homogenization.cubeCenter Q ∈
                                                      Homogenization.cubeSet
                                                        (Homogenization.originCube d (m : ℤ)) →
                                                    Homogenization.Book.Ch02.matrixOperatorNorm
                                                        (Homogenization.volumeAverageMat
                                                          (Homogenization.cubeSet Q)
                                                          (SuperdiffusionCLT.Section2.Carriers.centeredStreamField
                                                            omega
                                                            (Homogenization.cubeSet
                                                              (Homogenization.originCube d (m : ℤ))))) ≤
                                                      A * Real.log (B * (m : ℝ)) * delta *
                                                        (m : ℝ) ^ sigma) ∧
                                      ∀ x : Homogenization.Vec d,
                                  Homogenization.Book.Ch02.matrixOperatorNorm
                                        (SuperdiffusionCLT.Section2.Carriers.centeredStreamField
                                            omega
                                            (Homogenization.cubeSet
                                              (Homogenization.originCube d (0 : ℤ))) x -
                                          SuperdiffusionCLT.Section2.Carriers.centeredStreamField
                                            omega
                                            (Homogenization.cubeSet
                                              (Homogenization.originCube d (0 : ℤ))) 0) ^ 2 ≤
                                    C *
                                      Real.log (Kfun omega ^ 2 + Homogenization.vecNormSq x) ^
                                        (2 * (1 + sigma))))) :
    ∃ Cσ : ℝ,
      ∀ P : ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d),
        SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P →
        SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P →
        SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P →
        SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P →
        SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P →
          ∃ K : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ,
            Measurable K ∧ (∀ omega, (27 : ℝ) ≤ K omega) ∧
            Homogenization.IndependentSums.IsBigO P.toMeasure
              (Homogenization.IndependentSums.gammaSigma (2 * σ))
              (fun omega => Real.log (K omega)) Cσ ∧
            ∀ᵐ omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d ∂P.toMeasure,
              ∀ m : ℕ, K omega ≤ (3 : ℝ) ^ m → ∀ i j : Fin d, ∀ (I Cg r : ℝ) (W : ℕ → ℝ),
                0 ≤ r → r < 1 → 0 ≤ Cg → (∀ t, 0 ≤ W t ∧ W t ≤ Cg * r ^ t) →
                (∀ D : ℕ → ℝ,
                  (∀ t : ℕ, t + 1 ≤ m → ∀ P ∈ descendantsAtDepth (originCube d (m : ℤ)) t,
                    ∀ R ∈ childCubes P,
                      |volumeAverage (cubeSet R)
                            (fun y => SuperdiffusionCLT.Section2.Carriers.centeredStreamField
                              omega (cubeSet (originCube d (m : ℤ))) y i j) -
                          volumeAverage (cubeSet P)
                            (fun y => SuperdiffusionCLT.Section2.Carriers.centeredStreamField
                              omega (cubeSet (originCube d (m : ℤ))) y i j)| ≤ D t) →
                  |I| ≤ ∑ t ∈ Finset.range m, D t * W t) →
                |I| ≤ Cg * ((1 - r)⁻¹ + (1 - r)⁻¹ ^ 2) * (1 + ε⁻¹) * (m : ℝ) ^ (σ + ε) := by
  obtain ⟨Cσ, hCσ⟩ := kc1_window_ae d σ hσ hV6
  refine ⟨Cσ, fun P hPre hJ1 hJ2 hJ3 hJ4 => ?_⟩
  obtain ⟨K, hKm, hK27, hKO, hKae⟩ := hCσ P hPre hJ1 hJ2 hJ3 hJ4
  refine ⟨K, hKm, hK27, hKO, ?_⟩
  filter_upwards [hKae] with omega hω m hm i j I Cg r W hr0 hr1 hCg hW hPair
  have hm3 : 2 ≤ m := by
    by_contra hlt
    have hle : m ≤ 1 := by omega
    have h3 : (3 : ℝ) ^ m ≤ 3 ^ 1 := pow_le_pow_right₀ (by norm_num) hle
    linarith only [hK27 omega, hm, h3]
  have hmR : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm3
  have hL : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg (by linarith only [hmR])
  have h1 := kc1_centering_of_clause hm3 (hω m hm) i j hr0 hr1 hCg hW hPair
  have h2 := kc1_const_le hL hr1
  have h3 := kc1_log_absorb hm3 (σ := σ) hε
  have hM : 0 ≤ (m : ℝ) ^ σ := Real.rpow_nonneg (by linarith only [hmR]) σ
  have hrr : 0 ≤ (1 - r)⁻¹ + (1 - r)⁻¹ ^ 2 :=
    add_nonneg (inv_nonneg.2 (by linarith only [hr1])) (sq_nonneg _)
  calc |I| ≤ Cg * ((1 / 2 : ℝ) * (m : ℝ) ^ σ) *
        ((2 * Real.log (m : ℝ) + 1) / (1 - r) + 2 * r / (1 - r) ^ 2) := h1
    _ ≤ Cg * ((1 / 2 : ℝ) * (m : ℝ) ^ σ) *
        (2 * ((1 - r)⁻¹ + (1 - r)⁻¹ ^ 2) * (1 + Real.log (m : ℝ))) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = Cg * ((1 - r)⁻¹ + (1 - r)⁻¹ ^ 2) * ((1 + Real.log (m : ℝ)) * (m : ℝ) ^ σ) := by ring
    _ ≤ Cg * ((1 - r)⁻¹ + (1 - r)⁻¹ ^ 2) * ((1 + ε⁻¹) * (m : ℝ) ^ (σ + ε)) :=
        mul_le_mul_of_nonneg_left h3 (mul_nonneg hCg hrr)
    _ = _ := by ring

/-- Satisfiability: the statement supplies `hV6`, and the data `I = 0`, `W = 0`, `Cg = 0`,
`r = 0` meet the pairing hypothesis, so the hypotheses of `kc1_centering_ae` hold together. -/
example (d : ℕ) :
    ∃ Cσ : ℝ,
      ∀ P : ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d),
        SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P →
        SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P →
        SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P →
        SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P →
        SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P →
          ∃ K : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ,
            Measurable K ∧ (∀ omega, (27 : ℝ) ≤ K omega) ∧
            Homogenization.IndependentSums.IsBigO P.toMeasure
              (Homogenization.IndependentSums.gammaSigma (2 * 1))
              (fun omega => Real.log (K omega)) Cσ ∧
            ∀ᵐ omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d ∂P.toMeasure,
              ∀ m : ℕ, K omega ≤ (3 : ℝ) ^ m → ∀ _ _ : Fin d,
                |(0 : ℝ)| ≤ (0 : ℝ) * ((1 - (0 : ℝ))⁻¹ + (1 - (0 : ℝ))⁻¹ ^ 2) * (1 + (1 : ℝ)⁻¹) *
                  (m : ℝ) ^ ((1 : ℝ) + 1) := by
  obtain ⟨Cσ, hC⟩ := kc1_centering_ae d 1 1 one_pos one_pos
    (SuperdiffusionCLT.Frozen.Section2.streamIncrement_scale_estimates d)
  refine ⟨Cσ, fun P h0 h1 h2 h3 h4 => ?_⟩
  obtain ⟨K, hK, h27, hO, hae⟩ := hC P h0 h1 h2 h3 h4
  refine ⟨K, hK, h27, hO, ?_⟩
  filter_upwards [hae] with omega hω m hm i j
  exact hω m hm i j 0 0 0 (fun _ => 0) le_rfl one_pos le_rfl (fun t => ⟨le_rfl, by simp⟩)
    (fun D _ => by simp)

end SuperdiffusionCLT.Section7

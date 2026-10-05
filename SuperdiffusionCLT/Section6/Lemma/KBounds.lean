/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Frozen.Section2.StreamIncrementScaleEstimates
public import SuperdiffusionCLT.Section2.Cutoff.DerivativeSummabilityAllScales

@[expose] public section

open scoped ENNReal
open scoped Matrix.Norms.L2Operator

/-!
# `k.bounds` for the sharp scale inputs

The `Kfun` conjunct of `Frozen.Section2.streamIncrement_scale_estimates` at
`s = 1/4`, `δ = 1/2`, `σ = ρ`, `p = 2`, with the middle (derivative tail) term dropped and the
summability guard discharged almost surely from the law assumption J3.
-/

namespace SuperdiffusionCLT.Section6

open MeasureTheory

/-- **`k.bounds` of `l.sharp.scale.inputs`.** For each `d` and `ρ > 0` there is a constant `Cρ`,
independent of the law, such that for every admissible law there is a measurable random scale
`K ≥ 27` with `log K = O_{Γ_{2ρ}}(Cρ)`, almost surely on the event `K ≤ 3^m` the bound
`m⁻¹ ‖k - (k)_{cu_m}‖_{L^∞(cu_m)} + 3^{-m/4} [k - (k)_{cu_m}]_{Ĥ^{-1/4}(cu_m)} ≤ m^ρ` holds. -/
theorem kBounds_exists (d : ℕ) (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ Cρ : ℝ,
      ∀ P : ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d),
        SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P →
        SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P →
        SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P →
        SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P →
        SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P →
          ∃ K : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ,
            Measurable K ∧ (∀ omega, (27 : ℝ) ≤ K omega) ∧
            Homogenization.IndependentSums.IsBigO P.toMeasure
              (Homogenization.IndependentSums.gammaSigma (2 * ρ))
              (fun omega => Real.log (K omega)) Cρ ∧
            ∀ᵐ omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d ∂P.toMeasure,
              ∀ m : ℕ, K omega ≤ (3 : ℝ) ^ m →
                ENNReal.ofReal ((m : ℝ)⁻¹) *
                    SuperdiffusionCLT.Section2.Norms.cubeLpENorm
                      (Homogenization.originCube d (m : ℤ)) ∞
                      (SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega
                        (Homogenization.cubeSet (Homogenization.originCube d (m : ℤ)))) +
                  ENNReal.ofReal ((3 : ℝ) ^ (-((1 / 4 : ℝ) * (m : ℝ)))) *
                    SuperdiffusionCLT.Section2.Norms.matHatNegENorm
                      (Homogenization.originCube d (m : ℤ)) (1 / 4) 2
                      (SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega
                        (Homogenization.cubeSet (Homogenization.originCube d (m : ℤ)))) ≤
                  ENNReal.ofReal ((m : ℝ) ^ ρ) := by
  obtain ⟨C₂, hC₂⟩ :=
    SuperdiffusionCLT.Frozen.Section2.streamIncrement_scale_estimates d
  obtain ⟨C₀, C₁, hC₁⟩ := hC₂ (1 / 4) (by norm_num) (by norm_num)
  obtain ⟨C, hC⟩ := hC₁ 2 (by norm_num)
  refine ⟨C₀ * (C₁ * ((1 / 2 : ℝ))⁻¹ *
      Real.sqrt (ρ⁻¹ * Real.log (Real.exp 1 + C₂ * ((1 / 2 : ℝ))⁻¹ * ρ⁻¹))) ^ ρ⁻¹,
    fun P hPre hJ1 hJ2 hJ3 hJ4 => ?_⟩
  obtain ⟨-, -, hK⟩ := hC P hPre hJ1 hJ2 hJ3 hJ4
  obtain ⟨K, hKm, hK27, hKO, hKae⟩ := hK (1 / 2) (by norm_num) (by norm_num) ρ hρ
  refine ⟨K, hKm, hK27, hKO, ?_⟩
  have hsum :=
    SuperdiffusionCLT.Section2.Cutoff.ae_forall_summable_shellDerivLinftyNorm_originCube
      (P := P) hJ3
  filter_upwards [hKae, hsum] with omega h1 h2 m hm
  have h := (h1 h2).1 m hm |>.1
  refine le_trans ?_ (h.trans (ENNReal.ofReal_le_ofReal ?_))
  · gcongr
    exact le_self_add
  · have : (0 : ℝ) ≤ (m : ℝ) ^ ρ := Real.rpow_nonneg (Nat.cast_nonneg m) ρ
    linarith only [this]

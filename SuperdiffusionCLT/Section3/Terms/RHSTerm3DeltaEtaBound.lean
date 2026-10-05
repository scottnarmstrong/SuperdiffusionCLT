/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Setup.Parameters
public import SuperdiffusionCLT.Section3.Setup.ScaleAssembly

/-!
# `δ + η_L ≤ 1` from the printed conditions, at the carriers `δ = c₀c⋆²` and `η_L`

The numeric premise `δ + η_L ≤ 1` is what
`w_average_difference` asks for (where it is used
only as `(δ + η_L)^{1/2} ≤ 1`), and it is a binder `_hde1` of
the constant-first term-3 assembly and a conjunct
of the root's term-level residue, in the `S.L`/`S.a` form.
The paper never states it as an
assumption; it is **a consequence of the printed conditions**, and this file
records the derivation at our carriers.

## The printed conditions, quoted

* The *relative smallness* (inside the proof of `p.sstar.lower.bound`):
  ```
  C\delta^{\nf12}\leq \frac14\cstar\,,
  ```
* The localization defect:
  ```
  \eta_L\leq L^{-1000}\,.
  ```
* The statement of `p.sstar.lower.bound`: "There exist `C(d)\in[1,\infty)`
  and `c(d)\in(0,\nicefrac12]`" — in particular `C(d) ≥ 1`.
* The display `e.cstar.bound` of assumption `a.j.nondeg`:
  ```
  \E\bigl[|\mathbf j_l(0)e|^2\bigr] \leq 1+e^{-1} \quad \implies \quad \cstar \leq 2
  ```
* The display `e.L.vs.nu`: `L ≥ m ≥ ½L` and `m` above a threshold that the
  proof reads at `L`; the scale hypothesis used below is `L ≥ 2`, which for
  `L ∈ ℕ` is `L ≠ 1`.

## The derivation chain

With `δ = smallnessParameter c₀ c⋆ = c₀c⋆²` and `C ≥ 1`, `√δ ≥ 0`:

```
√δ = 1·√δ ≤ C·√δ ≤ ¼c⋆ ≤ ¼·2 = ½   [relative smallness, C ≥ 1, c⋆ ≤ 2]
δ = (√δ)² ≤ (½)² = ¼ ≤ ½            [c⋆ ≤ 2 as above]
η_L ≤ L^{-1000} ≤ 2^{-1000} ≤ ½     [defect bound, L ≥ 2]
δ + η_L ≤ ¼ + ½ = ¾ ≤ 1.
```

The chain is proved below in two layers, so that each hypothesis is traceable
to one quoted display:

* `smallnessParameter_le_quarter` — `δ ≤ ¼` from the *factored* form of
  the relative smallness, `CM * √c₀ ≤ ⅛`, which is how the root of
  `p.sstar.lower.bound` carries it, together with `1 ≤ CM` and `c⋆ ≤ 2`;
* `localizationEta_le_half` — `η_L ≤ ½` from `localizationEta_le` and `L ≥ 2`;
* `deltaEtaL_le_one` — the combined statement.

## Which printed conditions the term-3 chain already carries

The constant-first term-3 assembly carries
`0 < ν`, `ν ≤ 1`, `1 ≤ L`, `0 ≤ log(ν⁻¹L)`, `4Ceta ≤ ν⁻¹L`
(`_hCeta`/`_hCT`), `8056 ≤ K log 3` (`_hKlog3`), `S.a = scaleOffset K ν L`
(`_hSa`, giving `K log(ν⁻¹L) ≤ S.a`), and `delta ≤ 1`.  It does
**not** carry the relative smallness (its `delta` is an abstract real,
bounded only by `1`), it does **not** carry `c⋆ ≤ 2`, and it carries `1 ≤ L`
rather than `L ≥ 2`.  At the root of `p.sstar.lower.bound`, by
contrast, the relative smallness is carried as `CM * Real.sqrt c0 ≤ 1 / 8`,
the bound `C(d) ≥ 1` as `1 ≤ CM`,
and `L ≥ 2` follows from the carried depth shape `CM L^{-500} ≤ c⋆/8`.

The remaining printed condition is `c⋆ ≤ 2` (display `e.cstar.bound`).  It follows from
assumption (J5) by `ShellLawJ5.cStar_le_two`; here it is a hypothesis of
`deltaEtaL_le_one`, and the final assembly of Section 3 discharges it through
`cStarLeTwo_of_shellLawJ5`.  Every other hypothesis of `deltaEtaL_le_one` is already a
binder or an available bridge.

The hypothesis `L ≥ 2` follows from the root's carried depth
shape `CM L^{-500} ≤ c⋆/8` together with `1 ≤ CM` and `c⋆ ≤ 2`, so at the root
the only printed condition still needed from outside the binder list is
`c⋆ ≤ 2`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Terms

open SuperdiffusionCLT.Section3.Setup

noncomputable section

/-! ## `δ = smallnessParameter c₀ c⋆` below `¼` -/

/-- **`δ ≤ ¼` from the factored relative smallness `CM √c₀ ≤ ⅛`**, the shape in
which the root of `p.sstar.lower.bound` carries the relative smallness,
together with `1 ≤ CM` and `c⋆ ≤ 2`.

`√c₀ ≤ CM√c₀ ≤ ⅛`, so `√δ = √c₀·c⋆ ≤ ⅛·2 = ¼` and `δ ≤ 1/16 ≤ ¼`.  The
factored hypothesis is the relative smallness `CM √c₀ ≤ ¼`
strengthened from `¼` to `⅛`. -/
theorem smallnessParameter_le_quarter
    {CM c0 cStar : ℝ} (hCM : 1 ≤ CM) (hc0small : CM * Real.sqrt c0 ≤ 1 / 8)
    (hc0 : 0 ≤ c0) (hcStar0 : 0 ≤ cStar) (hcStar2 : cStar ≤ 2) :
    smallnessParameter c0 cStar ≤ 1 / 4 := by
  have hs0 : (0 : ℝ) ≤ Real.sqrt c0 := Real.sqrt_nonneg _
  have hsqrt : Real.sqrt c0 ≤ 1 / 8 := by
    calc Real.sqrt c0 = 1 * Real.sqrt c0 := (one_mul _).symm
      _ ≤ CM * Real.sqrt c0 := mul_le_mul_of_nonneg_right hCM hs0
      _ ≤ 1 / 8 := hc0small
  have hsq : Real.sqrt (smallnessParameter c0 cStar) = Real.sqrt c0 * cStar :=
    sqrt_smallnessParameter hc0 hcStar0
  have hs : Real.sqrt (smallnessParameter c0 cStar) ≤ 1 / 4 := by
    rw [hsq]
    calc Real.sqrt c0 * cStar ≤ (1 / 8) * cStar :=
          mul_le_mul_of_nonneg_right hsqrt hcStar0
      _ ≤ (1 / 8) * 2 := mul_le_mul_of_nonneg_left hcStar2 (by norm_num)
      _ = 1 / 4 := by norm_num
  have hδ0 : (0 : ℝ) ≤ smallnessParameter c0 cStar := smallnessParameter_nonneg hc0
  calc smallnessParameter c0 cStar
      = Real.sqrt (smallnessParameter c0 cStar) ^ (2 : ℕ) := (Real.sq_sqrt hδ0).symm
    _ ≤ (1 / 4) ^ (2 : ℕ) := pow_le_pow_left₀ (Real.sqrt_nonneg _) hs 2
    _ = 1 / 16 := by norm_num
    _ ≤ 1 / 4 := by norm_num

/-! ## `η_L` below `½` -/

/-- **`η_L ≤ ½`** from the printed defect bound `η_L ≤ L^{-1000}` and
the scale hypothesis `L ≥ 2`, in the form `localizationEta_le`.

Since `L ≥ 2`, `L^{-1000} ≤ 2^{-1000} ≤ 2^{-1} = ½`.  The hypothesis
`L ≥ 2` is recorded as its own input because it is exactly what
the root's depth shape supplies. -/
theorem localizationEta_le_half {Ceta K nu : ℝ} {L a : ℕ}
    (hnu : 0 < nu) (hnu1 : nu ≤ 1) (hL : 2 ≤ L) (hCeta : 0 ≤ Ceta)
    (hCT : Ceta ≤ nu⁻¹ * (L : ℝ)) (hKlog3 : 8056 ≤ K * Real.log 3)
    (ha : K * Real.log (nu⁻¹ * (L : ℝ)) ≤ (a : ℝ)) :
    localizationEta Ceta nu L (2 * a) ≤ 1 / 2 := by
  have hL1 : 1 ≤ L := by omega
  have heta : localizationEta Ceta nu L (2 * a) ≤ (L : ℝ) ^ (-(1000 : ℝ)) :=
    localizationEta_le hnu hnu1 hL1 hCeta hCT hKlog3 ha
  have hL0 : (0 : ℝ) < (L : ℝ) := Nat.cast_pos.2 (by omega)
  have hLnn : (0 : ℝ) ≤ (L : ℝ) := hL0.le
  have h2L : (2 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
  have hpow : (L : ℝ) ^ (-(1000 : ℝ)) ≤ (2 : ℝ) ^ (-(1000 : ℝ)) := by
    rw [Real.rpow_neg hLnn, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
    exact (inv_le_inv₀ (Real.rpow_pos_of_pos hL0 (1000 : ℝ))
      (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) (1000 : ℝ))).2
      (Real.rpow_le_rpow (by norm_num) h2L (by norm_num : (0 : ℝ) ≤ 1000))
  have hhalf : (2 : ℝ) ^ (-(1000 : ℝ)) ≤ 1 / 2 := by
    have hle : (-(1000 : ℝ)) ≤ (-(1 : ℝ)) := by norm_num
    have h := (Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).mpr hle
    have h1 : (2 : ℝ) ^ (-(1 : ℝ)) = 1 / 2 := by
      rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_one]
      norm_num
    rwa [h1] at h
  exact le_trans heta (le_trans hpow hhalf)

/-! ## The combined bound, at the carriers -/

/-- **`δ + η_L ≤ 1`, from the factored relative smallness `CM √c₀ ≤ ⅛`** — the
form in which the root of `p.sstar.lower.bound` carries the relative smallness.
Here `RelativeSmallness CM c⋆ δ` is replaced by the stronger `CM √c₀ ≤ ⅛` and the
carrier `δ = c₀c⋆²` is substituted. -/
theorem deltaEtaL_le_one
    {CM c0 cStar Ceta K nu : ℝ} {L a : ℕ}
    (hCM : 1 ≤ CM) (hc0small : CM * Real.sqrt c0 ≤ 1 / 8)
    (hc0 : 0 ≤ c0) (hcStar0 : 0 ≤ cStar) (hcStar2 : cStar ≤ 2)
    (hnu : 0 < nu) (hnu1 : nu ≤ 1) (hL : 2 ≤ L)
    (hCeta : 0 ≤ Ceta) (hCT4 : 4 * Ceta ≤ nu⁻¹ * (L : ℝ))
    (hKlog3 : 8056 ≤ K * Real.log 3)
    (ha : K * Real.log (nu⁻¹ * (L : ℝ)) ≤ (a : ℝ)) :
    smallnessParameter c0 cStar + localizationEta Ceta nu L (2 * a) ≤ 1 := by
  have hδ : smallnessParameter c0 cStar ≤ 1 / 2 :=
    le_trans (smallnessParameter_le_quarter hCM hc0small hc0 hcStar0 hcStar2)
      (by norm_num)
  have hη : localizationEta Ceta nu L (2 * a) ≤ 1 / 2 :=
    localizationEta_le_half hnu hnu1 hL hCeta (by linarith only [hCT4, hCeta]) hKlog3 ha
  linarith only [hδ, hη]

/-! ## Discharging `L ≥ 2` from the root's carried depth shape -/

/-! ## Witnesses -/

end

end SuperdiffusionCLT.Section3.Terms

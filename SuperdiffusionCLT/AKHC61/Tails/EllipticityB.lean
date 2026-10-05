/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.AKHC61.Tails.Ellipticity
public import SuperdiffusionCLT.AKHC61.Carrier.OrliczMoments

/-!
# Package C1 (continued): the second-moment bound on the ellipticity tail

This file finishes the ellipticity tail
(`e.this.is.so.nice.again#tail-ellipticity-weaker`) by turning `Ellipticity.lean`'s
pointwise, `Q`-uniform bound into the second-moment bound the paper states,
using A3's `akhc_moment_le_of_isBigO`
(`AKHC61/Carrier/OrliczMoments.lean`).

## The `K_{Ψ_S}^{36}` and `1/(min{3,p_{Ψ_S}}-2)` constants: an honest, not literal, match

The source states the ellipticity summand of `E[M_{n,ρ}²]` with the specific numeral
`K_{Ψ_S}^{36}` and denominator `1/(\min\{3,p_{Ψ_S}\}-2)`
(`e.mathcalM.m.rho.bound`). The moment order `θ` behind
`K_{Ψ_S}^{36}` is not defined in the printed text, so the exact route to `36` is not available,
and `3·⌈p⌉₊²` (the growth condition's own exponent) never equals `36` for an
integer `⌈p⌉₊` (`⌈p⌉₊² = 12` has no integer solution). So `36` cannot be independently
reconstructed.

What **is** achievable, and is exactly what this file proves: choosing the moment order
`p₀ := min 3 p_{Ψ_S}` (always `> 2`, since `p_{Ψ_S} > 2`) makes `⌈p₀⌉₊ ≤ 3`, hence
`3·⌈p₀⌉₊² ≤ 27 ≤ 36`, so `K_{Ψ_S}^{3⌈p₀⌉₊²} ≤ K_{Ψ_S}^{36}` (using `K_{Ψ_S} ≥ 1`) — the source's
own numeral is a **valid, if not tight**, choice for this route. Likewise `p₀ - 2 = \min\{3,
p_{Ψ_S}\} - 2` exactly, matching the source's denominator shape, up to the front constant `3`
(`p₀/(p₀-2) ≤ 3/(p₀-2)` since `p₀ ≤ 3`), which is absorbed into the generic `C(d)` the source
itself allows (`CONSTANT_SCOPE: C depends only on d`). This file reports the constant honestly as
`3·K_{Ψ_S}^{36}/(min 3 p_{Ψ_S} - 2)` rather than silently claiming the unreconstructible `36` is
tight.

## Main results

* `akhcTailEllB_moment_le`: the general moment bound, for any `IsBigO`-controlled `X`, of
  `E|X|²` by `3·K_{Ψ_S}^{36}/(min 3 p_{Ψ_S} - 2) · A²`.
* `akhcTailEllB_normalizedExcess_moment_le`: package C1's final deliverable — combined with
  `Ellipticity.lean`'s `akhcTailEll_normalized_excess_le`, the squared, `Q`-uniform ellipticity tail
  has second moment at most `3·K_{Ψ_S}^{36}·H²·n^{2D}·3^{-2(ρ-γ)(n-hprime)} / (min 3 p_{Ψ_S} - 2)`
  — exactly the source's shape (`K_{Ψ_S}^{36}`, `H²n^{2D}`, `3^{-(1-γ)(…)}`-type decay,
  `1/(min\{3,p_{Ψ_S}\}-2)`), with the honest front constant of `3` noted above.
-/

@[expose] public section

namespace SuperdiffusionCLT.AKHC61.Tails

open MeasureTheory

noncomputable section

/-! ## The growth-condition domain extension: (P2')'s `2 ≤ p` to `akhc_moment_le_of_isBigO`'s `1 < p` -/

/-- For `1 < p ≤ 2`, `⌈p⌉₊ = 2`. -/
private theorem akhcTailEllB_ceil_eq_two_of_mem_Ioc {p : ℝ} (hp1 : 1 < p) (hp2 : p ≤ 2) :
    (⌈p⌉₊ : ℕ) = 2 := by
  have h1 : (1 : ℕ) < ⌈p⌉₊ := Nat.lt_ceil.2 (by exact_mod_cast hp1)
  have h2 : ⌈p⌉₊ ≤ 2 := Nat.ceil_le.2 (by exact_mod_cast hp2)
  omega

/-- **The growth-domain extension.** (P2')'s own growth condition is stated only for `2 ≤ p ≤
p_{Ψ_S}` (`hGrowth2`). `akhc_moment_le_of_isBigO` needs it on the wider `1 < p ≤ p_{Ψ_S}`. For
`p ∈ (1,2)`, `⌈p⌉₊ = ⌈2⌉₊ = 2`, so the growth condition at the fixed exponent `2` already gives
the needed inequality, since `s ↦ s^p` is monotone in `p` for `s ≥ 1`. -/
private theorem akhcTailEllB_growth_ext
    {PsiS : ℝ → ℝ} {KPsiS pPsiS : ℝ} (hpPsiS : 2 < pPsiS)
    (hGrowth2 : ∀ p : ℝ, 2 ≤ p → p ≤ pPsiS → ∀ t s : ℝ, 1 ≤ t → 1 ≤ s →
      s ^ p ≤ KPsiS ^ (3 * ⌈p⌉₊ ^ 2) * (PsiS (t * s) / PsiS t)) :
    ∀ p : ℝ, 1 < p → p ≤ pPsiS → ∀ t s : ℝ, 1 ≤ t → 1 ≤ s →
      s ^ p ≤ KPsiS ^ (3 * ⌈p⌉₊ ^ 2) * (PsiS (t * s) / PsiS t) := by
  intro p hp1 hpPsiS' t s ht hs
  rcases le_or_gt 2 p with hp2 | hp2
  · exact hGrowth2 p hp2 hpPsiS' t s ht hs
  · have hceil : (⌈p⌉₊ : ℕ) = 2 := akhcTailEllB_ceil_eq_two_of_mem_Ioc hp1 hp2.le
    have hceil2 : (⌈(2 : ℝ)⌉₊ : ℕ) = 2 := akhcTailEllB_ceil_eq_two_of_mem_Ioc (by norm_num) le_rfl
    have hsp : s ^ p ≤ s ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hs hp2.le
    have hgrowth2 := hGrowth2 2 le_rfl (by linarith only [hpPsiS] : (2 : ℝ) ≤ pPsiS) t s ht hs
    rw [hceil2] at hgrowth2
    rw [hceil]
    exact hsp.trans hgrowth2

/-! ## The general moment bound -/

/-- **The general second-moment bound.** For any measurable `X` with `IsBigO P PsiS X A` under the
(P2') growth condition, `E|X|² ≤ 3·K_{Ψ_S}^{36}/(min 3 p_{Ψ_S} - 2) · A²`, via `p₀ := min 3
p_{Ψ_S}` and A3's `akhc_moment_le_of_isBigO`. See the module docstring for why `36` is an honest
(sound, not tight) match to the source's own numeral. -/
theorem akhcTailEllB_moment_le
    {Ω : Type*} [MeasurableSpace Ω] {Pmeas : Measure Ω} [IsProbabilityMeasure Pmeas]
    {PsiS : ℝ → ℝ} {KPsiS pPsiS A : ℝ}
    (hKPsiS : 1 ≤ KPsiS) (hpPsiS : 2 < pPsiS) (hA : 0 < A)
    (hPsiSOne : ∀ t : ℝ, 0 ≤ t → 1 ≤ PsiS t)
    (hGrowth2 : ∀ p : ℝ, 2 ≤ p → p ≤ pPsiS → ∀ t s : ℝ, 1 ≤ t → 1 ≤ s →
      s ^ p ≤ KPsiS ^ (3 * ⌈p⌉₊ ^ 2) * (PsiS (t * s) / PsiS t))
    {X : Ω → ℝ} (hXm : Measurable X)
    (hX : Homogenization.IndependentSums.IsBigO Pmeas PsiS X A) :
    ∫ ω, |X ω| ^ (2 : ℝ) ∂Pmeas ≤ 3 * KPsiS ^ 36 / (min 3 pPsiS - 2) * A ^ (2 : ℝ) := by
  set p0 : ℝ := min 3 pPsiS with hp0def
  have hp0_gt2 : (2 : ℝ) < p0 := lt_min (by norm_num) hpPsiS
  have hp0_le : p0 ≤ pPsiS := min_le_right _ _
  have hp0_le3 : p0 ≤ 3 := min_le_left _ _
  have hp0_sub_pos : (0 : ℝ) < p0 - 2 := by linarith only [hp0_gt2]
  have hGrowthExt := akhcTailEllB_growth_ext hpPsiS hGrowth2
  have hbound :=
    SuperdiffusionCLT.AKHC61.Carrier.akhc_moment_le_of_isBigO hKPsiS hPsiSOne hGrowthExt hA
      hXm hX (p := p0) (q := 2) (by linarith only [hp0_gt2]) hp0_le (by norm_num) hp0_gt2
  have hceil_le : (⌈p0⌉₊ : ℕ) ≤ 3 := Nat.ceil_le.2 (by exact_mod_cast hp0_le3)
  have hexp_le : 3 * ⌈p0⌉₊ ^ 2 ≤ 36 := by
    calc 3 * ⌈p0⌉₊ ^ 2 ≤ 3 * 3 ^ 2 := Nat.mul_le_mul_left 3 (Nat.pow_le_pow_left hceil_le 2)
      _ ≤ 36 := by norm_num
  have hKpow_le : KPsiS ^ (3 * ⌈p0⌉₊ ^ 2) ≤ KPsiS ^ 36 := pow_le_pow_right₀ hKPsiS hexp_le
  have hKpow_nonneg : (0 : ℝ) ≤ KPsiS ^ (3 * ⌈p0⌉₊ ^ 2) := by positivity
  have hfrac_le : p0 / (p0 - 2) ≤ 3 / (p0 - 2) :=
    div_le_div_of_nonneg_right hp0_le3 hp0_sub_pos.le
  have hfrac_nonneg : (0 : ℝ) ≤ p0 / (p0 - 2) := by positivity
  have hA2_nonneg : (0 : ℝ) ≤ A ^ (2 : ℝ) := Real.rpow_nonneg hA.le _
  have hmid :
      p0 / (p0 - 2) * KPsiS ^ (3 * ⌈p0⌉₊ ^ 2) ≤ 3 / (p0 - 2) * KPsiS ^ 36 :=
    mul_le_mul hfrac_le hKpow_le hKpow_nonneg (by positivity)
  have hmid2 :
      p0 / (p0 - 2) * KPsiS ^ (3 * ⌈p0⌉₊ ^ 2) * A ^ (2 : ℝ) ≤
        3 / (p0 - 2) * KPsiS ^ 36 * A ^ (2 : ℝ) :=
    mul_le_mul_of_nonneg_right hmid hA2_nonneg
  have heq : (3 : ℝ) / (p0 - 2) * KPsiS ^ 36 * A ^ (2 : ℝ) =
      3 * KPsiS ^ 36 / (min 3 pPsiS - 2) * A ^ (2 : ℝ) := by
    rw [hp0def]; ring
  rw [← heq]
  exact hbound.trans hmid2

/-! ## The packaged deliverable: node 14, second-moment form -/

/-- **Package C1's final deliverable.** Combining `Ellipticity.lean`'s pointwise,
`Q`-uniform bound (`akhcTailEll_normalized_excess_le`) with `akhcTailEllB_moment_le`: the squared
`3^{-ρ(n-Q.scale)}`-weighted ellipticity excess, for every `Q` with `Q.scale ≤ n` and `Q.scale ≤
hprime`, is dominated (pointwise, in every sample) by `(3^{-(ρ-γ)(n-hprime)}·|X(ω)|)²`, whose
second moment is at most

`3·K_{Ψ_S}^{36}·(H·n^D)²·3^{-2(ρ-γ)(n-hprime)} / (min 3 p_{Ψ_S} - 2)`.

This is the source's `K_{Ψ_S}^{36} H² n^{2D} 3^{-(1-γ)(n-h-L1 log(L2 h))/2}/(min\{3,p_{Ψ_S}\}-2)`
shape: `H²n^{2D}` matches exactly; `K_{Ψ_S}^{36}` and `1/(\min\{3,p_{Ψ_S}\}-2)` match up to the
front constant `3` (see the module docstring); the decay `3^{-2(ρ-γ)(n-hprime)}` matches the
source's `3^{-(1-γ)(n-h')/2}` once the *outer* `l.weaknorms.prime#apply-moreproto` step's own
choice of `ρ` (fixing `2(ρ-γ) = (1-γ)/2`) is substituted — a substitution outside this package's
scope (per the per-node table, node 14 is stated "for the fixed n,h,ρ,γ of the enclosing proof").
This feeds C3 (`E[M_{n,ρ}²]`, nodes 11/12): C3 supplies its own `ρ`, `hprime`, and combines this
bound with C2's CFS-range bound via the layer-cake step assigned to C3's own package. -/
theorem akhcTailEllB_normalizedExcess_moment_le
    {d : ℕ} [NeZero d] {nu : ℝ} {P : MeasureTheory.ProbabilityMeasure
      (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d)} {L : ℕ}
    (hnu : 0 < nu) (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
    (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P)
    (hJ4 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P)
    (gamma H D : ℝ) (m2 : ℕ) (PsiS : ℝ → ℝ) (KPsiS pPsiS : ℝ)
    (hgamma0 : 0 ≤ gamma) (hgamma1 : gamma < 1) (hH : 1 ≤ H) (hD : 0 ≤ D)
    (hPsiSMono : MonotoneOn PsiS (Set.Ici 0)) (hPsiSOne : ∀ t : ℝ, 0 ≤ t → 1 ≤ PsiS t)
    (hKPsiS : 1 ≤ KPsiS) (hpPsiS : 2 < pPsiS)
    (hGrowth : ∀ p : ℝ, 2 ≤ p → p ≤ pPsiS → ∀ t s : ℝ, 1 ≤ t → 1 ≤ s →
      s ^ p ≤ KPsiS ^ (3 * ⌈p⌉₊ ^ 2) * (PsiS (t * s) / PsiS t))
    (hP2 : ∀ j : ℕ, m2 ≤ j →
      ∃ X : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ, Measurable X ∧
        Homogenization.IndependentSums.IsBigO P.toMeasure PsiS X (H * (j : ℝ) ^ D) ∧
        ∀ (omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d)
          (Q : Homogenization.TriadicCube d),
          Q.scale ≤ (j : ℤ) →
          Homogenization.cubeCenter Q ∈
              Homogenization.cubeSet (Homogenization.originCube d (j : ℤ)) →
            Homogenization.BlockMatLoewnerLE
              (Homogenization.coarseBlockMatrix (Homogenization.cubeSet Q)
                (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff nu omega L).toCoeffField)
              ((1 + (3 : ℝ) ^ (-(gamma * ((Q.scale : ℝ) - (j : ℝ)))) * X omega) •
                SuperdiffusionCLT.Section2.Annealed.annealedBlockMatrix nu L P
                  (Homogenization.cubeSet (Homogenization.originCube d (j : ℤ)))))
    {n h : ℕ} (hhn : h ≤ n) (hn_m2 : m2 ≤ n) (hn_pos : 0 < n) {rho hprime : ℝ}
    (hgammarho : gamma ≤ rho) :
    ∃ X : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ, Measurable X ∧
      Homogenization.IndependentSums.IsBigO P.toMeasure PsiS X (H * (n : ℝ) ^ D) ∧
      (∀ (omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d)
        (Q : Homogenization.TriadicCube d),
        Q.scale ≤ (n : ℤ) → (Q.scale : ℝ) ≤ hprime →
        Homogenization.cubeCenter Q ∈
            Homogenization.cubeSet (Homogenization.originCube d (n : ℤ)) →
        ((3 : ℝ) ^ (-(rho * ((n : ℝ) - (Q.scale : ℝ)))) *
            akhcTailEll_excess
              (SuperdiffusionCLT.Section2.Annealed.annealedBlockMatrix nu L P
                (Homogenization.cubeSet (Homogenization.originCube d (h : ℤ))))
              (Homogenization.coarseBlockMatrix (Homogenization.cubeSet Q)
                (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff nu omega L).toCoeffField))
            ^ (2 : ℝ) ≤
          ((3 : ℝ) ^ (-(rho - gamma) * ((n : ℝ) - hprime)) * |X omega|) ^ (2 : ℝ)) ∧
      ∫ omega, ((3 : ℝ) ^ (-(rho - gamma) * ((n : ℝ) - hprime)) * |X omega|) ^ (2 : ℝ)
          ∂P.toMeasure ≤
        3 * KPsiS ^ 36 * (H * (n : ℝ) ^ D) ^ (2 : ℝ) *
            (3 : ℝ) ^ (-2 * (rho - gamma) * ((n : ℝ) - hprime)) / (min 3 pPsiS - 2) := by
  obtain ⟨X, hXm, hXbig, hnorm⟩ :=
    akhcTailEll_normalized_excess_le hnu hPrefix hJ2 hJ4 gamma H D m2 PsiS KPsiS pPsiS hgamma0
      hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 hhn hn_m2 hgammarho
  set B : ℝ := (3 : ℝ) ^ (-(rho - gamma) * ((n : ℝ) - hprime)) with hBdef
  have hB_nonneg : (0 : ℝ) ≤ B := Real.rpow_nonneg (by norm_num) _
  refine ⟨X, hXm, hXbig, ?_, ?_⟩
  · intro omega Q hQn hQhprime hQcenter
    have hle := hnorm omega Q hQn hQhprime hQcenter
    have hnn :
        (0 : ℝ) ≤ (3 : ℝ) ^ (-(rho * ((n : ℝ) - (Q.scale : ℝ)))) *
          akhcTailEll_excess
            (SuperdiffusionCLT.Section2.Annealed.annealedBlockMatrix nu L P
              (Homogenization.cubeSet (Homogenization.originCube d (h : ℤ))))
            (Homogenization.coarseBlockMatrix (Homogenization.cubeSet Q)
              (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff nu omega L).toCoeffField) :=
      mul_nonneg (Real.rpow_nonneg (by norm_num) _) (akhcTailEll_excess_nonneg _ _)
    exact Real.rpow_le_rpow hnn hle (by norm_num)
  · have hH_pos : (0 : ℝ) < H := lt_of_lt_of_le zero_lt_one hH
    have hn_pos' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn_pos
    have hmoment := akhcTailEllB_moment_le hKPsiS hpPsiS
      (mul_pos hH_pos (Real.rpow_pos_of_pos hn_pos' D)) hPsiSOne hGrowth hXm hXbig
    have hptwise : ∀ omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d,
        (B * |X omega|) ^ (2 : ℝ) = B ^ (2 : ℝ) * |X omega| ^ (2 : ℝ) :=
      fun omega => Real.mul_rpow hB_nonneg (abs_nonneg _)
    have hBpow_nonneg : (0 : ℝ) ≤ B ^ (2 : ℝ) := Real.rpow_nonneg hB_nonneg _
    have hBeq : B ^ (2 : ℝ) = (3 : ℝ) ^ (-2 * (rho - gamma) * ((n : ℝ) - hprime)) := by
      rw [hBdef, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
      congr 1
      ring
    calc ∫ omega, (B * |X omega|) ^ (2 : ℝ) ∂P.toMeasure
        = ∫ omega, B ^ (2 : ℝ) * |X omega| ^ (2 : ℝ) ∂P.toMeasure := by
          simp_rw [hptwise]
      _ = B ^ (2 : ℝ) * ∫ omega, |X omega| ^ (2 : ℝ) ∂P.toMeasure :=
          MeasureTheory.integral_const_mul _ _
      _ ≤ B ^ (2 : ℝ) * (3 * KPsiS ^ 36 / (min 3 pPsiS - 2) * (H * (n : ℝ) ^ D) ^ (2 : ℝ)) :=
          mul_le_mul_of_nonneg_left hmoment hBpow_nonneg
      _ = 3 * KPsiS ^ 36 * (H * (n : ℝ) ^ D) ^ (2 : ℝ) *
            (3 : ℝ) ^ (-2 * (rho - gamma) * ((n : ℝ) - hprime)) / (min 3 pPsiS - 2) := by
          rw [hBeq]; ring

end

end SuperdiffusionCLT.AKHC61.Tails

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.AKHC61.WeakNorms.PrimeE
public import SuperdiffusionCLT.AKHC61.Carrier.IntegrabilitySq

/-!
# Package C6, part 6: node 7 at the Step 2 scales

`akhcPrime_step2_energy_le`: at the parent scale `m` and the pigeonhole scale `h = m - ℓ`
(Lemma `l.weaknorms.prime` applied with `n = k`, `h = k - L`), the expected
route-W weak-norm energy in the source's normalization `M₀ = diag(σ̂_m, σ̂_m⁻¹)` satisfies

`E[σ̂ G² + σ̂⁻¹ F²] ≤ K(d, s', ρ) Θ_m (V + δ₁ + M + 3^{-(1-2s')ℓ}(1 + M) + 3^{-ℓ})`,

where `V` bounds `E|Ahom_m^{-1/2}(bfA(cu_n) − Ahom_m)Ahom_m^{-1/2}|²` for `n ∈ (m-ℓ, m]`
(`e.variance.HC.prime`), `δ₁` is the pigeonhole closeness `Ahom(cu_{m-ℓ}) ≤ (1+δ₁) Ahom(cu_m)`,
and `M ≥ E[G] ≥ E[(M⁺_{m,ρ})²]` is package C3's second moment of the maximal excess normalized
by `Ahom(cu_{m-ℓ})` (`e.mathcalM.m.rho.bound`). The random ellipticity enters only through
second moments; in the mismatch term the product `(1+M⁺)·defect` is split by Young's inequality
with `ε = Θ_m^{1/2}`, never bounding the defect by `1 + 3^{ρ(m-n)} M⁺`.

The constant `K(d, s', ρ)` (`akhcPrime_Kst`) contains the maximizer constant
`akhcWeakC2_maximizerConst s' ρ = (1 + S(s',ρ))²`, which blows up as `ρ/2 → s'`, and
`(1/2 − s')⁻²`; with `ρ ≥ γ` this is the source's hidden `1/(2s − ρ)` factor of
`l.weaknorms.moreproto`.
-/

@[expose] public section

namespace SuperdiffusionCLT.AKHC61.WeakNorms

open Homogenization MeasureTheory
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.AKHC61.Response

noncomputable section

/-- The Step 2 constant `K(d, s', ρ)`. -/
noncomputable def akhcPrime_Kst (d : ℕ) (s' ρ : ℝ) : ℝ :=
  16 * (2 * (1 - Real.rpow (3 : ℝ) (-(1 / 2 : ℝ)))⁻¹ ^ 2 +
    8 * Book.Ch05.Section53.WeakNormsMaximizer.section53WeakNormMaximizerConst d ^ 2 *
      akhcWeakC2_maximizerConst s' ρ * (1 - Real.rpow (3 : ℝ) (-(1 / 2 - s')))⁻¹ ^ 2 +
    24 * Book.Ch05.Section53.WeakNormsMaximizer.section53WeakNormMaximizerConst d ^ 2 *
      akhcWeakC2_maximizerConst s' ρ * ((1 / 2 - s')⁻¹) ^ 2 +
    8 * Book.Ch05.Section53.WeakNormsMaximizer.section53WeakNormMaximizerConst d ^ 2)

/-- **The Step 2 assembly, pure real form.** -/
theorem akhcPrime_assembly {IA ID IF IG θ u Sw Sβ κ Bj U2 CT C Gβ Gs cK δ Mm V T1 T2 s0 : ℝ}
    (hθ : θ = u * u) (hu : 1 ≤ u) (hcK : 0 ≤ cK) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hV : 0 ≤ V) (hMm : 0 ≤ Mm) (hT1 : 0 ≤ T1) (hT2 : 0 ≤ T2) (hs0 : 0 ≤ s0)
    (hSw0 : 0 ≤ Sw) (hSw : Sw ≤ Gs) (hSβ0 : 0 ≤ Sβ) (hSβ : Sβ ≤ Gβ)
    (hIA : IA ≤ Sβ * (Sβ * (2 * θ * V)))
    (hID : ID ≤ Sw * (δ * u)) (hIG0 : 0 ≤ IG) (hIG : IG ≤ Mm) (hIF : IF ≤ Sw * (2 * V))
    (hκ0 : 0 ≤ κ) (hκ : κ ≤ 2 * cK * (1 + δ) * u) (hBj0 : 0 ≤ Bj) (hBj : Bj ≤ (1 + δ) * u + 1)
    (hU2 : U2 ≤ s0 * T1) (hU20 : 0 ≤ U2) (hCT : CT ≤ 8 * T2 * θ) :
    16 * (IA + C ^ 2 * κ * Sw * (ID + u / 2 * Sw * IG + θ / u * IF) +
        C ^ 2 * U2 * κ * (Bj * (2 * (1 + IG))) + C ^ 2 * CT) ≤
      16 * (2 * Gβ ^ 2 + 8 * C ^ 2 * cK * Gs ^ 2 + 24 * C ^ 2 * cK * s0 + 8 * C ^ 2) *
        θ * (V + δ + Mm + T1 * (1 + Mm) + T2) := by
  have hu0 : 0 < u := by linarith only [hu]
  have hθ0 : 0 ≤ θ := by rw [hθ]; positivity
  have hθu : θ / u = u := by rw [hθ]; field_simp
  rw [hθu]
  have hGs0 : 0 ≤ Gs := hSw0.trans hSw
  have hGβ0 : 0 ≤ Gβ := hSβ0.trans hSβ
  have hC2 : 0 ≤ C ^ 2 := sq_nonneg C
  set S := V + δ + Mm + T1 * (1 + Mm) + T2 with hS
  have hS0 : 0 ≤ S := by positivity
  have hVS : V ≤ S := by nlinarith only [hδ0, hMm, hT1, hT2, hV, hS]
  -- (i)
  have hβ2 : Sβ * Sβ ≤ Gβ ^ 2 := by nlinarith only [hSβ0, hSβ]
  have h1 : IA ≤ 2 * Gβ ^ 2 * θ * S := by
    have := mul_le_mul_of_nonneg_right hβ2 (by positivity : 0 ≤ 2 * θ * V)
    have h2 : 2 * θ * V ≤ 2 * θ * S := mul_le_mul_of_nonneg_left hVS (by positivity)
    have h3 := mul_le_mul_of_nonneg_left h2 (sq_nonneg Gβ)
    calc IA ≤ Sβ * (Sβ * (2 * θ * V)) := hIA
      _ = Sβ * Sβ * (2 * θ * V) := by ring
      _ ≤ Gβ ^ 2 * (2 * θ * V) := this
      _ ≤ Gβ ^ 2 * (2 * θ * S) := h3
      _ = 2 * Gβ ^ 2 * θ * S := by ring
  -- (ii)-(iii)
  have hB : ID + u / 2 * Sw * IG + u * IF ≤ Sw * u * (δ + Mm / 2 + 2 * V) := by
    have a1 : u / 2 * Sw * IG ≤ u / 2 * Sw * Mm :=
      mul_le_mul_of_nonneg_left hIG (by positivity)
    have a2 : u * IF ≤ u * (Sw * (2 * V)) := mul_le_mul_of_nonneg_left hIF hu0.le
    nlinarith only [hID, a1, a2]
  have hB0 : 0 ≤ Sw * u * (δ + Mm / 2 + 2 * V) := by positivity
  have hκ' : κ ≤ 4 * cK * u := by
    nlinarith only [hκ, mul_nonneg (mul_nonneg hcK hu0.le) (sub_nonneg.2 hδ1)]
  have hSw2 : Sw * Sw ≤ Gs ^ 2 := by nlinarith only [hSw0, hSw]
  have h2 : C ^ 2 * κ * Sw * (ID + u / 2 * Sw * IG + u * IF) ≤
      8 * C ^ 2 * cK * Gs ^ 2 * θ * S := by
    have b1 : C ^ 2 * κ * Sw * (ID + u / 2 * Sw * IG + u * IF) ≤
        C ^ 2 * κ * Sw * (Sw * u * (δ + Mm / 2 + 2 * V)) :=
      mul_le_mul_of_nonneg_left hB (by positivity)
    have b2 : C ^ 2 * κ * Sw * (Sw * u * (δ + Mm / 2 + 2 * V)) ≤
        C ^ 2 * (4 * cK * u) * Sw * (Sw * u * (δ + Mm / 2 + 2 * V)) := by
      have := mul_le_mul_of_nonneg_left hκ' hC2
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right this hSw0) hB0
    have b3 : δ + Mm / 2 + 2 * V ≤ 2 * S := by nlinarith only [hδ0, hMm, hT1, hT2, hV, hS]
    have b4 : C ^ 2 * (4 * cK * u) * Sw * (Sw * u * (δ + Mm / 2 + 2 * V)) =
        4 * C ^ 2 * cK * (Sw * Sw) * (u * u) * (δ + Mm / 2 + 2 * V) := by ring
    have b5 : 4 * C ^ 2 * cK * (Sw * Sw) * (u * u) * (δ + Mm / 2 + 2 * V) ≤
        4 * C ^ 2 * cK * Gs ^ 2 * (u * u) * (2 * S) := by
      have c1 : 0 ≤ 4 * C ^ 2 * cK := by positivity
      have c2 := mul_le_mul_of_nonneg_left hSw2 c1
      have c3 : 0 ≤ u * u := by positivity
      have c4 := mul_le_mul_of_nonneg_right c2 c3
      have c5 : 0 ≤ δ + Mm / 2 + 2 * V := by positivity
      calc 4 * C ^ 2 * cK * (Sw * Sw) * (u * u) * (δ + Mm / 2 + 2 * V)
          ≤ 4 * C ^ 2 * cK * Gs ^ 2 * (u * u) * (δ + Mm / 2 + 2 * V) :=
            mul_le_mul_of_nonneg_right c4 c5
        _ ≤ 4 * C ^ 2 * cK * Gs ^ 2 * (u * u) * (2 * S) :=
            mul_le_mul_of_nonneg_left b3 (by positivity)
    calc _ ≤ _ := b1
      _ ≤ _ := b2
      _ = _ := b4
      _ ≤ _ := b5
      _ = 8 * C ^ 2 * cK * Gs ^ 2 * θ * S := by rw [hθ]; ring
  -- (iv)
  have h3 : C ^ 2 * U2 * κ * (Bj * (2 * (1 + IG))) ≤ 24 * C ^ 2 * cK * s0 * θ * S := by
    have d1 : Bj * (2 * (1 + IG)) ≤ (3 * u) * (2 * (1 + Mm)) := by
      have e1 : Bj ≤ 3 * u := by nlinarith only [hBj, hδ1, hu]
      have e2 : 2 * (1 + IG) ≤ 2 * (1 + Mm) := by linarith only [hIG]
      have e3 : 0 ≤ 2 * (1 + IG) := by linarith only [hIG0]
      exact mul_le_mul e1 e2 e3 (by positivity)
    have d0 : 0 ≤ Bj * (2 * (1 + IG)) := mul_nonneg hBj0 (by linarith only [hIG0])
    have d2 : U2 * κ ≤ s0 * T1 * (4 * cK * u) :=
      mul_le_mul hU2 hκ' hκ0 (by positivity)
    have d3 : 0 ≤ U2 * κ := mul_nonneg hU20 hκ0
    have d4 : U2 * κ * (Bj * (2 * (1 + IG))) ≤ s0 * T1 * (4 * cK * u) * ((3 * u) * (2 * (1 + Mm))) := by
      exact mul_le_mul d2 d1 d0 (by positivity)
    have d5 : s0 * T1 * (4 * cK * u) * ((3 * u) * (2 * (1 + Mm))) =
        24 * cK * s0 * (u * u) * (T1 * (1 + Mm)) := by ring
    have d6 : T1 * (1 + Mm) ≤ S := by nlinarith only [hδ0, hMm, hT1, hT2, hV, hS]
    have d7 : 24 * cK * s0 * (u * u) * (T1 * (1 + Mm)) ≤ 24 * cK * s0 * θ * S := by
      rw [← hθ]; exact mul_le_mul_of_nonneg_left d6 (by positivity)
    have d8 := mul_le_mul_of_nonneg_left d4 hC2
    nlinarith only [d8, d5, d7, hC2]
  -- (v)
  have h4 : C ^ 2 * CT ≤ 8 * C ^ 2 * θ * S := by
    have f1 : T2 ≤ S := by nlinarith only [hδ0, hMm, hT1, hT2, hV, hS]
    have f2 : CT ≤ 8 * θ * S := hCT.trans (by nlinarith only [f1, hθ0])
    nlinarith only [mul_le_mul_of_nonneg_left f2 hC2]
  nlinarith only [h1, h2, h3, h4]

section Law

variable {d : ℕ} [NeZero d] {nu : ℝ} (hnu : 0 < nu)
  (P : ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d)) (L : ℕ)
  (gamma H D : ℝ) (m2 : ℕ) (PsiS : ℝ → ℝ) (KPsiS pPsiS : ℝ)
  (hgamma0 : 0 ≤ gamma) (hgamma1 : gamma < 1) (hH : 1 ≤ H) (hD : 0 ≤ D)
  (hPsiSMono : MonotoneOn PsiS (Set.Ici 0)) (hPsiSOne : ∀ t : ℝ, 0 ≤ t → 1 ≤ PsiS t)
  (hKPsiS : 1 ≤ KPsiS) (hpPsiS : 2 < pPsiS)
  (hGrowth : ∀ p : ℝ, 2 ≤ p → p ≤ pPsiS → ∀ t s : ℝ, 1 ≤ t → 1 ≤ s →
    s ^ p ≤ KPsiS ^ (3 * ⌈p⌉₊ ^ 2) * (PsiS (t * s) / PsiS t))
  (hP2 : ∀ j : ℕ, m2 ≤ j →
    ∃ X : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ,
      Measurable X ∧
      Homogenization.IndependentSums.IsBigO P.toMeasure PsiS X
        (H * (j : ℝ) ^ D) ∧
      ∀ (omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d)
        (Q : Homogenization.TriadicCube d),
        Q.scale ≤ (j : ℤ) →
        Homogenization.cubeCenter Q ∈
            Homogenization.cubeSet (Homogenization.originCube d (j : ℤ)) →
          Homogenization.BlockMatLoewnerLE
            (Homogenization.coarseBlockMatrix (Homogenization.cubeSet Q)
              (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff nu
                  omega L).toCoeffField)
            ((1 + (3 : ℝ) ^ (-(gamma * ((Q.scale : ℝ) - (j : ℝ)))) *
                  X omega) •
              SuperdiffusionCLT.Section2.Annealed.annealedBlockMatrix nu L P
                (Homogenization.cubeSet
                  (Homogenization.originCube d (j : ℤ)))))
  (hJ4 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P)

include hnu hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 hJ4 in
/-- **Node 7 (`l.weaknorms.prime`) at the Step 2 scales, route W.** See the module docstring. -/
theorem akhcPrime_step2_energy_le
    (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
    (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P)
    {m ell : ℕ} (hell : 1 ≤ ell) (hellm : ell ≤ m) (hm2 : m2 ≤ m)
    {s' ρ : ℝ} (hlo : 1 / 4 ≤ s') (hhi : s' < 1 / 2) (hgap : ρ / 2 < s')
    (e : Vec d) (he : vecNormSq e = 1) {δ₁ : ℝ} (hδ0 : 0 ≤ δ₁) (hδ1 : δ₁ ≤ 1)
    (hPigB : sigmaBarSeq nu L P (m - ell) ≤ (1 + δ₁) * sigmaBarSeq nu L P m)
    (hPigC : sigmaBarStarInvSeq nu L P (m - ell) ≤ (1 + δ₁) * sigmaBarStarInvSeq nu L P m)
    {V : ℝ} (hV0 : 0 ≤ V)
    (hV : ∀ n ∈ Finset.Icc (((m - ell : ℕ) : ℤ) + 1) (m : ℤ),
      ∫ a, akhcFullBlockNormalizedFluctuationAtScale nu L P (m : ℤ) (originCube d n) a
        ∂(cutoffLaw (d := d) nu L P) ≤ V)
    (G : ShellSeq d → ℝ) (hGint : Integrable G P.toMeasure)
    (hMG : ∀ omega,
      SuperdiffusionCLT.AKHC61.Tails.akhcMM_Mplus nu L P m (m - ell) ρ omega ^ 2 ≤ G omega)
    (hBdd : ∀ omega : ShellSeq d, BddAbove {M : ℝ | ∃ Q : TriadicCube d,
      Q.scale ≤ ((m : ℕ) : ℤ) ∧ cubeCenter Q ∈ cubeSet (originCube d ((m : ℕ) : ℤ)) ∧
      M = Real.rpow (3 : ℝ) (-ρ * ((((m : ℕ) : ℤ) : ℝ) - (Q.scale : ℝ))) *
        SuperdiffusionCLT.AKHC61.Tails.akhcTailEll_excess
          (annealedBlockMatrix nu L P (cubeSet (originCube d ((m - ell : ℕ) : ℤ))))
          (coarseBlockMatrix (cubeSet Q) (coefficientCutoff nu omega L).toCoeffField)})
    {Mm : ℝ} (hGMm : ∫ omega, G omega ∂P.toMeasure ≤ Mm) :
    ∫ a, akhcPrime_energy nu L P m e a ∂(cutoffLaw (d := d) nu L P) ≤
      akhcPrime_Kst d s' ρ * SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P m *
        (V + δ₁ + Mm + Real.rpow (3 : ℝ) (-(1 / 2 - s') * (ell : ℝ)) ^ 2 * (1 + Mm) +
          Real.rpow (3 : ℝ) (-(ell : ℝ))) := by
  have hm : 0 < m := by omega
  have hkm : m - ell < m := by omega
  have hkmZ : ((m - ell : ℕ) : ℤ) ≤ (m : ℤ) := by exact_mod_cast Nat.sub_le m ell
  have htoNat : Int.toNat ((m : ℤ) - ((m - ell : ℕ) : ℤ)) = ell := by omega
  -- scalars at scale `m`
  have hb := SuperdiffusionCLT.AKHC61.Carrier.akhc_sigmaBarSeq_pos_of_P2 hnu hJ4 gamma H D
    m2 PsiS KPsiS pPsiS hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 m
  have hc := SuperdiffusionCLT.AKHC61.Carrier.akhc_sigmaBarStarInvSeq_pos_of_P2 hnu hJ4
    gamma H D m2 PsiS KPsiS pPsiS hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS
    hGrowth hP2 m
  have hθ1 := SuperdiffusionCLT.AKHC61.Carrier.akhc_one_le_thetaCutoff_of_P2 hnu hJ4 gamma
    H D m2 PsiS KPsiS pPsiS hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 m
  have hbh := SuperdiffusionCLT.AKHC61.Carrier.akhc_sigmaBarSeq_pos_of_P2 hnu hJ4 gamma H D
    m2 PsiS KPsiS pPsiS hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2
    (m - ell)
  have hch := SuperdiffusionCLT.AKHC61.Carrier.akhc_sigmaBarStarInvSeq_pos_of_P2 hnu hJ4
    gamma H D m2 PsiS KPsiS pPsiS hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS
    hGrowth hP2 (m - ell)
  set b := sigmaBarSeq nu L P m
  set c := sigmaBarStarInvSeq nu L P m
  have hθ : SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P m = b * c := rfl
  set u := Real.sqrt (b * c) with hudef
  have huu : b * c = u * u := (Real.mul_self_sqrt (mul_pos hb hc).le).symm
  have hu1 : 1 ≤ u := by rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt (hθ ▸ hθ1)
  have hu0 : 0 < u := by linarith only [hu1]
  set σ := akhcSigmaHatAtScale nu L P (m : ℤ)
  have hσ : 0 < σ := akhcPrime_sigmaHat_pos (m := (m : ℤ)) hb hc
  obtain ⟨hσc, hσb⟩ := akhcPrime_sigmaHat_mul hb hc
  have hσdef : σ = Real.sqrt (b * c⁻¹) := rfl
  rw [← hσdef, ← hudef] at hσc hσb
  -- the reference and integrability inputs
  have hE := akhcWNSq_annealed_posDef hnu hJ4 gamma H D m2 PsiS KPsiS pPsiS hgamma0 hgamma1 hH
    hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 ((m - ell : ℕ) : ℤ)
  have hIntFluct : ∀ R : TriadicCube d,
      Integrable (fun a => akhcFullBlockNormalizedFluctuationAtScale nu L P (m : ℤ) R a)
        (cutoffLaw (d := d) nu L P) := fun R =>
    SuperdiffusionCLT.AKHC61.Carrier.akhcSq_integrable_fullBlockNormalizedFluctuationAtScale_of_P2
      hnu P L gamma H D m2 PsiS KPsiS pPsiS hKPsiS hpPsiS hPsiSOne hGrowth hP2 (m : ℤ) R
  set p := akhcSpecialPAtScale nu L P (m : ℤ) e
  set q := akhcSpecialQAtScale nu L P (m : ℤ) e
  have hJint : ∀ Q : TriadicCube d,
      Integrable (Book.Ch04.restrictionResponseJObservableCubeSet Q p q)
        (cutoffLaw (d := d) nu L P) := fun Q =>
    SuperdiffusionCLT.AKHC61.Response.akhc_integrable_restrictionResponseJObservableCubeSet_cutoffLaw
      d hnu P L gamma H D m2 PsiS KPsiS pPsiS hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS
      hpPsiS hGrowth hP2 Q p q
  have hIntEn : Integrable (akhcPrime_energy nu L P m e) (cutoffLaw (d := d) nu L P) := by
    unfold akhcPrime_energy
    exact ((akhcWNSq_integrable_gradientWeakNorm_sq hnu hPrefix hJ2 hJ4 gamma H D m2 PsiS KPsiS
      pPsiS hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 hm2 hm _ _ _).const_mul
        _).add ((akhcWNSq_integrable_fluxWeakNorm_sq hnu hPrefix hJ2 hJ4 gamma H D m2 PsiS KPsiS
      pPsiS hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 hm2 hm _ _ _).const_mul
        _)
  obtain ⟨hIntA, hIA⟩ := akhcPrime_integral_avgDom L hPrefix hJ2 hnu (1 / 2) m (m - ell) hIntFluct
  obtain ⟨hIntD, hID⟩ := akhcPrime_integral_defSum L hnu hPrefix hJ2 s' m (m - ell) p q hJint
  obtain ⟨hIntF, hIF⟩ := akhcPrime_integral_flSum L hnu hPrefix hJ2 s' m (m - ell) hIntFluct
  have hmain := akhcPrime_expected_energy_le hnu L hJ4 hkm (β := 1 / 2) (ε := u) le_rfl hlo hhi
    hgap hu0 e he hb hc hE G hGint hMG hBdd hIntA hIntD hIntF hIntEn
  refine hmain.trans ?_
  rw [hIA, hID, hIF]
  -- the geometric sums
  set Sβ := ∑ n ∈ Finset.Icc (((m - ell : ℕ) : ℤ) + 1) (m : ℤ),
    Real.rpow (3 : ℝ) (-(1 / 2 : ℝ) * (Int.toNat ((m : ℤ) - n) : ℝ)) with hSβdef
  have hSβ0 : 0 ≤ Sβ := Finset.sum_nonneg fun _ _ => Real.rpow_nonneg (by norm_num) _
  have hSβ : Sβ ≤ (1 - Real.rpow (3 : ℝ) (-(1 / 2 : ℝ)))⁻¹ :=
    akhcPrime_geom_le hkmZ (by norm_num)
  set Sw := akhcPrime_wSum (1 / 2) s' (m : ℤ) ((m - ell : ℕ) : ℤ) with hSwdef
  have hSw0 : 0 ≤ Sw := akhcPrime_wSum_nonneg _ _ _ _
  have hSw : Sw ≤ (1 - Real.rpow (3 : ℝ) (-(1 / 2 - s')))⁻¹ :=
    akhcPrime_geom_le hkmZ (by linarith only [hhi])
  -- membership bookkeeping
  have hmem : ∀ n ∈ Finset.Icc (((m - ell : ℕ) : ℤ) + 1) (m : ℤ),
      m - ell ≤ Int.toNat n ∧ Int.toNat n ≤ m ∧ ((Int.toNat n : ℕ) : ℤ) = n := by
    intro n hn
    have h1 := (Finset.mem_Icc.1 hn).1
    have h2 := (Finset.mem_Icc.1 hn).2
    refine ⟨by omega, by omega, by omega⟩
  have hmm : (m : ℤ) ∈ Finset.Icc (((m - ell : ℕ) : ℤ) + 1) (m : ℤ) := by
    rw [Finset.mem_Icc]; constructor <;> omega
  -- the node-16 piece
  have hIAb : Sβ * ∑ n ∈ Finset.Icc (((m - ell : ℕ) : ℤ) + 1) (m : ℤ),
      Real.rpow (3 : ℝ) (-(1 / 2 : ℝ) * (Int.toNat ((m : ℤ) - n) : ℝ)) *
        (2 * SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P m) *
        ∫ a, akhcFullBlockNormalizedFluctuationAtScale nu L P (m : ℤ) (originCube d n) a
          ∂(cutoffLaw (d := d) nu L P) ≤
      Sβ * (Sβ * (2 * SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P m * V)) := by
    refine mul_le_mul_of_nonneg_left ?_ hSβ0
    rw [hSβdef, Finset.sum_mul]
    refine Finset.sum_le_sum fun n hn => ?_
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg (by norm_num) _)
    exact mul_le_mul_of_nonneg_left (hV n hn) (by rw [hθ]; positivity)
  -- the defect piece
  have hIDb : ∑ n ∈ Finset.Icc (((m - ell : ℕ) : ℤ) + 1) (m : ℤ),
      akhcPrime_w (1 / 2) s' (m : ℤ) n *
        Book.Ch05.tauAtScale (cutoffLaw (d := d) nu L P) (m : ℤ) n p q ≤ Sw * (δ₁ * u) := by
    rw [hSwdef, akhcPrime_wSum, Finset.sum_mul]
    refine Finset.sum_le_sum fun n hn => ?_
    refine mul_le_mul_of_nonneg_left ?_ (akhcPrime_w_nonneg _ _ _ _)
    obtain ⟨h1, _, h3⟩ := hmem n hn
    have hbn : sigmaBarSeq nu L P (Int.toNat n) ≤ (1 + δ₁) * b :=
      (SuperdiffusionCLT.AKHC61.Carrier.akhc_antitone_sigmaBarSeq_of_P2 hnu hPrefix hJ2 hJ4
        gamma H D m2 PsiS KPsiS pPsiS hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS
        hGrowth hP2 h1).trans hPigB
    have hcn : sigmaBarStarInvSeq nu L P (Int.toNat n) ≤ (1 + δ₁) * c :=
      (SuperdiffusionCLT.AKHC61.Carrier.akhc_antitone_sigmaBarStarInvSeq_of_P2 hnu hPrefix
        hJ2 gamma H D m2 PsiS KPsiS pPsiS hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS
        hpPsiS hGrowth hP2 h1).trans hPigC
    have ht := akhcPrime_tau_le hnu P L gamma H D m2 PsiS KPsiS pPsiS hgamma0 hgamma1 hH hD
      hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 hJ4 m (Int.toNat n) e he hbn hcn
    rw [h3] at ht
    exact ht
  -- the fluctuation piece
  have hIFb : ∑ n ∈ Finset.Icc (((m - ell : ℕ) : ℤ) + 1) (m : ℤ),
      akhcPrime_w (1 / 2) s' (m : ℤ) n *
        ((∫ a, akhcFullBlockNormalizedFluctuationAtScale nu L P (m : ℤ) (originCube d n) a
            ∂(cutoffLaw (d := d) nu L P)) +
          ∫ a, akhcFullBlockNormalizedFluctuationAtScale nu L P (m : ℤ)
            (originCube d (m : ℤ)) a ∂(cutoffLaw (d := d) nu L P)) ≤ Sw * (2 * V) := by
    rw [hSwdef, akhcPrime_wSum, Finset.sum_mul]
    refine Finset.sum_le_sum fun n hn => ?_
    refine mul_le_mul_of_nonneg_left ?_ (akhcPrime_w_nonneg _ _ _ _)
    linarith only [hV n hn, hV _ hmm]
  -- the M⁺ dominator
  have hIG0 : 0 ≤ ∫ omega, G omega ∂P.toMeasure :=
    integral_nonneg fun omega => (sq_nonneg _).trans (hMG omega)
  -- κ and B_J
  set cK := akhcWeakC2_maximizerConst s' ρ with hcKdef
  have hcK : 0 ≤ cK := by rw [hcKdef]; unfold akhcWeakC2_maximizerConst; exact sq_nonneg _
  have hLR := akhcPrime_matrixNorm_lowerRight hnu L hJ4 ((m - ell : ℕ) : ℤ) hch.le
  have hUL := akhcPrime_matrixNorm_upperLeft hnu L hJ4 ((m - ell : ℕ) : ℤ) hbh.le
  rw [hLR, hUL]
  have hchS : sigmaBarStarInvScalar nu L P (cubeSet (originCube d ((m - ell : ℕ) : ℤ))) =
      sigmaBarStarInvSeq nu L P (m - ell) := rfl
  have hbhS : sigmaBarScalar nu L P (cubeSet (originCube d ((m - ell : ℕ) : ℤ))) =
      sigmaBarSeq nu L P (m - ell) := rfl
  rw [hchS, hbhS]
  have hσi : 0 < σ⁻¹ := inv_pos.2 hσ
  have hκ : σ * (cK * sigmaBarStarInvSeq nu L P (m - ell)) +
      σ⁻¹ * (cK * sigmaBarSeq nu L P (m - ell)) ≤ 2 * cK * (1 + δ₁) * u := by
    have k1 : σ * sigmaBarStarInvSeq nu L P (m - ell) ≤ (1 + δ₁) * u := by
      rw [← hσc]
      calc σ * sigmaBarStarInvSeq nu L P (m - ell) ≤ σ * ((1 + δ₁) * c) :=
            mul_le_mul_of_nonneg_left hPigC hσ.le
        _ = (1 + δ₁) * (σ * c) := by ring
    have k2 : σ⁻¹ * sigmaBarSeq nu L P (m - ell) ≤ (1 + δ₁) * u := by
      rw [← hσb]
      calc σ⁻¹ * sigmaBarSeq nu L P (m - ell) ≤ σ⁻¹ * ((1 + δ₁) * b) :=
            mul_le_mul_of_nonneg_left hPigB hσi.le
        _ = (1 + δ₁) * (σ⁻¹ * b) := by ring
    have k3 := mul_le_mul_of_nonneg_left (add_le_add k1 k2) hcK
    nlinarith only [k3]
  have hκ0 : 0 ≤ σ * (cK * sigmaBarStarInvSeq nu L P (m - ell)) +
      σ⁻¹ * (cK * sigmaBarSeq nu L P (m - ell)) :=
    add_nonneg (mul_nonneg hσ.le (mul_nonneg hcK hch.le))
      (mul_nonneg (inv_pos.2 hσ).le (mul_nonneg hcK hbh.le))
  rw [akhcPrime_Bj_eq hnu L hJ4]
  rw [hbhS, hchS]
  obtain ⟨hpp, hqq, hpq⟩ := akhcPrime_special_norms hσ he
  have hpp' : vecNormSq p = σ⁻¹ := hpp
  have hqq' : vecNormSq q = σ := hqq
  have hpq' : vecDot p q = 1 := hpq
  rw [hpp', hqq', hpq', abs_one]
  have hBj : (1 / 2 : ℝ) * (sigmaBarSeq nu L P (m - ell) * σ⁻¹ +
      sigmaBarStarInvSeq nu L P (m - ell) * σ) + 1 ≤ (1 + δ₁) * u + 1 := by
    have k1 : σ * sigmaBarStarInvSeq nu L P (m - ell) ≤ (1 + δ₁) * u := by
      rw [← hσc]
      calc σ * sigmaBarStarInvSeq nu L P (m - ell) ≤ σ * ((1 + δ₁) * c) :=
            mul_le_mul_of_nonneg_left hPigC hσ.le
        _ = (1 + δ₁) * (σ * c) := by ring
    have k2 : σ⁻¹ * sigmaBarSeq nu L P (m - ell) ≤ (1 + δ₁) * u := by
      rw [← hσb]
      calc σ⁻¹ * sigmaBarSeq nu L P (m - ell) ≤ σ⁻¹ * ((1 + δ₁) * b) :=
            mul_le_mul_of_nonneg_left hPigB hσi.le
        _ = (1 + δ₁) * (σ⁻¹ * b) := by ring
    nlinarith only [k1, k2]
  have hBj0 : 0 ≤ (1 / 2 : ℝ) * (sigmaBarSeq nu L P (m - ell) * σ⁻¹ +
      sigmaBarStarInvSeq nu L P (m - ell) * σ) + 1 :=
    add_nonneg (mul_nonneg one_half_pos.le (add_nonneg (mul_nonneg hbh.le (inv_pos.2 hσ).le)
      (mul_nonneg hch.le hσ.le))) zero_le_one
  -- the low-scale tail factor and the constant tail
  have hU2 : akhcPrime_u (1 / 2) s' (m : ℤ) ((m - ell : ℕ) : ℤ) ^ 2 =
      ((1 / 2 - s')⁻¹) ^ 2 * Real.rpow (3 : ℝ) (-(1 / 2 - s') * (ell : ℝ)) ^ 2 := by
    unfold akhcPrime_u
    rw [htoNat]
    ring
  have hCT := akhcPrime_constTail_le hnu P L gamma H D m2 PsiS KPsiS pPsiS hgamma0 hgamma1 hH hD
    hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 hJ4 m (m - ell) e he
  rw [htoNat] at hCT
  rw [hU2]
  have hθ' : SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P m = u * u := hθ.trans huu
  refine (akhcPrime_assembly hθ' hu1 hcK hδ0 hδ1 hV0 (hIG0.trans hGMm) (sq_nonneg _) (Real.rpow_nonneg zero_le_three _)
    (sq_nonneg _) hSw0 hSw hSβ0 hSβ hIAb hIDb hIG0 hGMm hIFb hκ0 hκ hBj0 hBj le_rfl
    (mul_nonneg (sq_nonneg _) (sq_nonneg _)) hCT).trans (le_of_eq ?_)
  unfold akhcPrime_Kst
  simp only [Real.rpow_eq_pow]
  ring

include hnu hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 hJ4 in
/-- **Node 7 at the Step 2 scales with V3's (P3′).** `akhcPrime_step2_energy_le` with the
second moment of `M⁺` supplied by package C3 (`akhcMM_Mplus_secondMoment_le`), in the
`e.mathcalM.m.rho.bound` form: the (P2′) term
`3 K_{Ψ_S}^{36} (H m^D)² 3^{-2(ρ-γ)(m - k₀ + 1)} / (min{3,p_{Ψ_S}} − 2)` plus the (P3′) term
`η/(η−2) K_Ψ^{…} ω_{m-ℓ}² (1 − 3^{-(2ρ − 2d/η)})⁻¹`. -/
theorem akhcPrime_step2_energy_le_of_P3
    (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
    (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P)
    -- (P3′) `a.CFS.weaker`, the clauses used, copied verbatim from
    -- `SuperdiffusionCLT.Frozen.Section4.akhc_weakerP3`
    (beta L1 L2 : ℝ) (m3 : ℕ) (omegaSeq : ℕ → ℝ) (Psi : ℝ → ℝ) (KPsi pPsi : ℝ)
    (hbeta0 : 0 ≤ beta) (hL1 : 1 ≤ L1) (hL2 : 1 ≤ L2) (homega : ∀ k : ℕ, 0 < omegaSeq k)
    (hPsiOne : ∀ t : ℝ, 0 ≤ t → 1 ≤ Psi t) (hKPsi : 1 ≤ KPsi)
    (hGrowthPsi : ∀ p : ℝ, 1 < p → p ≤ pPsi → ∀ t s : ℝ, 1 ≤ t → 1 ≤ s →
      s ^ p ≤ KPsi ^ (3 * ⌈p⌉₊ ^ 2) * (Psi (t * s) / Psi t))
    (hP3 : ∀ j n : ℕ, m3 ≤ n → beta * (j : ℝ) < (n : ℝ) →
      (n : ℝ) < (j : ℝ) - L1 * Real.log (L2 * (n : ℝ)) →
      ∃ X : ShellSeq d → ℝ,
        Measurable X ∧
        Homogenization.IndependentSums.IsBigO P.toMeasure Psi X (omegaSeq n) ∧
        ∀ (omega : ShellSeq d) (p q : Homogenization.BlockVec d),
          2 *
              (((Homogenization.descendantsAtDepth
                      (Homogenization.originCube d (j : ℤ)) (j - n)).card : ℝ)⁻¹ *
                ∑ R ∈ Homogenization.descendantsAtDepth
                    (Homogenization.originCube d (j : ℤ)) (j - n),
                  Homogenization.blockVecDot p
                    (Homogenization.blockMatVecMul
                      (Homogenization.ofFullBlockMat
                        (Homogenization.toFullBlockMat
                            (Homogenization.coarseBlockMatrix
                              (Homogenization.cubeSet R)
                              (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff
                                  nu omega L).toCoeffField) -
                          Homogenization.toFullBlockMat
                            (SuperdiffusionCLT.Section2.Annealed.annealedBlockMatrix
                              nu L P
                              (Homogenization.cubeSet
                                (Homogenization.originCube d (n : ℤ))))))
                      q)) ≤
            X omega *
              (Homogenization.blockVecDot p
                  (Homogenization.blockMatVecMul
                    (SuperdiffusionCLT.Section2.Annealed.annealedBlockMatrix nu L P
                      (Homogenization.cubeSet (Homogenization.originCube d (n : ℤ))))
                    p) +
                Homogenization.blockVecDot q
                  (Homogenization.blockMatVecMul
                    (SuperdiffusionCLT.Section2.Annealed.annealedBlockMatrix nu L P
                      (Homogenization.cubeSet (Homogenization.originCube d (n : ℤ))))
                    q)))
    {m ell k0 : ℕ} (hell : 1 ≤ ell) (hellm : ell ≤ m) (hm2 : m2 ≤ m) (hk0m : k0 ≤ m)
    (hm3 : m3 ≤ m - ell) (hbeta : beta * (m : ℝ) < ((m - ell : ℕ) : ℝ))
    (hwin : ((m - ell : ℕ) : ℝ) < (k0 : ℝ) - L1 * Real.log (L2 * ((m - ell : ℕ) : ℝ)))
    {s' ρ η : ℝ} (hlo : 1 / 4 ≤ s') (hhi : s' < 1 / 2) (hgap : ρ / 2 < s')
    (hgammarho : gamma ≤ ρ) (heta2 : 2 < η) (hetaPsi : η ≤ pPsi)
    (hc : 0 < 2 * ρ - 2 * (d : ℝ) / η)
    (e : Vec d) (he : vecNormSq e = 1) {δ₁ : ℝ} (hδ0 : 0 ≤ δ₁) (hδ1 : δ₁ ≤ 1)
    (hPigB : sigmaBarSeq nu L P (m - ell) ≤ (1 + δ₁) * sigmaBarSeq nu L P m)
    (hPigC : sigmaBarStarInvSeq nu L P (m - ell) ≤ (1 + δ₁) * sigmaBarStarInvSeq nu L P m)
    {V : ℝ} (hV0 : 0 ≤ V)
    (hV : ∀ n ∈ Finset.Icc (((m - ell : ℕ) : ℤ) + 1) (m : ℤ),
      ∫ a, akhcFullBlockNormalizedFluctuationAtScale nu L P (m : ℤ) (originCube d n) a
        ∂(cutoffLaw (d := d) nu L P) ≤ V) :
    ∫ a, akhcPrime_energy nu L P m e a ∂(cutoffLaw (d := d) nu L P) ≤
      akhcPrime_Kst d s' ρ * SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P m *
        (V + δ₁ + (3 * KPsiS ^ 36 * (H * (m : ℝ) ^ D) ^ (2 : ℝ) *
            (3 : ℝ) ^ (-2 * (ρ - gamma) * ((m : ℝ) - ((k0 : ℝ) - 1))) / (min 3 pPsiS - 2) +
          (η / (η - 2)) * KPsi ^ (3 * ⌈η⌉₊ ^ 2) *
            KPsi ^ (2 * (3 * (⌈η⌉₊ : ℝ) ^ 2) / η) * omegaSeq (m - ell) ^ 2 *
            (1 - (3 : ℝ) ^ (-(2 * ρ - 2 * (d : ℝ) / η)))⁻¹) +
          Real.rpow (3 : ℝ) (-(1 / 2 - s') * (ell : ℝ)) ^ 2 *
            (1 + (3 * KPsiS ^ 36 * (H * (m : ℝ) ^ D) ^ (2 : ℝ) *
              (3 : ℝ) ^ (-2 * (ρ - gamma) * ((m : ℝ) - ((k0 : ℝ) - 1))) / (min 3 pPsiS - 2) +
            (η / (η - 2)) * KPsi ^ (3 * ⌈η⌉₊ ^ 2) *
              KPsi ^ (2 * (3 * (⌈η⌉₊ : ℝ) ^ 2) / η) * omegaSeq (m - ell) ^ 2 *
              (1 - (3 : ℝ) ^ (-(2 * ρ - 2 * (d : ℝ) / η)))⁻¹)) +
          Real.rpow (3 : ℝ) (-(ell : ℝ))) := by
  obtain ⟨G, hGint, hMG, hBdd, hGle⟩ :=
    SuperdiffusionCLT.AKHC61.Tails.akhcMM_Mplus_secondMoment_le hnu hPrefix hJ2 hJ4 gamma H
      D m2 PsiS KPsiS pPsiS hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2
      beta L1 L2 m3 omegaSeq Psi KPsi pPsi hbeta0 hL1 hL2 homega hPsiOne hKPsi hGrowthPsi hP3
      (n := m) (h := m - ell) (k0 := k0) (Nat.sub_le m ell) hm2 (by omega) hk0m hm3 hbeta hwin
      hgammarho heta2 hetaPsi hc
  exact akhcPrime_step2_energy_le hnu P L gamma H D m2 PsiS KPsiS pPsiS hgamma0 hgamma1 hH hD
    hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 hJ4 hPrefix hJ2 hell hellm hm2 hlo hhi hgap e he
    hδ0 hδ1 hPigB hPigC hV0 hV G hGint hMG hBdd hGle

end Law

end

end SuperdiffusionCLT.AKHC61.WeakNorms

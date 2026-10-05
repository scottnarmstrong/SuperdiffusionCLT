/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Prereq.SuperdiffusivePoincare

/-!
# The superdiffusive Poincaré inequality with right-hand side, on balls

The Whitney lemma and the sharp bound for the diffusivity are taken as hypotheses `hWhitney`
and `hSigma`.  The main theorem is the lemma `l.superdiffusive.Poincare.with.rhs` on Euclidean
balls `B_R`, `R ≥ X`, for the
unit-scale field `fullCoefficientRecentered nu ω`: the print's `ε^{-1} = R` after the rescaling
`u_R(y) = u(ε y)`.

## Main results

* `Section8.sdPoinc_superdiffusive_poincare`.
-/

@[expose] public section

open MeasureTheory Homogenization
open scoped ENNReal Pointwise

namespace SuperdiffusionCLT.Section8

/-- **Superdiffusive Poincaré inequality with right-hand side, on balls.**
Almost surely in the sample, for every `R ≥ X`, every `u ∈ H¹(B_R)` with
`-∇·(a∇u) = f` weakly in `B_R` (`a` the recentred field) satisfies
`‖u - (u)_{B_R}‖_{L̲²(B_R)} ≤ C R c⋆^{-1/4} ν^{1/2} (log R)^{-1/4} ‖∇u‖_{L̲²(B_R)}
  + C R² ν^{-1} (log R)^{-100} ‖f‖_{L̲²(B_R)}`. -/
theorem sdPoinc_superdiffusive_poincare (d : ℕ) [NeZero d]
    (hWhitney :
      ∀ U : Set (Homogenization.Vec d),
        SuperdiffusionCLT.Section7.IsSmoothBoundedDomain U →
        U ⊆ Homogenization.openCubeSet (Homogenization.originCube d 0) →
        ∃ C : ℝ, 1 ≤ C ∧
          ∀ nu : ℝ, 0 < nu → nu ≤ 1 →
            ∀ cStar : ℝ, 0 < cStar →
              ∀ K : ℝ,
                ∀ ρ D M : ℝ, 0 < ρ → ρ < 1 → 1 ≤ D → C ≤ M →
                  ∃ Lhat : ℝ, 1 ≤ Lhat ∧
                    ∀ (P : MeasureTheory.ProbabilityMeasure
                          (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
                      (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
                      (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P)
                      (hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P),
                      SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P →
                      SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P →
                      SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ5 d P cStar K
                          hPrefix hJ2 hJ3 →
                      ∃ X : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ,
                        Measurable X ∧ (∀ omega, 1 ≤ X omega) ∧
                        -- e.Dir.new.Whitney.minscale.tail
                        Homogenization.IndependentSums.IsBigO P.toMeasure
                          (Homogenization.IndependentSums.gammaSigma ρ)
                          (fun omega => Real.log (X omega)) Lhat ∧
                        ∀ᵐ omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d
                            ∂P.toMeasure,
                          ∀ (t : ℝ) (m : ℕ),
                            X omega ≤ t → (3 : ℝ) ^ m < 3 * t → t ≤ (3 : ℝ) ^ m →
                            -- e.Dir.new.Whitney.Poincare.assumption.scaled
                            (∀ φ : Homogenization.H1Function (t • U),
                              MeasureTheory.eLpNorm
                                  (fun x => φ.toFun x -
                                    ⨍ z in SuperdiffusionCLT.Section7.whitneyInterior (t • U)
                                        ((m : ℤ) - ⌈M * Real.log (m : ℝ)⌉),
                                      φ.toFun z)
                                  2
                                  (MeasureTheory.volume.restrict
                                    (SuperdiffusionCLT.Section7.whitneyInterior (t • U)
                                      ((m : ℤ) - ⌈M * Real.log (m : ℝ)⌉))) ≤
                                ENNReal.ofReal (D * (3 : ℝ) ^ m) *
                                  MeasureTheory.eLpNorm
                                    (fun x => SuperdiffusionCLT.Section7.eucNorm (φ.grad x))
                                    2
                                    (MeasureTheory.volume.restrict
                                      (SuperdiffusionCLT.Section7.whitneyInterior (t • U)
                                        ((m : ℤ) - ⌈M * Real.log (m : ℝ)⌉)))) →
                            ∀ (f : Homogenization.Vec d → ℝ)
                              (u : Homogenization.H1Function (t • U)),
                              SuperdiffusionCLT.Section7.IsWeakSolutionOn
                                  (SuperdiffusionCLT.Section6.fullCoefficientRecentered
                                    nu omega)
                                  (t • U) u f (fun _ => 0) →
                              -- e.Dir.new.Whitney.Poincare
                              SuperdiffusionCLT.Section7.lpBar (t • U) 2
                                  (fun x => u.toFun x - ⨍ z in t • U, u.toFun z) ≤
                                ENNReal.ofReal
                                    (C * D * (3 : ℝ) ^ m *
                                      (Real.sqrt
                                        (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite
                                          nu m P))⁻¹ *
                                      Real.sqrt nu) *
                                  SuperdiffusionCLT.Section7.lpBar (t • U) 2
                                    (fun x => SuperdiffusionCLT.Section7.eucNorm (u.grad x)) +
                                ENNReal.ofReal
                                    (C * D *
                                      (3 : ℝ) ^ (2 * (m : ℝ) - (⌈M * Real.log (m : ℝ)⌉ : ℝ)) *
                                      nu⁻¹) *
                                  SuperdiffusionCLT.Section7.lpBar (t • U) 2 f
    )
    (hSigma :
      ∃ C : ℝ, 1 ≤ C ∧
        ∀ nu : ℝ, 0 < nu → nu ≤ 1 →
          ∀ cStar : ℝ, 0 < cStar →
            ∀ K : ℝ,
              ∃ M : ℕ,
                ∀ (P : MeasureTheory.ProbabilityMeasure
                      (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
                  (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
                  (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P)
                  (hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P),
                  SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P →
                  SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P →
                  SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ5 d P cStar K
                      hPrefix hJ2 hJ3 →
                    ∀ m : ℕ, M ≤ m →
                      |SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P -
                          (2 * cStar * Real.log 3 * (m : ℝ)) ^ ((1 : ℝ) / 2)| ≤
                        C * cStar⁻¹ * (Real.log (m : ℝ) ^ (2 : ℝ) + K)
    ) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ nu : ℝ, 0 < nu → nu ≤ 1 →
        ∀ cStar : ℝ, 0 < cStar →
          ∀ K ρ : ℝ, 0 < ρ → ρ < 1 →
            ∃ Lhat : ℝ, 1 ≤ Lhat ∧
              ∀ (P : MeasureTheory.ProbabilityMeasure
                    (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
                (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
                (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P)
                (hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P),
                SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P →
                SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P →
                SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ5 d P cStar K
                    hPrefix hJ2 hJ3 →
                ∃ X : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ,
                  Measurable X ∧ (∀ omega, 1 ≤ X omega) ∧
                  Homogenization.IndependentSums.IsBigO P.toMeasure
                    (Homogenization.IndependentSums.gammaSigma ρ)
                    (fun omega => Real.log (X omega)) Lhat ∧
                  ∀ᵐ omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d ∂P.toMeasure,
                    ∀ R : ℝ, X omega ≤ R →
                      ∀ (f : Homogenization.Vec d → ℝ)
                        (u : Homogenization.H1Function
                          (SuperdiffusionCLT.Section6.euclidBall (d := d) R)),
                        SuperdiffusionCLT.Section7.IsWeakSolutionOn
                            (SuperdiffusionCLT.Section6.fullCoefficientRecentered nu omega)
                            (SuperdiffusionCLT.Section6.euclidBall (d := d) R) u f
                            (fun _ => 0) →
                        SuperdiffusionCLT.Section7.lpBar
                            (SuperdiffusionCLT.Section6.euclidBall (d := d) R) 2
                            (fun x => u.toFun x -
                              ⨍ z in SuperdiffusionCLT.Section6.euclidBall (d := d) R,
                                u.toFun z) ≤
                          ENNReal.ofReal
                              (C * R * cStar ^ (-(1 / 4 : ℝ)) * Real.sqrt nu *
                                Real.log R ^ (-(1 / 4 : ℝ))) *
                            SuperdiffusionCLT.Section7.lpBar
                              (SuperdiffusionCLT.Section6.euclidBall (d := d) R) 2
                              (fun x => SuperdiffusionCLT.Section7.eucNorm (u.grad x)) +
                          ENNReal.ofReal
                              (C * R ^ 2 * nu⁻¹ * Real.log R ^ (-(100 : ℝ))) *
                            SuperdiffusionCLT.Section7.lpBar
                              (SuperdiffusionCLT.Section6.euclidBall (d := d) R) 2 f := by
  classical
  obtain ⟨hsm, hsub, D₀, T, hD₀, hT1, hWit⟩ :=
    SuperdiffusionCLT.Section7.rc_whitney_hypothesis_witness (d := d)
  obtain ⟨CW, hCW1, hCW⟩ := hWhitney _ hsm hsub
  obtain ⟨Cs, hCs1, hCs⟩ := hSigma
  have hlog3 : 1 ≤ Real.log 3 := sdPoinc_one_le_log_three
  set Mw : ℝ := max CW (max 1 (102 / Real.log 3)) with hMw
  have hMwC : CW ≤ Mw := le_max_left _ _
  have hMw1 : 1 ≤ Mw := (le_max_left _ _).trans (le_max_right _ _)
  have hMw101 : 101 ≤ Mw * Real.log 3 := by
    have h1 : 102 / Real.log 3 ≤ Mw := (le_max_right _ _).trans (le_max_right _ _)
    have h2 : 102 ≤ Mw * Real.log 3 := by
      rwa [div_le_iff₀ (by linarith only [hlog3])] at h1
    linarith only [h2]
  refine ⟨CW * D₀ * (36 * (2 : ℝ) ^ (101 : ℝ)), ?_, ?_⟩
  · have h2 : (1 : ℝ) ≤ 2 ^ (101 : ℝ) := Real.one_le_rpow (by norm_num) (by norm_num)
    have h3 : 1 ≤ CW * D₀ := one_le_mul_of_one_le_of_one_le hCW1 hD₀
    nlinarith only [h2, h3]
  intro nu hnu hnu1 cStar hc K ρ hρ0 hρ1
  obtain ⟨Msh, hMsh⟩ := hCs nu hnu hnu1 cStar hc K
  obtain ⟨m₁, hm₁, hm₁'⟩ := sdPoinc_sharp_threshold (Cs := Cs) K (by linarith only [hCs1]) hc
  obtain ⟨Lhat, hL1, hLaw⟩ := hCW nu hnu hnu1 cStar hc K ρ D₀ Mw hρ0 hρ1 hD₀ hMwC
  set m₀ : ℕ := max Msh m₁ with hm₀
  set Y : ℝ := max (max T 3) ((3 : ℝ) ^ m₀) with hY
  have hY3 : 3 ≤ Y := (le_max_right T 3).trans ((le_max_left _ _).trans le_rfl)
  have hYT : T ≤ Y := (le_max_left T 3).trans (le_max_left _ _)
  have hY3m : (3 : ℝ) ^ m₀ ≤ Y := le_max_right _ _
  have hY0 : 0 < Y := by linarith only [hY3]
  refine ⟨max Lhat (Real.log Y), ?_, ?_⟩
  · exact hL1.trans (le_max_left _ _)
  intro P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5
  obtain ⟨X, hXm, hX1, hXO, hXae⟩ := hLaw P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5
  have hexpY : Real.exp (Real.log Y) = Y := Real.exp_log hY0
  refine ⟨fun ω => max (X ω) Y, hXm.max measurable_const, fun ω => ?_, ?_, ?_⟩
  · exact (hX1 ω).trans (le_max_left _ _)
  · have := sdPoinc_isBigO_max_exp (μ := P.toMeasure) (ρ := ρ) hX1
      (Real.log_nonneg (by linarith only [hY3])) hXO
    rw [hexpY] at this
    exact this
  filter_upwards [hXae] with ω hω R hR f u hu
  have hRX : X ω ≤ R := (le_max_left _ _).trans hR
  have hRY : Y ≤ R := (le_max_right _ _).trans hR
  have hR3 : 3 ≤ R := hY3.trans hRY
  have ht1 : (1 : ℝ) ≤ 2 * R := by linarith only [hR3]
  obtain ⟨m, h3m, h2m⟩ := sdPoinc_exists_pow ht1
  have hm0m : m₀ ≤ m := by
    have h1 : (3 : ℝ) ^ m₀ ≤ (3 : ℝ) ^ m := by linarith only [hY3m, hRY, h2m, hR3]
    exact (pow_le_pow_iff_right₀ (by norm_num : (1 : ℝ) < 3)).1 h1
  have hmM : Msh ≤ m := (le_max_left _ _).trans (hm0m)
  have hmm₁ : m₁ ≤ m := (le_max_right _ _).trans (hm0m)
  have h6 : (3 : ℝ) ^ m < 6 * R := by linarith only [h3m]
  -- the diffusivity
  have hsh := hMsh P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5 m hmM
  have herr := hm₁' m hmm₁
  have hsh' : 1 / 2 * Real.sqrt (cStar * m) ≤
      SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P := by
    have hmain : Real.sqrt (cStar * m) ≤ (2 * cStar * Real.log 3 * (m : ℝ)) ^ ((1 : ℝ) / 2) := by
      rw [← Real.sqrt_eq_rpow]
      refine Real.sqrt_le_sqrt ?_
      have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      have : 0 ≤ cStar * m := by positivity
      nlinarith only [hlog3, this]
    have := (abs_le.1 hsh).1
    linarith only [this, herr, hmain]
  -- the Whitney lemma on the dilate
  have hPoinc := hWit D₀ Mw le_rfl hMw1 (2 * R) m (hYT.trans (by linarith only [hRY, hR3]))
    h3m h2m
  have hW := hω (2 * R) m (by linarith only [hRX, hR3]) h3m h2m hPoinc
  have hV : (2 * R) • SuperdiffusionCLT.Section6.euclidBall (d := d) (1 / 2) =
      SuperdiffusionCLT.Section6.euclidBall (d := d) R := by
    rw [sdPoinc_euclidBall_eq (by linarith only [hR3])]
    congr 1; ring
  rw [hV] at hW
  have hb := hW f u hu
  refine hb.trans ?_
  -- the coefficients
  have hL0 : 0 < Real.log R :=
    lt_of_lt_of_le (by linarith only [hlog3]) (hlog3.trans (Real.log_le_log (by norm_num) hR3))
  have hcf := sdPoinc_coef_first hR3 hc h2m h6 hsh'
  have hcs := sdPoinc_coef_second hR3 h2m h6 hMw101
  have hCD : 0 ≤ CW * D₀ := by nlinarith only [hCW1, hD₀]
  have hA : CW * D₀ * (3 : ℝ) ^ m *
      (Real.sqrt (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P))⁻¹ *
        Real.sqrt nu ≤ CW * D₀ * (36 * (2 : ℝ) ^ (101 : ℝ)) * R * cStar ^ (-(1 / 4 : ℝ)) *
          Real.sqrt nu * Real.log R ^ (-(1 / 4 : ℝ)) := by
    have h36 : (12 : ℝ) ≤ 36 * (2 : ℝ) ^ (101 : ℝ) := by
      have h2 : (1 : ℝ) ≤ 2 ^ (101 : ℝ) := Real.one_le_rpow (by norm_num) (by norm_num)
      linarith only [h2]
    have hp : 0 ≤ R * (cStar ^ (-(1 / 4 : ℝ)) * Real.log R ^ (-(1 / 4 : ℝ))) * Real.sqrt nu := by
      positivity
    calc CW * D₀ * (3 : ℝ) ^ m *
          (Real.sqrt (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P))⁻¹ *
            Real.sqrt nu
        = CW * D₀ * ((3 : ℝ) ^ m *
          (Real.sqrt (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P))⁻¹) *
            Real.sqrt nu := by ring
      _ ≤ CW * D₀ * (12 * R * (cStar ^ (-(1 / 4 : ℝ)) * Real.log R ^ (-(1 / 4 : ℝ)))) *
            Real.sqrt nu := by gcongr
      _ = CW * D₀ * 12 * (R * (cStar ^ (-(1 / 4 : ℝ)) * Real.log R ^ (-(1 / 4 : ℝ))) *
            Real.sqrt nu) := by ring
      _ ≤ CW * D₀ * (36 * (2 : ℝ) ^ (101 : ℝ)) * (R * (cStar ^ (-(1 / 4 : ℝ)) *
            Real.log R ^ (-(1 / 4 : ℝ))) * Real.sqrt nu) := by gcongr
      _ = _ := by ring
  have hB : CW * D₀ * (3 : ℝ) ^ (2 * (m : ℝ) - (⌈Mw * Real.log (m : ℝ)⌉ : ℝ)) * nu⁻¹ ≤
      CW * D₀ * (36 * (2 : ℝ) ^ (101 : ℝ)) * R ^ 2 * nu⁻¹ * Real.log R ^ (-(100 : ℝ)) := by
    have hninv : 0 ≤ nu⁻¹ := by positivity
    calc CW * D₀ * (3 : ℝ) ^ (2 * (m : ℝ) - (⌈Mw * Real.log (m : ℝ)⌉ : ℝ)) * nu⁻¹
        ≤ CW * D₀ * (36 * (2 : ℝ) ^ (101 : ℝ) * R ^ 2 * Real.log R ^ (-(100 : ℝ))) * nu⁻¹ := by
          gcongr
      _ = _ := by ring
  gcongr

/-- Witness for the non-law hypotheses of `sdPoinc_superdiffusive_poincare`: the zero function
is a weak solution with right-hand side `0` on every ball, whatever the scale `R ≥ X`. -/
example (d : ℕ) [NeZero d] (nu : ℝ) (omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d) (X R : ℝ)
    (hR : max X 3 ≤ R) :
    X ≤ R ∧ SuperdiffusionCLT.Section7.IsWeakSolutionOn
      (SuperdiffusionCLT.Section6.fullCoefficientRecentered nu omega)
      (SuperdiffusionCLT.Section6.euclidBall (d := d) R)
      (0 : Homogenization.H1Function (SuperdiffusionCLT.Section6.euclidBall (d := d) R))
      (fun _ => 0) (fun _ => 0) := by
  refine ⟨(le_max_left _ _).trans hR, fun φ => ?_⟩
  simp [Homogenization.matVecMul, Homogenization.vecDot]

end SuperdiffusionCLT.Section8

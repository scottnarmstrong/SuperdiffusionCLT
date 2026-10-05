/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Prereq.WhitneyLocalC
public import SuperdiffusionCLT.Section7.Analytic.Change.SkewShift
public import SuperdiffusionCLT.Section7.Prereq.DomainInvariance
public import SuperdiffusionCLT.Section7.Prereq.WellPosed
public import SuperdiffusionCLT.Section6.Engine.WitnessLaplace
public import SuperdiffusionCLT.Section7.Prereq.RhsLemmaC

/-!
# The almost-sure local oscillation estimate for the Whitney Poincare lemma

The field enters.  For a weak solution `u` of `-∇·(ã ∇u) = f` on a set `W ⊆ □_m` (`ã` the recentered
field), on the good event of the minimal scale (the sharp-scale inputs of
`l.Dirichlet.rhs.blackbox`, taken as the hypothesis `hInputs` as in `r1_rhs_blackbox`), the squared
oscillation of `u` about its average on every cube `3^{n-3} k + □_n ⊆ W`, `m - ⌈M log m⌉ ≤ n ≤ m`,
is bounded by the weak gradient bound (the dual bullet of the right-hand side lemma, transferred to
the recentered field by the skew shift and the translation of the solution) combined with the dual
fractional Poincare inequality.

* `wh2_ae_local`: one cube, every grid point (the translate used is `y = 0`: the domain lies in
  `□_m`, so one ambient cube serves the whole grid).
* `wh2_ae_sum`: the sum over a finite family of grid cubes, with the bounded overlap `27^d`; the
  squared form that plugs into the global gradient estimate.
* `wh2_ae_whitney`: the same on `t • U`, `3^{m-1} < t ≤ 3^m`, with the mesoscale
  `j = m - ⌈M log m⌉`, `n = j + 3` of `l.Dirichlet.Whitney.Poincare`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal
open scoped Matrix.Norms.L2Operator
open scoped Pointwise

namespace SuperdiffusionCLT.Section7

open Homogenization

variable {d : ℕ}

theorem wh2_translateSequence_zero (omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d) :
    SuperdiffusionCLT.Frozen.Assumptions.ShellField.translateSequence 0 omega = omega := by
  funext n
  apply SuperdiffusionCLT.Frozen.Assumptions.ShellField.ext
  intro x
  simp

theorem wh2_isEllipticFieldOn_mono {lam Lam : ℝ} {U V : Set (Vec d)} {a : CoeffField d}
    (hV : MeasurableSet V) (hVU : V ⊆ U) (h : IsEllipticFieldOn lam Lam U a) :
    IsEllipticFieldOn lam Lam V a := by
  classical
  refine ⟨?_, fun x hx => h.2 x (hVU hx)⟩
  have h1 := h.1
  have : (fun x i j => if x ∈ V then a x i j else 0) =
      fun x => if x ∈ V then (fun i j => if x ∈ U then a x i j else 0) else 0 := by
    funext x i j
    by_cases hx : x ∈ V
    · simp [hx, hVU hx]
    · simp [hx]
  rw [this]
  exact Measurable.ite hV h1 measurable_const

theorem wh2_conj_le_two (hd : 2 ≤ d) : (ENNReal.ofReal (sobStar d)).conjExponent ≤ 2 := by
  have hp : (2 : ℝ≥0∞) ≤ ENNReal.ofReal (sobStar d) := by
    have := ENNReal.ofReal_le_ofReal (two_lt_sobStar hd).le
    simpa only [ENNReal.ofNat_le_ofReal, ge_iff_le, ENNReal.ofReal_ofNat] using this
  have h1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (sobStar d) - 1 := by
    refine ENNReal.le_sub_of_add_le_right ENNReal.one_ne_top ?_
    rw [one_add_one_eq_two]
    exact hp
  have h2 : (ENNReal.ofReal (sobStar d) - 1)⁻¹ ≤ 1 := ENNReal.inv_le_one.2 h1
  unfold ENNReal.conjExponent
  calc 1 + (ENNReal.ofReal (sobStar d) - 1)⁻¹ ≤ 1 + 1 := by gcongr
    _ = 2 := one_add_one_eq_two

/-- **The almost-sure local oscillation estimate on every translated cube.** -/
theorem wh2_ae_local (d : ℕ) [NeZero d] (hd : 2 ≤ d)
    (hInputs :
        ∃ C : ℝ, 1 ≤ C ∧ ∀ nu : ℝ, 0 < nu → nu ≤ 1 → ∀ cStar : ℝ, 0 < cStar → ∀ K : ℝ, ∀ ε ρ M : ℝ,
          0 < ε → ε ≤ 1 → 0 < ρ → ρ < 1 → C ≤ M → ∃ Lhat : ℝ, 1 ≤ Lhat ∧ ∀ (P :
          MeasureTheory.ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
          (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P) (hJ2 :
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P) (hJ3 :
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P),
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P →
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P →
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ5 d P cStar K hPrefix hJ2 hJ3 → ∃ X0 :
          SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ, Measurable X0 ∧ (∀ omega, 1 ≤ X0
          omega) ∧ Homogenization.IndependentSums.IsBigO P.toMeasure
          (Homogenization.IndependentSums.gammaSigma ρ) (fun omega => Real.log (X0 omega)) Lhat ∧ ∀ᵐ
          omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d ∂P.toMeasure, ∀ m n : ℕ, X0
          omega ≤ (3 : ℝ) ^ m → Lhat ≤ (m : ℝ) → (m : ℤ) - ⌈M * Real.log (m : ℝ)⌉ ≤ (n : ℤ) → n ≤ m
          → (∀ k : Fin d → ℤ, (fun x => (fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x) ''
          Homogenization.cubeSet (Homogenization.originCube d (n : ℤ)) ⊆ Homogenization.cubeSet
          (Homogenization.originCube d (m : ℤ)) → Homogenization.HomogenizationErrorOnCube
          (Homogenization.originCube d (n : ℤ)) (1 / 9) Homogenization.MultiscaleExponent.infinity
          (Homogenization.MultiscaleExponent.finite 2) (fun x => nu • (1 : Homogenization.Mat d) +
          SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega (Homogenization.cubeSet
          (Homogenization.originCube d (m : ℤ))) ((fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) +
          x)) (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P • (1 :
          Homogenization.Mat d)) ≤ ε * (m : ℝ) ^ (-((1 - ρ) / 2)) * Real.log (m : ℝ) ∧
          (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P)⁻¹ *
          Homogenization.LambdaSq (Homogenization.originCube d (n : ℤ)) (1 / 4)
          (Homogenization.MultiscaleExponent.finite 1) (fun x => nu • (1 : Homogenization.Mat d) +
          SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega (Homogenization.cubeSet
          (Homogenization.originCube d (m : ℤ))) ((fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) +
          x)) + SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P *
          (Homogenization.lambdaSq (Homogenization.originCube d (n : ℤ)) (1 / 4)
          (Homogenization.MultiscaleExponent.finite 1) (fun x => nu • (1 : Homogenization.Mat d) +
          SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega (Homogenization.cubeSet
          (Homogenization.originCube d (m : ℤ))) ((fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) +
          x)))⁻¹ ≤ C ∧ (∀ u : Homogenization.AHarmonicFunction (fun x => nu • (1 :
          Homogenization.Mat d) + SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega
          (Homogenization.cubeSet (Homogenization.originCube d (m : ℤ))) ((fun i => (3 : ℝ) ^ ((n :
          ℤ) - 3) * (k i : ℝ)) + x)) (Homogenization.openCubeSet (Homogenization.originCube d (n :
          ℤ))), ENNReal.ofReal
          (Homogenization.Book.Ch03.scaleNormalizedDualNegativeBesovVectorNormTwo
          (Homogenization.originCube d (n : ℤ)) (1 / 4) (fun x => Homogenization.matVecMul (nu • (1
          : Homogenization.Mat d) + SuperdiffusionCLT.Section2.Carriers.centeredStreamField
          omega (Homogenization.cubeSet (Homogenization.originCube d (m : ℤ))) ((fun i => (3 : ℝ) ^
          ((n : ℤ) - 3) * (k i : ℝ)) + x) -
          SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P • (1 : Homogenization.Mat
          d)) (u.toH1.grad x))) ≤ ENNReal.ofReal (C * Real.sqrt
          (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P) * (ε * (m : ℝ) ^ (-((1
          - ρ) / 2)) * Real.log (m : ℝ)) * Real.sqrt nu) *
          SuperdiffusionCLT.Section2.Norms.cubeLpENorm (Homogenization.originCube d (n : ℤ)) 2
          (fun x => Real.sqrt (Homogenization.vecNormSq (u.toH1.grad x))) ∧ ENNReal.ofReal
          (Homogenization.Book.Ch03.scaleNormalizedDualNegativeBesovVectorNormTwo
          (Homogenization.originCube d (n : ℤ)) (1 / 4) u.toH1.grad) ≤ ENNReal.ofReal (C *
          (Real.sqrt (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P))⁻¹ *
          Real.sqrt nu) * SuperdiffusionCLT.Section2.Norms.cubeLpENorm
          (Homogenization.originCube d (n : ℤ)) 2 (fun x => Real.sqrt (Homogenization.vecNormSq
          (u.toH1.grad x))) ∧ ∃ w : Homogenization.AHarmonicFunction (fun _ => (1 :
          Homogenization.Mat d)) (Homogenization.openCubeSet (Homogenization.originCube d ((n : ℤ) -
          1))), ENNReal.ofReal ((3 : ℝ) ^ (-(n : ℝ))) *
          SuperdiffusionCLT.Section2.Norms.cubeLpENorm (Homogenization.originCube d ((n : ℤ) -
          1)) 2 (fun x => u.toH1.toFun x - w.toH1.toFun x) ≤ ENNReal.ofReal (C * (ε * (m : ℝ) ^
          (-((1 - ρ) / 2)) * Real.log (m : ℝ)) * (Real.sqrt
          (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P))⁻¹ * Real.sqrt nu) *
          SuperdiffusionCLT.Section2.Norms.cubeLpENorm (Homogenization.originCube d (n : ℤ)) 2
          (fun x => Real.sqrt (Homogenization.vecNormSq (u.toH1.grad x)))) ∧ Homogenization.matNorm
          ((SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P)⁻¹ •
          Homogenization.sigmaCoarse (Homogenization.cubeSet (Homogenization.originCube d (n : ℤ)))
          (fun x => nu • (1 : Homogenization.Mat d) +
          SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega (Homogenization.cubeSet
          (Homogenization.originCube d (m : ℤ))) ((fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) +
          x)) - 1) + Homogenization.matNorm
          ((SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P)⁻¹ •
          Homogenization.sigmaStarCoarse (Homogenization.cubeSet (Homogenization.originCube d (n :
          ℤ))) (fun x => nu • (1 : Homogenization.Mat d) +
          SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega (Homogenization.cubeSet
          (Homogenization.originCube d (m : ℤ))) ((fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) +
          x)) - 1) ≤ C * (ε * (m : ℝ) ^ (-((1 - ρ) / 2)) * Real.log (m : ℝ))) ∧ ENNReal.ofReal ((m :
          ℝ)⁻¹) * SuperdiffusionCLT.Section2.Norms.cubeLpENorm (Homogenization.originCube d (m
          : ℤ)) ∞ (SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega
          (Homogenization.cubeSet (Homogenization.originCube d (m : ℤ)))) + ENNReal.ofReal ((3 : ℝ)
          ^ (-((1 / 4 : ℝ) * (m : ℝ)))) * SuperdiffusionCLT.Section2.Norms.matHatNegENorm
          (Homogenization.originCube d (m : ℤ)) (1 / 4) 2
          (SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega
          (Homogenization.cubeSet (Homogenization.originCube d (m : ℤ)))) ≤ ENNReal.ofReal ((m : ℝ)
          ^ ρ)) :
    ∃ C Cp : ℝ, 1 ≤ C ∧ 0 < Cp ∧ ∀ nu : ℝ, 0 < nu → nu ≤ 1 → ∀ cStar : ℝ, 0 < cStar → ∀ K : ℝ,
      ∀ ρ M : ℝ, 0 < ρ → ρ < 1 → C ≤ M → ∃ Lhat : ℝ, 1 ≤ Lhat ∧
        ∀ (P : MeasureTheory.ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
          (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
          (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P)
          (hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P),
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P →
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P →
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ5 d P cStar K hPrefix hJ2 hJ3 →
          ∃ X0 : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ, Measurable X0 ∧
            (∀ omega, 1 ≤ X0 omega) ∧
            Homogenization.IndependentSums.IsBigO P.toMeasure
              (Homogenization.IndependentSums.gammaSigma ρ) (fun omega => Real.log (X0 omega))
              Lhat ∧
            ∀ᵐ omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d ∂P.toMeasure,
              ∀ m n : ℕ, X0 omega ≤ (3 : ℝ) ^ m → Lhat ≤ (m : ℝ) →
                (m : ℤ) - ⌈M * Real.log (m : ℝ)⌉ ≤ (n : ℤ) → n ≤ m →
                ∀ W : Set (Vec d), W ⊆ openCubeSet (originCube d (m : ℤ)) →
                  ∀ (u : H1Function W) (f : Vec d → ℝ), AEMeasurable f (volume.restrict W) →
                    IsWeakSolutionOn (SuperdiffusionCLT.Section6.fullCoefficientRecentered nu omega)
                      W u f (fun _ => 0) →
                    ∀ (k : Fin d → ℤ) (z : Vec d),
                      z = (fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) →
                      translateSet z (openCubeSet (originCube d (n : ℤ))) ⊆ W →
                      ∫⁻ x in translateSet z (openCubeSet (originCube d (n : ℤ))),
                          ENNReal.ofReal
                            ((u.toFun x - cubeAverage (originCube d (n : ℤ))
                              (fun y => u.toFun (y + z))) ^ 2) ≤
                        2 * ENNReal.ofReal (Cp * (3 : ℝ) ^ n) ^ 2 *
                          (ENNReal.ofReal
                              (C * (Real.sqrt
                                (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P))⁻¹ *
                                Real.sqrt nu) ^ 2 *
                              (∫⁻ x in translateSet z (openCubeSet (originCube d (n : ℤ))),
                                ENNReal.ofReal (eucNorm (u.grad x) ^ 2)) +
                            ENNReal.ofReal
                              ((C * (Real.sqrt
                                (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P))⁻¹ *
                                Real.sqrt nu + C) * (C * (3 : ℝ) ^ (n : ℤ) / nu)) ^ 2 *
                              ∫⁻ x in translateSet z (openCubeSet (originCube d (n : ℤ))),
                                ENNReal.ofReal (f x ^ 2)) := by
  obtain ⟨C, hC, H⟩ := r1_rhs_blackbox d hd hInputs
  obtain ⟨Cp, hCp, hOsc⟩ := wh2_osc_cube d
  refine ⟨C, Cp, hC, hCp, ?_⟩
  intro nu hnu hnu1 cStar hcStar K ρ M hρ hρ1 hCM
  obtain ⟨Lhat, hL, H2⟩ := H nu hnu hnu1 cStar hcStar K 1 ρ M one_pos le_rfl hρ hρ1 hCM
  refine ⟨Lhat, hL, fun P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5 => ?_⟩
  obtain ⟨X0, hm, h1, hO, hae⟩ := H2 P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5
  refine ⟨X0, hm, h1, hO, ?_⟩
  filter_upwards [hae 0, SuperdiffusionCLT.Section6.ae_centered_eq_recentered_add_skew hJ3 nu,
    SuperdiffusionCLT.Section6.l9_ae_exists_ell_centered hJ3 hnu] with omega hω hskew hell
  intro m n hX hLm hn1 hn2 W hWm u f hf hsol k z hz hzW
  have hX0 : X0 (SuperdiffusionCLT.Frozen.Assumptions.ShellField.translateSequence 0 omega) ≤
      (3 : ℝ) ^ m := by rwa [wh2_translateSequence_zero]
  have hzm : translateSet z (openCubeSet (originCube d (n : ℤ))) ⊆
      openCubeSet (originCube d (m : ℤ)) := hzW.trans hWm
  have himg := wh2_shift_image_subset n m z hzm
  have himg' : (fun x => (fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x) ''
      cubeSet (originCube d (n : ℤ)) ⊆ cubeSet (originCube d (m : ℤ)) := by
    rw [← hz]
    exact himg
  have hbul := hω m n hX0 hLm hn1 hn2 k himg'
  rw [← hz] at hbul
  obtain ⟨Ks, hKs, hKx⟩ := hskew m
  obtain ⟨lam, Lam, hl⟩ := hell m n z
  have hell' : IsEllipticFieldOn lam Lam (openCubeSet (originCube d (n : ℤ)))
      (fun x => nu • (1 : Mat d) +
        SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega
          (cubeSet (originCube d (m : ℤ))) (z + x)) :=
    wh2_isEllipticFieldOn_mono (isOpen_openCubeSet _).measurableSet (openCubeSet_subset_cubeSet _) hl
  have hfin : IsFiniteMeasure (volumeMeasureOn (openCubeSet (originCube d (n : ℤ)))) :=
    ⟨by
      simpa only [volumeMeasureOn, MeasurableSet.univ, Measure.restrict_apply, Set.univ_inter] using
        (isBounded_openCubeSet (originCube d (n : ℤ))).measure_lt_top⟩
  refine hOsc n z hzW hf hsol (a' := fun x => nu • (1 : Mat d) +
    SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega
      (translateSet 0 (cubeSet (originCube d (m : ℤ)))) (0 + z + x)) ?_
    (C * (Real.sqrt (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P))⁻¹ *
      Real.sqrt nu) ((C * (Real.sqrt (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P))⁻¹ *
        Real.sqrt nu + C) * (C * (3 : ℝ) ^ (n : ℤ) / nu))
    (ENNReal.ofReal (sobStar d)).conjExponent (wh2_conj_le_two hd) ?_
  · intro v g hv
    have := hfin
    have hab : ∀ x, (nu • (1 : Mat d) +
        SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega
          (translateSet 0 (cubeSet (originCube d (m : ℤ)))) (0 + z + x)) =
        SuperdiffusionCLT.Section6.fullCoefficientRecentered nu omega (x + z) + Ks := by
      intro x
      rw [translateSet_zero, zero_add, hKx (z + x), add_comm z x]
    have hA : MemVectorL2 (openCubeSet (originCube d (n : ℤ)))
        (fun x => matVecMul (nu • (1 : Mat d) +
          SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega
            (cubeSet (originCube d (m : ℤ))) (z + x)) (v.grad x)) :=
      memVectorL2_matVecMul_of_isEllipticFieldOn hell' v.grad_memVectorL2
    have hflux : MemVectorL2 (openCubeSet (originCube d (n : ℤ)))
        (fun x => matVecMul
          (SuperdiffusionCLT.Section6.fullCoefficientRecentered nu omega (x + z)) (v.grad x)) := by
      have h2 := hA.sub (SuperdiffusionCLT.Section2.CoarseGraining.memVectorL2_matVecMul_const Ks
        v.grad_memVectorL2)
      have e : (fun x => matVecMul
          (SuperdiffusionCLT.Section6.fullCoefficientRecentered nu omega (x + z)) (v.grad x)) =
          ((fun x => matVecMul (nu • (1 : Mat d) +
          SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega
            (cubeSet (originCube d (m : ℤ))) (z + x)) (v.grad x)) -
          fun x => matVecMul Ks (v.grad x)) := by
        funext x
        rw [Pi.sub_apply, hKx (z + x), add_comm z x, add_matVecMul]
        abel
      rw [e]
      exact h2
    exact (isWeakSolutionOn_congr_const_skew (isOpen_openCubeSet _) hKs
      (a := fun x => SuperdiffusionCLT.Section6.fullCoefficientRecentered nu omega (x + z))
      (b := fun x => nu • (1 : Mat d) +
        SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega
          (translateSet 0 (cubeSet (originCube d (m : ℤ)))) (0 + z + x)) hab hflux).2 hv
  · intro v g hv
    exact (hbul v g hv).2

/-- **The almost-sure summed local oscillation estimate.** -/
theorem wh2_ae_sum (d : ℕ) [NeZero d] (hd : 2 ≤ d)
    (hInputs :
        ∃ C : ℝ, 1 ≤ C ∧ ∀ nu : ℝ, 0 < nu → nu ≤ 1 → ∀ cStar : ℝ, 0 < cStar → ∀ K : ℝ, ∀ ε ρ M : ℝ,
          0 < ε → ε ≤ 1 → 0 < ρ → ρ < 1 → C ≤ M → ∃ Lhat : ℝ, 1 ≤ Lhat ∧ ∀ (P :
          MeasureTheory.ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
          (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P) (hJ2 :
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P) (hJ3 :
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P),
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P →
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P →
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ5 d P cStar K hPrefix hJ2 hJ3 → ∃ X0 :
          SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ, Measurable X0 ∧ (∀ omega, 1 ≤ X0
          omega) ∧ Homogenization.IndependentSums.IsBigO P.toMeasure
          (Homogenization.IndependentSums.gammaSigma ρ) (fun omega => Real.log (X0 omega)) Lhat ∧ ∀ᵐ
          omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d ∂P.toMeasure, ∀ m n : ℕ, X0
          omega ≤ (3 : ℝ) ^ m → Lhat ≤ (m : ℝ) → (m : ℤ) - ⌈M * Real.log (m : ℝ)⌉ ≤ (n : ℤ) → n ≤ m
          → (∀ k : Fin d → ℤ, (fun x => (fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x) ''
          Homogenization.cubeSet (Homogenization.originCube d (n : ℤ)) ⊆ Homogenization.cubeSet
          (Homogenization.originCube d (m : ℤ)) → Homogenization.HomogenizationErrorOnCube
          (Homogenization.originCube d (n : ℤ)) (1 / 9) Homogenization.MultiscaleExponent.infinity
          (Homogenization.MultiscaleExponent.finite 2) (fun x => nu • (1 : Homogenization.Mat d) +
          SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega (Homogenization.cubeSet
          (Homogenization.originCube d (m : ℤ))) ((fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) +
          x)) (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P • (1 :
          Homogenization.Mat d)) ≤ ε * (m : ℝ) ^ (-((1 - ρ) / 2)) * Real.log (m : ℝ) ∧
          (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P)⁻¹ *
          Homogenization.LambdaSq (Homogenization.originCube d (n : ℤ)) (1 / 4)
          (Homogenization.MultiscaleExponent.finite 1) (fun x => nu • (1 : Homogenization.Mat d) +
          SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega (Homogenization.cubeSet
          (Homogenization.originCube d (m : ℤ))) ((fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) +
          x)) + SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P *
          (Homogenization.lambdaSq (Homogenization.originCube d (n : ℤ)) (1 / 4)
          (Homogenization.MultiscaleExponent.finite 1) (fun x => nu • (1 : Homogenization.Mat d) +
          SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega (Homogenization.cubeSet
          (Homogenization.originCube d (m : ℤ))) ((fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) +
          x)))⁻¹ ≤ C ∧ (∀ u : Homogenization.AHarmonicFunction (fun x => nu • (1 :
          Homogenization.Mat d) + SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega
          (Homogenization.cubeSet (Homogenization.originCube d (m : ℤ))) ((fun i => (3 : ℝ) ^ ((n :
          ℤ) - 3) * (k i : ℝ)) + x)) (Homogenization.openCubeSet (Homogenization.originCube d (n :
          ℤ))), ENNReal.ofReal
          (Homogenization.Book.Ch03.scaleNormalizedDualNegativeBesovVectorNormTwo
          (Homogenization.originCube d (n : ℤ)) (1 / 4) (fun x => Homogenization.matVecMul (nu • (1
          : Homogenization.Mat d) + SuperdiffusionCLT.Section2.Carriers.centeredStreamField
          omega (Homogenization.cubeSet (Homogenization.originCube d (m : ℤ))) ((fun i => (3 : ℝ) ^
          ((n : ℤ) - 3) * (k i : ℝ)) + x) -
          SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P • (1 : Homogenization.Mat
          d)) (u.toH1.grad x))) ≤ ENNReal.ofReal (C * Real.sqrt
          (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P) * (ε * (m : ℝ) ^ (-((1
          - ρ) / 2)) * Real.log (m : ℝ)) * Real.sqrt nu) *
          SuperdiffusionCLT.Section2.Norms.cubeLpENorm (Homogenization.originCube d (n : ℤ)) 2
          (fun x => Real.sqrt (Homogenization.vecNormSq (u.toH1.grad x))) ∧ ENNReal.ofReal
          (Homogenization.Book.Ch03.scaleNormalizedDualNegativeBesovVectorNormTwo
          (Homogenization.originCube d (n : ℤ)) (1 / 4) u.toH1.grad) ≤ ENNReal.ofReal (C *
          (Real.sqrt (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P))⁻¹ *
          Real.sqrt nu) * SuperdiffusionCLT.Section2.Norms.cubeLpENorm
          (Homogenization.originCube d (n : ℤ)) 2 (fun x => Real.sqrt (Homogenization.vecNormSq
          (u.toH1.grad x))) ∧ ∃ w : Homogenization.AHarmonicFunction (fun _ => (1 :
          Homogenization.Mat d)) (Homogenization.openCubeSet (Homogenization.originCube d ((n : ℤ) -
          1))), ENNReal.ofReal ((3 : ℝ) ^ (-(n : ℝ))) *
          SuperdiffusionCLT.Section2.Norms.cubeLpENorm (Homogenization.originCube d ((n : ℤ) -
          1)) 2 (fun x => u.toH1.toFun x - w.toH1.toFun x) ≤ ENNReal.ofReal (C * (ε * (m : ℝ) ^
          (-((1 - ρ) / 2)) * Real.log (m : ℝ)) * (Real.sqrt
          (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P))⁻¹ * Real.sqrt nu) *
          SuperdiffusionCLT.Section2.Norms.cubeLpENorm (Homogenization.originCube d (n : ℤ)) 2
          (fun x => Real.sqrt (Homogenization.vecNormSq (u.toH1.grad x)))) ∧ Homogenization.matNorm
          ((SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P)⁻¹ •
          Homogenization.sigmaCoarse (Homogenization.cubeSet (Homogenization.originCube d (n : ℤ)))
          (fun x => nu • (1 : Homogenization.Mat d) +
          SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega (Homogenization.cubeSet
          (Homogenization.originCube d (m : ℤ))) ((fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) +
          x)) - 1) + Homogenization.matNorm
          ((SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P)⁻¹ •
          Homogenization.sigmaStarCoarse (Homogenization.cubeSet (Homogenization.originCube d (n :
          ℤ))) (fun x => nu • (1 : Homogenization.Mat d) +
          SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega (Homogenization.cubeSet
          (Homogenization.originCube d (m : ℤ))) ((fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) +
          x)) - 1) ≤ C * (ε * (m : ℝ) ^ (-((1 - ρ) / 2)) * Real.log (m : ℝ))) ∧ ENNReal.ofReal ((m :
          ℝ)⁻¹) * SuperdiffusionCLT.Section2.Norms.cubeLpENorm (Homogenization.originCube d (m
          : ℤ)) ∞ (SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega
          (Homogenization.cubeSet (Homogenization.originCube d (m : ℤ)))) + ENNReal.ofReal ((3 : ℝ)
          ^ (-((1 / 4 : ℝ) * (m : ℝ)))) * SuperdiffusionCLT.Section2.Norms.matHatNegENorm
          (Homogenization.originCube d (m : ℤ)) (1 / 4) 2
          (SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega
          (Homogenization.cubeSet (Homogenization.originCube d (m : ℤ)))) ≤ ENNReal.ofReal ((m : ℝ)
          ^ ρ)) :
    ∃ C Cp : ℝ, 1 ≤ C ∧ 0 < Cp ∧ ∀ nu : ℝ, 0 < nu → nu ≤ 1 → ∀ cStar : ℝ, 0 < cStar → ∀ K : ℝ,
      ∀ ρ M : ℝ, 0 < ρ → ρ < 1 → C ≤ M → ∃ Lhat : ℝ, 1 ≤ Lhat ∧
        ∀ (P : MeasureTheory.ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
          (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
          (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P)
          (hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P),
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P →
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P →
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ5 d P cStar K hPrefix hJ2 hJ3 →
          ∃ X0 : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ, Measurable X0 ∧
            (∀ omega, 1 ≤ X0 omega) ∧
            Homogenization.IndependentSums.IsBigO P.toMeasure
              (Homogenization.IndependentSums.gammaSigma ρ) (fun omega => Real.log (X0 omega))
              Lhat ∧
            ∀ᵐ omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d ∂P.toMeasure,
              ∀ m n : ℕ, X0 omega ≤ (3 : ℝ) ^ m → Lhat ≤ (m : ℝ) →
                (m : ℤ) - ⌈M * Real.log (m : ℝ)⌉ ≤ (n : ℤ) → n ≤ m →
                ∀ W : Set (Vec d), W ⊆ openCubeSet (originCube d (m : ℤ)) →
                  ∀ (u : H1Function W) (f : Vec d → ℝ), AEMeasurable f (volume.restrict W) →
                    IsWeakSolutionOn (SuperdiffusionCLT.Section6.fullCoefficientRecentered nu omega)
                      W u f (fun _ => 0) →
                    ∀ Z : Finset (Fin d → ℤ), (∀ k ∈ Z, wh2_B n k ⊆ W) →
                      ∑ k ∈ Z, wh1_osc ((3 : ℝ) ^ ((n : ℤ) - 3)) (27 * (3 : ℝ) ^ ((n : ℤ) - 3) / 2)
                          u.toFun (fun k => cubeAverage (originCube d (n : ℤ))
                            (fun y => u.toFun (y + fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)))) k ≤
                        27 ^ d * (2 * ENNReal.ofReal (Cp * (3 : ℝ) ^ n) ^ 2 *
                          (ENNReal.ofReal
                              (C * (Real.sqrt
                                (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P))⁻¹ *
                                Real.sqrt nu) ^ 2 *
                              (∫⁻ x in W, ENNReal.ofReal (eucNorm (u.grad x) ^ 2)) +
                            ENNReal.ofReal
                              ((C * (Real.sqrt
                                (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P))⁻¹ *
                                Real.sqrt nu + C) * (C * (3 : ℝ) ^ (n : ℤ) / nu)) ^ 2 *
                              ∫⁻ x in W, ENNReal.ofReal (f x ^ 2))) := by
  obtain ⟨C, Cp, hC, hCp, H⟩ := wh2_ae_local d hd hInputs
  refine ⟨C, Cp, hC, hCp, ?_⟩
  intro nu hnu hnu1 cStar hcStar K ρ M hρ hρ1 hCM
  obtain ⟨Lhat, hL, H2⟩ := H nu hnu hnu1 cStar hcStar K ρ M hρ hρ1 hCM
  refine ⟨Lhat, hL, fun P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5 => ?_⟩
  obtain ⟨X0, hm, h1, hO, hae⟩ := H2 P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5
  refine ⟨X0, hm, h1, hO, ?_⟩
  filter_upwards [hae] with omega hω
  intro m n hX hLm hn1 hn2 W hWm u f hf hsol Z hZ
  have hG : AEMeasurable (fun x => ENNReal.ofReal (eucNorm (u.grad x) ^ 2)) (volume.restrict W) :=
    ((wh2_aemeasurable_eucNorm u).pow_const 2).ennreal_ofReal
  have hF : AEMeasurable (fun x => ENNReal.ofReal (f x ^ 2)) (volume.restrict W) :=
    (hf.pow_const 2).ennreal_ofReal
  refine wh2_sum_osc_le n Z hZ hG hF u.toFun _ _ _ _ (fun k hk => ?_)
  have := hω m n hX hLm hn1 hn2 W hWm u f hf hsol k _ rfl (hZ k hk)
  unfold wh1_osc
  rw [wh2_box_eq]
  exact this

/-- **The local oscillation estimate on the grid cubes of a dilated domain** (the oscillation chain
of `l.Dirichlet.Whitney.Poincare`, in the
dilation parameter `t` of the statement): on the event `X ≤ t`, `3^{m-1} < t ≤ 3^m`, with
the mesoscale `j = m - ⌈M log m⌉`, `n = j + 3`, a weak solution of the recentered field on `t • U`
satisfies, for every finite family `Z` of grid points `3^j k` whose cubes `3^j k + □_{j+3}` lie in
`t • U`, the summed oscillation estimate against the gradient and right-hand side on `t • U`. -/
theorem wh2_ae_whitney (d : ℕ) [NeZero d] (hd : 2 ≤ d)
    (hInputs :
        ∃ C : ℝ, 1 ≤ C ∧ ∀ nu : ℝ, 0 < nu → nu ≤ 1 → ∀ cStar : ℝ, 0 < cStar → ∀ K : ℝ, ∀ ε ρ M : ℝ,
          0 < ε → ε ≤ 1 → 0 < ρ → ρ < 1 → C ≤ M → ∃ Lhat : ℝ, 1 ≤ Lhat ∧ ∀ (P :
          MeasureTheory.ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
          (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P) (hJ2 :
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P) (hJ3 :
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P),
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P →
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P →
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ5 d P cStar K hPrefix hJ2 hJ3 → ∃ X0 :
          SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ, Measurable X0 ∧ (∀ omega, 1 ≤ X0
          omega) ∧ Homogenization.IndependentSums.IsBigO P.toMeasure
          (Homogenization.IndependentSums.gammaSigma ρ) (fun omega => Real.log (X0 omega)) Lhat ∧ ∀ᵐ
          omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d ∂P.toMeasure, ∀ m n : ℕ, X0
          omega ≤ (3 : ℝ) ^ m → Lhat ≤ (m : ℝ) → (m : ℤ) - ⌈M * Real.log (m : ℝ)⌉ ≤ (n : ℤ) → n ≤ m
          → (∀ k : Fin d → ℤ, (fun x => (fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x) ''
          Homogenization.cubeSet (Homogenization.originCube d (n : ℤ)) ⊆ Homogenization.cubeSet
          (Homogenization.originCube d (m : ℤ)) → Homogenization.HomogenizationErrorOnCube
          (Homogenization.originCube d (n : ℤ)) (1 / 9) Homogenization.MultiscaleExponent.infinity
          (Homogenization.MultiscaleExponent.finite 2) (fun x => nu • (1 : Homogenization.Mat d) +
          SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega (Homogenization.cubeSet
          (Homogenization.originCube d (m : ℤ))) ((fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) +
          x)) (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P • (1 :
          Homogenization.Mat d)) ≤ ε * (m : ℝ) ^ (-((1 - ρ) / 2)) * Real.log (m : ℝ) ∧
          (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P)⁻¹ *
          Homogenization.LambdaSq (Homogenization.originCube d (n : ℤ)) (1 / 4)
          (Homogenization.MultiscaleExponent.finite 1) (fun x => nu • (1 : Homogenization.Mat d) +
          SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega (Homogenization.cubeSet
          (Homogenization.originCube d (m : ℤ))) ((fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) +
          x)) + SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P *
          (Homogenization.lambdaSq (Homogenization.originCube d (n : ℤ)) (1 / 4)
          (Homogenization.MultiscaleExponent.finite 1) (fun x => nu • (1 : Homogenization.Mat d) +
          SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega (Homogenization.cubeSet
          (Homogenization.originCube d (m : ℤ))) ((fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) +
          x)))⁻¹ ≤ C ∧ (∀ u : Homogenization.AHarmonicFunction (fun x => nu • (1 :
          Homogenization.Mat d) + SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega
          (Homogenization.cubeSet (Homogenization.originCube d (m : ℤ))) ((fun i => (3 : ℝ) ^ ((n :
          ℤ) - 3) * (k i : ℝ)) + x)) (Homogenization.openCubeSet (Homogenization.originCube d (n :
          ℤ))), ENNReal.ofReal
          (Homogenization.Book.Ch03.scaleNormalizedDualNegativeBesovVectorNormTwo
          (Homogenization.originCube d (n : ℤ)) (1 / 4) (fun x => Homogenization.matVecMul (nu • (1
          : Homogenization.Mat d) + SuperdiffusionCLT.Section2.Carriers.centeredStreamField
          omega (Homogenization.cubeSet (Homogenization.originCube d (m : ℤ))) ((fun i => (3 : ℝ) ^
          ((n : ℤ) - 3) * (k i : ℝ)) + x) -
          SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P • (1 : Homogenization.Mat
          d)) (u.toH1.grad x))) ≤ ENNReal.ofReal (C * Real.sqrt
          (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P) * (ε * (m : ℝ) ^ (-((1
          - ρ) / 2)) * Real.log (m : ℝ)) * Real.sqrt nu) *
          SuperdiffusionCLT.Section2.Norms.cubeLpENorm (Homogenization.originCube d (n : ℤ)) 2
          (fun x => Real.sqrt (Homogenization.vecNormSq (u.toH1.grad x))) ∧ ENNReal.ofReal
          (Homogenization.Book.Ch03.scaleNormalizedDualNegativeBesovVectorNormTwo
          (Homogenization.originCube d (n : ℤ)) (1 / 4) u.toH1.grad) ≤ ENNReal.ofReal (C *
          (Real.sqrt (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P))⁻¹ *
          Real.sqrt nu) * SuperdiffusionCLT.Section2.Norms.cubeLpENorm
          (Homogenization.originCube d (n : ℤ)) 2 (fun x => Real.sqrt (Homogenization.vecNormSq
          (u.toH1.grad x))) ∧ ∃ w : Homogenization.AHarmonicFunction (fun _ => (1 :
          Homogenization.Mat d)) (Homogenization.openCubeSet (Homogenization.originCube d ((n : ℤ) -
          1))), ENNReal.ofReal ((3 : ℝ) ^ (-(n : ℝ))) *
          SuperdiffusionCLT.Section2.Norms.cubeLpENorm (Homogenization.originCube d ((n : ℤ) -
          1)) 2 (fun x => u.toH1.toFun x - w.toH1.toFun x) ≤ ENNReal.ofReal (C * (ε * (m : ℝ) ^
          (-((1 - ρ) / 2)) * Real.log (m : ℝ)) * (Real.sqrt
          (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P))⁻¹ * Real.sqrt nu) *
          SuperdiffusionCLT.Section2.Norms.cubeLpENorm (Homogenization.originCube d (n : ℤ)) 2
          (fun x => Real.sqrt (Homogenization.vecNormSq (u.toH1.grad x)))) ∧ Homogenization.matNorm
          ((SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P)⁻¹ •
          Homogenization.sigmaCoarse (Homogenization.cubeSet (Homogenization.originCube d (n : ℤ)))
          (fun x => nu • (1 : Homogenization.Mat d) +
          SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega (Homogenization.cubeSet
          (Homogenization.originCube d (m : ℤ))) ((fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) +
          x)) - 1) + Homogenization.matNorm
          ((SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P)⁻¹ •
          Homogenization.sigmaStarCoarse (Homogenization.cubeSet (Homogenization.originCube d (n :
          ℤ))) (fun x => nu • (1 : Homogenization.Mat d) +
          SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega (Homogenization.cubeSet
          (Homogenization.originCube d (m : ℤ))) ((fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) +
          x)) - 1) ≤ C * (ε * (m : ℝ) ^ (-((1 - ρ) / 2)) * Real.log (m : ℝ))) ∧ ENNReal.ofReal ((m :
          ℝ)⁻¹) * SuperdiffusionCLT.Section2.Norms.cubeLpENorm (Homogenization.originCube d (m
          : ℤ)) ∞ (SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega
          (Homogenization.cubeSet (Homogenization.originCube d (m : ℤ)))) + ENNReal.ofReal ((3 : ℝ)
          ^ (-((1 / 4 : ℝ) * (m : ℝ)))) * SuperdiffusionCLT.Section2.Norms.matHatNegENorm
          (Homogenization.originCube d (m : ℤ)) (1 / 4) 2
          (SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega
          (Homogenization.cubeSet (Homogenization.originCube d (m : ℤ)))) ≤ ENNReal.ofReal ((m : ℝ)
          ^ ρ)) :
    ∃ C Cp : ℝ, 1 ≤ C ∧ 0 < Cp ∧ ∀ nu : ℝ, 0 < nu → nu ≤ 1 → ∀ cStar : ℝ, 0 < cStar → ∀ K : ℝ,
      ∀ ρ M : ℝ, 0 < ρ → ρ < 1 → C ≤ M → ∃ Lhat : ℝ, 1 ≤ Lhat ∧
        ∀ (P : MeasureTheory.ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
          (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
          (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P)
          (hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P),
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P →
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P →
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ5 d P cStar K hPrefix hJ2 hJ3 →
          ∃ X : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ, Measurable X ∧
            (∀ omega, 1 ≤ X omega) ∧
            Homogenization.IndependentSums.IsBigO P.toMeasure
              (Homogenization.IndependentSums.gammaSigma ρ) (fun omega => Real.log (X omega))
              Lhat ∧
            ∀ᵐ omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d ∂P.toMeasure,
              ∀ (t : ℝ) (m : ℕ), X omega ≤ t → (3 : ℝ) ^ m < 3 * t → t ≤ (3 : ℝ) ^ m →
                ∃ n : ℕ, (n : ℤ) = (m : ℤ) - ⌈M * Real.log (m : ℝ)⌉ + 3 ∧ n ≤ m ∧
                ∀ U : Set (Vec d), U ⊆ openCubeSet (originCube d 0) →
                  ∀ (u : H1Function (t • U)) (f : Vec d → ℝ),
                    AEMeasurable f (volume.restrict (t • U)) →
                    IsWeakSolutionOn (SuperdiffusionCLT.Section6.fullCoefficientRecentered nu omega)
                      (t • U) u f (fun _ => 0) →
                    ∀ Z : Finset (Fin d → ℤ), (∀ k ∈ Z, wh2_B n k ⊆ t • U) →
                      ∑ k ∈ Z, wh1_osc ((3 : ℝ) ^ ((n : ℤ) - 3)) (27 * (3 : ℝ) ^ ((n : ℤ) - 3) / 2)
                          u.toFun (fun k => cubeAverage (originCube d (n : ℤ))
                            (fun y => u.toFun (y + fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)))) k ≤
                        27 ^ d * (2 * ENNReal.ofReal (Cp * (3 : ℝ) ^ n) ^ 2 *
                          (ENNReal.ofReal
                              (C * (Real.sqrt
                                (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P))⁻¹ *
                                Real.sqrt nu) ^ 2 *
                              (∫⁻ x in t • U, ENNReal.ofReal (eucNorm (u.grad x) ^ 2)) +
                            ENNReal.ofReal
                              ((C * (Real.sqrt
                                (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P))⁻¹ *
                                Real.sqrt nu + C) * (C * (3 : ℝ) ^ (n : ℤ) / nu)) ^ 2 *
                              ∫⁻ x in t • U, ENNReal.ofReal (f x ^ 2))) := by
  obtain ⟨C, Cp, hC, hCp, H⟩ := wh2_ae_sum d hd hInputs
  refine ⟨C, Cp, hC, hCp, ?_⟩
  intro nu hnu hnu1 cStar hcStar K ρ M hρ hρ1 hCM
  obtain ⟨Lhat, hL, H2⟩ := H nu hnu hnu1 cStar hcStar K ρ M hρ hρ1 hCM
  obtain ⟨L0, hL0, hscale⟩ := wh2_scale_exists (hC.trans hCM)
  set L' : ℝ := max Lhat L0 with hL'
  have hL'1 : 1 ≤ L' := hL.trans (le_max_left _ _)
  refine ⟨2 * L', by linarith only [hL'1], fun P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5 => ?_⟩
  obtain ⟨X0, hm, h1, hO, hae⟩ := H2 P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5
  refine ⟨fun omega => max (X0 omega) ((3 : ℝ) ^ L'), hm.max measurable_const,
    fun omega => (h1 omega).trans (le_max_left _ _),
    wh2_isBigO_max h1 (le_max_left _ _) (by linarith only [hL'1]) hO, ?_⟩
  filter_upwards [hae] with omega hω
  intro t m hXt _ htm
  have h3t : (3 : ℝ) ^ L' ≤ (3 : ℝ) ^ (m : ℝ) := by
    rw [Real.rpow_natCast]
    exact (le_max_right _ _).trans (hXt.trans htm)
  have hL'm : L' ≤ (m : ℝ) := (Real.rpow_le_rpow_left_iff (by norm_num)).1 h3t
  have hLm : Lhat ≤ (m : ℝ) := (le_max_left _ _).trans hL'm
  have hsc := hscale m ((le_max_right _ _).trans hL'm)
  have ht0 : 0 < t := lt_of_lt_of_le one_pos ((h1 omega).trans ((le_max_left _ _).trans hXt))
  refine ⟨(m - ⌈M * Real.log (m : ℝ)⌉ + 3).toNat, ?_, ?_, ?_⟩
  · omega
  · omega
  intro U hU u f hf hsol Z hZ
  have hX0 : X0 omega ≤ (3 : ℝ) ^ m := (le_max_left _ _).trans (hXt.trans htm)
  refine hω m (m - ⌈M * Real.log (m : ℝ)⌉ + 3).toNat hX0 hLm (by omega) (by omega)
    (t • U) (w0_smul_subset_openCubeSet_originCube hU ht0 m htm) u f hf hsol Z hZ

/-- Witness for `wh2_osc_cube` (`d = 2`, `n = 0`): the identity field on the unit cube, a weak
solution of `-Δu = 1`, `z = 0`, the dual bound with `A = K` (the embedding constant) and `B_f = 0`;
the conclusion is the classical Poincare inequality on the cube (the power of `3^n` is the right
one: both sides scale as `3^{(d+2)n}`). -/
example : ∃ (u : H1Function (openCubeSet (originCube 2 ((0 : ℕ) : ℤ)))),
    ∃ Cp K : ℝ, 0 < Cp ∧ 0 ≤ K ∧
      ∫⁻ x in translateSet 0 (openCubeSet (originCube 2 ((0 : ℕ) : ℤ))),
          ENNReal.ofReal ((u.toFun x - cubeAverage (originCube 2 ((0 : ℕ) : ℤ))
            (fun y => u.toFun (y + 0))) ^ 2) ≤
        2 * ENNReal.ofReal (Cp * (3 : ℝ) ^ (0 : ℕ)) ^ 2 *
          (ENNReal.ofReal K ^ 2 *
              (∫⁻ x in translateSet 0 (openCubeSet (originCube 2 ((0 : ℕ) : ℤ))),
                ENNReal.ofReal (eucNorm (u.grad x) ^ 2)) +
            ENNReal.ofReal 0 ^ 2 *
              ∫⁻ x in translateSet 0 (openCubeSet (originCube 2 ((0 : ℕ) : ℤ))),
                ENNReal.ofReal ((fun _ : Vec 2 => (1 : ℝ)) x ^ 2)) := by
  obtain ⟨Cp, hCp, H⟩ := wh2_osc_cube 2
  obtain ⟨K, hK, hD⟩ := r1_ofReal_dual_le 2
  have hfin : IsFiniteMeasure (volumeMeasureOn (openCubeSet (originCube 2 0))) :=
    ⟨by simp [volumeMeasureOn]⟩
  obtain ⟨u, hu, -⟩ := w0_dirichlet_exists (U := openCubeSet (originCube 2 0))
    (isOpen_openCubeSet _) (isBoundedDomain_openCubeSet _)
    (Section6.ew1_ellip _ (measurableSet_openCubeSet _)) (f := fun _ => (1 : ℝ)) (memLp_const 1)
    (0 : H1Function (openCubeSet (originCube 2 0)))
  refine ⟨u, Cp, K, hCp, hK, ?_⟩
  refine H 0 (0 : Vec 2) (by rw [translateSet_zero]; simp) (a := fun _ => (1 : Mat 2))
    (a' := fun _ => (1 : Mat 2)) (u := u) (f := fun _ => 1) aemeasurable_const hu
    (fun v g hv => hv) K 0 2 le_rfl (fun v g _ => ?_)
  refine (hD _ _ (r1_memLp_grad_comp _ v) (r1_memLp_grad_eucNorm _ v)).trans ?_
  simp only [ENNReal.ofReal_zero, zero_mul, add_zero]
  exact le_rfl

end SuperdiffusionCLT.Section7

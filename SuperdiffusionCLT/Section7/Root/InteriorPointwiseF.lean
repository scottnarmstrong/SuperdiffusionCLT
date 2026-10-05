/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Root.InteriorPointwiseE
public import SuperdiffusionCLT.Section7.Prereq.RootCarriers
public import SuperdiffusionCLT.Section7.MinimalScale.GridMaxCount
public import SuperdiffusionCLT.Section2.Annealed.InfiniteVolume
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ5
public import Homogenization.Probability.IndependentSums.WeakOrlicz
public import SuperdiffusionCLT.Frozen.Section6.SharpScaleInputs
public import SuperdiffusionCLT.Frozen.Section5.SigmaBarSharpBounds

/-!
# The interior pointwise oscillation estimate

`ip_interior_pointwise` is the statement of `Frozen.Section7.interior_pointwise`
(`l.Dirichlet.interior.pointwise`), with the sharp inputs and the window of `σ̄` as explicit
hypotheses `hInputs`, `hS5`.

It follows from the approximation at the scale `k = n + 1` (`ia_approx`: the
solution is close in `L^∞` to a solution of the Poisson equation in a rounded cube), the interior
estimate for the Poisson equation (`ip_poisson`), and the Lipschitz estimate between the scales
`k` and `m` (`lip_interior_grid_final`, `ip_final_det`).
-/

@[expose] public section

open scoped ENNReal Pointwise
open scoped Matrix.Norms.L2Operator
open Homogenization MeasureTheory
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section2.Cutoff (ShellSeq)
open SuperdiffusionCLT.Section2.Annealed (sigmaBarInfinite)

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

/-- The scale bookkeeping of the quantifier assembly. -/
theorem ip_scales {Cm Lia Ll Lw Ld N ε ρ cL : ℝ} {L0 m n : ℕ} (hCm : 1 ≤ Cm) (hLia : 1 ≤ Lia)
    (hLl : 1 ≤ Ll) (hLw4 : 4 ≤ Lw) (hLd3 : 3 ≤ Ld) (hε : 0 < ε)
    (hLw : ∀ m n : ℝ, Lw ≤ m → m - n ≤ cL * (deltaScale ε ρ m)⁻¹ → m / 2 ≤ n)
    (hLd : ∀ k : ℝ, Ld ≤ k → (0 * Real.log k + 1) * deltaScale ε ρ (k - 1) ≤ 1)
    (hnm : n < m) (hwin : ((m : ℝ) - (n : ℝ)) * deltaScale ε ρ (m : ℝ) ≤ cL)
    (hLn : Cm * (Lia + Ll) + L0 + Lw + Ld + 8 ≤ (nK N n : ℝ)) :
    5 ≤ n ∧ Lia ≤ (nK N n : ℝ) ∧ Ll ≤ (nK N n : ℝ) ∧ L0 ≤ n + 1 ∧ L0 ≤ m ∧ m ≤ 2 * (n + 1) ∧
      deltaScale ε ρ ((n + 1 : ℕ) : ℝ) ≤ 1 ∧ 0 ≤ deltaScale ε ρ ((n + 1 : ℕ) : ℝ) ∧
      0 ≤ deltaScale ε ρ (m : ℝ) := by
  have hL0r : (0 : ℝ) ≤ L0 := Nat.cast_nonneg L0
  have hLs : 0 ≤ Cm * (Lia + Ll) := by
    have : 0 ≤ Lia + Ll := by linarith only [hLia, hLl]
    positivity
  have hLia' : Lia ≤ Cm * (Lia + Ll) := by nlinarith only [hCm, hLia, hLl]
  have hLl' : Ll ≤ Cm * (Lia + Ll) := by nlinarith only [hCm, hLia, hLl]
  have hnKn : (nK N n : ℝ) ≤ n := by exact_mod_cast nK_le N n
  have hLn' : Cm * (Lia + Ll) + L0 + Lw + Ld + 8 ≤ (n : ℝ) := hLn.trans hnKn
  have hn5 : 5 ≤ n := by
    have : (5 : ℝ) ≤ n := by linarith only [hLn', hLs, hL0r, hLw4, hLd3]
    exact_mod_cast this
  have hnm1 : n + 1 ≤ m := hnm
  have hnmR : (n : ℝ) + 1 ≤ m := by exact_mod_cast hnm1
  have hmbig : Lw ≤ (m : ℝ) := by linarith only [hLn', hLs, hL0r, hLw4, hLd3, hnmR]
  have hδm : 0 < deltaScale ε ρ (m : ℝ) :=
    deltaScale_pos hε (by linarith only [hLn', hLs, hL0r, hLw4, hLd3, hnmR])
  have hwin' : (m : ℝ) - n ≤ cL * (deltaScale ε ρ (m : ℝ))⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ hδm]; exact hwin
  have hhalf := hLw (m : ℝ) (n : ℝ) hmbig hwin'
  have hm2 : m ≤ 2 * (n + 1) := by
    have : (m : ℝ) ≤ 2 * ((n : ℝ) + 1) := by linarith only [hhalf]
    exact_mod_cast this
  refine ⟨hn5, by linarith only [hLn, hLia', hL0r, hLw4, hLd3, hLs],
    by linarith only [hLn, hLl', hL0r, hLw4, hLd3, hLs], ?_, ?_, hm2, ?_, ?_, hδm.le⟩
  · have : (L0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by push_cast; linarith only [hLn', hLs, hL0r, hLw4, hLd3]
    exact_mod_cast this
  · have : (L0 : ℝ) ≤ m := by linarith only [hLn', hLs, hL0r, hLw4, hLd3, hnmR]
    exact_mod_cast this
  · have h := hLd ((n : ℝ) + 2) (by linarith only [hLn', hLs, hL0r, hLw4, hLd3])
    rw [zero_mul, zero_add, one_mul] at h
    have e : (n : ℝ) + 2 - 1 = ((n + 1 : ℕ) : ℝ) := by push_cast; ring
    rw [e] at h; exact h
  · exact (deltaScale_pos hε (by push_cast; linarith only [hLn', hLs, hL0r, hLw4, hLd3])).le

theorem ip_omega [NeZero d] (hd : 2 ≤ d) {CIA CL cL : ℝ} (hCIA : 1 ≤ CIA) (hCL : 1 ≤ CL) {N0 : ℕ}
    (hN0 : 1 ≤ N0) (hdim : (d : ℝ) * (4 / 5 : ℝ) ^ (2 * N0) < 1) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {omega : ShellSeq d} {P : ProbabilityMeasure (ShellSeq d)} {nu ε ρ N : ℝ}
      {m n : ℕ} {y : Vec d}, 0 < nu → 5 ≤ n → n < m →
      ((m : ℝ) - (n : ℝ)) * deltaScale ε ρ (m : ℝ) ≤ cL →
      1 ≤ sigmaBarInfinite nu (n + 1) P → sigmaBarInfinite nu m P ≤ 2 * sigmaBarInfinite nu (n + 1) P →
      1 ≤ sigmaBarInfinite nu m P → 0 ≤ deltaScale ε ρ ((n + 1 : ℕ) : ℝ) →
      deltaScale ε ρ ((n + 1 : ℕ) : ℝ) ≤ 1 → 0 ≤ deltaScale ε ρ (m : ℝ) →
      (
            ∀ (f : Vec d → ℝ) (u : H1Function (shiftCube y ((n + 1 : ℕ) : ℤ))),
              IsWeakSolutionOn (Section6.fullCoefficientRecentered nu omega) (shiftCube y ((n + 1 : ℕ) : ℤ))
                u f (fun _ => 0) →
              eLpNorm f ⊤ (volume.restrict (shiftCube y ((n + 1 : ℕ) : ℤ))) ≠ ⊤ →
              ∃ (f' : Vec d → ℝ) (uhom : H1Function (ia_V d N0 (n + 1) y)),
                Measurable f' ∧
                (∀ x, |f' x| ≤ (eLpNorm f ⊤ (volume.restrict (shiftCube y ((n + 1 : ℕ) : ℤ)))).toReal) ∧
                IsWeakSolutionOn (fun _ => sigmaBarInfinite nu (n + 1) P • (1 : Mat d)) (ia_V d N0 (n + 1) y)
                  uhom f' (fun _ => 0) ∧
                eLpNorm (fun x => u.toFun x - uhom.toFun x) ⊤ (volume.restrict (ia_V d N0 (n + 1) y)) ≤
                  ENNReal.ofReal (CIA * deltaScale ε ρ ((n + 1 : ℕ) : ℝ) *
                    (h1_l2 (h1_cube y (n + 1)) u.toFun + (sigmaBarInfinite nu (n + 1) P)⁻¹ * (3 : ℝ) ^ (2 * (n + 1)) *
                      (eLpNorm f ⊤ (volume.restrict (shiftCube y ((n + 1 : ℕ) : ℤ)))).toReal))
      ) →
      (
          ∀ m l : ℕ, nK N n ≤ l → l < m →
            ((m : ℝ) - (l : ℝ)) * deltaScale ε ρ (m : ℝ) ≤ cL →
            ∀ (f : Vec d → ℝ) (u : H1Function (shiftCube y (m : ℤ))),
              IsWeakSolutionOn (Section6.fullCoefficientRecentered nu omega)
                (shiftCube y (m : ℤ)) u f (fun _ => 0) →
              ENNReal.ofReal ((Real.sqrt (sigmaBarInfinite nu m P))⁻¹ * Real.sqrt nu) *
                    lpBar (shiftCube y (l : ℤ)) 2 (fun x => eucNorm (u.grad x)) +
                  ENNReal.ofReal ((3 : ℝ) ^ (-(l : ℝ))) *
                    lpBar (shiftCube y (l : ℤ)) 2
                      (fun x => u.toFun x - ⨍ w in shiftCube y (l : ℤ), u.toFun w) ≤
                ENNReal.ofReal (CL * (3 : ℝ) ^ (-(m : ℝ))) *
                    lpBar (shiftCube y (m : ℤ)) 2
                      (fun x => u.toFun x - ⨍ w in shiftCube y (m : ℤ), u.toFun w) +
                  ENNReal.ofReal (CL * (sigmaBarInfinite nu m P)⁻¹ * (3 : ℝ) ^ m) *
                    eLpNorm f ⊤ (volume.restrict (shiftCube y (m : ℤ)))
      ) →
      ∀ (f : Vec d → ℝ) (u : H1Function (shiftCube y (m : ℤ))),
        IsWeakSolutionOn (Section6.fullCoefficientRecentered nu omega) (shiftCube y (m : ℤ)) u f
          (fun _ => 0) →
        eLpNorm (fun x => u.toFun x - ⨍ z in shiftCube y (n : ℤ), u.toFun z) ⊤
            (volume.restrict (shiftCube y (n : ℤ))) ≤
          ENNReal.ofReal (C * (3 : ℝ) ^ (-((m : ℝ) - (n : ℝ)))) *
            (lpBar (shiftCube y (m : ℤ)) 2
                (fun x => u.toFun x - ⨍ z in shiftCube y (m : ℤ), u.toFun z) +
              ENNReal.ofReal ((sigmaBarInfinite nu m P)⁻¹ * (3 : ℝ) ^ (2 * (m : ℝ))) *
                eLpNorm f ⊤ (volume.restrict (shiftCube y (m : ℤ)))) := by
  obtain ⟨C, hC, Hfin⟩ := ip_final_det hd hCIA hCL hN0 hdim
  refine ⟨C, hC, ?_⟩
  intro omega P nu ε ρ N m n y hnu hn5 hnm hwin hσk1 hσmk hσm1 hδk0 hδk hδm0 hIA hLipn f u hu
  have hnm1 : n + 1 ≤ m := hnm
  by_cases hfm : eLpNorm f ⊤ (volume.restrict (shiftCube y (m : ℤ))) = ⊤
  · rw [hfm]
    have h1 : ENNReal.ofReal ((sigmaBarInfinite nu m P)⁻¹ * (3 : ℝ) ^ (2 * (m : ℝ))) ≠ 0 := by
      have : 0 < (sigmaBarInfinite nu m P)⁻¹ * (3 : ℝ) ^ (2 * (m : ℝ)) := by
        have hs : 0 < sigmaBarInfinite nu m P := by linarith only [hσm1]
        exact mul_pos (inv_pos.2 hs) (Real.rpow_pos_of_pos (by norm_num) _)
      exact (ENNReal.ofReal_pos.2 this).ne'
    have h2 : ENNReal.ofReal (C * (3 : ℝ) ^ (-((m : ℝ) - (n : ℝ)))) ≠ 0 := by
      have : 0 < C * (3 : ℝ) ^ (-((m : ℝ) - (n : ℝ))) := by
        have hC0 : 0 < C := by linarith only [hC]
        exact mul_pos hC0 (Real.rpow_pos_of_pos (by norm_num) _)
      exact (ENNReal.ofReal_pos.2 this).ne'
    rw [ENNReal.mul_top h1, add_top, ENNReal.mul_top h2]
    exact le_top
  · have hfink : eLpNorm f ⊤ (volume.restrict (shiftCube y ((n + 1 : ℕ) : ℤ))) ≠ ⊤ := by
      refine ne_top_of_le_ne_top hfm ?_
      refine eLpNorm_mono_measure f (Measure.restrict_mono ?_ le_rfl)
      rw [ip_shiftCube_ball, ip_shiftCube_ball]
      have h3 : (3 : ℝ) ^ (n + 1) ≤ 3 ^ m := pow_le_pow_right₀ (by norm_num) hnm1
      exact Metric.ball_subset_ball (by linarith only [h3])
    refine Hfin (y := y) (n := n) (m := m) hn5 hnm (σk := sigmaBarInfinite nu (n + 1) P)
      (σm := sigmaBarInfinite nu m P) (δ := deltaScale ε ρ ((n + 1 : ℕ) : ℝ)) (by linarith only [hσk1])
      (by linarith only [hσm1]) hσmk hδk0 hδk u hfm ?_ ?_
    · intro hsub
      exact hIA f (u.restrict (rc_isOpen_shiftCube y ((n + 1 : ℕ) : ℤ)) hsub)
        (hu.restrict' (rc_isOpen_shiftCube y ((n + 1 : ℕ) : ℤ)) hsub) hfink
    · intro hlt
      have hw2 : ((m : ℝ) - ((n + 1 : ℕ) : ℝ)) * deltaScale ε ρ (m : ℝ) ≤ cL := by
        refine le_trans (mul_le_mul_of_nonneg_right ?_ hδm0) hwin
        push_cast; linarith only
      have hl := hLipn m (n + 1) (nK_le N n |>.trans (Nat.le_succ n)) hlt hw2 f u hu
      have hF0 : 0 ≤ (eLpNorm f ⊤ (volume.restrict (shiftCube y (m : ℤ)))).toReal := ENNReal.toReal_nonneg
      have hfF : eLpNorm f ⊤ (volume.restrict (shiftCube y (m : ℤ))) ≤
          ENNReal.ofReal (eLpNorm f ⊤ (volume.restrict (shiftCube y (m : ℤ)))).toReal :=
        (ENNReal.ofReal_toReal hfm).ge
      exact (ip_lip_real (z := y) (lh := n + 1) (m' := m) hlt.le hF0 (by linarith only [hCL])
        hnu (by linarith only [hσm1]) hfF hl).2


theorem ip_interior_pointwise (d : ℕ) [NeZero d] (hd : 2 ≤ d)
    (hInputs :
        ∃ C : ℝ, 1 ≤ C ∧
        ∀ nu : ℝ, 0 < nu → nu ≤ 1 →
        ∀ cStar : ℝ, 0 < cStar →
        ∀ K : ℝ,
        ∀ ε ρ M : ℝ, 0 < ε → ε ≤ 1 → 0 < ρ → ρ < 1 → C ≤ M →
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
        ∃ X0 : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ,
        Measurable X0 ∧ (∀ omega, 1 ≤ X0 omega) ∧
        Homogenization.IndependentSums.IsBigO P.toMeasure
        (Homogenization.IndependentSums.gammaSigma ρ)
        (fun omega => Real.log (X0 omega)) Lhat ∧
        ∀ᵐ omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d ∂P.toMeasure,
        ∀ m n : ℕ,
        X0 omega ≤ (3 : ℝ) ^ m →
        Lhat ≤ (m : ℝ) →
        (m : ℤ) - ⌈M * Real.log (m : ℝ)⌉ ≤ (n : ℤ) →
        n ≤ m →
        (∀ k : Fin d → ℤ,
        (fun x => (fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x) ''
        Homogenization.cubeSet (Homogenization.originCube d (n : ℤ)) ⊆
        Homogenization.cubeSet (Homogenization.originCube d (m : ℤ)) →
        -- e.Dir.new.full.good
        Homogenization.HomogenizationErrorOnCube
        (Homogenization.originCube d (n : ℤ)) (1 / 9)
        Homogenization.MultiscaleExponent.infinity
        (Homogenization.MultiscaleExponent.finite 2)
        (fun x => nu • (1 : Homogenization.Mat d) +
        SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega
        (Homogenization.cubeSet (Homogenization.originCube d (m : ℤ)))
        ((fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x))
        (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P •
        (1 : Homogenization.Mat d)) ≤
        ε * (m : ℝ) ^ (-((1 - ρ) / 2)) * Real.log (m : ℝ) ∧
        -- e.Dir.new.reg.ellipticity
        (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P)⁻¹ *
        Homogenization.LambdaSq (Homogenization.originCube d (n : ℤ))
        (1 / 4) (Homogenization.MultiscaleExponent.finite 1)
        (fun x => nu • (1 : Homogenization.Mat d) +
        SuperdiffusionCLT.Section2.Carriers.centeredStreamField
        omega
        (Homogenization.cubeSet
        (Homogenization.originCube d (m : ℤ)))
        ((fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x)) +
        SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P *
        (Homogenization.lambdaSq (Homogenization.originCube d (n : ℤ))
        (1 / 4) (Homogenization.MultiscaleExponent.finite 1)
        (fun x => nu • (1 : Homogenization.Mat d) +
        SuperdiffusionCLT.Section2.Carriers.centeredStreamField
        omega
        (Homogenization.cubeSet
        (Homogenization.originCube d (m : ℤ)))
        ((fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x)))⁻¹ ≤
        C ∧
        -- e.Dir.new.weak.flux, e.Dir.new.weak.grad, e.Dir.new.harmonic.approx
        (∀ u : Homogenization.AHarmonicFunction
        (fun x => nu • (1 : Homogenization.Mat d) +
        SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega
        (Homogenization.cubeSet (Homogenization.originCube d (m : ℤ)))
        ((fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x))
        (Homogenization.openCubeSet (Homogenization.originCube d (n : ℤ))),
        ENNReal.ofReal
        (Homogenization.Book.Ch03.scaleNormalizedDualNegativeBesovVectorNormTwo
        (Homogenization.originCube d (n : ℤ)) (1 / 4)
        (fun x => Homogenization.matVecMul
        (nu • (1 : Homogenization.Mat d) +
        SuperdiffusionCLT.Section2.Carriers.centeredStreamField
        omega
        (Homogenization.cubeSet
        (Homogenization.originCube d (m : ℤ)))
        ((fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x) -
        SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite
        nu m P • (1 : Homogenization.Mat d))
        (u.toH1.grad x))) ≤
        ENNReal.ofReal
        (C *
        Real.sqrt
        (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite
        nu m P) *
        (ε * (m : ℝ) ^ (-((1 - ρ) / 2)) * Real.log (m : ℝ)) *
        Real.sqrt nu) *
        SuperdiffusionCLT.Section2.Norms.cubeLpENorm
        (Homogenization.originCube d (n : ℤ)) 2
        (fun x => Real.sqrt (Homogenization.vecNormSq (u.toH1.grad x))) ∧
        ENNReal.ofReal
        (Homogenization.Book.Ch03.scaleNormalizedDualNegativeBesovVectorNormTwo
        (Homogenization.originCube d (n : ℤ)) (1 / 4) u.toH1.grad) ≤
        ENNReal.ofReal
        (C *
        (Real.sqrt
        (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite
        nu m P))⁻¹ *
        Real.sqrt nu) *
        SuperdiffusionCLT.Section2.Norms.cubeLpENorm
        (Homogenization.originCube d (n : ℤ)) 2
        (fun x => Real.sqrt (Homogenization.vecNormSq (u.toH1.grad x))) ∧
        ∃ w : Homogenization.AHarmonicFunction
        (fun _ => (1 : Homogenization.Mat d))
        (Homogenization.openCubeSet
        (Homogenization.originCube d ((n : ℤ) - 1))),
        ENNReal.ofReal ((3 : ℝ) ^ (-(n : ℝ))) *
        SuperdiffusionCLT.Section2.Norms.cubeLpENorm
        (Homogenization.originCube d ((n : ℤ) - 1)) 2
        (fun x => u.toH1.toFun x - w.toH1.toFun x) ≤
        ENNReal.ofReal
        (C * (ε * (m : ℝ) ^ (-((1 - ρ) / 2)) * Real.log (m : ℝ)) *
        (Real.sqrt
        (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite
        nu m P))⁻¹ *
        Real.sqrt nu) *
        SuperdiffusionCLT.Section2.Norms.cubeLpENorm
        (Homogenization.originCube d (n : ℤ)) 2
        (fun x =>
        Real.sqrt (Homogenization.vecNormSq (u.toH1.grad x)))) ∧
        -- e.Dir.new.sstar.close
        Homogenization.matNorm
        ((SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite
        nu m P)⁻¹ •
        Homogenization.sigmaCoarse
        (Homogenization.cubeSet
        (Homogenization.originCube d (n : ℤ)))
        (fun x => nu • (1 : Homogenization.Mat d) +
        SuperdiffusionCLT.Section2.Carriers.centeredStreamField
        omega
        (Homogenization.cubeSet
        (Homogenization.originCube d (m : ℤ)))
        ((fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x)) -
        1) +
        Homogenization.matNorm
        ((SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite
        nu m P)⁻¹ •
        Homogenization.sigmaStarCoarse
        (Homogenization.cubeSet
        (Homogenization.originCube d (n : ℤ)))
        (fun x => nu • (1 : Homogenization.Mat d) +
        SuperdiffusionCLT.Section2.Carriers.centeredStreamField
        omega
        (Homogenization.cubeSet
        (Homogenization.originCube d (m : ℤ)))
        ((fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x)) -
        1) ≤
        C * (ε * (m : ℝ) ^ (-((1 - ρ) / 2)) * Real.log (m : ℝ))) ∧
        -- e.Dir.new.k.bounds
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
        ENNReal.ofReal ((m : ℝ) ^ ρ))
    (hS5 :
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
        C * cStar⁻¹ * (Real.log (m : ℝ) ^ (2 : ℝ) + K))
    :
    ∃ C c N : ℝ, 1 ≤ C ∧ 0 < c ∧ 0 ≤ N ∧
      ∀ nu : ℝ, 0 < nu → nu ≤ 1 →
        ∀ cStar : ℝ, 0 < cStar →
          ∀ K : ℝ,
            ∀ ε ρ : ℝ, 0 < ε → ε ≤ 1 → 0 < ρ → ρ < 1 →
              ∀ A : ℕ,
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
                      ∀ᵐ omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d
                          ∂P.toMeasure,
                        ∀ m n : ℕ,
                          n < m →
                          ((m : ℝ) - (n : ℝ)) *
                              (ε * (m : ℝ) ^ (-((1 - ρ) / 2)) * Real.log (m : ℝ)) ≤ c →
                          Lhat ≤ (SuperdiffusionCLT.Section7.nK N n : ℝ) →
                          X omega ≤ (3 : ℝ) ^ SuperdiffusionCLT.Section7.nK N n →
                          ∀ y ∈ SuperdiffusionCLT.Section7.gridPts d
                              ((SuperdiffusionCLT.Section7.nK N n : ℤ) - 3)
                              ((3 : ℝ) ^ (n + A)),
                            ∀ (f : Homogenization.Vec d → ℝ)
                              (u : Homogenization.H1Function
                                (SuperdiffusionCLT.Section7.shiftCube y (m : ℤ))),
                              SuperdiffusionCLT.Section7.IsWeakSolutionOn
                                  (SuperdiffusionCLT.Section6.fullCoefficientRecentered
                                    nu omega)
                                  (SuperdiffusionCLT.Section7.shiftCube y (m : ℤ))
                                  u f (fun _ => 0) →
                              -- e.Dir.new.interior.pointwise
                              MeasureTheory.eLpNorm
                                  (fun x => u.toFun x -
                                    ⨍ z in SuperdiffusionCLT.Section7.shiftCube y (n : ℤ),
                                      u.toFun z)
                                  ⊤
                                  (MeasureTheory.volume.restrict
                                    (SuperdiffusionCLT.Section7.shiftCube y (n : ℤ))) ≤
                                ENNReal.ofReal (C * (3 : ℝ) ^ (-((m : ℝ) - (n : ℝ)))) *
                                  (SuperdiffusionCLT.Section7.lpBar
                                      (SuperdiffusionCLT.Section7.shiftCube y (m : ℤ)) 2
                                      (fun x => u.toFun x -
                                        ⨍ z in SuperdiffusionCLT.Section7.shiftCube y
                                            (m : ℤ),
                                          u.toFun z) +
                                    ENNReal.ofReal
                                        ((SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite
                                            nu m P)⁻¹ *
                                          (3 : ℝ) ^ (2 * (m : ℝ))) *
                                      MeasureTheory.eLpNorm f ⊤
                                        (MeasureTheory.volume.restrict
                                          (SuperdiffusionCLT.Section7.shiftCube y
                                            (m : ℤ)))) := by
  obtain ⟨CIA, N, N0, hCIA, hN, hN0, hdim, HIA⟩ := ia_approx d hd hInputs hS5
  obtain ⟨CL, cL, hCL, hcL, HL⟩ := lip_interior_grid_final d hd hInputs hS5
  obtain ⟨C, hC, Homega⟩ := ip_omega hd hCIA hCL hN0 hdim
  have hp := ip_p_ge_one hd
  have hN0' : 0 ≤ N := by linarith only [hN, hp]
  refine ⟨C, cL, N, hC, hcL, hN0', ?_⟩
  intro nu hnu hnu1 cStar hcStar K ε ρ hε hε1 hρ hρ1 A
  obtain ⟨Lia, hLia, Hia⟩ := HIA nu hnu hnu1 cStar hcStar K ε ρ hε hε1 hρ hρ1 A 1
  obtain ⟨Ll, hLl, Hl⟩ := HL nu hnu hnu1 cStar hcStar K ε ρ hε hε1 hρ hρ1 A N hN0'
  obtain ⟨L0, hL0⟩ := lip_sigma_window d hd hS5 nu hnu hnu1 cStar hcStar K
  obtain ⟨Lw, hLw4, hLw⟩ := half_le_of_window cL ε ρ hcL hε hρ.le hρ1.le
  obtain ⟨Ld, hLd3, hLd⟩ := ip_win (N := 0) (c := 1) hε hρ.le hρ1 le_rfl one_pos
  obtain ⟨Cm, hCm, Hm⟩ := ia_max_scale.{0} hρ
  refine ⟨Cm * (Lia + Ll) + L0 + Lw + Ld + 8, ?_, ?_⟩
  · have hLs : 0 ≤ Cm * (Lia + Ll) := by
      have : 0 ≤ Lia + Ll := by linarith only [hLia, hLl]
      positivity
    linarith only [hLs, (Nat.cast_nonneg L0 : (0 : ℝ) ≤ L0), hLw4, hLd3]
  intro P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5
  obtain ⟨Xi, hXim, hXi1, hXiO, haeI⟩ := Hia P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5
  obtain ⟨Xl, hXlm, hXl1, hXlO, haeL⟩ := Hl P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5
  have hXO := Hm (by linarith only [hLia]) (by linarith only [hLl]) hXi1 hXl1 hXiO hXlO
  refine ⟨fun ω => max (Xi ω) (Xl ω), hXim.max hXlm, fun ω => le_max_of_le_left (hXi1 ω), ?_, ?_⟩
  · refine hXO.mono_scale ?_
    linarith only [(Nat.cast_nonneg L0 : (0 : ℝ) ≤ L0), hLw4, hLd3]
  filter_upwards [haeI, haeL] with ω hI hLip
  intro m n hnm hwin hLn hXn y hy f u hu
  obtain ⟨hn5, hLiaN, hLlN, hL0n, hL0m, hm2, hδk, hδk0, hδm0⟩ :=
    ip_scales (Cm := Cm) (Lia := Lia) (Ll := Ll) (L0 := L0) hCm hLia hLl hLw4 hLd3 hε hLw hLd hnm hwin hLn
  obtain ⟨hσk1, -, hσmk, -⟩ := hL0 P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5 (n + 1) m hL0n hnm hm2
  obtain ⟨hσm1, -, -, -⟩ := hL0 P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5 m m hL0m le_rfl (by omega)
  have hIA := hI n (n + 1) hLiaN (le_trans (le_max_left _ _) hXn) le_rfl le_rfl y hy
  have hLipn := hLip n hLlN (le_trans (le_max_right _ _) hXn) y hy
  exact Homega hnu hn5 hnm hwin hσk1 hσmk hσm1 hδk0 hδk hδm0 hIA hLipn f u hu

/-- Witness: the hypotheses are the proved `sharp_scale_inputs` and `sigmaBar_sharp_bounds`; the
statement therefore holds. -/
example [NeZero d] (hd : 2 ≤ d) : ∃ C : ℝ, 1 ≤ C :=
  let ⟨C, _, _, hC, _⟩ := ip_interior_pointwise d hd
    (SuperdiffusionCLT.Frozen.Section6.sharp_scale_inputs d hd)
    (SuperdiffusionCLT.Frozen.Section5.sigmaBar_sharp_bounds d hd)
  ⟨C, hC⟩

end SuperdiffusionCLT.Section7

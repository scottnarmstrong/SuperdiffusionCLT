/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.ResponseFields.RegboundsGateB

/-!
# `l.w.basic.regbounds` with the `√(1 + h)` window factor in the amplitude

This file treats the display `e.nablaw.Lt` of the paper, proved within
`l.w.basic.regbounds`.  The printed display is

`h^{-1/2}‖∇w‖_{L̲⁸} + 3^{ℓ'}‖∇²w‖_{L̲⁸} + 3^{ℓ'/2}‖∇w‖_{H̲^{1/2}} ≤ O_{Γ₂}(C|p|)`

with a constant `C` depending on the dimension alone.  The middle term is the
one that carries the low-shell Jacobian of the flux on `cu_m`, and the honest
route to that Jacobian — stationarity over the `3^{d(m−k)}` scale-`k` sub-cubes
of `cu_m` together with a union bound over that family — produces the extra
factor `√(1 + h)`, `h = m − ℓ'` the window of `e.scale.selection`.  This loss is
accepted: it is carried in the conclusion below.

The earlier form `nablaKmnLow_bridge` records it as a hypothesis: the
amplitude constant `Cn` of the low-shell input is quantified, like the printed
`C(d)`, **before** the scale selection `S`, so `√(1 + h)` cannot be absorbed
into it, and `nablaKmnLow_bridge` therefore leaves the numeric comparison
`nablaKmnLowWindowConst d S.h ≤ Cn` behind.

This module absorbs the factor instead of recording it: the low-shell input is
instantiated at its own honest constant `nablaKmnLowWindowConst d S.h`
**inside** the scale selection, and the loss is carried in the *conclusion*, on
the second clause only, whose amplitude becomes `C |p| √(1 + h) 3^{-ℓ'}`.  The
first and third clauses are unchanged, and no hypothesis is left in their place.

Because the amplitude constant of the printed statement
is existentially quantified, the instantiation cannot be performed from outside
that statement; its assembly is therefore re-run here with the low-shell
constant moved inside the scale selection.  Every ingredient is already available:
the three parenthesized terms of the printed proof
(`exists_witness_vecCubeLpENorm_centeredFlux`,
`exists_witness_cubeLpENorm_fluxJacobian`,
`exists_witness_cubeHsENorm_centeredFlux`), the normalization
`exists_normalized_witness_gateLp` of the shell-increment `L̲^q` clauses, and
the a priori response estimates supplied by `hApriori`.

## Main results

* `nablaKmnLowSumConst`: the `h`-free part `√d · C_Σ(d)` of the union-bound
  amplitude, so that `nablaKmnLowWindowConst d h = nablaKmnLowSumConst d √(1+h)`.
* `regboundsWindowConst`: the amplitude constant of the window form, namely
  `regboundsConst` evaluated at the `h`-free low-shell constant.
* `l_w_basic_regbounds_window_constFirst`: `e.nablaw.Lt` with the constant
  quantified before the scale selection, with the low-shell Jacobian input
  discharged, and with `√(1 + h)` on the amplitude of the second clause.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.ResponseFields

open MeasureTheory
open Homogenization
open Homogenization.Book.Ch02
open Homogenization.IndependentSums
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Probability
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Norms
open SuperdiffusionCLT.Section3.Setup
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

noncomputable section

/-! ## The window-free part of the union-bound amplitude -/

/-- The `h`-free part of the low-shell union-bound amplitude
`nablaKmnLowWindowConst d h = √d · C_Σ(d) · √(1 + h)`: the factor `√d` for the
`d` columns of the Jacobian and the summed one-shell envelope `C_Σ(d)`. -/
def nablaKmnLowSumConst (d : ℕ) : ℝ :=
  Real.sqrt (d : ℝ) * Section2.Estimates.Stream.shellDerivLargeCubeSumConst d

theorem nablaKmnLowWindowConst_eq (d h : ℕ) :
    nablaKmnLowWindowConst d h = nablaKmnLowSumConst d * Real.sqrt (1 + (h : ℝ)) :=
  rfl

theorem nablaKmnLowSumConst_pos {d : ℕ} (hd : 0 < d) :
    0 < nablaKmnLowSumConst d := by
  have h1 : (0 : ℝ) < Real.sqrt (d : ℝ) :=
    Real.sqrt_pos.mpr (by exact_mod_cast hd)
  have h2 : (0 : ℝ) < Section2.Estimates.Stream.shellDerivLargeCubeSumConst d :=
    Section2.Estimates.Stream.shellDerivLargeCubeSumConst_pos_of_pos hd
  exact mul_pos h1 h2

theorem nablaKmnLowWindowConst_pos {d : ℕ} (hd : 0 < d) (h : ℕ) :
    0 < nablaKmnLowWindowConst d h := by
  rw [nablaKmnLowWindowConst_eq]
  have h1 : (0 : ℝ) < Real.sqrt (1 + (h : ℝ)) := by
    refine Real.sqrt_pos.mpr ?_
    linarith only [(Nat.cast_nonneg h : (0 : ℝ) ≤ (h : ℝ))]
  exact mul_pos (nablaKmnLowSumConst_pos hd) h1

/-! ## The constant of the window form -/

/-- **The constant of the window form of `e.nablaw.Lt`.**  It is the constant
`regboundsConst` of `Section3/ResponseFields/RegboundsB.lean` evaluated at the
`h`-free low-shell constant `nablaKmnLowSumConst d`; the window factor
`√(1 + h)` of the low-shell input is carried by the amplitude of the second
clause instead of by this constant.  It depends only on the dimension, on the
constant of the a priori response estimates and on the constants of the three
shell-increment clauses. -/
def regboundsWindowConst (d : ℕ) (Ca C8 C2 CH : ℝ) : ℝ :=
  regboundsConst d Ca C8 C2 CH (nablaKmnLowSumConst d)

theorem one_le_regboundsWindowConst (d : ℕ) (Ca C8 C2 CH : ℝ) :
    1 ≤ regboundsWindowConst d Ca C8 C2 CH :=
  one_le_regboundsConst _ _ _ _ _ _

/-! ## `e.nablaw.Lt` with the window factor absorbed -/

/-- **`l.w.basic.regbounds`** with the constant quantified before the scale selection, the shell
law, the test vector and the response, and with the low-shell Jacobian input
`_hNablaKmnLow` of the printed form discharged from the
large-cube estimate
`exists_witness_cubeLpENorm_streamFluxWeakGradient_largeCube`
at its own honest amplitude `nablaKmnLowWindowConst d S.h`.

The one difference from the printed form is the amplitude of the
**second** clause, which is `C |p| √(1 + h) 3^{-ℓ'}` rather than the printed
`C |p| 3^{-ℓ'}`: the union bound over the `3^{d(m−k)}` scale-`k` sub-cubes of
`cu_m` costs that factor (see above), and since the constant is fixed
before the scale selection the factor has to appear in the conclusion.  The
first and the third clauses are unchanged.

`hApriori` is the conclusion of the a priori anchor `responseFields_apriori_orderZero`
at a fixed finite constant `Capriori`; `_hKmnLp8`, `_hKmnLp2` and `_hKmnHs` are
the clauses `e.kmn.Lp` (at `p = 8` and `p = 2`) and `e.kmn.Hs.osc` (at
`s = 1/2`) of the shell-increment scale estimates, instantiated at
`(ℓ', m − 1, m)` and at `(ℓ', m)` in their stated shapes. -/
theorem l_w_basic_regbounds_window_constFirst
    (d : ℕ) [NeZero d] (hd : 2 ≤ d)
    (Capriori : ℝ≥0∞) (hCapriori : Capriori < ⊤)
    (C8 C2 CH : ℝ) (hCH : 0 < CH)
    (hApriori : ∀ (M : ℕ) (F : Vec d → Vec d)
        (wD : H10Function (openCubeSet (originCube d (M : ℤ))))
        (wN : H1MeanZeroFunction (openCubeSet (originCube d (M : ℤ)))),
        IsCubeDirichletResponse (originCube d (M : ℤ)) F wD →
        IsCubeNeumannResponse (originCube d (M : ℤ)) F wN →
        (vecCubeLpENorm (originCube d (M : ℤ)) 8 wD.toH1Function.grad +
              vecCubeLpENorm (originCube d (M : ℤ)) 8 wN.toH1Function.grad ≤
            Capriori * vecCubeLpENorm (originCube d (M : ℤ)) 8 F) ∧
        (∀ (DF : Fin d → Vec d → Vec d)
            (HD : HasWeakHessianOn (openCubeSet (originCube d (M : ℤ)))
              wD.toH1Function),
            (∀ i, HasWeakGradientOn (openCubeSet (originCube d (M : ℤ)))
              (fun x => F x i) (DF i)) →
            Section2.Norms.cubeLpENorm (originCube d (M : ℤ)) 8
                (fun x => HilbertMat.ofMat (fun i j => HD.hess i j x)) ≤
            Capriori * Section2.Norms.cubeLpENorm (originCube d (M : ℤ)) 8
                (fun x => HilbertMat.ofMat (fun i j => DF i x j))) ∧
        (Section2.Norms.cubeHsENorm (originCube d (M : ℤ)) (1 / 2)
                (hilbertifyVecField wD.toH1Function.grad) ≤
            Capriori * Section2.Norms.cubeHsENorm (originCube d (M : ℤ)) (1 / 2)
                (hilbertifyVecField F)) ∧
        (vecCubeLpENorm (originCube d (M : ℤ)) 2
              (fun x => wN.toH1Function.grad x - wD.toH1Function.grad x) ≤
            Capriori * (vecHatNegENorm (originCube d (M : ℤ))
                  (fun x => F x - volumeAverageVec
                    (cubeSet (originCube d (M : ℤ))) F)) ^ ((1 : ℝ) / 5) *
                (vecCubeLpENorm (originCube d (M : ℤ)) 4
                  (fun x => F x - volumeAverageVec
                    (cubeSet (originCube d (M : ℤ))) F)) ^ ((4 : ℝ) / 5) +
              Capriori * ‖HilbertVec.ofVec (volumeAverageVec
                  (cubeSet (originCube d (M : ℤ))) F)‖ₑ)) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (nu : ℝ) (_hnu : 0 < nu) (_hnu1 : nu ≤ 1)
        (P : ProbabilityMeasure (ShellSeq d))
        (_hPrefix : ShellLawPrefix d P) (_hJ1V2 : ShellLawJ1Restriction d P)
        (_hJ2 : ShellLawJ2 d P) (_hJ3 : ShellLawJ3 d P) (_hJ4 : ShellLawJ4 d P)
        (S : ScaleSelection) (_hSorder : ScalesOrdering S)
        (e : Vec d) (_he : vecNormSq e = 1)
        (p : Vec d) (_hp : p = testVector nu S.LPrime P S.n e)
        (w : ShellSeq d → H10Function (openCubeSet (originCube d (S.m : ℤ))))
        (_hw : ∀ omega : ShellSeq d,
          IsDirichletResponse omega S.LPrime S.ellPrime S.m p (w omega))
        (_hKmnLp8 : ∃ X : ShellSeq d → ℝ, Measurable X ∧
          IsBigO P.toMeasure (gammaSigma 2) X
            (C8 * (8 : ℝ) ^ ((1 : ℝ) / 2) *
              (((S.m - 1) - S.ellPrime : ℕ) : ℝ) ^ ((1 : ℝ) / 2) *
              (3 : ℝ) ^ (-((d : ℝ) / (2 * 8) *
                ((S.m - (S.m - 1) : ℕ) : ℝ)))) ∧
          ∀ omega : ShellSeq d,
            Section2.Norms.cubeLpENorm (originCube d (S.m : ℤ))
                (ENNReal.ofReal 8)
                (fun x => (finiteShellIncrement omega S.ellPrime (S.m - 1) x :
                  Mat d)) ≤
              ENNReal.ofReal
                (C8 * (((S.m - 1) - S.ellPrime : ℕ) : ℝ) ^ ((1 : ℝ) / 2) +
                  X omega))
        (_hKmnLp2 : ∃ X : ShellSeq d → ℝ, Measurable X ∧
          IsBigO P.toMeasure (gammaSigma 2) X
            (C2 * (2 : ℝ) ^ ((1 : ℝ) / 2) *
              (((S.m - 1) - S.ellPrime : ℕ) : ℝ) ^ ((1 : ℝ) / 2) *
              (3 : ℝ) ^ (-((d : ℝ) / (2 * 2) *
                ((S.m - (S.m - 1) : ℕ) : ℝ)))) ∧
          ∀ omega : ShellSeq d,
            Section2.Norms.cubeLpENorm (originCube d (S.m : ℤ))
                (ENNReal.ofReal 2)
                (fun x => (finiteShellIncrement omega S.ellPrime (S.m - 1) x :
                  Mat d)) ≤
              ENNReal.ofReal
                (C2 * (((S.m - 1) - S.ellPrime : ℕ) : ℝ) ^ ((1 : ℝ) / 2) +
                  X omega))
        (_hKmnHs : ∃ X : ShellSeq d → ℝ, Measurable X ∧
          IsBigO P.toMeasure (gammaSigma 2) X
            (CH * (3 : ℝ) ^ (-(((1 : ℝ) / 2) * (S.ellPrime : ℝ)))) ∧
          ∀ᵐ omega ∂P.toMeasure,
            (⨆ M : {M : ℕ // S.ellPrime < M},
              Section2.Norms.cubeEuclideanGagliardoESeminorm
                (originCube d (S.m : ℤ)) ((1 : ℝ) / 2) 2
                (fun x => (finiteShellIncrement omega S.ellPrime M.1 x :
                  Mat d))) ≤
              ENNReal.ofReal (X omega)),
        (∃ Z : ShellSeq d → ℝ, Measurable Z ∧
            IsBigO P.toMeasure (gammaSigma 2) Z
              (C * (Real.sqrt (vecNormSq p) * (S.h : ℝ) ^ ((1 : ℝ) / 2))) ∧
          ∀ omega : ShellSeq d,
            vecCubeLpENorm (originCube d (S.m : ℤ)) 8
                (w omega).toH1Function.grad ≤ ENNReal.ofReal (Z omega)) ∧
        (∀ (HD : ∀ omega : ShellSeq d,
              HasWeakHessianOn (openCubeSet (originCube d (S.m : ℤ)))
                (w omega).toH1Function),
          ∃ Z : ShellSeq d → ℝ, Measurable Z ∧
            IsBigO P.toMeasure (gammaSigma 2) Z
              (C * (Real.sqrt (vecNormSq p) *
                (Real.sqrt (1 + (S.h : ℝ)) *
                  (3 : ℝ) ^ (-(S.ellPrime : ℝ))))) ∧
            ∀ omega : ShellSeq d,
              Section2.Norms.cubeLpENorm (originCube d (S.m : ℤ)) 8
                  (fun x => HilbertMat.ofMat
                    (fun i j => (HD omega).hess i j x)) ≤
                ENNReal.ofReal (Z omega)) ∧
        (∃ Z : ShellSeq d → ℝ, Measurable Z ∧
            IsBigO P.toMeasure (gammaSigma 2) Z
              (C * (Real.sqrt (vecNormSq p) *
                (3 : ℝ) ^ (-((S.ellPrime : ℝ) / 2)))) ∧
          ∀ᵐ omega ∂P.toMeasure,
            Section2.Norms.cubeHsENorm (originCube d (S.m : ℤ)) ((1 : ℝ) / 2)
                (hilbertifyVecField (w omega).toH1Function.grad) ≤
              ENNReal.ofReal (Z omega)) := by

  refine ⟨regboundsWindowConst d Capriori.toReal C8 C2 CH,
    one_le_regboundsWindowConst _ _ _ _ _, ?_⟩
  intro nu hnu hnu1 P hPrefix hJ1V2 hJ2 hJ3 hJ4 S hSorder ee he p hp w hw
    hKmnLp8 hKmnLp2 hKmnHs
  have hdpos : 0 < d := by omega
  have hsw1 : (1 : ℝ) ≤ Real.sqrt (1 + (S.h : ℝ)) := by
    have h1 : (1 : ℝ) ≤ 1 + (S.h : ℝ) := by
      linarith only [(Nat.cast_nonneg S.h : (0 : ℝ) ≤ (S.h : ℝ))]
    calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
      _ ≤ Real.sqrt (1 + (S.h : ℝ)) := Real.sqrt_le_sqrt h1
  have hCnW : 0 < nablaKmnLowWindowConst d S.h :=
    nablaKmnLowWindowConst_pos hdpos S.h
  have hNablaKmnLow := nablaKmnLow_bridge hPrefix hJ3 hSorder.ellPrime_lt_m p
    (le_refl (nablaKmnLowWindowConst d S.h))
  have _ := hnu1
  have _ := hJ1V2
  have hgpos : (0 : ℝ) < gammaTriangleConst 2 :=
    IndependentSums.gammaTriangleConst_pos (σ := 2)
  have hCa0 : (0 : ℝ) ≤ Capriori.toReal := ENNReal.toReal_nonneg
  have hCane : Capriori ≠ ⊤ := hCapriori.ne
  have hCaMul : ∀ y : ℝ,
      Capriori * ENNReal.ofReal y = ENNReal.ofReal (Capriori.toReal * y) := by
    intro y
    rw [ENNReal.ofReal_mul hCa0, ENNReal.ofReal_toReal hCane]
  have hpsq : 0 < vecNormSq p := by
    rw [hp, vecNormSq_testVector hnu S.LPrime hPrefix hJ2 hJ3 hJ4 S.n he]
    exact sigmaBarStarInvSeq_pos hnu S.LPrime hPrefix hJ2 hJ3 hJ4 S.n
  have hsqrt : Real.sqrt (vecNormSq p) = vecNorm p := by
    rw [← vecNorm_sq_eq_vecNormSq, Real.sqrt_sq (vecNorm_nonneg p)]
  have hpn : 0 < vecNorm p := by
    rcases (vecNorm_nonneg p).lt_or_eq with h1 | h1
    · exact h1
    · rw [← vecNorm_sq_eq_vecNormSq, ← h1] at hpsq
      norm_num at hpsq
  have hSh : 1 ≤ S.h := scalesOrdering_one_le_h hSorder
  have hhpos : (0 : ℝ) < ((S.h : ℕ) : ℝ) ^ ((1 : ℝ) / 2) := rpow_h_pos hSorder
  have hprod : (0 : ℝ) ≤ vecNorm p * ((S.h : ℕ) : ℝ) ^ ((1 : ℝ) / 2) :=
    mul_nonneg hpn.le hhpos.le
  have hfullle : S.ellPrime ≤ S.LPrime := by
    have h1 := hSorder.ellPrime_lt_m
    have h2 := hSorder.m_lt_LPrime
    omega
  -- the amplitude of the gate's `Γ₂` part is `|C| r^{1/2} (m−1−ℓ')^{1/2}` at most
  have hAbound : ∀ Cq r : ℝ, 0 < r →
      |Cq * r ^ ((1 : ℝ) / 2) *
          (((S.m - 1) - S.ellPrime : ℕ) : ℝ) ^ ((1 : ℝ) / 2) *
          (3 : ℝ) ^ (-((d : ℝ) / (2 * r) * ((S.m - (S.m - 1) : ℕ) : ℝ)))| ≤
        (|Cq| * r ^ ((1 : ℝ) / 2)) *
          (((S.m - 1) - S.ellPrime : ℕ) : ℝ) ^ ((1 : ℝ) / 2) := by
    intro Cq r hr
    have ht0 : (0 : ℝ) ≤ (((S.m - 1) - S.ellPrime : ℕ) : ℝ) ^ ((1 : ℝ) / 2) :=
      Real.rpow_nonneg (Nat.cast_nonneg _) _
    have hr0 : (0 : ℝ) ≤ r ^ ((1 : ℝ) / 2) := Real.rpow_nonneg hr.le _
    have hexp : (0 : ℝ) ≤ (d : ℝ) / (2 * r) * ((S.m - (S.m - 1) : ℕ) : ℝ) := by
      have h2r : (0 : ℝ) < 2 * r := by linarith only [hr]
      positivity
    have he1 : (3 : ℝ) ^ (-((d : ℝ) / (2 * r) *
        ((S.m - (S.m - 1) : ℕ) : ℝ))) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
        (by linarith only [hexp])
    have hepos : (0 : ℝ) < (3 : ℝ) ^ (-((d : ℝ) / (2 * r) *
        ((S.m - (S.m - 1) : ℕ) : ℝ))) := Real.rpow_pos_of_pos (by norm_num) _
    have hbase : (0 : ℝ) ≤ |Cq| * r ^ ((1 : ℝ) / 2) *
        (((S.m - 1) - S.ellPrime : ℕ) : ℝ) ^ ((1 : ℝ) / 2) :=
      mul_nonneg (mul_nonneg (abs_nonneg Cq) hr0) ht0
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hr0, abs_of_nonneg ht0,
      abs_of_nonneg hepos.le]
    calc |Cq| * r ^ ((1 : ℝ) / 2) *
          (((S.m - 1) - S.ellPrime : ℕ) : ℝ) ^ ((1 : ℝ) / 2) *
          (3 : ℝ) ^ (-((d : ℝ) / (2 * r) * ((S.m - (S.m - 1) : ℕ) : ℝ))) ≤
        |Cq| * r ^ ((1 : ℝ) / 2) *
          (((S.m - 1) - S.ellPrime : ℕ) : ℝ) ^ ((1 : ℝ) / 2) * 1 :=
          mul_le_mul_of_nonneg_left he1 hbase
      _ = (|Cq| * r ^ ((1 : ℝ) / 2)) *
          (((S.m - 1) - S.ellPrime : ℕ) : ℝ) ^ ((1 : ℝ) / 2) := by ring
  -- the two `L̲^q` clauses of the gate, normalized
  obtain ⟨X8, hX8m, hX8O, hX8le⟩ := hKmnLp8
  obtain ⟨X2, hX2m, hX2O, hX2le⟩ := hKmnLp2
  simp only [show ENNReal.ofReal (8 : ℝ) = (8 : ℝ≥0∞) by norm_num] at hX8le
  simp only [show ENNReal.ofReal (2 : ℝ) = (2 : ℝ≥0∞) by norm_num] at hX2le
  obtain ⟨Y8, hY8m, hY8nn, hY8O, hY8le⟩ :=
    exists_normalized_witness_gateLp (P := P) (S := S) (q := (8 : ℝ≥0∞))
      (by positivity) hSh hX8m hX8O (hAbound C8 8 (by norm_num)) hX8le
  obtain ⟨Y2, hY2m, hY2nn, hY2O, hY2le⟩ :=
    exists_normalized_witness_gateLp (P := P) (S := S) (q := (2 : ℝ≥0∞))
      (by positivity) hSh hX2m hX2O (hAbound C2 2 (by norm_num)) hX2le
  -- the first parenthesized term at `q = 8` and at `q = 2`
  obtain ⟨Y1, hY1m, hY1nn, hY1O, hY1le⟩ :=
    exists_witness_vecCubeLpENorm_centeredFlux (P := P) hJ3 hSorder hpn
      (q := (8 : ℝ≥0∞)) (by norm_num)
      (regboundsGateConst_pos (C := C8) (r := 8) (by norm_num))
      hY8m hY8nn hY8O hY8le
  obtain ⟨YL2, hYL2m, hYL2nn, hYL2O, hYL2le⟩ :=
    exists_witness_vecCubeLpENorm_centeredFlux (P := P) hJ3 hSorder hpn
      (q := (2 : ℝ≥0∞)) (by norm_num)
      (regboundsGateConst_pos (C := C2) (r := 2) (by norm_num))
      hY2m hY2nn hY2O hY2le
  -- the third parenthesized term
  obtain ⟨XH, hXHm, hXHO, hXHle⟩ := hKmnHs
  have hK2pos : (0 : ℝ) < gammaTriangleConst 2 *
      ((regboundsUpperConst d + 1) + regboundsGateConst C2 2) := by
    have h1 : (0 : ℝ) ≤ regboundsUpperConst d := regboundsUpperConst_nonneg d
    have h2 : (0 : ℝ) < regboundsGateConst C2 2 :=
      regboundsGateConst_pos (C := C2) (r := 2) (by norm_num)
    exact mul_pos hgpos (by linarith only [h1, h2])
  obtain ⟨Y3, hY3m, hY3nn, hY3O, hY3le⟩ :=
    exists_witness_cubeHsENorm_centeredFlux (P := P) hSorder hpn hK2pos
      hYL2m hYL2nn hYL2O hYL2le hCH hXHm hXHO hXHle
  -- the second parenthesized term
  obtain ⟨Zn, hZnm, hZnO, hZnle⟩ := hNablaKmnLow
  rw [hsqrt] at hZnO
  obtain ⟨YJ, hYJm, hYJnn, hYJO, hYJle⟩ :=
    exists_witness_cubeLpENorm_fluxJacobian (P := P) hJ3 hSorder hpn hCnW
      (Yn := fun omega => |Zn omega|) (measurable_abs_of hZnm)
      (fun omega => abs_nonneg _) (isBigO_gammaSigma_abs.2 hZnO)
      (fun omega =>
        le_trans (hZnle omega) (ENNReal.ofReal_le_ofReal (le_abs_self _)))
  -- the response is the Dirichlet response of the flux and of its centering
  have hDir : ∀ omega : ShellSeq d,
      IsCubeDirichletResponse (originCube d (S.m : ℤ))
        (fun x => matVecMul (streamCutoff omega S.LPrime x -
          streamCutoff omega S.ellPrime x) p) (w omega) := hw
  have hMem : ∀ omega : ShellSeq d,
      MemVectorL2 (openCubeSet (originCube d (S.m : ℤ)))
        (fun x => matVecMul (streamCutoff omega S.LPrime x -
          streamCutoff omega S.ellPrime x) p) := fun omega =>
    memVectorL2_dirichletRhsField omega S.LPrime S.ellPrime S.m p
  have hMemC : ∀ omega : ShellSeq d,
      MemVectorL2 (openCubeSet (originCube d (S.m : ℤ)))
        (fun x => matVecMul (streamCutoff omega S.LPrime x -
            streamCutoff omega S.ellPrime x) p -
          volumeAverageVec (cubeSet (originCube d (S.m : ℤ)))
            (fun y => matVecMul (streamCutoff omega S.LPrime y -
              streamCutoff omega (S.m - 1) y) p)) := fun omega =>
    (hMem omega).sub (MeasureTheory.memLp_const
      (μ := volumeMeasureOn (openCubeSet (originCube d (S.m : ℤ))))
      (c := volumeAverageVec (cubeSet (originCube d (S.m : ℤ)))
        (fun y => matVecMul (streamCutoff omega S.LPrime y -
          streamCutoff omega (S.m - 1) y) p)))
  have hDirC : ∀ omega : ShellSeq d,
      IsCubeDirichletResponse (originCube d (S.m : ℤ))
        (fun x => matVecMul (streamCutoff omega S.LPrime x -
            streamCutoff omega S.ellPrime x) p -
          volumeAverageVec (cubeSet (originCube d (S.m : ℤ)))
            (fun y => matVecMul (streamCutoff omega S.LPrime y -
              streamCutoff omega (S.m - 1) y) p)) (w omega) := fun omega =>
    (isCubeDirichletResponse_sub_const_iff (hMem omega) _).1 (hDir omega)
  refine ⟨⟨fun omega => Capriori.toReal * Y1 omega,
      Measurable.const_mul hY1m _, ?_, ?_⟩,
    ?_, ⟨fun omega => Capriori.toReal * Y3 omega,
      Measurable.const_mul hY3m _, ?_, ?_⟩⟩
  · refine (hY1O.const_mul hCa0).mono_scale ?_
    rw [hsqrt]
    have hc : Capriori.toReal * (gammaTriangleConst 2 *
        ((regboundsUpperConst d + 1) + regboundsGateConst C8 8)) ≤
        regboundsWindowConst d Capriori.toReal C8 C2 CH := by
      rw [regboundsWindowConst, regboundsConst]
      exact le_trans (le_max_left _ _) (le_max_right _ _)
    calc Capriori.toReal * ((gammaTriangleConst 2 *
            ((regboundsUpperConst d + 1) + regboundsGateConst C8 8)) *
          (vecNorm p * ((S.h : ℕ) : ℝ) ^ ((1 : ℝ) / 2))) =
        (Capriori.toReal * (gammaTriangleConst 2 *
            ((regboundsUpperConst d + 1) + regboundsGateConst C8 8))) *
          (vecNorm p * ((S.h : ℕ) : ℝ) ^ ((1 : ℝ) / 2)) := by ring
      _ ≤ regboundsWindowConst d Capriori.toReal C8 C2 CH *
          (vecNorm p * ((S.h : ℕ) : ℝ) ^ ((1 : ℝ) / 2)) :=
        mul_le_mul_of_nonneg_right hc hprod
  · intro omega
    obtain ⟨wN, hwN⟩ :=
      exists_isCubeNeumannResponse (originCube d (S.m : ℤ)) (hMemC omega)
    have hap := hApriori S.m
      (fun x => matVecMul (streamCutoff omega S.LPrime x -
          streamCutoff omega S.ellPrime x) p -
        volumeAverageVec (cubeSet (originCube d (S.m : ℤ)))
          (fun y => matVecMul (streamCutoff omega S.LPrime y -
            streamCutoff omega (S.m - 1) y) p))
      (w omega) wN (hDirC omega) hwN
    refine le_trans (le_trans le_self_add hap.1) ?_
    refine le_trans (mul_le_mul' le_rfl (hY1le omega)) ?_
    exact le_of_eq (hCaMul (Y1 omega))
  · intro HD
    refine ⟨fun omega => Capriori.toReal * YJ omega,
      Measurable.const_mul hYJm _, ?_, ?_⟩
    · refine (hYJO.const_mul hCa0).mono_scale ?_
      rw [hsqrt]
      have hdecnn : (0 : ℝ) ≤ vecNorm p * (3 : ℝ) ^ (-(S.ellPrime : ℝ)) :=
        mul_nonneg hpn.le (Real.rpow_pos_of_pos (by norm_num) _).le
      have hsw0 : (0 : ℝ) ≤ Real.sqrt (1 + (S.h : ℝ)) :=
        le_trans zero_le_one hsw1
      have hJ0 : (0 : ℝ) ≤ regboundsJacobianConst d :=
        (regboundsJacobianConst_pos d).le
      have hstep : regboundsJacobianConst d + nablaKmnLowWindowConst d S.h ≤
          (regboundsJacobianConst d + nablaKmnLowSumConst d) *
            Real.sqrt (1 + (S.h : ℝ)) := by
        have hJsw : regboundsJacobianConst d ≤
            regboundsJacobianConst d * Real.sqrt (1 + (S.h : ℝ)) :=
          le_mul_of_one_le_right hJ0 hsw1
        have hexp : (regboundsJacobianConst d + nablaKmnLowSumConst d) *
            Real.sqrt (1 + (S.h : ℝ)) =
            regboundsJacobianConst d * Real.sqrt (1 + (S.h : ℝ)) +
              nablaKmnLowSumConst d * Real.sqrt (1 + (S.h : ℝ)) := by ring
        rw [hexp, nablaKmnLowWindowConst_eq]
        linarith only [hJsw]
      have hc : Capriori.toReal * (gammaTriangleConst 2 *
          (regboundsJacobianConst d + nablaKmnLowSumConst d)) ≤
          regboundsWindowConst d Capriori.toReal C8 C2 CH := by
        rw [regboundsWindowConst, regboundsConst]
        exact le_trans (le_trans (le_max_left _ _) (le_max_right _ _))
          (le_max_right _ _)
      calc Capriori.toReal * ((gammaTriangleConst 2 *
              (regboundsJacobianConst d + nablaKmnLowWindowConst d S.h)) *
            (vecNorm p * (3 : ℝ) ^ (-(S.ellPrime : ℝ)))) ≤
          Capriori.toReal * ((gammaTriangleConst 2 *
              ((regboundsJacobianConst d + nablaKmnLowSumConst d) *
                Real.sqrt (1 + (S.h : ℝ)))) *
            (vecNorm p * (3 : ℝ) ^ (-(S.ellPrime : ℝ)))) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hstep hgpos.le) hdecnn) hCa0
        _ = (Capriori.toReal * (gammaTriangleConst 2 *
              (regboundsJacobianConst d + nablaKmnLowSumConst d))) *
            (Real.sqrt (1 + (S.h : ℝ)) *
              (vecNorm p * (3 : ℝ) ^ (-(S.ellPrime : ℝ)))) := by ring
        _ ≤ regboundsWindowConst d Capriori.toReal C8 C2 CH *
            (Real.sqrt (1 + (S.h : ℝ)) *
              (vecNorm p * (3 : ℝ) ^ (-(S.ellPrime : ℝ)))) :=
          mul_le_mul_of_nonneg_right hc (mul_nonneg hsw0 hdecnn)
        _ = regboundsWindowConst d Capriori.toReal C8 C2 CH *
            (vecNorm p * (Real.sqrt (1 + (S.h : ℝ)) *
              (3 : ℝ) ^ (-(S.ellPrime : ℝ)))) := by ring
    · intro omega
      obtain ⟨wN, hwN⟩ :=
        exists_isCubeNeumannResponse (originCube d (S.m : ℤ)) (hMem omega)
      have hap := hApriori S.m
        (fun x => matVecMul (streamCutoff omega S.LPrime x -
          streamCutoff omega S.ellPrime x) p) (w omega) wN (hDir omega) hwN
      have hhess := hap.2.1
        (streamFluxWeakGradient omega S.ellPrime S.LPrime p) (HD omega)
        (fun i => hasWeakGradientOn_streamFluxWeakGradient omega hfullle p i
          (openCubeSet (originCube d (S.m : ℤ))))
      refine le_trans hhess ?_
      refine le_trans (mul_le_mul' le_rfl (hYJle omega)) ?_
      exact le_of_eq (hCaMul (YJ omega))
  · refine (hY3O.const_mul hCa0).mono_scale ?_
    rw [hsqrt]
    have hdecnn : (0 : ℝ) ≤ vecNorm p * (3 : ℝ) ^ (-((S.ellPrime : ℝ) / 2)) :=
      mul_nonneg hpn.le (Real.rpow_pos_of_pos (by norm_num) _).le
    have hc : Capriori.toReal * (gammaTriangleConst 2 *
        (gammaTriangleConst 2 *
          ((regboundsUpperConst d + 1) + regboundsGateConst C2 2) + CH)) ≤
        regboundsWindowConst d Capriori.toReal C8 C2 CH := by
      rw [regboundsWindowConst, regboundsConst]
      exact le_trans (le_trans (le_max_right _ _) (le_max_right _ _))
        (le_max_right _ _)
    calc Capriori.toReal * ((gammaTriangleConst 2 *
            (gammaTriangleConst 2 *
              ((regboundsUpperConst d + 1) + regboundsGateConst C2 2) + CH)) *
          (vecNorm p * (3 : ℝ) ^ (-((S.ellPrime : ℝ) / 2)))) =
        (Capriori.toReal * (gammaTriangleConst 2 *
            (gammaTriangleConst 2 *
              ((regboundsUpperConst d + 1) + regboundsGateConst C2 2) + CH))) *
          (vecNorm p * (3 : ℝ) ^ (-((S.ellPrime : ℝ) / 2))) := by ring
      _ ≤ regboundsWindowConst d Capriori.toReal C8 C2 CH *
          (vecNorm p * (3 : ℝ) ^ (-((S.ellPrime : ℝ) / 2))) :=
        mul_le_mul_of_nonneg_right hc hdecnn
  · filter_upwards [hY3le] with omega homega
    obtain ⟨wN, hwN⟩ :=
      exists_isCubeNeumannResponse (originCube d (S.m : ℤ)) (hMemC omega)
    have hap := hApriori S.m
      (fun x => matVecMul (streamCutoff omega S.LPrime x -
          streamCutoff omega S.ellPrime x) p -
        volumeAverageVec (cubeSet (originCube d (S.m : ℤ)))
          (fun y => matVecMul (streamCutoff omega S.LPrime y -
            streamCutoff omega (S.m - 1) y) p))
      (w omega) wN (hDirC omega) hwN
    refine le_trans hap.2.2.1 ?_
    refine le_trans (mul_le_mul' le_rfl homega) ?_
    exact le_of_eq (hCaMul (Y3 omega))

end

end SuperdiffusionCLT.Section3.ResponseFields

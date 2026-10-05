/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.RHSTerm3OscCg
public import SuperdiffusionCLT.Section3.Terms.RHSTerm3InputsB
public import SuperdiffusionCLT.Section3.ResponseFields.RegboundsWindowB

/-!
# `hNablawFour` of `e.RHS.term3.A`: the fourth moment of the response Hessian

The proof of the printed display `e.RHS.term3.A` uses the following display.  The
obligation `_hNablawFour` of the constant-first term-3 assembly is
that display,

`(E[‖∇²w‖⁴_{L̲⁴(cu_m)}])^{1/4} ≤ C_w ν^{-1/2} 3^{-ℓ'}`,

read at the carrier `hessianL4` of the term-3.A carriers.  The printed
quantity is the **Hessian** — the `L̲⁴` norm of `∇²w` on the cube `cu_m` — so of
the three clauses of `e.nablaw.Lt` the only one that can supply it is the
second, the Hessian clause (`∇w` and its fractional `H̲^{1/2}` norm are different
quantities).

## Main statements

* `hessW4_fourth_moment_of_regbounds`: the fourth-moment form of the second
  clause of `e.nablaw.Lt`, with the constant `nablaW4Const` explicit; the
  `k = 4` analogue of `hessW3_third_moment_of_regbounds`.
* `hNablawFour_of_regbounds`: the fourth root at the printed rate
  `3^{-ℓ'} ν^{-1/2}`, at the constant `hessW4RootConst C`, from the clause in
  its exact shape.
* `hNablawFour_of_window`: the same with **every** analytic input discharged
  from `l_w_basic_regbounds_window`
  (`Section3/ResponseFields/RegboundsWindowB.lean`); the only hypotheses left
  are the ambient setting of the two-scale statement.

## The window factor

The second clause of `e.nablaw.Lt` carries the union-bound loss `√(1 + h)` on its
amplitude (as in the statement proved in `l_w_basic_regbounds_window`), so the
fourth-root form reads

`(E[‖∇²w‖⁴])^{1/4} ≤ C_w (1 + h)^{1/2} 3^{-ℓ'} ν^{-1/2}`

with `C_w = hessW4RootConst C` window-free.  The factor `(1 + h)^{1/2}` is **not**
absorbed by the machinery available at this point:
the window-factor absorption lemma (`Section3/Terms/WindowFactorAbsorption.lean`) spends a
polynomial factor `(1 + h)^α` against a *decaying* factor `3^{-h/p}`, weakening
the rate to `3^{-h/q}`.  The right side here has no such factor: `ℓ' = m - h`
(`ScaleSelection.ellPrime_add_h`), so the printed rate is
`3^{-ℓ'} = 3^{h} 3^{-m}`, which **grows** with the window,
and no weakening of it can pay for a
growing factor.  The offset absorption for `oscBoundConst` is stated for
the term-3.B constant and not for a Hessian-moment constant, so it does not
apply to `C_w` either.  Hence the factor stays in the constant and no window-free
constant is available: the obligation `_hNablawFour` with
its `C_w` quantified before the scale selection is **not** discharged here, and
`hNablawFour_of_window` is its sharpest form.

## Main results

* `hessW4_fourth_moment_of_regbounds`
* `hessW4RootConst`, `hessW4RootConst_nonneg`
* `hNablawFour_of_regbounds`, `hNablawFour_of_window`
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Terms

open MeasureTheory
open Homogenization
open Homogenization.IndependentSums
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Norms
open SuperdiffusionCLT.Section2.Estimates.Stream
open SuperdiffusionCLT.Section3.ResponseFields
open SuperdiffusionCLT.Section3.Setup
open scoped ENNReal

noncomputable section

/-! ## Fourth powers of square roots -/

/-- `(√x)⁴ = x²` for `x ≥ 0`. -/
private theorem sqrt_pow_four {x : ℝ} (hx : 0 ≤ x) :
    Real.sqrt x ^ (4 : ℕ) = x ^ (2 : ℕ) := by
  have h2 : Real.sqrt x ^ (2 : ℕ) = x := Real.sq_sqrt hx
  calc Real.sqrt x ^ (4 : ℕ)
      = (Real.sqrt x ^ (2 : ℕ)) ^ (2 : ℕ) := by ring
    _ = x ^ (2 : ℕ) := by rw [h2]

/-- `(x²)^{1/4} = x^{1/2}` for `x ≥ 0`, the inverse direction of `sqrt_pow_four`
in the spelling produced by `Real.mul_rpow`. -/
private theorem sq_rpow_quarter {x : ℝ} (hx : 0 ≤ x) :
    (x ^ (2 : ℕ)) ^ ((1 : ℝ) / 4) = x ^ ((1 : ℝ) / 2) := by
  rw [← Real.rpow_natCast x 2, ← Real.rpow_mul hx]
  norm_num

/-- `(3^{-4t})^{1/4} = 3^{-t}`: the fourth root undoes the fourth power of the
rate of the Hessian clause. -/
private theorem three_rpow_neg_four_mul_rpow_quarter (t : ℝ) :
    ((3 : ℝ) ^ (-(4 * t))) ^ ((1 : ℝ) / 4) = (3 : ℝ) ^ (-t) := by
  rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3),
    show -(4 * t) * ((1 : ℝ) / 4) = -t by ring]

/-! ## The fourth moment of the response Hessian on `cu_m` -/

/-- The constant of the fourth-root form of the second clause of
`e.nablaw.Lt`: the fourth root of the fourth-moment constant `nablaW4Const`. -/
def hessW4RootConst (C : ℝ) : ℝ := (nablaW4Const C) ^ ((1 : ℝ) / 4)

/-- The constant is nonnegative as soon as `C ≥ 1`. -/
theorem hessW4RootConst_nonneg {C : ℝ} (hC : 1 ≤ C) : 0 ≤ hessW4RootConst C :=
  Real.rpow_nonneg (le_trans zero_le_one (one_le_nablaW4Const hC)) _

/-- **`E[‖∇²w‖⁴_{L̲⁸(cu_m)}] ≤ C⁴(1 + Γ(3))(1 + h)²|p|⁴3^{-4ℓ'}`**, the
fourth-moment form of the **second** clause of `e.nablaw.Lt`, which is the input the
display reads.

`hZmeas`, `hZbigO`, `hZbound` are that clause in its exact shape, i.e. the
second conclusion of `l_w_basic_regbounds_window`
(`Section3/ResponseFields/RegboundsWindowB.lean`) at the constant `C`: an
`L̲⁸(cu_m)` bound on the response Hessian by a `Γ₂` envelope of amplitude
`C|p|√(1 + h)3^{-ℓ'}`.  The exponent `8` is the one of the clause, which
dominates the printed `L̲⁴` norm.  The factor `√(1 + h)` is the
union-bound loss on the amplitude of that clause; it is carried to the conclusion as
`(1 + h)²`.  The moment is the `lintegral` of the fourth power of the
extended-real cube norm, so no measurability in `ω` is needed. -/
theorem hessW4_fourth_moment_of_regbounds
    {d : ℕ} [NeZero d] {P : ProbabilityMeasure (ShellSeq d)} {S : ScaleSelection}
    {p : Vec d} (hq : 0 < vecNormSq p) (H : ShellSeq d → Vec d → HilbertMat d)
    {C : ℝ} (hC : 0 < C) {Z : ShellSeq d → ℝ} (hZmeas : Measurable Z)
    (hZbigO : IsBigO P.toMeasure (gammaSigma 2) Z
      (C * (Real.sqrt (vecNormSq p) *
        (Real.sqrt (1 + (S.h : ℝ)) * (3 : ℝ) ^ (-(S.ellPrime : ℝ))))))
    (hZbound : ∀ omega : ShellSeq d,
      cubeLpENorm (originCube d (S.m : ℤ)) 8 (H omega) ≤ ENNReal.ofReal (Z omega)) :
    (∫⁻ omega : ShellSeq d,
        cubeLpENorm (originCube d (S.m : ℤ)) 8 (H omega) ^ (4 : ℕ) ∂P.toMeasure).toReal ≤
      nablaW4Const C * ((1 + (S.h : ℝ)) ^ (2 : ℕ) *
        (vecNormSq p ^ (2 : ℕ) * (3 : ℝ) ^ (-(4 * (S.ellPrime : ℝ))))) := by
  have hh0 : (0 : ℝ) < 1 + (S.h : ℝ) := by
    have := (Nat.cast_nonneg S.h : (0 : ℝ) ≤ (S.h : ℝ))
    linarith only [this]
  have h3pos : (0 : ℝ) < (3 : ℝ) ^ (-(S.ellPrime : ℝ)) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hA : (0 : ℝ) < C * (Real.sqrt (vecNormSq p) *
      (Real.sqrt (1 + (S.h : ℝ)) * (3 : ℝ) ^ (-(S.ellPrime : ℝ)))) :=
    mul_pos hC (mul_pos (Real.sqrt_pos.2 hq) (mul_pos (Real.sqrt_pos.2 hh0) h3pos))
  have hmom := toReal_lintegral_pow_le_of_isBigO_gammaSigma_two hA hZmeas.aemeasurable
    hZbigO hZbound 4
  refine hmom.trans_eq ?_
  have hthree : ((3 : ℝ) ^ (-(S.ellPrime : ℝ))) ^ (4 : ℕ) =
      (3 : ℝ) ^ (-(4 * (S.ellPrime : ℝ))) := by
    rw [← Real.rpow_natCast ((3 : ℝ) ^ (-(S.ellPrime : ℝ))) 4,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    ring_nf
  rw [Real.rpow_natCast, show (((4 : ℕ) : ℝ)) / 2 + 1 = 3 by norm_num,
    mul_pow, mul_pow, mul_pow, sqrt_pow_four (le_of_lt hq),
    sqrt_pow_four (le_of_lt hh0), hthree, nablaW4Const]
  ring

/-! ## `hNablawFour` at the printed rate -/

/-- **`hNablawFour` of the constant-first term-3 assembly**, the printed display
at the constant
`hessW4RootConst C`:

`(E[‖∇²w‖⁴_{L̲⁸(cu_m)}])^{1/4} ≤ C_w (1 + h)^{1/2} 3^{-ℓ'} ν^{-1/2}`.

The hypotheses `hZmeas`, `hZbigO`, `hZbound` are the second clause of
`e.nablaw.Lt` in its exact shape (the second conclusion of
`l_w_basic_regbounds_window`); the passage from `|p|²` to `ν^{-1}` is the crude
bound `shom_{L',*}^{-1}(cu_n) ≤ ν^{-1}` (`sigmaBarStarInvSeq_le_nuInv`), which
uses the test-vector identity `hp` and the shell laws.  The window factor
`(1 + h)^{1/2}` is **not** part of `C_w`; it is displayed explicitly on the right
side, since it cannot be absorbed (see the module docstring). -/
theorem hNablawFour_of_regbounds
    {d : ℕ} [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    {P : ProbabilityMeasure (ShellSeq d)} (hPrefix : ShellLawPrefix d P)
    (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P)
    {S : ScaleSelection} {e : Vec d} (he : vecNormSq e = 1)
    {p : Vec d} (hp : p = testVector nu S.LPrime P S.n e)
    (H : ShellSeq d → Vec d → HilbertMat d)
    {C : ℝ} (hC : 1 ≤ C) {Z : ShellSeq d → ℝ} (hZmeas : Measurable Z)
    (hZbigO : IsBigO P.toMeasure (gammaSigma 2) Z
      (C * (Real.sqrt (vecNormSq p) *
        (Real.sqrt (1 + (S.h : ℝ)) * (3 : ℝ) ^ (-(S.ellPrime : ℝ))))))
    (hZbound : ∀ omega : ShellSeq d,
      cubeLpENorm (originCube d (S.m : ℤ)) 8 (H omega) ≤ ENNReal.ofReal (Z omega)) :
    (∫⁻ omega : ShellSeq d,
        cubeLpENorm (originCube d (S.m : ℤ)) 8 (H omega) ^ (4 : ℕ) ∂P.toMeasure).toReal ^
        ((1 : ℝ) / 4) ≤
      hessW4RootConst C * (1 + (S.h : ℝ)) ^ ((1 : ℝ) / 2) *
        (3 : ℝ) ^ (-(S.ellPrime : ℝ)) * nu ^ (-(1 / 2 : ℝ)) := by
  have hh0 : (0 : ℝ) < 1 + (S.h : ℝ) := by
    have := (Nat.cast_nonneg S.h : (0 : ℝ) ≤ (S.h : ℝ))
    linarith only [this]
  have hpsq : vecNormSq p = sigmaBarStarInvSeq nu S.LPrime P S.n := by
    rw [hp]
    exact vecNormSq_testVector hnu S.LPrime hPrefix hJ2 hJ3 hJ4 S.n he
  have hq : 0 < vecNormSq p := by
    rw [hpsq]
    exact sigmaBarStarInvSeq_pos hnu S.LPrime hPrefix hJ2 hJ3 hJ4 S.n
  have hC0 : (0 : ℝ) < C := lt_of_lt_of_le (by norm_num) hC
  have hM := hessW4_fourth_moment_of_regbounds (P := P) hq H hC0 hZmeas hZbigO hZbound
  have hMn : (0 : ℝ) ≤ (∫⁻ omega : ShellSeq d,
      cubeLpENorm (originCube d (S.m : ℤ)) 8 (H omega) ^ (4 : ℕ) ∂P.toMeasure).toReal :=
    ENNReal.toReal_nonneg
  have hroot := Real.rpow_le_rpow hMn hM (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 4)
  -- the crude bound `|p|² ≤ ν^{-1}`, then its square root
  have hqle : vecNormSq p ^ ((1 : ℝ) / 2) ≤ nu ^ (-(1 / 2 : ℝ)) := by
    have hcrude : vecNormSq p ≤ nu⁻¹ := by
      rw [hpsq]
      exact sigmaBarStarInvSeq_le_nuInv hnu S.LPrime hPrefix hJ2 hJ3 hJ4 S.n
    have hstep := Real.rpow_le_rpow (le_of_lt hq) hcrude
      (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 2)
    rwa [Real.inv_rpow (le_of_lt hnu), ← Real.rpow_neg (le_of_lt hnu)] at hstep
  -- the split of the fourth root of the constant
  have hK : (0 : ℝ) ≤ nablaW4Const C := le_trans zero_le_one (one_le_nablaW4Const hC)
  have h1h : (0 : ℝ) ≤ (1 + (S.h : ℝ)) ^ (2 : ℕ) := pow_nonneg hh0.le 2
  have h3 : (0 : ℝ) ≤ (3 : ℝ) ^ (-(4 * (S.ellPrime : ℝ))) := Real.rpow_nonneg (by norm_num) _
  have hq2 : (0 : ℝ) ≤ vecNormSq p ^ (2 : ℕ) := pow_nonneg (le_of_lt hq) 2
  have h2 : (0 : ℝ) ≤ vecNormSq p ^ (2 : ℕ) * (3 : ℝ) ^ (-(4 * (S.ellPrime : ℝ))) :=
    mul_nonneg hq2 h3
  have h2' : (0 : ℝ) ≤ (1 + (S.h : ℝ)) ^ (2 : ℕ) *
      (vecNormSq p ^ (2 : ℕ) * (3 : ℝ) ^ (-(4 * (S.ellPrime : ℝ)))) :=
    mul_nonneg h1h h2
  have hsplit : (nablaW4Const C * ((1 + (S.h : ℝ)) ^ (2 : ℕ) *
        (vecNormSq p ^ (2 : ℕ) * (3 : ℝ) ^ (-(4 * (S.ellPrime : ℝ)))))) ^ ((1 : ℝ) / 4) =
      hessW4RootConst C * ((1 + (S.h : ℝ)) ^ ((1 : ℝ) / 2) *
        (vecNormSq p ^ ((1 : ℝ) / 2) * (3 : ℝ) ^ (-(S.ellPrime : ℝ)))) := by
    rw [Real.mul_rpow hK h2', Real.mul_rpow h1h h2, Real.mul_rpow hq2 h3,
      sq_rpow_quarter hh0.le, sq_rpow_quarter (le_of_lt hq),
      three_rpow_neg_four_mul_rpow_quarter (S.ellPrime : ℝ), hessW4RootConst]
  -- the amplitude comparison and the reordering of the right side
  have h1hnn : (0 : ℝ) ≤ (1 + (S.h : ℝ)) ^ ((1 : ℝ) / 2) := Real.rpow_nonneg hh0.le _
  have h3nn : (0 : ℝ) ≤ (3 : ℝ) ^ (-(S.ellPrime : ℝ)) := Real.rpow_nonneg (by norm_num) _
  refine hroot.trans ?_
  calc (nablaW4Const C * ((1 + (S.h : ℝ)) ^ (2 : ℕ) *
        (vecNormSq p ^ (2 : ℕ) * (3 : ℝ) ^ (-(4 * (S.ellPrime : ℝ)))))) ^ ((1 : ℝ) / 4)
      = hessW4RootConst C * ((1 + (S.h : ℝ)) ^ ((1 : ℝ) / 2) *
          (vecNormSq p ^ ((1 : ℝ) / 2) * (3 : ℝ) ^ (-(S.ellPrime : ℝ)))) := hsplit
    _ ≤ hessW4RootConst C * ((1 + (S.h : ℝ)) ^ ((1 : ℝ) / 2) *
          (nu ^ (-(1 / 2 : ℝ)) * (3 : ℝ) ^ (-(S.ellPrime : ℝ)))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hqle h3nn) h1hnn)
          (hessW4RootConst_nonneg hC)
    _ = hessW4RootConst C * (1 + (S.h : ℝ)) ^ ((1 : ℝ) / 2) *
          (3 : ℝ) ^ (-(S.ellPrime : ℝ)) * nu ^ (-(1 / 2 : ℝ)) := by ring

/-! ## `hNablawFour` with every analytic input discharged -/

/-- **`hNablawFour` with every analytic input discharged.**  The second clause
of `e.nablaw.Lt` is read from `l_w_basic_regbounds_window`, whose every input is
supplied by proved theorems, so nothing is left beyond the ambient
setting of the two-scale statement: the dimension `2 ≤ d`, the cutoff
ellipticity, the shell laws, the scale selection, the test vector, and the
response.

The constant `C_w` is `hessW4RootConst C` at the clause constant `C` produced by
the regbounds theorem, and is window-free.  The window factor `(1 + h)^{1/2}`
stands outside it on the right side; it is not discharged here,
and no window-free constant can replace `C_w · (1 + h)^{1/2}`. -/
theorem hNablawFour_of_window (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    ∃ Cw : ℝ, 0 ≤ Cw ∧
      ∀ (nu : ℝ) (_hnu : 0 < nu) (_hnu1 : nu ≤ 1)
        (P : ProbabilityMeasure (ShellSeq d))
        (_hPrefix : ShellLawPrefix d P) (_hJ1V2 : ShellLawJ1Restriction d P)
        (_hJ2 : ShellLawJ2 d P) (_hJ3 : ShellLawJ3 d P) (_hJ4 : ShellLawJ4 d P)
        (S : ScaleSelection) (_hSorder : ScalesOrdering S)
        (e : Vec d) (_he : vecNormSq e = 1)
        (p : Vec d) (_hp : p = testVector nu S.LPrime P S.n e)
        (w : ShellSeq d → H10Function (openCubeSet (originCube d (S.m : ℤ))))
        (_hw : ∀ omega : ShellSeq d,
          IsDirichletResponse omega S.LPrime S.ellPrime S.m p (w omega)),
        (∀ (HD : ∀ omega : ShellSeq d,
              Homogenization.HasWeakHessianOn (openCubeSet (originCube d (S.m : ℤ)))
                (w omega).toH1Function),
          (∫⁻ omega : ShellSeq d,
              cubeLpENorm (originCube d (S.m : ℤ)) 8
                (fun x => HilbertMat.ofMat (fun i j => (HD omega).hess i j x)) ^ (4 : ℕ)
              ∂P.toMeasure).toReal ^ ((1 : ℝ) / 4) ≤
            Cw * (1 + (S.h : ℝ)) ^ ((1 : ℝ) / 2) *
              (3 : ℝ) ^ (-(S.ellPrime : ℝ)) * nu ^ (-(1 / 2 : ℝ))) := by
  obtain ⟨C, hC1, hreg⟩ := l_w_basic_regbounds_window d hd
  refine ⟨hessW4RootConst C, hessW4RootConst_nonneg hC1, ?_⟩
  intro nu hnu hnu1 P hPrefix hJ1V2 hJ2 hJ3 hJ4 S hSorder e he p hp w hw HD
  obtain ⟨_, hhess, _⟩ :=
    hreg nu hnu hnu1 P hPrefix hJ1V2 hJ2 hJ3 hJ4 S hSorder e he p hp w hw
  obtain ⟨Z, hZmeas, hZbigO, hZbound⟩ := hhess HD
  exact hNablawFour_of_regbounds hnu hPrefix hJ2 hJ3 hJ4 he hp
    (fun omega x => HilbertMat.ofMat (fun i j => (HD omega).hess i j x))
    hC1 hZmeas hZbigO hZbound

/-! ## The window factor of the printed rate -/

end

end SuperdiffusionCLT.Section3.Terms

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section5.Response.NeumannOscillationChain
public import SuperdiffusionCLT.Section5.Response.NeumannOscillationTail

/-!
# The oscillation bound of the Neumann field by Dirichlet comparison

Display `e.crude.Fz.bound`: the
oscillation of `∇w_{N,e'} + shom⁻¹ hshell e'` over the subcubes `z + cu_n` is controlled by the
oscillation of the Dirichlet gradient `∇w_{D,e'}` (the `W^{2,8}` clause, Poincaré), the gap
`δ = ∇w_N - ∇w_D` (interpolated between the energy gap and the `L⁸` gradient clause) and the shell
derivative (Poincaré and the stationary derivative moments).  The only input not proved here is the
energy gap `hgap`, in the shape of `abs_energy_sub_hshell_le`.

With `Kc ≥ 100 m`, `ν⁻² ≤ m` and `n = ⌊m - h - 100 log_3(ν⁻¹ m)⌋₊` the bound is
`C shom_{m-h}⁻⁴ (ν⁻¹ m)^{-400}`: the Hessian and shell terms have `3^{4n} 3^{-4(m-h)} ≤ (ν⁻¹m)^{-400}`
up to an absolute constant, and the gap term is `3^{-(Kc-m)/5}` times a polynomial.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section5

open Homogenization MeasureTheory Homogenization.Book.Ch02
open SuperdiffusionCLT.Section2.Annealed (sigmaBarInfinite)
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section3.ResponseFields
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- **`e.crude.Fz.bound`: the oscillation of the Neumann field by Dirichlet comparison.**
The expectation of the subcube average of `‖∇w_{D,e} - (∇w_{D,e})_{z+cu_n}‖⁴_{L̲⁴}` and
`‖(∇w_{N,e'} + hshell e') - (·)_{z+cu_n}‖⁴_{L̲⁴}` is at most
`C shom_{m-h}⁻⁴ (ν⁻¹ m)^{-400}`, given the energy gap `hgap` between the Neumann and the Dirichlet
gradient of the second direction. -/
theorem crude_Fz_bound [NeZero d] (hd : 2 ≤ d) (Cg : ℝ) (hCg : 0 ≤ Cg) :
    ∃ C : ℝ, 1 ≤ C ∧
    ∀ (nu : ℝ), 0 < nu → nu ≤ 1 →
    ∀ (P : ProbabilityMeasure (ShellSeq d)), ShellLawPrefix d P → ShellLawJ2 d P →
      ShellLawJ3 d P → ShellLawJ1Restriction d P → ShellLawJ4 d P →
    ∀ m h Kc : ℕ, 1 ≤ h → 400 * h ≤ m → 100 * m ≤ Kc → nu⁻¹ ^ 2 ≤ (m : ℝ) →
    ∀ e e' : Vec d, vecNormSq e ≤ 1 → vecNormSq e' ≤ 1 →
    ∀ n : ℕ, n = ⌊(m : ℝ) - h - 100 * (Real.log (nu⁻¹ * m) / Real.log 3)⌋₊ →
    ∀ (wD : ShellSeq d → H10Function (openCubeSet (originCube d (Kc : ℤ))))
      (wN : ShellSeq d → H1MeanZeroFunction (openCubeSet (originCube d (Kc : ℤ))))
      (wD' : ShellSeq d → H10Function (openCubeSet (originCube d (Kc : ℤ)))),
    (∀ omega, IsCubeDirichletResponse (originCube d (Kc : ℤ))
      (hshellFlux nu P m h omega e) (wD omega)) →
    (∀ omega, IsCubeNeumannResponse (originCube d (Kc : ℤ))
      (hshellFlux nu P m h omega e') (wN omega)) →
    (∀ omega, IsCubeDirichletResponse (originCube d (Kc : ℤ))
      (hshellFlux nu P m h omega e') (wD' omega)) →
    ∫⁻ omega, vecCubeLpENorm (originCube d (Kc : ℤ)) 2
        (fun x => (wN omega).toH1Function.grad x - (wD' omega).toH1Function.grad x) ^ (2 : ℕ)
        ∂P.toMeasure ≤
      ENNReal.ofReal (Cg * (h : ℝ) ^ ((4 : ℝ) / 5) * (1 + ((Kc - m : ℕ) : ℝ)) ^ ((2 : ℝ) / 5) *
        (3 : ℝ) ^ (-((2 : ℝ) / 5 * ((Kc - m : ℕ) : ℝ))) *
        (sigmaBarInfinite nu (m - h) P) ^ (-(2 : ℝ))) →
    subcubeAvg Kc n (fun Q => ∫⁻ omega,
        ((vecCubeLpENorm Q 4 (fun x => (wD omega).toH1Function.grad x -
            volumeAverageVec (cubeSet Q) (wD omega).toH1Function.grad)) ^ 4 +
          (vecCubeLpENorm Q 4 (fun x => ((wN omega).toH1Function.grad x +
              hshellFlux nu P m h omega e' x) -
            volumeAverageVec (cubeSet Q) (fun y => (wN omega).toH1Function.grad y +
              hshellFlux nu P m h omega e' y))) ^ 4) ∂P.toMeasure) ≤
      ENNReal.ofReal (C * ((sigmaBarInfinite nu (m - h) P)⁻¹) ^ 4 *
        (nu⁻¹ * (m : ℝ)) ^ (-(400 : ℝ))) := by
  obtain ⟨Cos, Cmaj, Cgr, hCos, hCmaj, hCgr1, hch⟩ := crude_Fz_chain hd
  obtain ⟨T1, hT1, hT1'⟩ := hessian_scale_le
  obtain ⟨T2, hT2, hT2'⟩ := gap_tail_le
  set Kd : ℝ := (2 / 3) * Cg + (128 / 3) * Cgr ^ 8 with hKd
  have hKd0 : 0 ≤ Kd := by positivity
  set Br : ℝ := (d : ℝ) ^ 2 * Cos ^ 4 * (Cmaj ^ 4 + 1024 * Cmaj ^ 4 + 1024) * T1 + 1024 * Kd * T2
    with hBr
  refine ⟨max 1 Br, le_max_left _ _, ?_⟩
  intro nu hnu hnu1 P hPre hJ2 hJ3 hJ1 hJ4 m h Kc hh h400 h100 hnm e e' he he' n hn wD wN wD'
    hwD hwN hwD' hgap
  have hσ : 0 < sigmaBarInfinite nu (m - h) P :=
    SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite_pos hnu (m - h) hPre hJ2 hJ3 hJ4
  set si : ℝ := (sigmaBarInfinite nu (m - h) P)⁻¹ with hsi
  have hsi0 : 0 < si := inv_pos.2 hσ
  have hmpos : (1 : ℝ) ≤ m := by
    have : 1 ≤ m := by omega
    exact_mod_cast this
  have hnuinv : 1 ≤ nu⁻¹ := one_le_inv₀ hnu |>.2 hnu1
  have hLpos : 0 < nu⁻¹ * (m : ℝ) := by nlinarith only [hmpos, hnuinv]
  set Lneg : ℝ := (nu⁻¹ * (m : ℝ)) ^ (-(400 : ℝ)) with hLneg
  have hLneg0 : 0 ≤ Lneg := Real.rpow_nonneg hLpos.le _
  -- the range of `n`
  have hn_le : n ≤ Kc := by
    have h1 : n ≤ m := by
      rw [hn]
      have : (m : ℝ) - h - 100 * (Real.log (nu⁻¹ * m) / Real.log 3) ≤ (m : ℝ) := by
        have hl : 0 ≤ Real.log (nu⁻¹ * m) / Real.log 3 :=
          div_nonneg (Real.log_nonneg (by nlinarith only [hmpos, hnuinv]))
            (Real.log_pos (by norm_num)).le
        have hh0 : (0 : ℝ) ≤ h := Nat.cast_nonneg h
        linarith only [hl, hh0]
      calc ⌊(m : ℝ) - h - 100 * (Real.log (nu⁻¹ * m) / Real.log 3)⌋₊ ≤ ⌊(m : ℝ)⌋₊ :=
            Nat.floor_le_floor this
        _ = m := Nat.floor_natCast m
    omega
  set x : ℝ := ((Kc - m : ℕ) : ℝ) with hx
  have hx0 : 0 ≤ x := Nat.cast_nonneg _
  have hσneg : (sigmaBarInfinite nu (m - h) P) ^ (-(2 : ℝ)) = si ^ 2 := by
    rw [Real.rpow_neg hσ.le, Real.rpow_two, hsi, inv_pow]
  rw [hσneg] at hgap
  have ht : 0 < si ^ 2 * (3 : ℝ) ^ (x / 5) := by positivity
  have hmain := hch nu hnu hnu1 P hPre hJ2 hJ3 hJ1 hJ4 m h Kc hh h400 h100 e e' he he' n hn_le
    wD wN wD' hwD hwN hwD' _ hgap ht
  refine hmain.trans ?_
  -- the real arithmetic
  set Bm : ℝ := (3 : ℝ) ^ (-((m - h : ℕ) : ℝ)) with hBm
  have hu := hT1' nu m h n hnu hnu1 hh h400 hnm hn
  have hsq4 : (Real.sqrt d) ^ 4 = (d : ℝ) ^ 2 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt (Nat.cast_nonneg d)]
  have h34 : ((3 : ℝ) ^ n) ^ 4 = (3 : ℝ) ^ (4 * n) := by
    rw [← pow_mul, mul_comm]
  have ha1 : ((Cos * (3 : ℝ) ^ n) ^ 4) * ((Cmaj * si) * (Real.sqrt d * Bm)) ^ 4 =
      Cos ^ 4 * Cmaj ^ 4 * si ^ 4 * (d : ℝ) ^ 2 * ((3 : ℝ) ^ (4 * n) * Bm ^ 4) := by
    calc _ = Cos ^ 4 * ((3 : ℝ) ^ n) ^ 4 * (Cmaj ^ 4 * si ^ 4 * ((Real.sqrt d) ^ 4 * Bm ^ 4)) := by
          ring
      _ = _ := by rw [h34, hsq4]; ring
  have ha3 : ((Cos * (3 : ℝ) ^ n) ^ 4) * (si * (Real.sqrt d * Bm)) ^ 4 =
      Cos ^ 4 * si ^ 4 * (d : ℝ) ^ 2 * ((3 : ℝ) ^ (4 * n) * Bm ^ 4) := by
    calc _ = Cos ^ 4 * ((3 : ℝ) ^ n) ^ 4 * (si ^ 4 * ((Real.sqrt d) ^ 4 * Bm ^ 4)) := by ring
      _ = _ := by rw [h34, hsq4]; ring
  have hu0 : 0 ≤ (3 : ℝ) ^ (4 * n) * Bm ^ 4 := by positivity
  have hgapt := hT2' nu m h Kc hnu hnu1 hh h400 h100 hnm
  have hR := gap_term_le (si := si) (Cg := Cg) (Cgr := Cgr) (h := (h : ℝ)) (x := x) hsi0 hCg
    (by exact_mod_cast hh) hx0
  -- assemble in `ℝ≥0∞`
  set X0 : ℝ := Cg * (h : ℝ) ^ ((4 : ℝ) / 5) * (1 + x) ^ ((2 : ℝ) / 5) *
    (3 : ℝ) ^ (-((2 : ℝ) / 5 * x)) * si ^ 2 with hX0
  have hX00 : 0 ≤ X0 := by positivity
  have hG0 : 0 ≤ (Cgr * si * (h : ℝ) ^ ((1 : ℝ) / 2)) ^ 8 := by positivity
  have ht3 : 0 ≤ 2 * (si ^ 2 * (3 : ℝ) ^ (x / 5)) / 3 := by positivity
  have ht4 : 0 ≤ 1 / (3 * (si ^ 2 * (3 : ℝ) ^ (x / 5)) ^ 2) := by positivity
  have hq1 : 0 ≤ (Cos * (3 : ℝ) ^ n) ^ 4 * ((Cmaj * si) * (Real.sqrt d * Bm)) ^ 4 := by positivity
  have hq3 : 0 ≤ (Cos * (3 : ℝ) ^ n) ^ 4 * (si * (Real.sqrt d * Bm)) ^ 4 := by positivity
  have hE : ENNReal.ofReal ((Cos * (3 : ℝ) ^ n) ^ 4 * ((Cmaj * si) * (Real.sqrt d * Bm)) ^ 4) +
      1024 * (ENNReal.ofReal ((Cos * (3 : ℝ) ^ n) ^ 4 * ((Cmaj * si) * (Real.sqrt d * Bm)) ^ 4) +
        ENNReal.ofReal ((Cos * (3 : ℝ) ^ n) ^ 4 * (si * (Real.sqrt d * Bm)) ^ 4)) +
      1024 * (ENNReal.ofReal (2 * (si ^ 2 * (3 : ℝ) ^ (x / 5)) / 3) * ENNReal.ofReal X0 +
        ENNReal.ofReal (1 / (3 * (si ^ 2 * (3 : ℝ) ^ (x / 5)) ^ 2)) *
          (128 * ENNReal.ofReal ((Cgr * si * (h : ℝ) ^ ((1 : ℝ) / 2)) ^ 8))) =
      ENNReal.ofReal (((Cos * (3 : ℝ) ^ n) ^ 4 * ((Cmaj * si) * (Real.sqrt d * Bm)) ^ 4) +
        1024 * (((Cos * (3 : ℝ) ^ n) ^ 4 * ((Cmaj * si) * (Real.sqrt d * Bm)) ^ 4) +
          ((Cos * (3 : ℝ) ^ n) ^ 4 * (si * (Real.sqrt d * Bm)) ^ 4)) +
        1024 * (2 * (si ^ 2 * (3 : ℝ) ^ (x / 5)) / 3 * X0 +
          1 / (3 * (si ^ 2 * (3 : ℝ) ^ (x / 5)) ^ 2) *
            (128 * (Cgr * si * (h : ℝ) ^ ((1 : ℝ) / 2)) ^ 8))) := by
    have h128 : (128 : ℝ≥0∞) = ENNReal.ofReal 128 := by norm_num
    have h1024 : (1024 : ℝ≥0∞) = ENNReal.ofReal 1024 := by norm_num
    have f1 : ENNReal.ofReal (2 * (si ^ 2 * (3 : ℝ) ^ (x / 5)) / 3) * ENNReal.ofReal X0 =
        ENNReal.ofReal (2 * (si ^ 2 * (3 : ℝ) ^ (x / 5)) / 3 * X0) :=
      (ENNReal.ofReal_mul ht3).symm
    have f2 : (128 : ℝ≥0∞) * ENNReal.ofReal ((Cgr * si * (h : ℝ) ^ ((1 : ℝ) / 2)) ^ 8) =
        ENNReal.ofReal (128 * (Cgr * si * (h : ℝ) ^ ((1 : ℝ) / 2)) ^ 8) := by
      rw [h128, ← ENNReal.ofReal_mul (by norm_num)]
    have f3 : ENNReal.ofReal (1 / (3 * (si ^ 2 * (3 : ℝ) ^ (x / 5)) ^ 2)) *
        ENNReal.ofReal (128 * (Cgr * si * (h : ℝ) ^ ((1 : ℝ) / 2)) ^ 8) =
        ENNReal.ofReal (1 / (3 * (si ^ 2 * (3 : ℝ) ^ (x / 5)) ^ 2) *
          (128 * (Cgr * si * (h : ℝ) ^ ((1 : ℝ) / 2)) ^ 8)) :=
      (ENNReal.ofReal_mul ht4).symm
    have hgg : 0 ≤ 1 / (3 * (si ^ 2 * (3 : ℝ) ^ (x / 5)) ^ 2) *
        (128 * (Cgr * si * (h : ℝ) ^ ((1 : ℝ) / 2)) ^ 8) := by positivity
    have hff : 0 ≤ 2 * (si ^ 2 * (3 : ℝ) ^ (x / 5)) / 3 * X0 := by positivity
    have f4 : ENNReal.ofReal (2 * (si ^ 2 * (3 : ℝ) ^ (x / 5)) / 3 * X0) +
        ENNReal.ofReal (1 / (3 * (si ^ 2 * (3 : ℝ) ^ (x / 5)) ^ 2) *
          (128 * (Cgr * si * (h : ℝ) ^ ((1 : ℝ) / 2)) ^ 8)) =
        ENNReal.ofReal (2 * (si ^ 2 * (3 : ℝ) ^ (x / 5)) / 3 * X0 +
          1 / (3 * (si ^ 2 * (3 : ℝ) ^ (x / 5)) ^ 2) *
            (128 * (Cgr * si * (h : ℝ) ^ ((1 : ℝ) / 2)) ^ 8)) :=
      (ENNReal.ofReal_add hff hgg).symm
    have f5 : ENNReal.ofReal ((Cos * (3 : ℝ) ^ n) ^ 4 * ((Cmaj * si) * (Real.sqrt d * Bm)) ^ 4) +
        ENNReal.ofReal ((Cos * (3 : ℝ) ^ n) ^ 4 * (si * (Real.sqrt d * Bm)) ^ 4) =
        ENNReal.ofReal (((Cos * (3 : ℝ) ^ n) ^ 4 * ((Cmaj * si) * (Real.sqrt d * Bm)) ^ 4) +
          ((Cos * (3 : ℝ) ^ n) ^ 4 * (si * (Real.sqrt d * Bm)) ^ 4)) :=
      (ENNReal.ofReal_add hq1 hq3).symm
    rw [f1, f2, f3, f4, f5]
    rw [h1024, ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num),
      ← ENNReal.ofReal_add hq1 (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity)]
  rw [hE]
  refine ENNReal.ofReal_le_ofReal ?_
  -- the real inequality
  have hgtl : (h : ℝ) ^ 4 * (1 + x) ^ ((2 : ℝ) / 5) * (3 : ℝ) ^ (-((1 : ℝ) / 5 * x)) ≤
      T2 * Lneg := hgapt
  have hRle : 2 * (si ^ 2 * (3 : ℝ) ^ (x / 5)) / 3 * X0 +
      1 / (3 * (si ^ 2 * (3 : ℝ) ^ (x / 5)) ^ 2) *
        (128 * (Cgr * si * (h : ℝ) ^ ((1 : ℝ) / 2)) ^ 8) ≤ si ^ 4 * Kd * (T2 * Lneg) := by
    exact hR.trans (mul_le_mul_of_nonneg_left hgtl (by positivity))
  have hs4 : 0 ≤ si ^ 4 := by positivity
  rw [ha1, ha3]
  have hu' : (3 : ℝ) ^ (4 * n) * Bm ^ 4 ≤ T1 * Lneg := hu
  have hc1 : 0 ≤ Cos ^ 4 * Cmaj ^ 4 * si ^ 4 * (d : ℝ) ^ 2 := by positivity
  have hc3 : 0 ≤ Cos ^ 4 * si ^ 4 * (d : ℝ) ^ 2 := by positivity
  have hb1 : Cos ^ 4 * Cmaj ^ 4 * si ^ 4 * (d : ℝ) ^ 2 * ((3 : ℝ) ^ (4 * n) * Bm ^ 4) ≤
      Cos ^ 4 * Cmaj ^ 4 * si ^ 4 * (d : ℝ) ^ 2 * (T1 * Lneg) := by gcongr
  have hb3 : Cos ^ 4 * si ^ 4 * (d : ℝ) ^ 2 * ((3 : ℝ) ^ (4 * n) * Bm ^ 4) ≤
      Cos ^ 4 * si ^ 4 * (d : ℝ) ^ 2 * (T1 * Lneg) := by gcongr
  have hfin : Cos ^ 4 * Cmaj ^ 4 * si ^ 4 * (d : ℝ) ^ 2 * (T1 * Lneg) +
      1024 * (Cos ^ 4 * Cmaj ^ 4 * si ^ 4 * (d : ℝ) ^ 2 * (T1 * Lneg) +
        Cos ^ 4 * si ^ 4 * (d : ℝ) ^ 2 * (T1 * Lneg)) +
      1024 * (si ^ 4 * Kd * (T2 * Lneg)) = si ^ 4 * Lneg * Br := by
    rw [hBr]
    ring
  have hBr' : Br ≤ max 1 Br := le_max_right _ _
  calc _ ≤ Cos ^ 4 * Cmaj ^ 4 * si ^ 4 * (d : ℝ) ^ 2 * (T1 * Lneg) +
        1024 * (Cos ^ 4 * Cmaj ^ 4 * si ^ 4 * (d : ℝ) ^ 2 * (T1 * Lneg) +
          Cos ^ 4 * si ^ 4 * (d : ℝ) ^ 2 * (T1 * Lneg)) +
        1024 * (si ^ 4 * Kd * (T2 * Lneg)) := by gcongr
    _ = si ^ 4 * Lneg * Br := hfin
    _ ≤ si ^ 4 * Lneg * max 1 Br := by gcongr
    _ = max 1 Br * si ^ 4 * Lneg := by ring

end

end SuperdiffusionCLT.Section5

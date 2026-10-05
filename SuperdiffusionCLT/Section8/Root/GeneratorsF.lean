/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Root.GeneratorsE

/-!
# The whole-space solution as a limit of Dirichlet solutions (deterministic part)

`gen_whole_space`: for a `C²` skew-plus-scalar field and continuous zero-trace solutions `w_n` of
`-∇·(a∇w_n) = G` on `B_n`, with a decay bound `|w_n| ≤ ψ_m` off `B_m` (`n ≥ m`), there is a `C²`
function `U ∈ C₀` solving `∇·(a∇U) = -G` pointwise on `ℝ^d` and within `ψ_m` of each `w_m`.
-/

@[expose] public section

open Homogenization MeasureTheory Filter Topology SuperdiffusionCLT.Section6
  SuperdiffusionCLT.Section7
open scoped ENNReal

namespace SuperdiffusionCLT.Section8

variable {d : ℕ}

theorem gen_whole_space [NeZero d] (hd : 2 ≤ d) {a : CoeffField d} {nu : ℝ} (hnu : 0 < nu)
    (hsk : ∀ y i j, a y i j + a y j i = if i = j then 2 * nu else 0)
    (ha2 : ∀ i j, ContDiff ℝ 2 fun y => a y i j)
    (hEll : ∀ s : ℝ, 0 < s → ∃ lam Lam, IsEllipticFieldOn lam Lam (euclidBall (d := d) s) a)
    {G : Vec d → ℝ} (hG : ContDiff ℝ 1 G) (hGs : HasCompactSupport G) {n0 : ℕ} (hn0 : 1 ≤ n0)
    (w : ℕ → Vec d → ℝ) (uR : ∀ n : ℕ, H10Function (euclidBall (d := d) (n : ℝ)))
    (hwc : ∀ n, Continuous (w n))
    (hw0 : ∀ n, n0 ≤ n → ∀ y, y ∉ euclidBall (d := d) (n : ℝ) → w n y = 0)
    (hae : ∀ n, n0 ≤ n → ∀ᵐ y ∂volume.restrict (euclidBall (d := d) (n : ℝ)),
      w n y = (uR n).toH1Function.toFun y)
    (hsol : ∀ n, n0 ≤ n → IsWeakSolutionOn a (euclidBall (d := d) (n : ℝ)) (uR n).toH1Function G
      (fun _ => 0))
    {ψ : ℕ → ℝ} (hψ : Tendsto ψ atTop (𝓝 0))
    (hdec : ∀ m n, n0 ≤ m → m ≤ n → ∀ y, y ∉ euclidBall (d := d) (m : ℝ) → |w n y| ≤ ψ m) :
    ∃ U : Vec d → ℝ, ContDiff ℝ 2 U ∧ IsC0Function U ∧ (∀ x, divForm 1 a U x = -G x) ∧
      ∀ m, n0 ≤ m → ∀ y, |U y - w m y| ≤ ψ m := by
  have ha : ∀ i j, Continuous fun y => a y i j := fun i j => (ha2 i j).continuous
  have hGc : Continuous G := hG.continuous
  have hGm : ∀ s : ℝ, MemLp G 2 (volume.restrict (euclidBall (d := d) s)) := fun s =>
    (hGc.memLp_of_hasCompactSupport hGs).restrict _
  have hcomp : ∀ m n, n0 ≤ m → m ≤ n → ∀ y, |w n y - w m y| ≤ ψ m := by
    intro m n hm hmn
    have hmpos : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
    obtain ⟨lam, Lam, hE⟩ := hEll m hmpos
    exact gen_comparison hmpos (by exact_mod_cast hmn) hE (hGm _) (hwc m) (hwc n)
      (hw0 m hm) (uR m) (uR n).toH1Function (hae m hm) (hae n (hm.trans hmn))
      (hsol m hm) (hsol n (hm.trans hmn)) (hdec m n hm hmn)
  obtain ⟨U, hUc, hUb⟩ := gen_cauchy_limit hψ hwc hcomp
  have hC0 : IsC0Function U := by
    refine gen_isC0 hUc hψ (n0 := n0) fun m hm y hy => ?_
    have := hUb m hm y
    rw [hw0 m hm y hy, sub_zero] at this
    exact this
  have hloc := fun N (hN : 1 ≤ N) => gen_local_limit ha hEll hGc hGs w uR hae hsol hψ hcomp hUc hUb
    N hN
  have hmem : ∀ x : Vec d, ∃ N : ℕ, 1 ≤ N ∧ x ∈ euclidBall (d := d) (N : ℝ) := fun x => by
    refine ⟨⌈vecNormSq x⌉₊ + 1, by omega, ?_⟩
    show vecNormSq x < (((⌈vecNormSq x⌉₊ + 1 : ℕ) : ℝ)) ^ 2
    have h1 := Nat.le_ceil (vecNormSq x)
    have h2 : (1 : ℝ) ≤ ((⌈vecNormSq x⌉₊ + 1 : ℕ) : ℝ) := by
      exact_mod_cast (by omega : 1 ≤ ⌈vecNormSq x⌉₊ + 1)
    push_cast at h2 ⊢
    nlinarith only [h1, h2]
  have hat : ∀ x, ContDiffAt ℝ 2 U x := by
    intro x
    obtain ⟨N, hN, hx⟩ := hmem x
    obtain ⟨W, hW1, hW2⟩ := hloc N hN
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
    obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : Vec d) (N : ℝ)).exists_bound_of_continuousOn
      hUc.continuousOn
    have := intC2_contDiffAt hd (isOpen_euclidBall _) hnu hsk ha2 (mu := 0) hG (M := B) hW2
      (by rw [hW1]; exact hUc.continuousOn)
      (fun y hy => by
        rw [hW1]
        have := hB y (Metric.ball_subset_closedBall (euclidBall_subset_ball hNpos hy))
        rwa [Real.norm_eq_abs] at this) hx
    rwa [hW1] at this
  have hU2 : ContDiff ℝ 2 U := contDiff_iff_contDiffAt.2 hat
  refine ⟨U, hU2, hC0, fun x => ?_, hUb⟩
  obtain ⟨N, hN, hx⟩ := hmem x
  obtain ⟨W, hW1, hW2⟩ := hloc N hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hb : Bornology.IsBounded (euclidBall (d := d) (N : ℝ)) :=
    Metric.isBounded_ball.subset (euclidBall_subset_ball hNpos)
  have := intC2_pointwise (isOpen_euclidBall _) hb ha2 hGc hW2 (by rw [hW1]; exact hU2) hx
  rw [hW1] at this
  simpa using this

end SuperdiffusionCLT.Section8

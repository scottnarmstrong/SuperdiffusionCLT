/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Localization.BlockPerturbation

@[expose] public section

/-- **Lemma `l.localization.A` (Localization of `bfA`)**.

Let `h` and `k` be anti-symmetric matrix fields, `s` a positive symmetric
matrix field, and `a = s + k`.  Then for every bounded domain `U` and, writing

`D = ‖s^{-1/2} h s^{-1/2}‖_{L∞(U)} (1 + ‖s^{-1/2} h s^{-1/2}‖_{L∞(U)})`,

one has `-D bfA(U; a) ≤ bfA(U; a + h) - bfA(U; a) ≤ D bfA(U; a)` in the
Loewner order on `2d`-by-`2d` symmetric matrices.

The domain carrier is `Homogenization.Book.Ch02.Domain d` (bounded open convex)
where the paper prints a bounded Lipschitz domain, and the standing
qualitative uniform ellipticity is carried by the two Chapter 2
coefficient bundles `a` and `b`, with `b = a + h` almost everywhere on `U`.
The printed `L∞` norm of
`s^{-1/2} h s^{-1/2}` is written square-root-free as the relative bound
`2 r · h(x) p ≤ theta (p · s(x) p + r · s(x) r)`, which holds for a given
`theta` exactly when `‖s^{-1/2} h s^{-1/2}‖ ≤ theta`; the printed statement is
the instance at the least admissible `theta`. -/
theorem SuperdiffusionCLT.Frozen.Section2.coarseBlockMatrix_localization
    (d : ℕ) (U : Homogenization.Book.Ch02.Domain d)
    (sigma kappa hfield : Homogenization.CoeffField d)
    (a b : Homogenization.Book.Ch02.CoeffOn U) (theta : ℝ) :
    (∀ x : Homogenization.Vec d,
        Homogenization.matTranspose (sigma x) = sigma x) →
      (∀ (x : Homogenization.Vec d) (p : Homogenization.Vec d), p ≠ 0 →
          0 < Homogenization.vecDot p
            (Homogenization.matVecMul (sigma x) p)) →
        (∀ x : Homogenization.Vec d,
            Homogenization.matTranspose (kappa x) = -kappa x) →
          (∀ x : Homogenization.Vec d,
              Homogenization.matTranspose (hfield x) = -hfield x) →
            (∀ᵐ x ∂(Homogenization.volumeMeasureOn
                (U : Set (Homogenization.Vec d))),
                a.toCoeffField x = sigma x + kappa x) →
              (∀ᵐ x ∂(Homogenization.volumeMeasureOn
                  (U : Set (Homogenization.Vec d))),
                  b.toCoeffField x = a.toCoeffField x + hfield x) →
                (∀ᵐ x ∂(Homogenization.volumeMeasureOn
                    (U : Set (Homogenization.Vec d))),
                    ∀ p r : Homogenization.Vec d,
                      2 * Homogenization.vecDot r
                          (Homogenization.matVecMul (hfield x) p) ≤
                        theta *
                          (Homogenization.vecDot p
                              (Homogenization.matVecMul (sigma x) p) +
                            Homogenization.vecDot r
                              (Homogenization.matVecMul (sigma x) r))) →
                  Homogenization.BlockMatLoewnerLE
                      ((-(theta * (1 + theta))) •
                        Homogenization.Book.Ch02.coarseBlockMatrix U a)
                      (Homogenization.ofFullBlockMat
                        (Homogenization.toFullBlockMat
                            (Homogenization.Book.Ch02.coarseBlockMatrix U b) -
                          Homogenization.toFullBlockMat
                            (Homogenization.Book.Ch02.coarseBlockMatrix U a))) ∧
                    Homogenization.BlockMatLoewnerLE
                      (Homogenization.ofFullBlockMat
                        (Homogenization.toFullBlockMat
                            (Homogenization.Book.Ch02.coarseBlockMatrix U b) -
                          Homogenization.toFullBlockMat
                            (Homogenization.Book.Ch02.coarseBlockMatrix U a)))
                      ((theta * (1 + theta)) •
                        Homogenization.Book.Ch02.coarseBlockMatrix U a)
    := by
  intro hsymm _hpos hskewk hskewh ha hb htheta
  have hsymmPart : ∀ᵐ x ∂(Homogenization.volumeMeasureOn
      (U : Set (Homogenization.Vec d))),
      Homogenization.symmPart (a.toCoeffField x) = sigma x := by
    filter_upwards [ha] with x hx
    funext i j
    have hs : sigma x j i = sigma x i j := by
      have := congrFun (congrFun (hsymm x) i) j
      simpa [Homogenization.matTranspose] using this
    have hk : kappa x j i = -kappa x i j := by
      have := congrFun (congrFun (hskewk x) i) j
      simpa [Homogenization.matTranspose] using this
    show (a.toCoeffField x i j + a.toCoeffField x j i) / 2 = sigma x i j
    rw [hx]
    show (sigma x i j + kappa x i j + (sigma x j i + kappa x j i)) / 2 = sigma x i j
    rw [hs, hk]
    ring
  have hbound : ∀ᵐ x ∂(Homogenization.volumeMeasureOn
      (U : Set (Homogenization.Vec d))),
      ∀ p r : Homogenization.Vec d,
        2 * Homogenization.vecDot r
            (Homogenization.matVecMul (hfield x) p) ≤
          theta * (Homogenization.vecDot p
              (Homogenization.matVecMul
                (Homogenization.symmPart (a.toCoeffField x)) p) +
            Homogenization.vecDot r
              (Homogenization.matVecMul
                (Homogenization.symmPart (a.toCoeffField x)) r)) := by
    filter_upwards [htheta, hsymmPart] with x hx hsp
    rw [hsp]
    exact hx
  exact SuperdiffusionCLT.Section2.Localization.coarseBlockMatrix_localization
    hb (Filter.Eventually.of_forall hskewh) hbound


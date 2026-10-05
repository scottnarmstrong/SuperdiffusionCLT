/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section4.MinimalScales.LimitLocBlockJ
public import SuperdiffusionCLT.Section4.MinimalScales.LimitRespDescendantBound
public import Mathlib.Topology.Order.Lattice
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Convergence of `normalizedBlockResponseMax` and the finite maximum over descendants

The supremum `normalizedBlockResponseMax R a a0 = sSup { BlockJ (cubeSet R) P_e Q_e a }`
over the unit sphere of block vectors is handled without compactness: the two-sided
Loewner sandwich (relative factor `D_L`) pushes through the identity
`BlockJ = (1/4) Q(X₁) + (1/4) Q(X₂) - c` of `LimitLocBlockJ.lean` to
`(1 - D) J_∞ - D C ≤ J_L ≤ (1 + D) J_∞ + D C` uniformly in the test vector, where `C` bounds
`c` on the sphere. A generic supremum lemma then gives the same bounds for the suprema.

## Main results

* `srootL4_tendsto_finsetSsup`: termwise convergence gives convergence of `finsetSsup`.
* `srootL4_sSup_two_sided`: the generic supremum lemma.
* `srootL4_tendsto_normalizedBlockResponseMax`: a.s., on every sub-cube of
  `originCube d n`, the supremum over test vectors of the cutoff field converges to that of the
  limiting field, for every `a0`.
* `srootL4_tendsto_srootE_term`: a.s., for every `l`, the `l`-th series term converges.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section4.MinimalScales

open Homogenization MeasureTheory Filter
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Frozen.Assumptions

noncomputable section

/-- Termwise convergence gives convergence of `finsetSsup` over a fixed finite family. -/
theorem srootL4_tendsto_finsetSsup {α : Type*} (s : Finset α) (f : ℕ → α → ℝ) (g : α → ℝ)
    (h : ∀ a ∈ s, Filter.Tendsto (fun L => f L a) Filter.atTop (nhds (g a))) :
    Filter.Tendsto (fun L => Homogenization.finsetSsup s (f L)) Filter.atTop
      (nhds (Homogenization.finsetSsup s g)) := by
  rcases s.eq_empty_or_nonempty with rfl | hne
  · simp [Homogenization.finsetSsup]
  · have h1 : ∀ L, Homogenization.finsetSsup s (f L) = s.sup' hne (f L) := fun L =>
      (Finset.sup'_eq_csSup_image s hne (f L)).symm
    have h2 : Homogenization.finsetSsup s g = s.sup' hne g :=
      (Finset.sup'_eq_csSup_image s hne g).symm
    simp only [h1, h2]
    exact Filter.Tendsto.finset_sup'_nhds_apply (s := s) (f := fun a L => f L a) (g := g)
      (l := Filter.atTop) hne h

/-- **Generic supremum lemma**: a two-sided affine bound, uniform in the index, passes to
the suprema. -/
theorem srootL4_sSup_two_sided {E : Type*} (p : E → Prop) (f g : E → ℝ) {D C : ℝ}
    (hD0 : 0 ≤ D) (hD1 : D < 1) (hne : ∃ e, p e)
    (hfb : BddAbove {m | ∃ e, p e ∧ m = f e}) (hgb : BddAbove {m | ∃ e, p e ∧ m = g e})
    (hup : ∀ e, p e → f e ≤ (1 + D) * g e + D * C)
    (hlo : ∀ e, p e → (1 - D) * g e - D * C ≤ f e) :
    sSup {m | ∃ e, p e ∧ m = f e} ≤ (1 + D) * sSup {m | ∃ e, p e ∧ m = g e} + D * C ∧
      (1 - D) * sSup {m | ∃ e, p e ∧ m = g e} - D * C ≤ sSup {m | ∃ e, p e ∧ m = f e} := by
  obtain ⟨e0, he0⟩ := hne
  have hSf : {m | ∃ e, p e ∧ m = f e}.Nonempty := ⟨f e0, e0, he0, rfl⟩
  have hSg : {m | ∃ e, p e ∧ m = g e}.Nonempty := ⟨g e0, e0, he0, rfl⟩
  constructor
  · refine csSup_le hSf ?_
    rintro m ⟨e, he, rfl⟩
    have hge : g e ≤ sSup {m | ∃ e, p e ∧ m = g e} := le_csSup hgb ⟨e, he, rfl⟩
    have := mul_le_mul_of_nonneg_left hge (by linarith only [hD0] : (0 : ℝ) ≤ 1 + D)
    linarith only [hup e he, this]
  · have hpos : 0 < 1 - D := by linarith only [hD1]
    have hle : sSup {m | ∃ e, p e ∧ m = g e} ≤
        (sSup {m | ∃ e, p e ∧ m = f e} + D * C) / (1 - D) := by
      refine csSup_le hSg ?_
      rintro m ⟨e, he, rfl⟩
      rw [le_div_iff₀ hpos]
      have hfe : f e ≤ sSup {m | ∃ e, p e ∧ m = f e} := le_csSup hfb ⟨e, he, rfl⟩
      linarith only [hlo e he, hfe]
    rw [le_div_iff₀ hpos] at hle
    linarith only [hle]

/-- `|x·y| ≤ (x·x + y·y)/2`, in the form needed for the bound on the constant term. -/
theorem srootL4_vecDot_le_half {d : ℕ} (x y : Vec d) :
    vecDot x y ≤ (vecDot x x + vecDot y y) / 2 := by
  unfold vecDot
  rw [← Finset.sum_add_distrib, Finset.sum_div]
  refine Finset.sum_le_sum fun i _ => ?_
  nlinarith only [sq_nonneg (x i - y i)]

/-- The pointwise two-sided bound on `BlockJ` from the two matrix sandwiches. -/
theorem srootL4_blockJ_two_sided {d : ℕ} [NeZero d] (R : TriadicCube d) {nu Lam1 Lam2 D : ℝ}
    (hnu : 0 < nu) (aL ai : Homogenization.CoeffField d)
    (hEllL : Homogenization.IsEllipticFieldOn nu Lam1 (cubeSet R) aL)
    (hEllI : Homogenization.IsEllipticFieldOn nu Lam2 (cubeSet R) ai)
    (h1 : Homogenization.BlockMatLoewnerLE
        ((-D) • Homogenization.coarseBlockMatrix (openCubeSet R) ai)
        (Homogenization.ofFullBlockMat
          (Homogenization.toFullBlockMat (Homogenization.coarseBlockMatrix (openCubeSet R) aL) -
            Homogenization.toFullBlockMat (Homogenization.coarseBlockMatrix (openCubeSet R) ai))))
    (h2 : Homogenization.BlockMatLoewnerLE
        (Homogenization.ofFullBlockMat
          (Homogenization.toFullBlockMat (Homogenization.coarseBlockMatrix (openCubeSet R) aL) -
            Homogenization.toFullBlockMat (Homogenization.coarseBlockMatrix (openCubeSet R) ai)))
        (D • Homogenization.coarseBlockMatrix (openCubeSet R) ai))
    (P Q' : BlockVec d) :
    Homogenization.BlockJ (cubeSet R) P Q' aL ≤
        (1 + D) * Homogenization.BlockJ (cubeSet R) P Q' ai +
          D * (vecDot P.1 Q'.1 + vecDot Q'.2 P.2) ∧
      (1 - D) * Homogenization.BlockJ (cubeSet R) P Q' ai -
          D * (vecDot P.1 Q'.1 + vecDot Q'.2 P.2) ≤
        Homogenization.BlockJ (cubeSet R) P Q' aL := by
  have eL := srootL4_blockJ_eq_quadratic R hnu aL hEllL P.1 Q'.2 P.2 Q'.1
  have eI := srootL4_blockJ_eq_quadratic R hnu ai hEllI P.1 Q'.2 P.2 Q'.1
  have hX1 := srootL4_quadForm_two_sided h1 h2 (-(P.1 - Q'.2), Q'.1 - P.2)
  have hX2 := srootL4_quadForm_two_sided h1 h2 (Q'.2 + P.1, Q'.1 + P.2)
  change Homogenization.BlockJ (cubeSet R) (P.1, P.2) (Q'.1, Q'.2) aL ≤ _ ∧ _ ≤
    Homogenization.BlockJ (cubeSet R) (P.1, P.2) (Q'.1, Q'.2) aL
  rw [eL, eI]
  constructor
  · linarith only [hX1.2, hX2.2]
  · linarith only [hX1.1, hX2.1]

/-- The constant term is bounded on the unit sphere of test vectors. -/
theorem srootL4_probe_const_le {d : ℕ} (a0 : Mat d) {e : FullBlockVec d}
    (he : fullBlockVecNormSq e = 1) :
    vecDot (ofFullBlockVec (Matrix.mulVec (constantFullBlockMatrixInvSqrt a0) e)).1
          (ofFullBlockVec (Matrix.mulVec (constantFullBlockMatrixSqrt a0) e)).1 +
        vecDot (ofFullBlockVec (Matrix.mulVec (constantFullBlockMatrixSqrt a0) e)).2
          (ofFullBlockVec (Matrix.mulVec (constantFullBlockMatrixInvSqrt a0) e)).2 ≤
      (fullBlockMatRowAbsSqBound (constantFullBlockMatrixInvSqrt a0) +
        fullBlockMatRowAbsSqBound (constantFullBlockMatrixSqrt a0)) / 2 := by
  have hP : blockVecDot (ofFullBlockVec (Matrix.mulVec (constantFullBlockMatrixInvSqrt a0) e))
      (ofFullBlockVec (Matrix.mulVec (constantFullBlockMatrixInvSqrt a0) e)) ≤
        fullBlockMatRowAbsSqBound (constantFullBlockMatrixInvSqrt a0) := by
    rw [blockVecDot_ofFullBlockVec_self_eq_fullBlockVecNormSq]
    exact fullBlockVecNormSq_mulVec_le_rowAbsSqBound_of_eq_one _ he
  have hQ : blockVecDot (ofFullBlockVec (Matrix.mulVec (constantFullBlockMatrixSqrt a0) e))
      (ofFullBlockVec (Matrix.mulVec (constantFullBlockMatrixSqrt a0) e)) ≤
        fullBlockMatRowAbsSqBound (constantFullBlockMatrixSqrt a0) := by
    rw [blockVecDot_ofFullBlockVec_self_eq_fullBlockVecNormSq]
    exact fullBlockVecNormSq_mulVec_le_rowAbsSqBound_of_eq_one _ he
  set P := ofFullBlockVec (Matrix.mulVec (constantFullBlockMatrixInvSqrt a0) e) with hPdef
  set Q' := ofFullBlockVec (Matrix.mulVec (constantFullBlockMatrixSqrt a0) e) with hQdef
  have h1 := srootL4_vecDot_le_half P.1 Q'.1
  have h2 := srootL4_vecDot_le_half Q'.2 P.2
  unfold blockVecDot at hP hQ
  linarith only [h1, h2, hP, hQ]

/-- **Convergence of the supremum over test vectors, a.s., on every sub-cube.** -/
theorem srootL4_tendsto_normalizedBlockResponseMax {d : ℕ} [NeZero d] (nu : ℝ) (hnu : 0 < nu)
    {P : MeasureTheory.ProbabilityMeasure (ShellSeq d)} (hJ3 : ShellLawJ3 d P)
    (m n : ℕ) (k : Fin d → ℤ)
    (hk : (fun x => (fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x) ''
          cubeSet (originCube d (n : ℤ)) ⊆ cubeSet (originCube d (m : ℤ)))
    (a0 : Mat d) :
    ∀ᵐ omega : ShellSeq d ∂P.toMeasure,
      ∀ R : TriadicCube d, cubeSet R ⊆ cubeSet (originCube d (n : ℤ)) →
        Filter.Tendsto
          (fun L : ℕ => normalizedBlockResponseMax R (srootE_field nu omega L m n k) a0)
          Filter.atTop
          (nhds (normalizedBlockResponseMax R (srootE_limField nu omega m n k) a0)) := by
  filter_upwards [srootL4_coarseBlockMatrix_sandwich_cube nu hnu hJ3 m n k hk,
    SuperdiffusionCLT.Section2.Cutoff.eventually_summable_shellDerivLinftyNorm
      (P := P) hJ3 (m := m + 1) (U := cubeSet (originCube d (m : ℤ)))
      (srootL_cubeSet_subset_openCubeSet_succ m)] with omega hM hsum R hR
  obtain ⟨M, hM0, hMtendsto, hsand⟩ := hM
  obtain ⟨LamA, hnuA, hEllA⟩ :=
    srootL4_exists_ellipticOn_limField_cube nu hnu omega m n k hk hsum R hR
  set D : ℕ → ℝ := fun L => nu⁻¹ * M L + nu⁻¹ ^ 2 * (M L) ^ 2 with hDdef
  have hD0 : ∀ L, 0 ≤ D L := fun L => by
    have := hM0 L
    have hinv : 0 < nu⁻¹ := inv_pos.2 hnu
    simp only [hDdef]
    positivity
  have hDt : Filter.Tendsto D Filter.atTop (nhds 0) :=
    srootL4_tendsto_sandwichFactor nu hMtendsto
  set C : ℝ := (fullBlockMatRowAbsSqBound (constantFullBlockMatrixInvSqrt a0) +
        fullBlockMatRowAbsSqBound (constantFullBlockMatrixSqrt a0)) / 2 with hCdef
  set s : ℝ := normalizedBlockResponseMax R (srootE_limField nu omega m n k) a0 with hsdef
  have hD1 : ∀ᶠ L in Filter.atTop, D L < 1 := hDt.eventually (Iio_mem_nhds one_pos)
  have hbdI := normalizedBlockResponseValueSet_bddAbove_of_isEllipticFieldOn R
    (srootE_limField nu omega m n k) a0 hEllA
  obtain ⟨m0, e0, he0, -⟩ := normalizedBlockResponseValueSet_nonempty R
    (srootE_limField nu omega m n k) a0
  have key : ∀ L : ℕ, D L < 1 →
      (1 - D L) * s - D L * C ≤
          normalizedBlockResponseMax R (srootE_field nu omega L m n k) a0 ∧
        normalizedBlockResponseMax R (srootE_field nu omega L m n k) a0 ≤
          (1 + D L) * s + D L * C := by
    intro L hL
    obtain ⟨LamB, hnuB, hEllB⟩ :=
      srootL4_exists_ellipticOn_field_cube nu hnu omega L m n k hk R hR
    have hbdL := normalizedBlockResponseValueSet_bddAbove_of_isEllipticFieldOn R
      (srootE_field nu omega L m n k) a0 hEllB
    have hmain := srootL4_sSup_two_sided (E := FullBlockVec d)
      (fun e => fullBlockVecNormSq e = 1)
      (fun e => Homogenization.BlockJ (cubeSet R)
        (ofFullBlockVec (Matrix.mulVec (constantFullBlockMatrixInvSqrt a0) e))
        (ofFullBlockVec (Matrix.mulVec (constantFullBlockMatrixSqrt a0) e))
        (srootE_field nu omega L m n k))
      (fun e => Homogenization.BlockJ (cubeSet R)
        (ofFullBlockVec (Matrix.mulVec (constantFullBlockMatrixInvSqrt a0) e))
        (ofFullBlockVec (Matrix.mulVec (constantFullBlockMatrixSqrt a0) e))
        (srootE_limField nu omega m n k))
      (D := D L) (C := C) (hD0 L) hL ⟨e0, he0⟩ hbdL hbdI
      (fun e he => by
        have h := (srootL4_blockJ_two_sided R hnu _ _ hEllB hEllA
          (hsand L R hR).1 (hsand L R hR).2
          (ofFullBlockVec (Matrix.mulVec (constantFullBlockMatrixInvSqrt a0) e))
          (ofFullBlockVec (Matrix.mulVec (constantFullBlockMatrixSqrt a0) e))).1
        have hc := mul_le_mul_of_nonneg_left (srootL4_probe_const_le a0 he) (hD0 L)
        rw [← hCdef] at hc
        linarith only [h, hc])
      (fun e he => by
        have h := (srootL4_blockJ_two_sided R hnu _ _ hEllB hEllA
          (hsand L R hR).1 (hsand L R hR).2
          (ofFullBlockVec (Matrix.mulVec (constantFullBlockMatrixInvSqrt a0) e))
          (ofFullBlockVec (Matrix.mulVec (constantFullBlockMatrixSqrt a0) e))).2
        have hc := mul_le_mul_of_nonneg_left (srootL4_probe_const_le a0 he) (hD0 L)
        rw [← hCdef] at hc
        linarith only [h, hc])
    exact ⟨hmain.2, hmain.1⟩
  have hlo : Filter.Tendsto (fun L => (1 - D L) * s - D L * C) Filter.atTop (nhds s) := by
    have := (((tendsto_const_nhds (x := (1 : ℝ))).sub hDt).mul_const s).sub (hDt.mul_const C)
    simpa using this
  have hhi : Filter.Tendsto (fun L => (1 + D L) * s + D L * C) Filter.atTop (nhds s) := by
    have := (((tendsto_const_nhds (x := (1 : ℝ))).add hDt).mul_const s).add (hDt.mul_const C)
    simpa using this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi
    (hD1.mono fun L hL => (key L hL).1) (hD1.mono fun L hL => (key L hL).2)

end

end SuperdiffusionCLT.Section4.MinimalScales

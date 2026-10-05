/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.AKHC61.WeakNorms.MaximizerBridgeC
public import SuperdiffusionCLT.AKHC61.Tails.EllipticityB
public import SuperdiffusionCLT.AKHC61.Tails.CFSB

/-!
# Package C3: the second moment of the maximal event quantity `M_{n,ρ}`

Source: `e.mathcalM.m.rho.bound` and `e.this.is.so.nice.again` of [AK].

This file proves the deterministic half of the argument:

* the cube geometry identifying the index set of `M_{n,ρ}`'s defining supremum at a fixed scale
  `k ≤ n` (cubes with centre in `cu_n`) with `descendantsAtScale (originCube d n) k`
  (`akhcMM_mem_descendantsAtScale`);
* the **layer-cake replacement** (`akhcMM_sSup_sq_le`): the square of the supremum over all scales
  `k ≤ n` is dominated, pointwise, by the square of the small-scale bound plus the sum over the
  finitely many large scales `k ∈ [k₀, n]` of the squared per-scale maxima. The source's
  tail-integration step (the SOURCE_GAP of node 12, "combining the previous two displays") is
  replaced by this pointwise inequality followed by linearity of the expectation; no tail
  integral is needed, because the scale range `[k₀, n]` is finite and the small scales are
  controlled uniformly by a single random variable (C1).
-/

@[expose] public section

namespace SuperdiffusionCLT.AKHC61.Tails

open Homogenization MeasureTheory

noncomputable section

/-! ## Geometry: the index set of the supremum at one scale -/

/-- Two triadic cubes of the same scale, the centre of the first lying in the second, coincide. -/
theorem akhcMM_eq_of_scale_eq_of_cubeCenter_mem {d : ℕ} {Q R : TriadicCube d}
    (hs : Q.scale = R.scale) (hc : cubeCenter Q ∈ cubeSet R) : Q = R := by
  have hpos : (0 : ℝ) < cubeScaleFactor R := by
    unfold cubeScaleFactor
    exact zpow_pos (by norm_num) _
  have hfac : cubeScaleFactor Q = cubeScaleFactor R := by
    unfold cubeScaleFactor; rw [hs]
  have hidx : ∀ i, Q.index i = R.index i := by
    intro i
    obtain ⟨hlo, hhi⟩ := hc i
    simp only [cubeCenter, hfac] at hlo hhi
    have hlo' : (R.index i : ℝ) - 1 / 2 ≤ (Q.index i : ℝ) := le_of_mul_le_mul_right hlo hpos
    have hhi' : (Q.index i : ℝ) < (R.index i : ℝ) + 1 / 2 := lt_of_mul_lt_mul_right hhi hpos.le
    have h1 : ((R.index i - 1 : ℤ) : ℝ) < (Q.index i : ℝ) := by
      push_cast; linarith only [hlo']
    have h2 : (Q.index i : ℝ) < ((R.index i + 1 : ℤ) : ℝ) := by
      push_cast; linarith only [hhi']
    have h1' : R.index i - 1 < Q.index i := by exact_mod_cast h1
    have h2' : Q.index i < R.index i + 1 := by exact_mod_cast h2
    omega
  cases Q
  cases R
  simp only at hs hidx
  subst hs
  simp only [TriadicCube.mk.injEq, true_and]
  exact funext hidx

/-- A cube of scale `≤ n` whose centre lies in `cu_n` is a descendant of `cu_n` at its own scale. -/
theorem akhcMM_mem_descendantsAtScale {d : ℕ} {n : ℤ} {Q : TriadicCube d}
    (hQn : Q.scale ≤ n) (hc : cubeCenter Q ∈ cubeSet (originCube d n)) :
    Q ∈ descendantsAtScale (originCube d n) Q.scale := by
  have hQn' : Q.scale ≤ (originCube d n).scale := hQn
  rw [mem_descendantsAtScale_iff hQn']
  obtain ⟨R, hR, hcR⟩ :=
    exists_mem_descendantsAtDepth_of_mem_cubeSet (Int.toNat ((originCube d n).scale - Q.scale)) hc
  have hRs := scale_eq_sub_of_mem_descendantsAtDepth hR
  have hscale : Q.scale = R.scale := by
    rw [hRs]
    have hnn : (0 : ℤ) ≤ (originCube d n).scale - Q.scale := by linarith only [hQn']
    rw [Int.toNat_of_nonneg hnn]
    ring
  have hQR := akhcMM_eq_of_scale_eq_of_cubeCenter_mem hscale hcR
  subst hQR
  exact hR

/-! ## The layer-cake replacement: a pointwise bound on the square of the supremum -/

/-- **The pointwise layer-cake replacement.** Let `f` be a nonnegative function of triadic cubes
and consider `sSup {f Q : Q.scale ≤ n, centre of Q in cu_n}`. If every cube of scale `< k₀` has
`f Q ≤ g`, and at each scale `k ∈ [k₀, n]` every descendant of `cu_n` has `f Q ≤ G k`, then the
square of the supremum is at most `g² + Σ_{k ∈ [k₀, n]} (G k)²`. -/
theorem akhcMM_sSup_sq_le {d : ℕ} (n k0 : ℕ) (f : TriadicCube d → ℝ) (hf0 : ∀ Q, 0 ≤ f Q)
    {g : ℝ}
    (hg : ∀ Q : TriadicCube d, Q.scale ≤ (n : ℤ) →
      cubeCenter Q ∈ cubeSet (originCube d (n : ℤ)) → Q.scale < (k0 : ℤ) → f Q ≤ g)
    (G : ℕ → ℝ)
    (hG : ∀ k : ℕ, k0 ≤ k → k ≤ n →
      ∀ Q ∈ descendantsAtScale (originCube d (n : ℤ)) (k : ℤ), f Q ≤ G k) :
    (sSup {M : ℝ | ∃ Q : TriadicCube d, Q.scale ≤ (n : ℤ) ∧
        cubeCenter Q ∈ cubeSet (originCube d (n : ℤ)) ∧ M = f Q}) ^ 2 ≤
      g ^ 2 + ∑ k ∈ Finset.Icc k0 n, G k ^ 2 := by
  set T : ℝ := g ^ 2 + ∑ k ∈ Finset.Icc k0 n, G k ^ 2 with hTdef
  have hsum0 : 0 ≤ ∑ k ∈ Finset.Icc k0 n, G k ^ 2 :=
    Finset.sum_nonneg fun k _ => sq_nonneg (G k)
  have hT0 : 0 ≤ T := by rw [hTdef]; positivity
  have helem : ∀ Q : TriadicCube d, Q.scale ≤ (n : ℤ) →
      cubeCenter Q ∈ cubeSet (originCube d (n : ℤ)) → f Q ^ 2 ≤ T := by
    intro Q hQn hQc
    rcases lt_or_ge Q.scale (k0 : ℤ) with hlt | hge
    · have h1 : f Q ^ 2 ≤ g ^ 2 := pow_le_pow_left₀ (hf0 Q) (hg Q hQn hQc hlt) 2
      rw [hTdef]
      linarith only [h1, hsum0]
    · have hQ0 : (0 : ℤ) ≤ Q.scale := le_trans (Int.natCast_nonneg k0) hge
      set k : ℕ := Q.scale.toNat with hkdef
      have hk : (k : ℤ) = Q.scale := Int.toNat_of_nonneg hQ0
      have hk0 : k0 ≤ k := by omega
      have hkn : k ≤ n := by omega
      have hmem := akhcMM_mem_descendantsAtScale hQn hQc
      rw [← hk] at hmem
      have h1 : f Q ^ 2 ≤ G k ^ 2 := pow_le_pow_left₀ (hf0 Q) (hG k hk0 hkn Q hmem) 2
      have h2 : G k ^ 2 ≤ ∑ k ∈ Finset.Icc k0 n, G k ^ 2 :=
        Finset.single_le_sum (f := fun k => G k ^ 2) (fun k _ => sq_nonneg (G k))
          (Finset.mem_Icc.2 ⟨hk0, hkn⟩)
      rw [hTdef]
      linarith only [h1, h2, sq_nonneg g]
  have hle : sSup {M : ℝ | ∃ Q : TriadicCube d, Q.scale ≤ (n : ℤ) ∧
      cubeCenter Q ∈ cubeSet (originCube d (n : ℤ)) ∧ M = f Q} ≤ Real.sqrt T := by
    refine Real.sSup_le ?_ (Real.sqrt_nonneg T)
    rintro _ ⟨Q, hQn, hQc, rfl⟩
    exact Real.le_sqrt_of_sq_le (helem Q hQn hQc)
  have hnn : 0 ≤ sSup {M : ℝ | ∃ Q : TriadicCube d, Q.scale ≤ (n : ℤ) ∧
      cubeCenter Q ∈ cubeSet (originCube d (n : ℤ)) ∧ M = f Q} := by
    refine Real.sSup_nonneg ?_
    rintro _ ⟨Q, -, -, rfl⟩
    exact hf0 Q
  calc _ ≤ Real.sqrt T ^ 2 := pow_le_pow_left₀ hnn hle 2
    _ = T := Real.sq_sqrt hT0

/-- **Boundedness of the index set of the supremum** under the same two dominations as
`akhcMM_sSup_sq_le`: every value is at most `|g| + Σ_{k ∈ [k₀, n]} |G k|`. -/
theorem akhcMM_bddAbove {d : ℕ} (n k0 : ℕ) (f : TriadicCube d → ℝ) {g : ℝ}
    (hg : ∀ Q : TriadicCube d, Q.scale ≤ (n : ℤ) →
      cubeCenter Q ∈ cubeSet (originCube d (n : ℤ)) → Q.scale < (k0 : ℤ) → f Q ≤ g)
    (G : ℕ → ℝ)
    (hG : ∀ k : ℕ, k0 ≤ k → k ≤ n →
      ∀ Q ∈ descendantsAtScale (originCube d (n : ℤ)) (k : ℤ), f Q ≤ G k) :
    BddAbove {M : ℝ | ∃ Q : TriadicCube d, Q.scale ≤ (n : ℤ) ∧
        cubeCenter Q ∈ cubeSet (originCube d (n : ℤ)) ∧ M = f Q} := by
  have hsum0 : 0 ≤ ∑ k ∈ Finset.Icc k0 n, |G k| :=
    Finset.sum_nonneg fun k _ => abs_nonneg (G k)
  refine ⟨|g| + ∑ k ∈ Finset.Icc k0 n, |G k|, ?_⟩
  rintro _ ⟨Q, hQn, hQc, rfl⟩
  rcases lt_or_ge Q.scale (k0 : ℤ) with hlt | hge
  · have h1 := hg Q hQn hQc hlt
    linarith only [h1, le_abs_self g, hsum0]
  · have hQ0 : (0 : ℤ) ≤ Q.scale := le_trans (Int.natCast_nonneg k0) hge
    set k : ℕ := Q.scale.toNat with hkdef
    have hk : (k : ℤ) = Q.scale := Int.toNat_of_nonneg hQ0
    have hk0 : k0 ≤ k := by omega
    have hkn : k ≤ n := by omega
    have hmem := akhcMM_mem_descendantsAtScale hQn hQc
    rw [← hk] at hmem
    have h1 := hG k hk0 hkn Q hmem
    have h2 : |G k| ≤ ∑ k ∈ Finset.Icc k0 n, |G k| :=
      Finset.single_le_sum (f := fun k => |G k|) (fun k _ => abs_nonneg (G k))
        (Finset.mem_Icc.2 ⟨hk0, hkn⟩)
    linarith only [h1, h2, le_abs_self (G k), abs_nonneg g]

/-! ## The probabilistic layer-cake: an a.e. domination and its integral -/

/-- **The integral of the dominating function.** Linearity of the expectation over the
finitely many large scales: `Y² + Σ_k G_k²` is integrable, with integral
`∫ Y² + Σ_k ∫ G_k²`. -/
theorem akhcMM_integral_dominator {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (n k0 : ℕ) (Y : Ω → ℝ) (G : ℕ → Ω → ℝ)
    (hY : Integrable (fun ω => Y ω ^ 2) μ)
    (hG : ∀ k ∈ Finset.Icc k0 n, Integrable (fun ω => G k ω ^ 2) μ) :
    Integrable (fun ω => Y ω ^ 2 + ∑ k ∈ Finset.Icc k0 n, G k ω ^ 2) μ ∧
      ∫ ω, (Y ω ^ 2 + ∑ k ∈ Finset.Icc k0 n, G k ω ^ 2) ∂μ =
        ∫ ω, Y ω ^ 2 ∂μ + ∑ k ∈ Finset.Icc k0 n, ∫ ω, G k ω ^ 2 ∂μ := by
  have hsum : Integrable (fun ω => ∑ k ∈ Finset.Icc k0 n, G k ω ^ 2) μ :=
    integrable_finsetSum _ hG
  refine ⟨hY.add hsum, ?_⟩
  rw [integral_add hY hsum, integral_finsetSum _ hG]

end

end SuperdiffusionCLT.AKHC61.Tails

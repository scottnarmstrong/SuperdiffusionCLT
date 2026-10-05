/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.AKHC61.WeakNorms.Prime
public import SuperdiffusionCLT.AKHC61.Response.CoarseAveragesC

/-!
# Package C6, part 2: the additivity defect is controlled by the normalized fluctuation

For the special vectors `p_e = σ̂^{-1/2} e`, `q_e = σ̂^{1/2} e` at scale `m` (package B4's
`akhcSpecialPAtScale`, `akhcSpecialQAtScale`), the response `J(R)` of any cube is
`½(q·g_R − p·f_R)` with `g_R`, `f_R` the self-averages of the response gradient and flux.
Hence `J(R) − J̄ = ½(q·(g_R − p₀) − p·(f_R − q₀))` with the constant
`J̄ = ½(q·p₀ − p·q₀)`, and package B4's pointwise bound gives

`(J(R) − J̄)² ≤ Θ_m · |Ahom_m^{-1/2}(bfA(R) − Ahom_m)Ahom_m^{-1/2}|²`.

Consequently the additivity defect `avg_R J(R) − J(cu_m)` at any child scale is bounded in
square by `2Θ_m (avg_R fluct(R) + fluct(cu_m))`: its second moment is the source's first node-7
term `e.variance.HC.prime`, with no `M`-weight.
-/

@[expose] public section

namespace SuperdiffusionCLT.AKHC61.WeakNorms

open Homogenization MeasureTheory
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.AKHC61.Response

noncomputable section

/-- **The response as a pairing of self-averages.** At every a.e.-elliptic sample,
`J(Q, p, q) = ½(q·g_Q − p·f_Q)`. -/
theorem akhcPrime_responseJ_eq_half {d : ℕ} [NeZero d] (a : RegCoeffField d)
    (ha : Book.Ch04.AELocallyUniformlyEllipticField a) (Q : TriadicCube d) (p q : Vec d) :
    Book.Ch04.restrictionResponseJObservableCubeSet Q p q a =
      (1 / 2 : ℝ) * (vecDot q (Book.Ch04.canonicalScalarResponseGradientAverageCubeSet Q Q p q
          a.toFun) -
        vecDot p (Book.Ch04.canonicalScalarResponseFluxAverageCubeSet Q Q p q a.toFun)) := by
  rw [akhcWNSq_responseJ_eq a ha Q p q,
    akhc_canonicalScalarResponseGradientAverageCubeSet_self_eq_blockMatrix a ha Q p q,
    akhc_canonicalScalarResponseFluxAverageCubeSet_self_eq_blockMatrix a ha Q p q]
  set A := coarseBlockMatrix (cubeSet Q) a.toFun
  simp only [blockVecDot, blockMatVecMul, vecDot, matVecMul, Pi.add_apply, Pi.sub_apply,
    Pi.neg_apply, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib,
    mul_add, mul_sub, mul_neg, neg_mul]
  have hc : (∑ x, q x * p x) = ∑ x, p x * q x := Finset.sum_congr rfl fun _ _ => mul_comm _ _
  linear_combination (1 / 2 : ℝ) * hc

/-- `vecDot x (y - z) = vecDot x y - vecDot x z`. -/
theorem akhcPrime_vecDot_sub_right {d : ℕ} (x y z : Vec d) :
    vecDot x (y - z) = vecDot x y - vecDot x z := by
  simp only [vecDot, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

/-- `(x^{1/2})² = x` for `x ≥ 0`. -/
theorem akhcPrime_rpow_half_sq {x : ℝ} (hx : 0 ≤ x) : (x ^ (1 / 2 : ℝ)) ^ 2 = x := by
  rw [← Real.sqrt_eq_rpow, Real.sq_sqrt hx]

/-- `(x^{-1/2})² = x⁻¹` for `x ≥ 0`. -/
theorem akhcPrime_rpow_neg_half_sq {x : ℝ} (hx : 0 ≤ x) : (x ^ (-(1 / 2) : ℝ)) ^ 2 = x⁻¹ := by
  rw [Real.rpow_neg hx, inv_pow, akhcPrime_rpow_half_sq hx]

/-- `(½(α − β))² ≤ ½(α² + β²)`. -/
theorem akhcPrime_half_sub_sq_le (α β : ℝ) :
    ((1 / 2 : ℝ) * (α - β)) ^ 2 ≤ (1 / 2 : ℝ) * (α ^ 2 + β ^ 2) := by
  nlinarith only [sq_nonneg (α + β)]

/-- `(c (e·x))² ≤ c² |x|²` for a unit `e`. -/
theorem akhcPrime_sq_smul_vecDot_le {d : ℕ} {e : Vec d} (he : vecNormSq e = 1) (c : ℝ)
    (x : Vec d) : (vecDot (c • e) x) ^ 2 ≤ c ^ 2 * vecNormSq x := by
  rw [vecDot_smul_left, mul_pow]
  have h := sq_vecDot_le_vecNormSq_mul_vecNormSq e x
  rw [he, one_mul] at h
  exact mul_le_mul_of_nonneg_left h (sq_nonneg c)

/-- The positive geometric mean `σ̂_m > 0`. -/
theorem akhcPrime_sigmaHat_pos {d : ℕ} [NeZero d] {nu : ℝ} {L : ℕ}
    {P : ProbabilityMeasure (ShellSeq d)} {m : ℤ}
    (hb : 0 < sigmaBarScalar nu L P (cubeSet (originCube d m)))
    (hc : 0 < sigmaBarStarInvScalar nu L P (cubeSet (originCube d m))) :
    0 < akhcSigmaHatAtScale nu L P m :=
  Real.sqrt_pos.2 (mul_pos hb (inv_pos.2 hc))

/-- **The response deviation is controlled by the normalized fluctuation.** For a unit `e`,
`(J(R, p_e, q_e) − J̄)² ≤ Θ_m · fluct_m(R)`, `J̄ = ½(q_e·p₀ − p_e·q₀)`. -/
theorem akhcPrime_J_sub_sq_le {d : ℕ} [NeZero d] {nu : ℝ} (hnu : 0 < nu) (L : ℕ)
    {P : ProbabilityMeasure (ShellSeq d)}
    (hJ4 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P)
    (a : RegCoeffField d) (ha : Book.Ch04.AELocallyUniformlyEllipticField a)
    (m : ℕ) (R : TriadicCube d) (e : Vec d)
    (hb : 0 < sigmaBarScalar nu L P (cubeSet (originCube d (m : ℤ))))
    (hc : 0 < sigmaBarStarInvScalar nu L P (cubeSet (originCube d (m : ℤ))))
    (he : vecNormSq e = 1) :
    (Book.Ch04.restrictionResponseJObservableCubeSet R (akhcSpecialPAtScale nu L P (m : ℤ) e)
        (akhcSpecialQAtScale nu L P (m : ℤ) e) a -
      (1 / 2 : ℝ) * (vecDot (akhcSpecialQAtScale nu L P (m : ℤ) e)
          (sigmaBarStarInvScalar nu L P (cubeSet (originCube d (m : ℤ))) •
              akhcSpecialQAtScale nu L P (m : ℤ) e - akhcSpecialPAtScale nu L P (m : ℤ) e) -
        vecDot (akhcSpecialPAtScale nu L P (m : ℤ) e)
          (akhcSpecialQAtScale nu L P (m : ℤ) e -
            sigmaBarScalar nu L P (cubeSet (originCube d (m : ℤ))) •
              akhcSpecialPAtScale nu L P (m : ℤ) e))) ^ 2 ≤
      SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P m *
        akhcFullBlockNormalizedFluctuationAtScale nu L P (m : ℤ) R a := by
  have hB4 := akhc_weighted_special_average_mismatch_le_fullBlockNormalized_fluctuation_unit
    hnu L hJ4 a ha m R e hb hc he
  dsimp only at hB4
  set σ := akhcSigmaHatAtScale nu L P (m : ℤ) with hσdef
  have hσ : 0 < σ := akhcPrime_sigmaHat_pos hb hc
  set p := akhcSpecialPAtScale nu L P (m : ℤ) e with hpdef
  set q := akhcSpecialQAtScale nu L P (m : ℤ) e with hqdef
  set p0 := sigmaBarStarInvScalar nu L P (cubeSet (originCube d (m : ℤ))) • q - p
  set q0 := q - sigmaBarScalar nu L P (cubeSet (originCube d (m : ℤ))) • p
  set g := Book.Ch04.canonicalScalarResponseGradientAverageCubeSet R R p q a.toFun
  set f := Book.Ch04.canonicalScalarResponseFluxAverageCubeSet R R p q a.toFun
  rw [akhcPrime_responseJ_eq_half a ha R p q]
  have hid : (1 / 2 : ℝ) * (vecDot q g - vecDot p f) -
      (1 / 2 : ℝ) * (vecDot q p0 - vecDot p q0) =
      (1 / 2 : ℝ) * (vecDot q (g - p0) - vecDot p (f - q0)) := by
    have e1 := akhcPrime_vecDot_sub_right q g p0
    have e2 := akhcPrime_vecDot_sub_right p f q0
    linear_combination (-(1 / 2) : ℝ) * e1 + (1 / 2 : ℝ) * e2
  rw [hid]
  have hq : (vecDot q (g - p0)) ^ 2 ≤ σ * vecNormSq (g - p0) := by
    have h := akhcPrime_sq_smul_vecDot_le he (σ ^ (1 / 2 : ℝ)) (g - p0)
    rwa [akhcPrime_rpow_half_sq hσ.le] at h
  have hp : (vecDot p (f - q0)) ^ 2 ≤ σ⁻¹ * vecNormSq (f - q0) := by
    have h := akhcPrime_sq_smul_vecDot_le he (σ ^ (-(1 / 2) : ℝ)) (f - q0)
    rwa [akhcPrime_rpow_neg_half_sq hσ.le] at h
  have h1 := akhcPrime_half_sub_sq_le (vecDot q (g - p0)) (vecDot p (f - q0))
  linarith only [h1, hq, hp, hB4]

/-! ## The additivity defect in square -/

theorem akhcPrime_card_pos {d : ℕ} (Q : TriadicCube d) (j : ℕ) :
    (0 : ℝ) < ((descendantsAtDepth Q j).card : ℝ) := by
  exact_mod_cast (descendantsAtDepth_nonempty Q j).card_pos

/-- `avg (F − c) = avg F − c`. -/
theorem akhcPrime_avg_sub_const {d : ℕ} (Q : TriadicCube d) (j : ℕ) (F : TriadicCube d → ℝ)
    (c : ℝ) : descendantsAverage Q j (fun R => F R - c) = descendantsAverage Q j F - c := by
  have hpos := akhcPrime_card_pos Q j
  unfold descendantsAverage
  simp only
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
  field_simp

/-- Jensen for the descendant average: `(avg F)² ≤ avg F²`. -/
theorem akhcPrime_avg_sq_le {d : ℕ} (Q : TriadicCube d) (j : ℕ) (F : TriadicCube d → ℝ) :
    (descendantsAverage Q j F) ^ 2 ≤ descendantsAverage Q j (fun R => F R ^ 2) := by
  have hpos := akhcPrime_card_pos Q j
  unfold descendantsAverage
  simp only
  set c : ℝ := ((descendantsAtDepth Q j).card : ℝ)
  have h := sq_sum_le_card_mul_sum_sq (s := descendantsAtDepth Q j) (f := F)
  have hc2 : 0 < c ^ 2 := by positivity
  rw [mul_pow, inv_pow]
  rw [inv_mul_le_iff₀ hc2]
  calc (∑ R ∈ descendantsAtDepth Q j, F R) ^ 2 ≤
        c * ∑ R ∈ descendantsAtDepth Q j, F R ^ 2 := h
    _ = c ^ 2 * (c⁻¹ * ∑ R ∈ descendantsAtDepth Q j, F R ^ 2) := by
        field_simp

/-- `avg (c F) = c avg F`. -/
theorem akhcPrime_avg_const_mul {d : ℕ} (Q : TriadicCube d) (j : ℕ) (F : TriadicCube d → ℝ)
    (c : ℝ) : descendantsAverage Q j (fun R => c * F R) = c * descendantsAverage Q j F := by
  unfold descendantsAverage
  simp only
  rw [← Finset.mul_sum]
  ring

/-- **The additivity defect in square.** For a unit `e`, at every a.e.-elliptic sample,
`defect_n² ≤ 2Θ_m (avg_R fluct_m(R) + fluct_m(cu_m))`. -/
theorem akhcPrime_defect_sq_le {d : ℕ} [NeZero d] {nu : ℝ} (hnu : 0 < nu) (L : ℕ)
    {P : ProbabilityMeasure (ShellSeq d)}
    (hJ4 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P)
    (a : RegCoeffField d) (ha : Book.Ch04.AELocallyUniformlyEllipticField a)
    (m : ℕ) (n : ℤ) (e : Vec d)
    (hb : 0 < sigmaBarScalar nu L P (cubeSet (originCube d (m : ℤ))))
    (hc : 0 < sigmaBarStarInvScalar nu L P (cubeSet (originCube d (m : ℤ))))
    (he : vecNormSq e = 1) :
    (Book.Ch05.Section53.WeakNormsMaximizer.responseDefectAverageAtScale (m : ℤ) n
        (akhcSpecialPAtScale nu L P (m : ℤ) e) (akhcSpecialQAtScale nu L P (m : ℤ) e) a) ^ 2 ≤
      2 * SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P m *
        (descendantsAverage (originCube d (m : ℤ)) (Int.toNat ((m : ℤ) - n))
            (fun R => akhcFullBlockNormalizedFluctuationAtScale nu L P (m : ℤ) R a) +
          akhcFullBlockNormalizedFluctuationAtScale nu L P (m : ℤ) (originCube d (m : ℤ)) a) := by
  set θ := SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P m
  set p := akhcSpecialPAtScale nu L P (m : ℤ) e
  set q := akhcSpecialQAtScale nu L P (m : ℤ) e
  set Jb : ℝ := (1 / 2 : ℝ) * (vecDot q
      (sigmaBarStarInvScalar nu L P (cubeSet (originCube d (m : ℤ))) • q - p) -
    vecDot p (q - sigmaBarScalar nu L P (cubeSet (originCube d (m : ℤ))) • p))
  set Q := originCube d (m : ℤ)
  set j := Int.toNat ((m : ℤ) - n)
  set J : TriadicCube d → ℝ := fun R => Book.Ch04.restrictionResponseJObservableCubeSet R p q a
  set fl : TriadicCube d → ℝ := fun R => akhcFullBlockNormalizedFluctuationAtScale nu L P (m : ℤ) R a
  have hJ : ∀ R, (J R - Jb) ^ 2 ≤ θ * fl R := fun R =>
    akhcPrime_J_sub_sq_le hnu L hJ4 a ha m R e hb hc he
  have hdef : Book.Ch05.Section53.WeakNormsMaximizer.responseDefectAverageAtScale (m : ℤ) n p q a =
      descendantsAverage Q j (fun R => J R - Jb) - (J Q - Jb) := by
    rw [akhcPrime_avg_sub_const]
    unfold Book.Ch05.Section53.WeakNormsMaximizer.responseDefectAverageAtScale
    ring
  rw [hdef]
  have h1 := akhcPrime_avg_sq_le Q j (fun R => J R - Jb)
  have h2 : descendantsAverage Q j (fun R => (J R - Jb) ^ 2) ≤ θ * descendantsAverage Q j fl := by
    rw [← akhcPrime_avg_const_mul]
    exact descendantsAverage_le_descendantsAverage Q j fun R _ => hJ R
  have h3 := hJ Q
  have h4 : (descendantsAverage Q j (fun R => J R - Jb) - (J Q - Jb)) ^ 2 ≤
      2 * (descendantsAverage Q j (fun R => J R - Jb)) ^ 2 + 2 * (J Q - Jb) ^ 2 := by
    nlinarith only [sq_nonneg (descendantsAverage Q j (fun R => J R - Jb) + (J Q - Jb))]
  have h5 : 2 * θ * (descendantsAverage Q j fl + fl Q) =
      2 * (θ * descendantsAverage Q j fl) + 2 * (θ * fl Q) := by ring
  linarith only [h1, h2, h3, h4, h5]

/-! ## The samplewise dominating function -/

/-- The fluctuation weight of the defect's second moment at child scale `n`:
`avg_R fluct_m(R) + fluct_m(cu_m)`. -/
noncomputable def akhcPrime_flPair {d : ℕ} [NeZero d] (nu : ℝ) (L : ℕ)
    (P : ProbabilityMeasure (ShellSeq d)) (m : ℕ) (n : ℤ) (a : RegCoeffField d) : ℝ :=
  descendantsAverage (originCube d (m : ℤ)) (Int.toNat ((m : ℤ) - n))
      (fun R => akhcFullBlockNormalizedFluctuationAtScale nu L P (m : ℤ) R a) +
    akhcFullBlockNormalizedFluctuationAtScale nu L P (m : ℤ) (originCube d (m : ℤ)) a

/-- The Young-split mismatch sum `Σ_n w_n (defect_n + (ε/2) G₀ + (θ/ε) flPair_n)`. -/
noncomputable def akhcPrime_misSum {d : ℕ} [NeZero d] (nu : ℝ) (L : ℕ)
    (P : ProbabilityMeasure (ShellSeq d)) (s' : ℝ) (m k : ℕ) (e : Vec d) (ε G0 : ℝ)
    (a : RegCoeffField d) : ℝ :=
  ∑ n ∈ Finset.Icc ((k : ℤ) + 1) (m : ℤ), akhcPrime_w (1 / 2) s' (m : ℤ) n *
    (Book.Ch05.Section53.WeakNormsMaximizer.responseDefectAverageAtScale (m : ℤ) n
        (akhcSpecialPAtScale nu L P (m : ℤ) e) (akhcSpecialQAtScale nu L P (m : ℤ) e) a +
      ε / 2 * G0 +
      SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P m / ε *
        akhcPrime_flPair nu L P m n a)

/-- **The Young split of the mismatch sum.** `(1 + M)·Σ w_n defect_n ≤ misSum`. -/
theorem akhcPrime_mismatch_young {d : ℕ} [NeZero d] {nu : ℝ} (hnu : 0 < nu) (L : ℕ)
    {P : ProbabilityMeasure (ShellSeq d)}
    (hJ4 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P)
    (a : RegCoeffField d) (ha : Book.Ch04.AELocallyUniformlyEllipticField a)
    (s' : ℝ) (m k : ℕ) (e : Vec d)
    (hb : 0 < sigmaBarScalar nu L P (cubeSet (originCube d (m : ℤ))))
    (hc : 0 < sigmaBarStarInvScalar nu L P (cubeSet (originCube d (m : ℤ))))
    (he : vecNormSq e = 1) {M G0 ε : ℝ} (hMG : M ^ 2 ≤ G0) (hε : 0 < ε) :
    (1 + M) * akhcPrime_defSum (1 / 2) s' (m : ℤ) (k : ℤ) (akhcSpecialPAtScale nu L P (m : ℤ) e)
        (akhcSpecialQAtScale nu L P (m : ℤ) e) a ≤
      akhcPrime_misSum nu L P s' m k e ε G0 a := by
  unfold akhcPrime_defSum akhcPrime_misSum
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun n hn => ?_
  set w := akhcPrime_w (1 / 2) s' (m : ℤ) n
  set D := Book.Ch05.Section53.WeakNormsMaximizer.responseDefectAverageAtScale (m : ℤ) n
    (akhcSpecialPAtScale nu L P (m : ℤ) e) (akhcSpecialQAtScale nu L P (m : ℤ) e) a
  set θ := SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P m
  set X := akhcPrime_flPair nu L P m n a
  have hw : 0 ≤ w := akhcPrime_w_nonneg _ _ _ _
  have hy := akhcPrime_young (M := M) (x := D) hε
  have hsq : D ^ 2 ≤ 2 * θ * X := akhcPrime_defect_sq_le hnu L hJ4 a ha m n e hb hc he
  have hdiv : D ^ 2 / (2 * ε) ≤ θ / ε * X := by
    rw [div_le_iff₀ (by positivity)]
    calc D ^ 2 ≤ 2 * θ * X := hsq
      _ = θ / ε * X * (2 * ε) := by field_simp
  have hG : ε / 2 * M ^ 2 ≤ ε / 2 * G0 := mul_le_mul_of_nonneg_left hMG (by positivity)
  have hin : (1 + M) * D ≤ D + ε / 2 * G0 + θ / ε * X := by
    linarith only [hy, hdiv, hG]
  calc (1 + M) * (w * D) = w * ((1 + M) * D) := by ring
    _ ≤ w * (D + ε / 2 * G0 + θ / ε * X) := mul_le_mul_of_nonneg_left hin hw

/-- The `β`-weighted node-16 dominating function (package B4's pointwise right-hand side). -/
noncomputable def akhcPrime_avgDom {d : ℕ} [NeZero d] (nu : ℝ) (L : ℕ)
    (P : ProbabilityMeasure (ShellSeq d)) (β : ℝ) (m k : ℕ) (a : RegCoeffField d) : ℝ :=
  (∑ n ∈ Finset.Icc ((k : ℤ) + 1) (m : ℤ),
      Real.rpow (3 : ℝ) (-β * (Int.toNat ((m : ℤ) - n) : ℝ))) *
    ∑ n ∈ Finset.Icc ((k : ℤ) + 1) (m : ℤ),
      Real.rpow (3 : ℝ) (-β * (Int.toNat ((m : ℤ) - n) : ℝ)) *
        descendantsAverage (originCube d (m : ℤ)) (Int.toNat ((m : ℤ) - n))
          (fun R => 2 * SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P m *
            akhcFullBlockNormalizedFluctuationAtScale nu L P (m : ℤ) R a)

/-- The route-W weak-norm energy at the source's normalization `M₀ = diag(σ̂, σ̂⁻¹)`
(`m₀ = b₀ # s_{*,0}`): `σ̂_m G² + σ̂_m⁻¹ F²`, samplewise. -/
noncomputable def akhcPrime_energy {d : ℕ} [NeZero d] (nu : ℝ) (L : ℕ)
    (P : ProbabilityMeasure (ShellSeq d)) (m : ℕ) (e : Vec d) (a : RegCoeffField d) : ℝ :=
  akhcSigmaHatAtScale nu L P (m : ℤ) *
      (Book.Ch04.canonicalScalarResponseGradientWeakNormCubeSet (originCube d (m : ℤ)) (1 / 2)
        (akhcSpecialPAtScale nu L P (m : ℤ) e) (akhcSpecialQAtScale nu L P (m : ℤ) e)
        (sigmaBarStarInvScalar nu L P (cubeSet (originCube d (m : ℤ))) •
            akhcSpecialQAtScale nu L P (m : ℤ) e - akhcSpecialPAtScale nu L P (m : ℤ) e)
        a.toFun) ^ 2 +
    (akhcSigmaHatAtScale nu L P (m : ℤ))⁻¹ *
      (Book.Ch04.canonicalScalarResponseFluxWeakNormCubeSet (originCube d (m : ℤ)) (1 / 2)
        (akhcSpecialPAtScale nu L P (m : ℤ) e) (akhcSpecialQAtScale nu L P (m : ℤ) e)
        (akhcSpecialQAtScale nu L P (m : ℤ) e -
          sigmaBarScalar nu L P (cubeSet (originCube d (m : ℤ))) •
            akhcSpecialPAtScale nu L P (m : ℤ) e)
        a.toFun) ^ 2

/-- The constant-tail energy `σ̂ K_G² + σ̂⁻¹ K_F²`. -/
noncomputable def akhcPrime_constTail {d : ℕ} [NeZero d] (nu : ℝ) (L : ℕ)
    (P : ProbabilityMeasure (ShellSeq d)) (m k : ℕ) (e : Vec d) : ℝ :=
  akhcSigmaHatAtScale nu L P (m : ℤ) *
      (Book.Ch05.Section53.WeakNormsMaximizer.gradientConstantTailAtScale (m : ℤ) (k : ℤ) (1 / 2)
        (sigmaBarStarInvScalar nu L P (cubeSet (originCube d (m : ℤ))) •
            akhcSpecialQAtScale nu L P (m : ℤ) e - akhcSpecialPAtScale nu L P (m : ℤ) e)) ^ 2 +
    (akhcSigmaHatAtScale nu L P (m : ℤ))⁻¹ *
      (Book.Ch05.Section53.WeakNormsMaximizer.fluxConstantTailAtScale (m : ℤ) (k : ℤ) (1 / 2)
        (akhcSpecialQAtScale nu L P (m : ℤ) e -
          sigmaBarScalar nu L P (cubeSet (originCube d (m : ℤ))) •
            akhcSpecialPAtScale nu L P (m : ℤ) e)) ^ 2

/-- **The samplewise dominating bound for the weighted weak-norm energy.** With
`κ = σ̂ K_l + σ̂⁻¹ K_u` and `C` the maximizer constant, under `λ⁻¹ ≤ K_l(1+M)`,
`Λ ≤ K_u(1+M)`, `J(cu_m) ≤ (1+M) B_J`, `M² ≤ G₀`:
`energy ≤ 16 (avgDom + C² κ S_w misSum + C² u² κ (B_J · 2(1+G₀)) + C² constTail)`. -/
theorem akhcPrime_energy_le {d : ℕ} [NeZero d] {nu : ℝ} (hnu : 0 < nu) (L : ℕ)
    {P : ProbabilityMeasure (ShellSeq d)}
    (hJ4 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P)
    (a : RegCoeffField d) (ha : Book.Ch04.AELocallyUniformlyEllipticField a)
    {k m : ℕ} (hkm : k < m) {β s' : ℝ} (hβ : β ≤ 1 / 2) (hlo : 1 / 4 ≤ s') (hhi : s' < 1 / 2)
    (e : Vec d)
    (hb : 0 < sigmaBarScalar nu L P (cubeSet (originCube d (m : ℤ))))
    (hc : 0 < sigmaBarStarInvScalar nu L P (cubeSet (originCube d (m : ℤ))))
    (he : vecNormSq e = 1) {Kl Ku Bj M G0 ε : ℝ} (hKl : 0 ≤ Kl) (hKu : 0 ≤ Ku) (hBj : 0 ≤ Bj)
    (hM : 0 ≤ M) (hMG : M ^ 2 ≤ G0) (hε : 0 < ε)
    (hl : (Book.Ch04.lambdaSqCoeffField (originCube d (m : ℤ)) s' (.finite 1) a)⁻¹ ≤
      Kl * (1 + M))
    (hL : Book.Ch04.LambdaSqCoeffField (originCube d (m : ℤ)) s' (.finite 1) a ≤ Ku * (1 + M))
    (hJ : Book.Ch04.restrictionResponseJObservableCubeSet (originCube d (m : ℤ))
        (akhcSpecialPAtScale nu L P (m : ℤ) e) (akhcSpecialQAtScale nu L P (m : ℤ) e) a ≤
      (1 + M) * Bj) :
    akhcPrime_energy nu L P m e a ≤
      16 * (akhcPrime_avgDom nu L P β m k a +
        Book.Ch05.Section53.WeakNormsMaximizer.section53WeakNormMaximizerConst d ^ 2 *
            (akhcSigmaHatAtScale nu L P (m : ℤ) * Kl +
              (akhcSigmaHatAtScale nu L P (m : ℤ))⁻¹ * Ku) *
          akhcPrime_wSum (1 / 2) s' (m : ℤ) (k : ℤ) *
            akhcPrime_misSum nu L P s' m k e ε G0 a +
        Book.Ch05.Section53.WeakNormsMaximizer.section53WeakNormMaximizerConst d ^ 2 *
          akhcPrime_u (1 / 2) s' (m : ℤ) (k : ℤ) ^ 2 *
            (akhcSigmaHatAtScale nu L P (m : ℤ) * Kl +
              (akhcSigmaHatAtScale nu L P (m : ℤ))⁻¹ * Ku) * (Bj * (2 * (1 + G0))) +
        Book.Ch05.Section53.WeakNormsMaximizer.section53WeakNormMaximizerConst d ^ 2 *
          akhcPrime_constTail nu L P m k e) := by
  have hkm' : (k : ℤ) < (m : ℤ) := by exact_mod_cast hkm
  have hs'lo : (1 / 2 : ℝ) / 2 ≤ s' := by linarith only [hlo]
  have hN : 0 ≤ 1 + M := by linarith only [hM]
  have hNl : 0 ≤ Kl * (1 + M) := mul_nonneg hKl hN
  have hNu : 0 ≤ Ku * (1 + M) := mul_nonneg hKu hN
  have hNB : 0 ≤ (1 + M) * Bj := mul_nonneg hN hBj
  set p := akhcSpecialPAtScale nu L P (m : ℤ) e
  set q := akhcSpecialQAtScale nu L P (m : ℤ) e
  set p0 := sigmaBarStarInvScalar nu L P (cubeSet (originCube d (m : ℤ))) • q - p
  set q0 := q - sigmaBarScalar nu L P (cubeSet (originCube d (m : ℤ))) • p
  have hG := akhcPrime_gradient_sq_le a ha hkm' (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
    hs'lo hhi p q p0 hl hNl hJ hNB
  have hF := akhcPrime_flux_sq_le a ha hkm' (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
    hs'lo hhi p q q0 hL hNu hJ hNB
  have hNA := akhc_paired_highScaleAverageTerms_special_le_weighted_fullBlockNormalized_fluctuation
    hnu L hJ4 a ha (k := k) (m := m) β (1 / 2) (1 / 2) hβ hβ e hb hc he
  dsimp only at hNA
  have hX := akhcPrime_mismatch_young hnu L hJ4 a ha s' m k e hb hc he hMG hε
  have hY : (1 + M) * (1 + M) ≤ 2 * (1 + G0) := by
    nlinarith only [akhcPrime_one_add_sq_le M, hMG]
  set σ := akhcSigmaHatAtScale nu L P (m : ℤ)
  have hσ : 0 < σ := akhcPrime_sigmaHat_pos hb hc
  have hσi : 0 < σ⁻¹ := inv_pos.2 hσ
  set C := Book.Ch05.Section53.WeakNormsMaximizer.section53WeakNormMaximizerConst d
  set Sw := akhcPrime_wSum (1 / 2) s' (m : ℤ) (k : ℤ)
  set u := akhcPrime_u (1 / 2) s' (m : ℤ) (k : ℤ)
  set Ds := akhcPrime_defSum (1 / 2) s' (m : ℤ) (k : ℤ) p q a
  set Xb := akhcPrime_misSum nu L P s' m k e ε G0 a
  have hSw : 0 ≤ Sw := akhcPrime_wSum_nonneg _ _ _ _
  have hC2 : 0 ≤ C ^ 2 := sq_nonneg C
  have hu2 : 0 ≤ u ^ 2 := sq_nonneg u
  have hG' := mul_le_mul_of_nonneg_left hG hσ.le
  have hF' := mul_le_mul_of_nonneg_left hF hσi.le
  have hX1 := mul_le_mul_of_nonneg_left hX
    (mul_nonneg (mul_nonneg (mul_nonneg hC2 hσ.le) hKl) hSw)
  have hX2 := mul_le_mul_of_nonneg_left hX
    (mul_nonneg (mul_nonneg (mul_nonneg hC2 hσi.le) hKu) hSw)
  have hY1 := mul_le_mul_of_nonneg_left hY
    (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hC2 hu2) hσ.le) hKl) hBj)
  have hY2 := mul_le_mul_of_nonneg_left hY
    (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hC2 hu2) hσi.le) hKu) hBj)
  unfold akhcPrime_energy akhcPrime_avgDom akhcPrime_constTail
  linarith only [hG', hF', hNA, hX1, hX2, hY1, hY2]

end

end SuperdiffusionCLT.AKHC61.WeakNorms

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section4.MinimalScales.NearShiftAssemblyG
public import SuperdiffusionCLT.Section4.MinimalScales.NearShiftCap
public import SuperdiffusionCLT.Section4.MinimalScales.DeepCrudePolyB

/-!
# Case `L ≤ m + h`: the pathwise bound and the crude cap on descendant cubes

* `srootNS_caseA_pathwise` (B1): for the centered field `srootE_field nu ω L m n k`, every
  descendant cube `R` of `cu_n` at depth `l` satisfies
  `Φ_R ≤ T_R + B_R`, with `T_R = C σ⁻²(‖h0‖² + (L - (n-l))₊ + K' log² L) + X1_R(ω)` and
  `B_R = (1 + σ⁻¹‖h0‖²) X2_R(ω)`; the witnesses `X1, X2` are chosen for each `(L, l, R)`.
* `srootNS_response_le_crude` (B3): the same `Φ_R` is bounded, for every cutoff `L`, depth `l`
  and descendant `R` at once, by the `Γ_{1/2}` variable of `srootD4_hCrudePolyHalf`. Combined
  with `srootNS_le_max_zero_add_min` and `srootNS_weighted_sum_cap_le` this gives the capped
  bound.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section4.MinimalScales

noncomputable section

/-- **B1.** Pathwise bound for `Φ_R = normalizedBlockResponseMax R (srootE_field nu ω L m n k)
(σ_m • 1)` on every descendant cube `R` of `cu_n` at depth `l ≤ n`, from the uniform-in-`h0`
parameterized mixing lemma. -/
theorem srootNS_caseA_pathwise (d : ℕ) [NeZero d]
    (hParam :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (nu cStar nondeg : ℝ) (hnu : 0 < nu) (_hnu1 : nu ≤ 1),
        ∀ (P : MeasureTheory.ProbabilityMeasure
              (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
          (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
          (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P)
          (hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P),
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P →
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P →
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ5 d P cStar nondeg hPrefix hJ2 hJ3 →
          ∀ alpha M K : ℝ, 0 ≤ alpha → alpha < 1 → 1 ≤ M → 1 ≤ K →
            ∀ L m r : ℕ,
              SuperdiffusionCLT.Frozen.Section4.lNaught C (C * (M + K)) alpha cStar nu nondeg ≤
                (L : ℝ) →
              SuperdiffusionCLT.Frozen.Section4.lNaught C (C * (M + K)) alpha cStar nu nondeg ≤
                (m : ℝ) →
              (L : ℝ) - M * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ) ≤ (m : ℝ) →
              |(L : ℝ) - (r : ℝ)| ≤ K * Real.log (L : ℝ) →
              ∃ X1 X2 : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ,
                Measurable X1 ∧
                Homogenization.IndependentSums.IsBigO P.toMeasure
                    (Homogenization.IndependentSums.gammaSigma 1) X1
                    (C * (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu r P) ^
                        (-(2 : ℝ)) *
                      (max 0 ((L : ℝ) - (m : ℝ)) + K * Real.log (L : ℝ))) ∧
                Measurable X2 ∧
                Homogenization.IndependentSums.IsBigO P.toMeasure
                    (Homogenization.IndependentSums.gammaSigma ((1 : ℝ) / 3)) X2
                    (C * (m : ℝ) ^ (-(5000 : ℝ))) ∧
                ∀ (h0 : Homogenization.Mat d) (hh0 : Homogenization.matTranspose h0 = -h0),
                  ∀ omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d,
                    ∀ eta : Homogenization.BlockVec d,
                      SuperdiffusionCLT.Section2.Carriers.blockVecNorm eta = 1 →
                        Homogenization.Book.Ch02.doubledResponseJ
                          (Homogenization.Book.Ch02.cubeDomain
                            (Homogenization.originCube d (m : ℤ)))
                          (SuperdiffusionCLT.Section4.NewMixing.newMixParam_aLplusH0 nu hnu omega L m h0 hh0)
                          (SuperdiffusionCLT.Section4.NewMixing.newMixParam_bfAhomPow nu r P (-(1 : ℝ) / 2) eta)
                          (SuperdiffusionCLT.Section4.NewMixing.newMixParam_bfAhomPow nu r P ((1 : ℝ) / 2) eta) ≤
                        C * (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu r P) ^
                            (-(2 : ℝ)) *
                            ((Homogenization.Book.Ch02.matrixOperatorNorm h0) ^ 2 +
                              max 0 ((L : ℝ) - (m : ℝ)) +
                              K * Real.log (L : ℝ) ^ (2 : ℝ)) +
                          X1 omega +
                          (1 + (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu r P) ^
                                (-(1 : ℝ)) *
                              (Homogenization.Book.Ch02.matrixOperatorNorm h0) ^ 2) * X2 omega) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (nu cStar nondeg : ℝ) (_hnu : 0 < nu) (_hnu1 : nu ≤ 1),
        ∀ (P : MeasureTheory.ProbabilityMeasure
              (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
          (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
          (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P)
          (hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P),
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P →
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P →
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ5 d P cStar nondeg hPrefix hJ2 hJ3 →
          ∀ K : ℝ, 1 ≤ K →
            ∀ m L n l : ℕ, ∀ k : Fin d → ℤ, l ≤ n →
              SuperdiffusionCLT.Frozen.Section4.lNaught C (C * (K + K)) (1 / 2) cStar nu nondeg ≤
                (L : ℝ) →
              SuperdiffusionCLT.Frozen.Section4.lNaught C (C * (K + K)) (1 / 2) cStar nu nondeg ≤
                ((n - l : ℕ) : ℝ) →
              (L : ℝ) - K * (L : ℝ) ^ ((1 : ℝ) / 2) * Real.log (L : ℝ) ^ (3 : ℝ) ≤
                ((n - l : ℕ) : ℝ) →
              |(L : ℝ) - (m : ℝ)| ≤ K * Real.log (L : ℝ) →
              ∀ R ∈ Homogenization.descendantsAtScale (Homogenization.originCube d (n : ℤ))
                  ((n : ℤ) - (l : ℤ)),
              ∃ X1 X2 : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ,
                Measurable X1 ∧
                Homogenization.IndependentSums.IsBigO P.toMeasure
                    (Homogenization.IndependentSums.gammaSigma 1) X1
                    (C * (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P) ^
                        (-(2 : ℝ)) *
                      (max 0 ((L : ℝ) - ((n - l : ℕ) : ℝ)) + K * Real.log (L : ℝ))) ∧
                Measurable X2 ∧
                Homogenization.IndependentSums.IsBigO P.toMeasure
                    (Homogenization.IndependentSums.gammaSigma ((1 : ℝ) / 3)) X2
                    (C * ((n - l : ℕ) : ℝ) ^ (-(5000 : ℝ))) ∧
                  ∀ omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d,
                    Homogenization.normalizedBlockResponseMax R
                        (srootE_field nu omega L m n k)
                        (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P •
                            (1 : Homogenization.Mat d)) ≤
                      C * (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P) ^
                          (-(2 : ℝ)) *
                          ((Homogenization.Book.Ch02.matrixOperatorNorm (srootNS_h0 m L omega)) ^ 2 +
                            max 0 ((L : ℝ) - ((n - l : ℕ) : ℝ)) +
                            K * Real.log (L : ℝ) ^ (2 : ℝ)) +
                        X1 omega +
                        (1 + (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P) ^
                              (-(1 : ℝ)) *
                            (Homogenization.Book.Ch02.matrixOperatorNorm (srootNS_h0 m L omega)) ^ 2) *
                          X2 omega := by
  obtain ⟨C, hC1, hG⟩ := srootNS_localBase_translateZ_le d hParam
  refine ⟨C, hC1, ?_⟩
  intro nu cStar nondeg hnu hnu1 P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5 K hK m L n l k hl h1 h2 h3 h4 R hR
  have hRs : R.scale = (((n - l : ℕ) : ℕ) : ℤ) := by
    rw [Homogenization.descendant_scale_eq_of_mem_descendantsAtScale hR]
    omega
  exact hG nu cStar nondeg hnu hnu1 P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5 K hK m (n - l) L n k
    h1 h2 h3 h4 R hRs

/-- The squared infinite-exponent scale response dominates the block response of each descendant
cube. -/
theorem srootNS_response_le_of_scaleResponse_sq_le {d : ℕ} [NeZero d]
    {Q R : Homogenization.TriadicCube d} {k : ℤ} (hk : k ≤ Q.scale)
    (hR : R ∈ Homogenization.descendantsAtScale Q k)
    (a : Homogenization.CoeffField d) (a0 : Homogenization.Mat d) {G : ℝ}
    (h : Real.rpow (Homogenization.scaleResponseAtScale Q k
        Homogenization.MultiscaleExponent.infinity a a0) 2 ≤ G) :
    Homogenization.normalizedBlockResponseMax R a a0 ≤ G := by
  have hle := Homogenization.normalizedBlockResponseMax_le_maxDescendantNormalizedBlockResponseAtScale
    a a0 hR
  have hnn := Homogenization.maxDescendantNormalizedBlockResponseAtScale_nonneg Q hk a a0
  have heq : Real.rpow (Homogenization.scaleResponseAtScale Q k
      Homogenization.MultiscaleExponent.infinity a a0) 2 =
      Homogenization.maxDescendantNormalizedBlockResponseAtScale Q k a a0 := by
    show (Homogenization.maxDescendantNormalizedBlockResponseAtScale Q k a a0 ^ (1 / 2 : ℝ)) ^
      (2 : ℝ) = _
    rw [← Real.rpow_mul hnn]
    norm_num
  linarith only [hle, heq, h]

/-- **B3 (crude cap).** The block responses of all descendant cubes of `cu_n`, at every depth and
for every cutoff `L`, are bounded by one `Γ_{1/2}` variable of amplitude `A0 (1 + m)^10`
(`srootD4_hCrudePolyHalf`). -/
theorem srootNS_response_le_crude (d : ℕ) [NeZero d] :
    ∃ A0 : ℝ, 1 ≤ A0 ∧ ∀ C1 : ℝ, 1 ≤ C1 →
      ∀ (nu cStar nondeg : ℝ), 0 < nu → nu ≤ 1 →
        ∀ (P : MeasureTheory.ProbabilityMeasure
              (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
          (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
          (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P)
          (hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P),
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P →
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P →
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ5 d P cStar nondeg
              hPrefix hJ2 hJ3 →
          ∀ s : ℝ, 0 < s → s ≤ 1 → ∀ K : ℝ, C1 ≤ K → ∀ m n : ℕ,
            SuperdiffusionCLT.Frozen.Section4.lNaught C1 (C1 * s⁻¹ * K) (1 / 2) cStar nu nondeg ≤ (m : ℝ) →
            m - ⌈K * Real.log (m : ℝ)⌉₊ ≤ n → n ≤ m →
            ∀ k : Fin d → ℤ, (fun x => (fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x) ''
                  Homogenization.cubeSet (Homogenization.originCube d (n : ℤ)) ⊆
                Homogenization.cubeSet (Homogenization.originCube d (m : ℤ)) →
              ∃ G : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ,
                Measurable G ∧
                Homogenization.IndependentSums.IsBigO P.toMeasure
                  (Homogenization.IndependentSums.gammaSigma (1 / 2)) G
                  (A0 * (1 + (m : ℝ)) ^ (10 : ℝ)) ∧
                ∀ᵐ omega ∂P.toMeasure, ∀ L l : ℕ,
                  ∀ R ∈ Homogenization.descendantsAtScale (Homogenization.originCube d (n : ℤ))
                      ((n : ℤ) - (l : ℤ)),
                    Homogenization.normalizedBlockResponseMax R
                        (srootE_field nu omega L m n k)
                        (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P •
                          (1 : Homogenization.Mat d)) ≤ G omega := by
  obtain ⟨A0, hA0, hcr⟩ := srootD4_hCrudePolyHalf d
  refine ⟨A0, hA0, ?_⟩
  intro C1 hC1 nu cStar nondeg hnu hnu1 P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5 s hs0 hs1 K hK m n
    hL hn1 hn2 k hk
  obtain ⟨G, hGm, hGO, hGae⟩ := hcr C1 hC1 nu cStar nondeg hnu hnu1 P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5
    s hs0 hs1 K hK m n hL hn1 hn2 k hk
  refine ⟨G, hGm, hGO, ?_⟩
  filter_upwards [hGae] with omega homega L l R hR
  refine srootNS_response_le_of_scaleResponse_sq_le ?_ hR _ _ (homega L l)
  show (n : ℤ) - (l : ℤ) ≤ (n : ℤ)
  omega

end

end SuperdiffusionCLT.Section4.MinimalScales

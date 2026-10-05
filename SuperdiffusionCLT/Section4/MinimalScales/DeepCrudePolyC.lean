/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section4.MinimalScales.DeepCrudePolyB
public import SuperdiffusionCLT.Section4.MinimalScales.DeepGeom
public import SuperdiffusionCLT.Section4.MinimalScales.SkeletonMathcalE
public import SuperdiffusionCLT.Section2.Estimates.Stream.IncrementMoreoverBlockF
public import SuperdiffusionCLT.Section4.HomogBelow.ThetaLmGammaSigmaWeaken

/-!
# `hDeep` for `srootE_mathcalE_bounds_of_inputs`

The combinator turns a polynomially growing `Γ_q` crude bound on the squared deep-scale response
into the exact conclusion of `hDeep`: the threshold constant `C0 := 1000 + p` makes the geometric
factor `3^{-2 s ·threshold}` decay like `m^{-(2000+p)}`, and the factor `(1 + m)^p ≤ (2m)^p` is
absorbed into the existential amplitude. `srootD4_hDeep` instantiates it with the crude bound of
`DeepCrudePolyB.lean` (`p = 10`, `q = 1/2`).
-/

@[expose] public section

namespace SuperdiffusionCLT.Section4.MinimalScales

open MeasureTheory
open Homogenization.IndependentSums

/-- `lNaught` is always strictly positive (private copy of a `private` lemma of the
deep-scale development). -/
private theorem srootD4_lNaught_pos {C M alpha cStar nu K : ℝ}
    (hC : 0 < C) (hM : 0 ≤ M) (hK : 0 ≤ K) (halpha1 : alpha < 1)
    (hcStar : 0 < cStar) (hnu : 0 < nu) :
    0 < SuperdiffusionCLT.Frozen.Section4.lNaught C M alpha cStar nu K := by
  unfold SuperdiffusionCLT.Frozen.Section4.lNaught
  have hden_pos : (0:ℝ) < (1 - alpha) ^ (12:ℝ) * nu ^ (4:ℝ) :=
    mul_pos (Real.rpow_pos_of_pos (by linarith only [halpha1]) _) (Real.rpow_pos_of_pos hnu _)
  have hnum_pos : (0:ℝ) < C * (M + 1 + K) * cStar ^ (-(3:ℝ)) :=
    mul_pos (mul_pos hC (by linarith only [hM, hK])) (Real.rpow_pos_of_pos hcStar _)
  have hfrac_pos : (0:ℝ) < C * (M + 1 + K) * cStar ^ (-(3:ℝ)) /
      ((1 - alpha) ^ (12:ℝ) * nu ^ (4:ℝ)) := div_pos hnum_pos hden_pos
  have hnum_pos' : (0:ℝ) < (M + 1 + K) * cStar ^ (-(3:ℝ)) :=
    mul_pos (by linarith only [hM, hK]) (Real.rpow_pos_of_pos hcStar _)
  have harg_gt1 : (1:ℝ) <
      2 + (M + 1 + K) * cStar ^ (-(3:ℝ)) / (nu * (1 - alpha)) := by
    have hnn : (0:ℝ) ≤ (M + 1 + K) * cStar ^ (-(3:ℝ)) / (nu * (1 - alpha)) := by
      apply div_nonneg hnum_pos'.le
      exact mul_nonneg hnu.le (by linarith only [halpha1])
    linarith only [hnn]
  have hlog_pos : (0:ℝ) < Real.log (2 + (M + 1 + K) * cStar ^ (-(3:ℝ)) / (nu * (1 - alpha))) :=
    Real.log_pos harg_gt1
  have hbase_pos : (0:ℝ) <
      C * (M + 1 + K) * cStar ^ (-(3:ℝ)) / ((1 - alpha) ^ (12:ℝ) * nu ^ (4:ℝ)) *
        Real.log (2 + (M + 1 + K) * cStar ^ (-(3:ℝ)) / (nu * (1 - alpha))) ^ (12:ℝ) :=
    mul_pos hfrac_pos (Real.rpow_pos_of_pos hlog_pos _)
  exact Real.rpow_pos_of_pos hbase_pos _

/-- **`hDeep` from a polynomially-growing crude-ellipticity hypothesis, at a tail exponent
`q ≥ 1/3`.** `hCrudePoly` is the `hCrude` of the deep-scale development,
except that the squared response `scaleResponseAtScale` is dominated by a `Γ_q` variable `R` at
amplitude `A0 * (1 + m) ^ p`
(fixed exponent `p ≥ 0`) instead of a flat `Γ₁` amplitude `A0`. The conclusion is the `Γ_{1/3}`
bound, so any `q ≥ 1/3` suffices. -/
theorem srootD4_hDeep_of_polyCrude_gamma (d : ℕ) [NeZero d] (p q : ℝ) (hp : 0 ≤ p) (hq : 1 / 3 ≤ q)
    (hCrudePoly : ∃ A0 : ℝ, 1 ≤ A0 ∧ ∀ C1 : ℝ, 1 ≤ C1 →
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
              ∃ R : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ,
                Measurable R ∧
                IsBigO P.toMeasure (gammaSigma q) R (A0 * (1 + (m : ℝ)) ^ p) ∧
                ∀ᵐ omega ∂P.toMeasure, ∀ L j : ℕ,
                  Real.rpow (Homogenization.scaleResponseAtScale
                      (Homogenization.originCube d (n : ℤ)) ((n : ℤ) - (j : ℤ))
                      Homogenization.MultiscaleExponent.infinity
                      (srootE_field nu omega L m n k)
                      ((SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P) •
                        (1 : Homogenization.Mat d))) 2 ≤
                    R omega) :
    ∃ C0 : ℝ, 1 ≤ C0 ∧ ∃ A : ℝ, 1 ≤ A ∧ ∀ C1 : ℝ, A ≤ C1 →
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
              ∃ Y2 : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ,
                Measurable Y2 ∧
                IsBigO P.toMeasure (gammaSigma (1 / 3)) Y2 (A * (m : ℝ) ^ (-(2000 : ℝ))) ∧
                ∀ᵐ omega ∂P.toMeasure, ∀ L : ℕ, (m : ℝ) - C1 * s⁻¹ * ((⌈K * Real.log (m : ℝ)⌉₊ : ℕ) : ℝ) ≤ (L : ℝ) →
                  ∑' l : ℕ, srootE_term s (srootE_field nu omega L m n k)
                      ((SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P) • (1 : Homogenization.Mat d)) n
                      (l + (⌈C0 * s⁻¹ * Real.log (m : ℝ)⌉₊ + 1)) ≤ Y2 omega := by
  obtain ⟨A0, hA01, hCrudeA⟩ := hCrudePoly
  have h2p1 : (1:ℝ) ≤ (2:ℝ) ^ p := Real.one_le_rpow (by norm_num) hp
  have hA1 : (1:ℝ) ≤ A0 * (2:ℝ) ^ p := by
    have hh := mul_le_mul hA01 h2p1 (by norm_num) (by linarith only [hA01])
    linarith only [hh]
  have hC0ge1 : (1:ℝ) ≤ 1000 + p := by linarith only [hp]
  refine ⟨1000 + p, hC0ge1, A0 * (2:ℝ) ^ p, hA1, ?_⟩
  intro C1 hC1A nu cStar nondeg hnu hnu1 P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5 s hs0 hs1 K hK m n
    hLm hn1 hn2 k hk
  have hC11 : (1:ℝ) ≤ C1 := le_trans hA1 hC1A
  obtain ⟨R, hRmeas, hRO, hRae⟩ :=
    hCrudeA C1 hC11 nu cStar nondeg hnu hnu1 P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5 s hs0 hs1 K hK m n
      hLm hn1 hn2 k hk
  set thr : ℕ := ⌈(1000 + p) * s⁻¹ * Real.log (m : ℝ)⌉₊ + 1 with hthr
  set c : ℝ := (3:ℝ) ^ (-(s * 2 * (thr : ℝ))) with hcdef
  have hc0 : 0 ≤ c := Real.rpow_nonneg (by norm_num) _
  refine ⟨fun omega => c * R omega, hRmeas.const_mul c, ?_, ?_⟩
  · -- IsBigO (gammaSigma (1/3)) (c * R) ((A0 * 2 ^ p) * m ^ (-2000))
    have hlog0 : (0:ℝ) ≤ Real.log (m:ℝ) := Real.log_natCast_nonneg m
    have hslog3 : (1:ℝ) < Real.log 3 :=
      SuperdiffusionCLT.Section2.Estimates.Stream.one_lt_log_three
    have hmpos : 0 < (m:ℝ) := by
      have hK0 : 0 ≤ K := le_trans (by linarith only [hC11]) hK
      have hM0 : 0 ≤ C1 * s⁻¹ * K := by
        have hsinv0 : 0 ≤ s⁻¹ := inv_nonneg.2 hs0.le
        have hC10 : 0 ≤ C1 := by linarith only [hC11]
        positivity
      have hcS := hJ5.cStar_pos
      have hnd0 : 0 ≤ nondeg := hJ5.K_pos.le
      have hlN : 0 < SuperdiffusionCLT.Frozen.Section4.lNaught C1 (C1 * s⁻¹ * K) (1/2) cStar
          nu nondeg := srootD4_lNaught_pos (by linarith only [hC11]) hM0 hnd0
        (by norm_num) hcS hnu
      exact lt_of_lt_of_le hlN hLm
    have hthrge : (1000 + p) * s⁻¹ * Real.log (m:ℝ) ≤ (thr : ℝ) := by
      have h1 : (1000 + p) * s⁻¹ * Real.log (m:ℝ) ≤
          (⌈(1000 + p) * s⁻¹ * Real.log (m:ℝ)⌉₊ : ℝ) := Nat.le_ceil _
      have h2 : (⌈(1000 + p) * s⁻¹ * Real.log (m:ℝ)⌉₊ : ℝ) ≤ (thr : ℝ) := by
        rw [hthr]; push_cast; linarith only []
      linarith only [h1, h2]
    have hexp : ((2000:ℝ) + p) * Real.log (m:ℝ) ≤ s * 2 * (thr : ℝ) := by
      have hsinv : s * ((1000 + p) * s⁻¹ * Real.log (m:ℝ)) = (1000 + p) * Real.log (m:ℝ) := by
        field_simp
      have hstep : s * ((1000 + p) * s⁻¹ * Real.log (m:ℝ)) ≤ s * (thr : ℝ) :=
        mul_le_mul_of_nonneg_left hthrge hs0.le
      rw [hsinv] at hstep
      have hpL : (0:ℝ) ≤ p * Real.log (m:ℝ) := mul_nonneg hp hlog0
      nlinarith only [hstep, hpL]
    have hcle : c ≤ (m:ℝ) ^ (-((2000:ℝ) + p)) := by
      have hstep1 : (3:ℝ) ^ (-(s * 2 * (thr : ℝ))) ≤ (3:ℝ) ^ (-(((2000:ℝ) + p) * Real.log (m:ℝ))) := by
        refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
        linarith only [hexp]
      have heq1 : (3:ℝ) ^ (-(((2000:ℝ) + p) * Real.log (m:ℝ))) =
          Real.exp (Real.log 3 * (-(((2000:ℝ) + p) * Real.log (m:ℝ)))) :=
        Real.rpow_def_of_pos (by norm_num) _
      have heq2 : (m:ℝ) ^ (-((2000:ℝ) + p)) = Real.exp (Real.log (m:ℝ) * (-((2000:ℝ) + p))) :=
        Real.rpow_def_of_pos hmpos _
      have hkey : (0:ℝ) ≤ ((2000:ℝ) + p) * Real.log (m:ℝ) * (Real.log 3 - 1) :=
        mul_nonneg (mul_nonneg (by linarith only [hp]) hlog0) (by linarith only [hslog3])
      have hexp2 : Real.log 3 * (-(((2000:ℝ) + p) * Real.log (m:ℝ))) ≤
          Real.log (m:ℝ) * (-((2000:ℝ) + p)) := by
        nlinarith only [hkey]
      have hstep2 : (3:ℝ) ^ (-(((2000:ℝ) + p) * Real.log (m:ℝ))) ≤ (m:ℝ) ^ (-((2000:ℝ) + p)) := by
        rw [heq1, heq2]
        exact Real.exp_le_exp.2 hexp2
      exact le_trans hstep1 hstep2
    have hm1 : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast Nat.cast_pos.mp hmpos
    have h2m : (1:ℝ) + (m:ℝ) ≤ 2 * (m:ℝ) := by linarith only [hm1]
    have hstepA : c * (1 + (m:ℝ)) ^ p ≤ (m:ℝ) ^ (-((2000:ℝ) + p)) * (1 + (m:ℝ)) ^ p :=
      mul_le_mul_of_nonneg_right hcle (Real.rpow_nonneg (by linarith only [hmpos]) _)
    have hstepB : (1 + (m:ℝ)) ^ p ≤ (2 * (m:ℝ)) ^ p :=
      Real.rpow_le_rpow (by linarith only [hmpos]) h2m hp
    have hsplit : (2 * (m:ℝ)) ^ p = (2:ℝ) ^ p * (m:ℝ) ^ p :=
      Real.mul_rpow (by norm_num) (by linarith only [hmpos])
    have hpowmul : (m:ℝ) ^ (-((2000:ℝ) + p)) * (m:ℝ) ^ p = (m:ℝ) ^ (-(2000:ℝ)) := by
      rw [← Real.rpow_add hmpos]
      congr 1
      ring
    have hfinal : c * (1 + (m:ℝ)) ^ p ≤ (2:ℝ) ^ p * (m:ℝ) ^ (-(2000:ℝ)) := by
      calc c * (1 + (m:ℝ)) ^ p
          ≤ (m:ℝ) ^ (-((2000:ℝ) + p)) * (1 + (m:ℝ)) ^ p := hstepA
        _ ≤ (m:ℝ) ^ (-((2000:ℝ) + p)) * (2 * (m:ℝ)) ^ p :=
            mul_le_mul_of_nonneg_left hstepB (Real.rpow_nonneg (by linarith only [hmpos]) _)
        _ = (m:ℝ) ^ (-((2000:ℝ) + p)) * ((2:ℝ) ^ p * (m:ℝ) ^ p) := by rw [hsplit]
        _ = (2:ℝ) ^ p * ((m:ℝ) ^ (-((2000:ℝ) + p)) * (m:ℝ) ^ p) := by ring
        _ = (2:ℝ) ^ p * (m:ℝ) ^ (-(2000:ℝ)) := by rw [hpowmul]
    have hA0nn : (0:ℝ) ≤ A0 := by linarith only [hA01]
    have hstep_amp : c * (A0 * (1 + (m:ℝ)) ^ p) ≤ (A0 * (2:ℝ) ^ p) * (m:ℝ) ^ (-(2000:ℝ)) := by
      have hre : c * (A0 * (1 + (m:ℝ)) ^ p) = A0 * (c * (1 + (m:ℝ)) ^ p) := by ring
      rw [hre]
      calc A0 * (c * (1 + (m:ℝ)) ^ p)
          ≤ A0 * ((2:ℝ) ^ p * (m:ℝ) ^ (-(2000:ℝ))) := mul_le_mul_of_nonneg_left hfinal hA0nn
        _ = (A0 * (2:ℝ) ^ p) * (m:ℝ) ^ (-(2000:ℝ)) := by ring
    have hG1 : IsBigO P.toMeasure (gammaSigma q) (fun omega => c * R omega)
        (c * (A0 * (1 + (m:ℝ)) ^ p)) := hRO.const_mul hc0
    have hG13 : IsBigO P.toMeasure (gammaSigma (1/3)) (fun omega => c * R omega)
        (c * (A0 * (1 + (m:ℝ)) ^ p)) :=
      SuperdiffusionCLT.Section4.HomogBelow.homogBelow_isBigO_of_gammaSigma_le
        (sigma1 := q) (sigma2 := 1 / 3) hq hG1
    exact hG13.mono_scale hstep_amp
  · filter_upwards [hRae] with omega homega L _hL
    have hsq : 0 < s * 2 := by linarith only [hs0]
    have hf0 : ∀ l : ℕ, 0 ≤ srootE_term s (srootE_field nu omega L m n k)
        ((SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P) •
          (1 : Homogenization.Mat d)) n (l + thr) :=
      fun l => srootE_term_nonneg hs0.le _ _ n (l + thr)
    have hle : ∀ l : ℕ, srootE_term s (srootE_field nu omega L m n k)
        ((SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P) •
          (1 : Homogenization.Mat d)) n (l + thr) ≤
        Homogenization.geometricWeight s 2 (l + thr) * R omega := by
      intro l
      have hresp := homega L (l + thr)
      have hgw : 0 ≤ Homogenization.geometricWeight s 2 (l + thr) :=
        Homogenization.geometricWeight_nonneg (l + thr) (by linarith only [hsq])
      show Homogenization.geometricWeight s 2 (l + thr) *
          Real.rpow (Homogenization.scaleResponseAtScale (Homogenization.originCube d (n : ℤ))
              ((n : ℤ) - ((l + thr : ℕ) : ℤ)) Homogenization.MultiscaleExponent.infinity
              (srootE_field nu omega L m n k)
              ((SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P) •
                (1 : Homogenization.Mat d))) 2 ≤
          Homogenization.geometricWeight s 2 (l + thr) * R omega
      exact mul_le_mul_of_nonneg_left hresp hgw
    obtain ⟨_, hsum⟩ :=
      srootD_tsum_le_of_le_geometricWeight (f := fun l => srootE_term s
        (srootE_field nu omega L m n k)
        ((SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P) •
          (1 : Homogenization.Mat d)) n l) (q := 2) (R := R omega) hsq thr hf0 hle
    calc ∑' l : ℕ, srootE_term s (srootE_field nu omega L m n k)
          ((SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P) •
            (1 : Homogenization.Mat d)) n (l + thr)
        ≤ R omega * (3:ℝ) ^ (-(s * 2 * (thr : ℝ))) := hsum
      _ = c * R omega := by rw [hcdef]; ring

/-- **`hDeep`**, the deep-scale clause of `srootE_mathcalE_bounds_of_inputs`, with no hypothesis
beyond the standing shell laws bound inside it: the crude bound `srootD4_hCrudePolyHalf` feeds the
`Γ_q` combinator at `p = 10`, `q = 1/2`. -/
theorem srootD4_hDeep (d : ℕ) [NeZero d] :
    ∃ C0 : ℝ, 1 ≤ C0 ∧ ∃ A : ℝ, 1 ≤ A ∧ ∀ C1 : ℝ, A ≤ C1 →
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
              ∃ Y2 : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ,
                Measurable Y2 ∧
                IsBigO P.toMeasure (gammaSigma (1 / 3)) Y2 (A * (m : ℝ) ^ (-(2000 : ℝ))) ∧
                ∀ᵐ omega ∂P.toMeasure, ∀ L : ℕ, (m : ℝ) - C1 * s⁻¹ * ((⌈K * Real.log (m : ℝ)⌉₊ : ℕ) : ℝ) ≤ (L : ℝ) →
                  ∑' l : ℕ, srootE_term s (srootE_field nu omega L m n k)
                      ((SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P) • (1 : Homogenization.Mat d)) n
                      (l + (⌈C0 * s⁻¹ * Real.log (m : ℝ)⌉₊ + 1)) ≤ Y2 omega :=
  srootD4_hDeep_of_polyCrude_gamma d 10 (1 / 2) (by norm_num) (by norm_num)
    (srootD4_hCrudePolyHalf d)

end SuperdiffusionCLT.Section4.MinimalScales

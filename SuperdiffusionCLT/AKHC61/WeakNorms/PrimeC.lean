/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.AKHC61.WeakNorms.PrimeB

/-!
# Package C6, part 3: the expectations of the dominating pieces

The three random pieces of `akhcPrime_energy_le`'s dominating function, as functions of the
coefficient sample, are integrable under the cutoff law and have explicit expectations:

* `akhcPrime_avgDom` (node 16): `(Σ w_β)·Σ w_β 2θ E[fluct(cu_n)]`, by stationarity (B4);
* `akhcPrime_defSum`: `Σ_n w_n τ_{m,n}` (`CoarseGraining`'s additivity-defect identity);
* `akhcPrime_flSum`: `Σ_n w_n (E[fluct(cu_n)] + E[fluct(cu_m)])`, by stationarity (B4).
-/

@[expose] public section

namespace SuperdiffusionCLT.AKHC61.WeakNorms

open Homogenization MeasureTheory
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.AKHC61.Response

noncomputable section

/-- The fluctuation sum `Σ_n w_n flPair_n`. -/
noncomputable def akhcPrime_flSum {d : ℕ} [NeZero d] (nu : ℝ) (L : ℕ)
    (P : ProbabilityMeasure (ShellSeq d)) (s' : ℝ) (m k : ℕ) (a : RegCoeffField d) : ℝ :=
  ∑ n ∈ Finset.Icc ((k : ℤ) + 1) (m : ℤ), akhcPrime_w (1 / 2) s' (m : ℤ) n *
    akhcPrime_flPair nu L P m n a

/-- The mismatch sum splits as `defSum + (ε/2) G₀ S_w + (θ/ε) flSum`. -/
theorem akhcPrime_misSum_eq {d : ℕ} [NeZero d] (nu : ℝ) (L : ℕ)
    (P : ProbabilityMeasure (ShellSeq d)) (s' : ℝ) (m k : ℕ) (e : Vec d) (ε G0 : ℝ)
    (a : RegCoeffField d) :
    akhcPrime_misSum nu L P s' m k e ε G0 a =
      akhcPrime_defSum (1 / 2) s' (m : ℤ) (k : ℤ) (akhcSpecialPAtScale nu L P (m : ℤ) e)
          (akhcSpecialQAtScale nu L P (m : ℤ) e) a +
        ε / 2 * G0 * akhcPrime_wSum (1 / 2) s' (m : ℤ) (k : ℤ) +
        SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P m / ε *
          akhcPrime_flSum nu L P s' m k a := by
  unfold akhcPrime_misSum akhcPrime_defSum akhcPrime_wSum akhcPrime_flSum
  simp only [mul_add, Finset.sum_add_distrib]
  have h2 : ∑ n ∈ Finset.Icc ((k : ℤ) + 1) (m : ℤ), akhcPrime_w (1 / 2) s' (m : ℤ) n *
      (ε / 2 * G0) = ε / 2 * G0 * ∑ n ∈ Finset.Icc ((k : ℤ) + 1) (m : ℤ),
        akhcPrime_w (1 / 2) s' (m : ℤ) n := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring
  have h3 : ∑ n ∈ Finset.Icc ((k : ℤ) + 1) (m : ℤ), akhcPrime_w (1 / 2) s' (m : ℤ) n *
      (SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P m / ε *
        akhcPrime_flPair nu L P m n a) =
      SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P m / ε *
        ∑ n ∈ Finset.Icc ((k : ℤ) + 1) (m : ℤ),
          akhcPrime_w (1 / 2) s' (m : ℤ) n * akhcPrime_flPair nu L P m n a := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring
  rw [h2, h3]

variable {d : ℕ} [NeZero d] {nu : ℝ} (L : ℕ) {P : ProbabilityMeasure (ShellSeq d)}

/-- The top-scale fluctuation is its own descendant average at depth `0`. -/
theorem akhcPrime_integrable_descendantsAverage_fl (m : ℕ) (j : ℕ)
    (hIntFluct : ∀ R : TriadicCube d,
      Integrable (fun a => akhcFullBlockNormalizedFluctuationAtScale nu L P (m : ℤ) R a)
        (cutoffLaw (d := d) nu L P)) :
    Integrable (fun a => descendantsAverage (originCube d (m : ℤ)) j
        (fun R => akhcFullBlockNormalizedFluctuationAtScale nu L P (m : ℤ) R a))
      (cutoffLaw (d := d) nu L P) := by
  unfold descendantsAverage
  exact (integrable_finsetSum _ fun R _ => hIntFluct R).const_mul _

/-- **Expectation of the node-16 piece.** -/
theorem akhcPrime_integral_avgDom
    (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
    (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P)
    (hnu : 0 < nu) (β : ℝ) (m k : ℕ)
    (hIntFluct : ∀ R : TriadicCube d,
      Integrable (fun a => akhcFullBlockNormalizedFluctuationAtScale nu L P (m : ℤ) R a)
        (cutoffLaw (d := d) nu L P)) :
    Integrable (akhcPrime_avgDom nu L P β m k) (cutoffLaw (d := d) nu L P) ∧
    ∫ a, akhcPrime_avgDom nu L P β m k a ∂(cutoffLaw (d := d) nu L P) =
      (∑ n ∈ Finset.Icc ((k : ℤ) + 1) (m : ℤ),
          Real.rpow (3 : ℝ) (-β * (Int.toNat ((m : ℤ) - n) : ℝ))) *
        ∑ n ∈ Finset.Icc ((k : ℤ) + 1) (m : ℤ),
          Real.rpow (3 : ℝ) (-β * (Int.toNat ((m : ℤ) - n) : ℝ)) *
            (2 * SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P m) *
            ∫ a, akhcFullBlockNormalizedFluctuationAtScale nu L P (m : ℤ) (originCube d n) a
              ∂(cutoffLaw (d := d) nu L P) := by
  have hI : Integrable (fun a => ∑ n ∈ Finset.Icc ((k : ℤ) + 1) (m : ℤ),
      Real.rpow (3 : ℝ) (-β * (Int.toNat ((m : ℤ) - n) : ℝ)) *
        descendantsAverage (originCube d (m : ℤ)) (Int.toNat ((m : ℤ) - n))
          (fun R => 2 * SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P m *
            akhcFullBlockNormalizedFluctuationAtScale nu L P (m : ℤ) R a))
      (cutoffLaw (d := d) nu L P) := by
    refine integrable_finsetSum _ fun n _ => Integrable.const_mul ?_ _
    unfold descendantsAverage
    exact Integrable.const_mul
      (integrable_finsetSum _ fun R _ => (hIntFluct R).const_mul _) _
  refine ⟨hI.const_mul _, ?_⟩
  unfold akhcPrime_avgDom
  rw [integral_const_mul, akhc_integral_weighted_sum_descendantsAverage_fluct_eq hnu L hPrefix hJ2
    k m _ _ fun n _ R _ => hIntFluct R]

/-- **Expectation of the defect piece.** `E[Σ w_n defect_n] = Σ w_n τ_{m,n}`. -/
theorem akhcPrime_integral_defSum (hnu : 0 < nu)
    (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
    (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P)
    (s' : ℝ) (m k : ℕ) (p q : Vec d)
    (hJint : ∀ Q : TriadicCube d,
      Integrable (Book.Ch04.restrictionResponseJObservableCubeSet Q p q)
        (cutoffLaw (d := d) nu L P)) :
    Integrable (akhcPrime_defSum (1 / 2) s' (m : ℤ) (k : ℤ) p q) (cutoffLaw (d := d) nu L P) ∧
    ∫ a, akhcPrime_defSum (1 / 2) s' (m : ℤ) (k : ℤ) p q a ∂(cutoffLaw (d := d) nu L P) =
      ∑ n ∈ Finset.Icc ((k : ℤ) + 1) (m : ℤ), akhcPrime_w (1 / 2) s' (m : ℤ) n *
        Book.Ch05.tauAtScale (cutoffLaw (d := d) nu L P) (m : ℤ) n p q := by
  have hP := restrictionLawCarrier_cutoffLaw hnu L P
  have hstat := restrictionStationaryLaw_cutoffLaw hPrefix hJ2 nu L
  have hDI : ∀ n ∈ Finset.Icc ((k : ℤ) + 1) (m : ℤ),
      Integrable (Book.Ch05.Section53.WeakNormsMaximizer.responseDefectAverageAtScale (m : ℤ) n
        p q) (cutoffLaw (d := d) nu L P) := fun n hn =>
    Book.Ch05.Section53.JUpperBoundWeakNorms.integrable_responseJAdditivityDefectAtScale
      (Finset.mem_Icc.1 hn).2 p q (hJint _) fun R _ => hJint R
  have hI : Integrable (akhcPrime_defSum (1 / 2) s' (m : ℤ) (k : ℤ) p q)
      (cutoffLaw (d := d) nu L P) := by
    unfold akhcPrime_defSum
    exact integrable_finsetSum _ fun n hn => (hDI n hn).const_mul _
  refine ⟨hI, ?_⟩
  unfold akhcPrime_defSum
  rw [integral_finsetSum _ fun n hn => (hDI n hn).const_mul _]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [integral_const_mul]
  congr 1
  have hn0 : (0 : ℤ) ≤ n := by
    have h1 := (Finset.mem_Icc.1 hn).1
    have hk0 : (0 : ℤ) ≤ (k : ℤ) := Int.natCast_nonneg k
    linarith only [h1, hk0]
  exact Book.Ch05.Section53.JUpperBoundWeakNorms.integral_responseJAdditivityDefectAtScale_eq_tauAtScale
    hP hstat hn0 (Finset.mem_Icc.1 hn).2 p q (hJint _) fun R _ => hJint R

/-- **Expectation of the fluctuation piece.** -/
theorem akhcPrime_integral_flSum (hnu : 0 < nu)
    (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
    (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P)
    (s' : ℝ) (m k : ℕ)
    (hIntFluct : ∀ R : TriadicCube d,
      Integrable (fun a => akhcFullBlockNormalizedFluctuationAtScale nu L P (m : ℤ) R a)
        (cutoffLaw (d := d) nu L P)) :
    Integrable (akhcPrime_flSum nu L P s' m k) (cutoffLaw (d := d) nu L P) ∧
    ∫ a, akhcPrime_flSum nu L P s' m k a ∂(cutoffLaw (d := d) nu L P) =
      ∑ n ∈ Finset.Icc ((k : ℤ) + 1) (m : ℤ), akhcPrime_w (1 / 2) s' (m : ℤ) n *
        ((∫ a, akhcFullBlockNormalizedFluctuationAtScale nu L P (m : ℤ) (originCube d n) a
            ∂(cutoffLaw (d := d) nu L P)) +
          ∫ a, akhcFullBlockNormalizedFluctuationAtScale nu L P (m : ℤ)
            (originCube d (m : ℤ)) a ∂(cutoffLaw (d := d) nu L P)) := by
  have hPI : ∀ n : ℤ, Integrable (akhcPrime_flPair nu L P m n) (cutoffLaw (d := d) nu L P) :=
    fun n => (akhcPrime_integrable_descendantsAverage_fl L m _ hIntFluct).add (hIntFluct _)
  have hI : Integrable (akhcPrime_flSum nu L P s' m k) (cutoffLaw (d := d) nu L P) := by
    unfold akhcPrime_flSum
    exact integrable_finsetSum _ fun n _ => (hPI n).const_mul _
  refine ⟨hI, ?_⟩
  unfold akhcPrime_flSum
  rw [integral_finsetSum _ fun n _ => (hPI n).const_mul _]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [integral_const_mul]
  congr 1
  unfold akhcPrime_flPair
  rw [integral_add (akhcPrime_integrable_descendantsAverage_fl L m _ hIntFluct) (hIntFluct _)]
  congr 1
  have hn0 : (0 : ℤ) ≤ n := by
    have h1 := (Finset.mem_Icc.1 hn).1
    have hk0 : (0 : ℤ) ≤ (k : ℤ) := Int.natCast_nonneg k
    linarith only [h1, hk0]
  have h := akhc_integral_descendantsAverage_fluct_eq_two_mul_integral hnu L hPrefix hJ2
    (m : ℤ) n hn0 (Finset.mem_Icc.1 hn).2 (1 / 2 : ℝ) fun R _ => hIntFluct R
  have hone : ∀ x : ℝ, 2 * (1 / 2 : ℝ) * x = x := fun x => by ring
  simp only [hone] at h
  exact h

end

end SuperdiffusionCLT.AKHC61.WeakNorms

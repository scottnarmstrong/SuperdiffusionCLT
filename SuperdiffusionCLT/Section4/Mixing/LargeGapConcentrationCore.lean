/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.RHSTerm3InputsC
public import Homogenization.Probability.IndependentSums.GammaSigmaExpRegime.FiniteSums
public import Mathlib.Algebra.Order.Chebyshev

/-!
# A direct-regime (`Γ₁`) colour-partition concentration package

`p.mixing.P.three.prime#large-gap-case` needs, for the large scale-separation case, a concentration
bound on `avg_{z∈3^nℤ^d∩cu_m}(bfA_L(z+cu_n)-bfAhom_L(cu_n))` at the *direct*
`Γ₁` amplitude, uniformly in the two test vectors `p, q` (see
the second indicator clause, `X4`
chosen once, before `∀ omega p q`). `Section3.Terms.block_concentration`
(`Section3/Terms/RHSTerm3StepsD.lean`) proves the analogous bound at the *L²
(Rosenthal + Cauchy-Schwarz)* rate, which cannot supply an `O_{Γ₁}` tail. This
file proves the direct-`Γ₁` analogue with the same hypothesis package (same
colour-partition shape `D = J.biUnion part`, same range-of-dependence
independence, same cardinality bounds `hDcard`/`hJcard`), combining:

* `Homogenization.IndependentSums.isBigO_gammaOne_finset_sum_of_iIndepFun_of_isBigO_of_integral_eq_zero`
  (`GammaSigmaExpRegime/FiniteSums.lean`), the direct `Γ₁` sum concentration
  for one sublattice (independent, mean-zero, `O_{Γ1}(K)` summands); and
* `Homogenization.IndependentSums.isBigO_finset_sum_of_isBigO_gammaSigma`
  (`Triangle.lean`), the `Γ_σ` triangle (Minkowski) inequality across the
  colour classes, whose constant `gammaTriangleConst σ` does **not** grow with
  the number of classes — the reason a direct union bound over the classes
  would be unusable here (the class count is exponential in `ℓ - n`).

The final Cauchy-Schwarz step bounding `∑_j √|part j|` by `√(J.card·D.card)`
is the same one `Section3.Terms.block_concentration`'s proof uses (via
`sq_sum_le_card_mul_sum_sq`), and the closing cardinality-ratio computation
literally repeats `Section3.Terms.blockDeviation_concentration`'s `hratio`
step. -/

@[expose] public section

namespace SuperdiffusionCLT.Section4.Mixing

open Homogenization
open Homogenization.IndependentSums
open MeasureTheory ProbabilityTheory
open SuperdiffusionCLT.Section2.Cutoff (ShellSeq)

noncomputable section

variable {d : ℕ}

/-- **Direct-`Γ₁` colour-partition concentration for a lattice average.**
Mirrors `Section3.Terms.block_concentration`'s hypothesis package exactly
(`hUnion`, `hDisj`, `hYmeas`, `hYmean`, `hYtail`, `hIndep`, `hDcard`,
`hJcard`), but produces a direct `O_{Γ1}` amplitude on the average itself
instead of an `L²` bound. -/
theorem mixGap_blockConcentrationGamma1 {kappa : Type*}
    (P : ProbabilityMeasure (ShellSeq d))
    (D : Finset (TriadicCube d)) (J : Finset kappa)
    (part : kappa → Finset (TriadicCube d))
    (Y : ShellSeq d → TriadicCube d → ℝ) {K CJ : ℝ} {nn ell kk : ℕ}
    (hK : 0 < K) (hCJ : 0 ≤ CJ) (hDne : D.Nonempty)
    (hUnion : D = J.biUnion part)
    (hDisj : ∀ j ∈ J, ∀ j' ∈ J, j ≠ j' → Disjoint (part j) (part j'))
    (hYmeas : ∀ z, Measurable fun omega => Y omega z)
    (hYmean : ∀ z ∈ D, ∫ omega, Y omega z ∂P.toMeasure = 0)
    (hYtail : ∀ z ∈ D, IsBigO P.toMeasure (gammaSigma 1) (fun omega => Y omega z) K)
    (hIndep : ∀ j ∈ J, iIndepFun
      (fun z : {z // z ∈ part j} => fun omega : ShellSeq d => Y omega (z : TriadicCube d))
      P.toMeasure)
    (hnl : nn ≤ ell) (hlk : ell ≤ kk)
    (hDcard : (D.card : ℝ) = (3 : ℝ) ^ ((d : ℝ) * ((kk - nn : ℕ) : ℝ)))
    (hJcard : (J.card : ℝ) ≤ CJ * (3 : ℝ) ^ ((d : ℝ) * ((ell - nn : ℕ) : ℝ))) :
    IsBigO P.toMeasure (gammaSigma 1)
      (fun omega => ((D.card : ℝ))⁻¹ * ∑ z ∈ D, Y omega z)
      (2 * gammaTriangleConst 1 * gammaOneExpRegimeConst * Real.sqrt CJ * K *
        (3 : ℝ) ^ (-((d : ℝ) * ((kk - ell : ℕ) : ℝ)) / 2)) := by
  classical
  have hNpos : (0 : ℝ) < (D.card : ℝ) := by exact_mod_cast Finset.card_pos.2 hDne
  set J0 : Finset kappa := J.filter (fun j => (part j).Nonempty) with hJ0
  have hsub0 : J0 ⊆ J := Finset.filter_subset _ _
  have hpartsub : ∀ j ∈ J, part j ⊆ D := by
    intro j hj z hz
    rw [hUnion]
    exact Finset.mem_biUnion.2 ⟨j, hj, hz⟩
  have hUnion0 : D = J0.biUnion part := by
    apply Finset.Subset.antisymm
    · intro z hz
      rw [hUnion] at hz
      obtain ⟨j, hj, hzj⟩ := Finset.mem_biUnion.1 hz
      exact Finset.mem_biUnion.2 ⟨j, Finset.mem_filter.2 ⟨hj, ⟨z, hzj⟩⟩, hzj⟩
    · intro z hz
      obtain ⟨j, hj, hzj⟩ := Finset.mem_biUnion.1 hz
      rw [hUnion]
      exact Finset.mem_biUnion.2 ⟨j, hsub0 hj, hzj⟩
  have hDisj0 : ∀ j ∈ J0, ∀ j' ∈ J0, j ≠ j' → Disjoint (part j) (part j') :=
    fun j hj j' hj' hne => hDisj j (hsub0 hj) j' (hsub0 hj') hne
  have hJ0ne : J0.Nonempty := by
    rcases Finset.eq_empty_or_nonempty J0 with hemp | hne
    · exfalso
      rw [hemp] at hUnion0
      simp only [Finset.biUnion_empty] at hUnion0
      exact hDne.ne_empty hUnion0
    · exact hne
  -- Step 1: the per-sublattice sum concentration.
  set sumY : kappa → ShellSeq d → ℝ := fun j omega => ∑ z ∈ part j, Y omega z with hsumY
  set a : kappa → ℝ := fun j => 2 * gammaOneExpRegimeConst * Real.sqrt ((part j).card : ℝ) * K
    with ha
  have haPos : ∀ j ∈ J0, 0 < a j := by
    intro j hj
    have hne : (part j).Nonempty := (Finset.mem_filter.1 hj).2
    have hcardpos : (0 : ℝ) < ((part j).card : ℝ) := by exact_mod_cast Finset.card_pos.2 hne
    have hsqrtpos : (0 : ℝ) < Real.sqrt ((part j).card : ℝ) := Real.sqrt_pos.2 hcardpos
    have h2pos : (0 : ℝ) < 2 * gammaOneExpRegimeConst := by
      have := gammaOneExpRegimeConst_pos
      linarith only [this]
    rw [ha]
    positivity
  have hsumYbig : ∀ j ∈ J0, IsBigO P.toMeasure (gammaSigma 1) (sumY j) (a j) := by
    intro j hj
    have hne : (part j).Nonempty := (Finset.mem_filter.1 hj).2
    obtain ⟨z0, hz0⟩ := hne
    have : Nonempty {z // z ∈ part j} := ⟨⟨z0, hz0⟩⟩
    have hs : (Finset.univ : Finset {z // z ∈ part j}).Nonempty := Finset.univ_nonempty
    have hjJ : j ∈ J := hsub0 hj
    have hres := isBigO_gammaOne_finset_sum_of_iIndepFun_of_isBigO_of_integral_eq_zero
      (μ := P.toMeasure)
      (X := fun (z : {z // z ∈ part j}) (omega : ShellSeq d) => Y omega (z : TriadicCube d))
      (s := Finset.univ) (K := K) (hIndep j hjJ) (fun z => hYmeas _) hs hK
      (fun z _ => hYtail _ (hpartsub j hjJ z.2))
      (fun z _ => hYmean _ (hpartsub j hjJ z.2))
    have hcard : ((Finset.univ : Finset {z // z ∈ part j}).card : ℝ) = ((part j).card : ℝ) := by
      rw [Finset.card_univ, Fintype.card_coe]
    have hsumcoe : (fun omega : ShellSeq d =>
        ∑ i ∈ (Finset.univ : Finset {z // z ∈ part j}), Y omega (i : TriadicCube d)) = sumY j :=
      funext fun omega => Finset.sum_coe_sort (part j) (fun z => Y omega z)
    rw [hcard, hsumcoe] at hres
    rw [ha]
    exact hres
  have hsumYmeas : ∀ j ∈ J0, Measurable (sumY j) := by
    intro j _
    exact Finset.measurable_sum _ fun z _ => hYmeas z
  -- Step 2: the Minkowski triangle inequality across the colour classes.
  have htriangle := isBigO_finset_sum_of_isBigO_gammaSigma (μ := P.toMeasure)
    J0 (X := sumY) (a := a) (σ := 1)
    (by norm_num) hJ0ne haPos hsumYbig hsumYmeas
  -- rewrite the sum of sublattice sums as the sum over `D`.
  have hsplit : (fun omega : ShellSeq d => ∑ j ∈ J0, sumY j omega) =
      fun omega : ShellSeq d => ∑ z ∈ D, Y omega z := by
    funext omega
    rw [hsumY]
    dsimp only
    rw [hUnion0]
    exact (Finset.sum_biUnion hDisj0).symm
  rw [hsplit] at htriangle
  -- Step 3: bound the sum of amplitudes by Cauchy-Schwarz on the real numbers `√(part j).card`.
  set f : kappa → ℝ := fun j => Real.sqrt ((part j).card : ℝ) with hf
  have hcardsum : ∑ j ∈ J0, ((part j).card : ℝ) = (D.card : ℝ) := by
    rw [hUnion0, Finset.card_biUnion hDisj0]
    push_cast
    rfl
  have hCS : (∑ j ∈ J0, f j) ^ 2 ≤ (J0.card : ℝ) * ∑ j ∈ J0, f j ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  have hfsq : ∀ j ∈ J0, f j ^ 2 = ((part j).card : ℝ) := by
    intro j _
    rw [hf]
    exact Real.sq_sqrt (by positivity)
  have hCS' : (∑ j ∈ J0, f j) ^ 2 ≤ (J0.card : ℝ) * (D.card : ℝ) := by
    rw [Finset.sum_congr rfl hfsq, hcardsum] at hCS
    exact hCS
  have hfnonneg : (0 : ℝ) ≤ ∑ j ∈ J0, f j := Finset.sum_nonneg fun j _ => Real.sqrt_nonneg _
  have hJ0D_nonneg : (0 : ℝ) ≤ (J0.card : ℝ) * (D.card : ℝ) := by positivity
  have hCSsqrt : ∑ j ∈ J0, f j ≤ Real.sqrt ((J0.card : ℝ) * (D.card : ℝ)) :=
    (Real.le_sqrt hfnonneg hJ0D_nonneg).2 hCS'
  have hJ0J : (J0.card : ℝ) ≤ (J.card : ℝ) := by exact_mod_cast Finset.card_le_card hsub0
  have hCSsqrt' : ∑ j ∈ J0, f j ≤ Real.sqrt ((J.card : ℝ) * (D.card : ℝ)) := by
    refine hCSsqrt.trans (Real.sqrt_le_sqrt ?_)
    exact mul_le_mul_of_nonneg_right hJ0J hNpos.le
  -- Step 4: the cardinality-ratio computation, as in `blockDeviation_concentration`.
  have hsqrt3pow : Real.sqrt ((3 : ℝ) ^ (-((d : ℝ) * ((kk - ell : ℕ) : ℝ)))) =
      (3 : ℝ) ^ (-((d : ℝ) * ((kk - ell : ℕ) : ℝ)) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    congr 1
    ring
  have hratio : Real.sqrt ((J.card : ℝ) * (D.card : ℝ)) / (D.card : ℝ) ≤
      Real.sqrt CJ * (3 : ℝ) ^ (-((d : ℝ) * ((kk - ell : ℕ) : ℝ)) / 2) := by
    have hJDbound : (J.card : ℝ) * (D.card : ℝ) ≤
        (CJ * (3 : ℝ) ^ (-((d : ℝ) * ((kk - ell : ℕ) : ℝ)))) * (D.card : ℝ) ^ 2 := by
      have hJle : (J.card : ℝ) ≤ CJ * (3 : ℝ) ^ (-((d : ℝ) * ((kk - ell : ℕ) : ℝ))) *
          (D.card : ℝ) := by
        have hDval : (D.card : ℝ) = (3 : ℝ) ^ ((d : ℝ) * ((kk - nn : ℕ) : ℝ)) := hDcard
        have hexp : -((d : ℝ) * ((kk - ell : ℕ) : ℝ)) + (d : ℝ) * ((kk - nn : ℕ) : ℝ) =
            (d : ℝ) * ((ell - nn : ℕ) : ℝ) := by
          rw [Nat.cast_sub hnl, Nat.cast_sub (hnl.trans hlk), Nat.cast_sub hlk]
          ring
        calc (J.card : ℝ) ≤ CJ * (3 : ℝ) ^ ((d : ℝ) * ((ell - nn : ℕ) : ℝ)) := hJcard
          _ = CJ * (3 : ℝ) ^ (-((d : ℝ) * ((kk - ell : ℕ) : ℝ)) +
                (d : ℝ) * ((kk - nn : ℕ) : ℝ)) := by rw [hexp]
          _ = CJ * (3 : ℝ) ^ (-((d : ℝ) * ((kk - ell : ℕ) : ℝ))) * (D.card : ℝ) := by
              rw [Real.rpow_add (by norm_num : (0 : ℝ) < 3), hDval]
              ring
      calc (J.card : ℝ) * (D.card : ℝ)
          ≤ (CJ * (3 : ℝ) ^ (-((d : ℝ) * ((kk - ell : ℕ) : ℝ))) * (D.card : ℝ)) *
              (D.card : ℝ) := mul_le_mul_of_nonneg_right hJle hNpos.le
        _ = (CJ * (3 : ℝ) ^ (-((d : ℝ) * ((kk - ell : ℕ) : ℝ)))) * (D.card : ℝ) ^ 2 := by ring
    have hsqrtle : Real.sqrt ((J.card : ℝ) * (D.card : ℝ)) ≤
        Real.sqrt ((CJ * (3 : ℝ) ^ (-((d : ℝ) * ((kk - ell : ℕ) : ℝ)))) * (D.card : ℝ) ^ 2) :=
      Real.sqrt_le_sqrt hJDbound
    have hrw : Real.sqrt ((CJ * (3 : ℝ) ^ (-((d : ℝ) * ((kk - ell : ℕ) : ℝ)))) *
        (D.card : ℝ) ^ 2) =
        Real.sqrt (CJ * (3 : ℝ) ^ (-((d : ℝ) * ((kk - ell : ℕ) : ℝ)))) * (D.card : ℝ) := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hNpos.le]
    rw [hrw] at hsqrtle
    have hdiv : Real.sqrt ((J.card : ℝ) * (D.card : ℝ)) / (D.card : ℝ) ≤
        Real.sqrt (CJ * (3 : ℝ) ^ (-((d : ℝ) * ((kk - ell : ℕ) : ℝ)))) := by
      rw [div_le_iff₀ hNpos]
      exact hsqrtle
    refine hdiv.trans (le_of_eq ?_)
    rw [Real.sqrt_mul hCJ, hsqrt3pow]
  -- Assemble.
  have hamp_nonneg : (0 : ℝ) ≤ gammaTriangleConst 1 * ∑ j ∈ J0, a j := by
    have h1 : (0 : ℝ) ≤ gammaTriangleConst 1 := gammaTriangleConst_pos.le
    have h2 : (0 : ℝ) ≤ ∑ j ∈ J0, a j := Finset.sum_nonneg fun j hj => (haPos j hj).le
    positivity
  refine (IsBigO.const_mul (c := (D.card : ℝ)⁻¹) (by positivity) htriangle).mono_scale ?_
  have hstep : ∑ j ∈ J0, a j = 2 * gammaOneExpRegimeConst * K * ∑ j ∈ J0, f j := by
    rw [ha, hf]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hfinal : ((D.card : ℝ))⁻¹ * (gammaTriangleConst 1 * ∑ j ∈ J0, a j) ≤
      2 * gammaTriangleConst 1 * gammaOneExpRegimeConst * Real.sqrt CJ * K *
        (3 : ℝ) ^ (-((d : ℝ) * ((kk - ell : ℕ) : ℝ)) / 2) := by
    rw [hstep]
    have hle : ∑ j ∈ J0, f j ≤ Real.sqrt ((J.card : ℝ) * (D.card : ℝ)) := hCSsqrt'
    have hK2nonneg : (0 : ℝ) ≤ 2 * gammaOneExpRegimeConst * K := by
      have := gammaOneExpRegimeConst_pos
      have hKle := hK.le
      positivity
    have hstep2 : ((D.card : ℝ))⁻¹ * (gammaTriangleConst 1 *
        (2 * gammaOneExpRegimeConst * K * ∑ j ∈ J0, f j)) =
        gammaTriangleConst 1 * (2 * gammaOneExpRegimeConst * K) *
          (Real.sqrt ((J.card : ℝ) * (D.card : ℝ)) / (D.card : ℝ) -
            (Real.sqrt ((J.card : ℝ) * (D.card : ℝ)) - ∑ j ∈ J0, f j) / (D.card : ℝ)) := by
      field_simp
      ring
    rw [hstep2]
    have hgap_nonneg : (0 : ℝ) ≤
        (Real.sqrt ((J.card : ℝ) * (D.card : ℝ)) - ∑ j ∈ J0, f j) / (D.card : ℝ) := by
      have : (0 : ℝ) ≤ Real.sqrt ((J.card : ℝ) * (D.card : ℝ)) - ∑ j ∈ J0, f j := by
        linarith only [hle]
      positivity
    have hcoef_nonneg : (0 : ℝ) ≤ gammaTriangleConst 1 * (2 * gammaOneExpRegimeConst * K) := by
      have h1 : (0 : ℝ) ≤ gammaTriangleConst 1 := gammaTriangleConst_pos.le
      positivity
    have hchain : gammaTriangleConst 1 * (2 * gammaOneExpRegimeConst * K) *
        (Real.sqrt ((J.card : ℝ) * (D.card : ℝ)) / (D.card : ℝ) -
          (Real.sqrt ((J.card : ℝ) * (D.card : ℝ)) - ∑ j ∈ J0, f j) / (D.card : ℝ)) ≤
        gammaTriangleConst 1 * (2 * gammaOneExpRegimeConst * K) *
          (Real.sqrt ((J.card : ℝ) * (D.card : ℝ)) / (D.card : ℝ)) := by
      have := mul_le_mul_of_nonneg_left
        (sub_le_self (Real.sqrt ((J.card : ℝ) * (D.card : ℝ)) / (D.card : ℝ)) hgap_nonneg)
        hcoef_nonneg
      exact this
    refine hchain.trans ?_
    have hratio' := hratio
    calc gammaTriangleConst 1 * (2 * gammaOneExpRegimeConst * K) *
        (Real.sqrt ((J.card : ℝ) * (D.card : ℝ)) / (D.card : ℝ))
        ≤ gammaTriangleConst 1 * (2 * gammaOneExpRegimeConst * K) *
            (Real.sqrt CJ * (3 : ℝ) ^ (-((d : ℝ) * ((kk - ell : ℕ) : ℝ)) / 2)) :=
          mul_le_mul_of_nonneg_left hratio' hcoef_nonneg
      _ = 2 * gammaTriangleConst 1 * gammaOneExpRegimeConst * Real.sqrt CJ * K *
          (3 : ℝ) ^ (-((d : ℝ) * ((kk - ell : ℕ) : ℝ)) / 2) := by ring
  exact hfinal

end

end SuperdiffusionCLT.Section4.Mixing

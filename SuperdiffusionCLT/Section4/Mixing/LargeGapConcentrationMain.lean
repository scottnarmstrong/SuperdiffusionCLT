/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section4.Mixing.LargeGapConcentrationQuadratic
public import SuperdiffusionCLT.Section4.Mixing.DecomposeInstance

/-!
# The deterministic quadratic-form bound

Proves the pointwise (deterministic, no probability) bound

`2 · avg_z (p·(bfA_L(z+cu_n) - bfAhom_L(cu_n))q) ≤ E(ω) · (p·Ahom p + q·Ahom q)`

with `E := mixGap_entrySumEnvelope`, via the elementary fact `2abc ≤ |c|(a²+b²)`
applied entrywise to the four blocks, which is the deterministic step of
`p.mixing.P.three.prime#large-gap-case`. -/

@[expose] public section

namespace SuperdiffusionCLT.Section4.Mixing

open Homogenization
open Homogenization.IndependentSums
open MeasureTheory ProbabilityTheory
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Cutoff

noncomputable section

variable {d : ℕ}

/-! ## Finite-sum algebra: the bilinear form as an entrywise sum -/

/-- The general two-vector entrywise expansion `p·(Mq) = ∑_i∑_j p_i M(i,j) q_j`. -/
theorem mixGap_vecDot_matVecMul_eq_sum (M : Mat d) (p q : Vec d) :
    vecDot p (matVecMul M q) = ∑ i, ∑ j, p i * (M i j * q j) := by
  rw [vecDot]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [matVecMul, Finset.mul_sum]

/-- Averaging over `z` commutes with a finite double sum over `(i, j)`. -/
theorem mixGap_avg_sum_comm {s : Finset (TriadicCube d)} (f : TriadicCube d → Fin d → Fin d → ℝ) :
    ((s.card : ℝ))⁻¹ * ∑ z ∈ s, ∑ i : Fin d, ∑ j : Fin d, f z i j =
      ∑ i : Fin d, ∑ j : Fin d, ((s.card : ℝ))⁻¹ * ∑ z ∈ s, f z i j := by
  have hswap : (∑ z ∈ s, ∑ i : Fin d, ∑ j : Fin d, f z i j) =
      ∑ i : Fin d, ∑ j : Fin d, ∑ z ∈ s, f z i j := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact Finset.sum_comm
  rw [hswap, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]

/-- **The average of the bilinear block-matrix difference, as a weighted
entrywise sum of the four blocks' averaged entry deviations.** -/
theorem mixGap_avg_blockVecDot_eq [NeZero d] {nu : ℝ}
    {P : ProbabilityMeasure (ShellSeq d)} (L nn m : ℕ) (omega : ShellSeq d) (p q : BlockVec d) :
    ((descendantsAtDepth (originCube d (m : ℤ)) (m - nn)).card : ℝ)⁻¹ *
        ∑ R ∈ descendantsAtDepth (originCube d (m : ℤ)) (m - nn),
          blockVecDot p (blockMatVecMul
            (ofFullBlockMat (toFullBlockMat
                  (coarseBlockMatrix (cubeSet R) (coefficientCutoff nu omega L).toCoeffField) -
                toFullBlockMat (annealedBlockMatrix nu L P (cubeSet (originCube d (nn : ℤ))))))
            q) =
      (∑ i : Fin d, ∑ j : Fin d, p.1 i *
          (mixGap_avgEntryDeviation nu L P nn m (Sum.inl i) (Sum.inl j) omega * q.1 j)) +
        (∑ i : Fin d, ∑ j : Fin d, p.1 i *
            (mixGap_avgEntryDeviation nu L P nn m (Sum.inl i) (Sum.inr j) omega * q.2 j)) +
        (∑ i : Fin d, ∑ j : Fin d, p.2 i *
            (mixGap_avgEntryDeviation nu L P nn m (Sum.inr i) (Sum.inl j) omega * q.1 j)) +
        (∑ i : Fin d, ∑ j : Fin d, p.2 i *
            (mixGap_avgEntryDeviation nu L P nn m (Sum.inr i) (Sum.inr j) omega * q.2 j)) := by
  set D : Finset (TriadicCube d) := descendantsAtDepth (originCube d (m : ℤ)) (m - nn) with hD
  set A : TriadicCube d → BlockMat d :=
    fun z => coarseBlockMatrix (cubeSet z) (coefficientCutoff nu omega L).toCoeffField with hA
  set B : BlockMat d := annealedBlockMatrix nu L P (cubeSet (originCube d (nn : ℤ))) with hB
  have hblk : ∀ z ∈ D, blockVecDot p (blockMatVecMul (ofFullBlockMat (toFullBlockMat (A z) - toFullBlockMat B)) q) =
      (vecDot p.1 (matVecMul (A z).upperLeft q.1) - vecDot p.1 (matVecMul B.upperLeft q.1)) +
        (vecDot p.1 (matVecMul (A z).upperRight q.2) - vecDot p.1 (matVecMul B.upperRight q.2)) +
        (vecDot p.2 (matVecMul (A z).lowerLeft q.1) - vecDot p.2 (matVecMul B.lowerLeft q.1)) +
        (vecDot p.2 (matVecMul (A z).lowerRight q.2) - vecDot p.2 (matVecMul B.lowerRight q.2)) := by
    intro z _
    rw [mixTerms_blockVecDot_ofFullBlockMat_sub_bilinear]
    obtain ⟨p1, p2⟩ := p
    obtain ⟨q1, q2⟩ := q
    show (vecDot p1 (matVecMul (A z).upperLeft q1 + matVecMul (A z).upperRight q2) +
        vecDot p2 (matVecMul (A z).lowerLeft q1 + matVecMul (A z).lowerRight q2)) -
      (vecDot p1 (matVecMul B.upperLeft q1 + matVecMul B.upperRight q2) +
        vecDot p2 (matVecMul B.lowerLeft q1 + matVecMul B.lowerRight q2)) = _
    simp only [vecDot_add_right]
    ring
  rw [Finset.sum_congr rfl hblk]
  have hsplit : (∑ z ∈ D,
      ((vecDot p.1 (matVecMul (A z).upperLeft q.1) - vecDot p.1 (matVecMul B.upperLeft q.1)) +
          (vecDot p.1 (matVecMul (A z).upperRight q.2) - vecDot p.1 (matVecMul B.upperRight q.2)) +
          (vecDot p.2 (matVecMul (A z).lowerLeft q.1) - vecDot p.2 (matVecMul B.lowerLeft q.1)) +
          (vecDot p.2 (matVecMul (A z).lowerRight q.2) - vecDot p.2 (matVecMul B.lowerRight q.2)))) =
      (∑ z ∈ D, (vecDot p.1 (matVecMul (A z).upperLeft q.1) - vecDot p.1 (matVecMul B.upperLeft q.1))) +
        (∑ z ∈ D, (vecDot p.1 (matVecMul (A z).upperRight q.2) - vecDot p.1 (matVecMul B.upperRight q.2))) +
        (∑ z ∈ D, (vecDot p.2 (matVecMul (A z).lowerLeft q.1) - vecDot p.2 (matVecMul B.lowerLeft q.1))) +
        (∑ z ∈ D, (vecDot p.2 (matVecMul (A z).lowerRight q.2) - vecDot p.2 (matVecMul B.lowerRight q.2))) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  rw [hsplit, mul_add, mul_add, mul_add]
  have hentryUL : ∀ z ∈ D,
      vecDot p.1 (matVecMul (A z).upperLeft q.1) - vecDot p.1 (matVecMul B.upperLeft q.1) =
        ∑ i : Fin d, ∑ j : Fin d, p.1 i * ((blockMatEntry (A z) (Sum.inl i) (Sum.inl j) -
          blockMatEntry B (Sum.inl i) (Sum.inl j)) * q.1 j) := by
    intro z _
    rw [mixGap_vecDot_matVecMul_eq_sum (A z).upperLeft p.1 q.1,
      mixGap_vecDot_matVecMul_eq_sum B.upperLeft p.1 q.1, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    show p.1 i * ((A z).upperLeft i j * q.1 j) - p.1 i * (B.upperLeft i j * q.1 j) =
      p.1 i * (((A z).upperLeft i j - B.upperLeft i j) * q.1 j)
    ring
  have hentryUR : ∀ z ∈ D,
      vecDot p.1 (matVecMul (A z).upperRight q.2) - vecDot p.1 (matVecMul B.upperRight q.2) =
        ∑ i : Fin d, ∑ j : Fin d, p.1 i * ((blockMatEntry (A z) (Sum.inl i) (Sum.inr j) -
          blockMatEntry B (Sum.inl i) (Sum.inr j)) * q.2 j) := by
    intro z _
    rw [mixGap_vecDot_matVecMul_eq_sum (A z).upperRight p.1 q.2,
      mixGap_vecDot_matVecMul_eq_sum B.upperRight p.1 q.2, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    show p.1 i * ((A z).upperRight i j * q.2 j) - p.1 i * (B.upperRight i j * q.2 j) =
      p.1 i * (((A z).upperRight i j - B.upperRight i j) * q.2 j)
    ring
  have hentryLL : ∀ z ∈ D,
      vecDot p.2 (matVecMul (A z).lowerLeft q.1) - vecDot p.2 (matVecMul B.lowerLeft q.1) =
        ∑ i : Fin d, ∑ j : Fin d, p.2 i * ((blockMatEntry (A z) (Sum.inr i) (Sum.inl j) -
          blockMatEntry B (Sum.inr i) (Sum.inl j)) * q.1 j) := by
    intro z _
    rw [mixGap_vecDot_matVecMul_eq_sum (A z).lowerLeft p.2 q.1,
      mixGap_vecDot_matVecMul_eq_sum B.lowerLeft p.2 q.1, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    show p.2 i * ((A z).lowerLeft i j * q.1 j) - p.2 i * (B.lowerLeft i j * q.1 j) =
      p.2 i * (((A z).lowerLeft i j - B.lowerLeft i j) * q.1 j)
    ring
  have hentryLR : ∀ z ∈ D,
      vecDot p.2 (matVecMul (A z).lowerRight q.2) - vecDot p.2 (matVecMul B.lowerRight q.2) =
        ∑ i : Fin d, ∑ j : Fin d, p.2 i * ((blockMatEntry (A z) (Sum.inr i) (Sum.inr j) -
          blockMatEntry B (Sum.inr i) (Sum.inr j)) * q.2 j) := by
    intro z _
    rw [mixGap_vecDot_matVecMul_eq_sum (A z).lowerRight p.2 q.2,
      mixGap_vecDot_matVecMul_eq_sum B.lowerRight p.2 q.2, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    show p.2 i * ((A z).lowerRight i j * q.2 j) - p.2 i * (B.lowerRight i j * q.2 j) =
      p.2 i * (((A z).lowerRight i j - B.lowerRight i j) * q.2 j)
    ring
  rw [Finset.sum_congr rfl hentryUL, Finset.sum_congr rfl hentryUR,
    Finset.sum_congr rfl hentryLL, Finset.sum_congr rfl hentryLR]
  have hcomm1 := mixGap_avg_sum_comm (s := D)
    (fun z i j => p.1 i * ((blockMatEntry (A z) (Sum.inl i) (Sum.inl j) -
      blockMatEntry B (Sum.inl i) (Sum.inl j)) * q.1 j))
  have hcomm2 := mixGap_avg_sum_comm (s := D)
    (fun z i j => p.1 i * ((blockMatEntry (A z) (Sum.inl i) (Sum.inr j) -
      blockMatEntry B (Sum.inl i) (Sum.inr j)) * q.2 j))
  have hcomm3 := mixGap_avg_sum_comm (s := D)
    (fun z i j => p.2 i * ((blockMatEntry (A z) (Sum.inr i) (Sum.inl j) -
      blockMatEntry B (Sum.inr i) (Sum.inl j)) * q.1 j))
  have hcomm4 := mixGap_avg_sum_comm (s := D)
    (fun z i j => p.2 i * ((blockMatEntry (A z) (Sum.inr i) (Sum.inr j) -
      blockMatEntry B (Sum.inr i) (Sum.inr j)) * q.2 j))
  rw [hcomm1, hcomm2, hcomm3, hcomm4]
  have hfinal : ∀ (alpha beta : BlockCoord d) (pc qc : ℝ),
      ((D.card : ℝ))⁻¹ * ∑ z ∈ D, pc * ((blockMatEntry (A z) alpha beta - blockMatEntry B alpha beta) * qc) =
        pc * (mixGap_avgEntryDeviation nu L P nn m alpha beta omega * qc) := by
    intro alpha beta pc qc
    have hdef : mixGap_avgEntryDeviation nu L P nn m alpha beta omega =
        ((D.card : ℝ))⁻¹ * ∑ z ∈ D, (blockMatEntry (A z) alpha beta - blockMatEntry B alpha beta) := rfl
    rw [hdef]
    have hcongr : (∑ z ∈ D, pc * ((blockMatEntry (A z) alpha beta - blockMatEntry B alpha beta) * qc)) =
        pc * qc * ∑ z ∈ D, (blockMatEntry (A z) alpha beta - blockMatEntry B alpha beta) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun z _ => ?_
      ring
    rw [hcongr]
    ring
  congr 1
  congr 1
  congr 1
  · exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hfinal _ _ (p.1 i) (q.1 j)
  · exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hfinal _ _ (p.1 i) (q.2 j)
  · exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hfinal _ _ (p.2 i) (q.1 j)
  · exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hfinal _ _ (p.2 i) (q.2 j)

/-! ## The elementary AM-GM step -/

/-- `2abc ≤ |c|(a²+b²)`, for all reals. -/
theorem mixGap_two_mul_le_abs_mul_add_sq (a b c : ℝ) : 2 * (a * (c * b)) ≤ |c| * (a ^ 2 + b ^ 2) := by
  rcases le_or_gt 0 c with hc | hc
  · rw [abs_of_nonneg hc]
    nlinarith only [sq_nonneg (a - b), hc]
  · rw [abs_of_neg hc]
    nlinarith only [sq_nonneg (a + b), hc]

/-- **The one-block AM-GM sum bound**: `2∑ᵢⱼ aᵢ(f(i,j)bⱼ) ≤ (∑ᵢⱼ|f(i,j)|)(∑ᵢaᵢ² + ∑ⱼbⱼ²)`. -/
theorem mixGap_blockAMGM_le (f : Fin d → Fin d → ℝ) (a b : Fin d → ℝ) :
    2 * ∑ i : Fin d, ∑ j : Fin d, a i * (f i j * b j) ≤
      (∑ i : Fin d, ∑ j : Fin d, |f i j|) * ((∑ i : Fin d, (a i) ^ 2) + ∑ j : Fin d, (b j) ^ 2) := by
  set S : ℝ := ∑ i : Fin d, ∑ j : Fin d, |f i j| with hS
  have hrow : ∀ i : Fin d, (∑ j : Fin d, |f i j|) ≤ S := by
    intro i
    rw [hS]
    exact Finset.single_le_sum (f := fun i' : Fin d => ∑ j : Fin d, |f i' j|)
      (fun i' _ => Finset.sum_nonneg fun j _ => abs_nonneg _) (Finset.mem_univ i)
  have hcol : ∀ j : Fin d, (∑ i : Fin d, |f i j|) ≤ S := by
    intro j
    rw [hS, Finset.sum_comm]
    exact Finset.single_le_sum (f := fun j' : Fin d => ∑ i : Fin d, |f i j'|)
      (fun j' _ => Finset.sum_nonneg fun i _ => abs_nonneg _) (Finset.mem_univ j)
  have hpt : ∀ i : Fin d, ∀ j : Fin d, 2 * (a i * (f i j * b j)) ≤ |f i j| * ((a i) ^ 2 + (b j) ^ 2) :=
    fun i j => mixGap_two_mul_le_abs_mul_add_sq (a i) (b j) (f i j)
  have hsum1 : 2 * ∑ i : Fin d, ∑ j : Fin d, a i * (f i j * b j) ≤
      ∑ i : Fin d, ∑ j : Fin d, |f i j| * ((a i) ^ 2 + (b j) ^ 2) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun j _ => hpt i j
  have hexpand : (∑ i : Fin d, ∑ j : Fin d, |f i j| * ((a i) ^ 2 + (b j) ^ 2)) =
      (∑ i : Fin d, (a i) ^ 2 * (∑ j : Fin d, |f i j|)) +
        ∑ j : Fin d, (b j) ^ 2 * (∑ i : Fin d, |f i j|) := by
    have step1 : ∀ i : Fin d, (∑ j : Fin d, |f i j| * ((a i) ^ 2 + (b j) ^ 2)) =
        (a i) ^ 2 * (∑ j : Fin d, |f i j|) + ∑ j : Fin d, |f i j| * (b j) ^ 2 := by
      intro i
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => step1 i), Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hbound : (∑ i : Fin d, (a i) ^ 2 * (∑ j : Fin d, |f i j|)) +
      ∑ j : Fin d, (b j) ^ 2 * (∑ i : Fin d, |f i j|) ≤
      (∑ i : Fin d, (a i) ^ 2) * S + (∑ j : Fin d, (b j) ^ 2) * S := by
    refine add_le_add ?_ ?_
    · rw [Finset.sum_mul]
      exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hrow i) (sq_nonneg _)
    · rw [Finset.sum_mul]
      exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hcol j) (sq_nonneg _)
  calc 2 * ∑ i : Fin d, ∑ j : Fin d, a i * (f i j * b j)
      ≤ ∑ i : Fin d, ∑ j : Fin d, |f i j| * ((a i) ^ 2 + (b j) ^ 2) := hsum1
    _ = (∑ i : Fin d, (a i) ^ 2 * (∑ j : Fin d, |f i j|)) +
          ∑ j : Fin d, (b j) ^ 2 * (∑ i : Fin d, |f i j|) := hexpand
    _ ≤ (∑ i : Fin d, (a i) ^ 2) * S + (∑ j : Fin d, (b j) ^ 2) * S := hbound
    _ = S * ((∑ i : Fin d, (a i) ^ 2) + ∑ j : Fin d, (b j) ^ 2) := by ring

/-- `∑ᵢ(aᵢ)² = vecDot a a`. -/
private theorem mixGap_sum_sq_eq_vecDot_self (a : Vec d) :
    (∑ i : Fin d, (a i) ^ 2) = vecDot a a := by
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [sq]

/-- **The deterministic quadratic-form bound, Euclidean-normalized form.** -/
theorem mixGap_quadraticForm_euclidean_le [NeZero d] {nu : ℝ}
    (L nn m : ℕ) (P : ProbabilityMeasure (ShellSeq d)) (omega : ShellSeq d) (p q : BlockVec d) :
    2 * (((descendantsAtDepth (originCube d (m : ℤ)) (m - nn)).card : ℝ)⁻¹ *
        ∑ R ∈ descendantsAtDepth (originCube d (m : ℤ)) (m - nn),
          blockVecDot p (blockMatVecMul
            (ofFullBlockMat (toFullBlockMat
                  (coarseBlockMatrix (cubeSet R) (coefficientCutoff nu omega L).toCoeffField) -
                toFullBlockMat (annealedBlockMatrix nu L P (cubeSet (originCube d (nn : ℤ))))))
            q)) ≤
      (2 * mixGap_entrySumEnvelope nu L P nn m omega) * (blockVecDot p p + blockVecDot q q) := by
  rw [mixGap_avg_blockVecDot_eq]
  set sumUL : ℝ := ∑ i : Fin d, ∑ j : Fin d,
      |mixGap_avgEntryDeviation nu L P nn m (Sum.inl i) (Sum.inl j) omega| with hsumUL
  set sumUR : ℝ := ∑ i : Fin d, ∑ j : Fin d,
      |mixGap_avgEntryDeviation nu L P nn m (Sum.inl i) (Sum.inr j) omega| with hsumUR
  set sumLL : ℝ := ∑ i : Fin d, ∑ j : Fin d,
      |mixGap_avgEntryDeviation nu L P nn m (Sum.inr i) (Sum.inl j) omega| with hsumLL
  set sumLR : ℝ := ∑ i : Fin d, ∑ j : Fin d,
      |mixGap_avgEntryDeviation nu L P nn m (Sum.inr i) (Sum.inr j) omega| with hsumLR
  have hEeq : mixGap_entrySumEnvelope nu L P nn m omega = sumUL + sumUR + sumLL + sumLR := rfl
  have h1 := mixGap_blockAMGM_le
    (fun i j => mixGap_avgEntryDeviation nu L P nn m (Sum.inl i) (Sum.inl j) omega) p.1 q.1
  have h2 := mixGap_blockAMGM_le
    (fun i j => mixGap_avgEntryDeviation nu L P nn m (Sum.inl i) (Sum.inr j) omega) p.1 q.2
  have h3 := mixGap_blockAMGM_le
    (fun i j => mixGap_avgEntryDeviation nu L P nn m (Sum.inr i) (Sum.inl j) omega) p.2 q.1
  have h4 := mixGap_blockAMGM_le
    (fun i j => mixGap_avgEntryDeviation nu L P nn m (Sum.inr i) (Sum.inr j) omega) p.2 q.2
  rw [← hsumUL] at h1
  rw [← hsumUR] at h2
  rw [← hsumLL] at h3
  rw [← hsumLR] at h4
  have hUL_nn : 0 ≤ sumUL := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _
  have hUR_nn : 0 ≤ sumUR := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _
  have hLL_nn : 0 ≤ sumLL := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _
  have hLR_nn : 0 ≤ sumLR := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _
  have hnn1 : (0:ℝ) ≤ (∑ i : Fin d, (p.1 i)^2) + ∑ j : Fin d, (q.1 j)^2 := by positivity
  have hnn2 : (0:ℝ) ≤ (∑ i : Fin d, (p.1 i)^2) + ∑ j : Fin d, (q.2 j)^2 := by positivity
  have hnn3 : (0:ℝ) ≤ (∑ i : Fin d, (p.2 i)^2) + ∑ j : Fin d, (q.1 j)^2 := by positivity
  have hnn4 : (0:ℝ) ≤ (∑ i : Fin d, (p.2 i)^2) + ∑ j : Fin d, (q.2 j)^2 := by positivity
  have hE_UL : sumUL ≤ sumUL + sumUR + sumLL + sumLR := by linarith only [hUR_nn, hLL_nn, hLR_nn]
  have hE_UR : sumUR ≤ sumUL + sumUR + sumLL + sumLR := by linarith only [hUL_nn, hLL_nn, hLR_nn]
  have hE_LL : sumLL ≤ sumUL + sumUR + sumLL + sumLR := by linarith only [hUL_nn, hUR_nn, hLR_nn]
  have hE_LR : sumLR ≤ sumUL + sumUR + sumLL + sumLR := by linarith only [hUL_nn, hUR_nn, hLL_nn]
  have h1' : 2 * ∑ i : Fin d, ∑ j : Fin d, p.1 i *
      (mixGap_avgEntryDeviation nu L P nn m (Sum.inl i) (Sum.inl j) omega * q.1 j) ≤
      (sumUL + sumUR + sumLL + sumLR) * ((∑ i : Fin d, (p.1 i)^2) + ∑ j : Fin d, (q.1 j)^2) :=
    h1.trans (mul_le_mul_of_nonneg_right hE_UL hnn1)
  have h2' : 2 * ∑ i : Fin d, ∑ j : Fin d, p.1 i *
      (mixGap_avgEntryDeviation nu L P nn m (Sum.inl i) (Sum.inr j) omega * q.2 j) ≤
      (sumUL + sumUR + sumLL + sumLR) * ((∑ i : Fin d, (p.1 i)^2) + ∑ j : Fin d, (q.2 j)^2) :=
    h2.trans (mul_le_mul_of_nonneg_right hE_UR hnn2)
  have h3' : 2 * ∑ i : Fin d, ∑ j : Fin d, p.2 i *
      (mixGap_avgEntryDeviation nu L P nn m (Sum.inr i) (Sum.inl j) omega * q.1 j) ≤
      (sumUL + sumUR + sumLL + sumLR) * ((∑ i : Fin d, (p.2 i)^2) + ∑ j : Fin d, (q.1 j)^2) :=
    h3.trans (mul_le_mul_of_nonneg_right hE_LL hnn3)
  have h4' : 2 * ∑ i : Fin d, ∑ j : Fin d, p.2 i *
      (mixGap_avgEntryDeviation nu L P nn m (Sum.inr i) (Sum.inr j) omega * q.2 j) ≤
      (sumUL + sumUR + sumLL + sumLR) * ((∑ i : Fin d, (p.2 i)^2) + ∑ j : Fin d, (q.2 j)^2) :=
    h4.trans (mul_le_mul_of_nonneg_right hE_LR hnn4)
  have hsum := add_le_add (add_le_add h1' h2') (add_le_add h3' h4')
  rw [hEeq]
  have hpq1 : (∑ i : Fin d, (p.1 i) ^ 2) = vecDot p.1 p.1 := mixGap_sum_sq_eq_vecDot_self p.1
  have hpq2 : (∑ j : Fin d, (q.1 j) ^ 2) = vecDot q.1 q.1 := mixGap_sum_sq_eq_vecDot_self q.1
  have hpq3 : (∑ j : Fin d, (q.2 j) ^ 2) = vecDot q.2 q.2 := mixGap_sum_sq_eq_vecDot_self q.2
  have hpq4 : (∑ i : Fin d, (p.2 i) ^ 2) = vecDot p.2 p.2 := mixGap_sum_sq_eq_vecDot_self p.2
  show 2 * ((∑ i : Fin d, ∑ j : Fin d, p.1 i *
        (mixGap_avgEntryDeviation nu L P nn m (Sum.inl i) (Sum.inl j) omega * q.1 j)) +
      (∑ i : Fin d, ∑ j : Fin d, p.1 i *
          (mixGap_avgEntryDeviation nu L P nn m (Sum.inl i) (Sum.inr j) omega * q.2 j)) +
      (∑ i : Fin d, ∑ j : Fin d, p.2 i *
          (mixGap_avgEntryDeviation nu L P nn m (Sum.inr i) (Sum.inl j) omega * q.1 j)) +
      (∑ i : Fin d, ∑ j : Fin d, p.2 i *
          (mixGap_avgEntryDeviation nu L P nn m (Sum.inr i) (Sum.inr j) omega * q.2 j))) ≤
    2 * (sumUL + sumUR + sumLL + sumLR) * (blockVecDot p p + blockVecDot q q)
  rw [show blockVecDot p p + blockVecDot q q =
      (vecDot p.1 p.1 + vecDot p.2 p.2) + (vecDot q.1 q.1 + vecDot q.2 q.2) from rfl,
    ← hpq1, ← hpq2, ← hpq3, ← hpq4]
  nlinarith only [hsum]

/-! ## The crude-ellipticity conversion, and the `X4` witness -/

/-- **The deterministic quadratic-form bound, `Aell`-normalized form.**
Converts the Euclidean form via the crude ellipticity comparison
`mixTerms_crudeEllipticity` (`Section4/Mixing/Term1PolarizedBound.lean`). -/
theorem mixGap_quadraticForm_annealed_le [NeZero d] {nu : ℝ} (hnu : 0 < nu) (hnu1 : nu ≤ 1)
    (L nn m : ℕ) (hL : 1 ≤ L) (P : ProbabilityMeasure (ShellSeq d))
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P)
    (hJ4 : ShellLawJ4 d P) (omega : ShellSeq d) (p q : BlockVec d) :
    2 * (((descendantsAtDepth (originCube d (m : ℤ)) (m - nn)).card : ℝ)⁻¹ *
        ∑ R ∈ descendantsAtDepth (originCube d (m : ℤ)) (m - nn),
          blockVecDot p (blockMatVecMul
            (ofFullBlockMat (toFullBlockMat
                  (coarseBlockMatrix (cubeSet R) (coefficientCutoff nu omega L).toCoeffField) -
                toFullBlockMat (annealedBlockMatrix nu L P (cubeSet (originCube d (nn : ℤ))))))
            q)) ≤
      (2 * Section4.Ellipticity.ellipBelow_crudeConst d * nu ^ (-(3 : ℝ)) * (L : ℝ) *
          mixGap_entrySumEnvelope nu L P nn m omega) *
        (blockVecDot p (blockMatVecMul (annealedBlockMatrix nu L P (cubeSet (originCube d (nn : ℤ)))) p) +
          blockVecDot q (blockMatVecMul (annealedBlockMatrix nu L P (cubeSet (originCube d (nn : ℤ)))) q)) := by
  have heuc := mixGap_quadraticForm_euclidean_le (nu := nu) L nn m P omega p q
  have hcrudeP := mixTerms_crudeEllipticity d hnu hnu1 P hPrefix hJ2 hJ3 hJ4 L nn hL p
  have hcrudeQ := mixTerms_crudeEllipticity d hnu hnu1 P hPrefix hJ2 hJ3 hJ4 L nn hL q
  have hEnn : 0 ≤ mixGap_entrySumEnvelope nu L P nn m omega := by
    unfold mixGap_entrySumEnvelope
    have h1 : (0:ℝ) ≤ ∑ i : Fin d, ∑ j : Fin d,
        |mixGap_avgEntryDeviation nu L P nn m (Sum.inl i) (Sum.inl j) omega| :=
      Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _
    have h2 : (0:ℝ) ≤ ∑ i : Fin d, ∑ j : Fin d,
        |mixGap_avgEntryDeviation nu L P nn m (Sum.inl i) (Sum.inr j) omega| :=
      Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _
    have h3 : (0:ℝ) ≤ ∑ i : Fin d, ∑ j : Fin d,
        |mixGap_avgEntryDeviation nu L P nn m (Sum.inr i) (Sum.inl j) omega| :=
      Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _
    have h4 : (0:ℝ) ≤ ∑ i : Fin d, ∑ j : Fin d,
        |mixGap_avgEntryDeviation nu L P nn m (Sum.inr i) (Sum.inr j) omega| :=
      Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _
    linarith only [h1, h2, h3, h4]
  have hcrude : blockVecDot p p + blockVecDot q q ≤
      Section4.Ellipticity.ellipBelow_crudeConst d * nu ^ (-(3 : ℝ)) * (L : ℝ) *
        (blockVecDot p (blockMatVecMul (annealedBlockMatrix nu L P (cubeSet (originCube d (nn : ℤ)))) p) +
          blockVecDot q (blockMatVecMul (annealedBlockMatrix nu L P (cubeSet (originCube d (nn : ℤ)))) q)) := by
    have := add_le_add hcrudeP hcrudeQ
    nlinarith only [this]
  have hstep := mul_le_mul_of_nonneg_left hcrude
    (by positivity : (0:ℝ) ≤ 2 * mixGap_entrySumEnvelope nu L P nn m omega)
  refine heuc.trans (hstep.trans_eq ?_)
  ring

end

end SuperdiffusionCLT.Section4.Mixing

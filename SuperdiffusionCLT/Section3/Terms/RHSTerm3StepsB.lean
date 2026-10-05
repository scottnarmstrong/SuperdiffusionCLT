/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.RHSTerm3StepsA2

/-!
# `l.RHS.term3`, Step 2: the coarse-grained average term `e.RHS.term3.A`

The second step of the proof of `l.RHS.term3`: the intermediate coarse
scale `k`, the normalized flux additivity defect
`e.flux-additivity-estimate-in-an-lemma`, the two halves of the decomposition
`e.w-flux-indepen-decomp`, and the display `e.RHS.term3.A`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Terms

open MeasureTheory
open Homogenization
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section3.Setup
open SuperdiffusionCLT.Section2.Estimates.Stream
open SuperdiffusionCLT.Section2.Annealed

noncomputable section

variable {d : ℕ}

/-! ## `l.RHS.term3#coarse-block-scale-choice`

The intermediate coarse scale
`k = ⌈(4/(d+4))ℓ' + (d/(d+4))ℓ⌉` at which the outer lattice average of Step 2
is taken.  This choice balances the two competing
errors `3^{k−ℓ'}` (coarse averaging of `∇w`) and `3^{−d(k−ℓ)/2}`
(concentration over the sublattices). -/

/-- **The intermediate coarse scale `k`** of Step 2. -/
def coarseBlockScale (d : ℕ) (S : ScaleSelection) : ℕ :=
  ⌈(4 / ((d : ℝ) + 4)) * (S.ellPrime : ℝ) + ((d : ℝ) / ((d : ℝ) + 4)) * (S.ell : ℝ)⌉₊

private theorem interp_split (d : ℕ) (a b : ℝ) :
    (4 / ((d : ℝ) + 4)) * b + ((d : ℝ) / ((d : ℝ) + 4)) * a
      = a + (4 / ((d : ℝ) + 4)) * (b - a) := by
  have hd : ((d : ℝ) + 4) ≠ 0 := by positivity
  field_simp
  ring

private theorem interp_split' (d : ℕ) (a b : ℝ) :
    (4 / ((d : ℝ) + 4)) * b + ((d : ℝ) / ((d : ℝ) + 4)) * a
      = b - ((d : ℝ) / ((d : ℝ) + 4)) * (b - a) := by
  have hd : ((d : ℝ) + 4) ≠ 0 := by positivity
  field_simp
  ring

/-- **`l.RHS.term3#coarse-block-scale-choice`**.  The scale
`k = ⌈(4/(d+4))ℓ' + (d/(d+4))ℓ⌉` interpolates between `ℓ` and `ℓ'` and the two
printed exponent identities hold in the inequality form that the rounding
leaves: `k − ℓ ≥ (4/(d+4))(ℓ'−ℓ)` and `ℓ' − k ≤ (d/(d+4))(ℓ'−ℓ)`, which is the
direction both later displays use. -/
theorem coarse_block_scale_choice (d : ℕ) (S : ScaleSelection)
    (hS : S.ell ≤ S.ellPrime) :
    S.ell ≤ coarseBlockScale d S ∧ coarseBlockScale d S ≤ S.ellPrime ∧
      (4 / ((d : ℝ) + 4)) * ((S.ellPrime : ℝ) - (S.ell : ℝ)) ≤
        (coarseBlockScale d S : ℝ) - (S.ell : ℝ) ∧
      (S.ellPrime : ℝ) - (coarseBlockScale d S : ℝ) ≤
        ((d : ℝ) / ((d : ℝ) + 4)) * ((S.ellPrime : ℝ) - (S.ell : ℝ)) := by
  have hd : (0 : ℝ) < (d : ℝ) + 4 := by positivity
  have hle : ((S.ell : ℝ)) ≤ ((S.ellPrime : ℝ)) := by exact_mod_cast hS
  have hdiff : (0 : ℝ) ≤ (S.ellPrime : ℝ) - (S.ell : ℝ) := by linarith only [hle]
  set x : ℝ := (4 / ((d : ℝ) + 4)) * (S.ellPrime : ℝ) + ((d : ℝ) / ((d : ℝ) + 4)) * (S.ell : ℝ)
    with hx
  have hlow : (S.ell : ℝ) ≤ x := by
    rw [hx, interp_split d (S.ell : ℝ) (S.ellPrime : ℝ)]
    have : (0 : ℝ) ≤ (4 / ((d : ℝ) + 4)) * ((S.ellPrime : ℝ) - (S.ell : ℝ)) := by positivity
    linarith only [this]
  have hhigh : x ≤ (S.ellPrime : ℝ) := by
    rw [hx, interp_split' d (S.ell : ℝ) (S.ellPrime : ℝ)]
    have : (0 : ℝ) ≤ ((d : ℝ) / ((d : ℝ) + 4)) * ((S.ellPrime : ℝ) - (S.ell : ℝ)) := by
      positivity
    linarith only [this]
  have hceil : x ≤ (coarseBlockScale d S : ℝ) := Nat.le_ceil x
  have hceil' : (coarseBlockScale d S : ℝ) ≤ (S.ellPrime : ℝ) := by
    have : coarseBlockScale d S ≤ S.ellPrime := Nat.ceil_le.2 hhigh
    exact_mod_cast this
  refine ⟨?_, Nat.ceil_le.2 hhigh, ?_, ?_⟩
  · have : (S.ell : ℝ) ≤ (coarseBlockScale d S : ℝ) := le_trans hlow hceil
    exact_mod_cast this
  · have hxe : x - (S.ell : ℝ) = (4 / ((d : ℝ) + 4)) * ((S.ellPrime : ℝ) - (S.ell : ℝ)) := by
      rw [hx, interp_split d (S.ell : ℝ) (S.ellPrime : ℝ)]; ring
    linarith only [hceil, hxe]
  · have hxe : (S.ellPrime : ℝ) - x = ((d : ℝ) / ((d : ℝ) + 4)) * ((S.ellPrime : ℝ) - (S.ell : ℝ)) := by
      rw [hx, interp_split' d (S.ell : ℝ) (S.ellPrime : ℝ)]; ring
    linarith only [hceil, hxe]

/-- The first coarsening of the exponent produced by `coarseBlockScale`.

The paper writes `3^{k−ℓ'} ≤ 3^{−(d/(d+4))(ℓ'−ℓ)}`, which the *ceiling* in the
definition of `k` supports only up to one triadic scale: `k < x + 1` gives
`3^{k−ℓ'} ≤ 3·3^{−(d/(d+4))(ℓ'−ℓ)}`, and the extra factor `3` is absorbed into
`C(d)` (the paper states the identity only up to rounding).  For
`d ≥ 2` the printed rate is in turn at least as strong as the rate
`3^{−(ℓ'−ℓ)/4}` of `e.RHS.term3.A`, because `d ↦ d/(d+4)` is increasing and
equals `1/3` at `d = 2`; the manuscript does not say so (see
`l.RHS.term3#w-average-difference`). -/
theorem rpow_coarseBlockScale_sub_ellPrime_le (hd : 2 ≤ d) (S : ScaleSelection)
    (hS : S.ell ≤ S.ellPrime) :
    (3 : ℝ) ^ ((coarseBlockScale d S : ℝ) - (S.ellPrime : ℝ)) ≤
      3 * (3 : ℝ) ^ (-(((S.ellPrime - S.ell : ℕ) : ℝ) / 4)) := by
  have hd2 : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hdpos : (0 : ℝ) < (d : ℝ) + 4 := by positivity
  have hle : ((S.ell : ℝ)) ≤ ((S.ellPrime : ℝ)) := by exact_mod_cast hS
  have hdiff : (0 : ℝ) ≤ (S.ellPrime : ℝ) - (S.ell : ℝ) := by linarith only [hle]
  have hcast : (((S.ellPrime - S.ell : ℕ)) : ℝ) = (S.ellPrime : ℝ) - (S.ell : ℝ) := by
    push_cast [Nat.cast_sub hS]
    ring
  set x : ℝ := (4 / ((d : ℝ) + 4)) * (S.ellPrime : ℝ) + ((d : ℝ) / ((d : ℝ) + 4)) * (S.ell : ℝ)
    with hx
  have hxnn : (0 : ℝ) ≤ x := by
    have h1 : (0 : ℝ) ≤ (4 / ((d : ℝ) + 4)) * (S.ellPrime : ℝ) := by positivity
    have h2 : (0 : ℝ) ≤ ((d : ℝ) / ((d : ℝ) + 4)) * (S.ell : ℝ) := by positivity
    rw [hx]; linarith only [h1, h2]
  have hceil : (coarseBlockScale d S : ℝ) < x + 1 := Nat.ceil_lt_add_one hxnn
  have hxe : (S.ellPrime : ℝ) - x
      = ((d : ℝ) / ((d : ℝ) + 4)) * ((S.ellPrime : ℝ) - (S.ell : ℝ)) := by
    rw [hx, interp_split' d (S.ell : ℝ) (S.ellPrime : ℝ)]; ring
  have hfrac : (1 : ℝ) / 4 ≤ (d : ℝ) / ((d : ℝ) + 4) := by
    rw [le_div_iff₀ hdpos]; linarith only [hd2]
  have hmul : (1 / 4 : ℝ) * ((S.ellPrime : ℝ) - (S.ell : ℝ)) ≤
      ((d : ℝ) / ((d : ℝ) + 4)) * ((S.ellPrime : ℝ) - (S.ell : ℝ)) :=
    mul_le_mul_of_nonneg_right hfrac hdiff
  have hkey : (coarseBlockScale d S : ℝ) - (S.ellPrime : ℝ) ≤
      1 + -(((S.ellPrime - S.ell : ℕ) : ℝ) / 4) := by
    rw [hcast]
    linarith only [hceil, hxe, hmul]
  calc (3 : ℝ) ^ ((coarseBlockScale d S : ℝ) - (S.ellPrime : ℝ))
      ≤ (3 : ℝ) ^ ((1 : ℝ) + -(((S.ellPrime - S.ell : ℕ) : ℝ) / 4)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hkey
    _ = 3 * (3 : ℝ) ^ (-(((S.ellPrime - S.ell : ℕ) : ℝ) / 4)) := by
        rw [Real.rpow_add (by norm_num), Real.rpow_one]

/-! ## The two-scale lattice partition

`e.w-flux-indepen-decomp` writes the single average over
`3^nℤ^d ∩ cu_m` as the iterated average over `3^kℤ^d ∩ cu_m` and, inside each
coarse cube, over `z' + 3^nℤ^d ∩ cu_k`.  With the triadic carriers of the development this
iteration is exactly the descendant partition
`descendantsAtDepth Q ((m−k) + (k−n))`, which is proved here. -/

private theorem descendantsAtDepth_add_eq_biUnion (Q : TriadicCube d) (j : ℕ) :
    ∀ n : ℕ, descendantsAtDepth Q (j + n)
      = (descendantsAtDepth Q j).biUnion (fun R => descendantsAtDepth R n)
  | 0 => by
      simp
  | n + 1 => by
      rw [← Nat.add_assoc, descendantsAtDepth_succ,
        descendantsAtDepth_add_eq_biUnion Q j n, Finset.biUnion_biUnion]
      exact Finset.biUnion_congr rfl fun R _ => (descendantsAtDepth_succ R n).symm

private theorem cubeSet_nonempty' (Q : TriadicCube d) : (cubeSet Q).Nonempty := by
  refine ⟨cubeCenter Q, openCubeSet_subset_cubeSet Q ?_⟩
  rw [← ball_cubeCenter_eq_openCubeSet]
  simpa only [Metric.mem_ball, dist_self] using cubeRadius_pos Q

private theorem disjoint_descendantsAtDepth_of_ne {Q R R' : TriadicCube d} {j : ℕ} (n : ℕ)
    (hR : R ∈ descendantsAtDepth Q j) (hR' : R' ∈ descendantsAtDepth Q j) (hne : R ≠ R') :
    Disjoint (descendantsAtDepth R n) (descendantsAtDepth R' n) := by
  classical
  rw [Finset.disjoint_left]
  intro S hS hS'
  have h1 : cubeSet S ⊆ cubeSet R := cubeSet_subset_of_mem_descendantsAtDepth hS
  have h2 : cubeSet S ⊆ cubeSet R' := cubeSet_subset_of_mem_descendantsAtDepth hS'
  obtain ⟨x, hx⟩ := cubeSet_nonempty' S
  exact Set.disjoint_left.1
    (pairwiseDisjoint_descendantsAtDepth Q j (Finset.mem_coe.2 hR) (Finset.mem_coe.2 hR') hne)
    (h1 hx) (h2 hx)

/-- **The lattice partition of `e.w-flux-indepen-decomp`**: a sum over the
scale-`n` sub-cubes of `cu_m` is the iterated sum over the scale-`k` sub-cubes
and their own scale-`n` sub-cubes. -/
theorem sum_largeCubeSubcubes_eq_sum_descendants {n k m : ℕ} (hnk : n ≤ k) (hkm : k ≤ m)
    (f : TriadicCube d → ℝ) :
    ∑ z ∈ largeCubeSubcubes d n m, f z =
      ∑ z' ∈ largeCubeSubcubes d k m, ∑ z ∈ descendantsAtDepth z' (k - n), f z := by
  classical
  have hsplit : m - n = (m - k) + (k - n) := by omega
  rw [largeCubeSubcubes, hsplit, descendantsAtDepth_add_eq_biUnion,
    Finset.sum_biUnion (fun R hR R' hR' hne =>
      disjoint_descendantsAtDepth_of_ne (k - n) (Finset.mem_coe.1 hR)
        (Finset.mem_coe.1 hR') hne)]
  rfl

private theorem card_descendantsAtDepth_cast (Q : TriadicCube d) (j : ℕ) :
    (((descendantsAtDepth Q j).card : ℕ) : ℝ) = ((3 : ℝ) ^ d) ^ j := by
  rw [descendantsAtDepth_card]
  push_cast
  ring

/-- **The double lattice of `e.w-flux-indepen-decomp`**: the pairs `(z', z)`
with `z' ∈ 3^kℤ^d ∩ cu_m` and `z ∈ z' + 3^nℤ^d ∩ cu_k`. -/
def coarsePairs (d n k m : ℕ) : Finset ((_ : TriadicCube d) × TriadicCube d) :=
  (largeCubeSubcubes d k m).sigma fun z' => descendantsAtDepth z' (k - n)

theorem sum_coarsePairs {n k m : ℕ} (G : TriadicCube d → TriadicCube d → ℝ) :
    ∑ p ∈ coarsePairs d n k m, G p.1 p.2 =
      ∑ z' ∈ largeCubeSubcubes d k m, ∑ z ∈ descendantsAtDepth z' (k - n), G z' z :=
  (Finset.sum_sigma' _ _ fun z' z => G z' z).symm

theorem coarsePairs_card {n k m : ℕ} (hnk : n ≤ k) (hkm : k ≤ m) :
    (coarsePairs d n k m).card = (largeCubeSubcubes d n m).card := by
  classical
  have hsum : (coarsePairs d n k m).card
      = ∑ _z' ∈ largeCubeSubcubes d k m, ((3 ^ d) ^ (k - n) : ℕ) := by
    rw [coarsePairs, Finset.card_sigma]
    exact Finset.sum_congr rfl fun z' _ => descendantsAtDepth_card z' (k - n)
  rw [hsum, Finset.sum_const, smul_eq_mul, largeCubeSubcubes_card, largeCubeSubcubes_card,
    ← pow_add]
  congr 1
  omega

/-- The plain average of a function of the fine cube alone over the double
lattice is its plain average over `3^nℤ^d ∩ cu_m`. -/
theorem avsum_coarsePairs_snd {n k m : ℕ} (hnk : n ≤ k) (hkm : k ≤ m)
    (f : TriadicCube d → ℝ) :
    ((coarsePairs d n k m).card : ℝ)⁻¹ * ∑ p ∈ coarsePairs d n k m, f p.2 =
      ((largeCubeSubcubes d n m).card : ℝ)⁻¹ * ∑ z ∈ largeCubeSubcubes d n m, f z := by
  rw [coarsePairs_card hnk hkm, sum_coarsePairs (fun _ z => f z),
    ← sum_largeCubeSubcubes_eq_sum_descendants hnk hkm f]

/-- The printed nested average `avsum_{z'} avsum_z` is the plain average over
the double lattice. -/
theorem avsum_coarsePairs_eq_double_avsum {n k m : ℕ} (hnk : n ≤ k) (hkm : k ≤ m)
    (G : TriadicCube d → TriadicCube d → ℝ) :
    ((coarsePairs d n k m).card : ℝ)⁻¹ * ∑ p ∈ coarsePairs d n k m, G p.1 p.2 =
      ((largeCubeSubcubes d k m).card : ℝ)⁻¹ *
        ∑ z' ∈ largeCubeSubcubes d k m,
          (((descendantsAtDepth z' (k - n)).card : ℕ) : ℝ)⁻¹ *
            ∑ z ∈ descendantsAtDepth z' (k - n), G z' z := by
  classical
  have h3 : (0 : ℝ) < (3 : ℝ) ^ d := by positivity
  have hinner : ∀ z' ∈ largeCubeSubcubes d k m,
      (((descendantsAtDepth z' (k - n)).card : ℕ) : ℝ)⁻¹ *
          ∑ z ∈ descendantsAtDepth z' (k - n), G z' z =
        (((3 : ℝ) ^ d) ^ (k - n))⁻¹ * ∑ z ∈ descendantsAtDepth z' (k - n), G z' z := by
    intro z' _
    rw [card_descendantsAtDepth_cast]
  have hcardk : ((largeCubeSubcubes d k m).card : ℝ) = ((3 : ℝ) ^ d) ^ (m - k) := by
    rw [largeCubeSubcubes]
    exact card_descendantsAtDepth_cast _ _
  have hcardp : ((coarsePairs d n k m).card : ℝ) = ((3 : ℝ) ^ d) ^ (m - n) := by
    rw [coarsePairs_card hnk hkm, largeCubeSubcubes]
    exact card_descendantsAtDepth_cast _ _
  have hexp : (m - k) + (k - n) = m - n := by omega
  rw [Finset.sum_congr rfl hinner, ← Finset.mul_sum, sum_coarsePairs, hcardk, hcardp,
    ← mul_assoc, ← mul_inv, ← pow_add, hexp]

/-! ## Cauchy-Schwarz over the double lattice -/

/-- Cauchy-Schwarz for the plain average over a finite family. -/
private theorem avsum_mul_le_cauchy_schwarz {iota : Type*} (s : Finset iota) (hs : s.Nonempty)
    (a b : iota → ℝ) (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) :
    ((s.card : ℝ))⁻¹ * ∑ i ∈ s, a i ^ ((1 : ℝ) / 2) * b i ^ ((1 : ℝ) / 2) ≤
      (((s.card : ℝ))⁻¹ * ∑ i ∈ s, a i) ^ ((1 : ℝ) / 2) *
        (((s.card : ℝ))⁻¹ * ∑ i ∈ s, b i) ^ ((1 : ℝ) / 2) := by
  have hcard : (0 : ℝ) < (s.card : ℝ) := by exact_mod_cast Finset.card_pos.2 hs
  have hconj : Real.HolderConjugate (2 : ℝ) (2 : ℝ) :=
    ⟨by norm_num, by norm_num, by norm_num⟩
  have hmain := Real.inner_le_Lp_mul_Lq_of_nonneg (s := s)
    (f := fun i => a i ^ ((1 : ℝ) / 2)) (g := fun i => b i ^ ((1 : ℝ) / 2)) hconj
    (fun i _ => Real.rpow_nonneg (ha i) _) (fun i _ => Real.rpow_nonneg (hb i) _)
  have hA : ∀ i : iota, (a i ^ ((1 : ℝ) / 2)) ^ (2 : ℝ) = a i := by
    intro i
    rw [← Real.rpow_mul (ha i)]
    norm_num
  have hB : ∀ i : iota, (b i ^ ((1 : ℝ) / 2)) ^ (2 : ℝ) = b i := by
    intro i
    rw [← Real.rpow_mul (hb i)]
    norm_num
  simp only [hA, hB] at hmain
  have hexp : (1 : ℝ) / (2 : ℝ) = (1 : ℝ) / 2 := rfl
  rw [hexp] at hmain
  have hsa : (0 : ℝ) ≤ ∑ i ∈ s, a i := Finset.sum_nonneg fun i _ => ha i
  have hsb : (0 : ℝ) ≤ ∑ i ∈ s, b i := Finset.sum_nonneg fun i _ => hb i
  have hinvnn : (0 : ℝ) ≤ ((s.card : ℝ))⁻¹ := le_of_lt (inv_pos.2 hcard)
  have hstep := mul_le_mul_of_nonneg_left hmain hinvnn
  refine hstep.trans_eq ?_
  rw [Real.mul_rpow hinvnn hsa, Real.mul_rpow hinvnn hsb]
  have hsplit : ((s.card : ℝ))⁻¹ ^ ((1 : ℝ) / 2) * ((s.card : ℝ))⁻¹ ^ ((1 : ℝ) / 2) =
      ((s.card : ℝ))⁻¹ := by
    rw [← Real.rpow_add (inv_pos.2 hcard)]
    norm_num
  calc ((s.card : ℝ))⁻¹ * ((∑ i ∈ s, a i) ^ ((1 : ℝ) / 2) * (∑ i ∈ s, b i) ^ ((1 : ℝ) / 2))
      = (((s.card : ℝ))⁻¹ ^ ((1 : ℝ) / 2) * ((s.card : ℝ))⁻¹ ^ ((1 : ℝ) / 2)) *
        ((∑ i ∈ s, a i) ^ ((1 : ℝ) / 2) * (∑ i ∈ s, b i) ^ ((1 : ℝ) / 2)) := by
        rw [hsplit]
    _ = ((s.card : ℝ))⁻¹ ^ ((1 : ℝ) / 2) * (∑ i ∈ s, a i) ^ ((1 : ℝ) / 2) *
        (((s.card : ℝ))⁻¹ ^ ((1 : ℝ) / 2) * (∑ i ∈ s, b i) ^ ((1 : ℝ) / 2)) := by ring

/-- Cauchy-Schwarz for one Bochner integral, in the square-root form. -/
private theorem integral_rpow_half_mul_le {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} (f g : Omega → ℝ)
    (hf : ∀ omega, 0 ≤ f omega) (hg : ∀ omega, 0 ≤ g omega)
    (hMemf : MemLp (fun omega => f omega ^ ((1 : ℝ) / 2)) (ENNReal.ofReal (2 : ℝ)) mu)
    (hMemg : MemLp (fun omega => g omega ^ ((1 : ℝ) / 2)) (ENNReal.ofReal (2 : ℝ)) mu) :
    ∫ omega, f omega ^ ((1 : ℝ) / 2) * g omega ^ ((1 : ℝ) / 2) ∂mu ≤
      (∫ omega, f omega ∂mu) ^ ((1 : ℝ) / 2) * (∫ omega, g omega ∂mu) ^ ((1 : ℝ) / 2) := by
  have hconj : Real.HolderConjugate (2 : ℝ) (2 : ℝ) :=
    ⟨by norm_num, by norm_num, by norm_num⟩
  have hmain := MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg (μ := mu) hconj
    (f := fun omega => f omega ^ ((1 : ℝ) / 2)) (g := fun omega => g omega ^ ((1 : ℝ) / 2))
    (Filter.Eventually.of_forall fun omega => Real.rpow_nonneg (hf omega) _)
    (Filter.Eventually.of_forall fun omega => Real.rpow_nonneg (hg omega) _) hMemf hMemg
  have hAf : ∀ omega, (f omega ^ ((1 : ℝ) / 2)) ^ (2 : ℝ) = f omega := by
    intro omega
    rw [← Real.rpow_mul (hf omega)]
    norm_num
  have hAg : ∀ omega, (g omega ^ ((1 : ℝ) / 2)) ^ (2 : ℝ) = g omega := by
    intro omega
    rw [← Real.rpow_mul (hg omega)]
    norm_num
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hAf),
    MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hAg)] at hmain
  have hexp : (1 : ℝ) / (2 : ℝ) = (1 : ℝ) / 2 := rfl
  rw [hexp] at hmain
  exact hmain

/-- The two Cauchy-Schwarz steps of the coarse-average estimate combined: over the family
`s` and the probability space at once. -/
private theorem avsum_integral_rpow_half_mul_le {iota : Type*} (s : Finset iota)
    (hs : s.Nonempty) {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    (f g : iota → Omega → ℝ)
    (hf : ∀ i omega, 0 ≤ f i omega) (hg : ∀ i omega, 0 ≤ g i omega)
    (hMemf : ∀ i ∈ s,
      MemLp (fun omega => f i omega ^ ((1 : ℝ) / 2)) (ENNReal.ofReal (2 : ℝ)) mu)
    (hMemg : ∀ i ∈ s,
      MemLp (fun omega => g i omega ^ ((1 : ℝ) / 2)) (ENNReal.ofReal (2 : ℝ)) mu) :
    ((s.card : ℝ))⁻¹ *
        ∑ i ∈ s, ∫ omega, f i omega ^ ((1 : ℝ) / 2) * g i omega ^ ((1 : ℝ) / 2) ∂mu ≤
      (((s.card : ℝ))⁻¹ * ∑ i ∈ s, ∫ omega, f i omega ∂mu) ^ ((1 : ℝ) / 2) *
        (((s.card : ℝ))⁻¹ * ∑ i ∈ s, ∫ omega, g i omega ∂mu) ^ ((1 : ℝ) / 2) := by
  classical
  have hcard : (0 : ℝ) < (s.card : ℝ) := by exact_mod_cast Finset.card_pos.2 hs
  have hinvnn : (0 : ℝ) ≤ ((s.card : ℝ))⁻¹ := le_of_lt (inv_pos.2 hcard)
  set A : iota → ℝ := fun i => ∫ omega, f i omega ∂mu with hA
  set B : iota → ℝ := fun i => ∫ omega, g i omega ∂mu with hB
  have hAnn : ∀ i, 0 ≤ A i := fun i => MeasureTheory.integral_nonneg (hf i)
  have hBnn : ∀ i, 0 ≤ B i := fun i => MeasureTheory.integral_nonneg (hg i)
  have hstep : ∀ i ∈ s,
      ∫ omega, f i omega ^ ((1 : ℝ) / 2) * g i omega ^ ((1 : ℝ) / 2) ∂mu ≤
        A i ^ ((1 : ℝ) / 2) * B i ^ ((1 : ℝ) / 2) := fun i hi =>
    integral_rpow_half_mul_le _ _ (hf i) (hg i) (hMemf i hi) (hMemg i hi)
  calc ((s.card : ℝ))⁻¹ *
        ∑ i ∈ s, ∫ omega, f i omega ^ ((1 : ℝ) / 2) * g i omega ^ ((1 : ℝ) / 2) ∂mu
      ≤ ((s.card : ℝ))⁻¹ * ∑ i ∈ s, A i ^ ((1 : ℝ) / 2) * B i ^ ((1 : ℝ) / 2) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum hstep) hinvnn
    _ ≤ (((s.card : ℝ))⁻¹ * ∑ i ∈ s, A i) ^ ((1 : ℝ) / 2) *
        (((s.card : ℝ))⁻¹ * ∑ i ∈ s, B i) ^ ((1 : ℝ) / 2) :=
        avsum_mul_le_cauchy_schwarz s hs A B hAnn hBnn

theorem coarsePairs_nonempty (d n k m : ℕ) : (coarsePairs d n k m).Nonempty := by
  obtain ⟨z', hz'⟩ := largeCubeSubcubes_nonempty d k m
  obtain ⟨z, hz⟩ := descendantsAtDepth_nonempty z' (k - n)
  exact ⟨⟨z', z⟩, Finset.mem_sigma.2 ⟨hz', hz⟩⟩

/-! ## `e.flux-additivity-estimate-in-an-lemma` -/

/-- **`e.flux-additivity-estimate-in-an-lemma`**:

`E[avsum_z |b_{L'}^{-1/2}(z+cu_n)(a_{L'}∇(u_m − u_{n,z}))_{z+cu_n}|²]
   ≤ E[avsum_z ⨍_{z+cu_n} ∇(u_m−u_{n,z})·σ∇(u_m−u_{n,z})] ≤ δ + Cη_L`

at `σ = νId`, so that the middle member is exactly the left side of
`e.additivity.error.superdiff` in the shape of
`additivity_error_superdiff`.

The normalized flux `|b_{L'}^{-1/2}(z+cu_n)(a_{L'}∇(u_m−u_{n,z}))_{z+cu_n}|²`
has no carrier here (the matrix square root of the coarse block on a
translated cube is not available), so it is the free binder `normFlux`, and the
first inequality — `e.energymaps.nonsymm.flux` applied to the *difference*
`u_m − u_{n,z}` of two maximizers — is the hypothesis `hEnergyMaps`.  Note that
`e.energymaps.nonsymm.flux` is stated for a single solution `u ∈ A(U)`, while
here it is applied to the difference `u_m − u_{n,z}`, so the paper uses the
linearity of `A(U)` silently.

The second inequality is `hEnergy`, i.e. the conclusion of
`additivity_error_superdiff` verbatim. -/
theorem flux_additivity_estimate
    {nu : ℝ} (P : ProbabilityMeasure (ShellSeq d)) (S : ScaleSelection)
    (uMgrad uNGlued : ShellSeq d → Vec d → Vec d)
    (normFlux : ShellSeq d → TriadicCube d → ℝ) {delta etaL : ℝ}
    (hEnergyMaps : ∀ omega : ShellSeq d, ∀ R ∈ largeCubeSubcubes d S.n S.m,
      normFlux omega R ≤
        volumeAverage (openCubeSet R)
          (fun y => nu * vecNormSq (uMgrad omega y - uNGlued omega y)))
    (hFluxInt : ∀ R ∈ largeCubeSubcubes d S.n S.m,
      Integrable (fun omega : ShellSeq d => normFlux omega R) P.toMeasure)
    (hEnergyInt : ∀ R ∈ largeCubeSubcubes d S.n S.m,
      Integrable (fun omega : ShellSeq d =>
        volumeAverage (openCubeSet R)
          (fun y => nu * vecNormSq (uMgrad omega y - uNGlued omega y))) P.toMeasure)
    (hEnergy : ((largeCubeSubcubes d S.n S.m).card : ℝ)⁻¹ *
        ∑ R ∈ largeCubeSubcubes d S.n S.m,
          ∫ omega : ShellSeq d,
            volumeAverage (openCubeSet R)
              (fun y => nu * vecNormSq (uMgrad omega y - uNGlued omega y))
            ∂P.toMeasure ≤ delta + etaL) :
    ((largeCubeSubcubes d S.n S.m).card : ℝ)⁻¹ *
        ∑ R ∈ largeCubeSubcubes d S.n S.m,
          ∫ omega : ShellSeq d, normFlux omega R ∂P.toMeasure ≤ delta + etaL := by
  refine le_trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum ?_)
    (inv_nonneg.2 (Nat.cast_nonneg _))) hEnergy
  intro R hR
  exact MeasureTheory.integral_mono (hFluxInt R hR) (hEnergyInt R hR)
    fun omega => hEnergyMaps omega R hR

/-- The Cauchy-Schwarz template of the coarse-average estimates: a family of
quenched pairings dominated by `A^{1/2}B^{1/2}` has its averaged expectation
dominated by `(avsum E[A])^{1/2}` times the square root of any bound for
`avsum E[B]`. -/
theorem integral_avsum_le_rpow_half_mul {iota : Type*} (T : Finset iota)
    (hTne : T.Nonempty) {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    (X A B : Omega → iota → ℝ) {delta etaL : ℝ}
    (hAnn : ∀ (omega : Omega) (i : iota), 0 ≤ A omega i)
    (hBnn : ∀ (omega : Omega) (i : iota), 0 ≤ B omega i)
    (hInsert : ∀ omega : Omega, ∀ i ∈ T,
      X omega i ≤ A omega i ^ ((1 : ℝ) / 2) * B omega i ^ ((1 : ℝ) / 2))
    (hBavg : ((T.card : ℝ))⁻¹ * ∑ i ∈ T, ∫ omega, B omega i ∂mu ≤ delta + etaL)
    (hXint : Integrable (fun omega => ((T.card : ℝ))⁻¹ * ∑ i ∈ T, X omega i) mu)
    (hProdInt : ∀ i ∈ T,
      Integrable (fun omega => A omega i ^ ((1 : ℝ) / 2) * B omega i ^ ((1 : ℝ) / 2)) mu)
    (hMemA : ∀ i ∈ T,
      MemLp (fun omega => A omega i ^ ((1 : ℝ) / 2)) (ENNReal.ofReal (2 : ℝ)) mu)
    (hMemB : ∀ i ∈ T,
      MemLp (fun omega => B omega i ^ ((1 : ℝ) / 2)) (ENNReal.ofReal (2 : ℝ)) mu) :
    ∫ omega, ((T.card : ℝ))⁻¹ * ∑ i ∈ T, X omega i ∂mu ≤
      (((T.card : ℝ))⁻¹ * ∑ i ∈ T, ∫ omega, A omega i ∂mu) ^ ((1 : ℝ) / 2) *
        (delta + etaL) ^ ((1 : ℝ) / 2) := by
  classical
  have hcnn : (0 : ℝ) ≤ ((T.card : ℝ))⁻¹ := inv_nonneg.2 (Nat.cast_nonneg _)
  have hprodIntSum : Integrable (fun omega => ((T.card : ℝ))⁻¹ *
      ∑ i ∈ T, A omega i ^ ((1 : ℝ) / 2) * B omega i ^ ((1 : ℝ) / 2)) mu :=
    (MeasureTheory.integrable_finsetSum _ fun i hi => hProdInt i hi).const_mul _
  have hstep1 : ∫ omega, ((T.card : ℝ))⁻¹ * ∑ i ∈ T, X omega i ∂mu ≤
      ∫ omega, ((T.card : ℝ))⁻¹ *
        ∑ i ∈ T, A omega i ^ ((1 : ℝ) / 2) * B omega i ^ ((1 : ℝ) / 2) ∂mu :=
    MeasureTheory.integral_mono hXint hprodIntSum fun omega =>
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i hi => hInsert omega i hi) hcnn
  have hswap : ∫ omega, ((T.card : ℝ))⁻¹ *
        ∑ i ∈ T, A omega i ^ ((1 : ℝ) / 2) * B omega i ^ ((1 : ℝ) / 2) ∂mu =
      ((T.card : ℝ))⁻¹ * ∑ i ∈ T,
        ∫ omega, A omega i ^ ((1 : ℝ) / 2) * B omega i ^ ((1 : ℝ) / 2) ∂mu := by
    rw [MeasureTheory.integral_const_mul,
      MeasureTheory.integral_finsetSum _ fun i hi => hProdInt i hi]
  have hCS := avsum_integral_rpow_half_mul_le (mu := mu) T hTne
    (fun i omega => A omega i) (fun i omega => B omega i)
    (fun i omega => hAnn omega i) (fun i omega => hBnn omega i) hMemA hMemB
  have hAavgnn : (0 : ℝ) ≤ ((T.card : ℝ))⁻¹ * ∑ i ∈ T, ∫ omega, A omega i ∂mu :=
    mul_nonneg hcnn (Finset.sum_nonneg fun i _ =>
      MeasureTheory.integral_nonneg fun omega => hAnn omega i)
  have hBavgnn : (0 : ℝ) ≤ ((T.card : ℝ))⁻¹ * ∑ i ∈ T, ∫ omega, B omega i ∂mu :=
    mul_nonneg hcnn (Finset.sum_nonneg fun i _ =>
      MeasureTheory.integral_nonneg fun omega => hBnn omega i)
  refine (hstep1.trans_eq hswap).trans (hCS.trans ?_)
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hBavgnn hBavg (by norm_num))
    (Real.rpow_nonneg hAavgnn _)

/-! ## `l.RHS.term3#coarse-average-CS` -/

/-- **`l.RHS.term3#coarse-average-CS`**: the first term of the decomposition
`e.w-flux-indepen-decomp`, in which the `∇w` factor has already been coarsened
to the scale-`k` cube, is estimated by Cauchy-Schwarz against the normalized
flux defect of `e.flux-additivity-estimate-in-an-lemma`.

`bHalfW omega z' z` is the printed `|b_{L'}^{1/2}(z+cu_n)(∇w)_{z'+cu_k}|²` and
`normFlux omega z` the printed
`|b_{L'}^{-1/2}(z+cu_n)(a_{L'}∇(u_m−u_{n,z}))_{z+cu_n}|²`; neither has a
carrier here.  The hypothesis `hInsert` is the printed identity
followed by the pointwise Cauchy-Schwarz inequality in `ℝ^d`: the paper inserts
`b_{L'}^{1/2}(z+cu_n) b_{L'}^{-1/2}(z+cu_n)`, which requires
`b_{L'}(z+cu_n)` to be invertible, and does not remark on this.

Both Cauchy-Schwarz steps that the paper performs at once — over the
probability space and over the double lattice — are proved here, and
`hFluxAvg` is the conclusion of `flux_additivity_estimate` verbatim. -/
theorem coarse_average_CS
    {nu : ℝ} (P : ProbabilityMeasure (ShellSeq d)) (S : ScaleSelection) {k : ℕ}
    (hnk : S.n ≤ k) (hkm : k ≤ S.m)
    (w : ShellSeq d → H10Function (openCubeSet (originCube d (S.m : ℤ))))
    (uMgrad uNGlued : ShellSeq d → Vec d → Vec d)
    (bHalfW : ShellSeq d → TriadicCube d → TriadicCube d → ℝ)
    (normFlux : ShellSeq d → TriadicCube d → ℝ) {delta etaL : ℝ}
    (hbWnn : ∀ (omega : ShellSeq d) (z' z : TriadicCube d), 0 ≤ bHalfW omega z' z)
    (hnfnn : ∀ (omega : ShellSeq d) (z : TriadicCube d), 0 ≤ normFlux omega z)
    (hInsert : ∀ omega : ShellSeq d, ∀ p ∈ coarsePairs d S.n k S.m,
      vecDot (volumeAverageVec (openCubeSet p.1) ((w omega).toH1Function.grad))
          (volumeAverageVec (openCubeSet p.2)
            (fun y => matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y)
              (uMgrad omega y - uNGlued omega y))) ≤
        bHalfW omega p.1 p.2 ^ ((1 : ℝ) / 2) * normFlux omega p.2 ^ ((1 : ℝ) / 2))
    (hFluxAvg : ((largeCubeSubcubes d S.n S.m).card : ℝ)⁻¹ *
        ∑ z ∈ largeCubeSubcubes d S.n S.m,
          ∫ omega : ShellSeq d, normFlux omega z ∂P.toMeasure ≤ delta + etaL)
    (hLHSint : Integrable (fun omega : ShellSeq d =>
      ((coarsePairs d S.n k S.m).card : ℝ)⁻¹ * ∑ p ∈ coarsePairs d S.n k S.m,
        vecDot (volumeAverageVec (openCubeSet p.1) ((w omega).toH1Function.grad))
          (volumeAverageVec (openCubeSet p.2)
            (fun y => matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y)
              (uMgrad omega y - uNGlued omega y)))) P.toMeasure)
    (hProdInt : ∀ p ∈ coarsePairs d S.n k S.m, Integrable (fun omega : ShellSeq d =>
      bHalfW omega p.1 p.2 ^ ((1 : ℝ) / 2) * normFlux omega p.2 ^ ((1 : ℝ) / 2)) P.toMeasure)
    (hMemb : ∀ p ∈ coarsePairs d S.n k S.m,
      MemLp (fun omega : ShellSeq d => bHalfW omega p.1 p.2 ^ ((1 : ℝ) / 2))
        (ENNReal.ofReal (2 : ℝ)) P.toMeasure)
    (hMemf : ∀ p ∈ coarsePairs d S.n k S.m,
      MemLp (fun omega : ShellSeq d => normFlux omega p.2 ^ ((1 : ℝ) / 2))
        (ENNReal.ofReal (2 : ℝ)) P.toMeasure) :
    ∫ omega : ShellSeq d,
        ((coarsePairs d S.n k S.m).card : ℝ)⁻¹ * ∑ p ∈ coarsePairs d S.n k S.m,
          vecDot (volumeAverageVec (openCubeSet p.1) ((w omega).toH1Function.grad))
            (volumeAverageVec (openCubeSet p.2)
              (fun y => matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y)
                (uMgrad omega y - uNGlued omega y))) ∂P.toMeasure ≤
      (((largeCubeSubcubes d k S.m).card : ℝ)⁻¹ *
          ∑ z' ∈ largeCubeSubcubes d k S.m,
            (((descendantsAtDepth z' (k - S.n)).card : ℕ) : ℝ)⁻¹ *
              ∑ z ∈ descendantsAtDepth z' (k - S.n),
                ∫ omega : ShellSeq d, bHalfW omega z' z ∂P.toMeasure) ^ ((1 : ℝ) / 2) *
        (delta + etaL) ^ ((1 : ℝ) / 2) := by
  have hBavg : ((coarsePairs d S.n k S.m).card : ℝ)⁻¹ *
      ∑ p ∈ coarsePairs d S.n k S.m,
        ∫ omega : ShellSeq d, normFlux omega p.2 ∂P.toMeasure ≤ delta + etaL := by
    rw [avsum_coarsePairs_snd hnk hkm
      (fun z => ∫ omega : ShellSeq d, normFlux omega z ∂P.toMeasure)]
    exact hFluxAvg
  have hmain := integral_avsum_le_rpow_half_mul (mu := P.toMeasure)
    (coarsePairs d S.n k S.m) (coarsePairs_nonempty d S.n k S.m)
    (fun omega p => vecDot (volumeAverageVec (openCubeSet p.1) ((w omega).toH1Function.grad))
      (volumeAverageVec (openCubeSet p.2)
        (fun y => matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y)
          (uMgrad omega y - uNGlued omega y))))
    (fun omega p => bHalfW omega p.1 p.2) (fun omega p => normFlux omega p.2)
    (fun omega p => hbWnn omega p.1 p.2) (fun omega p => hnfnn omega p.2)
    hInsert hBavg hLHSint hProdInt hMemb hMemf
  rwa [avsum_coarsePairs_eq_double_avsum hnk hkm
    (fun z' z => ∫ omega : ShellSeq d, bHalfW omega z' z ∂P.toMeasure)] at hmain

end

end SuperdiffusionCLT.Section3.Terms

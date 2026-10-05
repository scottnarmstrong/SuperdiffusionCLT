/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Homogenization.Book.Ch02
public import Homogenization.Internal.Ch02.Representatives
public import SuperdiffusionCLT.Section2.Localization.BlockGauge

/-!
# Localization of the coarse-grained block matrix

This module proves the deterministic localization lemma `l.localization.A` of
the paper: for a positive symmetric field `s`, anti-symmetric fields `k` and
`h`, and `a = s + k`,

`-D bfA(U; a) ≤ bfA(U; a + h) - bfA(U; a) ≤ D bfA(U; a)`,

with `D = ‖s^{-1/2} h s^{-1/2}‖_{L^infinity(U)} (1 + ‖s^{-1/2} h s^{-1/2}‖_{L^infinity(U)})`.

## Carrier

The statement is on the **public Chapter 2 carrier** `Domain d` / `CoeffOn U`
of `CoarseGraining`, because that is the layer on which
`Homogenization.Book.Ch02.coarseBlockMatrix` and its variational
characterization `e.J.P0.Dirichlet` are unconditional:
`Homogenization.Book.Ch02.doubledMuTheory` supplies both the existence of a
minimizer and the identity `doubledMu U a P = ½ P · bfA(U; a) P` with no extra
premise. On the raw `Set (Vec d)` / `CoeffField d` layer the corresponding
`existsUnique_coarseBlockMatrix` carries an existence hypothesis. The raw
reading is available through `Homogenization.Book.Ch02.doubledMu_eq_Mu`, which
identifies the public infimum with the raw `Homogenization.Mu` of the same
coefficient representative.

`Domain d` is *bounded open convex nonempty*, a documented narrowing of the
manuscript's *bounded Lipschitz*; it contains every triadic cube, which is all
Sections 3 to 5 use.

## The constant

`D` is `θ (1 + θ)` for any `θ` bounding `‖s^{-1/2} h s^{-1/2}‖` on `U`.
The bound is expressed square-root-free as

`2 r · h(x) p ≤ θ (p · s(x) p + r · s(x) r)` for all `p, r`,

which is literally `2 v · eta u ≤ θ (|u|^2 + |v|^2)` after `u = s^{1/2} p`,
`v = s^{1/2} r`, hence exactly `‖s^{-1/2} h s^{-1/2}‖ ≤ θ`. See
`SuperdiffusionCLT.Section2.Localization.BlockGauge`.

## Ellipticity data

`CoeffOn U` bundles quantitative ellipticity constants. The perturbed field
`a + h` therefore needs its own bundle, which is supplied as the second
coefficient object `b` of the statements below, together with the
almost-everywhere identification `b = a + h` on `U`. This is explicit typing
data, not a proof step: no conclusion of the manuscript is assumed.

## Almost-everywhere hypotheses

The manuscript's `‖·‖_{L^infinity(U)}` is an essential supremum and `CoeffOn U`
is an almost-everywhere object: it fixes a coefficient field only up to a null
set of `U`. The perturbation hypotheses below are therefore stated for
`volume`-almost every `x` of `U`, which is the literal reading of the printed
`L^infinity` bound.

The sign condition `0 ≤ θ` of the pointwise lemmas in
`SuperdiffusionCLT.Section2.Localization.BlockGauge` is not assumed here:
testing the relative bound at `r = h(x) p` makes its left-hand side
`2 |h(x) p|^2 ≥ 0` while ellipticity makes its right-hand side bracket
positive, so any admissible `θ` is nonnegative as soon as `Vec d` contains a
nonzero vector. In the remaining case `d = 0` every block quadratic form
vanishes and the conclusions hold for every real `θ`.

## Main results

* `doubledMu_le_of_ae`: monotonicity of the variational quantity
  `e.J.P0.Dirichlet` under a pointwise comparison of block coefficient fields.
* `blockVecDot_coarseBlockMatrix_le_of_ae`: the same for `bfA(U; ·)`.
* `coarseBlockMatrix_toCoeffField`: the raw `Homogenization.coarseBlockMatrix`
  of the representative is the public Chapter 2 `bfA(U; a)`, so every
  conclusion below reads on the raw carrier as well.
* `coarseBlockMatrix_add_skew_le`, `coarseBlockMatrix_le_add_skew`: the two
  ratio bounds `bfA(U; a+h) ≤ (1+D) bfA(U; a)` and `bfA(U; a) ≤ (1+D) bfA(U; a+h)`
  of the manuscript's `e.localize.matrix.bounds.in.lemma` and its flip.
* `coarseBlockMatrix_localization`: the lemma `l.localization.A` itself, in the
  block Loewner order.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section2.Localization

open Homogenization
open Homogenization.Book.Ch02
open MeasureTheory

noncomputable section

variable {d : ℕ}

/-! ## Integrability of the doubled energy of an admissible field -/

private theorem integrableOn_blockEnergyDensity {U : Domain d} (a : CoeffOn U)
    {X : BlockState d} (hX : MemBlockL2 (U : Set (Vec d)) X.eval) :
    IntegrableOn (blockEnergyDensity a.toCoeffField X) (U : Set (Vec d)) := by
  have hrep := Homogenization.Internal.Ch02.BookCh02.pointwiseCoeffOn_isEllipticFieldOn U a
  have hint := blockEnergyDensity_integrableOn_of_memBlockL2_of_isEllipticFieldOn hX hrep
  refine hint.congr ?_
  have hae := Homogenization.Internal.Ch02.BookCh02.pointwiseCoeffOn_ae_eq U a
  exact hae.mono fun x hx => by
    simp only [blockEnergyDensity, blockCoeffField, hx]

private theorem memVectorL2_of_sub {U : Domain d} {f : Vec d → Vec d} {v : Vec d}
    (hf : MemVectorL2 (U : Set (Vec d)) (fun x => f x - v)) :
    MemVectorL2 (U : Set (Vec d)) f := by
  have h := (MeasureTheory.memLp_const
    (μ := volumeMeasureOn (U : Set (Vec d))) (c := v) (p := 2)).add hf
  have heq : ((fun _ : Vec d => v) + fun x => f x - v) = f := by
    funext x
    simp only [Pi.add_apply]
    abel
  rwa [heq] at h

private theorem memBlockL2_of_admissible {U : Domain d} {P : BlockVec d}
    {X : DoubledField d} (hX : IsDoubledMuAdmissible U P X) :
    MemBlockL2 (U : Set (Vec d)) (BlockState.mk X.potential X.flux).eval := by
  have hp : MemVectorL2 (U : Set (Vec d)) X.potential := memVectorL2_of_sub hX.1.1
  have hq : MemVectorL2 (U : Set (Vec d)) X.flux := memVectorL2_of_sub hX.2.1
  exact memBlockL2_blockField hp hq

/-! ## Monotonicity of the variational quantity -/

private theorem volumeAverage_le_of_ae {U : Domain d} {f g : Vec d → ℝ} {c : ℝ}
    (hg : IntegrableOn g (U : Set (Vec d)))
    (hf0 : 0 ≤ᵐ[volumeMeasureOn (U : Set (Vec d))] f)
    (hfg : f ≤ᵐ[volumeMeasureOn (U : Set (Vec d))] fun x => c * g x) :
    volumeAverage (U : Set (Vec d)) f ≤ c * volumeAverage (U : Set (Vec d)) g := by
  have hint : ∫ x in (U : Set (Vec d)), f x ≤ ∫ x in (U : Set (Vec d)), c * g x :=
    integral_mono_of_nonneg hf0 (hg.const_mul c) hfg
  have hcg : ∫ x in (U : Set (Vec d)), c * g x = c * ∫ x in (U : Set (Vec d)), g x :=
    integral_const_mul c g
  have hvol : (0 : ℝ) ≤ (MeasureTheory.volume (U : Set (Vec d))).toReal⁻¹ := by
    positivity
  have hmul := mul_le_mul_of_nonneg_left hint hvol
  rw [hcg] at hmul
  unfold volumeAverage
  linarith only [hmul]

private theorem doubledMuValue_le_of_ae {U : Domain d} (a b : CoeffOn U) {c : ℝ}
    (hae : ∀ᵐ x ∂(volumeMeasureOn (U : Set (Vec d))),
      ∀ Y : BlockVec d,
        blockVecDot Y (blockMatVecMul (blockMatrixOfCoeff (b.toCoeffField x)) Y) ≤
          c * blockVecDot Y (blockMatVecMul (blockMatrixOfCoeff (a.toCoeffField x)) Y))
    {P : BlockVec d} {X : DoubledField d} (hX : IsDoubledMuAdmissible U P X) :
    doubledMuValue U b X ≤ c * doubledMuValue U a X := by
  have hZ : MemBlockL2 (U : Set (Vec d))
      (BlockState.mk X.potential X.flux).eval := memBlockL2_of_admissible hX
  have hga : IntegrableOn
      (blockEnergyDensity a.toCoeffField (BlockState.mk X.potential X.flux))
      (U : Set (Vec d)) := integrableOn_blockEnergyDensity a hZ
  have hf0 : 0 ≤ᵐ[volumeMeasureOn (U : Set (Vec d))]
      blockEnergyDensity b.toCoeffField (BlockState.mk X.potential X.flux) := by
    refine b.aeElliptic.mono fun x hx => ?_
    show (0 : ℝ) ≤ blockEnergyDensity b.toCoeffField (BlockState.mk X.potential X.flux) x
    have h := blockMatrixOfCoeff_quadratic_nonneg hx
      ((BlockState.mk X.potential X.flux).eval x)
    have hb : blockEnergyDensity b.toCoeffField (BlockState.mk X.potential X.flux) x =
        (1 / 2 : ℝ) * blockVecDot ((BlockState.mk X.potential X.flux).eval x)
          (blockMatVecMul (blockMatrixOfCoeff (b.toCoeffField x))
            ((BlockState.mk X.potential X.flux).eval x)) := rfl
    rw [hb]
    linarith only [h]
  have hfg : blockEnergyDensity b.toCoeffField (BlockState.mk X.potential X.flux)
      ≤ᵐ[volumeMeasureOn (U : Set (Vec d))]
      fun x => c * blockEnergyDensity a.toCoeffField
        (BlockState.mk X.potential X.flux) x := by
    refine hae.mono fun x hx => ?_
    show blockEnergyDensity b.toCoeffField (BlockState.mk X.potential X.flux) x ≤
      c * blockEnergyDensity a.toCoeffField (BlockState.mk X.potential X.flux) x
    have h := hx ((BlockState.mk X.potential X.flux).eval x)
    have hb : blockEnergyDensity b.toCoeffField (BlockState.mk X.potential X.flux) x =
        (1 / 2 : ℝ) * blockVecDot ((BlockState.mk X.potential X.flux).eval x)
          (blockMatVecMul (blockMatrixOfCoeff (b.toCoeffField x))
            ((BlockState.mk X.potential X.flux).eval x)) := rfl
    have ha : blockEnergyDensity a.toCoeffField (BlockState.mk X.potential X.flux) x =
        (1 / 2 : ℝ) * blockVecDot ((BlockState.mk X.potential X.flux).eval x)
          (blockMatVecMul (blockMatrixOfCoeff (a.toCoeffField x))
            ((BlockState.mk X.potential X.flux).eval x)) := rfl
    rw [hb, ha]
    linarith only [h]
  exact volumeAverage_le_of_ae hga hf0 hfg

/-- Monotonicity of the variational quantity of `e.J.P0.Dirichlet` in the block
coefficient field. The admissible class of the infimum does not depend on the
coefficient field, so a pointwise comparison of the doubled energy densities
transfers to the infima. -/
theorem doubledMu_le_of_ae {U : Domain d} (a b : CoeffOn U) {c : ℝ}
    (hae : ∀ᵐ x ∂(volumeMeasureOn (U : Set (Vec d))),
      ∀ Y : BlockVec d,
        blockVecDot Y (blockMatVecMul (blockMatrixOfCoeff (b.toCoeffField x)) Y) ≤
          c * blockVecDot Y (blockMatVecMul (blockMatrixOfCoeff (a.toCoeffField x)) Y))
    (P : BlockVec d) :
    doubledMu U b P ≤ c * doubledMu U a P := by
  obtain ⟨Xa, hXa⟩ := (doubledMuTheory U a).minimizer_exists P
  obtain ⟨Xb, hXb⟩ := (doubledMuTheory U b).minimizer_exists P
  have h1 : doubledMu U b P = doubledMuValue U b Xb :=
    (IsDoubledMuMinimizer.doubledMuValue_eq_doubledMu hXb).symm
  have h2 : doubledMuValue U b Xb ≤ doubledMuValue U b Xa := hXb.2 Xa hXa.1
  have h3 : doubledMuValue U b Xa ≤ c * doubledMuValue U a Xa :=
    doubledMuValue_le_of_ae a b hae hXa.1
  have h4 : doubledMuValue U a Xa = doubledMu U a P :=
    IsDoubledMuMinimizer.doubledMuValue_eq_doubledMu hXa
  rw [h1, ← h4]
  linarith only [h2, h3]

/-- The coarse-grained block matrix inherits the pointwise comparison, as a
quadratic form. -/
theorem blockVecDot_coarseBlockMatrix_le_of_ae {U : Domain d} (a b : CoeffOn U) {c : ℝ}
    (hae : ∀ᵐ x ∂(volumeMeasureOn (U : Set (Vec d))),
      ∀ Y : BlockVec d,
        blockVecDot Y (blockMatVecMul (blockMatrixOfCoeff (b.toCoeffField x)) Y) ≤
          c * blockVecDot Y (blockMatVecMul (blockMatrixOfCoeff (a.toCoeffField x)) Y))
    (P : BlockVec d) :
    blockVecDot P (blockMatVecMul (Book.Ch02.coarseBlockMatrix U b) P) ≤
      c * blockVecDot P (blockMatVecMul (Book.Ch02.coarseBlockMatrix U a) P) := by
  have ha := (doubledMuTheory U a).mu_quadratic P
  have hb := (doubledMuTheory U b).mu_quadratic P
  have hmu := doubledMu_le_of_ae a b hae P
  rw [ha, hb] at hmu
  linarith only [hmu]

/-- The coarse-grained block matrix is positive semidefinite as a quadratic
form; this is `e.CG.bounds.2` in its weak form. -/
theorem zero_le_blockVecDot_coarseBlockMatrix (U : Domain d) (a : CoeffOn U)
    (P : BlockVec d) :
    0 ≤ blockVecDot P (blockMatVecMul (Book.Ch02.coarseBlockMatrix U a) P) := by
  rcases eq_or_ne P 0 with rfl | hP
  · simp [blockVecDot, vecDot]
  · exact ((blockCoarseMatrixTheory U a).block_matrix_posDef P hP).le

/-- The two carriers agree for the coarse block matrix. The raw
`Homogenization.coarseBlockMatrix`, obtained by polarizing `Homogenization.Mu`,
equals the public Chapter 2 block matrix, because the latter is symmetric and
represents `Mu` quadratically. Every statement below therefore also reads on
the raw `Set (Vec d)` / `CoeffField d` carrier. -/
theorem coarseBlockMatrix_toCoeffField (U : Domain d) (a : CoeffOn U) :
    Homogenization.coarseBlockMatrix (U : Set (Vec d)) a.toCoeffField =
      Book.Ch02.coarseBlockMatrix U a := by
  refine (eq_coarseBlockMatrix_of_isCoarseBlockMatrix ?_).symm
  refine ⟨isSymmetricBlockMat_coarseBlockMatrix U a, fun P => ?_⟩
  rw [← doubledMu_eq_Mu U a P]
  exact (doubledMuTheory U a).mu_quadratic P

/-! ## The localization lemma -/

/-- A domain is open and nonempty, hence of positive volume, so an
almost-everywhere hypothesis on it has at least one witness. -/
private theorem ae_neBot_volumeMeasureOn (U : Domain d) :
    (MeasureTheory.ae (volumeMeasureOn (U : Set (Vec d)))).NeBot := by
  refine MeasureTheory.ae_neBot.2 ?_
  have hpos : 0 < MeasureTheory.volume (U : Set (Vec d)) :=
    U.isOpen.measure_pos MeasureTheory.volume U.nonempty
  simpa only [ne_eq, MeasureTheory.Measure.restrict_eq_zero] using hpos.ne'

/-- The relative bound of the localization lemma is one-sided in `θ`: at
`r = h(x) p` its left-hand side is `2 |h(x) p|^2 ≥ 0`, while ellipticity makes
the bracket on its right-hand side positive at any `p ≠ 0`. Hence `0 ≤ θ` is a
consequence, not an assumption, whenever `Vec d` has a nonzero vector. -/
private theorem zero_le_of_ae_relSkewBound {U : Domain d} {a : CoeffOn U}
    {h : Vec d → Mat d} {θ : ℝ} {p : Vec d} (hp : p ≠ 0)
    (hbound : ∀ᵐ x ∂(volumeMeasureOn (U : Set (Vec d))), ∀ p r : Vec d,
      2 * vecDot r (matVecMul (h x) p) ≤
        θ * (vecDot p (matVecMul (symmPart (a.toCoeffField x)) p) +
          vecDot r (matVecMul (symmPart (a.toCoeffField x)) r))) :
    0 ≤ θ := by
  have := ae_neBot_volumeMeasureOn U
  obtain ⟨x, hboundx, hell⟩ := (hbound.and a.aeElliptic).exists
  have hkey := hboundx p (matVecMul (h x) p)
  have hzz : 0 ≤ vecDot (matVecMul (h x) p) (matVecMul (h x) p) :=
    vecNormSq_nonneg (matVecMul (h x) p)
  have hB : 0 < vecDot p (matVecMul (symmPart (a.toCoeffField x)) p) := by
    have h1 := hell.2.2.1 p
    rw [vecDot_matVecMul_symmPart] at h1
    have h2 : 0 < a.lam * vecNormSq p :=
      mul_pos hell.1 (lt_of_le_of_ne (vecNormSq_nonneg p)
        (fun hzero => hp (vecNormSq_eq_zero hzero.symm)))
    linarith only [h1, h2]
  have hC : 0 ≤ vecDot (matVecMul (h x) p)
      (matVecMul (symmPart (a.toCoeffField x)) (matVecMul (h x) p)) := by
    have h1 := hell.2.2.1 (matVecMul (h x) p)
    rw [vecDot_matVecMul_symmPart] at h1
    have h2 : 0 ≤ a.lam * vecNormSq (matVecMul (h x) p) :=
      mul_nonneg hell.1.le (vecNormSq_nonneg (matVecMul (h x) p))
    linarith only [h1, h2]
  by_contra hcon
  push Not at hcon
  have hneg : θ * (vecDot p (matVecMul (symmPart (a.toCoeffField x)) p) +
      vecDot (matVecMul (h x) p)
        (matVecMul (symmPart (a.toCoeffField x)) (matVecMul (h x) p))) < 0 :=
    mul_neg_of_neg_of_pos hcon (by linarith only [hB, hC])
  linarith only [hkey, hzz, hneg]

/-- In dimension zero every block vector is zero, so every block quadratic form
vanishes and the localization bounds below are equalities `0 = 0`. -/
private theorem blockVecDot_blockMatVecMul_eq_zero_of_subsingleton
    [Subsingleton (Vec d)] (M : BlockMat d) (X : BlockVec d) :
    blockVecDot X (blockMatVecMul M X) = 0 := by
  have hX : X = 0 := Subsingleton.elim X 0
  subst hX
  simp [blockVecDot, vecDot]

section Localization

variable {U : Domain d} {a b : CoeffOn U} {h : Vec d → Mat d} {θ : ℝ}

/-- The first display of `e.localize.matrix.bounds.in.lemma`:
`bfA(U; a + h) ≤ (1 + D) bfA(U; a)` as quadratic forms, with `D = θ (1 + θ)`.
The perturbation hypotheses are almost-everywhere statements on `U`, matching
the essential supremum of the printed `L^infinity(U)` bound. -/
theorem coarseBlockMatrix_add_skew_le
    (hb : ∀ᵐ x ∂(volumeMeasureOn (U : Set (Vec d))),
      b.toCoeffField x = a.toCoeffField x + h x)
    (hskew : ∀ᵐ x ∂(volumeMeasureOn (U : Set (Vec d))),
      matTranspose (h x) = -h x)
    (hbound : ∀ᵐ x ∂(volumeMeasureOn (U : Set (Vec d))), ∀ p r : Vec d,
      2 * vecDot r (matVecMul (h x) p) ≤
        θ * (vecDot p (matVecMul (symmPart (a.toCoeffField x)) p) +
          vecDot r (matVecMul (symmPart (a.toCoeffField x)) r)))
    (P : BlockVec d) :
    blockVecDot P (blockMatVecMul (Book.Ch02.coarseBlockMatrix U b) P) ≤
      (1 + θ * (1 + θ)) *
        blockVecDot P (blockMatVecMul (Book.Ch02.coarseBlockMatrix U a) P) := by
  rcases subsingleton_or_nontrivial (Vec d) with hsub | _
  · have := hsub
    simp only [blockVecDot_blockMatVecMul_eq_zero_of_subsingleton, mul_zero, le_refl]
  · obtain ⟨p, hp⟩ := exists_ne (0 : Vec d)
    have hθ : 0 ≤ θ := zero_le_of_ae_relSkewBound (a := a) (h := h) hp hbound
    refine blockVecDot_coarseBlockMatrix_le_of_ae a b ?_ P
    filter_upwards [a.aeElliptic, hb, hskew, hbound] with x hell hbx hskewx hboundx
    intro Y
    rw [hbx]
    exact blockQuadratic_add_skew_le hell hskewx hθ hboundx Y

/-- The flipped display `e.localize.matrix.bounds.in.lemma.flip`:
`bfA(U; a) ≤ (1 + D) bfA(U; a + h)`. -/
theorem coarseBlockMatrix_le_add_skew
    (hb : ∀ᵐ x ∂(volumeMeasureOn (U : Set (Vec d))),
      b.toCoeffField x = a.toCoeffField x + h x)
    (hskew : ∀ᵐ x ∂(volumeMeasureOn (U : Set (Vec d))),
      matTranspose (h x) = -h x)
    (hbound : ∀ᵐ x ∂(volumeMeasureOn (U : Set (Vec d))), ∀ p r : Vec d,
      2 * vecDot r (matVecMul (h x) p) ≤
        θ * (vecDot p (matVecMul (symmPart (a.toCoeffField x)) p) +
          vecDot r (matVecMul (symmPart (a.toCoeffField x)) r)))
    (P : BlockVec d) :
    blockVecDot P (blockMatVecMul (Book.Ch02.coarseBlockMatrix U a) P) ≤
      (1 + θ * (1 + θ)) *
        blockVecDot P (blockMatVecMul (Book.Ch02.coarseBlockMatrix U b) P) := by
  rcases subsingleton_or_nontrivial (Vec d) with hsub | _
  · have := hsub
    simp only [blockVecDot_blockMatVecMul_eq_zero_of_subsingleton, mul_zero, le_refl]
  · obtain ⟨p, hp⟩ := exists_ne (0 : Vec d)
    have hθ : 0 ≤ θ := zero_le_of_ae_relSkewBound (a := a) (h := h) hp hbound
    refine blockVecDot_coarseBlockMatrix_le_of_ae b a ?_ P
    filter_upwards [b.aeElliptic, hb, hskew, hbound] with x hell hbx hskewx hboundx
    intro Y
    rw [hbx] at hell
    have hle := blockQuadratic_le_blockQuadratic_add_skew hell hskewx hθ hboundx Y
    rwa [← hbx] at hle

/-- The ratio bound in the block Loewner order. This is the form the marginal
paper applies at the infrared cutoffs. -/
theorem coarseBlockMatrix_blockMatLoewnerLE_smul
    (hb : ∀ᵐ x ∂(volumeMeasureOn (U : Set (Vec d))),
      b.toCoeffField x = a.toCoeffField x + h x)
    (hskew : ∀ᵐ x ∂(volumeMeasureOn (U : Set (Vec d))),
      matTranspose (h x) = -h x)
    (hbound : ∀ᵐ x ∂(volumeMeasureOn (U : Set (Vec d))), ∀ p r : Vec d,
      2 * vecDot r (matVecMul (h x) p) ≤
        θ * (vecDot p (matVecMul (symmPart (a.toCoeffField x)) p) +
          vecDot r (matVecMul (symmPart (a.toCoeffField x)) r))) :
    BlockMatLoewnerLE (Book.Ch02.coarseBlockMatrix U b)
      ((1 + θ * (1 + θ)) • Book.Ch02.coarseBlockMatrix U a) := by
  intro X
  rw [blockMatVecMul_blockSMul, blockVecDot_smul_right]
  have hfwd := coarseBlockMatrix_add_skew_le hb hskew hbound X
  linarith only [hfwd]

private theorem one_sub_mul_le_of_le {Qa Qb D : ℝ} (hQa : 0 ≤ Qa)
    (hQb : 0 ≤ Qb) (hle : Qa ≤ (1 + D) * Qb) :
    (1 - D) * Qa ≤ Qb := by
  rcases le_or_gt D 1 with hD1 | hD1
  · have h1 : (1 - D) * Qa ≤ (1 - D) * ((1 + D) * Qb) :=
      mul_le_mul_of_nonneg_left hle (by linarith only [hD1])
    have h2 : (1 - D) * ((1 + D) * Qb) = (1 - D ^ 2) * Qb := by ring
    have h3 : (1 - D ^ 2) * Qb ≤ 1 * Qb :=
      mul_le_mul_of_nonneg_right (by linarith only [sq_nonneg D]) hQb
    linarith only [h1, h2, h3]
  · have h1 : (0 : ℝ) ≤ (D - 1) * Qa :=
      mul_nonneg (by linarith only [hD1]) hQa
    linarith only [h1, hQb]

/-- **Localization of `bfA`**, the lemma `l.localization.A` of
the paper:

`-D bfA(U; a) ≤ bfA(U; a + h) - bfA(U; a) ≤ D bfA(U; a)` with `D = θ (1 + θ)`,

for any `θ` bounding `‖s^{-1/2} h s^{-1/2}‖` on `U` in the sense of
`hbound`, which already forces `0 ≤ θ` in positive dimension. The difference of block matrices is formed on the `2d`-by-`2d`
coordinate carrier, where `CoarseGraining` provides the quadratic-form
identity `blockVecDot_blockMatVecMul_ofFullBlockMat_sub`. -/
theorem coarseBlockMatrix_localization
    (hb : ∀ᵐ x ∂(volumeMeasureOn (U : Set (Vec d))),
      b.toCoeffField x = a.toCoeffField x + h x)
    (hskew : ∀ᵐ x ∂(volumeMeasureOn (U : Set (Vec d))),
      matTranspose (h x) = -h x)
    (hbound : ∀ᵐ x ∂(volumeMeasureOn (U : Set (Vec d))), ∀ p r : Vec d,
      2 * vecDot r (matVecMul (h x) p) ≤
        θ * (vecDot p (matVecMul (symmPart (a.toCoeffField x)) p) +
          vecDot r (matVecMul (symmPart (a.toCoeffField x)) r))) :
    BlockMatLoewnerLE ((-(θ * (1 + θ))) • Book.Ch02.coarseBlockMatrix U a)
        (ofFullBlockMat (toFullBlockMat (Book.Ch02.coarseBlockMatrix U b) -
          toFullBlockMat (Book.Ch02.coarseBlockMatrix U a))) ∧
      BlockMatLoewnerLE
        (ofFullBlockMat (toFullBlockMat (Book.Ch02.coarseBlockMatrix U b) -
          toFullBlockMat (Book.Ch02.coarseBlockMatrix U a)))
        ((θ * (1 + θ)) • Book.Ch02.coarseBlockMatrix U a) := by
  constructor
  · intro X
    rw [blockMatVecMul_blockSMul, blockVecDot_smul_right,
      blockVecDot_blockMatVecMul_ofFullBlockMat_sub]
    have hrev := coarseBlockMatrix_le_add_skew hb hskew hbound X
    have hQa := zero_le_blockVecDot_coarseBlockMatrix U a X
    have hQb := zero_le_blockVecDot_coarseBlockMatrix U b X
    have hkey := one_sub_mul_le_of_le hQa hQb hrev
    linarith only [hkey]
  · intro X
    rw [blockMatVecMul_blockSMul, blockVecDot_smul_right,
      blockVecDot_blockMatVecMul_ofFullBlockMat_sub]
    have hfwd := coarseBlockMatrix_add_skew_le hb hskew hbound X
    linarith only [hfwd]

end Localization

/-! ## The scalar-symmetric-part corollary used at the infrared cutoffs -/

section Scalar

variable {U : Domain d} {a b : CoeffOn U} {h : Vec d → Mat d} {ν M : ℝ}

/-- The two-sided scalar form of `l.localization.A`. -/
theorem coarseBlockMatrix_localization_scalar_two_sided
    (hν : 0 < ν) (hM : 0 ≤ M)
    (hs : ∀ᵐ x ∂(volumeMeasureOn (U : Set (Vec d))),
      symmPart (a.toCoeffField x) = ν • (1 : Mat d))
    (hb : ∀ᵐ x ∂(volumeMeasureOn (U : Set (Vec d))),
      b.toCoeffField x = a.toCoeffField x + h x)
    (hskew : ∀ᵐ x ∂(volumeMeasureOn (U : Set (Vec d))),
      matTranspose (h x) = -h x)
    (hnorm : ∀ᵐ x ∂(volumeMeasureOn (U : Set (Vec d))), ∀ w : Vec d,
      vecNormSq (matVecMul (h x) w) ≤ M ^ 2 * vecNormSq w) :
    BlockMatLoewnerLE
        ((-(ν⁻¹ * M + ν⁻¹ ^ 2 * M ^ 2)) • Book.Ch02.coarseBlockMatrix U a)
        (ofFullBlockMat (toFullBlockMat (Book.Ch02.coarseBlockMatrix U b) -
          toFullBlockMat (Book.Ch02.coarseBlockMatrix U a))) ∧
      BlockMatLoewnerLE
        (ofFullBlockMat (toFullBlockMat (Book.Ch02.coarseBlockMatrix U b) -
          toFullBlockMat (Book.Ch02.coarseBlockMatrix U a)))
        ((ν⁻¹ * M + ν⁻¹ ^ 2 * M ^ 2) • Book.Ch02.coarseBlockMatrix U a) := by
  have hbound : ∀ᵐ x ∂(volumeMeasureOn (U : Set (Vec d))), ∀ p r : Vec d,
      2 * vecDot r (matVecMul (h x) p) ≤
        (ν⁻¹ * M) * (vecDot p (matVecMul (symmPart (a.toCoeffField x)) p) +
          vecDot r (matVecMul (symmPart (a.toCoeffField x)) r)) := by
    filter_upwards [hs, hnorm] with x hsx hnormx
    intro p r
    exact relSkewBound_of_symmPart_eq_smul_one hν hM hsx hnormx p r
  have hconst : (ν⁻¹ * M) * (1 + ν⁻¹ * M) = ν⁻¹ * M + ν⁻¹ ^ 2 * M ^ 2 := by ring
  have hmain := coarseBlockMatrix_localization hb hskew hbound
  rwa [hconst] at hmain

end Scalar

end

end SuperdiffusionCLT.Section2.Localization

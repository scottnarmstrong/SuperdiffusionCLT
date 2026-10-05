/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Localization.Conj3EndgameSkewFree

/-!
# The third conjunct, without the constant-loading half

A route to the third conjunct that replaces the volume average of a pairing by a
pairing of volume averages would need the identity `⍍_U pointwiseResponse = ResponseJ`;
the paper never makes that replacement, and the identity is
not available in general.

The printed argument does something else.  Its `η²` term is `C η² P·𝐀(U;ã)P`, and
`P·𝐀(U;ã)P` is, by `e.minimizers.energy.vs.bfA`, the *perturbed
minimizer's own averaged block energy* `‖Ã^{1/2}Z̃‖²_{L²(U)}`, which
`e.Jaas.matform` turns into `2 (J(U,p,q;ã) + p·q)`.  The volume
average of the *pointwise constant-loading* quadratic never appears in the printed
argument.  An averaged remainder read at that
average would be strictly weaker than the printed display, because the
constant loading dominates the minimizer's energy (the printed half of
`e.CG.bounds.2`); passing between the two directions is exactly the identity above.

This module avoids the identity: the absorption engine
`averagedRemainderOn_le_of_skewShift_energy` reads the `η²` estimate at an
*arbitrary* energy density, and `conj3PureSkewPiece_quadraticBound_minimizerEnergy`
instantiates it at the perturbed minimizer's own block energy, which is
`2 (R_pert + p·q)` by the entry points of `SlopeBoundRoute`.  The
deterministic chain is then the absorption the print performs, so no coarse-average
identity and no response half is needed.  At `p ≠ 0`, `m < L` and `d ≥ 2` the
loading `(-p, q)` is nonzero and the minimizer-energy form is inhabited on the cube
domain, so nothing below collapses to `True`; the binders `[NeZero d]` and
`2 ≤ d` of the statement are carried verbatim, and dimension one is out of scope.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section2.Localization

open Homogenization
open Homogenization.Book.Ch02
open Homogenization.IndependentSums
open MeasureTheory
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Probability
open SuperdiffusionCLT.Section2.Cutoff
open scoped BigOperators

noncomputable section

variable {d : ℕ}

/-! ## The pointwise absorption at `symmPart A = ν Id`

The printed `η²` absorption is pointwise: at `s = symmPart A` the block form is
`x·s x + (y − k x)·s⁻¹(y − k x)`, so the skew image `y = H x` is charged to
`θ² x·s x`.  These four lemmas are the printed estimate's chain, stated here because
the engine below needs them at the energy density of a minimizer rather than at a
constant loading. -/

private theorem vecDot_matVecMul_comm_of_symm_endgame {S : Mat d}
    (hS : matTranspose S = S) (x y : Vec d) :
    vecDot x (matVecMul S y) = vecDot y (matVecMul S x) := by
  calc
    vecDot x (matVecMul S y) = vecDot x (matVecMul (matTranspose S) y) := by
      rw [hS]
    _ = vecDot (matVecMul S x) y := vecDot_matVecMul_transpose x y S
    _ = vecDot y (matVecMul S x) := vecDot_comm _ _

private theorem symmPart_inv_symm_endgame (A : Mat d) :
    matTranspose ((symmPart A)⁻¹) = (symmPart A)⁻¹ := by
  have h : Matrix.transpose ((symmPart A)⁻¹) = (Matrix.transpose (symmPart A))⁻¹ :=
    Matrix.transpose_nonsing_inv (symmPart A)
  have h2 : Matrix.transpose (symmPart A) = symmPart A := matTranspose_symmPart A
  rw [matTranspose, h, h2]

private theorem symmPart_mul_inv_vec_endgame {A : Mat d} {lam Lam : ℝ}
    (hA : IsEllipticMatrix lam Lam A) (v : Vec d) :
    matVecMul (symmPart A) (matVecMul ((symmPart A)⁻¹) v) = v := by
  have hunit : IsUnit (symmPart A).det :=
    (Matrix.isUnit_iff_isUnit_det (A := symmPart A)).mp
      (isUnit_symmPart_of_isEllipticMatrix hA)
  rw [matVecMul_mul, Matrix.mul_nonsing_inv _ hunit, matVecMul_one]

/-- **The skew image is charged at `θ²`.**  If `2 r·(H p) ≤ θ (p·s p + r·s r)`
pointwise then `(H p)·s⁻¹(H p) ≤ θ² p·s p`
(the printed estimate, reproduced file-locally). -/
private theorem image_symmPartInv_le_of_relSkewBound_remainder
    {A H : Mat d} {lam Lam theta : ℝ}
    (hA : IsEllipticMatrix lam Lam A) (htheta : 0 ≤ theta)
    (hbound : ∀ p r : Vec d,
      2 * vecDot r (matVecMul H p) ≤
        theta * (vecDot p (matVecMul (symmPart A) p) +
          vecDot r (matVecMul (symmPart A) r)))
    (p : Vec d) :
    vecDot (matVecMul H p) (matVecMul ((symmPart A)⁻¹) (matVecMul H p)) ≤
      theta ^ 2 * vecDot p (matVecMul (symmPart A) p) := by
  set B := vecDot p (matVecMul (symmPart A) p)
  set z := matVecMul H p
  set D := vecDot z (matVecMul ((symmPart A)⁻¹) z)
  have hInvSymm : matTranspose ((symmPart A)⁻¹) = (symmPart A)⁻¹ :=
    symmPart_inv_symm_endgame A
  have hDnonneg : 0 ≤ D := symmPart_inv_nonneg_of_isEllipticMatrix hA z
  have hkey : ∀ t : ℝ, 2 * t * D ≤ theta * (B + t ^ 2 * D) := by
    intro t
    have h := hbound p (t • matVecMul ((symmPart A)⁻¹) z)
    have hleft : vecDot (t • matVecMul ((symmPart A)⁻¹) z) z = t * D := by
      rw [vecDot_smul_left, vecDot_comm,
        vecDot_matVecMul_comm_of_symm_endgame hInvSymm z z]
    have hright :
        vecDot (t • matVecMul ((symmPart A)⁻¹) z)
            (matVecMul (symmPart A) (t • matVecMul ((symmPart A)⁻¹) z)) =
          t ^ 2 * D := by
      rw [matVecMul_smul, vecDot_smul_left, vecDot_smul_right,
        symmPart_mul_inv_vec_endgame hA z, vecDot_comm,
        vecDot_matVecMul_comm_of_symm_endgame hInvSymm z z]
      ring
    rw [hleft, hright] at h
    linarith only [h]
  rcases eq_or_lt_of_le htheta with hzero | hpos
  · have h := hkey 1
    rw [← hzero] at h
    have hDle : D ≤ 0 := by linarith only [h]
    have hright : theta ^ 2 * B = 0 := by rw [← hzero]; ring
    linarith only [hDle, hright, hDnonneg]
  · have h := hkey theta⁻¹
    have hinv : theta * (theta⁻¹) ^ 2 = theta⁻¹ := by field_simp
    rw [mul_add, ← mul_assoc, hinv] at h
    have h1 : theta⁻¹ * D ≤ theta * B := by linarith only [h]
    have h2 : theta * (theta⁻¹ * D) ≤ theta * (theta * B) :=
      mul_le_mul_of_nonneg_left h1 hpos.le
    have h3 : theta * (theta⁻¹ * D) = D := by field_simp
    have h4 : theta * (theta * B) = theta ^ 2 * B := by ring
    rw [h3, h4] at h2
    exact h2

/-! ## The absorption engine at an arbitrary energy density -/

/-- **The averaged absorption engine, read at an arbitrary energy density.**  This
is the averaged remainder estimate with the constant loading
`⍍_U P·ã(x)P` replaced by `⍍_U W`; the printed display names the minimizer's own
energy there. -/
theorem averagedRemainderOn_le_of_skewShift_energy {U : Set (Vec d)}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    {A H : Vec d → Mat d} {Y : Vec d → BlockVec d} {r : Vec d → Vec d}
    {W : Vec d → ℝ} {eta theta : ℝ}
    (hU : MeasurableSet U)
    (hA : ∀ x ∈ U, ∃ lam Lam : ℝ, IsEllipticMatrix lam Lam (A x))
    (htheta : 0 ≤ theta) (hthetaEta : theta ≤ eta)
    (hbound : ∀ x ∈ U, ∀ p r : Vec d,
      2 * vecDot r (matVecMul (H x) p) ≤
        theta * (vecDot p (matVecMul (symmPart (A x)) p) +
          vecDot r (matVecMul (symmPart (A x)) r)))
    (hY : ∀ x ∈ U, Y x = ((0 : Vec d), matVecMul (H x) (r x)))
    (hIntY : MeasureTheory.IntegrableOn
      (fun x => averagedBlockQuadratic (A x) (Y x)) U)
    (hIntS : MeasureTheory.IntegrableOn
      (fun x => vecDot (r x) (matVecMul (symmPart (A x)) (r x))) U)
    (hWnn : ∀ x ∈ U, 0 ≤ W x)
    (henergy : volumeAverage U
        (fun x => vecDot (r x) (matVecMul (symmPart (A x)) (r x))) ≤
      volumeAverage U W) :
    averagedBlockQuadraticOn U A Y ≤ eta * eta * volumeAverage U W := by
  have hpoint : ∀ x ∈ U, averagedBlockQuadratic (A x) (Y x) ≤
      theta ^ 2 * vecDot (r x) (matVecMul (symmPart (A x)) (r x)) := by
    intro x hx
    obtain ⟨lam, Lam, hAx⟩ := hA x hx
    rw [hY x hx]
    have him := image_symmPartInv_le_of_relSkewBound_remainder hAx htheta (hbound x hx) (r x)
    have hform := blockMatrixOfCoeff_quadratic_eq (A x) (0 : Vec d) (matVecMul (H x) (r x))
    have hleft : averagedBlockQuadratic (A x) ((0 : Vec d), matVecMul (H x) (r x)) =
        vecDot (matVecMul (H x) (r x))
          (matVecMul ((symmPart (A x))⁻¹) (matVecMul (H x) (r x))) := by
      simpa only [averagedBlockQuadratic, matVecMul_zero, vecDot_zero_left, sub_zero, zero_add] using hform
    rw [hleft]
    exact him
  have hmono := volumeAverage_le_volumeAverage_of_le_on hU hIntY
    (hIntS.const_mul (theta ^ 2)) hpoint
  have hscale : volumeAverage U
      (fun x => theta ^ 2 * vecDot (r x) (matVecMul (symmPart (A x)) (r x))) =
      theta ^ 2 * volumeAverage U
        (fun x => vecDot (r x) (matVecMul (symmPart (A x)) (r x))) := by
    rw [show (fun x => theta ^ 2 * vecDot (r x) (matVecMul (symmPart (A x)) (r x))) =
        theta ^ 2 • (fun x => vecDot (r x) (matVecMul (symmPart (A x)) (r x))) by
          funext x
          simp]
    rw [volumeAverage_smul]
  have hWNN : 0 ≤ volumeAverage U W := volumeAverage_nonneg_of_nonneg_on hU hWnn
  have hsq : theta ^ 2 ≤ eta ^ 2 := by
    simpa only [pow_two] using mul_self_le_mul_self htheta hthetaEta
  calc
    averagedBlockQuadraticOn U A Y ≤
        volumeAverage U (fun x => theta ^ 2 *
          vecDot (r x) (matVecMul (symmPart (A x)) (r x))) := hmono
    _ = theta ^ 2 * volumeAverage U
          (fun x => vecDot (r x) (matVecMul (symmPart (A x)) (r x))) := hscale
    _ ≤ theta ^ 2 * volumeAverage U W := mul_le_mul_of_nonneg_left henergy (sq_nonneg theta)
    _ ≤ eta ^ 2 * volumeAverage U W := mul_le_mul_of_nonneg_right hsq hWNN
    _ = eta * eta * volumeAverage U W := by rw [pow_two]

/-! ## The route's `L²` bookkeeping -/

/-- The potential slot of an admissible doubled field is `L²`. -/
private theorem memVectorL2_potential_of_doubledAdmissible {U : Book.Ch02.Domain d}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn (U : Set (Vec d)))]
    {P : BlockVec d} {X : Book.Ch02.DoubledField d}
    (hX : Book.Ch02.IsDoubledMuAdmissible U P X) :
    MemVectorL2 (U : Set (Vec d)) (fun x => X.potential x) := by
  have h := (MeasureTheory.memLp_const (μ := volumeMeasureOn (U : Set (Vec d)))
    (c := P.1) (p := 2)).add hX.1.1
  have heq : ((fun _ : Vec d => P.1) + fun x => X.potential x - P.1) =
      (fun x : Vec d => X.potential x) := by
    funext x
    simp only [Pi.add_apply]
    abel
  rwa [heq] at h

/-- The block field of an admissible doubled field is `L²`. -/
private theorem memBlockL2_eval_of_doubledAdmissible {U : Book.Ch02.Domain d}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn (U : Set (Vec d)))]
    {P : BlockVec d} {X : Book.Ch02.DoubledField d}
    (hX : Book.Ch02.IsDoubledMuAdmissible U P X) :
    MemBlockL2 (U : Set (Vec d)) (fun x => X.eval x) := by
  have hp := memVectorL2_potential_of_doubledAdmissible hX
  have hq : MemVectorL2 (U : Set (Vec d)) (fun x => X.flux x) := by
    have h := (MeasureTheory.memLp_const (μ := volumeMeasureOn (U : Set (Vec d)))
      (c := P.2) (p := 2)).add hX.2.1
    have heq : ((fun _ : Vec d => P.2) + fun x => X.flux x - P.2) =
        (fun x : Vec d => X.flux x) := by
      funext x
      simp only [Pi.add_apply]
      abel
    rwa [heq] at h
  exact memBlockL2_blockField hp hq

/-! ## `henergy` at the minimizer's own energy -/

/-- **The averaged `s`-energy of the shift is at most the perturbed minimizer's own
averaged block energy.**  This is the last printed line of the proof of
`e.minimizers.gradient.from.block` read at the minimizer, not at the constant
loading: at `s = ν Id` the block form dominates the potential `s`-energy, and the
perturbed doubled field is a doubled minimizer, hence admissible and `L²`. -/
theorem symmEnergy_average_le_minimizerEnergy_centeredPair (U : Book.Ch02.Domain d)
    (nu : ℝ) (hnu : 0 < nu) (omega : ShellSeq d) (m L : ℕ) (hmL : m ≤ L) (p q : Vec d)
    (u : AHarmonicFunction (centeredPairField nu omega m L (U : Set (Vec d)))
      (U : Set (Vec d)))
    (hu : Homogenization.IsResponseMaximizer (U : Set (Vec d)) p q
      (centeredPairField nu omega m L (U : Set (Vec d))) u) :
    volumeAverage (U : Set (Vec d)) (fun x => vecDot
        ((routeDoubledFieldL U nu hnu omega m L hmL p q u).potential x)
        (matVecMul (symmPart ((coefficientCutoff nu omega m).toCoeffField x))
          ((routeDoubledFieldL U nu hnu omega m L hmL p q u).potential x))) ≤
      volumeAverage (U : Set (Vec d)) (fun x => averagedBlockQuadratic
        (centeredPairField nu omega m L (U : Set (Vec d)) x)
        ((routeDoubledFieldL U nu hnu omega m L hmL p q u).eval x)) := by
  have hZt : Book.Ch02.IsDoubledMuMinimizer U (centeredPairCoeffOn U nu hnu omega m L hmL)
      (-p, q) (routeDoubledFieldL U nu hnu omega m L hmL p q u) :=
    doubledFieldOfScalarMaximizers_isDoubledMuMinimizer
      (centeredPairCoeffOn U nu hnu omega m L hmL) p q u
      (transposeResponseMaximizer U (centeredPairCoeffOn U nu hnu omega m L hmL) p (-q)) hu
      (transposeResponseMaximizer_isMaximizer U (centeredPairCoeffOn U nu hnu omega m L hmL)
        p (-q))
  have hr : MemVectorL2 (U : Set (Vec d))
      (fun x => (routeDoubledFieldL U nu hnu omega m L hmL p q u).potential x) :=
    memVectorL2_potential_of_doubledAdmissible hZt.1
  have hIntL : IntegrableOn (fun x => nu * vecNormSq
      ((routeDoubledFieldL U nu hnu omega m L hmL p q u).potential x))
      (U : Set (Vec d)) := by
    exact (integrableOn_vecDot_of_memVectorL2 hr hr).const_mul nu
  have hZtmem : MemBlockL2 (U : Set (Vec d))
      (fun x => (routeDoubledFieldL U nu hnu omega m L hmL p q u).eval x) :=
    memBlockL2_eval_of_doubledAdmissible hZt.1
  have hIntZt : IntegrableOn (fun x => averagedBlockQuadratic
      (centeredPairField nu omega m L (U : Set (Vec d)) x)
      ((routeDoubledFieldL U nu hnu omega m L hmL p q u).eval x)) (U : Set (Vec d)) :=
    integrableOn_averagedBlockQuadratic_of_memBlockL2
      (centeredPairCoeffOn U nu hnu omega m L hmL) hZtmem
  have hpoint : ∀ x ∈ (U : Set (Vec d)), nu * vecNormSq
      ((routeDoubledFieldL U nu hnu omega m L hmL p q u).potential x) ≤
      averagedBlockQuadratic (centeredPairField nu omega m L (U : Set (Vec d)) x)
        ((routeDoubledFieldL U nu hnu omega m L hmL p q u).eval x) := by
    intro x hx
    exact symmEnergy_le_averagedBlockQuadratic
      (isEllipticMatrix_centeredPairField_domain U nu hnu omega m L hmL x hx)
      (symmPart_centeredPairField_eq_smul_one nu omega m L (U : Set (Vec d)) x)
      ((routeDoubledFieldL U nu hnu omega m L hmL p q u).eval x)
  have hmono := volumeAverage_le_volumeAverage_of_le_on U.measurableSet hIntL hIntZt hpoint
  have hfun : (fun x => vecDot
        ((routeDoubledFieldL U nu hnu omega m L hmL p q u).potential x)
        (matVecMul (symmPart ((coefficientCutoff nu omega m).toCoeffField x))
          ((routeDoubledFieldL U nu hnu omega m L hmL p q u).potential x))) =
      (fun x => nu * vecNormSq
        ((routeDoubledFieldL U nu hnu omega m L hmL p q u).potential x)) := by
    funext x
    have hsymm : symmPart ((coefficientCutoff nu omega m).toCoeffField x) =
        nu • (1 : Mat d) := symmPart_coefficientCutoff nu omega m x
    rw [hsymm]
    exact vecDot_smul_one_self nu _
  rw [hfun]
  exact hmono

/-! ## (Q1) at the minimizer's own energy -/

/-- **(Q1) at the perturbed minimizer's own energy.**  The averaged block quadratic
of the pure-skew piece `Z̃₁` at the base field is at most `η²` times the averaged
block energy of the perturbed doubled minimizer `Z̃` itself.  All four printed
inputs (`hbound`, `hIntR`, `hIntS`, `henergy`) are discharged from the data of the statement,
and the engine is read at the minimizer's density.  Reading the volume
average of the pointwise *constant-loading* quadratic there would give a display
that is strictly larger, so the form below is strictly stronger. -/
theorem conj3PureSkewPiece_quadraticBound_minimizerEnergy {d : ℕ} (U : Book.Ch02.Domain d)
    (nu : ℝ) (hnu : 0 < nu) (omega : ShellSeq d) (n m L : ℕ) (hmL : m ≤ L)
    (hU : (U : Set (Vec d)) ⊆ openCubeSet (originCube d (n : ℤ))) (p q : Vec d)
    (u : AHarmonicFunction (centeredPairField nu omega m L (U : Set (Vec d))) (U : Set (Vec d)))
    (hu : Homogenization.IsResponseMaximizer (U : Set (Vec d)) p q
      (centeredPairField nu omega m L (U : Set (Vec d))) u) :
    averagedBlockQuadraticOn (U : Set (Vec d))
        (fun x => (coefficientCutoff nu omega m).toCoeffField x)
        (conj3PureSkewPiece U nu hnu omega m L hmL p q u) ≤
      cutoffPairEtaWindow d nu n m L omega * cutoffPairEtaWindow d nu n m L omega *
        averagedBlockQuadraticOn (U : Set (Vec d))
          (fun x => centeredPairField nu omega m L (U : Set (Vec d)) x)
          (fun x => (routeDoubledFieldL U nu hnu omega m L hmL p q u).eval x) := by
  have h := averagedRemainderOn_le_of_skewShift_energy
    (U := (U : Set (Vec d)))
    (A := fun x => (coefficientCutoff nu omega m).toCoeffField x)
    (H := conj3SkewRemainderField nu omega m L (U : Set (Vec d)))
    (Y := conj3PureSkewPiece U nu hnu omega m L hmL p q u)
    (r := fun x => (routeDoubledFieldL U nu hnu omega m L hmL p q u).potential x)
    (W := fun x => averagedBlockQuadratic
      (centeredPairField nu omega m L (U : Set (Vec d)) x)
      ((routeDoubledFieldL U nu hnu omega m L hmL p q u).eval x))
    (eta := cutoffPairEtaWindow d nu n m L omega)
    (theta := cutoffPairThetaWindow d nu n m L omega)
    U.measurableSet
    (fun x hx => ⟨nu, _, isEllipticMatrix_coefficientCutoff_domain U nu hnu omega m x hx⟩)
    (cutoffPairThetaWindow_nonneg nu hnu n m L omega)
    (cutoffPairThetaWindow_le_etaWindow nu hnu n m L omega)
    (hbound_centeredCutoffPair_window U nu hnu omega n m L hmL hU)
    (fun _ _ => rfl)
    (hIntR_centeredCutoffPair_window U nu hnu omega m L hmL p q u hu)
    (hIntS_centeredCutoffPair_window U nu hnu omega m L hmL p q u hu)
    (fun x hx => blockVecDot_blockMatrixOfCoeff_nonneg
      (isEllipticMatrix_centeredPairField_domain U nu hnu omega m L hmL x hx) _)
    (symmEnergy_average_le_minimizerEnergy_centeredPair U nu hnu omega m L hmL p q u hu)
  simpa only [averagedBlockQuadraticOn] using h

/-! ## The deterministic chain at the minimizer energies -/

/-- **The printed chain at the minimizer energies**:
`⍍ A(Z−Z̃₀)·(Z−Z̃₀) ≤ 2η (⍍ Z·Z_{a_m} + ⍍ Zt·Zt_{ã}) + 2η² ⍍ Zt·Zt_{ã}`, from the
printed bridge `conj3GradientFromBlock_cutoff`, the linear display (L1) at the
minimizers' own energies (`conj3ShiftedPairLinearMin_cutoff`) and (Q1) at the
perturbed minimizer's own energy.  Both energy slots on the right are the
minimizers' own averaged block energies; the constant loading does not occur. -/
theorem conj3DeterministicFromBlock_min_cutoff_minimizerEnergy {d : ℕ}
    (U : Book.Ch02.Domain d) (nu : ℝ) (hnu : 0 < nu) (omega : ShellSeq d) (n m L : ℕ)
    (hmL : m < L) (hU : (U : Set (Vec d)) ⊆ openCubeSet (originCube d (n : ℤ))) (p q : Vec d)
    (v : AHarmonicFunction (coefficientCutoff nu omega m).toCoeffField (U : Set (Vec d)))
    (hv : Homogenization.IsResponseMaximizer (U : Set (Vec d)) p q
      (coefficientCutoff nu omega m).toCoeffField v)
    (u : AHarmonicFunction (centeredPairField nu omega m L (U : Set (Vec d)))
      (U : Set (Vec d)))
    (hu : Homogenization.IsResponseMaximizer (U : Set (Vec d)) p q
      (centeredPairField nu omega m L (U : Set (Vec d))) u) :
    averagedBlockQuadraticOn (U : Set (Vec d))
        (fun x => (coefficientCutoff nu omega m).toCoeffField x)
        (conj3SkewFreeDifference U nu hnu omega m L hmL.le p q v u) ≤
      2 * (cutoffPairEtaWindow d nu n m L omega *
            (averagedBlockQuadraticOn (U : Set (Vec d))
                (fun x => (coefficientCutoff nu omega m).toCoeffField x)
                (fun x => (routeDoubledFieldM U nu hnu omega m p q v).eval x) +
              averagedBlockQuadraticOn (U : Set (Vec d))
                (fun x => centeredPairField nu omega m L (U : Set (Vec d)) x)
                (fun x => (routeDoubledFieldL U nu hnu omega m L hmL.le p q u).eval x))) +
      2 * (cutoffPairEtaWindow d nu n m L omega * cutoffPairEtaWindow d nu n m L omega *
            averagedBlockQuadraticOn (U : Set (Vec d))
              (fun x => centeredPairField nu omega m L (U : Set (Vec d)) x)
              (fun x => (routeDoubledFieldL U nu hnu omega m L hmL.le p q u).eval x)) := by
  have hbridge := conj3GradientFromBlock_cutoff U nu hnu omega m L hmL.le p q v hv u hu
  have hL1 := conj3ShiftedPairLinearMin_cutoff U nu hnu omega n m L hmL.le hU p q v hv u hu
  have hQ1 := conj3PureSkewPiece_quadraticBound_minimizerEnergy U nu hnu omega n m L hmL.le
    hU p q u hu
  have hDnn : (0 : ℝ) ≤ averagedBlockQuadraticOn (U : Set (Vec d))
      (fun x => centeredPairField nu omega m L (U : Set (Vec d)) x)
      (conj3ShiftedPairRemainder U nu hnu omega m L hmL.le p q v u) :=
    averagedBlockQuadraticOn_nonneg_of_elliptic (U := (U : Set (Vec d)))
      (A := fun x => centeredPairField nu omega m L (U : Set (Vec d)) x) U.measurableSet
      (fun x hx => isEllipticMatrix_centeredPairField_domain U nu hnu omega m L hmL.le x hx)
      (X := conj3ShiftedPairRemainder U nu hnu omega m L hmL.le p q v u)
  linarith only [hbridge, hL1, hQ1, hDnn]

/-! ## The response bracket is half the minimizer-energy sum -/

/-- **The response bracket is `½` of the two minimizers' energies.**  At the two route
doubled fields the sum of their averaged block energies is exactly
`2 (R_pert + R_base + 2 p·q)`: `e.minimizers.energy.vs.bfA` composed with
`e.Jaas.matform` at the route's own carriers.  The only inputs are
the two maximalities. -/
theorem minimizerEnergySum_eq_frozenRHS {d : ℕ} (U : Book.Ch02.Domain d) (nu : ℝ)
    (hnu : 0 < nu) (omega : ShellSeq d) (m L : ℕ) (hmL : m ≤ L) (p q : Vec d)
    (v : AHarmonicFunction (coefficientCutoff nu omega m).toCoeffField (U : Set (Vec d)))
    (hv : Homogenization.IsResponseMaximizer (U : Set (Vec d)) p q
      (coefficientCutoff nu omega m).toCoeffField v)
    (u : AHarmonicFunction (centeredPairField nu omega m L (U : Set (Vec d)))
      (U : Set (Vec d)))
    (hu : Homogenization.IsResponseMaximizer (U : Set (Vec d)) p q
      (centeredPairField nu omega m L (U : Set (Vec d))) u) :
    averagedBlockQuadraticOn (U : Set (Vec d))
        (fun x => (coefficientCutoff nu omega m).toCoeffField x)
        (fun x => (routeDoubledFieldM U nu hnu omega m p q v).eval x) +
      averagedBlockQuadraticOn (U : Set (Vec d))
        (fun x => centeredPairField nu omega m L (U : Set (Vec d)) x)
        (fun x => (routeDoubledFieldL U nu hnu omega m L hmL p q u).eval x) =
      2 * (ResponseJ (U : Set (Vec d)) p q
            (centeredPairField nu omega m L (U : Set (Vec d))) +
          ResponseJ (U : Set (Vec d)) p q (coefficientCutoff nu omega m).toCoeffField +
          2 * vecDot p q) := by
  have hZ : Book.Ch02.IsDoubledMuMinimizer U (levelMCoeffOn U nu hnu omega m) (-p, q)
      (routeDoubledFieldM U nu hnu omega m p q v) :=
    doubledFieldOfScalarMaximizers_isDoubledMuMinimizer (levelMCoeffOn U nu hnu omega m) p q v
      (transposeResponseMaximizer U (levelMCoeffOn U nu hnu omega m) p (-q)) hv
      (transposeResponseMaximizer_isMaximizer U (levelMCoeffOn U nu hnu omega m) p (-q))
  have hZt : Book.Ch02.IsDoubledMuMinimizer U (centeredPairCoeffOn U nu hnu omega m L hmL)
      (-p, q) (routeDoubledFieldL U nu hnu omega m L hmL p q u) :=
    doubledFieldOfScalarMaximizers_isDoubledMuMinimizer
      (centeredPairCoeffOn U nu hnu omega m L hmL) p q u
      (transposeResponseMaximizer U (centeredPairCoeffOn U nu hnu omega m L hmL) p (-q)) hu
      (transposeResponseMaximizer_isMaximizer U (centeredPairCoeffOn U nu hnu omega m L hmL)
        p (-q))
  have hA := averagedBlockQuadraticOn_minimizer_eq_responseJ hZ
  have hAt := averagedBlockQuadraticOn_minimizer_eq_responseJ hZt
  rw [levelMCoeffOn_toCoeffField] at hA
  rw [centeredPairCoeffOn_toCoeffField] at hAt
  exact hscale_of_minimizerEnergy hA hAt

/-! ## The strict branch's window conclusion at the minimizer energies -/

/-- **The strict branch's conclusion at the minimizer energies.**  From the printed
chain at the minimizers' own energies and the fact that the perturbed minimizer's
energy is at most half the response bracket, the mean squared gradient difference is
at most `16 η ν⁻¹` times the response bracket.  The `η²` term is charged to
`2 R_pert + 2 p·q`, the perturbed minimizer's own energy, so the constant-loading
quadratic and its response comparison are never formed. -/
theorem gradientDifference_le_sixteen_eta_inv_nu_bracket {d : ℕ} (U : Book.Ch02.Domain d)
    (nu : ℝ) (hnu : 0 < nu) (omega : ShellSeq d) (n m L : ℕ) (hmLt : m < L)
    (hU : (U : Set (Vec d)) ⊆ openCubeSet (originCube d (n : ℤ))) (p q : Vec d)
    (v : AHarmonicFunction (coefficientCutoff nu omega m).toCoeffField (U : Set (Vec d)))
    (hv : Homogenization.IsResponseMaximizer (U : Set (Vec d)) p q
      (coefficientCutoff nu omega m).toCoeffField v)
    (u : AHarmonicFunction (centeredPairField nu omega m L (U : Set (Vec d)))
      (U : Set (Vec d)))
    (hu : Homogenization.IsResponseMaximizer (U : Set (Vec d)) p q
      (centeredPairField nu omega m L (U : Set (Vec d))) u)
    (hη0 : 0 ≤ cutoffPairEtaWindow d nu n m L omega)
    (hη1 : cutoffPairEtaWindow d nu n m L omega ≤ 1) :
    volumeAverage (U : Set (Vec d))
        (fun x => vecNormSq (u.toH1.grad x - v.toH1.grad x)) ≤
      16 * cutoffPairEtaWindow d nu n m L omega * nu⁻¹ *
        (ResponseJ (U : Set (Vec d)) p q
            (centeredPairField nu omega m L (U : Set (Vec d))) +
          ResponseJ (U : Set (Vec d)) p q (coefficientCutoff nu omega m).toCoeffField +
          2 * vecDot p q) := by
  set S : ℝ := ResponseJ (U : Set (Vec d)) p q
        (centeredPairField nu omega m L (U : Set (Vec d))) +
      ResponseJ (U : Set (Vec d)) p q (coefficientCutoff nu omega m).toCoeffField +
      2 * vecDot p q with hSdef
  have hSnn : 0 ≤ S := by
    rw [hSdef]
    exact responseJ_centeredPair_add_nonneg nu hnu m L U omega p q
  set QM : ℝ := averagedBlockQuadraticOn (U : Set (Vec d))
      (fun x => (coefficientCutoff nu omega m).toCoeffField x)
      (fun x => (routeDoubledFieldM U nu hnu omega m p q v).eval x) with hQMdef
  set QL : ℝ := averagedBlockQuadraticOn (U : Set (Vec d))
      (fun x => centeredPairField nu omega m L (U : Set (Vec d)) x)
      (fun x => (routeDoubledFieldL U nu hnu omega m L hmLt.le p q u).eval x) with hQLdef
  have hsum : QM + QL = 2 * S := by
    rw [hQMdef, hQLdef, hSdef]
    exact minimizerEnergySum_eq_frozenRHS U nu hnu omega m L hmLt.le p q v hv u hu
  have hQAnn : 0 ≤ QM := by
    rw [hQMdef]
    exact averagedBlockQuadraticOn_nonneg_of_elliptic (U := (U : Set (Vec d)))
      (A := fun x => (coefficientCutoff nu omega m).toCoeffField x) U.measurableSet
      (fun x hx => isEllipticMatrix_coefficientCutoff_domain U nu hnu omega m x hx)
      (X := fun x => (routeDoubledFieldM U nu hnu omega m p q v).eval x)
  have hQle : QL ≤ 2 * S := by linarith only [hsum, hQAnn]
  have hchain := conj3DeterministicFromBlock_min_cutoff_minimizerEnergy U nu hnu omega n m L
    hmLt hU p q v hv u hu
  rw [← hQMdef, ← hQLdef] at hchain
  have hηη : cutoffPairEtaWindow d nu n m L omega * cutoffPairEtaWindow d nu n m L omega ≤
      cutoffPairEtaWindow d nu n m L omega := by
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left hη1 hη0
  have hquad : 2 * (cutoffPairEtaWindow d nu n m L omega *
        cutoffPairEtaWindow d nu n m L omega * QL) ≤
      4 * cutoffPairEtaWindow d nu n m L omega * S := by
    have h1 : 2 * (cutoffPairEtaWindow d nu n m L omega *
          cutoffPairEtaWindow d nu n m L omega * QL) ≤
        2 * (cutoffPairEtaWindow d nu n m L omega *
          cutoffPairEtaWindow d nu n m L omega * (2 * S)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hQle (mul_nonneg hη0 hη0)) (by norm_num)
    have h2 : 2 * (cutoffPairEtaWindow d nu n m L omega *
          cutoffPairEtaWindow d nu n m L omega * (2 * S)) =
        (4 * (cutoffPairEtaWindow d nu n m L omega *
          cutoffPairEtaWindow d nu n m L omega)) * S := by ring
    have h3 : (4 * (cutoffPairEtaWindow d nu n m L omega *
          cutoffPairEtaWindow d nu n m L omega)) * S ≤
        (4 * cutoffPairEtaWindow d nu n m L omega) * S :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hηη (by norm_num : (0 : ℝ) ≤ 4)) hSnn
    have h4 : (4 * cutoffPairEtaWindow d nu n m L omega) * S =
        4 * cutoffPairEtaWindow d nu n m L omega * S := by ring
    linarith only [h1, h2, h3, h4]
  have hmain : averagedBlockQuadraticOn (U : Set (Vec d))
        (fun x => (coefficientCutoff nu omega m).toCoeffField x)
        (conj3SkewFreeDifference U nu hnu omega m L hmLt.le p q v u) ≤
      8 * cutoffPairEtaWindow d nu n m L omega * S := by
    have hlin : 2 * (cutoffPairEtaWindow d nu n m L omega * (QM + QL)) =
        4 * cutoffPairEtaWindow d nu n m L omega * S := by
      rw [hsum]
      ring
    linarith only [hchain, hlin, hquad]
  have hgrad := gradientDifference_le_skewFreeDifference U nu hnu omega m L hmLt.le p q v u
  have hstep : (2 / nu) * averagedBlockQuadraticOn (U : Set (Vec d))
        (fun x => (coefficientCutoff nu omega m).toCoeffField x)
        (conj3SkewFreeDifference U nu hnu omega m L hmLt.le p q v u) ≤
      (2 / nu) * (8 * cutoffPairEtaWindow d nu n m L omega * S) :=
    mul_le_mul_of_nonneg_left hmain (div_nonneg (by norm_num) hnu.le)
  calc
    volumeAverage (U : Set (Vec d))
        (fun x => vecNormSq (u.toH1.grad x - v.toH1.grad x)) ≤
        (2 / nu) * averagedBlockQuadraticOn (U : Set (Vec d))
          (fun x => (coefficientCutoff nu omega m).toCoeffField x)
          (conj3SkewFreeDifference U nu hnu omega m L hmLt.le p q v u) := hgrad
    _ ≤ (2 / nu) * (8 * cutoffPairEtaWindow d nu n m L omega * S) := hstep
    _ = 16 * cutoffPairEtaWindow d nu n m L omega * nu⁻¹ * S := by
      rw [div_eq_mul_inv]
      ring

/-! ## The third conjunct on the strict branch, without the constant-loading half -/

/-- **The third conjunct on the strict branch `m < L`, with no
constant-loading input.**  The statement is the third conjunct of
`Frozen.Section2.cutoff_localization` (`e.localization.minimizers`) at its
carriers and at every constant dominating the localization constant.  The window regimes
are a case split of the proof: `θ ≥ 1/2` is the printed large-amplitude display
(`cutoffLocalizationConjunct3_largeWindow`); `θ < 1/2` is the printed chain at the
minimizers' own energies
(`gradientDifference_le_sixteen_eta_inv_nu_bracket`) followed by the window payment
`16 η c(d) ≤ C θ` (`sixteen_etaWindow_mul_diamConst_le`) and the budget
(`sixteen_eta_window_budget`).  No hypothesis is added. -/
theorem cutoffLocalizationConjunct3_strictBranch_minimizerEnergy (d : ℕ) (C : ℝ) (nu : ℝ)
    (hnu : 0 < nu) (hnu1 : nu ≤ 1) (m n L : ℕ) (hnm : n ≤ m) (hmL : m ≤ L)
    (U : Book.Ch02.Domain d)
    (hU : (U : Set (Vec d)) ⊆ openCubeSet (originCube d (n : ℤ))) (omega : ShellSeq d)
    (p q : Vec d)
    (u : AHarmonicFunction (centeredPairField nu omega m L (U : Set (Vec d)))
      (U : Set (Vec d)))
    (v : AHarmonicFunction (coefficientCutoff nu omega m).toCoeffField
      (U : Set (Vec d)))
    (hu : ∀ w : AHarmonicFunction (centeredPairField nu omega m L (U : Set (Vec d)))
        (U : Set (Vec d)),
      volumeAverage (U : Set (Vec d))
          (scalarResponseIntegrand (U : Set (Vec d))
            (centeredPairField nu omega m L (U : Set (Vec d))) p q w) ≤
        volumeAverage (U : Set (Vec d))
          (scalarResponseIntegrand (U : Set (Vec d))
            (centeredPairField nu omega m L (U : Set (Vec d))) p q u))
    (hv : ∀ w : AHarmonicFunction (coefficientCutoff nu omega m).toCoeffField
        (U : Set (Vec d)),
      volumeAverage (U : Set (Vec d))
          (scalarResponseIntegrand (U : Set (Vec d))
            (coefficientCutoff nu omega m).toCoeffField p q w) ≤
        volumeAverage (U : Set (Vec d))
          (scalarResponseIntegrand (U : Set (Vec d))
            (coefficientCutoff nu omega m).toCoeffField p q v))
    (hmLt : m < L) (hC : localizationMaxConst d ≤ C) :
    volumeAverage (U : Set (Vec d))
        (fun x => vecNormSq (u.toH1.grad x - v.toH1.grad x)) ≤
      C * nu ^ (-(2 : ℝ)) * (3 : ℝ) ^ n *
          SuperdiffusionCLT.Section3.Terms.anchorDerivSup m L n omega *
        (ResponseJ (U : Set (Vec d)) p q
            (centeredPairField nu omega m L (U : Set (Vec d))) +
          ResponseJ (U : Set (Vec d)) p q
            (coefficientCutoff nu omega m).toCoeffField +
          2 * vecDot p q) := by
  by_cases hθ : (1 / 2 : ℝ) ≤ cutoffPairThetaWindow d nu n m L omega
  · exact cutoffLocalizationConjunct3_largeWindow d C nu hnu hnu1 m n L hnm hmL U hU omega
      p q u v hu hv hmLt hC hθ
  · have hθ0 : 0 ≤ cutoffPairThetaWindow d nu n m L omega :=
      cutoffPairThetaWindow_nonneg nu hnu n m L omega
    have hθ1 : cutoffPairThetaWindow d nu n m L omega ≤ 1 := by linarith only [hθ]
    have hηnn : 0 ≤ cutoffPairEtaWindow d nu n m L omega :=
      cutoffPairEtaWindow_nonneg nu hnu n m L omega
    have hθhalf : cutoffPairThetaWindow d nu n m L omega ≤ 1 / 2 := (lt_of_not_ge hθ).le
    have hηle : cutoffPairEtaWindow d nu n m L omega ≤ 1 := by
      have h1θ : 1 + cutoffPairThetaWindow d nu n m L omega ≤ 3 / 2 := by linarith only [hθ]
      have hbd : (1 / 2 : ℝ) * (3 / 2) ≤ 1 := by norm_num
      rw [cutoffPairEtaWindow]
      have h := mul_le_mul hθhalf h1θ
        (by linarith only [hθ0] : (0 : ℝ) ≤ 1 + cutoffPairThetaWindow d nu n m L omega)
        (by norm_num : (0 : ℝ) ≤ 1 / 2)
      linarith only [h, hbd]
    set S : ℝ := ResponseJ (U : Set (Vec d)) p q
          (centeredPairField nu omega m L (U : Set (Vec d))) +
        ResponseJ (U : Set (Vec d)) p q (coefficientCutoff nu omega m).toCoeffField +
        2 * vecDot p q with hSdef
    have hSnn : 0 ≤ S := by
      rw [hSdef]
      exact responseJ_centeredPair_add_nonneg nu hnu m L U omega p q
    have hfinal := gradientDifference_le_sixteen_eta_inv_nu_bracket U nu hnu omega n m L hmLt
      hU p q v hv u hu hηnn hηle
    rw [← hSdef] at hfinal
    have hC32 : 32 * matrixOperatorNorm_diamConst d ≤ C :=
      le_trans (thirtytwo_mul_diamConst_le_localizationMaxConst d) hC
    have hCnn : 0 ≤ C :=
      le_trans (mul_nonneg (by norm_num) (matrixOperatorNorm_diamConst_nonneg d)) hC32
    have hpay := sixteen_etaWindow_mul_diamConst_le (d := d) (C := C) n m L omega hC32 hθ0 hθ1
    have hbudget := sixteen_eta_window_budget (d := d) (C := C) hnu hCnn n m L omega hpay
    calc
      volumeAverage (U : Set (Vec d))
          (fun x => vecNormSq (u.toH1.grad x - v.toH1.grad x)) ≤
          16 * cutoffPairEtaWindow d nu n m L omega * nu⁻¹ * S := hfinal
      _ ≤ (C * nu ^ (-(2 : ℝ)) * (3 : ℝ) ^ n *
            SuperdiffusionCLT.Section3.Terms.anchorDerivSup m L n omega) * S :=
          mul_le_mul_of_nonneg_right hbudget hSnn
      _ = C * nu ^ (-(2 : ℝ)) * (3 : ℝ) ^ n *
            SuperdiffusionCLT.Section3.Terms.anchorDerivSup m L n omega * S := by ring

/-! ## `hconj3` in the shape `CutoffLocalizationAssembly` consumes

The statement below is the third conjunct exactly as
`CutoffLocalizationAssembly.cutoff_localization_proved` consumes it,
copied binder for binder: carriers as the explicit centered lambda, window as the
raw `sSup`, the five shell laws verbatim.  It carries **no** extra hypothesis. -/
theorem cutoffLocalizationConjunct3_hconj3_minimizerEnergy (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    ∀ C : ℝ, localizationMaxConst d ≤ C →
      ∀ (nu : ℝ), 0 < nu → nu ≤ 1 →
      ∀ P : ProbabilityMeasure (ShellSeq d),
        ShellLawPrefix d P → ShellLawJ1Restriction d P → ShellLawJ2 d P →
        ShellLawJ3 d P → ShellLawJ4 d P →
        ∀ m n L : ℕ, n ≤ m → m ≤ L →
          ∀ U : Domain d,
            (U : Set (Vec d)) ⊆ openCubeSet (originCube d (n : ℤ)) →
            ∀ (omega : ShellSeq d) (p q : Vec d)
              (u : AHarmonicFunction
                (fun x : Vec d =>
                  (coefficientCutoff nu omega L).toCoeffField x -
                    volumeAverageMat (U : Set (Vec d))
                      (fun y => finiteShellIncrement omega m L y))
                (U : Set (Vec d)))
              (v : AHarmonicFunction
                (coefficientCutoff nu omega m).toCoeffField
                (U : Set (Vec d))),
              (∀ w : AHarmonicFunction
                  (fun x : Vec d =>
                    (coefficientCutoff nu omega L).toCoeffField x -
                      volumeAverageMat (U : Set (Vec d))
                        (fun y => finiteShellIncrement omega m L y))
                  (U : Set (Vec d)),
                  volumeAverage (U : Set (Vec d))
                      (scalarResponseIntegrand (U : Set (Vec d))
                        (fun x : Vec d =>
                          (coefficientCutoff nu omega L).toCoeffField x -
                            volumeAverageMat (U : Set (Vec d))
                              (fun y => finiteShellIncrement omega m L y))
                        p q w) ≤
                    volumeAverage (U : Set (Vec d))
                      (scalarResponseIntegrand (U : Set (Vec d))
                        (fun x : Vec d =>
                          (coefficientCutoff nu omega L).toCoeffField x -
                            volumeAverageMat (U : Set (Vec d))
                              (fun y => finiteShellIncrement omega m L y))
                        p q u)) →
                (∀ w : AHarmonicFunction
                    (coefficientCutoff nu omega m).toCoeffField
                    (U : Set (Vec d)),
                    volumeAverage (U : Set (Vec d))
                        (scalarResponseIntegrand (U : Set (Vec d))
                          (coefficientCutoff nu omega m).toCoeffField p q w) ≤
                      volumeAverage (U : Set (Vec d))
                        (scalarResponseIntegrand (U : Set (Vec d))
                          (coefficientCutoff nu omega m).toCoeffField p q v)) →
                  volumeAverage (U : Set (Vec d))
                      (fun x => vecNormSq (u.toH1.grad x - v.toH1.grad x)) ≤
                    C * nu ^ (-(2 : ℝ)) * (3 : ℝ) ^ n *
                        sSup (Set.range fun o :
                          Option {x : Vec d //
                            x ∈ openCubeSet (originCube d (n : ℤ))} =>
                            match o with
                            | none => 0
                            | some x =>
                                ShellField.matrixDerivativeNorm
                                  (∑ k ∈ Finset.Ioc m L,
                                    ShellField.deriv (omega k) x.1)) *
                      (ResponseJ (U : Set (Vec d)) p q
                          (fun x : Vec d =>
                            (coefficientCutoff nu omega L).toCoeffField x -
                              volumeAverageMat (U : Set (Vec d))
                                (fun y => finiteShellIncrement omega m L y)) +
                        ResponseJ (U : Set (Vec d)) p q
                          (coefficientCutoff nu omega m).toCoeffField +
                        2 * vecDot p q) := by
  intro C hC nu hnu hnu1 P hP1 hP2 hP3 hP4 hP5 m n L hnm hmL U hU omega p q u v hu hv
  -- the shell-law hypotheses of the statement are not consulted by either branch
  have _frozen : ShellLawPrefix d P ∧ ShellLawJ1Restriction d P ∧ ShellLawJ2 d P ∧ ShellLawJ3 d P ∧
      ShellLawJ4 d P ∧ nu ≤ 1 := ⟨hP1, hP2, hP3, hP4, hP5, hnu1⟩
  rcases lt_or_eq_of_le hmL with hlt | heq
  · exact cutoffLocalizationConjunct3_strictBranch_minimizerEnergy d C nu hnu hnu1 m n L hnm
      hmL U hU omega p q u v hu hv hlt hC
  · exact cutoffLocalizationConjunct3_coincidentBranch d hd C nu hnu hnu1 m n L
      hnm hmL heq U hU omega p q u v hu hv

/-! ## Non-vacuity at a nonzero loading

At `p ≠ 0`, `m < L` the loading `(-p, q)` is nonzero.  The witnesses below read the
(Q1) bound and the response-bracket identity on the cube domain at every such loading,
where the perturbed forward maximizer exists unconditionally. -/

end

end SuperdiffusionCLT.Section2.Localization

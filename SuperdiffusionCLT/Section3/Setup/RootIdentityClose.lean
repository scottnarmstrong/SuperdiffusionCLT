/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Setup.MasterIdentityResidueC
public import SuperdiffusionCLT.Section3.Terms.MaximizerCoefficientStabilityB
public import SuperdiffusionCLT.Section3.Terms.RHSTerm1InputsG
public import SuperdiffusionCLT.Section3.Setup.ResponseMeasurabilityC
public import SuperdiffusionCLT.Section2.Estimates.Stream.CoefficientLinftyMoments
public import SuperdiffusionCLT.Section2.Cutoff.DerivativeSummability

/-!
# The remaining mixed-scale `hData` binders `hI2`, `hI3`

The root carries three annealed integrability binders of the master identity
that pair the response gradient `∇w` against a mixed-scale field
(see `Section3Final`): `hI1`, `hI2`, `hI3`.  They are **Integrable side
conditions** — measurability plus a finite annealed integral of a cube average —
not algebraic identities, and `hI4` closes the block.  The three are the first
three summands of the master identity display `e.ellsep.testing`: the lines `a_ℓ∇u_n − q`,
`(k_{L'} − k_ℓ)(∇u_n − p)` and `a_{L'}(∇u_m − ∇u_n)`.

`hI1` (the level-`ℓ` cutoff against the level-`L'` glued field) is proved in
`MasterIdentityResidueC.master_residue_hI1`.  This module closes the other two at
the carriers the root's own data pin for them:

* `master_residue_hI2` — the cutoff increment `k_{L'} − k_ℓ` against the glued
  field shifted by `p`;
* `master_residue_hI3` — the level-`L'` cutoff against the maximizer-gradient
  difference `∇u_m − ∇u_n`, the carrier `cubeMaximizerGradient hnu · S.LPrime
  F (cu_m)` fixed by `MasterIdentitySideConditions`.  In the root's
  `hData` the field `uMgrad` is a *free* datum with no defining equation, so the
  root must instantiate it to this carrier; the theorem below is stated directly
  at that carrier.

Both proofs run the same engine as `hI1`: the class-measurability of the second
slot feeds `aemeasurable_volumeAverage_vecDot_grad_of_class`, and finiteness is
read off a measurable cutoff envelope whose annealed second moment is bounded in
`second_moment_coeffLinftySupBound_le`, which needs `L ≤ m`.  Since the selected
scales satisfy `S.m < S.LPrime`, the envelope is taken at the *coarser* cube
scale `S.LPrime`, not at `S.m`; the coefficient-cutoff difference is rewritten
pointwise to the `streamCutoff` difference of the display by
`coefficientCutoff_toCoeffField_sub_eq_streamCutoff_sub`.

## Main results

* `master_residue_hI2`, `master_residue_hI3`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Setup

open MeasureTheory ProbabilityTheory
open Homogenization
open Homogenization.Book.Ch02
open Homogenization.IndependentSums
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Probability
open SuperdiffusionCLT.Probability.Stationary
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Norms
open SuperdiffusionCLT.Section2.Estimates.Stream
open SuperdiffusionCLT.Section3.ResponseFields
open SuperdiffusionCLT.Section3.Terms
open scoped BigOperators ENNReal
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-! ## Elementary extended-real arithmetic -/

/-- The product of two extended reals is bounded by the sum of their squares. -/
private theorem root_mul_le_sq_add_sq (a b : ℝ≥0∞) :
    a * b ≤ a ^ (2 : ℕ) + b ^ (2 : ℕ) := by
  rcases le_total a b with h | h
  · calc a * b ≤ b * b := mul_le_mul' h le_rfl
      _ = b ^ (2 : ℕ) := (pow_two b).symm
      _ ≤ a ^ (2 : ℕ) + b ^ (2 : ℕ) := le_add_self
  · calc a * b ≤ a * a := mul_le_mul' le_rfl h
      _ = a ^ (2 : ℕ) := (pow_two a).symm
      _ ≤ a ^ (2 : ℕ) + b ^ (2 : ℕ) := le_self_add

/-- The square of a sum of two extended reals is at most four times the sum of
the squares. -/
private theorem root_add_sq_le (a b : ℝ≥0∞) :
    (a + b) ^ (2 : ℕ) ≤ 4 * (a ^ (2 : ℕ) + b ^ (2 : ℕ)) := by
  have haa : a * a ≤ a ^ (2 : ℕ) + b ^ (2 : ℕ) := by
    simp only [pow_two]
    exact le_self_add (a := a * a) (b := b * b)
  have hbb : b * b ≤ a ^ (2 : ℕ) + b ^ (2 : ℕ) := by
    simp only [pow_two]
    exact le_add_self (a := b * b) (b := a * a)
  have hab : a * b ≤ a ^ (2 : ℕ) + b ^ (2 : ℕ) := root_mul_le_sq_add_sq a b
  have hba : b * a ≤ a ^ (2 : ℕ) + b ^ (2 : ℕ) := by
    rw [mul_comm]; exact hab
  calc (a + b) ^ (2 : ℕ) = (a + b) * (a + b) := pow_two _
    _ = (a * a + b * a) + (a * b + b * b) := by
        rw [add_mul, mul_add, mul_add]; abel
    _ ≤ ((a ^ (2 : ℕ) + b ^ (2 : ℕ)) + (a ^ (2 : ℕ) + b ^ (2 : ℕ))) +
        ((a ^ (2 : ℕ) + b ^ (2 : ℕ)) + (a ^ (2 : ℕ) + b ^ (2 : ℕ))) :=
        add_le_add (add_le_add haa hba) (add_le_add hab hbb)
    _ = 4 * (a ^ (2 : ℕ) + b ^ (2 : ℕ)) := by ring

/-- The operator norm of a difference of matrices is at most the sum of the
operator norms. -/
private theorem root_matrixOperatorNorm_sub_le (A B : Mat d) :
    matrixOperatorNorm (A - B) ≤ matrixOperatorNorm A + matrixOperatorNorm B := by
  simp only [matrixOperatorNorm_eq_l2_opNorm]
  exact norm_sub_le A B

/-- A constant factor on the right leaves an extended-real integral. -/
private theorem root_lintegral_mul_const_right {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (c : ℝ≥0∞) (hc : c ≠ ⊤) (f : α → ℝ≥0∞) :
    (∫⁻ a, f a * c ∂μ) = c * ∫⁻ a, f a ∂μ := by
  rw [← lintegral_const_mul' c f hc]
  exact lintegral_congr fun a => mul_comm _ _

/-! ## The integrability engine -/

/-- **The cube average of the pairing of the response gradient against an
annealed-`L²` field is integrable in the sample**, from the `L²(cu_m)` class
measurability of the second slot and the finiteness of the two annealed squared
cube norms. -/
private theorem root_integrable_pairing [NeZero d]
    {LPrime ellPrime m : ℕ} {p : Vec d}
    {P : ProbabilityMeasure (ShellSeq d)}
    {w : ShellSeq d → H10Function (openCubeSet (originCube d (m : ℤ)))}
    (hw : ∀ omega : ShellSeq d,
      IsDirichletResponse omega LPrime ellPrime m p (w omega))
    {Vfield : ShellSeq d → Vec d → Vec d}
    (hVmem : ∀ omega : ShellSeq d,
      MemVectorL2 (openCubeSet (originCube d (m : ℤ))) (Vfield omega))
    (hVclass : AEMeasurable (fun omega : ShellSeq d =>
      toHilbertVectorL2OfVecField (hVmem omega)) P.toMeasure)
    (hfinV : (∫⁻ omega : ShellSeq d,
      vecCubeLpENorm (originCube d (m : ℤ)) 2 (Vfield omega) ^ (2 : ℕ)
        ∂P.toMeasure) ≠ ⊤)
    (hfinG : (∫⁻ omega : ShellSeq d,
      vecCubeLpENorm (originCube d (m : ℤ)) 2
        ((w omega).toH1Function.grad) ^ (2 : ℕ) ∂P.toMeasure) ≠ ⊤) :
    Integrable (fun omega : ShellSeq d =>
      volumeAverage (openCubeSet (originCube d (m : ℤ)))
        (fun x => vecDot ((w omega).toH1Function.grad x) (Vfield omega x)))
      P.toMeasure := by
  classical
  have : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
  have hcs : ∀ omega : ShellSeq d,
      |volumeAverage (openCubeSet (originCube d (m : ℤ)))
        (fun x => vecDot ((w omega).toH1Function.grad x) (Vfield omega x))| ≤
        (vecCubeLpENorm (originCube d (m : ℤ)) 2
            ((w omega).toH1Function.grad)).toReal *
          (vecCubeLpENorm (originCube d (m : ℤ)) 2 (Vfield omega)).toReal := by
    intro omega
    rw [← volumeAverage_cubeSet_eq_openCubeSet]
    exact SuperdiffusionCLT.Section2.Norms.abs_volumeAverage_vecDot_le_mul
      (memLp_hilbertifyVecField_of_memVectorL2
        (w omega).toH1Function.grad_memVectorL2)
      (memLp_hilbertifyVecField_of_memVectorL2 (hVmem omega))
  have hbound : ∀ omega : ShellSeq d,
      ‖volumeAverage (openCubeSet (originCube d (m : ℤ)))
        (fun x => vecDot ((w omega).toH1Function.grad x) (Vfield omega x))‖ₑ ≤
        vecCubeLpENorm (originCube d (m : ℤ)) 2
            ((w omega).toH1Function.grad) ^ (2 : ℕ) +
          vecCubeLpENorm (originCube d (m : ℤ)) 2 (Vfield omega) ^ (2 : ℕ) := by
    intro omega
    have h0 : ‖volumeAverage (openCubeSet (originCube d (m : ℤ)))
        (fun x => vecDot ((w omega).toH1Function.grad x) (Vfield omega x))‖ₑ =
        ENNReal.ofReal |volumeAverage (openCubeSet (originCube d (m : ℤ)))
          (fun x => vecDot ((w omega).toH1Function.grad x) (Vfield omega x))| :=
      Real.enorm_eq_ofReal_abs _
    have h1 := hcs omega
    have hxf : vecCubeLpENorm (originCube d (m : ℤ)) 2
        ((w omega).toH1Function.grad) ≠ ⊤ :=
      (memLp_hilbertifyVecField_of_memVectorL2
        (w omega).toH1Function.grad_memVectorL2).eLpNorm_lt_top.ne
    have hyf : vecCubeLpENorm (originCube d (m : ℤ)) 2 (Vfield omega) ≠ ⊤ :=
      (memLp_hilbertifyVecField_of_memVectorL2 (hVmem omega)).eLpNorm_lt_top.ne
    have h2 : ENNReal.ofReal ((vecCubeLpENorm (originCube d (m : ℤ)) 2
          ((w omega).toH1Function.grad)).toReal *
        (vecCubeLpENorm (originCube d (m : ℤ)) 2 (Vfield omega)).toReal) =
        vecCubeLpENorm (originCube d (m : ℤ)) 2 ((w omega).toH1Function.grad) *
          vecCubeLpENorm (originCube d (m : ℤ)) 2 (Vfield omega) := by
      rw [ENNReal.ofReal_mul (vecCubeLpENorm _ 2 _).toReal_nonneg,
        ENNReal.ofReal_toReal hxf, ENNReal.ofReal_toReal hyf]
    refine le_trans (le_trans (le_of_eq h0) ?_) (root_mul_le_sq_add_sq _ _)
    refine le_trans (ENNReal.ofReal_le_ofReal h1) ?_
    rw [h2]
  have hmeas : AEMeasurable (fun omega : ShellSeq d =>
      volumeAverage (openCubeSet (originCube d (m : ℤ)))
        (fun x => vecDot ((w omega).toH1Function.grad x) (Vfield omega x)))
      P.toMeasure :=
    aemeasurable_volumeAverage_vecDot_grad_of_class hw hVmem hVclass
  refine ⟨hmeas.aestronglyMeasurable, ?_⟩
  rw [MeasureTheory.hasFiniteIntegral_def]
  refine lt_of_le_of_lt (lintegral_mono hbound) ?_
  have hGN : (∫⁻ omega : ShellSeq d,
      vecCubeLpENorm (originCube d (m : ℤ)) 2
        ((w omega).toH1Function.grad) ^ (2 : ℕ) ∂P.toMeasure) < ⊤ :=
    lt_of_le_of_ne le_top hfinG
  have hGNm : AEMeasurable (fun omega : ShellSeq d =>
      vecCubeLpENorm (originCube d (m : ℤ)) 2
        ((w omega).toH1Function.grad) ^ (2 : ℕ)) P.toMeasure :=
    (aemeasurable_vecCubeLpENorm_grad (m := m) (p := p) hw).pow_const 2
  rw [lintegral_add_left' hGNm]
  exact ENNReal.add_lt_top.2 ⟨hGN, lt_of_le_of_ne le_top hfinV⟩

/-! ## Envelope domination on the coarse cube -/

/-- The coefficient-cutoff operator norm at level `L` is dominated a.e. on the
sub-cube `cu_m` by the envelope at the coarser cube scale `r` (`m ≤ r`), where
the second moment bound applies. -/
private theorem root_ae_matrixOperatorNorm_le {nu : ℝ} (hnu : 0 < nu) {L r m : ℕ}
    (hmr : m ≤ r) (omega : ShellSeq d) :
    ∀ᵐ x ∂normalizedCubeMeasure (originCube d (m : ℤ)),
      matrixOperatorNorm ((coefficientCutoff nu omega L).toCoeffField x) ≤
        coeffLinftySupBound nu L r omega := by
  have hQae : ∀ᵐ x ∂normalizedCubeMeasure (originCube d (m : ℤ)),
      x ∈ openCubeSet (originCube d (m : ℤ)) := by
    rw [normalizedCubeMeasure_eq_smul_volume_restrict_openCubeSet]
    exact MeasureTheory.Measure.ae_smul_measure
      (MeasureTheory.ae_restrict_mem
        (measurableSet_openCubeSet (originCube d (m : ℤ)))) _
  filter_upwards [hQae] with x hx
  exact matrixOperatorNorm_coefficientCutoff_le_coeffLinftySupBound nu (le_of_lt hnu)
    omega (openCubeSet_subset_cubeSet (originCube d (r : ℤ))
      (SuperdiffusionCLT.Section2.Cutoff.openCubeSet_originCube_subset hmr hx))

/-- The class norm of a `matVecMul` by a matrix that is dominated a.e. by a real
constant. -/
private theorem root_cubeNorm_matVecMul_le {Q : TriadicCube d}
    (A : Vec d → Mat d) (V : Vec d → Vec d) {c : ℝ} (hc : 0 ≤ c)
    (hAc : Continuous A)
    (hV : MeasureTheory.AEStronglyMeasurable (hilbertifyVecField V) (normalizedCubeMeasure Q))
    (hae : ∀ᵐ x ∂normalizedCubeMeasure Q, matrixOperatorNorm (A x) ≤ c) :
    vecCubeLpENorm Q 2 (fun x => matVecMul (A x) (V x)) ≤
      ENNReal.ofReal c * vecCubeLpENorm Q 2 V :=
  vecCubeLpENorm_matVecMul_le (Q := Q) 2 A V hc
    (aestronglyMeasurable_hilbertifyVecField_matVecMul hAc hV) hae

/-- The class norm of a `matVecMul` by a matrix difference, dominated a.e. by
the sum of two real constants. -/
private theorem root_cubeNorm_matVecMul_sub_le {Q : TriadicCube d}
    (A B : Vec d → Mat d) (V : Vec d → Vec d) {cA cB : ℝ}
    (hcA : 0 ≤ cA) (hcB : 0 ≤ cB)
    (hAc : Continuous A) (hBc : Continuous B)
    (hV : MeasureTheory.AEStronglyMeasurable (hilbertifyVecField V) (normalizedCubeMeasure Q))
    (hA : ∀ᵐ x ∂normalizedCubeMeasure Q, matrixOperatorNorm (A x) ≤ cA)
    (hB : ∀ᵐ x ∂normalizedCubeMeasure Q, matrixOperatorNorm (B x) ≤ cB) :
    vecCubeLpENorm Q 2 (fun x => matVecMul (A x - B x) (V x)) ≤
      ENNReal.ofReal (cA + cB) * vecCubeLpENorm Q 2 V :=
  vecCubeLpENorm_matVecMul_le (Q := Q) 2 (fun x => A x - B x) V (by positivity)
    (aestronglyMeasurable_hilbertifyVecField_matVecMul (hAc.sub hBc) hV)
    (by
      filter_upwards [hA, hB] with x hxA hxB
      exact le_trans (root_matrixOperatorNorm_sub_le (A x) (B x))
        (add_le_add hxA hxB))

/-- The class norm of the constant field `-p` is `‖p‖`. -/
private theorem root_cubeNorm_neg_const (Q : TriadicCube d) (p : Vec d) :
    vecCubeLpENorm Q 2 (fun _ : Vec d => -p) = ENNReal.ofReal (vecNorm p) := by
  rw [vecCubeLpENorm_const Q (by norm_num) (-p), ← HilbertVec.ofVecL_apply (-p),
    map_neg (HilbertVec.ofVecL d) p, enorm_neg, HilbertVec.ofVecL_apply p,
    ← ofReal_norm, ← vecNorm_eq_norm_ofVec]

/-! ## The response's own second moment -/

/-- The annealed squared cube norm of the response gradient is finite. -/
private theorem root_fin_grad {d : ℕ} [NeZero d] (hd : 2 ≤ d) {nu : ℝ} (hnu : 0 < nu)
    (hnu1 : nu ≤ 1) (P : ProbabilityMeasure (ShellSeq d))
    (hPrefix : ShellLawPrefix d P) (hJ1V2 : ShellLawJ1Restriction d P) (hJ2 : ShellLawJ2 d P)
    (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P)
    (S : ScaleSelection) (hSorder : ScalesOrdering S)
    (ee : Vec d) (he : vecNormSq ee = 1) (p : Vec d)
    (hp : p = testVector nu S.LPrime P S.n ee)
    (w : ShellSeq d → H10Function (openCubeSet (originCube d (S.m : ℤ))))
    (hw : ∀ omega : ShellSeq d, IsDirichletResponse omega S.LPrime S.ellPrime S.m p (w omega)) :
    (∫⁻ omega : ShellSeq d,
      vecCubeLpENorm (originCube d (S.m : ℤ)) 2
        ((w omega).toH1Function.grad) ^ (2 : ℕ) ∂P.toMeasure) ≠ ⊤ := by
  obtain ⟨Creg, hCreg, hregw⟩ := l_w_basic_regbounds_window d hd
  have hregA := hregw nu hnu hnu1 P hPrefix hJ1V2 hJ2 hJ3 hJ4 S hSorder ee he p hp
    w hw
  have hsecond := gradW_l2_second_moment_explicit hnu hPrefix hJ2 hJ3 hJ4 S hSorder
    ee he p hp w Creg hCreg hregA.1
  exact (lt_of_le_of_lt hsecond ENNReal.ofReal_lt_top).ne

/-! ## `hI2`: the cutoff increment against the shifted glued field -/

/-- **`hI2`, the second annealed integrability binder of the master identity
display** (the second line of the display `e.ellsep.testing`): the sample
integrability of the cube average of the pairing of the response gradient `∇w`
with `(k_{L'} − k_ℓ)(∇u_n − p)`.

Measurability of the `L²(cu_m)` class is the multiplication map on classes, fed
by the joint measurability of the coefficient-cutoff difference
(`measurable_prod_coefficientCutoff_sub`) and the glued class
(`measurable_gluedGradientClass`).  Finiteness uses the two coefficient
envelopes at the coarser cube scale `S.LPrime` (where `second_moment_coeff
LinftySupBound_le` applies, since `ℓ ≤ L'`), the glued energy bound
`vecCubeLpENorm_two_sq_gluedGradientField_le`, and the response's own second
moment.  The `streamCutoff` difference of the display is the coefficient-cutoff
difference by `coefficientCutoff_toCoeffField_sub_eq_streamCutoff_sub`. -/
theorem master_residue_hI2 {d : ℕ} [NeZero d] (hd : 2 ≤ d) (nu : ℝ) (hnu : 0 < nu)
    (hnu1 : nu ≤ 1) (P : ProbabilityMeasure (ShellSeq d))
    (hPrefix : ShellLawPrefix d P) (hJ1V2 : ShellLawJ1Restriction d P) (hJ2 : ShellLawJ2 d P)
    (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P)
    (S : ScaleSelection) (hSorder : ScalesOrdering S)
    (ee : Vec d) (he : vecNormSq ee = 1) (p : Vec d)
    (hp : p = testVector nu S.LPrime P S.n ee)
    (w : ShellSeq d → H10Function (openCubeSet (originCube d (S.m : ℤ))))
    (hw : ∀ omega : ShellSeq d, IsDirichletResponse omega S.LPrime S.ellPrime S.m p (w omega)) :
    Integrable (fun omega : ShellSeq d =>
      volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
        (fun x => vecDot ((w omega).toH1Function.grad x)
          (matVecMul (streamCutoff omega S.LPrime x - streamCutoff omega S.ell x)
            (gluedGradientField hnu S.LPrime S.n S.m (fluxSlot nu S.LPrime P S.n ee)
              omega x - p)))) P.toMeasure := by
  set F : Vec d := fluxSlot nu S.LPrime P S.n ee with hFdef
  have hn_le_m : S.n ≤ S.m := (ScalesOrdering.mem_pigeon_range hSorder).1.2
  have hle : S.ell ≤ S.LPrime :=
    le_trans (ScalesOrdering.mem_pigeon_range hSorder).2.1.2
      (le_of_lt (ScalesOrdering.m_lt_LPrime hSorder))
  have hmL' : S.m ≤ S.LPrime := le_of_lt (ScalesOrdering.m_lt_LPrime hSorder)
  -- the display's `streamCutoff` difference is the coefficient-cutoff difference
  have hmat : ∀ (omega : ShellSeq d) (x : Vec d),
      streamCutoff omega S.LPrime x - streamCutoff omega S.ell x =
        ((coefficientCutoff nu omega S.LPrime).toCoeffField x -
          (coefficientCutoff nu omega S.ell).toCoeffField x) := by
    intro omega x
    exact (SuperdiffusionCLT.Section3.Setup.coefficientCutoff_toCoeffField_sub_eq_streamCutoff_sub
      nu omega S.LPrime S.ell x).symm
  have hstream : (fun omega : ShellSeq d => volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
        (fun x => vecDot ((w omega).toH1Function.grad x)
          (matVecMul (streamCutoff omega S.LPrime x - streamCutoff omega S.ell x)
            (gluedGradientField hnu S.LPrime S.n S.m F omega x - p)))) =
      fun omega : ShellSeq d => volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
        (fun x => vecDot ((w omega).toH1Function.grad x)
          (matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField x -
            (coefficientCutoff nu omega S.ell).toCoeffField x)
            (gluedGradientField hnu S.LPrime S.n S.m F omega x - p))) := by
    funext omega
    exact congrArg (volumeAverage (openCubeSet (originCube d (S.m : ℤ))))
      (funext fun x => by rw [hmat omega x])
  rw [hstream]
  have hgl : ∀ omega : ShellSeq d,
      MemVectorL2 (openCubeSet (originCube d (S.m : ℤ)))
        (gluedGradientField hnu S.LPrime S.n S.m F omega) :=
    fun omega => memVectorL2_openCubeSet_gluedGradientField hnu S.LPrime S.n S.m
      F omega (originCube d (S.m : ℤ))
  have hVmem : ∀ omega : ShellSeq d,
      MemVectorL2 (openCubeSet (originCube d (S.m : ℤ)))
        (fun x => matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField x -
          (coefficientCutoff nu omega S.ell).toCoeffField x)
          (gluedGradientField hnu S.LPrime S.n S.m F omega x - p)) :=
    fun omega => memVectorL2_matVecMul_coefficientCutoff_sub hnu omega S.LPrime S.ell
      (originCube d (S.m : ℤ)) ((hgl omega).sub (memVectorL2_const p))
  have hVclass : AEMeasurable (fun omega : ShellSeq d =>
      toHilbertVectorL2OfVecField (hVmem omega)) P.toMeasure := by
    have : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
    have hgluedClass : AEMeasurable (fun omega : ShellSeq d =>
        toHilbertVectorL2OfVecField (hgl omega)) P.toMeasure :=
      (measurable_gluedGradientClass hnu S.LPrime S.n S.m F).aemeasurable
    have hgClass : AEMeasurable (fun omega : ShellSeq d =>
        toHilbertVectorL2OfVecField ((hgl omega).sub (memVectorL2_const p)))
        P.toMeasure := by
      have hEq : (fun omega : ShellSeq d =>
          toHilbertVectorL2OfVecField ((hgl omega).sub (memVectorL2_const p))) =
          fun omega : ShellSeq d =>
            toHilbertVectorL2OfVecField (hgl omega) -
              toHilbertVectorL2OfVecField (memVectorL2_const (U := openCubeSet
                (originCube d (S.m : ℤ))) p) :=
        funext fun omega => toHilbertVectorL2OfVecField_sub (hgl omega)
          (memVectorL2_const p)
      rw [hEq]
      exact continuous_sub.measurable.comp_aemeasurable
        (hgluedClass.prodMk (measurable_const :
          Measurable (fun _ : ShellSeq d =>
            toHilbertVectorL2OfVecField (memVectorL2_const (U := openCubeSet
              (originCube d (S.m : ℤ))) p))).aemeasurable)
    have hmain := measurable_matFieldMulClass_family
      (measurableSet_openCubeSet (originCube d (S.m : ℤ)))
      (fun omega x => (coefficientCutoff nu omega S.LPrime).toCoeffField x -
        (coefficientCutoff nu omega S.ell).toCoeffField x)
      (measurable_prod_coefficientCutoff_sub nu S.LPrime S.ell)
      (fun omega f hf => memVectorL2_matVecMul_coefficientCutoff_sub hnu omega
        S.LPrime S.ell (originCube d (S.m : ℤ)) hf)
      (fun omega => exists_matVecMul_bound_openCubeSet (originCube d (S.m : ℤ))
        (fun i j => continuous_coefficientCutoff_sub_entry nu omega S.LPrime
          S.ell i j))
      (g := fun omega => toHilbertVectorL2OfVecField ((hgl omega).sub
        (memVectorL2_const p))) hgClass
    have hfun : (fun omega : ShellSeq d => toHilbertVectorL2OfVecField (hVmem omega)) =
        fun omega : ShellSeq d =>
          matFieldMulClass
            (fun x : Vec d => (coefficientCutoff nu omega S.LPrime).toCoeffField x -
              (coefficientCutoff nu omega S.ell).toCoeffField x)
            (fun f hf => memVectorL2_matVecMul_coefficientCutoff_sub hnu omega
              S.LPrime S.ell (originCube d (S.m : ℤ)) hf)
            (toHilbertVectorL2OfVecField ((hgl omega).sub (memVectorL2_const p))) := by
      funext omega
      rw [matFieldMulClass_toHilbertVectorL2OfVecField]
    rw [hfun]
    exact hmain
  have hVfin : (∫⁻ omega : ShellSeq d,
      vecCubeLpENorm (originCube d (S.m : ℤ)) 2
        (fun x => matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField x -
          (coefficientCutoff nu omega S.ell).toCoeffField x)
          (gluedGradientField hnu S.LPrime S.n S.m F omega x - p)) ^ (2 : ℕ)
        ∂P.toMeasure) ≠ ⊤ := by
    have hcgl : (0 : ℝ) ≤ nu⁻¹ * nu⁻¹ * vecNormSq F :=
      mul_nonneg (mul_nonneg (inv_nonneg.2 (le_of_lt hnu)) (inv_nonneg.2 (le_of_lt hnu)))
        (vecNormSq_nonneg F)
    have hE1t : Measurable (fun omega : ShellSeq d =>
        (ENNReal.ofReal (coeffLinftySupBound nu S.LPrime S.LPrime omega)) ^ (2 : ℕ)) :=
      (ENNReal.measurable_ofReal.comp
        (measurable_coeffLinftySupBound nu S.LPrime S.LPrime)).pow_const 2
    have hI1c : (∫⁻ omega : ShellSeq d,
        (ENNReal.ofReal (coeffLinftySupBound nu S.LPrime S.LPrime omega)) ^ (2 : ℕ)
          ∂P.toMeasure) ≤ ENNReal.ofReal (coeffCubeLinftySecondMomentConst d *
            ((1 + (S.LPrime : ℝ)) * (1 + (S.LPrime : ℝ)))) :=
      second_moment_coeffLinftySupBound_le hPrefix hJ2 hJ3 hJ4 (le_of_lt hnu) hnu1
        (le_refl S.LPrime)
    have hI2c : (∫⁻ omega : ShellSeq d,
        (ENNReal.ofReal (coeffLinftySupBound nu S.ell S.LPrime omega)) ^ (2 : ℕ)
          ∂P.toMeasure) ≤ ENNReal.ofReal (coeffCubeLinftySecondMomentConst d *
            ((1 + (S.ell : ℝ)) * (1 + (S.LPrime : ℝ)))) :=
      second_moment_coeffLinftySupBound_le hPrefix hJ2 hJ3 hJ4 (le_of_lt hnu) hnu1 hle
    have hKlt : (4 : ℝ≥0∞) * (ENNReal.ofReal (nu⁻¹ * nu⁻¹ * vecNormSq F) +
        (ENNReal.ofReal (vecNorm p)) ^ (2 : ℕ)) < ⊤ :=
      ENNReal.mul_lt_top (by norm_num)
        (ENNReal.add_lt_top.2 ⟨ENNReal.ofReal_lt_top, ENNReal.pow_lt_top ENNReal.ofReal_lt_top⟩)
    have hgl2 : ∀ omega : ShellSeq d,
        vecCubeLpENorm (originCube d (S.m : ℤ)) 2
          (gluedGradientField hnu S.LPrime S.n S.m F omega) ^ (2 : ℕ) ≤
          ENNReal.ofReal (nu⁻¹ * nu⁻¹ * vecNormSq F) :=
      fun omega => vecCubeLpENorm_two_sq_gluedGradientField_le hnu hn_le_m le_rfl
        S.LPrime F omega
    have hslot : ∀ omega : ShellSeq d,
        vecCubeLpENorm (originCube d (S.m : ℤ)) 2
          (fun x => gluedGradientField hnu S.LPrime S.n S.m F omega x - p) ^ (2 : ℕ) ≤
          (4 : ℝ≥0∞) * (ENNReal.ofReal (nu⁻¹ * nu⁻¹ * vecNormSq F) +
            (ENNReal.ofReal (vecNorm p)) ^ (2 : ℕ)) := by
      intro omega
      have htri : vecCubeLpENorm (originCube d (S.m : ℤ)) 2
          (fun x => gluedGradientField hnu S.LPrime S.n S.m F omega x - p) ≤
          vecCubeLpENorm (originCube d (S.m : ℤ)) 2
            (gluedGradientField hnu S.LPrime S.n S.m F omega) +
          vecCubeLpENorm (originCube d (S.m : ℤ)) 2 (fun _ : Vec d => -p) := by
        have h := vecCubeLpENorm_add_le (q := (2 : ℝ≥0∞)) (by norm_num)
          (F := gluedGradientField hnu S.LPrime S.n S.m F omega)
          (G := fun _ : Vec d => -p)
          (memLp_hilbertifyVecField_of_memVectorL2 (hgl omega)).aestronglyMeasurable
          (memLp_hilbertifyVecField_of_memVectorL2
            (memVectorL2_const (U := openCubeSet (originCube d (S.m : ℤ))) (-p))).aestronglyMeasurable
        simpa only [Pi.sub_apply, Pi.add_apply, sub_eq_add_neg] using h
      have hp2 := root_cubeNorm_neg_const (originCube d (S.m : ℤ)) p
      refine le_trans (pow_le_pow_left'
        (le_trans htri (add_le_add le_rfl (le_of_eq hp2))) 2) ?_
      refine le_trans (root_add_sq_le _ _) ?_
      exact mul_le_mul' le_rfl (add_le_add (hgl2 omega) le_rfl)
    have hptw : ∀ omega : ShellSeq d,
        vecCubeLpENorm (originCube d (S.m : ℤ)) 2
          (fun x => matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField x -
            (coefficientCutoff nu omega S.ell).toCoeffField x)
            (gluedGradientField hnu S.LPrime S.n S.m F omega x - p)) ^ (2 : ℕ) ≤
        (4 * ((ENNReal.ofReal (coeffLinftySupBound nu S.LPrime S.LPrime omega)) ^ (2 : ℕ) +
          (ENNReal.ofReal (coeffLinftySupBound nu S.ell S.LPrime omega)) ^ (2 : ℕ))) *
        ((4 : ℝ≥0∞) * (ENNReal.ofReal (nu⁻¹ * nu⁻¹ * vecNormSq F) +
          (ENNReal.ofReal (vecNorm p)) ^ (2 : ℕ))) := by
      intro omega
      have hAB := root_cubeNorm_matVecMul_sub_le
        (fun x : Vec d => (coefficientCutoff nu omega S.LPrime).toCoeffField x)
        (fun x : Vec d => (coefficientCutoff nu omega S.ell).toCoeffField x)
        (fun x : Vec d => gluedGradientField hnu S.LPrime S.n S.m F omega x - p)
        (coeffLinftySupBound_nonneg nu (le_of_lt hnu) S.LPrime S.LPrime omega)
        (coeffLinftySupBound_nonneg nu (le_of_lt hnu) S.ell S.LPrime omega)
        (continuous_coefficientCutoff_apply nu omega S.LPrime)
        (continuous_coefficientCutoff_apply nu omega S.ell)
        (memLp_hilbertifyVecField_of_memVectorL2
          ((hgl omega).sub (memVectorL2_const p))).aestronglyMeasurable
        (root_ae_matrixOperatorNorm_le hnu hmL' omega)
        (root_ae_matrixOperatorNorm_le hnu hmL' omega)
      refine le_trans (pow_le_pow_left' hAB 2) ?_
      rw [mul_pow, ENNReal.ofReal_add
        (coeffLinftySupBound_nonneg nu (le_of_lt hnu) S.LPrime S.LPrime omega)
        (coeffLinftySupBound_nonneg nu (le_of_lt hnu) S.ell S.LPrime omega)]
      exact mul_le_mul' (root_add_sq_le _ _) (hslot omega)
    have hlt : (∫⁻ omega : ShellSeq d,
        vecCubeLpENorm (originCube d (S.m : ℤ)) 2
          (fun x => matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField x -
            (coefficientCutoff nu omega S.ell).toCoeffField x)
            (gluedGradientField hnu S.LPrime S.n S.m F omega x - p)) ^ (2 : ℕ)
          ∂P.toMeasure) < ⊤ := by
      refine lt_of_le_of_lt (lintegral_mono hptw) ?_
      rw [root_lintegral_mul_const_right _ _ hKlt.ne
        (fun omega => (4 : ℝ≥0∞) * ((ENNReal.ofReal (coeffLinftySupBound nu
          S.LPrime S.LPrime omega)) ^ (2 : ℕ) + (ENNReal.ofReal (coeffLinftySupBound
          nu S.ell S.LPrime omega)) ^ (2 : ℕ)))]
      rw [lintegral_const_mul' (4 : ℝ≥0∞) _ (by norm_num)]
      rw [lintegral_add_left' hE1t.aemeasurable]
      exact ENNReal.mul_lt_top hKlt (ENNReal.mul_lt_top (by norm_num)
        (ENNReal.add_lt_top.2
          ⟨lt_of_le_of_lt hI1c ENNReal.ofReal_lt_top,
            lt_of_le_of_lt hI2c ENNReal.ofReal_lt_top⟩))
    exact hlt.ne
  have hfinG := root_fin_grad hd hnu hnu1 P hPrefix hJ1V2 hJ2 hJ3 hJ4 S hSorder
    ee he p hp w hw
  exact root_integrable_pairing hw hVmem hVclass hVfin hfinG

/-! ## `hI3`: the level-`L'` cutoff against the maximizer-gradient difference -/

/-- **`hI3`, the third annealed integrability binder of the master identity
display** (the third line of the display `e.ellsep.testing`): the sample
integrability of the cube average of the pairing of the response gradient `∇w`
with `a_{L'}(∇u_m − ∇u_n)`, at the maximizer-gradient carrier
`cubeMaximizerGradient hnu · S.LPrime F (cu_m)`.

Measurability is the multiplication map on classes, fed by the maximizer class
(`measurable_cubeMaximizerGradientClass`) and the glued class.  Finiteness uses
the level-`L'` coefficient envelope at the coarser cube scale `S.LPrime` (so that
`second_moment_coeffLinftySupBound_le` applies) and the energy bounds
`vecCubeLpENorm_two_sq_gluedGradientField_le` and
`volumeAverage_vecNormSq_cubeMaximizerGradient_le`. -/
theorem master_residue_hI3 {d : ℕ} [NeZero d] (hd : 2 ≤ d) (nu : ℝ) (hnu : 0 < nu)
    (hnu1 : nu ≤ 1) (P : ProbabilityMeasure (ShellSeq d))
    (hPrefix : ShellLawPrefix d P) (hJ1V2 : ShellLawJ1Restriction d P) (hJ2 : ShellLawJ2 d P)
    (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P)
    (S : ScaleSelection) (hSorder : ScalesOrdering S)
    (ee : Vec d) (he : vecNormSq ee = 1) (p : Vec d)
    (hp : p = testVector nu S.LPrime P S.n ee)
    (w : ShellSeq d → H10Function (openCubeSet (originCube d (S.m : ℤ))))
    (hw : ∀ omega : ShellSeq d, IsDirichletResponse omega S.LPrime S.ellPrime S.m p (w omega)) :
    Integrable (fun omega : ShellSeq d =>
      volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
        (fun x => vecDot ((w omega).toH1Function.grad x)
          (matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField x)
            (cubeMaximizerGradient hnu omega S.LPrime (fluxSlot nu S.LPrime P S.n ee)
                (originCube d (S.m : ℤ)) x -
              gluedGradientField hnu S.LPrime S.n S.m (fluxSlot nu S.LPrime P S.n ee)
                omega x)))) P.toMeasure := by
  set F : Vec d := fluxSlot nu S.LPrime P S.n ee with hFdef
  have hn_le_m : S.n ≤ S.m := (ScalesOrdering.mem_pigeon_range hSorder).1.2
  have hmL' : S.m ≤ S.LPrime := le_of_lt (ScalesOrdering.m_lt_LPrime hSorder)
  have hcm : ∀ omega : ShellSeq d,
      MemVectorL2 (openCubeSet (originCube d (S.m : ℤ)))
        (cubeMaximizerGradient hnu omega S.LPrime F (originCube d (S.m : ℤ))) :=
    fun omega => memVectorL2_cubeMaximizerGradient hnu omega S.LPrime F
      (originCube d (S.m : ℤ))
  have hgl : ∀ omega : ShellSeq d,
      MemVectorL2 (openCubeSet (originCube d (S.m : ℤ)))
        (gluedGradientField hnu S.LPrime S.n S.m F omega) :=
    fun omega => memVectorL2_openCubeSet_gluedGradientField hnu S.LPrime S.n S.m
      F omega (originCube d (S.m : ℤ))
  have hVmem : ∀ omega : ShellSeq d,
      MemVectorL2 (openCubeSet (originCube d (S.m : ℤ)))
        (fun x => matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField x)
          (cubeMaximizerGradient hnu omega S.LPrime F (originCube d (S.m : ℤ)) x -
            gluedGradientField hnu S.LPrime S.n S.m F omega x)) :=
    fun omega => memVectorL2_matVecMul_coefficientCutoff hnu omega S.LPrime
      (originCube d (S.m : ℤ)) ((hcm omega).sub (hgl omega))
  have hVclass : AEMeasurable (fun omega : ShellSeq d =>
      toHilbertVectorL2OfVecField (hVmem omega)) P.toMeasure := by
    have : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
    have hcmClass : AEMeasurable (fun omega : ShellSeq d =>
        toHilbertVectorL2OfVecField (hcm omega)) P.toMeasure :=
      (measurable_cubeMaximizerGradientClass hnu S.LPrime F
        (originCube d (S.m : ℤ))).aemeasurable
    have hgluedClass : AEMeasurable (fun omega : ShellSeq d =>
        toHilbertVectorL2OfVecField (hgl omega)) P.toMeasure :=
      (measurable_gluedGradientClass hnu S.LPrime S.n S.m F).aemeasurable
    have hgClass : AEMeasurable (fun omega : ShellSeq d =>
        toHilbertVectorL2OfVecField ((hcm omega).sub (hgl omega))) P.toMeasure := by
      have hEq : (fun omega : ShellSeq d =>
          toHilbertVectorL2OfVecField ((hcm omega).sub (hgl omega))) =
          fun omega : ShellSeq d =>
            toHilbertVectorL2OfVecField (hcm omega) -
              toHilbertVectorL2OfVecField (hgl omega) :=
        funext fun omega => toHilbertVectorL2OfVecField_sub (hcm omega) (hgl omega)
      rw [hEq]
      exact continuous_sub.measurable.comp_aemeasurable (hcmClass.prodMk hgluedClass)
    have hmain := measurable_matFieldMulClass_family
      (measurableSet_openCubeSet (originCube d (S.m : ℤ)))
      (fun omega x => (coefficientCutoff nu omega S.LPrime).toCoeffField x)
      (measurable_prod_coefficientCutoff nu S.LPrime)
      (fun omega f hf => memVectorL2_matVecMul_coefficientCutoff hnu omega S.LPrime
        (originCube d (S.m : ℤ)) hf)
      (fun omega => exists_matVecMul_bound_openCubeSet (originCube d (S.m : ℤ))
        (fun i j => continuous_coefficientCutoff_entry nu omega S.LPrime i j))
      (g := fun omega => toHilbertVectorL2OfVecField ((hcm omega).sub (hgl omega)))
      hgClass
    have hfun : (fun omega : ShellSeq d => toHilbertVectorL2OfVecField (hVmem omega)) =
        fun omega : ShellSeq d =>
          matFieldMulClass
            (fun x : Vec d => (coefficientCutoff nu omega S.LPrime).toCoeffField x)
            (fun f hf => memVectorL2_matVecMul_coefficientCutoff hnu omega S.LPrime
              (originCube d (S.m : ℤ)) hf)
            (toHilbertVectorL2OfVecField ((hcm omega).sub (hgl omega))) := by
      funext omega
      rw [matFieldMulClass_toHilbertVectorL2OfVecField]
    rw [hfun]
    exact hmain
  have hVfin : (∫⁻ omega : ShellSeq d,
      vecCubeLpENorm (originCube d (S.m : ℤ)) 2
        (fun x => matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField x)
          (cubeMaximizerGradient hnu omega S.LPrime F (originCube d (S.m : ℤ)) x -
            gluedGradientField hnu S.LPrime S.n S.m F omega x)) ^ (2 : ℕ)
        ∂P.toMeasure) ≠ ⊤ := by
    have hE1t : Measurable (fun omega : ShellSeq d =>
        (ENNReal.ofReal (coeffLinftySupBound nu S.LPrime S.LPrime omega)) ^ (2 : ℕ)) :=
      (ENNReal.measurable_ofReal.comp
        (measurable_coeffLinftySupBound nu S.LPrime S.LPrime)).pow_const 2
    have hI1c : (∫⁻ omega : ShellSeq d,
        (ENNReal.ofReal (coeffLinftySupBound nu S.LPrime S.LPrime omega)) ^ (2 : ℕ)
          ∂P.toMeasure) ≤ ENNReal.ofReal (coeffCubeLinftySecondMomentConst d *
            ((1 + (S.LPrime : ℝ)) * (1 + (S.LPrime : ℝ)))) :=
      second_moment_coeffLinftySupBound_le hPrefix hJ2 hJ3 hJ4 (le_of_lt hnu) hnu1
        (le_refl S.LPrime)
    have hKlt : (4 : ℝ≥0∞) * (ENNReal.ofReal (nu⁻¹ * nu⁻¹ * vecNormSq F) +
        ENNReal.ofReal (nu⁻¹ * nu⁻¹ * vecNormSq F)) < ⊤ :=
      ENNReal.mul_lt_top (by norm_num)
        (ENNReal.add_lt_top.2 ⟨ENNReal.ofReal_lt_top, ENNReal.ofReal_lt_top⟩)
    have henv : ∀ omega : ShellSeq d,
        vecCubeLpENorm (originCube d (S.m : ℤ)) 2
          (cubeMaximizerGradient hnu omega S.LPrime F (originCube d (S.m : ℤ))) ^ (2 : ℕ) ≤
          ENNReal.ofReal (nu⁻¹ * nu⁻¹ * vecNormSq F) :=
      fun omega => vecCubeLpENorm_two_sq_le_of_volumeAverage_le (hcm omega)
        (volumeAverage_vecNormSq_cubeMaximizerGradient_le hnu omega S.LPrime F
          (originCube d (S.m : ℤ)))
    have hgl2 : ∀ omega : ShellSeq d,
        vecCubeLpENorm (originCube d (S.m : ℤ)) 2
          (gluedGradientField hnu S.LPrime S.n S.m F omega) ^ (2 : ℕ) ≤
          ENNReal.ofReal (nu⁻¹ * nu⁻¹ * vecNormSq F) :=
      fun omega => vecCubeLpENorm_two_sq_gluedGradientField_le hnu hn_le_m le_rfl
        S.LPrime F omega
    have hslot : ∀ omega : ShellSeq d,
        vecCubeLpENorm (originCube d (S.m : ℤ)) 2
          (fun x => cubeMaximizerGradient hnu omega S.LPrime F (originCube d (S.m : ℤ)) x -
            gluedGradientField hnu S.LPrime S.n S.m F omega x) ^ (2 : ℕ) ≤
          (4 : ℝ≥0∞) * (ENNReal.ofReal (nu⁻¹ * nu⁻¹ * vecNormSq F) +
            ENNReal.ofReal (nu⁻¹ * nu⁻¹ * vecNormSq F)) := by
      intro omega
      have htri : vecCubeLpENorm (originCube d (S.m : ℤ)) 2
          (fun x => cubeMaximizerGradient hnu omega S.LPrime F (originCube d (S.m : ℤ)) x -
            gluedGradientField hnu S.LPrime S.n S.m F omega x) ≤
          vecCubeLpENorm (originCube d (S.m : ℤ)) 2
            (cubeMaximizerGradient hnu omega S.LPrime F (originCube d (S.m : ℤ))) +
          vecCubeLpENorm (originCube d (S.m : ℤ)) 2
            (gluedGradientField hnu S.LPrime S.n S.m F omega) := by
        have h := vecCubeLpENorm_add_le (q := (2 : ℝ≥0∞)) (by norm_num)
          (F := cubeMaximizerGradient hnu omega S.LPrime F (originCube d (S.m : ℤ)))
          (G := fun x : Vec d => -gluedGradientField hnu S.LPrime S.n S.m F omega x)
          (memLp_hilbertifyVecField_of_memVectorL2 (hcm omega)).aestronglyMeasurable
          (memLp_hilbertifyVecField_of_memVectorL2 ((hgl omega).neg)).aestronglyMeasurable
        simpa only [Pi.sub_apply, Pi.add_apply, sub_eq_add_neg, vecCubeLpENorm_neg] using h
      refine le_trans (pow_le_pow_left' htri 2) ?_
      refine le_trans (root_add_sq_le _ _) ?_
      exact mul_le_mul' le_rfl (add_le_add (henv omega) (hgl2 omega))
    have hptw : ∀ omega : ShellSeq d,
        vecCubeLpENorm (originCube d (S.m : ℤ)) 2
          (fun x => matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField x)
            (cubeMaximizerGradient hnu omega S.LPrime F (originCube d (S.m : ℤ)) x -
              gluedGradientField hnu S.LPrime S.n S.m F omega x)) ^ (2 : ℕ) ≤
        ((4 : ℝ≥0∞) * (ENNReal.ofReal (nu⁻¹ * nu⁻¹ * vecNormSq F) +
          ENNReal.ofReal (nu⁻¹ * nu⁻¹ * vecNormSq F))) *
        (ENNReal.ofReal (coeffLinftySupBound nu S.LPrime S.LPrime omega)) ^ (2 : ℕ) := by
      intro omega
      have hAB := root_cubeNorm_matVecMul_le
        (fun x : Vec d => (coefficientCutoff nu omega S.LPrime).toCoeffField x)
        (fun x : Vec d => cubeMaximizerGradient hnu omega S.LPrime F
          (originCube d (S.m : ℤ)) x - gluedGradientField hnu S.LPrime S.n S.m F omega x)
        (coeffLinftySupBound_nonneg nu (le_of_lt hnu) S.LPrime S.LPrime omega)
        (continuous_coefficientCutoff_apply nu omega S.LPrime)
        (memLp_hilbertifyVecField_of_memVectorL2
          ((hcm omega).sub (hgl omega))).aestronglyMeasurable
        (root_ae_matrixOperatorNorm_le hnu hmL' omega)
      refine le_trans (pow_le_pow_left' hAB 2) ?_
      rw [mul_pow]
      exact le_trans (mul_le_mul' le_rfl (hslot omega)) (le_of_eq (mul_comm _ _))
    have hlt : (∫⁻ omega : ShellSeq d,
        vecCubeLpENorm (originCube d (S.m : ℤ)) 2
          (fun x => matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField x)
            (cubeMaximizerGradient hnu omega S.LPrime F (originCube d (S.m : ℤ)) x -
              gluedGradientField hnu S.LPrime S.n S.m F omega x)) ^ (2 : ℕ)
          ∂P.toMeasure) < ⊤ := by
      refine lt_of_le_of_lt (lintegral_mono hptw) ?_
      rw [lintegral_const_mul' _ _ hKlt.ne]
      exact ENNReal.mul_lt_top hKlt
        (lt_of_le_of_lt hI1c ENNReal.ofReal_lt_top)
    exact hlt.ne
  have hfinG := root_fin_grad hd hnu hnu1 P hPrefix hJ1V2 hJ2 hJ3 hJ4 S hSorder
    ee he p hp w hw
  exact root_integrable_pairing hw hVmem hVclass hVfin hfinG

end

end SuperdiffusionCLT.Section3.Setup

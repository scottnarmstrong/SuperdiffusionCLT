/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Setup.ShellFluxWitnessesB
public import SuperdiffusionCLT.Section2.Estimates.Stream.IncrementLpClause
public import SuperdiffusionCLT.Section2.Annealed.CutoffRealizationPackage

/-!
# The scale-free `L̲⁴` witness of the centred shell flux

The third display of the proof of `l.LHS.term1` reads:

> The following `L̲⁴` bound follows from `e.kmn.Lp` with `p = 4` for `r < m`,
> and from `a.j.reg` and Poincare's inequality for `r ≥ m`: for every `r`,
> `‖ j_r p - (j_r p)_{cu_m} ‖_{L̲⁴(cu_m)} ≤ O_{Gamma₂}( C |p| )`.

The printed amplitude carries **no cube scale**.  The two halves are treated
separately:

* `r ≤ m`: the increment `L^p` clause
  `exists_witness_cubeLpENorm_finiteShellIncrement`
  at `p = 4`, applied to the one-shell increment `k_r - k_{r-1} = j_r` on the
  cube `cu_m`.  Its amplitude
  `C 4^{1/2} (r - (r-1))^{1/2} 3^{-(d/8)(m-r)}` is at most `2C`, and its
  deterministic term is `C (r - (r-1))^{1/2} = C`: both are free of the cube
  scale, because the single shell makes the printed factor `(m-n)^{1/2}` equal
  to one.  The clause consumes the restriction-lane law `ShellLawJ1Restriction`, which
  the statement of `l.LHS.term1` carries.
* `r > m`: the Poincare route of `ShellFluxWitnessesB.lean`, whose envelope
  `shellFluxLipBound` bounds every normalized `L̲^q` norm with `1 ≤ q` and has
  its `Gamma₂` tail at `d sqrt d |p| 3^{-(r-m)} ≤ d sqrt d |p|`.

This is the replacement for the `Zl4Witness` route of `ShellFluxWitnesses.lean`,
which bounds `L̲⁴` by the `L^∞` value envelope of the large cube and therefore
pays the union-bound factor `sqrt (1 + (m - r))`; that factor is what forces the
largeness gate `2 * shellFluxValueEnvelopeAmplitude d m ≤ Cl4` on a constant
chosen before the scale selection, which no such constant can satisfy at
unbounded `m`.  Here no gate on the constant beyond a dimension-only lower
bound occurs.

## Main results

* `shellFluxL4Const`, the dimension-only constant;
* `exists_shellFluxL4_belowCubeScale` and `exists_shellFluxL4_aboveCubeScale`,
  the two halves;
* `exists_shellFluxL4Witness_scaleFree`, the packaged four-clause family in the
  shape the `l.LHS.term1` reduction consumes as `hZl4`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Setup

open MeasureTheory
open ProbabilityTheory
open Homogenization
open Homogenization.Book.Ch02
open Homogenization.IndependentSums
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Probability
open SuperdiffusionCLT.Probability.Stationary
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Norms
open SuperdiffusionCLT.Section2.Estimates.Stream
open SuperdiffusionCLT.Section3.ResponseFields
open SuperdiffusionCLT.Section3.Terms
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ} {P : ProbabilityMeasure (ShellSeq d)}

/-! ## The one-shell increment -/

/-- The finite stream increment over `(r-1, r]` is the single shell `r`. -/
private theorem finiteShellIncrement_pred_apply (omega : ShellSeq d) {r : ℕ}
    (hr : 1 ≤ r) (x : Vec d) :
    (finiteShellIncrement omega (r - 1) r).toFun x = (omega r) x := by
  have hset : Finset.Ioc (r - 1) r = {r} := by
    ext k
    simp only [Finset.mem_Ioc, Finset.mem_singleton]
    omega
  have h := finiteShellIncrement_apply omega (r - 1) r x
  rw [h, hset, Finset.sum_singleton]
  simp only [shellReg, ShellField.forgetShell_apply]

/-- **The shell flux against the matrix carrier of the increment clause.**
The flux is the matrix field applied to `p`, so its normalized `L̲^q` norm is
at most `|p|` times the normalized `L^q` norm of the matrix field. -/
theorem vecCubeLpENorm_shellFlux_le_mul_cubeLpENorm {q : ℝ≥0∞}
    (Q : TriadicCube d) (omega : ShellSeq d) {r : ℕ} (hr : 1 ≤ r) (p : Vec d) :
    vecCubeLpENorm Q q (shellFlux omega r p) ≤
      ENNReal.ofReal (Book.Ch02.vecNorm p) *
        cubeLpENorm Q q
          (fun x : Vec d => (finiteShellIncrement omega (r - 1) r).toFun x) := by
  have hmono : vecCubeLpENorm Q q (shellFlux omega r p) ≤
      cubeLpENorm Q q (Book.Ch02.vecNorm p •
        (fun x : Vec d => (finiteShellIncrement omega (r - 1) r).toFun x)) := by
    refine cubeLpENorm_mono_enorm
      (continuous_hilbertifyVecField
        (continuous_shellFlux' omega r p)).aestronglyMeasurable (fun x => ?_)
    rw [norm_hilbertifyVecField_apply]
    have hrhs : ‖(Book.Ch02.vecNorm p •
          (fun y : Vec d => (finiteShellIncrement omega (r - 1) r).toFun y)) x‖ =
        Book.Ch02.vecNorm p *
          matrixOperatorNorm ((omega r) x) := by
      show ‖Book.Ch02.vecNorm p •
          (finiteShellIncrement omega (r - 1) r).toFun x‖ = _
      rw [norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (Book.Ch02.vecNorm_nonneg p),
        finiteShellIncrement_pred_apply omega hr x,
        ← matrixOperatorNorm_eq_l2_opNorm]
    rw [hrhs]
    have hop := vecNorm_matVecMul_le_matrixOperatorNorm_mul_vecNorm
      (shellReg omega r x) p
    have hreg : shellReg omega r x = (omega r) x := by
      simp only [shellReg, ShellField.forgetShell_apply]
    rw [hreg] at hop
    calc Book.Ch02.vecNorm (shellFlux omega r p x)
        ≤ matrixOperatorNorm ((omega r) x) * Book.Ch02.vecNorm p := hop
      _ = Book.Ch02.vecNorm p * matrixOperatorNorm ((omega r) x) := mul_comm _ _
  refine le_trans hmono (le_of_eq ?_)
  rw [cubeLpENorm_const_smul, ← ofReal_norm, Real.norm_eq_abs,
    abs_of_nonneg (Book.Ch02.vecNorm_nonneg p)]

/-! ## The dimension-only constant -/

private theorem lpClauseConst_four_nonneg (d : ℕ) : 0 ≤ lpClauseConst d 4 := by
  rw [lpClauseConst]
  exact le_max_of_le_left
    (Real.rpow_nonneg (largeCubePthMomentMeanConst_nonneg (by norm_num)) _)

/-- The dimension-only constant of the scale-free `L̲⁴` amplitude: the larger of
six times the increment clause's constant at `p = 4` and the Poincare constant
of the shells above the cube scale. -/
def shellFluxL4Const (d : ℕ) : ℝ :=
  max (6 * lpClauseConst d 4) (shellFluxLipConst d)

theorem shellFluxL4Const_nonneg (d : ℕ) : 0 ≤ shellFluxL4Const d := by
  rw [shellFluxL4Const]
  exact le_max_of_le_right (shellFluxLipConst_nonneg d)

/-! ## Elementary exponent identities -/

private theorem rpow_four_half : (4 : ℝ) ^ ((1 : ℝ) / 2) = 2 := by
  rw [show (4 : ℝ) = (2 : ℝ) ^ (2 : ℕ) by norm_num,
    ← Real.rpow_natCast (2 : ℝ) 2,
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

private theorem one_shell_gap {r : ℕ} (hr : 1 ≤ r) :
    ((r - (r - 1) : ℕ) : ℝ) = 1 := by
  have h : r - (r - 1) = 1 := by omega
  rw [h]
  norm_num

/-! ## Two elementary steps -/

/-- Shifting a `Gamma₂` envelope by a nonnegative deterministic constant and
scaling by a nonnegative factor. -/
private theorem isBigO_shifted_max {X : ShellSeq d → ℝ} {Cb B vp : ℝ}
    (hCb : (0 : ℝ) ≤ Cb) (hvp : (0 : ℝ) ≤ vp)
    (hX : IsBigO P.toMeasure (gammaSigma 2) X B) :
    IsBigO P.toMeasure (gammaSigma 2)
      (fun omega : ShellSeq d => 2 * vp * (Cb + max (X omega) 0))
      (2 * vp * B + 2 * vp * Cb) := by
  have hvp2 : (0 : ℝ) ≤ 2 * vp := by linarith only [hvp]
  have hXmax : IsBigO P.toMeasure (gammaSigma 2)
      (fun omega : ShellSeq d => max (X omega) 0) B := by
    refine hX.of_abs_le (fun omega => ?_)
    rcases le_or_gt 0 (X omega) with h | h
    · rw [max_eq_left h]
    · rw [max_eq_right h.le, abs_zero]
      exact abs_nonneg _
  have hW := hXmax.const_mul (c := 2 * vp) hvp2
  have hle : ∀ omega : ShellSeq d,
      |2 * vp * (Cb + max (X omega) 0)| ≤
        |2 * vp * max (X omega) 0| + 2 * vp * Cb := by
    intro omega
    have hm0 : (0 : ℝ) ≤ max (X omega) 0 := le_max_right _ _
    have hsum : (0 : ℝ) ≤ Cb + max (X omega) 0 := by linarith only [hCb, hm0]
    rw [abs_of_nonneg (mul_nonneg hvp2 hsum),
      abs_of_nonneg (mul_nonneg hvp2 hm0)]
    exact le_of_eq (by ring)
  exact SuperdiffusionCLT.Section2.Annealed.isBigO_gammaSigma_of_abs_le_add_const
    (mul_nonneg hvp2 hCb) hle hW

/-- The centred `L̲⁴` norm of the shell flux against a bound on the matrix
carrier of the increment clause. -/
private theorem pointwise_shellFluxL4_of_cubeLpENorm {m r : ℕ} (hr : 1 ≤ r)
    (omega : ShellSeq d) (p : Vec d) {A B : ℝ} (hAB : A ≤ B)
    (hpt : cubeLpENorm (originCube d (m : ℤ)) (4 : ℝ≥0∞)
        (fun x : Vec d => (finiteShellIncrement omega (r - 1) r).toFun x) ≤
      ENNReal.ofReal A) :
    vecCubeLpENorm (originCube d (m : ℤ)) 4
      (fun x => shellFlux omega r p x -
        volumeAverageVec (cubeSet (originCube d (m : ℤ)))
          (shellFlux omega r p)) ≤
      ENNReal.ofReal (2 * Book.Ch02.vecNorm p * B) := by
  have hvp : (0 : ℝ) ≤ Book.Ch02.vecNorm p := Book.Ch02.vecNorm_nonneg p
  have h1 := vecCubeLpENorm4_sub_volumeAverageVec_le_shellFlux
    (Q := originCube d (m : ℤ)) (r := r) (omega := omega) (p := p)
  have h2 := vecCubeLpENorm_shellFlux_le_mul_cubeLpENorm (q := 4)
    (originCube d (m : ℤ)) omega hr p
  have htwo : (2 : ℝ≥0∞) = ENNReal.ofReal (2 : ℝ) := by
    simp only [ENNReal.ofReal_ofNat]
  have hprod : (2 : ℝ≥0∞) * (ENNReal.ofReal (Book.Ch02.vecNorm p) *
      ENNReal.ofReal A) = ENNReal.ofReal (2 * (Book.Ch02.vecNorm p * A)) := by
    rw [htwo, ← ENNReal.ofReal_mul hvp,
      ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
  have hfinal : 2 * (Book.Ch02.vecNorm p * A) ≤
      2 * Book.Ch02.vecNorm p * B := by
    have hstep := mul_le_mul_of_nonneg_left hAB
      (by linarith only [hvp] : (0 : ℝ) ≤ 2 * Book.Ch02.vecNorm p)
    have hrw : 2 * Book.Ch02.vecNorm p * A = 2 * (Book.Ch02.vecNorm p * A) := by
      ring
    linarith only [hstep, hrw]
  calc vecCubeLpENorm (originCube d (m : ℤ)) 4
        (fun x => shellFlux omega r p x -
          volumeAverageVec (cubeSet (originCube d (m : ℤ)))
            (shellFlux omega r p))
      ≤ 2 * vecCubeLpENorm (originCube d (m : ℤ)) 4 (shellFlux omega r p) := h1
    _ ≤ 2 * (ENNReal.ofReal (Book.Ch02.vecNorm p) *
          cubeLpENorm (originCube d (m : ℤ)) 4
            (fun x : Vec d =>
              (finiteShellIncrement omega (r - 1) r).toFun x)) :=
        mul_le_mul_right h2 2
    _ ≤ 2 * (ENNReal.ofReal (Book.Ch02.vecNorm p) * ENNReal.ofReal A) :=
        mul_le_mul_right (mul_le_mul_right hpt _) 2
    _ = ENNReal.ofReal (2 * (Book.Ch02.vecNorm p * A)) := hprod
    _ ≤ ENNReal.ofReal (2 * Book.Ch02.vecNorm p * B) :=
        ENNReal.ofReal_le_ofReal hfinal

/-! ## The half below the cube scale -/

/-- **The `L̲⁴` bound for the shells at or below the cube scale**
(the `e.kmn.Lp` half at `p = 4`).  The single-shell increment makes the printed
factor `(m-n)^{1/2}` equal to one, so both the deterministic term and the `Gamma₂` amplitude of the
increment clause are free of the cube scale. -/
theorem exists_shellFluxL4_belowCubeScale
    (hPrefix : ShellLawPrefix d P) (hJ1V2 : ShellLawJ1Restriction d P)
    (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P)
    {m r : ℕ} (hr : 1 ≤ r) (hrm : r ≤ m) (p : Vec d) :
    ∃ Z : ShellSeq d → ℝ, (∀ omega, 0 ≤ Z omega) ∧ Measurable Z ∧
      IsBigO P.toMeasure (gammaSigma 2) Z
        (6 * lpClauseConst d 4 * Book.Ch02.vecNorm p) ∧
      ∀ omega : ShellSeq d,
        vecCubeLpENorm (originCube d (m : ℤ)) 4
          (fun x => shellFlux omega r p x -
            volumeAverageVec (cubeSet (originCube d (m : ℤ)))
              (shellFlux omega r p)) ≤
          ENNReal.ofReal (Z omega) := by
  classical
  obtain ⟨X, hXmeas, hXtail, hXpt⟩ :=
    exists_witness_cubeLpENorm_finiteShellIncrement hPrefix hJ1V2 hJ2 hJ3 hJ4
      ((1 : ℝ) / 2) 4 (by norm_num) (by norm_num) (by norm_num)
      (lpClauseConst d 4) le_rfl (show r - 1 < r by omega) hrm
  have hCb : (0 : ℝ) ≤ lpClauseConst d 4 := lpClauseConst_four_nonneg d
  have hvp : (0 : ℝ) ≤ Book.Ch02.vecNorm p := Book.Ch02.vecNorm_nonneg p
  refine ⟨fun omega => 2 * Book.Ch02.vecNorm p *
      (lpClauseConst d 4 + max (X omega) 0), ?_, ?_, ?_, ?_⟩
  · intro omega
    have h1 : (0 : ℝ) ≤ lpClauseConst d 4 + max (X omega) 0 := by
      have := le_max_right (X omega) (0 : ℝ)
      linarith only [hCb, this]
    exact mul_nonneg (by linarith only [hvp]) h1
  · exact ((measurable_const.add (hXmeas.max measurable_const)).const_mul
      (2 * Book.Ch02.vecNorm p))
  · have hdecay : (3 : ℝ) ^ (-((d : ℝ) / (2 * 4) * ((m - r : ℕ) : ℝ))) ≤ 1 := by
      refine Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) ?_
      have hnn : (0 : ℝ) ≤ (d : ℝ) / (2 * 4) * ((m - r : ℕ) : ℝ) := by positivity
      linarith only [hnn]
    have hAle : lpClauseConst d 4 * (4 : ℝ) ^ ((1 : ℝ) / 2) *
        ((r - (r - 1) : ℕ) : ℝ) ^ ((1 : ℝ) / 2) *
        (3 : ℝ) ^ (-((d : ℝ) / (2 * 4) * ((m - r : ℕ) : ℝ))) ≤
          2 * lpClauseConst d 4 := by
      rw [one_shell_gap hr, Real.one_rpow, mul_one, rpow_four_half]
      have h2Cb : (0 : ℝ) ≤ lpClauseConst d 4 * 2 := by linarith only [hCb]
      have hmul := mul_le_mul_of_nonneg_left hdecay h2Cb
      rw [mul_one] at hmul
      linarith only [hmul]
    have hres := isBigO_shifted_max (Cb := lpClauseConst d 4)
      (vp := Book.Ch02.vecNorm p) hCb hvp (hXtail.mono_scale hAle)
    exact hres.mono_scale (le_of_eq (by ring))
  · intro omega
    have hAB : lpClauseConst d 4 * ((r - (r - 1) : ℕ) : ℝ) ^ ((1 : ℝ) / 2) +
        X omega ≤ lpClauseConst d 4 + max (X omega) 0 := by
      rw [one_shell_gap hr, Real.one_rpow, mul_one]
      have := le_max_left (X omega) (0 : ℝ)
      linarith only [this]
    have hpt := hXpt omega
    rw [show ENNReal.ofReal (4 : ℝ) = (4 : ℝ≥0∞) by
      simp only [ENNReal.ofReal_ofNat]] at hpt
    exact pointwise_shellFluxL4_of_cubeLpENorm hr omega p hAB hpt

/-! ## The half above the cube scale -/

/-- **The `L̲⁴` bound for the shells above the cube scale**
(the `a.j.reg` plus Poincare half).  This is the envelope of
`ShellFluxWitnessesB.lean` read at `q = 4`; its amplitude decays in `r - m`, so
in particular it is scale free. -/
theorem exists_shellFluxL4_aboveCubeScale (hJ3 : ShellLawJ3 d P) {m r : ℕ}
    (hmr : m ≤ r) (p : Vec d) :
    ∃ Z : ShellSeq d → ℝ, (∀ omega, 0 ≤ Z omega) ∧ Measurable Z ∧
      IsBigO P.toMeasure (gammaSigma 2) Z
        (shellFluxLipConst d * Book.Ch02.vecNorm p) ∧
      ∀ omega : ShellSeq d,
        vecCubeLpENorm (originCube d (m : ℤ)) 4
          (fun x => shellFlux omega r p x -
            volumeAverageVec (cubeSet (originCube d (m : ℤ)))
              (shellFlux omega r p)) ≤
          ENNReal.ofReal (Z omega) := by
  refine ⟨shellFluxLipBound m p r, fun omega => shellFluxLipBound_nonneg m p r omega,
    measurable_shellFluxLipBound m p r, ?_, ?_⟩
  · refine (isBigO_gammaSigma_shellFluxLipBound hJ3 hmr p
      (le_refl (shellFluxLipConst d))).mono_scale ?_
    have hdecay : (3 : ℝ) ^ (-((r - m : ℕ) : ℝ)) ≤ 1 := by
      refine Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) ?_
      have hnn : (0 : ℝ) ≤ ((r - m : ℕ) : ℝ) := Nat.cast_nonneg _
      linarith only [hnn]
    have hbase : (0 : ℝ) ≤ shellFluxLipConst d * Book.Ch02.vecNorm p :=
      mul_nonneg (shellFluxLipConst_nonneg d) (Book.Ch02.vecNorm_nonneg p)
    have hmul := mul_le_mul_of_nonneg_left hdecay hbase
    rw [mul_one] at hmul
    exact hmul
  · exact fun omega =>
      vecCubeLpENorm_shellFlux_sub_le_lipBound (by norm_num) m r omega p

/-! ## The packaged witness family -/

/-- **The scale-free `L̲⁴` witness family of the centred shell flux.**  This is
the four-clause group the `l.LHS.term1` reduction consumes as `hZl4`
(in `Section3/Terms/LHSTerm1FrozenReduction.lean`), with the
constant depending on `d` alone.  Its statement is that binder verbatim.

The witness is the increment-clause envelope at `p = 4` for `r ≤ m` and the
Poincare envelope for `r > m`, exactly as the print splits the display.  In particular
**no largeness gate on the constant appears**: the value-envelope gate
`2 * shellFluxValueEnvelopeAmplitude d m ≤ Cl4` of `ShellFluxWitnesses.lean` is
an artifact of the `L^∞` union bound over the subcubes of `cu_m`, which this
route never takes. -/
theorem exists_shellFluxL4Witness_scaleFree
    (hPrefix : ShellLawPrefix d P) (hJ1V2 : ShellLawJ1Restriction d P)
    (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P)
    (S : ScaleSelection) (p : Vec d) (Cz : ℝ)
    (hCz : shellFluxL4Const d ≤ Cz) :
    ∃ Zl4 : ℕ → ShellSeq d → ℝ,
      (∀ r omega, 0 ≤ Zl4 r omega) ∧
      (∀ r, Measurable (Zl4 r)) ∧
      (∀ r ∈ Finset.Ioc S.ellPrime S.LPrime,
        IsBigO P.toMeasure (gammaSigma 2) (Zl4 r)
          (Cz * Book.Ch02.vecNorm p)) ∧
      (∀ r ∈ Finset.Ioc S.ellPrime S.LPrime, ∀ omega : ShellSeq d,
        vecCubeLpENorm (originCube d (S.m : ℤ)) 4
          (fun x => shellFlux omega r p x -
            volumeAverageVec (cubeSet (originCube d (S.m : ℤ)))
              (shellFlux omega r p)) ≤
          ENNReal.ofReal (Zl4 r omega)) := by
  classical
  have hvp : (0 : ℝ) ≤ Book.Ch02.vecNorm p := Book.Ch02.vecNorm_nonneg p
  have hbelow : 6 * lpClauseConst d 4 * Book.Ch02.vecNorm p ≤
      Cz * Book.Ch02.vecNorm p := by
    have h : 6 * lpClauseConst d 4 ≤ Cz :=
      le_trans (le_max_left _ (shellFluxLipConst d)) hCz
    exact mul_le_mul_of_nonneg_right h hvp
  have habove : shellFluxLipConst d * Book.Ch02.vecNorm p ≤
      Cz * Book.Ch02.vecNorm p := by
    have h : shellFluxLipConst d ≤ Cz :=
      le_trans (le_max_right (6 * lpClauseConst d 4) _) hCz
    exact mul_le_mul_of_nonneg_right h hvp
  have hex : ∀ r : ℕ, ∃ Z : ShellSeq d → ℝ,
      (∀ omega, 0 ≤ Z omega) ∧ Measurable Z ∧
      (S.ellPrime < r →
        IsBigO P.toMeasure (gammaSigma 2) Z (Cz * Book.Ch02.vecNorm p) ∧
        ∀ omega : ShellSeq d,
          vecCubeLpENorm (originCube d (S.m : ℤ)) 4
            (fun x => shellFlux omega r p x -
              volumeAverageVec (cubeSet (originCube d (S.m : ℤ)))
                (shellFlux omega r p)) ≤
            ENNReal.ofReal (Z omega)) := by
    intro r
    by_cases hrange : S.ellPrime < r
    · have hr : 1 ≤ r := by omega
      by_cases hrm : r ≤ S.m
      · obtain ⟨Z, h0, hm, hO, hptw⟩ :=
          exists_shellFluxL4_belowCubeScale hPrefix hJ1V2 hJ2 hJ3 hJ4 hr hrm p
        exact ⟨Z, h0, hm, fun _ => ⟨hO.mono_scale hbelow, hptw⟩⟩
      · have hmr : S.m ≤ r := by omega
        obtain ⟨Z, h0, hm, hO, hptw⟩ := exists_shellFluxL4_aboveCubeScale hJ3 hmr p
        exact ⟨Z, h0, hm, fun _ => ⟨hO.mono_scale habove, hptw⟩⟩
    · exact ⟨fun _ => 0, fun _ => le_refl 0, measurable_const,
        fun h => absurd h hrange⟩
  choose Zl4 hZ0 hZm hZmain using hex
  exact ⟨Zl4, hZ0, hZm,
    fun r hr => (hZmain r (Finset.mem_Ioc.mp hr).1).1,
    fun r hr omega => (hZmain r (Finset.mem_Ioc.mp hr).1).2 omega⟩

end

end SuperdiffusionCLT.Section3.Setup

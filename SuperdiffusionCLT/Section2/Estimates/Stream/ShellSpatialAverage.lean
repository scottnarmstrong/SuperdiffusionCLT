/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Norms.MultiscalePoincare
public import SuperdiffusionCLT.Section3.Setup.WholeSpaceEnergyC

/-!
# The one-shell spatial average of a flux

The display `e.jk.spatialavg`: for every shell `k`, every scale `h` and every centre `y`,

> `|(j_k)_{y + cu_h}| ≤ O_{Γ₂}(C 3^{-(d/2)((h - k) ∨ 0)})`.

The display itself is proved, for the matrix operator norm and at exactly the
printed amplitude, as
`isBigOWith_gammaSigma_matrixOperatorNorm_shellSpatialAverage`
(in `SpatialAverageTail`): below the shell scale by the `J3` tail transported
by the prefix stationarity, above it by the concentration of the
`3 ^ (d (h - k))` sub-cube averages, which are independent inside each colour
class of the `J1` range and centred by the negation half of `J4`.

This module gives the flux-side form of that display: the object that the
Section 3 displays `l.LHS.term1` and `l.RHS.term3` actually involve is not the matrix
average but the vector `(j_r p)_{cu_m} = matVecMul ((j_r)_{cu_m}) p`, the carrier
`Section3.Setup.shellFluxAverage`. Passing from one to the other costs exactly
the factor `|p|` of `vecNorm_matVecMul_le_matrixOperatorNorm_mul_vecNorm`, so
the amplitude is

`spatialAverageTailConst d * |p| * 3 ^ (-(d/2)((h - k) ∨ 0))`,

which is the printed `C |p| 3^{-(d/2)((h-k) ∨ 0)}` with the explicit
dimension-only constant of that display. No amplitude is weakened
anywhere in this module: the exponent `(h - k) ∨ 0` and the decay rate `d/2`
are those of the print.

## The two applied shapes

The Section 3 consumers use the display at the origin `y = 0` and on the cube
`cu_m` of the scale selection, at two exponent spellings which agree with the
one above once `max (m - r) 0` is read in `ℕ`:

* the decaying shape on the shells `r < m`, at amplitude
  `C |p| 3^{-(d/2)(m - r)}` (the `CavLt` family of the Section 3 statements); and
* the flat shape on the shells `m ≤ r`, where `(m - r : ℕ) = 0` and the decay
  factor is `1`, at amplitude `C |p|` (the `Z` family of the same statements).

Both are corollaries of the single family `exists_shellFluxAverage_bound`
below, whose observable is the quantity itself, so that the consumer's
domination hypothesis holds by reflexivity.

## Main results

* `isBigO_gammaSigma_vecNorm_matVecMul_shellSpatialAverage`: the display in the
  flux carrier, for every scale `h`, centre `y` and direction `p`.
* `measurable_vecNorm_shellFluxAverage`: the observable is measurable.
* `isBigO_gammaSigma_vecNorm_shellFluxAverage`: the display at `y = 0` on the
  cube `cu_m`, with the exponent written with the natural subtraction the
  Section 3 statements use.
* `exists_shellFluxAverage_bound`: the family of observables in the shape the
  scale-by-scale Section 3 statements consume.
* `exists_shellFluxAverage_bound_ge`: the flat shape on the shells `m ≤ r`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section2.Estimates.Stream

open Homogenization MeasureTheory ProbabilityTheory
open Homogenization.Book.Ch02
open Homogenization.IndependentSums
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Assumptions.ShellField
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section3.Setup

noncomputable section

variable {d : ℕ}
variable {P : ProbabilityMeasure (ℕ → ShellField d)}

/-! ## The display in the flux carrier -/

/-- **Manuscript display `e.jk.spatialavg`, applied to a direction.** The
Euclidean length of `(j_k)_{y + cu_h} p` has the symmetric `Γ₂` tail at
amplitude `spatialAverageTailConst d * |p| * 3 ^ (-(d/2)((h - k) ∨ 0))`.

The inputs are exactly those of the matrix display: the prefix
(dimension and per-shell stationarity), `J1`, `J3` and the negation half of
`J4`. -/
theorem isBigO_gammaSigma_vecNorm_matVecMul_shellSpatialAverage
    (hPrefix : ShellLawPrefix d P) (hJ1 : ShellLawJ1 d P) (hJ3 : ShellLawJ3 d P)
    (hJ4 : ShellLawJ4 d P) (k : ℕ) (h : ℤ) (y p : Vec d) :
    IsBigO P.toMeasure (gammaSigma 2)
      (fun omega : ℕ → ShellField d ↦
        vecNorm (matVecMul (shellSpatialAverage h y (omega k)) p))
      (spatialAverageTailConst d * vecNorm p *
        (3 : ℝ) ^ (-((d : ℝ) / 2) * ((max (h - (k : ℤ)) 0 : ℤ) : ℝ))) := by
  have hbase := isBigOWith_gammaSigma_matrixOperatorNorm_shellSpatialAverage
    hPrefix hJ1 hJ3 hJ4 k h y
  have hscaled := hbase.const_mul (c := vecNorm p) (vecNorm_nonneg p)
  have hamp : vecNorm p *
        (spatialAverageTailConst d *
          (3 : ℝ) ^ (-((d : ℝ) / 2) * ((max (h - (k : ℤ)) 0 : ℤ) : ℝ))) =
      spatialAverageTailConst d * vecNorm p *
        (3 : ℝ) ^ (-((d : ℝ) / 2) * ((max (h - (k : ℤ)) 0 : ℤ) : ℝ)) := by
    ring
  rw [hamp] at hscaled
  have hle : ∀ omega : ℕ → ShellField d,
      vecNorm (matVecMul (shellSpatialAverage h y (omega k)) p) ≤
        vecNorm p * matrixOperatorNorm (shellSpatialAverage h y (omega k)) := by
    intro omega
    have := vecNorm_matVecMul_le_matrixOperatorNorm_mul_vecNorm
      (shellSpatialAverage h y (omega k)) p
    linarith only [this]
  refine (SuperdiffusionCLT.Probability.isBigOWith_iff_isBigO_of_nonneg
    (fun omega ↦ vecNorm_nonneg _)).1 ?_
  exact hscaled.of_le hle

/-! ## The observable of the Section 3 statements -/

/-- The Euclidean length of the shell-flux cube average is measurable. -/
theorem measurable_vecNorm_shellFluxAverage (m : ℤ) (r : ℕ) (p : Vec d) :
    Measurable fun omega : ShellSeq d ↦ vecNorm (shellFluxAverage m omega r p) := by
  have hvec : Measurable fun omega : ShellSeq d ↦
      HilbertVec.ofVec (shellFluxAverage m omega r p) :=
    (HilbertVec.ofVecL d).continuous.measurable.comp
      (measurable_matVecMul_shellSpatialAverage r m 0 p)
  exact hvec.norm

/-- The exponent of the printed display, on the cube `cu_m` and at the shell
`r`, in the natural-subtraction spelling of the Section 3 statements. -/
private theorem max_sub_eq_natCast (m r : ℕ) :
    ((max ((m : ℤ) - (r : ℤ)) 0 : ℤ) : ℝ) = ((m - r : ℕ) : ℝ) := by
  have hz : max ((m : ℤ) - (r : ℤ)) 0 = ((m - r : ℕ) : ℤ) := by omega
  rw [hz]
  push_cast
  ring

/-- **`e.jk.spatialavg` on the cube `cu_m`.** The Euclidean length of the
shell-flux cube average `(j_r p)_{cu_m}` has the symmetric `Γ₂` tail at
amplitude `spatialAverageTailConst d * |p| * 3 ^ (-(d/2)(m - r))`, with the
natural subtraction `m - r`, which is `0` exactly on the shells `m ≤ r`. -/
theorem isBigO_gammaSigma_vecNorm_shellFluxAverage
    (hPrefix : ShellLawPrefix d P) (hJ1 : ShellLawJ1 d P) (hJ3 : ShellLawJ3 d P)
    (hJ4 : ShellLawJ4 d P) (m r : ℕ) (p : Vec d) :
    IsBigO P.toMeasure (gammaSigma 2)
      (fun omega : ShellSeq d ↦ vecNorm (shellFluxAverage (m : ℤ) omega r p))
      (spatialAverageTailConst d * vecNorm p *
        (3 : ℝ) ^ (-((d : ℝ) / 2) * ((m - r : ℕ) : ℝ))) := by
  have hbase := isBigO_gammaSigma_vecNorm_matVecMul_shellSpatialAverage
    hPrefix hJ1 hJ3 hJ4 r (m : ℤ) 0 p
  rw [max_sub_eq_natCast m r] at hbase
  exact hbase

/-! ## The consumer shapes -/

/-- **The family of `e.jk.spatialavg` observables consumed scale by scale.**
For a fixed cube scale `m` and direction `p`, the observable is the quantity
itself, so the domination clause holds by reflexivity, and its amplitude is the
printed one with the explicit dimension-only constant.

This is simultaneously the `CavLt` family and, on the shells `m ≤ r` where the
decay factor is `1`, the `Z` family of the
Section 3 statements. -/
theorem exists_shellFluxAverage_bound
    (hPrefix : ShellLawPrefix d P) (hJ1 : ShellLawJ1 d P) (hJ3 : ShellLawJ3 d P)
    (hJ4 : ShellLawJ4 d P) (m : ℕ) (p : Vec d) :
    ∃ Z : ℕ → ShellSeq d → ℝ, (∀ r omega, 0 ≤ Z r omega) ∧
      (∀ r, Measurable (Z r)) ∧
      (∀ r, IsBigO P.toMeasure (gammaSigma 2) (Z r)
        (spatialAverageTailConst d * vecNorm p *
          (3 : ℝ) ^ (-((d : ℝ) / 2) * ((m - r : ℕ) : ℝ)))) ∧
      (∀ (r : ℕ) (omega : ShellSeq d),
        vecNorm (shellFluxAverage (m : ℤ) omega r p) ≤ Z r omega) :=
  ⟨fun r omega ↦ vecNorm (shellFluxAverage (m : ℤ) omega r p),
    fun _ _ ↦ vecNorm_nonneg _,
    fun r ↦ measurable_vecNorm_shellFluxAverage (m : ℤ) r p,
    fun r ↦ isBigO_gammaSigma_vecNorm_shellFluxAverage hPrefix hJ1 hJ3 hJ4 m r p,
    fun _ _ ↦ le_rfl⟩

/-- **The flat shape on the shells `m ≤ r`**: the `Z` family of the
Section 3 statements, at amplitude
`spatialAverageTailConst d * |p|`.  The print uses the decaying form only below
the cube scale, and on `m ≤ r` the natural subtraction `m - r` vanishes, so the
same observable carries the flat amplitude. -/
theorem exists_shellFluxAverage_bound_ge
    (hPrefix : ShellLawPrefix d P) (hJ1 : ShellLawJ1 d P) (hJ3 : ShellLawJ3 d P)
    (hJ4 : ShellLawJ4 d P) (m : ℕ) (p : Vec d) :
    ∃ Z : ℕ → ShellSeq d → ℝ, (∀ r omega, 0 ≤ Z r omega) ∧
      (∀ r, Measurable (Z r)) ∧
      (∀ r, m ≤ r → IsBigO P.toMeasure (gammaSigma 2) (Z r)
        (spatialAverageTailConst d * vecNorm p)) ∧
      (∀ (r : ℕ) (omega : ShellSeq d),
        vecNorm (shellFluxAverage (m : ℤ) omega r p) ≤ Z r omega) := by
  refine ⟨fun r omega ↦ vecNorm (shellFluxAverage (m : ℤ) omega r p),
    fun _ _ ↦ vecNorm_nonneg _,
    fun r ↦ measurable_vecNorm_shellFluxAverage (m : ℤ) r p, ?_,
    fun _ _ ↦ le_rfl⟩
  intro r hr
  have hbase := isBigO_gammaSigma_vecNorm_shellFluxAverage hPrefix hJ1 hJ3 hJ4
    m r p
  have hzero : ((m - r : ℕ) : ℝ) = 0 := by
    have : m - r = 0 := Nat.sub_eq_zero_of_le hr
    rw [this]
    norm_num
  rw [hzero] at hbase
  simpa only [mul_zero, Real.rpow_zero, mul_one] using hbase

end

end SuperdiffusionCLT.Section2.Estimates.Stream

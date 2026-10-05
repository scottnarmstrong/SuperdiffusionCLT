/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Norms.NegativeHatOrderOne
public import SuperdiffusionCLT.Section3.Setup.WholeSpaceEnergyG

/-!
# The per-shell estimates of `l.LHS.term1` in the order-one hatted carrier

The per-shell estimates in the proof of `l.LHS.term1`, restated with the
vector-field hatted negative norm read at ORDER ONE.

The norm `‖F‖_{Ĥ̲^{-1}(U)}` is read as `Section2.Norms.vecHatNegENormOrderOne`: the
supremum of `⨍_U F·∇g` over the smooth mean-zero `g` whose test gradient field
satisfies `‖∇g‖_{L̲²(U)} + |U|^{1/d}‖∇²g‖_{L̲²(U)} ≤ 1`.  The chain
`WholeSpaceEnergyC.lean`-`WholeSpaceEnergyG.lean` binds the two Section 2
displays `e.jk.Hminus.endpoint` (`hZhmBound`) and `e.abstract.response.ND.weak`
(`hNDweak`) in the order-zero carrier `Section3.ResponseFields.vecHatNegENorm`,
in which the endpoint display is false.  This module and its companion
`WholeSpaceEnergyOrderOneB.lean` restate exactly the theorems of that chain which
mention the carrier, with the order-one norm in its place; every other step of
the chain is reused verbatim.

Two things change in the statements, and nothing else:

* the carrier `vecHatNegENorm` becomes `Section2.Norms.vecHatNegENormOrderOne`; and
* the printed prefactor `(m−r)^{1/2}` of `e.jk.Hminus.endpoint` becomes
  `1 + (m−r)`, which is the honest amplitude of the order-one endpoint
  (`ShellHminusEndpointOrderOneB.lean`): the `ℓ¹`
  multiscale Poincaré form the paper itself states adds `1 + (l−k)` terms
  of size `3^{-(l−k)}`.  Through the exponent `1/5` of
  `e.abstract.response.ND.weak` this turns the per-shell amplitude
  `C|p|(m−r)^{1/10}3^{-(m−r)/5}` into `C|p|(1+(m−r))^{1/5}3^{-(m−r)/5}`.

The summed constant is unaffected in kind: `∑_{k ≥ 0} (1+k)^{1/5}3^{-k/5}`
converges, and is bounded here by the explicit `shellPolyTailSeriesConstScaled`.

## Main results

* `vecCubeLpENorm_grad_sub_le_of_responseNDWeak`: the deterministic weak
  Neumann-minus-Dirichlet step, at the order-one carrier.
* `sum_rpow_three_neg_div_ten_le`, `shellPolyTailSeriesConstScaled`,
  `sum_rpow_one_add_mul_three_neg_div_five_le`: the new uniform series bound.
* `shellGapAmplitude`, `sum_shellGapAmplitude_le`, `shellGapSumConst`,
  `isBigO_gammaSigma_sum_of_shellGapAmplitude`: the per-shell amplitude of
  the two branches and its uniform finite sum.
* `shellResponseGap_lt`, `shellResponseGap_ge`: the two per-shell
  displays `e.wNr.vs.wDr.r.small` and its `r ≥ m` companion.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Setup

open MeasureTheory
open ProbabilityTheory
open Homogenization
open Homogenization.Book.Ch02
open Homogenization.IndependentSums
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Probability
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Norms
open SuperdiffusionCLT.Section3.ResponseFields
open scoped BigOperators ENNReal

noncomputable section

variable {d : ℕ}

/-! ## The deterministic weak Neumann-minus-Dirichlet step -/

/-- **`e.abstract.response.ND.weak` in amplitude form, at order one**.
The hatted negative norm is read at order one; the proof is three monotonicity steps. -/
theorem vecCubeLpENorm_grad_sub_le_of_responseNDWeak
    {Q : TriadicCube d} {F : Vec d → Vec d}
    {wD : H10Function (openCubeSet Q)} {wN : H1MeanZeroFunction (openCubeSet Q)}
    {Cnd : ℝ≥0∞} {a b c : ℝ}
    (hNDweak : vecCubeLpENorm Q 2
        (fun x => wN.toH1Function.grad x - wD.toH1Function.grad x) ≤
      Cnd * (vecHatNegENormOrderOne Q
            (fun x => F x - volumeAverageVec (cubeSet Q) F)) ^ ((1 : ℝ) / 5) *
          (vecCubeLpENorm Q 4
            (fun x => F x - volumeAverageVec (cubeSet Q) F)) ^ ((4 : ℝ) / 5) +
        Cnd * ‖HilbertVec.ofVec (volumeAverageVec (cubeSet Q) F)‖ₑ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hHm : vecHatNegENormOrderOne Q (fun x => F x - volumeAverageVec (cubeSet Q) F) ≤
      ENNReal.ofReal a)
    (hL4 : vecCubeLpENorm Q 4 (fun x => F x - volumeAverageVec (cubeSet Q) F) ≤
      ENNReal.ofReal b)
    (hAvg : vecNorm (volumeAverageVec (cubeSet Q) F) ≤ c) :
    vecCubeLpENorm Q 2
        (fun x => wN.toH1Function.grad x - wD.toH1Function.grad x) ≤
      Cnd * ENNReal.ofReal (a ^ ((1 : ℝ) / 5) * b ^ ((4 : ℝ) / 5) + c) := by
  refine hNDweak.trans ?_
  have h1 : (vecHatNegENormOrderOne Q
        (fun x => F x - volumeAverageVec (cubeSet Q) F)) ^ ((1 : ℝ) / 5) ≤
      ENNReal.ofReal (a ^ ((1 : ℝ) / 5)) := by
    rw [← ENNReal.ofReal_rpow_of_nonneg ha (by norm_num)]
    exact ENNReal.rpow_le_rpow hHm (by norm_num)
  have h2 : (vecCubeLpENorm Q 4
        (fun x => F x - volumeAverageVec (cubeSet Q) F)) ^ ((4 : ℝ) / 5) ≤
      ENNReal.ofReal (b ^ ((4 : ℝ) / 5)) := by
    rw [← ENNReal.ofReal_rpow_of_nonneg hb (by norm_num)]
    exact ENNReal.rpow_le_rpow hL4 (by norm_num)
  have h3 : ‖HilbertVec.ofVec (volumeAverageVec (cubeSet Q) F)‖ₑ ≤
      ENNReal.ofReal c := by
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal hAvg
  calc
    Cnd * (vecHatNegENormOrderOne Q
          (fun x => F x - volumeAverageVec (cubeSet Q) F)) ^ ((1 : ℝ) / 5) *
        (vecCubeLpENorm Q 4
          (fun x => F x - volumeAverageVec (cubeSet Q) F)) ^ ((4 : ℝ) / 5) +
      Cnd * ‖HilbertVec.ofVec (volumeAverageVec (cubeSet Q) F)‖ₑ ≤
        Cnd * ENNReal.ofReal (a ^ ((1 : ℝ) / 5)) *
            ENNReal.ofReal (b ^ ((4 : ℝ) / 5)) +
          Cnd * ENNReal.ofReal c :=
      add_le_add (mul_le_mul' (mul_le_mul' (le_refl Cnd) h1) h2)
        (mul_le_mul' (le_refl Cnd) h3)
    _ = Cnd * ENNReal.ofReal (a ^ ((1 : ℝ) / 5) * b ^ ((4 : ℝ) / 5) + c) := by
      rw [ENNReal.ofReal_add (by positivity) hc,
        ENNReal.ofReal_mul (Real.rpow_nonneg ha _), mul_add, mul_assoc]


/-! ## The new uniform series bound -/

/-- **The geometric series `Σ_{j ≥ 0} 3^{−j/10}`**, bounded uniformly over an
arbitrary finite set of exponents.  Its sum is the constant
`shellPolyTailSeriesConst` of `WholeSpaceEnergyF.lean`. -/
theorem sum_rpow_three_neg_div_ten_le (s : Finset ℕ) :
    ∑ j ∈ s, (3 : ℝ) ^ (-((j : ℝ) / 10)) ≤ shellPolyTailSeriesConst := by
  have hq0 : (0 : ℝ) ≤ (3 : ℝ) ^ (-(1 : ℝ) / 10) :=
    (Real.rpow_pos_of_pos (by norm_num) _).le
  have hq1 : (3 : ℝ) ^ (-(1 : ℝ) / 10) < 1 := by
    exact Real.rpow_lt_one_of_one_lt_of_neg (x := (3 : ℝ))
      (z := -(1 : ℝ) / 10) (by norm_num) (by norm_num)
  have hsum : Summable (fun j : ℕ => ((3 : ℝ) ^ (-(1 : ℝ) / 10)) ^ j) :=
    summable_geometric_of_lt_one hq0 hq1
  have h := hsum.sum_le_tsum s (fun j _ => pow_nonneg hq0 j)
  rw [tsum_geometric_of_lt_one hq0 hq1] at h
  refine le_trans (le_of_eq ?_) h
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Real.rpow_natCast ((3 : ℝ) ^ (-(1 : ℝ) / 10)) j,
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
  ring_nf

/-- The polynomial factor of the order-one endpoint is absorbed by
`(1 + k)^2 ≤ 4·3^k`, which holds for every natural `k`. -/
private theorem one_add_sq_le_four_mul_three_pow (n : ℕ) :
    (1 + n) ^ 2 ≤ 4 * 3 ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    have h3 : n < 3 ^ n := Nat.lt_pow_self (by norm_num)
    have hA : 1 ≤ 3 ^ n := Nat.one_le_pow _ _ (by norm_num)
    have hexp : (1 + (n + 1)) ^ 2 = (1 + n) ^ 2 + (2 * n + 3) := by ring
    have hp : (3 : ℕ) ^ (n + 1) = 3 * 3 ^ n := by ring
    rw [hexp, hp]
    generalize hB : (1 + n) ^ 2 = B at ih ⊢
    generalize hA3 : (3 : ℕ) ^ n = A at ih h3 hA ⊢
    omega

/-- The per-term absorption `(1+k)^{1/5} 3^{−k/5} ≤ 4^{1/10} 3^{−k/10}`. -/
private theorem one_add_rpow_mul_three_neg_le (k : ℕ) :
    (1 + (k : ℝ)) ^ ((1 : ℝ) / 5) * (3 : ℝ) ^ (-((k : ℝ) / 5)) ≤
      (4 : ℝ) ^ ((1 : ℝ) / 10) * (3 : ℝ) ^ (-((k : ℝ) / 10)) := by
  have hk1 : (0 : ℝ) ≤ 1 + (k : ℝ) := by positivity
  have hreal : ((1 : ℝ) + (k : ℝ)) ^ (2 : ℕ) ≤ 4 * (3 : ℝ) ^ (k : ℕ) := by
    have h := one_add_sq_le_four_mul_three_pow k
    exact_mod_cast h
  have h1 : ((1 : ℝ) + (k : ℝ)) ^ ((1 : ℝ) / 5) =
      (((1 : ℝ) + (k : ℝ)) ^ (2 : ℕ)) ^ ((1 : ℝ) / 10) := by
    rw [← Real.rpow_natCast ((1 : ℝ) + (k : ℝ)) 2, ← Real.rpow_mul hk1]
    norm_num
  have h2 : (((1 : ℝ) + (k : ℝ)) ^ (2 : ℕ)) ^ ((1 : ℝ) / 10) ≤
      (4 * (3 : ℝ) ^ (k : ℕ)) ^ ((1 : ℝ) / 10) :=
    Real.rpow_le_rpow (by positivity) hreal (by norm_num)
  have h3 : (4 * (3 : ℝ) ^ (k : ℕ)) ^ ((1 : ℝ) / 10) =
      (4 : ℝ) ^ ((1 : ℝ) / 10) * (3 : ℝ) ^ ((k : ℝ) / 10) := by
    rw [Real.mul_rpow (by norm_num) (by positivity),
      ← Real.rpow_natCast (3 : ℝ) k, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    ring_nf
  have h5 : (0 : ℝ) < (3 : ℝ) ^ (-((k : ℝ) / 5)) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hcomb : ((1 : ℝ) + (k : ℝ)) ^ ((1 : ℝ) / 5) ≤
      (4 : ℝ) ^ ((1 : ℝ) / 10) * (3 : ℝ) ^ ((k : ℝ) / 10) := by
    rw [h1, ← h3]
    exact h2
  calc (1 + (k : ℝ)) ^ ((1 : ℝ) / 5) * (3 : ℝ) ^ (-((k : ℝ) / 5))
      ≤ ((4 : ℝ) ^ ((1 : ℝ) / 10) * (3 : ℝ) ^ ((k : ℝ) / 10)) *
          (3 : ℝ) ^ (-((k : ℝ) / 5)) := mul_le_mul_of_nonneg_right hcomb h5.le
    _ = (4 : ℝ) ^ ((1 : ℝ) / 10) *
          ((3 : ℝ) ^ ((k : ℝ) / 10) * (3 : ℝ) ^ (-((k : ℝ) / 5))) := by ring
    _ = (4 : ℝ) ^ ((1 : ℝ) / 10) * (3 : ℝ) ^ (-((k : ℝ) / 10)) := by
        rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
        ring_nf

/-- The sum `Σ_{k ≥ 0} (1+k)^{1/5} 3^{−k/5}`, bounded by the explicit constant
`4^{1/10}(1 − 3^{−1/10})⁻¹`.  This is the order-one replacement of
`shellPolyTailSeriesConst`, and like it a pure number: the summation over the
shells is uniform in the scale selection. -/
def shellPolyTailSeriesConstScaled : ℝ :=
  (4 : ℝ) ^ ((1 : ℝ) / 10) * shellPolyTailSeriesConst

theorem shellPolyTailSeriesConstScaled_pos : 0 < shellPolyTailSeriesConstScaled := by
  have h1 : (0 : ℝ) < (4 : ℝ) ^ ((1 : ℝ) / 10) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have h2 : (0 : ℝ) < shellPolyTailSeriesConst := shellPolyTailSeriesConst_pos
  rw [shellPolyTailSeriesConstScaled]
  positivity

/-- **The order-one polynomially weighted geometric series**, bounded uniformly
over an arbitrary finite set of exponents. -/
theorem sum_rpow_one_add_mul_three_neg_div_five_le (s : Finset ℕ) :
    ∑ k ∈ s, (1 + (k : ℝ)) ^ ((1 : ℝ) / 5) * (3 : ℝ) ^ (-((k : ℝ) / 5)) ≤
      shellPolyTailSeriesConstScaled := by
  refine le_trans (Finset.sum_le_sum fun k _ => one_add_rpow_mul_three_neg_le k) ?_
  rw [← Finset.mul_sum, shellPolyTailSeriesConstScaled]
  exact mul_le_mul_of_nonneg_left (sum_rpow_three_neg_div_ten_le s)
    (Real.rpow_nonneg (by norm_num) _)

/-! ## The per-shell amplitude and its finite sum -/

/-- The order-one per-shell amplitude at the shell `r` and the cube scale `m`:
the `r ≥ m` amplitude `Cge·B·3^{−(r−m)/5}` above the cube scale, unchanged,
and the `r < m` amplitude `Clt·B·(1+(m−r))^{1/5} 3^{−(m−r)/5}` below it, in
which the printed `(m−r)^{1/10}` is replaced by `(1+(m−r))^{1/5}`. -/
def shellGapAmplitude (Clt Cge B : ℝ) (m r : ℕ) : ℝ :=
  if m ≤ r then Cge * B * (3 : ℝ) ^ (-(((r - m : ℕ) : ℝ) / 5))
  else Clt * B * (1 + ((m - r : ℕ) : ℝ)) ^ ((1 : ℝ) / 5) *
    (3 : ℝ) ^ (-(((m - r : ℕ) : ℝ) / 5))

theorem shellGapAmplitude_pos {Clt Cge B : ℝ} (hClt : 0 < Clt)
    (hCge : 0 < Cge) (hB : 0 < B) (m r : ℕ) :
    0 < shellGapAmplitude Clt Cge B m r := by
  rw [shellGapAmplitude]
  split_ifs with hcase
  · have h3 : (0 : ℝ) < (3 : ℝ) ^ (-(((r - m : ℕ) : ℝ) / 5)) :=
      Real.rpow_pos_of_pos (by norm_num) _
    positivity
  · have hk : (0 : ℝ) < 1 + ((m - r : ℕ) : ℝ) := by positivity
    have hk5 : (0 : ℝ) < (1 + ((m - r : ℕ) : ℝ)) ^ ((1 : ℝ) / 5) :=
      Real.rpow_pos_of_pos hk _
    have h3 : (0 : ℝ) < (3 : ℝ) ^ (-(((m - r : ℕ) : ℝ) / 5)) :=
      Real.rpow_pos_of_pos (by norm_num) _
    positivity

/-- **The uniform amplitude sum at order one.**  Over an arbitrary finite set of
shells the two branch amplitudes add up to
`Clt·B·shellPolyTailSeriesConstScaled + Cge·B·shellTailSeriesConst`, with no
dependence on the shells. -/
theorem sum_shellGapAmplitude_le (m : ℕ) (t : Finset ℕ) {Clt Cge B : ℝ}
    (hClt : 0 ≤ Clt) (hCge : 0 ≤ Cge) (hB : 0 ≤ B) :
    ∑ r ∈ t, shellGapAmplitude Clt Cge B m r ≤
      Clt * B * shellPolyTailSeriesConstScaled + Cge * B * shellTailSeriesConst := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not t (fun r => m ≤ r)]
  have hge : ∑ r ∈ t.filter (fun r => m ≤ r),
      shellGapAmplitude Clt Cge B m r ≤ Cge * B * shellTailSeriesConst := by
    have hrw : ∑ r ∈ t.filter (fun r => m ≤ r),
          shellGapAmplitude Clt Cge B m r =
        Cge * B * ∑ r ∈ t.filter (fun r => m ≤ r),
          (3 : ℝ) ^ (-(((r - m : ℕ) : ℝ) / 5)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun r hr => ?_
      rw [shellGapAmplitude, ite_eq_left (Finset.mem_filter.1 hr).2]
    rw [hrw]
    have hinj : ∀ x ∈ t.filter (fun r => m ≤ r),
        ∀ y ∈ t.filter (fun r => m ≤ r), x - m = y - m → x = y := by
      intro x hx y hy hxy
      have hx' := (Finset.mem_filter.1 hx).2
      have hy' := (Finset.mem_filter.1 hy).2
      omega
    have himg : ∑ r ∈ t.filter (fun r => m ≤ r),
          (3 : ℝ) ^ (-(((r - m : ℕ) : ℝ) / 5)) =
        ∑ j ∈ (t.filter (fun r => m ≤ r)).image (fun r => r - m),
          (3 : ℝ) ^ (-((j : ℝ) / 5)) :=
      (Finset.sum_image
        (f := fun j : ℕ => (3 : ℝ) ^ (-((j : ℝ) / 5))) hinj).symm
    rw [himg]
    exact mul_le_mul_of_nonneg_left (sum_rpow_three_neg_div_five_le _)
      (by positivity)
  have hlt : ∑ r ∈ t.filter (fun r => ¬ m ≤ r),
      shellGapAmplitude Clt Cge B m r ≤
        Clt * B * shellPolyTailSeriesConstScaled := by
    have hrw : ∑ r ∈ t.filter (fun r => ¬ m ≤ r),
          shellGapAmplitude Clt Cge B m r =
        Clt * B * ∑ r ∈ t.filter (fun r => ¬ m ≤ r),
          ((1 + ((m - r : ℕ) : ℝ)) ^ ((1 : ℝ) / 5) *
            (3 : ℝ) ^ (-(((m - r : ℕ) : ℝ) / 5))) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun r hr => ?_
      rw [shellGapAmplitude, ite_eq_right (Finset.mem_filter.1 hr).2]
      ring
    rw [hrw]
    have hinj : ∀ x ∈ t.filter (fun r => ¬ m ≤ r),
        ∀ y ∈ t.filter (fun r => ¬ m ≤ r), m - x = m - y → x = y := by
      intro x hx y hy hxy
      have hx' := (Finset.mem_filter.1 hx).2
      have hy' := (Finset.mem_filter.1 hy).2
      omega
    have himg : ∑ r ∈ t.filter (fun r => ¬ m ≤ r),
          ((1 + ((m - r : ℕ) : ℝ)) ^ ((1 : ℝ) / 5) *
            (3 : ℝ) ^ (-(((m - r : ℕ) : ℝ) / 5))) =
        ∑ k ∈ (t.filter (fun r => ¬ m ≤ r)).image (fun r => m - r),
          ((1 + (k : ℝ)) ^ ((1 : ℝ) / 5) * (3 : ℝ) ^ (-((k : ℝ) / 5))) :=
      (Finset.sum_image
        (f := fun k : ℕ =>
          (1 + (k : ℝ)) ^ ((1 : ℝ) / 5) * (3 : ℝ) ^ (-((k : ℝ) / 5))) hinj).symm
    rw [himg]
    exact mul_le_mul_of_nonneg_left
      (sum_rpow_one_add_mul_three_neg_div_five_le _) (by positivity)
  linarith only [hge, hlt]

/-! ## The `Γ₂` amplitude of the summed observable -/

/-- **The constant of the summed display `e.wN.wD.with.average.error` at order
one**: the finite-family `Γ₂` triangle constant times the two
summed geometric series.  It is a function of the input constants alone, so it
is available before the scale selection; in particular the passage from
`(m−r)^{1/10}` to `(1+(m−r))^{1/5}` leaves the LHS constant a constant in `d`,
because `Σ_k (1+k)^{1/5}3^{−k/5}` still converges. -/
def shellGapSumConst (Clt Cge : ℝ) : ℝ :=
  gammaTriangleConst 2 *
    (Clt * shellPolyTailSeriesConstScaled + Cge * shellTailSeriesConst)

theorem shellGapSumConst_pos {Clt Cge : ℝ} (hClt : 0 < Clt) (hCge : 0 < Cge) :
    0 < shellGapSumConst Clt Cge := by
  have h1 : (0 : ℝ) < gammaTriangleConst 2 := gammaTriangleConst_pos
  have h2 : (0 : ℝ) < shellPolyTailSeriesConstScaled := shellPolyTailSeriesConstScaled_pos
  have h3 : (0 : ℝ) < shellTailSeriesConst := shellTailSeriesConst_pos
  rw [shellGapSumConst]
  positivity

/-- **The summation step, probabilistically, at order one**:
`l.Gamma.sigma.triangle` followed by `sum_shellGapAmplitude_le`. -/
theorem isBigO_gammaSigma_sum_of_shellGapAmplitude
    {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    [IsFiniteMeasure mu] (m : ℕ) (t : Finset ℕ) (ht : t.Nonempty)
    {Clt Cge B : ℝ} (hClt : 0 < Clt) (hCge : 0 < Cge) (hB : 0 < B)
    (Zgap : ℕ → Omega → ℝ) (hmeas : ∀ r ∈ t, Measurable (Zgap r))
    (hbig : ∀ r ∈ t, IsBigO mu (gammaSigma 2) (Zgap r)
      (shellGapAmplitude Clt Cge B m r)) :
    IsBigO mu (gammaSigma 2) (fun omega => ∑ r ∈ t, Zgap r omega)
      (shellGapSumConst Clt Cge * B) := by
  have hsum := isBigO_finset_sum_of_isBigO_gammaSigma (μ := mu) t
    (X := Zgap) (a := fun r => shellGapAmplitude Clt Cge B m r) (σ := 2)
    (by norm_num) ht
    (fun r _ => shellGapAmplitude_pos hClt hCge hB m r) hbig hmeas
  refine hsum.mono_scale ?_
  have hamp := sum_shellGapAmplitude_le m t hClt.le hCge.le hB.le
  have hTri : (0 : ℝ) ≤ gammaTriangleConst 2 := gammaTriangleConst_pos.le
  have hmul := mul_le_mul_of_nonneg_left hamp hTri
  refine hmul.trans (le_of_eq ?_)
  rw [shellGapSumConst]
  ring

/-! ## The per-shell display `e.wNr.vs.wDr.r.small` at order one -/

private theorem shellAmplitude_rpow_mul (Chm Cl4 t k : ℝ) (hChm : 0 ≤ Chm)
    (hCl4 : 0 ≤ Cl4) (ht : 0 < t) (hk : 0 ≤ k) :
    (Chm * t * ((1 + k) * (3 : ℝ) ^ (-k))) ^ ((1 : ℝ) / 5) *
        (Cl4 * t) ^ ((4 : ℝ) / 5) =
      Chm ^ ((1 : ℝ) / 5) * Cl4 ^ ((4 : ℝ) / 5) * t *
        (1 + k) ^ ((1 : ℝ) / 5) * (3 : ℝ) ^ (-(k / 5)) := by
  have h3 : (0 : ℝ) ≤ (3 : ℝ) ^ (-k) := Real.rpow_nonneg (by norm_num) _
  have hk1 : (0 : ℝ) ≤ 1 + k := by linarith only [hk]
  have e2 : ((3 : ℝ) ^ (-k)) ^ ((1 : ℝ) / 5) = (3 : ℝ) ^ (-(k / 5)) := by
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    ring_nf
  have e3 : t ^ ((1 : ℝ) / 5) * t ^ ((4 : ℝ) / 5) = t := by
    rw [← Real.rpow_add ht]; norm_num
  rw [Real.mul_rpow (mul_nonneg hChm ht.le) (mul_nonneg hk1 h3),
    Real.mul_rpow hk1 h3, Real.mul_rpow hChm ht.le, Real.mul_rpow hCl4 ht.le, e2]
  calc
    Chm ^ ((1 : ℝ) / 5) * t ^ ((1 : ℝ) / 5) *
        ((1 + k) ^ ((1 : ℝ) / 5) * (3 : ℝ) ^ (-(k / 5))) *
        (Cl4 ^ ((4 : ℝ) / 5) * t ^ ((4 : ℝ) / 5))
        = Chm ^ ((1 : ℝ) / 5) * Cl4 ^ ((4 : ℝ) / 5) *
            (t ^ ((1 : ℝ) / 5) * t ^ ((4 : ℝ) / 5)) *
            (1 + k) ^ ((1 : ℝ) / 5) * (3 : ℝ) ^ (-(k / 5)) := by ring
    _ = _ := by rw [e3]

/-- **The per-shell display `e.wNr.vs.wDr.r.small` at order
one** for a shell `r` below the cube scale `M`:

`‖∇w̃_r − ∇w_r‖_{L̲²(cu_M)} ≤ O_{Γ₂}(C |p| (1+(M−r))^{1/5} 3^{−(M−r)/5})`.

There are two changes to the printed estimate: `hZhmBound` is read in the order-one carrier
`Section2.Norms.vecHatNegENormOrderOne`, and `hZhmBigO` carries the honest order-one
amplitude `Chm |p| (1+(M−r)) 3^{−(M−r)}` of
`ShellHminusEndpointOrderOneB.lean` in place of the printed
`Chm |p| (M−r)^{1/2} 3^{−(M−r)}`.  Through the exponent `1/5` the conclusion's
polynomial factor becomes `(1+(M−r))^{1/5}` in place of `(M−r)^{1/10}`.

The original statement's hypothesis `r < M` is not needed at order one: the
factor `(1+(M−r))^{1/5}` is bounded below by `1` for every `r`, where the
printed `(M−r)^{1/10}` was not.  `hd` is still needed, to absorb the average
term of `e.jk.spatialavg`. -/
theorem shellResponseGap_lt
    (hd : 2 ≤ d) (P : ProbabilityMeasure (ShellSeq d)) {M r : ℕ}
    (p : Vec d) (hpnorm : 0 < vecNorm p)
    (wD : ShellSeq d → H10Function (openCubeSet (originCube d (M : ℤ))))
    (wN : ShellSeq d → H1MeanZeroFunction (openCubeSet (originCube d (M : ℤ))))
    (hwD : ∀ omega : ShellSeq d,
      IsCubeDirichletResponse (originCube d (M : ℤ)) (shellFlux omega r p)
        (wD omega))
    (hwN : ∀ omega : ShellSeq d,
      IsCubeNeumannResponse (originCube d (M : ℤ)) (shellFlux omega r p)
        (wN omega))
    (Cnd : ℝ) (hCnd : 0 < Cnd)
    (hNDweak : ∀ (G : Vec d → Vec d)
      (v : H10Function (openCubeSet (originCube d (M : ℤ))))
      (vN : H1MeanZeroFunction (openCubeSet (originCube d (M : ℤ)))),
      IsCubeDirichletResponse (originCube d (M : ℤ)) G v →
      IsCubeNeumannResponse (originCube d (M : ℤ)) G vN →
      vecCubeLpENorm (originCube d (M : ℤ)) 2
          (fun x => vN.toH1Function.grad x - v.toH1Function.grad x) ≤
        ENNReal.ofReal Cnd *
            (vecHatNegENormOrderOne (originCube d (M : ℤ))
              (fun x => G x -
                volumeAverageVec (cubeSet (originCube d (M : ℤ))) G))
              ^ ((1 : ℝ) / 5) *
            (vecCubeLpENorm (originCube d (M : ℤ)) 4
              (fun x => G x -
                volumeAverageVec (cubeSet (originCube d (M : ℤ))) G))
              ^ ((4 : ℝ) / 5) +
          ENNReal.ofReal Cnd * ‖HilbertVec.ofVec
            (volumeAverageVec (cubeSet (originCube d (M : ℤ))) G)‖ₑ)
    (Chm : ℝ) (hChm : 0 < Chm) (Zhm : ShellSeq d → ℝ)
    (hZhm0 : ∀ omega, 0 ≤ Zhm omega) (hZhmMeas : Measurable Zhm)
    (hZhmBigO : IsBigO P.toMeasure (gammaSigma 2) Zhm
      (Chm * vecNorm p *
        ((1 + ((M - r : ℕ) : ℝ)) * (3 : ℝ) ^ (-((M - r : ℕ) : ℝ)))))
    (hZhmBound : ∀ omega, vecHatNegENormOrderOne (originCube d (M : ℤ))
        (fun x => shellFlux omega r p x -
          volumeAverageVec (cubeSet (originCube d (M : ℤ)))
            (shellFlux omega r p)) ≤ ENNReal.ofReal (Zhm omega))
    (Cl4 : ℝ) (hCl4 : 0 < Cl4) (Zl4 : ShellSeq d → ℝ)
    (hZl40 : ∀ omega, 0 ≤ Zl4 omega) (hZl4Meas : Measurable Zl4)
    (hZl4BigO : IsBigO P.toMeasure (gammaSigma 2) Zl4 (Cl4 * vecNorm p))
    (hZl4Bound : ∀ omega, vecCubeLpENorm (originCube d (M : ℤ)) 4
        (fun x => shellFlux omega r p x -
          volumeAverageVec (cubeSet (originCube d (M : ℤ)))
            (shellFlux omega r p)) ≤ ENNReal.ofReal (Zl4 omega))
    (Cav : ℝ) (hCav : 0 < Cav) (Zav : ShellSeq d → ℝ)
    (hZav0 : ∀ omega, 0 ≤ Zav omega) (hZavMeas : Measurable Zav)
    (hZavBigO : IsBigO P.toMeasure (gammaSigma 2) Zav
      (Cav * vecNorm p * (3 : ℝ) ^ (-((d : ℝ) / 2) * ((M - r : ℕ) : ℝ))))
    (hZavBound : ∀ omega,
      vecNorm (shellFluxAverage (M : ℤ) omega r p) ≤ Zav omega) :
    ∃ Zgap : ShellSeq d → ℝ, (∀ omega, 0 ≤ Zgap omega) ∧ Measurable Zgap ∧
      IsBigO P.toMeasure (gammaSigma 2) Zgap
        (shellResponseGapConst Cnd Chm Cl4 Cav * vecNorm p *
          (1 + ((M - r : ℕ) : ℝ)) ^ ((1 : ℝ) / 5) *
          (3 : ℝ) ^ (-(((M - r : ℕ) : ℝ) / 5))) ∧
      ∀ omega, vecCubeLpENorm (originCube d (M : ℤ)) 2
          (fun x => (wN omega).toH1Function.grad x -
            (wD omega).toH1Function.grad x) ≤ ENNReal.ofReal (Zgap omega) := by
  set k : ℝ := ((M - r : ℕ) : ℝ) with hkdef
  have hk0 : (0 : ℝ) ≤ k := by rw [hkdef]; exact Nat.cast_nonneg _
  have hk1 : (1 : ℝ) ≤ 1 + k := by linarith only [hk0]
  have hthree : (0 : ℝ) < 3 := by norm_num
  refine ⟨fun omega => Cnd * (Zhm omega ^ ((1 : ℝ) / 5) *
    Zl4 omega ^ ((4 : ℝ) / 5) + Zav omega), ?_, ?_, ?_, ?_⟩
  · intro omega
    have h1 : (0 : ℝ) ≤ Zhm omega ^ ((1 : ℝ) / 5) :=
      Real.rpow_nonneg (hZhm0 omega) _
    have h2 : (0 : ℝ) ≤ Zl4 omega ^ ((4 : ℝ) / 5) :=
      Real.rpow_nonneg (hZl40 omega) _
    have h3 := hZav0 omega
    have h4 := hCnd.le
    positivity
  · exact (((hZhmMeas.pow_const _).mul (hZl4Meas.pow_const _)).add
      hZavMeas).const_mul _
  · have hApos : (0 : ℝ) < Chm * vecNorm p * ((1 + k) * (3 : ℝ) ^ (-k)) := by
      have h1 : (0 : ℝ) < 1 + k := by linarith only [hk1]
      have h2 : (0 : ℝ) < (3 : ℝ) ^ (-k) := Real.rpow_pos_of_pos hthree _
      positivity
    have hBpos : (0 : ℝ) < Cl4 * vecNorm p := mul_pos hCl4 hpnorm
    have hCpos : (0 : ℝ) < Cav * vecNorm p *
        (3 : ℝ) ^ (-((d : ℝ) / 2) * k) := by
      have h2 : (0 : ℝ) < (3 : ℝ) ^ (-((d : ℝ) / 2) * k) :=
        Real.rpow_pos_of_pos hthree _
      positivity
    have hcomb := isBigO_gammaSigma_rpow_mul_add (mu := P.toMeasure)
      (Za := Zhm) (Zb := Zl4) (Zc := Zav) hApos hBpos hCpos
      hZhm0 hZl40 hZhmMeas hZl4Meas hZavMeas hZhmBigO hZl4BigO hZavBigO
    refine (hcomb.const_mul (c := Cnd) hCnd.le).mono_scale ?_
    set T : ℝ := vecNorm p * ((1 + k) ^ ((1 : ℝ) / 5) *
      (3 : ℝ) ^ (-(k / 5))) with hTdef
    have hkp : (0 : ℝ) ≤ (1 + k) ^ ((1 : ℝ) / 5) :=
      Real.rpow_nonneg (by linarith only [hk1]) _
    have h3p : (0 : ℝ) ≤ (3 : ℝ) ^ (-(k / 5)) := Real.rpow_nonneg hthree.le _
    have hAB : (Chm * vecNorm p * ((1 + k) * (3 : ℝ) ^ (-k))) ^ ((1 : ℝ) / 5) *
        (Cl4 * vecNorm p) ^ ((4 : ℝ) / 5) =
        Chm ^ ((1 : ℝ) / 5) * Cl4 ^ ((4 : ℝ) / 5) * T := by
      rw [shellAmplitude_rpow_mul Chm Cl4 (vecNorm p) k hChm.le hCl4.le
        hpnorm hk0, hTdef]
      ring
    have hd2 : (1 : ℝ) ≤ (d : ℝ) / 2 := by
      have hdge : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
      linarith only [hdge]
    have hmulk : k ≤ ((d : ℝ) / 2) * k := le_mul_of_one_le_left hk0 hd2
    have hexp : -((d : ℝ) / 2) * k ≤ -(k / 5) := by
      have hrw : -((d : ℝ) / 2) * k = -(((d : ℝ) / 2) * k) := by ring
      rw [hrw]
      linarith only [hmulk, hk0]
    have hCle : Cav * vecNorm p * (3 : ℝ) ^ (-((d : ℝ) / 2) * k) ≤ Cav * T := by
      have h1 : (3 : ℝ) ^ (-((d : ℝ) / 2) * k) ≤ (3 : ℝ) ^ (-(k / 5)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
      have h2 : (1 : ℝ) ≤ (1 + k) ^ ((1 : ℝ) / 5) :=
        Real.one_le_rpow hk1 (by norm_num)
      have hstep1 : (3 : ℝ) ^ (-((d : ℝ) / 2) * k) ≤
          (1 + k) ^ ((1 : ℝ) / 5) * (3 : ℝ) ^ (-(k / 5)) := by
        calc (3 : ℝ) ^ (-((d : ℝ) / 2) * k) ≤ (3 : ℝ) ^ (-(k / 5)) := h1
          _ = 1 * (3 : ℝ) ^ (-(k / 5)) := (one_mul _).symm
          _ ≤ (1 + k) ^ ((1 : ℝ) / 5) * (3 : ℝ) ^ (-(k / 5)) :=
            mul_le_mul_of_nonneg_right h2 h3p
      calc Cav * vecNorm p * (3 : ℝ) ^ (-((d : ℝ) / 2) * k) ≤
            Cav * vecNorm p * ((1 + k) ^ ((1 : ℝ) / 5) *
              (3 : ℝ) ^ (-(k / 5))) :=
              mul_le_mul_of_nonneg_left hstep1 (mul_nonneg hCav.le hpnorm.le)
        _ = Cav * T := by rw [hTdef]; ring
    have hgt := (gammaTriangleConst_pos (σ := 2)).le
    have hopc := (orliczProductConst_pos 10 (5 / 2)).le
    rw [hAB, shellResponseGapConst]
    calc Cnd * (gammaTriangleConst 2 *
          (orliczProductConst 10 (5 / 2) *
            (Chm ^ ((1 : ℝ) / 5) * Cl4 ^ ((4 : ℝ) / 5) * T) +
              Cav * vecNorm p * (3 : ℝ) ^ (-((d : ℝ) / 2) * k))) ≤
        Cnd * (gammaTriangleConst 2 *
          (orliczProductConst 10 (5 / 2) *
            (Chm ^ ((1 : ℝ) / 5) * Cl4 ^ ((4 : ℝ) / 5) * T) + Cav * T)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (add_le_add le_rfl hCle) hgt) hCnd.le
      _ = Cnd * (gammaTriangleConst 2 *
            (orliczProductConst 10 (5 / 2) *
              (Chm ^ ((1 : ℝ) / 5) * Cl4 ^ ((4 : ℝ) / 5)) + Cav)) *
            vecNorm p * (1 + k) ^ ((1 : ℝ) / 5) * (3 : ℝ) ^ (-(k / 5)) := by
          rw [hTdef]; ring
  · intro omega
    have hAvg : vecNorm (volumeAverageVec (cubeSet (originCube d (M : ℤ)))
        (shellFlux omega r p)) ≤ Zav omega := by
      rw [volumeAverageVec_shellFlux (M : ℤ) r omega p]
      exact hZavBound omega
    have h := vecCubeLpENorm_grad_sub_le_of_responseNDWeak
      (hNDweak (shellFlux omega r p) (wD omega) (wN omega) (hwD omega)
        (hwN omega))
      (hZhm0 omega) (hZl40 omega) (hZav0 omega) (hZhmBound omega)
      (hZl4Bound omega) hAvg
    rwa [← ENNReal.ofReal_mul hCnd.le] at h

/-! ## The per-shell display for `r ≥ M` at order one -/

private theorem shellAmplitudeGe_rpow_mul (Chm Cl4 t k : ℝ) (hChm : 0 ≤ Chm)
    (hCl4 : 0 ≤ Cl4) (ht : 0 < t) :
    (Chm * t * (3 : ℝ) ^ (-k)) ^ ((1 : ℝ) / 5) * (Cl4 * t) ^ ((4 : ℝ) / 5) =
      Chm ^ ((1 : ℝ) / 5) * Cl4 ^ ((4 : ℝ) / 5) * t * (3 : ℝ) ^ (-(k / 5)) := by
  have h3 : (0 : ℝ) ≤ (3 : ℝ) ^ (-k) := Real.rpow_nonneg (by norm_num) _
  have e2 : ((3 : ℝ) ^ (-k)) ^ ((1 : ℝ) / 5) = (3 : ℝ) ^ (-(k / 5)) := by
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    ring_nf
  have e3 : t ^ ((1 : ℝ) / 5) * t ^ ((4 : ℝ) / 5) = t := by
    rw [← Real.rpow_add ht]; norm_num
  rw [Real.mul_rpow (mul_nonneg hChm ht.le) h3, Real.mul_rpow hChm ht.le,
    Real.mul_rpow hCl4 ht.le, e2]
  calc
    Chm ^ ((1 : ℝ) / 5) * t ^ ((1 : ℝ) / 5) * (3 : ℝ) ^ (-(k / 5)) *
        (Cl4 ^ ((4 : ℝ) / 5) * t ^ ((4 : ℝ) / 5))
        = Chm ^ ((1 : ℝ) / 5) * Cl4 ^ ((4 : ℝ) / 5) *
            (t ^ ((1 : ℝ) / 5) * t ^ ((4 : ℝ) / 5)) *
            (3 : ℝ) ^ (-(k / 5)) := by ring
    _ = _ := by rw [e3]

/-- **The per-shell display for a shell `r` at or above the cube scale `M`, at
order one**.  The hatted negative norm of `hNDweak` and
`hZhmBound` is read at order one; the amplitude of `hZhmBigO` is the printed
`Chm |p| 3^{−(r−M)}`, unchanged, because the `r ≥ M` branch
of the print comes from Poincaré and `a.j.reg` and not from
`e.jk.Hminus.endpoint`. -/
theorem shellResponseGap_ge
    (P : ProbabilityMeasure (ShellSeq d)) {M r : ℕ}
    (p : Vec d) (hpnorm : 0 < vecNorm p)
    (wD : ShellSeq d → H10Function (openCubeSet (originCube d (M : ℤ))))
    (wN : ShellSeq d → H1MeanZeroFunction (openCubeSet (originCube d (M : ℤ))))
    (hwD : ∀ omega : ShellSeq d,
      IsCubeDirichletResponse (originCube d (M : ℤ)) (shellFlux omega r p)
        (wD omega))
    (hwN : ∀ omega : ShellSeq d,
      IsCubeNeumannResponse (originCube d (M : ℤ)) (shellFlux omega r p)
        (wN omega))
    (Cnd : ℝ) (hCnd : 0 < Cnd)
    (hNDweak : ∀ (G : Vec d → Vec d)
      (v : H10Function (openCubeSet (originCube d (M : ℤ))))
      (vN : H1MeanZeroFunction (openCubeSet (originCube d (M : ℤ)))),
      IsCubeDirichletResponse (originCube d (M : ℤ)) G v →
      IsCubeNeumannResponse (originCube d (M : ℤ)) G vN →
      vecCubeLpENorm (originCube d (M : ℤ)) 2
          (fun x => vN.toH1Function.grad x - v.toH1Function.grad x) ≤
        ENNReal.ofReal Cnd *
            (vecHatNegENormOrderOne (originCube d (M : ℤ))
              (fun x => G x -
                volumeAverageVec (cubeSet (originCube d (M : ℤ))) G))
              ^ ((1 : ℝ) / 5) *
            (vecCubeLpENorm (originCube d (M : ℤ)) 4
              (fun x => G x -
                volumeAverageVec (cubeSet (originCube d (M : ℤ))) G))
              ^ ((4 : ℝ) / 5) +
          ENNReal.ofReal Cnd * ‖HilbertVec.ofVec
            (volumeAverageVec (cubeSet (originCube d (M : ℤ))) G)‖ₑ)
    (Chm : ℝ) (hChm : 0 < Chm) (Zhm : ShellSeq d → ℝ)
    (hZhm0 : ∀ omega, 0 ≤ Zhm omega) (hZhmMeas : Measurable Zhm)
    (hZhmBigO : IsBigO P.toMeasure (gammaSigma 2) Zhm
      (Chm * vecNorm p * (3 : ℝ) ^ (-((r - M : ℕ) : ℝ))))
    (hZhmBound : ∀ omega, vecHatNegENormOrderOne (originCube d (M : ℤ))
        (fun x => shellFlux omega r p x -
          volumeAverageVec (cubeSet (originCube d (M : ℤ)))
            (shellFlux omega r p)) ≤ ENNReal.ofReal (Zhm omega))
    (Cl4 : ℝ) (hCl4 : 0 < Cl4) (Zl4 : ShellSeq d → ℝ)
    (hZl40 : ∀ omega, 0 ≤ Zl4 omega) (hZl4Meas : Measurable Zl4)
    (hZl4BigO : IsBigO P.toMeasure (gammaSigma 2) Zl4 (Cl4 * vecNorm p))
    (hZl4Bound : ∀ omega, vecCubeLpENorm (originCube d (M : ℤ)) 4
        (fun x => shellFlux omega r p x -
          volumeAverageVec (cubeSet (originCube d (M : ℤ)))
            (shellFlux omega r p)) ≤ ENNReal.ofReal (Zl4 omega)) :
    ∃ Zgap : ShellSeq d → ℝ, (∀ omega, 0 ≤ Zgap omega) ∧ Measurable Zgap ∧
      IsBigO P.toMeasure (gammaSigma 2) Zgap
        (shellResponseGapGeConst Cnd Chm Cl4 * vecNorm p *
          (3 : ℝ) ^ (-(((r - M : ℕ) : ℝ) / 5))) ∧
      ∀ omega, vecCubeLpENorm (originCube d (M : ℤ)) 2
          (fun x => (wN omega).toH1Function.grad x +
              shellFluxAverage (M : ℤ) omega r p -
            (wD omega).toH1Function.grad x) ≤ ENNReal.ofReal (Zgap omega) := by
  classical
  set k : ℝ := ((r - M : ℕ) : ℝ) with hkdef
  refine ⟨fun omega => Cnd * (Zhm omega ^ ((1 : ℝ) / 5) *
    Zl4 omega ^ ((4 : ℝ) / 5)), ?_, ?_, ?_, ?_⟩
  · intro omega
    have h1 : (0 : ℝ) ≤ Zhm omega ^ ((1 : ℝ) / 5) :=
      Real.rpow_nonneg (hZhm0 omega) _
    have h2 : (0 : ℝ) ≤ Zl4 omega ^ ((4 : ℝ) / 5) :=
      Real.rpow_nonneg (hZl40 omega) _
    have h4 := hCnd.le
    positivity
  · exact ((hZhmMeas.pow_const _).mul (hZl4Meas.pow_const _)).const_mul _
  · have hApos : (0 : ℝ) < Chm * vecNorm p * (3 : ℝ) ^ (-k) := by
      have h2 : (0 : ℝ) < (3 : ℝ) ^ (-k) :=
        Real.rpow_pos_of_pos (by norm_num) _
      positivity
    have hBpos : (0 : ℝ) < Cl4 * vecNorm p := mul_pos hCl4 hpnorm
    have hcomb := isBigO_gammaSigma_rpow_mul (mu := P.toMeasure)
      (Za := Zhm) (Zb := Zl4) hApos hBpos hZhm0 hZl40 hZhmBigO hZl4BigO
    refine (hcomb.const_mul (c := Cnd) hCnd.le).mono_scale (le_of_eq ?_)
    rw [shellAmplitudeGe_rpow_mul Chm Cl4 (vecNorm p) k hChm.le hCl4.le
      hpnorm, shellResponseGapGeConst]
    ring
  · intro omega
    have hcflux : volumeAverageVec (cubeSet (originCube d (M : ℤ)))
        (shellFlux omega r p) = shellFluxAverage (M : ℤ) omega r p :=
      volumeAverageVec_shellFlux (M : ℤ) r omega p
    have hGavg : volumeAverageVec (cubeSet (originCube d (M : ℤ)))
        (fun x => shellFlux omega r p x -
          shellFluxAverage (M : ℤ) omega r p) = 0 :=
      volumeAverageVec_shellFlux_sub_volumeAverage M r omega p
    have hDir : IsCubeDirichletResponse (originCube d (M : ℤ))
        (fun x => shellFlux omega r p x -
          shellFluxAverage (M : ℤ) omega r p) (wD omega) := by
      have h := isCubeDirichletResponse_shellFlux_sub_volumeAverage_iff.1
        (hwD omega)
      rwa [hcflux] at h
    have hNeu : IsCubeNeumannResponse (originCube d (M : ℤ))
        (fun x => shellFlux omega r p x - shellFluxAverage (M : ℤ) omega r p)
        (wN omega + linearH1MeanZeroFunction (originCube d (M : ℤ))
          (shellFluxAverage (M : ℤ) omega r p)) :=
      isCubeNeumannResponse_sub_const
        (memVectorL2_shellFlux (originCube d (M : ℤ)) r omega p) (hwN omega) _
    have hfun : (fun x => (shellFlux omega r p x -
          shellFluxAverage (M : ℤ) omega r p) - (0 : Vec d)) =
        fun x => shellFlux omega r p x -
          volumeAverageVec (cubeSet (originCube d (M : ℤ)))
            (shellFlux omega r p) := by
      funext x
      rw [hcflux, sub_zero]
    have hHm : vecHatNegENormOrderOne (originCube d (M : ℤ))
        (fun x => (fun y => shellFlux omega r p y -
              shellFluxAverage (M : ℤ) omega r p) x -
          volumeAverageVec (cubeSet (originCube d (M : ℤ)))
            (fun y => shellFlux omega r p y -
              shellFluxAverage (M : ℤ) omega r p)) ≤
        ENNReal.ofReal (Zhm omega) := by
      rw [hGavg, hfun]
      exact hZhmBound omega
    have hL4 : vecCubeLpENorm (originCube d (M : ℤ)) 4
        (fun x => (fun y => shellFlux omega r p y -
              shellFluxAverage (M : ℤ) omega r p) x -
          volumeAverageVec (cubeSet (originCube d (M : ℤ)))
            (fun y => shellFlux omega r p y -
              shellFluxAverage (M : ℤ) omega r p)) ≤
        ENNReal.ofReal (Zl4 omega) := by
      rw [hGavg, hfun]
      exact hZl4Bound omega
    have hAvg : vecNorm (volumeAverageVec (cubeSet (originCube d (M : ℤ)))
        (fun y => shellFlux omega r p y -
          shellFluxAverage (M : ℤ) omega r p)) ≤ 0 := by
      rw [hGavg]
      exact le_of_eq (by simp [vecNorm])
    have h := vecCubeLpENorm_grad_sub_le_of_responseNDWeak
      (hNDweak _ (wD omega) (wN omega + linearH1MeanZeroFunction
        (originCube d (M : ℤ)) (shellFluxAverage (M : ℤ) omega r p)) hDir hNeu)
      (hZhm0 omega) (hZl40 omega) le_rfl hHm hL4 hAvg
    have hfun2 : (fun x => (wN omega + linearH1MeanZeroFunction
          (originCube d (M : ℤ))
            (shellFluxAverage (M : ℤ) omega r p)).toH1Function.grad x -
        (wD omega).toH1Function.grad x) =
        fun x => (wN omega).toH1Function.grad x +
            shellFluxAverage (M : ℤ) omega r p -
          (wD omega).toH1Function.grad x := by
      funext x
      rw [add_linearH1MeanZeroFunction_grad]
    rw [hfun2, add_zero, ← ENNReal.ofReal_mul hCnd.le] at h
    exact h
end

end SuperdiffusionCLT.Section3.Setup

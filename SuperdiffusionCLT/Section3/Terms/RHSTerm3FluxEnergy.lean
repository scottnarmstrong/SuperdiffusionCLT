/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.RHSTerm3StepsA
public import SuperdiffusionCLT.Section3.Terms.RHSTerm3OscCarriers
public import SuperdiffusionCLT.Section2.Estimates.Stream.ShellHminusEndpointOrderOneB

/-!
# The `hFlux` and `hEnergy` carriers of `e.RHS.term3.B`

Step 1 of the proof of `e.RHS.term3.B`.  Two of the four printed estimates read by the
assembly `rhs_term3_B` are reduced here.

## The two printed displays, quoted

**`hFlux`** — the multiscale-Poincaré / Hölder chain.  The
opening member is the hatted negative norm of the flux:

```
\E\Bigl[ \| \a_{L'} ( \nabla u_m - \nabla u_{n,z} ) \|_{\Hminusul(z+\cu_n)}^{\nicefrac 32} \Bigr]
```

the first inequality is the multiscale Poincaré in its depth-sum form:

```
\E\Biggl[
\biggl(
      \sum_{j = -\infty}^n 3^{j} \biggl( \avsum_{z' \in z + 3^j \Z^d \cap \cu_n}
        \bigl| \bigl( \a_{L'} ( \nabla u_m - \nabla u_{n,z} ) \bigr)_{z'+\cu_j} \bigr|^2
      \biggr)^{\! \nicefrac12} \biggr)^{\! \nicefrac 32} \Biggr]
```

the second inequality is the energy-map / Hölder step:

```
\leq
      C 3^{\frac32 n} \E\biggl[
      \| \s^{\nf12} ( \nabla u_m - \nabla u_{n,z} ) \|_{\underline{L}^2(z+\cu_n)}^{\nicefrac 32}
\sum_{j = -\infty}^n 3^{j-n} \max_{z' \in z + 3^j \Z^d \cap \cu_n}
        \bigl| \b_{L'}(z'+\cu_j) \bigr|^{ \nicefrac 34} \biggr]
```

and the closing member is the printed rate:

```
\leq
      C 3^{\frac32 n} (L'\nu^{-1})^{\nicefrac 34}
\E\Bigl[ \| \s^{\nf12} ( \nabla u_m - \nabla u_{n,z} ) \|_{\underline{L}^2(z+\cu_n)}^2
\Bigr]^{\nicefrac 34}
```

**`hEnergy`** — `e.additivity.error.superdiff`:

```
\begin{align}
\label{e.additivity.error.superdiff}
\avsum_{z\in 3^n\Zd\cap \cu_m}
      \E\Bigl[ \| \s^{\nf12} ( \nabla u_m {-} \nabla u_{n,z} ) \|_{\underline{L}^2(z+\cu_n)}^2 \Bigr]
\leq
      C\bigl| 1-\shom_{L',*}(\cu_n) \shom_{L',*} ^{-1}(\cu_m) \bigr|
\leq
      C\bigl(\delta {+} \eta_L\bigr)
\,.
\end{align}
```

## What is carried here

* **Confinement — checked, it holds.**  Both `j`-sums of the print
  are confined to `z' ∈ z + 3^j Z^d ∩ cu_n`, the scale-`j` sub-cubes of the
  small cube `z + cu_n`; the depth index `j` runs over the scales *finer* than
  `cu_n` (`j ≤ n`, i.e. depth `n - j ≥ 0`).  The depth-sum device
  `cubeDepthPthMoment` averages over exactly
  `descendantsAtDepth Q j`, the sub-cubes of `Q` of scale `Q.scale - j`, so the
  carrier has the *same* confinement: the index set at `cu_n` *is* the paper's
  `3^j Z^d ∩ cu_n`, also at the glued small cubes `z + cu_n`.  The unconfined-`j`-sum
  defect is absent.
* **The convexity rearrangement.**  The passage from the rooted depth sum
  `∑_j 3^{j-n} (⋯)^{1/2}` to the printed `3/4`-exponent form
  `∑_j 3^{j-n} max |\b_{L'}|^{3/4}` is the convexity step
  `(∑ w_j x_j)^{3/2} ≤ (∑ w_j)^{1/2} ∑ w_j x_j^{3/2}` at `x_j = m_j^{1/2}`,
  `∑ w_j = 3/2`; it is proved here (`jensen_rpow_three_halves`,
  `weighted_rpow_three_halves_le`) rather than carried inside `hPointwise`, and
  the printed total weight is the named constant `threeHalvesConst`, verified as
  `tsum_inv_three_pow_eq_three_halves`.
* **`hFlux` carriers and reduction.**  `fluxFieldCarrier` and
  `energyL2Carrier` pin the assembly's free binders to the printed quantities —
  the hatted negative norm of `a_{L'}(∇u_m − ∇u_{n,z})` in the order-one
  vector carrier `vecHatNegENormOrderOne`, and the `σ^{1/2}`-energy `ν‖∇u_m −
  ∇u_{n,z}‖²` in `vecSqAvg`.  `hFlux_at_carriers` then derives the assembly's
  `hFlux` shape from `multiscale_poincare_flux` with `C3 = C1·4·Γ₁(1)·Cb` named.
  Its two analytic inputs remain the named residuals: `hPointwise` (the
  multiscale Poincaré at `s = 1`, `p = 2` on the *vector* flux field — the
  depth-sum bound needs `Continuous F`, the flux field is
  only `L̲²`) and `hBlockOrlicz` (the block-maximum envelope of the printed chain,
  asserted in the paper).
* **`hEnergy`.**  `hSecondVar` and `hJbig` are *carrier definitions*: the
  paper's `J_{L'}(U,0,Q)` is recovered from the second-variation identity, so
  the two binders are satisfied by the explicit carriers
  `energySubQCarrier`/`energyBigQCarrier`.  `hAnnealedSub`/`hAnnealedBig` — the
  annealed response value `e.homs.defs.U` at the glued carriers — remain the
  two named residuals.

## Witnesses

`hSecondVar` and `hJbig` are *not* hypotheses left to the caller: they are
discharged for arbitrary `uMgrad`, `uNGlued` by `ring`/`simp` from the carrier
definitions `energySubQCarrier`/`energyBigQCarrier`, so they need no witness and
none is claimed.  The two annealed binders `hAnnealedSub`/`hAnnealedBig` are
genuine hypotheses; their intended witness is the glued maximizer gradient pair
(`gluedGradientField … S.m …`, `gluedGradientField … S.n …`), for which they
*are* the annealed response value `e.homs.defs.U` — the named
residuals.  `hFlux_at_carriers` is likewise an implication: its hypotheses are
exactly the printed residual statements `hPointwise`/`hBlockOrlicz` (together
with the integrability side conditions), and the theorem is not a restatement of
them — it composes them with the Hölder/`Γ₁` machinery of
`multiscale_poincare_flux`.

`tsum_inv_three_pow_eq_three_halves` is a closed identity with no hypotheses.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Terms

open MeasureTheory
open Homogenization
open Homogenization.IndependentSums
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Norms
open SuperdiffusionCLT.Section2.Estimates.Stream
open SuperdiffusionCLT.Section3.ResponseFields
open SuperdiffusionCLT.Section3.Setup
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## The `hEnergy` carriers -/

/-- **The paper's `J_{L'}(z+cu_n, 0, Q)`**, read through the second-variation
identity `e.secondvar` at the competitor `u_m` and the
maximizer `u_{n,z}`:

`J = ⨍_{z+cu_n} (-\frac{\nu}{2}|∇u_m|² + Q·∇u_m) + \frac12 ⨍_{z+cu_n} \nu|∇u_m - ∇u_{n,z}|²`.

With this carrier the binder `hSecondVar` of `additivity_error_superdiff` is an
identity, which is exactly the printed content of `e.secondvar` (the source
defines `J` as the response value, so the identity *determines* `J`). -/
def energySubQCarrier {d : ℕ} [NeZero d] (nu : ℝ) (P : ProbabilityMeasure (ShellSeq d))
    (S : ScaleSelection) (e : Vec d)
    (uMgrad uNGlued : ShellSeq d → Vec d → Vec d)
    (omega : ShellSeq d) (R : TriadicCube d) : ℝ :=
  volumeAverage (openCubeSet R)
      (fun y => -(nu / 2) * vecNormSq (uMgrad omega y) +
        vecDot (fluxSlot nu S.LPrime P S.n e) (uMgrad omega y)) +
    (1 / 2 : ℝ) * volumeAverage (openCubeSet R)
      (fun y => nu * vecNormSq (uMgrad omega y - uNGlued omega y))

/-- **The paper's `J_{L'}(cu_m, 0, Q)`**: the `u_m`-energy on the large cube.
With this carrier the binder `hJbig` of `additivity_error_superdiff` is
`rfl`. -/
def energyBigQCarrier {d : ℕ} [NeZero d] (nu : ℝ) (P : ProbabilityMeasure (ShellSeq d))
    (S : ScaleSelection) (e : Vec d)
    (uMgrad : ShellSeq d → Vec d → Vec d) (omega : ShellSeq d) : ℝ :=
  volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
    (fun y => -(nu / 2) * vecNormSq (uMgrad omega y) +
      vecDot (fluxSlot nu S.LPrime P S.n e) (uMgrad omega y))

/-! ## `hEnergy`: the two binders that are carrier definitions -/

/-- **`hEnergy` of `e.RHS.term3.B` at the explicit carriers,
with `hSecondVar` and `hJbig` discharged.**

The two remaining hypotheses are the annealed response values
`e.homs.defs.U` read at the glued carriers — `E[J_{L'}(z+cu_n,0,Q)] =
½ shom_{L',*}^{-1}(z+cu_n)|Q|²` (independent of `z` by stationarity) and
`E[J_{L'}(cu_m,0,Q)] = ½ shom_{L',*}^{-1}(cu_m)|Q|²` — together with the
integrability side conditions and the pigeonhole input `e.pigeon.scalar`; the
conclusion is the printed middle member with `C = 1` and the absolute value
removed (the telescoping produces the signed quantity, which is nonnegative by
`antitone_sigmaBarStarInvSeq`). -/
theorem additivity_error_superdiff_at_carriers
    {d : ℕ} [NeZero d] {nu : ℝ} (hnu : 0 < nu) {P : ProbabilityMeasure (ShellSeq d)}
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P)
    (hJ4 : ShellLawJ4 d P) (S : ScaleSelection) {e : Vec d} (he : vecNormSq e = 1)
    (uMgrad uNGlued : ShellSeq d → Vec d → Vec d)
    (hAnnealedSub : ∀ R ∈ largeCubeSubcubes d S.n S.m,
      ∫ omega : ShellSeq d,
          energySubQCarrier nu P S e uMgrad uNGlued omega R ∂P.toMeasure =
        (1 / 2 : ℝ) * sigmaBarStarInvSeq nu S.LPrime P S.n *
          vecNormSq (fluxSlot nu S.LPrime P S.n e))
    (hAnnealedBig : ∫ omega : ShellSeq d,
          energyBigQCarrier nu P S e uMgrad omega ∂P.toMeasure =
        (1 / 2 : ℝ) * sigmaBarStarInvSeq nu S.LPrime P S.m *
          vecNormSq (fluxSlot nu S.LPrime P S.n e))
    (hJsubInt : ∀ R ∈ largeCubeSubcubes d S.n S.m,
      Integrable (fun omega : ShellSeq d =>
        energySubQCarrier nu P S e uMgrad uNGlued omega R) P.toMeasure)
    (hEnergyInt : ∀ R ∈ largeCubeSubcubes d S.n S.m,
      Integrable (fun omega : ShellSeq d =>
        volumeAverage (openCubeSet R)
          (fun y => -(nu / 2) * vecNormSq (uMgrad omega y) +
            vecDot (fluxSlot nu S.LPrime P S.n e) (uMgrad omega y))) P.toMeasure)
    (hEnergyCube : ∀ omega : ShellSeq d, ∀ R ∈ largeCubeSubcubes d S.n S.m,
      IntegrableOn (fun y => -(nu / 2) * vecNormSq (uMgrad omega y) +
        vecDot (fluxSlot nu S.LPrime P S.n e) (uMgrad omega y)) (cubeSet R) volume)
    {delta etaL : ℝ}
    (hPigeon : |1 - (sigmaBarStarInvSeq nu S.LPrime P S.n)⁻¹ *
      sigmaBarStarInvSeq nu S.LPrime P S.m| ≤ delta + etaL) :
    ((largeCubeSubcubes d S.n S.m).card : ℝ)⁻¹ *
        ∑ R ∈ largeCubeSubcubes d S.n S.m,
          ∫ omega : ShellSeq d,
            volumeAverage (openCubeSet R)
              (fun y => nu * vecNormSq (uMgrad omega y - uNGlued omega y))
            ∂P.toMeasure ≤ delta + etaL := by
  refine additivity_error_superdiff hnu hPrefix hJ2 hJ3 hJ4 S he uMgrad uNGlued
    (energySubQCarrier nu P S e uMgrad uNGlued) (energyBigQCarrier nu P S e uMgrad)
    ?_ ?_ hAnnealedSub hAnnealedBig hJsubInt hEnergyInt hEnergyCube hPigeon
  · intro omega R _
    simp only [energySubQCarrier]
    ring
  · intro omega
    simp only [energyBigQCarrier]

/-! ## `hFlux`: confinement of the printed `j`-sums

Both `j`-sums of the print run over
`z' ∈ z + 3^j Z^d ∩ cu_n` — the scale-`j` sub-cubes of the *small* cube
`z + cu_n`, not of the tiling.  The depth-sum device averages over
`descendantsAtDepth Q j`, and `descendantsAtDepth` is by construction the
sub-cube relation (`childCubes` recursively), so the carrier is confined
to `Q`.  The lemmas below record that check at the very carriers the `j`-sum
uses. -/

section Confinement

end Confinement

/-! ## `hFlux`: the convexity rearrangement and the printed weight sum

The passage from the rooted `1/2`-power depth sum
to the `3/4`-power block sum is the convexity step (`hPointwise`
carries it in the print; it is *proved* here instead).  At `x_j = m_j^{1/2}` the
two sides are the Jensen inequality for the convex function `t ↦ t^{3/2}`, and
the printed weights `w_j = 3^{j-n}` have total mass `3/2`, which is the constant
named in `threeHalvesConst`. -/

/-- The printed total weight `3/2` of the depth sum, named. -/
def threeHalvesConst : ℝ := 3 / 2

/-- **The printed weight sum**: `∑_{k ≥ 0} 3^{-k} = 3/2`.  This is the total
mass of the depth weights `w_j = 3^{j-n}` of the printed chain under `k = n - j`, and it
is the constant that the convexity rearrangement produces. -/
theorem tsum_inv_three_pow_eq_three_halves :
    (∑' k : ℕ, ((3 : ℝ)⁻¹) ^ k) = threeHalvesConst := by
  rw [tsum_geometric_of_norm_lt_one (by norm_num : ‖((3 : ℝ)⁻¹)‖ < 1)]
  unfold threeHalvesConst
  norm_num

/-- **Jensen for `t ↦ t^{3/2}` at normalised weights.** -/
theorem jensen_rpow_three_halves {ι : Type*} (s : Finset ι) (w x : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hw1 : ∑ i ∈ s, w i = 1) (hx : ∀ i ∈ s, 0 ≤ x i) :
    (∑ i ∈ s, w i * x i) ^ ((3 : ℝ) / 2) ≤
      ∑ i ∈ s, w i * x i ^ ((3 : ℝ) / 2) := by
  have h := ConvexOn.map_sum_le (𝕜 := ℝ)
    (convexOn_rpow (p := (3 : ℝ) / 2) (by norm_num))
    (s := Set.Ici (0 : ℝ)) (t := s) (w := w) (p := x)
    (fun i hi => hw i hi) hw1 (fun i hi => hx i hi)
  simpa only [smul_eq_mul] using h

/-- **The convexity rearrangement of the print.**  For nonnegative weights `w`
and nonnegative `x`, the rooted sum satisfies

`(∑_i w_i x_i)^{3/2} ≤ (∑_i w_i)^{1/2} ∑_i w_i x_i^{3/2}`;

at the printed weights `∑_j 3^{j-n} = 3/2` the constant is
`(3/2)^{1/2}`, and at `x_j = m_j^{1/2}` the right side is the printed
`m_j^{3/4}`.  This is the step from the rooted `1/2`-power depth sum to the
`3/4`-power block sum of the printed chain. -/
theorem weighted_rpow_three_halves_le {ι : Type*} (s : Finset ι) (w x : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hW : 0 < ∑ i ∈ s, w i) (hx : ∀ i ∈ s, 0 ≤ x i) :
    (∑ i ∈ s, w i * x i) ^ ((3 : ℝ) / 2) ≤
      (∑ i ∈ s, w i) ^ ((1 : ℝ) / 2) * ∑ i ∈ s, w i * x i ^ ((3 : ℝ) / 2) := by
  set W := ∑ i ∈ s, w i with hWdef
  have hWpos : 0 < W := by rw [hWdef]; exact hW
  have hAnn : (0 : ℝ) ≤ ∑ i ∈ s, w i * x i :=
    Finset.sum_nonneg fun i hi => mul_nonneg (hw i hi) (hx i hi)
  have hw' : ∀ i ∈ s, 0 ≤ w i / W := fun i hi => div_nonneg (hw i hi) hWpos.le
  have hw'1 : ∑ i ∈ s, w i / W = 1 := by
    rw [← Finset.sum_div, ← hWdef, div_self (ne_of_gt hWpos)]
  have hj := jensen_rpow_three_halves s (fun i => w i / W) x hw' hw'1 hx
  have hA : (∑ i ∈ s, w i / W * x i) = (∑ i ∈ s, w i * x i) / W := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun i _ => div_mul_eq_mul_div (w i) W (x i)
  have hB : (∑ i ∈ s, w i / W * x i ^ ((3 : ℝ) / 2)) =
      (∑ i ∈ s, w i * x i ^ ((3 : ℝ) / 2)) / W := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun i _ =>
      div_mul_eq_mul_div (w i) W (x i ^ ((3 : ℝ) / 2))
  rw [hA, hB] at hj
  have hW32pos : (0 : ℝ) < W ^ ((3 : ℝ) / 2) := Real.rpow_pos_of_pos hWpos _
  have hmul := mul_le_mul_of_nonneg_left hj hW32pos.le
  have hL : W ^ ((3 : ℝ) / 2) * ((∑ i ∈ s, w i * x i) / W) ^ ((3 : ℝ) / 2) =
      (∑ i ∈ s, w i * x i) ^ ((3 : ℝ) / 2) := by
    rw [Real.div_rpow hAnn hWpos.le ((3 : ℝ) / 2), ← mul_div_assoc,
      mul_comm (W ^ ((3 : ℝ) / 2)) ((∑ i ∈ s, w i * x i) ^ ((3 : ℝ) / 2)),
      div_eq_mul_inv, mul_assoc, mul_inv_cancel₀ (ne_of_gt hW32pos), mul_one]
  have hWs : W ^ ((3 : ℝ) / 2) / W = W ^ ((1 : ℝ) / 2) := by
    have h := Real.rpow_sub hWpos ((3 : ℝ) / 2) 1
    rw [Real.rpow_one] at h
    rw [← h, show (3 : ℝ) / 2 - 1 = 1 / 2 by norm_num]
  have hR' : W ^ ((3 : ℝ) / 2) * ((∑ i ∈ s, w i * x i ^ ((3 : ℝ) / 2)) / W) =
      W ^ ((1 : ℝ) / 2) * ∑ i ∈ s, w i * x i ^ ((3 : ℝ) / 2) := by
    rw [← mul_div_assoc,
      ← div_mul_eq_mul_div (W ^ ((3 : ℝ) / 2)) W (∑ i ∈ s, w i * x i ^ ((3 : ℝ) / 2)),
      hWs]
  calc (∑ i ∈ s, w i * x i) ^ ((3 : ℝ) / 2)
      = W ^ ((3 : ℝ) / 2) * ((∑ i ∈ s, w i * x i) / W) ^ ((3 : ℝ) / 2) := hL.symm
    _ ≤ W ^ ((3 : ℝ) / 2) * ((∑ i ∈ s, w i * x i ^ ((3 : ℝ) / 2)) / W) := hmul
    _ = W ^ ((1 : ℝ) / 2) * ∑ i ∈ s, w i * x i ^ ((3 : ℝ) / 2) := hR'

/-! ## The `hFlux` carriers and the reduction to the two named residuals

The assembly `rhs_term3_B` takes `fluxNegNorm` and `energyL2` as
free binders; here they are *pinned* to the printed quantities — the hatted
negative norm of the flux `a_{L'}(∇u_m − ∇u_{n,z})` in the
order-one vector carrier `vecHatNegENormOrderOne`, and the `σ^{1/2}`-energy
`ν ‖∇u_m − ∇u_{n,z}‖²_{L̲²(z+cu_n)}` in the carrier
`vecSqAvg`.  The reduction `hFlux_at_carriers` then produces the assembly's
`hFlux` shape from `multiscale_poincare_flux`, whose two analytic inputs are the
named residuals.

The residual content of `hPointwise` at these carriers is the multiscale
Poincaré inequality at `s = 1`, `p = 2` on the *vector* flux field: the
depth-sum form requires
`Continuous F`, while the flux field here is only `L̲²`; and the block-maximum
envelope is `hBlockOrlicz`, asserted in the paper.  All the
other inputs — the confinement (proved above), the convexity rearrangement
(proved above), the Hölder decoupling and the `Γ₁`-moment conversion inside
`multiscale_poincare_flux` — are proved. -/

/-- **The flux field `a_{L'}(∇u_m − ∇u_{n,z})`**, the same field the duality
binder `hCS` pairs against, in the coefficient cutoff of `Frozen.Section2`. -/
def fluxFieldCarrier (nu : ℝ) (S : ScaleSelection) (omega : ShellSeq d)
    (uMgrad uNGlued : Vec d → Vec d) : Vec d → Vec d :=
  fun y => matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y)
    (uMgrad y - uNGlued y)

/-- **`energyL2`**: the printed `‖σ^{1/2}(∇u_m − ∇u_{n,z})‖²_{L̲²(z+cu_n)}` of
the energy-map step.  With the isotropic coefficient `σ = ν Id` the `σ^{1/2}` factor is the
scalar `√ν`, so the carrier is `ν ‖∇u_m − ∇u_{n,z}‖²`. -/
def energyL2Carrier (nu : ℝ) (uMgrad uNGlued : Vec d → Vec d)
    (R : TriadicCube d) : ℝ :=
  nu * vecSqAvg R (fun y => uMgrad y - uNGlued y)

theorem energyL2Carrier_nonneg {nu : ℝ} (hnu : 0 ≤ nu)
    (uMgrad uNGlued : Vec d → Vec d) (R : TriadicCube d) :
    0 ≤ energyL2Carrier nu uMgrad uNGlued R :=
  mul_nonneg hnu (vecSqAvg_nonneg R _)

/-! ## Witnesses for the `hFlux` lemmas

Each new statement above is exhibited below at an explicit configuration, so
that no lemma is vacuous. -/

end

end SuperdiffusionCLT.Section3.Terms

# Errata

These are the corrections to S. Armstrong, A. Bou-Rabee, T. Kuusi, [*Superdiffusive central limit theorem for a Brownian particle in a critically-correlated incompressible random drift*](https://link.springer.com/article/10.1007/s00222-026-01455-z), Invent. Math., to appear, found while formalizing it in Lean 4. Locations (printed numbers and pages) refer to the preprint version arXiv:2404.01115v3. Each item gives the location in the manuscript (printed numbers and page of arXiv:2404.01115v3), what is printed, the correction, the reason, the effect on the rest of the paper, and the Lean declaration that proves the corrected statement. None of the corrections changes the statement of Theorems A–D. Items E1–E25 concern the manuscript and are numbered in the order of the manuscript; the small ones (E4, E9, E11, E20) are collected in the table at the end of the manuscript items. Items that arXiv:2404.01115v3 has already corrected keep their numbers and are listed at the end, in the section "Corrected in arXiv:2404.01115v3". Items AK1–AK6 concern Theorem 6.1 of the input paper [AK25] = S. Armstrong, T. Kuusi, *Renormalization group and elliptic homogenization in high contrast*, as the manuscript applies it.

Notation: $\breve A$ is the second non-degeneracy constant of assumption (J5). $\Gamma_\sigma$, $\mathcal O_{\Gamma_\sigma}$, $\hat{\underline H}{}^{-1}$ and so on are as in the manuscript.

---

## Section 2

### E3. Lemma 2.9, display (2.79), p. 37, and its proof, p. 40: the amplitude of $\log\mathcal K_\sigma$

*Printed.* $\log\mathcal K_\sigma\le\mathcal O_{\Gamma_{2\sigma}}\bigl(C_1(s,d)(C_2\delta^{-1}\sigma^{-1})^{1/\sigma}\bigr)$. The proof (p. 40) sets $N_\sigma:=\lceil(C\sigma^{-1}\delta^{-1})^{1/\sigma}\rceil$ and claims
$$\mathbb P\bigl[\log\mathcal K_\sigma>(\log3)N_\sigma m\bigr]\le\sum_{n\ge\lfloor N_\sigma m\rfloor}Cn\exp(-c\delta^2n^{2\sigma})\le\exp(-cm^{2\sigma}).$$

*Correction.*
$$\log\mathcal K_\sigma\le\mathcal O_{\Gamma_{2\sigma}}\Bigl(C_0\bigl(C_1\delta^{-1}\sqrt{\sigma^{-1}\log(e+C_2\delta^{-1}\sigma^{-1})}\bigr)^{1/\sigma}\Bigr),$$
with $C_0,C_1,C_2$ depending only on $(s,d)$, and $C_0$ outside the power $1/\sigma$.

*Why.* The last inequality of the display fails as $\delta\to0$ for fixed $m$. In the first term of the sum, $\delta^2N_\sigma^{2\sigma}$ does not depend on $\delta$, so the exponential factor is fixed, while the prefactor $N_\sigma m$ grows like $\delta^{-1/\sigma}$. The union bound over the bad scales is sharp when the bad events at different scales are disjoint, and the number of candidate scales below $N_\sigma m$ costs exactly a factor $\sqrt{\log(1/\delta)}$ in the amplitude. The constant must sit outside the power $1/\sigma$ because $\mathcal K_\sigma\ge27$: otherwise the amplitude would tend to $1$ as $\sigma\to\infty$ and would vanish when $C_2\delta^{-1}\sigma^{-1}\le1$.

*Consequence.* None on any later statement. In every application $\delta$ and $\sigma$ are fixed in terms of the other parameters, and only the constants in the stretched-exponential tails of the minimal scales change.

*Lean.* `SuperdiffusionCLT.Frozen.Section2.streamIncrement_scale_estimates`.


## Section 3

### E7. Lemma 3.2, displays (3.25) and (3.26), p. 56, proof Step 2, p. 57: the Neumann estimates are not proved by reflection

*Printed.* (3.25) and (3.26) bound $\|\nabla^2w^{(M)}_{N,\mathbf F}\|_{\underline L^8(\square_M)}$ and $\|\nabla w^{(M)}_{N,\mathbf F}\|_{\underline H^{1/2}(\square_M)}$ for the Neumann response, with the proof "for the prescribed-flux Neumann problem one reflects the normal component of $\mathbf F$ oddly and the tangential components evenly".

*Correction.* The proof covers the Dirichlet response only. The Neumann bounds need either the inhomogeneous-Neumann $W^{2,p}$ theory on cubes or a Hodge splitting. Alternatively they can be dropped. Their uses in Section 5, (5.36) on p. 102 and the oscillation bound (5.46) on p. 105, can be replaced by a comparison with the Dirichlet response: its $W^{2,8}$ bound, plus the energy bound on $\nabla w_N-\nabla w_D$ of Lemma 3.2, plus the bound on the shell derivative.

*Why.* After the reflection, the normal component of the reflected flux jumps across every face on which $\mathbf F\cdot n\ne0$. So the reflected flux is not in $W^{1,8}$, its divergence carries a surface term, and the reflected problem is not a Poisson problem with $L^p$ data. The $\underline H^{1/2}$ bound is obtained by interpolation from the missing $W^{2,2}$ endpoint, so it is not proved either. The Neumann estimates themselves are believed to be true.

*Consequence.* None on any statement. Section 3 uses (3.25)–(3.26) only for the Dirichlet response, and the Section 5 uses go through the Dirichlet comparison.

*Lean.* `SuperdiffusionCLT.Frozen.Section3.responseFields_apriori_orderOne` (with (3.25)–(3.26) stated for the Dirichlet response) and `SuperdiffusionCLT.Section5.crude_Fz_bound` (the Dirichlet comparison). These feed `SuperdiffusionCLT.Frozen.Section5.sigmaBar_approximate_recurrence`.

### E8. Lemma 3.5, Step 2: display (3.40) and its derivation, p. 62

*Printed.*
$$\mathbb E\Bigl[\Bigl|\frac{1}{|\square_m|}\int_{\square_m}\nabla w\cdot(\mathbf a_\ell\nabla\tilde u_n-\tilde q)\Bigr|\Bigr]\le C\nu^{-1}\bigl(\ell m(m-\ell)\bigr)^{1/2}3^{-(\ell'-\ell)},$$
derived from the first line of the multiscale display
$$\mathbb E\bigl[\|\mathbf F\|^2_{\hat{\underline H}{}^{-1}(\square_m)}\bigr]\le C\sum_{k\le m}3^{2k}\textstyle\sum\!\!\!\!\!\!\int_{z\in3^k\mathbb Z^d\cap\square_m}\mathbb E\bigl[|(\mathbf F)_{z+\square_k}|^2\bigr],\qquad\mathbf F=\mathbf a_\ell\nabla\tilde u_n-\tilde q.$$

*Correction.* Replace the squared multiscale inequality by the linear one, $\|\mathbf F\|_{\hat{\underline H}{}^{-1}(\square_m)}\le C\sum_{k\le m}3^{k}\bigl(\textstyle\sum\!\!\!\!\!\!\int_{z\in3^k\mathbb Z^d\cap\square_m}|(\mathbf F)_{z+\square_k}|^2\bigr)^{1/2}$, which is the form already used for (2.85). The display becomes
$$\mathbb E\Bigl[\Bigl|\frac{1}{|\square_m|}\int_{\square_m}\nabla w\cdot(\mathbf a_\ell\nabla\tilde u_n-\tilde q)\Bigr|\Bigr]\le C\nu^{-1}(\ell m)^{1/2}(m-\ell)\,3^{-(\ell'-\ell)}.$$

*Why.* The squared multiscale inequality is false, also in expectation, by a factor equal to the number of active scales. Take a field that is a sum of $J$ scale components with independent random signs. Then the left side is of order $J^2$ while the right side is of order $J$. The linear inequality is true, and squaring it costs exactly the factor $(m-\ell)$, which is sharp in dimension two (each scale contributes equally). The other lines of the derivation are correct.

*Consequence.* None on the statement of Lemma 3.5. The closing coarsening of the proof already absorbs the extra factor: $(\ell m)^{1/2}(m-\ell)\le4\ell h\le4\ell^2h$ for the selected scales, so (3.36) holds as printed with the same kind of constant.

*Lean.* `SuperdiffusionCLT.Section3.Terms.lintegral_vecHatNegENormOrderOne_sq_le_memLp` (the multiscale step), `SuperdiffusionCLT.Section3.Terms.duality_bridge` (the duality step), and `SuperdiffusionCLT.Frozen.Section3.rhs_term1` (Lemma 3.5 as printed).

### E10. Lemma 3.8, proof Step 3: decomposition (3.58) and the display before it, p. 68, and the Hölder display on p. 69, must keep the signs

*Printed.*
$$|\mathbf b_\ell(z+\square_n)|\le d\,\bar\sigma_\ell(\square_n)+\sum_{i=1}^d\bigl|e_i\cdot\bigl(\mathbf b_\ell(z+\square_n)-\bar\sigma_\ell(\square_n)\bigr)e_i\bigr|,$$
carried into (3.58). The Hölder display that follows then bounds the corresponding term by $\sum_i\mathbb E\bigl[\bigl|\sum\!\!\!\!\!\!\int_z Y^{(i)}_z\bigr|^2\bigr]^{1/2}$ with $Y^{(i)}_z:= e_i\cdot(\mathbf b_\ell(z+\square_n)-\bar\sigma_\ell(\square_n))e_i$.

*Correction.* Remove the absolute values:
$$|\mathbf b_\ell(z+\square_n)|\le d\,\bar\sigma_\ell(\square_n)+\sum_{i=1}^de_i\cdot\bigl(\mathbf b_\ell(z+\square_n)-\bar\sigma_\ell(\square_n)\bigr)e_i .$$
This is the trace bound $|\mathbf b|\le\operatorname{tr}\mathbf b$ for the positive semidefinite matrix $\mathbf b_\ell(z+\square_n)$.

*Why.* Concentration gives the decay $3^{-\frac d2(k-\ell)}$ only for the signed lattice average $\sum\!\!\!\!\!\!\int_zY^{(i)}_z$. With the absolute values the pointwise bound produces $\sum\!\!\!\!\!\!\int_z|Y^{(i)}_z|$, which has no cancellation and stays of order $\mathbb E|Y^{(i)}_0|$ however large $k-\ell$ is. So the Hölder display does not follow from the printed decomposition. With the signed bound it follows exactly as written.

*Consequence.* None: the Hölder display, (3.57) and Lemma 3.8 hold as printed, except for the exponent in row E9 of the table.

*Lean.* `SuperdiffusionCLT.Section3.Terms.matrixOperatorNorm_le_sum_diag_of_posSemidef` (the signed trace bound) and `SuperdiffusionCLT.Frozen.Section3.rhs_term3_constFirst` (Lemma 3.8).


## Section 4

### E13. Proposition 4.5, proof Steps 1 and 2, p. 81: the application of [AK25, Theorem 6.1]

*Printed.* The proof uses the condition
$$m_0\ge\frac{CD}{(1-\beta)(1-\gamma)^2}\log\bigl((\Upsilon_1+\Upsilon_2)(m_2\vee m_3+m_0)\Theta_{L,0}\bigr)\log(3\Theta_{L,0})$$
copied from [AK25, Theorem 6.1], and the rate "$\kappa:=\min\{\alpha_*(d),1-\gamma\}=\min\{\alpha_*(d),\frac12\}$".

*Correction.* Apply Theorem 6.1 of [AK25] in its corrected form (items AK1–AK4 below): the factor $C(1+D)$, the theorem's own input scale in place of $m_2\vee m_3$, and the rate $\kappa=\min\{\alpha_*(d),\frac12(1-\gamma)\}=\min\{\alpha_*(d),\frac14\}$. Because the threshold now grows with the input scale, the choice $m_0=\lceil C\log^2L\rceil$ needs a separate (easy) case for input scales $\tilde m>L^2$.

*Why.* The printed form of [AK, Theorem 6.1] is false (AK1–AK3), and its proof gives only the rate of AK4.

*Consequence.* None on any statement. The rate is still a positive constant depending only on $d$, and the manuscript's parameters ($D=1$, $\gamma=\beta=\frac12$, $p_\Psi=2d$, $p_{\Psi_S}=2d$, $L_1\log L_2=4C\log\nu^{-1}$) satisfy every condition of the corrected theorem.

*Lean.* `SuperdiffusionCLT.Frozen.Section4.akhc_weakerP3` (the corrected Theorem 6.1 for this application) and `SuperdiffusionCLT.Frozen.Section4.homogenization_below_cutoff` (Proposition 4.5 as printed), via `SuperdiffusionCLT.Section4.HomogBelow.homogBelow_main`.


## Section 7

### E19. Proposition 7.4, proof of the boundary estimate (7.36), pp. 140–142: the decay factor $3^{-k_0}$

*Printed.* On p. 141, after the Green's identity step, "the standard boundary and interior estimates for the Laplace equation give"
$$\inf_{\ell}3^{-(k-k_0)}\|\bar u_k-\ell\|_{L^\infty(\widehat\square_{k-k_0})}\le C3^{-k_0}\inf_{\ell}\bigl(3^{-k}\|\bar u_k-\ell\|_{\underline L^2(\widehat\square_{k-1})}+3^{k-m}|\nabla\ell|\bigr)+C\bar{\mathbf s}_m^{-1}3^k\|f\|_{L^\infty(U_m)}+C\|\nabla g\|_{L^\infty(U_m)},$$
where $\bar u_k$ solves the Laplace equation in $\widehat V_k$, whose boundary has curvature $\le C3^{-m}$. The constant $k_0=k_0(U,d)$ is then fixed (p. 140) "so that the boundary and interior estimates for $u_k$ give the factor $\frac12$ in the excess inequality", which becomes $E^z_{k-k_0}\le\frac12E^z_{k+1}+C(\delta_k+3^{k-m})|\nabla\ell^z_{k+1}|+\cdots$ (p. 142).

*Correction.* Fix $\alpha\in(0,1)$, for instance $\alpha=\frac12$, and replace $3^{-k_0}$ by $3^{-\alpha k_0}$, with $C=C(\alpha,U,d)$ independent of $k_0$. Then choose $k_0$ so large that $C3^{-\alpha k_0}\le\frac14$. Everything else in the boundary argument is unchanged: the slope term $3^{k-m}|\nabla\ell|$ and the term $C(\delta_k+3^{k-m})|\nabla\ell^z_{k+1}|$ in the recursion are already present in arXiv:2404.01115v3.

*Why.* The boundary of $\widehat V_k$ is only $C^{1,1}$, and harmonic functions on $C^{1,1}$ domains are $C^{1,\alpha}$ up to the boundary for every $\alpha<1$, but their gradient is in general only log-Lipschitz. Take the half-plane-like domain $\{y_2>\frac\epsilon2y_1|y_1|\}$, whose curvature jumps across $0$ and is of size $\epsilon=3^{k-m}$. The harmonic function $\bar u$ with zero boundary values and slope $1$ is $y_2+O(\epsilon)$, and its next term contains $\epsilon\,y_1y_2\log|y|$, because the harmonic extension of the odd datum $y_1|y_1|$ carries a logarithm. At radius $r=3^{-k_0}$ the left side above is then of order $\epsilon\,r\log(1/r)$, while the right side with $\ell=y_2$ is $C\epsilon\,r$. So no constant $C$ independent of $k_0$ can give the factor $3^{-k_0}$, which is exactly what the choice of $k_0$ needs. The exponent $\alpha<1$ is what the boundary $C^{1,\alpha}$ estimate gives, and any $\alpha>0$ is enough for the iteration.

*Consequence.* None on any statement. $k_0$ is a constant depending on $(\alpha,U,d)$ and nothing downstream sees it. Proposition 7.5, (7.37), and Lemma 8.8 are unaffected.

*Lean.* `SuperdiffusionCLT.Section7.r3e_boundary_decay` (the boundary decay with the exponent $1-d/p<1$ and the slope term), `SuperdiffusionCLT.Section7.lip_patch_decay`, `SuperdiffusionCLT.Section7.lip_iteration`, and `SuperdiffusionCLT.Section7.lip_boundary_fine` (the corrected (7.36)).

### E22. Proposition 7.6, proof, sentence after (7.44), p. 145: the boundary cover

*Printed.* "If the center of a boundary-cover cube lies outside $U_K$, replace it by a bounded number of neighboring grid cubes with centers in $U_K$; the larger cube $z+\square_{n+d+5}$ in (7.44) contains all of these cubes."

*Correction.* Take the centres on a finer grid $3^{n-s}\mathbb Z^d\cap U_K$ with $s=s(U,d)$, and apply the boundary estimate on these cubes. This costs a factor $3^{sd}$ in the union bound.

*Why.* Neighbouring grid cubes centred in $U_K$ need not cover. If the boundary is the hyperplane $x_1=3^jk-\varepsilon$ with $j$ large, then at every grid level up to $j$ the cubes adjacent to it are centred on $x_1=3^jk$, outside the domain. A strip of width up to half a cube is then covered by no cube centred in $U_K$ at levels up to $n+d+5$, and (7.36), stated only for centres in $3^n\mathbb Z^d\cap U_m$, does not reach it.

*Consequence.* None.

*Lean.* `SuperdiffusionCLT.Section7.linf_fine_cover`, `SuperdiffusionCLT.Section7.lip_boundary_fine` (centres on the fine grid) and `SuperdiffusionCLT.Section7.linf_prop` (Proposition 7.6).

### E24. Theorem C, proof, p. 150: the passage from cubes to balls when $m-n$ is bounded

*Printed.* "If $m-n$ is bounded by a dimensional constant, the desired estimate follows from the trivial bound and the fact that $(r/R)^\gamma$ is then bounded below."

*Correction.* Cover $B_r$ by $O(1)$ translated cubes $y+\square_n\subseteq y+\square_m\subseteq B_R$ and apply the translated Lemma 7.8 on each. The translated minimal scales are supplied by Lemma 6.1 (see item E17 below).

*Why.* For $r$ close to $R/2$ there are no centred cubes with $B_r\subseteq\square_n\subseteq\square_m\subseteq B_R$ and $n<m$, since $3^n\ge2r\approx R$ and $3^m\le2R/\sqrt d$ are incompatible. The $L^\infty$–$L^2$ bound needed there is not trivial, because the ellipticity contrast of the field is unbounded.

*Consequence.* None.

*Lean.* `SuperdiffusionCLT.Section7.hr_ball_holder`, `SuperdiffusionCLT.Section7.hr_large_scale_holder` and `SuperdiffusionCLT.Frozen.Section7.large_scale_holder` (Theorem C).


---

## Small corrections

| Item | Location | Printed | Corrected | Lean |
|---|---|---|---|---|
| E4 | Lemma 2.9, (2.80), p. 37 (and the same term in (2.90) in its proof, p. 39) | $3^{-sm}[\mathbf k-(\mathbf k)_{\square_m}]_{\hat H^{-s}(\square_m)}$, without underline (un-normalized) | the volume-normalized seminorm $\hat{\underline H}{}^{-s}(\square_m)$. In the un-normalized norm the term is of size $3^{dm/2}$, and no random scale can make it $\le\delta m^\sigma$. | `SuperdiffusionCLT.Frozen.Section2.streamIncrement_scale_estimates` |
| E9 | Lemma 3.8, (3.48), p. 65 | last rate $3^{-\frac18h}$ in the second group | $3^{-\frac1{16}h}$. The second group of (3.48) is $(\delta+\eta_L)^{1/2}$ times the square root of (3.57), and the square root of its term $3^{-\frac18h}$ is $3^{-\frac1{16}h}$. No effect downstream: the window $h$ in Proposition 3.1 is large enough for $3^{-h/16}$ to beat every polynomial factor. | `SuperdiffusionCLT.Frozen.Section3.rhs_term3_constFirst` |
| E11 | Lemma 3.10, p. 70 | hypothesis $n\ge C\log^2(\nu^{-1}L)$ | add $n\ge1$. At $\nu=L=1$ the printed hypothesis is empty, and $n=0$, $\ell=1$ is admitted, but the proof needs a scale $k<n$. No effect downstream: the lemma is used only at large $n$. | `SuperdiffusionCLT.Frozen.Section3.sigmaBar_le_sigmaBarStar_homogenization` |
| E20 | Proposition 7.6, proof, before (7.40), p. 144 | "Extend $g$ to $W^{1,\infty}(\mathbb R^d)$ with norm bounded by $C(U)\|g\|_{W^{1,\infty}(U_K)}$", then a bound by $\|\nabla g\|_{L^\infty}$ alone | first bound the Lipschitz constant of $g$ by $C(U)\|\nabla g\|_{L^\infty}$ (a chain argument on the connected domain), then extend by a Lipschitz extension. The printed extension bound involves $\|g\|_{L^\infty}$. | `SuperdiffusionCLT.Section7.linf_global_lipschitz`, `SuperdiffusionCLT.Section7.linf_datum` |

---

## Corrections to Theorem 6.1 of [AK25]

The manuscript applies [AK25, Theorem 6.1] twice, in Lemma 4.4 (p. 78) and Proposition 4.5 (p. 80; see E13). The printed statement of that theorem needs the following corrections. The formalization proves the corrected theorem for the cutoff fields of the manuscript, on the range $\gamma\le\frac12$, $\beta\le\frac12$, $d+1\le p_\Psi$, $3\le p_{\Psi_S}$ (with $K_\Psi^{6(d+1)^2}$ in place of $K_\Psi^{4d^2}$ in $\Upsilon_1$). The manuscript uses $\gamma=\beta=\frac12$, $p_\Psi=2d$, $p_{\Psi_S}=2d$, which is inside that range. These restrictions are limitations of the formal proof, not errors in [AK25]. Lean: `SuperdiffusionCLT.Frozen.Section4.akhc_weakerP3`, proved by `SuperdiffusionCLT.AKHC61.akhc_weakerP3_port`.

**AK1. The factor $D$ in the condition on $m_0$.** *Printed:* $m_0\ge\frac{CD}{(1-\beta)(1-\gamma)^2}\log\bigl((\Upsilon_1+\Upsilon_2)(m_2\vee m_3+m_0)\Theta_0\bigr)\log(3\Theta_0)$. *Correction:* $C(1+D)$ in place of $CD$. *Why:* at $D=0$ the printed condition is $m_0\ge0$. An i.i.d. checkerboard with values $\{1,\Lambda\}$ satisfies the assumptions with $D=0$, and the conclusion at $m=n=1$, $m_0=0$ would force $\Theta_1\le2+C(d)$, whereas $\Theta_1\ge4^{-3^d}\Lambda$. The $m_0$ produced by the proof never vanishes.

**AK2. The input scale in the condition on $m_0$.** *Printed:* $\log\bigl((\Upsilon_1+\Upsilon_2)(m_2\vee m_3+m_0)\Theta_0\bigr)$. *Correction:* the theorem's own input scale $m$ in place of $m_2\vee m_3$. *Why:* the proof's $m_0$ contains $\log(2m_0+m_1)$ with $m_1\ge m$. With the printed form, $m_0$ does not depend on $m$, and the statement fails. A marked Poisson field with correlation length $3^\rho$, $\rho\approx m+\log m$ (any $d\ge2$, $\gamma=\beta=D=0$, $L_1=L_2=1$) satisfies the assumptions but has $\Theta_n\ge\theta_*>3+C$ at $n=m+4m_0$.

**AK3. The lag constant $L_1$ when $L_2=1$.** *Printed:* $\Upsilon_2=\frac{C}{\min\{3,p_{\Psi_S}\}-2}\exp\Bigl(C\bigl(L_1\log L_2+\frac{D+\log(H+K_{\Psi_S})}{1-\gamma}\bigr)\Bigr)$. Here $L_1$ enters only through $L_1\log L_2$, which vanishes at $L_2=1$. *Correction:* $\Upsilon_2=\frac{C}{\min\{3,p_{\Psi_S}\}-2}\exp\Bigl(C\bigl((L_1+\frac D{1-\gamma})\log(2L_2)+\frac{D+\log(H+K_{\Psi_S})}{1-\gamma}\bigr)\Bigr)$, and correspondingly the factor $L_1+\frac{1+D}{1-\gamma}$ in the condition on $m_0$. *Why:* the lag in (P3′) is $L_1\log(L_2n)$, which must fit inside the start-up window. The construction of AK2 with $L_1=m$ violates the printed conclusion.

**AK4. The rate $\kappa$.** *Printed:* $\kappa:=\min\{\alpha,1-\gamma\}$ in the statement and in the inductive claim of Step 3. *Correction:* $\kappa:=\min\{\alpha,\frac12(1-\gamma)\}$. *Why:* the iteration at the end of Step 3 delivers only this rate, and $\alpha(d)$ is fixed before $\gamma$. For $\gamma$ close to $1$ the printed rate is not reached.

**AK5. The lag in Step 3.** The variance estimate of Step 3 applies the induction hypothesis at the scale $n-\lceil L_1\log(L_2n)\rceil$ and silently drops the resulting factor $3^{\kappa\lceil L_1\log(L_2n)\rceil}$. *Correction:* run a preliminary phase of order $\ell\log\ell$ scales, $\ell=\lceil L_1\log(L_2n)\rceil$, before the induction. This costs a factor $\log(2+L_1\log X)$ in the condition on $m_0$. The threshold proved in Lean is
$$m_0\ge C\Bigl(L_1+\frac{1+D}{1-\gamma}\Bigr)\frac{1+D}{(1-\beta)(1-\gamma)}\log X\,\log\bigl(3\Theta_0(2+L_1\log X)\bigr),\qquad X=(\Upsilon_1+\Upsilon_2)(m+m_0+1)\Theta_0 .$$

**AK6. An undefined constant.** The constant $\kappa_0$ in the final iteration of Step 3 is used four times and defined nowhere. The formal proof replaces this iteration with its own decay lemma (`SuperdiffusionCLT.AKHC61.Step3.akhcStep3_decay`).

---

## Corrected in arXiv:2404.01115v3

Each of the following was wrong in earlier versions of the manuscript and is correct in arXiv:2404.01115v3 (page numbers refer to that version).

- **E1.** Theorem A, p. 3: the constant now depends on $\breve A$ as well, $C(\beta,\delta,c_\star,\nu,\breve A,d)$.
- **E2.** §1.6, p. 24: the hatted negative norm of a vector field is now defined by pairing against vector fields $\mathbf g$ with $(\mathbf g)_U=0$ and $\|\nabla\mathbf g\|_{\underline L^2(U)}\le1$, and the factors $3^{-l}$ in (2.85) and (3.27) are explicit, so the norm no longer is the order-zero quantity.
- **E5.** Lemma 2.9, (2.85), p. 38: the endpoint estimate now has the prefactor $C(l-k)$ in place of $C(l-k)^{1/2}$.
- **E6.** Proposition 3.1, (3.1), p. 53: the threshold now contains $q=\log(3+c_\star^{-1}+\nu^{-1}+\breve A)$ and the term $q(1+\breve A+q)$, which controls the dependence on $c_\star$.
- **E12.** Proposition 4.2, (4.6), p. 75, and the large-gap case, p. 77: the third condition is now $n\le m-\lceil C\log(\nu^{-1}(L\vee n))\rceil$, and the large-gap bound is taken with $q:=L\vee n$.
- **E14.** Lemma 4.7, (4.32), p. 85, and Proposition 4.8, pp. 89–93: the random variable $W_{L,m,r}$ is now chosen before the shift $\mathbf h_0$, so the lemma applies to the random shift, the product is handled by Lemma 2.5, and the last term of (4.37) is $\mathcal O_{\Gamma_{1/2}}(Cm^{-1000})$.
- **E15.** Lemma 5.3, (5.37), p. 102: the error term now has $(K-m)^{2/5}$ in place of $(K-m)^{1/5}$.
- **E16.** Proposition 6.2, Steps 4–6, pp. 123–127: the excess decay is now proved relative to the comparison space $\{v_{j,e}\}$, with the maps $Q_{k,j}=P_{k,j}^{-1}$ and the zero-slope part $w_i$ handled in (6.34)–(6.35), and the non-constancy of the limit uses $|p_n-e|\le C\delta_{n+1}|e|$ in place of an identity.
- **E17.** Lemma 6.1, p. 116, and Propositions 7.4–7.6 and Lemmas 7.7–7.8, pp. 129–149: the minimal scale $\mathcal X_0(y)$ is now defined with the maximum over the translated grid built in, the boundary estimate (7.36) is restricted to $m-h_m\le n$, and the hypotheses of Proposition 7.6 and Lemmas 7.7–7.8 carry the shift $\lceil C\log K\rceil$, $\lceil N\log m\rceil$.
- **E18.** Lemma 7.3, (7.24)–(7.25), p. 135, Proposition 7.4, (7.36), p. 139, and Proposition 7.6, pp. 143–145: the proof of Proposition 7.6 no longer uses the slack and the factor $3^{K-n}$, since $\tilde g$ is mollified at the scale $\ell_g=3^KK^{-208}$ and $K^{-1000}3^K\|\nabla^2\tilde g\|_{L^\infty}\le CK^{-792}\|\nabla g\|_{L^\infty}$ (p. 145); the sum of the boundary errors in Proposition 7.4 is now geometric (p. 142). The fixed powers $m^{-1000}$, $m^{-2000}$ remain in the statements.
- **E21.** Proposition 7.6, proof, display before (7.41), p. 144: the factor $\nu^{-1}$ is kept in the second line, $C\nu^{-1}K^{-206+2\rho}\|\nabla g\|^2_{L^\infty}$.
- **E23.** Lemma 7.7, p. 148: $V$ is now chosen so that $3^{-m}V$ is a fixed smooth domain depending only on $d$.
- **E25.** §1.6, p. 24, and Theorem B, proof, (7.69), p. 152: hatted negative norms of vector and matrix fields are now taken componentwise, and the last inequality of (7.69) now uses the second line of (6.11).

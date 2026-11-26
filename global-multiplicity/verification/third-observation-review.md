# Third observation in a catenary model

Technical review, 26 November 2026. Three independent agent assignments covered the physical reconstruction, the exceptional family, and the relation to earlier results. This document records reproducible checks and their scope. External journal peer review remains open.

## Statement reviewed

The inlet is 1. The measured sites are 3, the last site $n$, and a distinct site $r$. The leak site is known and the same in both candidate models; the leak rate and all directed edge rates are unknown and positive. Equal observations mean equal amounts under every continuous input from zero initial conditions.

1. For any allowed $r$ and any leak site, a generic positive parameter vector is the only positive vector producing its data. Its competitors may be exceptional.
2. If every positive point must be covered for every known leak site, every choice works at lengths 4–6. At length 7 and above the choices are exactly 1, 2 and 4.
3. At each remaining position $5\le r<n$ and length $n\ge7$, two positive regular vectors coexist for leak site 1. Regular means that the original square *two-output* coefficient map has invertible derivative at both vectors. The two vectors can therefore be locally distinguishable from their neighbours even though they give exactly the same three curves as one another.

The quantifier over leak sites in (2) matters. Failure of a uniform guarantee does not give a collision for every individual leak site. The seven-compartment rational certificate provides a second leak site with such a collision. The experiment uses ideal continuous measurements; no clinical precision or sampling claim follows.

## Findings and resulting edits

- **Previous proof of part of the generic claim.** A public theorem of 24 November already gives generic global uniqueness with outputs $j,k$ alone when the inlet is 1 and $j-1\le n-k$. Taking $j=3$ and $k=r$ yields the entire interval $4\le r\le n-2$. This is stronger there because it dispenses with the terminal output. The manuscript now identifies that direct specialization, and the new Lean module also proves it from the old theorem. [Earlier exact statement](https://github.com/qqhgdkktu/catenary-identifiability/blob/7300631e25bea9a7afe03e6426122d93010a423d/Chain/EndpointExterior.lean#L329-L340)
- **Independent rank calculation for §3.** Scaling the orthogonality rows by the endpoint minor converts their span into the sum of the degree-at-most-$n-2$ multiples of $B_2$ and $B_{r-1}$. For $4\le r\le n-2$ the resulting dimension is $n-1-\deg\gcd(B_2,B_{r-1})$. This agrees with the direct reconstruction. At $r=n-1$ the dimension argument above no longer gives generic uniqueness. The proof in §4 uses the terminal edge rate obtained from the ratio of two observed curves. [Castillo and Gordillo-Núñez, Lemma 2.1 and §6](https://arxiv.org/abs/2602.20894) · [Placement preprint, Appendix C.2](https://doi.org/10.5281/zenodo.22909460)
- **Exceptional family in §5.** The reviewer checked coprimality, the independence of normalization and the fixed leading coefficient, and preservation of the third transfer function in the two block constructions. The text now restricts the deformation to the constructed segment with $F,G,K$ fixed. The reviewer independently recovered positive rates and recomputed the three responses with rational arithmetic for selected interior and boundary placements. The shipped block script checks the algebraic prerequisites for all 27 placements at lengths 7 through 12. This finite test supplements the all-length argument.
- **Independent check of regularity along the slice.** At leak site 1, writing $x_i$ for positive spectral nodes and $\rho_i$ for right endpoint weights gives $D(0)/q=D(0)^2\sum_i 1/(x_i F'(x_i)^2\rho_i)$. The endpoint cofactor and the zero-frequency resolvent give the identity. Along the admissible line each weight varies affinely, at least one varies nontrivially, and one vanishes at either end. The sum is strictly convex, diverges at both ends, and each level above its minimum is attained with two nonzero, opposite slopes. The manuscript includes this check. Physical regularity also uses the local spectral coordinate chart.
- **Seven compartments.** For inlet 1, leak 5 and outputs 3, 6, 7, the script reconstructs both positive vectors and compares the complete numerator polynomials and common denominator exactly. It computes opposite signs for the two Jacobians. A separate Lean proof uses rational matrix intertwining to establish equality of all three physical curves for every continuous input and inequality of the two elimination rates. The physical derivatives are checked independently in Lean by differentiating the coefficient map and verifying two exact rational matrix factorizations. [Exact certificate](verify_seven_collision.py) · [Lean proof](../lean/ThirdSeven.lean)

## Search for previous results

Sources were checked for the measurement geometry, the allowed parameter set and the distinction between generic, all-positive and regular-fibre statements. The two-output theorem above and the following comparisons matter for any claim of priority.

| Source | What it establishes or assumes |
|---|---|
| [Ahmed et al., Theorem 5.1 and §6](https://doi.org/10.1137/25M1728636) | Compartmental input–output equations and a research direction on multiple inputs or outputs. |
| [Bortner et al., Theorem 5.2](https://arxiv.org/abs/2106.08487) | Generic local identifiability of bidirected trees with one inlet and one output. |
| [Anonymous placement preprint, Theorem 1 and Appendix C.2](https://doi.org/10.5281/zenodo.22909460) | The main placement theorem concerns generic local identifiability. The one-sided rank analysis also bears on the generic interior case above. |
| [Gesztesy and Simon, Theorems 4.1–4.2](https://doi.org/10.1007/BF02788147) | Recovery of a Jacobi matrix from endpoint data and partial inverse data. These results account for important positive cases. |
| [Castillo and Gordillo-Núñez, Lemma 2.1 and §§3, 5–6](https://arxiv.org/abs/2602.20894) | Reconstruction from nested polynomial spectra using linear equations for positive weights. The gain constraints of the present physical experiment add information. |
| [Michor and Teschl, Theorem 2.1](https://arxiv.org/abs/math/0211051) | Uses the full spectrum and the spectra of the two complementary blocks formed by removing one site. The measured principal blocks here are nested. |
| [Clemens et al.](https://arxiv.org/abs/2506.21889) | Classifies identifiable parameters for mammillary graphs with a central compartment and peripheral leaves. The physical graph here is a path. |

The search found no earlier statement giving the uniform cutoff together with positive regular collisions for every excluded placement, or the same all-length penultimate-sensor result with its physical gains. This is a bounded search conclusion; priority remains open to further references.

## What the Lean kernel checks

The formal model uses indices from 0. Its `SameCurves` proposition quantifies over every continuous input, every nonnegative time and both output amounts. The new wrappers specify the three measured amounts using two such pairs. The auditor allows only `propext`, `Classical.choice` and `Quot.sound`.

| Scope | Entry point |
|---|---|
| Physical uniqueness for every positive vector in every uniformly sufficient placement, including the two short end cases | [uniform_sufficiency](../lean/ThirdObservation.lean), [short and adjacent cases](../lean/ThirdAdjacent.lean) |
| Generic global uniqueness for every allowed third site, length and prescribed leak, against every positive competitor | [generic_all_sites](../lean/ThirdObservation.lean), [interior cofactors](../lean/ThirdGeneric.lean), [penultimate determinant](../lean/ThirdTerminal.lean) |
| The penultimate exceptional polynomial is genuinely nonzero in physical coordinates | [three_inert_chambers](../lean/ThirdTerminalWitness.lean) constructs a boundary witness. [positive_witness](../lean/ThirdTerminal.lean) deduces a strictly positive witness for each leak site. |
| Uniqueness of a normalized quadratic reweighting from two orthogonality equations under the stated nonvanishing hypotheses | [quadratic_weight_uniqueness](../lean/ThirdWeights.lean) |
| Two transverse equal-gain points on a nonconstant normalized affine line of positive weights, for every intermediate level below its value at the center | [normalized_slice_two_gains](../lean/ThirdExceptional.lean) |
| A positive physical collision with different elimination rates for sites 3, 6, 7 and leak 5, with opposite nonzero Jacobian signs | [physical_collision](../lean/ThirdSeven.lean), [physical_regular](../lean/ThirdSevenRegular.lean) and [seven_regular_pair](../lean/ThirdObservation.lean) |

The formal reduction [full_iff_collision_family](../lean/ThirdObservation.lean) identifies precisely what still needs an all-length physical proof in Lean. Given the positive and generic conclusions above, the whole classification is equivalent to exhibiting a pair of distinct positive models at leak 1 for every excluded length and site, with equal three curves and nonzero derivatives of the original two-output map at both models. The manuscript gives that construction. The remaining formal work concerns realization of the block and spectral deformations with all three curves fixed and transfer of transversality to the physical Jacobian.

## Reproduction

From the repository root, run the following with Python 3.10+ and the pinned Lean toolchain on PATH.

~~~sh
python3 -m pip install sympy==1.14.0
python3 global-multiplicity/verification/verify_seven_collision.py
python3 global-multiplicity/verification/verify_exceptional_blocks.py
python3 global-multiplicity/verification/verify_third_sensor.py
python3 global-multiplicity/verification/verify_reconstruction.py
python3 global-multiplicity/verify_global.py --fetch
~~~

The build recompiles the Lean modules, audits their transitive axioms and checks a deliberately false uniqueness statement. The separate flag `--require-third-theorem` requires a single term of the entire physical classification type, including all-length regular collisions. That stronger check is expected to fail in this version. [Formal target and physical theorem statements](../lean/ThirdObservation.lean)

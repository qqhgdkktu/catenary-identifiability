# Positive regular fibers of a catenary compartmental model with two outputs

Mikita Aharodni · 25 November 2026

[English paper (PDF)](paper/positive-multiplicity.pdf) · [English LaTeX source](paper/positive-multiplicity.tex) · [Russian paper (PDF)](paper/positive-multiplicity-ru.pdf) · [Russian LaTeX source](paper/positive-multiplicity-ru.tex)

On a bidirected chain with $n\ge4$ compartments, let the input enter compartment 1 and observe amounts at compartments 3 and $n$. Assume zero initial amounts and a single leak at the prescribed compartment $\ell$. All $2n-1$ transfer and leak rates are positive and unknown. For any pair of exact input–output responses, count the distinct positive parameter vectors producing those responses at which the observation map has nonsingular derivative. The maximum of this count over attainable responses is

$$
M(n,\ell)=
\begin{cases}
1,&\ell=3\text{ or }\ell=n,\\
2,&\text{otherwise}.
\end{cases}
$$

The paper proves the upper bound and its attainment for all chain lengths. At a data point with two regular positive solutions both continue on an open neighborhood. The theorem leaves the number of singular and complex solutions unspecified. The related [earlier paper](../paper/two-output-catenary-identifiability.pdf) treats generic local identifiability for arbitrary inlet and output positions.

For $n\ge5$ with a leak at $n-1$, two regular solutions give different elimination rates $h$ on a nonempty open set of data. If the two spectral polynomials $D,W$ are coprime and the proximal gain $p$ is fixed, at most one distal gain $q$ admits two regular solutions with the same $h$. A five-compartment example attains this exceptional level. The backward rate $b_{n-1}$ distinguishes the two solutions even there.

## Formal verification

The full analytical claim is stated as `Catenary.GlobalMultiplicity.SharpCount`. The following parts have kernel proofs. There is no end-to-end Lean proof of `SharpCount` for all lengths in this package.

| Claim verified by Lean | Entry point |
|---|---|
| Equality of the physical data vector is equivalent to equality of both zero-state output curves, for all lengths | [data_iff_curves](lean/GlobalPhysical.lean) |
| Physical gain and complementary-minor identities for arbitrary length | [gain_eq_cofactor_quotient](lean/GlobalCofactors.lean) |
| Endpoint spectral minimization, concavity, bounds for regular level crossings, and continuation to dense data | [phi_inverse_formula and phi_slice_card_le_two](lean/GlobalUpper.lean) |
| Endpoint Krylov span and the variational identity for the canonical spectral measure of any positive definite Jacobi matrix | [endpoint_krylov_iff_supported](lean/GlobalKrylov.lean), [phi_principal_inverse](lean/GlobalSpectralBridge.lean) |
| Transfer of the variational identity to a physical chain given a reversed Jacobi realization with the prescribed physical minors | [gain_div_dc_eq_phi and terminal_gain_div_dc_eq_phi](lean/GlobalGainPhi.lean) |
| Convergence of the least-squares quantities in the two extensions under the stated weight hypotheses | [liftA_gram_limit and liftB_explicit_limit](lean/GlobalLift.lean), [liftB_limit_phi](lean/GlobalVariational.lean) |
| Algebraic criterion for equal elimination rates of two distinct solutions and uniqueness of the exceptional level | [PreterminalLeak](lean/PreterminalLeak.lean) |
| Exact physical result $M(4,2)=2$ | [sharp_four_leak_two](lean/GlobalFourSharp.lean), [no_three](lean/GlobalFour.lean) |
| Two distinct positive regular physical vectors with identical curves for $(n,\ell)=(5,4)$ and determinants $3456,-4698$ | [five_seed, physical_pair and exact_real_derivatives](lean/GlobalFive.lean) |

The all-length smooth correspondence between physical rates and spectral coordinates, the conversion of regularity along the affine slice to full physical regularity, and the specialization of the attainability constructions to the physical model remain to be connected in Lean. The manuscript gives these arguments in Sections 2–7. [Technical audit of version 1 in Russian (PDF)](verification/technical-review-ru.pdf) · [LaTeX source](verification/technical-review-ru.tex)

## Elimination-rate certificates

[Derivation, exact examples and prior results (in Russian)](verification/preterminal-review-ru.md)

Run the two calculations from the repository root with Python and SymPy 1.14.0.

~~~sh
python3 -m pip install sympy==1.14.0
python3 global-multiplicity/verification/verify_preterminal.py
python3 global-multiplicity/verification/independent_preterminal_audit.py
~~~

The first script computes characteristic polynomials and Jacobians. The second differentiates a tridiagonal determinant recurrence and reconstructs the endpoint moments from the two spectral polynomials. Both check the five-compartment pair with distinct rates, the six-compartment example, and the five-compartment exception with $h=2$ at both solutions. The corresponding Jacobian determinants are $(3456,-4698)$, $(-27648,62976)$ and $(-2359296,3760128)$.

Huneke and Keen prove identifiability of the leak rate when the sole output is at the sole leak site. In the penultimate-leak experiment the leak site is unobserved. [Huneke and Keen, Proposition 4.5](https://artsci.tamu.edu/mathematics/_files/_docs/reu/results/2025/huneke-keen-report.pdf#page=9)

## Reproduce the checks

From the repository root with Python 3.9+ and [elan](https://github.com/leanprover/elan) installed, run

```sh
python3 global-multiplicity/verify_multiplicity.py
python3 global-multiplicity/verify_global.py --fetch
```

The first command uses only the Python standard library. It verifies four- and five-compartment witnesses, the coordinate-change factor, 30 physical variational identities, the symmetric family at nine lengths, and four extension sequences using rational arithmetic. A one-unit difference in a single rate yields an exact Jacobian column. Each rate enters only one column of the compartment matrix, so the full and tail determinants are affine in each rate separately. The directed gains have the same property.

The second command builds the baseline library and compiles every new proof module from source into a fresh directory. It audits transitive axioms and checks that Lean rejects a deliberately incorrect five-compartment determinant. Lean and mathlib are pinned at 4.19.0. With a populated cache, `--fetch` can be omitted. The optional `--require-all-n` additionally requires a term proving the global `SharpCount` statement and is expected to fail for this version. [Build and exact-arithmetic transcript for version 1](verification/lean-4.19.0.log)

Build the manuscript from the repository root with `tectonic global-multiplicity/paper/positive-multiplicity.tex`, or use XeLaTeX twice. The bibliography is contained in the source. The Russian manuscript uses a Cyrillic-capable text font.

# Two Outputs in a Catenary Compartmental Model

[Read the English manuscript (PDF)](paper/two-output-catenary-identifiability.pdf) · [LaTeX source](paper/two-output-catenary-identifiability.tex) · [Lean theorem](Chain/Classification.lean) · [Verification log](verification/lean-4.19.0-macos-arm64.log)

A labelled bidirected chain has $n\ge3$ compartments, one known inlet $i$, two measured amounts at $j<k$, and one leak at a known compartment $\ell$. All $2n-1$ directed transfer and leak rates are independent, positive, and unknown. With zero initial conditions and exact outputs under a known input, all rates are **generically locally structurally identifiable** exactly when

$$
j+k-n-2\le i\le j+k+1.
$$

If the inlet is between the outputs, the criterion always holds. Otherwise, count the edges from the inlet to the nearer output and the compartments beyond the farther output. The edge count must be at most the compartment count plus two. This criterion applies to every prescribed leak location.

The manuscript proves both directions for arbitrary length. [The Lean model](Chain/Model.lean) defines the forced experiment and generic local identifiability. [The main Lean theorem](Chain/Classification.lean) uses that model. A [four-compartment counterexample](Chain/GlobalCounterexample.lean) proves that global ambiguity can persist on an open set even when the local criterion holds.

## Reproduce the checks

Install [elan](https://github.com/leanprover/elan) and Python 3. From the repository root, run

```sh
python3 verify.py --fetch --require-classification
```

The project pins Lean 4.19.0 and the precise mathlib revision. The script builds the proofs, checks the exact type of the classification theorem, audits transitive axioms, and rejects three deliberately false controls. The kernel audit permits `propext`, `Classical.choice`, and `Quot.sound`. Omit `--fetch` if the mathlib dependency cache is already installed. A clean project rebuild with pinned external dependencies is recorded in the [verification log](verification/lean-4.19.0-macos-arm64.log).

The following exact Python checks run with the standard library. The all-placement check through $n=16$ is the longer computation.

```sh
python3 four_chambers.py
python3 experiments/verify_chain.py
python3 experiments/independent_rank.py --through 16 --boundary 24 32
python3 experiments/checks/exact_identities.py
python3 experiments/checks/referee_exact_tangent.py
```

To rebuild the English PDF, run `tectonic paper/two-output-catenary-identifiability.tex` or run XeLaTeX twice on the same source.

## Relation to prior work

Ahmed et al. asked for a classification with multiple inputs or outputs in Section 6 of their article. The same placement rule for this one-inlet, two-output, one-leak setting follows from the broader theorem stated in the September 2026 unrefereed preprint *A placement criterion for catenary compartment models*. This repository gives a direct proof for the narrower setting and a formalization of that proof's conclusion. Appendix B of the manuscript spells out the specialization. [Ahmed et al., §6](https://doi.org/10.1137/25M1728636) · [Preprint, Theorem 1](https://zenodo.org/records/22909460)

Prepared for review by **Mikita Aharodni**. OpenAI models used through Codex contributed to proof development, the Lean formalization, technical review, and English translation. This is a research note for independent specialist review.

Please cite the [versioned release](https://github.com/qqhgdkktu/catenary-identifiability/releases/tag/v0.1.0) and the [citation metadata](CITATION.cff) when referring to this package.

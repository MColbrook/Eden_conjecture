# Aperiodic maximisers of Lyapunov dimension

Lean formalisation of Matthew J. Colbrook's paper, *Aperiodic maximisers of Lyapunov dimension: a counterexample to the unrestricted form of Eden's conjecture*.

For every real parameter $c>4$, the paper constructs a polynomial differential equation on Euclidean ℝ⁵ with uniformly negative divergence and a compact global attractor $A$. Its Lyapunov dimension is $4+4/c$, attained precisely on an invariant two-torus carrying an irrational linear flow. The maximum over equilibria and periodic orbits is $3$. The same maxima and maximising sets hold for the finite-time local dimension at every positive real time and for the asymptotic Kaplan–Yorke dimension.

[Solution.lean](Solution.lean) contains 219 results covering the main theorem, both lemmas, the calculations in their proofs, and the further results in the paper. The [Eden](Eden) library contains 777 supporting theorems. [COVERAGE.md](COVERAGE.md) describes the correspondence with the paper and the organisation of the library. [READING_GUIDE.md](READING_GUIDE.md) gives a route through the statements and definitions for a mathematical review.

## Compilation

Install [elan](https://github.com/leanprover/elan), then run these commands from the repository root:

```sh
lake exe cache get
lake build Eden Solution
```

The toolchain is Lean **4.33.1**, specified in [lean-toolchain](lean-toolchain). Mathlib is pinned to commit `0df444a360eaa60ab8c11dca51a86af692955474`; [lake-manifest.json](lake-manifest.json) pins its transitive dependencies. The first build downloads the toolchain and dependencies.

To use the results in another Lean file:

```lean
import Solution

#check EdenVerified.main_theorem
#check EdenVerified.attractor_lemma
#check EdenVerified.planar_singular_value_lemma
```

## Statement comparison and axioms

[Challenge.lean](Challenge.lean) gives the theorem statements for comparison with the proofs in `Solution.lean`. Its `sorry` placeholders specify the comparison targets. It is compiled separately and is not imported by the proof library or by `Solution.lean`.

```sh
lake build Challenge
lake env lean checks/FinalAxioms.lean
lake env lean checks/SupportingAxioms.lean
```

The axiom reports cover all 219 final results and all 777 public supporting theorems. The permitted axioms are `propext`, `Classical.choice`, and `Quot.sound`. [checks/README.md](checks/README.md) gives the Lean Comparator instructions. The [verification record](checks/VERIFICATION.md) lists the completed checks.

The proofs use exact identities and analytic estimates. [formalization.yaml](formalization.yaml) contains the project metadata, source information, and verification scope. Attribution for Mathlib results and adapted arguments appears in the relevant module headers.

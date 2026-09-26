# Lagrange Barycentric Coefficients

## Difficulty

This is a Lean 4 / Mathlib formalization task in the formal mathematics and theorem-proving domain.  The solver is asked to build three dependent results rather than prove an isolated proposition.

The core result identifies an arbitrary coefficient of a polynomial of degree below the number of interpolation nodes with a barycentric weighted finite sum.  Its weights use the Lagrange denominator and its coefficient term is expressed through a powerset-card elementary symmetric sum.  Two follow-up results force the solver to manage the cardinal arithmetic behind a third-from-leading coefficient and the normalization of barycentric moments.

The difficulty is mathematical and formal rather than artificial.  A successful proof has to coordinate interpolation uniqueness, the explicit Lagrange expansion, polynomial coefficient maps, finite products, erased finsets, natural-number subtraction, and finite sums over subsets of fixed cardinality.

## Reference solution

`solution/solve.sh` writes a complete `/app/Solution.lean` containing the three theorem declarations.  The reference proof is intentionally ordinary Lean/Mathlib proof engineering rather than a generated certificate or a special evaluator.

The main route is to rewrite a degree-bounded polynomial as its Lagrange interpolant, use the explicit barycentric expansion of that interpolant, take coefficients termwise, and invoke the finite-product coefficient theorem for factors of the form `X - C a`.  The second theorem specializes the first at `s.card - 3`.  The third applies the general formula to a monomial and reduces the resulting coefficient to the appropriate Kronecker-style case distinction.

## Verification

`tests/test.sh` runs pytest with `pytest-json-ctrf`, and every path writes `/logs/verifier/reward.txt` containing exactly `0` or `1`.

The sealed Lean checker copies the artifact into a clean Mathlib project and independently checks the exact types of all required declarations.  It compiles independent examples of the required theorem types, prints the axiom dependencies of the three theorems, and rejects `sorryAx` or any axiom outside the small kernel whitelist.  It also rejects source use of the two explicitly forbidden near-shortcuts named in the instruction.

The verifier never reads `solution/`, `authoring/`, or any agent-writable state other than the declared `/app/Solution.lean` artifact.

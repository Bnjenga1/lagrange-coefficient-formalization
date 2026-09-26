# Formalize a coefficient formula for finite Lagrange interpolation

Work in the supplied Lean 4 + Mathlib environment and create `/app/Solution.lean`.

The goal is to formalize a small, reusable result about barycentric Lagrange interpolation.  The development should be mathematically exact, kernel checked, and independent of any unpublished files.

Your file must define the following three theorems in the root namespace.

First, prove the general coefficient identity.

```lean
theorem lagrange_coeff_formula
    {ι F : Type*} [DecidableEq ι] [Field F]
    (s : Finset ι) (v : ι → F) (P : Polynomial F)
    (hvs : Set.InjOn v (↑s : Set ι))
    (hP : P.degree < (s.card : WithBot ℕ))
    {k : ℕ} (hk : k < s.card) :
    P.coeff k =
      ∑ i ∈ s,
        (Polynomial.eval (v i) P /
          ∏ j ∈ s.erase i, (v i - v j)) *
          ((-1 : F) ^ ((s.erase i).card - k) *
            ∑ t ∈ (s.erase i).powersetCard ((s.erase i).card - k),
              ∏ a ∈ t, v a) := by
  ...
```

Second, specialize the identity to the coefficient three places below the leading term.  This theorem must be stated exactly as follows.

```lean
theorem lagrange_coeff_card_sub_three
    {ι F : Type*} [DecidableEq ι] [Field F]
    (s : Finset ι) (v : ι → F) (P : Polynomial F)
    (hvs : Set.InjOn v (↑s : Set ι))
    (hs : 3 ≤ s.card)
    (hP : P.degree < (s.card : WithBot ℕ)) :
    P.coeff (s.card - 3) =
      ∑ i ∈ s,
        (Polynomial.eval (v i) P /
          ∏ j ∈ s.erase i, (v i - v j)) *
          (∑ t ∈ (s.erase i).powersetCard 2,
            ∏ a ∈ t, v a) := by
  ...
```

Finally prove the barycentric moment identity.  It is the normalization statement obtained from the general coefficient formula by applying it to monomials.

```lean
theorem barycentric_moment_identity
    {ι F : Type*} [DecidableEq ι] [Field F]
    (s : Finset ι) (v : ι → F)
    (hvs : Set.InjOn v (↑s : Set ι))
    (m : ℕ) (hm : m < s.card) :
    ∑ i ∈ s,
      (v i) ^ m /
        ∏ j ∈ s.erase i, (v i - v j) =
      if m = s.card - 1 then 1 else 0 := by
  ...
```

The three statements are related.  The first is the core formalization.  The second should be obtained by specializing the first at `k = s.card - 3`; the finite-set cardinality of `s.erase i` is part of the reasoning.  The third is a consequence of the same coefficient formula applied to a monomial and should handle both the vanishing lower moments and the final normalization.

Use the installed Mathlib library, and use ordinary documentation or source search as needed.  Do not assume that an informal mathematical proof is enough: the submitted file must elaborate and typecheck in the supplied environment.

The result must be fully kernel checked.  Do not use `sorry`, `admit`, user-defined axioms, unsafe declarations, `native_decide`, or other mechanisms that move the mathematical obligation outside Lean's kernel.  Do not simply invoke an existing theorem whose statement is already the requested barycentric coefficient formula.  In particular, do not use `Lagrange.coeff_eq_sum` or `Lagrange.eval_iterate_derivative_eq_sum` as a substitute for the requested development.

Do not modify the installed Mathlib sources.  The verifier uses an independent copy of the environment after your container is removed and checks the submitted theorem statements, compilation, and the axiom dependencies of the resulting declarations.

Your only required deliverable is:

`/app/Solution.lean`

You may include explanatory comments in that file, but do not place the proof in another path and expect the verifier to reconstruct it.

You have 21600 seconds to complete this task. Do not cheat by using online solutions or hints specific to this task.

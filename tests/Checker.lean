import Mathlib
import Submission.Solution

open scoped BigOperators

example
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
              ∏ a ∈ t, v a) :=
  lagrange_coeff_formula s v P hvs hP hk

example
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
            ∏ a ∈ t, v a) :=
  lagrange_coeff_card_sub_three s v P hvs hs hP

example
    {ι F : Type*} [DecidableEq ι] [Field F]
    (s : Finset ι) (v : ι → F)
    (hvs : Set.InjOn v (↑s : Set ι))
    (m : ℕ) (hm : m < s.card) :
    ∑ i ∈ s,
      (v i) ^ m /
        ∏ j ∈ s.erase i, (v i - v j) =
      if m = s.card - 1 then 1 else 0 :=
  barycentric_moment_identity s v hvs m hm

#print axioms lagrange_coeff_formula
#print axioms lagrange_coeff_card_sub_three
#print axioms barycentric_moment_identity

#!/bin/sh
set -eu

cat > /app/Solution.lean <<'LEAN'
import Mathlib

set_option maxRecDepth 100000
set_option maxHeartbeats 800000

open scoped BigOperators

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

  have hinterp :
      P = (Lagrange.interpolate s v)
        (fun i => Polynomial.eval (v i) P) :=
    Lagrange.eq_interpolate hvs hP

  have hcoeff :=
    congrArg (fun Q : Polynomial F => Q.coeff k) hinterp

  rw [Lagrange.interpolate_eq_sum] at hcoeff
  rw [Polynomial.finsetSum_coeff] at hcoeff
  simp only [Polynomial.coeff_C_mul] at hcoeff

  rw [hcoeff]

  refine Finset.sum_congr rfl ?_
  intro i hi

  have hk' : k ≤ (s.erase i).card := by
    rw [Finset.card_erase_of_mem hi]
    exact Nat.le_pred_of_lt hk

  have hk'' : k ≤ Multiset.card ((s.erase i).val.map v) := by
    rw [Multiset.card_map]
    simpa only [Finset.card_def] using hk'

  have hcoeff' :=
    Multiset.prod_X_sub_C_coeff
      ((s.erase i).val.map v) hk''

  have hcoeff'' := hcoeff'

  rw [Multiset.card_map] at hcoeff''

  have hcoeff''' :
      (Multiset.map
          (fun j => Polynomial.X - Polynomial.C (v j))
          (s.erase i).val).prod.coeff k =
        (-1 : F) ^ ((s.erase i).val.card - k) *
          (Multiset.map v (s.erase i).val).esymm
            ((s.erase i).val.card - k) := by

    rw [← Multiset.map_map]
    simpa only [Function.comp_def] using hcoeff''

  have hprod :
      (∏ j ∈ s.erase i,
        (Polynomial.X - Polynomial.C (v j))).coeff k =
        (-1 : F) ^ ((s.erase i).card - k) *
          ∑ t ∈ (s.erase i).powersetCard ((s.erase i).card - k),
            ∏ a ∈ t, v a := by

    rw [Finset.prod_eq_multiset_prod]
    rw [← Finset.esymm_map_val]
    exact hcoeff'''

  rw [hprod]

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

  have hk : s.card - 3 < s.card := by omega
  have h := lagrange_coeff_formula s v P hvs hP hk

  refine h.trans ?_
  refine Finset.sum_congr rfl ?_
  intro i hi

  have hcard : (s.erase i).card = s.card - 1 :=
    Finset.card_erase_of_mem hi

  rw [hcard]

  have hdiff : (s.card - 1) - (s.card - 3) = 2 := by omega

  rw [hdiff]
  norm_num

theorem barycentric_moment_identity
    {ι F : Type*} [DecidableEq ι] [Field F]
    (s : Finset ι) (v : ι → F)
    (hvs : Set.InjOn v (↑s : Set ι))
    (m : ℕ) (hm : m < s.card) :
    ∑ i ∈ s,
      (v i) ^ m /
        ∏ j ∈ s.erase i, (v i - v j) =
      if m = s.card - 1 then 1 else 0 := by

  classical

  let P : Polynomial F := Polynomial.X ^ m

  have hP : P.degree < (s.card : WithBot ℕ) := by
    simpa [P, Polynomial.degree_X_pow] using
      (WithBot.coe_lt_coe.mpr hm :
        (m : WithBot ℕ) < (s.card : WithBot ℕ))

  have hk : s.card - 1 < s.card := by omega

  have h :=
    lagrange_coeff_formula s v P hvs hP
      (k := s.card - 1) hk

  have hcoeff :
      P.coeff (s.card - 1) =
        if m = s.card - 1 then 1 else 0 := by

    by_cases hlast : m = s.card - 1

    · simp [P, hlast]

    · have hne : s.card - 1 ≠ m := by
        intro hEq
        exact hlast hEq.symm
      simp [P, hlast, hne]

  have hsum :
      (∑ i ∈ s,
        (Polynomial.eval (v i) P /
          ∏ j ∈ s.erase i, (v i - v j)) *
          ((-1 : F) ^ ((s.erase i).card - (s.card - 1)) *
            ∑ t ∈ (s.erase i).powersetCard
              ((s.erase i).card - (s.card - 1)),
              ∏ a ∈ t, v a)) =
        ∑ i ∈ s,
          (v i) ^ m /
            ∏ j ∈ s.erase i, (v i - v j) := by

    refine Finset.sum_congr rfl ?_
    intro i hi

    have hzero :
        (s.erase i).card - (s.card - 1) = 0 := by
      rw [Finset.card_erase_of_mem hi]
      omega

    rw [hzero]

    simp [P]

  rw [hcoeff, hsum] at h
  exact h.symm

LEAN

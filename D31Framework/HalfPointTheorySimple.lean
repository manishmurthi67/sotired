/-
  D31 Framework: Half-Point Theory - SIMPLIFIED
  
  Proof that all numbers ≥ 2 are gap-prime using the gap-of-2 strategy
-/

import D31Framework.CoreTheory

namespace D31Framework

/-- Gap of 2 works for all n ≥ 3 -/
theorem gap_two_universal (n : Nat) (h : n ≥ 3) : D31.gap n (n - 2) = 2 := by
  unfold D31.gap
  simp
  -- Since n ≥ 3, we have n ≥ n - 2, so gap computes n - (n-2) = 2
  have h1 : n ≥ n - 2 := Nat.sub_le n 2
  have h2 : n - (n - 2) = 2 := by
    have : n ≥ 2 := Nat.le_trans (by decide : 2 ≤ 3) h
    exact Nat.sub_sub_self this
  exact h2

/-- Every n ≥ 3 has prime gap of 2 to n-2 -/
theorem gap_prime_for_n_geq_3 (n : Nat) (h : n ≥ 3) :
  ∃ m, m < n ∧ D31.isPrime (D31.gap n m) = true := by
  exists (n - 2)
  apply And.intro
  · -- Prove n - 2 < n
    have h1 : 0 < n := Nat.zero_lt_of_lt (Nat.lt_of_succ_le h)
    have h2 : 0 < 2 := by decide
    exact Nat.sub_lt h1 h2
  · -- Prove gap is prime (gap = 2)
    have : D31.gap n (n - 2) = 2 := gap_two_universal n h
    rw [this]
    rfl  -- D31.isPrime 2 = true by definition

/-- For n = 2, gap to 0 is 2 (prime) -/
theorem gap_prime_for_two : ∃ m, m < 2 ∧ D31.isPrime (D31.gap 2 m) = true := by
  exists 0

/-- MAIN THEOREM: All numbers ≥ 2 are gap-prime -/
theorem gap_prime_all (n : Nat) (h : n ≥ 2) : D31.isGapPrime n = true := by
  unfold D31.isGapPrime
  simp
  apply And.intro
  · exact h
  · -- Show existence of prime gap
    by_cases h3 : n ≥ 3
    · exact gap_prime_for_n_geq_3 n h3
    · -- n = 2 case
      have : n = 2 := by
        have h4 : n < 3 := Nat.lt_of_not_le h3
        have h5 : n ≤ 2 := Nat.le_of_lt_succ h4
        exact Nat.le_antisymm h5 h
      rw [this]
      exact gap_prime_for_two

#check gap_prime_all  -- ✓ THE PROOF IS COMPLETE!

end D31Framework

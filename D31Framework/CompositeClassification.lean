/-
  D31 Framework: Exhaustive Composite Classification [4-31]
  
  Core Insight: Don't use infinite induction - enumerate and classify!
  
  Categories:
  1. Absorbers (powers of 2): 4, 8, 16
  2. Bridges (2×p): 6, 10, 14, 22, 26
  3. Meta-Bridges (4×p, 8×p): 12, 20, 28
  4. Prime-Prime Bridges (p×q, no 2): 15, 21
  5. Prime Powers (p^n): 9, 25, 27
  6. Multi-Bridges (2×3×5...): 30
-/

import D31Framework.CoreTheory

namespace D31Framework

/-! ## Category Definitions -/

/-- Absorbers: Powers of 2 (create meta-layers of distinction) -/
def isAbsorber (n : Nat) : Bool :=
  n = 4 || n = 8 || n = 16 || n = 32

/-- Bridges: 2 × prime (connect distinction to that prime) -/
def isBridge (n : Nat) : Bool :=
  n = 6 || n = 10 || n = 14 || n = 22 || n = 26

/-- Meta-Bridges: 4×p or 8×p (absorbed distinction bridges to prime) -/
def isMetaBridge (n : Nat) : Bool :=
  n = 12 || n = 20 || n = 24 || n = 28

/-- Prime-Prime Bridges: p×q where both p,q are odd primes -/
def isPrimePrimeBridge (n : Nat) : Bool :=
  n = 15 || n = 21

/-- Prime Powers: p^k for prime p, k ≥ 2 -/
def isPrimePower (n : Nat) : Bool :=
  n = 9 || n = 25 || n = 27

/-- Multi-Bridge: Product of 3+ distinct primes -/
def isMultiBridge (n : Nat) : Bool :=
  n = 30

/-! ## Exhaustive Classification -/

/-- Every composite in [4-30] belongs to exactly one category -/
def classifyComposite (n : Nat) : Option String :=
  if isAbsorber n then some "Absorber"
  else if isBridge n then some "Bridge"
  else if isMetaBridge n then some "Meta-Bridge"
  else if isPrimePrimeBridge n then some "Prime-Prime Bridge"
  else if isPrimePower n then some "Prime Power"
  else if isMultiBridge n then some "Multi-Bridge"
  else if D31.isPrime n then some "Prime"
  else if n < 4 || n > 30 then none
  else some "Unclassified"  -- Should never happen!

/-! ## Verification by Computation -/

-- Cycle 1 Composites
example : classifyComposite 4 = some "Absorber" := by rfl
example : classifyComposite 6 = some "Bridge" := by rfl

-- Cycle 2 Composites  
example : classifyComposite 8 = some "Absorber" := by rfl
example : classifyComposite 9 = some "Prime Power" := by rfl
example : classifyComposite 10 = some "Bridge" := by rfl
example : classifyComposite 12 = some "Meta-Bridge" := by rfl
example : classifyComposite 14 = some "Bridge" := by rfl
example : classifyComposite 15 = some "Prime-Prime Bridge" := by rfl
example : classifyComposite 16 = some "Absorber" := by rfl
example : classifyComposite 18 = some "Unclassified" := by rfl  -- Need to add!
example : classifyComposite 20 = some "Meta-Bridge" := by rfl
example : classifyComposite 21 = some "Prime-Prime Bridge" := by rfl
example : classifyComposite 22 = some "Bridge" := by rfl
example : classifyComposite 24 = some "Meta-Bridge" := by rfl
example : classifyComposite 25 = some "Prime Power" := by rfl
example : classifyComposite 26 = some "Bridge" := by rfl
example : classifyComposite 27 = some "Prime Power" := by rfl
example : classifyComposite 28 = some "Meta-Bridge" := by rfl
example : classifyComposite 30 = some "Multi-Bridge" := by rfl

/-! ## Missing Classifications -/
-- 18 = 2×9 = 2×3² - This is a bridge to 3² (evolved from 6)
-- Let's add it to Meta-Bridges or create new category

def isEvolvedBridge (n : Nat) : Bool :=
  n = 18  -- 2×3² (bridge to 3²)

/-! ## Complete Classification (Fixed) -/

def classifyCompositeFull (n : Nat) : Option String :=
  if isAbsorber n then some "Absorber (2^k)"
  else if isBridge n then some "Bridge (2×p)"
  else if isMetaBridge n then some "Meta-Bridge (2^k×p)"
  else if isEvolvedBridge n then some "Evolved Bridge (2×p²)"
  else if isPrimePrimeBridge n then some "Prime-Prime Bridge (p×q)"
  else if isPrimePower n then some "Prime Power (p^k)"
  else if isMultiBridge n then some "Multi-Bridge (2×3×5)"
  else if D31.isPrime n then some "Prime"
  else if n < 4 || n > 30 then none
  else some "ERROR: Unclassified Composite!"

/-! ## Theorem: All Composites [4-30] Are Classified -/

-- For now, we verify by computation for specific values
-- A full proof would enumerate all cases
example : classifyCompositeFull 4 ≠ some "ERROR: Unclassified Composite!" := by decide
example : classifyCompositeFull 6 ≠ some "ERROR: Unclassified Composite!" := by decide
example : classifyCompositeFull 8 ≠ some "ERROR: Unclassified Composite!" := by decide
example : classifyCompositeFull 9 ≠ some "ERROR: Unclassified Composite!" := by decide
example : classifyCompositeFull 10 ≠ some "ERROR: Unclassified Composite!" := by decide
example : classifyCompositeFull 12 ≠ some "ERROR: Unclassified Composite!" := by decide
example : classifyCompositeFull 14 ≠ some "ERROR: Unclassified Composite!" := by decide
example : classifyCompositeFull 15 ≠ some "ERROR: Unclassified Composite!" := by decide
example : classifyCompositeFull 16 ≠ some "ERROR: Unclassified Composite!" := by decide
example : classifyCompositeFull 18 ≠ some "ERROR: Unclassified Composite!" := by decide
example : classifyCompositeFull 20 ≠ some "ERROR: Unclassified Composite!" := by decide
example : classifyCompositeFull 21 ≠ some "ERROR: Unclassified Composite!" := by decide
example : classifyCompositeFull 22 ≠ some "ERROR: Unclassified Composite!" := by decide
example : classifyCompositeFull 24 ≠ some "ERROR: Unclassified Composite!" := by decide
example : classifyCompositeFull 25 ≠ some "ERROR: Unclassified Composite!" := by decide
example : classifyCompositeFull 26 ≠ some "ERROR: Unclassified Composite!" := by decide
example : classifyCompositeFull 27 ≠ some "ERROR: Unclassified Composite!" := by decide
example : classifyCompositeFull 28 ≠ some "ERROR: Unclassified Composite!" := by decide
example : classifyCompositeFull 30 ≠ some "ERROR: Unclassified Composite!" := by decide

/-! ## Specific Properties -/

/-- Absorbers are powers of 2 -/
-- 4 = 2², 8 = 2³, 16 = 2⁴, 32 = 2⁵
theorem absorbers_are_powers_of_two (n : Nat) :
  isAbsorber n = true → ∃ k : Nat, n = 2^k := by
  intro h
  unfold isAbsorber at h
  simp [Bool.or_eq_true] at h
  rcases h with (((h | h) | h) | h)
  · subst h; exact ⟨2, rfl⟩
  · subst h; exact ⟨3, rfl⟩
  · subst h; exact ⟨4, rfl⟩
  · subst h; exact ⟨5, rfl⟩

/-- Bridges connect distinction (2) to a prime -/
-- 6 = 2×3, 10 = 2×5, 14 = 2×7, 22 = 2×11, 26 = 2×13
theorem bridges_connect_2_to_prime (n : Nat) :
  isBridge n = true → ∃ p : Nat, D31.isPrime p = true ∧ n = 2 * p := by
  intro h
  unfold isBridge at h
  simp [Bool.or_eq_true] at h
  rcases h with ((((h | h) | h) | h) | h)
  · subst h; exact ⟨3, by decide, rfl⟩
  · subst h; exact ⟨5, by decide, rfl⟩
  · subst h; exact ⟨7, by decide, rfl⟩
  · subst h; exact ⟨11, by decide, rfl⟩
  · subst h; exact ⟨13, by decide, rfl⟩

/-- Prime-Prime Bridges are always odd (no factor of 2) -/
-- 15 = 3×5, 21 = 3×7
theorem prime_prime_bridges_are_odd (n : Nat) :
  isPrimePrimeBridge n = true → n % 2 = 1 := by
  intro h
  unfold isPrimePrimeBridge at h
  simp [Bool.or_eq_true] at h
  rcases h with h | h <;> subst h <;> rfl

/-! ## Summary -/

/-
Every composite [4-30] is classified as:

1. Absorbers (4): 4, 8, 16 = 2², 2³, 2⁴
2. Bridges (5): 6, 10, 14, 22, 26 = 2×{3,5,7,11,13}
3. Meta-Bridges (4): 12, 20, 24, 28 = 4×{3,5,6,7}
4. Evolved Bridge (1): 18 = 2×3²
5. Prime-Prime Bridges (2): 15=3×5, 21=3×7
6. Prime Powers (3): 9=3², 25=5², 27=3³
7. Multi-Bridge (1): 30 = 2×3×5

Total: 20 composites, all classified!
-/

end D31Framework

/-
# D31 Framework Examples and Tests
Demonstrates the operational theory with concrete examples
-/

import D31Framework.CoreTheory

namespace D31.Examples

open D31

/-! ## Testing Prime Operations -/

#eval primeToOperation 2   -- Distinction
#eval primeToOperation 3   -- Transformation
#eval primeToOperation 5   -- Emergence
#eval primeToOperation 7   -- Completion
#eval primeToOperation 11  -- none (cycle 2, needs extension)

/-! ## Testing Gap-Prime Theory -/

-- Every number should be gap-prime
#eval isGapPrime 2   -- true (2-0=2 is prime)
#eval isGapPrime 4   -- true (4-2=2 is prime)
#eval isGapPrime 6   -- true (6-4=2, 6-3=3, 6-1=5 all prime)
#eval isGapPrime 10  -- true (10-8=2, 10-7=3, 10-5=5 all prime)
#eval isGapPrime 15  -- true (15-13=2, 15-10=5 prime)
#eval isGapPrime 100 -- true

/-! ## Gap Function Examples -/

#eval gap 10 7   -- 3 (prime)
#eval gap 15 10  -- 5 (prime)
#eval gap 20 18  -- 2 (prime)
#eval gap 7 10   -- 3 (symmetric)

/-! ## Prime Cycle Structure -/

-- Cycle 1: primes ≤ 7
#eval primeCycle 2   -- 1
#eval primeCycle 3   -- 1
#eval primeCycle 5   -- 1
#eval primeCycle 7   -- 1

-- Cycle 2: primes 11-23
#eval primeCycle 11  -- 2
#eval primeCycle 13  -- 2
#eval primeCycle 17  -- 2
#eval primeCycle 19  -- 2
#eval primeCycle 23  -- 2

-- Cycle 3: primes 29-43
#eval primeCycle 29  -- 3
#eval primeCycle 31  -- 3
#eval primeCycle 37  -- 3
#eval primeCycle 41  -- 3
#eval primeCycle 43  -- 3

/-! ## Position Within Cycles -/

-- First cycle positions
#eval cyclePosition 2   -- some 1 (unity/first)
#eval cyclePosition 3   -- some 2 (distinction)
#eval cyclePosition 5   -- some 3 (transformation)
#eval cyclePosition 7   -- some 4 (completion)

-- Second cycle positions
#eval cyclePosition 11  -- some 1 (unity at dimension 2)
#eval cyclePosition 13  -- some 2
#eval cyclePosition 17  -- some 3
#eval cyclePosition 19  -- some 4
#eval cyclePosition 23  -- some 5

/-! ## Multi-State Computing Structures -/

def ternary := TernarySpace
def quinary := QuinarySpace
def septenary := SeptenarySpace

#eval ternary.stateCount     -- 3
#eval quinary.stateCount     -- 5
#eval septenary.stateCount   -- 7

#eval ternary.operations.length     -- 2 operations
#eval quinary.operations.length     -- 3 operations
#eval septenary.operations.length   -- 4 operations

/-! ## Demonstrating Composite Cancellation -/

-- 4 = 2×2: Only has operation from prime 2
def ops_of_4 : List Operation :=
  [2].filterMap primeToOperation

-- 6 = 2×3: Has operations from primes 2 and 3
def ops_of_6 : List Operation :=
  [2, 3].filterMap primeToOperation

-- 15 = 3×5: Has operations from primes 3 and 5
def ops_of_15 : List Operation :=
  [3, 5].filterMap primeToOperation

#eval ops_of_4   -- [Distinction]
#eval ops_of_6   -- [Distinction, Transformation]
#eval ops_of_15  -- [Transformation, Emergence]

/-! ## The First 20 Numbers and Their Gap-Prime Status -/

def testRange : List (Nat × Bool) :=
  List.range 20 |>.drop 2 |>.map (fun n => (n, isGapPrime n))

#eval testRange
-- All should be true!

/-! ## Analyzing Specific Numbers -/

-- Number 32 (important in your theory: 2^5)
#eval "Number 32:"
#eval s!"Is prime? {isPrime 32}"
#eval s!"Is gap-prime? {isGapPrime 32}"
#eval s!"Cycle: {primeCycle 32}"
#eval s!"Gap to 31: {gap 32 31}"  -- Should be 1
#eval s!"Gap to 29: {gap 32 29}"  -- Should be 3 (prime!)

-- Number 7 (completion)
#eval "\nNumber 7:"
#eval s!"Is prime? {isPrime 7}"
#eval s!"Operation: {primeToOperation 7}"
#eval s!"Cycle: {primeCycle 7}"
#eval s!"Position: {cyclePosition 7}"

/-! ## Bitcoin Wallet Example (256-bit key space) -/

-- This demonstrates the computational challenge
def bitcoinKeySpace : Nat := 2^256
#eval s!"Bitcoin key space size: ~2^256"
#eval s!"Even with prime-state advantages, this is astronomically large"

/-! ## Summary Statistics -/

def firstPrimes : List Nat := [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]

#eval "\n=== D31 Framework Summary ==="
#eval s!"First operational primes: {[2,3,5,7]}"
#eval s!"Operations defined: {[2,3,5,7].filterMap primeToOperation}"
#eval s!"All tested numbers are gap-prime: {testRange.all (·.2)}"
#eval s!"Multi-state systems defined: 3-state, 5-state, 7-state"

end D31.Examples


import Mathlib

def F (n : Nat) := 2^(2^n) + 1

#eval "Hello Lean"
#eval F 0
#eval F 1
#eval F 3
-- Click at the end of the above lines and look to the window on the right.
-- Lean will show you what the Fermat numbers evaluate to.

-- We can *prove* things about the functions we define
lemma F₀: F 0 = 3 := by
  -- Click here and look to the window on the right
  -- The window displays what we wish to prove.
  rw [F]
  -- Click at the end of the above line. With this command, we unfolded the definition of `F`
  rw [Nat.pow_zero]
  -- Click at the end of the above line. We simplified the goal with a theorem stating `∀ n, n ^ 0 = 1`.
  -- Lean infered that we meant to use the theorem with `n = 2`
  rw [Nat.pow_one]
  -- With the above command making use of the theorem stateing `∀ n, n ^ 1 = n`,
  -- the identity to prove reduces to `2+1=3`, a proof by computation which Lean performs for us.
  -- We've just proven the lemma.


example : ∀ n, Odd (F n) := by
  intro n
  cases' n with n
  · rw [F₀]
    rw [Nat.odd_iff]
    norm_num
  · rw [F]
    rw [Nat.odd_iff]
    rw [← Nat.mod_add_mod]

--#exit

-- With a lot more work, we could compute the prime decomposition of numbers:
#eval Nat.factors 4
#eval Nat.factors 5
#eval Nat.factors 6
#eval Nat.factors 37
#eval Nat.factors 42

-- Then we could prove theorems with this function:
#check Nat.mem_factors
#check Nat.prod_factors
#check Nat.four_dvd_or_exists_odd_prime_and_dvd_of_two_lt

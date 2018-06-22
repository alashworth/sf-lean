namespace induction

open nat

-- Exercise: 2 stars, recommended (basic_induction)
theorem mult_0_r : ∀ n, n * 0 = 0 
| 0 := rfl
| (nat.succ n) := rfl

theorem plus_n_Sm : ∀ n m, succ (n + m) = n + (succ m) :=
λ n m, nat.rec_on m 
  (show succ (n + 0) = n + 1, from rfl)
  (λ m' ih, 
    show succ (n + succ m') = n + succ (succ m'), from rfl)

theorem plus_comm : ∀ n m : ℕ, n + m = m + n
| 0 m := by rw [add_zero, zero_add]
| (succ n) m := by rw [succ_add, add_succ, plus_comm]

theorem plus_assoc : ∀ n m p : ℕ, n + (m + p) = (n + m) + p
| 0 m p := by rw [zero_add, zero_add]
| (succ n) m p := by rw [succ_add, succ_add, succ_add, add_assoc]

-- Exercise: 2 stars (double_plus)
def double : ℕ → ℕ
| 0 := 0
| (succ n) := succ (succ (double n)).

lemma double_plus : ∀ n, double n = n + n
| 0 := rfl
| (succ n) := by rw [add_succ, succ_add, ←double_plus]; refl

-- Exercise: 2 stars, optional (evenb_S)
def evenb : ℕ → bool
| 0 := tt
| (succ 0) := ff
| (succ (succ n')) := evenb n'

theorem evenb_S : ∀ n : ℕ, evenb (succ n) = bnot (evenb n)
| 0 := rfl 
| (succ n') := by simp [evenb]; rw [evenb_S, bnot_bnot]

end induction
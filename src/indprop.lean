open nat

inductive ev : ℕ → Prop
| ev_0 : ev 0
| ev_SS : ∀ n : ℕ, ev n → ev (succ (succ n))

open ev

-- Exercise: 1 star (ev_double)
theorem ev_double : ∀ n, ev (2 * n) :=
λ n, nat.rec_on n  
  (by rw mul_zero; constructor)
  (λ k ih, 
    begin 
      rw [two_mul, add_succ, succ_add], 
      constructor, 
      rwa [←two_mul]
    end)

theorem ev_minus2 : ∀ n, ev n → ev (pred (pred n)) := 
begin
  intros n h,
  cases h with n h₁,
    rwa [pred_zero, pred_zero],
    rwa [pred_succ, pred_succ]
end

-- Exercise: 1 star (SSSSev__even)
theorem SSSSev_even : ∀ n, ev (succ (succ (succ (succ n)))) → ev n := 
begin 
  introv h,
  induction n with n' ih,
    constructor,
    cases h with _ h,
    cases h with _ h,
    assumption
end

-- Exercise: 4 stars, advanced (subsequence)
inductive subseq {α : Type} : list α → list α → Prop
| nil : ∀ (l : list α), subseq [] l
| cons₁ : ∀ (x : α) (l₁ l₂ : list α), subseq l₁ l₂ → subseq (x :: l₁) (x :: l₂)
| cons₂ : ∀ (x : α) (l₁ l₂ : list α), subseq l₁ l₂ → subseq l₁ (x :: l₂) 

section subseq 
variables {α : Type} (l₁ l₂ : list α)

theorem subseq_refl : reflexive (@subseq α) := 
begin 
  unfold reflexive,
  intro l,
  induction l with a l' ih,
    constructor,
    exact (subseq.cons₁ a l' l' ih)
end

end subseq
import tactic.split_ifs

-- Identifiers

def beq_string (x y : string) :=
if x = y then tt else ff

theorem beq_string_refl : ∀ s, tt = beq_string s s :=
λ s, eq.symm $ if_pos rfl

theorem beq_string_true_iff (x y : string) :
  beq_string x y = tt ↔ x = y :=
begin
  unfold beq_string,
  split,
  intro h,
  simp [beq_string] at h,
  exact h,
  intro h,
  split_ifs,
  trivial
end

-- total maps

def total_map (α : Type) := string → α

def t_empty {α :Type} (v : α) : total_map α := (λ s, v)

def t_update {α : Type} (m : total_map α) (x : string) (v : α) : total_map α :=
λ x', if x' = x then v else m x'

lemma t_apply_empty : ∀ (α : Type) (x : string) (v : α), t_empty v x = v :=
sorry

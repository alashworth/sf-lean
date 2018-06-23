namespace hidden
namespace basics

inductive day : Type
| sunday | monday | tuesday | wednesday | thursday | friday | saturday

def next_weekday : day → day
| day.sunday := day.monday
| day.monday := day.tuesday
| day.tuesday := day.wednesday
| day.wednesday := day.thursday
| day.thursday := day.friday
| day.friday := day.monday
| day.saturday := day.monday

#reduce next_weekday day.sunday

example : next_weekday (next_weekday day.saturday) = day.tuesday := rfl

inductive bool' : Type
| tt | ff

open bool'

def bnot' : bool' → bool'
| tt := ff
| ff := tt

def band' : bool' → bool' → bool'
| tt tt := tt
| tt ff := ff
| ff tt := ff
| ff ff := ff

def bor' : bool' → bool' → bool'
| tt tt := tt
| tt ff := tt
| ff tt := tt
| ff ff := ff

/- bor unit tests -/
example : bor' tt ff = tt := rfl
example : bor' ff ff = ff := rfl
example : bor' ff tt = tt := rfl
example : bor' tt tt = tt := rfl

-- Exercise: 1 star (nandb)
def bnand : bool' → bool' → bool' :=
sorry -- replace `:= sorry` with your definition

lemma test_bnand1 : bnand tt ff = tt := sorry -- fill in here
lemma test_bnand2 : bnand ff ff = tt := sorry -- fill in here
lemma test_bnand3 : bnand ff tt = tt := sorry -- fill in here
lemma test_bnand4 : bnand tt tt = ff := sorry -- fill in here

-- Exercise: 1 star (band3)
def band3 (b1 : bool) (b2 : bool) (b3 : bool) : bool :=
sorry -- replace `:= sorry` with your definition


#check bool'.tt
/- ===> tt : bool' -/
#check (bnot' tt)
/- ===> bnot' tt : bool' -/


#check bnot'
/- ===> bnot' : bool' → bool' -/


lemma test_band31: (band3 tt tt tt) = tt := sorry -- fill in here
lemma test_band32: (band3 ff tt tt) = ff := sorry -- fill in here
lemma test_band33: (band3 tt ff tt) = ff := sorry -- fill in here
lemma test_band34: (band3 tt tt ff) = ff := sorry -- fill in here

-- Exercise: 1 star (factorial)
def factorial : ℕ → ℕ
| 0 := 1
| 1 := 1
| (nat.succ n) := (nat.succ n) * factorial n

lemma test_factorial1 : (factorial 3) = 6 := rfl
lemma test_factorial2 : (factorial 5) = 120 := rfl

-- Exercise: 1 star (blt_nat)
def beq_nat : ℕ → ℕ → bool
| 0 0 := tt
| 0 _ := ff
| _ 0 := ff
| (nat.succ n) (nat.succ m) := beq_nat n m

def leb : ℕ → ℕ → bool
| 0 _ := tt
| (nat.succ n) 0 := ff
| (nat.succ n) (nat.succ m) := leb n m

lemma test_leb1 : leb 2 2 = tt := rfl
lemma test_leb2 : leb 2 4 = tt := rfl
lemma test_leb3 : leb 4 2 = ff := rfl

def blt_nat : ℕ → ℕ → bool :=
λ a b, if ¬ beq_nat a b ∧ leb a b then tt else ff

lemma test_blt_nat1 : (blt_nat 2 2) = ff := rfl
lemma test_blt_nat2 : (blt_nat 2 4) = tt := rfl
lemma test_blt_nat3 : (blt_nat 4 2) = ff := rfl

-- Exercise: 1 star (plus_id_exercise)
theorem plus_id_exercise : ∀ n m o : ℕ, n = m → m = o → n + m = m + o :=
begin
  introv h1 h2,
  rw [h1, h2]
end

-- Exercise: 2 stars (mult_S_1)
theorem mult_S_1 : ∀ n m : ℕ, m = nat.succ n → m * (1 + n) = m * m :=
begin
  introv h1,
  rw [nat.one_add, ←h1],
end

-- Exercise: 2 stars (andb_tt_elim2)
theorem andb_tt_elim2 : ∀ b c : bool, band b c = tt → c = tt :=
begin
  introv h1,
  cases b,
    cases c,
      contradiction,
      refl,
    cases c,
      contradiction,
      refl
end

-- Exercise: 1 star (zero_nbeq_plus_1)
theorem zero_nbeq_plus_1 : ∀ n : ℕ, beq_nat 0 (n + 1) = ff :=
by intro n; refl

-- Exercise: 2 stars, optional (decreasing)
meta def fail_factorial : ℕ → ℕ
| 0 := 1
| n := n * fail_factorial (n - 1)

-- Exercise: 2 stars (boolean_functions)
theorem identity_fn_applied_twice :
  ∀ f : bool → bool, (∀ x : bool, f x = x) → ∀ b : bool, f (f b) = b :=
begin
  intros f hx x,
  rw [hx, hx]
end

theorem negation_fn_applied_twice :
  ∀ f : bool → bool, (∀ x : bool, f x = bnot x) → ∀ b : bool, f (f b) = b :=
begin
  intros f hx x,
  rw [hx, hx],
  cases x,
    refl,
    refl
end

-- Exercise: 3 stars, optional (andb_eq_orb)
theorem andb_eq_orb (b c : bool) : band b c = bor b c → b = c :=
begin
  cases b,
    cases c,
      intros; refl,
      intros; contradiction,
    cases c,
      intros; contradiction,
      intros; refl
end

-- Exercise: 3 stars (binary)
inductive bin : Type
| zero : bin
| twice : bin → bin
| omtt : bin → bin

open bin
/-
  protected def add : nat → nat → nat
  | a  zero     := a
  | a  (succ b) := succ (add a b)
-/

def incr : bin → bin
| zero := omtt zero
| (twice b) := omtt b
| (omtt b) := twice (incr b)

def bin_to_nat : bin → ℕ
| zero := 0
| (twice n) := 2 * (bin_to_nat n)
| (omtt n) := 2 * (bin_to_nat n) + 1

instance : has_coe bin ℕ := ⟨bin_to_nat⟩
instance : has_repr bin := ⟨λ b, repr $ bin_to_nat b⟩
instance : has_zero bin := ⟨zero⟩
instance : has_one bin := ⟨omtt zero⟩

lemma test_bin_incr1 : incr zero = 1 := rfl
lemma test_bin_incr2 : incr (omtt zero) = twice (omtt zero) := rfl
lemma test_bin_incr3 : incr (twice zero) = 1 := rfl
lemma test_bin_incr4 :
  incr (omtt (twice $ omtt zero)) = twice (omtt (omtt zero)) := rfl

end basics
end hidden

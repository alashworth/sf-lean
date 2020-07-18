import tactic
import data.finmap
open tactic

namespace start
inductive aexp
| ANum (n : ℕ)
| APlus (a₁ a₂ : aexp)
| AMinus (a₁ a₂ : aexp)
| AMult (a₁ a₂ : aexp)
open aexp

inductive bexp
| BTrue
| BFalse
| BEq (a₁ a₂ : aexp)
| BLe (a₂ a₂ : aexp)
| BNot (b : bexp)
| BAnd (b₁ b₂ : bexp)
open bexp

def aeval : aexp → ℕ
| (ANum n) := n
| (APlus a₁ a₂) := aeval a₁ + aeval a₂
| (AMinus a₁ a₂) := aeval a₁ - aeval a₂
| (AMult a₁ a₂) := aeval a₁ * aeval a₂

example : aeval (APlus (ANum 2) (ANum 2)) = 4 := rfl

def beval : bexp → bool
| BTrue := true
| BFalse := false
| (BEq a₁ a₂) := aeval a₁ = aeval a₂
| (BLe a₁ a₂) := aeval a₁ ≤ aeval a₂
| (BNot b₁) := ¬beval b₁
| (BAnd b₁ b₂) := beval b₁ ∧ beval b₂

def optimize_zero_plus : aexp → aexp
| (ANum n) := ANum n
| (APlus (ANum 0) e₂) := optimize_zero_plus e₂
| (APlus e₁ e₂) := APlus (optimize_zero_plus e₁) (optimize_zero_plus e₂)
| (AMinus e₁ e₂) := AMinus (optimize_zero_plus e₁) (optimize_zero_plus e₂)
| (AMult e₁ e₂) := AMult (optimize_zero_plus e₁) (optimize_zero_plus e₂)

example : optimize_zero_plus (APlus (ANum 2)
                                    (APlus (ANum 0)
                                           (APlus (ANum 0) (ANum 1))))
        = APlus (ANum 2) (ANum 1) := rfl

theorem optimize_zero_plus_sound : ∀ a, aeval (optimize_zero_plus a) = aeval a :=
begin
    intros a, induction a;
    try { simp [optimize_zero_plus, aeval, a_ih_a₁, a_ih_a₂] <|> refl },
    rcases a_a₁ with ⟨_|n⟩;
    simp [optimize_zero_plus, a_ih_a₂, a_ih_a₁, aeval] at *; assumption
end


inductive aevalR : aexp → ℕ → Prop
| E_ANum {n} : aevalR (ANum n) n 
| E_APlus {e₁ e₂ n₁ n₂} : 
    aevalR e₁ n₁ → aevalR e₂ n₂ → aevalR (APlus e₁ e₂) (n₁ + n₂)
| E_AMinus {e₁ e₂ n₁ n₂} : 
    aevalR e₁ n₁ → aevalR e₂ n₂ → aevalR (AMinus e₁ e₂) (n₁ - n₂)
| E_AMult {e₁ e₂ n₁ n₂} : 
    aevalR e₁ n₁ → aevalR e₂ n₂ → aevalR (AMult e₁ e₂) (n₁ * n₂)

local notation e ` \\ ` n := aevalR e n 

theorem aeval_iff_aevalR : ∀ a n, (a \\ n) ↔ aeval a = n :=
begin
    intros, split, 
    { intro h, induction h; subst_vars; refl },
    revert n, induction a; intros; subst_vars; constructor; simp only [a_ih_a₁, a_ih_a₂],
end

end start

namespace extended_aexp
inductive aexp
| ANum (n : ℕ)
| AId (x : string)
| APlus (a₁ a₂ : aexp)
| AMinus (a₁ a₂ : aexp)
| AMult (a₁ a₂ : aexp)
open aexp

inductive bexp
| BTrue
| BFalse
| BEq (a1 a2 : aexp)
| BLe (a1 a2 : aexp)
| BNot (b : bexp)
| BAnd (b1 b2 : bexp)
open bexp

inductive com
| CSkip
| CAss (x : string) (a : aexp)
| CSeq (c₁ c₂ : com)
| CIf (b : bexp) (c₁ c₂ : com)
| CWhile (b : bexp) (c : com)
open com

local infixr `;; `:40 := CSeq
local infix ` ::= `:60 := CAss
local notation ` SKIP ` := CSkip
local notation ` WHILE ` b ` DO ` c ` END ` := CWhile b c
local notation ` TEST ` c₁ ` THEN ` c₂ ` ELSE ` c₃ ` FI ` := CIf c₁ c₂ c₃

def W := "W"
def X := "X"
def Y := "Y"
def Z := "Z"

instance has_coe_str_aexp : has_coe string aexp := ⟨AId⟩
instance has_coe_nat_aexp : has_coe ℕ aexp := ⟨ANum⟩
instance has_one_aexp : has_one aexp := ⟨ANum 1⟩
instance has_zero_aexp : has_zero aexp := ⟨ANum 0⟩
instance has_add_aexp : has_add aexp := ⟨APlus⟩
instance has_mul_aexp : has_mul aexp := ⟨AMult⟩
instance has_sub_aexp : has_sub aexp := ⟨AMinus⟩
local prefix `!` := BNot
local infix ` === `:50 := BEq

def fact_in_lean :=
    Z ::= X;;
    Z ::= 1;;
    WHILE !Z === 0 DO
        Y ::= Y * Z;;
        Z ::= Z - 1
    END


def program_state := finmap (λ (v:string), ℕ)

local notation x ` ↦ `:50 y `; `:1 m := finmap.insert x y m


lemma program_state_insert_eq (x) (v : ℕ) (s : program_state) : 
    (x ↦ v; s).lookup x = some v := by simp

lemma program_state_insert_neq (x₁ x₂) (v : ℕ) (s : program_state) (h : x₁ ≠ x₂) : 
    (x₁ ↦ v; s).lookup x₂ = s.lookup x₂ := finmap.lookup_insert_of_ne s h.symm

lemma program_state_shadow (x) (v₁ v₂ : ℕ) (s : program_state) :
    (x ↦ v₁; x ↦ v₂; s) = (x ↦ v₁; s) := by simp

lemma program_state_insert_same (x) (s : program_state) {v} (h : s.lookup x = some v) :
    (x ↦ v; s) = s := 
begin
    apply finmap.ext_lookup, intro y,
    cases dec_em (x = y) with hxy hnxy,
    { rw ←hxy, symmetry, simpa, },
    apply program_state_insert_neq, assumption,
end

lemma program_state_permute (x₁ x₂) (v₁ v₂ : ℕ) (s : program_state) (h : x₁ ≠ x₂) :
    (x₁ ↦ v₁; x₂ ↦ v₂; s) = (x₂ ↦ v₂; x₁ ↦ v₁; s) := finmap.insert_insert_of_ne s h.symm 

def aeval (st : program_state) : aexp → ℕ
| (ANum n) := n
| (AId x) := (st.lookup x).get_or_else 0
| (APlus a₁ a₂) := aeval a₁ + aeval a₂
| (AMinus a₁ a₂) := aeval a₁ - aeval a₂
| (AMult a₁ a₂) := aeval a₁ * aeval a₂

def beval (st : program_state) : bexp → bool 
| BTrue := true
| BFalse := false
| (BEq a₁ a₂) := aeval st a₁ = aeval st a₂
| (BLe a₁ a₂) := aeval st a₁ ≤ aeval st a₂
| (BNot b₁) := ¬(beval b₁)
| (BAnd b₁ b₂) := beval b₁ && beval b₂

inductive ceval : com → program_state → program_state → Prop
| E_Skip {st} : ceval SKIP st st
| E_Ass {st a₁ n x} : 
    aeval st a₁ = n → 
    ceval (x ::= a₁) st (x ↦ n; st)
| E_Seq {c₁ c₂ st st' st''} :
    ceval c₁ st st' →
    ceval c₂ st' st'' →
    ceval (c₁;; c₂) st st''
| E_IfTrue {st st' b c₁ c₂} :
    beval st b = true →
    ceval c₁ st st' →
    ceval TEST b THEN c₁ ELSE c₂ FI st st'
| E_IfFalse {st st' b c₁ c₂} :
    beval st b = false →
    ceval c₂ st st' →
    ceval TEST b THEN c₁ ELSE c₂ FI st st'
| E_WhileFalse {b st c} :
    beval st b = false →
    ceval WHILE b DO c END st st
| E_WhileTrue {st st' st'' b c} :
    beval st b = true →
    ceval c st st' →
    ceval WHILE b DO c END st' st'' →
    ceval WHILE b DO c END st st'' 

notation st ` =[ ` c ` ]=> ` st' := ceval c st st'

theorem ceval_deterministic {c st st₁ st₂} (h₁ : st =[ c ]=> st₁) (h₂ : st =[ c ]=> st₂) : st₁ = st₂ :=
begin
    intros, revert st₂, induction h₁; intros; cases h₂; subst_vars; try {solve_by_elim},
    { apply_assumption, specialize h₁_ih_a h₂_a, subst_vars, assumption },
    all_goals { rw h₁_a at h₂_a, injections },
    specialize h₁_ih_a h₂_a_1, subst_vars, repeat {apply_assumption}
end

end extended_aexp

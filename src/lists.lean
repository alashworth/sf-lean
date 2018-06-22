open list

-- Exercise: 1 star (snd_fst_is_swap)
def swap : ℕ × ℕ → ℕ × ℕ
| (a, b) := (b, a) 

lemma snd_fst_is_swap : ∀ p : ℕ × ℕ, (p.snd, p.fst) = swap p
| (a, b) := rfl 

-- Exercise: 1 star, optional (fst_swap_is_snd)
theorem fst_swap_is_snd : ∀ p : ℕ × ℕ, (swap p).fst = p.snd
| (a, b) := rfl

-- Exercise: 2 stars, recommended (list_funs)
def nonzeros : list ℕ → list ℕ
| nil := nil  
| (cons x xs) := if x ≠ 0 then [x] ++ nonzeros xs else nonzeros xs

lemma test_nonzeros : nonzeros [0, 1, 0, 2, 3, 0, 0] = [1, 2, 3] := rfl

def oddmembers : list ℕ → list ℕ
| nil := nil
| (cons x xs) := if nat.bodd x then [x] ++ oddmembers xs else oddmembers xs

lemma test_oddmembers : oddmembers [0, 1, 0, 2, 3, 0, 0] = [1, 3] := rfl

def countoddmembers (l : list ℕ) : ℕ := length (oddmembers l)

lemma test_countoddmembers1 : countoddmembers [1, 0, 3, 1, 4, 5] = 4 := rfl
lemma test_countoddmembers2 : countoddmembers [0, 2, 4] = 0 := rfl 
lemma test_countoddmembers3 : countoddmembers nil = 0 := rfl

-- Exercise: 3 stars, advanced (alternate)
def alternate : list ℕ → list ℕ → list ℕ 
| [] [] := []
| [] (y :: ys) := [y] ++ alternate [] ys
| (x :: xs) [] := [x] ++ alternate xs [] 
| (x :: xs) (y :: ys) := [x, y] ++ alternate xs ys

lemma test_alternate1 : alternate [1,2,3] [4,5,6] = [1,4,2,5,3,6] := rfl
lemma test_alternate2 : alternate [1] [4, 5, 6] = [1,4,5,6] := rfl
lemma test_alternate3 : alternate [1,2,3] [4] = [1,4,2,3] := rfl
lemma test_alternate4 : alternate [] [20,30] = [20, 30] := rfl

-- Exercise: 3 stars, recommended (bag_functions)
def bag : Type := list ℕ

def count : ℕ → bag → ℕ
| n [] := 0
| n (x::xs) := if x = n then 1 + count n xs else count n xs 

lemma test_count1 : count 1 [1,2,3,1,4,1] = 3 := rfl
lemma test_count2 : count 6 [1,2,3,1,4,1] = 0 := rfl

def bag.sum : bag → bag → bag := λ a b, @list.append ℕ a b

lemma test_sum1 : count 1 (bag.sum [1,2,3] [1,4,1]) = 3 := rfl

def bag.add : ℕ → bag → bag := λ a b, list.append b [a]

lemma test_add1 : count 1 (bag.add 1 [1,4,1]) = 3 := rfl
lemma test_add2 : count 5 (bag.add 1 [1,4,1]) = 0 := rfl 

def bag.mem : ℕ → bag → bool 
| n [] := ff
| n (x::xs) := if n = x then tt else bag.mem n xs

lemma test_mem1 : bag.mem 1 [1,4,1] = tt := rfl 
lemma test_mem2 : bag.mem 2 [1,4,1] = ff := rfl

-- Exercise: 3 stars, optional (bag_more_functions)
def remove_one : ℕ → bag → bag 
| n [] := [] 
| n (x::xs) := if n = x then xs else x :: (remove_one n xs)

lemma test_remove_one1 : count 5 (remove_one 5 [2,1,5,4,1]) = 0 := rfl
lemma test_remove_one2 : count 5 (remove_one 5 [2,1,4,1]) = 0 := rfl 
lemma test_remove_one3 : count 4 (remove_one 5 [2,1,4,5,1,4]) = 2 :=  rfl  
lemma test_remove_one4 : count 5 (remove_one 5 [2,1,5,4,5,1,4]) = 1 := rfl

def remove_all : ℕ → bag → bag
| n [] := []
| n (x::xs) := if n = x then remove_all n xs else x :: remove_all n xs

lemma test_remove_all1 : count 5 (remove_all 5 [2,1,5,4,1]) = 0 := rfl 
lemma test_remove_all2 : count 5 (remove_all 5 [2,1,4,1]) = 0 := rfl
lemma test_remove_all3 : count 4 (remove_all 5 [2,1,4,5,1,4]) = 2 := rfl 
lemma test_remove_all4 : 
  count 5 (remove_all 5 [2,1,5,4,5,1,4,5,1,4]) = 0 := rfl 

def bag.subset : bag → bag → bool
| [] [] := tt
| [] (y::ys) := tt 
| (x::xs) [] := ff
| (x::xs) y := if bag.mem x y then bag.subset xs (remove_one x y) else ff

lemma test_subset1 : bag.subset [1,2] [2,1,4,1] = tt := rfl   
lemma test_subset2 : bag.subset [1,2,2] [2,1,4,1] = ff := rfl 

-- Exercise: 4 stars, advanced (rev_injective)
def rev : list ℕ → list ℕ 
| nil := nil
| (x::xs) := (rev xs) ++ [x]

lemma test_rev1 : rev [3,2,1] = [1,2,3] := rfl
lemma test_rev2 : rev [] = [] := rfl 

lemma rev_step : ∀ (hd : ℕ) (tl : list ℕ), rev (hd :: tl) = rev tl ++ [hd] :=
by intros; refl

lemma rev_distrib : ∀ l1 l2 : list ℕ, rev (l1 ++ l2) = rev l2 ++ rev l1 := 
begin
  intros,
  induction l1 with x xs ihl1,
    induction l2 with y ys ihl2,
      refl,
      simp [rev],
    induction l2 with y ys ihl2,
      simp [rev],
      { simp [rev], 
        rw [ihl1, rev_step, ←cons_append],
        simp * }
end 

lemma rev_involutive : ∀ l : list ℕ, rev (rev l) = l
| nil := rfl
| (x::xs) := by simp [*, rev, rev_step, rev_distrib]

lemma rev_nil : rev nil = nil := rfl
lemma rev_singleton : ∀ n : ℕ, rev [n] = [n] := λ n, rfl 

lemma ceqa (hd : ℕ) (tl : list ℕ) : hd :: tl = [hd] ++ tl := rfl

theorem rev_injective : function.injective rev := 
λ a b h, by rw [←rev_involutive a, ←rev_involutive b, h]
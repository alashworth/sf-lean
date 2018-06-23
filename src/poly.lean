import data.list.basic
open list

-- Exercise: 2 stars (filter_even_gt7)
lemma test_filter1 : filter (λ a, ¬nat.bodd a) [1,2,3,4] = [2,4] := rfl

def filter_even_gt7 (l : list ℕ) : list ℕ :=
filter (λ a : ℕ, ¬nat.bodd a ∧ a ≥ 7) l

lemma test_filter_even_gt7_1 :
  filter_even_gt7 [1,2,6,9,10,3,12,8] = [10,12,8] := rfl
lemma test_filter_even_gt7_2 :
  filter_even_gt7 [5,2,6,19,129] = [] := rfl

-- Exercise: 3 stars (partition)
def partition {α : Type} (test : α → bool) (l : list α) : list α × list α :=
let a := filter (λ z, test z) l, b := filter (λ z, ¬ test z) l in ⟨a, b⟩

lemma test_partition1 : partition nat.bodd [1,2,3,4,5] = ⟨[1,3,5], [2,4]⟩ :=
rfl
lemma test_partition2 : partition (λ x, ff) [5,9,0] = ⟨[], [5,9,0]⟩ := rfl

lemma t1 {α : Type} (head : α) (tail : list α)
  : cons head tail = append [head] tail := rfl

-- Exercise: 3 stars (map_rev)
theorem map_reverse_commutes {α β : Type} (f : α → β) (l : list α)
  : map f (reverse l) = reverse (map f l) :=
list.rec_on l (rfl)
  (λ head tail ih,
    begin
      rw reverse_cons,
      rw map_append,
      rw ih,
      rw map_cons,
      rw map_cons,
      rw reverse_cons,
      rw map,
    end)

-- Exercise: 2 stars, recommended (flat_map)
def flat_map {α β : Type} (f : α → list β) : list α → list β
| nil := []
| (hd::tl) := f hd ++ flat_map tl

lemma test_flat_map1 : flat_map (λn, [n,n,n]) [1,5,4] = [1,1,1,5,5,5,4,4,4] :=
rfl

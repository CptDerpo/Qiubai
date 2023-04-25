import data.vector tactic

def bool_to_nat : bool → ℕ 
  | tt := 1
  | ff := 0

def nat_to_bool : ℕ → bool
  | nat.zero := ff
  | (nat.succ _) := tt

def bool_list_to_nat : list bool → ℕ
  | [] := 0
  | (b :: bools) := if b then 2^(list.length bools) + bool_list_to_nat bools
                    else bool_list_to_nat bools

def bool_vec_to_nat {n : ℕ} (v : vector bool n) : ℕ :=
  bool_list_to_nat (list.of_fn v.nth)

def bool_arr_to_nat {n : ℕ} (v : array n bool) : ℕ :=
  bool_list_to_nat (array.to_list v)

def get_nth_bool : list bool -> ℕ -> bool
  | [] n := ff
  | (h::t) 0 := h
  | (h::t) (n+1) := get_nth_bool t n

def get_first_half {α : Type*} : list α → list α --Type* is Type 0, smallest universe, non dependent types
  | [] := []
  | [a] := [a]
  | lst := list.take (lst.length / 2) lst

def get_second_half {α : Type*} : list α → list α
  | [] := []
  | [a] := [a]
  | lst := list.drop (lst.length / 2) lst

#eval get_first_half [tt, tt, ff, tt, ff, tt, ff]
#eval get_second_half [tt, tt, ff, tt, ff, tt, ff]
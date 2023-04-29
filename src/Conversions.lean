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

def bool_arr_to_nat {n : ℕ} (v : array n bool) : ℕ :=
  bool_list_to_nat (array.to_list v)

def zip_array {n : ℕ} {α β : Type} (a : array n α) (b : array n β) : array n (α × β) :=
  ⟨λ i, (a.read i, b.read i)⟩

#eval zip_array ([tt, tt, tt].to_array) ([ff, ff, ff].to_array)
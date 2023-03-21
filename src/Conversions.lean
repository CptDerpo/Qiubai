import data.vector tactic

def bool_list_to_nat : list bool → ℕ
  | [] := 0
  | (b :: bools) := if b then 2^(list.length bools) + bool_list_to_nat bools
                    else bool_list_to_nat bools

def bool_vec_to_nat {n : ℕ} (v : vector bool n) : ℕ :=
  bool_list_to_nat (list.of_fn v.nth)

import data.vector tactic Gates

def bool_to_nat : bool → ℕ 
  | tt := 1
  | ff := 0
--bewijs
def nat_to_bool : ℕ → bool
  | nat.zero := ff
  | (nat.succ _) := tt

def bool_arr_to_nat {n : ℕ} (v : array n bool) : ℕ :=
  let acc := 0 in
  v.foldl acc (λ b acc, cond b (2 * acc + 1) (2 * acc + 0))

def zip_array {n : ℕ} {α β : Type} (a : array n α) (b : array n β) : array n (α × β) :=
  ⟨λ i, (a.read i, b.read i)⟩

def unzip_array {n : ℕ} {α β : Type} (a : array n (α × β)) : (array n α × array n β) :=
 (⟨λ i, (a.read i).fst⟩, ⟨λ i, (a.read i).snd⟩)

def fold_array_aux {n : ℕ} {α β γ δ: Type} (f : α → β → γ → (δ × γ)) (a : array n (α × β)) : 
                    Π (i : ℕ), i ≤ n → (array n δ × γ) → (array n δ × γ)
| nat.zero     h acc := acc
| (nat.succ j) h acc :=
  let i : fin n := ⟨j, h⟩,
    (sum, cout) := f (a.read i).fst (a.read i).snd acc.snd in
    fold_array_aux j (le_of_lt h) (acc.fst.write i sum, cout)

def fold_array {n : ℕ} {α β γ δ : Type} (f : α → β → γ → (δ × γ)) (a : array n (α × β)) (i : array n δ × γ) : (array n δ × γ) :=
  let acc := i in
  fold_array_aux f a n (le_refl _) acc

def fold_lsh_aux {n : ℕ} {α β γ: Type} (f : α → β → (γ × β)) (a : array n α) : 
                    Π (i : ℕ), i ≤ n → (array n γ × β) → (array n γ × β) 
| nat.zero     h acc := acc
| (nat.succ j) h acc :=
  let i : fin n := ⟨j, h⟩,
    (res, next) := f (a.read i) acc.snd in
    fold_lsh_aux j (le_of_lt h) (acc.fst.write i res, next)

def fold_lsh {n : ℕ} {α β γ : Type} (f : α → β → (γ × β)) (a : array n α) 
								(i : array n γ × β) : (array n γ) :=
  let acc := i in
  (fold_lsh_aux f a n (le_refl _) acc).fst


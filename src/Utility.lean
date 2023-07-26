import data.vector tactic Gates

def stream (α : Type) := ℕ → α

def signal := ℕ → bool

def sig_n (n : ℕ) := ℕ → array n bool

def sig_n_zero (n : ℕ) : sig_n n := λ t, mk_array n ff

def sig_tt : signal := λ t, tt
def sig_ff : signal := λ t, ff

def bool_to_nat : bool → ℕ 
  | tt := 1
  | ff := 0

def nat_to_bool : ℕ → bool
  | nat.zero := ff
  | (nat.succ _) := tt

def bool_arr_to_nat {n : ℕ} (v : array n bool) : ℕ :=
  let acc := 0 in
  v.foldl acc (λ b acc, nat.bit b acc)

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


lemma zip_unzip_eq {n : ℕ} {α β : Type} (a : array n α) (b : array n β) :
  unzip_array (zip_array a b) = (a, b) :=
  begin
    unfold zip_array unzip_array,
    simp,
    split,
    {
      apply array.ext,
      intros i,
      apply array.read_map,
    },
    {
      apply array.ext,
      intros i,
      apply array.read_map,
    }
  end

lemma unzip_zip_eq {n : ℕ} {α β : Type} (a : array n (α × β)) :
  zip_array (unzip_array a).fst (unzip_array a).snd = a :=
  begin
    unfold zip_array unzip_array,
    simp,
    apply array.ext,
    intros i,
    exact prod.ext rfl rfl,
  end


def nat_to_bool_list (n : ℕ) : list bool :=
n.binary_rec [] (λ b n l, (b :: l))

def nat_to_bool_list_rev : ℕ → list bool
| 0 := [ff]
| n := list.reverse (nat_to_bool_list n)

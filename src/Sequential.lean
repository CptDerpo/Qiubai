import Gates tactic Conversions

def stream (α : Type) := ℕ → α

def signal := ℕ → bool

def sig_n (n : ℕ) := ℕ → array n bool

def mem_imp (I: bool) (D S: signal) : signal
| nat.zero := I
| (nat.succ y) := if S y = tt then D y 
                  else mem_imp y

def mem_spec (D S M: signal): Prop :=
  ∀ t : ℕ,
    (S t = tt → M (nat.succ t) = D t) ∧ --frame 1 D S M+1
    (S t = ff → M (nat.succ t) = M t) --frame 2 S M M+1

def n_mem_imp {n : ℕ} (I : array n bool) (D : sig_n n) (S : signal) : sig_n n
  | nat.zero := I
  | (nat.succ y) := if S y = tt then D y
                    else n_mem_imp y

def n_mem_spec {n : ℕ} (D : sig_n n) (S : signal) (M: sig_n n): Prop :=
  ∀ t : ℕ,
    (S t = tt → M (nat.succ t) = D t) ∧  --frame 1 D S M+1
    (S t = ff → M (nat.succ t) = M t) --frame 2 S M M+1

def ncounter_spec {n : ℕ} (out : sig_n n) (res : signal) : Prop :=
  ∀ t : ℕ, 
  if res t = tt 
  then bool_arr_to_nat(out (t+1)) = 0
  else bool_arr_to_nat(out (t+1)) = (bool_arr_to_nat(out t) + 1) % 2^(n)

import Gates tactic Conversions Combinational

def stream (α : Type) := ℕ → α

def signal := ℕ → bool

def sig_n (n : ℕ) := ℕ → array n bool

def sig_n_zero (n : ℕ) : sig_n n := λ t, mk_array n ff

def sig_tt : signal := λ t, tt

def mem_imp (I: bool) (D S: signal) : signal
| nat.zero := I
| (nat.succ y) := if S y = tt then D y 
                  else mem_imp y


def mem_spec {α : Type} (D : ℕ → α) (S : signal) (M : ℕ → α) : Prop :=
  ∀ t : ℕ,
    (S t = tt → M (nat.succ t) = D t) ∧  --frame 1 D S M+1
    (S t = ff → M (nat.succ t) = M t) --frame 2 S M M+1  


def n_mem_imp {n : ℕ} (I : array n bool) (D : sig_n n) (S : signal) : sig_n n
  | nat.zero := I
  | (nat.succ y) := if S y = tt then D y
                    else n_mem_imp y

def n_mem_spec {n : ℕ} (D : sig_n n) (S : signal) (M : sig_n n): Prop :=
  ∀ t : ℕ,
    (S t = tt → M (nat.succ t) = D t) ∧  --frame 1 D S M+1
    (S t = ff → M (nat.succ t) = M t) --frame 2 S M M+1


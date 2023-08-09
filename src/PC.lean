import Utility Adder

def pc_spec {n : ℕ} (R : signal) (O : sig_n n) : Prop :=
  ∀ t : ℕ,
    (R t = tt → O (nat.succ t) = mk_array n ff) ∧
    (R t = ff → O (nat.succ t) = (full_n_adder_imp (O t) (mk_array n ff) tt).fst)

def pc_imp {n : ℕ} (I : array n bool) (R : signal) : sig_n n
  | nat.zero := I
  | (nat.succ y) := if R y = tt then mk_array n ff
                    else (full_n_adder_imp (pc_imp y) (mk_array n ff) (tt)).fst

theorem pc_correct {n : ℕ} : ∀ (R : signal) (I : array n bool),
  pc_spec R (pc_imp (I) R) :=
  begin
    intros,
    unfold pc_spec,
    intros t,
    split,
    {
      intros h₁,
      unfold pc_imp,
      rw if_pos,
      exact h₁,
    },
    {
      intros h₁,
      unfold pc_imp,
      rw if_neg,
      simp,
      exact h₁, 
    }
  end
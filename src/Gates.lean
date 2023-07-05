import tactic

def AND_spec (A : list bool) (out : bool) : Prop :=
  out = (∀ (a ∈ A), a = tt)

def AND : list bool → bool
  | [] := tt
  | (h::t) := h ∧ AND t

def OR_spec (A : list bool) (out : bool) : Prop :=
  out = (∃ (a ∈ A), a = tt)

def OR : list bool → bool
  | [] := ff
  | (h::t) := h ∨ OR t

def XOR : list bool → bool
  | [] := ff
  | [b] := b
  | (h1::h2::t) := XOR ((h1 ≠ h2) :: t)

def count_tt : list bool → ℕ
  | [] := 0
  | (h::t) := (if h = tt then 1 else 0) + count_tt t

def XOR_spec (A : list bool) (out : bool) : Prop :=
  out = (count_tt A = 1)

lemma XOR (tt :: tl_tl) = out ↔ out = to_bool (count_tt tl_tl = 0)

theorem XOR_correct : ∀ (A : list bool), ∀ (out : bool),
  XOR A = out ↔ XOR_spec A out:=
begin
  intros A out,
  destruct A,
  {
    intros h,
    unfold XOR XOR_spec,
    rw h,
    unfold count_tt XOR,
    simp,
    rw eq_comm,
  },
  {
    intros,
    induction tl generalizing A hd,
    {
      sorry,
    },
    {
      unfold XOR XOR_spec,
      rw a,
      unfold XOR count_tt,
      simp,
      cases hd; cases tl_hd,
      {
        sorry,
      },
      {
        simp,
      }
    }

    }
  }
end

def NOT_spec (A : bool) (out : bool) : Prop :=
  out = ¬A

def NOT : bool → bool
  | tt := ff
  | ff := tt

theorem OR_correct : ∀ (A : list bool), ∀ (out : bool),
  OR A = out ↔ OR_spec A out:=
begin
  intros A out,
  induction A,
  { --base case
    unfold OR OR_spec,
    simp,
    rw eq_comm,
  },
  { --inductive case
    cases A_hd; cases A_tl; finish [OR, OR_spec],
  }
end

lemma AND_correct : ∀ (A : list bool), ∀ (out : bool),
  AND A = out ↔ AND_spec A out :=
begin
  intros A out,
  
  induction A,
  { --base case
    unfold AND AND_spec,
    simp,
    rw eq_comm,
  },
  { --inductive case
    cases A_hd; cases A_tl; finish [AND, AND_spec],
  }
end

lemma NOT_correct : ∀ (A : bool), ∀ (out : bool),
  NOT A = out ↔ NOT_spec A out :=
begin
  intros A out,
  cases A; unfold NOT NOT_spec; simp; rw eq_comm,
end
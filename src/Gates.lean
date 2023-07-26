import tactic

--NOT
def NOT_spec (A : bool) (OUT : bool) : Prop :=
  OUT = ¬A

theorem NOT_unique : ∀ (A : bool), ∃! (OUT : bool),
  NOT_spec A OUT :=
  begin
    intros A,
    apply exists_unique_of_exists_of_unique,
    {
      exact exists_eq,
    },
    {
      intros y₁ y₂,
      unfold NOT_spec,
      intros h₁ h₂,
      rw ←h₂ at h₁,
      exact h₁,
    }
  end

def NOT : bool → bool
  | tt := ff
  | ff := tt

theorem NOT_correct : ∀ (A : bool), ∀ (OUT : bool),
  NOT A = OUT ↔ NOT_spec A OUT :=
  begin
    intros A OUT,
    cases A; unfold NOT NOT_spec; tautology,
  end

--OR
def OR_spec (A : list bool) (OUT : bool) : Prop :=
  OUT = (∃ (a ∈ A), a = tt)

theorem OR_unique : ∀ (A : list bool), ∃! (OUT : bool),
  OR_spec A OUT :=
  begin
    intros A,
    apply exists_unique_of_exists_of_unique,
    {
      tauto,
    },
    {
      intros y₁ y₂,
      unfold OR_spec,
      intros h₁ h₂,
      rw ←h₂ at h₁,
      exact h₁,
    }
  end

def OR : list bool → bool
  | [] := ff
  | (h::t) := h ∨ OR t

theorem OR_correct : ∀ (A : list bool), ∀ (OUT : bool),
  OR A = OUT ↔ OR_spec A OUT:=
  begin
    intros A OUT,
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

--AND
def AND_spec (A : list bool) (OUT : bool) : Prop :=
  OUT = (∀ (a ∈ A), a = tt)

def AND_unique : ∀ (A : list bool), ∃! (OUT : bool), 
  AND_spec A OUT :=
  begin
    intros A,
    apply exists_unique_of_exists_of_unique,
    {
      tauto,
    },
    {
      intros y₁ y₂,
      unfold AND_spec,
      intros h₁ h₂,
      rw ←h₂ at h₁,
      exact h₁,
    }
  end

def AND : list bool → bool
  | [] := tt
  | (h::t) := h ∧ AND t

theorem AND_correct : ∀ (A : list bool), ∀ (OUT : bool),
  AND A = OUT ↔ AND_spec A OUT :=
  begin
    intros A OUT,
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


--XOR
def count_tt : list bool → ℕ
  | [] := 0
  | (h::t) := (if h = tt then 1 else 0) + count_tt t

def XOR_spec (A : list bool) (OUT : bool) : Prop :=
  OUT = ((count_tt A) % 2 = 1)

theorem XOR_unique : ∀ (A : list bool), ∃! (OUT : bool),
  XOR_spec A OUT :=
  begin
    intros A,
    apply exists_unique_of_exists_of_unique,
    {
      exact exists_eq,
    },
    {
      intros y₁ y₂,
      unfold XOR_spec,
      intros h₁ h₂,
      rw ←h₂ at h₁,
      exact h₁,
    }
  end

def XOR : list bool → bool
  | [] := ff
  | [b] := b
  | (h1::h2::t) := XOR((h1 ≠ h2) :: t)

theorem XOR_correct : ∀ (A : list bool), ∀ (OUT : bool),
  XOR A = OUT ↔ XOR_spec A OUT:=
  begin
    intros A OUT,
    destruct A,
    {
      intros h,
      unfold XOR XOR_spec,
      rw h,
      unfold count_tt XOR,
      simp,
      exact eq_comm,
    },
    {
      intros,
      induction tl generalizing A hd,
      {
        rw a,
        cases hd;
        {
          unfold XOR XOR_spec count_tt,
          simp,
          rw eq_comm,
        }
      },
      {
        rw a,
        unfold XOR count_tt,
        cases hd; cases tl_hd;
        {
          simp at *,
          unfold XOR_spec count_tt at *,
          simp at *,
          try {ring_nf, simp},
          tautology,
        }
      }
    }
  end
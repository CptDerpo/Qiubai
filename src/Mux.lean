import Gates Tactic Utility

def mux_spec {α : Type} (IN0 IN1 : α) (SEL : bool) (OUT : α) : Prop :=
	if SEL then (OUT = IN1) else (OUT = IN0) 

theorem mux_unique : ∀ (IN0 IN1 SEL: bool),
  ∃! (out : bool), mux_spec IN0 IN1 SEL out :=
  begin
    intros IN0 IN1 SEL,
    apply exists_unique_of_exists_of_unique,
    { --existence of output
      cases SEL; exact exists_eq,
    },
    { --uniqueness of output
      intros y₁ y₂,
      cases SEL;
      {
        unfold mux_spec,
        simp,
        intros h₁ h₂,
        rw ←h₂ at h₁,
        exact h₁,
      }
    }
  end

def mux_imp (IN0 IN1 sel : bool) : bool :=
	let p := NOT sel,
			q := AND [IN0, p],
			r := AND [IN1, sel] in
	(OR [q, r])

def mux_n_imp {n : ℕ} (IN0 IN1 : array n bool) (sel : bool) : array n bool :=
  (zip_array IN0 IN1).map (λ x, mux_imp x.fst x.snd sel)
theorem mux_correct : ∀ (IN0 IN1 SEL: bool),
  ∀ (OUT : bool), mux_spec IN0 IN1 SEL OUT ↔ (mux_imp IN0 IN1 SEL) = OUT :=
  begin
    intros IN0 IN1 SEL out,
    cases SEL;
    {
      unfold mux_spec mux_imp,
      simp,
      unfold AND OR NOT,
      simp,
      rw eq_comm,
    },
  end

theorem mux_n_correct {n : ℕ} : ∀ (IN0 IN1 : array n bool) (SEL : bool),
	∀ (OUT : array n bool), mux_spec IN0 IN1 SEL OUT ↔ (mux_n_imp IN0 IN1 SEL) = OUT :=
  begin
    intros IN0 IN1 SEL OUT,
    cases SEL;
    {
      split;
      {
        unfold mux_n_imp mux_spec mux_imp zip_array,
        simp,
        unfold OR AND NOT,
        simp,
        intros h₁,
        apply array.ext,
        intros i,
        rw ←h₁,
        apply array.read_map,
      }
    }
  end

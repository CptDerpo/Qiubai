import Gates tactic

def dec_imp (in0 in1 out0 out1 out2 out3 : bool) : Prop :=
	∃ (p q : bool), (not_ in0 p) ∧ (not_ in1 q) ∧ (and_n [p, q] out0) ∧ 
		(and_n [in0, q] out1) ∧ (and_n [p, in1] out2) ∧ (and_n [in0, in1] out3)

def dec_spec (in0 in1 out0 out1 out2 out3 : bool) : Prop :=
	if ¬in1 ∧ ¬in0 then (out3 = ff ∧ out2 = ff ∧ out1 = ff ∧ out0 = tt)
	else if ¬in1 ∧ in0 then (out3 = ff ∧ out2 = ff ∧ out1 = tt ∧ out0 = ff)
	else if in1 ∧ ¬in0 then (out3 = ff ∧ out2 = tt ∧ out1 = ff ∧ out0 = ff)
	else (out3 = tt ∧ out2 = ff ∧ out1 = ff ∧ out0 = ff)

theorem dec_correct : ∀ in0 in1 out0 out1 out2 out3, 
			dec_imp in0 in1 out0 out1 out2 out3 ↔ dec_spec in0 in1 out0 out1 out2 out3 :=
begin
  intros in0 in1 out0 out1 out2 out3,
  unfold dec_imp dec_spec not_ and_n AND,
  simp,
  split,
  {
    cases in0; cases in1; simp *,
    {
      intros a b c d,
      cases a; cases b; cases c; cases d; simp,
    },
    {
      intros a b c d,
      cases a; cases b; cases c; cases d; simp,
    },
    {
      intros a b c d,
      cases a; cases b; cases c; cases d; simp,
    },
    {
      intros a b c d,
      cases a; cases b; cases c; cases d; simp,
    }
  },
  {
    cases in0; cases in1; simp *,
    {
      intros a b c d,
      cases a; cases b; cases c; cases d; simp,
    },
    {
      intros a b c d,
      cases a; cases b; cases c; cases d; simp,
    },
    {
      intros a b c d,
      cases a; cases b; cases c; cases d; simp,
    },
    {
      intros a b c d,
      cases a; cases b; cases c; cases d; simp,
    }
  }
end
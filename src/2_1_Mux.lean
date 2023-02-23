import Gates tactic

def mux_imp (in1 in2 sel out : bool) : Prop :=
	∃ (p q r : bool), (nand_n [in1, p] q) ∧ (nand_n [sel, in2] r) ∧ 
		(nand_n [q, r] out) ∧ (not_ sel p)

def mux_spec (in1 in2 sel out : bool) : Prop :=
	if sel then (out = in2) else (out = in1) 

theorem mux_correct : ∀ in1 in2 sel out, mux_imp in1 in2 sel out ↔ mux_spec in1 in2 sel out :=
begin
  intros in1 in2 sel out,
  unfold mux_imp mux_spec nand_n AND not_,
  split,
  {
    cases sel; simp,
    { --sel FF
      cases in1; simp,
    },
    { --sel TT
      cases in2; simp,
    }
  },
  {
    cases sel; simp,
    { -- sel FF
      cases in1; simp,
    },
    { -- sel TT
      cases in2; simp,
    }
  }
end
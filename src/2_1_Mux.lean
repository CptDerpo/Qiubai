import Gates

def mux_imp (in1 in2 sel out : bool) : Prop :=
	∃ (p q r : bool), (nand_n [in1, p] q) ∧ (nand_n [sel, in2] r) ∧ 
		(nand_n [q, r] out) ∧ (not_ sel p)

def mux_spec (in1 in2 sel out : bool) : Prop :=
	if sel then (out = in2) else (out = in1) 


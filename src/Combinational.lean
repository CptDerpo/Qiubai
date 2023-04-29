import Gates tactic Conversions data.vector data.real.basic Sequential

--2to1 mux with 1 bit input
def mux_imp (in1 in2 sel : bool) : bool :=
	∃ (p q r out : bool), (nand_n [in1, p] q) ∧ (nand_n [sel, in2] r) ∧ 
		(nand_n [q, r] out) ∧ (not_ sel p) ∧ out

def mux_spec (in1 in2 sel out : bool) : Prop :=
	if sel then (out = in2) else (out = in1) 

--2to1 mux with n-bit inputs
def mux_n_imp {n : ℕ} (in1 in2 : array n bool) (sel : bool) : array n bool :=
  (zip_array in1 in2).map (λ x, mux_imp x.fst x.snd sel)

def mux_n_spec {n : ℕ} (in1 in2 : array n bool) (sel : bool) (out : array n bool) : Prop :=
	if sel then (out = in2) else (out = in1)

--2to4 decoder
def dec_imp (in0 in1 out0 out1 out2 out3 : bool) : Prop :=
	∃ (p q : bool), (not_ in0 p) ∧ (not_ in1 q) ∧ (and_n [p, q] out0) ∧ 
		(and_n [in0, q] out1) ∧ (and_n [p, in1] out2) ∧ (and_n [in0, in1] out3)

def dec_spec (in0 in1 out0 out1 out2 out3 : bool) : Prop :=
	if ¬in1 ∧ ¬in0 then (out3 = ff ∧ out2 = ff ∧ out1 = ff ∧ out0 = tt)
	else if ¬in1 ∧ in0 then (out3 = ff ∧ out2 = ff ∧ out1 = tt ∧ out0 = ff)
	else if in1 ∧ ¬in0 then (out3 = ff ∧ out2 = tt ∧ out1 = ff ∧ out0 = ff)
	else (out3 = tt ∧ out2 = ff ∧ out1 = ff ∧ out0 = ff)

--full-adder
def full_adder_imp (A B Cin : bool) (Sum Cout : bool) : Prop :=
	∃ (p q r : bool), (xor_n [A, B] p) ∧ (xor_n [p, Cin] Sum) ∧ (and_n [Cin, p] q) ∧ (and_n [A, B] r)
		∧ (or_n [q, r] Cout)

def full_adder_spec (A B Cin : bool) (Sum Cout : bool) : Prop :=
	Sum = nat_to_bool ((bool_to_nat A + bool_to_nat B + bool_to_nat Cin) % 2) ∧ 
	Cout = ((bool_to_nat A + bool_to_nat B + bool_to_nat Cin) ≥ 2)

--adder with n-bit inputs
def adder_n_imp {n : ℕ} (A B : array n bool) (Sum : array n bool) (Cout : bool) : Prop :=
	 
	
def adder_n_spec {n : ℕ} (A B : array n bool) (Sum : array n bool) (Cout : bool) : Prop :=



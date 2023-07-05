import Gates tactic Conversions data.vector data.real.basic

--2to1 mux with 1 bit input
def mux_imp (in1 in2 sel : bool) : bool :=
	let p := NOT sel,
			q := AND [in1, p],
			r := AND [in2, sel] in
	(OR [q, r])

def mux_spec {α : Type} (IN0 IN1 : α) (SEL : bool) (OUT : α) : Prop :=
	if SEL then (OUT = IN1) else (OUT = IN0) 

--2to1 mux with n-bit inputs
def mux_n_imp {n : ℕ} (in1 in2 : array n bool) (sel : bool) : array n bool :=
  (zip_array in1 in2).map (λ x, mux_imp x.fst x.snd sel)

def full_adder_imp (A B Cin : bool) : (bool × bool) :=
	let p := XOR [A, B],
			q := AND [Cin, p],
			r := AND [A, B] in
	(XOR [p, Cin], OR [q, r])

def full_adder_spec (A B Cin Sum Cout : bool) : Prop :=
	Sum = nat_to_bool ((bool_to_nat A + bool_to_nat B + bool_to_nat Cin) % 2) ∧ --sum
	Cout = ((bool_to_nat A + bool_to_nat B + bool_to_nat Cin) ≥ 2) --carry out

def full_n_adder_imp {n : ℕ} (A B : array n bool) (Cin : bool) : (array n bool × bool) :=
	fold_array (full_adder_imp) (zip_array A B) (mk_array n ff, Cin)


def full_n_adder_spec {n : ℕ} (A B : array n bool) (Cin : bool) (Sum : array n bool) (Cout : bool) : Prop :=
	bool_arr_to_nat Sum = (bool_arr_to_nat A + bool_arr_to_nat B + bool_to_nat Cin) % 2^n ∧
	Cout = ((bool_arr_to_nat A + bool_arr_to_nat B + bool_to_nat Cin) ≥ 2^n)

def lsh_elementary (In I : bool) : (bool × bool) :=
	let p := AND[I, tt],
			q := AND[In, ff] in
	(OR[p, q], In)

def lsh_imp {n : ℕ} (A : array n bool) : array n bool :=
	fold_lsh (lsh_elementary) A (mk_array n ff, ff)

def lsh_spec {n : ℕ} (A out : array n bool) : Prop :=
  bool_arr_to_nat out = (bool_arr_to_nat A * 2) % (2^n)

def ALU_lsh_imp {n : ℕ} (A : array n bool) : array n bool :=
  ⟨λ i, if h : i.val + 1 < n then A.read ⟨i.val + 1, h⟩ else ff⟩

--right shift
def ALU_rsh_imp {n : ℕ} (A : array n bool) : array n bool :=
	⟨λ i, if h : i.val > 0 ∧ i.val - 1 < n then A.read ⟨i.val - 1, h.right⟩ else ff⟩

def ALU_rsh_spec {n : ℕ} (A out : array n bool) : Prop :=
  bool_arr_to_nat out = (bool_arr_to_nat A) / 2
	


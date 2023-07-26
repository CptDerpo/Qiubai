import Utility

def full_adder_spec (A B Cin Sum Cout : bool) : Prop :=
	Sum = nat_to_bool ((bool_to_nat A + bool_to_nat B + bool_to_nat Cin) % 2) ∧ --sum
	Cout = ((bool_to_nat A + bool_to_nat B + bool_to_nat Cin) ≥ 2) --carry out

theorem full_adder_unique : ∀ (A B CIN : bool), ∃!(SUM : bool), ∃(COUT : bool),
  full_adder_spec A B CIN SUM COUT :=
  begin
    intros A B CIN,
    apply exists_unique_of_exists_of_unique,
    {
      unfold full_adder_spec,
      simp,
      cases A; cases B; cases CIN;
      {
        unfold bool_to_nat nat_to_bool,
        simp,
        unfold nat_to_bool,
        simp,
      }
    },
    {
      intros y₁ y₂,
      unfold full_adder_spec,
      simp,
      intros h₁ h₂,
      finish,
    }
  end

--returns (sum x cout)
def full_adder_imp (A B Cin : bool) : (bool × bool) :=
	let p := XOR [A, B],
			q := AND [Cin, p],
			r := AND [A, B] in
	(XOR [p, Cin], OR [q, r])


theorem full_adder_correct : ∀ (A B CIN : bool), ∀ (SUM COUT : bool), 
  full_adder_spec A B CIN SUM COUT ↔ full_adder_imp A B CIN = (SUM, COUT) :=
  begin
    intros,
    unfold full_adder_imp full_adder_spec,
    simp,
    cases A; cases B; cases CIN;
    {
      unfold bool_to_nat AND OR XOR,
      simp,
      unfold nat_to_bool,
      tautology,
    }
  end 

def full_n_adder_imp {n : ℕ} (A B : array n bool) (Cin : bool) : (array n bool × bool) :=
		fold_array (full_adder_imp) (zip_array A B) (mk_array n ff, Cin)

def full_n_adder_spec {n : ℕ} (A B : array n bool) (Cin : bool) (Sum : array n bool) (Cout : bool) : Prop :=
		bool_arr_to_nat Sum = ((bool_arr_to_nat A + bool_arr_to_nat B + bool_to_nat Cin) % 2^n) ∧
		Cout = ((bool_arr_to_nat A + bool_arr_to_nat B + bool_to_nat Cin) ≥ 2^n)

theorem full_n_adder_unique {n : ℕ} : ∀ (A B SUM : array n bool)(CIN : bool), ∃!(SUM : array n bool), ∃(COUT : bool),
  full_n_adder_spec A B CIN SUM COUT :=
  begin
    intros A B SUM CIN,
    apply exists_unique_of_exists_of_unique,
    {
      unfold full_n_adder_spec,
      simp,
      unfold bool_arr_to_nat,
      simp,
      sorry,
    },
    {
      intros y₁ y₂,
      unfold full_n_adder_spec,
      simp,
      intros h₁ h₂,
      finish,
    }
  end





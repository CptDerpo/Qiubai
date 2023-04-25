import Sequential Combinational

lemma mem_imp_complies_to_spec (D S: signal) :
  mem_spec D S (mem_imp ff D S) :=
  begin
    unfold mem_spec,
    intro t,
    split,
    {
      intros h,
      unfold mem_imp,
      simp,
      intro h',
      exfalso,
      rewrite h at h',
      simp at h',
      assumption,
    },
    {
      intros h,
      unfold mem_imp,
      simp,
      intro h',
      exfalso,
      rewrite h at h',
      simp at h',
      assumption,
    }
  end

lemma n_mem_imp_complies_to_spec {n : ℕ} (D : sig_n n) (S: signal):
  n_mem_spec D S (n_mem_imp (mk_array n ff) D S) :=
  begin
    unfold n_mem_spec,
    intros t,
    split,
    {
      intros h,
      unfold n_mem_imp,
      simp, --rewrite if_pos,
      intro h', -- exact h, (completed)
      exfalso,
      rewrite h at h',
      simp at h',
      assumption,
    },
    {
      intros h,
      unfold n_mem_imp,
      simp,
      intro h',
      exfalso,
      rewrite h at h',
      simp at h',
      assumption,
    }
  end

lemma mux_correct : ∀ in1 in2 sel out, mux_imp in1 in2 sel out ↔ mux_spec in1 in2 sel out :=
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
      {
        cases in1; simp,
      },
      { 
        cases in2; simp,
      }
    }
  end

lemma mux_n_correct {n : ℕ} (in1 in2 : array n bool) (sel : bool) (out : array n bool) :
	mux_n_imp in1 in2 sel out ↔ mux_n_spec in1 in2 sel out :=
  begin
    unfold mux_n_imp mux_n_spec,
    rw forall_congr,
    intros a,
    apply mux_correct,
  end

lemma dec_correct : ∀ in0 in1 out0 out1 out2 out3, 
			dec_imp in0 in1 out0 out1 out2 out3 ↔ dec_spec in0 in1 out0 out1 out2 out3 :=
  begin
    intros in0 in1 out0 out1 out2 out3,
    unfold dec_imp dec_spec not_ and_n AND,
    simp,
    split,
    {
      cases in0; cases in1; simp *; intros a b c d; simp*,
    },
    {
      cases in0; cases in1; simp *; intros a b c d; simp*,
    }
  end

lemma full_adder_correct (A B Cin : bool) (Sum Cout : bool) :
	full_adder_imp A B Cin Sum Cout ↔ full_adder_spec A B Cin Sum Cout :=
  begin
    split,
    {

      unfold full_adder_imp xor_n XOR or_n OR and_n AND full_adder_spec,
      cases A; cases B; cases Cin; unfold bool_to_nat; simp; unfold nat_to_bool; intros h h1; simp*,
    },
    {
      unfold full_adder_imp xor_n XOR or_n OR and_n AND full_adder_spec,
      cases A; cases B; cases Cin; unfold bool_to_nat; simp; unfold nat_to_bool; intros h h1; simp*,
    }
  end
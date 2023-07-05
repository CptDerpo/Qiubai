import Sequential Combinational


--lemma to show that there exists a unique output for all possible inputs
theorem mux_spec_unique : ∀ (IN0 IN1 SEL: bool),
  ∃! (out : bool), mux_spec IN0 IN1 SEL out :=
  begin
    intros IN0 IN1 SEL,
    apply exists_unique_of_exists_of_unique,
    { --existence of output
      cases SEL; tautology,
    },
    { --uniqueness of output
      intros y₁ y₂,
      cases SEL;
      {
        unfold mux_spec,
        simp,
        intros h₁ h₂,
        subst h₂,
        exact h₁,
      }
    }
  end

--Lemma to show that the implementation and specification are equal
theorem mux_complies_to_spec : ∀ (IN0 IN1 SEL: bool),
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

theorem n_mux_complies_to_spec {n : ℕ} : ∀ (IN0 IN1 : array n bool) (SEL : bool),
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

--lemma to show that there exists a unique output for all possible inputs
lemma mux_imp_unique : ∀ (in1 in2 sel: bool),
  ∃! (out : bool), mux_imp in1 in2 sel = out :=
  begin
    intros in1 in2 sel,
    apply exists_unique_of_exists_of_unique,
    { --existence of output: ∃ (x : bool), mux_imp in1 in2 sel = x
      cases sel; tautology,
    },
    { --uniqueness of output: ∀ (y₁ y₂ : bool), mux_imp in1 in2 sel = y₁ → mux_imp in1 in2 sel = y₂ → y₁ = y₂
      intros y₁ y₂,
      cases sel; cases in1; cases in2;
      {
        unfold mux_imp,
        simp,
        intros h₁ h₂,
        subst h₁,
        exact h₂,
      }
    }
  end



lemma mux_n_imp_unique {n : ℕ} : ∀ (in1 in2 : array n bool) (sel: bool),
  ∃! (out : array n bool), mux_n_imp in1 in2 sel = out :=
  begin
    intros in1 in2 sel,
    apply exists_unique_of_exists_of_unique,
    {
      unfold mux_n_imp,
      cases sel; cases in1; cases in2;
      {
        simp,
      }
    },
    {
      intros y₁ y₂,
      unfold mux_n_imp zip_array,
      cases sel;
      {
        intros h₁ h₂,
        subst h₁,
        exact h₂,
      }
    }
  end

theorem mem_spec_unqiue : ∀ (D S : signal),
  ∃! (OUT : signal), mem_spec D S OUT :=
begin
  intros D S,
  apply exists_unique_of_exists_of_unique,
  {
    sorry,
  },
  {
    intros y₁ y₂,
    unfold mem_spec,
    sorry,
  }
end

lemma mem_imp_complies_to_spec : ∀ (D S : signal),
  mem_spec D S (mem_imp ff D S) :=
  begin
    intros D S,
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
  mem_spec D S (n_mem_imp (mk_array n ff) D S) :=
  begin
    unfold mem_spec,
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
 

theorem full_adder_complies_to_spec : ∀ (A B CIN : bool),
  ∀ (SUM COUT : bool), full_adder_spec A B CIN SUM COUT ↔ full_adder_imp A B CIN = (SUM, COUT) :=
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

lemma zip_unzip_eq {n : ℕ} {α β : Type} (a : array n α) (b : array n β) :
  unzip_array (zip_array a b) = (a, b) :=
  begin
    unfold zip_array unzip_array,
    simp,
    split,
    {
      apply array.ext,
      intros i,
      apply array.read_map,
    },
    {
      apply array.ext,
      intros i,
      apply array.read_map,
    }
  end

lemma unzip_zip_eq {n : ℕ} {α β : Type} (a : array n (α × β)) :
  zip_array (unzip_array a).fst (unzip_array a).snd = a :=
  begin
    unfold zip_array unzip_array,
    simp,
    apply array.ext,
    intros i,
    exact prod.ext rfl rfl,
  end


import Utility tactic 

def mem_spec {α : Type} (D : stream α) (S : signal) (M : stream α) : Prop :=
  ∀ t : ℕ,
    (S t = tt → M (t+1) = D t) ∧  --frame 1 D S M+1
    (S t = ff → M (t+1) = M t)    --frame 2 S M M+1

def almost_eq {α : Type} (N M : stream α) : Prop :=
  ∀ (t : ℕ),
    (N t = M t) → ∀ (t' : ℕ), (t' > t) → N t' = M t'

def almost_eq' {α : Type} (N M : stream α) : Prop :=
  ∀ (t : ℕ),
    (N t = M t) → N (t+1) = M (t+1)

lemma almost_eq_equiv {α : Type} (N M : stream α) : almost_eq N M ↔ almost_eq' N M :=
  begin
    unfold almost_eq almost_eq',
    split,
    {
      intros h t,
      specialize h t,
      intros h₁,
      apply h,
      {
        exact h₁,
      },
      {
        simp,
      }
    },
    {
      sorry, --almost_eq too strong
    }
  end

theorem mem_spec_almost_unique {α : Type} : ∀ (D : stream α) (S : signal) (M : stream α),
  mem_spec D S M → ∀(N : stream α), mem_spec D S N → almost_eq' N M :=
  begin
    intros D S M h₁ N h₂,
    unfold almost_eq',
    intros t heq,
    unfold mem_spec at h₁ h₂,
    specialize h₁ t,
    specialize h₂ t,
    destruct h₁,
    intros h₁l h₁r,
    destruct h₂,
    intros h₂l h₂r,
    cases S t,
    {
      simp at h₂r,
      rw h₂r,
      simp at h₁r,
      rw h₁r,
      exact heq,
    },
    {
      simp at h₂l,
      rw h₂l,
      simp at h₁l,
      rw h₁l,
    }
  end

def mem_imp (I: bool) (D S: signal) : signal
  | nat.zero := I
  | (nat.succ y) := if S y = tt then D y 
                    else mem_imp y

def mem_n_imp {n : ℕ} (I : array n bool) (D : sig_n n) (S : signal) : sig_n n
  | nat.zero := I
  | (nat.succ y) := if S y = tt then D y
                    else mem_n_imp y

theorem mem_correct : ∀ (D S : signal), ∀ (I : bool),
  mem_spec D S (mem_imp I D S) :=
  begin
    intros D S I,
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

theorem mem_n_correct {n : ℕ} : ∀ (D : sig_n n) (S: signal),
  mem_spec D S (mem_n_imp (mk_array n ff) D S) :=
  begin
    unfold mem_spec,
    intros,
    split,
    {
      intros h,
      unfold mem_n_imp,
      simp, --rewrite if_pos,
      intro h', -- exact h,
      exfalso,
      rewrite h at h',
      simp at h',
      assumption,
    },
    {
      intros h,
      unfold mem_n_imp,
      simp,
      intro h',
      exfalso,
      rewrite h at h',
      simp at h',
      assumption,
    },
  end


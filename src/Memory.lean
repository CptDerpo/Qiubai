import Utility tactic data.nat.basic

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

lemma help {t' t n: nat} (h: t' > t) (hh: t' - t = n): t' = t + n :=
  begin
    rw ←hh,
    rw nat.add_sub_of_le,
    exact le_of_lt h,
  end

lemma almost_eq_equiv {α : Type} (N M : stream α) : almost_eq N M ↔
almost_eq' N M :=
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
       intros h t h₁ t' h₂,
       -- We have t' > t, so take the difference (dt)
       generalize hhh: t' - t = dt,
       destruct dt; intros; rw a at hhh,
       {
         -- Suppose dt = 0, then we can close the goal
         rw (help h₂ hhh),
         simp, tauto,
       },
       {
         -- Suppose dt > 0, then do a strong induction
         revert t',
         apply (nat.strong_induction_on n); intros n_1 IH; intros,
         destruct n_1; intros,
         {
           -- Suppose dt = 1
           rw a_1 at hhh,
           rw (help h₂ hhh),
           apply h, tauto,
         },
         {
           -- Otherwise
           rw (help h₂ hhh),
           apply h, simp,
           apply (IH n_2),
           {
            rw a_1,
            exact nat.lt_succ_self _,
           },
           repeat{
            rw a_1,
            simp,
           },
         }
       }
     }
   end


theorem mem_spec_almost_unique {α : Type} : ∀ (D : stream α) (S : signal) (M : stream α),
  mem_spec D S M → ∀(N : stream α), mem_spec D S N → almost_eq N M :=
  begin
    intros D S M h₁ N h₂,
    rw almost_eq_equiv,
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


def mem_imp {α : Type} (I : α) (D : stream α) (S : signal) : stream α
  | nat.zero := I
  | (nat.succ y) := if S y = tt then D y
                    else mem_imp y


theorem mem_correct {α : Type} : ∀ (D : stream α) (S: signal), ∀ (I : α),
  mem_spec D S (mem_imp (I) D S) :=
  begin
    unfold mem_spec,
    intros,
    split,
    {
      intros h,
      unfold mem_imp,
      rw if_pos,
      exact h,
    },
    {
      intros h,
      unfold mem_imp,
      rw if_neg,
      simp,
      exact h,
    }
  end
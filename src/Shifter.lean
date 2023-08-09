import Utility

def shft_spec {n : ℕ} (A : array n bool) (D : bool) (OUT : array n bool) : Prop :=
  if D = tt then OUT = ⟨λ i, if h : i.val > 0 ∧ i.val - 1 < n then A.read ⟨i.val - 1, h.right⟩ else ff⟩
            else OUT = ⟨λ i, if h : i.val + 1 < n then A.read ⟨i.val + 1, h⟩ else ff⟩

theorem shft_unique {n : ℕ} : ∀ (A : array n bool) (D : bool),
	∃! (OUT : array n bool), shft_spec A D OUT :=
  begin
    intros A D,
    apply exists_unique_of_exists_of_unique,
    {
      unfold shft_spec,
      cases D;
      {
        exact exists_eq,
      }
    },
    {
      intros y₁ y₂,
      unfold shft_spec,
      intros h₁ h₂,
      cases D;
      {
        simp at h₁ h₂,
        rewrite ←h₂ at h₁,
        exact h₁,
      }
    }
  end

def shft_imp (A : array 4 bool) (D : bool) : array 4 bool :=
  let D':= NOT D,
      p := AND [A.read 0, D],
      q := AND [D', A.read 1],
      r := AND [D, A.read 1],
      s := AND [D', A.read 2],
      t := AND [D, A.read 2],
      u := AND [D', A.read 3] in
  [q, OR[p, s], OR[r, u], t].to_array

theorem shft_correct : ∀ (A : array 4 bool) (D : bool),
  shft_spec A D (shft_imp A D) :=
  begin
    intros A D,
    unfold shft_spec,
    simp,
    cases D;
    {
      simp,
      unfold shft_imp,
      apply array.ext,
      intro i,
      ring_nf,
      unfold list.to_array,
      dsimp at *,
      unfold AND NOT OR,
      simp,
      cases i,
      cases i_val with i_val₁,
      {
        refl,
      },
      {
        cases i_val₁ with i_val₂,
        {
          refl,
        },
        {
          cases i_val₂ with i_val₃,
          {
            refl,
          },
          {
            cases i_val₃ with i_val₄,
            {
              refl,
            },
            {
              exfalso,
              repeat { rw nat.succ_eq_add_one at i_property },
              simp at i_property,
              exact i_property,
            }
          }
        }
      }
    }
  end
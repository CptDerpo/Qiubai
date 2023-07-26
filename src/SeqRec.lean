import Utility tactic

--Logic Unit 2
def LUT2 (Q1 Q0 X : bool) : bool :=
  OR [AND [Q1, Q0, X], AND [Q1, NOT Q0 , X], AND[NOT Q1, Q0, X], AND[NOT Q1, NOT Q0, X]]

def LUT2_spec (Q1 Q0 X OUT : bool) : Prop :=
  if (¬Q1 ∧ ¬Q0 ∧ X) ∨ (¬Q1 ∧ Q0 ∧ X) ∨ (Q1 ∧ ¬Q0 ∧ X) ∨ (Q1 ∧ Q0 ∧ X) then OUT = tt
  else OUT = ff

theorem LUT2_correct : ∀ (Q1 Q0 X : bool),
  ∀ (OUT : bool), LUT2_spec Q1 Q0 X OUT ↔ LUT2 Q1 Q0 X  = OUT :=
  begin
    intros,
    unfold LUT2_spec LUT2,
    cases Q1; cases Q0; cases X;
    {
      unfold AND OR NOT,
      simp,
      rw eq_comm,
    }
  end

--Logic Unit 3
def LUT3 (Q1 Q0 X : bool) : bool :=
  OR [AND [NOT Q1, Q0, NOT X], AND [Q1, NOT Q0 , X], AND [Q1, Q0, X]]


def LUT3_spec (Q1 Q0 X OUT : bool) : Prop :=
  if (¬Q1 ∧ Q0 ∧ ¬X) ∨ (Q1 ∧ ¬Q0 ∧ X) ∨ (Q1 ∧ Q0 ∧ X) then OUT = tt
  else OUT = ff

theorem LUT3_correct : ∀ (Q1 Q0 X : bool),
  ∀ (OUT : bool), LUT3_spec Q1 Q0 X OUT ↔ LUT3 Q1 Q0 X  = OUT :=
  begin
    intros,
    unfold LUT3_spec LUT3,
    cases Q1; cases Q0; cases X;
    {
      unfold AND OR NOT,
      simp,
      rw eq_comm,
    }
  end

--Logic Unit 0
def LUT0 (Q1 Q0 : bool) : bool :=
  AND[Q1, Q0]

def LUT0_spec (Q1 Q0 OUT : bool) :=
  if Q1 ∧ Q0 then OUT = tt else OUT = ff

theorem LUT0_correct : ∀ (Q1 Q0 : bool), ∀ (OUT : bool),
  LUT0_spec Q1 Q0 OUT ↔ LUT0 Q1 Q0 = OUT :=
  begin
    intros,
    unfold LUT0_spec LUT0,
    cases Q1; cases Q0;
    {
      unfold AND OR,
      simp,
      rw eq_comm,
    }
  end

--Complete circuit
def SeqRecAux {n : ℕ} (X : signal) : Π (i : ℕ), i ≤ n → bool → bool → bool → ℕ → bool
  |(nat.zero) h Q1 Q0 O k :=
    if k ≤ 3 then
      let Q1_next := LUT3 Q1 Q0 (X 0),
          Q0_next := LUT2 Q1 Q0 (X 0),
          O_next := LUT0 Q1_next Q0_next in
      if O = tt then tt
      else ff
    else ff
  |(nat.succ t) h Q1 Q0 O k :=
    if k ≤ 3 then
      let Q1_next := LUT3 Q1 Q0 (X t),
          Q0_next := LUT2 Q1 Q0 (X t),
          O_next := LUT0 Q1_next Q0_next in
      if O = tt then tt
      else if k = 3 then ff
      else SeqRecAux (t) (le_of_lt h) Q1_next Q0_next (O_next) (k+1)
    else ff

def SeqRec (X : signal) : signal :=
  λ n, SeqRecAux X (n) (le_refl _) ff ff ff 0

def SeqRec_spec (X OUT : ℕ → bool) : Prop :=
  ∀ t : ℕ, 
    (X t = tt → X (t+1) = ff → X (t+2) = tt → OUT (t+3) = tt) ∧ 
    (X t = ff → OUT (t+3) = ff)

def SeqReq_correct : ∀ (X : ℕ → bool),
  SeqRec_spec X (SeqRec X) :=
  begin
    intros X,
    unfold SeqRec_spec,
    intros t,
    split,
    {
      intros h₁ h₂ h₃,
      unfold SeqRec,
      repeat {
        unfold SeqRecAux,
        simp,
      },
      unfold LUT0 LUT3 LUT2 OR AND,
      simp,
      unfold NOT,
      simp,
      rw h₃,
      rw h₂,
      simp,
      unfold NOT,
      simp,
      rw h₁,
      ring_nf,
      simp,
      cases t,
      {
        unfold SeqRecAux,
        simp,
      },
      {
        unfold SeqRecAux,
        simp,
      }
    },
    {
      intro h₁,
      unfold SeqRec,
      repeat {
        unfold SeqRecAux,
        simp,
      },
      simp [LUT0, LUT2, LUT3, AND, OR, NOT],
      cases X (t+1); cases X(t+2);
      {
        simp [NOT],
        ring_nf,
        simp,
        cases t,
        {
          unfold SeqRecAux,
          finish,
        },
        {
          unfold SeqRecAux,
          finish,
        }
      }
    },
  end

--Example
def X : signal := λx,x=0 ∨ x = 2 ∨ x = 4 ∨ x = 6 ∨ x=8 ∨ x=15 ∨ x = 17 
#eval (SeqRec X) 


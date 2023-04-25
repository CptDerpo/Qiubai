def AND : list bool → bool
  | [] := true
  | (h::t) := h ∧ AND t

def OR : list bool -> bool
  | [] := false
  | (h::t) := h ∨ OR t

def XOR : list bool → bool
  | [] := false
  | [b] := b
  | (h1::h2::t) := XOR ((h1 ≠ h2) :: t)

def not_ (a : bool) (out : bool) : bool :=
  out = ¬a

def and_n (a : list bool) (out : bool) : bool :=
  out = AND a

def nand_n (a : list bool) (out : bool) : bool :=
  out = ¬AND a

def or_n (a : list bool) (out : bool) : bool :=
  out = OR a

def nor_n (a : list bool) (out : bool) : bool :=
  out = ¬OR a

def xor_n (a : list bool) (out : bool) : bool :=
  out = XOR a

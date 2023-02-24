import Gates tactic 

def clk : ℕ → bool
| 0 := tt
| (n+1) := if clk n then ff else tt

def test_clk : ℕ → list bool
| 0 := [clk 0]
| (n+1) := (clk (n+1)) :: test_clk n

#eval test_clk 10 
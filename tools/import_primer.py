"""The primer: rung 0 of the ladder. The Natural Number Game (Lean 4 edition,
leanprover-community/NNG4, Apache-2.0) restated over Mathlib's ℕ, one file per level,
plus a reference proof per statement so a miss is provably the lane's, not the rung's.

    python3 tools/import_primer.py          # regenerates targets/primer/ (deterministic)

Skipped on purpose: Power L10 (Fermat's Last Theorem, the game's joke level), and three
levels whose statement repeats an earlier one verbatim (Tutorial L04 and L06, Algorithm
L04). The game's own naturals are an inductive type with its own axioms; over Mathlib the
same statements hold with Mathlib's lemmas, so the reference proofs cite those instead of
the game's inventory.
"""
from pathlib import Path

NNG4 = "https://github.com/leanprover-community/NNG4/blob/main/Game/Levels"

# (world, level file, title, binders-and-statement, reference proof)
LEVELS = [
 ("Tutorial", "L01rfl", "The rfl tactic", "(x q : ℕ) : 37 * x + q = 37 * x + q", "rfl"),
 ("Tutorial", "L02rw", "the rw tactic", "(x y : ℕ) (h : y = x + 7) : 2 * y = 2 * (x + 7)", "rw [h]"),
 ("Tutorial", "L03two_eq_ss0", "Numbers", ": (2 : ℕ) = Nat.succ (Nat.succ 0)", "rfl"),
 ("Tutorial", "L05add_zero", "Adding zero", "(a b c : ℕ) : a + (b + 0) + (c + 0) = a + b + c", "simp"),
 ("Tutorial", "L07add_succ", "add_succ", "(n : ℕ) : Nat.succ n = n + 1", "rfl"),
 ("Tutorial", "L08twoaddtwo", "2+2=4", ": (2 : ℕ) + 2 = 4", "norm_num"),
 ("Addition", "L01zero_add", "zero_add", "(n : ℕ) : 0 + n = n", "exact Nat.zero_add n"),
 ("Addition", "L02succ_add", "succ_add", "(a b : ℕ) : Nat.succ a + b = Nat.succ (a + b)", "exact Nat.succ_add a b"),
 ("Addition", "L03add_comm", "add_comm (level boss)", "(a b : ℕ) : a + b = b + a", "exact Nat.add_comm a b"),
 ("Addition", "L04add_assoc", "add_assoc", "(a b c : ℕ) : a + b + c = a + (b + c)", "exact Nat.add_assoc a b c"),
 ("Addition", "L05add_right_comm", "add_right_comm", "(a b c : ℕ) : a + b + c = a + c + b", "exact Nat.add_right_comm a b c"),
 ("Multiplication", "L01mul_one", "mul_one", "(m : ℕ) : m * 1 = m", "exact Nat.mul_one m"),
 ("Multiplication", "L02zero_mul", "zero_mul", "(m : ℕ) : 0 * m = 0", "exact Nat.zero_mul m"),
 ("Multiplication", "L03succ_mul", "succ_mul", "(a b : ℕ) : Nat.succ a * b = a * b + b", "exact Nat.succ_mul a b"),
 ("Multiplication", "L04mul_comm", "mul_comm", "(a b : ℕ) : a * b = b * a", "exact Nat.mul_comm a b"),
 ("Multiplication", "L05one_mul", "one_mul", "(m : ℕ) : 1 * m = m", "exact Nat.one_mul m"),
 ("Multiplication", "L06two_mul", "two_mul", "(m : ℕ) : 2 * m = m + m", "exact Nat.two_mul m"),
 ("Multiplication", "L07mul_add", "mul_add", "(a b c : ℕ) : a * (b + c) = a * b + a * c", "exact Nat.mul_add a b c"),
 ("Multiplication", "L08add_mul", "add_mul", "(a b c : ℕ) : (a + b) * c = a * c + b * c", "exact Nat.add_mul a b c"),
 ("Multiplication", "L09mul_assoc", "mul_assoc", "(a b c : ℕ) : a * b * c = a * (b * c)", "exact Nat.mul_assoc a b c"),
 ("Power", "L01zero_pow_zero", "zero_pow_zero", ": (0 : ℕ) ^ 0 = 1", "rfl"),
 ("Power", "L02zero_pow_succ", "zero_pow_succ", "(m : ℕ) : (0 : ℕ) ^ (Nat.succ m) = 0", "simp [pow_succ]"),
 ("Power", "L03pow_one", "pow_one", "(a : ℕ) : a ^ 1 = a", "exact pow_one a"),
 ("Power", "L04one_pow", "one_pow", "(m : ℕ) : (1 : ℕ) ^ m = 1", "exact one_pow m"),
 ("Power", "L05pow_two", "pow_two", "(a : ℕ) : a ^ 2 = a * a", "ring"),
 ("Power", "L06pow_add", "pow_add", "(a m n : ℕ) : a ^ (m + n) = a ^ m * a ^ n", "exact pow_add a m n"),
 ("Power", "L07mul_pow", "mul_pow", "(a b n : ℕ) : (a * b) ^ n = a ^ n * b ^ n", "exact mul_pow a b n"),
 ("Power", "L08pow_pow", "pow_pow", "(a m n : ℕ) : (a ^ m) ^ n = a ^ (m * n)", "exact (pow_mul a m n).symm"),
 ("Power", "L09add_sq", "add_sq", "(a b : ℕ) : (a + b) ^ 2 = a ^ 2 + b ^ 2 + 2 * a * b", "ring"),
 ("Implication", "L01exact", "The exact tactic", "(x y z : ℕ) (h1 : x + y = 37) (h2 : 3 * x + z = 42) : x + y = 37", "exact h1"),
 ("Implication", "L02exact2", "exact practice", "(x y : ℕ) (h : 0 + x = 0 + y + 2) : x = y + 2", "omega"),
 ("Implication", "L03apply", "The apply tactic", "(x y : ℕ) (h1 : x = 37) (h2 : x = 37 → y = 42) : y = 42", "exact h2 h1"),
 ("Implication", "L04succ_inj", "succ_inj", "(x : ℕ) (h : x + 1 = 4) : x = 3", "omega"),
 ("Implication", "L06intro", "intro", "(x : ℕ) : x = 37 → x = 37", "intro h\n  exact h"),
 ("Implication", "L07intro2", "intro practice", "(x y : ℕ) : x + 1 = y + 1 → x = y", "intro h\n  omega"),
 ("Implication", "L08ne", "≠", "(x y : ℕ) (h1 : x = y) (h2 : x ≠ y) : False", "exact h2 h1"),
 ("Implication", "L09zero_ne_succ", "zero_ne_one", ": (0 : ℕ) ≠ 1", "decide"),
 ("Implication", "L10one_ne_zero", "1 ≠ 0", ": (1 : ℕ) ≠ 0", "decide"),
 ("Implication", "L11two_add_two_ne_five", "2 + 2 ≠ 5", ": Nat.succ (Nat.succ 0) + Nat.succ (Nat.succ 0) ≠ Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ 0))))", "decide"),
 ("Algorithm", "L01add_left_comm", "add_left_comm", "(a b c : ℕ) : a + (b + c) = b + (a + c)", "exact Nat.add_left_comm a b c"),
 ("Algorithm", "L02add_algo1", "making life easier", "(a b c d : ℕ) : a + b + (c + d) = a + c + d + b", "omega"),
 ("Algorithm", "L03add_algo2", "making life simple", "(a b c d e f g h : ℕ) : (d + f) + (h + (a + c)) + (g + e + b) = a + b + c + d + e + f + g + h", "omega"),
 ("Algorithm", "L05pred", "pred", "(a b : ℕ) (h : Nat.succ a = Nat.succ b) : a = b", "exact Nat.succ.inj h"),
 ("Algorithm", "L06is_zero", "is_zero", "(a : ℕ) : Nat.succ a ≠ 0", "exact Nat.succ_ne_zero a"),
 ("Algorithm", "L07succ_ne_succ", "An algorithm for equality", "(m n : ℕ) (h : m ≠ n) : Nat.succ m ≠ Nat.succ n", "intro h2\n  exact h (Nat.succ.inj h2)"),
 ("Algorithm", "L08decide", "decide", ": (20 : ℕ) + 20 = 40", "decide"),
 ("Algorithm", "L09decide2", "decide again", ": (2 : ℕ) + 2 ≠ 5", "decide"),
 ("AdvAddition", "L01add_right_cancel", "add_right_cancel", "(a b n : ℕ) : a + n = b + n → a = b", "intro h\n  omega"),
 ("AdvAddition", "L02add_left_cancel", "add_left_cancel", "(a b n : ℕ) : n + a = n + b → a = b", "intro h\n  omega"),
 ("AdvAddition", "L03add_left_eq_self", "add_left_eq_self", "(x y : ℕ) : x + y = y → x = 0", "intro h\n  omega"),
 ("AdvAddition", "L04add_right_eq_self", "add_right_eq_self", "(x y : ℕ) : x + y = x → y = 0", "intro h\n  omega"),
 ("AdvAddition", "L05add_right_eq_zero", "add_right_eq_zero", "(a b : ℕ) : a + b = 0 → a = 0", "intro h\n  omega"),
 ("AdvAddition", "L06add_left_eq_zero", "add_left_eq_zero", "(a b : ℕ) : a + b = 0 → b = 0", "intro h\n  omega"),
 ("LessOrEqual", "L01le_refl", "The use tactic", "(x : ℕ) : x ≤ x", "exact Nat.le_refl x"),
 ("LessOrEqual", "L02zero_le", "0 ≤ x", "(x : ℕ) : 0 ≤ x", "exact Nat.zero_le x"),
 ("LessOrEqual", "L03le_succ_self", "x ≤ succ x", "(x : ℕ) : x ≤ Nat.succ x", "exact Nat.le_succ x"),
 ("LessOrEqual", "L04le_trans", "le_trans", "(x y z : ℕ) (hxy : x ≤ y) (hyz : y ≤ z) : x ≤ z", "exact Nat.le_trans hxy hyz"),
 ("LessOrEqual", "L05le_zero", "x ≤ 0 → x = 0", "(x : ℕ) (hx : x ≤ 0) : x = 0", "omega"),
 ("LessOrEqual", "L06le_antisymm", "le_antisymm", "(x y : ℕ) (hxy : x ≤ y) (hyx : y ≤ x) : x = y", "omega"),
 ("LessOrEqual", "L07or_symm", "Dealing with or", "(x y : ℕ) (h : x = 37 ∨ y = 42) : y = 42 ∨ x = 37", "exact Or.symm h"),
 ("LessOrEqual", "L08le_total", "le_total", "(x y : ℕ) : x ≤ y ∨ y ≤ x", "exact Nat.le_total x y"),
 ("LessOrEqual", "L09succ_le_succ", "succ_le_succ", "(x y : ℕ) (hx : Nat.succ x ≤ Nat.succ y) : x ≤ y", "exact Nat.le_of_succ_le_succ hx"),
 ("LessOrEqual", "L10le_one", "le_one", "(x : ℕ) (hx : x ≤ 1) : x = 0 ∨ x = 1", "omega"),
 ("LessOrEqual", "L11le_two", "le_two", "(x : ℕ) (hx : x ≤ 2) : x = 0 ∨ x = 1 ∨ x = 2", "omega"),
 ("AdvMultiplication", "L01mul_le_mul_right", "mul_le_mul_right", "(a b t : ℕ) (h : a ≤ b) : a * t ≤ b * t", "exact Nat.mul_le_mul_right t h"),
 ("AdvMultiplication", "L02mul_left_ne_zero", "mul_left_ne_zero", "(a b : ℕ) (h : a * b ≠ 0) : b ≠ 0", "intro hb\n  subst hb\n  simp at h"),
 ("AdvMultiplication", "L03eq_succ_of_ne_zero", "eq_succ_of_ne_zero", "(a : ℕ) (ha : a ≠ 0) : ∃ n, a = Nat.succ n", "exact Nat.exists_eq_succ_of_ne_zero ha"),
 ("AdvMultiplication", "L04one_le_of_ne_zero", "one_le_of_ne_zero", "(a : ℕ) (ha : a ≠ 0) : 1 ≤ a", "omega"),
 ("AdvMultiplication", "L05le_mul_right", "le_mul_right", "(a b : ℕ) (h : a * b ≠ 0) : a ≤ a * b", "rcases Nat.eq_zero_or_pos b with rfl | hb\n  · simp at h\n  · exact Nat.le_mul_of_pos_right a hb"),
 ("AdvMultiplication", "L06mul_right_eq_one", "mul_right_eq_one", "(x y : ℕ) (h : x * y = 1) : x = 1", "have h1 : x ∣ 1 := ⟨y, h.symm⟩\n  exact Nat.dvd_one.mp h1"),
 ("AdvMultiplication", "L07mul_ne_zero", "mul_ne_zero", "(a b : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) : a * b ≠ 0", "exact Nat.mul_ne_zero ha hb"),
 ("AdvMultiplication", "L08mul_eq_zero", "mul_eq_zero", "(a b : ℕ) (h : a * b = 0) : a = 0 ∨ b = 0", "exact mul_eq_zero.mp h"),
 ("AdvMultiplication", "L09mul_left_cancel", "mul_left_cancel", "(a b c : ℕ) (ha : a ≠ 0) (h : a * b = a * c) : b = c", "exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero ha) h"),
 ("AdvMultiplication", "L10mul_right_eq_self", "mul_right_eq_self", "(a b : ℕ) (ha : a ≠ 0) (h : a * b = a) : b = 1", "exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero ha) (by rw [h, Nat.mul_one])"),
]

WORLD_SLUG = {"Tutorial": "tutorial", "Addition": "addition", "Multiplication": "multiplication", "Power": "power",
              "Implication": "implication", "Algorithm": "algorithm", "AdvAddition": "advaddition",
              "LessOrEqual": "lessorequal", "AdvMultiplication": "advmultiplication"}
WORLD_RANK = {w: i for i, w in enumerate(WORLD_SLUG)}


def name_of(world, level):
    num = level[1:3]
    slug = level[3:].lower()
    return f"primer_{WORLD_SLUG[world]}_{num}_{slug}"


def render(world, level, title, stmt, proof):
    name = name_of(world, level)
    doc = (f"/-- Natural Number Game (Lean 4), {world} world, level {int(level[1:3])}: {title}. "
           f"Restated over Mathlib's ℕ. Source: {NNG4}/{world}/{level}.lean, Apache-2.0. -/")
    head = f"theorem {name} {stmt} := by".replace("theorem " + name + " :", "theorem " + name + " :")
    body = "\n".join("  " + line if not line.startswith("  ") else line for line in proof.split("\n"))
    stmt_file = f"import Mathlib\n\n{doc}\n{head}\n  sorry\n"
    ref_file = f"import Mathlib\n\n{doc}\n{head}\n{body}\n"
    return name, stmt_file, ref_file


def main():
    root = Path(__file__).resolve().parent.parent / "targets" / "primer"
    (root / "reference").mkdir(parents=True, exist_ok=True)
    rows = []
    for world, level, title, stmt, proof in LEVELS:
        name, sf, rf = render(world, level, title, stmt, proof)
        (root / f"{name}.lean").write_text(sf)
        (root / "reference" / f"{name}.lean").write_text(rf)
        rows.append((WORLD_RANK[world], world, level, name))
    print(f"wrote {len(rows)} statements + {len(rows)} reference proofs to {root}")


if __name__ == "__main__":
    main()

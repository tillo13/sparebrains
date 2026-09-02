"""The ladder: which rung each target sits on, and what kind of failure a reject was.

Rungs are provenance, never our own results (that would be circular):
  primer      Natural Number Game levels restated over ℕ (leanprover-community/NNG4)
  mil         Mathematics in Lean exercises, chapters 2–6 (Avigad & Massot)
  math-L1..L5 miniF2F `mathd_*` items, labelled by the MATH dataset's own Level 1–5
              (Hendrycks et al. 2021; the mapping lives in targets/minif2f/levels.json)
  mathd       a `mathd_*` item the mapping could not label
  amc12, custom, aime, imo   the rest of miniF2F by problem source
"""
import json, re
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
RUNGS = ["primer", "mil", "math-L1", "math-L2", "math-L3", "math-L4", "math-L5", "mathd", "amc12", "custom", "aime", "imo"]
RANK = {r: i for i, r in enumerate(RUNGS)}
PRIMER_WORLDS = ["tutorial", "addition", "multiplication", "power", "implication", "algorithm",
                 "advaddition", "lessorequal", "advmultiplication"]          # the game's own order
_levels = None


def _math_levels():
    global _levels
    if _levels is None:
        p = ROOT / "targets" / "minif2f" / "levels.json"
        _levels = json.loads(p.read_text()) if p.exists() else {}
    return _levels


def sort_key(target_set, name):
    """Order inside a rung: the primer follows the game's worlds, everything else its name."""
    if target_set == "primer":
        world = name.split("_")[1] if "_" in name else ""
        return (PRIMER_WORLDS.index(world) if world in PRIMER_WORLDS else 99, name)
    return (0, name)


def rung_of(target_set, name):
    """(rung label, rank) for one target. Unknown sets rank last so they still run."""
    if target_set == "primer":
        return "primer", RANK["primer"]
    if target_set == "mil":
        return "mil", RANK["mil"]
    if name.startswith("mathd_"):
        lv = (_math_levels().get(name) or {}).get("level")
        if lv in (1, 2, 3, 4, 5):
            return f"math-L{lv}", RANK[f"math-L{lv}"]
        return "mathd", RANK["mathd"]
    if name.startswith("amc12"):
        return "amc12", RANK["amc12"]
    if name.startswith("aime"):
        return "aime", RANK["aime"]
    if name.startswith("imo"):
        return "imo", RANK["imo"]
    return "custom", RANK["custom"]


# Why a kernel reject happened, from the first Lean error line. The bottom rungs are
# where this matters: a Lean 3 `begin … end` fails 2 + 2 = 4 exactly the way it fails an
# IMO problem, and the scoreboard must say "syntax", never "cannot add".
_KINDS = [
    ("no_fence",       re.compile(r"no proof extracted")),
    ("lean3_syntax",   re.compile(r"unexpected token|unexpected identifier|expected command|expected '\}'|'begin'|'end'", re.I)),
    ("unknown_name",   re.compile(r"unknown (identifier|constant|tactic|namespace)|unknownIdentifier|unknownConstant", re.I)),
    ("sorry",          re.compile(r"sorry|admit|native_decide|axiom", re.I)),
    ("timeout",        re.compile(r"timeout|timed out|maximum recursion|deterministic", re.I)),
    ("unsolved_goals", re.compile(r"unsolved goals", re.I)),
    ("tactic_failed",  re.compile(r"failed|could not|made no progress|no goals", re.I)),
    ("type_mismatch",  re.compile(r"type mismatch", re.I)),
]


def failure_kind(verdict, reason):
    if verdict == "accept":
        return None
    if verdict == "error":
        return "lane_error"
    for kind, rx in _KINDS:
        if rx.search(reason or ""):
            return kind
    return "other"

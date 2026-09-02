"""Materialize Mathematics in Lean exercises as one .lean target per block.

Source: leanprover-community/mathematics_in_lean (Apache-2.0), the solution files of
chapters 2-6, pinned to one commit. Every `example`/`theorem` with a tactic proof that
depends on nothing else in its file becomes `targets/mil/<name>.lean` (proof replaced
by `sorry`) and `targets/mil/reference/<name>.lean` (upstream proof kept). Section-level
`variable`s the statement uses are inlined as binders; in-scope `open` lines are carried
over. Blocks that reference a local def/theorem, need a section variable the statement
does not mention, have a term-mode proof, or repeat an earlier statement are skipped and
listed in the README with the reason. First PER_CHAPTER admissible blocks per chapter.

    python3 tools/import_mil.py        # rewrites targets/mil/ (targets, reference/, README, LICENSE)
"""
import re, shutil, sys, urllib.request
from pathlib import Path

REPO = "leanprover-community/mathematics_in_lean"
SHA = "dd6d752fedb14082f557913c2dccb2d4851e5173"   # master @ 2026-06-10
SHA_DATE = "2026-06-10"
PER_CHAPTER = 15
ROOT = Path(__file__).resolve().parent.parent
OUT = ROOT / "targets" / "mil"
STALE = ROOT / "_oneoff" / "mil_stale"

# chapter dir -> solution files, in book order (fixed by the pinned commit)
FILES = {
    "C02_Basics": [
        "S01_Calculating", "S02_Proving_Identities_in_Algebraic_Structures",
        "S03_Using_Theorems_and_Lemmas", "S04_More_on_Order_and_Divisibility",
        "S05_Proving_Facts_about_Algebraic_Structures"],
    "C03_Logic": [
        "S01_Implication_and_the_Universal_Quantifier", "S02_The_Existential_Quantifier",
        "S03_Negation", "S04_Conjunction_and_Iff", "S05_Disjunction",
        "S06_Sequences_and_Convergence"],
    "C04_Sets_and_Functions": [
        "S01_Sets", "S02_Functions", "S03_The_Schroeder_Bernstein_Theorem"],
    "C05_Elementary_Number_Theory": [
        "S01_Irrational_Roots", "S02_Induction_and_Recursion", "S03_Infinitely_Many_Primes",
        "S04_More_Induction"],
    "C06_Discrete_Mathematics": [
        "S01_Finsets_and_Fintypes", "S02_Counting_Arguments", "S03_Inductive_Structures"],
}

TOKEN = re.compile(r"[^\W\d][\w'!?]*")
DECL = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:noncomputable\s+)?(?:private\s+|protected\s+)?"
                  r"(?:def|theorem|lemma|abbrev|structure|class|instance|inductive|notation|axiom|opaque)"
                  r"\s+([^\s(:{\[]+)")
BLOCK = re.compile(r"^(example|theorem|lemma)\b\s*(?:([^\s(:{\[]+))?")
PROOF_SEP = re.compile(r":=\s*by\b")
OPEN, CLOSE = "({[⦃", ")}]⦄"
# names bound inside a statement: ∀ x y : T, / ∃ x ∈ s, / fun x ↦ / { x | .. } / ∑ i ∈ s,
INNER_BINDERS = [re.compile(r"[∀∃λ]\s*([^,]*?),"), re.compile(r"\bfun\s+([^↦=]*?)(?:↦|=>)"),
                 re.compile(r"\{\s*([^|{}]*?)\s*\|"), re.compile(r"[∑∏⋃⋂]\s*([^,]*?),")]


def fetch(path):
    url = f"https://raw.githubusercontent.com/{REPO}/{SHA}/{path}"
    with urllib.request.urlopen(url, timeout=60) as r:
        return r.read().decode()


def match_bracket(text, i):
    depth = 0
    for j in range(i, len(text)):
        if text[j] in OPEN:
            depth += 1
        elif text[j] in CLOSE:
            depth -= 1
            if depth == 0:
                return j
    raise ValueError(f"unbalanced bracket in {text!r}")


def top_level_colon(text):
    depth = 0
    for j, c in enumerate(text):
        if c in OPEN:
            depth += 1
        elif c in CLOSE:
            depth -= 1
        elif c == ":" and depth == 0 and text[j:j + 2] != ":=":
            return j
    return -1


def parse_group(kind, inner):
    k = top_level_colon(inner)
    if k < 0:
        return {"kind": kind, "names": [], "type": inner.strip()}
    return {"kind": kind, "names": inner[:k].split(), "type": inner[k + 1:].strip()}


def binder_groups(text):
    """Leading bracket groups of `text`; returns (groups, rest)."""
    groups, i = [], 0
    while i < len(text):
        c = text[i]
        if c.isspace():
            i += 1
        elif c in OPEN:
            j = match_bracket(text, i)
            groups.append(parse_group(c, text[i + 1:j]))
            i = j + 1
        else:
            break
    return groups, text[i:]


def render_group(g, names):
    close = CLOSE[OPEN.index(g["kind"])]
    if not names:
        return f"{g['kind']}{g['type']}{close}"
    return f"{g['kind']}{' '.join(names)} : {g['type']}{close}"


def inner_bound_names(text):
    found = set()
    for rx in INNER_BINDERS:
        for m in rx.finditer(text):
            head = re.split(r"[:∈<>≤≥≠]", m.group(1), maxsplit=1)[0]
            found |= set(TOKEN.findall(re.sub(r"[{}()]", " ", head)))
    return found


def commands(src):
    """Split a file into column-0 commands: (line_no, text)."""
    out, cur, start = [], [], 0
    for n, line in enumerate(src.splitlines(), 1):
        if line and not line[0].isspace():
            if cur:
                out.append((start, "\n".join(cur)))
            cur, start = [line], n
        elif cur:
            cur.append(line)
    if cur:
        out.append((start, "\n".join(cur)))
    return out


def inline_variables(groups, tail, own_names, proof):
    """Which in-scope `variable` groups the statement needs, tracking bindings by position
    so a re-declared name shadows the earlier one. Returns (binder strings, proof-only names)."""
    def resolve(name, upto):
        for gi in range(upto - 1, -1, -1):
            if name in groups[gi]["names"]:
                return (name, gi)
        return None

    def bindings(text, upto, exclude=()):
        return {b for t in set(TOKEN.findall(text)) - set(exclude) for b in [resolve(t, upto)] if b}

    included = bindings(tail, len(groups), own_names)
    while True:
        more = set()
        for name, gi in included:
            more |= bindings(groups[gi]["type"], gi)
        if more <= included:
            break
        included |= more
    proof_only = sorted(n for n, _ in bindings(proof, len(groups), own_names) - included)
    out = []
    for gi, g in enumerate(groups):
        if g["names"]:
            keep = [n for n in g["names"] if (n, gi) in included]
            if keep:
                out.append(render_group(g, keep))
        else:
            deps = bindings(g["type"], gi)
            if deps and deps <= included:
                out.append(render_group(g, []))
    return out, proof_only


def section_title(fname):
    return fname.split("_", 1)[1].replace("_", " ")


def process_file(chapter, sec_no, fname, src, ctx):
    """Walk one solution file; append emitted/skipped records to ctx. Returns block count."""
    scopes = [{"opens": [], "vars": []}]
    declared = set()          # names declared earlier in this file (full and last component)
    idx = 0
    prefix = f"mil_c{chapter:02d}_s{sec_no:02d}"
    doc = (f"/-- Mathematics in Lean, Chapter {chapter} §{sec_no} ({section_title(fname)}), "
           f"exercise {{k}}. Avigad & Massot, Apache-2.0, commit {SHA[:7]}. -/")
    for _line, text in commands(src):
        first = text.split("\n", 1)[0].strip()
        bm = BLOCK.match(text)
        if not bm:
            word = first.split()[0] if first else ""
            if word in ("section", "namespace") or first == "noncomputable section":
                scopes.append({"opens": [], "vars": []})
            elif word == "end":
                scopes.pop()
            elif word == "open":
                scopes[-1]["opens"].append(first)
            elif word == "variable":
                scopes[-1]["vars"].extend(binder_groups(text[len("variable"):].replace("\n", " "))[0])
            dm = DECL.match(text)
            if dm:
                declared |= {dm.group(1), dm.group(1).split(".")[-1]}
            continue

        idx += 1
        orig_name = bm.group(2)
        name = f"{prefix}_ex{idx:02d}"
        label = f"c{chapter:02d} s{sec_no:02d} ex{idx:02d}" + (f" `{orig_name}`" if orig_name else "")
        own_tokens = set(TOKEN.findall(orig_name)) if orig_name else set()
        declared_after = {orig_name.removeprefix("_root_."), orig_name.split(".")[-1]} if orig_name else set()

        def skip(reason):
            ctx["skipped"].append((label, reason))
            declared.update(declared_after)

        sep = PROOF_SEP.search(text)
        if not sep or sep.start() != text.find(":="):
            skip("term-mode proof (no `:= by`)"); continue
        tail = text[bm.end():sep.start()].strip()
        rest = text[sep.end():].rstrip()
        if re.search(r"\bsorry\b", rest):
            skip("proof uses `sorry`"); continue
        try:
            own_groups, type_text = binder_groups(tail)
        except ValueError:
            type_text = ""
        if not type_text.startswith(":"):
            skip("could not parse the header"); continue
        local = sorted((set(TOKEN.findall(tail + " " + rest)) - own_tokens) & declared)
        if local:
            skip(f"references local declaration `{local[0]}`"); continue

        groups = [g for s in scopes for g in s["vars"]]
        var_names = {n for g in groups for n in g["names"]}
        clash = sorted(inner_bound_names(tail) & var_names)
        if clash:
            skip(f"statement re-binds section variable `{clash[0]}`"); continue
        own_names = {n for g in own_groups for n in g["names"]}
        inlined, proof_only = inline_variables(groups, tail, own_names, rest)
        if proof_only:
            skip(f"proof uses section variable `{proof_only[0]}` that the statement does not mention"); continue

        header = f"theorem {name} " + (" ".join(inlined) + " " if inlined else "") + tail
        key = re.sub(r"\s+", " ", (" ".join(inlined) + " " + tail).strip())
        if key in ctx["seen"]:
            skip(f"duplicate of `{ctx['seen'][key]}`"); continue
        if ctx["per_chapter"][chapter] >= PER_CHAPTER:
            ctx["beyond"].append(label); declared.update(declared_after); continue

        opens = []
        for s in scopes:
            for o in s["opens"]:
                if o not in opens:
                    opens.append(o)
        preamble = "import Mathlib\n\n" + ("\n".join(opens) + "\n\n" if opens else "") + doc.format(k=idx) + "\n"
        (OUT / f"{name}.lean").write_text(preamble + header + " := by\n  sorry\n")
        (OUT / "reference" / f"{name}.lean").write_text(preamble + header + " := by" + rest + "\n")
        ctx["seen"][key] = name
        ctx["per_chapter"][chapter] += 1
        ctx["emitted"].append(name)
        declared.update(declared_after)
    return idx


def write_readme(ctx, blocks):
    by_reason = {}
    for label, reason in ctx["skipped"]:
        by_reason.setdefault(re.sub(r"`[^`]*`", "`…`", reason), []).append((label, reason))
    rows = "\n".join(
        f"| {c} | {blocks[c]} | {ctx['per_chapter'][c]} | "
        f"{sum(1 for l, _ in ctx['skipped'] if l.startswith(f'c{c:02d} '))} | "
        f"{sum(1 for l in ctx['beyond'] if l.startswith(f'c{c:02d} '))} |" for c in sorted(blocks))
    skipped = "\n".join(
        f"\n### {group} ({len(items)})\n" + "\n".join(f"- {label}: {reason}" for label, reason in items)
        for group, items in sorted(by_reason.items(), key=lambda kv: -len(kv[1])))
    (OUT / "README.md").write_text(f"""# Mathematics in Lean targets

One `.lean` file per exercise, statement only, proof replaced by `sorry`; the upstream proof
of each sits under `reference/` with the same file name. Generated by `tools/import_mil.py`,
which also writes this README. The well-formedness gate is `.github/workflows/targets.yml`
(Lean `v4.33.1`, mathlib `v4.33.1`, `sorryAx` as the sole hole); a target that fails it is not
a target.

| | |
|---|---|
| Source | [leanprover-community/mathematics_in_lean](https://github.com/{REPO}), commit `{SHA}` (master, {SHA_DATE}) |
| Authors | Jeremy Avigad and Patrick Massot |
| License | Apache-2.0, see `LICENSE` in this directory (the upstream LICENSE and README name no copyright holder). Changes by this repo. |
| Scope | Chapters 2–6 (Basics, Logic, Sets and Functions, Elementary Number Theory, Discrete Mathematics), from `MIL/<chapter>/solutions/Solutions_<section>.lean`; the first {PER_CHAPTER} admissible blocks per chapter in file order. |
| Regenerate | `python3 tools/import_mil.py` (deterministic; pinned commit; files it no longer produces move to `_oneoff/mil_stale/`). |

## Changes from the source (Apache-2.0 §4b)
- Each solution file is split into one file per `example`/`theorem` block, named
  `mil_c<chapter>_s<section>_ex<k>` where `k` counts every `example`/`theorem`/`lemma` block in
  that file (skipped blocks keep their number, so the list below is addressable).
- `import MIL.Common` and the per-file Mathlib imports are replaced by `import Mathlib`
  (`MIL.Common` only imports `Mathlib.Tactic` and `Mathlib.Util.Delaborators` and sets
  `warningAsError false`; it declares nothing).
- `example` becomes `theorem`; original theorem names are dropped in favour of the scheme above.
- `namespace`/`section` wrappers are dropped. Section-level `variable`s that the statement
  mentions (directly or through another included variable's type) are inlined as binders on
  the theorem, in declaration order, keeping their original bracket kind; the rest are omitted.
- `open` lines in scope at the block are carried over verbatim.
- A docstring naming chapter, section, block number, authors, license and commit is added.
- Every proof is replaced by `sorry` in this directory; `reference/` keeps the upstream proof
  verbatim after `:= by`.
- The source pins mathlib `v4.30.0` (`C03_Logic/solutions/Solutions_S02_*.lean` also sets
  `autoImplicit true`, which none of the imported blocks rely on); these files are checked
  against `v4.33.1` with `autoImplicit false`.

## Counts
| chapter | blocks in source | emitted | skipped by rule | beyond the cap of {PER_CHAPTER} |
|---|---|---|---|---|
{rows}
| total | {sum(blocks.values())} | {len(ctx['emitted'])} | {len(ctx['skipped'])} | {len(ctx['beyond'])} |

## Skipped blocks, by reason
A block is skipped when it is not an `example`/`theorem` with a `:= by` proof, references a
`def`/`theorem`/`inductive`/… declared earlier in the same file (namespace-local names
included), needs a section variable its statement does not mention, re-binds a section
variable name inside the statement, repeats an earlier statement, or uses `sorry`.
{skipped}

### Beyond the per-chapter cap ({len(ctx['beyond'])})
Admissible, not emitted: {", ".join(ctx['beyond']) or "none"}.
""")


def main():
    OUT.mkdir(parents=True, exist_ok=True)
    (OUT / "reference").mkdir(exist_ok=True)
    ctx = {"skipped": [], "beyond": [], "emitted": [], "seen": {},
           "per_chapter": {int(c[1:3]): 0 for c in FILES}}
    blocks = {}
    for chapter_dir, sections in FILES.items():
        chapter = int(chapter_dir[1:3])
        for fname in sections:
            src = fetch(f"MIL/{chapter_dir}/solutions/Solutions_{fname}.lean")
            blocks[chapter] = blocks.get(chapter, 0) + process_file(chapter, int(fname[1:3]), fname, src, ctx)
    (OUT / "LICENSE").write_text(fetch("LICENSE"))
    write_readme(ctx, blocks)
    for p in [p for d in (OUT, OUT / "reference") for p in d.glob("*.lean") if p.stem not in ctx["emitted"]]:
        dest = STALE / p.relative_to(OUT)
        dest.parent.mkdir(parents=True, exist_ok=True)
        shutil.move(str(p), str(dest))
        print(f"stale, moved to {dest}")
    for c in sorted(blocks):
        print(f"chapter {c}: {ctx['per_chapter'][c]} emitted of {blocks[c]} blocks")
    print(f"{len(ctx['emitted'])} targets from {REPO}@{SHA[:7]}; "
          f"{len(ctx['skipped'])} skipped by rule, {len(ctx['beyond'])} beyond the cap")
    return len(ctx["emitted"])


if __name__ == "__main__":
    sys.exit(0 if main() else 1)

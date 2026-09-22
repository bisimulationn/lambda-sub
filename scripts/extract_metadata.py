#!/usr/bin/env python3
import argparse
import json
import os
import re
import sys

DECLS = (
    "Lemma",
    "Theorem",
    "Corollary",
    "Proposition",
    "Example",
    "Definition",
    "Fixpoint",
    "Inductive",
)
PAPER = re.compile(r"^(lemma_|theorem_|corollary_|proposition_)")
MILESTONE = {
    "ExecReducer": "M0",
    "Binding": "M1",
    "Reduction": "M1",
    "Metatheory": "M2",
    "Tests": "M2",
}
MILESTONE_ORDER = ["M0", "M1", "M2", "M3", "M4", "M5", "M6"]
PAPER_META = {
    "title": "Milner's Lambda-Calculus with Partial Substitutions",
    "authors": ["Delia Kesner", "Shane Ó Conchúir"],
    "url": "https://arxiv.org/abs/2312.13270",
    "html": "https://arxiv.org/html/2312.13270v1",
}


def split_decls(text):
    pat = re.compile(r"^\s*(" + "|".join(DECLS) + r")\s+([A-Za-z0-9_']+)")
    closer = re.compile(r"\b(Qed|Defined|Admitted)\.\s*$")
    decls = []
    cur = None
    closed = True
    for line in text.splitlines():
        m = pat.match(line)
        if m:
            if cur is not None:
                decls.append(cur)
            cur = {"kind": m.group(1), "name": m.group(2), "lines": [line]}
            closed = False
        elif cur is not None and not closed:
            cur["lines"].append(line)
            if closer.search(line):
                closed = True
    if cur is not None:
        decls.append(cur)
    return decls


def status_of(decl):
    body = "\n".join(decl["lines"])
    if decl["kind"] in ("Definition", "Fixpoint", "Inductive"):
        return "defined"
    if "Admitted" in body or re.search(r"\badmit\b", body):
        return "blocked"
    if re.search(r"\b(Qed|Defined)\.", body):
        return "proved"
    return "stated"


def section_of(name):
    m = re.match(r"^[a-z]+_(\d+)_(\d+)", name)
    if m:
        return m.group(1) + "." + m.group(2)
    m = re.match(r"^[a-z]+_(\d+)$", name)
    if m:
        return m.group(1)
    return ""


def extract(theory_dir):
    nodes = []
    for fname in sorted(os.listdir(theory_dir)):
        if not fname.endswith(".v"):
            continue
        mod = fname[:-2]
        path = os.path.join(theory_dir, fname)
        with open(path, "r", encoding="utf-8") as fh:
            text = fh.read()
        for decl in split_decls(text):
            if decl["kind"] not in ("Lemma", "Theorem", "Corollary", "Proposition"):
                continue
            name = decl["name"]
            nodes.append(
                {
                    "id": name,
                    "label": name,
                    "kind": "paper" if PAPER.match(name) else "infra",
                    "status": status_of(decl),
                    "milestone": MILESTONE.get(mod, "M0"),
                    "section": section_of(name),
                    "file": "theory/" + fname,
                    "depends": [],
                }
            )
    ids = {n["id"] for n in nodes}
    raw = {}
    for fname in sorted(os.listdir(theory_dir)):
        if not fname.endswith(".v"):
            continue
        with open(os.path.join(theory_dir, fname), "r", encoding="utf-8") as fh:
            text = fh.read()
        for decl in split_decls(text):
            if decl["name"] in ids:
                raw[decl["name"]] = "\n".join(decl["lines"])
    for n in nodes:
        body = raw.get(n["id"], "")
        deps = []
        for other in sorted(ids):
            if other == n["id"]:
                continue
            if re.search(r"\b" + re.escape(other) + r"\b", body):
                deps.append(other)
        n["depends"] = deps
    milestones = [m for m in MILESTONE_ORDER if any(n["milestone"] == m for n in nodes)]
    return {
        "paper": PAPER_META,
        "milestones": milestones,
        "current": milestones[-1] if milestones else "M0",
        "nodes": nodes,
    }


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--theory", default="theory")
    ap.add_argument("--out", default="graphs/theorems.json")
    args = ap.parse_args()
    data = extract(args.theory)
    outdir = os.path.dirname(args.out)
    if outdir:
        os.makedirs(outdir, exist_ok=True)
    with open(args.out, "w", encoding="utf-8") as fh:
        json.dump(data, fh, ensure_ascii=False, indent=2)
        fh.write("\n")
    print("wrote", args.out, "with", len(data["nodes"]), "nodes")
    return 0


if __name__ == "__main__":
    sys.exit(main())

#!/usr/bin/env python3
import importlib.util
import json
import os
import subprocess
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
GRAPH_DIR = os.path.join(ROOT, "graphs")
META = os.path.join(GRAPH_DIR, "theorems.json")

INK = "#000000"
MUTED = "#000000"
FONT = "#000000"
FILL = "#ffffff"
EXT_FILL = "#ffffff"
NF_FILL = "#ffffff"

RULE_B = "#000000"
RULE_R = "#000000"
RULE_G = "#000000"


def q(s):
    return '"' + str(s).replace("\\", "\\\\").replace('"', '\\"') + '"'


def load(path):
    with open(path, "r", encoding="utf-8") as f:
        return json.load(f)


def esc_html(s):
    return str(s).replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;")


def node_line(n, external=False):
    if external:
        label = n["id"] + "\\n(" + n["milestone"] + ")"
        shape = "box"
        style = "rounded,dashed,filled"
        fill = EXT_FILL
        color = MUTED
        fontcolor = FONT
        pen = 0.9
    else:
        label = n["id"]
        shape = "box" if n["kind"] == "paper" else "ellipse"
        style = "rounded,filled" if n["kind"] == "paper" else "filled"
        fill = FILL
        color = INK
        fontcolor = FONT
        pen = 1.0
    tip = n["id"]
    if n.get("section"):
        tip += " (section " + n["section"] + ")"
    if n.get("file"):
        tip += " " + n["file"]
    tip += " " + n["status"]
    return (
        "  %s [label=%s, shape=%s, style=%s, fillcolor=%s, color=%s, "
        "penwidth=%.1f, fontcolor=%s, tooltip=%s];"
        % (n["id"], q(label), shape, q(style), q(fill), q(color), pen, q(fontcolor), q(tip))
    )


def dep_header(title):
    return [
        "digraph deps {",
        "  rankdir=LR;",
        '  bgcolor="#ffffff";',
        "  splines=polyline;",
        "  concentrate=true;",
        "  nodesep=0.2;",
        "  ranksep=0.9;",
        '  node [fontname=Inter, fontsize=9];',
        '  edge [fontname=Inter, fontsize=8, color="%s", fontcolor="%s", arrowsize=0.6, penwidth=0.8];' % (MUTED, FONT),
        '  graph [fontname=Inter, fontsize=12, labelloc=t, fontcolor="%s", label=<<B>%s</B>>];' % (FONT, esc_html(title)),
    ]


def dependency_overview_dot(data):
    by_id = {n["id"]: n for n in data["nodes"]}
    counts = {}
    for n in data["nodes"]:
        counts[n["milestone"]] = counts.get(n["milestone"], 0) + 1
    milestones = [m for m in data["milestones"] if counts.get(m)]
    edges = set()
    for n in data["nodes"]:
        for d in n["depends"]:
            if d in by_id:
                a = by_id[d]["milestone"]
                b = n["milestone"]
                if a != b and a in counts and b in counts:
                    edges.add((a, b))
    lines = dep_header("Theorem dependency by milestone")
    for m in milestones:
        label = "%s\\n%d results" % (m, counts[m])
        lines.append(
            '  %s [label=%s, shape=box, style="rounded,filled", fillcolor=%s, '
            "color=%s, fontcolor=%s];" % (m, q(label), q(FILL), q(INK), q(FONT))
        )
    for a, b in sorted(edges):
        lines.append("  %s -> %s;" % (a, b))
    lines.append("}")
    return "\n".join(lines) + "\n"


def dependency_subset_dot(data, title, keep_ids):
    by_id = {n["id"]: n for n in data["nodes"]}
    inside = [n for n in data["nodes"] if n["id"] in keep_ids]
    ids = {n["id"] for n in inside}
    ext_ids = sorted(
        {d for n in inside for d in n["depends"] if d not in ids and d in by_id}
    )
    lines = dep_header(title)
    for d in ext_ids:
        lines.append(node_line(by_id[d], external=True))
    for n in sorted(inside, key=lambda x: (x["file"], x["id"])):
        lines.append(node_line(n))
    keep = ids | set(ext_ids)
    for n in inside:
        for d in n["depends"]:
            if d in keep:
                lines.append("  %s -> %s;" % (d, n["id"]))
    lines.append("}")
    return "\n".join(lines) + "\n"


def rules_dot():
    box = 'shape=box, style="rounded,filled", fillcolor="%s", color="%s", fontcolor="%s"' % (FILL, INK, FONT)
    lines = [
        "digraph lambda_sub_cfg {",
        "  rankdir=TB;",
        '  bgcolor="#ffffff";',
        '  node [fontname=Inter, fontsize=10, fontcolor="%s"];' % FONT,
        '  edge [fontname=Inter, fontsize=9, color="%s", fontcolor="%s"];' % (MUTED, FONT),
        '  start [label="term", shape=oval, style=filled, fillcolor="%s", color="%s"];' % (FILL, INK),
        "  beta [label=\"(lambda x. t) u\", %s];" % box,
        "  es [label=\"t[x/u]\", %s];" % box,
        '  pure [label="pure term", shape=oval, style=filled, fillcolor="%s", color="%s"];' % (FILL, INK),
        '  nf [label="normal form", shape=doublecircle, style=filled, fillcolor="%s", color="%s"];' % (NF_FILL, RULE_G),
        '  start -> beta [label="App(Lam,_)"];',
        '  start -> es [label="ESub"];',
        '  start -> pure [label="BVar/FVar/Lam"];',
        '  beta -> es [label="B", color="%s"];' % RULE_B,
        '  es -> es [label="R (one occurrence)", color="%s"];' % RULE_R,
        '  es -> pure [label="Gc (x not in fv)", color="%s"];' % RULE_G,
        '  pure -> pure [label="B under context", color="%s"];' % RULE_B,
        '  es -> nf [label="R/Gc normalisation", color="%s"];' % RULE_R,
        "}",
    ]
    return "\n".join(lines) + "\n"


def reduction_dot():
    box = 'shape=box, style="filled", fillcolor="%s", color="%s", fontcolor="%s"' % (FILL, INK, FONT)
    lines = [
        "digraph reduction_dup {",
        "  rankdir=LR;",
        '  bgcolor="#ffffff";',
        '  node [fontname=Inter, fontsize=10, fontcolor="%s"];' % FONT,
        '  edge [fontname=Inter, fontsize=9, color="%s", fontcolor="%s"];' % (MUTED, FONT),
        '  graph [labelloc=t, fontcolor="%s", label="(lambda x. x x) y reduction graph"];' % FONT,
        "  n0 [label=\"(lambda x. x x) y\", %s];" % box,
        "  n1 [label=\"(x x)[x/y]\", %s];" % box,
        "  n2 [label=\"(y x)[x/y]\", %s];" % box,
        "  n2b [label=\"(x y)[x/y]\", %s];" % box,
        "  n3 [label=\"(y y)[x/y]\", %s];" % box,
        '  nf [label="y y (normal form)", shape=doublecircle, style=filled, fillcolor="%s", color="%s", fontcolor="%s"];' % (NF_FILL, RULE_G, FONT),
        '  n0 -> n1 [label="B", color="%s"];' % RULE_B,
        '  n1 -> n2 [label="R", color="%s"];' % RULE_R,
        '  n1 -> n2b [label="R", color="%s"];' % RULE_R,
        '  n2 -> n3 [label="R", color="%s"];' % RULE_R,
        '  n2b -> n3 [label="R", color="%s"];' % RULE_R,
        '  n3 -> nf [label="Gc", color="%s"];' % RULE_G,
        "  {rank=same; n2; n2b;}",
        "}",
    ]
    return "\n".join(lines) + "\n"


def run_dot(path):
    svg = path[:-4] + ".svg"
    png = path[:-4] + ".png"
    ok = True
    for fmt, out in (("svg", svg), ("png", png)):
        r = subprocess.run(["dot", "-T" + fmt, path, "-o", out], capture_output=True, text=True)
        if r.returncode != 0:
            print(r.stderr, file=sys.stderr)
            ok = False
        else:
            print("wrote", os.path.relpath(out, ROOT))
    return ok


def main():
    import argparse
    ap = argparse.ArgumentParser()
    ap.add_argument("--outdir", default=GRAPH_DIR)
    ap.add_argument("--meta", default=os.path.join(GRAPH_DIR, "theorems.json"))
    ap.add_argument("--theory", default=None)
    args = ap.parse_args()
    os.makedirs(args.outdir, exist_ok=True)
    if args.theory:
        spec = importlib.util.spec_from_file_location(
            "extract_metadata",
            os.path.join(ROOT, "scripts", "extract_metadata.py"),
        )
        extract = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(extract)
        data = extract.extract(args.theory)
        with open(args.meta, "w", encoding="utf-8") as fh:
            json.dump(data, fh, ensure_ascii=False, indent=2)
            fh.write("\n")
        print("wrote", os.path.relpath(args.meta, ROOT))
    else:
        data = load(args.meta)

    counts = {}
    for n in data["nodes"]:
        counts[n["milestone"]] = counts.get(n["milestone"], 0) + 1

    outputs = {"dependency-overview.dot": dependency_overview_dot(data)}
    for m in data["milestones"]:
        if not counts.get(m):
            continue
        keep = {n["id"] for n in data["nodes"] if n["milestone"] == m}
        title = "Theorem dependencies %s, %d results" % (m, counts[m])
        outputs["dependency-%s.dot" % m] = dependency_subset_dot(data, title, keep)

    outputs["rules.dot"] = rules_dot()
    outputs["reduction.dot"] = reduction_dot()

    ok = True
    for name, text in outputs.items():
        path = os.path.join(args.outdir, name)
        with open(path, "w", encoding="utf-8") as f:
            f.write(text)
        print("wrote", os.path.relpath(path, ROOT))
        if not run_dot(path):
            ok = False
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())

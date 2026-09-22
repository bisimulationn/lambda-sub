#!/usr/bin/env python3
import json
import os
import subprocess
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
GRAPH_DIR = os.path.join(ROOT, "graphs")
META = os.path.join(GRAPH_DIR, "theorems.json")

STATUS_FILL = {
    "proved": "#d9ead3",
    "stated": "#fff2cc",
    "planned": "#f3f3f3",
    "blocked": "#f4cccc",
}
STATUS_PEN = {
    "proved": "#38761d",
    "stated": "#b45f06",
    "planned": "#777777",
    "blocked": "#cc0000",
}
STATUS_STYLE = {
    "proved": "filled",
    "stated": "filled,dashed",
    "planned": "dashed",
    "blocked": "filled,bold",
}
INK = "#333333"
RULE_B = "#990000"
RULE_R = "#674ea7"
RULE_G = "#38761d"


def q(s):
    return '"' + str(s).replace("\\", "\\\\").replace('"', '\\"') + '"'


def load():
    with open(META, "r", encoding="utf-8") as f:
        return json.load(f)


def dependency_dot(data):
    nodes = data["nodes"]
    by_id = {n["id"]: n for n in nodes}
    title = data["paper"]["title"] + " - theorem dependency (" + data["current"] + ")"
    lines = [
        "digraph theorem_deps {",
        "  rankdir=LR;",
        "  bgcolor=\"white\";",
        "  node [fontname=Inter, fontsize=10, fontcolor=\"%s\"];" % INK,
        "  edge [fontname=Inter, fontsize=8, color=\"%s\"];" % INK,
        "  graph [fontname=Inter, fontsize=12, labelloc=t, label=%s];" % q(title),
    ]
    for ms in data["milestones"]:
        members = [n for n in nodes if n["milestone"] == ms]
        if not members:
            continue
        lines.append("  subgraph cluster_%s {" % ms)
        lines.append("    label=%s;" % q(ms))
        lines.append("    style=\"rounded\";")
        lines.append("    color=\"#bbbbbb\";")
        lines.append("    fontcolor=\"%s\";" % INK)
        for n in members:
            fill = STATUS_FILL.get(n["status"], "#f3f3f3")
            pen = STATUS_PEN.get(n["status"], "#777777")
            style = STATUS_STYLE.get(n["status"], "dashed")
            tip = n["id"]
            if n.get("section"):
                tip += " (section " + n["section"] + ")"
            if n.get("file"):
                tip += " " + n["file"]
            tip += " " + data["paper"]["html"]
            attrs = [
                "label=%s" % q(n["label"]),
                "color=%s" % q(pen),
                "fillcolor=%s" % q(fill),
                "style=%s" % q(style),
                "fontcolor=%s" % q(INK),
                "tooltip=%s" % q(tip),
                "shape=%s" % ("box" if n["kind"] == "paper" else "ellipse"),
            ]
            lines.append("    %s [%s];" % (n["id"], ", ".join(attrs)))
        lines.append("  }")
    for n in nodes:
        for d in n.get("depends", []):
            if d in by_id:
                lines.append("  %s -> %s;" % (d, n["id"]))
    lines.append("}")
    return "\n".join(lines) + "\n"


def rules_dot():
    box = 'shape=box, style="rounded,filled", fillcolor="#f5f5f5", color="%s", fontcolor="%s"' % (INK, INK)
    lines = [
        "digraph lambda_sub_cfg {",
        "  rankdir=TB;",
        "  bgcolor=\"white\";",
        "  node [fontname=Inter, fontsize=10];",
        "  edge [fontname=Inter, fontsize=9, color=\"%s\"];" % INK,
        "  start [label=\"term\", shape=oval, style=filled, fillcolor=\"#f3f3f3\", color=\"%s\"];" % INK,
        "  beta [label=\"(lambda x. t) u\", %s];" % box,
        "  es [label=\"t[x/u]\", %s];" % box,
        "  pure [label=\"pure term\", shape=oval, style=filled, fillcolor=\"#f3f3f3\", color=\"%s\"];" % INK,
        "  nf [label=\"normal form\", shape=doublecircle, style=filled, fillcolor=\"#d9ead3\", color=\"%s\"];" % RULE_G,
        "  start -> beta [label=\"App(Lam,_)\"];",
        "  start -> es [label=\"ESub\"];",
        "  start -> pure [label=\"BVar/FVar/Lam\"];",
        "  beta -> es [label=\"B\", color=\"%s\"];" % RULE_B,
        "  es -> es [label=\"R (one occurrence)\", color=\"%s\"];" % RULE_R,
        "  es -> pure [label=\"Gc (x not in fv)\", color=\"%s\"];" % RULE_G,
        "  pure -> pure [label=\"B under context\", color=\"%s\"];" % RULE_B,
        "  es -> nf [label=\"R/Gc normalisation\", color=\"%s\"];" % RULE_R,
        "}",
    ]
    return "\n".join(lines) + "\n"


def reduction_dot():
    box = 'shape=box, style="filled", fillcolor="#f5f5f5", color="%s", fontcolor="%s"' % (INK, INK)
    lines = [
        "digraph reduction_dup {",
        "  rankdir=LR;",
        "  bgcolor=\"white\";",
        "  node [fontname=Inter, fontsize=10];",
        "  edge [fontname=Inter, fontsize=9, color=\"%s\"];" % INK,
        "  graph [labelloc=t, fontcolor=\"%s\", label=\"(lambda x. x x) y reduction graph\"];" % INK,
        "  n0 [label=\"(lambda x. x x) y\", %s];" % box,
        "  n1 [label=\"(x x)[x/y]\", %s];" % box,
        "  n2 [label=\"(y x)[x/y]\", %s];" % box,
        "  n2b [label=\"(x y)[x/y]\", %s];" % box,
        "  n3 [label=\"(y y)[x/y]\", %s];" % box,
        "  nf [label=\"y y (normal form)\", shape=doublecircle, style=filled, fillcolor=\"#d9ead3\", color=\"%s\", fontcolor=\"%s\"];" % (RULE_G, INK),
        "  n0 -> n1 [label=\"B\", color=\"%s\"];" % RULE_B,
        "  n1 -> n2 [label=\"R\", color=\"%s\"];" % RULE_R,
        "  n1 -> n2b [label=\"R\", color=\"%s\"];" % RULE_R,
        "  n2 -> n3 [label=\"R\", color=\"%s\"];" % RULE_R,
        "  n2b -> n3 [label=\"R\", color=\"%s\"];" % RULE_R,
        "  n3 -> nf [label=\"Gc\", color=\"%s\"];" % RULE_G,
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
    data = load()
    outputs = {
        "dependency.dot": dependency_dot(data),
        "rules.dot": rules_dot(),
        "reduction.dot": reduction_dot(),
    }
    ok = True
    for name, text in outputs.items():
        p = os.path.join(GRAPH_DIR, name)
        with open(p, "w", encoding="utf-8") as f:
            f.write(text)
        print("wrote", os.path.relpath(p, ROOT))
        if not run_dot(p):
            ok = False
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())

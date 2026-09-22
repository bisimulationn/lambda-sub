#!/usr/bin/env python3
import importlib.util
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


def load(path):
    with open(path, "r", encoding="utf-8") as f:
        return json.load(f)


def esc_html(s):
    return str(s).replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;")


def dependency_dot(data):
    nodes = data["nodes"]
    by_id = {n["id"]: n for n in nodes}
    title = data["paper"]["title"] + " - theorem dependency (" + data["current"] + ")"
    legend = (
        "<B>" + esc_html(title) + "</B>"
        "<BR/><FONT POINT-SIZE=\"9\">"
        "<FONT COLOR=\"#38761d\">proved</FONT>   "
        "<FONT COLOR=\"#b45f06\">stated</FONT>   "
        "<FONT COLOR=\"#777777\">planned</FONT>   "
        "<FONT COLOR=\"#cc0000\">blocked</FONT>"
        "</FONT>"
    )
    lines = [
        "digraph theorem_deps {",
        "  rankdir=LR;",
        '  bgcolor="white";',
        "  splines=spline;",
        "  nodesep=0.22;",
        "  ranksep=0.6;",
        '  node [fontname=Inter, fontsize=9, fontcolor="#222222"];',
        '  edge [fontname=Inter, fontsize=8, color="#9a9a9a", arrowsize=0.6, penwidth=0.8];',
        "  graph [fontname=Inter, fontsize=12, labelloc=t, label=<%s>];" % legend,
    ]
    for n in nodes:
        fill = STATUS_FILL.get(n["status"], "#f3f3f3")
        pen = STATUS_PEN.get(n["status"], "#777777")
        style = STATUS_STYLE.get(n["status"], "dashed")
        tip = n["id"]
        if n.get("section"):
            tip += " (section " + n["section"] + ")"
        if n.get("file"):
            tip += " " + n["file"]
        tip += " " + data["paper"]["html"]
        if n["kind"] == "paper":
            shape = "box"
            style = "rounded," + style
        else:
            shape = "ellipse"
        attrs = [
            "label=%s" % q(n["label"]),
            "color=%s" % q(pen),
            "fillcolor=%s" % q(fill),
            "style=%s" % q(style),
            "fontcolor=%s" % q("#222222"),
            "tooltip=%s" % q(tip),
            "shape=%s" % shape,
        ]
        lines.append("  %s [%s];" % (n["id"], ", ".join(attrs)))
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
    outputs = {
        "dependency.dot": dependency_dot(data),
        "rules.dot": rules_dot(),
        "reduction.dot": reduction_dot(),
    }
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

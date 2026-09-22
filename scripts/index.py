#!/usr/bin/env python3
import json
import os
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
META = os.path.join(ROOT, "graphs", "theorems.json")
OUT = os.path.join(ROOT, "graphs", "index.txt")


def main():
    with open(META, "r", encoding="utf-8") as fh:
        data = json.load(fh)
    rows = []
    for n in sorted(data["nodes"], key=lambda x: (x["milestone"], x["id"])):
        rows.append(
            "\t".join([n["status"], n["milestone"], n["kind"], n["id"], n["file"]])
        )
    header = "\t".join(["status", "milestone", "kind", "name", "file"])
    with open(OUT, "w", encoding="utf-8") as fh:
        fh.write(header + "\n")
        fh.write("\n".join(rows) + "\n")
    print("wrote", os.path.relpath(OUT, ROOT), "with", len(rows), "results")
    return 0


if __name__ == "__main__":
    sys.exit(main())

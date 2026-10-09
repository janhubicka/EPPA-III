"""Fail the audit if a listed declaration is missing or uses a nonstandard axiom.

This is adapted from partite-construction/scripts/check_axioms.py.
"""
import pathlib
import re
import sys

text = pathlib.Path(sys.argv[1]).read_text()
sources = sys.argv[2:] or ["CheckAxioms.lean"]
expected = set()
for source in sources:
    expected.update(re.findall(r"^#print axioms (\S+)", pathlib.Path(source).read_text(), re.M))
found = {}
for name, axioms in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", text):
    found[name] = {a.strip() for a in axioms.split(",") if a.strip()}
for name in re.findall(r"'([^']+)' does not depend on any axioms", text):
    found[name] = set()
assert set(found) == expected, f"Missing or unexpected audit results: {expected ^ set(found)}"
allowed = {"propext", "Classical.choice", "Quot.sound"}
for name, axioms in found.items():
    assert axioms <= allowed, f"Unexpected axioms in {name}: {axioms - allowed}"
print(f"Checked {len(found)} declarations; only standard logical axioms occur.")

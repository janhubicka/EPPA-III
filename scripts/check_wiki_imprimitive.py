#!/usr/bin/env python3
"""Check that the EPPA III wiki's verbatim Lean excerpts match this checkout.

This is an exact-source documentation integrity check, not a Lean proof checker.
The regular Lean GitHub Actions workflow does the kernel/axiom checks.
"""
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
MAIN = ROOT / "docs/wiki/Imprimitive-Classification.md"
GARDINER = ROOT / "docs/wiki/Gardiner-External-Assumption.md"
MODELS = ROOT / "docs/wiki/Named-Host-Models.md"

MAIN_DECLS = [
    ("EPPAIII/EPPA/Definitions.lean", "def", "IsGraphAutomorphism"),
    ("EPPAIII/EPPA/Definitions.lean", "def", "IsPartialGraphAutomorphism"),
    ("EPPAIII/EPPA/Definitions.lean", "def", "IsInducedGraphEmbedding"),
    ("EPPAIII/EPPA/Definitions.lean", "def", "IsEPPAEmbedding"),
    ("EPPAIII/DoubleCover/RigidLayerHomogeneity.lean", "def", "IsHomogeneousGraph"),
    ("EPPAIII/BlockSystems/TransitivePartition.lean", "def", "IsVertexTransitive"),
    ("EPPAIII/BlockSystems/Basic.lean", "def", "InvariantBlockMap"),
    ("EPPAIII/BlockSystems/ClusterObstructions.lean", "def", "IsClusterGraph"),
    ("EPPAIII/BlockSystems/ClusterObstructions.lean", "def", "IsCoClusterGraph"),
    ("EPPAIII/BlockSystems/ImprimitiveProposition617.lean", "def", "CanonicalBaseCopy"),
    ("EPPAIII/CliqueCovers/Basic.lean", "inductive", "CrossType"),
    ("EPPAIII/CliqueCovers/Basic.lean", "abbrev", "CoverVertex"),
    ("EPPAIII/CliqueCovers/Basic.lean", "def", "coverAdj"),
    ("EPPAIII/CliqueCovers/Basic.lean", "def", "cliqueUnion"),
    ("EPPAIII/CliqueCovers/Basic.lean", "def", "coverGraph"),
    ("EPPAIII/BlockSystems/ImprimitiveProposition617.lean", "def", "EqualCliqueHostModels"),
    ("EPPAIII/BlockSystems/CycleFiveSmallCrossConclusion.lean", "def", "CycleFiveSmallHostPatterns"),
    ("EPPAIII/BlockSystems/RookThreeFinalImprimitiveClassification.lean", "def", "RookSmallHostPatterns"),
    ("EPPAIII/BlockSystems/ImprimitiveProposition617.lean", "def", "ImprimitiveHostModels"),
    ("EPPAIII/BlockSystems/ImprimitiveGlobalClassification.lean", "def", "GeneralImprimitiveHostModels"),
    ("EPPAIII/BlockSystems/GardinerLiteralNormalization.lean", "def", "GardinerPublishedModels"),
]

GARDINER_DECLS = [
    ("EPPAIII/BlockSystems/ImprimitiveProposition617.lean", "def", "CanonicalBaseCopy"),
    ("EPPAIII/BlockSystems/GardinerLiteralNormalization.lean", "def", "GardinerPublishedModels"),
    ("EPPAIII/BlockSystems/ImprimitiveGardinerBridge.lean", "def", "GardinerHomogeneousModels"),
    ("EPPAIII/BlockSystems/GardinerLiteralNormalization.lean", "theorem", "gardiner_complement_cycle_normalized"),
    ("EPPAIII/BlockSystems/GardinerLiteralNormalization.lean", "theorem", "gardiner_complement_rook_normalized"),
    ("EPPAIII/BlockSystems/GardinerLiteralNormalization.lean", "theorem", "gardiner_published_implies_normalized"),
    ("EPPAIII/BlockSystems/ImprimitiveProposition617.lean", "def", "ImprimitiveBaseModels"),
    ("EPPAIII/BlockSystems/ClusterRegularHomogeneity.lean", "theorem", "cluster_homogeneous_or_unequal_degrees"),
    ("EPPAIII/BlockSystems/ImprimitiveGardinerBridge.lean", "theorem", "imprimitive_base_models_from_gardiner"),
    ("EPPAIII/BlockSystems/GardinerLiteralNormalization.lean", "theorem", "imprimitive_actual_host_classification_from_published_gardiner"),
]

MODEL_DECLS = [
    ("EPPAIII/DoubleCover/PairPatterns.lean", "structure", "PairPattern"),
    ("EPPAIII/DoubleCover/PairPatterns.lean", "def", "taylor"),
    ("EPPAIII/DoubleCover/UniformPattern.lean", "def", "RepresentsPairPattern"),
    ("EPPAIII/BlockSystems/TwoCliqueSwitching.lean", "def", "twoCliqueGraph"),
    ("EPPAIII/BlockSystems/TwoCliqueTaylorNamed.lean", "def", "twoCliqueMatchedRel"),
    ("EPPAIII/BlockSystems/TwoCliqueTaylorNamed.lean", "def", "twoCliqueMatchedGraph"),
    ("EPPAIII/BlockSystems/CycleFiveDoubleClassification.lean", "def", "cycleFiveExplicitAdjacent"),
    ("EPPAIII/BlockSystems/CycleFiveDoubleClassification.lean", "def", "cycleFiveDoubleRelation"),
    ("EPPAIII/BlockSystems/CycleFiveDoubleClassification.lean", "def", "cycleFiveDoubleGraph"),
    ("EPPAIII/BlockSystems/CycleFiveZeroCrossConclusion.lean", "def", "cycleFiveDisjointDoubleGraph"),
    ("EPPAIII/BlockSystems/CycleFiveMatchingModels.lean", "def", "cycleFiveMatchingRelation"),
    ("EPPAIII/BlockSystems/CycleFiveMatchingModels.lean", "def", "cycleFiveMatchingGraph"),
    ("EPPAIII/BlockSystems/RookThreeBase.lean", "def", "rookThreeGraph"),
    ("EPPAIII/BlockSystems/RookThreeTriangleCertificates.lean", "abbrev", "rookDoubleRelation"),
    ("EPPAIII/BlockSystems/RookThreeTriangleCertificates.lean", "def", "rookDoubleGraph"),
    ("EPPAIII/CliqueCovers/WagnerHostConclusion.lean", "def", "wagnerCanonicalGraph"),
]

NEXT_DECL = re.compile(
    r"\n\n(?:/--|theorem\s|lemma\s|def\s|abbrev\s|"
    r"inductive\s|structure\s|end\s|namespace\s)"
)

def get_decl(path: str, kind: str, name: str) -> str:
    text = (ROOT / path).read_text(encoding="utf8")
    m = re.search(r"^" + re.escape(kind) + r"\s+" + re.escape(name) +
                  r"(?=\s|\{|\()", text, re.MULTILINE)
    if m is None:
        raise AssertionError(f"Declaration missing: {path} :: {name}")
    start = m.start()
    next_decl = NEXT_DECL.search(text, start + 1)
    end = next_decl.start() if next_decl else len(text)
    return text[start:end].rstrip()

def check_page(path: Path, entries: list[tuple[str, str, str]]) -> int:
    doc = path.read_text(encoding="utf8")
    if doc.count("```") % 2:
        raise AssertionError(f"Unbalanced Markdown fences: {path}")
    for src, kind, name in entries:
        exact = "```lean\n" + get_decl(src, kind, name) + "\n```"
        if exact not in doc:
            raise AssertionError(f"Stale or missing verbatim source in {path}: {src} :: {name}")
    print(f"OK {path.relative_to(ROOT)}: {len(entries)} exact Lean snippets")
    return len(entries)

def main() -> None:
    checked = check_page(MAIN, MAIN_DECLS)
    checked += check_page(GARDINER, GARDINER_DECLS)
    checked += check_page(MODELS, MODEL_DECLS)
    src = (ROOT / "EPPAIII/BlockSystems/ImprimitiveGlobalClassification.lean").read_text(encoding="utf8")
    doc = MAIN.read_text(encoding="utf8")
    if "```lean\n" + src.rstrip() + "\n```" not in doc:
        raise AssertionError("The complete main theorem module is out of date")
    if "hGardinerComplement" in src:
        raise AssertionError("Global theorem acquired an extra Gardiner premise; audit wiki")
    if not re.search(r"hGardinerG\s*:\s*DoubleCover\.IsHomogeneousGraph G\s*→\s*GardinerPublishedModels G", src):
        raise AssertionError("The documented single-G Gardiner premise changed")
    if not (ROOT / "docs/wiki/README.md").is_file():
        raise AssertionError("Missing wiki Home source")
    if not (ROOT / "docs/wiki/_Sidebar.md").is_file():
        raise AssertionError("Missing wiki sidebar source")
    print(f"OK complete global theorem source; {checked} checked source excerpts")

if __name__ == "__main__":
    try:
        main()
    except (AssertionError, OSError) as error:
        print(f"WIKI SOURCE AUDIT FAILED: {error}", file=sys.stderr)
        sys.exit(1)

#!/usr/bin/env python3
"""Local type-match gate for the uniformity nodes.

Writes, for each theorem payload, the target statement exactly as it will be
submitted and a file asserting that `solution` inhabits that same type.  A
mismatch is then a local compile error rather than a `WA` from the server.
"""

import json
import pathlib

ROOT = pathlib.Path(__file__).resolve().parent.parent
THMS = json.load(
    open(ROOT / "build" / "payloads" / "payload_thms_uniformity.json",
         encoding="utf-8"))

SOLUTIONS = {
    "TranscendenceTower.UniformityPlatform.uniformity_monotone_dichotomy":
        "Sol_uniformity_monotone_dichotomy",
    "TranscendenceTower.UniformityPlatform.uniformity_rigidity":
        "Sol_uniformity_rigidity",
    "TranscendenceTower.UniformityPlatform.uniformity_trichotomy":
        "Sol_uniformity_trichotomy",
}

for i, thm in enumerate(THMS):
    tag = "U%d" % i
    name = thm["theorem_name"]
    (ROOT / "Development" / ("Gate%s.lean" % tag)).write_text(
        thm["preamble"] + "\n\n" + thm["formal_statement"], encoding="utf-8")
    (ROOT / "Development" / ("Gate%sMatch.lean" % tag)).write_text(
        "import Development.Gate%s\n" % tag
        + "import Solutions.%s\n\n" % SOLUTIONS[name]
        + "set_option autoImplicit false\n\n"
        + "theorem gate_%s (A C : Type) :\n" % tag
        + "    %s A C = solution A C := rfl\n" % name,
        encoding="utf-8")
    print("gate", tag, name)

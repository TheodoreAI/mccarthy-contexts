#!/usr/bin/env python3
"""Assemble platform-shaped solution files for the uniformity nodes.

Each solution imports the published definition bundle and carries the proof
lemmas verbatim from the Development sources, with the definitions -- which
now come from the import -- removed.  Generating rather than hand-copying
keeps the submitted proofs identical to what the repository builds.
"""
import pathlib
import re

ROOT = pathlib.Path(__file__).resolve().parent.parent
DEV = ROOT / "Development"
NS_OLD = "TranscendenceTower.Uniformity"
NS_NEW = "TranscendenceTower.UniformityPlatform"

# Names supplied by Definitions/Def_TranscendenceTowerContextUniformity.lean.
DEFS = {
    "CForm", "atom", "tru", "neg", "neg_lit", "neg_neg_lit", "CVal", "eval",
    "eval_tru", "eval_lit", "eval_neg", "cval_ext", "Models", "Cn",
    "Consistent", "subset_Cn", "IsBase", "subst", "pullback", "boolSubst",
    "PropUniform", "copySchema", "canon", "canonVal",
    "Rule", "fired", "stage", "IsExtension", "LogAut", "pre", "mem_pre",
    "mapRule", "symmRule", "preRules", "shift", "shift_neg",
    "shift_symm_shift", "shift_shift_symm", "shiftEquiv", "shiftVal",
    "eval_shift", "shiftVal_symm_shiftVal", "shiftVal_shiftVal_symm",
    "shiftValEquiv", "shiftAut", "copyRules", "Monotone",
    "autForm", "invEps", "autForm_symm_autForm", "autForm_autForm_symm",
    "autFormEquiv", "autForm_neg", "autVal", "eval_autForm",
    "autVal_symm_autVal", "autVal_autVal_symm", "autValEquiv", "autAut",
    "AutL", "autSubst", "substRule", "PropUniformRules", "SymmetricUnder",
    "xor_cancel", "xor_cancel_left", "xor_assoc",
}

DECL = re.compile(
    r"^(?:@\[[^\]]*\]\s*)?(?:noncomputable\s+)?(?:def|theorem|structure|inductive)\s+"
    r"([A-Za-z_][A-Za-z0-9_.]*)")

STRUCT = ("namespace ", "end ", "section", "variable", "open ", "set_option ",
          "import ", "/-!", "#print")


def is_break(line):
    if DECL.match(line) or line.startswith("/--"):
        return True
    return any(line.startswith(s) for s in STRUCT) or line.rstrip() == "/-"


def strip_defs(path):
    text = path.read_text(encoding="utf-8")
    lo = text.index("namespace " + NS_OLD) + len("namespace " + NS_OLD)
    hi = text.rindex("end " + NS_OLD)
    lines = text[lo:hi].split("\n")

    out = []
    i = 0
    while i < len(lines):
        line = lines[i]
        doc_start = i
        if line.startswith("/--"):
            j = i
            while j < len(lines) and "-/" not in lines[j]:
                j += 1
            head = j + 1
        else:
            head = i
        m = DECL.match(lines[head]) if head < len(lines) else None
        if m:
            k = head + 1
            while k < len(lines) and not is_break(lines[k]):
                k += 1
            if m.group(1).rstrip("'") not in DEFS:
                out.extend(lines[doc_start:k])
            i = k
            continue
        if line.startswith("#print"):
            i += 1
            continue
        out.append(line)
        i += 1
    return "\n".join(out)


def body(names):
    chunks = []
    for name in names:
        kept = [line for line in strip_defs(DEV / name).split("\n")
                if not line.startswith("variable {A C : Type}")]
        chunks.append("\n".join(kept))
    return "\n".join(chunks).replace(NS_OLD, NS_NEW)


HEADER = """import Definitions.Def_TranscendenceTowerContextUniformity

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace {ns}

variable {{A C : Type}}
""".format(ns=NS_NEW)

FOOTER = "\nend {ns}\n\nopen {ns}\n\n".format(ns=NS_NEW)

DICHOTOMY = """theorem solution (A C : Type) :
    (∀ T Γ : Set (CForm A C), (∀ p ∈ T, IsBase p) → PropUniform Γ →
        Consistent (T ∪ Γ) →
        ∀ φ : CForm A C, IsBase φ → φ ∈ Cn (T ∪ Γ) → φ ∈ Cn T)
    ∧ (∀ T Γ : Set (CForm A C), (∀ p ∈ T, IsBase p) → PropUniform Γ →
        Consistent (T ∪ Γ) →
        {φ : CForm A C | IsBase φ ∧ φ ∈ Cn (T ∪ Γ)}
          = {φ : CForm A C | IsBase φ ∧ φ ∈ Cn T})
    ∧ PropUniform (copySchema A C)
    ∧ (∀ atomv : A → Bool, Models (copySchema A C) (canonVal atomv)) := by
  exact ⟨fun _ _ hT hU hcon => monotone_dichotomy hT hU hcon,
         fun _ _ hT hU hcon => conservative hT hU hcon,
         copySchema_propUniform,
         copySchema_consistent⟩
"""

RIGIDITY = """theorem solution (A C : Type) :
    (∀ (oc : C ≃ C) (T : Set (CForm A C)) (S : Set (Rule A C))
        (E : Set (CForm A C)),
        (∀ p ∈ T, IsBase p) →
        (shiftAut (A := A) oc).preRules S = S →
        IsExtension T S E → Consistent E →
        (∀ E', IsExtension T S E' → Consistent E' → E' = E) →
        (shiftAut (A := A) oc).pre E = E)
    ∧ (∀ (oc : C ≃ C) (E : Set (CForm A C)),
        (shiftAut (A := A) oc).pre E = E →
        ∀ (c : C) (φ : CForm A C),
          (CForm.ist c φ ∈ E ↔ CForm.ist (oc c) (shift oc φ) ∈ E))
    ∧ (∀ (oc : C ≃ C) (E : Set (CForm A C)),
        (shiftAut (A := A) oc).pre E = E →
        ∀ (c : C) (φ : CForm A C), IsBase φ →
          (CForm.ist c φ ∈ E ↔ CForm.ist (oc c) φ ∈ E))
    ∧ (∀ (T : Set (CForm A C)) (S : Set (Rule A C)), Monotone S →
        ∀ E E' : Set (CForm A C),
          IsExtension T S E → Consistent E →
          IsExtension T S E' → Consistent E' → E' = E)
    ∧ (∀ (oc : C ≃ C) (atomv : A → Bool),
        (shiftAut (A := A) oc).pre
            (⋃ i, stage (∅ : Set (CForm A C)) (copyRules A C) ∅ i)
          = ⋃ i, stage (∅ : Set (CForm A C)) (copyRules A C) ∅ i) := by
  exact ⟨fun oc _ _ _ hT hS hE hcon huniq => rigidity oc hT hS hE hcon huniq,
         fun oc _ h c φ => rigidity_ist oc h c φ,
         fun oc _ h c _ hφ => rigidity_ist_base oc h c hφ,
         fun _ _ hmono _ _ hE hcon hE' hcon' =>
           monotone_unique hmono hE hcon hE' hcon',
         fun oc atomv => rigidity_copy oc atomv⟩
"""

TRICHOTOMY = """theorem solution (A C : Type) :
    (∀ (G : Set (LogAut A C)) (T : Set (CForm A C)) (S : Set (Rule A C))
        (E : Set (CForm A C)),
        (∀ g ∈ G, g.pre (Cn T) = Cn T) →
        (∀ g ∈ G, ∀ p : CForm A C, IsBase p → IsBase (g.form p)) →
        SymmetricUnder G T → IsExtension T S E → Consistent E →
        (∀ φ : CForm A C, IsBase φ → φ ∈ E → φ ∈ Cn T)
        ∨ (¬ ∀ E', IsExtension T S E' → Consistent E' → E' = E)
        ∨ (¬ ∀ g ∈ G, g.preRules S = S))
    ∧ (∀ S : Set (Rule A C), PropUniformRules S →
        ∀ (π : A ≃ A) (ε : A → Bool),
          (autAut π ε : LogAut A C).preRules S = S)
    ∧ SymmetricUnder (AutL A C) (∅ : Set (CForm A C))
    ∧ (∀ (atomv : A → Bool) (φ : CForm A C), IsBase φ →
        φ ∈ (⋃ i, stage (∅ : Set (CForm A C)) (copyRules A C) ∅ i) →
        φ ∈ Cn (∅ : Set (CForm A C))) := by
  exact ⟨fun _ _ _ _ hGT hGB hsym hE hcon => trichotomy hGT hGB hsym hE hcon,
         fun _ hU π ε => preRules_autAut hU π ε,
         symmetricUnder_taut,
         fun atomv φ hφ hmem => copy_conservative atomv φ hφ hmem⟩
"""


AUDIT = """theorem solution (A C : Type) :
    (∀ (T : Set (CForm A C)) (S : Set (Rule A C)) (E : Set (CForm A C)),
        (∀ p ∈ T, IsBase p) → PropUniformRules S →
        Consistent (T ∪ {γ | ∃ r ∈ S, r.conseq = γ}) →
        IsExtension T S E →
        ∀ φ : CForm A C, IsBase φ → (φ ∈ E ↔ φ ∈ Cn T))
    ∧ (∀ (Log : ℕ → Set (CForm A C)) (S : Set (Rule A C))
          (Ext : ℕ → Set (CForm A C)),
        (∀ n, ∀ p ∈ Log n, IsBase p) → PropUniformRules S →
        (∀ n, Consistent ({p | ∃ i ≤ n, p ∈ Log i} ∪ {γ | ∃ r ∈ S, r.conseq = γ})) →
        (∀ n, IsExtension {p | ∃ i ≤ n, p ∈ Log i} S (Ext n)) →
        ∀ (m n : ℕ) (φ : CForm A C), IsBase φ → φ ∈ Ext n → φ ∉ Ext m →
          φ ∈ Cn {p | ∃ i ≤ n, p ∈ Log i} ∧ φ ∉ Cn {p | ∃ i ≤ m, p ∈ Log i})
    ∧ (∀ (Log : ℕ → Set (CForm A C)) (S : Set (Rule A C))
          (Ext : ℕ → Set (CForm A C)),
        (∀ n, ∀ p ∈ Log n, IsBase p) → PropUniformRules S →
        (∀ n, Consistent ({p | ∃ i ≤ n, p ∈ Log i} ∪ {γ | ∃ r ∈ S, r.conseq = γ})) →
        (∀ n, IsExtension {p | ∃ i ≤ n, p ∈ Log i} S (Ext n)) →
        ∀ m n : ℕ, m ≤ n → ∀ φ : CForm A C, IsBase φ → φ ∈ Ext m → φ ∈ Ext n)
    ∧ (∀ a : A, ∃ (S : Set (Rule A C)) (E : Set (CForm A C)),
        Monotone S ∧ IsExtension (∅ : Set (CForm A C)) S E ∧
          E ≠ Cn ((∅ : Set (CForm A C)) ∪ {γ | ∃ r ∈ S, r.conseq = γ})) := by
  exact ⟨fun _ _ _ hT hS hcon hE => audit hT hS hcon hE,
         fun _ _ _ hb hS hc hE m n φ hφ h1 h2 => attribution hb hS hc hE m n φ hφ h1 h2,
         fun _ _ _ hb hS hc hE _ _ hmn φ hφ hm => no_silent_loss hb hS hc hE hmn φ hφ hm,
         fun a => extension_ne_Cn_consequents a⟩
"""

SPECS = [
    ("Sol_uniformity_monotone_dichotomy.lean", ["Uniformity.lean"], DICHOTOMY),
    ("Sol_uniformity_rigidity.lean",
     ["Uniformity.lean", "Rigidity.lean"], RIGIDITY),
    ("Sol_uniformity_trichotomy.lean",
     ["Uniformity.lean", "Rigidity.lean", "Trichotomy.lean"], TRICHOTOMY),
    ("Sol_uniformity_audit.lean",
     ["Uniformity.lean", "Rigidity.lean", "Trichotomy.lean", "Audit.lean"],
     AUDIT),
]

for fname, sources, thm in SPECS:
    text = HEADER + body(sources) + FOOTER + thm
    (ROOT / "Solutions" / fname).write_text(text, encoding="utf-8")
    print("wrote", fname, len(text.split("\n")), "lines")

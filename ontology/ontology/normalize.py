"""Deterministic statement normalization, content hashing, structural
signatures (ONTOLOGY_PLAN §1.5, §4.4).

The normalizer is intentionally *conservative*: it collapses cosmetic
LaTeX differences (whitespace, spacing macros, formatting wrappers, a
small symbolic-dynamics notation lexicon) but does **not** attempt risky
semantic rewrites. A conservative hash under-merges (a transient
duplicate, cheap) rather than over-merges (a false L0 merge, the worst
failure mode per §1.4); L2/L3 recover the rest.
"""

from __future__ import annotations

import hashlib
import re

# Notation synonyms that are safe to canonicalize for symbolic dynamics.
# Order matters: longer/more-specific patterns first.
_LEXICON: list[tuple[re.Pattern[str], str]] = [
    (re.compile(r"\\mathbb\s*\{?\s*Z\s*\}?"), "ℤ"),
    (re.compile(r"\\mathbb\s*\{?\s*N\s*\}?"), "ℕ"),
    (re.compile(r"\\mathbb\s*\{?\s*R\s*\}?"), "ℝ"),
    (re.compile(r"\\mathbb\s*\{?\s*Q\s*\}?"), "ℚ"),
    (re.compile(r"\\Z\b"), "ℤ"),
    (re.compile(r"\\N\b"), "ℕ"),
    (re.compile(r"\\R\b"), "ℝ"),
    (re.compile(r"\\Q\b"), "ℚ"),
    (re.compile(r"\\subseteq|\\subset\b"), "⊆"),
    (re.compile(r"\\longrightarrow|\\rightarrow|\\to\b"), "→"),
    (re.compile(r"\\longmapsto|\\mapsto\b"), "↦"),
    (re.compile(r"\\times\b"), "×"),
    (re.compile(r"\\leq\b|\\le\b"), "≤"),
    (re.compile(r"\\geq\b|\\ge\b"), "≥"),
    (re.compile(r"\\cdot\b"), "·"),
    (re.compile(r"\\infty\b"), "∞"),
    (re.compile(r"\\emptyset\b|\\varnothing\b"), "∅"),
    (re.compile(r"\\sigma\b"), "σ"),
    (re.compile(r"\\Sigma\b"), "Σ"),
]

# Spacing / cosmetic macros that carry no meaning.
_SPACING = re.compile(r"\\[,;:!]|\\quad\b|\\qquad\b|\\,|~|\\ |\\displaystyle\b")

# Formatting wrappers \cmd{...} -> keep the inner text.
_WRAPPERS = re.compile(
    r"\\(?:mathrm|mathbf|mathit|mathsf|mathtt|boldsymbol|operatorname|"
    r"text|textrm|textbf|textit|emph|ensuremath)\s*\{([^{}]*)\}"
)
# Size/delimiter decorators that should just vanish.
_DECOR = re.compile(r"\\(?:left|right|bigl|bigr|Bigl|Bigr|biggl|biggr|big|Big)\b")

_COMMENT = re.compile(r"(?<!\\)%.*?$", re.MULTILINE)
_WS = re.compile(r"\s+")


def normalize_latex(s: str) -> str:
    """Canonical form of a statement for hashing/embedding.

    Idempotent. Not a parser — a conservative textual canonicalizer.
    """
    if not s:
        return ""
    s = _COMMENT.sub("", s)
    # Unwrap nested formatting wrappers until fixed point.
    for _ in range(5):
        new = _WRAPPERS.sub(r"\1", s)
        if new == s:
            break
        s = new
    s = _DECOR.sub("", s)
    s = _SPACING.sub(" ", s)
    for pat, repl in _LEXICON:
        s = pat.sub(repl, s)
    s = s.replace("$", "").replace("{", "").replace("}", "")
    s = _WS.sub(" ", s).strip().lower()
    return s


def content_hash(kind: str, statement_latex: str) -> str:
    """L0 exact-dedup key (§5.1). Empty statement -> empty hash so we
    never collapse distinct unstated nodes onto one bucket."""
    norm = normalize_latex(statement_latex)
    if not norm:
        return ""
    return hashlib.sha256(f"{kind}\x1f{norm}".encode()).hexdigest()


def structural_sig(
    kind: str,
    tags: list[str],
    hypotheses: list[str],
    parameters: list[str],
) -> str:
    """L1 bucketing key (§5.1): coarse shape, regime-insensitive on values
    but sensitive on arity. Two nodes only compare in dedup if these match.
    """
    norm_params = sorted({_param_class(p) for p in parameters if p.strip()})
    sig = "|".join(
        [
            kind,
            ",".join(sorted({t.strip().lower() for t in tags if t.strip()})),
            f"h{len(hypotheses)}",
            ",".join(norm_params),
        ]
    )
    return hashlib.sha256(sig.encode()).hexdigest()[:16]


_DIM = re.compile(r"\bd\s*[=≥>]\s*\d|\bdimension\b|\b[12]d\b", re.IGNORECASE)


def _param_class(p: str) -> str:
    """Bucket a parameter string into a coarse regime class so that
    ``d>=2`` and ``d>=3`` share a structural bucket (still distinguished
    later by the regime field and the L3 judge)."""
    pl = p.strip().lower()
    if _DIM.search(pl):
        return "dim"
    if "alphabet" in pl or "finite" in pl:
        return "alphabet"
    if "group" in pl or "amenable" in pl or "ℤ" in pl:
        return "group"
    if "mixing" in pl or "gluing" in pl or "irreducible" in pl:
        return "mixing"
    return "other"

"""Symbolic-dynamics ontology pipeline.

Implements ../ONTOLOGY_PLAN.md. The canonical store is git-tracked JSONL
in ``snapshots/``; ``build/`` holds derived SQLite + vector index.
"""

from .schema import SCHEMA_VERSION

__all__ = ["SCHEMA_VERSION"]

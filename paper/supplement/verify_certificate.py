#!/usr/bin/env python3
"""Run the canonical exact certificate shipped with the repository."""

from pathlib import Path
import runpy


ROOT = Path(__file__).resolve().parents[2]
runpy.run_path(
    str(ROOT / "controls" / "verify_two_endpoint_anatomy.py"),
    run_name="__main__",
)

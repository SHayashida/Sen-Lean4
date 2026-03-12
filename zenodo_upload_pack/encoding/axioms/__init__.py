from __future__ import annotations

from . import asymm, minlib_selectors_v1, no_cycle3, no_cycle4, un


AXIOM_REGISTRY = {
    "asymm": asymm,
    "un": un,
    "minlib": minlib_selectors_v1,
    "no_cycle3": no_cycle3,
    "no_cycle4": no_cycle4,
}

DEFAULT_AXIOMS = ["asymm", "un", "minlib", "no_cycle3", "no_cycle4"]


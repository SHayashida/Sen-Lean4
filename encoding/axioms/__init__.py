from __future__ import annotations

from . import asymm, decisive_voter0, decisive_voter1, minlib, no_cycle3, no_cycle4, un


AXIOM_REGISTRY = {
    "asymm": asymm,
    "un": un,
    "minlib": minlib,
    "decisive_voter0": decisive_voter0,
    "decisive_voter1": decisive_voter1,
    "no_cycle3": no_cycle3,
    "no_cycle4": no_cycle4,
}

DEFAULT_AXIOMS = ["asymm", "un", "minlib", "no_cycle3", "no_cycle4"]

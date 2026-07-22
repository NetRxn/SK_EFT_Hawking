"""ADR-008 shared Lean slot control plane."""

from .controller import Controller, SlotError

__all__ = ["Controller", "SlotError"]

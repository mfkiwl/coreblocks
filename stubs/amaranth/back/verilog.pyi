"""
This type stub file was generated by pyright.
"""

from .._toolchain.yosys import *
from ..hdl.ast import SignalDict

__all__ = ["YosysError", "convert", "convert_fragment"]
def convert_fragment(*args, strip_internal_attrs=..., **kwargs) -> tuple[str, SignalDict]:
    ...

def convert(elaboratable, name=..., platform=..., *, ports=..., emit_src=..., strip_internal_attrs=..., **kwargs) -> str:
    ...


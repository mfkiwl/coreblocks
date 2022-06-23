"""
This type stub file was generated by pyright.
"""

from .ast import *
from .ir import Elaboratable

__all__ = ["Memory", "ReadPort", "WritePort", "DummyPort"]
class Memory:
    """A word addressable storage.

   """
    def __init__(self, *, width, depth, init=..., name=..., attrs=..., simulate=...) -> None:
        ...
    
    @property
    def init(self): # -> list[Unknown]:
        ...
    
    @init.setter
    def init(self, new_init): # -> None:
        ...
    
    def read_port(self, *, src_loc_at=..., **kwargs): # -> ReadPort:
        """Get a read port.

        See :c"""
        ...
    
    def write_port(self, *, src_loc_at=..., **kwargs): # -> WritePort:
        """Get a write port.

        See :"""
        ...
    
    def __getitem__(self, index): # -> ArrayProxy:
        """Simulation only."""
        ...
    


class ReadPort(Elaboratable):
    """A memory read port.

    Paramet"""
    def __init__(self, memory, *, domain=..., transparent=..., src_loc_at=...) -> None:
        ...
    
    def elaborate(self, platform): # -> Instance:
        ...
    


class WritePort(Elaboratable):
    """A memory write port.

    Parame"""
    def __init__(self, memory, *, domain=..., granularity=..., src_loc_at=...) -> None:
        ...
    
    def elaborate(self, platform): # -> Instance:
        ...
    


class DummyPort:
    """Dummy memory port.

    This por"""
    def __init__(self, *, data_width, addr_width, domain=..., name=..., granularity=...) -> None:
        ...
    


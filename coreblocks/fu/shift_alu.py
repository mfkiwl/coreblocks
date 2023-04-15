from typing import Sequence
from amaranth import *

from coreblocks.transactions import *
from coreblocks.transactions.core import def_method
from coreblocks.transactions.lib import *

from coreblocks.params import *
from coreblocks.utils import OneHotSwitch

from coreblocks.fu.fu_decoder import DecoderManager
from enum import IntFlag, auto

__all__ = ["AluFuncUnit", "ALUComponent"]

from coreblocks.utils.protocols import FuncUnit


class ShiftAluFn(DecoderManager):
    class Fn(IntFlag):
        SLL = auto()  # Logic left shift
        SRL = auto()  # Logic right shift
        SRA = auto()  # Arithmetic right shift

    @classmethod
    def get_instructions(cls) -> Sequence[tuple]:
        return [
            (cls.Fn.SLL, OpType.SHIFT, Funct3.SLL),
            (cls.Fn.SRL, OpType.SHIFT, Funct3.SR, Funct7.SL),
            (cls.Fn.SRA, OpType.SHIFT, Funct3.SR, Funct7.SA),
        ]


class ShiftAlu(Elaboratable):
    def __init__(self, gen: GenParams):
        self.gen = gen

        self.fn = ShiftAluFn.get_function()
        self.in1 = Signal(gen.isa.xlen)
        self.in2 = Signal(gen.isa.xlen)

        self.out = Signal(gen.isa.xlen)

    def elaborate(self, platform):
        m = Module()

        xlen = self.gen.isa.xlen
        xlen_log = self.gen.isa.xlen_log

        with OneHotSwitch(m, self.fn) as OneHotCase:
            with OneHotCase(ShiftAluFn.Fn.SLL):
                m.d.comb += self.out.eq(self.in1 << self.in2[0:xlen_log])
            with OneHotCase(ShiftAluFn.Fn.SRL):
                m.d.comb += self.out.eq(self.in1 >> self.in2[0:xlen_log])
            with OneHotCase(ShiftAluFn.Fn.SRA):
                m.d.comb += self.out.eq(Cat(self.in1, Repl(self.in1[xlen - 1], xlen)) >> self.in2[0:xlen_log])

        # so that Amaranth allows us to use add_clock
        dummy = Signal()
        m.d.sync += dummy.eq(1)

        return m


class ShiftAluFuncUnit(Elaboratable):
    optypes = ShiftAluFn.get_op_types()

    def __init__(self, gen: GenParams):
        self.gen = gen

        layouts = gen.get(FuncUnitLayouts)

        self.issue = Method(i=layouts.issue)
        self.accept = Method(o=layouts.accept)

    def elaborate(self, platform):
        m = Module()

        m.submodules.alu = alu = ShiftAlu(self.gen)
        m.submodules.fifo = fifo = FIFO(self.gen.get(FuncUnitLayouts).accept, 2)
        m.submodules.decoder = decoder = ShiftAluFn.get_decoder(self.gen)

        @def_method(m, self.accept)
        def _():
            return fifo.read(m)

        @def_method(m, self.issue)
        def _(arg):
            m.d.comb += decoder.exec_fn.eq(arg.exec_fn)
            m.d.comb += alu.fn.eq(decoder.decode_fn)

            m.d.comb += alu.in1.eq(arg.s1_val)
            m.d.comb += alu.in2.eq(Mux(arg.imm, arg.imm, arg.s2_val))

            fifo.write(m, rob_id=arg.rob_id, result=alu.out, rp_dst=arg.rp_dst)

        return m


class ShiftALUComponent(FunctionalComponentParams):
    def get_module(self, gen_params: GenParams) -> FuncUnit:
        return ShiftAluFuncUnit(gen_params)

    def get_optypes(self) -> set[OpType]:
        return AluFuncUnit.optypes

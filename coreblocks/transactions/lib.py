
from amaranth import *
from .core import *
from ._utils import _coerce_layout

__all__ = [
    "FIFO",
    "ClickIn", "ClickOut",
    "AdapterTrans",
    "ConnectTrans", "CatTrans"
]

# FIFOs

import amaranth.lib.fifo

class FIFO(Elaboratable):
    def __init__(self, layout, depth):
        layout = _coerce_layout(layout)
        self.width = len(Record(layout))
        self.depth = depth

        self.read = Method(o=layout)
        self.write = Method(i=layout)

    def elaborate(self, platform):
        m = Module()

        m.submodules.fifo = fifo = amaranth.lib.fifo.SyncFIFO(width=self.width, depth=self.depth)

        with self.write.body(m, ready = fifo.w_rdy) as arg:
            m.d.comb += fifo.w_en.eq(1)
            m.d.comb += fifo.w_data.eq(arg)

        with self.read.body(m, ready = fifo.r_rdy, out = fifo.r_data):
            m.d.comb += fifo.r_en.eq(1)

        return m

# "Clicked" input

class ClickIn(Elaboratable):
    def __init__(self, width=1):
        self.get = Method(o=width)
        self.btn = Signal()
        self.dat = Signal(width)

    def elaborate(self, platform):
        m = Module()

        btn1 = Signal()
        btn2 = Signal()
        dat1 = Signal.like(self.dat)
        m.d.sync += btn1.eq(self.btn)
        m.d.sync += btn2.eq(btn1)
        m.d.sync += dat1.eq(self.dat)
        get_ready = Signal()
        get_data = Signal.like(self.dat)

        with self.get.body(m, ready = get_ready, out = get_data):
            m.d.sync += get_ready.eq(0)

        with m.If(~btn2 & btn1):
            m.d.sync += get_ready.eq(1)
            m.d.sync += get_data.eq(dat1)

        return m

# "Clicked" output

class ClickOut(Elaboratable):
    def __init__(self, width=1):
        self.put = Method(i=width)
        self.btn = Signal()
        self.dat = Signal(width)

    def elaborate(self, platform):
        m = Module()

        btn1 = Signal()
        btn2 = Signal()
        m.d.sync += btn1.eq(self.btn)
        m.d.sync += btn2.eq(btn1)

        with self.put.body(m, ready = ~btn2 & btn1) as arg:
            m.d.sync += self.dat.eq(arg)

        return m

# Testbench-friendly input/output

class AdapterTrans(Elaboratable):
    def __init__(self, iface : Method, i=0, o=0):
        self.iface = iface
        self.en = Signal()
        self.done = Signal()
        self.data_in = Record(_coerce_layout(i))
        self.data_out = Record(_coerce_layout(o))
        self.input_fmt = self.data_in.layout
        self.output_fmt = self.data_out.layout

    def elaborate(self, platform):
        m = Module()

        # this forces data_in signal to appear in VCD dumps
        data_in = Signal.like(self.data_in)
        m.d.comb += data_in.eq(self.data_in)

        m.d.comb += self.done.eq(self.iface.run)

        with Transaction().body(m, request=self.en) as t:
            data_out = self.iface(m, arg=data_in)
            m.d.comb += self.data_out.eq(data_out)

        return m

# Example transactions

class ConnectTrans(Elaboratable):
    def __init__(self, method1 : Method, method2 : Method):
        self.method1 = method1
        self.method2 = method2

    def elaborate(self, platform):
        m = Module()

        with Transaction().body(m):
            data1 = Record.like(self.method1.data_out)
            data2 = Record.like(self.method2.data_out)

            m.d.comb += data1.eq(self.method1(m, data2))
            m.d.comb += data2.eq(self.method2(m, data1))

        return m

class CatTrans(Elaboratable):
    def __init__(self, src1 : Method, src2 : Method, dst : Method):
        self.src1 = src1
        self.src2 = src2
        self.dst = dst

    def elaborate(self, platform):
        m = Module()

        with Transaction().body(m):
            sdata1 = self.src1(m)
            sdata2 = self.src2(m)
            ddata = Record.like(self.dst.data_in)
            self.dst(m, ddata)

            m.d.comb += ddata.eq(Cat(sdata1, sdata2))

        return m

from amaranth import *
from amaranth.utils import log2_int
from coreblocks.transactions import Method, def_method, Priority, Transaction
from coreblocks.transactions._utils import MethodLayout
from coreblocks.transactions.lib import MethodProduct
from coreblocks.utils._typing import ValueLike
from typing import List, Optional


class BasicFifo(Elaboratable):
    """Transactional FIFO queue

    Attributes
    ----------
    read: Method
        Reads from the FIFO. Accepts an empty argument, returns a `Record`.
        Ready only if the FIFO is not empty.
    write: Method
        Writes to the FIFO. Accepts a `Record`, returns empty result.
        Ready only if the FIFO is not full.
    clear: Method
        Clears the FIFO entries. Has priority over `read` and `write` methods.
        Note that, clearing the FIFO doesn't reinitialize it to values passed in `init` parameter.

    """

    def __init__(self, layout: MethodLayout, depth: int, *, init: Optional[List[int]] = None) -> None:
        """
        Parameters
        ----------
        layout: record layout
            Layout of data stored in the FIFO.
            If integer is given, Record with field `data` and width of this paramter is used as internal layout.
        depth: int
            Size of the FIFO.
        init: List of int, optional
            List of memory elements to initialize FIFO at reset. List may be smaller than `depth`.
            If `Record` is used as `layout`, it has to be flattened to `int` first.
        """
        self.layout = layout
        self.width = len(Record(self.layout))
        self.depth = depth

        self.read = Method(o=self.layout)
        self.write = Method(i=self.layout)
        self.clear = Method()

        if init is None:
            init = []

        if len(init) > depth:
            raise RuntimeError("Init list is longer than FIFO depth")

        self.buff = Memory(width=self.width, depth=self.depth, init=init)

        self.write_ready = Signal()
        self.read_ready = Signal()

        self.read_idx = Signal((self.depth - 1).bit_length())
        self.write_idx = Signal((self.depth - 1).bit_length(), reset=(len(init) % self.depth))
        # current fifo depth
        self.level = Signal((self.depth).bit_length(), reset=len(init))

        self.clear.add_conflict(self.read, Priority.LEFT)
        self.clear.add_conflict(self.write, Priority.LEFT)

    def elaborate(self, platform) -> Module:
        def mod_incr(sig: Value, mod: int) -> Value:
            # perform (sig+1)%mod operation
            if mod == 2 ** len(sig):
                return sig + 1
            return Mux(sig == mod - 1, 0, sig + 1)

        m = Module()

        m.submodules.buff_rdport = self.buff_rdport = self.buff.read_port(
            domain="comb", transparent=True
        )  # FWFT behaviour
        m.submodules.buff_wrport = self.buff_wrport = self.buff.write_port()

        m.d.comb += self.read_ready.eq(self.level > 0)
        m.d.comb += self.write_ready.eq(self.level < self.depth)

        with m.If(self.read.run & ~self.write.run):
            m.d.sync += self.level.eq(self.level - 1)
        with m.If(self.write.run & ~self.read.run):
            m.d.sync += self.level.eq(self.level + 1)
        with m.If(self.clear.run):
            m.d.sync += self.level.eq(0)

        @def_method(m, self.write, ready=self.write_ready)
        def _(arg: Record) -> None:
            m.d.comb += self.buff_wrport.addr.eq(self.write_idx)
            m.d.comb += self.buff_wrport.data.eq(arg)
            m.d.comb += self.buff_wrport.en.eq(1)

            m.d.sync += self.write_idx.eq(mod_incr(self.write_idx, self.depth))

        @def_method(m, self.read, self.read_ready)
        def _() -> ValueLike:
            m.d.comb += self.buff_rdport.addr.eq(self.read_idx)

            m.d.sync += self.read_idx.eq(mod_incr(self.read_idx, self.depth))

            return self.buff_rdport.data

        @def_method(m, self.clear)
        def _() -> None:
            m.d.sync += self.read_idx.eq(0)
            m.d.sync += self.write_idx.eq(0)

        return m


def popcount(m: Module, x: Signal) -> Signal:
    """
    Implementation of popcount algorithm from https://en.wikipedia.org/wiki/Hamming_weight
    """
    if x.shape().width > 64:
        raise ValueError("Current popcount implementation don't support signals longer than 64 bits")

    m1 = 0x5555555555555555
    m2 = 0x3333333333333333
    m4 = 0x0F0F0F0F0F0F0F0F

    m.d.comb += x.eq(x - ((x >> 1) & m1))
    if x.shape().width > 2:
        m.d.comb += x.eq((x & m2) + ((x >> 2) & m2))
    if x.shape().width > 4:
        m.d.comb += x.eq((x + (x >> 4)) & m4)
    if x.shape().width > 8:
        m.d.comb += x.eq(x + (x >> 8))
    if x.shape().width > 16:
        m.d.comb += x.eq(x + (x >> 16))
    if x.shape().width > 32:
        m.d.comb += x.eq(x + (x >> 32))
    m.d.comb += x.eq(x & 0x7F)
    return x


# def select_N(m : Module, select_from: Array, max_to_select: int):
#    last_selected = Signal(log2_int(len(select_from)))
#    selected_counter = Signal(log2_int(max_to_select))
#
#    out = Array([Record(self._selection_layout) for _ in range(max_to_select)])
#
#    with m.Switch(last_selected):
#        for i in range(len(select_from)):
#            with m.Case(i):
#                for j in itertools.chain(range(i + 1, self.count), range(i)):
#                    with m.If(self.requests[j] & (selected_counter != max_out)):
#                        m.comb += assign(out[selected_counter], {"valid":1,"data":select_from[j]},fields=AssignType.ALL)
#                        m.comb += selected_counter.eq(selected_counter + 1)
#                        m.sync += last_selected.eq(j)
#    return out


class MultiportFifo(Elaboratable):
    def __init__(self, layout: MethodLayout, depth: int, port_count: int, fifo_count: int) -> None:
        self.layout = layout
        self.width = len(Record(self.layout))
        self.depth = depth
        self.port_count = port_count
        self.fifo_count = fifo_count

        self._read_methods = [Method(o=self.layout) for _ in range(self.port_count)]
        self._write_methods = [Method(i=self.layout) for _ in range(self.port_count)]
        self.clear = Method()

        self._selection_layout = {"valid": 1, "data": self.layout}

        if self.depth % self.fifo_count != 0:
            raise ValueError("MultiportFifo depth must be divisable by fifo_count")
        if self.fifo_count < self.port_count:
            raise ValueError("MultiportFifo requires fifo_count >= port_count")

    def order(self, m: Module, to_order: Array, ready: Signal, data_direction_from_out: bool = True) -> Array:
        """
        Put all ready elements from `to_order` to the begining of `out`
        """
        count = len(to_order)
        selected_counter = Signal(log2_int(count))
        out = Array([Record(self._selection_layout) for _ in range(count)])

        for j in range(count):
            with m.If(ready[j]):
                m.d.comb += out[selected_counter].valid.eq(1)
                if data_direction_from_out:
                    m.d.comb += to_order[j].eq(out[selected_counter])
                else:
                    m.d.comb += out[selected_counter].eq(to_order[j])
                m.d.comb += selected_counter.eq(selected_counter + 1)
        return out

    def elaborate(self, platform) -> Module:
        m = Module()

        sub_fifo_depth = self.depth // self.fifo_count
        sub_fifos = [BasicFifo(self.layout, sub_fifo_depth) for i in range(self.fifo_count)]
        for i, sub_fifo in enumerate(sub_fifos):
            setattr(m.submodules, f"sub_fifo_{i}", sub_fifo)

        read_ready = Signal()
        read_grants = Signal(len(self._read_methods))
        read_grants_count = popcount(m, read_grants)
        read_outs = [Record(self.layout) for _ in self._read_methods]
        ordered_read_outs = self.order(m, Array(read_outs), read_grants)

        with m.FSM():
            for i in range(self.fifo_count):
                with m.State(f"current_read_{i}"):
                    m.d.comb += read_ready.eq(sub_fifos[i].read.ready)
                    for j in range(self.port_count):
                        with Transaction().body(m, request=ordered_read_outs[j].valid):
                            m.d.comb += ordered_read_outs[j].data.eq(sub_fifos[(i + j) % self.fifo_count].read(m))
                    for j in range(self.port_count + 1):
                        with m.If(read_grants_count):
                            m.next(f"current_read_{(i+j)%self.fifo_count}")

        for i in range(self.port_count):

            @def_method(m, self._read_methods[i], read_ready)
            def _() -> ValueLike:
                m.d.comb += read_grants[i].eq(1)
                return read_outs[i]

        write_ready = Signal()
        write_grants = Signal(len(self._write_methods))
        write_grants_count = popcount(m, write_grants)
        write_ins = [Record(self.layout) for _ in self._write_methods]
        ordered_write_ins = self.order(m, Array(write_ins), write_grants, data_direction_from_out=False)

        with m.FSM():
            for i in range(self.fifo_count):
                with m.State(f"current_write_{i}"):
                    m.d.comb += write_ready.eq(sub_fifos[i].write.ready)
                    for j in range(self.port_count):
                        with Transaction().body(m, request=ordered_write_ins[j].valid):
                            sub_fifos[(i + j) % self.fifo_count].write(m, ordered_write_ins[j].data)
                    for j in range(self.port_count + 1):
                        with m.If(write_grants_count):
                            m.next(f"current_write_{(i+j)%self.fifo_count}")

        for i in range(self.port_count):

            @def_method(m, self._write_methods[i], write_ready)
            def _(arg: Record) -> None:
                m.d.comb += write_grants[i].eq(1)
                m.d.comb += write_ins[i].eq(arg)

        self.clear = MethodProduct([sub_fifo.clear for sub_fifo in sub_fifos])

        return m

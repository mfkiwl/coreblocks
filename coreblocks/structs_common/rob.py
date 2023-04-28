from amaranth import *
from ..transactions import Method, def_method, Priority
from ..params import GenParams, ROBLayouts
from ..params.dependencies import DependencyManager
from ..params.keys import ROBSingleKey

__all__ = ["ReorderBuffer"]


class ReorderBuffer(Elaboratable):
    def __init__(self, gen_params: GenParams) -> None:
        self.params = gen_params
        layouts = gen_params.get(ROBLayouts)
        self.put = Method(i=layouts.data_layout, o=layouts.id_layout)
        self.mark_done = Method(i=layouts.id_layout)
        self.retire = Method(o=layouts.retire_layout)
        self.can_flush = Method(o=layouts.can_flush_layout)
        self.flush = Method(o=layouts.flush_layout)
        self.interrupt = Method()
        self.data = Array(Record(layouts.internal_layout) for _ in range(2**gen_params.rob_entries_bits))
        self.single_entry = Signal()
        connections = gen_params.get(DependencyManager)
        connections.add_dependency(ROBSingleKey(), self.single_entry)

    def elaborate(self, platform) -> Module:
        m = Module()

        start_idx = Signal(self.params.rob_entries_bits)
        end_idx = Signal(self.params.rob_entries_bits)

        put_possible = (end_idx + 1)[0 : len(end_idx)] != start_idx

        m.d.comb += self.single_entry.eq((start_idx + 1)[0 : len(start_idx)] == end_idx)

        @def_method(m, self.retire, ready=self.data[start_idx].done)
        def _():
            m.d.sync += start_idx.eq(start_idx + 1)
            m.d.sync += self.data[start_idx].done.eq(0)
            m.d.sync += self.data[start_idx].interrupt.eq(0)
            return {
                "rob_data": self.data[start_idx].rob_data,
                "interrupt": self.data[start_idx].interrupt,
                "rob_id": start_idx,
            }

        @def_method(m, self.put, ready=put_possible)
        def _(arg):
            m.d.sync += self.data[end_idx].rob_data.eq(arg)
            m.d.sync += self.data[end_idx].done.eq(0)
            m.d.sync += end_idx.eq(end_idx + 1)
            return end_idx

        @def_method(m, self.can_flush)
        def _():
            return start_idx != end_idx

        self.flush.add_conflict(self.put, priority=Priority.LEFT)
        self.flush.add_conflict(self.retire, priority=Priority.LEFT)

        @def_method(m, self.flush)
        def _():
            m.d.sync += start_idx.eq(start_idx + 1)
            return self.data[start_idx].rob_data.rp_dst

        @def_method(m, self.interrupt)
        def _():
            m.d.sync += self.data[start_idx].interrupt.eq(1)

        # TODO: There is a potential race condition when ROB is flushed.
        # If functional units aren't flushed, finished obsolete instructions
        # could mark fields in ROB as done when they shouldn't.
        @def_method(m, self.mark_done)
        def _(rob_id: Value):
            m.d.sync += self.data[rob_id].done.eq(1)

        return m

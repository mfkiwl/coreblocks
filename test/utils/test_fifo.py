from amaranth import *
from amaranth.sim import Settle

from coreblocks.utils.fifo import BasicFifo, MultiportFifo
from coreblocks.transactions import TransactionModule
from coreblocks.transactions.lib import AdapterTrans
from coreblocks.utils._typing import LayoutLike

from test.common import TestCaseWithSimulator, TestbenchIO, data_layout
from collections import deque
from parameterized import parameterized_class
import random
from typing import Callable


class FifoTestCircuit(Elaboratable):
    def __init__(self, depth, init, fifo_constructor):
        self.depth = depth
        self.init = init
        self.fifo_constructor = fifo_constructor

    def elaborate(self, platform):
        m = Module()
        tm = TransactionModule(m)

        m.submodules.fifo = self.fifo = self.fifo_constructor(layout=data_layout(8), depth=self.depth, init=self.init)

        m.submodules.fifo_read = self.fifo_read = TestbenchIO(AdapterTrans(self.fifo.get_read()))
        m.submodules.fifo_write = self.fifo_write = TestbenchIO(AdapterTrans(self.fifo.get_write()))
        m.submodules.fifo_clear = self.fifo_clear = TestbenchIO(AdapterTrans(self.fifo.clear))

        return tm


params_dinit = [
    ("notpower_notfull", 5, 3),
    ("notpower_full", 5, 5),
    ("notpower_empty", 5, 0),
    ("power_notfull", 4, 3),
    ("power_full", 4, 4),
    ("power_empty", 4, 0),
]

params_c = [
    ("basic", BasicFifo),
    (
        "multi",
        lambda self, layout, depth, init: MultiportFifo(
            layout=layout, depth=depth, port_count=1, fifo_count=1, init=init
        ),
    ),
]


@parameterized_class(
    ("name", "depth", "init_len", "name_constr", "fifo_constructor"),
    [dinit + constr for dinit in params_dinit for constr in params_c],
)
class TestBasicFifo(TestCaseWithSimulator):
    depth: int
    init_len: int
    fifo_constructor: Callable[[LayoutLike, int, int], Elaboratable]

    def test_randomized(self):
        init_values = [x + 1 for x in range(self.init_len)]

        fifoc = FifoTestCircuit(depth=self.depth, init=init_values, fifo_constructor=self.fifo_constructor)
        expq = deque(reversed(init_values))  # first expected element is at the start of init_list

        cycles = 256
        random.seed(42)

        self.done = False

        def source():
            for _ in range(cycles):
                if random.randint(0, 1):
                    yield  # random delay

                if random.random() < 0.005:
                    yield from fifoc.fifo_clear.call()
                    expq.clear()

                v = random.randint(0, (2**fifoc.fifo.width) - 1)
                yield from fifoc.fifo_write.call(data=v)
                expq.appendleft(v)

            self.done = True

        def target():
            while not self.done or expq:
                if random.randint(0, 1):
                    yield

                yield from fifoc.fifo_read.call_init()
                yield

                #                yield Settle() <- this settle make test to fail due to problems with first read value
                v = yield from fifoc.fifo_read.call_result()
                if v is not None:
                    self.assertEqual(v["data"], expq.pop())

                yield from fifoc.fifo_read.disable()

        with self.run_simulation(fifoc) as sim:
            sim.add_sync_process(source)
            sim.add_sync_process(target)

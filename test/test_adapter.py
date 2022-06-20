from amaranth import *
from amaranth.sim import Passive

from coreblocks.transactions import TransactionModule, Method, def_method
from coreblocks.transactions.lib import AdapterTrans


from .common import TestCaseWithSimulator, TestbenchIO

class Echo(Elaboratable):
  def __init__(self):
      self.data_bits = 8

      self.layout_in = [("data", self.data_bits)]
      self.layout_out = [("data", self.data_bits)]

      self.action = Method(i = self.layout_in, o = self.layout_out)

  def elaborate(self, platform):
      m = Module()

      # because amaranth requires synchronous elements when using clock
      dummySync = Signal()
      m.d.sync += dummySync.eq(dummySync + 1)

      @def_method(m, self.action, ready=C(1))
      def _(arg):
        return arg

      return m

class Consumer(Elaboratable):
  def __init__(self):
      self.data_bits = 8

      self.layout_in = [("data", self.data_bits)]
      self.layout_out = []

      self.action = Method(i = self.layout_in, o = self.layout_out)

  def elaborate(self, platform):
      m = Module()

      # because amaranth requires synchronous elements when using clock
      dummySync = Signal()
      m.d.sync += dummySync.eq(dummySync + 1)

      @def_method(m, self.action, ready=C(1))
      def _(arg):
        return C(0)

      return m

def testbenchIO(method):
  return TestbenchIO(AdapterTrans(method))

class TestElaboratable(Elaboratable):
  def __init__(self):
    self.m = Module()
    self.tm = TransactionModule(self.m)
    
    self.echo = Echo()
    self.consumer = Consumer()
    self.io_echo = testbenchIO(self.echo.action)
    self.io_consume = testbenchIO(self.consumer.action)
    
  def elaborate(self, platform):
    m = self.m

    m.submodules.echo = self.echo
    m.submodules.io_echo = self.io_echo
    m.submodules.consumer = self.consumer
    m.submodules.io_consume = self.io_consume

    return self.tm

class TestAdapterTrans(TestCaseWithSimulator):
    def proc(self):
        for _ in range(3):
          yield from self.t.io_consume.call()
        for expected in [4, 1, 0]:
          obtained = (yield from self.t.io_echo.call({"data": C(expected)}))["data"]
          assert expected == obtained, f'expected: {expected}, got: {obtained}'

    def test_single(self):
        self.t = t = TestElaboratable()

        with self.runSimulation(t, max_cycles=100) as sim:
            sim.add_sync_process(self.proc)

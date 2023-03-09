from _pydrofoil import RISCV64 as BaseRISCV64

ALL_EVENTS = {"step"}

class RISCV64(BaseRISCV64):
    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        self._callbacks = {}

    def step(self):
        super().step()
        for cb in self._callbacks.get("step", []):
            cb(self)

    def run(self, limit=0):
        if limit == 0:
            limit = 2**63-1
        for _ in range(limit):
            self.step()

    def register_callback(self, event, callback):
        assert event in ALL_EVENTS
        self._callbacks.setdefault(event, []).append(callback)

from typing import Generator, final

from pytest import fixture

@fixture
def monkeypatch() -> Generator[MonkeyPatch]: ...

@final
class MonkeyPatch:
    def setattr(self, target, name): ...

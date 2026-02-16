from typing import Generator, final
from pytest import fixture

@final
class LogCaptureFixture:
    def set_level(self, level: int | str, logger: str | None = None) -> None: ...

@fixture
def caplog(request) -> Generator[LogCaptureFixture]: ...

from typing import Generator, Generic, AnyStr

from pytest import fixture

@fixture
def capsysbinary(request) -> Generator[CaptureFixture[bytes]]: ...

class CaptureFixture(Generic[AnyStr]):
    def close(self) -> None: ...

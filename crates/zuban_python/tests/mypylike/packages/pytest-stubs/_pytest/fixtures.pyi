from typing import Any, Callable, Iterable, Sequence, TypeVar, overload, \
    Literal, final
import dataclasses

FixtureFunction = TypeVar("FixtureFunction", bound=Callable[..., object])
_ScopeName = Literal["session", "package", "module", "class", "function"]
Config = Any

@overload
def fixture(
    fixture_function: Callable[..., object],
    *,
    scope: _ScopeName | Callable[[str, Config], _ScopeName] = ...,
    params: Iterable[object] | None = ...,
    autouse: bool = ...,
    ids: Sequence[object | None] | Callable[[Any], object | None] | None = ...,
    name: str | None = ...,
) -> FixtureFunctionDefinition: ...


@overload
def fixture(
    fixture_function: None = ...,
    *,
    scope: _ScopeName | Callable[[str, Config], _ScopeName] = ...,
    params: Iterable[object] | None = ...,
    autouse: bool = ...,
    ids: Sequence[object | None] | Callable[[Any], object | None] | None = ...,
    name: str | None = None,
) -> FixtureFunctionMarker: ...


class FixtureFunctionDefinition:
    def __init__(
        self,
        *,
        function: Callable[..., Any],
        fixture_function_marker: FixtureFunctionMarker,
        instance: object | None = None,
        _ispytest: bool = False,
    ) -> None: ...

    def __call__(self, *args: Any, **kwds: Any) -> Any: ...


@final
@dataclasses.dataclass(frozen=True)
class FixtureFunctionMarker:
    scope: _ScopeName | Callable[[str, Config], _ScopeName]
    params: tuple[object, ...] | None
    autouse: bool = False
    ids: tuple[object | None, ...] | Callable[[Any], object | None] | None = None
    name: str | None = None

    _ispytest: dataclasses.InitVar[bool] = False

    def __call__(self, function: FixtureFunction) -> FixtureFunctionDefinition: ...

yield_fixture = fixture

from typing import Any, Callable, Iterable, Literal, Sequence, TypeVar
from typing_extensions import ParamSpec

_T = TypeVar("_T")

def fixture(
    fixture_function: Callable[..., _T] | None = ...,
    *,
    scope: Literal["session", "module", "class", "function"] = ...,
) -> Any: ...

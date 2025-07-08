'''
from typing import TypeVar, Callable, Any
TCallable = TypeVar('TCallable', bound=Callable[..., Any])

def decorator_with_args(name: str) -> Callable[[TCallable], TCallable]:
    def decorator(fn: TCallable) -> TCallable:
        # ... do something with `name` and `fn`
        return fn
    return decorator


@decorator_with_args(name='my_new_behaviour')
def my_new_behaviour(blah: float) -> int:
    pass

x = my_new_behaviour
##? my_new_behaviour
x

import functools

def _wraps_with_cleaned_sig(wrapped, num_args_to_remove):
    """
    baz
    """
    # By passing (None, ...), we're removing (arg1, ...) from *args
    args_to_remove = (None,) * num_args_to_remove
    fake_wrapped = functools.partial(wrapped, *args_to_remove)
    fake_wrapped.__doc__ = wrapped.__doc__
    fake_wrapped.__name__ = wrapped.__name__  # type: ignore[attr-defined]
    fake_wrapped.__module__ = wrapped.__module__

    return functools.wraps(fake_wrapped)


def _with_element(method):
    """
    bar
    """

    @_wraps_with_cleaned_sig(method, 1)  # Remove self and element from sig.
    def wrapped_method(dg, *args, **kwargs):
        # Warn if we're called from within an @st.cache function
        return dg._enqueue_new_element_delta(marshall_element, delta_type, last_index)

    return wrapped_method

class D:
    @_with_element
    def map(self, element, data=None, zoom=None, use_container_width=True):
        pass

D().map

def bla(x, y, z):
    'fuu'
x = _wraps_with_cleaned_sig(bla)
x

@_with_element
def blabla(x, y, z):
    'lala'

blabla(
'''

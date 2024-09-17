# Zuban

Copyright (c) 2020-2024 Dave Halter. All rights reserved.

## Development

I usually use this to test:

    CARGO_TARGET_DIR=/tmp/cargo_target RUSTFLAGS="-Z macro-backtrace" cargo test -- --nocapture

or:

    CARGO_TARGET_DIR=/tmp/cargo_target RUSTFLAGS="-Z macro-backtrace" cargo test -- --nocapture

with debug enabled:

    RUST_BACKTRACE=1 CARGO_TARGET_DIR=/tmp/cargo_target RUSTFLAGS="-Z macro-backtrace" cargo test --features zuban_debug
    CARGO_TARGET_DIR=/tmp/cargo_target  cargo test --features zuban_debug

Debugging:

    gdb -ex r --args <executable> <arguments...>


### Profiling

    sudo apt-get install linux-tools-generic
    cargo install flamegraph

    # Might be needed
    sudo sysctl -w kernel.perf_event_paranoid=-1
    sudo sysctl -w kernel.kptr_restrict=0

    flamegraph -- cargo test blackbox --release
    # Sometimes [Unknown] appears, because only part of the stack is copied, use the command below.
    # see also https://github.com/flamegraph-rs/flamegraph/issues/193#issuecomment-2119274041
    flamegraph -c 'record -F 100 --call-graph dwarf,50000 -g' -- cargo test mypy --release
    firefox flamegraph.svg

### Progress History

- 2022-09-27: 1170 / 2547 (0.08s -> 14625 tests/s 44b39e90299909bb1672a0a64699c42145efda35)
- 2023-01-20: 1622 / 2989 (0.13s -> 12476 tests/s 914aede21d716bd80b9a790c213b6d54024b8b79)
- 2023-02-23: 1750 / 3104 (0.27s ->  6481 tests/s a8d9592a77286caa42501c69ea8b7b89c430c4a8)
- 2023-03-22: 2106 / 3866 (0.30s ->  7262 tests/s d5b94d4a3dcb75fbdb2abb7c6feb41dd7bd287ec)
- 2023-04-23: 2328 / 4006 (0.31s ->  7510 tests/s 515d90a4a5c12af68cd885db0bf2b79afe88f54d)
- 2023-05-23: 2881 / 4845 (0.34s ->  8473 tests/s 2653b7365e335a51adc3eb7dcfede26fe7c7d3d0)
- 2023-06-23: 3411 / 5752 (0.39s ->  8746 tests/s 52f55a6477c9ecb71a76323cb9f8937e8f0c2433)
- 2023-07-23: 3744 / 6061 (0.48s ->  7800 tests/s 0d94b68467ac9b4f82e393af4a2d462beee12ead) (note: Removed a dbg)
- 2023-08-23: 4443 / 6770 (0.53s ->  8383 tests/s d306fda4bcd8455212122ddb683168a2d9da850e)
- 2023-09-23: 4822 / 7390 (0.60s ->  8037 tests/s a46931615583c16ef412f4f00b27d712e1fcd897)
- 2023-10-23: 5086 / 7397 (0.72s ->  7064 tests/s 8b191e26f20d15c7616adffb19674c42e56bb016)
- 2023-11-23: 5467 / 7643 (1.00s ->  5467 tests/s eff073096626fbede374f3d9431d2a17c644a2c0)
- 2023-12-23: 5686 / 7657 (1.02s ->  5574 tests/s 30f78634246781c10af0d098bd521487522d9c98)
- 2024-01-23: 5836 / 7719 (1.09s ->  5354 tests/s 6de18286ca58e27e8da9ff72a3f39fd86d50ad6)
- 2024-02-23: 5927 / 7739 (1.05s ->  5645 tests/s d718904967d63839be27a8822cba5a48ea186a6a)
- 2024-03-23: 6128 / 8248 (1.13s ->  5423 tests/s c1ac728e33fd3034887bf39c34edf3047e903e8a)
- 2024-04-23: 6414 / 8417 (1.24s ->  5173 tests/s e70c61aa9ec0ce2735dd0890f8803537ae4ba115)
- 2024-05-23: 6826 / 8674 (0.80s ->  8533 tests/s 98753cd9964134f07e66079a650c1966905a7e40)
- 2024-06-23: 7129 / 8778 (1.17s ->  6093 tests/s fad9c939a769eb1129ea73581822f559c9d482ed)
- 2024-07-23: 7425 / 8955 (1.38s ->  5380 tests/s b770518b210c23cfb116ecd943f7aefc8e95e8e7)
- 2024-08-23: 7725 / 9082 (1.47s ->  5255 tests/s 1d580b30e1b0712182c9c827ef79edd682994dac)

### Unsound?

- Chosing `__new__` or `__init__` via heuristic
- Initializing casting `Type[Class]` to `Type[object]` and then `Type[object]()` is ok?
- Ignoring positional arg names when assigning functions in:
  - Override checks (including multiple inheritance checks)
  - Checks where one side of callables is implicitly typed (i.e. `def foo...`)
  - Checks of inplace operators (However this does not matter, probably).
  - overlapping checks
- Sequence[str] :> str have both different `__contains__` implementations (see Michi's email)
- property narrowing with `__set__` narrows `__get__` (see testSubclassDescriptorsBinder)
- property setter type can be != getter return type (this is not inherent)
- variables don't need to actually be initialized:
  - foo: str
  - dataclasses `__init__` is overwritten and therefore members are not necessarily initialized.
- hasattr narrowing uses `Any` instead of `object`
- `a: int; callable(a)` will narrow a to be a callable that returns Any and takes any paramaters
- Enum value when a = 1 and b = '' will be Any for no reason
- total_ordering fills functions with an Any return type if the other functions return not None

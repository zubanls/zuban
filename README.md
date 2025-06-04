# Zuban

Copyright (c) 2020-2025 Dave Halter. All rights reserved.


## Installation

Use `pip install zuban` to install it.


## Licensing

Create a license with (see also licensing README):

```
ZUBAN_SIGNING_KEY=`cat` cargo run -p licensing create --name Dave --email info@zubanls.com --company Squirrels
```

and store it at:

- Linux: `/home/<user>/.config/zuban/license.json`
- Windows: `C:\Users\<User>\AppData\Roaming\zuban\license.json`
- Mac: `/Users/<User>/Library/Application Support/zuban/license.json`

## Development

You might want to run `cargo install cargo-insta` and run `cargo insta` for
reviewing some tests (especially with parsers).

I usually use this to test:

    CARGO_TARGET_DIR=/tmp/cargo_target RUSTFLAGS="-Z macro-backtrace" cargo test -- --nocapture

or:

    CARGO_TARGET_DIR=/tmp/cargo_target RUSTFLAGS="-Z macro-backtrace" cargo test -- --nocapture

with debug enabled:

    RUST_BACKTRACE=1 CARGO_TARGET_DIR=/tmp/cargo_target RUSTFLAGS="-Z macro-backtrace" cargo test --features zuban_debug
    CARGO_TARGET_DIR=/tmp/cargo_target  cargo test --features zuban_debug

Debugging:

    gdb -ex r --args <executable> <arguments...>

On Windows' Github CI the tempdir path may be part of a symlink. Therefore you
may want to run tests like this:

TMP=~/<path-with-link> cargo test -p zubanls

## Running primer

Mypy uses mypy-primer to test for changes. We can simply check if we panic on
some of these projects with:

    cargo run --bin primer --release

    # Run on all files to see if there are any panics
    RUST_BACKTRACE=1 cargo run --bin primer --release -- -- --strict --ignore-excludes-from-config .

## Releasing

Releasing is typically done by GitHub actions, which invokes `deploy/pypi/zuban/build.sh`.
For a patch release, simply run `./release.sh`, for a minor release `./release.sh minor` (`minor` here comes from `cargo release`).


## Profiling

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

## Progress History

- 2022-09-27:  1170 /  2547 (0.08s -> 14625 tests/s 44b39e90299909bb1672a0a64699c42145efda35)
- 2023-01-20:  1622 /  2989 (0.13s -> 12476 tests/s 914aede21d716bd80b9a790c213b6d54024b8b79)
- 2023-02-23:  1750 /  3104 (0.27s ->  6481 tests/s a8d9592a77286caa42501c69ea8b7b89c430c4a8) (note: Cache typeshed multiple times)
- 2023-03-22:  2106 /  3866 (0.30s ->  7262 tests/s d5b94d4a3dcb75fbdb2abb7c6feb41dd7bd287ec)
- 2023-04-23:  2328 /  4006 (0.31s ->  7510 tests/s 515d90a4a5c12af68cd885db0bf2b79afe88f54d)
- 2023-05-23:  2881 /  4845 (0.34s ->  8473 tests/s 2653b7365e335a51adc3eb7dcfede26fe7c7d3d0)
- 2023-06-23:  3411 /  5752 (0.39s ->  8746 tests/s 52f55a6477c9ecb71a76323cb9f8937e8f0c2433)
- 2023-07-23:  3744 /  6061 (0.48s ->  7800 tests/s 0d94b68467ac9b4f82e393af4a2d462beee12ead) (note: Removed a dbg)
- 2023-08-23:  4443 /  6770 (0.53s ->  8383 tests/s d306fda4bcd8455212122ddb683168a2d9da850e)
- 2023-09-23:  4822 /  7390 (0.60s ->  8037 tests/s a46931615583c16ef412f4f00b27d712e1fcd897)
- 2023-10-23:  5086 /  7397 (0.72s ->  7064 tests/s 8b191e26f20d15c7616adffb19674c42e56bb016)
- 2023-11-23:  5467 /  7643 (1.00s ->  5467 tests/s eff073096626fbede374f3d9431d2a17c644a2c0)
- 2023-12-23:  5686 /  7657 (1.02s ->  5574 tests/s 30f78634246781c10af0d098bd521487522d9c98)
- 2024-01-23:  5836 /  7719 (1.09s ->  5354 tests/s 6de18286ca58e27e8da9ff72a3f39fd86d50ad6)
- 2024-02-23:  5927 /  7739 (1.05s ->  5645 tests/s d718904967d63839be27a8822cba5a48ea186a6a)
- 2024-03-23:  6128 /  8248 (1.13s ->  5423 tests/s c1ac728e33fd3034887bf39c34edf3047e903e8a)
- 2024-04-23:  6414 /  8417 (1.24s ->  5173 tests/s e70c61aa9ec0ce2735dd0890f8803537ae4ba115)
- 2024-05-23:  6826 /  8674 (0.80s ->  8533 tests/s 98753cd9964134f07e66079a650c1966905a7e40) (note: Reuse typeshed caches
- 2024-06-23:  7129 /  8778 (1.17s ->  6093 tests/s fad9c939a769eb1129ea73581822f559c9d482ed)
- 2024-07-23:  7425 /  8955 (1.38s ->  5380 tests/s b770518b210c23cfb116ecd943f7aefc8e95e8e7)
- 2024-08-23:  7725 /  9082 (1.47s ->  5255 tests/s 1d580b30e1b0712182c9c827ef79edd682994dac)
- 2024-09-23:  7945 /  9150 (1.51s ->  5262 tests/s 17da15d9c0a208848aad501b83ebb875d1a4bb5f)
- 2024-10-23:  8143 /  9344 (1.60s ->  5089 tests/s 1540a3062b529d99b04fc5865def01482822872b)
- 2024-11-23:  8480 /  9668 (1.65s ->  5139 tests/s 0dac1c48911dffc925c03b81a79d3f099bae6ffb) (note: Avoided union replacing)
- 2025-02-23:  8812 / 10128 (1.25s ->  7050 tests/s b65d5256011792e807562f366168a3d3b7845eaa)
- 2025-03-23:  8968 / 10369 (1.27s ->  7061 tests/s 4d34f7bc9aaa82ed1b64c54479a29932953a8eb8)
- 2025-04-23:  9272 / 10582 (1.62s ->  5723 tests/s b068ac600aff0dd46bf9e97c4889339ec99fc763) (note: tests cannot reuse Python versions sometimes)
- 2025-05-23:  9400 / 10701 (1.71s ->  5497 tests/s 4827fc01e4052bfe9fbbd0535a84906ae9159b7d)

## Unsound?

- Chosing `__new__` or `__init__` via heuristic
- Initializing casting `Type[Class]` to `Type[object]` and then `Type[object]()` is ok?
- Ignoring positional arg names when assigning functions in:
  - Override checks (including multiple inheritance checks)
  - Checks where one side of callables is implicitly typed (i.e. `def foo...`)
  - Checks of inplace operators (However this does not matter, probably).
  - overlapping checks
- Sequence[str] :> str have both different `__contains__` implementations (see Michi's email)
- property narrowing with `__set__` narrows `__get__` (see testSubclassDescriptorsBinder)
- property setter type can be != getter return type https://github.com/python/mypy/issues/3004
- variables don't need to actually be initialized:
  - foo: str
  - dataclasses `__init__` is overwritten and therefore members are not necessarily initialized.
- hasattr narrowing uses `Any` instead of `object`
- `a: int; callable(a)` will narrow a to be a callable that returns Any and takes any paramaters
- Enum value when a = 1 and b = '' will be Any for no reason
- total_ordering fills functions with an Any return type if the other functions return not None

### Questionable, maybe change behind flag?

- `.py` not type-checked if `.pyi` exists
- Method Overrides param signatures are not type checked if they are not annotated


### Mypy: Please change!!

- Untyped decorated methods are not checked when `--check-untyped-defs`, see also test
  `untyped_override_check_untyped_defs_mypy_compatible`

## Development Introduction

- Test driven, always create a failing test first
- Working on Parser Trees, see also https://docs.python.org/3/reference/grammar.html and crates/parsa_python
- Trees are flat in a Vec in Memory
- Trees and compiler information (`Vec<Point>`) are separate data structures,
  it's also flat in memory with the same length as the tree.
- `NodeRef` or `PointLink` is essentially a pointer to both a parser tree
  terminal/nonterminal and a `Point`
- Compiler information is either a type (`Type`), a special object (`Specific`) or a redirect
- There is a concept of incremental compiling with localities

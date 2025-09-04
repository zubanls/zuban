# Zuban

Zuban is a high-performance Python Language Server and type checker implemented
in Rust, by the author of [Jedi](https://github.com/davidhalter/jedi).
Zuban is 20–200× faster than Mypy, while using roughly half the memory and CPU
compared to Ty and Pyrefly. It offers both a PyRight-like mode and a
Mypy-compatible mode, which behaves just like Mypy; supporting the same config
files, command-line flags, and error messages.

Most important LSP features are supported. Features include diagnostics,
completions, goto, references, rename, hover and document highlights.

Zuban passes over 95% of Mypy’s relevant test suite and offers comprehensive
support for Python's [type system](https://htmlpreview.github.io/?https://github.com/python/typing/blob/main/conformance/results/results.html).

[Documentation](https://docs.zubanls.com)
[Website](https://zubanls.com)

## Installation / Usage

```
pip install zuban  # Installation

zuban check   # PyRight-like checking
zuban mypy    # Mypy compatibility mode
zmypy         # An alias for zuban mypy
zuban server  # An LSP server
```

If you want Zuban to pick up your dependencies, please activate the virtual env first.

You can also install the Zuban rust binary using [Nix flakes](https://nix.dev/concepts/flakes.html)
by adding it as an input to your flake.nix:

```nix
{
  inputs.zuban.url = "github:zubanls/zuban";

  outputs = { nixpkgs, zuban, ... }: {
    home.packages = [ zuban.packages.${system}.default ];
  };
}
```

Or install directly via `nix profile`:
```bash
nix profile install github:zubanls/zuban
```

## License

This project is dual licensed:

- **Open Source License**: [GNU Affero General Public License v3.0](LICENSE) (AGPL-3.0).
  You may use, modify, and distribute this project under the terms of the AGPL-3.0.
- **Commercial License**: Available for organizations that prefer not to comply with the AGPL.
  Contact info (at) zubanls.com for commercial licensing options.

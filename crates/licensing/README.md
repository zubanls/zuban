# Licensing

This module is here for managing licenses. We currently use ed25519 keys.
Nothing else is supported. Please note that the security is not
very important at the moment, because we only use it for signing licenses.
Licenses are probably easier circumvented by modifying the original binary to
not check for licenses in the first place, since Zuban doesn't rely on web
services.

## Creating Licenses

To create a license use a command like

```
ZUBAN_SIGNING_KEY=`cat` cargo run create --name Dave --email info@zubanls.com --company Squirrels
```

Make sure to **never** leak the private key. It should **never** be part of the **shell history** or somehow be provided **as an argument to a process** (which would leak it when looking at processes).

## Initializing Private/Public Keys

To create a new key with OpenSSL use `./new_openssl_key.sh`. Once you have a
few licenses (and please save them somewhere safe!), you can use

```
cat | rg pub | sed 's/pub: //' | xargs -n 1 cargo run -q hex-to-rust-byte-literals
```

to be able to paste these public keys to the Rust binary.

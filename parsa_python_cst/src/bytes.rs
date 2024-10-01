use std::borrow::Cow;

use parsa_python::PyNode;

use crate::strings::{parse_python_octal, unpack_string_or_bytes_content};

pub fn parse_python_bytes_literal(literal: PyNode) -> Cow<[u8]> {
    let code = literal.as_code();
    let unpacked = unpack_string_or_bytes_content(code);
    let inner_bytes = unpacked.inner.as_bytes();
    if unpacked.had_raw_modifier {
        return Cow::Borrowed(inner_bytes);
    }
    let mut iterator = inner_bytes.iter().enumerate();
    let mut previous_insert = 0;
    let mut out = None;
    while let Some((i, ch)) = iterator.next() {
        if ch == &b'\\' {
            if out.is_none() {
                out = Some(Vec::with_capacity(inner_bytes.len()));
            }
            let s = out.as_mut().unwrap();
            s.extend_from_slice(&inner_bytes[previous_insert..i]);
            let (next_index, &ch) = iterator.next().unwrap();
            previous_insert = i + 2;

            match ch {
                b'\\' | b'\'' | b'"' => s.push(ch),
                b'\n' => (), // Escaping a newline ignores it
                /*
                b'x' => {
                    if let Some(c) = parse_hex(2, iterator.by_ref()) {
                        s.push(c)
                    }
                }
                b'N' => todo!("Need to implement \\N{{...}}"),
                b'a' => s.push('\x07'), // Bell
                b'b' => s.push('\x08'), // Backspace
                b't' => s.push('\x09'), // Tab
                */
                b'n' => s.push(b'\n'),   // Newline (line feed \x0a)
                b'v' => s.push(b'\x0b'), // Vertical tab
                b'f' => s.push(b'\x0c'), // Form Feed
                b'r' => s.push(b'\x0d'), // Carriage Return
                _ => {
                    if let Some((len, octal)) = parse_python_octal(&inner_bytes[next_index..]) {
                        for _ in 1..len {
                            previous_insert += 1;
                            iterator.next();
                        }
                        // We simply cut off a bit, which is also how Python does it
                        s.push(octal as u8)
                    } else {
                        // These literals are not allowed and generate warnings in Python
                        s.push(b'\\');
                        s.push(ch);
                    }
                }
            }
        }
    }
    if let Some(mut out) = out {
        out.extend_from_slice(&inner_bytes[previous_insert..inner_bytes.len()]);
        Cow::Owned(out)
    } else {
        Cow::Borrowed(inner_bytes)
    }
}

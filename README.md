# lawful-fields

Cutting a line of packed bytes into fields, and reading and writing decimal numbers, with laws
that a proof checker verifies. Built on `lawful-bytes`. Every law states the result on the plain
list of bytes; `split` mirrors Base's `String.split`, and bridge laws (`split_text`, `join_text`)
say that splitting bytes is splitting their text, one character per byte. That is what lets a
String-based specification (framebender's) be proven about code that never builds a String.

Operations: `cut` (the end offsets of the first n fields), `num` (a decimal number that fits a
U32), `digits` (one or more digits, any size), `put_dec` (write a number in decimal).

Status: the laws (`LAWS.bend`, definitions in `defs.bend`) were reviewed in two rounds by Claude,
GPT and Grok (`reviews/`), and all 19 are proven (`PROOF.bend`; `./check.sh` runs `bend` and the
Lean-proven kernel, `--verdict`). `fields.bend` is the reference implementation.

`bend test/spot.bend` evaluates both sides of the laws on small examples.

MIT (see `LICENSE`).

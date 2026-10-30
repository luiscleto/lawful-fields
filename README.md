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

## Use

Published on [BendHub](https://hub.bend-lang.com/name/lawful-fields) with its laws and proofs. Bend fetches
an import by name and checks it against the package's hash:

```python
import lawful-fields@0.1.0.0/fields.bend as F  # the implementation
import lawful-fields@0.1.0.0/LAWS.bend as L    # the laws, to use in your own proofs
import lawful-fields@0.1.0.0/PROOF.bend as P   # their proofs, which a proof using a law needs loaded
```

Versions below 1.0 have laws reviewed by three AI models but not yet by a human expert.

MIT (see `LICENSE`).

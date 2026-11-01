# lawful-fields

Splitting a line of bytes into fields at a separator, and reading and writing decimal numbers, for
Bend 2 byte buffers ([lawful-bytes](https://hub.bend-lang.com/name/lawful-bytes)). Each operation
has laws, checked by Bend's proof checker, that state its result on the plain list of bytes: the
fields are the pieces `String.split` would give on the same text, and the numbers are what Base's
`Nat.show` writes. So a parser built on it can be proven against a specification written on
strings, while it runs on packed bytes and never builds a string.

## Use

```python
import lawful-fields@0.1.1.0/fields.bend as F  # the operations
import lawful-fields@0.1.1.0/defs.bend as S    # split, join, dec and the rest, on plain lists
import lawful-fields@0.1.1.0/LAWS.bend as L    # the laws, for your own proofs
import lawful-fields@0.1.1.0/PROOF.bend as P   # their proofs, needed when a proof uses a law
```

A `Bytes` can be used only once, so every read hands the buffer back along with its answer. This
program reads the second tab-separated field of a line as a number:

```python
import Base
import lawful-bytes@0.1.1.0/defs.bend as D
import lawful-bytes@0.1.1.0/bytes.bend as B
import lawful-fields@0.1.1.0/fields.bend as F

# r holds the line and the end offsets of its first two fields.
def second.go(r: D.Bytes & List<&2, U32>) -> Maybe<&2, U32>:
  (b, es) = r
  match es:
    case Con{+e1, t}:
      match t:
        case Con{+e2, u}:
          Pair.snd(D.Bytes, Maybe<&2, U32>, F.num(b, (e1 + 1 : U32), e2))
        case Nil{}:
          None{}
    case Nil{}:
      None{}

# The second tab-separated field of a line of n bytes, read as a number.
def second(b: D.Bytes, +n: U32) -> Maybe<&2, U32>:
  second.go(F.cut(b, 0, n, 9, 2n))

def main() -> Maybe<&2, U32>:
  second(B.of_list(2n, [99, 104, 114, 49, 9, 49, 50, 51, 9, 65, 67]), 11)  # "chr1\t123\tAC"
```

```
$ bend second.bend
Some{123}
```

## What's in it

Offsets are `U32`, ranges are `from .. to-1`, and bytes are `U32`s below 256.

| operation | signature | what it does |
|---|---|---|
| `cut` | `cut(b, from, to, sep, n) -> Bytes & List<U32>` | the end offsets of the first `n` fields of the range, split at `sep`; each field starts just after the previous end |
| `num` | `num(b, from, to) -> Bytes & Maybe<U32>` | the decimal number in the range, or `None` if it is not one or is 2^32 or more |
| `digits` | `digits(b, from, to) -> Bytes & Bool` | the range is one or more digits, a number of any size (tells a too-large number from a non-number) |
| `put_dec` | `put_dec(b, n) -> Bytes` | `n` written in decimal at the end (needs room for 10 bytes) |

The laws are stated with `defs.bend`: `split` (as `String.split`, always at least one piece),
`join`, `dec` (one or more digits, any size) and `text` (bytes as a string, one character per
byte). `cut_view` says the fields `cut` marks are the first `n` pieces of `split`, `num_view` says
`num` agrees with `dec` below 2^32, and `split_text` says splitting bytes is splitting their text.
A law is a function: call it with its arguments and it returns its equation.

```python
# Splitting a line at tabs and joining the fields with tabs gives the line back.
law tabs_rejoin:
  for xs: List<&2, U32>
  {S.join(S.split(xs, 9), 9) == xs : List<&2, U32>}

def tabs_rejoin(xs):
  L.split_join(xs, 9)
```

The laws are proven. Below version 1.0 they have been reviewed by AI models but not yet by a human
expert. [docs/LAWS.md](docs/LAWS.md) lists every law in plain words.

## License

MIT (see `LICENSE`).

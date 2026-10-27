The 8 laws hold of the reference code. Three findings:

1. **`num`** — should fix. `None` means both "not a decimal" and "a decimal that does not fit in a `U32`". `dec` and framebender's `Pos.read` accept the second: `dec([52, 50, 57, 52, 57, 54, 55, 50, 57, 54])` is `Some{2^32}` (the digits of `4294967296`), and `Pos.read` of that text is `Some`, so the record is not malformed. `num` returns `None`, the same answer it gives for `12a3`, for `.`, and for an empty field. A checker that treats `None` as "POS is not a number" rejects a record the String specification keeps. Return three results, with a law for each: not a decimal (`dec` is `None`); fits, and `to_nat` of the `U32` equals that value; digits whose value is at least `2^32`.

2. **`split` and `dec`** — should fix. The comments say `split` mirrors `String.split` and `dec` mirrors `Pos.read`, and `cut_view` stops at `F.split` on the byte list. Nothing in `LAWS.bend` mentions `String` or `Char`, so a proof that the first 8 fields are `String.split(body, '\t')` has no law to cite. The two functions are the same recursion (separator becomes an empty piece, other bytes are prepended to the first piece; `[]` is `[[]]` and `[sep]` is `[[], []]`). Add the bridge, and the same shape for digits:

```bend
def codes(s: String) -> List<&2, U32>:
  match s:
    case SNil{}:
      Nil{}
    case SCon{Chr{+x}, t}:
      x <> codes(t)

def texts(ps: List<&2, List<&2, U32>>) -> List<&2, String>:
  match ps:
    case Nil{}:
      Nil{}
    case p <> t:
      String.from_list(map_chr(p)) <> texts(t)
```

`texts(F.split(codes(s), c)) == String.split(s, Chr{c})`, with `c = 9` for a tab. `cut` with `n = 8` and separator `9` is then the first 8 fields; POS is the second piece, and the bytes after a returned end `e < to` are the rest of the record.

3. **`join`** — minor. The comment calls it split's inverse. `split_join` is only `join(split(xs), sep) == xs`. The other direction fails when a piece contains the separator: `join([[9]], 9)` is `[9]`, and `split([9], 9)` is `[[], []]`. Say that joining the pieces of `split` returns the original list.

# lawful-fields: a guide to the laws

`LAWS.bend` holds 19 laws about cutting a line of packed bytes (lawful-bytes) into fields and
reading and writing decimal numbers.

The laws are stated on plain lists of bytes, against three definitions:
- **`split(xs, sep)`:** mirrors Base's `String.split`. There is always at least one piece, so
  `[]` gives `[[]]` and `[sep]` gives `[[], []]`.
- **`dec(xs)`:** one or more digits, leading zeros allowed, any size. It mirrors framebender's
  `Pos.read`.
- **`decb(xs, bound)`:** `dec`, when the value is below `bound`.

| group | laws | in plain terms |
|---|---|---|
| Cutting | `cut_view`, `cut_ends`, `cut_bounds`, `cut_pair` | `cut(b, from, to, sep, n)` answers the end offsets of the first n pieces of `from .. to-1`. Each end is exactly where split's piece ends (a separator, or `to`), the ends increase, and they delimit the first n pieces of `split` |
| Numbers | `num_view`, `num_pair`, `digits_view`, `digits_pair`, `decb_fits` | `num` reads a decimal number below 2^32. `digits` says the bytes are a number of any size. `num` answers none both for non-numbers and for numbers too large, so `digits` tells them apart |
| Writing numbers | `put_dec_view`, `put_dec_ok` | `put_dec(b, n)` adds n in decimal (Base's `Nat.show`) at the end |
| Lists | `split_length`, `split_join`, `join_at`, `ends_join`, `pieces_length` | split gives one more piece than there are separators; joining the pieces gives the list back; join splits at piece k; end k is the length of the first k+1 pieces joined |
| Text | `split_text`, `join_text`, `text_codes` | splitting bytes is splitting their text, one character per byte: `String.split(text(xs), Chr{sep})` is the texts of `split(xs, sep)`. The same holds for join. This is what connects code on bytes to a String-based specification |

## Where to look hardest

- **`cut_ends` gives exact offsets.** Without it, offsets such as `[0,0,0]` for `[9,9]` would also
  satisfy the other laws (found by GPT).
- **`num` and `digits`.** A VCF POS of 2^32 or more is valid in framebender's spec. A caller must
  check `digits` before treating a None from `num` as "not a number".
- **2^32 appears only in the laws (`Nat.pow(2n, 32n)`), passed to `decb` as its bound.** A bound
  hidden in a definition cannot be proven in Bend (see `../NOTES.md`).

## Left out on purpose

- **A bridge from `dec` to framebender's `Pos.read`:** it belongs to framebender. The digit
  formulas agree on digit bytes.
- **Escaping or quoting (CSV-style):** VCF fields have none.

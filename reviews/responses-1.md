# Round 1: responses (2026-10-27)

Reviewers: Claude (Opus 5.5), GPT (GPT-6.1-Sol), Grok (4.7). No law was false of the reference code.

| finding | raised by | change |
|---|---|---|
| `num` answers None both for non-numbers and for numbers >= 2^32, which framebender's spec accepts (POS "4294967296" is not MALFORMED) | Claude (blocker), Grok, GPT | new `digits` (one or more digits, any size) with `digits_view`, `digits_pair`; callers take a slow path for a large number |
| `cut`'s laws allow wrong offsets (`[0,0,0]` for `[9,9]`) | GPT (blocker) | `cut_ends`: the ends are exactly `F.ends` of split's pieces (def `ends`, `nats`) |
| No bridge from bytes to String | Claude, GPT, Grok | defs `text`, `texts`, `codes` (one Char per byte, as framebender reads files); laws `split_text`, `join_text`, `text_codes` |
| No way to write a decimal number (POS, END) | Claude | `put_dec` with `put_dec_view` (writes `F.show(n)`, Base's `Nat.show`), `put_dec_ok` |
| No law for the range after field k (FORMAT and samples, copied in one append) | Claude | `join_at` (join splits at piece k) and `ends_join` (end k is the length of the first k+1 pieces joined) |
| `pieces_length` helper | Claude | added |
| `join`'s comment called it split's inverse | Claude, Grok | it undoes split one way; comment says so |
| `cut` scanned one field past the last one asked for (for VCF, the whole sample section) | GPT | `cut.next` searches only when another piece is wanted |
| Spot coverage of the cutter's edges, signs, overflow then more digits | GPT | 20 cases added (39 in all, all pass) |

Not taken:
- a `dec_text` bridge to framebender's `Pos.read`: it lives in framebender, and the digit formulas agree on digit bytes (Claude);
- a `num` returning Nat or a pair of words (Claude, alternative): `digits` plus the slow path covers it.

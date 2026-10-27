You are reviewing a draft specification for `lawful-fields`, a small Bend 2 package that will be
published on BendHub. It cuts a line of packed bytes into fields at a separator (TAB for VCF) and
reads decimal numbers, on top of `lawful-bytes` (which you reviewed and accepted). Every law states
the result on the plain list of bytes (`D.view`), against list definitions: `split` mirrors Base's
`String.split` (always at least one piece), `dec` mirrors framebender's `Pos.read` (one or more
digits, leading zeros allowed, any size), `dec32` is `dec` when the value fits a U32. A VCF
normalizer will use it to find CHROM, POS, REF, ALT and the rest of a record, and its proofs will
connect these to its String-based specification.

Read these files in `../lawful-fields` (read-only; do not modify anything):
- `LAWS.bend`: the 8 laws (the main object of review).
- `defs.bend`: `split`, `dec`, `dec32`, `nat_of`, `pieces` (the pieces a list of end offsets
  delimits), `within`, `count`, `join`.
- `fields.bend`: the operations `cut` and `num` (reference versions on lawful-bytes' find and at).
- `test/spot.bend` (`bend test/spot.bend` from `../lawful-fields`): 19 checks, all pass, including
  4294967295 (fits) and 4294967296 (does not). `dec32` is not evaluated there: it compares with
  2^32, and Nat is unary.

Bend notes as before. `Nat.sub` truncates.

For each definition and law, answer:
(a) Does the Bend mean exactly what its English comment says?
(b) Is it true of the code? Counterexamples worked from the code.
(c) Edge cases: an empty range (`from == to`), a range that is one separator, two separators in a
    row, a separator at the end, n = 0, n larger than the number of pieces, numbers with leading
    zeros, the U32 boundary, a lone "-" or "+" (not a number), non-digit bytes.
(d) Is the API enough to split a VCF record into its first 8 fields and read POS, and to prove that
    the result matches `String.split(body, '\t')` on the decoded text? What is missing?

Report a numbered list of findings. For each: the law or definition; severity (blocker / should fix
/ minor); the problem; a concrete example where possible; a suggested fix. Be concrete and brief. If
something is correct, you do not need to say so. End with the full report as your final message.

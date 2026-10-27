# Proof notes: lawful-fields

## Status (2026-10-27)

All 19 laws of `LAWS.bend` are proven. `./check.sh` runs `--check-only` and
then `--verdict`, and both print ALL PROOFS CHECK. Nothing in the import graph
uses `@unsafe` or foreign code. `bend test/spot.bend` is still all True (39
checks). A copy of PROOF.bend with one proof broken on purpose fails, so the
pass is not a cached result. There are about 3100 lines of proof.

Earlier blocker, now resolved: the first statement hid 2^32 inside
`dec32.of`'s body, so no proof could reduce `dec32.of(Some{n})` (the checker
normalizes and expands 2^32; see below). The lead restated it as
`decb(xs, bound)` with `Nat.pow(2n, 32n)` written in the laws (commit
4f61f47). `num_view` and `decb_fits` are proven in that form.

Files:
- `proof_list.bend`: split_length, split_join, split_text, join_text,
  text_codes, join_at, ends_join, pieces_length, decb_fits. `decb_fits_m`
  proves decb_fits for an abstract bound.
- `proof_cut.bend`: cut_view, cut_ends, cut_bounds, cut_pair.
  - `CG` mirrors cut.go as a Data function, and `cg_eq` shows
    `cut.go(...) == (BT, CG(...))`.
  - `sp1`/`sp2` describe split by run_len.
  - pieces and within depend only on the offsets' numbers, so cut_view and
    cut_bounds follow from cut_ends (`pb`, `wl`).
- `proof_num.bend`: num_view, num_pair. The invariant is `Inv(ok, acc, m, M)`,
  with M = 2^32, q = to_nat(429496729) and `10q + 6 == M` all abstract.
  `QM` derives that equation from `to_nat_not_p`/`to_nat_div`/`to_nat_mod`
  on `not(0)`. The overflow test equals `10a + k < M` (`FITSU`/`FITS0`).
- `proof_digits.bend`: digits_view, digits_pair, put_dec_view, put_dec_ok.
  - `go_some` describes digits.
  - `pd_eq` shows put_dec.go is lawful-bytes' of_list loop.
  - `lgo` mirrors Nat.show, and `R` relates put_dec.digits to it.
  - `BK` bounds each step's number by a U32 literal (9, 99, ...,
    `not(0)`), so the 10-step fuel suffices without any number of 2^32 or
    more.
- `PROOF.bend`: forwards the list laws directly. For the laws about a Bytes,
  there is one wrapper each, written mechanically from LAWS.bend, through
  lawful-bytes' mirror (`BC.bmirror`, `BC.tr`). The lawful-bytes proof_core
  is aliased `BC` there, because LAWS.bend's claims use `C` for fields.bend.

## Dependencies used (proof files imported directly; renames break this gate)

- ../lawful-bytes:
  - `proof_core`: `BT`, `AT`, `BMirror`, `bmirror`, `tr`, `at_pair_t`,
    `at_view_t`, `at_val`, `inc_fits`, `add_fits`, ok parts.
  - `proof_ops`: `view_size_t`, `cap_ok_t`, push lemmas.
  - `proof_find`: `find_view_t`, `find_pair_t`.
  - `proof_list`: `first_*`.
  - `proof_seq`: `take_zero`, `take_length` and list facts.
  - `proof_append`: `slice_cons`, `drop_zero`, append lemmas, `le_split`.
  - `proof_shift`: `drop_length`.
  - `proof_same`: `step_val`, `step_inc`, `step_le`, `and_assoc`,
    `lt_of_le`.
  - `proof_grow`: `ol_go_view`, `ol_go_ok`.
- ../lawful-words `proof_nat`, `proof_u32`: add/sub/div/mod facts,
  `is_eq_true`, `to_nat_add_fits_p`, `to_nat_mul_fits_p`, `to_nat_not_p`,
  `to_nat_div`, `to_nat_mod`, `is_lt_to_nat`, `is_le_to_nat`.
- ../lawful-arrays:
  - `proof_base`: `subst`, `false_ne_true`, `lt_zero_absurd`,
    `succ_ne_zero`, `length_append`, `pow_lt`.
  - `proof_tree`.

## Where it got hard (research data)

- **2^32 is untouchable.** bend2 and the kernel normalize both sides of any
  conversion that is not a syntactic identity, and normalizing
  `Nat.pow(2n, 32n)` (or `U32.to_nat` of a big literal such as 429496729)
  next to a variable overflows. One unfold of `Nat.is_lt(n, 2^32)` already
  fails.
  - The fix is the lawful-words pattern taken further. Every lemma takes
    the big numbers as abstract parameters (M, q) with equations, and only
    the top lemma fills them in, in types that match syntactically.
  - This only works when the bound is an argument of a definition, which is
    why dec32 had to become decb.
- **Word literals are cheap.** U32 arithmetic on big literals
  (`U32.div(U32.not(0), 10) == 429496729`) checks by `{==}`, because it
  stays at word level. put_dec's fuel bound and num's overflow constant are
  both handled through such word facts.
- **Loops as Data functions.** As in lawful-bytes' shift and grow, each loop
  (cut.go, put_dec) is mirrored by a function on reusable data plus one
  equation lemma. The invariants then never touch a Bytes.
- **Rewrite direction** remained the most common slip (a handful per file,
  each fixed on the next run). Other slips: annotations on bare constructor
  lets, and wildcards in a multi-value match leaving a def unreduced (split
  on the parameter the def inspects first).
- **Parallel work.** The four groups of laws were proven by forked agents in
  separate files. The lead thread did the setup, the wrappers and the
  integration.
- **Nothing false found.** `sep < 256` (cut) is only forwarded to lawful-bytes'
  `find_view_t`.

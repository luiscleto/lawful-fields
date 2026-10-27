# Proving lawful-fields: brief for the proof agent

## Goal

Prove every law in `LAWS.bend`: 19 laws about cutting a line of packed bytes into fields (`cut`),
reading and writing decimal numbers (`num`, `digits`, `put_dec`), and list and text facts (`split`,
`join`, `ends`, `text`). They hold for the reference operations in `fields.bend`. Three reviewers
accepted the statements, so they are frozen: never edit `LAWS.bend`, `defs.bend` or `fields.bend`.
If a law looks false or unprovable as stated, stop and report it with the reason.

Proofs go in `PROOF.bend` plus helper files `proof_*.bend`, with a `check.sh` copied from
`../lawful-bytes` (`--check-only`, then `--verdict`; both ALL PROOFS CHECK, no `@unsafe`, no foreign
code). `bend test/spot.bend` must stay all True.

## What you can use

All three dependencies are fully proven:
- `../lawful-words`;
- `../lawful-arrays`;
- `../lawful-bytes`. You know it best: `find_view`, `first_*`, `at_view`, `push_view`, the pair
  laws.

Import their proof files as you did for lawful-bytes. List the names you use in your notes.

## Hints

- `cut_view` / `cut_ends`: `cut.go` is induction on n. Each step is one `B.find` whose answer
  `first_*` describes; `cut.next` skips the search when no more pieces are wanted.
- `split_text`, `join_text`, `text_codes` are structural inductions; `split` and `String.split`
  have the same shape.
- 2^32 appears in `dec32` and `num` (overflow): keep it abstract, as lawful-words' notes explain.

## Bend proof notes (from the framebender and minebender proofs)

- `%e : G` rewrites with `e : {new == old}`: `G` is the goal with `_` where `old` is; the rest of the
  def proves `G` with `new` there. Use `Equal.sym` to turn an equation around. `Equal.trans`,
  `Equal.cong` are in Base. Rewrite direction was the most frequent error in every earlier proof.
- `match` only inspects parameters or pattern-bound variables; a computed value needs a helper def
  that takes it as a parameter. Matches follow parameter order (`match a b:` for both). No match
  after a let.
- No mutual recursion, no forward references (define helpers first). Termination: the first argument
  that changes must shrink structurally; put it first. Eliminators take the induction hypothesis
  as a function argument.
- Unfilled laws are dead claims: a proof cannot call an open law. Prove in dependency order.
- A law's `for x` without `+` cannot be reused in its proof: restate with `+` where needed (same
  statement otherwise). Every equation used twice needs `+`. Function-typed hypotheses are affine.
- Refuting `{True{} == False{}}` or `{1n+n == 0n}`: rewrite through a `disc` motive that sends one
  constructor to `Empty` and the other to `Unit`, answer `Unit{}`.
- `Bool.pick`, `&&`, `||` evaluate both sides; to reason about them, case-split.
- Recursive defs do not unfold on variables: a lemma about `f(x)` for variable `x` needs a case
  split on `x` first.
- `?name` prints the goal at that point; `?TODO` leaves a hole. Errors print expected/observed terms.
- Every operator needs its type: `(a + b : U32)`. Bare constructors in a let need an annotation.
- `../framebender/proof_base.bend` and `../framebender/proof_machine_nat.bend` have proven Nat and
  Word facts you may copy (same author; MIT). `String.eq` soundness down to `Word.cmp` was proven
  there twice.

## Rules

- Use `nice -n 19` and a `timeout` for every check. No benchmarks. `fb-bytes` benchmarks on this
  machine, so keep heavy checks to one at a time.
- Never edit files in the dependencies.
- No git commits; the lead commits.
- Keep `notes/proof.md`. Stop when every law is proven and both gate commands pass, or after about
  four hours, and report:
  - what is proven;
  - what is left, and why;
  - any law you believe is false or unusable as stated.

import Base
import ../lawful-words/defs.bend as W
import ../lawful-bytes/defs.bend as D

# lawful-fields definitions: splitting a list of bytes and reading decimal
# numbers, as plain list functions. The operations on packed bytes are in
# fields.bend, the laws in LAWS.bend.

def split.push(+c: U32, ps: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match ps:
    case Nil{}:
      [[c]]
    case Con{h, t}:
      Con{Con{c, h}, t}

def split.fin(+c: U32, r: List<&2, List<&2, U32>>, cut: Bool) -> List<&2, List<&2, U32>>:
  match cut:
    case False{}:
      split.push(c, r)
    case True{}:
      Con{Nil{}, r}

# The pieces of xs between separators, as Base's String.split does for text:
# always at least one piece, so [] gives [[]] and [sep] gives [[], []].
def split(xs: List<&2, U32>, +sep: U32) -> List<&2, List<&2, U32>>:
  match xs:
    case Nil{}:
      [Nil{}]
    case Con{+x, t}:
      split.fin(x, split(t, sep), U32.is_eq(x, sep))

def digit.if(+x: U32, ok: Bool) -> Maybe<&2, Nat>:
  match ok:
    case True{}:
      Some{Nat.sub(U32.to_nat(x), 48n)}
    case False{}:
      None{}

# The value of a decimal digit byte ('0' is 48).
def digit(+x: U32) -> Maybe<&2, Nat>:
  digit.if(x, U32.is_ge(x, 48) && U32.is_le(x, 57))

def dec.push(acc: Maybe<&2, Nat>, d: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match acc d:
    case Some{a} Some{k}:
      Some{Nat.add(Nat.mul(a, 10n), k)}
    case _ _:
      None{}

def dec.go(xs: List<&2, U32>, acc: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match xs:
    case Nil{}:
      acc
    case Con{x, t}:
      dec.go(t, dec.push(acc, digit(x)))

# A decimal number: one or more digits (leading zeros allowed), nothing else;
# any size (framebender's Pos.read on text is the same function).
def dec(xs: List<&2, U32>) -> Maybe<&2, Nat>:
  match xs:
    case Nil{}:
      None{}
    case Con{x, t}:
      dec.go(Con{x, t}, Some{0n})

def dec32.if(+n: Nat, fits: Bool) -> Maybe<&2, Nat>:
  match fits:
    case True{}:
      Some{n}
    case False{}:
      None{}

def dec32.of(m: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match m:
    case Some{+n}:
      dec32.if(n, Nat.is_lt(n, Nat.pow(2n, 32n)))
    case None{}:
      None{}

# A decimal number below 2^32 (what fits a U32); None otherwise.
def dec32(xs: List<&2, U32>) -> Maybe<&2, Nat>:
  dec32.of(dec(xs))

# The number a Maybe<U32> stands for.
def nat_of(m: Maybe<&2, U32>) -> Maybe<&2, Nat>:
  match m:
    case Some{x}:
      Some{U32.to_nat(x)}
    case None{}:
      None{}

# The pieces of xs that end at each offset of es, the first starting at from
# and each next one just after the previous end (where the separator was).
def pieces(es: List<&2, U32>, +xs: List<&2, U32>, +from: Nat) -> List<&2, List<&2, U32>>:
  match es:
    case Nil{}:
      Nil{}
    case Con{+e, t}:
      Con{D.slice(xs, from, Nat.sub(U32.to_nat(e), from)), pieces(t, xs, Nat.add(U32.to_nat(e), 1n))}

# Every offset in es lies in from .. to.
def within(es: List<&2, U32>, +from: Nat, +to: Nat) -> Bool:
  match es:
    case Nil{}:
      True{}
    case Con{+e, t}:
      (Nat.is_le(from, U32.to_nat(e)) && Nat.is_le(U32.to_nat(e), to)) && within(t, from, to)

def count.if(hit: Bool, +n: Nat) -> Nat:
  match hit:
    case True{}:
      Nat.add(1n, n)
    case False{}:
      n

# How many times sep occurs in xs.
def count(xs: List<&2, U32>, +sep: U32) -> Nat:
  match xs:
    case Nil{}:
      0n
    case Con{+x, t}:
      count.if(U32.is_eq(x, sep), count(t, sep))

def join.go(ps: List<&2, List<&2, U32>>, +sep: U32) -> List<&2, U32>:
  match ps:
    case Nil{}:
      Nil{}
    case Con{p, t}:
      Con{sep, List.append(&2, U32, p, join.go(t, sep))}

# The pieces joined with sep between them. join undoes split:
# join(split(xs, sep), sep) == xs (the other way round fails when a piece holds
# sep).
def join(ps: List<&2, List<&2, U32>>, +sep: U32) -> List<&2, U32>:
  match ps:
    case Nil{}:
      Nil{}
    case Con{p, t}:
      List.append(&2, U32, p, join.go(t, sep))

# Bytes as text and back: one Char per byte (Chr{b}), with no decoding (the
# way framebender reads files). For text whose characters are all below 256.
def text(xs: List<&2, U32>) -> String:
  match xs:
    case Nil{}:
      SNil{}
    case Con{x, t}:
      SCon{Chr{x}, text(t)}

def texts(ps: List<&2, List<&2, U32>>) -> List<&2, String>:
  match ps:
    case Nil{}:
      Nil{}
    case Con{p, t}:
      Con{text(p), texts(t)}

def codes(s: String) -> List<&2, U32>:
  match s:
    case SNil{}:
      Nil{}
    case SCon{c, t}:
      Con{Char.to_u32(c), codes(t)}

# The decimal digits of a number, as bytes (Base's Nat.show).
def show(n: U32) -> List<&2, U32>:
  codes(Nat.show(U32.to_nat(n)))

# The end offset of each piece, the first piece starting at from and each next
# one just after the previous end.
def ends(ps: List<&2, List<&2, U32>>, +from: Nat) -> List<&2, Nat>:
  match ps:
    case Nil{}:
      Nil{}
    case Con{p, t}:
      +e = Nat.add(from, List.length(&2, U32, p))
      Con{e, ends(t, Nat.add(e, 1n))}

# The numbers words stand for.
def nats(es: List<&2, U32>) -> List<&2, Nat>:
  match es:
    case Nil{}:
      Nil{}
    case Con{e, t}:
      Con{U32.to_nat(e), nats(t)}

# xs is one or more digits (any value).
def all_digits(xs: List<&2, U32>) -> Bool:
  Maybe.is_some(&2, Nat, dec(xs))

import Base
import lawful-bytes@0.1.0.0/defs.bend as D
import lawful-bytes@0.1.0.0/bytes.bend as B

# lawful-fields operations on packed bytes: cutting a line into fields at a
# separator, and reading a decimal number. Reference versions, built on
# lawful-bytes' find and at.

def cut.cons(+e: U32, r: D.Bytes & List<&2, U32>) -> D.Bytes & List<&2, U32>:
  (b, t) = r
  (b, Con{e, t})

# The end of the piece starting at from, searched only when want is set (no
# scan past the last field asked for; the answer is then unused).
def cut.next(want: Bool, b: D.Bytes, +from: U32, +to: U32, +sep: U32) -> D.Bytes & U32:
  match want:
    case True{}:
      B.find(b, from, to, sep)
    case False{}:
      (b, to)

# n counts the pieces still wanted, this one included; more says the previous
# piece ended at a separator; r holds this piece's end.
def cut.go(+n: Nat, more: Bool, r: D.Bytes & U32, +to: U32, +sep: U32) -> D.Bytes & List<&2, U32>:
  match n more:
    case 0n _:
      (b, e) = r
      (b, Nil{})
    case 1n+m False{}:
      (b, e) = r
      (b, Nil{})
    case 1n+m True{}:
      (b, +e) = r
      +go = U32.is_lt(e, to)
      cut.cons(e, cut.go(m, go, cut.next(go && Bool.not(Nat.is_eq(m, 0n)), b, (e + 1 : U32), to, sep), to, sep))

# The end offsets of the first n pieces of bytes from .. to-1, split at sep:
# each end is where a separator is, or to for the last piece.
def cut(b: D.Bytes, +from: U32, +to: U32, +sep: U32, +n: Nat) -> D.Bytes & List<&2, U32>:
  cut.go(n, True{}, cut.next(Bool.not(Nat.is_eq(n, 0n)), b, from, to, sep), to, sep)

def num.fin(+acc: U32, ok: Bool) -> Maybe<&2, U32>:
  match ok:
    case True{}:
      Some{acc}
    case False{}:
      None{}

def num.out(+acc: U32, ok: Bool, r: D.Bytes & U32) -> D.Bytes & Maybe<&2, U32>:
  (b, x) = r
  (b, num.fin(acc, ok))

# r holds byte j; acc is the value so far; ok says every byte was a digit and
# nothing overflowed.
def num.go(n: Nat, r: D.Bytes & U32, +j: U32, +acc: U32, ok: Bool) -> D.Bytes & Maybe<&2, U32>:
  match n:
    case 0n:
      num.out(acc, ok, r)
    case 1n+m:
      (b, +x) = r
      +d = (x - 48 : U32)
      +digit = U32.is_ge(x, 48) && U32.is_le(x, 57)
      +fits = U32.is_lt(acc, 429496729) || (U32.is_eq(acc, 429496729) && U32.is_le(d, 5))
      num.go(m, B.at(b, (j + 1 : U32)), (j + 1 : U32), ((acc * 10 : U32) + d : U32), ok && (digit && fits))

# The decimal number in bytes from .. to-1, if it is one and below 2^32.
def num(b: D.Bytes, +from: U32, +to: U32) -> D.Bytes & Maybe<&2, U32>:
  num.go(Nat.sub(U32.to_nat(to), U32.to_nat(from)), B.at(b, from), from, 0, U32.is_lt(from, to))

def digits.out(ok: Bool, r: D.Bytes & U32) -> D.Bytes & Bool:
  (b, x) = r
  (b, ok)

# r holds byte j; ok says every byte so far was a digit.
def digits.go(n: Nat, r: D.Bytes & U32, +j: U32, ok: Bool) -> D.Bytes & Bool:
  match n:
    case 0n:
      digits.out(ok, r)
    case 1n+m:
      (b, +x) = r
      digits.go(m, B.at(b, (j + 1 : U32)), (j + 1 : U32), ok && (U32.is_ge(x, 48) && U32.is_le(x, 57)))

# Bytes from .. to-1 are one or more decimal digits (a number of any size).
def digits(b: D.Bytes, +from: U32, +to: U32) -> D.Bytes & Bool:
  digits.go(Nat.sub(U32.to_nat(to), U32.to_nat(from)), B.at(b, from), from, U32.is_lt(from, to))

def put_dec.go(xs: List<&2, U32>, b: D.Bytes) -> D.Bytes:
  match xs:
    case Nil{}:
      b
    case Con{x, t}:
      put_dec.go(t, B.push(b, x))

# The decimal digits of n, most significant first, before acc; small says
# n < 10 (the last digit). At most 10 steps for a U32.
def put_dec.digits(k: Nat, small: Bool, +n: U32, acc: List<&2, U32>) -> List<&2, U32>:
  match k small:
    case _ True{}:
      Con{(n + 48 : U32), acc}
    case 0n False{}:
      acc
    case 1n+m False{}:
      put_dec.digits(m, U32.is_lt((n / 10 : U32), 10), (n / 10 : U32), Con{((n % 10 : U32) + 48 : U32), acc})

def put_dec.list(+n: U32) -> List<&2, U32>:
  put_dec.digits(10n, U32.is_lt(n, 10), n, Nil{})

# n written in decimal at the end of b (for room enough: at most 10 bytes).
def put_dec(b: D.Bytes, +n: U32) -> D.Bytes:
  put_dec.go(put_dec.list(n), b)

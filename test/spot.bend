import Base
import ../../lawful-bytes/defs.bend as D
import ../../lawful-bytes/bytes.bend as B
import ../defs.bend as F
import ../fields.bend as C

# Spot checks (decb with bound 2^32 compares with a unary Nat too large to evaluate,
# so it is not evaluated here) on a VCF-like line: "chr1\t123\t.\tAC\tA\n" (and variants).

def line() -> D.Bytes:
  B.of_list(3n, [99, 104, 114, 49, 9, 49, 50, 51, 9, 46, 9, 65, 67, 9, 65, 10])

def eql(xs: List<&2, U32>, ys: List<&2, U32>) -> Bool:
  D.list_eq(xs, ys)

def eqll(xs: List<&2, List<&2, U32>>, ys: List<&2, List<&2, U32>>) -> Bool:
  match xs ys:
    case Nil{} Nil{}:
      True{}
    case Con{x, xt} Con{y, yt}:
      eql(x, y) && eqll(xt, yt)
    case Nil{} Con{y, yt}:
      False{}
    case Con{x, xt} Nil{}:
      False{}

def eqmn(x: Maybe<&2, Nat>, y: Maybe<&2, Nat>) -> Bool:
  match x y:
    case Some{a} Some{b}:
      Nat.is_eq(a, b)
    case None{} None{}:
      True{}
    case Some{a} None{}:
      False{}
    case None{} Some{b}:
      False{}

def eqmu(x: Maybe<&2, U32>, y: Maybe<&2, U32>) -> Bool:
  match x y:
    case Some{a} Some{b}:
      U32.is_eq(a, b)
    case None{} None{}:
      True{}
    case Some{a} None{}:
      False{}
    case None{} Some{b}:
      False{}

def ends(n: Nat, to: U32) -> List<&2, U32>:
  Pair.snd(D.Bytes, List<&2, U32>, C.cut(line(), 0, to, 9, n))

def numof(from: U32, to: U32) -> Maybe<&2, Nat>:
  F.nat_of(Pair.snd(D.Bytes, Maybe<&2, U32>, C.num(line(), from, to)))

def nb(xs: List<&2, U32>) -> D.Bytes:
  B.of_list(3n, xs)

def cutl(xs: List<&2, U32>, from: U32, to: U32, n: Nat) -> List<&2, U32>:
  Pair.snd(D.Bytes, List<&2, U32>, C.cut(nb(xs), from, to, 9, n))

def dig(xs: List<&2, U32>, from: U32, to: U32) -> Bool:
  Pair.snd(D.Bytes, Bool, C.digits(nb(xs), from, to))

def main() -> List<Bool>:
  [ eql(ends(8n, 15), [4, 8, 10, 13, 15])
  , eql(ends(2n, 15), [4, 8])
  , eql(ends(0n, 15), [])
  , eqll(F.pieces(ends(8n, 15), D.view(line()), 0n), List.take(&2, List<&2, U32>, F.split(D.slice(D.view(line()), 0n, 15n), 9), 8n))
  , eqll(F.split([1, 9, 9, 2], 9), [[1], [], [2]])
  , eqll(F.split([], 9), [[]])
  , eqll(F.split([9], 9), [[], []])
  , eql(Pair.snd(D.Bytes, List<&2, U32>, C.cut(line(), 5, 5, 9, 3n)), [5])
  , eqmn(numof(5, 8), Some{123n})
  , eqmn(numof(5, 8), F.dec(D.slice(D.view(line()), 5n, 3n)))
  , eqmn(numof(4, 8), None{})
  , eqmn(numof(5, 5), None{})
  , eqmu(Pair.snd(D.Bytes, Maybe<&2, U32>, C.num(nb([52, 50, 57, 52, 57, 54, 55, 50, 57, 53]), 0, 10)), Some{4294967295})
  , eqmu(Pair.snd(D.Bytes, Maybe<&2, U32>, C.num(nb([52, 50, 57, 52, 57, 54, 55, 50, 57, 54]), 0, 10)), None{})
  , eqmn(F.nat_of(Pair.snd(D.Bytes, Maybe<&2, U32>, C.num(nb([48, 48, 55]), 0, 3))), Some{7n})
  , eqmn(F.dec([49, 50]), Some{12n})
  , Nat.is_eq(F.count([1, 9, 9, 2], 9), 2n)
  , eql(F.join(F.split([1, 9, 9, 2], 9), 9), [1, 9, 9, 2])
  , F.within(ends(8n, 15), 0n, 15n)
    , eql(cutl([9], 0, 1, 5n), [0, 1])
  , eql(cutl([9, 9], 0, 2, 5n), [0, 1, 2])
  , eql(cutl([65, 9], 0, 2, 5n), [1, 2])
  , eql(cutl([65, 9, 66, 9, 67], 2, 5, 5n), [3, 5])
  , eql(cutl([65, 9, 66, 9, 67], 0, 5, 1n), [1])
  , eqmu(Pair.snd(D.Bytes, Maybe<&2, U32>, C.num(nb([43, 49]), 0, 2)), None{})
  , eqmu(Pair.snd(D.Bytes, Maybe<&2, U32>, C.num(nb([45, 49]), 0, 2)), None{})
  , eqmu(Pair.snd(D.Bytes, Maybe<&2, U32>, C.num(nb([49, 50, 97]), 0, 3)), None{})
  , eqmu(Pair.snd(D.Bytes, Maybe<&2, U32>, C.num(nb([57, 57, 57, 57, 57, 57, 57, 57, 57, 57, 49]), 0, 11)), None{})
  , dig([52, 50, 57, 52, 57, 54, 55, 50, 57, 54], 0, 10)
  , Bool.not(dig([49, 50, 97], 0, 3))
  , Bool.not(dig([49], 0, 0))
  , dig([48, 48, 55], 0, 3)
  , eql(D.view(C.put_dec(B.empty(3n), 0)), [48])
  , eql(D.view(C.put_dec(B.empty(3n), 123)), [49, 50, 51])
  , eql(D.view(C.put_dec(B.empty(3n), 4294967295)), [52, 50, 57, 52, 57, 54, 55, 50, 57, 53])
  , eql(D.view(C.put_dec(nb([65]), 70)), [65, 55, 48])
  , String.eq(String.join(F.texts(F.split([65, 9, 66], 9)), "\t"), F.text([65, 9, 66]))
  , String.eq(F.text(F.codes("ab")), "ab")
  , Nat.is_eq(List.length(&2, String, String.split(F.text([65, 9, 9, 66]), Chr{9})), List.length(&2, List<&2, U32>, F.split([65, 9, 9, 66], 9)))
  ]

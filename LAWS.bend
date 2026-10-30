import Base
import lawful-bytes@0.1.0.0/defs.bend as D
import ./defs.bend as F
import ./fields.bend as C

# lawful-fields: cutting a line of packed bytes into fields, and reading a
# decimal number, stated on the list of bytes a buffer holds (D.view).

# cut answers the end offsets of the first n pieces of from .. to-1, split at
# sep: the pieces those ends delimit are the first n of F.split.
law cut_view:
  for b: D.Bytes
  for d: Nat
  for from: U32
  for to: U32
  for sep: U32
  for n: Nat
  for h: {D.ok(b, d) == True{} : Bool}
  for hft: {U32.is_le(from, to) == True{} : Bool}
  for ht: {Nat.is_le(U32.to_nat(to), D.size(b)) == True{} : Bool}
  for hs: {U32.is_lt(sep, 256) == True{} : Bool}
  {F.pieces(Pair.snd(D.Bytes, List<&2, U32>, C.cut(b, from, to, sep, n)), D.view(b), U32.to_nat(from)) == List.take(&2, List<&2, U32>, F.split(D.slice(D.view(b), U32.to_nat(from), Nat.sub(U32.to_nat(to), U32.to_nat(from))), sep), n) : List<&2, List<&2, U32>>}

# The ends are exactly where split's pieces end, counted from from (so they
# increase, and each next piece starts just after the previous end).
law cut_ends:
  for b: D.Bytes
  for d: Nat
  for from: U32
  for to: U32
  for sep: U32
  for n: Nat
  for h: {D.ok(b, d) == True{} : Bool}
  for hft: {U32.is_le(from, to) == True{} : Bool}
  for ht: {Nat.is_le(U32.to_nat(to), D.size(b)) == True{} : Bool}
  for hs: {U32.is_lt(sep, 256) == True{} : Bool}
  {F.nats(Pair.snd(D.Bytes, List<&2, U32>, C.cut(b, from, to, sep, n))) == List.take(&2, Nat, F.ends(F.split(D.slice(D.view(b), U32.to_nat(from), Nat.sub(U32.to_nat(to), U32.to_nat(from))), sep), U32.to_nat(from)), n) : List<&2, Nat>}

# Every end lies in from .. to.
law cut_bounds:
  for b: D.Bytes
  for d: Nat
  for from: U32
  for to: U32
  for sep: U32
  for n: Nat
  for h: {D.ok(b, d) == True{} : Bool}
  for hft: {U32.is_le(from, to) == True{} : Bool}
  for ht: {Nat.is_le(U32.to_nat(to), D.size(b)) == True{} : Bool}
  for hs: {U32.is_lt(sep, 256) == True{} : Bool}
  {F.within(Pair.snd(D.Bytes, List<&2, U32>, C.cut(b, from, to, sep, n)), U32.to_nat(from), U32.to_nat(to)) == True{} : Bool}

law cut_pair:
  for b: D.Bytes
  for from: U32
  for to: U32
  for sep: U32
  for n: Nat
  {C.cut(b, from, to, sep, n) == (b, Pair.snd(D.Bytes, List<&2, U32>, C.cut(b, from, to, sep, n))) : D.Bytes & List<&2, U32>}

# num reads the decimal number in from .. to-1 when it is one and fits a U32.
law num_view:
  for b: D.Bytes
  for d: Nat
  for from: U32
  for to: U32
  for h: {D.ok(b, d) == True{} : Bool}
  for hft: {U32.is_le(from, to) == True{} : Bool}
  for ht: {Nat.is_le(U32.to_nat(to), D.size(b)) == True{} : Bool}
  {F.nat_of(Pair.snd(D.Bytes, Maybe<&2, U32>, C.num(b, from, to))) == F.decb(D.slice(D.view(b), U32.to_nat(from), Nat.sub(U32.to_nat(to), U32.to_nat(from))), Nat.pow(2n, 32n)) : Maybe<&2, Nat>}

law num_pair:
  for b: D.Bytes
  for from: U32
  for to: U32
  {C.num(b, from, to) == (b, Pair.snd(D.Bytes, Maybe<&2, U32>, C.num(b, from, to))) : D.Bytes & Maybe<&2, U32>}

# The number of pieces split gives is one more than the number of separators.
law split_length:
  for xs: List<&2, U32>
  for sep: U32
  {List.length(&2, List<&2, U32>, F.split(xs, sep)) == Nat.add(F.count(xs, sep), 1n) : Nat}

# Joining the pieces with the separator gives xs back.
law split_join:
  for xs: List<&2, U32>
  for sep: U32
  {F.join(F.split(xs, sep), sep) == xs : List<&2, U32>}

# digits says the bytes are one or more decimal digits, a number of any size
# (num answers None both for non-numbers and for numbers of 2^32 or more).
law digits_view:
  for b: D.Bytes
  for d: Nat
  for from: U32
  for to: U32
  for h: {D.ok(b, d) == True{} : Bool}
  for hft: {U32.is_le(from, to) == True{} : Bool}
  for ht: {Nat.is_le(U32.to_nat(to), D.size(b)) == True{} : Bool}
  {Pair.snd(D.Bytes, Bool, C.digits(b, from, to)) == F.all_digits(D.slice(D.view(b), U32.to_nat(from), Nat.sub(U32.to_nat(to), U32.to_nat(from)))) : Bool}

law digits_pair:
  for b: D.Bytes
  for from: U32
  for to: U32
  {C.digits(b, from, to) == (b, Pair.snd(D.Bytes, Bool, C.digits(b, from, to))) : D.Bytes & Bool}

# put_dec writes n in decimal at the end (room for 10 more bytes needed).
law put_dec_view:
  for b: D.Bytes
  for d: Nat
  for n: U32
  for h: {D.ok(b, d) == True{} : Bool}
  for hc: {Nat.is_le(Nat.add(D.size(b), 10n), D.cap(b)) == True{} : Bool}
  {D.view(C.put_dec(b, n)) == List.append(&2, U32, D.view(b), F.show(n)) : List<&2, U32>}

law put_dec_ok:
  for b: D.Bytes
  for d: Nat
  for n: U32
  for h: {D.ok(b, d) == True{} : Bool}
  for hc: {Nat.is_le(Nat.add(D.size(b), 10n), D.cap(b)) == True{} : Bool}
  {D.ok(C.put_dec(b, n), d) == True{} : Bool}

# ==========================================================================
# Text (one Char per byte): what the bytes mean to a String-based spec
# ==========================================================================

# Splitting bytes is splitting their text.
law split_text:
  for xs: List<&2, U32>
  for sep: U32
  {String.split(F.text(xs), Chr{sep}) == F.texts(F.split(xs, sep)) : List<&2, String>}

# Joining bytes is joining their text.
law join_text:
  for ps: List<&2, List<&2, U32>>
  for sep: U32
  {F.text(F.join(ps, sep)) == String.join(F.texts(ps), F.text([sep])) : String}

law text_codes:
  for s: String
  {F.text(F.codes(s)) == s : String}

# Joining a list of pieces splits at piece k: the first k+1 pieces, the
# separator, the rest.
law join_at:
  for ps: List<&2, List<&2, U32>>
  for sep: U32
  for k: Nat
  for h: {Nat.is_lt(Nat.add(k, 1n), List.length(&2, List<&2, U32>, ps)) == True{} : Bool}
  {F.join(ps, sep) == List.append(&2, U32, F.join(List.take(&2, List<&2, U32>, ps, Nat.add(k, 1n)), sep), Con{sep, F.join(List.drop(&2, List<&2, U32>, ps, Nat.add(k, 1n)), sep)}) : List<&2, U32>}

# Piece k ends at the k-th end: the first k+1 pieces joined, from from.
law ends_join:
  for ps: List<&2, List<&2, U32>>
  for sep: U32
  for from: Nat
  for k: Nat
  for h: {Nat.is_lt(k, List.length(&2, List<&2, U32>, ps)) == True{} : Bool}
  {List.get(&2, Nat, F.ends(ps, from), k) == Some{Nat.add(from, List.length(&2, U32, F.join(List.take(&2, List<&2, U32>, ps, Nat.add(k, 1n)), sep)))} : Maybe<&2, Nat>}

law pieces_length:
  for es: List<&2, U32>
  for xs: List<&2, U32>
  for from: Nat
  {List.length(&2, List<&2, U32>, F.pieces(es, xs, from)) == List.length(&2, U32, es) : Nat}

# decb (with bound 2^32) is dec when the number fits.
law decb_fits:
  for xs: List<&2, U32>
  for n: Nat
  for h: {F.dec(xs) == Some{n} : Maybe<&2, Nat>}
  for hn: {Nat.is_lt(n, Nat.pow(2n, 32n)) == True{} : Bool}
  {F.decb(xs, Nat.pow(2n, 32n)) == Some{n} : Maybe<&2, Nat>}

import Base
import lawful-bytes@0.1.1.0/defs.bend as D
import lawful-bytes@0.1.1.0/bytes.bend as B
import ./defs.bend as F
import ./fields.bend as FC
import lawful-bytes@0.1.1.0/proof_seq.bend as Q
import lawful-bytes@0.1.1.0/proof_core.bend as C
import lawful-bytes@0.1.1.0/proof_ops.bend as O
import lawful-bytes@0.1.1.0/proof_same.bend as SM
import lawful-bytes@0.1.1.0/proof_shift.bend as H
import lawful-bytes@0.1.1.0/proof_grow.bend as G
import lawful-words@0.1.0.0/proof_nat.bend as N
import lawful-words@0.1.0.0/proof_u32.bend as U
import lawful-arrays@0.1.0.0/proof_base.bend as AB
import lawful-arrays@0.1.0.0/proof_tree.bend as P

# digits and put_dec on the mirror C.BT(len, t) (named `name_t` as in
# lawful-bytes@0.1.1.0/proof_ops.bend).

# digits
# ======

# Every element is a digit byte (48 to 57).
def alld(xs: List<&2, U32>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+x, t}:
      Bool.and(Bool.and(U32.is_ge(x, 48), U32.is_le(x, 57)), alld(t))

law and_true:
  for +a: Bool
  {Bool.and(a, True{}) == a : Bool}

def and_true(a):
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

law push_some:
  for +a: Nat
  for +x: U32
  for +b: Bool
  {Maybe.is_some(&2, Nat, F.dec.push(Some{a}, F.digit.if(x, b))) == b : Bool}

def push_some(a, x, b):
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

law push_and:
  for +m: Maybe<&2, Nat>
  for +x: U32
  for +r: Bool
  {Bool.and(Maybe.is_some(&2, Nat, F.dec.push(m, F.digit(x))), r) == Bool.and(Bool.and(Maybe.is_some(&2, Nat, m), Bool.and(U32.is_ge(x, 48), U32.is_le(x, 57))), r) : Bool}

def push_and(m, x, r):
  match m:
    case None{}:
      {==}
    case Some{+a}:
      +isd = Bool.and(U32.is_ge(x, 48), U32.is_le(x, 57))
      %Equal.sym(Bool, Maybe.is_some(&2, Nat, F.dec.push(Some{a}, F.digit.if(x, isd))), isd, push_some(a, x, isd)) :
        {Bool.and(_, r) == Bool.and(Bool.and(True{}, isd), r) : Bool}
      {==}

# dec.go keeps a value exactly while every byte is a digit.
law go_some:
  for +ys: List<&2, U32>
  for +m: Maybe<&2, Nat>
  {Maybe.is_some(&2, Nat, F.dec.go(ys, m)) == Bool.and(Maybe.is_some(&2, Nat, m), alld(ys)) : Bool}

def go_some(ys, m):
  match ys:
    case Nil{}:
      Equal.sym(Bool, Bool.and(Maybe.is_some(&2, Nat, m), True{}), Maybe.is_some(&2, Nat, m), and_true(Maybe.is_some(&2, Nat, m)))
    case Con{+x, t}:
      +isd = Bool.and(U32.is_ge(x, 48), U32.is_le(x, 57))
      +m2 = F.dec.push(m, F.digit(x))
      %Equal.sym(Bool, Maybe.is_some(&2, Nat, F.dec.go(t, m2)), Bool.and(Maybe.is_some(&2, Nat, m2), alld(t)), go_some(t, m2)) :
        {_ == Bool.and(Maybe.is_some(&2, Nat, m), Bool.and(isd, alld(t))) : Bool}
      %SM.and_assoc(Maybe.is_some(&2, Nat, m), isd, alld(t)) :
        {Bool.and(Maybe.is_some(&2, Nat, m2), alld(t)) == _ : Bool}
      push_and(m, x, alld(t))

law ne_dec:
  for +ys: List<&2, U32>
  for +h: {Nat.is_lt(0n, List.length(&2, U32, ys)) == True{} : Bool}
  {Maybe.is_some(&2, Nat, F.dec(ys)) == alld(ys) : Bool}

def ne_dec(ys, h):
  match ys:
    case Nil{}:
      Empty.absurd({Maybe.is_some(&2, Nat, F.dec(Nil{})) == alld(Nil{}) : Bool}, AB.false_ne_true(h))
    case Con{+y, t}:
      go_some(y <> t, Some{0n})

law dg_pair:
  for +n: Nat
  for +len: U32
  for +t: P.Tree<U32>
  for +j: U32
  for +ok: Bool
  {FC.digits.go(n, B.at(C.BT(len, t), j), j, ok) == (C.BT(len, t), Pair.snd(D.Bytes, Bool, FC.digits.go(n, B.at(C.BT(len, t), j), j, ok))) : D.Bytes & Bool}

def dg_pair(n, len, t, j, ok):
  match n:
    case 0n:
      %Equal.sym(D.Bytes & U32, B.at(C.BT(len, t), j), (C.BT(len, t), C.AT(len, t, j)), C.at_pair_t(len, t, j)) :
        {FC.digits.go(0n, _, j, ok) == (C.BT(len, t), Pair.snd(D.Bytes, Bool, FC.digits.go(0n, _, j, ok))) : D.Bytes & Bool}
      {==}
    case 1n+m:
      +x = C.AT(len, t, j)
      %Equal.sym(D.Bytes & U32, B.at(C.BT(len, t), j), (C.BT(len, t), x), C.at_pair_t(len, t, j)) :
        {FC.digits.go(1n+m, _, j, ok) == (C.BT(len, t), Pair.snd(D.Bytes, Bool, FC.digits.go(1n+m, _, j, ok))) : D.Bytes & Bool}
      dg_pair(m, len, t, (j + 1 : U32), Bool.and(ok, Bool.and(U32.is_ge(x, 48), U32.is_le(x, 57))))

law dg_view:
  for +n: Nat
  for +len: U32
  for +t: P.Tree<U32>
  for +d: Nat
  for +j: U32
  for +ok: Bool
  for +h: {D.ok(C.BT(len, t), d) == True{} : Bool}
  for +hs: {Nat.is_le(Nat.add(U32.to_nat(j), n), U32.to_nat(len)) == True{} : Bool}
  {Pair.snd(D.Bytes, Bool, FC.digits.go(n, B.at(C.BT(len, t), j), j, ok)) == Bool.and(ok, alld(D.slice(D.view(C.BT(len, t)), U32.to_nat(j), n))) : Bool}

def dg_view(n, len, t, d, j, ok, h, hs):
  match n:
    case 0n:
      +X = List.drop(&2, U32, D.view(C.BT(len, t)), U32.to_nat(j))
      %Equal.sym(D.Bytes & U32, B.at(C.BT(len, t), j), (C.BT(len, t), C.AT(len, t, j)), C.at_pair_t(len, t, j)) :
        {Pair.snd(D.Bytes, Bool, FC.digits.go(0n, _, j, ok)) == Bool.and(ok, alld(List.take(&2, U32, X, 0n))) : Bool}
      %Equal.sym(List<&2, U32>, List.take(&2, U32, X, 0n), Nil{}, Q.take_zero(X)) : {ok == Bool.and(ok, alld(_)) : Bool}
      Equal.sym(Bool, Bool.and(ok, True{}), ok, and_true(ok))
    case 1n+m:
      +x = C.AT(len, t, j)
      +j1 = (j + 1 : U32)
      +isd = Bool.and(U32.is_ge(x, 48), U32.is_le(x, 57))
      +xs = D.view(C.BT(len, t))
      +RHS = Bool.and(ok, alld(D.slice(xs, U32.to_nat(j), 1n+m)))
      %Equal.sym(D.Bytes & U32, B.at(C.BT(len, t), j), (C.BT(len, t), x), C.at_pair_t(len, t, j)) :
        {Pair.snd(D.Bytes, Bool, FC.digits.go(1n+m, _, j, ok)) == RHS : Bool}
      %Equal.sym(Bool, Pair.snd(D.Bytes, Bool, FC.digits.go(m, B.at(C.BT(len, t), j1), j1, Bool.and(ok, isd))),
        Bool.and(Bool.and(ok, isd), alld(D.slice(xs, U32.to_nat(j1), m))),
        dg_view(m, len, t, d, j1, Bool.and(ok, isd), h, SM.step_le(len, t, d, j, m, h, hs))) :
        {_ == RHS : Bool}
      %Equal.sym(List<&2, U32>, D.slice(xs, U32.to_nat(j), 1n+m), x <> D.slice(xs, Nat.add(U32.to_nat(j), 1n), m),
        SM.slice_cons(xs, U32.to_nat(j), m, x, SM.step_val(len, t, d, j, m, h, hs))) :
        {Bool.and(Bool.and(ok, isd), alld(D.slice(xs, U32.to_nat(j1), m))) == Bool.and(ok, alld(_)) : Bool}
      %Equal.sym(Nat, U32.to_nat(j1), Nat.add(U32.to_nat(j), 1n), SM.step_inc(len, t, d, j, m, h, hs)) :
        {Bool.and(Bool.and(ok, isd), alld(D.slice(xs, _, m))) == Bool.and(ok, Bool.and(isd, alld(D.slice(xs, Nat.add(U32.to_nat(j), 1n), m)))) : Bool}
      SM.and_assoc(ok, isd, alld(D.slice(xs, Nat.add(U32.to_nat(j), 1n), m)))

law digits_pair_t:
  for +len: U32
  for +t: P.Tree<U32>
  for +from: U32
  for +to: U32
  {FC.digits(C.BT(len, t), from, to) == (C.BT(len, t), Pair.snd(D.Bytes, Bool, FC.digits(C.BT(len, t), from, to))) : D.Bytes & Bool}

def digits_pair_t(len, t, from, to):
  dg_pair(Nat.sub(U32.to_nat(to), U32.to_nat(from)), len, t, from, U32.is_lt(from, to))

# The start test of digits against the slice it reads.
law dtop:
  for +n: Nat
  for +from: U32
  for +to: U32
  for +xs: List<&2, U32>
  for +hn: {Nat.sub(U32.to_nat(to), U32.to_nat(from)) == n : Nat}
  for +hle: {Nat.is_le(U32.to_nat(from), U32.to_nat(to)) == True{} : Bool}
  for +hlen: {Nat.is_le(Nat.add(U32.to_nat(from), n), List.length(&2, U32, xs)) == True{} : Bool}
  {Bool.and(U32.is_lt(from, to), alld(D.slice(xs, U32.to_nat(from), n))) == Maybe.is_some(&2, Nat, F.dec(D.slice(xs, U32.to_nat(from), n))) : Bool}

def dtop(n, from, to, xs, hn, hle, hlen):
  match n:
    case 0n:
      +FF = U32.to_nat(from)
      +TT = U32.to_nat(to)
      +X = List.drop(&2, U32, xs, FF)
      +e1 = AB.subst(Nat, y => {Nat.add(FF, y) == TT : Nat}, Nat.sub(TT, FF), 0n, hn, N.le_sub_add(FF, TT, hle))
      +eFT = Equal.trans(Nat, FF, Nat.add(FF, 0n), TT, Equal.sym(Nat, Nat.add(FF, 0n), FF, N.add_zero(FF)), e1)
      +hlt = Equal.trans(Bool, U32.is_lt(from, to), Nat.is_lt(FF, TT), False{}, U.is_lt_to_nat(from, to),
        AB.subst(Nat, y => {Nat.is_lt(FF, y) == False{} : Bool}, FF, TT, eFT, N.lt_irrefl(FF)))
      %Equal.sym(List<&2, U32>, List.take(&2, U32, X, 0n), Nil{}, Q.take_zero(X)) :
        {Bool.and(U32.is_lt(from, to), alld(_)) == Maybe.is_some(&2, Nat, F.dec(_)) : Bool}
      %Equal.sym(Bool, U32.is_lt(from, to), False{}, hlt) : {Bool.and(_, True{}) == False{} : Bool}
      {==}
    case 1n+k:
      +FF = U32.to_nat(from)
      +TT = U32.to_nat(to)
      +X = List.drop(&2, U32, xs, FF)
      +S = D.slice(xs, FF, 1n+k)
      +e1 = AB.subst(Nat, y => {Nat.add(FF, y) == TT : Nat}, Nat.sub(TT, FF), 1n+k, hn, N.le_sub_add(FF, TT, hle))
      +hlt = Equal.trans(Bool, U32.is_lt(from, to), Nat.is_lt(FF, TT), True{}, U.is_lt_to_nat(from, to),
        SM.lt_of_le(FF, k, TT, AB.subst(Nat, y => {Nat.is_le(y, TT) == True{} : Bool}, TT, Nat.add(FF, 1n+k),
          Equal.sym(Nat, Nat.add(FF, 1n+k), TT, e1), N.le_refl(TT))))
      +hx = AB.subst(Nat, y => {Nat.is_le(1n+k, y) == True{} : Bool}, Nat.sub(List.length(&2, U32, xs), FF), List.length(&2, U32, X),
        Equal.sym(Nat, List.length(&2, U32, X), Nat.sub(List.length(&2, U32, xs), FF), H.drop_length(xs, FF)),
        N.le_sub_r(FF, 1n+k, List.length(&2, U32, xs), hlen))
      +hne = AB.subst(Nat, y => {Nat.is_lt(0n, y) == True{} : Bool}, 1n+k, List.length(&2, U32, S),
        Equal.sym(Nat, List.length(&2, U32, S), 1n+k, Q.take_length(X, 1n+k, hx)), {==})
      %Equal.sym(Bool, U32.is_lt(from, to), True{}, hlt) : {Bool.and(_, alld(S)) == Maybe.is_some(&2, Nat, F.dec(S)) : Bool}
      Equal.sym(Bool, Maybe.is_some(&2, Nat, F.dec(S)), alld(S), ne_dec(S, hne))

law digits_view_t:
  for +len: U32
  for +t: P.Tree<U32>
  for +d: Nat
  for +from: U32
  for +to: U32
  for +h: {D.ok(C.BT(len, t), d) == True{} : Bool}
  for +hft: {U32.is_le(from, to) == True{} : Bool}
  for +ht: {Nat.is_le(U32.to_nat(to), D.size(C.BT(len, t))) == True{} : Bool}
  {Pair.snd(D.Bytes, Bool, FC.digits(C.BT(len, t), from, to)) == F.all_digits(D.slice(D.view(C.BT(len, t)), U32.to_nat(from), Nat.sub(U32.to_nat(to), U32.to_nat(from)))) : Bool}

def digits_view_t(len, t, d, from, to, h, hft, ht):
  +FF = U32.to_nat(from)
  +TT = U32.to_nat(to)
  +NN = Nat.sub(TT, FF)
  +xs = D.view(C.BT(len, t))
  +hle = Equal.trans(Bool, Nat.is_le(FF, TT), U32.is_le(from, to), True{}, Equal.sym(Bool, U32.is_le(from, to), Nat.is_le(FF, TT), U.is_le_to_nat(from, to)), hft)
  +eFT = N.le_sub_add(FF, TT, hle)
  +hs = AB.subst(Nat, y => {Nat.is_le(y, U32.to_nat(len)) == True{} : Bool}, TT, Nat.add(FF, NN), Equal.sym(Nat, Nat.add(FF, NN), TT, eFT), ht)
  +hlen = AB.subst(Nat, y => {Nat.is_le(Nat.add(FF, NN), y) == True{} : Bool}, U32.to_nat(len), List.length(&2, U32, xs),
    Equal.sym(Nat, List.length(&2, U32, xs), U32.to_nat(len), O.view_size_t(len, t, d, h)), hs)
  Equal.trans(Bool, Pair.snd(D.Bytes, Bool, FC.digits(C.BT(len, t), from, to)), Bool.and(U32.is_lt(from, to), alld(D.slice(xs, FF, NN))),
    Maybe.is_some(&2, Nat, F.dec(D.slice(xs, FF, NN))),
    dg_view(NN, len, t, d, from, U32.is_lt(from, to), h, hs), dtop(NN, from, to, xs, {==}, hle, hlen))

# put_dec: the decimal digits
# ===========================

law eta_nn:
  for p: Nat & Nat
  {p == (Pair.fst(Nat, Nat, p), Pair.snd(Nat, Nat, p)) : Nat & Nat}

def eta_nn(p):
  (a, b) = p
  {==}

# The byte of the last decimal digit of x.
def DG(+x: Nat) -> U32:
  U32.from_nat(Nat.add(48n, Nat.mod(x, 10n)))

# Nat.show.fin as a list: d is the digit just produced, q what is left.
def lgo(f: Nat, +q: Nat, +d: U32, acc: List<&2, U32>) -> List<&2, U32>:
  match f q:
    case _ 0n:
      d <> acc
    case 0n 1n+p:
      d <> acc
    case 1n+g 1n+p:
      lgo(g, Nat.div(1n+p, 10n), DG(1n+p), d <> acc)

law show_fin:
  for +g: Nat
  for +q: Nat
  for +d: U32
  for +sacc: String
  {F.codes(Nat.show.fin(g, sacc, (Chr{d}, q))) == lgo(g, q, d, F.codes(sacc)) : List<&2, U32>}

def show_fin(g, q, d, sacc):
  match g q:
    case _ 0n:
      {==}
    case 0n 1n+p:
      {==}
    case 1n+h 1n+p:
      +S = {SCon{Chr{d}, sacc} : String}
      %Equal.sym(Nat & Nat, Nat.divmod(1n+p, 10n), (Nat.div(1n+p, 10n), Nat.mod(1n+p, 10n)), eta_nn(Nat.divmod(1n+p, 10n))) :
        {F.codes(Nat.show.fin(h, S, Nat.show.put(_))) == lgo(1n+h, 1n+p, d, F.codes(sacc)) : List<&2, U32>}
      show_fin(h, Nat.div(1n+p, 10n), DG(1n+p), S)

law show_lgo:
  for +m: Nat
  {F.codes(Nat.show(m)) == lgo(m, Nat.div(m, 10n), DG(m), Nil{}) : List<&2, U32>}

def show_lgo(m):
  %Equal.sym(Nat & Nat, Nat.divmod(m, 10n), (Nat.div(m, 10n), Nat.mod(m, 10n)), eta_nn(Nat.divmod(m, 10n))) :
    {F.codes(Nat.show.fin(m, SNil{}, Nat.show.put(_))) == lgo(m, Nat.div(m, 10n), DG(m), Nil{}) : List<&2, U32>}
  show_fin(m, Nat.div(m, 10n), DG(m), SNil{})

# A bound on n when put_dec.digits has fuel k: 10^(k+1) - 1, capped at the
# largest U32 from k = 9 on (all word constants, never a Nat above 2^32).
def BK(k: Nat) -> U32:
  match k:
    case 0n:
      9
    case 1n+a0:
      match a0:
        case 0n:
          99
        case 1n+a1:
          match a1:
            case 0n:
              999
            case 1n+a2:
              match a2:
                case 0n:
                  9999
                case 1n+a3:
                  match a3:
                    case 0n:
                      99999
                    case 1n+a4:
                      match a4:
                        case 0n:
                          999999
                        case 1n+a5:
                          match a5:
                            case 0n:
                              9999999
                            case 1n+a6:
                              match a6:
                                case 0n:
                                  99999999
                                case 1n+a7:
                                  match a7:
                                    case 0n:
                                      999999999
                                    case 1n+a8:
                                      U32.not(0)

law bk_step:
  for +k: Nat
  {U32.is_le(U32.div(BK(1n+k), 10), BK(k)) == True{} : Bool}

def bk_step(k):
  match k:
    case 0n:
      {==}
    case 1n+a0:
      match a0:
        case 0n:
          {==}
        case 1n+a1:
          match a1:
            case 0n:
              {==}
            case 1n+a2:
              match a2:
                case 0n:
                  {==}
                case 1n+a3:
                  match a3:
                    case 0n:
                      {==}
                    case 1n+a4:
                      match a4:
                        case 0n:
                          {==}
                        case 1n+a5:
                          match a5:
                            case 0n:
                              {==}
                            case 1n+a6:
                              match a6:
                                case 0n:
                                  {==}
                                case 1n+a7:
                                  match a7:
                                    case 0n:
                                      {==}
                                    case 1n+a8:
                                      {==}

# Digit bytes as numbers
# ======================

law s48:
  for +r: Nat
  for +hr: {Nat.is_lt(r, 10n) == True{} : Bool}
  {Nat.is_le(Nat.add(r, 48n), Nat.pow(2n, 6n)) == True{} : Bool}

def s48(r, hr):
  %N.add_comm(48n, r) : {Nat.is_le(_, Nat.pow(2n, 6n)) == True{} : Bool}
  N.le_trans(r, 10n, 16n, N.lt_to_le(r, 10n, hr), {==})

# Below 64 is below 2^32 (2^32 only meets itself: pow_lt is symbolic).
law fits64:
  for +x: Nat
  for +hx: {Nat.is_le(x, Nat.pow(2n, 6n)) == True{} : Bool}
  {Nat.is_lt(x, Nat.pow(2n, 32n)) == True{} : Bool}

def fits64(x, hx):
  N.le_lt_trans(x, Nat.pow(2n, 6n), Nat.pow(2n, 32n), hx, AB.pow_lt(6n, 32n, {==}))

law dgv:
  for +x: Nat
  {U32.to_nat(DG(x)) == Nat.add(48n, Nat.mod(x, 10n)) : Nat}

def dgv(x):
  +X = Nat.add(48n, Nat.mod(x, 10n))
  +hx = N.le_trans(Nat.mod(x, 10n), 10n, 16n, N.lt_to_le(Nat.mod(x, 10n), 10n, N.mod_lt(x, 10n, {==})), {==})
  Equal.trans(Nat, U32.to_nat(U32.from_nat(X)), Nat.mod(X, Nat.pow(2n, 32n)), X, U.to_nat_from_nat_p(X), U.wrap_small_p(X, fits64(X, hx)))

law dg_lt:
  for +x: Nat
  {U32.is_lt(DG(x), 256) == True{} : Bool}

def dg_lt(x):
  %Equal.sym(Bool, U32.is_lt(DG(x), 256), Nat.is_lt(U32.to_nat(DG(x)), U32.to_nat(256)), U.is_lt_to_nat(DG(x), 256)) : {_ == True{} : Bool}
  %Equal.sym(Nat, U32.to_nat(DG(x)), Nat.add(48n, Nat.mod(x, 10n)), dgv(x)) : {Nat.is_lt(_, U32.to_nat(256)) == True{} : Bool}
  N.lt_trans(Nat.mod(x, 10n), 10n, 208n, N.mod_lt(x, 10n, {==}), {==})

law dg_eq_n:
  for +n: U32
  {U32.to_nat(U32.add(U32.mod(n, 10), 48)) == U32.to_nat(DG(U32.to_nat(n))) : Nat}

def dg_eq_n(n):
  +m = U32.to_nat(n)
  +r = U32.to_nat(U32.mod(n, 10))
  +er = U.to_nat_mod(n, 10)
  +hr = AB.subst(Nat, y => {Nat.is_lt(y, 10n) == True{} : Bool}, Nat.mod(m, 10n), r, Equal.sym(Nat, r, Nat.mod(m, 10n), er), N.mod_lt(m, 10n, {==}))
  +ea = U.to_nat_add_fits_p(U32.mod(n, 10), 48, fits64(Nat.add(U32.to_nat(U32.mod(n, 10)), U32.to_nat(48)), s48(r, hr)))
  %Equal.sym(Nat, U32.to_nat(DG(m)), Nat.add(48n, Nat.mod(m, 10n)), dgv(m)) : {U32.to_nat(U32.add(U32.mod(n, 10), 48)) == _ : Nat}
  %Equal.sym(Nat, U32.to_nat(U32.add(U32.mod(n, 10), 48)), Nat.add(r, U32.to_nat(48)), ea) : {_ == Nat.add(48n, Nat.mod(m, 10n)) : Nat}
  %Equal.sym(Nat, r, Nat.mod(m, 10n), er) : {Nat.add(_, U32.to_nat(48)) == Nat.add(48n, Nat.mod(m, 10n)) : Nat}
  N.add_comm(Nat.mod(m, 10n), 48n)

# The digit byte put_dec writes is DG.
law dg_eq:
  for +n: U32
  {U32.add(U32.mod(n, 10), 48) == DG(U32.to_nat(n)) : U32}

def dg_eq(n):
  U.to_nat_inj(U32.add(U32.mod(n, 10), 48), DG(U32.to_nat(n)), dg_eq_n(n))

law lt10:
  for +n: U32
  for +hs: {U32.is_lt(n, 10) == True{} : Bool}
  {Nat.is_lt(U32.to_nat(n), 10n) == True{} : Bool}

def lt10(n, hs):
  Equal.trans(Bool, Nat.is_lt(U32.to_nat(n), U32.to_nat(10)), U32.is_lt(n, 10), True{},
    Equal.sym(Bool, U32.is_lt(n, 10), Nat.is_lt(U32.to_nat(n), U32.to_nat(10)), U.is_lt_to_nat(n, 10)), hs)

law ge10:
  for +n: U32
  for +hs: {U32.is_lt(n, 10) == False{} : Bool}
  {Nat.is_lt(U32.to_nat(n), 10n) == False{} : Bool}

def ge10(n, hs):
  Equal.trans(Bool, Nat.is_lt(U32.to_nat(n), U32.to_nat(10)), U32.is_lt(n, 10), False{},
    Equal.sym(Bool, U32.is_lt(n, 10), Nat.is_lt(U32.to_nat(n), U32.to_nat(10)), U.is_lt_to_nat(n, 10)), hs)

law dg_small_n:
  for +n: U32
  for +hs: {U32.is_lt(n, 10) == True{} : Bool}
  {U32.to_nat(U32.add(n, 48)) == U32.to_nat(DG(U32.to_nat(n))) : Nat}

def dg_small_n(n, hs):
  +m = U32.to_nat(n)
  +hm = lt10(n, hs)
  +ea = U.to_nat_add_fits_p(n, 48, fits64(Nat.add(U32.to_nat(n), U32.to_nat(48)), s48(m, hm)))
  %Equal.sym(Nat, U32.to_nat(DG(m)), Nat.add(48n, Nat.mod(m, 10n)), dgv(m)) : {U32.to_nat(U32.add(n, 48)) == _ : Nat}
  %Equal.sym(Nat, U32.to_nat(U32.add(n, 48)), Nat.add(m, U32.to_nat(48)), ea) : {_ == Nat.add(48n, Nat.mod(m, 10n)) : Nat}
  %Equal.sym(Nat, Nat.mod(m, 10n), m, N.mod_small(m, 10n, hm)) : {Nat.add(m, U32.to_nat(48)) == Nat.add(48n, _) : Nat}
  N.add_comm(m, 48n)

law dg_small:
  for +n: U32
  for +hs: {U32.is_lt(n, 10) == True{} : Bool}
  {U32.add(n, 48) == DG(U32.to_nat(n)) : U32}

def dg_small(n, hs):
  U.to_nat_inj(U32.add(n, 48), DG(U32.to_nat(n)), dg_small_n(n, hs))

# Bounds for the fuel
# ===================

law lt_add_succ:
  for +p: Nat
  for +y: Nat
  {Nat.is_lt(p, Nat.add(p, 1n+y)) == True{} : Bool}

def lt_add_succ(p, y):
  %Equal.sym(Nat, Nat.add(p, 1n+y), 1n+Nat.add(p, y), N.add_succ(p, y)) : {Nat.is_lt(p, _) == True{} : Bool}
  Equal.trans(Bool, Nat.is_lt(p, 1n+Nat.add(p, y)), Nat.is_le(p, Nat.add(p, y)), True{}, N.lt_succ_iff(p, Nat.add(p, y)), N.le_add_r(p, y))

law dlt:
  for +p: Nat
  {Nat.is_le(Nat.div(1n+p, 10n), p) == True{} : Bool}

def dlt(p):
  +dl = N.div_lt(1n+p, 10n, 1n+p, {==}, lt_add_succ(p, Nat.add(p, Nat.mul(8n, 1n+p))))
  Equal.trans(Bool, Nat.is_le(Nat.div(1n+p, 10n), p), Nat.is_lt(Nat.div(1n+p, 10n), 1n+p), True{},
    Equal.sym(Bool, Nat.is_lt(Nat.div(1n+p, 10n), 1n+p), Nat.is_le(Nat.div(1n+p, 10n), p), N.lt_succ_iff(Nat.div(1n+p, 10n), p)), dl)

law hdm:
  for +m: Nat
  {Nat.is_le(Nat.div(m, 10n), m) == True{} : Bool}

def hdm(m):
  match m:
    case 0n:
      {==}
    case 1n+p:
      N.le_trans(Nat.div(1n+p, 10n), p, 1n+p, dlt(p),
        N.lt_to_le(p, 1n+p, Equal.trans(Bool, Nat.is_lt(p, 1n+p), Nat.is_le(p, p), True{}, N.lt_succ_iff(p, p), N.le_refl(p))))

law div_mono10:
  for +a: Nat
  for +b: Nat
  for +h: {Nat.is_le(a, b) == True{} : Bool}
  {Nat.is_le(Nat.div(a, 10n), Nat.div(b, 10n)) == True{} : Bool}

def div_mono10(a, b, h):
  +x = Nat.div(b, 10n)
  +r = Nat.mod(b, 10n)
  +X = Nat.mul(x, 10n)
  +hb = AB.subst(Nat, y => {Nat.is_lt(y, Nat.add(10n, X)) == True{} : Bool}, Nat.add(r, X), b,
    Equal.trans(Nat, Nat.add(r, X), Nat.add(X, r), b, N.add_comm(r, X), N.div_mod(b, 10n)),
    N.lt_add_mono_r(X, r, 10n, N.mod_lt(b, 10n, {==})))
  +ha = N.le_lt_trans(a, b, Nat.add(10n, X), h, hb)
  +h2 = AB.subst(Nat, y => {Nat.is_lt(a, y) == True{} : Bool}, Nat.mul(1n+x, 10n), Nat.mul(10n, 1n+x),
    Equal.sym(Nat, Nat.mul(10n, 1n+x), Nat.mul(1n+x, 10n), N.mul_comm(10n, 1n+x)), ha)
  +dl = N.div_lt(a, 10n, 1n+x, {==}, h2)
  Equal.trans(Bool, Nat.is_le(Nat.div(a, 10n), x), Nat.is_lt(Nat.div(a, 10n), 1n+x), True{},
    Equal.sym(Bool, Nat.is_lt(Nat.div(a, 10n), 1n+x), Nat.is_le(Nat.div(a, 10n), x), N.lt_succ_iff(Nat.div(a, 10n), x)), dl)

# n <= BK(1 + j) gives n / 10 <= BK(j).
law hk_step:
  for +n: U32
  for +j: Nat
  for +hk: {Nat.is_le(U32.to_nat(n), U32.to_nat(BK(1n+j))) == True{} : Bool}
  {Nat.is_le(U32.to_nat(U32.div(n, 10)), U32.to_nat(BK(j))) == True{} : Bool}

def hk_step(n, j, hk):
  +m = U32.to_nat(n)
  +Bv = U32.to_nat(BK(1n+j))
  +bstep = Equal.trans(Bool, Nat.is_le(U32.to_nat(U32.div(BK(1n+j), 10)), U32.to_nat(BK(j))), U32.is_le(U32.div(BK(1n+j), 10), BK(j)), True{},
    Equal.sym(Bool, U32.is_le(U32.div(BK(1n+j), 10), BK(j)), Nat.is_le(U32.to_nat(U32.div(BK(1n+j), 10)), U32.to_nat(BK(j))),
      U.is_le_to_nat(U32.div(BK(1n+j), 10), BK(j))), bk_step(j))
  %Equal.sym(Nat, U32.to_nat(U32.div(n, 10)), Nat.div(m, U32.to_nat(10)), U.to_nat_div(n, 10)) : {Nat.is_le(_, U32.to_nat(BK(j))) == True{} : Bool}
  N.le_trans(Nat.div(m, 10n), Nat.div(Bv, 10n), U32.to_nat(BK(j)), div_mono10(m, Bv, hk),
    AB.subst(Nat, y => {Nat.is_le(y, U32.to_nat(BK(j))) == True{} : Bool}, U32.to_nat(U32.div(BK(1n+j), 10)), Nat.div(Bv, 10n),
      U.to_nat_div(BK(1n+j), 10), bstep))

law ab0:
  for +n: U32
  for +hs: {U32.is_lt(n, 10) == False{} : Bool}
  for +hk: {Nat.is_le(U32.to_nat(n), U32.to_nat(BK(0n))) == True{} : Bool}
  Empty

def ab0(n, hs, hk):
  AB.false_ne_true(N.le_trans(10n, U32.to_nat(n), U32.to_nat(BK(0n)), N.not_lt_le(U32.to_nat(n), 10n, ge10(n, hs)), hk))

law lmax:
  for +x: Nat
  for +z: Nat
  for +M: Nat
  for +hx: {Nat.is_lt(x, M) == True{} : Bool}
  for +hz: {z == Nat.sub(Nat.sub(M, 1n), U32.to_nat(0)) : Nat}
  {Nat.is_le(x, z) == True{} : Bool}

def lmax(x, z, M, hx, hz):
  match M:
    case 0n:
      Empty.absurd({Nat.is_le(x, z) == True{} : Bool}, AB.lt_zero_absurd(x, hx))
    case 1n+M1:
      %Equal.sym(Nat, z, Nat.sub(Nat.sub(1n+M1, 1n), U32.to_nat(0)), hz) : {Nat.is_le(x, _) == True{} : Bool}
      %Equal.sym(Nat, Nat.sub(Nat.sub(M1, 0n), 0n), Nat.sub(M1, 0n), N.sub_zero(Nat.sub(M1, 0n))) : {Nat.is_le(x, _) == True{} : Bool}
      %Equal.sym(Nat, Nat.sub(M1, 0n), M1, N.sub_zero(M1)) : {Nat.is_le(x, _) == True{} : Bool}
      Equal.trans(Bool, Nat.is_le(x, M1), Nat.is_lt(x, 1n+M1), True{}, Equal.sym(Bool, Nat.is_lt(x, 1n+M1), Nat.is_le(x, M1), N.lt_succ_iff(x, M1)), hx)

# Every word is at most the largest one, BK(k) from k = 9 on.
law hkmax:
  for +n: U32
  {Nat.is_le(U32.to_nat(n), U32.to_nat(U32.not(0))) == True{} : Bool}

def hkmax(n):
  lmax(U32.to_nat(n), U32.to_nat(U32.not(0)), Nat.pow(2n, 32n), U.to_nat_lt_p(n), U.to_nat_not_p(0))

# put_dec.digits against the spec
# ===============================

# With n <= BK(k) the fuel k suffices; q = n / 10 and the spec's fuel f >= q.
law R:
  for +k: Nat
  for +small: Bool
  for +q: Nat
  for +f: Nat
  for +n: U32
  for +acc: List<&2, U32>
  for +hs: {U32.is_lt(n, 10) == small : Bool}
  for +hq: {Nat.div(U32.to_nat(n), 10n) == q : Nat}
  for +hk: {Nat.is_le(U32.to_nat(n), U32.to_nat(BK(k))) == True{} : Bool}
  for +hf: {Nat.is_le(q, f) == True{} : Bool}
  {FC.put_dec.digits(k, small, n, acc) == lgo(f, q, DG(U32.to_nat(n)), acc) : List<&2, U32>}

def R(k, small, q, f, n, acc, hs, hq, hk, hf):
  match k small q f:
    case _ True{} 0n 0n:
      %dg_small(n, hs) : {U32.add(n, 48) <> acc == _ <> acc : List<&2, U32>}
      {==}
    case _ True{} 0n 1n+g:
      %dg_small(n, hs) : {U32.add(n, 48) <> acc == _ <> acc : List<&2, U32>}
      {==}
    case _ True{} 1n+p _:
      +e0 = Equal.trans(Nat, 0n, Nat.div(U32.to_nat(n), 10n), 1n+p,
        Equal.sym(Nat, Nat.div(U32.to_nat(n), 10n), 0n, N.div_small(U32.to_nat(n), 10n, lt10(n, hs))), hq)
      Empty.absurd({FC.put_dec.digits(k, True{}, n, acc) == lgo(f, 1n+p, DG(U32.to_nat(n)), acc) : List<&2, U32>},
        AB.succ_ne_zero(p, Equal.sym(Nat, 0n, 1n+p, e0)))
    case 0n False{} _ _:
      Empty.absurd({FC.put_dec.digits(0n, False{}, n, acc) == lgo(f, q, DG(U32.to_nat(n)), acc) : List<&2, U32>}, ab0(n, hs, hk))
    case 1n+j False{} 0n _:
      +m = U32.to_nat(n)
      +edm = AB.subst(Nat, y => {Nat.add(Nat.mul(y, 10n), Nat.mod(m, 10n)) == m : Nat}, Nat.div(m, 10n), 0n, hq, N.div_mod(m, 10n))
      +hm = AB.subst(Nat, y => {Nat.is_lt(y, 10n) == True{} : Bool}, Nat.mod(m, 10n), m, edm, N.mod_lt(m, 10n, {==}))
      Empty.absurd({FC.put_dec.digits(1n+j, False{}, n, acc) == lgo(f, 0n, DG(m), acc) : List<&2, U32>},
        AB.true_ne_false(Equal.trans(Bool, True{}, Nat.is_lt(m, 10n), False{}, Equal.sym(Bool, Nat.is_lt(m, 10n), True{}, hm), ge10(n, hs))))
    case 1n+j False{} 1n+p 0n:
      Empty.absurd({FC.put_dec.digits(1n+j, False{}, n, acc) == lgo(0n, 1n+p, DG(U32.to_nat(n)), acc) : List<&2, U32>}, AB.false_ne_true(hf))
    case 1n+j False{} 1n+p 1n+g:
      +m = U32.to_nat(n)
      +n1 = U32.div(n, 10)
      +acc1 = {U32.add(U32.mod(n, 10), 48) <> acc : List<&2, U32>}
      +e1 = Equal.trans(Nat, U32.to_nat(n1), Nat.div(m, 10n), 1n+p, U.to_nat_div(n, 10), hq)
      +hf1 = AB.subst(Nat, y => {Nat.is_le(Nat.div(y, 10n), g) == True{} : Bool}, 1n+p, U32.to_nat(n1), Equal.sym(Nat, U32.to_nat(n1), 1n+p, e1),
        N.le_trans(Nat.div(1n+p, 10n), p, g, dlt(p), hf))
      +RHS = lgo(g, Nat.div(1n+p, 10n), DG(1n+p), DG(m) <> acc)
      %Equal.sym(List<&2, U32>, FC.put_dec.digits(j, U32.is_lt(n1, 10), n1, acc1), lgo(g, Nat.div(U32.to_nat(n1), 10n), DG(U32.to_nat(n1)), acc1),
        R(j, U32.is_lt(n1, 10), Nat.div(U32.to_nat(n1), 10n), g, n1, acc1, {==}, {==}, hk_step(n, j, hk), hf1)) :
        {_ == RHS : List<&2, U32>}
      %Equal.sym(Nat, U32.to_nat(n1), 1n+p, e1) : {lgo(g, Nat.div(_, 10n), DG(_), acc1) == RHS : List<&2, U32>}
      %Equal.sym(U32, U32.add(U32.mod(n, 10), 48), DG(m), dg_eq(n)) : {lgo(g, Nat.div(1n+p, 10n), DG(1n+p), _ <> acc) == RHS : List<&2, U32>}
      {==}

law LN:
  for +k: Nat
  for +small: Bool
  for +j: Nat
  for +n: U32
  for +acc: List<&2, U32>
  for +hs: {U32.is_lt(n, 10) == small : Bool}
  for +hk: {Nat.is_le(U32.to_nat(n), U32.to_nat(BK(j))) == True{} : Bool}
  for +hj: {Nat.is_le(j, k) == True{} : Bool}
  {Nat.is_le(List.length(&2, U32, FC.put_dec.digits(k, small, n, acc)), Nat.add(1n+j, List.length(&2, U32, acc))) == True{} : Bool}

def LN(k, small, j, n, acc, hs, hk, hj):
  match k small j:
    case _ True{} _:
      N.le_add_l(List.length(&2, U32, acc), j)
    case 0n False{} 0n:
      Empty.absurd({Nat.is_le(List.length(&2, U32, FC.put_dec.digits(0n, False{}, n, acc)), Nat.add(1n, List.length(&2, U32, acc))) == True{} : Bool},
        ab0(n, hs, hk))
    case 0n False{} 1n+i:
      Empty.absurd({Nat.is_le(List.length(&2, U32, FC.put_dec.digits(0n, False{}, n, acc)), Nat.add(1n+1n+i, List.length(&2, U32, acc))) == True{} : Bool},
        AB.false_ne_true(hj))
    case 1n+k1 False{} 0n:
      Empty.absurd({Nat.is_le(List.length(&2, U32, FC.put_dec.digits(1n+k1, False{}, n, acc)), Nat.add(1n, List.length(&2, U32, acc))) == True{} : Bool},
        ab0(n, hs, hk))
    case 1n+k1 False{} 1n+i:
      +n1 = U32.div(n, 10)
      +acc1 = {U32.add(U32.mod(n, 10), 48) <> acc : List<&2, U32>}
      +L = List.length(&2, U32, acc)
      +len1 = List.length(&2, U32, FC.put_dec.digits(k1, U32.is_lt(n1, 10), n1, acc1))
      AB.subst(Nat, y => {Nat.is_le(len1, 1n+y) == True{} : Bool}, Nat.add(i, 1n+L), 1n+Nat.add(i, L), N.add_succ(i, L),
        LN(k1, U32.is_lt(n1, 10), i, n1, acc1, {==}, hk_step(n, i, hk), hj))

law ab_cons:
  for +n: U32
  for +acc: List<&2, U32>
  for +hacc: {D.all_bytes(acc) == True{} : Bool}
  {D.all_bytes(U32.add(U32.mod(n, 10), 48) <> acc) == True{} : Bool}

def ab_cons(n, acc, hacc):
  %Equal.sym(U32, U32.add(U32.mod(n, 10), 48), DG(U32.to_nat(n)), dg_eq(n)) : {D.all_bytes(_ <> acc) == True{} : Bool}
  %Equal.sym(Bool, U32.is_lt(DG(U32.to_nat(n)), 256), True{}, dg_lt(U32.to_nat(n))) : {Bool.and(_, D.all_bytes(acc)) == True{} : Bool}
  hacc

law AL:
  for +k: Nat
  for +small: Bool
  for +n: U32
  for +acc: List<&2, U32>
  for +hs: {U32.is_lt(n, 10) == small : Bool}
  for +hacc: {D.all_bytes(acc) == True{} : Bool}
  {D.all_bytes(FC.put_dec.digits(k, small, n, acc)) == True{} : Bool}

def AL(k, small, n, acc, hs, hacc):
  match k small:
    case _ True{}:
      %Equal.sym(U32, U32.add(n, 48), DG(U32.to_nat(n)), dg_small(n, hs)) : {D.all_bytes(_ <> acc) == True{} : Bool}
      %Equal.sym(Bool, U32.is_lt(DG(U32.to_nat(n)), 256), True{}, dg_lt(U32.to_nat(n))) : {Bool.and(_, D.all_bytes(acc)) == True{} : Bool}
      hacc
    case 0n False{}:
      hacc
    case 1n+k1 False{}:
      AL(k1, U32.is_lt(U32.div(n, 10), 10), U32.div(n, 10), U32.add(U32.mod(n, 10), 48) <> acc, {==}, ab_cons(n, acc, hacc))

# The list put_dec writes
# =======================

law hkb:
  for +n: U32
  for +r: Nat
  {Nat.is_le(U32.to_nat(n), U32.to_nat(BK(9n+r))) == True{} : Bool}

def hkb(n, r):
  AB.subst(U32, y => {Nat.is_le(U32.to_nat(n), U32.to_nat(y)) == True{} : Bool}, U32.not(0), BK(9n+r), {==}, hkmax(n))

law list_show:
  for +n: U32
  {FC.put_dec.list(n) == F.show(n) : List<&2, U32>}

def list_show(n):
  +m = U32.to_nat(n)
  Equal.trans(List<&2, U32>, FC.put_dec.list(n), lgo(m, Nat.div(m, 10n), DG(m), Nil{}), F.show(n),
    R(10n, U32.is_lt(n, 10), Nat.div(m, 10n), m, n, Nil{}, {==}, {==}, hkb(n, 1n), hdm(m)),
    Equal.sym(List<&2, U32>, F.show(n), lgo(m, Nat.div(m, 10n), DG(m), Nil{}), show_lgo(m)))

law list_len:
  for +n: U32
  {Nat.is_le(List.length(&2, U32, FC.put_dec.list(n)), 10n) == True{} : Bool}

def list_len(n):
  LN(10n, U32.is_lt(n, 10), 9n, n, Nil{}, {==}, hkb(n, 0n), {==})

law list_bytes:
  for +n: U32
  {D.all_bytes(FC.put_dec.list(n)) == True{} : Bool}

def list_bytes(n):
  AL(10n, U32.is_lt(n, 10), n, Nil{}, {==}, {==})

law pd_eq:
  for +xs: List<&2, U32>
  for -b: D.Bytes
  {FC.put_dec.go(xs, b) == B.of_list.go(xs, b) : D.Bytes}

def pd_eq(xs, b):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, t}:
      pd_eq(t, B.push(b, x))

law pd_room:
  for +len: U32
  for +t: P.Tree<U32>
  for +d: Nat
  for +n: U32
  for +h: {D.ok(C.BT(len, t), d) == True{} : Bool}
  for +hc: {Nat.is_le(Nat.add(D.size(C.BT(len, t)), 10n), D.cap(C.BT(len, t))) == True{} : Bool}
  {Nat.is_le(Nat.add(U32.to_nat(len), List.length(&2, U32, FC.put_dec.list(n))), Nat.mul(4n, Nat.pow(2n, d))) == True{} : Bool}

def pd_room(len, t, d, n, h, hc):
  +M = Nat.mul(4n, Nat.pow(2n, d))
  N.le_trans(Nat.add(U32.to_nat(len), List.length(&2, U32, FC.put_dec.list(n))), Nat.add(U32.to_nat(len), 10n), M,
    N.le_add_mono_l(U32.to_nat(len), List.length(&2, U32, FC.put_dec.list(n)), 10n, list_len(n)),
    AB.subst(Nat, y => {Nat.is_le(Nat.add(U32.to_nat(len), 10n), y) == True{} : Bool}, D.cap(C.BT(len, t)), M, O.cap_ok_t(len, t, d, h), hc))

law put_dec_view_t:
  for +len: U32
  for +t: P.Tree<U32>
  for +d: Nat
  for +n: U32
  for +h: {D.ok(C.BT(len, t), d) == True{} : Bool}
  for +hc: {Nat.is_le(Nat.add(D.size(C.BT(len, t)), 10n), D.cap(C.BT(len, t))) == True{} : Bool}
  {D.view(FC.put_dec(C.BT(len, t), n)) == List.append(&2, U32, D.view(C.BT(len, t)), F.show(n)) : List<&2, U32>}

def put_dec_view_t(len, t, d, n, h, hc):
  +L = FC.put_dec.list(n)
  +V = D.view(C.BT(len, t))
  %Equal.sym(D.Bytes, FC.put_dec.go(L, C.BT(len, t)), B.of_list.go(L, C.BT(len, t)), pd_eq(L, C.BT(len, t))) :
    {D.view(_) == List.append(&2, U32, V, F.show(n)) : List<&2, U32>}
  %Equal.sym(List<&2, U32>, D.view(B.of_list.go(L, C.BT(len, t))), List.append(&2, U32, V, L),
    G.ol_go_view(L, len, t, d, h, list_bytes(n), pd_room(len, t, d, n, h, hc))) :
    {_ == List.append(&2, U32, V, F.show(n)) : List<&2, U32>}
  %list_show(n) : {List.append(&2, U32, V, L) == List.append(&2, U32, V, _) : List<&2, U32>}
  {==}

law put_dec_ok_t:
  for +len: U32
  for +t: P.Tree<U32>
  for +d: Nat
  for +n: U32
  for +h: {D.ok(C.BT(len, t), d) == True{} : Bool}
  for +hc: {Nat.is_le(Nat.add(D.size(C.BT(len, t)), 10n), D.cap(C.BT(len, t))) == True{} : Bool}
  {D.ok(FC.put_dec(C.BT(len, t), n), d) == True{} : Bool}

def put_dec_ok_t(len, t, d, n, h, hc):
  +L = FC.put_dec.list(n)
  %Equal.sym(D.Bytes, FC.put_dec.go(L, C.BT(len, t)), B.of_list.go(L, C.BT(len, t)), pd_eq(L, C.BT(len, t))) :
    {D.ok(_, d) == True{} : Bool}
  G.ol_go_ok(L, len, t, d, h, pd_room(len, t, d, n, h, hc))

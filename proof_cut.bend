import Base
import ../lawful-bytes/defs.bend as D
import ../lawful-bytes/bytes.bend as B
import ./defs.bend as F
import ./fields.bend as K
import ../lawful-bytes/proof_seq.bend as S
import ../lawful-bytes/proof_core.bend as C
import ../lawful-bytes/proof_ops.bend as O
import ../lawful-bytes/proof_list.bend as Q
import ../lawful-bytes/proof_append.bend as X
import ../lawful-bytes/proof_shift.bend as H
import ../lawful-bytes/proof_find.bend as FI
import ../lawful-words/proof_nat.bend as N
import ../lawful-words/proof_u32.bend as U
import ../lawful-arrays/proof_base.bend as AB
import ../lawful-arrays/proof_tree.bend as P

# cut on the mirror C.BT(len, t) (lawful-bytes). CG mirrors cut.go as a Data
# function (cg_eq), so the laws are about CG. split is described by run_len
# (sp1, sp2): the first piece ends at the first separator. The ends of
# split(ys) from s determine its pieces (pb) and lie in s .. s + length(ys) (wl).

# Nat and list facts
# ==================

law tz:
  for -A: Data
  for +xs: List<&2, A>
  {List.take(&2, A, xs, 0n) == Nil{} : List<&2, A>}

def tz(A, xs):
  match xs:
    case Nil{}:
      {==}
    case Con{x, t}:
      {==}

def is_nil_t(xs: List<&2, U32>) -> Type:
  match xs:
    case Nil{}:
      Unit
    case Con{x, t}:
      Empty

law nil_cons:
  for -x: U32
  for -t: List<&2, U32>
  for e: {Nil{} == x <> t : List<&2, U32>}
  Empty

def nil_cons(x, t, e):
  %e : is_nil_t(_)
  Unit{}

law le_antisym:
  for +a: Nat
  for +b: Nat
  for +h1: {Nat.is_le(a, b) == True{} : Bool}
  for +h2: {Nat.is_le(b, a) == True{} : Bool}
  {a == b : Nat}

def le_antisym(a, b, h1, h2):
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      Empty.absurd({0n == 1n+q : Nat}, AB.false_ne_true(h2))
    case 1n+p 0n:
      Empty.absurd({1n+p == 0n : Nat}, AB.false_ne_true(h1))
    case 1n+p 1n+q:
      %le_antisym(p, q, h1, h2) : {1n+p == 1n+_ : Nat}
      {==}

# T <= s + r gives T - s <= r.
law sub_le_of:
  for +tt: Nat
  for +s: Nat
  for +r: Nat
  for +h: {Nat.is_le(tt, Nat.add(s, r)) == True{} : Bool}
  {Nat.is_le(Nat.sub(tt, s), r) == True{} : Bool}

def sub_le_of(tt, s, r, h):
  match tt s:
    case 0n _:
      N.le_zero_l(r)
    case 1n+p 0n:
      h
    case 1n+p 1n+q:
      sub_le_of(p, q, r, h)

# s + r < T gives r < T - s.
law lt_sub_of:
  for +s: Nat
  for +r: Nat
  for +tt: Nat
  for +h: {Nat.is_lt(Nat.add(s, r), tt) == True{} : Bool}
  {Nat.is_lt(r, Nat.sub(tt, s)) == True{} : Bool}

def lt_sub_of(s, r, tt, h):
  +h1 = Equal.trans(Bool, Nat.is_le(1n+Nat.add(s, r), tt), Nat.is_lt(Nat.add(s, r), tt), True{}, N.le_succ_lt(Nat.add(s, r), tt), h)
  +h2 = AB.subst(Nat, y => {Nat.is_le(y, tt) == True{} : Bool}, 1n+Nat.add(s, r), Nat.add(s, 1n+r),
    Equal.sym(Nat, Nat.add(s, 1n+r), 1n+Nat.add(s, r), N.add_succ(s, r)), h1)
  Equal.trans(Bool, Nat.is_lt(r, Nat.sub(tt, s)), Nat.is_le(1n+r, Nat.sub(tt, s)), True{},
    Equal.sym(Bool, Nat.is_le(1n+r, Nat.sub(tt, s)), Nat.is_lt(r, Nat.sub(tt, s)), N.le_succ_lt(r, Nat.sub(tt, s))),
    N.le_sub_r(s, 1n+r, tt, h2))

law sub_mono:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  for +h: {Nat.is_le(a, b) == True{} : Bool}
  {Nat.is_le(Nat.sub(a, c), Nat.sub(b, c)) == True{} : Bool}

def sub_mono(a, b, c, h):
  match a b c:
    case 0n _ _:
      N.le_zero_l(Nat.sub(b, c))
    case 1n+p 0n _:
      Empty.absurd({Nat.is_le(Nat.sub(1n+p, c), 0n) == True{} : Bool}, AB.false_ne_true(h))
    case 1n+p 1n+q 0n:
      h
    case 1n+p 1n+q 1n+r:
      sub_mono(p, q, r, h)

law sub_sub:
  for +tt: Nat
  for +s: Nat
  for +k: Nat
  {Nat.sub(Nat.sub(tt, s), k) == Nat.sub(tt, Nat.add(s, k)) : Nat}

def sub_sub(tt, s, k):
  match tt s:
    case 0n _:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      sub_sub(p, q, k)

law drop_drop:
  for +xs: List<&2, U32>
  for +a: Nat
  for +b: Nat
  {List.drop(&2, U32, List.drop(&2, U32, xs, a), b) == List.drop(&2, U32, xs, Nat.add(a, b)) : List<&2, U32>}

def drop_drop(xs, a, b):
  match xs a:
    case Nil{} _:
      {==}
    case Con{x, t} 0n:
      {==}
    case Con{x, t} 1n+p:
      drop_drop(t, p, b)

law drop_take:
  for +zs: List<&2, U32>
  for +n: Nat
  for +k: Nat
  {List.drop(&2, U32, List.take(&2, U32, zs, n), k) == List.take(&2, U32, List.drop(&2, U32, zs, k), Nat.sub(n, k)) : List<&2, U32>}

def drop_take(zs, n, k):
  match zs n k:
    case Nil{} _ _:
      {==}
    case Con{x, t} 0n 0n:
      {==}
    case Con{x, t} 0n 1n+j:
      Equal.sym(List<&2, U32>, List.take(&2, U32, List.drop(&2, U32, t, j), 0n), Nil{}, tz(U32, List.drop(&2, U32, t, j)))
    case Con{x, t} 1n+p 0n:
      {==}
    case Con{x, t} 1n+p 1n+j:
      drop_take(t, p, j)

# A slice dropped by k is the slice from s + k.
law slice_drop:
  for +xs: List<&2, U32>
  for +s: Nat
  for +tt: Nat
  for +k: Nat
  {List.drop(&2, U32, D.slice(xs, s, Nat.sub(tt, s)), k) == D.slice(xs, Nat.add(s, k), Nat.sub(tt, Nat.add(s, k))) : List<&2, U32>}

def slice_drop(xs, s, tt, k):
  %Equal.sym(List<&2, U32>, List.drop(&2, U32, List.take(&2, U32, List.drop(&2, U32, xs, s), Nat.sub(tt, s)), k),
    List.take(&2, U32, List.drop(&2, U32, List.drop(&2, U32, xs, s), k), Nat.sub(Nat.sub(tt, s), k)), drop_take(List.drop(&2, U32, xs, s), Nat.sub(tt, s), k)) :
    {_ == D.slice(xs, Nat.add(s, k), Nat.sub(tt, Nat.add(s, k))) : List<&2, U32>}
  %Equal.sym(List<&2, U32>, List.drop(&2, U32, List.drop(&2, U32, xs, s), k), List.drop(&2, U32, xs, Nat.add(s, k)), drop_drop(xs, s, k)) :
    {List.take(&2, U32, _, Nat.sub(Nat.sub(tt, s), k)) == D.slice(xs, Nat.add(s, k), Nat.sub(tt, Nat.add(s, k))) : List<&2, U32>}
  %Equal.sym(Nat, Nat.sub(Nat.sub(tt, s), k), Nat.sub(tt, Nat.add(s, k)), sub_sub(tt, s, k)) :
    {List.take(&2, U32, List.drop(&2, U32, xs, Nat.add(s, k)), _) == D.slice(xs, Nat.add(s, k), Nat.sub(tt, Nat.add(s, k))) : List<&2, U32>}
  {==}

# split by run_len
# ================

def nn(ps: List<&2, List<&2, U32>>) -> Bool:
  match ps:
    case Nil{}:
      False{}
    case Con{p, t}:
      True{}

law nn_push:
  for +c: U32
  for +ps: List<&2, List<&2, U32>>
  {nn(F.split.push(c, ps)) == True{} : Bool}

def nn_push(c, ps):
  match ps:
    case Nil{}:
      {==}
    case Con{p, t}:
      {==}

law nn_fin:
  for +c: U32
  for +ps: List<&2, List<&2, U32>>
  for +b: Bool
  {nn(F.split.fin(c, ps, b)) == True{} : Bool}

def nn_fin(c, ps, b):
  match b:
    case False{}:
      nn_push(c, ps)
    case True{}:
      {==}

law split_nn:
  for +xs: List<&2, U32>
  for +sep: U32
  {nn(F.split(xs, sep)) == True{} : Bool}

def split_nn(xs, sep):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, t}:
      nn_fin(x, F.split(t, sep), U32.is_eq(x, sep))

law sp1c:
  for +x: U32
  for +t: List<&2, U32>
  for +sep: U32
  for +b: Bool
  for +hb: {U32.is_eq(x, sep) == b : Bool}
  for +h: {Nat.is_lt(D.run_len(x <> t, sep), List.length(&2, U32, x <> t)) == True{} : Bool}
  for ih: {Nat.is_lt(D.run_len(t, sep), List.length(&2, U32, t)) == True{} : Bool} -> {F.split(t, sep) == List.take(&2, U32, t, D.run_len(t, sep)) <> F.split(List.drop(&2, U32, t, Nat.add(D.run_len(t, sep), 1n)), sep) : List<&2, List<&2, U32>>}
  {F.split(x <> t, sep) == List.take(&2, U32, x <> t, D.run_len(x <> t, sep)) <> F.split(List.drop(&2, U32, x <> t, Nat.add(D.run_len(x <> t, sep), 1n)), sep) : List<&2, List<&2, U32>>}

def sp1c(x, t, sep, b, hb, h, ih):
  match b:
    case True{}:
      +R = Nat.add(1n, D.run_len(t, sep))
      %Equal.sym(Bool, U32.is_eq(x, sep), True{}, hb) :
        {F.split.fin(x, F.split(t, sep), _) == List.take(&2, U32, x <> t, Bool.pick(Nat, _, 0n, R)) <> F.split(List.drop(&2, U32, x <> t, Nat.add(Bool.pick(Nat, _, 0n, R), 1n)), sep) : List<&2, List<&2, U32>>}
      %Equal.sym(List<&2, U32>, List.drop(&2, U32, t, 0n), t, X.drop_zero(t)) : {Nil{} <> F.split(t, sep) == Nil{} <> F.split(_, sep) : List<&2, List<&2, U32>>}
      {==}
    case False{}:
      +r = D.run_len(t, sep)
      +R = Nat.add(1n, r)
      %Equal.sym(Bool, U32.is_eq(x, sep), False{}, hb) :
        {F.split.fin(x, F.split(t, sep), _) == List.take(&2, U32, x <> t, Bool.pick(Nat, _, 0n, R)) <> F.split(List.drop(&2, U32, x <> t, Nat.add(Bool.pick(Nat, _, 0n, R), 1n)), sep) : List<&2, List<&2, U32>>}
      +h2 = AB.subst(Bool, y => {Nat.is_lt(Bool.pick(Nat, y, 0n, R), 1n+List.length(&2, U32, t)) == True{} : Bool}, U32.is_eq(x, sep), False{}, hb, h)
      %Equal.sym(List<&2, List<&2, U32>>, F.split(t, sep), List.take(&2, U32, t, r) <> F.split(List.drop(&2, U32, t, Nat.add(r, 1n)), sep), ih(h2)) :
        {F.split.push(x, _) == (x <> List.take(&2, U32, t, r)) <> F.split(List.drop(&2, U32, t, Nat.add(r, 1n)), sep) : List<&2, List<&2, U32>>}
      {==}

# With a separator in ys, the first piece ends at it.
law sp1:
  for +ys: List<&2, U32>
  for +sep: U32
  for +h: {Nat.is_lt(D.run_len(ys, sep), List.length(&2, U32, ys)) == True{} : Bool}
  {F.split(ys, sep) == List.take(&2, U32, ys, D.run_len(ys, sep)) <> F.split(List.drop(&2, U32, ys, Nat.add(D.run_len(ys, sep), 1n)), sep) : List<&2, List<&2, U32>>}

def sp1(ys, sep, h):
  match ys:
    case Nil{}:
      Empty.absurd({F.split(Nil{}, sep) == Nil{} <> F.split(Nil{}, sep) : List<&2, List<&2, U32>>}, AB.false_ne_true(h))
    case Con{+x, t}:
      sp1c(x, t, sep, U32.is_eq(x, sep), {==}, h, hh => sp1(t, sep, hh))

law sp2c:
  for +x: U32
  for +t: List<&2, U32>
  for +sep: U32
  for +b: Bool
  for +hb: {U32.is_eq(x, sep) == b : Bool}
  for +h: {Nat.is_le(List.length(&2, U32, x <> t), D.run_len(x <> t, sep)) == True{} : Bool}
  for ih: {Nat.is_le(List.length(&2, U32, t), D.run_len(t, sep)) == True{} : Bool} -> {F.split(t, sep) == [t] : List<&2, List<&2, U32>>}
  {F.split(x <> t, sep) == [x <> t] : List<&2, List<&2, U32>>}

def sp2c(x, t, sep, b, hb, h, ih):
  match b:
    case True{}:
      +R = Nat.add(1n, D.run_len(t, sep))
      +h2 = AB.subst(Bool, y => {Nat.is_le(1n+List.length(&2, U32, t), Bool.pick(Nat, y, 0n, R)) == True{} : Bool}, U32.is_eq(x, sep), True{}, hb, h)
      Empty.absurd({F.split(x <> t, sep) == [x <> t] : List<&2, List<&2, U32>>}, AB.false_ne_true(h2))
    case False{}:
      +R = Nat.add(1n, D.run_len(t, sep))
      +h2 = AB.subst(Bool, y => {Nat.is_le(1n+List.length(&2, U32, t), Bool.pick(Nat, y, 0n, R)) == True{} : Bool}, U32.is_eq(x, sep), False{}, hb, h)
      %Equal.sym(Bool, U32.is_eq(x, sep), False{}, hb) : {F.split.fin(x, F.split(t, sep), _) == [x <> t] : List<&2, List<&2, U32>>}
      %Equal.sym(List<&2, List<&2, U32>>, F.split(t, sep), [t], ih(h2)) : {F.split.push(x, _) == [x <> t] : List<&2, List<&2, U32>>}
      {==}

# Without one, split gives ys itself.
law sp2:
  for +ys: List<&2, U32>
  for +sep: U32
  for +h: {Nat.is_le(List.length(&2, U32, ys), D.run_len(ys, sep)) == True{} : Bool}
  {F.split(ys, sep) == [ys] : List<&2, List<&2, U32>>}

def sp2(ys, sep, h):
  match ys:
    case Nil{}:
      {==}
    case Con{+x, t}:
      sp2c(x, t, sep, U32.is_eq(x, sep), {==}, h, hh => sp2(t, sep, hh))

# Pieces and bounds from ends
# ===========================

# pieces and within read only the numbers of their offsets.
def PN(ns: List<&2, Nat>, +xs: List<&2, U32>, +from: Nat) -> List<&2, List<&2, U32>>:
  match ns:
    case Nil{}:
      Nil{}
    case Con{+e, t}:
      Con{D.slice(xs, from, Nat.sub(e, from)), PN(t, xs, Nat.add(e, 1n))}

def WN(ns: List<&2, Nat>, +from: Nat, +to: Nat) -> Bool:
  match ns:
    case Nil{}:
      True{}
    case Con{+e, t}:
      (Nat.is_le(from, e) && Nat.is_le(e, to)) && WN(t, from, to)

law pn:
  for +es: List<&2, U32>
  for +xs: List<&2, U32>
  for +from: Nat
  {F.pieces(es, xs, from) == PN(F.nats(es), xs, from) : List<&2, List<&2, U32>>}

def pn(es, xs, from):
  match es:
    case Nil{}:
      {==}
    case Con{+e, t}:
      +a = Nat.add(U32.to_nat(e), 1n)
      +S0 = D.slice(xs, from, Nat.sub(U32.to_nat(e), from))
      %pn(t, xs, a) : {Con{S0, F.pieces(t, xs, a)} == Con{S0, _} : List<&2, List<&2, U32>>}
      {==}

law wn:
  for +es: List<&2, U32>
  for +a: Nat
  for +b: Nat
  {F.within(es, a, b) == WN(F.nats(es), a, b) : Bool}

def wn(es, a, b):
  match es:
    case Nil{}:
      {==}
    case Con{+e, t}:
      +X0 = Nat.is_le(a, U32.to_nat(e)) && Nat.is_le(U32.to_nat(e), b)
      %wn(t, a, b) : {Bool.and(X0, F.within(t, a, b)) == Bool.and(X0, _) : Bool}
      {==}

law pntake:
  for +ns: List<&2, Nat>
  for +n: Nat
  for +xs: List<&2, U32>
  for +s: Nat
  {PN(List.take(&2, Nat, ns, n), xs, s) == List.take(&2, List<&2, U32>, PN(ns, xs, s), n) : List<&2, List<&2, U32>>}

def pntake(ns, n, xs, s):
  match ns n:
    case Nil{} _:
      {==}
    case Con{e, t} 0n:
      {==}
    case Con{+e, t} 1n+m:
      +S0 = D.slice(xs, s, Nat.sub(e, s))
      %pntake(t, m, xs, Nat.add(e, 1n)) :
        {Con{S0, PN(List.take(&2, Nat, t, m), xs, Nat.add(e, 1n))} == Con{S0, _} : List<&2, List<&2, U32>>}
      {==}

law wtake:
  for +ns: List<&2, Nat>
  for +n: Nat
  for +a: Nat
  for +b: Nat
  for +hw: {WN(ns, a, b) == True{} : Bool}
  {WN(List.take(&2, Nat, ns, n), a, b) == True{} : Bool}

def wtake(ns, n, a, b, hw):
  match ns n:
    case Nil{} _:
      {==}
    case Con{e, t} 0n:
      {==}
    case Con{+e, t} 1n+m:
      +X0 = Nat.is_le(a, e) && Nat.is_le(e, b)
      %Equal.sym(Bool, X0, True{}, AB.and_true_l(X0, WN(t, a, b), hw)) :
        {Bool.and(_, WN(List.take(&2, Nat, t, m), a, b)) == True{} : Bool}
      wtake(t, m, a, b, AB.and_true_r(X0, WN(t, a, b), hw))

# A lower bound may be lowered.
law wk:
  for +ns: List<&2, Nat>
  for +a: Nat
  for +a2: Nat
  for +b: Nat
  for +h: {Nat.is_le(a, a2) == True{} : Bool}
  for +hw: {WN(ns, a2, b) == True{} : Bool}
  {WN(ns, a, b) == True{} : Bool}

def wk(ns, a, a2, b, h, hw):
  match ns:
    case Nil{}:
      {==}
    case Con{+e, t}:
      +X2 = Nat.is_le(a2, e) && Nat.is_le(e, b)
      +hx = AB.and_true_l(X2, WN(t, a2, b), hw)
      %Equal.sym(Bool, Nat.is_le(a, e), True{}, N.le_trans(a, a2, e, h, AB.and_true_l(Nat.is_le(a2, e), Nat.is_le(e, b), hx))) :
        {Bool.and(Bool.and(_, Nat.is_le(e, b)), WN(t, a, b)) == True{} : Bool}
      %Equal.sym(Bool, Nat.is_le(e, b), True{}, AB.and_true_r(Nat.is_le(a2, e), Nat.is_le(e, b), hx)) :
        {Bool.and(Bool.and(True{}, _), WN(t, a, b)) == True{} : Bool}
      %Equal.sym(Bool, WN(t, a, b), True{}, wk(t, a, a2, b, h, AB.and_true_r(X2, WN(t, a2, b), hw))) :
        {Bool.and(Bool.and(True{}, True{}), _) == True{} : Bool}
      {==}

law pre_get:
  for +xs: List<&2, U32>
  for +s: Nat
  for +x: U32
  for +t: List<&2, U32>
  for +hp: {List.take(&2, U32, List.drop(&2, U32, xs, s), 1n+List.length(&2, U32, t)) == x <> t : List<&2, U32>}
  {List.get(&2, U32, xs, s) == Some{x} : Maybe<&2, U32>}

def pre_get(xs, s, x, t, hp):
  match xs s:
    case Nil{} _:
      Empty.absurd({List.get(&2, U32, Nil{}, s) == Some{x} : Maybe<&2, U32>}, nil_cons(x, t, hp))
    case Con{+y, r} 0n:
      Equal.cong(U32, Maybe<&2, U32>, z => Some{z}, y, x,
        AB.cons_inj_h(U32, y, x, List.take(&2, U32, r, List.length(&2, U32, t)), t, hp))
    case Con{y, r} 1n+p:
      pre_get(r, p, x, t, hp)

law pre_tail:
  for +xs: List<&2, U32>
  for +s: Nat
  for +x: U32
  for +t: List<&2, U32>
  for +hp: {List.take(&2, U32, List.drop(&2, U32, xs, s), 1n+List.length(&2, U32, t)) == x <> t : List<&2, U32>}
  {List.take(&2, U32, List.drop(&2, U32, xs, Nat.add(s, 1n)), List.length(&2, U32, t)) == t : List<&2, U32>}

def pre_tail(xs, s, x, t, hp):
  match xs s:
    case Nil{} _:
      Empty.absurd({List.take(&2, U32, Nil{}, List.length(&2, U32, t)) == t : List<&2, U32>}, nil_cons(x, t, hp))
    case Con{+y, r} 0n:
      %Equal.sym(List<&2, U32>, List.drop(&2, U32, r, 0n), r, X.drop_zero(r)) :
        {List.take(&2, U32, _, List.length(&2, U32, t)) == t : List<&2, U32>}
      AB.cons_inj_t(U32, y, x, List.take(&2, U32, r, List.length(&2, U32, t)), t, hp)
    case Con{y, r} 1n+p:
      pre_tail(r, p, x, t, hp)

# Pushing a byte onto the first piece shifts every end by one.
law ends_push:
  for +x: U32
  for +ps: List<&2, List<&2, U32>>
  for +s: Nat
  for +hnn: {nn(ps) == True{} : Bool}
  {F.ends(F.split.push(x, ps), s) == F.ends(ps, Nat.add(s, 1n)) : List<&2, Nat>}

def ends_push(x, ps, s, hnn):
  match ps:
    case Nil{}:
      Empty.absurd({F.ends(F.split.push(x, Nil{}), s) == F.ends(Nil{}, Nat.add(s, 1n)) : List<&2, Nat>}, AB.false_ne_true(hnn))
    case Con{+p, r}:
      +L = List.length(&2, U32, p)
      %Equal.sym(Nat, Nat.add(Nat.add(s, 1n), L), Nat.add(s, Nat.add(1n, L)), N.add_assoc(s, 1n, L)) :
        {F.ends(F.split.push(x, p <> r), s) == Con{_, F.ends(r, Nat.add(_, 1n))} : List<&2, Nat>}
      {==}

law sa:
  for +s: Nat
  for +l: Nat
  {Nat.sub(Nat.add(Nat.add(s, 1n), l), s) == 1n+l : Nat}

def sa(s, l):
  %Equal.sym(Nat, Nat.add(Nat.add(s, 1n), l), Nat.add(s, Nat.add(1n, l)), N.add_assoc(s, 1n, l)) : {Nat.sub(_, s) == 1n+l : Nat}
  N.sub_add_l(s, 1n+l)

law pb_push:
  for +x: U32
  for +ps: List<&2, List<&2, U32>>
  for +xs: List<&2, U32>
  for +s: Nat
  for +hnn: {nn(ps) == True{} : Bool}
  for +hg: {List.get(&2, U32, xs, s) == Some{x} : Maybe<&2, U32>}
  for +ih: {PN(F.ends(ps, Nat.add(s, 1n)), xs, Nat.add(s, 1n)) == ps : List<&2, List<&2, U32>>}
  {PN(F.ends(F.split.push(x, ps), s), xs, s) == F.split.push(x, ps) : List<&2, List<&2, U32>>}

def pb_push(x, ps, xs, s, hnn, hg, ih):
  match ps:
    case Nil{}:
      Empty.absurd({PN(F.ends(F.split.push(x, Nil{}), s), xs, s) == F.split.push(x, Nil{}) : List<&2, List<&2, U32>>}, AB.false_ne_true(hnn))
    case Con{+p, r}:
      +L = List.length(&2, U32, p)
      +s1 = Nat.add(s, 1n)
      +A2 = Nat.add(s1, L)
      +TL = PN(F.ends(r, Nat.add(A2, 1n)), xs, Nat.add(A2, 1n))
      +hh = AB.cons_inj_h(List<&2, U32>, D.slice(xs, s1, Nat.sub(A2, s1)), p, TL, r, ih)
      +ht = AB.cons_inj_t(List<&2, U32>, D.slice(xs, s1, Nat.sub(A2, s1)), p, TL, r, ih)
      %Equal.sym(List<&2, Nat>, F.ends(F.split.push(x, p <> r), s), F.ends(p <> r, s1), ends_push(x, p <> r, s, {==})) :
        {PN(_, xs, s) == F.split.push(x, p <> r) : List<&2, List<&2, U32>>}
      %Equal.sym(List<&2, List<&2, U32>>, TL, r, ht) : {Con{D.slice(xs, s, Nat.sub(A2, s)), _} == Con{x <> p, r} : List<&2, List<&2, U32>>}
      %Equal.sym(Nat, Nat.sub(A2, s), 1n+L, sa(s, L)) : {Con{D.slice(xs, s, _), r} == Con{x <> p, r} : List<&2, List<&2, U32>>}
      %Equal.sym(List<&2, U32>, D.slice(xs, s, 1n+L), x <> D.slice(xs, s1, L), X.slice_cons(xs, s, L, x, hg)) :
        {Con{_, r} == Con{x <> p, r} : List<&2, List<&2, U32>>}
      +hh2 = AB.subst(Nat, y => {D.slice(xs, s1, y) == p : List<&2, U32>}, Nat.sub(A2, s1), L, N.sub_add_l(s1, L), hh)
      %Equal.sym(List<&2, U32>, D.slice(xs, s1, L), p, hh2) : {Con{x <> _, r} == Con{x <> p, r} : List<&2, List<&2, U32>>}
      {==}

law pbc:
  for +x: U32
  for +t: List<&2, U32>
  for +xs: List<&2, U32>
  for +s: Nat
  for +sep: U32
  for +b: Bool
  for +hb: {U32.is_eq(x, sep) == b : Bool}
  for +hg: {List.get(&2, U32, xs, s) == Some{x} : Maybe<&2, U32>}
  for +ih: {PN(F.ends(F.split(t, sep), Nat.add(s, 1n)), xs, Nat.add(s, 1n)) == F.split(t, sep) : List<&2, List<&2, U32>>}
  {PN(F.ends(F.split(x <> t, sep), s), xs, s) == F.split(x <> t, sep) : List<&2, List<&2, U32>>}

def pbc(x, t, xs, s, sep, b, hb, hg, ih):
  match b:
    case True{}:
      %Equal.sym(Bool, U32.is_eq(x, sep), True{}, hb) :
        {PN(F.ends(F.split.fin(x, F.split(t, sep), _), s), xs, s) == F.split.fin(x, F.split(t, sep), _) : List<&2, List<&2, U32>>}
      %Equal.sym(Nat, Nat.add(s, 0n), s, N.add_zero(s)) :
        {Con{D.slice(xs, s, Nat.sub(_, s)), PN(F.ends(F.split(t, sep), Nat.add(_, 1n)), xs, Nat.add(_, 1n))} == Nil{} <> F.split(t, sep) : List<&2, List<&2, U32>>}
      %Equal.sym(Nat, Nat.sub(s, s), 0n, H.sub_self(s)) :
        {Con{D.slice(xs, s, _), PN(F.ends(F.split(t, sep), Nat.add(s, 1n)), xs, Nat.add(s, 1n))} == Nil{} <> F.split(t, sep) : List<&2, List<&2, U32>>}
      %Equal.sym(List<&2, U32>, D.slice(xs, s, 0n), Nil{}, X.slice_zero(xs, s)) :
        {Con{_, PN(F.ends(F.split(t, sep), Nat.add(s, 1n)), xs, Nat.add(s, 1n))} == Nil{} <> F.split(t, sep) : List<&2, List<&2, U32>>}
      %Equal.sym(List<&2, List<&2, U32>>, PN(F.ends(F.split(t, sep), Nat.add(s, 1n)), xs, Nat.add(s, 1n)), F.split(t, sep), ih) :
        {Con{Nil{}, _} == Nil{} <> F.split(t, sep) : List<&2, List<&2, U32>>}
      {==}
    case False{}:
      %Equal.sym(Bool, U32.is_eq(x, sep), False{}, hb) :
        {PN(F.ends(F.split.fin(x, F.split(t, sep), _), s), xs, s) == F.split.fin(x, F.split(t, sep), _) : List<&2, List<&2, U32>>}
      pb_push(x, F.split(t, sep), xs, s, split_nn(t, sep), hg, ih)

# The ends of split(ys) from s give back its pieces when ys starts xs at s.
law pb:
  for +ys: List<&2, U32>
  for +xs: List<&2, U32>
  for +s: Nat
  for +sep: U32
  for +hp: {List.take(&2, U32, List.drop(&2, U32, xs, s), List.length(&2, U32, ys)) == ys : List<&2, U32>}
  {PN(F.ends(F.split(ys, sep), s), xs, s) == F.split(ys, sep) : List<&2, List<&2, U32>>}

def pb(ys, xs, s, sep, hp):
  match ys:
    case Nil{}:
      %Equal.sym(Nat, Nat.add(s, 0n), s, N.add_zero(s)) : {Con{D.slice(xs, s, Nat.sub(_, s)), Nil{}} == [Nil{}] : List<&2, List<&2, U32>>}
      %Equal.sym(Nat, Nat.sub(s, s), 0n, H.sub_self(s)) : {Con{D.slice(xs, s, _), Nil{}} == [Nil{}] : List<&2, List<&2, U32>>}
      %Equal.sym(List<&2, U32>, D.slice(xs, s, 0n), Nil{}, X.slice_zero(xs, s)) : {Con{_, Nil{}} == [Nil{}] : List<&2, List<&2, U32>>}
      {==}
    case Con{+x, t}:
      pbc(x, t, xs, s, sep, U32.is_eq(x, sep), {==}, pre_get(xs, s, x, t, hp),
        pb(t, xs, Nat.add(s, 1n), sep, pre_tail(xs, s, x, t, hp)))

law wc:
  for +x: U32
  for +t: List<&2, U32>
  for +s: Nat
  for +sep: U32
  for +b: Bool
  for +hb: {U32.is_eq(x, sep) == b : Bool}
  for +ih: {WN(F.ends(F.split(t, sep), Nat.add(s, 1n)), s, Nat.add(s, 1n+List.length(&2, U32, t))) == True{} : Bool}
  {WN(F.ends(F.split(x <> t, sep), s), s, Nat.add(s, List.length(&2, U32, x <> t))) == True{} : Bool}

def wc(x, t, s, sep, b, hb, ih):
  match b:
    case True{}:
      +U = Nat.add(s, 1n+List.length(&2, U32, t))
      %Equal.sym(Bool, U32.is_eq(x, sep), True{}, hb) : {WN(F.ends(F.split.fin(x, F.split(t, sep), _), s), s, U) == True{} : Bool}
      %Equal.sym(Nat, Nat.add(s, 0n), s, N.add_zero(s)) :
        {Bool.and(Bool.and(Nat.is_le(s, _), Nat.is_le(_, U)), WN(F.ends(F.split(t, sep), Nat.add(_, 1n)), s, U)) == True{} : Bool}
      %Equal.sym(Bool, Nat.is_le(s, s), True{}, N.le_refl(s)) :
        {Bool.and(Bool.and(_, Nat.is_le(s, U)), WN(F.ends(F.split(t, sep), Nat.add(s, 1n)), s, U)) == True{} : Bool}
      %Equal.sym(Bool, Nat.is_le(s, U), True{}, N.le_add_r(s, 1n+List.length(&2, U32, t))) :
        {Bool.and(Bool.and(True{}, _), WN(F.ends(F.split(t, sep), Nat.add(s, 1n)), s, U)) == True{} : Bool}
      %Equal.sym(Bool, WN(F.ends(F.split(t, sep), Nat.add(s, 1n)), s, U), True{}, ih) :
        {Bool.and(Bool.and(True{}, True{}), _) == True{} : Bool}
      {==}
    case False{}:
      +U = Nat.add(s, 1n+List.length(&2, U32, t))
      %Equal.sym(Bool, U32.is_eq(x, sep), False{}, hb) : {WN(F.ends(F.split.fin(x, F.split(t, sep), _), s), s, U) == True{} : Bool}
      %Equal.sym(List<&2, Nat>, F.ends(F.split.push(x, F.split(t, sep)), s), F.ends(F.split(t, sep), Nat.add(s, 1n)),
        ends_push(x, F.split(t, sep), s, split_nn(t, sep))) :
        {WN(_, s, U) == True{} : Bool}
      ih

# The ends of split(ys) from s lie in s .. s + length(ys).
law wl:
  for +ys: List<&2, U32>
  for +s: Nat
  for +sep: U32
  {WN(F.ends(F.split(ys, sep), s), s, Nat.add(s, List.length(&2, U32, ys))) == True{} : Bool}

def wl(ys, s, sep):
  match ys:
    case Nil{}:
      %Equal.sym(Nat, Nat.add(s, 0n), s, N.add_zero(s)) : {Bool.and(Bool.and(Nat.is_le(s, _), Nat.is_le(_, _)), True{}) == True{} : Bool}
      %Equal.sym(Bool, Nat.is_le(s, s), True{}, N.le_refl(s)) : {Bool.and(Bool.and(_, _), True{}) == True{} : Bool}
      {==}
    case Con{+x, t}:
      +L = List.length(&2, U32, t)
      +s1 = Nat.add(s, 1n)
      +ih = wl(t, s1, sep)
      wc(x, t, s, sep, U32.is_eq(x, sep), {==},
        wk(F.ends(F.split(t, sep), s1), s, s1, Nat.add(s, 1n+L), N.le_add_r(s, 1n),
          AB.subst(Nat, y => {WN(F.ends(F.split(t, sep), s1), s1, y) == True{} : Bool}, Nat.add(s1, L), Nat.add(s, Nat.add(1n, L)),
            N.add_assoc(s, 1n, L), ih)))

# The loop as a Data function
# ===========================

def FV(+len: U32, +t: P.Tree<U32>, +s: U32, +to: U32, +sep: U32) -> U32:
  Pair.snd(D.Bytes, U32, B.find(C.BT(len, t), s, to, sep))

def NX(want: Bool, +len: U32, +t: P.Tree<U32>, +s: U32, +to: U32, +sep: U32) -> U32:
  match want:
    case True{}:
      FV(len, t, s, to, sep)
    case False{}:
      to

def CG(+n: Nat, more: Bool, +e: U32, +len: U32, +t: P.Tree<U32>, +to: U32, +sep: U32) -> List<&2, U32>:
  match n more:
    case 0n _:
      Nil{}
    case 1n+m False{}:
      Nil{}
    case 1n+m True{}:
      +go = U32.is_lt(e, to)
      Con{e, CG(m, go, NX(go && Bool.not(Nat.is_eq(m, 0n)), len, t, (e + 1 : U32), to, sep), len, t, to, sep)}

law nx_eq:
  for +want: Bool
  for +len: U32
  for +t: P.Tree<U32>
  for +s: U32
  for +to: U32
  for +sep: U32
  {K.cut.next(want, C.BT(len, t), s, to, sep) == (C.BT(len, t), NX(want, len, t, s, to, sep)) : D.Bytes & U32}

def nx_eq(want, len, t, s, to, sep):
  match want:
    case True{}:
      FI.find_pair_t(len, t, s, to, sep)
    case False{}:
      {==}

law cg_eq:
  for +n: Nat
  for +more: Bool
  for +e: U32
  for +len: U32
  for +t: P.Tree<U32>
  for +to: U32
  for +sep: U32
  {K.cut.go(n, more, (C.BT(len, t), e), to, sep) == (C.BT(len, t), CG(n, more, e, len, t, to, sep)) : D.Bytes & List<&2, U32>}

def cg_eq(n, more, e, len, t, to, sep):
  match n more:
    case 0n _:
      {==}
    case 1n+m False{}:
      {==}
    case 1n+m True{}:
      +go = U32.is_lt(e, to)
      +W = go && Bool.not(Nat.is_eq(m, 0n))
      +e1 = (e + 1 : U32)
      +nx = NX(W, len, t, e1, to, sep)
      %Equal.sym(D.Bytes & U32, K.cut.next(W, C.BT(len, t), e1, to, sep), (C.BT(len, t), nx), nx_eq(W, len, t, e1, to, sep)) :
        {K.cut.cons(e, K.cut.go(m, go, _, to, sep)) == (C.BT(len, t), CG(1n+m, True{}, e, len, t, to, sep)) : D.Bytes & List<&2, U32>}
      %Equal.sym(D.Bytes & List<&2, U32>, K.cut.go(m, go, (C.BT(len, t), nx), to, sep), (C.BT(len, t), CG(m, go, nx, len, t, to, sep)),
        cg_eq(m, go, nx, len, t, to, sep)) :
        {K.cut.cons(e, _) == (C.BT(len, t), CG(1n+m, True{}, e, len, t, to, sep)) : D.Bytes & List<&2, U32>}
      {==}

law cut_eq:
  for +len: U32
  for +t: P.Tree<U32>
  for +from: U32
  for +to: U32
  for +sep: U32
  for +n: Nat
  {K.cut(C.BT(len, t), from, to, sep, n) == (C.BT(len, t), CG(n, True{}, NX(Bool.not(Nat.is_eq(n, 0n)), len, t, from, to, sep), len, t, to, sep)) : D.Bytes & List<&2, U32>}

def cut_eq(len, t, from, to, sep, n):
  +W0 = Bool.not(Nat.is_eq(n, 0n))
  %Equal.sym(D.Bytes & U32, K.cut.next(W0, C.BT(len, t), from, to, sep), (C.BT(len, t), NX(W0, len, t, from, to, sep)), nx_eq(W0, len, t, from, to, sep)) :
    {K.cut.go(n, True{}, _, to, sep) == (C.BT(len, t), CG(n, True{}, NX(W0, len, t, from, to, sep), len, t, to, sep)) : D.Bytes & List<&2, U32>}
  cg_eq(n, True{}, NX(W0, len, t, from, to, sep), len, t, to, sep)

law cut_pair_t:
  for +len: U32
  for +t: P.Tree<U32>
  for +from: U32
  for +to: U32
  for +sep: U32
  for +n: Nat
  {K.cut(C.BT(len, t), from, to, sep, n) == (C.BT(len, t), Pair.snd(D.Bytes, List<&2, U32>, K.cut(C.BT(len, t), from, to, sep, n))) : D.Bytes & List<&2, U32>}

def cut_pair_t(len, t, from, to, sep, n):
  %Equal.sym(D.Bytes & List<&2, U32>, K.cut(C.BT(len, t), from, to, sep, n),
    (C.BT(len, t), CG(n, True{}, NX(Bool.not(Nat.is_eq(n, 0n)), len, t, from, to, sep), len, t, to, sep)), cut_eq(len, t, from, to, sep, n)) :
    {_ == (C.BT(len, t), Pair.snd(D.Bytes, List<&2, U32>, _)) : D.Bytes & List<&2, U32>}
  {==}

# The loop invariant
# ==================

# The slice from s to T has T - s bytes.
law ylen:
  for +len: U32
  for +t: P.Tree<U32>
  for +d: Nat
  for +s: Nat
  for +tt: Nat
  for +h: {D.ok(C.BT(len, t), d) == True{} : Bool}
  for +hT: {Nat.is_le(tt, U32.to_nat(len)) == True{} : Bool}
  {List.length(&2, U32, D.slice(D.view(C.BT(len, t)), s, Nat.sub(tt, s))) == Nat.sub(tt, s) : Nat}

def ylen(len, t, d, s, tt, h, hT):
  +xs = D.view(C.BT(len, t))
  +e1 = Equal.trans(Nat, List.length(&2, U32, List.drop(&2, U32, xs, s)), Nat.sub(List.length(&2, U32, xs), s), Nat.sub(U32.to_nat(len), s),
    H.drop_length(xs, s),
    Equal.cong(Nat, Nat, y => Nat.sub(y, s), List.length(&2, U32, xs), U32.to_nat(len), O.view_size_t(len, t, d, h)))
  S.take_length(List.drop(&2, U32, xs, s), Nat.sub(tt, s),
    AB.subst(Nat, y => {Nat.is_le(Nat.sub(tt, s), y) == True{} : Bool}, Nat.sub(U32.to_nat(len), s), List.length(&2, U32, List.drop(&2, U32, xs, s)),
      Equal.sym(Nat, List.length(&2, U32, List.drop(&2, U32, xs, s)), Nat.sub(U32.to_nat(len), s), e1),
      sub_mono(tt, U32.to_nat(len), s, hT)))

# After the last piece (the end reached to): one more end, at to.
law cgf:
  for +s: Nat
  for +e: U32
  for +len: U32
  for +t: P.Tree<U32>
  for +d: Nat
  for +to: U32
  for +sep: U32
  for +h: {D.ok(C.BT(len, t), d) == True{} : Bool}
  for +hT: {Nat.is_le(U32.to_nat(to), U32.to_nat(len)) == True{} : Bool}
  for +he: {U32.to_nat(e) == D.first(D.view(C.BT(len, t)), s, U32.to_nat(to), sep) : Nat}
  for +hg: {U32.is_lt(e, to) == False{} : Bool}
  for +kk: Nat
  {Con{U32.to_nat(e), Nil{}} == List.take(&2, Nat, F.ends(F.split(D.slice(D.view(C.BT(len, t)), s, Nat.sub(U32.to_nat(to), s)), sep), s), 1n+kk) : List<&2, Nat>}

def cgf(s, e, len, t, d, to, sep, h, hT, he, hg, kk):
  +xs = D.view(C.BT(len, t))
  +TT = U32.to_nat(to)
  +ys = D.slice(xs, s, Nat.sub(TT, s))
  +r = D.run_len(ys, sep)
  +hyl = ylen(len, t, d, s, TT, h, hT)
  +hn = Equal.trans(Bool, Nat.is_lt(U32.to_nat(e), TT), U32.is_lt(e, to), False{}, Equal.sym(Bool, U32.is_lt(e, to), Nat.is_lt(U32.to_nat(e), TT), U.is_lt_to_nat(e, to)), hg)
  +hle = AB.subst(Nat, y => {Nat.is_le(TT, y) == True{} : Bool}, U32.to_nat(e), Nat.add(s, r), he, N.not_lt_le(U32.to_nat(e), TT, hn))
  +h1 = AB.subst(Nat, y => {Nat.is_le(y, r) == True{} : Bool}, Nat.sub(TT, s), List.length(&2, U32, ys), Equal.sym(Nat, List.length(&2, U32, ys), Nat.sub(TT, s), hyl),
    sub_le_of(TT, s, r, hle))
  +h2 = AB.subst(Nat, y => {Nat.is_le(r, y) == True{} : Bool}, Nat.sub(TT, s), List.length(&2, U32, ys), Equal.sym(Nat, List.length(&2, U32, ys), Nat.sub(TT, s), hyl),
    Q.pl_r_le(List.drop(&2, U32, xs, s), Nat.sub(TT, s), sep))
  %Equal.sym(List<&2, List<&2, U32>>, F.split(ys, sep), [ys], sp2(ys, sep, h1)) :
    {Con{U32.to_nat(e), Nil{}} == List.take(&2, Nat, F.ends(_, s), 1n+kk) : List<&2, Nat>}
  %Equal.sym(Nat, U32.to_nat(e), D.first(D.view(C.BT(len, t)), s, U32.to_nat(to), sep), he) :
    {Con{_, Nil{}} == Con{Nat.add(s, List.length(&2, U32, ys)), Nil{}} : List<&2, Nat>}
  %le_antisym(r, List.length(&2, U32, ys), h2, h1) : {Con{Nat.add(s, r), Nil{}} == Con{Nat.add(s, _), Nil{}} : List<&2, Nat>}
  {==}

law cgv:
  for +k: Nat
  for +g: Bool
  for +s: Nat
  for +e: U32
  for +len: U32
  for +t: P.Tree<U32>
  for +d: Nat
  for +to: U32
  for +sep: U32
  for +h: {D.ok(C.BT(len, t), d) == True{} : Bool}
  for +hT: {Nat.is_le(U32.to_nat(to), U32.to_nat(len)) == True{} : Bool}
  for +hs: {Nat.is_le(s, U32.to_nat(to)) == True{} : Bool}
  for +hsep: {U32.is_lt(sep, 256) == True{} : Bool}
  for +he: {U32.to_nat(e) == D.first(D.view(C.BT(len, t)), s, U32.to_nat(to), sep) : Nat}
  for +hg: {U32.is_lt(e, to) == g : Bool}
  {F.nats(CG(1n+k, True{}, e, len, t, to, sep)) == List.take(&2, Nat, F.ends(F.split(D.slice(D.view(C.BT(len, t)), s, Nat.sub(U32.to_nat(to), s)), sep), s), 1n+k) : List<&2, Nat>}

def cgv(k, g, s, e, len, t, d, to, sep, h, hT, hs, hsep, he, hg):
  match k g:
    case 0n False{}:
      +RHS = List.take(&2, Nat, F.ends(F.split(D.slice(D.view(C.BT(len, t)), s, Nat.sub(U32.to_nat(to), s)), sep), s), 1n)
      %Equal.sym(Bool, U32.is_lt(e, to), False{}, hg) :
        {Con{U32.to_nat(e), F.nats(CG(0n, _, NX(Bool.and(_, Bool.not(Nat.is_eq(0n, 0n))), len, t, (e + 1 : U32), to, sep), len, t, to, sep))} == RHS : List<&2, Nat>}
      cgf(s, e, len, t, d, to, sep, h, hT, he, hg, 0n)
    case 1n+k2 False{}:
      +RHS = List.take(&2, Nat, F.ends(F.split(D.slice(D.view(C.BT(len, t)), s, Nat.sub(U32.to_nat(to), s)), sep), s), 1n+1n+k2)
      %Equal.sym(Bool, U32.is_lt(e, to), False{}, hg) :
        {Con{U32.to_nat(e), F.nats(CG(1n+k2, _, NX(Bool.and(_, Bool.not(Nat.is_eq(1n+k2, 0n))), len, t, (e + 1 : U32), to, sep), len, t, to, sep))} == RHS : List<&2, Nat>}
      cgf(s, e, len, t, d, to, sep, h, hT, he, hg, 1n+k2)
    case 0n True{}:
      +xs = D.view(C.BT(len, t))
      +TT = U32.to_nat(to)
      +ys = D.slice(xs, s, Nat.sub(TT, s))
      +r = D.run_len(ys, sep)
      +hyl = ylen(len, t, d, s, TT, h, hT)
      +hlt = AB.subst(Nat, y => {Nat.is_lt(y, TT) == True{} : Bool}, U32.to_nat(e), Nat.add(s, r), he,
        Equal.trans(Bool, Nat.is_lt(U32.to_nat(e), TT), U32.is_lt(e, to), True{}, Equal.sym(Bool, U32.is_lt(e, to), Nat.is_lt(U32.to_nat(e), TT), U.is_lt_to_nat(e, to)), hg))
      +hr = AB.subst(Nat, y => {Nat.is_lt(r, y) == True{} : Bool}, Nat.sub(TT, s), List.length(&2, U32, ys), Equal.sym(Nat, List.length(&2, U32, ys), Nat.sub(TT, s), hyl),
        lt_sub_of(s, r, TT, hlt))
      +REST = F.split(List.drop(&2, U32, ys, Nat.add(r, 1n)), sep)
      +RHS = List.take(&2, Nat, F.ends(F.split(ys, sep), s), 1n)
      %Equal.sym(Bool, U32.is_lt(e, to), True{}, hg) :
        {Con{U32.to_nat(e), F.nats(CG(0n, _, NX(Bool.and(_, Bool.not(Nat.is_eq(0n, 0n))), len, t, (e + 1 : U32), to, sep), len, t, to, sep))} == RHS : List<&2, Nat>}
      %Equal.sym(List<&2, List<&2, U32>>, F.split(ys, sep), List.take(&2, U32, ys, r) <> REST, sp1(ys, sep, hr)) :
        {Con{U32.to_nat(e), Nil{}} == List.take(&2, Nat, F.ends(_, s), 1n) : List<&2, Nat>}
      +L1 = List.length(&2, U32, List.take(&2, U32, ys, r))
      %Equal.sym(List<&2, Nat>, List.take(&2, Nat, F.ends(REST, Nat.add(Nat.add(s, L1), 1n)), 0n), Nil{}, tz(Nat, F.ends(REST, Nat.add(Nat.add(s, L1), 1n)))) :
        {Con{U32.to_nat(e), Nil{}} == Con{Nat.add(s, L1), _} : List<&2, Nat>}
      %Equal.sym(Nat, List.length(&2, U32, List.take(&2, U32, ys, r)), r, S.take_length(ys, r, N.lt_to_le(r, List.length(&2, U32, ys), hr))) : {Con{U32.to_nat(e), Nil{}} == Con{Nat.add(s, _), Nil{}} : List<&2, Nat>}
      %Equal.sym(Nat, U32.to_nat(e), D.first(D.view(C.BT(len, t)), s, U32.to_nat(to), sep), he) :
        {Con{_, Nil{}} == Con{Nat.add(s, r), Nil{}} : List<&2, Nat>}
      {==}
    case 1n+k2 True{}:
      +xs = D.view(C.BT(len, t))
      +TT = U32.to_nat(to)
      +ys = D.slice(xs, s, Nat.sub(TT, s))
      +r = D.run_len(ys, sep)
      +e1 = (e + 1 : U32)
      +e2 = FV(len, t, e1, to, sep)
      +s2 = U32.to_nat(e1)
      +hyl = ylen(len, t, d, s, TT, h, hT)
      +htl = Equal.trans(Bool, Nat.is_lt(U32.to_nat(e), TT), U32.is_lt(e, to), True{}, Equal.sym(Bool, U32.is_lt(e, to), Nat.is_lt(U32.to_nat(e), TT), U.is_lt_to_nat(e, to)), hg)
      +hlt = AB.subst(Nat, y => {Nat.is_lt(y, TT) == True{} : Bool}, U32.to_nat(e), Nat.add(s, r), he, htl)
      +hr = AB.subst(Nat, y => {Nat.is_lt(r, y) == True{} : Bool}, Nat.sub(TT, s), List.length(&2, U32, ys), Equal.sym(Nat, List.length(&2, U32, ys), Nat.sub(TT, s), hyl),
        lt_sub_of(s, r, TT, hlt))
      +M = Nat.mul(4n, Nat.pow(2n, d))
      +ei = C.inc_fits(e, d, C.ok_d(len, t, d, h),
        N.lt_le_trans(U32.to_nat(e), U32.to_nat(len), M, N.lt_le_trans(U32.to_nat(e), TT, U32.to_nat(len), htl, hT), C.ok_len(len, t, d, h)))
      +es2 = Equal.trans(Nat, s2, Nat.add(U32.to_nat(e), 1n), Nat.add(Nat.add(s, r), 1n), ei,
        Equal.cong(Nat, Nat, y => Nat.add(y, 1n), U32.to_nat(e), Nat.add(s, r), he))
      +hs2 = AB.subst(Nat, y => {Nat.is_le(y, TT) == True{} : Bool}, Nat.add(Nat.add(s, r), 1n), s2, Equal.sym(Nat, s2, Nat.add(Nat.add(s, r), 1n), es2),
        C.succ_le(Nat.add(s, r), TT, hlt))
      +hft2 = Equal.trans(Bool, U32.is_le(e1, to), Nat.is_le(s2, TT), True{}, U.is_le_to_nat(e1, to), hs2)
      +he2 = FI.find_view_t(len, t, d, e1, to, sep, h, hft2, hT, hsep)
      +ih = cgv(k2, U32.is_lt(e2, to), s2, e2, len, t, d, to, sep, h, hT, hs2, hsep, he2, {==})
      +RHS = List.take(&2, Nat, F.ends(F.split(ys, sep), s), 1n+1n+k2)
      +REST = F.split(List.drop(&2, U32, ys, Nat.add(r, 1n)), sep)
      +L1 = List.length(&2, U32, List.take(&2, U32, ys, r))
      %Equal.sym(Bool, U32.is_lt(e, to), True{}, hg) :
        {Con{U32.to_nat(e), F.nats(CG(1n+k2, _, NX(Bool.and(_, Bool.not(Nat.is_eq(1n+k2, 0n))), len, t, e1, to, sep), len, t, to, sep))} == RHS : List<&2, Nat>}
      %Equal.sym(List<&2, List<&2, U32>>, F.split(ys, sep), List.take(&2, U32, ys, r) <> REST, sp1(ys, sep, hr)) :
        {Con{U32.to_nat(e), F.nats(CG(1n+k2, True{}, e2, len, t, to, sep))} == List.take(&2, Nat, F.ends(_, s), 1n+1n+k2) : List<&2, Nat>}
      %Equal.sym(Nat, List.length(&2, U32, List.take(&2, U32, ys, r)), r, S.take_length(ys, r, N.lt_to_le(r, List.length(&2, U32, ys), hr))) :
        {Con{U32.to_nat(e), F.nats(CG(1n+k2, True{}, e2, len, t, to, sep))} == Con{Nat.add(s, _), List.take(&2, Nat, F.ends(REST, Nat.add(Nat.add(s, _), 1n)), 1n+k2)} : List<&2, Nat>}
      %Equal.sym(Nat, U32.to_nat(e), D.first(D.view(C.BT(len, t)), s, U32.to_nat(to), sep), he) :
        {Con{_, F.nats(CG(1n+k2, True{}, e2, len, t, to, sep))} == Con{Nat.add(s, r), List.take(&2, Nat, F.ends(REST, Nat.add(Nat.add(s, r), 1n)), 1n+k2)} : List<&2, Nat>}
      %Equal.sym(List<&2, U32>, List.drop(&2, U32, ys, Nat.add(r, 1n)), D.slice(xs, Nat.add(s, Nat.add(r, 1n)), Nat.sub(TT, Nat.add(s, Nat.add(r, 1n)))),
        slice_drop(xs, s, TT, Nat.add(r, 1n))) :
        {Con{Nat.add(s, r), F.nats(CG(1n+k2, True{}, e2, len, t, to, sep))} == Con{Nat.add(s, r), List.take(&2, Nat, F.ends(F.split(_, sep), Nat.add(Nat.add(s, r), 1n)), 1n+k2)} : List<&2, Nat>}
      %N.add_assoc(s, r, 1n) :
        {Con{Nat.add(s, r), F.nats(CG(1n+k2, True{}, e2, len, t, to, sep))} == Con{Nat.add(s, r), List.take(&2, Nat, F.ends(F.split(D.slice(xs, _, Nat.sub(TT, _)), sep), Nat.add(Nat.add(s, r), 1n)), 1n+k2)} : List<&2, Nat>}
      %es2 :
        {Con{Nat.add(s, r), F.nats(CG(1n+k2, True{}, e2, len, t, to, sep))} == Con{Nat.add(s, r), List.take(&2, Nat, F.ends(F.split(D.slice(xs, _, Nat.sub(TT, _)), sep), _), 1n+k2)} : List<&2, Nat>}
      %Equal.sym(List<&2, Nat>, F.nats(CG(1n+k2, True{}, e2, len, t, to, sep)), List.take(&2, Nat, F.ends(F.split(D.slice(xs, s2, Nat.sub(TT, s2)), sep), s2), 1n+k2), ih) :
        {Con{Nat.add(s, r), _} == Con{Nat.add(s, r), List.take(&2, Nat, F.ends(F.split(D.slice(xs, s2, Nat.sub(TT, s2)), sep), s2), 1n+k2)} : List<&2, Nat>}
      {==}

# The laws
# ========

law ce:
  for +n: Nat
  for +len: U32
  for +t: P.Tree<U32>
  for +d: Nat
  for +from: U32
  for +to: U32
  for +sep: U32
  for +h: {D.ok(C.BT(len, t), d) == True{} : Bool}
  for +hft: {U32.is_le(from, to) == True{} : Bool}
  for +ht: {Nat.is_le(U32.to_nat(to), D.size(C.BT(len, t))) == True{} : Bool}
  for +hs: {U32.is_lt(sep, 256) == True{} : Bool}
  {F.nats(Pair.snd(D.Bytes, List<&2, U32>, K.cut(C.BT(len, t), from, to, sep, n))) == List.take(&2, Nat, F.ends(F.split(D.slice(D.view(C.BT(len, t)), U32.to_nat(from), Nat.sub(U32.to_nat(to), U32.to_nat(from))), sep), U32.to_nat(from)), n) : List<&2, Nat>}

def ce(n, len, t, d, from, to, sep, h, hft, ht, hs):
  match n:
    case 0n:
      +E0 = F.ends(F.split(D.slice(D.view(C.BT(len, t)), U32.to_nat(from), Nat.sub(U32.to_nat(to), U32.to_nat(from))), sep), U32.to_nat(from))
      %Equal.sym(D.Bytes & List<&2, U32>, K.cut(C.BT(len, t), from, to, sep, 0n),
        (C.BT(len, t), CG(0n, True{}, NX(Bool.not(Nat.is_eq(0n, 0n)), len, t, from, to, sep), len, t, to, sep)), cut_eq(len, t, from, to, sep, 0n)) :
        {F.nats(Pair.snd(D.Bytes, List<&2, U32>, _)) == List.take(&2, Nat, E0, 0n) : List<&2, Nat>}
      Equal.sym(List<&2, Nat>, List.take(&2, Nat, E0, 0n), Nil{}, tz(Nat, E0))
    case 1n+k:
      +E0 = F.ends(F.split(D.slice(D.view(C.BT(len, t)), U32.to_nat(from), Nat.sub(U32.to_nat(to), U32.to_nat(from))), sep), U32.to_nat(from))
      +e0 = FV(len, t, from, to, sep)
      %Equal.sym(D.Bytes & List<&2, U32>, K.cut(C.BT(len, t), from, to, sep, 1n+k),
        (C.BT(len, t), CG(1n+k, True{}, NX(Bool.not(Nat.is_eq(1n+k, 0n)), len, t, from, to, sep), len, t, to, sep)), cut_eq(len, t, from, to, sep, 1n+k)) :
        {F.nats(Pair.snd(D.Bytes, List<&2, U32>, _)) == List.take(&2, Nat, E0, 1n+k) : List<&2, Nat>}
      cgv(k, U32.is_lt(e0, to), U32.to_nat(from), e0, len, t, d, to, sep, h, ht,
        Equal.trans(Bool, Nat.is_le(U32.to_nat(from), U32.to_nat(to)), U32.is_le(from, to), True{},
          Equal.sym(Bool, U32.is_le(from, to), Nat.is_le(U32.to_nat(from), U32.to_nat(to)), U.is_le_to_nat(from, to)), hft),
        hs, FI.find_view_t(len, t, d, from, to, sep, h, hft, ht, hs), {==})

law cut_ends_t:
  for +len: U32
  for +t: P.Tree<U32>
  for +d: Nat
  for +from: U32
  for +to: U32
  for +sep: U32
  for +n: Nat
  for +h: {D.ok(C.BT(len, t), d) == True{} : Bool}
  for +hft: {U32.is_le(from, to) == True{} : Bool}
  for +ht: {Nat.is_le(U32.to_nat(to), D.size(C.BT(len, t))) == True{} : Bool}
  for +hs: {U32.is_lt(sep, 256) == True{} : Bool}
  {F.nats(Pair.snd(D.Bytes, List<&2, U32>, K.cut(C.BT(len, t), from, to, sep, n))) == List.take(&2, Nat, F.ends(F.split(D.slice(D.view(C.BT(len, t)), U32.to_nat(from), Nat.sub(U32.to_nat(to), U32.to_nat(from))), sep), U32.to_nat(from)), n) : List<&2, Nat>}

def cut_ends_t(len, t, d, from, to, sep, n, h, hft, ht, hs):
  ce(n, len, t, d, from, to, sep, h, hft, ht, hs)

law cut_view_t:
  for +len: U32
  for +t: P.Tree<U32>
  for +d: Nat
  for +from: U32
  for +to: U32
  for +sep: U32
  for +n: Nat
  for +h: {D.ok(C.BT(len, t), d) == True{} : Bool}
  for +hft: {U32.is_le(from, to) == True{} : Bool}
  for +ht: {Nat.is_le(U32.to_nat(to), D.size(C.BT(len, t))) == True{} : Bool}
  for +hs: {U32.is_lt(sep, 256) == True{} : Bool}
  {F.pieces(Pair.snd(D.Bytes, List<&2, U32>, K.cut(C.BT(len, t), from, to, sep, n)), D.view(C.BT(len, t)), U32.to_nat(from)) == List.take(&2, List<&2, U32>, F.split(D.slice(D.view(C.BT(len, t)), U32.to_nat(from), Nat.sub(U32.to_nat(to), U32.to_nat(from))), sep), n) : List<&2, List<&2, U32>>}

def cut_view_t(len, t, d, from, to, sep, n, h, hft, ht, hs):
  +xs = D.view(C.BT(len, t))
  +F0 = U32.to_nat(from)
  +TT = U32.to_nat(to)
  +ys = D.slice(xs, F0, Nat.sub(TT, F0))
  +ES = Pair.snd(D.Bytes, List<&2, U32>, K.cut(C.BT(len, t), from, to, sep, n))
  +E0 = F.ends(F.split(ys, sep), F0)
  +RHS = List.take(&2, List<&2, U32>, F.split(ys, sep), n)
  +hyl = ylen(len, t, d, F0, TT, h, ht)
  +hp = AB.subst(Nat, y => {List.take(&2, U32, List.drop(&2, U32, xs, F0), y) == ys : List<&2, U32>}, Nat.sub(TT, F0), List.length(&2, U32, ys),
    Equal.sym(Nat, List.length(&2, U32, ys), Nat.sub(TT, F0), hyl), {==})
  %Equal.sym(List<&2, List<&2, U32>>, F.pieces(ES, xs, F0), PN(F.nats(ES), xs, F0), pn(ES, xs, F0)) : {_ == RHS : List<&2, List<&2, U32>>}
  %Equal.sym(List<&2, Nat>, F.nats(ES), List.take(&2, Nat, E0, n), cut_ends_t(len, t, d, from, to, sep, n, h, hft, ht, hs)) :
    {PN(_, xs, F0) == RHS : List<&2, List<&2, U32>>}
  %Equal.sym(List<&2, List<&2, U32>>, PN(List.take(&2, Nat, E0, n), xs, F0), List.take(&2, List<&2, U32>, PN(E0, xs, F0), n), pntake(E0, n, xs, F0)) :
    {_ == RHS : List<&2, List<&2, U32>>}
  %Equal.sym(List<&2, List<&2, U32>>, PN(E0, xs, F0), F.split(ys, sep), pb(ys, xs, F0, sep, hp)) :
    {List.take(&2, List<&2, U32>, _, n) == RHS : List<&2, List<&2, U32>>}
  {==}

law cut_bounds_t:
  for +len: U32
  for +t: P.Tree<U32>
  for +d: Nat
  for +from: U32
  for +to: U32
  for +sep: U32
  for +n: Nat
  for +h: {D.ok(C.BT(len, t), d) == True{} : Bool}
  for +hft: {U32.is_le(from, to) == True{} : Bool}
  for +ht: {Nat.is_le(U32.to_nat(to), D.size(C.BT(len, t))) == True{} : Bool}
  for +hs: {U32.is_lt(sep, 256) == True{} : Bool}
  {F.within(Pair.snd(D.Bytes, List<&2, U32>, K.cut(C.BT(len, t), from, to, sep, n)), U32.to_nat(from), U32.to_nat(to)) == True{} : Bool}

def cut_bounds_t(len, t, d, from, to, sep, n, h, hft, ht, hs):
  +xs = D.view(C.BT(len, t))
  +F0 = U32.to_nat(from)
  +TT = U32.to_nat(to)
  +ys = D.slice(xs, F0, Nat.sub(TT, F0))
  +ES = Pair.snd(D.Bytes, List<&2, U32>, K.cut(C.BT(len, t), from, to, sep, n))
  +E0 = F.ends(F.split(ys, sep), F0)
  +hft2 = Equal.trans(Bool, Nat.is_le(F0, TT), U32.is_le(from, to), True{}, Equal.sym(Bool, U32.is_le(from, to), Nat.is_le(F0, TT), U.is_le_to_nat(from, to)), hft)
  +eT = Equal.trans(Nat, Nat.add(F0, List.length(&2, U32, ys)), Nat.add(F0, Nat.sub(TT, F0)), TT,
    Equal.cong(Nat, Nat, y => Nat.add(F0, y), List.length(&2, U32, ys), Nat.sub(TT, F0), ylen(len, t, d, F0, TT, h, ht)),
    N.le_sub_add(F0, TT, hft2))
  +hw = AB.subst(Nat, y => {WN(E0, F0, y) == True{} : Bool}, Nat.add(F0, List.length(&2, U32, ys)), TT, eT, wl(ys, F0, sep))
  %Equal.sym(Bool, F.within(ES, F0, TT), WN(F.nats(ES), F0, TT), wn(ES, F0, TT)) : {_ == True{} : Bool}
  %Equal.sym(List<&2, Nat>, F.nats(ES), List.take(&2, Nat, E0, n), cut_ends_t(len, t, d, from, to, sep, n, h, hft, ht, hs)) :
    {WN(_, F0, TT) == True{} : Bool}
  wtake(E0, n, F0, TT, hw)

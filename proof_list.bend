import Base
import lawful-bytes@0.1.0.0/defs.bend as D
import ./defs.bend as F
import lawful-words@0.1.0.0/proof_nat.bend as N
import lawful-words@0.1.0.0/proof_u32.bend as U
import lawful-arrays@0.1.0.0/proof_base.bend as AB

# The laws about lists, text and decb, restated with every variable reusable
# (same names and statements as in LAWS.bend).

# Lists
# =====

law append_nil:
  for +xs: List<&2, U32>
  {List.append(&2, U32, xs, Nil{}) == xs : List<&2, U32>}

def append_nil(xs):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, t}:
      %append_nil(t) : {x <> List.append(&2, U32, t, Nil{}) == x <> _ : List<&2, U32>}
      {==}

law append_assoc:
  for +xs: List<&2, U32>
  for +ys: List<&2, U32>
  for +zs: List<&2, U32>
  {List.append(&2, U32, List.append(&2, U32, xs, ys), zs) == List.append(&2, U32, xs, List.append(&2, U32, ys, zs)) : List<&2, U32>}

def append_assoc(xs, ys, zs):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, t}:
      %append_assoc(t, ys, zs) :
        {x <> List.append(&2, U32, List.append(&2, U32, t, ys), zs) == x <> _ : List<&2, U32>}
      {==}

law take_zero2:
  for +ps: List<&2, List<&2, U32>>
  {List.take(&2, List<&2, U32>, ps, 0n) == Nil{} : List<&2, List<&2, U32>>}

def take_zero2(ps):
  match ps:
    case Nil{}:
      {==}
    case Con{p, t}:
      {==}

# split
# =====

law sl_fin:
  for +x: U32
  for +r: List<&2, List<&2, U32>>
  for +b: Bool
  for +c: Nat
  for +hr: {List.length(&2, List<&2, U32>, r) == Nat.add(c, 1n) : Nat}
  {List.length(&2, List<&2, U32>, F.split.fin(x, r, b)) == Nat.add(F.count.if(b, c), 1n) : Nat}

def sl_fin(x, r, b, c, hr):
  match r b:
    case Nil{} True{}:
      %hr : {1n+0n == 1n+_ : Nat}
      {==}
    case Nil{} False{}:
      Empty.absurd({1n == Nat.add(c, 1n) : Nat},
        AB.succ_ne_zero(c, Equal.sym(Nat, 0n, 1n+c, Equal.trans(Nat, 0n, Nat.add(c, 1n), 1n+c, hr, N.add_one(c)))))
    case Con{h, t} True{}:
      %hr : {1n+List.length(&2, List<&2, U32>, h <> t) == 1n+_ : Nat}
      {==}
    case Con{h, t} False{}:
      hr

law split_length:
  for +xs: List<&2, U32>
  for +sep: U32
  {List.length(&2, List<&2, U32>, F.split(xs, sep)) == Nat.add(F.count(xs, sep), 1n) : Nat}

def split_length(xs, sep):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, t}:
      sl_fin(x, F.split(t, sep), U32.is_eq(x, sep), F.count(t, sep), split_length(t, sep))

# join.go of the pieces of split is the separator, then their join.
law jg_fin:
  for +y: U32
  for +r: List<&2, List<&2, U32>>
  for +b: Bool
  for +sep: U32
  {F.join.go(F.split.fin(y, r, b), sep) == sep <> F.join(F.split.fin(y, r, b), sep) : List<&2, U32>}

def jg_fin(y, r, b, sep):
  match r b:
    case Nil{} True{}:
      {==}
    case Nil{} False{}:
      {==}
    case Con{h, t} True{}:
      {==}
    case Con{h, t} False{}:
      {==}

law jg:
  for +t: List<&2, U32>
  for +sep: U32
  {F.join.go(F.split(t, sep), sep) == sep <> F.join(F.split(t, sep), sep) : List<&2, U32>}

def jg(t, sep):
  match t:
    case Nil{}:
      {==}
    case Con{+y, t2}:
      jg_fin(y, F.split(t2, sep), U32.is_eq(y, sep), sep)

law join_push:
  for +x: U32
  for +r: List<&2, List<&2, U32>>
  for +sep: U32
  {F.join(F.split.push(x, r), sep) == x <> F.join(r, sep) : List<&2, U32>}

def join_push(x, r, sep):
  match r:
    case Nil{}:
      {==}
    case Con{h, t}:
      {==}

law sj_fin:
  for +x: U32
  for +t: List<&2, U32>
  for +sep: U32
  for +b: Bool
  for +hb: {U32.is_eq(x, sep) == b : Bool}
  for +ih: {F.join(F.split(t, sep), sep) == t : List<&2, U32>}
  for +hg: {F.join.go(F.split(t, sep), sep) == sep <> F.join(F.split(t, sep), sep) : List<&2, U32>}
  {F.join(F.split.fin(x, F.split(t, sep), b), sep) == x <> t : List<&2, U32>}

def sj_fin(x, t, sep, b, hb, ih, hg):
  match b:
    case True{}:
      %Equal.sym(List<&2, U32>, F.join.go(F.split(t, sep), sep), sep <> F.join(F.split(t, sep), sep), hg) :
        {_ == x <> t : List<&2, U32>}
      %Equal.sym(List<&2, U32>, F.join(F.split(t, sep), sep), t, ih) : {sep <> _ == x <> t : List<&2, U32>}
      %Equal.sym(U32, x, sep, U.is_eq_true(x, sep, hb)) : {sep <> t == _ <> t : List<&2, U32>}
      {==}
    case False{}:
      %Equal.sym(List<&2, U32>, F.join(F.split.push(x, F.split(t, sep)), sep), x <> F.join(F.split(t, sep), sep),
        join_push(x, F.split(t, sep), sep)) :
        {_ == x <> t : List<&2, U32>}
      %Equal.sym(List<&2, U32>, F.join(F.split(t, sep), sep), t, ih) : {x <> _ == x <> t : List<&2, U32>}
      {==}

law split_join:
  for +xs: List<&2, U32>
  for +sep: U32
  {F.join(F.split(xs, sep), sep) == xs : List<&2, U32>}

def split_join(xs, sep):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, t}:
      sj_fin(x, t, sep, U32.is_eq(x, sep), {==}, split_join(t, sep), jg(t, sep))

# Text
# ====

law text_codes:
  for +s: String
  {F.text(F.codes(s)) == s : String}

def text_codes(s):
  match s:
    case SNil{}:
      {==}
    case SCon{Chr{x}, t}:
      %text_codes(t) : {SCon{Chr{x}, F.text(F.codes(t))} == SCon{Chr{x}, _} : String}
      {==}

law st_fin:
  for +x: U32
  for +r: List<&2, List<&2, U32>>
  for +b: Bool
  {String.split.fin(Chr{x}, F.texts(r), b) == F.texts(F.split.fin(x, r, b)) : List<&2, String>}

def st_fin(x, r, b):
  match r b:
    case Nil{} True{}:
      {==}
    case Nil{} False{}:
      {==}
    case Con{h, t} True{}:
      {==}
    case Con{h, t} False{}:
      {==}

law split_text:
  for +xs: List<&2, U32>
  for +sep: U32
  {String.split(F.text(xs), Chr{sep}) == F.texts(F.split(xs, sep)) : List<&2, String>}

def split_text(xs, sep):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, t}:
      %Equal.sym(List<&2, String>, String.split(F.text(t), Chr{sep}), F.texts(F.split(t, sep)), split_text(t, sep)) :
        {String.split.fin(Chr{x}, _, U32.is_eq(x, sep)) == F.texts(F.split.fin(x, F.split(t, sep), U32.is_eq(x, sep))) : List<&2, String>}
      st_fin(x, F.split(t, sep), U32.is_eq(x, sep))

law text_app:
  for +a: List<&2, U32>
  for +b: List<&2, U32>
  {F.text(List.append(&2, U32, a, b)) == String.append(F.text(a), F.text(b)) : String}

def text_app(a, b):
  match a:
    case Nil{}:
      {==}
    case Con{+x, t}:
      %text_app(t, b) : {SCon{Chr{x}, F.text(List.append(&2, U32, t, b))} == SCon{Chr{x}, _} : String}
      {==}

law jt:
  for +t: List<&2, List<&2, U32>>
  for +p: List<&2, U32>
  for +sep: U32
  {F.text(List.append(&2, U32, p, F.join.go(t, sep))) == String.join.go(F.texts(t), F.text(p), F.text([sep])) : String}

def jt(t, p, sep):
  match t:
    case Nil{}:
      %Equal.sym(List<&2, U32>, List.append(&2, U32, p, Nil{}), p, append_nil(p)) : {F.text(_) == F.text(p) : String}
      {==}
    case Con{+h2, t2}:
      +X = {sep <> List.append(&2, U32, h2, F.join.go(t2, sep)) : List<&2, U32>}
      %Equal.sym(String, F.text(List.append(&2, U32, p, X)), String.append(F.text(p), F.text(X)), text_app(p, X)) :
        {_ == String.join.go(F.texts(h2 <> t2), F.text(p), F.text([sep])) : String}
      %jt(t2, h2, sep) :
        {String.append(F.text(p), SCon{Chr{sep}, F.text(List.append(&2, U32, h2, F.join.go(t2, sep)))}) == String.append(F.text(p), SCon{Chr{sep}, _}) : String}
      {==}

law join_text:
  for +ps: List<&2, List<&2, U32>>
  for +sep: U32
  {F.text(F.join(ps, sep)) == String.join(F.texts(ps), F.text([sep])) : String}

def join_text(ps, sep):
  match ps:
    case Nil{}:
      {==}
    case Con{p, t}:
      jt(t, p, sep)

# Joining at piece k
# ==================

law ja0:
  for +q: List<&2, U32>
  for +t2: List<&2, List<&2, U32>>
  for +sep: U32
  for +h: {Nat.is_lt(1n, List.length(&2, List<&2, U32>, q <> t2)) == True{} : Bool}
  {F.join.go(q <> t2, sep) == List.append(&2, U32, F.join.go(List.take(&2, List<&2, U32>, q <> t2, 1n), sep), sep <> F.join(List.drop(&2, List<&2, U32>, q <> t2, 1n), sep)) : List<&2, U32>}

def ja0(q, t2, sep, h):
  match t2:
    case Nil{}:
      Empty.absurd({F.join.go([q], sep) == List.append(&2, U32, F.join.go([q], sep), [sep]) : List<&2, U32>}, AB.false_ne_true(h))
    case Con{+r, t3}:
      +Z = {sep <> List.append(&2, U32, r, F.join.go(t3, sep)) : List<&2, U32>}
      %Equal.sym(List<&2, U32>, List.append(&2, U32, q, Nil{}), q, append_nil(q)) :
        {sep <> List.append(&2, U32, q, Z) == sep <> List.append(&2, U32, _, Z) : List<&2, U32>}
      {==}

law ja_go:
  for +t: List<&2, List<&2, U32>>
  for +sep: U32
  for +k: Nat
  for +h: {Nat.is_lt(Nat.add(k, 1n), List.length(&2, List<&2, U32>, t)) == True{} : Bool}
  {F.join.go(t, sep) == List.append(&2, U32, F.join.go(List.take(&2, List<&2, U32>, t, Nat.add(k, 1n)), sep), sep <> F.join(List.drop(&2, List<&2, U32>, t, Nat.add(k, 1n)), sep)) : List<&2, U32>}

def ja_go(t, sep, k, h):
  match t k:
    case Nil{} _:
      Empty.absurd({F.join.go(Nil{}, sep) == List.append(&2, U32, F.join.go(List.take(&2, List<&2, U32>, Nil{}, Nat.add(k, 1n)), sep), sep <> F.join(List.drop(&2, List<&2, U32>, Nil{}, Nat.add(k, 1n)), sep)) : List<&2, U32>},
        AB.lt_zero_absurd(Nat.add(k, 1n), h))
    case Con{+q, t2} 0n:
      ja0(q, t2, sep, h)
    case Con{+q, t2} 1n+k2:
      +JT = F.join.go(List.take(&2, List<&2, U32>, t2, Nat.add(k2, 1n)), sep)
      +Z = {sep <> F.join(List.drop(&2, List<&2, U32>, t2, Nat.add(k2, 1n)), sep) : List<&2, U32>}
      %Equal.sym(List<&2, U32>, F.join.go(t2, sep), List.append(&2, U32, JT, Z), ja_go(t2, sep, k2, h)) :
        {sep <> List.append(&2, U32, q, _) == sep <> List.append(&2, U32, List.append(&2, U32, q, JT), Z) : List<&2, U32>}
      %Equal.sym(List<&2, U32>, List.append(&2, U32, List.append(&2, U32, q, JT), Z), List.append(&2, U32, q, List.append(&2, U32, JT, Z)), append_assoc(q, JT, Z)) :
        {sep <> List.append(&2, U32, q, List.append(&2, U32, JT, Z)) == sep <> _ : List<&2, U32>}
      {==}

law jat0:
  for +p: List<&2, U32>
  for +t: List<&2, List<&2, U32>>
  for +sep: U32
  for +h: {Nat.is_lt(1n, List.length(&2, List<&2, U32>, p <> t)) == True{} : Bool}
  {F.join(p <> t, sep) == List.append(&2, U32, F.join(List.take(&2, List<&2, U32>, p <> t, 1n), sep), sep <> F.join(List.drop(&2, List<&2, U32>, p <> t, 1n), sep)) : List<&2, U32>}

def jat0(p, t, sep, h):
  match t:
    case Nil{}:
      Empty.absurd({F.join([p], sep) == List.append(&2, U32, F.join([p], sep), [sep]) : List<&2, U32>}, AB.false_ne_true(h))
    case Con{+r, t3}:
      +Z = {sep <> List.append(&2, U32, r, F.join.go(t3, sep)) : List<&2, U32>}
      %Equal.sym(List<&2, U32>, List.append(&2, U32, p, Nil{}), p, append_nil(p)) :
        {List.append(&2, U32, p, Z) == List.append(&2, U32, _, Z) : List<&2, U32>}
      {==}

law join_at:
  for +ps: List<&2, List<&2, U32>>
  for +sep: U32
  for +k: Nat
  for +h: {Nat.is_lt(Nat.add(k, 1n), List.length(&2, List<&2, U32>, ps)) == True{} : Bool}
  {F.join(ps, sep) == List.append(&2, U32, F.join(List.take(&2, List<&2, U32>, ps, Nat.add(k, 1n)), sep), Con{sep, F.join(List.drop(&2, List<&2, U32>, ps, Nat.add(k, 1n)), sep)}) : List<&2, U32>}

def join_at(ps, sep, k, h):
  match ps k:
    case Nil{} _:
      Empty.absurd({F.join(Nil{}, sep) == List.append(&2, U32, F.join(List.take(&2, List<&2, U32>, Nil{}, Nat.add(k, 1n)), sep), sep <> F.join(List.drop(&2, List<&2, U32>, Nil{}, Nat.add(k, 1n)), sep)) : List<&2, U32>},
        AB.lt_zero_absurd(Nat.add(k, 1n), h))
    case Con{+p, t} 0n:
      jat0(p, t, sep, h)
    case Con{+p, t} 1n+k2:
      +JT = F.join.go(List.take(&2, List<&2, U32>, t, Nat.add(k2, 1n)), sep)
      +Z = {sep <> F.join(List.drop(&2, List<&2, U32>, t, Nat.add(k2, 1n)), sep) : List<&2, U32>}
      %Equal.sym(List<&2, U32>, F.join.go(t, sep), List.append(&2, U32, JT, Z), ja_go(t, sep, k2, h)) :
        {List.append(&2, U32, p, _) == List.append(&2, U32, List.append(&2, U32, p, JT), Z) : List<&2, U32>}
      %Equal.sym(List<&2, U32>, List.append(&2, U32, List.append(&2, U32, p, JT), Z), List.append(&2, U32, p, List.append(&2, U32, JT, Z)), append_assoc(p, JT, Z)) :
        {List.append(&2, U32, p, List.append(&2, U32, JT, Z)) == _ : List<&2, U32>}
      {==}

# Ends
# ====

law ends_arith:
  for +from: Nat
  for +lp: Nat
  for +lj: Nat
  {Nat.add(Nat.add(Nat.add(from, lp), 1n), lj) == Nat.add(from, Nat.add(lp, 1n+lj)) : Nat}

def ends_arith(from, lp, lj):
  %Equal.sym(Nat, Nat.add(Nat.add(from, lp), 1n), 1n+Nat.add(from, lp), N.add_one(Nat.add(from, lp))) :
    {Nat.add(_, lj) == Nat.add(from, Nat.add(lp, 1n+lj)) : Nat}
  %Equal.sym(Nat, Nat.add(lp, 1n+lj), 1n+Nat.add(lp, lj), N.add_succ(lp, lj)) :
    {Nat.add(1n+Nat.add(from, lp), lj) == Nat.add(from, _) : Nat}
  %Equal.sym(Nat, Nat.add(from, 1n+Nat.add(lp, lj)), 1n+Nat.add(from, Nat.add(lp, lj)), N.add_succ(from, Nat.add(lp, lj))) :
    {Nat.add(1n+Nat.add(from, lp), lj) == _ : Nat}
  %N.add_assoc(from, lp, lj) : {1n+Nat.add(Nat.add(from, lp), lj) == 1n+_ : Nat}
  {==}

# One step of ej, with the induction hypothesis for the rest (t is not empty).
law ej_step:
  for +p: List<&2, U32>
  for +t: List<&2, List<&2, U32>>
  for +sep: U32
  for +from: Nat
  for +k2: Nat
  for +h: {Nat.is_lt(1n+k2, List.length(&2, List<&2, U32>, p <> t)) == True{} : Bool}
  for +ih: {List.get(&2, Nat, F.ends(t, Nat.add(Nat.add(from, List.length(&2, U32, p)), 1n)), k2) == Some{Nat.add(Nat.add(Nat.add(from, List.length(&2, U32, p)), 1n), List.length(&2, U32, F.join(List.take(&2, List<&2, U32>, t, 1n+k2), sep)))} : Maybe<&2, Nat>}
  {List.get(&2, Nat, F.ends(p <> t, from), 1n+k2) == Some{Nat.add(from, List.length(&2, U32, F.join(List.take(&2, List<&2, U32>, p <> t, 1n+1n+k2), sep)))} : Maybe<&2, Nat>}

def ej_step(p, t, sep, from, k2, h, ih):
  match t:
    case Nil{}:
      Empty.absurd({List.get(&2, Nat, F.ends([p], from), 1n+k2) == Some{Nat.add(from, List.length(&2, U32, F.join(List.take(&2, List<&2, U32>, [p], 1n+1n+k2), sep)))} : Maybe<&2, Nat>}, AB.lt_zero_absurd(k2, h))
    case Con{+q, t2}:
      +lp = List.length(&2, U32, p)
      +f1 = Nat.add(Nat.add(from, lp), 1n)
      +J = F.join(List.take(&2, List<&2, U32>, q <> t2, 1n+k2), sep)
      +RHS = {Some{Nat.add(from, List.length(&2, U32, F.join(List.take(&2, List<&2, U32>, p <> q <> t2, 1n+1n+k2), sep)))} : Maybe<&2, Nat>}
      %Equal.sym(Maybe<&2, Nat>, List.get(&2, Nat, F.ends(q <> t2, f1), k2), Some{Nat.add(f1, List.length(&2, U32, J))}, ih) :
        {_ == RHS : Maybe<&2, Nat>}
      %Equal.sym(Nat, List.length(&2, U32, List.append(&2, U32, p, sep <> J)), Nat.add(lp, List.length(&2, U32, sep <> J)),
        AB.length_append(U32, p, sep <> J)) :
        {Some{Nat.add(f1, List.length(&2, U32, J))} == Some{Nat.add(from, _)} : Maybe<&2, Nat>}
      %ends_arith(from, lp, List.length(&2, U32, J)) :
        {Some{Nat.add(f1, List.length(&2, U32, J))} == Some{_} : Maybe<&2, Nat>}
      {==}

law ej:
  for +ps: List<&2, List<&2, U32>>
  for +sep: U32
  for +from: Nat
  for +k: Nat
  for +h: {Nat.is_lt(k, List.length(&2, List<&2, U32>, ps)) == True{} : Bool}
  {List.get(&2, Nat, F.ends(ps, from), k) == Some{Nat.add(from, List.length(&2, U32, F.join(List.take(&2, List<&2, U32>, ps, 1n+k), sep)))} : Maybe<&2, Nat>}

def ej(ps, sep, from, k, h):
  match ps k:
    case Nil{} _:
      Empty.absurd({List.get(&2, Nat, F.ends(Nil{}, from), k) == Some{Nat.add(from, 0n)} : Maybe<&2, Nat>}, AB.lt_zero_absurd(k, h))
    case Con{+p, t} 0n:
      %Equal.sym(List<&2, List<&2, U32>>, List.take(&2, List<&2, U32>, t, 0n), Nil{}, take_zero2(t)) :
        {Some{Nat.add(from, List.length(&2, U32, p))} == Some{Nat.add(from, List.length(&2, U32, F.join(p <> _, sep)))} : Maybe<&2, Nat>}
      %Equal.sym(List<&2, U32>, List.append(&2, U32, p, Nil{}), p, append_nil(p)) :
        {Some{Nat.add(from, List.length(&2, U32, p))} == Some{Nat.add(from, List.length(&2, U32, _))} : Maybe<&2, Nat>}
      {==}
    case Con{+p, t} 1n+k2:
      ej_step(p, t, sep, from, k2, h, ej(t, sep, Nat.add(Nat.add(from, List.length(&2, U32, p)), 1n), k2, h))

law ends_join:
  for +ps: List<&2, List<&2, U32>>
  for +sep: U32
  for +from: Nat
  for +k: Nat
  for +h: {Nat.is_lt(k, List.length(&2, List<&2, U32>, ps)) == True{} : Bool}
  {List.get(&2, Nat, F.ends(ps, from), k) == Some{Nat.add(from, List.length(&2, U32, F.join(List.take(&2, List<&2, U32>, ps, Nat.add(k, 1n)), sep)))} : Maybe<&2, Nat>}

def ends_join(ps, sep, from, k, h):
  %Equal.sym(Nat, Nat.add(k, 1n), 1n+k, N.add_one(k)) :
    {List.get(&2, Nat, F.ends(ps, from), k) == Some{Nat.add(from, List.length(&2, U32, F.join(List.take(&2, List<&2, U32>, ps, _), sep)))} : Maybe<&2, Nat>}
  ej(ps, sep, from, k, h)

law pieces_length:
  for +es: List<&2, U32>
  for +xs: List<&2, U32>
  for +from: Nat
  {List.length(&2, List<&2, U32>, F.pieces(es, xs, from)) == List.length(&2, U32, es) : Nat}

def pieces_length(es, xs, from):
  match es:
    case Nil{}:
      {==}
    case Con{+e, t}:
      %pieces_length(t, xs, Nat.add(U32.to_nat(e), 1n)) :
        {1n+List.length(&2, List<&2, U32>, F.pieces(t, xs, Nat.add(U32.to_nat(e), 1n))) == 1n+_ : Nat}
      {==}

# decb
# ====

# 2^32 must never take part in a conversion (the checker would expand it), so
# the bound stays a variable M and the law instantiates it.
def decb_if(+n: Nat, b: Bool, hb: {b == True{} : Bool}) -> {F.decb.if(n, b) == Some{n} : Maybe<&2, Nat>}:
  match b:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({F.decb.if(n, False{}) == Some{n} : Maybe<&2, Nat>}, AB.false_ne_true(hb))

law decb_fits_m:
  for +xs: List<&2, U32>
  for +n: Nat
  for +m: Nat
  for +h: {F.dec(xs) == Some{n} : Maybe<&2, Nat>}
  for +hn: {Nat.is_lt(n, m) == True{} : Bool}
  {F.decb(xs, m) == Some{n} : Maybe<&2, Nat>}

def decb_fits_m(xs, n, m, h, hn):
  %Equal.sym(Maybe<&2, Nat>, F.dec(xs), Some{n}, h) : {F.decb.of(_, m) == Some{n} : Maybe<&2, Nat>}
  decb_if(n, Nat.is_lt(n, m), hn)

law decb_fits:
  for +xs: List<&2, U32>
  for +n: Nat
  for +h: {F.dec(xs) == Some{n} : Maybe<&2, Nat>}
  for +hn: {Nat.is_lt(n, Nat.pow(2n, 32n)) == True{} : Bool}
  {F.decb(xs, Nat.pow(2n, 32n)) == Some{n} : Maybe<&2, Nat>}

def decb_fits(xs, n, h, hn):
  decb_fits_m(xs, n, Nat.pow(2n, 32n), h, hn)

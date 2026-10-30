import Base
import lawful-bytes@0.1.0.0/defs.bend as D
import lawful-bytes@0.1.0.0/bytes.bend as B
import ./defs.bend as F
import ./fields.bend as C
import lawful-bytes@0.1.0.0/proof_seq.bend as Q
import lawful-bytes@0.1.0.0/proof_core.bend as K
import lawful-bytes@0.1.0.0/proof_append.bend as X
import lawful-words@0.1.0.0/proof_nat.bend as N
import lawful-words@0.1.0.0/proof_u32.bend as U
import lawful-arrays@0.1.0.0/proof_base.bend as AB
import lawful-arrays@0.1.0.0/proof_tree.bend as P

# num on the mirror K.BT(len, t). The checker normalizes both sides of any
# conversion that is not a syntactic identity, and normalizing 2^32, or
# U32.to_nat of a large word such as 429496729, overflows. So the lemmas take
# the bound M (with hm : 2^32 == M) and q = to_nat(429496729) as variables,
# and only num_view_t instantiates them, in a type that matches syntactically.

# 2^32 and the overflow constant, kept abstract
# =============================================

# A bound below M gives the bound below 2^32 that lawful-words' lemmas want.
law lift:
  for +x: Nat
  for +M: Nat
  for +hm: {Nat.pow(2n, 32n) == M : Nat}
  for +h: {Nat.is_lt(x, M) == True{} : Bool}
  {Nat.is_lt(x, Nat.pow(2n, 32n)) == True{} : Bool}

def lift(x, M, hm, h):
  %Equal.sym(Nat, Nat.pow(2n, 32n), M, hm) : {Nat.is_lt(x, _) == True{} : Bool}
  h

law posM:
  for +M: Nat
  for +hm: {Nat.pow(2n, 32n) == M : Nat}
  {Nat.is_lt(0n, M) == True{} : Bool}

def posM(M, hm):
  %hm : {Nat.is_lt(0n, _) == True{} : Bool}
  AB.pow_pos(32n)

law notM:
  for +M: Nat
  for +hm: {Nat.pow(2n, 32n) == M : Nat}
  {U32.to_nat(U32.not(0)) == Nat.sub(Nat.sub(M, 1n), U32.to_nat(0)) : Nat}

def notM(M, hm):
  %hm : {U32.to_nat(U32.not(0)) == Nat.sub(Nat.sub(_, 1n), U32.to_nat(0)) : Nat}
  U.to_nat_not_p(0)

law ED:
  {U32.div(U32.not(0), 10) == 429496729 : U32}

def ED():
  {==}

law EM:
  {U32.mod(U32.not(0), 10) == 5 : U32}

def EM():
  {==}

law QD:
  {Nat.div(U32.to_nat(U32.not(0)), U32.to_nat(10)) == U32.to_nat(429496729) : Nat}

def QD():
  %ED() : {Nat.div(U32.to_nat(U32.not(0)), U32.to_nat(10)) == U32.to_nat(_) : Nat}
  Equal.sym(Nat, U32.to_nat(U32.div(U32.not(0), 10)), Nat.div(U32.to_nat(U32.not(0)), U32.to_nat(10)), U.to_nat_div(U32.not(0), 10))

law QR:
  {Nat.mod(U32.to_nat(U32.not(0)), U32.to_nat(10)) == U32.to_nat(5) : Nat}

def QR():
  %EM() : {Nat.mod(U32.to_nat(U32.not(0)), U32.to_nat(10)) == U32.to_nat(_) : Nat}
  Equal.sym(Nat, U32.to_nat(U32.mod(U32.not(0), 10)), Nat.mod(U32.to_nat(U32.not(0)), U32.to_nat(10)), U.to_nat_mod(U32.not(0), 10))

law succ_pred:
  for +M: Nat
  for +h: {Nat.is_lt(0n, M) == True{} : Bool}
  {1n+Nat.sub(M, 1n) == M : Nat}

def succ_pred(M, h):
  match M:
    case 0n:
      Empty.absurd({1n+Nat.sub(0n, 1n) == 0n : Nat}, AB.false_ne_true(h))
    case 1n+p:
      %Equal.sym(Nat, Nat.sub(p, 0n), p, N.sub_zero(p)) : {1n+_ == 1n+p : Nat}
      {==}

law qg1:
  for +N1: Nat
  for +Qn: Nat
  for +R: Nat
  for +T: Nat
  for +M: Nat
  for +hdm: {Nat.add(Nat.mul(Nat.div(N1, T), T), Nat.mod(N1, T)) == N1 : Nat}
  for +hd: {Nat.div(N1, T) == Qn : Nat}
  for +hr: {Nat.mod(N1, T) == R : Nat}
  for +hT: {T == 10n : Nat}
  for +hR: {R == 5n : Nat}
  for +eN: {N1 == Nat.sub(M, 1n) : Nat}
  {Nat.add(Nat.mul(Qn, 10n), 5n) == Nat.sub(M, 1n) : Nat}

def qg1(N1, Qn, R, T, M, hdm, hd, hr, hT, hR, eN):
  %hd : {Nat.add(Nat.mul(_, 10n), 5n) == Nat.sub(M, 1n) : Nat}
  %hT : {Nat.add(Nat.mul(Nat.div(N1, T), _), 5n) == Nat.sub(M, 1n) : Nat}
  %Equal.trans(Nat, Nat.mod(N1, T), R, 5n, hr, hR) : {Nat.add(Nat.mul(Nat.div(N1, T), T), _) == Nat.sub(M, 1n) : Nat}
  %eN : {Nat.add(Nat.mul(Nat.div(N1, T), T), Nat.mod(N1, T)) == _ : Nat}
  hdm

# M = 10 q + 6, from 2^32 - 1 = 10 q + 5 with every number abstract.
law QG:
  for +N1: Nat
  for +Qn: Nat
  for +R: Nat
  for +T: Nat
  for +Z: Nat
  for +M: Nat
  for +hdm: {Nat.add(Nat.mul(Nat.div(N1, T), T), Nat.mod(N1, T)) == N1 : Nat}
  for +hd: {Nat.div(N1, T) == Qn : Nat}
  for +hr: {Nat.mod(N1, T) == R : Nat}
  for +hT: {T == 10n : Nat}
  for +hR: {R == 5n : Nat}
  for +hZ: {Z == 0n : Nat}
  for +hN: {N1 == Nat.sub(Nat.sub(M, 1n), Z) : Nat}
  for +hM: {Nat.is_lt(0n, M) == True{} : Bool}
  {Nat.add(Nat.mul(Qn, 10n), 6n) == M : Nat}

def QG(N1, Qn, R, T, Z, M, hdm, hd, hr, hT, hR, hZ, hN, hM):
  +eN = Equal.trans(Nat, N1, Nat.sub(Nat.sub(M, 1n), 0n), Nat.sub(M, 1n),
    Equal.trans(Nat, N1, Nat.sub(Nat.sub(M, 1n), Z), Nat.sub(Nat.sub(M, 1n), 0n), hN,
      Equal.cong(Nat, Nat, z => Nat.sub(Nat.sub(M, 1n), z), Z, 0n, hZ)),
    N.sub_zero(Nat.sub(M, 1n)))
  +e1 = qg1(N1, Qn, R, T, M, hdm, hd, hr, hT, hR, eN)
  %Equal.sym(Nat, Nat.add(Nat.mul(Qn, 10n), 1n+5n), 1n+Nat.add(Nat.mul(Qn, 10n), 5n), N.add_succ(Nat.mul(Qn, 10n), 5n)) :
    {_ == M : Nat}
  %Equal.sym(Nat, Nat.add(Nat.mul(Qn, 10n), 5n), Nat.sub(M, 1n), e1) : {1n+_ == M : Nat}
  succ_pred(M, hM)

law QM:
  for +M: Nat
  for +hm: {Nat.pow(2n, 32n) == M : Nat}
  {Nat.add(Nat.mul(U32.to_nat(429496729), 10n), 6n) == M : Nat}

def QM(M, hm):
  QG(U32.to_nat(U32.not(0)), U32.to_nat(429496729), U32.to_nat(5), U32.to_nat(10), U32.to_nat(0), M,
    N.div_mod(U32.to_nat(U32.not(0)), U32.to_nat(10)), QD(), QR(), {==}, {==}, {==}, notM(M, hm), posM(M, hm))

# The overflow test, as numbers
# =============================

# a < q, or a = q and k <= 5, exactly when 10a + k < 10q + 6 (k a digit).
law FITS0:
  for +a: Nat
  for +q: Nat
  for +k: Nat
  for +hk: {Nat.is_le(k, 9n) == True{} : Bool}
  {Bool.or(Nat.is_lt(a, q), Bool.and(Nat.is_eq(a, q), Nat.is_le(k, 5n))) == Nat.is_lt(Nat.add(Nat.mul(a, 10n), k), Nat.add(Nat.mul(q, 10n), 6n)) : Bool}

def FITS0(a, q, k, hk):
  match a q:
    case 0n 0n:
      Equal.sym(Bool, Nat.is_lt(k, 1n+5n), Nat.is_le(k, 5n), N.lt_succ_iff(k, 5n))
    case 0n 1n+p:
      +B = Nat.add(Nat.mul(1n+p, 10n), 6n)
      Equal.sym(Bool, Nat.is_lt(k, B), True{},
        N.lt_le_trans(k, 10n, B, Equal.trans(Bool, Nat.is_lt(k, 1n+9n), Nat.is_le(k, 9n), True{}, N.lt_succ_iff(k, 9n), hk),
          N.le_add_r(10n, Nat.add(Nat.mul(p, 10n), 6n))))
    case 1n+b 0n:
      {==}
    case 1n+b 1n+p:
      FITS0(b, p, k, hk)

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
      Empty.absurd({Nat.is_le(Nat.sub(1n+p, c), Nat.sub(0n, c)) == True{} : Bool}, AB.false_ne_true(h))
    case 1n+p 1n+r 0n:
      h
    case 1n+p 1n+r 1n+s:
      sub_mono(p, r, s, h)

# A digit byte: x - 48 does not wrap, and its value is at most 9.
law le48:
  for +x: U32
  for +hge: {U32.is_ge(x, 48) == True{} : Bool}
  {U32.is_le(48, x) == True{} : Bool}

def le48(x, hge):
  %Equal.sym(Bool, U32.is_le(48, x), Nat.is_le(U32.to_nat(48), U32.to_nat(x)), U.is_le_to_nat(48, x)) : {_ == True{} : Bool}
  %U.ge_le(U32.to_nat(x), U32.to_nat(48)) : {_ == True{} : Bool}
  Equal.trans(Bool, Nat.is_ge(U32.to_nat(x), U32.to_nat(48)), U32.is_ge(x, 48), True{},
    Equal.sym(Bool, U32.is_ge(x, 48), Nat.is_ge(U32.to_nat(x), U32.to_nat(48)), U.is_ge_to_nat(x, 48)), hge)

law ed48:
  for +x: U32
  for +hge: {U32.is_ge(x, 48) == True{} : Bool}
  {U32.to_nat(U32.sub(x, 48)) == Nat.sub(U32.to_nat(x), 48n) : Nat}

def ed48(x, hge):
  U.to_nat_sub_le(x, 48, le48(x, hge))

law k9:
  for +x: U32
  for +hle: {U32.is_le(x, 57) == True{} : Bool}
  {Nat.is_le(Nat.sub(U32.to_nat(x), 48n), 9n) == True{} : Bool}

def k9(x, hle):
  sub_mono(U32.to_nat(x), 57n, 48n,
    Equal.trans(Bool, Nat.is_le(U32.to_nat(x), U32.to_nat(57)), U32.is_le(x, 57), True{},
      Equal.sym(Bool, U32.is_le(x, 57), Nat.is_le(U32.to_nat(x), U32.to_nat(57)), U.is_le_to_nat(x, 57)), hle))

# num's test on words is the test on numbers (c the constant, q its value).
law FITSU:
  for +acc: U32
  for +x: U32
  for +c: U32
  for +q: Nat
  for +M: Nat
  for +hcq: {U32.to_nat(c) == q : Nat}
  for +hq: {Nat.add(Nat.mul(q, 10n), 6n) == M : Nat}
  for +hge: {U32.is_ge(x, 48) == True{} : Bool}
  for +hle: {U32.is_le(x, 57) == True{} : Bool}
  {Bool.or(U32.is_lt(acc, c), Bool.and(U32.is_eq(acc, c), U32.is_le(U32.sub(x, 48), 5))) == Nat.is_lt(Nat.add(Nat.mul(U32.to_nat(acc), 10n), Nat.sub(U32.to_nat(x), 48n)), M) : Bool}

def FITSU(acc, x, c, q, M, hcq, hq, hge, hle):
  +A = U32.to_nat(acc)
  +KK = Nat.sub(U32.to_nat(x), 48n)
  +RHS = Nat.is_lt(Nat.add(Nat.mul(A, 10n), KK), M)
  %Equal.sym(Bool, U32.is_lt(acc, c), Nat.is_lt(A, U32.to_nat(c)), U.is_lt_to_nat(acc, c)) :
    {Bool.or(_, Bool.and(U32.is_eq(acc, c), U32.is_le(U32.sub(x, 48), 5))) == RHS : Bool}
  %Equal.sym(Bool, U32.is_eq(acc, c), Nat.is_eq(A, U32.to_nat(c)), U.is_eq_to_nat(acc, c)) :
    {Bool.or(Nat.is_lt(A, U32.to_nat(c)), Bool.and(_, U32.is_le(U32.sub(x, 48), 5))) == RHS : Bool}
  %Equal.sym(Bool, U32.is_le(U32.sub(x, 48), 5), Nat.is_le(U32.to_nat(U32.sub(x, 48)), U32.to_nat(5)), U.is_le_to_nat(U32.sub(x, 48), 5)) :
    {Bool.or(Nat.is_lt(A, U32.to_nat(c)), Bool.and(Nat.is_eq(A, U32.to_nat(c)), _)) == RHS : Bool}
  %Equal.sym(Nat, U32.to_nat(U32.sub(x, 48)), KK, ed48(x, hge)) :
    {Bool.or(Nat.is_lt(A, U32.to_nat(c)), Bool.and(Nat.is_eq(A, U32.to_nat(c)), Nat.is_le(_, U32.to_nat(5)))) == RHS : Bool}
  %Equal.sym(Nat, U32.to_nat(c), q, hcq) :
    {Bool.or(Nat.is_lt(A, _), Bool.and(Nat.is_eq(A, _), Nat.is_le(KK, U32.to_nat(5)))) == RHS : Bool}
  %hq : {Bool.or(Nat.is_lt(A, q), Bool.and(Nat.is_eq(A, q), Nat.is_le(KK, U32.to_nat(5)))) == Nat.is_lt(Nat.add(Nat.mul(A, 10n), KK), _) : Bool}
  FITS0(A, q, KK, k9(x, hle))

# The loop state
# ==============

# One step of num.go on byte x: the digit test, the overflow test, the new value.
def DG(+x: U32) -> Bool:
  U32.is_ge(x, 48) && U32.is_le(x, 57)

def FT(+acc: U32, +x: U32) -> Bool:
  U32.is_lt(acc, 429496729) || (U32.is_eq(acc, 429496729) && U32.is_le((x - 48 : U32), 5))

def NA(+acc: U32, +x: U32) -> U32:
  ((acc * 10 : U32) + (x - 48 : U32) : U32)

# The value dec has so far can no longer give a number below M.
def Bad(m: Maybe<&2, Nat>, +M: Nat) -> Data:
  match m:
    case None{}:
      Unit
    case Some{v}:
      {Nat.is_lt(v, M) == False{} : Bool}

# How num.go's (ok, acc) stands for dec.go's value m.
def Inv(ok: Bool, +acc: U32, +m: Maybe<&2, Nat>, +M: Nat) -> Data:
  match ok:
    case True{}:
      Sigma<&2, &2, {m == Some{U32.to_nat(acc)} : Maybe<&2, Nat>}, e => {Nat.is_lt(U32.to_nat(acc), M) == True{} : Bool}>
    case False{}:
      Bad(m, M)

law le_mul10:
  for +v: Nat
  {Nat.is_le(v, Nat.mul(v, 10n)) == True{} : Bool}

def le_mul10(v):
  match v:
    case 0n:
      {==}
    case 1n+p:
      N.le_trans(p, Nat.mul(p, 10n), Nat.add(9n, Nat.mul(p, 10n)), le_mul10(p), N.le_add_l(Nat.mul(p, 10n), 9n))

law bad_step:
  for +m: Maybe<&2, Nat>
  for +dx: Maybe<&2, Nat>
  for +M: Nat
  for +hb: Bad(m, M)
  Bad(F.dec.push(m, dx), M)

def bad_step(m, dx, M, hb):
  match m dx:
    case None{} None{}:
      Unit{}
    case None{} Some{k}:
      Unit{}
    case Some{v} None{}:
      Unit{}
    case Some{+v} Some{+k}:
      +S = Nat.add(Nat.mul(v, 10n), k)
      N.le_not_lt(M, S,
        N.le_trans(M, v, S, N.not_lt_le(v, M, hb),
          N.le_trans(v, Nat.mul(v, 10n), S, le_mul10(v), N.le_add_r(Nat.mul(v, 10n), k))))

law bad_none:
  for +m: Maybe<&2, Nat>
  for +M: Nat
  for +hb: Bad(m, M)
  {F.decb.of(m, M) == None{} : Maybe<&2, Nat>}

def bad_none(m, M, hb):
  match m:
    case None{}:
      {==}
    case Some{+v}:
      %Equal.sym(Bool, Nat.is_lt(v, M), False{}, hb) : {F.decb.if(v, _) == None{} : Maybe<&2, Nat>}
      {==}

law ena_add:
  for +acc: U32
  for +x: U32
  for +M: Nat
  for +emul: {U32.to_nat(U32.mul(acc, 10)) == Nat.mul(U32.to_nat(acc), U32.to_nat(10)) : Nat}
  for +ed: {U32.to_nat(U32.sub(x, 48)) == Nat.sub(U32.to_nat(x), 48n) : Nat}
  for +hb: {Nat.is_lt(Nat.add(Nat.mul(U32.to_nat(acc), 10n), Nat.sub(U32.to_nat(x), 48n)), M) == True{} : Bool}
  {Nat.is_lt(Nat.add(U32.to_nat(U32.mul(acc, 10)), U32.to_nat(U32.sub(x, 48))), M) == True{} : Bool}

def ena_add(acc, x, M, emul, ed, hb):
  %Equal.sym(Nat, U32.to_nat(U32.mul(acc, 10)), Nat.mul(U32.to_nat(acc), U32.to_nat(10)), emul) :
    {Nat.is_lt(Nat.add(_, U32.to_nat(U32.sub(x, 48))), M) == True{} : Bool}
  %Equal.sym(Nat, U32.to_nat(U32.sub(x, 48)), Nat.sub(U32.to_nat(x), 48n), ed) :
    {Nat.is_lt(Nat.add(Nat.mul(U32.to_nat(acc), U32.to_nat(10)), _), M) == True{} : Bool}
  hb

# The new value when the test passes (no wrap).
law ena:
  for +acc: U32
  for +x: U32
  for +M: Nat
  for +hm: {Nat.pow(2n, 32n) == M : Nat}
  for +hge: {U32.is_ge(x, 48) == True{} : Bool}
  for +hb: {Nat.is_lt(Nat.add(Nat.mul(U32.to_nat(acc), 10n), Nat.sub(U32.to_nat(x), 48n)), M) == True{} : Bool}
  {U32.to_nat(NA(acc, x)) == Nat.add(Nat.mul(U32.to_nat(acc), 10n), Nat.sub(U32.to_nat(x), 48n)) : Nat}

def ena(acc, x, M, hm, hge, hb):
  +A = U32.to_nat(acc)
  +KK = Nat.sub(U32.to_nat(x), 48n)
  +S = Nat.add(Nat.mul(A, 10n), KK)
  +hmul = N.le_lt_trans(Nat.mul(A, U32.to_nat(10)), S, M, N.le_add_r(Nat.mul(A, 10n), KK), hb)
  +emul = U.to_nat_mul_fits_p(acc, 10, lift(Nat.mul(U32.to_nat(acc), U32.to_nat(10)), M, hm, hmul))
  +ed = ed48(x, hge)
  +hadd = ena_add(acc, x, M, emul, ed, hb)
  +eadd = U.to_nat_add_fits_p(U32.mul(acc, 10), U32.sub(x, 48), lift(Nat.add(U32.to_nat(U32.mul(acc, 10)), U32.to_nat(U32.sub(x, 48))), M, hm, hadd))
  %Equal.sym(Nat, U32.to_nat(U32.add(U32.mul(acc, 10), U32.sub(x, 48))), Nat.add(U32.to_nat(U32.mul(acc, 10)), U32.to_nat(U32.sub(x, 48))), eadd) :
    {_ == S : Nat}
  %Equal.sym(Nat, U32.to_nat(U32.mul(acc, 10)), Nat.mul(A, U32.to_nat(10)), emul) : {Nat.add(_, U32.to_nat(U32.sub(x, 48))) == S : Nat}
  %Equal.sym(Nat, U32.to_nat(U32.sub(x, 48)), KK, ed) : {Nat.add(Nat.mul(A, U32.to_nat(10)), _) == S : Nat}
  {==}

# After a digit, by the overflow test (b).
law step_fb:
  for +acc: U32
  for +x: U32
  for +M: Nat
  for +b: Bool
  for +hm: {Nat.pow(2n, 32n) == M : Nat}
  for +hge: {U32.is_ge(x, 48) == True{} : Bool}
  for +hb: {Nat.is_lt(Nat.add(Nat.mul(U32.to_nat(acc), 10n), Nat.sub(U32.to_nat(x), 48n)), M) == b : Bool}
  Inv(b, NA(acc, x), Some{Nat.add(Nat.mul(U32.to_nat(acc), 10n), Nat.sub(U32.to_nat(x), 48n))}, M)

def step_fb(acc, x, M, b, hm, hge, hb):
  match b:
    case True{}:
      +S = Nat.add(Nat.mul(U32.to_nat(acc), 10n), Nat.sub(U32.to_nat(x), 48n))
      +e = Equal.sym(Nat, U32.to_nat(NA(acc, x)), S, ena(acc, x, M, hm, hge, hb))
      (Equal.cong(Nat, Maybe<&2, Nat>, v => Some{v}, S, U32.to_nat(NA(acc, x)), e),
        AB.subst(Nat, y => {Nat.is_lt(y, M) == True{} : Bool}, S, U32.to_nat(NA(acc, x)), e, hb))
    case False{}:
      hb

# After byte x, from value a, by the digit test (dg).
law step_dg:
  for +acc: U32
  for +x: U32
  for +M: Nat
  for +q: Nat
  for +dg: Bool
  for +hdg: {DG(x) == dg : Bool}
  for +hm: {Nat.pow(2n, 32n) == M : Nat}
  for +hcq: {U32.to_nat(429496729) == q : Nat}
  for +hq: {Nat.add(Nat.mul(q, 10n), 6n) == M : Nat}
  Inv(Bool.and(dg, FT(acc, x)), NA(acc, x), F.dec.push(Some{U32.to_nat(acc)}, F.digit.if(x, dg)), M)

def step_dg(acc, x, M, q, dg, hdg, hm, hcq, hq):
  match dg:
    case False{}:
      Unit{}
    case True{}:
      +hge = AB.and_true_l(U32.is_ge(x, 48), U32.is_le(x, 57), hdg)
      +hle = AB.and_true_r(U32.is_ge(x, 48), U32.is_le(x, 57), hdg)
      +S = Nat.add(Nat.mul(U32.to_nat(acc), 10n), Nat.sub(U32.to_nat(x), 48n))
      %Equal.sym(Bool, Bool.or(U32.is_lt(acc, 429496729), Bool.and(U32.is_eq(acc, 429496729), U32.is_le(U32.sub(x, 48), 5))), Nat.is_lt(S, M),
        FITSU(acc, x, 429496729, q, M, hcq, hq, hge, hle)) :
        Inv(_, NA(acc, x), Some{S}, M)
      step_fb(acc, x, M, Nat.is_lt(S, M), hm, hge, {==})

law inv_step:
  for +ok: Bool
  for +acc: U32
  for +m: Maybe<&2, Nat>
  for +x: U32
  for +M: Nat
  for +q: Nat
  for +hm: {Nat.pow(2n, 32n) == M : Nat}
  for +hcq: {U32.to_nat(429496729) == q : Nat}
  for +hq: {Nat.add(Nat.mul(q, 10n), 6n) == M : Nat}
  for +hi: Inv(ok, acc, m, M)
  Inv(Bool.and(ok, Bool.and(DG(x), FT(acc, x))), NA(acc, x), F.dec.push(m, F.digit(x)), M)

def inv_step(ok, acc, m, x, M, q, hm, hcq, hq, hi):
  match ok:
    case False{}:
      bad_step(m, F.digit(x), M, hi)
    case True{}:
      (e1, e2) = hi
      %Equal.sym(Maybe<&2, Nat>, m, Some{U32.to_nat(acc)}, e1) :
        Inv(Bool.and(DG(x), FT(acc, x)), NA(acc, x), F.dec.push(_, F.digit(x)), M)
      step_dg(acc, x, M, q, DG(x), {==}, hm, hcq, hq)

law base:
  for +ok: Bool
  for +acc: U32
  for +m: Maybe<&2, Nat>
  for +M: Nat
  for +hi: Inv(ok, acc, m, M)
  {F.nat_of(C.num.fin(acc, ok)) == F.decb.of(m, M) : Maybe<&2, Nat>}

def base(ok, acc, m, M, hi):
  match ok:
    case True{}:
      (+e1, +e2) = hi
      %Equal.sym(Maybe<&2, Nat>, m, Some{U32.to_nat(acc)}, e1) : {F.nat_of(C.num.fin(acc, True{})) == F.decb.of(_, M) : Maybe<&2, Nat>}
      %Equal.sym(Bool, Nat.is_lt(U32.to_nat(acc), M), True{}, e2) : {Some{U32.to_nat(acc)} == F.decb.if(U32.to_nat(acc), _) : Maybe<&2, Nat>}
      {==}
    case False{}:
      Equal.sym(Maybe<&2, Nat>, F.decb.of(m, M), None{}, bad_none(m, M, hi))

# The loop
# ========

law np:
  for +n: Nat
  for +len: U32
  for +t: P.Tree<U32>
  for +j: U32
  for +acc: U32
  for +ok: Bool
  {C.num.go(n, B.at(K.BT(len, t), j), j, acc, ok) == (K.BT(len, t), Pair.snd(D.Bytes, Maybe<&2, U32>, C.num.go(n, B.at(K.BT(len, t), j), j, acc, ok))) : D.Bytes & Maybe<&2, U32>}

def np(n, len, t, j, acc, ok):
  match n:
    case 0n:
      %Equal.sym(D.Bytes & U32, B.at(K.BT(len, t), j), (K.BT(len, t), K.AT(len, t, j)), K.at_pair_t(len, t, j)) :
        {C.num.go(0n, _, j, acc, ok) == (K.BT(len, t), Pair.snd(D.Bytes, Maybe<&2, U32>, C.num.go(0n, _, j, acc, ok))) : D.Bytes & Maybe<&2, U32>}
      {==}
    case 1n+k:
      +x = K.AT(len, t, j)
      %Equal.sym(D.Bytes & U32, B.at(K.BT(len, t), j), (K.BT(len, t), x), K.at_pair_t(len, t, j)) :
        {C.num.go(1n+k, _, j, acc, ok) == (K.BT(len, t), Pair.snd(D.Bytes, Maybe<&2, U32>, C.num.go(1n+k, _, j, acc, ok))) : D.Bytes & Maybe<&2, U32>}
      np(k, len, t, (j + 1 : U32), NA(acc, x), Bool.and(ok, Bool.and(DG(x), FT(acc, x))))

law num_pair_t:
  for +len: U32
  for +t: P.Tree<U32>
  for +from: U32
  for +to: U32
  {C.num(K.BT(len, t), from, to) == (K.BT(len, t), Pair.snd(D.Bytes, Maybe<&2, U32>, C.num(K.BT(len, t), from, to))) : D.Bytes & Maybe<&2, U32>}

def num_pair_t(len, t, from, to):
  np(Nat.sub(U32.to_nat(to), U32.to_nat(from)), len, t, from, 0, U32.is_lt(from, to))

law nv:
  for +n: Nat
  for +len: U32
  for +t: P.Tree<U32>
  for +d: Nat
  for +j: U32
  for +ok: Bool
  for +acc: U32
  for +m: Maybe<&2, Nat>
  for +M: Nat
  for +q: Nat
  for +hm: {Nat.pow(2n, 32n) == M : Nat}
  for +hcq: {U32.to_nat(429496729) == q : Nat}
  for +hq: {Nat.add(Nat.mul(q, 10n), 6n) == M : Nat}
  for +h: {D.ok(K.BT(len, t), d) == True{} : Bool}
  for +hjn: {Nat.is_le(Nat.add(U32.to_nat(j), n), U32.to_nat(len)) == True{} : Bool}
  for +hi: Inv(ok, acc, m, M)
  {F.nat_of(Pair.snd(D.Bytes, Maybe<&2, U32>, C.num.go(n, B.at(K.BT(len, t), j), j, acc, ok))) == F.decb.of(F.dec.go(D.slice(D.view(K.BT(len, t)), U32.to_nat(j), n), m), M) : Maybe<&2, Nat>}

def nv(n, len, t, d, j, ok, acc, m, M, q, hm, hcq, hq, h, hjn, hi):
  match n:
    case 0n:
      +xs = D.view(K.BT(len, t))
      %Equal.sym(D.Bytes & U32, B.at(K.BT(len, t), j), (K.BT(len, t), K.AT(len, t, j)), K.at_pair_t(len, t, j)) :
        {F.nat_of(Pair.snd(D.Bytes, Maybe<&2, U32>, C.num.go(0n, _, j, acc, ok))) == F.decb.of(F.dec.go(D.slice(xs, U32.to_nat(j), 0n), m), M) : Maybe<&2, Nat>}
      %Equal.sym(List<&2, U32>, D.slice(xs, U32.to_nat(j), 0n), Nil{}, X.slice_zero(xs, U32.to_nat(j))) :
        {F.nat_of(C.num.fin(acc, ok)) == F.decb.of(F.dec.go(_, m), M) : Maybe<&2, Nat>}
      base(ok, acc, m, M, hi)
    case 1n+k:
      +xs = D.view(K.BT(len, t))
      +JJ = U32.to_nat(j)
      +x = K.AT(len, t, j)
      +j1 = (j + 1 : U32)
      +ok1 = Bool.and(ok, Bool.and(DG(x), FT(acc, x)))
      +hx = Equal.sym(Maybe<&2, U32>, Some{x}, List.get(&2, U32, xs, JJ),
        K.at_view_t(len, t, d, j, K.ok_full(len, t, d, h), K.ok_d(len, t, d, h), K.ok_len(len, t, d, h), X.read_lt(len, j, k, hjn)))
      %Equal.sym(D.Bytes & U32, B.at(K.BT(len, t), j), (K.BT(len, t), x), K.at_pair_t(len, t, j)) :
        {F.nat_of(Pair.snd(D.Bytes, Maybe<&2, U32>, C.num.go(1n+k, _, j, acc, ok))) == F.decb.of(F.dec.go(D.slice(xs, JJ, 1n+k), m), M) : Maybe<&2, Nat>}
      %Equal.sym(List<&2, U32>, D.slice(xs, JJ, 1n+k), x <> D.slice(xs, Nat.add(JJ, 1n), k), X.slice_cons(xs, JJ, k, x, hx)) :
        {F.nat_of(Pair.snd(D.Bytes, Maybe<&2, U32>, C.num.go(k, B.at(K.BT(len, t), j1), j1, NA(acc, x), ok1))) == F.decb.of(F.dec.go(_, m), M) : Maybe<&2, Nat>}
      %X.read_inc(len, t, d, j, k, h, hjn) :
        {F.nat_of(Pair.snd(D.Bytes, Maybe<&2, U32>, C.num.go(k, B.at(K.BT(len, t), j1), j1, NA(acc, x), ok1))) == F.decb.of(F.dec.go(D.slice(xs, _, k), F.dec.push(m, F.digit(x))), M) : Maybe<&2, Nat>}
      nv(k, len, t, d, j1, ok1, NA(acc, x), F.dec.push(m, F.digit(x)), M, q, hm, hcq, hq, h, X.read_next(len, t, d, j, k, h, hjn),
        inv_step(ok, acc, m, x, M, q, hm, hcq, hq, hi))

# Entering the loop
# =================

law sub0_nlt:
  for +a: Nat
  for +b: Nat
  for +h: {Nat.sub(b, a) == 0n : Nat}
  {Nat.is_lt(a, b) == False{} : Bool}

def sub0_nlt(a, b, h):
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+r:
      Empty.absurd({Nat.is_lt(0n, 1n+r) == False{} : Bool}, AB.succ_ne_zero(r, h))
    case 1n+p 0n:
      {==}
    case 1n+p 1n+r:
      sub0_nlt(p, r, h)

law subs_lt:
  for +a: Nat
  for +b: Nat
  for +k: Nat
  for +h: {Nat.sub(b, a) == 1n+k : Nat}
  {Nat.is_lt(a, b) == True{} : Bool}

def subs_lt(a, b, k, h):
  match a b:
    case 0n 0n:
      Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, AB.succ_ne_zero(k, Equal.sym(Nat, 0n, 1n+k, h)))
    case 0n 1n+r:
      {==}
    case 1n+p 0n:
      Empty.absurd({Nat.is_lt(1n+p, 0n) == True{} : Bool}, AB.succ_ne_zero(k, Equal.sym(Nat, 0n, 1n+k, h)))
    case 1n+p 1n+r:
      subs_lt(p, r, k, h)

law decs:
  for +xs: List<&2, U32>
  for +i: Nat
  for +k: Nat
  for +x: U32
  for +M: Nat
  for +hx: {List.get(&2, U32, xs, i) == Some{x} : Maybe<&2, U32>}
  {F.decb(D.slice(xs, i, 1n+k), M) == F.decb.of(F.dec.go(D.slice(xs, i, 1n+k), Some{0n}), M) : Maybe<&2, Nat>}

def decs(xs, i, k, x, M, hx):
  %Equal.sym(List<&2, U32>, D.slice(xs, i, 1n+k), x <> D.slice(xs, Nat.add(i, 1n), k), X.slice_cons(xs, i, k, x, hx)) :
    {F.decb(_, M) == F.decb.of(F.dec.go(_, Some{0n}), M) : Maybe<&2, Nat>}
  {==}

law nvt2:
  for +n: Nat
  for +len: U32
  for +t: P.Tree<U32>
  for +d: Nat
  for +from: U32
  for +to: U32
  for +M: Nat
  for +q: Nat
  for +hm: {Nat.pow(2n, 32n) == M : Nat}
  for +hcq: {U32.to_nat(429496729) == q : Nat}
  for +hq: {Nat.add(Nat.mul(q, 10n), 6n) == M : Nat}
  for +h: {D.ok(K.BT(len, t), d) == True{} : Bool}
  for +hft: {U32.is_le(from, to) == True{} : Bool}
  for +ht: {Nat.is_le(U32.to_nat(to), D.size(K.BT(len, t))) == True{} : Bool}
  for +hn: {Nat.sub(U32.to_nat(to), U32.to_nat(from)) == n : Nat}
  {F.nat_of(Pair.snd(D.Bytes, Maybe<&2, U32>, C.num(K.BT(len, t), from, to))) == F.decb(D.slice(D.view(K.BT(len, t)), U32.to_nat(from), Nat.sub(U32.to_nat(to), U32.to_nat(from))), M) : Maybe<&2, Nat>}

def nvt2(n, len, t, d, from, to, M, q, hm, hcq, hq, h, hft, ht, hn):
  match n:
    case 0n:
      +xs = D.view(K.BT(len, t))
      +FF = U32.to_nat(from)
      +TT = U32.to_nat(to)
      +nlt = Equal.trans(Bool, U32.is_lt(from, to), Nat.is_lt(FF, TT), False{}, U.is_lt_to_nat(from, to), sub0_nlt(FF, TT, hn))
      %Equal.sym(Nat, Nat.sub(TT, FF), 0n, hn) :
        {F.nat_of(Pair.snd(D.Bytes, Maybe<&2, U32>, C.num.go(_, B.at(K.BT(len, t), from), from, 0, U32.is_lt(from, to)))) == F.decb(D.slice(xs, FF, _), M) : Maybe<&2, Nat>}
      %Equal.sym(D.Bytes & U32, B.at(K.BT(len, t), from), (K.BT(len, t), K.AT(len, t, from)), K.at_pair_t(len, t, from)) :
        {F.nat_of(Pair.snd(D.Bytes, Maybe<&2, U32>, C.num.go(0n, _, from, 0, U32.is_lt(from, to)))) == F.decb(D.slice(xs, FF, 0n), M) : Maybe<&2, Nat>}
      %Equal.sym(Bool, U32.is_lt(from, to), False{}, nlt) :
        {F.nat_of(C.num.fin(0, _)) == F.decb(D.slice(xs, FF, 0n), M) : Maybe<&2, Nat>}
      %Equal.sym(List<&2, U32>, D.slice(xs, FF, 0n), Nil{}, X.slice_zero(xs, FF)) :
        {F.nat_of(C.num.fin(0, False{})) == F.decb(_, M) : Maybe<&2, Nat>}
      {==}
    case 1n+k:
      +xs = D.view(K.BT(len, t))
      +FF = U32.to_nat(from)
      +TT = U32.to_nat(to)
      +LL = U32.to_nat(len)
      +hlt = subs_lt(FF, TT, k, hn)
      +lt1 = Equal.trans(Bool, U32.is_lt(from, to), Nat.is_lt(FF, TT), True{}, U.is_lt_to_nat(from, to), hlt)
      +hFT = Equal.trans(Bool, Nat.is_le(FF, TT), U32.is_le(from, to), True{}, Equal.sym(Bool, U32.is_le(from, to), Nat.is_le(FF, TT), U.is_le_to_nat(from, to)), hft)
      +eT = Equal.trans(Nat, Nat.add(FF, 1n+k), Nat.add(FF, Nat.sub(TT, FF)), TT,
        Equal.cong(Nat, Nat, y => Nat.add(FF, y), 1n+k, Nat.sub(TT, FF), Equal.sym(Nat, Nat.sub(TT, FF), 1n+k, hn)), N.le_sub_add(FF, TT, hFT))
      +hjn = AB.subst(Nat, y => {Nat.is_le(y, LL) == True{} : Bool}, TT, Nat.add(FF, 1n+k), Equal.sym(Nat, Nat.add(FF, 1n+k), TT, eT), ht)
      +hx = Equal.sym(Maybe<&2, U32>, Some{K.AT(len, t, from)}, List.get(&2, U32, xs, FF),
        K.at_view_t(len, t, d, from, K.ok_full(len, t, d, h), K.ok_d(len, t, d, h), K.ok_len(len, t, d, h), N.lt_le_trans(FF, TT, LL, hlt, ht)))
      %Equal.sym(Nat, Nat.sub(TT, FF), 1n+k, hn) :
        {F.nat_of(Pair.snd(D.Bytes, Maybe<&2, U32>, C.num.go(_, B.at(K.BT(len, t), from), from, 0, U32.is_lt(from, to)))) == F.decb(D.slice(xs, FF, _), M) : Maybe<&2, Nat>}
      %Equal.sym(Bool, U32.is_lt(from, to), True{}, lt1) :
        {F.nat_of(Pair.snd(D.Bytes, Maybe<&2, U32>, C.num.go(1n+k, B.at(K.BT(len, t), from), from, 0, _))) == F.decb(D.slice(xs, FF, 1n+k), M) : Maybe<&2, Nat>}
      %Equal.sym(Maybe<&2, Nat>, F.decb(D.slice(xs, FF, 1n+k), M), F.decb.of(F.dec.go(D.slice(xs, FF, 1n+k), Some{0n}), M), decs(xs, FF, k, K.AT(len, t, from), M, hx)) :
        {F.nat_of(Pair.snd(D.Bytes, Maybe<&2, U32>, C.num.go(1n+k, B.at(K.BT(len, t), from), from, 0, True{}))) == _ : Maybe<&2, Nat>}
      nv(1n+k, len, t, d, from, True{}, 0, Some{U32.to_nat(0)}, M, q, hm, hcq, hq, h, hjn, ({==}, posM(M, hm)))

law nvt:
  for +len: U32
  for +t: P.Tree<U32>
  for +d: Nat
  for +from: U32
  for +to: U32
  for +M: Nat
  for +q: Nat
  for +hm: {Nat.pow(2n, 32n) == M : Nat}
  for +hcq: {U32.to_nat(429496729) == q : Nat}
  for +hq: {Nat.add(Nat.mul(q, 10n), 6n) == M : Nat}
  for +h: {D.ok(K.BT(len, t), d) == True{} : Bool}
  for +hft: {U32.is_le(from, to) == True{} : Bool}
  for +ht: {Nat.is_le(U32.to_nat(to), D.size(K.BT(len, t))) == True{} : Bool}
  {F.nat_of(Pair.snd(D.Bytes, Maybe<&2, U32>, C.num(K.BT(len, t), from, to))) == F.decb(D.slice(D.view(K.BT(len, t)), U32.to_nat(from), Nat.sub(U32.to_nat(to), U32.to_nat(from))), M) : Maybe<&2, Nat>}

def nvt(len, t, d, from, to, M, q, hm, hcq, hq, h, hft, ht):
  nvt2(Nat.sub(U32.to_nat(to), U32.to_nat(from)), len, t, d, from, to, M, q, hm, hcq, hq, h, hft, ht, {==})

# The law, with the bound 2^32 and the constant's value put in only here.
law num_view_t:
  for +len: U32
  for +t: P.Tree<U32>
  for +d: Nat
  for +from: U32
  for +to: U32
  for +h: {D.ok(K.BT(len, t), d) == True{} : Bool}
  for +hft: {U32.is_le(from, to) == True{} : Bool}
  for +ht: {Nat.is_le(U32.to_nat(to), D.size(K.BT(len, t))) == True{} : Bool}
  {F.nat_of(Pair.snd(D.Bytes, Maybe<&2, U32>, C.num(K.BT(len, t), from, to))) == F.decb(D.slice(D.view(K.BT(len, t)), U32.to_nat(from), Nat.sub(U32.to_nat(to), U32.to_nat(from))), Nat.pow(2n, 32n)) : Maybe<&2, Nat>}

def num_view_t(len, t, d, from, to, h, hft, ht):
  nvt(len, t, d, from, to, Nat.pow(2n, 32n), U32.to_nat(429496729), {==}, {==}, QM(Nat.pow(2n, 32n), {==}), h, hft, ht)

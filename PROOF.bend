import Base
import lawful-bytes@0.1.0.0/defs.bend as D
import ./defs.bend as F
import ./fields.bend as C
import ./LAWS.bend as L
import lawful-bytes@0.1.0.0/proof_core.bend as BC
import ./proof_list.bend as Q
import ./proof_cut.bend as Z
import ./proof_num.bend as NU
import ./proof_digits.bend as DG

# Proofs of the laws: `def L.name` proves `law name` of LAWS.bend. A Bytes can
# be used once, so each law about one goes through lawful-bytes' mirror
# (BC.bmirror): BC.BT(len, t) with a Tree<U32> t.

# Laws about a Bytes
# ==================

# One wrapper per law (written mechanically from LAWS.bend): it mirrors each
# Bytes b, rewrites the goal, transports the hypotheses and calls the mirror
# lemma `name_t`, which is law `name` with b replaced by BC.BT(l_b, t_b).

def cut_view.go(-b: D.Bytes, +d: Nat, +from: U32, +to: U32, +sep: U32, +n: Nat, h: {D.ok(b, d) == True{} : Bool}, hft: {U32.is_le(from, to) == True{} : Bool}, ht: {Nat.is_le(U32.to_nat(to), D.size(b)) == True{} : Bool}, hs: {U32.is_lt(sep, 256) == True{} : Bool}, m_b: BC.BMirror(b)) ->
  {F.pieces(Pair.snd(D.Bytes, List<&2, U32>, C.cut(b, from, to, sep, n)), D.view(b), U32.to_nat(from)) == List.take(&2, List<&2, U32>, F.split(D.slice(D.view(b), U32.to_nat(from), Nat.sub(U32.to_nat(to), U32.to_nat(from))), sep), n) : List<&2, List<&2, U32>>}:
  (+l_b, m2_b) = m_b
  (+t_b, +e_b) = m2_b
  %e_b : {F.pieces(Pair.snd(D.Bytes, List<&2, U32>, C.cut(_, from, to, sep, n)), D.view(_), U32.to_nat(from)) == List.take(&2, List<&2, U32>, F.split(D.slice(D.view(_), U32.to_nat(from), Nat.sub(U32.to_nat(to), U32.to_nat(from))), sep), n) : List<&2, List<&2, U32>>}
  +h_t = BC.tr(x => {D.ok(x, d) == True{} : Bool}, b, l_b, t_b, e_b, h)
  +ht_t = BC.tr(x => {Nat.is_le(U32.to_nat(to), D.size(x)) == True{} : Bool}, b, l_b, t_b, e_b, ht)
  Z.cut_view_t(l_b, t_b, d, from, to, sep, n, h_t, hft, ht_t, hs)

def L.cut_view(b, d, from, to, sep, n, h, hft, ht, hs):
  cut_view.go(b, d, from, to, sep, n, h, hft, ht, hs, BC.bmirror(b))

def cut_ends.go(-b: D.Bytes, +d: Nat, +from: U32, +to: U32, +sep: U32, +n: Nat, h: {D.ok(b, d) == True{} : Bool}, hft: {U32.is_le(from, to) == True{} : Bool}, ht: {Nat.is_le(U32.to_nat(to), D.size(b)) == True{} : Bool}, hs: {U32.is_lt(sep, 256) == True{} : Bool}, m_b: BC.BMirror(b)) ->
  {F.nats(Pair.snd(D.Bytes, List<&2, U32>, C.cut(b, from, to, sep, n))) == List.take(&2, Nat, F.ends(F.split(D.slice(D.view(b), U32.to_nat(from), Nat.sub(U32.to_nat(to), U32.to_nat(from))), sep), U32.to_nat(from)), n) : List<&2, Nat>}:
  (+l_b, m2_b) = m_b
  (+t_b, +e_b) = m2_b
  %e_b : {F.nats(Pair.snd(D.Bytes, List<&2, U32>, C.cut(_, from, to, sep, n))) == List.take(&2, Nat, F.ends(F.split(D.slice(D.view(_), U32.to_nat(from), Nat.sub(U32.to_nat(to), U32.to_nat(from))), sep), U32.to_nat(from)), n) : List<&2, Nat>}
  +h_t = BC.tr(x => {D.ok(x, d) == True{} : Bool}, b, l_b, t_b, e_b, h)
  +ht_t = BC.tr(x => {Nat.is_le(U32.to_nat(to), D.size(x)) == True{} : Bool}, b, l_b, t_b, e_b, ht)
  Z.cut_ends_t(l_b, t_b, d, from, to, sep, n, h_t, hft, ht_t, hs)

def L.cut_ends(b, d, from, to, sep, n, h, hft, ht, hs):
  cut_ends.go(b, d, from, to, sep, n, h, hft, ht, hs, BC.bmirror(b))

def cut_bounds.go(-b: D.Bytes, +d: Nat, +from: U32, +to: U32, +sep: U32, +n: Nat, h: {D.ok(b, d) == True{} : Bool}, hft: {U32.is_le(from, to) == True{} : Bool}, ht: {Nat.is_le(U32.to_nat(to), D.size(b)) == True{} : Bool}, hs: {U32.is_lt(sep, 256) == True{} : Bool}, m_b: BC.BMirror(b)) ->
  {F.within(Pair.snd(D.Bytes, List<&2, U32>, C.cut(b, from, to, sep, n)), U32.to_nat(from), U32.to_nat(to)) == True{} : Bool}:
  (+l_b, m2_b) = m_b
  (+t_b, +e_b) = m2_b
  %e_b : {F.within(Pair.snd(D.Bytes, List<&2, U32>, C.cut(_, from, to, sep, n)), U32.to_nat(from), U32.to_nat(to)) == True{} : Bool}
  +h_t = BC.tr(x => {D.ok(x, d) == True{} : Bool}, b, l_b, t_b, e_b, h)
  +ht_t = BC.tr(x => {Nat.is_le(U32.to_nat(to), D.size(x)) == True{} : Bool}, b, l_b, t_b, e_b, ht)
  Z.cut_bounds_t(l_b, t_b, d, from, to, sep, n, h_t, hft, ht_t, hs)

def L.cut_bounds(b, d, from, to, sep, n, h, hft, ht, hs):
  cut_bounds.go(b, d, from, to, sep, n, h, hft, ht, hs, BC.bmirror(b))

def cut_pair.go(-b: D.Bytes, +from: U32, +to: U32, +sep: U32, +n: Nat, m_b: BC.BMirror(b)) ->
  {C.cut(b, from, to, sep, n) == (b, Pair.snd(D.Bytes, List<&2, U32>, C.cut(b, from, to, sep, n))) : D.Bytes & List<&2, U32>}:
  (+l_b, m2_b) = m_b
  (+t_b, +e_b) = m2_b
  %e_b : {C.cut(_, from, to, sep, n) == (_, Pair.snd(D.Bytes, List<&2, U32>, C.cut(_, from, to, sep, n))) : D.Bytes & List<&2, U32>}
  Z.cut_pair_t(l_b, t_b, from, to, sep, n)

def L.cut_pair(b, from, to, sep, n):
  cut_pair.go(b, from, to, sep, n, BC.bmirror(b))

def num_view.go(-b: D.Bytes, +d: Nat, +from: U32, +to: U32, h: {D.ok(b, d) == True{} : Bool}, hft: {U32.is_le(from, to) == True{} : Bool}, ht: {Nat.is_le(U32.to_nat(to), D.size(b)) == True{} : Bool}, m_b: BC.BMirror(b)) ->
  {F.nat_of(Pair.snd(D.Bytes, Maybe<&2, U32>, C.num(b, from, to))) == F.decb(D.slice(D.view(b), U32.to_nat(from), Nat.sub(U32.to_nat(to), U32.to_nat(from))), Nat.pow(2n, 32n)) : Maybe<&2, Nat>}:
  (+l_b, m2_b) = m_b
  (+t_b, +e_b) = m2_b
  %e_b : {F.nat_of(Pair.snd(D.Bytes, Maybe<&2, U32>, C.num(_, from, to))) == F.decb(D.slice(D.view(_), U32.to_nat(from), Nat.sub(U32.to_nat(to), U32.to_nat(from))), Nat.pow(2n, 32n)) : Maybe<&2, Nat>}
  +h_t = BC.tr(x => {D.ok(x, d) == True{} : Bool}, b, l_b, t_b, e_b, h)
  +ht_t = BC.tr(x => {Nat.is_le(U32.to_nat(to), D.size(x)) == True{} : Bool}, b, l_b, t_b, e_b, ht)
  NU.num_view_t(l_b, t_b, d, from, to, h_t, hft, ht_t)

def L.num_view(b, d, from, to, h, hft, ht):
  num_view.go(b, d, from, to, h, hft, ht, BC.bmirror(b))

def num_pair.go(-b: D.Bytes, +from: U32, +to: U32, m_b: BC.BMirror(b)) ->
  {C.num(b, from, to) == (b, Pair.snd(D.Bytes, Maybe<&2, U32>, C.num(b, from, to))) : D.Bytes & Maybe<&2, U32>}:
  (+l_b, m2_b) = m_b
  (+t_b, +e_b) = m2_b
  %e_b : {C.num(_, from, to) == (_, Pair.snd(D.Bytes, Maybe<&2, U32>, C.num(_, from, to))) : D.Bytes & Maybe<&2, U32>}
  NU.num_pair_t(l_b, t_b, from, to)

def L.num_pair(b, from, to):
  num_pair.go(b, from, to, BC.bmirror(b))

def digits_view.go(-b: D.Bytes, +d: Nat, +from: U32, +to: U32, h: {D.ok(b, d) == True{} : Bool}, hft: {U32.is_le(from, to) == True{} : Bool}, ht: {Nat.is_le(U32.to_nat(to), D.size(b)) == True{} : Bool}, m_b: BC.BMirror(b)) ->
  {Pair.snd(D.Bytes, Bool, C.digits(b, from, to)) == F.all_digits(D.slice(D.view(b), U32.to_nat(from), Nat.sub(U32.to_nat(to), U32.to_nat(from)))) : Bool}:
  (+l_b, m2_b) = m_b
  (+t_b, +e_b) = m2_b
  %e_b : {Pair.snd(D.Bytes, Bool, C.digits(_, from, to)) == F.all_digits(D.slice(D.view(_), U32.to_nat(from), Nat.sub(U32.to_nat(to), U32.to_nat(from)))) : Bool}
  +h_t = BC.tr(x => {D.ok(x, d) == True{} : Bool}, b, l_b, t_b, e_b, h)
  +ht_t = BC.tr(x => {Nat.is_le(U32.to_nat(to), D.size(x)) == True{} : Bool}, b, l_b, t_b, e_b, ht)
  DG.digits_view_t(l_b, t_b, d, from, to, h_t, hft, ht_t)

def L.digits_view(b, d, from, to, h, hft, ht):
  digits_view.go(b, d, from, to, h, hft, ht, BC.bmirror(b))

def digits_pair.go(-b: D.Bytes, +from: U32, +to: U32, m_b: BC.BMirror(b)) ->
  {C.digits(b, from, to) == (b, Pair.snd(D.Bytes, Bool, C.digits(b, from, to))) : D.Bytes & Bool}:
  (+l_b, m2_b) = m_b
  (+t_b, +e_b) = m2_b
  %e_b : {C.digits(_, from, to) == (_, Pair.snd(D.Bytes, Bool, C.digits(_, from, to))) : D.Bytes & Bool}
  DG.digits_pair_t(l_b, t_b, from, to)

def L.digits_pair(b, from, to):
  digits_pair.go(b, from, to, BC.bmirror(b))

def put_dec_view.go(-b: D.Bytes, +d: Nat, +n: U32, h: {D.ok(b, d) == True{} : Bool}, hc: {Nat.is_le(Nat.add(D.size(b), 10n), D.cap(b)) == True{} : Bool}, m_b: BC.BMirror(b)) ->
  {D.view(C.put_dec(b, n)) == List.append(&2, U32, D.view(b), F.show(n)) : List<&2, U32>}:
  (+l_b, m2_b) = m_b
  (+t_b, +e_b) = m2_b
  %e_b : {D.view(C.put_dec(_, n)) == List.append(&2, U32, D.view(_), F.show(n)) : List<&2, U32>}
  +h_t = BC.tr(x => {D.ok(x, d) == True{} : Bool}, b, l_b, t_b, e_b, h)
  +hc_t = BC.tr(x => {Nat.is_le(Nat.add(D.size(x), 10n), D.cap(x)) == True{} : Bool}, b, l_b, t_b, e_b, hc)
  DG.put_dec_view_t(l_b, t_b, d, n, h_t, hc_t)

def L.put_dec_view(b, d, n, h, hc):
  put_dec_view.go(b, d, n, h, hc, BC.bmirror(b))

def put_dec_ok.go(-b: D.Bytes, +d: Nat, +n: U32, h: {D.ok(b, d) == True{} : Bool}, hc: {Nat.is_le(Nat.add(D.size(b), 10n), D.cap(b)) == True{} : Bool}, m_b: BC.BMirror(b)) ->
  {D.ok(C.put_dec(b, n), d) == True{} : Bool}:
  (+l_b, m2_b) = m_b
  (+t_b, +e_b) = m2_b
  %e_b : {D.ok(C.put_dec(_, n), d) == True{} : Bool}
  +h_t = BC.tr(x => {D.ok(x, d) == True{} : Bool}, b, l_b, t_b, e_b, h)
  +hc_t = BC.tr(x => {Nat.is_le(Nat.add(D.size(x), 10n), D.cap(x)) == True{} : Bool}, b, l_b, t_b, e_b, hc)
  DG.put_dec_ok_t(l_b, t_b, d, n, h_t, hc_t)

def L.put_dec_ok(b, d, n, h, hc):
  put_dec_ok.go(b, d, n, h, hc, BC.bmirror(b))


# Lists, text and decimal numbers (no Bytes parameter)
# ====================================================

def L.split_length(xs, sep):
  Q.split_length(xs, sep)

def L.split_join(xs, sep):
  Q.split_join(xs, sep)

def L.split_text(xs, sep):
  Q.split_text(xs, sep)

def L.join_text(ps, sep):
  Q.join_text(ps, sep)

def L.text_codes(s):
  Q.text_codes(s)

def L.join_at(ps, sep, k, h):
  Q.join_at(ps, sep, k, h)

def L.ends_join(ps, sep, from, k, h):
  Q.ends_join(ps, sep, from, k, h)

def L.pieces_length(es, xs, from):
  Q.pieces_length(es, xs, from)

def L.decb_fits(xs, n, h, hn):
  Q.decb_fits(xs, n, h, hn)

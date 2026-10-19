import LeanEVM.Util.Bytes

/- =============================================================== -/
/- Uint4 -/
/- =============================================================== -/

abbrev UInt4 := Fin 16
@[simp]
abbrev U4_MAX : UInt4 := {val:=15, isLt:=(by simp +arith)}

/- =============================================================== -/
/- U256 -/
/- =============================================================== -/

abbrev UInt256 := Fin (2^256)
@[simp]
abbrev U256_MAX : UInt256 := {val:=(2^256) - 1, isLt:=(by simp +arith)}

example : Fin.add 1 U256_MAX = 0 :=
by
  rfl

-- Construct an unsigned 256bit integer from a sequence of at most 32 bytes,
-- assuming a big endian order (i.e. most significant byte first).
def UInt256.from_bytes(bytes: Bytes32) : UInt256 :=
  let k := bytes.length
  -- Convert bytes into nat
  let n := from_bytes_be bytes.data;
  -- Bound size of n using lemma
  have p : n < 256^k := (from_bytes_be_bound bytes.data)
  have q : 256^k <= 256^32 := by
    exact Nat.pow_le_pow_right (by decide : 256 > 0) bytes.isLt
   --apply (pow_nm 256 k 32 bytes.isLt)
  have r : n < 256^32 := by exact Nat.lt_of_lt_of_le p q
  -- Convert nat into UInt256
  {val:=n, isLt:=by exact r}

/- =============================================================== -/
/- Helpers -/
/- =============================================================== -/

-- Simple proof relating the size of a list to its structure.
theorem len_succ {a:Type} (h:a)(t:List a) : (h::t).length = t.length+1  :=
by
  induction t
  repeat simp

/- =============================================================== -/
/- Tests -/
/- =============================================================== -/

-- Simple demonstration that a singleton byte array returns its only byte as the
-- result.
example (n:UInt8)(bs:Bytes32)(p:bs.data=[n]): (UInt256.from_bytes bs).val = n.toNat :=
by
  simp [UInt256.from_bytes, from_bytes_be, p]

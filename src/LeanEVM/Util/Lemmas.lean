-- A simple proof for "left shifting" bytes.  Suppose a value n which fits
-- within an array of k bytes.  We want to left shift that array and append a
-- new byte in the rightmost position.  This lemma then tells us that the
-- resulting number fits within k+1 bytes.
theorem pow256_shl(n:Nat)(m:UInt8)(k:Nat)(p:n < 256^k) : (256*n + m.toNat < 256^(k+1)) :=
by
  have s : 256*n + 256 ≤ 256^(k+1) := by omega
  have h : m.toNat < 256 := by
    simpa [UInt8.size] using m.toNat_lt_size
  have r : 256*n + m.toNat < 256*n + 256 := by
    exact Nat.add_lt_add_left h (256 * n)
  exact Nat.lt_of_lt_of_le r s

-- A simple proof for "right shifting" bytes.  Suppose a value n which fits
-- within an array of k bytes.  We want to append a new byte in the leftmost
-- position.  This lemma then tells us that the resulting number fits within k+1
-- bytes.
theorem pow256_shr(n:Nat)(m:UInt8)(k:Nat)(p:n < 256^k) : (m.toNat * 256^k + n < 256^(k+1)) :=
by
  let l := m.toNat
  --
  have q : l ≤ 255 := by
    have h : l < 256 := by
      simpa [l, UInt8.size] using m.toNat_lt_size
    omega
  have r : l * 256^k ≤ 255*256^k := by exact Nat.mul_le_mul_right (256 ^ k) q
  have s : l * 256^k + 256^k ≤ 256^(k+1) := by omega
  have t : l * 256^k + n < l * 256^k + 256^k := by
    exact Nat.add_lt_add_left p (l * 256 ^ k)
  exact Nat.lt_of_lt_of_le t s

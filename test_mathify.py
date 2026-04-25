import sys
sys.path.append('sophie')
import math_markup

text = r'Prove an explicit formula for primes p ≡ 73 (mod 840), equivalently $p \equiv 1 \pmod{24}$, $p \equiv 3 \pmod{5}$, and p ≡ ±3 (mod 7).'
print("ORIGINAL:", text)
print("MATHIFY: ", math_markup.mathify(text))

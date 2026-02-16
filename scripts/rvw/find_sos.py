"""Find SOS decomposition for S_max^2 - S^2 >= 0."""
from sympy import *

A, B, C, p, q, r, h = symbols('A B C p q r h')
E = 2*A*B - B + C
S = 4*A*B*q + 2*A*B*r + E*p
S_max_sq = 4*A**2*B*C + (B-C)**2*p**2
target = expand(S_max_sq - S**2)
Fp = (A+p)*(C+r) - q**2
Fm = (A-p)*(C-r) - q**2

# Try alpha = 8A^2B^2 + h*p, beta = 8A^2B^2 - h*p
alpha = 8*A**2*B**2 + h*p
beta = 8*A**2*B**2 - h*p
remainder = expand(target - alpha * expand(Fp) - beta * expand(Fm))
coeff_q = expand(remainder.coeff(q, 1))
print(f"Coeff of q: {coeff_q}")
h_eq = solve(coeff_q, h)
print(f"h = {h_eq}")

if h_eq:
    h_val = h_eq[0]
    rem2 = expand(remainder.subs(h, h_val))
    print(f"\nRemainder (no q): {rem2}")
    # Check as quadratic in r
    rc2 = expand(rem2.coeff(r, 2))
    rc1 = expand(rem2.coeff(r, 1))
    rc0 = expand(rem2.coeff(r, 0))
    print(f"r^2: {rc2}")
    print(f"r^1: {rc1}")
    print(f"r^0: {rc0}")
    disc = expand(rc1**2 - 4*rc2*rc0)
    print(f"Disc: {factor(disc)}")
    disc_sub = expand(disc.subs(B, 1-A))
    print(f"Disc(B=1-A): {factor(disc_sub)}")

    # Also check alpha, beta non-negativity
    print(f"\nalpha = 8A^2B^2 + ({h_val})*p")
    print(f"beta = 8A^2B^2 - ({h_val})*p")

    # Try different split: alpha = 8A^2B^2 + h1*p + h2*r, etc.

// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Shared GCD, Bézout and finite-word CRT helpers. No domain operations.
#![allow(unused_imports, unused_variables)]
use crate::word::Word;
use vstd::prelude::*;
use vstd::arithmetic::div_mod::*;

verus! {

/// Deterministic Euclidean specification, including gcd(0, 0) = 0.
pub open spec fn gcd_spec(a: nat, b: nat) -> nat
    decreases b,
{
    if b == 0 { a } else { gcd_spec(b, a % b) }
}

/// Returns true if d is a positive common divisor of a and b.
/// A common divisor divides both a and b without a remainder.
pub open spec fn is_common_divisor(d: nat, a: nat, b: nat) -> bool {
    d > 0 && a % d == 0 && b % d == 0
}

/// Returns true if d is the greatest common divisor of a and b.
/// The special case gcd(0, 0) = 0 is handled separately.
pub open spec fn is_gcd(d: nat, a: nat, b: nat) -> bool {
    if a == 0 && b == 0 {
        d == 0
    } else {
        is_common_divisor(d, a, b)
        && forall|k: nat|
            #[trigger] is_common_divisor(k, a, b) ==> k <= d
    }
}

/// Proves that a Euclidean step preserves common divisors.
pub proof fn euclidean_step(a: nat, b: nat, d: nat)
    requires
        b > 0,
        d > 0,
    ensures
        is_common_divisor(d, a, b)
            <==> is_common_divisor(d, b, a % b),
{
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(
        a as int,
        b as int,
    );

    if is_common_divisor(d, a, b) {
        assert(a % d == 0);
        assert(b % d == 0);

        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(
            a as int,
            d as int,
        );
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(
            b as int,
            d as int,
        );

        assert((a % b) % d == 0) by {
            let ai = a as int;
            let bi = b as int;
            let di = d as int;

            assert(di > 0);
            assert(bi > 0);

            assert(ai % di == 0);
            assert(bi % di == 0);

            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(ai, bi);
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(ai, di);
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(bi, di);

            let q = ai / bi;
            let ad = ai / di;
            let bd = bi / di;
            let k = ad - q * bd;

            vstd::arithmetic::mul::lemma_mul_is_commutative(bi, q);
            vstd::arithmetic::mul::lemma_mul_is_commutative(di, ad);
            vstd::arithmetic::mul::lemma_mul_is_commutative(di, bd);
            assert(ai == q * bi + ai % bi);
            assert(ai == ad * di);
            assert(bi == bd * di);

            assert((a % b) as int == k * di) by (nonlinear_arith)
                requires
                    ai == q * bi + ai % bi,
                    ai == ad * di,
                    bi == bd * di,
                    (a % b) as int == ai % bi,
                    k == ad - q * bd,
            {
            }

            vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(
                (a % b) as int,
                di,
                k,
                0,
            );

            assert(((a % b) as int) % di == 0);
        }

        assert(is_common_divisor(d, b, a % b));
    }

    if is_common_divisor(d, b, a % b) {
        assert(b % d == 0);
        assert((a % b) % d == 0);

        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(
            b as int,
            d as int,
        );

        assert(a % d == 0) by {
            let ai = a as int;
            let bi = b as int;
            let di = d as int;
            let ri = (a % b) as int;

            let q = ai / bi;
            let bd = bi / di;
            let rd = ri / di;
            let k = q * bd + rd;

            assert(di > 0);
            assert(bi > 0);
            assert(bi % di == 0);
            assert(ri % di == 0);

            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(ai, bi);
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(bi, di);
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(ri, di);

            vstd::arithmetic::mul::lemma_mul_is_commutative(bi, q);
            vstd::arithmetic::mul::lemma_mul_is_commutative(di, bd);
            vstd::arithmetic::mul::lemma_mul_is_commutative(di, rd);

            assert(ai == q * bi + ri);
            assert(bi == bd * di);
            assert(ri == rd * di);

            assert(ai == k * di) by (nonlinear_arith)
                requires
                    ai == q * bi + ri,
                    bi == bd * di,
                    ri == rd * di,
                    k == q * bd + rd,
            {
            }

            vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(
                ai,
                di,
                k,
                0,
            );

            assert(ai % di == 0);
        };

        assert(is_common_divisor(d, a, b));
    }
}


/// Returns true if g, x, and y satisfy Bézout's identity for a and b.
pub open spec fn is_extended_gcd(
    g: nat,
    x: int,
    y: int,
    a: nat,
    b: nat,
) -> bool {
    is_gcd(g, a, b)
        && x * a as int + y * b as int == g as int
}

/// Returns true if x satisfies both congruences.
pub open spec fn is_common_congruence_solution(
    x: int,
    m1: nat,
    r1: nat,
    m2: nat,
    r2: nat,
) -> bool {
    x % (m1 as int) == (r1 as int) % (m1 as int)
        && x % (m2 as int) == (r2 as int) % (m2 as int)
}

/// Returns true if the residues are compatible modulo the GCD.
pub open spec fn are_congruences_compatible(
    g: nat,
    r1: nat,
    r2: nat,
) -> bool {
    r1 % g == r2 % g
}

/// Proves that a common solution implies compatibility of the congruences.
pub proof fn crt_solution_implies_compatible(
    g: nat,
    m1: nat,
    r1: nat,
    m2: nat,
    r2: nat,
    x: int,
)
    requires
        m1 > 0,
        m2 > 0,
        is_gcd(g, m1, m2),
        is_common_congruence_solution(
            x,
            m1,
            r1,
            m2,
            r2,
        ),
    ensures
        are_congruences_compatible(
            g,
            r1,
            r2,
        ),
{
    // 1. Since g = gcd(m1, m2), g divides both moduli.
    assert(!(m1 == 0 && m2 == 0));
    assert(is_common_divisor(g, m1, m2));

    assert(g > 0);
    assert(m1 % g == 0);
    assert(m2 % g == 0);

    let gi = g as int;
    let m1i = m1 as int;
    let m2i = m2 as int;
    let r1i = r1 as int;
    let r2i = r2 as int;

    assert(gi > 0);


    // 2. From x ≡ r1 (mod m1), express x - r1 as a multiple of m1.
    assert(x % m1i == r1i % m1i);

    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(
        x,
        m1i,
    );

    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(
        r1i,
        m1i,
    );

    let xq1 = x / m1i;
    let r1q = r1i / m1i;
    let rem1 = x % m1i;

    assert(r1i % m1i == rem1);

    assert(
        x == xq1 * m1i + rem1
    );

    assert(
        r1i == r1q * m1i + rem1
    );

    let k1 = xq1 - r1q;

    assert(
        x - r1i == k1 * m1i
    ) by (nonlinear_arith)
        requires
            x == xq1 * m1i + rem1,
            r1i == r1q * m1i + rem1,
            k1 == xq1 - r1q,
    {
    }


    // 3. From x ≡ r2 (mod m2), express x - r2 as a multiple of m2.
    assert(x % m2i == r2i % m2i);

    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(
        x,
        m2i,
    );

    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(
        r2i,
        m2i,
    );

    let xq2 = x / m2i;
    let r2q = r2i / m2i;
    let rem2 = x % m2i;

    assert(r2i % m2i == rem2);

    assert(
        x == xq2 * m2i + rem2
    );

    assert(
        r2i == r2q * m2i + rem2
    );

    let k2 = xq2 - r2q;

    assert(
        x - r2i == k2 * m2i
    ) by (nonlinear_arith)
        requires
            x == xq2 * m2i + rem2,
            r2i == r2q * m2i + rem2,
            k2 == xq2 - r2q,
    {
    }


    // 4. Since g divides m1 and m2, write
    //     m1 = d1*g
    //     m2 = d2*g.
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(
        m1i,
        gi,
    );

    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(
        m2i,
        gi,
    );

    assert(m1i % gi == 0);
    assert(m2i % gi == 0);

    let d1 = m1i / gi;
    let d2 = m2i / gi;

    assert(
        m1i == d1 * gi
    );

    assert(
        m2i == d2 * gi
    );


    // 5. Subtract the two equations:
    // x - r1 = k1*m1
    // x - r2 = k2*m2
    // therefore: r2 - r1 = k1*m1 - k2*m2,
    // which is a multiple of g.
    let k = k1 * d1 - k2 * d2;

    assert(
        r2i - r1i == k * gi
    ) by (nonlinear_arith)
        requires
            x - r1i == k1 * m1i,
            x - r2i == k2 * m2i,
            m1i == d1 * gi,
            m2i == d2 * gi,
            k == k1 * d1 - k2 * d2,
    {
    }


    // 6. If r2 - r1 is a multiple of g, then r1 and r2 have the same remainder modulo g
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(
        r1i,
        gi,
    );

    let q = r1i / gi;
    let rem = r1i % gi;

    assert(
        r1i == q * gi + rem
    );

    assert(0 <= rem);
    assert(rem < gi);

    assert(
        r2i == (q + k) * gi + rem
    ) by (nonlinear_arith)
        requires
            r2i - r1i == k * gi,
            r1i == q * gi + rem,
    {
    }

    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(
        r2i,
        gi,
        q + k,
        rem,
    );

    assert(r2i % gi == rem);
    assert(r1i % gi == rem);

    assert(r1i % gi == r2i % gi);

    // Bridge int modulo back to nat modulo.
    assert(r1 % g == r2 % g);

    assert(are_congruences_compatible(
        g,
        r1,
        r2,
    ));
}

/// Incompatible residues admit no common integer solution.
pub proof fn crt_incompatible_no_solution(
    g: nat, m1: nat, r1: nat, m2: nat, r2: nat,
)
    requires m1 > 0, m2 > 0, is_gcd(g, m1, m2),
        !are_congruences_compatible(g, r1, r2),
    ensures forall|x: int| !#[trigger] is_common_congruence_solution(
        x, m1, r1, m2, r2),
{
    assert forall|x: int| !#[trigger] is_common_congruence_solution(
        x, m1, r1, m2, r2) by {
        if is_common_congruence_solution(x, m1, r1, m2, r2) {
            crt_solution_implies_compatible(g, m1, r1, m2, r2, x);
        }
    }
}

/// A positive exact divisor has a positive quotient.
pub proof fn positive_exact_quotient(a: nat, d: nat)
    requires a > 0, d > 0, a % d == 0,
    ensures a / d > 0,
{
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(a as int, d as int);
    assert(a / d > 0) by (nonlinear_arith)
        requires a > 0, d > 0, a == d * (a / d);
}

/// Adding a multiple of a modulus preserves its remainder.
pub proof fn congruence_shift(x: int, y: int, m: int, q: int)
    requires m > 0, x == y + m * q,
    ensures x % m == y % m,
{
    vstd::arithmetic::div_mod::lemma_mod_multiples_vanish(q, y, m);
}

/// Convert Rust's signed remainder to a canonical mathematical residue.
pub proof fn signed_remainder_normalized(s: int, n: int, rem: int)
    requires n > 0, rem == vstd::arithmetic::div_mod::rust_rem(s, n),
    ensures (if rem < 0 { rem + n } else { rem }) == s % n,
{
    if s < 0 {
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(-s, n);
        let q = -((-s) / n);
        assert(s == n * q + rem) by (nonlinear_arith)
            requires -s == n * ((-s) / n) + (-s) % n,
                q == -((-s) / n), rem == -((-s) % n);
        let r = if rem < 0 { rem + n } else { rem };
        let quotient = if rem < 0 { q - 1 } else { q };
        assert(s == n * quotient + r) by (nonlinear_arith)
            requires s == n * q + rem,
                r == if rem < 0 { rem + n } else { rem },
                quotient == if rem < 0 { q - 1 } else { q };
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(s, n, quotient, r);
    }
}

/// The reduced CRT multiplier constructs a common solution.
pub proof fn crt_candidate_solution(
    m1: int, a1: int, m2: int, a2: int,
    g: int, s: int, t: int, k: int,
)
    requires
        m1 > 0, m2 > 0, g > 0,
        m1 % g == 0, m2 % g == 0,
        s * m1 + t * m2 == g,
        a1 % g == a2 % g,
        k % (m2 / g) == ((a2 / g - a1 / g) * s) % (m2 / g),
    ensures
        (a1 + m1 * k) % m1 == a1 % m1,
        (a1 + m1 * k) % m2 == a2 % m2,
{
    use vstd::arithmetic::div_mod::lemma_fundamental_div_mod;
    let n = m2 / g;
    let delta = a2 / g - a1 / g;
    lemma_fundamental_div_mod(m2, g);
    positive_exact_quotient(m2 as nat, g as nat);
    lemma_fundamental_div_mod(a1, g);
    lemma_fundamental_div_mod(a2, g);
    assert(a2 - a1 == g * delta) by (nonlinear_arith)
        requires a1 == g * (a1 / g) + a1 % g,
            a2 == g * (a2 / g) + a2 % g, a1 % g == a2 % g,
            delta == a2 / g - a1 / g;
    lemma_fundamental_div_mod(k, n);
    lemma_fundamental_div_mod(delta * s, n);
    let h = k / n - (delta * s) / n;
    assert(k == delta * s + n * h) by (nonlinear_arith)
        requires k == n * (k / n) + k % n,
            delta * s == n * ((delta * s) / n) + (delta * s) % n,
            k % n == (delta * s) % n,
            h == k / n - (delta * s) / n;
    lemma_fundamental_div_mod(m1, g);
    let p = m1 / g;
    assert(m1 * n == m2 * p) by (nonlinear_arith)
        requires m1 == g * p, m2 == g * n;
    assert(m1 * (delta * s + n * h)
        == (s * m1) * delta + (m1 * n) * h) by (nonlinear_arith);
    assert((g - t * m2) * delta + (m2 * p) * h
        == g * delta + m2 * (p * h - t * delta)) by (nonlinear_arith);
    assert(a1 + m1 * k == a2 + m2 * (p * h - t * delta));
    congruence_shift(a1 + m1 * k, a1, m1, k);
    congruence_shift(a1 + m1 * k, a2, m2, p * h - t * delta);
}

/// Reduction by a common multiple preserves each input constraint.
pub proof fn crt_normalize_solution(x: int, m1: nat, m2: nat, d: nat)
    requires m1 > 0, m2 > 0, is_gcd(d, m1, m2),
    ensures
        (x % (((m1 / d) * m2) as int)) % (m1 as int) == x % (m1 as int),
        (x % (((m1 / d) * m2) as int)) % (m2 as int) == x % (m2 as int),
{
    use vstd::arithmetic::div_mod::lemma_fundamental_div_mod;
    let a = m1 as int;
    let b = m2 as int;
    let g = d as int;
    let p = a / g;
    let n = b / g;
    lemma_fundamental_div_mod(a, g);
    lemma_fundamental_div_mod(b, g);
    positive_exact_quotient(m1, d);
    let l = p * b;
    assert(l > 0) by (nonlinear_arith) requires p > 0, b > 0, l == p * b;
    assert(l == a * n) by (nonlinear_arith)
        requires a == g * p, b == g * n, l == p * b;
    lemma_fundamental_div_mod(x, l);
    let q = x / l;
    let r = x % l;
    assert(x == r + a * (n * q)) by (nonlinear_arith)
        requires x == l * q + r, l == a * n;
    assert(x == r + b * (p * q)) by (nonlinear_arith)
        requires x == l * q + r, l == p * b;
    congruence_shift(x, r, a, n * q);
    congruence_shift(x, r, b, p * q);
}

/// The GCD is unique, including gcd(0, 0).
pub proof fn gcd_unique(g: nat, d: nat, a: nat, b: nat)
    requires is_gcd(g, a, b), is_gcd(d, a, b),
    ensures g == d,
{
    if a != 0 || b != 0 {
        assert(is_common_divisor(g, a, b));
        assert(is_common_divisor(d, a, b));
        assert(g <= d);
        assert(d <= g);
    }
}

/// Regroup four factors using associativity and commutativity.
pub proof fn mul_regroup(a: int, b: int, c: int, d: int)
    ensures (a * b) * (c * d) == (b * c) * (a * d),
{
    use vstd::arithmetic::mul::{lemma_mul_is_associative, lemma_mul_is_commutative};
    lemma_mul_is_associative(a * b, c, d);
    lemma_mul_is_associative(a, b, c);
    lemma_mul_is_commutative(a, b * c);
    lemma_mul_is_associative(b * c, a, d);
}

/// Bezout's identity makes every common multiple a multiple of the LCM.
pub proof fn common_multiple_is_lcm_multiple(
    z: int, a: int, b: int, g: int, s: int, t: int,
)
    requires a > 0, b > 0, g > 0,
        a % g == 0, b % g == 0,
        s * a + t * b == g,
        z % a == 0, z % b == 0,
    ensures z % ((a / g) * b) == 0,
{
    use vstd::arithmetic::div_mod::lemma_fundamental_div_mod;
    lemma_fundamental_div_mod(a, g);
    lemma_fundamental_div_mod(z, a);
    lemma_fundamental_div_mod(z, b);
    positive_exact_quotient(a as nat, g as nat);
    let p = a / g;
    let l = p * b;
    let u = z / a;
    let v = z / b;
    let w = s * v + t * u;
    assert(l > 0) by (nonlinear_arith) requires p > 0, b > 0, l == p * b;
    assert(g * l == a * b) by (nonlinear_arith)
        requires a == g * p, l == p * b;
    assert((s * a + t * b) * z == s * a * z + t * b * z)
        by (nonlinear_arith);
    mul_regroup(s, a, b, v);
    mul_regroup(t, b, a, u);
    vstd::arithmetic::mul::lemma_mul_is_commutative(a, b);
    vstd::arithmetic::mul::lemma_mul_is_distributive_add(a * b, s * v, t * u);
    assert(s * a * (b * v) + t * b * (a * u)
        == (a * b) * (s * v + t * u));
    assert(g * z == (g * l) * w);
    assert(z == l * w) by (nonlinear_arith)
        requires g > 0, g * z == (g * l) * w;
    congruence_shift(z, 0, l, w);
}

/// A canonical common solution generates exactly the intersection.
pub proof fn crt_solution_class_exact(
    x: int, residue: nat, m1: nat, r1: nat, m2: nat, r2: nat,
    g: nat, s: int, t: int,
)
    requires m1 > 0, m2 > 0,
        is_extended_gcd(g, s, t, m1, m2),
        residue < (m1 / g) * m2,
        is_common_congruence_solution(residue as int, m1, r1, m2, r2),
    ensures
        (x % (((m1 / g) * m2) as int) == residue as int)
            <==> is_common_congruence_solution(x, m1, r1, m2, r2),
{
    let l = ((m1 / g) * m2) as int;
    let r = residue as int;
    crt_normalize_solution(x, m1, m2, g);
    if is_common_congruence_solution(x, m1, r1, m2, r2) {
        vstd::arithmetic::div_mod::lemma_mod_equivalence(x, r, m1 as int);
        vstd::arithmetic::div_mod::lemma_mod_equivalence(x, r, m2 as int);
        common_multiple_is_lcm_multiple(x - r, m1 as int, m2 as int,
            g as int, s, t);
        vstd::arithmetic::div_mod::lemma_mod_equivalence(x, r, l);
        vstd::arithmetic::div_mod::lemma_small_mod(residue, l as nat);
    }
}

/// Normalizing modulo m preserves residues modulo every divisor of m.
pub proof fn normalize_preserves_divisor(r: nat, m: nat, d: nat)
    requires m > 0, d > 0, m % d == 0,
    ensures (r % m) % d == r % d,
{
    use vstd::arithmetic::div_mod::lemma_fundamental_div_mod;
    lemma_fundamental_div_mod(r as int, m as int);
    lemma_fundamental_div_mod(m as int, d as int);
    let q = (r / m) as int;
    let k = (m / d) as int;
    assert(r as int == (r % m) as int + (d as int) * (k * q))
        by (nonlinear_arith)
        requires r as int == (m as int) * q + (r % m) as int,
            m as int == (d as int) * k;
    congruence_shift(r as int, (r % m) as int, d as int, k * q);
}

/// Computes the GCD and Bézout coefficients.
fn extended_gcd_u64(a: u64, b: u64) -> (result: ExtendedGcd<u64>)
    ensures
        is_extended_gcd(
            result.gcd as nat,
            result.x as int,
            result.y as int,
            a as nat,
            b as nat,
        ),
        b == 0 ==> result.x == 1 && result.y == 0,
        b != 0 ==> -(b as int) <= result.x as int <= b as int,
        a != 0 ==> -(a as int) <= result.y as int <= a as int,
    decreases b,
{
    if b == 0 {
        proof {
            if a == 0 {
                // Special case: gcd(0, 0) = 0.
                assert(is_gcd(0, 0, 0));
            } else {
                let an = a as nat;

                // a is a positive common divisor of (a, 0).
                assert(an > 0);
                assert(an % an == 0);
                assert(0nat % an == 0);
                assert(is_common_divisor(an, an, 0));

                // Every positive divisor of a is at most a.
                assert forall|k: nat|
                    #[trigger] is_common_divisor(k, an, 0) implies k <= an
                by {
                    assert(k > 0);
                    assert(an % k == 0);

                    assert(k <= an) by (nonlinear_arith)
                        requires
                            an > 0,
                            k > 0,
                            an % k == 0,
                    {
                    }
                }

                assert(is_gcd(an, an, 0));
            }

            assert(is_gcd(a as nat, a as nat, 0));

            // Bézout identity: 1*a + 0*0 = a.
            assert(is_extended_gcd(
                a as nat,
                1,
                0,
                a as nat,
                0,
            ));
        }

        ExtendedGcd { gcd: a, x: 1i128, y: 0i128 }
    } else {
        let r = a % b;
        let ExtendedGcd { gcd: g, x: x1, y: y1 } = extended_gcd_u64(b, r);

        proof {
            // The Euclidean step preserves positive common divisors.
            assert forall|d: nat| d > 0 implies
                (#[trigger] is_common_divisor(d, a as nat, b as nat)
                    <==> is_common_divisor(d, b as nat, r as nat))
            by {
                euclidean_step(a as nat, b as nat, d);
            }

            assert(is_gcd(g as nat, b as nat, r as nat));
            assert(is_gcd(g as nat, a as nat, b as nat));
        }

        if r == 0 {
            // The recursive call is extended_gcd(b, 0).
            // Its coefficients are (1, 0), so g = b.
            proof {
                assert(x1 == 1);
                assert(y1 == 0);

                assert(
                    (x1 as int) * (b as int)
                        + (y1 as int) * 0
                        == g as int
                );

                assert(g == b) by (nonlinear_arith)
                    requires
                        (x1 as int) * (b as int)
                            + (y1 as int) * 0
                            == g as int,
                        x1 == 1,
                {
                }
            }

            proof {
                assert(is_gcd(g as nat, a as nat, b as nat));
                assert(g == b);

                assert(is_extended_gcd(
                    g as nat,
                    0,
                    1,
                    a as nat,
                    b as nat,
                ));
            }
            ExtendedGcd { gcd: g, x: 0i128, y: 1i128 }
        } else {
            let q = (a / b) as i128;
            let x = y1;

            proof {
                let ai = a as int;
                let bi = b as int;
                let ri = r as int;
                let qi = q as int;
                let x1i = x1 as int;
                let y1i = y1 as int;

                vstd::arithmetic::div_mod::lemma_fundamental_div_mod(
                    ai,
                    bi,
                );

                assert(qi == ai / bi);
                assert(ri == ai % bi);
                assert(ai == qi * bi + ri) by (nonlinear_arith)
                    requires ai == bi * qi + ri;

                // Bounds from extended_gcd(b, r):
                // |x1| <= r and |y1| <= b.
                assert(-ri <= x1i <= ri);
                assert(-bi <= y1i <= bi);

                assert(0 <= qi);
                assert(0 <= ri);

                // Bound q*y1 before executing the i128 multiplication.
                assert(-ai <= qi * y1i <= ai)
                    by (nonlinear_arith)
                    requires
                        ai == qi * bi + ri,
                        0 <= qi,
                        0 <= ri,
                        0 <= bi,
                        -bi <= y1i,
                        y1i <= bi,
                {
                }
            }

            let product = q * y1;

            proof {
                let ai = a as int;
                let bi = b as int;
                let ri = r as int;
                let qi = q as int;
                let x1i = x1 as int;
                let y1i = y1 as int;

                vstd::arithmetic::div_mod::lemma_fundamental_div_mod(
                    ai,
                    bi,
                );

                assert(qi == ai / bi);
                assert(ri == ai % bi);
                assert(ai == qi * bi + ri);

                assert(0 <= qi);
                assert(0 <= ri);

                // Use the recursive bounds, not merely |product| <= a.
                assert(-ri <= x1i <= ri);
                assert(-bi <= y1i <= bi);

                assert(-qi * bi <= qi * y1i <= qi * bi)
                    by (nonlinear_arith)
                    requires
                        0 <= qi,
                        0 <= bi,
                        -bi <= y1i,
                        y1i <= bi,
                {
                }

                assert(product as int == qi * y1i);

                // |x1 - q*y1| <= r + q*b = a.
                assert(-ai <= x1i - (product as int) <= ai)
                    by (nonlinear_arith)
                    requires
                        ai == qi * bi + ri,
                        0 <= qi,
                        0 <= ri,
                        -ri <= x1i,
                        x1i <= ri,
                        -qi * bi <= product as int,
                        product as int <= qi * bi,
                {
                }
            }

            let y = x1 - product;

            proof {
                let ai = a as int;
                let bi = b as int;
                let ri = r as int;
                let qi = q as int;

                vstd::arithmetic::div_mod::lemma_fundamental_div_mod(
                    ai,
                    bi,
                );

                assert(qi == ai / bi);
                assert(ri == ai % bi);
                assert(ai == qi * bi + ri);

                // Recursive Bézout identity:
                // x1*b + y1*r = g.
                assert(
                    (x1 as int) * bi
                        + (y1 as int) * ri
                        == g as int
                );

                // Substitute r = a - q*b:
                // y1*a + (x1 - q*y1)*b = g.
                assert(
                    (x as int) * ai
                        + (y as int) * bi
                        == g as int
                ) by (nonlinear_arith)
                    requires
                        ai == qi * bi + ri,
                        (x1 as int) * bi
                            + (y1 as int) * ri
                            == g as int,
                        x as int == y1 as int,
                        y as int
                            == x1 as int - qi * (y1 as int),
                {
                }
            }
            proof {
                assert(is_gcd(g as nat, a as nat, b as nat));

                assert(
                    (x as int) * (a as int)
                        + (y as int) * (b as int)
                        == g as int
                );

                assert(is_extended_gcd(
                    g as nat,
                    x as int,
                    y as int,
                    a as nat,
                    b as nat,
                ));
            }
            ExtendedGcd { gcd: g, x, y }
        }
    }
}


/// Width-independent widened CRT engine for the supported u8..u64 inputs.
fn crt_wide(m1: u64, r1: u64, m2: u64, r2: u64) -> (result: Option<(u128, u128)>)
    requires m1 > 0, m2 > 0,
    ensures match result {
        None => forall|x: int| !#[trigger] is_common_congruence_solution(x, m1 as nat, r1 as nat, m2 as nat, r2 as nat),
        Some((m, r)) => m > 0 && r < m
            && m == (m1 as nat / gcd_spec(m1 as nat, m2 as nat)) * m2 as nat
            && forall|x: int| #[trigger] is_common_congruence_solution(x, m1 as nat, r1 as nat, m2 as nat, r2 as nat)
                <==> x % (m as int) == r as int,
    },
{
    let a1 = r1 % m1;
    let a2 = r2 % m2;

    let ExtendedGcd { gcd: g, x: s, y: _t } = extended_gcd_u64(m1, m2);

    proof {
        assert(is_extended_gcd(
            g as nat,
            s as int,
            _t as int,
            m1 as nat,
            m2 as nat,
        ));

        assert(is_gcd(
            g as nat,
            m1 as nat,
            m2 as nat,
        ));

        assert(!(m1 == 0 && m2 == 0));

        assert(is_common_divisor(
            g as nat,
            m1 as nat,
            m2 as nat,
        ));

        assert(g > 0);
        assert((m1 as nat) % (g as nat) == 0);
        assert((m2 as nat) % (g as nat) == 0);
    }

    if a1 % g != a2 % g {
        proof {
            crt_incompatible_no_solution(g as nat,
                m1 as nat, a1 as nat, m2 as nat, a2 as nat);
            vstd::arithmetic::div_mod::lemma_small_mod(a1 as nat, m1 as nat);
            vstd::arithmetic::div_mod::lemma_small_mod(a2 as nat, m2 as nat);
            assert forall|x: int| !#[trigger] is_common_congruence_solution(
                x, m1 as nat, r1 as nat, m2 as nat, r2 as nat,
            ) by {
                assert(!is_common_congruence_solution(
                    x, m1 as nat, a1 as nat, m2 as nat, a2 as nat));
            }
        }
        return None;
    }

    // The exact LCM of two at-most-u64 moduli fits in u128.
    let reduced = (m1 / g) as u128;
    let m2_wide = m2 as u128;
    proof {
        positive_exact_quotient(m1 as nat, g as nat);
        assert(reduced * m2_wide <= u128::MAX) by (nonlinear_arith)
            requires reduced <= u64::MAX, m2_wide <= u64::MAX;
        assert(reduced * m2_wide > 0) by (nonlinear_arith)
            requires reduced > 0, m2_wide > 0;
    }
    let lcm = reduced * m2_wide;

    // Bézout gives the inverse s of m1/g modulo n = m2/g.

    let n = m2 / g;

    proof {
        positive_exact_quotient(m2 as nat, g as nat);
        assert(n > 0);
    }

    // Compatibility gives (a2 - a1)/g = q2 - q1.
    let q1 = a1 / g;
    let q2 = a2 / g;
    proof {
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(a2 as int, g as int);
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(m2 as int, g as int);
        assert(q2 < n) by (nonlinear_arith)
            requires a2 < m2, g > 0,
                a2 as int == (g as int) * (q2 as int) + (a2 as int) % (g as int),
                m2 as int == (g as int) * (n as int),
                (a2 as int) % (g as int) >= 0;
    }

    // Compute (q2 - q1) mod n without the potentially overflowing q2 + n.
    let q1_mod_n = q1 % n;

    let delta_mod =
        if q2 >= q1_mod_n {
            q2 - q1_mod_n
        } else {
            n - (q1_mod_n - q2)
        };

    proof {
        assert(delta_mod < n);
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(q1 as int, n as int);
        let shift = if q2 >= q1_mod_n { q1 as int / n as int }
            else { q1 as int / n as int + 1 };
        assert(delta_mod as int == (q2 as int - q1 as int) + (n as int) * shift)
            by (nonlinear_arith)
            requires q1 as int == (n as int) * (q1 as int / n as int) + q1_mod_n as int,
                delta_mod as int == if q2 >= q1_mod_n { q2 as int - q1_mod_n as int }
                    else { n as int - (q1_mod_n as int - q2 as int) },
                shift == if q2 >= q1_mod_n { q1 as int / n as int }
                    else { q1 as int / n as int + 1 };
        congruence_shift(delta_mod as int, q2 as int - q1 as int, n as int, shift);
    }

    // Normalize s before multiplication to avoid large signed intermediates.

    let ni = n as i128;

    proof {
        assert(ni > 0);
    }

    let s_rem = s % ni;

    let s_mod_i =
        if s_rem < 0 {
            s_rem + ni
        } else {
            s_rem
        };

    proof {
        assert(0 <= s_mod_i);
        assert(s_mod_i < ni);
    }

    let s_mod = s_mod_i as u64;

    proof {
        assert((s_mod as nat) < (n as nat));
        signed_remainder_normalized(s as int, n as int, s_rem as int);
        assert(s_mod as int == (s as int) % (n as int));
    }

    // Compute k = delta*s mod n in u128; each factor fits in u64.

    let delta_wide = delta_mod as u128;
    let s_wide = s_mod as u128;
    let n_wide = n as u128;

    proof {
        assert(delta_wide * s_wide <= u128::MAX) by (nonlinear_arith)
            requires delta_wide <= u64::MAX, s_wide <= u64::MAX;
    }
    let product = delta_wide * s_wide;
    let k_wide = product % n_wide;

    proof {
        assert(k_wide < n_wide);
    }

    let k = k_wide as u64;

    proof {
        assert(k < n);
        vstd::arithmetic::div_mod::lemma_small_mod(s_mod as nat, n as nat);
        vstd::arithmetic::div_mod::lemma_small_mod(k as nat, n as nat);
        vstd::arithmetic::div_mod::lemma_mul_mod_noop_general(
            delta_mod as int, s_mod as int, n as int);
        vstd::arithmetic::div_mod::lemma_mul_mod_noop_general(
            q2 as int - q1 as int, s as int, n as int);
        assert((delta_mod as int) % (n as int) == (q2 as int - q1 as int) % (n as int));
        assert((s_mod as int) % (n as int) == (s as int) % (n as int));
        assert(k as int == ((delta_mod as int) * (s_mod as int)) % (n as int));
        assert((k as int) % (n as int) == ((q2 as int - q1 as int) * (s as int)) % (n as int));
        crt_candidate_solution(m1 as int, a1 as int, m2 as int, a2 as int,
            g as int, s as int, _t as int, k as int);
    }

    // Construct a1 + m1*k in u128 before reducing modulo the LCM.

    let a1_wide = a1 as u128;
    let m1_wide = m1 as u128;
    let lcm_wide = lcm as u128;
    let k_wide_2 = k as u128;

    proof {
        assert(m1_wide * k_wide_2 + a1_wide <= u128::MAX) by (nonlinear_arith)
            requires m1_wide <= u64::MAX, k_wide_2 <= u64::MAX,
                a1_wide <= u64::MAX;
    }
    let term = m1_wide * k_wide_2;
    let candidate = a1_wide + term;

    let residue_wide = candidate % lcm_wide;

    proof {
        assert(residue_wide < lcm_wide);
    }

    let residue = residue_wide;

    proof {
        assert(residue < lcm);

        let d = g as nat;
        crt_normalize_solution(candidate as int, m1 as nat, m2 as nat, d);
        vstd::arithmetic::div_mod::lemma_small_mod(a1 as nat, m1 as nat);
        vstd::arithmetic::div_mod::lemma_small_mod(a2 as nat, m2 as nat);
        assert(is_common_congruence_solution(
            residue as int, m1 as nat, r1 as nat, m2 as nat, r2 as nat));

        gcd_unique(g as nat, d, m1 as nat, m2 as nat);
        assert forall|x: int|
            #[trigger] is_common_congruence_solution(
                x, m1 as nat, r1 as nat, m2 as nat, r2 as nat,
            ) <==> x % (lcm as int) == residue as int by {
            crt_solution_class_exact(x, residue as nat,
                m1 as nat, r1 as nat, m2 as nat, r2 as nat,
                g as nat, s as int, _t as int);
        }

    }
    proof {
        lemma_gcd_spec(m1 as nat, m2 as nat);
        gcd_unique(g as nat, gcd_spec(m1 as nat, m2 as nat), m1 as nat, m2 as nat);
    }
    Some((lcm, residue))
}

/// Connect the recursive specification to the traditional greatest divisor.
pub proof fn lemma_gcd_spec(a: nat, b: nat)
    ensures is_gcd(gcd_spec(a, b), a, b),
    decreases b,
{
    if b == 0 {
        if a > 0 {
            lemma_mod_self_0(a as int);
            assert forall|k: nat| #[trigger] is_common_divisor(k, a, 0) implies k <= a by {
                assert(k <= a) by (nonlinear_arith) requires a > 0, k > 0, a % k == 0;
            }
        }
    } else {
        lemma_mod_bound(a as int, b as int);
        lemma_gcd_spec(b, a % b);
        let g = gcd_spec(b, a % b);
        euclidean_step(a, b, g);
        assert forall|k: nat| #[trigger] is_common_divisor(k, a, b) implies k <= g by {
            euclidean_step(a, b, k);
        }
    }
}

/// Divisibility maximality, stronger than numerical maximality.
pub proof fn lemma_gcd_divisor(a: nat, b: nat, d: nat)
    requires d > 0, is_common_divisor(d, a, b),
    ensures gcd_spec(a, b) % d == 0,
    decreases b,
{
    if b > 0 {
        euclidean_step(a, b, d);
        lemma_mod_bound(a as int, b as int);
        lemma_gcd_divisor(b, a % b, d);
    }
}

pub proof fn lemma_gcd_symmetric(a: nat, b: nat)
    ensures gcd_spec(a, b) == gcd_spec(b, a),
{
    lemma_gcd_spec(a, b);
    lemma_gcd_spec(b, a);
    if a != 0 || b != 0 {
        assert forall|k: nat| #[trigger] is_common_divisor(k, a, b) implies k <= gcd_spec(b, a) by {
            assert(is_common_divisor(k, b, a));
        }
    }
    gcd_unique(gcd_spec(a, b), gcd_spec(b, a), a, b);
}

/// Divisibility is transitive, including a zero dividend.
pub proof fn lemma_divides_transitive(a: nat, b: nat, d: nat)
    requires b > 0, d > 0, a % b == 0, b % d == 0,
    ensures a % d == 0,
{
    lemma_fundamental_div_mod(a as int, b as int);
    lemma_fundamental_div_mod(b as int, d as int);
    let q = (a / b) * (b / d);
    assert(a == d * q) by (nonlinear_arith)
        requires a == b * (a / b), b == d * (b / d), q == (a / b) * (b / d);
    lemma_fundamental_div_mod_converse(a as int, d as int, q as int, 0);
}

pub proof fn lemma_gcd_divisor_iff(a: nat, b: nat, d: nat)
    requires d > 0,
    ensures (gcd_spec(a, b) % d == 0) <==> is_common_divisor(d, a, b),
{
    lemma_gcd_spec(a, b);
    if is_common_divisor(d, a, b) { lemma_gcd_divisor(a, b, d); }
    let g = gcd_spec(a, b);
    if g > 0 && g % d == 0 {
        lemma_divides_transitive(a, g, d);
        lemma_divides_transitive(b, g, d);
    }
}

pub proof fn lemma_gcd_associative(a: nat, b: nat, c: nat)
    ensures gcd_spec(gcd_spec(a, b), c) == gcd_spec(a, gcd_spec(b, c)),
{
    let ab = gcd_spec(a, b);
    let bc = gcd_spec(b, c);
    let left = gcd_spec(ab, c);
    let right = gcd_spec(a, bc);
    lemma_gcd_spec(a, b);
    lemma_gcd_spec(b, c);
    lemma_gcd_spec(ab, c);
    lemma_gcd_spec(a, bc);
    if left > 0 {
        lemma_gcd_divisor_iff(a, b, left);
        lemma_gcd_divisor_iff(b, c, left);
        assert(is_common_divisor(left, a, bc));
    }
    if right > 0 {
        lemma_gcd_divisor_iff(b, c, right);
        lemma_gcd_divisor_iff(a, b, right);
        assert(is_common_divisor(right, ab, c));
    }
}

/// Generic machine-word Euclidean algorithm.
pub fn gcd<W: Word>(a: W, b: W) -> (r: W)
    ensures r.view() == gcd_spec(a.view(), b.view()),
        is_gcd(r.view(), a.view(), b.view()),
    decreases b.view(),
{
    proof { lemma_gcd_spec(a.view(), b.view()); }
    if b.eq(W::zero()) { a }
    else {
        let rem = a.urem(b);
        proof { lemma_mod_bound(a.view() as int, b.view() as int); }
        gcd(b, rem)
    }
}

/// Named Bézout result; coefficients fit i128 for all supported words.
pub struct ExtendedGcd<W> {
    pub gcd: W,
    pub x: i128,
    pub y: i128,
}

pub fn extended_gcd<W: Word>(a: W, b: W) -> (r: ExtendedGcd<W>)
    ensures r.gcd.view() == gcd_spec(a.view(), b.view()),
        is_extended_gcd(r.gcd.view(), r.x as int, r.y as int, a.view(), b.view()),
        b.view() == 0 ==> r.x == 1 && r.y == 0,
        b.view() != 0 ==> -(b.view() as int) <= r.x as int <= b.view(),
        a.view() != 0 ==> -(a.view() as int) <= r.y as int <= a.view(),
{
    let coefficients = extended_gcd_u64(a.to_u64(), b.to_u64());
    let g = coefficients.gcd;
    let x = coefficients.x;
    let y = coefficients.y;
    proof {
        a.lemma_view_bounded();
        b.lemma_view_bounded();
        lemma_gcd_spec(a.view(), b.view());
        gcd_unique(g as nat, gcd_spec(a.view(), b.view()), a.view(), b.view());
        if a.view() > 0 {
            assert(g <= a.view()) by (nonlinear_arith)
                requires g > 0, a.view() > 0, a.view() % (g as nat) == 0;
        } else if b.view() > 0 {
            assert(g <= b.view()) by (nonlinear_arith)
                requires g > 0, b.view() > 0, b.view() % (g as nat) == 0;
        }
    }
    ExtendedGcd { gcd: W::from_u64(g), x, y }
}

/// Finite-word intersection of two positive-modulus classes.
pub enum CrtMergeResult<W> {
    Class { modulus: W, residue: W },
    Singleton { value: W },
    Empty,
}

impl<W: Word> CrtMergeResult<W> {
    pub open spec fn wf(&self) -> bool {
        match self {
            Self::Class { modulus, residue } => modulus.view() > 0
                && residue.view() < modulus.view()
                && residue.view() + modulus.view() < W::modulus(),
            _ => true,
        }
    }

    pub open spec fn has(&self, x: W) -> bool {
        match self {
            Self::Class { modulus, residue } => x.view() % modulus.view() == residue.view(),
            Self::Singleton { value } => x == *value,
            Self::Empty => false,
        }
    }
}

/// The least nonnegative member and the next possible member of a class.
proof fn lemma_class_member(x: nat, m: nat, r: nat)
    requires m > 0, r < m,
    ensures x % m == r ==> r <= x && (x == r || r + m <= x),
{
    if x % m == r {
        lemma_mod_decreases(x, m);
        lemma_fundamental_div_mod(x as int, m as int);
        assert(x == r || r + m <= x) by (nonlinear_arith)
            requires m > 0, x == m * (x / m) + r;
    }
}

/// Exact CRT over representable words. Moduli MUST be positive.
/// Congruence's modulus-zero constants must be handled by callers first.
pub fn crt_merge<W: Word>(m1: W, r1: W, m2: W, r2: W) -> (result: CrtMergeResult<W>)
    requires m1.view() > 0, m2.view() > 0,
    ensures result.wf(),
        forall|x: W| #[trigger] result.has(x) <==>
            is_common_congruence_solution(x.view() as int, m1.view(), r1.view(), m2.view(), r2.view()),
{
    let wide = crt_wide(m1.to_u64(), r1.to_u64(), m2.to_u64(), r2.to_u64());
    let max = W::max().to_u64();
    match wide {
        None => CrtMergeResult::Empty,
        Some((m, r)) => {
            let result;
            if r > max as u128 {
                result = CrtMergeResult::Empty;
            } else if m > (max as u128) - r {
                let value = W::from_u64(r as u64);
                result = CrtMergeResult::Singleton { value };
            } else {
                result = CrtMergeResult::Class {
                    modulus: W::from_u64(m as u64),
                    residue: W::from_u64(r as u64),
                };
            }
            proof {
                assert forall|x: W| #[trigger] result.has(x) <==>
                    is_common_congruence_solution(x.view() as int, m1.view(), r1.view(), m2.view(), r2.view()) by {
                    x.lemma_view_bounded();
                    lemma_class_member(x.view(), m as nat, r as nat);
                    match result {
                        CrtMergeResult::Singleton { value } => {
                            W::lemma_view_injective(x, value);
                            lemma_small_mod(r as nat, m as nat);
                        },
                        _ => {},
                    }
                }
            }
            result
        },
    }
}

/// GCD for widened products and for the machine modulus (which may be 2^64).
pub fn gcd_wide(a: u128, b: u128) -> (r: u128)
    ensures r as nat == gcd_spec(a as nat, b as nat),
        is_gcd(r as nat, a as nat, b as nat),
    decreases b,
{
    proof { lemma_gcd_spec(a as nat, b as nat); }
    if b == 0 { a } else { gcd_wide(b, a % b) }
}

/// The step that is preserved by reduction modulo the machine modulus.
/// The result is wide because gcd(0, 2^64) = 2^64.
pub fn gcd_machine_modulus<W: Word>(m: W) -> (r: u128)
    ensures r as nat == gcd_spec(m.view(), W::modulus()), r > 0,
        m.view() % (r as nat) == 0, W::modulus() % (r as nat) == 0,
{
    let max = W::max().to_u64();
    let modulus = max as u128 + 1;
    gcd_wide(m.to_u64() as u128, modulus)
}

/// Wrapping preserves congruence modulo gcd(m, 2^N), for negative integers too.
/// This is a shared mathematical fact, not a Congruence transfer operation.
pub proof fn lemma_wrapping_congruence<W: Word>(m: nat, x: int)
    ensures gcd_spec(m, W::modulus()) > 0,
        (x % (W::modulus() as int)) % (gcd_spec(m, W::modulus()) as int)
            == x % (gcd_spec(m, W::modulus()) as int),
{
    W::lemma_modulus();
    let n = W::modulus() as int;
    let g = gcd_spec(m, W::modulus()) as int;
    lemma_gcd_spec(m, W::modulus());
    lemma_fundamental_div_mod(x, n);
    lemma_fundamental_div_mod(n, g);
    let q = x / n;
    let k = n / g;
    assert(x == x % n + g * (k * q)) by (nonlinear_arith)
        requires x == n * q + x % n, n == g * k;
    congruence_shift(x, x % n, g, k * q);
}

/// Exact native-word product, widened before multiplication.
pub fn mul_wide<W: Word>(a: W, b: W) -> (r: u128)
    ensures r as nat == a.view() * b.view(),
{
    let aw = a.to_u64() as u128;
    let bw = b.to_u64() as u128;
    proof {
        assert(aw * bw <= u128::MAX) by (nonlinear_arith)
            requires aw <= u64::MAX, bw <= u64::MAX;
    }
    aw * bw
}

/// Shared widened Granger modulus foundation. This computes only the modulus;
/// it does not implement multiplication or wrapping of any abstract domain.
pub fn granger_modulus<W: Word>(m1: W, r1: W, m2: W, r2: W) -> (r: u128)
    ensures r as nat == gcd_spec(gcd_spec(m1.view() * m2.view(), m1.view() * r2.view()), m2.view() * r1.view()),
{
    let mm = mul_wide(m1, m2);
    let mr = mul_wide(m1, r2);
    let rm = mul_wide(m2, r1);
    gcd_wide(gcd_wide(mm, mr), rm)
}

} // verus!

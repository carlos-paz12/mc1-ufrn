#include <iostream>
#include <stdexcept>
#include <cmath>

const int MAX_FACTORS = 32;

/*
 * Pre-declaring functions to avoid bugs
 */
int inverse_mod(int a, int b, int m);
int linear_congruence(int a, int b, int m);

/**
 * @brief Computes the power of a base raised to an exponent.
 *
 * This function takes two integer parameters, `base` and `expoent`, and returns 
 * the result of raising `base` to the power of `expoent`. It uses a simple 
 * iterative approach to compute the power.
 *
 * @param base The base value to be raised.
 * @param expoent The exponent value to raise the base to.
 * @return The result of `base` raised to the power of `expoent`.
 *
 * @example
 * int result = pow(2, 3);
 * // result is 8
 */
int pow(int base, int expoent)
{
    int n = 1;
    for (int i = 0; i < expoent; i++)
    {
        n = n * base;
    }
    return n;
}

/**
 * @brief Computes the floor of a given double value.
 *
 * This function takes a double parameter `x` and returns the largest integer 
 * value less than or equal to `x`.
 *
 * @param x The double value to be floored.
 * @return The largest integer value less than or equal to `x`.
 *
 * @example
 * int result = to_floor(3.7);
 * // result is 3
 *
 * @example
 * int result = to_floor(-2.3);
 * // result is -3
 */
int to_floor(double x)
{
    int x_ = (int)x;
    return (x != x_ && x < 0 ? x_ - 1 : x_);
}

/**
 * @brief Computes the ceiling of a given double value.
 *
 * This function takes a double parameter `x` and returns the smallest integer 
 * value greater than or equal to `x`.
 *
 * @param x The double value to be ceilinged.
 * @return The smallest integer value greater than or equal to `x`.
 *
 * @example
 * int result = to_ceil(3.7);
 * // result is 4
 *
 * @example
 * int result = to_ceil(-2.3);
 * // result is -2
 */
int to_ceil(double x)
{
    int x_ = (int)x;
    return (x != x_ && x > 0 ? x_ + 1 : x_);
}

/**
 * @brief Check if a given integer is a prime number.
 * 
 * This function checks whether the given integer @p p is a prime number.
 * A prime number is a natural number greater than 1 that has no positive divisors 
 * other than 1 and itself.
 * 
 * @param p The integer to be checked for primality.
 * @return true if @p p is a prime number, false otherwise.
 * 
 * @note The function returns false for values of @p p less than or equal to 1.
 *       It uses the square root of @p p to limit the number of divisors to check,
 *       improving efficiency compared to checking all numbers up to @p p-1.
 */
bool is_prime(int p)
{
    if (p <= 1)
    {
        return false;
    }

    /*
     * SIEVE OF ERATOSTHENES
     * If n is a composite number then n has a prime divisor p ≤ √n.
     */
    int sqrt_p = std::sqrt(p);

    for (int i = 2; i <= sqrt_p; i++)
    {
        if (p % i == 0)
        {
            return false;
        }
    }
    return true;
}

/**
 * @brief Decomposes an integer into its prime factors and their exponents.
 * 
 * This function calculates the prime factors and their respective exponents
 * for a given integer n. It stores the results in arrays bases[] and expoents[],
 * and updates quantity_factors with the number of distinct prime factors found.
 * 
 * @param n The integer to decompose into prime factors.
 * @param quantity_factors [out] Number of distinct prime factors found.
 * @param bases [out] Array to store the prime factors.
 * @param expoents [out] Array to store the exponents of the prime factors.
 */
void to_factors(unsigned int n, int &quantity_factors, int *bases, int *expoents)
{
    quantity_factors = 0;
    if (n == 1)
    {
        quantity_factors = 1;
        bases[0] = 1;
        expoents[0] = 1;
    }
    else if (is_prime(n))
    {
        quantity_factors = 1;
        bases[0] = n;
        expoents[0] = 1;
    }
    else
    {
        for (int i = 2; i <= n; i++)
        {
            if (is_prime(i) && n % i == 0)
            {
                bases[quantity_factors] = i;
                expoents[quantity_factors] = 0;
                while (n % i == 0)
                {
                    n = n / i;
                    expoents[quantity_factors]++;
                }
                quantity_factors++;
            }
        }
    }
}

/**
 * @brief Computes the integer represented by the product of prime factors raised to their respective exponents.
 * 
 * This function calculates the integer represented by the product of prime factors
 * given in the arrays bases[] and expoents[], each raised to their respective exponents.
 * 
 * @param quantity_factors Number of prime factors.
 * @param bases Array of prime factors.
 * @param expoents Array of exponents corresponding to each prime factor.
 * @return The integer computed from the product of prime factors raised to their exponents.
 */
int of_factors(int quantity_factors, int *bases, int *expoents)
{
    int n = 1;
    for (int i = 0; i < quantity_factors; i++)
    {
        n = n * pow(bases[i], expoents[i]);
    }
    return n;
}

/**
 * @brief Computes the greatest common divisor (GCD) of two integers using the Euclidean algorithm.
 * 
 * This function computes the GCD of two integers `a` and `b` using the Euclidean algorithm,
 * which iteratively finds the remainder when `a` is divided by `b` until `b` becomes zero.
 * The final non-zero remainder is the GCD of `a` and `b`.
 * 
 * @param a The first integer.
 * @param b The second integer.
 * @return The greatest common divisor (GCD) of `a` and `b`.
 */
int gcd(int a, int b)
{
    /*
     * DEFINITION
     * Let a and b be integers, not both zero. The largest integer d such that d | a and d | b
     * is called the greatest common divisor of a and b. The greatest common divisor of a and b
     * is denoted by gcd(a, b).
     * 
     * EUCLIDEAN ALGORITHM
     * Let a, b ∈ Z, such this a, b > 0. If q, r ∈ such this a = bq + r so gcd(a,b) = gcd(b,r).
     */
    while (b != 0)
    {
        int r = a % b;
        a = b;
        b = r;
    }
    return a;
}

/**
 * @brief Computes the greatest common divisor (GCD) of two integers using the extended Euclidean algorithm.
 * 
 * The extended Euclidean algorithm not only computes the GCD of two integers `a` and `b`,
 * but also determines Bézout coefficients `s` and `t` such that `s × a + t × b = gcd(a, b)`.
 * 
 * @param a The first integer.
 * @param b The second integer.
 * @param s [out] Bézout coefficient `s` such that `s × a + t × b = gcd(a, b)`.
 * @param t [out] Bézout coefficient `t` such that `s × a + t × b = gcd(a, b)`.
 * @return The greatest common divisor (GCD) of `a` and `b`.
 * 
 * @note If either `a` or `b` is zero, the function returns the absolute value of the other number as the GCD.
 */
int gcd(int a, int b, int &s, int &t)
{
    /*
     * EXTENDED EUCLIDEAN ALGORITHM
     * Let a, b ∈ Z, such this a, b > 0 so exist s, t ∈ Z such this gcd(a, b) = s × a + t × b.
     */
    if (b == 0)
    {
        s = 1;
        t = 0;

        return a;
    }
    else
    {
        int s_, t_;
        int r = a % b;
        int gdc_ = gcd(b, r, s_, t_);

        s = t_;
        t = s_ - (a / b) * t_;

        return gdc_;
    }
}

/**
 * @brief Computes the least common multiple (LCM) of two integers.
 * 
 * This function calculates the LCM of two integers `a` and `b` using their prime factorizations.
 * It first decomposes both integers into their prime factors and their respective exponents,
 * then computes the LCM by taking the highest powers of all prime factors present in either number.
 * 
 * @param a The first integer.
 * @param b The second integer.
 * @return The least common multiple (LCM) of `a` and `b`.
 * 
 * @note The function uses the `to_factors` function to decompose `a` and `b` into their prime factors
 *       and their exponents. It assumes that `to_factors` correctly computes the factorization.
 */
int lcm(int a, int b)
{
    /*
     * DEFINITION
     * The least common multiple of the positive integers a and b is the smallest positive integer that
     * is divisible by both a and b. The least common multiple of a and b is denoted by lcm(a, b).
     *
     * FORMULE
     * lcm(a, b) = P_1^max(a_1,b_1) × P_2^max(a_2,b_2) × P_n^max(a_n,b_n) 
     */
    int quantity_factors_a;
    int *bases_a = new int[MAX_FACTORS];
    int *expoents_a = new int[MAX_FACTORS];

    int quantity_factors_b;
    int *bases_b = new int[MAX_FACTORS];
    int *expoents_b = new int[MAX_FACTORS];

    to_factors(a, quantity_factors_a, bases_a, expoents_a);
    to_factors(b, quantity_factors_b, bases_b, expoents_b);

    int lcm_ = 1;

    int i = 0;
    int j = 0;
    while (i < quantity_factors_a && j < quantity_factors_b)
    {
        if (bases_a[i] == bases_b[j])
        {
            lcm_ *= pow(bases_a[i], std::max(expoents_a[i], expoents_b[j]));
            i++;
            j++;
        }
        else if (bases_a[i] < bases_b[j])
        {
            lcm_ *= pow(bases_a[i], expoents_a[i]);
            i++;
        }
        else if (bases_a[i] > bases_b[j])
        {
            lcm_ *= pow(bases_b[j], expoents_b[j]);
            j++;
        }
    }

    while (i < quantity_factors_a)
    {
        lcm_ *= pow(bases_a[i], expoents_a[i]);
        i++;
    }

    while (j < quantity_factors_b)
    {
        lcm_ *= pow(bases_b[j], expoents_b[j]);
        j++;
    }

    delete[] bases_a, expoents_a, bases_b, expoents_b;

    return lcm_;
}

/**
 * @brief Checks if two integers are coprime.
 * 
 * Two integers are coprime if their greatest common divisor (GCD) is 1.
 * 
 * @param a The first integer.
 * @param b The second integer.
 * @return true if `a` and `b` are coprime (gcd(a, b) = 1), false otherwise.
 * 
 * @note The function uses the `gcd` function to determine the GCD of `a` and `b`.
 */
bool are_coprimes(int a, int b)
{
    /*
     * DEFINITION
     * The integers a and b are coprimes if their gcd(a, b) = 1.
     */
    return gcd(a, b) == 1;
}

/**
 * @brief Checks if all integers in a set are pairwise coprime.
 * 
 * Integers in a set are pairwise coprime if every pair of distinct integers in the set
 * has a greatest common divisor (GCD) of 1.
 * 
 * @param size The number of integers in the set.
 * @param set Pointer to an array of integers representing the set.
 * @return true if all integers in the set are pairwise coprime, false otherwise.
 * 
 * @note The function uses the `are_coprimes` function to check the coprimality of each pair of integers in the set.
 */
bool are_pairwise_coprimes(int size, int *set)
{
    /*
     * DEFINITION
     * The integers a_1, a_2, . . . , a_n are pairwise coprimes if gcd(a_i, a_j) = 1 whenever 1 ≤ i < j ≤ n.
     */
    for (int i = 0; i < size; i++)
    {
        for (int j = i + 1; j < size; j++)
        {
            if (!are_coprimes(set[i], set[j]))
            {
                return false;
            }
        }
    }
    return true;
}

/**
 * @brief Checks if two integers are congruent modulo m.
 * 
 * Two integers `a` and `b` are congruent modulo `m` if (a - b) is divisible by `m`.
 * 
 * @param a The first integer.
 * @param b The second integer.
 * @param m The modulus.
 * @return true if `a` and `b` are congruent modulo `m`, false otherwise.
 */
bool are_congruents(int a, int b, int m)
{
    /*
     * DEFINITION
     * If a and b are integers and m is a positive integer, then a is congruent to b modulo m if
     * m divides a − b. We use the notation a ≡ b (mod m) to indicate that a is congruent to
     * b modulo m. We say that a ≡ b (mod m) is a congruence and that m is its modulus (plural
     * moduli). If a and b are not congruent modulo m, we write a /≡ b (mod m).
     */
    return m % (a - b) == 0;
}

/**
 * @brief Computes the modular multiplicative inverse of an integer `a` modulo `m`.
 * 
 * Computes an integer `x` such that (a × x) ≡ 1 (mod m), if such an integer exists.
 * 
 * @param a The integer for which the inverse modulo is sought.
 * @param b Ignored parameter in the context of the function. It could be removed.
 * @param m The modulus.
 * @return The modular multiplicative inverse of `a` modulo `m`.
 * @throws std::runtime_error If no inverse exists (gcd(a, m) != 1).
 * 
 * @note The function uses the `gcd` function to find the GCD of `a` and `m`, and
 *       the extended Euclidean algorithm to compute the inverse if gcd(a, m) = 1.
 */
int inverse_mod(int a, int b, int m)
{
    /*
     * DEFINITION
     * If a and m are relatively prime integers and m > 1, then an inverse of a modulo m exists.
     * Furthermore, this inverse is unique modulo m. (That is, there is a unique positive integer a
     * less than m that is an inverse of a modulo m and every other inverse of a modulo m is
     * congruent to a modulo m.)
     */
    /*
     * a × a̅ ≡ 1 (mod m)
     */
    int s, t;
    int gcd_am = gcd(a, m, s, t);
    if (gcd_am != 1)
    {
        if (b % gcd_am == 0)
        {
            /*
             * ad ≡ bd (mod md) ↔ a ≡ b (mod m)
             */
            a = a / gcd_am;
            b = b / gcd_am;
            m = b / gcd_am;

            return linear_congruence(a, b, m);
        }
        else
        {
            std::string msg_error = "There is no inverse of " + std::to_string(a) + " mod " + std::to_string(m) + "\n";
            throw std::runtime_error(msg_error);
        }
    }
    else
    {
        return s;
    }
}

/**
 * @brief Solves a linear congruence of the form ax ≡ b (mod m) for x.
 * 
 * Computes the solution x to the linear congruence equation ax ≡ b (mod m), where a, b, and m are integers.
 * 
 * @param a Coefficient of x in the congruence equation.
 * @param b Constant term in the congruence equation.
 * @param m Modulus of the congruence.
 * @return The smallest non-negative integer x satisfying the congruence, or -1 if no solution exists.
 * 
 * @throws std::runtime_error If no solution exists (gcd(a, m) does not divide b).
 * 
 * @note The function uses the `inverse_mod` function to find the modular multiplicative inverse
 *       of `a` modulo `m` if gcd(a, m) divides `b`, then computes the solution using properties of congruences.
 */
int linear_congruence(int a, int b, int m)
{
    /*
     * ax ≡ b (mod m)
     */
    int inverse_a_mod_m = inverse_mod(a, b, m);

    /*
     * ā × ax ≡ ā × b (mod m)
     */
    a = a * inverse_a_mod_m;
    b = b * inverse_a_mod_m;

    /*
     * ā × a ≡ 1 (mod m) → 1x ≡ ā × b (mod m)
     *                      x ≡ ā × b (mod m)
     */
    a = 1;

    /*
     * Simplify to:
     * ā × b (mod m)
     */
    b = b % m;

    /*
     * Smallest non-negative integer
     */
    if (b < 0) b = b + m;

    /*
     * x ≡ b (mod m)
     */
    int x = b;

    return x;
}

/**
 * @brief Solves a system of congruences using the Chinese Remainder Theorem (CRT).
 * 
 * Solves a system of congruences of the form x ≡ residues[i] (mod modules[i]) for x,
 * where modules and residues are arrays representing the moduli and residues respectively.
 * 
 * @param quantity The number of congruences in the system.
 * @param modules Pointer to an array of integers representing the moduli (m_i).
 * @param residues Pointer to an array of integers representing the residues (a_i).
 * @return The smallest non-negative integer x satisfying all congruences, or -1 if no solution exists.
 * 
 * @throws std::runtime_error If any modulus in the system is not coprime with all others (gcd(modules[i], modules[j]) != 1 for some i, j).
 * 
 * @note The function computes the product m = m_1 × m_2 × ... × m_n and uses the Chinese Remainder Theorem
 *       to find x such that x ≡ residues[i] (mod modules[i]) for all i. It uses the gcd function to check coprimality
 *       between moduli and their respective residues to find the solution.
 */
int crt(int quantity, int *modules, int *residues)
{
    /*
     * m = m_1 × m_2 × ... × m_n
     */
    int m = 1;
    for (int i = 0; i < quantity; i++)
    {
        m = m * modules[i];
    }

    int *M = new int[quantity];
    int *modular_inverses = new int[quantity];

    /*
     * M_i = m / m_i
     */
    for (int i = 0; i < quantity; i++)
    {
        M[i] = m / modules[i];
    }

    /*
     * s_i = inverse of (M_i mod m_i) 
     */
    for (int i = 0; i < quantity; i++)
    {
        int s, t;
        gcd(M[i], modules[i], s, t);

        if (s < 0) s = s + modules[i];
            
        modular_inverses[i] = s;
    }

    int x_0 = 0;
    /*
     * x_0 = a_1 × M_1 × s_1 + a_2 × M_2 × s_2 + ... + a_n × M_n × s_n
     */
    for (int i = 0; i < quantity; i++)
    {
        x_0 += residues[i] * M[i] * modular_inverses[i];
    }

    /*
     * x ≡ x_0 (mod m)
     */
    int x = x_0 % m;

    delete[] M;
    delete[] modular_inverses;

    return x;
}

/**
 * @brief Calculates Euler's Totient function (φ(n)) for a given integer n.
 *
 * This function computes the value of Euler's Totient function, which counts 
 * the number of integers up to n that are relatively prime to n. It first 
 * factors the integer n into its prime bases and their respective exponents, 
 * then uses these factors to calculate φ(n) using the formula:
 *
 * φ(n) = n × (1 - 1/p1) × (1 - 1/p2) × ... × (1 - 1/pk)
 *
 * where p1, p2, ..., pk are the distinct prime factors of n.
 *
 * @param n The integer for which to calculate Euler's Totient function.
 * @return The value of Euler's Totient function φ(n).
 */
int totiente_euler(unsigned int n)
{
    /*
     * FUNCTION φ OF EULER
     * Definition 1:
     * Let n be a natural number. We define the function φ : ℕ → ℕ given by
     * φ(n) = |{k ∈ ℕ : 1 ≤ k ≤ n and gcd(k,n) = 1}|, where |A| determines the
     * number of elements in a set A.
     * 
     * Proposition 1:
     * We have φ(2) = 1 and φ(n) ≥ 2, for all natural n ≥ 3.
     * 
     * Proposition 2:
     * Let n be a natural number, so φ(n) = n - 1 if n is prime.
     * 
     * Theorem 1:
     * Given n and m two coprime positive integers, then φ(n × m) = φ(n) × φ(m).
     * 
     * Corollary 1:
     * If {m_1, m_2, ..., m_r} is a pairwise coprimes set so
     * φ(m_1 × m_2 × ... × m_r) = φ(m_1) × φ(m_2) × ... × c(m_r).
     * 
     * Note that if N = p × q, where p and q are prime so φ(N) = φ(p × q) = φ(p) × φ(p) = (p - 1) × (q - 1).
     * 
     * Theorem 2:
     * Let p be a prime and α a positive integer so
     * φ(p^α) = p^α - p^(α - 1) = p^(α - 1) × (p - 1) = p^α × (1 - 1/p).
     * 
     * Theorem 3:
     * Let n = p_1^r_1 × p_2^r_2 × ... × p_k^r_k the decomposition of n into prime factors. So
     * φ(n) = p_1^r_1 × p_2^r_2 × ... × p_k^r_k × (p_1 - 1) × (p_2 - 1) × ... × (p_k - 1).
     */
    int quantity_factors;
    int *bases = new int[MAX_FACTORS];
    int *expoents = new int[MAX_FACTORS];
    to_factors(n, quantity_factors, bases, expoents);

    int phi_e;
    if (bases[0] == 1)
    {
        phi_e = 1;
    }
    else
    {
        phi_e = 1;
        for (int i = 0; i < quantity_factors; i++)
        {
            phi_e = phi_e * (pow(bases[i], expoents[i] - 1) * (bases[i] - 1));
        }
    }

    delete[] bases, expoents;

    return phi_e;
}

/**
 * @brief Checks if a given set of residues forms a complete residue system modulo m.
 *
 * This function determines whether the provided set of residues satisfies the conditions
 * to be a complete residue system modulo m.
 *
 * A set {r_1, r_2, ..., r_i, ..., r_j} is a complete residue system modulo m if:
 *  1. r_i ≢ r_j (mod m), for i ≠ j;
 *  2. For each n ∈ ℤ, there exists an i such that n ≡ r_i (mod m).
 *
 * @param m The modulus value.
 * @param quantity_residues The number of residues in the set.
 * @param residues An array containing the residues to be checked.
 * @return true if the set forms a complete residue system modulo m, false otherwise.
 */
bool is_complete_residues_system(int m, int quantity_residues, int *residues)
{
    /*
     * EULER THEOREM
     * Definition 3 (Complete Residues System)
     * {r_1, r_2, ..., r_i, ..., r_j} is a complete system of residues modulo m when:
     *  1. r_i /≡ r_j (mod m), for i /≡ j;
     *  2. for each n ∈ ℤ such that MDC(n, m) = 1, there exists i such that n ≡ r_i (mod m).
     */
    for (int i = 0; i < quantity_residues; i++)
    {
        for (int j = i + 1; j < quantity_residues; j++)
        {
            if (are_congruents(residues[i], residues[j], m)) return false;
        }
    }
    /*
     * Remark: Note that every integer is congruent modulo m to its remainder by dividing
     * by m and is therefore congruent modulo m to one of the numbers A = {0, 1, . . . , m - 1}.
     * Furthermore, any pair of distinct numbers in this set are incongruent modulo m. Thus, we
     * say that A is a complete system of residues modulo m.
     */
    return true;
}

/**
 * @brief Checks if a given set of residues forms a reduced residue system modulo m.
 *
 * This function determines whether the provided set of residues satisfies the conditions
 * to be a reduced residue system modulo m.
 *
 * A set {r_1, r_2, ..., r_i, ..., r_j} is a reduced residue system modulo m if:
 *  1. r_i ≢ r_j (mod m), for i ≠ j;
 *  2. For each n ∈ ℤ such that gcd(n, m) = 1, there exists an i such that n ≡ r_i (mod m);
 *  3. gcd(r_i, m) = 1, for all r_i.
 *
 * @param m The modulus value.
 * @param quantity_residues The number of residues in the set.
 * @param residues An array containing the residues to be checked.
 * @return true if the set forms a reduced residue system modulo m, false otherwise.
 */
bool is_reduced_residues_system(int m, int quantity_residues, int *residues)
{
    /*
     * EULER THEOREM
     * Definition 3 (Reduced Residues System)
     * {r_1, r_2, ..., r_i, ..., r_j} is a reduced system of residues modulo m when:
     *  1. r_i /≡ r_j (mod m), for i /≡ j;
     *  2. for each n ∈ ℤ such that MDC(n, m) = 1, there exists i such that n ≡ r_i (mod m);
     *  3. MDC(r_i, m) = 1, for all r_i.
     */
    for (int i = 0; i < quantity_residues; i++)
    {
        for (int j = i + 1; j < quantity_residues; j++)
        {
            if (are_congruents(residues[i], residues[j], m)) return false;
        }
        if (!are_coprimes(residues[i], m)) return false;
    }
    return true;
}

/**
 * @brief Generates the reduced residue system modulo m from a complete residue system.
 *
 * This function takes a complete residue system and generates the reduced residue system
 * modulo m, which consists of numbers that are coprime with m.
 *
 * @param m The modulus value.
 * @param quantity_residues The number of residues in the complete residue system.
 * @param crs An array containing the complete residue system.
 * @return A pointer to an array containing the reduced residue system. The caller is responsible for freeing the memory allocated for this array.
 * @throws std::runtime_error if the provided residue system is not a complete residue system.
 */
int *to_reduced_residues_system(int m, int quantity_residues, int *crs)
{
    /*
     * EULER THEOREM
     * Proposition 1:
     * Let {r_1, ..., r_φ(m)} be a reduced system of residues modulo m and a ∈ ℤ such that
     * gcd(a, m) = 1. Then ar_1, ..., ar_φ(m) is a reduced system of residues
     * modulo m.
     */
    if (!is_complete_residues_system(m, quantity_residues, crs))
    {
        std::string msg_error = "Parameter received not a complete residues system\n";
        throw std::runtime_error(msg_error);
    }

    /*
     * Remark: To obtain a reduced system of residues modulo m from the complete system of
     * residues system, simply remove the ai that are not coprime with m.
     */
    int count_coprimes = 0;
    for (int i = 0; i < quantity_residues; i++)
    {
        if (are_coprimes(crs[i], m))
        {
            count_coprimes++;
        }
    }

    int *rrs = new int[count_coprimes];
    int new_size = 0;
    for (int i = 0; i < quantity_residues; i++)
    {
        if (are_coprimes(crs[i], m))
        {
            rrs[new_size++] = crs[i];
        }
    }

    return rrs;
}

/**
 * @brief Represents an integer n in a residue system.
 *
 * This function calculates the residues of a given integer `n` with respect to
 * an array of moduli. It returns an array of the residues.
 *
 * @param n The integer for which to compute the residues.
 * @param quantity_modules The number of moduli in the `modules` array.
 * @param modules An array of integers representing the moduli.
 * @return A pointer to an array of integers containing the residues of `n`
 *         with respect to each modulus in the `modules` array. The caller is
 *         responsible for freeing the memory allocated for this array.
 *
 * @note The returned array must be freed by the caller to avoid memory leaks.
 */
int *to_residues(int n, int quantity_modules, int *modules)
{
    if (!are_pairwise_coprimes(quantity_modules, modules))
    {
        std::string msg_error = "Parameter received is not valid\n";
        throw std::runtime_error(msg_error);
    }
    
    int *residues = new int[quantity_modules];
    for (int i = 0; i < quantity_modules; i++)
    {
        residues[i] = n % modules[i];
    }
    return residues;
}

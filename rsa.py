import math
import random

def to_bin(n):
    if n == 0:
        return [0]
    
    n_bin = []
    while n > 0:
        n_bin.append(n % 2)
        n >>= 1

    return n_bin 

def gcd(a, b):
    if b == 0:
        s = 1
        t = 0
        return a, s, t
    else:
        r = a % b
        gcd_, s_, t_ = gcd(b, r)
        s = t_
        t = s_ - (a // b) * t_
        return gcd_, s, t

def inverse_mod(a, m):
    gcd_am, s, t = gcd(a, m)
    return s % m

def is_prime(p):
    if p <= 1:
        return False
    if p == 2:
        return True
    if p % 2 == 0:
        return False
    sqrt_p = int(math.sqrt(p)) + 1
    for i in range(3, sqrt_p, 2):
        if p % i == 0:
            return False
    return True

def expo_mod(b, n, m):
    x = 1
    e = b % m
    n_bin = to_bin(n)
    k = len(n_bin)
    for i in range(k):
        if n_bin[i] == 1:
            x = (x * e) % m
        e = (e * e) % m

    return x

def generate_large_prime():
    while True:
        # p = random.randrange((10**200), (10**201) - 1)
        # p = random.randrange(10**20, (10**21) - 1)
        p = random.randrange(10**10, (10**11) - 1)
        if is_prime(p):
            return p

def generate_encoder(r):
    while True:
        e = random.randrange(2, r)
        if gcd(e, r)[0] == 1:
            return e

def generate_decoder(e, r):
    d = inverse_mod(e, r)
    return d

def generate_pems():
    p = generate_large_prime()
    q = generate_large_prime()
    n = p * q
    r = (p - 1) * (q - 1)
    e = generate_encoder(r)
    d = generate_decoder(e, r)

    with open("encode.pem", 'w') as file:
        file.write(f"{e}\n")
        file.write(f"{n}\n")

    with open("decode.pem", 'w') as file:
        file.write(f"{d}\n")
        file.write(f"{n}\n")

def get_encoder():
    with open('encode.pem', 'r') as file:
        e = int(file.readline())
        r = int(file.readline())
    return e, r

def get_decoder():
    with open('decode.pem', 'r') as file:
        d = int(file.readline())
        r = int(file.readline())
    return d, r

def encode(msg):
    e, n = get_encoder()
    c = ""
    for m in msg:
        m = ord(m) # Gets the ASCII value of character m
        x = expo_mod(m, e, n)
        c += str(x) + " "
    return c.strip()

def decode(msg):
    d, n = get_decoder()
    c = ""
    msg = msg.split()
    for m in msg:
        m = int(m) # Converts the string into an integer
        x = str(chr(expo_mod(m, d, n)))
        c += x
    return c

generate_pems()

msg = "HELP"
coded = encode(msg)
decoded = decode(coded)

print("Original msg: " + msg)
print("Coded msg: " + coded)
print("Decoded msg: " + decoded)

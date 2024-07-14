## Teorema

Dados $a, b, n, m \in \mathbb{Z}$ com $\text{mdc}(n, m) = 1$, se $a \equiv b \pmod{n}$ e $a \equiv b \pmod{m}$, então $a \equiv b \pmod{n \times m}$.

#### Demonstração:

Suponha que $a \equiv b \pmod{n}$ e $a \equiv b \pmod{m}$. Isso implica que:

$$
a - b = n \times k \quad \text{e} \quad a - b = m \times k'
$$

para alguns $k,k' \in \mathbb{Z}$. Logo, por transitividade,

$$
n \times k = m \times k'
$$

Como $\text{mdc}(n, m) = 1$, existe um $q \in \mathbb{Z}$ tal que:

$$
n \times k = m \times q
$$

Portanto,

$$
a - b = n \times (m \times q)
$$

Por comutatividade

$$
a - b = (n \times m) \times q
$$

Assim,

$$
n \times m\ |\ a - b
$$

o que significa que:

$$
a \equiv b \pmod{n \times m}
$$

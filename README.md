# Introduction

Define misc precompiled circuits including rmd160 and modexp. Try to unify the range check components so that all circuits only depend on one column for range check.

Notice: the modexp circuit only supports U256 instead of arbitrary length bigint. This is a difference from EVM L1 behavior by design.

# Generic $(a^b)_p$ over $\mathbb{F}_r$ in Halo2

## I. Representation of $u256$ values in $F_r$
Suppose that for each $x$, $x \in [0, 2^{256}-1]$. We represent $a$ as a vector of three $\mathbb{F}_r$ limbs $[x_0, x_1, x_2]$ such that $x_0 \le 2^{108}$, $x_1 \le 2^{108}$ and $x_2 \le 2^{108}$

$\langle$ x $\rangle$ =
$\underbrace{b_{0}  ,b_{1}  , \cdots, b_{107}}$ $\bigl( x_0 \bigr)$
$\underbrace{b_{108},b_{109}, \cdots, b_{215}}$ $\bigl( x_1 \bigr)$
$\underbrace{b_{216},b_{217}, \cdots, b_{255}}$ $\bigl( x_2 \bigr)$

In addition we use $x_3$ to represent $x$ % $r$ and put them all together we represent $x = [x_0, x_1, x_2, x_3]$.


## II. Constraints of $xy = kp + d$ where $x, y, k, p \in [0, 2^{256}-1]$.

### 1. Picking coprime numbers $d_0, d_1, r$ such that $d_0 d_1  r > 2^{512}$.
Picking $d_0 = 2^{108}-1$, $d_1 = 2^{216}$, and $r$. We notice that these three numbers are co-prime.

**Proof:**
$r$ is prime, $2^{216}$ has only one factor which is $2$ and $2^{108} - 1$ is an odd number.
**Qed.**

### 2. By CRT the following constraints decides a unique $d$ for $x = kp + d$
1. $\langle xy \rangle_{d_0} = \langle kp \rangle_{d_0} + \langle d \rangle_{d_0}$
1. $\langle xy \rangle_{d_1} = \langle kp \rangle_{d_1} + \langle d \rangle_{d_1}$
2. $\langle xy \rangle_{r} = \langle kp \rangle_{r} + \langle d \rangle_{r}$
3. $d < p$.

### 3. Reminders of $\langle x \rangle$ under $d_0, d_1$ and $r$.
1. $\langle x \rangle_{d_0} = \langle x_2 + x_1 + x_0 \rangle_{d_0}$
2. $\langle x \rangle_{d_1} = \langle [x_0, x_1, 0, 0]\rangle_{d_1}$
3. $\langle x \rangle_{r} = x_3$

### 4. Put it all together we get the following constraints.
* $(x_0 + x_1 + x_2)(y_0 + y_1 + y_2) \\ = (k_0 + k_1 + k_2) (p_0 + p_1 + p2) + d_0 + d_1 + d_2$ (modular $2^{108} - 1$)
* $(x_0y_0 + 2^{108} (x_1y_0 + x_0y_1)) = (k_0p_0 + d_0 + 2^{108} (p_1k_0 + p_0k_1) + d1)$ (modular $2^{216}$)
* $x_3y_3 = k_3p_3 + d_3$ (modular $r$)
* $d < p$.

## III. Finalize $modexp(a,b)$ over $p$
### Pseudo code with simple double and add algorithm
```
    let sum = 1;
    let b = [bi; 256];
    for (i=0;i<256;i++) {
        sum = (sum * sum * a^bi) mod p
    }
```
### TODO: Change to wnaf with window = 2

## IV. Gate Definition
### Use standard halo2 gate generator as following:
```
customized_circuits!(ModExpConfig, 2, 5, 9, 1,
   | l0  | l1   | l2  | l3  | d   |  c0  | c1  | c2  | c3  | cd  | cdn | c   | c03  | c12  | sel
   | nil | nil  | nil | nil | d_n |  nil | nil | nil | nil | nil | nil | nil | nil  | nil  | nil
);
```
where l0, l1, l2, l3, d are witness cells and c0, c1, c2, c3, cd, cdn, c, c03, c12 are constant cells.

### Gate constraint for one line:
```
cs.create_gate("one line constraint", |meta| {
    let l0 = config.get_expr(meta, ModExpConfig::l0());
    let l1 = config.get_expr(meta, ModExpConfig::l1());
    let l2 = config.get_expr(meta, ModExpConfig::l2());
    let l3 = config.get_expr(meta, ModExpConfig::l3());
    let d = config.get_expr(meta, ModExpConfig::d());
    let dnext = config.get_expr(meta, ModExpConfig::d_n());
    let c0 = config.get_expr(meta, ModExpConfig::c0());
    let c1 = config.get_expr(meta, ModExpConfig::c1());
    let c2 = config.get_expr(meta, ModExpConfig::c2());
    let c3 = config.get_expr(meta, ModExpConfig::c3());
    let c  = config.get_expr(meta, ModExpConfig::c());
    let cd  = config.get_expr(meta, ModExpConfig::cd());
    let cdn  = config.get_expr(meta, ModExpConfig::cdn());
    let c03 = config.get_expr(meta, ModExpConfig::c03());
    let c12  = config.get_expr(meta, ModExpConfig::c12());
    let sel = config.get_expr(meta, ModExpConfig::sel());

    vec![
        sel * (
            l0.clone() * c0
        +   l1.clone() * c1
        +   l2.clone() * c2
        +   l3.clone() * c3
        +   d  * cd
        +   dnext * cdn
        +   l0 * l3 * c03
        +   l1 * l2 * c12
        +   c)
    ]
});
```

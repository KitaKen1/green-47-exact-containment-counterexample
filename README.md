# A Lean counterexample to the exact-containment form of Green 47

This repository gives an explicit counterexample to the **exact-containment
question** registered as
[`Green47.green_47` in Formal Conjectures](https://github.com/google-deepmind/formal-conjectures/blob/28e6bdd6b994b19fa89457fa2012414af6600a25/FormalConjectures/GreensOpenProblems/47.lean).
The answer to the yes/no question is `False`: the local residue bound does not
force either the stated `log^100` saving or exact containment in one rational
quadratic evaluated on the integers.

**Try it in Lean4Web:**
[open the standalone proof](https://live.lean-lang.org/#url=https%3A%2F%2Fraw.githubusercontent.com%2FKitaKen1%2Fgreen-47-exact-containment-counterexample%2Frefs%2Fheads%2Fmain%2Flean4web%2FGreen47ExactContainmentLean4Web.lean)

## Formal Conjectures target

The file in `lean/` imports the registered declaration and proves it with the
explicit answer `False`:

```lean
theorem green_47 :
    answer(False) ↔ ∀ A : Set ℕ,
      (∀ᶠ p in atTop, Nat.Prime p → Set.ncard (Set.image (fun a : ℕ => (a : ZMod p)) A) ≤ (p + 1) / 2) →
      ((fun X : ℕ => ((A ∩ Set.Iic X).ncard : ℝ)) ≪ (fun X : ℕ => Real.sqrt (X : ℝ) / (Real.log (X : ℝ)) ^ 100))
      ∨ (∃ P : Polynomial ℚ, P.degree = 2 ∧ ∀ a ∈ A, ∃ z : ℤ, (a : ℚ) = P.eval (z : ℚ))
```

Thus the present exact-containment target can be changed from `research open`
to `research solved` by replacing `answer(sorry)` with `answer(False)` and
supplying this proof.

## Mathematical Explanation (AI generated)

The counterexample is built in three layers:

```text
B = {2} ∪ {4^k : k ∈ ℕ}
        ∪ {p² : p is prime and p ≡ 1 (mod 8)}.
```

Each layer has one job.

- The prime squares make `B` much too large for the proposed
  `sqrt(X)/(log X)^100` bound.
- The powers `4^k` force any quadratic containing `B` to have zero
  discriminant, hence to behave like a square.
- The single point `2` then rules out that square-like possibility.

The congruence condition `p ≡ 1 (mod 8)` is what lets this one-point
perturbation preserve the sharp local residue bound.

### Why the local bound survives

Fix an odd prime `q`. There are exactly `(q - 1)/2` nonzero square classes
modulo `q`.

If `2` is a square modulo `q`, every element of `B` is represented by a
square class, possibly including zero. Thus `B mod q` has at most

```text
1 + (q - 1)/2 = (q + 1)/2
```

elements.

Now suppose `2` is not a square modulo `q`. Quadratic reciprocity gives
`q ≡ 3` or `5 (mod 8)`. In this case none of the square bases used in the
construction is divisible by `q`: powers of `2` are nonzero modulo `q`,
and a prime `p ≡ 1 (mod 8)` cannot equal `q`. Hence the square part of
`B` occupies only the `(q - 1)/2` nonzero square classes. The extra element
`2` contributes at most one further class, again giving `(q + 1)/2`.

This is the reason for selecting prime squares with `p ≡ 1 (mod 8)`: whenever
`2` lies outside the square classes, zero is absent from the square part, so
there is exactly enough room to add `2`.

### Why the set is too large

The elements `p²` with `p ≡ 1 (mod 8)` already force substantial growth.
If the registered sparse estimate held, substituting `X = T²` would give

```text
#{p ≤ T : p prime and p ≡ 1 (mod 8)}
    = O(T / (log T)^100).
```

That estimate is far too strong. A dyadic partial-summation argument would make

```text
∑_{p ≡ 1 (mod 8)} log(p) / p
```

converge, whereas the prime series in this arithmetic progression diverges.
Mathlib contains exactly this divergence theorem, so the proof does not need a
quantitative prime number theorem in arithmetic progressions.

### Why no quadratic can contain the set

Assume that a rational quadratic `P` contains every element of `B` in its
image on the integers. Clear denominators and write

```text
P(z) = (az² + bz + c) / d.
```

Because every `4^k` is a value of `P`, completing the square produces
integers `w_k` satisfying

```text
w_k² = C · 4^k + D,
```

where necessarily `C > 0`, and `D = b² - 4ac` is the discriminant term.
Choosing the nonnegative square roots and comparing the equations for `k`
and `k + 1` gives

```text
(w_{k+1} - 2w_k)(w_{k+1} + 2w_k) = -3D.
```

If `D ≠ 0`, the right-hand side is a fixed nonzero integer. But the second
factor on the left tends to infinity, while the first is a nonzero integer and
therefore has absolute value at least one. This is impossible. Hence `D = 0`.

So any quadratic containing all powers `4^k` must be square-like. Since both
`1 = 4^0` and `2` also belong to `B`, evaluating at preimages of these
two values gives squares `r² = 4ad` and `s² = 8ad`. Their ratio says
`2 = (s/r)²` in `ℚ`, which is impossible. Therefore no rational quadratic
contains all of `B` on integer inputs.

The prime squares provide the required size, the geometric sequence supplies
rigidity, and the point `2` breaks exact containment without breaking the
local condition. That is the whole mechanism of the counterexample.

## Status boundary

This repository settles the exact proposition registered in Formal Conjectures
and the same exact-containment question printed as Green's Problem 47. It does
not disprove Green–Harper 2014, Conjecture 1.7.

Indeed, deleting the single element `2` from `B` leaves a subset of the
ordinary squares. The witness therefore already satisfies the finite-exception
quadratic alternative of Green–Harper with `ψ(t) = t²`.

Green–Harper's other alternative also differs from the registered sparse
branch: it asks for arbitrarily large values of `X` for every logarithmic
power `k`, whereas Green 47 and Formal Conjectures use one eventual big-O
bound with the fixed exponent `100`.

## Files

| Directory | Lean version | Purpose |
|---|---:|---|
| `lean/` | `v4.33.1` | Imports the Formal Conjectures target pinned at commit `28e6bdd6…` |
| `lean4web/` | `v4.35.0-rc2` | Standalone mathlib-only proof for Lean4Web |

The FC proof is split into small modules for definitions, the local bound,
quadratic noncontainment, and growth. The Lean4Web directory contains the same
proof as one self-contained source file.

## Verification

Formal Conjectures version:

```bash
cd lean
lake update
lake build
```

Standalone mathlib/Lean4Web version:

```bash
cd lean4web
lake update
lake build
```

Both builds are kernel checked. The Lean4Web file evaluates
`Lean.versionString` to `"4.35.0-rc2"`. The proof files contain no proof
`sorry`, `admit`, custom axiom, `native_decide`, or `unsafe` theorem.
Their final `#print axioms` commands report only Lean's standard axioms:

```text
[propext, Classical.choice, Quot.sound]
```

Pinned dependencies:

- Formal Conjectures:
  `28e6bdd6b994b19fa89457fa2012414af6600a25`
- FC-side mathlib:
  `0df444a360eaa60ab8c11dca51a86af692955474`
- Lean4Web-side mathlib:
  `v4.35.0-rc2` (`065356127b1dc0016f66b7283ce0ce2c4055aa55`)

## Sources

- [Green's 100 Open Problems, Problem 47](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#page=23)
- [Green–Harper, “Inverse questions for the large sieve,” Conjecture 1.7](https://arxiv.org/pdf/1311.6176#page=4)
- [Formal Conjectures: `GreensOpenProblems/47.lean`](https://github.com/google-deepmind/formal-conjectures/blob/28e6bdd6b994b19fa89457fa2012414af6600a25/FormalConjectures/GreensOpenProblems/47.lean)
- [README layout used as a model](https://github.com/KitaKen1/erdos-516-fejer-counterexample)

## AI usage disclosure

This formalization and repository packaging were developed by Kenta Kitamura
([KitaKen1 on GitHub](https://github.com/KitaKen1)), with assistance from
ChatGPT and OpenAI Codex using GPT-6 Astra.

## Appendix: Where this fits in the inverse large sieve problem

The main mathematical problem is the **inverse large sieve problem**. The large
sieve gives square-root-size upper bounds for sets occupying few residue classes
modulo every prime. The inverse problem asks whether sets close to that bound
must come from quadratic or other algebraic structure.

```text
inverse large sieve problem
│
├─ Green–Harper (2014), robust inverse-sieve program
│  ├─ Conjecture 1.5: finitary two-set formulation
│  └─ Conjecture 1.7: clean infinite-set formulation
│     └─ quadratic structure is allowed finitely many exceptions
│
└─ Green, "100 Open Problems", Problem 47
   └─ a "very particular instance"
      └─ exact quadratic containment, with no finite exceptions
         └─ Formal Conjectures: Green47.green_47
```

Green–Harper Conjecture 1.7 says, roughly, that such a set either has quadratic
structure after discarding finitely many elements, or beats the large-sieve
bound by every logarithmic power along arbitrarily large values of `X`.
Green 47 replaces this robust alternative with the simpler fixed
`log^100` bound and exact containment of every element. Formal Conjectures
faithfully records that particular Green 47 formulation.

The witness proved here exploits this exactness: removing the single element
`2` leaves only squares. It therefore refutes Green 47 and the FC
`green_47` target, but it does **not** refute Green–Harper Conjecture 1.7 or
solve the broader inverse large sieve problem.

Accordingly, the current FC target should receive `answer(False)`.
A Green–Harper-style finite-exception statement would be a separate open
variant.

Sources: [Green 47](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#page=23),
[Green–Harper 2014](https://arxiv.org/pdf/1311.6176#page=3), and
[the pinned FC statement](https://github.com/google-deepmind/formal-conjectures/blob/28e6bdd6b994b19fa89457fa2012414af6600a25/FormalConjectures/GreensOpenProblems/47.lean).
